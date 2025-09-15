Require Import Utf8.Spec.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import NArith.BinNat.
From Coq Require Import Hexadecimal.
From Coq Require Import Strings.Byte.
From Coq Require Import Lia.

Ltac crush_bits :=
  let B := fresh "B" in
  repeat match goal with
    | |- context[if ?bit then _ else _] =>
        destruct bit eqn:B
    | _: context[if ?bit then _ else _ ] |- _ =>
        destruct bit eqn:B
    end.

Ltac to_bits byte :=
  let rec break_bit bits :=
    match type of bits with
    | (bool * bool)%type => let b1 := fresh "b" in let b2 := fresh "b" in destruct bits as [b1 b2]
    | (bool * ?rest)%type => let b := fresh "b" in destruct bits as [b _bits]; break_bit _bits
    | (?rest * bool)%type => let b := fresh "b" in destruct bits as [_bits b]; break_bit _bits
    | ?other => idtac other
    end
  in 
  match type of byte with
  | Spec.codepoint =>
      unfold Spec.codepoint in byte;
      let b := fresh "b" in
      destruct byte as [[[[[b b4_1] b4_2] b4_3] b4_4] b4_5];
      break_bit b4_1; break_bit b4_2; break_bit b4_3; break_bit b4_4; break_bit b4_5
  | Byte.byte =>
      let B := fresh "B" in
      let eqn_name := fresh "byte_bits" in
      remember (Byte.to_bits byte) as B eqn:eqn_name;
      break_bit B;
      symmetry in eqn_name;
      apply (f_equal Byte.of_bits) in eqn_name;
      rewrite Byte.of_bits_to_bits in eqn_name
  end.

Definition c0800 := N.of_hex_uint (D8 (D0 (D0 Nil))).
Definition ce000 := N.of_hex_uint (De (D0 (D0 (D0 Nil)))).

Definition nth_valid_codepoint (n: N) : option codepoint :=
  if (n <? cd800)%N then
    Some n
  else if (n <=? c10ffff - c0800)%N then
    Some (n + c0800)%N
  else
    None.

Lemma nth_valid_codepoint_is_some_implies_valid : forall n code,
    nth_valid_codepoint n = Some code ->
    valid_codepoint code.
Proof.
  intros n code nth.
  unfold valid_codepoint, codepoint_less_than_10ffff, codepoint_is_not_surrogate.
  unfold nth_valid_codepoint in nth.
  destruct (n <? cd800)%N eqn:less_than_d800; inversion nth; subst; clear nth.
  - apply N.ltb_lt in less_than_d800.
    split. apply N.lt_le_incl in less_than_d800. apply N.le_trans with (m:= cd800). assumption. vm_compute. easy.
    left. assumption.
  - apply N.ltb_nlt in less_than_d800.
    destruct (n <=? 1112063)%N eqn:less_than_10ffff_m_800; [| discriminate].
    apply N.leb_le in less_than_10ffff_m_800.
    inversion H0. subst. clear H0.
    split. replace (1112063)%N with (c10ffff - c0800)%N in less_than_10ffff_m_800 by reflexivity.
    specialize (N.add_le_mono_r n (c10ffff - c0800)%N c0800) as [G1 G2].
    apply G1 in less_than_10ffff_m_800.
    rewrite N.sub_add in less_than_10ffff_m_800.
    apply less_than_10ffff_m_800. vm_compute. intro. discriminate.
    apply N.nlt_ge in less_than_d800.
    right. apply N.lt_gt.
    specialize (N.add_le_mono_r cd800 n c0800) as [G1 G2].
    apply G1 in less_than_d800.
    replace (cd800 + c0800)%N with (ce000) in less_than_d800 by reflexivity.
    specialize (N.lt_succ_diag_r cdfff) as s. replace (N.succ cdfff) with ce000 in s by reflexivity.
    lia.
Qed.
    
Definition inverse_nth_valid_codepoint (code: codepoint) : option N :=
  if (code <? cd800)%N then
    Some code
  else if (code <=? c10ffff)%N then
    Some (code - c0800)%N
  else
    None.

Theorem nth_valid_codepoint_invertible : forall code n,
    nth_valid_codepoint n = Some code <->
      inverse_nth_valid_codepoint code = Some n /\ valid_codepoint code.
Proof.
  intros code n.
  split; intros.
  - apply nth_valid_codepoint_is_some_implies_valid in H as code_valid. split; [|apply code_valid].
    unfold inverse_nth_valid_codepoint. unfold nth_valid_codepoint in H.
    destruct (n <? cd800)%N eqn:less_than_d800.
    + inversion H. subst. rewrite less_than_d800. reflexivity.
    + apply N.ltb_nlt in less_than_d800.
      destruct (n <=? c10ffff - c0800)%N eqn:less_than_10ffff; [| discriminate].
      inversion H. subst. clear H.
      apply N.leb_le in less_than_10ffff.
      destruct (n + cdfff <? cd800)%N eqn:plus_less_than_d800.
      apply N.ltb_lt in plus_less_than_d800. lia.
      apply N.ltb_nlt in plus_less_than_d800.
      destruct (n + c0800 <? cd800)%N eqn:plus_less_than_cd800.
      * apply N.ltb_lt in plus_less_than_cd800. lia.
      * apply N.ltb_nlt in plus_less_than_cd800.
        destruct (n + c0800 <=? c10ffff)%N eqn: plus_less_than_10ffff.
        -- rewrite N.add_sub. reflexivity.
        -- apply N.leb_nle in plus_less_than_10ffff.
           apply N.add_le_mono_r with (p:=c0800) in less_than_10ffff. 
           rewrite N.sub_add in less_than_10ffff. 
           lia. unfold N.le. intro G. simpl in G. vm_compute in G. discriminate.
  - destruct H as [H valid_code].
    unfold inverse_nth_valid_codepoint in H.
    unfold valid_codepoint, codepoint_less_than_10ffff, codepoint_is_not_surrogate in valid_code.
    destruct valid_code as [code_less_than_10ffff code_not_surrogate].
    unfold nth_valid_codepoint.
    destruct (N.ltb code cd800) eqn:less_than_d800.
    + inversion H. subst. rewrite less_than_d800. reflexivity.
    + apply N.ltb_nlt in less_than_d800.
      destruct (code <=? c10ffff)%N eqn:less_than_10ffff; [| discriminate].
      inversion H. subst. clear H.
      apply N.leb_le in less_than_10ffff.
      destruct (code - c0800 <? cd800)%N eqn: plus_less_than_cdfff.
      * apply N.ltb_lt in plus_less_than_cdfff.
        apply N.nlt_ge in less_than_d800. destruct code_not_surrogate; try lia.
        apply N.add_lt_mono_r with (p:=c0800) in plus_less_than_cdfff.
        rewrite N.sub_add in plus_less_than_cdfff.
        apply N.gt_lt in H.
        apply N.succ_lt_mono in H. 
        replace (cd800 + c0800)%N with ce000 in plus_less_than_cdfff by reflexivity.
        replace (N.succ cdfff) with ce000 in H by reflexivity. lia.
        apply (N.le_trans) with (m := cd800). vm_compute. intro G. discriminate G. assumption.
      * apply N.ltb_nlt in plus_less_than_cdfff.
        destruct (code - c0800 <=? c10ffff - c0800)%N eqn:plus_less_than_10ffff_m_800.
        -- rewrite N.sub_add. reflexivity.
           apply N.nlt_ge in less_than_d800.
           apply N.le_trans with (m:= cd800).  vm_compute. intro G. discriminate G. assumption.
        -- apply N.leb_nle in plus_less_than_10ffff_m_800.
           lia.
Qed.
        
Definition nth_valid_codepoint_representation (n: N) : option (list byte).
  destruct (Nat.leb n 127) eqn:E.
  assert (n < 255) as valid_byte. 
  apply PeanoNat.Nat.leb_le in E. lia.
  destruct (of_nat n) eqn:b.
  2: { apply of_nat_None_iff in b. lia. } 
  apply (Some [b0]).
  apply None.
Defined.

From Coq Require Extraction.
Extraction nth_valid_byte.
      
  

Lemma byte_compare_antisymmetric : forall byte1 byte2, byte_compare byte1 byte2 = CompOpp (byte_compare byte2 byte1).
Proof.
  intros byte1 byte2.
  unfold byte_compare.
  apply PeanoNat.Nat.compare_antisym.
Qed.

Lemma byte_compare_eq_iff : forall b1 b2, byte_compare b1 b2 = Eq <-> b1 = b2.
Proof.
  intros b1 b2.
  unfold byte_compare.
  specialize (PeanoNat.Nat.compare_eq_iff (Byte.to_nat b1) (Byte.to_nat b2)) as [G1 G2].
  split; intros.
  - apply G1 in H. apply (f_equal Byte.of_nat) in H. do 2 rewrite Byte.of_to_nat in H. inversion H. reflexivity.
  - subst. specialize (G2 ltac:(reflexivity)).
    apply G2.
Qed.

Lemma list_compare_refl_if {T} (cmp: T -> T -> comparison) : forall (t: list T), 
    (forall x y, cmp x y = Eq <-> x = y) ->
    list_compare cmp t t = Eq.
Proof.
  intros t cmp_eq.
  apply list_compare_refl; [| reflexivity].
  apply cmp_eq.
Qed.

