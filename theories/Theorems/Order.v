Require Import Utf8.Spec.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import NArith.BinNat.
From Coq Require Import Hexadecimal.
From Coq Require Import Strings.Byte.
From Coq Require Import Arith.
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

Lemma nth_valid_codepoint_is_some_implies_valid : forall code,
    (exists n, nth_valid_codepoint n = Some code) <->
      valid_codepoint code.
Proof.
  intros code. split. 
  - intro nth. destruct nth as [n nth].
    unfold valid_codepoint, codepoint_less_than_10ffff, codepoint_is_not_surrogate.
    unfold nth_valid_codepoint in nth.
    destruct (n <? cd800)%N eqn:less_than_d800; inversion nth; subst; clear nth.
    + apply N.ltb_lt in less_than_d800.
      split. apply N.lt_le_incl in less_than_d800. apply N.le_trans with (m:= cd800). assumption. vm_compute. easy.
      left. assumption.
    + apply N.ltb_nlt in less_than_d800.
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
  - intro valid_code.
    unfold valid_codepoint, codepoint_less_than_10ffff, codepoint_is_not_surrogate in valid_code.
    destruct valid_code as [code_less_10ffff code_not_surrogate].
    unfold nth_valid_codepoint.
    destruct code_not_surrogate.
    + exists code. apply <- N.ltb_lt in H. rewrite H. reflexivity.
    + exists (code - c0800)%N.
      destruct (code - c0800 <? cd800)%N eqn:less_d800.
      * apply N.ltb_lt in less_d800. specialize (N.add_lt_mono_r (code - c0800)%N cd800 c0800) as [G1 G2].
        apply G1 in less_d800. rewrite N.sub_add in less_d800.
        replace (cd800 + c0800)%N with (N.succ cdfff) in less_d800 by reflexivity. lia.
        apply N.gt_lt in H. apply N.lt_le_incl in H. apply N.le_trans with (m := cdfff). vm_compute. intro. discriminate.
        assumption.
      * apply N.ltb_nlt in less_d800.
        destruct (code - c0800 <=? c10ffff - c0800)%N eqn: less_c10ffff_m_800.
        -- rewrite N.sub_add. reflexivity.
           apply N.gt_lt in H. apply N.lt_le_incl in H. apply N.le_trans with (m := cdfff). vm_compute. intro. discriminate. assumption.
        -- apply N.leb_nle in less_c10ffff_m_800.
           apply N.lt_nge in less_c10ffff_m_800.
           apply N.lt_sub_lt_add_r in less_c10ffff_m_800. rewrite N.sub_add in less_c10ffff_m_800.
           lia. apply N.gt_lt in H. apply N.lt_le_incl in H. apply N.le_trans with (m := cdfff). vm_compute. intro. discriminate. assumption.
Qed.

Theorem nth_valid_codepoint_compat : forall n1 code1 n2 code2,
    nth_valid_codepoint n1 = Some code1 ->
    nth_valid_codepoint n2 = Some code2 ->
    N.compare n1 n2 = N.compare code1 code2.
Proof.
  intros n1 code1 n2 code2 code1_valid code2_valid.
  unfold nth_valid_codepoint in code1_valid, code2_valid.
  repeat match goal with
  | [G: context[if (?a <=? ?b)%N then _ else _] |- _] => 
      let l := fresh "less_than_eq" in
      destruct (a <=? b)%N eqn:l; [apply N.leb_le in l| apply N.leb_nle in l]
  | [G: context[if (?a <? ?b)%N then _ else _] |- _] => 
      let l := fresh "less_than" in
      destruct (a <? b)%N eqn:l; [apply N.ltb_lt in l| apply N.ltb_nlt in l]
  end; inversion code1_valid; inversion code2_valid; subst; try reflexivity; try lia.
  - specialize (N.compare_spec n1 code2) as compare_spec. 
    destruct compare_spec; subst; try lia. 
    apply N.lt_lt_add_r with (p:= c0800) in H. 
    apply N.gt_lt_iff in H.
    rewrite H. reflexivity.
  - specialize (N.compare_spec code1 n2) as compare_spec. 
    destruct compare_spec; subst; try lia. 
    apply N.lt_lt_add_r with (p:= c0800) in H. 
    rewrite H. reflexivity.
  - specialize (N.compare_spec n1 n2) as compare_spec. 
    destruct compare_spec; subst.
    + rewrite N.compare_refl. reflexivity.
    + apply N.add_lt_mono_r with (p := c0800) in H. rewrite H. reflexivity.
    + apply N.add_lt_mono_r with (p := c0800) in H. apply N.gt_lt_iff in H. rewrite H. reflexivity.
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
  - assert (exists m, nth_valid_codepoint m = Some code). exists n. apply H.
    apply nth_valid_codepoint_is_some_implies_valid in H0 as code_valid. split; [|apply code_valid].
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

Definition c07ff := N.of_hex_uint     (D7 (Df (Df Nil))).
Definition cd800 := N.of_hex_uint (Dd (D8 (D0 (D0 Nil)))).
Definition cffff := N.of_hex_uint (Df (Df (Df (Df Nil)))).

Open Scope N_scope.
Definition nth_valid_codepoint_representation (n: N) : option (list byte) :=
  let n := if N.leb cd800 n then n + c0800 else n in
  let b := fun (idx: N) => N.testbit n idx in
  if (N.leb n 127) then
    Some [ Byte.of_bits (b 0, (b 1, (b 2, (b 3, (b 4, (b 5, (b 6, false))))))) ]
  else if (N.leb n c07ff) then
    Some [ Byte.of_bits (b 6, (b 7, (b 8, (b 9, (b 10, (false, (true, true)))))));
           Byte.of_bits (b 0, (b 1, (b 2, (b 3, (b 4,  (b 5, (false, true)))))))]
  else if (N.leb n cffff) then
    Some [ Byte.of_bits (b 12, (b 13, (b 14, (b 15, (false, (true, (true, true)))))));
           Byte.of_bits (b 6,  (b 7,  (b 8,  (b 9,  (b 10, (b 11, (false, true)))))));
           Byte.of_bits (b 0,  (b 1,  (b 2,  (b 3,  (b 4,  (b 5, (false, true)))))))]
  else if (N.leb n c10ffff) then
    Some [ Byte.of_bits (b 18, (b 19, (b 20, (false, (true, (true, (true, true)))))));
           Byte.of_bits (b 12, (b 13, (b 14, (b 15, (b 16, (b 17, (false, true)))))));
           Byte.of_bits (b 6,  (b 7,  (b 8,  (b 9,  (b 10, (b 11, (false, true)))))));
           Byte.of_bits (b 0,  (b 1,  (b 2,  (b 3,  (b 4,  (b 5, (false, true)))))))]
  else 
    None.

Opaque of_bits.



Lemma byte_range_of_bits_00_7f: forall b1 b2 b3 b4 b5 b6 b7,
    byte_range (Byte.of_bits (b1, (b2, (b3, (b4, (b5, (b6, (b7, false)))))))) = Range_00_7F.
Proof.
  intros.
  let byte := constr:(of_bits (b1, (b2, (b3, (b4, (b5, (b6, (b7, false)))))))) in
  pose (byte_eq := eq_refl byte);
  apply (f_equal Byte.to_bits) in byte_eq;
  rewrite Byte.to_bits_of_bits in byte_eq at 1;
  destruct byte eqn:H2;
    inversion byte_eq;
    try reflexivity; destruct H as [G | [G | [G | G]]]; subst;
    match goal with
    | [F: true = false |- _] => apply Bool.diff_true_false in F; destruct F
    end.
Qed.

Lemma byte_range_of_bits_c2_df: forall b1 b2 b3 b4 b5,
    (b2 = true \/ b3 = true \/ b4 = true \/ b5 = true) ->
    byte_range (Byte.of_bits (b1, (b2, (b3, (b4, (b5, (false, (true, true)))))))) = Range_C2_DF.
Proof.
  intros.
  let byte := constr:(Byte.of_bits (b1, (b2, (b3, (b4, (b5, (false, (true, true)))))))) in
  pose (byte_eq := eq_refl byte);
  apply (f_equal Byte.to_bits) in byte_eq;
  rewrite Byte.to_bits_of_bits in byte_eq at 1;
  destruct byte eqn:H2; inversion byte_eq;
    try reflexivity; destruct H as [G | [G | [G | G]]]; subst;
    match goal with
    | [F: true = false |- _] => apply Bool.diff_true_false in F; destruct F
    end.
Qed.

Lemma in_range_80_bf_of_bits: forall b1 b2 b3 b4 b5 b6,
    in_range_80_bf (of_bits (b1, (b2, (b3, (b4, (b5, (b6, (false, true)))))))).
Proof.
  intros.
  let byte := constr:(Byte.of_bits (b1, (b2, (b3, (b4, (b5, (b6, (false, true)))))))) in
  pose (byte_eq := eq_refl byte);
  apply (f_equal Byte.to_bits) in byte_eq;
  rewrite Byte.to_bits_of_bits in byte_eq at 1;
  destruct byte eqn:H2; inversion byte_eq;
    try reflexivity; destruct H as [G | [G | [G | G]]]; subst;
    match goal with
    | [F: true = false |- _] => apply Bool.diff_true_false in F; destruct F
    end.
Qed.

Lemma at_least_one_bit_1 : forall n, 
    127 < n ->
    n <= 2047 ->
    N.testbit n 7 = true \/ N.testbit n 8 = true \/ N.testbit n 9 = true \/ N.testbit n 10 = true.
Proof.
  intros.
  Search 
  Admitted.

Lemma at_least_one_bit_2 : forall n, 
    127 < n ->
    n <= 2047 ->
    N.testbit n 7 = true \/ N.testbit n 8 = true \/ N.testbit n 9 = true \/ N.testbit n 10 = true.
Proof.
Admitted.

Theorem nth_valid_codepoint_representation_spec: forall bytes,
    (exists n, nth_valid_codepoint_representation n = Some bytes) <->
      valid_codepoint_representation bytes.
Proof.
  intros bytes. split.
  - intros [n valid_code]. unfold nth_valid_codepoint_representation in valid_code.
    destruct (cd800 <=? n)%N eqn:n_more_cdb00.
    destruct (n <=? 127)%N eqn:n_less_127; [apply N.leb_le in n_less_127 | apply N.leb_nle in n_less_127].
    + inversion valid_code. apply OneByte. apply byte_range_of_bits_00_7f.
    + destruct (n <=? c07ff)%N eqn:n_less_07ff; [apply N.leb_le in n_less_07ff | apply N.leb_nle in n_less_07ff].
      * inversion valid_code.
        apply TwoByte. 2: apply in_range_80_bf_of_bits.
        apply byte_range_of_bits_c2_df.
        apply N.nle_gt in n_less_127.
        clear valid_code. clear H0.
        apply at_least_one_bit_1. apply n_less_127. apply n_less_07ff.
      * destruct (n <=? cffff)%N eqn:n_less_ffff; [apply N.leb_le in n_less_ffff | apply N.leb_nle in n_less_ffff].
        -- inversion valid_code. clear H0. clear valid_code. clear n_less_127.
        
Admitted.
        

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

