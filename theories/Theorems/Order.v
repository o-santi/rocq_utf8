Require Import Utf8.Spec.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import ZArith.BinInt.
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

Definition nth_valid_codepoint (n: Z) : option codepoint :=
  if n <? 0 then
    None
  else if n <? 0xd800 then
    Some n
  else if n <=? 0x10ffff - 0x0800 then
    Some (n + 0x0800)
  else
    None.

Lemma nth_valid_codepoint_is_some_implies_valid : forall code,
    (exists n, nth_valid_codepoint n = Some code) <->
      valid_codepoint code.
Proof.
  intros code. split. 
  - intro nth. destruct nth as [n nth].
    unfold valid_codepoint, codepoint_less_than_10ffff, codepoint_is_not_surrogate, codepoint_not_negative.
    unfold nth_valid_codepoint in nth.
    destruct (n <? 0) eqn:n_not_neg; [ discriminate|]. apply Z.ltb_nlt in n_not_neg. apply Z.nlt_ge in n_not_neg. 
    destruct (n <? 0xd800) eqn:less_than_d800; inversion nth; subst; clear nth.
    + lia.
    + apply Z.ltb_nlt in less_than_d800.
      destruct (n <=? 1112063)%Z eqn:less_than_10ffff_m_800; [| discriminate]. 
      apply Z.leb_le in less_than_10ffff_m_800.
      inversion H0. subst. clear H0. lia.
  - intro valid_code.
    unfold valid_codepoint, codepoint_less_than_10ffff, codepoint_is_not_surrogate, codepoint_not_negative in valid_code.
    destruct valid_code as [code_less_10ffff [code_not_surrogate code_not_neg]].
    unfold nth_valid_codepoint.
    destruct code_not_surrogate.
    + exists code. apply <- Z.ltb_lt in H. apply Z.ge_le in code_not_neg. apply <- Z.ltb_ge in code_not_neg. rewrite code_not_neg.
      rewrite H. reflexivity.
    + exists (code - 0x0800)%Z.
      destruct (code - 2048 <? 0) eqn:less_than_zero. lia.
      destruct (code - 0x0800 <? 0xd800)%Z eqn:less_d800. lia.
      destruct (code - 0x0800 <=? 0x10ffff - 0x0800)%Z eqn:less_c10ffff_m_800.
      rewrite Z.sub_add. reflexivity.
      lia.
Qed.

Theorem nth_valid_codepoint_compat : forall n1 code1 n2 code2,
    nth_valid_codepoint n1 = Some code1 ->
    nth_valid_codepoint n2 = Some code2 ->
    Z.compare n1 n2 = Z.compare code1 code2.
Proof.
  intros n1 code1 n2 code2 code1_valid code2_valid.
  unfold nth_valid_codepoint in code1_valid, code2_valid.
  repeat match goal with
  | [G: context[if (?a <=? ?b)%N then _ else _] |- _] => 
      let l := fresh "less_than_eq" in
      destruct (a <=? b)%N eqn:l; [apply Z.leb_le in l| apply Z.leb_nle in l]
  | [G: context[if (?a <? ?b)%N then _ else _] |- _] => 
      let l := fresh "less_than" in
      destruct (a <? b)%N eqn:l; [apply Z.ltb_lt in l| apply Z.ltb_nlt in l]
  end; inversion code1_valid; inversion code2_valid; subst; try reflexivity; try lia.
  - specialize (Z.compare_spec n1 code2) as compare_spec. 
    destruct compare_spec; subst; try lia. Search (?a < ?b -> ?c). 
    apply Z.add_lt_mono with (p:=0) (q:= 0x0800) in H; try lia.
    apply Z.gt_lt_iff in H. rewrite Z.add_0_r in H.
    rewrite H. reflexivity.
  - specialize (Z.compare_spec code1 n2) as compare_spec. 
    destruct compare_spec; subst; try lia. 
    apply Z.add_lt_mono with (p:=0) (q:= 0x0800) in H; try lia.
    rewrite Z.add_0_r in H.
    rewrite H. reflexivity.
  - specialize (Z.compare_spec n1 n2) as compare_spec. 
    destruct compare_spec; subst.
    + rewrite Z.compare_refl. reflexivity.
    + apply Z.add_lt_mono_r with (p := 0x0800) in H. rewrite H. reflexivity.
    + apply Z.add_lt_mono_r with (p := 0x800) in H. apply Z.gt_lt_iff in H. rewrite H. reflexivity.
Qed.

Definition inverse_nth_valid_codepoint (code: codepoint) : option Z :=
  if (code <? 0xd800) then
    Some code
  else if (code <=? 0x10ffff)%Z then
    Some (code - 0x0800)%Z
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
    destruct code_valid as [code_less_10ffff [code_not_surrogate code_not_neg]].
    unfold inverse_nth_valid_codepoint. unfold nth_valid_codepoint in H.
    destruct (n <? 0) eqn:n_not_neg; [discriminate |]. apply Z.ltb_ge in n_not_neg.
    destruct (n <? 0xd800) eqn:less_than_d800.
    + inversion H. subst. rewrite less_than_d800. reflexivity.
    + apply Z.ltb_nlt in less_than_d800.
      destruct (n <=? 0x10ffff - 0x0800) eqn:less_than_10ffff; [| discriminate].
      inversion H. subst. clear H. 
      apply Z.leb_le in less_than_10ffff.
      destruct (n + 0xdfff <? 0xd800)%Z eqn:plus_less_than_d800.
      apply Z.ltb_lt in plus_less_than_d800. lia.
      apply Z.ltb_nlt in plus_less_than_d800.
      destruct (n + 0x0800 <? 0xd800)%Z eqn:plus_less_than_cd800.
      * apply Z.ltb_lt in plus_less_than_cd800. lia.
      * apply Z.ltb_nlt in plus_less_than_cd800.
        destruct (n + 0x0800 <=? 0x10ffff)%Z eqn: plus_less_than_10ffff.
        -- rewrite Z.add_simpl_r. reflexivity.
        -- apply Z.leb_nle in plus_less_than_10ffff.
           apply Z.add_le_mono_r with (p:=0x0800) in less_than_10ffff. 
           rewrite Z.sub_add in less_than_10ffff. 
           lia.
  - destruct H as [H valid_code].
    unfold inverse_nth_valid_codepoint in H.
    unfold valid_codepoint, codepoint_less_than_10ffff, codepoint_is_not_surrogate, codepoint_not_negative in valid_code.
    destruct valid_code as [code_less_than_10ffff [code_not_surrogate code_not_neg]].
    unfold nth_valid_codepoint.
    destruct (Z.ltb code 0xd800) eqn:less_than_d800.
    + inversion H. subst. rewrite less_than_d800. destruct (n <? 0) eqn:n_not_neg; [ lia | reflexivity].
    + apply Z.ltb_nlt in less_than_d800.
      destruct (code <=? 0x10ffff)%Z eqn:less_than_10ffff; [| discriminate].
      inversion H. subst. clear H.
      destruct (code - 2048 <? 0) eqn:less_than_zero; [ lia | ].
      apply Z.leb_le in less_than_10ffff.
      destruct (code - 0x0800 <? 0xd800)%Z eqn: plus_less_than_cdfff.
      * lia. 
      * apply Z.ltb_nlt in plus_less_than_cdfff.
        destruct (code - 0x0800 <=? 0x10ffff - 0x0800)%Z eqn:plus_less_than_10ffff_m_800.
        -- rewrite Z.sub_add. reflexivity.
        -- lia.
Qed.

Definition nth_valid_codepoint_representation (n: Z) : option byte_str :=
  let n := if Z.ltb n 0xd800 then n else n + 0x800 in
  if (n <? 0) then
    None
  else if (n <=? 127) then
    Some [ n ]
  else if (n <=? 0x7ff) then
    let b1 := n / 64 in
    let b2 := n mod 64 in
    Some [ 192 + b1; 128 + b2]
  else if (n <=? 0xffff) then
    let r := n / 64 in
    let b1 := r / 64 in
    let b2 := r mod 64 in
    let b3 := n mod 64 in
    Some [ 224 + b1; 128 + b2; 128 + b3]
  else if (n <=? 0x10ffff) then
    let r1 := n / 64 in
    let r2 := r1 / 64 in
    let b1 := r2 / 64 in
    let b2 := r2 mod 64 in
    let b3 := r1 mod 64 in
    let b4 := n mod 64 in
    Some [ 240 + b1; 128 + b2; 128 + b3; 128 + b4]
  else
    None.

Lemma some_injective {T}: forall (a b: T),
    Some a = Some b ->
    a = b.
Proof.
  intros. inversion H. reflexivity.
Qed.

Lemma continuation_is_correct : forall n,
    128 <= 128 + (n mod 64) <= 191.
Proof.
  intros.
  specialize (Z.mod_pos_bound n 64 ltac:(lia)) as [G1 G2]. lia.
Qed.

Theorem nth_valid_codepoint_representation_spec: forall bytes,
    (exists n, nth_valid_codepoint_representation n = Some bytes) <->
      valid_codepoint_representation bytes.
Proof.
  intros bytes. split.
  - intros [n valid_code]. unfold nth_valid_codepoint_representation in valid_code.
    destruct (n <? 0xd800) eqn:n_more_db00; [apply Z.ltb_lt in n_more_db00 | apply Z.ltb_nlt in n_more_db00; apply Z.nlt_ge in n_more_db00].
    destruct (n <? 0) eqn:n_not_neg; [discriminate | apply Z.ltb_nlt in n_not_neg; apply Z.nlt_ge in n_not_neg].
    destruct (n <=? 127)%N eqn:n_less_127; [apply Z.leb_le in n_less_127 | apply Z.leb_nle in n_less_127].
    + inversion valid_code. apply OneByte. lia.
    + destruct (n <=? 0x7ff)%Z eqn:n_less_07ff; [apply Z.leb_le in n_less_07ff | apply Z.leb_nle in n_less_07ff].
      * apply some_injective in valid_code. rewrite <- valid_code.
        apply TwoByte. split. apply Zorder.Znot_le_gt in n_less_127. 
        assert (n / 64 >= 2). {
          apply Z.gt_lt in n_less_127.
          apply Zorder.Zlt_le_succ in n_less_127. apply Z.le_ge in n_less_127.
          specialize (Zdiv.Z_div_ge n 128 64 ltac:(lia) n_less_127) as G. apply G.
        } lia. 
        assert (n / 64 <= 31). { 
          apply (Zdiv.Z_div_le n 2047 64 ltac:(lia) n_less_07ff).
        } lia.
        apply continuation_is_correct.
      * destruct (n <=? 0xffff)%N eqn:n_less_ffff; [apply Z.leb_le in n_less_ffff | apply Z.leb_nle in n_less_ffff].
        -- apply some_injective in valid_code. rewrite <- valid_code.
           apply Zorder.Znot_le_gt in n_less_07ff, n_less_127.
           assert (n / 64 >= 32). {
             apply Z.gt_lt in n_less_07ff.
             apply Zorder.Zlt_le_succ in n_less_07ff. apply Z.le_ge in n_less_07ff.
             apply (Zdiv.Z_div_ge n 2048 64 ltac:(lia) n_less_07ff).
           }
           specialize (Zdiv.Z_div_mod_eq_full (n / 64) 64) as G.
           destruct (Z.compare_spec (n / 64 / 64) 0).
           --- rewrite H0. apply ThreeByte1. reflexivity. split. lia.
               specialize (Z.mod_pos_bound (n / 64) 64 ltac:(lia)) as G2. lia.
               apply continuation_is_correct.
           --- apply Zorder.Zmult_gt_0_lt_compat_l with (p := 64 * 64) in H0.
               rewrite Zdiv.Zdiv_Zdiv in H0.
               replace (64 * 64) with 4096 in H0 by reflexivity.
               rewrite Z.mul_0_r in H0. Search (?a * (?b / ?a)).
               apply Z.lt_mul_0 in H0. destruct H0. lia. destruct H0.
               specialize (Z.div_pos n 4096 n_not_neg ltac:(lia)) as G2. all: lia.
           --- assert (n / 4096 <= 13). {
                 apply Z.lt_le_incl in n_more_db00.
                 apply (Zdiv.Z_div_le n 55296 4096 ltac:(lia) n_more_db00).
               }
               rewrite Zdiv.Zdiv_Zdiv in valid_code, G |- *; try lia.
               replace (64 * 64) with 4096 in valid_code, G |- * by reflexivity. 
               destruct (Z.compare_spec (n / 4096) 13).
               ---- apply ThreeByte3. lia. split. specialize (Z.mod_pos_bound (n / 64) 64 ltac:(lia)) as G2. lia.
                    assert ((n / 64) mod 64 <= 31). {
                      rewrite H2 in G. apply (f_equal (fun a => (-(64 * 13)) + a)) in G.
                      rewrite Z.add_assoc in G.
                      rewrite Z.add_opp_diag_l in G.
                      rewrite Z.add_0_l in G.
                      rewrite <- G. Search (?a <= ?b).
                      specialize (Z.add_le_mono_l (- (64 * 13) + n / 64) 31 (64 * 13)) as [G1 G2].
                      apply G2. rewrite Z.add_assoc.
                      rewrite Z.add_opp_diag_r.
                      rewrite Z.add_0_l.
                      apply Zorder.Zlt_le_succ in n_more_db00. replace 55296 with (Z.succ 55295) in n_more_db00 by reflexivity.
                      apply Zorder.Zsucc_le_reg in n_more_db00.
                      replace (64 * 13 + 31) with 863 by reflexivity.
                      apply (Zdiv.Z_div_le n 55295 64 ltac:(lia) n_more_db00).
                    } lia.
                    apply continuation_is_correct.
               ---- apply ThreeByte2. left. split. rewrite Z.div_div in H0.
                    replace (64 * 64) with 4096 in H0 by reflexivity. apply Zorder.Zlt_le_succ in H0. 1,2,3:lia.
                    lia. all: apply continuation_is_correct.
               ---- lia.
        -- destruct (n <=? 1114111) eqn:n_impossible; [| discriminate].
           apply Z.leb_le in n_impossible. lia.
    + destruct (n + 2048 <? 0) eqn:n_not_neg; [ discriminate| apply Z.ltb_ge in n_not_neg]. 
      destruct (n + 2048 <=? 127) eqn:n_less_127; [ lia | apply Z.leb_gt in n_less_127 ]. 
      destruct (n + 2048 <=? 2047) eqn:n_less_7ff; [ lia | apply Z.leb_gt in n_less_7ff ].
      destruct (n + 2048 <=? 65535) eqn:n_less_ffff; [ apply Z.leb_le in n_less_ffff | apply Z.leb_gt in n_less_ffff].
      * apply some_injective in valid_code. rewrite <- valid_code.
        assert (14 <= (n + 2048) / 64 / 64 <= 15). {
          apply Zorder.Zplus_le_compat_r with (p:=0x800) in n_more_db00.
          replace (55296 + 2048) with 57344 in n_more_db00 by reflexivity.
          rewrite Z.div_div; try lia. split.
          apply (Zdiv.Z_div_le 57344 (n + 2048) (64 * 64) ltac:(lia) n_more_db00).
          apply (Zdiv.Z_div_le (n + 2048) 65535 (64 * 64) ltac:(lia) n_less_ffff).
        } 
        apply ThreeByte2. right. lia. all: apply continuation_is_correct.
      * destruct (n + 2048 <=? 1114111) eqn:n_less_10ffff; [ apply Z.leb_le in n_less_10ffff | discriminate].
        apply some_injective in valid_code. rewrite <- valid_code.
        specialize (Zdiv.Z_div_mod_eq_full ((n + 2048) / 64 / 64) 64) as G.
        destruct (Z.compare_spec ((n + 2048) / 64 / 64 / 64) 0).
        -- apply FourBytes1. rewrite H. reflexivity. split.
           assert (16 <= ((n + 2048) / 64 / 64) mod 64). {
             rewrite H in G. rewrite Z.add_0_l in G. rewrite <- G.
             apply Zorder.Zlt_le_succ in n_less_ffff. 
             rewrite Z.div_div; try lia.
             specialize (Zdiv.Z_div_le 65536 (n+2048) (64 * 64) ltac:(lia) n_less_ffff) as G2.
             replace (65536 / (64 * 64)) with 16 in G2 by reflexivity. apply G2.
           } lia. all: apply continuation_is_correct.
        -- 
 
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

