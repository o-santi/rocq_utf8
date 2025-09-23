Require Import Utf8.Spec.
Require Import Utf8.Theorems.Enumerations.
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
    destruct compare_spec; subst; try lia. 
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

Lemma nth_valid_codepoint_none : forall n,
    nth_valid_codepoint n = None ->
    n < 0 \/ n > (0x10ffff - 0x800).
Proof.
  intros n is_none.
  unfold nth_valid_codepoint in is_none.
  destruct (n <? 0) eqn:n_lt_0. lia.
  destruct (n <? 55296) eqn:n_lt_d800. discriminate.
  destruct (n <=? 1114111 - 2048) eqn:n_lt_10ffff. discriminate. lia.
Qed.
  
Definition inverse_nth_valid_codepoint (code: codepoint) : option Z :=
  if (code <? 0) then
    None 
  else if (code <? 0xd800) then
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
    + inversion H. subst.
      replace (code <? 0) with false by lia.
      rewrite less_than_d800. reflexivity.
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
        -- rewrite Z.add_simpl_r.
           replace (n + 2048 <? 0) with false by lia. reflexivity.
        -- apply Z.leb_nle in plus_less_than_10ffff.
           apply Z.add_le_mono_r with (p:=0x0800) in less_than_10ffff. 
           rewrite Z.sub_add in less_than_10ffff. 
           lia.
  - destruct H as [H valid_code].
    unfold inverse_nth_valid_codepoint in H.
    unfold valid_codepoint, codepoint_less_than_10ffff, codepoint_is_not_surrogate, codepoint_not_negative in valid_code.
    destruct valid_code as [code_less_than_10ffff [code_not_surrogate code_not_neg]].
    unfold nth_valid_codepoint.
    destruct (Z.ltb code 0) eqn:less_than_0; [discriminate|].
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


Module F := FiniteEnumerations Z.

Theorem nth_valid_codepoint_ordered : F.ordered_enumeration valid_codepoint (0x10ffff - 0x7ff) nth_valid_codepoint inverse_nth_valid_codepoint.
Proof.
  split.
  - split.
    + intros n code is_some.
      apply nth_valid_codepoint_is_some_implies_valid. exists n. apply is_some.
    + intros n is_none. unfold F.interval. apply nth_valid_codepoint_none in is_none. lia.
  - split.
    + split.
      * intros n code is_some. unfold inverse_nth_valid_codepoint in is_some.
        unfold F.interval.
        destruct (n <? 0) eqn:n_lt_0; [discriminate|].
        destruct (n <? 55296) eqn:n_lt_d800.
        -- inversion is_some. lia.
        -- destruct (n <=? 0x10ffff) eqn:n_lt_10ffff; [|discriminate]. inversion is_some. lia.
      * intros n is_none. unfold inverse_nth_valid_codepoint in is_none.
        unfold valid_codepoint, codepoint_less_than_10ffff, codepoint_is_not_surrogate, codepoint_not_negative.
        destruct (n <? 0) eqn:n_lt_0. lia.
        destruct (n <? 55296) eqn:n_lt_d800. discriminate.
        destruct (n <=? 0x10ffff) eqn:n_lt_10ffff. discriminate.
        lia.
    + split.
      * unfold F.pointwise_equal, F.and_then.
        intros n in_range.
        destruct (nth_valid_codepoint n) eqn:nth_valid.
        apply nth_valid_codepoint_invertible. apply nth_valid.
        apply nth_valid_codepoint_none in nth_valid. unfold F.interval in in_range. lia.
      * split.
        -- unfold F.pointwise_equal, F.and_then.
           intros code valid_code.
           destruct (inverse_nth_valid_codepoint code) eqn:inverse_code.
           apply nth_valid_codepoint_invertible. split; assumption.
           apply nth_valid_codepoint_is_some_implies_valid in valid_code.
           destruct valid_code as [n nth_valid_is_some].
           apply nth_valid_codepoint_invertible in nth_valid_is_some as [invertible_some _].
           rewrite inverse_code in invertible_some. discriminate.
        -- intros n1 n2 code1 code2 range1 range2 n1_lt_n2 code1_some code2_some.
           symmetry in code1_some, code2_some.
           specialize (nth_valid_codepoint_compat n1 code1 n2 code2 code1_some code2_some) as compare_compat.
           rewrite <- compare_compat.
           apply n1_lt_n2.
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
    a = b <->
          Some a = Some b.
Proof.
  split; intros.
  subst. reflexivity.
  inversion H. reflexivity.
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
               rewrite Z.mul_0_r in H0. 
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
                      rewrite <- G. 
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
        -- specialize (Z.div_pos (n + 2048) 64 n_not_neg ltac:(lia)) as G2.
           specialize (Z.div_pos ((n + 2048) / 64) 64 G2 ltac:(lia)) as G3.
           specialize (Z.div_pos (((n + 2048) / 64) / 64) 64 G3 ltac:(lia)) as G4. lia.
        -- destruct (Z.compare_spec ((n + 2048) / 64 / 64 / 64) 4).
           --- apply FourBytes3. rewrite H0. reflexivity. 
               split. specialize (Z.mod_pos_bound ((n + 2048) / 64 / 64) 64 ltac:(lia)) as G2. lia.
               specialize (Zdiv.Z_div_mod_eq_full ((n + 2048) / 64 / 64) 64) as G2.
               rewrite H0 in G2. apply (f_equal (fun b => -(64 * 4) + b)) in G2.
               rewrite Z.add_assoc in G2.
               rewrite Z.add_opp_diag_l in G2. rewrite Z.add_0_l in G2. 
               specialize (Zdiv.Z_div_le (n + 2048) 1114111 (64 * 64) ltac:(lia) ltac:(assumption)) as G3.
               rewrite Z.div_div in G2 |- *. 
               replace (1114111 / (64 * 64)) with 271 in G3 by reflexivity.
               all: try lia; apply continuation_is_correct.
           --- apply FourBytes2. lia. all: apply continuation_is_correct.
           --- specialize (Zdiv.Z_div_le (n+2048) 1114111 (64 * 64 * 64) ltac:(lia) n_less_10ffff) as G2.
               replace (1114111 / (64 * 64 * 64)) with 4 in G2 by reflexivity.
               do 2 rewrite Z.div_div in H0; try lia. rewrite Z.mul_assoc in H0. lia.
  - intros bytes_valid.
    unfold nth_valid_codepoint_representation.
    destruct bytes_valid eqn:B_valid.
    + exists b. destruct a as [G1 G2].
      replace (b <? 0xd800 ) with true by lia.
      replace (b <? 0) with false by lia.
      replace (b <=? 127) with true by lia. reflexivity.
    + pose (n := ((b1 - 192) * 64) + (b2 mod 64)).
      destruct a. destruct a0.
      exists n.
      clear B_valid.
      rewrite Z.sub_le_mono_r with (p:= 192) in l, l0.
      replace (194 - 192) with 2 in l by reflexivity.
      replace (223 - 192) with 31 in l0 by reflexivity.
      specialize (Z.mod_pos_bound b2 64 ltac:(lia)) as G.
      replace (n <? 0xd800) with true by lia.
      replace (n <? 0) with false by lia.
      replace (n <=? 127) with false by lia.
      replace (n <=? 2047) with true by lia.
      rewrite <- some_injective.
      assert (b1 = 192 + n / 64). {
        unfold n.
        rewrite Z.div_add_l; [| lia].
        rewrite Z.mod_div; [| lia].
        lia.
      } rewrite <- H.
      assert (b2 = 128 + (n mod 64)). {
        unfold n. 
        rewrite Zdiv.Zplus_mod. rewrite Z.mod_mul; [ |lia].
        rewrite Zdiv.Zmod_mod. rewrite Z.add_0_l.
        rewrite Zdiv.Zmod_mod.
        specialize (Zdiv.Z_div_mod_eq_full b2 64) as G2.
        assert (b2 / 64 = 2). lia. rewrite H0 in G2. lia.
      } rewrite <- H0. reflexivity.
    + pose (n := (b2 mod 64) * 64 + (b3 mod 64)).
      destruct a; destruct a0.
      exists n.
      specialize (Z.mod_pos_bound b2 64 ltac:(lia)) as G1.
      specialize (Z.mod_pos_bound b3 64 ltac:(lia)) as G2.
      specialize (Zdiv.Z_div_mod_eq_full b2 64) as G3.
      specialize (Zdiv.Z_div_mod_eq_full b3 64) as G4.
      assert (b2 / 64 = 2). lia.
      assert (b3 / 64 = 2). lia.
      replace (n <? 0xd800) with true by lia.
      replace (n <? 0) with false by lia.
      replace (n <=? 127) with false by lia.
      replace (n <=? 2047) with false by lia.
      replace (n <=? 65535) with true by lia.
      rewrite <- some_injective.
      assert (n / 64 / 64 = 0). {
        unfold n. rewrite Z.div_add_l; [| lia].
        rewrite Z.mod_div. rewrite Z.add_0_r. rewrite Z.mod_div. all:lia.
      } rewrite H1. rewrite Z.add_0_r. rewrite <- e.
      assert (128 + (n / 64) mod 64 = b2). {
        unfold n. rewrite Z.div_add_l; [| lia].
        rewrite Z.mod_div. rewrite Z.add_0_r. rewrite Z.mod_mod.
        rewrite H in G3.
        rewrite G3 at 2. all: lia.
      } rewrite H2.
      assert (128 + n mod 64 = b3). {
        unfold n. rewrite Zdiv.Zplus_mod.
        rewrite Z.mod_mod.
        rewrite Z.mod_mul. rewrite Z.add_0_l.
        rewrite Z.mod_mod. rewrite H0 in G4. rewrite G4 at 2.
        reflexivity. all: lia.
      } rewrite H3. reflexivity.
    + pose (n := ((b1 - 224) * 4096) + (b2 mod 64) * 64 + (b3 mod 64)).
      destruct o; destruct a1; destruct a; destruct a0;
      specialize (Z.mod_pos_bound b2 64 ltac:(lia)) as G1;
      specialize (Z.mod_pos_bound b3 64 ltac:(lia)) as G2;
      specialize (Zdiv.Z_div_mod_eq_full b2 64) as G3;
      specialize (Zdiv.Z_div_mod_eq_full b3 64) as G4;
      assert ((b2 / 64) = 2) as b2_64; try lia;
      assert ((b3 / 64) = 2) as b3_64; try lia;
      rewrite b2_64 in G3;
      rewrite b3_64 in G4.
      * exists n.
        replace (n <? 0xd800) with true by lia.
        replace (n <? 0) with false by lia.
        replace (n <=? 127) with false by lia.
        replace (n <=? 2047) with false by lia.
        replace (n <=? 65535) with true by lia.
        assert (224 + n / 4096 = b1). {
          unfold n.
          rewrite <- Z.add_assoc.
          rewrite Z.div_add_l.
          replace 4096 with (64 * 64) by reflexivity.
          rewrite <- Z.div_div. rewrite Z.div_add_l.
          rewrite Z.mod_div. rewrite Z.add_0_r.
          rewrite Z.mod_div. all: lia.
        } rewrite Z.div_div. replace (64 * 64) with 4096 by reflexivity. rewrite H.
        assert (128 + (n / 64) mod 64 = b2). {
          unfold n.
          replace 4096 with (64 * 64) by reflexivity.
          rewrite <- Z.add_assoc.
          rewrite Z.mul_assoc.
          rewrite Z.div_add_l.
          rewrite Zdiv.Zplus_mod.
          rewrite Z.mod_mul. rewrite Z.add_0_l.
          rewrite Z.div_add_l. rewrite Z.mod_div.
          rewrite Z.add_0_r.
          repeat rewrite Z.mod_mod.
          rewrite G3 at 2. all: lia.
        } rewrite H0.
        assert (128 + n mod 64 = b3). {
          unfold n.
          replace 4096 with (64 * 64) by reflexivity.
          rewrite Zdiv.Zplus_mod.
          rewrite Z.mul_assoc.
          rewrite <- Z.mul_add_distr_r. 
          rewrite Z.mod_mul.
          rewrite Z.add_0_l. repeat rewrite Z.mod_mod.
          all: lia.
        } rewrite H1. reflexivity. all: lia.
      * exists (n - 2048).
        replace ((n - 2048) <? 0xd800) with false by lia.
        rewrite Z.sub_add.
        replace (n <? 0) with false by lia.
        replace (n <=? 127) with false by lia.
        replace (n <=? 2047) with false by lia.
        replace (n <=? 65535) with true by lia.
        assert (224 + n / 4096 = b1). {
          unfold n.
          rewrite <- Z.add_assoc.
          rewrite Z.div_add_l.
          replace 4096 with (64 * 64) by reflexivity.
          rewrite <- Z.div_div. rewrite Z.div_add_l.
          rewrite Z.mod_div. rewrite Z.add_0_r.
          rewrite Z.mod_div. all: lia.
        } rewrite Z.div_div. replace (64 * 64) with 4096 by reflexivity. rewrite H.
        assert (128 + (n / 64) mod 64 = b2). {
          unfold n.
          replace 4096 with (64 * 64) by reflexivity.
          rewrite <- Z.add_assoc.
          rewrite Z.mul_assoc.
          rewrite Z.div_add_l.
          rewrite Zdiv.Zplus_mod.
          rewrite Z.mod_mul. rewrite Z.add_0_l.
          rewrite Z.div_add_l. rewrite Z.mod_div.
          rewrite Z.add_0_r.
          repeat rewrite Z.mod_mod.
          rewrite G3 at 2. all: lia.
        } rewrite H0.
        assert (128 + n mod 64 = b3). {
          unfold n.
          replace 4096 with (64 * 64) by reflexivity.
          rewrite Zdiv.Zplus_mod.
          rewrite Z.mul_assoc.
          rewrite <- Z.mul_add_distr_r. 
          rewrite Z.mod_mul.
          rewrite Z.add_0_l. repeat rewrite Z.mod_mod.
          all: lia.
        } rewrite H1. reflexivity. all: lia.
    + pose (n := (13 * 4096) + (b2 mod 64) * 64 + (b3 mod 64)).
      clear B_valid.
      destruct a; destruct a0; 
      specialize (Z.mod_pos_bound b2 64 ltac:(lia)) as G1;
      specialize (Z.mod_pos_bound b3 64 ltac:(lia)) as G2;
      specialize (Zdiv.Z_div_mod_eq_full b2 64) as G3;
      specialize (Zdiv.Z_div_mod_eq_full b3 64) as G4;
      assert ((b2 / 64) = 2) as b2_64; try lia;
      assert ((b3 / 64) = 2) as b3_64; try lia;
      rewrite b2_64 in G3;
      rewrite b3_64 in G4.
      exists n.
      replace (n <? 0xd800) with true by lia.
      replace (n <? 0) with false by lia.
      replace (n <=? 127) with false by lia.
      replace (n <=? 2047) with false by lia.
      replace (n <=? 65535) with true by lia.
      assert (224 + n / 4096 = b1). {
        unfold n.
        rewrite <- Z.add_assoc.
        rewrite Z.div_add_l.
        replace 4096 with (64 * 64) by reflexivity.
        rewrite <- Z.div_div. rewrite Z.div_add_l.
        rewrite Z.mod_div. rewrite Z.add_0_r.
        rewrite Z.mod_div. rewrite e. all: lia.
      } rewrite Z.div_div. replace (64 * 64) with 4096 by reflexivity. rewrite H3.
      assert (128 + (n / 64) mod 64 = b2). {
        unfold n.
        replace 4096 with (64 * 64) by reflexivity.
        rewrite <- Z.add_assoc.
        rewrite Z.mul_assoc.
        rewrite Z.div_add_l.
        rewrite Zdiv.Zplus_mod.
        rewrite Z.mod_mul. rewrite Z.add_0_l.
        rewrite Z.div_add_l. rewrite Z.mod_div.
        rewrite Z.add_0_r.
        repeat rewrite Z.mod_mod.
        rewrite G3 at 2. all: lia.
      } rewrite H4.
      assert (128 + n mod 64 = b3). {
        unfold n.
        replace 4096 with (64 * 64) by reflexivity.
        rewrite Zdiv.Zplus_mod.
        rewrite Z.mul_assoc.
        rewrite <- Z.mul_add_distr_r. 
        rewrite Z.mod_mul.
        rewrite Z.add_0_l. repeat rewrite Z.mod_mod.
        all: lia.
      } rewrite H5. reflexivity. all: lia.
    + pose (n := (b1 - 240) * 64 * 64 * 64 + (b2 mod 64) * 64 * 64 + (b3 mod 64) * 64 + (b4 mod 64)).
      destruct a. destruct a0. destruct a1. clear B_valid.
      specialize (Z.mod_pos_bound b2 64 ltac:(lia)) as G1;
      specialize (Z.mod_pos_bound b3 64 ltac:(lia)) as G2;
      specialize (Z.mod_pos_bound b4 64 ltac:(lia)) as G3;
      specialize (Zdiv.Z_div_mod_eq_full b2 64) as G4;
      specialize (Zdiv.Z_div_mod_eq_full b3 64) as G5;
      specialize (Zdiv.Z_div_mod_eq_full b4 64) as G6;
      assert ((b2 / 64) = 2) as b2_64; try lia;
      assert ((b3 / 64) = 2) as b3_64; try lia;
      assert ((b4 / 64) = 2) as b4_64; try lia;
      rewrite b2_64 in G4;
      rewrite b3_64 in G5;
      rewrite b4_64 in G6.
      exists (n - 2048).
      replace ((n - 2048) <? 0xd800) with false by lia.
      rewrite Z.sub_add.
      replace (n <? 0) with false by lia.
      replace (n <=? 127) with false by lia.
      replace (n <=? 2047) with false by lia.
      replace (n <=? 65535) with false by lia.
      replace (n <=? 1114111) with true by lia.
      assert (n / 64 / 64 / 64 = 0). { 
        unfold n.
        do 2 rewrite <- Z.add_assoc. 
        repeat rewrite Z.div_add_l. rewrite e.
        rewrite Z.mod_div. rewrite Z.add_0_r.
        rewrite Z.mod_div. rewrite Z.add_0_r.
        rewrite Z.mod_div. all: lia.
      } rewrite H. rewrite <- e. rewrite Z.add_0_r.
      assert (128 + (n / 64 / 64) mod 64 = b2). { 
        unfold n.
        do 2 rewrite <- Z.add_assoc.
        repeat rewrite Z.div_add_l. rewrite Z.mod_div. rewrite Z.add_0_r.
        rewrite Z.mod_div. rewrite Z.add_0_r.
        rewrite Zdiv.Zplus_mod.
        rewrite Z.mod_mul. rewrite Z.add_0_l.
        rewrite Z.mod_mod. rewrite Z.mod_mod.
        rewrite G4 at 2. all: lia.
      } rewrite H0. 
      assert (128 + (n / 64) mod 64 = b3). { 
        unfold n.
        do 2 rewrite <- Z.add_assoc.
        repeat rewrite Z.div_add_l. rewrite Z.mod_div. rewrite Z.add_0_r.
        rewrite Zdiv.Zplus_mod.
        rewrite Z.mod_mul. rewrite Z.add_0_l.
        rewrite Z.mod_mod. rewrite Zdiv.Zplus_mod.
        rewrite Z.mod_mul.  rewrite Z.mod_mod.
        rewrite Z.add_0_l. rewrite Z.mod_mod.
        rewrite G5 at 2. all: lia.
      } rewrite H1. 
      assert (128 + n mod 64 = b4). { 
        unfold n.
        do 2 rewrite <- Z.add_assoc.
        rewrite Zdiv.Zplus_mod.
        rewrite Z.mod_mul at 1. rewrite Z.add_0_l.
        rewrite Zdiv.Zplus_mod.
        rewrite Z.mod_mul at 1. rewrite Z.add_0_l.
        rewrite Zdiv.Zplus_mod.
        rewrite Z.mod_mul at 1. rewrite Z.add_0_l.
        repeat rewrite Z.mod_mod.
        rewrite G6 at 2. all: lia.
      } rewrite H2. reflexivity.
    + pose (n := (b1 - 240) * 64 * 64 * 64 + (b2 mod 64) * 64 * 64 + (b3 mod 64) * 64 + (b4 mod 64)).
      destruct a. destruct a0. destruct a1. destruct a2. clear B_valid.
      specialize (Z.mod_pos_bound b2 64 ltac:(lia)) as G1;
      specialize (Z.mod_pos_bound b3 64 ltac:(lia)) as G2;
      specialize (Z.mod_pos_bound b4 64 ltac:(lia)) as G3;
      specialize (Zdiv.Z_div_mod_eq_full b2 64) as G4;
      specialize (Zdiv.Z_div_mod_eq_full b3 64) as G5;
      specialize (Zdiv.Z_div_mod_eq_full b4 64) as G6;
      assert ((b2 / 64) = 2) as b2_64; try lia;
      assert ((b3 / 64) = 2) as b3_64; try lia;
      assert ((b4 / 64) = 2) as b4_64; try lia;
      rewrite b2_64 in G4;
      rewrite b3_64 in G5;
      rewrite b4_64 in G6.
      exists (n - 2048).
      replace ((n - 2048) <? 0xd800) with false by lia.
      rewrite Z.sub_add.
      replace (n <? 0) with false by lia.
      replace (n <=? 127) with false by lia.
      replace (n <=? 2047) with false by lia.
      replace (n <=? 65535) with false by lia.
      replace (n <=? 1114111) with true by lia.
      assert (240 + n / 64 / 64 / 64 = b1). { 
        unfold n.
        do 2 rewrite <- Z.add_assoc. 
        repeat rewrite Z.div_add_l. 
        rewrite Z.mod_div. rewrite Z.add_0_r.
        rewrite Z.mod_div. rewrite Z.add_0_r.
        rewrite Z.mod_div. all: lia.
      } rewrite H. 
      assert (128 + (n / 64 / 64) mod 64 = b2). { 
        unfold n.
        do 2 rewrite <- Z.add_assoc.
        repeat rewrite Z.div_add_l. rewrite Z.mod_div. rewrite Z.add_0_r.
        rewrite Z.mod_div. rewrite Z.add_0_r.
        rewrite Zdiv.Zplus_mod.
        rewrite Z.mod_mul. rewrite Z.add_0_l.
        rewrite Z.mod_mod. rewrite Z.mod_mod.
        rewrite G4 at 2. all: lia.
      } rewrite H0. 
      assert (128 + (n / 64) mod 64 = b3). { 
        unfold n.
        do 2 rewrite <- Z.add_assoc.
        repeat rewrite Z.div_add_l. rewrite Z.mod_div. rewrite Z.add_0_r.
        rewrite Zdiv.Zplus_mod.
        rewrite Z.mod_mul. rewrite Z.add_0_l.
        rewrite Z.mod_mod. rewrite Zdiv.Zplus_mod.
        rewrite Z.mod_mul.  rewrite Z.mod_mod.
        rewrite Z.add_0_l. rewrite Z.mod_mod.
        rewrite G5 at 2. all: lia.
      } rewrite H1. 
      assert (128 + n mod 64 = b4). { 
        unfold n.
        do 2 rewrite <- Z.add_assoc.
        rewrite Zdiv.Zplus_mod.
        rewrite Z.mod_mul at 1. rewrite Z.add_0_l.
        rewrite Zdiv.Zplus_mod.
        rewrite Z.mod_mul at 1. rewrite Z.add_0_l.
        rewrite Zdiv.Zplus_mod.
        rewrite Z.mod_mul at 1. rewrite Z.add_0_l.
        repeat rewrite Z.mod_mod.
        rewrite G6 at 2. all: lia.
      } rewrite H2. reflexivity.
    + pose (n := (b1 - 240) * 64 * 64 * 64 + (b2 mod 64) * 64 * 64 + (b3 mod 64) * 64 + (b4 mod 64)).
      destruct a. destruct a0. destruct a1. clear B_valid.
      specialize (Z.mod_pos_bound b2 64 ltac:(lia)) as G1;
      specialize (Z.mod_pos_bound b3 64 ltac:(lia)) as G2;
      specialize (Z.mod_pos_bound b4 64 ltac:(lia)) as G3;
      specialize (Zdiv.Z_div_mod_eq_full b2 64) as G4;
      specialize (Zdiv.Z_div_mod_eq_full b3 64) as G5;
      specialize (Zdiv.Z_div_mod_eq_full b4 64) as G6;
      assert ((b2 / 64) = 2) as b2_64; try lia;
      assert ((b3 / 64) = 2) as b3_64; try lia;
      assert ((b4 / 64) = 2) as b4_64; try lia;
      rewrite b2_64 in G4;
      rewrite b3_64 in G5;
      rewrite b4_64 in G6.

      exists (n - 2048).
      replace ((n - 2048) <? 0xd800) with false by lia.
      rewrite Z.sub_add.
      replace (n <? 0) with false by lia.
      replace (n <=? 127) with false by lia.
      replace (n <=? 2047) with false by lia.
      replace (n <=? 65535) with false by lia.
      replace (n <=? 1114111) with true by lia.
      assert (240 + n / 64 / 64 / 64 = b1). { 
        unfold n.
        do 2 rewrite <- Z.add_assoc. 
        repeat rewrite Z.div_add_l. 
        rewrite Z.mod_div. rewrite Z.add_0_r.
        rewrite Z.mod_div. rewrite Z.add_0_r.
        rewrite Z.mod_div. all: lia.
      } rewrite H. 
      assert (128 + (n / 64 / 64) mod 64 = b2). { 
        unfold n.
        do 2 rewrite <- Z.add_assoc.
        repeat rewrite Z.div_add_l. rewrite Z.mod_div. rewrite Z.add_0_r.
        rewrite Z.mod_div. rewrite Z.add_0_r.
        rewrite Zdiv.Zplus_mod.
        rewrite Z.mod_mul. rewrite Z.add_0_l.
        rewrite Z.mod_mod. rewrite Z.mod_mod.
        rewrite G4 at 2. all: lia.
      } rewrite H0. 
      assert (128 + (n / 64) mod 64 = b3). { 
        unfold n.
        do 2 rewrite <- Z.add_assoc.
        repeat rewrite Z.div_add_l. rewrite Z.mod_div. rewrite Z.add_0_r.
        rewrite Zdiv.Zplus_mod.
        rewrite Z.mod_mul. rewrite Z.add_0_l.
        rewrite Z.mod_mod. rewrite Zdiv.Zplus_mod.
        rewrite Z.mod_mul.  rewrite Z.mod_mod.
        rewrite Z.add_0_l. rewrite Z.mod_mod.
        rewrite G5 at 2. all: lia.
      } rewrite H1. 
      assert (128 + n mod 64 = b4). { 
        unfold n.
        do 2 rewrite <- Z.add_assoc.
        rewrite Zdiv.Zplus_mod.
        rewrite Z.mod_mul at 1. rewrite Z.add_0_l.
        rewrite Zdiv.Zplus_mod.
        rewrite Z.mod_mul at 1. rewrite Z.add_0_l.
        rewrite Zdiv.Zplus_mod.
        rewrite Z.mod_mul at 1. rewrite Z.add_0_l.
        repeat rewrite Z.mod_mod.
        rewrite G6 at 2. all: lia.
      } rewrite H2. reflexivity.
Qed.

Definition inverse_nth_valid_codepoint_representation (bytes: byte_str) : option Z :=
  let between b lo hi := andb (lo <=? b) (b <=? hi) in 
  match bytes with
  | [b] => if between b 0 127 then Some b else None
  | [b1; b2] =>
      if andb (between b1 0xc2 0xdf) (between b2 0x80 0xbf) then
        Some ((b1 mod 64) * 64 + (b2 mod 64))
      else None
  | [b1; b2; b3] =>
      let fst := andb (andb (b1 =? 0xed) (between b2 0x80 0x9f)) (between b3 0x80 0xbf) in
      let snd := andb (andb (b1 =? 0xe0) (between b2 0xa0 0xbf)) (between b3 0x80 0xbf) in
      let trd := andb (andb (between b1 0xe1 0xec) (between b2 0x80 0xbf)) (between b3 0x80 0xbf) in
      let frth := andb (andb (between b1 0xee 0xef) (between b2 0x80 0xbf)) (between b3 0x80 0xbf) in
      if orb (orb (orb fst snd) trd) frth then
        Some (((b1 - 224) * 4096) + (b2 mod 64) * 64 + (b3 mod 64))
      else None
  | [b1; b2; b3; b4] =>
      let fst := andb (andb (andb (b1 =? 0xf0) (between b2 0x90 0xbf)) (between b3 0x80 0xbf)) (between b4 0x80 0xbf) in
      let snd := andb (andb (andb (between b1 0xf1 0xf3) (between b2 0x90 0xbf)) (between b3 0x80 0xbf)) (between b4 0x80 0xbf) in
      let trd := andb (andb (andb (b1 =? 0xf4) (between b2 0x80 0x8f)) (between b3 0x80 0xbf)) (between b4 0x80 0xbf) in
      if orb (orb fst snd) trd then
        Some ((b1 - 240) * 64 * 64 * 64 + (b2 mod 64) * 64 * 64 + (b3 mod 64) * 64 + (b4 mod 64))
      else None
  | _ => None
  end.

Ltac crush_comparisons :=
  repeat match goal with
    | [G: context[if (?a <=? ?b)%N then _ else _] |- _] => 
        let l := fresh "less_than_eq" in
        destruct (a <=? b)%N eqn:l; [apply Z.leb_le in l| apply Z.leb_nle in l]
    | [G: context[if (?a <? ?b)%N then _ else _] |- _] => 
        let l := fresh "less_than" in
        destruct (a <? b)%N eqn:l; [apply Z.ltb_lt in l| apply Z.ltb_nlt in l]
    end.

Lemma list_equals_1 {T}: forall (a b: T), [a] = [b] -> a = b. 
Proof. intros. inversion H. reflexivity. Qed.
Lemma list_equals_2 {T}: forall (a1 a2 b1 b2: T), [a1;a2] = [b1;b2] -> a1 = b1 /\ a2 = b2. 
Proof. intros. inversion H. split; reflexivity. Qed.
Lemma list_equals_3 {T}: forall (a1 a2 a3 b1 b2 b3: T), [a1;a2;a3] = [b1;b2;b3] -> a1 = b1 /\ a2 = b2 /\ a3 = b3.
 Proof. intros. inversion H. do 2 split; reflexivity. Qed.
Lemma list_equals_4 {T}: forall (a1 a2 a3 a4 b1 b2 b3 b4: T), [a1;a2;a3;a4] = [b1;b2;b3;b4] -> a1 = b1 /\ a2 = b2 /\ a3 = b3 /\ a4 = b4. 
Proof. intros. inversion H. do 3 split; reflexivity. Qed.

Theorem nth_valid_codepoint_representation_invertible : forall n bytes,
    nth_valid_codepoint_representation n = Some bytes ->
    inverse_nth_valid_codepoint_representation bytes = Some n.
Proof.
  intros n bytes bytes_nth.
  assert (exists n, nth_valid_codepoint_representation n = Some bytes) as valid_bytes.
  exists n. assumption.
  apply nth_valid_codepoint_representation_spec in valid_bytes.
  unfold inverse_nth_valid_codepoint_representation.
  unfold nth_valid_codepoint_representation in bytes_nth.
  destruct valid_bytes.
  - replace (andb (0 <=? b) (b <=? 127)) with true by lia.
    crush_comparisons; inversion bytes_nth; try lia. reflexivity.
  - crush_comparisons; try discriminate; try lia.
    replace (andb (andb (194 <=? b1) (b1 <=? 223)) (andb (128 <=? b2) (b2 <=? 191))) with true by lia.
    apply some_injective in bytes_nth.
    apply list_equals_2 in bytes_nth. destruct bytes_nth as [G1 G2].
    rewrite <- G1, <- G2.
    rewrite Zdiv.Zplus_mod. rewrite Z.add_0_l.
    rewrite Z.mod_mod; [|lia]. rewrite Zdiv.Zplus_mod.  rewrite Z.add_0_l.
    repeat rewrite Z.mod_mod; try lia.
    specialize (Zdiv.Z_div_mod_eq_full n 64) as G.
    specialize (Z.rem_mul_r n 64 64 ltac:(lia) ltac:(lia)) as G3.
    rewrite Z.add_comm in G3. rewrite Z.mul_comm. rewrite <- G3.
    rewrite <- some_injective.
    apply Z.mod_small; lia.
  - crush_comparisons; try discriminate; try lia;
      match goal with | [|- (if ?cond then _ else _) = _] => replace cond with true by lia end;
      apply some_injective in bytes_nth;
      apply list_equals_3 in bytes_nth; destruct bytes_nth as [b1eq [b2eq b3eq]];
      rewrite <- some_injective; rewrite H; vm_compute (224 - 224); rewrite Z.add_0_l.
    2: { apply Z.nlt_ge in less_than0. rewrite H in b1eq.
         apply (f_equal (fun c => (-224 + c))) in b1eq. rewrite Z.add_assoc in b1eq.
         vm_compute (-224 + 224) in b1eq. rewrite Z.add_0_l in b1eq. rewrite Z.div_div in b1eq; try lia.
         apply Z.add_le_mono_r with (p:=2048) in less_than0.
         apply Zdiv.Z_div_le with (c := 64 * 64) in less_than0. vm_compute ((55296 + 2048) / (64 * 64)) in less_than0. lia. lia. }
    rewrite <- b2eq, <- b3eq. repeat (rewrite Zdiv.Zplus_mod; rewrite Z.add_0_l; rewrite Z.mod_mod; try lia).
    rewrite Z.mod_mod; [|lia]. rewrite Z.mod_mod; [|lia].
    specialize (Z.rem_mul_r n 64 64 ltac:(lia) ltac:(lia)) as G3. rewrite Z.add_comm in G3. rewrite Z.mul_comm. rewrite <- G3.
    rewrite H in b1eq.
    apply (f_equal (fun c => (-224 + c))) in b1eq. rewrite Z.add_assoc in b1eq. vm_compute (-224 + 224) in b1eq.
    rewrite Z.add_0_l in b1eq.
    apply Z.mod_small. split; [lia|].
    specialize (Z.div_small_iff n (64 * 64) ltac:(lia)) as [G1 G2].
    rewrite Z.div_div in b1eq.
    apply G1 in b1eq. destruct b1eq. all: lia.
  - crush_comparisons; try discriminate; try lia;
      match goal with | [|- (if ?cond then _ else _) = _] => replace cond with true by lia end;
      apply some_injective in bytes_nth;
      apply list_equals_3 in bytes_nth; destruct bytes_nth as [b1eq [b2eq b3eq]];
      rewrite <- some_injective; destruct H; rewrite <- b1eq, <- b2eq, <- b3eq.
    + replace (224 + n / 64 / 64 - 224) with (n / 64 / 64) by lia.
      replace ((128 + (n / 64) mod 64) mod 64) with (n / 64 mod 64) by (rewrite Zdiv.Zplus_mod; rewrite Z.add_0_l; repeat rewrite Z.mod_mod; lia).
      replace ((128 + n mod 64) mod 64) with (n mod 64) by (rewrite Zdiv.Zplus_mod; rewrite Z.add_0_l; repeat rewrite Z.mod_mod; lia).
      specialize (Zdiv.Z_div_mod_eq_full n 64) as div_mod.
      specialize (Zdiv.Z_div_mod_eq_full (n / 64) 64) as div_mod2. rewrite div_mod2 in div_mod. lia.
    + replace (224 + n / 64 / 64 - 224) with (n / 64 / 64) by lia.
      replace ((128 + (n / 64) mod 64) mod 64) with (n / 64 mod 64) by (rewrite Zdiv.Zplus_mod; rewrite Z.add_0_l; repeat rewrite Z.mod_mod; lia).
      replace ((128 + n mod 64) mod 64) with (n mod 64) by (rewrite Zdiv.Zplus_mod; rewrite Z.add_0_l; repeat rewrite Z.mod_mod; lia).
      specialize (Zdiv.Z_div_mod_eq_full n 64) as div_mod.
      specialize (Zdiv.Z_div_mod_eq_full (n / 64) 64) as div_mod2. rewrite div_mod2 in div_mod. lia.
    + replace (224 + (n + 2048) / 64 / 64 - 224) with ((n + 2048) / 64 / 64) by lia.
      replace ((128 + ((n + 2048) / 64) mod 64) mod 64) with ((n + 2048) / 64 mod 64) by (rewrite Zdiv.Zplus_mod; rewrite Z.add_0_l; repeat rewrite Z.mod_mod; lia).
      replace ((128 + (n + 2048) mod 64) mod 64) with (n mod 64) by (rewrite Zdiv.Zplus_mod; rewrite Z.add_0_l; rewrite Z.mod_mod; [|lia]; rewrite Zdiv.Zplus_mod; rewrite Z.add_0_r; repeat rewrite Z.mod_mod; lia).  
      specialize (Zdiv.Z_div_mod_eq_full (n + 2048) 64) as div_mod. 
      specialize (Zdiv.Z_div_mod_eq_full ((n + 2048) / 64) 64) as div_mod2. rewrite div_mod2 in div_mod. lia. 
    + replace (224 + (n + 2048) / 64 / 64 - 224) with ((n + 2048) / 64 / 64) by lia.
      replace ((128 + ((n + 2048) / 64) mod 64) mod 64) with (n / 64 mod 64) by (rewrite Zdiv.Zplus_mod with (b:= (n + 2048) mod 64); rewrite Z.add_0_l; rewrite Z.mod_mod; [|lia]; rewrite Zdiv.Zplus_mod; rewrite Z.add_0_r; repeat rewrite Z.mod_mod; lia).
      replace ((128 + (n + 2048) mod 64) mod 64) with (n mod 64) by (rewrite Zdiv.Zplus_mod with (b:= (n + 2048) mod 64); rewrite Z.add_0_l; rewrite Z.mod_mod; [|lia]; rewrite Zdiv.Zplus_mod; rewrite Z.add_0_r; repeat rewrite Z.mod_mod; lia).
      specialize (Zdiv.Z_div_mod_eq_full (n + 2048) 64) as div_mod.
      specialize (Zdiv.Z_div_mod_eq_full ((n + 2048) / 64) 64) as div_mod2. rewrite div_mod2 in div_mod. lia.
      
      
      
Lemma bytes_compare_single : forall b1 b2,
    bytes_compare [b1] [b2] = Z.compare b1 b2.
Proof.
  intros.
  simpl. destruct (Z.compare b1 b2); reflexivity.
Qed.

Lemma byte_compare_length : forall (a b: byte_str),
    valid_codepoint_representation a ->
    valid_codepoint_representation b ->
    ((length a) < (length b))%nat ->
    bytes_compare a b = Lt. 
Proof.
  intros.
  destruct H; destruct H0; simpl in H1; try lia; 
    repeat match goal with
      | [G: ?a <= ?b <= ?c |- _] => 
          destruct G
      end; simpl; 
    let G := fresh "G" in
    match goal with
    | [ |- match (?b1 ?= ?b2) with  | _ => _ end = _ ] =>
        assert (b1 <? b2 = true) as G; try lia; 
        apply Z.ltb_lt in G; rewrite G; reflexivity
    end.
Qed.

Lemma valid_codepoint_representation_length1 : forall n bytes,
    length bytes = 1%nat ->
    nth_valid_codepoint_representation n = Some bytes ->
    0 <= n <= 127.
Proof.
  intros.
  assert (exists n, nth_valid_codepoint_representation n = Some bytes) as E. exists n. assumption.
  apply nth_valid_codepoint_representation_spec in E.
  destruct E; simpl in H; try lia.
  unfold nth_valid_codepoint_representation in H0.
  repeat let eq := fresh "G" in
  match goal with
  | [G: context[if ?a <? ?b then _ else _] |- _] =>
      destruct (a <? b) eqn:eq; try discriminate
  | [G: context[if ?a <=? ?b then _ else _ ] |- _] =>
      destruct (a <=? b) eqn:eq; try discriminate
  end.
  inversion H0. lia. inversion H0. lia.
Qed.


Lemma valid_codepoint_representation_length2 : forall n bytes,
    length bytes = 2%nat ->
    nth_valid_codepoint_representation n = Some bytes ->
    128 <= n <= 0x7ff.
Proof.
  intros.
  assert (exists n, nth_valid_codepoint_representation n = Some bytes) as E. exists n. assumption.
  apply nth_valid_codepoint_representation_spec in E.
  destruct E; simpl in H; try lia.
  unfold nth_valid_codepoint_representation in H0.
  repeat let eq := fresh "G" in
  match goal with
  | [G: context[if ?a <? ?b then _ else _] |- _] =>
      destruct (a <? b) eqn:eq; try discriminate
  | [G: context[if ?a <=? ?b then _ else _ ] |- _] =>
      destruct (a <=? b) eqn:eq; try discriminate
  end.
  inversion H0. lia. inversion H0. lia.
Qed.

Lemma valid_codepoint_representation_length3 : forall n bytes,
    length bytes = 3%nat ->
    nth_valid_codepoint_representation n = Some bytes ->
    0x800 <= n <= (0xffff - 0x800).
Proof.
  intros.
  unfold nth_valid_codepoint_representation in H0.
  assert (exists n, nth_valid_codepoint_representation n = Some bytes) as E. exists n. assumption.
  apply nth_valid_codepoint_representation_spec in E.
  destruct E; simpl in H; try lia.
  all: repeat let eq := fresh "G" in
  match goal with
  | [G: context[if ?a <? ?b then _ else _] |- _] =>
      destruct (a <? b) eqn:eq; try discriminate
  | [G: context[if ?a <=? ?b then _ else _ ] |- _] =>
      destruct (a <=? b) eqn:eq; try discriminate
  end; try lia.
Qed.

Lemma valid_codepoint_representation_length4 : forall n bytes,
    length bytes = 4%nat ->
    nth_valid_codepoint_representation n = Some bytes ->
    (0xffff - 0x7ff) <= n <= (0x10ffff - 0x800).
Proof.
  intros.
  unfold nth_valid_codepoint_representation in H0.
  assert (exists n, nth_valid_codepoint_representation n = Some bytes) as E. exists n. assumption.
  apply nth_valid_codepoint_representation_spec in E.
  destruct E; simpl in H; try lia.
  all: repeat let eq := fresh "G" in
  match goal with
  | [G: context[if ?a <? ?b then _ else _] |- _] =>
      destruct (a <? b) eqn:eq; try discriminate
  | [G: context[if ?a <=? ?b then _ else _ ] |- _] =>
      destruct (a <=? b) eqn:eq; try discriminate
  end; try lia.
Qed.

Lemma byte_compare_antisymm : forall b1 b2,
    bytes_compare b1 b2 = CompOpp (bytes_compare b2 b1).
Proof.
  intros.
  unfold bytes_compare.
  apply list_compare_antisym.
  apply Z.compare_eq_iff.
  apply Z.compare_antisym.
Qed.

Theorem nth_valid_codepoint_representation_compat: forall n1 n2 bytes1 bytes2,
    nth_valid_codepoint_representation n1 = Some bytes1 -> 
    nth_valid_codepoint_representation n2 = Some bytes2 -> 
    Z.compare n1 n2 = bytes_compare bytes1 bytes2.
Proof.
  intros n1 n2 bytes1 bytes2 bytes1_valid bytes2_valid.
  assert (exists n, nth_valid_codepoint_representation n = Some bytes1) as valid_bytes1. exists n1. assumption. 
  assert (exists n, nth_valid_codepoint_representation n = Some bytes2) as valid_bytes2. exists n2. assumption.
  apply nth_valid_codepoint_representation_spec in valid_bytes1, valid_bytes2.
  remember (bytes1).
  remember (bytes2).
  pose (valid1 := valid_bytes1).
  pose (valid2 := valid_bytes2).
  destruct valid_bytes1; destruct valid_bytes2;
  (do 2 let eq := fresh "n_bound" in
  match goal with
  | [L: [?b] = ?bytes, E: nth_valid_codepoint_representation ?n = Some [?b] |- _] =>
      specialize (valid_codepoint_representation_length1 n [b] ltac:(reflexivity) E) as eq;
      clear L
  | [L: [?b; ?b1] = ?bytes, E: nth_valid_codepoint_representation ?n = Some [?b;?b1] |- _] =>
      specialize (valid_codepoint_representation_length2 n [b; b1] ltac:(reflexivity) E) as eq;
      clear L
  | [L: [?b; ?b1; ?b2] = ?bytes, E: nth_valid_codepoint_representation ?n = Some [?b;?b1;?b2] |- _] =>
      specialize (valid_codepoint_representation_length3 n [b; b1; b2] ltac:(reflexivity) E) as eq;
      clear L
  | [L: [?b; ?b1; ?b2; ?b3] = ?bytes, E: nth_valid_codepoint_representation ?n = Some [?b;?b1; ?b2; ?b3] |- _] =>
      specialize (valid_codepoint_representation_length4 n [b; b1; b2; b3] ltac:(reflexivity) E) as eq;
      clear L
  end); try let b_eq := fresh "bytes_compare_eq" in
       match goal with
       | [G1: valid_codepoint_representation [?a1], G2: valid_codepoint_representation [?b1; ?b2] |- _] =>
           specialize (byte_compare_length [a1] [b1; b2] G1 G2 ltac:(simpl in *; lia)) as b_eq
       | [G1: valid_codepoint_representation [?a1], G2: valid_codepoint_representation [?b1; ?b2; ?b3] |- _] =>
           specialize (byte_compare_length [a1] [b1; b2; b3] G1 G2 ltac:(simpl in *; lia)) as b_eq
       | [G1: valid_codepoint_representation [?a1], G2: valid_codepoint_representation [?b1; ?b2; ?b3; ?b4] |- _] =>
           specialize (byte_compare_length [a1] [b1; b2; b3; b4] G1 G2 ltac:(simpl in *; lia)) as b_eq
       | [G1: valid_codepoint_representation [?a1; ?a2], G2: valid_codepoint_representation [?b1; ?b2; ?b3] |- _] =>
           specialize (byte_compare_length [a1; a2] [b1; b2; b3] G1 G2 ltac:(simpl in *; lia)) as b_eq
       | [G1: valid_codepoint_representation [?a1; ?a2], G2: valid_codepoint_representation [?b1; ?b2; ?b3; ?b4] |- _] =>
           specialize (byte_compare_length [a1; a2] [b1; b2; b3; b4] G1 G2 ltac:(simpl in *; lia)) as b_eq
       | [G1: valid_codepoint_representation [?a1; ?a2; ?a3], G2: valid_codepoint_representation [?b1; ?b2; ?b3; ?b4] |- _] =>
           specialize (byte_compare_length [a1; a2; a3] [b1; b2; b3; b4] G1 G2 ltac:(simpl in *; lia)) as b_eq
       end; try match goal with
              | [C: bytes_compare ?a ?b = Lt |- _ = bytes_compare ?a ?b] =>
                rewrite C
              | [C: bytes_compare ?a ?b = Lt |- _ = bytes_compare ?b ?a] =>
                  rewrite byte_compare_antisymm; rewrite C; simpl
              end; try fold (Z.lt n1 n2); try fold (Z.gt n1 n2); try lia.
  all: unfold nth_valid_codepoint_representation in bytes1_valid, bytes2_valid;
  (repeat let eq := fresh "G" in
  match goal with
  | [G: context[if ?a <? ?b then _ else _] |- _] =>
      destruct (a <? b) eqn:eq; try discriminate; try lia
  | [G: context[if ?a <=? ?b then _ else _ ] |- _] =>
      destruct (a <=? b) eqn:eq; try discriminate; try lia
  end);
    (do 2 
        let H1 := fresh "H" in
        let H2 := fresh "H" in
        let H3 := fresh "H" in
        let H4 := fresh "H" in
       match goal with
     | [G: Some [?a] = Some [?b] |- _] =>
      apply some_injective in G; apply list_equals_1 in G; subst
     | [G: Some [?a1; ?a2] = Some [?b1;?b2] |- _] =>
      apply some_injective in G; apply list_equals_2 in G; destruct G; subst
     | [G: Some [?a1; ?a2; ?a3] = Some [?b1;?b2; ?b3] |- _] =>
      apply some_injective in G; apply list_equals_3 in G; destruct G as [H1 [H2 H3]]; subst
     | [G: Some [?a1; ?a2; ?a3; ?a4] = Some [?b1;?b2; ?b3; ?b4] |- _] =>
      apply some_injective in G; apply list_equals_4 in G; destruct G as [H1 [H2 [H3 H4]]]; subst
     end);
    unfold bytes_compare, list_compare.
  Ltac add_bounds G :=
    let mul_div := fresh "mul_div" in
    let div_mod := fresh "div_mod" in
    let mod_bound := fresh "mod_bound" in
    lazymatch G with
    | (?n mod 64)%Z =>
        specialize (Zdiv.Z_div_mod_eq_full n 64) as div_mod;
        specialize (Z.mod_pos_bound n 64 ltac:(lia)) as mod_bound;
        add_bounds n
    | (?n / 64)%Z =>
        specialize (Z.mul_div_le n 64 ltac:(lia)) as mul_div;
        specialize (Zdiv.Z_div_mod_eq_full n 64) as div_mod;
        add_bounds n
    | ?a => idtac 
    end.
  Ltac crush_lia :=
    (repeat 
       let comp_eq := fresh "comp_eq" in
       let range := fresh "range" in
       match goal with
       | [G: (_ \/ _) |- _] =>
           destruct G as [range | range]
       | [|- context[?a + ?b ?= ?a + ?c]] =>
           add_bounds b; add_bounds c;
           destruct (Z.compare_spec (a + b) (a + c)) as [ comp_eq | comp_eq | comp_eq ];
           [ apply (f_equal (fun x => -a + x)) in comp_eq (* when equal *)
           | apply Zorder.Zplus_lt_compat_l with (p:=-a) in comp_eq (* LT *)
           | apply Zorder.Zplus_lt_compat_l with (p:=-a) in comp_eq (* GT *)
           ];
           (repeat rewrite Z.add_assoc in comp_eq);
           replace (-a + a) with 0 in comp_eq by reflexivity;
           (do 2 rewrite Z.add_0_l in comp_eq);
           try rewrite comp_eq in * |- *
       | [|- context[?a ?= ?c + ?b]] =>
           add_bounds b;
           destruct (Z.compare_spec a (c + b)) as [ comp_eq | comp_eq | comp_eq ];
           [ apply (f_equal (fun x => -a + x)) in comp_eq (* when equal *)
           | apply Zorder.Zplus_lt_compat_l with (p:=-a) in comp_eq (* LT *)
           | apply Zorder.Zplus_lt_compat_l with (p:=-a) in comp_eq (* GT *)
           ];
           (repeat rewrite Z.add_assoc in comp_eq);
           vm_compute (-a + c) in comp_eq;
           try rewrite Z.add_0_l in comp_eq;
           try rewrite comp_eq in * |- *
       | [H: ?a + ?b = ?a |- context[?a ?= ?a + ?b]] =>
           rewrite H; rewrite Z.compare_refl
       | [H: ?a = ?a + ?b |- context[?a ?= ?a + ?b]] =>
           rewrite H; rewrite Z.compare_refl
       end);
    (do 3 try match goal with
       | [H1: (?a / ?b) = _, H2: context[?c * (?a / ?b)] |- _] =>
           rewrite H1 in H2
       end);
    match goal with       
    | [|- (?n1 ?= ?n2 = Eq)] => apply Z.compare_eq_iff
    | [|- (?n1 ?= ?n2 = Lt)] => fold (Z.lt n1 n2)
    | [|- (?n1 ?= ?n2 = Gt)] => fold (Z.gt n1 n2)
    | [ |- ?g] => idtac
    end.
  1: destruct (b ?= b0); reflexivity.
  par: crush_lia; try lia.
Qed.

  
Lemma list_compare_refl_if {T} (cmp: T -> T -> comparison) : forall (t: list T),
    (forall x y, cmp x y = Eq <-> x = y) ->
    list_compare cmp t t = Eq.
Proof.
  intros t cmp_eq.
  apply list_compare_refl; [| reflexivity].
  apply cmp_eq.
Qed.

