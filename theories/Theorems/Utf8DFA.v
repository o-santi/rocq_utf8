Require Import Utf8.Parser.
Require Import Utf8.Utf8.
Require Import Utf8.Utf8DFA.
Require Import Utf8.Theorems.Parser.
Require Import Utf8.Theorems.Utf8.

From Stdlib Require Import Strings.Byte.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lia.

Local Notation "0" := false.
Local Notation "1" := true.
Definition zero_codep : codepoint := (0, b4_zero, b4_zero, b4_zero, b4_zero, b4_zero).

(* The character sequence U+0041 U+2262 U+0391 U+002E "A<NOT IDENTICAL
   TO><ALPHA>." is encoded in UTF-8 as follows: *)

(*     --+--------+-----+-- *)
(*     41 E2 89 A2 CE 91 2E *)
(*     --+--------+-----+-- *)
Definition test1 :
  (fmap (fun '(s, r) => (List.map show_codepoint s, r)) (utf8_dfa_decode [x41; xe2; x89; xa2; xce; x91; x2e]))
  = Ok (["U+0041"%string; "U+2262"%string; "U+0391"%string; "U+002E"%string], []).
  simpl.
  reflexivity.
Qed.

(* The character sequence U+D55C U+AD6D U+C5B4 (Korean "hangugeo", *)
(* meaning "the Korean language") is encoded in UTF-8 as follows: *)

(*     --------+--------+-------- *)
(*     ED 95 9C EA B5 AD EC 96 B4 *)
(*     --------+--------+-------- *)
Definition test2 :
  (fmap (fun '(s, r) => (List.map show_codepoint s, r)) (utf8_dfa_decode [xed; x95; x9c; xea; xb5; xad; xec; x96; xb4]))
  = Ok (["U+D55C"%string; "U+AD6D"%string; "U+C5B4"%string], []).
  reflexivity.
Qed.


(* The character sequence U+65E5 U+672C U+8A9E (Japanese "nihongo", *)
(* meaning "the Japanese language") is encoded in UTF-8 as follows: *)

(*     --------+--------+-------- *)
(*     E6 97 A5 E6 9C AC E8 AA 9E *)
(*     --------+--------+-------- *)
Definition test3 :
  (fmap (fun '(s, r) => (List.map show_codepoint s, r)) (utf8_dfa_decode [xe6; x97; xa5; xe6; x9c; xac; xe8; xaa; x9e]))
  = Ok (["U+65E5"%string; "U+672C"%string; "U+8A9E"%string], []).
  reflexivity.
Qed.

(* The character U+233B4 (a Chinese character meaning 'stump of tree'), *)
(* prepended with a UTF-8 BOM, is encoded in UTF-8 as follows: *)

(*     --------+----------- *)
(*     EF BB BF F0 A3 8E B4 *)
(*     --------+----------- *)

Definition test4 :
  (fmap (fun '(s, r) => (List.map show_codepoint s, r)) (utf8_dfa_decode [xef; xbb; xbf; xf0; xa3; x8e; xb4]))
  = Ok (["U+FEFF"%string; "U+0233B4"%string], []).
  reflexivity.
Qed.


Lemma byte_range_00_7f_bits : forall b,
    byte_range b = Range_00_7F ->
    exists b1 b2 b3 b4 b5 b6 b7,
      Byte.to_bits b = (b1, (b2, (b3, (b4, (b5, (b6, (b7, 0))))))).
Proof.
  intros.
  destruct b; inversion H; repeat eexists.
Qed.

Lemma byte_range_80_8f_bits : forall b,
    byte_range b = Range_80_8F ->
    exists b1 b2 b3 b4,
      Byte.to_bits b = (b1, (b2, (b3, (b4, (0, (0, (0, 1))))))).
Proof.
  intros.
  destruct b; inversion H; repeat eexists.
Qed.

Lemma byte_range_90_9f_bits : forall b,
    byte_range b = Range_90_9F ->
    exists b1 b2 b3 b4,
      Byte.to_bits b = (b1, (b2, (b3, (b4, (1, (0, (0, 1))))))).
Proof.
  intros.
  destruct b; inversion H; repeat eexists.
Qed.

Lemma byte_range_a0_bf_bits : forall b,
    byte_range b = Range_A0_BF ->
    exists b1 b2 b3 b4 b5,
      Byte.to_bits b = (b1, (b2, (b3, (b4, (b5, (1, (0, 1))))))).
Proof.
  intros.
  - destruct b; inversion H; repeat eexists.
Qed.

Lemma byte_range_c0_c1_bits : forall b,
    byte_range b = Range_C0_C1 ->
    exists b1,
      Byte.to_bits b = (b1, (0, (0, (0, (0, (0, (1, 1))))))).
Proof.
  intros.
  destruct b; inversion H; repeat eexists.
Qed.

Lemma byte_range_c2_df_bits : forall b,
    byte_range b = Range_C2_DF ->
    exists b1 b2 b3 b4 b5,
      (Byte.to_bits b = (b1, (b2, (b3, (b4, (b5, (0, (1, 1))))))) /\
       (b3 = 1 \/ b4 = 1 \/ b5 = 1 \/ b2 = 1)).
Proof.
  intros.
  destruct b; inversion H; repeat eexists; auto. 
Qed.

Lemma byte_e0_bits : forall b,
    byte_range b = Byte_E0 ->
    (Byte.to_bits b = (0, (0, (0, (0, (0, (1, (1, 1)))))))).
Proof.
  intros.
  destruct b; inversion H; reflexivity.
Qed.

Lemma byte_range_e1_ec_bits : forall b,
    byte_range b = Range_E1_EC ->
    exists b1 b2 b3 b4,
      Byte.to_bits b = (b1, (b2, (b3, (b4, (0, (1, (1, 1))))))) /\ ((b1 = 1 \/ b2 = 1 \/ b3 = 1 \/ b4 = 1) /\ (b3 = 0 \/ b4 = 0 \/ (b1 = 0 /\ b2 = 0))).
Proof.
  intros.
  destruct b; inversion H; repeat eexists; auto.
Qed.


Lemma byte_ed_bits : forall b,
    byte_range b = Byte_ED ->
    (Byte.to_bits b = (1, (0, (1, (1, (0, (1, (1, 1)))))))).
Proof.
  intros.
  destruct b; inversion H; reflexivity.
Qed.


Lemma byte_range_ee_ef_bits : forall b,
    byte_range b = Range_EE_EF ->
    exists bit,
      Byte.to_bits b = (bit, (1, (1, (1, (0, (1, (1, 1))))))).
Proof.
  intros.
  destruct b; inversion H; repeat eexists.
Qed.

Lemma byte_f0_bits : forall b,
    byte_range b = Byte_F0 ->
    Byte.to_bits b = (0, (0, (0, (0, (1, (1, (1, 1))))))).
Proof.
  intros.
  destruct b; inversion H; reflexivity.
Qed.


Lemma byte_range_f1_f3_bits : forall b,
    byte_range b = Range_F1_F3 ->
    exists b1 b2,
      Byte.to_bits b = (b1, (b2, (0, (0, (1, (1, (1, 1))))))) /\
        (b2 = 1 \/ b1 = 1).
Proof.
  intros.
  destruct b; inversion H; repeat eexists; auto.
Qed.

Lemma byte_f4_bits : forall b,
    byte_range b = Byte_F4 ->
    Byte.to_bits b = (0, (0, (1, (0, (1, (1, (1, 1))))))).
Proof.
  intros.
  destruct b; inversion H; reflexivity.
Qed.


Lemma byte_range_f5_ff_bits : forall b,
    byte_range b = Range_F5_FF ->
    exists b1 b2 b3 b4,
      Byte.to_bits b = (b1, (b2, (b3, (b4, (1, (1, (1, 1))))))).
Proof.
  intros.
  destruct b; inversion H; repeat eexists.
Qed.

Lemma byte_range_of_bits_00_7f: forall b1 b2 b3 b4 b5 b6 b7,
    byte_range (of_bits (b1, (b2, (b3, (b4, (b5, (b6, (b7, 0)))))))) = Range_00_7F.
Proof.
  intros.
  destruct (of_bits (b1, (b2, (b3, (b4, (b5, (b6, (b7, 0)))))))) eqn:H;
    apply (f_equal Byte.to_bits) in H;
    rewrite Byte.to_bits_of_bits in H;
    inversion H;
    reflexivity.
Qed.

Lemma byte_range_of_bits_c2_df: forall b1 b2 b3 b4 b5,
    (b2 = 1 \/ b3 = 1 \/ b4 = 1 \/ b5 = 1) ->
    byte_range (of_bits (b1, (b2, (b3, (b4, (b5, (0, (1, 1)))))))) = Range_C2_DF.
Proof.
  intros.
  destruct (of_bits (b1, (b2, (b3, (b4, (b5, (0, (1, 1)))))))) eqn:H2;
    apply (f_equal Byte.to_bits) in H2;
    rewrite Byte.to_bits_of_bits in H2;
    inversion H2;
    try reflexivity; destruct H as [G | [G | [G | G]]]; subst;
    match goal with
    | [F: 1 = 0 |- _] => apply Bool.diff_true_false in F; destruct F
    end.
Qed.

Lemma byte_range_of_bits_a0_bf: forall b1 b2 b3 b4 b5,
    byte_range (of_bits (b1, (b2, (b3, (b4, (b5, (1, (0, 1)))))))) = Range_A0_BF.
Proof.
  intros.
  destruct (of_bits (b1, (b2, (b3, (b4, (b5, (1, (0, 1)))))))) eqn:H;
    apply (f_equal Byte.to_bits) in H;
    rewrite Byte.to_bits_of_bits in H;
    inversion H;
    reflexivity.
Qed.

Lemma byte_range_of_bits_80_8f: forall (b1 b2 b3 b4: bool),
    byte_range (of_bits (b1, (b2, (b3, (b4, (0, (0, (0, 1)))))))) = Range_80_8F.
Proof.
  intros.
  destruct (of_bits (b1, (b2, (b3, (b4, (0, (0, (0, 1)))))))) eqn:H;
    apply (f_equal Byte.to_bits) in H;
    rewrite Byte.to_bits_of_bits in H;
    inversion H;
    auto.
Qed.


Lemma byte_range_of_bits_80_9f: forall (b1 b2 b3 b4 b5: bool),
    let b := of_bits (b1, (b2, (b3, (b4, (b5, (0, (0, 1))))))) in
    (byte_range b = Range_80_8F) \/
      (byte_range b = Range_90_9F).
Proof.
  intros.
  destruct b eqn:H;
    apply (f_equal Byte.to_bits) in H;
    subst b;
    rewrite Byte.to_bits_of_bits in H;
    inversion H;
    auto.
Qed.


Lemma byte_range_of_bits_80_bf: forall (b1 b2 b3 b4 b5 b6: bool),
    let b := of_bits (b1, (b2, (b3, (b4, (b5, (b6, (0, 1))))))) in
    (byte_range b = Range_80_8F) \/
      (byte_range b = Range_90_9F) \/
      (byte_range b = Range_A0_BF).
Proof.
  intros.
  destruct b eqn:H;
    apply (f_equal Byte.to_bits) in H;
    subst b;
    rewrite Byte.to_bits_of_bits in H;
    inversion H;
    auto.
Qed.

Lemma byte_range_of_bits_90_9f: forall (b1 b2 b3 b4: bool),
    let b := of_bits (b1, (b2, (b3, (b4, (1, (0, (0, 1))))))) in
    (byte_range b = Range_90_9F).
Proof.
  intros.
  destruct b eqn:H;
    apply (f_equal Byte.to_bits) in H;
    subst b;
    rewrite Byte.to_bits_of_bits in H;
    inversion H;
    auto.
Qed.


Lemma byte_range_of_bits_ee_ef: forall (bit: bool),
    let b := of_bits (bit, (1, (1, (1, (0, (1, (1, 1))))))) in
    byte_range b = Range_EE_EF.
Proof.
  intros.
  destruct b eqn:H;
    apply (f_equal Byte.to_bits) in H;
    subst b;
    rewrite Byte.to_bits_of_bits in H;
    inversion H;
    auto.
Qed.

Lemma next_state_initial_00_7f :
  forall b1 b2 b3 b4 b5 b6 b7,
    let b := (of_bits (b7, (b6, (b5, (b4, (b3, (b2, (b1, 0)))))))) in
    next_state Initial zero_codep b
    = Ok (Finished (0, b4_zero, b4_zero, b4_zero, (0, b1, b2, b3), (b4, b5, b6, b7))).
Proof.
  intros.
  unfold next_state. subst b.
  pose proof (byte_range_of_bits_00_7f b7 b6 b5 b4 b3 b2 b1) as G.
  rewrite G.
  unfold extract_7_bits.
  rewrite Byte.to_bits_of_bits.
  reflexivity.
Qed.

Lemma next_state_initial_c2_df :
  forall b1 b2 b3 b4 b5, (b1 = 1 \/ b2 = 1 \/ b3 = 1 \/ b4 = 1) ->
    let b := (of_bits (b5, (b4, (b3, (b2, (b1, (0, (1, 1)))))))) in
    next_state Initial zero_codep b
    = Ok (More Expecting_1_80_BF (0, b4_zero, b4_zero, b4_zero, (0, 0, 0, b1), (b2, b3, b4, b5))).
Proof.
  intros.
  unfold next_state. subst b.
  pose proof (byte_range_of_bits_c2_df b5 b4 b3 b2 b1) as G.
  rewrite G.
  unfold extract_5_bits.
  rewrite Byte.to_bits_of_bits.
  reflexivity.
  destruct H as [F | [F | [F | F]]]; auto.
Qed.

Lemma next_state_initial_e1_ec :
  forall b1 b2 b3 b4,
    ((b1 = 1 \/ b2 = 1 \/ b3 = 1 \/ b4 = 1) /\ (b3 = 0 \/ b4 = 0 \/ (b1 = 0 /\ b2 = 0))) ->
  let b := (of_bits (b1, (b2, (b3, (b4, (0, (1, (1, 1)))))))) in
  next_state Initial zero_codep b
  = Ok (More Expecting_2_80_BF (0, b4_zero, b4_zero, b4_zero, b4_zero, (b4, b3, b2, b1))).
Proof.
  intros.
  unfold next_state,  extract_4_bits. destruct b eqn:B; subst b;
    apply (f_equal Byte.to_bits) in B; rewrite Byte.to_bits_of_bits in B; try discriminate; inversion B; try reflexivity;
    destruct H as [[G1 | [G1 | [G1 | G1]]] [G2 | [G2 | [G2 G3]]]]; subst;
    match goal with
      | [F: 0 = 1 |- _] => symmetry in F; apply Bool.diff_true_false in F; destruct F
      | [F: 1 = 0 |- _] => apply Bool.diff_true_false in F; destruct F
      end.
Qed.

Lemma next_state_initial_e0 :
    let b := (of_bits (0, (0, (0, (0, (0, (1, (1, 1)))))))) in
    next_state Initial zero_codep b
    = Ok (More Expecting_2_A0_BF (0, b4_zero, b4_zero, b4_zero, b4_zero, (0, 0, 0, 0))).
Proof.
  intros.
  unfold next_state. destruct b eqn:B; subst b;
  apply (f_equal Byte.to_bits) in B; rewrite Byte.to_bits_of_bits in B; try discriminate.
  unfold extract_4_bits.
  reflexivity.
Qed.

  
Lemma next_state_initial_ed :
    next_state Initial zero_codep (of_bits (1, (0, (1, (1, (0, (1, (1, 1))))))))
    = Ok (More Expecting_2_80_9F (0, b4_zero, b4_zero, b4_zero, (0, 0, 0, 0), (1, 1, 0, 1))).
Proof.
  intros.
  unfold next_state. destruct (of_bits (1, (0, (1, (1, (0, (1, (1, 1)))))))) eqn:B;
  apply (f_equal Byte.to_bits) in B; rewrite Byte.to_bits_of_bits in B; try discriminate.
  unfold extract_4_bits.
  reflexivity.
Qed.

Lemma next_state_initial_ee_ef :
  forall bit, 
    let b := (of_bits (bit, (1, (1, (1, (0, (1, (1, 1)))))))) in
    next_state Initial zero_codep b
    = Ok (More Expecting_2_80_BF (0, b4_zero, b4_zero, b4_zero, (0, 0, 0, 0), (1, 1, 1, bit))).
Proof.
  intros.
  unfold next_state. subst b.
  pose proof (byte_range_of_bits_ee_ef bit) as G.
  rewrite G.
  unfold extract_4_bits.
  rewrite Byte.to_bits_of_bits.
  reflexivity.
Qed.

Lemma next_state_initial_f1_f3 :
  forall b1 b2, (b2 = 1 \/ b1 = 1) ->
    let b := (of_bits (b1, (b2, (0, (0, (1, (1, (1, 1)))))))) in
    next_state Initial zero_codep b
    = Ok (More Expecting_3_80_BF (0, b4_zero, b4_zero, b4_zero, b4_zero, (0, 0, b2, b1))).
Proof.
  intros.
  unfold next_state. destruct b eqn:B; subst b;
  apply (f_equal Byte.to_bits) in B; rewrite Byte.to_bits_of_bits in B; try discriminate;
    unfold extract_3_bits;
    inversion B; subst;
    try reflexivity; destruct H; match goal with
      | [F: 0 = 1 |- _] => symmetry in F; apply Bool.diff_true_false in F; destruct F
      | [F: 1 = 0 |- _] => apply Bool.diff_true_false in F; destruct F
      end.
Qed.

Lemma next_state_initial_f0 :
  let b := (of_bits (0, (0, (0, (0, (1, (1, (1, 1)))))))) in
  next_state Initial zero_codep b
  = Ok (More Expecting_3_90_BF (0, b4_zero, b4_zero, b4_zero, b4_zero, (0, 0, 0, 0))).
Proof.
  intros.
  unfold next_state. destruct b eqn:B; subst b;
  apply (f_equal Byte.to_bits) in B; rewrite Byte.to_bits_of_bits in B; try discriminate.
  unfold extract_3_bits.
  reflexivity.
Qed.

Lemma next_state_initial_f4 :
  let b := (of_bits (0, (0, (1, (0, (1, (1, (1, 1)))))))) in
  next_state Initial zero_codep b
  = Ok (More Expecting_3_80_8F (0, b4_zero, b4_zero, b4_zero, b4_zero, (0, 1, 0, 0))).
Proof.
  intros.
  unfold next_state. destruct b eqn:B; subst b;
  apply (f_equal Byte.to_bits) in B; rewrite Byte.to_bits_of_bits in B; try discriminate.
  unfold extract_3_bits.
  reflexivity.
Qed.

Lemma next_state_expecting_1_80_bf :
  forall c1 c2 c3 c4 c5 c6
    b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21,
    let b := (of_bits (b21, (b20, (b19, (b18, (b17, (b16, (0, 1)))))))) in
    next_state Expecting_1_80_BF (c1, (c2, c3, c4, c5), (c6, b1, b2, b3), (b4, b5, b6, b7), (b8, b9, b10, b11), (b12, b13, b14, b15)) b
    = Ok (Finished (b1, (b2, b3, b4, b5), (b6, b7, b8, b9), (b10, b11, b12, b13), (b14, b15, b16, b17), (b18, b19, b20, b21))).
Proof.
  intros.
  unfold next_state. subst b.
  pose proof (byte_range_of_bits_80_bf b21 b20 b19 b18 b17 b16) as [G | [G | G]]; rewrite G;
    unfold push_bottom_bits;
    rewrite Byte.to_bits_of_bits; reflexivity.
Qed.

Lemma next_state_expecting_2_80_bf :
  forall c1 c2 c3 c4 c5 c6
    b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21,
    let b := (of_bits (b21, (b20, (b19, (b18, (b17, (b16, (0, 1)))))))) in 
    next_state Expecting_2_80_BF (c1, (c2, c3, c4, c5), (c6, b1, b2, b3), (b4, b5, b6, b7), (b8, b9, b10, b11), (b12, b13, b14, b15)) b
    = Ok (More Expecting_1_80_BF (b1, (b2, b3, b4, b5), (b6, b7, b8, b9), (b10, b11, b12, b13), (b14, b15, b16, b17), (b18, b19, b20, b21))).
Proof.
  intros.
  unfold next_state. subst b.
  pose proof (byte_range_of_bits_80_bf b21 b20 b19 b18 b17 b16) as [G | [G | G]]; rewrite G;
    unfold push_bottom_bits;
    rewrite Byte.to_bits_of_bits; reflexivity.
Qed.


Lemma next_state_expecting_2_80_9f :
  forall c1 c2 c3 c4 c5 c6
    b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b17 b18 b19 b20 b21,
    let b := (of_bits (b21, (b20, (b19, (b18, (b17, (0, (0, 1)))))))) in 
    next_state Expecting_2_80_9F (c1, (c2, c3, c4, c5), (c6, b1, b2, b3), (b4, b5, b6, b7), (b8, b9, b10, b11), (b12, b13, b14, b15)) b
    = Ok (More Expecting_1_80_BF (b1, (b2, b3, b4, b5), (b6, b7, b8, b9), (b10, b11, b12, b13), (b14, b15, 0, b17), (b18, b19, b20, b21))).
Proof.
  intros.
  unfold next_state. subst b.
  pose proof (byte_range_of_bits_80_9f b21 b20 b19 b18 b17) as [G | G]; rewrite G;
    unfold push_bottom_bits;
    rewrite Byte.to_bits_of_bits; reflexivity.
Qed.

Lemma next_state_expecting_3_80_bf :
  forall c1 c2 c3 c4 c5 c6
    b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21,
    let b := (of_bits (b21, (b20, (b19, (b18, (b17, (b16, (0, 1)))))))) in 
    next_state Expecting_3_80_BF (c1, (c2, c3, c4, c5), (c6, b1, b2, b3), (b4, b5, b6, b7), (b8, b9, b10, b11), (b12, b13, b14, b15)) b
    = Ok (More Expecting_2_80_BF (b1, (b2, b3, b4, b5), (b6, b7, b8, b9), (b10, b11, b12, b13), (b14, b15, b16, b17), (b18, b19, b20, b21))).
Proof.
  intros.
  unfold next_state. subst b.
  pose proof (byte_range_of_bits_80_bf b21 b20 b19 b18 b17 b16) as [G | [G | G]]; rewrite G;
    unfold push_bottom_bits;
    rewrite Byte.to_bits_of_bits; reflexivity.
Qed.

Lemma next_state_expecting_3_80_8f :
  forall c1 c2 c3 c4 c5 c6
    b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b18 b19 b20 b21,
    let b := (of_bits (b21, (b20, (b19, (b18, (0, (0, (0, 1)))))))) in
    next_state Expecting_3_80_8F (c1, (c2, c3, c4, c5), (c6, b1, b2, b3), (b4, b5, b6, b7), (b8, b9, b10, b11), (b12, b13, b14, b15)) b
    = Ok (More Expecting_2_80_BF (b1, (b2, b3, b4, b5), (b6, b7, b8, b9), (b10, b11, b12, b13), (b14, b15, 0, 0), (b18, b19, b20, b21))).
Proof.
  intros.
  unfold next_state. subst b.
  pose proof (byte_range_of_bits_80_8f b21 b20 b19 b18) as G.
  rewrite G.
  unfold push_bottom_bits.
  rewrite Byte.to_bits_of_bits. reflexivity.
Qed.

Lemma next_state_expecting_3_90_bf_p1 :
  forall c1 c2 c3 c4 c5 c6
    b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b17 b18 b19 b20 b21,
    let b := (of_bits (b21, (b20, (b19, (b18, (b17, (1, (0, 1)))))))) in 
    next_state Expecting_3_90_BF (c1, (c2, c3, c4, c5), (c6, b1, b2, b3), (b4, b5, b6, b7), (b8, b9, b10, b11), (b12, b13, b14, b15)) b
    = Ok (More Expecting_2_80_BF (b1, (b2, b3, b4, b5), (b6, b7, b8, b9), (b10, b11, b12, b13), (b14, b15, 1, b17), (b18, b19, b20, b21))).
Proof.
  intros.
  unfold next_state. subst b.
  pose proof (byte_range_of_bits_a0_bf b21 b20 b19 b18 b17) as G.
  rewrite G.
  unfold push_bottom_bits.
  rewrite Byte.to_bits_of_bits; reflexivity.
Qed.

Lemma next_state_expecting_3_90_bf_p2 :
  forall c1 c2 c3 c4 c5 c6
    b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b18 b19 b20 b21,
    let b := (of_bits (b21, (b20, (b19, (b18, (1, (0, (0, 1)))))))) in 
    next_state Expecting_3_90_BF (c1, (c2, c3, c4, c5), (c6, b1, b2, b3), (b4, b5, b6, b7), (b8, b9, b10, b11), (b12, b13, b14, b15)) b
    = Ok (More Expecting_2_80_BF (b1, (b2, b3, b4, b5), (b6, b7, b8, b9), (b10, b11, b12, b13), (b14, b15, 0, 1), (b18, b19, b20, b21))).
Proof.
  intros.
  unfold next_state. subst b.
  pose proof (byte_range_of_bits_90_9f b21 b20 b19 b18) as G; rewrite G;
    unfold push_bottom_bits;
    rewrite Byte.to_bits_of_bits; reflexivity.
Qed.

Lemma next_state_expecting_2_a0_bf :
  forall c1 c2 c3 c4 c5 c6
    b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b17 b18 b19 b20 b21,
    let b := (of_bits (b21, (b20, (b19, (b18, (b17, (1, (0, 1)))))))) in
    next_state Expecting_2_A0_BF (c1, (c2, c3, c4, c5), (c6, b1, b2, b3), (b4, b5, b6, b7), (b8, b9, b10, b11), (b12, b13, b14, b15)) b
    = Ok (More Expecting_1_80_BF (b1, (b2, b3, b4, b5), (b6, b7, b8, b9), (b10, b11, b12, b13), (b14, b15, 1, b17), (b18, b19, b20, b21))).
Proof.
  intros.
  unfold next_state. subst b.
  pose proof (byte_range_of_bits_a0_bf b21 b20 b19 b18 b17) as G. rewrite G.
  unfold push_bottom_bits.
  rewrite Byte.to_bits_of_bits. reflexivity.
Qed.

Lemma if_redundant : forall T (P: T) (b: bool), (if b then P else P) = P.
Proof.
  destruct b; reflexivity.
Qed.

Ltac next_state_DFA_run :=
  unfold b4_zero;
  lazymatch goal with
  | [ |- context[next_state Initial           ?code (of_bits (?b1, (?b2, (?b3, (?b4, (?b5, (?b6, (?b7, 0))))))))]] => rewrite next_state_initial_00_7f; simpl
  | [ |- context[next_state Expecting_1_80_BF ?code (of_bits (?b0, (?b1, (?b2, (?b3, (?b4, (?b5, (0, 1))))))))]]   => rewrite next_state_expecting_1_80_bf; simpl
  | [ |- context[next_state Initial           ?code (of_bits (?b0, (?b1, (?b2, (?b3, (?b4, (0, (1, 1))))))))]]     => rewrite next_state_initial_c2_df; auto; simpl; next_state_DFA_run
  | [ |- context[next_state Initial           ?code (of_bits (0, (0, (0, (0, (0, (1, (1, 1))))))))]]               => rewrite next_state_initial_e0; simpl; next_state_DFA_run
  | [ |- context[next_state Initial           ?code (of_bits (1, (0, (1, (1, (0, (1, (1, 1))))))))]]               => rewrite next_state_initial_ed; simpl; next_state_DFA_run
  | [ |- context[next_state Initial           ?code (of_bits (?b, (1, (1, (1, (0, (1, (1, 1))))))))]]              => rewrite next_state_initial_ee_ef; simpl; next_state_DFA_run
  | [ |- context[next_state Initial           ?code (of_bits (?b0, (?b1, (?b2, (?b3, (0, (1, (1, 1))))))))]]       => rewrite next_state_initial_e1_ec; auto; simpl; next_state_DFA_run
  | [ |- context[next_state Initial           ?code (of_bits (0, (0, (0, (0, (1, (1, (1, 1))))))))]]               => rewrite next_state_initial_f0; simpl; next_state_DFA_run
  | [ |- context[next_state Initial           ?code (of_bits (0, (0, (1, (0, (1, (1, (1, 1))))))))]]               => rewrite next_state_initial_f4; simpl; next_state_DFA_run
  | [ |- context[next_state Initial           ?code (of_bits (?b0, (?b1, (0, (0, (1, (1, (1, 1))))))))]]           => rewrite next_state_initial_f1_f3; auto; simpl; next_state_DFA_run
  | [ |- context[next_state Expecting_2_80_9F ?code (of_bits (?b0, (?b1, (?b2, (?b3, (?b4, (0, (0, 1))))))))]]     => rewrite next_state_expecting_2_80_9f; simpl; next_state_DFA_run
  | [ |- context[next_state Expecting_2_A0_BF ?code (of_bits (?b0, (?b1, (?b2, (?b3, (?b4, (1, (0, 1))))))))]]     => rewrite next_state_expecting_2_a0_bf; simpl; next_state_DFA_run
  | [ |- context[next_state Expecting_2_80_BF ?code (of_bits (?b0, (?b1, (?b2, (?b3, (?b4, (?b5, (0, 1))))))))]]   => rewrite next_state_expecting_2_80_bf; simpl; next_state_DFA_run
  | [ |- context[next_state Expecting_3_80_8F ?code (of_bits (?b0, (?b1, (?b2, (?b3, (0, (0, (0, 1))))))))]]       => rewrite next_state_expecting_3_80_8f; simpl; next_state_DFA_run
  | [ |- context[next_state Expecting_3_90_BF ?code (of_bits (?b0, (?b1, (?b2, (?b3, (?b4, (1, (0, 1))))))))]]     => rewrite next_state_expecting_3_90_bf_p1; simpl; next_state_DFA_run
  | [ |- context[next_state Expecting_3_90_BF ?code (of_bits (?b0, (?b1, (?b2, (?b3, (1, (0, (0, 1))))))))]]       => rewrite next_state_expecting_3_90_bf_p2; simpl; next_state_DFA_run
  | [ |- context[next_state Expecting_3_80_BF ?code (of_bits (?b0, (?b1, (?b2, (?b3, (?b4, (?b5, (0, 1))))))))]]   => rewrite next_state_expecting_3_80_bf; simpl; next_state_DFA_run
  | _                                                                                                             => idtac
  end.

Theorem utf8_decoders_equal_left_strong : forall (bytes less: list byte) code rest,
    (List.length less) <= (List.length bytes) ->
    utf8_decode less = Ok (code, rest) -> utf8_dfa_decode less = Ok (code, rest).
Proof.
  Opaque Byte.of_bits.
  intros bytes.
  induction bytes; intros less code rest LessLesser Utf8DecodeOk; [ inversion LessLesser; rewrite List.length_zero_iff_nil in H0; subst; inversion Utf8DecodeOk; reflexivity  | ].
  destruct less; [ inversion Utf8DecodeOk; reflexivity | ].
  unfold utf8_decode, all, all_aux in Utf8DecodeOk. fold (all_aux parse_codepoint).
  destruct (parse_codepoint (b:: less)) as [[parsed_code unparsed_rest] | err] eqn:ParseB; [ | discriminate Utf8DecodeOk].
  rewrite <- all_aux_saturation_aux with (n := (S (S (Datatypes.length unparsed_rest)))) in Utf8DecodeOk.
  2: apply parse_codepoint_strong_progress.
  2, 3: apply parse_codepoint_strong_progress in ParseB; simpl in *; lia.
  fold (all parse_codepoint unparsed_rest) in Utf8DecodeOk. fold (utf8_decode unparsed_rest) in Utf8DecodeOk.
  destruct (utf8_decode unparsed_rest) as [[parsed_rest_codes unparsed_rest_rest] | err] eqn:Utf8DecodeRestOk; [| discriminate Utf8DecodeOk].
  inversion Utf8DecodeOk; subst.
  apply IHbytes in Utf8DecodeRestOk. 2: apply parse_codepoint_strong_progress in ParseB; simpl in *; lia.

  unfold parse_codepoint, parse_header, encoding_size_from_header in ParseB. to_bits b.
  unfold utf8_dfa_decode, utf8_dfa_decode_rec.
  fold utf8_dfa_decode_rec. fold (utf8_dfa_decode less).

  crush_bits; try discriminate; simpl in ParseB; rewrite byte_bits;
    try (inversion ParseB; subst; next_state_DFA_run; rewrite Utf8DecodeRestOk; reflexivity).
  1,3,5: destruct_parse_continuation; inversion ParseB; subst; next_state_DFA_run; fold (utf8_dfa_decode unparsed_rest); rewrite Utf8DecodeRestOk; reflexivity.
  1: { destruct (parse_continuation less) as [[snd less_rest] | err] eqn:ParseContLess; try discriminate; simpl in ParseB;
      destruct (parse_continuation less_rest) as [[trd less_rest2] | err] eqn:ParseContLessRest; try discriminate; simpl in ParseB;
       repeat destruct_parse_continuation; to_bits snd; to_bits trd.
      crush_bits; inversion ParseB; inversion ParseContLess; inversion ParseContLessRest; subst. 2: { Show. rewrite next_state_initial_ed.
  1,3: destruct (parse_continuation less) as [[snd less_rest] | err] eqn:ParseContLess; try discriminate; simpl in ParseB;
      destruct (parse_continuation less_rest) as [[trd less_rest2] | err] eqn:ParseContLessRest; try discriminate; simpl in ParseB;
      repeat destruct_parse_continuation; to_bits snd; to_bits trd;
      crush_bits; inversion ParseB; inversion ParseContLess; inversion ParseContLessRest; subst;
      next_state_DFA_run; fold (utf8_dfa_decode unparsed_rest); rewrite Utf8DecodeRestOk; reflexivity. 
  - destruct (parse_continuation less) as [[snd less_rest] | err] eqn:ParseContLess; [| discriminate]. simpl in ParseB.
    destruct (parse_continuation less_rest) as [[trd less_rest2] | err] eqn:ParseContLessRest; [| discriminate]. simpl in ParseB.
    destruct (parse_continuation less_rest2) as [[frth less_rest3] | err] eqn:ParseContLessRest2; [| discriminate]. simpl in ParseB.
    to_bits snd. to_bits trd. to_bits frth. repeat destruct_parse_continuation.
    inversion ParseContLess. inversion ParseContLessRest. inversion ParseContLessRest2.
    crush_bits; inversion ParseB; subst; next_state_DFA_run; fold (utf8_dfa_decode unparsed_rest); rewrite Utf8DecodeRestOk; reflexivity.
  - destruct_parse_continuation. crush_bits; inversion ParseB; inversion Utf8DecodeOk; subst; next_state_DFA_run; fold (utf8_dfa_decode unparsed_rest); rewrite Utf8DecodeRestOk; reflexivity.
Qed.

Ltac destruct_bits B :=
  match type of B with
  | exists (b: bool), ?P => let bit := fresh "b" in let P := fresh "byte_bits" in destruct B as [bit P]; destruct_bits P
  | ?A /\ ?C => let p := fresh "Pred" in let b := fresh "byte_bits" in destruct B as [b p]; destruct_bits b
  | to_bits ?b = _ => apply (f_equal Byte.of_bits) in B; rewrite Byte.of_bits_to_bits in B; rewrite B in *
  end.

Ltac byte_range_bits ByteRange :=
  let new := fresh "_byte_bits" in
  match type of ByteRange with
  | byte_range ?byte = Range_00_7F => apply byte_range_00_7f_bits in ByteRange as new
  | byte_range ?byte = Range_80_8F => apply byte_range_80_8f_bits in ByteRange as new
  | byte_range ?byte = Range_90_9F => apply byte_range_90_9f_bits in ByteRange as new
  | byte_range ?byte = Range_A0_BF => apply byte_range_a0_bf_bits in ByteRange as new
  | byte_range ?byte = Range_C2_DF => apply byte_range_c2_df_bits in ByteRange as new
  | byte_range ?byte = Byte_E0     => apply byte_e0_bits          in ByteRange as new
  | byte_range ?byte = Range_E1_EC => apply byte_range_e1_ec_bits in ByteRange as new
  | byte_range ?byte = Byte_ED     => apply byte_ed_bits          in ByteRange as new
  | byte_range ?byte = Range_EE_EF => apply byte_range_ee_ef_bits in ByteRange as new
  | byte_range ?byte = Byte_F0     => apply byte_f0_bits          in ByteRange as new
  | byte_range ?byte = Range_F1_F3 => apply byte_range_f1_f3_bits in ByteRange as new
  | byte_range ?byte = Byte_F4     => apply byte_f4_bits          in ByteRange as new
  end; destruct_bits new.

Ltac for_all_valid_byte_ranges:=
  match goal with
  | [U: context[let* (_, _) := utf8_dfa_decode_rec ?list ?code Initial in _] |- _] =>
      let parsed_code := fresh "parsed_codes" in
      let unparsed_rest := fresh "unparsed_bytes" in
      fold (utf8_dfa_decode list) in U; destruct (utf8_dfa_decode list) as [[parsed_codes unparsed_rest] | err] eqn:Utf8DfaDecodeLessOk; try discriminate U; inversion U
  | [U: context[utf8_dfa_decode_rec (?byte :: ?byte_rest) ?code ?state] |- _] =>
      let byte_eqn := fresh "ByteRange" in
      simpl in U; unfold next_state, extract_7_bits, extract_5_bits, extract_4_bits, extract_3_bits in U;
      destruct (byte_range byte) eqn:byte_eqn; try discriminate U; byte_range_bits byte_eqn; simpl in U; try rewrite Byte.to_bits_of_bits in U; simpl in U; for_all_valid_byte_ranges
  | [U: context[utf8_dfa_decode_rec ?bytes zero_codep Initial] |- _] =>
      let parsed_name := fresh "parsed_code" in
      let unparsed_bytes_name := fresh "unparsed_bytes" in
      fold (utf8_dfa_decode bytes) in U; destruct (utf8_dfa_decode bytes) as [[parsed_name unparsed_bytes_name] | _err] eqn:Utf8DfaDecodeLess; [| discriminate U];
      fold (utf8_decode bytes)
  | [U: context[utf8_dfa_decode_rec ?list ?code ?state] |- _] =>
      let byte_name := fresh "byte" in
      let byte_rest_name := fresh "byte_rest" in
        destruct list as [| byte_name byte_rest_name]; [ try discriminate U | for_all_valid_byte_ranges  ]
  end.

Theorem utf8_decoders_equal_right_strong : forall (bytes less: list byte) code rest,
    (List.length less) <= (List.length bytes) ->
    utf8_dfa_decode less = Ok (code, rest) -> utf8_decode less = Ok (code, rest).
Proof.
  intros bytes.
  induction bytes; intros less code rest LessLesser Utf8DfaDecodeOk; [ inversion LessLesser; rewrite List.length_zero_iff_nil in H0; subst; inversion Utf8DfaDecodeOk; reflexivity  | ].
  unfold utf8_dfa_decode in Utf8DfaDecodeOk.
  destruct less; [ inversion Utf8DfaDecodeOk; reflexivity | ].
  unfold utf8_decode, all, all_aux. unfold parse_codepoint; fold parse_codepoint; unfold parse_header.
  for_all_valid_byte_ranges;
    rewrite enc_four_spec || rewrite enc_three_spec || rewrite enc_two_spec || rewrite enc_one_spec;
    unfold bind, codepoint_range_to_codepoint; repeat rewrite parse_continuation_spec.
  
  all: repeat match goal with
         | [ B: ?a \/ ?b |- _ ] => let G1 := fresh "G" in let G2 := fresh "G" in destruct B as [ G1 | G2]
         | [ B: ?a /\ ?b |- _ ] => let G1 := fresh "G" in let G2 := fresh "G" in destruct B as [ G1 G2]
         end; subst; try match goal with
                     | [C: 0 = 1 |- _] => symmetry in G; apply Bool.diff_true_false in C; destruct C
                     | [C: 1 = 0 |- _] => apply Bool.diff_true_false in C; destruct C
                     end;
   repeat rewrite if_redundant.
  all: match goal with
       | [ |- context[match _ codepoint byte unicode_decode_error parse_codepoint ?len ?bytes with _ => _  end]] =>
           rewrite <- all_aux_saturation_aux with (n := (S (S (Datatypes.length bytes))));
           apply IHbytes in Utf8DfaDecodeLessOk;
           try apply parse_codepoint_strong_progress; try (simpl in *; lia);
           fold (all parse_codepoint bytes);
           fold (utf8_decode bytes);
           rewrite Utf8DfaDecodeLessOk; subst; reflexivity
       end.
Qed.

Theorem utf8_decoders_equal : forall bytes code rest,
    utf8_decode bytes = Ok (code, rest) <-> utf8_dfa_decode bytes = Ok (code, rest).
Proof.
  intros bytes code rest.
  split; intros Utf8DecodeOk.
  apply (utf8_decoders_equal_left_strong bytes bytes) in Utf8DecodeOk; auto.
  apply (utf8_decoders_equal_right_strong bytes bytes) in Utf8DecodeOk; auto.
Qed.
