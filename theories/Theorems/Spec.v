From Coq Require Import Strings.Byte.
From Coq Require Import Lia.

Require Import Utf8.Parser.
Require Import Utf8.Spec.


Local Notation "1" := true.
Local Notation "0" := false.

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
      unfold Spec.codepoint, Spec.b4 in byte;
      let b := fresh "b" in
      destruct byte as [[[[[b b4_1] b4_2] b4_3] b4_4] b4_5];
      break_bit b4_1; break_bit b4_2; break_bit b4_3; break_bit b4_4; break_bit b4_5
  | Spec.b7 =>
      unfold Spec.b7 in byte; break_bit byte
  | Spec.b6 =>
      unfold Spec.b6 in byte; break_bit byte
  | Spec.b5 =>
      unfold Spec.b5 in byte; break_bit byte
  | Spec.b4 =>
      unfold Spec.b4 in byte; break_bit byte
  | Spec.b3 =>
      unfold Spec.b3 in byte; break_bit byte
  | Byte.byte =>
      let B := fresh "B" in
      let eqn_name := fresh "byte_bits" in
      remember (Byte.to_bits byte) as B eqn:eqn_name;
      break_bit B;
      symmetry in eqn_name;
      apply (f_equal Byte.of_bits) in eqn_name;
      rewrite Byte.of_bits_to_bits in eqn_name
  end.

Definition antisymmetric {T} (comparison: T -> T -> bool) :=
  forall t1 t2,
    comparison t1 t2 = false ->
    comparison t2 t1 = false ->
    t1 = t2.

Definition irreflexive {T} (comparison: T -> T -> bool) :=
  forall t, comparison t t = false.

Ltac crush_bits :=
  let B := fresh "B" in
  repeat match goal with
    | |- context[if ?bit then _ else _] =>
        destruct bit eqn:B
    | _: context[if ?bit then _ else _ ] |- _ =>
        destruct bit eqn:B
    end.

Lemma b4_lt_antisymmetric : antisymmetric b4_lt.
Proof.
  intros b1 b2 b1_lt_b2 b2_lt_b1.
  to_bits b1. to_bits b2.
  unfold b4_lt, negb, andb, orb in b1_lt_b2, b2_lt_b1.
  repeat (crush_bits; try discriminate); reflexivity.
Qed.

Lemma b4_lt_irreflexive : irreflexive b4_lt.
Proof.
  unfold irreflexive.
  intros b. unfold b4_lt.
  to_bits b. repeat rewrite Bool.andb_negb_l. reflexivity.
Qed.

Lemma codepoint_lt_antisymmetric : antisymmetric codepoint_lt.
  intros c1 c2 c1_lt_c2 c2_lt_c1.
  to_bits c1. to_bits c2.
  unfold codepoint_lt in c1_lt_c2, c2_lt_c1.
  do 5 (match type of c1_lt_c2 with
  | context[b4_lt ?b4_1 ?b4_2] =>
      let B4_eq1 := fresh "B4_1_eq" in
      let B4_eq2 := fresh "B4_2_eq" in
      let b_eq   := fresh "b4_eq" in
      destruct (b4_lt b4_1 b4_2) eqn:B4_eq1;
      destruct (b4_lt b4_2 b4_1) eqn:B4_eq2;
      try rewrite Bool.orb_true_r in *; try rewrite Bool.andb_true_r in *; try discriminate;
      specialize (b4_lt_antisymmetric b4_1 b4_2 B4_eq1 B4_eq2) as b_eq;
      rewrite b_eq in * |- *
        end); repeat rewrite Bool.orb_false_r in c1_lt_c2, c2_lt_c1.
  destruct b; destruct b20; try discriminate; reflexivity.
Qed.

Lemma codepoint_lt_irreflexive : irreflexive codepoint_lt.
Proof.
  intros c.
  unfold codepoint_lt.
  to_bits c. rewrite Bool.andb_negb_l. repeat rewrite b4_lt_irreflexive. reflexivity.
Qed.

Lemma bit_compare_antisymmetric : antisymmetric (fun bool1 bool2 => (andb (negb bool1) bool2)).
Proof.
  intros bool1 bool2.
  destruct bool1; destruct bool2; try discriminate; reflexivity.
Qed.

Lemma byte_lt_antisymetric : antisymmetric byte_lt.
Proof.
  intros byte1 byte2 b1_lt_b2 b2_lt_b1.
  unfold byte_lt in b1_lt_b2, b2_lt_b1.
  to_bits byte1. to_bits byte2.
  do 8 (match type of b1_lt_b2 with
  | context[andb (negb ?b1) ?b2] =>
      let B_eq1 := fresh "B1_eq" in
      let B_eq2 := fresh "B2_eq" in
      let b_eq := fresh b_eq in
      destruct (andb (negb b1) b2) eqn:B_eq1;
      destruct (andb (negb b2) b1) eqn:B_eq2;
      try rewrite Bool.orb_true_r in *; try rewrite Bool.andb_true_r in *; try discriminate;
      specialize (bit_compare_antisymmetric b1 b2 B_eq1 B_eq2) as b_eq;
      rewrite b_eq in *
        end).
  subst. reflexivity.
Qed.

Lemma byte_lt_irreflexive : irreflexive byte_lt.
Proof.
  intros byte.
  unfold byte_lt.
  to_bits byte.
  repeat rewrite Bool.andb_negb_l.
  reflexivity.
Qed.

Lemma lexicographic_compare_antisymetric {T} (lt: T -> T -> bool):
  antisymmetric lt ->
  antisymmetric (lexicographic_compare lt).
Proof.
  intros antisymmetric_lt.
  unfold antisymmetric in *.
  intros t1.
  induction t1 as [| t1_head t1_rest];  intros t2 lexi_compare_t1_t2 lexi_compare_t2_t1.
  - simpl in lexi_compare_t1_t2. destruct t2; [ reflexivity | discriminate].
  - destruct t2 as [| t2_head t2_rest].
    + discriminate lexi_compare_t2_t1.
    + simpl in *.
      destruct (lt t1_head t2_head) eqn:LtT1T2; [discriminate |].
      destruct (lt t2_head t1_head) eqn:LtT2T1; [discriminate |].
      specialize (antisymmetric_lt t1_head t2_head LtT1T2 LtT2T1).
      subst.
      simpl in lexi_compare_t1_t2, lexi_compare_t2_t1.
      specialize (IHt1_rest t2_rest lexi_compare_t1_t2 lexi_compare_t2_t1). subst. reflexivity.
Qed.

Lemma lexicographic_compare_irreflexive {T} (lt: T -> T -> bool):
  irreflexive lt ->
  irreflexive (lexicographic_compare lt).
Proof.
  unfold irreflexive.
  intros irreflexive_lt ts.
  induction ts.
  - reflexivity.
  - simpl. rewrite irreflexive_lt. rewrite IHts. reflexivity.
Qed.

Lemma codepoints_lt_antisymmetric : antisymmetric codepoints_lt.
Proof.
  unfold codepoints_lt.
  apply lexicographic_compare_antisymetric.
  apply codepoint_lt_antisymmetric.
Qed.

Lemma codepoints_lt_irreflexive : irreflexive codepoints_lt.
Proof.
  unfold codepoints_lt.
  apply lexicographic_compare_irreflexive.
  apply codepoint_lt_irreflexive.
Qed.

Lemma bytes_lt_antisymetric : antisymmetric bytes_lt.
Proof.
  unfold bytes_lt.
  apply lexicographic_compare_antisymetric.
  apply byte_lt_antisymetric.
Qed.

Lemma bytes_lt_irreflexive: irreflexive bytes_lt.
  unfold bytes_lt.
  apply lexicographic_compare_irreflexive.
  apply byte_lt_irreflexive.
Qed.

Lemma lexicographic_nil_smallest {T} (lt: T -> T -> bool): forall t,
    t = nil \/ (lexicographic_compare lt nil t = true).
Proof.
  intros.
  destruct t; [left | right]; reflexivity.
Qed.

Lemma antisymmetric_cases {T} (lt: T -> T -> bool): forall t1 t2,
    antisymmetric lt ->
    t1 = t2 \/ (lt t1 t2 = true) \/ (lt t2 t1 = true).
Proof.
  intros.
  unfold antisymmetric in H. 
  destruct (lt t1 t2) eqn:Lt1.
  - tauto.
  - destruct (lt t2 t1) eqn:Lt2.
    + tauto.
    + specialize (H t1 t2 Lt1 Lt2). left. apply H.
Qed.

Lemma byte_range_of_bits_00_7f: forall b1 b2 b3 b4 b5 b6 b7,
    byte_range (of_bits (b1, (b2, (b3, (b4, (b5, (b6, (b7, 0)))))))) = Range_00_7F.
Proof.
  intros.
  simpl. unfold byte_range.
  
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

Lemma byte_range_of_bits_90_bf_p1: forall (b1 b2 b3 b4 b5: bool),
    let b := of_bits (b1, (b2, (b3, (b4, (b5, (1, (0, 1))))))) in
    byte_range b = Range_90_9F \/ byte_range b = Range_A0_BF.
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


Lemma byte_range_of_bits_e0 :
  byte_range (of_bits (0, (0, (0, (0, (0, (1, (1, 1)))))))) = Byte_E0.
Proof.
    destruct (of_bits (0, (0, (0, (0, (0, (1, (1, 1)))))))) eqn:B;
    apply (f_equal Byte.to_bits) in B;
    rewrite Byte.to_bits_of_bits in B;
    inversion B;
    reflexivity.
Qed.

Lemma byte_range_of_bits_e1_ec: forall b1 b2 b3 b4,
    ((b1 = 1 \/ b2 = 1 \/ b3 = 1 \/ b4 = 1) /\ (b3 = 0 \/ b4 = 0 \/ (b1 = 0 /\ b2 = 0))) ->
  byte_range (of_bits (b1, (b2, (b3, (b4, (0, (1, (1, 1)))))))) = Range_E1_EC.
Proof.
  intros b1 b2 b3 b4 [[G| [G | [G | G]]] [G2 | [G2 | [G2 G3]]]]; match goal with
  | |- byte_range ?byte = _ => destruct byte eqn:B
  end; apply (f_equal Byte.to_bits) in B;
    rewrite Byte.to_bits_of_bits in B;
    inversion B;
    subst; easy.
Qed.


Lemma byte_range_of_bits_ed:
  byte_range (of_bits (1, (0, (1, (1, (0, (1, (1, 1)))))))) = Byte_ED.
Proof.
  destruct (of_bits (1, (0, (1, (1, (0, (1, (1, 1)))))))) eqn:B;
    apply (f_equal Byte.to_bits) in B;
    rewrite Byte.to_bits_of_bits in B;
    inversion B;
    reflexivity.
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

Lemma byte_range_of_bits_f0 :
  byte_range (of_bits (0, (0, (0, (0, (1, (1, (1, 1)))))))) = Byte_F0.
Proof.
  destruct (of_bits (0, (0, (0, (0, (1, (1, (1, 1)))))))) eqn:H;
    apply (f_equal Byte.to_bits) in H;
    rewrite Byte.to_bits_of_bits in H; inversion H; reflexivity.
Qed.
    

Lemma byte_range_of_bits_f1_f3: forall b1 b2,
    (b1 = 1 \/ b2 = 1) ->
    byte_range (of_bits (b1, (b2, (0, (0, (1, (1, (1, 1)))))))) = Range_F1_F3.
Proof.
  intros.
  destruct (of_bits (b1, (b2, (0, (0, (1, (1, (1, 1)))))))) eqn:G;
    apply (f_equal Byte.to_bits) in G;
    rewrite Byte.to_bits_of_bits in G;
    inversion G; destruct H; subst; try discriminate;
    auto.
Qed.

Lemma byte_range_of_bits_f4:
    let b := of_bits (0, (0, (1, (0, (1, (1, (1, 1))))))) in
    byte_range b = Byte_F4.
Proof.
  intros.
  destruct b eqn:H;
    apply (f_equal Byte.to_bits) in H;
    subst b;
    rewrite Byte.to_bits_of_bits in H;
    inversion H;
    auto.
Qed.


Lemma byte_f4_bits : forall b,
    byte_range b = Byte_F4 ->
    Byte.to_bits b = (0, (0, (1, (0, (1, (1, (1, 1))))))).
Proof.
  intros.
  destruct b; inversion H; reflexivity.
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
       (b2 = 1 \/ b3 = 1 \/ b4 = 1 \/ b5 = 1)).
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
        (b1 = 1 \/ b2 = 1).
Proof.
  intros.
  destruct b; inversion H; repeat eexists; auto.
Qed.


Lemma byte_range_f5_ff_bits : forall b,
    byte_range b = Range_F5_FF ->
    exists b1 b2 b3 b4,
      Byte.to_bits b = (b1, (b2, (b3, (b4, (1, (1, (1, 1))))))).
Proof.
  intros.
  destruct b; inversion H; repeat eexists.
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


Ltac rewrite_bits_in_hypothesis B :=
  unfold valid_utf8_bytes in B; fold valid_utf8_bytes in B; unfold expect in B;
  unfold in_range_80_bf, in_range_80_8f, in_range_a0_bf, in_range_90_bf, in_range_80_9f in B;
  match type of B with
  | valid_utf8_bytes ?bytes =>
      idtac
  | True => idtac
  | context[byte_range (of_bits (?b1, (?b2, (?b3, (?b4, (?b5, (?b6, (?b7, 0))))))))] =>
      rewrite byte_range_of_bits_00_7f in B
  | context[byte_range (of_bits (?b1, (?b2, (?b3, (?b4, (?b5, (0, (1, 1))))))))] =>
      rewrite byte_range_of_bits_c2_df in B; auto
  | context[byte_range (of_bits (?b1, (?b2, (?b3, (?b4, (?b5, (1, (0, 1))))))))] =>
      rewrite byte_range_of_bits_a0_bf in B
  | context[byte_range (of_bits (?b1, (?b2, (?b3, (?b4, (0, (0, (0, 1))))))))] =>
      rewrite byte_range_of_bits_80_8f in B
  | context[byte_range (of_bits (?b1, (?b2, (?b3, (?b4, (1, (0, (0, 1))))))))] =>
      rewrite byte_range_of_bits_90_9f in B
  | context[byte_range (of_bits (0, (0, (0, (0, (0, (1, (1, 1))))))))] =>
      rewrite byte_range_of_bits_e0 in B
  | context[byte_range (of_bits (1, (0, (1, (1, (0, (1, (1, 1))))))))] =>
      rewrite byte_range_of_bits_ed in B
  | context[byte_range (of_bits (?bit, (1, (1, (1, (0, (1, (1, 1))))))))] =>
      rewrite byte_range_of_bits_ee_ef in B
  | context[byte_range (of_bits (?b1, (?b2, (?b3, (?b4, (0, (1, (1, 1))))))))] =>
      rewrite byte_range_of_bits_e1_ec in B; auto
  | context[byte_range (of_bits (0, (0, (1, (0, (1, (1, (1, 1))))))))] =>
      rewrite byte_range_of_bits_f4 in B
  | context[byte_range (of_bits (0, (0, (0, (0, (1, (1, (1, 1))))))))] =>
      rewrite byte_range_of_bits_f0 in B
  | context[byte_range (of_bits (?b1, (?b2, (0, (0, (1, (1, (1, 1))))))))] =>
      rewrite byte_range_of_bits_f1_f3 in B; auto
  | ?a /\ ?b =>
      let P1 := fresh "P1" in let P2 := fresh "P2" in
                              destruct B as [P1 P2]; rewrite_bits_in_hypothesis P1; rewrite_bits_in_hypothesis P2
  end.

Ltac validate_utf8_bytes :=
  unfold valid_utf8_bytes; fold valid_utf8_bytes; unfold expect;
  repeat match goal with
    | [ |- valid_utf8_bytes nil ] => unfold valid_utf8_bytes
    | [ |- True ] => constructor
    | [ |- ?A /\ ?B ] => split
    | [ |- context[byte_range (of_bits (?b1, (?b2, (?b3, (?b4, (?b5, (?b6, (?b7, 0))))))))]] =>
        rewrite byte_range_of_bits_00_7f
    | [ |- context[byte_range (of_bits (?b1, (?b2, (?b3, (?b4, (?b5, (0, (1, 1))))))))]] =>
        rewrite byte_range_of_bits_c2_df; auto
    | [ |- context[byte_range (of_bits (0, (0, (0, (0, (0, (1, (1, 1))))))))]] =>
        rewrite byte_range_of_bits_e0
    | [ |- context[byte_range (of_bits (1, (0, (1, (1, (0, (1, (1, 1))))))))]] =>
        rewrite byte_range_of_bits_ed
    | [ |- context[byte_range (of_bits (?bit, (1, (1, (1, (0, (1, (1, 1))))))))]] =>
        rewrite byte_range_of_bits_ee_ef
    | [ |- context[byte_range (of_bits (?b1, (?b2, (?b3, (?b4, (0, (1, (1, 1))))))))]] =>
        rewrite byte_range_of_bits_e1_ec; auto
    | [ |- context[byte_range (of_bits (0, (0, (1, (0, (1, (1, (1, 1))))))))]] =>
        rewrite byte_range_of_bits_f4
    | [ |- context[byte_range (of_bits (0, (0, (0, (0, (1, (1, (1, 1))))))))]] =>
        rewrite byte_range_of_bits_f0
    | [ |- context[byte_range (of_bits (?b1, (?b2, (0, (0, (1, (1, (1, 1))))))))]] =>
        rewrite byte_range_of_bits_f1_f3; auto
    | [ |- in_range_80_8f (of_bits (?b1, (?b2, (?b3, (?b4, (0, (0, (0, 1)))))))) ] =>
        let byte_bits := fresh "ByteBits" in
        unfold in_range_80_8f;
        rewrite byte_range_of_bits_80_8f; auto
    | [ |- in_range_80_9f (of_bits (?b1, (?b2, (?b3, (?b4, (?b5, (0, (0, 1))))))))] =>
          unfold in_range_80_9f;
          destruct b5; [ rewrite byte_range_of_bits_90_9f | rewrite byte_range_of_bits_80_8f ] 
    | [ |- in_range_90_bf (of_bits (?b1, (?b2, (?b3, (?b4, (?b5, (1, (0, 1)))))))) ] =>
        let byte_bits := fresh "ByteBits" in
        let bits := fresh "Bits" in
        pose proof (byte_range_of_bits_90_bf_p1 b1 b2 b3 b4 b5) as bits;
        unfold in_range_90_bf;
        destruct bits as [byte_bits | byte_bits]; rewrite byte_bits
    | [ |- in_range_90_bf (of_bits (?b1, (?b2, (?b3, (?b4, (1, (0, (0, 1)))))))) ] =>
        unfold in_range_90_bf;
        rewrite byte_range_of_bits_90_9f
    | [ |- in_range_80_8f (of_bits (?b1, (?b2, (?b3, (?b4, (0, (0, (0, 1)))))))) ] =>
        unfold in_range_80_8f;
        rewrite byte_range_of_bits_80_8f
    | [ |- in_range_a0_bf (of_bits (?b1, (?b2, (?b3, (?b4, (?b5, (1, (0, 1)))))))) ] =>
        unfold in_range_a0_bf;
        rewrite byte_range_of_bits_a0_bf
    | [ |- in_range_80_bf (of_bits (?b1, (?b2, (?b3, (?b4, (?b5, (?b6, (0, 1))))))))] =>
        let byte_bits := fresh "ByteBits" in
        let bits := fresh "Bits" in
        pose proof (byte_range_of_bits_80_bf b1 b2 b3 b4 b5 b6) as bits;
        unfold in_range_80_bf;
        destruct bits as [byte_bits | [byte_bits | byte_bits]]; rewrite byte_bits
    end.

Ltac destruct_valid_bytes R :=
  match type of R with
  | valid_utf8_bytes ?bytes =>
      idtac
  | context[byte_range ?byte] =>
      let r := fresh "ByteRange" in
      destruct (byte_range byte) eqn:r; try easy; byte_range_bits r;
      destruct_valid_bytes R
  | expect ?pred ?bytes_pred ?bytes =>
      let b := fresh "byte" in
      let bs := fresh "bytes" in
      let pred := fresh "pred" in
      let pred_rest := fresh "bytes_valid" in
      destruct bytes as [| b bs]; try easy; simpl in R;
      destruct R as [pred pred_rest];
      unfold in_range_80_bf, in_range_80_8f, in_range_a0_bf, in_range_90_bf, in_range_80_9f in pred;
      destruct_valid_bytes pred;
      destruct_valid_bytes pred_rest
  | True => idtac
  end.


Theorem valid_utf8_bytes_concat_strong : forall (bytes_big bytes1 bytes2: list byte),
    (length bytes1) <= (length bytes_big) ->
    valid_utf8_bytes bytes1 ->
    valid_utf8_bytes bytes2 ->
    valid_utf8_bytes (bytes1 ++ bytes2).
Proof.
  intros bytes_big. induction bytes_big; intros bytes1 bytes2 lesser bytes1_valid bytes2_valid.
  inversion lesser. apply List.length_zero_iff_nil in H0. subst. apply bytes2_valid.
  destruct bytes1 as [| byte1 rest1]; auto.
  simpl in bytes1_valid |- *.
  destruct (byte_range byte1); auto;
  let rec prove_concat :=
    match goal with
    | |- valid_utf8_bytes (?b1 ++ ?b2) =>
        apply IHbytes_big; simpl in lesser; try lia; assumption
    | [G: expect ?byte_pred1 ?rest_pred1 ?b1 |- expect ?byte_pred2 ?rest_pred2 (?b1 ++ ?b2)] =>
        let byte := fresh "byte_in_range" in
        let rest := fresh "rest_pred" in
        simpl in G |- *; destruct b1; simpl in G |- *; try easy;
        destruct G as [byte rest];
        split; try apply byte; prove_concat
  end
  in prove_concat.
Qed.

Theorem valid_utf8_bytes_concat : forall (bytes1 bytes2: list byte),
    valid_utf8_bytes bytes1 ->
    valid_utf8_bytes bytes2 ->
    valid_utf8_bytes (bytes1 ++ bytes2).
Proof.
  intros bytes1 bytes2 valid_bytes1 valid_bytes2.
  apply valid_utf8_bytes_concat_strong with (bytes_big := bytes1). lia.
  1,2: assumption.
Qed.

Theorem valid_utf8_decompose_strong : forall (bytes_big bytes1 bytes2: list byte),
    (length bytes1) <= (length bytes_big) -> 
    valid_utf8_bytes (bytes1 ++ bytes2) ->
    valid_utf8_bytes bytes1 ->
    valid_utf8_bytes bytes2.
Proof.
  intros bytes_big.
  induction bytes_big.
  - intros. inversion H. rewrite List.length_zero_iff_nil in H3. subst. simpl in H0. apply H0.
  - intros bytes1 bytes2 LessThan bytes_concat_valid bytes1_valid.
    destruct bytes1.
    + apply bytes_concat_valid.
    + simpl in bytes1_valid. Opaque Byte.of_bits.
      destruct_valid_bytes bytes1_valid; simpl in bytes_concat_valid; repeat rewrite_bits_in_hypothesis bytes_concat_valid; try contradiction; match goal with
      | [G: valid_utf8_bytes (?bytes1 ++ ?bytes2) |- _ ]  => apply (IHbytes_big bytes1 bytes2); repeat assumption; simpl in LessThan |- *; try lia
      end. 
Qed.

Theorem encoder_spec_implies_unique_encoding : forall encoder,
    utf8_encoder_spec encoder ->
    forall codes bytes,
      encoder codes = (bytes, nil) ->
      forall other_bytes,
        encoder codes = (other_bytes, nil) ->
        bytes = other_bytes.
Proof.
  intros encoder encoder_spec_compliant.
  unfold utf8_encoder_spec, encoder_encode_correctly_implies_valid, encoder_encode_valid_codes_correctly, encoder_strictly_increasing in encoder_spec_compliant.
  destruct encoder_spec_compliant as [enc_implies_valid_utf8_bytes [valid_codepoints_iff_enc enc_strictly_increasing]].
  intros codes bytes encode_codes1 other_bytes encode_codes2.
  specialize (enc_strictly_increasing codes codes bytes other_bytes nil nil encode_codes1 encode_codes2) as G1.
  specialize (enc_strictly_increasing codes codes other_bytes bytes nil nil encode_codes2 encode_codes1) as G2.
  rewrite codepoints_lt_irreflexive in G1, G2.
  symmetry in G1, G2.
  specialize (bytes_lt_antisymetric bytes other_bytes G1 G2) as equal.
  apply equal.
Qed.

Theorem encoder_spec_valid_all_equal : forall encoder,
    utf8_encoder_spec encoder ->
    encoder nil = (nil, nil).
Proof.
  intros encoder encoder_spec_compliant.
  unfold utf8_encoder_spec, encoder_encode_correctly_implies_valid, encoder_encode_valid_codes_correctly, encoder_strictly_increasing in encoder_spec_compliant.
  destruct encoder_spec_compliant as [enc_implies_valid_utf8_bytes [valid_codepoints_iff_enc enc_strictly_increasing]].
  assert (valid_codepoints nil) as nil_valid. {
    apply List.Forall_nil.
  }
  apply valid_codepoints_iff_enc in nil_valid as [bytes encode_nil].
  destruct (antisymmetric_cases bytes_lt bytes nil bytes_lt_antisymetric).
  - subst. apply encode_nil.
  - induction bytes.
    + apply encode_nil.
    + simpl in H.
    

Theorem encoder_spec_valid_all_equal : forall encoder1 encoder2,
    utf8_encoder_spec encoder1 ->
    utf8_encoder_spec encoder2 ->
    forall codes bytes codes_suffix,
      encoder1 codes = (bytes, codes_suffix) ->
      exists codes_prefix, encoder2 codes_prefix = (bytes, nil) /\ codes = (codes_prefix ++ codes_suffix).
Proof.
  intros encoder1 encoder2 encoder1_spec_compliant encoder2_spec_compliant.
  unfold utf8_encoder_spec, encoder_encode_correctly_implies_valid, encoder_encode_valid_codes_correctly, encoder_strictly_increasing in encoder1_spec_compliant, encoder2_spec_compliant.
  destruct encoder1_spec_compliant as [enc1_implies_valid_utf8_bytes [valid_codepoints_iff_enc1 enc1_strictly_increasing]].
  destruct encoder2_spec_compliant as [enc2_implies_valid_utf8_bytes [valid_codepoints_iff_enc2 enc2_strictly_increasing]].
  intros codes bytes enc1_codes.
  assert (exists bytes, encoder1 codes = (bytes, nil)) as codes_valid. {
    exists bytes. apply enc1_codes.
  }
  apply <- valid_codepoints_iff_enc1 in codes_valid.
  apply valid_codepoints_iff_enc2 in codes_valid as enc2_codes.
  destruct enc2_codes as [bytes2 enc2_codes].
  specialize (enc1_strictly_increasing codes codes bytes bytes nil nil codes_valid codes_valid enc1_codes enc1_codes).
  specialize (enc2_strictly_increasing codes codes bytes2 bytes2 nil nil codes_valid codes_valid enc2_codes enc2_codes).
  rewrite enc1_strictly_increasing in enc2_strictly_increasing.
  
Admitted.

Theorem decoder_spec_valid_all_equal : forall decoder1 decoder2,
    utf8_decoder_spec decoder1 ->
    utf8_decoder_spec decoder2 ->
    forall bytes codes,
      decoder1 bytes = (codes, nil) ->
      decoder2 bytes = (codes, nil).
Proof.
  Admitted.

Theorem decode_encode_spec_compliant_inverses : forall encoder decoder,
    utf8_encoder_spec encoder ->
    utf8_decoder_spec decoder ->
    (forall codes bytes codes_suffix,
        encoder codes = (bytes, codes_suffix) ->
        exists codes_prefix, decoder bytes = (codes_prefix, nil) /\ codes = (codes_prefix ++ codes_suffix)%list)
    /\
      (forall bytes codes bytes_suffix,
          decoder bytes = (codes, bytes_suffix) ->
          exists bytes_prefix, encoder codes = (bytes_prefix, nil) /\ bytes = (bytes_prefix ++ bytes_suffix)%list).
Proof.
  intros encoder decoder encoder_spec_compliant decoder_spec_compliant.
  unfold utf8_encoder_spec, encoder_encode_correctly_implies_valid, encoder_encode_valid_codes_correctly, encoder_strictly_increasing in encoder_spec_compliant.
  destruct encoder_spec_compliant as [enc_implies_valid_utf8_bytes [valid_codepoints_iff_enc enc_strictly_increasing]].
  unfold utf8_decoder_spec, decoder_decode_correctly_implies_valid, decoder_decode_valid_utf8_bytes_correctly, decoder_strictly_increasing in decoder_spec_compliant.
  destruct decoder_spec_compliant as [dec_implies_valid [valid_implies_dec dec_strictly_increasing]].
  split.
  - intros codes bytes codes_rest encoder_bytes.
    apply enc_implies_valid_utf8_bytes in encoder_bytes as G.
    destruct G as [bytes_utf8_valid [codes_prefix [codes_prefix_eq encoder_prefix]]].
    exists codes_prefix.
    apply valid_implies_dec in bytes_utf8_valid as [codes2 decode_bytes].
    split; [| apply codes_prefix_eq].
    apply dec_implies_valid in decode_bytes as G.
    destruct G as [codes2_valid [bytes_prefix [bytes_prefix_eq decoder_bytes_prefix]]]. rewrite List.app_nil_r in bytes_prefix_eq. rewrite bytes_prefix_eq in *.
    apply valid_codepoints_iff_enc in codes2_valid as G.
    destruct G as [bytes2 enc_bytes2].
    assert (exists bytes, encoder codes_prefix = (bytes, nil)). {
      exists bytes_prefix. apply encoder_prefix.
    } 
    apply <- valid_codepoints_iff_enc in H.
    specialize (enc_strictly_increasing codes_prefix codes2 bytes_prefix bytes2 nil nil H codes2_valid encoder_prefix enc_bytes2).
    
    
    
Admitted.

(*   intros encoder decoder encoder_spec_compliant decoder_spec_compliant. *)
(*   unfold utf8_encoder_spec, encoder_encode_correctly_implies_valid, encoder_encode_valid_codes_correctly, encoder_injective in encoder_spec_compliant. *)
(*   destruct encoder_spec_compliant as [enc_implies_valid [valid_implies_enc enc_injective]]. *)
(*   unfold utf8_decoder_spec, decoder_decode_correctly_implies_valid, decoder_decode_valid_utf8_bytes_correctly, decoder_injective in decoder_spec_compliant. *)
(*   destruct decoder_spec_compliant as [dec_implies_valid [valid_implies_dec dec_injective]]. *)
(*   split. *)
(*   - intros codes bytes codes_rest encoder_bytes. *)
(*     apply enc_implies_valid in encoder_bytes as G. *)
(*     destruct G as [valid_bytes [codes_prefix [codes_eq encoder_prefix]]]. *)
(*     apply valid_implies_dec in valid_bytes. *)
(*     destruct valid_bytes as [codes2 codes2_eq]. *)
(*     apply dec_implies_valid in codes2_eq as G. *)
(*     destruct G as [codes2_valid [bytes_prefix [bytes_prefix_eq decode_bytes_prefix]]]. *)
(*     apply valid_implies_enc in codes2_valid. *)
(*     destruct codes2_valid as [bytes2 bytes2_enc]. *)
(*     subst.  *)
(*     exists codes2. subst. split. apply codes2_eq.  *)
(*     apply List.app_inv_tail_iff. *)
        
