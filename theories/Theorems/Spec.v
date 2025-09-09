From Coq Require Import Strings.Byte.
From Coq Require Import Lia.

Require Import Utf8.Parser.
Require Import Utf8.Spec.
Require Import Utf8.Theorems.Order.

Local Notation "1" := true.
Local Notation "0" := false.

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

Definition next_valid_codepoint (code: codepoint) : option codepoint :=
  match code with
  | (0, (0, 0, 0, 0), (1, 1, 0, 1), (0, 1, 1, 1), (1, 1, 1, 1), (1, 1, 1, 1)) =>
      Some (0, b4_zero, (1, 1, 1, 0), b4_zero, b4_zero, b4_zero)
  | (1, (0, 0, 0, 0), (1, 1, 1, 1), (1, 1, 1, 1), (1, 1, 1, 1), (1, 1, 1, 1)) =>
      None
  | (b1, (b2, b3, b4, b5), (b6, b7, b8, b9), (b10, b11, b12, b13), (b14, b15, b16, b17), (b18, b19, b20, b21)) =>
      None
  end.

Require Import Coq.Lists.List. Import ListNotations.

Lemma list_equals_self_append_implies_nil {T}: forall (list1 list2: list T),
    list1 = list1 ++ list2 ->
    list2 = nil.
Proof.
  intros.
  destruct list1.
  - symmetry in H. apply List.app_eq_nil in H. destruct H. assumption. 
  - apply (f_equal (@length T)) in H.
    rewrite List.length_app in H. simpl in H. Search (S (?a + ?b)). rewrite <- plus_Sn_m in H.
    destruct list2. reflexivity. simpl in H. lia.
Qed.

Lemma encoder_spec_implies_nil_mapsto_nil : forall encoder,
    utf8_encoder_spec encoder ->
    encoder nil = (nil, nil).
Proof.
  intros encoder encoder_spec_compliant.
  assert (G := encoder_spec_compliant).
  unfold utf8_encoder_spec, encoder_encode_correctly_implies_valid, encoder_encode_valid_codes_correctly, encoder_strictly_increasing, encoder_projects in G.
  destruct G as [enc_implies_valid_utf8_bytes [valid_codepoints_iff_enc [enc_strictly_increasing enc_projects]]].
  assert (valid_codepoints []) as nil_valid. apply Forall_nil.
  
  apply valid_codepoints_iff_enc in nil_valid.
  destruct nil_valid as [bytes encode_bytes].
  specialize (enc_projects [] []). rewrite encode_bytes in enc_projects. simpl in enc_projects. rewrite enc_projects in encode_bytes. inversion encode_bytes.
  symmetry in H0.
  apply list_equals_self_append_implies_nil in H0.
  subst. simpl in *. apply enc_projects.
Qed.

Lemma encoder_spec_injective : forall encoder,
    utf8_encoder_spec encoder ->
    forall (codes1 codes2: list codepoint) bytes,
      encoder codes1 = (bytes, []) ->
      encoder codes2 = (bytes, []) ->
      codes1 = codes2.
Proof.
  intros encoder encoder_spec_compliant.
  assert (G := encoder_spec_compliant).
  unfold utf8_encoder_spec, encoder_encode_correctly_implies_valid, encoder_encode_valid_codes_correctly, encoder_strictly_increasing, encoder_projects in G.
  destruct G as [enc_implies_valid_utf8_bytes [valid_codepoints_iff_enc [enc_strictly_increasing enc_projects]]].
  intros codes1 codes2 bytes encoder_codes1 encoder_codes2.
  specialize (enc_strictly_increasing codes1 codes2 bytes bytes encoder_codes1 encoder_codes2) as compare_codes.
  specialize (codepoints_compare_antisymmetric codes1 codes2) as G.
  rewrite (@antisymmetric_reflexive (list byte) bytes_compare bytes_compare_antisymmetric) in compare_codes.
  rewrite compare_codes in G.
  apply G.
Qed.

Theorem encoder_spec_implies_encode_single_equals : forall encoder1 code bytes,
    utf8_encoder_spec encoder1 ->
    encoder1 [code] = (bytes, nil) ->
    forall encoder2,
      utf8_encoder_spec encoder2 ->
      encoder2 [code] = (bytes, nil).
Proof.
  intros encoder1 code bytes encoder1_spec_compliant encoder1_code encoder2 encoder2_spec_compliant.
  assert (G1 := encoder1_spec_compliant).
  assert (G2 := encoder2_spec_compliant).
  unfold utf8_encoder_spec, encoder_encode_correctly_implies_valid, encoder_encode_valid_codes_correctly, encoder_strictly_increasing, encoder_projects in G1, G2.
  destruct G1 as [enc1_implies_valid_utf8_bytes [valid_codepoints_iff_enc1 [enc1_strictly_increasing enc1_projects]]].
  destruct G2 as [enc2_implies_valid_utf8_bytes [valid_codepoints_iff_enc2 [enc2_strictly_increasing enc2_projects]]].
  assert (exists bytes, encoder1 [code] = (bytes, nil)). exists bytes. assumption.
  apply valid_codepoints_iff_enc1 in H.
  apply valid_codepoints_iff_enc2 in H.
  destruct H as [bytes2 encoder2_code]. rewrite encoder2_code.
  apply pair_equal_spec. split; [| reflexivity].
  Admitted.

   
Theorem encoder_spec_implies_encoder_equal : forall encoder1 codes bytes,
    utf8_encoder_spec encoder1 ->
    encoder1 codes = (bytes, nil) ->
    forall encoder2,
      utf8_encoder_spec encoder2 ->
      encoder2 codes = (bytes, nil).
Proof.
  intros encoder1.
  induction codes as [| code codes_tail]; intros bytes encoder1_spec_compliant encoder1_codes encoder2 encoder2_spec_compliant; 
    assert (G1 := encoder1_spec_compliant);
    assert (G2 := encoder2_spec_compliant);
    unfold utf8_encoder_spec, encoder_encode_correctly_implies_valid, encoder_encode_valid_codes_correctly, encoder_strictly_increasing, encoder_projects in G1, G2;
    destruct G1 as [enc1_implies_valid_utf8_bytes [valid_codepoints_iff_enc1 [enc1_strictly_increasing enc1_projects]]];
    destruct G2 as [enc2_implies_valid_utf8_bytes [valid_codepoints_iff_enc2 [enc2_strictly_increasing enc2_projects]]].
  - specialize (enc1_projects nil nil) as enc_nil. simpl in enc_nil. rewrite encoder1_codes in enc_nil.
    inversion enc_nil.
    apply list_equals_self_append_implies_nil in H0. subst. clear enc_nil.
    specialize (enc2_projects nil nil). simpl in enc2_projects.
    destruct (encoder2 nil) as [bytes rest] eqn:E.
    destruct rest.
    + inversion enc2_projects. apply list_equals_self_append_implies_nil in H0. subst. reflexivity.
    + apply enc2_implies_valid_utf8_bytes in E as G.
      destruct G as [valid_utf8_bytes [codes_prefix [codes_eq enc_codes_prefix]]].
      symmetry in codes_eq.
      apply List.app_eq_nil in codes_eq as [codes_prefix_nil c_cons_rest_nil]. discriminate.
  - replace (code :: codes_tail) with ([code] ++ codes_tail) in encoder1_codes |- * by reflexivity.
    rewrite enc1_projects in encoder1_codes.
    destruct (encoder1 [code]) as [bytes1 code_rest] eqn:encoder1_code.
    destruct code_rest; [|inversion encoder1_codes].
    destruct (encoder1 codes_tail) as [bytes2 codes_rest] eqn:encoder1_codes_tail.
    inversion encoder1_codes_tail. inversion encoder1_codes. subst.
    specialize (IHcodes_tail bytes2 encoder1_spec_compliant ltac:(reflexivity) encoder2 encoder2_spec_compliant) as encoder2_codes_tail.
    rewrite enc2_projects. rewrite encoder2_codes_tail.
    assert (exists bytes, encoder1 [code] = (bytes, nil)). exists bytes1. assumption.
    apply valid_codepoints_iff_enc1 in H.
    apply valid_codepoints_iff_enc2 in H.
    destruct H as [bytes3 encoder2_code]. rewrite encoder2_code.
    apply pair_equal_spec; split; auto.
    apply app_inv_tail_iff.
    specialize (encoder_spec_implies_encode_single_equals encoder1 code bytes1 encoder1_spec_compliant encoder1_code encoder2 encoder2_spec_compliant) as G. rewrite G in encoder2_code. inversion encoder2_code.
    reflexivity.
Qed.

(* Theorem encoder_spec_valid_all_equal : forall encoder decoder, *)
(*     utf8_encoder_spec encoder -> *)
(*     utf8_decoder_spec decoder -> *)
(*     encoder nil = (nil, nil) /\ decoder nil = (nil, nil). *)
(* Proof. *)
(*   intros encoder decoder encoder_spec_compliant decoder_spec_compliant. *)
(*   unfold utf8_encoder_spec, encoder_encode_correctly_implies_valid, encoder_encode_valid_codes_correctly, encoder_strictly_increasing in encoder_spec_compliant. *)
(*   destruct encoder_spec_compliant as [enc_implies_valid_utf8_bytes [valid_codepoints_iff_enc enc_strictly_increasing]]. *)
(*   unfold utf8_decoder_spec, decoder_decode_correctly_implies_valid, decoder_decode_valid_utf8_bytes_correctly, decoder_strictly_increasing in decoder_spec_compliant. *)
(*   destruct decoder_spec_compliant as [dec_implies_valid [valid_implies_dec dec_strictly_increasing]]. *)
(*   assert (valid_codepoints nil) as nil_valid_codepoints. { *)
(*     apply List.Forall_nil. *)
(*   } *)
(*   apply valid_codepoints_iff_enc in nil_valid_codepoints as [bytes encode_nil]. *)
(*   assert (valid_utf8_bytes nil) as nil_valid_bytes. { *)
(*     constructor. *)
(*   } *)
(*   apply valid_implies_dec in nil_valid_bytes as [codes decode_nil]. *)
(*   destruct (encoder codes) as [bytes2 codes_rest] eqn:encode_codes. *)
(*   destruct (decoder bytes) as [codes2 bytes_rest] eqn:decode_bytes. *)
(*   specialize (enc_strictly_increasing nil codes bytes bytes2 nil codes_rest encode_nil encode_codes). *)
(*   specialize (dec_strictly_increasing nil bytes codes codes2 nil bytes_rest decode_nil decode_bytes). *)
(*   unfold codepoints_lt in enc_strictly_increasing, dec_strictly_increasing. *)
(*   simpl in enc_strictly_increasing, dec_strictly_increasing. *)
(*   destruct codes. *)

(* Theorem encoder_spec_valid_all_equal : forall encoder1 encoder2, *)
(*     utf8_encoder_spec encoder1 -> *)
(*     utf8_encoder_spec encoder2 -> *)
(*     forall codes bytes codes_suffix, *)
(*       encoder1 codes = (bytes, codes_suffix) -> *)
(*       exists codes_prefix, encoder2 codes_prefix = (bytes, nil) /\ codes = (codes_prefix ++ codes_suffix). *)
(* Proof. *)
(*   intros encoder1 encoder2 encoder1_spec_compliant encoder2_spec_compliant. *)
(*   unfold utf8_encoder_spec, encoder_encode_correctly_implies_valid, encoder_encode_valid_codes_correctly, encoder_strictly_increasing in encoder1_spec_compliant, encoder2_spec_compliant. *)
(*   destruct encoder1_spec_compliant as [enc1_implies_valid_utf8_bytes [valid_codepoints_iff_enc1 enc1_strictly_increasing]]. *)
(*   destruct encoder2_spec_compliant as [enc2_implies_valid_utf8_bytes [valid_codepoints_iff_enc2 enc2_strictly_increasing]]. *)
(*   intros codes bytes enc1_codes. *)
(*   assert (exists bytes, encoder1 codes = (bytes, nil)) as codes_valid. { *)
(*     exists bytes. apply enc1_codes. *)
(*   } *)
(*   apply <- valid_codepoints_iff_enc1 in codes_valid. *)
(*   apply valid_codepoints_iff_enc2 in codes_valid as enc2_codes. *)
(*   destruct enc2_codes as [bytes2 enc2_codes]. *)
(*   specialize (enc1_strictly_increasing codes codes bytes bytes nil nil codes_valid codes_valid enc1_codes enc1_codes). *)
(*   specialize (enc2_strictly_increasing codes codes bytes2 bytes2 nil nil codes_valid codes_valid enc2_codes enc2_codes). *)
(*   rewrite enc1_strictly_increasing in enc2_strictly_increasing. *)
  
(* Admitted. *)

Lemma decoder_spec_injective : forall decoder,
    utf8_decoder_spec decoder ->
    forall (bytes1 bytes2: list byte) codes,
      decoder bytes1 = (codes, []) ->
      decoder bytes2 = (codes, []) ->
      bytes1 = bytes2.
Proof.
  intros decoder decoder_spec_compliant.
  assert (G := decoder_spec_compliant).
  unfold utf8_decoder_spec, decoder_decode_correctly_implies_valid, decoder_decode_valid_utf8_bytes_correctly, decoder_strictly_increasing in G.
  destruct G as [dec_implies_valid_utf8_bytes [valid_bytes_iff_enc dec_strictly_increasing]].
  intros bytes1 bytes2 codes decoder_bytes1 decoder_bytes2.
  specialize (dec_strictly_increasing bytes1 bytes2 codes codes decoder_bytes1 decoder_bytes2) as compare_codes.
  specialize (bytes_compare_antisymmetric bytes1 bytes2) as G.
  rewrite (@antisymmetric_reflexive (list codepoint) codepoints_compare codepoints_compare_antisymmetric) in compare_codes.
  rewrite <- compare_codes in G.
  apply G.
Qed.

Lemma decoder_spec_nil_mapsto_nil : forall decoder,
    utf8_decoder_spec decoder ->
    decoder nil = (nil, []).
  intros decoder decoder_spec_compliant.
  assert (G := decoder_spec_compliant).
  unfold utf8_decoder_spec, decoder_decode_correctly_implies_valid, decoder_decode_valid_utf8_bytes_correctly, decoder_strictly_increasing in G.
  destruct G as [dec_implies_valid_utf8_bytes [valid_bytes_iff_enc dec_strictly_increasing]].
  assert (valid_utf8_bytes []) as nil_valid. constructor. apply valid_bytes_iff_enc in nil_valid.
  destruct nil_valid.
  
  Admitted.

Theorem decode_encode_spec_compliant_decode_inverse_of_encode : forall encoder decoder,
    utf8_encoder_spec encoder ->
    utf8_decoder_spec decoder ->
    forall codes bytes codes_suffix,
      encoder codes = (bytes, codes_suffix) ->
      exists codes_prefix, decoder bytes = (codes_prefix, nil) /\ codes = (codes_prefix ++ codes_suffix)%list.
Proof.
  intros encoder decoder encoder_spec_compliant decoder_spec_compliant.
  assert (G1 := encoder_spec_compliant).
  assert (G2 := decoder_spec_compliant).
  unfold utf8_encoder_spec, encoder_encode_correctly_implies_valid, encoder_encode_valid_codes_correctly, encoder_strictly_increasing in G1.
  destruct G1 as [enc_implies_valid_utf8_bytes [valid_codepoints_iff_enc [enc_strictly_increasing enc_projects]]].
  unfold utf8_decoder_spec, decoder_decode_correctly_implies_valid, decoder_decode_valid_utf8_bytes_correctly, decoder_strictly_increasing in G2.
  destruct G2 as [dec_implies_valid [valid_implies_dec dec_strictly_increasing]].
  intros codes bytes codes_suffix encoder_codes.
  apply enc_implies_valid_utf8_bytes in encoder_codes as G.
  destruct G as [bytes_valid [codes_prefix [codes_prefix_eq encoder_prefix]]].
  exists codes_prefix. split; [| apply codes_prefix_eq]. clear encoder_codes. clear codes_prefix_eq.
  apply valid_implies_dec in bytes_valid.
  destruct bytes_valid as [codes2 decode_bytes].
  apply dec_implies_valid in decode_bytes as G.
  destruct G as [codes2_valid _].
  apply valid_codepoints_iff_enc in codes2_valid.
  destruct codes2_valid as [bytes2 encoder_codes2].
  specialize (enc_strictly_increasing codes_prefix codes2 bytes bytes2 encoder_prefix encoder_codes2).
  apply enc_implies_valid_utf8_bytes in encoder_codes2.
  destruct encoder_codes2 as [bytes2_valid _].
  apply valid_implies_dec in bytes2_valid as [codes3 decode_bytes2].
  specialize (dec_strictly_increasing bytes bytes2 codes2 codes3 decode_bytes decode_bytes2).
  rewrite <- enc_strictly_increasing in dec_strictly_increasing.
  symmetry in dec_strictly_increasing.
  specialize (codepoints_compare_transitive codes_prefix codes2 codes3 dec_strictly_increasing) as codes_trans.
  induction codes2.
  - unfold codepoints_compare in *. simpl in *.
    destruct codes3. 
Qed.

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
        
