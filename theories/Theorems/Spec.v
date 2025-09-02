From Coq Require Import Strings.Byte.
From Coq Require Import Lia.

Require Import Utf8.Parser.
Require Import Utf8.Spec.


Local Notation "1" := true.
Local Notation "0" := false.

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
  
