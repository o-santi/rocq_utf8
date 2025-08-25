From Coq Require Import Strings.String.
From Coq Require Import ZArith.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.

Require Import Utf8.Parser.
Require Import Utf8.Theorems.Parser.
Require Import Utf8.Utf8.

Open Scope string_scope.

(* The character sequence U+0041 U+2262 U+0391 U+002E "A<NOT IDENTICAL 
   TO><ALPHA>." is encoded in UTF-8 as follows: *)

(*     --+--------+-----+-- *)
(*     41 E2 89 A2 CE 91 2E *)
(*     --+--------+-----+-- *)

From Coq.Strings Require Import Byte.
Definition test1 :
  (fmap (fun '(s, r) => (List.map show_codepoint s, r)) (utf8_decode [x41; xe2; x89; xa2; xce; x91; x2e]))
  = Ok (["U+0041"%string; "U+2262"%string; "U+0391"%string; "U+002E"%string], []).
  reflexivity.
Qed.

(* The character sequence U+D55C U+AD6D U+C5B4 (Korean "hangugeo", *)
(* meaning "the Korean language") is encoded in UTF-8 as follows: *)

(*     --------+--------+-------- *)
(*     ED 95 9C EA B5 AD EC 96 B4 *)
(*     --------+--------+-------- *)
Definition test2 :
  (fmap (fun '(s, r) => (List.map show_codepoint s, r)) (utf8_decode [xed; x95; x9c; xea; xb5; xad; xec; x96; xb4]))
  = Ok (["U+D55C"%string; "U+AD6D"%string; "U+C5B4"%string], []).
  reflexivity.
Qed.

(* The character sequence U+65E5 U+672C U+8A9E (Japanese "nihongo", *)
(* meaning "the Japanese language") is encoded in UTF-8 as follows: *)

(*     --------+--------+-------- *)
(*     E6 97 A5 E6 9C AC E8 AA 9E *)
(*     --------+--------+-------- *)
Definition test3 :
  (fmap (fun '(s, r) => (List.map show_codepoint s, r)) (utf8_decode [xe6; x97; xa5; xe6; x9c; xac; xe8; xaa; x9e]))
  = Ok (["U+65E5"%string; "U+672C"%string; "U+8A9E"%string], []).
  reflexivity.
Qed.

(* The character U+233B4 (a Chinese character meaning 'stump of tree'), *)
(* prepended with a UTF-8 BOM, is encoded in UTF-8 as follows: *)

(*     --------+----------- *)
(*     EF BB BF F0 A3 8E B4 *)
(*     --------+----------- *)

Definition test4 :
  (fmap (fun '(s, r) => (List.map show_codepoint s, r)) (utf8_decode [xef; xbb; xbf; xf0; xa3; x8e; xb4]))
  = Ok (["U+FEFF"%string; "U+0233B4"%string], []).
  simpl.
  reflexivity.
Qed.


Ltac destruct_parse_continuation :=
  match goal with
  | [G: context[parse_continuation (?a::?b)] |- _] => idtac
  | [H: context[parse_continuation ?text] |- _] => destruct text; [ try discriminate | ]
  end;
  match goal with
  | [H: context[parse_continuation (?b::?rest)] |- _] =>
      unfold parse_continuation in H;
      rewrite parser_map_correct in H;
      simpl in H;
      let B1 := fresh "b" in
      let B2 := fresh "b" in
      let B3 := fresh "b" in
      let B4 := fresh "b" in
      let B5 := fresh "b" in
      let B6 := fresh "b" in
      let B7 := fresh "b" in
      let B8 := fresh "b" in
      let eqn_name := fresh "byte_bits" in
      let eqn_name2 := fresh "byte_of_bits" in
      destruct (Byte.to_bits b) as [B1 [B2 [B3 [B4 [B5 [B6 [B7 B8]]]]]]] eqn:eqn_name;
      match goal with
      | [G: context[if (?a && negb ?b) then _ else _] |- _ ] =>
          destruct a; destruct b; try discriminate G; simpl in H; rewrite eqn_name in H;
          apply (f_equal Byte.of_bits) in eqn_name;
          rewrite Byte.of_bits_to_bits in eqn_name
      end
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
  | Utf8.codepoint =>
      unfold Utf8.codepoint, Utf8.b4 in byte;
      destruct byte as [[[[[b b4_1] b4_2] b4_3] b4_4] b4_5];
      break_bit b4_1; break_bit b4_2; break_bit b4_3; break_bit b4_4; break_bit b4_5
  | Utf8.b7 =>
      unfold Utf8.b7 in byte; break_bit byte
  | Utf8.b6 =>
      unfold Utf8.b6 in byte; break_bit byte
  | Utf8.b5 =>
      unfold Utf8.b5 in byte; break_bit byte
  | Utf8.b4 =>
      unfold Utf8.b4 in byte; break_bit byte
  | Utf8.b3 =>
      unfold Utf8.b3 in byte; break_bit byte
  | Byte.byte =>
      let B := fresh "B" in
      let eqn_name := fresh "byte_bits" in
      remember (Byte.to_bits byte) as B eqn:eqn_name;
      break_bit B;
      symmetry in eqn_name;
      apply (f_equal Byte.of_bits) in eqn_name;
      rewrite Byte.of_bits_to_bits in eqn_name
  end.



Ltac crush_bits :=
  repeat match goal with
    | |- context[if ?bit then _ else _] => destruct bit
    | _: context[if ?bit then _ else _ ] |- _ => destruct bit
    end.

Ltac no_overlongs2 :=
  repeat match goal with
    | [ H: ?bit = _ \/ ?b |- _] => destruct H
    | [ G: ?bit = _ |- context[if ?bit then _ else _] ] => rewrite G
    | [ F: context[if ?bit then _ else _] |- _] => destruct bit
    | |- context[if ?bit then _ else _] => destruct bit
    end.

Opaque Byte.of_bits.

Theorem utf8_encode_codepoint_one_correct: forall (c: codepoint) b1 b2 b3 b4 b5 b6 b7,
    utf8_encode_codepoint c = Ok [ Byte.of_bits (b7, (b6, (b5, (b4, (b3, (b2, (b1, false))))))) ]
    <-> c = (false, b4_zero, b4_zero, b4_zero, (false, b1, b2, b3), (b4, b5, b6, b7)).
Proof.
  split; intros.
  - unfold utf8_encode_codepoint in H. to_bits c.
    repeat match goal with
           | [_: context[if ?bit then _ else _] |- _] => destruct bit
           | [_: _ = _ |- _] => try discriminate
           end.
    injection H; intros H0. 
    apply (f_equal Byte.to_bits) in H0. repeat rewrite Byte.to_bits_of_bits in H0. inversion H0. subst. reflexivity.
  - subst. unfold utf8_encode_codepoint, b4_zero. reflexivity.
Defined.

Theorem utf8_encode_codepoint_two_correct: forall (c: codepoint) b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11,
    utf8_encode_codepoint c = Ok [ Byte.of_bits (b5,  (b4,  (b3, (b2, (b1, (false,  (true, true)))))));
                                   Byte.of_bits (b11, (b10, (b9, (b8, (b7, (b6, (false, true))))))) ]
    <-> (c = (false, b4_zero, b4_zero, (false, b1, b2, b3), (b4, b5, b6, b7), (b8, b9, b10, b11))
       /\ (b1 = true \/ b2 = true \/ b3 = true \/ b4 = true)).
Proof.
  split; intros.
  - unfold utf8_encode_codepoint in H. to_bits c.
    repeat match goal with
           | [_: context[if ?bit then _ else _] |- _] => destruct bit
           | [_: _ = _ |- _] => try discriminate
           end;
      injection H; intros H1 H2;
      apply (f_equal Byte.to_bits) in H1, H2;
      repeat (rewrite Byte.to_bits_of_bits in H1, H2); inversion H1; inversion H2; subst; split; auto.
  - destruct H. subst. unfold utf8_encode_codepoint, b4_zero.
    no_overlongs2; subst; reflexivity.
Defined.

Theorem utf8_encode_codepoint_three_correct: forall (c: codepoint) b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16,
    utf8_encode_codepoint c = Ok [ Byte.of_bits (b4,  (b3,  (b2,  (b1,  (false,   (true, (true, true)))))));
                                   Byte.of_bits (b10, (b9,  (b8,  (b7,  (b6,  (b5,  (false, true)))))));
                                   Byte.of_bits (b16, (b15, (b14, (b13, (b12, (b11, (false, true)))))))]
    <-> (c = (false, b4_zero, (b1, b2, b3, b4), (b5, b6, b7, b8), (b9, b10, b11, b12), (b13, b14, b15, b16))
       /\ (b1 = true \/ b2 = true \/ b3 = true \/ b4 = true \/ b5 = true) (* no overlong encodings *)
       /\ (b1 = false \/ b2 = false \/ b3 = true \/ b4 = false \/ b5 = false)).
Proof.
  split; intros.
  - unfold utf8_encode_codepoint in H. to_bits c.
    repeat match goal with
           | [_: context[if ?bit then _ else _] |- _] => destruct bit
           | [_: _ = _ |- _] => try discriminate
           end;
      injection H; intros H1 H2 H3;
      apply (f_equal Byte.to_bits) in H1, H2, H3;
      repeat (rewrite Byte.to_bits_of_bits in H1, H2, H3); inversion H1; inversion H2; inversion H3; subst; repeat split; auto.
  - destruct H as [H1 [H2 H3]]. unfold utf8_encode_codepoint, b4_zero in *. to_bits c. inversion_clear H1; subst.
    no_overlongs2; subst; try discriminate; auto.
Defined.

Theorem utf8_encode_codepoint_four_correct: forall (c: codepoint) b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21,
    utf8_encode_codepoint c = Ok [ Byte.of_bits (b3,  (b2,  (b1,  (false,   (true,  (true,   (true, true)))))));
                                   Byte.of_bits (b9,  (b8,  (b7,  (b6,  (b5,  (b4,  (false, true)))))));
                                   Byte.of_bits (b15, (b14, (b13, (b12, (b11, (b10, (false, true)))))));
                                   Byte.of_bits (b21, (b20, (b19, (b18, (b17, (b16, (false, true))))))) ]
    <-> (c = (b1, (b2, b3, b4, b5), (b6, b7, b8, b9), (b10, b11, b12, b13), (b14, b15, b16, b17), (b18, b19, b20, b21))
       /\ ((b1 = true /\ b2 = false /\ b3 = false /\ b4 = false /\ b5 = false)
          \/ (b1 = false /\ (b2 = true \/ b3 = true \/ b4 = true \/ b5 = true)))).
Proof.
  split; intros.
  - unfold utf8_encode_codepoint in H. to_bits c.
    crush_bits; try discriminate;
      injection H; intros H1 H2 H3 H4;
      apply (f_equal Byte.to_bits) in H1, H2, H3, H4;
      repeat (rewrite Byte.to_bits_of_bits in H1, H2, H3, H4); inversion H1; inversion H2; inversion H3; inversion H4; subst; repeat split; tauto.
  - unfold utf8_encode_codepoint, b4_zero in *. to_bits c.
    destruct H as [c_eq [[eb1 [eb2 [eb3 [eb4 eb5]]]] | [eb1 [eb2 | [ eb3 | [ eb4 | eb5]]]]]];
      inversion c_eq;
      crush_bits; subst; try discriminate; auto.
Defined.

Lemma utf8_encode_codepoint_correct : forall (c: codepoint),
    (exists e, utf8_encode_codepoint c = Err e)
    \/ 
      (exists b1 b2 b3 b4 b5 b6 b7,
          utf8_encode_codepoint c = Ok [ Byte.of_bits (b7, (b6, (b5, (b4, (b3, (b2, (b1, false))))))) ])
    \/ (exists b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11,
          utf8_encode_codepoint c = Ok [ Byte.of_bits (b5,  (b4,  (b3, (b2, (b1, (false,  (true, true)))))));
                                         Byte.of_bits (b11, (b10, (b9, (b8, (b7, (b6, (false, true))))))) ]) 
    \/ (exists b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16,
          utf8_encode_codepoint c = Ok [ Byte.of_bits (b4,  (b3,  (b2,  (b1,  (false,   (true, (true, true)))))));
                                         Byte.of_bits (b10, (b9,  (b8,  (b7,  (b6,  (b5,  (false, true)))))));
                                         Byte.of_bits (b16, (b15, (b14, (b13, (b12, (b11, (false, true)))))))])
    \/ (exists b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21,
          utf8_encode_codepoint c = Ok[ Byte.of_bits (b3,  (b2,  (b1,  (false,   (true,  (true,   (true, true)))))));
                                        Byte.of_bits (b9,  (b8,  (b7,  (b6,  (b5,  (b4,  (false, true)))))));
                                        Byte.of_bits (b15, (b14, (b13, (b12, (b11, (b10, (false, true)))))));
                                        Byte.of_bits (b21, (b20, (b19, (b18, (b17, (b16, (false, true))))))) ]). 
Proof.
  intros.
  destruct (utf8_encode_codepoint c) eqn: utf8_enc_codepoint_c. 
  to_bits c.
  unfold utf8_encode_codepoint in utf8_enc_codepoint_c. symmetry in utf8_enc_codepoint_c.
  crush_bits;
    repeat match type of utf8_enc_codepoint_c with
      | Ok _ = Err _ => discriminate
      | context[Ok [_]] => right; left; repeat eexists; apply utf8_enc_codepoint_c
      | context[Ok [_; _]]  => right; right; left; repeat eexists; apply utf8_enc_codepoint_c
      | context[Ok [_; _; _]]  => right; right; right; left; repeat eexists; apply utf8_enc_codepoint_c
      | context[Ok [_; _; _; _]]  => right; right; right; right; repeat eexists; apply utf8_enc_codepoint_c
      end. left. eexists. reflexivity.
Defined.

Ltac for_all_valid_utf8_encodings c :=
  let encodings := constr:(utf8_encode_codepoint_correct c) in
  let rec f H :=
    match type of H with
    | exists error: unicode_encode_error, _ => let e := fresh "err" in destruct H as [err H]
    | exists bit : bool, _ => let b := fresh "b" in destruct H as [b _rest]; f _rest
    | ?a /\ ?b /\ ?c => destruct H as [eq [c_eq no_overlong]]
    | ?a /\ ?b => destruct H as [eq c_eq]
    | ?a \/ ?b => destruct H as [A | B]; [f A | f B]
    | utf8_encode_codepoint c = _ => idtac
    end
  in f encodings.

Theorem encoding_size_correct :
  (forall byte b1 b2 b3 b4 b5 b6 b7, byte = (Byte.of_bits (b1, (b2, (b3, (b4, (b5, (b6, (b7, false)))))))) <->
                                  encoding_size_from_header byte = Some (OneByte (b7, b6, b5, b4, b3, b2, b1)))
  /\ (forall byte b1 b2 b3 b4 b5, byte = (Byte.of_bits (b1, (b2, (b3, (b4, (b5, (false, (true, true)))))))) <->
                              encoding_size_from_header byte = Some (TwoBytes (b5, b4, b3, b2, b1)))
  /\ (forall byte b1 b2 b3 b4, byte = (Byte.of_bits (b1, (b2, (b3, (b4, (false, (true, (true, true)))))))) <->
                           encoding_size_from_header byte = Some (ThreeBytes (b4, b3, b2, b1)))
  /\ (forall byte b1 b2 b3, byte = (Byte.of_bits (b1, (b2, (b3, (false, (true, (true, (true, true)))))))) <->
                        encoding_size_from_header byte = Some (FourBytes (b3, b2, b1))).
Proof.
  repeat (split; intros; subst);
    try (unfold encoding_size_from_header; repeat rewrite Byte.to_bits_of_bits;
         repeat match goal with
           | [ |- (if ?bit then _ else _) = _ ] => destruct bit
           | [ |- (_ = _)] => reflexivity
           end);
    unfold encoding_size_from_header in H;
    to_bits byte;
    rewrite byte_bits; 
    crush_bits; try discriminate; inversion H; try reflexivity.
Defined.

Lemma enc_one_spec: forall b1 b2 b3 b4 b5 b6 b7, encoding_size_from_header (Byte.of_bits (b1, (b2, (b3, (b4, (b5, (b6, (b7, false)))))))) = Some (OneByte (b7, b6, b5, b4, b3, b2, b1)).
Proof.
  intros.
  destruct encoding_size_correct as [e1 [e2 [e3 e4]]].
  eapply e1. reflexivity.
Defined.

Lemma enc_two_spec: forall b1 b2 b3 b4 b5, encoding_size_from_header (Byte.of_bits (b1, (b2, (b3, (b4, (b5, (false, (true, true)))))))) = Some (TwoBytes (b5, b4, b3, b2, b1)).
Proof.
  intros.
  destruct encoding_size_correct as [e1 [e2 [e3 e4]]].
  eapply e2. reflexivity.
Defined.

Lemma enc_three_spec: forall b1 b2 b3 b4, encoding_size_from_header (Byte.of_bits (b1, (b2, (b3, (b4, (false, (true, (true, true)))))))) = Some (ThreeBytes (b4, b3, b2, b1)).
Proof.
  intros.
  destruct encoding_size_correct as [e1 [e2 [e3 e4]]].
  eapply e3. reflexivity.
Defined.

Lemma enc_four_spec: forall b1 b2 b3, encoding_size_from_header (Byte.of_bits (b1, (b2, (b3, (false, (true, (true, (true, true)))))))) = Some (FourBytes (b3, b2, b1)).
Proof.
  intros.
  destruct encoding_size_correct as [e1 [e2 [e3 e4]]].
  eapply e4. reflexivity.
Defined.

Theorem parse_continuation_correct: forall byte rest b1 b2 b3 b4 b5 b6,
    parse_continuation (byte :: rest) = Ok ((b6, b5, b4, b3, b2, b1), rest) <-> byte = Byte.of_bits (b1, (b2, (b3, (b4, (b5, (b6, (false, true))))))).
Proof.
  intros. split; intros.
  - destruct_parse_continuation. inversion H; subst. reflexivity.
  - subst. unfold parse_continuation. rewrite parser_map_correct. unfold predicate. rewrite Byte.to_bits_of_bits. unfold fmap, bind. assert (true && negb false = true). reflexivity. rewrite H. rewrite Byte.to_bits_of_bits. reflexivity.
Defined.

Theorem parse_continuation_strong_progress: forall suffix response text,
    (parse_continuation text = Ok (response, suffix)) ->
    length suffix < length text.
Proof.
  intros.
  generalize dependent response.
  generalize dependent suffix.
  induction text as [| byte1 text_rest]; intros.
  - inversion H.
  - destruct_parse_continuation. inversion H. subst.
    simpl. lia.
Defined.

Lemma parse_continuation_spec: forall rest b1 b2 b3 b4 b5 b6, parse_continuation ((Byte.of_bits (b1, (b2, (b3, (b4, (b5, (b6, (false, true)))))))) :: rest) = Ok ((b6, b5, b4, b3, b2, b1), rest).
Proof.
  intros.
  eapply parse_continuation_correct.
  reflexivity.
Defined.

Theorem parse_codepoint_encode_correct : forall c bytes rest,
    utf8_encode_codepoint c = Ok bytes ->
    parse_codepoint (bytes ++ rest)%list = Ok (c, rest).
Proof.
  Opaque Byte.of_bits.
  intros.
  for_all_valid_utf8_encodings c; try (rewrite H in A; discriminate); [
      apply utf8_encode_codepoint_one_correct in _rest as c_eq
    | apply utf8_encode_codepoint_two_correct in _rest as G; destruct G as [c_eq no_overlongs]
    | apply utf8_encode_codepoint_three_correct in _rest as G; destruct G as [c_eq [no_overlongs no_surrogates]]
    | apply utf8_encode_codepoint_four_correct in _rest as G; destruct G as [c_eq no_overlongs]];
    rewrite H in _rest;
    injection _rest; intros; rewrite H0;
    simpl; unfold parse_codepoint, parse_header, encoding_size_from_header, parse_continuation; rewrite Byte.to_bits_of_bits;
    crush_bits;
    subst; simpl;
    repeat (rewrite parser_map_correct; simpl; rewrite Byte.to_bits_of_bits; simpl; rewrite Byte.to_bits_of_bits);
    try reflexivity;
    no_overlongs2; auto; subst; try discriminate.
  destruct no_overlongs as [[eb1 [eb2 [eb3 [eb4 eb5]]]] | [eb1 [eb2 | [ eb3 | [ eb4 | eb5]]]]]; discriminate.
Defined.

Theorem encode_parse_codepoint_correct : forall bytes code rest,
    parse_codepoint bytes = Ok (code, rest) -> 
    exists prefix,
      (utf8_encode_codepoint code = Ok prefix) /\ bytes = (prefix ++ rest)%list.
Proof.
  intros.
  destruct bytes; [ discriminate H |].
  unfold parse_codepoint, parse_header, encoding_size_from_header, bind in H.
  to_bits b; crush_bits; try discriminate H;
    match type of H with
    | context[FirstRange _] => inversion H; subst; repeat eexists
    | context[SecondRange _ _] => destruct_parse_continuation; crush_bits; try discriminate; inversion H; subst; repeat eexists
    | context[ThirdRange _ _ _] => destruct_parse_continuation; rewrite  parser_map_correct in H; unfold predicate in H; destruct bytes as [| byte bytes_rest]; try discriminate H;
                                  to_bits byte; destruct b17; destruct b16; try discriminate; simpl in H; rewrite byte_bits1 in H; rewrite Byte.to_bits_of_bits in H; crush_bits; inversion H; subst; repeat eexists
    | context[FourthRange _ _ _] => destruct_parse_continuation; rewrite parser_map_correct in H; destruct bytes as [| bytes bytes_rest]; try discriminate; to_bits bytes;
                                   apply (f_equal Byte.to_bits) in byte_bits1 as byte_to_bits1; rewrite Byte.to_bits_of_bits in byte_to_bits1; simpl in H; rewrite byte_to_bits1 in H; destruct b17; destruct b16; try discriminate; simpl in H;
                                   rewrite parser_map_correct in H; destruct bytes_rest as [| byte1 bytes_rest1]; try discriminate; to_bits byte1;
                                   apply (f_equal Byte.to_bits) in byte_bits2 as byte_to_bits2; rewrite Byte.to_bits_of_bits in byte_to_bits2; simpl in H; rewrite byte_to_bits2 in H; destruct b23; destruct b22; try discriminate; simpl in H; rewrite byte_to_bits1 in H; rewrite byte_to_bits2 in H; crush_bits; try discriminate; inversion H; subst; repeat eexists

  | _ => idtac
  end.
Defined.

Theorem parse_codepoint_injective : forall bytes1 bytes2 code rest,
    parse_codepoint bytes1 = Ok (code, rest) ->
    parse_codepoint bytes2 = Ok (code, rest) ->
    bytes1 = bytes2.
Proof.
Admitted.
  (* intro bytes1.
  destruct bytes1; intros.
  - inversion H.
  - destruct bytes2.
    + inversion H0.
    + unfold parse_codepoint, parse_header, encoding_size_from_header in *. to_bits b; to_bits b0. crush_bits; try inversion H0; try inversion H; f_equal; *)
  (*       simpl in *; try (rewrite <- H2 in H4; inversion H4; subst; *)
  (*       rewrite <- byte_bits in byte_bits0; apply (f_equal Byte.of_bits) in byte_bits0; repeat rewrite (Byte.of_bits_to_bits) in byte_bits0; auto). *)
      

Lemma parse_single_codepoint_correct : forall c bytes,
    (utf8_encode_codepoint c) = Ok bytes ->
    parse_codepoint bytes = Ok (c, []).
Proof.
  intros.
  apply parse_codepoint_encode_correct  with (rest := []) in H.
  rewrite List.app_nil_r in H.
  apply H.
Defined.

Ltac no_overlong_encoding Hyp :=
  repeat match type of Hyp with
    | context[if ?bit then _ else _] => destruct bit
    | Err _ = Ok _ => discriminate Hyp
    end.

Lemma parse_codepoint_strong_progress: forall rest code text,
    parse_codepoint text = Ok (code, rest) ->
    length rest < length text.
Proof.
  intros.
  apply encode_parse_codepoint_correct in H as G.
  destruct G as [prefix [encode bytes_part]].
  rewrite bytes_part. rewrite length_app.
  for_all_valid_utf8_encodings code. rewrite A in encode. discriminate.
  1-4: rewrite _rest in encode; inversion encode; simpl; lia.
Defined.
    
Theorem encode_decode_correct_strong : forall (unicode unicode_rest: unicode_str) bytes,
  forall unicode_lesser,
    (length unicode_lesser) <= (length unicode) -> 
    utf8_encode unicode_lesser = Ok (bytes, unicode_rest) ->
    utf8_decode bytes = Ok (unicode_lesser, []).
Proof.
  intros unicode.
  induction unicode; intros.
  - inversion H. rewrite length_zero_iff_nil in H2. subst. inversion H0. reflexivity.
  - destruct unicode_lesser as [| codepoint1 unicode_rest1] eqn:E_lesser.
    + inversion H0. reflexivity.
    + simpl in H0.
      destruct (utf8_encode_codepoint codepoint1) as [utf8_bytes | err ] eqn:U_enc_codepoint1; [| discriminate H0].
      destruct (utf8_encode unicode_rest1) as [[val2 rest2] | err] eqn:U_enc_unicode_rest1; [| discriminate H0].
      inversion_clear H0. subst.
      apply IHunicode in U_enc_unicode_rest1; try (simpl in H; lia).
      unfold utf8_decode, all. simpl.
      apply parse_codepoint_encode_correct with (c := codepoint1) (rest := val2) in U_enc_codepoint1.
      rewrite U_enc_codepoint1.
      apply parse_codepoint_strong_progress in U_enc_codepoint1.
      unfold bind.
      rewrite <- all_aux_saturation_aux with (n := (S (Datatypes.length (utf8_bytes ++ val2))));
        try apply parse_codepoint_strong_progress; try lia.
      fold (all parse_codepoint val2). fold (utf8_decode val2). rewrite U_enc_unicode_rest1.
      destruct ((utf8_bytes ++ val2)%list) eqn:L.
      * apply app_eq_nil in L as [L1 L2]. subst. inversion U_enc_codepoint1.
      * reflexivity.
Defined.

Theorem encode_decode_correct : forall unicode unicode_rest bytes,
    utf8_encode unicode = Ok (bytes, unicode_rest) ->
    utf8_decode bytes = Ok (unicode, []).
Proof.
  intros.
  apply encode_decode_correct_strong with (unicode := unicode) (unicode_rest := unicode_rest). lia.
  apply H.
Defined.

Theorem decode_encode_correct_strong: forall (bytes bytes_rest: list Byte.byte) (unicode: unicode_str),
  forall bytes_lesser,
    (length bytes_lesser) <= (length bytes) ->
    utf8_decode bytes_lesser = Ok (unicode, bytes_rest) ->
    utf8_encode unicode = Ok (bytes_lesser, []).
Proof.
  intros bytes.
  induction bytes; intros.
  - inversion H. rewrite length_zero_iff_nil in H2. subst. inversion H0. split; reflexivity.
  - destruct bytes_lesser as [| byte1 bytes_rest1] eqn:E_lesser.
    + inversion H0; reflexivity.
    + unfold utf8_decode, all in H0. simpl in H0.
      destruct (parse_codepoint (byte1 :: bytes_rest1)) as [[code1 bytes_rest2] | err] eqn:Parse_bytes1; [| discriminate H0].
      destruct (parse_codepoint bytes_rest2) as [[code2 bytes_rest3] | err] eqn:Parse_bytes_rest2.
      2: {
        destruct bytes_rest2. inversion_clear H0; subst. unfold utf8_encode.
        destruct (utf8_encode_codepoint code1) eqn:U_enc_code1.
        * simpl. apply parse_codepoint_encode_correct with (rest:= []) in U_enc_code1.
          rewrite app_nil_r in *.
          apply parse_codepoint_injective with (bytes1 := byte1::bytes_rest1) in U_enc_code1.
          rewrite U_enc_code1. reflexivity. auto.
        * apply encode_parse_codepoint_correct in Parse_bytes1 as [prefix [enc r]]. rewrite enc in U_enc_code1. discriminate.
        * discriminate H0.
      }
      unfold bind in H0.
      destruct bytes_rest2; try discriminate.
      rewrite <- all_aux_saturation_aux with (n := S (length bytes_rest1)) in H0. fold (all parse_codepoint bytes_rest3) in H0. fold (utf8_decode bytes_rest3) in H0.
      2: apply parse_codepoint_strong_progress.
      2,3: apply parse_codepoint_strong_progress in Parse_bytes1; apply parse_codepoint_strong_progress in Parse_bytes_rest2; simpl in *; lia.
      destruct (utf8_decode bytes_rest3) as [[codes bytes_rest4] | err] eqn:Parse_bytes_rest3; try discriminate H0.
      inversion H0; subst.
      apply encode_parse_codepoint_correct in Parse_bytes1 as G1, Parse_bytes_rest2 as G2. destruct G1 as [prefix1 [enc1 bytes_part1]]. destruct G2 as [prefix2 [enc2 bytes_part2]].
      apply IHbytes in Parse_bytes_rest3.
      unfold utf8_encode. fold utf8_encode.
      rewrite enc1. rewrite enc2. rewrite Parse_bytes_rest3. simpl. rewrite <- bytes_part2. rewrite <- bytes_part1. reflexivity.
      simpl in *.
      apply parse_codepoint_strong_progress in Parse_bytes1, Parse_bytes_rest2. simpl in *. lia.
Defined. 

Theorem decode_encode_correct: forall (unicode: unicode_str) (bytes rest: list Byte.byte),
    utf8_decode bytes = Ok (unicode, rest) ->
    utf8_encode unicode = Ok (bytes, []).
Proof.
  intros.
  apply decode_encode_correct_strong with (bytes:= bytes) (bytes_rest:=rest). lia. apply H.
Defined.

Local Notation "0" := false.
Local Notation "1" := true.

Definition codepoint_less_than_10ffff (code: codepoint) : Prop :=
  match code with
  | (0, (b2, b3, b4, b5), (b6, b7, b8, b9), (b10, b11, b12, b13), (b14, b15, b16, b17), (b18, b19, b20, b21)) => True
  | (1, (0,  0,  0,  0), (b6, b7, b8, b9), (b10, b11, b12, b13), (b14, b15, b16, b17), (b18, b19, b20, b21)) => True
  | _ => False
  end.

Definition codepoint_is_not_surrogate (code: codepoint) : Prop :=
  match code with
  | (0, (0, 0, 0, 0), (1, 1, 0, 1), (1, b6, b7, b8), (b9, b10, b11, b12), (b13, b14, b15, b16)) => False
  | _ => True
  end.

Definition valid_codepoint (code: codepoint) := codepoint_less_than_10ffff code /\ codepoint_is_not_surrogate code.

Theorem encode_valid_codepoint : forall code,
    valid_codepoint code <->
    exists bytes, utf8_encode_codepoint code = Ok bytes.
Proof.
  split; intros.
  unfold utf8_encode_codepoint, valid_codepoint in *.
  destruct H as [H1 H2].
  to_bits code.
  crush_bits; simpl in *; try easy; repeat eexists.
  destruct H.
  unfold utf8_encode_codepoint in H.
  to_bits code.
  crush_bits; try discriminate; easy.
Qed.

Theorem utf8_encode_valid_codepoints : forall codepoints,
    Forall valid_codepoint codepoints <->
    exists bytes, utf8_encode codepoints = Ok (bytes, []).
Proof.
  split; intros.
  induction H as [| code rest].
  - repeat eexists. 
  - unfold utf8_encode. apply encode_valid_codepoint in H.
    destruct H.
    rewrite H. destruct IHForall.
    fold (utf8_encode rest). rewrite H1. repeat eexists.
  - generalize dependent H. induction codepoints; intros.
    + auto.
    + rewrite Forall_cons_iff. destruct H. unfold utf8_encode in H. fold utf8_encode in H.
      destruct (utf8_encode_codepoint a) eqn:U; [ | discriminate].
      split.
      apply <- encode_valid_codepoint. exists x0. apply U.
      destruct (utf8_encode codepoints) as [[code unicode_rest] | err] eqn:Utf8Encode; [| discriminate].
      simpl in H. inversion H. subst. clear H.
      apply IHcodepoints.
      exists code. reflexivity.
Qed.
  
Theorem parsed_codepoint_is_valid : forall code bytes rest,
    parse_codepoint bytes = Ok (code, rest) -> valid_codepoint code.
Proof.
  intros.
  apply encode_parse_codepoint_correct in H as [prefix [G1 G2]]. 
  apply encode_valid_codepoint.
  exists prefix. apply G1.
Qed.

Theorem utf8_decode_valid_codepoints : forall bytes codepoints,
    utf8_decode bytes = Ok (codepoints, []) ->
    Forall valid_codepoint codepoints.
Proof.
  intros.
  apply decode_encode_correct in H.
  apply utf8_encode_valid_codepoints.
  exists bytes. apply H.
Qed.
