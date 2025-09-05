From Coq Require Import Strings.String.
From Coq Require Import ZArith.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.

Require Import Utf8.Parser.
Require Import Utf8.Theorems.Parser.
Require Import Utf8.Spec.
Require Import Utf8.Theorems.Spec.
Require Import Utf8.Utf8.

Open Scope string_scope.
Open Scope bool_scope.

(* The character sequence U+0041 U+2262 U+0391 U+002E "A<NOT IDENTICAL 
   TO><ALPHA>." is encoded in UTF-8 as follows: *)

(*     --+--------+-----+-- *)
(*     41 E2 89 A2 CE 91 2E *)
(*     --+--------+-----+-- *)

From Coq.Strings Require Import Byte.
Definition test1 :
  let '(codes, _) := utf8_decode [x41; xe2; x89; xa2; xce; x91; x2e] in
  List.map show_codepoint codes
  = ["U+0041"%string; "U+2262"%string; "U+0391"%string; "U+002E"%string].
  reflexivity.
Qed.

(* The character sequence U+D55C U+AD6D U+C5B4 (Korean "hangugeo", *)
(* meaning "the Korean language") is encoded in UTF-8 as follows: *)

(*     --------+--------+-------- *)
(*     ED 95 9C EA B5 AD EC 96 B4 *)
(*     --------+--------+-------- *)
Definition test2 :
  let '(codes, _) := utf8_decode [xed; x95; x9c; xea; xb5; xad; xec; x96; xb4] in
  List.map show_codepoint codes
  = ["U+D55C"%string; "U+AD6D"%string; "U+C5B4"%string].
  reflexivity.
Qed.

(* The character sequence U+65E5 U+672C U+8A9E (Japanese "nihongo", *)
(* meaning "the Japanese language") is encoded in UTF-8 as follows: *)

(*     --------+--------+-------- *)
(*     E6 97 A5 E6 9C AC E8 AA 9E *)
(*     --------+--------+-------- *)
Definition test3 :
  let '(codes, _) := utf8_decode [xe6; x97; xa5; xe6; x9c; xac; xe8; xaa; x9e] in
  List.map show_codepoint codes
  = ["U+65E5"%string; "U+672C"%string; "U+8A9E"%string].
  reflexivity.
Qed.

(* The character U+233B4 (a Chinese character meaning 'stump of tree'), *)
(* prepended with a UTF-8 BOM, is encoded in UTF-8 as follows: *)

(*     --------+----------- *)
(*     EF BB BF F0 A3 8E B4 *)
(*     --------+----------- *)

Definition test4 :
  let '(codes, _) := utf8_decode [xef; xbb; xbf; xf0; xa3; x8e; xb4] in
  List.map show_codepoint codes
  = ["U+FEFF"%string; "U+0233B4"%string].
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

Ltac no_overlongs2 :=
  repeat match goal with
    | [ H: ?bit = _ \/ ?b |- _] => destruct H
    | [ G: ?bit = _ |- context[if ?bit then _ else _] ] => rewrite G
    | [ F: context[if ?bit then _ else _] |- _] => destruct bit
    | |- context[if ?bit then _ else _] => destruct bit
    end.

Opaque Byte.of_bits.

(* ================= *)
(* Utf8 ENCODER PART *)
(* ================= *)

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
Qed.

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

Lemma if_redundant : forall T (P: T) (b: bool), (if b then P else P) = P.
Proof.
  destruct b; reflexivity.
Qed.


Theorem utf8_encode_codepoint_three_correct: forall (c: codepoint) b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16,
    utf8_encode_codepoint c = Ok [ Byte.of_bits (b4,  (b3,  (b2,  (b1,  (false,   (true, (true, true)))))));
                                   Byte.of_bits (b10, (b9,  (b8,  (b7,  (b6,  (b5,  (false, true)))))));
                                   Byte.of_bits (b16, (b15, (b14, (b13, (b12, (b11, (false, true)))))))]
    <-> (c = (false, b4_zero, (b1, b2, b3, b4), (b5, b6, b7, b8), (b9, b10, b11, b12), (b13, b14, b15, b16))
       /\ (b1 = true \/ b2 = true \/ b3 = true \/ b4 = true \/ b5 = true) (* no overlong encodings *)
       /\ (b1 = false \/ b2 = false \/ b3 = true \/ b4 = false \/ b5 = false)).
Proof.
  split; intros.
  - unfold utf8_encode_codepoint in H. to_bits c. crush_bits; try discriminate; inversion H;
      apply (f_equal Byte.to_bits) in H1,H2,H3; repeat rewrite Byte.to_bits_of_bits in H1,H2,H3;
      inversion H1; inversion H2; inversion H3; subst; tauto.
  - destruct H as [code [[G1 | [G1 | [G1 | [G1 | G1]]]] [G2 | [G2 | [G2 | [G2 | G2]]]]]]; subst; try discriminate; simpl; repeat rewrite if_redundant; reflexivity.
Qed.

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
Qed.

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

Theorem encode_valid_codepoint : forall code,
    valid_codepoint code ->
    exists bytes, utf8_encode_codepoint code = Ok bytes.
Proof.
  intros.
  - pose (eq_refl (utf8_encode_codepoint code)) as Code.
    unfold valid_codepoint in H. destruct H as [LessThan NotSurrogate].
    to_bits code.
    unfold codepoint_less_than_10ffff in LessThan.
    unfold codepoint_is_not_surrogate in NotSurrogate.
    crush_bits; try easy; simpl in Code.
    10: crush_bits.
    all: match type of Code with
    | Ok ?bytes = Ok ?bytes => exists bytes
         end; split; try easy.
Qed.

Theorem encode_ok_implies_valid_codepoint : forall code bytes,
    utf8_encode_codepoint code = Ok bytes ->
    valid_codepoint code.
Proof.
  intros code bytes encode_ok.
  unfold utf8_encode_codepoint in encode_ok.
  unfold valid_codepoint, codepoint_less_than_10ffff, codepoint_is_not_surrogate.
  to_bits code.
  crush_bits; auto; discriminate.
Qed.

Theorem encode_ok_implies_valid_bytes : forall code bytes,
    utf8_encode_codepoint code = Ok bytes ->
    valid_utf8_bytes bytes.
Proof.
  intros code bytes encode_ok.
  apply encode_ok_implies_valid_codepoint in encode_ok as valid_code.
  unfold valid_codepoint, codepoint_less_than_10ffff, codepoint_is_not_surrogate in valid_code.
  to_bits code.
  crush_bits; try easy; simpl in encode_ok.
  10: crush_bits.
  all: inversion encode_ok; validate_utf8_bytes.
Qed.

Theorem utf8_encode_valid_codepoints : forall codepoints,
    valid_codepoints codepoints <->
    exists! bytes, utf8_encode codepoints = (bytes, []).
Proof.
  split; intros.
  induction H as [| code rest].
  - eexists. eexists. reflexivity. intros. inversion H. reflexivity.
  - unfold utf8_encode. apply encode_valid_codepoint in H.
    destruct H as [bytes encode_ok].
    rewrite encode_ok. destruct IHForall as [bytes_rest [encode_rest_ok uniqueness]].
    fold (utf8_encode rest). rewrite encode_rest_ok. repeat eexists.
    intros bytes' bytes'_eq. inversion bytes'_eq. reflexivity.
  - unfold valid_codepoints. generalize dependent H. induction codepoints; intros.
    + auto.
    + rewrite Forall_cons_iff. destruct H as [bytes [encode_codes uniqueness]]. unfold utf8_encode in encode_codes. fold utf8_encode in encode_codes.
      destruct (utf8_encode_codepoint a) eqn:U; [ | discriminate].
      split.
      apply encode_ok_implies_valid_codepoint in U. apply U.
      apply IHcodepoints.
      destruct (utf8_encode codepoints) as [bytes' unicode_rest] eqn:EncCodes.
      inversion encode_codes.
      exists bytes'. split. reflexivity.
      intros. inversion H. reflexivity.
Qed.

Theorem utf8_encoder_implies_valid_bytes_strong : forall (codes_big codes: list codepoint) (bytes : list byte) codes_suffix,
    (length codes) <= (length codes_big) ->
    utf8_encode codes = (bytes, codes_suffix) ->
    valid_utf8_bytes bytes /\ exists codes_prefix, codes = (codes_prefix ++ codes_suffix)%list.
Proof.
  intros codes_big; induction codes_big; intros codes bytes rest LessThan EncodeOk.
  1: { inversion LessThan. rewrite length_zero_iff_nil in H0. subst. inversion EncodeOk. split. easy. exists []. reflexivity. } 
  destruct codes as [| code code_rest].
  1: { inversion EncodeOk. split. easy. exists []. reflexivity. } 
  unfold utf8_encode in EncodeOk. fold utf8_encode in EncodeOk.
  destruct (utf8_encode_codepoint code) as [bytes2| err] eqn:EncCode.
  2: { inversion EncodeOk. split. easy. subst. exists []. reflexivity.} 
  destruct (utf8_encode code_rest) as [bytes3 code_rest2] eqn:EncCodes.
  inversion EncodeOk.
  apply IHcodes_big in EncCodes as [EncCodesValidUtf8 [codes_prefix code_rest_eq]]; [ | simpl in LessThan; lia].
  apply encode_ok_implies_valid_bytes in EncCode as EncCodeValidUtf8.
  split. 
  - apply valid_utf8_bytes_concat.
    apply EncCodeValidUtf8.
    apply EncCodesValidUtf8.
  - subst. exists (code :: codes_prefix). reflexivity.
Qed.

Theorem utf8_encoder_implies_valid_bytes: forall codes bytes codes_suffix,
    utf8_encode codes = (bytes, codes_suffix) ->
    valid_utf8_bytes bytes /\ exists codes_prefix, codes = (codes_prefix ++ codes_suffix)%list.
Proof.
  intros.
  apply utf8_encoder_implies_valid_bytes_strong with (codes_big := codes) (codes := codes) (codes_suffix := codes_suffix). lia.
  apply H.
Qed.
  
Theorem utf8_encoder_is_compliant : utf8_encoder_spec utf8_encode.
Proof.
  unfold utf8_encoder_spec.
  split.
  - unfold encoder_encode_correctly_implies_valid.
    intros.
    apply utf8_encoder_implies_valid_bytes. apply H.
  - unfold encoder_encode_valid_codes_correctly.
    intros.
    apply utf8_encode_valid_codepoints.
Qed.

(* ================= *)
(* UTF8 DECODER PART *)
(* ================= *)

Theorem parse_continuation_correct: forall byte rest b1 b2 b3 b4 b5 b6,
    parse_continuation (byte :: rest) = Ok ((b6, b5, b4, b3, b2, b1), rest) <-> byte = Byte.of_bits (b1, (b2, (b3, (b4, (b5, (b6, (false, true))))))).
Proof.
  intros. split; intros.
  - destruct_parse_continuation. inversion H; subst. reflexivity.
  - subst. unfold parse_continuation. rewrite parser_map_correct. unfold predicate. rewrite Byte.to_bits_of_bits. unfold fmap, bind. assert (true && negb false = true). reflexivity. rewrite H. rewrite Byte.to_bits_of_bits. reflexivity.
Defined.

Theorem parse_continuation_consumes_only_one_byte: forall byte rest1 rest2 b1 b2 b3 b4 b5 b6,
    parse_continuation (byte :: rest1) = Ok ((b6, b5, b4, b3, b2, b1), rest2) ->
    rest1 = rest2.
Proof.
  intros. 
  destruct_parse_continuation. inversion H; subst. reflexivity.
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

  end.
Defined.

Lemma parse_header_spec : forall byte bytes enc rest,
    parse_header (byte :: bytes) = Ok (enc, rest) ->
    (bytes = rest /\
       ((exists b1 b2 b3 b4 b5 b6 b7, to_bits byte = (b1, (b2, (b3, (b4, (b5, (b6, (b7, false))))))) /\ enc = OneByte (b7, b6, b5, b4, b3, b2, b1)) \/
          (exists b1 b2 b3 b4 b5, to_bits byte = (b1, (b2, (b3, (b4, (b5, (false, (true, true))))))) /\ enc = TwoBytes (b5, b4, b3, b2, b1)) \/
          (exists b1 b2 b3 b4, to_bits byte = (b1, (b2, (b3, (b4, (false, (true, (true, true))))))) /\ enc = ThreeBytes (b4, b3, b2, b1)) \/
          (exists b1 b2 b3, to_bits byte = (b1, (b2, (b3, (false, (true, (true, (true, true))))))) /\ enc = FourBytes (b3, b2, b1)))).
Proof.
  intros byte bytes enc rest parse_header_ok.
  unfold parse_header in parse_header_ok.
  unfold encoding_size_from_header in parse_header_ok. to_bits byte.
  crush_bits; inversion parse_header_ok; apply (f_equal Byte.to_bits) in byte_bits;
    rewrite Byte.to_bits_of_bits in byte_bits; repeat split; try easy; 
    match goal with
    | [_: context[OneByte _] |- _] => left
    | [_: context[TwoBytes  _] |- _ ] => right; left
    | [_: context[ThreeBytes _] |- _]  => right; right; left
    | [_: context[FourBytes  _] |- _] => right; right; right
    end; repeat eexists.
Qed.

Theorem valid_bytes_implies_parse_codepoint_ok  : forall byte bytes,
    valid_utf8_bytes (byte :: bytes) ->
      exists code rest, parse_codepoint (byte :: bytes) = Ok (code, rest).
Proof.
  intros byte bytes valid_bytes.
  simpl in valid_bytes.
  destruct_valid_bytes valid_bytes;
  unfold parse_codepoint, parse_header, encoding_size_from_header; subst;
        rewrite Byte.to_bits_of_bits;
  repeat (simpl; try rewrite parse_continuation_spec; repeat rewrite if_redundant); simpl; repeat eexists.
  all: no_overlongs2; try discriminate; try reflexivity.
Qed.

Theorem parse_codepoint_ok_implies_valid_codepoint  : forall byte bytes code rest,
    parse_codepoint (byte :: bytes) = Ok (code, rest) ->
    valid_codepoint code /\ exists prefix, (byte::bytes) = (prefix ++ rest)%list.
Proof.
  intros byte bytes code rest parse_codepoint_ok.
  unfold parse_codepoint in parse_codepoint_ok.
  destruct (parse_header (byte :: bytes)) as [[enc_size bytes_rest] | err] eqn:ParseHeader; [| discriminate].
  to_bits code.
  apply parse_header_spec in ParseHeader as [bytes_eq [R | [R | [R | R]]]];
    let rec f B :=
      match type of B with
      | exists (b: bool), ?P => let bit := fresh "b" in
                       let P := fresh "byte_bits"
                       in destruct B as [bit P]; f P
      | ?A /\ ?C => destruct B
      end in f R; rewrite H0 in parse_codepoint_ok; simpl in parse_codepoint_ok; unfold valid_codepoint, codepoint_less_than_10ffff, codepoint_is_not_surrogate.
  - inversion parse_codepoint_ok; split. easy. subst. exists [byte]. reflexivity.
  - destruct_parse_continuation. crush_bits; try discriminate; split; try easy; inversion parse_codepoint_ok; exists [byte; b25]; subst; reflexivity.
  - destruct (parse_continuation bytes_rest) as [[v bytes_rest2] | ?] eqn:ParseCont1; try discriminate. simpl in parse_codepoint_ok. to_bits v.
    destruct (parse_continuation bytes_rest2) as [[v2 bytes_rest3] | ?] eqn:ParseCont2; try discriminate. to_bits v2.
    repeat destruct_parse_continuation.
    simpl in parse_codepoint_ok. crush_bits; try discriminate; split; try easy.
    all: inversion ParseCont1; inversion ParseCont2; exists [byte; b43; b36]; inversion parse_codepoint_ok; subst; reflexivity.
  - destruct (parse_continuation bytes_rest) as [[v bytes_rest2] | ?] eqn:ParseCont1; try discriminate. simpl in parse_codepoint_ok. to_bits v.
    destruct (parse_continuation bytes_rest2) as [[v2 bytes_rest3] | ?] eqn:ParseCont2; try discriminate. to_bits v2. simpl in parse_codepoint_ok.
    destruct (parse_continuation bytes_rest3) as [[v3 bytes_rest4] | ?] eqn:ParseCont3; try discriminate. to_bits v3.
    repeat destruct_parse_continuation.
    simpl in parse_codepoint_ok. crush_bits; try discriminate; split; try easy.
    all: inversion ParseCont1; inversion ParseCont2; inversion ParseCont3; inversion parse_codepoint_ok;
      exists [byte; b55; b48; b41]; subst; reflexivity.
Qed.

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


Theorem parse_codepoint_implies_prefix_valid_bytes : forall byte bytes code rest,
    parse_codepoint (byte :: bytes) = Ok (code, rest) ->
    exists prefix,
      valid_utf8_bytes prefix /\
        (([byte] = prefix /\ bytes = rest)
         \/ match bytes with
           | byte2 :: bytes_rest => [byte; byte2] = prefix /\ rest = bytes_rest
           | _ => False
           end
         \/ match bytes with
           | byte2 :: byte3 :: bytes_rest => [byte; byte2; byte3] = prefix /\ rest = bytes_rest
           | _ => False
           end
         \/ match bytes with
           | byte2 :: byte3 :: byte4 :: bytes_rest =>
               [byte; byte2; byte3; byte4] = prefix /\ rest = bytes_rest
           | _ => False
           end).      
Proof.
  intros byte bytes code rest parse_codepoint_ok.
  unfold parse_codepoint in parse_codepoint_ok.
  destruct (parse_header (byte :: bytes)) as [[size rest2] | err] eqn:ParseHeader; [| discriminate parse_codepoint_ok].
  apply parse_header_spec in ParseHeader as [bytes_eq [G | [G | [G | G]]]];
    destruct_bits G; simpl in parse_codepoint_ok; rewrite Pred in parse_codepoint_ok.
  - exists [byte]. split. rewrite byte_bits0. validate_utf8_bytes. simpl in parse_codepoint_ok. left. inversion parse_codepoint_ok.
    simpl. rewrite <- byte_bits0. subst. split; reflexivity.
  - destruct_parse_continuation. 
    exists [byte; b4].
    rewrite bytes_eq. rewrite byte_bits. rewrite byte_bits0. split; crush_bits; try discriminate; try validate_utf8_bytes; right; left; subst; split; inversion parse_codepoint_ok; reflexivity.
  - destruct (parse_continuation rest2) as [[cont1 rest3] | err] eqn:ParseCont1; [| discriminate parse_codepoint_ok]. simpl in parse_codepoint_ok.
    destruct (parse_continuation rest3) as [[cont2 rest4] | err] eqn:ParseCont2; [| discriminate parse_codepoint_ok].
    repeat destruct_parse_continuation.
    inversion ParseCont1. inversion ParseCont2. 
    exists [byte; b10; b3]. subst.
    simpl in parse_codepoint_ok.
    crush_bits; try discriminate; try validate_utf8_bytes; right; right; left; inversion parse_codepoint_ok; subst; split; reflexivity.
  - destruct (parse_continuation rest2) as [[cont1 rest3] | err] eqn:ParseCont1; [| discriminate parse_codepoint_ok]. simpl in parse_codepoint_ok.
    destruct (parse_continuation rest3) as [[cont2 rest4] | err] eqn:ParseCont2; [| discriminate parse_codepoint_ok]. simpl in parse_codepoint_ok.
    destruct (parse_continuation rest4) as [[cont3 rest5] | err] eqn:ParseCont3; [| discriminate parse_codepoint_ok].
    repeat destruct_parse_continuation.
    inversion ParseCont1. inversion ParseCont2. inversion ParseCont3.
    exists [byte; b16; b9; b2]. subst. 
    simpl in parse_codepoint_ok.
    crush_bits; try discriminate; validate_utf8_bytes; right; right; right; inversion parse_codepoint_ok; subst; split; reflexivity.
Qed.

(* Theorem utf8_decode_valid_utf8_byte_strong : forall bytes_big bytes: list byte, *)
(*     (Datatypes.length bytes) <= (Datatypes.length bytes_big) ->  *)
(*     valid_utf8_bytes bytes -> *)
(*     exists codes : list codepoint, utf8_decode bytes = Ok (codes, []). *)
(* Proof. *)
(*   intros bytes_big. *)
(*   induction bytes_big; intros bytes LessThan bytes_valid; [ inversion LessThan; rewrite length_zero_iff_nil in H0; subst; now eexists |]. *)
(*   destruct bytes as [| byte1 byte_rest ] eqn:Bytes; [ now eexists | ]. *)
(*   simpl in bytes_valid. destruct_valid_bytes bytes_valid. *)
(*   eexists. *)
(*   all: match goal with *)
(*        | [G: valid_utf8_bytes ?bytes |- _] => apply IHbytes_big in G; simpl in LessThan; try lia *)
(*        end. *)
(*   unfold utf8_decode, all. *)
(*   simpl. *)
  
Theorem utf8_decode_ok_implies_valid_codepoints_strong : forall (bytes_big bytes bytes_suffix: list byte) codes,
    (Datatypes.length bytes) <= (Datatypes.length bytes_big) ->
    utf8_decode bytes = (codes, bytes_suffix) ->
    valid_codepoints codes /\ exists bytes_prefix, bytes = (bytes_prefix ++ bytes_suffix)%list.
Proof.    
  intros bytes_big.
  induction bytes_big; intros bytes bytes_suffix codes LessThan decode_ok; unfold valid_codepoints. 
  1: { inversion LessThan; rewrite length_zero_iff_nil in H0; subst. inversion decode_ok. split. easy. exists []. reflexivity. } 
  destruct bytes as [| byte1 byte1_rest].
  1: { inversion decode_ok. split. easy. exists []. reflexivity. }   
  unfold utf8_decode, many, many_aux in decode_ok. fold (@many_aux codepoint byte unicode_decode_error) in decode_ok.
  destruct (parse_codepoint (byte1 :: byte1_rest)) as [[code1 rest1] | err] eqn:ParseCodepoint.
  2: { inversion decode_ok. split. easy. exists []. reflexivity. }
  rewrite <- many_aux_saturation_aux with (n := S (S (length rest1))) in decode_ok. fold (many parse_codepoint rest1) in decode_ok. fold (utf8_decode rest1) in decode_ok.
  2: { apply parse_codepoint_strong_progress. }
  2: simpl in *; lia.
  2: { apply parse_codepoint_strong_progress in ParseCodepoint. lia. }
  destruct (utf8_decode rest1) as [vals rest] eqn:DecodeRest1.
  apply IHbytes_big in DecodeRest1 as [vals_valid_codepoints [bytes_prefix bytes_prefix_eq]].
  2: { inversion decode_ok. subst. apply parse_codepoint_strong_progress in ParseCodepoint. simpl in *. lia. } 
  apply parse_codepoint_ok_implies_valid_codepoint in ParseCodepoint as [code_is_valid  byte_prefix_eq].
  inversion decode_ok. 
  split.
  - apply Forall_cons_iff. split. apply code_is_valid. apply vals_valid_codepoints.
  - subst. destruct byte_prefix_eq as [prefix prefix_eq]. exists (prefix ++ bytes_prefix)%list. rewrite prefix_eq. rewrite app_assoc. reflexivity.
Qed.
  
Theorem utf8_decode_ok_implies_valid_codepoints : forall bytes bytes_suffix codes,
    utf8_decode bytes = (codes, bytes_suffix) ->
    valid_codepoints codes /\ exists bytes_prefix, bytes = (bytes_prefix ++ bytes_suffix)%list.
Proof.
  intros.
  apply utf8_decode_ok_implies_valid_codepoints_strong with (bytes_big := bytes).
  lia. apply H.
Qed.

Theorem utf8_decode_valid_utf8_bytes_iff_decode_ok_strong: forall (bytes_big bytes: list byte),
    (Datatypes.length bytes) <= (Datatypes.length bytes_big) -> 
    valid_utf8_bytes bytes <->
      (exists codes : list codepoint, utf8_decode bytes = (codes, [])).
Proof.
  intros bytes_big. induction bytes_big.
  - intros. inversion H.  rewrite length_zero_iff_nil in H1. subst. split.
    + intros. exists []. reflexivity.
    + intros. easy.
  - intros bytes LessThan. split.
    + intro valid_bytes.
      destruct bytes.
      * exists []. reflexivity.
      * unfold utf8_decode, many, many_aux. fold (@many_aux codepoint byte).
        apply valid_bytes_implies_parse_codepoint_ok in valid_bytes as G.
        destruct G as [code [rest parse_codepoint_ok]].
        rewrite parse_codepoint_ok.
        rewrite <- many_aux_saturation_aux with (n:= S (Datatypes.length (b::bytes))).
        2: apply parse_codepoint_strong_progress.
        2,3: apply parse_codepoint_strong_progress in parse_codepoint_ok; lia.
        fold (many parse_codepoint rest). fold (utf8_decode rest).
        apply parse_codepoint_implies_prefix_valid_bytes in parse_codepoint_ok as [prefix [prefix_valid_utf8 G]].
        destruct G as [ [prefix_eq bytes_eq ] | [bytes_eq | [bytes_eq | bytes_eq]] ].
        -- subst. specialize (valid_utf8_decompose_strong [b] [b] rest ltac:(lia)) as G.
           unfold app in G. apply (G valid_bytes) in prefix_valid_utf8.
           apply IHbytes_big in prefix_valid_utf8 as [codes decode_prefix_ok].
           rewrite decode_prefix_ok. eexists. reflexivity. simpl in LessThan. lia.
        -- destruct bytes; try easy. destruct bytes_eq as [prefix_eq rest_eq].
           subst. specialize (valid_utf8_decompose_strong [b; b0] [b;b0] bytes ltac:(lia)) as G. unfold app in G. apply (G valid_bytes) in prefix_valid_utf8.
           apply IHbytes_big in prefix_valid_utf8 as [codes decode_prefix_ok].
           rewrite decode_prefix_ok. eexists. reflexivity.
           simpl in LessThan. lia.
        -- destruct bytes; try easy; destruct bytes; try easy. destruct bytes_eq as [prefix_eq rest_eq].
           subst. specialize (valid_utf8_decompose_strong [b; b0;b1] [b;b0;b1] bytes ltac:(lia)) as G. unfold app in G. apply (G valid_bytes) in prefix_valid_utf8.
           apply IHbytes_big in prefix_valid_utf8 as [codes decode_prefix_ok].
           rewrite decode_prefix_ok. eexists. reflexivity.
           simpl in LessThan. lia.
        -- destruct bytes; try easy; destruct bytes; try easy; destruct bytes; try easy. destruct bytes_eq as [prefix_eq rest_eq].
           subst. specialize (valid_utf8_decompose_strong [b; b0;b1;b2] [b;b0;b1;b2] bytes ltac:(lia)) as G. unfold app in G. apply (G valid_bytes) in prefix_valid_utf8.
           apply IHbytes_big in prefix_valid_utf8 as [codes decode_prefix_ok].
           rewrite decode_prefix_ok. eexists. reflexivity.
           simpl in LessThan. lia.
    + intros [code decode_ok].
      destruct bytes. easy.
      unfold utf8_decode, many, many_aux in decode_ok. fold (@many_aux codepoint byte) in decode_ok.
      destruct (parse_codepoint (b::bytes)) as [[val rest] | err] eqn:ParseCodepoint.
      2: { inversion decode_ok. }
      rewrite <- many_aux_saturation_aux with (n:= S (S (length rest))) in decode_ok .
      2: apply parse_codepoint_strong_progress.
      2,3 : apply parse_codepoint_strong_progress in ParseCodepoint; lia.
      fold (many parse_codepoint rest) in decode_ok.
      fold (utf8_decode rest) in decode_ok.
      destruct (utf8_decode rest) as [vals bytes_rest] eqn:DecodeOk.
      inversion decode_ok. rewrite H1 in DecodeOk.
      
      specialize (IHbytes_big rest).
      assert ((Datatypes.length rest) <= (Datatypes.length bytes_big)) as G. {
        simpl in LessThan. apply parse_codepoint_strong_progress in ParseCodepoint. simpl in ParseCodepoint. lia.
      }
      specialize (IHbytes_big G). destruct IHbytes_big.
      assert (exists codes, utf8_decode rest = (codes, [])). { exists vals. apply DecodeOk. }
      apply H2 in H3.
      apply parse_codepoint_implies_prefix_valid_bytes in ParseCodepoint as [prefix [prefix_valid_utf8 G1]].
      destruct G1 as [[prefix_eq rest_eq] | [bytes_eq | [bytes_eq | bytes_eq]]]; subst.
      * specialize (valid_utf8_bytes_concat [b] rest prefix_valid_utf8 H3) as ValidAll. apply ValidAll.
      * destruct bytes; try easy. destruct bytes_eq as [prefix_eq rest_eq]. subst.
        specialize (valid_utf8_bytes_concat [b; b0] bytes prefix_valid_utf8 H3) as ValidAll. apply ValidAll.
      * do 2 (destruct bytes; try easy). destruct bytes_eq as [prefix_eq rest_eq]. subst.
        specialize (valid_utf8_bytes_concat [b; b0; b1] bytes prefix_valid_utf8 H3) as ValidAll. apply ValidAll.
      * do 3 (destruct bytes; try easy). destruct bytes_eq as [prefix_eq rest_eq]. subst.
        specialize (valid_utf8_bytes_concat [b; b0; b1; b2] bytes prefix_valid_utf8 H3) as ValidAll. apply ValidAll.
Qed.

Theorem utf8_encoder_spec_compliant : utf8_decoder_spec utf8_decode.
Proof.
  unfold utf8_decoder_spec.
  split.
  - unfold decoder_decode_correctly_implies_valid.
    intros.
    apply utf8_decode_ok_implies_valid_codepoints. apply H.
  - unfold decoder_decode_valid_utf8_bytes_correctly.
    intros.
    apply utf8_decode_valid_utf8_bytes_iff_decode_ok_strong with (bytes_big := bytes).
    lia.
Qed.

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
