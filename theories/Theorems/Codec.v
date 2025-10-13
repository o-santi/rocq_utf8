Require Import Utf8.Spec.
Require Import Utf8.Codec.

From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import ZArith.BinInt.
From Coq Require Import Lia.



(* The character sequence U+0041 U+2262 U+0391 U+002E "A<NOT IDENTICAL
   TO><ALPHA>." is encoded in UTF-8 as follows: *)

(*     --+--------+-----+-- *)
(*     41 E2 89 A2 CE 91 2E *)
(*     --+--------+-----+-- *)

Example test1_encode :
  utf8_encode [0x0041; 0x2262; 0x0391; 0x002E] = ([0x41; 0xe2; 0x89; 0xa2; 0xce; 0x91; 0x2e], []).
  reflexivity.
Qed.

Example test1_decode :
  utf8_dfa_decode [0x41; 0xe2; 0x89; 0xa2; 0xce; 0x91; 0x2e] = ([0x0041; 0x2262; 0x0391; 0x002E], []).
  reflexivity.
Qed.

(* The character sequence U+D55C U+AD6D U+C5B4 (Korean "hangugeo", *)
(* meaning "the Korean language") is encoded in UTF-8 as follows: *)

(*     --------+--------+-------- *)
(*     ED 95 9C EA B5 AD EC 96 B4 *)
(*     --------+--------+-------- *)

Example test2_encode :
  utf8_encode [0xD55C; 0xAD6D; 0xC5B4] = ([0xed; 0x95; 0x9c; 0xea; 0xb5; 0xad; 0xec; 0x96; 0xb4], []).
reflexivity. 
Qed.

Example test2_decode : utf8_dfa_decode [0xed; 0x95; 0x9c; 0xea; 0xb5; 0xad; 0xec; 0x96; 0xb4]
  = ([0xD55C; 0xAD6D; 0xC5B4], []).
  reflexivity.
Qed.

(* The character sequence U+65E5 U+672C U+8A9E (Japanese "nihongo", *)
(* meaning "the Japanese language") is encoded in UTF-8 as follows: *)

(*     --------+--------+-------- *)
(*     E6 97 A5 E6 9C AC E8 AA 9E *)
(*     --------+--------+-------- *)

Example test3_encode :
  utf8_encode [0x65E5; 0x672C; 0x8A9E] = ([0xe6; 0x97; 0xa5; 0xe6; 0x9c; 0xac; 0xe8; 0xaa; 0x9e], []).
  reflexivity.
Qed.

Example test3_decode : utf8_dfa_decode [0xe6; 0x97; 0xa5; 0xe6; 0x9c; 0xac; 0xe8; 0xaa; 0x9e]
  = ([0x65E5; 0x672C; 0x8A9E], []).
  reflexivity.
Qed.

(* The character U+233B4 (a Chinese character meaning 'stump of tree'), *)
(* prepended with a UTF-8 BOM, is encoded in UTF-8 as follows: *)

(*     --------+----------- *)
(*     EF BB BF F0 A3 8E B4 *)
(*     --------+----------- *)

Example test4_encode : utf8_encode [0xFEFF; 0x0233B4]
  = ([0xef; 0xbb; 0xbf; 0xf0; 0xa3; 0x8e; 0xb4], []).
  reflexivity.
Qed.

Example test4_decode : utf8_dfa_decode [0xef; 0xbb; 0xbf; 0xf0; 0xa3; 0x8e; 0xb4]
  = ([0xFEFF; 0x0233B4], []).
  reflexivity.
Qed.

Lemma utf8_encode_error_suffix : encoder_error_suffix utf8_encode.
Admitted.

Lemma utf8_encode_monoid : encoder_monoid_morphism utf8_encode.
Admitted.
Lemma utf8_encode_output : encoder_output_single utf8_encode.
Admitted.
Lemma utf8_encode_increasing: encoder_strictly_increasing utf8_encode.
Admitted.

Theorem utf8_encode_spec_compliant : utf8_encoder_spec utf8_encode.
Proof.
  split.
  - apply utf8_encode_error_suffix.
  - apply utf8_encode_monoid.
  - apply utf8_encode_output.
  - apply utf8_encode_increasing.
Qed.
  
  
Lemma utf8_dfa_error_suffix_strong: forall (bytes_big bytes: byte_str) (codes : unicode_str) (rest : byte_str),
    ((length bytes) <= (length bytes_big))%nat ->
    utf8_dfa_decode bytes = (codes, rest) ->
    exists valid_prefix : list byte,
      bytes = valid_prefix ++ rest /\ utf8_dfa_decode valid_prefix = (codes, []) /\ no_prefix valid_utf8_bytes rest.
Proof.
  induction bytes_big; intros bytes codes rest less_than decode_bytes.
  - inversion less_than. apply length_zero_iff_nil in H0. subst.
    inversion decode_bytes. subst.
    exists []. repeat split.
    intros p p_prefix.
    unfold prefix in p_prefix. symmetry in p_prefix.
    apply app_eq_nil in p_prefix. destruct p_prefix. auto.
  - destruct bytes as [| b1 bytes].
    -- inversion decode_bytes. subst.
       exists []. repeat split.
       intros p p_prefix.
       unfold prefix in p_prefix. symmetry in p_prefix.
       apply app_eq_nil in p_prefix. destruct p_prefix. auto.
    -- unfold utf8_dfa_decode, utf8_dfa_decode_rec in decode_bytes.
       fold utf8_dfa_decode_rec in decode_bytes.
       unfold next_state in decode_bytes.
       destruct (byte_range_dec b1) as [b1_range|] eqn:B1Range.
       --- admit.
       --- admit.
Admitted.

Lemma utf8_dfa_error_suffix : decoder_error_suffix utf8_dfa_decode.
Proof.
Admitted.  
  

Lemma utf8_dfa_comonoid : decoder_comonoid_morphism utf8_dfa_decode.
Proof.
Admitted.

Lemma utf8_dfa_output_single : decoder_output_single utf8_dfa_decode.
Proof.
Admitted.

Lemma utf8_dfa_increasing : decoder_strictly_increasing utf8_dfa_decode.
Proof.
Admitted.
        
Theorem utf8_decoder_spec_compliant : utf8_decoder_spec utf8_dfa_decode.
Proof.
  split.
  - apply utf8_dfa_error_suffix.
  - apply utf8_dfa_comonoid.
  - apply utf8_dfa_output_single.
  - apply utf8_dfa_increasing.
Qed.
    
