Require Import Utf8.Spec.
Require Import Utf8.Codec.
Require Import Utf8.Theorems.Order.

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

Lemma utf8_encode_codepoint_input : forall code,
    valid_codepoint code ->
    exists bytes, utf8_encode_codepoint code = Some bytes.
Proof.
  intros code valid_code.
  destruct (utf8_encode_codepoint code) as [bytes |] eqn:encode_code.
  - exists bytes. reflexivity.
  - unfold utf8_encode_codepoint in encode_code.
    destruct valid_code as [c1 [c2 c3]].
    unfold codepoint_less_than_10ffff in c1.
    unfold codepoint_is_not_surrogate in c2.
    unfold codepoint_not_negative in c3.
    repeat match goal with
      | [G: context[if (code <=? ?val) then _ else _] |- _] =>
          
          let range := fresh "range" in
          destruct (code <=? val) eqn:range; try discriminate; try lia
      | [G: context[if code <? ?val then _ else _] |- _] =>
          let range := fresh "range" in
          destruct (code <? val) eqn:range; try discriminate; try lia
      end.
Qed.

Lemma utf8_encode_error_suffix : encoder_error_suffix utf8_encode.
Proof.
  intro codes. induction codes as [| code codes]; intros bytes rest encoder_codes.
  - inversion encoder_codes. subst.
    exists []. repeat split. intros p p_prefix. unfold prefix in p_prefix.
    symmetry in p_prefix.
    apply app_eq_nil in p_prefix. destruct p_prefix. auto.
  - unfold utf8_encode in encoder_codes.
    fold utf8_encode in encoder_codes.
    destruct (utf8_encode_codepoint code) as [bytes2 |] eqn:encode_codepoint_code.
    + destruct (utf8_encode codes) as [bytes3 rest2] eqn:encode_codes.
      specialize (IHcodes bytes3 rest2 ltac:(reflexivity)) as G.
      destruct G as [prefix [codes_eq [encode_prefix no_prefix_rest]]].
      inversion encoder_codes. subst.
      exists (code :: prefix). repeat split.
      * unfold utf8_encode. fold utf8_encode.
        rewrite encode_codepoint_code.
        rewrite encode_prefix.
        reflexivity.
      * assumption.
    + inversion encoder_codes. subst.
      exists []. repeat split.
      intros p p_prefix. unfold prefix in p_prefix.
      apply (f_equal utf8_encode) in p_prefix.
      unfold utf8_encode in p_prefix. fold utf8_encode in p_prefix.
      rewrite encode_codepoint_code in p_prefix.
      destruct p.
      * left. reflexivity.
      * right. intro p_valid. simpl in p_prefix.
        inversion p_valid. apply utf8_encode_codepoint_input in H1.
        destruct H1 as [bytes encode_c]. rewrite encode_c in p_prefix.
        destruct (utf8_encode (p ++ skipn (length p) codes)) as [bytes2 rest].
        inversion p_prefix. symmetry in H3. apply app_eq_nil in H3.
        destruct H3; subst.
        unfold utf8_encode_codepoint in encode_c.
        repeat match goal with
               | [G: context[if c <? ?v then _ else _] |- _] =>
                   destruct (c <? v); try discriminate
               | [G: context[if c <=? ?v then _ else _] |- _] =>
                   destruct (c <=? v); try discriminate
        end.
Qed.

Lemma utf8_encode_monoid : encoder_monoid_morphism utf8_encode.
Proof.
  intro codes1. induction codes1 as [| code1 codes1]; intros codes2 bytes1 bytes2 encode_codes1 encode_codes2.
  - inversion encode_codes1. subst. assumption.
  - unfold utf8_encode in encode_codes1. fold utf8_encode in encode_codes1.
    destruct (utf8_encode_codepoint code1) as [bytes_code1|] eqn:encode_code1; [| inversion encode_codes1].
    destruct (utf8_encode codes1) as [bytes_codes1 rest] eqn:encode_codes1_eq.
    inversion encode_codes1. subst.
    specialize (IHcodes1 codes2 bytes_codes1 bytes2 ltac:(reflexivity) encode_codes2).
    simpl. rewrite encode_code1. rewrite IHcodes1.
    rewrite app_assoc. reflexivity.
Qed.
    
Lemma utf8_encode_output : encoder_output_single utf8_encode.
Proof.
  intros code bytes codes_valid encode_codes.
  apply utf8_encode_codepoint_input in codes_valid as G.
  destruct G as [bytes2 encode_codepoint_code].
  simpl in encode_codes. rewrite encode_codepoint_code in encode_codes.
  inversion encode_codes. rewrite app_nil_r in *. subst.
  clear encode_codes.
  unfold utf8_encode_codepoint in encode_codepoint_code.
  unfold valid_codepoint, codepoint_less_than_10ffff, codepoint_is_not_surrogate, codepoint_not_negative in codes_valid.
  destruct codes_valid as [c1 [c2 c3]].
  repeat match goal with
         | [G: context[if (code <=? ?val) then _ else _] |- _] =>
          
          let range := fresh "range" in
          destruct (code <=? val) eqn:range; try discriminate; try lia
      | [G: context[if code <? ?val then _ else _] |- _] =>
          let range := fresh "range" in
          destruct (code <? val) eqn:range; try discriminate; try lia
         end; rewrite <- some_injective in encode_codepoint_code; subst.
  - apply OneByte. lia.
  - add_bounds (code mod 64). apply TwoByte; lia.
  - add_bounds (code mod 64).
    add_bounds ((code / 64) mod 64).
    destruct c2.
    + destruct (code / 64 / 64 =? 0) eqn:is_e0.
      * apply ThreeByte1; lia.
      * destruct (code <? 0xd000) eqn:code_less_d000.
        ** apply ThreeByte2. left. all: lia.
        ** apply ThreeByte3; lia.
    + apply ThreeByte2. right. all: lia.
  - add_bounds (code mod 64).
    add_bounds (code / 64 mod 64).
    add_bounds ((code / 64 / 64) mod 64).
    destruct (code / 64 / 64 / 64 =? 0) eqn:is_f0.
    + apply FourBytes1; try lia. split; try lia.
      apply (f_equal (fun x => - 64 * (code / 64 / 64 / 64) + x)) in div_mod2.
      rewrite Z.add_assoc in div_mod2.
      replace (-64 * (code / 64 / 64 / 64) + 64 * (code / 64 / 64 / 64)) with 0 in div_mod2 by lia. rewrite Z.add_0_l in div_mod2.
      rewrite <- div_mod2.
      lia.
  
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
    
