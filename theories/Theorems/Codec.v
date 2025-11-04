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

Lemma utf8_encode_nil : encoder_nil utf8_encode.
Proof.
  reflexivity.
Qed.

Lemma utf8_encode_codepoint_input : forall code,
    valid_codepoint code <->
    exists bytes, utf8_encode_codepoint code = Some bytes.
Proof.
  intro code; split. 
  - intro valid_code.
    destruct (utf8_encode_codepoint code) as [bytes |] eqn:encode_code.
    + exists bytes. reflexivity.
    + unfold utf8_encode_codepoint in encode_code.
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
             | [G: context[if andb ?a ?b then _ else _] |- _] =>
                 let range1 := fresh "range" in
                 let range2 := fresh "range" in
                 destruct a eqn:range1;
                 destruct b eqn:range2; simpl in G;
                 try discriminate; try lia
             end.
  - intros [bytes encode_code].
    unfold utf8_encode_codepoint in encode_code.
    unfold valid_codepoint, codepoint_less_than_10ffff, codepoint_is_not_surrogate, codepoint_not_negative.
    repeat match goal with
           | [G: context[if (code <=? ?val) then _ else _] |- _] =>
               let range := fresh "range" in
               destruct (code <=? val) eqn:range; try discriminate; try lia
           | [G: context[if code <? ?val then _ else _] |- _] =>
               let range := fresh "range" in
               destruct (code <? val) eqn:range; try discriminate; try lia
           | [G: context[if andb ?a ?b then _ else _] |- _] =>
               let range1 := fresh "range" in
               let range2 := fresh "range" in
               destruct a eqn:range1;
               destruct b eqn:range2; simpl in G;
               try discriminate; try lia
           end.
Qed.


Lemma utf8_encode_correct : encoder_input_correct_iff utf8_encode.
Proof.
  intros code. split.
  - intro valid_code.
    destruct (utf8_encode [code]) as [bytes rest] eqn: enc.
    exists bytes. apply pair_equal_spec. repeat split.
    simpl in enc.
    apply utf8_encode_codepoint_input in valid_code.
    destruct valid_code as [bytes2 enc_code]. rewrite enc_code in enc.
    inversion enc. reflexivity.
  - intros [bytes enc_code].
    simpl in enc_code.
    destruct (utf8_encode_codepoint code) as [bytes2 |] eqn:enc_single; [| discriminate].
    inversion enc_code. subst.
    apply utf8_encode_codepoint_input.
    exists bytes2. assumption.
Qed.

Lemma utf8_encode_output : encoder_output_correct utf8_encode.
Proof.
  intros code.
  destruct (utf8_encode [code]) as [bytes rest] eqn:encode_single.
  simpl in encode_single.
  destruct (utf8_encode_codepoint code) as [bytes2 |] eqn:encode_code; [| inversion encode_single; split; reflexivity].
  assert (exists bytes, utf8_encode_codepoint code = Some bytes) as code_valid. exists bytes2. assumption.
  apply utf8_encode_codepoint_input in code_valid.
  unfold valid_codepoint, codepoint_less_than_10ffff, codepoint_is_not_surrogate, codepoint_not_negative in code_valid.
  destruct code_valid as [c1 [c2 c3]].
  inversion encode_single. rewrite app_nil_r in *. subst.
  unfold utf8_encode_codepoint in encode_code.
  repeat match goal with
         | [G: context[if (code <=? ?val) then _ else _] |- _] =>
             let range := fresh "range" in
             destruct (code <=? val) eqn:range; try discriminate; try lia
         | [G: context[if code <? ?val then _ else _] |- _] =>
             let range := fresh "range" in
             destruct (code <? val) eqn:range; try discriminate; try lia
         | [G: context[if andb ?b false then _ else _] |- _] =>
             replace (andb b false) with false in G by reflexivity
         | [G: context[if andb false ?b then _ else _] |- _] =>
             replace (andb false b) with false in G by reflexivity
         | [G: context[if andb true true then _ else _] |- _] =>
             replace (andb true true) with true in G by reflexivity               
         | [G: context[if andb ?a ?b then _ else _] |- _] =>
             let range1 := fresh "range" in
             let range2 := fresh "range" in
             destruct a eqn:range1; try discriminate; try lia;
             destruct b eqn:range2; try discriminate; try lia
         end; rewrite <- some_injective in encode_code; subst.
  + apply OneByte. lia.
  + add_bounds (code mod 64). apply TwoByte; lia.
  + add_bounds (code mod 64).
    add_bounds ((code / 64) mod 64).
    destruct c2.
    * destruct (code / 64 / 64 =? 0) eqn:is_e0.
      -- apply ThreeByte1; lia.
      -- destruct (code <? 0xd000) eqn:code_less_d000.
         --- apply ThreeByte2. left. all: lia.
         --- apply ThreeByte3; lia.
    * apply ThreeByte2. right. all: lia.
  + add_bounds (code mod 64).
    add_bounds (code / 64 mod 64).
    add_bounds ((code / 64 / 64) mod 64).
    destruct (code / 64 / 64 / 64 =? 0) eqn:is_f0.
    * apply FourBytes1; try lia.
    * destruct (code / 64 / 64 / 64 =? 4) eqn:is_f4.
      -- apply FourBytes3; try lia.
      -- apply FourBytes2; try lia.
Qed.

Lemma utf8_encode_projects : encoder_projects utf8_encode.
Proof.
  intro xs. induction xs as [|x xs]; intros ys.
  - rewrite utf8_encode_nil. rewrite app_nil_l.
    destruct (utf8_encode ys). reflexivity.
  - rewrite <- app_comm_cons.
    unfold utf8_encode. fold utf8_encode.
    destruct (utf8_encode_codepoint x) as [bytes |]eqn:encode_x.
    + rewrite IHxs.
      destruct (utf8_encode xs). destruct (utf8_encode ys).
      destruct l0. rewrite app_assoc. reflexivity. reflexivity.
    + rewrite app_comm_cons. reflexivity.
Qed.

 
Lemma utf8_encode_increasing: encoder_strictly_increasing utf8_encode.
Proof.
  intros code1 code2 bytes1 bytes2 encode_code1 encode_code2.
  simpl in encode_code1, encode_code2.
  destruct (utf8_encode_codepoint code1) as [bytes1'|] eqn:enc_code1; [|inversion encode_code1].
  destruct (utf8_encode_codepoint code2) as [bytes2'|] eqn:enc_code2; [|inversion encode_code2]. rewrite app_nil_r in *.
  inversion encode_code1. inversion encode_code2. subst.
  clear encode_code1. clear encode_code2.
  unfold utf8_encode_codepoint in enc_code1, enc_code2.
  repeat match goal with
         | [G: context[if (?code <=? ?val) then _ else _] |- _] =>
             let range := fresh "range" in
             destruct (code <=? val) eqn:range; try discriminate; try lia
         | [G: context[if ?code <? ?val then _ else _] |- _] =>
             let range := fresh "range" in
             destruct (code <? val) eqn:range; try discriminate; try lia
         | [G: context[if andb ?b false then _ else _] |- _] =>
             replace (andb b false) with false in G by reflexivity
         | [G: context[if andb false ?b then _ else _] |- _] =>
             replace (andb false b) with false in G by reflexivity
         | [G: context[if andb true true then _ else _] |- _] =>
             replace (andb true true) with true in G by reflexivity               
         | [G: context[if andb ?a ?b then _ else _] |- _] =>
             let range1 := fresh "range" in
             let range2 := fresh "range" in
             destruct a eqn:range1; try discriminate; try lia;
             destruct b eqn:range2; try discriminate; try lia
         end; rewrite <- some_injective in enc_code1; rewrite <- some_injective in enc_code2; subst; unfold bytes_compare, list_compare.
  1: destruct (code1 ?= code2); reflexivity.
  all: (repeat match goal with
          | |- context[match ?a ?= ?b with | _ => _ end] =>
              let comp := fresh "compare" in
              add_bounds a; add_bounds b;
              destruct (Z.compare_spec a b) as [comp | comp | comp]
          end);
    match goal with
    | [|- (?n1 ?= ?n2 = Eq)] => apply Z.compare_eq_iff
    | [|- (?n1 ?= ?n2 = Lt)] => fold (Z.lt n1 n2)
    | [|- (?n1 ?= ?n2 = Gt)] => fold (Z.gt n1 n2)
    end; subst; try discriminate; lia.
Qed.

Theorem utf8_encode_spec_compliant : utf8_encoder_spec utf8_encode.
Proof.
  split.
  - apply utf8_encode_nil.
  - apply utf8_encode_increasing.
  - apply utf8_encode_correct.
  - apply utf8_encode_output.
  - apply utf8_encode_projects.
Qed.
  
Lemma utf8_dfa_nil : decoder_nil utf8_dfa_decode.
Proof.
  reflexivity.
Qed.

Lemma utf8_dfa_decode_invalid: forall bytes suffix,
    utf8_dfa_decode bytes = ([], suffix) ->
    bytes = suffix.
Proof.
  intros bytes suffix decode_bytes.
  unfold utf8_dfa_decode in decode_bytes.
  destruct bytes as [| byte1 bytes].
  - simpl in decode_bytes. inversion decode_bytes. reflexivity.
  - do 2 lazymatch goal with
           | [NextState: context[next_state ?state ?carry ?byte] |- _] =>
               unfold next_state in NextState;
               let range := fresh "range" in
               idtac byte;
               destruct (byte_range_dec byte) as [range|];
               [| inversion NextState; reflexivity];
               destruct range;
               try (inversion NextState; reflexivity)
           | [Decode: context[utf8_dfa_decode_rec (?byte :: ?rest) ?code ?state ?consumed] |- _] =>
               simpl in Decode
           | [Decode: context[utf8_dfa_decode_rec ?bytes 0 Initial ?consumed] |- _] =>
               destruct (utf8_dfa_decode_rec bytes 0 Initial); inversion Decode
           | [Decode: context[utf8_dfa_decode_rec ?bytes ?code ?state ?consumed] |- _] =>
               let byte := fresh "byte" in
               let rest := fresh "bytes" in
               destruct bytes as [| byte rest]; simpl in Decode;
               [inversion Decode; reflexivity|]
           end.

Lemma utf8_dfa_output : decoder_output_correct utf8_dfa_decode.
Proof.
  intros bytes suffix codes decode_bytes.
  induction codes.
  - split. constructor.
    exists []. repeat split. constructor.
    apply utf8_dfa_decode_invalid in decode_bytes.
    subst. reflexivity.
    
    

Lemma utf8_dfa_input : decoder_input_correct_iff utf8_dfa_decode.
Proof.
Admitted.


Lemma utf8_dfa_increasing : decoder_strictly_increasing utf8_dfa_decode.
Proof.
Admitted.

Lemma utf8_dfa_accepts_codepoint_repr : forall bytes,
    valid_codepoint_representation bytes ->
    exists code, utf8_dfa_decode bytes = ([code], []).
Proof.
  Admitted.

Lemma utf8_dfa_projects : decoder_projects utf8_dfa_decode.
Proof.
  intros xs ys valid_xs.
  destruct valid_xs.
  2: { 
  - 
  unfold next_state. 
       
Theorem utf8_decoder_spec_compliant : utf8_decoder_spec utf8_dfa_decode.
Proof.
  split.
  - apply utf8_dfa_nil.
  - apply utf8_dfa_input.
  - apply utf8_dfa_output.
  - apply utf8_dfa_increasing.
  - apply utf8_dfa_projects.
Qed.

