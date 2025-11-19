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
      crush_comparisons; try discriminate; lia.
  - intros [bytes encode_code].
    unfold utf8_encode_codepoint in encode_code.
    unfold valid_codepoint, codepoint_less_than_10ffff, codepoint_is_not_surrogate, codepoint_not_negative.
    crush_comparisons; try discriminate; lia.
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
  crush_comparisons; try discriminate; try lia; rewrite <- some_injective in encode_code; subst.
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
  + add_bounds (code mod 64). add_bounds (code / 64 mod 64). apply ThreeByte2; try lia.
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
  crush_comparisons; try discriminate; try lia; rewrite <- some_injective in enc_code1; rewrite <- some_injective in enc_code2; subst; unfold bytes_compare, list_compare.
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

Ltac lia_simplify_hyp H :=
  repeat match type of H with
    | context[match (if ?cond then ?a else ?b) with | _ => _ end] =>
        (replace cond with false in H by lia)
            || (replace cond with true in H by lia)
            || let C := fresh "cond" in destruct cond eqn:C
    end.

Ltac lia_simplify :=
  repeat match goal with
    | |- context[match (if ?cond then ?a else ?b) with | _ => _ end] =>
        ((replace cond with false by lia) || (replace cond with true by lia) || (destruct cond))
    end.

Lemma utf8_dfa_projects : decoder_projects utf8_dfa_decode.
Proof.
  intros xs ys valid_xs.
  unfold utf8_dfa_decode.
  destruct valid_xs; simpl; unfold next_state, byte_range_dec; lia_simplify; 
    destruct (utf8_dfa_decode_rec ys 0 Initial []); reflexivity.
Qed.


Lemma utf8_dfa_decode_invalid: forall bytes suffix,
    utf8_dfa_decode bytes = ([], suffix) ->
    bytes = suffix.
Proof.
  intros bytes suffix decode_bytes.
  unfold utf8_dfa_decode in decode_bytes.
  destruct bytes as [| byte1 bytes].
  - simpl in decode_bytes. inversion decode_bytes. reflexivity.
  - repeat lazymatch goal with
           | [NextState: context[next_state ?state ?carry ?byte] |- _] =>
               unfold next_state in NextState;
               let range := fresh "range" in
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
               destruct bytes as [| byte rest]; simpl in Decode; [inversion Decode; reflexivity|]
           end.
Qed.

Lemma utf8_dfa_decode_prefix: forall bytes code codes suffix,
    utf8_dfa_decode bytes = (code :: codes, suffix) ->
    exists prefix rest,
      valid_codepoint code /\
        valid_codepoint_representation prefix /\ 
        utf8_dfa_decode prefix = ([code], []) /\
        utf8_dfa_decode rest = (codes, suffix) /\
        bytes = prefix ++ rest.
Proof.
  intros bytes code codes suffix decode_bytes.
  destruct bytes as [| byte1 bytes1] eqn:bytes_eq; [ inversion decode_bytes|].
  unfold utf8_dfa_decode in decode_bytes. simpl in decode_bytes.
  unfold next_state, byte_range_dec in decode_bytes.
  lia_simplify_hyp decode_bytes; try (inversion decode_bytes);
  let rec destruct_bytes :=
      match goal with
      | G: context[utf8_dfa_decode_rec ?bytes 0 Initial []] |- _ =>
          let codes := fresh "codes" in
          let suffix := fresh "suffix" in
          let dec := fresh "decode_bytes" in
          destruct (utf8_dfa_decode_rec bytes 0 Initial []) as [codes suffix] eqn:dec;
          inversion G; subst
      | G: context[utf8_dfa_decode_rec ?bytes ?acc ?state ?consumed] |- _ =>
          let b := fresh "byte" in
          let bs := fresh "bytes" in
          let b_eq := fresh "bytes_eq" in
          destruct bytes as [| b bs] eqn:b_eq; [ inversion G|];
          simpl in G; unfold next_state, byte_range_dec in G;
          lia_simplify_hyp G; solve [inversion G] || destruct_bytes
  end in
  let rec reconstruct_prefix :=
    match goal with
    | |- exists prefix rest, _ /\ _ /\ _ /\ _ /\ (?byte1 :: ?byte2 :: ?byte3 :: ?byte4 :: ?bytes = _) =>
        exists [byte1; byte2; byte3; byte4]; exists bytes
    | |- exists prefix rest, _ /\ _ /\ _ /\ _ /\ (?byte1 :: ?byte2 :: ?byte3 :: ?bytes = _) =>
        exists [byte1; byte2; byte3]; exists bytes
    | |- exists prefix rest, _ /\ _ /\ _ /\ _ /\ (?byte1 :: ?byte2 :: ?bytes = _) =>
        exists [byte1; byte2]; exists bytes
    | |- exists prefix rest, _ /\ _ /\ _ /\ _ /\ (?byte1 :: ?bytes = _) =>
        exists [byte1]; exists bytes
    end in
  destruct_bytes; reconstruct_prefix.
  all: let rec codepoint_is_valid :=
    unfold extract_3_bits, extract_4_bits, extract_5_bits, extract_7_bits, push_bottom_bits;
    lazymatch goal with
    | |- (valid_codepoint ?codepoint) =>
        unfold valid_codepoint, codepoint_less_than_10ffff, codepoint_is_not_surrogate, codepoint_not_negative in *;
        repeat split; add_bounds codepoint; try lia
    end 
  in
  let rec valid_bytes :=
    match goal with
    | |- valid_codepoint_representation [?byte] => apply OneByte; lia
    | |- valid_codepoint_representation [?byte1; ?byte2] => apply TwoByte; lia
    | |- valid_codepoint_representation [?byte1; ?byte2; ?byte3] =>
        (apply ThreeByte1; lia) || (apply ThreeByte2; lia) || (apply ThreeByte3; lia) || idtac
    | |- valid_codepoint_representation [?byte1; ?byte2; ?byte3; ?byte4] =>
        (apply FourBytes1; lia) || (apply FourBytes2; lia) || (apply FourBytes3; lia) || idtac
    end
  in
  let rec decode_prefix := unfold utf8_dfa_decode; simpl; unfold next_state, byte_range_dec; lia_simplify; reflexivity in
  split; [codepoint_is_valid | split; [ valid_bytes| split; [ decode_prefix | split; [ unfold utf8_dfa_decode; assumption | reflexivity]] ]].
Qed.
  
Lemma utf8_dfa_output : decoder_output_correct utf8_dfa_decode.
Proof.
  intros bytes suffix codes decode_bytes.
  generalize dependent bytes.
  induction codes as [| code codes].
  - split. constructor.
    exists []. repeat split. constructor.
    apply utf8_dfa_decode_invalid in decode_bytes.
    subst. reflexivity.
  - intros bytes decode_bytes.
    apply utf8_dfa_decode_prefix in decode_bytes as G.
    destruct G as [prefix [rest [valid_code [valid_prefix [decode_prefix [decode_rest bytes_eq]]]]]].
    apply IHcodes in decode_rest as G.
    destruct G as [valid_codes [prefix2 [decode_prefix2 [valid_prefix2 G]]]].
    subst. split.
    + apply Forall_cons. all: assumption.
    + exists (prefix ++ prefix2). repeat split.
      * rewrite utf8_dfa_projects. rewrite decode_prefix, decode_prefix2. reflexivity. assumption.
      * constructor. all: assumption.
      * rewrite app_assoc. reflexivity.
Qed.

      
Lemma utf8_dfa_input : decoder_input_correct_iff utf8_dfa_decode.
Proof.
  split.
  - intros bytes_valid.
    destruct bytes_valid; unfold utf8_dfa_decode; simpl; unfold next_state, byte_range_dec; lia_simplify; eexists; reflexivity.
  - intros [code decode_bytes].
    apply utf8_dfa_decode_prefix in decode_bytes as G.
    destruct G as [prefix [rest [code_valid [prefix_valid [decode_prefix [decode_rest bytes_eq]]]]]].
    subst.
    apply utf8_dfa_decode_invalid in decode_rest. subst. rewrite app_nil_r in *.
    assumption.
Qed.

Lemma one_byte_bounds : forall byte code,
    valid_codepoint_representation [byte] ->
    utf8_dfa_decode [byte] = ([code], []) ->
    code = byte /\ 0 <= code <= 0x7f.
Proof.
  intros.
  unfold utf8_dfa_decode in H0. simpl in H0.
  unfold next_state, byte_range_dec in H0. lia_simplify_hyp H0; inversion H0.
  unfold extract_7_bits in *. add_bounds (byte mod 128). lia.
Qed.

Lemma two_byte_bounds : forall byte1 byte2 code,
    valid_codepoint_representation [byte1; byte2] ->
    utf8_dfa_decode [byte1; byte2] = ([code], []) ->
    code = byte1 mod 32 * 64 + byte2 mod 64
    /\ (0x80 <= code <= 0x7ff).
Proof.
  intros.
  unfold utf8_dfa_decode in H0. simpl in H0.
  unfold next_state, byte_range_dec in H0.
  lia_simplify_hyp H0; inversion H0;
    unfold push_bottom_bits, extract_5_bits in *; split; try reflexivity;
    match goal with
    | |- ?a <= ?code <= ?b =>
        add_bounds code; lia
    end.
Qed.

Lemma three_byte_bounds : forall byte1 byte2 byte3 code,
    valid_codepoint_representation [byte1; byte2; byte3] ->
    utf8_dfa_decode [byte1; byte2; byte3] = ([code], []) ->
    code = (byte1 mod 16 * 64 + byte2 mod 64) * 64 + byte3 mod 64 /\
      (0x800 <= code <= 0xffff).
Proof.
  intros.
  unfold utf8_dfa_decode in H0. simpl in H0.
  unfold next_state, byte_range_dec in H0.
  lia_simplify_hyp H0; inversion H0;
    unfold push_bottom_bits, extract_4_bits in *; split; try reflexivity;
    match goal with
    | |- ?a <= ?code <= ?b =>
        add_bounds code; lia
    end.
Qed.

Lemma four_byte_bounds : forall byte1 byte2 byte3 byte4 code,
    valid_codepoint_representation [byte1; byte2; byte3; byte4] ->
    utf8_dfa_decode [byte1; byte2; byte3; byte4] = ([code], []) ->
    code = ((byte1 mod 8 * 64 + byte2 mod 64) * 64 + byte3 mod 64) * 64 + byte4 mod 64 /\
      0x1000 <= code <= 0x10ffff.
Proof.
  intros.
  unfold utf8_dfa_decode in H0. simpl in H0.
  unfold next_state, byte_range_dec in H0.
  lia_simplify_hyp H0; inversion H0;
    unfold push_bottom_bits, extract_3_bits in *; split; try reflexivity;
    match goal with
    | |- ?a <= ?code <= ?b =>
        add_bounds code; lia
    end; reflexivity.
Qed.

Lemma utf8_dfa_increasing : decoder_strictly_increasing utf8_dfa_decode.
Proof.
  intros bytes1 bytes2 code1 code2 decode_bytes1 decode_bytes2.
  apply utf8_dfa_decode_prefix in decode_bytes1 as G1, decode_bytes2 as G2.
  destruct G1 as [prefix1 [rest1 [code_valid1 [prefix_valid1 [decode_prefix1 [decode_rest1 bytes_eq1]]]]]].
  destruct G2 as [prefix2 [rest2 [code_valid2 [prefix_valid2 [decode_prefix2 [decode_rest2 bytes_eq2]]]]]].
  subst.
  apply utf8_dfa_decode_invalid in decode_rest1, decode_rest2. subst. repeat rewrite app_nil_r in *.
  clear decode_bytes1. clear decode_bytes2.
  let rec break bytes bytes_valid decode :=
    let b1 := fresh "bounds" in
    let b2 := fresh "bounds" in
    (destruct bytes;
     [ inversion bytes_valid
     | destruct bytes;
       [apply one_byte_bounds in decode as [b1 b2]|
         destruct bytes;
         [apply two_byte_bounds in decode as [b1 b2]|
           destruct bytes;
           [apply three_byte_bounds in decode as [b1 b2]|
             destruct bytes;
             [apply four_byte_bounds in decode as [b1 b2]| inversion bytes_valid]]]]])
  in (break prefix1 prefix_valid1 decode_prefix1); (break prefix2 prefix_valid2 decode_prefix2); try assumption; simpl;
     unfold valid_codepoint, codepoint_less_than_10ffff, codepoint_is_not_surrogate, codepoint_not_negative in code_valid1, code_valid2;
     destruct code_valid1 as [code1_less [code1_not_surrogate code1_not_neg]], code_valid2 as [code2_less [code2_not_surrogate code2_not_neg]];
     destruct bounds0; destruct bounds2; inversion prefix_valid1; inversion prefix_valid2; subst;
     repeat match goal with
       | |- context[?a ?= ?b] =>
           let comp := fresh "compare" in
           add_bounds a; add_bounds b;
           destruct (Z.compare_spec a b) as [comp | comp | comp]
       end; try reflexivity; lia.
Qed.
  
Theorem utf8_decoder_spec_compliant : utf8_decoder_spec utf8_dfa_decode.
Proof.
  split.
  - apply utf8_dfa_nil.
  - apply utf8_dfa_input.
  - apply utf8_dfa_output.
  - apply utf8_dfa_increasing.
  - apply utf8_dfa_projects.
Qed.

Theorem utf8_spec_compliant: utf8_spec utf8_encode utf8_dfa_decode.
  split.
  - apply utf8_encode_spec_compliant.
  - apply utf8_decoder_spec_compliant.
Qed.
