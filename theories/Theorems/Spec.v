From Coq Require Import Strings.Byte.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import ZArith.BinInt.

Require Import Utf8.Spec.
Require Import Utf8.Theorems.Enumerations.
Require Import Utf8.Theorems.Order.

Theorem valid_utf8_bytes_concat : forall (bytes1 bytes2: byte_str),
    valid_utf8_bytes bytes1 ->
    valid_utf8_bytes bytes2 ->
    valid_utf8_bytes (bytes1 ++ bytes2).
Proof.
  intros bytes1 bytes2 valid_bytes1. induction valid_bytes1; intros valid_bytes2. assumption.
  rewrite <- app_assoc. apply Utf8Concat. apply H. apply IHvalid_bytes1. apply valid_bytes2.
Qed.

Lemma list0_list0_app_list1 {T}: forall (list0 list1: list T),
    list0 = list0 ++ list1 ->
    list1 = nil.
Proof.
  intros.
  rewrite <- (app_nil_r list0) in H at 1.
  apply app_inv_head in H. symmetry.
  assumption.
Qed.

Lemma encode_nil : forall encoder,
  utf8_encoder_spec encoder ->
  encoder [] = ([], []).
Proof.
Admitted.

Lemma prefix_transitive : forall {X} (l0 l1 l2 : list X),
  prefix l0 l1 ->
  prefix l1 l2 ->
  prefix l0 l2.
Proof.
Admitted.

Lemma prefix_antisym : forall {X} (l0 l1 : list X),
  prefix l0 l1 ->
  prefix l1 l0 ->
  l0 = l1.
Proof.
Admitted.

Lemma prefix_app : forall {X} (l p s : list X),
  l = p ++ s ->
  prefix p l.
Proof.
Admitted.

Lemma prefix_reflexive : forall {X} (l : list X),
  prefix l l.
Proof.
Admitted.

Lemma maximal_prefix_unique : forall {X} (P : list X -> Prop) (p0 p1 l : list X),
  maximal_prefix P p0 l ->
  maximal_prefix P p1 l ->
  p0 = p1.
Proof.
Admitted.
(*
Lemma prefix_length : forall {X} (p l : list X),
  prefix p l ->
  (length p <= length l)%nat.
Proof.
Admitted.

Lemma prefix_not_bigger : forall {X} (p l : list X),
  (length p > length l)%nat ->
  ~ (prefix p l).
Proof.
  unfold not.
  intros X p l bound is_prefix.
  apply prefix_length in is_prefix.
  lia.
Qed.
 *)

Lemma encode_error_unique : forall encoder0 encoder1 codes,
  utf8_encoder_spec encoder0 ->
  utf8_encoder_spec encoder1 ->
  snd (encoder0 codes) = snd (encoder1 codes).
Proof.
  intros encoder0 encoder1 codes encoder0_spec encoder1_spec.
  generalize
    (enc_error encoder0 encoder0_spec codes
      (fst (encoder0 codes)) (snd (encoder0 codes))
      ltac:(apply surjective_pairing)); intros error0.
  destruct error0 as [valid_prefix0 [codes_app0 [[is_valid0 maximal0] _]]].
  generalize (prefix_app _ _ _ codes_app0); intros is_codes_prefix0.
  generalize
    (enc_error encoder1 encoder1_spec codes
      (fst (encoder1 codes)) (snd (encoder1 codes))
      ltac:(apply surjective_pairing)); intros error1.
  destruct error1 as [valid_prefix1 [codes_app1 [[is_valid1 maximal1] _]]].
  generalize (prefix_app _ _ _ codes_app1); intros is_codes_prefix1.
  specialize (maximal0 valid_prefix1 is_codes_prefix1 is_valid1).
  specialize (maximal1 valid_prefix0 is_codes_prefix0 is_valid0).
  generalize (prefix_antisym valid_prefix0 valid_prefix1 maximal1 maximal0);
  intros prefixes_equal.
  rewrite codes_app0 in codes_app1 at 1.
  rewrite <- prefixes_equal in codes_app1.
  apply app_inv_head with (l := valid_prefix0).
  apply codes_app1.
Qed.

Lemma encode_valid_codepoints : forall encoder codes,
  utf8_encoder_spec encoder ->
  valid_codepoints codes ->
  snd (encoder codes) = [].
Proof.
  intros encoder codes encoder_spec codes_valid.
  generalize
    (enc_error encoder encoder_spec codes
      (fst (encoder codes)) (snd (encoder codes))
      ltac:(apply surjective_pairing)); intros error.
  destruct error as [valid_prefix [codes_app [[is_valid maximal] _]]].
  generalize (prefix_app _ _ _ codes_app); intros is_codes_prefix.
  specialize (maximal codes (prefix_reflexive codes) codes_valid).
  generalize (prefix_antisym _ _ maximal is_codes_prefix);
  intros codes_prefix_equal.
  rewrite <- codes_prefix_equal in codes_app.
  apply list0_list0_app_list1 with (list0 := codes).
  apply codes_app.
Qed.

Definition encoder_to_option (encoder: encoder_type) code :=
  match encoder [code] with
  | (bytes, []) => Some bytes
  | _ => None
  end.

Lemma encoder_partial_morphism : forall encoder,
    utf8_encoder_spec encoder ->
    partial_morphism valid_codepoint valid_codepoint_representation (encoder_to_option encoder).
Proof.
  (*
  intros encoder encoder_spec.
  unfold encoder_to_option.
  split.
  - intros code bytes' encode_some.
    destruct (encoder [code]) as [bytes rest] eqn:encoder_code.
    destruct rest; [| discriminate].
    specialize (enc_output encoder encoder_spec code) as bytes_valid.
    rewrite encoder_code in bytes_valid.
    inversion encode_some. subst.
    apply bytes_valid.
  - intros code encode_none code_valid.
    destruct (encoder [code]) as [bytes rest] eqn: encoder_code.
    destruct rest; [ discriminate|].
    eapply enc_input in code_valid; [| apply encoder_spec].
    destruct code_valid as [bytes' enc_code].
    rewrite encoder_code in enc_code. inversion enc_code.
   *)
Admitted.

Lemma encoder_to_option_increasing : forall encoder,
    utf8_encoder_spec encoder ->
    increasing valid_codepoint Z.compare bytes_compare (encoder_to_option encoder).
Proof.
  (*
  intros encoder encoder_spec.
  unfold encoder_to_option.
  intros code1 code2 code1_valid code2_valid.
  eapply enc_input in code1_valid; [| apply encoder_spec].
  eapply enc_input in code2_valid; [| apply encoder_spec].
  destruct code1_valid as [bytes1 encoder_code1].
  destruct code2_valid as [bytes2 encoder_code2].
  rewrite encoder_code1. rewrite encoder_code2.
  specialize (enc_increasing encoder encoder_spec [code1] [code2] bytes1 bytes2 encoder_code1 encoder_code2) as increasing.
  simpl in increasing.
  destruct (code1 ?= code2); assumption.
  *)
Admitted.

Theorem utf8_spec_encoder_unique_single : forall encoder0 encoder1 code,
    utf8_encoder_spec encoder0 ->
    utf8_encoder_spec encoder1 ->
    valid_codepoint code ->
    encoder0 [code] = encoder1 [code].
Proof.
  (* TODO *)
  (* This is where the magic happens *)
Admitted.

Lemma utf8_spec_encoder_unique_valid : forall encoder0 encoder1 codes,
    utf8_encoder_spec encoder0 ->
    utf8_encoder_spec encoder1 ->
    valid_codepoints codes ->
    fst (encoder0 codes) = fst (encoder1 codes).
Proof.
Admitted.

Theorem utf8_spec_encoder_unique : forall encoder0 encoder1 codes,
    utf8_encoder_spec encoder0 ->
    utf8_encoder_spec encoder1 ->
    encoder0 codes = encoder1 codes.
Proof.
  intros encoder0 encoder1 codes encoder0_spec encoder1_spec.
  rewrite (surjective_pairing (encoder1 codes)).
  rewrite (surjective_pairing (encoder0 codes)).
  rewrite (encode_error_unique encoder0 encoder1); try assumption.
  assert (fst (encoder0 codes) = fst (encoder1 codes)) as encodings_equal.
  - generalize (fun code =>
      (utf8_spec_encoder_unique_single encoder0 encoder1 code encoder0_spec encoder1_spec)); intros.
    generalize
      (enc_error encoder0 encoder0_spec codes
        (fst (encoder0 codes)) (snd (encoder0 codes))
        ltac:(apply surjective_pairing));
      intros [valid_prefix0 [_ [maximal0 fst_equal0]]].
    generalize
      (enc_error encoder1 encoder1_spec codes
        (fst (encoder1 codes)) (snd (encoder1 codes))
        ltac:(apply surjective_pairing));
      intros [valid_prefix1 [_ [maximal1 fst_equal1]]].
    assert (valid_prefix0 = valid_prefix1)
    by (
      apply maximal_prefix_unique with (P := valid_codepoints) (l := codes); assumption
    ); subst valid_prefix1.
    rewrite <- fst_equal0.
    rewrite <- fst_equal1.
    clear - maximal0 encoder0_spec encoder1_spec.
    destruct maximal0 as [valid _].
    apply utf8_spec_encoder_unique_valid; assumption.
  - rewrite encodings_equal. reflexivity.
Qed.

Theorem decoder_decode_valid_bytes : forall decoder,
    utf8_decoder_spec decoder ->
    forall bytes,
      valid_utf8_bytes bytes ->
      exists codes, decoder bytes = (codes, []) /\ valid_codepoints codes.
Proof.
  (*
  intros decoder decoder_spec.
  intros bytes bytes_valid. induction bytes_valid.
  + exists []. split. apply dec_nil. assumption. constructor.
  + rewrite dec_projects; [| assumption].
    apply (decoder_spec.(dec_input decoder)) in H.
    destruct H as [code decode_bytes].
    apply dec_output in decode_bytes as G; [| assumption].
    destruct G as [code_valid [bytes_prefix bytes_eq]].
    inversion code_valid.
    destruct IHbytes_valid as [codes [decode_tail codes_valid]].
    rewrite decode_bytes.
    rewrite decode_tail.
    exists ([code] ++ codes). split.
    reflexivity.
    apply Forall_cons; try assumption.
   *)
Admitted.

Definition decoder_to_option (decoder: decoder_type) bytes :=
  match decoder bytes with
  | ([code], []) => Some code
  | _ => None
  end.

Lemma decoder_partial_morphism : forall decoder,
    utf8_decoder_spec decoder ->
    partial_morphism valid_codepoint_representation valid_codepoint (decoder_to_option decoder).
Proof.
  (*
  intros decoder decoder_spec.
  unfold decoder_to_option.
  assert (G := decoder_spec). destruct G.
  split.
  - intros bytes code bytes_some.
    destruct (decoder bytes) as [codes rest] eqn:decode_bytes.
    destruct codes as [| code2 tail]; [discriminate |].
    destruct tail; [|discriminate].
    destruct rest; [|discriminate].
    inversion bytes_some. subst.
    assert (exists code, decoder bytes = ([code], [])). exists code. assumption.
    apply dec_input in H as bytes_valid.
    specialize (dec_output bytes [code] [] decode_bytes).
    destruct dec_output as [valid_code _].
    inversion valid_code.
    assumption.
  - intros bytes bytes_none bytes_valid.
    destruct (decoder bytes) as [codes rest] eqn:decoder_bytes.
    apply dec_input in bytes_valid.
    destruct bytes_valid as [code decode_bytes].
    rewrite decode_bytes in decoder_bytes.
    destruct codes as [| code' tail].
    + specialize (dec_nil) as enc_nil. unfold decoder_nil in enc_nil.
      inversion decoder_bytes.
    + destruct tail. destruct rest; [discriminate|].
      all: inversion decoder_bytes.
   *)
Admitted.

Lemma decoder_to_option_increasing: forall decoder,
    utf8_decoder_spec decoder ->
    increasing valid_codepoint_representation bytes_compare Z.compare (decoder_to_option decoder).
Proof.
  (*
  intros decoder decoder_spec.
  unfold decoder_to_option.
  intros bytes1 bytes2 bytes1_valid bytes2_valid.
  eapply dec_input in bytes1_valid; [| apply decoder_spec].
  eapply dec_input in bytes2_valid; [| apply decoder_spec].
  destruct bytes1_valid as [code1 decoder_bytes1].
  destruct bytes2_valid as [code2 decoder_bytes2].
  rewrite decoder_bytes1, decoder_bytes2.
  specialize (dec_increasing decoder decoder_spec bytes1 bytes2 [code1] [code2] decoder_bytes1 decoder_bytes2) as increasing.
  simpl in increasing. symmetry in increasing.
  destruct (code1 ?= code2); assumption.
   *)
Admitted.

Lemma utf8_spec_implies_encoder_maps_nth_to_nth : forall encoder decoder,
    utf8_encoder_spec encoder ->
    utf8_decoder_spec decoder ->
    forall code bytes,
      encoder [code] = (bytes, []) -> 
      exists n, nth_valid_codepoint n = Some code /\ nth_valid_codepoint_representation n = Some bytes.
Proof.
  (*
  intros encoder decoder encoder_spec decoder_spec code bytes encoder_code.
  specialize (finite_partial_isomorphism_unique (0x10ffff - 0x7ff) valid_codepoint valid_codepoint_representation Z.compare bytes_compare) as iso.
  specialize (iso inverse_nth_valid_codepoint inverse_nth_valid_codepoint_representation (decoder_to_option decoder)).
  specialize (iso nth_valid_codepoint         nth_valid_codepoint_representation         (encoder_to_option encoder)).
  specialize (iso codepoint_nth_isomorphism valid_codepoint_representation_isomorphism).
  specialize (iso (encoder_partial_morphism encoder encoder_spec)).
  specialize (iso (decoder_partial_morphism decoder decoder_spec)).
  specialize (iso (encoder_to_option_increasing encoder encoder_spec)).
  specialize (iso (decoder_to_option_increasing decoder decoder_spec)).
  destruct iso as [going back].
  unfold pointwise_equal in going.
  assert (exists bytes, encoder [code] = (bytes, [])) as enc_bytes. exists bytes. assumption.
  specialize (enc_input encoder encoder_spec code) as [G1 G2].
  apply G2 in enc_bytes as code_valid.
  specialize (going code code_valid).
  unfold encoder_to_option in going.
  rewrite encoder_code in going.
  unfold and_then in going.
  destruct (inverse_nth_valid_codepoint code) as [n|] eqn:inverse_nth_valid_codepoint; [|discriminate].
  exists n. split.
  - apply nth_valid_codepoint_invertible. split; assumption.
  - symmetry in going. apply going.
   *)
Admitted.

Lemma utf8_spec_implies_decoder_maps_nth_to_nth : forall encoder decoder,
    utf8_encoder_spec encoder ->
    utf8_decoder_spec decoder ->
    forall code bytes,
      decoder bytes = ([code], []) -> 
      exists n, nth_valid_codepoint n = Some code /\ nth_valid_codepoint_representation n = Some bytes.
Proof.
  (*
  intros encoder decoder encoder_spec decoder_spec code bytes decode_bytes.
  specialize (finite_partial_isomorphism_unique (0x10ffff - 0x7ff) valid_codepoint valid_codepoint_representation Z.compare bytes_compare) as iso.
  specialize (iso inverse_nth_valid_codepoint inverse_nth_valid_codepoint_representation (decoder_to_option decoder)).
  specialize (iso nth_valid_codepoint         nth_valid_codepoint_representation         (encoder_to_option encoder)).
  specialize (iso codepoint_nth_isomorphism valid_codepoint_representation_isomorphism).
  specialize (iso (encoder_partial_morphism encoder encoder_spec)).
  specialize (iso (decoder_partial_morphism decoder decoder_spec)).
  specialize (iso (encoder_to_option_increasing encoder encoder_spec)).
  specialize (iso (decoder_to_option_increasing decoder decoder_spec)).
  destruct iso as [going back].
  unfold pointwise_equal in back.
  (*assert (exists code, decoder bytes = ([code], [])) as dec_code. exists code. assumption.*)
  specialize (dec_output decoder decoder_spec bytes [code] [] decode_bytes) as bytes_are_valid.
  unfold valid_codepoints in bytes_are_valid.
  inversion bytes_are_valid; subst. clear H2.
  destruct bytes_are_valid as [actually_bytes [substitution [bytes_valid _]] ].
  rewrite (app_nil_r actually_bytes) in substitution.
  subst actually_bytes.
  specialize (back bytes bytes_valid).
  unfold decoder_to_option in back.
  rewrite decode_bytes in back.
  unfold and_then in back.
  destruct (inverse_nth_valid_codepoint_representation bytes) as [n|] eqn: inverse_nth_valid_codepoint_representation; [|discriminate].
  exists n. split.
  - symmetry. assumption.
  - apply inverse_nth_valid_codepoint_representation_invertible; assumption.
   *)
Admitted.

Theorem utf8_spec_encoder_decoder_inverse_single: forall encoder decoder,
    utf8_encoder_spec encoder ->
    utf8_decoder_spec decoder ->
    forall code bytes,
      encoder [code] = (bytes, []) ->
      decoder bytes = ([code], []).
Proof.
  (*
  intros encoder decoder encoder_spec decoder_spec.
  intros code bytes encode_code.
  eapply utf8_spec_implies_encoder_maps_nth_to_nth in encode_code as G; [ | assumption | apply decoder_spec].
  destruct G as [n [nth_code nth_byte]].
  assert (exists bytes, encoder [code] = (bytes, [])) as code_valid. exists bytes. assumption.
  apply enc_input in code_valid; [|assumption].
  specialize (enc_output encoder encoder_spec code) as bytes_valid.
  rewrite encode_code in bytes_valid.
  eapply dec_input in bytes_valid; [| apply decoder_spec].
  destruct bytes_valid as [code2 decode_code2].
  eapply utf8_spec_implies_decoder_maps_nth_to_nth in decode_code2 as G; [ | apply encoder_spec | apply decoder_spec].
  destruct G as [n2 [nth_code2 nth_byte2]].
  apply nth_valid_codepoint_representation_invertible in nth_byte, nth_byte2.
  rewrite nth_byte in nth_byte2. apply some_injective in nth_byte2.
  subst. rewrite nth_code in nth_code2. apply some_injective in nth_code2. subst.
  assumption.
   *)
Admitted.

Theorem utf8_spec_decoder_encoder_inverse_single: forall encoder decoder,
    utf8_encoder_spec encoder ->
    utf8_decoder_spec decoder ->
    forall code bytes,
      decoder bytes = ([code], []) ->
      encoder [code] = (bytes, []).
Proof.
  (*
  intros encoder decoder encoder_spec decoder_spec.
  intros code bytes decode_bytes.
  eapply utf8_spec_implies_decoder_maps_nth_to_nth in decode_bytes as G; [ | apply encoder_spec | assumption].
  destruct G as [n [nth_code nth_byte]].
  apply dec_output in decode_bytes as [valid_code _]; [|assumption].
  eapply encoder_encode_valid_codepoints in valid_code; [| apply encoder_spec].
  destruct valid_code as [bytes2 [encoder_code _]].
  eapply utf8_spec_implies_encoder_maps_nth_to_nth in encoder_code as G; [ | apply encoder_spec | apply decoder_spec].
  destruct G as [n2 [nth2_code nth2_byte]].
  apply nth_valid_codepoint_invertible in nth_code as [inverse_n _], nth2_code as [inverse_n2 _].
  rewrite inverse_n in inverse_n2. apply some_injective in inverse_n2.
  subst. rewrite nth2_byte in nth_byte. apply some_injective in nth_byte.
  subst. assumption.
   *)
Admitted.

Theorem utf8_spec_encoder_decoder_inverse : forall encoder decoder codes,
    utf8_encoder_spec encoder ->
    utf8_decoder_spec decoder ->
    (fst (decoder (fst (encoder codes))) ++ (snd (encoder codes)) = codes)
    /\ (snd (decoder (fst (encoder codes))) = []).
Proof.
  (*
  intros encoder decoder encoder_spec decoder_spec.
  induction codes as [| code tail]; intros bytes codes_suffix encode_codes.
  - exists []. pose proof (enc_nil encoder encoder_spec). rewrite H in encode_codes. inversion encode_codes.
    split. apply dec_nil. assumption. reflexivity.
  - replace (code :: tail) with ([code] ++ tail) in encode_codes by reflexivity.
    rewrite enc_projects in encode_codes; [| assumption].
    destruct (encoder [code]) as [bytes2 rest] eqn:encoder_code.
    destruct rest.
    2: {
      inversion encode_codes. subst.
      specialize (enc_output encoder encoder_spec code) as bytes_invalid.
      rewrite encoder_code in bytes_invalid. destruct bytes_invalid as [bytes_eq rest_eq].
      inversion rest_eq. subst.
      exists nil. split. apply dec_nil. assumption. reflexivity.
    }
    destruct (encoder tail) as [bytes3 rest] eqn:encoder_tail.
    specialize (IHtail bytes3 rest ltac:(reflexivity)).
    destruct IHtail as [codes_tail [decode_bytes3 tail_eq]].
    inversion encode_codes.
    rewrite dec_projects; [|assumption].
    eapply utf8_spec_encoder_decoder_inverse_single in encoder_code; [ | assumption | apply decoder_spec].
    rewrite encoder_code.
    rewrite decode_bytes3.
    exists ([code] ++ codes_tail). split. reflexivity. inversion tail_eq. subst. reflexivity.
  *)
Admitted.
