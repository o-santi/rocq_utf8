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

Lemma list_equals_self_append_implies_nil {T}: forall (list1 list2: list T),
    list1 = list1 ++ list2 ->
    list2 = nil.
Proof.
  intros.
  destruct list1.
  - symmetry in H. apply List.app_eq_nil in H. destruct H. assumption. 
  - apply (f_equal (@length T)) in H.
    rewrite List.length_app in H. simpl in H. rewrite <- plus_Sn_m in H.
    destruct list2. reflexivity. simpl in H. lia.
Qed.

Theorem decoder_decode_valid_bytes : forall decoder,
    utf8_decoder_spec decoder ->
    forall bytes,
      valid_utf8_bytes bytes ->
      exists codes, decoder bytes = (codes, []) /\ valid_codepoints codes.
Proof.
  intros decoder decoder_spec.
  intros bytes bytes_valid. induction bytes_valid.
  + exists []. split. apply dec_nil. assumption. constructor.
  + rewrite (dec_projects decoder decoder_spec bytes tail H).
    apply (decoder_spec.(dec_input decoder)) in H.
    destruct H as [code decode_bytes].
    apply dec_output in decode_bytes as G; [| assumption].
    destruct G as [code_valid [prefix [decode_prefix [prefix_valid bytes_eq]]]].
    inversion code_valid.
    destruct IHbytes_valid as [codes [decode_tail codes_valid]].
    rewrite decode_bytes.
    rewrite decode_tail.
    exists ([code] ++ codes). split.
    reflexivity.
    apply Forall_cons; try assumption.
Qed.

Theorem encoder_encode_valid_codepoints : forall encoder,
    utf8_encoder_spec encoder ->
    forall codes,
      valid_codepoints codes ->
      exists bytes, encoder codes = (bytes, []) /\ valid_utf8_bytes bytes.
Proof.
  intros encoder encoder_spec.
  intros codes codes_valid. induction codes_valid as [| code tail].
  - exists []. split. apply enc_nil. assumption. constructor.
  - replace (code :: tail) with ([code] ++ tail) by reflexivity.
    rewrite enc_projects; [| assumption].
    apply (encoder_spec.(enc_input encoder)) in H.
    destruct H as [bytes encode_code].
    specialize (enc_output encoder encoder_spec code) as bytes_valid.
    rewrite encode_code in bytes_valid.
    destruct IHcodes_valid as [bytes_tail [encode_tail bytes_tail_valid]].
    rewrite encode_code.
    rewrite encode_tail.
    exists (bytes ++ bytes_tail). split.
    reflexivity.
    apply Utf8Concat; try assumption.
Qed.

Definition encoder_to_option (encoder: encoder_type) code :=
  match encoder [code] with
  | (bytes, []) => Some bytes
  | _ => None
  end.

Definition decoder_to_option (decoder: decoder_type) bytes :=
  match decoder bytes with
  | ([code], []) => Some code
  | _ => None
  end.

Lemma encoder_partial_morphism : forall encoder,
    utf8_encoder_spec encoder -> 
    partial_morphism valid_codepoint valid_codepoint_representation (encoder_to_option encoder).
Proof.
  intros encoder encoder_spec.
  unfold encoder_to_option.
  split.
  - intros code bytes' encode_some encoder_eq.
    destruct (encoder [code]) as [bytes rest] eqn:encoder_code.
    destruct rest; [| discriminate]. 
    specialize (enc_output encoder encoder_spec code) as bytes_valid.
    rewrite encoder_code in bytes_valid.
    inversion encoder_eq. subst. assumption.
  - intros code encode_none code_valid.
    destruct (encoder [code]) as [bytes rest] eqn: encoder_code.
    destruct rest; [ discriminate|].
    eapply enc_input in code_valid; [| apply encoder_spec].
    destruct code_valid as [bytes' enc_code].
    rewrite encoder_code in enc_code. inversion enc_code.
Qed.

   
Lemma decoder_partial_morphism : forall decoder,
    utf8_decoder_spec decoder ->
    partial_morphism valid_codepoint_representation valid_codepoint (decoder_to_option decoder).
Proof.
  intros decoder decoder_spec.
  unfold decoder_to_option.
  assert (G := decoder_spec). destruct G.
  split.
  - intros bytes code bytes_valid bytes_some.
    destruct (decoder bytes) as [codes rest] eqn:decode_bytes.
    destruct codes as [| code2 tail]; [discriminate |].
    destruct tail; [|discriminate].
    destruct rest; [|discriminate].
    inversion bytes_some. subst.
    assert (exists code, decoder bytes = ([code], [])) as exists_code. exists code. assumption.
    specialize (dec_output bytes [] [code] decode_bytes).
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
Qed.

Lemma encoder_to_option_increasing : forall encoder,
    utf8_encoder_spec encoder ->
    increasing valid_codepoint Z.compare bytes_compare (encoder_to_option encoder).
Proof.
  intros encoder encoder_spec.
  unfold encoder_to_option.
  intros code1 code2 code1_valid code2_valid.
  eapply enc_input in code1_valid; [| apply encoder_spec].
  eapply enc_input in code2_valid; [| apply encoder_spec].
  destruct code1_valid as [bytes1 encoder_code1].
  destruct code2_valid as [bytes2 encoder_code2].
  rewrite encoder_code1. rewrite encoder_code2.
  specialize (enc_increasing encoder encoder_spec code1 code2 bytes1 bytes2 encoder_code1 encoder_code2) as increasing.
  simpl in increasing.
  destruct (code1 ?= code2); assumption.
Qed.

Lemma decoder_to_option_increasing: forall decoder,
    utf8_decoder_spec decoder ->
    increasing valid_codepoint_representation bytes_compare Z.compare (decoder_to_option decoder).
Proof.
  intros decoder decoder_spec.
  unfold decoder_to_option.
  intros bytes1 bytes2 bytes1_valid bytes2_valid.
  eapply dec_input in bytes1_valid; [| apply decoder_spec].
  eapply dec_input in bytes2_valid; [| apply decoder_spec].
  destruct bytes1_valid as [code1 decoder_bytes1].
  destruct bytes2_valid as [code2 decoder_bytes2].
  rewrite decoder_bytes1, decoder_bytes2.
  specialize (dec_increasing decoder decoder_spec bytes1 bytes2 code1 code2 decoder_bytes1 decoder_bytes2) as increasing.
  simpl in increasing. symmetry in increasing.
  destruct (code1 ?= code2); assumption.
Qed.

Lemma utf8_spec_implies_encoder_maps_nth_to_nth : forall encoder decoder,
    utf8_encoder_spec encoder ->
    utf8_decoder_spec decoder ->
    forall code bytes,
      encoder [code] = (bytes, []) -> 
      exists n, nth_valid_codepoint n = Some code /\ nth_valid_codepoint_representation n = Some bytes.
Proof.
  intros encoder decoder encoder_spec decoder_spec code bytes encoder_code.
  specialize (finite_partial_isomorphism_unique (0x10ffff - 0x7ff) valid_codepoint valid_codepoint_representation Z.compare bytes_compare) as iso.
  specialize (iso inverse_nth_valid_codepoint inverse_nth_valid_codepoint_representation (decoder_to_option decoder)).
  specialize (iso nth_valid_codepoint         nth_valid_codepoint_representation         (encoder_to_option encoder)).
  specialize (iso ltac:(lia) codepoint_nth_isomorphism valid_codepoint_representation_isomorphism).
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
Qed.

Lemma utf8_spec_implies_decoder_maps_nth_to_nth : forall encoder decoder,
    utf8_encoder_spec encoder ->
    utf8_decoder_spec decoder ->
    forall code bytes,
      decoder bytes = ([code], []) -> 
      exists n, nth_valid_codepoint n = Some code /\ nth_valid_codepoint_representation n = Some bytes.
Proof.
  intros encoder decoder encoder_spec decoder_spec code bytes decode_bytes.
  specialize (finite_partial_isomorphism_unique (0x10ffff - 0x7ff) valid_codepoint valid_codepoint_representation Z.compare bytes_compare) as iso.
  specialize (iso inverse_nth_valid_codepoint inverse_nth_valid_codepoint_representation (decoder_to_option decoder)).
  specialize (iso nth_valid_codepoint         nth_valid_codepoint_representation         (encoder_to_option encoder)).
  specialize (iso ltac:(lia) codepoint_nth_isomorphism valid_codepoint_representation_isomorphism).
  specialize (iso (encoder_partial_morphism encoder encoder_spec)).
  specialize (iso (decoder_partial_morphism decoder decoder_spec)).
  specialize (iso (encoder_to_option_increasing encoder encoder_spec)).
  specialize (iso (decoder_to_option_increasing decoder decoder_spec)).
  destruct iso as [going back].
  unfold pointwise_equal in back.
  assert (exists code, decoder bytes = ([code], [])) as dec_code. exists code. assumption.
  specialize (dec_input decoder decoder_spec bytes) as [G1 G2].
  apply G2 in dec_code as bytes_valid.
  specialize (back bytes bytes_valid).
  unfold decoder_to_option in back.
  rewrite decode_bytes in back.
  unfold and_then in back.
  destruct (inverse_nth_valid_codepoint_representation bytes) as [n|] eqn: inverse_nth_valid_codepoint_representation; [|discriminate].
  exists n. split.
  - symmetry. assumption.
  - apply inverse_nth_valid_codepoint_representation_invertible; assumption.
Qed.

Theorem utf8_spec_encoder_decoder_inverse_single: forall encoder decoder,
    utf8_encoder_spec encoder ->
    utf8_decoder_spec decoder ->
    forall code bytes,
      encoder [code] = (bytes, []) ->
      decoder bytes = ([code], []).
Proof.
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
Qed.

Theorem utf8_spec_decoder_encoder_inverse_single: forall encoder decoder,
    utf8_encoder_spec encoder ->
    utf8_decoder_spec decoder ->
    forall code bytes,
      decoder bytes = ([code], []) ->
      encoder [code] = (bytes, []).
Proof.
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
Qed.

Theorem utf8_spec_encoder_decoder_inverse : forall encoder decoder,
    utf8_encoder_spec encoder ->
    utf8_decoder_spec decoder ->
    forall codes bytes codes_suffix,
      encoder codes = (bytes, codes_suffix) ->
      exists codes_prefix, decoder bytes = (codes_prefix, nil) /\ codes = (codes_prefix ++ codes_suffix)%list.
Proof.
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
    eapply utf8_spec_encoder_decoder_inverse_single in encoder_code; [ | assumption | apply decoder_spec].
    rewrite dec_projects.
    + rewrite encoder_code.
      rewrite decode_bytes3.
      exists ([code] ++ codes_tail). split. reflexivity. inversion tail_eq. subst. reflexivity.
    + apply decoder_spec.
    + apply (decoder_spec.(dec_input decoder)).
      exists code. assumption.
Qed.

Lemma list_app_right_is_nil {A} : forall (a b: list A),
    a ++ b = a -> b = [].
Proof.
  induction a; intros b concat.
  - assumption.
  - inversion concat. apply IHa in H0. assumption.
Qed.

Lemma utf8_spec_decoder_correct: forall decoder,
    utf8_decoder_spec decoder ->
    forall bytes bytes_suffix codes,
      decoder bytes = (codes, bytes_suffix) ->
      exists bytes_prefix,
        decoder bytes_prefix = (codes, [])
        /\ valid_utf8_bytes bytes_prefix /\ bytes = bytes_prefix ++ bytes_suffix.
Proof.
  intros decoder decoder_spec bytes suffix codes decoder_bytes.
  apply dec_output in decoder_bytes as G; [|assumption].
  destruct G as [codes_valid [prefix [decode_prefix [prefix_valid bytes_eq]]]].
  exists prefix. auto.
Qed.

Theorem utf8_spec_decoder_project_dual : forall encoder decoder,
    utf8_encoder_spec encoder ->
    utf8_decoder_spec decoder ->
    forall xs ys bytes bytes_suffix,
      decoder bytes = (xs ++ ys, bytes_suffix) ->
      (exists bytes1 bytes2,
          decoder bytes1 = (xs, []) /\ 
            decoder bytes2 = (ys, []) /\
            bytes = bytes1 ++ bytes2 ++ bytes_suffix).
Proof.
  intros encoder decoder encoder_spec decoder_spec.
  intros xs ys bytes bytes_suffix decoder_bytes.
  apply utf8_spec_decoder_correct in decoder_bytes; [| assumption].
  destruct decoder_bytes as [bytes_prefix [decoder_bytes_prefix [bytes_prefix_valid bytes_eq]]].
  generalize dependent ys.
  generalize dependent xs.
  subst.
  induction bytes_prefix_valid as [| bytes tail bytes_valid]; intros xs ys decoder_bytes.
  - subst. rewrite dec_nil in decoder_bytes; [| assumption]. inversion decoder_bytes.
    symmetry in H0. apply app_eq_nil in H0. destruct H0. subst.
    exists []. exists []. repeat split. all: apply dec_nil; assumption.
  - rewrite dec_projects in decoder_bytes; [| assumption | assumption].
    eapply dec_input in bytes_valid as G; [| apply decoder_spec].
    destruct G as [code decoder_bytes_code].
    rewrite decoder_bytes_code in decoder_bytes.
    destruct (decoder tail) as [codes2 rest] eqn:decoder_tail.
    apply pair_equal_spec in decoder_bytes. destruct decoder_bytes as [codes_eq rest_eq]. subst.
    apply app_eq_app in codes_eq.
    destruct codes_eq as [suffix [[code_eq ys_eq] | [xs_eq codes2_eq]]].
    + destruct suffix.
      * rewrite app_nil_r in code_eq. rewrite app_nil_l in ys_eq.
        specialize (IHbytes_prefix_valid [] ys ltac:(rewrite ys_eq; reflexivity)).
        destruct IHbytes_prefix_valid as [bytes1 [bytes2 [decoder_bytes1 [decoder_bytes2 tail_eq]]]].
        exists bytes. exists tail. repeat split; subst. assumption. assumption.
        rewrite app_assoc. reflexivity.
      * destruct xs.
        2: { apply (f_equal (fun l => length l)) in code_eq. rewrite length_app in code_eq. simpl in code_eq. lia. }
        inversion code_eq. subst. clear code_eq.
        exists nil. exists (bytes ++ tail). repeat split. apply dec_nil; assumption.
        rewrite dec_projects; [| assumption| assumption]. rewrite decoder_bytes_code.
        rewrite decoder_tail. reflexivity.
    + destruct suffix.
      * rewrite app_nil_r in xs_eq. rewrite app_nil_l in codes2_eq.
        specialize (IHbytes_prefix_valid [] ys ltac:(rewrite codes2_eq; reflexivity)).
        destruct IHbytes_prefix_valid as [bytes1 [bytes2 [decoder_bytes1 [decoder_bytes2 tail_eq]]]]. subst. 
        exists bytes. exists tail. repeat split; try assumption. rewrite app_assoc. reflexivity.
      * specialize (IHbytes_prefix_valid (c :: suffix) ys ltac:(rewrite codes2_eq; reflexivity)).
        destruct IHbytes_prefix_valid as [bytes1 [bytes2 [decoder_bytes1 [decoder_bytes2 tail_eq]]]].
        exists (bytes ++ bytes1). exists bytes2. repeat split.
        -- rewrite dec_projects; [| assumption| assumption].
           rewrite decoder_bytes_code. rewrite decoder_bytes1. subst. reflexivity.
        -- assumption.
        -- repeat rewrite <- app_assoc.
           replace (tail ++ bytes_suffix) with (bytes1 ++ bytes2 ++ bytes_suffix).
           repeat rewrite app_assoc. reflexivity.
Qed.

Lemma utf8_spec_decoder_nil_unique : forall decoder,
    utf8_decoder_spec decoder ->
    forall bytes,
      decoder bytes = ([], []) ->
      bytes = [].
Proof.
  intros decoder decoder_spec bytes decoder_bytes.
  destruct decoder_spec.
  apply dec_output in decoder_bytes as G.
  destruct G as [codes_valid [prefix [decoder_prefix [prefix_valid bytes_eq]]]].
  rewrite app_nil_r in bytes_eq.
  subst.
  destruct prefix_valid.
  - reflexivity.
  - rewrite dec_projects in decoder_bytes; [|assumption].
    apply dec_input in H as [code decode_bytes].
    rewrite decode_bytes in decoder_bytes.
    destruct (decoder tail) as [codes2 rest2] eqn:decode_tail.
    inversion decoder_bytes.
Qed.

Theorem utf8_spec_decoder_encoder_inverse_strong : forall encoder decoder,
    utf8_encoder_spec encoder ->
    utf8_decoder_spec decoder ->
    forall (codes_big codes: unicode_str) bytes bytes_suffix,
      ((length codes) <= (length codes_big))%nat ->
      decoder bytes = (codes, bytes_suffix) ->
      exists bytes_prefix, encoder codes = (bytes_prefix, nil) /\ bytes = (bytes_prefix ++ bytes_suffix)%list.
Proof.
  intros encoder decoder encoder_spec decoder_spec.
  induction codes as [| code codes]; intros bytes bytes_suffix length decoder_bytes.
  - exists []. split. apply enc_nil. assumption.
    apply dec_output in decoder_bytes as G; [|assumption].
    destruct G as [_ [prefix [decode_prefix [prefix_valid bytes_eq]]]].
    apply utf8_spec_decoder_nil_unique in decode_prefix; [|assumption].
    subst. reflexivity.
  - replace (code :: codes) with ([code] ++ codes) in decoder_bytes |- * by reflexivity.
    eapply utf8_spec_decoder_project_dual in decoder_bytes; [| apply encoder_spec | assumption ].
    destruct decoder_bytes as [bytes1 [bytes2 [decoder_bytes1 [decoder_bytes2 bytes_eq]]]].
    eapply utf8_spec_decoder_encoder_inverse_single in decoder_bytes1; [| apply encoder_spec | assumption].
    apply IHcodes in decoder_bytes2; [|  simpl in length; lia].
    destruct decoder_bytes2 as [bytes_prefix [encoder_codes bytes2_eq]].
    rewrite enc_projects; [| assumption].
    rewrite decoder_bytes1. rewrite encoder_codes.
    exists (bytes1 ++ bytes_prefix).
    split. reflexivity. inversion bytes2_eq. inversion bytes_eq. subst.
    rewrite app_assoc. rewrite app_nil_r. reflexivity.
Qed.

Theorem utf8_spec_decoder_encoder_inverse: forall encoder decoder,
    utf8_encoder_spec encoder ->
    utf8_decoder_spec decoder ->
    forall codes bytes bytes_suffix,
      decoder bytes = (codes, bytes_suffix) ->
      exists bytes_prefix, encoder codes = (bytes_prefix, nil) /\ bytes = (bytes_prefix ++ bytes_suffix)%list.
Proof.
  intros encoder decoder encoder_spec decoder_spec codes bytes bytes_suffix.
  apply utf8_spec_decoder_encoder_inverse_strong with (codes_big := codes); [assumption | assumption | lia].
Qed.

Theorem utf8_spec_encoder_unique_single : forall encoder1 decoder code bytes,
    utf8_encoder_spec encoder1 ->
    utf8_decoder_spec decoder ->
    encoder1 [code] = (bytes, nil) ->
    forall encoder2,
      utf8_encoder_spec encoder2 ->
      encoder2 [code] = (bytes, nil).
Proof.
  intros encoder1 decoder code bytes encoder1_spec decoder_spec encoder1_code encoder2 encoder2_spec.
  assert (exists bytes, encoder1 [code] = (bytes, [])) as valid_code. exists bytes. assumption.
  eapply enc_input in valid_code; [| assumption].
  eapply enc_input in valid_code; [| apply encoder2_spec].
  destruct valid_code as [bytes2 encoder2_code].
  eapply utf8_spec_implies_encoder_maps_nth_to_nth in encoder1_code as G1; [| assumption | apply decoder_spec].
  eapply utf8_spec_implies_encoder_maps_nth_to_nth in encoder2_code as G2; [| assumption | apply decoder_spec].
  destruct G1 as [n1 [nth1_code nth1_bytes]].
  destruct G2 as [n2 [nth2_code nth2_bytes]].
  apply nth_valid_codepoint_invertible in nth1_code, nth2_code.
  destruct nth1_code as [inverse_n1 _], nth2_code as [inverse_n2 _].
  rewrite inverse_n1 in inverse_n2. inversion inverse_n2. subst. rewrite nth1_bytes in nth2_bytes. inversion nth2_bytes. subst.
  assumption.
Qed.
   
Theorem utf8_spec_encoder_unique : forall encoder1 decoder codes bytes rest,
    utf8_encoder_spec encoder1 ->
    utf8_decoder_spec decoder ->
    encoder1 codes = (bytes, rest) ->
    forall encoder2,
      utf8_encoder_spec encoder2 ->
      encoder2 codes = (bytes, rest).
Proof.
  intros encoder1 decoder.
  induction codes as [| code codes_tail]; intros bytes rest encoder1_spec decoder_spec encoder1_codes encoder2 encoder2_spec.
  - pose proof (enc_nil encoder1 encoder1_spec) as encode1_nil. unfold encoder_nil in encode1_nil. rewrite encoder1_codes in encode1_nil.
    inversion encode1_nil.
    apply enc_nil. assumption.
  - replace (code :: codes_tail) with ([code] ++ codes_tail) in encoder1_codes |- * by reflexivity.
    rewrite enc_projects in encoder1_codes; [| assumption].
    destruct (encoder1 [code]) as [bytes1 code_rest] eqn:encoder1_code.
    destruct code_rest; [|inversion encoder1_codes].
    2: {
      specialize (enc_output encoder1 encoder1_spec code) as G.
      rewrite encoder1_code in G. destruct G. inversion H2. subst.
      destruct (encoder2 [code]) as [bytes2 rest2] eqn:encoder2_code.
      specialize (enc_output encoder2 encoder2_spec code) as G.
      rewrite encoder2_code in G. destruct rest2.
      + assert (exists bytes, encoder2 [code] = (bytes, [])) as code_valid. exists bytes2. assumption.
        apply enc_input in code_valid; [|assumption].
        eapply enc_input in code_valid; [|apply encoder1_spec].
        destruct code_valid as [bytes encoder1_code2].
        rewrite encoder1_code in encoder1_code2. inversion encoder1_code2.
      + destruct G as [bytes_eq rest_eq]. inversion bytes_eq. inversion rest_eq. subst.
        rewrite enc_projects; [|assumption].
        rewrite encoder2_code. reflexivity.
    } 
    destruct (encoder1 codes_tail) as [bytes2 codes_rest] eqn:encoder1_codes_tail.
    inversion encoder1_codes_tail. inversion encoder1_codes. subst.
    specialize (IHcodes_tail bytes2 rest encoder1_spec decoder_spec ltac:(reflexivity) encoder2 encoder2_spec) as encoder2_codes_tail.
    rewrite enc_projects. rewrite encoder2_codes_tail.
    assert (exists bytes, encoder1 [code] = (bytes, nil)). exists bytes1. assumption.
    apply enc_input in H.
    eapply enc_input in H; [| apply encoder2_spec].
    destruct H as [bytes3 encoder2_code]. rewrite encoder2_code.
    apply pair_equal_spec; split; auto.
    apply app_inv_tail_iff.
    specialize (utf8_spec_encoder_unique_single encoder1 decoder code bytes1 encoder1_spec decoder_spec encoder1_code encoder2 encoder2_spec) as G. rewrite G in encoder2_code. inversion encoder2_code.
    reflexivity.
    all: assumption.
Qed.
