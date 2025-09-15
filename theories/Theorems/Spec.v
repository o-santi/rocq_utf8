From Coq Require Import Strings.Byte.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import ZArith.BinInt.

Require Import Utf8.Parser.
Require Import Utf8.Spec.
Require Import Utf8.Theorems.Order.

(* Ltac destruct_valid_bytes valid_bytes := *)
(*   let start R := *)
(*     match type of R with *)
(*     | valid_utf8_bytes (cons ?head ?tail) => idtac *)
(*     | valid_utf8_bytes ?bytes => *)
(*         let head := fresh "byte" in *)
(*         let tail := fresh "byte_rest" in *)
(*         let bytes_eq := fresh "bytes_eq" in *)
(*         destruct bytes as [|head tail] eqn:bytes_eq *)
(*     end; *)
(*     unfold valid_utf8_bytes in valid_bytes; *)
(*     fold valid_utf8_bytes in valid_bytes; *)
(*     match type of R with *)
(*     | context[byte_range ?byte] => *)
(*         let byte_in_range := fresh "byte_in_range" in *)
(*         destruct (byte_range byte) eqn:byte_in_range; try contradiction *)
(*     end *)
(*   in *)
(* let rec go R := *)
(*   unfold expect in R; *)
(*   match type of R with *)
(*   | valid_utf8_bytes ?b => idtac *)
(*   | match ?bytes with | _ => _ end => *)
(*       let head := fresh "byte" in *)
(*       let tail := fresh "byte_rest" in *)
(*       let bytes_eq := fresh "bytes_eq" in *)
(*       let byte_pred := fresh "byte_pred" in  *)
(*       let rest_pred := fresh "rest_pred" in *)
(*       destruct bytes as [| head tail] eqn:bytes_eq; try contradiction; *)
(*       destruct R as [byte_pred rest_pred]; *)
(*       go rest_pred *)
(*   end in *)
(*   start valid_bytes; go valid_bytes. *)

Theorem valid_utf8_bytes_concat : forall (bytes1 bytes2: list byte),
    valid_utf8_bytes bytes1 ->
    valid_utf8_bytes bytes2 ->
    valid_utf8_bytes (bytes1 ++ bytes2).
Proof.
  intros bytes1 bytes2 valid_bytes1. induction valid_bytes1; intros valid_bytes2. assumption.
  rewrite <- app_assoc. apply Utf8Concat. apply H. apply IHvalid_bytes1. apply valid_bytes2.
Qed.

Theorem valid_utf8_decompose : forall (bytes1 bytes2: list byte),
    valid_utf8_bytes (bytes1 ++ bytes2) ->
    valid_utf8_bytes bytes1 ->
    valid_utf8_bytes bytes2.
Proof.
  intros bytes1 bytes2 valid_concat valid_bytes1. induction valid_bytes1.
  - assumption.
  - rewrite <- app_assoc in valid_concat.
    inversion valid_concat. symmetry in H1. apply app_eq_nil in H1. destruct H1. apply app_eq_nil in H1. destruct H1. subst. constructor.
    Admitted.


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
  unfold bytes_compare in compare_codes.
  rewrite list_compare_refl_if in compare_codes. 2: apply byte_compare_eq_iff.
  unfold codepoints_compare in compare_codes. apply list_compare_refl in compare_codes. apply compare_codes.
  apply Z.compare_eq_iff.
Qed.

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
  unfold codepoints_compare in compare_codes.
  rewrite list_compare_refl_if in compare_codes. 2: apply Z.compare_eq_iff.
  unfold bytes_compare in compare_codes. symmetry in compare_codes. rewrite list_compare_refl in compare_codes.
  apply compare_codes. apply byte_compare_eq_iff.
Qed.

Lemma decoder_spec_projects_inverse: forall decoder,
    utf8_decoder_spec decoder ->
    forall bytes codes1 codes2,
      decoder bytes = (codes1 ++ codes2, []) ->
      exists bytes1 bytes2,
        decoder bytes1 = (codes1, []) /\
          decoder bytes2 = (codes2, []) /\
          bytes = bytes1 ++ bytes2.
Admitted.

Lemma decoder_spec_decode_app_valid_bytes : forall decoder,
    utf8_decoder_spec decoder ->
    forall bytes1 bytes2,
      valid_utf8_bytes bytes1 ->
      valid_utf8_bytes bytes2 ->
      decoder (bytes1 ++ bytes2) =
        let '(codes1, rest1) := decoder bytes1 in
        let '(codes2, rest2) := decoder bytes2 in
        (codes1 ++ codes2, []).
Proof.
  intros decoder decoder_spec_compliant.
  assert (G := decoder_spec_compliant).
  unfold utf8_decoder_spec, decoder_decode_correctly_implies_valid, decoder_decode_valid_utf8_bytes_correctly, decoder_strictly_increasing in G.
  destruct G as [dec_implies_valid_utf8_bytes [valid_bytes_iff_enc dec_strictly_increasing]].
  Admitted.

Lemma decoder_spec_nil_mapsto_nil : forall decoder,
    utf8_decoder_spec decoder ->
    decoder nil = (nil, []).
  intros decoder decoder_spec_compliant.
  assert (G := decoder_spec_compliant).
  unfold utf8_decoder_spec, decoder_decode_correctly_implies_valid, decoder_decode_valid_utf8_bytes_correctly, decoder_strictly_increasing in G.
  destruct G as [dec_implies_valid_utf8_bytes [valid_bytes_iff_dec dec_strictly_increasing]].
  assert (valid_utf8_bytes []) as nil_valid. constructor. apply valid_bytes_iff_dec in nil_valid as G.
  destruct G as [codes decode_codes].
  assert (decode_codes_copy := decode_codes).
  replace (nil) with (@nil byte ++ @nil byte) in decode_codes by reflexivity.
  rewrite decoder_spec_decode_app_valid_bytes in decode_codes; try assumption.
  rewrite decode_codes_copy in decode_codes.
  inversion decode_codes. symmetry in H0.
  apply list_equals_self_append_implies_nil in H0.
  subst. assumption.
Qed.

Lemma encoder_spec_implies_nth_code_mapsto_nth_byte : forall encoder,
    utf8_encoder_spec encoder ->
    forall code bytes,
      encoder [code] = (bytes, []) -> 
      exists n, nth_valid_codepoint n = Some code /\ nth_valid_byte n = Some bytes.
Admitted.

Lemma decoder_spec_implies_nth_bytes_mapsto_nth_code : forall decoder,
    utf8_decoder_spec decoder ->
    forall bytes code,
      decoder bytes = ([code], []) -> 
      exists n, nth_valid_codepoint n = Some code /\ nth_valid_byte n = Some bytes.
Admitted.

Theorem decode_encode_spec_inverses_for_single: forall encoder decoder,
    utf8_encoder_spec encoder ->
    utf8_decoder_spec decoder ->
    forall code bytes,
      encoder [code] = (bytes, []) ->
      decoder bytes = ([code], []).
Proof.
  intros encoder decoder encoder_spec_compliant decoder_spec_compliant.
  assert (G1 := encoder_spec_compliant).
  assert (G2 := decoder_spec_compliant).
  destruct G1 as [enc_implies_valid_utf8_bytes [valid_codepoints_iff_enc [enc_strictly_increasing enc_projects]]].
  destruct G2 as [dec_implies_valid [valid_implies_dec dec_strictly_increasing]].
  intros code bytes encode_code.
  apply enc_implies_valid_utf8_bytes in encode_code as G. destruct G as [bytes_valid _].
  apply valid_implies_dec in bytes_valid as G. destruct G as [codes decode_bytes].
  apply dec_implies_valid in decode_bytes as G. destruct G as [codes_valid _].
  apply valid_codepoints_iff_enc in codes_valid as G. destruct G as [bytes2 encode_codes].
  specialize (enc_strictly_increasing [code] codes bytes bytes2 encode_code encode_codes) as compare_code_codes.
  specialize (encoder_spec_implies_nil_mapsto_nil encoder encoder_spec_compliant) as encode_nil.
  specialize (decoder_spec_nil_mapsto_nil decoder decoder_spec_compliant) as decode_nil.
  destruct codes as [|code2 codes_rest].
  - specialize (decoder_spec_injective decoder decoder_spec_compliant [] bytes [] decode_nil decode_bytes) as G.
    subst. simpl in compare_code_codes. destruct bytes2; discriminate.
  - replace (code2 :: codes_rest) with ([code2] ++ codes_rest) in encode_codes, decode_bytes, codes_valid, compare_code_codes by reflexivity.
    rewrite enc_projects in encode_codes.
    destruct (encoder [code2]) as [bytes3 rest] eqn:encode_code2.
    destruct (encoder codes_rest) as [bytes4 rest2] eqn:encode_codes_rest.
    destruct rest; [|discriminate]. inversion encode_codes. subst. clear encode_codes.
    specialize (enc_strictly_increasing [code] [code2] bytes bytes3 encode_code encode_code2) as compare_code_code2.
    apply decoder_spec_projects_inverse in decode_bytes. 2: assumption.
    destruct decode_bytes as [bytes1 [bytes2 [decode_bytes1 [decode_bytes2 bytes_eq]]]].
    rewrite bytes_eq in compare_code_codes, compare_code_code2, encode_code, bytes_valid |- *.
    destruct bytes1. rewrite decode_nil in decode_bytes1. inversion decode_bytes1.
    rewrite <- app_comm_cons in bytes_valid.
    destruct bytes3. specialize (encoder_spec_injective encoder encoder_spec_compliant [] [code2] [] encode_nil encode_code2) as G. inversion G.
Admitted.
    (* destruct_valid_bytes bytes_valid. *)

    
   
Theorem decode_encode_spec_compliant_decode_inverse_of_encode : forall encoder decoder,
    utf8_encoder_spec encoder ->
    utf8_decoder_spec decoder ->
    forall (codes_big codes: list codepoint) bytes codes_suffix,
      (length codes) <= (length codes_big) ->
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
  induction codes_big; intros codes bytes codes_suffix less_than encoder_codes.
  - inversion less_than. apply length_zero_iff_nil in H0. subst.
    specialize (encoder_spec_implies_nil_mapsto_nil encoder encoder_spec_compliant) as encode_nil.
    rewrite encode_nil in encoder_codes. inversion encoder_codes. exists [].
    split. apply decoder_spec_nil_mapsto_nil. apply decoder_spec_compliant. reflexivity.
  - apply enc_implies_valid_utf8_bytes in encoder_codes as [bytes_valid [codes_prefix [codes_prefix_eq encoder_codes_prefix]]].
    exists codes_prefix. destruct codes_prefix.
    + rewrite encoder_spec_implies_nil_mapsto_nil in encoder_codes_prefix. 2: apply encoder_spec_compliant. inversion encoder_codes_prefix. split. apply decoder_spec_nil_mapsto_nil. apply decoder_spec_compliant. assumption.
    + split; [| apply codes_prefix_eq].
      replace (c :: codes_prefix) with ([c] ++ codes_prefix) in encoder_codes_prefix by reflexivity.
      rewrite enc_projects in encoder_codes_prefix.
      destruct (encoder [c]) as [bytes1 c_rest]  eqn:encoder_c.
      destruct (encoder codes_prefix) as [bytes2 codes_rest] eqn:encoder_codes_prefix2.
      destruct c_rest; try discriminate. inversion encoder_codes_prefix. subst.
      rewrite length_app in less_than.
      clear encoder_codes_prefix.
      apply enc_implies_valid_utf8_bytes in encoder_c as G1, encoder_codes_prefix2 as G2.
      destruct G1 as [bytes1_valid _]. destruct G2 as [bytes2_valid _].
      simpl in less_than. apply IHcodes_big in encoder_codes_prefix2. 2: lia.
      rewrite decoder_spec_decode_app_valid_bytes; try assumption.
      destruct encoder_codes_prefix2 as [codes_prefix2 [decoder_bytes2 codes_prefix2_eq]]. subst.
      rewrite decoder_bytes2. apply valid_implies_dec in bytes1_valid as [codes decode_bytes1].
      rewrite decode_bytes1. rewrite app_nil_r.
      rewrite pair_equal_spec. split; [| reflexivity].
      replace (c :: codes_prefix2) with ([c] ++ codes_prefix2) by reflexivity.
      clear decoder_bytes2. clear bytes2_valid.
      apply app_inv_tail_iff.

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
        
