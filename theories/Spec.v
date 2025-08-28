From Coq Require Import Lists.List.
Import ListNotations.
Require Import Utf8.Parser.

Definition b3 : Type := bool * bool * bool.
Definition b4 : Type := bool * bool * bool * bool.
Definition b5 : Type := bool * bool * bool * bool * bool.
Definition b6 : Type := bool * bool * bool * bool * bool * bool.
Definition b7 : Type := bool * bool * bool * bool * bool * bool * bool.

Definition b4_zero: b4 := (false, false, false, false).

Definition b4_equal (a b: b4) : bool :=
  let '(a1, a2, a3, a4) := a in
  let '(b1, b2, b3, b4) := b in
  (Bool.eqb a1 b1) && (Bool.eqb a2 b2) && (Bool.eqb a3 b3) && (Bool.eqb a4 b4).

Definition codepoint : Type := bool * b4 * b4 *b4 * b4 * b4.
Definition unicode_str : Type := list codepoint.

Local Notation "0" := false.
Local Notation "1" := true.

Inductive unicode_decode_error :=
| OverlongEncoding
| InvalidSurrogatePair
| CodepointTooBig
| InvalidContinuationHeader (x: option Byte.byte)
| InvalidStartHeader (x: option Byte.byte).

Inductive unicode_encode_error :=
| EncodingCodepointTooBig (c: codepoint)
| IllegalSurrogatePair (c: codepoint).

Definition encoder_type := @parser (list Byte.byte) codepoint unicode_decode_error.
Definition decoder_type := @parser (list codepoint) Byte.byte unicode_encode_error.

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

Definition valid_codepoints (codes: list codepoint) := Forall valid_codepoint codes.

Definition valid_utf8_bytes (decoder: decoder_type) (bytes: list Byte.byte) := exists codes, decoder bytes = Ok (codes, []).

Definition encoder_encode_valid_codes_correctly (encoder: encoder_type) := forall codes,
    valid_codepoints codes ->
    exists bytes, encoder codes = Ok (bytes, []).

Definition encoder_encode_correctly_implies_valid (encoder: encoder_type) (decoder: decoder_type) := forall codes bytes,
    encoder codes = Ok (bytes, []) ->
    valid_utf8_bytes decoder bytes.

Definition utf8_encoder_spec encoder decoder := encoder_encode_correctly_implies_valid encoder decoder /\ encoder_encode_valid_codes_correctly encoder.


Definition decoder_decode_correctly_implies_valid (decoder: decoder_type) := forall codes bytes,
    decoder bytes = Ok (codes, bytes) ->
    valid_codepoints codes.

Definition utf8_decoder_spec decoder := decoder_decode_correctly_implies_valid decoder.

Definition decoder_encoder_inverses (encoder: encoder_type) (decoder: decoder_type) := forall bytes bytes_rest codes codes_rest,
    encoder bytes = Ok (codes, bytes_rest) <-> decoder codes = Ok (bytes, codes_rest).

Definition utf8_spec encoder decoder :=
  utf8_encoder_spec encoder decoder /\
    utf8_decoder_spec decoder /\
    decoder_encoder_inverses encoder decoder.
