From Coq Require Import Lists.List.
From Coq Require Import Hexadecimal.
From Coq Require Import ZArith.BinInt.
Import ListNotations.
Require Import Utf8.Parser.

Open Scope Z_scope.

Definition codepoint : Type := Z.

Definition unicode_str : Type := list codepoint.
Definition byte_str : Type := list Z.

Local Notation "0" := false.
Local Notation "1" := true.

Definition codepoints_compare := List.list_compare Z.compare.
Definition bytes_compare := List.list_compare Z.compare.

Inductive unicode_decode_error :=
| OverlongEncoding
| InvalidSurrogatePair
| CodepointTooBig
| InvalidContinuationHeader (x: option Byte.byte)
| InvalidStartHeader (x: option Byte.byte).

Inductive unicode_encode_error :=
| EncodingCodepointTooBig (c: codepoint)
| IllegalSurrogatePair (c: codepoint).

Definition encoder_type := unicode_str -> byte_str * unicode_str.
Definition decoder_type := byte_str -> unicode_str * byte_str.

Definition codepoint_less_than_10ffff (code: codepoint) : Prop :=
  Z.le code 0x10ffff.

Definition codepoint_is_not_surrogate (code: codepoint) : Prop :=
  (Z.lt code 0xd800) \/ (Z.gt code 0xdfff).

Definition codepoint_not_negative (code: codepoint): Prop :=
  Z.ge code 0.

Definition valid_codepoint (code: codepoint) := codepoint_less_than_10ffff code /\ codepoint_is_not_surrogate code /\ codepoint_not_negative code.

Definition valid_codepoints (codes: list codepoint) := Forall valid_codepoint codes.

Inductive valid_codepoint_representation : list Z -> Prop :=
| OneByte (b: Z) :
  0 <= b <= 0x7f ->
  valid_codepoint_representation [b]
| TwoByte (b1 b2: Z):
  0xc2 <= b1 <= 0xdf ->
  0x80 <= b2 <= 0xbf ->
  valid_codepoint_representation [b1; b2]
| ThreeByte1 (b1 b2 b3: Z):
  b1 = 0xe0 ->
  0xa0 <= b2 <= 0xbf ->
  0x80 <= b3 <= 0xbf ->
  valid_codepoint_representation [b1; b2; b3]
| ThreeByte2 (b1 b2 b3: Z):
  0xe1 <= b1 <= 0xec \/ 0xee <= b1 <= 0xef ->
  0x80 <= b2 <= 0xbf ->
  0x80 <= b3 <= 0xbf ->
  valid_codepoint_representation [b1; b2; b3]
| ThreeByte3 (b1 b2 b3: Z):
  b1 = 0xed ->
  0x80 <= b2 <= 0x9f ->
  0x80 <= b3 <= 0xbf ->
  valid_codepoint_representation [b1; b2; b3]
| FourBytes1 (b1 b2 b3 b4: Z):
  b1 = 0xf0 ->
  0x90 <= b2 <= 0xbf ->
  0x80 <= b3 <= 0xbf ->
  0x80 <= b4 <= 0xbf ->
  valid_codepoint_representation [b1; b2; b3; b4]
| FourBytes2 (b1 b2 b3 b4: Z):
  0xf1 <= b1 <= 0xf3 ->
  0x80 <= b2 <= 0xbf ->
  0x80 <= b3 <= 0xbf ->
  0x80 <= b4 <= 0xbf ->
  valid_codepoint_representation [b1; b2; b3; b4]
| FourBytes3 (b1 b2 b3 b4: Z):
  b1 = 0xf4 ->
  0x80 <= b2 <= 0x8f ->
  0x80 <= b3 <= 0xbf ->
  0x80 <= b4 <= 0xbf ->
  valid_codepoint_representation [b1; b2; b3; b4].

Inductive valid_utf8_bytes: list Z ->  Prop :=
| Utf8Nil : valid_utf8_bytes []
| Utf8Concat (bytes tail: list Z) :
    valid_codepoint_representation bytes ->
    valid_utf8_bytes tail ->
    valid_utf8_bytes (bytes ++ tail).

Definition encoder_encode_valid_codes_correctly (encoder: encoder_type) := forall codes,
    valid_codepoints codes <->
      exists bytes, encoder codes = (bytes, []).

Definition encoder_encode_correctly_implies_valid (encoder: encoder_type) := forall codes codes_suffix bytes,
    encoder codes = (bytes, codes_suffix) ->
    (valid_utf8_bytes bytes
     /\ exists codes_prefix,
        (codes = codes_prefix ++ codes_suffix /\ encoder codes_prefix = (bytes, nil))).

Definition encoder_strictly_increasing (encoder: encoder_type) := forall codes1 codes2 bytes1 bytes2,
    encoder codes1 = (bytes1, nil) ->
    encoder codes2 = (bytes2, nil) ->
    codepoints_compare codes1 codes2 = bytes_compare bytes1 bytes2.

Definition encoder_projects (encoder: encoder_type) := forall xs ys,
    encoder (xs ++ ys) =
      match encoder xs with
      | (bytes, nil) =>
          let (bytes2, rest) := encoder ys in
          (bytes ++ bytes2, rest)
      | (bytes, rest) => (bytes, rest ++ ys)
      end.

Definition utf8_encoder_spec encoder :=
  encoder_encode_correctly_implies_valid encoder
  /\ encoder_encode_valid_codes_correctly encoder
  /\ encoder_strictly_increasing encoder
  /\ encoder_projects encoder.

Definition decoder_decode_correctly_implies_valid (decoder: decoder_type) := forall codes bytes bytes_suffix,
    decoder bytes = (codes, bytes_suffix) ->
    valid_codepoints codes /\
      (exists bytes_prefix,
          (bytes = bytes_prefix ++ bytes_suffix) /\ (decoder bytes_prefix = (codes, nil))).

Definition decoder_decode_valid_utf8_bytes_correctly (decoder: decoder_type) := forall bytes,
    valid_utf8_bytes bytes <->
      exists codes, decoder bytes = (codes, []).

Definition decoder_strictly_increasing (decoder: decoder_type) := forall bytes1 bytes2 codes1 codes2,
    decoder bytes1 = (codes1, nil) ->
    decoder bytes2 = (codes2, nil) ->
    codepoints_compare codes1 codes2 = bytes_compare bytes1 bytes2.

Definition utf8_decoder_spec decoder :=
  decoder_decode_correctly_implies_valid decoder
  /\ decoder_decode_valid_utf8_bytes_correctly decoder
  /\ decoder_strictly_increasing decoder.

Definition utf8_spec encoder decoder :=
  utf8_encoder_spec encoder /\ utf8_decoder_spec decoder.
