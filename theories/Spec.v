From Coq Require Import Lists.List.
From Coq Require Import Strings.Byte.
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


Inductive range :=
  Range_00_7F
| Range_80_8F
| Range_90_9F
| Range_A0_BF
| Range_C0_C1
| Range_C2_DF
| Byte_E0 
| Range_E1_EC
| Byte_ED
| Range_EE_EF
| Byte_F0
| Range_F1_F3
| Byte_F4
| Range_F5_FF
.

Definition byte_range (b: Byte.byte) : range :=
  match b with
    x00 | x01 | x02 | x03 | x04 | x05 | x06 | x07 | x08 | x09 | x0a | x0b | x0c | x0d | x0e | x0f
  | x10 | x11 | x12 | x13 | x14 | x15 | x16 | x17 | x18 | x19 | x1a | x1b | x1c | x1d | x1e | x1f
  | x20 | x21 | x22 | x23 | x24 | x25 | x26 | x27 | x28 | x29 | x2a | x2b | x2c | x2d | x2e | x2f
  | x30 | x31 | x32 | x33 | x34 | x35 | x36 | x37 | x38 | x39 | x3a | x3b | x3c | x3d | x3e | x3f
  | x40 | x41 | x42 | x43 | x44 | x45 | x46 | x47 | x48 | x49 | x4a | x4b | x4c | x4d | x4e | x4f
  | x50 | x51 | x52 | x53 | x54 | x55 | x56 | x57 | x58 | x59 | x5a | x5b | x5c | x5d | x5e | x5f
  | x60 | x61 | x62 | x63 | x64 | x65 | x66 | x67 | x68 | x69 | x6a | x6b | x6c | x6d | x6e | x6f
  | x70 | x71 | x72 | x73 | x74 | x75 | x76 | x77 | x78 | x79 | x7a | x7b | x7c | x7d | x7e | x7f => Range_00_7F
  | x80 | x81 | x82 | x83 | x84 | x85 | x86 | x87 | x88 | x89 | x8a | x8b | x8c | x8d | x8e | x8f => Range_80_8F
  | x90 | x91 | x92 | x93 | x94 | x95 | x96 | x97 | x98 | x99 | x9a | x9b | x9c | x9d | x9e | x9f => Range_90_9F
  | xa0 | xa1 | xa2 | xa3 | xa4 | xa5 | xa6 | xa7 | xa8 | xa9 | xaa | xab | xac | xad | xae | xaf
  | xb0 | xb1 | xb2 | xb3 | xb4 | xb5 | xb6 | xb7 | xb8 | xb9 | xba | xbb | xbc | xbd | xbe | xbf => Range_A0_BF
  | xc0 | xc1 => Range_C0_C1
  | xc2 | xc3 | xc4 | xc5 | xc6 | xc7 | xc8 | xc9 | xca | xcb | xcc | xcd | xce | xcf
  | xd0 | xd1 | xd2 | xd3 | xd4 | xd5 | xd6 | xd7 | xd8 | xd9 | xda | xdb | xdc | xdd | xde | xdf => Range_C2_DF
  | xe0 => Byte_E0
  | xe1 | xe2 | xe3 | xe4 | xe5 | xe6 | xe7 | xe8 | xe9 | xea | xeb | xec  => Range_E1_EC
  | xed => Byte_ED
  | xee | xef => Range_EE_EF
  | xf0 => Byte_F0
  | xf1 | xf2 | xf3 => Range_F1_F3
  | xf4 => Byte_F4
  | xf5 | xf6 | xf7 | xf8 | xf9 | xfa | xfb | xfc | xfd | xfe | xff => Range_F5_FF
  end.

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

Definition expect (Pred: byte -> Prop) (Pred_rest: list byte -> Prop) bytes :=
  match bytes with
  | [] => False
  | byte :: rest => Pred byte /\ Pred_rest rest
  end.

Definition in_range_80_bf byte :=
  match byte_range byte with
  | Range_80_8F | Range_90_9F | Range_A0_BF => True
  | _ => False
  end.

Definition in_range_80_8f byte :=
  match byte_range byte with
  | Range_80_8F => True
  | _ => False
  end.

Definition in_range_a0_bf byte :=
  match byte_range byte with
  | Range_A0_BF => True
  | _ => False
  end.

Definition in_range_90_bf byte :=
  match byte_range byte with
  | Range_90_9F | Range_A0_BF => True
  | _ => False
  end.

Definition in_range_80_9f byte :=
  match byte_range byte with
  | Range_80_8F | Range_90_9F => True
  | _ => False
  end.

Fixpoint valid_utf8_bytes (bytes: list Byte.byte) : Prop :=
  match bytes with
  | [] => True
  | byte1 :: rest =>
      match byte_range byte1 with
      | Range_00_7F => valid_utf8_bytes rest
      | Range_C2_DF => expect in_range_80_bf valid_utf8_bytes rest
      | Byte_E0     => expect in_range_a0_bf (expect in_range_80_8f valid_utf8_bytes) rest
      | Range_E1_EC
      | Range_EE_EF => expect in_range_80_bf (expect in_range_80_bf valid_utf8_bytes) rest
      | Byte_ED     => expect in_range_80_9f (expect in_range_80_bf valid_utf8_bytes) rest
      | Byte_F0     => expect in_range_90_bf (expect in_range_80_bf (expect in_range_80_bf valid_utf8_bytes)) rest
      | Range_F1_F3 => expect in_range_80_bf (expect in_range_80_bf (expect in_range_80_bf valid_utf8_bytes)) rest
      | Byte_F4     => expect in_range_80_8f (expect in_range_80_bf (expect in_range_80_bf valid_utf8_bytes)) rest
      | _           => False
      end
  end.

Definition encoder_encode_valid_codes_correctly (encoder: encoder_type) := forall codes,
    valid_codepoints codes ->
    exists bytes, encoder codes = Ok (bytes, []).

Definition encoder_encode_correctly_implies_valid (encoder: encoder_type) := forall codes bytes,
    encoder codes = Ok (bytes, []) ->
    valid_utf8_bytes bytes.

Definition utf8_encoder_spec encoder := encoder_encode_correctly_implies_valid encoder /\ encoder_encode_valid_codes_correctly encoder.

Definition decoder_decode_correctly_implies_valid (decoder: decoder_type) := forall codes bytes,
    decoder bytes = Ok (codes, bytes) ->
    valid_codepoints codes.

Definition decoder_decode_valid_utf8_bytes_correctly (decoder: decoder_type) := forall bytes,
    valid_utf8_bytes bytes ->
    exists codes, decoder bytes = Ok (codes, []).

Definition utf8_decoder_spec decoder := decoder_decode_correctly_implies_valid decoder /\ decoder_decode_valid_utf8_bytes_correctly decoder.

Definition decoder_encoder_inverses (encoder: encoder_type) (decoder: decoder_type) := forall bytes bytes_rest codes codes_rest,
    encoder bytes = Ok (codes, bytes_rest) <-> decoder codes = Ok (bytes, codes_rest).

Definition utf8_spec encoder decoder :=
  utf8_encoder_spec encoder /\ utf8_decoder_spec decoder /\
    decoder_encoder_inverses encoder decoder.
