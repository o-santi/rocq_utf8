From Stdlib Require Import Strings.Byte.

Require Import Utf8.Utf8.
Require Import Utf8.Parser.
From Stdlib Require Import Lia.

Local Notation "0" := false.
Local Notation "1" := true.
Definition zero_codep : codepoint := (0, b4_zero, b4_zero, b4_zero, b4_zero, b4_zero).


(* An implementation of the fast and efficient UTF8 decoding DFA *)
(* presented in the following post: *)
(* https://writings.sh/post/en/utf8/ *)

Inductive range :=
  Range_00_7F
| Range_80_8F
| Range_90_9F
| Range_A0_BF
| Range_C0_C1
| Range_C2_DF
| Byte_E0 
| Range_E1_EF
| Byte_F0
| Range_F1_F3
| Byte_F4
| Range_F5_FF
.

Inductive parsing_state :=
  Initial
| Expecting_1_80_BF
| Expecting_2_80_BF
| Expecting_3_80_BF
| Expecting_2_A0_BF
| Expecting_3_90_BF
| Expecting_3_80_8F.

Inductive parsing_result :=
  Finished (codep: codepoint)
| More (state: parsing_state) (acc: codepoint).

Definition byte_range (b: byte) : range :=
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
  | xe1 | xe2 | xe3 | xe4 | xe5 | xe6 | xe7 | xe8 | xe9 | xea | xeb | xec | xed | xee | xef => Range_E1_EF
  | xf0 => Byte_F0
  | xf1 | xf2 | xf3 => Range_F1_F3
  | xf4 => Byte_F4
  | xf5 | xf6 | xf7 | xf8 | xf9 | xfa | xfb | xfc | xfd | xfe | xff => Range_F5_FF
  end.


Definition push_bottom_bits (carry: codepoint) (b: byte): codepoint :=
  let '(_, _, (_, b1, b2, b3), (b4, b5, b6, b7), (b8, b9, b10, b11), (b12, b13, b14, b15)) := carry in
  let '(b21, (b20, (b19, (b18, (b17, (b16, (h1, h2))))))) := Byte.to_bits b in
  (b1, (b2, b3, b4, b5), (b6, b7, b8, b9), (b10, b11, b12, b13), (b14, b15, b16, b17), (b18, b19, b20, b21)).

Definition extract_7_bits (b: byte) : codepoint :=
  let '(b1, (b2, (b3, (b4, (b5, (b6, (b7, b8))))))) := Byte.to_bits b in
  (0, b4_zero, b4_zero, b4_zero, (0, b7, b6, b5), (b4, b3, b2, b1)).

Definition extract_5_bits (b: byte) : codepoint :=
  let '(b1, (b2, (b3, (b4, (b5, (b6, (b7, b8))))))) := Byte.to_bits b in
  (0, b4_zero, b4_zero, b4_zero, (0, 0, 0, b5), (b4, b3, b2, b1)).

Definition extract_4_bits (b: byte) : codepoint :=
  let '(b1, (b2, (b3, (b4, (b5, (b6, (b7, b8))))))) := Byte.to_bits b in
  (0, b4_zero, b4_zero, b4_zero, b4_zero, (b4, b3, b2, b1)).

Definition extract_3_bits (b: byte) : codepoint :=
  let '(b1, (b2, (b3, (b4, (b5, (b6, (b7, b8))))))) := Byte.to_bits b in
  (0, b4_zero, b4_zero, b4_zero, b4_zero, (0, b3, b2, b1)).

Definition next_state (state: parsing_state) (carry: codepoint) (b: byte) : @result parsing_result (@error unicode_decode_error) :=
  match (state, byte_range b) with
  | (Initial, Range_00_7F) => Ok (Finished (extract_7_bits b))
  | (Initial, Range_C2_DF) => Ok (More Expecting_1_80_BF (extract_5_bits b))
  | (Initial, Byte_E0)     => Ok (More Expecting_2_A0_BF (extract_4_bits b))
  | (Initial, Range_E1_EF) => Ok (More Expecting_2_80_BF (extract_5_bits b))
  | (Initial, Byte_F0)     => Ok (More Expecting_3_90_BF (extract_3_bits b))
  | (Initial, Range_F1_F3) => Ok (More Expecting_3_80_BF (extract_3_bits b))
  | (Initial, Byte_F4)     => Ok (More Expecting_3_80_8F (extract_3_bits b))
  | (Initial, Range_C0_C1) => Err (Error InvalidSurrogatePair)
  | (Initial, Range_F5_FF) => Err (Error CodepointTooBig)
  | (Initial, _) => Err (Error (InvalidStartHeader (Some b)))
  | (Expecting_1_80_BF,  Range_A0_BF)
  | (Expecting_1_80_BF,  Range_90_9F)
  | (Expecting_1_80_BF,  Range_80_8F) => Ok (Finished (push_bottom_bits carry b))
  | (Expecting_2_80_BF,  Range_80_8F)
  | (Expecting_2_80_BF,  Range_90_9F)
  | (Expecting_2_80_BF,  Range_A0_BF) => Ok (More Expecting_1_80_BF (push_bottom_bits carry b))
  | (Expecting_3_80_BF, Range_80_8F)
  | (Expecting_3_80_BF, Range_90_9F)
  | (Expecting_3_80_BF, Range_A0_BF)
  | (Expecting_3_90_BF, Range_90_9F)
  | (Expecting_3_90_BF, Range_A0_BF)
  | (Expecting_3_80_8F, Range_80_8F) => Ok (More Expecting_2_80_BF (push_bottom_bits carry b))
  | (Expecting_2_A0_BF, Range_A0_BF) => Ok (More Expecting_1_80_BF (push_bottom_bits carry b))
  | (Expecting_3_80_8F, Range_90_9F)
  | (Expecting_3_80_8F, Range_A0_BF) => Err (Error CodepointTooBig)
  | _ => Err (Error (InvalidContinuationHeader (Some b)))
  end.

Fixpoint utf8_dfa_decode_rec (bytes: list byte) (carry: codepoint) (state: parsing_state)
  : @result (unicode_str * (list byte)) (@error unicode_decode_error) :=
  match bytes with
  | nil => Ok (nil, nil)
  | cons b rest =>
      let* next := next_state state carry b in
      match next with
      | Finished codep =>
          let* (vals, rest) := utf8_dfa_decode_rec rest zero_codep Initial in
          Ok (cons codep vals, rest)
      | More state codep =>
          utf8_dfa_decode_rec rest codep state
      end
  end.

Definition utf8_dfa_decode (bytes: list byte) : @result (unicode_str * (list byte)) (@error unicode_decode_error) :=
  utf8_dfa_decode_rec bytes zero_codep Initial.
