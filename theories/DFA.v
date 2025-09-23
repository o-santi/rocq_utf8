From Coq Require Import Strings.Byte.

Require Import Utf8.Spec.
Require Import Utf8.Parser.
From Coq Require Import Lia.

Local Notation "0" := false.
Local Notation "1" := true.
Definition zero_codep : codepoint := (0, b4_zero, b4_zero, b4_zero, b4_zero, b4_zero).


(* An implementation of the fast and efficient UTF8 decoding DFA *)
(* presented in the following post: *)
(* https://bjoern.hoehrmann.de/utf-8/decoder/dfa/ *)

Inductive parsing_state :=
  Initial
| Expecting_1_80_BF
| Expecting_2_80_BF
| Expecting_3_80_BF
| Expecting_2_80_9F
| Expecting_2_A0_BF
| Expecting_3_90_BF
| Expecting_3_80_8F.

Inductive parsing_result :=
  Finished (codep: codepoint)
| More (state: parsing_state) (acc: codepoint).

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

Definition next_state (state: parsing_state) (carry: codepoint) (b: byte) : @result parsing_result unicode_decode_error :=
  match (state, byte_range b) with
  | (Initial, Range_00_7F) => Ok (Finished (extract_7_bits b))
  | (Initial, Range_C2_DF) => Ok (More Expecting_1_80_BF (extract_5_bits b))
  | (Initial, Byte_E0)     => Ok (More Expecting_2_A0_BF (extract_4_bits b))
  | (Initial, Range_E1_EC)
  | (Initial, Range_EE_EF) => Ok (More Expecting_2_80_BF (extract_4_bits b))
  | (Initial, Byte_ED)     => Ok (More Expecting_2_80_9F (extract_4_bits b))
  | (Initial, Byte_F0)     => Ok (More Expecting_3_90_BF (extract_3_bits b))
  | (Initial, Range_F1_F3) => Ok (More Expecting_3_80_BF (extract_3_bits b))
  | (Initial, Byte_F4)     => Ok (More Expecting_3_80_8F (extract_3_bits b))
  | (Initial, _) => Err (InvalidStartHeader (Some b))
  | (Expecting_1_80_BF, Range_A0_BF)
  | (Expecting_1_80_BF, Range_90_9F)
  | (Expecting_1_80_BF, Range_80_8F) => Ok (Finished (push_bottom_bits carry b))
  | (Expecting_2_80_BF, Range_80_8F)
  | (Expecting_2_80_BF, Range_90_9F)
  | (Expecting_2_80_9F, Range_80_8F)
  | (Expecting_2_80_9F, Range_90_9F)
  | (Expecting_2_80_BF, Range_A0_BF) => Ok (More Expecting_1_80_BF (push_bottom_bits carry b))
  | (Expecting_3_80_BF, Range_80_8F)
  | (Expecting_3_80_BF, Range_90_9F)
  | (Expecting_3_80_BF, Range_A0_BF)
  | (Expecting_3_90_BF, Range_90_9F)
  | (Expecting_3_90_BF, Range_A0_BF)
  | (Expecting_3_80_8F, Range_80_8F) => Ok (More Expecting_2_80_BF (push_bottom_bits carry b))
  | (Expecting_2_A0_BF, Range_A0_BF) => Ok (More Expecting_1_80_BF (push_bottom_bits carry b))
  | (Expecting_3_80_8F, Range_90_9F)
  | (Expecting_3_80_8F, Range_A0_BF) => Err CodepointTooBig
  | _ => Err (InvalidContinuationHeader (Some b))
  end.

Fixpoint utf8_dfa_decode_rec (bytes: list byte) (carry: codepoint) (state: parsing_state)
  : @result (unicode_str * (list byte)) unicode_decode_error :=
  match bytes with
  | nil =>
      match state with
      | Initial => Ok (nil, nil)
      | _ => Err (InvalidContinuationHeader None)
      end 
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

Definition utf8_dfa_decode (bytes: list byte) : @result (unicode_str * (list byte)) unicode_decode_error :=
  utf8_dfa_decode_rec bytes zero_codep Initial.
