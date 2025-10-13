From Coq Require Import ZArith.BinInt.

Require Import Utf8.Spec.
From Coq Require Import Lia.

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

Inductive byte_range :=
| Range_00_7F 
| Range_80_8F
| Range_90_9F
| Range_A0_BF
| Range_C2_DF
| Byte_E0      
| Range_E1_EC
| Byte_ED
| Range_EE_EF
| Byte_F0
| Range_F1_F3
| Byte_F4
.

Definition push_bottom_bits (carry: codepoint) (b: byte): codepoint :=
  carry * 64 + (b mod 64).

Definition extract_7_bits (b: byte) : codepoint :=
  b mod 128.

Definition extract_5_bits (b: byte) : codepoint :=
  b mod 32.

Definition extract_4_bits (b: byte) : codepoint :=
  b mod 16.

Definition extract_3_bits (b: byte) : codepoint :=
  b mod 8.

Definition byte_range_dec (b: byte) : option byte_range :=
  if b <? 0 then
    None
  else if b <=? 0x7f then
    Some Range_00_7F
  else if b <=? 0x8f then
    Some Range_80_8F
  else if b <=? 0x9f then
    Some Range_90_9F
  else if b <=? 0xbf then
    Some Range_A0_BF
  else if b <=? 0xc1 then
    None
  else if b <=? 0xdf then
    Some Range_C2_DF
  else if b  =? 0xe0 then
    Some Byte_E0
  else if b <=? 0xec then
    Some Range_E1_EC
  else if b  =? 0xe then
    Some Byte_ED
  else if b <=? 0xef then
    Some Range_EE_EF
  else if b  =? 0xf0 then
    Some Byte_F0
  else if b <=? 0xf3 then
    Some Range_F1_F3
  else if b  =? 0xf4 then
    Some Byte_F4
  else
    None.

Inductive parsing_result :=
  Finished (codep: codepoint)
| More (state: parsing_state) (acc: codepoint).

Definition next_state (state: parsing_state) (carry: codepoint) (b: byte) : @option parsing_result :=
  match (state, byte_range_dec b) with
  | (Initial, Some Range_00_7F) => Some (Finished (extract_7_bits b))
  | (Initial, Some Range_C2_DF) => Some (More Expecting_1_80_BF (extract_5_bits b))
  | (Initial, Some Byte_E0)     => Some (More Expecting_2_A0_BF (extract_4_bits b))
  | (Initial, Some Range_E1_EC)
  | (Initial, Some Range_EE_EF) => Some (More Expecting_2_80_BF (extract_4_bits b))
  | (Initial, Some Byte_ED)     => Some (More Expecting_2_80_9F (extract_4_bits b))
  | (Initial, Some Byte_F0)     => Some (More Expecting_3_90_BF (extract_3_bits b))
  | (Initial, Some Range_F1_F3) => Some (More Expecting_3_80_BF (extract_3_bits b))
  | (Initial, Some Byte_F4)     => Some (More Expecting_3_80_8F (extract_3_bits b))
  | (Initial, _) => None
  | (Expecting_1_80_BF, Some Range_A0_BF)
  | (Expecting_1_80_BF, Some Range_90_9F)
  | (Expecting_1_80_BF, Some Range_80_8F) => Some (Finished (push_bottom_bits carry b))
  | (Expecting_2_80_BF, Some Range_80_8F)
  | (Expecting_2_80_BF, Some Range_90_9F)
  | (Expecting_2_80_9F, Some Range_80_8F)
  | (Expecting_2_80_9F, Some Range_90_9F)
  | (Expecting_2_80_BF, Some Range_A0_BF) => Some (More Expecting_1_80_BF (push_bottom_bits carry b))
  | (Expecting_3_80_BF, Some Range_80_8F)
  | (Expecting_3_80_BF, Some Range_90_9F)
  | (Expecting_3_80_BF, Some Range_A0_BF)
  | (Expecting_3_90_BF, Some Range_90_9F)
  | (Expecting_3_90_BF, Some Range_A0_BF)
  | (Expecting_3_80_8F, Some Range_80_8F) => Some (More Expecting_2_80_BF (push_bottom_bits carry b))
  | (Expecting_2_A0_BF, Some Range_A0_BF) => Some (More Expecting_1_80_BF (push_bottom_bits carry b))
  | (Expecting_3_80_8F, Some Range_90_9F)
  | (Expecting_3_80_8F, Some Range_A0_BF) => None
  | _ => None
  end.

Fixpoint utf8_dfa_decode_rec (bytes: list byte) (carry: codepoint) (state: parsing_state) (consumed: list byte)
  : unicode_str * (list byte) :=
  match bytes with
  | nil => (nil, nil)
  | cons b rest =>
      match next_state state carry b with
      | Some (Finished codep) =>
          let (vals, rest) := utf8_dfa_decode_rec rest 0x00 Initial nil in
          (cons codep vals, rest)
      | Some (More state codep) =>
          utf8_dfa_decode_rec rest codep state (b :: consumed)
      | None => (nil, consumed ++ bytes)
      end
  end.

Definition utf8_dfa_decode (bytes: list byte) : unicode_str * (list byte) :=
  utf8_dfa_decode_rec bytes 0x00 Initial nil.

From Coq Require Import List.
Import ListNotations.

Compute (utf8_dfa_decode [0xe0; 0xbf; 0xbf; 0x8f]).
