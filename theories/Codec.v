From Coq Require Import ZArith.BinInt.
From Coq Require Import Lists.List.
Import ListNotations.

Require Import Utf8.Spec.

(* The definition of UTF-8 prohibits encoding character numbers between *)
(* U+D800 and U+DFFF and characters bigger than U+10FFFF*)
Definition utf8_encode_codepoint (n: codepoint) : @option (list byte) :=
  if (n <? 0) then
    None
  else if (n <=? 127) then
    Some [ n ]
  else if (n <=? 0x7ff) then
    let b1 := n / 64 in
    let b2 := n mod 64 in
    Some [ 192 + b1; 128 + b2]
  else if (andb (n <=? 0xffff) (orb (n <? 0xd800) (n >? 0xdfff))) then
    let r := n / 64 in
    let b1 := r / 64 in
    let b2 := r mod 64 in
    let b3 := n mod 64 in
    Some [ 224 + b1; 128 + b2; 128 + b3]
  else if (andb (n <=? 0x10ffff) (n >? 0xffff)) then
    let r1 := n / 64 in
    let r2 := r1 / 64 in
    let b1 := r2 / 64 in
    let b2 := r2 mod 64 in
    let b3 := r1 mod 64 in
    let b4 := n mod 64 in
    Some [ 240 + b1; 128 + b2; 128 + b3; 128 + b4]
  else
    None.

Fixpoint utf8_encode (unicode: unicode_str) : (list byte) * (list codepoint) :=
  match unicode with
  | [] => ([], [])
  | code :: unicode_rest =>
      match utf8_encode_codepoint code with
      | None => ([], code :: unicode_rest)
      | Some bytes => 
          let (bytes_rest, unicode_rest) := utf8_encode unicode_rest in
          (bytes ++ bytes_rest, unicode_rest)
      end
  end.

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
      | None => (nil, app consumed bytes)
      end
  end.

Definition utf8_dfa_decode (bytes: list byte) : unicode_str * (list byte) :=
  utf8_dfa_decode_rec bytes 0x00 Initial nil.
