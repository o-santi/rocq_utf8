From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.Byte.

From Coq Require Import Lists.List. Import ListNotations.

Require Import Utf8.Parser.

(* ============================================== *)
(* UTF-8 encoding and decoding                    *)
(* ============================================== *)

Local Notation "0" := false.
Local Notation "1" := true.

Definition b3 : Type := bool * bool * bool.
Definition b4 : Type := bool * bool * bool * bool.
Definition b5 : Type := bool * bool * bool * bool * bool.
Definition b6 : Type := bool * bool * bool * bool * bool * bool.
Definition b7 : Type := bool * bool * bool * bool * bool * bool * bool.

Definition b4_zero: b4 := (false, false, false, false).

Open Scope bool_scope.

Definition b4_equal (a b: b4) : bool :=
  let '(a1, a2, a3, a4) := a in
  let '(b1, b2, b3, b4) := b in
  (Bool.eqb a1 b1) && (Bool.eqb a2 b2) && (Bool.eqb a3 b3) && (Bool.eqb a4 b4).

Inductive hex : Type :=
| H0 | H1 | H2 | H3
| H4 | H5 | H6 | H7
| H8 | H9 | HA | HB
| HC | HD | HE | HF.

Definition b4_to_hex (b: b4) : hex :=
  match b with
  | (0, 0, 0, 0) => H0
  | (0, 0, 0, 1) => H1
  | (0, 0, 1, 0) => H2
  | (0, 0, 1, 1) => H3
  | (0, 1, 0, 0) => H4
  | (0, 1, 0, 1) => H5
  | (0, 1, 1, 0) => H6
  | (0, 1, 1, 1) => H7
  | (1, 0, 0, 0) => H8
  | (1, 0, 0, 1) => H9
  | (1, 0, 1, 0) => HA
  | (1, 0, 1, 1) => HB
  | (1, 1, 0, 0) => HC
  | (1, 1, 0, 1) => HD
  | (1, 1, 1, 0) => HE
  | (1, 1, 1, 1) => HF
  end.

Definition hex_to_ascii (h: hex) : ascii :=
  match h with 
  | H0 => "0"
  | H1 => "1"
  | H2 => "2"
  | H3 => "3"
  | H4 => "4"
  | H5 => "5"
  | H6 => "6"
  | H7 => "7"
  | H8 => "8"
  | H9 => "9"
  | HA => "A"
  | HB => "B"
  | HC => "C"
  | HD => "D"
  | HE => "E"
  | HF => "F"
  end.

Inductive codepoint_range :=
| FirstRange (b: b7)
| SecondRange (fst: b5) (snd: b6)
| ThirdRange (fst: b4) (snd: b6) (trd: b6)
| FourthRange (fst: b3) (snd: b6) (trd: b6) (frth: b6).

Inductive unicode_decode_error :=
| OverlongEncoding
| InvalidSurrogatePair
| CodepointTooBig
| InvalidContinuationHeader (x: option byte)
| InvalidStartHeader (x: option byte).

Inductive encoding_size :=
| OneByte (b: b7)
| TwoBytes (b: b5)
| ThreeBytes (b: b4)
| FourBytes (b: b3).

Definition codepoint : Type := bool * b4 * b4 *b4 * b4 * b4.

Definition show_codepoint (c: codepoint) : string :=
  let p := fun (b: b4) => hex_to_ascii (b4_to_hex b) in
  let '(b1, b2, b3, b4, b5, b6) := c in
  match (b1, b2) with
  | (0, (0, 0, 0, 0)) => String "U" (String "+" (String (p b3) (String (p b4) (String (p b5) (String (p b6) EmptyString)))))
  | _ => String "U" (String "+" (String (match b1 with true => "1"| false => "0" end) (String (p b2) (String (p b3) (String (p b4) (String (p b5) (String (p b6) EmptyString)))))))
  end.

(* The definition of UTF-8 prohibits encoding character numbers between *)
(* U+D800 and U+DFFF, which are reserved for use with the UTF-16 *)
(* encoding form (as surrogate pairs) and do not directly represent *)
(* characters. *)

(* 16#D800 = 2#1101100000000000 *)
(* 16#DFFF = 2#1101111111111111 *)

Definition codepoint_range_to_codepoint (cr: codepoint_range) : @result codepoint unicode_decode_error :=
  match cr with
  | FirstRange (b1, b2, b3, b4, b5, b6, b7) =>
      Ok (0, b4_zero, b4_zero, b4_zero, (0, b1, b2, b3), (b4, b5, b6, b7))
  | SecondRange (0, 0, 0, 0, _) _snd => Err OverlongEncoding (* overlong encoding *)
  | SecondRange (b1, b2, b3, b4, b5) (b6, b7, b8, b9, b10, b11) =>
      Ok (0, b4_zero, b4_zero, (0, b1, b2, b3), (b4, b5, b6, b7), (b8, b9, b10, b11))
  | ThirdRange (0, 0, 0, 0) (0, _, _, _, _, _) _trd => Err OverlongEncoding (* overlong encoding *)
  | ThirdRange (1, 1, 0, 1) (1, _, _, _, _, _) _trd => Err InvalidSurrogatePair (* surrogate pairs are not allowed *)                 
  | ThirdRange (b1, b2, b3, b4) (b5, b6, b7, b8, b9, b10) (b11, b12, b13, b14, b15, b16) =>
      Ok (0, b4_zero, (b1, b2, b3, b4), (b5, b6, b7, b8), (b9, b10, b11, b12), (b13, b14, b15, b16))
  | FourthRange (0, 0, 0) (0, 0, _, _, _, _) _trd _frth => Err OverlongEncoding (* overlong encoding *)
  | FourthRange (0, b2, b3) (b4, b5, b6, b7, b8, b9) (b10, b11, b12, b13, b14, b15) (b16, b17, b18, b19, b20, b21) =>
      Ok (0, (b2, b3, b4, b5), (b6, b7, b8, b9), (b10, b11, b12, b13), (b14, b15, b16, b17), (b18, b19, b20, b21))
  | FourthRange (1, 0, 0) (0, 0, b6, b7, b8, b9) (b10, b11, b12, b13, b14, b15) (b16, b17, b18, b19, b20, b21) =>
      Ok (1, (0, 0, 0, 0), (b6, b7, b8, b9), (b10, b11, b12, b13), (b14, b15, b16, b17), (b18, b19, b20, b21))
  | FourthRange _fst _snd _trd _frth => Err CodepointTooBig
  (* | _ => None *)
  end.

Definition codepoint_eqb (a b: codepoint) : bool :=
  let '(a1, a2, a3, a4, a5, a6) := a in
  let '(b1, b2, b3, b4, b5, b6) := b in
  (Bool.eqb a1 b1) && b4_equal a2 b2 && b4_equal a3 b3 && b4_equal a4 b4 && b4_equal a5 b5 && b4_equal a6 b6.

Definition from_ascii (c: ascii) : codepoint :=
  let '(b1, (b2, (b3, (b4, (b5, (b6, (b7, _))))))) := to_bits (byte_of_ascii c) in
  (0, b4_zero, b4_zero, b4_zero, (false, b7, b6, b5), (b4, b3, b2, b1)).

Definition unicode_str : Type := list codepoint.


(* Char. number range  |        UTF-8 octet sequence *)
(*    (hexadecimal)    |              (binary) *)
(* --------------------+--------------------------------------------- *)
(* 0000 0000-0000 007F | 0xxxxxxx *)
(* 0000 0080-0000 07FF | 110xxxxx 10xxxxxx *)
(* 0000 0800-0000 FFFF | 1110xxxx 10xxxxxx 10xxxxxx *)
(* 0001 0000-0010 FFFF | 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx *)

Definition encoding_size_from_header (b: byte) : option encoding_size :=
  match to_bits b with
  | (b1, (b2, (b3, (b4, (b5, (b6, (b7, 0))))))) => Some (OneByte (b7, b6, b5, b4, b3, b2, b1))
  | (b1, (b2, (b3, (b4, (b5, (0, (1, 1))))))) => Some (TwoBytes (b5, b4, b3, b2, b1))
  | (b1, (b2, (b3, (b4, (0, (1, (1, 1))))))) => Some (ThreeBytes (b4, b3, b2, b1))
  | (b1, (b2, (b3, (0, (1, (1, (1, 1))))))) => Some (FourBytes (b3, b2, b1))
  | _ => None
  end. 

Definition parse_continuation : @parser b6 byte unicode_decode_error :=
  let continuation_from_byte :=
    fun b =>
      let '(b1, (b2, (b3, (b4, (b5, (b6, (b7, b8))))))) := to_bits b in
      (b6, b5, b4, b3, b2, b1) in
  let is_continuation :=
    fun (b: byte) =>
      let '(b1, (b2, (b3, (b4, (b5, (b6, (b7, b8))))))) := to_bits b in
      andb b8 (negb b7) in
  parser_map continuation_from_byte (predicate is_continuation InvalidContinuationHeader).

Definition parse_header : @parser encoding_size byte unicode_decode_error :=
  fun s =>
    match s with
    | [] => Err (Error (InvalidStartHeader None))
    | h :: rest =>
        match encoding_size_from_header h with
        | None => Err (Error (InvalidStartHeader (Some h)))
        | Some e => Ok (e, rest)
        end
    end.

Definition parse_codepoint : @parser codepoint byte unicode_decode_error :=
  fun s =>
    let* (size, rest) := parse_header s in
    let* (codepoint_bits, rest) :=
      match size with
      | OneByte fst => Ok (FirstRange fst, rest)
      | TwoBytes fst =>
          let* (snd, rest) := parse_continuation rest in
          Ok (SecondRange fst snd, rest)
      | ThreeBytes fst =>
          let* (snd, rest) := parse_continuation rest in
          let* (trd, rest) := parse_continuation rest in
          Ok (ThirdRange fst snd trd, rest)
      | FourBytes fst =>
          let* (snd,  rest) := parse_continuation rest in
          let* (trd,  rest) := parse_continuation rest in
          let* (frth, rest) := parse_continuation rest in
          Ok (FourthRange fst snd trd frth, rest)
      end in
    match codepoint_range_to_codepoint codepoint_bits with
    | Ok code => Ok (code, rest)
    | Err err => Err (Error err)
    end.

Definition utf8_decode : @parser unicode_str byte unicode_decode_error :=
  all parse_codepoint.

Definition to_unicode (s: string) : @result unicode_str (@error unicode_decode_error) :=
  let bytes := List.map byte_of_ascii (list_ascii_of_string s) in
  fmap (fun '(v, _) => v) (utf8_decode bytes).

Inductive unicode_encode_error :=
| EncodingCodepointTooBig (c: codepoint)
| IllegalSurrogatePair (c: codepoint).

(* The definition of UTF-8 prohibits encoding character numbers between *)
(*    U+D800 and U+DFFF
   and characters bigger than U+10FFFF*)
Definition utf8_encode_codepoint (c: codepoint) : @result (list byte) unicode_encode_error :=
  match c with
  | (0, (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, b1, b2, b3), (b4, b5, b6, b7)) =>
      Ok [ Byte.of_bits (b7, (b6, (b5, (b4, (b3, (b2, (b1, 0))))))) ]
  | (0, (0, 0, 0, 0), (0, 0, 0, 0), (0, b1, b2, b3), (b4, b5, b6, b7), (b8, b9, b10, b11)) =>
      Ok [ Byte.of_bits (b5,  (b4,  (b3, (b2, (b1, (0,  (1, 1)))))));
           Byte.of_bits (b11, (b10, (b9, (b8, (b7, (b6, (0, 1))))))) ]
  | (0, (0, 0, 0, 0), (1, 1, 0, 1), (1, b6, b7, b8), (b9, b10, b11, b12), (b13, b14, b15, b16)) =>
      Err (IllegalSurrogatePair c)
  | (0, (0, 0, 0, 0), (b1, b2, b3, b4), (b5, b6, b7, b8), (b9, b10, b11, b12), (b13, b14, b15, b16)) =>
      Ok [ Byte.of_bits (b4,  (b3,  (b2,  (b1,  (0,   (1,   (1, 1)))))));
           Byte.of_bits (b10, (b9,  (b8,  (b7,  (b6,  (b5,  (0, 1)))))));
           Byte.of_bits (b16, (b15, (b14, (b13, (b12, (b11, (0, 1)))))))]
  | (0, (b2, b3, b4, b5), (b6, b7, b8, b9), (b10, b11, b12, b13), (b14, b15, b16, b17), (b18, b19, b20, b21)) =>
      Ok [ Byte.of_bits (b3,  (b2,  (0,   (0,   (1,   (1,   (1, 1)))))));
           Byte.of_bits (b9,  (b8,  (b7,  (b6,  (b5,  (b4,  (0, 1)))))));
           Byte.of_bits (b15, (b14, (b13, (b12, (b11, (b10, (0, 1)))))));
           Byte.of_bits (b21, (b20, (b19, (b18, (b17, (b16, (0, 1))))))) ]
  | (1, (0, 0, 0, 0), (b6, b7, b8, b9), (b10, b11, b12, b13), (b14, b15, b16, b17), (b18, b19, b20, b21)) =>
      Ok [ Byte.of_bits (0,   (0,   (1,   (0,   (1,   (1,   (1, 1)))))));
           Byte.of_bits (b9,  (b8,  (b7,  (b6,  (0,   (0,   (0, 1)))))));
           Byte.of_bits (b15, (b14, (b13, (b12, (b11, (b10, (0, 1)))))));
           Byte.of_bits (b21, (b20, (b19, (b18, (b17, (b16, (0, 1))))))) ]
  | _ => Err (EncodingCodepointTooBig c)
  end.

Fixpoint utf8_encode (unicode: unicode_str) : @result ((list byte) * (list codepoint)) (@error unicode_encode_error) :=
  match unicode with
  | [] => Ok ([], [])
  | code :: unicode_rest =>
      let bytes := utf8_encode_codepoint code in
      match bytes with
      | Err err => Err (Error err)
      | Ok bytes => 
          let* (bytes_rest, unicode_rest) := utf8_encode unicode_rest in
          Ok (bytes ++ bytes_rest, unicode_rest)
      end
  end.
