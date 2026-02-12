From Coq Require Import Lists.List.
From Coq Require Import Hexadecimal.
From Coq Require Import ZArith.BinInt.
Import ListNotations.

Open Scope Z_scope.

Definition codepoint : Type := Z.
Definition byte : Type := Z.

Definition byte_str : Type := list byte.

Definition bytes_compare := List.list_compare Z.compare.

Definition codepoint_less_than_10ffff (code: codepoint) : Prop :=
  (code <= 0x10ffff).

Definition codepoint_is_not_surrogate (code: codepoint) : Prop :=
  (code < 0xd800) \/ (code > 0xdfff).

Definition codepoint_not_negative (code: codepoint): Prop :=
  (code >= 0).

Definition valid_codepoint (code: codepoint) :=
  codepoint_less_than_10ffff code
  /\ codepoint_is_not_surrogate code
  /\ codepoint_not_negative code.

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

(* Se a gente considerasse apenas `encode_single : codepoint -> option byte_str`
   e `decode_single : byte_str -> option codepoint`, morfismos parciais
   ordenados entre `valid_codepoint` e `valid_codepoint_representation`, ficaria
   mais tranquilo entender o que está acontecendo. Esses dois sub-ensembles são
   finitos e têm o mesmo tamanho, o que significa que existe um único
   isomorfismo parcial ordenado entre eles. A especificação inteira seria dizer
   que o `encoder_single` mapeia `valid_codepoint` em
   `valid_codepoint_representation` e `decode_single` faz o oposto. No entanto
   não é assim... *)

Definition unicode_str : Type := list codepoint.

Definition codepoints_compare : unicode_str -> unicode_str -> comparison :=
  List.list_compare Z.compare.

Definition valid_codepoints (codes: list codepoint) : Prop :=
  Forall valid_codepoint codes.

Inductive valid_utf8_bytes: list Z ->  Prop :=
| Utf8Nil : valid_utf8_bytes []
| Utf8Concat (bytes tail: list Z) :
    valid_codepoint_representation bytes ->
    valid_utf8_bytes tail ->
    valid_utf8_bytes (bytes ++ tail).

(* Dando mais um passo em direção a especificação completa precisamos considerar
   encode_simple : unicode_str -> option byte_str
   decode_simple : byte_str -> option unicode_str
   que tencionam mapear valid_codepoints em valid_utf8_bytes e vice-versa. Agora
   não podemos simplemente falar que este é um isomorfismo parcial ordenado.
   Precisamos falar que `encode_simple` é um morfismo de monoides e que o
   `decode_simple` é o conceito dual. Para que consigamos retornar ao nível de
   abstração anterior vamos usar o fato de que `valid_codepoint_representation`
   é um código prefixo. *)

Definition encoder_type := unicode_str -> byte_str * unicode_str.
Definition decoder_type := byte_str -> unicode_str * byte_str.

Inductive unicode_decode_error :=
| OverlongEncoding
| InvalidSurrogatePair
| CodepointTooBig
| InvalidContinuationHeader (x: option Byte.byte)
| InvalidStartHeader (x: option Byte.byte).

Inductive unicode_encode_error :=
| EncodingCodepointTooBig (c: codepoint)
| IllegalSurrogatePair (c: codepoint).

Definition prefix {X} (p : list X) (l : list X) :=
  l = p ++ skipn (length p) l.

Definition no_prefix {X} (valid : list X -> Prop) (l : list X) :=
  forall (p : list X),
    prefix p l ->
    (p = [] \/ ~ (valid p)).

(* Por fim, precisamos dar mais informação sobre o erro que aconteceu no retorno
   da função. Aqui a ideia é que processamos o máximo possível da input. Ou
   seja, não é só que o sufixo rejeitado não é válido, todo prefixo não-trivial
   dos rejeitos é inválido. *)

Definition maximal_prefix {X} (P : list X -> Prop) (p l : list X) : Prop :=
  (P p)
  /\ (forall lesser,
      prefix lesser l ->
      P lesser ->
      prefix lesser p).

Definition encoder_error_suffix (encoder: encoder_type) :=
  forall codes bytes rest,
    encoder codes = (bytes, rest) ->
    exists valid_prefix,
      codes = valid_prefix ++ rest
      /\ (maximal_prefix valid_codepoints valid_prefix codes)
      /\ fst (encoder valid_prefix) = bytes.

(* `valid_codepoints code` se e somente se rest = [] *)

Definition encoder_monoid_morphism (encoder : encoder_type) :=
  forall codes0 codes1,
    valid_codepoints codes0 ->
    valid_codepoints codes1 ->
    fst (encoder (codes0 ++ codes1)) = fst (encoder codes0) ++ fst (encoder codes1).

Definition encoder_output_single (encoder : encoder_type) :=
  forall code bytes,
    valid_codepoint code ->
    encoder [code] = (bytes, []) ->
    valid_codepoint_representation bytes.

Definition encoder_strictly_increasing (encoder: encoder_type) :=
  forall code0 code1 bytes0 bytes1,
    encoder [code0] = (bytes0, []) ->
    encoder [code1] = (bytes1, []) ->
    Z.compare code0 code1 = bytes_compare bytes0 bytes1.

Record utf8_encoder_spec encoder := {
    enc_error : encoder_error_suffix encoder;
    enc_morphism : encoder_monoid_morphism encoder;
    enc_output : encoder_output_single encoder;
    enc_increasing : encoder_strictly_increasing encoder;
  }.

Definition decoder_error_suffix (decoder : decoder_type) :=
  forall bytes codes rest,
    decoder bytes = (codes, rest) ->
    exists valid_prefix,
    bytes = valid_prefix ++ rest
    /\ decoder valid_prefix = (codes, [])
    /\ no_prefix valid_utf8_bytes rest.

Definition decoder_dual_monoid_morphism (decoder : decoder_type) :=
  forall bytes codes_prefix codes_suffix,
    decoder bytes = (codes_prefix ++ codes_suffix, []) ->
    exists bytes_prefix bytes_suffix,
      (bytes = bytes_prefix ++ bytes_suffix)
      /\ (decoder bytes_prefix = (codes_prefix, []))
      /\ (decoder bytes_suffix = (codes_suffix, [])).

Definition decoder_output_single (decoder : decoder_type) :=
  forall bytes,
  valid_codepoint_representation bytes ->
  exists code,
    decoder bytes = ([code], [])
    /\ valid_codepoint code.

Definition decoder_strictly_increasing (decoder : decoder_type) :=
  forall bytes0 bytes1 code0 code1,
    decoder bytes0 = ([code0], nil) ->
    decoder bytes1 = ([code1], nil) ->
    bytes_compare bytes0 bytes1 = Z.compare code0 code1.

Record utf8_decoder_spec decoder := {
    dec_error : decoder_error_suffix decoder;
    dec_morphism : decoder_dual_monoid_morphism decoder;
    dec_output : decoder_output_single decoder;
    dec_increasing : decoder_strictly_increasing decoder;
  }.

Record utf8_spec encoder decoder := {
    encoder_spec_compliant : utf8_encoder_spec encoder;
    decoder_spec_compliant : utf8_decoder_spec decoder;
  }.
