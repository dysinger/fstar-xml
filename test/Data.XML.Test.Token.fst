(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)

(**
Data.XML.Test.Token — unit tests for [Data.XML.Token].

Re-states the entity-reference roundtrips ([lemma_entity_*_roundtrip]) and
the [entity_ref] [one_of]-based choice roundtrip as public test bindings, so
the Integration module can mechanically enforce their presence
(CODE_GUIDELINES §Integration test pattern).

@header Data.XML.Test.Token
*)
module Data.XML.Test.Token

open Data.XML.Token
open Data.Text.Codec.UTF8
open Data.Text.Codec.UTF8String
open Data.Codec
open FStar.Seq
open FStar.Char

(** [&amp;] roundtrips to byte [&] (0x26), consuming 5 bytes. *)
let test_entity_amp () : Lemma
  (ensures entity_amp.dec (entity_amp.enc 0x26uy) == Inr (0x26uy, 5))
  = lemma_entity_amp_roundtrip ()

(** [&lt;] roundtrips to byte [<] (0x3C), consuming 4 bytes. *)
let test_entity_lt () : Lemma
  (ensures entity_lt.dec (entity_lt.enc 0x3Cuy) == Inr (0x3Cuy, 4))
  = lemma_entity_lt_roundtrip ()

(** [&gt;] roundtrips to byte [>] (0x3E), consuming 4 bytes. *)
let test_entity_gt () : Lemma
  (ensures entity_gt.dec (entity_gt.enc 0x3Euy) == Inr (0x3Euy, 4))
  = lemma_entity_gt_roundtrip ()

(** [&quot;] roundtrips to byte ["] (0x22), consuming 6 bytes. *)
let test_entity_quot () : Lemma
  (ensures entity_quot.dec (entity_quot.enc 0x22uy) == Inr (0x22uy, 6))
  = lemma_entity_quot_roundtrip ()

(** [&apos;] roundtrips to byte ['] (0x27), consuming 6 bytes. *)
let test_entity_apos () : Lemma
  (ensures entity_apos.dec (entity_apos.enc 0x27uy) == Inr (0x27uy, 6))
  = lemma_entity_apos_roundtrip ()

(** The full [entity_ref] choice roundtrips for every entity value. *)
let test_entity_ref_amp (r: byte_seq) : Lemma
  (requires entity_wfcv 0x26uy)
  (ensures entity_dec (entity_enc 0x26uy `Seq.append` r) == Inr (0x26uy, 5))
  = lemma_entity_ref_roundtrip 0x26uy r

(** [entity_ref] roundtrip for [<] (0x3C). *)
let test_entity_ref_lt (r: byte_seq) : Lemma
  (requires entity_wfcv 0x3Cuy)
  (ensures entity_dec (entity_enc 0x3Cuy `Seq.append` r) == Inr (0x3Cuy, 4))
  = lemma_entity_ref_roundtrip 0x3Cuy r

(** [entity_ref] roundtrip for [>] (0x3E). *)
let test_entity_ref_gt (r: byte_seq) : Lemma
  (requires entity_wfcv 0x3Euy)
  (ensures entity_dec (entity_enc 0x3Euy `Seq.append` r) == Inr (0x3Euy, 4))
  = lemma_entity_ref_roundtrip 0x3Euy r

(** [entity_ref] roundtrip for ["] (0x22). *)
let test_entity_ref_quot (r: byte_seq) : Lemma
  (requires entity_wfcv 0x22uy)
  (ensures entity_dec (entity_enc 0x22uy `Seq.append` r) == Inr (0x22uy, 6))
  = lemma_entity_ref_roundtrip 0x22uy r

(** [entity_ref] roundtrip for ['] (0x27). *)
let test_entity_ref_apos (r: byte_seq) : Lemma
  (requires entity_wfcv 0x27uy)
  (ensures entity_dec (entity_enc 0x27uy `Seq.append` r) == Inr (0x27uy, 6))
  = lemma_entity_ref_roundtrip 0x27uy r

(** Decimal character reference [&#65;] roundtrips to [A]. *)
let test_char_ref_decimal_roundtrip () : Lemma
  (ensures char_ref_decimal.dec (char_ref_decimal.enc 'A')
           == Inr ('A', Seq.length (char_ref_decimal.enc 'A')))
  = lemma_char_ref_decimal_roundtrip ()

(** Hexadecimal character reference [&#x41;] roundtrips to [A]. *)
let test_char_ref_hex_roundtrip () : Lemma
  (ensures char_ref_hex.dec (char_ref_hex.enc 'A')
           == Inr ('A', Seq.length (char_ref_hex.enc 'A')))
  = lemma_char_ref_hex_roundtrip ()

(** A surrogate code point (U+D800) is rejected at the [mk_char] gate. *)
let test_char_ref_reject_surrogate () : Lemma
  (ensures is_valid_cp 55296 == false /\ mk_char 55296 == None)
  = lemma_char_ref_reject_surrogate ()

(** An above-max code point (U+110000) is rejected at the [mk_char] gate. *)
let test_char_ref_reject_above_max () : Lemma
  (ensures is_valid_cp 1114112 == false /\ mk_char 1114112 == None)
  = lemma_char_ref_reject_above_max ()

(** [char_ref] roundtrips [&#65;] to [A] (concrete vector, §47 path (b)). *)
let test_char_ref_roundtrip () : Lemma
  (ensures char_ref.dec (char_ref.enc 'A') == Inr ('A', Seq.length (char_ref.enc 'A')))
  = lemma_char_ref_roundtrip ()

(** [char_ref] rejects a truncated reference (["&#"] with no digits). *)
let test_char_ref_reject_truncated () : Lemma
  (ensures (match char_ref.dec (seq_of_list [0x26uy;0x23uy]) with
            | Inl _ -> True | Inr _ -> False))
  = ()

(** [text_char] roundtrips a literal [A] (concrete vector). *)
let test_text_char_roundtrip () : Lemma
  (ensures text_char.dec (text_char.enc 'A') == Inr ('A', Seq.length (text_char.enc 'A')))
  = lemma_text_char_roundtrip ()

(** [text_char] decodes a literal [A] to [A], consuming 1 byte. *)
let test_text_char_literal () : Lemma
  (ensures text_char.dec (seq_of_list [0x41uy]) == Inr ('A', 1))
  = ()

(** [text_char] rejects a bare [<] (not a text literal). *)
let test_text_char_reject_lt () : Lemma
  (ensures (match text_char.dec (seq_of_list [0x3Cuy]) with
            | Inl _ -> True | Inr _ -> False))
  = ()

(** Name — non-ASCII acceptance (Task 5.2): [é] (U+00E9) is a NameStartChar. *)
let test_name_accepts_nonascii () : Lemma
  (ensures is_name_start_char (FStar.Char.char_of_int 0xE9))
  = lemma_name_accepts_nonascii ()

(** Name rejection (finding M1 / task 2.1): the empty string is not a Name. *)
let test_name_reject_empty () : Lemma (is_name_string "" == false) =
  lemma_name_reject_empty ()

(** Name rejection: a leading digit is not a NameStartChar. *)
let test_name_reject_leading_digit () : Lemma (is_name_string "1abc" == false) =
  lemma_name_reject_leading_digit ()

(** Name rejection: an interior space is not a NameChar. *)
let test_name_reject_interior_space () : Lemma (is_name_string "a b" == false) =
  lemma_name_reject_interior_space ()

(** PI-target accept: [pi] is a valid target (finding P1). *)
let test_pi_target_accept_pi () : Lemma (is_pi_target "pi" == true) =
  lemma_pi_target_accept_pi ()

(** PI-target reject: [xml] (lowercase) is the reserved target. *)
let test_pi_target_reject_xml () : Lemma (is_pi_target "xml" == false) =
  lemma_pi_target_reject_xml ()

(** PI-target reject: [XML] (uppercase) is the reserved target. *)
let test_pi_target_reject_XML () : Lemma (is_pi_target "XML" == false) =
  lemma_pi_target_reject_XML ()

(** PI-target reject: [Xml] (mixed) is the reserved target. *)
let test_pi_target_reject_Xml () : Lemma (is_pi_target "Xml" == false) =
  lemma_pi_target_reject_Xml ()

(** PI-target reject: [xMl] (mixed) is the reserved target. *)
let test_pi_target_reject_xMl () : Lemma (is_pi_target "xMl" == false) =
  lemma_pi_target_reject_xMl ()

(** PI-target reject: [xmL] (mixed) is the reserved target. *)
let test_pi_target_reject_xmL () : Lemma (is_pi_target "xmL" == false) =
  lemma_pi_target_reject_xmL ()

(** PI-target reject: [xML] (mixed) is the reserved target. *)
let test_pi_target_reject_xML () : Lemma (is_pi_target "xML" == false) =
  lemma_pi_target_reject_xML ()

(** PI-target reject: [XmL] (mixed) is the reserved target. *)
let test_pi_target_reject_XmL () : Lemma (is_pi_target "XmL" == false) =
  lemma_pi_target_reject_XmL ()

(** PI-target reject: [XMl] (mixed) is the reserved target. *)
let test_pi_target_reject_XMl () : Lemma (is_pi_target "XMl" == false) =
  lemma_pi_target_reject_XMl ()

(** Char-ref rejection (task 2.3): [&#65] (missing [;]) is rejected. *)
let test_char_ref_reject_missing_semi () : Lemma
  ((match char_ref.dec (seq_of_list [0x26uy; 0x23uy; 0x36uy; 0x35uy]) with
    | Inl _ -> true | Inr _ -> false) == true) =
  lemma_char_ref_reject_missing_semi ()

(** Char-ref rejection (task 2.3): [&#x] (empty hex) is rejected. *)
let test_char_ref_reject_empty_hex () : Lemma
  ((match char_ref.dec (seq_of_list [0x26uy; 0x23uy; 0x78uy]) with
    | Inl _ -> true | Inr _ -> false) == true) =
  lemma_char_ref_reject_empty_hex ()

(** Name — non-ASCII roundtrip through the [utf8_string] layer. *)
let test_name_nonascii_roundtrip () : Lemma
  (ensures
    utf8_string_dec xml_max_name_len
      (utf8_string_enc "é" `Seq.append` Seq.empty)
      == Inr ("é", Seq.length (utf8_string_enc "é")))
  = lemma_name_nonascii_roundtrip ()

(** [is_xml_char] accept vectors (finding M1 / task 1.3). *)

(** [is_xml_char] accepts TAB (#x9). *)
let test_is_xml_char_tab () : Lemma
  (ensures is_xml_char (FStar.Char.char_of_int 0x9)) = lemma_is_xml_char_tab ()

(** [is_xml_char] accepts LF (#xA). *)
let test_is_xml_char_lf () : Lemma
  (ensures is_xml_char (FStar.Char.char_of_int 0xA)) = lemma_is_xml_char_lf ()

(** [is_xml_char] accepts CR (#xD). *)
let test_is_xml_char_cr () : Lemma
  (ensures is_xml_char (FStar.Char.char_of_int 0xD)) = lemma_is_xml_char_cr ()

(** [is_xml_char] accepts [A] (U+0041). *)
let test_is_xml_char_a () : Lemma
  (ensures is_xml_char 'A') = lemma_is_xml_char_a ()

(** [is_xml_char] reject vectors (finding M1 / task 1.4). *)

(** [is_xml_char] rejects the control #x1. *)
let test_is_xml_char_reject_1 () : Lemma
  (ensures is_xml_char (FStar.Char.char_of_int 0x1) == false) = lemma_is_xml_char_reject_1 ()

(** [is_xml_char] rejects the control #x8. *)
let test_is_xml_char_reject_8 () : Lemma
  (ensures is_xml_char (FStar.Char.char_of_int 0x8) == false) = lemma_is_xml_char_reject_8 ()

(** [is_xml_char] rejects the control #xB. *)
let test_is_xml_char_reject_b () : Lemma
  (ensures is_xml_char (FStar.Char.char_of_int 0xB) == false) = lemma_is_xml_char_reject_b ()

(** [is_xml_char] rejects the control #xC. *)
let test_is_xml_char_reject_c () : Lemma
  (ensures is_xml_char (FStar.Char.char_of_int 0xC) == false) = lemma_is_xml_char_reject_c ()

(** [is_xml_char] rejects the control #xE. *)
let test_is_xml_char_reject_e () : Lemma
  (ensures is_xml_char (FStar.Char.char_of_int 0xE) == false) = lemma_is_xml_char_reject_e ()

(** [is_xml_char] rejects the noncharacter #xFFFE. *)
let test_is_xml_char_reject_fffe () : Lemma
  (ensures is_xml_char (FStar.Char.char_of_int 0xFFFE) == false) = lemma_is_xml_char_reject_fffe ()

(** [is_xml_char] rejects the noncharacter #xFFFF. *)
let test_is_xml_char_reject_ffff () : Lemma
  (ensures is_xml_char (FStar.Char.char_of_int 0xFFFF) == false) = lemma_is_xml_char_reject_ffff ()

(** [is_xml_char] rejects the surrogate U+D800 (at the code-point level). *)
let test_is_xml_char_reject_surrogate () : Lemma
  (ensures is_xml_cp 0xD800 == false) = lemma_is_xml_char_reject_surrogate ()

(** WIRING rejection lemmas (finding M1): the REC [2] exclusion is enforced
    by the character-level codecs' [.dec]. *)

(** [text_char] rejects a control byte (#x1) on the literal path. *)
let test_text_char_reject_control () : Lemma
  (ensures (match text_char.dec (seq_of_list [0x01uy]) with
            | Inl _ -> True | Inr _ -> False)) = lemma_text_char_reject_control ()

(** [literal_char] rejects a control byte (#x1) at the [satisfy] gate. *)
let test_literal_char_reject_control () : Lemma
  (ensures (match literal_char.dec (seq_of_list [0x01uy]) with
            | Inl _ -> True | Inr _ -> False)) = lemma_literal_char_reject_control ()

(** [char_ref] rejects a decimal control reference ([&#1;]). *)
let test_char_ref_reject_control () : Lemma
  (ensures (match char_ref.dec (seq_of_list [0x26uy; 0x23uy; 0x31uy; 0x3Buy]) with
            | Inl _ -> True | Inr _ -> False)) = lemma_char_ref_reject_control ()

(** A noncharacter ([#xFFFE]/[#xFFFF]) is rejected at the [mk_xml_char] gate. *)
let test_char_ref_reject_noncharacter () : Lemma
  (ensures is_xml_cp 0xFFFE == false /\ is_xml_cp 0xFFFF == false /\
           mk_xml_char 0xFFFE == None /\ mk_xml_char 0xFFFF == None)
  = lemma_char_ref_reject_noncharacter ()
