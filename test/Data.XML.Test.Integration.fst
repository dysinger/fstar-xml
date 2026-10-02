(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)


(**
Data.XML.Test.Integration — integration test for the [xml] package.

Opens all test modules and binds every test/lemma function by name, so
deleting or renaming any function breaks verification (CODE_GUIDELINES
§Integration test pattern).  Uses [--admit_smt_queries true] because the
bindings are SMT-integration anchors, not security proofs.

@header Data.XML.Test.Integration
*)
module Data.XML.Test.Integration


open Data.XML.Token
open Data.XML.Codec
open Data.XML.Codec.Wrapped
open Data.XML.Types
open Data.XML.Pulse
open Data.XML.Types.Pulse
open Data.Codec


#push-options "--admit_smt_queries true"


(** Pulse tag codec bindings (the mechanical gate — every public symbol of
    [Data.XML.Pulse] and [Data.XML.Types.Pulse] bound by name, so deleting or
    renaming any Pulse lemma/function breaks verification; the [xml-pulse]
    spec's central requirement). *)


(** [Data.XML.Pulse] — pure tag spec roundtrip + bridge lemmas. *)
(** [Data.XML.Pulse.tag_of] *)
let _test_xml_pulse_tag_types : Data.XML.Pulse.xml_token -> FStar.UInt8.t = Data.XML.Pulse.tag_of
(** [Data.XML.Pulse.tag_to_type] *)
let _test_xml_pulse_tag_to_type : FStar.UInt8.t -> option Data.XML.Pulse.xml_token =
  Data.XML.Pulse.tag_to_type
(** [Data.XML.Pulse.lemma_roundtrip] *)
let _test_xml_pulse_lemma_roundtrip = Data.XML.Pulse.lemma_roundtrip
(** [Data.XML.Pulse.encode] *)
let _test_xml_pulse_encode = Data.XML.Pulse.encode
(** [Data.XML.Pulse.decode] *)
let _test_xml_pulse_decode = Data.XML.Pulse.decode
(** [Data.XML.Pulse.lemma_pulse_roundtrip] *)
let _test_xml_pulse_lemma_pulse_roundtrip = Data.XML.Pulse.lemma_pulse_roundtrip
(** [Data.XML.Pulse.lemma_pulse_encode_decode_match] *)
let _test_xml_pulse_lemma_pulse_encode_decode_match = Data.XML.Pulse.lemma_pulse_encode_decode_match


(** [Data.XML.Types.Pulse] — pure tag spec roundtrip + bridge lemmas. *)
(** [Data.XML.Types.Pulse.tag_of] *)
let _test_xml_types_pulse_tag_of : Data.XML.Types.Pulse.xml_node -> FStar.UInt8.t =
  Data.XML.Types.Pulse.tag_of
(** [Data.XML.Types.Pulse.tag_to_type] *)
let _test_xml_types_pulse_tag_to_type : FStar.UInt8.t -> option Data.XML.Types.Pulse.xml_node =
  Data.XML.Types.Pulse.tag_to_type
(** [Data.XML.Types.Pulse.lemma_roundtrip] *)
let _test_xml_types_pulse_lemma_roundtrip = Data.XML.Types.Pulse.lemma_roundtrip
(** [Data.XML.Types.Pulse.encode] *)
let _test_xml_types_pulse_encode = Data.XML.Types.Pulse.encode
(** [Data.XML.Types.Pulse.decode] *)
let _test_xml_types_pulse_decode = Data.XML.Types.Pulse.decode
(** [Data.XML.Types.Pulse.lemma_pulse_roundtrip] *)
let _test_xml_types_pulse_lemma_pulse_roundtrip = Data.XML.Types.Pulse.lemma_pulse_roundtrip
(** [Data.XML.Types.Pulse.lemma_pulse_encode_decode_match] *)
let _test_xml_types_pulse_lemma_pulse_encode_decode_match = Data.XML.Types.Pulse.lemma_pulse_encode_decode_match


(** Token entity roundtrips. *)
(** [Data.XML.Test.Token.test_entity_amp] *)
let _test_entity_amp = Data.XML.Test.Token.test_entity_amp
(** [Data.XML.Test.Token.test_entity_lt] *)
let _test_entity_lt = Data.XML.Test.Token.test_entity_lt
(** [Data.XML.Test.Token.test_entity_gt] *)
let _test_entity_gt = Data.XML.Test.Token.test_entity_gt
(** [Data.XML.Test.Token.test_entity_quot] *)
let _test_entity_quot = Data.XML.Test.Token.test_entity_quot
(** [Data.XML.Test.Token.test_entity_apos] *)
let _test_entity_apos = Data.XML.Test.Token.test_entity_apos
(** [Data.XML.Test.Token.test_entity_ref_amp] *)
let _test_entity_ref_amp = Data.XML.Test.Token.test_entity_ref_amp
(** [Data.XML.Test.Token.test_entity_ref_lt] *)
let _test_entity_ref_lt = Data.XML.Test.Token.test_entity_ref_lt
(** [Data.XML.Test.Token.test_entity_ref_gt] *)
let _test_entity_ref_gt = Data.XML.Test.Token.test_entity_ref_gt
(** [Data.XML.Test.Token.test_entity_ref_quot] *)
let _test_entity_ref_quot = Data.XML.Test.Token.test_entity_ref_quot
(** [Data.XML.Test.Token.test_entity_ref_apos] *)
let _test_entity_ref_apos = Data.XML.Test.Token.test_entity_ref_apos


(** Character-reference roundtrips + rejections. *)
(** [Data.XML.Test.Token.test_char_ref_decimal_roundtrip] *)
let _test_char_ref_decimal = Data.XML.Test.Token.test_char_ref_decimal_roundtrip
(** [Data.XML.Test.Token.test_char_ref_hex_roundtrip] *)
let _test_char_ref_hex = Data.XML.Test.Token.test_char_ref_hex_roundtrip
(** [Data.XML.Test.Token.test_char_ref_reject_surrogate] *)
let _test_char_ref_reject_surrogate = Data.XML.Test.Token.test_char_ref_reject_surrogate
(** [Data.XML.Test.Token.test_char_ref_reject_above_max] *)
let _test_char_ref_reject_above_max = Data.XML.Test.Token.test_char_ref_reject_above_max


(** [char_ref] + [text_char] roundtrips + rejections. *)
(** [Data.XML.Test.Token.test_char_ref_roundtrip] *)
let _test_char_ref_roundtrip = Data.XML.Test.Token.test_char_ref_roundtrip
(** [Data.XML.Test.Token.test_char_ref_reject_truncated] *)
let _test_char_ref_reject_truncated = Data.XML.Test.Token.test_char_ref_reject_truncated
(** [Data.XML.Test.Token.test_text_char_roundtrip] *)
let _test_text_char_roundtrip = Data.XML.Test.Token.test_text_char_roundtrip
(** [Data.XML.Test.Token.test_text_char_literal] *)
let _test_text_char_literal = Data.XML.Test.Token.test_text_char_literal
(** [Data.XML.Test.Token.test_text_char_reject_lt] *)
let _test_text_char_reject_lt = Data.XML.Test.Token.test_text_char_reject_lt


(** Name — non-ASCII acceptance + roundtrip (Task 5.2). *)
(** [Data.XML.Test.Token.test_name_accepts_nonascii] *)
let _test_name_accepts_nonascii = Data.XML.Test.Token.test_name_accepts_nonascii
(** [Data.XML.Test.Token.test_name_nonascii_roundtrip] *)
let _test_name_nonascii_roundtrip = Data.XML.Test.Token.test_name_nonascii_roundtrip


(** Name rejection lemmas (M1 / task 2.1). *)
(** [Data.XML.Test.Token.test_name_reject_empty] *)
let _test_name_reject_empty = Data.XML.Test.Token.test_name_reject_empty
(** [Data.XML.Test.Token.test_name_reject_leading_digit] *)
let _test_name_reject_leading_digit = Data.XML.Test.Token.test_name_reject_leading_digit
(** [Data.XML.Test.Token.test_name_reject_interior_space] *)
let _test_name_reject_interior_space = Data.XML.Test.Token.test_name_reject_interior_space


(** PI-target accept/reject lemmas (finding P1 / REC [17]). *)
(** [Data.XML.Test.Token.test_pi_target_accept_pi] *)
let _test_pi_target_accept_pi = Data.XML.Test.Token.test_pi_target_accept_pi
(** [Data.XML.Test.Token.test_pi_target_reject_xml] *)
let _test_pi_target_reject_xml = Data.XML.Test.Token.test_pi_target_reject_xml
(** [Data.XML.Test.Token.test_pi_target_reject_XML] *)
let _test_pi_target_reject_XML = Data.XML.Test.Token.test_pi_target_reject_XML
(** [Data.XML.Test.Token.test_pi_target_reject_Xml] *)
let _test_pi_target_reject_Xml = Data.XML.Test.Token.test_pi_target_reject_Xml
(** [Data.XML.Test.Token.test_pi_target_reject_xMl] *)
let _test_pi_target_reject_xMl = Data.XML.Test.Token.test_pi_target_reject_xMl
(** [Data.XML.Test.Token.test_pi_target_reject_xmL] *)
let _test_pi_target_reject_xmL = Data.XML.Test.Token.test_pi_target_reject_xmL
(** [Data.XML.Test.Token.test_pi_target_reject_xML] *)
let _test_pi_target_reject_xML = Data.XML.Test.Token.test_pi_target_reject_xML
(** [Data.XML.Test.Token.test_pi_target_reject_XmL] *)
let _test_pi_target_reject_XmL = Data.XML.Test.Token.test_pi_target_reject_XmL
(** [Data.XML.Test.Token.test_pi_target_reject_XMl] *)
let _test_pi_target_reject_XMl = Data.XML.Test.Token.test_pi_target_reject_XMl


(** Char-ref truncation rejection lemmas (M4 / task 2.3). *)
(** [Data.XML.Test.Token.test_char_ref_reject_missing_semi] *)
let _test_char_ref_reject_missing_semi = Data.XML.Test.Token.test_char_ref_reject_missing_semi
(** [Data.XML.Test.Token.test_char_ref_reject_empty_hex] *)
let _test_char_ref_reject_empty_hex = Data.XML.Test.Token.test_char_ref_reject_empty_hex


(** [is_xml_char] accept + reject vectors + WIRING rejection (finding M1). *)
(** [Data.XML.Test.Token.test_is_xml_char_tab] *)
let _test_is_xml_char_tab = Data.XML.Test.Token.test_is_xml_char_tab
(** [Data.XML.Test.Token.test_is_xml_char_lf] *)
let _test_is_xml_char_lf = Data.XML.Test.Token.test_is_xml_char_lf
(** [Data.XML.Test.Token.test_is_xml_char_cr] *)
let _test_is_xml_char_cr = Data.XML.Test.Token.test_is_xml_char_cr
(** [Data.XML.Test.Token.test_is_xml_char_a] *)
let _test_is_xml_char_a = Data.XML.Test.Token.test_is_xml_char_a
(** [Data.XML.Test.Token.test_is_xml_char_reject_1] *)
let _test_is_xml_char_reject_1 = Data.XML.Test.Token.test_is_xml_char_reject_1
(** [Data.XML.Test.Token.test_is_xml_char_reject_8] *)
let _test_is_xml_char_reject_8 = Data.XML.Test.Token.test_is_xml_char_reject_8
(** [Data.XML.Test.Token.test_is_xml_char_reject_b] *)
let _test_is_xml_char_reject_b = Data.XML.Test.Token.test_is_xml_char_reject_b
(** [Data.XML.Test.Token.test_is_xml_char_reject_c] *)
let _test_is_xml_char_reject_c = Data.XML.Test.Token.test_is_xml_char_reject_c
(** [Data.XML.Test.Token.test_is_xml_char_reject_e] *)
let _test_is_xml_char_reject_e = Data.XML.Test.Token.test_is_xml_char_reject_e
(** [Data.XML.Test.Token.test_is_xml_char_reject_fffe] *)
let _test_is_xml_char_reject_fffe = Data.XML.Test.Token.test_is_xml_char_reject_fffe
(** [Data.XML.Test.Token.test_is_xml_char_reject_ffff] *)
let _test_is_xml_char_reject_ffff = Data.XML.Test.Token.test_is_xml_char_reject_ffff
(** [Data.XML.Test.Token.test_is_xml_char_reject_surrogate] *)
let _test_is_xml_char_reject_surrogate = Data.XML.Test.Token.test_is_xml_char_reject_surrogate
(** [Data.XML.Test.Token.test_text_char_reject_control] *)
let _test_text_char_reject_control = Data.XML.Test.Token.test_text_char_reject_control
(** [Data.XML.Test.Token.test_literal_char_reject_control] *)
let _test_literal_char_reject_control = Data.XML.Test.Token.test_literal_char_reject_control
(** [Data.XML.Test.Token.test_char_ref_reject_control] *)
let _test_char_ref_reject_control = Data.XML.Test.Token.test_char_ref_reject_control
(** [Data.XML.Test.Token.test_char_ref_reject_noncharacter] *)
let _test_char_ref_reject_noncharacter = Data.XML.Test.Token.test_char_ref_reject_noncharacter


(** Codec wrapped-leaf roundtrips. *)
(** [Data.XML.Test.Codec.test_comment_content_roundtrip] *)
let _test_comment_content_roundtrip = Data.XML.Test.Codec.test_comment_content_roundtrip
(** [Data.XML.Test.Codec.test_cdata_content_roundtrip] *)
let _test_cdata_content_roundtrip = Data.XML.Test.Codec.test_cdata_content_roundtrip
(** [Data.XML.Test.Codec.test_pi_content_roundtrip] *)
let _test_pi_content_roundtrip = Data.XML.Test.Codec.test_pi_content_roundtrip
(** [Data.XML.Test.Codec.test_comment_single_dash] *)
let _test_comment_single_dash = Data.XML.Test.Codec.test_comment_single_dash
(** [Data.XML.Test.Codec.test_cdata_single_bracket] *)
let _test_cdata_single_bracket = Data.XML.Test.Codec.test_cdata_single_bracket
(** [Data.XML.Test.Codec.test_pi_single_question] *)
let _test_pi_single_question = Data.XML.Test.Codec.test_pi_single_question
(** [Data.XML.Test.Codec.test_empty_attr_value_roundtrip] *)
let _test_empty_attr_value = Data.XML.Test.Codec.test_empty_attr_value_roundtrip
(** [Data.XML.Test.Codec.test_attr_text_char_reject_control] *)
let _test_attr_text_char_reject_control = Data.XML.Test.Codec.test_attr_text_char_reject_control
(** [Data.XML.Test.Codec.test_comment_reject_double_dash] *)
let _test_comment_reject_double_dash = Data.XML.Test.Codec.test_comment_reject_double_dash
(** [Data.XML.Test.Codec.test_comment_reject_trailing_dash] *)
let _test_comment_reject_trailing_dash = Data.XML.Test.Codec.test_comment_reject_trailing_dash
(** [Data.XML.Test.Codec.test_comment_accept_single_dash] *)
let _test_comment_accept_single_dash = Data.XML.Test.Codec.test_comment_accept_single_dash
(** [Data.XML.Test.Codec.test_cdata_reject_close] *)
let _test_cdata_reject_close = Data.XML.Test.Codec.test_cdata_reject_close
(** [Data.XML.Test.Codec.test_cdata_accept_single_bracket] *)
let _test_cdata_accept_single_bracket = Data.XML.Test.Codec.test_cdata_accept_single_bracket
(** [Data.XML.Test.Codec.test_pi_reject_close] *)
let _test_pi_reject_close = Data.XML.Test.Codec.test_pi_reject_close
(** [Data.XML.Test.Codec.test_pi_accept_single_question] *)
let _test_pi_accept_single_question = Data.XML.Test.Codec.test_pi_accept_single_question


(** CODEC-level content rejection lemmas (M4 / task 2.2). *)
(** [Data.XML.Test.Codec.test_comment_dec_reject_truncated] *)
let _test_comment_dec_reject_truncated = Data.XML.Test.Codec.test_comment_dec_reject_truncated
(** [Data.XML.Test.Codec.test_cdata_dec_reject_truncated] *)
let _test_cdata_dec_reject_truncated = Data.XML.Test.Codec.test_cdata_dec_reject_truncated
(** [Data.XML.Test.Codec.test_pi_dec_reject_truncated] *)
let _test_pi_dec_reject_truncated = Data.XML.Test.Codec.test_pi_dec_reject_truncated


(** Prolog doctype bracket-tracking (byte-level). *)
(** [Data.XML.Test.Prolog.test_doctype_balanced_nested] *)
let _test_doctype_balanced_nested = Data.XML.Test.Prolog.test_doctype_balanced_nested
(** [Data.XML.Test.Prolog.test_doctype_stray_gt_rejected] *)
let _test_doctype_stray_gt_rejected = Data.XML.Test.Prolog.test_doctype_stray_gt_rejected
(** [Data.XML.Test.Prolog.test_doctype_unclosed_bracket_rejected] *)
let _test_doctype_unclosed_bracket_rejected = Data.XML.Test.Prolog.test_doctype_unclosed_bracket_rejected
(** [Data.XML.Test.Prolog.test_doctype_stray_close_bracket_rejected] *)
let _test_doctype_stray_close_bracket_rejected = Data.XML.Test.Prolog.test_doctype_stray_close_bracket_rejected
(** [Data.XML.Test.Prolog.test_doctype_system_literal_close_bracket] *)
let _test_doctype_system_literal_close_bracket = Data.XML.Test.Prolog.test_doctype_system_literal_close_bracket
(** [Data.XML.Test.Prolog.test_doctype_system_literal_open_bracket] *)
let _test_doctype_system_literal_open_bracket = Data.XML.Test.Prolog.test_doctype_system_literal_open_bracket
(** [Data.XML.Test.Prolog.test_doctype_system_literal_gt] *)
let _test_doctype_system_literal_gt = Data.XML.Test.Prolog.test_doctype_system_literal_gt


(** Structural XML declaration char-list predicates + roundtrips (Task 4.2). *)
(** [Data.XML.Test.Prolog.test_version_chars_ok] *)
let _test_version_chars_ok = Data.XML.Test.Prolog.test_version_chars_ok
(** [Data.XML.Test.Prolog.test_version_chars_ok_bad] *)
let _test_version_chars_ok_bad = Data.XML.Test.Prolog.test_version_chars_ok_bad
(** [Data.XML.Test.Prolog.test_encname_chars_ok] *)
let _test_encname_chars_ok = Data.XML.Test.Prolog.test_encname_chars_ok
(** [Data.XML.Test.Prolog.test_xml_decl_scan_roundtrip_10] *)
let _test_xml_decl_scan_roundtrip_10 = Data.XML.Test.Prolog.test_xml_decl_scan_roundtrip_10
(** [Data.XML.Test.Prolog.test_xml_decl_wfcv_full] *)
let _test_xml_decl_wfcv_full = Data.XML.Test.Prolog.test_xml_decl_wfcv_full


(** Doctype envelope + declaration reject/accept lemmas (C1/M2/M5). *)
(** [Data.XML.Test.Prolog.test_doctype_reject_empty] *)
let _test_doctype_reject_empty = Data.XML.Test.Prolog.test_doctype_reject_empty
(** [Data.XML.Test.Prolog.test_doctype_reject_garbage] *)
let _test_doctype_reject_garbage = Data.XML.Test.Prolog.test_doctype_reject_garbage
(** [Data.XML.Test.Prolog.test_doctype_reject_malformed_extid] *)
let _test_doctype_reject_malformed_extid = Data.XML.Test.Prolog.test_doctype_reject_malformed_extid
(** [Data.XML.Test.Prolog.test_doctype_accept_simple] *)
let _test_doctype_accept_simple = Data.XML.Test.Prolog.test_doctype_accept_simple
(** [Data.XML.Test.Prolog.test_doctype_accept_extid] *)
let _test_doctype_accept_extid = Data.XML.Test.Prolog.test_doctype_accept_extid
(** [Data.XML.Test.Prolog.test_xml_decl_reject_empty_version] *)
let _test_xml_decl_reject_empty_version = Data.XML.Test.Prolog.test_xml_decl_reject_empty_version
(** [Data.XML.Test.Prolog.test_xml_decl_reject_multidot_version] *)
let _test_xml_decl_reject_multidot_version = Data.XML.Test.Prolog.test_xml_decl_reject_multidot_version
(** [Data.XML.Test.Prolog.test_decl_reject_empty_encname] *)
let _test_decl_reject_empty_encname = Data.XML.Test.Prolog.test_decl_reject_empty_encname


(** Document/element examples + generic roundtrip (combinator [.roundtrip], 0-admit). *)
(** [Data.XML.Test.Element.test_empty_doc] *)
let _test_empty_doc = Data.XML.Test.Element.test_empty_doc
(** [Data.XML.Test.Element.test_text_doc] *)
let _test_text_doc = Data.XML.Test.Element.test_text_doc
(** [Data.XML.Test.Element.test_nested_doc] *)
let _test_nested_doc = Data.XML.Test.Element.test_nested_doc
(** [Data.XML.Test.Element.test_attr_doc] *)
let _test_attr_doc = Data.XML.Test.Element.test_attr_doc
(** [Data.XML.Test.Element.test_multi_attr_doc] *)
let _test_multi_attr_doc = Data.XML.Test.Element.test_multi_attr_doc
(** [Data.XML.Test.Element.test_comment_doc] *)
let _test_comment_doc = Data.XML.Test.Element.test_comment_doc
(** [Data.XML.Test.Element.test_cdata_doc] *)
let _test_cdata_doc = Data.XML.Test.Element.test_cdata_doc
(** [Data.XML.Test.Element.test_pi_doc] *)
let _test_pi_doc = Data.XML.Test.Element.test_pi_doc
(** [Data.XML.Test.Element.test_decl_doc] *)
let _test_decl_doc = Data.XML.Test.Element.test_decl_doc
(** [Data.XML.Test.Element.test_decl_doctype_doc] *)
let _test_decl_doctype_doc = Data.XML.Test.Element.test_decl_doctype_doc
(** [Data.XML.Test.Element.test_doctype_extid_doc] *)
let _test_doctype_extid_doc = Data.XML.Test.Element.test_doctype_extid_doc
(** [Data.XML.Test.Element.test_refs_nested_doc] *)
let _test_refs_nested_doc = Data.XML.Test.Element.test_refs_nested_doc
(** [Data.XML.Test.Element.test_document_codec_roundtrip] *)
let _test_document_codec_roundtrip = Data.XML.Test.Element.test_document_codec_roundtrip


(** Element mismatch rejection lemmas (m2 / task 3.2). *)
(** [Data.XML.Test.Element.test_element_reject_mismatched_tag] *)
let _test_element_reject_mismatched_tag = Data.XML.Test.Element.test_element_reject_mismatched_tag
(** [Data.XML.Test.Element.test_element_accept_matched_tag] *)
let _test_element_accept_matched_tag = Data.XML.Test.Element.test_element_accept_matched_tag


#pop-options

