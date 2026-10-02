(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)


(**
Data.XML.Test.Prolog — unit tests for [Data.XML.Codec.Prolog].

Re-states the doctype bracket-tracking predicates and scan at the BYTE-list
level (which reduces directly) as public test bindings, so the Integration
module mechanically enforces their presence (CODE_GUIDELINES §Integration
test pattern).  The general doctype roundtrip is proven GENERICALLY by
[lemma_doctype_roundtrip] (0-admit); the concrete-string regression vectors
are deferred (they hit the §47 bounded-computation wall: [doctype_balanced]
over [text_string_to_bytes] of a concrete string does not reduce under
[assert_norm]).

@header Data.XML.Test.Prolog
*)
module Data.XML.Test.Prolog


open Data.XML.Codec.Prolog
open Data.XML.Types
open Data.Codec
open FStar.List.Tot


(** The bracket-tracking scan accepts a nested [..] run (a lone []] and a
    [>] inside the subset are regular bytes). *)
#push-options "--z3rlimit 400"
let test_doctype_balanced_nested () : Lemma
  (doctype_balanced [0x5Buy; 0x3Euy; 0x5Duy; 0x3Euy] 0 None == true)
  = ()
#pop-options


(** A stray top-level [>] mid-token is rejected (a [>] at depth 0 must be
    terminal). *)
#push-options "--z3rlimit 400"
let test_doctype_stray_gt_rejected () : Lemma
  (doctype_balanced [0x3Euy; 0x3Euy] 0 None == false)
  = ()
#pop-options


(** A lone open bracket without a close is rejected (depth never returns to
    zero). *)
#push-options "--z3rlimit 400"
let test_doctype_unclosed_bracket_rejected () : Lemma
  (doctype_balanced [0x5Buy] 0 None == false)
  = ()
#pop-options


(** A stray top-level close bracket is rejected (depth never negative). *)
#push-options "--z3rlimit 400"
let test_doctype_stray_close_bracket_rejected () : Lemma
  (doctype_balanced [0x5Duy; 0x3Euy] 0 None == false)
  = ()
#pop-options


(* ========================================================================
   PITarget / doctype quote-awareness (finding P2).

   The quote-aware [doctype_balanced] no longer counts ['[']/[']'] inside a
   quoted SystemLiteral/PubidLiteral as bracket structure, so a legal
   [<!DOCTYPE a SYSTEM "]">] is ACCEPTED (it was previously a FALSE
   rejection) and the two scans ([doctype_balance] and [doctype_scan_quoted])
   now agree on a bracket-bearing literal.
   ======================================================================== *)


(** A SystemLiteral containing a lone []] at depth 0 is accepted: the quoted
    []] is inert, not an [intSubset] close (finding P2). *)
#push-options "--z3rlimit 400"
let test_doctype_system_literal_close_bracket () : Lemma
  (doctype_balanced [0x22uy; 0x5Duy; 0x22uy; 0x3Euy] 0 None == true)
  = ()
#pop-options


(** A SystemLiteral containing a lone ['['] is accepted: the quoted ['['] is
    inert (finding P2). *)
#push-options "--z3rlimit 400"
let test_doctype_system_literal_open_bracket () : Lemma
  (doctype_balanced [0x22uy; 0x5Buy; 0x22uy; 0x3Euy] 0 None == true)
  = ()
#pop-options


(** A SystemLiteral containing a ['>'] is accepted: the quoted ['>'] is inert,
    not the terminating ['>'] (finding P2). *)
#push-options "--z3rlimit 400"
let test_doctype_system_literal_gt () : Lemma
  (doctype_balanced [0x22uy; 0x3Euy; 0x22uy; 0x3Euy] 0 None == true)
  = ()
#pop-options


(* ========================================================================
   Structural XML declaration — concrete vectors (Task 4.2).

   The STRUCTURAL [xml_decl] view is recovered by the pure parser
   [xml_decl_scan] and rendered by [xml_decl_enc_bytes] over the [list char]
   fields ([decl_version]/[decl_encoding]).  The general symbolic roundtrip
   hits the §65 list-constructor congruence wall, so these CONCRETE vectors
   (closed literals, reduced by [assert_norm]) are the structural
   roundtrip/accept anchors; the codec layer carries the declaration
   OPAQUELY via [xmldecl_text_codec] (0-admit).
   ======================================================================== *)


(** The canonical [version="1.0"] declaration value ([list char] fields). *)
let decl_10 : xml_decl =
  { decl_version = ['1'; '.'; '0']; decl_encoding = None; decl_standalone = None }


(** The [version="1.0"] + [encoding="UTF-8"] + [standalone="yes"] value. *)
let decl_full : xml_decl =
  { decl_version = ['1'; '.'; '0'];
    decl_encoding = Some ['U'; 'T'; 'F'; '-'; '8'];
    decl_standalone = Some true }


(** The version char-list well-formedness predicate accepts [1.0]. *)
#push-options "--z3rlimit 400"
let test_version_chars_ok () : Lemma (version_chars_ok ['1'; '.'; '0'] == true) = ()
#pop-options


(** The version char-list predicate rejects a non-[1.] lead. *)
#push-options "--z3rlimit 400"
let test_version_chars_ok_bad () : Lemma (version_chars_ok ['2'; '.'; '0'] == false) = ()
#pop-options


(** The EncName char-list predicate accepts [UTF-8]. *)
#push-options "--z3rlimit 400"
let test_encname_chars_ok () : Lemma (encname_chars_ok ['U'; 'T'; 'F'; '-'; '8'] == true) = ()
#pop-options


(** The canonical declaration rounds through the structural parser/renderer. *)
#push-options "--z3rlimit 800 --ifuel 8 --fuel 8"
let test_xml_decl_scan_roundtrip_10 () : Lemma
  (xml_decl_scan (xml_decl_enc_bytes decl_10) == Some (decl_10, []))
  = assert_norm (xml_decl_enc_bytes decl_10 ==
      [0x3Cuy;0x3Fuy;0x78uy;0x6Duy;0x6Cuy; (* <?xml *)
       0x20uy; (* S *)
       0x76uy;0x65uy;0x72uy;0x73uy;0x69uy;0x6Fuy;0x6Euy; (* version *)
       0x3Duy;0x22uy; (* =" *)
       0x31uy;0x2Euy;0x30uy; (* 1.0 *)
       0x22uy; (* " *)
       0x3Fuy;0x3Euy]); (* ?> *)
    ()
#pop-options


(** The full declaration (version + encoding + standalone) renders and the
    char-list predicates hold. *)
#push-options "--z3rlimit 400"
let test_xml_decl_wfcv_full () : Lemma (xml_decl_wfcv decl_full == true) = ()
#pop-options


(* ========================================================================
   Doctype envelope + declaration reject/accept lemmas (xml-audit-gaps).
   Re-state the SOURCE lemmas in [Data.XML.Codec.Prolog] so the Integration
   module enforces their presence mechanically. *)


(** [<!DOCTYPE>] — empty doctype name — rejected. *)
let test_doctype_reject_empty () : Lemma (doctype_ok doctype_empty_bytes == false) =
  lemma_doctype_reject_empty ()


(** [<!DOCTYPE <<<<>>>>] — balanced garbage — rejected. *)
let test_doctype_reject_garbage () : Lemma (doctype_ok doctype_garbage_content == false) =
  lemma_doctype_reject_garbage ()


(** [<!DOCTYPE a SYSTEM>] — unterminated ExternalID literal — rejected. *)
let test_doctype_reject_malformed_extid () : Lemma (doctype_ok doctype_malformed_extid_bytes == false) =
  lemma_doctype_reject_malformed_extid ()


(** [<!DOCTYPE a>] — valid simple doctype — envelope accepted. *)
let test_doctype_accept_simple () : Lemma
  ((match doctype_scan_envelope doctype_simple_bytes with Some _ -> true | None -> false) == true) =
  lemma_doctype_accept_simple ()


(** [<!DOCTYPE a SYSTEM "x.dtd">] — ExternalID doctype — envelope accepted. *)
let test_doctype_accept_extid () : Lemma
  ((match doctype_scan_envelope doctype_extid_bytes with Some _ -> true | None -> false) == true) =
  lemma_doctype_accept_extid ()


(** The empty VersionNum digit run ([1.]) is rejected by the char-level gate. *)
let test_xml_decl_reject_empty_version () : Lemma (version_chars_ok ['1'; '.'] == false) =
  lemma_xml_decl_reject_empty_version ()


(** The multi-dot version ([1.0.0]) is rejected by the char-level gate. *)
let test_xml_decl_reject_multidot_version () : Lemma
  (version_chars_ok ['1'; '.'; '0'; '.'; '0'] == false) =
  lemma_xml_decl_reject_multidot_version ()


(** The empty EncName is rejected by the char-level gate. *)
let test_decl_reject_empty_encname () : Lemma (encname_chars_ok [] == false) =
  lemma_decl_reject_empty_encname ()

