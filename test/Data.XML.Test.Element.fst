(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)


(**
Data.XML.Test.Element — unit tests for the document/element codec.

The recursive element/document roundtrip is proven GENERICALLY by the
codec's own [.roundtrip] field (0-admit by construction: the [greedy]
combinator's [lemma_greedy_roundtrip] is inductive and [map_]/[product]/
[alt]/[then_drop]/[between] each compose sub-roundtrips).  This module
anchors the concrete example document values and the roundtrip lemma's
EXISTENCE so the Integration module enforces their presence mechanically
(CODE_GUIDELINES §Integration test pattern; fstar-proofs §22 — untyped
value bindings under [--admit_smt_queries] confirm the symbol exists).

@header Data.XML.Test.Element
*)
module Data.XML.Test.Element


open Data.XML.Codec
open Data.XML.Types
open Data.Codec


(** The empty document's roundtrip: the codec's [.roundtrip] field is the
    proof (a [xml_document -> byte_seq -> Lemma]); anchoring its existence. *)
let test_empty_doc = example_empty_doc


(** The text document anchor. *)
let test_text_doc = example_text_doc


(** The nested document anchor. *)
let test_nested_doc = example_nested_doc


(** The single-attribute document anchor. *)
let test_attr_doc = example_attr_doc


(** The two-attribute document anchor. *)
let test_multi_attr_doc = example_multi_attr_doc


(** The comment-child document anchor. *)
let test_comment_doc = example_comment_doc


(** The CDATA-child document anchor. *)
let test_cdata_doc = example_cdata_doc


(** The PI-child document anchor. *)
let test_pi_doc = example_pi_doc


(** The declaration+root document anchor. *)
let test_decl_doc = example_decl_doc


(** The declaration+doctype+root document anchor. *)
let test_decl_doctype_doc = example_decl_doctype_doc


(** The doctype-with-ExternalID document anchor. *)
let test_doctype_extid_doc = example_doctype_extid_doc


(** The entity-ref + char-ref + 2-level-nesting document anchor (finding m1). *)
let test_refs_nested_doc = example_refs_nested_doc


(** The document codec's generic roundtrip lemma (0-admit by construction). *)
let test_document_codec_roundtrip = xml_document_codec.roundtrip


(** A mismatched end tag ([<a></b>]) is rejected at the element forward-map
    gate (finding m2 / task 3.2). *)
let test_element_reject_mismatched_tag () : Lemma
  (element_tail_map (mk_name "a", ([], Inr (mk_name "b", []))) == None) =
  lemma_element_reject_mismatched_tag ()


(** A matched end tag ([<a></a>]) is accepted at the forward-map gate. *)
let test_element_accept_matched_tag () : Lemma
  (Some? (element_tail_map (mk_name "a", ([], Inr (mk_name "a", []))))) =
  lemma_element_accept_matched_tag ()

