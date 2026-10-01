(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)

(**
Data.XML.Types — XML 1.0 Abstract Syntax Tree.

Pure F\* types per W3C XML 1.0 Fifth Edition.  Represents well-formed XML
documents: elements, attributes, text, comments, PIs, and CDATA.

No codec dependency — this module is the pure AST shared by
[Data.XML.Codec], [Data.XML.Token], and the Low\* modules.

It also carries the CHAR-LEVEL well-formedness predicates for the XML
declaration ([version_chars_ok] / [encname_chars_ok] / [is_verdigit_char] /
[is_encname_char]) — the §65-probe-verified forms that let the declaration
roundtrip operate on an explicit [list char] rather than the opaque
[FStar.String.list_of_string] primitive (fstar-proofs §63).

Copyright 2026 Department of Code LLC. All rights reserved.

@header Data.XML.Types
*)
module Data.XML.Types

open FStar.Char
open FStar.List.Tot

(** Name — XML 1.0 §2.3 *)

(** [xml_name] — a qualified name: an optional namespace prefix and a
    required local name.  The v0.1 subset encodes [prefix = None] always
    (QName splitting is deferred; see xml/docs/README.md). *)
type xml_name = {
  prefix : option string;
  local  : string;
}

(** [mk_name local] — build a plain (unprefixed) name. *)
let mk_name (local: string) : xml_name = { prefix = None; local = local }

(** Attribute — XML 1.0 §3.1 *)

(** [xml_attribute] — a name/value pair on an element. *)
type xml_attribute = {
  attr_name  : xml_name;
  attr_value : string;
}

(** Node — XML 1.0 §4 *)

(** [xml_node] — one node in an element's children.

    Five node kinds: [XmlElement] (a nested element), [XmlText] (a run of
    character data), [XmlComment], [XmlPI] (a processing instruction, with
    target and data), and [XmlCDATA]. *)
type xml_node =
  | XmlElement : xml_element -> xml_node
  | XmlText    : string -> xml_node
  | XmlComment : string -> xml_node
  | XmlPI      : target:string -> data:string -> xml_node
  | XmlCDATA   : string -> xml_node

(** [xml_element] — an element: a name, a list of attributes, and a list of
    child nodes.  The [xml_node]/[xml_element] pair is mutually recursive;
    the codec breaks the recursion with a fuel-indexed builder. *)
and xml_element = {
  elt_name       : xml_name;
  elt_attributes : list xml_attribute;
  elt_children   : list xml_node;
}

(** Declaration — XML 1.0 §2.8 *)

(** [xml_decl] — an XML declaration: version, optional encoding, and
    optional standalone flag.

    The version and encoding are carried as their grammar's OWN alphabet
    ([list char]) — NOT [string] — so the declaration roundtrip operates on
    an explicit char list and never re-constructs a [string] field from an
    [FStar.String.string_of_list] congruence (fstar-proofs §64/§65, the
    [string_of_list] wall).  [decl_version] is the full VersionNum
    ([1. + digits]); [decl_encoding] is the optional EncName; both verbatim.
    [decl_standalone] is the optional [yes]/[no] flag. *)
type xml_decl = {
  decl_version  : list char;
  decl_encoding : option (list char);
  decl_standalone : option bool;
}

(** Is [c] a VersionNum digit character ([0-9])? *)
let is_verdigit_char (c: char) : bool =
  let v = FStar.Char.int_of_char c in 0x30 <= v && v <= 0x39

(** Is [c] an [EncName] character ([A-Za-z0-9._-])? *)
let is_encname_char (c: char) : bool =
  let v = FStar.Char.int_of_char c in
  (0x41 <= v && v <= 0x5A) || (0x61 <= v && v <= 0x7A) ||
  (0x30 <= v && v <= 0x39) || v = 0x2E || v = 0x5F || v = 0x2D

(** [version_chars_ok cs] — [cs] is a well-formed VersionNum
    ([1. + one-or-more digits], XML 1.0 production [26]).  The leading
    [1.] is a fixed two-char prefix; the remainder is one-or-more digit
    characters.  Empty or non-matching lists are rejected. *)
let version_chars_ok (cs: list char) : bool =
  match cs with
  | c1 :: c2 :: dig :: rest ->
    FStar.Char.int_of_char c1 = 0x31 && FStar.Char.int_of_char c2 = 0x2E &&
    is_verdigit_char dig && for_all is_verdigit_char rest
  | _ -> false

(** [encname_chars_ok cs] — [cs] is a well-formed EncName (XML 1.0
    production [81]): one-or-more [A-Za-z0-9._-] characters. *)
let encname_chars_ok (cs: list char) : bool =
  match cs with
  | c :: rest -> is_encname_char c && for_all is_encname_char rest
  | [] -> false

(** Prolog — XML 1.0 §2.8 *)

(** [xml_prolog] — the document prolog: an optional declaration, an optional
    DOCTYPE, and miscellaneous leading comments/PIs.

    Both [prolog_decl] and [prolog_doctype] are carried as OPAQUE canonical
    text ([option string]) — NOT structural — matching the §65 decision for
    the declaration and the already-landed doctype pattern: the codec
    roundtrip reconstructs the field by the opaque [string_of_list] bijection
    ([text_bytes_to_string (text_string_to_bytes s) == s], fstar-proofs §45),
    which is 0-admit, whereas a STRUCTURAL [xml_decl] field's symbolic
    roundtrip hits the §65 list-constructor congruence wall.  The STRUCTURAL
    declaration view remains available as the pure parser [xml_decl_scan] /
    renderer [xml_decl_enc_bytes] in [Data.XML.Codec.Prolog]. *)
type xml_prolog = {
  prolog_decl    : option string;
  prolog_doctype : option string;
  prolog_misc    : list xml_node;  (* comments and PIs before root *)
}

(** Document — XML 1.0 §2.1 *)

(** [xml_document] — a document: a prolog followed by a single root element. *)
type xml_document = {
  doc_prolog : xml_prolog;
  doc_root   : xml_element;
}
