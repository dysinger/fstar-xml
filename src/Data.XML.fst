(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)


(**
Data.XML — Verified XML 1.0 Parser/Printer (re-exporter)

Top-level module.  Re-exports the pure AST and the bidirectional record
codec by [include]-ing each sub-module in dependency order (leaf types
first, then the leaf codecs, then the composing codec), matching the
canonical re-exporter pattern of [Data.Codec], [Data.BaseN],
[Language.Cypher], and [Language.SQL].

Re-exported sub-modules:

- [Data.XML.Types] — the pure XML 1.0 AST ([xml_element], [xml_node],
  [xml_name], [xml_attribute], [xml_decl], [xml_prolog], [xml_document]).
- [Data.XML.Token] — leaf codecs: the five predefined entities, names,
  whitespace, and delimiter markers.
- [Data.XML.Codec.Wrapped] — the comment, CDATA, and PI leaf codecs.
- [Data.XML.Codec.Prolog] — the doctype, XML declaration, misc, and
  [ExternalID] scans/codecs.
- [Data.XML.Codec] — the name/attribute/text/element/document codecs plus
  the fuel-indexed recursive element builder and the bounded greedy-list
  combinator.

Zero admits.  Zero magic.  The recursive element/document roundtrip is
proven GENERICALLY by the codec's own [.roundtrip] field ([greedy] induction
+ [map_]/[product]/[alt] composition, fstar-proofs §43); the concrete example
documents are regression anchors restated in [Data.XML.Test.Element].

@header Data.XML
*)
module Data.XML


include Data.XML.Types
include Data.XML.Token
include Data.XML.Codec.Wrapped
include Data.XML.Codec.Prolog
include Data.XML.Codec

