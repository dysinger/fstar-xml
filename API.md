# Data.XML API Reference

## Named bounds

| Constant | Value | Meaning |
|----------|-------|---------|
| `xml_max_name_len` | 1048576 | Max XML name length (1 Mi chars) |
| `xml_max_attr_len` | 16777216 | Max attribute value length (16 Mi chars) |
| `xml_max_text_len` | 1073741824 | Max text content length (1 Gi chars) |
| `xml_max_ws_len` | 1048576 | Max whitespace run length (1 Mi chars) |
| `xml_max_depth` | 1024 | Max element nesting depth (fuel) |

XML 1.0 imposes no length bound; each bound is a named constant large
enough to never truncate a legitimate document yet small enough to remain
invertible (bounded greedy) and terminating.

## Types (Data.XML.Types)

| Type | Fields | Description |
|------|--------|-------------|
| `xml_name` | `prefix : option string`, `local : string` | XML Name (§2.3) |
| `xml_attribute` | `attr_name : xml_name`, `attr_value : string` | Attribute (§3.1) |
| `xml_node` | `XmlElement \| XmlText \| XmlComment \| XmlPI \| XmlCDATA` | Node (§4) |
| `xml_element` | `elt_name`, `elt_attributes`, `elt_children` | Element |
| `xml_decl` | `decl_version : list char`, `decl_encoding : option (list char)`, `decl_standalone : option bool` | Declaration (§2.8), version/encoding as `list char` §65) |
| `xml_prolog` | `prolog_decl : option string`, `prolog_doctype : option string`, `prolog_misc : list xml_node` | Prolog (§2.8); decl/doctype carried opaquely |
| `xml_document` | `doc_prolog`, `doc_root` | Document (§2.1) |

Helpers: `mk_name`.

Char-level predicates: `is_verdigit_char`, `is_encname_char`,
`version_chars_ok`, `encname_chars_ok`.

## Codecs (Data.XML.Codec)

| Function | Signature | Description |
|----------|-----------|-------------|
| `xml_name_codec` | `codec xml_name` | Name (`prefix = None`) |
| `xml_attribute_codec` | `codec xml_attribute` | `Name = "value"` (resolves entity/char refs, empties) |
| `xml_text_value_codec` | `codec string` | RESOLVED text run (literal \| entity \| char-ref) |
| `xml_attr_value_codec` | `codec string` | RESOLVED attr value (escapes `"` as `&quot;`) |
| `xml_node_body` | `codec xml_element -> codec xml_node` | Node builder (all five kinds) |
| `xml_element_tail` | `codec xml_element -> codec xml_element` | Element body builder (empty \| paired) |
| `xml_element_codec` | `nat -> codec xml_element` | Fuel-indexed element codec |
| `xml_prolog_codec` | `codec xml_prolog` | Prolog (decl? misc* doctype? misc*) |
| `xml_document_codec` | `codec xml_document` | Prolog + root element |
| `encode_xml` | `xml_document -> byte_seq` | Document encode |
| `decode_xml` | `byte_seq -> decode_result xml_document` | Document decode |
| `greedy` | `codec a -> nat -> codec (list a)` | Bounded greedy list |

## Prolog codecs (Data.XML.Codec.Prolog)

| Function | Signature | Description |
|----------|-----------|-------------|
| `doctype_decl_codec` | `codec string` | `<!DOCTYPE ...>` (opaque text, bracket-tracked) |
| `xmldecl_text_codec` | `codec string` | `<?xml ...?>` (opaque text) |
| `optional_decl` | `codec (option string)` | Untagged-optional declaration |
| `optional_doctype` | `codec (option string)` | Untagged-optional doctype |
| `misc_opt` | `codec (option xml_node)` | One Misc (comment/PI/S) |
| `doctype_scan_envelope` | `list byte -> option (list byte)` | Doctype envelope scan ([28] shell: `<!DOCTYPE S Name (S ExternalID)?`) |
| `doctype_scan_external_id` | `list byte -> option (list byte)` | ExternalID [75] shell scan (SYSTEM/PUBLIC) |
| `doctype_scan_quoted` | `list byte -> option (list byte)` | Quoted SystemLiteral/PubidLiteral [11]/[12] scan |
| `xml_decl_scan` | `list byte -> option (xml_decl & list byte)` | Structural decl parser (pure) |
| `xml_decl_enc_bytes` | `xml_decl -> list byte` | Structural decl renderer (pure) |

Note: the `system_literal_codec`/`pubid_literal_codec`/`external_id_codec`
COMPOSED codecs were DELETED (finding M2 — they were dead scaffolding).  The
ExternalID grammar is now validated by the list-level scans above, inside the
doctype `custom` decoder.

## Token codecs (Data.XML.Token)

| Function | Signature | Description |
|----------|-----------|-------------|
| `entity_amp` / `lt` / `gt` / `quot` / `apos` | `codec byte` | The five predefined entities |
| `entity_ref` | custom codec | Ordered choice over the five entities (`one_of`) |
| `char_ref` | `codec char` | `&#DDD;` \| `&#xHHH;` (decimal \| hex) |
| `text_char` | `codec char` | literal \| entity \| char ref |
| `name_codec` | `codec string` | Full Unicode Name ([4]/[4a]/[5]) |
| `ws` | `codec string` | Whitespace run |

## Wrapped codecs (Data.XML.Codec.Wrapped)

| Function | Signature | Description |
|----------|-----------|-------------|
| `comment_content_codec` | `codec string` | `<!-- content -->` (single `-` legal) |
| `cdata_content_codec` | `codec string` | `<![CDATA[ content ]]>` (lone `]` legal) |
| `pi_content_codec` | `codec string` | `<? target data ?>` (lone `?` legal) |

## Roundtrip strategy

The recursive element/document roundtrip is proven GENERICALLY by each
codec's own `.roundtrip` field (0-admit by construction, §43/§58): the
[greedy] combinator's roundtrip is inductive over the child list, and
[map_]/[product]/[alt]/[then_drop]/[between] compose sub-roundtrips.  All
parsing/printing is via the record [codec a] combinator library (Mandate 22).

## Lemmas

| Lemma | Proves |
|-------|--------|
| `lemma_entity_{amp,lt,gt,quot,apos}_roundtrip` | Each entity roundtrips |
| `lemma_entity_ref_roundtrip` | The `one_of` choice roundtrips |
| `lemma_char_ref_{decimal,hex}_roundtrip` | Character-reference roundtrips |
| `lemma_name_nonascii_roundtrip` | Non-ASCII name roundtrip |
| `{comment,cdata,pi}_content_roundtrip` | Wrapped leaf content roundtrips |
| `lemma_doctype_roundtrip` | Doctype opaque-text roundtrip |
| `lemma_xmldecl_text_roundtrip` | Declaration opaque-text roundtrip |
| `lemma_optional_{decl,doctype}_roundtrip` | Untagged-optional roundtrips |
| `xml_document_codec.roundtrip` | General document roundtrip (0-admit, §43) |
| `test_xml_decl_scan_roundtrip_10` | Structural decl concrete vector (§65) |
