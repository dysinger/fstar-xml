# XML 1.0 (Fifth Edition) — Design & Coverage Notes

Status: full W3C XML 1.0 (Fifth Edition, REC vendored at
`xml/docs/xml10-fifth-edition.txt`) well-formedness grammar.  These notes
describe the concrete wire-format decisions and proof strategy, not
aspirational spec (fstar-proofs §28: docs/ holds markdown, never `.fst`
specification skeletons).

## Scope

Well-formedness only (XML 1.0 §2 "documents").  DTD/schema VALIDITY
productions ([9]/[11]/[12]/[13]/[28]-[63]) are OUT of scope — the doctype
declaration is carried STRUCTURALLY for its Name + ExternalID, with the
internal-subset interior carried as an OPAQUE validated string.

## Wire format covered

- **Document [1]** — `prolog element`: optional XML declaration, optional
  doctype declaration, prolog misc (comments/PIs/whitespace), then a single
  root element.
- **Element [39]/[44]** — `<name attrs/>` (empty) or
  `<name attrs>children</name>` (paired), with an attribute list.
- **Attribute [41]/[10]** — `Name = "value"`, whitespace-separated; the value
  resolves entity + character references inline and escapes `"` as `&quot;`;
  empty values (`name=""`) are representable.
- **Node [43]** — text, element, comment, CDATA, and PI, dispatched on the
  first byte after `<`.
- **Text [42]/[14]** — character data as a RUN of XML `Char` productions
  (literal | entity reference | character reference), each resolved inline.
- **Comment [15]** — `<!-- ... -->`, accepting a single `-`, rejecting only
  `--` and a trailing `-`.
- **CDATA [18]/[20]** — `<![CDATA[ ... ]]>`, accepting lone `]`/`]]`,
  rejecting only `]]>`.
- **PI [16]/[17]** — `<?target data?>`, accepting lone `?`, rejecting only
  `?>`.
- **Name [4]/[4a]/[5]** — the full Unicode Name grammar (non-ASCII letters
  admitted), via the UTF-8-aware `Data.Text.Codec.UTF8String` codec.
- **XML declaration [23]-[26]** — `<?xml version="1.x" encoding="EncName"
  standalone="yes|no"?>`; VersionNum is `1.` + digits (`1.0` canonical; any
  `1.x` accepted and roundtripped verbatim).
- **Character references [66]-[68]** — `&#DDD;` (decimal) and `&#xHHH;`
  (hex), with the Unicode code-point bound discipline (fstar-proofs §46).
- **Entities [68]** — the five predefined entities
  (`&amp; &lt; &gt; &quot; &apos;`).
- **SystemLiteral [11] / PubidLiteral [12] / ExternalID [75]** — the
  single-byte-quoted literals and `SYSTEM`/`PUBLIC` external id, VALIDATED
  as part of the doctype declaration envelope (the list-level scans
  `doctype_scan_external_id` / `doctype_scan_system_id` /
  `doctype_scan_public_id` / `doctype_scan_quoted` are the doctype [custom]
  decoder's internals).  They are NOT exposed as standalone composed codecs
  (the former dead `external_id_codec`/`system_literal_codec`/
  `pubid_literal_codec` were DELETED — finding M2).

## Declaration is carried opaquely (fstar-proofs §65)

The `xml_decl` AST carries `decl_version` / `decl_encoding` as **`list char`**
(their grammar's own alphabet), and the prolog carries the declaration as an
**opaque `option string`** (the canonical `<?xml ... ?>` text), exactly as the
doctype is carried opaquely.  The structural `list char` view is recovered by
the PURE parser `xml_decl_scan` and rendered by `xml_decl_enc_bytes` (named
functions, proven on CONCRETE vectors).  A general symbolic
`dec (enc d) == d` roundtrip over the structural record hits the
list-constructor congruence wall (§65), so the codec roundtrip carries the
declaration OPAQUELY via `xmldecl_text_codec` (0-admit), the same pattern the
doctype already used.

## Proof strategy

1. **Combinator roundtrip is generic (Mandate 22).**  All parsing/printing is
   via the record `codec a` combinator library.  The recursive element/
   document roundtrip is proven GENERICALLY by each codec's own `.roundtrip`
   field (0-admit by construction): `greedy`'s roundtrip is inductive over the
   child list, and `map_`/`product`/`alt`/`then_drop`/`between` compose
   sub-roundtrips (fstar-proofs §43/§58).  There is no list-level proof
   mirror.

2. **Fuel-indexed recursion.**  The element codec is
   `let rec xml_element_codec (fuel: nat)`; fuel 0 is `reject`, otherwise one
   more nesting level (LowParse pattern).

3. **Higher-order anti-mutual-recursion.**  The `xml_node`/`xml_element`
   mutual recursion is broken by passing the recursive element codec as a
   VALUE to the children codec, keeping each function self-recursive
   (fstar-proofs §2/§44).

4. **Delimiter-aware leaf content is a `custom` codec with a list-level
   scan.**  Comment/CDATA/PI content, and the doctype bracket-tracking scan,
   are `custom` codecs whose `.dec` does a single `Seq.seq_to_list` at the
   boundary then a list-level scan (fstar-proofs §60/§62).  Their roundtrips
   are the structural-induction `lemma_scan_*_exact` facts.

5. **Untagged optionals are `custom` prefix-tests.**  The optional decl and
   doctype are untagged (absent == no bytes), so they cannot use `sum` (§57
   tag byte) nor `alt` (§62 no empty branch); each is a `custom` codec whose
   decoder does a transparent `starts_with` list-cons prefix test
   (fstar-proofs §62/§63).

## Known scope limits (documented, not admits)

- No DTD/schema validity — well-formedness only.
- No namespace prefix split (`prefix = None` always).
- The DOCTYPE internal subset (`markupdecl` grammar) is carried as an opaque
  validated string, not structurally.
- Prolog misc after the doctype is canonicalized to before it (all misc in
  one `prolog_misc` list); trailing document `Misc*` after the root is not
  represented in the AST.
- **Doctype envelope bracket tracking is quote-aware (finding P2, FIXED).**
  `doctype_balanced`/`scan_doctype_go` now thread a quote state (the
  `SystemLiteral`/`PubidLiteral` opening quote), so a `[`/`]`/`>` INSIDE a
  quoted literal is inert — part of the literal, not bracket structure.  A
  legal `<!DOCTYPE a SYSTEM "]">` (a quoted `]` at depth 0) is now ACCEPTED,
  and `doctype_balanced` agrees with `doctype_scan_quoted` on a bracket-bearing
  literal (previously an internal inconsistency: the quoted scan accepted it
  while the balancer falsely rejected it).  The ExternalID structure itself is
  still validated separately by `doctype_scan_system_id` / `doctype_scan_public_id`.

## REC [2] `Char` exclusion set (enforced)

The full REC [2] production
(`Char ::= #x9 | #xA | #xD | [#x20-#xD7FF] | [#xE000-#xFFFD] |
[#x10000-#x10FFFF]`) is enforced.  `is_xml_cp` / `is_xml_char` (in
`Data.XML.Token`) reject the controls `#x0-#x8`, `#xB`, `#xC`, `#xE-#x1F`
and the noncharacters `#xFFFE`/`#xFFFF`; the surrogates `#xD800-#xDFFF` and
above-max code points are already excluded by `is_valid_cp`/`mk_char` (§46).
The gate `mk_xml_char` is the single code-point validity check used by BOTH
the `&#…;` character references (decimal and hex) and the literal
text/attribute paths (`is_text_char_literal` / `is_attr_char_literal`).
Each accept/reject vector is a NAMED lemma bound in
`Data.XML.Test.Integration`, and the `text_char` / `literal_char` /
`char_ref` decoders reject a control/noncharacter in a concrete
`.dec`-level test binding.
