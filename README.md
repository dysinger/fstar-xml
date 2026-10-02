# xml — verified XML 1.0 parser/printer

A formally verified XML 1.0 (W3C Fifth Edition) bidirectional parser/printer
in F*, built on the record-based [Data.Codec] combinator framework.  This is
the first RECURSIVE record codec in the tree: the mutually-recursive
`xml_element` ↔ `xml_node` AST is handled with a fuel-indexed builder, not a
GADT self-reference.

Zero admits.  Zero magic.  Zero assumptions.  Full XML 1.0 well-formedness
grammar MINUS the documented scope limits (see [docs/README.md § Known
scope limits]): elements, attributes, text with entity/character
references, comments, CDATA, PIs (with the REC [17] [xml]-target exclusion),
full Unicode names, the XML declaration, and a quote-aware doctype.  The
doctype internal subset is carried opaquely (bracket-balanced), trailing
document [Misc*] is not represented, and namespace prefixes are not split.

## Architecture

```
Data.XML.Types           — pure XML 1.0 AST + char-level decl predicates
Data.XML.Token           — leaf codecs: entities, char refs, names, whitespace
Data.XML.Codec.Wrapped   — comment, CDATA, and PI content codecs
Data.XML.Codec.Prolog    — doctype, XML declaration, misc, ExternalID trees
Data.XML.Codec           — name/attribute/text/element/document codecs
Data.XML.Pulse           — C-extractable token tag codec
Data.XML.Types.Pulse     — C-extractable AST node tag codec
Data.XML                 — top-level re-export
```

The recursive element/document roundtrip is proven GENERICALLY by each
codec's own [.roundtrip] field (0-admit by construction): the [greedy]
combinator's roundtrip is inductive over the child list, and [map_]/[product]/
[alt]/[then_drop]/[between] each compose sub-roundtrips (fstar-proofs §43/§58).
There is no separate list-level proof mirror; all parsing/printing is via the
record [codec a] combinators (Mandate 22).

## Key properties

- **Zero explicit escape hatches.**  Every module verifies with structural
  roundtrip proofs (leaves, bounded greedy, delimiter scans) or the generic
  combinator `.roundtrip` field; no proof escape hatch, no value coercion, no
  axioms.
- **First recursive record codec.**  The element codec is built with a
  fuel-indexed `let rec xml_element_codec (fuel: nat)`; fuel 0 is `reject`
  (fstar-proofs §23).
- **Bounded greedy lists.**  Variable-length children/misc use a bounded
  greedy-list combinator ([greedy c max]); an unbounded greedy scan is not
  invertible (fstar-proofs §43).
- **Content-based alternation.**  Entities use `one_of`; node/empty-vs-paired
  dispatch use `alt` (first-byte-disjoint).  Untagged optionals (decl,
  doctype) use `custom` prefix-tests (§62).
- **Delimiter-aware content.**  Comment/CDATA/PI content and the doctype
  bracket-tracking scan are `custom` codecs with a list-level scan (§60/§62).
- **Full Unicode names.**  Names admit non-ASCII letters via the UTF-8-aware
  `Data.Text.Codec.UTF8String` codec (§46/§59).
- **REC [2] `Char` enforced.**  `is_xml_cp`/`is_xml_char`/`mk_xml_char` reject
  the control characters (`#x0-#x8`, `#xB`, `#xC`, `#xE-#x1F`) and the
  noncharacters (`#xFFFE`/`#xFFFF`) in text, attribute, and character-
  reference content; surrogates and above-max code points are already
  excluded by `is_valid_cp`/`mk_char`.
- **C extraction.**  The two Pulse modules (token tags, AST node tags)
  extract to C11 via Custard (no KaRaMeL).

## Wire format

- document: optional XML declaration, optional doctype, prolog misc, then a
  single root element.
- element: `<name attrs/>` (empty) or `<name attrs>children</name>` (paired).
- attribute: `Name = "value"` (resolves entity/char refs, escapes `"`).
- node: text | element | comment | CDATA | PI.
- text: a run of XML `Char` productions, entity/char refs resolved inline.
- declaration: `<?xml version="1.x" ...?>` (carried opaque; `1.0` canonical).
- doctype: `<!DOCTYPE ...>` (Name + ExternalID structured; interior opaque).

## Testing

`test/` holds Token, Codec, Element, Prolog, and Integration test
modules.  The wrapped comment/CDATA/PI content codecs are tested in
`Data.XML.Test.Codec`.  The Integration module binds every public test/lemma
function by name, so deleting or renaming any function breaks verification.
Concrete example documents are regression anchors restated in the test
modules.

## Build

```sh
nix develop
make check    # Verify all modules (src + test)
```

Or via nix:

```sh
nix build .#checked  # F* verification gate (0-admit)
nix build .#native   # C11 shared/static lib (default)
nix build .#ocaml    # OCaml findlib package
nix build .#fsharp   # .NET library
```

## Dependencies

- `Data.Codec` — record `codec` combinator library (`custom`, `bytes`,
  `byte_val`, `product`, `map_`, `one_of`, `alt`, `between`, `then_drop`).
- `Data.Text.Codec` — text codec library (`text_chars`, `utf8_string`,
  `Data.Text.Codec.Chars`, `Data.Text.Codec.UTF8`, `Data.Text.Codec.UTF8String`).

Both are consumed from the published `dysinger/codec` /
`dysinger/text` flake inputs (see [flake.nix]).

## Normative reference

The full W3C XML 1.0 (Fifth Edition) recommendation is vendored at
`docs/xml10-fifth-edition.txt` for offline auditing.
