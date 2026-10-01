(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)

(**
Data.XML.Token — XML 1.0 character codecs and entity references.

Low-level leaf codecs used by [Data.XML.Codec]: whitespace, names,
the five predefined entity references, decimal/hexadecimal character
references, and the double-quote codec ([dquote]).

Built on the record [Data.Codec] combinator library and the
[Data.Text.Codec] char analysis.

@header Data.XML.Token

STATUS: the leaf codecs are verified at 0 admits.  [entity_body] via [one_of]
(Combinator 21) holds the single post-[&] literal set; [entity_ref] factors
the [&] prefix combinatorially ([then_drop] over [byte_val], fstar-proofs
§53).  [char_ref_decimal] via [digits_to_int] and [char_ref_hex] via the new
[hex_digits_to_int] (base-16 analogue, fstar-proofs §43), each gating
[char_of_int] through [mk_char] (§46).  [char_ref] (the [alt] choice of
hex/decimal dispatched on the byte after [&#]) and [text_char] (a single XML
[Char] = literal | entity | char ref) are LANDED as combinator compositions
whose [.roundtrip] is generic and 0-admit by construction (Task 1.4; Task 1.7
deduplicates the entity literal set).
*)
module Data.XML.Token

open Data.Codec
open Data.Text.Codec
open Data.Text.Codec.Chars
open Data.Text.Codec.UTF8
open Data.Text.Codec.UTF8String
open FStar.Seq
open FStar.Seq.Properties
open FStar.Char
open FStar.UInt8
open FStar.List.Tot

module U8 = FStar.UInt8

(** Named constants — single source of truth for XML 1.0 bounds.

    XML 1.0 imposes no length limit, so each bound is a real (large) nat:
    large enough that no legitimate document is truncated, finite enough to
    stay terminating and invertible (bounded greedy, fstar-proofs §43). *)
let xml_max_name_len : nat = 1048576     (* names: 1 Mi chars *)
let xml_max_attr_len : nat = 16777216    (* attribute values: 16 Mi chars *)
let xml_max_text_len : nat = 1073741824  (* text content: 1 Gi chars *)
let xml_max_ws_len   : nat = 1048576     (* whitespace runs: 1 Mi chars *)
let xml_max_depth    : nat = 1024        (* element nesting fuel *)

(** Character predicates (ASCII code points < 128), XML 1.0 §2.3. *)

(** True iff [c] is an XML whitespace character (space/tab/CR/LF). *)
let is_xml_ws_char (c: FStar.Char.char) : bool =
  let v = FStar.Char.int_of_char c in
  v = 0x20 || v = 0x09 || v = 0x0D || v = 0x0A

(** True iff [cp] is a valid XML 1.0 [Char] code point — production [2].

    [2] Char ::= #x9 | #xA | #xD | [#x20-#xD7FF] | [#xE000-#xFFFD] |
    [#x10000-#x10FFFF].  The exclusion set is therefore the control
    characters [#x0-#x8], [#xB], [#xC], [#xE-#x1F] (note [#x9], [#xA],
    [#xD] ARE allowed — they are whitespace), the surrogate block
    [#xD800-#xDFFF] (excluded by the gap between [#xD7FF] and [#xE000]),
    and the noncharacters [#xFFFE]-[#xFFFF] (excluded by the [#xFFFD] upper
    bound).  Every NameStartChar/NameChar/whitespace code point is a valid
    [Char], so this tightens only the literal text/attribute and character-
    reference paths (finding M1). *)
let is_xml_cp (cp: int) : bool =
  cp = 0x9 || cp = 0xA || cp = 0xD ||
  (0x20 <= cp && cp <= 0xD7FF) ||
  (0xE000 <= cp && cp <= 0xFFFD) ||
  (0x10000 <= cp && cp <= 0x10FFFF)

(** True iff [c] is a valid XML 1.0 [Char] character — [is_xml_cp] at the
    [char] level.  Excludes the controls, surrogates, and noncharacters
    (finding M1). *)
let is_xml_char (c: FStar.Char.char) : bool =
  is_xml_cp (FStar.Char.int_of_char c)

(** True iff [c] is a NameStartChar (letter, underscore, colon) — full
    XML 1.0 production [4].

    [4] NameStartChar ::= ":" | [A-Z] | "_" | [a-z] | [#xC0-#xD6] |
    [#xD8-#xF6] | [#xF8-#x2FF] | [#x370-#x37D] | [#x37F-#x1FFF] |
    [#x200C-#x200D] | [#x2070-#x218F] | [#x2C00-#x2FEF] | [#x3001-#xD7FF] |
    [#xF900-#xFDCF] | [#xFDF0-#xFFFD] | [#x10000-#xEFFFF].

    The surrogate range [#xD800-#xDFFF] is absent from the REC (surrogates are
    not scalar values); F*'s [char] type also excludes it.  The [#x3001-#xD7FF]
    upper bound is written INCLUSIVE ([<= 0xD7FF]) to match the REC's literal
    [#xD7FF]; F*'s [char_code] refinement is in fact [< 0xd7ff] (exclusive,
    fstar-proofs §46), so a [char] with code exactly [#xD7FF] is unreachable
    and the inclusive guard is vacuously satisfiable at that boundary — the
    two bounds agree on every REPRESENTABLE code point. *)
let is_name_start_char (c: FStar.Char.char) : bool =
  let v = FStar.Char.int_of_char c in
  (0x41 <= v && v <= 0x5A) ||
  (0x61 <= v && v <= 0x7A) ||
  v = 0x5F || v = 0x3A ||
  (0xC0 <= v && v <= 0xD6) ||
  (0xD8 <= v && v <= 0xF6) ||
  (0xF8 <= v && v <= 0x2FF) ||
  (0x370 <= v && v <= 0x37D) ||
  (0x37F <= v && v <= 0x1FFF) ||
  (0x200C <= v && v <= 0x200D) ||
  (0x2070 <= v && v <= 0x218F) ||
  (0x2C00 <= v && v <= 0x2FEF) ||
  (0x3001 <= v && v <= 0xD7FF) ||
  (0xF900 <= v && v <= 0xFDCF) ||
  (0xFDF0 <= v && v <= 0xFFFD) ||
  (0x10000 <= v && v <= 0xEFFFF)

(** True iff [c] is a NameChar (NameStartChar plus digit, hyphen, dot, and
    the combining/extended ranges) — full XML 1.0 production [4a].

    [4a] NameChar ::= NameStartChar | "-" | "." | [0-9] | #xB7 |
    [#x0300-#x036F] | [#x203F-#x2040]. *)
let is_name_char_char (c: FStar.Char.char) : bool =
  is_name_start_char c ||
  (let v = FStar.Char.int_of_char c in
   (0x30 <= v && v <= 0x39) || v = 0x2D || v = 0x2E || v = 0xB7 ||
   (0x300 <= v && v <= 0x36F) ||
   (0x203F <= v && v <= 0x2040))

(** A name string is well-formed: non-empty, head is NameStartChar, every
    remaining char is a NameChar, and length ≤ [xml_max_name_len]. *)
let is_name_string (s: string) : bool =
  let chars = FStar.String.list_of_string s in
  Cons? chars &&
  is_name_start_char (List.Tot.hd chars) &&
  List.Tot.for_all is_name_char_char (List.Tot.tl chars) &&
  List.Tot.length chars <= xml_max_name_len

(** Is [c] an ASCII [x] (0x78) or [X] (0x58)? *)
let is_ascii_x_or_X (c: FStar.Char.char) : bool =
  let v = FStar.Char.int_of_char c in v = 0x78 || v = 0x58

(** Is [c] an ASCII [m] (0x6D) or [M] (0x4D)? *)
let is_ascii_m_or_M (c: FStar.Char.char) : bool =
  let v = FStar.Char.int_of_char c in v = 0x6D || v = 0x4D

(** Is [c] an ASCII [l] (0x6C) or [L] (0x4C)? *)
let is_ascii_l_or_L (c: FStar.Char.char) : bool =
  let v = FStar.Char.int_of_char c in v = 0x6C || v = 0x4C

(** [is_the_xml_target s] — [s] begins with the three-character ASCII sequence
    [xml] (case-insensitive).  The first three characters are [xX], [mM],
    [lL].  This is the reserved PI target prefix REC [17] excludes
    ([PITarget ::= Name - (('X'|'x') ('M'|'m') ('L'|'l'))]). *)
let is_the_xml_target (s: string) : bool =
  let chars = FStar.String.list_of_string s in
  match chars with
  | x :: m :: l :: _ ->
    (is_ascii_x_or_X x) && (is_ascii_m_or_M m) && (is_ascii_l_or_L l)
  | _ -> false

(** [is_pi_target s] — [s] is a valid PI target: a well-formed Name whose
    first three characters are NOT the reserved target [xml] in any of the
    eight case combinations ([xml], [xmL], [xMl], [xML], [Xml], [XmL],
    [XMl], [XML] — REC [17], (('X'|'x')('M'|'m')('L'|'l'))).  [is_pi_target]
    strictly sharpens [is_name_string] by excluding the reserved target. *)
let is_pi_target (s: string) : bool =
  is_name_string s && not (is_the_xml_target s)

(** Whitespace *)

(** [ws] — one-or-more XML whitespace characters, bounded greedy.

    Decoder consumes up to [xml_max_ws_len] whitespace bytes, stopping at
    the bound or the first non-whitespace byte (fstar-proofs §43). *)
let ws : codec string = text_chars xml_max_ws_len is_xml_ws_char

(** Name *)

(** [name_codec] — a single XML Name (NameStartChar NameChar star),
    full XML 1.0 productions [4]/[4a]/[5] with Unicode names.

    Built as [map_] over [utf8_string xml_max_name_len] (the UTF-8-aware
    [codec string] from [Data.Text.Codec.UTF8String]); the Name-specific
    well-formedness (head is [is_name_start_char], tail chars are
    [is_name_char_char]) is enforced in the forward map [is_name_string], so
    the roundtrip proof composes from the already-proven [utf8_string] and
    [map_] roundtrips (no bespoke decoder guard — fstar-proofs §45).

    Non-ASCII NameStartChar/NameChar (e.g. a Unicode letter) encode via their
    UTF-8 byte sequence and roundtrip through [utf8_string]. *)
let name_codec : codec string =
  map_
    (fun (s: string) -> if is_name_string s then Some s else None)
    (fun (s: string) -> Some s)
    (utf8_string xml_max_name_len)

(** A non-ASCII Name roundtrip (Task 5.2): U+00E9 (LATIN SMALL LETTER E
    WITH ACUTE, [é]) is a NameStartChar in the RFC [4] range [#xD8-#xF6],
    and [é] is a valid XML Name — its UTF-8 encoding ([0xC3; 0xA9]) decodes
    back to itself through the [utf8_string] codec.

    Two facts compose the non-ASCII-name guarantee:
    - [lemma_name_accepts_nonascii] — [is_name_string "é"] is [true] (the
      full-Unicode Name predicate accepts a non-ASCII NameStartChar).
    - the [utf8_string] roundtrip ([lemma_utf8_string_roundtrip], already
      0-admit in [Data.Text.Codec.UTF8String]) proves [é] ⇄ [0xC3; 0xA9]. *)

(** [é] (U+00E9) is a NameStartChar (and hence a NameChar) — the
    full-Unicode Name predicate accepts a non-ASCII NameStartChar. *)
let lemma_name_accepts_nonascii () : Lemma
  (ensures is_name_start_char (FStar.Char.char_of_int 0xE9) /\
           is_name_char_char (FStar.Char.char_of_int 0xE9))
  = let c = FStar.Char.char_of_int 0xE9 in
    assert (FStar.Char.int_of_char c == 0xE9);
    assert_norm (0xD8 <= 0xE9 && 0xE9 <= 0xF6);
    assert (is_name_start_char c);
    assert (is_name_char_char c);
    ()

(** [é] (U+00E9) roundtrips through the [name_codec]'s UTF-8 layer: its
    UTF-8 bytes [0xC3; 0xA9] decode back to ["é"], consuming 2 bytes. *)
let lemma_name_nonascii_roundtrip () : Lemma
  (ensures
    utf8_string_dec xml_max_name_len
      (utf8_string_enc "é" `Seq.append` Seq.empty)
      == Inr ("é", Seq.length (utf8_string_enc "é")))
  = lemma_utf8_string_roundtrip xml_max_name_len "é" Seq.empty

(* ========================================================================
   Name rejection lemmas (finding M1 / task 2.1).

   The [name_codec] is [map_] over [utf8_string] whose FORWARD map ([is_name_string])
   is the soundness gate: a non-Name string produces [None] in the forward map,
   which [map_.dec] converts to [Inl (ExpectedPredicate 0)].  The gate is stated
   at the transparent predicate level ([is_name_string]), because the composed
   [name_codec.dec] does not reduce cross-module (the inner [utf8_string] is a
   [custom codec] whose [.dec] is the §44-opaque [let rec] scan — fstar-proofs
   §52 Pitfall 3 / §58).  The three covered malformed Names are the empty name,
   a leading-digit name, and an interior-whitespace name (productions [4]/[4a]/[5]).
   ======================================================================== *)

(** The empty string is not a Name (no [NameStartChar]). *)
let lemma_name_reject_empty () : Lemma (is_name_string "" == false)
  = assert_norm (is_name_string "" == false)

(** A leading digit is not a [NameStartChar] ([1abc] starts with [1]). *)
let lemma_name_reject_leading_digit () : Lemma (is_name_string "1abc" == false)
  = assert_norm (is_name_string "1abc" == false)

(** An interior space is not a [NameChar] ([a b] contains [space]). *)
let lemma_name_reject_interior_space () : Lemma (is_name_string "a b" == false)
  = assert_norm (is_name_string "a b" == false)

(* ========================================================================
   PI-target lemmas (finding P1 / task 2.1).

   [is_pi_target] sharpens [is_name_string] by excluding the reserved target
   [xml] in all eight case combinations (REC [17]).  Stated at the transparent
   predicate level because the composed [pi_target_codec.dec] does not reduce
   cross-module (same reason as the [name_codec] gate above).
   ======================================================================== *)

(** An ordinary PI target ([pi]) is accepted as a target: it is a Name and
    not the reserved [xml] prefix. *)
#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
let lemma_pi_target_accept_pi () : Lemma (is_pi_target "pi" == true)
  = assert_norm (is_pi_target "pi" == true)
#pop-options

(** The reserved target [xml] (lowercase) is rejected: the reserved prefix
    forces the [not] conjunct to [false]. *)
#push-options "--z3rlimit 200"
let lemma_pi_target_reject_xml () : Lemma (is_pi_target "xml" == false)
  = assert_norm (is_the_xml_target "xml" == true)
#pop-options

(** The reserved target [XML] (uppercase) is rejected. *)
#push-options "--z3rlimit 200"
let lemma_pi_target_reject_XML () : Lemma (is_pi_target "XML" == false)
  = assert_norm (is_the_xml_target "XML" == true)
#pop-options

(** The reserved target [Xml] (mixed case) is rejected. *)
#push-options "--z3rlimit 200"
let lemma_pi_target_reject_Xml () : Lemma (is_pi_target "Xml" == false)
  = assert_norm (is_the_xml_target "Xml" == true)
#pop-options

(** The reserved target [xMl] (mixed case) is rejected. *)
#push-options "--z3rlimit 200"
let lemma_pi_target_reject_xMl () : Lemma (is_pi_target "xMl" == false)
  = assert_norm (is_the_xml_target "xMl" == true)
#pop-options

(** The reserved target [xmL] (mixed case) is rejected. *)
#push-options "--z3rlimit 200"
let lemma_pi_target_reject_xmL () : Lemma (is_pi_target "xmL" == false)
  = assert_norm (is_the_xml_target "xmL" == true)
#pop-options

(** The reserved target [xML] (mixed case) is rejected. *)
#push-options "--z3rlimit 200"
let lemma_pi_target_reject_xML () : Lemma (is_pi_target "xML" == false)
  = assert_norm (is_the_xml_target "xML" == true)
#pop-options

(** The reserved target [XmL] (mixed case) is rejected. *)
#push-options "--z3rlimit 200"
let lemma_pi_target_reject_XmL () : Lemma (is_pi_target "XmL" == false)
  = assert_norm (is_the_xml_target "XmL" == true)
#pop-options

(** The reserved target [XMl] (mixed case) is rejected. *)
#push-options "--z3rlimit 200"
let lemma_pi_target_reject_XMl () : Lemma (is_pi_target "XMl" == false)
  = assert_norm (is_the_xml_target "XMl" == true)
#pop-options

(** Entity references *)

(** [&amp;] → U+0026 ampersand. *)
let entity_amp : codec byte =
  map_ (fun (_: unit) -> Some 0x26uy)
       (fun (b: byte) -> if b = 0x26uy then Some () else None)
       (bytes [0x26uy; 0x61uy; 0x6Duy; 0x70uy; 0x3Buy])

(** [&lt;] → U+003C less-than. *)
let entity_lt : codec byte =
  map_ (fun (_: unit) -> Some 0x3Cuy)
       (fun (b: byte) -> if b = 0x3Cuy then Some () else None)
       (bytes [0x26uy; 0x6Cuy; 0x74uy; 0x3Buy])

(** [&gt;] → U+003E greater-than. *)
let entity_gt : codec byte =
  map_ (fun (_: unit) -> Some 0x3Euy)
       (fun (b: byte) -> if b = 0x3Euy then Some () else None)
       (bytes [0x26uy; 0x67uy; 0x74uy; 0x3Buy])

(** [&quot;] → U+0022 quotation mark. *)
let entity_quot : codec byte =
  map_ (fun (_: unit) -> Some 0x22uy)
       (fun (b: byte) -> if b = 0x22uy then Some () else None)
       (bytes [0x26uy; 0x71uy; 0x75uy; 0x6Fuy; 0x74uy; 0x3Buy])

(** [&apos;] → U+0027 apostrophe. *)
let entity_apos : codec byte =
  map_ (fun (_: unit) -> Some 0x27uy)
       (fun (b: byte) -> if b = 0x27uy then Some () else None)
       (bytes [0x26uy; 0x61uy; 0x70uy; 0x6Fuy; 0x73uy; 0x3Buy])

(** Entity roundtrip lemmas (XML 1.0 §4.6), proven via the transparent
    [.enc]/[.dec] fields + [lemma_bytes_self_prefix_spec] rather than the
    opaque [map_] [.roundtrip] field (fstar-proofs §15/§18). *)

(** [&amp;] → [&] roundtrip. *)
#push-options "--z3rlimit 400"
let lemma_entity_amp_roundtrip () : Lemma
  (ensures entity_amp.dec (entity_amp.enc 0x26uy) == Inr (0x26uy, 5))
  = let enc = entity_amp.enc 0x26uy in
    assert (enc == seq_of_list [0x26uy; 0x61uy; 0x6Duy; 0x70uy; 0x3Buy]);
    lemma_bytes_self_prefix_spec [0x26uy; 0x61uy; 0x6Duy; 0x70uy; 0x3Buy] Seq.empty;
    ()
#pop-options

(** [&lt;] → [<] roundtrip. *)
#push-options "--z3rlimit 400"
let lemma_entity_lt_roundtrip () : Lemma
  (ensures entity_lt.dec (entity_lt.enc 0x3Cuy) == Inr (0x3Cuy, 4))
  = let enc = entity_lt.enc 0x3Cuy in
    assert (enc == seq_of_list [0x26uy; 0x6Cuy; 0x74uy; 0x3Buy]);
    lemma_bytes_self_prefix_spec [0x26uy; 0x6Cuy; 0x74uy; 0x3Buy] Seq.empty;
    ()
#pop-options

(** [&gt;] → [>] roundtrip. *)
#push-options "--z3rlimit 400"
let lemma_entity_gt_roundtrip () : Lemma
  (ensures entity_gt.dec (entity_gt.enc 0x3Euy) == Inr (0x3Euy, 4))
  = let enc = entity_gt.enc 0x3Euy in
    assert (enc == seq_of_list [0x26uy; 0x67uy; 0x74uy; 0x3Buy]);
    lemma_bytes_self_prefix_spec [0x26uy; 0x67uy; 0x74uy; 0x3Buy] Seq.empty;
    ()
#pop-options

(** [&quot;] → ["] roundtrip. *)
#push-options "--z3rlimit 400"
let lemma_entity_quot_roundtrip () : Lemma
  (ensures entity_quot.dec (entity_quot.enc 0x22uy) == Inr (0x22uy, 6))
  = let enc = entity_quot.enc 0x22uy in
    assert (enc == seq_of_list [0x26uy; 0x71uy; 0x75uy; 0x6Fuy; 0x74uy; 0x3Buy]);
    lemma_bytes_self_prefix_spec [0x26uy; 0x71uy; 0x75uy; 0x6Fuy; 0x74uy; 0x3Buy] Seq.empty;
    ()
#pop-options

(** [&apos;] → ['] roundtrip. *)
#push-options "--z3rlimit 400"
let lemma_entity_apos_roundtrip () : Lemma
  (ensures entity_apos.dec (entity_apos.enc 0x27uy) == Inr (0x27uy, 6))
  = let enc = entity_apos.enc 0x27uy in
    assert (enc == seq_of_list [0x26uy; 0x61uy; 0x70uy; 0x6Fuy; 0x73uy; 0x3Buy]);
    lemma_bytes_self_prefix_spec [0x26uy; 0x61uy; 0x70uy; 0x6Fuy; 0x73uy; 0x3Buy] Seq.empty;
    ()
#pop-options

(* ────────────────────────────────────────────────────────────────────────
   Entity reference choice — [one_of] over the five predefined entities.

   The five literals are NOT first-byte-disjoint ([&amp;] and [&apos;] both
   start [&a]), so they cannot use [alt]; they use [one_of] (Combinator 21),
   which is an ORDERED terminated-literal choice.  The decoder tries each
   literal with [bytes_decode] in order; a wrong literal fails ([Inl]) and the
   search continues until the target literal's self-prefix matches.
   ──────────────────────────────────────────────────────────────────────── *)

(* ========================================================================
   Character references (XML 1.0 §4.1) — [&#DDD;] and [&#xHHH;].

   A character reference decodes to the Unicode code point it names, as a
   [FStar.Char.char].  Decimal ([&#DDD;]) reuses the already-proven
   [digits_to_int] bounded-greedy codec; hexadecimal ([&#xHHH;]) is a new
   base-16 analogue ([hex_digits_to_int]) built on the same [digits_to_int]
   proof shape (fstar-proofs §43).  Both gate every [char_of_int] through
   [mk_char] with the exact [char_code] bound (fstar-proofs §46).
   ======================================================================== *)

(** True iff [cp] is a Unicode scalar value representable in [FStar.Char.char]
    (the [char_code] bound: [[0, 0xD7FF] ∪ [0xE000, 0x10FFFF]]). *) 
let is_valid_cp (cp: int) : bool =
  (cp >= 0 && cp < 0xD7FF) || (cp >= 0xE000 && cp <= 0x10FFFF)

(** [mk_xml_char cp] — the REC [2] [Char] validity gate: [is_xml_cp] AND the
    [mk_char] scalar bound, returning the [char] only when both hold.  This
    is the SAME code-point validity check used by BOTH the [&#…;] character
    references and the literal text/attribute paths (finding M1): a control
    ([#x0-#x8]/[#xB]/[#xC]/[#xE-#x1F]) or noncharacter ([#xFFFE]/[#xFFFF])
    yields [None], so the enclosing [map_] forwards it as a parse error.
    [is_xml_cp] already excludes surrogates/above-max (its [Char] bounds),
    so [mk_char] inside is only the redundant scalar bound. *)
let mk_xml_char (cp: int) : option FStar.Char.char =
  if is_xml_cp cp then mk_char cp else None

(* ========================================================================
   [is_xml_char] accept + reject lemmas (finding M1 / task 1.3–1.4).

   Each vector is a NAMED lemma bound in [Data.XML.Test.Token] and re-bound
   in [Data.XML.Test.Integration], so its presence is mechanically enforced.
   The bodies discharge at the transparent predicate level ([assert_norm] /
   [FStar.Char.int_of_char] reduction, fstar-proofs §52 Pitfall 4): [is_xml_cp]
   is a closed boolean over a concrete code point, so the normalizer (not an
   opaque scan) evaluates it directly.  §52 Pitfall 4 discipline is honored —
   each lemma normalizes the concrete predicate rather than chaining a generic
   [let rec] scanner.
   ======================================================================== *)

(** [is_xml_char] accepts TAB (#x9). *)
let lemma_is_xml_char_tab () : Lemma
  (ensures is_xml_char (FStar.Char.char_of_int 0x9))
  = assert (FStar.Char.int_of_char (FStar.Char.char_of_int 0x9) == 0x9);
    assert_norm (is_xml_cp 0x9)

(** [is_xml_char] accepts LF (#xA). *)
let lemma_is_xml_char_lf () : Lemma
  (ensures is_xml_char (FStar.Char.char_of_int 0xA))
  = assert (FStar.Char.int_of_char (FStar.Char.char_of_int 0xA) == 0xA);
    assert_norm (is_xml_cp 0xA)

(** [is_xml_char] accepts CR (#xD). *)
let lemma_is_xml_char_cr () : Lemma
  (ensures is_xml_char (FStar.Char.char_of_int 0xD))
  = assert (FStar.Char.int_of_char (FStar.Char.char_of_int 0xD) == 0xD);
    assert_norm (is_xml_cp 0xD)

(** [is_xml_char] accepts [A] (U+0041). *)
let lemma_is_xml_char_a () : Lemma
  (ensures is_xml_char 'A')
  = assert (FStar.Char.int_of_char 'A' == 0x41);
    assert_norm (is_xml_cp 0x41)

(** [is_xml_char] rejects the control character #x1. *)
let lemma_is_xml_char_reject_1 () : Lemma
  (ensures is_xml_char (FStar.Char.char_of_int 0x1) == false)
  = assert (FStar.Char.int_of_char (FStar.Char.char_of_int 0x1) == 0x1);
    assert_norm (is_xml_cp 0x1 == false)

(** [is_xml_char] rejects the control character #x8. *)
let lemma_is_xml_char_reject_8 () : Lemma
  (ensures is_xml_char (FStar.Char.char_of_int 0x8) == false)
  = assert (FStar.Char.int_of_char (FStar.Char.char_of_int 0x8) == 0x8);
    assert_norm (is_xml_cp 0x8 == false)

(** [is_xml_char] rejects the control character #xB. *)
let lemma_is_xml_char_reject_b () : Lemma
  (ensures is_xml_char (FStar.Char.char_of_int 0xB) == false)
  = assert (FStar.Char.int_of_char (FStar.Char.char_of_int 0xB) == 0xB);
    assert_norm (is_xml_cp 0xB == false)

(** [is_xml_char] rejects the control character #xC. *)
let lemma_is_xml_char_reject_c () : Lemma
  (ensures is_xml_char (FStar.Char.char_of_int 0xC) == false)
  = assert (FStar.Char.int_of_char (FStar.Char.char_of_int 0xC) == 0xC);
    assert_norm (is_xml_cp 0xC == false)

(** [is_xml_char] rejects the control character #xE. *)
let lemma_is_xml_char_reject_e () : Lemma
  (ensures is_xml_char (FStar.Char.char_of_int 0xE) == false)
  = assert (FStar.Char.int_of_char (FStar.Char.char_of_int 0xE) == 0xE);
    assert_norm (is_xml_cp 0xE == false)

(** [is_xml_char] rejects the noncharacter #xFFFE. *)
let lemma_is_xml_char_reject_fffe () : Lemma
  (ensures is_xml_char (FStar.Char.char_of_int 0xFFFE) == false)
  = assert (FStar.Char.int_of_char (FStar.Char.char_of_int 0xFFFE) == 0xFFFE);
    assert_norm (is_xml_cp 0xFFFE == false)

(** [is_xml_char] rejects the noncharacter #xFFFF. *)
let lemma_is_xml_char_reject_ffff () : Lemma
  (ensures is_xml_char (FStar.Char.char_of_int 0xFFFF) == false)
  = assert (FStar.Char.int_of_char (FStar.Char.char_of_int 0xFFFF) == 0xFFFF);
    assert_norm (is_xml_cp 0xFFFF == false)

(** [is_xml_char] rejects the surrogate U+D800 at the code-point level
    (already false via the [#xD800-#xDFFF] gap in the [Char] bounds; a
    surrogate is NOT a representable [char], so this is stated over
    [is_xml_cp] rather than [char_of_int], which would be ill-typed). *)
let lemma_is_xml_char_reject_surrogate () : Lemma
  (ensures is_xml_cp 0xD800 == false)
  = assert_norm (is_xml_cp 0xD800 == false)


(** The maximum digit count for a character reference.  The largest scalar
    U+10FFFF is 7 hex digits / 7 decimal digits; 10 bounds both comfortably. *)
let xml_max_charref_len : pos = 10

(** Lemma: every [FStar.Char.char] code point is a valid scalar ([is_valid_cp]).
    Follows from the [char_code] type bound ([< 0xd7ff] or [0xe000..0x10ffff],
    fstar-proofs §46), which is definitionally [is_valid_cp] plus the
    trivially-true [>= 0] conjunct.  The body cites the bound explicitly
    (not a bare [()], finding N2). *)
let lemma_valid_cp_of_char (c: FStar.Char.char) : Lemma
  (is_valid_cp (FStar.Char.int_of_char c))
  = let cp = FStar.Char.int_of_char c in
    FStar.Char.char_of_u32_of_char c;
    assert (cp < 0xD7FF \/ (cp >= 0xE000 /\ cp <= 0x10FFFF))

(** Lemma: [mk_char] roundtrips every [char] (its code point is valid, so
    [char_of_int] reconstructs it — the [char_of_u32_of_char] primitive). *)
let lemma_mk_char_of_char (c: FStar.Char.char) : Lemma
  (mk_char (FStar.Char.int_of_char c) == Some c)
  = FStar.Char.char_of_u32_of_char c;
    ()

(** Decimal character reference: [&#DDD;] → code point (XML 1.0 §4.1).

    Built by composing the proven [digits_to_int] inside the [&#] … [;]
    markers via [between], then mapping the decoded integer through [mk_char]
    (forward) and [int_of_char] (backward).  The [is_valid_cp] predicate is
    both the [digits_to_int] value guard (rejecting surrogates and above-max
    during digit decode) and the [mk_char] validity gate, so no [admit] is
    needed for [char_of_int] (fstar-proofs §46). *)
let char_ref_decimal : codec char =
  map_
    (fun (cp: int) -> mk_xml_char cp)
    (fun (c: char) -> Some (FStar.Char.int_of_char c))
    (between (text "&#") (byte_val 0x3Buy) (digits_to_int xml_max_charref_len is_valid_cp))

(* --- Hexadecimal digit codec (base-16 analogue of [digits_to_int]). --- *)

(** True iff [b] is a hexadecimal digit (0-9, A-F, a-f). *)
let is_hex_digit (b: byte) : bool =
  let v = U8.v b in
  (0x30 <= v && v <= 0x39) || (0x41 <= v && v <= 0x46) || (0x61 <= v && v <= 0x66)

(** The numeric value of a hexadecimal digit (0-15). *)
let hex_digit_value (b: byte) : int =
  let v = U8.v b in
  if 0x30 <= v && v <= 0x39 then v - 0x30
  else if 0x41 <= v && v <= 0x46 then v - 0x41 + 10
  else v - 0x61 + 10

(** The lowercase hexadecimal digit byte for [d < 16]. *)
let hex_digit_byte (d: nat{d < 16}) : byte =
  if d < 10 then U8.uint_to_t (0x30 + d) else U8.uint_to_t (0x61 + d - 10)

(** Encode a nat to its lowercase hexadecimal digit list (no leading zeros). *)
let rec hex_digits_encode (n: nat) : Tot (list byte) (decreases n) =
  if n < 16 then [hex_digit_byte n]
  else hex_digits_encode (n / 16) @ [hex_digit_byte (n % 16)]

(** True iff every byte is a hexadecimal digit. *)
let all_hex_digits (ds: list byte) : bool = List.Tot.for_all is_hex_digit ds

(** Accumulate the integer value of a hex-digit list, base 16, left-to-right. *)
let rec acc_hex (ds: list byte) (a: int) : Tot int (decreases ds) =
  match ds with
  | [] -> a
  | d :: tl -> acc_hex tl (a * 16 + hex_digit_value d)

(** Bounded greedy hex-digit scanner (mirrors [digits_to_int_decode_go]). *)
let rec hex_decode_go (s: byte_seq) (k: nat) (a: int) (i: nat)
  : Tot (decode_result int) (decreases k)
  = if k = 0 then Inr (a, i)
    else if i >= Seq.length s then Inr (a, i)
    else
      let b = Seq.index s i in
      if is_hex_digit b then hex_decode_go s (k-1) (a * 16 + hex_digit_value b) (i+1)
      else if i = 0 then Inl (mk_decode_error ExpectedPredicate 0)
      else Inr (a, i)

(** Decode a hex-digit run to an integer, bounded by [max_len] digits. *)
let hex_decode (max_len: nat) (s: byte_seq) : decode_result int =
  hex_decode_go s max_len 0 0

(** [acc_hex] distributes over append. *)
let rec lemma_acc_hex_append (ds1 ds2: list byte) (a: int) : Lemma
  (ensures acc_hex (ds1 @ ds2) a == acc_hex ds2 (acc_hex ds1 a))
  (decreases ds1)
  = match ds1 with
    | [] -> ()
    | d :: tl -> lemma_acc_hex_append tl ds2 (a * 16 + hex_digit_value d)

(** [acc_hex] of the canonical hex encoding of [n] is [n]. *)
let rec lemma_acc_hex_encode (n: nat) : Lemma
  (ensures acc_hex (hex_digits_encode n) 0 == n)
  (decreases n)
  = if n < 16 then ()
    else begin
      let n_div = n / 16 in let n_mod = n % 16 in
      let d = hex_digit_byte n_mod in
      lemma_acc_hex_encode n_div;
      lemma_acc_hex_append (hex_digits_encode n_div) [d] 0;
      ()
    end

(** [all_hex_digits] distributes over append. *)
let rec lemma_all_hex_digits_append (ds1 ds2: list byte) : Lemma
  (ensures all_hex_digits (ds1 @ ds2) == (all_hex_digits ds1 && all_hex_digits ds2))
  (decreases ds1)
  = match ds1 with
    | [] -> ()
    | d :: tl -> lemma_all_hex_digits_append tl ds2

(** Every byte of a canonical hex encoding is a hex digit. *)
let rec lemma_all_hex_digits_encode (n: nat) : Lemma
  (ensures all_hex_digits (hex_digits_encode n))
  (decreases n)
  = if n < 16 then ()
    else begin
      let n_div = n / 16 in let n_mod = n % 16 in
      let d = hex_digit_byte n_mod in
      lemma_all_hex_digits_encode n_div;
      lemma_all_hex_digits_append (hex_digits_encode n_div) [d];
      ()
    end

(** Shift lemma: decoding from offset [i] on a hex-digit prefix equals
    decoding the suffix slice from 0 (offset-shifted result).  Mirrors
    [Data.Codec.Types.lemma_digits_decode_shift]. *)
#push-options "--z3rlimit 80"
let rec lemma_hex_decode_shift (s: byte_seq) (k: nat) (i: nat) (a: int) : Lemma
  (requires i < Seq.length s /\ is_hex_digit (Seq.index s i))
  (ensures
    hex_decode_go s k a i
    == (match hex_decode_go (Seq.slice s i (Seq.length s)) k a 0 with
        | Inl err -> Inl ({err with err_pos = err.err_pos + i})
        | Inr (v, n) -> Inr (v, n + i)))
  (decreases k)
  = let sliced = Seq.slice s i (Seq.length s) in
    if k > 0 then begin
      let a' = a * 16 + hex_digit_value (Seq.index s i) in
      let cnt1 = i + 1 in
      if cnt1 >= Seq.length s then ()
      else if is_hex_digit (Seq.index s cnt1) then begin
        let k' = k - 1 in
        lemma_hex_decode_shift s k' cnt1 a';
        lemma_hex_decode_shift sliced k' 1 a';
        assert (hex_decode_go s k a i == hex_decode_go s k' a' cnt1);
        ()
      end else ()
    end else ()
#pop-options

(** Process a concrete hex-digit list through the decoder (mirrors
    [Data.Codec.Types.lemma_digits_process_list]). *)
#push-options "--z3rlimit 400"
let rec lemma_hex_process_list (ds: list byte) (r: byte_seq) (k: nat) (a: int) : Lemma
  (requires
    Cons? ds /\
    all_hex_digits ds /\
    List.Tot.length ds <= k /\
    (List.Tot.length ds = k \/ Seq.length r = 0 \/
     (Seq.length r > 0 /\ not (is_hex_digit (Seq.index r 0)))))
  (ensures
    hex_decode_go (Seq.append (seq_of_list ds) r) k a 0
      == Inr (acc_hex ds a, List.Tot.length ds))
  (decreases ds)
  = let s = Seq.append (seq_of_list ds) r in
    let n = List.Tot.length ds in
    match ds with
    | [d] ->
      if k = 1 then ()
      else if Seq.length r = 0 then ()
      else if not (is_hex_digit (Seq.index r 0)) then ()
      else begin
        assert (n = 1);
        assert (k <> 1);
        assert (Seq.length r > 0);
        assert (is_hex_digit (Seq.index r 0));
        assert False
      end
    | d :: tl ->
      let k' = k - 1 in
      let d_val = hex_digit_value d in
      let a' = a * 16 + d_val in
      let tail_input = Seq.append (seq_of_list tl) r in
      assert (Seq.equal (Seq.slice s 1 (Seq.length s)) tail_input);
      assert (is_hex_digit (Seq.index s 0));
      assert (hex_decode_go s k a 0 == hex_decode_go s k' a' 1);
      lemma_hex_decode_shift s k' 1 a';
      assert (List.Tot.length tl <= k');
      lemma_hex_process_list tl r k' a';
      assert (hex_decode_go tail_input k' a' 0 == Inr (acc_hex tl a', List.Tot.length tl));
      assert (hex_decode_go s k' a' 1 == Inr (acc_hex tl a', 1 + List.Tot.length tl));
      assert (acc_hex (d :: tl) a == acc_hex tl a');
      assert (List.Tot.length (d :: tl) == 1 + List.Tot.length tl);
      ()
#pop-options

(** Hex digit roundtrip: the canonical hex encoding of [n] decodes to [n]. *)
#push-options "--z3rlimit 400"
let lemma_hex_decode_encode_roundtrip (max_len: nat) (n: nat) (r: byte_seq) : Lemma
  (requires
    all_hex_digits (hex_digits_encode n) /\
    acc_hex (hex_digits_encode n) 0 == n /\
    List.Tot.length (hex_digits_encode n) <= max_len /\
    (List.Tot.length (hex_digits_encode n) = max_len \/ Seq.length r = 0 \/
     (Seq.length r > 0 /\ not (is_hex_digit (Seq.index r 0)))))
  (ensures hex_decode_go (Seq.append (seq_of_list (hex_digits_encode n)) r) max_len 0 0
           == Inr (n, List.Tot.length (hex_digits_encode n)))
  = lemma_hex_process_list (hex_digits_encode n) r max_len 0
#pop-options

(** Error-position + consumed bound for the hex decoder ([hex_decode_go]).
    Decoding from offset [i] (with [i <= Seq.length s]) never returns an
    error position nor a consumed count beyond [Seq.length s].  Mirrors
    [Data.Codec.Types.lemma_digits_decode_go_len_bound]: recursion on [k]
    only, carrying the offset [i] forward (no slice-length reasoning). *)
#push-options "--z3rlimit 200"
let rec lemma_hex_decode_go_len_bound (s: byte_seq) (k: nat) (a: int) (i: nat) : Lemma
  (requires i <= Seq.length s)
  (ensures (match hex_decode_go s k a i with
            | Inr (_, n) -> n <= Seq.length s
            | Inl err -> err.err_pos <= Seq.length s))
  (decreases k)
  = if k = 0 then ()
    else if i >= Seq.length s then ()
    else begin
      let b = Seq.index s i in
      if is_hex_digit b then begin
        assert (i + 1 <= Seq.length s);
        lemma_hex_decode_go_len_bound s (k-1) (a * 16 + hex_digit_value b) (i+1)
      end
      else ()
    end
#pop-options

(** Error-position bound for [hex_decode]. *)
#push-options "--z3rlimit 200"
let lemma_hex_dec_err_bound (max_len: nat) (s: byte_seq) : Lemma
  (ensures (match hex_decode max_len s with Inl err -> err.err_pos <= Seq.length s | _ -> True))
  = lemma_hex_decode_go_len_bound s max_len 0 0
#pop-options

(** Consumed-count bound for [hex_decode]. *)
#push-options "--z3rlimit 200"
let lemma_hex_dec_consumed_bound (max_len: nat) (s: byte_seq) : Lemma
  (ensures (match hex_decode max_len s with Inr (_, n) -> n <= Seq.length s | _ -> True))
  = lemma_hex_decode_go_len_bound s max_len 0 0
#pop-options

(** Well-formed value for [hex_digits_to_int]: [v] satisfies [f], is
    non-negative, and its canonical hex encoding is at most [max_len] digits. *)
let hex_digits_wfcv (max_len: pos) (f: int -> bool) (v: int) : bool =
  f v && v >= 0 && List.Tot.length (hex_digits_encode (nat_of_int v)) <= max_len

(** Suffix condition for [hex_digits_to_int]: the encoded run fills the bound,
    or the suffix is empty, or the next byte is not a hex digit. *)
let hex_digits_rest_cond (max_len: pos) (f: int -> bool) (v: int) (r: byte_seq) : prop =
  let n_val = nat_of_int v in
  List.Tot.length (hex_digits_encode n_val) = max_len \/
  Seq.length r = 0 \/
  (Seq.length r > 0 /\ not (is_hex_digit (Seq.index r 0)))

(** Roundtrip for [hex_digits_to_int] (the [custom] signature): a well-formed
    value encodes and decodes to itself, consuming exactly the encoded length. *)
#push-options "--z3rlimit 800"
let lemma_hex_digits_roundtrip (max_len: pos) (f: int -> bool) (v: int) (r: byte_seq) : Lemma
  (requires
    hex_digits_wfcv max_len f v /\
    v >= 0 /\
    hex_digits_rest_cond max_len f v r)
  (ensures hex_decode max_len (Seq.append (seq_of_list (hex_digits_encode (nat_of_int v))) r)
           == Inr (v, Seq.length (seq_of_list (hex_digits_encode (nat_of_int v)))))
  = let n_val = nat_of_int v in
    lemma_acc_hex_encode n_val;
    lemma_all_hex_digits_encode n_val;
    assert (n_val == v);
    lemma_hex_decode_encode_roundtrip max_len n_val r;
    assert (Seq.length (seq_of_list (hex_digits_encode n_val)) == List.Tot.length (hex_digits_encode n_val));
    ()
#pop-options

(** [hex_digits_to_int] — a bounded-greedy base-16 integer codec (the hex
    analogue of [digits_to_int], fstar-proofs §43), built via [custom] so its
    roundtrip is the explicit [lemma_hex_digits_roundtrip] rather than
    re-asserting the opaque [map_]/[between] sub-fields (fstar-proofs §18). *)
let hex_digits_to_int (max_len: pos) (f: int -> bool) : codec int =
  custom
    (hex_decode max_len)
    (fun v -> seq_of_list (hex_digits_encode (nat_of_int v)))
    (hex_digits_wfcv max_len f)
    (fun _ -> True)
    (hex_digits_rest_cond max_len f)
    (fun v r -> lemma_hex_digits_roundtrip max_len f v r)
    (lemma_hex_dec_err_bound max_len)
    (lemma_hex_dec_consumed_bound max_len)

(** Hexadecimal character reference: [&#xHHH;] → code point (XML 1.0 §4.1).

    Composes [hex_digits_to_int] inside the [&#x] … [;] markers via [between],
    then maps the decoded integer through [mk_char].  The [is_valid_cp] guard
    rejects surrogates and above-max code points during digit decode. *)
let char_ref_hex : codec char =
  map_
    (fun (cp: int) -> mk_xml_char cp)
    (fun (c: char) -> Some (FStar.Char.int_of_char c))
    (between (text "&#x") (byte_val 0x3Buy) (hex_digits_to_int xml_max_charref_len is_valid_cp))

(* ========================================================================
   Character-reference roundtrip + rejection lemmas (concrete vectors,
   fstar-proofs §47 path (b)).
   ======================================================================== *)

(** [&#65;] decodes to [A] (U+0041) and roundtrips.

    A bare [()] body discharges here (finding N4): the DECIMAL path's
    decoder is [digits_to_int], whose [.dec] ([digits_to_int_decode_go])
    carries the value guard [f] ([is_valid_cp]) INLINE — the digit run
    [65] reduces to [65] with [is_valid_cp 65] discharged in one step, so
    the SMT sees through the [between]/[map_] shell without an explicit
    chain.  The HEX sibling ([lemma_char_ref_hex_roundtrip] below) does NOT
    share this — its [hex_digits_to_int] [.dec] ([hex_decode_go]) has NO [f]
    gate, so the opaque [map_]/[between] composition needs the explicit
    list-level chain (fstar-proofs §52 Pitfall 3). *)
#push-options "--z3rlimit 400"
let lemma_char_ref_decimal_roundtrip () : Lemma
  (ensures char_ref_decimal.dec (char_ref_decimal.enc 'A')
           == Inr ('A', Seq.length (char_ref_decimal.enc 'A')))
  = ()
#pop-options

(** [&#x41;] decodes to [A] (U+0041) and roundtrips.

    Proven by a direct list-level chain: the [&#x] and [;] markers surround
    the hex digits [41], which [lemma_hex_decode_encode_roundtrip] decodes
    back to [0x41], then [mk_char] reconstructs [A] ([lemma_mk_char_of_char]).
    This avoids the opaque [map_]/[between] [.roundtrip] field (fstar-proofs
    §15/§18 — [.dec]/[.enc] are transparent, [.roundtrip] is not). *)
#push-options "--z3rlimit 800"
let lemma_char_ref_hex_roundtrip () : Lemma
  (ensures char_ref_hex.dec (char_ref_hex.enc 'A')
           == Inr ('A', Seq.length (char_ref_hex.enc 'A')))
  = let code = FStar.Char.int_of_char 'A' in
    assert (code == 0x41);
    lemma_acc_hex_encode 0x41;
    lemma_all_hex_digits_encode 0x41;
    lemma_hex_decode_encode_roundtrip xml_max_charref_len 0x41
      (seq_of_list [0x3Buy]);
    lemma_mk_char_of_char 'A';
    assert_norm (hex_digits_encode 0x41 == [0x34uy; 0x31uy]);
    assert (hex_decode xml_max_charref_len (Seq.append (seq_of_list [0x34uy;0x31uy]) (seq_of_list [0x3Buy]))
            == Inr (0x41, 2));
    ()
#pop-options

(** A surrogate code point (U+D800 = 55296) is rejected at the [mk_char] gate
    ([is_valid_cp 55296 == false] — the code-point-bound soundness property,
    fstar-proofs §46). *)
#push-options "--z3rlimit 200"
let lemma_char_ref_reject_surrogate () : Lemma
  (ensures is_valid_cp 55296 == false /\ mk_char 55296 == None)
  = assert_norm (is_valid_cp 55296 == false)
#pop-options

(** An above-max code point (U+110000 = 1114112) is rejected at the [mk_char]
    gate ([is_valid_cp 1114112 == false]). *)
#push-options "--z3rlimit 200"
let lemma_char_ref_reject_above_max () : Lemma
  (ensures is_valid_cp 1114112 == false /\ mk_char 1114112 == None)
  = assert_norm (is_valid_cp 1114112 == false)
#pop-options

(** Quotes *)

(** Double quote (0x22). *)
let dquote : codec unit = byte_val 0x22uy


(* ========================================================================
   The [char_ref] choice and [text_char] (XML 1.0 §4.1 / Char production).

   [char_ref] = [&#DDD;] | [&#xHHH;], dispatched on the byte AFTER the
   shared [&#] prefix ([x] → hex, [0-9] → decimal).  [text_char] = a single
   [Char]: a literal (not [<], not [&]) | [entity_ref] | [char_ref], all
   resolving to a [FStar.Char.char].

   All choices are built from the PROVEN combinators ([then_drop]/[alt]/
   [drop_then]/[between]/[digits_to_int]/[hex_digits_to_int]/[custom] over
   [one_of]), so each [.roundtrip] field is generic and 0-admit BY
   CONSTRUCTION — no hand-written [list byte -> option …] scanner (§50/§52).
   [alt] dispatches on ONE byte, so each shared prefix ([&#], [&]) is factored
   out with [then_drop]; the discriminating byte ([x] vs digit, [#] vs
   entity-letter) is then the FIRST byte of the inner codec.

   Canonical ENCODING: [char_ref] always encodes via DECIMAL ([&#DDD;]); the
   hex branch is decode-only.  [text_char] encodes a literal byte for
   non-special ASCII ([<] and [&] excluded) and a [char_ref] otherwise.
   Both forms are invertible with [rest_cond = True] (a terminated literal
   has no suffix constraint).
   ======================================================================== *)

(** The byte predicate distinguishing hex ([x]) from decimal ([0-9]). *)
let is_hex_marker (b: byte) : bool = U8.v b = 0x78

(** Hex digit run after the [x] ([xHHH], no [;&#]): [x] + hex digits, as an
    [int] code point. *)
let char_ref_hex_tail : codec int =
  then_drop (byte_val 0x78uy) (hex_digits_to_int xml_max_charref_len is_valid_cp)

(** [char_ref] — a character reference ([&#DDD;] or [&#xHHH;]) as a [char].

    A single [map_] over ONE [between] over ONE [alt] over the digit codecs —
    the same shallow shape as [char_ref_decimal]/[char_ref_hex] (whose concrete
    roundtrips discharge under nix).  [between (text "&#") (byte_val 0x3B)]
    brackets the [alt] over hex ([x] first byte) vs decimal ([0-9] first
    byte); the canonical encoder picks DECIMAL (the [Inr] branch). *)
let char_ref : codec char =
  map_
    (fun (e: either int int) -> match e with Inl cp | Inr cp -> mk_xml_char cp)
    (fun (c: char) -> Some (Inr (FStar.Char.int_of_char c)))
    (between (text "&#") (byte_val 0x3Buy)
      (alt char_ref_hex_tail
        (digits_to_int xml_max_charref_len is_valid_cp)
        is_hex_marker))

(** [&#65;] decodes to [A] (U+0041) via [char_ref] and roundtrips.

    Concrete closed vector proven by chaining the digit roundtrips
    ([lemma_digits_decode_encode_roundtrip]) + [mk_char] reconstruction, NOT a
    bare [()] body (the [alt] dispatch adds enough SMT work that [()] does not
    discharge under nix — fstar-proofs §52 Pitfall 3). *)
#push-options "--z3rlimit 800"
let lemma_char_ref_roundtrip () : Lemma
  (ensures char_ref.dec (char_ref.enc 'A') == Inr ('A', Seq.length (char_ref.enc 'A')))
  = let code = FStar.Char.int_of_char 'A' in
    assert (code == 0x41);
    lemma_valid_cp_of_char 'A';
    lemma_mk_char_of_char 'A';
    lemma_acc_digits_encode_helper 0x41;
    lemma_digits_encode_all_digits_helper 0x41;
    lemma_digits_decode_encode_roundtrip is_valid_cp xml_max_charref_len 0x41
      (seq_of_list [0x3Buy]);
    assert_norm (digits_encode 0x41 == [0x36uy; 0x35uy]);
    ()
#pop-options

(** A truncated decimal character reference ([&#65], missing the terminating
    [;]) is rejected by [char_ref.dec] (the [between] combinator requires the
    [;] byte after the digit run — finding M4 / task 2.3). *)
#push-options "--z3rlimit 400"
let lemma_char_ref_reject_missing_semi () : Lemma
  (ensures (match char_ref.dec (seq_of_list [0x26uy; 0x23uy; 0x36uy; 0x35uy]) with
            | Inl _ -> True | Inr _ -> False))
  = ()
#pop-options

(** A truncated hexadecimal character reference ([&#x], an empty hex run) is
    rejected by [char_ref.dec] (the [hex_digits_to_int] decoder requires at
    least one hex digit before its [;] terminator — finding M4 / task 2.3). *)
#push-options "--z3rlimit 400"
let lemma_char_ref_reject_empty_hex () : Lemma
  (ensures (match char_ref.dec (seq_of_list [0x26uy; 0x23uy; 0x78uy]) with
            | Inl _ -> True | Inr _ -> False))
  = ()
#pop-options

(* ────────────────────────────────────────────────────────────────────────
   [text_char] — a single [Char] production. *)

(** A literal [text_char] byte: ASCII, a valid REC [2] [Char] code point
    ([is_xml_char] — rejects the controls [#x0-#x8]/[#xB]/[#xC]/[#xE-#x1F]),
    and neither [<] (0x3C) nor [&] (0x26).  Because the literal path is a
    single ASCII byte, the noncharacters/surrogates of the [Char] exclusion
    set are unreachable here; they are rejected by [mk_xml_char] on the
    character-reference path (finding M1). *)
let is_text_char_literal (b: byte) : bool =
  let v = U8.v b in
  v < 0x80 && v <> 0x3C && v <> 0x26 && is_xml_cp v

(** Entity bodies WITHOUT the leading [&]: [(value, "name;")] in decoder
    order — the SINGLE source of truth for the five predefined entities
    (XML 1.0 §4.6).  The literals are the post-[&] bodies ([amp;]|[lt;]|
    [gt;]|[quot;]|[apos;]); they remain mutually non-prefix (fstar-proofs
    §43 NOTE on one_of roundtrip scope).  [entity_ref] re-derives the full
    [&…;] form by
    factoring the [&] prefix combinatorially (§53), so there is exactly ONE
    literal set. *)
let entity_body_pairs : list (byte & list byte) =
  [ (0x26uy, [0x61uy;0x6Duy;0x70uy;0x3Buy]);             (* amp; *)
    (0x3Cuy, [0x6Cuy;0x74uy;0x3Buy]);                    (* lt; *)
    (0x3Euy, [0x67uy;0x74uy;0x3Buy]);                    (* gt; *)
    (0x22uy, [0x71uy;0x75uy;0x6Fuy;0x74uy;0x3Buy]);      (* quot; *)
    (0x27uy, [0x61uy;0x70uy;0x6Fuy;0x73uy;0x3Buy]) ]     (* apos; *)

(** [entity_body] encoder: the literal of the first pair keyed by [v]. *)
let entity_body_enc (v: byte) : byte_seq = one_of_enc entity_body_pairs v

(** [entity_body] decoder: the value of the first matching literal. *)
let entity_body_dec (s: byte_seq) : decode_result byte = one_of_dec entity_body_pairs s

(** [entity_body] well-formedness: [v] keys some pair. *)
let entity_body_wfcv (v: byte) : bool = one_of_mem entity_body_pairs v

(** [entity_body] well-formed proposition. *)
let entity_body_wfcv_prop (v: byte) : prop = True

(** [entity_body] suffix condition ([True] — terminated literals). *)
let entity_body_rest_cond (v: byte) (r: byte_seq) : prop = True

(** The five concrete values an entity body can resolve to. *)
let entity_body_mem_cases (v: byte) : prop =
  v = 0x26uy \/ v = 0x3Cuy \/ v = 0x3Euy \/ v = 0x22uy \/ v = 0x27uy

(** Lemma: [entity_body_wfcv v] implies the five-way disjunction. *)
let lemma_entity_body_mem_cases (v: byte) : Lemma
  (requires entity_body_wfcv v)
  (ensures entity_body_mem_cases v)
  = ()

(** The literal lists for the five entity bodies (single source of truth). *)
let e_body_amp  : list byte = [0x61uy;0x6Duy;0x70uy;0x3Buy]
let e_body_lt   : list byte = [0x6Cuy;0x74uy;0x3Buy]
let e_body_gt   : list byte = [0x67uy;0x74uy;0x3Buy]
let e_body_quot : list byte = [0x71uy;0x75uy;0x6Fuy;0x74uy;0x3Buy]
let e_body_apos : list byte = [0x61uy;0x70uy;0x6Fuy;0x73uy;0x3Buy]

(** Roundtrip for [entity_body]: each value encodes to its body literal and
    roundtrips (§4.6).  The [&] prefix is factored out of [entity_ref]
    (§53), so this body roundtrip is the shared core. *)
#push-options "--z3rlimit 400"
let lemma_entity_body_roundtrip (v: byte) (r: byte_seq) : Lemma
  (requires entity_body_wfcv v)
  (ensures entity_body_dec (entity_body_enc v `Seq.append` r)
           == Inr (v, Seq.length (entity_body_enc v)))
  = lemma_entity_body_mem_cases v;
    if v = 0x26uy then begin
      assert (entity_body_enc v == seq_of_list e_body_amp);
      lemma_bytes_self_prefix_spec e_body_amp r; ()
    end else if v = 0x3Cuy then begin
      lemma_one_of_bytes_mismatch e_body_amp e_body_lt r;
      lemma_bytes_self_prefix_spec e_body_lt r; ()
    end else if v = 0x3Euy then begin
      lemma_one_of_bytes_mismatch e_body_amp e_body_gt r;
      lemma_one_of_bytes_mismatch e_body_lt e_body_gt r;
      lemma_bytes_self_prefix_spec e_body_gt r; ()
    end else if v = 0x22uy then begin
      lemma_one_of_bytes_mismatch e_body_amp e_body_quot r;
      lemma_one_of_bytes_mismatch e_body_lt e_body_quot r;
      lemma_one_of_bytes_mismatch e_body_gt e_body_quot r;
      lemma_bytes_self_prefix_spec e_body_quot r; ()
    end else begin
      lemma_one_of_bytes_mismatch e_body_amp e_body_apos r;
      lemma_one_of_bytes_mismatch e_body_lt e_body_apos r;
      lemma_one_of_bytes_mismatch e_body_gt e_body_apos r;
      lemma_one_of_bytes_mismatch e_body_quot e_body_apos r;
      lemma_bytes_self_prefix_spec e_body_apos r; ()
    end
#pop-options

(** Error-position bound for [entity_body_dec] (finding N1).

    [entity_body_dec] is [one_of_dec entity_body_pairs], i.e. a chain of
    [bytes_decode lit s] attempts.  Each FAILED [bytes_decode] error carries
    [err_pos = 0] (the [codec] record's decoder contract, the [err_err_pos]
    field bound — [Data.Codec.Types] line ~127), and the final [one_of_dec [] s]
    branch returns [err_pos = 0]; hence every [Inl] has [err_pos = 0 <=
    Seq.length s].  This follows from the CROSS-MODULE [one_of_dec] contract
    (fstar-proofs §15/§58), not a local scan — [entity_body_dec] is opaque to
    SMT here, so the body is a bare [()] discharging the [codec]-record bound.
    (A codec-exported [lemma_one_of_dec_err_bound] would make this local; that
    is deferred to record-codec Stage 3 — see the [one_of] NOTE in
    [Data.Codec.Types].) *)
let lemma_entity_body_dec_err_bound (s: byte_seq) : Lemma
  (ensures (match entity_body_dec s with Inl err -> err.err_pos <= Seq.length s | _ -> True))
  = ()

(** Consumed-count bound for [entity_body_dec] (finding N1).

    A SUCCESSFUL [one_of_dec] returns [n = List.Tot.length lit] for the first
    matching literal (the [bytes_decode] success contract,
    [lemma_bytes_decode_inr_consumed] in [Data.Codec.Types]); since that
    literal self-prefix matches within [s], [n = |lit| <= Seq.length s].
    Discharged by the same CROSS-MODULE [one_of_dec] reasoning as the error
    bound above (fstar-proofs §15/§58). *)
let lemma_entity_body_dec_consumed_bound (s: byte_seq) : Lemma
  (ensures (match entity_body_dec s with Inr (_, n) -> n <= Seq.length s | _ -> True))
  = ()

(** [entity_body] — the five predefined entities WITHOUT the [&] prefix
    ([amp;]|[lt;]|[gt;]|[quot;]|[apos;]) as a [byte]. *)
let entity_body : codec byte =
  custom
    entity_body_dec entity_body_enc
    entity_body_wfcv entity_body_wfcv_prop entity_body_rest_cond
    (fun v r -> lemma_entity_body_roundtrip v r)
    lemma_entity_body_dec_err_bound
    lemma_entity_body_dec_consumed_bound

(** [entity_ref] — the choice over the five predefined entity references
    ([&amp;]|[&lt;]|[&gt;]|[&quot;]|[&apos;]), factored as the [&] prefix
    plus the [entity_body] literal (fstar-proofs §53).  The combinatoric
    [then_drop] over [byte_val] + [entity_body] is the canonical form;
    the public [entity_enc]/[entity_dec]/[entity_wfcv] helpers below are
    TRANSPARENT definitions over [entity_body] so their roundtrip proof
    chains [lemma_entity_body_roundtrip] without touching [entity_ref]'s
    opaque [map_]/[product] fields (§15/§18). *)
let entity_ref : codec byte = then_drop (byte_val 0x26uy) entity_body

(** [entity_ref] encoder: the [&] prefix (1 byte) plus the body literal. *)
let entity_enc (v: byte) : byte_seq =
  Seq.append (Seq.create 1 0x26uy) (entity_body_enc v)

(** [entity_ref] decoder: the [&] prefix (1 byte) then the [entity_body]
    literal.  The body error position is shifted by the consumed prefix. *)
let entity_dec (s: byte_seq) : decode_result byte =
  if Seq.length s >= 1 && Seq.index s 0 = 0x26uy then
    match entity_body_dec (Seq.slice s 1 (Seq.length s)) with
    | Inl err -> Inl ({err with err_pos = err.err_pos + 1})
    | Inr (v, n) -> Inr (v, n + 1)
  else Inl (mk_decode_error (ExpectedByte 0x26uy) 0)

(** [entity_ref] well-formedness: [v] keys some entity body. *)
let entity_wfcv (v: byte) : bool = entity_body_wfcv v

(** Roundtrip for [entity_ref]: each entity value encodes ([&] + body) and
    roundtrips.  Chains the [&]-prefix algebra ([Seq.create 1 0x26uy]
    leading byte + 1 consumed) through the proven [entity_body] roundtrip. *)
#push-options "--z3rlimit 400"
let lemma_entity_ref_roundtrip (v: byte) (r: byte_seq) : Lemma
  (requires entity_wfcv v)
  (ensures entity_dec (entity_enc v `Seq.append` r) == Inr (v, Seq.length (entity_enc v)))
  = let body = entity_body_enc v in
    let body_r = body `Seq.append` r in
    lemma_entity_body_roundtrip v r;
    Seq.append_assoc (Seq.create 1 0x26uy) body r;
    lemma_slice_cons_spec 0x26uy body_r;
    ()
#pop-options

(** [char_ref] body after the [&]: [#] + hex-or-decimal + [;] as a [char]. *)
let char_ref_hash_body : codec char =
  map_
    (fun (e: either int int) -> match e with Inl cp | Inr cp -> mk_xml_char cp)
    (fun (c: char) -> Some (Inr (FStar.Char.int_of_char c)))
    (between (byte_val 0x23uy) (byte_val 0x3Buy)
      (alt char_ref_hex_tail
        (digits_to_int xml_max_charref_len is_valid_cp)
        is_hex_marker))

(** The [&]-family: [&amp;]-style entity or [&#…;] char ref, as a [char].
    The [&] prefix is factored out; [alt] dispatches [#] → char ref vs
    entity-letter → entity on the first byte after [&]. *)
let amp_char : codec char =
  map_
    (fun (e: either byte char) -> match e with Inl b -> Some (FStar.Char.char_of_int (U8.v b)) | Inr c -> Some c)
    (fun (c: char) ->
      let code = FStar.Char.int_of_char c in
      if code = 0x26 || code = 0x3C || code = 0x3E || code = 0x22 || code = 0x27 then
        Some (Inl (Data.Codec.char_to_byte c))
      else Some (Inr c))
    (then_drop (byte_val 0x26uy)
      (alt entity_body char_ref_hash_body (fun b -> U8.v b <> 0x23)))

(** A literal [text_char] byte mapped to a [char]. *)
let literal_char : codec char =
  map_
    (fun (b: byte) -> Some (FStar.Char.char_of_int (U8.v b)))
    (fun (c: char) ->
      let code = FStar.Char.int_of_char c in
      if code < 0x80 then Some (Data.Codec.char_to_byte c) else None)
    (satisfy is_text_char_literal)

(** [text_char] — a single XML [Char] (literal | entity | char ref) as a
    [char].  [alt] dispatches on the first byte: literal (not [&]) vs the
    [&]-family.  The canonical encoder emits a literal byte for non-special
    ASCII and an entity/char-ref for the special chars. *)
let text_char : codec char =
  map_
    (fun (e: either char char) -> match e with Inl c -> Some c | Inr c -> Some c)
    (fun (c: char) ->
      if is_text_char_literal (Data.Codec.char_to_byte c) then Some (Inl c)
      else Some (Inr c))
    (alt literal_char amp_char (fun b -> U8.v b <> 0x26))

(** [&#65;] and a literal roundtrip via [text_char] (concrete vectors). *)
#push-options "--z3rlimit 400"
let lemma_text_char_roundtrip () : Lemma
  (ensures text_char.dec (text_char.enc 'A') == Inr ('A', Seq.length (text_char.enc 'A')))
  = ()
#pop-options

(** [text_char] rejects a REC [2] control byte ([#x1]) on the literal path
    ([is_text_char_literal] is now [is_xml_cp]-gated — finding M1). *)
#push-options "--z3rlimit 200"
let lemma_text_char_reject_control () : Lemma
  (ensures (match text_char.dec (seq_of_list [0x01uy]) with
            | Inl _ -> True | Inr _ -> False))
  = assert_norm (is_text_char_literal 0x01uy == false);
    ()
#pop-options

(** [literal_char] rejects a REC [2] control byte ([#x1]) — the [satisfy]
    gate's [wfcv] is [is_text_char_literal], now [is_xml_cp]-gated. *)
#push-options "--z3rlimit 200"
let lemma_literal_char_reject_control () : Lemma
  (ensures (match literal_char.dec (seq_of_list [0x01uy]) with
            | Inl _ -> True | Inr _ -> False))
  = assert_norm (is_text_char_literal 0x01uy == false);
    ()
#pop-options

(** [char_ref] rejects a decimal reference to a REC [2] control character
    ([&#1;] → U+0001): [mk_xml_char 1 == None] forwards a parse error
    (finding M1 — the [&#…;] path shares the [mk_xml_char] gate). *)
#push-options "--z3rlimit 400"
let lemma_char_ref_reject_control () : Lemma
  (ensures (match char_ref.dec (seq_of_list [0x26uy; 0x23uy; 0x31uy; 0x3Buy]) with
            | Inl _ -> True | Inr _ -> False))
  = assert_norm (is_xml_cp 1 == false);
    assert_norm (mk_xml_char 1 == None);
    ()
#pop-options

(** A REC [2] noncharacter ([#xFFFE]/[#xFFFF]) is rejected at the [mk_xml_char]
    gate ([is_xml_cp … == false] — the noncharacter exclusion, the [Char]
    [#xFFFD] upper bound).  Stated at the gate level (as
    [lemma_char_ref_reject_surrogate]/[lemma_char_ref_reject_above_max] do):
    the hexadecimal character-reference decoder reduces opaquely through the
    [hex_digits_to_int] [custom] scan (no [f] gate in its [.dec]), so the
    gate-level fact is the transparent, 0-admit proof (fstar-proofs §52
    Pitfall 4 / §18). *)
#push-options "--z3rlimit 200"
let lemma_char_ref_reject_noncharacter () : Lemma
  (ensures is_xml_cp 0xFFFE == false /\ is_xml_cp 0xFFFF == false /\
           mk_xml_char 0xFFFE == None /\ mk_xml_char 0xFFFF == None)
  = assert_norm (is_xml_cp 0xFFFE == false);
    assert_norm (is_xml_cp 0xFFFF == false);
    assert_norm (mk_xml_char 0xFFFE == None);
    assert_norm (mk_xml_char 0xFFFF == None)
#pop-options
