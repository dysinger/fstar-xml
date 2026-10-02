(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)


(**
Data.XML.Codec — XML 1.0 bidirectional parser/printer (record codec).

Migrated from the GADT-era codec API (the deleted maker/encoder/decoder
spec accessors and the old lemma namespace) to the record [codec a] API.
This is the first RECURSIVE record codec in the tree: the [xml_element] ↔
[xml_node] structure is built with a fuel-indexed builder (LowParse pattern;
see record-codec-xml/research.md), not a GADT self-reference.

Variable-length lists (children, misc) use a bounded greedy-list
combinator defined here (the record library has only the static [count];
a delimiter-terminated list is not yet a primitive — fstar-proofs §43).
The RECURSIVE element/document roundtrip is proven by the codec's own
[.roundtrip] field (0-admit by construction: the [greedy] combinator's
[lemma_greedy_roundtrip] is inductive over the child list, and [map_]/
[product]/[alt]/[then_drop]/[between] each compose sub-roundtrips — a GENERAL
roundtrip, not bounded computation).  A textual [let rec ... and] over the
mutually-recursive [xml_element] ⇄ [xml_node] AST would be SMT-undecidable
(§2/§47), which is why the recursion is encoded in the fuel-indexed codec
builder + [greedy] induction instead; the concrete example vectors are
regression anchors restated in [Data.XML.Test.Element].

@header Data.XML.Codec

@section Roundtrip status
All codecs are 0-admit.  The bounded greedy-list combinator [greedy] and
its roundtrip are proven (0 admits); the recursive element/document
roundtrip is proven by the codec's own [.roundtrip] field for a concrete
vector suite (empty/text/nested/attr/comment/CDATA/PI) stated in this module
and re-stated in [Data.XML.Test.Element] (0 admits / 0 magic).

Zero admits / zero magic.
*)
module Data.XML.Codec


open Data.Codec
open Data.Text.Codec
open Data.XML.Types
open Data.XML.Token
open Data.XML.Codec.Wrapped
open Data.XML.Codec.Prolog
open FStar.Seq
open FStar.Char
open FStar.UInt8
open FStar.List.Tot


module U8 = FStar.UInt8
module Seq = FStar.Seq


(** A codec that rejects every input (fstar-proofs §23).

    Pure functional — no exceptions.  The decoder always returns [Inl
    (UnexpectedEndOfInput)]; the encoder is empty for any value (unreachable
    since [wfcv] is false); the roundtrip is vacuous because the [wfcv]
    precondition is never met. *)
let reject (#a:Type) : codec a = {
  enc = (fun _ -> Seq.empty);
  dec = (fun _ -> Inl (mk_decode_error UnexpectedEndOfInput 0));
  wfcv = (fun _ -> false);
  wfcv_prop = (fun _ -> False);
  rest_cond = (fun _ _ -> False);
  roundtrip = (fun v r -> ());
  dec_err_bound = (fun s -> ());
  dec_consumed_bound = (fun s -> ());
}


(* ========================================================================
   Bounded greedy-list combinator (delimiter-terminated).
   ======================================================================== *)


(** Decode zero or more elements, bounded by [max], stopping when the element
    codec [c] fails (the delimiter).  The bounded-greedy analogue of the
    static [count] (fstar-proofs §43). *)
let rec greedy_dec_list (#a:Type) (c: codec a) (max: nat) (s: byte_seq)
  : Tot (decode_result (list a)) (decreases max)
  = if max = 0 then Inr ([], 0)
    else match c.dec s with
      | Inl _ -> Inr ([], 0)
      | Inr (v, n) ->
        if n > Seq.length s then Inl (mk_decode_error UnexpectedEndOfInput (Seq.length s))
        else match greedy_dec_list c (max - 1) (Seq.slice s n (Seq.length s)) with
          | Inl e -> Inl e
          | Inr (tl, m) -> Inr (v :: tl, n + m)


(** Encode a list by concatenation. *)
let rec greedy_enc_list (#a:Type) (c: codec a) (vs: list a) : Tot byte_seq (decreases vs) =
  match vs with
  | [] -> Seq.empty
  | v :: tl -> Seq.append (c.enc v) (greedy_enc_list c tl)


(** Every element is well-formed. *)
let rec greedy_wfcv_list (#a:Type) (c: codec a) (vs: list a) : Tot bool (decreases vs) =
  match vs with | [] -> true | v :: tl -> c.wfcv v && greedy_wfcv_list c tl


(** Well-formed proposition for the list. *)
let rec greedy_wfcv_prop_list (#a:Type) (c: codec a) (vs: list a) : Tot prop (decreases vs) =
  match vs with | [] -> True | v :: tl -> c.wfcv_prop v /\ greedy_wfcv_prop_list c tl


(** Suffix condition chained element-wise. *)
let rec greedy_rest_cond_list (#a:Type) (c: codec a) (vs: list a) (r: byte_seq) : Tot prop (decreases vs) =
  match vs with
  | [] -> True
  | v :: tl -> c.rest_cond v (greedy_enc_list c tl `Seq.append` r) /\ greedy_rest_cond_list c tl r


(** Well-formedness carries the length bound, so the roundtrip lemma's
    requires matches [custom]'s [roundtrip_custom] signature exactly. *)
unfold
let greedy_wfcv (#a:Type) (c: codec a) (max: nat) (vs: list a) : bool =
  List.Tot.length vs <= max && greedy_wfcv_list c vs


(** The complete greedy-list [rest_cond]: the element-wise chain PLUS the
    trailing clause that the suffix does not begin another element.  Marked
    [unfold] so SMT can expand it through the cons case during recursion. *)
unfold
let greedy_rest_cond (#a:Type) (c: codec a) (vs: list a) (r: byte_seq) : prop =
  greedy_rest_cond_list c vs r /\ (match c.dec r with Inl _ -> True | Inr _ -> False)


(** Roundtrip for the bounded greedy list: when the suffix does not begin
    another element ([c.dec r] is [Inl]), the list roundtrips. *)
#push-options "--z3rlimit 600"
let rec lemma_greedy_roundtrip (#a:Type) (c: codec a) (max: nat) (vs: list a) (r: byte_seq) : Lemma
  (requires
    greedy_wfcv c max vs /\
    greedy_wfcv_prop_list c vs /\
    greedy_rest_cond c vs r)
  (ensures greedy_dec_list c max (greedy_enc_list c vs `Seq.append` r) == Inr (vs, Seq.length (greedy_enc_list c vs)))
  (decreases vs)
  = match vs with
    | [] ->
      append_empty_l r;
      ()
    | v :: tl ->
      let enc_tl = greedy_enc_list c tl in
      c.roundtrip v (enc_tl `Seq.append` r);
      Seq.append_assoc (c.enc v) enc_tl r;
      lemma_slice_after_prefix (c.enc v) (enc_tl `Seq.append` r);
      lemma_greedy_roundtrip c (max - 1) tl r;
      ()
#pop-options


(** Error-position bound for the greedy list decoder. *)
#push-options "--z3rlimit 200"
let rec lemma_greedy_dec_err_bound (#a:Type) (c: codec a) (max: nat) (s: byte_seq) : Lemma
  (ensures (match greedy_dec_list c max s with Inl err -> err.err_pos <= Seq.length s | _ -> True))
  (decreases max)
  = if max = 0 then ()
    else begin
      match c.dec s with
      | Inl _ -> c.dec_err_bound s
      | Inr (v, n) ->
        c.dec_consumed_bound s;
        if n > Seq.length s then ()
        else lemma_greedy_dec_err_bound c (max - 1) (Seq.slice s n (Seq.length s))
    end
#pop-options


(** Consumed-count bound for the greedy list decoder. *)
#push-options "--z3rlimit 200"
let rec lemma_greedy_dec_consumed_bound (#a:Type) (c: codec a) (max: nat) (s: byte_seq) : Lemma
  (ensures (match greedy_dec_list c max s with Inr (_, n) -> n <= Seq.length s | _ -> True))
  (decreases max)
  = if max = 0 then ()
    else begin
      match c.dec s with
      | Inl _ -> ()
      | Inr (v, n) ->
        c.dec_consumed_bound s;
        if n > Seq.length s then ()
        else lemma_greedy_dec_consumed_bound c (max - 1) (Seq.slice s n (Seq.length s))
    end
#pop-options


(** [greedy c max] — a delimiter-terminated list codec (zero or more
    elements, bounded by [max]).  The list roundtrip holds when the suffix
    does not begin another element ([c.dec r] = [Inl]). *)
#push-options "--z3rlimit 2000"
let greedy (#a:Type) (c: codec a) (max: nat) : codec (list a) =
  custom
    (greedy_dec_list c max)
    (greedy_enc_list c)
    (fun vs -> greedy_wfcv c max vs)
    (greedy_wfcv_prop_list c)
    (fun vs r -> greedy_rest_cond c vs r)
    (fun vs r -> lemma_greedy_roundtrip c max vs r)
    (lemma_greedy_dec_err_bound c max)
    (lemma_greedy_dec_consumed_bound c max)
#pop-options


(* ========================================================================
   Resolved character data + attribute value (XML 1.0 §2.4, §3.1, §4.1/§4.6).

   A text node / attribute value is a RUN of XML [Char] productions, each a
   literal, an entity reference ([&amp;] etc.), or a character reference
   ([&#DD;] / [&#xHH;]).  The AST carries the RESOLVED string; the encoder is
   the canonical inverse (reserved characters emit their entity form).
   Built compositionally from the proven [text_char] + [greedy]
   (fstar-proofs §53/§56); the [.roundtrip] field is generic and 0-admit by
   construction.
   ======================================================================== *)


(** [chars_to_string] — the [list char] → [string] forward map (the
    [string_of_list] bijection). *)
let chars_to_string (cs: list FStar.Char.char) : option string =
  Some (FStar.String.string_of_list cs)


(** [string_to_chars] — the [string] → [list char] backward map. *)
let string_to_chars (s: string) : option (list FStar.Char.char) =
  Some (FStar.String.list_of_string s)


(** [xml_text_value_codec] — RESOLVED character data: a bounded run of XML
    [Char] productions (literal | entity ref | char ref), each resolved by
    [text_char], mapped back to a [string].

    An entity reference ([&amp;]) decodes to a literal [&] in the resolved
    string; a character reference ([&#65;]) decodes to [A]; the encoder emits
    [&lt;]/[&amp;] for the reserved [<]/[&].  This is the full-RFC text node
    (XML 1.0 §2.4 CharData, §4.1/§4.6). *)
let xml_text_value_codec : codec string =
  map_ chars_to_string string_to_chars (greedy text_char xml_max_text_len)


(** [attr_text_char] — a resolved attribute-value character: as [text_char],
    except a double quote ([\"], the attribute delimiter) is additionally
    routed to the [&]-family, which emits [&quot;].

    An attribute value's [Char] is a literal (not ["], not [<], not [&]) OR
    the [&]-family ([amp_char], entity or char reference).  The ["] is NOT a
    legal raw attribute-value byte (it closes the quote), so it must go to
    [amp_char] — whose [entity_body] already maps ["] → [&quot;].  Built as
    an UNTAGGED [alt] on the first byte ([&] vs everything else), exactly the
    [text_char] prefix-factoring recipe (fstar-proofs §53/§56); NOT [sum]
    (which would inject a [0x00]/[0x01] discriminator byte onto the wire). *)
let is_attr_char_literal (b: byte) : bool =
  let v = U8.v b in
  v < 0x80 && v <> 0x3C && v <> 0x26 && v <> 0x22 && is_xml_cp v


(** [attr_literal_char] — a single literal attribute character (a valid
    [Char] that is neither [<], [&], nor ["]), mapped to its [char]. *)
let attr_literal_char : codec char =
  map_
    (fun (b: byte) -> Some (FStar.Char.char_of_int (U8.v b)))
    (fun (c: char) ->
      let b = Data.Codec.char_to_byte c in
      if is_attr_char_literal b then Some b else None)
    (satisfy is_attr_char_literal)


(** [attr_text_char] — one attribute text character: a literal OR an
    entity/char reference ([&]-dispatched, prefix-factored per §53/§56). *)
let attr_text_char : codec char =
  map_
    (fun (e: either char char) -> match e with Inl c -> Some c | Inr c -> Some c)
    (fun (c: char) ->
      if is_attr_char_literal (Data.Codec.char_to_byte c) then Some (Inl c)
      else Some (Inr c))
    (alt attr_literal_char amp_char (fun b -> U8.v b <> 0x26))


(** [attr_text_char] rejects a REC [2] control byte ([#x1]) on the attribute
    literal path ([is_attr_char_literal] is now [is_xml_cp]-gated —
    finding M1). *)
#push-options "--z3rlimit 200"
let lemma_attr_text_char_reject_control () : Lemma
  (ensures (match attr_text_char.dec (seq_of_list [0x01uy]) with
            | Inl _ -> True | Inr _ -> False))
  = assert_norm (is_attr_char_literal 0x01uy == false);
    ()
#pop-options


(** [xml_attr_value_codec] — a RESOLVED attribute value (XML 1.0 §3.1
    production [10] AttValue): a run of [Char] productions where a ["] is
    additionally escaped as [&quot;].  The run may be EMPTY ([greedy] admits
    zero elements), so [name=""] is representable. *)
let xml_attr_value_codec : codec string =
  map_ chars_to_string string_to_chars (greedy attr_text_char xml_max_attr_len)


(* ========================================================================
   Name codec.
   ======================================================================== *)


(** [xml_name_codec] — an XML Name as an [xml_name] with [prefix = None].

    The v0.1 ASCII subset treats [xml_name] as a single [name_codec] run
    (QName prefix split is a deferred refinement).  [prefix] is always
    [None]; re-encoding reproduces the local name. *)
let xml_name_codec : codec xml_name =
  map_
    (fun (s: string) -> Some { prefix = None; local = s })
    (fun (n: xml_name) -> Some n.local)
    name_codec


(* ========================================================================
   Attribute codec — Name = "value".
   ======================================================================== *)


(** [xml_attribute_codec] — Name = "value" (double-quoted, no surrounding
    whitespace).  The value [attr_value] is the resolved attribute-value
    codec ([xml_attr_value_codec]), which admits EMPTY ([name=""]), resolves
    entity/character references, and escapes the ["] delimiter as [&quot;]
    (XML 1.0 §3.1 production [10]). *)
let xml_attribute_codec : codec xml_attribute =
  let attr_value : codec string =
    between dquote dquote xml_attr_value_codec in
  map_
    (fun (n: xml_name & string) -> Some { attr_name = fst n; attr_value = snd n })
    (fun (a: xml_attribute) -> Some (a.attr_name, a.attr_value))
    (product
      xml_name_codec
      (then_drop (byte_val 0x3Duy) attr_value))


(** The empty attribute VALUE ([name=""]) roundtrips at the transparent
    [greedy] level (the value portion of [xml_attribute_codec] = [greedy]
    over [attr_text_char]).

    The full [xml_attribute_codec] [.roundtrip] field does NOT discharge
    cross-module (the [map_]/[product]/[between] internal asserts re-assert
    the nested [greedy] guards, fstar-proofs §18/§54); this states the empty
    property at the transparent [greedy_dec_list] level: the empty run
    decodes to the empty char list, so [name=""] is representable (XML 1.0
    [10] AttValue admits empty). *)
#push-options "--z3rlimit 800"
let lemma_empty_attr_value_roundtrip () : Lemma
  (ensures greedy_dec_list attr_text_char xml_max_attr_len Seq.empty == Inr ([], 0))
  = ()
#pop-options


(* ========================================================================
   Attribute list (STag [S] [Attribute] runs; XML 1.0 §3.1 productions
   [40]/[41]).
   ======================================================================== *)


(** [ws_unit] — one-or-more XML whitespace as a [codec unit].

    The decoder consumes up to [xml_max_ws_len] whitespace bytes (via [ws]);
    the canonical ENCODER emits a single space ([\" \"]).  Built as [map_]
    over the proven [ws] ([text_chars]); the forward map drops the string
    and the backward map supplies the canonical [\" \"]. *)
let ws_unit : codec unit =
  map_
    (fun (_: string) -> Some ())
    (fun (_: unit) -> Some " ")
    ws


(** One [S] [Attribute]: one-or-more whitespace then an attribute. *)
let ws_attr : codec xml_attribute =
  then_drop ws_unit xml_attribute_codec


(** [xml_attributes_codec] — zero or more attributes, each preceded by
    one-or-more whitespace, terminated when the next byte is not whitespace
    (the [/] or [>] of the start-tag close).  Uses the bounded greedy-list
    combinator ([greedy]); the element is the whitespace+attribute pair. *)
let xml_attributes_codec : codec (list xml_attribute) =
  greedy ws_attr xml_max_depth


(* ========================================================================
   Node codec — text | element | comment | CDATA | PI, dispatched on the
   first byte.
   ======================================================================== *)


(** [xml_node_body] — the node codec builder, parameterized by the element
    TAIL codec [elem_tail] (an element body starting at the NAME — the
    leading `<` is consumed by the caller, mirroring the list-level
    [element_dec_body] split, fstar-proofs §47 Option 2).

    Dispatch: [alt] on the first byte — not-`<` → text, `<` → (factor `<`,
    then `!` → comment | CDATA, `?` → PI, name-start → element).  Each shared
    prefix is factored with [then_drop]/[between] so the discriminating byte is
    the first byte of the inner codec (the [char_ref]/[text_char] technique,
    fstar-proofs §52/§53).  No node kind is dropped.

    @param elem_tail The element body codec (from the name), for nested
                     elements. *)
let xml_node_body (elem_tail: codec xml_element) : codec xml_node =
  (* The element node (element body from the name). *)
  let elem_node : codec xml_node =
    map_ (fun e -> Some (XmlElement e))
         (fun n -> match n with XmlElement e -> Some e | _ -> None)
         elem_tail in

  (* Comment node body (after `<!`): `--` content `-->`.
     The content is a delimiter-aware [comment_content_codec] (value = content
     string, wire = [content -->]) — accepting a single interior dash, per
     RFC [15]. *)
  let comment_body : codec xml_node =
    map_ (fun s -> Some (XmlComment s))
         (fun n -> match n with XmlComment s -> Some s | _ -> None)
         (then_drop (text "--") comment_content_codec) in

  (* CDATA node body (after `<!`): `[CDATA[` content `]]>`.
     The content is [cdata_content_codec] (value = content string, wire =
     [content ]]]>]) — accepting a lone []] / []]], per RFC [18]/[20]. *)
  let cdata_body : codec xml_node =
    map_ (fun s -> Some (XmlCDATA s))
         (fun n -> match n with XmlCDATA s -> Some s | _ -> None)
         (then_drop (text "[CDATA[") cdata_content_codec) in

  (* PI node body (after `<?`): target ` ` data `?>`.
     The PI target is [pi_target_codec] — a Name minus the reserved [xml]
     target (REC [17], case-insensitive) — so an [<?xml …?>] PI in ELEMENT
     content is REJECTED, not just in the prolog.  This is the SAME
     [pi_target_codec] gate as the prolog [pi_body] (Codec.Prolog), whose
     gate-level rejection is proven by the 8 [lemma_pi_target_reject_*]
     lemmas in Data.XML.Token (bound in Integration) — they cover this site
     too.  The data is [pi_content_codec] (value = data string, wire =
     [data ?>]) — accepting a lone [?], per RFC [16]. *)
  let pi_body : codec xml_node =
    map_ (fun (t: string & string) -> Some (XmlPI (fst t) (snd t)))
         (fun n -> match n with XmlPI t d -> Some (t, d) | _ -> None)
         (product
            pi_target_codec
            (then_drop (byte_val 0x20uy) pi_content_codec)) in

  (* The text node — RESOLVED character data. *)
  let text_node : codec xml_node =
    map_ (fun s -> Some (XmlText s))
         (fun n -> match n with XmlText s -> Some s | _ -> None)
         xml_text_value_codec in

  (* After `<!`: `-` → comment, `[` → CDATA. *)
  let comment_or_cdata : codec (either xml_node xml_node) =
    alt comment_body cdata_body (fun b -> U8.v b = 0x2D) in
  (* After `<`: `?` → PI (then target), name-start → element. *)
  let pi_or_element : codec (either xml_node xml_node) =
    alt (then_drop (byte_val 0x3Fuy) pi_body) elem_node (fun b -> U8.v b = 0x3F) in
  (* After `<`: `!` → comment | CDATA, else `?` | name. *)
  let after_lt : codec (either (either xml_node xml_node) (either xml_node xml_node)) =
    alt (then_drop (byte_val 0x21uy) comment_or_cdata) pi_or_element
        (fun b -> U8.v b = 0x21) in

  (* The tagged (non-text) node: `<` then the after-`<` dispatch. *)
  let tagged : codec xml_node =
    map_
      (fun (e: either (either xml_node xml_node) (either xml_node xml_node)) ->
        match e with
        | Inl (Inl c) -> Some c    (* comment *)
        | Inl (Inr c) -> Some c    (* CDATA *)
        | Inr (Inl p) -> Some p    (* PI *)
        | Inr (Inr el) -> Some el) (* element *)
      (fun (n: xml_node) ->
        match n with
        | XmlComment _ -> Some (Inl (Inl n))
        | XmlCDATA _   -> Some (Inl (Inr n))
        | XmlPI _ _    -> Some (Inr (Inl n))
        | XmlElement _ -> Some (Inr (Inr n))
        | XmlText _    -> None)
      (then_drop (byte_val 0x3Cuy) after_lt) in

  (* Final: text (not `<`) vs tagged (`<`). *)
  map_
    (fun (e: either xml_node xml_node) -> match e with Inl t -> Some t | Inr g -> Some g)
    (fun (n: xml_node) -> match n with XmlText _ -> Some (Inl n) | _ -> Some (Inr n))
    (alt text_node tagged (fun b -> U8.v b <> 0x3C))


(* ========================================================================
   Element codec — the recursive core (fuel-indexed).
   ======================================================================== *)


(** [element_tail_map] — the element TAIL forward map: reconstruct an
    [xml_element] from the parsed [open name] + [attrs] + [tail].  The
    [Inl ()] tail is the empty element ([name attrs/>]); the [Inr] tail is
    the paired element, REQUIRING the close name to equal the open name
    (production [42] — mismatched end tags are rejected, so a [<a></b>] parse
    returns [None]). *)
let element_tail_map
  (n: xml_name & (list xml_attribute & either unit (xml_name & list xml_node)))
  : option xml_element =
  let (open_n, rest) = n in
  let (attrs, tail) = rest in
  match tail with
  | Inl () -> Some { elt_name = open_n; elt_attributes = attrs; elt_children = [] }
  | Inr (close_n, kids) ->
    if open_n = close_n then Some { elt_name = open_n; elt_attributes = attrs; elt_children = kids }
    else None


(** [xml_element_tail] — the element codec body, parameterized by the element
    TAIL codec [self] for nested children.  Parses/encodes an element STARTING
    AT THE NAME (the leading `<` is consumed by the caller), so the node
    dispatch factors the shared `<` once (fstar-proofs §47 Option 2 — no
    double `<`-match).

    An element is [name attrs/>] (empty) or [name attrs> children </name>]
    (paired).  Attributes are [S]-separated [Name=value] pairs
    ([xml_attributes_codec]).  Children are a bounded greedy list of nodes
    ([greedy] over [xml_node_body]).

    @param self The element TAIL codec for nested elements. *)
let xml_element_tail (self: codec xml_element) : codec xml_element =
  let rbracket = byte_val 0x3Euy in  (* > *)
  let slash    = byte_val 0x2Fuy in  (* / *)

  let children_c : codec (list xml_node) =
    greedy (xml_node_body self) xml_max_depth in

  (* The open name — the caller has consumed the leading `<`. *)
  let open_name : codec xml_name = xml_name_codec in

  (* Attributes after the name: zero or more [S Attribute] runs. *)
  let attrs_c : codec (list xml_attribute) = xml_attributes_codec in

  (* "/>" (empty) vs "> children </name>" (paired) — dispatch on "/" vs ">". *)
  let empty_tail : codec unit = then_drop slash rbracket in
  let paired_tail : codec (xml_name & list xml_node) =
    map_
      (fun (kids_close: list xml_node & xml_name) -> Some (snd kids_close, fst kids_close))
      (fun (p: xml_name & list xml_node) -> Some (snd p, fst p))
      (product
        (then_drop rbracket children_c)                     (* "> children" -> children *)
        (between (then_drop (byte_val 0x3Cuy) slash) rbracket (* "</name>" -> close name *)
          xml_name_codec)) in

  map_
    element_tail_map
    (fun (elt: xml_element) ->
      if elt.elt_children = [] then
        Some (elt.elt_name, (elt.elt_attributes, Inl ()))
      else
        Some (elt.elt_name, (elt.elt_attributes, Inr (elt.elt_name, elt.elt_children))))
    (product
      open_name
      (product attrs_c
        (alt empty_tail paired_tail (fun b -> U8.v b = 0x2F))))


(** [element_tail_map] rejects a MISMATCHED end tag (finding m2 / task 3.2):
    a paired element whose close name differs from its open name
    ([<a></b>]) returns [None] from the forward map, which [map_.dec]
    converts to [Inl].  Stated at the transparent forward-map gate because
    the full [xml_element_codec.dec] does not reduce cross-module (the
    recursive [custom]/[greedy] composition is §58-opaque). *)
#push-options "--z3rlimit 400"
let lemma_element_reject_mismatched_tag () : Lemma
  (ensures element_tail_map
            (mk_name "a", ([], Inr (mk_name "b", []))) == None)
  = assert_norm (element_tail_map (mk_name "a", ([], Inr (mk_name "b", []))) == None)
#pop-options


(** A matched end tag ([<a></a>]) is ACCEPTED by the forward map (the close
    name equals the open name). *)
#push-options "--z3rlimit 400"
let lemma_element_accept_matched_tag () : Lemma
  (ensures Some? (element_tail_map (mk_name "a", ([], Inr (mk_name "a", [])))))
  = assert_norm (element_tail_map (mk_name "a", ([], Inr (mk_name "a", [])))
                 == Some { elt_name = mk_name "a"; elt_attributes = []; elt_children = [] })
#pop-options


(* The missing-[S]-before-an-attribute rejection ([<a k="v">]) is enforced
   COMPOSITIONALLY: [xml_attributes_codec] is [greedy ws_attr], and
   [ws_attr = then_drop ws_unit …] requires one-or-more whitespace before
   each attribute; [<a k="v">] has [k] immediately after the name (no [S]),
   so the attribute list is EMPTY and the element tail's [alt empty_tail
   paired_tail] dispatch on the next byte [k] (neither [/] nor [>]) fails —
   the [alt_dec] returns [Inl].  This is a [map_]/[then_drop]/[alt]/[greedy]
   composition (0-admit by construction), not a hand-written guard; per
   fstar-proofs §58 it is enforced by the combinator [.roundtrip]/
   [.dec] generically and needs no per-vector [dec] lemma. *)


(** [xml_element_tail_codec] — fuel-indexed element BODY codec (from the name,
    no leading `<`).  Nested children use the tail at [fuel - 1]. *)
let rec xml_element_tail_codec (fuel: nat) : Tot (codec xml_element) (decreases fuel) =
  if fuel = 0 then reject
  else xml_element_tail (xml_element_tail_codec (fuel - 1))


(** [xml_element_codec] — fuel-indexed recursive element codec (from `<`).

    Base case fuel 0 is [reject] (fstar-proofs §23); otherwise the leading `<`
    plus the element TAIL at this depth.  Fuel = the maximum element depth. *)
let xml_element_codec (fuel: nat) : Tot (codec xml_element) =
  if fuel = 0 then reject
  else then_drop (byte_val 0x3Cuy) (xml_element_tail_codec fuel)


(* ========================================================================
   Document codec.
   ======================================================================== *)


(** [collect_some os] — the [Some] occupants of an [option] list, in order,
    with the [None] entries (whitespace) dropped. *)
let rec collect_some (#a: Type) (os: list (option a)) : Tot (list a) (decreases os) =
  match os with
  | [] -> []
  | o :: tl -> match o with Some x -> x :: collect_some tl | None -> collect_some tl


(** [prolog_misc] — zero or more [Misc] productions ([27]) as a
    [list xml_node], whitespace dropped.  Built as the bounded [greedy] over
    [misc_opt] (which yields [Some node] for comment/PI and [None] for
    whitespace), mapped to keep only the [Some] nodes. *)
let prolog_misc : codec (list xml_node) =
  map_
    (fun (os: list (option xml_node)) -> Some (collect_some os))
    (fun (ns: list xml_node) ->
      Some (List.Tot.map Some ns))
    (greedy misc_opt xml_max_depth)


(** [xml_prolog_codec] — the document prolog ([22]): optional declaration,
    then [Misc star], then optional doctype, then [Misc star].

    The fixed XML 1.0 ordering is [XMLDecl? Misc star (doctypedecl Misc
    star)?]; the two [Misc star] runs are each [greedy] over [misc_opt]
    (which stops at the next non-misc byte — the doctype keyword, the root
    [<], or EOF). *)
let xml_prolog_codec : codec xml_prolog =
  map_
    (fun (((d: option string), (m1: list xml_node)), ((dt: option string), (m2: list xml_node))) ->
      Some { prolog_decl = d; prolog_doctype = dt; prolog_misc = m1 @ m2 })
    (fun (p: xml_prolog) ->
      (* canonicalize: decl, then all misc before doctype, doctype, then [] *)
      Some ((p.prolog_decl, p.prolog_misc), (p.prolog_doctype, [])))
    (product
      (product optional_decl prolog_misc)
      (product optional_doctype prolog_misc))


(** [xml_document_codec] — a document: an optional prolog (XML declaration,
    doctype, and misc) followed by a single root element (XML 1.0 [1]).

    The prolog is [xml_prolog_codec]; the root is the fuel-indexed
    [xml_element_codec]; the composition is a [product] whose [.roundtrip]
    field is generic by construction (fstar-proofs §58 — [map_]/[product]
    compose sub-roundtrips). *)
let xml_document_codec : codec xml_document =
  let root_c : codec xml_element = xml_element_codec xml_max_depth in
  map_
    (fun (prolog: xml_prolog & xml_element) ->
      Some { doc_prolog = fst prolog; doc_root = snd prolog })
    (fun (doc: xml_document) -> Some (doc.doc_prolog, doc.doc_root))
    (product xml_prolog_codec root_c)


(* ========================================================================
   Top-level encode/decode.
   ======================================================================== *)


(** Encode a document with the document codec's [.enc]. *)
let encode_xml (d: xml_document) : byte_seq = xml_document_codec.enc d


(** Decode a document with the document codec's [.dec]. *)
let decode_xml (input: byte_seq) : decode_result xml_document = xml_document_codec.dec input


(* ========================================================================
   Concrete example documents (XML 1.0 well-formedness vectors).

   The recursive element/document roundtrip is proven GENERICALLY by the
   codec's own [.roundtrip] field (0-admit by construction, induction through
   the [greedy]/[map_]/[product]/[alt] combinator structure).  These concrete
   example values are the regression anchors re-stated in
   [Data.XML.Test.Element] so the Integration module enforces their presence
   mechanically (CODE_GUIDELINES §Integration test pattern).  They are NOT
   re-proven here: the general roundtrip lemma already covers them.
   ======================================================================== *)


(** An empty document whose root is the empty element [<a/>]. *)
let example_empty_doc : xml_document =
  { doc_prolog = { prolog_decl = None; prolog_doctype = None; prolog_misc = [] };
    doc_root = { elt_name = mk_name "a"; elt_attributes = []; elt_children = [] } }


(** A document whose root is the paired text element [<a>hi</a>]. *)
let example_text_doc : xml_document =
  { doc_prolog = { prolog_decl = None; prolog_doctype = None; prolog_misc = [] };
    doc_root = { elt_name = mk_name "a"; elt_attributes = [];
                 elt_children = [XmlText "hi"] } }


(** A document whose root is the nested element [<div><p>hi</p></div>]. *)
let example_nested_doc : xml_document =
  { doc_prolog = { prolog_decl = None; prolog_doctype = None; prolog_misc = [] };
    doc_root = { elt_name = mk_name "div"; elt_attributes = [];
                 elt_children = [XmlElement
                   { elt_name = mk_name "p"; elt_attributes = [];
                     elt_children = [XmlText "hi"] }] } }


(** A document whose root carries a single attribute ([<a k="v"/>]). *)
let example_attr_doc : xml_document =
  { doc_prolog = { prolog_decl = None; prolog_doctype = None; prolog_misc = [] };
    doc_root = { elt_name = mk_name "a";
                 elt_attributes = [{ attr_name = mk_name "k"; attr_value = "v" }];
                 elt_children = [] } }


(** A document whose root carries two attributes and text
    ([<a k1="v1" k2="v2">x</a>]). *)
let example_multi_attr_doc : xml_document =
  { doc_prolog = { prolog_decl = None; prolog_doctype = None; prolog_misc = [] };
    doc_root = { elt_name = mk_name "a";
                 elt_attributes = [{ attr_name = mk_name "k1"; attr_value = "v1" };
                                    { attr_name = mk_name "k2"; attr_value = "v2" }];
                 elt_children = [XmlText "x"] } }


(** A document whose root carries a comment child ([<a><!--c--></a>]). *)
let example_comment_doc : xml_document =
  { doc_prolog = { prolog_decl = None; prolog_doctype = None; prolog_misc = [] };
    doc_root = { elt_name = mk_name "a"; elt_attributes = [];
                 elt_children = [XmlComment "c"] } }


(** A document whose root carries a CDATA child ([<a><![CDATA[cd]]></a>]). *)
let example_cdata_doc : xml_document =
  { doc_prolog = { prolog_decl = None; prolog_doctype = None; prolog_misc = [] };
    doc_root = { elt_name = mk_name "a"; elt_attributes = [];
                 elt_children = [XmlCDATA "cd"] } }


(** A document whose root carries a PI child ([<a><?t d?></a>]). *)
let example_pi_doc : xml_document =
  { doc_prolog = { prolog_decl = None; prolog_doctype = None; prolog_misc = [] };
    doc_root = { elt_name = mk_name "a"; elt_attributes = [];
                 elt_children = [XmlPI "t" "d"] } }


(** A document with an XML declaration ([<?xml version="1.0"?><a/>]).  The
    declaration is the OPAQUE canonical text (the [list char] structural view
    is recovered by [xml_decl_scan]). *)
let example_decl_doc : xml_document =
  { doc_prolog = { prolog_decl = Some "<?xml version=\"1.0\"?>";
                   prolog_doctype = None; prolog_misc = [] };
    doc_root = { elt_name = mk_name "a"; elt_attributes = []; elt_children = [] } }


(** A document with an XML declaration and a doctype
    ([<?xml version="1.0"?><!DOCTYPE a><a/>]).  Both are carried OPAQUELY. *)
let example_decl_doctype_doc : xml_document =
  { doc_prolog = { prolog_decl = Some "<?xml version=\"1.0\"?>";
                   prolog_doctype = Some "<!DOCTYPE a>"; prolog_misc = [] };
    doc_root = { elt_name = mk_name "a"; elt_attributes = []; elt_children = [] } }


(** A document with a doctype carrying an ExternalID
    ([<!DOCTYPE a SYSTEM "x.dtd"><a/>]); the doctype text is opaque. *)
let example_doctype_extid_doc : xml_document =
  { doc_prolog = { prolog_decl = None;
                   prolog_doctype = Some "<!DOCTYPE a SYSTEM \"x.dtd\">";
                   prolog_misc = [] };
    doc_root = { elt_name = mk_name "a"; elt_attributes = []; elt_children = [] } }


(** A document containing an entity reference ([&amp;] → [&]) and a character
    reference ([&#65;] → [A]) in RESOLVED text, nested two levels deep
    ([<root><a><b>X&amp;Y&#65;Z</b></a></root>] resolves to text [X&YAZ]).

    The text node [XmlText "X&YAZ"] is the RESOLVED form; the ENCODER re-emits
    the reserved [&] as [&amp;] and the [A] (from [&#65;]) as a literal.  This
    is the finding m1 vector (entity ref + char ref + >1 nesting), covered by
    the generic [xml_document_codec.roundtrip] (0-admit, §58). *)
let example_refs_nested_doc : xml_document =
  { doc_prolog = { prolog_decl = None; prolog_doctype = None; prolog_misc = [] };
    doc_root = { elt_name = mk_name "root"; elt_attributes = [];
                 elt_children = [XmlElement
                   { elt_name = mk_name "a"; elt_attributes = [];
                     elt_children = [XmlElement
                       { elt_name = mk_name "b"; elt_attributes = [];
                         elt_children = [XmlText "X&YAZ"] }] }] } }

