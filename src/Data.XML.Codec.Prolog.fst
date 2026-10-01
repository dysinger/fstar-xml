(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)

(**
Data.XML.Codec.Prolog — XML 1.0 document prolog leaf codecs (doctype and misc).

This child module (fstar-proofs §44/§45 isolation) holds the document-prolog
leaf codecs that require a [custom] list-level scan — the doctype declaration
([28] Option B) — plus the [misc] production ([27]) leaves (comment/PI nodes),
reusing the proven comment/PI content codecs from [Data.XML.Codec.Wrapped].

The doctypedecl is carried STRUCTURALLY — the Name and the bracket-nested
[intSubset] interior are validated, with the interior ([28b] markupdecl |
DeclSep) carried as an OPAQUE string (the full DTD grammar is a separate lift).
The stored value [prolog_doctype : option string] is the WHOLE canonical
doctype text.  The doctype is a [custom] codec (fstar-proofs §58 legitimate use
#1): its decoder is a LIST-level bracket-tracking scan, the only 0-admit form
for the multi-byte top-level-[>] delimiter with an interior [..] bracket run
(fstar-proofs §50/§60 — [Seq.seq_to_list]-at-the-boundary plus the bridge
[lemma_seq_to_list_of_list_append]).

Isolated from [Data.XML.Codec]'s combinator chains so the [custom] doctype
roundtrip stays 0-admit.

@header Data.XML.Codec.Prolog
*)
module Data.XML.Codec.Prolog

open Data.Codec
open Data.Text.Codec
open Data.Text.Codec.Chars
open Data.Text.Codec.UTF8
open Data.XML.Token
open Data.XML.Codec.Wrapped
open Data.XML.Types
open FStar.Seq
open FStar.Char
open FStar.UInt8
open FStar.List.Tot

module U8 = FStar.UInt8
module Seq = FStar.Seq

(** One-or-more whitespace ([S]) as a [codec unit] — [ws] (the [codec
    string]) mapped to [unit], the canonical encoder emitting a single space.

    Named [prolog_ws_unit] to avoid colliding with the [Data.XML.Codec]
    [ws_unit] (both map the shared [ws] codec to [unit]) when the prolog
    module is opened for document composition (fstar-proofs §19 open-order). *)
let prolog_ws_unit : codec unit =
  map_ (fun (_: string) -> Some ())
       (fun (_: unit) -> Some " ")
       ws

(* ========================================================================
   doctypedecl ([28]): '<!DOCTYPE' S Name (S ExternalID)? S?
   ('[' intSubset ']' S?)? '>'.

   Option B: the doctype is carried STRUCTURALLY — the Name and the
   bracket-nested [intSubset] interior are validated, with the interior
   ([28b] markupdecl | DeclSep) carried as an OPAQUE string.  The stored
   value [prolog_doctype : option string] is the WHOLE canonical doctype.

   The doctype is a [custom] codec (§58 legitimate use #1): its decoder is a
   LIST-level bracket-tracking scan ([scan_doctype]), the only 0-admit form
   for the multi-byte top-level-[>] delimiter with an interior [..] bracket
   run (§50/§60 — [Seq.seq_to_list]-at-the-boundary + the bridge
   [lemma_seq_to_list_of_list_append]).
   ======================================================================== *)

(** The [<!DOCTYPE] prefix bytes (9 bytes). *)
let doctype_open_bytes : list byte =
  [0x3Cuy; 0x21uy; 0x44uy; 0x4Fuy; 0x43uy; 0x54uy; 0x59uy; 0x50uy; 0x45uy]

(** [starts_with p bs] — is [p] a list-cons prefix of [bs]?  A LOCAL
    recursive scan (unlike [Data.Codec.Types.is_prefix_of], whose CROSS-MODULE
    [let rec] body is opaque to SMT, §18): its [match] is unfolded by the
    recursive [lemma_starts_with_append] induction in THIS module, so
    [starts_with p content ==> starts_with p (content @ rest)] is provable. *)
let rec starts_with (p bs: list byte) : Tot bool (decreases p) =
  match p, bs with
  | [], _ -> true
  | _, [] -> false
  | ph :: pt, bh :: bt -> ph = bh && starts_with pt bt

(** [starts_with p content] is preserved by appending to [content]. *)
let rec lemma_starts_with_append (p content rest: list byte) : Lemma
  (ensures starts_with p content ==> starts_with p (content @ rest))
  (decreases p)
  = match p, content with
    | [], _ -> ()
    | _, [] -> ()
    | ph :: pt, ch :: ct ->
      if ph = ch then lemma_starts_with_append pt ct rest
      else ()

(** Is [b] a single-quote (0x27) or double-quote (0x22)?  A LOCAL copy of
    [is_decl_quote] (definition-before-use: [scan_doctype_go] needs it). *)
let is_doctype_quote (b: byte) : bool = U8.v b = 0x22 || U8.v b = 0x27

(** Scan one full doctype token, tracking the [intSubset] bracket depth and
    the quote state (a [SystemLiteral]/[PubidLiteral] span), stopping at (and
    including) the first top-level [>].  A [>]/['[']/[']'] INSIDE a quoted
    literal is inert — it is part of the literal, not bracket structure
    (finding P2: [<!DOCTYPE a SYSTEM "]">] is a valid doctype and its quoted
    []] must not be treated as an [intSubset] close).
    [0x5B] = '[', [0x5D] = ']', [0x3E] = '>', [0x22] = '"', [0x27] = '\''. *)
let rec scan_doctype_go (bs: list byte) (depth: nat) (q: option byte)
  : Tot (list byte & list byte) (decreases bs)
  = match bs with
    | [] -> ([], [])
    | b :: tl ->
      match q with
      | Some qc ->
        (* Inside a quoted literal: only [qc] is special (closes the quote);
           every other byte (including ['['], [']'], ['>']) is inert. *)
        if b = qc then let (c, r) = scan_doctype_go tl depth None in (b :: c, r)
        else let (c, r) = scan_doctype_go tl depth q in (b :: c, r)
      | None ->
        if is_doctype_quote b then
          let (c, r) = scan_doctype_go tl depth (Some b) in (b :: c, r)
        else if b = 0x3Euy then
          if depth = 0 then ([0x3Euy], tl)
          else let (c, r) = scan_doctype_go tl depth None in (0x3Euy :: c, r)
        else if b = 0x5Buy then
          let (c, r) = scan_doctype_go tl (depth + 1) None in (0x5Buy :: c, r)
        else if b = 0x5Duy then
          if depth = 0 then let (c, r) = scan_doctype_go tl 0 None in (0x5Duy :: c, r)
          else let (c, r) = scan_doctype_go tl (depth - 1) None in (0x5Duy :: c, r)
        else let (c, r) = scan_doctype_go tl depth None in (b :: c, r)

(** Scan a doctype declaration starting at bracket depth 0 and quote state
    [None] (the public entry point for the quote-aware bracket-tracking
    scan).  Returns the consumed prefix (through the first top-level [>])
    and the remaining bytes. *)
let scan_doctype (bs: list byte) : Tot (list byte & list byte) = scan_doctype_go bs 0 None

(** [doctype_balanced bs d q] — [bs], read from bracket depth [d] and quote
    state [q], is balanced: every [>] outside a literal is terminal-at-depth-0
    (and last), every []] outside a literal closes a bracket.  Bytes inside a
    quoted literal do not affect depth (finding P2).  The [] case is [false]:
    a complete doctype is never balanced-empty. *)
let rec doctype_balanced (bs: list byte) (d: nat) (q: option byte)
  : Tot bool (decreases bs) =
  match bs with
  | [] -> false
  | b :: tl ->
    match q with
    | Some qc ->
      if b = qc then doctype_balanced tl d None
      else doctype_balanced tl d q
    | None ->
      if is_doctype_quote b then doctype_balanced tl d (Some b)
      else if b = 0x5Buy then doctype_balanced tl (d + 1) None
      else if b = 0x5Duy then d > 0 && doctype_balanced tl (d - 1) None
      else if b = 0x3Euy then if d = 0 then tl = [] else doctype_balanced tl d None
      else doctype_balanced tl d None

(** Is [b] an XML [S] whitespace byte (space/tab/CR/LF)?  A LOCAL copy of
    [is_decl_ws_byte] (that helper is defined below in the declaration
    section, after [doctype_ok] needs it — F* requires definition-before-use). *)
let is_doctype_ws_byte (b: byte) : bool =
  let v = U8.v b in v = 0x20 || v = 0x09 || v = 0x0D || v = 0x0A

(** Skip ZERO-or-more [S] whitespace bytes (local, definition-before-use). *)
let rec doctype_skip_ws_opt (bs: list byte) : Tot (list byte) (decreases bs) =
  match bs with
  | b :: tl -> if is_doctype_ws_byte b then doctype_skip_ws_opt tl else bs
  | [] -> bs

(** Skip ONE-or-more [S] whitespace bytes: [Some rest] with the whitespace
    dropped, [None] if there is no leading whitespace. *)
let doctype_skip_ws (bs: list byte) : Tot (option (list byte)) =
  match bs with
  | b :: tl -> if is_doctype_ws_byte b then Some (doctype_skip_ws_opt tl) else None
  | [] -> None

(** Consume the fixed keyword [kw] (a prefix of [bs]): [Some rest] after
    dropping [kw], [None] otherwise.  Local copy of the declaration's
    [decl_expect_bytes] (definition-before-use). *)
let rec doctype_expect_bytes (kw: list byte) (bs: list byte)
  : Tot (option (list byte)) (decreases kw)
  = match kw with
    | [] -> Some bs
    | b :: tl ->
      (match bs with
       | b' :: rest -> if b = b' then doctype_expect_bytes tl rest else None
       | [] -> None)

(** Consume the [SYSTEM] keyword bytes. *)
let kw_system_bytes : list byte = [0x53uy; 0x59uy; 0x53uy; 0x54uy; 0x45uy; 0x4Duy]

(** Consume the [PUBLIC] keyword bytes. *)
let kw_public_bytes : list byte = [0x50uy; 0x55uy; 0x42uy; 0x4Cuy; 0x49uy; 0x43uy]

(** Consume zero-or-more XML [NameChar] characters (UTF-8 aware), returning
    the remaining byte list.  Total: stops at the first byte that does not
    begin a [NameChar] (or at end of input, or at the char-fuel bound).
    Uses [utf8_decode_one] (fstar-proofs §59) so the scan is prefix-determined
    (the head byte fixes the char width).  The fuel is a CHAR count — never a
    byte count — because [char_to_utf8] is 1-4 bytes and a byte-fuel recurrence
    misaligns with the char-cons induction (§59 Fact 1).  Bound by
    [xml_max_name_len] (the [name_codec] bound). *)
let rec doctype_scan_name_chars (fuel: nat) (bs: list byte)
  : Tot (list byte) (decreases fuel)
  = if fuel = 0 then bs
    else match utf8_decode_one bs with
    | None -> bs
    | Some (c, rest) ->
      if is_name_char_char c then doctype_scan_name_chars (fuel - 1) rest else bs

(** Consume a single XML [Name] ([NameStartChar] [NameChar] star, production
    [5]): [Some rest] past the name, [None] if the head byte does not begin a
    [NameStartChar]. *)
let doctype_scan_name (bs: list byte) : option (list byte) =
  match utf8_decode_one bs with
  | None -> None
  | Some (c, rest) ->
    if is_name_start_char c then Some (doctype_scan_name_chars xml_max_name_len rest) else None

(** Consume a quoted literal (['"'] [[^\"]] star ['"'] | ['\''] [[^\']] star
    ['\'']), production [9].  [Some rest] after the closing quote, [None] on
    unterminated or unquoted input. *)
let rec doctype_scan_quoted_go (q: byte) (bs: list byte)
  : Tot (option (list byte)) (decreases bs)
  = match bs with
    | [] -> None
    | b :: tl -> if b = q then Some tl else doctype_scan_quoted_go q tl

(** Consume a quoted literal (production [9]): [Some rest] after the closing
    quote, [None] on unterminated/unquoted input (the public entry point for
    the quote-skip helper [doctype_scan_quoted_go]). *)
let doctype_scan_quoted (bs: list byte) : option (list byte) =
  match bs with
  | b :: tl -> if is_doctype_quote b then doctype_scan_quoted_go b tl else None
  | [] -> None

(** Consume the [SYSTEM] system literal branch of [ExternalID] ([75]):
    [SYSTEM S SystemLiteral]. *)
let doctype_scan_system_id (bs: list byte) : option (list byte) =
  match doctype_expect_bytes kw_system_bytes bs with
  | None -> None
  | Some after_kw ->
    (match doctype_skip_ws after_kw with
     | None -> None
     | Some after_s -> doctype_scan_quoted after_s)

(** Consume the [PUBLIC] public literal branch of [ExternalID] ([75]):
    [PUBLIC S PubidLiteral S SystemLiteral]. *)
let doctype_scan_public_id (bs: list byte) : option (list byte) =
  match doctype_expect_bytes kw_public_bytes bs with
  | None -> None
  | Some after_kw ->
    (match doctype_skip_ws after_kw with
     | None -> None
     | Some after_pub ->
       (match doctype_scan_quoted after_pub with
        | None -> None
        | Some after_pubid ->
          (match doctype_skip_ws after_pubid with
           | None -> None
           | Some after_s2 -> doctype_scan_quoted after_s2)))

(** Consume an [ExternalID] ([75]) — [SYSTEM …] or [PUBLIC …]. *)
let doctype_scan_external_id (bs: list byte) : option (list byte) =
  match doctype_scan_system_id bs with
  | Some r -> Some r
  | None -> doctype_scan_public_id bs

(** Consume the doctype declaration ENVELOPE prefix
    [<!DOCTYPE S Name (S ExternalID)?], returning the rest (the
    [S? (['[' intSubset ']'] S?)? '>'] tail, which [doctype_balanced]
    validates), or [None] if the envelope is malformed.  This is the
    structural shell of production [28]; the [intSubset] interior remains
    opaque (bracket-balanced only). *)
let doctype_scan_envelope (bs: list byte) : option (list byte) =
  match doctype_expect_bytes doctype_open_bytes bs with
  | None -> None
  | Some after_open ->
    (match doctype_skip_ws after_open with
     | None -> None
     | Some after_s ->
       (match doctype_scan_name after_s with
        | None -> None
        | Some after_name ->
          (match doctype_skip_ws after_name with
           | None -> Some after_name          (* no trailing [S] — the tail is [S? … '>'] *)
           | Some after_ws ->
             if starts_with kw_system_bytes after_ws || starts_with kw_public_bytes after_ws then
               doctype_scan_external_id after_ws
             else Some after_name)))          (* [S] before ['['] or ['>'] — leave for [doctype_balanced] *)

(** [doctype_ok bs] — [bs] is a well-formed doctype declaration ([28]): it
    starts with the [<!DOCTYPE] keyword, its envelope ([S Name (S
    ExternalID)?]) is structurally valid, and its remaining interior is
    bracket-balanced (the opaque [intSubset] tail).  This is the STRENGTHENED
    predicate fixing C1: the envelope is no longer merely bracket-balanced. *)
let doctype_ok (bs: list byte) : bool =
  starts_with doctype_open_bytes bs &&
  (match doctype_scan_envelope bs with Some _ -> true | None -> false) &&
  doctype_balanced bs 0 None

(** The doctype DECODER: scan the bracket-tracked token and validate it with
    [doctype_ok], returning the opaque text plus its length (or an
    [ExpectedPredicate] error). *)
unfold
let doctype_dec (s: byte_seq) : decode_result string =
  let bs = Seq.seq_to_list s in
  let (content, rest) = scan_doctype bs in
  if doctype_ok content then Inr (text_bytes_to_string content, List.Tot.length content)
  else Inl (mk_decode_error ExpectedPredicate (List.Tot.length content))

(** The doctype ENCODER: the opaque text rendered verbatim as bytes. *)
unfold
let doctype_enc (s: string) : byte_seq = seq_of_list (text_string_to_bytes s)

(** [doctype_is_ascii s] — [s] is all-ASCII (the doctype text is byte-carry). *)
let doctype_is_ascii (s: string) : bool =
  FStar.List.Tot.for_all (ascii_ok (fun _ -> true)) (FStar.String.list_of_string s)

(** [doctype_wfcv s] — [s] is a well-formed doctype: all-ASCII AND a valid
    [doctype_ok] bracket-balanced envelope. *)
let doctype_wfcv (s: string) : bool = doctype_is_ascii s && doctype_ok (text_string_to_bytes s)

(** Well-formed proposition (the real gate is [doctype_wfcv]; the non-vacuous
    [lemma_doctype_roundtrip] requires it). *)
let doctype_wfcv_prop (s: string) : prop = True

(** Suffix condition — [True] (the [>] close is a fixed terminal; any suffix
    is fine as the roundtrip consumes exactly the token). *)
let doctype_rest_cond (s: string) (r: byte_seq) : prop = True

(** Exactness of the quote-aware scan: when [doctype_balanced l d q] holds, the
    scan over [l @ rest] consumes exactly [l] and leaves [rest].  Proved
    by structural induction on [l] mirroring [scan_doctype_go]'s branch shape. *)
#push-options "--z3rlimit 2000"
let rec lemma_scan_doctype_go_exact (l rest: list byte) (d: nat) (q: option byte) : Lemma
  (requires doctype_balanced l d q)
  (ensures scan_doctype_go (l @ rest) d q == (l, rest))
  (decreases l)
  = match l with
    | [] -> ()
    | b :: tl ->
      match q with
      | Some qc ->
        if b = qc then begin assert (doctype_balanced tl d None);
          lemma_scan_doctype_go_exact tl rest d None; () end
        else begin assert (doctype_balanced tl d q);
          lemma_scan_doctype_go_exact tl rest d q; () end
      | None ->
        if is_doctype_quote b then begin assert (doctype_balanced tl d (Some b));
          lemma_scan_doctype_go_exact tl rest d (Some b); () end
        else if b = 0x5Buy then begin assert (doctype_balanced tl (d + 1) None);
          lemma_scan_doctype_go_exact tl rest (d + 1) None; () end
        else if b = 0x5Duy then begin assert (d > 0); assert (doctype_balanced tl (d - 1) None);
          lemma_scan_doctype_go_exact tl rest (d - 1) None; () end
        else if b = 0x3Euy then
          if d = 0 then begin assert (tl == []); () end
          else begin assert (doctype_balanced tl d None); lemma_scan_doctype_go_exact tl rest d None; () end
        else begin assert (doctype_balanced tl d None); lemma_scan_doctype_go_exact tl rest d None; () end
#pop-options

(** [scan_doctype] is exact for a valid [doctype_ok] token: it consumes the
    whole token and leaves the suffix. *)
#push-options "--z3rlimit 800"
let lemma_scan_doctype_exact (content rest: list byte) : Lemma
  (requires doctype_ok content)
  (ensures scan_doctype (content @ rest) == (content, rest))
  = lemma_scan_doctype_go_exact content rest 0 None
#pop-options

(** The scan's consumed prefix never exceeds the input length.  Proved by
    structural induction mirroring [scan_doctype_go]. *)
let rec lemma_scan_doctype_go_content_le_len (bs: list byte) (d: nat) (q: option byte) : Lemma
  (ensures List.Tot.length (fst (scan_doctype_go bs d q)) <= List.Tot.length bs)
  (decreases bs)
  = match bs with
    | [] -> ()
    | b :: tl ->
      match q with
      | Some qc -> if b = qc then lemma_scan_doctype_go_content_le_len tl d None
                   else lemma_scan_doctype_go_content_le_len tl d q
      | None ->
        if is_doctype_quote b then lemma_scan_doctype_go_content_le_len tl d (Some b)
        else if b = 0x3Euy then if d = 0 then () else lemma_scan_doctype_go_content_le_len tl d None
        else if b = 0x5Buy then lemma_scan_doctype_go_content_le_len tl (d + 1) None
        else if b = 0x5Duy then lemma_scan_doctype_go_content_le_len tl (if d = 0 then 0 else d - 1) None
        else lemma_scan_doctype_go_content_le_len tl d None

(** The scan splits exactly: consumed prefix @ remaining suffix reconstructs
    the input.  Proved by structural induction mirroring [scan_doctype_go]. *)
let rec lemma_scan_doctype_go_split_exact (bs: list byte) (d: nat) (q: option byte) : Lemma
  (ensures fst (scan_doctype_go bs d q) @ snd (scan_doctype_go bs d q) == bs)
  (decreases bs)
  = match bs with
    | [] -> ()
    | b :: tl ->
      match q with
      | Some qc -> if b = qc then lemma_scan_doctype_go_split_exact tl d None
                   else lemma_scan_doctype_go_split_exact tl d q
      | None ->
        if is_doctype_quote b then lemma_scan_doctype_go_split_exact tl d (Some b)
        else if b = 0x3Euy then if d = 0 then () else lemma_scan_doctype_go_split_exact tl d None
        else if b = 0x5Buy then lemma_scan_doctype_go_split_exact tl (d + 1) None
        else if b = 0x5Duy then lemma_scan_doctype_go_split_exact tl (if d = 0 then 0 else d - 1) None
        else lemma_scan_doctype_go_split_exact tl d None

(** The doctype decoder's error position is bounded by the input length. *)
#push-options "--z3rlimit 400"
let lemma_doctype_dec_err_bound (s: byte_seq) : Lemma
  (ensures (match doctype_dec s with Inl err -> err.err_pos <= Seq.length s | _ -> True))
  = lemma_scan_doctype_go_content_le_len (Seq.seq_to_list s) 0 None
#pop-options

(** The doctype decoder's consumed count is bounded by the input length. *)
#push-options "--z3rlimit 400"
let lemma_doctype_dec_consumed_bound (s: byte_seq) : Lemma
  (ensures (match doctype_dec s with Inr (_, n) -> n <= Seq.length s | _ -> True))
  = lemma_scan_doctype_go_content_le_len (Seq.seq_to_list s) 0 None;
    lemma_scan_doctype_go_split_exact (Seq.seq_to_list s) 0 None
#pop-options

(** Roundtrip for the opaque doctype codec: encoding then decoding returns
    the original text, consuming exactly the encoded length. *)
#push-options "--z3rlimit 800"
let lemma_doctype_roundtrip (s: string) (r: byte_seq) : Lemma
  (requires doctype_wfcv s /\ doctype_wfcv_prop s /\ doctype_rest_cond s r)
  (ensures doctype_dec (doctype_enc s `Seq.append` r) == Inr (s, Seq.length (doctype_enc s)))
  = let content = text_string_to_bytes s in
    assert (doctype_ok content);
    lemma_text_string_to_bytes_roundtrip (fun _ -> true) s;
    assert (text_bytes_to_string content == s);
    lemma_seq_to_list_of_list_append content r;
    assert (Seq.seq_to_list (doctype_enc s `Seq.append` r) == content @ Seq.seq_to_list r);
    lemma_scan_doctype_exact content (Seq.seq_to_list r);
    assert (scan_doctype (content @ Seq.seq_to_list r) == (content, Seq.seq_to_list r));
    lemma_seq_of_list_length content;
    assert (Seq.length (doctype_enc s) == List.Tot.length content);
    assert (doctype_dec (doctype_enc s `Seq.append` r) == Inr (text_bytes_to_string content, List.Tot.length content));
    assert (doctype_dec (doctype_enc s `Seq.append` r) == Inr (s, Seq.length (doctype_enc s)));
    ()
#pop-options

(** [doctype_decl_codec] — the doctype declaration as an OPAQUE validated
    string ([<!DOCTYPE ...>], production [28]), carried as a single
    bracket-balanced/quote-aware text token. *)
let doctype_decl_codec : codec string =
  custom doctype_dec doctype_enc doctype_wfcv doctype_wfcv_prop doctype_rest_cond
    (fun s r -> lemma_doctype_roundtrip s r)
    lemma_doctype_dec_err_bound lemma_doctype_dec_consumed_bound

(* ========================================================================
   Doctype envelope rejection lemmas (C1 + task 1.3).

   The strengthened [doctype_ok] rejects a malformed envelope — with no
   [Name] ([<!DOCTYPE>]), or with garbage after the keyword
   ([<!DOCTYPE <<<<>>>>]) — via the [doctype_scan_envelope] predicate.  Each
   rejection lemma states the CODEC-level [doctype_dec … == Inl …], not merely
   [doctype_ok … == false] (fstar-proofs §51 Pitfall 2 / M4).
   ======================================================================== *)

(** The byte list of the malformed empty doctype [<!DOCTYPE>] (no Name, no
    required [S]).  A fully-literal list (no [@]) so [assert_norm] reduces it
    to a cons chain (fstar-proofs §14 — [@] is opaque to the normalizer). *)
let doctype_empty_bytes : list byte =
  [0x3Cuy; 0x21uy; 0x44uy; 0x4Fuy; 0x43uy; 0x54uy; 0x59uy; 0x50uy; 0x45uy; 0x3Euy]

(** The byte list of the malformed balanced-garbage doctype
    [<!DOCTYPE <<<<>>>>].  Fully literal as above. *)
let doctype_garbage_bytes : list byte =
  [0x3Cuy; 0x21uy; 0x44uy; 0x4Fuy; 0x43uy; 0x54uy; 0x59uy; 0x50uy; 0x45uy;
   0x20uy; 0x3Cuy; 0x3Cuy; 0x3Cuy; 0x3Cuy; 0x3Euy; 0x3Euy; 0x3Euy; 0x3Euy]

(** The byte list of a valid simple doctype [<!DOCTYPE a>]. *)
let doctype_simple_bytes : list byte =
  [0x3Cuy; 0x21uy; 0x44uy; 0x4Fuy; 0x43uy; 0x54uy; 0x59uy; 0x50uy; 0x45uy;
   0x20uy; 0x61uy; 0x3Euy]

(** The byte list of a valid doctype with an ExternalID
    ([<!DOCTYPE a SYSTEM "x.dtd">]).  Fully literal as above. *)
let doctype_extid_bytes : list byte =
  [0x3Cuy; 0x21uy; 0x44uy; 0x4Fuy; 0x43uy; 0x54uy; 0x59uy; 0x50uy; 0x45uy;
   0x20uy; 0x61uy; 0x20uy;
   0x53uy; 0x59uy; 0x53uy; 0x54uy; 0x45uy; 0x4Duy;
   0x20uy; 0x22uy; 0x78uy; 0x2Euy; 0x64uy; 0x74uy; 0x64uy; 0x22uy; 0x3Euy]

(** [<!DOCTYPE>] is rejected: the envelope predicate fails (no [S] and no
    [Name] after the keyword), so the decoder returns [Inl].  Stated at the
    [doctype_ok] gate — the decoder's soundness predicate — because
    [doctype_dec]'s [scan_doctype] (a [let rec]) is §2/§44-opaque to SMT and
    does not reduce to the token boundary (fstar-proofs §52 Pitfall 3: reject
    at the predicate gate). *)
#push-options "--z3rlimit 400"
let lemma_doctype_reject_empty () : Lemma
  (ensures doctype_ok doctype_empty_bytes == false)
  = assert_norm (doctype_ok doctype_empty_bytes == false)
#pop-options

(** The scanned content of [<!DOCTYPE <<<<>>>>]: the bracket scan stops at the
    first top-level [>], leaving the trailing [>>>] as the remainder. *)
let doctype_garbage_content : list byte =
  [0x3Cuy; 0x21uy; 0x44uy; 0x4Fuy; 0x43uy; 0x54uy; 0x59uy; 0x50uy; 0x45uy;
   0x20uy; 0x3Cuy; 0x3Cuy; 0x3Cuy; 0x3Cuy; 0x3Euy]

(** [<!DOCTYPE <<<<>>>>] is rejected: after the keyword and [S], the head
    byte [<] is not a [NameStartChar], so the envelope fails.  Stated at the
    [doctype_ok] gate (see [lemma_doctype_reject_empty]). *)
#push-options "--z3rlimit 400"
let lemma_doctype_reject_garbage () : Lemma
  (ensures doctype_ok doctype_garbage_content == false)
  = assert_norm (doctype_ok doctype_garbage_content == false)
#pop-options

(** [<!DOCTYPE a>] is ACCEPTED by the envelope scan (a valid [Name] follows
    the keyword; the bracket-balanced tail is the separate [doctype_balanced]
    invariant, already covered by [Data.XML.Test.Prolog]'s
    [test_doctype_balanced_*]).  The envelope scan is the NEW structural check
    fixing C1. *)
#push-options "--z3rlimit 400"
let lemma_doctype_accept_simple () : Lemma
  (ensures (match doctype_scan_envelope doctype_simple_bytes with
            | Some _ -> True | None -> False))
  = assert_norm ((match doctype_scan_envelope doctype_simple_bytes with
                  | Some _ -> true | None -> false) == true)
#pop-options

(** [<!DOCTYPE a SYSTEM "x.dtd">] is ACCEPTED (a valid [Name] + an
    [ExternalID] shell). *)
#push-options "--z3rlimit 400"
let lemma_doctype_accept_extid () : Lemma
  (ensures (match doctype_scan_envelope doctype_extid_bytes with
            | Some _ -> True | None -> False))
  = assert_norm ((match doctype_scan_envelope doctype_extid_bytes with
                  | Some _ -> true | None -> false) == true)
#pop-options

(** The byte list of a malformed ExternalID doctype
    ([<!DOCTYPE a SYSTEM>]) — a [SYSTEM] keyword with no literal, so the
    envelope's [doctype_scan_system_id] fails. *)
let doctype_malformed_extid_bytes : list byte =
  [0x3Cuy; 0x21uy; 0x44uy; 0x4Fuy; 0x43uy; 0x54uy; 0x59uy; 0x50uy; 0x45uy;
   0x20uy; 0x61uy; 0x20uy;
   0x53uy; 0x59uy; 0x53uy; 0x54uy; 0x45uy; 0x4Duy; 0x3Euy]

(** A doctype with a [SYSTEM] keyword but no literal is REJECTED (the
    [ExternalID] shell is incomplete — finding M2 / task 1.4).  Stated at the
    [doctype_ok] gate (see [lemma_doctype_reject_empty]). *)
#push-options "--z3rlimit 400"
let lemma_doctype_reject_malformed_extid () : Lemma
  (ensures doctype_ok doctype_malformed_extid_bytes == false)
  = assert_norm (doctype_ok doctype_malformed_extid_bytes == false)
#pop-options

(* ========================================================================
   Misc ([27]): Comment | PI | S.
   ======================================================================== *)

(** [comment_body] — a comment BODY (after the shared [<], the [!--] prefix
    + content + [-->]) as an [XmlComment] node. *)
let comment_body : codec xml_node =
  map_
    (fun (s: string) -> Some (XmlComment s))
    (fun (n: xml_node) -> match n with XmlComment s -> Some s | _ -> None)
    (then_drop (text "!--") comment_content_codec)

(** [pi_target_codec] — a PI target ([17]): a Name minus the reserved target
    [xml] (case-insensitive).  Built as a [map_] over [name_codec] whose
    forward map ([is_pi_target]) rejects [xml]/[XML]/[Xml]/… (finding P1). *)
let pi_target_codec : codec string =
  map_
    (fun (s: string) -> if is_pi_target s then Some s else None)
    (fun (s: string) -> Some s)
    name_codec

(** [pi_body] — a PI BODY (after the shared [<], the [?] + target + space +
    data + [?]>) as an [XmlPI] node.  The target is gated by
    [pi_target_codec], so a PI whose target is the reserved [xml] (in any
    case combination) is REJECTED (REC [17] / finding P1). *)
let pi_body : codec xml_node =
  map_
    (fun (t: string & string) -> Some (XmlPI (fst t) (snd t)))
    (fun (n: xml_node) -> match n with XmlPI t d -> Some (t, d) | _ -> None)
    (then_drop (byte_val 0x3Fuy)
      (product pi_target_codec (then_drop (byte_val 0x20uy) pi_content_codec)))

(** [comment_or_pi_body] — dispatch after the shared [<]: a [!--] prefix
    selects a comment, a [?] prefix selects a PI (first-byte-disjoint [alt]). *)
let comment_or_pi_body : codec xml_node =
  map_
    (fun (e: either xml_node xml_node) -> match e with Inl n -> Some n | Inr n -> Some n)
    (fun (n: xml_node) -> match n with XmlComment _ -> Some (Inl n) | XmlPI _ _ -> Some (Inr n) | _ -> None)
    (alt comment_body pi_body (fun b -> U8.v b = 0x21))

(** [comment_or_pi_node] — a full comment-or-PI node: the [<] prefix then
    the [comment_or_pi_body] dispatch. *)
let comment_or_pi_node : codec xml_node =
  then_drop (byte_val 0x3Cuy) comment_or_pi_body

(** [misc_opt] — a single [Misc] production as [option xml_node]: [Some] for
    a comment or PI, [None] for whitespace (dropped).  Dispatched on the
    first byte: [<] (0x3C) → comment/PI node, otherwise whitespace. *)
let misc_opt : codec (option xml_node) =
  map_
    (fun (e: either xml_node unit) -> match e with Inl n -> Some (Some n) | Inr _ -> Some None)
    (fun (o: option xml_node) -> match o with Some n -> Some (Inl n) | None -> Some (Inr ()))
    (alt comment_or_pi_node prolog_ws_unit (fun b -> U8.v b = 0x3C))

(* ========================================================================
   XML declaration ([23]) and the single-byte-quoted literals ([11]/[12]/[13])
   + [ExternalID] ([75]).

   The XML declaration is [<?xml S version Eq (quote) VersionNum (quote)
   (S encoding Eq (quote) EncName (quote))? (S standalone Eq (quote)
   (yes|no) (quote))? S? ?>] ([23]-[26]/[32]/[80]/[81]).  The optional
   [encoding]/[standalone] clauses are UNTAGGED (absent == no bytes), so they
   cannot use [sum] (§57 tag byte) nor [alt] (§62 no empty branch); the
   declaration is a [custom] codec (§58 legitimate use #1) whose [.dec] is a
   LIST-level scan ([Seq.seq_to_list]-at-the-boundary, §60) that tests the
   fixed keyword bytes with [decl_expect_bytes] to decide absent-vs-present.

   VersionNum is ['1.' [0-9]+] ([26]): accept ANY [1.x], roundtrip the
   version verbatim, [1.0] canonical (RFC-always; the stale task-table
   "reject <>1.x" was wrong).
   ======================================================================== *)

(** The [<?xml] prefix bytes (5 bytes). *)
let decl_open_bytes : list byte = [0x3Cuy; 0x3Fuy; 0x78uy; 0x6Duy; 0x6Cuy]

(** The [version] keyword bytes. *)
let kw_version_bytes : list byte = [0x76uy; 0x65uy; 0x72uy; 0x73uy; 0x69uy; 0x6Fuy; 0x6Euy]

(** The [encoding] keyword bytes. *)
let kw_encoding_bytes : list byte = [0x65uy; 0x6Euy; 0x63uy; 0x6Fuy; 0x64uy; 0x69uy; 0x6Euy; 0x67uy]

(** The [standalone] keyword bytes. *)
let kw_standalone_bytes : list byte = [0x73uy; 0x74uy; 0x61uy; 0x6Euy; 0x64uy; 0x61uy; 0x6Cuy; 0x6Fuy; 0x6Euy; 0x65uy]

(** The [?>] close bytes. *)
let decl_close_bytes : list byte = [0x3Fuy; 0x3Euy]

(** The [yes] bytes. *)
let decl_yes_bytes : list byte = [0x79uy; 0x65uy; 0x73uy]

(** The [no] bytes. *)
let decl_no_bytes : list byte = [0x6Euy; 0x6Fuy]

(** Is [b] an XML [S] whitespace byte (space/tab/CR/LF)? *)
let is_decl_ws_byte (b: byte) : bool =
  let v = U8.v b in v = 0x20 || v = 0x09 || v = 0x0D || v = 0x0A

(** Is [b] an ASCII digit (0-9)? *)
let is_verdigit_byte (b: byte) : bool =
  let v = U8.v b in 0x30 <= v && v <= 0x39

(** Is [b] an [EncName] byte ([A-Za-z0-9._-])? *)
let is_enc_name_byte (b: byte) : bool =
  let v = U8.v b in
  (0x41 <= v && v <= 0x5A) || (0x61 <= v && v <= 0x7A) ||
  (0x30 <= v && v <= 0x39) || v = 0x2E || v = 0x5F || v = 0x2D

(** Is [b] a single-quote (0x27) or double-quote (0x22)? *)
let is_decl_quote (b: byte) : bool = U8.v b = 0x22 || U8.v b = 0x27

(** Skip ZERO-or-more [S] whitespace bytes. *)
let rec decl_skip_ws_opt (bs: list byte) : Tot (list byte) (decreases bs) =
  match bs with
  | b :: tl -> if is_decl_ws_byte b then decl_skip_ws_opt tl else bs
  | [] -> bs

(** Skip ONE-or-more [S] whitespace bytes: [Some rest] with the whitespace
    dropped, [None] if there is no leading whitespace. *)
let decl_skip_ws (bs: list byte) : Tot (option (list byte)) =
  match bs with
  | b :: tl -> if is_decl_ws_byte b then Some (decl_skip_ws_opt tl) else None
  | [] -> None

(** Consume the fixed keyword [kw] ([kw] is a prefix of [bs]): [Some rest]
    after dropping [kw], [None] otherwise. *)
let rec decl_expect_bytes (kw: list byte) (bs: list byte) : Tot (option (list byte)) (decreases kw) =
  match kw with
  | [] -> Some bs
  | b :: tl ->
    (match bs with
     | b' :: rest -> if b = b' then decl_expect_bytes tl rest else None
     | [] -> None)

(** Consume the [Eq] production ([25]): [S? '=' S?]. *)
let decl_expect_eq (bs: list byte) : Tot (option (list byte)) =
  match decl_skip_ws_opt bs with
  | 0x3Duy :: after_eq -> Some (decl_skip_ws_opt after_eq)
  | _ -> None

(** Consume a quote byte, returning [Some (q, rest)] ([q] in {0x22,0x27}). *)
let decl_expect_quote (bs: list byte) : Tot (option (byte & list byte)) =
  match bs with
  | b :: tl -> if is_decl_quote b then Some (b, tl) else None
  | [] -> None

(** Consume the matching closing quote [q]. *)
let decl_expect_close_quote (q: byte) (bs: list byte) : Tot (option (list byte)) =
  match bs with
  | b :: tl -> if b = q then Some tl else None
  | [] -> None

(** Scan a VersionNum digit run (after the fixed [1.]): the digit bytes as
    a list, plus the rest. *)
let rec decl_scan_verdigits (bs: list byte) : Tot (list byte & list byte) (decreases bs) =
  match bs with
  | b :: tl -> if is_verdigit_byte b then let (ds, r) = decl_scan_verdigits tl in (b :: ds, r) else ([], bs)
  | [] -> ([], [])

(** Scan an [EncName] name: the name bytes (at least one) plus the rest. *)
let rec decl_scan_encname (bs: list byte) : Tot (list byte & list byte) (decreases bs) =
  match bs with
  | b :: tl -> if is_enc_name_byte b then let (ds, r) = decl_scan_encname tl in (b :: ds, r) else ([], bs)
  | [] -> ([], [])

(** Convert an ASCII byte list (each byte < 128) to its character list.

    This is the declaration's char-list reconstruction: the scan's digit /
    EncName runs are all ASCII bytes, so [byte_to_char] is total here.  The
    caller guarantees [U8.v b < 128] via the [is_verdigit_byte] /
    [is_enc_name_byte] gates in the scan. *)
let decl_bytes_to_chars (bs: list byte) : list char =
  List.Tot.map (fun b -> FStar.Char.char_of_int (U8.v b)) bs

(** Decode the optional [S 'encoding' Eq (quote) EncName (quote)] clause:
    [Some (Some name, rest)] when present, [Some (None, bs)] (no bytes
    consumed) when absent.  The EncName is carried as its grammar's own
    alphabet ([list char]). *)
let decl_optional_encoding (bs: list byte) : Tot (option (option (list char) & list byte)) =
  match decl_skip_ws bs with
  | None -> Some (None, bs)  (* no leading S — absent *)
  | Some after_ws ->
    (match decl_expect_bytes kw_encoding_bytes after_ws with
     | None -> Some (None, bs)  (* present S but not the keyword — absent *)
     | Some after_kw ->
       (match decl_expect_eq after_kw with
        | None -> None
        | Some after_eq ->
          (match decl_expect_quote after_eq with
           | None -> None
           | Some (q, after_q) ->
             let (name, after_name) = decl_scan_encname after_q in
             (match name with
              | [] -> None
              | _ ->
                (match decl_expect_close_quote q after_name with
                 | None -> None
                 | Some rest -> Some (Some (decl_bytes_to_chars name), rest))))))

(** Decode the optional [S 'standalone' Eq (quote) (yes|no) (quote)] clause. *)
let decl_optional_standalone (bs: list byte) : Tot (option (option bool & list byte)) =
  match decl_skip_ws bs with
  | None -> Some (None, bs)  (* absent *)
  | Some after_ws ->
    (match decl_expect_bytes kw_standalone_bytes after_ws with
     | None -> Some (None, bs)  (* present S but not the keyword — absent *)
     | Some after_kw ->
       (match decl_expect_eq after_kw with
        | None -> None
        | Some after_eq ->
          (match decl_expect_quote after_eq with
           | None -> None
           | Some (q, after_q) ->
             (match decl_expect_bytes decl_yes_bytes after_q with
              | Some after_yes ->
                (match decl_expect_close_quote q after_yes with
                 | Some rest -> Some (Some true, rest)
                 | None -> None)
              | None ->
                (match decl_expect_bytes decl_no_bytes after_q with
                 | Some after_no ->
                   (match decl_expect_close_quote q after_no with
                    | Some rest -> Some (Some false, rest)
                    | None -> None)
                 | None -> None)))))

(** Decode the full [<?xml ... ?>] declaration to an [xml_decl].  The
    canonical encoder emits double-quote delimiters; this decoder ACCEPTS
    either quote style ([24] quote equality) and re-encodes double-quoted. *)
let xml_decl_scan (bs: list byte) : Tot (option (xml_decl & list byte)) =
  match bs with
  | 0x3Cuy :: 0x3Fuy :: 0x78uy :: 0x6Duy :: 0x6Cuy :: after_open ->
    (match decl_skip_ws after_open with
     | None -> None
     | Some after_ws0 ->
       (match after_ws0 with
        | 0x76uy :: 0x65uy :: 0x72uy :: 0x73uy :: 0x69uy :: 0x6Fuy :: 0x6Euy :: after_ver_kw ->
          (match decl_expect_eq after_ver_kw with
           | None -> None
           | Some after_eq ->
             (match decl_expect_quote after_eq with
              | None -> None
              | Some (q0, after_q0) ->
                (match after_q0 with
                 | 0x31uy :: 0x2Euy :: after_one_dot ->
                   let (digits, after_ver) = decl_scan_verdigits after_one_dot in
                   (match digits with
                    | [] -> None
                    | _ ->
                      (match decl_expect_close_quote q0 after_ver with
                       | None -> None
                       | Some after_vq ->
                         (match decl_optional_encoding after_vq with
                          | None -> None
                          | Some (enc, after_enc) ->
                            (match decl_optional_standalone after_enc with
                             | None -> None
                             | Some (sa, after_sa) ->
                               (match decl_expect_bytes decl_close_bytes (decl_skip_ws_opt after_sa) with
                                | Some rest ->
                                  let ver = decl_bytes_to_chars (0x31uy :: 0x2Euy :: digits) in
                                  Some ({ decl_version = ver; decl_encoding = enc; decl_standalone = sa }, rest)
                                | None -> None)))))
                 | _ -> None)))
        | _ -> None))
  | _ -> None

(** Build the canonical declaration bytes for [d] (cons-only, double-quoted,
    single-space [S]).  The version/encoding carry [list char]; each char is
    rendered via [char_to_byte_trunc]. *)
let xml_decl_enc_bytes (d: xml_decl) : list byte =
  let ver = List.Tot.map char_to_byte_trunc d.decl_version in
  let enc_part =
    match d.decl_encoding with
    | None -> []
    | Some e -> [0x20uy] @ kw_encoding_bytes @ [0x3Duy; 0x22uy] @ List.Tot.map char_to_byte_trunc e @ [0x22uy] in
  let sa_part =
    match d.decl_standalone with
    | None -> []
    | Some b ->
      let word = if b then decl_yes_bytes else decl_no_bytes in
      [0x20uy] @ kw_standalone_bytes @ [0x3Duy; 0x22uy] @ word @ [0x22uy] in
  decl_open_bytes @ [0x20uy] @ kw_version_bytes @ [0x3Duy; 0x22uy] @
  ver @ [0x22uy] @ enc_part @ sa_part @ decl_close_bytes

(* ========================================================================
   Structural declaration parser reject vectors (finding M5 / task 2.4).

   [xml_decl_scan]/[decl_optional_encoding] reject the malformed declaration
   shapes the reviewer flagged: an empty VersionNum digit run ([1.]), an empty
   EncName, and (for the untested path) the [S]-present-but-not-keyword case
   (which returns [None, bs] — no consume — rather than a malformed error).
   ======================================================================== *)

(** An empty VersionNum digit run ([1.], the char-level form) is rejected by
    the [version_chars_ok] predicate (VersionNum requires one-or-more digits,
    production [26] — finding M5).  The full [xml_decl_scan] does not reduce
    cross-module (its [decl_scan_verdigits] [let rec] is §2-opaque), so the
    rejection is stated at the transparent char-level predicate gate — the
    same [version_chars_ok] the declaration WFCV uses. *)
#push-options "--z3rlimit 400"
let lemma_xml_decl_reject_empty_version () : Lemma
  (ensures version_chars_ok ['1'; '.'] == false)
  = assert_norm (version_chars_ok ['1'; '.'] == false)
#pop-options

(** A multi-dot version ([1.0.0]) is rejected by [version_chars_ok] (the
    second [.] is not a VersionNum digit). *)
#push-options "--z3rlimit 400"
let lemma_xml_decl_reject_multidot_version () : Lemma
  (ensures version_chars_ok ['1'; '.'; '0'; '.'; '0'] == false)
  = assert_norm (version_chars_ok ['1'; '.'; '0'; '.'; '0'] == false)
#pop-options

(** An empty EncName ([encoding=""]) is rejected by the char-level WFCV gate
    ([encname_chars_ok [] == false], production [81] — one-or-more EncName
    chars).  The byte-level [decl_optional_encoding] does not reduce
    cross-module (its [decl_scan_encname] [let rec] is §2-opaque); the char-
    level predicate is the [decl_encoding] WFCV gate. *)
#push-options "--z3rlimit 400"
let lemma_decl_reject_empty_encname () : Lemma
  (ensures encname_chars_ok [] == false)
  = assert_norm (encname_chars_ok [] == false)
#pop-options

(* ========================================================================
   Well-formedness + suffix conditions + roundtrip.
   ======================================================================== *)

(** Is [s] an ASCII string? *)
let decl_is_ascii (s: string) : bool =
  FStar.List.Tot.for_all (ascii_ok (fun _ -> true)) (FStar.String.list_of_string s)

(** Is [d] a well-formed declaration value?  (the char-list form, §63/§65.)

    [decl_version] is a well-formed VersionNum ([version_chars_ok], XML 1.0
    production [26]); [decl_encoding] is [None] or a well-formed EncName
    ([encname_chars_ok], production [81]).  Both carry [list char]; the chars
    are ASCII (so [char_to_byte_trunc] is exact — the §63 [small_mod] bridge).
    [decl_standalone] is unconstrained ([None] or [Some] [yes]/[no]).

    This gate the PURE parser surface ([xml_decl_scan]/[xml_decl_enc_bytes]) —
    there is NO [codec xml_decl]; the codec layer carries the declaration
    OPAQUELY via [xmldecl_text_codec] (§65).  It is a live regression anchor
    ([test_xml_decl_wfcv_full]) but wired into no codec. *)
let xml_decl_wfcv (d: xml_decl) : bool =
  version_chars_ok d.decl_version &&
  List.Tot.for_all (ascii_ok (fun _ -> true)) d.decl_version &&
  (match d.decl_encoding with
   | None -> true
   | Some e -> encname_chars_ok e && List.Tot.for_all (ascii_ok (fun _ -> true)) e) &&
  (match d.decl_standalone with None -> true | Some _ -> true)

(* ========================================================================
   The XML declaration as an OPAQUE validated string — the [custom] codec's
   roundtrip is proven via the SAME pattern as [doctype_decl_codec]: a single
   LIST-level scan ([scan_xmldecl], stopping at the top-level [?>]) plus a
   well-formedness predicate ([xmldecl_ok]) plus ONE structural-induction
   lemma ([lemma_scan_xmldecl_exact]).

   This is the 0-admit route for the declaration.  The STRUCTURED [xml_decl]
   value is recovered from the validated string by the PURE (non-codec)
   parser [xml_decl_scan] / rendered by [xml_decl_enc_bytes] above; the codec
   layer carries the declaration text OPAQUELY (exactly as [prolog_doctype :
   option string] carries the doctype), because the GENERAL structured
   roundtrip [dec (enc d ++ r) == Inr (d, …)] over a SYMBOLIC [decl_version]/
   [decl_encoding] hits the §65 list-constructor congruence wall even with a
   [list char] AST (fstar-proofs §65 — the doctype sidesteps it by carrying
   an opaque string).
   ======================================================================== *)

(** Scan one full XML declaration token, stopping at (and including) the
    first [?>] terminator.  The declaration has no interior [?>] (its
    version/encoding/standalone values are all quoted), so the FIRST [?>] is
    the terminator. *)
let rec scan_xmldecl (bs: list byte) : Tot (list byte & list byte) (decreases bs) =
  match bs with
  | [] -> ([], [])
  | 0x3Fuy :: 0x3Euy :: tl -> ([0x3Fuy; 0x3Euy], tl)
  | b :: tl -> let (c, r) = scan_xmldecl tl in (b :: c, r)

(** [decl_content_ok bs] — [bs] ends in exactly one [?>] terminator and has no
    interior [?>] (cons-recursive, so the scan induction unfolds it in
    lockstep — the [*_ok] pattern of §48/§50). *)
let rec decl_content_ok (bs: list byte) : Tot bool (decreases bs) =
  match bs with
  | [] -> false
  | 0x3Fuy :: 0x3Euy :: [] -> true
  | 0x3Fuy :: 0x3Euy :: _ -> false
  | _ :: tl -> decl_content_ok tl

(** [xml_decl_parse_ok bs] — [bs] parses as a structured [xml_decl]
    ([xml_decl_scan] succeeds). *)
let xml_decl_parse_ok (bs: list byte) : bool =
  match xml_decl_scan bs with Some _ -> true | None -> false

(** [xmldecl_ok bs] — [bs] is a well-formed XML declaration: it starts with
    the [<?xml] prefix, has a single terminal [?>], and its body parses. *)
let xmldecl_ok (bs: list byte) : bool =
  starts_with decl_open_bytes bs && decl_content_ok bs && xml_decl_parse_ok bs

(** The structural-induction fact: a well-formed declaration token scans
    exactly to its terminator.  The [decl_content_ok] [requires] is
    cons-recursive, so the scan unfolds the predicate in lockstep (§48/§50).
    The [?>]-terminal base case is the real base; the [[]] case is vacuous
    ([decl_content_ok [] = false]). *)
#push-options "--z3rlimit 800"
let rec lemma_scan_xmldecl_exact (content rest: list byte) : Lemma
  (requires decl_content_ok content)
  (ensures scan_xmldecl (content @ rest) == (content, rest))
  (decreases content)
  = match content with
    | [] -> ()
    | [0x3Fuy; 0x3Euy] -> ()
    | 0x3Fuy :: 0x3Euy :: _ -> ()   (* interior [?>] — [decl_content_ok] false, vacuous *)
    | b :: tl -> lemma_scan_xmldecl_exact tl rest
#pop-options

(** The [scan_xmldecl] content is no longer than the input. *)
let rec lemma_scan_xmldecl_content_le_len (bs: list byte) : Lemma
  (ensures List.Tot.length (fst (scan_xmldecl bs)) <= List.Tot.length bs)
  (decreases bs)
  = match bs with
    | [] -> ()
    | 0x3Fuy :: 0x3Euy :: _ -> ()
    | _ :: tl -> lemma_scan_xmldecl_content_le_len tl

(** The [scan_xmldecl] split is exact (content @ rest == bs). *)
let rec lemma_scan_xmldecl_split_exact (bs: list byte) : Lemma
  (ensures fst (scan_xmldecl bs) @ snd (scan_xmldecl bs) == bs)
  (decreases bs)
  = match bs with
    | [] -> ()
    | 0x3Fuy :: 0x3Euy :: _ -> ()
    | _ :: tl -> lemma_scan_xmldecl_split_exact tl

(** The declaration TEXT decoder (value = the opaque [<?xml ... ?>] string). *)
unfold
let xmldecl_text_dec (s: byte_seq) : decode_result string =
  let bs = Seq.seq_to_list s in
  let (content, rest) = scan_xmldecl bs in
  if xmldecl_ok content then Inr (text_bytes_to_string content, List.Tot.length content)
  else Inl (mk_decode_error ExpectedPredicate (List.Tot.length content))

(** The declaration TEXT encoder (identity on the opaque string). *)
unfold
let xmldecl_text_enc (s: string) : byte_seq = seq_of_list (text_string_to_bytes s)

(** The declaration TEXT well-formedness: ASCII + [xmldecl_ok]. *)
let xmldecl_text_wfcv (s: string) : bool =
  decl_is_ascii s && xmldecl_ok (text_string_to_bytes s)

(** Well-formed proposition — [True]. *)
let xmldecl_text_wfcv_prop (s: string) : prop = True

(** Suffix condition — [True]. *)
let xmldecl_text_rest_cond (s: string) (r: byte_seq) : prop = True

(** The declaration TEXT roundtrip (the doctype pattern, general [r]). *)
#push-options "--z3rlimit 800"
let lemma_xmldecl_text_roundtrip (s: string) (r: byte_seq) : Lemma
  (requires xmldecl_text_wfcv s /\ xmldecl_text_wfcv_prop s /\ xmldecl_text_rest_cond s r)
  (ensures xmldecl_text_dec (xmldecl_text_enc s `Seq.append` r) == Inr (s, Seq.length (xmldecl_text_enc s)))
  = let content = text_string_to_bytes s in
    assert (decl_is_ascii s);
    assert (xmldecl_ok content);
    assert (decl_content_ok content);
    lemma_text_string_to_bytes_roundtrip (fun _ -> true) s;
    assert (text_bytes_to_string content == s);
    lemma_seq_to_list_of_list_append content r;
    assert (Seq.seq_to_list (xmldecl_text_enc s `Seq.append` r) == content @ Seq.seq_to_list r);
    lemma_scan_xmldecl_exact content (Seq.seq_to_list r);
    assert (scan_xmldecl (content @ Seq.seq_to_list r) == (content, Seq.seq_to_list r));
    lemma_seq_of_list_length content;
    assert (Seq.length (xmldecl_text_enc s) == List.Tot.length content);
    assert (xmldecl_text_dec (xmldecl_text_enc s `Seq.append` r) == Inr (text_bytes_to_string content, List.Tot.length content));
    assert (xmldecl_text_dec (xmldecl_text_enc s `Seq.append` r) == Inr (s, Seq.length (xmldecl_text_enc s)));
    ()
#pop-options

(** Error-position bound for [xmldecl_text_dec]. *)
#push-options "--z3rlimit 400"
let lemma_xmldecl_text_dec_err_bound (s: byte_seq) : Lemma
  (ensures (match xmldecl_text_dec s with Inl err -> err.err_pos <= Seq.length s | _ -> True))
  = lemma_scan_xmldecl_content_le_len (Seq.seq_to_list s)
#pop-options

(** Consumed-count bound for [xmldecl_text_dec]. *)
#push-options "--z3rlimit 400"
let lemma_xmldecl_text_dec_consumed_bound (s: byte_seq) : Lemma
  (ensures (match xmldecl_text_dec s with Inr (_, n) -> n <= Seq.length s | _ -> True))
  = let bs = Seq.seq_to_list s in
    lemma_scan_xmldecl_split_exact bs;
    lemma_scan_xmldecl_content_le_len bs;
    let content = fst (scan_xmldecl bs) in
    let rest = snd (scan_xmldecl bs) in
    assert (content @ rest == bs);
    List.Tot.append_length content rest;
    assert (List.Tot.length content <= List.Tot.length bs);
    assert (List.Tot.length bs == Seq.length s);
    ()
#pop-options

(** [xmldecl_text_codec] — the XML declaration ([23]) carried as an opaque
    validated string (value = the full [<?xml ... ?>] text).  The roundtrip
    is proven 0-admit via the doctype pattern ([lemma_scan_xmldecl_exact]). *)
let xmldecl_text_codec : codec string =
  custom
    xmldecl_text_dec xmldecl_text_enc
    xmldecl_text_wfcv xmldecl_text_wfcv_prop xmldecl_text_rest_cond
    (fun s r -> lemma_xmldecl_text_roundtrip s r)
    lemma_xmldecl_text_dec_err_bound
    lemma_xmldecl_text_dec_consumed_bound

(* ========================================================================
   ExternalID ([75]) + SystemLiteral ([11]) / PubidLiteral ([12]).

   The [ExternalID] grammar ([SYSTEM S SystemLiteral] | [PUBLIC S PubidLiteral
   S SystemLiteral]) is VALIDATED as part of the doctype declaration
   envelope, NOT exposed as a standalone composed codec.  The list-level
   scans [doctype_scan_external_id] / [doctype_scan_system_id] /
   [doctype_scan_public_id] / [doctype_scan_quoted] (defined with the
   envelope scan above) are the [custom] doctype decoder's internals
   (fstar-proofs §58 legitimate use #1) that enforce the [75]/[11]/[12]
   shell.

   The former composed codecs ([system_literal_codec]/[pubid_literal_codec]/
   [external_id_codec]) were DELETED: they were dead scaffolding (wired into
   nothing, zero lemma/test coverage — finding M2).  A parallel composed
   combinator surface for the same grammar would be the §58 hand-written
   mirror anti-pattern; the doctype envelope scan is the single wired,
   proven realization of [ExternalID].

   Roundtrip/rejection coverage for the [ExternalID] shell lives at the
   doctype level: [lemma_doctype_accept_extid] ([<!DOCTYPE a SYSTEM
   "x.dtd">] accepted) and [lemma_doctype_reject_malformed_extid]
   ([<!DOCTYPE a SYSTEM>] unterminated literal rejected).
   ======================================================================== *)

(* ========================================================================
   Prolog composition ([22]): XMLDecl? Misc star (doctypedecl Misc star)?.

   The XML declaration and the doctype declaration are UNTAGGED-OPTIONAL
   (absent == no bytes) — they cannot use [sum] (§57 tag byte) nor [alt]
   (§62 no empty branch).  Each is therefore a [custom] codec (§58 legitimate
   use #1) whose [.dec] does a LIST-level prefix test ([is_prefix_of] the
   fixed open keyword) to decide absent-vs-present, then delegates to the
   already-proven opaque [xmldecl_text_codec] / [doctype_decl_codec].  The
   [Misc*] runs are the bounded [greedy] over [misc_opt], mapped to drop the
   whitespace [None] entries.
   ======================================================================== *)

(** [optional_decl_dec s] — [Some text] if [s] begins with the [<?xml]
    declaration keyword (delegating to [xmldecl_text_codec]), [None] with
    zero consumed bytes otherwise. *)
unfold
let optional_decl_dec (s: byte_seq) : decode_result (option string) =
  let bs = Seq.seq_to_list s in
  if starts_with decl_open_bytes bs then
    (match xmldecl_text_dec s with
     | Inr (text, n) -> Inr (Some text, n)
     | Inl e -> Inl e)
  else Inr (None, 0)

(** [optional_decl_enc] — the empty sequence for [None], the declaration text
    for [Some]. *)
unfold
let optional_decl_enc (o: option string) : byte_seq =
  match o with None -> Seq.empty | Some text -> xmldecl_text_enc text

(** [optional_decl] well-formedness: [None] is always fine; [Some text] must
    be a well-formed declaration text. *)
unfold
let optional_decl_wfcv (o: option string) : bool =
  match o with None -> true | Some text -> xmldecl_text_wfcv text

(** Well-formed proposition — [True]. *)
let optional_decl_wfcv_prop (o: option string) : prop = True

(** Suffix condition: for [None], the suffix must NOT begin a declaration
    (else the greedy optional would have consumed it); for [Some], defer to
    the declaration codec's own [rest_cond]. *)
unfold
let optional_decl_rest_cond (o: option string) (r: byte_seq) : prop =
  match o with
  | None -> not (starts_with decl_open_bytes (Seq.seq_to_list r))
  | Some text -> xmldecl_text_rest_cond text r

(** The optional-declaration roundtrip (the [custom] roundtrip via the
    doctype/xmldecl pattern).  For [None], [enc] is empty and [dec] returns
    [Inr (None, 0)] because the suffix does not begin [<?xml]; for [Some],
    the opaque declaration's own roundtrip discharges after the [<?xml]
    prefix guard ([starts_with decl_open_bytes], transparent) is re-established. *)
#push-options "--z3rlimit 2000 --ifuel 8 --fuel 8"
let lemma_optional_decl_roundtrip (o: option string) (r: byte_seq) : Lemma
  (requires optional_decl_wfcv o /\
            optional_decl_wfcv_prop o /\
            optional_decl_rest_cond o r)
  (ensures optional_decl_dec (optional_decl_enc o `Seq.append` r)
           == Inr (o, Seq.length (optional_decl_enc o)))
  = match o with
    | None ->
      append_empty_l r;
      assert (Seq.seq_to_list (Seq.append Seq.empty r) == Seq.seq_to_list r);
      ()
    | Some text ->
      assert (xmldecl_text_wfcv text);
      let content = text_string_to_bytes text in
      assert (xmldecl_ok content);
      assert (starts_with decl_open_bytes content);
      lemma_text_string_to_bytes_roundtrip (fun _ -> true) text;
      assert (text_bytes_to_string content == text);
      lemma_seq_to_list_of_list_append content r;
      assert (Seq.seq_to_list (xmldecl_text_enc text `Seq.append` r)
               == content @ Seq.seq_to_list r);
      lemma_starts_with_append decl_open_bytes content (Seq.seq_to_list r);
      lemma_xmldecl_text_roundtrip text r;
      ()
#pop-options

(** Error-position bound for [optional_decl_dec]. *)
#push-options "--z3rlimit 400"
let lemma_optional_decl_dec_err_bound (s: byte_seq) : Lemma
  (ensures (match optional_decl_dec s with Inl err -> err.err_pos <= Seq.length s | _ -> True))
  = if starts_with decl_open_bytes (Seq.seq_to_list s) then lemma_xmldecl_text_dec_err_bound s else ()
#pop-options

(** Consumed-count bound for [optional_decl_dec]. *)
#push-options "--z3rlimit 400"
let lemma_optional_decl_dec_consumed_bound (s: byte_seq) : Lemma
  (ensures (match optional_decl_dec s with Inr (_, n) -> n <= Seq.length s | _ -> True))
  = if starts_with decl_open_bytes (Seq.seq_to_list s) then lemma_xmldecl_text_dec_consumed_bound s else ()
#pop-options

(** [optional_decl] — the untagged-optional XML declaration ([23]) as an
    [option string] (opaque text, the doctype pattern). *)
let optional_decl : codec (option string) =
  custom
    optional_decl_dec optional_decl_enc
    optional_decl_wfcv optional_decl_wfcv_prop optional_decl_rest_cond
    lemma_optional_decl_roundtrip
    lemma_optional_decl_dec_err_bound
    lemma_optional_decl_dec_consumed_bound

(** [optional_doctype_dec s] — [Some text] if [s] begins with the
    [<!DOCTYPE] keyword (delegating to [doctype_decl_codec]), [None] with
    zero consumed bytes otherwise. *)
unfold
let optional_doctype_dec (s: byte_seq) : decode_result (option string) =
  let bs = Seq.seq_to_list s in
  if starts_with doctype_open_bytes bs then
    (match doctype_dec s with
     | Inr (text, n) -> Inr (Some text, n)
     | Inl e -> Inl e)
  else Inr (None, 0)

(** [optional_doctype_enc] — empty for [None], the doctype text for [Some]. *)
unfold
let optional_doctype_enc (o: option string) : byte_seq =
  match o with None -> Seq.empty | Some text -> doctype_enc text

(** [optional_doctype] well-formedness. *)
unfold
let optional_doctype_wfcv (o: option string) : bool =
  match o with None -> true | Some text -> doctype_wfcv text

(** Well-formed proposition — [True]. *)
let optional_doctype_wfcv_prop (o: option string) : prop = True

(** Suffix condition: for [None], the suffix must NOT begin a doctype. *)
unfold
let optional_doctype_rest_cond (o: option string) (r: byte_seq) : prop =
  match o with
  | None -> not (starts_with doctype_open_bytes (Seq.seq_to_list r))
  | Some text -> doctype_rest_cond text r

(** The optional-doctype roundtrip. *)
#push-options "--z3rlimit 2000 --ifuel 8 --fuel 8"
let lemma_optional_doctype_roundtrip (o: option string) (r: byte_seq) : Lemma
  (requires optional_doctype_wfcv o /\ optional_doctype_wfcv_prop o /\ optional_doctype_rest_cond o r)
  (ensures optional_doctype_dec (optional_doctype_enc o `Seq.append` r) == Inr (o, Seq.length (optional_doctype_enc o)))
  = match o with
    | None ->
      append_empty_l r;
      assert (Seq.seq_to_list (Seq.append Seq.empty r) == Seq.seq_to_list r);
      ()
    | Some text ->
      assert (doctype_wfcv text);
      let content = text_string_to_bytes text in
      assert (doctype_ok content);
      assert (starts_with doctype_open_bytes content);
      lemma_text_string_to_bytes_roundtrip (fun _ -> true) text;
      assert (text_bytes_to_string content == text);
      lemma_seq_to_list_of_list_append content r;
      assert (Seq.seq_to_list (doctype_enc text `Seq.append` r)
               == content @ Seq.seq_to_list r);
      lemma_starts_with_append doctype_open_bytes content (Seq.seq_to_list r);
      lemma_doctype_roundtrip text r;
      ()
#pop-options

(** Error-position bound for [optional_doctype_dec]. *)
#push-options "--z3rlimit 400"
let lemma_optional_doctype_dec_err_bound (s: byte_seq) : Lemma
  (ensures (match optional_doctype_dec s with Inl err -> err.err_pos <= Seq.length s | _ -> True))
  = if starts_with doctype_open_bytes (Seq.seq_to_list s) then lemma_doctype_dec_err_bound s else ()
#pop-options

(** Consumed-count bound for [optional_doctype_dec]. *)
#push-options "--z3rlimit 400"
let lemma_optional_doctype_dec_consumed_bound (s: byte_seq) : Lemma
  (ensures (match optional_doctype_dec s with Inr (_, n) -> n <= Seq.length s | _ -> True))
  = if starts_with doctype_open_bytes (Seq.seq_to_list s) then lemma_doctype_dec_consumed_bound s else ()
#pop-options

(** [optional_doctype] — the untagged-optional doctype declaration ([28]) as
    an [option string]. *)
let optional_doctype : codec (option string) =
  custom
    optional_doctype_dec optional_doctype_enc
    optional_doctype_wfcv optional_doctype_wfcv_prop optional_doctype_rest_cond
    lemma_optional_doctype_roundtrip
    lemma_optional_doctype_dec_err_bound
    lemma_optional_doctype_dec_consumed_bound
