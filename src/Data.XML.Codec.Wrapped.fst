(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)

(**
Data.XML.Codec.Wrapped — comment, CDATA, and PI codecs (delimiter-wrapped text).

Each of these three leaf codecs has the shape [open-marker ++ content ++
close-marker], where the content is a run delimited by a MULTI-BYTE close
marker that the content may PARTIALLY contain.  XML 1.0 forbids only the
close-marker sequence (and, for comments, the two-dash run), NOT the single
leading byte — so single `-`/`]`/`?` inside content are LEGAL.

Such content is delimiter-AWARE.  The open/close markers are decoded with the
proven [bytes] combinator ([lemma_bytes_self_prefix_spec]); the CONTENT is a
[custom] decoder that does [Seq.seq_to_list] ONCE at the boundary, then a
LIST-level scan (where a multi-byte lookahead reduces — fstar-proofs §50),
validating the RFC-correct content predicate ([comment_ok]/[cdata_ok]/
[pi_ok]).  The GENERAL-[r] roundtrip — the [codec] record's [.roundtrip] field,
which requires [dec (enc v ++ r) == Inr (v, |enc v|)] for an ARBITRARY
[r: byte_seq] — is proven by chaining [lemma_seq_to_list_of_list_append] (the
[seq_to_list]-distributes-over-append bridge, in [Data.Codec.Types]) with the
list-level [lemma_scan_*_exact] structural-induction facts (fstar-proofs §50).

The RFC productions carried:

- Comment [15] — [comment_ok] rejects a two-dash run and a trailing dash;
  a single dash is LEGAL (fixes the Phase-3.5 over-restriction).
- CDATA [18]/[20] — [cdata_ok] rejects only the close marker []]>].
- PI [16] — [pi_ok] rejects only the close marker [?]>].

They live in this CHILD module (fstar-proofs §45 workaround #2), isolated from
[Data.XML.Codec]'s combinator chains so the [custom] leaf roundtrips stay 0-admit.

@header Data.XML.Codec.Wrapped
*)
module Data.XML.Codec.Wrapped

open Data.Codec
open Data.Text.Codec
open Data.Text.Codec.Chars
open FStar.Seq
open FStar.UInt8
open FStar.List.Tot

module U8 = FStar.UInt8
module Seq = FStar.Seq

(* ========================================================================
   Markers.
   ======================================================================== *)

(** The comment close marker ([-->]). *)
let comment_close_bytes : list byte = [0x2Duy; 0x2Duy; 0x3Euy]

(** The CDATA close marker ([]]>). *)
let cdata_close_bytes : list byte = [0x5Duy; 0x5Duy; 0x3Euy]

(** The PI close marker ([?>]). *)
let pi_close_bytes : list byte = [0x3Fuy; 0x3Euy]

(* ========================================================================
   RFC-correct content-validity predicates (list level).
   ======================================================================== *)

(** Comment content is well-formed: no two-dash run, and no trailing dash
    (a dash must be followed by a non-dash).  A single interior dash is LEGAL
    (XML 1.0 production [15]). *)
let rec comment_ok (bs: list byte) : Tot bool (decreases bs) =
  match bs with
  | [0x2Duy] -> false                 (* trailing dash *)
  | 0x2Duy :: 0x2Duy :: _ -> false    (* two-dash run *)
  | _ :: tl -> comment_ok tl
  | [] -> true

(** CDATA content is well-formed: no close-marker []]>] sequence (a lone
    []] or []]] is LEGAL, production [18]/[20]). *)
let rec cdata_ok (bs: list byte) : Tot bool (decreases bs) =
  match bs with
  | 0x5Duy :: 0x5Duy :: 0x3Euy :: _ -> false
  | _ :: tl -> cdata_ok tl
  | [] -> true

(** PI content is well-formed: no close-marker [?>] sequence (a lone [?]
    is LEGAL, production [16]). *)
let rec pi_ok (bs: list byte) : Tot bool (decreases bs) =
  match bs with
  | 0x3Fuy :: 0x3Euy :: _ -> false
  | _ :: tl -> pi_ok tl
  | [] -> true

(* ========================================================================
   List-level scans (the [custom] decoder internals, fstar-proofs §58 #1).
   ======================================================================== *)

(** Scan comment content, stopping at the two-dash prefix of [-->]. *)
let rec scan_comment (bs: list byte) : Tot (list byte & list byte) (decreases bs) =
  match bs with
  | 0x2Duy :: (0x2Duy :: _) -> ([], bs)
  | b :: rest -> let content, remaining = scan_comment rest in (b :: content, remaining)
  | [] -> ([], [])

(** Scan CDATA content, stopping at the []]>] close marker. *)
let rec scan_cdata (bs: list byte) : Tot (list byte & list byte) (decreases bs) =
  match bs with
  | 0x5Duy :: (0x5Duy :: (0x3Euy :: _)) -> ([], bs)
  | b :: rest -> let content, remaining = scan_cdata rest in (b :: content, remaining)
  | [] -> ([], [])

(** Scan PI content, stopping at the [?>] close marker. *)
let rec scan_pi (bs: list byte) : Tot (list byte & list byte) (decreases bs) =
  match bs with
  | 0x3Fuy :: (0x3Euy :: _) -> ([], bs)
  | b :: rest -> let content, remaining = scan_pi rest in (b :: content, remaining)
  | [] -> ([], [])

(* ========================================================================
   Roundtrip lemmas for the scans (structural induction, fstar-proofs §50).
   ======================================================================== *)

(** A well-formed comment content scans exactly to its close marker. *)
let rec lemma_scan_comment_exact (content r: list byte) : Lemma
  (requires comment_ok content == true)
  (ensures scan_comment (content @ comment_close_bytes @ r)
           == (content, comment_close_bytes @ r))
  (decreases content)
  = match content with
    | [] -> ()
    | b :: tl -> lemma_scan_comment_exact tl r

(** A well-formed CDATA content scans exactly to its close marker. *)
let rec lemma_scan_cdata_exact (content r: list byte) : Lemma
  (requires cdata_ok content == true)
  (ensures scan_cdata (content @ cdata_close_bytes @ r)
           == (content, cdata_close_bytes @ r))
  (decreases content)
  = match content with
    | [] -> ()
    | b :: tl -> lemma_scan_cdata_exact tl r

(** A well-formed PI content scans exactly to its close marker. *)
let rec lemma_scan_pi_exact (content r: list byte) : Lemma
  (requires pi_ok content == true)
  (ensures scan_pi (content @ pi_close_bytes @ r)
           == (content, pi_close_bytes @ r))
  (decreases content)
  = match content with
    | [] -> ()
    | b :: tl -> lemma_scan_pi_exact tl r

(* ========================================================================
   Scan length bounds (the [custom] err/consumed-bound lemmas).
   ======================================================================== *)

(** The content scanned by [scan_comment] is no longer than the input. *)
let rec lemma_scan_comment_content_le_len (bs: list byte) : Lemma
  (ensures List.Tot.length (fst (scan_comment bs)) <= List.Tot.length bs)
  (decreases bs)
  = match bs with
    | [] -> ()
    | 0x2Duy :: 0x2Duy :: _ -> ()
    | _ :: tl -> lemma_scan_comment_content_le_len tl

(** The content scanned by [scan_cdata] is no longer than the input. *)
let rec lemma_scan_cdata_content_le_len (bs: list byte) : Lemma
  (ensures List.Tot.length (fst (scan_cdata bs)) <= List.Tot.length bs)
  (decreases bs)
  = match bs with
    | [] -> ()
    | 0x5Duy :: 0x5Duy :: 0x3Euy :: _ -> ()
    | _ :: tl -> lemma_scan_cdata_content_le_len tl

(** The content scanned by [scan_pi] is no longer than the input. *)
let rec lemma_scan_pi_content_le_len (bs: list byte) : Lemma
  (ensures List.Tot.length (fst (scan_pi bs)) <= List.Tot.length bs)
  (decreases bs)
  = match bs with
    | [] -> ()
    | 0x3Fuy :: 0x3Euy :: _ -> ()
    | _ :: tl -> lemma_scan_pi_content_le_len tl

(* ========================================================================
   Found-bound lemmas: the scan split is exact (content ++ rest == bs), so
   when the close marker is found, |content| + |close| <= |bs|.
   ======================================================================== *)

(** [scan_comment] splits its input exactly: content @ rest == bs. *)
let rec lemma_scan_comment_split_exact (bs: list byte) : Lemma
  (ensures fst (scan_comment bs) @ snd (scan_comment bs) == bs)
  (decreases bs)
  = match bs with
    | [] -> ()
    | 0x2Duy :: 0x2Duy :: _ -> ()
    | _ :: tl -> lemma_scan_comment_split_exact tl

(** [scan_cdata] splits its input exactly. *)
let rec lemma_scan_cdata_split_exact (bs: list byte) : Lemma
  (ensures fst (scan_cdata bs) @ snd (scan_cdata bs) == bs)
  (decreases bs)
  = match bs with
    | [] -> ()
    | 0x5Duy :: 0x5Duy :: 0x3Euy :: _ -> ()
    | _ :: tl -> lemma_scan_cdata_split_exact tl

(** [scan_pi] splits its input exactly. *)
let rec lemma_scan_pi_split_exact (bs: list byte) : Lemma
  (ensures fst (scan_pi bs) @ snd (scan_pi bs) == bs)
  (decreases bs)
  = match bs with
    | [] -> ()
    | 0x3Fuy :: 0x3Euy :: _ -> ()
    | _ :: tl -> lemma_scan_pi_split_exact tl

(* ========================================================================
   ASCII guard (reused [ascii_ok] from [Data.Text.Codec.Chars]).
   ======================================================================== *)

(** A list is a prefix of itself extended by any suffix. *)
let rec lemma_is_prefix_self_append (#a:eqtype) (p l: list a) : Lemma
  (ensures is_prefix_of p (p @ l) == true)
  (decreases p)
  = match p with
    | [] -> ()
    | _ :: tl -> lemma_is_prefix_self_append tl l

(** The content is an ASCII string, so the low-byte string↔bytes roundtrip
    holds ([lemma_text_string_to_bytes_roundtrip]).  Uses [ascii_ok] so its
    [for_all] shape matches the roundtrip lemma's [requires] exactly. *)
let is_ascii_string (s: string) : bool =
  FStar.List.Tot.for_all (ascii_ok (fun _ -> true)) (FStar.String.list_of_string s)

(* ========================================================================
   CONTENT codecs (value = content string; wire = [content ++ close-marker]).
   The open marker is decoded by the caller via [bytes].  Each has a
   GENERAL-[r] roundtrip.
   ======================================================================== *)

(** Comment content decoder: [content -->] → the content string. *)
unfold
let comment_content_dec (s: byte_seq) : decode_result string =
  let bs = Seq.seq_to_list s in
  let (content, rest) = scan_comment bs in
  if is_prefix_of comment_close_bytes rest then
    if comment_ok content then Inr (text_bytes_to_string content, List.Tot.length content + 3)
    else Inl (mk_decode_error ExpectedPredicate (List.Tot.length content))
  else Inl (mk_decode_error UnexpectedEndOfInput (List.Tot.length content))

(** Comment content encoder: content string → [content -->]. *)
let comment_content_enc (s: string) : byte_seq =
  seq_of_list (text_string_to_bytes s @ comment_close_bytes)

(** Comment content well-formedness. *)
let comment_content_wfcv (s: string) : bool =
  is_ascii_string s && comment_ok (text_string_to_bytes s)

(** Comment content well-formed proposition — [True] (finding N3).

    [wfcv_prop = True] is NOT a §24 "ensures True" shortcut: the NON-VACUOUS
    proof is [comment_content_roundtrip] below, whose [requires] forces [wfcv]
    ([is_ascii_string s && comment_ok …]) at every call site and whose
    [ensures] proves the [dec (enc s ++ r) == Inr (s, …)] roundtrip (§60/
    §62 list-level scan).  [True] here only declines to re-state the
    content-validity predicate as a separate [prop]; the real validity gate
    is [wfcv]. *)
let comment_content_wfcv_prop (s: string) : prop = True

(** Comment content suffix condition — [True] (finding N3): a terminated
    [-->]-delimited literal has no suffix constraint; the non-vacuous
    roundtrip proof is [comment_content_roundtrip]. *)
let comment_content_rest_cond (s: string) (r: byte_seq) : prop = True

(** CDATA content decoder: [content ]]]>] → the content string. *)
unfold
let cdata_content_dec (s: byte_seq) : decode_result string =
  let bs = Seq.seq_to_list s in
  let (content, rest) = scan_cdata bs in
  if is_prefix_of cdata_close_bytes rest then
    if cdata_ok content then Inr (text_bytes_to_string content, List.Tot.length content + 3)
    else Inl (mk_decode_error ExpectedPredicate (List.Tot.length content))
  else Inl (mk_decode_error UnexpectedEndOfInput (List.Tot.length content))

(** CDATA content encoder: content string → [content ]]]>]. *)
let cdata_content_enc (s: string) : byte_seq =
  seq_of_list (text_string_to_bytes s @ cdata_close_bytes)

(** CDATA content well-formedness. *)
let cdata_content_wfcv (s: string) : bool =
  is_ascii_string s && cdata_ok (text_string_to_bytes s)

(** CDATA content well-formed proposition — [True] (finding N3): [wfcv]
    ([is_ascii_string s && cdata_ok …]) is the real gate; the non-vacuous
    roundtrip proof is [cdata_content_roundtrip] below. *)
let cdata_content_wfcv_prop (s: string) : prop = True

(** CDATA content suffix condition — [True] (finding N3): a terminated
    []]]>]-delimited literal has no suffix constraint; the non-vacuous proof
    is [cdata_content_roundtrip]. *)
let cdata_content_rest_cond (s: string) (r: byte_seq) : prop = True

(** PI content decoder: [content ?>] → the content string. *)
unfold
let pi_content_dec (s: byte_seq) : decode_result string =
  let bs = Seq.seq_to_list s in
  let (content, rest) = scan_pi bs in
  if is_prefix_of pi_close_bytes rest then
    if pi_ok content then Inr (text_bytes_to_string content, List.Tot.length content + 2)
    else Inl (mk_decode_error ExpectedPredicate (List.Tot.length content))
  else Inl (mk_decode_error UnexpectedEndOfInput (List.Tot.length content))

(** PI content encoder: content string → [content ?>]. *)
let pi_content_enc (s: string) : byte_seq =
  seq_of_list (text_string_to_bytes s @ pi_close_bytes)

(** PI content well-formedness. *)
let pi_content_wfcv (s: string) : bool =
  is_ascii_string s && pi_ok (text_string_to_bytes s)

(** PI content well-formed proposition — [True] (finding N3): [wfcv]
    ([is_ascii_string s && pi_ok …]) is the real gate; the non-vacuous
    roundtrip proof is [pi_content_roundtrip] below. *)
let pi_content_wfcv_prop (s: string) : prop = True

(** PI content suffix condition — [True] (finding N3): a terminated
    [?]>-delimited literal has no suffix constraint; the non-vacuous proof
    is [pi_content_roundtrip]. *)
let pi_content_rest_cond (s: string) (r: byte_seq) : prop = True

(* ========================================================================
   GENERAL-[r] roundtrip lemmas for the CONTENT codecs.
   ======================================================================== *)

(** Comment content roundtrip. *)
#push-options "--z3rlimit 800"
let comment_content_roundtrip (s: string) (r: byte_seq) : Lemma
  (requires comment_content_wfcv s /\ comment_content_wfcv_prop s /\ comment_content_rest_cond s r)
  (ensures comment_content_dec (comment_content_enc s `Seq.append` r)
            == Inr (s, Seq.length (comment_content_enc s)))
  = let content = text_string_to_bytes s in
    let l = content @ comment_close_bytes in
    assert (is_ascii_string s);
    assert (comment_ok content);
    lemma_text_string_to_bytes_roundtrip (fun _ -> true) s;
    assert (text_bytes_to_string content == s);
    lemma_seq_to_list_of_list_append l r;
    List.Tot.append_assoc content comment_close_bytes (Seq.seq_to_list r);
    assert (Seq.seq_to_list (comment_content_enc s `Seq.append` r)
             == content @ comment_close_bytes @ Seq.seq_to_list r);
    lemma_scan_comment_exact content (Seq.seq_to_list r);
    lemma_is_prefix_self_append comment_close_bytes (Seq.seq_to_list r);
    lemma_seq_of_list_length l;
    List.Tot.append_length content comment_close_bytes;
    assert (List.Tot.length comment_close_bytes == 3);
    assert (Seq.length (comment_content_enc s) == List.Tot.length content + 3);
    let result : decode_result string = comment_content_dec (comment_content_enc s `Seq.append` r) in
    assert (result == Inr (text_bytes_to_string content, List.Tot.length content + 3));
    ()
#pop-options

(** CDATA content roundtrip. *)
#push-options "--z3rlimit 800"
let cdata_content_roundtrip (s: string) (r: byte_seq) : Lemma
  (requires cdata_content_wfcv s /\ cdata_content_wfcv_prop s /\ cdata_content_rest_cond s r)
  (ensures cdata_content_dec (cdata_content_enc s `Seq.append` r)
            == Inr (s, Seq.length (cdata_content_enc s)))
  = let content = text_string_to_bytes s in
    let l = content @ cdata_close_bytes in
    assert (is_ascii_string s);
    assert (cdata_ok content);
    lemma_text_string_to_bytes_roundtrip (fun _ -> true) s;
    assert (text_bytes_to_string content == s);
    lemma_seq_to_list_of_list_append l r;
    List.Tot.append_assoc content cdata_close_bytes (Seq.seq_to_list r);
    assert (Seq.seq_to_list (cdata_content_enc s `Seq.append` r)
             == content @ cdata_close_bytes @ Seq.seq_to_list r);
    lemma_scan_cdata_exact content (Seq.seq_to_list r);
    lemma_is_prefix_self_append cdata_close_bytes (Seq.seq_to_list r);
    lemma_seq_of_list_length l;
    List.Tot.append_length content cdata_close_bytes;
    assert (List.Tot.length cdata_close_bytes == 3);
    assert (Seq.length (cdata_content_enc s) == List.Tot.length content + 3);
    let result : decode_result string = cdata_content_dec (cdata_content_enc s `Seq.append` r) in
    assert (result == Inr (text_bytes_to_string content, List.Tot.length content + 3));
    ()
#pop-options

(** PI content roundtrip. *)
#push-options "--z3rlimit 800"
let pi_content_roundtrip (s: string) (r: byte_seq) : Lemma
  (requires pi_content_wfcv s /\ pi_content_wfcv_prop s /\ pi_content_rest_cond s r)
  (ensures pi_content_dec (pi_content_enc s `Seq.append` r)
            == Inr (s, Seq.length (pi_content_enc s)))
  = let content = text_string_to_bytes s in
    let l = content @ pi_close_bytes in
    assert (is_ascii_string s);
    assert (pi_ok content);
    lemma_text_string_to_bytes_roundtrip (fun _ -> true) s;
    assert (text_bytes_to_string content == s);
    lemma_seq_to_list_of_list_append l r;
    List.Tot.append_assoc content pi_close_bytes (Seq.seq_to_list r);
    assert (Seq.seq_to_list (pi_content_enc s `Seq.append` r)
             == content @ pi_close_bytes @ Seq.seq_to_list r);
    lemma_scan_pi_exact content (Seq.seq_to_list r);
    lemma_is_prefix_self_append pi_close_bytes (Seq.seq_to_list r);
    lemma_seq_of_list_length l;
    List.Tot.append_length content pi_close_bytes;
    assert (List.Tot.length pi_close_bytes == 2);
    assert (Seq.length (pi_content_enc s) == List.Tot.length content + 2);
    let result : decode_result string = pi_content_dec (pi_content_enc s `Seq.append` r) in
    assert (result == Inr (text_bytes_to_string content, List.Tot.length content + 2));
    ()
#pop-options

(* ========================================================================
   Error- and consumed-count bound lemmas (the [custom] field requirements).
   ======================================================================== *)

(** The comment-content decoder's error position is bounded by the input
    length. *)
#push-options "--z3rlimit 400"
let lemma_comment_content_dec_err_bound (s: byte_seq) : Lemma
  (ensures (match comment_content_dec s with Inl err -> err.err_pos <= Seq.length s | _ -> True))
  = lemma_scan_comment_content_le_len (Seq.seq_to_list s)
#pop-options

(** The comment-content decoder's consumed count is bounded by the input
    length. *)
#push-options "--z3rlimit 400"
let lemma_comment_content_dec_consumed_bound (s: byte_seq) : Lemma
  (ensures (match comment_content_dec s with Inr (_, n) -> n <= Seq.length s | _ -> True))
  = let bs = Seq.seq_to_list s in
    lemma_scan_comment_split_exact bs;
    lemma_scan_comment_content_le_len bs;
    let content = fst (scan_comment bs) in
    let rest = snd (scan_comment bs) in
    assert (content @ rest == bs);
    List.Tot.append_length content rest;
    assert (List.Tot.length content + List.Tot.length rest == List.Tot.length bs);
    assert (List.Tot.length bs == Seq.length s);
    assert (List.Tot.length comment_close_bytes == 3);
    if is_prefix_of comment_close_bytes rest then begin
      lemma_is_prefix_len comment_close_bytes rest;
      assert (3 <= List.Tot.length rest);
      assert (List.Tot.length content + 3 <= List.Tot.length bs);
      ()
    end else ()
#pop-options

(** The CDATA-content decoder's error position is bounded by the input
    length. *)
#push-options "--z3rlimit 400"
let lemma_cdata_content_dec_err_bound (s: byte_seq) : Lemma
  (ensures (match cdata_content_dec s with Inl err -> err.err_pos <= Seq.length s | _ -> True))
  = lemma_scan_cdata_content_le_len (Seq.seq_to_list s)
#pop-options

(** The CDATA-content decoder's consumed count is bounded by the input
    length. *)
#push-options "--z3rlimit 400"
let lemma_cdata_content_dec_consumed_bound (s: byte_seq) : Lemma
  (ensures (match cdata_content_dec s with Inr (_, n) -> n <= Seq.length s | _ -> True))
  = let bs = Seq.seq_to_list s in
    lemma_scan_cdata_split_exact bs;
    lemma_scan_cdata_content_le_len bs;
    let content = fst (scan_cdata bs) in
    let rest = snd (scan_cdata bs) in
    assert (content @ rest == bs);
    List.Tot.append_length content rest;
    assert (List.Tot.length content + List.Tot.length rest == List.Tot.length bs);
    assert (List.Tot.length bs == Seq.length s);
    assert (List.Tot.length cdata_close_bytes == 3);
    if is_prefix_of cdata_close_bytes rest then begin
      lemma_is_prefix_len cdata_close_bytes rest;
      assert (3 <= List.Tot.length rest);
      assert (List.Tot.length content + 3 <= List.Tot.length bs);
      ()
    end else ()
#pop-options

(** The PI-content decoder's error position is bounded by the input length. *)
#push-options "--z3rlimit 400"
let lemma_pi_content_dec_err_bound (s: byte_seq) : Lemma
  (ensures (match pi_content_dec s with Inl err -> err.err_pos <= Seq.length s | _ -> True))
  = lemma_scan_pi_content_le_len (Seq.seq_to_list s)
#pop-options

(** The PI-content decoder's consumed count is bounded by the input length. *)
#push-options "--z3rlimit 400"
let lemma_pi_content_dec_consumed_bound (s: byte_seq) : Lemma
  (ensures (match pi_content_dec s with Inr (_, n) -> n <= Seq.length s | _ -> True))
  = let bs = Seq.seq_to_list s in
    lemma_scan_pi_split_exact bs;
    lemma_scan_pi_content_le_len bs;
    let content = fst (scan_pi bs) in
    let rest = snd (scan_pi bs) in
    assert (content @ rest == bs);
    List.Tot.append_length content rest;
    assert (List.Tot.length content + List.Tot.length rest == List.Tot.length bs);
    assert (List.Tot.length bs == Seq.length s);
    assert (List.Tot.length pi_close_bytes == 2);
    if is_prefix_of pi_close_bytes rest then begin
      lemma_is_prefix_len pi_close_bytes rest;
      assert (2 <= List.Tot.length rest);
      assert (List.Tot.length content + 2 <= List.Tot.length bs);
      ()
    end else ()
#pop-options

(* ========================================================================
   The public leaf content codecs — [codec string] with general-[r] roundtrips.
   ======================================================================== *)

(** [comment_content_codec] — [content -->]. *)
let comment_content_codec : codec string =
  custom
    comment_content_dec comment_content_enc
    comment_content_wfcv comment_content_wfcv_prop comment_content_rest_cond
    (fun s r -> comment_content_roundtrip s r)
    lemma_comment_content_dec_err_bound
    lemma_comment_content_dec_consumed_bound

(** [cdata_content_codec] — [content ]]]>]. *)
let cdata_content_codec : codec string =
  custom
    cdata_content_dec cdata_content_enc
    cdata_content_wfcv cdata_content_wfcv_prop cdata_content_rest_cond
    (fun s r -> cdata_content_roundtrip s r)
    lemma_cdata_content_dec_err_bound
    lemma_cdata_content_dec_consumed_bound

(** [pi_content_codec] — [content ?>]. *)
let pi_content_codec : codec string =
  custom
    pi_content_dec pi_content_enc
    pi_content_wfcv pi_content_wfcv_prop pi_content_rest_cond
    (fun s r -> pi_content_roundtrip s r)
    lemma_pi_content_dec_err_bound
    lemma_pi_content_dec_consumed_bound

(* ========================================================================
   Concrete roundtrip vectors — the legal single-[-/-]/? forms Phase 3.5
   over-restricted.
   ======================================================================== *)

(** [<!--a-b-->] (single interior dash) roundtrips to ["a-b"].  Legal per
    RFC [15] — the exact vector Phase 3.5's single-char predicate rejected. *)
let lemma_comment_single_dash_roundtrip () : Lemma
  (ensures comment_content_dec (comment_content_enc "a-b")
            == Inr ("a-b", Seq.length (comment_content_enc "a-b")))
  = assert_norm (comment_content_wfcv "a-b" == true);
    comment_content_roundtrip "a-b" Seq.empty;
    Seq.append_empty_r (comment_content_enc "a-b")

(** [<![CDATA[a]b]]>] (single interior bracket) roundtrips to ["a]b"]. *)
let lemma_cdata_single_bracket_roundtrip () : Lemma
  (ensures cdata_content_dec (cdata_content_enc "a]b")
            == Inr ("a]b", Seq.length (cdata_content_enc "a]b")))
  = assert_norm (cdata_content_wfcv "a]b" == true);
    cdata_content_roundtrip "a]b" Seq.empty;
    Seq.append_empty_r (cdata_content_enc "a]b")

(** [<?a?b?>] (single interior question) roundtrips to ["a?b"]. *)
let lemma_pi_single_question_roundtrip () : Lemma
  (ensures pi_content_dec (pi_content_enc "a?b")
            == Inr ("a?b", Seq.length (pi_content_enc "a?b")))
  = assert_norm (pi_content_wfcv "a?b" == true);
    pi_content_roundtrip "a?b" Seq.empty;
    Seq.append_empty_r (pi_content_enc "a?b")

(* ========================================================================
   Rejection lemmas — the forbidden forms (fstar-proofs §51 Pitfall 2).
   ======================================================================== *)

(** A two-dash comment content is rejected. *)
let lemma_comment_double_dash_rejected () : Lemma
  (ensures comment_ok [0x61uy; 0x2Duy; 0x2Duy; 0x62uy] == false)
  = ()

(** A trailing-dash comment content is rejected. *)
let lemma_comment_trailing_dash_rejected () : Lemma
  (ensures comment_ok [0x61uy; 0x2Duy] == false)
  = ()

(** A CDATA close marker in content is rejected. *)
let lemma_cdata_close_rejected () : Lemma
  (ensures cdata_ok [0x61uy; 0x5Duy; 0x5Duy; 0x3Euy] == false)
  = ()

(** A PI close marker in content is rejected. *)
let lemma_pi_close_rejected () : Lemma
  (ensures pi_ok [0x61uy; 0x3Fuy; 0x3Euy] == false)
  = ()

(* ========================================================================
   CODEC-level rejection lemmas (finding M4 / task 2.2).

   The SPEC predicates ([comment_ok]/[cdata_ok]/[pi_ok]) reject the forbidden
   interior sequence, but the DECODER's rejection is INCIDENTAL (§51 Pitfall 2):
   the list-level scan stops at the first forbidden prefix, so the close-marker
   boundary check ([is_prefix_of close rest]) fails and the content codec's
   [.dec] returns [Inl].  These lemmas state that [.dec] result DIRECTLY on a
   truncated (missing/partial close-marker) vector, proving the CODECD-level
   rejection — not merely the predicate ([*_ok] == [false]).  The [is_prefix_of]
   calls reduce under [assert_norm] (the normalizer unfolds the cross-module
   [let rec] even though SMT treats it as opaque, §66 Wall 1).
   ======================================================================== *)

(** A truncated comment content ([a-], no [-->] close) is rejected by the
    content codec's DECODER. *)
#push-options "--z3rlimit 400"
let lemma_comment_dec_reject_truncated () : Lemma
  (ensures Inl? (comment_content_dec (seq_of_list [0x61uy; 0x2Duy])))
  = assert_norm (scan_comment [0x61uy; 0x2Duy] == ([0x61uy; 0x2Duy], []));
    assert_norm (is_prefix_of comment_close_bytes [] == false);
    ()
#pop-options

(** A truncated CDATA content ([a]]], no []]]>] close) is rejected by the
    content codec's DECODER. *)
#push-options "--z3rlimit 400"
let lemma_cdata_dec_reject_truncated () : Lemma
  (ensures Inl? (cdata_content_dec (seq_of_list [0x61uy; 0x5Duy; 0x5Duy])))
  = assert_norm (scan_cdata [0x61uy; 0x5Duy; 0x5Duy] == ([0x61uy; 0x5Duy; 0x5Duy], []));
    assert_norm (is_prefix_of cdata_close_bytes [] == false);
    ()
#pop-options

(** A truncated PI content ([a?], no [?>] close) is rejected by the content
    codec's DECODER. *)
#push-options "--z3rlimit 400"
let lemma_pi_dec_reject_truncated () : Lemma
  (ensures Inl? (pi_content_dec (seq_of_list [0x61uy; 0x3Fuy])))
  = assert_norm (scan_pi [0x61uy; 0x3Fuy] == ([0x61uy; 0x3Fuy], []));
    assert_norm (is_prefix_of pi_close_bytes [] == false);
    ()
#pop-options
