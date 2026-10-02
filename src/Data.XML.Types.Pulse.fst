(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)

(**
Data.XML.Types.Pulse — C-extractable XML node tag codec via Pulse + Custard.

A single-byte tag selects the XML node kind — [XN_Element]
(0x00), [XN_Text] (0x01), [XN_Comment] (0x02), [XN_PI] (0x03) — written/read
through a [Pulse.Lib.Array.array].

Each encode/decode `fn` carries a byte-level post-condition tied to the pure
spec [tag_of]/[tag_to_type] (both `noextract`; the tag->type mapping is the
single source of truth shared with the pure [Data.XML] layer).

Written for F* v2026.09.20 (Custard `--custard_backend C`).  Zero admits.

@header Data.XML.Types.Pulse

@section Types
- [xml_node] — XN_Element, XN_Text, XN_Comment, XN_PI
- [opt_xml_node] — C-friendly decode result (no [option])

@section Tag bytes
- [tag_element] / [tag_text] / [tag_comment] / [tag_pi] — the four tag byte
  constants

@section Specs
- [tag_of] — xml_node -> tag byte
- [tag_to_type] — tag byte -> xml_node option

@section Encode
- [encode] — write [tag_of t] at [off], returns 1ul

@section Decode
- [decode] — read the tag at [off] into [opt_xml_node]

@section Roundtrip lemmas
- [lemma_roundtrip] — pure [tag_of] o [tag_to_type] roundtrip
- [lemma_pulse_roundtrip] — buffer-level encode->decode roundtrip
- [lemma_pulse_encode_decode_match] — master roundtrip across every tag
*)
module Data.XML.Types.Pulse
#lang-pulse

open Pulse
open Pulse.Lib.Reference
module A = Pulse.Lib.Array
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Seq = FStar.Seq

open FStar.Seq

(* ── Types (alphabetical) ──────────────────────────────────────────── *)

(** [xml_node] — the XML node kinds the tag byte selects. *)
type xml_node =
  | XN_Element
  | XN_Text
  | XN_Comment
  | XN_PI

(** [opt_xml_node] — option wrapper for the decode result (C-friendly, no
    [option]). *)
type opt_xml_node =
  | OXN_None
  | OXN_Some of (xml_node & U32.t)

(* ── Tag bytes — single source of truth (fstar-proofs §33) ─────────── *)

(** [tag_element] — the element tag byte (0x00). *)
let tag_element : U8.t = 0x00uy

(** [tag_text] — the text tag byte (0x01). *)
let tag_text : U8.t = 0x01uy

(** [tag_comment] — the comment tag byte (0x02). *)
let tag_comment : U8.t = 0x02uy

(** [tag_pi] — the processing-instruction tag byte (0x03). *)
let tag_pi : U8.t = 0x03uy

(* ── Pure spec (noextract: not C-representable) ────────────────────── *)

(** [tag_of t] — pure spec: [xml_node] -> tag byte. *)
noextract
let tag_of (t: xml_node) : U8.t =
  match t with
  | XN_Element -> tag_element
  | XN_Text -> tag_text
  | XN_Comment -> tag_comment
  | XN_PI -> tag_pi

(** [tag_to_type b] — pure spec: tag byte -> [xml_node] option.

    Returns [option xml_node] (not [opt_xml_node]) — [tag_to_type] is the
    PURE spec and is never extracted; only [decode] uses the C-friendly
    [opt_xml_node] wrapper. *)
noextract
let tag_to_type (b: U8.t) : option xml_node =
  if U8.eq b tag_element then Some XN_Element
  else if U8.eq b tag_text then Some XN_Text
  else if U8.eq b tag_comment then Some XN_Comment
  else if U8.eq b tag_pi then Some XN_PI
  else None

(* ── Encode ────────────────────────────────────────────────────────── *)

(** [encode t buf off] — encode an XML node tag into [buf] at [off]; returns 1
    (bytes written).

    @param t The XML node kind to write.
    @param buf The destination buffer (must hold at least 1 byte at [off]).
    @param off The write offset.
    @returns The number of bytes written (always [1ul]).
    The byte written equals [tag_of t]. *)
fn encode (t: xml_node) (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 1 <= A.length buf)
    returns w: U32.t
    ensures
      (exists* (s1: Seq.seq U8.t).
        A.pts_to buf s1 **
        pure (U32.v off + 1 <= A.length buf /\
              Seq.length s1 == A.length buf /\
              Seq.index s1 (U32.v off) == tag_of t)) **
      pure (w == 1ul)
{
  let j = US.uint32_to_sizet off;
  A.pts_to_len buf;
  buf.(j) <- tag_of t;
  1ul
}

(* ── Decode ────────────────────────────────────────────────────────── *)

(** [decode buf off] — decode an XML node tag from [buf] at [off].

    @param buf The source buffer (must hold at least 1 byte at [off]).
    @param off The read offset.
    @returns [OXN_Some (t, 1ul)] when the byte is a known tag, else
             [OXN_None]. *)
fn decode (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 1 <= A.length buf)
    returns r: opt_xml_node
    ensures
      A.pts_to buf s0 **
      pure (
        A.length buf == Seq.length s0 /\
        U32.v off + 1 <= A.length buf /\
        (let b = Seq.index s0 (U32.v off) in
         match r, tag_to_type b with
         | OXN_Some (t, n), Some t' -> n == 1ul /\ t == t'
         | OXN_None, None -> True
         | _, _ -> False))
{
  A.pts_to_len buf;
  let j = US.uint32_to_sizet off;
  let tag = buf.(j);
  if U8.eq tag tag_element {
    OXN_Some (XN_Element, 1ul)
  } else if U8.eq tag tag_text {
    OXN_Some (XN_Text, 1ul)
  } else if U8.eq tag tag_comment {
    OXN_Some (XN_Comment, 1ul)
  } else if U8.eq tag tag_pi {
    OXN_Some (XN_PI, 1ul)
  } else {
    OXN_None
  }
}

(* ── Roundtrip lemmas (alphabetical) ───────────────────────────────── *)

(** [lemma_roundtrip t] — pure roundtrip: encoding then decoding returns the
    original value. *)
let lemma_roundtrip (t: xml_node) : Lemma (tag_to_type (tag_of t) == Some t) =
  match t with
  | XN_Element -> ()
  | XN_Text -> ()
  | XN_Comment -> ()
  | XN_PI -> ()

(** [lemma_pulse_roundtrip t buf off] — encode then decode a tag roundtrips.

    @param t The XML node kind to roundtrip.
    @param buf The buffer.
    @param off The offset.
    Proves [decode buf off] after [encode t buf off] returns
    [OXN_Some (t, 1ul)]. *)
fn lemma_pulse_roundtrip (t: xml_node) (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 1 <= A.length buf)
    returns res: (U32.t & opt_xml_node)
    ensures
      (exists* (s1: Seq.seq U8.t).
        A.pts_to buf s1) **
      pure (fst res == 1ul /\ snd res == OXN_Some (t, 1ul))
{
  let n = encode t buf off;
  let r = decode buf off;
  lemma_roundtrip t;
  (n, r)
}

(** [lemma_pulse_encode_decode_match t buf off] — master roundtrip across every
    tag.

    @param t The XML node kind.
    @param buf The buffer.
    @param off The offset.
    Proves [decode] o [encode] returns [OXN_Some (t, 1ul)] for all four tags. *)
fn lemma_pulse_encode_decode_match (t: xml_node) (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 1 <= A.length buf)
    returns res: (U32.t & opt_xml_node)
    ensures
      (exists* (s1: Seq.seq U8.t).
        A.pts_to buf s1) **
      pure (fst res == 1ul /\ snd res == OXN_Some (t, 1ul))
{
  match t {
    XN_Element -> { lemma_pulse_roundtrip XN_Element buf off }
    XN_Text -> { lemma_pulse_roundtrip XN_Text buf off }
    XN_Comment -> { lemma_pulse_roundtrip XN_Comment buf off }
    XN_PI -> { lemma_pulse_roundtrip XN_PI buf off }
  }
}
