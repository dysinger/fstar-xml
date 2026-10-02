(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)

(**
Data.XML.Pulse — C-extractable XML token tag codec via Pulse + Custard.

A single-byte tag selects the XML token kind — [XT_ElementStart] (0x00),
[XT_ElementEnd] (0x01), [XT_AttrKey] (0x02), [XT_AttrValue] (0x03),
[XT_Text] (0x04), [XT_Comment] (0x05), [XT_PI] (0x06), [XT_CDATA] (0x07) —
written/read through a [Pulse.Lib.Array.array].

Each encode/decode `fn` carries a byte-level post-condition tied to the pure
spec [tag_of]/[tag_to_type] (both `noextract`; the tag->type mapping is the
single source of truth shared with the pure [Data.XML] layer).

Written for F* v2026.09.20 (Custard `--custard_backend C`).  Zero admits.

@header Data.XML.Pulse

@section Types
- [xml_token] — XT_ElementStart, XT_ElementEnd, XT_AttrKey, XT_AttrValue,
  XT_Text, XT_Comment, XT_PI, XT_CDATA
- [opt_xml_token] — C-friendly decode result (no [option])

@section Tag bytes
- [tag_element_start] / [tag_element_end] / [tag_attr_key] / [tag_attr_value] /
  [tag_text] / [tag_comment] / [tag_pi] / [tag_cdata] — the eight tag byte
  constants

@section Specs
- [tag_of] — xml_token -> tag byte
- [tag_to_type] — tag byte -> xml_token option

@section Encode
- [encode] — write [tag_of t] at [off], returns 1ul

@section Decode
- [decode] — read the tag at [off] into [opt_xml_token]

@section Roundtrip lemmas
- [lemma_roundtrip] — pure [tag_of] o [tag_to_type] roundtrip
- [lemma_pulse_roundtrip] — buffer-level encode->decode roundtrip
- [lemma_pulse_encode_decode_match] — master roundtrip across every tag
*)
module Data.XML.Pulse
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

(** [xml_token] — the XML token kinds the tag byte selects. *)
type xml_token =
  | XT_ElementStart
  | XT_ElementEnd
  | XT_AttrKey
  | XT_AttrValue
  | XT_Text
  | XT_Comment
  | XT_PI
  | XT_CDATA

(** [opt_xml_token] — option wrapper for the decode result (C-friendly, no
    [option]). *)
type opt_xml_token =
  | OXT_None
  | OXT_Some of (xml_token & U32.t)

(* ── Tag bytes — single source of truth (fstar-proofs §33) ─────────── *)

(** [tag_element_start] — the element-start tag byte (0x00). *)
let tag_element_start : U8.t = 0x00uy

(** [tag_element_end] — the element-end tag byte (0x01). *)
let tag_element_end : U8.t = 0x01uy

(** [tag_attr_key] — the attribute-key tag byte (0x02). *)
let tag_attr_key : U8.t = 0x02uy

(** [tag_attr_value] — the attribute-value tag byte (0x03). *)
let tag_attr_value : U8.t = 0x03uy

(** [tag_text] — the text tag byte (0x04). *)
let tag_text : U8.t = 0x04uy

(** [tag_comment] — the comment tag byte (0x05). *)
let tag_comment : U8.t = 0x05uy

(** [tag_pi] — the processing-instruction tag byte (0x06). *)
let tag_pi : U8.t = 0x06uy

(** [tag_cdata] — the CDATA tag byte (0x07). *)
let tag_cdata : U8.t = 0x07uy

(* ── Pure spec (noextract: not C-representable) ────────────────────── *)

(** [tag_of t] — pure spec: [xml_token] -> tag byte. *)
noextract
let tag_of (t: xml_token) : U8.t =
  match t with
  | XT_ElementStart -> tag_element_start
  | XT_ElementEnd -> tag_element_end
  | XT_AttrKey -> tag_attr_key
  | XT_AttrValue -> tag_attr_value
  | XT_Text -> tag_text
  | XT_Comment -> tag_comment
  | XT_PI -> tag_pi
  | XT_CDATA -> tag_cdata

(** [tag_to_type b] — pure spec: tag byte -> [xml_token] option.

    Returns [option xml_token] (not [opt_xml_token]) — [tag_to_type] is the
    PURE spec and is never extracted; only [decode] uses the C-friendly
    [opt_xml_token] wrapper. *)
noextract
let tag_to_type (b: U8.t) : option xml_token =
  if U8.eq b tag_element_start then Some XT_ElementStart
  else if U8.eq b tag_element_end then Some XT_ElementEnd
  else if U8.eq b tag_attr_key then Some XT_AttrKey
  else if U8.eq b tag_attr_value then Some XT_AttrValue
  else if U8.eq b tag_text then Some XT_Text
  else if U8.eq b tag_comment then Some XT_Comment
  else if U8.eq b tag_pi then Some XT_PI
  else if U8.eq b tag_cdata then Some XT_CDATA
  else None

(* ── Encode ────────────────────────────────────────────────────────── *)

(** [encode t buf off] — encode an XML token tag into [buf] at [off]; returns 1
    (bytes written).

    @param t The XML token kind to write.
    @param buf The destination buffer (must hold at least 1 byte at [off]).
    @param off The write offset.
    @returns The number of bytes written (always [1ul]).
    The byte written equals [tag_of t]. *)
fn encode (t: xml_token) (buf: A.array U8.t) (off: U32.t)
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

(** [decode buf off] — decode an XML token tag from [buf] at [off].

    @param buf The source buffer (must hold at least 1 byte at [off]).
    @param off The read offset.
    @returns [OXT_Some (t, 1ul)] when the byte is a known tag, else
             [OXT_None]. *)
fn decode (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 1 <= A.length buf)
    returns r: opt_xml_token
    ensures
      A.pts_to buf s0 **
      pure (
        A.length buf == Seq.length s0 /\
        U32.v off + 1 <= A.length buf /\
        (let b = Seq.index s0 (U32.v off) in
         match r, tag_to_type b with
         | OXT_Some (t, n), Some t' -> n == 1ul /\ t == t'
         | OXT_None, None -> True
         | _, _ -> False))
{
  A.pts_to_len buf;
  let j = US.uint32_to_sizet off;
  let tag = buf.(j);
  if U8.eq tag tag_element_start {
    OXT_Some (XT_ElementStart, 1ul)
  } else if U8.eq tag tag_element_end {
    OXT_Some (XT_ElementEnd, 1ul)
  } else if U8.eq tag tag_attr_key {
    OXT_Some (XT_AttrKey, 1ul)
  } else if U8.eq tag tag_attr_value {
    OXT_Some (XT_AttrValue, 1ul)
  } else if U8.eq tag tag_text {
    OXT_Some (XT_Text, 1ul)
  } else if U8.eq tag tag_comment {
    OXT_Some (XT_Comment, 1ul)
  } else if U8.eq tag tag_pi {
    OXT_Some (XT_PI, 1ul)
  } else if U8.eq tag tag_cdata {
    OXT_Some (XT_CDATA, 1ul)
  } else {
    OXT_None
  }
}

(* ── Roundtrip lemmas (alphabetical) ───────────────────────────────── *)

(** [lemma_roundtrip t] — pure roundtrip: encoding then decoding returns the
    original value. *)
let lemma_roundtrip (t: xml_token) : Lemma (tag_to_type (tag_of t) == Some t) =
  match t with
  | XT_ElementStart -> ()
  | XT_ElementEnd -> ()
  | XT_AttrKey -> ()
  | XT_AttrValue -> ()
  | XT_Text -> ()
  | XT_Comment -> ()
  | XT_PI -> ()
  | XT_CDATA -> ()

(** [lemma_pulse_roundtrip t buf off] — encode then decode a tag roundtrips.

    @param t The XML token kind to roundtrip.
    @param buf The buffer.
    @param off The offset.
    Proves [decode buf off] after [encode t buf off] returns
    [OXT_Some (t, 1ul)]. *)
fn lemma_pulse_roundtrip (t: xml_token) (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 1 <= A.length buf)
    returns res: (U32.t & opt_xml_token)
    ensures
      (exists* (s1: Seq.seq U8.t).
        A.pts_to buf s1) **
      pure (fst res == 1ul /\ snd res == OXT_Some (t, 1ul))
{
  let n = encode t buf off;
  let r = decode buf off;
  lemma_roundtrip t;
  (n, r)
}

(** [lemma_pulse_encode_decode_match t buf off] — master roundtrip across every
    tag.

    @param t The XML token kind.
    @param buf The buffer.
    @param off The offset.
    Proves [decode] o [encode] returns [OXT_Some (t, 1ul)] for all eight tags. *)
fn lemma_pulse_encode_decode_match (t: xml_token) (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 1 <= A.length buf)
    returns res: (U32.t & opt_xml_token)
    ensures
      (exists* (s1: Seq.seq U8.t).
        A.pts_to buf s1) **
      pure (fst res == 1ul /\ snd res == OXT_Some (t, 1ul))
{
  match t {
    XT_ElementStart -> { lemma_pulse_roundtrip XT_ElementStart buf off }
    XT_ElementEnd -> { lemma_pulse_roundtrip XT_ElementEnd buf off }
    XT_AttrKey -> { lemma_pulse_roundtrip XT_AttrKey buf off }
    XT_AttrValue -> { lemma_pulse_roundtrip XT_AttrValue buf off }
    XT_Text -> { lemma_pulse_roundtrip XT_Text buf off }
    XT_Comment -> { lemma_pulse_roundtrip XT_Comment buf off }
    XT_PI -> { lemma_pulse_roundtrip XT_PI buf off }
    XT_CDATA -> { lemma_pulse_roundtrip XT_CDATA buf off }
  }
}
