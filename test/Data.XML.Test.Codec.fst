(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)

(**
Data.XML.Test.Codec — unit tests for [Data.XML.Codec.Wrapped].

Re-states the leaf content-codec roundtrips and the RFC-correct
accept/reject lemmas for comment, CDATA, and PI as public test bindings, so
the Integration module mechanically enforces their presence (CODE_GUIDELINES
§Integration test pattern).

@header Data.XML.Test.Codec
*)
module Data.XML.Test.Codec

open Data.XML.Codec
open Data.XML.Codec.Wrapped
open Data.XML.Types
open Data.XML.Token
open Data.Codec
open FStar.Seq

(** Comment content roundtrip re-statement (imports the proven lemma). *)
let test_comment_content_roundtrip (s: string) : Lemma
  (requires comment_content_wfcv s)
  (ensures comment_content_dec (comment_content_enc s)
          == Inr (s, Seq.length (comment_content_enc s)))
  = assert (comment_content_wfcv_prop s);
    assert (comment_content_rest_cond s Seq.empty);
    Seq.append_empty_r (comment_content_enc s);
    comment_content_roundtrip s Seq.empty

(** CDATA content roundtrip re-statement. *)
let test_cdata_content_roundtrip (s: string) : Lemma
  (requires cdata_content_wfcv s)
  (ensures cdata_content_dec (cdata_content_enc s)
          == Inr (s, Seq.length (cdata_content_enc s)))
  = assert (cdata_content_wfcv_prop s);
    assert (cdata_content_rest_cond s Seq.empty);
    Seq.append_empty_r (cdata_content_enc s);
    cdata_content_roundtrip s Seq.empty

(** PI content roundtrip re-statement. *)
let test_pi_content_roundtrip (s: string) : Lemma
  (requires pi_content_wfcv s)
  (ensures pi_content_dec (pi_content_enc s)
          == Inr (s, Seq.length (pi_content_enc s)))
  = assert (pi_content_wfcv_prop s);
    assert (pi_content_rest_cond s Seq.empty);
    Seq.append_empty_r (pi_content_enc s);
    pi_content_roundtrip s Seq.empty

(** [<!--a-b-->] (single interior dash) roundtrips to ["a-b"]. *)
let test_comment_single_dash () : Lemma
  (ensures comment_content_dec (comment_content_enc "a-b")
          == Inr ("a-b", Seq.length (comment_content_enc "a-b")))
  = lemma_comment_single_dash_roundtrip ()

(** [<![CDATA[a]b]]>] (single interior bracket) roundtrips to ["a]b"]. *)
let test_cdata_single_bracket () : Lemma
  (ensures cdata_content_dec (cdata_content_enc "a]b")
          == Inr ("a]b", Seq.length (cdata_content_enc "a]b")))
  = lemma_cdata_single_bracket_roundtrip ()

(** [<?a?b?>] (single interior question) roundtrips to ["a?b"]. *)
let test_pi_single_question () : Lemma
  (ensures pi_content_dec (pi_content_enc "a?b")
          == Inr ("a?b", Seq.length (pi_content_enc "a?b")))
  = lemma_pi_single_question_roundtrip ()

(** The empty attribute value ([name=""]) roundtrips at the transparent
    [greedy] level (the value portion of [xml_attribute_codec]). *)
let test_empty_attr_value_roundtrip () : Lemma
  (ensures greedy_dec_list attr_text_char xml_max_attr_len Seq.empty == Inr ([], 0))
  = lemma_empty_attr_value_roundtrip ()

(** [attr_text_char] rejects a REC [2] control byte ([#x1]) on the attribute
    literal path (finding M1). *)
let test_attr_text_char_reject_control () : Lemma
  (ensures (match attr_text_char.dec (seq_of_list [0x01uy]) with
            | Inl _ -> True | Inr _ -> False))
  = lemma_attr_text_char_reject_control ()

(* ========================================================================
   Soundness / rejection lemmas (list-level [*_ok] predicates, fstar-proofs
   §50/§51/§52).

   The RFC-correct [*_ok] predicates reject ONLY the forbidden subsequence —
   a two-dash run / trailing dash for comments, the close marker for CDATA
   and PI — and ACCEPT a single interior `-`/`]`/`?`.  The soundness property
   is stated at the predicate gate (which normalizes directly), not the full
   [.dec] chain.
   ======================================================================== *)

(** A two-dash comment content is rejected (XML 1.0 §2.5 production [15]). *)
let test_comment_reject_double_dash () : Lemma
  (comment_ok [0x61uy; 0x2Duy; 0x2Duy; 0x62uy] == false)
  = lemma_comment_double_dash_rejected ()

(** A trailing-dash comment content is rejected. *)
let test_comment_reject_trailing_dash () : Lemma
  (comment_ok [0x61uy; 0x2Duy] == false)
  = lemma_comment_trailing_dash_rejected ()

(** A single interior dash comment content is ACCEPTED (the Phase-3.5 fix). *)
let test_comment_accept_single_dash () : Lemma
  (comment_ok [0x61uy; 0x2Duy; 0x62uy] == true)
  = ()

(** A CDATA close marker in content is rejected (production [20]). *)
let test_cdata_reject_close () : Lemma
  (cdata_ok [0x61uy; 0x5Duy; 0x5Duy; 0x3Euy] == false)
  = lemma_cdata_close_rejected ()

(** A single interior bracket CDATA content is ACCEPTED. *)
let test_cdata_accept_single_bracket () : Lemma
  (cdata_ok [0x61uy; 0x5Duy; 0x62uy] == true)
  = ()

(** A PI close marker in content is rejected (production [16]). *)
let test_pi_reject_close () : Lemma
  (pi_ok [0x61uy; 0x3Fuy; 0x3Euy] == false)
  = lemma_pi_close_rejected ()

(** A single interior question PI content is ACCEPTED. *)
let test_pi_accept_single_question () : Lemma
  (pi_ok [0x61uy; 0x3Fuy; 0x62uy] == true)
  = ()

(* ========================================================================
   CODEC-level rejection lemmas (finding M4 / task 2.2). *)

(** A truncated comment content is rejected by the content codec's DECODER. *)
let test_comment_dec_reject_truncated () : Lemma
  (Inl? (comment_content_dec (seq_of_list [0x61uy; 0x2Duy]))) =
  lemma_comment_dec_reject_truncated ()

(** A truncated CDATA content is rejected by the content codec's DECODER. *)
let test_cdata_dec_reject_truncated () : Lemma
  (Inl? (cdata_content_dec (seq_of_list [0x61uy; 0x5Duy; 0x5Duy]))) =
  lemma_cdata_dec_reject_truncated ()

(** A truncated PI content is rejected by the content codec's DECODER. *)
let test_pi_dec_reject_truncated () : Lemma
  (Inl? (pi_content_dec (seq_of_list [0x61uy; 0x3Fuy]))) =
  lemma_pi_dec_reject_truncated ()
