# fstar-xml — Agent Guide & Handoff

`Data.XML` — verified XML 1.0 codec library, extracted from the xeno
monorepo, built on `Data.Codec` and `Data.Text.Codec`.  F* source is 0-admit.
This file records the completed Pulse port so the next session resumes cleanly.

## ⛔ MANDATES (binding — read before doing anything)

1. **NEVER run `fstar.exe`, `nix build`, or `make` in the foreground.**  They
   can hang forever.  **Always** run them **detached** and poll the log:

   ```bash
   cd /Users/user/_/fstar-xml
   rm -f /tmp/xml-build.log
   nohup nix build .#checked --print-out-paths --no-link > /tmp/xml-build.log 2>&1 &
   # … poll: tail /tmp/xml-build.log ; ps -p $!
   ```

   A stuck process (0% CPU `stopped`, or 100% CPU spin) is a hang — kill it,
   diagnose, don't wait.  Per-step budgets: fstar verify ≤ 10 min, `nix build`
   ≤ 15 min (but the F\* bootstrap itself takes ~20 min *only on first build*;
   it is now cached).

2. **The F\* overlay in `flake.nix` MUST stay byte-identical to
   `fstar-codec`/`fstar-basen`/`fstar-text`'s.**  Any comment/whitespace change
   to the `buildPhase`/`installPhase` strings changes the derivation hash and
   forces a full F\* bootstrap.  Do NOT touch those strings.

## ✅ Current state — Pulse port DONE, 4/4 targets GREEN (this session)

The KaRaMeL→Custard port is complete and verified 0-admit.  The old
`src/Data.XML.Low` / `src/Data.XML.Types.Low` (KaRaMeL Low\*:
`FStar.HyperStack.ST`, `LowStar.Buffer`, `Stack`) were **deleted** (Low\*
stdlib removed in `v2026.09.20`), replaced by `src/Data.XML.Pulse.fst` and
`src/Data.XML.Types.Pulse.fst` (`#lang-pulse`).

### Build matrix (verified this session, F* `v2026.09.20+lsp`)

| Target | Status | Output |
|---|---|---|
| `checked` | ✅ GREEN 0-admit | 13 modules verified (8 src + 5 test) |
| `native` (C) | ✅ GREEN | `Custard.c`/`Custard.h`/`xml.h`, `libxml.{dylib,a}` (C11, no karamel) |
| `ocaml` | ✅ GREEN | findlib `xml-ocaml` |
| `fsharp` (.NET) | ✅ GREEN | `Custard.dll` (.NET 10) |

Target names: `default = native`, `checked`, `ocaml`, `native`, `fsharp`.

### The OCaml cross-repo fix (this session)

`Data.XML`'s pure modules `open Data.Codec` AND `open Data.Text.Codec.*`, so
the OCaml-extracted `.ml` files reference the *bare* top-level modules
`Data_Codec_Types`/`Data_Codec`/`Data_Text_Codec_*`.  The `codec-ocaml` /
`text-ocaml` findlib packages **wrap** their modules into `Codec.*`/`Text.*`
namespaces, so the bare names are unbound.

**Fix (landed):** the `default.nix` `ocaml-src` derivation now extracts BOTH
dependencies' pure specs **locally** via `--codegen OCaml` — codec
(`Data.Codec.Types` + `Data.Codec`) and text (`Data.Text.Codec.Chars`/`Codec`/
`Delims`/`Zero`/`UTF8`/`UTF8String`) — compiles them into the `xml-ocaml` dune
library alongside xml's own modules, and drops the findlib dependencies.  No
`Custard` collision: only codec/text *pure* specs are extracted, never their
Pulse leaves.

### The two-Pulse-leaf extraction fix (this session — IMPORTANT)

XML has **TWO** Pulse leaves (`Data.XML.Pulse` token tags + `Data.XML.Types.Pulse`
node tags), unlike codec/basen/text which each have ONE.  Custard emits a
single `Custard.c`/`Custard.h` per invocation, so two separate `--codegen
Custard` invocations **silently overwrite** — the first module's functions
vanish.  The fix: a SINGLE Custard invocation roots BOTH modules via four
`--custard_entry` flags (`Data.XML.Pulse.encode`/`.decode` +
`Data.XML.Types.Pulse.encode`/`.decode`) on one entry file
(`src/Data.XML.Pulse.fst`); the other module resolves from the `.checked`
cache.  All three backends (native/ocaml/fsharp) use this single-invocation
shape.

### Roll-forward fixes (landed, 0-admit preserved)

- `src/Data.XML.Token.fst`: `Prims.op_Multiply a 16` → `a * 16` (the
  `op_Multiply` primitive was deleted in v2026.09.20; `*` is natively
  multiplication in `Prims`).
- All pure modules: removed `--split_queries always` from `#push-options`
  (option deleted; F* now emits one SMT query per obligation).

### fstar-text input is a `path:` (NOT yet `github:`)

`fstar-text` is **not yet published** to GitHub (located at
`/Users/user/_/fstar-text`, no `origin` remote), so `flake.nix` wires it via
`fstar-text.url = "path:/Users/user/_/fstar-text"`.  Once `dysinger/fstar-text`
is pushed, flip to `github:dysinger/fstar-text` and re-lock.  `fstar-codec`
(`github:dysinger/fstar-codec`) IS already published.

## Architecture (post-port)

```
Data.XML.Types          — pure XML 1.0 AST + char-level decl predicates
Data.XML.Token          — leaf codecs: entities, char refs, names, whitespace
Data.XML.Codec.Wrapped  — comment, CDATA, PI content codecs
Data.XML.Codec.Prolog   — doctype, XML decl, misc, ExternalID trees
Data.XML.Codec          — name/attribute/text/element/document codecs
Data.XML                — top-level re-export
Data.XML.Pulse          — C-extractable token tag codec (Custard)
Data.XML.Types.Pulse    — C-extractable AST node tag codec (Custard)
```

Both Pulse leaves are trivial single-byte tag codecs (mirroring fstar-text's
`Data.Text.Codec.Pulse`): a 1-byte tag selects a token/node kind, `encode`/
`decode` (`A.array U8.t`, `fn`), plus `lemma_roundtrip` (pure),
`lemma_pulse_roundtrip`, `lemma_pulse_encode_decode_match`.  `Data.XML.Pulse`
carries 8 token tags (XT_ElementStart … XT_CDATA); `Data.XML.Types.Pulse`
carries 4 node tags (XN_Element/Text/Comment/PI).  No varint, no multi-byte
arithmetic.

## The codec + text dependencies

`fstar-xml` consumes `Data.Codec` from the **published** `dysinger/fstar-codec`
repo and `Data.Text.Codec.*` from **local** `fstar-text` (flake inputs pinned
in `flake.lock`).  `codec-src`/`text-src` (the flake input trees) provide the
`.fst` sources for `--include`; `codec-checked`/`text-checked`
(`fstar-codec.packages.<system>.checked` / `fstar-text.packages.<system>.checked`)
seed the `.checked` cache.

## Build commands

```bash
nix build .#checked   # F* verification gate (0-admit)
nix build .#native    # C11 shared/static lib (default)
nix build .#ocaml     # OCaml findlib package
nix build .#fsharp    # .NET library
nix develop && make check   # dev loop (no nix)
```

## Reference

- Canonical references: `../fstar-codec` (the codec, incl. its
  `Data.Codec.Pulse`), `../fstar-text` (the text codec, incl. its
  `Data.Text.Codec.Pulse` and the downstream-dependency wiring), and
  `../fstar-basen` (the same downstream-dependency shape, `Data.BaseN.Pulse`).
- The F\* skill: `~/.pi/agent/skills/fstar/fstar-2026.09.20/SKILL.md`
  (Custard, Pulse idiom, `U8.v`/`U32.v` → `Int.Cast`, the dead-Low\* delta).
