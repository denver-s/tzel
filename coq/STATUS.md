# Rocq model — current status

Snapshot of where the formalization stands as of branch `coq-model`,
commit pending. Pause here; main-branch PR review takes priority.

## Architecture (recommended by team expert)

Three layers, with the spec layer derived from documents (whitepaper
+ spec.md), not the Cairo code:

```
docs/whitepaper.tex + specs/spec.md
            │
            ▼ (transcribe)
        coq/Spec/                ← whitepaper-derived abstract spec
            │
            ▼ (refine + prove refinement)
        coq/Impl/                ← extractable, Cairo-shaped refinement
            │
            ▼ (Coq → OCaml extraction)
        certified OCaml model
            │
            ▼ (PBT / QCheck2 conformance)
        cairo/src/*.cairo        ← actual on-chain implementation
```

Strict requirement: **no `admit` anywhere**. Every theorem closes.

## Done

- **Branch + scaffolding:** `coq-model` branch exists with the
  three-layer directory structure: `coq/Common`, `coq/Spec`,
  `coq/Impl`. `_CoqProject` lists all three with `-Q` mappings.
- **Drift detection:** `coq/MANIFEST.toml` pins SHA-256 of every
  modeled Cairo file; `coq/Drift/check.sh` re-hashes and fails CI
  on divergence. Verified working in CI on the previous scaffolding
  commit.
- **CI:** `.github/workflows/coq.yml` runs the drift check and (now,
  pending the build job's first run on this restructure) builds the
  Rocq theory via opam-installed `rocq-prover`. Same opam-via-
  setup-ocaml pattern as the OCaml unit tests workflow — actions
  pinned to commit SHAs.
- **`Common/Felt.v`:** opaque [Felt] type, shared between Spec and
  Impl so refinement statements can mention the same type on both
  sides.
- **`Spec/Wots.v`:** abstract WOTS+ chain step. Defines `step` (one
  application of `F pub_seed (ADRS k c s) x`) and `iter` (n-step
  iteration, with the step counter incrementing). Parameterized
  over the hash and the address encoding. Whitepaper-derived; does
  *not* look at the Cairo. Definitions only — proofs land next.
- **`Spec/Hashes.v` / `Spec/Merkle.v` / `Spec/Xmss.v` /
  `Spec/Transfer.v` / `Spec/Shield.v` / `Spec/Unshield.v`:** stubs
  with intent docs explaining what each will model.
- **`Impl/Common.v`:** placeholder for impl-side shared declarations.
- **`Impl/Hashes.v`:** declares `Hash3` parameter (concrete, will be
  realized at extraction).
- **`Impl/Wots.v`:** mirrors Cairo `xmss_chain_step` as a one-line
  Coq function. Contains an `pack_adrs_chain` parameter for the
  ADRS encoding. Refinement theorem to `Spec.Wots.step` is intended
  but not written yet.
- **`Impl/{Merkle,Xmss,Transfer,Shield,Unshield}.v`:** stubs with
  intent docs and updated imports (`From Common Require Import
  Felt`, etc.).

## Not done

### Spec-layer proofs (next concrete piece)

In `Spec/Wots.v`, prove:

```
Lemma iter_succ : forall n x p k c s,
  iter (S n) x p k c s = step (iter n x p k c s) p k c (s + n).

Lemma iter_compose : forall n m x p k c s,
  iter (n + m) x p k c s = iter m (iter n x p k c s) p k c (s + n).
```

Both are induction-on-n with `Nat.add_succ_r` / `Nat.add_0_r`
arithmetic. Needs `Require Import Arith.` (or Rocq equivalent).
~30 lines of proof total. Scoping rationale: smallest piece that
lands a real proof in the Spec layer; subsequent properties
(L-tree compression, full XMSS verifier) build on these.

### Impl-side refinement theorems

In `Impl/Wots.v`, after the Spec lemmas are in place:

```
Theorem refines_spec : forall x p k c s,
  xmss_chain_step x p k c s = Spec.Wots.step Hash3 pack_adrs_chain x p k c s.
Proof. reflexivity. Qed.
```

Trivial by `Definition` expansion — but states the connection
explicitly so future Spec-level theorems transfer to Impl.

### Extraction + OCaml driver

Was attempted in the previous coq-model commit (61f5cd5) with a
placeholder hash; the OCaml build step in CI failed and was
removed during this restructure. Reintroduce as:

1. `Impl/Extraction.v` writes extracted .ml/.mli for the
   currently-modeled Impl functions (start with `xmss_chain_step`).
2. `coq/Extracted/` directory with a build script that compiles the
   extracted code + a small driver, linking against the OCaml
   protocol port (`tzel` library) for the realizations of `Hash3`
   and `pack_adrs_chain` — `Tzel.Hash.hash3` and
   `Tzel.Wots.pack_adrs` are bit-equivalent to the Cairo via the
   existing cross-impl interop check.
3. CI step: build extracted driver, smoke-run on a fixed witness.

### Cairo runner for differential check

Add `cairo/src/run_chain_step.cairo` as an executable target in
`Scarb.toml`. Takes 5 felts as input, calls
`xmss_common::xmss_chain_step`, returns the result. Lets the
differential driver call Cairo as a subprocess.

### QCheck2 conformance harness

OCaml driver:
- Generate random `(x, pub_seed, key_idx, chain_idx, step)`
- Run the extracted Coq's `xmss_chain_step` (with OCaml
  protocol-port realizations)
- Run the Cairo `run_chain_step` executable on the same inputs
- Assert outputs byte-equal

Initial budget: ~30 seconds per CI run, scheduled longer runs
nightly. After basic conformance lands, ask for edge-case search;
divergences trigger triage:
- Spec model bug → fix Spec, re-derive Impl refinement
- Cairo bug → fix Cairo
- Generator bug → fix generator

### Beyond chain step

Once the Wots chain-step pattern is end-to-end (Spec proofs +
refinement + extraction + conformance), the same shape repeats for:
- Merkle path verification (`Spec.Merkle` ↔ `Impl.Merkle`)
- L-tree compression (extension of `Spec.Wots`)
- Full XMSS verifier (`Spec.Xmss` ↔ `Impl.Xmss`) — the headline
  module; soundness theorem here is the most subtle and the
  highest-value to mechanically check
- The three top-level circuits: `Spec.Transfer` ↔ `Impl.Transfer`,
  same for shield + unshield. Soundness predicates `Phi_*` enumerate
  the protocol-level safety properties; the Spec proofs force the
  `*Relation pub wit -> Phi pub` chain to close on actual Coq
  assertions, which is the missing-assertion check.

## Open questions / decisions deferred

1. **Whether to formalize XMSS unforgeability or axiomatize it.**
   Light path: state the standard XMSS unforgeability theorem as a
   parameter, leaning on the published Hülsing et al. proofs. Heavy
   path: re-derive in Rocq from PRF/PRE/SM-DSPR axioms. Light is
   the obvious starting point; heavy is a separate research-grade
   undertaking we may never need.

2. **mathcomp dependency.** Not yet pulled in. Will likely want
   `mathcomp-ssreflect` for tactic ergonomics when proofs grow;
   `mathcomp-algebra` if we end up reasoning about the Stark prime
   field algebraically. Adding both is one opam install line; not
   urgent until the proofs feel painful in vanilla Rocq.

3. **LaTeX-aligned spec step.** The expert recommended writing the
   spec in LaTeX first and aligning before going to Rocq for
   non-trivial pieces. Currently we're going straight to Rocq for
   the WOTS+ chain step (small enough to skip LaTeX). For the full
   XMSS verifier and the per-circuit safety predicates, the LaTeX
   step is probably worth it — roughly the same size as the
   whitepaper's existing math sections.

## Resumption checklist

When picking this back up:

1. `git checkout coq-model`
2. Read `coq/STATUS.md` (this file)
3. Re-read `coq/README.md` for the architecture refresher
4. Pick the next concrete piece — currently: prove `iter_succ` and
   `iter_compose` in `Spec/Wots.v`, then add the trivial refinement
   theorem in `Impl/Wots.v`, then reintroduce extraction +
   `coq/Extracted/` driver
5. Run CI on each commit; the build job will catch syntax issues
   that can't be caught locally without an opam Rocq install
