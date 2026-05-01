# Coq model of the tzel circuits

This directory contains a Coq model of the Cairo circuits in
`cairo/src/` and (eventually) machine-checked soundness proofs about
them. The motivating concern is that ZK circuits fail by *omission*:
a missing assertion looks normal under honest-prover testing and only
surfaces when an attacker constructs a malicious witness exploiting
the gap. This kind of bug isn't catchable by negative testing or
fuzzing alone; the only way to be sure every needed assertion is
present is to write down what they're collectively supposed to prove
and check that they prove it.

## Approach

Following the seL4 refinement-by-resemblance pattern:

1. **Write a Coq model that mirrors the Cairo structurally.** Same
   function decomposition, same control flow, same asserts. Each Coq
   module corresponds to a Cairo file (see `MANIFEST.toml`).

2. **Prove protocol-level safety theorems about the model.** For each
   circuit (`shield`, `transfer`, `unshield`) we prove:

   ```
   <Circuit>Relation pub wit  ->  Phi_<circuit> pub
   ```

   where `Phi_<circuit>` is the protocol-level safety predicate
   enumerating what the verifier is *supposed* to enforce: input
   authenticity, nullifier correctness, value conservation, spend
   authorization, sighash completeness, type-tag separation. If the
   asserts in the Cairo aren't sufficient to discharge the proof, the
   proof gets stuck — and we've localized the missing assertion.

3. **Audit refinement-by-inspection.** Because the Coq model and the
   Cairo file have the same structure, a human reviewer can check
   that the assertions in the Cairo correspond line-for-line to the
   assertions in the Coq. Drift between the two is caught by
   `Drift/check.sh`.

## What's modeled vs not

The hash functions are opaque parameters in `Tzel/Hashes.v` with
collision-resistance / preimage-resistance / PRF axioms. We do **not**
model them as random oracles — relation soundness only needs the
standard-model properties, and pulling in ROM would be a heavier
abstraction than the proofs require.

`xmss_common.cairo` is split into `Tzel/Wots.v` (chain step + L-tree)
and `Tzel/Xmss.v` (auth-tree traversal) for modularity, hence the one
manifest entry mapping one Cairo file to two Coq mirrors.

`cairo/src/lib.cairo` and the `cairo/src/run_*.cairo` thin executable
wrappers are not modeled — `lib.cairo` only re-exports modules, and
the `run_*` wrappers just unpack args and call into the verifier
modules we already mirror.

## Drift detection

`MANIFEST.toml` pins the SHA-256 of each modeled Cairo file. CI runs
`Drift/check.sh` on every push, which fails if any file has drifted.
The hash is a speed bump — its job is to force a maintainer who
edits the Cairo to also re-read and update the Coq mirror, not to
mechanically verify semantic equivalence. False alarms on cosmetic
edits are intentional.

A planned second layer (`Extracted/`) extracts the Coq model to
OCaml and runs a corpus of test vectors through both the Cairo
verifier and the extracted-Coq model, asserting they agree. That
catches semantic drift the file-hash misses (e.g., variable rename
plus manifest bump without re-reading the model).

## Build

Coq 8.18, no external dependencies for the stub stage. Adding
`mathcomp-ssreflect` will land alongside the first real proof.

```
cd coq
coq_makefile -f _CoqProject -o Makefile
make -j2
```

CI: `.github/workflows/coq.yml` runs the drift check + the build.

## Status

Scaffolding only. All `.v` files are stubs with module headers and
intent docs; no axioms or theorems yet. First real target: the
WOTS+ chain step in `Tzel/Wots.v` plus its supporting hash axioms
in `Tzel/Hashes.v`, which is the smallest piece that exercises the
end-to-end "Cairo function ↔ Coq function ↔ proven property" flow.
