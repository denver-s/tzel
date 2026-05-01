(** * Tzel.Hashes

    Mirror of [cairo/src/blake_hash.cairo].

    The Cairo file declares BLAKE2s-based hash functions parameterized
    by a 32-byte personalization IV per use site (sighash, owner,
    commit, nullifier, merkle, nk_spend, nk_tag, plus the WOTS+ ADRS
    chain hash). Distinct IVs give independent functions for our
    purposes — the same input under different IVs produces unrelated
    outputs.

    What we model here:

    - The hash family as opaque parameters, one per IV-distinguished
      use site.
    - Collision-resistance, preimage-resistance, and PRF properties as
      axioms over those parameters.

    What we do NOT model:

    - The concrete BLAKE2s round function. The Cairo implementation
      computes BLAKE2s; the Coq side abstracts past it. The mapping
      between "what the Cairo computes" and "the abstract H_* in this
      file" is part of the cryptographic boundary — i.e., we lean on
      "BLAKE2s with personalized IVs gives a CR/PRF-ish family" as a
      heuristic at the boundary, not inside the proofs.

    Status: stub. To be filled in alongside the first proof target.
*)

From Tzel Require Import Common.
