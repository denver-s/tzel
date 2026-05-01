(** * Spec.Hashes

    Abstract hash families and the cryptographic axioms about them
    that the spec-layer soundness theorems will use.

    Source: derive from the protocol-level documents (whitepaper /
    spec.md), not from the Cairo. The whitepaper specifies
    domain-separated BLAKE2s for each use site (sighash, commit,
    nullifier, owner_tag, merkle, nk_spend, nk_tag, plus the WOTS+
    chain hash); the spec layer abstracts this as a family of
    distinct opaque functions, with collision-resistance and
    preimage-resistance axiomatized.

    Status: stub.
*)

From Common Require Import Felt.
