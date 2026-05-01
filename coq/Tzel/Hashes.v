(** * Tzel.Hashes

    Mirror of [cairo/src/blake_hash.cairo].

    For now we declare only the hash flavors actually used by the
    pieces of model written so far; more will land as additional
    modules are filled in.

    [Hash3] is the generic 3-input hash ([blake_hash::hash3_generic]
    in Cairo) used by [xmss_chain_step] to mix [pub_seed], the
    ADRS-encoded chain index, and the running chain element. Domain
    separation comes from the ADRS encoding, not from a separate IV.

    The cryptographic abstraction here is intentional. The Coq side
    treats [Hash3] as opaque and adds CR/PRF axioms when the proofs
    need them. Soundness theorems should not depend on the hash being
    a random oracle — relation-level soundness only needs standard-
    model properties. The extraction realizes [Hash3] with a
    bit-equivalent OCaml/Cairo hash so the differential check (in
    [coq/Extracted]) can confirm that the model and the Cairo agree on
    every tested witness.
*)

From Tzel Require Import Common.

Parameter Hash3 : Felt -> Felt -> Felt -> Felt.
