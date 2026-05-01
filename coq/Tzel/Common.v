(** * Tzel.Common

    Shared types and notations for the tzel circuit model. The Cairo
    source has no single file dedicated to these — the Felt type, ADRS
    encoding, and basic record shapes are implicit across the cairo
    crate. We pull them together here as a small foundation for the
    other modules.

    Status: stub. Will be filled in alongside the first concrete proof
    target (currently planned: WOTS+ chain step in [Tzel.Wots]).
*)

(** Field element. The Cairo circuit operates over the Stark prime field
    with elements of bit-width 251; we keep [Felt] opaque here because
    the soundness theorems we plan to prove are independent of the
    field's specific structure as long as it has decidable equality.
    Tightening to [Z] modulo the Stark prime is a future refinement. *)
Parameter Felt : Type.
Parameter felt_eq_dec : forall x y : Felt, {x = y} + {x <> y}.

(** A 32-byte personalization tag identifying a domain-separated hash
    use site (sighash, commit, nullifier, owner_tag, merkle, nk_spend,
    nk_tag, …). Each Cairo file declares its IV constants; we reflect
    them in [Tzel.Hashes] as inhabitants of this type. *)
Parameter PersonalizationTag : Type.
Parameter tag_eq_dec : forall t1 t2 : PersonalizationTag, {t1 = t2} + {t1 <> t2}.
