(** * Common.Felt

    Shared field element type. Used by both the [Spec] and [Impl]
    layers — kept in [Common] so the refinement statement
    [Impl.foo = Spec.foo] can mention the same type on both sides. *)

(** Field element over the StarkPrime (251-bit). Treated opaquely for
    soundness reasoning — the proofs we plan don't need the field's
    structure beyond decidable equality. The [Impl] extraction
    realizes [Felt] as OCaml [bytes] (32-byte little-endian),
    matching [tzel/protocol/felt.ml]. *)
Parameter Felt : Type.
