(** * Tzel.Common

    Shared types and notations for the tzel circuit model. The Cairo
    source has no single file dedicated to these — the Felt type and
    basic record shapes are implicit across the cairo crate. We pull
    them together here as a small foundation for the other modules.
*)

(** Field element. The Cairo circuit operates over the Stark prime
    field with elements of bit-width 251; we keep [Felt] opaque here
    because the soundness theorems we plan to prove are independent of
    the field's specific structure as long as it has decidable
    equality. The extraction realizes [Felt] as OCaml [bytes] (32-byte
    sequences), matching [tzel/protocol/felt.ml]. *)
Parameter Felt : Type.
