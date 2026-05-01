(** * Spec.Merkle — abstract Merkle path verification

    Source: whitepaper notes on the commitment tree (depth-48 in the
    current parameterization) and the auth tree (depth-16); standard
    hash-tree mechanics. The spec abstracts the hash and proves the
    standard membership-implies-recoverable-root property.

    Status: stub.
*)

From Common Require Import Felt.
