(** * Spec.Unshield — abstract unshield-circuit safety predicate

    Source: whitepaper unshield section + spec.md. Unshield consumes
    [N] (1 ≤ N ≤ 7) input notes, emits an L1 outbox transfer of
    [v_pub], optionally creates a private change note, and creates a
    producer-fee note.

    Soundness target:

      forall pub wit, UnshieldRelation pub wit -> Phi_unshield pub

    Mirrors transfer for the input side (Merkle inclusion +
    nullifier + WOTS+ verification per input). Output side: one
    public exit, optional change, one producer fee. Value-balance
    equation [sum_in = v_pub + fee + producer_fee + (v_change?)].

    Status: stub.
*)

From Common Require Import Felt.
