(** * Spec.Shield — abstract shield-circuit safety predicate

    Source: whitepaper shield section + spec.md. Shield drains a
    deposit pool (keyed by [pubkey_hash]) and produces two private
    notes (recipient, producer-fee).

    Soundness target:

      forall pub wit, ShieldRelation pub wit -> Phi_shield pub

    where [Phi_shield pub] enumerates:
      - [pubkey_hash] commits to the recipient's auth tree
      - In-circuit WOTS+ signature covers every public output
      - Drained amount equals [v_note + fee + producer_fee]
      - Output commitments well-formed

    Status: stub.
*)

From Common Require Import Felt.
