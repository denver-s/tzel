(** * Spec.Transfer — abstract transfer-circuit safety predicate

    Source: whitepaper transfer section + spec.md. Transfer consumes
    [N] (1 ≤ N ≤ 7) input notes and produces three output notes
    (recipient, change, producer-fee).

    Soundness target — the [Spec]-level statement we prove:

      forall pub wit, TransferRelation pub wit -> Phi_transfer pub

    where [Phi_transfer pub] enumerates:
      - Input authenticity: every input is Merkle-included under [root]
      - Nullifier correctness: derived from real spent notes
      - Spend authorization: valid one-time WOTS+ signature on sighash
      - Sighash completeness: signature covers every public output
      - Value conservation: [sum_in = v_1 + v_2 + v_3 + fee]
      - Output well-formedness
      - Type-tag separation (no shield/transfer/unshield cross-replay)

    Status: stub.
*)

From Common Require Import Felt.
