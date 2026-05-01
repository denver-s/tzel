(** * Spec.Xmss — abstract XMSS verifier

    Source: whitepaper §"Authorization tree and in-circuit
    verification" + RFC 8391. The whitepaper enumerates:

      1. recompute the sighash from the public outputs;
      2. decompose into base-[w] digits;
      3. hash signature chains forward (via [Spec.Wots])
         to recover the per-chain pubkey endpoints;
      4. compress endpoints through the L-tree;
      5. prove membership of the recovered leaf under [auth_root].

    The headline soundness target (proven against this spec):

      XmssVerify msg sig auth_idx auth_path auth_root = true ->
      exists pk, MembersOf auth_root auth_idx (LeafFromPk pk)
              /\ WotsRecover msg sig = pk

    Status: stub.
*)

From Common Require Import Felt.
