(** * Tzel.Wots

    Mirror of the WOTS+ portion of [cairo/src/xmss_common.cairo].

    The Cairo file implements WOTS+ chain verification: starting from a
    signature element, hash forward (W-1 - digit) times under
    ADRS-encoded chain step tags, and check the chain end equals the
    public-key element for that chain. The shared [xmss_common.cairo]
    file also covers the L-tree compression and ADRS encoding; we keep
    those here under [Tzel.Wots] when they pertain to the per-chain
    structure, and split the auth-tree traversal to [Tzel.Xmss].

    Soundness targets:

      wots_chain_sound:
        WotsChain start n_steps adrs = end_value ->
        end_value = iter_hash n_steps (chain_step adrs) start

      wots_verify_sound:
        WotsVerify msg sig pk adrs = true ->
        forall i, sig[i] = chain_start_for(msg_digit[i], pk[i], adrs)

    The first is structural; the second connects the digits derived
    from [msg] to the chain endpoints, which is what makes WOTS+
    one-time-secure: a forger trying to sign a different message would
    need to extend a chain *backwards*, which (by preimage resistance
    of the chain hash, modeled in [Tzel.Hashes]) is infeasible.

    Status: stub.
*)

From Tzel Require Import Common.
From Tzel Require Import Hashes.
