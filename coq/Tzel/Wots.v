(** * Tzel.Wots

    Mirror of the WOTS+ portion of [cairo/src/xmss_common.cairo].

    The Cairo file declares:

      pub fn xmss_chain_step(
        x: felt252, pub_seed: felt252,
        key_idx: u32, chain_idx: u32, step: u32,
      ) -> felt252 {
        let adrs = pack_adrs(TAG_XMSS_CHAIN, key_idx, chain_idx, step, 0);
        hash::hash3_generic(pub_seed, adrs, x)
      }

    We mirror it here. The ADRS encoding ([pack_adrs] in Cairo) is
    captured here as the opaque parameter [pack_adrs_chain]: it bakes
    in the [TAG_XMSS_CHAIN] tag and the trailing zero, exposing only
    the three indices the chain step varies over. The full [pack_adrs]
    will land alongside the L-tree and auth-tree mirrors when those
    modules need it.

    [xmss_chain_step] is then a one-liner. The full chain iteration
    ([xmss_chain_iter] / the inner loop of [xmss_recover_pk]) lands
    next.
*)

From Tzel Require Import Common.
From Tzel Require Import Hashes.

(** ADRS encoding of the chain-step address: [pack_adrs(TAG_XMSS_CHAIN,
    key_idx, chain_idx, step, 0)] in Cairo. Opaque here; the
    extraction maps it to [Tzel.Wots.pack_adrs] in the OCaml protocol
    port (which is bit-equivalent to the Cairo [pack_adrs] under the
    cross-impl interop check). *)
Parameter pack_adrs_chain : nat -> nat -> nat -> Felt.

(** One step of WOTS+ chain hashing. Mirrors [xmss_chain_step] in
    [cairo/src/xmss_common.cairo]:

      hash3_generic(pub_seed, pack_adrs(TAG, key_idx, chain_idx, step, 0), x)
*)
Definition xmss_chain_step
  (x pub_seed : Felt) (key_idx chain_idx step : nat) : Felt :=
  Hash3 pub_seed (pack_adrs_chain key_idx chain_idx step) x.
