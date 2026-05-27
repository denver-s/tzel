(** * Spec.Unshield — unshield circuit safety predicate (multiasset)

    Source: [cairo/src/unshield.cairo::verify] (pre-multiasset:
    16 + 7 assertions).

    Unshield withdraws funds from the private pool to L1.  It
    consumes [N] (1 ≤ N ≤ 7) input notes and produces (multiasset):

    - A public L1 exit of [v_pub] mutez of asset [asset_pub] to
      [recipient].  In v1 [asset_pub = tez] is forced because the
      tez bridge is the only bridge.
    - Two private change-slot notes [cm_change_1], [cm_change_2]
      (mirroring transfer's two change slots), free to hold any
      asset the input balance supports.  Either may be a zero-value
      placeholder.
    - A mandatory producer-fee note [cm_producer] pinned to
      [asset = tez].

    Input side mirrors transfer: per-input Merkle inclusion,
    nullifier derivation, XMSS signature verification, and each
    input carries a private asset tag.

    ** Per-asset balance.  For every asset [α]:

      sum_{i : input_asset_i = α} v_i
        = (output side at α)
        + (if α = tez then v_pub + fee_public else 0)

    where "output side at α" sums the change-slot and producer-fee
    contributions whose asset equals α.

    Sighash uses tag 0x02 to prevent cross-circuit replay.
*)

From Stdlib Require Import List Arith.
Import ListNotations.
From Common Require Import Felt.
From Spec Require Import Hashes.
From Spec Require Import Transfer.

Section PhiUnshield.

  Variable H_sighash : Felt -> Felt -> Felt.
  Variable H_commit : Felt -> Felt -> Felt -> Felt -> Felt -> Felt.
  Variable H_nf : Felt -> Felt -> Felt.
  Variable H_owner : Felt -> Felt -> Felt -> Felt.
  Variable H_rcm : Felt -> Felt.

  (** Canonical tez asset tag. *)
  Variable asset_tez : Felt.

  (** 1. Per-asset value conservation.

      Inputs: parallel lists [(input_assets, input_values)].
      Outputs: parallel lists [(output_assets, output_values)] that
      enumerate the change-slot notes and the producer-fee note
      (three entries total: change_1, change_2, producer).
      Public side: [(v_pub, asset_pub)] for the L1 exit and [fee] for
      the rollup-burned tez fee.

      Cairo (multiasset): per-asset accumulators for tez and the
      witness-supplied "primary non-tez asset"; final equality
      assertion per accumulator.  Implies this semantic predicate. *)
  Definition phi_unshield_value_conservation
      (input_assets : list Felt) (input_values : list nat)
      (output_assets : list Felt) (output_values : list nat)
      (v_pub : nat) (asset_pub : Felt)
      (fee : nat) : Prop :=
    forall a : Felt,
      sum_at a input_assets input_values
      = sum_at a output_assets output_values
        + (if Felt_eq_dec a asset_pub then v_pub else 0)
        + (if Felt_eq_dec a asset_tez then fee else 0).

  (** 2. Nullifier correctness (per input).
      Cairo: [assert(nf == *nf_list.at(i), 'unshield: bad nf')]. *)
  Definition phi_unshield_nullifier := phi_nullifier_correct.

  (** 3. Producer fee positive.
      Cairo: [assert(v_fee > 0_u64, 'unshield prod fee')]. *)
  Definition phi_unshield_fee_positive (v_fee : nat) : Prop :=
    v_fee > 0.

  (** 4. Input count in range.
      Cairo: [assert(n >= 1)] and [assert(n <= MAX_INPUTS)]. *)
  Definition phi_unshield_input_count := phi_input_count.

  (** 5. Public exit asset = tez (v1 single-bridge constraint).

      With only the tez bridge deployed, L1 exits can only deliver
      tez.  Lift this when additional bridges land; the per-bridge
      version would require [asset_pub] to match a bridge-specific
      whitelist. *)
  Definition phi_unshield_exit_asset_tez (asset_pub : Felt) : Prop :=
    asset_pub = asset_tez.

  (** 6. Producer fee asset = tez.  Permanent constraint. *)
  Definition phi_unshield_producer_asset_tez
      (asset_producer : Felt) : Prop :=
    asset_producer = asset_tez.

  (** 7. Output commitment well-formedness.

      Each of [cm_change_1], [cm_change_2], [cm_producer] is
      reconstructed from witness fields including the asset tag
      (same shape as [Spec.Transfer.phi_output_wellformed]). *)
  Definition phi_unshield_output_wellformed
      (cm d_j v asset rcm owner_tag : Felt) : Prop :=
    cm = H_commit d_j v asset rcm owner_tag.

  (** 7b. Input commitment well-formedness (per input).  Same as
      [Spec.Transfer.phi_input_wellformed]; included here for
      symmetry of the Phi assembly.  Binds each input's witness
      [(d_j, v, asset, rcm, otag)] to its [cm], which is then used
      as the leaf in the Merkle inclusion check.  Without this,
      witness values for v / asset are unbound and the per-asset
      balance can be cooked. *)
  Definition phi_unshield_input_wellformed
      (cm d_j v asset rcm owner_tag : Felt) : Prop :=
    cm = H_commit d_j v asset rcm owner_tag.

  (** 8. Sighash completeness.

      Cairo (multiasset): sighash = fold(0x02, auth_domain, root,
      nf_0..nf_{n-1}, v_pub, asset_pub, fee, recipient,
      cm_change_1, cm_change_2, cm_producer,
      memo_change_1, memo_change_2, memo_producer).

      [asset_pub] is included because it is public at L1 (the
      bridge identifies it); change-slot assets are hidden and
      bound only via [cm_*].

      Missing [recipient] would allow redirecting the L1 exit.
      Missing [asset_pub] would allow swapping the exit asset
      after signing (when multi-bridge lands). *)
  Definition phi_unshield_sighash
      (sighash tag_felt auth_domain root : Felt)
      (nullifiers : list Felt)
      (v_pub_felt asset_pub fee_felt recipient
       cm_change_1 cm_change_2 cm_producer
       memo_change_1 memo_change_2 memo_producer : Felt) : Prop :=
    sighash = sighash_fold H_sighash
                (sighash_fold H_sighash tag_felt
                   (auth_domain :: root :: nullifiers))
                [v_pub_felt; asset_pub; fee_felt; recipient;
                 cm_change_1; cm_change_2; cm_producer;
                 memo_change_1; memo_change_2; memo_producer].

  (** 9. Input list well-formedness (parallel asset / value lists). *)
  Definition phi_unshield_input_lists_parallel
      (input_assets : list Felt) (input_values : list nat) : Prop :=
    length input_assets = length input_values.

  (** 10. Output list well-formedness (parallel asset / value lists).
      Unshield has exactly 3 private output slots (change_1,
      change_2, producer), so both lists must have length 3; this
      conjunct enforces parallelism, the count invariant is
      Relation-level. *)
  Definition phi_unshield_output_lists_parallel
      (output_assets : list Felt) (output_values : list nat) : Prop :=
    length output_assets = length output_values.

End PhiUnshield.
