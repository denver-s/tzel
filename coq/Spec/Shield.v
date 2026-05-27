(** * Spec.Shield — shield circuit safety predicate (multiasset)

    Source: [cairo/src/shield.cairo::verify] (pre-multiasset: 6
    assertions).

    Shield deposits funds from L1 into the private pool.  The
    circuit:
    - Verifies the signer controls the pubkey_hash (via XMSS sig).
    - Checks the recipient commitment is well-formed.
    - Checks the producer-fee commitment is well-formed.
    - Ensures the producer fee is positive.

    There is NO Merkle inclusion check (nothing is consumed) and
    NO general value conservation in the rollup — the deposited
    amount comes from L1, which the kernel checks separately.

    The sighash uses tag 0x03 to prevent cross-circuit replay
    with transfer (0x01) or unshield (0x02).

    ** Multiasset note (v1 — single tez bridge).

    Shield's L1 boundary currently exposes only the tez bridge, so
    the deposit is always tez.  The circuit-level commitments,
    however, are asset-tagged — both [cm_new] and [cm_producer] bind
    an explicit asset field through [H_commit].  In v1 we pin both
    to [asset_tez] (the only bridge), but the commitment hash
    structure is already in place for future bridges:

      cm_new      = H_commit(d_j, v_note, asset_new, rcm, otag_new)
      cm_producer = H_commit(d_j', v_fee, asset_tez, rcm', otag')

    For v1, [phi_shield_asset_tez] requires [asset_new = asset_tez].
    A future "shield_asset_A" entry point would relax that constraint
    after deploying an asset-A bridge.

    The producer fee MUST remain tez even after future bridges land,
    by the same liquidity argument as in [Spec.Transfer]
    ([phi_producer_asset_tez]).
*)

From Stdlib Require Import List.
Import ListNotations.
From Common Require Import Felt.
From Spec Require Import Hashes.
From Spec Require Import Transfer.

Section PhiShield.

  Variable H_sighash : Felt -> Felt -> Felt.
  Variable H_commit : Felt -> Felt -> Felt -> Felt -> Felt -> Felt.
  Variable H_owner : Felt -> Felt -> Felt -> Felt.
  Variable H_rcm : Felt -> Felt.

  (** Canonical tez asset tag. *)
  Variable asset_tez : Felt.

  (** 1. Pubkey hash correctness: the pubkey_hash published on L1
      commits to the signer's auth material.
      Cairo: [assert(pkh == pubkey_hash, 'shield: bad pubkey_hash')].
      [pkh = fold(0x04, auth_domain, auth_root, auth_pub_seed, blind)].
      Missing this decouples the L1 deposit address from the circuit
      authorization — anyone could claim the deposit. *)
  Definition phi_pubkey_hash
      (pubkey_hash tag_pkh auth_domain auth_root
       auth_pub_seed blind : Felt) : Prop :=
    pubkey_hash = sighash_fold H_sighash
                    (sighash_fold H_sighash tag_pkh
                       [auth_domain; auth_root])
                    [auth_pub_seed; blind].

  (** 2. Recipient commitment well-formed.

      Cairo (multiasset): [assert(hash::commit(d_j, v_note, asset_new,
      rcm, otag) == cm_new)].

      Missing the asset binding here is the "asset substitution at
      shield" bug — the prover could mint a commitment for an
      arbitrary asset while the L1 deposit is for tez.  In v1 this
      is additionally guarded by [phi_shield_asset_tez] below; the
      hash-level binding is the structural defense. *)
  Definition phi_recipient_commitment
      (cm_new d_j v_felt asset rcm auth_root auth_pub_seed nk_tag
       : Felt) : Prop :=
    let otag := H_owner auth_root auth_pub_seed nk_tag in
    let rcm_val := H_rcm rcm in
    cm_new = H_commit d_j v_felt asset rcm_val otag.

  (** 3. Producer commitment well-formed.
      Cairo: [assert(hash::commit(...) == cm_producer)]. *)
  Definition phi_producer_commitment
      (cm_producer producer_d_j producer_fee_felt producer_asset
       producer_rcm producer_auth_root producer_auth_pub_seed
       producer_nk_tag : Felt) : Prop :=
    let otag := H_owner producer_auth_root producer_auth_pub_seed
                        producer_nk_tag in
    let rcm_val := H_rcm producer_rcm in
    cm_producer = H_commit producer_d_j producer_fee_felt
                           producer_asset rcm_val otag.

  (** 4. Recipient asset = tez (v1 single-bridge constraint).

      With only the tez bridge deployed, the L1 deposit is always
      tez and the produced [cm_new] must carry [asset = tez].
      Remove this conjunct when a non-tez bridge is added; replace
      with a per-bridge "deposit asset matches drained pool"
      constraint. *)
  Definition phi_shield_asset_tez (asset_new : Felt) : Prop :=
    asset_new = asset_tez.

  (** 5. Producer fee asset = tez.

      Permanent constraint (not v1-only).  See [Spec.Transfer]
      [phi_producer_asset_tez] for the liquidity rationale. *)
  Definition phi_shield_producer_asset_tez
      (asset_producer : Felt) : Prop :=
    asset_producer = asset_tez.

  (** 6. Producer fee positive.
      Cairo: [assert(producer_fee > 0_u64, 'shield: producer fee zero')]. *)
  Definition phi_shield_producer_fee (producer_fee : nat) : Prop :=
    producer_fee > 0.

  (** 7. Value conservation against the L1 deposit.

      The L1 ticket carries [v_deposit] mutez of tez.  The circuit's
      private outputs plus the public fee must equal the drained
      amount:

        v_deposit = v_note + v_producer + fee_public

      In v1 every asset involved is tez, so this is a single
      equation.  For future non-tez bridges, the L1 deposit would
      be denominated in asset A and the producer-fee / public-fee
      paths would need a separate tez source (see whitepaper
      §"Multiasset deposits" — TBW). *)
  Definition phi_shield_value_conservation
      (v_deposit v_note v_producer fee : nat) : Prop :=
    v_deposit = v_note + v_producer + fee.

  (** 8. Sighash completeness.

      Cairo (multiasset): sighash = fold(0x03, auth_domain,
      pubkey_hash, v_note, fee, producer_fee, asset_new,
      asset_producer, cm_new, cm_producer, memo, producer_memo).

      Unlike transfer, the asset fields ARE in the sighash here
      because shield is the asset's entry point — the asset tag is
      public at L1 anyway (the bridge identifies it).  Binding it
      in the sighash prevents the prover from claiming "I shielded
      asset X" while drafting commitments for asset Y; kernel
      reconciliation against L1 catches this anyway, but the
      circuit-level binding is the structural defense. *)
  Definition phi_shield_sighash
      (sighash tag_felt auth_domain pubkey_hash
       v_note_felt fee_felt producer_fee_felt
       asset_new asset_producer
       cm_new cm_producer memo producer_memo : Felt) : Prop :=
    sighash = sighash_fold H_sighash
                (sighash_fold H_sighash tag_felt
                   [auth_domain; pubkey_hash])
                [v_note_felt; fee_felt; producer_fee_felt;
                 asset_new; asset_producer;
                 cm_new; cm_producer;
                 memo; producer_memo].

End PhiShield.
