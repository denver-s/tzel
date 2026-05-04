(** * Spec.Shield — shield circuit safety predicate

    Source: [cairo/src/shield.cairo::verify] (6 assertions).

    Shield deposits funds from L1 into the private pool.  The
    circuit:
    - Verifies the signer controls the pubkey_hash (via XMSS sig)
    - Checks the recipient commitment is well-formed
    - Checks the producer-fee commitment is well-formed
    - Ensures the producer fee is positive

    There is NO Merkle inclusion check (nothing is consumed) and
    NO value conservation (the deposited amount comes from L1,
    which the kernel checks separately).

    The sighash uses tag 0x03 to prevent cross-circuit replay
    with transfer (0x01) or unshield (0x02).
*)

From Stdlib Require Import List.
From Common Require Import Felt.
From Spec Require Import Hashes.
From Spec Require Import Transfer.

Section PhiShield.

  Variable H_sighash : Felt -> Felt -> Felt.
  Variable H_commit : Felt -> Felt -> Felt -> Felt -> Felt.
  Variable H_owner : Felt -> Felt -> Felt -> Felt.
  Variable H_rcm : Felt -> Felt.

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
                       (auth_domain :: auth_root :: nil))
                    (auth_pub_seed :: blind :: nil).

  (** 2. Recipient commitment well-formed.
      Cairo: [assert(hash::commit(d_j, v_note, rcm, otag) == cm_new)].
      Missing this allows a malformed commitment that doesn't bind
      the recipient or value. *)
  Definition phi_recipient_commitment
      (cm_new d_j v_felt rcm auth_root auth_pub_seed nk_tag : Felt) : Prop :=
    let otag := H_owner auth_root auth_pub_seed nk_tag in
    let rcm_val := H_rcm rcm in
    cm_new = H_commit d_j v_felt rcm_val otag.

  (** 3. Producer commitment well-formed.
      Cairo: [assert(hash::commit(...) == cm_producer)]. *)
  Definition phi_producer_commitment
      (cm_producer producer_d_j producer_fee_felt producer_rcm
       producer_auth_root producer_auth_pub_seed
       producer_nk_tag : Felt) : Prop :=
    let otag := H_owner producer_auth_root producer_auth_pub_seed
                        producer_nk_tag in
    let rcm_val := H_rcm producer_rcm in
    cm_producer = H_commit producer_d_j producer_fee_felt rcm_val otag.

  (** 4. Producer fee positive.
      Cairo: [assert(producer_fee > 0_u64, 'shield: producer fee zero')]. *)
  Definition phi_shield_producer_fee (producer_fee : nat) : Prop :=
    producer_fee > 0.

  (** 5. Sighash completeness.
      Cairo: sighash = fold(0x03, auth_domain, pubkey_hash, v_note,
      fee, producer_fee, cm_new, cm_producer, memo, producer_memo).
      Missing any field allows the signer to change that field after
      signing. *)
  Definition phi_shield_sighash
      (sighash tag_felt auth_domain pubkey_hash
       v_note_felt fee_felt producer_fee_felt
       cm_new cm_producer memo producer_memo : Felt) : Prop :=
    sighash = sighash_fold H_sighash
                (sighash_fold H_sighash tag_felt
                   (auth_domain :: pubkey_hash :: nil))
                (v_note_felt :: fee_felt :: producer_fee_felt
                  :: cm_new :: cm_producer
                  :: memo :: producer_memo :: nil).

End PhiShield.
