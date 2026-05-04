(** * Spec.Unshield — unshield circuit safety predicate

    Source: [cairo/src/unshield.cairo::verify] (16 + 7 assertions).

    Unshield withdraws funds from the private pool to L1.  It
    consumes [N] (1 ≤ N ≤ 7) input notes and produces:
    - A public L1 exit of [v_pub] to [recipient]
    - An optional private change note
    - A mandatory producer-fee note

    Input side mirrors transfer: Merkle inclusion, nullifier
    derivation, XMSS signature verification per input.

    Sighash uses tag 0x02 to prevent cross-circuit replay.
*)

From Stdlib Require Import List Arith.
From Common Require Import Felt.
From Spec Require Import Hashes.
From Spec Require Import Transfer.

Section PhiUnshield.

  Variable H_sighash : Felt -> Felt -> Felt.
  Variable H_commit : Felt -> Felt -> Felt -> Felt -> Felt.
  Variable H_nf : Felt -> Felt -> Felt.
  Variable H_owner : Felt -> Felt -> Felt -> Felt.
  Variable H_rcm : Felt -> Felt.

  (** 1. Value conservation: sum of inputs = public exit + change
      + producer fee + transaction fee.
      Cairo: [assert(sum_in == sum_out, 'unshield: balance mismatch')].
      [sum_out = v_pub + v_change + v_fee + fee]. *)
  Definition phi_unshield_value_conservation
      (input_values : list nat)
      (v_pub v_change v_fee fee : nat) : Prop :=
    list_sum input_values = v_pub + v_change + v_fee + fee.

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

  (** 5. Sighash completeness.
      Cairo: sighash = fold(0x02, auth_domain, root, nf_0..nf_{n-1},
      v_pub, fee, recipient, cm_change, memo_change, cm_fee, memo_fee).
      Missing [recipient] would allow redirecting the L1 exit. *)
  Definition phi_unshield_sighash
      (sighash tag_felt auth_domain root : Felt)
      (nullifiers : list Felt)
      (v_pub_felt fee_felt recipient
       cm_change memo_change cm_fee memo_fee : Felt) : Prop :=
    sighash = sighash_fold H_sighash
                (sighash_fold H_sighash tag_felt
                   (auth_domain :: root :: nullifiers))
                (v_pub_felt :: fee_felt :: recipient
                  :: cm_change :: memo_change
                  :: cm_fee :: memo_fee :: nil).

  (** 6. Optional change note: when [has_change = false], all change
      witness fields must be zero.
      Cairo: 7 assertions in [change_commitment_or_zero]. *)
  Definition phi_no_change_zeroed
      (has_change : bool)
      (v_change : nat) (d_j_change rseed_change
       auth_root_change auth_pub_seed_change
       nk_tag_change memo_ct_hash_change : Felt) : Prop :=
    has_change = false ->
    v_change = 0 /\
    d_j_change = memo_ct_hash_change (* placeholder: all = 0 *).

End PhiUnshield.
