(** * Spec.Transfer — transfer circuit safety predicate

    Source: [cairo/src/transfer.cairo::verify] (19 assertions).

    Safety predicate [Phi_transfer]: the conjunction of properties
    that MUST hold when the circuit accepts.  Each conjunct maps to
    one or more Cairo [assert] statements.  If a conjunct fails to
    prove from the circuit relation, the corresponding assertion is
    missing from the Cairo — a real bug.

    The predicate is parameterized over abstract hash functions so
    soundness proofs compose with the hash-level theorems in
    [Spec.Hashes], [Spec.Merkle], and [Spec.Xmss].
*)

From Stdlib Require Import List Arith.
From Common Require Import Felt.
From Spec Require Import Hashes.

(** ** Type tag: prevents cross-circuit replay *)
(** Transfer = 0x01, Unshield = 0x02, Shield = 0x03, Pubkey = 0x04.
    The sighash starts with the tag, so a transfer signature cannot
    be replayed as a shield (different first hash input). *)
Definition tag_transfer : nat := 1.
Definition tag_unshield : nat := 2.
Definition tag_shield : nat := 3.

(** ** Safety predicate components *)

Section PhiTransfer.

  (** Hash families (abstract, realized at Impl layer). *)
  Variable H_sighash : Felt -> Felt -> Felt.
  Variable H_commit : Felt -> Felt -> Felt -> Felt -> Felt.
  Variable H_nf : Felt -> Felt -> Felt.
  Variable H_owner : Felt -> Felt -> Felt -> Felt.
  Variable H_rcm : Felt -> Felt.
  Variable H_nktag : Felt -> Felt.

  (** ** Phi_transfer conjuncts

      Each corresponds to a security property.  The name in brackets
      is the Cairo assertion that enforces it. *)

  (** 1. Value conservation: sum of inputs = sum of outputs + fee.
      Cairo: [assert(sum_in == sum_out, 'transfer: balance mismatch')].
      Missing this allows value creation from nothing. *)
  Definition phi_value_conservation
      (input_values : list nat) (v1 v2 v3 fee : nat) : Prop :=
    list_sum input_values = v1 + v2 + v3 + fee.

  (** 2. Nullifier correctness (per input): each published nullifier
      is correctly derived from the commitment and leaf position.
      Cairo: [assert(nf == *nf_list.at(i), 'transfer: bad nf')].
      Missing this allows nullifier reuse (double-spend). *)
  Definition phi_nullifier_correct
      (nf nk_spend cm pos : Felt) : Prop :=
    nf = nullifier H_nf nk_spend cm pos.

  (** 3. Sighash completeness: the sighash covers ALL public outputs.
      Cairo: sighash = fold(0x01, auth_domain, root, nf_0..nf_{n-1},
      fee, cm_1, cm_2, cm_3, memo_1, memo_2, memo_3).
      Missing any field allows that field to be changed after signing
      (transaction malleability). *)
  Definition phi_sighash_complete
      (sighash tag_felt auth_domain root : Felt)
      (nullifiers : list Felt) (fee_felt : Felt)
      (cm1 cm2 cm3 memo1 memo2 memo3 : Felt) : Prop :=
    sighash = sighash_fold H_sighash
                (sighash_fold H_sighash tag_felt
                   (auth_domain :: root :: nullifiers))
                (fee_felt :: cm1 :: cm2 :: cm3
                  :: memo1 :: memo2 :: memo3 :: nil).

  (** 4. Output commitment well-formedness: each output commitment
      is correctly constructed from its components.
      Cairo: [assert(hash::commit(...) == cm_k, 'transfer: bad cm_k')].
      Missing this allows a malformed commitment that doesn't bind
      the recipient or value. *)
  Definition phi_output_wellformed
      (cm d_j rcm owner_tag : Felt) (v : Felt) : Prop :=
    cm = H_commit d_j v rcm owner_tag.

  (** 5. Producer fee positive.
      Cairo: [assert(v_3 > 0_u64, 'transfer prod fee')].
      Missing this lets the prover skip paying the producer. *)
  Definition phi_producer_fee_positive (v3 : nat) : Prop :=
    v3 > 0.

  (** 6. Input count in range.
      Cairo: [assert(n >= 1)] and [assert(n <= MAX_INPUTS)].
      MAX_INPUTS = 7.  Structural, not directly security-critical,
      but prevents degenerate edge cases. *)
  Definition phi_input_count (n : nat) : Prop :=
    1 <= n /\ n <= 7.

End PhiTransfer.
