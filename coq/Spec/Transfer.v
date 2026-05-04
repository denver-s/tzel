(** * Spec.Transfer — transfer circuit safety predicate

    Source: whitepaper transfer section + spec.md. Transfer consumes
    [N] (1 ≤ N ≤ 7) input notes and produces three output notes
    (recipient, change, producer-fee).

    We define the circuit relation [TransferRelation] and the
    safety predicate [Phi_transfer], then state the soundness
    target:

      forall pub wit, TransferRelation pub wit -> Phi_transfer pub

    If this theorem does not close, the Cairo circuit is missing an
    assertion.  Each conjunct of [Phi_transfer] that fails to prove
    identifies a specific gap.

    For now we define the key types and the safety predicate.
    The full proof requires wiring through XMSS, Merkle, and
    sighash results from the other Spec modules.
*)

From Stdlib Require Import List Arith.
From Common Require Import Felt.
From Spec Require Import Hashes.

(** ** Public and witness types for the transfer circuit *)

(** Public outputs visible on-chain. *)
Record TransferPublic := mkTransferPublic {
  tp_auth_domain : Felt;
  tp_root : Felt;              (** commitment tree root *)
  tp_nullifiers : list Felt;   (** one per consumed input *)
  tp_fee : nat;                (** transaction fee *)
  tp_cm_out : list Felt;       (** output commitments (3) *)
}.

(** Per-input witness (private data for each consumed note). *)
Record InputWitness := mkInputWitness {
  iw_nk_spend : Felt;          (** nullifier spend key *)
  iw_auth_root : Felt;         (** XMSS auth tree root *)
  iw_auth_pub_seed : Felt;     (** XMSS public seed *)
  iw_auth_idx : nat;           (** leaf index in auth tree *)
  iw_d_j : Felt;               (** address diversifier *)
  iw_value : nat;              (** note value *)
  iw_rseed : Felt;             (** commitment randomness seed *)
  iw_cm_siblings : list Felt;  (** Merkle path for commitment *)
  iw_cm_path_idx : nat;        (** leaf position in commitment tree *)
  iw_wots_sig : list Felt;     (** WOTS+ signature (133 elements) *)
  iw_auth_siblings : list Felt; (** XMSS auth path *)
}.

(** ** Safety predicate [Phi_transfer]

    Each conjunct corresponds to a security property that the
    circuit MUST enforce.  If any conjunct is missing from the
    Cairo, the soundness proof will fail at that point. *)

Section PhiTransfer.

  Variable H_sighash : Felt -> Felt -> Felt.
  Variable H_merkle : Felt -> Felt -> Felt.
  Variable H_commit : Felt -> Felt -> Felt -> Felt -> Felt.
  Variable H_nf : Felt -> Felt -> Felt.

  (** Value conservation: total input value equals total output
      value plus fee.  Missing this lets the prover create value
      from nothing. *)
  Definition value_conservation
      (input_values : list nat) (output_values : list nat)
      (fee : nat) : Prop :=
    list_sum input_values = list_sum output_values + fee.

  (** Nullifier correctness: each nullifier is correctly derived
      from the commitment and position.  Missing this lets the
      prover reuse a nullifier (double-spend). *)
  Definition nullifier_correct
      (nf : Felt) (nk_spend cm : Felt) (pos : Felt) : Prop :=
    nf = nullifier H_nf nk_spend cm pos.

  (** Sighash completeness: the sighash covers all public outputs.
      Missing any field lets the prover change that field after
      signing (transaction malleability). *)
  Definition sighash_complete
      (sighash : Felt) (tag auth_domain root : Felt)
      (nullifiers : list Felt) (fee_felt : Felt)
      (cm_out : list Felt) : Prop :=
    sighash = sighash_fold H_sighash
                (sighash_fold H_sighash
                   (sighash_fold H_sighash tag
                     (auth_domain :: root :: nullifiers))
                   (fee_felt :: nil))
                cm_out.

  (** Producer fee must be positive.  Missing this lets the
      prover skip paying the producer. *)
  Definition producer_fee_positive (cm_out : list Felt)
      (output_values : list nat) : Prop :=
    (* The third output value is the producer fee *)
    nth 2 output_values 0 > 0.

End PhiTransfer.

(** ** Summary of Phi_transfer conjuncts

    A complete [Phi_transfer pub] asserts ALL of:
    1. Value conservation (sum_in = sum_out + fee)
    2. Input authenticity (each commitment Merkle-included under root)
    3. Nullifier correctness (each nf derived from real spent note)
    4. Spend authorization (valid XMSS signature on sighash)
    5. Sighash completeness (signature covers every public output)
    6. Output well-formedness (commitments correctly constructed)
    7. Producer fee positive (v_3 > 0)
    8. Type-tag separation (tag = 0x01 for transfer)

    Items 2 and 4 use [Spec.Merkle] and [Spec.Xmss] respectively.
    Items 1, 3, 5–8 are defined above or are structural checks.

    The proof [TransferRelation pub wit -> Phi_transfer pub] is the
    headline result: if the Cairo circuit accepts (all its asserts
    pass), then all safety properties hold.  Each missing Cairo
    assert causes the corresponding conjunct to fail. *)
