(** * Spec.Transfer — transfer circuit safety predicate (multiasset)

    Source: [cairo/src/transfer.cairo::verify] (pre-multiasset: 19
    assertions).  The multiasset generalization replaces the single
    [v_1 + v_2 + v_3 + fee] balance with a per-asset balance over
    four output slots, and adds asset-tag binding to every output
    commitment.

    Safety predicate [Phi_transfer]: the conjunction of properties
    that MUST hold when the circuit accepts.  Each conjunct maps to
    one or more Cairo [assert] statements (post-multiasset; the
    Cairo migration is tracked separately).

    The predicate is parameterized over abstract hash functions so
    soundness proofs compose with the hash-level theorems in
    [Spec.Hashes], [Spec.Merkle], and [Spec.Xmss].

    ** Multiasset model.  Each note commitment binds a hidden asset
    tag [a : Felt] (with [a = Felt(0)] reserved for tez).  The tag
    is preimaged inside [H_commit] alongside value and randomness,
    so two commitments with the same [(d_j, v, rcm, otag)] but
    different assets are distinguishable to a holder of the witness
    but indistinguishable to an on-chain observer.  All four output
    commitments and every input commitment carry an independent
    asset tag; the circuit constrains them via per-asset balance,
    not by tag equality.

    ** N → 4 output layout.  Inputs: [N] (1 ≤ N ≤ 7) shielded UTXOs,
    each with private asset [a_i] and value [v_i].  Outputs (fixed):

      - [cm_recipient] — primary output to the recipient; asset / value
        chosen by sender.
      - [cm_change_1], [cm_change_2] — two free change slots.  The
        sender allocates them however needed.  Typical patterns:
          • pure-tez transfer: one tez change + one zero-value slot.
          • asset-A + tez-fee transfer: one A change + one tez change.
          • atomic-swap-flavored: change slots can hold any two assets
            for which the inputs supply balance.
      - [cm_producer] — DAL slot publisher's fee note.  Pinned to
        [asset = tez] so the publisher gets liquid revenue
        regardless of the transfer's primary asset.

    ** Fee model.  Public [fee] is denominated in tez (the rollup
    ledger's only unit on L1).  Producer fee is a private shielded
    note paid in tez (see [phi_producer_asset_tez] below).  These
    are the two fees described in whitepaper §"Fees".
*)

From Stdlib Require Import List Arith.
Import ListNotations.
From Common Require Import Felt.
From Spec Require Import Hashes.

(** ** Type tag: prevents cross-circuit replay *)
(** Transfer = 0x01, Unshield = 0x02, Shield = 0x03, Pubkey = 0x04.
    The sighash starts with the tag, so a transfer signature cannot
    be replayed as a shield (different first hash input). *)
Definition tag_transfer : nat := 1.
Definition tag_unshield : nat := 2.
Definition tag_shield : nat := 3.

(** ** Per-asset summation utility

    Sum the values whose asset tag equals [target].  Used by the
    per-asset balance predicate to partition inputs and outputs by
    asset.  Decidable equality on [Felt] is supplied by
    [Common.Felt.Felt_eq_dec].

    [assets] and [values] are taken to be parallel lists of the same
    length.  Extra entries on either side are silently ignored
    (the [combine] semantics). *)

Fixpoint sum_at (target : Felt) (assets : list Felt) (values : list nat)
  : nat :=
  match assets, values with
  | nil, _ | _, nil => 0
  | a :: arest, v :: vrest =>
      (if Felt_eq_dec a target then v else 0) + sum_at target arest vrest
  end.

(** ** Safety predicate components *)

Section PhiTransfer.

  (** Hash families (abstract, realized at Impl layer). *)
  Variable H_sighash : Felt -> Felt -> Felt.
  Variable H_commit : Felt -> Felt -> Felt -> Felt -> Felt -> Felt.
  Variable H_nf : Felt -> Felt -> Felt.
  Variable H_owner : Felt -> Felt -> Felt -> Felt.
  Variable H_rcm : Felt -> Felt.
  Variable H_nktag : Felt -> Felt.

  (** Canonical tez asset tag.  Realized at Impl layer as [Felt(0)]. *)
  Variable asset_tez : Felt.

  (** ** Phi_transfer conjuncts

      Each corresponds to a security property.  The name in brackets
      is the Cairo assertion that enforces it (Cairo migration TBD). *)

  (** 1. Per-asset value conservation.

      For every asset [α], the sum of inputs equals the sum of outputs
      plus the public fee (only when [α = tez]; non-tez public fees
      are not representable, the L1 ledger denominates only in mutez).

      This is the multiasset generalization of the original
      [sum_in = v_1 + v_2 + v_3 + fee].  In Cairo it is implemented
      by a witness-supplied "primary non-tez asset" with separate
      tez and non-tez accumulators; that implementation strategy
      implies this semantic predicate.

      Missing this allows value creation, asset substitution
      (e.g., spending an NFT and minting tez), or fee evasion. *)
  Definition phi_value_conservation
      (input_assets : list Felt) (input_values : list nat)
      (output_assets : list Felt) (output_values : list nat)
      (fee : nat) : Prop :=
    forall a : Felt,
      sum_at a input_assets input_values
      = sum_at a output_assets output_values
        + (if Felt_eq_dec a asset_tez then fee else 0).

  (** 2. Nullifier correctness (per input): each published nullifier
      is correctly derived from the commitment and leaf position.

      The asset is bound through [cm] (which appears inside the
      nullifier's inner hash), so no separate asset-nullifier
      check is needed.

      Cairo: [assert(nf == *nf_list.at(i), 'transfer: bad nf')].
      Missing this allows nullifier reuse (double-spend). *)
  Definition phi_nullifier_correct
      (nf nk_spend cm pos : Felt) : Prop :=
    nf = nullifier H_nf nk_spend cm pos.

  (** 3. Sighash completeness: the sighash covers ALL public outputs.

      Cairo (multiasset): sighash = fold(0x01, auth_domain, root,
      nf_0..nf_{n-1}, fee, cm_recipient, cm_change_1, cm_change_2,
      cm_producer, memo_recipient, memo_change_1, memo_change_2,
      memo_producer).

      The asset tags are NOT in the sighash — they are hidden values
      already bound through the [cm_*] preimages.  Adding them
      explicitly would leak the assets without strengthening the
      binding.

      Missing any field allows that field to be changed after signing
      (transaction malleability). *)
  Definition phi_sighash_complete
      (sighash tag_felt auth_domain root : Felt)
      (nullifiers : list Felt) (fee_felt : Felt)
      (cm_recipient cm_change_1 cm_change_2 cm_producer : Felt)
      (memo_recipient memo_change_1 memo_change_2 memo_producer : Felt)
    : Prop :=
    sighash = sighash_fold H_sighash
                (sighash_fold H_sighash tag_felt
                   (auth_domain :: root :: nullifiers))
                [fee_felt;
                 cm_recipient; cm_change_1; cm_change_2; cm_producer;
                 memo_recipient; memo_change_1; memo_change_2;
                 memo_producer].

  (** 4. Output commitment well-formedness: each output commitment
      is correctly constructed from its components, INCLUDING the
      asset tag.

      Cairo (multiasset): [assert(hash::commit(d_j, v, asset, rcm,
      otag) == cm_k, 'transfer: bad cm_k')] for each output slot.

      Missing the asset field in this check is the "asset substitution"
      bug: a malicious prover could publish a [cm_k] for a different
      asset than the witness claims, breaking the per-asset balance
      check by misrouting accumulator contributions. *)
  Definition phi_output_wellformed
      (cm d_j v asset rcm owner_tag : Felt) : Prop :=
    cm = H_commit d_j v asset rcm owner_tag.

  (** 4b. Input commitment well-formedness: each spent note's
      commitment is correctly reconstructed from witness fields,
      INCLUDING the asset tag.

      Cairo (multiasset): [assert(hash::commit(d_j_i, v_i, asset_i,
      rcm_i, otag_i) == cm_i, 'transfer: bad input cm')] for each
      input, before the Merkle inclusion check uses [cm_i] as the
      leaf.

      Without this, the [cm_i] used in the Merkle path could
      correspond to a real on-chain note while the witness fields
      lie about that note's asset / value, breaking
      [phi_value_conservation] by injecting unbacked balance into an
      arbitrary asset's accumulator.  This is the input-side dual
      of the asset-substitution bug guarded by [phi_output_wellformed]. *)
  Definition phi_input_wellformed
      (cm d_j v asset rcm owner_tag : Felt) : Prop :=
    cm = H_commit d_j v asset rcm owner_tag.

  (** 5. Producer fee asset must be tez.

      The producer-fee note is intended for the DAL slot publisher
      who includes the transaction; it must be in tez so the
      publisher can monetize it regardless of the transfer's primary
      asset.  Without this constraint, a malicious wallet could pay
      the producer an illiquid NFT, effectively starving the
      inclusion market.

      Cairo (multiasset): [assert(asset_producer == ASSET_TEZ,
      'transfer: producer asset')]. *)
  Definition phi_producer_asset_tez (asset_producer : Felt) : Prop :=
    asset_producer = asset_tez.

  (** 6. Producer fee positive.

      Cairo: [assert(v_producer > 0_u64, 'transfer prod fee')].
      Missing this lets the prover skip paying the producer. *)
  Definition phi_producer_fee_positive (v_producer : nat) : Prop :=
    v_producer > 0.

  (** 7. Input count in range.

      Cairo: [assert(n >= 1)] and [assert(n <= MAX_INPUTS)].
      MAX_INPUTS = 7.  Structural, not directly security-critical,
      but prevents degenerate edge cases. *)
  Definition phi_input_count (n : nat) : Prop :=
    1 <= n /\ n <= 7.

  (** 8. Input list well-formedness: [input_assets] and [input_values]
      are parallel lists of the same length.  Structural — required
      so [sum_at] interprets them coherently.  In Cairo this is
      ensured by reading both fields from the same per-input witness
      record.

      Without parallel-length enforcement, [sum_at] silently truncates
      to the shorter list — a prover could pad [input_values] with
      extra entries that contribute to balance without corresponding
      asset tags, or vice versa.  This becomes a value-creation
      vulnerability through the asymmetry. *)
  Definition phi_input_lists_parallel
      (input_assets : list Felt) (input_values : list nat) : Prop :=
    length input_assets = length input_values.

  (** 9. Output list well-formedness: [output_assets] and
      [output_values] are parallel lists of the same length.  The
      transfer circuit has exactly 4 output slots, so both lists must
      have length 4; this conjunct only enforces parallelism.  The
      count = 4 invariant is structural (the Cairo struct has 4
      slots) and is enforced at the Relation-assembly layer. *)
  Definition phi_output_lists_parallel
      (output_assets : list Felt) (output_values : list nat) : Prop :=
    length output_assets = length output_values.

End PhiTransfer.
