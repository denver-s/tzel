(** * Spec.Xmss — abstract XMSS signature verification

    Source: whitepaper §"Authorization tree and in-circuit
    verification" + RFC 8391.

    Defines:
    - L-tree compression: pairwise hashing of WOTS+ chain endpoints
      into a single auth-tree leaf (RFC 8391 §4.1.5).
    - WOTS+ endpoint recovery: chaining each signature element
      forward by [chain_len − digit] steps to reconstruct the
      public key chain endpoints.
    - Full XMSS verification predicate combining recovery, L-tree,
      and auth-tree path verification.

    The headline soundness target (not yet proved):

      [xmss_verify] holds ->
      exists pk, the recovered leaf is at position [key_idx]
      in the auth tree with root [auth_root_val],
      and the leaf equals [ltree(pk)].
*)

From Stdlib Require Import List Arith Lia.
From Common Require Import Felt.
From Spec Require Import Hashes.
From Spec Require Import Wots.
From Spec Require Import Merkle.

(* ================================================================ *)
(** ** Two-at-a-time list induction                                  *)
(* ================================================================ *)

(** Standard induction handles one list element per step; L-tree's
    [pair_nodes] consumes two at a time.  This principle provides
    three cases: empty, singleton, and two-or-more. *)
Lemma pair_ind (P : list Felt -> Prop) :
  P nil ->
  (forall x, P (x :: nil)) ->
  (forall x y rest, P rest -> P (x :: y :: rest)) ->
  forall l, P l.
Proof.
  intros H0 H1 H2.
  assert (Hpair : forall l, P l /\ (forall x, P (x :: l))).
  { induction l as [| a tl IH].
    - split; [exact H0 | intro x; exact (H1 x)].
    - destruct IH as [IHl IHcl].
      split; [exact (IHcl a) | intro x; exact (H2 x a tl IHl)].
  }
  intro l; exact (proj1 (Hpair l)).
Qed.

(* ================================================================ *)
(** ** L-tree: pairwise compression of WOTS+ endpoints               *)
(* ================================================================ *)

Section LTree.

  (** Node hash parameterized by level and node index within the
      level.  In the protocol: [H4(pub_seed, ADRS(TAG_XMSS_LTREE,
      key_idx, level, node_idx, 0), left, right)].  The [pub_seed]
      and [key_idx] are baked into the section variable — the L-tree
      definition is parameterized over them. *)
  Variable H_node : nat -> nat -> Felt -> Felt -> Felt.

  (** Compress adjacent pairs at one level.  If the list has odd
      length, the last element carries over unpaired (standard L-tree
      behavior per RFC 8391 §4.1.5). *)
  Fixpoint pair_nodes (nodes : list Felt)
                       (level node_idx : nat) : list Felt :=
    match nodes with
    | a :: b :: rest =>
        H_node level node_idx a b
          :: pair_nodes rest level (S node_idx)
    | _ => nodes
    end.

  (** [pair_nodes] never increases the list length. *)
  Lemma pair_nodes_length_le : forall nodes level nidx,
    length (pair_nodes nodes level nidx) <= length nodes.
  Proof.
    intro nodes. pattern nodes. apply pair_ind; clear nodes.
    - intros level nidx. simpl. apply Nat.le_refl.
    - intros x level nidx. simpl. apply Nat.le_refl.
    - intros x y rest IH level nidx. simpl.
      specialize (IH level (S nidx)). lia.
  Qed.

  (** Iterate [pair_nodes] until a single node remains.
      [fuel] bounds the number of compression levels; setting
      [fuel := length nodes] is always sufficient for non-empty
      input. *)
  Fixpoint ltree_aux (fuel : nat) (nodes : list Felt)
                      (level : nat) : option Felt :=
    match nodes with
    | x :: nil => Some x
    | nil => None
    | _ =>
        match fuel with
        | O => None
        | S f => ltree_aux f (pair_nodes nodes level 0) (S level)
        end
    end.

  (** L-tree compression with automatic fuel. *)
  Definition ltree (nodes : list Felt) : option Felt :=
    ltree_aux (length nodes) nodes 0.

  (** Singleton collapses immediately. *)
  Lemma ltree_singleton (x : Felt) :
    ltree (x :: nil) = Some x.
  Proof. reflexivity. Qed.

  (** Pair compresses to a single hash. *)
  Lemma ltree_pair (a b : Felt) :
    ltree (a :: b :: nil) = Some (H_node 0 0 a b).
  Proof. reflexivity. Qed.

End LTree.

(* ================================================================ *)
(** ** WOTS+ endpoint recovery                                       *)
(* ================================================================ *)

Section WotsRecover.

  Variable F : Felt -> Felt -> Felt -> Felt.
  Variable ADRS_chain : nat -> nat -> nat -> Felt.
  Variable pub_seed : Felt.

  (** Recover one WOTS+ chain endpoint from a signature element.
      [digit] is the base-[w] digit for this chain position;
      the signature element is chained forward [chain_len − digit]
      more steps to reach the public key endpoint. *)
  Definition recover_endpoint (key_idx chain_idx digit : nat)
      (sig_elem : Felt) : Felt :=
    Wots.iter F ADRS_chain (wots_chain_len - digit)
              sig_elem pub_seed key_idx chain_idx digit.

  (** Recover all chain endpoints from a WOTS+ signature.
      [digits] and [sig] must have equal length (= [wots_chains]).
      The chain index starts at [start_chain] and increments. *)
  Fixpoint recover_all (key_idx start_chain : nat)
      (digits : list nat) (sig : list Felt) : list Felt :=
    match digits, sig with
    | d :: ds, s :: ss =>
        recover_endpoint key_idx start_chain d s
          :: recover_all key_idx (S start_chain) ds ss
    | _, _ => nil
    end.

  (** Recovery of a single chain is correct: if the signature
      element was produced by chaining [d] steps from the secret
      key, then recovering chains the remaining steps to give the
      full public key endpoint.  Direct corollary of
      [Wots.recover_correct]. *)
  Theorem recover_endpoint_correct
          (key_idx chain_idx digit : nat) (sk : Felt) :
    digit <= wots_chain_len ->
    recover_endpoint key_idx chain_idx digit
      (Wots.iter F ADRS_chain digit sk pub_seed key_idx chain_idx 0) =
    Wots.iter F ADRS_chain wots_chain_len sk pub_seed key_idx chain_idx 0.
  Proof.
    intro Hle.
    unfold recover_endpoint.
    apply Wots.recover_correct. exact Hle.
  Qed.

End WotsRecover.

(* ================================================================ *)
(** ** Full XMSS verification predicate                              *)
(* ================================================================ *)

Section XmssVerify.

  Variable F : Felt -> Felt -> Felt -> Felt.
  Variable ADRS_chain : nat -> nat -> nat -> Felt.
  Variable H_node : nat -> nat -> Felt -> Felt -> Felt.
  Variable pub_seed : Felt.

  (** XMSS signature verification.  Given per-chain WOTS digits,
      signature elements, and an auth-tree path, the predicate holds
      iff:
      1. WOTS+ recovery yields chain endpoints,
      2. L-tree compression of the endpoints yields a leaf,
      3. the auth-tree path from that leaf reaches [auth_root_val].

      Sighash computation and digit decomposition are handled
      upstream — this definition starts from the digits. *)
  Definition xmss_verify
      (key_idx : nat) (digits : list nat) (sig : list Felt)
      (auth_bits : list bool) (auth_siblings : list Felt)
      (auth_root_val : Felt) : Prop :=
    let endpoints :=
      recover_all F ADRS_chain pub_seed key_idx 0 digits sig in
    match ltree H_node endpoints with
    | Some leaf =>
        Merkle.auth_root H_node auth_bits auth_siblings
                         leaf key_idx 0 = auth_root_val
    | None => False
    end.

End XmssVerify.
