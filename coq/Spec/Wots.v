(** * Spec.Wots — abstract WOTS+ chain step

    Whitepaper-derived spec for the chain-hashing primitive used in
    the in-circuit XMSS verifier.

    Source: [docs/whitepaper.tex] §"Authorization tree and in-circuit
    verification" plus the cited references RFC 8391 (XMSS), Buchmann
    et al. (XMSS), and Hülsing (WOTS+). The whitepaper deliberately
    stays at the level of the standard scheme — base [w = 4], 133
    chains of length [w − 1] — and the chain math is the standard
    one. We transcribe it here, NOT the Cairo source: the [Impl]
    layer is allowed to look at the Cairo, but [Spec] derives from
    the protocol-level documents only.

    The chain step abstracts over the hash family [F] and the address
    encoding [ADRS]. A chain at position [(key_idx, chain_idx)],
    starting from value [x] under public seed [pub_seed], applies
    [F pub_seed (ADRS key_idx chain_idx step) x] iteratively, with
    [step] running through [start_step ..= start_step + n − 1].
*)

From Coq Require Import Arith.
From Common Require Import Felt.

Section ChainStep.

  (** Abstract 3-input hash. The whitepaper specifies BLAKE2s with a
      personalized IV; we keep it abstract here because the chain
      math doesn't depend on which concrete hash we pick — only on
      the algebraic structure of "a function from three felts to a
      felt." Cryptographic properties (collision resistance,
      preimage resistance, PRF) get axiomatized when soundness
      proofs need them. *)
  Variable F : Felt -> Felt -> Felt -> Felt.

  (** Address encoding. [ADRS key_idx chain_idx step] returns the
      packed address used as the second hash input. The whitepaper
      and RFC 8391 specify the bit layout in detail; the chain math
      is independent of it, so we abstract here. *)
  Variable ADRS : nat -> nat -> nat -> Felt.

  (** One step of the WOTS+ chain at position [step] under address
      [(key_idx, chain_idx)]:

         step (x, pub_seed, key_idx, chain_idx, step_no)
            = F pub_seed (ADRS key_idx chain_idx step_no) x
  *)
  Definition step (x pub_seed : Felt)
                  (key_idx chain_idx step_no : nat) : Felt :=
    F pub_seed (ADRS key_idx chain_idx step_no) x.

  (** [n]-step chain starting from [x] at [start_step], applying
      [step] [n] times with the step number incrementing each
      iteration. *)
  Fixpoint iter (n : nat)
                (x pub_seed : Felt)
                (key_idx chain_idx start_step : nat) : Felt :=
    match n with
    | O => x
    | S k =>
        iter k
             (step x pub_seed key_idx chain_idx start_step)
             pub_seed key_idx chain_idx (S start_step)
    end.

  (** Chain extension: an [n+1]-step chain equals one [step]
      applied to the [n]-step output. The slightly subtle bit is
      the step counter: the appended [step] uses [start_step + n]
      because [iter] has already advanced the counter [n] times. *)
  Lemma iter_succ
        (n : nat) (x pub_seed : Felt)
        (key_idx chain_idx start_step : nat) :
    iter (S n) x pub_seed key_idx chain_idx start_step =
    step (iter n x pub_seed key_idx chain_idx start_step)
         pub_seed key_idx chain_idx (start_step + n).
  Proof.
    revert x start_step.
    induction n as [|k IH]; intros x start_step.
    - simpl. now rewrite Nat.add_0_r.
    - simpl. rewrite IH. simpl. now rewrite Nat.add_succ_r.
  Qed.

  (** Chain concatenation: an [(n + m)]-step chain equals an
      [m]-step chain run on the [n]-step output, with the step
      counter offset by [n]. *)
  Lemma iter_compose
        (n m : nat) (x pub_seed : Felt)
        (key_idx chain_idx start_step : nat) :
    iter (n + m) x pub_seed key_idx chain_idx start_step =
    iter m
         (iter n x pub_seed key_idx chain_idx start_step)
         pub_seed key_idx chain_idx (start_step + n).
  Proof.
    revert x start_step.
    induction n as [|k IH]; intros x start_step.
    - simpl. now rewrite Nat.add_0_r.
    - simpl. rewrite IH. simpl. now rewrite Nat.add_succ_r.
  Qed.

End ChainStep.
