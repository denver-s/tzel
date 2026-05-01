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

    Proofs land in follow-up commits. Targets:
    - [iter_succ]: extending an [n]-step chain by one more step
      equals one [step] applied to the [n]-step output.
    - [iter_compose]: an [(n + m)]-step chain equals an [m]-step
      chain run on the [n]-step output.
    - The refinement theorem in [Impl.Wots] proves the executable
      [Impl.xmss_chain_step] equals [Spec.step] under the realized
      hash and ADRS, closing the spec ↔ extractable connection.
*)

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

End ChainStep.
