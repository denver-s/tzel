(** * Spec.Hashes — abstract hash families and protocol constants

    Source: whitepaper §"Cryptographic primitives" and spec.md hash
    catalogue.  The protocol uses domain-separated BLAKE2s at three
    arities; the spec layer abstracts each use-site as a distinct
    opaque function parameterized in each module's Section.

    Hash arities used by the protocol:

    - [H2 : Felt -> Felt -> Felt]
        Commitment Merkle tree internal nodes (personalized with
        [mrklSP__]), nullifier derivation ([nulfSP__]), sighash fold
        ([sighSP__]), nk_spend key derivation ([nkspSP__]).

    - [H3 : Felt -> Felt -> Felt -> Felt]
        WOTS+ chain step (unpersonalized BLAKE2s over 96 bytes;
        domain separation via ADRS packed into the second argument).

    - [H4 : Felt -> Felt -> Felt -> Felt -> Felt]
        L-tree and auth-tree internal node hashing (unpersonalized
        BLAKE2s over 128 bytes: [pub_seed || ADRS || left || right]).

    Cryptographic properties (collision resistance, preimage resistance,
    PRF) will be stated as axioms here when soundness proofs in
    [Spec.Xmss] or [Spec.Transfer] need them.  Currently unused —
    the structural properties proved so far hold for any functions of
    the right arity.
*)

From Common Require Import Felt.

(** ** WOTS+ protocol parameters (whitepaper / RFC 8391)

    Base [w = 4]: each WOTS digit is in [{0, 1, 2, 3}].
    Chain length [w − 1 = 3]: each chain applies the hash [w − 1]
    times from secret key to public key endpoint.
    Total chains: 128 message digits + 5 checksum digits = 133. *)

Definition wots_w : nat := 4.
Definition wots_chain_len : nat := wots_w - 1.
Definition wots_chains : nat := 133.

(** ** Tree depth parameters

    Auth tree depth: 16 (2^16 = 65 536 one-time keys per address).
    Commitment tree depth: 48 (2^48 leaves). *)

Definition auth_depth : nat := 16.
Definition tree_depth : nat := 48.
