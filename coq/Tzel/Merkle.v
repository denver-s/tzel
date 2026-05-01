(** * Tzel.Merkle

    Mirror of [cairo/src/merkle.cairo].

    The Cairo file implements:
    - Append-only commitment tree of fixed depth ([TREE_DEPTH]).
    - Merkle path verification: given a leaf, a sibling list, and a
      position index, recompute the root and check membership.
    - Auth-tree mirror of the same with [AUTH_DEPTH].

    Soundness target (future work):

      MerklePathVerify leaf siblings idx root = true ->
      exists path, ValidPath leaf siblings idx root path.

    where [ValidPath] is the ground-truth membership relation. The
    interesting wrinkle is the index-bit decomposition: each bit of
    [idx] selects whether the sibling is on the left or the right at
    that level, and a missing-or-mis-ordered bit lets a malicious
    prover put the leaf at the wrong position. The proof has to make
    that explicit.

    Status: stub.
*)

From Tzel Require Import Common.
From Tzel Require Import Hashes.
