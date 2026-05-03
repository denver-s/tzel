(** * Impl.Extraction

    Coq → OCaml extraction directives.

    Realizes the abstract [Felt] type and the opaque [Hash3] /
    [pack_adrs_chain] parameters with concrete OCaml. For this first
    end-to-end commit on the restructured layout the realizations are
    placeholders — both [Hash3] and [pack_adrs_chain] return a fixed
    zero felt — so the extracted code compiles and runs without
    depending on the OCaml [tzel] library. The placeholder makes
    [xmss_chain_step] degenerate (always zero) but exercises the
    Coq → OCaml extraction pipeline end-to-end.

    The next commit will replace the placeholders with the bit-
    equivalent [Tzel.Hash.hash3] and [Tzel.Wots.pack_adrs] from the
    OCaml protocol port. At that point the extracted [xmss_chain_step]
    will produce the same output as the Cairo [xmss_chain_step] on the
    same input, and the differential driver (also planned for the
    next commit) will start exercising that equivalence.

    Note: extraction writes [tzel_wots.ml] / [tzel_wots.mli] to the
    directory [coqc] runs from when processing this file. With our
    [_CoqProject], that's [coq/Impl/]. The build script in
    [coq/Extracted/] copies the file into place for the OCaml driver.
*)

From Coq Require Extraction.
From Common Require Import Felt.
From Impl Require Import Hashes.
From Impl Require Import Wots.

Extraction Language OCaml.

(** Realize [Felt] as OCaml [bytes] (32-byte buffer), matching
    [tzel/protocol/felt.ml] in the OCaml port. *)
Extract Constant Felt => "bytes".

(** Placeholder hash: returns a fixed zero felt regardless of input.
    Smoke-test only — extraction pipeline exercise. To be replaced
    with [Tzel.Hash.hash3] once the differential driver lands. *)
Extract Constant Hash3 => "(fun _ _ _ -> Bytes.make 32 '\000')".

(** Placeholder ADRS encoder: same idea, fixed output. Replaced
    alongside [Hash3]. *)
Extract Constant pack_adrs_chain =>
  "(fun _ _ _ -> Bytes.make 32 '\000')".

(** Map Coq [nat] to OCaml [int] so indices don't go through
    Peano-encoded linked lists — readable extracted code, fast
    arithmetic. Standard idiom. *)
Extract Inductive nat => "int" [ "0" "Stdlib.succ" ]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extraction "tzel_wots.ml" xmss_chain_step.
