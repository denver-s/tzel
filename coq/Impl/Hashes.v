(** * Impl.Hashes

    Implementation-side hash declarations, mirroring
    [cairo/src/blake_hash.cairo].

    [Hash3] is the generic 3-input hash ([blake_hash::hash3_generic]
    in Cairo) used by [xmss_chain_step] to mix [pub_seed], the
    ADRS-encoded chain index, and the running chain element. Domain
    separation comes from the ADRS encoding, not a separate IV.

    The [Spec] layer's [Spec.Wots.step] is parameterized over an
    abstract hash; the [Impl] layer here declares the concrete
    parameter and the extraction realizes it bit-equivalently to the
    Cairo. The refinement theorem in [Impl.Wots] connects the two:
    the executable [Impl.xmss_chain_step] equals
    [Spec.step Hash3 pack_adrs_chain] when applied to the same
    arguments.
*)

From Common Require Import Felt.

Parameter Hash3 : Felt -> Felt -> Felt -> Felt.
