# Native clock and shortest-verifier torser bridge

`Native_Clock_Torser_Proof.md` gives the full construction and algebra proofs.
`Native_Clock_Torser.het` is the portable CASL extension of the included,
unchanged `deps/Native_Shortest_Proof.het`. `SOURCE_MAP.json` records the original
source files and their hashes. `VERIFICATION.json` records the final source hash,
proof methods, exact automated outcomes, and their scope.

The construction retains the actual original input, machine configuration,
local reversible history, output, and natural-number bit clock. The same
operation has the sparse native four-by-four matrix, the six original frames,
and the full Gram dagger. Costed composition adds actual ticks. A presentation
equality is zero-cost only when no program operation executes. The full
`NativeClockUniformTarget` chooses the same original machine and clock constants
before all original inputs; it proves exact return to the source clock sentence
without asserting that this target is inhabited.

## Recorded verification

Hets 0.108.0 parsed and statically analyzed all nine new specifications and
their original imports. EProver and SPASS discharged **33 of 39 selected CASL
goals**, including all selected source-state, run, bit-clock, original-minimum,
and whole-class clock-return goals. The remaining six goals stayed open in
the recorded four-second prover attempts. They have the explicit written
algebra proofs below and in the full proof; their corresponding concrete
algebra is also checked by exact ordered polynomial normalization.

The included checker passed **91 exact identities**, retaining coefficient
word order, with all 36 original frame products and all eight Fredkin/Toffoli
input rows. It uses the unchanged archived free-associative normalization
kernel. This is a separate exact algebra check; it does not change an open
CASL prover status into a recorded Hets proof.

| CASL goal remaining open in the recorded run | Written proof and exact checker support |
|---|---|
| `nt_operator_rho_preserves_ordered_product` | Section 3 expands the 16 entries of the product; `noncommutative_native_product` checks those entries with arbitrary ordered coefficients. |
| `nt_context_work_cocycle_is_native_product` | Section 3 proves the two-by-two block product and the action on every basis vector; `weighted_context_clock_cocycle` checks the full native matrix equation. |
| `nt_source_natural_clock_adds_in_native_block` | Section 3 multiplies the shears and uses the stipulated characteristic-zero natural embedding; `clock_shear_addition` checks the universal coefficient identity. |
| `nt_native_dagger_reverses_composition` | Section 5 proves the identity for arbitrary matrices by associativity, conjugate transpose, and the Gram inverse. `gram_dagger_reverses_ordered_product` checks the general native six-coordinate specialization; both Gram inverse identities are checked separately. |
| `nt_framed_clock_composition_cancels_middle_chart` | Section 4 cancels the two middle inverse frame factors for arbitrary source, middle and target frames and arbitrary matrices. All 36 concrete frame products are checked; the 36 `framed_clock_fusion_*` checks independently cover the native closed-endpoint specializations. |
| `nt_framed_native_operator_returns_exactly` | Section 4 removes the retained source and target frames using their two inverse equations. The finite frame inverse pairs occur in the checked 36-product table. The general matrix identity follows from these inverse equations and associativity. |

For precision, the two general frame proofs are

\[
(F_k B F_h^{-1})(F_h A F_g^{-1})
=F_k B(F_h^{-1}F_h)A F_g^{-1}
=F_k(BA)F_g^{-1}
\]

and

\[
F_h^{-1}(F_h A F_g^{-1})F_g
=(F_h^{-1}F_h)A(F_g^{-1}F_g)=A.
\]

The general dagger proof is

\[
(J^{-1}B^*J)(J^{-1}A^*J)
=J^{-1}B^*(JJ^{-1})A^*J
=J^{-1}(AB)^*J=(AB)^\dagger.
\]

These are valid over the specified associative coefficient algebra; no
commutation of contextual operators is used. The two finite-frame goals
outside the selected prover schedule follow from the literal group table,
its faithful matrix representation, and the same associative multiplication.

## Replay

Run the exact algebra check with Python 3:

```sh
python3 verify_native_algebra.py
```

Run the recorded focused CASL schedule with a working Hets installation and
EProver/SPASS available:

```sh
TORSER_HETS_BIN=/path/to/runtime/bin python3 replay_casl.py
```

`TORSER_HETS_BIN` is a directory containing `hets` and the prover executables.
If it is unset, the script uses the recorded local runtime when available,
otherwise `hets` from `PATH`. The included dependencies allow the files to
travel together. Replaying updates the receipts in `checks/`.

The imported historical parent theorems are reused; this focused run does not
reprove the entire parent library. The local history inverse is an explicit
fixed-machine implementation interface. All-CNF polynomial reserve existence
remains the named source target, with its original quantifiers and actual
execution clock. No such inhabitant is supplied by these transport identities.
