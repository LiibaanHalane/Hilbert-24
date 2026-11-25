# H24 clock and prover — operation/proof/type invariant layer

25 November 2026. Constructive continuation of the native six-stream, sparse
4×4 Gram-dagger, marked Hilbert 24 proof integral and relational clock. This is
an executable extension, not a replacement for the original prover or an
assertion of the remaining Millennium source requirements.

## Use

Requires Python 3.10+ and SymPy. From this directory:

```sh
python test_invariants.py
```

Use `operations.Claim` to request an exact finite operation, `operations.prove`
to construct its receipt, and `operations.accepts` to replay the *actual* claim.
Use `guarded_prover.guarded_construct` and `guarded_prover.guarded_return` instead
of the original direct CNF constructor/reader. `guarded_history` returns the
original closed history only after the Gram isometry and holonomy seam checks;
`guarded_transport` keeps semantic covariance separate from work covariance.
The adapter imports the retained `self_witness.py` and its existing residual,
paracollatz-polylog chart and independent verifier without changing them.

```python
from operations import Claim, prove, accepts
from invariants import Status
from guarded_prover import guarded_construct

request = Claim('winding', (9, 2, (1,)*18))
proof = prove(request)
assert accepts(request, proof, Status.PROVED)

bad = Claim('uniform_gap_counterexample', ('1/100',))
obstruction = prove(bad)
assert accepts(bad, obstruction, Status.REFUTED)

r = guarded_construct(1, ((1,),(-1,)))
assert r.source_belnap == (0,1)
assert r.operational_clock.status == Status.OPEN
```

The registry has 34 callable operation constructors; the separate H24 adapter
adds original minimum/certificate checking. `OperationProof` retains the
original typed request together with the result. Replay recomputes from the
supplied request, rather than accepting a claimed certificate, a string name
of a theorem, or a numerical match at an unrelated aperture. This is a local
Python proof-object checker, not a cryptographic trust system or a formal
kernel. Use exact integers, rationals and Gaussian-rational matrices, not
untrusted expression strings or floating point approximations.

`PROVED` and `REFUTED` refer to the named instance/claimed packet, not to a
refutation of a universal implication if its premises fail. `OPEN` means no
licensed conclusion. Failed authentication of a CNF proof produces neither
source evidence rail. For example, a failed closure seam refutes that proposed
history, not all possible stationary histories. The JSON receipts include
scope, evidence and the two Belnap evidence bits.

## Executable theorem and obstruction register

| Operation | Mathematical content and proof |
|---|---|
| `persistent_mode` | In a positive Gram space, with A†=-A and D=-B†B, if (A+D)x=iωx and x≠0, real pairing yields 0=-‖Bx‖². Thus Bx=Dx=0 and Ax=iωx. A purely dissipative generator cannot supply a nonzero oscillation frequency under these hypotheses. |
| `stationary_observation` | If [K,ρ]=0, cyclicity of trace gives tr(ρ U†OU)=tr(ρO) for U=e^(-itK). A fixed one-event observable cannot tick in such a stationary state. Two-event correlations need not be constant. |
| `symmetric_input` | UT=TU and Ux=x imply UTx=Tx. A symmetry-preserving operation cannot create a noninvariant state from an invariant input. Does not forbid relational correlations. |
| `history` | Prefix products of the U_j generate the history; its last seam is exactly (U_(N-1)…U_0-I)x. A zero-residual history with prescribed nonzero initial value exists iff that value is fixed by the holonomy. |
| `covariance` | Check UF-F′U on every basis column of the actual finite matrices. This certifies the whole linear operator; it supplies a concrete column residual if false. |
| `locality` | Strict radius-r locality requires every matrix entry outside |i-j|≤r to vanish. The 3-site skew-adjoint Cayley update has entry U_31=2h²/(1+2h²), so unitarity does not imply a strict one-site cone. |
| `vacuum_flux` | For unit n, u-n·(E×B)=(‖B-n×E‖²+(n·E)²)/2≥0. Equality is the radiative sector; the retained Maxwell proof provides the continuum domain-of-dependence argument under its smoothness hypotheses. |
| `classical_energy_floor` | A nonzero classical field scaled by 2^-k has positive energy u/4^k. No universal strictly positive minimum exists without a signal constraint. |
| `winding` | In a local N-cycle lift, |sum ε_j|≤L implies L≥N|w|. The constant-sign route attains this H24 minimum. |
| `winding_alias`, `finite_observation_clock_alias` | Uniform root-of-unity phase samples identify w and w+N. Wrapped clock position identifies j and j+N. Preserve the lifted mark. |
| `gap_claim`, `uniform_gap_counterexample` | For identity holonomy the unit-weight cycle Laplacian has eigenvalues 4sin²(πk/N). The gap for N=3^d is at most 40/9^d. For any proposed positive rational floor, choose d so that this bound is smaller: an explicit obstruction to a uniform positive floor in this family, despite its short resolvent. |
| `finite_clock_ccr` | tr([Q,P])=0 while tr(iI)=i dim; no finite positive-dimensional exact canonical commutator. |
| `finite_perfect_clock` | N mutually orthogonal nonzero vectors require Hilbert dimension at least N; the coordinate basis attains the dimension bound. This is about perfect orthogonal readout, not all clock models. |
| `two_level_orthogonal` | Overlap 1-p+pz is zero only for p=1/2,z=-1 when |z|=1. For a fixed positive gap and the Schrödinger law, the first orthogonalization attains E T=πħ/2. Not a proof of every quantum speed-limit theorem. |
| `scale_identification` | Independent positive rescalings of length and the additive response preserve the uncalibrated laws and change speed by their ratio. Thus a dimensional c needs a physical calibration. |
| `dyadic_zero_claim` | 0 and 2^k have the same mod-2^k observation and different inverse-limit values. Finite zero cannot certify global zero. |
| `dyadic_gram_claim` | In a finite dyadic residue ring, x=2^ceil(k/2) is nonzero but x²=0 for k≥2. Never substitute real positive Gram reasoning for a finite-ring zero test. |
| `six_frame_integral_haar` | C3 Haar division by 3 is integral. Full S3 averaging in the native representation has coefficient b=1/2 and is not integral. Retain the rational measure domain or undivided sum. |
| `projector_involution` | P²=P and P²=I imply P=I. Do not confuse a ground filter with its ground reflection. |
| `empty_ground_from_reflection` | -I is self-adjoint and self-inverse in the original positive Gram space, with no nonzero fixed vector. Algebraic symmetry is not a witness existence certificate. |
| `posterior` | Finite Bayes conditioning needs a positive normalizer. Zero weight cannot manufacture evidence. |
| `independent_evidence_claim` | (x,x) and (x,not x) have identical uniform marginals but different intersections, so dependence must be retained. |
| `moment_sufficiency_claim` | The fixed q=2/3 histograms (8,12,186,0,279,0,27) and (0,72,0,305,0,135,0) agree in the first three partition moments but have different ground support. Preserve the marked integral, not just these moments. |
| `residual_expansion` | For the connected equality chain C_k, fixed x-first pinning yields 2^k distinct normalized futures: their linear y coefficients differ by ±2. The explicitly enumerated residual DAG is not polynomial in original input size; no lower bound against other contraction algorithms follows. |
| `check_trace` | Every explicit admitted live transition must pay charge plus remaining reserve from preceding reserve. Telescoping bounds total declared work. Check the specified terminal. This does not authenticate a claim that the declared transition table models actual host bit work. |
| `boundary_charge` | w′-w=φ(target)-φ(source) on each edge telescopes; all closed charges agree and endpoint-constrained minima transport. Semantic covariance alone is not enough. |
| `haar_owner_integral` | Each unique owner with depth k, charge c, has mass 2^-k; integrate (c/μ(V))1_V to get c. Repeated references are separate charged actions. Haar averaging is not a division of acquired work. |
| `clock_no_hit` | Every all-zero finite first-hit prefix has both never-hit and later-hit extensions. No finite silence implies global refutation absent a separately proved deadline. |
| `bool_diagonal` | A total naming map for all Boolean-valued functions would name g(x)=not ev(x,x); evaluation at its own name forces b=not b. No unrestricted Boolean diagonal fixed-point oracle. |
| `no_work_from_identity` | Two unit-cost bit flips compose to identity but cost two; a certified contraction must pay for its own acquisition and readback. |
| `claim_universal_clock` | OPEN until the actual original uniform coverage theorem and paid implementation are supplied. No finite regression suite establishes P=NP. |
| `physical_external` | OPEN until the external theorem and exact original physical model binding have been authenticated. Not a placeholder proof. |

## Source and mathematical scope

The retained files implement the original H24 residual grammar, all-ties ground
filter, native chart, clock history, Maxwell cone, covariance and marked proof
balls. Their source hashes are listed in `SOURCE_SHA256.txt`. The `retained`
Python programs were independently run in this extension; logs are in
`replay_logs/`. The original source code copies have not been modified. The
clock's JSON result is regenerated by its original script.

The operational-clock theorem in `Torser_H24_Complete_Bridge_Text.txt` supplies
the rank/reserve argument. Its actual-step condition is retained, not inferred
from the size of a proof term. A full source theorem binds each step to a fixed
implementation and each terminal to the original problem. The finite example
here checks its supplied finite transition system only. The explicit residual
counterexample is tested using the original constructor, not a new search.

The finite positive-metric mode theorem is motivated by Ogami–Tajima,
*Open Quantum Time Crystals without External Thermodynamic Resources*,
https://arxiv.org/abs/2611.09540v2 (24 November 2026), whose no-go theorem is
under time-independent Lindblad dynamics, time-translation covariance and
detailed balance. Its full thermodynamic-limit stationary-state statement is
not re-proved by a finite Gram eigenmode test. The proof of the finite square
factor lemma above is independent of that external result. The paper's full
physical conclusion is retained as an explicit OPEN binding requirement.
The winding constructions correspond to the marked finite models motivated by
https://arxiv.org/abs/2608.27650, not a proof of photonic-device performance.

The new executable tests operate on exact finite packets. The mathematical
proofs in this register use explicit inverse maps, finite sums, positive
pairings, finite algebra, and constructive recurrences. They invoke neither
choice nor general excluded middle; positivity is stated for the appropriate
real/complex interpretation, not for arbitrary dyadic coefficients. The
continuum Stokes result keeps its existing calculus assumptions. There is no
claim of a new universal no-go theorem covering every conceivable physical
clock, or of an exhaustive formalization of all literature no-go results.

`InvariantContracts.lean` is a separate portable candidate for several core
logical, budget and cocycle contracts; no Lean, Hets or Agda executable is
available in this runtime, so no fresh formal kernel receipt is claimed. The
Python execution results are separate from such receipts.

## Results

The new suite produces `receipts.json` and `CHECKS.txt`; successful checks include
expected refutations and explicit OPEN returns. Six retained component replay
programs passed in the current run. Use the guarded entry points for future
calls; no changes have been made to a remote installed prover or its kernel.
