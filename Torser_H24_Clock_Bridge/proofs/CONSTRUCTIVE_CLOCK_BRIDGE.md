# A constructed Hilbert 24 bridge from the torser ledger to the original clock

This construction turns the original frontier accounting law into a **natural-valued ranking of the same actual execution**. It then puts that execution into the declared Hilbert 24 comparison grammar. The required uniform resource content is one precise source judgement, `β⁻(M,K,B)`, retained as a whole proof-bearing object by every torser chart.

The principal source is *Reversible H24: Time, amortization, triple adjoints, and exact decision reads*, 25 November 2026, especially its frontier identity and promised-side prefix theorem. The original `APP` specifications provide the actual-machine ranking and terminal-source interfaces; `PNP_Multiple_Constructions` supplies whole-record, indexed-operation, all-tail, and polynomial-composition interfaces. Exact source locators appear at the end.

## 1. Fix the executable target and its original output type

Fix **one finite deterministic local bit program** `M`. Its source input is the original written CNF `C`, of length `N = |C|`. The complete configuration retains the original source identifier, finite control, tape contents and heads, working stores, the selected torser frame, any history that the implementation keeps, and output registers. A primitive tick touches bounded local information. All parsing, source compilation, address processing, routing, lookup, exact arithmetic, rule selection, proof acquisition, output construction, checking, readback and performed cleanup belong to these ticks.

The marked event is `Ready⁻_M(C,s)`: the actual machine has reached a checked original negative result. A finite certificate interface can be written

\[
\operatorname{Cert}^{-}(C)
 =\sum_{r:\operatorname{RefutationCode}(C)}
   [\operatorname{Check}^{-}(C,r)=\mathsf{true}],
\]

with a fixed sound decoder

\[
\operatorname{decode}^{-}_C:
\operatorname{Cert}^{-}(C)
\longrightarrow
\prod_{a:\{0,1\}^{n(C)}}\operatorname{FailedOriginalLabel}_C(a).
\]

The latter returns an original clause index and its failed-literal evidence for every original assignment. One can use the already admitted source refutation calculus instead of this concrete code interface, provided its verifier and source decoder remain fixed.

An event is an observation boundary. It need not be an absorbing configuration of an injective reversible dynamical system. The observer stops the recorded prefix there, even if the underlying machine continues with a changing history register. This matches the original reversible-clock source.

Let `Pre⁻_M(C)` be the type of finite actual execution prefixes beginning at the raw-input initial configuration and containing no earlier checked event. Its final configuration may be the **first** checked event. A prefix retains its actual transitions and their source identity. Every nonempty primitive transition has charge one. A macro is permitted only together with its complete finite primitive microtrace; its charge is the length of that microtrace.

The desired clock is negative-only. Resource and progress conditions below apply to prefixes for `C` together with a proof `h : UNSAT(C)`. Source soundness of an observed event applies to **all** inputs. No ranking on arbitrary SAT runs is required.

## 2. The exact uniform source judgement β

Write `Poly` for the explicit monomial presentation

\[
P_{c,d}(N)=c(N+1)^d,\qquad c,d\in\mathbb N.
\]

For fixed `M`, two fixed polynomials `K,B`, a natural frontier potential `Φ`, and signed amortized edge charges `a`, define `β⁻(M,K,B)` to be the following **single dependent record**:

```text
record β⁻(M,K,B):
  source_readback:
    every Ready⁻ state returns a Cert⁻ of its unchanged original C

  event_sound:
    for every C and actual prefix π,
    Ready⁻(last π) implies UNSAT(C)

  progress:
    for every C, h:UNSAT(C), and pre-event reachable state,
    either Ready⁻ holds or the fixed M has its next actual primitive tick

  frontier:
    Φ(C,π) : Nat for every promised-side event-stopped finite prefix

  initial_bound:
    for every C,h, Φ(C,empty-prefix) ≤ K(|C|)

  local_balance:
    for every promised-side actual tick π --e--> πe,
    1 + Φ(C,πe) = a(C,e) + Φ(C,π) in the integers

  prefix_budget:
    for every C,h and every event-stopped finite prefix π,
    A(C,π) := sum of its signed a(C,e) satisfies A(C,π) ≤ B(|C|)
```

For a macro of actual length `w`, replace `1` by `w`, and retain its primitive refinement when asserting a primitive-tick deadline. The empty prefix has `A=0`. `Φ` and `A` are proof fields on reachable execution prefixes; they are not uncharged operations that the producer must evaluate. If the producer does evaluate them, those instructions occur in its actual trace.

The full input type has the order

\[
\sum_{M:\mathrm{FiniteProgram}}
\sum_{K,B:\mathrm{Poly}}
\sum_{\Phi}\sum_a
\operatorname{SoundReadback}(M)
\;\times\!
\prod_{C}\prod_{h:\mathrm{UNSAT}(C)}
\operatorname{PrefixLedger}(M,C,h,K,B,\Phi,a).
\tag{β}
\]

All code and all polynomial coefficients/degrees precede `C`. If the programme fixes `M` already, only its `β⁻(M,K,B)` fibre is the target. This is the exact mathematical content to place in Hilbert 24 as a source judgement:

\[
J_{\beta}(M,K,B):
\quad\Gamma_{\mathrm{original}}(M,\operatorname{Check}^{-})
\ \vdash\ \beta^{-}(M,K,B).
\tag{H24 source judgement}
\]

Its proof grammar, admissible source rules and proof grade are retained. A proof of this judgement is a proof of the universal resource statement about the fixed execution, rather than a replacement of runtime by the grade of an instance-level source certificate. In a torser chart the complete record, including `M`, `K`, `B`, all prefix fields and source readback, is the transported coefficient object.

## 3. Construct the ranking field from β

For a promised-side prefix `π`, put

\[
\beta_\pi=B(N)-A(C,\pi),\qquad
\Psi_\pi=\Phi(C,\pi)+\beta_\pi.
\tag{1}
\]

The first difference is formed in the integers. The prefix-budget field proves it is nonnegative, so both `β_π` and `Ψ_π` canonically inhabit `Nat`. There is no rounding or change of charge.

For an actual primitive tick, `A_{πe}=A_π+a_e`. Thus

\[
\begin{aligned}
1+\Psi_{\pi e}
 &=1+\Phi_{\pi e}+B-A_\pi-a_e\\
 &=a_e+\Phi_\pi+B-A_\pi-a_e\\
 &=\Psi_\pi.
\end{aligned}
\tag{2}
\]

For a macro this equation reads `w+Ψ_after=Ψ_before`. In particular, every actual live primitive tick decreases the natural reserve by exactly one, and every positive-cost macro strictly decreases it. Initially

\[
\Psi_0=\Phi_0+B(N)\le K(N)+B(N).
\tag{3}
\]

This explicitly constructs the `Ranking` required by the actual-machine `APP` interface and by the operational Hilbert 24 development. To use an interface whose ranking is a function of a state rather than a prefix, take the reachable-state type to retain the source, its reachability witness and the ghost accumulator `A`. This is proof indexing; it adds no executed instructions. Alternatively supply the same accumulator as an already charged machine register. The two interpretations are not interchanged.

For the original H24 frontier, each amortized charge is a nonnegative calibration slack `σ`. Then `A` is a natural counter, `A+β=B`, and β decreases as slack is consumed. For general signed amortized charges, β may rise after a negative charge; equation (2) proves that the **total** reserve still decreases by the paid work. No monotonicity of β alone is needed.

### A subtraction-free local constructor

The same argument uses natural numbers only when local slacks are nonnegative. The input fields for one edge are

\[
w+\Phi'=\sigma+\Phi,\qquad
A'=A+\sigma,\qquad
A+\beta=B=A'+\beta'.
\]

Cancellation gives `σ+β'=β`, and substitution gives

\[
w+(\Phi'+\beta')=\Phi+\beta.
\]

This is the exact local constructor for the checked `Ranking.decrease` field.

## 4. Construct the execution and its deadline

The proof is a bounded recursive constructor, not an inference from a bound on already completed runs.

Given a promised-side reachable configuration with reserve `r`, inspect its already defined event flag. If the event holds, return its certificate, source equation and empty continuation. Otherwise progress supplies the next primitive tick. Equation (2) supplies a successor reserve `r'` with `1+r'=r`; recurse on `r'` and prepend the actual tick to the returned execution. A live state of reserve zero is impossible, because it would require `1+r' = 0` in the naturals.

Natural recursion therefore returns a finite original execution ending at the first checked event, with

\[
W(C,\pi)+\Psi_\pi=\Psi_0,
\qquad
W(C,\pi)\le K(N)+B(N).
\tag{4}
\]

For `K=k(N+1)^e` and `B=b(N+1)^f`, an explicit common polynomial is

\[
p(N)=(k+b)(N+1)^{\max(e,f)}.
\tag{5}
\]

If the machine-clock interface requires a positive coefficient, use `max(1,k+b)` with the same degree. The exact attained bound remains `K(N)+B(N)`.

Thus one fixed `M` and one fixed pair of clock constants precede every original input. The recursive proof supplies the semantic existence and exact record of the run; `M` itself follows its own transitions and need not compute the analysis potential.

On an arbitrary input, run `M` to this deadline and inspect whether its original checked negative event has occurred. Soundness forbids such an event on SAT. Equation (4) forces it on UNSAT. The complementary bit is therefore the original SAT decision. Clock administration, simulation and output must use the stated machine realization; a separately executed universal simulation adds its proved polynomial overhead through the constructors below.

This theorem requires only negative event production on UNSAT. It does not insert an original-model search into the timed negative monitor. If a full positive certificate is wanted, the resulting decision procedure supplies it by at most `n+1` pinned queries, followed by original-source verification. Query construction, enlarged written sizes and the final verification are then included in the separate composed polynomial.

## 5. H24 frontier calibration is the exact source of the accounting

In the original occurrence-sensitive grammar, each admitted rule `r` has a head `h(r)`, an ordered list of premise occurrences `p_i(r)`, a declared charge `c(r)` and nonnegative slack `σ(r)`, with

\[
c(r)+\sum_i V(p_i(r))=V(h(r))+\sigma(r).
\tag{6}
\]

For the ordered frontier `F`, set `Φ(F)=Σ_{j∈F}V(j)`. Expanding one occurrence of the head into its premises gives

\[
c(r)+\Phi(F')=\Phi(F)+\sigma(r).
\tag{7}
\]

Thus `a(r)=σ(r)` is a literal instance of the balance in β. Repeated equal premises remain repeated occurrences. An explicit leftmost expansion of any finite proof starts at `[j]` and ends at the empty frontier. Summing (7) gives

\[
\operatorname{cost}(p)=V(j)+\sum_{r\text{ occurring in }p}\sigma(r).
\tag{8}
\]

Consequently `V(j)` lower-bounds every admitted proof of the same conclusion. A constructed proof with all local slacks zero attains the bound and is minimum in that grammar. This is the original `HCWholeProofReturns` and `HCMinimumReturn` theorem with its actual inputs.

To instantiate (7) as a **bit-clock** law, the charge must be the complete actual primitive cost of the admitted operational rule. The old `n+1/n+2` proof representation does not acquire this interpretation by renaming its grade. The operational refinement keeps the original rule and source return, attaches its actual microtrace, and includes performed routing, lookups, checks and cleanup as additional costed steps. No existing comparison grammar is silently changed.

### Construct a primitive calibration from a costed macro

Suppose one admitted macro has source and target natural potentials `u,v`, actual microtrace length `w≥1`, and verified nonnegative slack `σ=w+v-u`. A natural potential at every primitive boundary can be constructed explicitly:

- If `u≥v`, let `Δ=u-v≤w` and put `Φ_i=max(u-i,v)` for `0≤i≤w`. The first `Δ` ticks decrease the potential by one; later ticks keep it fixed. Every primitive slack `1+Φ_{i+1}-Φ_i` is zero or one.
- If `v>u`, keep `Φ_i=u` for `0≤i<w` and put `Φ_w=v`. The first `w-1` slacks are one and the last is `1+v-u`.

The primitive slacks are natural, sum to `σ`, and recover both endpoint potentials. This is a proof-only interpolation through the macro's actual in-progress configurations. In particular a tight macro has `u-v=w` and every microtick is tight. It is not necessary to evaluate this interpolation at runtime.

This supplies actual per-bit calibration when the macro's actual microtrace and source return are available. It does not replace those microtraces with matrix multiplication as a unit-time instruction.

## 6. Exact H24 tightness of an attained operational return

Let `𝒢_M(C)` be the declared original operational grammar: actual primitive ticks of `M` from the original input, serial composition of those ticks, and the checked-event terminal rule. The complete configuration and original source are retained in the judgement. A comparison with a larger grammar requires calibration for the additional rules as well.

For a promised-side input the bounded constructor in §4 yields a finite deterministic execution

\[
s_0\to s_1\to\cdots\to s_T
\]

whose first event is at `T`. Define the exact residual calibration on its reachable prefix positions by

\[
\lambda(s_i,i)=T-i.
\tag{9}
\]

The source-state type retains the prefix position or equivalent reachability witness; there is no ambiguity from repeated semantic payloads. For a primitive rule, `1+λ_{i+1}=λ_i`; the event has `λ_T=0`. This is a tight local calibration of the actual execution grammar. Every valid derivation of a checked event from the same initial source follows the same deterministic ticks until that event; applying the calibration gives `W≥T`. The constructed derivation has `W=T`. Therefore it is an attained original H24 minimum in `𝒢_M(C)`.

The exact calibration can be built from the finite execution already constructed by reserve recursion. It does not require discovering a shortest unrelated SAT algorithm. The resulting record is

```text
OperationalH24Return(C):
  original_input = C
  fixed_program = M
  execution e : actual run to the first checked original event
  output z : Cert⁻(C)
  source_equation : decode(last(e)) = z
  actual_work : W(e) = T
  deadline : T ≤ (k+b)(|C|+1)^max(e,f)
  local_calibration : every actual tick has zero λ-excess
  minimum : every competitor in the same declared operational grammar costs ≥ T
```

The lower calibration and upper reserve can now be compared explicitly:

\[
\lambda(s_0) = T\le\Psi(s_0)\le p(N).
\]

If `λ(s_0)=Ψ(s_0)` and the terminal reserve is zero, all reserve balances are tight and `T=Ψ(s_0)`. Tightness does not mean that the semantic original failed-clause minimum, the source proof length and the producer clock have become the same number.

## 7. A full polynomial cost-decomposition constructor

The local work grammar keeps all performed components:

```text
Cost ::= Parse | Compile | Route | Address | Lookup | Arithmetic
       | SelectRule | Acquire | Produce | Verify | Readback | Cleanup
       | Seq Cost Cost
       | Choice selector_cost finite_branch_costs
       | Repeat count_bound Cost
       | AtSize operand_size_bound Cost
```

Each leaf is paired with its actual operational implementation and a proved uniform polynomial bound in its declared input size. `Seq` adds paid work. `Choice` pays for its actual selector and adds a common maximum bound for the selected finite branch; the selector must return a valid branch and its required source evidence. `Repeat` requires a bound on the **actual number of executed occurrences**. `AtSize` requires a bound on the actual encoded operand length. These are constructor fields; the interface's four matrix rows do not supply either bound.

Represent local bounds by `P(c,d)(N)=c(N+1)^d`. The following operations construct new explicit monomial bounds:

\[
\begin{aligned}
P(c,d)+P(a,e)&\le P(c+a,\max(d,e)),\\
P(c,d)P(a,e)&=P(ca,d+e),\\
\max(P(c,d),P(a,e))&\le P(\max(c,a),\max(d,e)),\\
P(c,d)(P(a,e)(N))&\le
P(c(a+1)^d,ed)(N).
\end{aligned}
\tag{10}
\]

For composition, put `x=N+1≥1`. Then `a x^e+1≤(a+1)x^e`; raising to `d` and multiplying by `c` proves the last line, including degree-zero cases. The first line follows because both exponents are at most their maximum; product is direct; the maximum line follows from componentwise monotonicity. Thus every syntactic cost expression yields its explicit coefficient and degree by structural recursion.

For example, supplied bounds for setup `S`, the count of actual expansion events `Q`, operand size `L`, local work components `L_i`, and final components `F_j` give

\[
W(C)\le
S(N)+Q(N)\sum_i L_i(L(N))+\sum_j F_j(N).
\tag{11}
\]

The executable `complete_clock_bound` implements exactly this recurrence. The local proofs together with an exact event-coverage and all-prefix ledger proof construct β; bounding a cost expression only for already finished executions does not construct its progress or coverage fields.

A useful alternative avoids multiplying a worst per-event bound by every duplicate call. In the original shared-key proof, an exact local cost `q(N)` reserves discovery and completion for each fresh key, and reuse is charged within an admitted expansion. If an actual source theorem bounds acquired keys by `Q(N)`, setup plus `qQ` plus readback is an instance of (11). Its `Q` field belongs to `J_β`; it is not inferred from the six-frame group or from the ability to encode a key in a canonical cylinder.

## 8. Transport the complete bridge on the torser

The original literal operation type is

\[
\operatorname{Op}(X,Y)
=\sum_{f:X\to Y}\prod_x\operatorname{Iso}_G(P_x,Q_{f(x)}),
\quad G=\mathrm{GL}_2(\mathbb F_2)\cong S_3.
\]

Choose `X` to retain source configurations, event certificates and the actual resource record above. Its native matrix column has destination `f(x)` and the invertible frame block `ρ(h(x))`. The existing faithful decoder recovers both fields. Regrouping gives a four-by-four matrix over the context-operator algebra, whose multiplication is composition of those operators.

Decorate an actual path with its paid work:

\[
(V,d)\circ(U,c)=(VU,c+d),
\qquad (U,c)^\dagger=(U^\dagger,c).
\tag{12}
\]

This representation keeps the source-state return and the chronological grade simultaneously. Applying an inverse after execution gives `(I,2c)`, while the empty execution is `(I,0)`. Compiler cancellation before execution is a different admitted implementation and must have its own actual trace.

The chart maps transport `β⁻`, `Ψ`, `λ`, the event decoder and the original program/clock fields as a whole dependent record. Under passive conjugation, the pulled-back work returns exactly. If the codecs are executed, their actual costs are added once through `Seq` and (10). Canonical prefix/tail coding has its existing all-tail inverse; it does not change the source quantifier or the event being timed.

## 9. Executable finite checks and precise limits

Run:

```sh
python bridge_h24/agent_clock/bridge_clock_ledger.py
```

The checker validates nonnegative work, state and credit continuity, every-prefix budget, the exact local balance, the constructed reserve, a first-event boundary and an original-source terminal check. Its primitive fixture constructs the original clean four-port OR lift with nine compute gates, one copy, and nine inverse gates. The fixed eight-wire register and fixed gate programme make these bounded local primitives. The fixture records 19 paid transitions and 38 for the executed inverse return.

The checks also retain the original tight frontier `[A]→[B,B]→[B]→[]`, with potentials `5,4,2,0` and rule charges `1,2,2`; that fixture is expressly a rule-grade ledger until supplied with its actual microtrace. A signed-amortized fixture confirms that the allowance can rise while the total reserve falls.

Five false inferences are rejected: zero runtime for an executed inverse pair; substituting a small candidate grade for this execution's work; a completed-return claim without an event; an unbudgeted positive slack; and a live transition assigned zero primitive cost. These are targeted finite diagnostics of grade and event preservation. Their receipt does not claim to establish an unrestricted input-polynomial event bound.

## 10. Original source map

1. `bridge_h24/originals/Reversible_H24_Clock_Adjoints.pdf`, original Library file `libfile_fde3_f-c175670932b0819195cd5284d57412fb_1c1d5836f5948191a57956db18020361`, version 0. Full ten-page argument read. Theorems 1 and 2, frontier §§3–3.1, source adjunction §4 and exact event conventions §2.2 are used above.
2. `h24_work/originals/Final_Proofs_Seven_Twenty_GRH_YM_Hilbert24_PNP.het`: `APPRankingData`, `APPRankingReturns`, `APPFredkinFuelData/Returns`, `APPDiagonalData/Returns`, and `APPFullHigherData/Returns`. The exact Fredkin cursor fuel is `1+6 clauses+14 literals` for one original assignment; its gate addresses are separately charged. That per-assignment cursor is not the full empty-diagonal producer.
3. `h24_work/originals/Hilbert24_Portable.het`: `HCProofData`, `HCWholeProofReturns`, `HCMinimumReturn`, `HCNativeMinimumReturns`, and the explicitly scoped induction/replay nodes. The original charge grammar and occurrence multiplicity are retained.
4. `pnp_work/extracted/PNP_Multiple_Constructions/PNP_Multiple_Constructions/README.md`, `TORSOR_MODEL.md`, `agda/RouteBounds.agda`, and `prior/FullReturn.agda`. Complete chapters and the two source modules read; their code and supplied-input boundaries remain unchanged.
5. `h24_work/extracted/Hilbert24_ConstructMinimum_Fixed/Hilbert24_ConstructMinimum/Reversibility_Time_Adjoints.txt`: original 19-step reversible cell, positive historical work, credit balance and source-dependent adjoints.

The new proved bridge is the explicit constructor

\[
\boxed{
\beta^{-}(M,K,B)
\longmapsto
\operatorname{Ranking}_{\mathrm{actual\ promised\ prefixes}}
\longmapsto
\operatorname{CheckedOriginalDeadline}
\longmapsto
\operatorname{OperationalH24Return}.
}
\]

Its remaining source content has the exact judgement `J_β(M,K,B)` and the input fields in §2. It can be attacked, composed and minimized in the programme's original proof grammar without changing the meaning of the clock or of the returned original certificate.
