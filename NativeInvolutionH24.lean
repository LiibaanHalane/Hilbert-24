import Lean

/- Self-contained edition of the checked reversible H24 development.
   Modular originals and full replay receipts are in the companion archive. -/


/- Module: Hilbert24_Calibrated_Policy -/
/-
Constructive proof-path calibration and a well-founded tight-policy constructor.
Arbitrary judgement and rule types; each rule has finite ordered arity.
No search over proofs is used by the policy constructor.
-/

namespace Hilbert24Policy

universe u v w

def sumFin : {n : Nat} → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => f ⟨0, Nat.zero_lt_succ n⟩ + sumFin (fun i => f i.succ)

theorem sumFin_congr {n : Nat} (f g : Fin n → Nat)
    (h : ∀ i, f i = g i) : sumFin f = sumFin g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change f ⟨0, Nat.zero_lt_succ n⟩ + sumFin (fun i => f i.succ) =
        g ⟨0, Nat.zero_lt_succ n⟩ + sumFin (fun i => g i.succ)
      rw [h, ih (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ)]

theorem sumFin_add {n : Nat} (f g : Fin n → Nat) :
    sumFin (fun i => f i + g i) = sumFin f + sumFin g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (f ⟨0, Nat.zero_lt_succ n⟩ + g ⟨0, Nat.zero_lt_succ n⟩) +
          sumFin (fun i => f i.succ + g i.succ) =
        (f ⟨0, Nat.zero_lt_succ n⟩ + sumFin (fun i => f i.succ)) +
          (g ⟨0, Nat.zero_lt_succ n⟩ + sumFin (fun i => g i.succ))
      rw [ih]
      exact Nat.add_add_add_comm _ _ _ _

theorem sumFin_zero {n : Nat} : sumFin (fun _ : Fin n => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change 0 + sumFin (fun _ : Fin n => 0) = 0
      rw [Nat.zero_add]
      exact ih

structure RuleSystem (J : Type u) where
  Rule : Type v
  conclusion : Rule → J
  arity : Rule → Nat
  premise : (r : Rule) → Fin (arity r) → J
  charge : Rule → Nat

inductive Derivation {J : Type u} (S : RuleSystem.{u,v} J) : J → Type (max u v)
  | node (r : S.Rule)
      (children : (i : Fin (S.arity r)) → Derivation S (S.premise r i)) :
      Derivation S (S.conclusion r)

def work {J : Type u} {S : RuleSystem.{u,v} J} : {j : J} → Derivation S j → Nat
  | _, .node r children => S.charge r + sumFin (fun i => work (children i))

structure Calibration {J : Type u} (S : RuleSystem.{u,v} J) where
  potential : J → Nat
  slack : S.Rule → Nat
  local_identity : ∀ r, S.charge r + sumFin (fun i => potential (S.premise r i)) =
      potential (S.conclusion r) + slack r

def totalSlack {J : Type u} {S : RuleSystem.{u,v} J} (V : Calibration S) :
    {j : J} → Derivation S j → Nat
  | _, .node r children => V.slack r + sumFin (fun i => totalSlack V (children i))

/-- Exact discrete Stokes identity over the entire original derivation tree. -/
theorem stokes {J : Type u} {S : RuleSystem.{u,v} J}
    (V : Calibration S) {j : J} (p : Derivation S j) :
    work p = V.potential j + totalSlack V p := by
  induction p with
  | node r children ih =>
      change S.charge r + sumFin (fun i => work (children i)) =
        V.potential (S.conclusion r) +
          (V.slack r + sumFin (fun i => totalSlack V (children i)))
      rw [sumFin_congr (fun i => work (children i))
        (fun i => V.potential (S.premise r i) + totalSlack V (children i)) ih]
      rw [sumFin_add, ← Nat.add_assoc, V.local_identity, Nat.add_assoc]

theorem global_lower_bound {J : Type u} {S : RuleSystem.{u,v} J}
    (V : Calibration S) {j : J} (p : Derivation S j) : V.potential j ≤ work p := by
  rw [stokes V p]
  exact Nat.le_add_right _ _

theorem add_sub_of_le_constructive {a b : Nat} (h : a ≤ b) :
    a + (b - a) = b := by
  induction a generalizing b with
  | zero => exact Nat.zero_add b
  | succ a ih =>
      cases b with
      | zero => cases h
      | succ b =>
          rw [Nat.succ_sub_succ, Nat.succ_add, ih (Nat.le_of_succ_le_succ h)]

/-- Feasible local inequalities produce the exact nonnegative slack data. -/
def calibrationFromFeasible {J : Type u} (S : RuleSystem.{u,v} J)
    (potential : J → Nat)
    (feasible : ∀ r, potential (S.conclusion r) ≤
      S.charge r + sumFin (fun i => potential (S.premise r i))) : Calibration S :=
  { potential := potential
    slack := fun r =>
      (S.charge r + sumFin (fun i => potential (S.premise r i))) -
        potential (S.conclusion r)
    local_identity := fun r => (add_sub_of_le_constructive (feasible r)).symm }

structure TightPolicy {J : Type u} (S : RuleSystem.{u,v} J) (V : Calibration S) where
  chosen : (j : J) → {r : S.Rule // S.conclusion r = j}
  tight : ∀ j, V.slack (chosen j).val = 0
  rank : J → Nat
  decrease : ∀ j i, rank (S.premise (chosen j).val i) < rank j

/-- Every recursive call follows the selected rule's original premise.  The
    displayed rank proof makes this a total constructor, without a search cap. -/
def build {J : Type u} {S : RuleSystem.{u,v} J} {V : Calibration S}
    (policy : TightPolicy S V) (j : J) : Derivation S j :=
  let r := policy.chosen j
  r.property ▸ Derivation.node r.val
    (fun i => build policy (S.premise r.val i))
termination_by policy.rank j
decreasing_by exact policy.decrease j i

-- Main theorems for the policy's exact work and minimum follow below.

theorem totalSlack_transport {J : Type u} {S : RuleSystem.{u,v} J}
    (V : Calibration S) {j k : J} (h : j = k) (p : Derivation S j) :
    totalSlack V (h ▸ p) = totalSlack V p := by
  cases h
  rfl

theorem build_has_zero_slack {J : Type u} {S : RuleSystem.{u,v} J}
    {V : Calibration S} (policy : TightPolicy S V) (j : J) :
    totalSlack V (build policy j) = 0 := by
  generalize hn : policy.rank j = n
  induction n using Nat.strongRecOn generalizing j with
  | ind n ih =>
      rw [build, totalSlack_transport]
      change V.slack (policy.chosen j).val +
        sumFin (fun i => totalSlack V
          (build policy (S.premise (policy.chosen j).val i))) = 0
      rw [policy.tight, Nat.zero_add]
      calc
        sumFin (fun i => totalSlack V
          (build policy (S.premise (policy.chosen j).val i))) =
            sumFin (fun _ => 0) := by
              apply sumFin_congr
              intro i
              apply ih (policy.rank (S.premise (policy.chosen j).val i))
              · rw [← hn]
                exact policy.decrease j i
              · rfl
        _ = 0 := sumFin_zero

theorem build_attains {J : Type u} {S : RuleSystem.{u,v} J}
    {V : Calibration S} (policy : TightPolicy S V) (j : J) :
    work (build policy j) = V.potential j := by
  rw [stokes, build_has_zero_slack, Nat.add_zero]

/-- The selected original proof is optimal against every original derivation,
    without an enumeration, a maximum proof depth or a coefficient aperture. -/
theorem build_is_global_minimum {J : Type u} {S : RuleSystem.{u,v} J}
    {V : Calibration S} (policy : TightPolicy S V)
    (j : J) (competitor : Derivation S j) :
    work (build policy j) ≤ work competitor := by
  rw [build_attains]
  exact global_lower_bound V competitor

def IsGlobalMinimum {J : Type u} {S : RuleSystem.{u,v} J}
    {j : J} (p : Derivation S j) : Prop :=
  ∀ competitor : Derivation S j, work p ≤ work competitor

theorem cancel_add_le_left {a b c : Nat} (h : a + b ≤ a + c) : b ≤ c := by
  induction a with
  | zero =>
      rw [Nat.zero_add, Nat.zero_add] at h
      exact h
  | succ a ih =>
      rw [Nat.succ_add, Nat.succ_add] at h
      exact ih (Nat.le_of_succ_le_succ h)

/-- Every minimizer is retained: zero total slack characterizes the complete
    minimum fibre, not only the policy's selected representative. -/
theorem minimum_iff_zero_slack {J : Type u} {S : RuleSystem.{u,v} J}
    {V : Calibration S} (policy : TightPolicy S V) {j : J}
    (p : Derivation S j) : IsGlobalMinimum p ↔ totalSlack V p = 0 := by
  constructor
  · intro h
    have hp : V.potential j + totalSlack V p ≤ V.potential j + 0 := by
      calc
        V.potential j + totalSlack V p = work p := (stokes V p).symm
        _ ≤ work (build policy j) := h _
        _ = V.potential j + 0 := by rw [build_attains, Nat.add_zero]
    exact Nat.eq_zero_of_le_zero (cancel_add_le_left hp)
  · intro h competitor
    calc
      work p = V.potential j := by rw [stokes V p, h, Nat.add_zero]
      _ ≤ work competitor := global_lower_bound V competitor

theorem add_eq_zero_parts {a b : Nat} (h : a + b = 0) : a = 0 ∧ b = 0 := by
  cases a with
  | zero => exact ⟨rfl, (Nat.zero_add b).symm.trans h⟩
  | succ a =>
      rw [Nat.succ_add] at h
      cases h

theorem sumFin_zero_imp {n : Nat} (f : Fin n → Nat)
    (h : sumFin f = 0) : ∀ i, f i = 0 := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      have parts : f ⟨0, Nat.zero_lt_succ n⟩ = 0 ∧
          sumFin (fun i => f i.succ) = 0 := add_eq_zero_parts h
      intro i
      cases i with
      | mk k hk =>
          cases k with
          | zero => exact parts.left
          | succ k =>
              exact ih (fun t => f t.succ) parts.right
                ⟨k, Nat.lt_of_succ_lt_succ hk⟩

def allTight {J : Type u} {S : RuleSystem.{u,v} J} (V : Calibration S) :
    {j : J} → Derivation S j → Prop
  | _, .node r children => V.slack r = 0 ∧ ∀ i, allTight V (children i)

theorem zero_slack_iff_allTight {J : Type u} {S : RuleSystem.{u,v} J}
    (V : Calibration S) {j : J} (p : Derivation S j) :
    totalSlack V p = 0 ↔ allTight V p := by
  induction p with
  | node r children ih =>
      constructor
      · intro h
        have parts := add_eq_zero_parts h
        refine ⟨parts.left, ?_⟩
        intro i
        exact (ih i).mp (sumFin_zero_imp _ parts.right i)
      · intro h
        change V.slack r + sumFin (fun i => totalSlack V (children i)) = 0
        rw [h.left, Nat.zero_add]
        calc
          sumFin (fun i => totalSlack V (children i)) = sumFin (fun _ => 0) :=
            sumFin_congr _ _ (fun i => (ih i).mpr (h.right i))
          _ = 0 := sumFin_zero

theorem complete_minimum_fibre {J : Type u} {S : RuleSystem.{u,v} J}
    {V : Calibration S} (policy : TightPolicy S V) {j : J}
    (p : Derivation S j) : IsGlobalMinimum p ↔ allTight V p :=
  (minimum_iff_zero_slack policy p).trans (zero_slack_iff_allTight V p)

structure OptimalReturn {J : Type u} (S : RuleSystem.{u,v} J)
    (V : Calibration S) (j : J) where
  derivation : Derivation S j
  exact_cost : work derivation = V.potential j
  optimal : IsGlobalMinimum derivation

/-- One executable return containing the proof and its exact/global certificates. -/
def constructMinimum {J : Type u} {S : RuleSystem.{u,v} J} {V : Calibration S}
    (policy : TightPolicy S V) (j : J) : OptimalReturn S V j :=
  { derivation := build policy j
    exact_cost := build_attains policy j
    optimal := build_is_global_minimum policy j }

/-- Interpret each rule by its actual original typed constructor. -/
def interpret {J : Type u} {S : RuleSystem.{u,v} J} (Meaning : J → Type w)
    (constructor : (r : S.Rule) →
      ((i : Fin (S.arity r)) → Meaning (S.premise r i)) →
      Meaning (S.conclusion r)) : {j : J} → Derivation S j → Meaning j
  | _, .node r children => constructor r (fun i => interpret Meaning constructor (children i))

/-- The policy returns an inhabitant of the original dependent judgement when
    the actual source rules have the displayed typed interpretations. -/
def returnOriginal {J : Type u} {S : RuleSystem.{u,v} J} {V : Calibration S}
    (Meaning : J → Type w)
    (constructor : (r : S.Rule) →
      ((i : Fin (S.arity r)) → Meaning (S.premise r i)) →
      Meaning (S.conclusion r))
    (policy : TightPolicy S V) (j : J) : Meaning j :=
  interpret Meaning constructor (build policy j)

/- An infinite family, supplied symbolically.  For every n there is a cheap
   n-step proof, an expensive direct proof, and a zero-cost loop.  The policy
   constructs the optimum for every n without a grammar or depth bound. -/
inductive ChainRule
  | base
  | step (n : Nat)
  | expensive (n : Nat)
  | loop (n : Nat)

def chainSystem : RuleSystem Nat where
  Rule := ChainRule
  conclusion
    | .base => 0
    | .step n => n + 1
    | .expensive n => n
    | .loop n => n
  arity
    | .base => 0
    | .step _ => 1
    | .expensive _ => 0
    | .loop _ => 1
  premise
    | .base, i => Fin.elim0 i
    | .step n, _ => n
    | .expensive _, i => Fin.elim0 i
    | .loop n, _ => n
  charge
    | .base => 0
    | .step _ => 1
    | .expensive n => n + 5
    | .loop _ => 0

def chainCalibration : Calibration chainSystem where
  potential := fun n => n
  slack
    | .base => 0
    | .step _ => 0
    | .expensive _ => 5
    | .loop _ => 0
  local_identity r := by
    cases r with
    | base => rfl
    | step n =>
        change 1 + (n + 0) = (n + 1) + 0
        rw [Nat.add_zero, Nat.add_zero, Nat.add_comm]
    | expensive n => rfl
    | loop n => exact Nat.zero_add _

def chainPolicy : TightPolicy chainSystem chainCalibration where
  chosen
    | 0 => ⟨.base, rfl⟩
    | n + 1 => ⟨.step n, rfl⟩
  tight j := by cases j <;> rfl
  rank := fun n => n
  decrease j i := by
    cases j with
    | zero => exact Fin.elim0 i
    | succ n => exact Nat.lt_succ_self n

theorem chain_all_inputs (n : Nat) (competitor : Derivation chainSystem n) :
    work (build chainPolicy n) = n ∧ n ≤ work competitor :=
  ⟨build_attains chainPolicy n, global_lower_bound chainCalibration competitor⟩

def chainLoopProof (n : Nat) : Derivation chainSystem n :=
  Derivation.node (S := chainSystem) (ChainRule.loop n) (fun _ => build chainPolicy n)

theorem chainLoop_is_also_minimum (n : Nat) : IsGlobalMinimum (chainLoopProof n) := by
  apply (minimum_iff_zero_slack chainPolicy _).mpr
  change 0 + (totalSlack chainCalibration (build chainPolicy n) + 0) = 0
  rw [build_has_zero_slack]

-- Evaluation follows only the chosen tight rule and retains a typed derivation.
#eval work (build chainPolicy 25)

theorem chain_example_25 : work (build chainPolicy 25) = 25 :=
  build_attains chainPolicy 25

#print axioms sumFin_congr
#print axioms sumFin_add
#print axioms stokes
#print axioms global_lower_bound
#print axioms calibrationFromFeasible
#print axioms build
#print axioms build_has_zero_slack
#print axioms build_attains
#print axioms build_is_global_minimum
#print axioms minimum_iff_zero_slack
#print axioms zero_slack_iff_allTight
#print axioms add_eq_zero_parts
#print axioms sumFin_zero_imp
#print axioms complete_minimum_fibre
#print axioms constructMinimum
#print axioms interpret
#print axioms returnOriginal
#print axioms chain_all_inputs
#print axioms chain_example_25
#print axioms chainLoop_is_also_minimum

end Hilbert24Policy


/- Module: ReversibleCore -/

/- Constructive clock, source-return, and potential interfaces.
   Every assumption is an explicit parameter. No SAT algorithm or polynomial
   bound is postulated. Natural balances avoid truncated subtraction. -/

namespace ReversibleH24

universe u v

def orig (r p n x : Bool) : Bool :=
  r && ((x || p) && ((!x) || n))

def reduced (r p n : Bool) : Bool := r && (p || n)

def toffoliThird (a b c : Bool) : Bool := Bool.xor c (a && b)
def fredkinSecond (a b c : Bool) : Bool := if a then c else b
def fredkinThird (a b c : Bool) : Bool := if a then b else c

theorem zero_branch (r p n : Bool) :
    orig r p n false = (r && p) := by
  cases r <;> cases p <;> cases n <;> rfl

theorem one_branch (r p n : Bool) :
    orig r p n true = (r && n) := by
  cases r <;> cases p <;> cases n <;> rfl

theorem finite_exists_exact (r p n : Bool) :
    (orig r p n false || orig r p n true) = reduced r p n := by
  cases r <;> cases p <;> cases n <;> rfl

theorem chosen_lift_exact (r p n : Bool) :
    orig r p n (!p) = reduced r p n := by
  cases r <;> cases p <;> cases n <;> rfl

theorem projection_sound (r p n x : Bool) :
    orig r p n x = true → reduced r p n = true := by
  cases r <;> cases p <;> cases n <;> cases x <;> intro h
  all_goals first | rfl | cases h

theorem bool_or_false : (a b : Bool) →
    (a || b) = false ↔ a = false ∧ b = false
  | false, false => ⟨fun _ => ⟨rfl, rfl⟩, fun _ => rfl⟩
  | false, true => ⟨(fun h => by cases h), (fun h => by cases h.right)⟩
  | true, false => ⟨(fun h => by cases h), (fun h => by cases h.left)⟩
  | true, true => ⟨(fun h => by cases h), (fun h => by cases h.left)⟩

theorem finite_refuter_exact (r p n : Bool) :
    reduced r p n = false ↔
      orig r p n false = false ∧ orig r p n true = false := by
  rw [← finite_exists_exact r p n]
  exact bool_or_false _ _

theorem projection_can_have_two_witnesses :
    orig true true true false = true ∧
    orig true true true true = true := ⟨rfl, rfl⟩

theorem toffoli_involution (a b c : Bool) :
    toffoliThird a b (toffoliThird a b c) = c := by
  cases a <;> cases b <;> cases c <;> rfl

theorem fredkin_second_return (a b c : Bool) :
    fredkinSecond a (fredkinSecond a b c) (fredkinThird a b c) = b := by
  cases a <;> cases b <;> cases c <;> rfl

theorem fredkin_third_return (a b c : Bool) :
    fredkinThird a (fredkinSecond a b c) (fredkinThird a b c) = c := by
  cases a <;> cases b <;> cases c <;> rfl

abbrev OriginalModel (r p n : Bool) := {x : Bool // orig r p n x = true}
abbrev ReducedModel (r p n : Bool) := reduced r p n = true

def projectModel {r p n : Bool} (m : OriginalModel r p n) : ReducedModel r p n :=
  projection_sound r p n m.val m.property

def liftModel {r p n : Bool} (m : ReducedModel r p n) : OriginalModel r p n :=
  ⟨!p, (chosen_lift_exact r p n).trans m⟩

theorem project_lift {r p n : Bool} (m : ReducedModel r p n) :
    projectModel (liftModel m) = m := rfl

def refuteOriginal {r p n : Bool} (h : ReducedModel r p n → False) :
    OriginalModel r p n → False := fun m => h (projectModel m)

def refuteReduced {r p n : Bool} (h : OriginalModel r p n → False) :
    ReducedModel r p n → False := fun m => h (liftModel m)

/-- A typed inverse-return fragment; composition on noncomposable arrows
    is unrepresentable in this interface. -/
structure InverseSystem (Obj : Type u) where
  Arrow : Obj → Obj → Type v
  identity : (x : Obj) → Arrow x x
  compose : {x y z : Obj} → Arrow y z → Arrow x y → Arrow x z
  inverse : {x y : Obj} → Arrow x y → Arrow y x
  inverse_left : ∀ {x y} (f : Arrow x y),
    compose (inverse f) f = identity x

structure NonnegativeClock {Obj : Type u} (G : InverseSystem.{u,v} Obj) where
  ticks : {x y : Obj} → G.Arrow x y → Nat
  identity_zero : ∀ x, ticks (G.identity x) = 0
  composable_add : ∀ {x y z} (f : G.Arrow y z) (g : G.Arrow x y),
    ticks (G.compose f g) = ticks f + ticks g

theorem additive_nonnegative_groupoid_clock_vanishes
    {Obj : Type u} (G : InverseSystem.{u,v} Obj) (W : NonnegativeClock G)
    {x y : Obj} (f : G.Arrow x y) : W.ticks f = 0 := by
  have h : W.ticks (G.inverse f) + W.ticks f = 0 := by
    calc
      W.ticks (G.inverse f) + W.ticks f =
        W.ticks (G.compose (G.inverse f) f) := (W.composable_add _ _).symm
      _ = W.ticks (G.identity x) := congrArg W.ticks (G.inverse_left f)
      _ = 0 := W.identity_zero x
  exact (Hilbert24Policy.add_eq_zero_parts h).right

theorem fixedpoint_has_no_distinct_incoming_state
    {State : Type u} (step : State → State)
    (injective : ∀ a b, step a = step b → a = b)
    (halt : State) (fixed : step halt = halt) (s : State)
    (arrives : step s = halt) : s = halt :=
  injective s halt (arrives.trans fixed.symm)

abbrev Timed (A : Type u) := A × Nat

def timedCompose {A : Type u} (mul : A → A → A) (v u : Timed A) : Timed A :=
  (mul v.1 u.1, u.2 + v.2)

def timedDagger {A : Type u} (dagger : A → A) (u : Timed A) : Timed A :=
  (dagger u.1, u.2)

theorem dagger_preserves_paid_work {A : Type u} (dagger : A → A) (u : Timed A) :
    (timedDagger dagger u).2 = u.2 := rfl

theorem reversible_roundtrip_charged {A : Type u}
    (mul : A → A → A) (dagger : A → A) (one : A)
    (inverse_left : ∀ a, mul (dagger a) a = one) (u : Timed A) :
    timedCompose mul (timedDagger dagger u) u = (one, u.2 + u.2) := by
  cases u with
  | mk a c =>
      change (mul (dagger a) a, c + c) = (one, c + c)
      rw [inverse_left a]

theorem dagger_twice {A : Type u} (dagger : A → A)
    (involution : ∀ a, dagger (dagger a) = a) (u : Timed A) :
    timedDagger dagger (timedDagger dagger u) = u := by
  cases u with
  | mk a c =>
      change (dagger (dagger a), c) = (a, c)
      rw [involution a]

def accumulated (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => accumulated f k + f k

/-- The original rule slack is precisely the amortized charge when a frontier
    head is replaced by its ordered premises; the untouched context is kept. -/
theorem h24_frontier_slack_balance
    {J : Type u} {S : Hilbert24Policy.RuleSystem.{u,v} J}
    (V : Hilbert24Policy.Calibration S) (r : S.Rule) (context : Nat) :
    S.charge r +
      (Hilbert24Policy.sumFin (fun i => V.potential (S.premise r i)) + context) =
    V.slack r + (V.potential (S.conclusion r) + context) := by
  rw [← Nat.add_assoc, V.local_identity,
    Nat.add_comm (V.potential (S.conclusion r)) (V.slack r), Nat.add_assoc]

theorem natural_balance_telescope
    (paid potential amortized : Nat → Nat)
    (balance : ∀ k, paid k + potential (k+1) =
      amortized k + potential k) (k : Nat) :
    accumulated paid k + potential k =
      accumulated amortized k + potential 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (accumulated paid k + paid k) + potential (k+1) =
        (accumulated amortized k + amortized k) + potential 0
      calc
        (accumulated paid k + paid k) + potential (k+1)
          = accumulated paid k + (paid k + potential (k+1)) := Nat.add_assoc _ _ _
        _ = accumulated paid k + (amortized k + potential k) :=
          congrArg (fun t => accumulated paid k + t) (balance k)
        _ = (accumulated paid k + potential k) + amortized k := by
          rw [Nat.add_comm (amortized k) (potential k), ← Nat.add_assoc]
        _ = (accumulated amortized k + potential 0) + amortized k :=
          congrArg (fun t => t + amortized k) ih
        _ = (accumulated amortized k + amortized k) + potential 0 := by
          rw [Nat.add_assoc, Nat.add_comm (potential 0) (amortized k),
            ← Nat.add_assoc]

theorem prefix_paid_bound
    (paid potential amortized : Nat → Nat)
    (balance : ∀ k, paid k + potential (k+1) =
      amortized k + potential k)
    (k K B : Nat) (initial : potential 0 ≤ K)
    (budget : accumulated amortized k ≤ B) :
    accumulated paid k ≤ B + K := by
  calc
    accumulated paid k ≤ accumulated paid k + potential k := Nat.le_add_right _ _
    _ = accumulated amortized k + potential 0 :=
      natural_balance_telescope paid potential amortized balance k
    _ ≤ B + K := Nat.add_le_add budget initial

theorem positive_steps_count (paid : Nat → Nat)
    (positive : ∀ k, 1 ≤ paid k) (k : Nat) :
    k ≤ accumulated paid k := by
  induction k with
  | zero => exact Nat.le_refl 0
  | succ k ih => exact Nat.add_le_add ih (positive k)

theorem prefix_length_bound
    (paid potential amortized : Nat → Nat)
    (balance : ∀ k, paid k + potential (k+1) =
      amortized k + potential k)
    (positive : ∀ k, 1 ≤ paid k)
    (k K B : Nat) (initial : potential 0 ≤ K)
    (budget : accumulated amortized k ≤ B) : k ≤ B + K :=
  Nat.le_trans (positive_steps_count paid positive k)
    (prefix_paid_bound paid potential amortized balance k K B initial budget)

theorem no_prefix_beyond_budget
    (paid potential amortized : Nat → Nat)
    (balance : ∀ k, paid k + potential (k+1) =
      amortized k + potential k)
    (positive : ∀ k, 1 ≤ paid k)
    (K B : Nat) (initial : potential 0 ≤ K)
    (budget : accumulated amortized (B + K + 1) ≤ B) : False := by
  have h := prefix_length_bound paid potential amortized balance positive
    (B + K + 1) K B initial budget
  exact Nat.not_succ_le_self (B + K) h

/-- Two adjacent balances compose without any signed or truncated subtraction. -/
theorem two_step_balance (c d a b e h k : Nat)
    (first : c + b = h + a) (second : d + e = k + b) :
    (c + d) + e = (h + k) + a := by
  calc
    (c + d) + e = c + (d + e) := Nat.add_assoc _ _ _
    _ = c + (k + b) := congrArg (fun t => c + t) second
    _ = (c + b) + k := by rw [Nat.add_comm k b, ← Nat.add_assoc]
    _ = (h + a) + k := congrArg (fun t => t + k) first
    _ = (h + k) + a := by rw [Nat.add_assoc, Nat.add_comm a k, ← Nat.add_assoc]

theorem nat_cancel_right (a b c : Nat) (h : a + c = b + c) : a = b := by
  induction c with
  | zero => exact h
  | succ c ih => exact ih (Nat.succ.inj h)

theorem closed_path_paid_balance (c d a b h k : Nat)
    (first : c + b = h + a) (second : d + a = k + b) :
    c + d = h + k :=
  nat_cancel_right _ _ _ (two_step_balance c d a b a h k first second)

theorem equal_potential_preserves_cost (c a h : Nat)
    (balance : c + a = h + a) : c = h := nat_cancel_right _ _ _ balance

#print axioms chosen_lift_exact
#print axioms projection_sound
#print axioms finite_refuter_exact
#print axioms liftModel
#print axioms refuteOriginal
#print axioms refuteReduced
#print axioms toffoli_involution
#print axioms fredkin_second_return
#print axioms fredkin_third_return
#print axioms additive_nonnegative_groupoid_clock_vanishes
#print axioms fixedpoint_has_no_distinct_incoming_state
#print axioms reversible_roundtrip_charged
#print axioms natural_balance_telescope
#print axioms h24_frontier_slack_balance
#print axioms prefix_paid_bound
#print axioms prefix_length_bound
#print axioms no_prefix_beyond_budget
#print axioms closed_path_paid_balance

end ReversibleH24


/- Module: DependentAdjoints -/
/- Explicit family adjunctions and Beck--Chevalley maps.
   Equalities of dependent functions are stated pointwise. No function
   extensionality, choice, propositional extensionality, or postulates. -/

namespace ReversibleH24.Adjoints

universe u v w t

abbrev FamilyHom {I : Type u} (A : I → Type v) (B : I → Type w) :=
  (i : I) → A i → B i

abbrev Pullback {X : Type u} {Y : Type v} (q : X → Y) (B : Y → Type w) :=
  fun x => B (q x)

abbrev Fibre {X : Type u} {Y : Type v} (q : X → Y) (y : Y) :=
  {x : X // q x = y}

abbrev SigmaPush {X : Type u} {Y : Type v}
    (q : X → Y) (A : X → Type w) (y : Y) :=
  (z : Fibre q y) × A z.val

abbrev PiPush {X : Type u} {Y : Type v}
    (q : X → Y) (A : X → Type w) (y : Y) :=
  (z : Fibre q y) → A z.val

def sigmaTo {X : Type u} {Y : Type v} {q : X → Y}
    {A : X → Type w} {B : Y → Type t}
    (f : FamilyHom (SigmaPush q A) B) :
    FamilyHom A (Pullback q B) :=
  fun x a => f (q x) ⟨⟨x, rfl⟩, a⟩

def sigmaFrom {X : Type u} {Y : Type v} {q : X → Y}
    {A : X → Type w} {B : Y → Type t}
    (g : FamilyHom A (Pullback q B)) :
    FamilyHom (SigmaPush q A) B :=
  fun _ z => Eq.mp (congrArg B z.1.property) (g z.1.val z.2)

theorem sigma_to_from {X : Type u} {Y : Type v} {q : X → Y}
    {A : X → Type w} {B : Y → Type t}
    (g : FamilyHom A (Pullback q B)) (x : X) (a : A x) :
    sigmaTo (sigmaFrom g) x a = g x a := rfl

theorem sigma_from_to {X : Type u} {Y : Type v} {q : X → Y}
    {A : X → Type w} {B : Y → Type t}
    (f : FamilyHom (SigmaPush q A) B) (y : Y) (z : SigmaPush q A y) :
    sigmaFrom (sigmaTo f) y z = f y z := by
  rcases z with ⟨⟨x, h⟩, a⟩
  cases h
  rfl

def piTo {X : Type u} {Y : Type v} {q : X → Y}
    {A : X → Type w} {B : Y → Type t}
    (f : FamilyHom (Pullback q B) A) :
    FamilyHom B (PiPush q A) :=
  fun _ b z => f z.val (Eq.mp (congrArg B z.property.symm) b)

def piFrom {X : Type u} {Y : Type v} {q : X → Y}
    {A : X → Type w} {B : Y → Type t}
    (g : FamilyHom B (PiPush q A)) :
    FamilyHom (Pullback q B) A :=
  fun x b => g (q x) b ⟨x, rfl⟩

theorem pi_from_to {X : Type u} {Y : Type v} {q : X → Y}
    {A : X → Type w} {B : Y → Type t}
    (f : FamilyHom (Pullback q B) A) (x : X) (b : B (q x)) :
    piFrom (piTo f) x b = f x b := rfl

theorem pi_to_from {X : Type u} {Y : Type v} {q : X → Y}
    {A : X → Type w} {B : Y → Type t}
    (g : FamilyHom B (PiPush q A)) (y : Y) (b : B y) (z : Fibre q y) :
    piTo (piFrom g) y b z = g y b z := by
  rcases z with ⟨x, h⟩
  cases h
  rfl

/-- Hom-equivalence data with equality expressed pointwise, so the package
    itself does not require an extensionality principle for function types. -/
structure SigmaAdjunctionData {X : Type u} {Y : Type v}
    (q : X → Y) (A : X → Type w) (B : Y → Type t) where
  forward : FamilyHom (SigmaPush q A) B → FamilyHom A (Pullback q B)
  backward : FamilyHom A (Pullback q B) → FamilyHom (SigmaPush q A) B
  forward_backward : ∀ g x a, forward (backward g) x a = g x a
  backward_forward : ∀ f y z, backward (forward f) y z = f y z

def sigmaAdjunction {X : Type u} {Y : Type v}
    (q : X → Y) (A : X → Type w) (B : Y → Type t) :
    SigmaAdjunctionData q A B :=
  ⟨sigmaTo, sigmaFrom, sigma_to_from, sigma_from_to⟩

structure PiAdjunctionData {X : Type u} {Y : Type v}
    (q : X → Y) (A : X → Type w) (B : Y → Type t) where
  forward : FamilyHom (Pullback q B) A → FamilyHom B (PiPush q A)
  backward : FamilyHom B (PiPush q A) → FamilyHom (Pullback q B) A
  backward_forward : ∀ f x b, backward (forward f) x b = f x b
  forward_backward : ∀ g y b z, forward (backward g) y b z = g y b z

def piAdjunction {X : Type u} {Y : Type v}
    (q : X → Y) (A : X → Type w) (B : Y → Type t) :
    PiAdjunctionData q A B :=
  ⟨piTo, piFrom, pi_from_to, pi_to_from⟩

def sigmaMap {X : Type u} {Y : Type v} {q : X → Y}
    {A : X → Type w} {B : X → Type t}
    (f : FamilyHom A B) : FamilyHom (SigmaPush q A) (SigmaPush q B) :=
  fun _ z => ⟨z.1, f z.1.val z.2⟩

def piMap {X : Type u} {Y : Type v} {q : X → Y}
    {A : X → Type w} {B : X → Type t}
    (f : FamilyHom A B) : FamilyHom (PiPush q A) (PiPush q B) :=
  fun _ h z => f z.val (h z)

theorem sigma_map_identity {X : Type u} {Y : Type v} {q : X → Y}
    {A : X → Type w} (y : Y) (z : SigmaPush q A y) :
    sigmaMap (fun _ a => a) y z = z := by
  cases z
  rfl

theorem pi_map_identity {X : Type u} {Y : Type v} {q : X → Y}
    {A : X → Type w} (y : Y) (h : PiPush q A y) (z : Fibre q y) :
    piMap (fun _ a => a) y h z = h z := rfl

theorem sigma_map_composition {X : Type u} {Y : Type v} {q : X → Y}
    {A B C : X → Type w} (f : FamilyHom A B) (g : FamilyHom B C)
    (y : Y) (z : SigmaPush q A y) :
    sigmaMap (fun x a => g x (f x a)) y z =
      sigmaMap g y (sigmaMap f y z) := rfl

theorem pi_map_composition {X : Type u} {Y : Type v} {q : X → Y}
    {A B C : X → Type w} (f : FamilyHom A B) (g : FamilyHom B C)
    (y : Y) (h : PiPush q A y) (z : Fibre q y) :
    piMap (fun x a => g x (f x a)) y h z =
      piMap g y (piMap f y h) z := rfl

theorem sigma_adjunction_natural_source
    {X : Type u} {Y : Type v} {q : X → Y}
    {A A' : X → Type w} {B : Y → Type t}
    (f : FamilyHom (SigmaPush q A) B) (h : FamilyHom A' A)
    (x : X) (a : A' x) :
    sigmaTo (fun y z => f y (sigmaMap h y z)) x a =
      sigmaTo f x (h x a) := rfl

theorem sigma_adjunction_natural_target
    {X : Type u} {Y : Type v} {q : X → Y}
    {A : X → Type w} {B B' : Y → Type t}
    (f : FamilyHom (SigmaPush q A) B) (k : FamilyHom B B')
    (x : X) (a : A x) :
    sigmaTo (fun y z => k y (f y z)) x a =
      k (q x) (sigmaTo f x a) := rfl

theorem pi_adjunction_natural_source
    {X : Type u} {Y : Type v} {q : X → Y}
    {A : X → Type w} {B B' : Y → Type t}
    (h : FamilyHom (Pullback q B) A) (k : FamilyHom B' B)
    (y : Y) (b : B' y) (z : Fibre q y) :
    piTo (fun x b' => h x (k (q x) b')) y b z =
      piTo h y (k y b) z := by
  rcases z with ⟨x, hx⟩
  cases hx
  rfl

theorem pi_adjunction_natural_target
    {X : Type u} {Y : Type v} {q : X → Y}
    {A A' : X → Type w} {B : Y → Type t}
    (h : FamilyHom (Pullback q B) A) (k : FamilyHom A A')
    (y : Y) (b : B y) (z : Fibre q y) :
    piTo (fun x b' => k x (h x b')) y b z =
      piMap k y (piTo h y b) z := rfl

def sigmaUnit {X : Type u} {Y : Type v} {q : X → Y} (A : X → Type w) :
    FamilyHom A (Pullback q (SigmaPush q A)) :=
  fun x a => ⟨⟨x, rfl⟩, a⟩

def sigmaCounit {X : Type u} {Y : Type v} {q : X → Y} (B : Y → Type w) :
    FamilyHom (SigmaPush q (Pullback q B)) B :=
  sigmaFrom (fun _ b => b)

def piUnit {X : Type u} {Y : Type v} {q : X → Y} (B : Y → Type w) :
    FamilyHom B (PiPush q (Pullback q B)) :=
  piTo (fun _ b => b)

def piCounit {X : Type u} {Y : Type v} {q : X → Y} (A : X → Type w) :
    FamilyHom (Pullback q (PiPush q A)) A :=
  fun x h => h ⟨x, rfl⟩

theorem sigma_triangle_pullback {X : Type u} {Y : Type v} {q : X → Y}
    (B : Y → Type w) (x : X) (b : B (q x)) :
    sigmaCounit B (q x) (sigmaUnit (Pullback q B) x b) = b := rfl

theorem sigma_triangle_push {X : Type u} {Y : Type v} {q : X → Y}
    (A : X → Type w) (y : Y) (z : SigmaPush q A y) :
    sigmaCounit (SigmaPush q A) y
      (sigmaMap (sigmaUnit A) y z) = z := by
  rcases z with ⟨⟨x, h⟩, a⟩
  cases h
  rfl

theorem pi_triangle_pullback {X : Type u} {Y : Type v} {q : X → Y}
    (B : Y → Type w) (x : X) (b : B (q x)) :
    piCounit (Pullback q B) x (piUnit B (q x) b) = b := rfl

theorem pi_triangle_push {X : Type u} {Y : Type v} {q : X → Y}
    (A : X → Type w) (y : Y) (h : PiPush q A y) (z : Fibre q y) :
    piMap (piCounit A) y (piUnit (PiPush q A) y h) z = h z := by
  rcases z with ⟨x, hx⟩
  cases hx
  rfl

/-- The actual pullback consists of a new base point and an old fibre point. -/
abbrev PullbackObject {X : Type u} {Y : Type v} {Z : Type w}
    (q : X → Y) (f : Z → Y) :=
  (z : Z) × Fibre q (f z)

def pullbackLeft {X : Type u} {Y : Type v} {Z : Type w}
    {q : X → Y} {f : Z → Y} (e : PullbackObject q f) : Z := e.1

def pullbackRight {X : Type u} {Y : Type v} {Z : Type w}
    {q : X → Y} {f : Z → Y} (e : PullbackObject q f) : X := e.2.val

theorem pullback_square {X : Type u} {Y : Type v} {Z : Type w}
    {q : X → Y} {f : Z → Y} (e : PullbackObject q f) :
    q (pullbackRight e) = f (pullbackLeft e) := e.2.property

def sigmaBCTo {X : Type u} {Y : Type v} {Z : Type w}
    {q : X → Y} {f : Z → Y} {A : X → Type t}
    (z : Z) (a : SigmaPush q A (f z)) :
    SigmaPush (@pullbackLeft X Y Z q f) (fun e => A (pullbackRight e)) z :=
  ⟨⟨⟨z, a.1⟩, rfl⟩, a.2⟩

def sigmaBCFrom {X : Type u} {Y : Type v} {Z : Type w}
    {q : X → Y} {f : Z → Y} {A : X → Type t}
    (z : Z)
    (a : SigmaPush (@pullbackLeft X Y Z q f) (fun e => A (pullbackRight e)) z) :
    SigmaPush q A (f z) := by
  rcases a with ⟨⟨⟨z', x⟩, h⟩, a⟩
  change z' = z at h
  cases h
  exact ⟨x, a⟩

theorem sigma_bc_from_to {X : Type u} {Y : Type v} {Z : Type w}
    {q : X → Y} {f : Z → Y} {A : X → Type t}
    (z : Z) (a : SigmaPush q A (f z)) :
    sigmaBCFrom z (sigmaBCTo z a) = a := by
  cases a
  rfl

theorem sigma_bc_to_from {X : Type u} {Y : Type v} {Z : Type w}
    {q : X → Y} {f : Z → Y} {A : X → Type t}
    (z : Z)
    (a : SigmaPush (@pullbackLeft X Y Z q f) (fun e => A (pullbackRight e)) z) :
    sigmaBCTo z (sigmaBCFrom z a) = a := by
  rcases a with ⟨⟨⟨z', x⟩, h⟩, a⟩
  change z' = z at h
  cases h
  rfl

def piBCTo {X : Type u} {Y : Type v} {Z : Type w}
    {q : X → Y} {f : Z → Y} {A : X → Type t}
    (z : Z) (h : PiPush q A (f z)) :
    PiPush (@pullbackLeft X Y Z q f) (fun e => A (pullbackRight e)) z := by
  intro e
  rcases e with ⟨⟨z', x⟩, he⟩
  change z' = z at he
  cases he
  exact h x

def piBCFrom {X : Type u} {Y : Type v} {Z : Type w}
    {q : X → Y} {f : Z → Y} {A : X → Type t}
    (z : Z)
    (h : PiPush (@pullbackLeft X Y Z q f) (fun e => A (pullbackRight e)) z) :
    PiPush q A (f z) :=
  fun x => h ⟨⟨z, x⟩, rfl⟩

theorem pi_bc_from_to {X : Type u} {Y : Type v} {Z : Type w}
    {q : X → Y} {f : Z → Y} {A : X → Type t}
    (z : Z) (h : PiPush q A (f z)) (x : Fibre q (f z)) :
    piBCFrom z (piBCTo z h) x = h x := rfl

theorem pi_bc_to_from {X : Type u} {Y : Type v} {Z : Type w}
    {q : X → Y} {f : Z → Y} {A : X → Type t}
    (z : Z)
    (h : PiPush (@pullbackLeft X Y Z q f) (fun e => A (pullbackRight e)) z)
    (e : Fibre (@pullbackLeft X Y Z q f) z) :
    piBCTo z (piBCFrom z h) e = h e := by
  rcases e with ⟨⟨z', x⟩, he⟩
  change z' = z at he
  cases he
  rfl

/-- Constructive negation of the dependent sum, by explicit application. -/
def negateSigma {X : Type u} {A : X → Type v}
    (h : (x : X) × A x → False) : (x : X) → A x → False :=
  fun x a => h ⟨x, a⟩

def unNegateSigma {X : Type u} {A : X → Type v}
    (h : (x : X) → A x → False) : (x : X) × A x → False :=
  fun z => h z.1 z.2

theorem negate_sigma_pointwise {X : Type u} {A : X → Type v}
    (h : (x : X) → A x → False) (x : X) (a : A x) :
    negateSigma (unNegateSigma h) x a = h x a := rfl

theorem un_negate_sigma_pointwise {X : Type u} {A : X → Type v}
    (h : (x : X) × A x → False) (z : (x : X) × A x) :
    unNegateSigma (negateSigma h) z = h z := by
  cases z
  rfl

#print axioms sigma_to_from
#print axioms sigma_from_to
#print axioms pi_from_to
#print axioms pi_to_from
#print axioms sigma_triangle_pullback
#print axioms sigma_triangle_push
#print axioms pi_triangle_pullback
#print axioms pi_triangle_push
#print axioms sigma_bc_from_to
#print axioms sigma_bc_to_from
#print axioms pi_bc_from_to
#print axioms pi_bc_to_from
#print axioms negate_sigma_pointwise
#print axioms un_negate_sigma_pointwise

end ReversibleH24.Adjoints


/- Module: MatrixFrames -/

/- Concrete four-port matrices for control-one Fredkin/Toffoli.
   Matrix identities are pointwise; coefficients are exact natural 0/1.
   The same polynomial identities transport through any semiring morphism.
   Tail theorems quantify over an arbitrary retained tail type. -/

namespace ReversibleH24.Matrices

universe u

abbrev Port := Bool × Bool
abbrev Matrix4 := Port → Port → Nat

def sum4 (f : Port → Nat) : Nat :=
  f (false,false) + f (false,true) + f (true,false) + f (true,true)

def identity4 (row col : Port) : Nat := if row = col then 1 else 0

def permMatrix (p : Port → Port) (row col : Port) : Nat :=
  if row = p col then 1 else 0

def dagger (A : Matrix4) (row col : Port) : Nat := A col row
def multiply (A B : Matrix4) (row col : Port) : Nat :=
  sum4 (fun middle => A row middle * B middle col)

def toffoliPort (p : Port) : Port :=
  (p.1, ReversibleH24.toffoliThird true p.1 p.2)

def fredkinPort (p : Port) : Port :=
  (ReversibleH24.fredkinSecond true p.1 p.2,
   ReversibleH24.fredkinThird true p.1 p.2)

def T1 : Matrix4 := permMatrix toffoliPort
def F1 : Matrix4 := permMatrix fredkinPort
def FT : Matrix4 := multiply F1 T1

theorem toffoli_self_dagger (row col : Port) :
    dagger T1 row col = T1 row col := by
  rcases row with ⟨a,b⟩
  rcases col with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem fredkin_self_dagger (row col : Port) :
    dagger F1 row col = F1 row col := by
  rcases row with ⟨a,b⟩
  rcases col with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem toffoli_gram_identity (row col : Port) :
    multiply (dagger T1) T1 row col = identity4 row col := by
  rcases row with ⟨a,b⟩
  rcases col with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem fredkin_gram_identity (row col : Port) :
    multiply (dagger F1) F1 row col = identity4 row col := by
  rcases row with ⟨a,b⟩
  rcases col with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem product_gram_identity (row col : Port) :
    multiply (dagger FT) FT row col = identity4 row col := by
  rcases row with ⟨a,b⟩
  rcases col with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem fredkin_toffoli_order_three (row col : Port) :
    multiply FT (multiply FT FT) row col = identity4 row col := by
  rcases row with ⟨a,b⟩
  rcases col with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem fredkin_toffoli_not_involution :
    multiply FT FT ≠ identity4 := by
  intro h
  have bad : 0 = 1 :=
    congrArg (fun A => A (false,true) (false,true)) h
  cases bad

def nz (n : Nat) : Nat := if n = 0 then 0 else 1
def nonzeros (A : Matrix4) : Nat := sum4 (fun row => sum4 (fun col => nz (A row col)))

theorem toffoli_four_nonzeros : nonzeros T1 = 4 := rfl
theorem fredkin_four_nonzeros : nonzeros F1 = 4 := rfl
theorem product_four_nonzeros : nonzeros FT = 4 := rfl

def toffoliTail {R : Type u} : Bool × Bool × Bool × R → Bool × Bool × Bool × R
  | ⟨a,b,c,r⟩ => ⟨a,b,ReversibleH24.toffoliThird a b c,r⟩

def fredkinTail {R : Type u} : Bool × Bool × Bool × R → Bool × Bool × Bool × R
  | ⟨a,b,c,r⟩ =>
    ⟨a,ReversibleH24.fredkinSecond a b c,ReversibleH24.fredkinThird a b c,r⟩

theorem toffoli_all_tail_return {R : Type u} (s : Bool × Bool × Bool × R) :
    toffoliTail (toffoliTail s) = s := by
  rcases s with ⟨a,b,c,r⟩
  cases a <;> cases b <;> cases c <;> rfl

theorem fredkin_all_tail_return {R : Type u} (s : Bool × Bool × Bool × R) :
    fredkinTail (fredkinTail s) = s := by
  rcases s with ⟨a,b,c,r⟩
  cases a <;> cases b <;> cases c <;> rfl

theorem toffoli_retains_original_tail {R : Type u} (s : Bool × Bool × Bool × R) :
    (toffoliTail s).2.2.2 = s.2.2.2 := by
  rcases s with ⟨a,b,c,r⟩
  rfl

theorem fredkin_retains_original_tail {R : Type u} (s : Bool × Bool × Bool × R) :
    (fredkinTail s).2.2.2 = s.2.2.2 := by
  rcases s with ⟨a,b,c,r⟩
  rfl

#print axioms toffoli_gram_identity
#print axioms fredkin_gram_identity
#print axioms product_gram_identity
#print axioms fredkin_toffoli_order_three
#print axioms fredkin_toffoli_not_involution
#print axioms toffoli_all_tail_return
#print axioms fredkin_all_tail_return

end ReversibleH24.Matrices


/- Module: ScalarReceivers -/
/- Exact receivers for certified scalar ranges.
   a and d are nonnegative integers and d > 0.
   The represented read is a/(s*d), where s is 8,160,16,8 respectively.
   This file proves the receivers from explicit range evidence.
   It does not assume or claim an efficient acquisition of that evidence. -/

namespace ReversibleH24.Scalars

def test (p : Prop) [Decidable p] : Bool := decide p

theorem test_true (p : Prop) (D : Decidable p) (h : p) :
    @test p D = true := by
  cases D with
  | isTrue yes => rfl
  | isFalse no => exact False.elim (no h)

theorem test_false (p : Prop) (D : Decidable p) (h : ¬ p) :
    @test p D = false := by
  cases D with
  | isTrue yes => exact False.elim (h yes)
  | isFalse no => rfl

def above (a threshold : Nat) : Bool := test (threshold < a)
def below (a threshold : Nat) : Bool := test (a < threshold)

theorem above_from_lower {a threshold lower : Nat}
    (gap : threshold < lower) (bound : lower ≤ a) :
    above a threshold = true :=
  test_true _ _ (Nat.lt_of_lt_of_le gap bound)

theorem above_from_upper {a threshold upper : Nat}
    (gap : upper ≤ threshold) (bound : a ≤ upper) :
    above a threshold = false :=
  test_false _ _ (Nat.not_lt_of_ge (Nat.le_trans bound gap))

theorem below_from_upper {a threshold upper : Nat}
    (gap : upper < threshold) (bound : a ≤ upper) :
    below a threshold = true :=
  test_true _ _ (Nat.lt_of_le_of_lt bound gap)

theorem below_from_lower {a threshold lower : Nat}
    (gap : threshold ≤ lower) (bound : lower ≤ a) :
    below a threshold = false :=
  test_false _ _ (Nat.not_lt_of_ge (Nat.le_trans gap bound))

def tower (a d : Nat) : Bool := above a (13*d)
def bayes (a d : Nat) : Bool := above a (85*d)
def fredkin (a d : Nat) : Bool := above a (2*d)
def freeEnergy (a d : Nat) : Bool := below a (4*d)

theorem tower_sat {a d : Nat} (positive : 0 < d) (range : 14*d ≤ a) :
    tower a d = true :=
  above_from_lower (Nat.mul_lt_mul_of_pos_right (by decide : 13 < 14) positive) range

theorem tower_unsat {a d : Nat} (range : a ≤ 12*d) :
    tower a d = false :=
  above_from_upper (Nat.mul_le_mul_right d (by decide : 12 ≤ 13)) range

theorem bayes_sat {a d : Nat} (positive : 0 < d) (range : 88*d ≤ a) :
    bayes a d = true :=
  above_from_lower (Nat.mul_lt_mul_of_pos_right (by decide : 85 < 88) positive) range

theorem bayes_unsat {a d : Nat} (range : a ≤ 80*d) :
    bayes a d = false :=
  above_from_upper (Nat.mul_le_mul_right d (by decide : 80 ≤ 85)) range

theorem fredkin_sat {a d : Nat} (positive : 0 < d) (range : 3*d ≤ a) :
    fredkin a d = true :=
  above_from_lower (Nat.mul_lt_mul_of_pos_right (by decide : 2 < 3) positive) range

theorem fredkin_unsat {a d : Nat} (range : a ≤ d) :
    fredkin a d = false := by
  have h : a ≤ 1*d := Eq.mpr (congrArg (fun x => a ≤ x) (Nat.one_mul d)) range
  exact above_from_upper (Nat.mul_le_mul_right d (by decide : 1 ≤ 2)) h

theorem freeEnergy_sat {a d : Nat} (positive : 0 < d) (range : a ≤ d) :
    freeEnergy a d = true := by
  have h : a ≤ 1*d := Eq.mpr (congrArg (fun x => a ≤ x) (Nat.one_mul d)) range
  exact below_from_upper
    (Nat.mul_lt_mul_of_pos_right (by decide : 1 < 4) positive) h

theorem freeEnergy_unsat {a d : Nat} (range : 6*d ≤ a) :
    freeEnergy a d = false :=
  below_from_lower (Nat.mul_le_mul_right d (by decide : 4 ≤ 6)) range

end ReversibleH24.Scalars

#print axioms ReversibleH24.Scalars.test_true
#print axioms ReversibleH24.Scalars.test_false
#print axioms ReversibleH24.Scalars.above_from_lower
#print axioms ReversibleH24.Scalars.above_from_upper
#print axioms ReversibleH24.Scalars.below_from_upper
#print axioms ReversibleH24.Scalars.below_from_lower
#print axioms ReversibleH24.Scalars.tower_sat
#print axioms ReversibleH24.Scalars.tower_unsat
#print axioms ReversibleH24.Scalars.bayes_sat
#print axioms ReversibleH24.Scalars.bayes_unsat
#print axioms ReversibleH24.Scalars.fredkin_sat
#print axioms ReversibleH24.Scalars.fredkin_unsat
#print axioms ReversibleH24.Scalars.freeEnergy_sat
#print axioms ReversibleH24.Scalars.freeEnergy_unsat


/- Module: DeadlineCounts -/

/- Original missed-port counts and their all-length zero criterion.
   The finite record enumerations, original-model bits, and actual checked-hit
   bits are explicit input data. This is the coefficient-level criterion for
   the original square-block Xi; no polynomial producer is assumed. -/
namespace ReversibleH24.Deadlines
open Hilbert24Policy

def missed : Bool → Bool → Nat
  | true, false => 1
  | _, _ => 0

theorem missed_zero_iff (v h : Bool) :
    missed v h = 0 ↔ (v = true → h = true) := by
  cases v <;> cases h
  · exact ⟨(fun _ hv => by cases hv), (fun _ => rfl)⟩
  · exact ⟨(fun _ _ => rfl), (fun _ => rfl)⟩
  · exact ⟨(fun hz => by cases hz), (fun f => by have bad := f rfl; cases bad)⟩
  · exact ⟨(fun _ _ => rfl), (fun _ => rfl)⟩

theorem sum_zero_from_components {n : Nat} (f : Fin n → Nat)
    (h : ∀ i, f i = 0) : sumFin f = 0 :=
  (sumFin_congr f (fun _ => 0) h).trans sumFin_zero

def rowCount {m : Nat} (model : Fin m → Bool) (hit : Bool) : Nat :=
  sumFin (fun a => missed (model a) hit)

theorem row_zero_iff {m : Nat} (model : Fin m → Bool) (hit : Bool) :
    rowCount model hit = 0 ↔ ∀ a, model a = true → hit = true := by
  constructor
  · intro h a
    exact (missed_zero_iff (model a) hit).mp (sumFin_zero_imp _ h a)
  · intro h
    exact sum_zero_from_components _ (fun a => (missed_zero_iff _ _).mpr (h a))

def blockCount {n m : Nat} (model : Fin n → Fin m → Bool)
    (hit : Fin n → Bool) : Nat :=
  sumFin (fun c => rowCount (model c) (hit c))

theorem block_zero_iff {n m : Nat} (model : Fin n → Fin m → Bool)
    (hit : Fin n → Bool) :
    blockCount model hit = 0 ↔ ∀ c a, model c a = true → hit c = true := by
  constructor
  · intro h c
    exact (row_zero_iff _ _).mp (sumFin_zero_imp _ h c)
  · intro h
    exact sum_zero_from_components _ (fun c => (row_zero_iff _ _).mpr (h c))

structure DeadlineData where
  records : Nat → Nat
  assignments : Nat → Nat
  originalModel : (length : Nat) → Fin (records length) → Fin (assignments length) → Bool
  checkedHit : (length : Nat) → Fin (records length) → Bool

def coefficient (D : DeadlineData) (length : Nat) : Nat :=
  blockCount (D.originalModel length) (D.checkedHit length)

theorem all_lengths_zero_iff (D : DeadlineData) :
    (∀ length, coefficient D length = 0) ↔
    (∀ length c a, D.originalModel length c a = true →
      D.checkedHit length c = true) := by
  constructor
  · intro h length
    exact (block_zero_iff _ _).mp (h length)
  · intro h length
    exact (block_zero_iff _ _).mpr (h length)

end ReversibleH24.Deadlines

#print axioms ReversibleH24.Deadlines.missed_zero_iff
#print axioms ReversibleH24.Deadlines.sum_zero_from_components
#print axioms ReversibleH24.Deadlines.row_zero_iff
#print axioms ReversibleH24.Deadlines.block_zero_iff
#print axioms ReversibleH24.Deadlines.all_lengths_zero_iff


/- Module: CechContraction -/
/- Constructive extra degeneracy of the augmented Cech nerve.
   A vector is an ordinary word together with its exact length certificate.
   This representation retains every degree and every label. All operations
   recurse on words; valid face/degeneracy indices carry their finite bounds.
   The chosen failed label is explicit section data, never selected by choice. -/

namespace ReversibleH24.Cech
universe u v

inductive Word (A : Type u) : Type u
  | nil : Word A
  | cons : A → Word A → Word A

def length {A : Type u} : Word A → Nat
  | .nil => 0
  | .cons _ xs => Nat.succ (length xs)

abbrev Index (n : Nat) := Fin n
abbrev Vec (A : Type u) (n : Nat) := {xs : Word A // length xs = n}

def zeroIndex (n : Nat) : Index (n+1) := ⟨0, Nat.zero_lt_succ n⟩

def deleteLabel {A : Type u} : Nat → Word A → Word A
  | _, .nil => .nil
  | 0, .cons _ xs => xs
  | k+1, .cons x xs => .cons x (deleteLabel k xs)

def duplicateLabel {A : Type u} : Nat → Word A → Word A
  | _, .nil => .nil
  | 0, .cons x xs => .cons x (.cons x xs)
  | k+1, .cons x xs => .cons x (duplicateLabel k xs)

theorem delete_length {A : Type u} :
    (k : Nat) → (xs : Word A) → k < length xs →
      Nat.succ (length (deleteLabel k xs)) = length xs
  | _, .nil, h => by cases h
  | 0, .cons _ _, _ => rfl
  | k+1, .cons _ xs, h =>
    congrArg Nat.succ (delete_length k xs (Nat.lt_of_succ_lt_succ h))

theorem duplicate_length {A : Type u} :
    (k : Nat) → (xs : Word A) → k < length xs →
      length (duplicateLabel k xs) = Nat.succ (length xs)
  | _, .nil, h => by cases h
  | 0, .cons _ _, _ => rfl
  | k+1, .cons _ xs, h =>
    congrArg Nat.succ (duplicate_length k xs (Nat.lt_of_succ_lt_succ h))

def face {A : Type u} {n : Nat} (i : Index (n+1))
    (xs : Vec A (n+1)) : Vec A n :=
  ⟨deleteLabel i.val xs.val,
    Nat.succ.inj
      ((delete_length i.val xs.val
        (Eq.mpr (congrArg (fun k => i.val < k) xs.property) i.isLt)).trans
          xs.property)⟩

def duplicate {A : Type u} {n : Nat} (i : Index (n+1))
    (xs : Vec A (n+1)) : Vec A (n+2) :=
  ⟨duplicateLabel i.val xs.val,
    (duplicate_length i.val xs.val
      (Eq.mpr (congrArg (fun k => i.val < k) xs.property) i.isLt)).trans
        (congrArg Nat.succ xs.property)⟩

def cone {A : Type u} (chosen : A) {n : Nat}
    (xs : Vec A n) : Vec A (n+1) :=
  ⟨.cons chosen xs.val, congrArg Nat.succ xs.property⟩

theorem face_zero_cone {A : Type u} (chosen : A) {n : Nat} (xs : Vec A n) :
    face (zeroIndex n) (cone chosen xs) = xs := rfl

theorem face_succ_cone {A : Type u} (chosen : A) {n : Nat}
    (i : Index (n+1)) (xs : Vec A (n+1)) :
    face i.succ (cone chosen xs) = cone chosen (face i xs) := rfl

theorem repeat_zero_cone {A : Type u} (chosen : A) {n : Nat} (xs : Vec A n) :
    duplicate (zeroIndex n) (cone chosen xs) = cone chosen (cone chosen xs) := rfl

theorem repeat_succ_cone {A : Type u} (chosen : A) {n : Nat}
    (i : Index (n+1)) (xs : Vec A (n+1)) :
    duplicate i.succ (cone chosen xs) = cone chosen (duplicate i xs) := rfl

def head {A : Type u} : (xs : Word A) → 0 < length xs → A
  | .nil, h => by
      have impossible : False := by cases h
      exact False.elim impossible
  | .cons x _, _ => x

def vertex {A : Type u} (xs : Vec A 1) : A :=
  head xs.val
    (Eq.mpr (congrArg (fun k => 0 < k) xs.property) (Nat.zero_lt_succ 0))

def no_vertex_of_empty {A : Type u} (empty : A → False) (xs : Vec A 1) : False :=
  empty (vertex xs)

def fibreCone {Base : Type u} (Failure : Base → Type v)
    (chosenLabel : (x : Base) → Failure x) (x : Base) {n : Nat}
    (xs : Vec (Failure x) n) : Vec (Failure x) (n+1) :=
  cone (chosenLabel x) xs

theorem fibre_contraction_return {Base : Type u} (Failure : Base → Type v)
    (chosenLabel : (x : Base) → Failure x) (x : Base) {n : Nat}
    (xs : Vec (Failure x) n) :
    face (zeroIndex n) (fibreCone Failure chosenLabel x xs) = xs := rfl

end ReversibleH24.Cech

#print axioms ReversibleH24.Cech.delete_length
#print axioms ReversibleH24.Cech.duplicate_length
#print axioms ReversibleH24.Cech.face
#print axioms ReversibleH24.Cech.duplicate
#print axioms ReversibleH24.Cech.face_zero_cone
#print axioms ReversibleH24.Cech.face_succ_cone
#print axioms ReversibleH24.Cech.repeat_zero_cone
#print axioms ReversibleH24.Cech.repeat_succ_cone
#print axioms ReversibleH24.Cech.no_vertex_of_empty
#print axioms ReversibleH24.Cech.fibre_contraction_return


/- Module: BelnapEvidence -/
/- The two evidence channels of Belnap FOUR remain independent data.
   Negation exchanges the channels; both and neither are retained.
   This is the finite evidence representation, not an imported proof system. -/
namespace ReversibleH24.Belnap

abbrev FOUR := Bool × Bool

def neither : FOUR := (false, false)
def positive : FOUR := (true, false)
def negative : FOUR := (false, true)
def both : FOUR := (true, true)

def determinateNegation (e : FOUR) : FOUR := (e.2, e.1)

theorem negation_involution (e : FOUR) :
    determinateNegation (determinateNegation e) = e := by
  cases e
  rfl

theorem neither_fixed : determinateNegation neither = neither := rfl
theorem both_fixed : determinateNegation both = both := rfl
theorem positive_to_negative : determinateNegation positive = negative := rfl
theorem negative_to_positive : determinateNegation negative = positive := rfl

theorem both_distinct_from_neither : both ≠ neither := by
  intro h
  have impossible : true = false := congrArg Prod.fst h
  cases impossible

end ReversibleH24.Belnap

#print axioms ReversibleH24.Belnap.negation_involution
#print axioms ReversibleH24.Belnap.neither_fixed
#print axioms ReversibleH24.Belnap.both_fixed
#print axioms ReversibleH24.Belnap.both_distinct_from_neither


/- Complete declaration dependency report. -/
#print axioms Hilbert24Policy.sumFin
#print axioms Hilbert24Policy.sumFin_congr
#print axioms Hilbert24Policy.sumFin_add
#print axioms Hilbert24Policy.sumFin_zero
#print axioms Hilbert24Policy.work
#print axioms Hilbert24Policy.totalSlack
#print axioms Hilbert24Policy.stokes
#print axioms Hilbert24Policy.global_lower_bound
#print axioms Hilbert24Policy.add_sub_of_le_constructive
#print axioms Hilbert24Policy.calibrationFromFeasible
#print axioms Hilbert24Policy.build
#print axioms Hilbert24Policy.totalSlack_transport
#print axioms Hilbert24Policy.build_has_zero_slack
#print axioms Hilbert24Policy.build_attains
#print axioms Hilbert24Policy.build_is_global_minimum
#print axioms Hilbert24Policy.IsGlobalMinimum
#print axioms Hilbert24Policy.cancel_add_le_left
#print axioms Hilbert24Policy.minimum_iff_zero_slack
#print axioms Hilbert24Policy.add_eq_zero_parts
#print axioms Hilbert24Policy.sumFin_zero_imp
#print axioms Hilbert24Policy.allTight
#print axioms Hilbert24Policy.zero_slack_iff_allTight
#print axioms Hilbert24Policy.complete_minimum_fibre
#print axioms Hilbert24Policy.constructMinimum
#print axioms Hilbert24Policy.interpret
#print axioms Hilbert24Policy.returnOriginal
#print axioms Hilbert24Policy.chainSystem
#print axioms Hilbert24Policy.chainCalibration
#print axioms Hilbert24Policy.chainPolicy
#print axioms Hilbert24Policy.chain_all_inputs
#print axioms Hilbert24Policy.chainLoopProof
#print axioms Hilbert24Policy.chainLoop_is_also_minimum
#print axioms Hilbert24Policy.chain_example_25
#print axioms ReversibleH24.orig
#print axioms ReversibleH24.reduced
#print axioms ReversibleH24.toffoliThird
#print axioms ReversibleH24.fredkinSecond
#print axioms ReversibleH24.fredkinThird
#print axioms ReversibleH24.zero_branch
#print axioms ReversibleH24.one_branch
#print axioms ReversibleH24.finite_exists_exact
#print axioms ReversibleH24.chosen_lift_exact
#print axioms ReversibleH24.projection_sound
#print axioms ReversibleH24.bool_or_false
#print axioms ReversibleH24.finite_refuter_exact
#print axioms ReversibleH24.projection_can_have_two_witnesses
#print axioms ReversibleH24.toffoli_involution
#print axioms ReversibleH24.fredkin_second_return
#print axioms ReversibleH24.fredkin_third_return
#print axioms ReversibleH24.OriginalModel
#print axioms ReversibleH24.ReducedModel
#print axioms ReversibleH24.projectModel
#print axioms ReversibleH24.liftModel
#print axioms ReversibleH24.project_lift
#print axioms ReversibleH24.refuteOriginal
#print axioms ReversibleH24.refuteReduced
#print axioms ReversibleH24.additive_nonnegative_groupoid_clock_vanishes
#print axioms ReversibleH24.fixedpoint_has_no_distinct_incoming_state
#print axioms ReversibleH24.Timed
#print axioms ReversibleH24.timedCompose
#print axioms ReversibleH24.timedDagger
#print axioms ReversibleH24.dagger_preserves_paid_work
#print axioms ReversibleH24.reversible_roundtrip_charged
#print axioms ReversibleH24.dagger_twice
#print axioms ReversibleH24.accumulated
#print axioms ReversibleH24.h24_frontier_slack_balance
#print axioms ReversibleH24.natural_balance_telescope
#print axioms ReversibleH24.prefix_paid_bound
#print axioms ReversibleH24.positive_steps_count
#print axioms ReversibleH24.prefix_length_bound
#print axioms ReversibleH24.no_prefix_beyond_budget
#print axioms ReversibleH24.two_step_balance
#print axioms ReversibleH24.nat_cancel_right
#print axioms ReversibleH24.closed_path_paid_balance
#print axioms ReversibleH24.equal_potential_preserves_cost
#print axioms ReversibleH24.Adjoints.FamilyHom
#print axioms ReversibleH24.Adjoints.Pullback
#print axioms ReversibleH24.Adjoints.Fibre
#print axioms ReversibleH24.Adjoints.SigmaPush
#print axioms ReversibleH24.Adjoints.PiPush
#print axioms ReversibleH24.Adjoints.sigmaTo
#print axioms ReversibleH24.Adjoints.sigmaFrom
#print axioms ReversibleH24.Adjoints.sigma_to_from
#print axioms ReversibleH24.Adjoints.sigma_from_to
#print axioms ReversibleH24.Adjoints.piTo
#print axioms ReversibleH24.Adjoints.piFrom
#print axioms ReversibleH24.Adjoints.pi_from_to
#print axioms ReversibleH24.Adjoints.pi_to_from
#print axioms ReversibleH24.Adjoints.sigmaAdjunction
#print axioms ReversibleH24.Adjoints.piAdjunction
#print axioms ReversibleH24.Adjoints.sigmaMap
#print axioms ReversibleH24.Adjoints.piMap
#print axioms ReversibleH24.Adjoints.sigma_map_identity
#print axioms ReversibleH24.Adjoints.pi_map_identity
#print axioms ReversibleH24.Adjoints.sigma_map_composition
#print axioms ReversibleH24.Adjoints.pi_map_composition
#print axioms ReversibleH24.Adjoints.sigma_adjunction_natural_source
#print axioms ReversibleH24.Adjoints.sigma_adjunction_natural_target
#print axioms ReversibleH24.Adjoints.pi_adjunction_natural_source
#print axioms ReversibleH24.Adjoints.pi_adjunction_natural_target
#print axioms ReversibleH24.Adjoints.sigmaUnit
#print axioms ReversibleH24.Adjoints.sigmaCounit
#print axioms ReversibleH24.Adjoints.piUnit
#print axioms ReversibleH24.Adjoints.piCounit
#print axioms ReversibleH24.Adjoints.sigma_triangle_pullback
#print axioms ReversibleH24.Adjoints.sigma_triangle_push
#print axioms ReversibleH24.Adjoints.pi_triangle_pullback
#print axioms ReversibleH24.Adjoints.pi_triangle_push
#print axioms ReversibleH24.Adjoints.PullbackObject
#print axioms ReversibleH24.Adjoints.pullbackLeft
#print axioms ReversibleH24.Adjoints.pullbackRight
#print axioms ReversibleH24.Adjoints.pullback_square
#print axioms ReversibleH24.Adjoints.sigmaBCTo
#print axioms ReversibleH24.Adjoints.sigmaBCFrom
#print axioms ReversibleH24.Adjoints.sigma_bc_from_to
#print axioms ReversibleH24.Adjoints.sigma_bc_to_from
#print axioms ReversibleH24.Adjoints.piBCTo
#print axioms ReversibleH24.Adjoints.piBCFrom
#print axioms ReversibleH24.Adjoints.pi_bc_from_to
#print axioms ReversibleH24.Adjoints.pi_bc_to_from
#print axioms ReversibleH24.Adjoints.negateSigma
#print axioms ReversibleH24.Adjoints.unNegateSigma
#print axioms ReversibleH24.Adjoints.negate_sigma_pointwise
#print axioms ReversibleH24.Adjoints.un_negate_sigma_pointwise
#print axioms ReversibleH24.Matrices.Port
#print axioms ReversibleH24.Matrices.Matrix4
#print axioms ReversibleH24.Matrices.sum4
#print axioms ReversibleH24.Matrices.identity4
#print axioms ReversibleH24.Matrices.permMatrix
#print axioms ReversibleH24.Matrices.dagger
#print axioms ReversibleH24.Matrices.multiply
#print axioms ReversibleH24.Matrices.toffoliPort
#print axioms ReversibleH24.Matrices.fredkinPort
#print axioms ReversibleH24.Matrices.T1
#print axioms ReversibleH24.Matrices.F1
#print axioms ReversibleH24.Matrices.FT
#print axioms ReversibleH24.Matrices.toffoli_self_dagger
#print axioms ReversibleH24.Matrices.fredkin_self_dagger
#print axioms ReversibleH24.Matrices.toffoli_gram_identity
#print axioms ReversibleH24.Matrices.fredkin_gram_identity
#print axioms ReversibleH24.Matrices.product_gram_identity
#print axioms ReversibleH24.Matrices.fredkin_toffoli_order_three
#print axioms ReversibleH24.Matrices.fredkin_toffoli_not_involution
#print axioms ReversibleH24.Matrices.nz
#print axioms ReversibleH24.Matrices.nonzeros
#print axioms ReversibleH24.Matrices.toffoli_four_nonzeros
#print axioms ReversibleH24.Matrices.fredkin_four_nonzeros
#print axioms ReversibleH24.Matrices.product_four_nonzeros
#print axioms ReversibleH24.Matrices.toffoliTail
#print axioms ReversibleH24.Matrices.fredkinTail
#print axioms ReversibleH24.Matrices.toffoli_all_tail_return
#print axioms ReversibleH24.Matrices.fredkin_all_tail_return
#print axioms ReversibleH24.Matrices.toffoli_retains_original_tail
#print axioms ReversibleH24.Matrices.fredkin_retains_original_tail
#print axioms ReversibleH24.Scalars.test
#print axioms ReversibleH24.Scalars.test_true
#print axioms ReversibleH24.Scalars.test_false
#print axioms ReversibleH24.Scalars.above
#print axioms ReversibleH24.Scalars.below
#print axioms ReversibleH24.Scalars.above_from_lower
#print axioms ReversibleH24.Scalars.above_from_upper
#print axioms ReversibleH24.Scalars.below_from_upper
#print axioms ReversibleH24.Scalars.below_from_lower
#print axioms ReversibleH24.Scalars.tower
#print axioms ReversibleH24.Scalars.bayes
#print axioms ReversibleH24.Scalars.fredkin
#print axioms ReversibleH24.Scalars.freeEnergy
#print axioms ReversibleH24.Scalars.tower_sat
#print axioms ReversibleH24.Scalars.tower_unsat
#print axioms ReversibleH24.Scalars.bayes_sat
#print axioms ReversibleH24.Scalars.bayes_unsat
#print axioms ReversibleH24.Scalars.fredkin_sat
#print axioms ReversibleH24.Scalars.fredkin_unsat
#print axioms ReversibleH24.Scalars.freeEnergy_sat
#print axioms ReversibleH24.Scalars.freeEnergy_unsat
#print axioms ReversibleH24.Deadlines.missed
#print axioms ReversibleH24.Deadlines.missed_zero_iff
#print axioms ReversibleH24.Deadlines.sum_zero_from_components
#print axioms ReversibleH24.Deadlines.rowCount
#print axioms ReversibleH24.Deadlines.row_zero_iff
#print axioms ReversibleH24.Deadlines.blockCount
#print axioms ReversibleH24.Deadlines.block_zero_iff
#print axioms ReversibleH24.Deadlines.coefficient
#print axioms ReversibleH24.Deadlines.all_lengths_zero_iff
#print axioms ReversibleH24.Cech.length
#print axioms ReversibleH24.Cech.Index
#print axioms ReversibleH24.Cech.Vec
#print axioms ReversibleH24.Cech.zeroIndex
#print axioms ReversibleH24.Cech.deleteLabel
#print axioms ReversibleH24.Cech.duplicateLabel
#print axioms ReversibleH24.Cech.delete_length
#print axioms ReversibleH24.Cech.duplicate_length
#print axioms ReversibleH24.Cech.face
#print axioms ReversibleH24.Cech.duplicate
#print axioms ReversibleH24.Cech.cone
#print axioms ReversibleH24.Cech.face_zero_cone
#print axioms ReversibleH24.Cech.face_succ_cone
#print axioms ReversibleH24.Cech.repeat_zero_cone
#print axioms ReversibleH24.Cech.repeat_succ_cone
#print axioms ReversibleH24.Cech.head
#print axioms ReversibleH24.Cech.vertex
#print axioms ReversibleH24.Cech.no_vertex_of_empty
#print axioms ReversibleH24.Cech.fibreCone
#print axioms ReversibleH24.Cech.fibre_contraction_return
#print axioms ReversibleH24.Belnap.FOUR
#print axioms ReversibleH24.Belnap.neither
#print axioms ReversibleH24.Belnap.positive
#print axioms ReversibleH24.Belnap.negative
#print axioms ReversibleH24.Belnap.both
#print axioms ReversibleH24.Belnap.determinateNegation
#print axioms ReversibleH24.Belnap.negation_involution
#print axioms ReversibleH24.Belnap.neither_fixed
#print axioms ReversibleH24.Belnap.both_fixed
#print axioms ReversibleH24.Belnap.positive_to_negative
#print axioms ReversibleH24.Belnap.negative_to_positive
#print axioms ReversibleH24.Belnap.both_distinct_from_neither

/- Simultaneous extension of the recovered ReversibleH24.lean.
   New source: written against Lean 4.19 core, not kernel-replayed in this session.
   The executable Python companion supplies and independently checks finite
   Bellman certificates. No global SAT policy or polynomial oracle is axiomatized.
-/
namespace H24Simultaneous
open Hilbert24Policy
universe u v w

/-- Each premise contribution is bounded by the sum of all occurrences. -/
theorem component_le_sum {n : Nat} (f : Fin n → Nat) (i : Fin n) :
    f i ≤ sumFin f := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases i with
      | mk k hk =>
          cases k with
          | zero => exact Nat.le_add_right _ _
          | succ k =>
              change f ⟨k+1,hk⟩ ≤ f ⟨0,Nat.zero_lt_succ n⟩ + sumFin (fun t => f t.succ)
              have h := ih (fun t => f t.succ) ⟨k,Nat.lt_of_succ_lt_succ hk⟩
              exact Nat.le_trans h (Nat.le_add_left _ _)

/-- Positive prices make the optimal potential itself a termination rank.
    No second rank supplier is needed. -/
def policyFromPositiveTight {J : Type u} {S : RuleSystem.{u,v} J}
    (V : Calibration S)
    (positive : ∀ r, 0 < S.charge r)
    (chosen : (j : J) → {r : S.Rule // S.conclusion r = j})
    (tight : ∀ j, V.slack (chosen j).val = 0) : TightPolicy S V where
  chosen := chosen
  tight := tight
  rank := V.potential
  decrease j i := by
    let r := (chosen j).val
    have h : S.charge r + sumFin (fun k => V.potential (S.premise r k)) = V.potential j := by
      have hh := V.local_identity r
      have hc : S.conclusion r = j := (chosen j).property
      have hz : V.slack r = 0 := tight j
      rw [hc, hz, Nat.add_zero] at hh
      exact hh
    have hle := component_le_sum (fun k => V.potential (S.premise r k)) i
    have hs : sumFin (fun k => V.potential (S.premise r k)) <
        S.charge r + sumFin (fun k => V.potential (S.premise r k)) := by
      have hp := positive r
      omega
    change V.potential (S.premise r i) < V.potential j
    rw [← h]
    exact Nat.lt_of_le_of_lt hle hs

/-- Feasibility means precisely the Bellman linear inequalities. -/
def BellmanFeasible {J : Type u} (S : RuleSystem.{u,v} J) (x : J → Nat) : Prop :=
  ∀ r, x (S.conclusion r) ≤ S.charge r + sumFin (fun i => x (S.premise r i))

/-- A feasible potential, with an attained tight policy, is the greatest
    feasible potential, not merely a locally stationary one. -/
theorem greatestFeasible {J : Type u} {S : RuleSystem.{u,v} J}
    (V : Calibration S) (P : TightPolicy S V) (x : J → Nat)
    (hx : BellmanFeasible S x) (j : J) : x j ≤ V.potential j := by
  let X := calibrationFromFeasible S x hx
  calc
    x j ≤ work (build P j) := global_lower_bound X (build P j)
    _ = V.potential j := build_attains P j

/-- An explicit finite rule scanner. The original rule and tightness proof
    are returned, not just a Boolean answer. -/
def TightRule {J : Type u} {S : RuleSystem.{u,v} J} (V : Calibration S) (j : J) :=
  {r : S.Rule // S.conclusion r = j ∧ V.slack r = 0}

def scanTight {J : Type u} [DecidableEq J] {S : RuleSystem.{u,v} J}
    (V : Calibration S) (j : J) : List S.Rule → Option (TightRule V j)
  | [] => none
  | r :: rs =>
      if h : S.conclusion r = j ∧ V.slack r = 0 then some ⟨r,h⟩
      else scanTight V j rs

theorem scanTight_no_hit {J : Type u} [DecidableEq J] {S : RuleSystem.{u,v} J}
    (V : Calibration S) (j : J) (rs : List S.Rule)
    (h : scanTight V j rs = none) (r : S.Rule) (hr : r ∈ rs) :
    ¬ (S.conclusion r = j ∧ V.slack r = 0) := by
  induction rs with
  | nil => simp at hr
  | cons a rs ih =>
      by_cases ha : S.conclusion a = j ∧ V.slack a = 0
      · simp [scanTight, ha] at h
      · have ht : scanTight V j rs = none := by simpa [scanTight, ha] using h
        rcases List.mem_cons.mp hr with he | he
        · subst r; exact ha
        · exact ih ht he

/-- A scan can be turned into an executable choice whenever finite coverage
    is proved. The proof is erased, not an oracle supplied to the executor. -/
def selectTight {J : Type u} [DecidableEq J] {S : RuleSystem.{u,v} J}
    (V : Calibration S) (rs : List S.Rule) (j : J)
    (covered : ∃ r, r ∈ rs ∧ S.conclusion r = j ∧ V.slack r = 0) : TightRule V j :=
  match h : scanTight V j rs with
  | some r => r
  | none => False.elim (by
      obtain ⟨r,hm,ht⟩ := covered
      exact scanTight_no_hit V j rs h r hm ht)

def scannedPolicy {J : Type u} [DecidableEq J] {S : RuleSystem.{u,v} J}
    (V : Calibration S) (rs : List S.Rule) (positive : ∀ r, 0 < S.charge r)
    (covered : ∀ j, ∃ r, r ∈ rs ∧ S.conclusion r = j ∧ V.slack r = 0) :
    TightPolicy S V :=
  policyFromPositiveTight V positive
    (fun j => ⟨(selectTight V rs j (covered j)).val,
      (selectTight V rs j (covered j)).property.left⟩)
    (fun j => (selectTight V rs j (covered j)).property.right)

/-- Simultaneously return the source proof, exact grade, and global minimum. -/
def constructFromBellman {J : Type u} [DecidableEq J] {S : RuleSystem.{u,v} J}
    (x : J → Nat) (hx : BellmanFeasible S x) (rs : List S.Rule)
    (positive : ∀ r, 0 < S.charge r)
    (covered : ∀ j, ∃ r, r ∈ rs ∧ S.conclusion r = j ∧
      (calibrationFromFeasible S x hx).slack r = 0) (j : J) :
    OptimalReturn S (calibrationFromFeasible S x hx) j :=
  constructMinimum (scannedPolicy (calibrationFromFeasible S x hx) rs positive covered) j

/-- The explicit Bellman fold. The table is materialized, rather than a
    recursively nested function that would recompute all previous entries.
    `none` represents infinity. Caller supplies the literal finite lists.
    The separate mathematical argument proves that N rounds suffice for N
    distinct judgments and positive charges; the Python checker independently
    verifies the final Bellman and tight-policy conditions. -/
abbrev ValueTable (J : Type u) := List (J × Option Nat)

def readTable {J : Type u} [DecidableEq J] (j : J) : ValueTable J → Option Nat
  | [] => none
  | (k,v) :: rest => if k = j then v else readTable j rest

def minValue : Option Nat → Option Nat → Option Nat
  | none, y => y
  | x, none => x
  | some x, some y => some (min x y)

def sumValues : List (Option Nat) → Option Nat
  | [] => some 0
  | none :: _ => none
  | some x :: xs => (sumValues xs).map (fun y => x+y)

def ruleValue {J : Type u} [DecidableEq J] (S : RuleSystem.{u,v} J)
    (tab : ValueTable J) (r : S.Rule) : Option Nat :=
  (sumValues (List.ofFn (fun i : Fin (S.arity r) => readTable (S.premise r i) tab))).map
    (fun x => S.charge r + x)

def bellmanRound {J : Type u} [DecidableEq J] (S : RuleSystem.{u,v} J)
    (js : List J) (rs : List S.Rule) (tab : ValueTable J) : ValueTable J :=
  js.map (fun j => (j, rs.foldl (fun best r =>
    if S.conclusion r = j then minValue best (ruleValue S tab r) else best)
    (readTable j tab)))

def bellmanIterate {J : Type u} [DecidableEq J] (S : RuleSystem.{u,v} J)
    (js : List J) (rs : List S.Rule) : Nat → ValueTable J → ValueTable J
  | 0, tab => tab
  | n+1, tab => bellmanIterate S js rs n (bellmanRound S js rs tab)

def explicitBellman {J : Type u} [DecidableEq J] (S : RuleSystem.{u,v} J)
    (js : List J) (rs : List S.Rule) : ValueTable J :=
  bellmanIterate S js rs js.length (js.map (fun j => (j, none)))

/-- A closed productive set cannot omit the conclusion of any actual
    original finite derivation. This is the certificate for `none`. -/
theorem productive_of_derivation {J : Type u} {S : RuleSystem.{u,v} J}
    (live : J → Prop)
    (closed : ∀ r, (∀ i, live (S.premise r i)) → live (S.conclusion r))
    {j : J} (p : Derivation S j) : live j := by
  induction p with
  | node r children ih => exact closed r ih

theorem absent_no_derivation {J : Type u} {S : RuleSystem.{u,v} J}
    (live : J → Prop)
    (closed : ∀ r, (∀ i, live (S.premise r i)) → live (S.conclusion r))
    {j : J} (absent : ¬ live j) (p : Derivation S j) : False :=
  absent (productive_of_derivation live closed p)

/-- Exact spectrum-zero transport in a scaled nonnegative form. Natural
    inequalities here are the integer numerator interface of the real
    relative PSD comparison; no spectral solver is assumed. -/
theorem relative_zero (original sparse : Nat)
    (lower : original ≤ 2 * sparse) (upper : 2 * sparse ≤ 3 * original) :
    original = 0 ↔ sparse = 0 := by
  constructor <;> intro h <;> omega

/-- Binary finite-field parity masks: the basis case is already a
    deterministic zero-reflecting probe family. -/
def parityDot : List Bool → List Bool → Bool
  | a :: as, b :: bs => Bool.xor (a && b) (parityDot as bs)
  | _, _ => false

/-- Cech failure labels and original model fibre; the supplied failure
    list retains occurrence indices and proof of actual source failure. -/
def Failure {J : Type u} (f : J → Bool) := {j : J // f j = true}

def noFailureModel {J : Type u} (f : J → Bool) : Prop := ∀ j, f j = false

theorem model_iff_empty_failure {J : Type u} (f : J → Bool) :
    noFailureModel f ↔ (Failure f → False) := by
  constructor
  · intro h w
    have eq := (h w.val).symm.trans w.property
    cases eq
  · intro h j
    cases hj : f j with
    | false => rfl
    | true => exact False.elim (h ⟨j,hj⟩)

/-- A Horn/explicit-grammar negative certificate can supply the chosen label
    to the actual recovered Cech contraction without printing its nerve. -/
def coneFromFailure {J : Type u} (f : J → Bool) (w : Failure f) {n : Nat}
    (xs : ReversibleH24.Cech.Vec (Failure f) n) :=
  ReversibleH24.Cech.cone w xs

theorem coneFromFailure_return {J : Type u} (f : J → Bool) (w : Failure f)
    {n : Nat} (xs : ReversibleH24.Cech.Vec (Failure f) n) :
    ReversibleH24.Cech.face (ReversibleH24.Cech.zeroIndex n)
      (coneFromFailure f w xs) = xs := rfl

/-- Source satisfaction and cost are independent fields of a transport.
    Proof-valued data remain typed; execution costs have one unit. -/
structure ChargedReturn (A : Type u) (B : Type v) where
  encode : A → B
  decode : B → A
  leftInverse : ∀ a, decode (encode a) = a
  encodeCost : A → Nat
  decodeCost : B → Nat

theorem transport_truth {A : Type u} {B : Type v} (t : ChargedReturn A B)
    (P : A → Prop) (a : A) : P (t.decode (t.encode a)) ↔ P a := by
  rw [t.leftInverse]

/-- The costed commuting diagram: a native semantic identity is not itself
    a bound on the encoding/decoding implementation. -/
theorem composedClock (enc native dec E V D : Nat)
    (he : enc ≤ E) (hn : native ≤ V) (hd : dec ≤ D) :
    enc + native + dec ≤ E + V + D := Nat.add_le_add (Nat.add_le_add he hn) hd

/-- Contradiction from a live prefix exceeding the actual clock. Uses the
    existing prefix theorem, not a minimum over possible executions. -/
theorem deadlineFromActualPrefix (paid potential slack : Nat → Nat)
    (balance : ∀ k, paid k + potential (k+1) = slack k + potential k)
    (positive : ∀ k, 1 ≤ paid k) (K B : Nat)
    (initial : potential 0 ≤ K)
    (budget : ReversibleH24.accumulated slack (B+K+1) ≤ B) : False :=
  ReversibleH24.no_prefix_beyond_budget paid potential slack balance positive K B initial budget

open ReversibleH24.Matrices in
def controlledCommutator (u v : Bool) (p : Port) : Port :=
  let p1 := if v then toffoliPort p else p
  let p2 := if u then fredkinPort p1 else p1
  let p3 := if v then toffoliPort p2 else p2
  if u then fredkinPort p3 else p3

open ReversibleH24.Matrices in
theorem commutator_detects_and (u v : Bool) :
    decide (controlledCommutator u v (false,true) ≠ (false,true)) = (u && v) := by
  cases u <;> cases v <;> rfl

/-- Carry with retained quotient: exact integral base-3/2 numerator. -/
theorem carry_preserves (a b q : Int) :
    2 * (a - 3*q) + 3 * (b + 2*q) = 2*a + 3*b := by omega

theorem carry_roundtrip (a b q : Int) :
    (a - 3*q + 3*q, b + 2*q - 2*q) = (a,b) := by
  apply Prod.ext <;> simp <;> omega

#print axioms policyFromPositiveTight
#print axioms greatestFeasible
#print axioms scanTight_no_hit
#print axioms constructFromBellman
#print axioms productive_of_derivation
#print axioms absent_no_derivation
#print axioms explicitBellman
#print axioms relative_zero
#print axioms model_iff_empty_failure
#print axioms coneFromFailure_return
#print axioms transport_truth
#print axioms composedClock
#print axioms deadlineFromActualPrefix
#print axioms commutator_detects_and
#print axioms carry_preserves
#print axioms carry_roundtrip
end H24Simultaneous

/- New extension of the recovered 15 October Clifford descent, 25 November.
   The preceding H24 source is preserved verbatim. This extension is supplied
   for Lean replay; no new Lean kernel run is claimed in this environment.
   Integer numerator calculus is used before rational/2-adic division.
   The finite-field root bound and real spectral interpretation are proved in
   the companion written proof, not introduced as global Lean axioms. -/
namespace CliffordH24

universe u v w u' v'

structure DescentPort (X : Type u) (Y : Type v) (K : Type w) where
  subX : X → X → X
  subY : Y → Y → Y
  scale : K → X → X
  forward : X → Y
  adjoint : Y → X
  target : Y

def step {X : Type u} {Y : Type v} {K : Type w}
    (P : DescentPort X Y K) (eta : K) (x : X) : X :=
  P.subX x (P.scale eta (P.adjoint (P.subY (P.forward x) P.target)))

/-- CG24: both adjoint squares, not just the forward square. -/
theorem step_covariant {X : Type u} {Y : Type v} {K : Type w}
    {Xc : Type u'} {Yc : Type v'}
    (F : DescentPort X Y K) (C : DescentPort Xc Yc K)
    (q : X → Xc) (p : Y → Yc)
    (qSub : ∀ x y, q (F.subX x y) = C.subX (q x) (q y))
    (pSub : ∀ x y, p (F.subY x y) = C.subY (p x) (p y))
    (qScale : ∀ eta x, q (F.scale eta x) = C.scale eta (q x))
    (forwardSquare : ∀ x, p (F.forward x) = C.forward (q x))
    (adjointSquare : ∀ y, q (F.adjoint y) = C.adjoint (p y))
    (targetSquare : p F.target = C.target) (eta : K) (x : X) :
    q (step F eta x) = step C eta (q x) := by
  simp only [step, qSub, qScale, adjointSquare, pSub, forwardSquare, targetSquare]

def run {X : Type u} {Y : Type v} {K : Type w}
    (P : DescentPort X Y K) : List K → X → X
  | [], x => x
  | eta :: es, x => run P es (step P eta x)

theorem run_covariant {X : Type u} {Y : Type v} {K : Type w}
    {Xc : Type u'} {Yc : Type v'}
    (F : DescentPort X Y K) (C : DescentPort Xc Yc K) (q : X → Xc)
    (localSquare : ∀ eta x, q (step F eta x) = step C eta (q x))
    (es : List K) (x : X) : q (run F es x) = run C es (q x) := by
  induction es generalizing x with
  | nil => rfl
  | cons eta es ih =>
      change q (run F es (step F eta x)) = run C es (step C eta (q x))
      rw [ih, localSquare]

/-- Exact old controller matrix identities, with the original positive Gram. -/
structure Mat2 where
  a : Int
  b : Int
  c : Int
  d : Int
  deriving DecidableEq, Repr

def mul2 (A B : Mat2) : Mat2 :=
  ⟨A.a*B.a + A.b*B.c, A.a*B.b + A.b*B.d,
   A.c*B.a + A.d*B.c, A.c*B.b + A.d*B.d⟩
def transpose2 (A : Mat2) : Mat2 := ⟨A.a,A.c,A.b,A.d⟩
def scale2 (k : Int) (A : Mat2) : Mat2 := ⟨k*A.a,k*A.b,k*A.c,k*A.d⟩
def I2 : Mat2 := ⟨1,0,0,1⟩
def controller : Mat2 := ⟨1,1,-1,0⟩
def gram : Mat2 := ⟨2,1,1,2⟩
def normMatrix : Mat2 := ⟨-1,-2,2,1⟩
def inverseNumerator : Mat2 := ⟨1,2,-2,-1⟩

theorem controller_cube : mul2 (mul2 controller controller) controller = scale2 (-1) I2 := by decide

theorem controller_gram : mul2 (mul2 (transpose2 controller) gram) controller = gram := by decide

theorem inverse_both_sides :
    mul2 normMatrix inverseNumerator = scale2 3 I2 ∧
    mul2 inverseNumerator normMatrix = scale2 3 I2 := by decide

theorem normalization_conformal :
    mul2 (mul2 (transpose2 normMatrix) gram) normMatrix = scale2 3 gram := by decide

theorem inverse_numerator_conformal :
    mul2 (mul2 (transpose2 inverseNumerator) gram) inverseNumerator = scale2 3 gram := by decide

/-- Integer numerator of the finite scalar gradient filter. The corresponding
    rational step for energy t/(2q) is (d-t)/d. -/
def numFold (t : Int) : List Int → Int
  | [] => 1
  | d :: ds => (d-t) * numFold t ds

theorem numFold_zero_of_mem (t : Int) (ds : List Int) (h : t ∈ ds) :
    numFold t ds = 0 := by
  induction ds with
  | nil => simp at h
  | cons d ds ih =>
      rcases List.mem_cons.mp h with eq | hm
      · subst d
        simp [numFold]
      · simp [numFold, ih hm]

def levels (q m : Nat) : List Int :=
  (List.range m).map (fun j => (q : Int) - (j : Int))

theorem level_mem (q m r : Nat) (h : r < m) :
    ((q : Int) - (r : Int)) ∈ levels q m := by
  unfold levels
  exact List.mem_map.mpr ⟨r, List.mem_range.mpr h, rfl⟩

theorem filter_numerator (model : Bool) (t : Int) (ds : List Int)
    (zeroOnModel : model = true → t = 0)
    (levelOnFailure : model = false → t ∈ ds) :
    numFold t ds = if model then numFold 0 ds else 0 := by
  cases model with
  | false => exact numFold_zero_of_mem t ds (levelOnFailure rfl)
  | true => rw [zeroOnModel rfl]

/-- Actual original return at each mark. No global existential read is assumed. -/
theorem cayley_filter_numerator (model : Bool) (t : Int) (q m : Nat)
    (zeroOnModel : model = true → t = 0)
    (rootBound : model = false → ∃ r : Nat, r < m ∧ t = (q : Int) - (r : Int)) :
    numFold t (levels q m) = if model then numFold 0 (levels q m) else 0 := by
  apply filter_numerator model t (levels q m) zeroOnModel
  intro h
  obtain ⟨r,hr,he⟩ := rootBound h
  rw [he]
  exact level_mem q m r hr

/-- Noninvertible projection has an explicit retained lift. -/
def retainDebit (x y : Int) : Int × Int := (y, x-y)
def undoDebit (packet : Int × Int) : Int := packet.1 + packet.2

theorem debit_returns (x y : Int) : undoDebit (retainDebit x y) = x := by
  change y + (x-y) = x
  omega

/-- An arbitrary length sequence of unnormalised filter steps and their
    original intermediate debit packets. -/
def recordedRun (t : Int) : List Int → Int → Int × List Int
  | [], x => (x,[])
  | d :: ds, x =>
      let y := (d-t)*x
      let out := recordedRun t ds y
      (out.1, (x-y) :: out.2)

def undoRun : List Int → Int → Int
  | [], y => y
  | d :: ds, y => d + undoRun ds y

theorem recorded_run_returns (t : Int) (ds : List Int) (x : Int) :
    undoRun (recordedRun t ds x).2 (recordedRun t ds x).1 = x := by
  induction ds generalizing x with
  | nil => rfl
  | cons d ds ih =>
      change (x - (d-t)*x) + undoRun (recordedRun t ds ((d-t)*x)).2
        (recordedRun t ds ((d-t)*x)).1 = x
      rw [ih]
      omega

/-- H24's original calibrated chain now has the actual filter as its
    dependent interpretation. Grade counts stages, not host bit operations. -/
def prefixValue (d : Nat → Int) (t x : Int) : Nat → Int
  | 0 => x
  | n+1 => (d n-t) * prefixValue d t x n

def FilterMeaning (d : Nat → Int) (t x : Int) (n : Nat) :=
  {y : Int // y = prefixValue d t x n}

def filterConstructors (d : Nat → Int) (t x : Int) :
    (r : Hilbert24Policy.chainSystem.Rule) →
      ((i : Fin (Hilbert24Policy.chainSystem.arity r)) →
        FilterMeaning d t x (Hilbert24Policy.chainSystem.premise r i)) →
      FilterMeaning d t x (Hilbert24Policy.chainSystem.conclusion r)
  | .base, _ => ⟨x,rfl⟩
  | .step n, children =>
      let child := children ⟨0, by decide⟩
      ⟨(d n-t)*child.val, congrArg (fun y => (d n-t)*y) child.property⟩
  | .expensive n, _ => ⟨prefixValue d t x n,rfl⟩
  | .loop _, children => children ⟨0, by decide⟩

def h24Filter (d : Nat → Int) (t x : Int) (n : Nat) : FilterMeaning d t x n :=
  Hilbert24Policy.returnOriginal (FilterMeaning d t x) (filterConstructors d t x)
    Hilbert24Policy.chainPolicy n

theorem h24_filter_exact (d : Nat → Int) (t x : Int) (n : Nat) :
    (h24Filter d t x n).val = prefixValue d t x n :=
  (h24Filter d t x n).property

def h24FilterMinimum (n : Nat) :=
  Hilbert24Policy.constructMinimum Hilbert24Policy.chainPolicy n

theorem h24_filter_minimum (n : Nat)
    (competitor : Hilbert24Policy.Derivation Hilbert24Policy.chainSystem n) :
    Hilbert24Policy.work (h24FilterMinimum n).derivation = n ∧
    n ≤ Hilbert24Policy.work competitor :=
  Hilbert24Policy.chain_all_inputs n competitor

/-- An original labelled failed clause can be returned from the symbolic
    projection. It is not inferred from a small nonzero scalar alone. -/
def scanFailure {J : Type u} (f : J → Bool) : List J → Option (H24Simultaneous.Failure f)
  | [] => none
  | j :: js => if h : f j = true then some ⟨j,h⟩ else scanFailure f js

theorem no_hit_means_all_false {J : Type u} (f : J → Bool) (js : List J)
    (h : scanFailure f js = none) (j : J) (hj : j ∈ js) : f j = false := by
  induction js with
  | nil => simp at hj
  | cons k ks ih =>
      by_cases hk : f k = true
      · simp [scanFailure,hk] at h
      · have tail : scanFailure f ks = none := by simpa [scanFailure,hk] using h
        rcases List.mem_cons.mp hj with eq | hm
        · subst j
          cases he : f k with
          | false => rfl
          | true => exact False.elim (hk he)
        · exact ih tail hm

def cechReturn {J : Type u} (f : J → Bool) (w : H24Simultaneous.Failure f) {n : Nat}
    (xs : ReversibleH24.Cech.Vec (H24Simultaneous.Failure f) n) :=
  H24Simultaneous.coneFromFailure f w xs

theorem cech_return_face {J : Type u} (f : J → Bool) (w : H24Simultaneous.Failure f) {n : Nat}
    (xs : ReversibleH24.Cech.Vec (H24Simultaneous.Failure f) n) :
    ReversibleH24.Cech.face (ReversibleH24.Cech.zeroIndex n) (cechReturn f w xs) = xs := rfl

#print axioms step_covariant
#print axioms run_covariant
#print axioms controller_cube
#print axioms controller_gram
#print axioms inverse_both_sides
#print axioms normalization_conformal
#print axioms inverse_numerator_conformal
#print axioms numFold_zero_of_mem
#print axioms level_mem
#print axioms filter_numerator
#print axioms cayley_filter_numerator
#print axioms debit_returns
#print axioms recorded_run_returns
#print axioms h24_filter_exact
#print axioms h24_filter_minimum
#print axioms no_hit_means_all_false
#print axioms cech_return_face
end CliffordH24

/- New finite transport obligations; appended to the existing CliffordH24 source.
   The analytic chart and its modular implementation are proved in README.md
   and tested by check_polylog.py. These declarations are not a kernel receipt. -/
namespace PolylogCliffordH24

/-- Work at a supplied finite coefficient cut. A chart may be represented by
    integer representatives of residues. -/
def transformedNumerator (tau : Int → Int) (t : Int) (ds : List Int) : Int :=
  CliffordH24.numFold (tau t) (ds.map tau)

/-- The known spectral levels, not a learned minimum, supply the annihilator.
    This is an integer identity on common representatives; modular evaluation
    of the two sides uses the same representatives. -/
theorem transformed_filter (tau : Int → Int) (hz : tau 0 = 0)
    (model : Bool) (t : Int) (ds : List Int)
    (zeroOnModel : model = true → t = 0)
    (levelOnFailure : model = false → t ∈ ds) :
    transformedNumerator tau t ds =
      if model then CliffordH24.numFold 0 (ds.map tau) else 0 := by
  unfold transformedNumerator
  apply CliffordH24.filter_numerator model (tau t) (ds.map tau)
  · intro h
    rw [zeroOnModel h, hz]
  · intro h
    exact List.mem_map.mpr ⟨t, levelOnFailure h, rfl⟩

/-- Reuse the exact H24 chain and original dependent interpretation with the
    transformed operands. The resulting grade is still a stage count. -/
def chartedH24 (tau : Int → Int) (d : Nat → Int) (t x : Int) (n : Nat) :=
  CliffordH24.h24Filter (fun i => tau (d i)) (tau t) x n

theorem chartedH24_exact (tau : Int → Int) (d : Nat → Int) (t x : Int) (n : Nat) :
    (chartedH24 tau d t x n).val =
      CliffordH24.prefixValue (fun i => tau (d i)) (tau t) x n :=
  (chartedH24 tau d t x n).property

/-- Explicit multiplicity arithmetic, without an assumed global trace oracle. -/
def modelCount : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + modelCount bs

def markedTrace (w : Nat) : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then w else 0) + markedTrace w bs

theorem marked_trace_factor (w : Nat) (bs : List Bool) :
    markedTrace w bs = w * modelCount bs := by
  induction bs with
  | nil => simp [markedTrace, modelCount]
  | cons b bs ih =>
      cases b <;> simp [markedTrace, modelCount, ih, Nat.mul_add]

/-- Finite residues return counts below the modulus, including the endpoint
    2^n when the caller uses modulus 2^(n+1). -/
theorem exact_count_from_cut (count modulus : Nat) (h : count < modulus) :
    count % modulus = count := Nat.mod_eq_of_lt h

/-- Receiver uses the original count bound, not a parity test. -/
theorem zero_count_receiver (count modulus : Nat) (h : count < modulus) :
    count % modulus = 0 ↔ count = 0 := by
  rw [exact_count_from_cut count modulus h]

#print axioms transformed_filter
#print axioms chartedH24_exact
#print axioms marked_trace_factor
#print axioms exact_count_from_cut
#print axioms zero_count_receiver
end PolylogCliffordH24

/- Bayes–Belnap–H24: extension of the retained PolylogCliffordH24 source.
   The numerical certificate is a proposition: its witnesses need not be
   computed by the executable branch reader. No reader is postulated to
   exist for unrestricted CNFs. New declarations await Lean kernel replay. -/
namespace BayesBelnapH24

universe u

/-- Independent evidence bits, not exclusive hypotheses. -/
structure Four where
  pos : Bool
  neg : Bool

def negFour (b : Four) : Four := ⟨b.neg, b.pos⟩

def knowledgeJoin (a b : Four) : Four := ⟨a.pos || b.pos, a.neg || b.neg⟩

theorem neg_involution (a : Four) : negFour (negFour a) = a := by
  cases a
  rfl

theorem neg_join (a b : Four) :
    negFour (knowledgeJoin a b) = knowledgeJoin (negFour a) (negFour b) := rfl

/-- w0,w1 are nonnegative true weights scaled by a common denominator.
    r is the approximate posterior times their total, at the same scale.
    A common further denominator makes all three natural numbers. -/
def select (w0 w1 r : Nat) : Bool :=
  if w0 + w1 ≤ 2*r then false else true

/-- From a quarter ground-weight reserve to the one-fifth mass bound. -/
theorem fifth_margin (bad ground other : Nat) (h : 4*bad ≤ ground) :
    5*bad ≤ bad+ground+other := by omega

/-- A branch bit plus an erased arithmetic certificate. When a branch
    does not contain a minimum, its conditional mass is at most 1/5.
    The two error inequalities encode absolute posterior error <= 1/4.
    The existence of the weights is proof data, not a readout oracle. -/
structure MarginRead (e0 e1 : Nat) where
  bit : Bool
  certificate : ∃ a b r : Nat,
    0 < a+b ∧
    4*r ≤ 4*a+(a+b) ∧
    4*a ≤ 4*r+(a+b) ∧
    (e1 < e0 → 5*a ≤ a+b) ∧
    (e0 < e1 → 5*b ≤ a+b) ∧
    bit = select a b r

theorem selected_minimum {e0 e1 : Nat} (R : MarginRead e0 e1) :
    (if R.bit then e1 else e0) = min e0 e1 := by
  rcases R.certificate with ⟨a,b,r,hpos,hup,hdown,hbad0,hbad1,hbit⟩
  by_cases h : a+b ≤ 2*r
  · have hzero : R.bit = false := by simpa [select,h] using hbit
    have hle : e0 ≤ e1 := by
      by_cases k : e0 ≤ e1
      · exact k
      · have hh := hbad0 (by omega)
        omega
    simp [hzero, Nat.min_eq_left hle]
  · have hone : R.bit = true := by simpa [select,h] using hbit
    have hle : e1 ≤ e0 := by
      by_cases k : e1 ≤ e0
      · exact k
      · have hh := hbad1 (by omega)
        omega
    simp [hone, Nat.min_eq_right hle]

/-- The conditional original prefix interface. The minimum value is used in
    the specification. No computation of it is needed in run/route, except
    insofar as a particular implementation of reader chooses to use it.
    stepCost must be independently justified as actual bit work. -/
structure PrefixSystem (S : Nat → Type u) where
  value : {d : Nat} → S d → Nat
  child : {d : Nat} → S (d+1) → Bool → S d
  split : ∀ {d : Nat} (p : S (d+1)),
    value p = min (value (child p false)) (value (child p true))
  reader : ∀ {d : Nat} (p : S (d+1)),
    MarginRead (value (child p false)) (value (child p true))
  stepCost : {d : Nat} → S (d+1) → Nat

def run {S : Nat → Type u} (P : PrefixSystem S) : (d : Nat) → S d → S 0
  | 0,p => p
  | d+1,p => run P d (P.child p (P.reader p).bit)

def route {S : Nat → Type u} (P : PrefixSystem S) : (d : Nat) → S d → List Bool
  | 0,_ => []
  | d+1,p => (P.reader p).bit :: route P d (P.child p (P.reader p).bit)

def paid {S : Nat → Type u} (P : PrefixSystem S) : (d : Nat) → S d → Nat
  | 0,_ => 0
  | d+1,p => P.stepCost p + paid P d (P.child p (P.reader p).bit)

theorem one_step_min {S : Nat → Type u} (P : PrefixSystem S) {d : Nat}
    (p : S (d+1)) : P.value (P.child p (P.reader p).bit) = P.value p := by
  have hm := selected_minimum (P.reader p)
  rw [P.split p]
  cases h : (P.reader p).bit <;> simpa [h] using hm

/-- Each pin costs one declared grade unit; the terminal rule has charge
    1+original violation count. These positive grades are not bit costs. -/
def stagePotential {S : Nat → Type u} (P : PrefixSystem S) {d : Nat}
    (p : S d) : Nat := d+1+P.value p

theorem every_pin_calibrated {S : Nat → Type u} (P : PrefixSystem S)
    {d : Nat} (p : S (d+1)) (b : Bool) :
    stagePotential P p ≤ 1+stagePotential P (P.child p b) := by
  have h : P.value p ≤ P.value (P.child p b) := by
    rw [P.split p]
    cases b
    · exact Nat.min_le_left _ _
    · exact Nat.min_le_right _ _
  unfold stagePotential
  omega

theorem selected_pin_tight {S : Nat → Type u} (P : PrefixSystem S)
    {d : Nat} (p : S (d+1)) :
    1+stagePotential P (P.child p (P.reader p).bit) = stagePotential P p := by
  have h := one_step_min P p
  unfold stagePotential
  omega

theorem run_minimum {S : Nat → Type u} (P : PrefixSystem S)
    (d : Nat) (p : S d) : P.value (run P d p) = P.value p := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change P.value (run P d (P.child p (P.reader p).bit)) = P.value p
    exact (ih _).trans (one_step_min P p)

theorem route_length {S : Nat → Type u} (P : PrefixSystem S)
    (d : Nat) (p : S d) : (route P d p).length = d := by
  induction d with
  | zero => rfl
  | succ d ih => simp [route, ih]

theorem paid_bound {S : Nat → Type u} (P : PrefixSystem S)
    (K : Nat) (h : ∀ {d : Nat} (p : S (d+1)), P.stepCost p ≤ K)
    (d : Nat) (p : S d) : paid P d p ≤ d*K := by
  induction d with
  | zero => simp [paid]
  | succ d ih =>
    change P.stepCost p + paid P d (P.child p (P.reader p).bit) ≤ (d+1)*K
    calc
      _ ≤ K + d*K := Nat.add_le_add (h p) (ih _)
      _ = (d+1)*K := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm K (d*K)]

/-- Exact original minimum result, with the checked dependent equality. -/
def constructOriginalMinimum {S : Nat → Type u} (P : PrefixSystem S)
    (d : Nat) (p : S d) : {a : S 0 // P.value a = P.value p} :=
  ⟨run P d p, run_minimum P d p⟩

/-- Reuse the earlier H24 stage-grade constructor. The stage grade is not
    identified with paid P d p without the corresponding cost proof. -/
def h24Schedule (d : Nat) :=
  Hilbert24Policy.constructMinimum Hilbert24Policy.chainPolicy d

theorem h24_schedule_minimum (d : Nat)
    (competitor : Hilbert24Policy.Derivation Hilbert24Policy.chainSystem d) :
    Hilbert24Policy.work (h24Schedule d).derivation = d ∧
    d ≤ Hilbert24Policy.work competitor :=
  Hilbert24Policy.chain_all_inputs d competitor

#print axioms neg_involution
#print axioms neg_join
#print axioms fifth_margin
#print axioms selected_minimum
#print axioms one_step_min
#print axioms every_pin_calibrated
#print axioms selected_pin_tight
#print axioms run_minimum
#print axioms route_length
#print axioms paid_bound
#print axioms constructOriginalMinimum
#print axioms h24_schedule_minimum
end BayesBelnapH24

/- Ultrametric extension of the retained BayesBelnapH24 development.
   Grade is the compressed representation of {0} union {2^e : e : Nat}.
   none means zero amplitude; at a finite cut it means unobserved.
   The mathematical identification of cut with reduction mod 2^k is
   proved in README.md. This file proves the symbolic-cut laws, not an
   imported theorem about a completed p-adic field. No runtime available
   in the current session: new declarations await kernel replay. -/
namespace UltrametricH24
universe u
abbrev Grade := Option Nat

def cut (k : Nat) : Grade → Grade
  | none => none
  | some a => if a < k then some a else none

def alt : Grade → Grade → Grade
  | none, y => y
  | x, none => x
  | some a, some b => some (min a b)

def mul : Grade → Grade → Grade
  | some a, some b => some (a+b)
  | _, _ => none

def delay : Grade → Grade
  | none => none
  | some a => some (a+1)

/-- Equality of the first k dyadic planes. -/
def Agree (k : Nat) (a b : Grade) : Prop := cut k a = cut k b

theorem cut_nested (k l : Nat) (x : Grade) (h : k ≤ l) :
    cut k (cut l x) = cut k x := by
  cases x with
  | none => rfl
  | some a =>
    by_cases ha : a < l
    · simp [cut, ha]
    · have hk : ¬ a < k := by omega
      simp [cut, ha, hk]

theorem agree_lower {k l : Nat} {x y : Grade}
    (h : k ≤ l) (e : Agree l x y) : Agree k x y := by
  unfold Agree at *
  calc
    cut k x = cut k (cut l x) := (cut_nested k l x h).symm
    _ = cut k (cut l y) := congrArg (cut k) e
    _ = cut k y := cut_nested k l y h

/-- Strong triangle inequality, exactly at finite apertures.
    v(x-z) >= min(v(x-y),v(y-z)). -/
theorem strong_triangle {k l : Nat} {x y z : Grade}
    (h : Agree k x y) (e : Agree l y z) : Agree (min k l) x z :=
  Eq.trans (agree_lower (Nat.min_le_left k l) h)
    (agree_lower (Nat.min_le_right k l) e)

theorem cut_zero (x : Grade) : cut 0 x = none := by
  cases x <;> simp [cut]

theorem separated (x y : Grade) (h : ∀ k, Agree k x y) : x = y := by
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some b =>
      have hb : b < b+1 := by omega
      have e := h (b+1)
      simp [Agree,cut,hb] at e
  | some a =>
    cases y with
    | none =>
      have ha : a < a+1 := by omega
      have e := h (a+1)
      simp [Agree,cut,ha] at e
    | some b =>
      have ha : a < a+b+1 := by omega
      have hb : b < a+b+1 := by omega
      have e := h (a+b+1)
      simpa [Agree,cut,ha,hb] using e

/-- A tie is idempotent; addition in Z_2 would instead carry. -/
theorem alt_idempotent (x : Grade) : alt x x = x := by
  cases x <;> simp [alt]

/-- Both semiring operations respect every finite observation. -/
theorem cut_alt (k : Nat) (x y : Grade) :
    cut k (alt x y) = alt (cut k x) (cut k y) := by
  cases x with
  | none => rfl
  | some a =>
    cases y with
    | none =>
      by_cases ha : a < k <;> simp [cut,alt,ha]
    | some b =>
      by_cases ha : a < k
      · by_cases hb : b < k
        · have hm : min a b < k := Nat.lt_of_le_of_lt (Nat.min_le_left a b) ha
          simp [cut,alt,ha,hb,hm]
        · have hle : a ≤ b := by omega
          simp [cut,alt,ha,hb,Nat.min_eq_left hle]
      · by_cases hb : b < k
        · have hle : b ≤ a := by omega
          simp [cut,alt,ha,hb,Nat.min_eq_right hle]
        · by_cases hle : a ≤ b
          · simp [cut,alt,ha,hb,Nat.min_eq_left hle]
          · have hba : b ≤ a := by omega
            simp [cut,alt,ha,hb,Nat.min_eq_right hba]

theorem cut_mul (k : Nat) (x y : Grade) :
    cut k (mul x y) = cut k (mul (cut k x) (cut k y)) := by
  cases x with
  | none =>
    cases y <;> simp [cut,mul]
  | some a =>
    cases y with
    | none =>
      by_cases ha : a < k <;> simp [cut,mul,ha]
    | some b =>
      by_cases ha : a < k
      · by_cases hb : b < k
        · simp [cut,mul,ha,hb]
        · have hs : ¬ a+b < k := by omega
          simp [cut,mul,ha,hb,hs]
      · by_cases hb : b < k
        · have hs : ¬ a+b < k := by omega
          simp [cut,mul,ha,hb,hs]
        · have hs : ¬ a+b < k := by omega
          simp [cut,mul,ha,hb,hs]

theorem alt_agree {k : Nat} {x x' y y' : Grade}
    (hx : Agree k x x') (hy : Agree k y y') :
    Agree k (alt x y) (alt x' y') := by
  unfold Agree at *
  calc
    cut k (alt x y) = alt (cut k x) (cut k y) := cut_alt k x y
    _ = alt (cut k x') (cut k y') := by rw [hx,hy]
    _ = cut k (alt x' y') := (cut_alt k x' y').symm

theorem mul_agree {k : Nat} {x x' y y' : Grade}
    (hx : Agree k x x') (hy : Agree k y y') :
    Agree k (mul x y) (mul x' y') := by
  unfold Agree at *
  calc
    cut k (mul x y) = cut k (mul (cut k x) (cut k y)) := cut_mul k x y
    _ = cut k (mul (cut k x') (cut k y')) := by rw [hx,hy]
    _ = cut k (mul x' y') := (cut_mul k x' y').symm

/-- Multiplication by 2 gains one digit of error precision. -/
theorem cut_delay (k : Nat) (x : Grade) :
    cut (k+1) (delay x) = delay (cut k x) := by
  cases x with
  | none => rfl
  | some a =>
    by_cases h : a < k
    · have h' : a+1 < k+1 := by omega
      simp [cut,delay,h,h']
    · have h' : ¬ a+1 < k+1 := by omega
      simp [cut,delay,h,h']

theorem delay_agree {k : Nat} {x y : Grade} (h : Agree k x y) :
    Agree (k+1) (delay x) (delay y) := by
  unfold Agree at *
  rw [cut_delay k x,cut_delay k y,h]

def foldAlt : List Grade → Grade
  | [] => none
  | x::xs => alt x (foldAlt xs)

def foldMul : List Grade → Grade
  | [] => some 0
  | x::xs => mul x (foldMul xs)

theorem fold_alt_agree {A : Type u} (xs : List A) {f g : A → Grade} {k : Nat}
    (h : ∀ a, Agree k (f a) (g a)) :
    Agree k (foldAlt (xs.map f)) (foldAlt (xs.map g)) := by
  induction xs with
  | nil => rfl
  | cons a as ih => exact alt_agree (h a) ih

theorem fold_mul_agree {A : Type u} (xs : List A) {f g : A → Grade} {k : Nat}
    (h : ∀ a, Agree k (f a) (g a)) :
    Agree k (foldMul (xs.map f)) (foldMul (xs.map g)) := by
  induction xs with
  | nil => rfl
  | cons a as ih => exact mul_agree (h a) ih

/-- Every rule has positive charge 1+extra, with actual ordered premises.
    Rule families are locally finite; no global finite state bound assumed. -/
structure Rule (J : Type u) where
  extra : Nat
  premises : List J

def evalRule {J : Type u} (x : J → Grade) (r : Rule J) : Grade :=
  delay (mul (some r.extra) (foldMul (r.premises.map x)))

def bellman {J : Type u} (R : J → List (Rule J)) (x : J → Grade) (j : J) : Grade :=
  foldAlt ((R j).map (evalRule x))

/-- The constructive ultrametric contraction of the H24 Bellman operator.
    All states can be considered simultaneously without enumerating proofs. -/
theorem bellman_contract {J : Type u} (R : J → List (Rule J))
    {x y : J → Grade} {k : Nat} (h : ∀ j, Agree k (x j) (y j)) :
    ∀ j, Agree (k+1) (bellman R x j) (bellman R y j) := by
  intro j
  unfold bellman
  apply fold_alt_agree
  intro r
  unfold evalRule
  exact delay_agree (mul_agree rfl (fold_mul_agree r.premises h))

def iterate {J : Type u} (R : J → List (Rule J)) : Nat → J → Grade
  | 0 => fun _ => none
  | k+1 => bellman R (iterate R k)

theorem iterate_agree {J : Type u} (R : J → List (Rule J)) (k : Nat) :
    ∀ j, Agree k (iterate R k j) (iterate R (k+1) j) := by
  induction k with
  | zero => intro j; simp [Agree,cut_zero]
  | succ k ih => exact bellman_contract R ih

def observation {J : Type u} (R : J → List (Rule J)) (k : Nat) (j : J) : Grade :=
  cut k (iterate R k j)

theorem observation_compatible {J : Type u} (R : J → List (Rule J))
    (k : Nat) (j : J) :
    cut k (observation R (k+1) j) = observation R k j := by
  unfold observation
  rw [cut_nested k (k+1) _ (by omega)]
  exact Eq.symm (iterate_agree R k j)

/-- Uniform precision bound relative to any fixed point, not a search
    for the fixed point or an axiom asserting a productive judgement. -/
theorem fixed_point_cut {J : Type u} (R : J → List (Rule J))
    (x : J → Grade) (fixed : ∀ j, bellman R x j = x j) (k : Nat) :
    ∀ j, Agree k (iterate R k j) (x j) := by
  induction k with
  | zero => intro j; simp [Agree,cut_zero]
  | succ k ih =>
    intro j
    have h := bellman_contract R ih j
    change Agree (k+1) (bellman R (iterate R k) j) (x j)
    rw [← fixed j]
    exact h

theorem fixed_point_unique {J : Type u} (R : J → List (Rule J))
    (x y : J → Grade) (hx : ∀ j, bellman R x j = x j)
    (hy : ∀ j, bellman R y j = y j) (j : J) : x j = y j := by
  apply separated
  intro k
  exact Eq.trans (Eq.symm (fixed_point_cut R x hx k j)) (fixed_point_cut R y hy k j)

/-- Select the largest visible norm. false means left; true means right.
    Neither-visible must NOT be used as evidence of an unrestricted empty
    fibre. Left tie-breaking is explicit, and both flags remain available. -/
def choose : Grade → Grade → Bool
  | none, some _ => true
  | some a, some b => decide (b<a)
  | _,_ => false

def visibleFlags (a b : Grade) : BayesBelnapH24.Four :=
  match alt a b with
  | none => ⟨false,false⟩
  | some e => ⟨decide (a = some e),decide (b = some e)⟩

theorem select_visible_min (a b k : Nat) (hv : a<k ∨ b<k) :
    (if choose (cut k (some a)) (cut k (some b)) then b else a) = min a b := by
  by_cases ha : a<k
  · by_cases hb : b<k
    · by_cases h : b<a
      · have hle : b≤a := by omega
        simp [cut,choose,ha,hb,h,Nat.min_eq_right hle]
      · have hle : a≤b := by omega
        simp [cut,choose,ha,hb,h,Nat.min_eq_left hle]
    · have hle : a≤b := by omega
      simp [cut,choose,ha,hb,Nat.min_eq_left hle]
  · by_cases hb : b<k
    · have hle : b≤a := by omega
      simp [cut,choose,ha,hb,Nat.min_eq_right hle]
    · omega

/-- Observations are computational data; exact-grade and visibility
    guarantees are propositions. No unrestricted readout is postulated. -/
structure NormRead (e0 e1 : Nat) where
  depth : Nat
  left : Grade
  right : Grade
  leftCorrect : left = cut depth (some e0)
  rightCorrect : right = cut depth (some e1)
  visible : e0<depth ∨ e1<depth

def NormRead.bit {e0 e1 : Nat} (r : NormRead e0 e1) : Bool :=
  choose r.left r.right

theorem norm_read_min {e0 e1 : Nat} (r : NormRead e0 e1) :
    (if r.bit then e1 else e0) = min e0 e1 := by
  unfold NormRead.bit
  rw [r.leftCorrect,r.rightCorrect]
  exact select_visible_min e0 e1 r.depth r.visible

/-- The same attained grade as the old Bayesian margin receiver, though
    tie-breaking need not select the same original witness. -/
theorem bayes_and_norm_same_grade {e0 e1 : Nat}
    (B : BayesBelnapH24.MarginRead e0 e1) (R : NormRead e0 e1) :
    (if B.bit then e1 else e0) = (if R.bit then e1 else e0) :=
  (BayesBelnapH24.selected_minimum B).trans (norm_read_min R).symm

structure PrefixSystem (S : Nat → Type u) where
  value : {d : Nat} → S d → Nat
  child : {d : Nat} → S (d+1) → Bool → S d
  split : ∀ {d : Nat} (p : S (d+1)),
    value p = min (value (child p false)) (value (child p true))
  reader : ∀ {d : Nat} (p : S (d+1)),
    NormRead (value (child p false)) (value (child p true))
  stepCost : {d : Nat} → S (d+1) → Nat

def run {S : Nat → Type u} (P : PrefixSystem S) : (d : Nat) → S d → S 0
  | 0,p => p
  | d+1,p => run P d (P.child p (P.reader p).bit)

def paid {S : Nat → Type u} (P : PrefixSystem S) : (d : Nat) → S d → Nat
  | 0,_ => 0
  | d+1,p => P.stepCost p + paid P d (P.child p (P.reader p).bit)

theorem step_min {S : Nat → Type u} (P : PrefixSystem S) {d : Nat}
    (p : S (d+1)) : P.value (P.child p (P.reader p).bit) = P.value p := by
  have hm := norm_read_min (P.reader p)
  rw [P.split p]
  cases h : (P.reader p).bit <;> simpa [h] using hm

def potential {S : Nat → Type u} (P : PrefixSystem S) {d : Nat} (p : S d) : Nat :=
  d+1+P.value p

theorem pin_calibrated {S : Nat → Type u} (P : PrefixSystem S) {d : Nat}
    (p : S (d+1)) (b : Bool) : potential P p ≤ 1+potential P (P.child p b) := by
  have h : P.value p ≤ P.value (P.child p b) := by
    rw [P.split p]
    cases b
    · exact Nat.min_le_left _ _
    · exact Nat.min_le_right _ _
  unfold potential
  omega

theorem pin_tight {S : Nat → Type u} (P : PrefixSystem S) {d : Nat}
    (p : S (d+1)) : 1+potential P (P.child p (P.reader p).bit) = potential P p := by
  have h := step_min P p
  unfold potential
  omega

theorem run_minimum {S : Nat → Type u} (P : PrefixSystem S) (d : Nat) (p : S d) :
    P.value (run P d p) = P.value p := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change P.value (run P d (P.child p (P.reader p).bit)) = P.value p
    exact (ih _).trans (step_min P p)

def constructOriginalMinimum {S : Nat → Type u} (P : PrefixSystem S)
    (d : Nat) (p : S d) : {a : S 0 // P.value a = P.value p} :=
  ⟨run P d p, run_minimum P d p⟩

theorem paid_bound {S : Nat → Type u} (P : PrefixSystem S)
    (K : Nat) (h : ∀ {d : Nat} (p : S (d+1)), P.stepCost p ≤ K)
    (d : Nat) (p : S d) : paid P d p ≤ d*K := by
  induction d with
  | zero => simp [paid]
  | succ d ih =>
    change P.stepCost p + paid P d (P.child p (P.reader p).bit) ≤ (d+1)*K
    calc
      _ ≤ K+d*K := Nat.add_le_add (h p) (ih _)
      _ = (d+1)*K := by rw [Nat.add_mul,Nat.one_mul,Nat.add_comm K (d*K)]

#print axioms strong_triangle
#print axioms cut_alt
#print axioms cut_mul
#print axioms cut_delay
#print axioms bellman_contract
#print axioms observation_compatible
#print axioms fixed_point_cut
#print axioms fixed_point_unique
#print axioms norm_read_min
#print axioms bayes_and_norm_same_grade
#print axioms pin_tight
#print axioms constructOriginalMinimum
#print axioms paid_bound
end UltrametricH24

/- Native-involution extension. The chart laws are interfaces to the explicit
   restricted-series construction in README.md. No global norm reader is
   introduced. The new declarations have not been kernel-replayed. -/
namespace NativeInvolutionH24
universe u

structure Chart (A : Type u) where
  encode : A → A
  decode : A → A
  decode_encode : ∀ x, decode (encode x) = x
  encode_decode : ∀ x, encode (decode x) = x

def turn {A : Type u} (C : Chart A) (s : A → A) (y : A) : A :=
  C.encode (s (C.decode y))

theorem turn_on_source {A : Type u} (C : Chart A) (s : A → A) (x : A) :
    turn C s (C.encode x) = C.encode (s x) := by
  simp [turn, C.decode_encode]

theorem turn_twice {A : Type u} (C : Chart A) (s : A → A)
    (hs : ∀ x, s (s x) = x) (y : A) : turn C s (turn C s y) = y := by
  simp [turn, C.decode_encode, hs, C.encode_decode]

theorem turn_fixed_iff {A : Type u} (C : Chart A) (s : A → A) (x : A) :
    turn C s (C.encode x) = C.encode x ↔ s x = x := by
  rw [turn_on_source]
  constructor
  · intro h
    have h' := congrArg C.decode h
    simpa only [C.decode_encode] using h'
  · intro h
    exact congrArg C.encode h

/-- Congruences at finite dyadic apertures, not a classical choice of a limit. -/
structure CutChart (A : Type u) where
  chart : Chart A
  agree : Nat → A → A → Prop
  isometry : ∀ k x y, agree k (chart.encode x) (chart.encode y) ↔ agree k x y

/-- Source negation has the one-guard-bit law because x-(-x)=2x.
    The analytic chart must preserve and reflect each congruence. -/
theorem involution_defect_cut {A : Type u} (C : CutChart A) (s : A → A)
    (z : A) (shift : ∀ k x, C.agree (k+1) (s x) x ↔ C.agree k x z)
    (k : Nat) (x : A) :
    C.agree (k+1) (turn C.chart s (C.chart.encode x)) (C.chart.encode x) ↔
      C.agree k x z := by
  rw [turn_on_source, C.isometry, shift]

/-- Scalar diagonal of the native clause involution I-2F. -/
def clauseSign (f : Bool) : Int := if f then -1 else 1

def clauseFactor (f : Bool) : Int := if f then 2 else 1

theorem clauseSign_square (f : Bool) : clauseSign f * clauseSign f = 1 := by
  cases f <;> decide

/-- For the odd Lerch chart of an involution tau(U)=c U; this is the
    cleared numerator law before division by the guard digit and odd c. -/
theorem polylog_clause_numerator (c : Int) (f : Bool) :
    3*c - c*clauseSign f = 2*c*clauseFactor f := by
  cases f <;> simp [clauseSign, clauseFactor] <;> omega

/-- Reuse the original minimum receiver on two source grades after decoding.
    These hypotheses certify actual finite observations, not a way to
    acquire them from unrestricted CNFs. -/
theorem native_branch_minimum {a b k : Nat}
    (C : Chart UltrametricH24.Grade) (x y : UltrametricH24.Grade)
    (hx : x = C.encode (UltrametricH24.cut k (some a)))
    (hy : y = C.encode (UltrametricH24.cut k (some b)))
    (visible : a < k ∨ b < k) :
    (if UltrametricH24.choose (C.decode x) (C.decode y) then b else a) = min a b := by
  rw [hx, hy, C.decode_encode, C.decode_encode]
  exact UltrametricH24.select_visible_min a b k visible

#print axioms turn_on_source
#print axioms turn_twice
#print axioms turn_fixed_iff
#print axioms involution_defect_cut
#print axioms clauseSign_square
#print axioms polylog_clause_numerator
#print axioms native_branch_minimum
end NativeInvolutionH24
