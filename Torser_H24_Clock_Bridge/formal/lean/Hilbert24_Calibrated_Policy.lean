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
