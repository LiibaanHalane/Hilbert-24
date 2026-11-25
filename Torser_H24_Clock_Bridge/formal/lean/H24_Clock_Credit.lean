import Std
import H24_Operational_Bridge

/-
The reversible-clock bridge, used as an actual H24 constructor input.
The state type may already be the subtype reachable on the promised source
side. No decision procedure receives a proof of that promise.
Every next=some edge is one actual bit tick of the fixed implementation.
Signed amortized charges are allowed; only the complete reserve must fall.
-/
namespace H24ClockCredit

open H24OperationalBridge
universe u

/-- Natural-valued frontier credit, with the two original local equations. -/
structure FrontierAccount {S : Type u} (M : BitMachine S) where
  potential : S → Nat
  credit : S → Nat
  charge : S → S → Nat
  balance : ∀ s t, M.next s = some t →
    1 + potential t = charge s t + potential s
  pays : ∀ s t, M.next s = some t →
    charge s t + credit t ≤ credit s

def FrontierAccount.reserve {S : Type u} {M : BitMachine S}
    (A : FrontierAccount M) (s : S) : Nat :=
  A.potential s + A.credit s

theorem FrontierAccount.reserve_step {S : Type u} {M : BitMachine S}
    (A : FrontierAccount M) (s t : S) (h : M.next s = some t) :
    1 + A.reserve t ≤ A.reserve s := by
  change 1 + (A.potential t + A.credit t) ≤ A.potential s + A.credit s
  calc
    1 + (A.potential t + A.credit t)
        = (1 + A.potential t) + A.credit t := (Nat.add_assoc _ _ _).symm
    _ = (A.charge s t + A.potential s) + A.credit t :=
      congrArg (fun x => x + A.credit t) (A.balance s t h)
    _ = A.potential s + (A.charge s t + A.credit t) := by
      rw [Nat.add_comm (A.charge s t) (A.potential s), Nat.add_assoc]
    _ ≤ A.potential s + A.credit s :=
      Nat.add_le_add_left (A.pays s t h) _

def FrontierAccount.toRanking {S : Type u} {M : BitMachine S}
    (A : FrontierAccount M) : Ranking M where
  reserve := A.reserve
  decrease := by
    intro s t h
    apply Nat.lt_of_succ_le
    exact (Nat.one_add (A.reserve t)) ▸ (A.reserve_step s t h)

def putFrontierInH24 {S : Type u} {M : BitMachine S}
    (A : FrontierAccount M) (s : S) :=
  putRunInH24 A.toRanking s

theorem frontier_constructs_actual_clock {S : Type u} {M : BitMachine S}
    (A : FrontierAccount M) (s : S) :
    ticks (sourceRun A.toRanking s) ≤ A.potential s + A.credit s :=
  sourceRun_paid A.toRanking s

structure SignedAccount {S : Type u} (M : BitMachine S) where
  potential : S → Nat
  spent : S → Int
  allowance : Nat
  prefix_cap : ∀ s, spent s ≤ (allowance : Int)
  balance : ∀ s t, M.next s = some t →
    (1 : Int) + (potential t : Int) ≤
      (spent t - spent s) + (potential s : Int)

def SignedAccount.reserve {S : Type u} {M : BitMachine S}
    (A : SignedAccount M) (s : S) : Nat :=
  ((A.potential s : Int) + (A.allowance : Int) - A.spent s).toNat

theorem SignedAccount.reserve_cast {S : Type u} {M : BitMachine S}
    (A : SignedAccount M) (s : S) :
    (A.reserve s : Int) =
      (A.potential s : Int) + (A.allowance : Int) - A.spent s := by
  apply Int.toNat_of_nonneg
  have h := A.prefix_cap s
  omega

theorem SignedAccount.reserve_step {S : Type u} {M : BitMachine S}
    (A : SignedAccount M) (s t : S) (h : M.next s = some t) :
    1 + A.reserve t ≤ A.reserve s := by
  have hs := A.reserve_cast s
  have ht := A.reserve_cast t
  have hb := A.balance s t h
  omega

def SignedAccount.toRanking {S : Type u} {M : BitMachine S}
    (A : SignedAccount M) : Ranking M where
  reserve := A.reserve
  decrease := by
    intro s t h
    have hb := A.reserve_step s t h
    omega

theorem SignedAccount.initial_reserve {S : Type u} {M : BitMachine S}
    (A : SignedAccount M) (s : S) (h : A.spent s = 0) :
    A.reserve s = A.potential s + A.allowance := by
  have hr := A.reserve_cast s
  omega

/-- The bridge is placed in the original H24 constructor by this definition. -/
def putCreditInH24 {S : Type u} {M : BitMachine S}
    (A : SignedAccount M) (s : S) :=
  putRunInH24 A.toRanking s

theorem credit_constructs_actual_run {S : Type u} {M : BitMachine S}
    (A : SignedAccount M) (s : S) :
    ticks (sourceRun A.toRanking s) ≤ A.reserve s :=
  sourceRun_paid A.toRanking s

theorem credit_constructs_initial_clock {S : Type u} {M : BitMachine S}
    (A : SignedAccount M) (s : S) (h : A.spent s = 0) :
    ticks (sourceRun A.toRanking s) ≤ A.potential s + A.allowance := by
  have hb := credit_constructs_actual_run A s
  rw [A.initial_reserve s h] at hb
  exact hb

/-- A polynomial envelope is explicit data; no coefficients are searched for. -/
structure Budget where
  coefficient : Nat
  degree : Nat

def Budget.eval (p : Budget) (n : Nat) : Nat :=
  p.coefficient * (n+1)^p.degree

/-- Primitive-recursive maximum, with elementary constructive order proofs. -/
def joinDegree : Nat → Nat → Nat
  | 0, b => b
  | a+1, 0 => a+1
  | a+1, b+1 => joinDegree a b + 1

theorem joinDegree_left (a b : Nat) : a ≤ joinDegree a b := by
  induction a generalizing b with
  | zero => exact Nat.zero_le _
  | succ a ih =>
      cases b with
      | zero => exact Nat.le_refl _
      | succ b => exact Nat.succ_le_succ (ih b)

theorem joinDegree_right (a b : Nat) : b ≤ joinDegree a b := by
  induction a generalizing b with
  | zero => exact Nat.le_refl _
  | succ a ih =>
      cases b with
      | zero => exact Nat.zero_le _
      | succ b => exact Nat.succ_le_succ (ih b)

def Budget.add (p q : Budget) : Budget :=
  ⟨p.coefficient+q.coefficient, joinDegree p.degree q.degree⟩

theorem add_mul_constructive (a b k : Nat) :
    (a+b)*k = a*k + b*k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Nat.mul_succ, Nat.mul_succ, Nat.mul_succ, ih]
      exact Nat.add_add_add_comm _ _ _ _

theorem Budget.add_bound (p q : Budget) (n : Nat) :
    p.eval n + q.eval n ≤ (p.add q).eval n := by
  have hp : (n+1)^p.degree ≤ (n+1)^(joinDegree p.degree q.degree) :=
    Nat.pow_le_pow_right (Nat.zero_lt_succ n) (joinDegree_left _ _)
  have hq : (n+1)^q.degree ≤ (n+1)^(joinDegree p.degree q.degree) :=
    Nat.pow_le_pow_right (Nat.zero_lt_succ n) (joinDegree_right _ _)
  change p.coefficient * (n+1)^p.degree + q.coefficient * (n+1)^q.degree ≤
    (p.coefficient+q.coefficient) * (n+1)^(joinDegree p.degree q.degree)
  rw [add_mul_constructive]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ hp) (Nat.mul_le_mul_left _ hq)

def Budget.mul (p q : Budget) : Budget :=
  ⟨p.coefficient*q.coefficient, p.degree+q.degree⟩

theorem Budget.mul_exact (p q : Budget) (n : Nat) :
    p.eval n * q.eval n = (p.mul q).eval n := by
  simp only [eval, mul, Nat.pow_add]
  ac_rfl

/-- The natural frontier version of the complete uniform H24 clock. -/
theorem uniform_frontier_clock
    {Input : Type} {S : Input → Type u}
    (M : (C : Input) → BitMachine (S C))
    (initial : (C : Input) → S C)
    (size : Input → Nat)
    (A : (C : Input) → FrontierAccount (M C))
    (p q : Budget)
    (potential_bound : ∀ C, (A C).potential (initial C) ≤ p.eval (size C))
    (credit_bound : ∀ C, (A C).credit (initial C) ≤ q.eval (size C)) :
    ∀ C, ticks (sourceRun (A C).toRanking (initial C)) ≤ (p.add q).eval (size C) := by
  intro C
  calc
    ticks (sourceRun (A C).toRanking (initial C))
        ≤ (A C).potential (initial C) + (A C).credit (initial C) :=
      frontier_constructs_actual_clock (A C) (initial C)
    _ ≤ p.eval (size C) + q.eval (size C) :=
      Nat.add_le_add (potential_bound C) (credit_bound C)
    _ ≤ (p.add q).eval (size C) := Budget.add_bound p q (size C)

/-- The returned coefficient/degree are fixed before all source inputs. -/
theorem uniform_credit_clock
    {Input : Type} {S : Input → Type u}
    (M : (C : Input) → BitMachine (S C))
    (initial : (C : Input) → S C)
    (size : Input → Nat)
    (A : (C : Input) → SignedAccount (M C))
    (p q : Budget)
    (spent_zero : ∀ C, (A C).spent (initial C) = 0)
    (potential_bound : ∀ C, (A C).potential (initial C) ≤ p.eval (size C))
    (allowance_bound : ∀ C, (A C).allowance ≤ q.eval (size C)) :
    ∀ C, ticks (sourceRun (A C).toRanking (initial C)) ≤ (p.add q).eval (size C) := by
  intro C
  calc
    ticks (sourceRun (A C).toRanking (initial C))
        ≤ (A C).potential (initial C) + (A C).allowance :=
      credit_constructs_initial_clock (A C) (initial C) (spent_zero C)
    _ ≤ p.eval (size C) + q.eval (size C) :=
      Nat.add_le_add (potential_bound C) (allowance_bound C)
    _ ≤ (p.add q).eval (size C) := Budget.add_bound p q (size C)

/-- Construct the exact promised-side source reserve from the frontier fields.
    The fixed implementation and p,q precede all original inputs. -/
def frontierUniformReserve
    {Input : Type} {State : Type u}
    (G : GeneratorImplementation Input State)
    (A : ∀ C, G.Negative C → FrontierAccount (ReachMachine G C))
    (p q : Budget)
    (positive : 0 < p.coefficient + q.coefficient)
    (potential_bound : ∀ C h, (A C h).potential (Initial G C) ≤ p.eval (G.inputBits C))
    (credit_bound : ∀ C h, (A C h).credit (Initial G C) ≤ q.eval (G.inputBits C)) :
    UniformReserve G where
  coefficient := p.coefficient + q.coefficient
  degree := joinDegree p.degree q.degree
  positive := positive
  ranking C h := (A C h).toRanking
  initial_bound C h := by
    change (A C h).potential (Initial G C) + (A C h).credit (Initial G C) ≤
      (p.add q).eval (G.inputBits C)
    exact Nat.le_trans (Nat.add_le_add (potential_bound C h) (credit_bound C h))
      (Budget.add_bound p q (G.inputBits C))

/-- A native frontier account now enters the original H24 constructor directly. -/
def putFrontierBridgeInH24
    {Input : Type} {State : Type u}
    (G : GeneratorImplementation Input State)
    (A : ∀ C, G.Negative C → FrontierAccount (ReachMachine G C))
    (p q : Budget)
    (positive : 0 < p.coefficient + q.coefficient)
    (potential_bound : ∀ C h, (A C h).potential (Initial G C) ≤ p.eval (G.inputBits C))
    (credit_bound : ∀ C h, (A C h).credit (Initial G C) ≤ q.eval (G.inputBits C))
    (C : Input) (h : G.Negative C) :=
  putBridgeInH24 (frontierUniformReserve G A p q positive potential_bound credit_bound) C h

/-- The actual stopped decision receives C; negative evidence is not an input. -/
def decideFromFrontier
    {Input : Type} {State : Type u}
    (G : GeneratorImplementation Input State)
    (A : ∀ C, G.Negative C → FrontierAccount (ReachMachine G C))
    (p q : Budget)
    (positive : 0 < p.coefficient + q.coefficient)
    (potential_bound : ∀ C h, (A C h).potential (Initial G C) ≤ p.eval (G.inputBits C))
    (credit_bound : ∀ C h, (A C h).credit (Initial G C) ≤ q.eval (G.inputBits C))
    (C : Input) : Decidable (G.Negative C) :=
  decideNegative (bridgeDeadline
    (frontierUniformReserve G A p q positive potential_bound credit_bound)) C

-- Pointwise statement: this native polynomial field has to be supplied for
-- the same concrete implementation, not for an unrelated code-length grade.
-- It contains no axiom asserting the existence of an account for SAT.

#print axioms FrontierAccount.reserve_step
#print axioms frontier_constructs_actual_clock
#print axioms SignedAccount.reserve_cast
#print axioms SignedAccount.reserve_step
#print axioms SignedAccount.initial_reserve
#print axioms credit_constructs_actual_run
#print axioms credit_constructs_initial_clock
#print axioms Budget.add_bound
#print axioms Budget.mul_exact
#print axioms uniform_frontier_clock
#print axioms uniform_credit_clock
#print axioms frontierUniformReserve
#print axioms putFrontierBridgeInH24
#print axioms decideFromFrontier

end H24ClockCredit
