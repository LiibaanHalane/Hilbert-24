import H24_Operational_Bridge

/-!
The named local-reserve source judgement is equivalent to the original whole
negative deadline, for the SAME fixed deterministic bit machine. The converse
constructs a reserve by finite recursion at the already supplied deadline.
It neither chooses a reachability trace nor searches for a new machine/clock.
The constructed reserve is proof data; its synthesis is not declared free
inside an independently executed generator.
-/

namespace H24OperationalBridge

universe u v w

def boundedTicks {S : Type u} (M : BitMachine S) : Nat → S → Nat
  | 0, _ => 0
  | n+1, s => match M.next s with
    | none => 0
    | some t => 1 + boundedTicks M n t

theorem boundedTicks_halt {S : Type u} (M : BitMachine S) (n : Nat)
    (s : S) (h : M.next s = none) : boundedTicks M n s = 0 := by
  cases n with
  | zero => rfl
  | succ n => rw [boundedTicks, h]

theorem boundedTicks_tick {S : Type u} (M : BitMachine S) (n : Nat)
    (s t : S) (h : M.next s = some t) :
    boundedTicks M (n+1) s = 1 + boundedTicks M n t := by
  rw [boundedTicks, h]

theorem boundedTicks_le {S : Type u} (M : BitMachine S) (n : Nat)
    (s : S) : boundedTicks M n s ≤ n := by
  induction n generalizing s with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
      cases h : M.next s with
      | none => rw [boundedTicks_halt M (n+1) s h]; exact Nat.zero_le _
      | some t =>
          rw [boundedTicks_tick M n s t h, Nat.add_comm 1]
          exact Nat.succ_le_succ (ih t)

theorem halted_after_extra {S : Type u} (M : BitMachine S) (n k : Nat)
    (s : S) (h : M.next (runFor M n s) = none) :
    M.next (runFor M (n+k) s) = none := by
  rw [runFor_add, runFor_halt M k (runFor M n s) h]
  exact h

theorem boundedTicks_stable {S : Type u} (M : BitMachine S) (n : Nat)
    (s : S) (h : M.next (runFor M n s) = none) :
    boundedTicks M (n+1) s = boundedTicks M n s := by
  induction n generalizing s with
  | zero => exact boundedTicks_halt M 1 s h
  | succ n ih =>
      cases hs : M.next s with
      | none => rw [boundedTicks_halt M (n+1+1) s hs, boundedTicks_halt M (n+1) s hs]
      | some t =>
          rw [runFor, hs] at h
          rw [boundedTicks_tick M (n+1) s t hs, boundedTicks_tick M n s t hs]
          exact congrArg (fun k => 1+k) (ih t h)

theorem halted_tail {S : Type u} (M : BitMachine S) (n : Nat)
    (s t : S) (step : M.next s = some t)
    (h : M.next (runFor M n s) = none) : M.next (runFor M n t) = none := by
  cases n with
  | zero =>
      change M.next s = none at h
      rw [step] at h
      cases h
  | succ n =>
      rw [runFor, step] at h
      exact halted_after_extra M n 1 t h

theorem reached_halted_by_same_deadline {S : Type u} (M : BitMachine S)
    (n : Nat) (start : S) (h : M.next (runFor M n start) = none)
    (s : S) (reachable : Reachable M start s) : M.next (runFor M n s) = none := by
  induction reachable with
  | initial => exact h
  | @advance s t previous step ih => exact halted_tail M n s t step ih

theorem boundedTicks_decreases {S : Type u} (M : BitMachine S) (n : Nat)
    (s t : S) (step : M.next s = some t)
    (h : M.next (runFor M n s) = none) : boundedTicks M n t < boundedTicks M n s := by
  cases n with
  | zero =>
      change M.next s = none at h
      rw [step] at h
      cases h
  | succ n =>
      rw [runFor, step] at h
      rw [boundedTicks_tick M n s t step, boundedTicks_stable M n t h,
        Nat.add_comm 1]
      exact Nat.lt_succ_self _

/-- A finite, explicit local ranking on reached negative states. -/
def rankingFromDeadline {Input : Type u} {State : Type v}
    {G : GeneratorImplementation.{u,v,w} Input State} (D : UniformDeadline G)
    (C : Input) (negative : G.Negative C) : Ranking (ReachMachine G C) where
  reserve q := boundedTicks G.machine
    (D.coefficient * (G.inputBits C + 1)^D.degree) q.val
  decrease q r step := by
    have actual := reached_projection G.machine (G.initial C) q
    rw [step] at actual
    have sourceStep : G.machine.next q.val = some r.val := actual.symm
    exact boundedTicks_decreases G.machine _ q.val r.val sourceStep
      (reached_halted_by_same_deadline G.machine _ (G.initial C) (D.hit C negative)
        q.val q.property)

def reserveFromDeadline {Input : Type u} {State : Type v}
    {G : GeneratorImplementation.{u,v,w} Input State} (D : UniformDeadline G) :
    UniformReserve G where
  coefficient := D.coefficient
  degree := D.degree
  positive := D.positive
  ranking := rankingFromDeadline D
  initial_bound C _h := boundedTicks_le G.machine _ (G.initial C)

/-- Exact judgement equivalence, with one original program and fixed c,d. -/
theorem reserve_target_iff_deadline_target {Input : Type u} {State : Type v}
    (G : GeneratorImplementation.{u,v,w} Input State) :
    UniformReserveTarget G ↔ UniformDeadlineTarget G := by
  constructor
  · exact named_source_bridge G
  · intro ⟨D⟩
    exact ⟨reserveFromDeadline D⟩

theorem converse_keeps_clock {Input : Type u} {State : Type v}
    {G : GeneratorImplementation.{u,v,w} Input State} (D : UniformDeadline G) :
    (reserveFromDeadline D).coefficient = D.coefficient ∧
    (reserveFromDeadline D).degree = D.degree := ⟨rfl, rfl⟩

end H24OperationalBridge

#print axioms H24OperationalBridge.boundedTicks_le
#print axioms H24OperationalBridge.boundedTicks_stable
#print axioms H24OperationalBridge.reached_halted_by_same_deadline
#print axioms H24OperationalBridge.boundedTicks_decreases
#print axioms H24OperationalBridge.rankingFromDeadline
#print axioms H24OperationalBridge.reserveFromDeadline
#print axioms H24OperationalBridge.reserve_target_iff_deadline_target
#print axioms H24OperationalBridge.converse_keeps_clock
