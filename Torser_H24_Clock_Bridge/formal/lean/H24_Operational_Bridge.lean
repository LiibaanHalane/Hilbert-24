import Hilbert24_Calibrated_Policy

/-!
H24 for the actual execution of a proof/certificate GENERATOR.

`next` denotes one actual primitive bit transition of that implementation,
including rule selection, cofactor acquisition, checking, and output/readback.
This machine is not an interpreter that merely executes the proof it emits.
The interpretation of a primitive tick is a source interface, not inferred
from a code-length grade or from the number of outer cofactor calls.

All construction below is recursion on the supplied LOCAL operational reserve.
No halting answer, complete run, minimum proof, or global clock is a field of
`Ranking`. The remaining source-uniform reserve field is named separately.
-/

namespace H24OperationalBridge

universe u v w

structure BitMachine (State : Type u) where
  next : State → Option State

structure Ranking {State : Type u} (M : BitMachine State) where
  reserve : State → Nat
  decrease : ∀ s t, M.next s = some t → reserve t < reserve s

/-- Actual tick count, constructed by following the original bit transition. -/
def remaining {State : Type u} {M : BitMachine State} (R : Ranking M)
    (s : State) : Nat :=
  match h : M.next s with
  | none => 0
  | some t => 1 + remaining R t
termination_by R.reserve s
decreasing_by exact R.decrease s t h

theorem remaining_halt {State : Type u} {M : BitMachine State} (R : Ranking M)
    (s : State) (h : M.next s = none) : remaining R s = 0 := by
  rw [remaining]
  split
  · rfl
  · rename_i t ht
    have impossible : (none : Option State) = some t := h.symm.trans ht
    cases impossible

theorem remaining_tick {State : Type u} {M : BitMachine State} (R : Ranking M)
    (s t : State) (h : M.next s = some t) :
    remaining R s = 1 + remaining R t := by
  rw [remaining]
  split
  · rename_i hn
    have impossible : (some t : Option State) = none := h.symm.trans hn
    cases impossible
  · rename_i q hq
    have equal : t = q := Option.some.inj (h.symm.trans hq)
    cases equal
    rfl

/-- The source operational grammar has exactly its original halt/tick rules. -/
inductive Rule {State : Type u} (M : BitMachine State) : Type u
  | halt (s : State) (actual : M.next s = none)
  | tick (s t : State) (actual : M.next s = some t)

def system {State : Type u} (M : BitMachine State) :
    Hilbert24Policy.RuleSystem State where
  Rule := Rule M
  conclusion
    | .halt s _ => s
    | .tick s _ _ => s
  arity
    | .halt _ _ => 0
    | .tick _ _ _ => 1
  premise
    | .halt _ _, i => Fin.elim0 i
    | .tick _ t _, _ => t
  charge
    | .halt _ _ => 0
    | .tick _ _ _ => 1

def calibration {State : Type u} {M : BitMachine State} (R : Ranking M) :
    Hilbert24Policy.Calibration (system M) where
  potential := remaining R
  slack := fun _ => 0
  local_identity := by
    intro r
    cases r with
    | halt s h =>
        change 0 = remaining R s
        exact (remaining_halt R s h).symm
    | tick s t h =>
        change 1 + remaining R t = remaining R s
        exact (remaining_tick R s t h).symm

def chosen {State : Type u} (M : BitMachine State) (s : State) :
    {r : Rule M // (system M).conclusion r = s} :=
  match h : M.next s with
  | none => ⟨.halt s h, rfl⟩
  | some t => ⟨.tick s t h, rfl⟩

def policy {State : Type u} {M : BitMachine State} (R : Ranking M) :
    Hilbert24Policy.TightPolicy (system M) (calibration R) where
  chosen := chosen M
  tight := fun _ => rfl
  rank := R.reserve
  decrease := by
    intro s
    unfold chosen
    split
    next h =>
      intro i
      exact Fin.elim0 i
    next t h =>
      intro _
      exact R.decrease s t h

/-- A source execution retains every actual intermediate state and transition. -/
inductive Execution {State : Type u} (M : BitMachine State) : State → Type u
  | halt (s : State) (actual : M.next s = none) : Execution M s
  | tick (s t : State) (actual : M.next s = some t)
      (tail : Execution M t) : Execution M s

def ticks {State : Type u} {M : BitMachine State} :
    {s : State} → Execution M s → Nat
  | _, .halt _ _ => 0
  | _, .tick _ _ _ tail => 1 + ticks tail

def finish {State : Type u} {M : BitMachine State} :
    {s : State} → Execution M s → State
  | _, .halt s _ => s
  | _, .tick _ _ _ tail => finish tail

theorem finish_halted {State : Type u} {M : BitMachine State} {s : State}
    (e : Execution M s) : M.next (finish e) = none := by
  induction e with
  | halt s h => exact h
  | tick s t h tail ih => exact ih

/-- Actual source-rule interpretation; it returns a run, not a mere cost. -/
def ruleReturn {State : Type u} {M : BitMachine State}
    (r : Rule M)
    (children : (i : Fin ((system M).arity r)) →
      Execution M ((system M).premise r i)) : Execution M ((system M).conclusion r) :=
  match r with
  | .halt s h => .halt s h
  | .tick s t h => .tick s t h (children ⟨0, Nat.zero_lt_succ 0⟩)

def decode {State : Type u} {M : BitMachine State} {s : State}
    (p : Hilbert24Policy.Derivation (system M) s) : Execution M s :=
  Hilbert24Policy.interpret (Execution M) ruleReturn p

theorem decode_ticks {State : Type u} {M : BitMachine State} {s : State}
    (p : Hilbert24Policy.Derivation (system M) s) :
    ticks (decode p) = Hilbert24Policy.work p := by
  induction p with
  | node r children ih =>
      cases r with
      | halt s h => rfl
      | tick s t h =>
          simpa [decode, ticks, Hilbert24Policy.work, system, Hilbert24Policy.sumFin]
            using congrArg (fun n => 1 + n) (ih ⟨0, Nat.zero_lt_succ 0⟩)

/-- H24's total constructor applied to the actual bit-machine source grammar. -/
def putRunInH24 {State : Type u} {M : BitMachine State} (R : Ranking M)
    (s : State) : Hilbert24Policy.OptimalReturn (system M) (calibration R) s :=
  Hilbert24Policy.constructMinimum (policy R) s

def sourceRun {State : Type u} {M : BitMachine State} (R : Ranking M)
    (s : State) : Execution M s := decode (putRunInH24 R s).derivation

theorem sourceRun_exact {State : Type u} {M : BitMachine State}
    (R : Ranking M) (s : State) : ticks (sourceRun R s) = remaining R s := by
  rw [sourceRun, decode_ticks]
  exact (putRunInH24 R s).exact_cost

theorem sourceRun_minimum {State : Type u} {M : BitMachine State}
    (R : Ranking M) (s : State)
    (q : Hilbert24Policy.Derivation (system M) s) :
    ticks (sourceRun R s) ≤ Hilbert24Policy.work q := by
  rw [sourceRun, decode_ticks]
  exact (putRunInH24 R s).optimal q

/-- Local one-bit decrease pays for all actual ticks by induction. -/
theorem remaining_le_reserve {State : Type u} {M : BitMachine State}
    (R : Ranking M) (s : State) : remaining R s ≤ R.reserve s := by
  generalize hr : R.reserve s = n
  induction n using Nat.strongRecOn generalizing s with
  | ind n ih =>
      cases h : M.next s with
      | none => rw [remaining_halt R s h]; exact Nat.zero_le _
      | some t =>
          rw [remaining_tick R s t h]
          have ht := R.decrease s t h
          have it : remaining R t ≤ R.reserve t :=
            ih (R.reserve t) (by simpa [hr] using ht) t rfl
          exact Nat.le_trans (Nat.add_le_add_left it 1)
            (by simpa only [Nat.succ_eq_add_one, Nat.add_comm, hr] using Nat.succ_le_of_lt ht)

theorem sourceRun_paid {State : Type u} {M : BitMachine State}
    (R : Ranking M) (s : State) : ticks (sourceRun R s) ≤ R.reserve s := by
  rw [sourceRun_exact]
  exact remaining_le_reserve R s

/-- The executable bounded wrapper uses input and fuel, never a negative proof. -/
def runFor {State : Type u} (M : BitMachine State) : Nat → State → State
  | 0, s => s
  | n+1, s => match M.next s with
    | none => s
    | some t => runFor M n t

theorem runFor_halt {State : Type u} (M : BitMachine State) (n : Nat)
    (s : State) (h : M.next s = none) : runFor M n s = s := by
  cases n with
  | zero => rfl
  | succ n => rw [runFor, h]

theorem execution_runFor {State : Type u} {M : BitMachine State} {s : State}
    (e : Execution M s) : runFor M (ticks e) s = finish e := by
  induction e with
  | halt s h => rfl
  | tick s t h tail ih =>
      simpa [ticks, finish, Nat.add_comm, runFor, h] using ih

theorem runFor_add {State : Type u} (M : BitMachine State) (m n : Nat)
    (s : State) : runFor M (m+n) s = runFor M n (runFor M m s) := by
  induction m generalizing s with
  | zero => exact congrArg (fun k => runFor M k s) (Nat.zero_add n)
  | succ m ih =>
      cases h : M.next s with
      | none =>
          rw [runFor_halt M (m+1+n) s h, runFor_halt M (m+1) s h,
            runFor_halt M n s h]
      | some t => simpa [Nat.succ_add, runFor, h] using ih t

theorem execution_within {State : Type u} {M : BitMachine State} {s : State}
    (e : Execution M s) (budget : Nat) (h : ticks e ≤ budget) :
    runFor M budget s = finish e := by
  have splitBudget : ticks e + (budget - ticks e) = budget :=
    Hilbert24Policy.add_sub_of_le_constructive h
  rw [← splitBudget, runFor_add, execution_runFor]
  exact runFor_halt M (budget - ticks e) (finish e) (finish_halted e)

/-- A simulation maps each actual counted tick, including its source labels. -/
def mapExecution {S : Type u} {T : Type v} {M : BitMachine S} {N : BitMachine T}
    (f : S → T) (step : ∀ s, (M.next s).map f = N.next (f s)) :
    {s : S} → Execution M s → Execution N (f s)
  | _, .halt s h => .halt (f s) (by rw [← step, h]; rfl)
  | _, .tick s t h tail => .tick (f s) (f t)
      (by rw [← step, h]; rfl) (mapExecution f step tail)

theorem mapExecution_ticks {S : Type u} {T : Type v}
    {M : BitMachine S} {N : BitMachine T}
    (f : S → T) (step : ∀ s, (M.next s).map f = N.next (f s))
    {s : S} (e : Execution M s) : ticks (mapExecution f step e) = ticks e := by
  induction e with
  | halt s h => rfl
  | tick s t h tail ih => exact congrArg (fun n => 1+n) ih

theorem mapExecution_finish {S : Type u} {T : Type v}
    {M : BitMachine S} {N : BitMachine T}
    (f : S → T) (step : ∀ s, (M.next s).map f = N.next (f s))
    {s : S} (e : Execution M s) : finish (mapExecution f step e) = f (finish e) := by
  induction e with
  | halt s h => rfl
  | tick s t h tail ih => exact ih

inductive Reachable {S : Type u} (M : BitMachine S) (start : S) : S → Prop
  | initial : Reachable M start start
  | advance {s t : S} : Reachable M start s → M.next s = some t → Reachable M start t

def reachedMachine {S : Type u} (M : BitMachine S) (start : S) :
    BitMachine {s : S // Reachable M start s} where
  next q := match h : M.next q.val with
    | none => none
    | some t => some ⟨t, Reachable.advance q.property h⟩

def reachedStart {S : Type u} (M : BitMachine S) (start : S) :
    {s : S // Reachable M start s} := ⟨start, .initial⟩

theorem reached_projection {S : Type u} (M : BitMachine S) (start : S)
    (q : {s : S // Reachable M start s}) :
    ((reachedMachine M start).next q).map Subtype.val = M.next q.val := by
  dsimp only [reachedMachine]
  split
  · rename_i h
    exact h.symm
  · rename_i t h
    exact h.symm

def eraseReach {S : Type u} {M : BitMachine S} {start : S}
    {q : {s : S // Reachable M start s}} (e : Execution (reachedMachine M start) q) :
    Execution M q.val := mapExecution Subtype.val (reached_projection M start) e

theorem runFor_reachable {S : Type u} (M : BitMachine S) (start : S)
    (n : Nat) (s : S) (hs : Reachable M start s) :
    Reachable M start (runFor M n s) := by
  induction n generalizing s with
  | zero => exact hs
  | succ n ih =>
      cases h : M.next s with
      | none => simpa [runFor, h] using hs
      | some t => simpa [runFor, h] using ih t (Reachable.advance hs h)

/-- The original checked-negative generator implementation, fixed before inputs.
    `machine.next` is its complete actual bit transition. It includes execution
    of rule selection, cofactor acquisition, checking, and readback. A terminal
    here is a recognized checked negative event, not an unverified label. On
    positive inputs the monitored machine may keep running. `readReceipt`
    interprets only an ACTUALLY reached terminal state; no receipt is an input. -/
structure GeneratorImplementation (Input : Type u) (State : Type v) where
  machine : BitMachine State
  initial : Input → State
  inputBits : Input → Nat
  Negative : Input → Prop
  SourceReceipt : Input → Type w
  readReceipt : ∀ C s, Reachable machine (initial C) s →
    machine.next s = none → SourceReceipt C
  receipt_sound : ∀ C, SourceReceipt C → Negative C

abbrev ReachMachine {Input : Type u} {State : Type v}
    (G : GeneratorImplementation.{u,v,w} Input State) (C : Input) :=
  reachedMachine G.machine (G.initial C)

abbrev Initial {Input : Type u} {State : Type v}
    (G : GeneratorImplementation.{u,v,w} Input State) (C : Input) :=
  reachedStart G.machine (G.initial C)

/-- This is the explicit remaining SOURCE field. c,d are chosen once, before
    every C. Ranking is required only for reached states on Negative inputs.
    It does not assert a bound on the emitted proof's code grade. -/
structure UniformReserve {Input : Type u} {State : Type v}
    (G : GeneratorImplementation.{u,v,w} Input State) where
  coefficient : Nat
  degree : Nat
  positive : 0 < coefficient
  ranking : ∀ C, G.Negative C → Ranking (ReachMachine G C)
  initial_bound : ∀ C h, (ranking C h).reserve (Initial G C) ≤
    coefficient * (G.inputBits C + 1)^degree

/-- Named open source judgement, ready for an exact torser presentation. -/
def UniformReserveTarget {Input : Type u} {State : Type v}
    (G : GeneratorImplementation.{u,v,w} Input State) : Prop := Nonempty (UniformReserve G)

def deadline {Input : Type u} {State : Type v}
    {G : GeneratorImplementation.{u,v,w} Input State} (B : UniformReserve G) (C : Input) :=
  B.coefficient * (G.inputBits C + 1)^B.degree

/-- The explicit H24 entry point for the bridge. Negative evidence occurs only
    in the termination proof interface. The bit transition remains G.machine. -/
def putBridgeInH24 {Input : Type u} {State : Type v}
    {G : GeneratorImplementation.{u,v,w} Input State} (B : UniformReserve G)
    (C : Input) (h : G.Negative C) := putRunInH24 (B.ranking C h) (Initial G C)

def generatedRun {Input : Type u} {State : Type v}
    {G : GeneratorImplementation.{u,v,w} Input State} (B : UniformReserve G)
    (C : Input) (h : G.Negative C) : Execution G.machine (G.initial C) :=
  eraseReach (decode (putBridgeInH24 B C h).derivation)

theorem generatedRun_grade {Input : Type u} {State : Type v}
    {G : GeneratorImplementation.{u,v,w} Input State} (B : UniformReserve G)
    (C : Input) (h : G.Negative C) : ticks (generatedRun B C h) =
      Hilbert24Policy.work (putBridgeInH24 B C h).derivation := by
  rw [generatedRun, eraseReach, mapExecution_ticks, decode_ticks]

theorem generatedRun_deadline {Input : Type u} {State : Type v}
    {G : GeneratorImplementation.{u,v,w} Input State} (B : UniformReserve G)
    (C : Input) (h : G.Negative C) : ticks (generatedRun B C h) ≤ deadline B C := by
  rw [generatedRun_grade]
  have paid := sourceRun_paid (B.ranking C h) (Initial G C)
  have paidH24 : Hilbert24Policy.work (putBridgeInH24 B C h).derivation ≤
      (B.ranking C h).reserve (Initial G C) := by
    simpa [sourceRun, decode_ticks, putBridgeInH24] using paid
  exact Nat.le_trans paidH24 (B.initial_bound C h)

theorem generatedRun_minimum {Input : Type u} {State : Type v}
    {G : GeneratorImplementation.{u,v,w} Input State} (B : UniformReserve G)
    (C : Input) (h : G.Negative C)
    (q : Hilbert24Policy.Derivation (system (ReachMachine G C)) (Initial G C)) :
    ticks (generatedRun B C h) ≤ Hilbert24Policy.work q := by
  rw [generatedRun_grade]
  exact (putBridgeInH24 B C h).optimal q

theorem generatedRun_is_actual_wrapper {Input : Type u} {State : Type v}
    {G : GeneratorImplementation.{u,v,w} Input State} (B : UniformReserve G)
    (C : Input) (h : G.Negative C) :
    runFor G.machine (deadline B C) (G.initial C) = finish (generatedRun B C h) :=
  execution_within (generatedRun B C h) (deadline B C) (generatedRun_deadline B C h)

/-- The clock conclusion retains the original source machine and input. -/
structure UniformDeadline {Input : Type u} {State : Type v}
    (G : GeneratorImplementation.{u,v,w} Input State) where
  coefficient : Nat
  degree : Nat
  positive : 0 < coefficient
  hit : ∀ C, G.Negative C →
    G.machine.next (runFor G.machine (coefficient * (G.inputBits C + 1)^degree)
      (G.initial C)) = none

def UniformDeadlineTarget {Input : Type u} {State : Type v}
    (G : GeneratorImplementation.{u,v,w} Input State) : Prop := Nonempty (UniformDeadline G)

def bridgeDeadline {Input : Type u} {State : Type v}
    {G : GeneratorImplementation.{u,v,w} Input State} (B : UniformReserve G) :
    UniformDeadline G where
  coefficient := B.coefficient
  degree := B.degree
  positive := B.positive
  hit C h := by
    change G.machine.next (runFor G.machine (deadline B C) (G.initial C)) = none
    rw [generatedRun_is_actual_wrapper B C h]
    exact finish_halted (generatedRun B C h)

theorem named_source_bridge {Input : Type u} {State : Type v}
    (G : GeneratorImplementation.{u,v,w} Input State) :
    UniformReserveTarget G → UniformDeadlineTarget G := by
  intro ⟨B⟩
  exact ⟨bridgeDeadline B⟩

def returnedReceipt {Input : Type u} {State : Type v}
    {G : GeneratorImplementation.{u,v,w} Input State} (B : UniformReserve G)
    (C : Input) (h : G.Negative C) : G.SourceReceipt C :=
  G.readReceipt C (runFor G.machine (deadline B C) (G.initial C))
    (runFor_reachable G.machine (G.initial C) (deadline B C) (G.initial C) .initial)
    ((bridgeDeadline B).hit C h)

/-- One executable timeout decision from the constructed deadline. It receives
    C, fixed A=G.machine and c,d. No negative evidence is an executed input. -/
def decideNegative {Input : Type u} {State : Type v}
    {G : GeneratorImplementation.{u,v,w} Input State} (D : UniformDeadline G)
    (C : Input) : Decidable (G.Negative C) :=
  let n := D.coefficient * (G.inputBits C + 1)^D.degree
  let s := runFor G.machine n (G.initial C)
  match h : G.machine.next s with
  | none => isTrue (G.receipt_sound C (G.readReceipt C s
      (runFor_reachable G.machine (G.initial C) n (G.initial C) .initial) h))
  | some t => isFalse (fun negative => by
      have stop := D.hit C negative
      change G.machine.next s = none at stop
      rw [h] at stop
      cases stop)

/-- Exact retained native presentation. A separate native implementation must
    supply its actual microstep costs; encode/decode computation is not silently
    declared free by this record. Here the SAME source execution is represented. -/
structure ExactChart (Source : Type u) (Native : Type v) where
  write : Source → Native
  read : Native → Source
  read_write : ∀ x, read (write x) = x
  write_read : ∀ y, write (read y) = y

def nativeMachine {S : Type u} {N : Type v} (E : ExactChart S N)
    (M : BitMachine S) : BitMachine N where
  next n := (M.next (E.read n)).map E.write

theorem native_tick_square {S : Type u} {N : Type v} (E : ExactChart S N)
    (M : BitMachine S) (s : S) :
    (M.next s).map E.write = (nativeMachine E M).next (E.write s) := by
  change (M.next s).map E.write = (M.next (E.read (E.write s))).map E.write
  rw [E.read_write]

def nativeRun {S : Type u} {N : Type v} (E : ExactChart S N)
    {M : BitMachine S} {s : S} (e : Execution M s) :
    Execution (nativeMachine E M) (E.write s) :=
  mapExecution E.write (native_tick_square E M) e

theorem nativeRun_grade {S : Type u} {N : Type v} (E : ExactChart S N)
    {M : BitMachine S} {s : S} (e : Execution M s) : ticks (nativeRun E e) = ticks e :=
  mapExecution_ticks E.write (native_tick_square E M) e

theorem nativeRun_return {S : Type u} {N : Type v} (E : ExactChart S N)
    {M : BitMachine S} {s : S} (e : Execution M s) :
    E.read (finish (nativeRun E e)) = finish e := by
  rw [nativeRun, mapExecution_finish, E.read_write]

def putNativeBridgeInH24 {Input : Type u} {State : Type v} {Native : Type w}
    {G : GeneratorImplementation Input State} (E : ExactChart State Native)
    (B : UniformReserve G) (C : Input) (h : G.Negative C) :=
  nativeRun E (generatedRun B C h)

theorem native_bridge_deadline {Input : Type u} {State : Type v} {Native : Type w}
    {G : GeneratorImplementation Input State} (E : ExactChart State Native)
    (B : UniformReserve G) (C : Input) (h : G.Negative C) :
    ticks (putNativeBridgeInH24 E B C h) ≤ deadline B C := by
  rw [putNativeBridgeInH24, nativeRun_grade]
  exact generatedRun_deadline B C h

/-- The WHOLE source reserve witness, including fixed c,d and its universal
    input family, may be represented. A partial input-specific fragment is not
    substituted for this source judgement. -/
def NativeReserveTarget {Input : Type u} {State : Type v} {Native : Type w}
    {G : GeneratorImplementation Input State}
    (_E : ExactChart (UniformReserve G) Native) : Prop := Nonempty Native

theorem native_reserve_target_exact {Input : Type u} {State : Type v} {Native : Type w}
    {G : GeneratorImplementation Input State} (E : ExactChart (UniformReserve G) Native) :
    NativeReserveTarget E ↔ UniformReserveTarget G := by
  constructor
  · intro ⟨n⟩; exact ⟨E.read n⟩
  · intro ⟨b⟩; exact ⟨E.write b⟩

theorem native_reserve_readback {Input : Type u} {State : Type v} {Native : Type w}
    {G : GeneratorImplementation Input State} (E : ExactChart (UniformReserve G) Native)
    (B : UniformReserve G) : E.read (E.write B) = B := E.read_write B

def constructFromNativeReserve {Input : Type u} {State : Type v} {Native : Type w}
    {G : GeneratorImplementation Input State} (E : ExactChart (UniformReserve G) Native)
    (n : Native) : UniformDeadline G := bridgeDeadline (E.read n)

end H24OperationalBridge
