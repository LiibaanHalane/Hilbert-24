"""Exact finite ledger checks for the H24 operational clock bridge.

This module checks finite, supplied traces. It does not test a universal CNF
deadline or use host-Python elapsed time as a bit-clock measurement.
The executable fixtures use finite-control, bounded-wire gate primitives.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
import json
from pathlib import Path
from typing import Callable, Iterable


COMPONENTS = (
    "parse", "compile", "route", "address", "lookup", "arithmetic",
    "select_rule", "acquire", "produce", "verify", "readback", "cleanup",
)


class InvalidLedger(ValueError):
    pass


@dataclass(frozen=True)
class Polynomial:
    coefficient: int
    degree: int

    def __post_init__(self) -> None:
        if self.coefficient < 0 or self.degree < 0:
            raise ValueError("Polynomial parameters must be natural numbers")

    def value(self, source_bits: int) -> int:
        if source_bits < 0:
            raise ValueError("Source length must be nonnegative")
        return self.coefficient * (source_bits + 1) ** self.degree

    def plus(self, other: "Polynomial") -> "Polynomial":
        return Polynomial(self.coefficient + other.coefficient,
                          max(self.degree, other.degree))

    def times(self, other: "Polynomial") -> "Polynomial":
        return Polynomial(self.coefficient * other.coefficient,
                          self.degree + other.degree)

    def after(self, inner: "Polynomial") -> "Polynomial":
        # self(inner(N)) <= c*(a+1)^d*(N+1)^(e*d).
        return Polynomial(self.coefficient * (inner.coefficient + 1) ** self.degree,
                          self.degree * inner.degree)

    def maximum_bound(self, other: "Polynomial") -> "Polynomial":
        return Polynomial(max(self.coefficient, other.coefficient),
                          max(self.degree, other.degree))


def sum_polynomials(values: Iterable[Polynomial]) -> Polynomial:
    result = Polynomial(0, 0)
    for p in values:
        result = result.plus(p)
    return result


def choice_bound(selector: Polynomial, branches: tuple[Polynomial, ...]) -> Polynomial:
    """Pay an effective selector and its selected, source-valid branch."""
    if not branches:
        raise ValueError("An executable choice needs an admitted branch")
    maximum = branches[0]
    for branch in branches[1:]:
        maximum = maximum.maximum_bound(branch)
    return selector.plus(maximum)


def complete_clock_bound(
    setup: Polynomial,
    events: Polynomial,
    operand_size: Polynomial,
    per_event_components: dict[str, Polynomial],
    final_components: dict[str, Polynomial],
) -> Polynomial:
    """Construct a monomial bound after all stated local bounds are supplied."""
    if set(per_event_components) - set(COMPONENTS):
        raise ValueError("Unknown per-event cost component")
    if set(final_components) - set(COMPONENTS):
        raise ValueError("Unknown final cost component")
    local = sum_polynomials(p.after(operand_size)
                            for p in per_event_components.values())
    final = sum_polynomials(final_components.values())
    return setup.plus(events.times(local)).plus(final)


@dataclass(frozen=True)
class LedgerStep:
    state_before: str
    state_after: str
    components: dict[str, int]
    phi_before: int
    phi_after: int
    amortized: int  # signed in the general source identity
    event_after: bool = False

    @property
    def actual(self) -> int:
        return sum(self.components.values())


def check_ledger(
    *, program: str, source: str, steps: tuple[LedgerStep, ...],
    initial_phi: int, initial_bound: int, amortized_budget: int,
    complete: bool, terminal_check: Callable[[str, str], bool],
    claimed_work: int | None = None,
    initial_state: str | None = None, initial_event: bool = False,
) -> dict:
    """Check balance, every-prefix reserve, event boundary and exact return.

    Source and program identities are retained. Costs must already refer to a
    common declared primitive unit, with complete local microtrace evidence.
    This checker validates their accounting; the transition checker below
    supplies such evidence for the bounded-wire fixtures.
    """
    if not program or not source:
        raise InvalidLedger("Original source and fixed program must be retained")
    if min(initial_phi, initial_bound, amortized_budget) < 0:
        raise InvalidLedger("Initial potential and budget must be nonnegative")
    if initial_phi > initial_bound:
        raise InvalidLedger("Initial potential exceeds its original bound")
    phi = initial_phi
    spent = 0
    issued = 0
    last_state = initial_state
    event_seen = initial_event
    if initial_event and (initial_state is None or not terminal_check(source, initial_state)):
        raise InvalidLedger("The initial checked event fails its original-source return")
    reserves = [phi + amortized_budget]
    local_excesses = []
    for index, step in enumerate(steps):
        if event_seen:
            raise InvalidLedger("Trace must stop at its first checked event")
        if last_state is not None and step.state_before != last_state:
            raise InvalidLedger("Adjacent original states do not agree")
        if step.phi_before != phi:
            raise InvalidLedger("Adjacent potential fields do not agree")
        if step.phi_after < 0:
            raise InvalidLedger("Negative remaining frontier potential")
        if set(step.components) - set(COMPONENTS):
            raise InvalidLedger("Unknown cost component")
        if any(c < 0 for c in step.components.values()):
            raise InvalidLedger("Executed work cannot be negative")
        if step.actual < 1:
            raise InvalidLedger("A live execution segment must pay positive work")
        if step.actual + step.phi_after != step.amortized + phi:
            raise InvalidLedger("Local actual/potential/amortized balance fails")
        before_reserve = phi + amortized_budget - issued
        spent += step.actual
        issued += step.amortized
        if issued > amortized_budget:
            raise InvalidLedger("A finite prefix exceeds the fixed slack budget")
        phi = step.phi_after
        after_reserve = phi + amortized_budget - issued
        if after_reserve < 0:
            raise InvalidLedger("The constructed combined reserve is negative")
        if step.actual + after_reserve != before_reserve:
            raise InvalidLedger("The derived actual-work reserve does not telescope")
        reserves.append(after_reserve)
        local_excesses.append(step.amortized)
        event_seen = step.event_after
        last_state = step.state_after
        if event_seen and not terminal_check(source, last_state):
            raise InvalidLedger("The terminal event fails its original-source return")
    if complete and not event_seen:
        raise InvalidLedger("A completed return requires the checked event")
    if claimed_work is not None and claimed_work != spent:
        raise InvalidLedger("The claimed grade is not this execution's actual work")
    if spent + reserves[-1] != initial_phi + amortized_budget:
        raise InvalidLedger("Whole-trace telescope fails")
    return {
        "program": program, "source": source, "complete": complete,
        "checked_event": event_seen, "actual_work": spent,
        "amortized_work": issued, "initial_phi": initial_phi,
        "final_phi": phi, "initial_reserve": reserves[0],
        "final_reserve": reserves[-1], "reserve_by_boundary": reserves,
        "uniform_instance_bound": initial_bound + amortized_budget,
        "local_amortized_charges": local_excesses,
        "clock_unit": "declared primitive transitions, not host wall time",
    }


@dataclass(frozen=True)
class Gate:
    operation: str
    wires: tuple[int, ...]

    def apply(self, value: tuple[int, ...]) -> tuple[int, ...]:
        if any(x not in (0, 1) for x in value):
            raise ValueError("Gate configurations are binary")
        if any(i < 0 or i >= len(value) for i in self.wires):
            raise ValueError("Gate address outside this fixed finite register")
        if len(set(self.wires)) != len(self.wires):
            raise ValueError("The local primitive requires distinct wires")
        out = list(value)
        if self.operation == "cnot" and len(self.wires) == 2:
            a, t = self.wires
            out[t] ^= out[a]
        elif self.operation == "toffoli" and len(self.wires) == 3:
            a, b, t = self.wires
            out[t] ^= out[a] & out[b]
        elif self.operation == "fredkin" and len(self.wires) == 3:
            c, a, b = self.wires
            if out[c]:
                out[a], out[b] = out[b], out[a]
        else:
            raise ValueError("Unknown bounded-wire primitive")
        return tuple(out)


def four_port_program() -> tuple[Gate, ...]:
    def or_into(a: int, b: int, t: int) -> tuple[Gate, ...]:
        return Gate("cnot", (a, t)), Gate("cnot", (b, t)), Gate("toffoli", (a, b, t))
    forward = or_into(0, 1, 5) + or_into(2, 3, 6) + or_into(5, 6, 7)
    return forward + (Gate("cnot", (7, 4)),) + tuple(reversed(forward))


def gate_trace(program: tuple[Gate, ...], initial: tuple[int, ...]) -> tuple[LedgerStep, ...]:
    current = initial
    result = []
    def name(pc: int, data: tuple[int, ...]) -> str:
        return f"pc={pc};bits={''.join(map(str, data))}"
    for i, gate in enumerate(program):
        after = gate.apply(current)
        # The fixture's remaining program is a literal finite-control suffix.
        result.append(LedgerStep(
            name(i, current), name(i + 1, after),
            {"acquire" if i < 10 else "cleanup": 1},
            len(program) - i, len(program) - i - 1, 0,
            event_after=i + 1 == len(program),
        ))
        current = after
    return tuple(result)


def run_diagnostics() -> dict:
    receipts = {}
    initial = (0, 1, 0, 1, 0, 0, 0, 0)
    cell = four_port_program()
    assert len(cell) == 19
    source = "original-eight-wire-input:01010000"
    cell_expected = f"pc=19;bits=01011000"
    receipts["finite_19_step_original_return"] = check_ledger(
        program="fixed-eight-wire-four-port-v1", source=source,
        steps=gate_trace(cell, initial), initial_phi=19, initial_bound=19,
        amortized_budget=0, complete=True,
        terminal_check=lambda original, final: original == source and final == cell_expected,
    )
    roundtrip = cell + tuple(reversed(cell))
    trace = gate_trace(roundtrip, initial)
    receipts["inverse_pair_keeps_38_paid_steps"] = check_ledger(
        program="fixed-eight-wire-four-port-and-inverse-v1", source=source,
        steps=trace, initial_phi=38, initial_bound=38, amortized_budget=0,
        complete=True,
        terminal_check=lambda original, final: original == source and final == "pc=38;bits=01010000",
    )
    failures = {}
    try:
        check_ledger(program="fixed-roundtrip", source=source, steps=trace,
                     initial_phi=38, initial_bound=38, amortized_budget=0,
                     complete=True, terminal_check=lambda _, final: final == "pc=38;bits=01010000",
                     claimed_work=0)
    except InvalidLedger as error:
        failures["inverse_identity_is_zero_runtime"] = str(error)
    try:
        check_ledger(program="fixed-cell", source=source, steps=gate_trace(cell, initial),
                     initial_phi=19, initial_bound=19, amortized_budget=0,
                     complete=True, terminal_check=lambda _, final: final == cell_expected,
                     claimed_work=5)
    except InvalidLedger as error:
        failures["five_symbol_candidate_grade_is_19_step_clock"] = str(error)
    try:
        check_ledger(program="unfinished-prefix", source=source, steps=(),
                     initial_phi=0, initial_bound=0, amortized_budget=0,
                     complete=True, terminal_check=lambda *_: True)
    except InvalidLedger as error:
        failures["completed_run_bound_supplies_event_without_progress"] = str(error)
    try:
        check_ledger(program="unpaid-live-step", source=source,
                     steps=(LedgerStep("s0", "s1", {"acquire": 1}, 0, 0, 1),),
                     initial_phi=0, initial_bound=0, amortized_budget=0,
                     complete=False, terminal_check=lambda *_: True)
    except InvalidLedger as error:
        failures["nonnegative_slack_alone_is_a_zero_clock"] = str(error)
    try:
        check_ledger(program="zero-price-live-loop", source=source,
                     steps=(LedgerStep("s", "s", {}, 0, 0, 0),),
                     initial_phi=0, initial_bound=0, amortized_budget=0,
                     complete=False, terminal_check=lambda *_: True)
    except InvalidLedger as error:
        failures["zero_price_live_steps_prove_a_tick_deadline"] = str(error)
    receipts["signed_amortized_refund_keeps_total_reserve_decreasing"] = check_ledger(
        program="two-costed-transitions", source="fixed-original-record",
        steps=(LedgerStep("s0", "s1", {"acquire": 1}, 2, 0, -1),
               LedgerStep("s1", "event", {"verify": 1}, 0, 0, 1, True)),
        initial_phi=2, initial_bound=2, amortized_budget=0, complete=True,
        terminal_check=lambda original, final: original == "fixed-original-record" and final == "event",
    )
    # Original frontier example: all three calibration slacks vanish.
    receipts["tight_original_frontier"] = check_ledger(
        program="declared-original-frontier-grammar", source="judgement:A",
        steps=(LedgerStep("[A]", "[B,B]", {"produce": 1}, 5, 4, 0),
               LedgerStep("[B,B]", "[B]", {"produce": 2}, 4, 2, 0),
               LedgerStep("[B]", "[]", {"produce": 2}, 2, 0, 0, True)),
        initial_phi=5, initial_bound=5, amortized_budget=0, complete=True,
        terminal_check=lambda original, final: original == "judgement:A" and final == "[]",
    )
    receipts["tight_original_frontier"]["clock_unit"] = "declared original rule charge; bit-clock use requires its microtrace realization"
    bound = complete_clock_bound(
        Polynomial(3, 2), Polynomial(2, 3), Polynomial(4, 2),
        {"lookup": Polynomial(2, 1), "arithmetic": Polynomial(3, 2), "verify": Polynomial(1, 1)},
        {"readback": Polynomial(5, 2), "cleanup": Polynomial(1, 3)},
    )
    receipts["constructed_polynomial_closure"] = {
        "bound": asdict(bound),
        "derivation": "setup + event_count*(lookup+arithmetic+verify)(operand_size) + readback + cleanup",
        "meaning": "Explicit constructor from supplied uniform local bounds; no source-wide event-count bound is inferred",
    }
    assert len(failures) == 5
    return {"status": "pass", "scope": "Exact finite accounting and original-return diagnostics", "receipts": receipts,
            "rejected_false_grade_or_event_swaps": failures,
            "universal_deadline_tested": False, "host_runtime_reported_as_bit_work": False}


if __name__ == "__main__":
    result = run_diagnostics()
    target = Path(__file__).with_name("Bridge_Clock_Ledger_Receipt.json")
    target.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "receipt": str(target),
                      "accepted_receipts": len(result["receipts"]),
                      "false_swaps_rejected": len(result["rejected_false_grade_or_event_swaps"])}))
