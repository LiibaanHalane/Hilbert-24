TORSER → H24 → ORIGINAL CLOCK

Start with Torser_H24_Clock_Bridge.html or Torser_H24_Clock_Bridge.txt.

Main formal entry: H24ClockCredit.putFrontierBridgeInH24
Actual decoder: H24OperationalBridge.generatedRun
Exact converse: reserve_target_iff_deadline_target
Native source: formal/hets/Native_Clock_Torser.het

The formal/lean folder supplies the unchanged generic H24 dependency and all
new imports. Use Lean 4.19.0; TORSER_LEAN=/path/to/lean python replay_lean.py.
No mathlib or choice axiom is needed by the central natural frontier route.

For Hets, set TORSER_HETS_BIN to a directory containing the intended Hets,
EProver and SPASS executables, then run formal/hets/replay_casl.py. The primary
CASL file imports the original Native_Shortest_Proof.het from its included deps.
Hets proof markers retain their status; exact current outcomes are recorded in
formal/hets/checks/casl-replay.json. 33 of 39
selected obligations were discharged by that recorded focused run.
The six remaining automated goals have complete written proofs and precisely
scoped independent algebra checks in formal/hets/VERIFICATION.json and README.md.

The ordered-ring and frame identities are checked by
formal/hets/verify_native_algebra.py using included unchanged source modules.
The actual clock ledger checker is checks/bridge_clock_ledger.py.

Fresh checks: 69 core/converse declarations and 7 additional central frontier
results have empty axiom dependency lists. Optional signed-integer and product
arithmetic use propext and Quot.sound; exact outputs are retained. No additional
problem axiom or Classical.choice is introduced.

The target is the fixed generator's original complete execution. The code
constructs the bridge, its native return and H24 policy instance. The full
all-CNF uniform frontier account remains the explicit source/native judgement.
