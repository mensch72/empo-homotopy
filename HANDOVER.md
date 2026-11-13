# Handover and log

To resume in a new session/account: read `CLAUDE.md`, this file, `notes/STATEMENTS.md`,
`protocol/PROJECT.md`, `protocol/REVIEW_LEDGER.md` (findings F1–F4).  Setup: install elan,
`lake exe cache get && lake build`; `pip install numpy scipy matplotlib`.
Paper source for the equations: `curl -L https://arxiv.org/e-print/2508.00159 | tar xz` (Table `tab:equations`).

## Owner decisions (2026-11-13)
- Protocol E.  Target system: paper's robot side (eqs. 4, 5, 7–9) + proposal's power-mean eq. (5)
  for V_h; alternative trajectory-goal form (7T).  See STATEMENTS §0.
- Push often; keep this log current.

## State
- Lean, audited (non-author statement audit passed): LOC-1..4 (proposal's variant only, not the
  target), LEH-1..3, BEL-1, BEL-2; SYS-1..3, SYS-W, SYS-L, SYS-T at commit d2dda7a (after F4 rework,
  re-audited); SYS-6 (three solutions of a cyclic two-state game at β = 2) at c4556d0, audited.
- Numerics: `numerics/REPORT.md` (proposal's variant); `numerics/cyclic/` (target system) in progress.
- Not a completed Protocol E release (no clean-checkout review, manifest, manuscript).

## In flight when this was written
Owner (11-13): main objective = something that helps solving these systems; choice of next steps left to the agent.
1. Solver agent: Python package `solver/empo_solver/` (backward induction, finite-horizon unrolling,
   arclength continuation in β / γ_r / γ_h, multistart, diagnostics; tests incl. the SYS-6 instance;
   `solver/README.md`).  If lost: spec = this list + STATEMENTS §0; reuse `numerics/cyclic/system.py`.
2. Lean author agent: `EmpoHomotopy/Trajectory.lean` — TRJ-1 (X = 1 + γ M X has exactly one solution,
   1 ≤ X ≤ 1/(1−γm), if row sums ≤ m and γm < 1), TRJ-2 (row sums of max_{a_h} P^ζ ≤ |A_h|), TRJ-3
   (sys1/sys2 for the trajectory form without evaluation hypothesis), TRJ-4 (is Brouwer in Mathlib?).
3. Afterwards: non-author statement audit of Trajectory.lean; update STATEMENTS marks and ledger.

## Next (in order)
- Power-mean Φ instance in Lean (definition, locality); SYS-P (is V_h unique given π_r for κ, θ < 1?).
- SYS-4 existence (ε-regularisation or positivity conditions); SYS-5 guided by the numerics.
- Path theorems (PATH-1..3) for the target system; Herings–Peeters framework; system with eq. (6)
  of the proposal (information-theoretic empowerment); Year-2 low-rank part.

## Log
- 11-13: repo set up; release-candidate 0.1 lemmas proved and audited; F1 (proposal vs paper eq. for
  Q_r) → owner chose paper; then pdf eq. (5) for V_h; then (7T) added; abstract system proved;
  audit found F4; rework started.
- 11-13 later: F4 fixed and re-audited; statements and ledger updated.
- 11-13 later: cyclic numerics done (SYS-N); two-state non-uniqueness instance found, re-derived by
  hand and checked in exact rational arithmetic (SYS-6); Lean proof started.
- 11-13 later: SYS-6 proved in Lean (three solutions) and audited.
- 11-13 later: owner: (7T) gets a discount γ_h; acyclicity only as an optional extra condition.
  Existence for small γ_h recorded as SYS-TE (informal).
