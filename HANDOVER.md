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
  target), LEH-1..3, BEL-1, BEL-2; `sys1`, `sys2`, SYS-L, SYS-T at commit 4068309.
- Finding F4: `sys3` (acyclic uniqueness) at 4068309 is vacuous (no terminal states).  §0 corrected.
- Numerics: `numerics/REPORT.md` (proposal's variant); `numerics/cyclic/` (target system) in progress.
- Not a completed Protocol E release (no clean-checkout review, manifest, manuscript).

## In flight when this was written
1. Lean author agent: rework `EmpoHomotopy/System.lean` for terminal states; re-prove sys1–3; add
   non-vacuity witnesses `sys1_nonvacuous`, `sys3_nonvacuous`; `trajΨ`.  If lost: redo from
   STATEMENTS §0 (targets SYS-1..3, SYS-W) on top of the last pushed System.lean.
2. Numerics agent: `numerics/cyclic/` — search small cyclic games for multiple solutions (linear,
   power-mean, trajectory variants), tracer comparison, `numerics/cyclic/REPORT.md`.
3. After 1: a fresh non-author statement audit of the reworked System.lean (all roots again, since
   `IsSolution` changed), then update STATEMENTS marks and the ledger's formal-roots table.

## Next (in order)
- Power-mean Φ instance in Lean (definition, locality); SYS-P (is V_h unique given π_r for κ, θ < 1?).
- SYS-4 existence (ε-regularisation or positivity conditions); SYS-5 guided by the numerics.
- Path theorems (PATH-1..3) for the target system; Herings–Peeters framework; system with eq. (6)
  of the proposal (information-theoretic empowerment); Year-2 low-rank part.

## Log
- 11-13: repo set up; release-candidate 0.1 lemmas proved and audited; F1 (proposal vs paper eq. for
  Q_r) → owner chose paper; then pdf eq. (5) for V_h; then (7T) added; abstract system proved;
  audit found F4; rework started.
