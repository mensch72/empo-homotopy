# Handover (2026-11-13)

Read `CLAUDE.md`, `notes/STATEMENTS.md`, `protocol/PROJECT.md`, `protocol/REVIEW_LEDGER.md`.

State: release candidate 0.1.  Lean (`EmpoHomotopy/`): LOC-1..4, LEH-1..3, BEL-1, BEL-2 proved,
statement audit passed; no published-theorem assumptions.  Numerics (`numerics/REPORT.md`):
three-solution instance of the local problem (LOC-5), none in the bus toy model; arclength tracer
vs warm start compared.  Not a completed Protocol E release (no clean-checkout review, no manifest).

Blocking owner decision (finding F1): target system = proposal Table 1 as printed (U_r(s) in eq. 2)
or arXiv:2508.00159 (U_r(s') effectively)?  Under the latter §1/§4 are vacuous; §2/§3 stand.

Next, in order: (1) owner decision F1, F2; (2) formalise the system and the corollary of §3
(reduction to |S| unknowns for β ≤ 1); (3) PATH-1/2 for the planar curve (or, under the paper's
form, a minimal cyclic example with multiplicity); (4) general β > 1 non-monotonicity (LEH-3);
(5) system (1)–(3)+(6).

Setup in a fresh container: install elan, `lake exe cache get && lake build`;
`pip install numpy scipy matplotlib`.
