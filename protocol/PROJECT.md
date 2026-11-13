# Project brief

## Selected framework

- Protocol: Protocol_E, framework edition 1, installed as PROTOCOL.md (kit from
  github.com/elliotglazer/protocols, cloned 2026-11-13).
- Protocol file SHA-256: a6935609c68ae3e899e735fd7dd8e4cac2115c50805d168079ae9842a4d4a3d7
- Completion claim intended: "Protocol_E formal verification relative to the listed
  published-theorem assumptions" for the targets marked for Lean in `notes/STATEMENTS.md`.
- Departures: (a) numerical experiments (`numerics/`) are exploratory evidence outside the
  protocol and are labelled N; (b) informal results (I) are research notes, not completion claims.
  Protocol chosen by the agent on the owner's instruction "a suitable protocol" + "Lean workflow";
  owner may override.

## Mathematical target

- Agenda: MATH+ proposal "Homotopy Continuation Methods for Solving the Steering Equations of AI
  Systems Interacting With Many Humans" (J. Heitzig), Year 1: existence/regularity of homotopy
  paths for systems (1)–(5) and (1)–(3)+(6); predictor–corrector vs warm-start numerics.
- Release 0.1 targets (exact statements in `notes/STATEMENTS.md`): LOC-1..4, LEH-1..3, BEL-1.
  Stretch: BEL-2.  Later releases: §4 (acyclic games), §5 (PATH-1..3), system (6), low rank (Year 2).
- Ambient objects: finite index types, real scalars, β ≥ 0; see STATEMENTS §1–3.
- Conditional assumptions: readings R1, R2 and positivity P of STATEMENTS §0 (affect only the
  informal link between the abstract theorems and the proposal's system, not the Lean targets).
- Exclusions for 0.1: any claim about the full system (1)–(5), path connectedness, bifurcations.
- Sources: the proposal PDF (owner's upload); refs [1]–[6] therein (not yet consulted in full).

## Trust and review

- Known objections: R2 may differ from arXiv:2508.00159 (there Q_r may use U_r(s')); to be checked.
- Canonical ledger: REVIEW_LEDGER.md.  Unit ids: the statement ids (LOC-n, LEH-n, BEL-n, PATH-n).
- Author: Lean-author agent(s).  Integration owner: the coordinating agent of the session.
- Reviewers: a separate agent that did not write the proofs audits every root statement and
  definition body against STATEMENTS.md (statement fidelity), and the axiom report.
- Closing criteria per unit: Lean root compiles in a clean build, `#print axioms` shows only
  propext, Classical.choice, Quot.sound (+ registered assumptions), non-author statement audit passed.

## Formal proof contract

- Lean 4 `leanprover/lean4:v4.35.0-rc3`, Mathlib `v4.35.0-rc3` (pins: lean-toolchain, lake-manifest.json).
- Root declarations: listed in REVIEW_LEDGER.md once fixed; collected in `EmpoHomotopy/Roots.lean`.
- Foundations: Lean kernel with propext, Classical.choice, Quot.sound.  No `sorry`, no `native_decide`.
- Permitted published-theorem assumptions: none for release 0.1.
- Axiom extraction: `#print axioms` on every root in `EmpoHomotopy/Roots.lean` (output saved in
  `protocol/axioms_report.txt`).
- Certificates: none.
- Build: `lake exe cache get && lake build`.

## Release contract

- Repository mensch72/empo-homotopy (private), branch `claude/elegant-clarke-lp4em3`; no other destination authorised.
- Manuscript: `notes/STATEMENTS.md` (0.1); handoff: `HANDOVER.md`.
- Versions: 0.x, dated; reproduction: build command above; `python3 numerics/*.py`.

## Resources and existing authorization

- 4 cores, 15 GB RAM: one Lean process at a time.  Owner asked for token economy.
- Decisions needing the owner: readings R1/R2; which homotopy parameters to prioritise; protocol level.
