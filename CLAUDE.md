# Project notes for agents

Research project: homotopy continuation for the steering equations of human-empowering AI
(agenda: MATH+ proposal EF-MA-Sys, summarised in `notes/STATEMENTS.md` §0).  Verification standard: Protocol E (`protocol/PROTOCOL.md`,
`protocol/AGENTS.md`), brief in `protocol/PROJECT.md`, ledger in `protocol/REVIEW_LEDGER.md`.

* `notes/STATEMENTS.md` is the source of truth for targets and their status marks
  (L = Lean, I = informal, N = numerical, ? = open).  Never report I/N/? items as verified.
* Lean 4 + Mathlib (pins: `lean-toolchain`, `lake-manifest.json`); `export PATH=$HOME/.elan/bin:$PATH`.
  Build discipline: check single files with `lake env lean File.lean`; one `lake build` per batch;
  one Lean process at a time (15 GB RAM); no `sorry`, no new `axiom` outside
  `EmpoHomotopy/Assumptions.lean` (published theorems only, each registered in the ledger).
* Scalars are ℝ here (real powers, continuity, IVT are essential); no generic-field layer.
* Propositional definitions are the reference; numerics (`numerics/`) are evidence, never proofs.
* Pipe long-running command output through `tail`; push work in progress often.
* Style: brief, precise, mathematical; claim only what is supported.
