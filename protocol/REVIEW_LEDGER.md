# Review ledger

Framework: Protocol_E. This blank template is not a completed audit. Empty fields mean unrecorded, not accepted. Use stable IDs, append dated decisions, and link exact proofs instead of copying them. Additional sections may share this file or be linked from it.

## Target claims and proof units

| ID | Exact claim or linked statement | Proof location and version | Direct inputs | Consumers | Author | Mathematical status | Review scope and status |
| --- | --- | --- | --- | --- | --- | --- | --- |

## Source and application inventory

| Use ID | Required assertion | Source, final publication, exact statement and file identity | Definitions and corrections checked | Objects, hypotheses, conventions and exceptional cases | Connecting argument | Consuming locations | Decision and exact scope |
| --- | --- | --- | --- | --- | --- | --- | --- |

Include uncited substantive inputs. Unavailable final-version checks remain explicit. Group repeated uses only with a justification covering every listed consumer.

## Computational evidence

| ID | Consumed mathematical assertion | Input and representation | Generator or certificate | Checker and mathematical justification | Tool versions and command | Result and hashes | Negative tests and limitations |
| --- | --- | --- | --- | --- | --- | --- | --- |

## Audit intake and findings

| Finding ID | Audit, author and date | Affected version and inference | Diagnosis | Earlier evidence and search limits | Repair or rebuttal | Affected/related uses | Incorporation | Decision, reviewer and remaining work |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |

Register every received substantive objection. Link duplicates without deleting their intake record. Distinguish incomplete review, missing evidence and a demonstrated invalid inference.

## Decisions and changes

| Decision ID | Author/reviewer and human/model provenance | Bound files, statements, assumptions and version | Actual review scope | Findings | Decision | Date | Supersedes and reason |
| --- | --- | --- | --- | --- | --- | --- | --- |

For each change, identify affected consumers and the reason other evidence remains applicable. Do not replace a prior decision's bindings to imply new acceptance.

## Formal roots, assumptions and statement audits

| Root/module | Exact declaration and definitions | Independent semantic review | Formal dependency/axiom report | Allowed source-assumption IDs | Checking result and version |
| --- | --- | --- | --- | --- | --- |

| Assumption ID | Exact formal type | Published theorem and final source | Source-to-formal comparison | Independent reviewer | Actual consumers |
| --- | --- | --- | --- | --- | --- |

List the declared foundations separately. Compare the complete transitive axiom set with these lists. Record certificate-soundness and actual certificate-acceptance theorems, encoding audits and clean builds. Extra computational assumptions and unfinished proof axioms block the completion claim.

## Release record

- Version, date and source revision:
- Exact selected protocol and completion status:
- Target statements, remaining assumptions and unresolved work:
- Manifest of required files, hashes, roles and source relationships:
- Build/reproduction commands, versions and results:
- Manuscript, README, inventory, findings and artifact-index synchronization:
- Cumulative handoff identity, coverage, exclusions and provenance:
- Archived prior release and correction links:
- Link checks and destination readback:
- Closure decision, responsible reviewer or author, scope and bound evidence:

Keep the manifest's own hash in an external record if needed; do not create a self-hashing cycle. For a non-release change, explain any deferred release-only duties.

## Findings (project entries)

| ID | Date | Affected | Finding | Status |
| --- | --- | --- | --- | --- |
| F1 | 2026-11-13 | STATEMENTS §0 (R2), LOC-1..4, §4 | Proposal Table 1 eq. (2) puts U_r(s) at the current state; arXiv:2508.00159v2 eqs. 4/9 give Q_r(s,a) = γ_r E[U_r(s') + E Q_r(s',a')]. Under the paper's form the local problem (LOC) is vacuous and acyclic games are uniquely solvable. LEH and BEL unaffected. | Resolved 2026-11-13: owner chose the paper's version; equations re-read from the arXiv LaTeX source by the integrator; STATEMENTS §0 rewritten, LOC and old §4 demoted to the proposal's variant |
| F2 | 2026-11-13 | STATEMENTS §0 | Numerics agent: eq. (2) needs a goal-marginal human policy for E_{a_H}; terminal V_h unspecified. | Open: owner to specify |
| F3 | 2026-11-13 | LOC-4, BEL-1/2, LOC-2, LEH-1 | Statement audit: STATEMENTS.md imprecise (m > 0 needed in LOC-4; unused hypotheses). | Resolved: STATEMENTS.md aligned with the Lean roots |
| F4 | 2026-11-13 | STATEMENTS §0 abstract form, `sys3` (commit 4068309) | Statement audit: with Q < 0 required at all states, no solution exists under the acyclicity hypothesis, so `sys3` is vacuous (reviewer proved ¬IsSolution in a scratch file). `sys1`, `sys2`, SYS-L, SYS-T faithful. | Resolved: terminal states added (commit d2dda7a), `sys1`–`sys3` re-proved, witnesses `sys3_nonvacuous`, `sys1_nonvacuous`; fresh non-author audit passed |

## Formal roots (project entries, release candidate 0.1)

Lean commit b7ca9f1; axioms of every root: propext, Classical.choice, Quot.sound (`axioms_report.txt`);
allowed source assumptions: none.  Statement audit: separate agent that wrote no proofs, read
definition bodies and root statements against STATEMENTS §1–3, did not run Lean; verdict below.

| Unit | Root | Audit |
| --- | --- | --- |
| LOC-1 | `EmpoHomotopy.loc1` | faithful |
| LOC-2 | `loc2` | faithful (holds for all real β) |
| LOC-3 | `loc3`, `loc3_beta_zero` | faithful |
| LOC-4 | `loc4` | faithful (0 < m required; "at most one") |
| LEH-1..3 | `leh1`, `leh2`, `leh3` | faithful |
| BEL-1 | `bel1`, instance `lehmerBellmanOp_hyps` | faithful |
| BEL-2 | `bel2` | faithful; Lehmer instance of its hypotheses not formalised |
| SYS-1, SYS-2, SYS-3 | `sys1`, `sys2`, `sys3` (commit d2dda7a) | faithful (second audit, after F4) |
| SYS-W | `sys3_nonvacuous`, `sys1_nonvacuous` | faithful; witnesses hand-checked by the reviewer |
| SYS-L | `sys_linear_uniqEval`, `sys_linear_local` | faithful |
| SYS-T | `sys_T_uniqEval` | faithful; concrete M_π and composition with sys1/2 not formalised |
| Ψ instance | `sys_paper_psi_neg` | faithful; meaningful only for positive arguments |
| SYS-6 | `sys6_two_solutions`, `sys6_three_solutions` (commit c4556d0) | faithful; instance checked field by field; reviewer's own exact-arithmetic check agrees |

Audits of the SYS roots: reviewers read definitions and statements, ran no Lean; all 22 roots in
`axioms_report.txt` depend only on propext, Classical.choice, Quot.sound.

Not yet done for a Protocol E release: clean-checkout build by a reviewer, release manifest,
manuscript.  Status: **not a completed Protocol E release.**
