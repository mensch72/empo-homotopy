# Protocol_E: formal proof relative to published theorems

Framework edition 1 | November 9, 2026

## Completion standard and trust boundary

Formalize every project argument supporting the announced results, including connecting lemmas and essential computational verification. Permit only explicitly listed, independently audited published-theorem assumptions in addition to the declared foundations and verification system. The final formal result must display or have a mechanically extracted dependency on precisely those assumptions.

This is a formal proof **relative to published-theorem assumptions**, not a formal proof of those imported theorems. It can strengthen the verification of the project's reasoning while still trusting the external mathematics and its translation. A successful build with hidden axioms or unexamined formal statements does not meet this standard.

Formal dependency evidence replaces duplicated manual inventories of every internal inference. Independent review of target statements, imported theorem translations, definitions, computational meaning and release identity remains necessary. Protocol_E is a complete alternative framework; it does not require a second implementation of every documentary procedure in Protocol_D.

## Freeze the target and formal system

Record exact mathematical claims, domains, quantifiers, bounds, witness representations and intended conditional assumptions in `PROJECT.md`. Choose and pin the prover, compiler, libraries, foundational axioms and checking mode. Record whether the result is constructive or uses classical principles and what that means for any claimed executable construction.

Assign stable identifiers to the mathematical targets and formal declarations. An independent reviewer must compare each target's complete elaborated type and relevant definition bodies with the intended mathematics. Check coercions, hidden parameters, typeclass instances, quantifier order, domains, degenerate cases and nonvacuity. A proposition that merely assumes its desired conclusion is not the target theorem.

Freeze the definitions shared between modules before parallel proof work. Changes reopen affected statement and dependency reviews. A proof of a different statement does not count as progress toward the approved target merely because its name matches.

## Audit the permitted source assumptions

Maintain one explicit assumption registry. For each imported published theorem, record:

- Its exact mathematical statement, authors, publication, edition, theorem location, source file identity and applicable corrections.
- The final published statement and definitions actually checked; unresolved comparisons with an author manuscript remain open.
- The exact formal declaration, complete type and required definition bodies, with a source-to-formal comparison by a non-author reviewer.
- All restrictions, conventions, domains and exceptional cases relevant to its uses.
- Its actual consumers and the reason it is trusted rather than proved within this project.

The assumption must express the published result faithfully. Any specialization or translation requiring new mathematics needs a formal proof from that assumption. Do not silently assume a convenient stronger variant. Make ordinary published mathematical inputs assumptions only when they have passed the same source and translation checks.

Unknown, disputed or unpublished results cannot be admitted as published-theorem assumptions. Prove the needed result within the project, resolve the source concern, or state a separate conditional target with the new premise exposed. Such a target does not satisfy the original unconditional completion goal. A published source may be trusted without reproving its entire ancestry, but concrete objections to its needed content must be resolved.

## Prove the project arguments

Require checked proof terms for all new lemmas, theorem applications, object identifications, existence and termination arguments, and changes of representation. Module interfaces must use the same audited definitions. At final assembly, establish the announced targets through these declarations rather than through a parallel unaudited shortcut.

Inspect the transitive assumptions of each final theorem. In Lean, use `#print axioms` or equivalent dependency inspection as part of this check. A text search for `sorry` is useful but insufficient. Reject unapproved axioms, `sorryAx`, placeholder assumptions, unsafe proof shortcuts, and unexpected dependencies. Audit the proof-producing and checking mechanism rather than assuming every command that returns success is kernel verification.

Archived experiments may contain incomplete work if isolated and clearly labeled. They must not be imported into or counted as the completed proof. Identify the exact root declarations and their dependency closure in the release.

Review formally stated lemmas for meaning and genuine use of the intended inputs. The kernel verifies a derivation of its formal conclusion; it does not decide whether that conclusion captures the intended theorem. Non-author statement review is required at important module boundaries and for all final targets and assumption interfaces.

## Computation and certificates

Keep computational search separate from the final proof. Search can run in untrusted external software. Its output must enter the formal argument through a verified checker or another checked derivation.

For each certificate, supply its exact bytes or a reproducible unambiguous generation and encoding procedure, a formally specified checker, and a checked theorem that acceptance implies the needed mathematical fact. Also establish acceptance of the actual certificate through the declared trusted checking path. A proved checker-soundness theorem plus an unverified external claim that it returned true leaves a gap.

Do not add a computational axiom merely because direct evaluation is expensive. Chunk certificates, exploit structure or use proof-producing computation. If external attestation remains necessary, expose it as an additional conditional assumption and do not call the Protocol_E goal complete.

Bind the parser, encoding and mathematical interpretation of data. Machine arithmetic must model the intended exact arithmetic, or overflow and rounding must be proved harmless. Distinguish complete expansion, symbolic representation, generator and sampled evidence. Include appropriate corrupted-certificate tests as engineering checks, while keeping their role separate from checker correctness.

## Findings and efficient review

Register every substantive objection with its affected statement and version. Resolve by formal repair and renewed statement review, a supported non-author rebuttal, or an explicit change to the target. Kernel acceptance does not dismiss an objection about a wrong definition, source assumption or artifact interpretation.

Preserve prior evidence and decisions. Use one ledger linking source assumptions, formal roots, statement audits, computations, findings and releases. Derive internal dependency information from the actual formal environment where possible. Do not hand-copy every proof tactic into a separate application database.

Reuse unchanged proofs and reviewed interfaces. A change in definitions, assumptions, libraries or the checking mode requires an impact assessment even when theorem text is unchanged. Give parallel workers fixed declaration contracts and isolated edits, with one integration owner.

## Closure and release

Build from a clean checkout with pinned dependencies. Independently verify the release's target declarations and definition bodies, inspect the full transitive axiom set, check the assumption registry against actual dependencies, and confirm that all essential computational facts are formally discharged. Record the trusted kernel, foundations and any other mechanism relied on by the checking path.

The manuscript must state the same results and limitations as the formal roots. Synchronize the README, source and assumption inventories, findings, formal files, supplied manuscript and PDF, artifact index and cumulative research handoff. Include the relevant research history, failed approaches, repairs, certificate provenance and review evidence. Exclude conversational transcripts, credentials and unrelated private material. Record restricted sources and do not redistribute them without authority.

The release manifest binds version, date, source revision, build commands, dependency pins, targets, assumption report, artifacts and hashes. Preserve prior releases, check links and read back every authorized destination. Reviewers must assess the actual release, not an earlier successful build. Stop after all required proof, statement, source and release checks pass.

Report completion as **Protocol_E formal verification relative to the listed published-theorem assumptions**. Publish that list prominently. Do not call the result fully formalized from foundations until the remaining theorem assumptions have been discharged.
