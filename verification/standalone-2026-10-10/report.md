# Erdős 1057 proof verification and submission review

**Overall verdict: Verification passed for both specified proof versions. Prize acceptance and priority remain undecided.**

This review covers the original public modular proof at `55fe0f1cd4d8e63b417eb122067ab3e307b39f32` and the later standalone proof at `a95a41e18d13474150be7b127a4231e8c4c0e3af` in [JENW1N/erdos1057-lean](https://github.com/JENW1N/erdos1057-lean). The newer source is exactly the user-supplied `Challenge.lean`, SHA-256 `20df80a9cba8503fe6cfceeccc6de2e7b7db94beb0532eed064ca1e2a65ff667`, 17,716,380 bytes. The reports apply to those source bytes, rather than an unspecified current branch.

Both versions fully establish the original Carmichael counting limit within the stated standard classical Lean trust scope. All required proof obligations are covered; no additional number-theoretic hypotheses or placeholder axioms remain in the target closure. This is an AI-assisted technical verification, not an independent human referee report or a Prize decision.

| Required question | Original October 8 version | Later standalone version | Decisive evidence |
| --- | --- | --- | --- |
| Does the proof address the specified original problem? | Yes | Yes | The count uses the standard composite Carmichael predicate and ranges over all bounded naturals; the conclusion is the full logarithmic limit. |
| Did the specified commit actually pass verification? | Yes | Yes | Frozen source, exact target and independent bridge checks, axiom output, kernel replay and independent exported-proof checking. |
| Does it fully solve the original problem? | Yes | Yes | The theorem has no additional hypotheses; its closure proves all requirements in the coverage table. |
| Does it meet the Lean completeness requirements for this verification? | Meets | Meets | Exact versions, complete scope and the recorded technical checks. |

## Original statement and proof coverage

The question is [Erdős 1057](https://www.erdosproblems.com/1057), listed as **JSP-000877** in the Prize catalog. Does the number `C(x)` of Carmichael numbers up to `x` satisfy `C(x)=x^(1-o(1))`? This is the exponent-one growth assertion, not Pomerance's finer conjectural asymptotic.

Both sources conclude with the parameter-free declaration:

```lean
Bounty.target : True ↔
  Filter.Tendsto
    (fun x => Real.log (Erdos1057.carmichaelCounting x) / Real.log x)
    Filter.atTop (nhds 1)
```

The independently authored bridge defines the count directly:

```lean
def Intended1057 : Prop :=
  Filter.Tendsto
    (fun x : ℝ =>
      Real.log (({n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ x}.ncard : ℝ)) /
        Real.log x)
    Filter.atTop (nhds 1)
```

The checked theorem obtains this statement from `Bounty.target.mp True.intro`, with the submitted counting definition expanded. The task uses the pinned Formal Conjectures compatibility definition of `IsCarmichael`. [DefinitionAudit1057.lean](DefinitionAudit1057.lean) separately proves that it is equivalent to `1 < n`, non-primality, and the Fermat divisibility condition for every positive coprime base, then proves equality of the counting functions for every real bound. That audit passed Lean and source-built Nanoda; [its result](definition-audit-result.json) and [output](logs/definition-nanoda.log) are retained. Primes and trivial values are excluded. There is no assumption that a finite witness or an infinite but sparse family supplies the required density.

| Original obligation | Formal correspondence | Scope |
| --- | --- | --- |
| Count all Carmichael numbers up to the bound | The bounded set uses the root standard `IsCarmichael` predicate | All qualifying natural numbers |
| Approach exponent one | Logarithmic ratio tends to one | Freely approaching exponent one, rather than a fixed smaller exponent |
| Cover every sufficiently large bound | `Filter.atTop` on real `x` | Not a chosen subsequence or finite range |
| Prove the result unconditionally | `Bounty.target` has no mathematical parameters | No unproved zero-free or smooth-prime hypothesis remains |
| Supply the analytic and combinatorial proof | Complete custom source and transitive proof closure | Includes the selected-residue, prime-supply and Carmichael-transfer chain |

The [mathematical account](../../MATHEMATICAL-ACCOUNT.md) explains the proof chain using the preserved modular sources. Its actual analytic input has zero-free bound `23/24` and subsequent Mangoldt exponent `95/96`. Its smooth primes lie in the stated wider interval, and its parameter choices cover every large real bound. The earlier S0005 manuscript contains stronger-input caveats and is historical evidence; the formal verification is not a certification of those stronger historical assertions.

## Versions and pinned evidence

The [existing Prize PR 4874](https://github.com/TheJustinSunPrize/awards/pull/4874) was inspected against awards base `16877004910734cecca83cc5af0fec2f5a4125b3`, with head `54843825af6b18d4f53c421063dc8b3e735d88f6` before this evidence update. It was open and unmerged with no posted review or comment. The new evidence is provided in the same submission, preserving the earlier source and release history.

The two proof versions are different. Of 320 component source hashes, 297 match and 23 differ. Each version was checked separately; the newer pass is not substituted for checking the earlier version. The older 18,330,625-byte file in `standalone-pending/` is another historical snapshot and is not the attached file checked here.

The original public release [v2026.10.08](https://github.com/JENW1N/erdos1057-lean/releases/tag/v2026.10.08) has a GitHub publication time of **October 8, 2026, 18:29:25 UTC**. Existing October 9 compile/audit receipts for the newer source remain preserved separately. Their existence and dates were checked; this review additionally produced new proof objects and independent checking evidence.

## Execution and trust scope

The review followed the [Prize's Lean verification skill](https://github.com/TheJustinSunPrize/awards/blob/16877004910734cecca83cc5af0fec2f5a4125b3/skills/lean-verify/SKILL.md). It used macOS ARM64 with Lean **4.35.0-rc2**, compiler commit `11acb17ec6b07a8f9e9173e6845197929540936b`, and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`. All nine standard dependencies were checked at their pinned revisions with unchanged tracked sources. Their existing caches were trusted; rebuilding all Mathlib source is not claimed.

The macOS sandbox denied network access, restricted writes to each audit directory and denied user-directory reads apart from the pinned toolchain and standard dependency directories. A control test confirmed that unrelated-file reads/writes and a network connection were denied. The environment was replaced with a minimal set of variables. No proof compiler received account credentials. Host system runtime libraries remained trusted; no separate CPU or address-space cap was imposed.

For the standalone version, all 189 baseline modules, the support module and the entire custom proof were compiled to a new object directory. The first baseline jobs ran sequentially; the remainder used three one-thread workers. All objects came from this run. The whole standalone file was compiled with `--trust=0`, the original challenge's affirmative-answer setting and eight Lean threads.

For the original version, source bytes were extracted from the immutable public commit. The 189 baseline modules and support source were compared byte-for-byte with the just-rebuilt baseline. Only those newly produced baseline artifacts were reused, including Lean's matching private/server/IR files. All 320 original custom modules were compiled afresh in a separate directory. No submitted custom `.olean` was reused.

| Check | Original modular version | Standalone version |
| --- | --- | --- |
| Custom source compilation | All 320 modules passed | Entire file passed in 726.120 seconds |
| Exact target and axiom audit | Passed | Passed |
| Independent explicit-count bridge | Passed | Passed |
| Lean kernel replay | Passed for `ActualErdos1057Target` | Passed for `Challenge` |
| Nanoda 0.4.17 | Passed | Passed |
| Source-built Nanoda 0.4.19 | 126089 declarations checked with no errors | 125597 declarations checked with no errors |
| Submitted source changed during checks | No | No |

Nanoda 0.4.19 was built from unmodified [`ammkrn/nanoda_lib` source at `3a2407216ee84a75f9e1aead6803d0578be06ae7`](https://github.com/ammkrn/nanoda_lib/tree/3a2407216ee84a75f9e1aead6803d0578be06ae7), offline after locked dependency fetching. [Build provenance](../checker-2026-10-10/result.json) and each version's `nanoda-latest-result.json` record the source, binary hash, invocation and output.

The exact command lines, working directories, exit codes, durations, environment and hashes are retained with each run. The generic `audit.py preflight` identifies the absence of root-level Lake configuration in this repository. The standard runner therefore cannot drive its non-Lake layout directly. Equivalent explicit compiler commands and target audits were used. The standalone preflight also saw unrelated documentation/launcher edits in the publication checkout; the compiler read only the frozen, hash-matched proof sources. This is documented rather than represented as a generic automation pass.

Both bridges and all target checks preserve full `#check`, `#print` and `#print axioms` output. The complete transitive axiom set for each `Bounty.target` and bridge was:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx`, `Lean.trustCompiler`, custom proof axiom or unproved prime-supply assumption appears in the audited targets or independent bridges. The imported challenge contains admitted statements; their bodies are not proof dependencies of the submitted result.

Lean's `leanchecker` replays the selected module's declarations against its imported environment; it is not an independent kernel implementation. Nanoda independently checks the exported transitive proof closure. Its configuration permits exactly the three standard axioms, with `unsafe_permit_all_axioms=false`. Exporter and checker hashes and output counts are retained in the run receipts.

An installed Lean4Lean binary failed to read even a trivial Lean 4.35 control module because of an incompatible object header. That check did not pass and is not presented as a proof failure. The compatible Lean exporter and Nanoda control check passed, and the actual exported proof checks are reported separately. Initial setup attempts for the original modular run omitted required baseline sidecar/IR files; they failed before proof checking. The final run copied the complete matching baseline artifacts without changing submitted source. Those diagnostics are retained.

## Priority and remaining award steps

The [literature review](../literature-2026-10-10.md) found no earlier complete unconditional proof of this exact counting limit among the reviewed publications and Prize submissions. It distinguishes classical/fixed-exponent results, conditional results, computations and the credited OpenAI ingredients. The unavailable full text of SSRN 6913501 and unindexed/private work remain limits of the search.

This supports presenting the original public version and dated evidence for review. It does not establish priority by itself. Mathematical and formalization contributions are evaluated separately. The internal manuscript date, compilation date, Git commit date, public release time and organizer candidate notice are different events.

The contribution package supplies both original source versions, complete formal arguments, the mathematical account, attribution, locked environment, reproduction commands and verification evidence. The Prize must still review the mathematics, formalization and contributor/priority evidence, accept the submission, publish any candidate notice and complete the claim process. Neither a successful check nor a source publication creates official eligibility or a payment entitlement.

## Evidence index

- [Standalone source-build receipt](result.json), [subsequent checks](final-result.json), [logs](logs/), [independent bridge](Independent1057.lean), [target manifest](targets.json).
- [Original modular verification](../modular-2026-10-10/report.md), including its own receipt, bridge, logs and source hashes.
- [October 9 author-side records](../standalone-2026-10-09/), preserved separately from this review.
- [Reproduction guide](../../standalone/BUILD.md). Raw large proof exports and compiled objects are identified by hash and regenerated by the retained commands; they are not added to the source repository.
