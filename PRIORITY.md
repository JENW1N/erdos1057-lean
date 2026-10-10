# Priority and publication record

This repository records the mathematical work credited to Jensen Kohlmeyer (JENW1N / jenw1n), Liam Kruer (lkruer), Will Howe (H0W4RD-dev), and Grant Huffman (Ghuffy1). Lean formalization credit is recorded separately in [AUTHORS.md](AUTHORS.md). It supplies dated public evidence for review; it does not by itself determine mathematical priority, validate identity, or grant an award.

## Which dates mean what

| Event | Date or time | Evidence and scope |
| --- | --- | --- |
| Original S0005 manuscript | Internally dated 6 October 2026 | [Preserved manuscript](original-candidate.md); author-side date, not established public disclosure. |
| Current modular audit | 8 October 2026, 16:44:16 UTC | [Existing audit receipt](verification/modular__canonical__audit-receipt.json); author-side machine-check evidence. |
| Current modular snapshot export | 8 October 2026, 16:45:17 UTC | [Existing export receipt](verification/modular__export-receipt.json); source-lock SHA-256 `0f0ee393d8024ecd7b3ebf23889d7bb5bef3833328899cd51ba7cb2fbc213108`. |
| Public version | Use the selected full Git commit and GitHub release/PR server records | The public publication time is distinct from all internal work dates above. |

No backdating or claim of earlier public disclosure is made. Mathematical-solution priority and Lean-formalization priority should be assessed separately against the actual complete versions and other public work.

## Public evidence

The selected proof is identified by a full Git commit in the `main` branch. `SHA256SUMS` identifies the published files. Release assets preserve a source package and its checksum. The submission PR links the exact selected commit and the public release; the GitHub server records provide public evidence in addition to editable author and committer dates.

A timestamp receipt, when included with the release, is supplementary evidence of existence of the exact checksum manifest. A pending calendar receipt is not a confirmed blockchain timestamp; it must be upgraded and verified before claiming that stronger status. A timestamp establishes existence of bytes, not correctness or authorship.

The [Justin Sun Prize process](https://github.com/TheJustinSunPrize/awards/blob/16877004910734cecca83cc5af0fec2f5a4125b3/docs/award-process.md) assesses independent public history and explicitly says Git timestamps alone are insufficient. The organizers determine acceptance, attribution and any competing priority claims.

## Correct target and previous submissions

The correct catalog mapping is **Erdős 1057 → JSP-000877**, not Erdős 877 and not JSP-001057. This submission addresses the full growth exponent of the Carmichael counting function. Existing witness-only submissions, including [PR 4847](https://github.com/TheJustinSunPrize/awards/pull/4847) for 561 and [PR 1094](https://github.com/TheJustinSunPrize/awards/pull/1094) for finite examples, have a different mathematical scope. Their existence does not settle novelty or priority of this full target. The bounded search performed for this publication is not an exhaustive prior-art clearance.

## Claim and review sequence

This publication and contribution PR are not personal award claims. The required contribution PR must merge before a new Lean/both-role claim is accepted. Each contributor must claim only their own contribution through their own GitHub account, supply an authorized public correspondence address, and complete the mandatory private identity-verification email. Coauthor credit is not a proxy claim.

The 14-day review period starts only when the organizers publish the applicable candidate notice, separately for mathematical and formalization contributions. It does not start from this repository, the PR, a local audit, or a claimed discovery date.

## Conjectures.io interaction

The preserved one-file candidate exceeds the current task's uncompressed 10 MiB limit and is not submitted here as an admissible Conjectures.io payload. The user prioritized publication and the JSP route despite that size. Under the [current Conjectures.io terms](https://github.com/conjectures-io/conjectures-validator/blob/874d37f532f8798bebfd43c7c7d42f19d06e615e/docs/SUBMISSION_TERMS.md), an earlier public solution or formalization may affect bounty eligibility. This publication does not claim eligibility for both awards.

## Attribution correction

The 8 October 2026 [attribution update](ATTRIBUTION-UPDATE.md) adds Will Howe and Grant Huffman to the mathematical solver credits. It changes no proof source, verification result, or selected proof commit. The initial proof publication is still `55fe0f1cd4d8e63b417eb122067ab3e307b39f32`; its original checksum manifest and timestamp receipt are preserved in `provenance/` and in that commit. A later attribution date is not presented as a new proof-completion date or backdated disclosure.

## October 9 source revision and October 10 evidence update

The first public modular proof remains commit `55fe0f1cd4d8e63b417eb122067ab3e307b39f32`, with GitHub release [v2026.10.08](https://github.com/JENW1N/erdos1057-lean/releases/tag/v2026.10.08) published on **8 October 2026 at 18:29:25 UTC**. The existing [Prize PR 4874](https://github.com/TheJustinSunPrize/awards/pull/4874) was opened immediately afterward. Updating that same PR preserves its history.

The new single-file source has SHA-256 `20df80a9cba8503fe6cfceeccc6de2e7b7db94beb0532eed064ca1e2a65ff667`. Its recorded successful compile ended on 9 October at 17:00:19 UTC, and its target audit passed immediately afterward. These are author-side execution timestamps. Publication of the file and logs on October 10 does not backdate public availability of this revised file to October 9.

The new assembly originated from 320 modules: 297 source hashes match the earlier modular snapshot, while 23 differ. No byte-for-byte or blanket semantic-equivalence claim is made for the revisions. The old source, original release, notices and earlier verification remain accessible. Each version's evidence applies to that version.

A bounded literature search on October 10 found no earlier unconditional full proof of the exact Carmichael counting limit. It found classical and newer fixed-exponent lower bounds, conditional near-linear counts, existence results, finite computations, and the credited OpenAI analytic and smooth-prime inputs. This supports submitting the priority evidence for review; it is not a certification of first priority. See [literature review](verification/literature-2026-10-10.md) for sources and access limits.

Both public proof versions were checked separately on October 10, including fresh custom source compilation, exact statements, standard axiom closure, Lean kernel replay and independent Nanoda checking. The [verification report](verification/standalone-2026-10-10/report.md) distinguishes the versions and trust scope. Later verification does not change the earlier public release timestamp or guarantee priority.
