# Erdős 1057 Carmichael counting proof submission

**Mathematical solvers: Jensen Kohlmeyer (JENW1N / jenw1n), Liam Kruer (lkruer), Will Howe (H0W4RD-dev), and Grant Huffman (Ghuffy1).**

**Lean formalization: Jensen Kohlmeyer and Liam Kruer.** See the [attribution update](ATTRIBUTION-UPDATE.md).

This repository publishes the current modular Lean proof sources and the original mathematical candidate for [Erdős problem 1057](https://www.erdosproblems.com/1057), listed by the Justin Sun Prize as [JSP-000877, Carmichael numbers](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000877).

The target is the full counting asymptotic

```text
lim_{x → ∞} log(C(x)) / log(x) = 1,
```

where C(x) counts Carmichael numbers at most x. It is not merely an existence proof or verification of finitely many Carmichael examples.

## Submitted proof version and evidence

The October 9 single-file revision is now available at [standalone/Challenge.lean](standalone/Challenge.lean), together with its successful source compile and exact-target audit logs. Its SHA-256 is `20df80a9cba8503fe6cfceeccc6de2e7b7db94beb0532eed064ca1e2a65ff667`. See the [standalone build and verification guide](standalone/BUILD.md) for the version distinction, reproducible commands, and the checks actually performed. The October 8 public modular snapshot and its evidence below remain preserved.


The selected modular source is the complete 320-module `joined0f0e-reviewed-320` snapshot exported on 8 October 2026 at 16:45:17 UTC. The source owner's recorded Lean audit completed at 16:44:16 UTC. It reports the exact parameter-free target, with only `propext`, `Classical.choice`, and `Quot.sound` in its axiom closure. Extraction rechecked all 320 source hashes and all 993 entries of the original export certificate. The evidence and its scope are described in [VERIFICATION.md](VERIFICATION.md).

The public package preserves those October 8 proof source bytes. That original extraction did not rerun Lean. Its modular recipe remains in [BUILD.md](BUILD.md); the later standalone revision and its verification are recorded separately in [standalone/BUILD.md](standalone/BUILD.md). This submission remains subject to the Prize’s mathematical and formal review.

- [Current mathematical account and source correspondence](MATHEMATICAL-ACCOUNT.md)
- [Exact proof endpoint](modular/src/ActualErdos1057Target.lean), theorem `Bounty.target`
- [Recorded statement and axiom output](verification/modular__canonical__audit-target.log)
- [Build and reproduction instructions](BUILD.md)
- [Original S0005 candidate, preserved verbatim](original-candidate.md)
- [Joint authorship and third-party attribution](AUTHORS.md)
- [Priority and publication record](PRIORITY.md)

## Original candidate and corrected scope

The original S0005 candidate carries an internal date of 6 October 2026 and explicitly discloses unresolved verification of its borrowed inputs. That internal date is not asserted as a verified public-disclosure date. Its mathematical text is unchanged here.

The current Lean route uses the actual `23/24` zero-free bound, while S0005 described a `7/8` input. The current mathematical account distinguishes the revised route and its formal sources from the historical manuscript; the current proof must not be read as certifying every statement in that manuscript verbatim.

## Historical standalone candidate and Conjectures.io

[standalone-pending/Erdos1057Diagnostic.lean](standalone-pending/Erdos1057Diagnostic.lean) is a separate, exact snapshot of the latest assembled one-file candidate. It is 18,330,625 bytes, SHA-256 `8819d40f238102fe48516a1a9995921aa397f2d805abc32f6cf27ad4b933ec0c`. Its original owner was still checking that older snapshot at the extraction time. The successful October 9 logs concern the distinct 17,716,380-byte [current standalone source](standalone/Challenge.lean), not that historical file.

It exceeds the [current Conjectures.io task cap](https://github.com/conjectures-io/conjectures-tasks/blob/03d9c665d8ac9c8e283d0cea180f217fafc7daa6/pool/tier-1/erdos-1057-formalized/manifest.json) of 10,485,760 uncompressed proof bytes. Compression does not remove that limit. The JSP evidence package includes the newer compiled source. Both one-file versions exceed that separate service limit; JSP uses an external-repository reference and does not impose that Conjectures.io payload cap.

## Reuse and citation

Please cite all four mathematical solvers and the exact version; [CITATION.cff](CITATION.cff) supplies citation metadata. The sources include OpenAI mathematics and depend on Lean, Mathlib and Formal Conjectures. Original source notices and the [upstream license texts](licenses/) are preserved. Publication does not transfer authorship of those dependencies to this project's authors.
