# Erdős 1057 literature and priority review

**No earlier complete, unconditional proof of the exact Carmichael counting limit was located in this bounded search. This is support for submitting a priority claim, not certification of first priority.**

The result being compared is `log C(x) / log x → 1`, where `C(x)` counts every Carmichael number up to a real bound `x`. The lower bound must apply to every sufficiently large bound. Infinitude, finite computations, a fixed exponent below one, and a conditional exponent-one result do not establish this conclusion.

## Prior results and nearby claims

| Source | Result relevant to this review | Relation to the submitted target |
| --- | --- | --- |
| [Alford, Granville and Pomerance, 1994](https://math.dartmouth.edu/~carlp/PDF/paper95.pdf) | Infinitely many Carmichael numbers and a power lower bound | Foundational partial result |
| [Lichtman, arXiv 2211.09641](https://arxiv.org/html/2211.09641) | Corollary 1.2 gives exponent 0.3389 | Fixed exponent below one |
| [Runbo Li, arXiv 2308.04458v8](https://arxiv.org/html/2308.04458v8) | Theorem 10 claims exponent 0.34 | Still a partial bound; this review did not validate its sieve computations |
| [Wright, A conditional density for Carmichael numbers](https://www.cambridge.org/core/journals/bulletin-of-the-australian-mathematical-society/article/conditional-density-for-carmichael-numbers/E732DD46A7CF3D0EE22BB21D16D72645) | Near-linear counting under a strong least-prime-in-progressions hypothesis | Conditional |
| [Larsen, arXiv 2111.06963](https://arxiv.org/abs/2111.06963) | Bertrand-type existence and lower bounds in intervals | Does not establish the global exponent-one count |
| [Larsen, arXiv 2504.09056](https://arxiv.org/abs/2504.09056) | Carmichael numbers in admissible arithmetic progressions | Different conclusion |
| [Larsen and Wright, arXiv 2510.16632](https://arxiv.org/html/2510.16632) | Carmichael numbers with prescribed sufficiently large numbers of prime factors | Existence rather than the required count |
| [Bharadwaj and Rodgers, arXiv 2402.11884](https://arxiv.org/abs/2402.11884) | Poisson–Dirichlet laws under distribution hypotheses | Relevant analytic background, not this unconditional count |
| [Wright, arXiv 2607.02738](https://arxiv.org/abs/2607.02738) | Generalized near-linear counting with a least-prime hypothesis | Conditional |
| [jdb19937 construction manuscript](https://github.com/jdb19937/carmichael/blob/main/carmichael.tex) | A claimed deterministic construction beyond a given bound | An algorithmic/existence claim does not supply the required density |
| [Gupta, Webster and Webster, arXiv 2610.02550](https://arxiv.org/abs/2610.02550) | Compression of finite Carmichael tabulations | Computational data, not the asymptotic theorem |
| [OpenAI, weighted dilation graphs and smooth shifted primes](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026/build/sections/00-introduction.tex) | Supplies prior smooth-prime and operator ingredients; explicitly distinguishes the additional progression input for Carmichael constructions | Prior work incorporated in this proof, not a stated proof of the complete Carmichael endpoint |
| [OpenAI, The Quasi-Riemann Hypothesis](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex) | Prior analytic input; no Carmichael counting conclusion found in the reviewed manuscript | Must be credited; the submitted argument uses its actual formal 23/24 route |
| [Polson, Sokolov and Zantedeschi, SSRN 6913501](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6913501) | Abstract discusses AGP density and a derandomization gap | Abstract only; full text returned HTTP 403, so it has not been cleared by a full-text comparison |

The latest inspected `openai/math` branch tip was `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, dated October 8, 2026, 05:20 UTC. Its weighted-dilation introduction and companion Poisson–Dirichlet introduction were inspected. They discuss Carmichael applications and the separate distribution input; neither introduction states the submitted full Carmichael counting result. This does not transfer authorship of their ingredients to this project.

## Prize submissions and chronology

The review searched open, merged and closed Prize PRs by JSP-000877, Erdős 1057, the title and repository references. The reviewed earlier alternatives included [1094](https://github.com/TheJustinSunPrize/awards/pull/1094), [1559](https://github.com/TheJustinSunPrize/awards/pull/1559), [2488](https://github.com/TheJustinSunPrize/awards/pull/2488), [2669](https://github.com/TheJustinSunPrize/awards/pull/2669), [3355](https://github.com/TheJustinSunPrize/awards/pull/3355) and [4847](https://github.com/TheJustinSunPrize/awards/pull/4847). They concern finite witnesses, duplicate witness claims or a mismatched problem number. None of those reviewed alternatives supplies the complete counting limit.

The original public proof commit is `55fe0f1cd4d8e63b417eb122067ab3e307b39f32`; GitHub records publication of [release v2026.10.08](https://github.com/JENW1N/erdos1057-lean/releases/tag/v2026.10.08) at **October 8, 2026, 18:29:25 UTC**. That server-side release record is distinct from user-set commit dates and the historical manuscript's internal October 6 date. The newer source was published at `a95a41e18d13474150be7b127a4231e8c4c0e3af` on October 10; its October 9 compile timestamp does not backdate publication.

The versions differ internally. Each proof version must be assessed on its own evidence; newer verification does not automatically establish the earlier version's validity. Preserve the original release and submit the new evidence through [the existing PR](https://github.com/TheJustinSunPrize/awards/pull/4874).

## Scope of the conclusion

Mathematical priority and Lean formalization priority are separate under the [Prize process](https://github.com/TheJustinSunPrize/awards/blob/16877004910734cecca83cc5af0fec2f5a4125b3/docs/award-process.md). The committee must assess the complete result, original repository, public chronology and contributions. Reuse of credited OpenAI mathematics, Larsen's methods, Mathlib and other foundations is relevant to that attribution assessment.

Search results may omit private work, unindexed publications and new developments. The unavailable SSRN full text remains an explicit comparison limit. The defensible conclusion is that this review located no earlier complete unconditional proof of the exact target; it cannot guarantee that no such proof exists or that the Prize will award priority.

The earlier [review text](literature-2026-10-10.txt) is retained as a record of the initial read-only review. Its build and publication status statements precede this update and are superseded by the completed verification reports and current submission record.
