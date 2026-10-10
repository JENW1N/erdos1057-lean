# Erdős 1057 / JSP-000877: mathematical account of the submitted proof

**Mathematical solvers:** Jensen Kohlmeyer (JENW1N / jenw1n), Liam Kruer (lkruer), Will Howe (H0W4RD-dev), and Grant Huffman (Ghuffy1). See [authorship and contributions](AUTHORS.md) for joint credit, AI assistance, and attribution of third-party work.

This account explains the mathematical content and organization of the October 8 modular Lean proof. The October 9 [standalone revision](standalone/Challenge.lean) establishes the same explicitly checked target; its [version and verification record](standalone/BUILD.md) is separate. The module links below identify the preserved October 8 source and are not a claim that all intermediate declarations in the two revisions are byte-identical. The linked formal sources supply the detailed proof steps, including the analytic input and the construction of smooth shifted primes. This document is a guide to that complete formal argument, not a claim that the original short manuscript alone proved all of its inputs. No new mathematical proof development or independent human review was performed while preparing this account.

## 1. The assertion and its formal statement

Let $C(x)$ count the Carmichael numbers at most $x$. The assertion is

$$
\lim_{x\to\infty}\frac{\log C(x)}{\log x}=1,
$$

usually written $C(x)=x^{1-o(1)}$. The submitted theorem concerns this exponent-one asymptotic. It does not assert Pomerance's finer conjectural asymptotic.

The [challenge source](baseline/formal-conjectures/FormalConjectures/ErdosProblems/1057.lean#L45) defines $C(x)$ by the finite cardinality of the Carmichael numbers bounded by $x$. The final declaration is [Bounty.target](modular/src/ActualErdos1057Target.lean#L545). Its recorded printed type is

    Bounty.target : True ↔
      Filter.Tendsto
        (fun x => Real.log (Erdos1057.carmichaelCounting x) / Real.log x)
        Filter.atTop (nhds 1)

The True on the left records the affirmative answer to the challenge's question. The substantial conclusion is the limit on the right. The [audit source](verification/AuditTarget.lean) checks exact agreement with the challenge type and checks the axiom closure of this separate proof. The imported challenge contains conjecture placeholders; those placeholders are not presented as proofs of the result.

The formal development also proves the [equivalence with eventual power lower bounds](modular/src/ExpandedFrontier.lean#L40313): for every positive $\varepsilon$, eventually $C(x)\ge x^{1-\varepsilon}$. The elementary upper bound $C(x)\le x$, together with these lower bounds, gives the stated limit.

## 2. Actual analytic input: a 23/24 zero-free half-plane

The current proof uses the following nonprincipal Dirichlet $L$-function statement:

$$
\chi\ne 1,\quad \Re s>23/24
\quad\Longrightarrow\quad L(s,\chi)\ne0.
$$

The source declaration is [OAI.ApplicationAudit.nonprincipal_LFunction_ne_zero](modular/src/PinnedNonprincipal.lean#L41). It uses the included OpenAI analytic development through OAI.NumberTheory.DirichletL.RowCompletion.ZeroFreeRegion. Its proof treats the strip below real part one through the theta-model construction and uses Mathlib's nonvanishing theorem on and to the right of one. The functions here are the actual Mathlib Dirichlet $L$-functions: the primitive-character wrapper is [defined explicitly](modular/src/ExpandedFrontier.lean#L114).

[Bounty.WeakZeroFree.actual_zero_free](modular/src/WeakCandidateTarget.lean#L11) supplies this theorem to the primitive-character interface. The subsequent [Mangoldt-sum estimate](modular/src/WeakCandidateTarget.lean#L16) has exponent $95/96$: a uniform constant bounds the twisted sum by

$$
C x^{95/96}\log(qx),\qquad x\ge2,
$$

for primitive nonprincipal characters of modulus $q$. The intervening formal argument includes the analytic passage to a smoothed sum, removal of smoothing, and the required prime-character companions. The proof needs a fixed positive power saving, not specifically the historical exponent $7/8$.

For the final reservoir, [wideAmbientPrimeCancellation_of_zero_free](modular/src/WeakCandidateTarget.lean#L658) supplies cancellation on the ambient prime interval. The [precise interface](modular/src/ExpandedFrontier.lean#L97954) permits moduli $L$ with

$$
\log L\le y^\delta\log(5y)
$$

and bounds every nonprincipal character sum over primes in $(y/4,5y]$ by $y^{95/96+2\delta+\sigma}$, for fixed positive loss parameter $\sigma$ and sufficiently large $y$. This large-modulus statement is used directly; a qualitative fixed-modulus equidistribution statement would not replace it.

## 3. Constructing the smooth shifted-prime supply

The sufficient prime supply in the current proof has a wider interval than the historical manuscript. The [exact contract](modular/src/ExpandedFrontier.lean#L97895), WideSmoothShiftedPrimeSupply, says that for every fixed $0<\delta<1/4$ and every $\sigma>0$, all sufficiently large $x$ admit a finite set $P$ of primes such that

$$
P\subset(2x,33x],\qquad |P|\ge x^{1-\sigma},
$$

and every prime divisor of $p-1$, for every $p\in P$, is at most $x^\delta$.

This definition is a contract. Its presence alone is not evidence that it holds. The current final proof supplies it through the candidate-weight construction and the following chain.

The [weighted prime-mass contract](modular/src/ExpandedFrontier.lean#L139659) asks for sufficient total candidate weight on integers $u$ for which $2u+1$ is prime. The candidate integers lie in the product window $(e^T,16e^T]$. The established support and prime-factor estimates ensure that the predecessors of the resulting shifted primes are smooth. [eventually_candidate_shifted_prime_supply](modular/src/ExpandedFrontier.lean#L139605) turns weighted mass into a cardinality bound, uses the injectivity of $u\mapsto2u+1$, and proves the predecessor-factor condition. [wide_smooth_supply_of_candidate_prime_mass](modular/src/ExpandedFrontier.lean#L139668) then obtains the displayed prime supply.

The mass itself is obtained by a sieve comparison. [candidate_shifted_prime_fraction_of_fixed_slot_error_bound](modular/src/WeakCandidateTarget.lean#L1538) compares a positive rough-number contribution with unbalanced and balanced composite contributions, with a controlled replacement error. The next [mass-supply theorem](modular/src/WeakCandidateTarget.lean#L1620) derives the weighted contract from the fixed-slot replacement estimate and the actual zero-free input. The needed replacement is supplied by component bounds and active-block estimates; this is the sequence of [target implications](modular/src/WeakCandidateTarget.lean#L1635) through line 1655.

The remaining active-block estimates are reduced to selected central moments by [actual_candidate_half_active_blocks_of_selected_central_moments](modular/src/WeakActualRawBlocks.lean#L4119). The [selected-residue interface](modular/src/WeakSelectedResidueTransfer.lean#L560) makes the relevant estimate precise: after choosing finite probes and disjoint groups of large primes, it bounds the original signed residue model, uniformly over the specified real frequencies and nonzero determinant parameters, by a negative power whose exponent scales with the chosen moment length. Its quantifiers choose the fixed precision parameters before passing to sufficiently large scale.

Crucially, the submitted final proof does not leave this interface as an assumption. [candidate_uniform_numbered_residue_bounds](modular/src/ActualErdos1057Target.lean#L336) proves the numbered version from the actual prime-pool, operator, and high-rank estimates. [candidate_selected_residue_bounds](modular/src/ActualErdos1057Target.lean#L533) converts it to the selected interface. [target_of_selected_residue_bounds](modular/src/WeakSelectedResidueTransfer.lean#L663) passes through the central-moment and active-block chain, and the final Bounty.target supplies the proved bound for each positive scale. The analytic and combinatorial obligations are therefore in the formal source, rather than represented by a remaining prime-supply hypothesis at the final theorem.

## 4. From those primes to many Carmichael numbers

The [rescaling theorem](modular/src/ExpandedFrontier.lean#L97932) applies the wider supply at $x=y/8$, absorbs fixed constants into the freely chosen power loss, and produces a prime set in $(y/4,5y]$. Let $L$ be the least common multiple of its prime predecessors. Smoothness bounds the size of $\log L$; the selected primes represent units modulo $L$.

The next stages implement the finite transfer described in the original candidate. [Subgroup pruning](modular/src/ExpandedFrontier.lean#L5673) removes poorly supported character directions while retaining a substantial part of the prime set. The proof then extends characters from the retained subgroup to the ambient unit group. Low-order characters have discrete separation from one. High-order characters are handled with the nonnegative Fejér polynomial and the ambient prime-character bound. The relevant formal endpoints are [character_energy_lower_of_pruned_ambient](modular/src/ExpandedFrontier.lean#L6180) and [exists_pruned_energy_reservoir](modular/src/ExpandedFrontier.lean#L6276).

Independently selecting the retained primes with a fixed probability defines a Bernoulli distribution on subsets. Its character transform factors into one term per prime. The energy estimate makes every nontrivial character contribution small, giving a lower bound for the probability that the subset product is the identity. The sources contain the [factor estimate](modular/src/ExpandedFrontier.lean#L6409), [identity-mass estimate](modular/src/ExpandedFrontier.lean#L6555), and [subset-size tail bound](modular/src/ExpandedFrontier.lean#L6736). Restricting to subsets near the expected size still leaves enough probability, which becomes a lower bound on the number of such subsets.

Every counted subset has at least two distinct primes. Its product is squarefree and composite, and its residue is one modulo $L$. Since every selected prime satisfies $p-1\mid L$, it also satisfies $p-1\mid n-1$ for the product $n$. The sufficient direction of Korselt's criterion makes $n$ a Carmichael number. Distinct subsets have distinct products. [finite_carmichael_transfer](modular/src/ExpandedFrontier.lean#L7011) combines these statements; [finite_carmichael_counting_bound](modular/src/ExpandedFrontier.lean#L7117) supplies the form used in the asymptotic argument.

## 5. Parameters and coverage of every large bound

The source does not retain the manuscript's numerical condition $\delta<1/16$ as the only cancellation constraint. For a character-saving exponent $\beta<1$, [asymptotic_density_parameters_at](modular/src/ExpandedFrontier.lean#L41061) chooses positive $\delta,\eta,\nu,\sigma$ with

$$
\begin{gathered}
\delta<1/16,\qquad \nu<1,\qquad
2\delta+4\sigma<\eta<1-\sigma,\\
\beta+2\delta+2\sigma<1,\qquad
1-\varepsilon<\frac{1-\nu}{1+\nu}(1-\eta-2\sigma).
\end{gathered}
$$

Its explicit choice is

$$
e=\min\{\varepsilon/16,(1-\beta)/16,1/32\},\quad
\delta=e/8,\quad \eta=\nu=e,\quad \sigma=e/16.
$$

Here $\beta=95/96$. In particular the displayed cancellation inequality requires $\delta+\sigma<1/192$; the original numerical bounds cannot simply be copied unchanged.

The expected subset size grows like $y^\eta$. The [size parameter](modular/src/ExpandedFrontier.lean#L7267) bounds the resulting products by $(5y)^{(1+\nu)y^\eta}$. The entropy lower bound for the number of products, with the displayed parameter inequalities, gives the desired exponent $1-\varepsilon$. The passage to every sufficiently large real bound is included in [eventual_carmichael_power_lower_of_exp_entropy](modular/src/ExpandedFrontier.lean#L39935) and the [general reservoir-to-target theorem](modular/src/ExpandedFrontier.lean#L41197). It is not merely a result on an unspecified subsequence.

## 6. Historical record and verification scope

The unchanged S0005 candidate is retained as an earlier record of the proposed synthesis. Its stated caveats remain part of that record: its narrow-interval smooth-prime input was unformalized, and its cited $7/8$ zero-free formalization had not been rerun locally. The current development uses the different sufficient statements explained above. It does not retroactively establish that the manuscript was fully verified on its internal date, or certify all of its stronger intermediate statements.

Likewise, the older introductory comments in ExpandedFrontier.lean describe a partial stage of that module. The later imported modules and final theorem are essential. Neither an old incomplete header nor an intermediate conditional theorem should be substituted for inspection of the submitted final target and its dependencies.

The preserved audit records a passed check of the 320-module assembly on 8 October 2026, completed at 16:44:16 UTC, with no parameters on Bounty.target and only propext, Classical.choice, and Quot.sound in its axiom closure. The export completed at 16:45:17 UTC. These are existing author-side machine-check records. They are not organizer acceptance or an independent mathematical referee report.

The environment is pinned to Lean 4.35.0-rc2 and the recorded Mathlib and package revisions. [Reproduction instructions](BUILD.md) supply the portable clean-build procedure; that new portable procedure was source-checked but has not been executed as a full rebuild during publication. The standalone candidate and platform admission have separate statuses. The complete mathematical proofs submitted for review are the original modular formal source and the later standalone revision, each with its dependency closure and separate [October 10 verification evidence](verification/standalone-2026-10-10/report.md).
