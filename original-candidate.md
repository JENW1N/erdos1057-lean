# A synthesis proof of Erdős 1057

Attempt S0005. Written 2026-10-06, America/New_York.
Target: C(X)=X^(1−o(1)), where C counts Carmichael numbers at most X.

**Status: candidate complete proof, awaiting independent verification.** The new argument below has been checked by the parent solver and research agents. It uses two distinct OpenAI results at the fixed release commit stated below. One of them is unformalized, so the conclusion is only as reliable as that input. No Lean proof or external submission is claimed. The proof of the new transfer step is given in full, not left as a heuristic.

## 1. Inputs, provenance and exact scope

All OpenAI references below are pinned to commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, confirmed by the GitHub API on 2026-10-07 00:21 UTC. The release README explicitly allows that unformalized manuscripts may contain errors.

**Input S (smooth shifted-prime abundance).** For each fixed 0<δ<1/4 and all sufficiently large Y, there is a set P=P(Y,δ) of N=Y^(1−o(1)) primes in (2Y,5Y] such that every prime factor of p−1 is at most Y^δ. The o(1) may depend on δ. This is Theorem `thm:smooth` of OpenAI, *Weighted dilation graphs, smooth shifted primes and totient fibers*, 24 September 2026, family 011. Exact source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026/build/sections/00-introduction.tex .

Verification: family 011 has no catalogued Lean formalization. Its theorem contract and relevant internal estimates were inspected, but its long analytic proof has not been independently certified in this attempt. We use only fixed δ, the stated interval, and the stated cardinality; we do not assume uniformity as δ→0, positive density, a Poisson–Dirichlet law, or distribution of P in progressions.

**Input Z (uniform fixed zero-free half-plane).** Every Dirichlet L-function is nonzero in Re(s)>7/8, with the principal pole at s=1 excepted. This is the Dirichlet conclusion of OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s)>7/8*, 30 September 2026, family 003. Paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf . Formalization scope: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/003.md .

Verification: the catalogue describes Z as formalized uniformly over all moduli and characters. The solution points to `OAI.NumberTheory.DirichletL.Nonvanishing`; the comparator configuration permits only `propext`, `Quot.sound`, and `Classical.choice`. No compilation or full dependency-closure audit was performed here. The formalization explicitly excludes the paper's subsequent applications; we therefore derive the needed application below rather than assuming it is formalized.

**Classical ingredients.** We use the prime number theorem, functional equations of primitive Dirichlet L-functions, a uniform truncated explicit formula and local zero count, extension of characters from subgroups of finite abelian groups, finite-character orthogonality, elementary trigonometric bounds, and the Chernoff bound for independent Bernoulli variables. For the analytic formula and zero count, see D. Koukoulopoulos, *The Distribution of Prime Numbers*, Theorem 11.3 and Lemma 11.4(a), author's preliminary version: https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf . Its formula applies to x≥T≥2 without a q≤x restriction. We use T=x. Korselt's criterion is the final number-theoretic conversion; the original condition is composite, squarefree, and p−1|n−1 for every p|n, as stated in https://www.erdosproblems.com/1057 and the AGP paper.

Neither S nor Z directly counts Carmichael numbers. The new step is an ambient-character estimate, subgroup pruning, and subset-product argument connecting them.

## 2. Uniform prime-character estimate from Z

For a nonprincipal Dirichlet character χ modulo any positive integer q, define ψ(x,χ)=Σ_{n≤x}Λ(n)χ(n). We claim, uniformly in q and χ,

    |ψ(x,χ)| ≪ x^(7/8) log²(qx),       x≥2.                 (2.1)

First take χ primitive. The functional equation and Z, also applied to the conjugate character, place every nontrivial zero ρ=β+iγ in 1/8≤β≤7/8. In particular |ρ| is bounded below uniformly when |γ|≤1. The local zero count gives

    Σ_{|γ|≤x} 1/|ρ| ≪ log(qx) log(2x).

The zero sum in the truncated explicit formula, with T=x, is therefore bounded by

    Σ_{|γ|≤x} |(x^ρ−1)/ρ|
       ≪ (x^(7/8)+1) log(qx) log(2x).

The truncation error is O(log²(qx)), absorbed in (2.1). The principal main term is absent because χ is nonprincipal.

If χ is imprimitive and induced by χ* of conductor q*|q, the difference of the two ψ sums is supported on powers of primes dividing q. Its absolute value is at most O(log q log(2x)), also absorbed in (2.1). The implied constant is independent of q: all zero bounds use the same strip and the uniform local zero count. Thus exponentially large q are allowed.

Remove prime powers at cost O(sqrt(x) log²(2x)). Partial summation on the interval (2Y,5Y] then gives

    |Σ_{2Y<p≤5Y} χ(p)| ≪ Y^(7/8) log²(5qY).              (2.2)

For example, partial summation can start at 2Y, so it only needs weighted prime-sum estimates at arguments comparable to Y. No information about small primes or relative errors in an individual arithmetic progression is needed. Equation (2.2) is a character-sum estimate, not an AP main-term estimate.

## 3. The smooth-prime modulus

Fix 0<δ<1/16 once and for all. Let P be supplied by S and set

    N=|P|,       L=lcm{p−1:p∈P},       G=(Z/LZ)^×,
    Q=#{p prime:2Y<p≤5Y}.

All prime divisors of L are at most Y^δ, and every q-adic exponent of L is at most log(5Y)/log q. Consequently

    log L ≤ π(Y^δ) log(5Y) ≤ Y^δ log(5Y)=Y^(δ+o(1)).     (3.1)

Every ambient prime in (2Y,5Y] exceeds Y^δ and hence is coprime to L for large Y. In particular P gives elements of G. The prime number theorem gives Q∼3Y/log Y, while S gives N=Y^(1−o(1)). Define

    D=max(1,ceil(log₂|G|)),      R=ceil(64Q/N).

Then

    D≤Y^(δ+o(1)),      R=Y^o(1).                         (3.2)

For every nonprincipal character ξ of G, viewed as a Dirichlet character modulo L, (2.2) yields the common bound

    |Σ_{2Y<p≤5Y} ξ(p)| ≤ A,
    A=O(Y^(7/8) log²(5LY))=Y^(7/8+2δ+o(1)).             (3.3)

Because δ<1/16 and R=Y^o(1), we have RA=o(Q). This is the only place requiring δ<1/16. The bound uses the full ambient prime interval, not the smooth subset P.

## 4. Prune low-order concentration without losing half the primes

Start with H=G and S=P. While there exists a nontrivial character χ of the current H for which fewer than

    M=N/(2D)

members of S satisfy χ(p)≠1, remove those members of S and replace H by kerχ. Every retained p lies in the new H.

Each step reduces |H| by a factor of at least two. There are at most ceil(log₂|G|)≤D steps. Fewer than M primes are removed per step, so when the process stops,

    N/2 ≤ N'=|S| ≤ N.                                  (4.1)

At termination every nontrivial character χ of H has at least M members p∈S with χ(p)≠1. If H is trivial this condition is vacuous and all subset products are already the identity. No algorithmic efficiency is asserted or needed.

We will prove that for every nontrivial χ of the terminal H,

    Eχ:=Σ_{p∈S}(1−Reχ(p)) ≥ N/(100D R²).                (4.2)

The issue is that a high-order nontrivial character can take values extremely close to 1. Discrete separation alone cannot prove (4.2). The ambient estimate (3.3) supplies that missing control.

## 5. Fejér control of high-order characters

Extend χ from H to a character ξ of G; such an extension always exists for finite abelian groups. On p∈S its values equal χ(p). There are two cases according to the order of the extension ξ, not necessarily the order of χ.

If ord(ξ)<R, every value ξ(p)≠1 is a root of unity of order less than R, so

    1−Reξ(p) ≥ 1−cos(2π/ord(ξ)) ≥ 8/R².

For the last inequality use 1−cos(2π/m)=2sin²(π/m)≥8/m² for m≥2. At least M values are nontrivial by termination of the pruning. Hence Eχ≥8M/R², more than (4.2).

If ord(ξ)≥R, all ξ^j with 1≤j<R are nonprincipal. Use the nonnegative Fejér polynomial

    F_R(e^(iθ)) = (1/R)|Σ_{j=0}^{R−1}e^(ijθ)|²
                =1+2Σ_{j=1}^{R−1}(1−j/R)cos(jθ).

By (3.3),

    Σ_{2Y<p≤5Y} F_R(ξ(p)) ≤ Q+2RA ≤2Q                 (5.1)

for sufficiently large Y. For the angular representative −π≤θ≤π, if |θ|≤1/R, then ReΣ_{j=0}^{R−1}e^(ijθ)≥R cos(1)>R/2, and therefore F_R(e^(iθ))≥R/4. Equation (5.1) implies that at most

    8Q/R ≤ N/8

of the ambient primes have |arg ξ(p)|≤1/R. In particular this bounds the number among S. Since N'≥N/2, at least 3N'/4 members of S lie outside that arc. For them

    1−Reξ(p) ≥1−cos(1/R) ≥2/(π²R²).

Thus Eχ≥3N'/(2π²R²)≥3N/(4π²R²), again more than (4.2).

This proves (4.2) for every nontrivial terminal character. The argument does not assume that S itself is equidistributed. The extension ξ can have much larger order than χ; the high-order Fejér case explicitly handles that possibility.

## 6. Random subset products and their count

Fix constants η and ν satisfying

    2δ<η<1,       0<ν<1.

Put t=Y^η and ρ=t/N'. Since N'=Y^(1−o(1)), eventually 0<ρ<1/2. Choose each prime of S independently with probability ρ, and call the random subset B. Its expected size is t.

For any character χ of H, independence gives

    E[χ(Π_{p∈B}p)] = Π_{p∈S}(1−ρ+ρχ(p)).

For |z|=1,

    |1−ρ+ρz|² =1−2ρ(1−ρ)(1−Re z),

so every nontrivial character satisfies

    |E[χ(Π_{p∈B}p)]|
      ≤exp(−ρ(1−ρ)Eχ)
      ≤exp(−t/(200D R²)).                              (6.1)

Here (4.2), N'≤N and 1−ρ≥1/2 were used. Character orthogonality gives

    |Pr[Π_{p∈B}p=1 in H]−1/|H||
      ≤ ((|H|−1)/|H|) exp(−t/(200D R²)).

Now D R²≤Y^(δ+o(1)), while log|H|≤log L≤Y^(δ+o(1)). Since η>2δ,

    t/(200D R²) −log|H| →+∞.

Therefore the identity probability is at least 1/(2|H|) for sufficiently large Y. For H trivial it is exactly one, so the same lower bound holds without any character argument.

The Chernoff estimate gives

    Pr[||B|−t|>νt] ≤2exp(−ν²t/3)=o(1/|H|),             (6.2)

because η>δ. Thus at least 1/(4|H|) of the Bernoulli probability belongs to identity subsets whose sizes lie in [(1−ν)t,(1+ν)t]. A particular such subset of size s has probability

    ρ^s(1−ρ)^(N'−s) ≤ρ^s ≤ρ^((1−ν)t).

Consequently their number K satisfies

    K ≥(4|H|)^(-1)(N'/t)^((1−ν)t),
    log K ≥(1−ν)t(log N'−log t)−log(4|H|).             (6.3)

Since log N'=(1−o(1))log Y and η>δ, the last group-size term is o(t log Y). Hence

    log K ≥(1−ν)(1−η−o(1))t log Y.                     (6.4)

## 7. Korselt conversion and every large X

For each counted subset B put n=Π_{p∈B}p. These primes are distinct; |B|≥(1−ν)t→∞, so n is squarefree and composite. Its product is the identity in H⊂G, hence n≡1 mod L. Every selected prime satisfies p−1|L by definition. Therefore p−1|n−1 for every p|n, and Korselt's criterion makes n a Carmichael number.

Different subsets give different n by unique factorization. Every such n is at most

    X(Y)=(5Y)^((1+ν)Y^η).

Combining with (6.4) gives

    liminf_{Y→∞} log C(X(Y))/log X(Y)
      ≥ ((1−ν)/(1+ν))(1−η).                           (7.1)

This yields all large X, not just a subsequence. The function X(Y) is continuous, strictly increasing for Y>1, and tends to infinity. For any sufficiently large real X choose the unique real Y>1 solving X=X(Y). Inputs S and the estimates apply for every sufficiently large real Y with the fixed δ,η,ν. Thus the same asymptotic lower bound holds at every sufficiently large X.

Given ε>0, choose positive η,ν sufficiently small that ((1−ν)/(1+ν))(1−η)>1−ε. Next choose δ<min(η/2,1/16), fixed before letting Y grow. The argument gives C(X)≥X^(1−ε) for all sufficiently large X (shrinking the margin in the parameter choice if needed). Also C(X)≤floor(X)≤X. Hence

    lim_{X→∞} log C(X)/log X =1,

which is the exact intended main target. In particular C(X)>0 eventually, so the real logarithms in the target are well-defined in the limiting regime.

## 8. New contribution, earlier approaches and novelty audit

The borrowed ingredients separately supply smooth prime predecessors and a fixed zero-free half-plane. Subgroup pruning and Fourier/Bernoulli subset products are already present in D. Larsen, *Bertrand's Postulate for Carmichael Numbers*, arXiv:2111.06963v2, Section 4, https://arxiv.org/html/2111.06963v2 . We expressly credit that strategy. Larsen's quantitative pruning uses a cost governed by the full group exponent. The new bridge here uses uniform ambient prime-character sums at exponentially large L and a Fejér polynomial to handle high-order characters; the remaining phase-separation cost is only R²=Y^o(1). This produces a compatible reservoir of size Y^(1−o(1)) and bypasses the full-exponent cost. The argument never invokes near-linear least primes in APs or equidistribution of smooth primes in large progressions.

This bypasses the exponent loss in the AGP/Harman multiplier construction. Early attempted shortcuts—pigeonhole collisions treated as identity products, replacing the Davenport constant by the largest local CRT order, or reading relative AP precision out of an absolute Type II error—were rejected and are retained in the auxiliary reports. They are not steps of this proof.

Fresh site evidence in `eligibility.md` records the open target and terms v6/review v3. Wright's 2020 conditional density theorem assumes a different, stronger near-linear least-prime hypothesis and does not unconditionally settle this target. Larsen's Bertrand construction and the September 2026 public deterministic algorithm at https://github.com/jdb19937/carmichael/blob/main/carmichael.tex concern construction beyond a bound, not C(X)=X^(1−o(1)). Neither provides this Fejér/pruning transfer. Limited targeted searches did not find a prior exact resolution or public formalization of the target. This is not an exhaustive literature search or a binding novelty decision.

The current policy allows borrowing ingredients; a shared conclusion or conventional strategy alone does not establish `NOT_NOVEL`. No earlier source identified in this attempt directly gives the full unconditional Carmichael counting conclusion by this argument. A final eligibility decision still requires the actual proof and source comparison, and eventually a valid Lean artifact. No payment, submission intent, external publication or reward claim was made.

## 9. Dependencies and gaps audit

1. **New transfer step:** Sections 2–7 give an internally complete argument; there is no remaining progression-distribution or spectral hypothesis. Character extension, varying Fejér length, adaptive pruning, all-X coverage, distinctness and compositeness are explicitly checked. Independent agent reviews are saved in the attempt directory.
2. **Smooth-prime input S:** unformalized OpenAI manuscript claim, not independently certified. If its proof is erroneous, the target conclusion is not established by this report. This is the principal external reliability limitation.
3. **Zero-free input Z:** catalogued Lean result with exact uniform Dirichlet scope matching the proof. The declared certificate was inspected at the scope/configuration level, not locally rerun or fully audited. Its validity is another dependency.
4. **Explicit formula:** the crucial large-conductor use was checked against a primary mathematical reference; no q≤Y condition is imposed. Section 2 derives the consequence instead of assuming the manuscript's AP corollary covers exponentially large L.
5. **Novelty/openness:** fresh status and terms were saved with dated URLs and hashes. No equivalent occupied reservation was identified in the active registry titles. Screening does not guarantee a future reward or exclude undiscovered prior work.
6. **Formalization:** intentionally not performed, as requested. A prose proof depending on an unformalized input is not a Lean-accepted submission. No completion certificate from conjectures.io is claimed.
7. **Internal review artifacts:** `proof-review.md` independently checks the complete preferred transfer; `qr-character-audit.md` verifies the unrestricted-conductor explicit-formula step and another full derivation; `spectral-bridge.md` gives a separate finite-group derivation, prior-art comparison and exact toy checks. The companion `spectral-bridge-checks.json` records 65,535 ambient and 32,767 terminal characters checked exactly in a finite model. These checks support the transfer, not the long analytic proof of S. The source-level partial audit of S is recorded separately as `smooth-input-proof-audit.md`.

The result should be independently verified first as a transfer theorem from S and Z, and then by auditing those two inputs. If either input fails, preserve the rigorous transfer theorem as an intermediate result and revise the completion claim accordingly.