import OAI.NumberTheory.DirichletL.RowCompletion.ZeroFreeRegion

/-! Pointwise nonprincipal specialization for measuring the actual analytic dependency closure. -/

noncomputable section
open scoped Classical BigOperators ContDiff
namespace OAI.ApplicationAudit
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open ShortDraftHeckeBridge
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open SixthPowerAverage CompactMellinBridge InitialMeanSquare CanonicalRowCompletion

theorem nonprincipal_open_strip_of_theta_models {q₀ : ℕ} [NeZero q₀]
    (χ : DirichletCharacter ℂ q₀) (hχ : χ ≠ 1)
    (S : Finset (Ideal ActualEisensteinCubic.O))
    (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S (conjugateMonoid (normCharacter χ)) ρ q levelBound)
    (z : ℂ) (hz : (23:ℝ)/24<z.re) (hz1 : z.re<1) : χ.LFunction z≠0 := by
  let W : ℝ→ℂ:=ConcreteCompactWeight.weight z
  have hW : ContDiff ℝ ∞ W:=ConcreteCompactWeight.weight_smooth z
  have hWs : ∀x,x≤1 ∨ 2≤x→W x=0:=ConcreteCompactWeight.weight_support z
  have hM:=weightedCompactMellin_analytic χ S hbad hSp ρ q levelBound hρ hq hlevel hmodels W hW hWs
  have hE:=finiteEulerFactor_analytic χ S hSp ((23:ℝ)/24)
  have hH : AnalyticOnNhd ℂ (SmoothMobiusCorrection.eulerCorrection χ S)
      {s : ℂ | (23:ℝ)/24<s.re} :=
    (SmoothMobiusCorrection.eulerCorrection_analytic χ S).mono (by intro s hs;change 0<s.re;change (23:ℝ)/24<s.re at hs;linarith)
  have hWanalytic:=compact_weight_mellin_analytic W hW hWs ((23:ℝ)/24)
  have hnotboth : χ≠1 ∨ baseChangeChar χ≠1 := Or.inl hχ
  have hzneq : z≠1 := by intro he;subst z;norm_num at hz1
  exact (pair_zero_free_of_identity_gt_two χ (baseChangeChar χ) hnotboth
    ((23:ℝ)/24) (by norm_num)
    (fun s=>(finiteEulerFactor χ S s*SmoothMobiusCorrection.eulerCorrection χ S s)*
      mellin (fun Z : ℝ=>weightedCompactSum χ S W Z⁻¹) (-s))
    (mellin W) ((hE.mul hH).mul hM) hWanalytic
    (corrected_weighted_mellin_identity χ S hSp W hW hWs)
    z hz hzneq (ConcreteCompactWeight.weight_mellin_ne_zero z)).1

theorem nonprincipal_LFunction_ne_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (z : ℂ)
    (hz : (23 : ℝ) / 24 < z.re) : χ.LFunction z ≠ 0 := by
  by_cases hz1 : z.re < 1
  · have hm := hasCanonicalThetaModels_of_fixed_shell_models
      (reflectionExcludedPrimes q) (CanonicalCoefficientClass.initialBase χ)
      (CubicEisenstein.fixedReflectionRayCount (reflectionConductor q)
        (reflectionConductor_ne_zero q (NeZero.ne q)))
      actualReflectionScale 1 CompletedGauss.completedRamifiedStep
      (CubicEisenstein.fixedCuspLevelBound (reflectionConductor q))
      (actual_fixedShellModels q (NeZero.ne q) χ)
    exact nonprincipal_open_strip_of_theta_models χ hχ (reflectionExcludedPrimes q)
      (reflectionExcludedPrimes_bad q) (reflectionExcludedPrimes_prime q)
      1 CompletedGauss.completedRamifiedStep
      (CubicEisenstein.fixedCuspLevelBound (reflectionConductor q))
      (by norm_num) CompletedGauss.completedRamifiedStep_gt_one
      (reflectionLevelBound_ge_one q (NeZero.ne q)) hm z hz hz1
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
      (le_of_not_gt hz1)

end OAI.ApplicationAudit
