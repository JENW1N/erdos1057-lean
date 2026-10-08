import WeakActualOriginalDecay

/-! Nonempty-pattern sums and complete comparison decay from the actual zero-free theorem. -/

open scoped Topology BigOperators Classical

-- Source module: CandidateNonemptyPatternSum

/- The exact nonempty-pattern sum preserves arbitrary power saving. -/

open Filter Finset Real
open scoped Classical
namespace Bounty

theorem exists_candidate_nonempty_pattern_sum_exponent {c : ℝ} (hc : 0 < c)
    (J : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (groups : Finset ℕ), groups ⊆ candidatePIndices c L →
      ∀ (ell : ℕ) (probes : groups → Finset (Fin J)) (r t : Finset groups),
      Disjoint r t → ∀ (D : ℝ) (F : RepeatedBigPrimePatternPair (ell := ell) probes r t → ℂ),
      (∀ ab, ‖F ab‖ ≤ L^(-(D+A))) → ‖∑ ab, F ab‖ ≤ L^(-D) := by
  obtain ⟨v,A,_hv,hA,hinputs⟩ := exists_candidate_shared_error_inputs hc J
  refine ⟨A*log 2+1,by positivity,?_⟩
  filter_upwards [hinputs,eventually_ge_atTop (2 : ℝ)] with L hinput hL
  intro groups hgroups ell probes r t hrt D F hF
  have hL0 : 0 < L := by linarith
  have hslots : ((J*Fintype.card groups : ℕ) : ℝ) ≤ A*log L := by
    simpa only [Fintype.card_coe] using (hinput groups hgroups).1
  have hcard := harmonic_pattern_card_power (ell := ell) probes r t hrt hL hA hslots
  have hpair : (Fintype.card (RepeatedBigPrimePatternPair (ell := ell) probes r t) : ℝ) ≤
      L^(A*log 2+1) := by
    simp only [RepeatedBigPrimePatternIndex,Fintype.card_sum,Fintype.card_unit,
      Nat.cast_add,Nat.cast_one] at hcard
    linarith
  calc
    ‖∑ ab, F ab‖ ≤ ∑ ab, ‖F ab‖ := norm_sum_le _ _
    _ ≤ ∑ _ab : RepeatedBigPrimePatternPair (ell := ell) probes r t,
        L^(-(D+(A*log 2+1))) := sum_le_sum (fun ab _ => hF ab)
    _ = (Fintype.card (RepeatedBigPrimePatternPair (ell := ell) probes r t) : ℝ)*
        L^(-(D+(A*log 2+1))) := by simp
    _ ≤ L^(A*log 2+1)*L^(-(D+(A*log 2+1))) :=
      mul_le_mul_of_nonneg_right hpair (rpow_nonneg hL0.le _)
    _ = L^(-D) := by rw [← rpow_add hL0]; congr 1; ring

end Bounty


-- Source module: ActualPrimeNonemptyDecay

/- Complete nonempty-pattern harmonic decay with the exact original signed weights. -/

open Finset Filter
open scoped Classical ComplexConjugate
namespace Bounty.WeakZeroFree

theorem exists_actual_prime_nonempty_harmonic_decay
    (hZeta : PrimitiveZeroFreeRightOf (23 / 24)) {c bWindow Kdet : ℝ}
    (hc : 0 < c) (hb : 0 < bWindow) (hKdet : 0 ≤ Kdet) :
    ∃ J₀ : ℕ, ∀ jStar : ℕ, J₀ < jStar →
      ∀ (D : ℝ) (J ell : ℕ) (B C R Kfull Tmod Sshift Cmod Sfreq W : ℝ),
      0 < ell → 0 ≤ B → 0 ≤ Kfull →
    ∃ S₀ : ℝ, 0 ≤ S₀ ∧ ∀ S : ℝ, S₀ ≤ S → ∀ᶠ L : ℝ in atTop,
      ∀ (rQ : ℕ) (hrQ : 0 < rQ) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*rQ) → Bool)
        (hkeep : take ((candidateAllocationOrder c L rQ).symm
          (candidateRoughSlot c L rQ jStar hrQ hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L rQ jStar) → ℝ)
        (lo hi : ℕ) (κM ν₀ ν₁ : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      0 ≤ κM → κM ≤ 1/50 → (qM : ℝ) ≤ L^Cmod → |ν₀| ≤ L^Sfreq → |ν₁| ≤ L^Sfreq →
      ∀ (σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      let P := fun g : candidatePIndices c L => candidatePBand (c*L) g.val
      let mass := fun g => ∑ p ∈ P g, 1/(p : ℝ)
      let pool := (candidatePIndices c L).biUnion (candidatePBand (c*L))
      let α₀ := fun n => (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ)*
        (χM (n : ZMod qM)*typeIIPhase ν₀ n)
      let α₁ := fun n => (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ)*
        (χM (n : ZMod qM)*typeIIPhase ν₁ n)
      let β := fun n => if n ∈ candidateRoughBand c L jStar then typeIIPhase σ n*χQ (n : ZMod qQ) else 0
      let γ := fun n => conj (candidateResidualPrimeCoefficient c L rQ jStar hrQ hj
        take hkeep (candidateAllocationFourierTwist c L rQ jStar take ξ) n)
      ∀ (probes : candidatePIndices c L → Finset (Fin J)) (r t : Finset (candidatePIndices c L))
        (hrt : Disjoint r t),
      (∀ g ∈ r ∪ t, g.val ∈ candidateBigPIndices c L) →
      ∀ (Q : ℕ), (Q : ℝ) ≤ L^R →
      ∀ U V : ℝ, Real.exp (bWindow*L) ≤ U → U ≤ Real.exp L →
        Real.exp (bWindow*L) ≤ V → V ≤ Real.exp L →
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L Kdet : ℤ)) (typeIIAdmissibleDeterminantBound L Kdet : ℤ),
      k ≠ 0 → (k.natAbs : ℝ) ≤ L^Kfull →
      ∀ j ∈ range (typeIISmoothDyadicCount L), ∀ a b : ℝ, |a| ≤ L^W →
      let Z := typeIISmoothDyadicScale U V (U*L^(-Kdet)) j
      ‖∑ ab : RepeatedBigPrimePatternPair (ell := ell) probes r t,
        ∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t (.inr ab)),
        (physicalAuxMass mass (repeatedBigPrimePatternCut probes r t (.inr ab)) aux : ℂ)*
          physicalFreePositiveHarmonicMain P mass probes r t hrt Q (L^(-B)) (L^(-C)) (.inr ab) aux
            a b Z k pool α₀ β γ α₁ β γ‖ ≤ L^(-D) := by
  obtain ⟨J₀,hbase⟩ := exists_actual_prime_original_harmonic_decay hZeta hc hb hKdet
  refine ⟨J₀,?_⟩
  intro jStar hjStar D J ell B C R Kfull Tmod Sshift Cmod Sfreq W hell hB hKfull
  obtain ⟨A,_hA,hsum⟩ := exists_candidate_nonempty_pattern_sum_exponent hc J
  obtain ⟨S₀,hS₀,hdecay⟩ := hbase jStar hjStar (D+A) J ell B C R Kfull Tmod Sshift
    Cmod Sfreq W hell hB hKfull
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [hdecay S hS,hsum] with L hdec hsumL
  intro rQ hrQ hj take hkeep ξ lo hi κM ν₀ ν₁ qM _ χM hκM hκmax hqM hν₀ hν₁
    σ qQ _ χQ hqQ hσ P mass pool α₀ α₁ β γ probes r t hrt hbig Q hQ
    U V hUlo hUhi hVlo hVhi k hk hk0 hkfull j hjd a b ha Z
  apply hsumL (candidatePIndices c L) (subset_refl _) ell probes r t hrt D
  intro ab
  exact hdec rQ hrQ hj take hkeep ξ lo hi κM ν₀ ν₁ qM χM hκM hκmax hqM hν₀ hν₁
    σ qQ χQ hqQ hσ probes r t hrt hbig ab Q hQ
    U V hUlo hUhi hVlo hVhi k hk hk0 hkfull j hjd a b ha

end Bounty.WeakZeroFree


-- Source module: ActualPrimeComparisonDecay

/- The full replacement error plus nonempty comparison term has arbitrary power saving. -/

open Finset Filter
open scoped Classical ComplexConjugate
namespace Bounty.WeakZeroFree

theorem exists_actual_prime_comparison_harmonic_decay
    (hZeta : PrimitiveZeroFreeRightOf (23 / 24)) {c bWindow Kdet : ℝ}
    (hc : 0 < c) (hb : 0 < bWindow) (hKdet : 0 ≤ Kdet) :
    ∃ J₀ : ℕ, ∀ jStar : ℕ, J₀ < jStar →
      ∀ (D : ℝ) (J ell : ℕ) (B C R Kfull Tmod Sshift Cmod Sfreq W : ℝ),
      0 < ell → 0 ≤ B → 0 ≤ Kfull →
    ∃ S₀ : ℝ, 0 ≤ S₀ ∧ ∀ S : ℝ, S₀ ≤ S → ∀ᶠ L : ℝ in atTop,
      ∀ (rQ : ℕ) (hrQ : 0 < rQ) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*rQ) → Bool)
        (hkeep : take ((candidateAllocationOrder c L rQ).symm
          (candidateRoughSlot c L rQ jStar hrQ hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L rQ jStar) → ℝ)
        (lo hi : ℕ) (κM ν₀ ν₁ : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      0 ≤ κM → κM ≤ 1/50 → (qM : ℝ) ≤ L^Cmod → |ν₀| ≤ L^Sfreq → |ν₁| ≤ L^Sfreq →
      ∀ (σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      let P := fun g : candidatePIndices c L => candidatePBand (c*L) g.val
      let mass := fun g => ∑ p ∈ P g, 1/(p : ℝ)
      let pool := (candidatePIndices c L).biUnion (candidatePBand (c*L))
      let α₀ := fun n => (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ)*
        (χM (n : ZMod qM)*typeIIPhase ν₀ n)
      let α₁ := fun n => (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ)*
        (χM (n : ZMod qM)*typeIIPhase ν₁ n)
      let β := fun n => if n ∈ candidateRoughBand c L jStar then typeIIPhase σ n*χQ (n : ZMod qQ) else 0
      let γ := fun n => conj (candidateResidualPrimeCoefficient c L rQ jStar hrQ hj
        take hkeep (candidateAllocationFourierTwist c L rQ jStar take ξ) n)
      ∀ (probes : candidatePIndices c L → Finset (Fin J)) (r t : Finset (candidatePIndices c L))
        (hrt : Disjoint r t),
      (∀ g ∈ r ∪ t, g.val ∈ candidateBigPIndices c L) →
      ∀ (Q : ℕ), (Q : ℝ) ≤ L^R →
      ∀ U V : ℝ, Real.exp (bWindow*L) ≤ U → U ≤ Real.exp L →
        Real.exp (bWindow*L) ≤ V → V ≤ Real.exp L →
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L Kdet : ℤ)) (typeIIAdmissibleDeterminantBound L Kdet : ℤ),
      k ≠ 0 → (k.natAbs : ℝ) ≤ L^Kfull →
      ∀ j ∈ range (typeIISmoothDyadicCount L), ∀ a b : ℝ, |a| ≤ L^W →
      let Z := typeIISmoothDyadicScale U V (U*L^(-Kdet)) j
      ‖(∑ i : RepeatedBigPrimePatternIndex (ell := ell) probes r t,
        ∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t i),
          (physicalAuxMass mass (repeatedBigPrimePatternCut probes r t i) aux : ℂ)*
            physicalPositiveHarmonicDifference P mass probes r t hrt Q (L^(-B)) (L^(-C)) i aux
              a b Z k pool α₀ β γ α₁ β γ) +
        (∑ ab : RepeatedBigPrimePatternPair (ell := ell) probes r t,
        ∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t (.inr ab)),
        (physicalAuxMass mass (repeatedBigPrimePatternCut probes r t (.inr ab)) aux : ℂ)*
          physicalFreePositiveHarmonicMain P mass probes r t hrt Q (L^(-B)) (L^(-C)) (.inr ab) aux
            a b Z k pool α₀ β γ α₁ β γ)‖ ≤ L^(-D) := by
  obtain ⟨J₀,hbase⟩ := exists_actual_prime_nonempty_harmonic_decay hZeta hc hb hKdet
  refine ⟨J₀,?_⟩
  intro jStar hjStar D J ell B C R Kfull Tmod Sshift Cmod Sfreq W hell hB hKfull
  obtain ⟨S₀,hS₀,hdecay⟩ := hbase jStar hjStar (D+1) J ell B C R Kfull Tmod Sshift
    Cmod Sfreq W hell hB hKfull
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [hdecay S hS,
    eventually_candidate_pattern_harmonic_decay hc hb hKdet
      (le_max_right R 0) (le_max_right C 0) J ell 0 (D+1),
    eventually_actual_prime_source_factor_properties hc S (hS₀.trans hS),
    eventually_actual_remaining_factor_properties hc,
    eventually_ge_atTop (2 : ℝ)] with L hdec herror hfactor hremain hL
  intro rQ hrQ hj take hkeep ξ lo hi κM ν₀ ν₁ qM _ χM hκM hκmax hqM hν₀ hν₁
    σ qQ _ χQ hqQ hσ P mass pool α₀ α₁ β γ probes r t hrt hbig Q hQ
    U V hUlo hUhi hVlo hVhi k hk hk0 hkfull j hjd a b ha Z
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hα₀ := hfactor κM hκM hκmax (Ioc lo hi) qM χM ν₀
  have hα₁ := hfactor κM hκM hκmax (Ioc lo hi) qM χM ν₁
  have hθ (n : ℕ) : ‖typeIIPhase σ n*χQ (n : ZMod qQ)‖ ≤ 1 := by
    rw [norm_mul,typeIIPhase_norm,one_mul]
    exact χQ.norm_le_one _
  have hβγ := hremain rQ jStar hrQ hj take hkeep ξ _ hθ
  have hQ' : (Q : ℝ) ≤ L^(max R 0) :=
    hQ.trans (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _))
  have hξ : L^(-(max C 0)) ≤ L^(-C) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (neg_le_neg (le_max_left _ _))
  have he := herror (candidatePIndices c L) (subset_refl _) probes r t hrt Q (L^(-B)) (L^(-C))
    hQ' hξ a b pool (fun g p hp => mem_biUnion.mpr ⟨g.val,g.property,hp⟩)
    α₀ β γ α₁ β γ
    (by simpa only [Real.rpow_zero] using hα₀.1)
    (by simpa only [Real.rpow_zero] using hβγ.1)
    (by simpa only [Real.rpow_zero] using hβγ.2.2)
    (by simpa only [Real.rpow_zero] using hα₁.1)
    (by simpa only [Real.rpow_zero] using hβγ.1)
    (by simpa only [Real.rpow_zero] using hβγ.2.2)
    U V hUlo hUhi hVlo hVhi k hk j hjd
  have hc' := hdec rQ hrQ hj take hkeep ξ lo hi κM ν₀ ν₁ qM χM hκM hκmax hqM hν₀ hν₁
    σ qQ χQ hqQ hσ probes r t hrt hbig Q hQ
    U V hUlo hUhi hVlo hVhi k hk hk0 hkfull j hjd a b ha
  calc
    _ ≤ L^(-(D+1)) + L^(-(D+1)) :=
      (norm_add_le _ _).trans (_root_.add_le_add he hc')
    _ = 2*L^(-(D+1)) := by ring
    _ ≤ L*L^(-(D+1)) := mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hL0.le _)
    _ = L^(-D) := by
      nth_rw 1 [← Real.rpow_one L]
      rw [← Real.rpow_add hL0]
      congr 1
      ring

end Bounty.WeakZeroFree


-- Source module: ActualRoughNonemptyDecay

/- Complete nonempty-pattern harmonic decay with the exact original signed weights. -/

open Finset Filter
open scoped Classical ComplexConjugate
namespace Bounty.WeakZeroFree

theorem exists_actual_rough_nonempty_harmonic_decay
    (hZeta : PrimitiveZeroFreeRightOf (23 / 24)) {c bWindow Kdet γrough vMax ρ : ℝ}
    (hc : 0 < c) (hb : 0 < bWindow) (hKdet : 0 ≤ Kdet)
    (hγrough : 0 < γrough) (hvMax : vMax < 1) (hρ : 0 < ρ) :
    ∃ J₀ : ℕ, ∀ jStar : ℕ, J₀ < jStar →
      ∀ (D : ℝ) (J ell : ℕ) (B C R Kfull Tmod Sshift Cmod Sfreq W : ℝ),
      0 < ell → 0 ≤ B → 0 ≤ Kfull →
    ∃ S₀ : ℝ, 0 ≤ S₀ ∧ ∀ S : ℝ, S₀ ≤ S → ∀ᶠ L : ℝ in atTop,
      ∀ (rQ : ℕ) (hrQ : 0 < rQ) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*rQ) → Bool)
        (hkeep : take ((candidateAllocationOrder c L rQ).symm
          (candidateRoughSlot c L rQ jStar hrQ hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L rQ jStar) → ℝ)
        (lo hi : ℕ) (aM vM ν₀ ν₁ : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      vM ≤ vMax → (qM : ℝ) ≤ L^Cmod → |ν₀| ≤ L^Sfreq → |ν₁| ≤ L^Sfreq →
      ∀ (σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      let P := fun g : candidatePIndices c L => candidatePBand (c*L) g.val
      let mass := fun g => ∑ p ∈ P g, 1/(p : ℝ)
      let pool := (candidatePIndices c L).biUnion (candidatePBand (c*L))
      let α₀ := fun n => (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM vM) n : ℂ)*
        (χM (n : ZMod qM)*typeIIPhase ν₀ n)
      let α₁ := fun n => (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM vM) n : ℂ)*
        (χM (n : ZMod qM)*typeIIPhase ν₁ n)
      let β := fun n => if n ∈ candidateRoughBand c L jStar then typeIIPhase σ n*χQ (n : ZMod qQ) else 0
      let γ := fun n => conj (candidateResidualPrimeCoefficient c L rQ jStar hrQ hj
        take hkeep (candidateAllocationFourierTwist c L rQ jStar take ξ) n)
      ∀ (probes : candidatePIndices c L → Finset (Fin J)) (r t : Finset (candidatePIndices c L))
        (hrt : Disjoint r t),
      (∀ g ∈ r ∪ t, g.val ∈ candidateBigPIndices c L) →
      ∀ (Q : ℕ), (Q : ℝ) ≤ L^R →
      ∀ U V : ℝ, Real.exp (bWindow*L) ≤ U → U ≤ Real.exp L →
        Real.exp (bWindow*L) ≤ V → V ≤ Real.exp L →
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L Kdet : ℤ)) (typeIIAdmissibleDeterminantBound L Kdet : ℤ),
      k ≠ 0 → (k.natAbs : ℝ) ≤ L^Kfull →
      ∀ j ∈ range (typeIISmoothDyadicCount L), ∀ a b : ℝ, |a| ≤ L^W →
      let Z := typeIISmoothDyadicScale U V (U*L^(-Kdet)) j
      ‖∑ ab : RepeatedBigPrimePatternPair (ell := ell) probes r t,
        ∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t (.inr ab)),
        (physicalAuxMass mass (repeatedBigPrimePatternCut probes r t (.inr ab)) aux : ℂ)*
          physicalFreePositiveHarmonicMain P mass probes r t hrt Q (L^(-B)) (L^(-C)) (.inr ab) aux
            a b Z k pool α₀ β γ α₁ β γ‖ ≤ L^(-D) := by
  obtain ⟨J₀,hbase⟩ := exists_actual_rough_original_harmonic_decay hZeta hc hb hKdet hγrough hvMax hρ
  refine ⟨J₀,?_⟩
  intro jStar hjStar D J ell B C R Kfull Tmod Sshift Cmod Sfreq W hell hB hKfull
  obtain ⟨A,_hA,hsum⟩ := exists_candidate_nonempty_pattern_sum_exponent hc J
  obtain ⟨S₀,hS₀,hdecay⟩ := hbase jStar hjStar (D+A) J ell B C R Kfull Tmod Sshift
    Cmod Sfreq W hell hB hKfull
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [hdecay S hS,hsum] with L hdec hsumL
  intro rQ hrQ hj take hkeep ξ lo hi aM vM ν₀ ν₁ qM _ χM hvM hqM hν₀ hν₁
    σ qQ _ χQ hqQ hσ P mass pool α₀ α₁ β γ probes r t hrt hbig Q hQ
    U V hUlo hUhi hVlo hVhi k hk hk0 hkfull j hjd a b ha Z
  apply hsumL (candidatePIndices c L) (subset_refl _) ell probes r t hrt D
  intro ab
  exact hdec rQ hrQ hj take hkeep ξ lo hi aM vM ν₀ ν₁ qM χM hvM hqM hν₀ hν₁
    σ qQ χQ hqQ hσ probes r t hrt hbig ab Q hQ
    U V hUlo hUhi hVlo hVhi k hk hk0 hkfull j hjd a b ha

end Bounty.WeakZeroFree


-- Source module: ActualRoughComparisonDecay

/- The full replacement error plus nonempty comparison term has arbitrary power saving. -/

open Finset Filter
open scoped Classical ComplexConjugate
namespace Bounty.WeakZeroFree

theorem exists_actual_rough_comparison_harmonic_decay
    (hZeta : PrimitiveZeroFreeRightOf (23 / 24)) {c bWindow Kdet γrough vMax ρ : ℝ}
    (hc : 0 < c) (hb : 0 < bWindow) (hKdet : 0 ≤ Kdet)
    (hγrough : 0 < γrough) (hvMax : vMax < 1) (hρ : 0 < ρ) :
    ∃ J₀ : ℕ, ∀ jStar : ℕ, J₀ < jStar →
      ∀ (D : ℝ) (J ell : ℕ) (B C R Kfull Tmod Sshift Cmod Sfreq W : ℝ),
      0 < ell → 0 ≤ B → 0 ≤ Kfull →
    ∃ S₀ : ℝ, 0 ≤ S₀ ∧ ∀ S : ℝ, S₀ ≤ S → ∀ᶠ L : ℝ in atTop,
      ∀ (rQ : ℕ) (hrQ : 0 < rQ) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*rQ) → Bool)
        (hkeep : take ((candidateAllocationOrder c L rQ).symm
          (candidateRoughSlot c L rQ jStar hrQ hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L rQ jStar) → ℝ)
        (lo hi : ℕ) (aM vM ν₀ ν₁ : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      vM ≤ vMax → (qM : ℝ) ≤ L^Cmod → |ν₀| ≤ L^Sfreq → |ν₁| ≤ L^Sfreq →
      ∀ (σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      let P := fun g : candidatePIndices c L => candidatePBand (c*L) g.val
      let mass := fun g => ∑ p ∈ P g, 1/(p : ℝ)
      let pool := (candidatePIndices c L).biUnion (candidatePBand (c*L))
      let α₀ := fun n => (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM vM) n : ℂ)*
        (χM (n : ZMod qM)*typeIIPhase ν₀ n)
      let α₁ := fun n => (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM vM) n : ℂ)*
        (χM (n : ZMod qM)*typeIIPhase ν₁ n)
      let β := fun n => if n ∈ candidateRoughBand c L jStar then typeIIPhase σ n*χQ (n : ZMod qQ) else 0
      let γ := fun n => conj (candidateResidualPrimeCoefficient c L rQ jStar hrQ hj
        take hkeep (candidateAllocationFourierTwist c L rQ jStar take ξ) n)
      ∀ (probes : candidatePIndices c L → Finset (Fin J)) (r t : Finset (candidatePIndices c L))
        (hrt : Disjoint r t),
      (∀ g ∈ r ∪ t, g.val ∈ candidateBigPIndices c L) →
      ∀ (Q : ℕ), (Q : ℝ) ≤ L^R →
      ∀ U V : ℝ, Real.exp (bWindow*L) ≤ U → U ≤ Real.exp L →
        Real.exp (bWindow*L) ≤ V → V ≤ Real.exp L →
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L Kdet : ℤ)) (typeIIAdmissibleDeterminantBound L Kdet : ℤ),
      k ≠ 0 → (k.natAbs : ℝ) ≤ L^Kfull →
      ∀ j ∈ range (typeIISmoothDyadicCount L), ∀ a b : ℝ, |a| ≤ L^W →
      let Z := typeIISmoothDyadicScale U V (U*L^(-Kdet)) j
      ‖(∑ i : RepeatedBigPrimePatternIndex (ell := ell) probes r t,
        ∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t i),
          (physicalAuxMass mass (repeatedBigPrimePatternCut probes r t i) aux : ℂ)*
            physicalPositiveHarmonicDifference P mass probes r t hrt Q (L^(-B)) (L^(-C)) i aux
              a b Z k pool α₀ β γ α₁ β γ) +
        (∑ ab : RepeatedBigPrimePatternPair (ell := ell) probes r t,
        ∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t (.inr ab)),
        (physicalAuxMass mass (repeatedBigPrimePatternCut probes r t (.inr ab)) aux : ℂ)*
          physicalFreePositiveHarmonicMain P mass probes r t hrt Q (L^(-B)) (L^(-C)) (.inr ab) aux
            a b Z k pool α₀ β γ α₁ β γ)‖ ≤ L^(-D) := by
  obtain ⟨J₀,hbase⟩ := exists_actual_rough_nonempty_harmonic_decay hZeta hc hb hKdet hγrough hvMax hρ
  refine ⟨J₀,?_⟩
  intro jStar hjStar D J ell B C R Kfull Tmod Sshift Cmod Sfreq W hell hB hKfull
  obtain ⟨S₀,hS₀,hdecay⟩ := hbase jStar hjStar (D+1) J ell B C R Kfull Tmod Sshift
    Cmod Sfreq W hell hB hKfull
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [hdecay S hS,
    eventually_candidate_pattern_harmonic_decay hc hb hKdet
      (le_max_right R 0) (le_max_right C 0) J ell 0 (D+1),
    eventually_actual_rough_source_factor_properties hc hγrough,
    eventually_actual_remaining_factor_properties hc,
    eventually_ge_atTop (2 : ℝ)] with L hdec herror hfactor hremain hL
  intro rQ hrQ hj take hkeep ξ lo hi aM vM ν₀ ν₁ qM _ χM hvM hqM hν₀ hν₁
    σ qQ _ χQ hqQ hσ P mass pool α₀ α₁ β γ probes r t hrt hbig Q hQ
    U V hUlo hUhi hVlo hVhi k hk hk0 hkfull j hjd a b ha Z
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hα₀ := hfactor S aM vM (Ioc lo hi) qM χM ν₀
  have hα₁ := hfactor S aM vM (Ioc lo hi) qM χM ν₁
  have hθ (n : ℕ) : ‖typeIIPhase σ n*χQ (n : ZMod qQ)‖ ≤ 1 := by
    rw [norm_mul,typeIIPhase_norm,one_mul]
    exact χQ.norm_le_one _
  have hβγ := hremain rQ jStar hrQ hj take hkeep ξ _ hθ
  have hQ' : (Q : ℝ) ≤ L^(max R 0) :=
    hQ.trans (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _))
  have hξ : L^(-(max C 0)) ≤ L^(-C) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (neg_le_neg (le_max_left _ _))
  have he := herror (candidatePIndices c L) (subset_refl _) probes r t hrt Q (L^(-B)) (L^(-C))
    hQ' hξ a b pool (fun g p hp => mem_biUnion.mpr ⟨g.val,g.property,hp⟩)
    α₀ β γ α₁ β γ
    (by simpa only [Real.rpow_zero] using hα₀.1)
    (by simpa only [Real.rpow_zero] using hβγ.1)
    (by simpa only [Real.rpow_zero] using hβγ.2.2)
    (by simpa only [Real.rpow_zero] using hα₁.1)
    (by simpa only [Real.rpow_zero] using hβγ.1)
    (by simpa only [Real.rpow_zero] using hβγ.2.2)
    U V hUlo hUhi hVlo hVhi k hk j hjd
  have hc' := hdec rQ hrQ hj take hkeep ξ lo hi aM vM ν₀ ν₁ qM χM hvM hqM hν₀ hν₁
    σ qQ χQ hqQ hσ probes r t hrt hbig Q hQ
    U V hUlo hUhi hVlo hVhi k hk hk0 hkfull j hjd a b ha
  calc
    _ ≤ L^(-(D+1)) + L^(-(D+1)) :=
      (norm_add_le _ _).trans (_root_.add_le_add he hc')
    _ = 2*L^(-(D+1)) := by ring
    _ ≤ L*L^(-(D+1)) := mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hL0.le _)
    _ = L^(-D) := by
      nth_rw 1 [← Real.rpow_one L]
      rw [← Real.rpow_add hL0]
      congr 1
      ring

end Bounty.WeakZeroFree


namespace Bounty.WeakZeroFree

theorem actual_prime_comparison_harmonic_decay
    {c bWindow Kdet : ℝ}
    (hc : 0 < c) (hb : 0 < bWindow) (hKdet : 0 ≤ Kdet) :
    ∃ J₀ : ℕ, ∀ jStar : ℕ, J₀ < jStar →
      ∀ (D : ℝ) (J ell : ℕ) (B C R Kfull Tmod Sshift Cmod Sfreq W : ℝ),
      0 < ell → 0 ≤ B → 0 ≤ Kfull →
    ∃ S₀ : ℝ, 0 ≤ S₀ ∧ ∀ S : ℝ, S₀ ≤ S → ∀ᶠ L : ℝ in atTop,
      ∀ (rQ : ℕ) (hrQ : 0 < rQ) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*rQ) → Bool)
        (hkeep : take ((candidateAllocationOrder c L rQ).symm
          (candidateRoughSlot c L rQ jStar hrQ hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L rQ jStar) → ℝ)
        (lo hi : ℕ) (κM ν₀ ν₁ : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      0 ≤ κM → κM ≤ 1/50 → (qM : ℝ) ≤ L^Cmod → |ν₀| ≤ L^Sfreq → |ν₁| ≤ L^Sfreq →
      ∀ (σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      let P := fun g : candidatePIndices c L => candidatePBand (c*L) g.val
      let mass := fun g => ∑ p ∈ P g, 1/(p : ℝ)
      let pool := (candidatePIndices c L).biUnion (candidatePBand (c*L))
      let α₀ := fun n => (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ)*
        (χM (n : ZMod qM)*typeIIPhase ν₀ n)
      let α₁ := fun n => (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ)*
        (χM (n : ZMod qM)*typeIIPhase ν₁ n)
      let β := fun n => if n ∈ candidateRoughBand c L jStar then typeIIPhase σ n*χQ (n : ZMod qQ) else 0
      let γ := fun n => conj (candidateResidualPrimeCoefficient c L rQ jStar hrQ hj
        take hkeep (candidateAllocationFourierTwist c L rQ jStar take ξ) n)
      ∀ (probes : candidatePIndices c L → Finset (Fin J)) (r t : Finset (candidatePIndices c L))
        (hrt : Disjoint r t),
      (∀ g ∈ r ∪ t, g.val ∈ candidateBigPIndices c L) →
      ∀ (Q : ℕ), (Q : ℝ) ≤ L^R →
      ∀ U V : ℝ, Real.exp (bWindow*L) ≤ U → U ≤ Real.exp L →
        Real.exp (bWindow*L) ≤ V → V ≤ Real.exp L →
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L Kdet : ℤ)) (typeIIAdmissibleDeterminantBound L Kdet : ℤ),
      k ≠ 0 → (k.natAbs : ℝ) ≤ L^Kfull →
      ∀ j ∈ range (typeIISmoothDyadicCount L), ∀ a b : ℝ, |a| ≤ L^W →
      let Z := typeIISmoothDyadicScale U V (U*L^(-Kdet)) j
      ‖(∑ i : RepeatedBigPrimePatternIndex (ell := ell) probes r t,
        ∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t i),
          (physicalAuxMass mass (repeatedBigPrimePatternCut probes r t i) aux : ℂ)*
            physicalPositiveHarmonicDifference P mass probes r t hrt Q (L^(-B)) (L^(-C)) i aux
              a b Z k pool α₀ β γ α₁ β γ) +
        (∑ ab : RepeatedBigPrimePatternPair (ell := ell) probes r t,
        ∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t (.inr ab)),
        (physicalAuxMass mass (repeatedBigPrimePatternCut probes r t (.inr ab)) aux : ℂ)*
          physicalFreePositiveHarmonicMain P mass probes r t hrt Q (L^(-B)) (L^(-C)) (.inr ab) aux
            a b Z k pool α₀ β γ α₁ β γ)‖ ≤ L^(-D) := by
  exact exists_actual_prime_comparison_harmonic_decay actual_zero_free hc hb hKdet

theorem actual_rough_comparison_harmonic_decay
    {c bWindow Kdet γrough vMax ρ : ℝ}
    (hc : 0 < c) (hb : 0 < bWindow) (hKdet : 0 ≤ Kdet)
    (hγrough : 0 < γrough) (hvMax : vMax < 1) (hρ : 0 < ρ) :
    ∃ J₀ : ℕ, ∀ jStar : ℕ, J₀ < jStar →
      ∀ (D : ℝ) (J ell : ℕ) (B C R Kfull Tmod Sshift Cmod Sfreq W : ℝ),
      0 < ell → 0 ≤ B → 0 ≤ Kfull →
    ∃ S₀ : ℝ, 0 ≤ S₀ ∧ ∀ S : ℝ, S₀ ≤ S → ∀ᶠ L : ℝ in atTop,
      ∀ (rQ : ℕ) (hrQ : 0 < rQ) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*rQ) → Bool)
        (hkeep : take ((candidateAllocationOrder c L rQ).symm
          (candidateRoughSlot c L rQ jStar hrQ hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L rQ jStar) → ℝ)
        (lo hi : ℕ) (aM vM ν₀ ν₁ : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      vM ≤ vMax → (qM : ℝ) ≤ L^Cmod → |ν₀| ≤ L^Sfreq → |ν₁| ≤ L^Sfreq →
      ∀ (σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      let P := fun g : candidatePIndices c L => candidatePBand (c*L) g.val
      let mass := fun g => ∑ p ∈ P g, 1/(p : ℝ)
      let pool := (candidatePIndices c L).biUnion (candidatePBand (c*L))
      let α₀ := fun n => (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM vM) n : ℂ)*
        (χM (n : ZMod qM)*typeIIPhase ν₀ n)
      let α₁ := fun n => (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM vM) n : ℂ)*
        (χM (n : ZMod qM)*typeIIPhase ν₁ n)
      let β := fun n => if n ∈ candidateRoughBand c L jStar then typeIIPhase σ n*χQ (n : ZMod qQ) else 0
      let γ := fun n => conj (candidateResidualPrimeCoefficient c L rQ jStar hrQ hj
        take hkeep (candidateAllocationFourierTwist c L rQ jStar take ξ) n)
      ∀ (probes : candidatePIndices c L → Finset (Fin J)) (r t : Finset (candidatePIndices c L))
        (hrt : Disjoint r t),
      (∀ g ∈ r ∪ t, g.val ∈ candidateBigPIndices c L) →
      ∀ (Q : ℕ), (Q : ℝ) ≤ L^R →
      ∀ U V : ℝ, Real.exp (bWindow*L) ≤ U → U ≤ Real.exp L →
        Real.exp (bWindow*L) ≤ V → V ≤ Real.exp L →
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L Kdet : ℤ)) (typeIIAdmissibleDeterminantBound L Kdet : ℤ),
      k ≠ 0 → (k.natAbs : ℝ) ≤ L^Kfull →
      ∀ j ∈ range (typeIISmoothDyadicCount L), ∀ a b : ℝ, |a| ≤ L^W →
      let Z := typeIISmoothDyadicScale U V (U*L^(-Kdet)) j
      ‖(∑ i : RepeatedBigPrimePatternIndex (ell := ell) probes r t,
        ∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t i),
          (physicalAuxMass mass (repeatedBigPrimePatternCut probes r t i) aux : ℂ)*
            physicalPositiveHarmonicDifference P mass probes r t hrt Q (L^(-B)) (L^(-C)) i aux
              a b Z k pool α₀ β γ α₁ β γ) +
        (∑ ab : RepeatedBigPrimePatternPair (ell := ell) probes r t,
        ∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t (.inr ab)),
        (physicalAuxMass mass (repeatedBigPrimePatternCut probes r t (.inr ab)) aux : ℂ)*
          physicalFreePositiveHarmonicMain P mass probes r t hrt Q (L^(-B)) (L^(-C)) (.inr ab) aux
            a b Z k pool α₀ β γ α₁ β γ)‖ ≤ L^(-D) := by
  exact exists_actual_rough_comparison_harmonic_decay actual_zero_free hc hb hKdet hγrough hvMax hρ

end Bounty.WeakZeroFree
