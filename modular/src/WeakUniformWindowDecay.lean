import WeakActualComparisonDecay

/-! The actual zero-free theorem gives thresholds uniform in the later determinant window. -/

open scoped Topology BigOperators Classical

-- Source module: ActualPrimeUniformOriginalDecay

/- The distinguished-band threshold is uniform in the later determinant window. -/

open Finset Filter
open scoped Classical ComplexConjugate
namespace Bounty.WeakZeroFree

theorem exists_actual_prime_original_harmonic_decay_uniform_window
    (hZeta : PrimitiveZeroFreeRightOf (23 / 24)) {c bWindow : ℝ}
    (hc : 0 < c) (hb : 0 < bWindow) :
    ∃ J₀ : ℕ, ∀ jStar : ℕ, J₀ < jStar →
      ∀ Kdet : ℝ, 0 ≤ Kdet → ∀ (D : ℝ) (J ell : ℕ) (B C R Kfull Tmod Sshift Cmod Sfreq W : ℝ),
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
      ∀ (ab : RepeatedBigPrimePatternPair (ell := ell) probes r t) (Q : ℕ), (Q : ℝ) ≤ L^R →
      ∀ U V : ℝ, Real.exp (bWindow*L) ≤ U → U ≤ Real.exp L →
        Real.exp (bWindow*L) ≤ V → V ≤ Real.exp L →
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L Kdet : ℤ)) (typeIIAdmissibleDeterminantBound L Kdet : ℤ),
      k ≠ 0 → (k.natAbs : ℝ) ≤ L^Kfull →
      ∀ j ∈ range (typeIISmoothDyadicCount L), ∀ a b : ℝ, |a| ≤ L^W →
      let Z := typeIISmoothDyadicScale U V (U*L^(-Kdet)) j
      ‖∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t (.inr ab)),
        (physicalAuxMass mass (repeatedBigPrimePatternCut probes r t (.inr ab)) aux : ℂ)*
          physicalFreePositiveHarmonicMain P mass probes r t hrt Q (L^(-B)) (L^(-C)) (.inr ab) aux
            a b Z k pool α₀ β γ α₁ β γ‖ ≤ L^(-D) := by
  obtain ⟨J₀,hlocal⟩ := exists_actual_prime_cell_local_energy_decay hZeta hc (by linarith : 0 < bWindow/2)
  refine ⟨J₀,?_⟩
  intro jStar hjStar Kdet hKdet D J ell B C R Kfull Tmod Sshift Cmod Sfreq W hell hB hKfull
  obtain ⟨_q,_hq,S₀,hS₀,hloc⟩ := hlocal jStar hjStar ((D+1)+2*(B+C+2*R+2)+2)
    J ell 0 Kfull Tmod Sshift Cmod Sfreq (max W 2) hKfull
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  obtain ⟨v,_m,hv,_hm,hmarked⟩ := exists_candidate_marked_error_inputs hc (ell+J)
  filter_upwards [hloc S hS,
    eventually_physical_free_harmonic_inr_of_peeled_central hc hb hKdet (by norm_num : (0 : ℝ) < 1)
      J ell 0 D B C R hB,
    eventually_original_cell_central_transfer hc hb hKdet J,
    eventually_actual_prime_source_factor_properties hc S (hS₀.trans hS),
    eventually_actual_remaining_factor_properties hc,
    eventually_candidate_small_group_outside_big hc, hmarked,
    eventually_candidate_subset_product_range hc (by norm_num : (0 : ℝ) < 1) J,
    eventually_ge_atTop (8 : ℝ)] with L hcell hmain htransfer hfactor hremain hsmall hmark hrange hL
  intro rQ hrQ hj take hkeep ξ lo hi κM ν₀ ν₁ qM _ χM hκM hκmax hqM hν₀ hν₁
    σ qQ _ χQ hqQ hσ P mass pool α₀ α₁ β γ probes r t hrt hbig ab Q hQ
    U V hUlo hUhi hVlo hVhi k hk hk0 hkfull j hjd a b ha Z
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hα₀ := hfactor κM hκM hκmax (Ioc lo hi) qM χM ν₀
  have hα₁ := hfactor κM hκM hκmax (Ioc lo hi) qM χM ν₁
  have hθ (n : ℕ) : ‖typeIIPhase σ n*χQ (n : ZMod qQ)‖ ≤ 1 := by
    rw [norm_mul,typeIIPhase_norm,one_mul]
    exact χQ.norm_le_one _
  have hβγ := hremain rQ jStar hrQ hj take hkeep ξ _ hθ
  have hmass : ∀ g, 0 < mass g := fun g => hv.trans_le ((hmark _ (subset_refl _)).2 g)
  obtain ⟨g,hgsmall,hg⟩ := hsmall (r ∪ t) hbig
  have hAsub := ((clean_mem_nonempty_subsets _ _).mp ab.1.property).2
  have hAne := Finset.nonempty_iff_ne_empty.mpr (((clean_mem_nonempty_subsets _ _).mp ab.1.property).1)
  have hBsub := ((clean_mem_nonempty_subsets _ _).mp ab.2.property).2
  have hBne := Finset.nonempty_iff_ne_empty.mpr (((clean_mem_nonempty_subsets _ _).mp ab.2.property).1)
  have hκ := actual_pattern_peel_mark probes r t ab.1.val ab.2.val hAsub hBsub g hg hell
  have hlog (s : Finset (candidatePIndices c L))
      (A : Finset (RepeatedBigFlatIndex (candidatePIndices c L) J ell))
      (hA : A ⊆ s.sigma (repeatedBigPrimeProbeSlots probes)) (hne : A.Nonempty)
      (x : ∀ i : A, P i.val.1) :
      0 ≤ Real.log (∏ i, (x i).val : ℕ) ∧ Real.log (∏ i, (x i).val : ℕ) ≤ L := by
    obtain ⟨hlo,hhi⟩ := hrange _ (subset_refl _) ell probes s A hA hne x
    have hp : (1 : ℝ) ≤ (∏ i, (x i).val : ℕ) :=
      (Real.one_le_exp (Real.rpow_nonneg hL0.le _)).trans hlo
    exact ⟨Real.log_nonneg hp,(Real.log_le_iff_le_exp (zero_lt_one.trans_le hp)).mpr
      (by simpa only [one_mul] using hhi)⟩
  apply hmain probes r t hrt ab g (ell-1) hκ hg hmass Q hQ
    (hlog r ab.1.val hAsub hAne) (hlog t ab.2.val hBsub hBne)
    pool (fun g p hp => mem_biUnion.mpr ⟨g.val,g.property,hp⟩)
    α₀ β γ α₁ β γ hα₀.2 hβγ.2.1 hα₁.2 hβγ.2.1
    (by simpa only [Real.rpow_zero] using hα₀.1)
    (by simpa only [Real.rpow_zero] using hβγ.1)
    (by simpa only [Real.rpow_zero] using hβγ.2.2)
    (by simpa only [Real.rpow_zero] using hα₁.1)
    (by simpa only [Real.rpow_zero] using hβγ.1)
    (by simpa only [Real.rpow_zero] using hβγ.2.2)
    U V hUlo hUhi hVlo hVhi k hk j hjd a b
  intro d _ χ e _ ψ v hv
  let hvPair := repeated_big_prime_pattern_pair_valid probes r t hrt ab
  have hA : ∀ i ∈ ab.1.val, i.1 ∈ r ∪ t := fun _ hi =>
    mem_union_left t (mem_sigma.mp (hAsub hi)).1
  have hB' : ∀ i ∈ ab.2.val, i.1 ∈ r ∪ t := fun _ hi =>
    mem_union_right r (mem_sigma.mp (hBsub hi)).1
  let b₀ := fun u => star (primeProductCellCharacter (fun i : ab.2.val => P i.val.1) (L^(-B)) e ψ
    (physicalSelectedPrimeRestriction ab.1.val ab.2.val ab.2.val subset_union_right (r ∪ t) hB' u))
  let b₁ := fun u => primeProductCellCharacter (fun i : ab.1.val => P i.val.1) (L^(-B)) d χ
    (physicalSelectedPrimeRestriction ab.1.val ab.2.val ab.1.val subset_union_left (r ∪ t) hA u)
  have hb₀ : ∀ u, ‖b₀ u‖ ≤ L^(0 : ℝ) := by
    intro u
    dsimp only [b₀]
    rw [norm_star,Real.rpow_zero]
    exact prime_product_cell_character_norm _ _ _ _ _
  have hb₁ : ∀ u, ‖b₁ u‖ ≤ L^(0 : ℝ) := by
    intro u
    rw [Real.rpow_zero]
    exact prime_product_cell_character_norm _ _ _ _ _
  have hh : 0 < L^(-B) := Real.rpow_pos_of_pos hL0 _
  have hh1 : L^(-B) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  apply htransfer (candidatePIndices c L) (subset_refl _) ell ab.1.val ab.2.val
    (repeated_big_active_pair_avoids_tail hvPair.1 hvPair.2.1) hvPair.2.2
    U V hUlo hUhi hVlo hVhi k hk j hjd Q (L^(-B)) hh hh1 d e χ ψ a b v _ _ _
  intro hZ hYlog hproduct
  have hav : |a| ≤ L^(max W 2) := ha.trans (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _))
  have hvL : |v| ≤ L := by simpa only [Real.norm_eq_abs,Real.rpow_one] using hv
  have hvv : |2*Real.pi*v| ≤ L^(max W 2) := by
    calc
      _ = |2*Real.pi| * |v| := abs_mul _ _
      _ ≤ 8*L := mul_le_mul (by rw [abs_of_pos (by positivity)]; linarith [Real.pi_lt_four])
        hvL (abs_nonneg _) (by norm_num)
      _ ≤ L^(2 : ℝ) := by norm_num; nlinarith
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1 (le_max_right _ _)
  have hAbig := actual_pattern_group_witness probes r ab.1.val hAsub hAne
    (fun g : candidatePIndices c L => g.val ∈ candidateBigPIndices c L)
    (fun g hg => hbig g (mem_union_left t hg))
  simpa only [physicalPrimeCellAuxCoeff,harmonicCellProductScale,Z,b₀,b₁,α₀,α₁,β,γ,pool,starRingEnd_apply,mul_assoc] using
    hcell rQ hrQ hj take hkeep ξ (repeatedBigAuxCut ab.1.val ab.2.val) (r ∪ t) g (ell-1) hκ hg hgsmall
      b₀ b₁ hb₀ hb₁
      lo hi κM ν₀ ν₁ qM χM hκM hκmax hqM hν₀ hν₁ σ qQ χQ hqQ hσ
      (candidatePIndices c L) (subset_refl _) probes r t ab.1.val ab.2.val hAsub hAne hBsub hBne hAbig
      (repeated_big_active_pair_avoids_tail hvPair.1 hvPair.2.1) hvPair.2.2 k hk0 hkfull
      Q (L^(-B)) hh hh1 d e χ ψ a b v Z hZ hav hvv hYlog hproduct

end Bounty.WeakZeroFree


-- Source module: ActualRoughUniformOriginalDecay

/- The distinguished-band threshold is uniform in the later determinant window. -/

open Finset Filter
open scoped Classical ComplexConjugate
namespace Bounty.WeakZeroFree

theorem exists_actual_rough_original_harmonic_decay_uniform_window
    (hZeta : PrimitiveZeroFreeRightOf (23 / 24)) {c bWindow γrough vMax ρ : ℝ}
    (hc : 0 < c) (hb : 0 < bWindow)
    (hγrough : 0 < γrough) (hvMax : vMax < 1) (hρ : 0 < ρ) :
    ∃ J₀ : ℕ, ∀ jStar : ℕ, J₀ < jStar →
      ∀ Kdet : ℝ, 0 ≤ Kdet → ∀ (D : ℝ) (J ell : ℕ) (B C R Kfull Tmod Sshift Cmod Sfreq W : ℝ),
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
      ∀ (ab : RepeatedBigPrimePatternPair (ell := ell) probes r t) (Q : ℕ), (Q : ℝ) ≤ L^R →
      ∀ U V : ℝ, Real.exp (bWindow*L) ≤ U → U ≤ Real.exp L →
        Real.exp (bWindow*L) ≤ V → V ≤ Real.exp L →
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L Kdet : ℤ)) (typeIIAdmissibleDeterminantBound L Kdet : ℤ),
      k ≠ 0 → (k.natAbs : ℝ) ≤ L^Kfull →
      ∀ j ∈ range (typeIISmoothDyadicCount L), ∀ a b : ℝ, |a| ≤ L^W →
      let Z := typeIISmoothDyadicScale U V (U*L^(-Kdet)) j
      ‖∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t (.inr ab)),
        (physicalAuxMass mass (repeatedBigPrimePatternCut probes r t (.inr ab)) aux : ℂ)*
          physicalFreePositiveHarmonicMain P mass probes r t hrt Q (L^(-B)) (L^(-C)) (.inr ab) aux
            a b Z k pool α₀ β γ α₁ β γ‖ ≤ L^(-D) := by
  obtain ⟨J₀,hlocal⟩ := exists_actual_rough_cell_local_energy_decay hZeta hc (by linarith : 0 < bWindow/2) hγrough hvMax hρ
  refine ⟨J₀,?_⟩
  intro jStar hjStar Kdet hKdet D J ell B C R Kfull Tmod Sshift Cmod Sfreq W hell hB hKfull
  obtain ⟨_q,_hq,S₀,hS₀,hloc⟩ := hlocal jStar hjStar ((D+1)+2*(B+C+2*R+2)+2)
    J ell 0 Kfull Tmod Sshift Cmod Sfreq (max W 2) hKfull
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  obtain ⟨v,_m,hv,_hm,hmarked⟩ := exists_candidate_marked_error_inputs hc (ell+J)
  filter_upwards [hloc S hS,
    eventually_physical_free_harmonic_inr_of_peeled_central hc hb hKdet (by norm_num : (0 : ℝ) < 1)
      J ell 0 D B C R hB,
    eventually_original_cell_central_transfer hc hb hKdet J,
    eventually_actual_rough_source_factor_properties hc hγrough,
    eventually_actual_remaining_factor_properties hc,
    eventually_candidate_small_group_outside_big hc, hmarked,
    eventually_candidate_subset_product_range hc (by norm_num : (0 : ℝ) < 1) J,
    eventually_ge_atTop (8 : ℝ)] with L hcell hmain htransfer hfactor hremain hsmall hmark hrange hL
  intro rQ hrQ hj take hkeep ξ lo hi aM vM ν₀ ν₁ qM _ χM hvM hqM hν₀ hν₁
    σ qQ _ χQ hqQ hσ P mass pool α₀ α₁ β γ probes r t hrt hbig ab Q hQ
    U V hUlo hUhi hVlo hVhi k hk hk0 hkfull j hjd a b ha Z
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hα₀ := hfactor S aM vM (Ioc lo hi) qM χM ν₀
  have hα₁ := hfactor S aM vM (Ioc lo hi) qM χM ν₁
  have hθ (n : ℕ) : ‖typeIIPhase σ n*χQ (n : ZMod qQ)‖ ≤ 1 := by
    rw [norm_mul,typeIIPhase_norm,one_mul]
    exact χQ.norm_le_one _
  have hβγ := hremain rQ jStar hrQ hj take hkeep ξ _ hθ
  have hmass : ∀ g, 0 < mass g := fun g => hv.trans_le ((hmark _ (subset_refl _)).2 g)
  obtain ⟨g,hgsmall,hg⟩ := hsmall (r ∪ t) hbig
  have hAsub := ((clean_mem_nonempty_subsets _ _).mp ab.1.property).2
  have hAne := Finset.nonempty_iff_ne_empty.mpr (((clean_mem_nonempty_subsets _ _).mp ab.1.property).1)
  have hBsub := ((clean_mem_nonempty_subsets _ _).mp ab.2.property).2
  have hBne := Finset.nonempty_iff_ne_empty.mpr (((clean_mem_nonempty_subsets _ _).mp ab.2.property).1)
  have hκ := actual_pattern_peel_mark probes r t ab.1.val ab.2.val hAsub hBsub g hg hell
  have hlog (s : Finset (candidatePIndices c L))
      (A : Finset (RepeatedBigFlatIndex (candidatePIndices c L) J ell))
      (hA : A ⊆ s.sigma (repeatedBigPrimeProbeSlots probes)) (hne : A.Nonempty)
      (x : ∀ i : A, P i.val.1) :
      0 ≤ Real.log (∏ i, (x i).val : ℕ) ∧ Real.log (∏ i, (x i).val : ℕ) ≤ L := by
    obtain ⟨hlo,hhi⟩ := hrange _ (subset_refl _) ell probes s A hA hne x
    have hp : (1 : ℝ) ≤ (∏ i, (x i).val : ℕ) :=
      (Real.one_le_exp (Real.rpow_nonneg hL0.le _)).trans hlo
    exact ⟨Real.log_nonneg hp,(Real.log_le_iff_le_exp (zero_lt_one.trans_le hp)).mpr
      (by simpa only [one_mul] using hhi)⟩
  apply hmain probes r t hrt ab g (ell-1) hκ hg hmass Q hQ
    (hlog r ab.1.val hAsub hAne) (hlog t ab.2.val hBsub hBne)
    pool (fun g p hp => mem_biUnion.mpr ⟨g.val,g.property,hp⟩)
    α₀ β γ α₁ β γ hα₀.2 hβγ.2.1 hα₁.2 hβγ.2.1
    (by simpa only [Real.rpow_zero] using hα₀.1)
    (by simpa only [Real.rpow_zero] using hβγ.1)
    (by simpa only [Real.rpow_zero] using hβγ.2.2)
    (by simpa only [Real.rpow_zero] using hα₁.1)
    (by simpa only [Real.rpow_zero] using hβγ.1)
    (by simpa only [Real.rpow_zero] using hβγ.2.2)
    U V hUlo hUhi hVlo hVhi k hk j hjd a b
  intro d _ χ e _ ψ v hv
  let hvPair := repeated_big_prime_pattern_pair_valid probes r t hrt ab
  have hA : ∀ i ∈ ab.1.val, i.1 ∈ r ∪ t := fun _ hi =>
    mem_union_left t (mem_sigma.mp (hAsub hi)).1
  have hB' : ∀ i ∈ ab.2.val, i.1 ∈ r ∪ t := fun _ hi =>
    mem_union_right r (mem_sigma.mp (hBsub hi)).1
  let b₀ := fun u => star (primeProductCellCharacter (fun i : ab.2.val => P i.val.1) (L^(-B)) e ψ
    (physicalSelectedPrimeRestriction ab.1.val ab.2.val ab.2.val subset_union_right (r ∪ t) hB' u))
  let b₁ := fun u => primeProductCellCharacter (fun i : ab.1.val => P i.val.1) (L^(-B)) d χ
    (physicalSelectedPrimeRestriction ab.1.val ab.2.val ab.1.val subset_union_left (r ∪ t) hA u)
  have hb₀ : ∀ u, ‖b₀ u‖ ≤ L^(0 : ℝ) := by
    intro u
    dsimp only [b₀]
    rw [norm_star,Real.rpow_zero]
    exact prime_product_cell_character_norm _ _ _ _ _
  have hb₁ : ∀ u, ‖b₁ u‖ ≤ L^(0 : ℝ) := by
    intro u
    rw [Real.rpow_zero]
    exact prime_product_cell_character_norm _ _ _ _ _
  have hh : 0 < L^(-B) := Real.rpow_pos_of_pos hL0 _
  have hh1 : L^(-B) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  apply htransfer (candidatePIndices c L) (subset_refl _) ell ab.1.val ab.2.val
    (repeated_big_active_pair_avoids_tail hvPair.1 hvPair.2.1) hvPair.2.2
    U V hUlo hUhi hVlo hVhi k hk j hjd Q (L^(-B)) hh hh1 d e χ ψ a b v _ _ _
  intro hZ hYlog hproduct
  have hav : |a| ≤ L^(max W 2) := ha.trans (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _))
  have hvL : |v| ≤ L := by simpa only [Real.norm_eq_abs,Real.rpow_one] using hv
  have hvv : |2*Real.pi*v| ≤ L^(max W 2) := by
    calc
      _ = |2*Real.pi| * |v| := abs_mul _ _
      _ ≤ 8*L := mul_le_mul (by rw [abs_of_pos (by positivity)]; linarith [Real.pi_lt_four])
        hvL (abs_nonneg _) (by norm_num)
      _ ≤ L^(2 : ℝ) := by norm_num; nlinarith
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1 (le_max_right _ _)
  have hAbig := actual_pattern_group_witness probes r ab.1.val hAsub hAne
    (fun g : candidatePIndices c L => g.val ∈ candidateBigPIndices c L)
    (fun g hg => hbig g (mem_union_left t hg))
  simpa only [physicalPrimeCellAuxCoeff,harmonicCellProductScale,Z,b₀,b₁,α₀,α₁,β,γ,pool,starRingEnd_apply,mul_assoc] using
    hcell rQ hrQ hj take hkeep ξ (repeatedBigAuxCut ab.1.val ab.2.val) (r ∪ t) g (ell-1) hκ hg hgsmall
      b₀ b₁ hb₀ hb₁
      lo hi aM vM ν₀ ν₁ qM χM hvM hqM hν₀ hν₁ σ qQ χQ hqQ hσ
      (candidatePIndices c L) (subset_refl _) probes r t ab.1.val ab.2.val hAsub hAne hBsub hBne hAbig
      (repeated_big_active_pair_avoids_tail hvPair.1 hvPair.2.1) hvPair.2.2 k hk0 hkfull
      Q (L^(-B)) hh hh1 d e χ ψ a b v Z hZ hav hvv hYlog hproduct

end Bounty.WeakZeroFree


-- Source module: ActualPrimeUniformComparisonDecay

/- Complete comparison decay with the distinguished-band threshold before the window and precision. -/

open Finset Filter
open scoped Classical ComplexConjugate
namespace Bounty.WeakZeroFree

theorem exists_actual_prime_comparison_harmonic_decay_uniform_window
    (hZeta : PrimitiveZeroFreeRightOf (23 / 24)) {c bWindow : ℝ}
    (hc : 0 < c) (hb : 0 < bWindow) :
    ∃ J₀ : ℕ, ∀ jStar : ℕ, J₀ < jStar →
      ∀ Kdet : ℝ, 0 ≤ Kdet → ∀ (D : ℝ) (J ell : ℕ) (B C R Kfull Tmod Sshift Cmod Sfreq W : ℝ),
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
  obtain ⟨J₀,hbase⟩ := exists_actual_prime_original_harmonic_decay_uniform_window hZeta hc hb
  refine ⟨J₀,?_⟩
  intro jStar hjStar Kdet hKdet D J ell B C R Kfull Tmod Sshift Cmod Sfreq W hell hB hKfull
  obtain ⟨A,_hA,hsum⟩ := exists_candidate_nonempty_pattern_sum_exponent hc J
  obtain ⟨S₀,hS₀,hdecay⟩ := hbase jStar hjStar Kdet hKdet (D+1+A) J ell B C R Kfull Tmod Sshift
    Cmod Sfreq W hell hB hKfull
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [hdecay S hS,hsum,
    eventually_candidate_pattern_harmonic_decay hc hb hKdet
      (le_max_right R 0) (le_max_right C 0) J ell 0 (D+1),
    eventually_actual_prime_source_factor_properties hc S (hS₀.trans hS),
    eventually_actual_remaining_factor_properties hc,
    eventually_ge_atTop (2 : ℝ)] with L hdec hsumL herror hfactor hremain hL
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
  have hc' := hsumL (candidatePIndices c L) (subset_refl _) ell probes r t hrt (D+1)
    (fun ab => ∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t (.inr ab)),
      (physicalAuxMass mass (repeatedBigPrimePatternCut probes r t (.inr ab)) aux : ℂ)*
        physicalFreePositiveHarmonicMain P mass probes r t hrt Q (L^(-B)) (L^(-C)) (.inr ab) aux
          a b Z k pool α₀ β γ α₁ β γ)
    (fun ab => hdec rQ hrQ hj take hkeep ξ lo hi κM ν₀ ν₁ qM χM hκM hκmax hqM hν₀ hν₁
      σ qQ χQ hqQ hσ probes r t hrt hbig ab Q hQ
      U V hUlo hUhi hVlo hVhi k hk hk0 hkfull j hjd a b ha)
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


-- Source module: ActualRoughUniformComparisonDecay

/- Complete comparison decay with the distinguished-band threshold before the window and precision. -/

open Finset Filter
open scoped Classical ComplexConjugate
namespace Bounty.WeakZeroFree

theorem exists_actual_rough_comparison_harmonic_decay_uniform_window
    (hZeta : PrimitiveZeroFreeRightOf (23 / 24)) {c bWindow γrough vMax ρ : ℝ}
    (hc : 0 < c) (hb : 0 < bWindow)
    (hγrough : 0 < γrough) (hvMax : vMax < 1) (hρ : 0 < ρ) :
    ∃ J₀ : ℕ, ∀ jStar : ℕ, J₀ < jStar →
      ∀ Kdet : ℝ, 0 ≤ Kdet → ∀ (D : ℝ) (J ell : ℕ) (B C R Kfull Tmod Sshift Cmod Sfreq W : ℝ),
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
  obtain ⟨J₀,hbase⟩ := exists_actual_rough_original_harmonic_decay_uniform_window hZeta hc hb hγrough hvMax hρ
  refine ⟨J₀,?_⟩
  intro jStar hjStar Kdet hKdet D J ell B C R Kfull Tmod Sshift Cmod Sfreq W hell hB hKfull
  obtain ⟨A,_hA,hsum⟩ := exists_candidate_nonempty_pattern_sum_exponent hc J
  obtain ⟨S₀,hS₀,hdecay⟩ := hbase jStar hjStar Kdet hKdet (D+1+A) J ell B C R Kfull Tmod Sshift
    Cmod Sfreq W hell hB hKfull
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [hdecay S hS,hsum,
    eventually_candidate_pattern_harmonic_decay hc hb hKdet
      (le_max_right R 0) (le_max_right C 0) J ell 0 (D+1),
    eventually_actual_rough_source_factor_properties hc hγrough,
    eventually_actual_remaining_factor_properties hc,
    eventually_ge_atTop (2 : ℝ)] with L hdec hsumL herror hfactor hremain hL
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
  have hc' := hsumL (candidatePIndices c L) (subset_refl _) ell probes r t hrt (D+1)
    (fun ab => ∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t (.inr ab)),
      (physicalAuxMass mass (repeatedBigPrimePatternCut probes r t (.inr ab)) aux : ℂ)*
        physicalFreePositiveHarmonicMain P mass probes r t hrt Q (L^(-B)) (L^(-C)) (.inr ab) aux
          a b Z k pool α₀ β γ α₁ β γ)
    (fun ab => hdec rQ hrQ hj take hkeep ξ lo hi aM vM ν₀ ν₁ qM χM hvM hqM hν₀ hν₁
      σ qQ χQ hqQ hσ probes r t hrt hbig ab Q hQ
      U V hUlo hUhi hVlo hVhi k hk hk0 hkfull j hjd a b ha)
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

theorem actual_prime_original_harmonic_decay_uniform_window
    {c bWindow : ℝ}
    (hc : 0 < c) (hb : 0 < bWindow) :
    ∃ J₀ : ℕ, ∀ jStar : ℕ, J₀ < jStar →
      ∀ Kdet : ℝ, 0 ≤ Kdet → ∀ (D : ℝ) (J ell : ℕ) (B C R Kfull Tmod Sshift Cmod Sfreq W : ℝ),
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
      ∀ (ab : RepeatedBigPrimePatternPair (ell := ell) probes r t) (Q : ℕ), (Q : ℝ) ≤ L^R →
      ∀ U V : ℝ, Real.exp (bWindow*L) ≤ U → U ≤ Real.exp L →
        Real.exp (bWindow*L) ≤ V → V ≤ Real.exp L →
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L Kdet : ℤ)) (typeIIAdmissibleDeterminantBound L Kdet : ℤ),
      k ≠ 0 → (k.natAbs : ℝ) ≤ L^Kfull →
      ∀ j ∈ range (typeIISmoothDyadicCount L), ∀ a b : ℝ, |a| ≤ L^W →
      let Z := typeIISmoothDyadicScale U V (U*L^(-Kdet)) j
      ‖∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t (.inr ab)),
        (physicalAuxMass mass (repeatedBigPrimePatternCut probes r t (.inr ab)) aux : ℂ)*
          physicalFreePositiveHarmonicMain P mass probes r t hrt Q (L^(-B)) (L^(-C)) (.inr ab) aux
            a b Z k pool α₀ β γ α₁ β γ‖ ≤ L^(-D) := by
  exact exists_actual_prime_original_harmonic_decay_uniform_window actual_zero_free hc hb

theorem actual_rough_original_harmonic_decay_uniform_window
    {c bWindow γrough vMax ρ : ℝ}
    (hc : 0 < c) (hb : 0 < bWindow)
    (hγrough : 0 < γrough) (hvMax : vMax < 1) (hρ : 0 < ρ) :
    ∃ J₀ : ℕ, ∀ jStar : ℕ, J₀ < jStar →
      ∀ Kdet : ℝ, 0 ≤ Kdet → ∀ (D : ℝ) (J ell : ℕ) (B C R Kfull Tmod Sshift Cmod Sfreq W : ℝ),
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
      ∀ (ab : RepeatedBigPrimePatternPair (ell := ell) probes r t) (Q : ℕ), (Q : ℝ) ≤ L^R →
      ∀ U V : ℝ, Real.exp (bWindow*L) ≤ U → U ≤ Real.exp L →
        Real.exp (bWindow*L) ≤ V → V ≤ Real.exp L →
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L Kdet : ℤ)) (typeIIAdmissibleDeterminantBound L Kdet : ℤ),
      k ≠ 0 → (k.natAbs : ℝ) ≤ L^Kfull →
      ∀ j ∈ range (typeIISmoothDyadicCount L), ∀ a b : ℝ, |a| ≤ L^W →
      let Z := typeIISmoothDyadicScale U V (U*L^(-Kdet)) j
      ‖∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t (.inr ab)),
        (physicalAuxMass mass (repeatedBigPrimePatternCut probes r t (.inr ab)) aux : ℂ)*
          physicalFreePositiveHarmonicMain P mass probes r t hrt Q (L^(-B)) (L^(-C)) (.inr ab) aux
            a b Z k pool α₀ β γ α₁ β γ‖ ≤ L^(-D) := by
  exact exists_actual_rough_original_harmonic_decay_uniform_window actual_zero_free hc hb hγrough hvMax hρ

theorem actual_prime_comparison_harmonic_decay_uniform_window
    {c bWindow : ℝ}
    (hc : 0 < c) (hb : 0 < bWindow) :
    ∃ J₀ : ℕ, ∀ jStar : ℕ, J₀ < jStar →
      ∀ Kdet : ℝ, 0 ≤ Kdet → ∀ (D : ℝ) (J ell : ℕ) (B C R Kfull Tmod Sshift Cmod Sfreq W : ℝ),
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
  exact exists_actual_prime_comparison_harmonic_decay_uniform_window actual_zero_free hc hb

theorem actual_rough_comparison_harmonic_decay_uniform_window
    {c bWindow γrough vMax ρ : ℝ}
    (hc : 0 < c) (hb : 0 < bWindow)
    (hγrough : 0 < γrough) (hvMax : vMax < 1) (hρ : 0 < ρ) :
    ∃ J₀ : ℕ, ∀ jStar : ℕ, J₀ < jStar →
      ∀ Kdet : ℝ, 0 ≤ Kdet → ∀ (D : ℝ) (J ell : ℕ) (B C R Kfull Tmod Sshift Cmod Sfreq W : ℝ),
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
  exact exists_actual_rough_comparison_harmonic_decay_uniform_window actual_zero_free hc hb hγrough hvMax hρ

end Bounty.WeakZeroFree
