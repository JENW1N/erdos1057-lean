import WeakActualLocalEnergy

/-! Original harmonic decay with the actual weaker zero-free input. -/

open scoped Topology BigOperators Classical

-- Source module: PrimeAuxCellCoefficient

/- The exact auxiliary cell coefficients have total absolute mass at most one and preserve the occupied cell scale. -/

open Finset
open scoped Classical
namespace Bounty

noncomputable def physicalPrimeCellAuxCoeff
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ)
    (A B : Finset (RepeatedBigFlatIndex G J ell))
    (hU : ∀ g (j : Fin ell), (⟨g, Sum.inr j⟩ : RepeatedBigFlatIndex G J ell) ∉ A ∪ B)
    (hAB : Disjoint A B) (h : ℝ) (d : ℤ) {Q : ℕ} (χ : BoundedPrimitiveCharacter Q)
    (e : ℤ) (ψ : BoundedPrimitiveCharacter Q)
    (aux : PhysicalAuxLabels P (repeatedBigAuxCut A B)) : ℂ :=
  (physicalAuxMass V (repeatedBigAuxCut A B) aux : ℂ) *
    star (primeProductCellCharacter (fun i : A => P i.val.1) h d χ
      (repeatedBigAuxSplitEquiv P A B hU hAB aux).1) *
    star (primeProductCellCharacter (fun i : B => P i.val.1) h e ψ
      (repeatedBigAuxSplitEquiv P A B hU hAB aux).2)

theorem physical_prime_cell_aux_mass
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ)
    (A B : Finset (RepeatedBigFlatIndex G J ell))
    (hU : ∀ g (j : Fin ell), (⟨g, Sum.inr j⟩ : RepeatedBigFlatIndex G J ell) ∉ A ∪ B)
    (hAB : Disjoint A B) (h : ℝ) (d : ℤ) {Q : ℕ} (χ : BoundedPrimitiveCharacter Q)
    (e : ℤ) (ψ : BoundedPrimitiveCharacter Q)
    (hV : ∀ g, 0 < V g) (hMass : ∀ g, ∑ p ∈ P g, 1/(p : ℝ) = V g) :
    (∑ aux, ‖physicalPrimeCellAuxCoeff P V A B hU hAB h d χ e ψ aux‖) ≤ 1 := by
  calc
    _ ≤ ∑ aux, physicalAuxMass V (repeatedBigAuxCut A B) aux := by
      apply sum_le_sum
      intro aux _
      have hm := physical_aux_mass_nonneg V (repeatedBigAuxCut A B) (fun g => (hV g).le) aux
      have ha := prime_product_cell_character_norm (fun i : A => P i.val.1) h d χ
        (repeatedBigAuxSplitEquiv P A B hU hAB aux).1
      have hb := prime_product_cell_character_norm (fun i : B => P i.val.1) h e ψ
        (repeatedBigAuxSplitEquiv P A B hU hAB aux).2
      simp only [physicalPrimeCellAuxCoeff, norm_mul, norm_star, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hm]
      exact (mul_le_mul (mul_le_mul_of_nonneg_left ha hm) hb (norm_nonneg _)
        (mul_nonneg hm zero_le_one)).trans_eq (by ring)
    _ = 1 := physical_aux_mass_sum V (repeatedBigAuxCut A B) hV hMass

theorem physical_prime_cell_aux_scale
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ)
    (A B : Finset (RepeatedBigFlatIndex G J ell))
    (hU : ∀ g (j : Fin ell), (⟨g, Sum.inr j⟩ : RepeatedBigFlatIndex G J ell) ∉ A ∪ B)
    (hAB : Disjoint A B) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (d : ℤ) {Q : ℕ} (χ : BoundedPrimitiveCharacter Q) (e : ℤ) (ψ : BoundedPrimitiveCharacter Q)
    (hP : ∀ g, ∀ p ∈ P g, 0 < p)
    (aux : PhysicalAuxLabels P (repeatedBigAuxCut A B))
    (hc : physicalPrimeCellAuxCoeff P V A B hU hAB h d χ e ψ aux ≠ 0) :
    harmonicCellProductScale h d e ≤ (physicalFreeFactor (repeatedBigAuxCut A B) aux : ℝ) ∧
    (physicalFreeFactor (repeatedBigAuxCut A B) aux : ℝ) ≤
      Real.exp 2*harmonicCellProductScale h d e := by
  have hca : primeProductCellCharacter (fun i : A => P i.val.1) h d χ
      (repeatedBigAuxSplitEquiv P A B hU hAB aux).1 ≠ 0 := by
    intro hz
    exact hc (by simp only [physicalPrimeCellAuxCoeff, hz, star_zero, mul_zero, zero_mul])
  have hcb : primeProductCellCharacter (fun i : B => P i.val.1) h e ψ
      (repeatedBigAuxSplitEquiv P A B hU hAB aux).2 ≠ 0 := by
    intro hz
    exact hc (by simp only [physicalPrimeCellAuxCoeff, hz, star_zero, mul_zero])
  have hpA : 0 < ∏ i : A, ((repeatedBigAuxSplitEquiv P A B hU hAB aux).1 i).val :=
    prod_pos (fun i _ => hP i.val.1 _ ((repeatedBigAuxSplitEquiv P A B hU hAB aux).1 i).property)
  have hpB : 0 < ∏ i : B, ((repeatedBigAuxSplitEquiv P A B hU hAB aux).2 i).val :=
    prod_pos (fun i _ => hP i.val.1 _ ((repeatedBigAuxSplitEquiv P A B hU hAB aux).2 i).property)
  have heq : physicalFreeFactor (repeatedBigAuxCut A B) aux =
      (∏ i : A, ((repeatedBigAuxSplitEquiv P A B hU hAB aux).1 i).val) *
      (∏ i : B, ((repeatedBigAuxSplitEquiv P A B hU hAB aux).2 i).val) := by
    have he := repeatedBigAuxSplitEquiv_symm_label_prod P A B hU hAB
      (repeatedBigAuxSplitEquiv P A B hU hAB aux).1
      (repeatedBigAuxSplitEquiv P A B hU hAB aux).2
    simpa only [physicalFreeFactor, Prod.eta, Equiv.symm_apply_apply] using he
  rw [heq]
  have hs := harmonic_cell_product_bounds hh hh1 hpA hpB
    (prime_cell_character_mem _ h d χ _ hca) (prime_cell_character_mem _ h e ψ _ hcb)
  exact ⟨hs.1.le, hs.2⟩

end Bounty


-- Source module: PrimeAuxHarmonicFamily

/- The exact finite harmonic family attached to a retained pair of prime cells. -/

open Finset
open scoped Classical
namespace Bounty

noncomputable def physicalPrimeCellHarmonicFamily
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ)
    (A B : Finset (RepeatedBigFlatIndex G J ell))
    (hU : ∀ g (j : Fin ell), (⟨g, Sum.inr j⟩ : RepeatedBigFlatIndex G J ell) ∉ A ∪ B)
    (hAB : Disjoint A B) (h : ℝ) (d : ℤ) {Q : ℕ} (χ : BoundedPrimitiveCharacter Q)
    (e : ℤ) (ψ : BoundedPrimitiveCharacter Q) (a b Z : ℝ) (k : ℤ) (F G : ℤ → ℂ) : ℂ :=
  ∑ aux : PhysicalAuxLabels P (repeatedBigAuxCut A B),
    physicalPrimeCellAuxCoeff P V A B hU hAB h d χ e ψ aux *
      (physicalPhase (-(a+b)) (physicalFreeFactor (repeatedBigAuxCut A B) aux) *
        ∑ n ∈ harmonicPositiveSupport Z k (physicalFreeFactor (repeatedBigAuxCut A B) aux),
          ((typeIIHarmonicDyadic ((n : ℝ)/(Z*(physicalFreeFactor (repeatedBigAuxCut A B) aux : ℝ))) : ℂ)/(n : ℂ))*
            physicalPhase a n.natAbs*
            physicalPhase b (n+k*(physicalFreeFactor (repeatedBigAuxCut A B) aux : ℤ)).natAbs*
            star (F n)*G (n+k*(physicalFreeFactor (repeatedBigAuxCut A B) aux : ℤ)))


end Bounty


-- Source module: PrimeAuxFamilyPerturbation

/- A uniform finite harmonic replacement error survives the exact auxiliary probability average. -/

open Finset
open scoped Classical
namespace Bounty

theorem physical_prime_cell_family_perturbation
    {Gt : Type*} [Fintype Gt] [DecidableEq Gt] {J ell : ℕ}
    (P : Gt → Finset ℕ) (V : Gt → ℝ)
    (A B : Finset (RepeatedBigFlatIndex Gt J ell))
    (hU : ∀ g (j : Fin ell), (⟨g, Sum.inr j⟩ : RepeatedBigFlatIndex Gt J ell) ∉ A ∪ B)
    (hAB : Disjoint A B) (h : ℝ) (d : ℤ) {Q : ℕ} (χ : BoundedPrimitiveCharacter Q)
    (e : ℤ) (ψ : BoundedPrimitiveCharacter Q) (a b Z : ℝ) (k : ℤ) (F G F' G' : ℤ → ℂ)
    (hV : ∀ g, 0 < V g) (hMass : ∀ g, ∑ p ∈ P g, 1/(p : ℝ) = V g)
    {ε : ℝ} (hε : 0 ≤ ε)
    (herr : ∀ aux : PhysicalAuxLabels P (repeatedBigAuxCut A B),
      let m := physicalFreeFactor (P := P) (repeatedBigAuxCut A B) aux
      ‖(∑ n ∈ harmonicPositiveSupport Z k m,
          (physicalPhasedHarmonicCutoff a b Z k m n/(n : ℂ))*star (F n)*G (n+k*(m : ℤ))) -
        (∑ n ∈ harmonicPositiveSupport Z k m,
          (physicalPhasedHarmonicCutoff a b Z k m n/(n : ℂ))*star (F' n)*G' (n+k*(m : ℤ)))‖ ≤ ε) :
    ‖physicalPrimeCellHarmonicFamily P V A B hU hAB h d χ e ψ a b Z k F G -
      physicalPrimeCellHarmonicFamily P V A B hU hAB h d χ e ψ a b Z k F' G'‖ ≤ ε := by
  let c := physicalPrimeCellAuxCoeff P V A B hU hAB h d χ e ψ
  let m := physicalFreeFactor (P := P) (repeatedBigAuxCut A B)
  have hsum (F G : ℤ → ℂ) : physicalPrimeCellHarmonicFamily P V A B hU hAB h d χ e ψ a b Z k F G =
      ∑ aux, c aux*physicalPhase (-(a+b)) (m aux) *
        ∑ n ∈ harmonicPositiveSupport Z k (m aux),
          (physicalPhasedHarmonicCutoff a b Z k (m aux) n/(n : ℂ))*star (F n)*G (n+k*(m aux : ℤ)) := by
    unfold physicalPrimeCellHarmonicFamily
    apply sum_congr rfl
    intro aux _
    dsimp only [c, m]
    simp only [mul_assoc]
    congr 1
    congr 1
    apply sum_congr rfl
    intro n _
    dsimp only [physicalPhasedHarmonicCutoff, m]
    ring
  rw [hsum F G, hsum F' G', ← sum_sub_distrib]
  calc
    _ ≤ ∑ aux, ‖c aux*physicalPhase (-(a+b)) (m aux) *
        (∑ n ∈ harmonicPositiveSupport Z k (m aux),
          (physicalPhasedHarmonicCutoff a b Z k (m aux) n/(n : ℂ))*star (F n)*G (n+k*(m aux : ℤ))) -
      c aux*physicalPhase (-(a+b)) (m aux) *
        (∑ n ∈ harmonicPositiveSupport Z k (m aux),
          (physicalPhasedHarmonicCutoff a b Z k (m aux) n/(n : ℂ))*star (F' n)*G' (n+k*(m aux : ℤ)))‖ := norm_sum_le _ _
    _ ≤ ∑ aux, ‖c aux‖*ε := by
      apply sum_le_sum
      intro aux _
      rw [← mul_sub, norm_mul, norm_mul, physical_phase_norm, mul_one]
      exact mul_le_mul_of_nonneg_left (herr aux) (norm_nonneg _)
    _ = (∑ aux, ‖c aux‖)*ε := (sum_mul ..).symm
    _ ≤ 1*ε := mul_le_mul_of_nonneg_right
      (physical_prime_cell_aux_mass P V A B hU hAB h d χ e ψ hV hMass) hε
    _ = ε := one_mul _

end Bounty


-- Source module: CandidateAuxCellPeel

/- The marked-to-peeled approximation is uniform before the exact auxiliary cell average, on all original candidate groups. -/

open Finset Filter
open scoped Classical
namespace Bounty

theorem eventually_candidate_aux_cell_peel {c bWindow Kdet : ℝ}
    (hc : 0 < c) (hb : 0 < bWindow) (hK : 0 ≤ Kdet) (J ell : ℕ) (Ce D : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      let P := fun g : candidatePIndices c L => candidatePBand (c*L) g.val
      let mass := fun g => ∑ p ∈ P g, 1/(p : ℝ)
      ∀ (A B : Finset (RepeatedBigFlatIndex (candidatePIndices c L) J ell))
        (hU : ∀ g (j : Fin ell),
          (⟨g, Sum.inr j⟩ : RepeatedBigFlatIndex (candidatePIndices c L) J ell) ∉ A ∪ B)
        (hAB : Disjoint A B) (Q : ℕ) (h : ℝ) (d : ℤ) (χ : BoundedPrimitiveCharacter Q)
        (e : ℤ) (ψ : BoundedPrimitiveCharacter Q),
      let cut := repeatedBigAuxCut A B
      let marks := fun g => ell+(cut g).card
      ∀ (big : Finset (candidatePIndices c L)) (g : candidatePIndices c L) (κ : ℕ),
      marks g = κ+1 → g ∉ big → (∀ j, 0 < mass j) →
      ∀ (b₀ b₁ : GroupMarkedLists (fun j : big => P j.val) (fun j : big => marks j.val) → ℂ),
      (∀ u, ‖b₀ u‖ ≤ 1) → (∀ u, ‖b₁ u‖ ≤ 1) →
      ∀ (pool : Finset ℕ), (∀ j, P j ⊆ pool) →
      ∀ (α₀ β₀ γ₀ α₁ β₁ γ₁ : ℕ → ℂ),
      (∀ n, ¬ Disjoint n.primeFactors pool → α₀ n = 0) →
      (∀ n, ¬ Disjoint n.primeFactors pool → β₀ n = 0) →
      (∀ n, ¬ Disjoint n.primeFactors pool → α₁ n = 0) →
      (∀ n, ¬ Disjoint n.primeFactors pool → β₁ n = 0) →
      (∀ n, ‖α₀ n‖ ≤ L^Ce) → (∀ n, ‖β₀ n‖ ≤ L^Ce) → (∀ n, ‖γ₀ n‖ ≤ L^Ce) →
      (∀ n, ‖α₁ n‖ ≤ L^Ce) → (∀ n, ‖β₁ n‖ ≤ L^Ce) → (∀ n, ‖γ₁ n‖ ≤ L^Ce) →
      ∀ U V : ℝ, Real.exp (bWindow*L) ≤ U → U ≤ Real.exp L →
        Real.exp (bWindow*L) ≤ V → V ≤ Real.exp L →
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L Kdet : ℤ)) (typeIIAdmissibleDeterminantBound L Kdet : ℤ),
      ∀ j ∈ range (typeIISmoothDyadicCount L), ∀ a b : ℝ,
      let Z := typeIISmoothDyadicScale U V (U*L^(-Kdet)) j
      let F := fun n : ℤ => selectedMarkedEndpoint P (1/2) mass marks big b₀ pool α₀ β₀ γ₀ n.natAbs
      let G := fun n : ℤ => selectedMarkedEndpoint P (1/2) mass marks big b₁ pool α₁ β₁ γ₁ n.natAbs
      let F' := fun n : ℤ => selectedPeeledEndpoint P (1/2) mass marks g κ big b₀ pool α₀ β₀ γ₀ n.natAbs
      let G' := fun n : ℤ => selectedPeeledEndpoint P (1/2) mass marks g κ big b₁ pool α₁ β₁ γ₁ n.natAbs
      ‖physicalPrimeCellHarmonicFamily P mass A B hU hAB h d χ e ψ a b Z k F G -
        physicalPrimeCellHarmonicFamily P mass A B hU hAB h d χ e ψ a b Z k F' G'‖ ≤ L^(-D) := by
  filter_upwards [eventually_candidate_selected_harmonic_peel_decay hc hb hK J ell 0 Ce D,
    eventually_gt_atTop (0 : ℝ)] with L hpeel hL
  intro P mass A B hU hAB Q h d χ e ψ cut marks big g κ hκ hg hmass b₀ b₁ hb₀ hb₁
    pool hpool α₀ β₀ γ₀ α₁ β₁ γ₁ hα₀free hβ₀free hα₁free hβ₁free
    hα₀ hβ₀ hγ₀ hα₁ hβ₁ hγ₁ U V hUlo hUhi hVlo hVhi k hk j hj a b Z F G F' G'
  apply physical_prime_cell_family_perturbation P mass A B hU hAB h d χ e ψ a b Z k F G F' G'
    hmass (fun _ => rfl) (Real.rpow_pos_of_pos hL _).le
  intro aux
  exact hpeel (candidatePIndices c L) (subset_refl _) cut aux big g κ hκ hg b₀ b₁
    (by simpa only [Real.rpow_zero] using hb₀) (by simpa only [Real.rpow_zero] using hb₁)
    pool hpool α₀ β₀ γ₀ α₁ β₁ γ₁ hα₀free hβ₀free hα₁free hβ₁free
    hα₀ hβ₀ hγ₀ hα₁ hβ₁ hγ₁ U V hUlo hUhi hVlo hVhi k hk j hj
    (physicalPhasedHarmonicCutoff a b Z k (physicalFreeFactor cut aux))
    (fun n _ => physical_phased_harmonic_cutoff_bound a b Z k (physicalFreeFactor cut aux) n)

end Bounty


-- Source module: HarmonicFamilyTruncation

/- The signed auxiliary average keeps its cancellation on the central interval. -/

open Finset MeasureTheory
namespace Bounty

theorem harmonic_cell_family_truncation {ι : Type*} {Z H : ℝ}
    (hZ : 0 < Z) (hH : 0 < H) (I : Finset ι) (c : ι → ℂ) (d : ι → ℕ)
    (hscale : ∀ i ∈ I, c i ≠ 0 → H ≤ (d i : ℝ) ∧ (d i : ℝ) ≤ Real.exp 2*H)
    {k : ℤ} (hk : |(k : ℝ)| ≤ Z/4) (a b : ℝ) (F G : ℤ → ℂ) (R : ℝ) :
    ‖(∑ i ∈ I, c i * (physicalPhase (-(a+b)) (d i) *
      ∑ n ∈ harmonicPositiveSupport Z k (d i),
        ((typeIIHarmonicDyadic ((n : ℝ)/(Z*(d i : ℝ))) : ℂ)/(n : ℂ))*
          physicalPhase a n.natAbs*physicalPhase b (n+k*(d i : ℤ)).natAbs*
          star (F n)*G (n+k*(d i : ℤ)))) -
      ((Z*H : ℝ) : ℂ)⁻¹ * ∫ v in {v : ℝ | ‖v‖ ≤ R}, harmonicLogFourier v *
        ∑ i ∈ I, c i*physicalPhase (-(a+b+2*Real.pi*v)) (d i)*
          harmonicCellPairing (Z*H) Z a b (2*Real.pi*v) (k*(d i : ℤ)) F G‖ ≤
      (∫ v in {v : ℝ | R < ‖v‖}, ‖harmonicLogFourier v‖) *
        ∑ i ∈ I, ‖c i‖ * ∑ n ∈ harmonicCommonSupport (Z*H),
          ‖harmonicCellCoefficient (Z*H) a b (d i) (k*(d i : ℤ)) F G n‖ := by
  let mass := fun i => ∑ n ∈ harmonicCommonSupport (Z*H),
    ‖harmonicCellCoefficient (Z*H) a b (d i) (k*(d i : ℤ)) F G n‖
  have hY : 0 < Z*H := mul_pos hZ hH
  have hn (v : ℝ) :
      ‖((Z*H : ℝ) : ℂ)⁻¹ * (harmonicLogFourier v *
        ∑ i ∈ I, c i*physicalPhase (-(a+b+2*Real.pi*v)) (d i)*
          harmonicCellPairing (Z*H) Z a b (2*Real.pi*v) (k*(d i : ℤ)) F G)‖ ≤
        ‖harmonicLogFourier v‖ * ∑ i ∈ I, ‖c i‖*mass i := by
    rw [mul_sum, mul_sum]
    refine (norm_sum_le _ _).trans ?_
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    by_cases hc : c i = 0
    · simp only [hc, zero_mul, mul_zero, norm_zero, le_refl]
    · have hd : d i ≠ 0 := by
        have hpos : (0 : ℝ) < d i := hH.trans_le (hscale i hi hc).1
        exact_mod_cast hpos.ne'
      calc
        _ = ‖c i‖ * ‖((Z*H : ℝ) : ℂ)⁻¹ *
            (harmonicLogFourier v*physicalPhase (-(a+b+2*Real.pi*v)) (d i)*
              harmonicCellPairing (Z*H) Z a b (2*Real.pi*v) (k*(d i : ℤ)) F G)‖ := by
          rw [← norm_mul]
          congr 1
          ring
        _ ≤ ‖c i‖ * (‖harmonicLogFourier v‖ * mass i) :=
          mul_le_mul_of_nonneg_left
            (harmonic_cell_normalized_integrand_norm hY hZ.ne' hd a b
              (k*(d i : ℤ)) F G v) (norm_nonneg _)
        _ = _ := by ring
  have hs : MeasurableSet {v : ℝ | ‖v‖ ≤ R} :=
    (isClosed_le continuous_norm continuous_const).measurableSet
  have heq : {v : ℝ | ‖v‖ ≤ R}ᶜ = {v : ℝ | R < ‖v‖} := by ext v; simp
  rw [harmonic_cell_family_sum_eq_mellin hZ hH I c d hscale hk a b F G,
    ← integral_const_mul, ← integral_const_mul,
    ← setIntegral_compl hs
      ((harmonic_cell_family_integrable hZ hH I c d hscale a b k F G).const_mul _), heq]
  calc
    _ ≤ ∫ v in {v : ℝ | R < ‖v‖},
        ‖harmonicLogFourier v‖ * ∑ i ∈ I, ‖c i‖*mass i :=
      norm_integral_le_of_norm_le
        ((harmonic_log_fourier_integrable.norm.mul_const _).integrableOn)
        (Filter.Eventually.of_forall hn)
    _ = _ := integral_mul_const _ _

end Bounty


-- Source module: HarmonicFamilyDecay

/- Arbitrary decay of the original signed family from central cancellation and polynomial tail mass. -/

open Finset MeasureTheory Filter
namespace Bounty

theorem eventually_harmonic_cell_family_decay {r : ℝ} (hr : 0 < r) (C D : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ {ι : Type*} (Z H : ℝ) (I : Finset ι)
      (c : ι → ℂ) (d : ι → ℕ) (k : ℤ) (a b : ℝ) (F G : ℤ → ℂ),
      0 < Z → 0 < H →
      (∀ i ∈ I, c i ≠ 0 → H ≤ (d i : ℝ) ∧ (d i : ℝ) ≤ Real.exp 2*H) →
      |(k : ℝ)| ≤ Z/4 →
      (∑ i ∈ I, ‖c i‖ * ∑ n ∈ harmonicCommonSupport (Z*H),
        ‖harmonicCellCoefficient (Z*H) a b (d i) (k*(d i : ℤ)) F G n‖) ≤ L^C →
      (∀ v : ℝ, ‖v‖ ≤ L^r →
        ‖∑ i ∈ I, c i*physicalPhase (-(a+b+2*Real.pi*v)) (d i)*
          harmonicCellPairing (Z*H) Z a b (2*Real.pi*v) (k*(d i : ℤ)) F G‖ ≤
            (Z*H)*L^(-(D+2))) →
      ‖∑ i ∈ I, c i * (physicalPhase (-(a+b)) (d i) *
        ∑ n ∈ harmonicPositiveSupport Z k (d i),
          ((typeIIHarmonicDyadic ((n : ℝ)/(Z*(d i : ℝ))) : ℂ)/(n : ℂ))*
            physicalPhase a n.natAbs*physicalPhase b (n+k*(d i : ℤ)).natAbs*
            star (F n)*G (n+k*(d i : ℤ)))‖ ≤ L^(-D) := by
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    eventually_harmonic_mellin_tail_power hr C (D+1),
    eventually_harmonic_central_integral_decay (D+1)] with L hL ht hc
  intro ι Z H I c d k a b F G hZ hH hscale hk hmass hcentral
  let S := ∑ i ∈ I, c i * (physicalPhase (-(a+b)) (d i) *
    ∑ n ∈ harmonicPositiveSupport Z k (d i),
      ((typeIIHarmonicDyadic ((n : ℝ)/(Z*(d i : ℝ))) : ℂ)/(n : ℂ))*
        physicalPhase a n.natAbs*physicalPhase b (n+k*(d i : ℤ)).natAbs*
        star (F n)*G (n+k*(d i : ℤ)))
  let A := fun v : ℝ => ∑ i ∈ I, c i*physicalPhase (-(a+b+2*Real.pi*v)) (d i)*
    harmonicCellPairing (Z*H) Z a b (2*Real.pi*v) (k*(d i : ℤ)) F G
  let T := ((Z*H : ℝ) : ℂ)⁻¹ *
    ∫ v in {v : ℝ | ‖v‖ ≤ L^r}, harmonicLogFourier v*A v
  have htail : ‖S-T‖ ≤ L^(-(D+1)) :=
    (harmonic_cell_family_truncation hZ hH I c d hscale hk a b F G (L^r)).trans
      (ht _ (by positivity) hmass)
  have hcent : ‖T‖ ≤ L^(-(D+1)) := by
    apply hc (Z*H) (L^r) A (mul_pos hZ hH)
    intro v hv
    simpa only [show D+1+1 = D+2 by ring] using hcentral v hv
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  change ‖S‖ ≤ _
  calc
    ‖S‖ = ‖(S-T)+T‖ := by congr 1; ring
    _ ≤ ‖S-T‖+‖T‖ := norm_add_le _ _
    _ ≤ L^(-(D+1))+L^(-(D+1)) := add_le_add htail hcent
    _ ≤ L*L^(-(D+1)) := by nlinarith [Real.rpow_pos_of_pos hL0 (-(D+1))]
    _ = L^(-D) := by
      calc
        _ = L^(1 : ℝ)*L^(-(D+1)) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hL0]; congr 1; ring

end Bounty


-- Source module: HarmonicFamilyMass

/- Polynomial endpoint energies control the absolute mass used only for the tail. -/

open Finset Real
namespace Bounty

theorem harmonic_cell_family_mass_le {ι : Type*} {Y E M : ℝ}
    (hY : 0 < Y) (hE : 0 ≤ E) (I : Finset ι) (c : ι → ℂ) (d : ι → ℕ)
    (δ : ι → ℤ) (a b : ℝ) (F G : ℤ → ℂ)
    (hc : ∑ i ∈ I, ‖c i‖ ≤ M)
    (hF : ∑ n ∈ harmonicCommonSupport Y,
      ‖(harmonicCommonCutoff ((n : ℝ)/Y) : ℂ)*F n‖^2 ≤ Y*E)
    (hG : ∀ i ∈ I, c i ≠ 0 → ∑ n ∈ harmonicCommonSupport Y,
      ‖(harmonicCommonCutoff (((n+δ i : ℤ) : ℝ)/Y) : ℂ)*G (n+δ i)‖^2 ≤ Y*E) :
    (∑ i ∈ I, ‖c i‖ * ∑ n ∈ harmonicCommonSupport Y,
      ‖harmonicCellCoefficient Y a b (d i) (δ i) F G n‖) ≤ M*(8*E) := by
  calc
    _ ≤ ∑ i ∈ I, ‖c i‖*(8*E) := by
      apply sum_le_sum
      intro i hi
      by_cases hci : c i = 0
      · simp only [hci, norm_zero, zero_mul, le_refl]
      · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        refine (harmonic_cell_coefficient_mass_le_energy hY a b (d i) (δ i) F G).trans ?_
        calc
          _ ≤ (8/Y)*sqrt (Y*E)*sqrt (Y*E) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (sqrt_le_sqrt hF) (by positivity))
              (sqrt_le_sqrt (hG i hi hci)) (sqrt_nonneg _) (by positivity)
          _ = 8*E := by rw [mul_assoc, mul_self_sqrt (mul_nonneg hY.le hE)]; field_simp
    _ = (∑ i ∈ I, ‖c i‖)*(8*E) := (sum_mul ..).symm
    _ ≤ M*(8*E) := mul_le_mul_of_nonneg_right hc (by positivity)

end Bounty


-- Source module: PrimeAuxCellDecay

/- Central cancellation and individual cutoff energies imply decay of the original auxiliary cell family. -/

open Finset Filter
open scoped Classical
namespace Bounty

theorem eventually_physical_prime_cell_family_decay {r : ℝ} (hr : 0 < r) (T D : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
      (P : G → Finset ℕ) (V : G → ℝ) (A B : Finset (RepeatedBigFlatIndex G J ell))
      (hU : ∀ g (j : Fin ell), (⟨g, Sum.inr j⟩ : RepeatedBigFlatIndex G J ell) ∉ A ∪ B)
      (hAB : Disjoint A B) (h : ℝ) (d : ℤ) {Q : ℕ} (χ : BoundedPrimitiveCharacter Q)
      (e : ℤ) (ψ : BoundedPrimitiveCharacter Q) (a b Z : ℝ) (k : ℤ) (F G : ℤ → ℂ),
      (∀ g, 0 < V g) → (∀ g, ∑ p ∈ P g, 1/(p : ℝ) = V g) →
      (∀ g, ∀ p ∈ P g, 0 < p) → 0 < h → h ≤ 1 → 0 < Z → |(k : ℝ)| ≤ Z/4 →
      let Y := Z*harmonicCellProductScale h d e
      let c := physicalPrimeCellAuxCoeff P V A B hU hAB h d χ e ψ
      let m := physicalFreeFactor (repeatedBigAuxCut A B)
      (∑ n ∈ harmonicCommonSupport Y, ‖(harmonicCommonCutoff ((n : ℝ)/Y) : ℂ)*F n‖^2) ≤ Y*L^T →
      (∀ aux, c aux ≠ 0 → (∑ n ∈ harmonicCommonSupport Y,
        ‖(harmonicCommonCutoff (((n+k*(m aux : ℤ) : ℤ) : ℝ)/Y) : ℂ)*G (n+k*(m aux : ℤ))‖^2) ≤ Y*L^T) →
      (∀ v : ℝ, ‖v‖ ≤ L^r →
        ‖∑ aux, c aux*physicalPhase (-(a+b+2*Real.pi*v)) (m aux)*
          harmonicCellPairing Y Z a b (2*Real.pi*v) (k*(m aux : ℤ)) F G‖ ≤ Y*L^(-(D+2))) →
      ‖physicalPrimeCellHarmonicFamily P V A B hU hAB h d χ e ψ a b Z k F G‖ ≤ L^(-D) := by
  filter_upwards [eventually_ge_atTop (8 : ℝ),
    eventually_harmonic_cell_family_decay hr (T+1) D] with L hL hdecay
  intro Gt _ _ J ell P V A B hU hAB h d Q χ e ψ a b Z k F G hV hMass hP hh hh1 hZ hk Y c m hF hG hcentral
  have hL0 : 0 < L := by linarith
  have hY : 0 < Y := mul_pos hZ (harmonic_cell_product_scale_pos h d e)
  have hcoeff := physical_prime_cell_aux_mass P V A B hU hAB h d χ e ψ hV hMass
  have hmass := harmonic_cell_family_mass_le hY (Real.rpow_pos_of_pos hL0 T).le univ c m
    (fun aux => k*(m aux : ℤ)) a b F G hcoeff hF (fun aux _ hc => hG aux hc)
  have hmass' : (∑ aux, ‖c aux‖ * ∑ n ∈ harmonicCommonSupport Y,
      ‖harmonicCellCoefficient Y a b (m aux) (k*(m aux : ℤ)) F G n‖) ≤ L^(T+1) := by
    apply hmass.trans
    simp only [one_mul]
    calc
      8*L^T ≤ L*L^T := mul_le_mul_of_nonneg_right hL (Real.rpow_pos_of_pos hL0 T).le
      _ = L^(T+1) := by rw [Real.rpow_add hL0, Real.rpow_one]; ring
  exact hdecay Z (harmonicCellProductScale h d e) univ c m k a b F G hZ
    (harmonic_cell_product_scale_pos h d e)
    (fun aux _ hc => physical_prime_cell_aux_scale P V A B hU hAB hh hh1 d χ e ψ hP aux hc)
    hk hmass' hcentral

end Bounty


-- Source module: PrimeRetainedAuxDecay

/- Absorb the exact outer inverse cell masses and character sums after auxiliary cancellation. -/

open Finset Filter
open scoped Classical
namespace Bounty

theorem eventually_retained_prime_aux_decay {r : ℝ} (hr : 0 < r) (T D B C R : ℝ)
    (hB : 0 ≤ B) :
    ∀ᶠ L : ℝ in atTop, ∀ {Gt : Type*} [Fintype Gt] [DecidableEq Gt] {J ell : ℕ}
      (P : Gt → Finset ℕ) (V : Gt → ℝ) (A B' : Finset (RepeatedBigFlatIndex Gt J ell))
      (hU : ∀ g (j : Fin ell), (⟨g, Sum.inr j⟩ : RepeatedBigFlatIndex Gt J ell) ∉ A ∪ B')
      (hAB : Disjoint A B') (Q : ℕ) (a b Z : ℝ) (k : ℤ)
      (F G : ℤ → BoundedPrimitiveCharacter Q → ℤ → ℂ),
      (∀ g, 0 < V g) → (∀ g, ∑ p ∈ P g, 1/(p : ℝ) = V g) →
      (∀ g, ∀ p ∈ P g, 0 < p) → (Q : ℝ) ≤ L^R → 0 < Z → |(k : ℝ)| ≤ Z/4 →
      (∀ x : (∀ i : A, P i.val.1),
        0 ≤ Real.log (∏ i, (x i).val : ℕ) ∧ Real.log (∏ i, (x i).val : ℕ) ≤ L) →
      (∀ x : (∀ i : B', P i.val.1),
        0 ≤ Real.log (∏ i, (x i).val : ℕ) ∧ Real.log (∏ i, (x i).val : ℕ) ≤ L) →
      let h := L^(-B)
      let kept := fun U : Finset (RepeatedBigFlatIndex Gt J ell) =>
        primeProductRetainedCells (fun i : U => P i.val.1) (fun i => V i.val.1) h (L^(-C))
      let c := physicalPrimeCellAuxCoeff P V A B' hU hAB h
      let m := physicalFreeFactor (repeatedBigAuxCut A B')
      (∀ d ∈ kept A, ∀ χ, ∀ e ∈ kept B', ∀ ψ,
        let Y := Z*harmonicCellProductScale h d e
        (∑ n ∈ harmonicCommonSupport Y,
          ‖(harmonicCommonCutoff ((n : ℝ)/Y) : ℂ)*F e ψ n‖^2) ≤ Y*L^T ∧
        (∀ aux, c d χ e ψ aux ≠ 0 → (∑ n ∈ harmonicCommonSupport Y,
          ‖(harmonicCommonCutoff (((n+k*(m aux : ℤ) : ℤ) : ℝ)/Y) : ℂ)*G d χ (n+k*(m aux : ℤ))‖^2) ≤ Y*L^T) ∧
        (∀ v : ℝ, ‖v‖ ≤ L^r →
          ‖∑ aux, c d χ e ψ aux*physicalPhase (-(a+b+2*Real.pi*v)) (m aux)*
            harmonicCellPairing Y Z a b (2*Real.pi*v) (k*(m aux : ℤ)) (F e ψ) (G d χ)‖ ≤
              Y*L^(-(D+2*(B+C+2*R+2)+2)))) →
      let mA := fun d => ((1 / finiteCellMass (finiteProductWeight (physicalLabelLaw (P := fun i : A => P i.val.1)
        (fun i => V i.val.1))) (fun x => upperLogCell h (Real.log (∏ i, (x i).val : ℕ))) d : ℝ) : ℂ)
      let mB := fun e => ((1 / finiteCellMass (finiteProductWeight (physicalLabelLaw (P := fun i : B' => P i.val.1)
        (fun i => V i.val.1))) (fun x => upperLogCell h (Real.log (∏ i, (x i).val : ℕ))) e : ℝ) : ℂ)
      ‖∑ d ∈ kept A, ∑ χ : BoundedPrimitiveCharacter Q, ∑ e ∈ kept B', ∑ ψ : BoundedPrimitiveCharacter Q,
        mA d*mB e*physicalPrimeCellHarmonicFamily P V A B' hU hAB h d χ e ψ a b Z k (F e ψ) (G d χ)‖ ≤ L^(-D) := by
  filter_upwards [eventually_ge_atTop (3 : ℝ),
    eventually_physical_prime_cell_family_decay hr T (D+2*(B+C+2*R+2))] with L hL hdecay
  intro Gt _ _ J ell P V A B' hU hAB Q a b Z k F G hV hMass hP hQ hZ hk hPA hPB h kept c m he mA mB
  have hL0 : 0 < L := by linarith
  have hh : 0 < h := Real.rpow_pos_of_pos hL0 _
  have hh1 : h ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hcell : ∀ d ∈ kept A, ∀ χ, ∀ e ∈ kept B', ∀ ψ,
      ‖physicalPrimeCellHarmonicFamily P V A B' hU hAB h d χ e ψ a b Z k (F e ψ) (G d χ)‖ ≤
        1*L^(-(D+2*(B+C+2*R+2))) := by
    intro d hd χ e he' ψ
    obtain ⟨hF,hG,hcentral⟩ := he d hd χ e he' ψ
    simpa only [one_mul] using hdecay P V A B' hU hAB h d χ e ψ a b Z k (F e ψ) (G d χ)
      hV hMass hP hh hh1 hZ hk hF hG hcentral
  simpa only [one_mul] using prime_retained_pair_cell_decay
    (fun i : A => P i.val.1) (fun i => V i.val.1)
    (fun i : B' => P i.val.1) (fun i => V i.val.1) hL hB hQ zero_le_one hPA hPB
    (fun d χ e ψ => physicalPrimeCellHarmonicFamily P V A B' hU hAB h d χ e ψ a b Z k (F e ψ) (G d χ)) hcell

end Bounty


-- Source module: PrimeRetainedFamilyDifference

/- The same retained-cell cost controls the difference of two exact endpoint families. -/

open Finset
open scoped Classical
namespace Bounty

theorem prime_retained_harmonic_families_close
    {Gt : Type*} [Fintype Gt] [DecidableEq Gt] {J ell : ℕ}
    (P : Gt → Finset ℕ) (V : Gt → ℝ)
    (A B' : Finset (RepeatedBigFlatIndex Gt J ell))
    (hU : ∀ g (j : Fin ell), (⟨g, Sum.inr j⟩ : RepeatedBigFlatIndex Gt J ell) ∉ A ∪ B')
    (hAB : Disjoint A B') {Q : ℕ} {L B C R D : ℝ}
    (hL : 3 ≤ L) (hB : 0 ≤ B) (hQ : (Q : ℝ) ≤ L^R)
    (hPA : ∀ x : (∀ i : A, P i.val.1),
      0 ≤ Real.log (∏ i, (x i).val : ℕ) ∧ Real.log (∏ i, (x i).val : ℕ) ≤ L)
    (hPB : ∀ x : (∀ i : B', P i.val.1),
      0 ≤ Real.log (∏ i, (x i).val : ℕ) ∧ Real.log (∏ i, (x i).val : ℕ) ≤ L)
    (a b Z : ℝ) (k : ℤ)
    (F G F' G' : ℤ → BoundedPrimitiveCharacter Q → ℤ → ℂ) :
    let h := L^(-B)
    let kept := fun U : Finset (RepeatedBigFlatIndex Gt J ell) =>
      primeProductRetainedCells (fun i : U => P i.val.1) (fun i => V i.val.1) h (L^(-C))
    let mA := fun d => ((1 / finiteCellMass (finiteProductWeight (physicalLabelLaw (P := fun i : A => P i.val.1)
      (fun i => V i.val.1))) (fun x => upperLogCell h (Real.log (∏ i, (x i).val : ℕ))) d : ℝ) : ℂ)
    let mB := fun e => ((1 / finiteCellMass (finiteProductWeight (physicalLabelLaw (P := fun i : B' => P i.val.1)
      (fun i => V i.val.1))) (fun x => upperLogCell h (Real.log (∏ i, (x i).val : ℕ))) e : ℝ) : ℂ)
    (∀ d ∈ kept A, ∀ χ, ∀ e ∈ kept B', ∀ ψ,
      ‖physicalPrimeCellHarmonicFamily P V A B' hU hAB h d χ e ψ a b Z k (F e ψ) (G d χ) -
        physicalPrimeCellHarmonicFamily P V A B' hU hAB h d χ e ψ a b Z k (F' e ψ) (G' d χ)‖ ≤
          L^(-(D+2*(B+C+2*R+2)))) →
    ‖(∑ d ∈ kept A, ∑ χ : BoundedPrimitiveCharacter Q, ∑ e ∈ kept B', ∑ ψ : BoundedPrimitiveCharacter Q,
        mA d*mB e*physicalPrimeCellHarmonicFamily P V A B' hU hAB h d χ e ψ a b Z k (F e ψ) (G d χ)) -
      (∑ d ∈ kept A, ∑ χ : BoundedPrimitiveCharacter Q, ∑ e ∈ kept B', ∑ ψ : BoundedPrimitiveCharacter Q,
        mA d*mB e*physicalPrimeCellHarmonicFamily P V A B' hU hAB h d χ e ψ a b Z k (F' e ψ) (G' d χ))‖ ≤ L^(-D) := by
  intro h kept mA mB herr
  have he := prime_retained_pair_cell_decay
    (fun i : A => P i.val.1) (fun i => V i.val.1)
    (fun i : B' => P i.val.1) (fun i => V i.val.1) hL hB hQ zero_le_one hPA hPB
    (fun d χ e ψ => physicalPrimeCellHarmonicFamily P V A B' hU hAB h d χ e ψ a b Z k (F e ψ) (G d χ) -
      physicalPrimeCellHarmonicFamily P V A B' hU hAB h d χ e ψ a b Z k (F' e ψ) (G' d χ))
    (fun d hd χ e he ψ => by simpa only [one_mul] using herr d hd χ e he ψ)
  simpa only [mul_sub, sum_sub_distrib, one_mul] using he

end Bounty


-- Source module: FiniteCellHarmonicLift

/- Lifting an exact finite cell expansion to a phased harmonic finite sum. -/

open Finset
open scoped Classical
namespace Bounty

theorem finite_cell_harmonic_lift {G ι : Type*} [Fintype G]
    (P : G → Finset ℕ) (marks : G → ℕ) (cells : Finset ι)
    (f g : ι → GroupMarkedLists P marks → ℂ) (coeff : ι → ℂ)
    (W : ℕ → ℝ) (K : ℕ → ℕ → ℂ)
    (hK : ∀ w z, K w z = ∑ i ∈ cells,
      coeff i * (((W w : ℂ)*groupMarkedAverage P marks (w : ℤ) (f i)) *
        ((W z : ℂ)*groupMarkedAverage P marks (z : ℤ) (g i))))
    (T : Finset ℤ) (w z : ℤ → ℕ) (θ : ℤ → ℂ) (F H : ℕ → ℂ)
    (a b : ℝ) (C : ℂ) :
    (∑ n ∈ T, θ n*star (F (w n))*H (z n)*
      (C*physicalPhase a (w n)*physicalPhase b (z n)*K (w n) (z n))) =
      C*∑ i ∈ cells, coeff i*∑ n ∈ T, θ n*
        star (physicalPhase (-a) (w n)*
          ((W (w n) : ℂ)*groupMarkedAverage P marks (w n : ℤ)
            (fun u => star (f i u))*F (w n)))*
        (physicalPhase b (z n)*
          ((W (z n) : ℂ)*groupMarkedAverage P marks (z n : ℤ) (g i)*H (z n))) := by
  simp_rw [hK]
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro n hn
  have hp := selected_marked_phased_pair P marks (f i) (g i) (w n) (z n)
    (W (w n)) (W (z n)) a b (C*coeff i) (θ n) (F (w n)) (H (z n))
    ((C*coeff i)*physicalPhase a (w n)*physicalPhase b (z n)*
      ((W (w n) : ℂ)*groupMarkedAverage P marks (w n : ℤ) (f i))*
      ((W (z n) : ℂ)*groupMarkedAverage P marks (z n : ℤ) (g i))) rfl
  convert hp using 1 <;> ring

end Bounty


-- Source module: PrimeCellsHarmonic

/- Exact cell-dependent endpoints in the original two-sided prime average. -/

open Finset
open scoped Classical
namespace Bounty

theorem physical_prime_cells_harmonic
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ)
    (A B : Finset (RepeatedBigFlatIndex G J ell))
    (hU : ∀ g (j : Fin ell), (⟨g, Sum.inr j⟩ : RepeatedBigFlatIndex G J ell) ∉ A ∪ B)
    (hAB : Disjoint A B) (Q : ℕ) (h : ℝ) (keptA keptB : Finset ℤ)
    (S : Finset G) (hA : ∀ i ∈ A, i.1 ∈ S) (hB : ∀ i ∈ B, i.1 ∈ S)
    (q : ℝ) (aux : PhysicalAuxLabels P (repeatedBigAuxCut A B))
    (T : Finset ℤ) (w z : ℤ → ℕ) (θ : ℤ → ℂ) (F H : ℕ → ℂ)
    (a b : ℝ) (C : ℂ) :
    let marks := fun g => ell + (repeatedBigAuxCut A B g).card
    let W := fun n : ℕ => markedDivisorWeight univ P q V marks n
    let cells := (keptA ×ˢ (univ : Finset (BoundedPrimitiveCharacter Q))) ×ˢ
      (keptB ×ˢ (univ : Finset (BoundedPrimitiveCharacter Q)))
    let f := fun (j : (ℤ × BoundedPrimitiveCharacter Q) × (ℤ × BoundedPrimitiveCharacter Q)) u => primeProductCellCharacter (fun i : B => P i.val.1) h j.2.1 j.2.2
      (physicalSelectedPrimeRestriction A B B subset_union_right S hB u)
    let g := fun (j : (ℤ × BoundedPrimitiveCharacter Q) × (ℤ × BoundedPrimitiveCharacter Q)) u => primeProductCellCharacter (fun i : A => P i.val.1) h j.1.1 j.1.2
      (physicalSelectedPrimeRestriction A B A subset_union_left S hA u)
    let coeff := fun (j : (ℤ × BoundedPrimitiveCharacter Q) × (ℤ × BoundedPrimitiveCharacter Q)) =>
      ((((1 / finiteCellMass (finiteProductWeight (physicalLabelLaw (P := fun i : A => P i.val.1)
        (fun i => V i.val.1))) (fun x => upperLogCell h (Real.log (∏ i, (x i).val : ℕ))) j.1.1 : ℝ) : ℂ) *
       ((1 / finiteCellMass (finiteProductWeight (physicalLabelLaw (P := fun i : B => P i.val.1)
        (fun i => V i.val.1))) (fun x => upperLogCell h (Real.log (∏ i, (x i).val : ℕ))) j.2.1 : ℝ) : ℂ)) *
       ((starRingEnd ℂ) (primeProductCellCharacter (fun i : A => P i.val.1) h j.1.1 j.1.2
          (repeatedBigAuxSplitEquiv P A B hU hAB aux).1) *
        (starRingEnd ℂ) (primeProductCellCharacter (fun i : B => P i.val.1) h j.2.1 j.2.2
          (repeatedBigAuxSplitEquiv P A B hU hAB aux).2)))
    (∑ n ∈ T, θ n*star (F (w n))*H (z n)*
      (C*physicalPhase a (w n)*physicalPhase b (z n)*
        (((W (w n)*W (z n) : ℝ) : ℂ)*groupMarkedAverage P marks (w n : ℤ) (fun u =>
          groupMarkedAverage P marks (z n : ℤ) (fun v =>
            physicalUnsharedPrimeCoefficient P V A B hU hAB Q h keptA keptB u v aux))))) =
      C*∑ j ∈ cells, coeff j*∑ n ∈ T, θ n*
        star (physicalPhase (-a) (w n)*
          ((W (w n) : ℂ)*groupMarkedAverage (fun i : S => P i.val) (fun i : S => marks i.val)
            (w n : ℤ) (fun u => star (f j u))*F (w n)))*
        (physicalPhase b (z n)*
          ((W (z n) : ℂ)*groupMarkedAverage (fun i : S => P i.val) (fun i : S => marks i.val)
            (z n : ℤ) (g j)*H (z n))) := by
  intro marks W cells f g coeff
  let K := fun x y : ℕ => ((W x*W y : ℝ) : ℂ)*groupMarkedAverage P marks (x : ℤ) (fun u =>
    groupMarkedAverage P marks (y : ℤ) (fun v =>
      physicalUnsharedPrimeCoefficient P V A B hU hAB Q h keptA keptB u v aux))
  apply finite_cell_harmonic_lift (fun i : S => P i.val) (fun i : S => marks i.val)
    cells f g coeff W K _ T w z θ F H a b C
  intro x y
  have he := physical_prime_cell_average P V A B hU hAB Q h keptA keptB S hA hB q
    (x : ℤ) (y : ℤ) aux
  dsimp only at he
  simpa only [cells, sum_product] using he

end Bounty


-- Source module: PrimePatternHarmonicAverage

/- The original signed pattern and auxiliary phase stay outside the cell expansion. -/

open Finset
open scoped Classical
namespace Bounty

theorem physical_free_prime_inr_weighted_average
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ) (probes : G → Finset (Fin J))
    (r t : Finset G) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (ab : RepeatedBigPrimePatternPair (ell := ell) probes r t)
    (aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t (.inr ab)))
    (a b q : ℝ) (w z : ℕ) :
    let hv := repeated_big_prime_pattern_pair_valid probes r t hrt ab
    let cut := repeatedBigPrimePatternCut probes r t (.inr ab)
    let kept := fun U : Finset (RepeatedBigFlatIndex G J ell) =>
      primeProductRetainedCells (fun j : U => P j.val.1) (fun j => V j.val.1) h ξ
    let marks := fun g => ell+(cut g).card
    let W := fun n : ℕ => markedDivisorWeight univ P q V marks n
    ((W w*W z : ℝ) : ℂ)*groupMarkedAverage P marks (w : ℤ) (fun u =>
      groupMarkedAverage P marks (z : ℤ)
        (physicalFreePrimePairCoefficient P V probes r t hrt Q h ξ (.inr ab) aux a b w z u)) =
      (repeatedBigPrimePatternWeight probes r t (.inr ab)*
        physicalPhase (-(a+b)) (physicalFreeFactor cut aux))*physicalPhase a w*physicalPhase b z*
        (((W w*W z : ℝ) : ℂ)*groupMarkedAverage P marks (w : ℤ) (fun u =>
          groupMarkedAverage P marks (z : ℤ) (fun v =>
            physicalUnsharedPrimeCoefficient P V ab.1.val ab.2.val
              (repeated_big_active_pair_avoids_tail hv.1 hv.2.1) hv.2.2 Q h
              (kept ab.1.val) (kept ab.2.val) u v aux))) := by
  intro hv cut kept marks W
  unfold physicalFreePrimePairCoefficient
  dsimp only [physicalUnsharedPrimePatternKernel, marks, cut, repeatedBigPrimePatternCut]
  simp only [groupMarkedAverage, mul_sum]
  apply sum_congr rfl
  intro u _
  apply sum_congr rfl
  intro v _
  dsimp only [kept, hv]
  ring

theorem physical_free_prime_raw_coefficient
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ) (probes : G → Finset (Fin J))
    (r t : Finset G) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut (ell := ell) probes r t (.inl ())))
    (a b : ℝ) (w z : ℕ)
    (u v : GroupMarkedLists P (fun g => ell+(repeatedBigPrimePatternCut (ell := ell) probes r t (.inl ()) g).card)) :
    physicalFreePrimePairCoefficient P V probes r t hrt Q h ξ (.inl ()) aux a b w z u v =
      physicalPhase a w*physicalPhase b z*
        physicalPhase (-(a+b)) (physicalFreeFactor (repeatedBigPrimePatternCut (ell := ell) probes r t (.inl ())) aux) := by
  simp only [physicalFreePrimePairCoefficient, repeatedBigPrimePatternWeight,
    physicalUnsharedPrimePatternKernel, mul_one, one_mul]


theorem physical_free_harmonic_inr_average
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ) (probes : G → Finset (Fin J))
    (r t : Finset G) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (ab : RepeatedBigPrimePatternPair (ell := ell) probes r t)
    (aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t (.inr ab)))
    (a b Z : ℝ) (k : ℤ) (pool : Finset ℕ) (α β γ α' β' γ' : ℕ → ℂ) :
    let hv := repeated_big_prime_pattern_pair_valid probes r t hrt ab
    let cut := repeatedBigPrimePatternCut probes r t (.inr ab)
    let kept := fun U : Finset (RepeatedBigFlatIndex G J ell) =>
      primeProductRetainedCells (fun j : U => P j.val.1) (fun j => V j.val.1) h ξ
    let marks := fun g => ell+(cut g).card
    let W := fun n : ℕ => markedDivisorWeight univ P (1/2) V marks n
    let d := physicalFreeFactor cut aux
    let δ : ℤ := k*(d : ℤ)
    physicalFreePositiveHarmonicMain P V probes r t hrt Q h ξ (.inr ab) aux a b Z k pool α β γ α' β' γ' =
      ∑ n ∈ harmonicPositiveSupport Z k d,
        ((typeIIHarmonicDyadic ((n : ℝ)/(Z*(d : ℝ))) : ℂ)/(n : ℂ))*
          star (invariantTripleEndpoint pool α β γ n.natAbs)*
          invariantTripleEndpoint pool α' β' γ' (n+δ).natAbs*
          ((repeatedBigPrimePatternWeight probes r t (.inr ab)*physicalPhase (-(a+b)) d)*
            physicalPhase a n.natAbs*physicalPhase b (n+δ).natAbs*
            (((W n.natAbs*W (n+δ).natAbs : ℝ) : ℂ)*
              groupMarkedAverage P marks (n.natAbs : ℤ) (fun u =>
                groupMarkedAverage P marks ((n+δ).natAbs : ℤ) (fun v =>
                  physicalUnsharedPrimeCoefficient P V ab.1.val ab.2.val
                    (repeated_big_active_pair_avoids_tail hv.1 hv.2.1) hv.2.2 Q h
                    (kept ab.1.val) (kept ab.2.val) u v aux)))) := by
  intro hv cut kept marks W d δ
  unfold physicalFreePositiveHarmonicMain
  dsimp only
  apply sum_congr rfl
  intro n _
  have he := physical_free_prime_inr_weighted_average P V probes r t hrt Q h ξ ab aux
    a b (1/2) n.natAbs (n+δ).natAbs
  dsimp only at he
  simpa only [mul_assoc] using congrArg (fun x : ℂ =>
    ((typeIIHarmonicDyadic ((n : ℝ)/(Z*(d : ℝ))) : ℂ)/(n : ℂ))*
      star (invariantTripleEndpoint pool α β γ n.natAbs)*
      invariantTripleEndpoint pool α' β' γ' (n+δ).natAbs*x) he

end Bounty


-- Source module: PrimePatternHarmonicCells

/- The literal original nonempty pattern is a finite sum of its exact cell-dependent harmonic pairings. -/

open Finset
open scoped Classical
namespace Bounty

noncomputable def physicalPrimeHarmonicCellSum
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ)
    (A B : Finset (RepeatedBigFlatIndex G J ell))
    (hU : ∀ g (j : Fin ell), (⟨g, Sum.inr j⟩ : RepeatedBigFlatIndex G J ell) ∉ A ∪ B)
    (hAB : Disjoint A B) (Q : ℕ) (h : ℝ) (keptA keptB : Finset ℤ)
    (S : Finset G) (hA : ∀ i ∈ A, i.1 ∈ S) (hB : ∀ i ∈ B, i.1 ∈ S)
    (q : ℝ) (aux : PhysicalAuxLabels P (repeatedBigAuxCut A B))
    (T : Finset ℤ) (w z : ℤ → ℕ) (θ : ℤ → ℂ) (F H : ℕ → ℂ)
    (a b : ℝ) (C : ℂ) : ℂ :=
    let marks := fun g => ell + (repeatedBigAuxCut A B g).card
    let W := fun n : ℕ => markedDivisorWeight univ P q V marks n
    let cells := (keptA ×ˢ (univ : Finset (BoundedPrimitiveCharacter Q))) ×ˢ
      (keptB ×ˢ (univ : Finset (BoundedPrimitiveCharacter Q)))
    let f := fun (j : (ℤ × BoundedPrimitiveCharacter Q) × (ℤ × BoundedPrimitiveCharacter Q)) u => primeProductCellCharacter (fun i : B => P i.val.1) h j.2.1 j.2.2
      (physicalSelectedPrimeRestriction A B B subset_union_right S hB u)
    let g := fun (j : (ℤ × BoundedPrimitiveCharacter Q) × (ℤ × BoundedPrimitiveCharacter Q)) u => primeProductCellCharacter (fun i : A => P i.val.1) h j.1.1 j.1.2
      (physicalSelectedPrimeRestriction A B A subset_union_left S hA u)
    let coeff := fun (j : (ℤ × BoundedPrimitiveCharacter Q) × (ℤ × BoundedPrimitiveCharacter Q)) =>
      ((((1 / finiteCellMass (finiteProductWeight (physicalLabelLaw (P := fun i : A => P i.val.1)
        (fun i => V i.val.1))) (fun x => upperLogCell h (Real.log (∏ i, (x i).val : ℕ))) j.1.1 : ℝ) : ℂ) *
       ((1 / finiteCellMass (finiteProductWeight (physicalLabelLaw (P := fun i : B => P i.val.1)
        (fun i => V i.val.1))) (fun x => upperLogCell h (Real.log (∏ i, (x i).val : ℕ))) j.2.1 : ℝ) : ℂ)) *
       ((starRingEnd ℂ) (primeProductCellCharacter (fun i : A => P i.val.1) h j.1.1 j.1.2
          (repeatedBigAuxSplitEquiv P A B hU hAB aux).1) *
        (starRingEnd ℂ) (primeProductCellCharacter (fun i : B => P i.val.1) h j.2.1 j.2.2
          (repeatedBigAuxSplitEquiv P A B hU hAB aux).2)))
    C*∑ j ∈ cells, coeff j*∑ n ∈ T, θ n*
        star (physicalPhase (-a) (w n)*
          ((W (w n) : ℂ)*groupMarkedAverage (fun i : S => P i.val) (fun i : S => marks i.val)
            (w n : ℤ) (fun u => star (f j u))*F (w n)))*
        (physicalPhase b (z n)*
          ((W (z n) : ℂ)*groupMarkedAverage (fun i : S => P i.val) (fun i : S => marks i.val)
            (z n : ℤ) (g j)*H (z n)))

theorem physical_free_harmonic_inr_cells
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ) (probes : G → Finset (Fin J))
    (r t : Finset G) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (ab : RepeatedBigPrimePatternPair (ell := ell) probes r t)
    (aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t (.inr ab)))
    (a b Z : ℝ) (k : ℤ) (pool : Finset ℕ) (α β γ α' β' γ' : ℕ → ℂ) :
    let hv := repeated_big_prime_pattern_pair_valid probes r t hrt ab
    let kept := fun U : Finset (RepeatedBigFlatIndex G J ell) =>
      primeProductRetainedCells (fun j : U => P j.val.1) (fun j => V j.val.1) h ξ
    let hA : ∀ j ∈ ab.1.val, j.1 ∈ r ∪ t := fun _j hj =>
      mem_union_left t (mem_sigma.mp (((clean_mem_nonempty_subsets _ _).mp ab.1.property).2 hj)).1
    let hB : ∀ j ∈ ab.2.val, j.1 ∈ r ∪ t := fun _j hj =>
      mem_union_right r (mem_sigma.mp (((clean_mem_nonempty_subsets _ _).mp ab.2.property).2 hj)).1
    let d := physicalFreeFactor (repeatedBigPrimePatternCut probes r t (.inr ab)) aux
    physicalFreePositiveHarmonicMain P V probes r t hrt Q h ξ (.inr ab) aux a b Z k pool α β γ α' β' γ' =
      physicalPrimeHarmonicCellSum P V ab.1.val ab.2.val
        (repeated_big_active_pair_avoids_tail hv.1 hv.2.1) hv.2.2 Q h
        (kept ab.1.val) (kept ab.2.val) (r ∪ t) hA hB (1/2) aux
        (harmonicPositiveSupport Z k d) Int.natAbs (fun n => (n+k*(d : ℤ)).natAbs)
        (fun n => (typeIIHarmonicDyadic ((n : ℝ)/(Z*(d : ℝ))) : ℂ)/(n : ℂ))
        (invariantTripleEndpoint pool α β γ) (invariantTripleEndpoint pool α' β' γ') a b
        (repeatedBigPrimePatternWeight probes r t (.inr ab)*physicalPhase (-(a+b)) d) := by
  intro hv kept hA hB d
  rw [physical_free_harmonic_inr_average]
  exact physical_prime_cells_harmonic P V ab.1.val ab.2.val
    (repeated_big_active_pair_avoids_tail hv.1 hv.2.1) hv.2.2 Q h
    (kept ab.1.val) (kept ab.2.val) (r ∪ t) hA hB (1/2) aux
    (harmonicPositiveSupport Z k d) Int.natAbs (fun n => (n+k*(d : ℤ)).natAbs)
    (fun n => (typeIIHarmonicDyadic ((n : ℝ)/(Z*(d : ℝ))) : ℂ)/(n : ℂ))
    (invariantTripleEndpoint pool α β γ) (invariantTripleEndpoint pool α' β' γ') a b
    (repeatedBigPrimePatternWeight probes r t (.inr ab)*physicalPhase (-(a+b)) d)

end Bounty


-- Source module: PrimeAuxHarmonicExpansion

/- Exact reindexing of the original auxiliary average into its cell-dependent endpoint families. -/

open Finset
open scoped Classical
namespace Bounty

noncomputable def physicalPrimeCellEndpoint
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ)
    (A B U : Finset (RepeatedBigFlatIndex G J ell)) (hUAB : U ⊆ A ∪ B)
    (S : Finset G) (hUS : ∀ i ∈ U, i.1 ∈ S) (q : ℝ)
    (f : (∀ i : U, P i.val.1) → ℂ) (E : ℕ → ℂ) (n : ℕ) : ℂ :=
  (markedDivisorWeight univ P q V (fun g => ell + (repeatedBigAuxCut A B g).card) n : ℂ) *
    groupMarkedAverage (fun i : S => P i.val) (fun i : S => ell + (repeatedBigAuxCut A B i.val).card)
      (n : ℤ) (fun u => f (physicalSelectedPrimeRestriction A B U hUAB S hUS u)) * E n

theorem physical_prime_harmonic_cells_aux_sum
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ)
    (A B : Finset (RepeatedBigFlatIndex G J ell))
    (hU : ∀ g (j : Fin ell), (⟨g, Sum.inr j⟩ : RepeatedBigFlatIndex G J ell) ∉ A ∪ B)
    (hAB : Disjoint A B) (Q : ℕ) (h : ℝ) (keptA keptB : Finset ℤ)
    (S : Finset G) (hA : ∀ i ∈ A, i.1 ∈ S) (hB : ∀ i ∈ B, i.1 ∈ S)
    (q : ℝ) (E E' : ℕ → ℂ) (a b Z : ℝ) (k : ℤ) (σ : ℂ) :
    let F := fun e (ψ : BoundedPrimitiveCharacter Q) (n : ℤ) => physicalPrimeCellEndpoint P V A B B subset_union_right S hB q
      (fun x => star (primeProductCellCharacter (fun i : B => P i.val.1) h e ψ x)) E n.natAbs
    let G := fun d (χ : BoundedPrimitiveCharacter Q) (n : ℤ) => physicalPrimeCellEndpoint P V A B A subset_union_left S hA q
      (primeProductCellCharacter (fun i : A => P i.val.1) h d χ) E' n.natAbs
    let mA := fun d => ((1 / finiteCellMass (finiteProductWeight (physicalLabelLaw (P := fun i : A => P i.val.1)
        (fun i => V i.val.1))) (fun x => upperLogCell h (Real.log (∏ i, (x i).val : ℕ))) d : ℝ) : ℂ)
    let mB := fun e => ((1 / finiteCellMass (finiteProductWeight (physicalLabelLaw (P := fun i : B => P i.val.1)
        (fun i => V i.val.1))) (fun x => upperLogCell h (Real.log (∏ i, (x i).val : ℕ))) e : ℝ) : ℂ)
    (∑ aux : PhysicalAuxLabels P (repeatedBigAuxCut A B),
      (physicalAuxMass V (repeatedBigAuxCut A B) aux : ℂ) *
        physicalPrimeHarmonicCellSum P V A B hU hAB Q h keptA keptB S hA hB q aux
          (harmonicPositiveSupport Z k (physicalFreeFactor (repeatedBigAuxCut A B) aux))
          Int.natAbs (fun n => (n+k*(physicalFreeFactor (repeatedBigAuxCut A B) aux : ℤ)).natAbs)
          (fun n => (typeIIHarmonicDyadic ((n : ℝ)/(Z*(physicalFreeFactor (repeatedBigAuxCut A B) aux : ℝ))) : ℂ)/(n : ℂ))
          E E' a b (σ*physicalPhase (-(a+b)) (physicalFreeFactor (repeatedBigAuxCut A B) aux))) =
      σ * ∑ d ∈ keptA, ∑ χ : BoundedPrimitiveCharacter Q, ∑ e ∈ keptB, ∑ ψ : BoundedPrimitiveCharacter Q,
        mA d*mB e*physicalPrimeCellHarmonicFamily P V A B hU hAB h d χ e ψ a b Z k (F e ψ) (G d χ) := by
  intro F G mA mB
  simp only [physicalPrimeHarmonicCellSum, sum_product]
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro d _
  rw [sum_comm]
  apply sum_congr rfl
  intro χ _
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  rw [sum_comm]
  apply sum_congr rfl
  intro ψ _
  simp only [physicalPrimeCellHarmonicFamily, mul_sum]
  apply sum_congr rfl
  intro aux _
  simp only [physicalPrimeCellAuxCoeff]
  apply sum_congr rfl
  intro n _
  dsimp only [F, G, mA, mB, physicalPrimeCellEndpoint]
  rw [star_mul, physical_phase_star, neg_neg]
  simp only [starRingEnd_apply]
  ring

end Bounty


-- Source module: PrimePatternAuxPeel

/- The literal nonempty-pattern auxiliary average differs from its peeled cell expansion by an arbitrary logarithmic saving. -/

open Finset Filter
open scoped Classical
namespace Bounty

theorem eventually_physical_free_harmonic_inr_peel {c bWindow Kdet : ℝ}
    (hc : 0 < c) (hb : 0 < bWindow) (hK : 0 ≤ Kdet)
    (J ell : ℕ) (Ce D B C R : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ L : ℝ in atTop,
      let P := fun g : candidatePIndices c L => candidatePBand (c*L) g.val
      let mass := fun g => ∑ p ∈ P g, 1/(p : ℝ)
      ∀ (probes : candidatePIndices c L → Finset (Fin J)) (r t : Finset (candidatePIndices c L))
        (hrt : Disjoint r t) (ab : RepeatedBigPrimePatternPair (ell := ell) probes r t),
      let hv := repeated_big_prime_pattern_pair_valid probes r t hrt ab
      let hA : ∀ j ∈ ab.1.val, j.1 ∈ r ∪ t := fun _j hj =>
        mem_union_left t (mem_sigma.mp (((clean_mem_nonempty_subsets _ _).mp ab.1.property).2 hj)).1
      let hB' : ∀ j ∈ ab.2.val, j.1 ∈ r ∪ t := fun _j hj =>
        mem_union_right r (mem_sigma.mp (((clean_mem_nonempty_subsets _ _).mp ab.2.property).2 hj)).1
      let cut := repeatedBigAuxCut ab.1.val ab.2.val
      let marks := fun j => ell+(cut j).card
      ∀ (g : candidatePIndices c L) (κ : ℕ), marks g = κ+1 → g ∉ r ∪ t →
      (∀ j, 0 < mass j) →
      ∀ Q : ℕ, (Q : ℝ) ≤ L^R →
      (∀ x : (∀ i : ab.1.val, P i.val.1),
        0 ≤ Real.log (∏ i, (x i).val : ℕ) ∧ Real.log (∏ i, (x i).val : ℕ) ≤ L) →
      (∀ x : (∀ i : ab.2.val, P i.val.1),
        0 ≤ Real.log (∏ i, (x i).val : ℕ) ∧ Real.log (∏ i, (x i).val : ℕ) ≤ L) →
      ∀ (pool : Finset ℕ), (∀ j, P j ⊆ pool) →
      ∀ (α₀ β₀ γ₀ α₁ β₁ γ₁ : ℕ → ℂ),
      (∀ n, ¬ Disjoint n.primeFactors pool → α₀ n = 0) →
      (∀ n, ¬ Disjoint n.primeFactors pool → β₀ n = 0) →
      (∀ n, ¬ Disjoint n.primeFactors pool → α₁ n = 0) →
      (∀ n, ¬ Disjoint n.primeFactors pool → β₁ n = 0) →
      (∀ n, ‖α₀ n‖ ≤ L^Ce) → (∀ n, ‖β₀ n‖ ≤ L^Ce) → (∀ n, ‖γ₀ n‖ ≤ L^Ce) →
      (∀ n, ‖α₁ n‖ ≤ L^Ce) → (∀ n, ‖β₁ n‖ ≤ L^Ce) → (∀ n, ‖γ₁ n‖ ≤ L^Ce) →
      ∀ U V : ℝ, Real.exp (bWindow*L) ≤ U → U ≤ Real.exp L →
        Real.exp (bWindow*L) ≤ V → V ≤ Real.exp L →
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L Kdet : ℤ)) (typeIIAdmissibleDeterminantBound L Kdet : ℤ),
      ∀ j ∈ range (typeIISmoothDyadicCount L), ∀ a b : ℝ,
      let Z := typeIISmoothDyadicScale U V (U*L^(-Kdet)) j
      let h := L^(-B)
      let kept := fun U : Finset (RepeatedBigFlatIndex (candidatePIndices c L) J ell) =>
        primeProductRetainedCells (fun i : U => P i.val.1) (fun i => mass i.val.1) h (L^(-C))
      let b₀ := fun e (ψ : BoundedPrimitiveCharacter Q) u =>
        star (primeProductCellCharacter (fun i : ab.2.val => P i.val.1) h e ψ
          (physicalSelectedPrimeRestriction ab.1.val ab.2.val ab.2.val subset_union_right (r ∪ t) hB' u))
      let b₁ := fun d (χ : BoundedPrimitiveCharacter Q) u =>
        primeProductCellCharacter (fun i : ab.1.val => P i.val.1) h d χ
          (physicalSelectedPrimeRestriction ab.1.val ab.2.val ab.1.val subset_union_left (r ∪ t) hA u)
      let F' := fun e ψ (n : ℤ) => selectedPeeledEndpoint P (1/2) mass marks g κ (r ∪ t) (b₀ e ψ)
        pool α₀ β₀ γ₀ n.natAbs
      let G' := fun d χ (n : ℤ) => selectedPeeledEndpoint P (1/2) mass marks g κ (r ∪ t) (b₁ d χ)
        pool α₁ β₁ γ₁ n.natAbs
      let mA := fun d => ((1 / finiteCellMass (finiteProductWeight (physicalLabelLaw (P := fun i : ab.1.val => P i.val.1)
        (fun i => mass i.val.1))) (fun x => upperLogCell h (Real.log (∏ i, (x i).val : ℕ))) d : ℝ) : ℂ)
      let mB := fun e => ((1 / finiteCellMass (finiteProductWeight (physicalLabelLaw (P := fun i : ab.2.val => P i.val.1)
        (fun i => mass i.val.1))) (fun x => upperLogCell h (Real.log (∏ i, (x i).val : ℕ))) e : ℝ) : ℂ)
      ‖(∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t (.inr ab)),
        (physicalAuxMass mass (repeatedBigPrimePatternCut probes r t (.inr ab)) aux : ℂ)*
          physicalFreePositiveHarmonicMain P mass probes r t hrt Q h (L^(-C)) (.inr ab) aux
            a b Z k pool α₀ β₀ γ₀ α₁ β₁ γ₁) -
        repeatedBigPrimePatternWeight probes r t (.inr ab)*
          ∑ d ∈ kept ab.1.val, ∑ χ : BoundedPrimitiveCharacter Q,
            ∑ e ∈ kept ab.2.val, ∑ ψ : BoundedPrimitiveCharacter Q,
              mA d*mB e*physicalPrimeCellHarmonicFamily P mass ab.1.val ab.2.val
                (repeated_big_active_pair_avoids_tail hv.1 hv.2.1) hv.2.2 h d χ e ψ a b Z k (F' e ψ) (G' d χ)‖ ≤ L^(-D) := by
  filter_upwards [eventually_candidate_aux_cell_peel hc hb hK J ell Ce (D+2*(B+C+2*R+2)),
    eventually_ge_atTop (3 : ℝ)] with L hpeel hL
  intro P mass probes r t hrt ab hv hA hB' cut marks g κ hκ hg hmass Q hQ hPA hPB
    pool hpool α₀ β₀ γ₀ α₁ β₁ γ₁ hα₀free hβ₀free hα₁free hβ₁free
    hα₀ hβ₀ hγ₀ hα₁ hβ₁ hγ₁ U V hUlo hUhi hVlo hVhi k hk j hj a b Z h kept b₀ b₁ F' G' mA mB
  let F := fun e (ψ : BoundedPrimitiveCharacter Q) (n : ℤ) =>
    selectedMarkedEndpoint P (1/2) mass marks (r ∪ t) (b₀ e ψ) pool α₀ β₀ γ₀ n.natAbs
  let G := fun d (χ : BoundedPrimitiveCharacter Q) (n : ℤ) =>
    selectedMarkedEndpoint P (1/2) mass marks (r ∪ t) (b₁ d χ) pool α₁ β₁ γ₁ n.natAbs
  have hdiff := prime_retained_harmonic_families_close (C := C) (D := D) P mass ab.1.val ab.2.val
    (repeated_big_active_pair_avoids_tail hv.1 hv.2.1) hv.2.2 hL hB hQ hPA hPB
    a b Z k F G F' G'
  have heach : ∀ d ∈ kept ab.1.val, ∀ χ : BoundedPrimitiveCharacter Q,
      ∀ e ∈ kept ab.2.val, ∀ ψ : BoundedPrimitiveCharacter Q,
      ‖physicalPrimeCellHarmonicFamily P mass ab.1.val ab.2.val
          (repeated_big_active_pair_avoids_tail hv.1 hv.2.1) hv.2.2 h d χ e ψ a b Z k (F e ψ) (G d χ) -
        physicalPrimeCellHarmonicFamily P mass ab.1.val ab.2.val
          (repeated_big_active_pair_avoids_tail hv.1 hv.2.1) hv.2.2 h d χ e ψ a b Z k (F' e ψ) (G' d χ)‖ ≤
          L^(-(D+2*(B+C+2*R+2))) := by
    intro d _ χ e _ ψ
    have hb₀ : ∀ u, ‖b₀ e ψ u‖ ≤ 1 := by
      intro u
      dsimp only [b₀]
      rw [norm_star]
      exact prime_product_cell_character_norm _ h e ψ _
    have hb₁ : ∀ u, ‖b₁ d χ u‖ ≤ 1 := fun _ => prime_product_cell_character_norm _ h d χ _
    exact hpeel ab.1.val ab.2.val
      (repeated_big_active_pair_avoids_tail hv.1 hv.2.1) hv.2.2 Q h d χ e ψ (r ∪ t) g κ hκ hg hmass
      (b₀ e ψ) (b₁ d χ) hb₀ hb₁ pool hpool α₀ β₀ γ₀ α₁ β₁ γ₁
      hα₀free hβ₀free hα₁free hβ₁free hα₀ hβ₀ hγ₀ hα₁ hβ₁ hγ₁
      U V hUlo hUhi hVlo hVhi k hk j hj a b
  have hexp := physical_prime_harmonic_cells_aux_sum P mass ab.1.val ab.2.val
    (repeated_big_active_pair_avoids_tail hv.1 hv.2.1) hv.2.2 Q h
    (kept ab.1.val) (kept ab.2.val) (r ∪ t) hA hB' (1/2)
    (invariantTripleEndpoint pool α₀ β₀ γ₀) (invariantTripleEndpoint pool α₁ β₁ γ₁)
    a b Z k (repeatedBigPrimePatternWeight probes r t (.inr ab))
  have hsum := Finset.sum_congr (s₁ := (univ : Finset (PhysicalAuxLabels P
      (repeatedBigPrimePatternCut probes r t (.inr ab))))) rfl
    (fun aux _ => congrArg (fun z : ℂ =>
      (physicalAuxMass mass (repeatedBigPrimePatternCut probes r t (.inr ab)) aux : ℂ)*z)
        (physical_free_harmonic_inr_cells P mass probes r t hrt Q h (L^(-C)) ab aux
          a b Z k pool α₀ β₀ γ₀ α₁ β₁ γ₁))
  rw [hsum.trans hexp, ← mul_sub, norm_mul, repeated_big_prime_pattern_weight_norm, one_mul]
  exact hdiff heach

end Bounty


-- Source module: PrimeAuxPairDecay

/- Central cancellation and shifted pair energies imply decay of the original auxiliary cell family. -/

open Finset Filter
open scoped Classical
namespace Bounty

theorem eventually_physical_prime_cell_family_decay_of_pair {r : ℝ} (hr : 0 < r) (T D : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
      (P : G → Finset ℕ) (V : G → ℝ) (A B : Finset (RepeatedBigFlatIndex G J ell))
      (hU : ∀ g (j : Fin ell), (⟨g, Sum.inr j⟩ : RepeatedBigFlatIndex G J ell) ∉ A ∪ B)
      (hAB : Disjoint A B) (h : ℝ) (d : ℤ) {Q : ℕ} (χ : BoundedPrimitiveCharacter Q)
      (e : ℤ) (ψ : BoundedPrimitiveCharacter Q) (a b Z : ℝ) (k : ℤ) (F G : ℤ → ℂ),
      (∀ g, 0 < V g) → (∀ g, ∑ p ∈ P g, 1/(p : ℝ) = V g) →
      (∀ g, ∀ p ∈ P g, 0 < p) → 0 < h → h ≤ 1 → 0 < Z → |(k : ℝ)| ≤ Z/4 →
      let Y := Z*harmonicCellProductScale h d e
      let c := physicalPrimeCellAuxCoeff P V A B hU hAB h d χ e ψ
      let m := physicalFreeFactor (repeatedBigAuxCut A B)
      (∀ aux, c aux ≠ 0 →
        (8/Y)*Real.sqrt (∑ n ∈ harmonicCommonSupport Y,
          ‖(harmonicCommonCutoff ((n : ℝ)/Y) : ℂ)*F n‖^2)*
          Real.sqrt (∑ n ∈ harmonicCommonSupport Y,
            ‖(harmonicCommonCutoff (((n+k*(m aux : ℤ) : ℤ) : ℝ)/Y) : ℂ)*G (n+k*(m aux : ℤ))‖^2) ≤ L^T) →
      (∀ v : ℝ, ‖v‖ ≤ L^r →
        ‖∑ aux, c aux*physicalPhase (-(a+b+2*Real.pi*v)) (m aux)*
          harmonicCellPairing Y Z a b (2*Real.pi*v) (k*(m aux : ℤ)) F G‖ ≤ Y*L^(-(D+2))) →
      ‖physicalPrimeCellHarmonicFamily P V A B hU hAB h d χ e ψ a b Z k F G‖ ≤ L^(-D) := by
  filter_upwards [eventually_ge_atTop (8 : ℝ),
    eventually_harmonic_cell_family_decay hr T D] with L hL hdecay
  intro Gt _ _ J ell P V A B hU hAB h d Q χ e ψ a b Z k F G hV hMass hP hh hh1 hZ hk Y c m hpair hcentral
  have hL0 : 0 < L := by linarith
  have hY : 0 < Y := mul_pos hZ (harmonic_cell_product_scale_pos h d e)
  have hcoeff := physical_prime_cell_aux_mass P V A B hU hAB h d χ e ψ hV hMass
  have hmass : (∑ aux, ‖c aux‖ * ∑ n ∈ harmonicCommonSupport Y,
      ‖harmonicCellCoefficient Y a b (m aux) (k*(m aux : ℤ)) F G n‖) ≤ L^T := by
    calc
      _ ≤ ∑ aux, ‖c aux‖*L^T := by
        apply sum_le_sum
        intro aux _
        by_cases hz : c aux = 0
        · simp only [hz, norm_zero, zero_mul, le_refl]
        · exact mul_le_mul_of_nonneg_left
            ((harmonic_cell_coefficient_mass_le_energy hY a b (m aux) (k*(m aux : ℤ)) F G).trans
              (hpair aux hz)) (norm_nonneg _)
      _ = (∑ aux, ‖c aux‖)*L^T := (sum_mul ..).symm
      _ ≤ 1*L^T := mul_le_mul_of_nonneg_right hcoeff (Real.rpow_pos_of_pos hL0 T).le
      _ = L^T := one_mul _
  exact hdecay Z (harmonicCellProductScale h d e) univ c m k a b F G hZ
    (harmonic_cell_product_scale_pos h d e)
    (fun aux _ hc => physical_prime_cell_aux_scale P V A B hU hAB hh hh1 d χ e ψ hP aux hc)
    hk hmass hcentral

end Bounty


-- Source module: ActualRetainedCellSourceParameters

/- Original retained harmonic windows supply the source-scale hypotheses for
occupied comparison cells, with source exponent half the window exponent. -/

open Finset Filter
open scoped Classical

namespace Bounty

theorem eventually_actual_retained_cell_source_parameters {c bWindow K : ℝ}
    (hc : 0 < c) (hbWindow : 0 < bWindow) (hK : 0 ≤ K) (J : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (groups : Finset ℕ), groups ⊆ candidatePIndices c L →
      let P := fun g : groups => candidatePBand (c*L) g.val
      ∀ (ell : ℕ) (A B : Finset (RepeatedBigFlatIndex groups J ell))
        (_hU : ∀ g (i : Fin ell),
          (⟨g, Sum.inr i⟩ : RepeatedBigFlatIndex groups J ell) ∉ A ∪ B)
        (_hAB : Disjoint A B),
      ∀ U V : ℝ, Real.exp (bWindow*L) ≤ U → U ≤ Real.exp L →
        Real.exp (bWindow*L) ≤ V → V ≤ Real.exp L →
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L K : ℤ))
        (typeIIAdmissibleDeterminantBound L K : ℤ),
      ∀ j ∈ range (typeIISmoothDyadicCount L),
      ∀ (Q : ℕ) (h : ℝ), 0 < h → h ≤ 1 →
      ∀ (d e : ℤ) (χ ψ : BoundedPrimitiveCharacter Q) (ζ : ℝ)
        (x : ∀ i : A, P i.val.1) (y : ∀ i : B, P i.val.1),
        (starRingEnd ℂ) (primeProductCellCharacter (fun i : A => P i.val.1) h d χ x) *
          physicalPhase ζ (∏ i, (x i).val) ≠ 0 →
        (starRingEnd ℂ) (primeProductCellCharacter (fun i : B => P i.val.1) h e ψ y) *
          physicalPhase ζ (∏ i, (y i).val) ≠ 0 →
      let Z := typeIISmoothDyadicScale U V (U*L^(-K)) j
      let HA := Real.exp (((d : ℝ)-1)*h)
      let HB := Real.exp (((e : ℝ)-1)*h)
      let Y := Z*(HA*HB)
      0 < Z ∧
        Real.exp (2*(bWindow/2)*L) ≤
          Z*((((∏ i, (x i).val)*(∏ i, (y i).val)) : ℕ) : ℝ)/2 ∧
        1 ≤ Y ∧ Real.log Y ≤ 6*L ∧ |(k : ℝ)| ≤ Z/4 := by
  filter_upwards [eventually_candidate_harmonic_common_scale hc hbWindow hK J,
    eventually_typeII_harmonic_scale_lower hbWindow hK] with L hcommon hlower
  intro groups hgroups P ell A B hU hAB U V hUlo hUhi hVlo hVhi k hk j hj
    Q h hh hh1 d e χ ψ ζ x y hx hy
  let aux := (repeatedBigAuxSplitEquiv P A B hU hAB).symm (x,y)
  have hprod : physicalFreeFactor (repeatedBigAuxCut A B) aux =
      (∏ i : A, (x i).val)*(∏ i : B, (y i).val) :=
    repeatedBigAuxSplitEquiv_symm_label_prod P A B hU hAB x y
  have hposA : 0 < ∏ i : A, (x i).val := by
    apply Finset.prod_pos
    intro i _
    exact ((mem_dyadicPrimeBand_iff (c*L) (3/2) (9/5) i.val.1.val (x i).val).mp
      (x i).property).1.pos
  have hposB : 0 < ∏ i : B, (y i).val := by
    apply Finset.prod_pos
    intro i _
    exact ((mem_dyadicPrimeBand_iff (c*L) (3/2) (9/5) i.val.1.val (y i).val).mp
      (y i).property).1.pos
  have hcharA : primeProductCellCharacter (fun i : A => P i.val.1) h d χ x ≠ 0 := by
    intro hz
    exact hx (by rw [hz,map_zero,zero_mul])
  have hcharB : primeProductCellCharacter (fun i : B => P i.val.1) h e ψ y ≠ 0 := by
    intro hz
    exact hy (by rw [hz,map_zero,zero_mul])
  have hs := hcommon groups hgroups (repeatedBigAuxCut A B) aux
    U V hUlo hUhi hVlo hVhi k hk j hj h _ _ d e hh hh1 hposA hposB hprod
    (prime_cell_character_mem (fun i : A => P i.val.1) h d χ x hcharA)
    (prime_cell_character_mem (fun i : B => P i.val.1) h e ψ y hcharB)
  have hzLower := hlower U V hUlo hVlo j
  have hZ : 0 < typeIISmoothDyadicScale U V (U*L^(-K)) j :=
    (mul_pos (by norm_num) (Real.exp_pos _)).trans_le hzLower
  have hprodOne : (1 : ℝ) ≤
      (((∏ i : A, (x i).val)*(∏ i : B, (y i).val) : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.mul_pos hposA hposB)
  refine ⟨hZ,?_,hs.2.1,hs.2.2.1,hs.2.2.2.1⟩
  rw [show 2*(bWindow/2)*L = bWindow*L by ring]
  nlinarith only [hzLower,mul_le_mul_of_nonneg_left hprodOne hZ.le]

end Bounty


-- Source module: CandidateOriginalCellDecay

/- Peeled auxiliary cell decay on the original harmonic windows; pair energies and occupied-cell scales are discharged. -/

open Finset Filter
open scoped Classical
namespace Bounty

theorem eventually_candidate_aux_cell_decay {c bWindow Kdet r : ℝ}
    (hc : 0 < c) (hb : 0 < bWindow) (hK : 0 ≤ Kdet) (hr : 0 < r) (J ell : ℕ) (Ce D : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      let P := fun g : candidatePIndices c L => candidatePBand (c*L) g.val
      let mass := fun g => ∑ p ∈ P g, 1/(p : ℝ)
      ∀ (A B : Finset (RepeatedBigFlatIndex (candidatePIndices c L) J ell))
        (hU : ∀ g (j : Fin ell),
          (⟨g, Sum.inr j⟩ : RepeatedBigFlatIndex (candidatePIndices c L) J ell) ∉ A ∪ B)
        (hAB : Disjoint A B) (Q : ℕ) (h : ℝ), 0 < h → h ≤ 1 → ∀ (d : ℤ) (χ : BoundedPrimitiveCharacter Q)
        (e : ℤ) (ψ : BoundedPrimitiveCharacter Q),
      let cut := repeatedBigAuxCut A B
      let marks := fun g => ell+(cut g).card
      ∀ (big : Finset (candidatePIndices c L)) (g : candidatePIndices c L) (κ : ℕ),
      marks g = κ+1 → g ∉ big → (∀ j, 0 < mass j) →
      ∀ (b₀ b₁ : GroupMarkedLists (fun j : big => P j.val) (fun j : big => marks j.val) → ℂ),
      (∀ u, ‖b₀ u‖ ≤ 1) → (∀ u, ‖b₁ u‖ ≤ 1) →
      ∀ (pool : Finset ℕ), (∀ j, P j ⊆ pool) →
      ∀ (α₀ β₀ γ₀ α₁ β₁ γ₁ : ℕ → ℂ),
      (∀ n, ¬ Disjoint n.primeFactors pool → α₀ n = 0) →
      (∀ n, ¬ Disjoint n.primeFactors pool → β₀ n = 0) →
      (∀ n, ¬ Disjoint n.primeFactors pool → α₁ n = 0) →
      (∀ n, ¬ Disjoint n.primeFactors pool → β₁ n = 0) →
      (∀ n, ‖α₀ n‖ ≤ L^Ce) → (∀ n, ‖β₀ n‖ ≤ L^Ce) → (∀ n, ‖γ₀ n‖ ≤ L^Ce) →
      (∀ n, ‖α₁ n‖ ≤ L^Ce) → (∀ n, ‖β₁ n‖ ≤ L^Ce) → (∀ n, ‖γ₁ n‖ ≤ L^Ce) →
      ∀ U V : ℝ, Real.exp (bWindow*L) ≤ U → U ≤ Real.exp L →
        Real.exp (bWindow*L) ≤ V → V ≤ Real.exp L →
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L Kdet : ℤ)) (typeIIAdmissibleDeterminantBound L Kdet : ℤ),
      ∀ j ∈ range (typeIISmoothDyadicCount L), ∀ a b : ℝ,
      let Z := typeIISmoothDyadicScale U V (U*L^(-Kdet)) j
      let F' := fun n : ℤ => selectedPeeledEndpoint P (1/2) mass marks g κ big b₀ pool α₀ β₀ γ₀ n.natAbs
      let G' := fun n : ℤ => selectedPeeledEndpoint P (1/2) mass marks g κ big b₁ pool α₁ β₁ γ₁ n.natAbs
      let Y := Z*harmonicCellProductScale h d e
      let caux := physicalPrimeCellAuxCoeff P mass A B hU hAB h d χ e ψ
      let m := physicalFreeFactor (repeatedBigAuxCut A B)
      (∀ v : ℝ, ‖v‖ ≤ L^r →
        ‖∑ aux, caux aux*physicalPhase (-(a+b+2*Real.pi*v)) (m aux)*
          harmonicCellPairing Y Z a b (2*Real.pi*v) (k*(m aux : ℤ)) F' G'‖ ≤ Y*L^(-(D+2))) →
      ‖physicalPrimeCellHarmonicFamily P mass A B hU hAB h d χ e ψ a b Z k F' G'‖ ≤ L^(-D) := by
  obtain ⟨T,henergy⟩ := exists_candidate_harmonic_cutoff_energy hc J ell 0 Ce
  filter_upwards [henergy, eventually_physical_prime_cell_family_decay_of_pair hr T D,
    eventually_actual_retained_cell_source_parameters hc hb hK J,
    eventually_gt_atTop (0 : ℝ)] with L he hdecay hscale hL
  intro P mass A B hU hAB Q h hh hh1 d χ e ψ cut marks big g κ hκ hg hmass b₀ b₁ hb₀ hb₁
    pool hpool α₀ β₀ γ₀ α₁ β₁ γ₁ hα₀free hβ₀free hα₁free hβ₁free
    hα₀ hβ₀ hγ₀ hα₁ hβ₁ hγ₁ U V hUlo hUhi hVlo hVhi k hk j hj a b Z F' G' Y caux m hcentral
  by_cases hocc : ∃ aux, caux aux ≠ 0
  · obtain ⟨aux,haux⟩ := hocc
    have hca : primeProductCellCharacter (fun i : A => P i.val.1) h d χ
        (repeatedBigAuxSplitEquiv P A B hU hAB aux).1 ≠ 0 := by
      intro hz
      exact haux (by simp only [caux, physicalPrimeCellAuxCoeff, hz, star_zero, mul_zero, zero_mul])
    have hcb : primeProductCellCharacter (fun i : B => P i.val.1) h e ψ
        (repeatedBigAuxSplitEquiv P A B hU hAB aux).2 ≠ 0 := by
      intro hz
      exact haux (by simp only [caux, physicalPrimeCellAuxCoeff, hz, star_zero, mul_zero])
    have hp (n : ℕ) : physicalPhase 0 n ≠ 0 := by
      intro hz
      have hn := physical_phase_norm 0 n
      rw [hz, norm_zero] at hn
      exact zero_ne_one hn
    have hs := hscale (candidatePIndices c L) (subset_refl _) ell A B hU hAB
      U V hUlo hUhi hVlo hVhi k hk j hj Q h hh hh1 d e χ ψ 0
      (repeatedBigAuxSplitEquiv P A B hU hAB aux).1
      (repeatedBigAuxSplitEquiv P A B hU hAB aux).2
      (mul_ne_zero (star_ne_zero.mpr hca) (hp _)) (mul_ne_zero (star_ne_zero.mpr hcb) (hp _))
    apply hdecay P mass A B hU hAB h d χ e ψ a b Z k F' G'
      hmass (fun _ => rfl) (fun g p hp =>
        ((mem_dyadicPrimeBand_iff (c*L) (3/2) (9/5) g.val p).mp hp).1.pos)
      hh hh1 hs.1 hs.2.2.2.2
    · intro aux _
      have he' := (he (candidatePIndices c L) (subset_refl _) cut big g κ hκ hg b₀ b₁
        (by simpa only [Real.rpow_zero] using hb₀) (by simpa only [Real.rpow_zero] using hb₁)
        pool hpool α₀ β₀ γ₀ α₁ β₁ γ₁ hα₀free hβ₀free hα₁free hβ₁free
        hα₀ hβ₀ hγ₀ hα₁ hβ₁ hγ₁ Y hs.2.2.1 hs.2.2.2.1 (k*(m aux : ℤ))).2
      simpa only [add_zero] using he'
    · exact hcentral
  · have hz : ∀ aux, caux aux = 0 := by simpa only [not_exists, not_not] using hocc
    have hf : physicalPrimeCellHarmonicFamily P mass A B hU hAB h d χ e ψ a b Z k F' G' = 0 := by
      unfold physicalPrimeCellHarmonicFamily
      apply sum_eq_zero
      intro aux _
      rw [show physicalPrimeCellAuxCoeff P mass A B hU hAB h d χ e ψ aux = 0 from hz aux, zero_mul]
    rw [hf,norm_zero]
    exact (Real.rpow_pos_of_pos hL _).le

end Bounty


-- Source module: PrimePatternCentralDecay

/- The original nonempty-pattern auxiliary average decays from central cancellation of the exact peeled cell endpoints. -/

open Finset Filter
open scoped Classical
namespace Bounty

theorem eventually_physical_free_harmonic_inr_of_peeled_central {c bWindow Kdet r0 : ℝ}
    (hc : 0 < c) (hb : 0 < bWindow) (hK : 0 ≤ Kdet) (hr0 : 0 < r0)
    (J ell : ℕ) (Ce D B C R : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ L : ℝ in atTop,
      let P := fun g : candidatePIndices c L => candidatePBand (c*L) g.val
      let mass := fun g => ∑ p ∈ P g, 1/(p : ℝ)
      ∀ (probes : candidatePIndices c L → Finset (Fin J)) (r t : Finset (candidatePIndices c L))
        (hrt : Disjoint r t) (ab : RepeatedBigPrimePatternPair (ell := ell) probes r t),
      let hv := repeated_big_prime_pattern_pair_valid probes r t hrt ab
      let hA : ∀ j ∈ ab.1.val, j.1 ∈ r ∪ t := fun _j hj =>
        mem_union_left t (mem_sigma.mp (((clean_mem_nonempty_subsets _ _).mp ab.1.property).2 hj)).1
      let hB' : ∀ j ∈ ab.2.val, j.1 ∈ r ∪ t := fun _j hj =>
        mem_union_right r (mem_sigma.mp (((clean_mem_nonempty_subsets _ _).mp ab.2.property).2 hj)).1
      let cut := repeatedBigAuxCut ab.1.val ab.2.val
      let marks := fun j => ell+(cut j).card
      ∀ (g : candidatePIndices c L) (κ : ℕ), marks g = κ+1 → g ∉ r ∪ t →
      (∀ j, 0 < mass j) →
      ∀ Q : ℕ, (Q : ℝ) ≤ L^R →
      (∀ x : (∀ i : ab.1.val, P i.val.1),
        0 ≤ Real.log (∏ i, (x i).val : ℕ) ∧ Real.log (∏ i, (x i).val : ℕ) ≤ L) →
      (∀ x : (∀ i : ab.2.val, P i.val.1),
        0 ≤ Real.log (∏ i, (x i).val : ℕ) ∧ Real.log (∏ i, (x i).val : ℕ) ≤ L) →
      ∀ (pool : Finset ℕ), (∀ j, P j ⊆ pool) →
      ∀ (α₀ β₀ γ₀ α₁ β₁ γ₁ : ℕ → ℂ),
      (∀ n, ¬ Disjoint n.primeFactors pool → α₀ n = 0) →
      (∀ n, ¬ Disjoint n.primeFactors pool → β₀ n = 0) →
      (∀ n, ¬ Disjoint n.primeFactors pool → α₁ n = 0) →
      (∀ n, ¬ Disjoint n.primeFactors pool → β₁ n = 0) →
      (∀ n, ‖α₀ n‖ ≤ L^Ce) → (∀ n, ‖β₀ n‖ ≤ L^Ce) → (∀ n, ‖γ₀ n‖ ≤ L^Ce) →
      (∀ n, ‖α₁ n‖ ≤ L^Ce) → (∀ n, ‖β₁ n‖ ≤ L^Ce) → (∀ n, ‖γ₁ n‖ ≤ L^Ce) →
      ∀ U V : ℝ, Real.exp (bWindow*L) ≤ U → U ≤ Real.exp L →
        Real.exp (bWindow*L) ≤ V → V ≤ Real.exp L →
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L Kdet : ℤ)) (typeIIAdmissibleDeterminantBound L Kdet : ℤ),
      ∀ j ∈ range (typeIISmoothDyadicCount L), ∀ a b : ℝ,
      let Z := typeIISmoothDyadicScale U V (U*L^(-Kdet)) j
      let h := L^(-B)
      let kept := fun U : Finset (RepeatedBigFlatIndex (candidatePIndices c L) J ell) =>
        primeProductRetainedCells (fun i : U => P i.val.1) (fun i => mass i.val.1) h (L^(-C))
      let b₀ := fun e (ψ : BoundedPrimitiveCharacter Q) u =>
        star (primeProductCellCharacter (fun i : ab.2.val => P i.val.1) h e ψ
          (physicalSelectedPrimeRestriction ab.1.val ab.2.val ab.2.val subset_union_right (r ∪ t) hB' u))
      let b₁ := fun d (χ : BoundedPrimitiveCharacter Q) u =>
        primeProductCellCharacter (fun i : ab.1.val => P i.val.1) h d χ
          (physicalSelectedPrimeRestriction ab.1.val ab.2.val ab.1.val subset_union_left (r ∪ t) hA u)
      let F' := fun e ψ (n : ℤ) => selectedPeeledEndpoint P (1/2) mass marks g κ (r ∪ t) (b₀ e ψ)
        pool α₀ β₀ γ₀ n.natAbs
      let G' := fun d χ (n : ℤ) => selectedPeeledEndpoint P (1/2) mass marks g κ (r ∪ t) (b₁ d χ)
        pool α₁ β₁ γ₁ n.natAbs
      (∀ d ∈ kept ab.1.val, ∀ χ : BoundedPrimitiveCharacter Q,
        ∀ e ∈ kept ab.2.val, ∀ ψ : BoundedPrimitiveCharacter Q, ∀ v : ℝ, ‖v‖ ≤ L^r0 →
        let Y := Z*harmonicCellProductScale h d e
        ‖∑ aux : PhysicalAuxLabels P (repeatedBigAuxCut ab.1.val ab.2.val),
          physicalPrimeCellAuxCoeff P mass ab.1.val ab.2.val
            (repeated_big_active_pair_avoids_tail hv.1 hv.2.1) hv.2.2 h d χ e ψ aux *
          physicalPhase (-(a+b+2*Real.pi*v)) (physicalFreeFactor (repeatedBigAuxCut ab.1.val ab.2.val) aux) *
          harmonicCellPairing Y Z a b (2*Real.pi*v)
            (k*(physicalFreeFactor (repeatedBigAuxCut ab.1.val ab.2.val) aux : ℤ)) (F' e ψ) (G' d χ)‖ ≤
              Y*L^(-((D+1)+2*(B+C+2*R+2)+2))) →
      ‖(∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t (.inr ab)),
        (physicalAuxMass mass (repeatedBigPrimePatternCut probes r t (.inr ab)) aux : ℂ)*
          physicalFreePositiveHarmonicMain P mass probes r t hrt Q h (L^(-C)) (.inr ab) aux
            a b Z k pool α₀ β₀ γ₀ α₁ β₁ γ₁)‖ ≤ L^(-D) := by
  filter_upwards [eventually_physical_free_harmonic_inr_peel hc hb hK J ell Ce (D+1) B C R hB,
    eventually_candidate_aux_cell_decay hc hb hK hr0 J ell Ce ((D+1)+2*(B+C+2*R+2)),
    eventually_ge_atTop (3 : ℝ)] with L hpeel hdecay hL
  intro P mass probes r t hrt ab hv hA hB' cut marks g κ hκ hg hmass Q hQ hPA hPB
    pool hpool α₀ β₀ γ₀ α₁ β₁ γ₁ hα₀free hβ₀free hα₁free hβ₁free
    hα₀ hβ₀ hγ₀ hα₁ hβ₁ hγ₁ U V hUlo hUhi hVlo hVhi k hk j hj a b Z h kept b₀ b₁ F' G' hcentral
  have hL0 : 0 < L := by linarith
  have hh : 0 < h := Real.rpow_pos_of_pos hL0 _
  have hh1 : h ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hb₀ (e : ℤ) (ψ : BoundedPrimitiveCharacter Q) : ∀ u, ‖b₀ e ψ u‖ ≤ 1 := by
    intro u
    dsimp only [b₀]
    rw [norm_star]
    exact prime_product_cell_character_norm _ h e ψ _
  have hb₁ (d : ℤ) (χ : BoundedPrimitiveCharacter Q) : ∀ u, ‖b₁ d χ u‖ ≤ 1 :=
    fun _ => prime_product_cell_character_norm _ h d χ _
  have hcell : ∀ d ∈ kept ab.1.val, ∀ χ : BoundedPrimitiveCharacter Q,
      ∀ e ∈ kept ab.2.val, ∀ ψ : BoundedPrimitiveCharacter Q,
      ‖physicalPrimeCellHarmonicFamily P mass ab.1.val ab.2.val
        (repeated_big_active_pair_avoids_tail hv.1 hv.2.1) hv.2.2 h d χ e ψ a b Z k (F' e ψ) (G' d χ)‖ ≤
          1*L^(-((D+1)+2*(B+C+2*R+2))) := by
    intro d hd χ e he ψ
    simpa only [one_mul] using hdecay ab.1.val ab.2.val
      (repeated_big_active_pair_avoids_tail hv.1 hv.2.1) hv.2.2 Q h hh hh1 d χ e ψ
      (r ∪ t) g κ hκ hg hmass (b₀ e ψ) (b₁ d χ) (hb₀ e ψ) (hb₁ d χ)
      pool hpool α₀ β₀ γ₀ α₁ β₁ γ₁ hα₀free hβ₀free hα₁free hβ₁free
      hα₀ hβ₀ hγ₀ hα₁ hβ₁ hγ₁ U V hUlo hUhi hVlo hVhi k hk j hj a b
      (hcentral d hd χ e he ψ)
  have hret := prime_retained_pair_cell_decay
    (fun i : ab.1.val => P i.val.1) (fun i => mass i.val.1)
    (fun i : ab.2.val => P i.val.1) (fun i => mass i.val.1)
    hL hB hQ zero_le_one hPA hPB
    (fun d χ e ψ => physicalPrimeCellHarmonicFamily P mass ab.1.val ab.2.val
      (repeated_big_active_pair_avoids_tail hv.1 hv.2.1) hv.2.2 h d χ e ψ a b Z k (F' e ψ) (G' d χ)) hcell
  have hclose := hpeel probes r t hrt ab g κ hκ hg hmass Q hQ hPA hPB
    pool hpool α₀ β₀ γ₀ α₁ β₁ γ₁ hα₀free hβ₀free hα₁free hβ₁free
    hα₀ hβ₀ hγ₀ hα₁ hβ₁ hγ₁ U V hUlo hUhi hVlo hVhi k hk j hj a b
  have htri (x y : ℂ) : ‖x‖ ≤ ‖x-y‖+‖y‖ := by
    simpa only [add_comm] using norm_le_norm_add_norm_sub' x y
  have hnorm := (htri _ _).trans (_root_.add_le_add hclose (show _ ≤ L^(-(D+1)) from by
    rw [norm_mul, repeated_big_prime_pattern_weight_norm, one_mul]
    simpa only [one_mul] using hret))
  apply hnorm.trans
  calc
    L^(-(D+1))+L^(-(D+1)) = 2*L^(-(D+1)) := by ring
    _ ≤ L*L^(-(D+1)) := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_pos_of_pos hL0 _).le
    _ = L^(-D) := by
      conv_lhs => lhs; rw [← Real.rpow_one L]
      rw [← Real.rpow_add hL0]
      congr 1
      ring

end Bounty


-- Source module: OriginalCellCentralTransfer

/- Remove occupied-cell scale conditions from the original-window central estimate. -/

open Finset Filter
open scoped Classical
namespace Bounty

theorem eventually_original_cell_central_transfer {c bWindow Kdet : ℝ}
    (hc : 0 < c) (hb : 0 < bWindow) (hK : 0 ≤ Kdet) (J : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (groups : Finset ℕ), groups ⊆ candidatePIndices c L →
      let P := fun g : groups => candidatePBand (c*L) g.val
      let mass := fun g => ∑ p ∈ P g, 1/(p : ℝ)
      ∀ (ell : ℕ) (A B : Finset (RepeatedBigFlatIndex groups J ell))
        (hU : ∀ g (i : Fin ell), (⟨g, Sum.inr i⟩ : RepeatedBigFlatIndex groups J ell) ∉ A ∪ B)
        (hAB : Disjoint A B),
      ∀ U V : ℝ, Real.exp (bWindow*L) ≤ U → U ≤ Real.exp L →
        Real.exp (bWindow*L) ≤ V → V ≤ Real.exp L →
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L Kdet : ℤ)) (typeIIAdmissibleDeterminantBound L Kdet : ℤ),
      ∀ j ∈ range (typeIISmoothDyadicCount L),
      ∀ (Q : ℕ) (h : ℝ), 0 < h → h ≤ 1 →
      ∀ (d e : ℤ) (χ ψ : BoundedPrimitiveCharacter Q) (a b v E : ℝ) (F G : ℤ → ℂ),
      let Z := typeIISmoothDyadicScale U V (U*L^(-Kdet)) j
      let Y := Z*harmonicCellProductScale h d e
      let value := ∑ aux : PhysicalAuxLabels P (repeatedBigAuxCut A B),
        physicalPrimeCellAuxCoeff P mass A B hU hAB h d χ e ψ aux *
          physicalPhase (-(a+b+2*Real.pi*v)) (physicalFreeFactor (repeatedBigAuxCut A B) aux) *
          harmonicCellPairing Y Z a b (2*Real.pi*v)
            (k*(physicalFreeFactor (repeatedBigAuxCut A B) aux : ℤ)) F G
      (0 < Z → Real.log Y ≤ 6*L →
        (∀ (x : ∀ i : A, P i.val.1) (y : ∀ i : B, P i.val.1),
          (starRingEnd ℂ) (primeProductCellCharacter (fun i : A => P i.val.1) h d χ x)*
            physicalPhase (-(a+b+2*Real.pi*v)) (∏ i, (x i).val) ≠ 0 →
          (starRingEnd ℂ) (primeProductCellCharacter (fun i : B => P i.val.1) h e ψ y)*
            physicalPhase (-(a+b+2*Real.pi*v)) (∏ i, (y i).val) ≠ 0 →
          Real.exp (2*(bWindow/2)*L) ≤ Z*((((∏ i, (x i).val)*(∏ i, (y i).val)) : ℕ) : ℝ)/2) →
        ‖value‖ ≤ Y*L^(-E)) → ‖value‖ ≤ Y*L^(-E) := by
  filter_upwards [eventually_actual_retained_cell_source_parameters hc hb hK J,
    eventually_gt_atTop (0 : ℝ)] with L hs hL
  intro groups hgroups P mass ell A B hU hAB U V hUlo hUhi hVlo hVhi k hk j hj
    Q h hh hh1 d e χ ψ a b v E F G Z Y value hbound
  have hZ : 0 < Z := typeII_smooth_dyadic_scale_pos
    ((Real.exp_pos _).trans_le hUlo) ((Real.exp_pos _).trans_le hVlo)
    (mul_pos ((Real.exp_pos _).trans_le hUlo) (Real.rpow_pos_of_pos hL _)) j
  have hnonneg : 0 ≤ Y*L^(-E) := mul_nonneg
    (mul_pos hZ (harmonic_cell_product_scale_pos h d e)).le (Real.rpow_pos_of_pos hL _).le
  by_cases hx : ∃ x : (∀ i : A, P i.val.1),
      (starRingEnd ℂ) (primeProductCellCharacter (fun i : A => P i.val.1) h d χ x)*
        physicalPhase (-(a+b+2*Real.pi*v)) (∏ i, (x i).val) ≠ 0
  · by_cases hy : ∃ y : (∀ i : B, P i.val.1),
        (starRingEnd ℂ) (primeProductCellCharacter (fun i : B => P i.val.1) h e ψ y)*
          physicalPhase (-(a+b+2*Real.pi*v)) (∏ i, (y i).val) ≠ 0
    · obtain ⟨x,hx⟩ := hx
      obtain ⟨y,hy⟩ := hy
      have hscale := hs groups hgroups ell A B hU hAB U V hUlo hUhi hVlo hVhi
        k hk j hj Q h hh hh1 d e χ ψ (-(a+b+2*Real.pi*v)) x y hx hy
      apply hbound hZ hscale.2.2.2.1
      intro x y hx hy
      exact (hs groups hgroups ell A B hU hAB U V hUlo hUhi hVlo hVhi
        k hk j hj Q h hh hh1 d e χ ψ (-(a+b+2*Real.pi*v)) x y hx hy).2.1
    · have hz : value = 0 := by
        simpa only [value,physicalPrimeCellAuxCoeff,starRingEnd_apply,mul_assoc] using
          candidate_cell_aux_sum_eq_zero_of_no_right P mass A B hU hAB k Q h d e χ ψ Y Z a b v F G hy
      rw [hz,norm_zero]
      exact hnonneg
  · have hz : value = 0 := by
      simpa only [value,physicalPrimeCellAuxCoeff,starRingEnd_apply,mul_assoc] using
        candidate_cell_aux_sum_eq_zero_of_no_left P mass A B hU hAB k Q h d e χ ψ Y Z a b v F G hx
    rw [hz,norm_zero]
    exact hnonneg

end Bounty


-- Source module: ActualRemainingFactorProperties

/- Uniform unit bounds and prime-pool exclusion for the original remaining factors.
The witnesses are extracted from `exists_actual_selected_source_energy`. -/

open Finset Filter
open scoped ComplexConjugate

namespace Bounty

theorem eventually_actual_remaining_factor_properties {c : ℝ} (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (r jStar : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (θQ : ℕ → ℂ), (∀ n, ‖θQ n‖ ≤ 1) →
      let pool := (candidatePIndices c L).biUnion (candidatePBand (c*L))
      let β := fun n => if n ∈ candidateRoughBand c L jStar then θQ n else 0
      let γ := fun n => conj (candidateResidualPrimeCoefficient c L r jStar hr hj
        take hkeep (candidateAllocationFourierTwist c L r jStar take ξ) n)
      (∀ n, ‖β n‖ ≤ 1) ∧
      (∀ n, ¬ Disjoint n.primeFactors pool → β n = 0) ∧
      (∀ n, ‖γ n‖ ≤ 1) := by
  classical
  filter_upwards [eventually_candidate_P_pool_below_rough_cutoff hc,
    eventually_ge_atTop (0 : ℝ)] with L hpool hL
  intro r jStar hr hj take hkeep ξ θQ hθQ pool β γ
  refine ⟨?_, ?_, ?_⟩
  · intro n
    dsimp only [β]
    split_ifs
    · exact hθQ n
    · simp only [norm_zero, zero_le_one]
  · intro n hn
    have hout : n ∉ candidateRoughBand c L jStar := by
      intro hmem
      exact hn (prime_factors_disjoint_of_rough hpool (mem_filter.mp hmem).2)
    exact if_neg hout
  · intro n
    dsimp only [γ]
    rw [Complex.norm_conj]
    exact norm_candidate_residual_prime_coefficient_le_one (mul_nonneg hc.le hL)
      hr hj take hkeep (candidateAllocationFourierTwist c L r jStar take ξ)
      (fun slot p hp => (candidate_allocation_fourier_twist_norm c L r jStar take ξ slot
        (Nat.pos_of_ne_zero (candidate_Q_slot_nonzero c L r jStar slot hp))).le) n

end Bounty


-- Source module: ActualCandidateSmallWitness

/- A small candidate group remains outside every selection of big groups. -/

open Finset Filter

namespace Bounty

theorem eventually_candidate_small_group_outside_big {c : ℝ} (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      ∀ big : Finset (candidatePIndices c L),
      (∀ g ∈ big, g.val ∈ candidateBigPIndices c L) →
      ∃ g : candidatePIndices c L,
        g.val ∈ candidateSmallPIndices c L ∧ g ∉ big := by
  obtain ⟨v, V, hv, hV, hpool⟩ := exists_candidate_P_pool_bounds hc
  filter_upwards [hpool, eventually_candidate_small_big_indices_disjoint hc,
    eventually_gt_atTop (1 : ℝ)] with L hpoolL hdis hL
  intro big hbig
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcard : 0 < ((candidateSmallPIndices c L).card : ℝ) :=
    (mul_pos (div_pos zero_lt_one (mul_pos (by norm_num) hlog2))
      (Real.log_pos hL)).trans_le hpoolL.2.1
  have hcardNat : 0 < (candidateSmallPIndices c L).card := by exact_mod_cast hcard
  obtain ⟨j, hj⟩ := card_pos.mp hcardNat
  have hjAll : j ∈ candidatePIndices c L := mem_union_left _ hj
  refine ⟨⟨j, hjAll⟩, hj, ?_⟩
  intro hjBig
  exact disjoint_left.mp hdis hj (hbig ⟨j, hjAll⟩ hjBig)

end Bounty


-- Source module: ActualPatternPeelMark

/- The original pattern leaves a positive peel mark outside its selected groups. -/

open Finset

namespace Bounty

theorem actual_pattern_aux_cut_eq_empty
    {G : Type*} [DecidableEq G] {J ell : ℕ}
    (probes : G → Finset (Fin J)) (r t : Finset G)
    (A B : Finset (RepeatedBigFlatIndex G J ell))
    (hA : A ⊆ r.sigma (repeatedBigPrimeProbeSlots probes))
    (hB : B ⊆ t.sigma (repeatedBigPrimeProbeSlots probes))
    (g : G) (hg : g ∉ r ∪ t) :
    repeatedBigAuxCut A B g = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro j hj
  rcases mem_union.mp ((mem_repeatedBigAuxCut A B g j).mp hj) with ha | hb
  · exact hg (mem_union_left _ (mem_sigma.mp (hA ha)).1)
  · exact hg (mem_union_right _ (mem_sigma.mp (hB hb)).1)

theorem actual_pattern_peel_mark
    {G : Type*} [DecidableEq G] {J ell : ℕ}
    (probes : G → Finset (Fin J)) (r t : Finset G)
    (A B : Finset (RepeatedBigFlatIndex G J ell))
    (hA : A ⊆ r.sigma (repeatedBigPrimeProbeSlots probes))
    (hB : B ⊆ t.sigma (repeatedBigPrimeProbeSlots probes))
    (g : G) (hg : g ∉ r ∪ t) (hell : 0 < ell) :
    ell + (repeatedBigAuxCut A B g).card = (ell - 1) + 1 := by
  rw [actual_pattern_aux_cut_eq_empty probes r t A B hA hB g hg, card_empty,
    Nat.add_zero, Nat.sub_add_cancel hell]

end Bounty


-- Source module: ActualPatternBigWitness

/- A nonempty original comparison pattern inherits its selected group property. -/

open Finset

namespace Bounty

theorem actual_pattern_group_witness
    {G : Type*} [DecidableEq G] {J ell : ℕ}
    (probes : G → Finset (Fin J)) (r : Finset G)
    (A : Finset (RepeatedBigFlatIndex G J ell))
    (hA : A ⊆ r.sigma (repeatedBigPrimeProbeSlots probes)) (hAne : A.Nonempty)
    (property : G → Prop) (hproperty : ∀ g ∈ r, property g) :
    ∃ i : A, property i.val.1 := by
  obtain ⟨i, hi⟩ := hAne
  exact ⟨⟨i, hi⟩, hproperty i.1 (mem_sigma.mp (hA hi)).1⟩

end Bounty


-- Source module: ActualPrimeOriginalDecay

/- Original nonempty prime-pattern harmonic decay for the actual prime coefficients. -/

open Finset Filter
open scoped Classical ComplexConjugate
namespace Bounty.WeakZeroFree

theorem exists_actual_prime_original_harmonic_decay
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
  intro jStar hjStar D J ell B C R Kfull Tmod Sshift Cmod Sfreq W hell hB hKfull
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


-- Source module: ActualRoughOriginalDecay

/- Original nonempty prime-pattern harmonic decay for the actual rough coefficients. -/

open Finset Filter
open scoped Classical ComplexConjugate
namespace Bounty.WeakZeroFree

theorem exists_actual_rough_original_harmonic_decay
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
  intro jStar hjStar D J ell B C R Kfull Tmod Sshift Cmod Sfreq W hell hB hKfull
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


namespace Bounty.WeakZeroFree

theorem actual_prime_original_harmonic_decay
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
  exact exists_actual_prime_original_harmonic_decay actual_zero_free hc hb hKdet

theorem actual_rough_original_harmonic_decay
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
  exact exists_actual_rough_original_harmonic_decay actual_zero_free hc hb hKdet hγrough hvMax hρ

end Bounty.WeakZeroFree
