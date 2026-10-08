import WeakUniformWindowDecay

/-! Original raw and block estimates from the actual zero-free theorem, conditional only on the selected central moments. -/

open scoped Topology BigOperators Classical

-- Source module: ActualRawShiftPower

/- Preserve the distinction between determinant precision and the resulting shift exponent. -/

open Finset
namespace Bounty

theorem actual_determinant_shift_power {L K : ℝ} (hL : 3 ≤ L) (hK : 0 ≤ K)
    {k : ℤ} (hk : k ∈ Icc (-(typeIIAdmissibleDeterminantBound L K : ℤ))
      (typeIIAdmissibleDeterminantBound L K : ℤ)) :
    |(k : ℝ)| ≤ L^(K+89) := by
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hk' : |(k : ℝ)| ≤ (typeIIAdmissibleDeterminantBound L K : ℝ) := by
    apply abs_le.mpr
    obtain ⟨hklo, hkhi⟩ := mem_Icc.mp hk
    constructor
    · exact_mod_cast hklo
    · exact_mod_cast hkhi
  calc
    _ ≤ 3*L^(K+88) := hk'.trans (determinant_bound_le_three_rpow_public hL1 hK)
    _ ≤ L*L^(K+88) := mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hL0.le _)
    _ = L^(K+89) := by
      calc
        L*L^(K+88) = L^(1 : ℝ)*L^(K+88) := by rw [Real.rpow_one]
        _ = L^((1 : ℝ)+(K+88)) := (Real.rpow_add hL0 _ _).symm
        _ = L^(K+89) := by congr 1; ring

end Bounty


-- Source module: PhysicalDExponentialBound

/- Exponential bounds for physical dilation products and their finite maxima. -/

open Finset
namespace Bounty

theorem physical_D_le_exp {G : Type*} [Fintype G] [DecidableEq G]
    {P : G → Finset ℕ} {J ell : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hP : ∀ g p, p ∈ P g → (p : ℝ) ≤ Real.exp B)
    (C : G → Finset (Fin J)) (labels : PhysicalMarkLists P J ell)
    (aux : PhysicalAuxLabels P C) :
    (physicalD C labels aux : ℝ) ≤
      Real.exp ((Fintype.card G : ℝ) * (2 * J) * B) := by
  classical
  have hprod (S : Finset (Fin J)) (f : S → ℕ)
      (hf : ∀ i, (f i : ℝ) ≤ Real.exp B) :
      ((∏ i, f i : ℕ) : ℝ) ≤ Real.exp ((J : ℝ) * B) := by
    calc
      _ = ∏ i : S, (f i : ℝ) := by simp only [Nat.cast_prod]
      _ ≤ ∏ _i : S, Real.exp B :=
        prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => hf i)
      _ = Real.exp ((S.card : ℝ) * B) := by
        rw [← Real.exp_sum]
        simp only [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]
      _ ≤ Real.exp ((J : ℝ) * B) := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_right _ hB
        exact_mod_cast (show S.card ≤ J by simpa using card_le_univ S)
  have hg (g : G) : (physicalGroupD C labels aux g : ℝ) ≤
      Real.exp ((2 * J : ℝ) * B) := by
    have hleft := hprod (univ \ C g) (fun j => (labels g (Sum.inl j.val)).val)
      (fun j => hP g _ (labels g (Sum.inl j.val)).property)
    rw [Finset.prod_coe_sort (univ \ C g) (fun j => (labels g (Sum.inl j)).val)] at hleft
    have hright := hprod (C g) (fun j => (aux g j).val)
      (fun j => hP g _ (aux g j).property)
    calc
      _ ≤ Real.exp ((J : ℝ)*B) * Real.exp ((J : ℝ)*B) := by
        unfold physicalGroupD
        rw [Nat.cast_mul]
        exact mul_le_mul hleft hright (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ = ∏ g, (physicalGroupD C labels aux g : ℝ) := by
      simp only [physicalD, Nat.cast_prod]
    _ ≤ ∏ _g : G, Real.exp ((2 * J : ℝ) * B) :=
      prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun g _ => hg g)
    _ = _ := by
      rw [← Real.exp_sum]
      simp only [sum_const, card_univ, nsmul_eq_mul]
      congr 1
      ring

theorem physical_D_max_le_exp {G : Type*} [Fintype G] [DecidableEq G]
    {P : G → Finset ℕ} {J ell : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hP : ∀ g p, p ∈ P g → (p : ℝ) ≤ Real.exp B)
    (C : G → Finset (Fin J)) :
    (physicalDMax P J ell C : ℝ) ≤
      Real.exp ((Fintype.card G : ℝ) * (2 * J) * B) := by
  classical
  rw [physicalDMax, ← Nat.le_floor_iff (Real.exp_pos _).le]
  apply Finset.sup_le
  intro a _
  exact Nat.le_floor (physical_D_le_exp hB hP C a.1 a.2)

end Bounty


-- Source module: ScaledLogPower

/- A fixed logarithmic cost fits inside any larger power. -/

open Filter
namespace Bounty

theorem eventually_scaled_log_power {A s t ε : ℝ}
    (hA : 0 ≤ A) (hst : s < t) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, A*L^s*Real.log L ≤ ε*L^t := by
  have hsmall := ((isLittleO_log_rpow_atTop (sub_pos.mpr hst)).const_mul_left A).bound hε
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with L hb hL
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hn : A*Real.log L ≤ ε*L^(t-s) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hA (Real.log_nonneg hL)),
      abs_of_nonneg (Real.rpow_nonneg hL0.le (t-s))] using hb
  calc
    _ = L^s*(A*Real.log L) := by ring
    _ ≤ L^s*(ε*L^(t-s)) :=
      mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg hL0.le s)
    _ = ε*(L^s*L^(t-s)) := by ring
    _ = ε*L^t := by rw [← Real.rpow_add hL0]; congr 2; ring

end Bounty


-- Source module: CandidateStepSublinear

/- The dilation range of candidate pools is subexponential, uniformly in cuts. -/

open Finset Filter
namespace Bounty

theorem eventually_candidate_D_max_le_exp_power {c ε t : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (ht : (2/5 : ℝ) < t) (J : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (S : Finset ℕ), S ⊆ candidatePIndices c L →
      ∀ (ell : ℕ) (C : S → Finset (Fin J)),
      (physicalDMax (fun g : S => candidatePBand (c*L) g.val) J ell C : ℝ) ≤
        Real.exp (ε*L^t) := by
  obtain ⟨v, W, _, _, hpool⟩ := exists_candidate_P_pool_bounds hc
  let D : ℝ := (2 * J) * (2/(5*Real.log 2))
  filter_upwards [hpool, eventually_scaled_log_power
    (A := D) (by dsimp [D]; positivity) (s := (2/5 : ℝ)) ht hε]
    with L hp hscaled
  intro S hS ell C
  have hL : 0 ≤ L := zero_le_one.trans hp.1
  have hScard : (S.card : ℝ) ≤ (2/(5*Real.log 2))*Real.log L :=
    (Nat.cast_le.mpr (card_le_card hS)).trans hp.2.2.2.1
  have hlabels (g : S) (p : ℕ) (hpm : p ∈ candidatePBand (c*L) g.val) :
      (p : ℝ) ≤ Real.exp (L^(2/5 : ℝ)) :=
    ((hp.2.2.2.2.2 g.val (hS g.property)).2.2 p hpm).2.2
  calc
    _ ≤ Real.exp ((S.card : ℝ) * (2 * J) * L^(2/5 : ℝ)) := by
      simpa only [Fintype.card_coe] using physical_D_max_le_exp
        (J := J) (ell := ell) (Real.rpow_nonneg (zero_le_one.trans hp.1) _) hlabels C
    _ ≤ Real.exp (D * L^(2/5 : ℝ) * Real.log L) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right hScard
        (show 0 ≤ (2 * J : ℝ) * L^(2/5 : ℝ) by positivity)
      dsimp [D]
      nlinarith
    _ ≤ _ := Real.exp_le_exp.mpr hscaled

end Bounty


-- Source module: PolynomialPowerExponential

/- Any positive power exponential absorbs a fixed polynomial. -/

open Filter
namespace Bounty

theorem eventually_rpow_le_exp_power (K : ℝ) {t ε : ℝ}
    (ht : 0 < t) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, L^K ≤ Real.exp (ε*L^t) := by
  filter_upwards [eventually_scaled_log_power (A := max K 0)
    (le_max_right _ _) (s := 0) ht hε,
    eventually_ge_atTop (1 : ℝ)] with L hscale hL
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  simp only [Real.rpow_zero, mul_one] at hscale
  rw [Real.rpow_def_of_pos hL0]
  apply Real.exp_le_exp.mpr
  calc
    Real.log L*K = K*Real.log L := mul_comm _ _
    _ ≤ max K 0*Real.log L :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.log_nonneg hL)
    _ ≤ ε*L^t := hscale

end Bounty


-- Source module: CandidatePositiveStepPower

/- A positive displacement bound with a sublinear logarithm. -/

open Finset Filter
namespace Bounty

theorem eventually_candidate_positive_step_power {c t ε : ℝ}
    (hc : 0 < c) (ht : (2/5 : ℝ) < t) (hε : 0 < ε) (J : ℕ) (K : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (S : Finset ℕ), S ⊆ candidatePIndices c L →
      ∀ (ell : ℕ) {I : Type} (patterns : Finset I)
        (C : I → S → Finset (Fin J)) (k : I → ℤ),
        (∀ i ∈ patterns, |(k i : ℝ)| ≤ L^K) →
          ((max 1 (physicalOperatorStepBound
            (fun g : S => candidatePBand (c*L) g.val) J ell patterns C k) : ℕ) : ℝ)
            ≤ Real.exp (ε*L^t) := by
  have hε2 : 0 < ε/2 := by positivity
  have ht0 : 0 < t := by linarith
  filter_upwards [eventually_candidate_D_max_le_exp_power hc hε2 ht J,
    eventually_rpow_le_exp_power K ht0 hε2,
    eventually_ge_atTop (1 : ℝ)] with L hD hpoly hL
  intro S hS ell I patterns C k hk
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  rw [Nat.cast_max, Nat.cast_one]
  apply max_le
  · exact Real.one_le_exp_iff.mpr (mul_nonneg hε.le (Real.rpow_nonneg hL0 _))
  · rw [← Nat.le_floor_iff (Real.exp_pos _).le]
    apply Finset.sup_le
    intro i hi
    apply Nat.le_floor
    unfold physicalStepBound
    rw [Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs]
    calc
      _ ≤ Real.exp (ε/2*L^t) * Real.exp (ε/2*L^t) :=
        mul_le_mul ((hk i hi).trans hpoly) (hD S hS ell (C i))
          (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Bounty


-- Source module: PolynomialSqrtRadius

/- Polynomial lengths times a square-root exponential fit in a linear exponential. -/

open Filter
namespace Bounty

theorem eventually_polynomial_sqrt_radius (M : ℝ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ L : ℝ in atTop,
      L^M * Real.exp (Real.sqrt L) ≤ Real.exp (b*L)/8 := by
  filter_upwards [eventually_exp_neg_rpow_mul_rpow_mul_exp_sqrt_le
    (b := (1 : ℝ)) (by norm_num) hb (show (0 : ℝ) ≤ 1 by norm_num) M 1,
    eventually_ge_atTop (8 : ℝ)] with L hd hL
  simp only [Real.rpow_one, one_mul, Real.rpow_neg_one] at hd
  have hinv : L⁻¹ ≤ (8 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hL
  have hdiv : (L^M * Real.exp (Real.sqrt L)) / Real.exp (b*L) ≤ (8 : ℝ)⁻¹ := by
    simpa only [neg_mul, mul_neg, Real.exp_neg, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
      using hd.trans hinv
  have h := (div_le_iff₀ (Real.exp_pos (b*L))).mp hdiv
  simpa only [div_eq_mul_inv, mul_comm] using h

end Bounty


-- Source module: CandidatePositiveGraphRadius

/- The positive step bound needed by the block inequality obeys the same localization scale. -/

open Finset Filter
namespace Bounty

theorem eventually_candidate_positive_graph_radius {c b : ℝ}
    (hc : 0 < c) (hb : 0 < b) (J : ℕ) (K M : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (S : Finset ℕ), S ⊆ candidatePIndices c L →
      ∀ (ell : ℕ) {I : Type} (patterns : Finset I)
        (C : I → S → Finset (Fin J)) (k : I → ℤ),
        (∀ i ∈ patterns, |(k i : ℝ)| ≤ L^K) →
        ∀ N : ℕ, (N : ℝ) ≤ L^M →
          ((N * max 1 (physicalOperatorStepBound
            (fun g : S => candidatePBand (c*L) g.val) J ell patterns C k) : ℕ) : ℝ)
            ≤ Real.exp (b*L)/8 := by
  filter_upwards [eventually_candidate_positive_step_power hc
    (t := (1/2 : ℝ)) (by norm_num) (show (0 : ℝ) < 1 by norm_num) J K,
    eventually_polynomial_sqrt_radius M hb,
    eventually_ge_atTop (1 : ℝ)] with L hs hr hL
  intro S hS ell I patterns C k hk N hN
  have hstep := hs S hS ell patterns C k hk
  rw [one_mul, ← Real.sqrt_eq_rpow] at hstep
  calc
    _ ≤ L^M * Real.exp (Real.sqrt L) := by
      rw [Nat.cast_mul]
      exact mul_le_mul hN hstep (Nat.cast_nonneg _)
        (Real.rpow_nonneg (zero_le_one.trans hL) _)
    _ ≤ _ := hr

end Bounty


-- Source module: PositiveDyadicGraphRadius

/- The chosen moment length localizes the positive physical displacement bound. -/

open Finset Filter
namespace Bounty

theorem eventually_candidate_positive_dyadic_radius {c b : ℝ}
    (hc : 0 < c) (hb : 0 < b) (J : ℕ) (K : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (S : Finset ℕ), S ⊆ candidatePIndices c L →
      ∀ (ell : ℕ) {I : Type} (patterns : Finset I)
        (C : I → S → Finset (Fin J)) (k : I → ℤ),
        (∀ i ∈ patterns, |(k i : ℝ)| ≤ L^K) →
        ∀ Z : ℝ, Real.exp (b*L) ≤ Z →
          (((2 * ⌈L^(13/25 : ℝ)⌉₊) * max 1 (physicalOperatorStepBound
            (fun g : S => candidatePBand (c*L) g.val) J ell patterns C k) : ℕ) : ℝ)
            ≤ Z/8 := by
  filter_upwards [eventually_candidate_positive_graph_radius hc hb J K 1,
    eventually_repeated_big_visit_density_le (alpha := (13/25 : ℝ))
      (tau := 1) (by norm_num) (by norm_num)] with L hradius hlength
  intro S hS ell I patterns C k hk Z hZ
  have hN : (((2 * ⌈L^(13/25 : ℝ)⌉₊ : ℕ) : ℝ)) ≤ L^((1 : ℝ)) := by
    apply hlength
    push_cast
    linarith
  exact (hradius S hS ell patterns C k hk _ hN).trans
    (div_le_div_of_nonneg_right hZ (by norm_num))

theorem eventually_raw_moment_at_least_two :
    ∀ᶠ L : ℝ in atTop, 2 ≤ ⌈L^(13/25 : ℝ)⌉₊ := by
  filter_upwards [(tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 13/25)).eventually_ge_atTop 2]
    with L hL
  exact_mod_cast hL.trans (Nat.le_ceil (L^(13/25 : ℝ)))

end Bounty


-- Source module: PhysicalPoolSharedScale

/- Shared-prime stripping for every pool containing the original prime groups. -/

open Finset
namespace Bounty

theorem positive_invariant_endpoint_shared_scale_of_pool
    {G : Type*} [Fintype G] [DecidableEq G] {P : G → Finset ℕ} {J ell : ℕ}
    (C : G → Finset (Fin J)) (hprime : ∀ g p, p ∈ P g → p.Prime)
    (pool : Finset ℕ) (hpool : ∀ g, P g ⊆ pool)
    (α β γ : ℕ → ℂ) (L : PhysicalMarkLists P J ell) (w : ℤ) :
    positiveInvariantEndpoint pool α β γ ((physicalSharedFactor C L : ℤ) * w) =
      positiveInvariantEndpoint pool α β γ w := by
  have hs : 0 < (physicalSharedFactor C L : ℤ) := by
    exact_mod_cast physical_shared_factor_pos C L hprime
  have hm : physicalSharedFactor C L ∈ Nat.factoredNumbers pool :=
    Nat.factoredNumbers_mono (by
      intro p hp
      obtain ⟨g, _, hp⟩ := mem_biUnion.mp hp
      exact hpool g hp) (physical_shared_factor_supported C L hprime)
  have he : invariantTripleEndpoint pool α β γ
      ((physicalSharedFactor C L : ℤ) * w).natAbs =
      invariantTripleEndpoint pool α β γ w.natAbs := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using
      invariant_triple_endpoint_mul_supported hm α β γ w.natAbs
  simp only [positiveInvariantEndpoint, mul_pos_iff_of_pos_left hs, he]

end Bounty


-- Source module: PhysicalPoolPositiveRoot

/- The original positive harmonic root on its literal dyadic support. -/

open Finset
open scoped Classical
namespace Bounty

theorem physical_prime_positive_harmonic_root_of_pool
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ) (probes : G → Finset (Fin J))
    (r t : Finset G) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (i : RepeatedBigPrimePatternIndex (ell := ell) probes r t)
    (aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t i))
    (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))
    (hprime : ∀ g p, p ∈ P g → p.Prime)
    (pool : Finset ℕ) (hpool : ∀ g, P g ⊆ pool)
    (q a b : ℝ) (k : ℤ) (positions : Finset ℤ)
    (α₀ β₀ γ₀ α₁ β₁ γ₁ : ℕ → ℂ) {Z : ℝ} (hZ : 0 < Z)
    (hclosure : physicalFixedAuxPositionClosure P
      (repeatedBigPrimePatternCut probes r t i) ell k aux
      (harmonicPositiveSupport Z k (physicalFreeFactor (repeatedBigPrimePatternCut probes r t i) aux)) ⊆ positions) :
    physicalFixedRootCorrelation V (repeatedBigPrimePatternCut probes r t i) q (-(a+b)) k
      (physicalRootPrimeKernel P V probes r t hrt Q h ξ i) aux positions
      (fun n => physicalPhase (-a) n.natAbs *
        positiveInvariantEndpoint pool α₀ β₀ γ₀ n)
      (fun n => physicalPhase b n.natAbs *
        positiveInvariantEndpoint pool α₁ β₁ γ₁ n)
      (fun x => (typeIIHarmonicDyadic x : ℂ)) Z =
    (physicalAuxMass V (repeatedBigPrimePatternCut probes r t i) aux : ℂ) *
      ∑ w ∈ harmonicPositiveSupport Z k (physicalFreeFactor (repeatedBigPrimePatternCut probes r t i) aux),
        ((typeIIHarmonicDyadic ((w : ℝ) /
          (Z * physicalFreeFactor (repeatedBigPrimePatternCut probes r t i) aux)) : ℂ) *
          (w : ℂ)⁻¹ *
          (starRingEnd ℂ) (invariantTripleEndpoint pool α₀ β₀ γ₀ w.natAbs) *
          invariantTripleEndpoint pool α₁ β₁ γ₁
            (w + k * (physicalFreeFactor (repeatedBigPrimePatternCut probes r t i) aux : ℕ)).natAbs) *
        physicalFullPairCorrelation P (repeatedBigPrimePatternCut probes r t i) V q w.natAbs
          (w + k * (physicalFreeFactor (repeatedBigPrimePatternCut probes r t i) aux : ℕ)).natAbs
          (physicalOriginalPrimePairCoefficient P V probes r t hrt Q h ξ i aux a b w.natAbs
            (w + k * (physicalFreeFactor (repeatedBigPrimePatternCut probes r t i) aux : ℕ)).natAbs) := by
  have hd : 0 < physicalFreeFactor (repeatedBigPrimePatternCut probes r t i) aux :=
    prod_pos (fun g _ => prod_pos (fun j _ => (hprime g _ (aux g j).property).pos))
  have hbase := physical_fixed_root_full_pair_on_fixed_support hdis hprime V
    (repeatedBigPrimePatternCut probes r t i) q a b k
    (physicalRootPrimeKernel P V probes r t hrt Q h ξ i) aux positions
    (harmonicPositiveSupport Z k (physicalFreeFactor (repeatedBigPrimePatternCut probes r t i) aux)) hclosure
    (positiveInvariantEndpoint pool α₀ β₀ γ₀) (positiveInvariantEndpoint pool α₁ β₁ γ₁)
    (fun x => (typeIIHarmonicDyadic x : ℂ)) Z
    (positive_invariant_endpoint_shared_scale_of_pool _ hprime pool hpool α₀ β₀ γ₀)
    (positive_invariant_endpoint_shared_scale_of_pool _ hprime pool hpool α₁ β₁ γ₁)
    (original_harmonic_test_support pool α₀ β₀ γ₀ α₁ β₁ γ₁ hZ k hd)
  apply Eq.trans hbase
  congr 1
  apply sum_congr rfl
  intro w hw
  have hs := mem_harmonic_positive_support hw
  rw [positiveInvariantEndpoint, if_pos hs.1,
    positiveInvariantEndpoint, if_pos hs.2.2.2]
  rfl

end Bounty


-- Source module: PhysicalHarmonicResidual

/- The literal signed full-pair harmonic residual. Pattern weights already
occur inside the original coefficient and are not multiplied in again. -/

open Finset
open scoped Classical
namespace Bounty

section
variable {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ) (probes : G → Finset (Fin J))
    (r t : Finset G) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (a b Z : ℝ) (k : ℤ) (pool : Finset ℕ) (α β γ α' β' γ' : ℕ → ℂ)

noncomputable def physicalSignedPositiveHarmonicResidual : ℂ :=
  ∑ i : RepeatedBigPrimePatternIndex (ell := ell) probes r t,
    ∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t i),
      let cut := repeatedBigPrimePatternCut probes r t i
      let d := physicalFreeFactor cut aux
      let δ : ℤ := k*(d : ℤ)
      (physicalAuxMass V cut aux : ℂ) *
        ∑ n ∈ harmonicPositiveSupport Z k d,
          ((typeIIHarmonicDyadic ((n : ℝ)/(Z*(d : ℝ))) : ℂ)/(n : ℂ)) *
            star (invariantTripleEndpoint pool α β γ n.natAbs) *
            invariantTripleEndpoint pool α' β' γ' (n+δ).natAbs *
            physicalFullPairCorrelation P cut V (1/2) n.natAbs (n+δ).natAbs
              (physicalOriginalPrimePairCoefficient P V probes r t hrt Q h ξ i aux a b
                n.natAbs (n+δ).natAbs)

theorem physical_harmonic_residual_decomposition :
    physicalSignedPositiveHarmonicResidual (ell := ell) P V probes r t hrt Q h ξ a b Z k pool α β γ α' β' γ' =
      (∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut (ell := ell) probes r t (.inl ())),
        (physicalAuxMass V (repeatedBigPrimePatternCut (ell := ell) probes r t (.inl ())) aux : ℂ) *
          physicalFreePositiveHarmonicMain P V probes r t hrt Q h ξ (.inl ()) aux a b Z k pool α β γ α' β' γ') +
      (∑ ab : RepeatedBigPrimePatternPair (ell := ell) probes r t,
      ∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut (ell := ell) probes r t (.inr ab)),
        (physicalAuxMass V (repeatedBigPrimePatternCut (ell := ell) probes r t (.inr ab)) aux : ℂ) *
          physicalFreePositiveHarmonicMain P V probes r t hrt Q h ξ (.inr ab) aux a b Z k pool α β γ α' β' γ') +
      (∑ i : RepeatedBigPrimePatternIndex (ell := ell) probes r t,
      ∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut (ell := ell) probes r t i),
        (physicalAuxMass V (repeatedBigPrimePatternCut (ell := ell) probes r t i) aux : ℂ) *
          physicalPositiveHarmonicDifference P V probes r t hrt Q h ξ i aux a b Z k pool α β γ α' β' γ') := by
  unfold physicalSignedPositiveHarmonicResidual
  calc
    _ = (∑ i : RepeatedBigPrimePatternIndex (ell := ell) probes r t,
      ∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut (ell := ell) probes r t i),
        (physicalAuxMass V (repeatedBigPrimePatternCut (ell := ell) probes r t i) aux : ℂ) *
          physicalFreePositiveHarmonicMain P V probes r t hrt Q h ξ i aux a b Z k pool α β γ α' β' γ') + (∑ i : RepeatedBigPrimePatternIndex (ell := ell) probes r t,
      ∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut (ell := ell) probes r t i),
        (physicalAuxMass V (repeatedBigPrimePatternCut (ell := ell) probes r t i) aux : ℂ) *
          physicalPositiveHarmonicDifference P V probes r t hrt Q h ξ i aux a b Z k pool α β γ α' β' γ') := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro i _
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro aux _
      rw [physical_positive_harmonic_difference_eq_main]
      dsimp only
      ring
    _ = _ := by
      congr 1
      rw [Fintype.sum_sum_type]
      simp only [Fintype.sum_unique]

end
end Bounty


-- Source module: PhysicalSignedRootIdentity

/- The complete signed harmonic residual is a single physical root pairing. -/

open Finset
open scoped Classical
namespace Bounty

section
variable {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ) (probes : G → Finset (Fin J))
    (r t : Finset G) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (a b Z : ℝ) (k : ℤ) (pool : Finset ℕ) (α β γ α' β' γ' : ℕ → ℂ)

noncomputable def physicalSignedHarmonicPositions : Finset ℤ :=
  univ.biUnion (fun i : RepeatedBigPrimePatternIndex (ell := ell) probes r t =>
    univ.biUnion (fun aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t i) =>
      physicalFixedAuxPositionClosure P (repeatedBigPrimePatternCut probes r t i) ell k aux
        (harmonicPositiveSupport Z k (physicalFreeFactor (repeatedBigPrimePatternCut probes r t i) aux))))

theorem physical_signed_harmonic_position_coverage
    (i : RepeatedBigPrimePatternIndex (ell := ell) probes r t)
    (aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t i)) :
    physicalFixedAuxPositionClosure P (repeatedBigPrimePatternCut probes r t i) ell k aux
      (harmonicPositiveSupport Z k (physicalFreeFactor (repeatedBigPrimePatternCut probes r t i) aux)) ⊆
      physicalSignedHarmonicPositions (ell := ell) P probes r t Z k := by
  intro n hn
  exact mem_biUnion.mpr ⟨i, mem_univ _, mem_biUnion.mpr ⟨aux, mem_univ _, hn⟩⟩

theorem physical_signed_harmonic_residual_eq_root
    (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))
    (hprime : ∀ g p, p ∈ P g → p.Prime) (hpool : ∀ g, P g ⊆ pool) (hZ : 0 < Z)
    (positions : Finset ℤ)
    (hclosure : physicalSignedHarmonicPositions (ell := ell) P probes r t Z k ⊆ positions) :
    physicalSignedPositiveHarmonicResidual (ell := ell) P V probes r t hrt Q h ξ a b Z k pool α β γ α' β' γ' =
      physicalMellinRootCorrelation V (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
        (repeatedBigPrimePatternCut probes r t) (1/2) (fun _ => -(a+b)) (fun _ => k)
        (physicalRootPrimeKernel P V probes r t hrt Q h ξ) positions
        (fun n => physicalPhase (-a) n.natAbs * positiveInvariantEndpoint pool α β γ n)
        (fun n => physicalPhase b n.natAbs * positiveInvariantEndpoint pool α' β' γ' n)
        (fun x => (typeIIHarmonicDyadic x : ℂ)) Z := by
  rw [physical_mellin_root_sum_fixed]
  unfold physicalSignedPositiveHarmonicResidual
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro aux _
  rw [physical_prime_positive_harmonic_root_of_pool P V probes r t hrt Q h ξ i aux
    hdis hprime pool hpool (1/2) a b k positions α β γ α' β' γ' hZ
    ((physical_signed_harmonic_position_coverage P probes r t Z k i aux).trans hclosure)]
  simp only [div_eq_mul_inv, starRingEnd_apply]

end
end Bounty


-- Source module: PhysicalSignedPositionBounds

/- The canonical physical positions and every associated source dyad stay above the harmonic scale. -/

open Finset
open scoped Classical
namespace Bounty

theorem physical_fixed_aux_closure_lower
    {G : Type*} [Fintype G] [DecidableEq G] {P : G → Finset ℕ} {J ell : ℕ}
    (C : G → Finset (Fin J)) (aux : PhysicalAuxLabels P C)
    (hprime : ∀ g p, p ∈ P g → p.Prime) {Z : ℝ} (hZ : 0 < Z) (k : ℤ)
    (hk : |(k : ℝ)| ≤ Z/4) {n : ℤ}
    (hn : n ∈ physicalFixedAuxPositionClosure P C ell k aux
      (harmonicPositiveSupport Z k (physicalFreeFactor C aux))) : Z/4 < (n : ℝ) := by
  obtain ⟨L, _, hn⟩ := mem_biUnion.mp hn
  have hs : (1 : ℝ) ≤ physicalSharedFactor C L := by
    exact_mod_cast physical_shared_factor_pos C L hprime
  have hdN : 0 < physicalFreeFactor C aux :=
    prod_pos (fun g _ => prod_pos (fun j _ => (hprime g _ (aux g j).property).pos))
  have hd : (1 : ℝ) ≤ physicalFreeFactor C aux := by exact_mod_cast hdN
  have hmul (x : ℝ) (hx : Z/4 < x) : Z/4 < (physicalSharedFactor C L : ℝ)*x := by
    have hx0 : 0 ≤ x := le_of_lt ((by positivity : 0 < Z/4).trans hx)
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) hx0]
  rcases mem_union.mp hn with hn | hn
  · obtain ⟨w, hw, rfl⟩ := mem_image.mp hn
    have hw' := mem_harmonic_positive_support hw
    push_cast
    apply hmul
    nlinarith [mul_nonneg hZ.le (sub_nonneg.mpr hd)]
  · obtain ⟨w, hw, rfl⟩ := mem_image.mp hn
    have hw' := mem_harmonic_positive_support hw
    have hklo := (abs_le.mp hk).1
    have hkm := mul_le_mul_of_nonneg_right hklo (Nat.cast_nonneg (physicalFreeFactor C aux))
    push_cast
    apply hmul
    nlinarith [mul_nonneg hZ.le (sub_nonneg.mpr hd)]

theorem physical_signed_harmonic_positions_lower
    {G : Type*} [Fintype G] [DecidableEq G] {P : G → Finset ℕ} {J ell : ℕ}
    (probes : G → Finset (Fin J)) (r t : Finset G)
    (hprime : ∀ g p, p ∈ P g → p.Prime) {Z : ℝ} (hZ : 0 < Z) (k : ℤ)
    (hk : |(k : ℝ)| ≤ Z/4) {n : ℤ}
    (hn : n ∈ physicalSignedHarmonicPositions (ell := ell) P probes r t Z k) :
    Z/4 < (n : ℝ) := by
  obtain ⟨i, _, hn⟩ := mem_biUnion.mp hn
  obtain ⟨aux, _, hn⟩ := mem_biUnion.mp hn
  exact physical_fixed_aux_closure_lower (ell := ell)
    (repeatedBigPrimePatternCut probes r t i) aux hprime hZ k hk hn

theorem physical_signed_harmonic_dyadic_lower
    {G : Type*} [Fintype G] [DecidableEq G] {P : G → Finset ℕ} {J ell : ℕ}
    (probes : G → Finset (Fin J)) (r t : Finset G)
    (hprime : ∀ g p, p ∈ P g → p.Prime) {Z : ℝ} (hZ : 0 < Z) (k : ℤ)
    (hk : |(k : ℝ)| ≤ Z/4) {j : ℕ}
    (hj : j ∈ (physicalSignedHarmonicPositions (ell := ell) P probes r t Z k).image
      (fun n => n.natAbs.log2)) : Z/8 < (2 : ℝ)^j := by
  obtain ⟨n, hn, hj⟩ := mem_image.mp hj
  have hl := physical_signed_harmonic_positions_lower probes r t hprime hZ k hk hn
  have hn0 : 0 < n := by exact_mod_cast ((by positivity : (0 : ℝ) < Z/4).trans hl)
  have hb := (Nat.log2_eq_iff (Int.natAbs_ne_zero.mpr (ne_of_gt hn0))).mp hj
  have he : (n.natAbs : ℤ) = n := by rw [Int.natCast_natAbs, abs_of_pos hn0]
  have he' : (n.natAbs : ℝ) = n := by
    calc
      (n.natAbs : ℝ) = ((n.natAbs : ℤ) : ℝ) := by simp
      _ = (n : ℝ) := congrArg (fun z : ℤ => (z : ℝ)) he
  have hb' : (n.natAbs : ℝ) < (2 : ℝ)^(j+1) := by exact_mod_cast hb.2
  rw [he', pow_succ] at hb'
  linarith

theorem physical_signed_harmonic_dyadic_radius
    {G : Type*} [Fintype G] [DecidableEq G] {P : G → Finset ℕ} {J ell : ℕ}
    (probes : G → Finset (Fin J)) (r t : Finset G)
    (hprime : ∀ g p, p ∈ P g → p.Prime) {Z : ℝ} (hZ : 0 < Z) (k : ℤ)
    (hk : |(k : ℝ)| ≤ Z/4) {j radius : ℕ} (hr : (radius : ℝ) ≤ Z/8)
    (hj : j ∈ (physicalSignedHarmonicPositions (ell := ell) P probes r t Z k).image
      (fun n => n.natAbs.log2)) : radius ≤ 2^j := by
  exact_mod_cast (hr.trans_lt (physical_signed_harmonic_dyadic_lower probes r t hprime hZ k hk hj)).le

end Bounty


-- Source module: PhysicalPositionUpper

/- Upper bounds for the complete source and target position closure. -/

open Finset
open scoped Classical
namespace Bounty

theorem physical_fixed_aux_closure_upper
    {G : Type*} [Fintype G] [DecidableEq G] {P : G → Finset ℕ} {J ell : ℕ}
    (C : G → Finset (Fin J)) (aux : PhysicalAuxLabels P C)
    {Z : ℝ} (hZ : 0 ≤ Z) (k : ℤ) (hk : |(k : ℝ)| ≤ Z) {n : ℤ}
    (hn : n ∈ physicalFixedAuxPositionClosure P C ell k aux
      (harmonicPositiveSupport Z k (physicalFreeFactor C aux))) :
    (n : ℝ) ≤ 3*Z*(physicalDMax P J ell C : ℝ) := by
  obtain ⟨L, _, hn⟩ := mem_biUnion.mp hn
  have hmax : (physicalD C L aux : ℝ) ≤ physicalDMax P J ell C :=
    Nat.cast_le.mpr (physical_D_le_max P J ell C L aux)
  have htop : 3*Z*(physicalD C L aux : ℝ) ≤ 3*Z*(physicalDMax P J ell C : ℝ) :=
    mul_le_mul_of_nonneg_left hmax (by positivity)
  rw [physical_D_shared_free, Nat.cast_mul] at htop
  have hs : (0 : ℝ) ≤ physicalSharedFactor C L := Nat.cast_nonneg _
  have hd : (0 : ℝ) ≤ physicalFreeFactor C aux := Nat.cast_nonneg _
  rcases mem_union.mp hn with hn | hn
  · obtain ⟨w, hw, rfl⟩ := mem_image.mp hn
    have hw' := (mem_harmonic_positive_support hw).2.2.1
    push_cast
    calc
      _ ≤ (physicalSharedFactor C L : ℝ)*(2*Z*(physicalFreeFactor C aux : ℝ)) :=
        mul_le_mul_of_nonneg_left hw' hs
      _ ≤ 3*Z*((physicalSharedFactor C L : ℝ)*(physicalFreeFactor C aux : ℝ)) := by
        nlinarith [mul_nonneg hZ (mul_nonneg hs hd)]
      _ ≤ _ := htop
  · obtain ⟨w, hw, rfl⟩ := mem_image.mp hn
    have hw' := (mem_harmonic_positive_support hw).2.2.1
    have hk' := mul_le_mul_of_nonneg_right ((le_abs_self (k : ℝ)).trans hk) hd
    push_cast
    calc
      _ ≤ (physicalSharedFactor C L : ℝ)*(3*Z*(physicalFreeFactor C aux : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hs
        linarith
      _ = 3*Z*((physicalSharedFactor C L : ℝ)*(physicalFreeFactor C aux : ℝ)) := by ring
      _ ≤ _ := htop

theorem physical_signed_harmonic_positions_upper
    {G : Type*} [Fintype G] [DecidableEq G] {P : G → Finset ℕ} {J ell : ℕ}
    (probes : G → Finset (Fin J)) (r t : Finset G)
    {Z H : ℝ} (hZ : 0 ≤ Z) (k : ℤ) (hk : |(k : ℝ)| ≤ Z)
    (hD : ∀ i : RepeatedBigPrimePatternIndex (ell := ell) probes r t,
      (physicalDMax P J ell (repeatedBigPrimePatternCut probes r t i) : ℝ) ≤ H)
    {n : ℤ} (hn : n ∈ physicalSignedHarmonicPositions (ell := ell) P probes r t Z k) :
    (n : ℝ) ≤ 3*Z*H := by
  obtain ⟨i, _, hn⟩ := mem_biUnion.mp hn
  obtain ⟨aux, _, hn⟩ := mem_biUnion.mp hn
  exact (physical_fixed_aux_closure_upper (repeatedBigPrimePatternCut probes r t i)
    aux hZ k hk hn).trans (mul_le_mul_of_nonneg_left (hD i) (by positivity))

end Bounty


-- Source module: CandidateDExponentialBound

/- The dilation range of candidate pools is subexponential, uniformly in cuts. -/

open Finset Filter
namespace Bounty

theorem eventually_candidate_D_max_le_exp {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (J : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (S : Finset ℕ), S ⊆ candidatePIndices c L →
      ∀ (ell : ℕ) (C : S → Finset (Fin J)),
      (physicalDMax (fun g : S => candidatePBand (c*L) g.val) J ell C : ℝ) ≤
        Real.exp (ε*L) := by
  obtain ⟨v, W, _, _, hpool⟩ := exists_candidate_P_pool_bounds hc
  let D : ℝ := (2 * J) * (2/(5*Real.log 2))
  filter_upwards [hpool, eventually_scaled_log_sublinear
    (A := D) (by dsimp [D]; positivity) (s := (2/5 : ℝ)) (by norm_num) hε]
    with L hp hscaled
  intro S hS ell C
  have hL : 0 ≤ L := zero_le_one.trans hp.1
  have hScard : (S.card : ℝ) ≤ (2/(5*Real.log 2))*Real.log L :=
    (Nat.cast_le.mpr (card_le_card hS)).trans hp.2.2.2.1
  have hlabels (g : S) (p : ℕ) (hpm : p ∈ candidatePBand (c*L) g.val) :
      (p : ℝ) ≤ Real.exp (L^(2/5 : ℝ)) :=
    ((hp.2.2.2.2.2 g.val (hS g.property)).2.2 p hpm).2.2
  calc
    _ ≤ Real.exp ((S.card : ℝ) * (2 * J) * L^(2/5 : ℝ)) := by
      simpa only [Fintype.card_coe] using physical_D_max_le_exp
        (J := J) (ell := ell) (Real.rpow_nonneg (zero_le_one.trans hp.1) _) hlabels C
    _ ≤ Real.exp (D * L^(2/5 : ℝ) * Real.log L) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right hScard
        (show 0 ≤ (2 * J : ℝ) * L^(2/5 : ℝ) by positivity)
      dsimp [D]
      nlinarith
    _ ≤ _ := Real.exp_le_exp.mpr hscaled

end Bounty


-- Source module: CandidatePositionUpper

/- The candidate position closure is contained in a fixed exponential interval. -/

open Finset Filter
namespace Bounty

theorem eventually_candidate_harmonic_positions_upper {c : ℝ} (hc : 0 < c)
    (J : ℕ) (a : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (S : Finset ℕ), S ⊆ candidatePIndices c L →
      ∀ (ell : ℕ) (probes : S → Finset (Fin J)) (r t : Finset S)
        (Z : ℝ) (k : ℤ), 0 ≤ Z → Z ≤ Real.exp (a*L) → |(k : ℝ)| ≤ Z →
        ∀ n ∈ physicalSignedHarmonicPositions (ell := ell)
          (fun g : S => candidatePBand (c*L) g.val) probes r t Z k,
          (n : ℝ) ≤ Real.exp ((a+2)*L) := by
  filter_upwards [eventually_candidate_D_max_le_exp hc
    (show (0 : ℝ) < 1 by norm_num) J,
    eventually_ge_atTop (Real.log (3 : ℝ))] with L hd hL
  intro S hS ell probes r t Z k hZ hZhi hk n hn
  have h3 : (3 : ℝ) ≤ Real.exp L := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_le_exp.mpr hL
  have hbound := physical_signed_harmonic_positions_upper probes r t hZ k hk
    (fun i => hd S hS ell (repeatedBigPrimePatternCut probes r t i)) hn
  rw [one_mul] at hbound
  calc
    (n : ℝ) ≤ 3*Z*Real.exp L := hbound
    _ ≤ Real.exp L * Real.exp (a*L) * Real.exp L := by gcongr
    _ = Real.exp ((a+2)*L) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Bounty


-- Source module: ActualPositionBounds

/- Canonical positions for the original harmonic windows are positive and exponentially bounded. -/

open Finset Filter
namespace Bounty

theorem eventually_actual_harmonic_positions_bounds {c b K : ℝ}
    (hc : 0 < c) (hb : 0 < b) (hK : 0 ≤ K) (J : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (S : Finset ℕ), S ⊆ candidatePIndices c L →
      ∀ (ell : ℕ) (probes : S → Finset (Fin J)) (r t : Finset S),
      ∀ U V : ℝ, Real.exp (b*L) ≤ U → U ≤ Real.exp L →
        Real.exp (b*L) ≤ V → V ≤ Real.exp L →
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L K : ℤ))
        (typeIIAdmissibleDeterminantBound L K : ℤ),
      ∀ j ∈ range (typeIISmoothDyadicCount L),
      ∀ n ∈ physicalSignedHarmonicPositions (ell := ell)
        (fun g : S => candidatePBand (c*L) g.val) probes r t
        (typeIISmoothDyadicScale U V (U*L^(-K)) j) k,
        0 < n ∧ (n : ℝ) ≤ Real.exp (6*L) := by
  filter_upwards [eventually_candidate_harmonic_positions_upper hc J 4,
    eventually_actual_harmonic_scale_inputs hb hK,
    eventually_typeII_original_harmonic_shift_small hb hK] with L hupper hscale hshift
  intro S hS ell probes r t U V hUlo hUhi hVlo hVhi k hk j hj n hn
  obtain ⟨hZ, _, hkZ, hZhi⟩ := hscale U V hUlo hUhi hVlo hVhi k hk j hj
  have hkquarter := hshift U V hUlo hUhi hVlo hVhi k hk j hj
  have hprime (g : S) (p : ℕ) (hp : p ∈ candidatePBand (c*L) g.val) : p.Prime :=
    ((mem_dyadicPrimeBand_iff (c*L) (3/2) (9/5) g.val p).mp hp).1
  have hlower := physical_signed_harmonic_positions_lower probes r t hprime hZ k hkquarter hn
  refine ⟨?_, ?_⟩
  · have hpos : (0 : ℝ) < n := lt_trans (div_pos hZ (by norm_num)) hlower
    exact_mod_cast hpos
  · have hu := hupper S hS ell probes r t _ k hZ.le (by linarith) hkZ n hn
    norm_num only [show (4 : ℝ)+2=6 by norm_num] at hu
    exact hu

end Bounty


-- Source module: ActualRawDyadicRadius

/- The original determinant and harmonic windows supply the literal raw moment radius. -/

open Finset Filter
open scoped Classical
namespace Bounty

theorem eventually_actual_raw_dyadic_radius {c b K : ℝ}
    (hc : 0 < c) (hb : 0 < b) (hK : 0 ≤ K) (J : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (S : Finset ℕ), S ⊆ candidatePIndices c L →
      ∀ (ell : ℕ) (probes : S → Finset (Fin J)) (r t : Finset S),
      ∀ U V : ℝ, Real.exp (b*L) ≤ U → U ≤ Real.exp L →
        Real.exp (b*L) ≤ V → V ≤ Real.exp L →
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L K : ℤ))
        (typeIIAdmissibleDeterminantBound L K : ℤ),
      ∀ j ∈ range (typeIISmoothDyadicCount L),
      let P := fun g : S => candidatePBand (c*L) g.val
      let Z := typeIISmoothDyadicScale U V (U*L^(-K)) j
      let D := max 1 (physicalOperatorStepBound P J ell
        (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
        (repeatedBigPrimePatternCut probes r t) (fun _ => k))
      ∀ i ∈ (physicalSignedHarmonicPositions (ell := ell) P probes r t Z k).image
        (fun n => n.natAbs.log2), 2*⌈L^(13/25 : ℝ)⌉₊*D ≤ 2^i := by
  filter_upwards [eventually_candidate_positive_dyadic_radius hc hb J (K+89),
    eventually_typeII_harmonic_scale_lower hb hK,
    eventually_typeII_original_harmonic_shift_small hb hK,
    eventually_ge_atTop (3 : ℝ)] with L hradius hlower hshift hL
  intro S hS ell probes r t U V hUlo hUhi hVlo hVhi k hk j hj
  dsimp only
  intro i hi
  have hlow := hlower U V hUlo hVlo j
  have hZ : 0 < typeIISmoothDyadicScale U V (U*L^(-K)) j := by
    have hp := Real.exp_pos (b*L)
    linarith
  have hzexp : Real.exp (b*L) ≤ typeIISmoothDyadicScale U V (U*L^(-K)) j := by
    have hp := Real.exp_pos (b*L)
    linarith
  have hprime (g : S) (p : ℕ) (hp : p ∈ candidatePBand (c*L) g.val) : p.Prime :=
    ((mem_dyadicPrimeBand_iff (c*L) (3/2) (9/5) g.val p).mp hp).1
  have hrad := hradius S hS ell
    (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
    (repeatedBigPrimePatternCut probes r t) (fun _ => k)
    (fun _ _ => actual_determinant_shift_power hL hK hk) _ hzexp
  exact physical_signed_harmonic_dyadic_radius probes r t hprime hZ k
    (hshift U V hUlo hUhi hVlo hVhi k hk j hj) hrad hi

end Bounty


-- Source module: CandidateBlockMoment

/- The block supremum cost is uniformly bounded at the chosen moment order. -/

open Finset Filter
namespace Bounty

theorem eventually_candidate_block_moment {c C₀ : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C₀) (J : ℕ) (K : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (S : Finset ℕ), S ⊆ candidatePIndices c L →
      ∀ (ell : ℕ) {I : Type} (patterns : Finset I)
        (C : I → S → Finset (Fin J)) (k : I → ℤ),
        (∀ i ∈ patterns, |(k i : ℝ)| ≤ L^K) →
          (((max 1 (physicalOperatorStepBound
            (fun g : S => candidatePBand (c*L) g.val) J ell patterns C k) : ℕ) : ℝ)
            * Real.exp (C₀ * Real.sqrt L)^2)^
              (1/(2*(Nat.ceil (L^(13/25 : ℝ)) : ℝ))) ≤ Real.exp 1 := by
  filter_upwards [eventually_candidate_positive_step_power hc
    (t := (1/2 : ℝ)) (by norm_num) (show (0 : ℝ) < 1 by norm_num) J K,
    eventually_block_sup_moment_bound (a := (13/25 : ℝ)) (d := (1/2 : ℝ))
      (by norm_num) (by norm_num) hC 1,
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop (1 : ℝ)] with L hs hm hlog hL
  intro S hS ell I patterns C k hk
  let D := max 1 (physicalOperatorStepBound
    (fun g : S => candidatePBand (c*L) g.val) J ell patterns C k)
  have hD : (0 : ℝ) < D := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _) : 0 < D)
  apply hm D hD
  have hstep := hs S hS ell patterns C k hk
  rw [one_mul] at hstep
  have hlogD : Real.log D ≤ L^(1/2 : ℝ) := by
    exact (Real.log_le_iff_le_exp hD).mpr hstep
  calc
    Real.log D ≤ L^(1/2 : ℝ) := hlogD
    _ ≤ 1 * L^(1/2 : ℝ) * Real.log L := by
      rw [one_mul]
      exact le_mul_of_one_le_right (Real.rpow_nonneg (zero_le_one.trans hL) _) hlog

end Bounty


-- Source module: ActualRawBlockCost

/- The original determinant range supplies a bounded block cost at the actual moment order. -/

open Finset Filter
namespace Bounty

theorem eventually_actual_raw_block_cost {c K : ℝ}
    (hc : 0 < c) (hK : 0 ≤ K) (J : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (S : Finset ℕ), S ⊆ candidatePIndices c L →
      ∀ (ell : ℕ) (probes : S → Finset (Fin J)) (r t : Finset S),
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L K : ℤ))
        (typeIIAdmissibleDeterminantBound L K : ℤ),
      let D := max 1 (physicalOperatorStepBound
        (fun g : S => candidatePBand (c*L) g.val) J ell
        (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
        (repeatedBigPrimePatternCut probes r t) (fun _ => k))
      ((D : ℝ)*Real.exp ((14*Real.log 2)*Real.sqrt L)^2)^
        (1/(2*(Nat.ceil (L^(13/25 : ℝ)) : ℝ))) ≤ Real.exp 1 := by
  have hC : (0 : ℝ) ≤ 14*Real.log 2 :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))
  filter_upwards [eventually_candidate_block_moment hc hC J (K+89),
    eventually_ge_atTop (3 : ℝ)] with L hblock hL
  intro S hS ell probes r t k hk
  exact hblock S hS ell
    (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
    (repeatedBigPrimePatternCut probes r t) (fun _ => k)
    (fun _ _ => actual_determinant_shift_power hL hK hk)

end Bounty


-- Source module: FinitePairingCutoff

/- Move a finitely supported pairing to any cutoff containing its active edges. -/

open Finset
open scoped ComplexConjugate
namespace Bounty

theorem finite_pairing_cutoff_mask {X : Type*} [DecidableEq X]
    (S T : Finset X) (f g : X → ℂ) (K : X → X → ℂ)
    (hsource : ∀ x ∈ S, f x ≠ 0 → x ∈ T)
    (hedge : ∀ x ∈ S, f x ≠ 0 → ∀ y ∈ S, K x y ≠ 0 → y ∈ T) :
    (∑ x ∈ S, ∑ y ∈ S, star (f x) * K x y * g y) =
      ∑ x ∈ T, ∑ y ∈ T,
        star (if x ∈ S then f x else 0) * K x y * (if y ∈ S then g y else 0) := by
  have hleft : (∑ x ∈ S, ∑ y ∈ S, star (f x) * K x y * g y) =
      ∑ x ∈ S ∩ T, ∑ y ∈ S ∩ T, star (f x) * K x y * g y := by
    calc
      _ = ∑ x ∈ S ∩ T, ∑ y ∈ S, star (f x) * K x y * g y := by
        symm
        apply sum_subset inter_subset_left
        intro x hx hxt
        have hf : f x = 0 := by
          by_contra hn
          exact hxt (mem_inter.mpr ⟨hx, hsource x hx hn⟩)
        simp [hf]
      _ = _ := by
        apply sum_congr rfl
        intro x hx
        symm
        apply sum_subset inter_subset_left
        intro y hy hyt
        by_cases hf : f x = 0
        · simp [hf]
        · have hk : K x y = 0 := by
            by_contra hn
            exact hyt (mem_inter.mpr ⟨hy, hedge x (mem_inter.mp hx).1 hf y hy hn⟩)
          simp [hk]
  rw [hleft]
  symm
  calc
    _ = ∑ x ∈ S ∩ T, ∑ y ∈ T,
        star (if x ∈ S then f x else 0) * K x y * (if y ∈ S then g y else 0) := by
      symm
      apply sum_subset inter_subset_right
      intro x hx hxt
      have hs : x ∉ S := fun hs => hxt (mem_inter.mpr ⟨hs, hx⟩)
      simp [hs]
    _ = _ := by
      apply sum_congr rfl
      intro x hx
      simp only [if_pos (mem_inter.mp hx).1]
      calc
        _ = ∑ y ∈ S ∩ T, star (f x) * K x y * (if y ∈ S then g y else 0) := by
          symm
          apply sum_subset inter_subset_right
          intro y hy hyt
          have hs : y ∉ S := fun hs => hyt (mem_inter.mpr ⟨hs, hy⟩)
          simp [hs]
        _ = _ := by
          apply sum_congr rfl
          intro y hy
          rw [if_pos (mem_inter.mp hy).1]

end Bounty


-- Source module: PhysicalPairingCutoff

/- Exact restriction of a physical endpoint pairing to a reachable position set. -/

open Finset
open scoped Classical InnerProductSpace
namespace Bounty

noncomputable def physicalPositionMask (S : Finset ℤ) (f : ℤ → ℂ) (n : ℤ) : ℂ :=
  if n ∈ S then f n else 0

theorem physical_unsym_operator_zero_of_far
    {G I : Type*} [Fintype G] [DecidableEq G] {P : G → Finset ℕ} {J ell : ℕ}
    (V : G → ℝ) (patterns : Finset I) (C : I → G → Finset (Fin J))
    (q : ℝ) (ζ : I → ℝ) (k : I → ℤ)
    (K : ∀ i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell → PhysicalAuxLabels P (C i) → ℂ)
    (x y : PhysicalState P J ell)
    (hfar : physicalOperatorStepBound P J ell patterns C k < (y.1 - x.1).natAbs) :
    (∑ i ∈ patterns, physicalPatternKernel V (C i) q (ζ i) (k i) (K i) x y) = 0 := by
  apply sum_eq_zero
  intro i hi
  unfold physicalPatternKernel
  apply sum_eq_zero
  intro aux _
  exact physical_edge_zero_of_far V (C i) q (ζ i) (k i) (K i) aux x y
    ((le_sup (f := fun i => physicalStepBound P J ell (C i) (k i)) hi).trans_lt hfar)

theorem physical_endpoint_pairing_cutoff
    {G I : Type*} [Fintype G] [DecidableEq G] {P : G → Finset ℕ} {J ell : ℕ}
    (V : G → ℝ) (hV : ∀ g, 0 < V g)
    (patterns : Finset I) (C : I → G → Finset (Fin J)) (q : ℝ)
    (ζ : I → ℝ) (k : I → ℤ)
    (K : ∀ i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell → PhysicalAuxLabels P (C i) → ℂ)
    (positions starts : Finset ℤ) (radius : ℕ)
    (hstep : physicalOperatorStepBound P J ell patterns C k ≤ radius)
    (f g : ℤ → ℂ) (hf : ∀ n ∈ positions, f n ≠ 0 → n ∈ starts) :
    inner ℂ (physicalEndpointVector P V J ell q positions f)
      (physicalHilbertOperator V patterns C q ζ k K positions
        (physicalEndpointVector P V J ell q positions g)) =
      inner ℂ (physicalEndpointVector P V J ell q (reachablePositions starts radius)
        (physicalPositionMask positions f))
        (physicalHilbertOperator V patterns C q ζ k K (reachablePositions starts radius)
          (physicalEndpointVector P V J ell q (reachablePositions starts radius)
            (physicalPositionMask positions g))) := by
  simp only [physicalEndpointVector, physicalHilbertOperator]
  rw [physical_position_kernel_pairing P V hV, physical_position_kernel_pairing P V hV]
  congr 1
  let F := fun x : PhysicalState P J ell => f x.1 * (physicalDamping P J ell q x.1 : ℂ)
  let Gf := fun x : PhysicalState P J ell => g x.1 * (physicalDamping P J ell q x.1 : ℂ)
  let A := fun x y : PhysicalState P J ell =>
    ∑ i ∈ patterns, physicalPatternKernel V (C i) q (ζ i) (k i) (K i) x y
  have hs : ∀ x ∈ physicalCutoff P J ell positions, F x ≠ 0 →
      x ∈ physicalCutoff P J ell (reachablePositions starts radius) := by
    intro x hx hfx
    apply (mem_physical_cutoff _ _ _ _ _).mpr
    apply mem_reachable_positions_self _ radius
    apply hf x.1 ((mem_physical_cutoff _ _ _ _ _).mp hx)
    intro hz
    exact hfx (by simp [F, hz])
  have he : ∀ x ∈ physicalCutoff P J ell positions, F x ≠ 0 →
      ∀ y ∈ physicalCutoff P J ell positions, A x y ≠ 0 →
        y ∈ physicalCutoff P J ell (reachablePositions starts radius) := by
    intro x hx hfx y _ hxy
    apply (mem_physical_cutoff _ _ _ _ _).mpr
    apply mem_reachable_positions (hf x.1 ((mem_physical_cutoff _ _ _ _ _).mp hx) (by
      intro hz
      exact hfx (by simp [F, hz])))
    apply le_trans _ hstep
    by_contra hn
    exact hxy (physical_unsym_operator_zero_of_far V patterns C q ζ k K x y (lt_of_not_ge hn))
  simpa only [F, Gf, A, starRingEnd_apply, physicalPositionMask, mem_physical_cutoff,
    ite_mul, zero_mul] using
    finite_pairing_cutoff_mask (physicalCutoff P J ell positions)
      (physicalCutoff P J ell (reachablePositions starts radius)) F Gf A hs he

end Bounty


-- Source module: PhysicalDyadicRoot

/- Exact partition of the physical source variable into dyadic blocks. -/

open Finset
open scoped Classical
namespace Bounty

noncomputable def physicalDyadicSource (j : ℕ) (f : ℤ → ℂ) (n : ℤ) : ℂ :=
  if n.natAbs.log2 = j then f n else 0

theorem physical_dyadic_source_nonzero (j : ℕ) (f : ℤ → ℂ) {n : ℤ}
    (hn : physicalDyadicSource j f n ≠ 0) : f n ≠ 0 ∧ n.natAbs.log2 = j := by
  by_cases h : n.natAbs.log2 = j
  · exact ⟨by simpa only [physicalDyadicSource, if_pos h] using hn, h⟩
  · exact False.elim (hn (if_neg h))

theorem physical_dyadic_source_scale (j : ℕ) (f : ℤ → ℂ)
    (hf : ∀ n, f n ≠ 0 → 0 < n) {n : ℤ}
    (hn : physicalDyadicSource j f n ≠ 0) :
    (2 : ℝ)^j ≤ (n : ℝ) ∧ (n : ℝ) < 2*(2 : ℝ)^j := by
  obtain ⟨hnf, hnj⟩ := physical_dyadic_source_nonzero j f hn
  have hp := hf n hnf
  have hpn : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (ne_of_gt hp)
  have hb := (Nat.log2_eq_iff hpn).mp hnj
  have he : (n.natAbs : ℤ) = n := by simp only [Int.natCast_natAbs, abs_of_pos hp]
  have he' : (n.natAbs : ℝ) = n := by
    calc
      (n.natAbs : ℝ) = ((n.natAbs : ℤ) : ℝ) := by simp
      _ = (n : ℝ) := congrArg (fun z : ℤ => (z : ℝ)) he
  rw [pow_succ] at hb
  constructor
  · have hr : (2 : ℝ)^j ≤ n.natAbs := by exact_mod_cast hb.1
    simpa only [he'] using hr
  · have hr : (n.natAbs : ℝ) < (2 : ℝ)^j*2 := by exact_mod_cast hb.2
    simpa only [he', mul_comm] using hr

theorem physical_mellin_root_dyadic_sum
    {G I : Type*} [Fintype G] [DecidableEq G] {P : G → Finset ℕ} {J ell : ℕ}
    (V : G → ℝ) (patterns : Finset I) (C : I → G → Finset (Fin J))
    (q : ℝ) (ζ : I → ℝ) (k : I → ℤ)
    (K : ∀ i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell → PhysicalAuxLabels P (C i) → ℂ)
    (positions : Finset ℤ) (f g : ℤ → ℂ) (Ψ : ℝ → ℂ) (Z : ℝ) :
    (∑ j ∈ positions.image (fun n => n.natAbs.log2),
      physicalMellinRootCorrelation V patterns C q ζ k K positions
        (physicalDyadicSource j f) g Ψ Z) =
      physicalMellinRootCorrelation V patterns C q ζ k K positions f g Ψ Z := by
  simp only [physical_mellin_root_as_atoms, ← mul_sum]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  rw [← sum_mul]
  congr 1
  have hm : a.1.val.1.natAbs.log2 ∈ positions.image (fun n => n.natAbs.log2) :=
    mem_image_of_mem _ ((mem_physical_cutoff P J ell positions a.1.val).mp a.1.property)
  calc
    _ = ∑ j ∈ positions.image (fun n => n.natAbs.log2),
        if a.1.val.1.natAbs.log2 = j then
          physicalMellinAtomCoefficient V patterns C q ζ k K positions f g a else 0 := by
      apply sum_congr rfl
      intro j _
      unfold physicalMellinAtomCoefficient
      by_cases hj : a.1.val.1.natAbs.log2 = j <;>
        simp [physicalDyadicSource, hj]
    _ = _ := by simp [hm]

end Bounty


-- Source module: PhysicalDyadicPairingCutoff

/- Localize each actual Mellin source block, with both original endpoint masks retained. -/

open Finset
open scoped Classical
namespace Bounty

def physicalDyadicStarts (j : ℕ) : Finset ℤ := Ico ((2 : ℤ)^j) ((2 : ℤ)^(j+1))

theorem physical_dyadic_source_mem_starts (j : ℕ) (f : ℤ → ℂ)
    (hf : ∀ n, f n ≠ 0 → 0 < n) {n : ℤ}
    (hn : physicalDyadicSource j f n ≠ 0) : n ∈ physicalDyadicStarts j := by
  have hb := physical_dyadic_source_scale j f hf hn
  rw [mul_comm, ← pow_succ] at hb
  apply mem_Ico.mpr
  exact_mod_cast hb

theorem physical_position_mask_mellin (S : Finset ℤ) (X Z v : ℝ) (f : ℤ → ℂ) :
    physicalPositionMask S (physicalMellinSource X Z v f) =
      physicalMellinSource X Z v (physicalPositionMask S f) := by
  funext n
  by_cases hn : n ∈ S <;> simp [physicalPositionMask, physicalMellinSource, hn]

theorem physical_dyadic_mellin_pairing_cutoff
    {G I : Type*} [Fintype G] [DecidableEq G] {P : G → Finset ℕ} {J ell : ℕ}
    (V : G → ℝ) (hV : ∀ g, 0 < V g)
    (patterns : Finset I) (C : I → G → Finset (Fin J)) (q : ℝ)
    (ζ : I → ℝ) (k : I → ℤ)
    (K : ∀ i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell → PhysicalAuxLabels P (C i) → ℂ)
    (positions : Finset ℤ) (radius j : ℕ)
    (hstep : physicalOperatorStepBound P J ell patterns C k ≤ radius)
    (f g : ℤ → ℂ) (hf : ∀ n, f n ≠ 0 → 0 < n) (X Z v : ℝ) :
    physicalMellinPairing V patterns C q ζ k K positions (physicalDyadicSource j f) g X Z v =
      physicalMellinPairing V patterns C q ζ k K
        (reachablePositions (physicalDyadicStarts j) radius)
        (physicalPositionMask positions (physicalDyadicSource j f))
        (physicalPositionMask positions g) X Z v := by
  unfold physicalMellinPairing
  rw [← physical_position_mask_mellin]
  apply physical_endpoint_pairing_cutoff V hV patterns C q (fun i => ζ i - v) k K
    positions (physicalDyadicStarts j) radius hstep
  intro n _ hn
  apply physical_dyadic_source_mem_starts j f hf
  intro hz
  exact hn (physical_mellin_source_zero X Z v _ n hz)

theorem physical_position_mask_endpoint_norm_le
    {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (V : G → ℝ) (hV : ∀ g, 0 < V g) (J ell : ℕ)
    {q : ℝ} (hq : 0 ≤ q) (S T : Finset ℤ) (f : ℤ → ℂ) :
    ‖physicalEndpointVector P V J ell q T (physicalPositionMask S f)‖ ≤
      ‖physicalEndpointVector P V J ell q S f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [physical_endpoint_vector_norm_sq P V hV J ell hq,
    physical_endpoint_vector_norm_sq P V hV J ell hq]
  calc
    _ = ∑ n ∈ T.filter (fun n => n ∈ S),
        uniformMarkedDivisorWeight univ P q V (J+ell) n * ‖f n‖^2 := by
      rw [sum_filter]
      apply sum_congr rfl
      intro n _
      by_cases hn : n ∈ S <;> simp [physicalPositionMask, hn]
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg (fun n hn => (mem_filter.mp hn).2)
      intro n _ _
      apply mul_nonneg _ (sq_nonneg _)
      exact marked_divisor_weight_nonneg univ P hq V (fun _ => J+ell)
        (fun g _ => (hV g).le) n

theorem physical_position_mask_endpoint_norm_same_le
    {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (V : G → ℝ) (hV : ∀ g, 0 < V g) (J ell : ℕ)
    {q : ℝ} (hq : 0 ≤ q) (S T : Finset ℤ) (f : ℤ → ℂ) :
    ‖physicalEndpointVector P V J ell q T (physicalPositionMask S f)‖ ≤
      ‖physicalEndpointVector P V J ell q T f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [physical_endpoint_vector_norm_sq P V hV J ell hq,
    physical_endpoint_vector_norm_sq P V hV J ell hq]
  apply sum_le_sum
  intro n _
  apply mul_le_mul_of_nonneg_left _
    (marked_divisor_weight_nonneg univ P hq V (fun _ => J+ell) (fun g _ => (hV g).le) n)
  by_cases hn : n ∈ S
  · simp only [physicalPositionMask, if_pos hn, le_refl]
  · simp only [physicalPositionMask, if_neg hn, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    positivity

end Bounty


-- Source module: PhysicalDyadicNeighborhood

/- Integer geometry of the reachable neighborhood of one physical source dyad. -/

open Finset
namespace Bounty

theorem physical_reachable_dyadic_bounds (j radius : ℕ) {n : ℤ}
    (hn : n ∈ reachablePositions (physicalDyadicStarts j) radius) :
    (2 : ℤ)^j - radius ≤ n ∧ n < (2 : ℤ)^(j+1) + radius := by
  obtain ⟨m, hm, hn⟩ := mem_biUnion.mp hn
  have hm' := mem_Ico.mp hm
  have hn' := mem_Icc.mp hn
  omega

theorem physical_reachable_dyadic_range (j radius : ℕ) (hr : radius ≤ 2^j) :
    ∀ n ∈ reachablePositions (physicalDyadicStarts j) radius,
      0 ≤ n ∧ n ≤ ((2^(j+1) + radius : ℕ) : ℤ) := by
  intro n hn
  have hb := physical_reachable_dyadic_bounds j radius hn
  have hr' : (radius : ℤ) ≤ (2 : ℤ)^j := by exact_mod_cast hr
  have he : ((2^(j+1)+radius : ℕ) : ℤ) = (2 : ℤ)^(j+1)+radius := by push_cast; rfl
  rw [he]
  omega

end Bounty


-- Source module: PhysicalRawEndpointPointwise

/- The actual phases, source dyad, and cutoff masks contract the invariant endpoints. -/

open Finset
open scoped Classical
namespace Bounty

theorem physical_phase_positive_endpoint_norm_le
    (pool : Finset ℕ) (α β γ : ℕ → ℂ) (a : ℝ) (n : ℤ) :
    ‖physicalPhase a n.natAbs * positiveInvariantEndpoint pool α β γ n‖ ≤
      ‖invariantTripleEndpoint pool α β γ n.natAbs‖ := by
  rw [norm_mul, physical_phase_norm, one_mul]
  by_cases hn : 0 < n <;> simp [positiveInvariantEndpoint, hn]

theorem physical_masked_phase_endpoint_norm_le
    (S : Finset ℤ) (pool : Finset ℕ) (α β γ : ℕ → ℂ) (a : ℝ) (n : ℤ) :
    ‖physicalPositionMask S
      (fun n => physicalPhase a n.natAbs * positiveInvariantEndpoint pool α β γ n) n‖ ≤
      ‖invariantTripleEndpoint pool α β γ n.natAbs‖ := by
  by_cases hn : n ∈ S
  · simpa only [physicalPositionMask, if_pos hn] using
      physical_phase_positive_endpoint_norm_le pool α β γ a n
  · simp only [physicalPositionMask, if_neg hn, norm_zero, norm_nonneg]

theorem physical_masked_dyadic_mellin_endpoint_norm_le
    (S : Finset ℤ) (pool : Finset ℕ) (α β γ : ℕ → ℂ) (a Z v : ℝ) (j : ℕ) (n : ℤ) :
    ‖physicalMellinSource ((2 : ℝ)^j) Z v
      (physicalPositionMask S (physicalDyadicSource j
        (fun n => physicalPhase a n.natAbs * positiveInvariantEndpoint pool α β γ n))) n‖ ≤
      ‖invariantTripleEndpoint pool α β γ n.natAbs‖ := by
  let f := fun n : ℤ => physicalPhase a n.natAbs * positiveInvariantEndpoint pool α β γ n
  let F := physicalPositionMask S (physicalDyadicSource j f)
  change ‖physicalMellinSource ((2 : ℝ)^j) Z v F n‖ ≤ _
  have hnorm : ‖F n‖ ≤ ‖invariantTripleEndpoint pool α β γ n.natAbs‖ := by
    by_cases hn : n ∈ S
    · by_cases hj : n.natAbs.log2 = j
      · simpa only [F, physicalPositionMask, if_pos hn, physicalDyadicSource, if_pos hj, f] using
          physical_phase_positive_endpoint_norm_le pool α β γ a n
      · simp only [F, physicalPositionMask, if_pos hn, physicalDyadicSource, if_neg hj, norm_zero, norm_nonneg]
    · simp only [F, physicalPositionMask, if_neg hn, norm_zero, norm_nonneg]
  by_cases hn : F n = 0
  · rw [physical_mellin_source_zero _ _ _ _ _ hn, norm_zero]
    exact norm_nonneg _
  · have hd : physicalDyadicSource j f n ≠ 0 := by
      intro hz
      exact hn (by simp [F, physicalPositionMask, hz])
    have hp : ∀ n, f n ≠ 0 → 0 < n := by
      intro n hn
      apply positive_invariant_endpoint_nonzero pool α β γ
      intro hz
      exact hn (by simp [f, hz])
    have hb := (physical_dyadic_source_scale j f hp hd).1
    have hx : (0 : ℝ) < 2^j := by positivity
    have hnpos : (0 : ℝ) < n := hx.trans_le hb
    rw [physical_mellin_source_norm, abs_of_nonneg (div_nonneg hx.le hnpos.le)]
    exact (mul_le_of_le_one_left (norm_nonneg _) ((div_le_one hnpos).mpr hb)).trans hnorm

end Bounty


-- Source module: PhysicalDyadicSourceSupport

/- Exact support and cardinality of the original physical dyadic source. -/

open Finset
open scoped Classical
namespace Bounty

theorem physical_dyadic_starts_card (j : ℕ) : (physicalDyadicStarts j).card = 2^j := by
  simp only [physicalDyadicStarts, Int.card_Ico, pow_succ]
  rw [show (2 : ℤ)^j*2 - 2^j = 2^j by ring]
  norm_cast

theorem physical_raw_dyadic_source_support (S : Finset ℤ)
    (pool : Finset ℕ) (α β γ : ℕ → ℂ) (a Z v : ℝ) (j : ℕ) {n : ℤ}
    (hn : n ∉ physicalDyadicStarts j) :
    physicalMellinSource ((2 : ℝ)^j) Z v
      (physicalPositionMask S (physicalDyadicSource j
        (fun n => physicalPhase a n.natAbs * positiveInvariantEndpoint pool α β γ n))) n = 0 := by
  apply physical_mellin_source_zero
  by_cases hS : n ∈ S
  · rw [physicalPositionMask, if_pos hS]
    by_contra hne
    apply hn
    apply physical_dyadic_source_mem_starts j _ _ hne
    intro m hm
    apply positive_invariant_endpoint_nonzero pool α β γ
    intro hz
    exact hm (by rw [hz, mul_zero])
  · simp only [physicalPositionMask, if_neg hS]

end Bounty


-- Source module: PhysicalAlternatingMomentNonneg

/- Positivity of the literal alternating physical root moment. -/

open Finset
open scoped BigOperators InnerProductSpace
namespace Bounty

theorem physical_alternating_root_moment_nonneg
    {G I : Type*} [Fintype G] [DecidableEq G] {P : G → Finset ℕ} {J ell : ℕ}
    (V : G → ℝ) (hV : ∀ g, 0 < V g) (patterns : Finset I)
    (C : I → G → Finset (Fin J)) (q : ℝ) (ζ : I → ℝ) (k : I → ℤ)
    (K : ∀ i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell → PhysicalAuxLabels P (C i) → ℂ)
    (starts : Finset ℤ) (R b : ℕ) (hR : 0 < R) :
    0 ≤ (physicalRootMoment V patterns C q
      (fun j i => if j % 2 = 0 then -ζ i else ζ i)
      (fun j i => if j % 2 = 0 then -k i else k i)
      (fun j i a c aux => if j % 2 = 0 then (starRingEnd ℂ) (K i c a aux) else K i a c aux)
      starts (2*R-1) b).re := by
  rw [physical_root_moment_re_eq_fiber_gram V hV patterns C q ζ k K starts R b hR]
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply sum_nonneg
  intro n _
  apply positive_spectral_moment_nonneg _ (LinearMap.isSymmetric_self_comp_adjoint _)
  intro v
  rw [LinearMap.comp_apply, ← LinearMap.adjoint_inner_left]
  exact inner_self_nonneg (𝕜 := ℂ)

end Bounty


-- Source module: PhysicalRawEndpointNorm

/- Raw physical endpoint norms with an absolute logarithmic exponent, uniform in mark counts. -/

open Finset
open scoped Classical
namespace Bounty

section
variable {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (hP : Pairwise (fun g h => Disjoint (P g) (P h)))
    (hprime : ∀ g p, p ∈ P g → p.Prime)
    (V : G → ℝ) (hV : ∀ g, 0 < V g) (hMass : ∀ g, ∑ p ∈ P g, 1/(p : ℝ) = V g)
    (pool : Finset ℕ) (hpool : ∀ g, P g ⊆ pool) (α β γ : ℕ → ℂ)
    {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hα : ∀ m, ‖α m‖ ≤ A) (hβ : ∀ p, ‖β p‖ ≤ B) (hγ : ∀ r, ‖γ r‖ ≤ C)
    (J ell : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (S : Finset ℤ) (j radius : ℕ) (hr : radius ≤ 2^j) (a Z v : ℝ)

include hP hprime hV hMass hpool hA hB hC hα hβ hγ hq0 hq1 hr

theorem physical_raw_mellin_source_endpoint_norm :
    ‖physicalEndpointVector P V J ell q (reachablePositions (physicalDyadicStarts j) radius)
      (physicalMellinSource ((2 : ℝ)^j) Z v
        (physicalPositionMask S (physicalDyadicSource j
          (fun n => physicalPhase a n.natAbs * positiveInvariantEndpoint pool α β γ n))))‖ ≤
      A*B*C * Real.sqrt (2^(j+1)+radius : ℕ) * (1+Real.log (2^(j+1)+radius : ℕ))^8 := by
  apply physical_invariant_endpoint_norm P hP hprime V hV hMass pool hpool α β γ
    hA hB hC hα hβ hγ J ell hq0 hq1 _ (2^(j+1)+radius)
    (physical_reachable_dyadic_range j radius hr)
  intro n _
  exact physical_masked_dyadic_mellin_endpoint_norm_le S pool α β γ a Z v j n

theorem physical_raw_target_endpoint_norm :
    ‖physicalEndpointVector P V J ell q (reachablePositions (physicalDyadicStarts j) radius)
      (physicalPositionMask S
        (fun n => physicalPhase a n.natAbs * positiveInvariantEndpoint pool α β γ n))‖ ≤
      A*B*C * Real.sqrt (2^(j+1)+radius : ℕ) * (1+Real.log (2^(j+1)+radius : ℕ))^8 := by
  apply physical_invariant_endpoint_norm P hP hprime V hV hMass pool hpool α β γ
    hA hB hC hα hβ hγ J ell hq0 hq1 _ (2^(j+1)+radius)
    (physical_reachable_dyadic_range j radius hr)
  intro n _
  exact physical_masked_phase_endpoint_norm_le S pool α β γ a n

end
end Bounty


-- Source module: PhysicalRawDyadicGram

/- The actual masked dyadic Mellin pairing is bounded by its literal alternating root moment. -/

open Finset
open scoped Classical InnerProductSpace
namespace Bounty

theorem physical_raw_dyadic_gram_bound
    {G I : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (hP : Pairwise (fun g h => Disjoint (P g) (P h)))
    (hprime : ∀ g p, p ∈ P g → p.Prime)
    (V : G → ℝ) (hV : ∀ g, 0 < V g) (hMass : ∀ g, ∑ p ∈ P g, 1/(p : ℝ) = V g)
    (patterns : Finset I) (C : I → G → Finset (Fin J)) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ζ : I → ℝ) (k : I → ℤ)
    (K : ∀ i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell → PhysicalAuxLabels P (C i) → ℂ)
    (pool : Finset ℕ) (hpool : ∀ g, P g ⊆ pool) (α β γ α' β' γ' : ℕ → ℂ)
    {A B C₀ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C₀)
    (hα : ∀ m, ‖α m‖ ≤ A) (hβ : ∀ p, ‖β p‖ ≤ B) (hγ : ∀ r, ‖γ r‖ ≤ C₀)
    (hα' : ∀ m, ‖α' m‖ ≤ A) (hβ' : ∀ p, ‖β' p‖ ≤ B) (hγ' : ∀ r, ‖γ' r‖ ≤ C₀)
    (S : Finset ℤ) (j R b D : ℕ) (hR : 2 ≤ R) (hD : 0 < D)
    (hstep : physicalOperatorStepBound P J ell patterns C k ≤ D)
    (hr : 2*R*b ≤ 2^j) (a c Z v : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hfM : ∀ n ∈ physicalDyadicStarts j, ‖invariantTripleEndpoint pool α β γ n.natAbs‖ ≤ M) :
    let f := physicalPositionMask S (physicalDyadicSource j
      (fun n => physicalPhase a n.natAbs * positiveInvariantEndpoint pool α β γ n))
    let g := physicalPositionMask S
      (fun n => physicalPhase c n.natAbs * positiveInvariantEndpoint pool α' β' γ' n)
    let E := A*B*C₀ * Real.sqrt (2^(j+1)+2*R*b : ℕ) * (1+Real.log (2^(j+1)+2*R*b : ℕ))^8
    let moment := physicalRootMoment V patterns C q
      (fun e i => if e % 2 = 0 then -(ζ i-v) else ζ i-v)
      (fun e i => if e % 2 = 0 then -k i else k i)
      (fun e i x y aux => if e % 2 = 0 then (starRingEnd ℂ) (K i y x aux) else K i x y aux)
      (physicalDyadicStarts j) (2*R-1) b
    ‖physicalMellinPairing V patterns C q ζ k K
      (reachablePositions (physicalDyadicStarts j) (2*R*b)) f g ((2 : ℝ)^j) Z v‖ ≤
      ((D : ℝ)*M^2)^(1/(2*(R : ℝ))) * (3*E^2)^(1/2 : ℝ) *
        (E^2)^((1-1/(R : ℝ))/2) * ((2 : ℝ)^j*moment.re)^(1/(2*(R : ℝ))) := by
  dsimp only
  have hs := physical_raw_mellin_source_endpoint_norm P hP hprime V hV hMass pool hpool
    α β γ hA hB hC hα hβ hγ J ell hq0 hq1 S j (2*R*b) hr a Z v
  have ht := physical_raw_target_endpoint_norm P hP hprime V hV hMass pool hpool
    α' β' γ' hA hB hC hα' hβ' hγ' J ell hq0 hq1 S j (2*R*b) hr c
  have hm := physical_alternating_root_moment_nonneg V hV patterns C q
    (fun i => ζ i-v) k K (physicalDyadicStarts j) R b (by omega)
  have hp := physical_endpoint_block_gram_bound V hV patterns C hq0 hq1
    (fun i => ζ i-v) k K (physicalDyadicStarts j) R b D hR hD hstep
    (physicalMellinSource ((2 : ℝ)^j) Z v (physicalPositionMask S (physicalDyadicSource j
      (fun n => physicalPhase a n.natAbs * positiveInvariantEndpoint pool α β γ n))))
    (physicalPositionMask S
      (fun n => physicalPhase c n.natAbs * positiveInvariantEndpoint pool α' β' γ' n))
    (fun n _ hn => physical_raw_dyadic_source_support S pool α β γ a Z v j hn) hM
    (fun n hn => (physical_masked_dyadic_mellin_endpoint_norm_le S pool α β γ a Z v j n).trans (hfM n hn))
  dsimp only at hp
  rw [physical_dyadic_starts_card, Nat.cast_pow, Nat.cast_ofNat] at hp
  apply hp.trans
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast (by omega : 1 ≤ R)
  have htheta : 0 ≤ (1-1/(R : ℝ))/2 := by
    have hdiv := (div_le_one (lt_of_lt_of_le zero_lt_one hR1)).mpr hR1
    linarith
  gcongr

end Bounty


-- Source module: PhysicalDyadicEnergyScalar

/- Fixed endpoint-energy powers on a dyadic neighborhood. -/

namespace Bounty

theorem dyadic_sqrt_energy_sq_le {N X C U : ℝ} (hN : 0 ≤ N) (hX : 0 ≤ X)
    (hC : 0 ≤ C) (hNbound : N ≤ 4*X) (hU : 2*C ≤ U) :
    (C * Real.sqrt N)^2 ≤ X*U^2 := by
  calc
    _ = C^2*N := by rw [mul_pow, Real.sq_sqrt hN]
    _ ≤ C^2*(4*X) := mul_le_mul_of_nonneg_left hNbound (sq_nonneg C)
    _ = X*(2*C)^2 := by ring
    _ ≤ X*U^2 := by gcongr

theorem physical_dyadic_endpoint_energy_sq (j radius : ℕ) (hr : radius ≤ 2^j)
    {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    (A*B*C * Real.sqrt (2^(j+1)+radius : ℕ) * (1+Real.log (2^(j+1)+radius : ℕ))^8)^2 ≤
      (2 : ℝ)^j * (max 1 (2*(A*B*C*(1+Real.log (2^(j+1)+radius : ℕ))^8)))^2 := by
  have hN : ((2^(j+1)+radius : ℕ) : ℝ) ≤ 4*(2 : ℝ)^j := by
    have hr' : (radius : ℝ) ≤ (2 : ℝ)^j := by exact_mod_cast hr
    push_cast
    rw [pow_succ]
    linarith [show 0 ≤ (2 : ℝ)^j by positivity]
  have hs := dyadic_sqrt_energy_sq_le (Nat.cast_nonneg (2^(j+1)+radius))
    (show 0 ≤ (2 : ℝ)^j by positivity)
    (show 0 ≤ A*B*C*(1+Real.log (2^(j+1)+radius : ℕ))^8 by positivity)
    hN (le_max_right 1 (2*(A*B*C*(1+Real.log (2^(j+1)+radius : ℕ))^8)))
  convert hs using 1
  ring

end Bounty


-- Source module: PhysicalRawDyadicDecay

/- Actual raw per-dyad decay from the literal alternating root moment. -/

open Finset
open scoped Classical InnerProductSpace
namespace Bounty

theorem physical_raw_dyadic_moment_decay
    {G I : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (hP : Pairwise (fun g h => Disjoint (P g) (P h)))
    (hprime : ∀ g p, p ∈ P g → p.Prime)
    (V : G → ℝ) (hV : ∀ g, 0 < V g) (hMass : ∀ g, ∑ p ∈ P g, 1/(p : ℝ) = V g)
    (patterns : Finset I) (C : I → G → Finset (Fin J)) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ζ : I → ℝ) (k : I → ℤ)
    (K : ∀ i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell → PhysicalAuxLabels P (C i) → ℂ)
    (pool : Finset ℕ) (hpool : ∀ g, P g ⊆ pool) (α β γ α' β' γ' : ℕ → ℂ)
    {A B C₀ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C₀)
    (hα : ∀ m, ‖α m‖ ≤ A) (hβ : ∀ p, ‖β p‖ ≤ B) (hγ : ∀ r, ‖γ r‖ ≤ C₀)
    (hα' : ∀ m, ‖α' m‖ ≤ A) (hβ' : ∀ p, ‖β' p‖ ≤ B) (hγ' : ∀ r, ‖γ' r‖ ≤ C₀)
    (S : Finset ℤ) (j R b D : ℕ) (hR : 2 ≤ R) (hD : 0 < D)
    (hstep : physicalOperatorStepBound P J ell patterns C k ≤ D)
    (hr : 2*R*b ≤ 2^j) (a c Z v : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hfM : ∀ n ∈ physicalDyadicStarts j, ‖invariantTripleEndpoint pool α β γ n.natAbs‖ ≤ M)
    {B₀ T : ℝ} (hB₀ : 0 ≤ B₀) (hT : 0 ≤ T)
    (hblock : ((D : ℝ)*M^2)^(1/(2*(R : ℝ))) ≤ B₀)
    (hmoment : (physicalRootMoment V patterns C q
      (fun e i => if e % 2 = 0 then -(ζ i-v) else ζ i-v)
      (fun e i => if e % 2 = 0 then -k i else k i)
      (fun e i x y aux => if e % 2 = 0 then (starRingEnd ℂ) (K i y x aux) else K i x y aux)
      (physicalDyadicStarts j) (2*R-1) b).re ≤ T^(2*R)) :
    let f := physicalPositionMask S (physicalDyadicSource j
      (fun n => physicalPhase a n.natAbs * positiveInvariantEndpoint pool α β γ n))
    let g := physicalPositionMask S
      (fun n => physicalPhase c n.natAbs * positiveInvariantEndpoint pool α' β' γ' n)
    let U := max 1 (2*(A*B*C₀*(1+Real.log (2^(j+1)+2*R*b : ℕ))^8))
    ‖physicalMellinPairing V patterns C q ζ k K
      (reachablePositions (physicalDyadicStarts j) (2*R*b)) f g ((2 : ℝ)^j) Z v‖ ≤
      B₀ * Real.sqrt 3 * (2 : ℝ)^j * U^2 * T := by
  dsimp only
  have hp := physical_raw_dyadic_gram_bound P hP hprime V hV hMass patterns C hq0 hq1
    ζ k K pool hpool α β γ α' β' γ' hA hB hC hα hβ hγ hα' hβ' hγ'
    S j R b D hR hD hstep hr a c Z v hM hfM
  dsimp only at hp
  have hm := physical_alternating_root_moment_nonneg V hV patterns C q
    (fun i => ζ i-v) k K (physicalDyadicStarts j) R b (by omega)
  have he := physical_dyadic_endpoint_energy_sq j (2*R*b) hr hA hB hC
  apply hp.trans
  apply block_gram_of_energy_bounds (by omega : 1 ≤ R)
    (sq_nonneg _) (sq_nonneg _) (mul_nonneg (by positivity) hm)
    hB₀ (by positivity) (le_max_left _ _) hT hblock he he
  exact mul_le_mul_of_nonneg_left hmoment (by positivity)

end Bounty


-- Source module: PhysicalDyadicMellinSum

/- Exact finite dyadic sum of localized Mellin pairings. -/

open Finset MeasureTheory
open scoped Classical
namespace Bounty

theorem physical_dyadic_mellin_sum_cutoff
    {G I : Type*} [Fintype G] [DecidableEq G] {P : G → Finset ℕ} {J ell : ℕ}
    (V : G → ℝ) (hV : ∀ g, 0 < V g)
    (patterns : Finset I) (C : I → G → Finset (Fin J)) (q : ℝ)
    (ζ : I → ℝ) (k : I → ℤ)
    (K : ∀ i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell → PhysicalAuxLabels P (C i) → ℂ)
    (positions : Finset ℤ) (radius : ℕ)
    (hstep : physicalOperatorStepBound P J ell patterns C k ≤ radius)
    (f g : ℤ → ℂ) (hf : ∀ n, f n ≠ 0 → 0 < n)
    (s : Finset ℕ) (Z : ℝ) (ρ : ℝ → ℂ) (ν : ℝ → ℝ) :
    (∑ j ∈ s, (((2 : ℝ)^j : ℝ) : ℂ)⁻¹ * ∫ v : ℝ, ρ v *
      physicalMellinPairing V patterns C q ζ k K positions
        (physicalDyadicSource j f) g ((2 : ℝ)^j) Z (ν v)) =
    ∑ j ∈ s, (((2 : ℝ)^j : ℝ) : ℂ)⁻¹ * ∫ v : ℝ, ρ v *
      physicalMellinPairing V patterns C q ζ k K
        (reachablePositions (physicalDyadicStarts j) radius)
        (physicalPositionMask positions (physicalDyadicSource j f))
        (physicalPositionMask positions g) ((2 : ℝ)^j) Z (ν v) := by
  apply sum_congr rfl
  intro j _
  apply congrArg (fun z : ℂ => (((2 : ℝ)^j : ℝ) : ℂ)⁻¹ * z)
  apply integral_congr_ae
  filter_upwards [] with v
  apply congrArg (fun z : ℂ => ρ v * z)
  exact physical_dyadic_mellin_pairing_cutoff V hV patterns C q ζ k K
    positions radius j hstep f g hf ((2 : ℝ)^j) Z (ν v)

end Bounty


-- Source module: PhysicalSignedRootMellin

/- Exact physical Mellin representation of the entire signed residual. -/

open Finset MeasureTheory
open scoped Classical
namespace Bounty

section
variable {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ) (probes : G → Finset (Fin J))
    (r t : Finset G) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (a b Z : ℝ) (k : ℤ) (pool : Finset ℕ) (α β γ α' β' γ' : ℕ → ℂ)
    (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))
    (hprime : ∀ g p, p ∈ P g → p.Prime) (hpool : ∀ g, P g ⊆ pool)
    (hV : ∀ g, 0 < V g) (hZ : 0 < Z)
    (positions : Finset ℤ)
    (hclosure : physicalSignedHarmonicPositions (ell := ell) P probes r t Z k ⊆ positions)

include hdis hprime hpool hV hZ hclosure

theorem physical_signed_harmonic_residual_mellin (X : ℝ) (hX : X ≠ 0) :
    physicalSignedPositiveHarmonicResidual (ell := ell) P V probes r t hrt Q h ξ a b Z k pool α β γ α' β' γ' =
      (X : ℂ)⁻¹ * ∫ v : ℝ, harmonicLogFourier v *
        physicalMellinPairing V (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
          (repeatedBigPrimePatternCut probes r t) (1/2) (fun _ => -(a+b)) (fun _ => k)
          (physicalRootPrimeKernel P V probes r t hrt Q h ξ) positions
          (fun n => physicalPhase (-a) n.natAbs * positiveInvariantEndpoint pool α β γ n)
          (fun n => physicalPhase b n.natAbs * positiveInvariantEndpoint pool α' β' γ' n)
          X Z (2*Real.pi*v) := by
  rw [physical_signed_harmonic_residual_eq_root P V probes r t hrt Q h ξ a b Z k pool
    α β γ α' β' γ' hdis hprime hpool hZ positions hclosure]
  apply physical_mellin_root_eq_integral (fun g p hp => (hprime g p hp).pos) V hV
    _ _ (by norm_num) _ _ _ positions _ _ _ X Z hX hZ harmonicLogFourier
    (fun v => 2*Real.pi*v) harmonic_log_fourier_integrable (by fun_prop)
    (fun x => (typeIIHarmonicDyadic x : ℂ)) (fun _ ht => harmonic_dyadic_mellin_representation ht)
  intro n _ hn
  apply positive_invariant_endpoint_nonzero pool α β γ
  intro hz
  exact hn (by rw [hz, mul_zero])

theorem physical_signed_harmonic_residual_dyadic_mellin :
    physicalSignedPositiveHarmonicResidual (ell := ell) P V probes r t hrt Q h ξ a b Z k pool α β γ α' β' γ' =
      ∑ j ∈ positions.image (fun n => n.natAbs.log2),
        (((2 : ℝ)^j : ℝ) : ℂ)⁻¹ * ∫ v : ℝ, harmonicLogFourier v *
          physicalMellinPairing V (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
            (repeatedBigPrimePatternCut probes r t) (1/2) (fun _ => -(a+b)) (fun _ => k)
            (physicalRootPrimeKernel P V probes r t hrt Q h ξ) positions
            (physicalDyadicSource j
              (fun n => physicalPhase (-a) n.natAbs * positiveInvariantEndpoint pool α β γ n))
            (fun n => physicalPhase b n.natAbs * positiveInvariantEndpoint pool α' β' γ' n)
            ((2 : ℝ)^j) Z (2*Real.pi*v) := by
  rw [physical_signed_harmonic_residual_eq_root P V probes r t hrt Q h ξ a b Z k pool
    α β γ α' β' γ' hdis hprime hpool hZ positions hclosure,
    ← physical_mellin_root_dyadic_sum]
  apply sum_congr rfl
  intro j _
  apply physical_mellin_root_eq_integral (fun g p hp => (hprime g p hp).pos) V hV
    _ _ (by norm_num) _ _ _ positions _ _ _ ((2 : ℝ)^j) Z (by positivity) hZ harmonicLogFourier
    (fun v => 2*Real.pi*v) harmonic_log_fourier_integrable (by fun_prop)
    (fun x => (typeIIHarmonicDyadic x : ℂ)) (fun _ ht => harmonic_dyadic_mellin_representation ht)
  intro n _ hn
  have hf := (physical_dyadic_source_nonzero j _ hn).1
  apply positive_invariant_endpoint_nonzero pool α β γ
  intro hz
  exact hf (by rw [hz, mul_zero])

theorem physical_signed_harmonic_residual_norm_le
    (B : ℕ → ℝ → ℝ)
    (hB : ∀ j ∈ positions.image (fun n => n.natAbs.log2),
      Integrable (fun v => ‖harmonicLogFourier v‖ * B j v))
    (hpair : ∀ j ∈ positions.image (fun n => n.natAbs.log2), ∀ᵐ v,
      ‖physicalMellinPairing V (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
        (repeatedBigPrimePatternCut probes r t) (1/2) (fun _ => -(a+b)) (fun _ => k)
        (physicalRootPrimeKernel P V probes r t hrt Q h ξ) positions
        (physicalDyadicSource j
          (fun n => physicalPhase (-a) n.natAbs * positiveInvariantEndpoint pool α β γ n))
        (fun n => physicalPhase b n.natAbs * positiveInvariantEndpoint pool α' β' γ' n)
        ((2 : ℝ)^j) Z (2*Real.pi*v)‖ ≤ B j v) :
    ‖physicalSignedPositiveHarmonicResidual (ell := ell) P V probes r t hrt Q h ξ a b Z k pool α β γ α' β' γ'‖ ≤
      ∑ j ∈ positions.image (fun n => n.natAbs.log2),
        ((2 : ℝ)^j)⁻¹ * ∫ v : ℝ, ‖harmonicLogFourier v‖ * B j v := by
  rw [physical_signed_harmonic_residual_eq_root P V probes r t hrt Q h ξ a b Z k pool
    α β γ α' β' γ' hdis hprime hpool hZ positions hclosure,
    ← physical_mellin_root_dyadic_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro j hj
  apply physical_mellin_root_norm_bound (fun g p hp => (hprime g p hp).pos) V hV
    _ _ (by norm_num) _ _ _ positions _ _ _ ((2 : ℝ)^j) Z (by positivity) hZ harmonicLogFourier
    (fun v => 2*Real.pi*v) harmonic_log_fourier_integrable (by fun_prop)
    (fun x => (typeIIHarmonicDyadic x : ℂ)) (fun _ ht => harmonic_dyadic_mellin_representation ht)
    (B j) (hB j hj) (hpair j hj)
  intro n _ hn
  have hf := (physical_dyadic_source_nonzero j _ hn).1
  apply positive_invariant_endpoint_nonzero pool α β γ
  intro hz
  exact hf (by rw [hz, mul_zero])

end
end Bounty


-- Source module: PhysicalActualDyadicCutoff

/- The original signed residual as localized dyadic physical Mellin pairings. -/

open Finset MeasureTheory
open scoped Classical
namespace Bounty

theorem physical_signed_harmonic_residual_local_mellin
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ) (probes : G → Finset (Fin J))
    (r t : Finset G) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (a b Z : ℝ) (k : ℤ) (pool : Finset ℕ) (α β γ α' β' γ' : ℕ → ℂ)
    (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))
    (hprime : ∀ g p, p ∈ P g → p.Prime) (hpool : ∀ g, P g ⊆ pool)
    (hV : ∀ g, 0 < V g) (hZ : 0 < Z)
    (positions : Finset ℤ)
    (hclosure : physicalSignedHarmonicPositions (ell := ell) P probes r t Z k ⊆ positions)
    (radius : ℕ)
    (hstep : physicalOperatorStepBound P J ell
      (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
      (repeatedBigPrimePatternCut probes r t) (fun _ => k) ≤ radius) :
    physicalSignedPositiveHarmonicResidual (ell := ell) P V probes r t hrt Q h ξ a b Z k pool α β γ α' β' γ' =
      ∑ j ∈ positions.image (fun n => n.natAbs.log2),
        (((2 : ℝ)^j : ℝ) : ℂ)⁻¹ * ∫ v : ℝ, harmonicLogFourier v *
          physicalMellinPairing V (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
            (repeatedBigPrimePatternCut probes r t) (1/2) (fun _ => -(a+b)) (fun _ => k)
            (physicalRootPrimeKernel P V probes r t hrt Q h ξ)
            (reachablePositions (physicalDyadicStarts j) radius)
            (physicalPositionMask positions (physicalDyadicSource j
              (fun n => physicalPhase (-a) n.natAbs * positiveInvariantEndpoint pool α β γ n)))
            (physicalPositionMask positions
              (fun n => physicalPhase b n.natAbs * positiveInvariantEndpoint pool α' β' γ' n))
            ((2 : ℝ)^j) Z (2*Real.pi*v) := by
  refine (physical_signed_harmonic_residual_dyadic_mellin P V probes r t hrt Q h ξ a b Z k pool
    α β γ α' β' γ' hdis hprime hpool hV hZ positions hclosure).trans ?_
  apply physical_dyadic_mellin_sum_cutoff V hV _ _ _ _ _ _ positions radius hstep
  intro n hn
  apply positive_invariant_endpoint_nonzero pool α β γ
  intro hz
  exact hn (by rw [hz, mul_zero])

end Bounty


-- Source module: PhysicalActualDyadicMomentBound

/- The original signed prime kernel in the literal alternating dyadic moment bound. -/

open Finset
open scoped Classical
namespace Bounty

theorem physical_actual_dyadic_moment_bound
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ) (probes : G → Finset (Fin J))
    (r t : Finset G) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (a b Z : ℝ) (k : ℤ) (pool : Finset ℕ) (α β γ α' β' γ' : ℕ → ℂ)
    (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))
    (hprime : ∀ g p, p ∈ P g → p.Prime) (hpool : ∀ g, P g ⊆ pool)
    (hV : ∀ g, 0 < V g) (hMass : ∀ g, ∑ p ∈ P g, 1/(p : ℝ) = V g)
    {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hα : ∀ n, ‖α n‖ ≤ A) (hβ : ∀ n, ‖β n‖ ≤ B) (hγ : ∀ n, ‖γ n‖ ≤ C)
    (hα' : ∀ n, ‖α' n‖ ≤ A) (hβ' : ∀ n, ‖β' n‖ ≤ B) (hγ' : ∀ n, ‖γ' n‖ ≤ C)
    (positions : Finset ℤ) (j R D : ℕ) (hR : 2 ≤ R) (hD : 0 < D)
    (hstep : physicalOperatorStepBound P J ell
      (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
      (repeatedBigPrimePatternCut probes r t) (fun _ => k) ≤ D)
    (hr : 2*R*D ≤ 2^j) (v : ℝ) {M B₀ T : ℝ} (hM : 0 ≤ M) (hB₀ : 0 ≤ B₀) (hT : 0 ≤ T)
    (hsource : ∀ n ∈ physicalDyadicStarts j, ‖invariantTripleEndpoint pool α β γ n.natAbs‖ ≤ M)
    (hblock : ((D : ℝ)*M^2)^(1/(2*(R : ℝ))) ≤ B₀)
    (hmoment : (physicalRootMoment V
      (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
      (repeatedBigPrimePatternCut probes r t) (1/2)
      (fun e _ => if e % 2 = 0 then -(-(a+b)-2*Real.pi*v) else -(a+b)-2*Real.pi*v)
      (fun e _ => if e % 2 = 0 then -k else k)
      (fun e i x y aux => if e % 2 = 0 then
        (starRingEnd ℂ) (physicalRootPrimeKernel P V probes r t hrt Q h ξ i y x aux)
        else physicalRootPrimeKernel P V probes r t hrt Q h ξ i x y aux)
      (physicalDyadicStarts j) (2*R-1) D).re ≤ T^(2*R)) :
    ‖physicalMellinPairing V
      (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
      (repeatedBigPrimePatternCut probes r t) (1/2) (fun _ => -(a+b)) (fun _ => k)
      (physicalRootPrimeKernel P V probes r t hrt Q h ξ)
      (reachablePositions (physicalDyadicStarts j) (2*R*D))
      (physicalPositionMask positions (physicalDyadicSource j
        (fun n => physicalPhase (-a) n.natAbs * positiveInvariantEndpoint pool α β γ n)))
      (physicalPositionMask positions
        (fun n => physicalPhase b n.natAbs * positiveInvariantEndpoint pool α' β' γ' n))
      ((2 : ℝ)^j) Z (2*Real.pi*v)‖ ≤
      (2 : ℝ)^j * (B₀ * Real.sqrt 3 *
        (max 1 (2*(A*B*C*(1+Real.log (2^(j+1)+2*R*D : ℕ))^8)))^2 * T) := by
  have hp := physical_raw_dyadic_moment_decay P hdis hprime V hV hMass
    (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
    (repeatedBigPrimePatternCut probes r t) (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) ≤ 1) (fun _ => -(a+b)) (fun _ => k)
    (physicalRootPrimeKernel P V probes r t hrt Q h ξ) pool hpool α β γ α' β' γ'
    hA hB hC hα hβ hγ hα' hβ' hγ' positions j R D D hR hD hstep hr
    (-a) b Z (2*Real.pi*v) hM hsource hB₀ hT hblock hmoment
  dsimp only at hp
  convert hp using 1
  ring

end Bounty


-- Source module: DyadicMellinEnvelope

/- Reciprocal dyadic scale cancellation with an integrable frequency envelope. -/

open Finset MeasureTheory
namespace Bounty

theorem dyadic_mellin_sum_norm_le_envelope {I : Type*} (S : Finset I) (X : I → ℝ)
    (hX : ∀ i ∈ S, 0 < X i) (F : I → ℝ → ℂ) (g : ℝ → ℂ) (B : I → ℝ → ℝ)
    (hB : ∀ i ∈ S, Integrable (fun v => ‖g v‖ * B i v))
    (hF : ∀ i ∈ S, ∀ᵐ v : ℝ, ‖F i v‖ ≤ X i * B i v) :
    ‖∑ i ∈ S, (X i : ℂ)⁻¹ * ∫ v : ℝ, g v * F i v‖ ≤
      ∑ i ∈ S, ∫ v : ℝ, ‖g v‖ * B i v := by
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro i hi
  have hb : ‖∫ v : ℝ, g v * F i v‖ ≤ X i * ∫ v : ℝ, ‖g v‖ * B i v := by
    calc
      _ ≤ ∫ v : ℝ, X i * (‖g v‖ * B i v) := by
        apply norm_integral_le_of_norm_le ((hB i hi).const_mul (X i))
        filter_upwards [hF i hi] with v hv
        rw [norm_mul]
        calc
          _ ≤ ‖g v‖ * (X i * B i v) := mul_le_mul_of_nonneg_left hv (norm_nonneg _)
          _ = _ := by ring
      _ = _ := integral_const_mul _ _
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (hX i hi).le]
  calc
    _ ≤ (X i)⁻¹ * (X i * ∫ v : ℝ, ‖g v‖ * B i v) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (hX i hi).le)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (hX i hi).ne', one_mul]

end Bounty


-- Source module: PhysicalResidualMellinEnvelope

/- The original signed residual with an integrable, frequency-dependent local envelope. -/

open Finset MeasureTheory
open scoped Classical
namespace Bounty

theorem physical_residual_local_envelope
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ) (probes : G → Finset (Fin J))
    (r t : Finset G) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (a b Z : ℝ) (k : ℤ) (pool : Finset ℕ) (α β γ α' β' γ' : ℕ → ℂ)
    (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))
    (hprime : ∀ g p, p ∈ P g → p.Prime) (hpool : ∀ g, P g ⊆ pool)
    (hV : ∀ g, 0 < V g) (hZ : 0 < Z) (positions : Finset ℤ)
    (hclosure : physicalSignedHarmonicPositions (ell := ell) P probes r t Z k ⊆ positions)
    (radius : ℕ)
    (hstep : physicalOperatorStepBound P J ell
      (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
      (repeatedBigPrimePatternCut probes r t) (fun _ => k) ≤ radius)
    (B : ℕ → ℝ → ℝ)
    (hB : ∀ j ∈ positions.image (fun n => n.natAbs.log2),
      Integrable (fun v => ‖harmonicLogFourier v‖ * B j v))
    (hpair : ∀ j ∈ positions.image (fun n => n.natAbs.log2), ∀ᵐ v : ℝ,
      ‖physicalMellinPairing V
        (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
        (repeatedBigPrimePatternCut probes r t) (1/2) (fun _ => -(a+b)) (fun _ => k)
        (physicalRootPrimeKernel P V probes r t hrt Q h ξ)
        (reachablePositions (physicalDyadicStarts j) radius)
        (physicalPositionMask positions (physicalDyadicSource j
          (fun n => physicalPhase (-a) n.natAbs * positiveInvariantEndpoint pool α β γ n)))
        (physicalPositionMask positions
          (fun n => physicalPhase b n.natAbs * positiveInvariantEndpoint pool α' β' γ' n))
        ((2 : ℝ)^j) Z (2*Real.pi*v)‖ ≤ (2 : ℝ)^j * B j v) :
    ‖physicalSignedPositiveHarmonicResidual (ell := ell) P V probes r t hrt Q h ξ a b Z k
      pool α β γ α' β' γ'‖ ≤
        ∑ j ∈ positions.image (fun n => n.natAbs.log2), ∫ v : ℝ, ‖harmonicLogFourier v‖ * B j v := by
  rw [physical_signed_harmonic_residual_local_mellin P V probes r t hrt Q h ξ a b Z k
    pool α β γ α' β' γ' hdis hprime hpool hV hZ positions hclosure radius hstep]
  exact dyadic_mellin_sum_norm_le_envelope _ (fun j => (2 : ℝ)^j)
    (fun _ _ => by positivity) _ harmonicLogFourier B hB hpair

end Bounty


-- Source module: PhysicalResidualCommonEnvelope

/- A common frequency envelope leaves only the finite dyadic count. -/

open Finset MeasureTheory
open scoped Classical
namespace Bounty

theorem physical_residual_common_envelope
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ) (probes : G → Finset (Fin J))
    (r t : Finset G) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (a b Z : ℝ) (k : ℤ) (pool : Finset ℕ) (α β γ α' β' γ' : ℕ → ℂ)
    (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))
    (hprime : ∀ g p, p ∈ P g → p.Prime) (hpool : ∀ g, P g ⊆ pool)
    (hV : ∀ g, 0 < V g) (hZ : 0 < Z) (positions : Finset ℤ)
    (hclosure : physicalSignedHarmonicPositions (ell := ell) P probes r t Z k ⊆ positions)
    (radius : ℕ)
    (hstep : physicalOperatorStepBound P J ell
      (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
      (repeatedBigPrimePatternCut probes r t) (fun _ => k) ≤ radius)
    (C : ℝ) (B : ℝ → ℝ)
    (hB : Integrable (fun v => ‖harmonicLogFourier v‖ * B v))
    (hpair : ∀ j ∈ positions.image (fun n => n.natAbs.log2), ∀ᵐ v : ℝ,
      ‖physicalMellinPairing V
        (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
        (repeatedBigPrimePatternCut probes r t) (1/2) (fun _ => -(a+b)) (fun _ => k)
        (physicalRootPrimeKernel P V probes r t hrt Q h ξ)
        (reachablePositions (physicalDyadicStarts j) radius)
        (physicalPositionMask positions (physicalDyadicSource j
          (fun n => physicalPhase (-a) n.natAbs * positiveInvariantEndpoint pool α β γ n)))
        (physicalPositionMask positions
          (fun n => physicalPhase b n.natAbs * positiveInvariantEndpoint pool α' β' γ' n))
        ((2 : ℝ)^j) Z (2*Real.pi*v)‖ ≤ (2 : ℝ)^j * (C * B v)) :
    ‖physicalSignedPositiveHarmonicResidual (ell := ell) P V probes r t hrt Q h ξ a b Z k
      pool α β γ α' β' γ'‖ ≤
        ((positions.image (fun n => n.natAbs.log2)).card : ℝ) * C *
          ∫ v : ℝ, ‖harmonicLogFourier v‖ * B v := by
  have hi : Integrable (fun v => ‖harmonicLogFourier v‖ * (C * B v)) := by
    apply (hB.const_mul C).congr
    exact Filter.Eventually.of_forall (fun v => by ring)
  have hp := physical_residual_local_envelope P V probes r t hrt Q h ξ a b Z k pool
    α β γ α' β' γ' hdis hprime hpool hV hZ positions hclosure radius hstep
    (fun _ v => C * B v) (fun _ _ => hi) hpair
  apply hp.trans_eq
  have he : (fun v : ℝ => ‖harmonicLogFourier v‖ * (C * B v)) =
      (fun v : ℝ => C * (‖harmonicLogFourier v‖ * B v)) := by funext v; ring
  simp only [he, integral_const_mul, sum_const, nsmul_eq_mul]
  ring

end Bounty


-- Source module: WeightedPiecewiseMellin

/- A measurable split retains the exact integrable Fourier weight on both pieces. -/

open MeasureTheory
open scoped Classical
namespace Bounty

theorem weighted_piecewise_mellin_properties
    {s : Set ℝ} (hs : MeasurableSet s) (w f g : ℝ → ℝ)
    (hf : IntegrableOn (fun v => w v * f v) s)
    (hg : IntegrableOn (fun v => w v * g v) sᶜ) :
    Integrable (fun v => w v * s.piecewise f g v) ∧
      (∫ v : ℝ, w v * s.piecewise f g v) =
        (∫ v in s, w v * f v) + ∫ v in sᶜ, w v * g v := by
  have he : (fun v => w v * s.piecewise f g v) =
      (fun v => s.indicator (fun x => w x * f x) v +
        sᶜ.indicator (fun x => w x * g x) v) := by
    funext v
    by_cases hv : v ∈ s <;> simp [Set.piecewise, hv]
  have hf' := hf.integrable_indicator hs
  have hg' := hg.integrable_indicator hs.compl
  rw [he]
  exact ⟨hf'.add hg', by rw [integral_add hf' hg', integral_indicator hs,
    integral_indicator hs.compl]⟩

end Bounty


-- Source module: PhysicalResidualSplitEnvelope

/- An exact central/tail split for the original signed residual. -/

open Finset MeasureTheory
open scoped Classical
namespace Bounty

theorem physical_residual_split_envelope
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ) (probes : G → Finset (Fin J))
    (r t : Finset G) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (a b Z : ℝ) (k : ℤ) (pool : Finset ℕ) (α β γ α' β' γ' : ℕ → ℂ)
    (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))
    (hprime : ∀ g p, p ∈ P g → p.Prime) (hpool : ∀ g, P g ⊆ pool)
    (hV : ∀ g, 0 < V g) (hZ : 0 < Z) (positions : Finset ℤ)
    (hclosure : physicalSignedHarmonicPositions (ell := ell) P probes r t Z k ⊆ positions)
    (radius : ℕ)
    (hstep : physicalOperatorStepBound P J ell
      (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
      (repeatedBigPrimePatternCut probes r t) (fun _ => k) ≤ radius)
    (s : Set ℝ) (hs : MeasurableSet s) (C : ℝ) (T E : ℝ → ℝ)
    (hT : IntegrableOn (fun v => ‖harmonicLogFourier v‖ * T v) s)
    (hE : IntegrableOn (fun v => ‖harmonicLogFourier v‖ * E v) sᶜ)
    (hcentral : ∀ j ∈ positions.image (fun n => n.natAbs.log2), ∀ᵐ v : ℝ, v ∈ s →
      ‖physicalMellinPairing V
        (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
        (repeatedBigPrimePatternCut probes r t) (1/2) (fun _ => -(a+b)) (fun _ => k)
        (physicalRootPrimeKernel P V probes r t hrt Q h ξ)
        (reachablePositions (physicalDyadicStarts j) radius)
        (physicalPositionMask positions (physicalDyadicSource j
          (fun n => physicalPhase (-a) n.natAbs * positiveInvariantEndpoint pool α β γ n)))
        (physicalPositionMask positions
          (fun n => physicalPhase b n.natAbs * positiveInvariantEndpoint pool α' β' γ' n))
        ((2 : ℝ)^j) Z (2*Real.pi*v)‖ ≤ (2 : ℝ)^j * (C * T v))
    (htail : ∀ j ∈ positions.image (fun n => n.natAbs.log2), ∀ᵐ v : ℝ,
      ‖physicalMellinPairing V
        (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
        (repeatedBigPrimePatternCut probes r t) (1/2) (fun _ => -(a+b)) (fun _ => k)
        (physicalRootPrimeKernel P V probes r t hrt Q h ξ)
        (reachablePositions (physicalDyadicStarts j) radius)
        (physicalPositionMask positions (physicalDyadicSource j
          (fun n => physicalPhase (-a) n.natAbs * positiveInvariantEndpoint pool α β γ n)))
        (physicalPositionMask positions
          (fun n => physicalPhase b n.natAbs * positiveInvariantEndpoint pool α' β' γ' n))
        ((2 : ℝ)^j) Z (2*Real.pi*v)‖ ≤ (2 : ℝ)^j * E v) :
    ‖physicalSignedPositiveHarmonicResidual (ell := ell) P V probes r t hrt Q h ξ a b Z k
      pool α β γ α' β' γ'‖ ≤
        ((positions.image (fun n => n.natAbs.log2)).card : ℝ) *
          (C * (∫ v in s, ‖harmonicLogFourier v‖ * T v) +
            ∫ v in sᶜ, ‖harmonicLogFourier v‖ * E v) := by
  have hTc : IntegrableOn (fun v => ‖harmonicLogFourier v‖ * (C * T v)) s := by
    apply (hT.const_mul C).congr
    exact Filter.Eventually.of_forall (fun v => by ring)
  have hprops := weighted_piecewise_mellin_properties hs
    (fun v => ‖harmonicLogFourier v‖) (fun v => C * T v) E hTc hE
  have hpair : ∀ j ∈ positions.image (fun n => n.natAbs.log2), ∀ᵐ v : ℝ,
      ‖physicalMellinPairing V
        (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
        (repeatedBigPrimePatternCut probes r t) (1/2) (fun _ => -(a+b)) (fun _ => k)
        (physicalRootPrimeKernel P V probes r t hrt Q h ξ)
        (reachablePositions (physicalDyadicStarts j) radius)
        (physicalPositionMask positions (physicalDyadicSource j
          (fun n => physicalPhase (-a) n.natAbs * positiveInvariantEndpoint pool α β γ n)))
        (physicalPositionMask positions
          (fun n => physicalPhase b n.natAbs * positiveInvariantEndpoint pool α' β' γ' n))
        ((2 : ℝ)^j) Z (2*Real.pi*v)‖ ≤ (2 : ℝ)^j * (1 * s.piecewise (fun v => C * T v) E v) := by
    intro j hj
    filter_upwards [hcentral j hj, htail j hj] with v hc ht
    by_cases hv : v ∈ s
    · simpa [Set.piecewise, hv] using hc hv
    · simpa [Set.piecewise, hv] using ht
  have hp := physical_residual_common_envelope P V probes r t hrt Q h ξ a b Z k pool
    α β γ α' β' γ' hdis hprime hpool hV hZ positions hclosure radius hstep
    1 (s.piecewise (fun v => C * T v) E) hprops.1 hpair
  have he : (∫ v in s, ‖harmonicLogFourier v‖ * (C * T v)) =
      C * ∫ v in s, ‖harmonicLogFourier v‖ * T v := by
    calc
      _ = ∫ v in s, C * (‖harmonicLogFourier v‖ * T v) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun v => by ring)
      _ = _ := integral_const_mul C _
  simpa only [mul_one, hprops.2, he] using hp

end Bounty


-- Source module: PhysicalResidualFiniteMoment

/- A bounded-frequency moment estimate combined with a direct pairing bound for the tail. -/

open Finset MeasureTheory
open scoped Classical
namespace Bounty

theorem physical_residual_finite_moment_envelope
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ) (probes : G → Finset (Fin J))
    (r t : Finset G) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (a b Z : ℝ) (k : ℤ) (pool : Finset ℕ) (α β γ α' β' γ' : ℕ → ℂ)
    (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))
    (hprime : ∀ g p, p ∈ P g → p.Prime) (hpool : ∀ g, P g ⊆ pool)
    (hV : ∀ g, 0 < V g) (hMass : ∀ g, ∑ p ∈ P g, 1/(p : ℝ) = V g)
    {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hα : ∀ n, ‖α n‖ ≤ A) (hβ : ∀ n, ‖β n‖ ≤ B) (hγ : ∀ n, ‖γ n‖ ≤ C)
    (hα' : ∀ n, ‖α' n‖ ≤ A) (hβ' : ∀ n, ‖β' n‖ ≤ B) (hγ' : ∀ n, ‖γ' n‖ ≤ C)
    (hZ : 0 < Z) (positions : Finset ℤ)
    (hclosure : physicalSignedHarmonicPositions (ell := ell) P probes r t Z k ⊆ positions)
    (R D : ℕ) (hR : 2 ≤ R) (hD : 0 < D)
    (hstep : physicalOperatorStepBound P J ell
      (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
      (repeatedBigPrimePatternCut probes r t) (fun _ => k) ≤ D)
    (hr : ∀ j ∈ positions.image (fun n => n.natAbs.log2), 2*R*D ≤ 2^j)
    (M : ℕ → ℝ) (B₀ U W : ℝ) (T E : ℝ → ℝ) (hB₀ : 0 ≤ B₀)
    (hM : ∀ j ∈ positions.image (fun n => n.natAbs.log2), 0 ≤ M j)
    (hT : ∀ᵐ v : ℝ, ‖v‖ ≤ W → 0 ≤ T v)
    (hsource : ∀ j ∈ positions.image (fun n => n.natAbs.log2),
      ∀ n ∈ physicalDyadicStarts j, ‖invariantTripleEndpoint pool α β γ n.natAbs‖ ≤ M j)
    (hblock : ∀ j ∈ positions.image (fun n => n.natAbs.log2),
      ((D : ℝ)*(M j)^2)^(1/(2*(R : ℝ))) ≤ B₀)
    (hmoment : ∀ j ∈ positions.image (fun n => n.natAbs.log2), ∀ᵐ v : ℝ, ‖v‖ ≤ W →
      (physicalRootMoment V
        (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
        (repeatedBigPrimePatternCut probes r t) (1/2)
        (fun e _ => if e % 2 = 0 then -(-(a+b)-2*Real.pi*v) else -(a+b)-2*Real.pi*v)
        (fun e _ => if e % 2 = 0 then -k else k)
        (fun e i x y aux => if e % 2 = 0 then
          (starRingEnd ℂ) (physicalRootPrimeKernel P V probes r t hrt Q h ξ i y x aux)
          else physicalRootPrimeKernel P V probes r t hrt Q h ξ i x y aux)
        (physicalDyadicStarts j) (2*R-1) D).re ≤ (T v)^(2*R))
    (hU : ∀ j ∈ positions.image (fun n => n.natAbs.log2),
      max 1 (2*(A*B*C*(1+Real.log (2^(j+1)+2*R*D : ℕ))^8)) ≤ U)
    (htail : ∀ j ∈ positions.image (fun n => n.natAbs.log2), ∀ᵐ v : ℝ,
      ‖physicalMellinPairing V
        (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
        (repeatedBigPrimePatternCut probes r t) (1/2) (fun _ => -(a+b)) (fun _ => k)
        (physicalRootPrimeKernel P V probes r t hrt Q h ξ)
        (reachablePositions (physicalDyadicStarts j) (2*R*D))
        (physicalPositionMask positions (physicalDyadicSource j
          (fun n => physicalPhase (-a) n.natAbs * positiveInvariantEndpoint pool α β γ n)))
        (physicalPositionMask positions
          (fun n => physicalPhase b n.natAbs * positiveInvariantEndpoint pool α' β' γ' n))
        ((2 : ℝ)^j) Z (2*Real.pi*v)‖ ≤ (2 : ℝ)^j * E v)
    (hEnvelope : IntegrableOn (fun v => ‖harmonicLogFourier v‖ * T v) {v | ‖v‖ ≤ W})
    (hTailEnvelope : IntegrableOn (fun v => ‖harmonicLogFourier v‖ * E v) {v | ‖v‖ ≤ W}ᶜ) :
    ‖physicalSignedPositiveHarmonicResidual (ell := ell) P V probes r t hrt Q h ξ a b Z k
      pool α β γ α' β' γ'‖ ≤
      ((positions.image (fun n => n.natAbs.log2)).card : ℝ) *
        ((B₀ * Real.sqrt 3 * U^2) * (∫ v in {v : ℝ | ‖v‖ ≤ W}, ‖harmonicLogFourier v‖ * T v) +
          ∫ v in {v : ℝ | ‖v‖ ≤ W}ᶜ, ‖harmonicLogFourier v‖ * E v) := by
  have hstep' : physicalOperatorStepBound P J ell
      (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
      (repeatedBigPrimePatternCut probes r t) (fun _ => k) ≤ 2*R*D := by
    apply hstep.trans
    simpa only [one_mul] using Nat.mul_le_mul_right D (show 1 ≤ 2*R by omega)
  apply physical_residual_split_envelope P V probes r t hrt Q h ξ a b Z k pool
    α β γ α' β' γ' hdis hprime hpool hV hZ positions hclosure (2*R*D) hstep'
    {v | ‖v‖ ≤ W} ((isClosed_le continuous_norm continuous_const).measurableSet)
    (B₀ * Real.sqrt 3 * U^2) T E hEnvelope hTailEnvelope _ htail
  intro j hj
  filter_upwards [hT, hmoment j hj] with v hTv hmv
  intro hv
  have hp := physical_actual_dyadic_moment_bound P V probes r t hrt Q h ξ a b Z k pool
    α β γ α' β' γ' hdis hprime hpool hV hMass hA hB hC hα hβ hγ hα' hβ' hγ'
    positions j R D hR hD hstep (hr j hj) v (hM j hj) hB₀ (hTv hv) (hsource j hj) (hblock j hj) (hmv hv)
  apply hp.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (hTv hv)
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hB₀ (Real.sqrt_nonneg 3))
  exact pow_le_pow_left₀ (by positivity) (hU j hj) 2

end Bounty


-- Source module: PhysicalDyadicUpper

/- Exponential position support gives linear logarithmic dyad bounds. -/

open Finset
namespace Bounty

theorem physical_dyadic_index_upper {S : Finset ℤ} {A : ℝ}
    (hS : ∀ n ∈ S, 0 < n ∧ (n : ℝ) ≤ Real.exp A) {j : ℕ}
    (hj : j ∈ S.image (fun n => n.natAbs.log2)) : (2 : ℝ)^j ≤ Real.exp A := by
  classical
  obtain ⟨n, hn, hj⟩ := mem_image.mp hj
  have hn0 := (hS n hn).1
  have hb := (Nat.log2_eq_iff (Int.natAbs_ne_zero.mpr (ne_of_gt hn0))).mp hj
  have he : (n.natAbs : ℝ) = n := by
    have hi : (n.natAbs : ℤ) = n := by rw [Int.natCast_natAbs, abs_of_pos hn0]
    calc
      (n.natAbs : ℝ) = ((n.natAbs : ℤ) : ℝ) := by simp
      _ = (n : ℝ) := congrArg (fun z : ℤ => (z : ℝ)) hi
  have hl : (2 : ℝ)^j ≤ (n.natAbs : ℝ) := by exact_mod_cast hb.1
  rw [he] at hl
  exact hl.trans (hS n hn).2

theorem physical_dyadic_indices_card {S : Finset ℤ} {A : ℝ}
    (hS : ∀ n ∈ S, 0 < n ∧ (n : ℝ) ≤ Real.exp A) :
    (S.image (fun n => n.natAbs.log2)).card ≤ Nat.floor (A/Real.log 2)+1 := by
  classical
  apply (card_le_card (t := range (Nat.floor (A/Real.log 2)+1)) ?_).trans
    (le_of_eq (card_range _))
  intro j hj
  apply mem_range.mpr
  apply Nat.lt_succ_of_le
  apply Nat.le_floor
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ)^j)
    (physical_dyadic_index_upper hS hj)
  simpa only [Real.log_pow, Real.log_exp] using hl

theorem physical_dyadic_log_upper {j : ℕ} {A : ℝ}
    (hj : (2 : ℝ)^j ≤ Real.exp A) {n : ℤ}
    (hn : n ∈ physicalDyadicStarts j) :
    0 < n ∧ Real.log (n.natAbs : ℝ) ≤ Real.log 2 + A := by
  have hn' := mem_Ico.mp hn
  have hn0 : 0 < n := (by positivity : (0 : ℤ) < 2^j).trans_le hn'.1
  refine ⟨hn0, ?_⟩
  have he : (n.natAbs : ℝ) = n := by
    have hi : (n.natAbs : ℤ) = n := by rw [Int.natCast_natAbs, abs_of_pos hn0]
    calc
      (n.natAbs : ℝ) = ((n.natAbs : ℤ) : ℝ) := by simp
      _ = (n : ℝ) := congrArg (fun z : ℤ => (z : ℝ)) hi
  have hhi : (n.natAbs : ℝ) ≤ 2*Real.exp A := by
    rw [he]
    have hh : (n : ℝ) < (2 : ℝ)^(j+1) := by exact_mod_cast hn'.2
    rw [pow_succ] at hh
    nlinarith
  have hp : (0 : ℝ) < n.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hn0.ne'
  have hl := Real.log_le_log hp hhi
  simpa only [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero A),
    Real.log_exp] using hl

end Bounty


-- Source module: PhysicalResidualScalarBounds

/- Absolute polynomial bounds for the raw dyadic count and fixed endpoint allowance. -/

open Finset Filter
namespace Bounty

theorem physical_dyadic_unit_allowance_le {L : ℝ} (hL : 1 ≤ L)
    (hconst : 2*(8 : ℝ)^8 ≤ L) (hlog : Real.log 3 ≤ L)
    (j radius : ℕ) (hr : radius ≤ 2^j) (hj : (2 : ℝ)^j ≤ Real.exp (6*L)) :
    max 1 (2*(1+Real.log (2^(j+1)+radius : ℕ))^8) ≤ L^9 := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hN1 : (1 : ℝ) ≤ (2^(j+1)+radius : ℕ) := by
    exact_mod_cast (Nat.succ_le_of_lt (show 0 < 2^(j+1)+radius by positivity))
  have hN : ((2^(j+1)+radius : ℕ) : ℝ) ≤ 3*Real.exp (6*L) := by
    have hr' : (radius : ℝ) ≤ (2 : ℝ)^j := by exact_mod_cast hr
    push_cast
    rw [pow_succ]
    linarith
  have hnlog := Real.log_le_log (lt_of_lt_of_le zero_lt_one hN1) hN
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp] at hnlog
  have hbase0 : 0 ≤ 1+Real.log (2^(j+1)+radius : ℕ) := by
    linarith [Real.log_nonneg hN1]
  have hbase : 1+Real.log (2^(j+1)+radius : ℕ) ≤ 8*L := by linarith
  apply max_le
  · simpa using (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hL 9)
  · calc
      2*(1+Real.log (2^(j+1)+radius : ℕ))^8 ≤ 2*(8*L)^8 := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase0 hbase 8) (by norm_num)
      _ = (2*(8 : ℝ)^8)*L^8 := by ring
      _ ≤ L*L^8 := mul_le_mul_of_nonneg_right hconst (pow_nonneg hL0 _)
      _ = L^9 := by ring

theorem physical_dyadic_card_le_sq {L : ℝ} (hL : 1 ≤ L)
    (hc : 6/Real.log 2+1 ≤ L) (S : Finset ℤ)
    (hS : ∀ n ∈ S, 0 < n ∧ (n : ℝ) ≤ Real.exp (6*L)) :
    ((S.image (fun n => n.natAbs.log2)).card : ℝ) ≤ L^2 := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hb : ((S.image (fun n => n.natAbs.log2)).card : ℝ) ≤
      (Nat.floor (6*L/Real.log 2) : ℝ)+1 := by
    exact_mod_cast physical_dyadic_indices_card hS
  have hf := Nat.floor_le (show 0 ≤ 6*L/Real.log 2 by positivity)
  calc
    _ ≤ 6*L/Real.log 2+1 := hb.trans (by linarith)
    _ = (6/Real.log 2)*L+1 := by ring
    _ ≤ (6/Real.log 2+1)*L := by nlinarith
    _ ≤ L*L := mul_le_mul_of_nonneg_right hc hL0
    _ = L^2 := by ring

theorem physical_raw_prefactor_le {L U : ℝ} {N : ℕ}
    (hL : 0 ≤ L) (hN : (N : ℝ) ≤ L^2) (hU0 : 0 ≤ U) (hU : U ≤ L^9)
    (hcost : Real.exp 1*Real.sqrt 3 ≤ L) :
    (N : ℝ)*(Real.exp 1*Real.sqrt 3*U^2) ≤ L^21 := by
  have hinner := mul_le_mul hcost (pow_le_pow_left₀ hU0 hU 2) (sq_nonneg U) hL
  calc
    _ ≤ L^2*(L*(L^9)^2) :=
      mul_le_mul hN hinner (by positivity) (sq_nonneg L)
    _ = L^21 := by ring

theorem eventually_physical_residual_scalar_bounds :
    ∀ᶠ L : ℝ in atTop, ∀ S : Finset ℤ,
      (∀ n ∈ S, 0 < n ∧ (n : ℝ) ≤ Real.exp (6*L)) →
      ((S.image (fun n => n.natAbs.log2)).card : ℝ) ≤ L^2 ∧
      (∀ j ∈ S.image (fun n => n.natAbs.log2), ∀ radius : ℕ, radius ≤ 2^j →
        max 1 (2*(1+Real.log (2^(j+1)+radius : ℕ))^8) ≤ L^9) ∧
      ((S.image (fun n => n.natAbs.log2)).card : ℝ)*
        (Real.exp 1*Real.sqrt 3*(L^9)^2) ≤ L^21 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (2*(8 : ℝ)^8),
    eventually_ge_atTop (Real.log 3), eventually_ge_atTop (6/Real.log 2+1),
    eventually_ge_atTop (Real.exp 1*Real.sqrt 3)] with L hL hconst hlog hc hcost
  intro S hS
  have hcard := physical_dyadic_card_le_sq hL hc S hS
  refine ⟨hcard, ?_, physical_raw_prefactor_le (zero_le_one.trans hL) hcard
    (pow_nonneg (zero_le_one.trans hL) _) le_rfl hcost⟩
  intro j hj radius hr
  exact physical_dyadic_unit_allowance_le hL hconst hlog j radius hr
    (physical_dyadic_index_upper hS hj)

end Bounty


-- Source module: PhysicalResidualPolynomialSplit

/- Polynomial central and tail prefactors with only a bounded-frequency moment premise. -/

open Finset MeasureTheory
open scoped Classical
namespace Bounty

theorem physical_residual_polynomial_finite_moment
    {L : ℝ} (hL : 1 ≤ L) (hconst : 2*(8 : ℝ)^8 ≤ L)
    (hlog : Real.log 3 ≤ L) (hc : 6/Real.log 2+1 ≤ L)
    (hcost : Real.exp 1*Real.sqrt 3 ≤ L)
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ) (probes : G → Finset (Fin J))
    (r t : Finset G) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (a b Z : ℝ) (k : ℤ) (pool : Finset ℕ) (α β γ α' β' γ' : ℕ → ℂ)
    (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))
    (hprime : ∀ g p, p ∈ P g → p.Prime) (hpool : ∀ g, P g ⊆ pool)
    (hV : ∀ g, 0 < V g) (hMass : ∀ g, ∑ p ∈ P g, 1/(p : ℝ) = V g)
    (hα : ∀ n, ‖α n‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1) (hγ : ∀ n, ‖γ n‖ ≤ 1)
    (hα' : ∀ n, ‖α' n‖ ≤ 1) (hβ' : ∀ n, ‖β' n‖ ≤ 1) (hγ' : ∀ n, ‖γ' n‖ ≤ 1)
    (hZ : 0 < Z) (positions : Finset ℤ)
    (hpositions : ∀ n ∈ positions, 0 < n ∧ (n : ℝ) ≤ Real.exp (6*L))
    (hclosure : physicalSignedHarmonicPositions (ell := ell) P probes r t Z k ⊆ positions)
    (R D : ℕ) (hR : 2 ≤ R) (hD : 0 < D)
    (hstep : physicalOperatorStepBound P J ell
      (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
      (repeatedBigPrimePatternCut probes r t) (fun _ => k) ≤ D)
    (hr : ∀ j ∈ positions.image (fun n => n.natAbs.log2), 2*R*D ≤ 2^j)
    (M : ℕ → ℝ) (W : ℝ) (T E : ℝ → ℝ)
    (hM : ∀ j ∈ positions.image (fun n => n.natAbs.log2), 0 ≤ M j)
    (hT : ∀ᵐ v : ℝ, ‖v‖ ≤ W → 0 ≤ T v)
    (hE : ∀ᵐ v : ℝ, 0 ≤ E v)
    (hsource : ∀ j ∈ positions.image (fun n => n.natAbs.log2),
      ∀ n ∈ physicalDyadicStarts j, ‖invariantTripleEndpoint pool α β γ n.natAbs‖ ≤ M j)
    (hblock : ∀ j ∈ positions.image (fun n => n.natAbs.log2),
      ((D : ℝ)*(M j)^2)^(1/(2*(R : ℝ))) ≤ Real.exp 1)
    (hmoment : ∀ j ∈ positions.image (fun n => n.natAbs.log2), ∀ᵐ v : ℝ, ‖v‖ ≤ W →
      (physicalRootMoment V
        (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
        (repeatedBigPrimePatternCut probes r t) (1/2)
        (fun e _ => if e % 2 = 0 then -(-(a+b)-2*Real.pi*v) else -(a+b)-2*Real.pi*v)
        (fun e _ => if e % 2 = 0 then -k else k)
        (fun e i x y aux => if e % 2 = 0 then
          (starRingEnd ℂ) (physicalRootPrimeKernel P V probes r t hrt Q h ξ i y x aux)
          else physicalRootPrimeKernel P V probes r t hrt Q h ξ i x y aux)
        (physicalDyadicStarts j) (2*R-1) D).re ≤ (T v)^(2*R))
    (htail : ∀ j ∈ positions.image (fun n => n.natAbs.log2), ∀ᵐ v : ℝ,
      ‖physicalMellinPairing V
        (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
        (repeatedBigPrimePatternCut probes r t) (1/2) (fun _ => -(a+b)) (fun _ => k)
        (physicalRootPrimeKernel P V probes r t hrt Q h ξ)
        (reachablePositions (physicalDyadicStarts j) (2*R*D))
        (physicalPositionMask positions (physicalDyadicSource j
          (fun n => physicalPhase (-a) n.natAbs * positiveInvariantEndpoint pool α β γ n)))
        (physicalPositionMask positions
          (fun n => physicalPhase b n.natAbs * positiveInvariantEndpoint pool α' β' γ' n))
        ((2 : ℝ)^j) Z (2*Real.pi*v)‖ ≤ (2 : ℝ)^j * E v)
    (hEnvelope : IntegrableOn (fun v => ‖harmonicLogFourier v‖ * T v) {v | ‖v‖ ≤ W})
    (hTailEnvelope : IntegrableOn (fun v => ‖harmonicLogFourier v‖ * E v) {v | ‖v‖ ≤ W}ᶜ) :
    ‖physicalSignedPositiveHarmonicResidual (ell := ell) P V probes r t hrt Q h ξ a b Z k
      pool α β γ α' β' γ'‖ ≤
      L^21 * (∫ v in {v : ℝ | ‖v‖ ≤ W}, ‖harmonicLogFourier v‖ * T v) +
        L^2 * ∫ v in {v : ℝ | ‖v‖ ≤ W}ᶜ, ‖harmonicLogFourier v‖ * E v := by
  have hallow : ∀ j ∈ positions.image (fun n => n.natAbs.log2),
      max 1 (2*((1 : ℝ)*1*1*(1+Real.log (2^(j+1)+2*R*D : ℕ))^8)) ≤ L^9 := by
    intro j hj
    simpa only [one_mul] using physical_dyadic_unit_allowance_le hL hconst hlog j
      (2*R*D) (hr j hj) (physical_dyadic_index_upper hpositions hj)
  have hp := physical_residual_finite_moment_envelope P V probes r t hrt Q h ξ
    a b Z k pool α β γ α' β' γ' hdis hprime hpool hV hMass
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) ≤ 1) hα hβ hγ hα' hβ' hγ' hZ positions hclosure
    R D hR hD hstep hr M (Real.exp 1) (L^9) W T E (le_of_lt (Real.exp_pos _))
    hM hT hsource hblock hmoment hallow htail hEnvelope hTailEnvelope
  have hcard := physical_dyadic_card_le_sq hL hc positions hpositions
  have hfactor := physical_raw_prefactor_le (zero_le_one.trans hL) hcard
    (pow_nonneg (zero_le_one.trans hL) 9) (le_refl (L^9)) hcost
  have hs : MeasurableSet {v : ℝ | ‖v‖ ≤ W} :=
    (isClosed_le continuous_norm continuous_const).measurableSet
  have hIntegral : 0 ≤ ∫ v in {v : ℝ | ‖v‖ ≤ W}, ‖harmonicLogFourier v‖ * T v := by
    apply integral_nonneg_of_ae
    filter_upwards [hT.filter_mono ae_restrict_le, ae_restrict_mem hs] with v hv hm
    exact mul_nonneg (norm_nonneg _) (hv hm)
  have hTailIntegral : 0 ≤ ∫ v in {v : ℝ | ‖v‖ ≤ W}ᶜ, ‖harmonicLogFourier v‖ * E v := by
    apply integral_nonneg_of_ae
    filter_upwards [hE.filter_mono ae_restrict_le] with v hv
    exact mul_nonneg (norm_nonneg _) hv
  apply hp.trans
  rw [mul_add, ← mul_assoc]
  exact add_le_add (mul_le_mul_of_nonneg_right hfactor hIntegral)
    (mul_le_mul_of_nonneg_right hcard hTailIntegral)

end Bounty


-- Source module: PhysicalResidualScalarDecay

/- A finite central saving and a polynomial direct tail give arbitrary decay after integration. -/

open MeasureTheory Filter
namespace Bounty

theorem eventually_physical_residual_scalar_decay {r : ℝ} (hr : 0 < r) (C D : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      L^21 * (∫ v in {v : ℝ | ‖v‖ ≤ L^r}, ‖harmonicLogFourier v‖ * L^(-(D+23))) +
        L^2 * (∫ v in {v : ℝ | ‖v‖ ≤ L^r}ᶜ, ‖harmonicLogFourier v‖ * L^C) ≤ L^(-D) := by
  filter_upwards [eventually_harmonic_mellin_tail_power hr (C+2) (D+1),
    eventually_ge_atTop (2 : ℝ), eventually_ge_atTop (∫ v : ℝ, ‖harmonicLogFourier v‖)]
    with L htail hL hmass
  have hL0 : 0 < L := by linarith
  have hcentral : (∫ v in {v : ℝ | ‖v‖ ≤ L^r}, ‖harmonicLogFourier v‖) ≤ L := by
    exact (setIntegral_le_integral harmonic_log_fourier_integrable.norm
      (Filter.Eventually.of_forall (fun v => norm_nonneg (harmonicLogFourier v)))).trans hmass
  have hc : L^21 * (∫ v in {v : ℝ | ‖v‖ ≤ L^r},
      ‖harmonicLogFourier v‖ * L^(-(D+23))) ≤ L^(-(D+1)) := by
    rw [integral_mul_const]
    calc
      _ ≤ L^21 * (L * L^(-(D+23))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hcentral (Real.rpow_pos_of_pos hL0 _).le)
          (pow_nonneg hL0.le _)
      _ = L^(-(D+1)) := by
        calc
          _ = L^(21 : ℝ) * (L^(1 : ℝ) * L^(-(D+23))) := by
            rw [Real.rpow_ofNat, Real.rpow_one]
          _ = _ := by
            rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
            congr 1
            ring
  have heq : {v : ℝ | ‖v‖ ≤ L^r}ᶜ = {v : ℝ | L^r < ‖v‖} := by ext v; simp
  have ht : L^2 * (∫ v in {v : ℝ | ‖v‖ ≤ L^r}ᶜ,
      ‖harmonicLogFourier v‖ * L^C) ≤ L^(-(D+1)) := by
    rw [heq, integral_mul_const]
    convert htail (L^(C+2)) (Real.rpow_pos_of_pos hL0 _).le le_rfl using 1
    rw [Real.rpow_add hL0, Real.rpow_ofNat]
    ring
  calc
    _ ≤ L^(-(D+1)) + L^(-(D+1)) := add_le_add hc ht
    _ = 2 * L^(-(D+1)) := by ring
    _ ≤ L * L^(-(D+1)) :=
      mul_le_mul_of_nonneg_right hL (Real.rpow_pos_of_pos hL0 _).le
    _ = L^(-D) := by
      calc
        _ = L^(1 : ℝ) * L^(-(D+1)) := by rw [Real.rpow_one]
        _ = _ := by
          rw [← Real.rpow_add hL0]
          congr 1
          ring

end Bounty


-- Source module: FiniteKernelSchurNorm

/- The finite Schur estimate controls the actual Euclidean kernel operator. -/

open Finset
open scoped Classical
namespace Bounty

theorem finite_kernel_schur_norm {X : Type*} [Fintype X]
    (K : X → X → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (hrow : ∀ x, ∑ y, ‖K x y‖ ≤ A)
    (hcol : ∀ y, ∑ x, ‖K x y‖ ≤ A) (f : EuclideanSpace ℂ X) :
    ‖finiteKernelOperator K f‖ ≤ A*‖f‖ := by
  have h := constant_measure_schur univ K (μ := 1) zero_le_one
    (fun x _ => hrow x) (fun y _ => hcol y) f
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hA (norm_nonneg f))).mp
  simpa only [EuclideanSpace.norm_sq_eq, finite_kernel_operator_apply, one_mul, mul_pow] using h

end Bounty


-- Source module: PhysicalHilbertSchur

/- Uniform Schur bounds for the literal physical Hilbert operator at every frequency. -/

open Finset
open scoped Classical
namespace Bounty

theorem exists_physical_hilbert_schur_bound {q v : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hv : 0 < v) (ell m : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (G : Type) [Fintype G] [DecidableEq G] (P : G → Finset ℕ)
      (J : ℕ) (V : G → ℝ), (∀ g, v ≤ V g) →
      (∀ g, ∑ p ∈ P g, 1/(p : ℝ) = V g) →
      ∀ (I : Type) (patterns : Finset I) (C : I → G → Finset (Fin J))
        (ζ : I → ℝ) (k : I → ℤ)
        (K : ∀ i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell → PhysicalAuxLabels P (C i) → ℂ)
        (B : I → ℝ),
        (∀ i ∈ patterns, ∀ g, (C i g).card ≤ m) →
        (∀ i ∈ patterns, 0 ≤ B i) →
        (∀ i ∈ patterns, ∀ a b aux, ‖K i a b aux‖ ≤ B i) →
        ∀ (positions : Finset ℤ) (f : EuclideanSpace ℂ (physicalCutoff P J ell positions)),
        ‖physicalHilbertOperator V patterns C q ζ k K positions f‖ ≤
          ((∑ i ∈ patterns, B i)*A^(Fintype.card G))*‖f‖ := by
  obtain ⟨A, hA, hbound⟩ := exists_physical_operator_bounds hq0 hq1 hv ell m
  refine ⟨A, hA, ?_⟩
  intro G _ _ P J V hV hMass I patterns C ζ k K B hC hB hK positions f
  apply finite_kernel_schur_norm _
    (mul_nonneg (sum_nonneg hB) (pow_nonneg (zero_le_one.trans hA) _))
  · intro x
    rw [sum_coe_sort (physicalCutoff P J ell positions)
      (fun y => ‖physicalSymmetricKernel (fun a b => ∑ i ∈ patterns,
        physicalPatternKernel V (C i) q (ζ i) (k i) (K i) a b) x.val y‖)]
    exact (hbound G P J V hV hMass I patterns C ζ k K B hC hB hK x.val
      (physicalCutoff P J ell positions)).1
  · intro y
    rw [sum_coe_sort (physicalCutoff P J ell positions)
      (fun x => ‖physicalSymmetricKernel (fun a b => ∑ i ∈ patterns,
        physicalPatternKernel V (C i) q (ζ i) (k i) (K i) a b) x y.val‖)]
    exact (hbound G P J V hV hMass I patterns C ζ k K B hC hB hK y.val
      (physicalCutoff P J ell positions)).2

end Bounty


-- Source module: CandidateHilbertPolynomial

/- The literal signed candidate kernel has an absolute polynomial operator bound. -/

open Finset Filter
open scoped Classical
namespace Bounty

theorem exists_candidate_hilbert_polynomial {c q x : ℝ}
    (hc : 0 < c) (hq : 0 ≤ q) (hx : 0 ≤ x) (J ell : ℕ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (S : Finset ℕ), S ⊆ candidatePIndices c L →
      ∀ (probes : S → Finset (Fin J)) (r t : Finset S) (hrt : Disjoint r t)
        (Q : ℕ) (h ξ : ℝ), (Q : ℝ) ≤ L^q → L^(-x) ≤ ξ →
      let P := fun g : S => candidatePBand (c*L) g.val
      let V := fun g : S => ∑ p ∈ P g, 1/(p : ℝ)
      ∀ ζ : RepeatedBigPrimePatternIndex (ell := ell) probes r t → ℝ,
      ∀ k : RepeatedBigPrimePatternIndex (ell := ell) probes r t → ℤ,
      ∀ (positions : Finset ℤ) (f : EuclideanSpace ℂ (physicalCutoff P J ell positions)),
      ‖physicalHilbertOperator V univ (repeatedBigPrimePatternCut probes r t) (1/2) ζ k
        (physicalRootPrimeKernel P V probes r t hrt Q h ξ) positions f‖ ≤ L^E*‖f‖ := by
  obtain ⟨v, A₀, hv, hA₀, hinput⟩ := exists_candidate_shared_error_inputs hc J
  obtain ⟨v₁, A₁, _, hA₁, hcount⟩ := exists_candidate_shared_error_inputs hc 1
  obtain ⟨A, hA, hschur⟩ := exists_physical_hilbert_schur_bound
    (q := (1/2 : ℝ)) (by norm_num) (by norm_num) hv ell J
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  refine ⟨(A₀*Real.log 2+1+(4*q+2*x))+(A₁*Real.log A), by positivity, ?_⟩
  filter_upwards [hinput, hcount, eventually_ge_atTop (2 : ℝ)] with L hinput hcount hL
  intro S hS probes r t hrt Q h ξ hQ hξ P V ζ k positions f
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hξ0 : 0 < ξ := (Real.rpow_pos_of_pos hL0 (-x)).trans_le hξ
  have hslots : ((J*Fintype.card S : ℕ) : ℝ) ≤ A₀*Real.log L := by
    simpa only [Fintype.card_coe] using (hinput S hS).1
  have hcard : (Fintype.card S : ℝ) ≤ A₁*Real.log L := by
    simpa only [Nat.one_mul, Fintype.card_coe] using (hcount S hS).1
  have hp := harmonic_pattern_card_power (ell := ell) probes r t hrt hL hA₀ hslots
  have hK : ∀ i ∈ (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t)),
      ∀ a b aux, ‖physicalRootPrimeKernel P V probes r t hrt Q h ξ i a b aux‖ ≤ L^(4*q+2*x) := by
    intro i _ a b aux
    have hi := repeated_big_prime_pattern_kernel_norm_le P V probes r t hrt Q h ξ hξ0 i
      (fun g s => a g s) (fun g s => b g s) aux
    rw [physicalRootPrimeKernel, norm_mul, repeated_big_prime_pattern_weight_norm, one_mul]
    exact hi.trans (harmonic_pattern_bound_power probes r t hL1 hq hx Q hQ hξ i)
  have hs := hschur S P J V (fun g => ((hinput S hS).2 g).1) (fun _ => rfl)
    (RepeatedBigPrimePatternIndex (ell := ell) probes r t) univ
    (repeatedBigPrimePatternCut probes r t) ζ k
    (physicalRootPrimeKernel P V probes r t hrt Q h ξ) (fun _ => L^(4*q+2*x))
    (fun i _ g => by simpa only [Fintype.card_fin] using (card_le_univ (repeatedBigPrimePatternCut probes r t i g))) (fun _ _ => Real.rpow_nonneg hL0.le _) hK positions f
  have hpow : A^(Fintype.card S) ≤ L^(A₁*Real.log A) := by
    calc
      _ = Real.exp (Real.log A*(Fintype.card S : ℝ)) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hA)]
      _ ≤ Real.exp (Real.log A*(A₁*Real.log L)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcard hlogA)
      _ = _ := by rw [Real.rpow_def_of_pos hL0]; congr 1; ring
  have hsum : (∑ _i : RepeatedBigPrimePatternIndex (ell := ell) probes r t, L^(4*q+2*x)) ≤
      L^(A₀*Real.log 2+1+(4*q+2*x)) := by
    simp only [sum_const, card_univ, nsmul_eq_mul]
    calc
      _ ≤ L^(A₀*Real.log 2+1)*L^(4*q+2*x) :=
        mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hL0.le _)
      _ = _ := (Real.rpow_add hL0 _ _).symm
  apply hs.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
  calc
    _ ≤ L^(A₀*Real.log 2+1+(4*q+2*x))*L^(A₁*Real.log A) :=
      mul_le_mul hsum hpow (pow_nonneg (zero_le_one.trans hA) _) (Real.rpow_nonneg hL0.le _)
    _ = _ := (Real.rpow_add hL0 _ _).symm

end Bounty


-- Source module: PhysicalRawDyadicAbsolute

/- A direct all-frequency pairing envelope from an absolute operator bound. -/

open Finset
open scoped Classical InnerProductSpace
namespace Bounty

theorem physical_raw_dyadic_absolute_bound
    {G I : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (hP : Pairwise (fun g h => Disjoint (P g) (P h)))
    (hprime : ∀ g p, p ∈ P g → p.Prime)
    (V : G → ℝ) (hV : ∀ g, 0 < V g) (hMass : ∀ g, ∑ p ∈ P g, 1/(p : ℝ) = V g)
    (patterns : Finset I) (C : I → G → Finset (Fin J)) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ζ : I → ℝ) (k : I → ℤ)
    (K : ∀ i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell → PhysicalAuxLabels P (C i) → ℂ)
    (pool : Finset ℕ) (hpool : ∀ g, P g ⊆ pool) (α β γ α' β' γ' : ℕ → ℂ)
    {A B C₀ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C₀)
    (hα : ∀ m, ‖α m‖ ≤ A) (hβ : ∀ p, ‖β p‖ ≤ B) (hγ : ∀ r, ‖γ r‖ ≤ C₀)
    (hα' : ∀ m, ‖α' m‖ ≤ A) (hβ' : ∀ p, ‖β' p‖ ≤ B) (hγ' : ∀ r, ‖γ' r‖ ≤ C₀)
    (S : Finset ℤ) (j radius : ℕ) (hr : radius ≤ 2^j) (a c Z v H : ℝ) (hH : 0 ≤ H)
    (hop : ∀ f : EuclideanSpace ℂ (physicalCutoff P J ell
        (reachablePositions (physicalDyadicStarts j) radius)),
      ‖physicalHilbertOperator V patterns C q (fun i => ζ i-v) k K
        (reachablePositions (physicalDyadicStarts j) radius) f‖ ≤ H*‖f‖) :
    let f := physicalPositionMask S (physicalDyadicSource j
      (fun n => physicalPhase a n.natAbs * positiveInvariantEndpoint pool α β γ n))
    let g := physicalPositionMask S
      (fun n => physicalPhase c n.natAbs * positiveInvariantEndpoint pool α' β' γ' n)
    let U := max 1 (2*(A*B*C₀*(1+Real.log (2^(j+1)+radius : ℕ))^8))
    ‖physicalMellinPairing V patterns C q ζ k K
      (reachablePositions (physicalDyadicStarts j) radius) f g ((2 : ℝ)^j) Z v‖ ≤
      (2 : ℝ)^j*(H*U^2) := by
  dsimp only
  let positions := reachablePositions (physicalDyadicStarts j) radius
  let F := physicalEndpointVector P V J ell q positions
    (physicalMellinSource ((2 : ℝ)^j) Z v
      (physicalPositionMask S (physicalDyadicSource j
        (fun n => physicalPhase a n.natAbs * positiveInvariantEndpoint pool α β γ n))))
  let G₀ := physicalEndpointVector P V J ell q positions
    (physicalPositionMask S
      (fun n => physicalPhase c n.natAbs * positiveInvariantEndpoint pool α' β' γ' n))
  let E := A*B*C₀*Real.sqrt (2^(j+1)+radius : ℕ)*(1+Real.log (2^(j+1)+radius : ℕ))^8
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hs : ‖F‖ ≤ E := physical_raw_mellin_source_endpoint_norm P hP hprime V hV hMass
    pool hpool α β γ hA hB hC hα hβ hγ J ell hq0 hq1 S j radius hr a Z v
  have ht : ‖G₀‖ ≤ E := physical_raw_target_endpoint_norm P hP hprime V hV hMass
    pool hpool α' β' γ' hA hB hC hα' hβ' hγ' J ell hq0 hq1 S j radius hr c
  have henergy := physical_dyadic_endpoint_energy_sq j radius hr hA hB hC
  change ‖inner ℂ F (physicalHilbertOperator V patterns C q (fun i => ζ i-v) k K positions G₀)‖ ≤ _
  calc
    _ ≤ ‖F‖*‖physicalHilbertOperator V patterns C q (fun i => ζ i-v) k K positions G₀‖ :=
      norm_inner_le_norm _ _
    _ ≤ E*(H*E) := mul_le_mul hs
      ((hop G₀).trans (mul_le_mul_of_nonneg_left ht hH)) (norm_nonneg _) hE
    _ = H*E^2 := by ring
    _ ≤ H*((2 : ℝ)^j*(max 1 (2*(A*B*C₀*(1+Real.log (2^(j+1)+radius : ℕ))^8)))^2) :=
      mul_le_mul_of_nonneg_left henergy hH
    _ = _ := by ring

end Bounty


-- Source module: CandidateDyadicAbsolute

/- A polynomial all-frequency envelope for the actual candidate Mellin pairing. -/

open Finset Filter
open scoped Classical
namespace Bounty

theorem exists_candidate_dyadic_absolute_envelope {c q x : ℝ}
    (hc : 0 < c) (hq : 0 ≤ q) (hx : 0 ≤ x) (J ell : ℕ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (S : Finset ℕ), S ⊆ candidatePIndices c L →
      ∀ (probes : S → Finset (Fin J)) (r t : Finset S) (hrt : Disjoint r t)
        (Q : ℕ) (h ξ : ℝ), (Q : ℝ) ≤ L^q → L^(-x) ≤ ξ →
      let P := fun g : S => candidatePBand (c*L) g.val
      let V := fun g : S => ∑ p ∈ P g, 1/(p : ℝ)
      ∀ (pool : Finset ℕ), (∀ g, P g ⊆ pool) →
      ∀ (α β γ α' β' γ' : ℕ → ℂ),
      (∀ n, ‖α n‖ ≤ 1) → (∀ n, ‖β n‖ ≤ 1) → (∀ n, ‖γ n‖ ≤ 1) →
      (∀ n, ‖α' n‖ ≤ 1) → (∀ n, ‖β' n‖ ≤ 1) → (∀ n, ‖γ' n‖ ≤ 1) →
      ∀ (positions : Finset ℤ) (i radius : ℕ), radius ≤ 2^i →
      (2 : ℝ)^i ≤ Real.exp (6*L) →
      ∀ (ζ a a' Z v : ℝ) (k : ℤ),
      ‖physicalMellinPairing (ell := ell) V univ (repeatedBigPrimePatternCut probes r t) (1/2)
        (fun _ => ζ) (fun _ => k) (physicalRootPrimeKernel P V probes r t hrt Q h ξ)
        (reachablePositions (physicalDyadicStarts i) radius)
        (physicalPositionMask positions (physicalDyadicSource i
          (fun n => physicalPhase a n.natAbs * positiveInvariantEndpoint pool α β γ n)))
        (physicalPositionMask positions
          (fun n => physicalPhase a' n.natAbs * positiveInvariantEndpoint pool α' β' γ' n))
        ((2 : ℝ)^i) Z (2*Real.pi*v)‖ ≤ (2 : ℝ)^i*L^E := by
  obtain ⟨E₀, hE₀, hop⟩ := exists_candidate_hilbert_polynomial hc hq hx J ell
  obtain ⟨v₀, A, hv₀, _, hinput⟩ := exists_candidate_shared_error_inputs hc J
  refine ⟨E₀+18, by linarith, ?_⟩
  filter_upwards [hop, hinput, eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (2*(8 : ℝ)^8), eventually_ge_atTop (Real.log 3)]
    with L hop hinput hL hconst hlog
  intro S hS probes r t hrt Q h ξ hQ hξ P V pool hpool α β γ α' β' γ'
    hα hβ hγ hα' hβ' hγ' positions i radius hr hi ζ a a' Z v k
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hdis : Pairwise (fun g h => Disjoint (P g) (P h)) := by
    intro g g' hgg'
    exact pairwise_disjoint_dyadicPrimeBand (mul_nonneg hc.le hL0.le)
      (by norm_num : (0 : ℝ) ≤ 3/2) (by norm_num : (9/5 : ℝ) ≤ 2*(3/2))
      (Subtype.val_injective.ne hgg')
  have hprime : ∀ g p, p ∈ P g → p.Prime := by
    intro g p hp
    exact ((hinput S hS).2 g).2 p hp |>.1
  have hV : ∀ g, 0 < V g := fun g => hv₀.trans_le ((hinput S hS).2 g).1
  have hb := physical_raw_dyadic_absolute_bound (ell := ell) P hdis hprime V hV (fun _ => rfl)
    univ (repeatedBigPrimePatternCut probes r t) (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) ≤ 1) (fun _ => ζ) (fun _ => k)
    (physicalRootPrimeKernel P V probes r t hrt Q h ξ) pool hpool α β γ α' β' γ'
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
    hα hβ hγ hα' hβ' hγ' positions i radius hr a a' Z (2*Real.pi*v) (L^E₀)
    (Real.rpow_nonneg hL0.le _)
    (hop S hS probes r t hrt Q h ξ hQ hξ (fun _ => ζ-2*Real.pi*v) (fun _ => k) _)
  dsimp only at hb
  simp only [one_mul] at hb
  have hU := physical_dyadic_unit_allowance_le hL hconst hlog i radius hr hi
  apply hb.trans
  calc
    _ ≤ (2 : ℝ)^i*(L^E₀*(L^9)^2) := by gcongr
    _ = (2 : ℝ)^i*L^(E₀+18) := by
      rw [show (L^9)^2 = L^18 by ring, ← Real.rpow_natCast L 18, ← Real.rpow_add hL0]
      norm_num

end Bounty


-- Source module: InvariantRoughSupremum

/- Rough coefficients give the square-root exponential supremum used in block moments. -/

open Finset
namespace Bounty

theorem invariant_triple_endpoint_rough_exp {W : ℝ} (hW : 1 < W)
    (pool : Finset ℕ) (α β γ : ℕ → ℂ) {A B C : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hα : ∀ m, ‖α m‖ ≤ A) (hβ : ∀ p, ‖β p‖ ≤ B) (hγ : ∀ r, ‖γ r‖ ≤ C)
    (hαrough : ∀ m, ¬ (∀ p : ℕ, p ∈ m.primeFactors → W ≤ (p : ℝ)) → α m = 0)
    (hβrough : ∀ m, ¬ (∀ p : ℕ, p ∈ m.primeFactors → W ≤ (p : ℝ)) → β m = 0)
    {n : ℕ} (hn : n ≠ 0) :
    ‖invariantTripleEndpoint pool α β γ n‖ ≤
      A*B*C*Real.exp (2*(Real.log 2*Real.log n/Real.log W)) := by
  have hb := endpoint_triple_convolution_rough_exp hW α β γ hA hB hC
    hα hβ hγ hαrough hβrough (primePoolFreePart_ne_zero pool hn)
  apply hb.trans
  have hpos : (0 : ℝ) < primePoolFreePart pool n := by
    exact_mod_cast Nat.pos_of_ne_zero (primePoolFreePart_ne_zero pool hn)
  have hle : (primePoolFreePart pool n : ℝ) ≤ n := by
    exact_mod_cast (Nat.div_le_self n (primePoolPart pool n))
  have hlog := Real.log_le_log hpos hle
  have hlogW : 0 ≤ Real.log W := (Real.log_pos hW).le
  gcongr

theorem invariant_triple_endpoint_sqrt_bound {L C : ℝ} (hL : 0 < L)
    (pool : Finset ℕ) (α β γ : ℕ → ℂ)
    (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ p, ‖β p‖ ≤ 1) (hγ : ∀ r, ‖γ r‖ ≤ 1)
    (hαrough : ∀ m, ¬ (∀ p : ℕ, p ∈ m.primeFactors → Real.exp (Real.sqrt L) ≤ (p : ℝ)) → α m = 0)
    (hβrough : ∀ m, ¬ (∀ p : ℕ, p ∈ m.primeFactors → Real.exp (Real.sqrt L) ≤ (p : ℝ)) → β m = 0)
    {n : ℕ} (hn : n ≠ 0) (hlog : Real.log n ≤ C*L) :
    ‖invariantTripleEndpoint pool α β γ n‖ ≤ Real.exp ((2*Real.log 2*C)*Real.sqrt L) := by
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hb := invariant_triple_endpoint_rough_exp (Real.one_lt_exp_iff.mpr hs)
    pool α β γ zero_le_one zero_le_one zero_le_one hα hβ hγ hαrough hβrough hn
  simp only [one_mul, Real.log_exp] at hb
  apply hb.trans
  apply Real.exp_le_exp.mpr
  have hratio : Real.log n/Real.sqrt L ≤ C*Real.sqrt L := by
    apply (div_le_iff₀ hs).mpr
    calc
      Real.log n ≤ C*L := hlog
      _ = C*Real.sqrt L*Real.sqrt L := by
        rw [mul_assoc, ← pow_two, Real.sq_sqrt hL.le]
  have hh := mul_le_mul_of_nonneg_left hratio (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  rw [← mul_div_assoc] at hh
  nlinarith

theorem invariant_triple_endpoint_dyadic_sqrt_bound {L a : ℝ} (hL : 0 < L)
    (hlogL : Real.log 2 ≤ L) (pool : Finset ℕ) (α β γ : ℕ → ℂ)
    (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ p, ‖β p‖ ≤ 1) (hγ : ∀ r, ‖γ r‖ ≤ 1)
    (hαrough : ∀ m, ¬ (∀ p : ℕ, p ∈ m.primeFactors → Real.exp (Real.sqrt L) ≤ (p : ℝ)) → α m = 0)
    (hβrough : ∀ m, ¬ (∀ p : ℕ, p ∈ m.primeFactors → Real.exp (Real.sqrt L) ≤ (p : ℝ)) → β m = 0)
    {j : ℕ} (hj : (2 : ℝ)^j ≤ Real.exp (a*L)) {n : ℤ}
    (hn : n ∈ physicalDyadicStarts j) :
    ‖invariantTripleEndpoint pool α β γ n.natAbs‖ ≤
      Real.exp ((2*Real.log 2*(a+1))*Real.sqrt L) := by
  obtain ⟨hn0, hlog⟩ := physical_dyadic_log_upper hj hn
  apply invariant_triple_endpoint_sqrt_bound hL pool α β γ hα hβ hγ hαrough hβrough
    (Int.natAbs_ne_zero.mpr hn0.ne')
  linarith

end Bounty


-- Source module: ActualFiniteResidual

/- A central-frequency original moment bound implies decay of the actual signed residual. -/

open Finset Filter MeasureTheory
open scoped Classical
namespace Bounty

theorem eventually_actual_residual_of_central_moment {c b K q x η : ℝ}
    (hc : 0 < c) (hb : 0 < b) (hK : 0 ≤ K)
    (hq : 0 ≤ q) (hx : 0 ≤ x) (hη : 0 < η) (J ell : ℕ) (F : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (S : Finset ℕ), S ⊆ candidatePIndices c L →
      ∀ (probes : S → Finset (Fin J)) (r t : Finset S)
        (hrt : Disjoint r t) (Q : ℕ) (h ξ a a' : ℝ),
      (Q : ℝ) ≤ L^q → L^(-x) ≤ ξ →
      ∀ U W : ℝ, Real.exp (b*L) ≤ U → U ≤ Real.exp L →
        Real.exp (b*L) ≤ W → W ≤ Real.exp L →
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L K : ℤ))
        (typeIIAdmissibleDeterminantBound L K : ℤ),
      ∀ j ∈ range (typeIISmoothDyadicCount L),
      let P := fun g : S => candidatePBand (c*L) g.val
      let V := fun g : S => ∑ p ∈ P g, 1/(p : ℝ)
      let Z := typeIISmoothDyadicScale U W (U*L^(-K)) j
      let R := Nat.ceil (L^(13/25 : ℝ))
      let D := max 1 (physicalOperatorStepBound P J ell
        (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
        (repeatedBigPrimePatternCut probes r t) (fun _ => k))
      let positions := physicalSignedHarmonicPositions (ell := ell) P probes r t Z k
      ∀ (pool : Finset ℕ), (∀ g, P g ⊆ pool) →
      ∀ (α β γ α' β' γ' : ℕ → ℂ),
      (∀ n, ‖α n‖ ≤ 1) → (∀ n, ‖β n‖ ≤ 1) → (∀ n, ‖γ n‖ ≤ 1) →
      (∀ n, ‖α' n‖ ≤ 1) → (∀ n, ‖β' n‖ ≤ 1) → (∀ n, ‖γ' n‖ ≤ 1) →
      (∀ n, ¬ (∀ p : ℕ, p ∈ n.primeFactors → Real.exp (Real.sqrt L) ≤ (p : ℝ)) → α n = 0) →
      (∀ n, ¬ (∀ p : ℕ, p ∈ n.primeFactors → Real.exp (Real.sqrt L) ≤ (p : ℝ)) → β n = 0) →
      (∀ i ∈ positions.image (fun n => n.natAbs.log2), ∀ᵐ v : ℝ, ‖v‖ ≤ L^η →
        (physicalRootMoment V
          (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
          (repeatedBigPrimePatternCut probes r t) (1/2)
          (fun e _ => if e % 2 = 0 then -(-(a+a')-2*Real.pi*v) else -(a+a')-2*Real.pi*v)
          (fun e _ => if e % 2 = 0 then -k else k)
          (fun e i x y aux => if e % 2 = 0 then
            (starRingEnd ℂ) (physicalRootPrimeKernel P V probes r t hrt Q h ξ i y x aux)
            else physicalRootPrimeKernel P V probes r t hrt Q h ξ i x y aux)
          (physicalDyadicStarts i) (2*R-1) D).re ≤ (L^(-(F+23)))^(2*R)) →
      ‖physicalSignedPositiveHarmonicResidual (ell := ell) P V probes r t hrt Q h ξ
        a a' Z k pool α β γ α' β' γ'‖ ≤
        L^(-F) := by
  obtain ⟨E, _, hop⟩ := exists_candidate_dyadic_absolute_envelope hc hq hx J ell
  obtain ⟨v₀, A, hv₀, _, hinput⟩ := exists_candidate_shared_error_inputs hc J
  filter_upwards [hinput, hop, eventually_physical_residual_scalar_decay hη E F,
    eventually_actual_raw_dyadic_radius hc hb hK J,
    eventually_actual_raw_block_cost hc hK J,
    eventually_actual_harmonic_positions_bounds hc hb hK J,
    eventually_actual_harmonic_scale_inputs hb hK,
    eventually_raw_moment_at_least_two,
    eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (2*(8 : ℝ)^8),
    eventually_ge_atTop (Real.log 3), eventually_ge_atTop (6/Real.log 2+1),
    eventually_ge_atTop (Real.exp 1*Real.sqrt 3), eventually_ge_atTop (Real.log 2)]
    with L hinput hop hdecay hradius hblock hpositions hscale hR hL hconst hlog hcard hcost hlog2
  intro S hS probes r t hrt Q h ξ a a' hQ hξ U W hUlo hUhi hWlo hWhi k hk j hj
    P V Z R D positions pool hpool α β γ α' β' γ' hα hβ hγ hα' hβ' hγ'
    hαrough hβrough hmoment
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hdis : Pairwise (fun g h => Disjoint (P g) (P h)) := by
    intro g g' hgg'
    exact pairwise_disjoint_dyadicPrimeBand (mul_nonneg hc.le hL0.le)
      (by norm_num : (0 : ℝ) ≤ 3/2) (by norm_num : (9/5 : ℝ) ≤ 2*(3/2))
      (Subtype.val_injective.ne hgg')
  have hprime : ∀ g p, p ∈ P g → p.Prime := by
    intro g p hp
    exact ((hinput S hS).2 g).2 p hp |>.1
  have hV : ∀ g, 0 < V g := fun g => hv₀.trans_le ((hinput S hS).2 g).1
  have hpos : ∀ n ∈ positions, 0 < n ∧ (n : ℝ) ≤ Real.exp (6*L) :=
    hpositions S hS ell probes r t U W hUlo hUhi hWlo hWhi k hk j hj
  have hD : 0 < D := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hZ : 0 < Z := (hscale U W hUlo hUhi hWlo hWhi k hk j hj).1
  apply le_trans (physical_residual_polynomial_finite_moment hL hconst hlog hcard hcost
    P V probes r t hrt Q h ξ a a' Z k pool α β γ α' β' γ'
    hdis hprime hpool hV (fun _ => rfl) hα hβ hγ hα' hβ' hγ' hZ positions hpos
    (Subset.refl _) R D hR hD (le_max_right _ _)
    (hradius S hS ell probes r t U W hUlo hUhi hWlo hWhi k hk j hj)
    (fun _ => Real.exp ((14*Real.log 2)*Real.sqrt L)) (L^η)
    (fun _ => L^(-(F+23))) (fun _ => L^E)
    (fun _ _ => (Real.exp_pos _).le)
    (Eventually.of_forall (fun _ _ => (Real.rpow_pos_of_pos hL0 _).le))
    (Eventually.of_forall (fun _ => (Real.rpow_pos_of_pos hL0 _).le))
    ?_ (fun _ _ => hblock S hS ell probes r t k hk) hmoment ?_
    (harmonic_log_fourier_integrable.norm.mul_const _).integrableOn
    (harmonic_log_fourier_integrable.norm.mul_const _).integrableOn) hdecay
  · intro i hi n hn
    have he : 2*Real.log 2*((6 : ℝ)+1) = 14*Real.log 2 := by ring
    simpa only [he] using invariant_triple_endpoint_dyadic_sqrt_bound hL0 hlog2
      pool α β γ hα hβ hγ hαrough hβrough (physical_dyadic_index_upper hpos hi) hn
  · intro i hi
    apply Eventually.of_forall
    intro v
    exact hop S hS probes r t hrt Q h ξ hQ hξ pool hpool
      α β γ α' β' γ' hα hβ hγ hα' hβ' hγ' positions i (2*R*D)
      (hradius S hS ell probes r t U W hUlo hUhi hWlo hWhi k hk j hj i hi)
      (physical_dyadic_index_upper hpos hi) (-(a+a')) (-a) a' Z v k

end Bounty


-- Source module: CentralHarmonicMoment

/- The exact central moment hypothesis for the original signed harmonic residual. -/

open Finset MeasureTheory
open scoped Classical
namespace Bounty

def physicalCentralHarmonicMoment
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ) (probes : G → Finset (Fin J))
    (r t : Finset G) (hrt : Disjoint r t) (Q : ℕ) (h ξ a a' Z : ℝ) (k : ℤ)
    (L η F : ℝ) : Prop :=
  let R := Nat.ceil (L^(13/25 : ℝ))
  let D := max 1 (physicalOperatorStepBound P J ell
    (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
    (repeatedBigPrimePatternCut probes r t) (fun _ => k))
  let positions := physicalSignedHarmonicPositions (ell := ell) P probes r t Z k
  ∀ i ∈ positions.image (fun n => n.natAbs.log2), ∀ᵐ v : ℝ, ‖v‖ ≤ L^η →
    (physicalRootMoment V
      (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
      (repeatedBigPrimePatternCut probes r t) (1/2)
      (fun e _ => if e % 2 = 0 then -(-(a+a')-2*Real.pi*v) else -(a+a')-2*Real.pi*v)
      (fun e _ => if e % 2 = 0 then -k else k)
      (fun e i x y aux => if e % 2 = 0 then
        (starRingEnd ℂ) (physicalRootPrimeKernel P V probes r t hrt Q h ξ i y x aux)
        else physicalRootPrimeKernel P V probes r t hrt Q h ξ i x y aux)
      (physicalDyadicStarts i) (2*R-1) D).re ≤ (L^(-(F+23)))^(2*R)

end Bounty


-- Source module: PhysicalRawHarmonicIsolation

/- The raw harmonic main is recovered from the signed physical residual,
the signed replacement error, and the nonempty comparison mains. -/

open Finset
open scoped Classical
namespace Bounty

section
variable {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ) (probes : G → Finset (Fin J))
    (r t : Finset G) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (a b Z : ℝ) (k : ℤ) (pool : Finset ℕ) (α β γ α' β' γ' : ℕ → ℂ)

theorem physical_raw_harmonic_isolation :
    (∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut (ell := ell) probes r t (.inl ())),
        (physicalAuxMass V (repeatedBigPrimePatternCut (ell := ell) probes r t (.inl ())) aux : ℂ) *
          physicalFreePositiveHarmonicMain P V probes r t hrt Q h ξ (.inl ()) aux a b Z k pool α β γ α' β' γ') =
      physicalSignedPositiveHarmonicResidual (ell := ell) P V probes r t hrt Q h ξ a b Z k pool α β γ α' β' γ' -
      (∑ i : RepeatedBigPrimePatternIndex (ell := ell) probes r t,
      ∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut (ell := ell) probes r t i),
        (physicalAuxMass V (repeatedBigPrimePatternCut (ell := ell) probes r t i) aux : ℂ) *
          physicalPositiveHarmonicDifference P V probes r t hrt Q h ξ i aux a b Z k pool α β γ α' β' γ') -
      (∑ ab : RepeatedBigPrimePatternPair (ell := ell) probes r t,
      ∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut (ell := ell) probes r t (.inr ab)),
        (physicalAuxMass V (repeatedBigPrimePatternCut (ell := ell) probes r t (.inr ab)) aux : ℂ) *
          physicalFreePositiveHarmonicMain P V probes r t hrt Q h ξ (.inr ab) aux a b Z k pool α β γ α' β' γ') := by
  rw [physical_harmonic_residual_decomposition]
  ring

theorem physical_raw_harmonic_bound
    (Rbound Ebound : ℝ)
    (B : RepeatedBigPrimePatternPair (ell := ell) probes r t → ℝ)
    (hR : ‖physicalSignedPositiveHarmonicResidual (ell := ell) P V probes r t hrt Q h ξ a b Z k pool α β γ α' β' γ'‖ ≤ Rbound)
    (hE : ‖∑ i : RepeatedBigPrimePatternIndex (ell := ell) probes r t,
      ∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut (ell := ell) probes r t i),
        (physicalAuxMass V (repeatedBigPrimePatternCut (ell := ell) probes r t i) aux : ℂ) *
          physicalPositiveHarmonicDifference P V probes r t hrt Q h ξ i aux a b Z k pool α β γ α' β' γ'‖ ≤ Ebound)
    (hB : ∀ ab : RepeatedBigPrimePatternPair (ell := ell) probes r t,
      ‖∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t (.inr ab)),
        (physicalAuxMass V (repeatedBigPrimePatternCut probes r t (.inr ab)) aux : ℂ) *
          physicalFreePositiveHarmonicMain P V probes r t hrt Q h ξ (.inr ab) aux a b Z k pool α β γ α' β' γ'‖ ≤ B ab) :
    ‖∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut (ell := ell) probes r t (.inl ())),
        (physicalAuxMass V (repeatedBigPrimePatternCut (ell := ell) probes r t (.inl ())) aux : ℂ) *
          physicalFreePositiveHarmonicMain P V probes r t hrt Q h ξ (.inl ()) aux a b Z k pool α β γ α' β' γ'‖ ≤ Rbound + Ebound + ∑ ab, B ab := by
  have hC : ‖∑ ab : RepeatedBigPrimePatternPair (ell := ell) probes r t,
      ∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut (ell := ell) probes r t (.inr ab)),
        (physicalAuxMass V (repeatedBigPrimePatternCut (ell := ell) probes r t (.inr ab)) aux : ℂ) *
          physicalFreePositiveHarmonicMain P V probes r t hrt Q h ξ (.inr ab) aux a b Z k pool α β γ α' β' γ'‖ ≤ ∑ ab, B ab :=
    (norm_sum_le _ _).trans (sum_le_sum (fun ab _ => hB ab))
  rw [physical_raw_harmonic_isolation]
  exact (norm_sub_le _ _).trans
    (add_le_add ((norm_sub_le _ _).trans (add_le_add hR hE)) hC)

theorem physical_raw_harmonic_bound_of_pointwise
    (hV : ∀ g, 0 < V g) (hMass : ∀ g, ∑ p ∈ P g, 1/(p : ℝ) = V g)
    (Rbound Ebound : ℝ)
    (B : RepeatedBigPrimePatternPair (ell := ell) probes r t → ℝ)
    (hR : ‖physicalSignedPositiveHarmonicResidual (ell := ell) P V probes r t hrt Q h ξ a b Z k pool α β γ α' β' γ'‖ ≤ Rbound)
    (hE : ‖∑ i : RepeatedBigPrimePatternIndex (ell := ell) probes r t,
      ∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut (ell := ell) probes r t i),
        (physicalAuxMass V (repeatedBigPrimePatternCut (ell := ell) probes r t i) aux : ℂ) *
          physicalPositiveHarmonicDifference P V probes r t hrt Q h ξ i aux a b Z k pool α β γ α' β' γ'‖ ≤ Ebound)
    (hB : ∀ (ab : RepeatedBigPrimePatternPair (ell := ell) probes r t)
      (aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t (.inr ab))),
      ‖physicalFreePositiveHarmonicMain P V probes r t hrt Q h ξ (.inr ab) aux a b Z k pool α β γ α' β' γ'‖ ≤ B ab) :
    ‖∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut (ell := ell) probes r t (.inl ())),
        (physicalAuxMass V (repeatedBigPrimePatternCut (ell := ell) probes r t (.inl ())) aux : ℂ) *
          physicalFreePositiveHarmonicMain P V probes r t hrt Q h ξ (.inl ()) aux a b Z k pool α β γ α' β' γ'‖ ≤ Rbound + Ebound + ∑ ab, B ab := by
  apply physical_raw_harmonic_bound P V probes r t hrt Q h ξ a b Z k pool α β γ α' β' γ' Rbound Ebound B hR hE
  intro ab
  exact physical_auxiliary_error_average V _ hV hMass _ (hB ab)

end

theorem physical_raw_auxiliary_average
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ) (probes : G → Finset (Fin J)) (r t : Finset G)
    (F : PhysicalAuxLabels P (repeatedBigPrimePatternCut (ell := ell) probes r t (.inl ())) → ℂ)
    (aux0 : PhysicalAuxLabels P (repeatedBigPrimePatternCut (ell := ell) probes r t (.inl ()))) :
    (∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut (ell := ell) probes r t (.inl ())),
      (physicalAuxMass V (repeatedBigPrimePatternCut (ell := ell) probes r t (.inl ())) aux : ℂ) * F aux) =
      F aux0 := by
  have : Subsingleton (PhysicalAuxLabels P
      (repeatedBigPrimePatternCut (ell := ell) probes r t (.inl ()))) := by
    change Subsingleton (PhysicalAuxLabels P (fun _ => (∅ : Finset (Fin J))))
    infer_instance
  let : Unique (PhysicalAuxLabels P
      (repeatedBigPrimePatternCut (ell := ell) probes r t (.inl ()))) :=
    ⟨⟨aux0⟩, fun _ => Subsingleton.elim _ _⟩
  rw [Fintype.sum_unique]
  change (physicalAuxMass V (repeatedBigPrimePatternCut (ell := ell) probes r t (.inl ())) aux0 : ℂ) * F aux0 = F aux0
  have hm : physicalAuxMass V (repeatedBigPrimePatternCut (ell := ell) probes r t (.inl ())) aux0 = 1 := by
    exact physical_aux_mass_empty V aux0
  simp only [hm, Complex.ofReal_one, one_mul]

end Bounty


-- Source module: PhysicalRawOriginalCorrelation

/- Exact raw harmonic recovery of the original candidate correlation. -/

/- Marked weights retain constant averages even when a marked-list fiber is empty. -/

open Finset
open scoped Classical
namespace Bounty

theorem weighted_group_marked_average_const {G : Type*} [Fintype G]
    (P : G → Finset ℕ) (q : ℝ) (V : G → ℝ) (t : G → ℕ) (n : ℤ) (c : ℂ) :
    (markedDivisorWeight univ P q V t n : ℂ) *
      groupMarkedAverage P t n (fun _ => c) =
        (markedDivisorWeight univ P q V t n : ℂ) * c := by
  rw [← weighted_group_marked_sum_eq_average]
  simp only [weightedGroupMarkedSum, sum_const, card_univ, nsmul_eq_mul,
    marked_divisor_weight_eq_fiber_mass, Nat.card_eq_fintype_card]
  push_cast
  ring

theorem weighted_group_marked_pair_average_const {G : Type*} [Fintype G]
    (P : G → Finset ℕ) (q : ℝ) (V : G → ℝ) (t : G → ℕ) (n m : ℤ) (c : ℂ) :
    (markedDivisorWeight univ P q V t n : ℂ) *
      (markedDivisorWeight univ P q V t m : ℂ) *
      groupMarkedAverage P t n (fun _ => groupMarkedAverage P t m (fun _ => c)) =
        (markedDivisorWeight univ P q V t n : ℂ) *
          (markedDivisorWeight univ P q V t m : ℂ) * c := by
  calc
    _ = (markedDivisorWeight univ P q V t m : ℂ) *
        ((markedDivisorWeight univ P q V t n : ℂ) *
          groupMarkedAverage P t n (fun _ => groupMarkedAverage P t m (fun _ => c))) := by ring
    _ = (markedDivisorWeight univ P q V t m : ℂ) *
        ((markedDivisorWeight univ P q V t n : ℂ) * groupMarkedAverage P t m (fun _ => c)) := by
      rw [weighted_group_marked_average_const]
    _ = (markedDivisorWeight univ P q V t n : ℂ) *
        ((markedDivisorWeight univ P q V t m : ℂ) * groupMarkedAverage P t m (fun _ => c)) := by ring
    _ = _ := by rw [weighted_group_marked_average_const]; ring

end Bounty

/- The empty-cut main is the literal marked harmonic correlation with no residual kernel. -/

open Finset
open scoped Classical
namespace Bounty

theorem physical_free_prime_pair_coefficient_raw
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ) (probes : G → Finset (Fin J))
    (r t : Finset G) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut (ell := ell) probes r t (.inl ())))
    (a b : ℝ) (w z : ℕ) (u v : GroupMarkedLists P (fun _ => ell)) :
    physicalFreePrimePairCoefficient P V probes r t hrt Q h ξ (.inl ()) aux a b w z u v =
      physicalPhase a w * physicalPhase b z := by
  have hd : physicalFreeFactor (repeatedBigPrimePatternCut (ell := ell) probes r t (.inl ())) aux = 1 :=
    physical_free_factor_empty aux
  change 1 * 1 * physicalPhase a w * physicalPhase b z *
    physicalPhase (-(a+b))
      (physicalFreeFactor (repeatedBigPrimePatternCut (ell := ell) probes r t (.inl ())) aux) = _
  rw [hd]
  have he : physicalPhase (-(a+b)) 1 = 1 := by simp [physicalPhase]
  rw [he]
  ring

theorem physical_raw_group_marked_average
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ) (probes : G → Finset (Fin J))
    (r t : Finset G) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut (ell := ell) probes r t (.inl ())))
    (a b : ℝ) (w z : ℕ) :
    groupMarkedAverage P (fun _ => ell) (w : ℤ) (fun u =>
      groupMarkedAverage P (fun _ => ell) (z : ℤ)
        (physicalFreePrimePairCoefficient P V probes r t hrt Q h ξ (.inl ()) aux a b w z u)) =
    groupMarkedAverage P (fun _ => ell) (w : ℤ) (fun _ =>
      groupMarkedAverage P (fun _ => ell) (z : ℤ)
        (fun _ => physicalPhase a w * physicalPhase b z)) := by
  apply congrArg (groupMarkedAverage P (fun _ => ell) (w : ℤ))
  funext u
  apply congrArg (groupMarkedAverage P (fun _ => ell) (z : ℤ))
  funext v
  exact physical_free_prime_pair_coefficient_raw P V probes r t hrt Q h ξ aux a b w z u v

theorem physical_raw_harmonic_main_eq_marked_sum
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ) (probes : G → Finset (Fin J))
    (r t : Finset G) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut (ell := ell) probes r t (.inl ())))
    (a b Z : ℝ) (k : ℤ) (pool : Finset ℕ) (α β γ α' β' γ' : ℕ → ℂ) :
    physicalFreePositiveHarmonicMain P V probes r t hrt Q h ξ (.inl ()) aux
      a b Z k pool α β γ α' β' γ' =
      ∑ n ∈ harmonicPositiveSupport Z k 1,
        ((typeIIHarmonicDyadic ((n : ℝ)/Z) : ℂ)/(n : ℂ)) *
          star (invariantTripleEndpoint pool α β γ n.natAbs) *
          invariantTripleEndpoint pool α' β' γ' (n+k).natAbs *
          ((markedDivisorWeight univ P (1/2) V (fun _ => ell) (n.natAbs : ℤ) *
            markedDivisorWeight univ P (1/2) V (fun _ => ell) ((n+k).natAbs : ℤ) : ℝ) : ℂ) *
          (physicalPhase a n.natAbs * physicalPhase b (n+k).natAbs) := by
  have hd : physicalFreeFactor (repeatedBigPrimePatternCut (ell := ell) probes r t (.inl ())) aux = 1 :=
    physical_free_factor_empty aux
  unfold physicalFreePositiveHarmonicMain
  dsimp only
  rw [hd]
  simp only [repeatedBigPrimePatternCut, card_empty, Nat.add_zero,
    Nat.cast_one, mul_one]
  apply sum_congr rfl
  intro n _hn
  rw [physical_raw_group_marked_average P V probes r t hrt Q h ξ aux a b n.natAbs (n+k).natAbs]
  simp only [Complex.ofReal_mul]
  simpa only [mul_assoc] using congrArg
    (fun z => (((typeIIHarmonicDyadic ((n : ℝ)/Z) : ℂ)/(n : ℂ)) *
      star (invariantTripleEndpoint pool α β γ n.natAbs) *
      invariantTripleEndpoint pool α' β' γ' (n+k).natAbs) * z)
    (weighted_group_marked_pair_average_const P (1/2) V (fun _ => ell)
      (n.natAbs : ℤ) ((n+k).natAbs : ℤ) (physicalPhase a n.natAbs * physicalPhase b (n+k).natAbs))

end Bounty

/- Exact reindexing of the positive integer harmonic window onto its finite natural support. -/

open Finset
namespace Bounty

theorem positive_harmonic_cast_summand (Z : ℝ) (F : ℕ → ℂ)
    {n : ℤ} (hn : 0 ≤ n) :
    ((typeIIHarmonicDyadic ((n : ℝ)/Z) : ℂ)/(n : ℂ)) * F n.natAbs =
      ((typeIIHarmonicDyadic ((n.natAbs : ℝ)/Z) : ℂ)/(n.natAbs : ℂ)) * F n.natAbs := by
  have he : (n.natAbs : ℤ) = n := by
    simpa only [abs_of_nonneg hn] using Int.natCast_natAbs n
  have hr := congrArg (fun z : ℤ => (z : ℝ)) he
  have hc := congrArg (fun z : ℤ => (z : ℂ)) he
  simp only [Int.cast_natCast] at hr hc
  rw [hr, hc]

theorem positive_harmonic_sum_eq_active {Z : ℝ} (hZ : 0 < Z) (k : ℤ)
    (B : ℕ) (F : ℕ → ℂ)
    (hbound : ∀ n ∈ harmonicPositiveSupport Z k 1, F n.natAbs ≠ 0 → n.natAbs ≤ B) :
    (∑ n ∈ harmonicPositiveSupport Z k 1,
      ((typeIIHarmonicDyadic ((n : ℝ)/Z) : ℂ)/(n : ℂ)) * F n.natAbs) =
      ∑ z ∈ typeIIActiveCrossZ Z k (Icc 0 B),
        ((typeIIHarmonicDyadic ((z : ℝ)/Z) : ℂ)/(z : ℂ)) * F z := by
  classical
  apply sum_bij_ne_zero (fun n _ _ => n.natAbs)
  · intro n hn hne
    have hs := mem_harmonic_positive_support hn
    have he : (n.natAbs : ℤ) = n := by
      simpa only [abs_of_nonneg hs.1.le] using Int.natCast_natAbs n
    have hr := congrArg (fun z : ℤ => (z : ℝ)) he
    simp only [Int.cast_natCast] at hr
    have hF : F n.natAbs ≠ 0 := by
      intro hz
      exact hne (by rw [hz, mul_zero])
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨Nat.zero_le _, hbound n hn hF⟩, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · have hp : (0 : ℤ) < (n.natAbs : ℤ) := by simpa only [he] using hs.1
      exact_mod_cast hp
    · simpa only [he, Nat.cast_one, mul_one] using hs.2.2.2
    · simpa only [hr, Nat.cast_one, mul_one] using hs.2.2.1
  · intro n hn _ m hm _ he
    have hn0 := (mem_harmonic_positive_support hn).1.le
    have hm0 := (mem_harmonic_positive_support hm).1.le
    have hcast := congrArg (fun z : ℕ => (z : ℤ)) he
    simpa only [Int.natCast_natAbs, abs_of_nonneg hn0, abs_of_nonneg hm0] using hcast
  · intro z hz hne
    obtain ⟨hzB, hzpos, hwpos, hzupper⟩ := mem_filter.mp hz
    have hpsi : typeIIHarmonicDyadic ((z : ℝ)/Z) ≠ 0 := by
      intro hzero
      exact hne (by simp only [hzero, Complex.ofReal_zero, zero_div, zero_mul])
    have hs := typeII_harmonic_dyadic_support hpsi
    have hlo : Z/2 < (z : ℝ) := by
      have hh := (lt_div_iff₀ hZ).mp hs.1
      linarith
    have hzH : (z : ℤ) ∈ harmonicPositiveSupport Z k 1 := by
      apply mem_filter.mpr
      refine ⟨mem_Icc.mpr ⟨by omega, ?_⟩, ?_, ?_⟩
      · apply Int.le_floor.mpr
        simpa only [Int.cast_natCast, Nat.cast_one, mul_one] using hzupper
      · simpa only [Int.cast_natCast, Nat.cast_one, mul_one] using hlo
      · simpa only [Nat.cast_one, mul_one] using hwpos
    refine ⟨(z : ℤ), hzH, ?_, by simp⟩
    simpa only [Int.cast_natCast, Int.natAbs_natCast] using hne
  · intro n hn _
    exact positive_harmonic_cast_summand Z F (mem_harmonic_positive_support hn).1.le

end Bounty

/- Nonzero finite cross-pair coefficients retain both original product supports. -/

open Finset
namespace Bounty

theorem finite_cross_pair_nonzero_bounds
    (M H : Finset ℕ) (A : ℕ → ℂ) (W : ℕ → ℝ) (B : ℕ → ℂ)
    (ρ ξ₁ ξ₂ ξ₃ : ℝ) (z w : ℕ)
    (hne : typeIICrossPairCoefficient M H A W B ρ ξ₁ ξ₂ ξ₃ z w ≠ 0) :
    z ≤ M.sup id * H.sup id ∧ w ≤ M.sup id * H.sup id := by
  classical
  unfold typeIICrossPairCoefficient at hne
  obtain ⟨m, hm, hne⟩ := exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨h', hh', hne⟩ := exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨m', hm', hne⟩ := exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨h, hh, hne⟩ := exists_ne_zero_of_sum_ne_zero hne
  have he : m'*h=z ∧ m*h'=w := by
    by_contra hz
    exact hne (if_neg hz)
  constructor
  · rw [← he.1]
    exact Nat.mul_le_mul (le_sup (f := id) hm') (le_sup (f := id) hh)
  · rw [← he.2]
    exact Nat.mul_le_mul (le_sup (f := id) hm) (le_sup (f := id) hh')

end Bounty

/- The raw physical main written on the original finite natural harmonic window. -/

open Finset
open scoped Classical
namespace Bounty

theorem physical_phase_eq_typeIIPhase (a : ℝ) (n : ℕ) :
    physicalPhase a n = typeIIPhase a n := by
  unfold physicalPhase typeIIPhase
  congr 1
  ring

noncomputable def physicalRawNaturalCoefficient
    {G : Type*} [Fintype G] (P : G → Finset ℕ) (V : G → ℝ) (ell : ℕ)
    (a b : ℝ) (k : ℤ) (pool : Finset ℕ) (α β γ α' β' γ' : ℕ → ℂ) (z : ℕ) : ℂ :=
  typeIIPhase a z * typeIIPhase b ((z : ℤ)+k).toNat *
    star (invariantTripleEndpoint pool α β γ z) *
    invariantTripleEndpoint pool α' β' γ' ((z : ℤ)+k).toNat *
    (markedDivisorWeight univ P (1/2) V (fun _ => ell) (z : ℤ) : ℂ) *
    (markedDivisorWeight univ P (1/2) V (fun _ => ell) (((z : ℤ)+k).toNat : ℤ) : ℂ)

theorem physical_raw_harmonic_main_eq_natural_sum
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ) (probes : G → Finset (Fin J))
    (r t : Finset G) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut (ell := ell) probes r t (.inl ())))
    (a b Z : ℝ) (k : ℤ) (pool : Finset ℕ) (α β γ α' β' γ' : ℕ → ℂ)
    (hZ : 0 < Z) (B : ℕ)
    (hbound : ∀ n ∈ harmonicPositiveSupport Z k 1,
      physicalRawNaturalCoefficient P V ell a b k pool α β γ α' β' γ' n.natAbs ≠ 0 → n.natAbs ≤ B) :
    physicalFreePositiveHarmonicMain P V probes r t hrt Q h ξ (.inl ()) aux
      a b Z k pool α β γ α' β' γ' =
      ∑ z ∈ typeIIActiveCrossZ Z k (Icc 0 B),
        ((typeIIHarmonicDyadic ((z : ℝ)/Z) : ℂ)/(z : ℂ)) *
          physicalRawNaturalCoefficient P V ell a b k pool α β γ α' β' γ' z := by
  rw [physical_raw_harmonic_main_eq_marked_sum]
  trans ∑ n ∈ harmonicPositiveSupport Z k 1,
    ((typeIIHarmonicDyadic ((n : ℝ)/Z) : ℂ)/(n : ℂ)) *
      physicalRawNaturalCoefficient P V ell a b k pool α β γ α' β' γ' n.natAbs
  · apply sum_congr rfl
    intro n hn
    have hs := mem_harmonic_positive_support hn
    have hncast : (n.natAbs : ℤ) = n := by
      simpa only [abs_of_nonneg hs.1.le] using Int.natCast_natAbs n
    have htpos : 0 ≤ n+k := by simpa only [Nat.cast_one, mul_one] using hs.2.2.2.le
    have htnat : ((n.natAbs : ℤ)+k).toNat = (n+k).natAbs := by
      rw [hncast]
      have he : (((n+k).toNat : ℕ) : ℤ) = ((n+k).natAbs : ℤ) := by
        rw [Int.toNat_of_nonneg htpos, Int.natCast_natAbs, abs_of_nonneg htpos]
      exact_mod_cast he
    simp only [physicalRawNaturalCoefficient, htnat, physical_phase_eq_typeIIPhase,
      Complex.ofReal_mul]
    ring
  · exact positive_harmonic_sum_eq_active hZ k B _ hbound

end Bounty

/- The literal empty-cut, one-mark main equals the original saturated candidate harmonic test. -/

open Finset Filter
open scoped Classical ComplexConjugate
namespace Bounty

theorem eventually_candidate_raw_harmonic_eq_b0 {c : ℝ} (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (r jStar : ℕ) (hr : 0 < r)
      (hj : jStar ∈ candidateQIndices c L) (X : ℝ)
      (take : Fin ((candidateQIndices c L).card*r) → Bool)
      (hkeep : take ((candidateAllocationOrder c L r).symm
        (candidateRoughSlot c L r jStar hr hj)) = false)
      (twist : (candidateQIndices c L) × Fin r → ℕ → ℂ) (σ : ℝ),
    (∀ p ∈ candidateRoughBand c L jStar,
      twist (candidateRoughSlot c L r jStar hr hj) p = typeIIPhase σ p) →
    ∀ (Z : ℝ) (k : ℤ) (M : Finset ℕ) (α : ℕ → ℂ) (ν : ℝ)
      (χ : DirichletCharacter ℂ (2*k.natAbs)) (ζ : EuclideanSpace ℝ (Fin 3)),
    0 < Z → |(k : ℝ)| ≤ Z → 3*Z < X →
    (∀ m ∈ M, 0 < m) → (∀ m, m ∉ M → α m = 0) →
    (∀ m ∈ M, α m ≠ 0 → Disjoint m.primeFactors
      ((candidatePIndices c L).biUnion (candidatePBand (c*L)))) →
    let P := fun g : candidatePIndices c L => candidatePBand (c*L) g.val
    let V := fun g : candidatePIndices c L => ∑ p ∈ P g, 1/(p : ℝ)
    let pool := (candidatePIndices c L).biUnion (candidatePBand (c*L))
    let cr := candidateResidualPrimeCoefficient c L r jStar hr hj take hkeep twist
    let α₀ := fun m => α m * χ (m : ZMod (2*k.natAbs)) *
      typeIIPhase ((2*Real.pi*ν)-2*Real.pi*ζ 1) m
    let β₀ := fun p => if p ∈ candidateRoughBand c L jStar then typeIIPhase (-σ) p else 0
    let γ₀ := fun s => conj (cr s)
    let α₁ := fun m => α m * χ (m : ZMod (2*k.natAbs)) *
      typeIIPhase (2*Real.pi*ζ 0+(2*Real.pi*ν)) m
    ∀ (J : ℕ) (probes : candidatePIndices c L → Finset (Fin J))
      (rP tP : Finset (candidatePIndices c L)) (hrt : Disjoint rP tP)
      (Q : ℕ) (h ξ : ℝ)
      (aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut (ell := 1) probes rP tP (.inl ()))),
    physicalFreePositiveHarmonicMain P V probes rP tP hrt Q h ξ (.inl ()) aux
      ((2*Real.pi*ν)+2*Real.pi*ζ 2) (-(2*Real.pi*ν)) Z k pool α₀ β₀ γ₀ α₁ β₀ γ₀ =
      candidateB0HarmonicCorrelation c L (1/2) r jStar (candidateSmallPSet c L X)
        take twist ν Z k M α χ ζ := by
  filter_upwards [eventually_candidate_harmonic_eq_saturated_endpoints hc,
    eventually_candidate_cross_pair_eq_saturated_endpoints hc] with L hsum hpoint
  intro r jStar hr hj X take hkeep twist σ hphase Z k M α ν χ ζ hZ hk hX hM hα hfree
    P V pool cr α₀ β₀ γ₀ α₁ J probes rP tP hrt Q h ξ aux
  let M₀ := M.filter (fun m => α m ≠ 0)
  let H := candidateRetainedAllocationSupport c L r jStar (candidateSmallPSet c L X) take
  have hM₀ : ∀ m ∈ M₀, 0 < m := fun m hm => hM m (mem_filter.mp hm).1
  have hfree₀ : ∀ m ∈ M₀, Disjoint m.primeFactors pool :=
    fun m hm => hfree m (mem_filter.mp hm).1 (mem_filter.mp hm).2
  have hα₀ : ∀ m, m ∉ M₀ → α m = 0 := by
    intro m hm
    by_cases hmM : m ∈ M
    · by_contra hn
      exact hm (mem_filter.mpr ⟨hmM, hn⟩)
    · exact hα m hmM
  have hW (n : ℤ) := marked_divisor_weight_subtype (candidatePIndices c L)
    (candidatePBand (c*L)) (1/2) (fun j => ∑ p ∈ candidatePBand (c*L) j, 1/(p : ℝ))
    (fun _ => 1) n
  have hbound : ∀ n ∈ harmonicPositiveSupport Z k 1,
      physicalRawNaturalCoefficient P V 1 ((2*Real.pi*ν)+2*Real.pi*ζ 2)
        (-(2*Real.pi*ν)) k pool α₀ β₀ γ₀ α₁ β₀ γ₀ n.natAbs ≠ 0 →
      n.natAbs ≤ M₀.sup id * H.sup id := by
    intro n hn hne
    have hs := mem_harmonic_positive_support hn
    have hncast : (n.natAbs : ℤ) = n := by
      simpa only [abs_of_nonneg hs.1.le] using Int.natCast_natAbs n
    have hnr := congrArg (fun z : ℤ => (z : ℝ)) hncast
    simp only [Int.cast_natCast] at hnr
    have hnp : 0 < n.natAbs := by
      have hh : (0 : ℤ) < (n.natAbs : ℤ) := by simpa only [hncast] using hs.1
      exact_mod_cast hh
    have hwp : 0 < (n.natAbs : ℤ)+k := by
      simpa only [hncast, Nat.cast_one, mul_one] using hs.2.2.2
    have hwt : (((n.natAbs : ℤ)+k).toNat : ℤ) = n+k := by
      rw [Int.toNat_of_nonneg hwp.le, hncast]
    have hwr := congrArg (fun z : ℤ => (z : ℝ)) hwt
    simp only [Int.cast_natCast, Int.cast_add] at hwr
    have hnupper : (n.natAbs : ℝ) ≤ 2*Z := by
      simpa only [hnr, Nat.cast_one, mul_one] using hs.2.2.1
    have hwupper : (((n.natAbs : ℤ)+k).toNat : ℝ) ≤ 3*Z := by
      rw [hwr]
      have hkupper := (le_abs_self (k : ℝ)).trans hk
      linarith
    have he := hpoint (1/2) r jStar hr hj X take hkeep twist σ hphase M₀ α
      (2*k.natAbs) χ (2*Real.pi*ν) (2*Real.pi*ζ 0) (2*Real.pi*ζ 1) (2*Real.pi*ζ 2)
      n.natAbs ((n.natAbs : ℤ)+k).toNat hnp (Int.pos_iff_toNat_pos.mp hwp)
      (by linarith) (hwupper.trans_lt hX) hM₀ hfree₀ hα₀
    have hcp : typeIICrossPairCoefficient M₀ H (fun m => α m * χ (m : ZMod (2*k.natAbs)))
        (fun n => markedDivisorWeight (candidatePIndices c L) (candidatePBand (c*L)) (1/2)
          (fun j => ∑ p ∈ candidatePBand (c*L) j, 1/(p : ℝ)) (fun _ => 1) (n : ℤ))
        (fun s => candidateRemainingComplexCoefficient c L r jStar take twist (primePoolFreePart pool s))
        (2*Real.pi*ν) (2*Real.pi*ζ 0) (2*Real.pi*ζ 1) (2*Real.pi*ζ 2)
        n.natAbs ((n.natAbs : ℤ)+k).toNat ≠ 0 := by
      intro hz
      apply hne
      have he' := he.symm.trans hz
      simpa only [physicalRawNaturalCoefficient, P, V, pool, cr, α₀, β₀, γ₀, α₁,
        hW, starRingEnd_apply] using he'
    exact (finite_cross_pair_nonzero_bounds M₀ H _ _ _ _ _ _ _ _ _ hcp).1
  rw [physical_raw_harmonic_main_eq_natural_sum P V probes rP tP hrt Q h ξ aux
    _ _ Z k pool α₀ β₀ γ₀ α₁ β₀ γ₀ hZ (M₀.sup id * H.sup id) hbound]
  symm
  simpa only [physicalRawNaturalCoefficient, P, V, pool, cr, α₀, β₀, γ₀, α₁, M₀, H,
    hW, starRingEnd_apply, Complex.ofReal_div, Complex.ofReal_natCast] using
    hsum (1/2) r jStar hr hj X take hkeep twist σ hphase Z k M α ν χ ζ hk hX hM hα hfree

end Bounty

/- The complete raw auxiliary average equals the original saturated candidate harmonic test. -/

open Finset Filter
open scoped Classical ComplexConjugate
namespace Bounty

theorem eventually_candidate_raw_average_eq_b0 {c : ℝ} (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (r jStar : ℕ) (hr : 0 < r)
      (hj : jStar ∈ candidateQIndices c L) (X : ℝ)
      (take : Fin ((candidateQIndices c L).card*r) → Bool)
      (hkeep : take ((candidateAllocationOrder c L r).symm
        (candidateRoughSlot c L r jStar hr hj)) = false)
      (twist : (candidateQIndices c L) × Fin r → ℕ → ℂ) (σ : ℝ),
    (∀ p ∈ candidateRoughBand c L jStar,
      twist (candidateRoughSlot c L r jStar hr hj) p = typeIIPhase σ p) →
    ∀ (Z : ℝ) (k : ℤ) (M : Finset ℕ) (α : ℕ → ℂ) (ν : ℝ)
      (χ : DirichletCharacter ℂ (2*k.natAbs)) (ζ : EuclideanSpace ℝ (Fin 3)),
    0 < Z → |(k : ℝ)| ≤ Z → 3*Z < X →
    (∀ m ∈ M, 0 < m) → (∀ m, m ∉ M → α m = 0) →
    (∀ m ∈ M, α m ≠ 0 → Disjoint m.primeFactors
      ((candidatePIndices c L).biUnion (candidatePBand (c*L)))) →
    let P := fun g : candidatePIndices c L => candidatePBand (c*L) g.val
    let V := fun g : candidatePIndices c L => ∑ p ∈ P g, 1/(p : ℝ)
    let pool := (candidatePIndices c L).biUnion (candidatePBand (c*L))
    let cr := candidateResidualPrimeCoefficient c L r jStar hr hj take hkeep twist
    let α₀ := fun m => α m * χ (m : ZMod (2*k.natAbs)) *
      typeIIPhase ((2*Real.pi*ν)-2*Real.pi*ζ 1) m
    let β₀ := fun p => if p ∈ candidateRoughBand c L jStar then typeIIPhase (-σ) p else 0
    let γ₀ := fun s => conj (cr s)
    let α₁ := fun m => α m * χ (m : ZMod (2*k.natAbs)) *
      typeIIPhase (2*Real.pi*ζ 0+(2*Real.pi*ν)) m
    ∀ (J : ℕ) (probes : candidatePIndices c L → Finset (Fin J))
      (rP tP : Finset (candidatePIndices c L)) (hrt : Disjoint rP tP)
      (Q : ℕ) (h ξ : ℝ),
    (∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut (ell := 1) probes rP tP (.inl ())),
      (physicalAuxMass V (repeatedBigPrimePatternCut (ell := 1) probes rP tP (.inl ())) aux : ℂ) *
        physicalFreePositiveHarmonicMain P V probes rP tP hrt Q h ξ (.inl ()) aux
          ((2*Real.pi*ν)+2*Real.pi*ζ 2) (-(2*Real.pi*ν)) Z k pool α₀ β₀ γ₀ α₁ β₀ γ₀) =
      candidateB0HarmonicCorrelation c L (1/2) r jStar (candidateSmallPSet c L X)
        take twist ν Z k M α χ ζ := by
  filter_upwards [eventually_candidate_raw_harmonic_eq_b0 hc] with L hL
  intro r jStar hr hj X take hkeep twist σ hphase Z k M α ν χ ζ hZ hk hX hM hα hfree
    P V pool cr α₀ β₀ γ₀ α₁ J probes rP tP hrt Q h ξ
  let aux0 : PhysicalAuxLabels P (repeatedBigPrimePatternCut (ell := 1) probes rP tP (.inl ())) :=
    fun _ j => False.elim (by simpa only [repeatedBigPrimePatternCut, notMem_empty] using j.property)
  rw [physical_raw_auxiliary_average P V probes rP tP _ aux0]
  exact hL r jStar hr hj X take hkeep twist σ hphase Z k M α ν χ ζ hZ hk hX hM hα hfree
    J probes rP tP hrt Q h ξ aux0

end Bounty

/- Recovering the raw main from the residual and the combined error/comparison term. -/

open Finset
open scoped Classical
namespace Bounty

theorem physical_raw_harmonic_two_term_bound
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ) (probes : G → Finset (Fin J))
    (r t : Finset G) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (a b Z : ℝ) (k : ℤ) (pool : Finset ℕ) (α β γ α' β' γ' : ℕ → ℂ)
    (Rbound ECbound : ℝ)
    (hR : ‖physicalSignedPositiveHarmonicResidual (ell := ell) P V probes r t hrt Q h ξ
      a b Z k pool α β γ α' β' γ'‖ ≤ Rbound)
    (hEC : ‖(∑ i : RepeatedBigPrimePatternIndex (ell := ell) probes r t,
        ∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut (ell := ell) probes r t i),
          (physicalAuxMass V (repeatedBigPrimePatternCut (ell := ell) probes r t i) aux : ℂ) *
            physicalPositiveHarmonicDifference P V probes r t hrt Q h ξ i aux
              a b Z k pool α β γ α' β' γ') +
      (∑ ab : RepeatedBigPrimePatternPair (ell := ell) probes r t,
        ∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut (ell := ell) probes r t (.inr ab)),
          (physicalAuxMass V (repeatedBigPrimePatternCut (ell := ell) probes r t (.inr ab)) aux : ℂ) *
            physicalFreePositiveHarmonicMain P V probes r t hrt Q h ξ (.inr ab) aux
              a b Z k pool α β γ α' β' γ')‖ ≤ ECbound) :
    ‖∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut (ell := ell) probes r t (.inl ())),
      (physicalAuxMass V (repeatedBigPrimePatternCut (ell := ell) probes r t (.inl ())) aux : ℂ) *
        physicalFreePositiveHarmonicMain P V probes r t hrt Q h ξ (.inl ()) aux
          a b Z k pool α β γ α' β' γ'‖ ≤ Rbound + ECbound := by
  rw [physical_raw_harmonic_isolation, sub_sub]
  exact (norm_sub_le _ _).trans (add_le_add hR hEC)

end Bounty


-- Source module: ActualPrimeB0Decay

/- The literal original B0 harmonic correlation follows from its selected central moment. -/

open Finset Filter MeasureTheory
open scoped Classical ComplexConjugate
namespace Bounty.WeakZeroFree

theorem exists_actual_prime_b0_decay_of_central_moment
    (hZeta : PrimitiveZeroFreeRightOf (23 / 24)) {c bWindow : ℝ}
    (hc : 0 < c) (hb : 0 < bWindow) :
    ∃ J₀ : ℕ, ∀ jStar : ℕ, J₀ < jStar →
      ∀ Kdet : ℝ, 0 ≤ Kdet → ∀ (D : ℝ) (J : ℕ) (B C R T F η : ℝ),
      0 ≤ B → 0 < η →
    ∃ S₀ : ℝ, 0 ≤ S₀ ∧ ∀ S : ℝ, S₀ ≤ S → ∀ᶠ L : ℝ in atTop,
      ∀ (rQ : ℕ) (hrQ : 0 < rQ) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*rQ) → Bool)
        (_hkeep : take ((candidateAllocationOrder c L rQ).symm
          (candidateRoughSlot c L rQ jStar hrQ hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L rQ jStar) → ℝ)
        (lo hi : ℕ) (κM : ℝ), 0 ≤ κM → κM ≤ 1/50 →
      ∀ (ν : ℝ) (ζ : EuclideanSpace ℝ (Fin 3)), ‖ν‖ ≤ L^T → ‖ζ‖ ≤ L^F →
      ∀ U V : ℝ, Real.exp (bWindow*L) ≤ U → U ≤ Real.exp L →
        Real.exp (bWindow*L) ≤ V → V ≤ Real.exp L →
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L Kdet : ℤ))
          (typeIIAdmissibleDeterminantBound L Kdet : ℤ), k ≠ 0 →
      ∀ (χ : DirichletCharacter ℂ (2*k.natAbs)) j, j ∈ range (typeIISmoothDyadicCount L) →
      let Z := typeIISmoothDyadicScale U V (U*L^(-Kdet)) j
      let P := fun g : candidatePIndices c L => candidatePBand (c*L) g.val
      let mass := fun g => ∑ p ∈ P g, 1/(p : ℝ)
      ∀ (probes : candidatePIndices c L → Finset (Fin J)) (r t : Finset (candidatePIndices c L))
        (hrt : Disjoint r t), (∀ g ∈ r ∪ t, g.val ∈ candidateBigPIndices c L) →
      ∀ Q : ℕ, (Q : ℝ) ≤ L^R →
      physicalCentralHarmonicMoment (ell := 1) P mass probes r t hrt Q (L^(-B)) (L^(-C))
        (2*Real.pi*ν+2*Real.pi*ζ 2) (-(2*Real.pi*ν)) Z k L η (D+1) →
      ‖candidateB0HarmonicCorrelation c L (1/2) rQ jStar
        (candidateSmallPSet c L (Real.exp (4*L))) take
        (candidateAllocationFourierTwist c L rQ jStar take ξ) ν Z k (Ioc lo hi)
        (fun m => (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) m : ℂ)) χ ζ‖ ≤ L^(-D) := by
  obtain ⟨J₀,hbase⟩ := exists_actual_prime_comparison_harmonic_decay_uniform_window hZeta hc hb
  refine ⟨J₀,?_⟩
  intro jStar hjStar Kdet hKdet D J B C R T F η hB hη
  obtain ⟨S₀,hS₀,hcmp⟩ := hbase jStar hjStar Kdet hKdet (D+1) J 1 B C R (Kdet+89)
    0 0 (Kdet+89) (max T F+1) (max T F+1) (by decide) hB (by linarith)
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [hcmp S hS,
    eventually_actual_residual_of_central_moment hc hb hKdet (le_max_right R 0) (le_max_right C 0)
      hη J 1 (D+1),
    eventually_candidate_raw_average_eq_b0 hc,
    eventually_actual_harmonic_scale_inputs hb hKdet,
    eventually_actual_prime_source_factor_properties hc S (hS₀.trans hS),
    eventually_actual_remaining_factor_properties hc,
    eventually_balanced_typeII_coefficient_properties S (hS₀.trans hS),
    eventually_ambient_prime_endpoint_group_free hc S (hS₀.trans hS),
    eventually_original_harmonic_modulus_bound hKdet,
    eventually_original_endpoint_phase_bounds T F,
    eventually_ge_atTop (2 : ℝ)]
    with L hcmp hres hraw hscale hfactor hremain hrough hfree hmod hphase hL
  intro rQ hrQ hj take hkeep ξ lo hi κM hκM hκmax ν ζ hν hζ U V hUlo hUhi hVlo hVhi
    k hk hk0 χ j hjd Z P mass probes r t hrt hbig Q hQ hmoment
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  let : NeZero (2*k.natAbs) := ⟨Nat.ne_of_gt (Nat.mul_pos (by decide) (Int.natAbs_pos.mpr hk0))⟩
  let pool := (candidatePIndices c L).biUnion (candidatePBand (c*L))
  let αM := fun m => (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) m : ℂ)
  let α₀ := fun m => αM m*χ (m : ZMod (2*k.natAbs))*typeIIPhase (2*Real.pi*ν-2*Real.pi*ζ 1) m
  let α₁ := fun m => αM m*χ (m : ZMod (2*k.natAbs))*typeIIPhase (2*Real.pi*ζ 0+2*Real.pi*ν) m
  let β := fun n => if n ∈ candidateRoughBand c L jStar then (1 : ℂ) else 0
  let γ := fun n => conj (candidateResidualPrimeCoefficient c L rQ jStar hrQ hj take hkeep
    (candidateAllocationFourierTwist c L rQ jStar take ξ) n)
  have hchar (n : ℕ) : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 := by
    rw [Subsingleton.elim (n : ZMod 1) 1, map_one]
  have hph := hphase ν ζ hν hζ
  have hkfull : (k.natAbs : ℝ) ≤ L^(Kdet+89) := by
    have hm := hmod k hk
    push_cast at hm
    nlinarith [Nat.cast_nonneg (α := ℝ) k.natAbs]
  have hEC := hcmp rQ hrQ hj take hkeep ξ lo hi κM
    (2*Real.pi*ν-2*Real.pi*ζ 1) (2*Real.pi*ζ 0+2*Real.pi*ν) (2*k.natAbs) χ
    hκM hκmax (hmod k hk) (hph.2 1).2 (by simpa only [add_comm] using (hph.2 0).1)
    0 1 1 (by simp) (by simp) probes r t hrt hbig Q hQ
    U V hUlo hUhi hVlo hVhi k hk hk0 hkfull j hjd
    (2*Real.pi*ν+2*Real.pi*ζ 2) (-(2*Real.pi*ν)) (hph.2 2).1
  simp only [typeIIPhase_zero,hchar,mul_one] at hEC
  have hα₀ := hfactor κM hκM hκmax (Ioc lo hi) (2*k.natAbs) χ (2*Real.pi*ν-2*Real.pi*ζ 1)
  have hα₁ := hfactor κM hκM hκmax (Ioc lo hi) (2*k.natAbs) χ (2*Real.pi*ζ 0+2*Real.pi*ν)
  have hβγ := hremain rQ jStar hrQ hj take hkeep ξ (fun _ => 1) (by intro n; simp)
  have hαrough : ∀ n, ¬ (∀ p : ℕ, p ∈ n.primeFactors → Real.exp (Real.sqrt L) ≤ (p : ℝ)) → α₀ n = 0 := by
    intro n hn
    have hz : ambientPrimeTypeIIAlpha κM L S n = 0 := by
      by_contra hne
      exact hn (fun p hp => (((hrough κM hκM hκmax n).2.2.2 hne).2 p hp).le)
    simp only [α₀,αM,typeIIRestrict,hz,ite_self,Complex.ofReal_zero,zero_mul]
  have hβrough : ∀ n, ¬ (∀ p : ℕ, p ∈ n.primeFactors → Real.exp (Real.sqrt L) ≤ (p : ℝ)) → β n = 0 := by
    intro n hn
    have hout : n ∉ candidateRoughBand c L jStar := by
      intro hm
      exact hn (fun p hp => ((mem_filter.mp hm).2 p hp).le)
    exact if_neg hout
  have hQ' : (Q : ℝ) ≤ L^(max R 0) := hQ.trans (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _))
  have hξ : L^(-(max C 0)) ≤ L^(-C) := Real.rpow_le_rpow_of_exponent_le hL1 (neg_le_neg (le_max_left _ _))
  have hR := hres (candidatePIndices c L) (subset_refl _) probes r t hrt Q (L^(-B)) (L^(-C))
    (2*Real.pi*ν+2*Real.pi*ζ 2) (-(2*Real.pi*ν)) hQ' hξ U V hUlo hUhi hVlo hVhi k hk j hjd
    pool (fun g p hp => mem_biUnion.mpr ⟨g.val,g.property,hp⟩) α₀ β γ α₁ β γ
    (by simpa only [α₀,αM,mul_assoc] using hα₀.1) hβγ.1 hβγ.2.2
    (by simpa only [α₁,αM,mul_assoc] using hα₁.1) hβγ.1 hβγ.2.2 hαrough hβrough hmoment
  have hsc := hscale U V hUlo hUhi hVlo hVhi k hk j hjd
  have htwist : ∀ p ∈ candidateRoughBand c L jStar,
      candidateAllocationFourierTwist c L rQ jStar take ξ
        (candidateRoughSlot c L rQ jStar hrQ hj) p = typeIIPhase 0 p := by
    intro p _
    rw [candidate_rough_slot_allocation_twist_eq_one c L rQ jStar hrQ hj take hkeep ξ p,typeIIPhase_zero]
  have heq := hraw rQ jStar hrQ hj (Real.exp (4*L)) take hkeep
    (candidateAllocationFourierTwist c L rQ jStar take ξ) 0 htwist Z k (Ioc lo hi) αM ν χ ζ
    hsc.1 hsc.2.2.1 hsc.2.2.2
    (fun m hm => (Nat.zero_le lo).trans_lt (mem_Ioc.mp hm).1)
    (by intro m hm; simp only [αM,typeIIRestrict,if_neg hm,Complex.ofReal_zero])
    (by
      intro m _ hm
      exact (hfree κM hκM hκmax m
        ((typeIIRestrict_complex_ne_zero_iff _ _ _).mp hm).2).2)
    J probes r t hrt Q (L^(-B)) (L^(-C))
  simp only [neg_zero,typeIIPhase_zero] at heq
  rw [← heq]
  have hbound := physical_raw_harmonic_two_term_bound P mass probes r t hrt Q (L^(-B)) (L^(-C))
    (2*Real.pi*ν+2*Real.pi*ζ 2) (-(2*Real.pi*ν)) Z k pool α₀ β γ α₁ β γ
    (L^(-(D+1))) (L^(-(D+1))) hR (by
      simpa only [α₀,α₁,αM,β,γ,pool,mul_assoc] using hEC)
  apply hbound.trans
  calc
    L^(-(D+1))+L^(-(D+1)) = 2*L^(-(D+1)) := by ring
    _ ≤ L*L^(-(D+1)) := mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hL0.le _)
    _ = L^(-D) := by
      nth_rw 1 [← Real.rpow_one L]
      rw [← Real.rpow_add hL0]
      congr 1
      ring

end Bounty.WeakZeroFree


-- Source module: SelectedCentralMoments

/- A selected-data central moment premise with the threshold before all later precision choices. -/

open Finset Filter
open scoped Classical
namespace Bounty

def CandidateSelectedCentralMoments (c bWindow : ℝ) (rQ : ℕ) : Prop :=
  ∃ J₀ : ℕ, ∀ jStar : ℕ, J₀ < jStar →
    ∀ Kdet : ℝ, 0 ≤ Kdet → ∀ D T F : ℝ,
    ∃ (J : ℕ) (B C R η : ℝ), 0 ≤ B ∧ 0 < η ∧
    ∀ᶠ L : ℝ in atTop,
      ∀ (hrQ : 0 < rQ) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*rQ) → Bool)
        (_hkeep : take ((candidateAllocationOrder c L rQ).symm
          (candidateRoughSlot c L rQ jStar hrQ hj)) = false)
        (_ξ : ActiveAllocationIndex (candidateAllocationActive c L rQ jStar) → ℝ)
        (ν : ℝ) (ζ : EuclideanSpace ℝ (Fin 3)),
      ‖ν‖ ≤ L^T → ‖ζ‖ ≤ L^F →
      ∀ U V : ℝ, Real.exp (bWindow*L) ≤ U → U ≤ Real.exp L →
        Real.exp (bWindow*L) ≤ V → V ≤ Real.exp L →
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L Kdet : ℤ))
          (typeIIAdmissibleDeterminantBound L Kdet : ℤ), k ≠ 0 →
      ∀ j ∈ range (typeIISmoothDyadicCount L),
      let Z := typeIISmoothDyadicScale U V (U*L^(-Kdet)) j
      let P := fun g : candidatePIndices c L => candidatePBand (c*L) g.val
      let mass := fun g => ∑ p ∈ P g, 1/(p : ℝ)
      ∃ (probes : candidatePIndices c L → Finset (Fin J))
        (r t : Finset (candidatePIndices c L)) (hrt : Disjoint r t),
      (∀ g ∈ r ∪ t, g.val ∈ candidateBigPIndices c L) ∧
      ∃ Q : ℕ, (Q : ℝ) ≤ L^R ∧
        physicalCentralHarmonicMoment (ell := 1) P mass probes r t hrt Q (L^(-B)) (L^(-C))
          (2*Real.pi*ν+2*Real.pi*ζ 2) (-(2*Real.pi*ν)) Z k L η (D+1)

end Bounty


-- Source module: ActualPrimeBlockCentral

/- Prime blocks from a selected central moment, with the fixed index chosen first. -/

open Finset Filter
open scoped Classical
namespace Bounty.WeakZeroFree

theorem exists_actual_prime_block_of_selected_central_moments
    (hZeta : PrimitiveZeroFreeRightOf (23 / 24)) {c : ℝ} (hc : 0 < c) {r : ℕ} (hr : 6 ≤ r)
    (hmoment : CandidateSelectedCentralMoments c (1/5) r) :
    ∃ J₀ : ℕ, ∀ jStar : ℕ, J₀ < jStar → ∀ D : ℝ,
      ∃ S₀ : ℝ, 0 ≤ S₀ ∧ ∀ S : ℝ, S₀ ≤ S → ∀ᶠ L : ℝ in atTop,
      ∀ κ : ℝ, 0 ≤ κ → κ ≤ 1/50 → ∀ proxy : Bool, ∀ i j : ℕ,
      let H := ⌊33*Real.exp L⌋₊
      let M := dyadicNatBucket (Icc 1 H) i
      let N := dyadicNatBucket (Icc 1 H) j
      let α := typeIIRestrict M (ambientPrimeTypeIIAlpha κ L S)
      let β := typeIIRestrict N (if proxy then ambientProxyTypeIIBeta κ L S else ambientPrimeTypeIIBeta κ L)
      let B := shiftedTypeIIBilinear (arithmeticProductWindow 1 (Real.exp L))
        (candidateCoefficient c L (1/2) r jStar) α β
      B ≠ 0 → |B| ≤ Real.exp L*L^(-D) := by
  obtain ⟨Jblock,hblock⟩ := exists_actual_prime_block_harmonic_reduction hc hr
  obtain ⟨Jb0,hb0⟩ := exists_actual_prime_b0_decay_of_central_moment hZeta hc (by norm_num : (0 : ℝ) < 1/5)
  obtain ⟨Jmoment,hmoment⟩ := hmoment
  refine ⟨max Jblock (max Jb0 Jmoment),?_⟩
  intro jStar hjStar D
  have hjblock := (le_max_left Jblock (max Jb0 Jmoment)).trans_lt hjStar
  have hjb0 := ((le_max_left Jb0 Jmoment).trans (le_max_right Jblock (max Jb0 Jmoment))).trans_lt hjStar
  have hjmoment := ((le_max_right Jb0 Jmoment).trans (le_max_right Jblock (max Jb0 Jmoment))).trans_lt hjStar
  obtain ⟨T,_hT,K,hK,hblock⟩ := hblock jStar hjblock D
  obtain ⟨Q,F,_hQ,_hF,hblock⟩ := hblock K le_rfl
  obtain ⟨J,B,C,R,η,hB,hη,hmoment⟩ := hmoment jStar hjmoment K hK.le Q T F
  obtain ⟨S₀,hS₀,hb0⟩ := hb0 jStar hjb0 K hK.le Q J B C R T F η hB hη
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [hblock S (hS₀.trans hS),hb0 S hS,hmoment,
    eventually_ambient_prime_active_dyadic_bounds,eventually_fixed_candidateQ_prefix hc jStar]
    with L hblock hb0 hmoment hsizes hprefix
  intro κ hκ hκmax proxy i j
  dsimp only
  intro hne
  apply hblock κ hκ hκmax proxy i j hne
  intro ν hν take htake ξ _hξ k hk hk0 jd hjd χ ζ hζ
  have hr0 : 0 < r := by omega
  have hj : jStar ∈ candidateQIndices c L := hprefix (mem_Icc.mpr ⟨Nat.zero_le _,le_rfl⟩)
  have hkeep : take ((candidateAllocationOrder c L r).symm
      (candidateRoughSlot c L r jStar hr0 hj)) = false := by
    apply htake
    simp only [candidateAllocationActive,Equiv.apply_symm_apply,candidateRoughSlot,
      and_self,not_true_eq_false,decide_false]
  have hsize := hsizes κ S hκ hκmax proxy (arithmeticProductWindow 1 (Real.exp L))
    (candidateCoefficient c L (1/2) r jStar) ⌊33*Real.exp L⌋₊ i j hne
  obtain ⟨probes,rP,tP,hrt,hbig,q,hq,hmom⟩ := hmoment hr0 hj take hkeep ξ ν ζ hν hζ
    (originalDyadicBase i) (originalDyadicBase j) hsize.1 hsize.2.1 hsize.2.2.1 hsize.2.2.2
    k hk hk0 jd hjd
  have htest := hb0 r hr0 hj take hkeep ξ ((2 : ℕ)^i-1)
    (min ⌊33*Real.exp L⌋₊ ((2 : ℕ)^(i+1)-1)) κ hκ hκmax ν ζ hν hζ
    (originalDyadicBase i) (originalDyadicBase j) hsize.1 hsize.2.1 hsize.2.2.1 hsize.2.2.2
    k hk hk0 χ jd hjd probes rP tP hrt hbig q hq hmom
  simpa only [dyadicNatBucket_Icc_eq_Ioc] using htest

end Bounty.WeakZeroFree


-- Source module: ActualRoughB0Decay

/- The literal original B0 harmonic correlation follows from its selected central moment. -/

open Finset Filter MeasureTheory
open scoped Classical ComplexConjugate
namespace Bounty.WeakZeroFree

theorem exists_actual_rough_b0_decay_of_central_moment
    (hZeta : PrimitiveZeroFreeRightOf (23 / 24)) {c bWindow γrough vMax ρ : ℝ}
    (hc : 0 < c) (hb : 0 < bWindow)
    (hγrough : 0 < γrough) (hvMax : vMax < 1) (hρ : 0 < ρ) :
    ∃ J₀ : ℕ, ∀ jStar : ℕ, J₀ < jStar →
      ∀ Kdet : ℝ, 0 ≤ Kdet → ∀ (D : ℝ) (J : ℕ) (B C R T F η : ℝ),
      0 ≤ B → 0 < η →
    ∃ S₀ : ℝ, 0 ≤ S₀ ∧ ∀ S : ℝ, S₀ ≤ S → ∀ᶠ L : ℝ in atTop,
      ∀ (rQ : ℕ) (hrQ : 0 < rQ) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*rQ) → Bool)
        (_hkeep : take ((candidateAllocationOrder c L rQ).symm
          (candidateRoughSlot c L rQ jStar hrQ hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L rQ jStar) → ℝ)
        (lo hi : ℕ) (aM vM : ℝ), vM ≤ vMax →
      ∀ (ν : ℝ) (ζ : EuclideanSpace ℝ (Fin 3)), ‖ν‖ ≤ L^T → ‖ζ‖ ≤ L^F →
      ∀ U V : ℝ, Real.exp (bWindow*L) ≤ U → U ≤ Real.exp L →
        Real.exp (bWindow*L) ≤ V → V ≤ Real.exp L →
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L Kdet : ℤ))
          (typeIIAdmissibleDeterminantBound L Kdet : ℤ), k ≠ 0 →
      ∀ (χ : DirichletCharacter ℂ (2*k.natAbs)) j, j ∈ range (typeIISmoothDyadicCount L) →
      let Z := typeIISmoothDyadicScale U V (U*L^(-Kdet)) j
      let P := fun g : candidatePIndices c L => candidatePBand (c*L) g.val
      let mass := fun g => ∑ p ∈ P g, 1/(p : ℝ)
      ∀ (probes : candidatePIndices c L → Finset (Fin J)) (r t : Finset (candidatePIndices c L))
        (hrt : Disjoint r t), (∀ g ∈ r ∪ t, g.val ∈ candidateBigPIndices c L) →
      ∀ Q : ℕ, (Q : ℝ) ≤ L^R →
      physicalCentralHarmonicMoment (ell := 1) P mass probes r t hrt Q (L^(-B)) (L^(-C))
        (2*Real.pi*ν+2*Real.pi*ζ 2) (-(2*Real.pi*ν)) Z k L η (D+1) →
      ‖candidateB0HarmonicCorrelation c L (1/2) rQ jStar
        (candidateSmallPSet c L (Real.exp (4*L))) take
        (candidateAllocationFourierTwist c L rQ jStar take ξ) ν Z k (Ioc lo hi)
        (fun m => (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM vM) m : ℂ)) χ ζ‖ ≤ L^(-D) := by
  obtain ⟨J₀,hbase⟩ := exists_actual_rough_comparison_harmonic_decay_uniform_window hZeta hc hb hγrough hvMax hρ
  refine ⟨J₀,?_⟩
  intro jStar hjStar Kdet hKdet D J B C R T F η hB hη
  obtain ⟨S₀,hS₀,hcmp⟩ := hbase jStar hjStar Kdet hKdet (D+1) J 1 B C R (Kdet+89)
    0 0 (Kdet+89) (max T F+1) (max T F+1) (by decide) hB (by linarith)
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [hcmp S hS,
    eventually_actual_residual_of_central_moment hc hb hKdet (le_max_right R 0) (le_max_right C 0)
      hη J 1 (D+1),
    eventually_candidate_raw_average_eq_b0 hc,
    eventually_actual_harmonic_scale_inputs hb hKdet,
    eventually_actual_rough_source_factor_properties hc hγrough,
    eventually_actual_remaining_factor_properties hc,
    eventually_rough_typeII_restriction_properties hγrough,
    eventually_ambient_rough_endpoint_group_free hc hγrough,
    eventually_original_harmonic_modulus_bound hKdet,
    eventually_original_endpoint_phase_bounds T F,
    eventually_ge_atTop (2 : ℝ)]
    with L hcmp hres hraw hscale hfactor hremain hrough hfree hmod hphase hL
  intro rQ hrQ hj take hkeep ξ lo hi aM vM hvM ν ζ hν hζ U V hUlo hUhi hVlo hVhi
    k hk hk0 χ j hjd Z P mass probes r t hrt hbig Q hQ hmoment
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  let : NeZero (2*k.natAbs) := ⟨Nat.ne_of_gt (Nat.mul_pos (by decide) (Int.natAbs_pos.mpr hk0))⟩
  let pool := (candidatePIndices c L).biUnion (candidatePBand (c*L))
  let αM := fun m => (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM vM) m : ℂ)
  let α₀ := fun m => αM m*χ (m : ZMod (2*k.natAbs))*typeIIPhase (2*Real.pi*ν-2*Real.pi*ζ 1) m
  let α₁ := fun m => αM m*χ (m : ZMod (2*k.natAbs))*typeIIPhase (2*Real.pi*ζ 0+2*Real.pi*ν) m
  let β := fun n => if n ∈ candidateRoughBand c L jStar then (1 : ℂ) else 0
  let γ := fun n => conj (candidateResidualPrimeCoefficient c L rQ jStar hrQ hj take hkeep
    (candidateAllocationFourierTwist c L rQ jStar take ξ) n)
  have hchar (n : ℕ) : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 := by
    rw [Subsingleton.elim (n : ZMod 1) 1, map_one]
  have hph := hphase ν ζ hν hζ
  have hkfull : (k.natAbs : ℝ) ≤ L^(Kdet+89) := by
    have hm := hmod k hk
    push_cast at hm
    nlinarith [Nat.cast_nonneg (α := ℝ) k.natAbs]
  have hEC := hcmp rQ hrQ hj take hkeep ξ lo hi aM vM
    (2*Real.pi*ν-2*Real.pi*ζ 1) (2*Real.pi*ζ 0+2*Real.pi*ν) (2*k.natAbs) χ
    hvM (hmod k hk) (hph.2 1).2 (by simpa only [add_comm] using (hph.2 0).1)
    0 1 1 (by simp) (by simp) probes r t hrt hbig Q hQ
    U V hUlo hUhi hVlo hVhi k hk hk0 hkfull j hjd
    (2*Real.pi*ν+2*Real.pi*ζ 2) (-(2*Real.pi*ν)) (hph.2 2).1
  simp only [typeIIPhase_zero,hchar,mul_one] at hEC
  have hα₀ := hfactor S aM vM (Ioc lo hi) (2*k.natAbs) χ (2*Real.pi*ν-2*Real.pi*ζ 1)
  have hα₁ := hfactor S aM vM (Ioc lo hi) (2*k.natAbs) χ (2*Real.pi*ζ 0+2*Real.pi*ν)
  have hβγ := hremain rQ jStar hrQ hj take hkeep ξ (fun _ => 1) (by intro n; simp)
  have hαrough : ∀ n, ¬ (∀ p : ℕ, p ∈ n.primeFactors → Real.exp (Real.sqrt L) ≤ (p : ℝ)) → α₀ n = 0 := by
    intro n hn
    have hz : ambientRoughIntervalTypeIIAlpha γrough L S aM vM n = 0 := by
      by_contra hne
      exact hn (fun p hp => (((hrough S (ambientRoughCofactorRange L aM vM) n).2 hne).2 p hp).le)
    simp only [α₀,αM,typeIIRestrict,hz,ite_self,Complex.ofReal_zero,zero_mul]
  have hβrough : ∀ n, ¬ (∀ p : ℕ, p ∈ n.primeFactors → Real.exp (Real.sqrt L) ≤ (p : ℝ)) → β n = 0 := by
    intro n hn
    have hout : n ∉ candidateRoughBand c L jStar := by
      intro hm
      exact hn (fun p hp => ((mem_filter.mp hm).2 p hp).le)
    exact if_neg hout
  have hQ' : (Q : ℝ) ≤ L^(max R 0) := hQ.trans (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _))
  have hξ : L^(-(max C 0)) ≤ L^(-C) := Real.rpow_le_rpow_of_exponent_le hL1 (neg_le_neg (le_max_left _ _))
  have hR := hres (candidatePIndices c L) (subset_refl _) probes r t hrt Q (L^(-B)) (L^(-C))
    (2*Real.pi*ν+2*Real.pi*ζ 2) (-(2*Real.pi*ν)) hQ' hξ U V hUlo hUhi hVlo hVhi k hk j hjd
    pool (fun g p hp => mem_biUnion.mpr ⟨g.val,g.property,hp⟩) α₀ β γ α₁ β γ
    (by simpa only [α₀,αM,mul_assoc] using hα₀.1) hβγ.1 hβγ.2.2
    (by simpa only [α₁,αM,mul_assoc] using hα₁.1) hβγ.1 hβγ.2.2 hαrough hβrough hmoment
  have hsc := hscale U V hUlo hUhi hVlo hVhi k hk j hjd
  have htwist : ∀ p ∈ candidateRoughBand c L jStar,
      candidateAllocationFourierTwist c L rQ jStar take ξ
        (candidateRoughSlot c L rQ jStar hrQ hj) p = typeIIPhase 0 p := by
    intro p _
    rw [candidate_rough_slot_allocation_twist_eq_one c L rQ jStar hrQ hj take hkeep ξ p,typeIIPhase_zero]
  have heq := hraw rQ jStar hrQ hj (Real.exp (4*L)) take hkeep
    (candidateAllocationFourierTwist c L rQ jStar take ξ) 0 htwist Z k (Ioc lo hi) αM ν χ ζ
    hsc.1 hsc.2.2.1 hsc.2.2.2
    (fun m hm => (Nat.zero_le lo).trans_lt (mem_Ioc.mp hm).1)
    (by intro m hm; simp only [αM,typeIIRestrict,if_neg hm,Complex.ofReal_zero])
    (by
      intro m _ hm
      exact (hfree S aM vM m
        ((typeIIRestrict_complex_ne_zero_iff _ _ _).mp hm).2).2)
    J probes r t hrt Q (L^(-B)) (L^(-C))
  simp only [neg_zero,typeIIPhase_zero] at heq
  rw [← heq]
  have hbound := physical_raw_harmonic_two_term_bound P mass probes r t hrt Q (L^(-B)) (L^(-C))
    (2*Real.pi*ν+2*Real.pi*ζ 2) (-(2*Real.pi*ν)) Z k pool α₀ β γ α₁ β γ
    (L^(-(D+1))) (L^(-(D+1))) hR (by
      simpa only [α₀,α₁,αM,β,γ,pool,mul_assoc] using hEC)
  apply hbound.trans
  calc
    L^(-(D+1))+L^(-(D+1)) = 2*L^(-(D+1)) := by ring
    _ ≤ L*L^(-(D+1)) := mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hL0.le _)
    _ = L^(-D) := by
      nth_rw 1 [← Real.rpow_one L]
      rw [← Real.rpow_add hL0]
      congr 1
      ring

end Bounty.WeakZeroFree


-- Source module: ActualRoughBlockCentral

/- Rough blocks from a selected central moment, with the fixed index chosen first. -/

open Finset Filter
open scoped Classical
namespace Bounty.WeakZeroFree

theorem exists_actual_rough_block_of_selected_central_moments
    (hZeta : PrimitiveZeroFreeRightOf (23 / 24)) {c γ a v : ℝ} (hc : 0 < c) (hγ : 0 < γ) (ha : 0 < a) (hv : v < 1) {r : ℕ} (hr : 6 ≤ r)
    (hmoment : CandidateSelectedCentralMoments c (min ((1-v)/2) (a/2)) r) :
    ∃ J₀ : ℕ, ∀ jStar : ℕ, J₀ < jStar → ∀ D : ℝ,
      ∃ S₀ : ℝ, 0 ≤ S₀ ∧ ∀ S : ℝ, S₀ ≤ S → ∀ᶠ L : ℝ in atTop,
      ∀ i j : ℕ,
      let H := ⌊33*Real.exp L⌋₊
      let M := dyadicNatBucket (Icc 1 H) i
      let N := dyadicNatBucket (Icc 1 H) j
      let α := typeIIRestrict M (ambientRoughIntervalTypeIIAlpha γ L S a v)
      let β := typeIIRestrict N (ambientRoughTypeIIBeta (Real.exp (a*L)) (Real.exp (v*L)))
      let B := shiftedTypeIIBilinear (arithmeticProductWindow 1 (Real.exp L))
        (candidateCoefficient c L (1/2) r jStar) α β
      B ≠ 0 → |B| ≤ Real.exp L*L^(-D) := by
  obtain ⟨Jblock,hblock⟩ := exists_actual_rough_block_harmonic_reduction hc hγ ha hv hr
  obtain ⟨Jb0,hb0⟩ := exists_actual_rough_b0_decay_of_central_moment hZeta hc
    (lt_min (by linarith : (0 : ℝ) < (1-v)/2) (by linarith : (0 : ℝ) < a/2)) hγ hv (by norm_num : (0 : ℝ) < 1)
  obtain ⟨Jmoment,hmoment⟩ := hmoment
  refine ⟨max Jblock (max Jb0 Jmoment),?_⟩
  intro jStar hjStar D
  have hjblock := (le_max_left Jblock (max Jb0 Jmoment)).trans_lt hjStar
  have hjb0 := ((le_max_left Jb0 Jmoment).trans (le_max_right Jblock (max Jb0 Jmoment))).trans_lt hjStar
  have hjmoment := ((le_max_right Jb0 Jmoment).trans (le_max_right Jblock (max Jb0 Jmoment))).trans_lt hjStar
  obtain ⟨T,_hT,K,hK,hblock⟩ := hblock jStar hjblock D
  obtain ⟨Q,F,_hQ,_hF,hblock⟩ := hblock K le_rfl
  obtain ⟨J,B,C,R,η,hB,hη,hmoment⟩ := hmoment jStar hjmoment K hK.le Q T F
  obtain ⟨S₀,hS₀,hb0⟩ := hb0 jStar hjb0 K hK.le Q J B C R T F η hB hη
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [hblock S (hS₀.trans hS),hb0 S hS,hmoment,
    eventually_ambient_rough_active_dyadic_bounds ha hv,eventually_fixed_candidateQ_prefix hc jStar]
    with L hblock hb0 hmoment hsizes hprefix
  intro i j
  dsimp only
  intro hne
  apply hblock i j hne
  intro ν hν take htake ξ _hξ k hk hk0 jd hjd χ ζ hζ
  have hr0 : 0 < r := by omega
  have hj : jStar ∈ candidateQIndices c L := hprefix (mem_Icc.mpr ⟨Nat.zero_le _,le_rfl⟩)
  have hkeep : take ((candidateAllocationOrder c L r).symm
      (candidateRoughSlot c L r jStar hr0 hj)) = false := by
    apply htake
    simp only [candidateAllocationActive,Equiv.apply_symm_apply,candidateRoughSlot,
      and_self,not_true_eq_false,decide_false]
  have hsize := hsizes γ S a v le_rfl le_rfl (arithmeticProductWindow 1 (Real.exp L))
    (candidateCoefficient c L (1/2) r jStar) ⌊33*Real.exp L⌋₊ i j hne
  obtain ⟨probes,rP,tP,hrt,hbig,q,hq,hmom⟩ := hmoment hr0 hj take hkeep ξ ν ζ hν hζ
    (originalDyadicBase i) (originalDyadicBase j) hsize.1 hsize.2.1 hsize.2.2.1 hsize.2.2.2
    k hk hk0 jd hjd
  have htest := hb0 r hr0 hj take hkeep ξ ((2 : ℕ)^i-1)
    (min ⌊33*Real.exp L⌋₊ ((2 : ℕ)^(i+1)-1)) a v le_rfl ν ζ hν hζ
    (originalDyadicBase i) (originalDyadicBase j) hsize.1 hsize.2.1 hsize.2.2.1 hsize.2.2.2
    k hk hk0 χ jd hjd probes rP tP hrt hbig q hq hmom
  simpa only [dyadicNatBucket_Icc_eq_Ioc] using htest

end Bounty.WeakZeroFree


-- Source module: HalfActiveCentralMoments

/- The half-active block contract follows from selected central moments. -/

open Finset Filter
open scoped Classical
namespace Bounty.WeakZeroFree

theorem candidate_half_active_blocks_of_selected_central_moments
    (hZeta : PrimitiveZeroFreeRightOf (23 / 24))
    (hmoment : ∀ (c : ℝ) (r : ℕ), 0 < c → 6 ≤ r → (11/5 : ℝ)*(r : ℝ)*c = 1 →
      ∀ bWindow : ℝ, 0 < bWindow → CandidateSelectedCentralMoments c bWindow r) :
    CandidateHalfActiveBlockBounds := by
  intro c r hc hr hcenter D _hD κ b N hκ hκmax hb hbq hN
  constructor
  · intro z
    let a := reciprocalGrid b (1/2-κ) N (z : ℕ)
    let v := reciprocalGrid b (1/2-κ) N ((z : ℕ)+1)
    have ha : 0 < a := hb.trans_le (reciprocal_grid_mem hbq.le hN z.isLt.le).1
    have hv : v < 1 := lt_of_le_of_lt
      (reciprocal_grid_mem hbq.le hN (Nat.succ_le_of_lt z.isLt)).2 (by linarith)
    have hwindow : 0 < min ((1-v)/2) (a/2) := lt_min (by linarith) (by linarith)
    obtain ⟨J,hblock⟩ := exists_actual_rough_block_of_selected_central_moments hZeta hc ha ha hv hr
      (hmoment c r hc hr hcenter _ hwindow)
    refine ⟨J,?_⟩
    intro jStar hj
    obtain ⟨S₀,hS₀,hblock⟩ := hblock jStar hj D
    refine ⟨S₀,hS₀,?_⟩
    intro S hS
    filter_upwards [hblock S hS] with L hblock
    intro i _hi j _hj
    exact hblock i j
  · obtain ⟨J,hblock⟩ := exists_actual_prime_block_of_selected_central_moments hZeta hc hr
      (hmoment c r hc hr hcenter (1/5) (by norm_num))
    refine ⟨J,?_⟩
    intro jStar hj
    obtain ⟨S₀,hS₀,hblock⟩ := hblock jStar hj D
    refine ⟨S₀,hS₀,?_⟩
    intro S hS
    filter_upwards [hblock S hS] with L hblock
    intro proxy i _hi j _hj
    exact hblock κ hκ.le hκmax proxy i j

end Bounty.WeakZeroFree


namespace Bounty.WeakZeroFree

theorem actual_prime_b0_decay_of_central_moment
     {c bWindow : ℝ}
    (hc : 0 < c) (hb : 0 < bWindow) :
    ∃ J₀ : ℕ, ∀ jStar : ℕ, J₀ < jStar →
      ∀ Kdet : ℝ, 0 ≤ Kdet → ∀ (D : ℝ) (J : ℕ) (B C R T F η : ℝ),
      0 ≤ B → 0 < η →
    ∃ S₀ : ℝ, 0 ≤ S₀ ∧ ∀ S : ℝ, S₀ ≤ S → ∀ᶠ L : ℝ in atTop,
      ∀ (rQ : ℕ) (hrQ : 0 < rQ) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*rQ) → Bool)
        (_hkeep : take ((candidateAllocationOrder c L rQ).symm
          (candidateRoughSlot c L rQ jStar hrQ hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L rQ jStar) → ℝ)
        (lo hi : ℕ) (κM : ℝ), 0 ≤ κM → κM ≤ 1/50 →
      ∀ (ν : ℝ) (ζ : EuclideanSpace ℝ (Fin 3)), ‖ν‖ ≤ L^T → ‖ζ‖ ≤ L^F →
      ∀ U V : ℝ, Real.exp (bWindow*L) ≤ U → U ≤ Real.exp L →
        Real.exp (bWindow*L) ≤ V → V ≤ Real.exp L →
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L Kdet : ℤ))
          (typeIIAdmissibleDeterminantBound L Kdet : ℤ), k ≠ 0 →
      ∀ (χ : DirichletCharacter ℂ (2*k.natAbs)) j, j ∈ range (typeIISmoothDyadicCount L) →
      let Z := typeIISmoothDyadicScale U V (U*L^(-Kdet)) j
      let P := fun g : candidatePIndices c L => candidatePBand (c*L) g.val
      let mass := fun g => ∑ p ∈ P g, 1/(p : ℝ)
      ∀ (probes : candidatePIndices c L → Finset (Fin J)) (r t : Finset (candidatePIndices c L))
        (hrt : Disjoint r t), (∀ g ∈ r ∪ t, g.val ∈ candidateBigPIndices c L) →
      ∀ Q : ℕ, (Q : ℝ) ≤ L^R →
      physicalCentralHarmonicMoment (ell := 1) P mass probes r t hrt Q (L^(-B)) (L^(-C))
        (2*Real.pi*ν+2*Real.pi*ζ 2) (-(2*Real.pi*ν)) Z k L η (D+1) →
      ‖candidateB0HarmonicCorrelation c L (1/2) rQ jStar
        (candidateSmallPSet c L (Real.exp (4*L))) take
        (candidateAllocationFourierTwist c L rQ jStar take ξ) ν Z k (Ioc lo hi)
        (fun m => (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) m : ℂ)) χ ζ‖ ≤ L^(-D) := by
  exact exists_actual_prime_b0_decay_of_central_moment actual_zero_free hc hb

theorem actual_prime_block_of_selected_central_moments
     {c : ℝ} (hc : 0 < c) {r : ℕ} (hr : 6 ≤ r)
    (hmoment : CandidateSelectedCentralMoments c (1/5) r) :
    ∃ J₀ : ℕ, ∀ jStar : ℕ, J₀ < jStar → ∀ D : ℝ,
      ∃ S₀ : ℝ, 0 ≤ S₀ ∧ ∀ S : ℝ, S₀ ≤ S → ∀ᶠ L : ℝ in atTop,
      ∀ κ : ℝ, 0 ≤ κ → κ ≤ 1/50 → ∀ proxy : Bool, ∀ i j : ℕ,
      let H := ⌊33*Real.exp L⌋₊
      let M := dyadicNatBucket (Icc 1 H) i
      let N := dyadicNatBucket (Icc 1 H) j
      let α := typeIIRestrict M (ambientPrimeTypeIIAlpha κ L S)
      let β := typeIIRestrict N (if proxy then ambientProxyTypeIIBeta κ L S else ambientPrimeTypeIIBeta κ L)
      let B := shiftedTypeIIBilinear (arithmeticProductWindow 1 (Real.exp L))
        (candidateCoefficient c L (1/2) r jStar) α β
      B ≠ 0 → |B| ≤ Real.exp L*L^(-D) := by
  exact exists_actual_prime_block_of_selected_central_moments actual_zero_free hc hr hmoment

theorem actual_rough_b0_decay_of_central_moment
     {c bWindow γrough vMax ρ : ℝ}
    (hc : 0 < c) (hb : 0 < bWindow)
    (hγrough : 0 < γrough) (hvMax : vMax < 1) (hρ : 0 < ρ) :
    ∃ J₀ : ℕ, ∀ jStar : ℕ, J₀ < jStar →
      ∀ Kdet : ℝ, 0 ≤ Kdet → ∀ (D : ℝ) (J : ℕ) (B C R T F η : ℝ),
      0 ≤ B → 0 < η →
    ∃ S₀ : ℝ, 0 ≤ S₀ ∧ ∀ S : ℝ, S₀ ≤ S → ∀ᶠ L : ℝ in atTop,
      ∀ (rQ : ℕ) (hrQ : 0 < rQ) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*rQ) → Bool)
        (_hkeep : take ((candidateAllocationOrder c L rQ).symm
          (candidateRoughSlot c L rQ jStar hrQ hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L rQ jStar) → ℝ)
        (lo hi : ℕ) (aM vM : ℝ), vM ≤ vMax →
      ∀ (ν : ℝ) (ζ : EuclideanSpace ℝ (Fin 3)), ‖ν‖ ≤ L^T → ‖ζ‖ ≤ L^F →
      ∀ U V : ℝ, Real.exp (bWindow*L) ≤ U → U ≤ Real.exp L →
        Real.exp (bWindow*L) ≤ V → V ≤ Real.exp L →
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L Kdet : ℤ))
          (typeIIAdmissibleDeterminantBound L Kdet : ℤ), k ≠ 0 →
      ∀ (χ : DirichletCharacter ℂ (2*k.natAbs)) j, j ∈ range (typeIISmoothDyadicCount L) →
      let Z := typeIISmoothDyadicScale U V (U*L^(-Kdet)) j
      let P := fun g : candidatePIndices c L => candidatePBand (c*L) g.val
      let mass := fun g => ∑ p ∈ P g, 1/(p : ℝ)
      ∀ (probes : candidatePIndices c L → Finset (Fin J)) (r t : Finset (candidatePIndices c L))
        (hrt : Disjoint r t), (∀ g ∈ r ∪ t, g.val ∈ candidateBigPIndices c L) →
      ∀ Q : ℕ, (Q : ℝ) ≤ L^R →
      physicalCentralHarmonicMoment (ell := 1) P mass probes r t hrt Q (L^(-B)) (L^(-C))
        (2*Real.pi*ν+2*Real.pi*ζ 2) (-(2*Real.pi*ν)) Z k L η (D+1) →
      ‖candidateB0HarmonicCorrelation c L (1/2) rQ jStar
        (candidateSmallPSet c L (Real.exp (4*L))) take
        (candidateAllocationFourierTwist c L rQ jStar take ξ) ν Z k (Ioc lo hi)
        (fun m => (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM vM) m : ℂ)) χ ζ‖ ≤ L^(-D) := by
  exact exists_actual_rough_b0_decay_of_central_moment actual_zero_free hc hb hγrough hvMax hρ

theorem actual_rough_block_of_selected_central_moments
     {c γ a v : ℝ} (hc : 0 < c) (hγ : 0 < γ) (ha : 0 < a) (hv : v < 1) {r : ℕ} (hr : 6 ≤ r)
    (hmoment : CandidateSelectedCentralMoments c (min ((1-v)/2) (a/2)) r) :
    ∃ J₀ : ℕ, ∀ jStar : ℕ, J₀ < jStar → ∀ D : ℝ,
      ∃ S₀ : ℝ, 0 ≤ S₀ ∧ ∀ S : ℝ, S₀ ≤ S → ∀ᶠ L : ℝ in atTop,
      ∀ i j : ℕ,
      let H := ⌊33*Real.exp L⌋₊
      let M := dyadicNatBucket (Icc 1 H) i
      let N := dyadicNatBucket (Icc 1 H) j
      let α := typeIIRestrict M (ambientRoughIntervalTypeIIAlpha γ L S a v)
      let β := typeIIRestrict N (ambientRoughTypeIIBeta (Real.exp (a*L)) (Real.exp (v*L)))
      let B := shiftedTypeIIBilinear (arithmeticProductWindow 1 (Real.exp L))
        (candidateCoefficient c L (1/2) r jStar) α β
      B ≠ 0 → |B| ≤ Real.exp L*L^(-D) := by
  exact exists_actual_rough_block_of_selected_central_moments actual_zero_free hc hγ ha hv hr hmoment

theorem actual_candidate_half_active_blocks_of_selected_central_moments
    
    (hmoment : ∀ (c : ℝ) (r : ℕ), 0 < c → 6 ≤ r → (11/5 : ℝ)*(r : ℝ)*c = 1 →
      ∀ bWindow : ℝ, 0 < bWindow → CandidateSelectedCentralMoments c bWindow r) :
    CandidateHalfActiveBlockBounds := by
  exact candidate_half_active_blocks_of_selected_central_moments actual_zero_free hmoment

end Bounty.WeakZeroFree
