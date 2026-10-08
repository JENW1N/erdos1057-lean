import ConditionalSelectedTarget

/-! The exact remaining original residue-model estimate implies the challenge target. -/

open scoped Topology BigOperators Classical

-- Source module: CandidateRootReplacement

/- The actual candidate prime pools meet every prime and mass hypothesis
of finite root replacement at the chosen moment length. -/

open Finset Filter
open scoped Classical
namespace Bounty

theorem eventually_candidate_root_replacement
    {scale γ E B : ℝ} (hscale : 0 < scale) (hγ : 0 < γ)
    (hE : 0 ≤ E) (hB : 0 ≤ B) (J ell : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (S : Finset ℕ), S ⊆ candidatePIndices scale L →
      let P := fun g : S => candidatePBand (scale * L) g.val
      let V := fun g : S => ∑ p ∈ P g, 1 / (p : ℝ)
      ∀ [∀ p : PhysicalPrime P, NeZero p.2.val]
        (I : Type) (patterns : Finset I) (cuts : I → S → Finset (Fin J))
        (bounds : I → ℝ) (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ)
        (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
          PhysicalAuxLabels P (cuts i) → ℂ) (D N : ℕ) (z : ℤ),
      (∀ i ∈ patterns, 0 ≤ bounds i) → (∑ i ∈ patterns, bounds i) ≤ L ^ B →
      (∀ j i, i ∈ patterns → ∀ x y aux, ‖K j i x y aux‖ ≤ bounds i) →
      (∀ j < 2 * Nat.ceil (L ^ (13/25 : ℝ)),
        physicalOperatorStepBound P J ell patterns cuts (k j) ≤ D) →
      0 < N → γ * L ≤ Real.log (N : ℝ) →
      ‖physicalRootMoment V patterns cuts (1/2) ζ k K (Ico z (z + N))
          (2 * Nat.ceil (L ^ (13/25 : ℝ)) - 1) D -
        physicalRootResidueModel V patterns cuts (1/2) ζ k K
          (2 * Nat.ceil (L ^ (13/25 : ℝ)) - 1)‖ ≤
        Real.exp (-E * (2 * Nat.ceil (L ^ (13/25 : ℝ))) * Real.log L) := by
  obtain ⟨v, Vmax, hv, hVmax, hpools⟩ := exists_candidate_P_pool_bounds hscale
  have hC : 0 < (2 : ℝ) / (5 * Real.log 2) := by positivity
  filter_upwards [hpools, eventually_physical_root_replacement
    (a := (13/25 : ℝ)) (c := (1/10 : ℝ)) (d := (2/5 : ℝ))
    (C := (2 : ℝ) / (5 * Real.log 2)) (V := Vmax) (v := v)
    (E := E) (γ := γ) (B := B) (q := (1/2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hC hVmax hv hE hγ hB (by norm_num) (by norm_num) J ell J] with L hpools hreplace
  intro S hS P V inst I patterns cuts bounds ζ k K D N z hbounds hsum hK hcut hN hlog
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hpools.1
  have hceil : 0 < Nat.ceil (L ^ (13/25 : ℝ)) := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hL _)
  have hlen : 2 * Nat.ceil (L ^ (13/25 : ℝ)) - 1 + 1 =
      2 * Nat.ceil (L ^ (13/25 : ℝ)) := by omega
  have hdata (g : S) := hpools.2.2.2.2.2 g.val (hS g.property)
  have hdis : Pairwise (fun g h : S => Disjoint (P g) (P h)) := by
    intro g h hgh
    exact hpools.2.2.2.2.1 (Subtype.val_injective.ne hgh)
  have hcard : (Fintype.card S : ℝ) ≤ (2 / (5 * Real.log 2)) * Real.log L := by
    have hs : (S.card : ℝ) ≤ ((candidatePIndices scale L).card : ℝ) := by
      exact_mod_cast card_le_card hS
    simpa only [Fintype.card_coe] using hs.trans hpools.2.2.2.1
  have h := hreplace S P V I patterns cuts bounds ζ k K
    (2 * Nat.ceil (L ^ (13/25 : ℝ)) - 1) D N z hlen hdis
    (fun g p hp => ((hdata g).2.2 p hp).1) hcard
    (fun g => (hdata g).1) (fun _ => rfl) (fun g => (hdata g).2.1)
    (fun g p hp => ((hdata g).2.2 p hp).2.1.le)
    (fun g p hp => ((hdata g).2.2 p hp).2.2)
    (fun i _ g => (card_le_univ (cuts i g)).trans_eq (Fintype.card_fin J))
    hbounds hsum hK (by simpa only [hlen] using hcut) hN hlog
  have hlenR : ((2 * Nat.ceil (L ^ (13/25 : ℝ)) - 1 : ℕ) : ℝ) + 1 =
      2 * (Nat.ceil (L ^ (13/25 : ℝ)) : ℝ) := by exact_mod_cast hlen
  simpa only [hlenR] using h

end Bounty


-- Source module: PhysicalRootBirthAtoms

/- The actual reciprocal root birth law has the prime-atom decay required
by the common-history high-rank estimate. -/

namespace Bounty

theorem physical_root_reciprocal_atom_bound
    (p : ℕ) {L baseline V vmin : ℝ}
    (hvmin : 0 < vmin) (hV : vmin ≤ V) (hbase : 1 / 2 ≤ baseline)
    (hp : Real.exp (L ^ (3/10 : ℝ)) ≤ (p : ℝ)) :
    ((p : ℝ) * baseline)⁻¹ / V ≤
      (2 / vmin) * Real.exp (-(L ^ (3/10 : ℝ))) := by
  have hb0 : 0 ≤ baseline := by linarith
  have hden : Real.exp (L ^ (3/10 : ℝ)) * (1/2) * vmin ≤ (p : ℝ) * baseline * V := by
    calc
      _ ≤ (p : ℝ) * baseline * vmin := mul_le_mul_of_nonneg_right
        (mul_le_mul hp hbase (by norm_num) (Nat.cast_nonneg p)) hvmin.le
      _ ≤ _ := mul_le_mul_of_nonneg_left hV (mul_nonneg (Nat.cast_nonneg p) hb0)
  calc
    _ = 1 / ((p : ℝ) * baseline * V) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ 1 / (Real.exp (L ^ (3/10 : ℝ)) * (1/2) * vmin) :=
      one_div_le_one_div_of_le (by positivity) hden
    _ = _ := by
      rw [Real.exp_neg]
      field_simp

theorem root_birth_rarity_envelope_bounds
    {L vmin vmax ρ v : ℝ} (hvmin : 0 < vmin) (hρ : 0 < ρ) (hv : 0 ≤ v) :
    let η := (2 / vmin) * Real.exp (-(L ^ (3/10 : ℝ)))
    let β := max (2 / vmin) (2 * vmax * v / (ρ * vmin)) *
      Real.exp (-(L ^ (3/10 : ℝ)))
    0 < η ∧ η ≤ β ∧ 0 < β ∧
      ∀ q V : ℝ, 0 ≤ q → q ≤ 1 → vmin ≤ V → V ≤ vmax →
        |(1 - q) * V / ρ| * η * v ≤ β := by
  intro η β
  have hη : 0 < η := mul_pos (div_pos (by norm_num) hvmin) (Real.exp_pos _)
  have hηβ : η ≤ β :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  refine ⟨hη, hηβ, hη.trans_le hηβ, ?_⟩
  intro q V hq0 hq1 hVmin hVmax
  have hV0 : 0 ≤ V := hvmin.le.trans hVmin
  have hfactor : (1 - q) * V / ρ ≤ vmax / ρ := by
    apply div_le_div_of_nonneg_right _ hρ.le
    calc
      _ ≤ 1 * V := mul_le_mul_of_nonneg_right (by linarith) hV0
      _ ≤ vmax := by simpa only [one_mul] using hVmax
  rw [abs_of_nonneg (div_nonneg (mul_nonneg (sub_nonneg.mpr hq1) hV0) hρ.le)]
  calc
    _ ≤ (vmax / ρ) * η * v :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfactor hη.le) hv
    _ = (2 * vmax * v / (ρ * vmin)) * Real.exp (-(L ^ (3/10 : ℝ))) := by
      dsimp only [η]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ β := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

end Bounty


-- Source module: CandidateRootBirthAtoms

/- The actual candidate big primes and original endpoint baseline satisfy
the exponential reciprocal-atom bound at the literal moment length. -/

open Filter
namespace Bounty

theorem eventually_candidate_root_birth_atoms
    {scale q vmin : ℝ} (hscale : 0 < scale) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hvmin : 0 < vmin) :
    ∀ᶠ L : ℝ in atTop,
      ∀ i ∈ candidateBigPIndices scale L, ∀ p ∈ candidatePBand (scale * L) i,
      ∀ V : ℝ, vmin ≤ V →
        ((p : ℝ) * physicalEndpointBaseline q (2 * Nat.ceil (L ^ (13/25 : ℝ))) p)⁻¹ / V ≤
          (2 / vmin) * Real.exp (-(L ^ (3/10 : ℝ))) := by
  obtain ⟨_, _, _, _, hbig⟩ := eventually_candidate_P_groups
    (α := (3/10 : ℝ)) (β := (2/5 : ℝ)) hscale (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [hbig, eventually_gt_atTop (0 : ℝ),
    eventually_repeated_big_visit_density_le (alpha := 13/25) (tau := 1)
      zero_lt_one (by norm_num),
    eventually_mul_rpow_log_add_le_rpow (a := 0) (b := 3/10) (c := 1)
      (by norm_num) (by norm_num) zero_lt_one 1 (Real.log 2)] with L hb hL hlength hlog
  intro i hi p hp V hV
  have hprime : Real.exp (L ^ (3/10 : ℝ)) < (p : ℝ) :=
    ((hb.2.2.2 i hi).2.2 p hp).2.1
  have hp0 : 0 < p := by
    exact_mod_cast (Real.exp_pos (L ^ (3/10 : ℝ))).trans hprime
  have hlen : ((2 * Nat.ceil (L ^ (13/25 : ℝ)) + 1 : ℕ) : ℝ) ≤ L := by
    have ht := hlength (2 * (Nat.ceil (L ^ (13/25 : ℝ)) : ℝ) + 1) le_rfl
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Real.rpow_one] using ht
  have hexp : 2 * L ≤ Real.exp (L ^ (3/10 : ℝ)) := by
    calc
      2 * L = Real.exp (Real.log L + Real.log 2) := by
        rw [Real.exp_add, Real.exp_log hL, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by
        simpa only [Real.rpow_zero, mul_one, one_mul] using hlog)
  have hsize : 2 * (2 * Nat.ceil (L ^ (13/25 : ℝ)) + 1) ≤ p := by
    have h := (mul_le_mul_of_nonneg_left hlen (by norm_num : (0 : ℝ) ≤ 2)).trans
      (hexp.trans hprime.le)
    exact_mod_cast h
  exact physical_root_reciprocal_atom_bound p hvmin hV
    (physical_endpoint_baseline_bounds hq0 hq1 _ p hp0 hsize).1 hprime.le

end Bounty


-- Source module: RootDyadicLogLower

/- An exponential lower bound for a source dyad supplies the logarithmic
interval length needed by the finite moment replacement theorem. -/

open Filter
namespace Bounty

theorem eventually_root_dyadic_log_lower {b : ℝ} (hb : 0 < b) :
    ∀ᶠ L : ℝ in atTop, ∀ Z : ℝ, Real.exp (b * L) ≤ Z →
      ∀ i : ℕ, Z / 8 < (2 : ℝ) ^ i →
        (b / 2) * L ≤ Real.log ((2 : ℕ) ^ i : ℝ) := by
  filter_upwards [eventually_ge_atTop (2 * Real.log 8 / b)] with L hL
  intro Z hZ i hi
  have hbudget : Real.log 8 ≤ (b / 2) * L := by
    have hh := (div_le_iff₀ hb).mp hL
    nlinarith
  have hpow : 0 < (2 : ℝ) ^ i := by positivity
  have hexp : Real.exp (b * L) ≤ 8 * (2 : ℝ) ^ i := by linarith
  have hlog := Real.log_le_log (Real.exp_pos _) hexp
  rw [Real.log_exp, Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (ne_of_gt hpow)] at hlog
  push_cast
  linarith

end Bounty


-- Source module: ActualRootDyadicLog

/- Every source dyad in the original harmonic windows is long enough
for the actual finite root replacement, with one uniform threshold. -/

open Finset Filter
open scoped Classical
namespace Bounty

theorem eventually_actual_root_dyadic_log {b K : ℝ}
    (hb : 0 < b) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop, ∀ (G : Type) [Fintype G] [DecidableEq G]
      (P : G → Finset ℕ) (J ell : ℕ) (probes : G → Finset (Fin J))
      (r t : Finset G), (∀ g p, p ∈ P g → p.Prime) →
      ∀ U W : ℝ, Real.exp (b*L) ≤ U → U ≤ Real.exp L →
        Real.exp (b*L) ≤ W → W ≤ Real.exp L →
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L K : ℤ))
        (typeIIAdmissibleDeterminantBound L K : ℤ),
      ∀ j ∈ range (typeIISmoothDyadicCount L),
      ∀ i ∈ (physicalSignedHarmonicPositions (ell := ell) P probes r t
        (typeIISmoothDyadicScale U W (U*L^(-K)) j) k).image (fun n => n.natAbs.log2),
      (b/2)*L ≤ Real.log ((2 : ℕ)^i : ℝ) := by
  filter_upwards [eventually_root_dyadic_log_lower hb,
    eventually_typeII_harmonic_scale_lower hb hK,
    eventually_typeII_original_harmonic_shift_small hb hK] with L hlog hscale hshift
  intro G inst inst' P J ell probes r t hprime U W hUlo hUhi hWlo hWhi k hk j hj i hi
  have hZ := hscale U W hUlo hWlo j
  have hZlo : Real.exp (b*L) ≤ typeIISmoothDyadicScale U W (U*L^(-K)) j := by
    linarith [Real.exp_pos (b*L)]
  have hZpos : 0 < typeIISmoothDyadicScale U W (U*L^(-K)) j :=
    (Real.exp_pos _).trans_le hZlo
  exact hlog _ hZlo i (physical_signed_harmonic_dyadic_lower probes r t hprime hZpos k
    (hshift U W hUlo hUhi hWlo hWhi k hk j hj) hi)

end Bounty


-- Source module: CandidateSignedDyadicReplacement

/- Finite replacement for the literal alternating adjoint/original moment
on every dyad occurring in the original harmonic windows. -/

open Finset Filter
open scoped Classical
namespace Bounty

theorem eventually_candidate_signed_dyadic_replacement
    {scale b Kpow E B : ℝ} (hscale : 0 < scale) (hb : 0 < b)
    (hKpow : 0 ≤ Kpow) (hE : 0 ≤ E) (hB : 0 ≤ B) (J ell : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (S : Finset ℕ), S ⊆ candidatePIndices scale L →
      let P := fun g : S => candidatePBand (scale * L) g.val
      let V := fun g : S => ∑ p ∈ P g, 1 / (p : ℝ)
      ∀ [∀ p : PhysicalPrime P, NeZero p.2.val]
        (probes : S → Finset (Fin J)) (r t : Finset S),
      ∀ U W : ℝ, Real.exp (b*L) ≤ U → U ≤ Real.exp L →
        Real.exp (b*L) ≤ W → W ≤ Real.exp L →
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L Kpow : ℤ))
        (typeIIAdmissibleDeterminantBound L Kpow : ℤ),
      ∀ j ∈ range (typeIISmoothDyadicCount L),
      ∀ i ∈ (physicalSignedHarmonicPositions (ell := ell) P probes r t
        (typeIISmoothDyadicScale U W (U*L^(-Kpow)) j) k).image (fun n => n.natAbs.log2),
      ∀ (I : Type) (patterns : Finset I) (cuts : I → S → Finset (Fin J))
        (bounds : I → ℝ) (ζ : I → ℝ)
        (K : ∀ i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
          PhysicalAuxLabels P (cuts i) → ℂ),
      (∀ i ∈ patterns, 0 ≤ bounds i) → (∑ i ∈ patterns, bounds i) ≤ L ^ B →
      (∀ i, i ∈ patterns → ∀ x y aux, ‖K i x y aux‖ ≤ bounds i) →
      let ζt := fun e a => if e % 2 = 0 then -ζ a else ζ a
      let kt := fun e (_ : I) => if e % 2 = 0 then -k else k
      let Kt := fun e a x y aux => if e % 2 = 0 then (starRingEnd ℂ) (K a y x aux) else K a x y aux
      let D := max 1 (physicalOperatorStepBound P J ell patterns cuts (fun _ => k))
      ‖physicalRootMoment V patterns cuts (1/2) ζt kt Kt (physicalDyadicStarts i)
          (2 * Nat.ceil (L ^ (13/25 : ℝ)) - 1) D -
        physicalRootResidueModel V patterns cuts (1/2) ζt kt Kt
          (2 * Nat.ceil (L ^ (13/25 : ℝ)) - 1)‖ ≤
        Real.exp (-E * (2 * Nat.ceil (L ^ (13/25 : ℝ))) * Real.log L) := by
  filter_upwards [eventually_candidate_root_replacement hscale (by positivity : 0 < b/2) hE hB J ell,
    eventually_actual_root_dyadic_log hb hKpow] with L hreplace hlog
  intro S hS P V inst probes r t U W hUlo hUhi hWlo hWhi k hk j hj i hi
    I patterns cuts bounds ζ K hbounds hsum hK ζt kt Kt D
  have hprime (g : S) (p : ℕ) (hp : p ∈ P g) : p.Prime :=
    ((mem_dyadicPrimeBand_iff (scale*L) (3/2) (9/5) g.val p).mp hp).1
  have hiLog := hlog S P J ell probes r t hprime U W hUlo hUhi hWlo hWhi k hk j hj i hi
  have hKt : ∀ e a, a ∈ patterns → ∀ x y aux, ‖Kt e a x y aux‖ ≤ bounds a := by
    intro e a ha x y aux
    dsimp only [Kt]
    split_ifs
    · simpa only [starRingEnd_apply, norm_star] using hK a ha y x aux
    · exact hK a ha x y aux
  have hcut : ∀ e < 2 * Nat.ceil (L ^ (13/25 : ℝ)),
      physicalOperatorStepBound P J ell patterns cuts (kt e) ≤ D := by
    intro e _
    dsimp only [kt, D]
    by_cases he : e % 2 = 0
    · simp only [he, if_true, physical_operator_step_bound_neg]
      exact le_max_right _ _
    · simp only [he, if_false]
      exact le_max_right _ _
  have hstarts : Ico ((2 : ℤ)^i) ((2 : ℤ)^i + ((2^i : ℕ) : ℤ)) = physicalDyadicStarts i := by
    simp only [physicalDyadicStarts, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
    congr 1
    ring
  have hiLogNat : (b/2)*L ≤ Real.log ((2^i : ℕ) : ℝ) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hiLog
  have h := hreplace S hS I patterns cuts bounds ζt kt Kt D (2^i) ((2 : ℤ)^i)
    hbounds hsum hKt hcut (by positivity) hiLogNat
  simpa only [hstarts] using h

end Bounty


-- Source module: RootMomentBudget

/- Reserve one power of the large parameter for the sum of the finite,
cap, and working-scalar errors in the final central moment. -/

namespace Bounty

theorem root_three_errors_power_budget {L F : ℝ} (hL : 3 ≤ L)
    {N : ℕ} (hN : 0 < N) :
    3 * L ^ (-(F + 1) * (N : ℝ)) ≤ (L ^ (-F)) ^ N := by
  have hL0 : 0 < L := by linarith
  have hLN : (3 : ℝ) ≤ L ^ N :=
    hL.trans (le_self_pow₀ (by linarith : 1 ≤ L) (Nat.ne_zero_of_lt hN))
  have hproduct : L ^ (-(F + 1) * (N : ℝ)) * L ^ (N : ℝ) = (L ^ (-F)) ^ N := by
    rw [← Real.rpow_add hL0, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    congr 1
    ring
  calc
    _ ≤ L ^ N * L ^ (-(F + 1) * (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hLN (Real.rpow_nonneg hL0.le _)
    _ = (L ^ (-F)) ^ N := by rw [mul_comm, ← Real.rpow_natCast, hproduct]

theorem root_central_moment_of_three_errors {L F : ℝ} (hL : 3 ≤ L)
    {N : ℕ} (hN : 0 < N) (moment model : ℂ)
    (hfinite : ‖moment - model‖ ≤ L ^ (-(F + 1) * (N : ℝ)))
    (hmodel : ‖model‖ ≤ 2 * L ^ (-(F + 1) * (N : ℝ))) :
    moment.re ≤ (L ^ (-F)) ^ N := by
  have hnorm : ‖moment‖ ≤ 3 * L ^ (-(F + 1) * (N : ℝ)) := by
    calc
      ‖moment‖ ≤ ‖moment - model‖ + ‖model‖ := norm_le_norm_sub_add _ _
      _ ≤ L ^ (-(F + 1) * (N : ℝ)) + 2 * L ^ (-(F + 1) * (N : ℝ)) :=
        add_le_add hfinite hmodel
      _ = _ := by ring
  exact (Complex.re_le_norm moment).trans (hnorm.trans (root_three_errors_power_budget hL hN))

theorem root_finite_error_as_power {L F : ℝ} (hL : 0 < L) (N : ℕ) :
    Real.exp (-F * (N : ℝ) * Real.log L) = L ^ (-F * (N : ℝ)) := by
  rw [Real.rpow_def_of_pos hL]
  congr 1
  ring

end Bounty


-- Source module: CandidateSignedCentralMoment

/- Only the actual residue-model estimate remains after finite replacement
on the original signed dyadic moments. One reserved power absorbs all three errors. -/

open Finset Filter
open scoped Classical
namespace Bounty

theorem eventually_candidate_signed_central_moment
    {scale b Kpow E B : ℝ} (hscale : 0 < scale) (hb : 0 < b)
    (hKpow : 0 ≤ Kpow) (hE : 0 ≤ E) (hB : 0 ≤ B) (J ell : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (S : Finset ℕ), S ⊆ candidatePIndices scale L →
      let P := fun g : S => candidatePBand (scale * L) g.val
      let V := fun g : S => ∑ p ∈ P g, 1 / (p : ℝ)
      ∀ [∀ p : PhysicalPrime P, NeZero p.2.val]
        (probes : S → Finset (Fin J)) (r t : Finset S),
      ∀ U W : ℝ, Real.exp (b*L) ≤ U → U ≤ Real.exp L →
        Real.exp (b*L) ≤ W → W ≤ Real.exp L →
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L Kpow : ℤ))
        (typeIIAdmissibleDeterminantBound L Kpow : ℤ),
      ∀ j ∈ range (typeIISmoothDyadicCount L),
      ∀ i ∈ (physicalSignedHarmonicPositions (ell := ell) P probes r t
        (typeIISmoothDyadicScale U W (U*L^(-Kpow)) j) k).image (fun n => n.natAbs.log2),
      ∀ (I : Type) (patterns : Finset I) (cuts : I → S → Finset (Fin J))
        (bounds : I → ℝ) (ζ : I → ℝ)
        (K : ∀ i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
          PhysicalAuxLabels P (cuts i) → ℂ),
      (∀ i ∈ patterns, 0 ≤ bounds i) → (∑ i ∈ patterns, bounds i) ≤ L ^ B →
      (∀ i, i ∈ patterns → ∀ x y aux, ‖K i x y aux‖ ≤ bounds i) →
      let ζt := fun e a => if e % 2 = 0 then -ζ a else ζ a
      let kt := fun e (_ : I) => if e % 2 = 0 then -k else k
      let Kt := fun e a x y aux => if e % 2 = 0 then (starRingEnd ℂ) (K a y x aux) else K a x y aux
      let D := max 1 (physicalOperatorStepBound P J ell patterns cuts (fun _ => k))
      let moment := physicalRootMoment V patterns cuts (1/2) ζt kt Kt (physicalDyadicStarts i)
        (2 * Nat.ceil (L ^ (13/25 : ℝ)) - 1) D
      let model := physicalRootResidueModel V patterns cuts (1/2) ζt kt Kt
        (2 * Nat.ceil (L ^ (13/25 : ℝ)) - 1)
      ‖model‖ ≤ 2 * L ^ (-(E + 1) * (2 * Nat.ceil (L ^ (13/25 : ℝ)) : ℕ)) →
      moment.re ≤ (L ^ (-E)) ^ (2 * Nat.ceil (L ^ (13/25 : ℝ))) := by
  filter_upwards [eventually_candidate_signed_dyadic_replacement hscale hb hKpow
    (show 0 ≤ E + 1 by linarith) hB J ell, eventually_ge_atTop (3 : ℝ)] with L hreplace hL
  intro S hS P V inst probes r t U W hUlo hUhi hWlo hWhi k hk j hj i hi
    I patterns cuts bounds ζ K hbounds hsum hK ζt kt Kt D moment model hmodel
  have hL0 : 0 < L := by linarith
  have hN : 0 < 2 * Nat.ceil (L ^ (13/25 : ℝ)) :=
    Nat.mul_pos (by decide) (Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hL0 _))
  have hfinite := hreplace S hS probes r t U W hUlo hUhi hWlo hWhi k hk j hj i hi
    I patterns cuts bounds ζ K hbounds hsum hK
  have heq : Real.exp (-(E + 1) * (2 * Nat.ceil (L ^ (13/25 : ℝ))) * Real.log L) =
      L ^ (-(E + 1) * (2 * Nat.ceil (L ^ (13/25 : ℝ)) : ℕ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      root_finite_error_as_power (F := E + 1) hL0 (2 * Nat.ceil (L ^ (13/25 : ℝ)))
  rw [heq] at hfinite
  exact root_central_moment_of_three_errors hL hN moment model hfinite hmodel

end Bounty


-- Source module: PhysicalRootPrimeEnvelope

/- The exact original prime kernel has a polynomially summable pattern
majorant, uniformly over all candidate probes and all auxiliary labels. -/

open Finset Filter
open scoped Classical
namespace Bounty

theorem physical_root_prime_kernel_norm_le
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ) (probes : G → Finset (Fin J))
    (r t : Finset G) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ) (hξ : 0 < ξ)
    (i : RepeatedBigPrimePatternIndex (ell := ell) probes r t)
    (L R : PhysicalMarkLists P J ell)
    (aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t i)) :
    ‖physicalRootPrimeKernel P V probes r t hrt Q h ξ i L R aux‖ ≤
      repeatedBigPrimePatternBound probes r t Q ξ i := by
  rw [physicalRootPrimeKernel, norm_mul, repeated_big_prime_pattern_weight_norm, one_mul]
  exact repeated_big_prime_pattern_kernel_norm_le P V probes r t hrt Q h ξ hξ i _ _ aux

theorem repeated_big_prime_pattern_bound_sum_le_envelope
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (probes : G → Finset (Fin J)) (r t : Finset G) (hrt : Disjoint r t)
    (Q : ℕ) (ξ : ℝ) :
    (∑ i : RepeatedBigPrimePatternIndex (ell := ell) probes r t,
      repeatedBigPrimePatternBound probes r t Q ξ i) ≤
      repeatedBigFamilyEnvelope (Fintype.card G) J Q ξ := by
  apply (repeated_big_prime_pattern_bound_sum_le probes r t
    (fun g => (card_le_univ (probes g)).trans_eq (Fintype.card_fin J)) Q ξ).trans
  unfold repeatedBigFamilyEnvelope
  apply add_le_add (le_refl _)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
  apply Nat.mul_le_mul_left
  rw [← card_union_of_disjoint hrt]
  exact card_le_univ _

theorem exists_candidate_root_pattern_power {scale q x : ℝ}
    (hscale : 0 < scale) (hq : 0 ≤ q) (hx : 0 ≤ x) (J ell : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ L : ℝ in atTop, ∀ (S : Finset ℕ),
      S ⊆ candidatePIndices scale L → ∀ (probes : S → Finset (Fin J))
      (r t : Finset S), Disjoint r t → ∀ (Q : ℕ) (ξ : ℝ),
      (Q : ℝ) ≤ L ^ q → L ^ (-x) ≤ ξ →
      (∑ i : RepeatedBigPrimePatternIndex (ell := ell) probes r t,
        repeatedBigPrimePatternBound probes r t Q ξ i) ≤ L ^ B := by
  obtain ⟨v, V, _, _, hpools⟩ := exists_candidate_P_pool_bounds hscale
  let a : ℝ := 2 / (5 * Real.log 2)
  let d : ℝ := (J : ℝ) * a * Real.log 2 + 4 * q + 2 * x
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  refine ⟨d + 1, by linarith, ?_⟩
  filter_upwards [hpools, eventually_ge_atTop (2 : ℝ)] with L hpools hL
  intro S hS probes r t hrt Q ξ hQ hξ
  have hL0 : 0 < L := by linarith
  have hcard : (Fintype.card S : ℝ) ≤ a * Real.log L := by
    simpa only [Fintype.card_coe] using
      (Nat.cast_le.mpr (card_le_card hS)).trans hpools.2.2.2.1
  calc
    _ ≤ repeatedBigFamilyEnvelope (Fintype.card S) J Q ξ :=
      repeated_big_prime_pattern_bound_sum_le_envelope probes r t hrt Q ξ
    _ ≤ 2 * L ^ d := repeated_big_family_envelope_le _ J Q (by linarith) ha hq hx hcard hQ hξ
    _ ≤ L * L ^ d := mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hL0.le _)
    _ = L ^ (d + 1) := by rw [mul_comm, ← Real.rpow_add_one hL0.ne']

end Bounty


-- Source module: ActualPrimeCentralMoment

/- The actual prime kernel discharges every finite replacement input.
The remaining premise is the residue-model estimate for the selected data. -/

open Finset Filter
open scoped Classical
namespace Bounty

theorem eventually_actual_prime_central_moment
    {scale b Kpow q x E : ℝ} (hscale : 0 < scale) (hb : 0 < b)
    (hKpow : 0 ≤ Kpow) (hq : 0 ≤ q) (hx : 0 ≤ x) (hE : 0 ≤ E) (J ell : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (S : Finset ℕ), S ⊆ candidatePIndices scale L →
      let P := fun g : S => candidatePBand (scale * L) g.val
      let V := fun g : S => ∑ p ∈ P g, 1 / (p : ℝ)
      ∀ [∀ p : PhysicalPrime P, NeZero p.2.val]
        (probes : S → Finset (Fin J)) (r t : Finset S) (hrt : Disjoint r t)
        (Q : ℕ) (h ξ ζ : ℝ), (Q : ℝ) ≤ L ^ q → L ^ (-x) ≤ ξ →
      ∀ U W : ℝ, Real.exp (b*L) ≤ U → U ≤ Real.exp L →
        Real.exp (b*L) ≤ W → W ≤ Real.exp L →
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L Kpow : ℤ))
        (typeIIAdmissibleDeterminantBound L Kpow : ℤ),
      ∀ j ∈ range (typeIISmoothDyadicCount L),
      ∀ i ∈ (physicalSignedHarmonicPositions (ell := ell) P probes r t
        (typeIISmoothDyadicScale U W (U*L^(-Kpow)) j) k).image (fun n => n.natAbs.log2),
      let patterns := (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
      let cuts := repeatedBigPrimePatternCut (ell := ell) probes r t
      let ζt := fun e (_ : RepeatedBigPrimePatternIndex (ell := ell) probes r t) =>
        if e % 2 = 0 then -ζ else ζ
      let kt := fun e (_ : RepeatedBigPrimePatternIndex (ell := ell) probes r t) =>
        if e % 2 = 0 then -k else k
      let Kt := fun e a u v aux => if e % 2 = 0 then
        (starRingEnd ℂ) (physicalRootPrimeKernel P V probes r t hrt Q h ξ a v u aux)
        else physicalRootPrimeKernel P V probes r t hrt Q h ξ a u v aux
      let D := max 1 (physicalOperatorStepBound P J ell patterns cuts (fun _ => k))
      let moment := physicalRootMoment V patterns cuts (1/2) ζt kt Kt (physicalDyadicStarts i)
        (2 * Nat.ceil (L ^ (13/25 : ℝ)) - 1) D
      let model := physicalRootResidueModel V patterns cuts (1/2) ζt kt Kt
        (2 * Nat.ceil (L ^ (13/25 : ℝ)) - 1)
      ‖model‖ ≤ 2 * L ^ (-(E + 1) * (2 * Nat.ceil (L ^ (13/25 : ℝ)) : ℕ)) →
      moment.re ≤ (L ^ (-E)) ^ (2 * Nat.ceil (L ^ (13/25 : ℝ))) := by
  obtain ⟨B, hB, hbounds⟩ := exists_candidate_root_pattern_power hscale hq hx J ell
  filter_upwards [hbounds, eventually_candidate_signed_central_moment hscale hb hKpow hE hB J ell,
    eventually_gt_atTop (0 : ℝ)] with L hbounds hcentral hL
  intro S hS P V inst probes r t hrt Q h ξ ζ hQ hξ U W hUlo hUhi hWlo hWhi k hk j hj i hi
    patterns cuts ζt kt Kt D moment model hmodel
  have hξpos := (Real.rpow_pos_of_pos hL (-x)).trans_le hξ
  exact hcentral S hS probes r t U W hUlo hUhi hWlo hWhi k hk j hj i hi
    (RepeatedBigPrimePatternIndex (ell := ell) probes r t) patterns cuts
    (repeatedBigPrimePatternBound probes r t Q ξ) (fun _ => ζ)
    (physicalRootPrimeKernel P V probes r t hrt Q h ξ)
    (fun a _ => repeated_big_prime_pattern_bound_nonneg probes r t Q ξ a)
    (hbounds S hS probes r t hrt Q ξ hQ hξ)
    (fun a _ u v aux => physical_root_prime_kernel_norm_le P V probes r t hrt Q h ξ hξpos a u v aux)
    hmodel

end Bounty


-- Source module: SelectedResiduePremise

/- The explicit remaining original residue-model estimate, with common data
chosen before the phase and determinant. -/

open Finset Filter
open scoped Classical
namespace Bounty

def CandidateSelectedResidueBounds (c : ℝ) : Prop :=
  ∀ E z K : ℝ, 0 ≤ E → 0 ≤ z → 0 ≤ K →
    ∃ (J : ℕ) (w x q : ℝ), 0 ≤ w ∧ 0 ≤ x ∧ 0 ≤ q ∧
    ∀ᶠ L : ℝ in atTop,
      let S := candidatePIndices c L
      let P := fun g : S => candidatePBand (c * L) g.val
      let V := fun g : S => ∑ p ∈ P g, 1 / (p : ℝ)
      ∃ (probes : S → Finset (Fin J)) (r t : Finset S) (hrt : Disjoint r t) (Q : ℕ),
        (∀ g ∈ r ∪ t, g.val ∈ candidateBigPIndices c L) ∧ (Q : ℝ) ≤ L ^ q ∧
        ∀ [∀ p : PhysicalPrime P, NeZero p.2.val],
        ∀ ζ : ℝ, |ζ| ≤ L ^ z →
        ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L K : ℤ))
          (typeIIAdmissibleDeterminantBound L K : ℤ), k ≠ 0 →
        let patterns := (univ : Finset (RepeatedBigPrimePatternIndex (ell := 1) probes r t))
        let cuts := repeatedBigPrimePatternCut (ell := 1) probes r t
        let ζt := fun e (_ : RepeatedBigPrimePatternIndex (ell := 1) probes r t) =>
          if e % 2 = 0 then -ζ else ζ
        let kt := fun e (_ : RepeatedBigPrimePatternIndex (ell := 1) probes r t) =>
          if e % 2 = 0 then -k else k
        let Kt := fun e a u v aux => if e % 2 = 0 then
          (starRingEnd ℂ) (physicalRootPrimeKernel P V probes r t hrt Q (L ^ (-w)) (L ^ (-x)) a v u aux)
          else physicalRootPrimeKernel P V probes r t hrt Q (L ^ (-w)) (L ^ (-x)) a u v aux
        ‖physicalRootResidueModel V patterns cuts (1/2) ζt kt Kt
          (2 * Nat.ceil (L ^ (13/25 : ℝ)) - 1)‖ ≤
          2 * L ^ (-(E + 1) * (2 * Nat.ceil (L ^ (13/25 : ℝ)) : ℕ))

end Bounty


-- Source module: SelectedCentralFrequency

/- Cancellation of the original endpoint frequency in the central Mellin range. -/

open Filter
namespace Bounty

theorem eventually_original_central_phase_bound (F η : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (ν : ℝ) (ζ : EuclideanSpace ℝ (Fin 3)) (u : ℝ),
      ‖ζ‖ ≤ L ^ F → ‖u‖ ≤ L ^ η →
      |-((2 * Real.pi * ν + 2 * Real.pi * ζ 2) + (-(2 * Real.pi * ν))) -
          2 * Real.pi * u| ≤ L ^ (max η F + 1) := by
  filter_upwards [eventually_original_endpoint_phase_bounds η F] with L hL
  intro ν ζ u hζ hu
  have he : -((2 * Real.pi * ν + 2 * Real.pi * ζ 2) + (-(2 * Real.pi * ν))) -
      2 * Real.pi * u = -(2 * Real.pi * u + 2 * Real.pi * ζ 2) := by ring
  rw [he, abs_neg]
  exact ((hL u ζ hu hζ).2 2).1

theorem central_moment_precision_mono {L E F : ℝ} (hL : 1 ≤ L) (hEF : F ≤ E) (n : ℕ) :
    (L ^ (-E)) ^ n ≤ (L ^ (-F)) ^ n := by
  exact pow_le_pow_left₀ (Real.rpow_nonneg (by linarith) _)
    (Real.rpow_le_rpow_of_exponent_le hL (neg_le_neg hEF)) n

end Bounty


-- Source module: SelectedMomentTransfer

/- An explicit uniform original residue-model bound implies the selected
central moment contract. -/

open Finset Filter MeasureTheory
open scoped Classical
namespace Bounty

theorem candidate_selected_central_moments_of_residue_bounds
    {c bWindow : ℝ} (hc : 0 < c) (hb : 0 < bWindow) (rQ : ℕ)
    (hmodel : CandidateSelectedResidueBounds c) :
    CandidateSelectedCentralMoments c bWindow rQ := by
  refine ⟨0, ?_⟩
  intro jStar _ Kdet hK D T F
  let E := max 0 D + 24
  let z := max 1 F + 1
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hz : 0 ≤ z := by dsimp [z]; linarith [le_max_left (1 : ℝ) F]
  obtain ⟨J, w, x, q, hw, hx, hq, hmodels⟩ := hmodel E z Kdet hE hz hK
  obtain ⟨v, V, _, _, hpools⟩ := exists_candidate_P_pool_bounds hc
  refine ⟨J, w, x, q, 1, hw, zero_lt_one, ?_⟩
  filter_upwards [hmodels, hpools, eventually_original_central_phase_bound F 1,
    eventually_actual_prime_central_moment hc hb hK hq hx hE J 1] with L hm hp hphase hactual
  intro hrQ hj take _ _ ν ζ _ hζ U W hUlo hUhi hWlo hWhi k hk hk0 j hjrange Z P mass
  let _ : ∀ p : PhysicalPrime P, NeZero p.2.val := fun p =>
    ⟨(((hp.2.2.2.2.2 p.1.val p.1.property).2.2 p.2.val p.2.property).1).ne_zero⟩
  obtain ⟨probes, r, t, hrt, Q, hbig, hQ, hbound⟩ := hm
  refine ⟨probes, r, t, hrt, hbig, Q, hQ, ?_⟩
  intro i hi
  filter_upwards [] with u
  intro hu
  let phase := -((2 * Real.pi * ν + 2 * Real.pi * ζ 2) + (-(2 * Real.pi * ν))) -
    2 * Real.pi * u
  have hphase' : |phase| ≤ L ^ z := hphase ν ζ u hζ hu
  have hmod := hbound phase hphase' k hk hk0
  have hmoment := hactual (candidatePIndices c L) (by intro i hi; exact hi) probes r t hrt Q
    (L ^ (-w)) (L ^ (-x)) phase hQ (le_refl _) U W hUlo hUhi hWlo hWhi k hk j hjrange i hi hmod
  have hprec : D + 1 + 23 ≤ E := by dsimp [E]; linarith [le_max_right (0 : ℝ) D]
  exact hmoment.trans (central_moment_precision_mono hp.1 hprec
    (2 * Nat.ceil (L ^ (13/25 : ℝ))))

end Bounty


namespace Bounty.WeakZeroFree

theorem target_of_selected_residue_bounds
    (hmodel : ∀ c : ℝ, 0 < c → CandidateSelectedResidueBounds c) :
    fcTypeOfName% "Erdos1057.erdos_1057" := by
  apply target_of_selected_central_moments
  intro c r hc _ _ bWindow hb
  exact candidate_selected_central_moments_of_residue_bounds hc hb r (hmodel c hc)

end Bounty.WeakZeroFree
