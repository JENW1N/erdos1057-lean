import ExpandedFrontier
import PinnedNonprincipal

/-! Sound migration of the candidate target to the actual 23/24 zero-free theorem. -/

/- Actual zero-free and prime-sum inputs at the weaker exponent. -/

namespace Bounty.WeakZeroFree

/-- The actual Mathlib L-function is nonzero in the weaker half-plane. -/
theorem actual_zero_free : PrimitiveZeroFreeRightOf (23 / 24) := by
  intro χ s hs
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  exact OAI.ApplicationAudit.nonprincipal_LFunction_ne_zero χ.character χ.nontrivial s hs

theorem primitive_twistedPsi_power_saving
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : OAI.Ostmann.PrimitiveComplexCharacter) (x : ℝ),
      2 ≤ x → ‖twistedPsi χ.character x‖ ≤
        C * x ^ ((95 : ℝ) / 96) * Real.log ((χ.modulus : ℝ) * x) :=
  Bounty.primitive_twistedPsi_power_saving_23_24 hZ

theorem actual_primitive_twistedPsi_power_saving :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : OAI.Ostmann.PrimitiveComplexCharacter) (x : ℝ),
      2 ≤ x → ‖twistedPsi χ.character x‖ ≤
        C * x ^ ((95 : ℝ) / 96) * Real.log ((χ.modulus : ℝ) * x) :=
  primitive_twistedPsi_power_saving actual_zero_free

end Bounty.WeakZeroFree


/- Quantitative prime-character companions for the 23/24 zero-free strip. -/

open Finset Filter
open scoped Topology BigOperators
namespace Bounty.WeakZeroFree

theorem prime_power_error_le_character_scale_linear {q x : ℝ}
    (hq : 1 ≤ q) (hx : 2 ≤ x) :
    2 * Real.sqrt x * Real.log x ≤
      2 * x ^ ((95 : ℝ) / 96) * Real.log (q * x) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlog : Real.log x ≤ Real.log (q * x) :=
    Real.log_le_log hx0 (by nlinarith)
  have hsqrt : Real.sqrt x ≤ x ^ ((95 : ℝ) / 96) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  gcongr

theorem primitive_twistedTheta_power_saving_linear_log
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : OAI.Ostmann.PrimitiveComplexCharacter) (x : ℝ),
      2 ≤ x → ‖twistedTheta χ.character x‖ ≤
        C * x ^ ((95 : ℝ) / 96) * Real.log ((χ.modulus : ℝ) * x) := by
  obtain ⟨C, hC, hbound⟩ := primitive_twistedPsi_power_saving hZ
  refine ⟨C + 2, by linarith, ?_⟩
  intro χ x hx
  have hq : (1 : ℝ) ≤ χ.modulus := by exact_mod_cast χ.positive
  have he := prime_power_error_le_character_scale_linear hq hx
  have ht := norm_twistedTheta_le χ.character (by linarith : 1 ≤ x) (hbound χ x hx)
  nlinarith

end Bounty.WeakZeroFree


/- Quantitative prime-character companions for the 23/24 zero-free strip. -/

open Finset Filter
open scoped Topology BigOperators
namespace Bounty.WeakZeroFree

/-- The logarithm in a character prefix estimate loses only a logarithmic ratio. -/
theorem reciprocal_character_shell_scale_le {q x C : ℝ}
    (hq : 1 ≤ q) (hx : 2 ≤ x) (hC : 0 ≤ C) :
    2 * (1 / (x * Real.log x)) *
      (C * (2 * x) ^ ((95 : ℝ) / 96) * Real.log (q * (2 * x))) ≤
    8 * C * x ^ (-(1 : ℝ) / 96) * (1 + Real.log q / Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hq0 : 0 < q := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq
  have hltwo : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hp : (2 : ℝ) ^ ((95 : ℝ) / 96) ≤ 2 :=
    Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have hxpow : x ^ ((95 : ℝ) / 96) = x * x ^ (-(1 : ℝ) / 96) := by
    calc
      _ = x ^ ((1 : ℝ) + (-(1 : ℝ) / 96)) := by norm_num
      _ = x ^ (1 : ℝ) * x ^ (-(1 : ℝ) / 96) := Real.rpow_add hx0 _ _
      _ = _ := by rw [Real.rpow_one]
  have hl : Real.log (q * (2 * x)) ≤ 2 * (Real.log x + Real.log q) := by
    rw [Real.log_mul hq0.ne' (by positivity), Real.log_mul (by norm_num) hx0.ne']
    linarith
  have hratio : Real.log (q * (2 * x)) / Real.log x ≤
      2 * (1 + Real.log q / Real.log x) := by
    apply (div_le_iff₀ hlx).mpr
    calc
      _ ≤ 2 * (Real.log x + Real.log q) := hl
      _ = _ := by field_simp
  have hr0 : 0 ≤ Real.log (q * (2 * x)) / Real.log x := by
    apply div_nonneg _ hlx.le
    exact Real.log_nonneg (by nlinarith)
  calc
    _ = (2 * C * (2 : ℝ) ^ ((95 : ℝ) / 96) * x ^ (-(1 : ℝ) / 96)) *
        (Real.log (q * (2 * x)) / Real.log x) := by
      rw [Real.mul_rpow (by norm_num) hx0.le, hxpow]
      field_simp
    _ ≤ (2 * C * 2 * x ^ (-(1 : ℝ) / 96)) *
        (2 * (1 + Real.log q / Real.log x)) := by
      have hfirst : 2 * C * (2 : ℝ) ^ ((95 : ℝ) / 96) * x ^ (-(1 : ℝ) / 96) ≤
          2 * C * 2 * x ^ (-(1 : ℝ) / 96) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity))
          (Real.rpow_nonneg hx0.le _)
      exact mul_le_mul hfirst hratio hr0 (by positivity)
    _ = _ := by ring

/-- Every subinterval ending within twice its lower endpoint has a true
reciprocal-prime power saving. The prefix hypothesis is the actual twisted theta sum. -/
theorem reciprocal_prime_partial_dyadic_shell_bound {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hq : 0 < q) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z : ℝ, 2 ≤ z → ‖twistedTheta χ z‖ ≤
      C * z ^ ((95 : ℝ) / 96) * Real.log ((q : ℝ) * z))
    {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) (hy : y ≤ 2 * x) :
    ‖∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
      (1 / (p : ℝ)) • χ (p : ZMod q)‖ ≤
      8 * C * x ^ (-(1 : ℝ) / 96) * (1 + Real.log q / Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  let B := C * (2 * x) ^ ((95 : ℝ) / 96) * Real.log ((q : ℝ) * (2 * x))
  have hB : 0 ≤ B := by
    have hl : 0 ≤ Real.log ((q : ℝ) * (2 * x)) := Real.log_nonneg (by nlinarith)
    positivity
  have hm : 2 ≤ ⌊x⌋₊ := by
    apply Nat.le_floor
    norm_num
    exact hx
  have hprefix : ∀ k ∈ Finset.Icc ⌊x⌋₊ ⌊y⌋₊, ‖twistedTheta χ k‖ ≤ B := by
    intro k hk
    obtain ⟨hmk, hkn⟩ := Finset.mem_Icc.mp hk
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hm.trans hmk
    have hkx : (k : ℝ) ≤ 2 * x := ((Nat.le_floor_iff hy0).mp hkn).trans hy
    have hl : 0 ≤ Real.log ((q : ℝ) * k) := Real.log_nonneg (by nlinarith)
    apply (hbound k hk2).trans
    dsimp [B]
    gcongr
  exact (norm_reciprocal_prime_sum_real_Ioc_le χ hx hB hprefix).trans
    (reciprocal_character_shell_scale_le hq1 hx hC)

end Bounty.WeakZeroFree


/- Quantitative prime-character companions for the 23/24 zero-free strip. -/

open Finset Filter
open scoped Topology BigOperators
namespace Bounty.WeakZeroFree

theorem reciprocal_character_profile_doubling {q x : ℝ} (hq : 1 ≤ q) (hx : 2 ≤ x) :
    (2 * x) ^ (-(1 : ℝ) / 96) * (1 + Real.log q / Real.log (2 * x)) ≤
      (2 : ℝ) ^ (-(1 : ℝ) / 96) *
        (x ^ (-(1 : ℝ) / 96) * (1 + Real.log q / Real.log x)) := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq
  have hlogs : Real.log x ≤ Real.log (2 * x) := Real.log_le_log hx0 (by linarith)
  have hratio : Real.log q / Real.log (2 * x) ≤ Real.log q / Real.log x :=
    div_le_div_of_nonneg_left hlq hlx hlogs
  rw [Real.mul_rpow (by norm_num) hx0.le]
  calc
    _ ≤ ((2 : ℝ) ^ (-(1 : ℝ) / 96) * x ^ (-(1 : ℝ) / 96)) *
        (1 + Real.log q / Real.log x) := by gcongr
    _ = _ := by ring

/-- The upper endpoint is unrestricted. The constant and decay depend only
on the theta prefix constant and the lower endpoint. -/
theorem reciprocal_prime_interval_bound_of_theta {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hq : 0 < q) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z : ℝ, 2 ≤ z → ‖twistedTheta χ z‖ ≤
      C * z ^ ((95 : ℝ) / 96) * Real.log ((q : ℝ) * z))
    {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    ‖∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
      (1 / (p : ℝ)) • χ (p : ZMod q)‖ ≤
      (8 * C / (1 - (2 : ℝ) ^ (-(1 : ℝ) / 96))) *
        x ^ (-(1 : ℝ) / 96) * (1 + Real.log q / Real.log x) := by
  classical
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have htail := norm_sum_real_Ioc_le_of_dyadic_bound
    (fun p : ℕ => if p.Prime then (1 / (p : ℝ)) • χ (p : ZMod q) else 0)
    (fun a : ℝ => a ^ (-(1 : ℝ) / 96) * (1 + Real.log q / Real.log a))
    (K := 8 * C) (r := (2 : ℝ) ^ (-(1 : ℝ) / 96)) (by positivity)
    (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
    (by
      intro a ha
      have hla : 0 ≤ Real.log a := Real.log_nonneg (by linarith)
      have ha0 : 0 ≤ a := by linarith
      positivity)
    (fun a ha => reciprocal_character_profile_doubling hq1 ha)
    (by
      intro a b ha hab hb
      rw [← Finset.sum_filter]
      simpa only [mul_assoc] using
        reciprocal_prime_partial_dyadic_shell_bound χ hq hC hbound ha hab hb)
    hx hxy
  rw [← Finset.sum_filter] at htail
  simpa only [mul_assoc] using htail

end Bounty.WeakZeroFree


/- Quantitative prime-character companions for the 23/24 zero-free strip. -/

open Finset Filter
open scoped Topology BigOperators
namespace Bounty.WeakZeroFree

theorem reciprocal_prime_induction_error_absorbed {q x : ℝ}
    (hq : 1 ≤ q) (hx : 2 ≤ x) :
    2 * Real.log q / x ≤
      4 * x ^ (-(1 : ℝ) / 96) * (1 + Real.log q / Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq
  have hr : 0 < x ^ (-(1 : ℝ) / 96) := Real.rpow_pos_of_pos hx0 _
  have hp : x ^ ((95 : ℝ) / 96) = x * x ^ (-(1 : ℝ) / 96) := by
    calc
      _ = x ^ ((1 : ℝ) + (-(1 : ℝ) / 96)) := by norm_num
      _ = _ := by rw [Real.rpow_add hx0, Real.rpow_one]
  have hlog : Real.log x ≤ 2 * (x * x ^ (-(1 : ℝ) / 96)) := by
    have hh := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 95 / 96)
    rw [hp] at hh
    have hxp : 0 ≤ x * x ^ (-(1 : ℝ) / 96) := by positivity
    linarith
  have hratio : Real.log x / x ≤ 2 * x ^ (-(1 : ℝ) / 96) :=
    (div_le_iff₀ hx0).mpr (by nlinarith [hlog])
  calc
    2 * Real.log q / x =
        (2 * (Real.log q / Real.log x)) * (Real.log x / x) := by
      field_simp
    _ ≤ (2 * (Real.log q / Real.log x)) * (2 * x ^ (-(1 : ℝ) / 96)) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ ≤ _ := by nlinarith

theorem norm_reciprocal_prime_sum_sub_primitive_le_decay {q : ℕ} (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {a : ℝ} (ha : 2 ≤ a) (haS : ∀ p ∈ S, a ≤ (p : ℝ)) :
    ‖(∑ p ∈ S, (1 / (p : ℝ)) • χ (p : ZMod q)) -
      ∑ p ∈ S, (1 / (p : ℝ)) •
        χ.primitiveCharacter (p : ZMod χ.conductor)‖ ≤
      4 * a ^ (-(1 : ℝ) / 96) * (1 + Real.log q / Real.log a) := by
  exact (norm_reciprocal_prime_sum_sub_primitive_le_two_log hq χ S hS
    (by linarith : 0 < a) haS).trans
      (reciprocal_prime_induction_error_absorbed (by exact_mod_cast hq) ha)

end Bounty.WeakZeroFree


/- Quantitative prime-character companions for the 23/24 zero-free strip. -/

open Finset Filter
open scoped Topology BigOperators
namespace Bounty.WeakZeroFree

/-- Uniform in the upper endpoint, the modulus, and the nonprincipal character.
The lower endpoint retains the full `1/96` power saving. -/
theorem reciprocal_prime_interval_bound_of_zero_free
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ), 0 < q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ x y : ℝ, 2 ≤ x → x ≤ y →
          ‖∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
            (1 / (p : ℝ)) • χ (p : ZMod q)‖ ≤
            C * x ^ (-(1 : ℝ) / 96) * (1 + Real.log q / Real.log x) := by
  classical
  obtain ⟨A, hA, htheta⟩ := primitive_twistedTheta_power_saving_linear_log hZ
  let D := 8 * A / (1 - (2 : ℝ) ^ (-(1 : ℝ) / 96))
  have hr : (2 : ℝ) ^ (-(1 : ℝ) / 96) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D + 4, by positivity, ?_⟩
  intro q hq χ hχ x y hx hxy
  let : NeZero q := ⟨hq.ne'⟩
  have hd : 0 < χ.conductor := Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hdq : χ.conductor ≤ q := Nat.le_of_dvd hq χ.conductor_dvd_level
  have hprimitive : χ.primitiveCharacter ≠ 1 := by
    intro he
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter, he, map_one]
  let ψ : OAI.Ostmann.PrimitiveComplexCharacter :=
    ⟨χ.conductor, hd, χ.primitiveCharacter, χ.primitiveCharacter_isPrimitive, hprimitive⟩
  have hp := reciprocal_prime_interval_bound_of_theta χ.primitiveCharacter hd hA.le
    (fun z hz => htheta ψ z hz) hx hxy
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hd0 : (0 : ℝ) < χ.conductor := by exact_mod_cast hd
  have hlogs : Real.log (χ.conductor : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_le_log hd0 (by exact_mod_cast hdq)
  have hp' : ‖∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
        (1 / (p : ℝ)) • χ.primitiveCharacter (p : ZMod χ.conductor)‖ ≤
      D * x ^ (-(1 : ℝ) / 96) * (1 + Real.log q / Real.log x) := by
    apply hp.trans
    change D * x ^ (-(1 : ℝ) / 96) * (1 + Real.log χ.conductor / Real.log x) ≤ _
    gcongr
  have he := norm_reciprocal_prime_sum_sub_primitive_le_decay hq χ
    ((Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime)
    (fun p hp => (Finset.mem_filter.mp hp).2) hx (fun p hp => by
      have hm := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
      exact ((Nat.floor_lt hx0.le).mp hm).le)
  calc
    _ = ‖((∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
          (1 / (p : ℝ)) • χ (p : ZMod q)) -
        (∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
          (1 / (p : ℝ)) • χ.primitiveCharacter (p : ZMod χ.conductor))) +
        (∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
          (1 / (p : ℝ)) • χ.primitiveCharacter (p : ZMod χ.conductor))‖ := by
      rw [sub_add_cancel]
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add he hp')
    _ = _ := by ring

end Bounty.WeakZeroFree


/- Quantitative prime-character companions for the 23/24 zero-free strip. -/

open Finset Filter
open scoped Topology BigOperators
namespace Bounty.WeakZeroFree

theorem reciprocal_character_profile_antitone {a x Q : ℝ}
    (ha : 2 ≤ a) (hax : a ≤ x) (hQ : 1 ≤ Q) :
    x ^ (-(1 : ℝ) / 96) * (1 + Real.log Q / Real.log x) ≤
      a ^ (-(1 : ℝ) / 96) * (1 + Real.log Q / Real.log a) := by
  have ha0 : 0 < a := by linarith
  have hla : 0 < Real.log a := Real.log_pos (by linarith)
  have hlog : Real.log a ≤ Real.log x := Real.log_le_log ha0 hax
  have hlx : 0 < Real.log x := hla.trans_le hlog
  have hQlog : 0 ≤ Real.log Q := Real.log_nonneg hQ
  apply mul_le_mul
  · exact Real.rpow_le_rpow_of_nonpos ha0 hax (by norm_num)
  · have h := div_le_div_of_nonneg_left hQlog hla hlog
    linarith
  · positivity
  · positivity

theorem reciprocal_prime_band_product_interval_bound
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ), 0 < q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ a b c U V : ℝ, 2 ≤ a → 0 ≤ b → 0 < c → 0 ≤ U → 0 ≤ V →
        ‖∑ p ∈ (primeBand a b).filter
            (fun p : ℕ => U < c * (p : ℝ) ∧ c * (p : ℝ) ≤ V),
          (1 / (p : ℝ)) • χ (p : ZMod q)‖ ≤
            C * a ^ (-(1 : ℝ) / 96) * (1 + Real.log q / Real.log a) := by
  obtain ⟨C, hC, hbound⟩ := reciprocal_prime_interval_bound_of_zero_free hZ
  refine ⟨C, hC, ?_⟩
  intro q hq χ hχ a b c U V ha hb hc hU hV
  rw [primeBand_product_interval (by linarith : 0 ≤ a) hb hc hU hV]
  let x := max a (U / c)
  let y := min b (V / c)
  have hax : a ≤ x := le_max_left _ _
  have hx : 2 ≤ x := ha.trans hax
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  by_cases hxy : x ≤ y
  · have h := hbound q hq χ hχ x y hx hxy
    change ‖∑ p ∈ primeBand x y, (1 / (p : ℝ)) • χ (p : ZMod q)‖ ≤ _ at h
    apply h.trans
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (reciprocal_character_profile_antitone ha hax hqR) hC.le
  · change ‖∑ p ∈ primeBand x y, (1 / (p : ℝ)) • χ (p : ZMod q)‖ ≤ _
    rw [primeBand_eq_empty_of_upper_le (le_of_not_ge hxy), Finset.sum_empty, norm_zero]
    have hlq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqR
    have hla : 0 < Real.log a := Real.log_pos (by linarith)
    positivity

end Bounty.WeakZeroFree


/- Quantitative prime-character companions for the 23/24 zero-free strip. -/

open Finset Filter
open scoped Topology BigOperators
namespace Bounty.WeakZeroFree

theorem ordinary_prime_band_product_interval_bound
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ), 0 < q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ a b c U V : ℝ, 2 ≤ a → 0 ≤ b → 0 < c → 0 ≤ U → 0 ≤ V →
        ‖∑ p ∈ (primeBand a b).filter
            (fun p : ℕ => U < c * (p : ℝ) ∧ c * (p : ℝ) ≤ V),
          χ (p : ZMod q)‖ ≤
            2 * b * C * a ^ (-(1 : ℝ) / 96) * (1 + Real.log q / Real.log a) := by
  obtain ⟨C, hC, hbound⟩ := reciprocal_prime_band_product_interval_bound hZ
  refine ⟨C, hC, ?_⟩
  intro q hq χ hχ a b c U V ha hb hc hU hV
  have haq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have haa : 0 < Real.log a := Real.log_pos (by linarith)
  have ha0 : 0 ≤ a := by linarith
  have hB : 0 ≤ C * a ^ (-(1 : ℝ) / 96) * (1 + Real.log q / Real.log a) := by
    positivity
  have h := ordinary_sum_le_of_reciprocal_prefix
    ((primeBand a b).filter (fun p : ℕ => U < c * (p : ℝ) ∧ c * (p : ℝ) ≤ V))
    (fun p => χ (p : ZMod q)) hb hB
    (fun p hp => ((mem_primeBand_iff ha0 hb p).mp (mem_filter.mp hp).1).1.pos)
    (fun p hp => ((mem_primeBand_iff ha0 hb p).mp (mem_filter.mp hp).1).2.2)
    (fun k => by
      rw [primeBand_product_filter_prefix ha0 hb]
      exact hbound q hq χ hχ a (min b (k : ℝ)) c U V ha
        (le_min hb (Nat.cast_nonneg k)) hc hU hV)
  convert h using 1
  ring

end Bounty.WeakZeroFree


/- Quantitative prime-character companions for the 23/24 zero-free strip. -/

open Finset Filter
open scoped Topology BigOperators
namespace Bounty.WeakZeroFree

theorem ordinary_prime_band_product_relative_bound
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ), 0 < q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ a b c U V : ℝ, 2 ≤ a → 0 ≤ b → 0 < c → 0 ≤ U → 0 ≤ V →
        ‖∑ p ∈ (primeBand a b).filter
            (fun p : ℕ => U < c * (p : ℝ) ∧ c * (p : ℝ) ≤ V), χ (p : ZMod q)‖ ≤
          2 * (V / c) * C * a ^ (-(1 : ℝ) / 96) *
            (1 + Real.log q / Real.log a) := by
  obtain ⟨C, hC, hbound⟩ := ordinary_prime_band_product_interval_bound hZ
  refine ⟨C, hC, ?_⟩
  intro q hq χ hχ a b c U V ha hb hc hU hV
  have hqlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have halog : 0 < Real.log a := Real.log_pos (by linarith)
  rw [primeBand_product_clip_upper (by linarith) hb hc hU hV]
  apply (hbound q hq χ hχ a (min b (V / c)) c U V ha
    (le_min hb (div_nonneg hV hc.le)) hc hU hV).trans
  gcongr
  exact min_le_right _ _

theorem ordinary_prime_band_product_coprime_relative_bound
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ), 0 < q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ a b c U V : ℝ, 2 ≤ a → 0 ≤ b → 0 < c → 0 ≤ U → 0 ≤ V →
      ∀ m : ℕ, m ≠ 0 →
        ‖∑ p ∈ ((primeBand a b).filter
            (fun p : ℕ => U < c * (p : ℝ) ∧ c * (p : ℝ) ≤ V)).filter
              (fun p => p.Coprime m), χ (p : ZMod q)‖ ≤
          (V / c) * (2 * C * a ^ (-(1 : ℝ) / 96) *
            (1 + Real.log q / Real.log a) + (m.primeFactors.card : ℝ) / a) := by
  obtain ⟨C, hC, hbound⟩ := ordinary_prime_band_product_relative_bound hZ
  refine ⟨C, hC, ?_⟩
  intro q hq χ hχ a b c U V ha hb hc hU hV m hm
  let S := (primeBand a b).filter
    (fun p : ℕ => U < c * (p : ℝ) ∧ c * (p : ℝ) ≤ V)
  have hS (p : ℕ) (hp : p ∈ S) : p.Prime ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b :=
    (mem_primeBand_iff (by linarith) hb p).mp (mem_filter.mp hp).1
  have hupper (p : ℕ) (hp : p ∈ S) : (p : ℝ) ≤ V / c := by
    apply (le_div_iff₀ hc).mpr
    simpa only [mul_comm] using (mem_filter.mp hp).2.2
  have herr := prime_sum_filter_coprime_relative_error S (fun p hp => (hS p hp).1)
    (fun p => χ (p : ZMod q)) (fun p _ => χ.norm_le_one _)
    (by linarith : 0 < a) (div_nonneg hV hc.le)
    (fun p hp => (hS p hp).2.1.le) hupper hm
  apply herr.trans
  apply le_trans (add_le_add (hbound q hq χ hχ a b c U V ha hb hc hU hV) le_rfl)
  exact le_of_eq (by ring)

end Bounty.WeakZeroFree


/- Quantitative prime-character companions for the 23/24 zero-free strip. -/

open Finset Filter
open scoped Topology BigOperators
namespace Bounty.WeakZeroFree

theorem prime_coprime_relative_profile_bound {c L C : ℝ}
    (hc : 0 < c) (hL : 0 < L) (hC : 0 ≤ C)
    {f m : ℕ} (hf : 0 < f) (hfL : (f : ℝ) ≤ Real.exp L)
    (hm : m ≠ 0) (hmL : (m : ℝ) ≤ Real.exp L) :
    2 * C * (Real.exp (c * L)) ^ (-(1 : ℝ) / 96) *
        (1 + Real.log (f : ℝ) / Real.log (Real.exp (c * L))) +
          (m.primeFactors.card : ℝ) / Real.exp (c * L) ≤
      (2 * C * (1 + 1 / c)) * Real.exp (-(c / 96) * L) +
        (1 / Real.log 2) * L * Real.exp (-c * L) := by
  have hf0 : (0 : ℝ) < f := by exact_mod_cast hf
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hflog : Real.log (f : ℝ) ≤ L := by
    simpa only [Real.log_exp] using Real.log_le_log hf0 hfL
  have hmlog : Real.log (m : ℝ) ≤ L := by
    simpa only [Real.log_exp] using Real.log_le_log hm0 hmL
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcard : (m.primeFactors.card : ℝ) ≤ L / Real.log 2 :=
    (primeFactors_card_le_log_div_log_two (Nat.pos_of_ne_zero hm)).trans
      (div_le_div_of_nonneg_right hmlog hlog2.le)
  have hquot : Real.log (f : ℝ) / (c * L) ≤ 1 / c := by
    apply (div_le_iff₀ (mul_pos hc hL)).mpr
    calc
      Real.log (f : ℝ) ≤ L := hflog
      _ = (1 / c) * (c * L) := by field_simp
  rw [Real.log_exp, ← Real.exp_mul]
  have hexp : c * L * (-(1 : ℝ) / 96) = -(c / 96) * L := by ring
  rw [hexp]
  calc
    _ ≤ 2 * C * Real.exp (-(c / 96) * L) * (1 + 1 / c) +
        (L / Real.log 2) / Real.exp (c * L) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hquot) (by positivity)
      · exact div_le_div_of_nonneg_right hcard (Real.exp_nonneg _)
    _ = _ := by simp only [neg_mul, Real.exp_neg]; ring

theorem eventually_prime_band_coprime_relative_power_bound
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c : ℝ} (hc : 0 < c) (B : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (f : ℕ), 0 < f → (f : ℝ) ≤ Real.exp L →
      ∀ χ : DirichletCharacter ℂ f, χ ≠ 1 →
      ∀ b t U V : ℝ, 0 ≤ b → 0 < t → 0 ≤ U → 0 ≤ V →
      ∀ m : ℕ, m ≠ 0 → (m : ℝ) ≤ Real.exp L →
        ‖∑ p ∈ ((primeBand (Real.exp (c * L)) b).filter
          (fun p : ℕ => U < t * (p : ℝ) ∧ t * (p : ℝ) ≤ V)).filter
            (fun p => p.Coprime m), χ (p : ZMod f)‖ ≤
          (V / t) * L ^ (-B) := by
  obtain ⟨C, hC, hbound⟩ := ordinary_prime_band_product_coprime_relative_bound hZ
  have hlarge : ∀ᶠ L : ℝ in atTop, (2 : ℝ) ≤ Real.exp (c * L) :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hc)).eventually_ge_atTop 2
  filter_upwards [eventually_linear_exponential_profile_le_rpow
    (div_pos hc (by norm_num : (0 : ℝ) < 96)) hc
    (2 * C * (1 + 1 / c)) (1 / Real.log 2) B,
    hlarge, eventually_gt_atTop (0 : ℝ)] with L hdecay hlarge hL
  intro f hf hfL χ hχ b t U V hb ht hU hV m hm hmL
  apply (hbound f hf χ hχ (Real.exp (c * L)) b t U V hlarge hb ht hU hV m hm).trans
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hV ht.le)
  exact (prime_coprime_relative_profile_bound hc hL hC.le hf hfL hm hmL).trans hdecay

end Bounty.WeakZeroFree


/- Quantitative prime-character companions for the 23/24 zero-free strip. -/

open Finset Filter
open scoped Topology BigOperators
namespace Bounty.WeakZeroFree

theorem eventually_prime_profile_exponential {c : ℝ} (hc : 0 < c) (C D : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      C * Real.exp (-(c / 96) * L) + D * L * Real.exp (-c * L) ≤
        Real.exp (-(c / 192) * L) := by
  have hsmall : 0 < c / 192 := div_pos hc (by norm_num)
  have hlarge : 0 < 191 * c / 192 := by positivity
  filter_upwards [eventually_linear_exponential_profile_le_rpow hsmall hlarge C D 0] with L hL
  simp only [neg_zero, Real.rpow_zero] at hL
  have hx : Real.exp (-(c / 192) * L) * Real.exp (-(c / 192) * L) =
      Real.exp (-(c / 96) * L) := by rw [← Real.exp_add]; congr 1; ring
  have hy : Real.exp (-(191 * c / 192) * L) * Real.exp (-(c / 192) * L) =
      Real.exp (-c * L) := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ = (C * Real.exp (-(c / 192) * L) +
        D * L * Real.exp (-(191 * c / 192) * L)) * Real.exp (-(c / 192) * L) := by
      rw [add_mul, mul_assoc C, mul_assoc (D * L), hx, hy]
    _ ≤ 1 * Real.exp (-(c / 192) * L) :=
      mul_le_mul_of_nonneg_right hL (Real.exp_nonneg _)
    _ = _ := one_mul _

theorem eventually_prime_band_coprime_relative_exponential_bound
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (f : ℕ), 0 < f → (f : ℝ) ≤ Real.exp L →
      ∀ χ : DirichletCharacter ℂ f, χ ≠ 1 →
      ∀ b t U V : ℝ, 0 ≤ b → 0 < t → 0 ≤ U → 0 ≤ V →
      ∀ m : ℕ, m ≠ 0 → (m : ℝ) ≤ Real.exp L →
        ‖∑ p ∈ ((primeBand (Real.exp (c * L)) b).filter
          (fun p : ℕ => U < t * (p : ℝ) ∧ t * (p : ℝ) ≤ V)).filter
            (fun p => p.Coprime m), χ (p : ZMod f)‖ ≤
          (V / t) * Real.exp (-(c / 192) * L) := by
  obtain ⟨C, hC, hbound⟩ := ordinary_prime_band_product_coprime_relative_bound hZ
  have hlarge : ∀ᶠ L : ℝ in atTop, (2 : ℝ) ≤ Real.exp (c * L) :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hc)).eventually_ge_atTop 2
  filter_upwards [eventually_prime_profile_exponential hc
    (2 * C * (1 + 1 / c)) (1 / Real.log 2),
    hlarge, eventually_gt_atTop (0 : ℝ)] with L hdecay hlarge hL
  intro f hf hfL χ hχ b t U V hb ht hU hV m hm hmL
  apply (hbound f hf χ hχ (Real.exp (c * L)) b t U V hlarge hb ht hU hV m hm).trans
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hV ht.le)
  exact (prime_coprime_relative_profile_bound hc hL hC.le hf hfL hm hmL).trans hdecay

end Bounty.WeakZeroFree

open Finset Filter
open scoped Topology BigOperators
namespace Bounty.WeakZeroFree

theorem eventually_wide_ambient_prime_cancellation
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ) :
    ∀ᶠ y : ℝ in atTop, ∀ L : ℕ, 0 < L →
      Real.log (L : ℝ) ≤ y ^ δ * Real.log (5 * y) →
      ∀ χ : DirichletCharacter ℂ L, χ ≠ 1 →
      ‖∑ p ∈ primeBand (y / 4) (5 * y), χ (p : ZMod L)‖ ≤
        y ^ ((95 : ℝ) / 96 + 2 * δ + σ) := by
  obtain ⟨C, hC, hbound⟩ := ordinary_prime_band_product_interval_bound hZ
  let A : ℝ := 20 * C / (4 : ℝ) ^ (-(1 : ℝ) / 96)
  filter_upwards [eventually_log_natLog_le_rpow δ hδ,
    eventually_const_le_mul_rpow hσ (show (0 : ℝ) < 1 by norm_num) A,
    eventually_ge_atTop (4 * Real.exp 1), eventually_ge_atTop (8 : ℝ)]
    with y hlog hA hyexp hy8
  have hy0 : 0 < y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have ha2 : 2 ≤ y / 4 := by linarith
  have ha0 : 0 < y / 4 := by positivity
  have hb0 : 0 ≤ 5 * y := by positivity
  have hden : 1 ≤ Real.log (y / 4) := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (y / 4) := Real.log_le_log (Real.exp_pos _) (by linarith)
  have hden0 : 0 < Real.log (y / 4) := by linarith
  have hpow : 1 ≤ y ^ (2 * δ) := Real.one_le_rpow hy1 (by linarith)
  intro L hL hLlog χ hχ
  have hL0 : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg (by exact_mod_cast hL)
  have hLpow : Real.log (L : ℝ) ≤ y ^ (2 * δ) := by
    simpa only [two_mul] using (hlog L hLlog).1
  have hfrac : Real.log (L : ℝ) / Real.log (y / 4) ≤ y ^ (2 * δ) := by
    apply le_trans _ hLpow
    apply (div_le_iff₀ hden0).mpr
    exact le_mul_of_one_le_right hL0 hden
  have hfactor : 1 + Real.log (L : ℝ) / Real.log (y / 4) ≤ 2 * y ^ (2 * δ) := by linarith
  have hfilter : (primeBand (y / 4) (5 * y)).filter
      (fun p : ℕ => (0 : ℝ) < 1 * (p : ℝ) ∧ 1 * (p : ℝ) ≤ 5 * y) =
      primeBand (y / 4) (5 * y) := by
    apply filter_eq_self.mpr
    intro p hp
    have hp' := (mem_primeBand_iff ha0.le hb0 p).mp hp
    simpa only [one_mul] using And.intro (show (0 : ℝ) < p by exact_mod_cast hp'.1.pos) hp'.2.2
  have hbasic := hbound L hL χ hχ (y / 4) (5 * y) 1 0 (5 * y)
    ha2 hb0 (by norm_num) (by norm_num) hb0
  rw [hfilter] at hbasic
  calc
    _ ≤ 2 * (5 * y) * C * (y / 4) ^ (-(1 : ℝ) / 96) *
        (1 + Real.log (L : ℝ) / Real.log (y / 4)) := hbasic
    _ ≤ 2 * (5 * y) * C * (y / 4) ^ (-(1 : ℝ) / 96) * (2 * y ^ (2 * δ)) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = A * y ^ ((95 : ℝ) / 96 + 2 * δ) := by
      rw [Real.div_rpow hy0.le (by norm_num)]
      have h31 : y ^ ((95 : ℝ) / 96) = y * y ^ (-(1 : ℝ) / 96) := by
        rw [show (95 : ℝ) / 96 = 1 + (-(1 : ℝ) / 96) by norm_num, Real.rpow_add hy0, Real.rpow_one]
      rw [Real.rpow_add hy0, h31]
      dsimp only [A]
      ring
    _ ≤ y ^ σ * y ^ ((95 : ℝ) / 96 + 2 * δ) :=
      mul_le_mul_of_nonneg_right (by simpa only [one_mul] using hA) (by positivity)
    _ = y ^ ((95 : ℝ) / 96 + 2 * δ + σ) := by
      rw [← Real.rpow_add hy0]
      congr 1
      ring

theorem wideAmbientPrimeCancellation_of_zero_free
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) : WideAmbientPrimeCancellationAt (95 / 96) := by
  intro δ hδ _ σ hσ
  exact eventually_wide_ambient_prime_cancellation hZ hδ hσ

theorem target_of_wide_smooth_primes_and_zero_free
    (hS : WideSmoothShiftedPrimeSupply) (hZ : PrimitiveZeroFreeRightOf (23 / 24)) :
    fcTypeOfName% "Erdos1057.erdos_1057" := by
  exact target_of_wide_smooth_supply_and_cancellation (by norm_num : (95 : ℝ) / 96 < 1)
    hS (wideAmbientPrimeCancellation_of_zero_free hZ)

theorem target_of_candidate_prime_mass_and_zero_free
    (hM : CandidateShiftedPrimeMassSupply) (hZ : PrimitiveZeroFreeRightOf (23 / 24)) :
    fcTypeOfName% "Erdos1057.erdos_1057" :=
  target_of_wide_smooth_primes_and_zero_free (wide_smooth_supply_of_candidate_prime_mass hM) hZ

theorem eventually_candidate_Q_prime_exponential_cancellation
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (f : ℕ), 0 < f → (f : ℝ) ≤ Real.exp L →
      ∀ χ : DirichletCharacter ℂ f, χ ≠ 1 →
      ∀ (m : ℕ), m ≠ 0 → (m : ℝ) ≤ Real.exp L →
      ∀ (a R : ℕ), a ≠ 0 → R ≠ 0 →
        ‖∑ p ∈ ((candidateQBand (c*L) 0).filter
          (fun p => p*R ∈ arithmeticProductWindow a (Real.exp L))).filter
            (fun p => p.Coprime m), χ (p : ZMod f)‖ ≤
          ((16*Real.exp L) / ((a*R : ℕ) : ℝ)) * Real.exp (-(c/192)*L) := by
  filter_upwards [eventually_prime_band_coprime_relative_exponential_bound hZ hc] with L hL
  intro f hf hfL χ hχ m hm hmL a R ha hR
  rw [candidate_Q_zero_product_window_eq c L ha]
  exact hL f hf hfL χ hχ (Real.exp ((6/5 : ℝ)*(c*L))) ((a*R : ℕ) : ℝ)
    (Real.exp L) (16*Real.exp L) (Real.exp_pos _).le
    (Nat.cast_pos.mpr (Nat.mul_pos (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hR)))
    (Real.exp_pos L).le (by positivity) m hm hmL

theorem eventually_candidate_Q_character_exponential_cancellation
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (f : ℕ), 0 < f → (f : ℝ) ≤ Real.exp L →
      ∀ χ : DirichletCharacter ℂ f, χ ≠ 1 →
      ∀ (m : ℕ), m ≠ 0 → (m : ℝ) ≤ Real.exp L →
      ∀ (r jStar : ℕ) (hr : 0 < r), 0 < jStar →
      ∀ a : ℕ, a ≠ 0 →
        ‖∑ n ∈ (arithmeticProductWindow a (Real.exp L)).filter (fun n => n.Coprime m),
          (candidateQWeight c L r jStar n : ℂ) * χ (n : ZMod f)‖ ≤
          ((16*Real.exp L) / (a : ℝ)) * Real.exp (-(c/192)*L) * candidateQRestHarmonicMass c L r jStar hr := by
  filter_upwards [eventually_candidate_Q_prime_exponential_cancellation hZ hc] with L hL
  intro f hf hfL χ hχ m hm hmL r jStar hr hj a ha
  apply candidate_Q_character_bound_of_prime_bound c L r jStar hr hj
    (arithmeticProductWindow a (Real.exp L)) χ m ((16*Real.exp L)/(a : ℝ)) (Real.exp (-(c/192)*L))
    (by positivity) (Real.exp_nonneg _)
  intro y
  have hb := hL f hf hfL χ hχ m hm hmL a
    (orderedSlotProduct (candidateQRestChoices c L r jStar hr) y) ha
    (candidate_Q_rest_product_nonzero c L r jStar hr y)
  simpa only [Nat.cast_mul, div_mul_eq_div_div] using hb

theorem eventually_candidate_character_exponential_cancellation
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (q : ℝ), 0 ≤ q →
      ∀ (r jStar : ℕ) (hr : 0 < r), 0 < jStar →
      ∀ (f : ℕ), 0 < f → (f : ℝ) ≤ Real.exp L →
      ∀ χ : DirichletCharacter ℂ f, χ ≠ 1 →
      ∀ (m : ℕ), m ≠ 0 → (m : ℝ) ≤ Real.exp L →
        ‖∑ u ∈ (arithmeticProductWindow 1 (Real.exp L)).filter (fun u => u.Coprime m),
          (candidateCoefficient c L q r jStar u : ℂ) * χ (u : ZMod f)‖ ≤
          (16*Real.exp L) * Real.exp (-(c/192)*L) * candidateOneMarkedHarmonicMass c L q *
            candidateQRestHarmonicMass c L r jStar hr := by
  filter_upwards [eventually_candidate_character_coprime_convolution hc,
    eventually_candidate_Q_character_exponential_cancellation hZ hc,
    eventually_ge_atTop (0 : ℝ)] with L hconv hQ hL
  intro q hq r jStar hr hj f hf hfL χ hχ m hm hmL
  let R : ℝ := candidateQRestHarmonicMass c L r jStar hr
  let C : ℝ := (16*Real.exp L) * Real.exp (-(c/192)*L) * R
  have hR : 0 ≤ R := candidate_Q_rest_harmonic_nonneg c L r jStar hr
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have htest := hconv q r jStar f m χ (fun _ => 1)
  simp only [mul_one] at htest
  rw [htest]
  calc
    _ ≤ ∑ a ∈ (candidateSmallPSet c L (16*Real.exp L + 1)).filter (fun a => a.Coprime m),
        ‖(candidatePWeight c L q a : ℂ) * χ (a : ZMod f) *
          ∑ n ∈ (arithmeticProductWindow a (Real.exp L)).filter (fun n => n.Coprime m),
            (candidateQWeight c L r jStar n : ℂ) * χ (n : ZMod f)‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ (candidateSmallPSet c L (16*Real.exp L + 1)).filter (fun a => a.Coprime m),
        (candidatePWeight c L q a / (a : ℝ)) * C := by
      apply sum_le_sum
      intro a ha
      have hWa := candidate_P_weight_nonneg c L hq a
      have ha0 : a ≠ 0 := candidate_small_P_set_nonzero (mem_filter.mp ha).1
      have hi := hQ f hf hfL χ hχ m hm hmL r jStar hr hj a ha0
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hWa]
      calc
        _ ≤ candidatePWeight c L q a *
            ‖∑ n ∈ (arithmeticProductWindow a (Real.exp L)).filter (fun n => n.Coprime m),
              (candidateQWeight c L r jStar n : ℂ) * χ (n : ZMod f)‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_of_le_one_right hWa (χ.norm_le_one _)
        _ ≤ candidatePWeight c L q a *
            (((16*Real.exp L)/(a : ℝ)) * Real.exp (-(c/192)*L) * R) :=
          mul_le_mul_of_nonneg_left hi hWa
        _ = _ := by dsimp only [C]; ring
    _ ≤ ∑ a ∈ candidateSmallPSet c L (16*Real.exp L + 1),
        (candidatePWeight c L q a / (a : ℝ)) * C := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro a _ _
      exact mul_nonneg (div_nonneg (candidate_P_weight_nonneg c L hq a) (Nat.cast_nonneg a)) hC
    _ = (∑ a ∈ candidateSmallPSet c L (16*Real.exp L + 1),
        candidatePWeight c L q a / (a : ℝ)) * C := (sum_mul _ _ _).symm
    _ ≤ candidateOneMarkedHarmonicMass c L q * C := by
      apply mul_le_mul_of_nonneg_right _ hC
      exact candidate_full_P_harmonic_sum_le_total (mul_nonneg hc.le hL) hq
    _ = _ := by dsimp only [C, R]; ring

theorem exists_candidate_character_relative_exponential_bound
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q : ℝ} {r : ℕ}
    (hc : 0 < c) (hr : 0 < r) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcenter : (11/5 : ℝ) * (r : ℝ) * c = 1) :
    ∃ J : ℕ, ∀ᶠ L : ℝ in atTop, ∀ jStar : ℕ, J < jStar →
      ∀ (f : ℕ), 0 < f → (f : ℝ) ≤ Real.exp L →
      ∀ χ : DirichletCharacter ℂ f, χ ≠ 1 →
      ∀ (m : ℕ), m ≠ 0 → (m : ℝ) ≤ Real.exp L →
        ‖∑ u ∈ (arithmeticProductWindow 1 (Real.exp L)).filter (fun u => u.Coprime m),
          (candidateCoefficient c L q r jStar u : ℂ) * χ (u : ZMod f)‖ ≤
          candidateCoefficientWindowMass c L q r jStar * Real.exp (-(c/384)*L) := by
  obtain ⟨V, hV, hrest⟩ := exists_candidate_Q_rest_harmonic_upper hc r hr
  obtain ⟨K, hK, J, hlower⟩ :=
    exists_candidate_coefficient_window_mass_lower hc hr hq0 hq1 hcenter
  have hsmall := eventually_linear_exponential_profile_le_rpow
    (div_pos hc (by norm_num : (0 : ℝ) < 384))
    (div_pos hc (by norm_num : (0 : ℝ) < 384)) 0 ((16*V)/K) 0
  simp only [zero_mul, zero_add, neg_zero, Real.rpow_zero] at hsmall
  refine ⟨J, ?_⟩
  filter_upwards [eventually_candidate_character_exponential_cancellation hZ hc,
    hrest, hlower, hsmall, eventually_candidate_one_marked_mass_ge_one hc hq0 hq1.le,
    eventually_gt_atTop (0 : ℝ)] with L hcancel hrestL hlowerL hsmallL hPone hL
  intro jStar hj f hf hfL χ hχ m hm hmL
  have hj0 : 0 < jStar := (Nat.zero_le J).trans_lt hj
  have hP : 0 ≤ candidateOneMarkedHarmonicMass c L q := zero_le_one.trans hPone
  have hQ : 0 ≤ candidateQHarmonicMass c L r jStar := by
    apply tsum_nonneg
    intro n
    exact div_nonneg (candidate_Q_weight_nonneg c L r jStar n) (Nat.cast_nonneg n)
  have hexp : Real.exp (-(c/384)*L) * Real.exp (-(c/384)*L) =
      Real.exp (-(c/192)*L) := by rw [← Real.exp_add]; congr 1; ring
  have hdecay : ((16*V)/K) * L * Real.exp (-(c/192)*L) ≤ Real.exp (-(c/384)*L) := by
    calc
      _ = (((16*V)/K) * L * Real.exp (-(c/384)*L)) * Real.exp (-(c/384)*L) := by
        rw [mul_assoc (((16*V)/K)*L), hexp]
      _ ≤ 1 * Real.exp (-(c/384)*L) :=
        mul_le_mul_of_nonneg_right hsmallL (Real.exp_nonneg _)
      _ = _ := one_mul _
  calc
    _ ≤ (16*Real.exp L) * Real.exp (-(c/192)*L) * candidateOneMarkedHarmonicMass c L q *
        candidateQRestHarmonicMass c L r jStar hr :=
      hcancel q hq0 r jStar hr hj0 f hf hfL χ hχ m hm hmL
    _ ≤ (16*Real.exp L) * Real.exp (-(c/192)*L) * candidateOneMarkedHarmonicMass c L q *
        (V * candidateQHarmonicMass c L r jStar) :=
      mul_le_mul_of_nonneg_left (hrestL jStar hj0) (by positivity)
    _ = (((16*V)/K) * L * Real.exp (-(c/192)*L)) *
        (K * (Real.exp L/L) * candidateOneMarkedHarmonicMass c L q *
          candidateQHarmonicMass c L r jStar) := by
      field_simp
    _ ≤ Real.exp (-(c/384)*L) *
        (K * (Real.exp L/L) * candidateOneMarkedHarmonicMass c L q *
          candidateQHarmonicMass c L r jStar) :=
      mul_le_mul_of_nonneg_right hdecay (by positivity)
    _ ≤ Real.exp (-(c/384)*L) * candidateCoefficientWindowMass c L q r jStar :=
      mul_le_mul_of_nonneg_left (hlowerL jStar hj) (Real.exp_nonneg _)
    _ = _ := mul_comm _ _

theorem exists_candidate_exponential_conductor_range_power_bound
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q : ℝ} {r : ℕ}
    (hc : 0 < c) (hr : 0 < r) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcenter : (11/5 : ℝ) * (r : ℝ) * c = 1) (B : ℝ) :
    ∃ J : ℕ, ∀ᶠ L : ℝ in atTop, ∀ jStar : ℕ, J < jStar →
      ∀ N R : ℕ, (N : ℝ) ≤ Real.exp L → (R : ℝ) ≤ Real.exp ((c/512)*L) →
        candidateSmallPrimitiveTypeIMass c L q r jStar N R ≤
          candidateCoefficientWindowMass c L q r jStar * L^(-B) := by
  obtain ⟨J, hnorm⟩ := exists_candidate_character_relative_exponential_bound
    hZ hc hr hq0 hq1 hcenter
  have hdecay := eventually_linear_exponential_profile_le_rpow
    (by positivity : 0 < c/1536) (by positivity : 0 < c/1536)
    0 (4*primeEulerProductUpperConstant) B
  simp only [zero_mul, zero_add] at hdecay
  refine ⟨J, ?_⟩
  filter_upwards [hnorm, hdecay, eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (Real.log 2)] with L hnormL hdecayL hL1 hlog2
  intro jStar hj N R hN hR
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  let XA := candidateCoefficientWindowMass c L q r jStar
  have hXA : 0 ≤ XA := by
    apply sum_nonneg
    intro u _
    exact candidate_coefficient_nonneg c L hq0 r jStar u
  have hweight : 0 ≤ XA * Real.exp (-(c/384)*L) := by positivity
  have hD : 1 ≤ Real.exp L := by
    exact (Real.one_le_exp_iff).mpr hL.le
  have hbound := candidate_small_primitive_mass_le c L q r jStar N R
    (fun _ => XA * Real.exp (-(c/384)*L)) (fun _ _ => hweight) hD hN (by
      intro d hd f hf ψ _ hψ
      have hdpos : 0 < d := (mem_Icc.mp (mem_filter.mp hd).1).1
      have hdN : d ≤ N := (mem_Icc.mp (mem_filter.mp hd).1).2
      have hffilt := mem_filter.mp hf
      have hfpos : 0 < f := lt_trans Nat.zero_lt_one hffilt.2.1
      have hfdvd : f ∣ d := Nat.dvd_of_mem_divisors hffilt.1
      have hfle : f ≤ d := Nat.le_of_dvd hdpos hfdvd
      have hfL : (f : ℝ) ≤ Real.exp L :=
        (Nat.cast_le.mpr (hfle.trans hdN)).trans hN
      have hdf : d/f ≠ 0 := (Nat.div_pos hfle hfpos).ne'
      have hdfL : ((d/f : ℕ) : ℝ) ≤ Real.exp L :=
        (Nat.cast_le.mpr ((Nat.div_le_self d f).trans hdN)).trans hN
      exact hnormL jStar hj f hfpos hfL ψ hψ (d/f) hdf hdfL)
  have hlog : Real.log (2*Real.exp L) ≤ 2*L := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero L), Real.log_exp]
    linarith
  have hlog0 : 0 ≤ Real.log (2*Real.exp L) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero L), Real.log_exp]
    positivity
  have hcardN : (Icc 2 R).card ≤ R := by rw [Nat.card_Icc]; omega
  have hcard : ((Icc 2 R).card : ℝ) ≤ Real.exp ((c/512)*L) := (Nat.cast_le.mpr hcardN).trans hR
  have hsum : (∑ _f ∈ Icc 2 R, XA * Real.exp (-(c/384)*L)) ≤
      Real.exp ((c/512)*L) * (XA * Real.exp (-(c/384)*L)) := by
    simp only [sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard hweight
  calc
    _ ≤ ((2*primeEulerProductUpperConstant) * Real.log (2*Real.exp L)) *
        ∑ _f ∈ Icc 2 R, XA * Real.exp (-(c/384)*L) := hbound
    _ ≤ ((2*primeEulerProductUpperConstant) * (2*L)) *
        (Real.exp ((c/512)*L) * (XA * Real.exp (-(c/384)*L))) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hlog (by positivity [primeEulerProductUpperConstant_pos])
      · exact hsum
      · exact sum_nonneg (fun _ _ => hweight)
      · positivity [primeEulerProductUpperConstant_pos]
    _ = XA * ((4*primeEulerProductUpperConstant) * L * Real.exp (-(c/1536)*L)) := by
      have hexp : Real.exp ((c/512)*L) * Real.exp (-(c/384)*L) =
          Real.exp (-(c/1536)*L) := by rw [← Real.exp_add]; congr 1; ring
      calc
        _ = XA * ((4*primeEulerProductUpperConstant) * L *
            (Real.exp ((c/512)*L) * Real.exp (-(c/384)*L))) := by ring
        _ = _ := by rw [hexp]
    _ ≤ XA * L^(-B) := mul_le_mul_of_nonneg_left hdecayL hXA

theorem exists_candidate_relative_typeI_remainder_bound_of_large
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q θ : ℝ} {r : ℕ}
    (hc : 0 < c) (hr : 0 < r) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcenter : (11/5 : ℝ) * (r : ℝ) * c = 1) (hθ : θ ≤ 1)
    (hlarge : ∀ B : ℝ, ∀ᶠ L : ℝ in atTop, ∀ jStar : ℕ, 0 < jStar →
      ∀ N : ℕ, (N : ℝ) ≤ Real.exp (θ * L) →
        candidateLargePrimitiveTypeIMass c L q r jStar N ⌊Real.exp ((c/512)*L)⌋₊ ≤
          Real.exp L * L^(-B)) (D : ℝ) :
    ∃ J : ℕ, ∀ jStar : ℕ, J < jStar → ∀ᶠ L : ℝ in atTop,
      ∀ N : ℕ, (N : ℝ) ≤ Real.exp (θ * L) →
        (∑ d ∈ oddSquarefreeModuli N,
          |shiftedTotientSieveRemainder (arithmeticProductWindow 1 (Real.exp L))
            (candidateCoefficient c L q r jStar) d|) ≤
          candidateCoefficientWindowMass c L q r jStar *
            (L^(-D) + (16 * primeEulerProductUpperConstant) * L^(-18 : ℝ)) := by
  obtain ⟨C, _, Jmass, hmass⟩ :=
    exists_candidate_coefficient_mass_polynomial_lower hc hr hq0 hq1 hcenter
  obtain ⟨Jsmall, hsmall⟩ :=
    exists_candidate_exponential_conductor_range_power_bound hZ hc hr hq0 hq1 hcenter (D + 1)
  refine ⟨max Jmass Jsmall, ?_⟩
  intro jStar hj
  have hjmass : Jmass < jStar := lt_of_le_of_lt (le_max_left _ _) hj
  have hjsmall : Jsmall < jStar := lt_of_le_of_lt (le_max_right _ _) hj
  have hjpos : 0 < jStar := lt_of_le_of_lt (Nat.zero_le _) hj
  filter_upwards [hmass jStar hjmass, hsmall, hlarge (C + D + 1),
    eventually_candidate_typeI_remainder_le_primitive hc,
    eventually_ge_atTop (2 : ℝ)] with L hm hs hl hrem hL
  intro N hN
  have hL0 : 0 ≤ L := by linarith
  have hN' : (N : ℝ) ≤ Real.exp L := hN.trans
    (Real.exp_le_exp.mpr (by nlinarith only [hθ, hL0]))
  have hR : (⌊Real.exp ((c/512)*L)⌋₊ : ℝ) ≤ Real.exp ((c/512)*L) :=
    Nat.floor_le (Real.exp_pos _).le
  have hprim := candidate_primitive_typeI_relative_bound_of_split c L q C D
    r jStar N ⌊Real.exp ((c/512)*L)⌋₊ hL hm
    (hs jStar hjsmall N _ hN' hR) (hl jStar hjpos N hN)
  calc
    _ ≤ candidatePrimitiveTypeIMass c L q r jStar N +
        candidateCoefficientWindowMass c L q r jStar *
          ((16 * primeEulerProductUpperConstant) * L^(-18 : ℝ)) := hrem q hq0 r jStar N hN'
    _ ≤ candidateCoefficientWindowMass c L q r jStar * L^(-D) +
        candidateCoefficientWindowMass c L q r jStar *
          ((16 * primeEulerProductUpperConstant) * L^(-18 : ℝ)) := add_le_add hprim le_rfl
    _ = _ := (mul_add _ _ _).symm

theorem exists_candidate_relative_typeI_remainder_power_bound
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q θ : ℝ} {r : ℕ}
    (hc : 0 < c) (hr : 0 < r) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcenter : (11/5 : ℝ) * (r : ℝ) * c = 1) (hθ : θ < 1/2) (D : ℝ) :
    ∃ J : ℕ, ∀ jStar : ℕ, J < jStar → ∀ᶠ L : ℝ in atTop,
      ∀ N : ℕ, (N : ℝ) ≤ Real.exp (θ * L) →
        (∑ d ∈ oddSquarefreeModuli N,
          |shiftedTotientSieveRemainder (arithmeticProductWindow 1 (Real.exp L))
            (candidateCoefficient c L q r jStar) d|) ≤
          candidateCoefficientWindowMass c L q r jStar *
            (L^(-D) + (16 * primeEulerProductUpperConstant) * L^(-18 : ℝ)) := by
  apply exists_candidate_relative_typeI_remainder_bound_of_large hZ hc hr hq0 hq1 hcenter
    (by linarith : θ ≤ 1) ?_ D
  intro B
  exact eventually_candidate_large_primitive_power_saving hc hr hcenter hq0 hq1 hθ B

theorem exists_candidate_shifted_rough_mass_estimate (hZ : PrimitiveZeroFreeRightOf (23 / 24)) :
    ∃ K : ℝ, 0 < K ∧ ∀ (c q b : ℝ) (r h : ℕ),
      0 < c → 0 < r → 0 ≤ q → q < 1 →
      (11/5 : ℝ) * (r : ℝ) * c = 1 →
      0 < b → 1 ≤ h → Even h → b * (4 * (h : ℝ) + 2) < 1/2 →
      ∃ J : ℕ, ∀ jStar : ℕ, J < jStar → ∀ᶠ L : ℝ in atTop,
        |candidateShiftedRoughMass c L q r jStar (Real.exp (b * L)) -
            candidateCoefficientWindowMass c L q r jStar *
              shiftedPrimeAvoidanceProduct (Real.exp (b * L))| ≤
          candidateCoefficientWindowMass c L q r jStar *
            shiftedPrimeAvoidanceProduct (Real.exp (b * L)) *
            (K * Real.exp (-(h : ℝ)) + L^(-16 : ℝ)) := by
  obtain ⟨K, hK, hsieve⟩ := exists_shifted_totient_rough_sieve
  refine ⟨K, hK, ?_⟩
  intro c q b r h hc hr hq0 hq1 hcenter hb hh heven hlevel
  let theta : ℝ := (b * (4 * (h : ℝ) + 2) + 1/2) / 2
  have htheta : theta < 1/2 := by dsimp [theta]; linarith only [hlevel]
  obtain ⟨J, hdist⟩ := exists_candidate_relative_typeI_remainder_power_bound
    hZ hc hr hq0 hq1 hcenter htheta (18 : ℝ)
  refine ⟨J, ?_⟩
  intro jStar hj
  filter_upwards [hdist jStar hj, eventually_candidate_midpoint_sieve_scale hb h hlevel,
    eventually_shifted_avoidance_absorbs_power hb (1 + 16 * primeEulerProductUpperConstant)
      (by positivity [primeEulerProductUpperConstant_pos])]
    with L hd hscale habs
  let N : ℕ := ⌊Real.exp (theta * L)⌋₊
  have hN : (N : ℝ) ≤ Real.exp (theta * L) := Nat.floor_le (Real.exp_pos _).le
  have hXA : 0 ≤ candidateCoefficientWindowMass c L q r jStar := by
    apply sum_nonneg
    intro u _
    exact candidate_coefficient_nonneg c L hq0 r jStar u
  have hsub : blockSieveModuli ((primeBand 0 (Real.exp (b * L))).erase 2)
      ((Real.exp (b * L))^(4 * (h : ℝ) + 2)) ⊆ oddSquarefreeModuli N := by
    apply odd_sieve_moduli_subset
    · intro p hp
      exact small_prime_pool_prime (mem_of_mem_erase hp)
    · intro p hp
      exact (mem_erase.mp hp).1
    · exact hscale.2.1
  have herror : (∑ d ∈ blockSieveModuli ((primeBand 0 (Real.exp (b * L))).erase 2)
        ((Real.exp (b * L))^(4 * (h : ℝ) + 2)),
        |shiftedTotientSieveRemainder (arithmeticProductWindow 1 (Real.exp L))
          (candidateCoefficient c L q r jStar) d|) ≤
      candidateCoefficientWindowMass c L q r jStar *
        shiftedPrimeAvoidanceProduct (Real.exp (b * L)) * L^(-16 : ℝ) := by
    calc
      _ ≤ ∑ d ∈ oddSquarefreeModuli N,
          |shiftedTotientSieveRemainder (arithmeticProductWindow 1 (Real.exp L))
            (candidateCoefficient c L q r jStar) d| :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)
      _ ≤ candidateCoefficientWindowMass c L q r jStar *
          (L^(-18 : ℝ) + (16 * primeEulerProductUpperConstant) * L^(-18 : ℝ)) := hd N hN
      _ = candidateCoefficientWindowMass c L q r jStar *
          ((1 + 16 * primeEulerProductUpperConstant) * L^(-18 : ℝ)) := by ring
      _ ≤ candidateCoefficientWindowMass c L q r jStar *
          (shiftedPrimeAvoidanceProduct (Real.exp (b * L)) * L^(-16 : ℝ)) :=
        mul_le_mul_of_nonneg_left habs hXA
      _ = _ := by ring
  have hs := hsieve (arithmeticProductWindow 1 (Real.exp L))
    (candidateCoefficient c L q r jStar) hscale.1 hh heven
    (fun u _ => candidate_coefficient_nonneg c L hq0 r jStar u)
  change |candidateShiftedRoughMass c L q r jStar (Real.exp (b * L)) -
      candidateCoefficientWindowMass c L q r jStar *
        shiftedPrimeAvoidanceProduct (Real.exp (b * L))| ≤
    candidateCoefficientWindowMass c L q r jStar *
      shiftedPrimeAvoidanceProduct (Real.exp (b * L)) * K * Real.exp (-(h : ℝ)) + _ at hs
  calc
    _ ≤ candidateCoefficientWindowMass c L q r jStar *
        shiftedPrimeAvoidanceProduct (Real.exp (b * L)) * K * Real.exp (-(h : ℝ)) +
        ∑ d ∈ blockSieveModuli ((primeBand 0 (Real.exp (b * L))).erase 2)
          ((Real.exp (b * L))^(4 * (h : ℝ) + 2)),
          |shiftedTotientSieveRemainder (arithmeticProductWindow 1 (Real.exp L))
            (candidateCoefficient c L q r jStar) d| := hs
    _ ≤ candidateCoefficientWindowMass c L q r jStar *
        shiftedPrimeAvoidanceProduct (Real.exp (b * L)) * K * Real.exp (-(h : ℝ)) +
        candidateCoefficientWindowMass c L q r jStar *
          shiftedPrimeAvoidanceProduct (Real.exp (b * L)) * L^(-16 : ℝ) :=
      add_le_add le_rfl herror
    _ = _ := by ring

theorem exists_candidate_shifted_rough_mass_density_lower (hZ : PrimitiveZeroFreeRightOf (23 / 24)) :
    ∃ K : ℝ, 0 < K ∧ ∀ (c q b : ℝ) (r h : ℕ),
      0 < c → 0 < r → 0 ≤ q → q < 1 →
      (11/5 : ℝ)*(r : ℝ)*c = 1 →
      0 < b → 1 ≤ h → Even h → b*(4*(h : ℝ)+2) < 1/2 →
      ∃ J : ℕ, ∀ jStar : ℕ, J < jStar → ∀ ε : ℝ, 0 < ε → ∀ᶠ L : ℝ in atTop,
        ((shiftedSieveRatioConstant*Mertens.primeProductLimitConstant/b)*
            (1-K*Real.exp (-(h : ℝ)))-ε) *
          candidateCoefficientWindowMass c L q r jStar / L ≤
        candidateShiftedRoughMass c L q r jStar (Real.exp (b*L)) := by
  obtain ⟨K, hK, hmass⟩ := exists_candidate_shifted_rough_mass_estimate hZ
  refine ⟨K, hK, ?_⟩
  intro c q b r h hc hr hq0 hq1 hcenter hb hh heven hlevel
  obtain ⟨J, hJ⟩ := hmass c q b r h hc hr hq0 hq1 hcenter hb hh heven hlevel
  refine ⟨J, ?_⟩
  intro jStar hj ε hε
  have hpow : Tendsto (fun L : ℝ => L^(-16 : ℝ)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 16)
  have hlim := (exponential_shifted_prime_avoidance_product_tendsto hb).mul
    (hpow.const_sub (1-K*Real.exp (-(h : ℝ))))
  simp only [sub_zero] at hlim
  have hev := hlim.eventually_const_lt (show
    (shiftedSieveRatioConstant*Mertens.primeProductLimitConstant/b)*
        (1-K*Real.exp (-(h : ℝ)))-ε <
      (shiftedSieveRatioConstant*Mertens.primeProductLimitConstant/b)*
        (1-K*Real.exp (-(h : ℝ))) by linarith)
  filter_upwards [hJ jStar hj, hev, eventually_gt_atTop (0 : ℝ)] with L hm hd hL
  have hXA : 0 ≤ candidateCoefficientWindowMass c L q r jStar := by
    apply sum_nonneg
    intro u _
    exact candidate_coefficient_nonneg c L hq0 r jStar u
  have hlower : candidateCoefficientWindowMass c L q r jStar *
      shiftedPrimeAvoidanceProduct (Real.exp (b*L)) *
        (1-K*Real.exp (-(h : ℝ))-L^(-16 : ℝ)) ≤
      candidateShiftedRoughMass c L q r jStar (Real.exp (b*L)) := by
    have h := (neg_le_neg hm).trans (neg_abs_le _)
    nlinarith
  calc
    _ ≤ ((L*shiftedPrimeAvoidanceProduct (Real.exp (b*L)))*
          (1-K*Real.exp (-(h : ℝ))-L^(-16 : ℝ))) *
          candidateCoefficientWindowMass c L q r jStar / L := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hd.le hXA) hL.le
    _ = candidateCoefficientWindowMass c L q r jStar *
        shiftedPrimeAvoidanceProduct (Real.exp (b*L)) *
        (1-K*Real.exp (-(h : ℝ))-L^(-16 : ℝ)) := by field_simp
    _ ≤ _ := hlower

theorem exists_candidate_prime_band_sqrt_rough_mass_estimate (hZ : PrimitiveZeroFreeRightOf (23 / 24)) :
    ∃ K : ℝ, 0 < K ∧ ∀ (c q a v : ℝ) (r : ℕ),
      0 < c → 0 < r → 0 ≤ q → q < 1 →
      (11/5 : ℝ)*(r : ℝ)*c = 1 →
      0 < a → a ≤ v → v < 1/2 →
      ∃ J : ℕ, ∀ jStar : ℕ, J < jStar → ∀ᶠ L : ℝ in atTop,
        |candidatePrimeBandRoughMass c L q r jStar
            (Real.exp (a*L)) (Real.exp (v*L)) (Real.exp (Real.sqrt L)) -
          candidateCoefficientWindowMass c L q r jStar *
            shiftedPrimeAvoidanceProduct (Real.exp (Real.sqrt L)) *
              (∑ p ∈ primeBand (Real.exp (a*L)) (Real.exp (v*L)),
                1 / ((p : ℝ)-1))| ≤
          candidateCoefficientWindowMass c L q r jStar *
            shiftedPrimeAvoidanceProduct (Real.exp (Real.sqrt L)) *
              (∑ p ∈ primeBand (Real.exp (a*L)) (Real.exp (v*L)),
                1 / ((p : ℝ)-1)) * K * Real.exp (-(roughCellSieveOrder L : ℝ)) +
          candidateCoefficientWindowMass c L q r jStar *
            ((1+16*primeEulerProductUpperConstant)*L^(-18 : ℝ)) := by
  classical
  obtain ⟨K, hK, hsieve⟩ := exists_summed_external_odd_prime_shifted_sieve
  refine ⟨K, hK, ?_⟩
  intro c q a v r hc hr hq0 hq1 hcenter ha hav hvhalf
  let theta : ℝ := (v+1/2)/2
  have htheta : theta < 1/2 := by dsimp [theta]; linarith only [hvhalf]
  have hv : 0 < v := ha.trans_le hav
  have hgap : 0 < theta-v := by dsimp [theta]; linarith only [hvhalf]
  have hmid : v+(theta-v)/2 < theta := by linarith
  have hbase : 0 ≤ v+(theta-v)/2 := by positivity
  obtain ⟨J, hdist⟩ := exists_candidate_relative_typeI_remainder_power_bound
    hZ hc hr hq0 hq1 hcenter htheta (18 : ℝ)
  refine ⟨J, ?_⟩
  intro jStar hj
  filter_upwards [hdist jStar hj, eventually_exp_le_floor_exp hbase hmid,
    eventually_rough_cell_sieve_parameters hgap, eventually_rough_test_proxy_cutoff ha,
    eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (Real.log 2/a)]
    with L hd hscale hpar hcut hL hLa
  let N : ℕ := ⌊Real.exp (theta*L)⌋₊
  let P : Finset ℕ := (primeBand 0 (Real.exp (Real.sqrt L))).erase 2
  let Q : Finset ℕ := primeBand (Real.exp (a*L)) (Real.exp (v*L))
  have hz : 1 < Real.exp (Real.sqrt L) := hpar.2.2.1
  have hP : ∀ p ∈ P, p.Prime := fun p hp => small_prime_pool_prime (mem_of_mem_erase hp)
  have hQ : ∀ p ∈ Q, p.Prime := by
    intro p hp
    exact ((mem_primeBand_iff (Real.exp_pos _).le (Real.exp_pos _).le p).mp hp).1
  have hQlower : ∀ p ∈ Q, Real.exp (a*L) < (p : ℝ) := by
    intro p hp
    exact ((mem_primeBand_iff (Real.exp_pos _).le (Real.exp_pos _).le p).mp hp).2.1
  have hQupper : ∀ p ∈ Q, (p : ℝ) ≤ Real.exp (v*L) := by
    intro p hp
    exact ((mem_primeBand_iff (Real.exp_pos _).le (Real.exp_pos _).le p).mp hp).2.2
  have hQodd : ∀ p ∈ Q, p ≠ 2 := by
    have hexp : 2 ≤ Real.exp (a*L) := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ)<2)]
      apply Real.exp_le_exp.mpr
      have := (div_le_iff₀ ha).mp hLa
      nlinarith only [this]
    intro p hp heq
    have hp' := hQlower p hp
    norm_num [heq] at hp'
    linarith
  have hout : ∀ p ∈ Q, p ∉ P := by
    intro p hp hpP
    have hpmax := small_prime_pool_le (Real.exp_pos (Real.sqrt L)).le (mem_of_mem_erase hpP)
    have hcutexp : Real.exp (Real.sqrt L) ≤ Real.exp (a*L) :=
      Real.exp_le_exp.mpr hcut
    exact (not_lt_of_ge (hpmax.trans hcutexp)) (hQlower p hp)
  have hprodlevel : ∀ p ∈ Q, ∀ d ∈ blockSieveModuli P
      ((Real.exp (Real.sqrt L))^(4*(roughCellSieveOrder L : ℝ)+2)), p*d ≤ N := by
    intro p hp d hd
    have hdmax := (block_sieve_modulus_properties P hP _ hd).2.1
    have hprod : (p : ℝ)*(d : ℝ) ≤ Real.exp ((v+(theta-v)/2)*L) := by
      calc
        _ ≤ Real.exp (v*L)*((Real.exp (Real.sqrt L))^(4*(roughCellSieveOrder L : ℝ)+2)) :=
          mul_le_mul (hQupper p hp) hdmax (Nat.cast_nonneg d) (Real.exp_pos _).le
        _ ≤ Real.exp (v*L)*Real.exp (((theta-v)/2)*L) :=
          mul_le_mul_of_nonneg_left hpar.2.2.2.1 (Real.exp_pos _).le
        _ = _ := by
          rw [← Real.exp_add]
          congr 1
          ring
    exact_mod_cast hprod.trans hscale
  have hs := hsieve P Q (arithmeticProductWindow 1 (Real.exp L))
    (candidateCoefficient c L q r jStar) N hz hpar.1 hpar.2.1 hP
    (fun p hp => (mem_erase.mp hp).1)
    (fun p hp => small_prime_pool_le (Real.exp_pos _).le (mem_of_mem_erase hp))
    hQ hQodd hout (fun u _ => candidate_coefficient_nonneg c L hq0 r jStar u) hprodlevel
  have hmass : (∑ p ∈ Q, ∑ u ∈ (arithmeticProductWindow 1 (Real.exp L)).filter
      (fun u => p ∣ 2*u+1 ∧ ∀ q ∈ P, ¬q ∣ 2*u+1),
      candidateCoefficient c L q r jStar u) =
      candidatePrimeBandRoughMass c L q r jStar
        (Real.exp (a*L)) (Real.exp (v*L)) (Real.exp (Real.sqrt L)) := by
    unfold candidatePrimeBandRoughMass
    apply sum_congr rfl
    intro p hp
    rw [shifted_rough_prime_filter_eq _ (Real.exp_pos _).le]
  rw [hmass] at hs
  have hN : (N : ℝ) ≤ Real.exp (theta*L) := Nat.floor_le (Real.exp_pos _).le
  have herr := hd N hN
  have herr' : (∑ m ∈ oddSquarefreeModuli N,
      |shiftedTotientSieveRemainder (arithmeticProductWindow 1 (Real.exp L))
        (candidateCoefficient c L q r jStar) m|) ≤
      candidateCoefficientWindowMass c L q r jStar *
        ((1+16*primeEulerProductUpperConstant)*L^(-18 : ℝ)) := by
    convert herr using 1; ring
  exact hs.trans (add_le_add le_rfl herr')

theorem exists_candidate_prime_band_sqrt_rough_mass_density_upper
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q a v : ℝ} {r : ℕ}
    (hc : 0 < c) (hr : 0 < r) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcenter : (11/5 : ℝ)*(r : ℝ)*c = 1)
    (ha : 0 < a) (hav : a ≤ v) (hvhalf : v < 1/2) :
    ∃ J : ℕ, ∀ jStar : ℕ, J < jStar → ∀ ε : ℝ, 0 < ε → ∀ᶠ L : ℝ in atTop,
      candidatePrimeBandRoughMass c L q r jStar
          (Real.exp (a*L)) (Real.exp (v*L)) (Real.exp (Real.sqrt L)) ≤
        (shiftedSieveRatioConstant*Mertens.primeProductLimitConstant*Real.log (v/a)+ε)*
          candidateCoefficientWindowMass c L q r jStar / Real.sqrt L := by
  obtain ⟨K, hK, hmass⟩ := exists_candidate_prime_band_sqrt_rough_mass_estimate hZ
  obtain ⟨J, hJ⟩ := hmass c q a v r hc hr hq0 hq1 hcenter ha hav hvhalf
  refine ⟨J, ?_⟩
  intro jStar hj ε hε
  have hinv : Tendsto (fun L : ℝ => L^(-1 : ℝ)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)
  have hpow : Tendsto (fun L : ℝ => L^(-17 : ℝ)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 17)
  have hlim := ((sqrt_shifted_prime_avoidance_product_tendsto.mul
    (exponential_prime_predecessor_reciprocal_tendsto ha hav)).mul (hinv.const_add 1)).add
      (hpow.const_mul (1+16*primeEulerProductUpperConstant))
  simp only [add_zero, mul_one, mul_zero] at hlim
  have hev := hlim.eventually_lt_const (show
    shiftedSieveRatioConstant*Mertens.primeProductLimitConstant*Real.log (v/a) <
      shiftedSieveRatioConstant*Mertens.primeProductLimitConstant*Real.log (v/a)+ε by linarith)
  filter_upwards [hJ jStar hj, hev,
    eventually_rough_cell_order_error_le ha hK.le (-1) 1,
    eventually_ge_atTop (1 : ℝ)] with L hm hd heL hL
  let X := candidateCoefficientWindowMass c L q r jStar
  let V := shiftedPrimeAvoidanceProduct (Real.exp (Real.sqrt L))
  let H := ∑ p ∈ primeBand (Real.exp (a*L)) (Real.exp (v*L)), 1/((p : ℝ)-1)
  let C := 1+16*primeEulerProductUpperConstant
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hsqrt : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hX : 0 ≤ X := by
    apply sum_nonneg
    intro u _
    exact candidate_coefficient_nonneg c L hq0 r jStar u
  have hV : 0 ≤ V := (shifted_prime_avoidance_product_pos _).le
  have hH : 0 ≤ H := by
    apply sum_nonneg
    intro p hp
    have hpprime := ((mem_primeBand_iff (Real.exp_pos _).le (Real.exp_pos _).le p).mp hp).1
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpprime.two_le
    exact div_nonneg (by norm_num) (by linarith)
  have hC : 0 ≤ C := by dsimp [C]; positivity [primeEulerProductUpperConstant_pos]
  have he : K*Real.exp (-(roughCellSieveOrder L : ℝ)) ≤ L^(-1 : ℝ) := by
    have hp : 0 ≤ L^((-1 : ℝ)+1)*Real.exp (-(a/2)*L) := by positivity
    nlinarith only [heL, hp, hK]
  have hpow_id : L*L^(-18 : ℝ)=L^(-17 : ℝ) := by
    calc
      _ = L^(1 : ℝ)*L^(-18 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hL0]; norm_num
  have hpow_bound : Real.sqrt L*L^(-18 : ℝ) ≤ L^(-17 : ℝ) := by
    rw [← hpow_id]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_self_iff.mpr (Or.inr hL)) (by positivity)
  have hmain : 0 ≤ X*V*H := mul_nonneg (mul_nonneg hX hV) hH
  have hupper : candidatePrimeBandRoughMass c L q r jStar
      (Real.exp (a*L)) (Real.exp (v*L)) (Real.exp (Real.sqrt L)) ≤
      X*V*H*(1+L^(-1 : ℝ))+X*C*L^(-18 : ℝ) := by
    have hb := (le_abs_self _).trans hm
    change _ ≤ X*V*H*K*Real.exp (-(roughCellSieveOrder L : ℝ))+
      X*(C*L^(-18 : ℝ)) at hb
    have he' := mul_le_mul_of_nonneg_left he hmain
    nlinarith only [hb, he']
  apply (le_div_iff₀ hsqrt).mpr
  calc
    _ ≤ (X*V*H*(1+L^(-1 : ℝ))+X*C*L^(-18 : ℝ))*Real.sqrt L :=
      mul_le_mul_of_nonneg_right hupper hsqrt.le
    _ = X*((Real.sqrt L*V*H)*(1+L^(-1 : ℝ))+C*(Real.sqrt L*L^(-18 : ℝ))) := by ring
    _ ≤ X*((Real.sqrt L*V*H)*(1+L^(-1 : ℝ))+C*L^(-17 : ℝ)) := by gcongr
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hd.le hX
      change X*((Real.sqrt L*V*H)*(1+L^(-1 : ℝ))+C*L^(-17 : ℝ)) ≤ _ at hh
      simpa only [mul_comm] using hh

theorem exists_candidate_unbalanced_proxy_upper
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q a v : ℝ} {r : ℕ}
    (hc : 0 < c) (hr : 0 < r) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcenter : (11 / 5 : ℝ) * (r : ℝ) * c = 1)
    (ha : 0 < a) (hav : a ≤ v) (hvhalf : v < 1 / 2) :
    ∃ J : ℕ, ∀ jStar : ℕ, J < jStar → ∀ M : ℝ, 0 ≤ M → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ L : ℝ in atTop, ∀ (F : Finset (ℕ × ℕ)) (f : ℕ → ℝ) (u : ℕ × ℕ → ℕ),
        (∀ w ∈ F, u w ∈ arithmeticProductWindow 1 (Real.exp L) ∧
          w.1 ∈ primeBand (Real.exp (a * L)) (Real.exp (v * L)) ∧ w.1 * w.2 = 2 * u w + 1) →
        (∀ w ∈ F, 0 ≤ f w.2 ∧ f w.2 ≤ M / (Mertens.primeProductLimitConstant * Real.sqrt L)) →
        (∀ w ∈ F, f w.2 ≠ 0 → ∀ p ∈ w.2.primeFactors, Real.exp (Real.sqrt L) < (p : ℝ)) →
        (∑ w ∈ F, candidateCoefficient c L q r jStar (u w) * f w.2) ≤
          (shiftedSieveRatioConstant * M * Real.log (v / a) + ε) *
            candidateCoefficientWindowMass c L q r jStar / L := by
  obtain ⟨J, hJ⟩ := exists_candidate_prime_band_sqrt_rough_mass_density_upper
    hZ hc hr hq0 hq1 hcenter ha hav hvhalf
  refine ⟨J, ?_⟩
  intro jStar hj M hM ε hε
  let K := Mertens.primeProductLimitConstant
  have hK : 0 < K := Mertens.prime_product_limit_constant_pos
  let δ := ε * K / (M + 1)
  have hδ : 0 < δ ∧ M * δ / K ≤ ε := proxy_mass_error_budget hK hM hε
  filter_upwards [hJ jStar hj δ hδ.1, eventually_rough_test_proxy_cutoff ha,
    eventually_gt_atTop (0 : ℝ)] with L hmass hcut hL
  intro F f u hdata hf hrough
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hC : 0 ≤ M / (K * Real.sqrt L) := div_nonneg hM (mul_pos hK hs).le
  have hbridge := candidate_prime_factor_proxy_bound (c := c) r jStar hq0 (Real.exp_nonneg _)
    (Real.exp_nonneg _) (Real.exp_le_exp.mpr hcut) hC F f u hdata hf hrough
  have hX : 0 ≤ candidateCoefficientWindowMass c L q r jStar := by
    apply sum_nonneg
    intro n hn
    exact candidate_coefficient_nonneg c L hq0 r jStar n
  calc
    _ ≤ (M / (K * Real.sqrt L)) * candidatePrimeBandRoughMass c L q r jStar
        (Real.exp (a * L)) (Real.exp (v * L)) (Real.exp (Real.sqrt L)) := hbridge
    _ ≤ (M / (K * Real.sqrt L)) *
        ((shiftedSieveRatioConstant * K * Real.log (v / a) + δ) *
          candidateCoefficientWindowMass c L q r jStar / Real.sqrt L) :=
      mul_le_mul_of_nonneg_left hmass hC
    _ = (shiftedSieveRatioConstant * M * Real.log (v / a) + M * δ / K) *
          candidateCoefficientWindowMass c L q r jStar / L :=
      sqrt_proxy_mass_product hK hL _ _ _ _ _
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (add_le_add le_rfl hδ.2) hX) hL.le

theorem exists_candidate_unbalanced_rough_logarithmic_proxy_upper
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q a v : ℝ} {r : ℕ}
    (hc : 0 < c) (hr : 0 < r) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcenter : (11 / 5 : ℝ) * (r : ℝ) * c = 1)
    (ha : 0 < a) (hav : a ≤ v) (hvhalf : v < 1 / 2) :
    ∃ J : ℕ, ∀ jStar : ℕ, J < jStar → ∀ M : ℝ, 0 ≤ M → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ L : ℝ in atTop, ∀ (γ S : ℝ) (F : Finset (ℕ × ℕ)) (u : ℕ × ℕ → ℕ),
        (∀ w ∈ F, u w ∈ arithmeticProductWindow 1 (Real.exp L) ∧
          w.1 ∈ primeBand (Real.exp (a * L)) (Real.exp (v * L)) ∧ w.1 * w.2 = 2 * u w + 1) →
        (∀ w ∈ F, roughTestCellProxyCoefficient γ L S
          (logarithmicCellBase (L ^ (-S)) (logarithmicCellIndex (L ^ (-S)) w.2)) ≤
            M / (Mertens.primeProductLimitConstant * Real.sqrt L)) →
        (∑ w ∈ F, candidateCoefficient c L q r jStar (u w) * roughTestLogarithmicProxy γ L S w.2) ≤
          (shiftedSieveRatioConstant * M * Real.log (v / a) + ε) *
            candidateCoefficientWindowMass c L q r jStar / L := by
  obtain ⟨J, hJ⟩ := exists_candidate_unbalanced_proxy_upper hZ hc hr hq0 hq1 hcenter ha hav hvhalf
  refine ⟨J, ?_⟩
  intro jStar hj M hM ε hε
  filter_upwards [hJ jStar hj M hM ε hε, eventually_gt_atTop (0 : ℝ)] with L hbound hL
  intro γ S F u hdata hcoef
  apply hbound F (roughTestLogarithmicProxy γ L S) u hdata
  · intro w hw
    refine ⟨rough_test_logarithmic_proxy_nonneg γ L S w.2, ?_⟩
    exact rough_test_logarithmic_proxy_le_coefficient
      (div_nonneg hM (mul_pos Mertens.prime_product_limit_constant_pos (Real.sqrt_pos.mpr hL)).le)
      (hcoef w hw)
  · intro w hw hne
    exact rough_test_logarithmic_proxy_support hne

theorem exists_candidate_unbalanced_rough_bin_upper_uniform_precision
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q γ a v M : ℝ} {r : ℕ}
    (hc : 0 < c) (hr : 0 < r) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcenter : (11 / 5 : ℝ) * (r : ℝ) * c = 1)
    (hγ : 0 < γ) (ha : 0 < a) (hav : a ≤ v) (hvhalf : v < 1 / 2)
    (hvγ : v < 1 - γ) (hM : 0 ≤ M)
    (hdensity : ∀ α ∈ Set.Icc a v, buchstabDensity γ (1 - α) ≤ M) :
    ∃ J : ℕ, ∀ S : ℝ, 0 ≤ S → ∀ jStar : ℕ, J < jStar → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ L : ℝ in atTop, ∀ (F : Finset (ℕ × ℕ)) (u : ℕ × ℕ → ℕ),
        (∀ w ∈ F, u w ∈ arithmeticProductWindow 1 (Real.exp L) ∧
          w.1 ∈ primeBand (Real.exp (a * L)) (Real.exp (v * L)) ∧ w.1 * w.2 = 2 * u w + 1) →
        (∑ w ∈ F, candidateCoefficient c L q r jStar (u w) * roughTestLogarithmicProxy γ L S w.2) ≤
          (shiftedSieveRatioConstant * M * Real.log (v / a) + ε) *
            candidateCoefficientWindowMass c L q r jStar / L := by
  obtain ⟨J, hJ⟩ := exists_candidate_unbalanced_rough_logarithmic_proxy_upper
    hZ hc hr hq0 hq1 hcenter ha hav hvhalf
  refine ⟨J, ?_⟩
  intro S hS jStar hj ε hε
  let R := shiftedSieveRatioConstant * Real.log (v / a)
  let η := ε / (2 * (|R| + 1))
  have hη : 0 < η ∧ R * η ≤ ε / 2 := half_error_density_slack hε
  filter_upwards [hJ jStar hj (M + η) (by positivity) (ε / 2) (by positivity),
    eventually_cofactor_rough_test_coefficient_upper hγ ha hav hvγ
      (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 33) hS hdensity hη.1,
    eventually_gt_atTop (0 : ℝ)] with L hbound hcoef hL
  intro F u hdata
  have hb := hbound γ S F u hdata (by
    intro w hw
    obtain ⟨huw, hpw, hprod⟩ := hdata w hw
    obtain ⟨hm, hlo, hhi⟩ := arithmetic_window_cofactor_product_bounds hL.le huw hprod
    exact hcoef w.1 w.2 hpw hm hlo hhi)
  have hX : 0 ≤ candidateCoefficientWindowMass c L q r jStar := by
    apply sum_nonneg
    intro n hn
    exact candidate_coefficient_nonneg c L hq0 r jStar n
  apply hb.trans
  apply div_le_div_of_nonneg_right _ hL.le
  apply mul_le_mul_of_nonneg_right _ hX
  dsimp [R] at hη
  nlinarith [hη.2]

theorem exists_candidate_unbalanced_rough_finite_bins_upper_uniform_precision
    {ι : Type*} [Fintype ι]
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q : ℝ} {r : ℕ}
    {γ a v M : ι → ℝ}
    (hc : 0 < c) (hr : 0 < r) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcenter : (11 / 5 : ℝ) * (r : ℝ) * c = 1)
    (hγ : ∀ i, 0 < γ i) (ha : ∀ i, 0 < a i) (hav : ∀ i, a i ≤ v i)
    (hvhalf : ∀ i, v i < 1 / 2) (hvγ : ∀ i, v i < 1 - γ i)
    (hM : ∀ i, 0 ≤ M i)
    (hdensity : ∀ i, ∀ α ∈ Set.Icc (a i) (v i), buchstabDensity (γ i) (1 - α) ≤ M i) :
    ∃ J : ℕ, ∀ S : ℝ, 0 ≤ S → ∀ jStar : ℕ, J < jStar → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ L : ℝ in atTop,
        ∀ (F : ι → Finset (ℕ × ℕ)) (u : ι → ℕ × ℕ → ℕ),
        (∀ i, ∀ w ∈ F i, u i w ∈ arithmeticProductWindow 1 (Real.exp L) ∧
          w.1 ∈ primeBand (Real.exp (a i * L)) (Real.exp (v i * L)) ∧
          w.1 * w.2 = 2 * u i w + 1) →
        (∑ i, ∑ w ∈ F i, candidateCoefficient c L q r jStar (u i w) *
          roughTestLogarithmicProxy (γ i) L S w.2) ≤
          (shiftedSieveRatioConstant * (∑ i, M i * Real.log (v i / a i)) + ε) *
            candidateCoefficientWindowMass c L q r jStar / L := by
  classical
  have hbins := fun i => exists_candidate_unbalanced_rough_bin_upper_uniform_precision
    hZ hc hr hq0 hq1 hcenter (hγ i) (ha i) (hav i) (hvhalf i) (hvγ i)
    (hM i) (hdensity i)
  choose Js hJs using hbins
  refine ⟨Finset.univ.sup Js, ?_⟩
  intro S hS jStar hj ε hε
  let δ := ε / ((Fintype.card ι : ℝ) + 1)
  have hden : 0 < (Fintype.card ι : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hδeq : ((Fintype.card ι : ℝ) + 1) * δ = ε := by
    dsimp [δ]
    field_simp
  have hδerror : (Fintype.card ι : ℝ) * δ ≤ ε := by nlinarith
  have hbinEvent := fun i => hJs i S hS jStar
    (lt_of_le_of_lt (Finset.le_sup (Finset.mem_univ i)) hj) δ hδ
  have hEvent := Filter.eventually_all.mpr hbinEvent
  filter_upwards [hEvent, eventually_gt_atTop (0 : ℝ)] with L hbound hL
  intro F u hdata
  have hX : 0 ≤ candidateCoefficientWindowMass c L q r jStar := by
    apply sum_nonneg
    intro n hn
    exact candidate_coefficient_nonneg c L hq0 r jStar n
  have hsum :
      (∑ i, (shiftedSieveRatioConstant * M i * Real.log (v i / a i) + δ)) =
        shiftedSieveRatioConstant * (∑ i, M i * Real.log (v i / a i)) +
          (Fintype.card ι : ℝ) * δ := by
    simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
    rw [mul_sum]
    congr 1
    apply sum_congr rfl
    intro i hi
    ring
  calc
    (∑ i, ∑ w ∈ F i, candidateCoefficient c L q r jStar (u i w) *
        roughTestLogarithmicProxy (γ i) L S w.2) ≤
        ∑ i, (shiftedSieveRatioConstant * M i * Real.log (v i / a i) + δ) *
          candidateCoefficientWindowMass c L q r jStar / L := by
      apply sum_le_sum
      intro i hi
      exact hbound i (F i) (u i) (hdata i)
    _ = (shiftedSieveRatioConstant * (∑ i, M i * Real.log (v i / a i)) +
          (Fintype.card ι : ℝ) * δ) * candidateCoefficientWindowMass c L q r jStar / L := by
      rw [← sum_div, ← sum_mul, hsum]
    _ ≤ (shiftedSieveRatioConstant * (∑ i, M i * Real.log (v i / a i)) + ε) *
          candidateCoefficientWindowMass c L q r jStar / L := by
      apply div_le_div_of_nonneg_right _ hL.le
      exact mul_le_mul_of_nonneg_right (by linarith [hδerror]) hX

theorem exists_candidate_positive_proxy_gap_uniform_precision
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q : ℝ} {r : ℕ}
    (hc : 0 < c) (hr : 0 < r) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcenter : (11 / 5 : ℝ) * (r : ℝ) * c = 1) :
    ∃ κ qCut b : ℝ, ∃ h N : ℕ, ∃ M : Fin N → ℝ,
      0 < κ ∧ κ ≤ 1 / 50 ∧ qCut = 1 / 2 - κ ∧ 0 < qCut ∧ qCut < 1 / 2 ∧
      0 < b ∧ b < qCut ∧ 1 ≤ h ∧ Even h ∧ b * (4 * (h : ℝ) + 2) < 1 / 2 ∧
      0 < N ∧
      (∀ i : Fin N,
        reciprocalGrid b qCut N (i : ℕ) < reciprocalGrid b qCut N ((i : ℕ) + 1) ∧
        0 < M i ∧ ∀ α ∈ Set.Icc (reciprocalGrid b qCut N (i : ℕ))
          (reciprocalGrid b qCut N ((i : ℕ) + 1)),
          buchstabDensity (reciprocalGrid b qCut N (i : ℕ)) (1 - α) ≤ M i) ∧
      (∑ i : Fin N, M i * Real.log
        (reciprocalGrid b qCut N ((i : ℕ) + 1) / reciprocalGrid b qCut N (i : ℕ))) ≤
          buchstabDensity b 1 - 1 + 1 / 16 ∧
      ∃ J : ℕ, ∀ S : ℝ, 0 ≤ S → ∀ jStar : ℕ, J < jStar → ∀ᶠ L : ℝ in atTop,
        ∀ (F : Fin N → Finset (ℕ × ℕ)) (u : Fin N → ℕ × ℕ → ℕ)
          (B : Finset (ℕ × ℕ)) (uB : ℕ × ℕ → ℕ),
        (∀ i, ∀ w ∈ F i, u i w ∈ arithmeticProductWindow 1 (Real.exp L) ∧
          w.1 ∈ primeBand (Real.exp (reciprocalGrid b qCut N (i : ℕ) * L))
            (Real.exp (reciprocalGrid b qCut N ((i : ℕ) + 1) * L)) ∧
          w.1 * w.2 = 2 * u i w + 1) →
        (∀ w ∈ B, balancedPairWindow κ L w ∧
          uB w ∈ arithmeticProductWindow 1 (Real.exp L) ∧ w.1 * w.2 = 2 * uB w + 1) →
        (shiftedSieveRatioConstant / 3) * candidateCoefficientWindowMass c L q r jStar / L ≤
          candidateShiftedRoughMass c L q r jStar (Real.exp (b * L)) -
            (∑ i : Fin N, ∑ w ∈ F i, candidateCoefficient c L q r jStar (u i w) *
              roughTestLogarithmicProxy (reciprocalGrid b qCut N (i : ℕ)) L S w.2) -
            ∑ w ∈ B, candidateCoefficient c L q r jStar (uB w) *
              primeLogarithmicProxy L S w.1 * primeLogarithmicProxy L S w.2 := by
  obtain ⟨Kpre, hKpre, hpre⟩ := exists_candidate_shifted_rough_mass_density_lower hZ
  obtain ⟨Cbal, hCbal, Jbal, hbal⟩ :=
    exists_candidate_balanced_logarithmic_prime_proxy_bound hc hr hq0 hq1 hcenter
  obtain ⟨κ, qCut, b, h, N, M, hκ, hκup, hqCut, hqCut0, hqCuthalf, hb, hbq,
    hh, heven, hlevel, hκloss, hN, hbins, hmesh, hmargin⟩ :=
      exists_positive_buchstab_mesh_parameters Kpre Cbal hCbal.le
  have hstart (i : Fin N) : 0 < reciprocalGrid b qCut N (i : ℕ) :=
    hb.trans_le (reciprocal_grid_mem hbq.le hN (Nat.le_of_lt i.isLt)).1
  have hend (i : Fin N) : reciprocalGrid b qCut N ((i : ℕ) + 1) < 1 / 2 :=
    (reciprocal_grid_mem hbq.le hN (Nat.succ_le_of_lt i.isLt)).2.trans_lt hqCuthalf
  have hgap (i : Fin N) : reciprocalGrid b qCut N ((i : ℕ) + 1) <
      1 - reciprocalGrid b qCut N (i : ℕ) := by
    have hs := (reciprocal_grid_mem hbq.le hN (Nat.le_of_lt i.isLt)).2
    have he := hend i
    linarith
  refine ⟨κ, qCut, b, h, N, M, hκ, hκup, hqCut,
    hqCut0, hqCuthalf, hb, hbq, hh, heven, hlevel, hN, hbins, hmesh, ?_⟩
  obtain ⟨Junbal, hunbal⟩ := exists_candidate_unbalanced_rough_finite_bins_upper_uniform_precision
    hZ hc hr hq0 hq1 hcenter hstart hstart (fun i => (hbins i).1.le) hend hgap
      (fun i => (hbins i).2.1.le) (fun i => (hbins i).2.2)
  obtain ⟨Jpre, hprebound⟩ := hpre c q b r h hc hr hq0 hq1 hcenter hb hh heven hlevel
  refine ⟨max Jpre (max Junbal Jbal), ?_⟩
  intro S hS jStar hj
  have hjpre : Jpre < jStar := lt_of_le_of_lt (le_max_left _ _) hj
  have hjunbal : Junbal < jStar := lt_of_le_of_lt
    ((le_max_left Junbal Jbal).trans (le_max_right Jpre _)) hj
  have hjbal : Jbal < jStar := lt_of_le_of_lt
    ((le_max_right Junbal Jbal).trans (le_max_right Jpre _)) hj
  have hd : 0 < shiftedSieveRatioConstant :=
    lt_of_lt_of_le zero_lt_one shifted_sieve_ratio_constant_bounds.1
  have hε : 0 < shiftedSieveRatioConstant / 24 := by positivity
  filter_upwards [hprebound jStar hjpre _ hε, hunbal S hS jStar hjunbal _ hε,
    hbal S hS, eventually_proxy_gap_reciprocal_bound (C := Cbal) hd] with L hpreL hunbalL hbalL htail
  intro F u B uB hF hB
  have hX : 0 ≤ candidateCoefficientWindowMass c L q r jStar := by
    apply sum_nonneg
    intro n hn
    exact candidate_coefficient_nonneg c L hq0 r jStar n
  have hu := hunbalL F u hF
  have hbL := hbalL κ hκ.le hκup jStar hjbal B uB
    (fun w hw => (hB w hw).1) (fun w hw => (hB w hw).2.2)
  have hm : shiftedSieveRatioConstant / 2 <
      (shiftedSieveRatioConstant * Mertens.primeProductLimitConstant / b) *
        (1 - Kpre * Real.exp (-(h : ℝ))) -
      shiftedSieveRatioConstant *
        (∑ i : Fin N, M i * Real.log
          (reciprocalGrid b qCut N ((i : ℕ) + 1) / reciprocalGrid b qCut N (i : ℕ))) -
      Cbal * κ := by
    convert hmargin using 1
    ring
  exact candidate_proxy_gap_arithmetic hd htail.1 hX htail.2 hm hpreL hu hbL

theorem candidate_shifted_prime_fraction_of_fixed_slot_error_bound
    (hZ : PrimitiveZeroFreeRightOf (23 / 24))
    {c q : ℝ} {r : ℕ} (hc : 0<c) (hr : 0<r) (hq0 : 0≤q) (hq1 : q<1)
    (hcenter : (11/5:ℝ)*(r:ℝ)*c=1)
    (hR : ∀ (κ b : ℝ) (N : ℕ), 0<κ → κ≤1/50 → 0<b → b<1/2-κ → 0<N →
      ∃ J : ℕ, ∀ jStar : ℕ, J<jStar → ∃ S : ℝ, 0≤S ∧ ∀ᶠ L : ℝ in atTop,
        |ambientBuchstabMeshError (arithmeticProductWindow 1 (Real.exp L))
          (candidateCoefficient c L q r jStar) b (1/2-κ) κ L S N| ≤
            ((N:ℝ)+1)*candidateCoefficientWindowMass c L q r jStar*L^(-2:ℝ)) :
    ∃ J : ℕ, ∀ jStar : ℕ, J<jStar → ∀ᶠ L : ℝ in atTop,
      (shiftedSieveRatioConstant/4)*candidateCoefficientWindowMass c L q r jStar/L ≤
        ∑ u ∈ (arithmeticProductWindow 1 (Real.exp L)).filter (fun u => (2*u+1).Prime),
          candidateCoefficient c L q r jStar u := by
  classical
  obtain ⟨κ,qCut,b,h,N,M,hκ,hκmax,hqCut,hqCut0,hqCuthalf,hb,hbq,hh,heven,hlevel,hN,hbins,hmesh,hgap⟩ :=
    exists_candidate_positive_proxy_gap_uniform_precision hZ hc hr hq0 hq1 hcenter
  subst qCut
  obtain ⟨Jerr,herr⟩ := hR κ b N hκ hκmax hb hbq hN
  obtain ⟨Jgap,hgapAll⟩ := hgap
  refine ⟨max Jerr Jgap,?_⟩
  intro jStar hj
  have hjerr := lt_of_le_of_lt (le_max_left Jerr Jgap) hj
  have hjgap := lt_of_le_of_lt (le_max_right Jerr Jgap) hj
  obtain ⟨S,hS,herrS⟩ := herr jStar hjerr
  have hratio : 0<shiftedSieveRatioConstant :=
    lt_of_lt_of_le zero_lt_one shifted_sieve_ratio_constant_bounds.1
  filter_upwards [herrS,hgapAll S hS jStar hjgap,
    eventually_shifted_ambient_mesh_prime_lower hκ hκmax hbq.le hN,
    eventually_gt_atTop (0:ℝ),eventually_ge_atTop (12*((N:ℝ)+1)/shiftedSieveRatioConstant)]
    with L herror hpositive hlower hL hLbig
  let T := arithmeticProductWindow 1 (Real.exp L)
  let μ := candidateCoefficient c L q r jStar
  let X := candidateCoefficientWindowMass c L q r jStar
  let F : Fin N → Finset (ℕ×ℕ) := fun i => shiftedPrimeBandPairs T
    (Real.exp (reciprocalGrid b (1/2-κ) N (i:ℕ)*L))
    (Real.exp (reciprocalGrid b (1/2-κ) N ((i:ℕ)+1)*L))
  let B := shiftedBalancedPairs T κ L
  have hμ : ∀u∈T,0≤μ u := fun u _ => candidate_coefficient_nonneg c L hq0 r jStar u
  have hX : 0≤X := sum_nonneg hμ
  have hpos := hpositive F (fun _ => shiftedPairIndex) B shiftedPairIndex
    (fun i v hv => shifted_prime_band_pair_data T _ _ hv)
    (fun v hv => by
      have hd := shifted_balanced_pair_data T κ L hv
      exact ⟨hd.2.1,hd.1,hd.2.2⟩)
  have hlo := hlower μ S hμ
  let E := ambientBuchstabMeshError T μ b (1/2-κ) κ L S N
  let U := ambientBuchstabUnbalancedProxy T μ b (1/2-κ) L S N
  let BP := ambientBuchstabBalancedProxy T μ κ L S
  let R := candidateShiftedRoughMass c L q r jStar (Real.exp (b*L))
  change (shiftedSieveRatioConstant/3)*X/L ≤ R-U-BP at hpos
  change R-U-BP-E ≤ ∑ u∈(shiftedRoughSet T (Real.exp (b*L))).filter
    (fun u=>(2*u+1).Prime),μ u at hlo
  have hscalar : ((N:ℝ)+1)*L^(-2:ℝ) ≤ (shiftedSieveRatioConstant/12)/L := by
    rw [Real.rpow_neg hL.le,Real.rpow_two,← div_eq_mul_inv]
    have hbig := (div_le_iff₀ hratio).mp hLbig
    apply (div_le_iff₀ (sq_pos_of_pos hL)).mpr
    have heq : ((shiftedSieveRatioConstant/12)/L)*L^2=shiftedSieveRatioConstant*L/12 := by
      field_simp
    rw [heq]
    linarith
  have hE : E ≤ (shiftedSieveRatioConstant/12)*X/L := by
    have he := (le_abs_self E).trans herror
    have hh := mul_le_mul_of_nonneg_left hscalar hX
    calc
      E ≤ ((N:ℝ)+1)*X*L^(-2:ℝ) := he
      _ = X*(((N:ℝ)+1)*L^(-2:ℝ)) := by ring
      _ ≤ X*((shiftedSieveRatioConstant/12)/L) := hh
      _ = _ := by ring
  have hprime : (shiftedSieveRatioConstant/4)*X/L ≤
      ∑ u∈(shiftedRoughSet T (Real.exp (b*L))).filter (fun u=>(2*u+1).Prime),μ u := by
    have heq : (shiftedSieveRatioConstant/4)*X/L=
      (shiftedSieveRatioConstant/3)*X/L-(shiftedSieveRatioConstant/12)*X/L := by ring
    rw [heq]
    linarith
  apply hprime.trans
  apply sum_le_sum_of_subset_of_nonneg
  · intro u hu
    exact mem_filter.mpr ⟨(mem_shifted_rough_set_iff T _ u).mp (mem_filter.mp hu).1 |>.1,
      (mem_filter.mp hu).2⟩
  · intro u hu hnot
    exact hμ u (mem_filter.mp hu).1

theorem candidate_shifted_prime_mass_supply_of_half_fixed_slot_replacement
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) (hR : CandidateHalfFixedSlotReplacement) :
    CandidateShiftedPrimeMassSupply := by
  apply candidate_shifted_prime_mass_supply_of_half_positive_fraction
  intro c r hc hr hcenter
  obtain ⟨J, hJ⟩ := candidate_shifted_prime_fraction_of_fixed_slot_error_bound
    hZ hc (by omega : 0 < r) (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1) hcenter (hR c r hc hr hcenter)
  refine ⟨J, ?_⟩
  intro jStar hj
  refine ⟨shiftedSieveRatioConstant/4, ?_, hJ jStar hj⟩
  have hratio : 0 < shiftedSieveRatioConstant :=
    lt_of_lt_of_le zero_lt_one shifted_sieve_ratio_constant_bounds.1
  positivity

theorem target_of_candidate_half_fixed_slot_replacement
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) (hR : CandidateHalfFixedSlotReplacement) :
    fcTypeOfName% "Erdos1057.erdos_1057" :=
  target_of_candidate_prime_mass_and_zero_free
    (candidate_shifted_prime_mass_supply_of_half_fixed_slot_replacement hZ hR) hZ

theorem target_of_candidate_half_fixed_slot_components
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) (hR : CandidateHalfFixedSlotComponentBounds) :
    fcTypeOfName% "Erdos1057.erdos_1057" :=
  target_of_candidate_half_fixed_slot_replacement hZ
    (candidate_half_fixed_slot_replacement_of_component_bounds hR)

theorem target_of_candidate_half_active_blocks
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) (hB : CandidateHalfActiveBlockBounds) :
    fcTypeOfName% "Erdos1057.erdos_1057" :=
  target_of_candidate_half_fixed_slot_components hZ
    (candidate_half_components_of_active_blocks hB)

theorem target_of_actual_zero_free_and_candidate_half_active_blocks
    (hB : CandidateHalfActiveBlockBounds) : fcTypeOfName% "Erdos1057.erdos_1057" :=
  target_of_candidate_half_active_blocks actual_zero_free hB

end Bounty.WeakZeroFree
