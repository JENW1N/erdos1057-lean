import WeakCandidateTarget

/-! Weaker-zero-free companions for the prime-memory and Mellin estimate chains. -/

open Finset Filter
open scoped Topology BigOperators Classical
universe u v
namespace Bounty.WeakZeroFree

/-- The endpoint correction is smaller than the same lower-endpoint profile. -/
theorem reciprocal_prime_endpoint_error_absorbed {q x : ℝ}
    (hq : 1 ≤ q) (hx : 2 ≤ x) :
    2 / x ≤ 2 * x ^ (-(1 : ℝ) / 96) * (1 + Real.log q / Real.log x) := by
  have hx1 : 1 ≤ x := by linarith
  have hp : 1 / x ≤ x ^ (-(1 : ℝ) / 96) := by
    simpa only [Real.rpow_neg_one, one_div] using
      (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (-1 : ℝ) ≤ -(1 : ℝ) / 96))
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hratio : 1 ≤ 1 + Real.log q / Real.log x := le_add_of_nonneg_right (div_nonneg hlq hlx)
  have hpow : 0 ≤ x ^ (-(1 : ℝ) / 96) := Real.rpow_nonneg (by linarith) _
  have hh := mul_le_mul_of_nonneg_left hratio hpow
  have he : 2 / x = 2 * (1 / x) := by ring
  rw [he]
  nlinarith

/-- The same uniform power-saving estimate for the real convention `[x,y)`. -/
theorem reciprocal_prime_closed_open_bound_of_zero_free
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ), 0 < q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ x y : ℝ, 2 ≤ x → x ≤ y →
          ‖∑ p ∈ (Finset.Ico ⌈x⌉₊ ⌈y⌉₊).filter Nat.Prime,
            (1 / (p : ℝ)) • χ (p : ZMod q)‖ ≤
            C * x ^ (-(1 : ℝ) / 96) * (1 + Real.log q / Real.log x) := by
  obtain ⟨C, hC, hbound⟩ := reciprocal_prime_interval_bound_of_zero_free hZ
  refine ⟨C + 2, by positivity, ?_⟩
  intro q hq χ hχ x y hx hxy
  have hb := hbound q hq χ hχ x y hx hxy
  have he := (reciprocal_prime_endpoint_difference_le χ (by linarith : 0 < x) hxy).trans
    (reciprocal_prime_endpoint_error_absorbed (q := (q : ℝ)) (by exact_mod_cast hq) hx)
  have hh := norm_le_norm_sub_add
    (∑ p ∈ (Finset.Ico ⌈x⌉₊ ⌈y⌉₊).filter Nat.Prime, (1 / (p : ℝ)) • χ (p : ZMod q))
    (∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, (1 / (p : ℝ)) • χ (p : ZMod q))
  nlinarith

/-- For cell vectors `conj(χ)`, their off-diagonal product is `χ * conj(ψ)`.
Its interval cancellation follows from distinct primitive indices, without
assuming nonprincipality of that product. -/
theorem primitive_character_correlation_closed_open_bound
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q r : ℕ), 0 < q → 0 < r →
      ∀ (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r),
        χ.IsPrimitive → ψ.IsPrimitive →
        (⟨q, χ⟩ : (n : ℕ) × DirichletCharacter ℂ n) ≠ ⟨r, ψ⟩ →
        ∀ x y : ℝ, 2 ≤ x → x ≤ y →
          ‖∑ p ∈ (Finset.Ico ⌈x⌉₊ ⌈y⌉₊).filter Nat.Prime,
            (1 / (p : ℝ)) • (χ (p : ZMod q) * star (ψ (p : ZMod r)))‖ ≤
            C * x ^ (-(1 : ℝ) / 96) *
              (1 + Real.log (q * r : ℕ) / Real.log x) := by
  obtain ⟨C, hC, hbound⟩ := reciprocal_prime_closed_open_bound_of_zero_free hZ
  refine ⟨C, hC, ?_⟩
  intro q r hq hr χ ψ hχ hψ hne x y hx hxy
  have hn := primitive_product_level_mul_star_ne_one χ ψ hq hr hχ hψ hne
  have hb := hbound (q * r) (Nat.mul_pos hq hr)
    (χ.changeLevel (Nat.dvd_mul_right q r) * star (ψ.changeLevel (Nat.dvd_mul_left r q)))
    hn x y hx hxy
  simpa only [product_level_mul_star_nat_apply] using hb

theorem prime_tuple_cell_bound_of_zero_free (hZ : PrimitiveZeroFreeRightOf (23 / 24)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ), 0 < q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ {I : Type*} [Fintype I] [DecidableEq I],
      ∀ (P : I → Finset ℕ) (V : I → ℝ) (i : I),
      (∀ j, 0 < V j) → (∀ j p, p ∈ P j → 0 < p) →
      (∀ j, ∑ p ∈ P j, 1 / (p : ℝ) = V j) →
      ∀ a b : ℝ, P i = primeBand a b → 2 ≤ a → 0 ≤ b →
      ∀ U W : ℝ, 0 ≤ U → 0 ≤ W →
        ‖∑ x : (∀ j, P j), (finiteProductWeight (physicalLabelLaw V) x : ℂ) *
          (if U < ((∏ j, (x j).val : ℕ) : ℝ) ∧ ((∏ j, (x j).val : ℕ) : ℝ) ≤ W
          then χ ((∏ j, (x j).val : ℕ) : ZMod q) else 0)‖ ≤
            (C / V i) * a ^ (-(1 : ℝ) / 96) * (1 + Real.log q / Real.log a) := by
  obtain ⟨C, hC, hbound⟩ := reciprocal_prime_band_product_interval_bound hZ
  refine ⟨C, hC, ?_⟩
  intro q hq χ hχ I _ _ P V i hV hp hmass a b hPi ha hb U W hU hW
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqR
  have hla : 0 < Real.log a := Real.log_pos (by linarith)
  have hB : 0 ≤ C * a ^ (-(1 : ℝ) / 96) * (1 + Real.log q / Real.log a) := by positivity
  have h := prime_tuple_cell_norm_le P V i hV hp hmass χ U W hB (fun c hc => by
    rw [hPi]
    simpa only [Nat.cast_mul] using
      hbound q hq χ hχ a b (c : ℝ) U W ha hb (by exact_mod_cast hc) hU hW)
  calc
    _ ≤ (C * a ^ (-(1 : ℝ) / 96) * (1 + Real.log q / Real.log a)) / V i := h
    _ = _ := by ring

theorem prime_tuple_cell_correlation_bound (hZ : PrimitiveZeroFreeRightOf (23 / 24)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q r : ℕ), 0 < q → 0 < r →
      ∀ (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r),
      χ.IsPrimitive → ψ.IsPrimitive →
      (⟨q, χ⟩ : (n : ℕ) × DirichletCharacter ℂ n) ≠ ⟨r, ψ⟩ →
      ∀ {I : Type*} [Fintype I] [DecidableEq I],
      ∀ (P : I → Finset ℕ) (V : I → ℝ) (i : I),
      (∀ j, 0 < V j) → (∀ j p, p ∈ P j → 0 < p) →
      (∀ j, ∑ p ∈ P j, 1 / (p : ℝ) = V j) →
      ∀ a b : ℝ, P i = primeBand a b → 2 ≤ a → 0 ≤ b →
      ∀ U W : ℝ, 0 ≤ U → 0 ≤ W →
        ‖∑ x : (∀ j, P j), (finiteProductWeight (physicalLabelLaw V) x : ℂ) *
          (if U < ((∏ j, (x j).val : ℕ) : ℝ) ∧ ((∏ j, (x j).val : ℕ) : ℝ) ≤ W
          then χ ((∏ j, (x j).val : ℕ) : ZMod q) *
            star (ψ ((∏ j, (x j).val : ℕ) : ZMod r)) else 0)‖ ≤
            (C / V i) * a ^ (-(1 : ℝ) / 96) * (1 + Real.log (q * r : ℕ) / Real.log a) := by
  obtain ⟨C, hC, hbound⟩ := prime_tuple_cell_bound_of_zero_free hZ
  refine ⟨C, hC, ?_⟩
  intro q r hq hr χ ψ hχ hψ hne I _ _ P V i hV hp hmass a b hPi ha hb U W hU hW
  have hn := primitive_product_level_mul_star_ne_one χ ψ hq hr hχ hψ hne
  have h := hbound (q * r) (Nat.mul_pos hq hr)
    (χ.changeLevel (Nat.dvd_mul_right q r) * star (ψ.changeLevel (Nat.dvd_mul_left r q)))
    hn P V i hV hp hmass a b hPi ha hb U W hU hW
  simpa only [product_level_mul_star_nat_apply] using h

theorem prime_tuple_log_cell_correlation_bound (hZ : PrimitiveZeroFreeRightOf (23 / 24)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q r : ℕ), 0 < q → 0 < r →
      ∀ (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r),
      χ.IsPrimitive → ψ.IsPrimitive →
      (⟨q, χ⟩ : (n : ℕ) × DirichletCharacter ℂ n) ≠ ⟨r, ψ⟩ →
      ∀ {I : Type*} [Fintype I] [DecidableEq I],
      ∀ (P : I → Finset ℕ) (V : I → ℝ) (i : I),
      (∀ j, 0 < V j) → (∀ j p, p ∈ P j → 0 < p) →
      (∀ j, ∑ p ∈ P j, 1 / (p : ℝ) = V j) →
      ∀ a b : ℝ, P i = primeBand a b → 2 ≤ a → 0 ≤ b →
      ∀ h : ℝ, 0 < h → ∀ d : ℤ,
        ‖∑ x : (∀ j, P j),
          if upperLogCell h (Real.log (∏ j, (x j).val : ℕ)) = d then
            (finiteProductWeight (physicalLabelLaw V) x : ℂ) *
              χ ((∏ j, (x j).val : ℕ) : ZMod q) *
              star (ψ ((∏ j, (x j).val : ℕ) : ZMod r)) else 0‖ ≤
            (C / V i) * a ^ (-(1 : ℝ) / 96) * (1 + Real.log (q * r : ℕ) / Real.log a) := by
  obtain ⟨C, hC, hbound⟩ := prime_tuple_cell_correlation_bound hZ
  refine ⟨C, hC, ?_⟩
  intro q r hq hr χ ψ hχ hψ hne I _ _ P V i hV hp hmass a b hPi ha hb h hh d
  let U := Real.exp (((d : ℝ) - 1) * h)
  let W := Real.exp ((d : ℝ) * h)
  have hbnd := hbound q r hq hr χ ψ hχ hψ hne P V i hV hp hmass a b hPi ha hb U W
    (Real.exp_pos _).le (Real.exp_pos _).le
  have heq (x : ∀ j, P j) :
      (if upperLogCell h (Real.log (∏ j, (x j).val : ℕ)) = d then
        (finiteProductWeight (physicalLabelLaw V) x : ℂ) *
          χ ((∏ j, (x j).val : ℕ) : ZMod q) *
          star (ψ ((∏ j, (x j).val : ℕ) : ZMod r)) else 0) =
      (finiteProductWeight (physicalLabelLaw V) x : ℂ) *
        (if U < ((∏ j, (x j).val : ℕ) : ℝ) ∧ ((∏ j, (x j).val : ℕ) : ℝ) ≤ W
        then χ ((∏ j, (x j).val : ℕ) : ZMod q) *
          star (ψ ((∏ j, (x j).val : ℕ) : ZMod r)) else 0) := by
    have hn : 0 < ∏ j, (x j).val := Finset.prod_pos (fun j _ => hp j _ (x j).property)
    simp only [upper_log_cell_nat_eq_iff hh hn]
    change (if U < _ ∧ _ ≤ W then _ else _) = _
    split_ifs <;> simp only [mul_assoc, mul_zero]
  rw [Finset.sum_congr rfl (fun x _ => heq x)]
  exact hbnd

theorem prime_tuple_log_cell_kernel_energy (hZ : PrimitiveZeroFreeRightOf (23 / 24)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T : Type*} [Fintype T] (q : T → ℕ) (χ : (t : T) → DirichletCharacter ℂ (q t)),
      (∀ t, 0 < q t) → (∀ t, (χ t).IsPrimitive) →
      Function.Injective (fun t => (⟨q t, χ t⟩ : (n : ℕ) × DirichletCharacter ℂ n)) →
      ∀ Q : ℕ, 0 < Q → (∀ t, q t ≤ Q) →
      ∀ {I : Type*} [Fintype I] [DecidableEq I],
      ∀ (P : I → Finset ℕ) (V : I → ℝ) (i : I),
      (∀ j, 0 < V j) → (∀ j p, p ∈ P j → 0 < p) →
      (∀ j, ∑ p ∈ P j, 1 / (p : ℝ) = V j) →
      (∀ t j p, p ∈ P j → p.Coprime (q t)) →
      ∀ a b : ℝ, P i = primeBand a b → 2 ≤ a → 0 ≤ b →
      ∀ h ξ : ℝ, 0 < h → 0 < ξ → ∀ kept : Finset ℤ,
      (∀ d ∈ kept, ξ ≤ finiteCellMass (finiteProductWeight (physicalLabelLaw (P := P) V))
        (fun x => upperLogCell h (Real.log (∏ j, (x j).val : ℕ))) d) →
      (Fintype.card T - 1 : ℕ) *
        (((C / V i) * a ^ (-(1 : ℝ) / 96) *
          (1 + Real.log (Q * Q : ℕ) / Real.log a)) / ξ) ≤ 1 →
      ∀ f : (∀ j, P j) → ℂ,
        (∑ x, finiteProductWeight (physicalLabelLaw (P := P) V) x *
          ‖∑ y, (finiteProductWeight (physicalLabelLaw (P := P) V) y : ℂ) *
            finiteCellFrameKernel (finiteProductWeight (physicalLabelLaw (P := P) V))
              (fun z => upperLogCell h (Real.log (∏ j, (z j).val : ℕ))) kept
              (fun t z => star (χ t ((∏ j, (z j).val : ℕ) : ZMod (q t)))) x y * f y‖ ^ 2) ≤
        4 * ∑ x, finiteProductWeight (physicalLabelLaw (P := P) V) x * ‖f x‖ ^ 2 := by
  obtain ⟨C, hC, hbnd⟩ := prime_tuple_log_cell_correlation_bound hZ
  refine ⟨C, hC, ?_⟩
  intro T _ q χ hq hχ hinj Q hQ hqQ I _ _ P V i hV hp hmass hcop a b hPi ha hb h ξ hh hξ kept hkept hsmall f
  have hVi := hV i
  have ha0 : 0 < a := by linarith
  have hlog : 0 < Real.log a := Real.log_pos (by linarith)
  have hQ1 : (1 : ℝ) ≤ (Q * Q : ℕ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.ne_of_gt hQ) (Nat.ne_of_gt hQ))
  have hδ : 0 ≤ (C / V i) * a ^ (-(1 : ℝ) / 96) *
      (1 + Real.log (Q * Q : ℕ) / Real.log a) := by
    have := Real.log_nonneg hQ1
    positivity
  refine finite_cell_kernel_energy_of_raw_gram
    (finiteProductWeight (physicalLabelLaw (P := P) V)) ?_
    (fun z => upperLogCell h (Real.log (∏ j, (z j).val : ℕ))) kept hδ hξ hkept
    (fun t z => star (χ t ((∏ j, (z j).val : ℕ) : ZMod (q t)))) ?_ hsmall ?_ f
  · intro x
    exact Finset.prod_nonneg (fun j _ => physical_label_law_nonneg V (fun k => (hV k).le) j (x j))
  · intro t x _
    rw [norm_star]
    exact prime_tuple_character_norm_one P (χ t) (hcop t) x
  · intro d hd t s hts
    have hraw := hbnd (q t) (q s) (hq t) (hq s) (χ t) (χ s) (hχ t) (hχ s)
      (fun he => hts (hinj he)) P V i hV hp hmass a b hPi ha hb h hh d
    have hqprod : (0 : ℝ) < (q t * q s : ℕ) := by exact_mod_cast Nat.mul_pos (hq t) (hq s)
    have hprod : (q t * q s : ℕ) ≤ Q * Q := Nat.mul_le_mul (hqQ t) (hqQ s)
    have hlogs : Real.log (q t * q s : ℕ) ≤ Real.log (Q * Q : ℕ) :=
      Real.log_le_log hqprod (by exact_mod_cast hprod)
    have hmono : (C / V i) * a ^ (-(1 : ℝ) / 96) *
        (1 + Real.log (q t * q s : ℕ) / Real.log a) ≤
        (C / V i) * a ^ (-(1 : ℝ) / 96) *
        (1 + Real.log (Q * Q : ℕ) / Real.log a) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl (div_le_div_of_nonneg_right hlogs hlog.le)) (by positivity)
    simpa only [starRingEnd_apply, star_star] using hraw.trans hmono

theorem bounded_primitive_smallness (Q : ℕ) {V C a ξ : ℝ}
    (hV : 0 < V) (hC : 0 < C) (ha : 2 ≤ a) (hQ : 0 < Q) (hξ : 0 < ξ)
    (hsmall : (Q * Q - 1 : ℕ) *
      (((C / V) * a ^ (-(1 : ℝ) / 96) *
        (1 + Real.log (Q * Q : ℕ) / Real.log a)) / ξ) ≤ 1) :
    (Fintype.card (BoundedPrimitiveCharacter Q) - 1 : ℕ) *
      (((C / V) * a ^ (-(1 : ℝ) / 96) *
        (1 + Real.log (Q * Q : ℕ) / Real.log a)) / ξ) ≤ 1 := by
  have hlog : 0 < Real.log a := Real.log_pos (by linarith)
  have hQ1 : (1 : ℝ) ≤ (Q * Q : ℕ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.ne_of_gt hQ) (Nat.ne_of_gt hQ))
  have hδ : 0 ≤ ((C / V) * a ^ (-(1 : ℝ) / 96) *
      (1 + Real.log (Q * Q : ℕ) / Real.log a)) / ξ := by
    have := Real.log_nonneg hQ1
    positivity
  have hcard : (Fintype.card (BoundedPrimitiveCharacter Q) - 1 : ℕ) ≤ Q * Q - 1 :=
    Nat.sub_le_sub_right (bounded_primitive_character_card_le Q) 1
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hδ).trans hsmall

theorem prime_product_ideal_kernel_energy (hZ : PrimitiveZeroFreeRightOf (23 / 24)) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 0 < Q →
      ∀ {I : Type*} [Fintype I] [DecidableEq I],
      ∀ (P : I → Finset ℕ) (V : I → ℝ) (i : I),
      (∀ j, 0 < V j) →
      (∀ j p, p ∈ P j → p.Prime ∧ Q < p) →
      (∀ j, ∑ p ∈ P j, 1 / (p : ℝ) = V j) →
      ∀ a b : ℝ, P i = primeBand a b → 2 ≤ a → 0 ≤ b →
      ∀ h ξ : ℝ, 0 < h → 0 < ξ → ∀ kept : Finset ℤ,
      (∀ d ∈ kept, ξ ≤ finiteCellMass (finiteProductWeight (physicalLabelLaw (P := P) V))
        (fun x => upperLogCell h (Real.log (∏ j, (x j).val : ℕ))) d) →
      (Q * Q - 1 : ℕ) *
        (((C / V i) * a ^ (-(1 : ℝ) / 96) *
          (1 + Real.log (Q * Q : ℕ) / Real.log a)) / ξ) ≤ 1 →
      ∀ f : (∀ j, P j) → ℂ,
        (∑ x, finiteProductWeight (physicalLabelLaw V) x *
          ‖∑ y, (finiteProductWeight (physicalLabelLaw V) y : ℂ) *
            primeProductIdealKernel P V Q h kept x y * f y‖ ^ 2) ≤
        4 * ∑ x, finiteProductWeight (physicalLabelLaw V) x * ‖f x‖ ^ 2 := by
  obtain ⟨C, hC, hbnd⟩ := prime_tuple_log_cell_kernel_energy hZ
  refine ⟨C, hC, ?_⟩
  intro Q hQ I _ _ P V i hV hp hmass a b hPi ha hb h ξ hh hξ kept hkept hsmall f
  have hs := bounded_primitive_smallness Q (hV i) hC ha hQ hξ hsmall
  change _ ≤ _
  unfold primeProductIdealKernel
  have test := hbnd (T := BoundedPrimitiveCharacter Q) boundedPrimitiveModulus boundedPrimitiveValue
    bounded_primitive_modulus_pos bounded_primitive_value_primitive
    (bounded_primitive_character_injective Q) Q hQ bounded_primitive_modulus_le
    P V i hV (fun j p h => (hp j p h).1.pos) hmass
    (fun t j p h => prime_above_modulus_coprime (hp j p h).1
      (bounded_primitive_modulus_pos t) (bounded_primitive_modulus_le t) (hp j p h).2)
    a b hPi ha hb h ξ hh hξ kept hkept hs f
  exact test

theorem prime_family_log_cell_gram (hZ : PrimitiveZeroFreeRightOf (23 / 24)) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 0 < Q →
      ∀ {I : Type*} [Fintype I] [DecidableEq I],
      ∀ (P : I → Finset ℕ) (V : I → ℝ) (i : I),
      (∀ j, 0 < V j) → (∀ j p, p ∈ P j → 0 < p) →
      (∀ j, ∑ p ∈ P j, 1 / (p : ℝ) = V j) →
      ∀ a b : ℝ, P i = primeBand a b → 2 ≤ a → 0 ≤ b →
      ∀ h : ℝ, 0 < h → ∀ d : ℤ,
      ∀ t s : BoundedPrimitiveCharacter Q, t ≠ s →
        ‖∑ x : (∀ j, P j),
          if upperLogCell h (Real.log (∏ j, (x j).val : ℕ)) = d then
            (finiteProductWeight (physicalLabelLaw V) x : ℂ) *
              boundedPrimitiveValue t ((∏ j, (x j).val : ℕ) : ZMod (boundedPrimitiveModulus t)) *
              star (boundedPrimitiveValue s ((∏ j, (x j).val : ℕ) : ZMod (boundedPrimitiveModulus s))) else 0‖ ≤
            (C / V i) * a ^ (-(1 : ℝ) / 96) * (1 + Real.log (Q * Q : ℕ) / Real.log a) := by
  obtain ⟨C, hC, hbnd⟩ := prime_tuple_log_cell_correlation_bound hZ
  refine ⟨C, hC, ?_⟩
  intro Q hQ I _ _ P V i hV hp hmass a b hPi ha hb h hh d t s hts
  have hVi := hV i
  have hlog : 0 < Real.log a := Real.log_pos (by linarith)
  have hraw := hbnd (boundedPrimitiveModulus t) (boundedPrimitiveModulus s)
    (bounded_primitive_modulus_pos t) (bounded_primitive_modulus_pos s)
    (boundedPrimitiveValue t) (boundedPrimitiveValue s)
    (bounded_primitive_value_primitive t) (bounded_primitive_value_primitive s)
    (fun he => hts (bounded_primitive_character_injective Q he))
    P V i hV hp hmass a b hPi ha hb h hh d
  have hprod : boundedPrimitiveModulus t * boundedPrimitiveModulus s ≤ Q * Q :=
    Nat.mul_le_mul (bounded_primitive_modulus_le t) (bounded_primitive_modulus_le s)
  have hpos : (0 : ℝ) < (boundedPrimitiveModulus t * boundedPrimitiveModulus s : ℕ) := by
    exact_mod_cast Nat.mul_pos (bounded_primitive_modulus_pos t) (bounded_primitive_modulus_pos s)
  have hl := Real.log_le_log hpos (show ((boundedPrimitiveModulus t * boundedPrimitiveModulus s : ℕ) : ℝ) ≤ (Q * Q : ℕ) by exact_mod_cast hprod)
  apply hraw.trans
  exact mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (div_le_div_of_nonneg_right hl hlog.le)) (by positivity)

theorem prime_product_ideal_character_reproduction (hZ : PrimitiveZeroFreeRightOf (23 / 24)) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 0 < Q →
      ∀ {I : Type*} [Fintype I] [DecidableEq I],
      ∀ (P : I → Finset ℕ) (V : I → ℝ) (i : I),
      (∀ j, 0 < V j) →
      (∀ j p, p ∈ P j → p.Prime ∧ Q < p) →
      (∀ j, ∑ p ∈ P j, 1 / (p : ℝ) = V j) →
      ∀ a b : ℝ, P i = primeBand a b → 2 ≤ a → 0 ≤ b →
      ∀ h ξ : ℝ, 0 < h → 0 < ξ → ∀ kept : Finset ℤ,
      (∀ d ∈ kept, ξ ≤ finiteCellMass (finiteProductWeight (physicalLabelLaw (P := P) V))
        (fun x => upperLogCell h (Real.log (∏ j, (x j).val : ℕ))) d) →
      ∀ (t : BoundedPrimitiveCharacter Q) (y : ∀ j, P j),
      upperLogCell h (Real.log (∏ j, (y j).val : ℕ)) ∈ kept →
        ‖(∑ x, (finiteProductWeight (physicalLabelLaw V) x : ℂ) *
            primeProductIdealKernel P V Q h kept x y *
            boundedPrimitiveValue t ((∏ j, (x j).val : ℕ) : ZMod (boundedPrimitiveModulus t))) -
          boundedPrimitiveValue t ((∏ j, (y j).val : ℕ) : ZMod (boundedPrimitiveModulus t))‖ ≤
        (Q * Q : ℕ) * (((C / V i) * a ^ (-(1 : ℝ) / 96) *
          (1 + Real.log (Q * Q : ℕ) / Real.log a)) / ξ) := by
  obtain ⟨C, hC, hbnd⟩ := prime_family_log_cell_gram hZ
  refine ⟨C, hC, ?_⟩
  intro Q hQ I _ _ P V i hV hp hmass a b hPi ha hb h ξ hh hξ kept hkept t y hy
  let ψ : BoundedPrimitiveCharacter Q → (∀ j, P j) → ℂ := fun s x =>
    star (boundedPrimitiveValue s ((∏ j, (x j).val : ℕ) : ZMod (boundedPrimitiveModulus s)))
  let δ := (C / V i) * a ^ (-(1 : ℝ) / 96) * (1 + Real.log (Q * Q : ℕ) / Real.log a)
  have hVi := hV i
  have hlog : 0 < Real.log a := Real.log_pos (by linarith)
  have hQ1 : (1 : ℝ) ≤ (Q * Q : ℕ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.ne_of_gt hQ) (Nat.ne_of_gt hQ))
  have hδ : 0 ≤ δ := by
    have := Real.log_nonneg hQ1
    dsimp only [δ]
    positivity
  have hunit : ∀ s x, finiteProductWeight (physicalLabelLaw (P := P) V) x ≠ 0 → ‖ψ s x‖ = 1 := by
    intro s x _
    rw [show ψ s x = star (boundedPrimitiveValue s ((∏ j, (x j).val : ℕ) : ZMod (boundedPrimitiveModulus s))) from rfl, norm_star]
    exact prime_tuple_character_norm_one P (boundedPrimitiveValue s)
      (fun j p hj => prime_above_modulus_coprime (hp j p hj).1
        (bounded_primitive_modulus_pos s) (bounded_primitive_modulus_le s) (hp j p hj).2) x
  have hraw : ∀ d ∈ kept, ∀ s u, s ≠ u →
      ‖∑ x : (∀ j, P j), if upperLogCell h (Real.log (∏ j, (x j).val : ℕ)) = d then
        (finiteProductWeight (physicalLabelLaw V) x : ℂ) * (starRingEnd ℂ) (ψ s x) * ψ u x else 0‖ ≤ δ := by
    intro d _ s u hsu
    simpa only [ψ, starRingEnd_apply, star_star] using
      hbnd Q hQ P V i hV (fun j p hj => (hp j p hj).1.pos) hmass a b hPi ha hb h hh d s u hsu
  have hrec := finite_cell_character_reproduction
    (finiteProductWeight (physicalLabelLaw (P := P) V))
    (fun x => upperLogCell h (Real.log (∏ j, (x j).val : ℕ))) kept ψ hunit hδ hξ hkept hraw t y hy
    (fun s => by
      dsimp only [ψ]
      rw [norm_star]
      exact (boundedPrimitiveValue s).norm_le_one _)
  have hc : ((Fintype.card (BoundedPrimitiveCharacter Q) - 1 : ℕ) : ℝ) ≤ (Q * Q : ℕ) := by
    exact_mod_cast (Nat.sub_le (Fintype.card (BoundedPrimitiveCharacter Q)) 1).trans
      (bounded_primitive_character_card_le Q)
  have hout := hrec.trans (mul_le_mul_of_nonneg_right hc (div_nonneg hδ hξ.le))
  simpa only [primeProductIdealKernel, ψ, starRingEnd_apply, star_star, δ] using hout

/-- The logarithmic factor is bounded crudely by another `Q²`, leaving a
uniform exponential-times-power majorant. The exponent bounds may be any reals. -/
theorem prime_kernel_reproduction_error_majorant (c C q v x L : ℝ)
    (hc : 0 < c) (hC : 0 < C) (hL : 1 < L) (Q : ℕ) (V ξ a : ℝ)
    (hQ : 0 < Q) (hQbound : (Q : ℝ) ≤ L ^ q)
    (hV : L ^ (-v) ≤ V) (hξ : L ^ (-x) ≤ ξ) (ha : Real.exp (L ^ c) ≤ a) :
    ((Q * Q : ℕ) : ℝ) *
        (((C / V) * a ^ (-(1 : ℝ) / 96) *
          (1 + Real.log ((Q * Q : ℕ) : ℝ) / Real.log a)) / ξ) ≤
      (2 * C) * Real.exp (-(1 / 96 : ℝ) * L ^ c) * L ^ (4 * q + v + x) := by
  have hL0 : 0 < L := by linarith
  have hV0 : 0 < V := (Real.rpow_pos_of_pos hL0 (-v)).trans_le hV
  have hξ0 : 0 < ξ := (Real.rpow_pos_of_pos hL0 (-x)).trans_le hξ
  have ha0 : 0 < a := (Real.exp_pos _).trans_le ha
  have halog : 1 ≤ Real.log a := by
    have hh := Real.log_le_log (Real.exp_pos (L ^ c)) ha
    rw [Real.log_exp] at hh
    exact (Real.one_le_rpow hL.le hc.le).trans hh
  have hVinv : 1 / V ≤ L ^ v := by
    calc
      _ ≤ 1 / L ^ (-v) := one_div_le_one_div_of_le (Real.rpow_pos_of_pos hL0 (-v)) hV
      _ = _ := by rw [Real.rpow_neg hL0.le]; simp
  have hξinv : 1 / ξ ≤ L ^ x := by
    calc
      _ ≤ 1 / L ^ (-x) := one_div_le_one_div_of_le (Real.rpow_pos_of_pos hL0 (-x)) hξ
      _ = _ := by rw [Real.rpow_neg hL0.le]; simp
  have hadecay : a ^ (-(1 : ℝ) / 96) ≤ Real.exp (-(1 / 96 : ℝ) * L ^ c) := by
    calc
      _ ≤ (Real.exp (L ^ c)) ^ (-(1 : ℝ) / 96) :=
        Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) ha (by norm_num)
      _ = _ := by rw [← Real.exp_mul]; congr 1; ring
  have hQsq : (Q : ℝ) ^ 2 ≤ (L ^ q) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg Q) hQbound 2
  have hlogbound : 1 + Real.log ((Q * Q : ℕ) : ℝ) / Real.log a ≤ 2 * (L ^ q) ^ 2 :=
    (prime_kernel_log_factor_le Q a hQ halog).trans (by linarith)
  have hlog0 : 0 ≤ 1 + Real.log ((Q * Q : ℕ) : ℝ) / Real.log a := by
    have hQQ : (1 : ℝ) ≤ ((Q * Q : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ Q * Q by nlinarith)
    have hh := Real.log_nonneg hQQ
    positivity
  calc
    _ = (Q : ℝ) ^ 2 * C * (1 / V) * a ^ (-(1 : ℝ) / 96) *
        (1 + Real.log ((Q * Q : ℕ) : ℝ) / Real.log a) * (1 / ξ) := by
      push_cast
      ring
    _ ≤ (L ^ q) ^ 2 * C * L ^ v * Real.exp (-(1 / 96 : ℝ) * L ^ c) *
        (2 * (L ^ q) ^ 2) * L ^ x := by
      gcongr
    _ = _ := by
      rw [show 4 * q + v + x = q + q + v + q + q + x by ring]
      simp only [Real.rpow_add hL0]
      ring

/-- One threshold in `L` works for every allowed modulus bound, mass,
cell width, and prime-band starting point. -/
theorem eventually_prime_kernel_reproduction_error_small (c C q v x D : ℝ)
    (hc : 0 < c) (hC : 0 < C) :
    ∀ᶠ L : ℝ in atTop, ∀ (Q : ℕ) (V ξ a : ℝ), 0 < Q →
      (Q : ℝ) ≤ L ^ q → L ^ (-v) ≤ V → L ^ (-x) ≤ ξ → Real.exp (L ^ c) ≤ a →
      ((Q * Q : ℕ) : ℝ) *
        (((C / V) * a ^ (-(1 : ℝ) / 96) *
          (1 + Real.log ((Q * Q : ℕ) : ℝ) / Real.log a)) / ξ) ≤ L ^ (-D) := by
  filter_upwards [eventually_exp_neg_rpow_mul_rpow_le hc (by norm_num : (0 : ℝ) < 1 / 96)
      (4 * q + v + x + 1) D,
    eventually_gt_atTop (1 : ℝ), eventually_ge_atTop (2 * C)] with L hdecay hL hCL
  intro Q V ξ a hQ hQbound hV hξ ha
  have hL0 : 0 < L := by linarith
  calc
    _ ≤ (2 * C) * Real.exp (-(1 / 96 : ℝ) * L ^ c) * L ^ (4 * q + v + x) :=
      prime_kernel_reproduction_error_majorant c C q v x L hc hC hL Q V ξ a
        hQ hQbound hV hξ ha
    _ ≤ L * Real.exp (-(1 / 96 : ℝ) * L ^ c) * L ^ (4 * q + v + x) := by
      gcongr
    _ = Real.exp (-(1 / 96 : ℝ) * L ^ c) * L ^ (4 * q + v + x + 1) := by
      rw [Real.rpow_add hL0 (4 * q + v + x) 1, Real.rpow_one]
      ring
    _ ≤ L ^ (-D) := hdecay

theorem prime_product_ideal_dirichlet_reproduction (hZ : PrimitiveZeroFreeRightOf (23 / 24)) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 0 < Q →
      ∀ {I : Type*} [Fintype I] [DecidableEq I],
      ∀ (P : I → Finset ℕ) (V : I → ℝ) (i : I),
      (∀ j, 0 < V j) →
      (∀ j p, p ∈ P j → p.Prime ∧ Q < p) →
      (∀ j, ∑ p ∈ P j, 1 / (p : ℝ) = V j) →
      ∀ a b : ℝ, P i = primeBand a b → 2 ≤ a → 0 ≤ b →
      ∀ h ξ : ℝ, 0 < h → 0 < ξ → ∀ kept : Finset ℤ,
      (∀ d ∈ kept, ξ ≤ finiteCellMass (finiteProductWeight (physicalLabelLaw (P := P) V))
        (fun x => upperLogCell h (Real.log (∏ j, (x j).val : ℕ))) d) →
      ∀ q : ℕ, 0 < q → q ≤ Q → ∀ (χ : DirichletCharacter ℂ q) (y : ∀ j, P j),
      upperLogCell h (Real.log (∏ j, (y j).val : ℕ)) ∈ kept →
        ‖(∑ x, (finiteProductWeight (physicalLabelLaw V) x : ℂ) *
            primeProductIdealKernel P V Q h kept x y *
            χ ((∏ j, (x j).val : ℕ) : ZMod q)) -
          χ ((∏ j, (y j).val : ℕ) : ZMod q)‖ ≤
        (Q * Q : ℕ) * (((C / V i) * a ^ (-(1 : ℝ) / 96) *
          (1 + Real.log (Q * Q : ℕ) / Real.log a)) / ξ) := by
  obtain ⟨C, hC, hbnd⟩ := prime_product_ideal_character_reproduction hZ
  refine ⟨C, hC, ?_⟩
  intro Q hQ I _ _ P V i hV hp hmass a b hPi ha hb h ξ hh hξ kept hkept q hq hqQ χ y hy
  obtain ⟨t, _, ht⟩ := bounded_primitive_inducing hq hqQ χ
  have heval (x : ∀ j, P j) :
      boundedPrimitiveValue t ((∏ j, (x j).val : ℕ) : ZMod (boundedPrimitiveModulus t)) =
        χ ((∏ j, (x j).val : ℕ) : ZMod q) := by
    apply ht
    exact Nat.coprime_prod_left_iff.mpr (fun j _ =>
      prime_above_modulus_coprime (hp j (x j).val (x j).property).1 hq hqQ
        (hp j (x j).val (x j).property).2)
  simpa only [heval] using hbnd Q hQ P V i hV hp hmass a b hPi ha hb h ξ hh hξ kept hkept t y hy

noncomputable def primeKernelError (C : ℝ) (Q : ℕ) (V a ξ : ℝ) : ℝ :=
  (Q * Q : ℕ) * (((C / V) * a ^ (-(1 : ℝ) / 96) *
    (1 + Real.log (Q * Q : ℕ) / Real.log a)) / ξ)

theorem prime_kernel_error_nonneg {C V a ξ : ℝ} {Q : ℕ}
    (hC : 0 ≤ C) (hV : 0 ≤ V) (ha : 2 ≤ a) (hξ : 0 ≤ ξ) (hQ : 0 < Q) :
    0 ≤ primeKernelError C Q V a ξ := by
  have hlog : 0 < Real.log a := Real.log_pos (by linarith)
  have hq : (1 : ℝ) ≤ (Q * Q : ℕ) := by
    exact_mod_cast Nat.mul_pos hQ hQ
  have hlogq := Real.log_nonneg hq
  unfold primeKernelError
  positivity

theorem prime_major_arc_comparison (hZ : PrimitiveZeroFreeRightOf (23 / 24)) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 0 < Q →
    ∀ {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J],
    ∀ (P : I → Finset ℕ) (V : I → ℝ) (i : I)
      (R : J → Finset ℕ) (W : J → ℝ) (j : J),
    (∀ k, 0 < V k) → (∀ k, 0 < W k) →
    (∀ k p, p ∈ P k → p.Prime ∧ Q < p) →
    (∀ k p, p ∈ R k → p.Prime ∧ Q < p) →
    (∀ k, ∑ p ∈ P k, 1 / (p : ℝ) = V k) →
    (∀ k, ∑ p ∈ R k, 1 / (p : ℝ) = W k) →
    ∀ a b a' b' : ℝ, P i = primeBand a b → R j = primeBand a' b' →
    2 ≤ a → 0 ≤ b → 2 ≤ a' → 0 ≤ b' →
    ∀ h ξ : ℝ, 0 < h → 0 < ξ → ∀ keptP keptR : Finset ℤ,
    (∀ d ∈ keptP, ξ ≤ finiteCellMass (finiteProductWeight (physicalLabelLaw (P := P) V))
      (fun x => upperLogCell h (Real.log (∏ k, (x k).val : ℕ))) d) →
    (∀ d ∈ keptR, ξ ≤ finiteCellMass (finiteProductWeight (physicalLabelLaw (P := R) W))
      (fun y => upperLogCell h (Real.log (∏ k, (y k).val : ℕ))) d) →
    ∀ (x : ∀ k, P k) (y : ∀ k, R k),
    upperLogCell h (Real.log (∏ k, (x k).val : ℕ)) ∈ keptP →
    upperLogCell h (Real.log (∏ k, (y k).val : ℕ)) ∈ keptR →
    ∀ r : ℕ, 0 < r → r ≤ Q → ∀ u : ℤ, ∀ ζ β B : ℝ, 0 ≤ B →
    ((∏ k, (x k).val : ℕ) : ℝ) * (∏ k, (y k).val : ℕ) ≤ B →
    (∀ d e, primeProductIdealKernel P V Q h keptP d x *
      primeProductIdealKernel R W Q h keptR e y ≠ 0 →
      ((∏ k, (d k).val : ℕ) : ℝ) * (∏ k, (e k).val : ℕ) ≤ B) →
    ‖finiteTwoKernelAverage (finiteProductWeight (physicalLabelLaw V))
        (finiteProductWeight (physicalLabelLaw W))
        (primeProductIdealKernel P V Q h keptP) (primeProductIdealKernel R W Q h keptR) x y
        (fun d e => Complex.exp (Complex.I *
          (ζ * Real.log (((∏ k, (d k).val : ℕ) : ℝ) * (∏ k, (e k).val : ℕ)) +
            2 * Real.pi * (((u : ℝ) / r + β) *
              (((∏ k, (d k).val : ℕ) : ℝ) * (∏ k, (e k).val : ℕ))) : ℝ))) -
      Complex.exp (Complex.I *
        (ζ * Real.log (((∏ k, (x k).val : ℕ) : ℝ) * (∏ k, (y k).val : ℕ)) +
          2 * Real.pi * (((u : ℝ) / r + β) *
            (((∏ k, (x k).val : ℕ) : ℝ) * (∏ k, (y k).val : ℕ))) : ℝ))‖ ≤
      (2 * h * (|ζ| + 2 * Real.pi * |β| * B)) * (Q * Q : ℕ) * (Q * Q : ℕ) +
        Real.sqrt (Q : ℝ) * (primeKernelError C Q (V i) a ξ +
          primeKernelError C Q (W j) a' ξ +
          primeKernelError C Q (V i) a ξ * primeKernelError C Q (W j) a' ξ) := by
  obtain ⟨C, hC, hrep⟩ := prime_product_ideal_dirichlet_reproduction hZ
  refine ⟨C, hC, ?_⟩
  intro Q hQ I J _ _ _ _ P V i R W j hV hW hP hR hVP hWR
    a b a' b' hPi hRj ha hb ha' hb' h ξ hh hξ keptP keptR hkeptP hkeptR
    x y hx hy r hr hrQ u ζ β B hB hxy hsupport
  let π : (∀ k, P k) → ℕ := fun d => ∏ k, (d k).val
  let τ : (∀ k, R k) → ℕ := fun e => ∏ k, (e k).val
  have hπpos (d : ∀ k, P k) : (0 : ℝ) < π d := by
    exact_mod_cast Finset.prod_pos (fun k _ => (hP k (d k).val (d k).property).1.pos)
  have hτpos (e : ∀ k, R k) : (0 : ℝ) < τ e := by
    exact_mod_cast Finset.prod_pos (fun k _ => (hR k (e k).val (e k).property).1.pos)
  have hπ (d : ∀ k, P k) : (π d).Coprime r :=
    Nat.coprime_prod_left_iff.mpr (fun k _ => prime_above_modulus_coprime
      (hP k (d k).val (d k).property).1 hr hrQ (hP k (d k).val (d k).property).2)
  have hτ (e : ∀ k, R k) : (τ e).Coprime r :=
    Nat.coprime_prod_left_iff.mpr (fun k _ => prime_above_modulus_coprime
      (hR k (e k).val (e k).property).1 hr hrQ (hR k (e k).val (e k).property).2)
  have hμ (d : ∀ k, P k) : 0 ≤ finiteProductWeight (physicalLabelLaw V) d :=
    Finset.prod_nonneg (fun k _ => physical_label_law_nonneg V (fun k => (hV k).le) k (d k))
  have hν (e : ∀ k, R k) : 0 ≤ finiteProductWeight (physicalLabelLaw W) e :=
    Finset.prod_nonneg (fun k _ => physical_label_law_nonneg W (fun k => (hW k).le) k (e k))
  let M := fun d e => majorArcMultiplier ζ β (Real.log ((π d : ℝ) * τ e))
  have hm (d : ∀ k, P k) (e : ∀ k, R k)
      (hne : primeProductIdealKernel P V Q h keptP d x * primeProductIdealKernel R W Q h keptR e y ≠ 0) :
      ‖M d e - M x y‖ ≤ 2 * h * (|ζ| + 2 * Real.pi * |β| * B) := by
    exact major_arc_multiplier_log_products ζ β _ _ _ _ B h (hπpos d) (hτpos e)
      (hπpos x) (hτpos y)
      (prime_ideal_kernel_log_localized P V Q hh keptP d x (mul_ne_zero_iff.mp hne).1).le
      (prime_ideal_kernel_log_localized R W Q hh keptR e y (mul_ne_zero_iff.mp hne).2).le
      (hsupport d e hne) hxy
  have hmain := rational_kernel_multiplier_comparison π τ
    (finiteProductWeight (physicalLabelLaw V)) (finiteProductWeight (physicalLabelLaw W))
    (primeProductIdealKernel P V Q h keptP) (primeProductIdealKernel R W Q h keptR) x y
    hr hrQ u hπ hτ
    (prime_kernel_error_nonneg hC.le (hV i).le ha hξ.le hQ)
    (prime_kernel_error_nonneg hC.le (hW j).le ha' hξ.le hQ)
    (fun χ => hrep Q hQ P V i hV hP hVP a b hPi ha hb h ξ hh hξ keptP hkeptP r hr hrQ χ x hx)
    (fun χ => hrep Q hQ R W j hW hR hWR a' b' hRj ha' hb' h ξ hh hξ keptR hkeptR r hr hrQ χ y hy)
    hμ hν (by positivity)
    (prime_ideal_kernel_abs_column_le P V (fun k => (hV k).le) Q h keptP
      (fun d hd => hξ.trans_le (hkeptP d hd)) x)
    (prime_ideal_kernel_abs_column_le R W (fun k => (hW k).le) Q h keptR
      (fun d hd => hξ.trans_le (hkeptR d hd)) y)
    M (by exact (major_arc_multiplier_norm ζ β _).le) hm
  have hphase (d : ∀ k, P k) (e : ∀ k, R k) :
      M d e * Complex.exp (Complex.I * (2 * Real.pi * ((u : ℝ) / r * (π d * τ e)) : ℝ)) =
        Complex.exp (Complex.I * (ζ * Real.log ((π d : ℝ) * τ e) +
          2 * Real.pi * (((u : ℝ) / r + β) * ((π d : ℝ) * τ e)) : ℝ)) := by
    simpa only [Nat.cast_mul] using
      major_arc_rational_phase_factor ζ β u (mul_pos (hπpos d) (hτpos e))
  simpa only [hphase, π, τ] using hmain

theorem prime_kernel_gram_error_le {C V a ξ : ℝ} {Q : ℕ}
    (hC : 0 ≤ C) (hV : 0 ≤ V) (ha : 2 ≤ a) (hξ : 0 ≤ ξ) (hQ : 0 < Q) :
    (Q * Q - 1 : ℕ) * (((C / V) * a ^ (-(1 : ℝ) / 96) *
      (1 + Real.log (Q * Q : ℕ) / Real.log a)) / ξ) ≤ primeKernelError C Q V a ξ := by
  have hlog : 0 < Real.log a := Real.log_pos (by linarith)
  have hq : (1 : ℝ) ≤ (Q * Q : ℕ) := by exact_mod_cast Nat.mul_pos hQ hQ
  have hlogq := Real.log_nonneg hq
  unfold primeKernelError
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast Nat.sub_le (Q * Q) 1
  · positivity

theorem prime_kernel_error_mono_constant {C C' V a ξ : ℝ} {Q : ℕ}
    (hCC : C ≤ C') (hV : 0 ≤ V) (ha : 2 ≤ a) (hξ : 0 ≤ ξ) (hQ : 0 < Q) :
    primeKernelError C Q V a ξ ≤ primeKernelError C' Q V a ξ := by
  have hlog : 0 < Real.log a := Real.log_pos (by linarith)
  have hq : (1 : ℝ) ≤ (Q * Q : ℕ) := by exact_mod_cast Nat.mul_pos hQ hQ
  have hlogq := Real.log_nonneg hq
  unfold primeKernelError
  gcongr

theorem eventually_prime_kernel_error_and_energy_small (c C q v x D : ℝ)
    (hc : 0 < c) (hC : 0 < C) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop, ∀ (Q : ℕ) (V ξ a : ℝ), 0 < Q →
      (Q : ℝ) ≤ L ^ q → L ^ (-v) ≤ V → L ^ (-x) ≤ ξ → Real.exp (L ^ c) ≤ a →
      primeKernelError C Q V a ξ ≤ L ^ (-D) ∧
      (Q * Q - 1 : ℕ) * (((C / V) * a ^ (-(1 : ℝ) / 96) *
        (1 + Real.log (Q * Q : ℕ) / Real.log a)) / ξ) ≤ 1 := by
  filter_upwards [eventually_prime_kernel_reproduction_error_small c C q v x D hc hC,
    eventually_ge_atTop (1 : ℝ)] with L herror hL
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  intro Q V ξ a hQ hQb hV hξ ha
  have herr : primeKernelError C Q V a ξ ≤ L ^ (-D) := herror Q V ξ a hQ hQb hV hξ ha
  have ha2 : 2 ≤ a := by
    calc
      2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      _ ≤ Real.exp (L ^ c) := Real.exp_le_exp.mpr (Real.one_le_rpow hL hc.le)
      _ ≤ a := ha
  refine ⟨herr, (prime_kernel_gram_error_le hC.le ?_ ha2 ?_ hQ).trans (herr.trans ?_)⟩
  · exact (Real.rpow_pos_of_pos hL0 (-v)).le.trans hV
  · exact (Real.rpow_pos_of_pos hL0 (-x)).le.trans hξ
  · simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hL (show -D ≤ 0 by linarith)

theorem prime_major_arc_dyadic_pairing (hZ : PrimitiveZeroFreeRightOf (23 / 24)) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 0 < Q →
    ∀ {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J],
    ∀ (P : I → Finset ℕ) (V : I → ℝ) (i : I)
      (R : J → Finset ℕ) (W : J → ℝ) (j : J),
    (∀ k, 0 < V k) → (∀ k, 0 < W k) →
    (∀ k p, p ∈ P k → p.Prime ∧ Q < p) →
    (∀ k p, p ∈ R k → p.Prime ∧ Q < p) →
    (∀ k, ∑ p ∈ P k, 1 / (p : ℝ) = V k) →
    (∀ k, ∑ p ∈ R k, 1 / (p : ℝ) = W k) →
    ∀ a b a' b' : ℝ, P i = primeBand a b → R j = primeBand a' b' →
    2 ≤ a → 0 ≤ b → 2 ≤ a' → 0 ≤ b' →
    ∀ h ξ : ℝ, 0 < h → h ≤ Real.log 2 → 0 < ξ →
    ∀ U T : ℝ, 0 ≤ U → 0 ≤ T →
    ∀ (f : (∀ k, P k) → ℂ) (g : (∀ k, R k) → ℂ),
    (∀ x, f x ≠ 0 → U ≤ ((∏ k, (x k).val : ℕ) : ℝ) ∧
      ((∏ k, (x k).val : ℕ) : ℝ) ≤ 2 * U) →
    (∀ y, g y ≠ 0 → T ≤ ((∏ k, (y k).val : ℕ) : ℝ) ∧
      ((∏ k, (y k).val : ℕ) : ℝ) ≤ 2 * T) →
    ∀ r : ℕ, 0 < r → r ≤ Q → ∀ u : ℤ, ∀ ζ β : ℝ,
    let μ := finiteProductWeight (physicalLabelLaw (P := P) V)
    let ν := finiteProductWeight (physicalLabelLaw (P := R) W)
    let cellP := fun x : (∀ k, P k) => upperLogCell h (Real.log (∏ k, (x k).val : ℕ))
    let cellR := fun y : (∀ k, R k) => upperLogCell h (Real.log (∏ k, (y k).val : ℕ))
    let KA := primeProductIdealKernel P V Q h (primeProductRetainedCells P V h ξ)
    let KB := primeProductIdealKernel R W Q h (primeProductRetainedCells R W h ξ)
    let phase := fun (x : ∀ k, P k) (y : ∀ k, R k) => Complex.exp (Complex.I *
      (ζ * Real.log (((∏ k, (x k).val : ℕ) : ℝ) * (∏ k, (y k).val : ℕ)) +
        2 * Real.pi * (((u : ℝ) / r + β) *
          (((∏ k, (x k).val : ℕ) : ℝ) * (∏ k, (y k).val : ℕ))) : ℝ))
    ‖∑ x, ∑ y, ((μ x * ν y : ℝ) : ℂ) *
      ((phase x y - finiteTwoKernelAverage μ ν KA KB x y phase) * f x * g y)‖ ≤
      (Real.sqrt (((finiteOccupiedCells cellP).card + (finiteOccupiedCells cellR).card : ℝ) * ξ) +
        (2 * h * (|ζ| + 2 * Real.pi * |β| * (16 * U * T))) * (Q * Q : ℕ) * (Q * Q : ℕ) +
        Real.sqrt (Q : ℝ) * (primeKernelError C Q (V i) a ξ + primeKernelError C Q (W j) a' ξ +
          primeKernelError C Q (V i) a ξ * primeKernelError C Q (W j) a' ξ)) *
      Real.sqrt ((∑ x, μ x * ‖f x‖ ^ 2) * ∑ y, ν y * ‖g y‖ ^ 2) := by
  obtain ⟨C, hC, hpoint⟩ := prime_major_arc_comparison.{u} hZ
  refine ⟨C, hC, ?_⟩
  intro Q hQ I J _ _ _ _ P V i R W j hV hW hP hR hVP hWR
    a b a' b' hPi hRj ha hb ha' hb' h ξ hh hh2 hξ U T hU hT f g hf hg r hr hrQ u ζ β
  let μ := finiteProductWeight (physicalLabelLaw (P := P) V)
  let ν := finiteProductWeight (physicalLabelLaw (P := R) W)
  let cellP := fun x : (∀ k, P k) => upperLogCell h (Real.log (∏ k, (x k).val : ℕ))
  let cellR := fun y : (∀ k, R k) => upperLogCell h (Real.log (∏ k, (y k).val : ℕ))
  let keptP := primeProductRetainedCells P V h ξ
  let keptR := primeProductRetainedCells R W h ξ
  let KA := primeProductIdealKernel P V Q h keptP
  let KB := primeProductIdealKernel R W Q h keptR
  let phase := fun (x : ∀ k, P k) (y : ∀ k, R k) => Complex.exp (Complex.I *
    (ζ * Real.log (((∏ k, (x k).val : ℕ) : ℝ) * (∏ k, (y k).val : ℕ)) +
      2 * Real.pi * (((u : ℝ) / r + β) *
        (((∏ k, (x k).val : ℕ) : ℝ) * (∏ k, (y k).val : ℕ))) : ℝ))
  let comparison := fun x y => finiteTwoKernelAverage μ ν KA KB x y phase
  let E := fun x y => cellP x ∉ keptP ∨ cellR y ∉ keptR
  let ε := (2 * h * (|ζ| + 2 * Real.pi * |β| * (16 * U * T))) * (Q * Q : ℕ) * (Q * Q : ℕ) +
    Real.sqrt (Q : ℝ) * (primeKernelError C Q (V i) a ξ + primeKernelError C Q (W j) a' ξ +
      primeKernelError C Q (V i) a ξ * primeKernelError C Q (W j) a' ξ)
  have hμ (x : ∀ k, P k) : 0 ≤ μ x :=
    Finset.prod_nonneg (fun k _ => physical_label_law_nonneg V (fun k => (hV k).le) k (x k))
  have hν (y : ∀ k, R k) : 0 ≤ ν y :=
    Finset.prod_nonneg (fun k _ => physical_label_law_nonneg W (fun k => (hW k).le) k (y k))
  have hμmass : ∑ x, μ x = 1 :=
    finite_product_weight_sum_one _ (fun k => physical_label_law_sum V k (hV k) (hVP k))
  have hνmass : ∑ y, ν y = 1 :=
    finite_product_weight_sum_one _ (fun k => physical_label_law_sum W k (hW k) (hWR k))
  have hraw (x : ∀ k, P k) (y : ∀ k, R k) : ‖phase x y‖ ≤ 1 := by
    have hn (t : ℝ) : ‖Complex.exp (Complex.I * (t : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    exact (hn _).le
  have hzero (x : ∀ k, P k) (y : ∀ k, R k) (he : E x y) : comparison x y = 0 := by
    rcases he with hx | hy
    · apply finite_two_kernel_average_zero_left
      intro d
      exact prime_ideal_kernel_zero_of_right_discarded P V Q h keptP d x hx
    · apply finite_two_kernel_average_zero_right
      intro e
      exact prime_ideal_kernel_zero_of_right_discarded R W Q h keptR e y hy
  have hε : 0 ≤ ε := by
    have hεA := prime_kernel_error_nonneg hC.le (hV i).le ha hξ.le hQ
    have hεB := prime_kernel_error_nonneg hC.le (hW j).le ha' hξ.le hQ
    dsimp only [ε]
    positivity
  have hclose (x : ∀ k, P k) (y : ∀ k, R k)
      (hfx : f x ≠ 0) (hgy : g y ≠ 0) (he : ¬ E x y) :
      ‖phase x y - comparison x y‖ ≤ ε := by
    have hx : cellP x ∈ keptP := not_not.mp (not_or.mp he).1
    have hy : cellR y ∈ keptR := not_not.mp (not_or.mp he).2
    have hc := prime_kernel_pair_dyadic_cap P V R W Q
      (fun k p hp => (hP k p hp).1.pos) (fun k p hp => (hR k p hp).1.pos)
      hh hh2 keptP keptR hU hT x y (hf x hfx).2 (hg y hgy).2
    have hp := hpoint Q hQ P V i R W j hV hW hP hR hVP hWR
      a b a' b' hPi hRj ha hb ha' hb' h ξ hh hξ keptP keptR
      (fun d hd => prime_product_retained_cell_mass P V h ξ hd)
      (fun e he => prime_product_retained_cell_mass R W h ξ he)
      x y hx hy r hr hrQ u ζ β (16 * U * T) (by positivity) hc.1 hc.2
    rw [norm_sub_rev]
    exact hp
  have hpair := finite_retained_comparison_pairing_supported μ ν hμ hν hμmass hνmass
    E phase comparison hraw hzero f g hε hclose
  have hmass : finitePairEventMass μ ν E ≤
      ((finiteOccupiedCells cellP).card + (finiteOccupiedCells cellR).card : ℝ) * ξ :=
    finite_pair_discarded_mass_le μ ν hμ hν hμmass hνmass cellP cellR hξ.le
  have heps : Real.sqrt (finitePairEventMass μ ν E) + ε ≤
      Real.sqrt (((finiteOccupiedCells cellP).card + (finiteOccupiedCells cellR).card : ℝ) * ξ) + ε :=
    add_le_add (Real.sqrt_le_sqrt hmass) le_rfl
  have hbound := hpair.trans (mul_le_mul_of_nonneg_right heps (Real.sqrt_nonneg _))
  simpa only [ε, add_assoc] using hbound

theorem prime_minor_arc_dyadic_pairing (hZ : PrimitiveZeroFreeRightOf (23 / 24)) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ Q : ℕ, 0 < Q →
    ∀ {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J],
    ∀ (P : I → Finset ℕ) (V : I → ℝ) (i : I)
      (R : J → Finset ℕ) (W : J → ℝ) (j : J),
    (∀ k, 0 < V k) → (∀ k, 0 < W k) →
    (∀ k p, p ∈ P k → p.Prime ∧ Q < p) →
    (∀ k p, p ∈ R k → p.Prime ∧ Q < p) →
    (∀ k, ∑ p ∈ P k, 1 / (p : ℝ) = V k) →
    (∀ k, ∑ p ∈ R k, 1 / (p : ℝ) = W k) →
    ∀ a b a' b' : ℝ, P i = primeBand a b → R j = primeBand a' b' →
    2 ≤ a → 0 ≤ b → 2 ≤ a' → 0 ≤ b' →
    ∀ h ξ : ℝ, 0 < h → h ≤ Real.log 2 → 0 < ξ →
    (Q * Q - 1 : ℕ) * (((C₀ / V i) * a ^ (-(1 : ℝ) / 96) *
      (1 + Real.log (Q * Q : ℕ) / Real.log a)) / ξ) ≤ 1 →
    (Q * Q - 1 : ℕ) * (((C₀ / W j) * a' ^ (-(1 : ℝ) / 96) *
      (1 + Real.log (Q * Q : ℕ) / Real.log a')) / ξ) ≤ 1 →
    ∀ U T : ℕ, 0 < U → 0 < T →
    ∀ (f : (∀ k, P k) → ℂ) (g : (∀ k, R k) → ℂ),
    (∀ x, f x ≠ 0 → U ≤ (∏ k, (x k).val : ℕ) ∧ (∏ k, (x k).val : ℕ) < 2 * U) →
    (∀ y, g y ≠ 0 → T ≤ (∏ k, (y k).val : ℕ) ∧ (∏ k, (y k).val : ℕ) < 2 * T) →
    ∀ C D : ℝ, 0 ≤ C → 0 ≤ D →
    (∀ m : ℕ, (∑ x ∈ Finset.univ.filter (fun x : (∀ k, P k) => (∏ k, (x k).val : ℕ) = m),
      finiteProductWeight (physicalLabelLaw V) x) ≤ C / (m : ℝ)) →
    (∀ m : ℕ, (∑ y ∈ Finset.univ.filter (fun y : (∀ k, R k) => (∏ k, (y k).val : ℕ) = m),
      finiteProductWeight (physicalLabelLaw W) y) ≤ D / (m : ℝ)) →
    ∀ r : ℕ, 0 < r → ∀ u : ℤ, (r : ℤ).gcd u = 1 →
    ∀ β : ℝ, |β| ≤ 1 / (r : ℝ) ^ 2 → ∀ ζ : ℝ,
    let μ := finiteProductWeight (physicalLabelLaw (P := P) V)
    let ν := finiteProductWeight (physicalLabelLaw (P := R) W)
    let KA := primeProductIdealKernel P V Q h (primeProductRetainedCells P V h ξ)
    let KB := primeProductIdealKernel R W Q h (primeProductRetainedCells R W h ξ)
    let phase := fun (x : ∀ k, P k) (y : ∀ k, R k) => Complex.exp (Complex.I *
      (ζ * Real.log (((∏ k, (x k).val : ℕ) : ℝ) * (∏ k, (y k).val : ℕ)) +
        2 * Real.pi * (((u : ℝ) / r + β) *
          (((∏ k, (x k).val : ℕ) : ℝ) * (∏ k, (y k).val : ℕ))) : ℝ))
    ‖∑ x, ∑ y, ((μ x * ν y : ℝ) : ℂ) *
      ((phase x y - finiteTwoKernelAverage μ ν KA KB x y phase) * f x * g y)‖ ≤
      33 * Real.sqrt (6 * C * D * (1 + Real.log r) *
        (1 / (r : ℝ) + 1 / (U : ℝ) + 1 / (T : ℝ) + (r : ℝ) / ((U : ℝ) * T))) *
        Real.sqrt ((∑ x, μ x * ‖f x‖ ^ 2) * ∑ y, ν y * ‖g y‖ ^ 2) := by
  obtain ⟨C₀, hC₀, henergy⟩ := prime_product_ideal_kernel_energy.{u} hZ
  refine ⟨C₀, hC₀, ?_⟩
  intro Q hQ I J _ _ _ _ P V i R W j hV hW hP hR hVP hWR
    a b a' b' hPi hRj ha hb ha' hb' h ξ hh hh2 hξ hsmallP hsmallR
    U T hU hT f g hf hg C D hC hD hμatom hνatom r hr u hcop β hβ ζ
  let μ := finiteProductWeight (physicalLabelLaw (P := P) V)
  let ν := finiteProductWeight (physicalLabelLaw (P := R) W)
  let KA := primeProductIdealKernel P V Q h (primeProductRetainedCells P V h ξ)
  let KB := primeProductIdealKernel R W Q h (primeProductRetainedCells R W h ξ)
  have hμ (x : ∀ k, P k) : 0 ≤ μ x :=
    Finset.prod_nonneg (fun k _ => physical_label_law_nonneg V (fun k => (hV k).le) k (x k))
  have hν (y : ∀ k, R k) : 0 ≤ ν y :=
    Finset.prod_nonneg (fun k _ => physical_label_law_nonneg W (fun k => (hW k).le) k (y k))
  have hπ (x : ∀ k, P k) : 0 < (∏ k, (x k).val : ℕ) :=
    Finset.prod_pos (fun k _ => (hP k (x k).val (x k).property).1.pos)
  have hτ (y : ∀ k, R k) : 0 < (∏ k, (y k).val : ℕ) :=
    Finset.prod_pos (fun k _ => (hR k (y k).val (y k).property).1.pos)
  have hEA := henergy Q hQ P V i hV hP hVP a b hPi ha hb h ξ hh hξ
    (primeProductRetainedCells P V h ξ)
    (fun d hd => prime_product_retained_cell_mass P V h ξ hd) hsmallP f
  have hEB := henergy Q hQ R W j hW hR hWR a' b' hRj ha' hb' h ξ hh hξ
    (primeProductRetainedCells R W h ξ)
    (fun d hd => prime_product_retained_cell_mass R W h ξ hd) hsmallR g
  have hTf := prime_kernel_transform_dyadic_support P V Q
    (fun k p hp => (hP k p hp).1.pos) hh hh2 (primeProductRetainedCells P V h ξ) f hf
  have hTg := prime_kernel_transform_dyadic_support R W Q
    (fun k p hp => (hR k p hp).1.pos) hh hh2 (primeProductRetainedCells R W h ξ) g hg
  exact kernel_full_phase_dyadic_comparison
    (fun x : ∀ k, P k => ∏ k, (x k).val) (fun y : ∀ k, R k => ∏ k, (y k).val)
    hπ hτ U T hU hT μ ν hμ hν KA KB f g hf hg hTf hTg hEA hEB
    hC hD hμatom hνatom hr hcop hβ ζ

theorem prime_all_frequency_dyadic_pairing (hZ : PrimitiveZeroFreeRightOf (23 / 24)) :
    ∃ CM CE : ℝ, 0 < CM ∧ 0 < CE ∧
    ∀ L q κ t n x w z d B : ℝ,
    512 ≤ L → 0 ≤ q → 0 ≤ t → 0 ≤ d →
    2 * κ + t + 2 * B + 3 ≤ q →
    n + 2 * B + 2 ≤ x → 4 * q + max z q + B + 2 ≤ w → q + B + 2 ≤ d →
    ∀ Q : ℕ, Q = ⌊L ^ q⌋₊ → 0 < Q →
    ∀ {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J],
    ∀ (P : I → Finset ℕ) (V : I → ℝ) (i : I)
      (R : J → Finset ℕ) (W : J → ℝ) (j : J),
    (∀ k, 0 < V k) → (∀ k, 0 < W k) →
    (∀ k p, p ∈ P k → p.Prime ∧ Q < p) →
    (∀ k p, p ∈ R k → p.Prime ∧ Q < p) →
    (∀ k, ∑ p ∈ P k, 1 / (p : ℝ) = V k) →
    (∀ k, ∑ p ∈ R k, 1 / (p : ℝ) = W k) →
    ∀ a b a' b' : ℝ, P i = primeBand a b → R j = primeBand a' b' →
    2 ≤ a → 0 ≤ b → 2 ≤ a' → 0 ≤ b' →
    ∀ h ξ : ℝ, 0 < h → h ≤ Real.log 2 → 0 < ξ → h ≤ L ^ (-w) → ξ ≤ L ^ (-x) →
    (Q * Q - 1 : ℕ) * (((CE / V i) * a ^ (-(1 : ℝ) / 96) *
      (1 + Real.log (Q * Q : ℕ) / Real.log a)) / ξ) ≤ 1 →
    (Q * Q - 1 : ℕ) * (((CE / W j) * a' ^ (-(1 : ℝ) / 96) *
      (1 + Real.log (Q * Q : ℕ) / Real.log a')) / ξ) ≤ 1 →
    primeKernelError CM Q (V i) a ξ ≤ L ^ (-d) →
    primeKernelError CM Q (W j) a' ξ ≤ L ^ (-d) →
    (((finiteOccupiedCells (fun v : (∀ k, P k) =>
        upperLogCell h (Real.log (∏ k, (v k).val : ℕ)))).card +
      (finiteOccupiedCells (fun v : (∀ k, R k) =>
        upperLogCell h (Real.log (∏ k, (v k).val : ℕ)))).card : ℕ) : ℝ) ≤ L ^ n →
    ∀ U T : ℕ, L ^ q ≤ (U : ℝ) → L ^ q ≤ (T : ℝ) →
    Real.log ((U : ℝ) * T) ≤ L ^ t →
    ∀ (f : (∀ k, P k) → ℂ) (g : (∀ k, R k) → ℂ),
    (∀ v, f v ≠ 0 → U ≤ (∏ k, (v k).val : ℕ) ∧ (∏ k, (v k).val : ℕ) < 2 * U) →
    (∀ v, g v ≠ 0 → T ≤ (∏ k, (v k).val : ℕ) ∧ (∏ k, (v k).val : ℕ) < 2 * T) →
    ∀ C D : ℝ, 0 ≤ C → 0 ≤ D → C ≤ L ^ κ → D ≤ L ^ κ →
    (∀ m : ℕ, (∑ v ∈ Finset.univ.filter (fun v : (∀ k, P k) => (∏ k, (v k).val : ℕ) = m),
      finiteProductWeight (physicalLabelLaw V) v) ≤ C / (m : ℝ)) →
    (∀ m : ℕ, (∑ v ∈ Finset.univ.filter (fun v : (∀ k, R k) => (∏ k, (v k).val : ℕ) = m),
      finiteProductWeight (physicalLabelLaw W) v) ≤ D / (m : ℝ)) →
    ∀ α ζ : ℝ, |ζ| ≤ L ^ z →
    let μ := finiteProductWeight (physicalLabelLaw (P := P) V)
    let ν := finiteProductWeight (physicalLabelLaw (P := R) W)
    let KA := primeProductIdealKernel P V Q h (primeProductRetainedCells P V h ξ)
    let KB := primeProductIdealKernel R W Q h (primeProductRetainedCells R W h ξ)
    let phase := fun (v : ∀ k, P k) (s : ∀ k, R k) => Complex.exp (Complex.I *
      (ζ * Real.log (((∏ k, (v k).val : ℕ) : ℝ) * (∏ k, (s k).val : ℕ)) +
        2 * Real.pi * (α * (((∏ k, (v k).val : ℕ) : ℝ) * (∏ k, (s k).val : ℕ))) : ℝ))
    ‖∑ v, ∑ s, ((μ v * ν s : ℝ) : ℂ) *
      ((phase v s - finiteTwoKernelAverage μ ν KA KB v s phase) * f v * g s)‖ ≤
      L ^ (-B) * Real.sqrt ((∑ v, μ v * ‖f v‖ ^ 2) * ∑ s, ν s * ‖g s‖ ^ 2) := by
  obtain ⟨CM, hCM, hmajor⟩ := prime_major_arc_dyadic_pairing.{u} hZ
  obtain ⟨CE, hCE, hminor⟩ := prime_minor_arc_dyadic_pairing.{u} hZ
  refine ⟨CM, CE, hCM, hCE, ?_⟩
  intro L q κ t n x w z d B hL hq ht hd hparam hxp hwp hdp Q hQfloor hQ
    I J _ _ _ _ P V i R W j hV hW hP hR hVP hWR a b a' b' hPi hRj ha hb ha' hb'
    h ξ hh hh2 hξ hhb hξb hsmallP hsmallR hεP hεR hcells U T hUb hTb hlog
    f g hf hg C D hC hD hCb hDb hμatom hνatom α ζ hζ
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hU0 : (0 : ℝ) < U := (Real.rpow_pos_of_pos hL0 q).trans_le hUb
  have hT0 : (0 : ℝ) < T := (Real.rpow_pos_of_pos hL0 q).trans_le hTb
  have hU : 0 < U := by exact_mod_cast hU0
  have hT : 0 < T := by exact_mod_cast hT0
  obtain ⟨u, r, β, hr, hcop, hα, hβ, hscale, hratio, hcase⟩ :=
    polynomial_dirichlet_dichotomy α L q U T hL1 hq hUb hTb
  rw [hα]
  rcases hcase with hmajorr | hminorr
  · have hrQ : r ≤ Q := by simpa only [hQfloor] using hmajorr
    have hpair := hmajor Q hQ P V i R W j hV hW hP hR hVP hWR
      a b a' b' hPi hRj ha hb ha' hb' h ξ hh hh2 hξ U T hU0.le hT0.le f g
      (fun v hv => ⟨by exact_mod_cast (hf v hv).1, by exact_mod_cast (hf v hv).2.le⟩)
      (fun v hv => ⟨by exact_mod_cast (hg v hv).1, by exact_mod_cast (hg v hv).2.le⟩)
      r hr hrQ u ζ β
    apply hpair.trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    have hQb : (Q : ℝ) ≤ L ^ q := by
      rw [hQfloor]
      exact Nat.floor_le (Real.rpow_pos_of_pos hL0 q).le
    have hnum := major_arc_coefficient_small hL (Nat.cast_nonneg Q) (by positivity)
      hξ.le hh.le (abs_nonneg ζ) (mul_nonneg (abs_nonneg β) (mul_pos hU0 hT0).le)
      (prime_kernel_error_nonneg hCM.le (hV i).le ha hξ.le hQ)
      (prime_kernel_error_nonneg hCM.le (hW j).le ha' hξ.le hQ) hq hd
      hQb hcells hξb hhb hζ hscale hεP hεR hxp hwp hdp
    convert hnum using 1 <;> first | rfl | (push_cast; ring)
  · have hpair := hminor Q hQ P V i R W j hV hW hP hR hVP hWR
      a b a' b' hPi hRj ha hb ha' hb' h ξ hh hh2 hξ hsmallP hsmallR
      U T hU hT f g hf hg C D hC hD hμatom hνatom r hr u hcop β hβ ζ
    apply hpair.trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact minor_arc_uniform_factor_le hL hC hD ht hq hparam hCb hDb
      hUb hTb hminorr.le hratio hlog

theorem eventually_prime_arbitrary_test_comparison
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) (c κ s z v B : ℝ)
    (hc : 0 < c) (hκ : 0 ≤ κ) (hs : 0 ≤ s) (hz : 0 ≤ z) (hB : 0 ≤ B) :
    let A := B + 2 * (s + 1)
    let q := 2 * κ + (s + 1) + 2 * A + 3
    let w := 4 * q + max z q + A + 2
    let x := (s + w + 2) + 2 * A + 2
    ∀ᶠ L : ℝ in atTop,
    let Q := ⌊L ^ q⌋₊
    let h := L ^ (-w)
    let ξ := L ^ (-x)
    ∀ {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J],
    ∀ (P : I → Finset ℕ) (V : I → ℝ) (i : I)
      (R : J → Finset ℕ) (W : J → ℝ) (j : J),
    (∀ k, 0 < V k) → (∀ k, 0 < W k) →
    (∀ k p, p ∈ P k → p.Prime ∧ Q < p) →
    (∀ k p, p ∈ R k → p.Prime ∧ Q < p) →
    (∀ k, ∑ p ∈ P k, 1 / (p : ℝ) = V k) →
    (∀ k, ∑ p ∈ R k, 1 / (p : ℝ) = W k) →
    L ^ (-v) ≤ V i → L ^ (-v) ≤ W j →
    ∀ a b a' b' : ℝ, P i = primeBand a b → R j = primeBand a' b' →
    Real.exp (L ^ c) ≤ a → 0 ≤ b → Real.exp (L ^ c) ≤ a' → 0 ≤ b' →
    (∀ t : (∀ k, P k), Real.log (∏ k, (t k).val : ℕ) ≤ L ^ s) →
    (∀ t : (∀ k, R k), Real.log (∏ k, (t k).val : ℕ) ≤ L ^ s) →
    (∀ m : ℕ, (∑ t ∈ Finset.univ.filter (fun t : (∀ k, P k) => (∏ k, (t k).val : ℕ) = m),
      finiteProductWeight (physicalLabelLaw V) t) ≤ L ^ κ / (m : ℝ)) →
    (∀ m : ℕ, (∑ t ∈ Finset.univ.filter (fun t : (∀ k, R k) => (∏ k, (t k).val : ℕ) = m),
      finiteProductWeight (physicalLabelLaw W) t) ≤ L ^ κ / (m : ℝ)) →
    ∀ (f : (∀ k, P k) → ℂ) (g : (∀ k, R k) → ℂ),
    ∀ α ζ : ℝ, |ζ| ≤ L ^ z →
    let μ := finiteProductWeight (physicalLabelLaw (P := P) V)
    let ν := finiteProductWeight (physicalLabelLaw (P := R) W)
    let KA := primeProductIdealKernel P V Q h (primeProductRetainedCells P V h ξ)
    let KB := primeProductIdealKernel R W Q h (primeProductRetainedCells R W h ξ)
    let phase := fun (t : ∀ k, P k) (r : ∀ k, R k) => Complex.exp (Complex.I *
      (ζ * Real.log (((∏ k, (t k).val : ℕ) : ℝ) * (∏ k, (r k).val : ℕ)) +
        2 * Real.pi * (α * (((∏ k, (t k).val : ℕ) : ℝ) * (∏ k, (r k).val : ℕ))) : ℝ))
    ‖∑ t, ∑ r, ((μ t * ν r : ℝ) : ℂ) *
      ((phase t r - finiteTwoKernelAverage μ ν KA KB t r phase) * f t * g r)‖ ≤
      L ^ (-B) * Real.sqrt ((∑ t, μ t * ‖f t‖ ^ 2) * ∑ r, ν r * ‖g r‖ ^ 2) := by
  intro A q w x
  let n := s + w + 2
  let d := q + A + 2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hw : 1 ≤ w := by
    have hmax : 0 ≤ max z q := hz.trans (le_max_left _ _)
    dsimp only [w]
    linarith
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  obtain ⟨CM, CE, hCM, hCE, hbound⟩ := prime_all_frequency_dyadic_pairing.{u} hZ
  filter_upwards [eventually_ge_atTop (512 : ℝ),
    eventually_prime_kernel_error_and_energy_small c CM q v x d hc hCM hd,
    eventually_prime_kernel_error_and_energy_small c CE q v x d hc hCE hd,
    eventually_prime_band_product_scale.{u} hc q] with L hL hM hE hprod
  intro Q h ξ I J _ _ _ _ P V i R W j hV hW hP hR hVP hWR hVi hWj
    a b a' b' hPi hRj ha hb ha' hb' hmaxP hmaxR hμatom hνatom f g α ζ hζ
  let μ := finiteProductWeight (physicalLabelLaw (P := P) V)
  let ν := finiteProductWeight (physicalLabelLaw (P := R) W)
  let π := fun t : ∀ k, P k => (∏ k, (t k).val : ℕ)
  let τ := fun t : ∀ k, R k => (∏ k, (t k).val : ℕ)
  let KA := primeProductIdealKernel P V Q h (primeProductRetainedCells P V h ξ)
  let KB := primeProductIdealKernel R W Q h (primeProductRetainedCells R W h ξ)
  let phase := fun (t : ∀ k, P k) (r : ∀ k, R k) => Complex.exp (Complex.I *
    (ζ * Real.log ((π t : ℝ) * τ r) + 2 * Real.pi * (α * ((π t : ℝ) * τ r)) : ℝ))
  let K := fun t r => phase t r - finiteTwoKernelAverage μ ν KA KB t r phase
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hQ : 0 < Q := Nat.floor_pos.mpr (Real.one_le_rpow hL1 hq)
  have hQb : (Q : ℝ) ≤ L ^ q := Nat.floor_le (Real.rpow_pos_of_pos hL0 q).le
  have hh : 0 < h := Real.rpow_pos_of_pos hL0 _
  have hξ : 0 < ξ := Real.rpow_pos_of_pos hL0 _
  have hh2 : h ≤ Real.log 2 := polynomial_width_le_log_two (by linarith) hw
  have ha2 : 2 ≤ a := by
    have he : 2 ≤ Real.exp (L ^ c) := by
      calc
        2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        _ ≤ Real.exp (L ^ c) := Real.exp_le_exp.mpr (Real.one_le_rpow hL1 hc.le)
    exact he.trans ha
  have ha2' : 2 ≤ a' := by
    have he : 2 ≤ Real.exp (L ^ c) := by
      calc
        2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        _ ≤ Real.exp (L ^ c) := Real.exp_le_exp.mpr (Real.one_le_rpow hL1 hc.le)
    exact he.trans ha'
  have hμ (t : ∀ k, P k) : 0 ≤ μ t :=
    Finset.prod_nonneg (fun k _ => physical_label_law_nonneg V (fun k => (hV k).le) k (t k))
  have hν (t : ∀ k, R k) : 0 ≤ ν t :=
    Finset.prod_nonneg (fun k _ => physical_label_law_nonneg W (fun k => (hW k).le) k (t k))
  have hπ (t : ∀ k, P k) : 0 < π t :=
    Finset.prod_pos (fun k _ => (hP k (t k).val (t k).property).1.pos)
  have hτ (t : ∀ k, R k) : 0 < τ t :=
    Finset.prod_pos (fun k _ => (hR k (t k).val (t k).property).1.pos)
  have hlogP (t : ∀ k, P k) : 0 ≤ Real.log (π t) ∧ Real.log (π t) ≤ L ^ s :=
    ⟨Real.log_nonneg (by exact_mod_cast hπ t), hmaxP t⟩
  have hlogR (t : ∀ k, R k) : 0 ≤ Real.log (τ t) ∧ Real.log (τ t) ≤ L ^ s :=
    ⟨Real.log_nonneg (by exact_mod_cast hτ t), hmaxR t⟩
  have hcells := two_upper_log_cell_cards_polynomial
    (fun t => Real.log (π t)) (fun t => Real.log (τ t)) (by linarith : 4 ≤ L) hs
    (show 0 ≤ w by linarith) hlogP hlogR
  have hminP := hprod P i (fun k p hp => (hP k p hp).1.pos) a b hPi ha hb
  have hminR := hprod R j (fun k p hp => (hR k p hp).1.pos) a' b' hRj ha' hb'
  have hMP := (hM Q (V i) ξ a hQ hQb hVi le_rfl ha).1
  have hMR := (hM Q (W j) ξ a' hQ hQb hWj le_rfl ha').1
  have hEP := (hE Q (V i) ξ a hQ hQb hVi le_rfl ha).2
  have hER := (hE Q (W j) ξ a' hQ hQb hWj le_rfl ha').2
  change ‖∑ t, ∑ r, ((μ t * ν r : ℝ) : ℂ) * (K t r * f t * g r)‖ ≤ _
  rw [finite_weighted_pairing_reorder]
  apply finite_dyadic_pairing_polynomial_bound π τ μ ν hμ hν f g K hL0
    (finite_dyadic_card_polynomial π hπ (by linarith) hs hmaxP)
    (finite_dyadic_card_polynomial τ hτ (by linarith) hs hmaxR)
  intro k _ l _
  by_cases hfk : ∃ t, finiteDyadicTest π k f t ≠ 0
  · by_cases hgl : ∃ r, finiteDyadicTest τ l g r ≠ 0
    · have hU := finite_dyadic_endpoint_scales π f hπ (fun t _ => hminP t) hmaxP hfk
      have hT := finite_dyadic_endpoint_scales τ g hτ (fun t _ => hminR t) hmaxR hgl
      have hlog := dyadic_log_product_polynomial
        (show (0 : ℝ) < (2 ^ k : ℕ) by positivity)
        (show (0 : ℝ) < (2 ^ l : ℕ) by positivity) (by linarith : 2 ≤ L) hU.2 hT.2
      have hp := hbound L q κ (s + 1) n x w z d A hL hq (by positivity) hd
        (by dsimp only [q]; linarith) (by dsimp only [x, n]; linarith)
        (by dsimp only [w]; linarith) (by dsimp only [d]; linarith) Q rfl hQ
        P V i R W j hV hW hP hR hVP hWR a b a' b' hPi hRj ha2 hb ha2' hb'
        h ξ hh hh2 hξ le_rfl le_rfl hEP hER hMP hMR hcells (2 ^ k) (2 ^ l) hU.1 hT.1 hlog
        (finiteDyadicTest π k f) (finiteDyadicTest τ l g)
        (finite_dyadic_test_range π f (fun t _ => hπ t) k)
        (finite_dyadic_test_range τ g (fun r _ => hτ r) l)
        (L ^ κ) (L ^ κ) (by positivity) (by positivity) le_rfl le_rfl hμatom hνatom α ζ hζ
      have he : -B - (s + 1) - (s + 1) = -A := by dsimp only [A]; ring
      rw [he, ← finite_weighted_pairing_reorder]
      exact hp
    · have hg0 : ∀ r, finiteDyadicTest τ l g r = 0 := by
        intro r
        by_contra hn
        exact hgl ⟨r, hn⟩
      simp [hg0]
  · have hf0 : ∀ t, finiteDyadicTest π k f t = 0 := by
      intro t
      by_contra hn
      exact hfk ⟨t, hn⟩
    simp [hf0]

theorem eventually_candidate_Q_prime_cancellation
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c : ℝ} (hc : 0 < c) (B : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (f : ℕ), 0 < f → (f : ℝ) ≤ Real.exp L →
      ∀ χ : DirichletCharacter ℂ f, χ ≠ 1 →
      ∀ (m : ℕ), m ≠ 0 → (m : ℝ) ≤ Real.exp L →
      ∀ (a R : ℕ), a ≠ 0 → R ≠ 0 →
        ‖∑ p ∈ ((candidateQBand (c*L) 0).filter
          (fun p => p*R ∈ arithmeticProductWindow a (Real.exp L))).filter
            (fun p => p.Coprime m), χ (p : ZMod f)‖ ≤
          ((16*Real.exp L) / ((a*R : ℕ) : ℝ)) * L^(-B) := by
  filter_upwards [eventually_prime_band_coprime_relative_power_bound hZ hc B] with L hL
  intro f hf hfL χ hχ m hm hmL a R ha hR
  rw [candidate_Q_zero_product_window_eq c L ha]
  exact hL f hf hfL χ hχ (Real.exp ((6/5 : ℝ)*(c*L))) ((a*R : ℕ) : ℝ)
    (Real.exp L) (16*Real.exp L) (Real.exp_pos _).le
    (Nat.cast_pos.mpr (Nat.mul_pos (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hR)))
    (Real.exp_pos L).le (by positivity) m hm hmL

theorem eventually_candidate_Q_character_cancellation
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c : ℝ} (hc : 0 < c) (B : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (f : ℕ), 0 < f → (f : ℝ) ≤ Real.exp L →
      ∀ χ : DirichletCharacter ℂ f, χ ≠ 1 →
      ∀ (m : ℕ), m ≠ 0 → (m : ℝ) ≤ Real.exp L →
      ∀ (r jStar : ℕ) (hr : 0 < r), 0 < jStar →
      ∀ a : ℕ, a ≠ 0 →
        ‖∑ n ∈ (arithmeticProductWindow a (Real.exp L)).filter (fun n => n.Coprime m),
          (candidateQWeight c L r jStar n : ℂ) * χ (n : ZMod f)‖ ≤
          ((16*Real.exp L) / (a : ℝ)) * L^(-B) * candidateQRestHarmonicMass c L r jStar hr := by
  filter_upwards [eventually_candidate_Q_prime_cancellation hZ hc B,
    eventually_ge_atTop (0 : ℝ)] with L hL hL0
  intro f hf hfL χ hχ m hm hmL r jStar hr hj a ha
  apply candidate_Q_character_bound_of_prime_bound c L r jStar hr hj
    (arithmeticProductWindow a (Real.exp L)) χ m ((16*Real.exp L)/(a : ℝ)) (L^(-B))
    (by positivity) (Real.rpow_nonneg hL0 _)
  intro y
  have hb := hL f hf hfL χ hχ m hm hmL a
    (orderedSlotProduct (candidateQRestChoices c L r jStar hr) y) ha
    (candidate_Q_rest_product_nonzero c L r jStar hr y)
  simpa only [Nat.cast_mul, div_mul_eq_div_div] using hb

theorem eventually_prime_interval_mellin_power_bound (hZ : PrimitiveZeroFreeRightOf (23 / 24))
    {a T : ℝ} (ha : 0 < a) (hT : 0 ≤ T) (Bsave : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ, Real.exp (a*L) ≤ Y →
      ∀ (r : ℕ), 0 < r → (r : ℝ) ≤ L^T →
      ∀ χ : DirichletCharacter ℂ r, χ ≠ 1 →
      ∀ v : ℝ, |v| ≤ L^T → ∀ m n : ℕ, m ≤ n → Y ≤ (m+1 : ℕ) → (n : ℝ) ≤ 2*Y →
        ‖∑ i ∈ (Ioc m n).filter Nat.Prime, harmonicMellinWeight v i*χ (i : ZMod r)‖ ≤
          L^(-Bsave) := by
  have ha2 : 0 < a/2 := by positivity
  filter_upwards [eventually_prime_band_coprime_relative_power_bound hZ ha2 (Bsave+T+1),
    eventually_rpow_le_exp_sqrt T, eventually_ge_atTop (10 : ℝ)] with L hraw hmod hL10
  intro Y hY r hr hrT χ hχ v hv m n hmn hYm hn
  have hL : 0 < L := by linarith
  have hY0 : 0 < Y := (Real.exp_pos _).trans_le hY
  have hrL : (r : ℝ) ≤ Real.exp L := hrT.trans (hmod.trans
    (Real.exp_le_exp.mpr (Real.sqrt_le_self_iff.mpr (Or.inr (by linarith)))))
  have hexp : Real.exp ((a/2)*L) < Y := by
    apply lt_of_lt_of_le _ hY
    exact Real.exp_lt_exp.mpr (by nlinarith)
  by_cases heq : m = n
  · subst n
    simp only [Ioc_self, filter_empty, sum_empty, norm_zero]
    positivity
  have hmn' : m < n := lt_of_le_of_ne hmn heq
  let g := fun i : ℕ => if i.Prime then χ (i : ZMod r) else 0
  have hprefix : ∀ i ∈ Icc m n,
      ‖∑ j ∈ Ioc m i, g j‖ ≤ 2*Y*L^(-(Bsave+T+1)) := by
    intro i hi
    have hb := hraw r hr hrL χ hχ (i : ℝ) 1 (m : ℝ) (i : ℝ)
      (Nat.cast_nonneg _) zero_lt_one (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      1 (by omega) (by simpa only [Nat.cast_one] using Real.one_le_exp hL.le)
    have hset : ((primeBand (Real.exp ((a/2)*L)) (i : ℝ)).filter
        (fun p : ℕ => (m : ℝ) < 1*(p : ℝ) ∧ 1*(p : ℝ) ≤ i)).filter
        (fun p => p.Coprime 1) = (Ioc m i).filter Nat.Prime := by
      ext p
      simp only [mem_filter, mem_primeBand_iff (Real.exp_pos _).le (Nat.cast_nonneg i),
        one_mul, Nat.coprime_one_right_iff, and_true, mem_Ioc, Nat.cast_lt, Nat.cast_le]
      constructor
      · intro hp
        exact ⟨hp.2, hp.1.1⟩
      · intro hp
        have hpY : Y ≤ (p : ℝ) := hYm.trans (Nat.cast_le.mpr hp.1.1)
        exact ⟨⟨hp.2, hexp.trans_le hpY, hp.1.2⟩, hp.1⟩
    rw [hset, div_one] at hb
    have hiY : (i : ℝ) ≤ 2*Y := (Nat.cast_le.mpr (mem_Icc.mp hi).2).trans hn
    have hb' := hb.trans (mul_le_mul_of_nonneg_right hiY (by positivity))
    simpa only [g, sum_filter] using hb'
  have hh := norm_harmonic_mellin_interval_sum_le g hY0 hmn' hYm hn
    (v := v) (B := 2*Y*L^(-(Bsave+T+1))) (by positivity) hprefix
  have hpow : 1 ≤ L^T := Real.one_le_rpow (by linarith) hT
  have hgain : 2*(3+2*|v|) ≤ L^(T+1) := by
    calc
      _ ≤ 10*L^T := by nlinarith
      _ ≤ L*L^T := mul_le_mul_of_nonneg_right hL10 (by positivity)
      _ = _ := by rw [Real.rpow_add hL, Real.rpow_one]; ring
  calc
    _ = ‖∑ i ∈ Ioc m n, harmonicMellinWeight v i*g i‖ := by
      simp only [sum_filter, g, mul_ite, mul_zero]
    _ ≤ ((3+2*|v|)/Y)*(2*Y*L^(-(Bsave+T+1))) := hh
    _ = (2*(3+2*|v|))*L^(-(Bsave+T+1)) := by field_simp
    _ ≤ L^(T+1)*L^(-(Bsave+T+1)) := mul_le_mul_of_nonneg_right hgain (by positivity)
    _ = L^(-Bsave) := by
      rw [← Real.rpow_add hL]
      congr 1
      ring

theorem eventually_candidate_character_cancellation
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c : ℝ} (hc : 0 < c) (B : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (q : ℝ), 0 ≤ q →
      ∀ (r jStar : ℕ) (hr : 0 < r), 0 < jStar →
      ∀ (f : ℕ), 0 < f → (f : ℝ) ≤ Real.exp L →
      ∀ χ : DirichletCharacter ℂ f, χ ≠ 1 →
      ∀ (m : ℕ), m ≠ 0 → (m : ℝ) ≤ Real.exp L →
        ‖∑ u ∈ (arithmeticProductWindow 1 (Real.exp L)).filter (fun u => u.Coprime m),
          (candidateCoefficient c L q r jStar u : ℂ) * χ (u : ZMod f)‖ ≤
          (16*Real.exp L) * L^(-B) * candidateOneMarkedHarmonicMass c L q *
            candidateQRestHarmonicMass c L r jStar hr := by
  filter_upwards [eventually_candidate_character_coprime_convolution hc,
    eventually_candidate_Q_character_cancellation hZ hc B,
    eventually_ge_atTop (0 : ℝ)] with L hconv hQ hL
  intro q hq r jStar hr hj f hf hfL χ hχ m hm hmL
  let R : ℝ := candidateQRestHarmonicMass c L r jStar hr
  let C : ℝ := (16*Real.exp L) * L^(-B) * R
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
            (((16*Real.exp L)/(a : ℝ)) * L^(-B) * R) :=
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

theorem eventually_prime_mellin_band_power_bound (hZ : PrimitiveZeroFreeRightOf (23 / 24))
    {a C T : ℝ} (ha : 0 < a) (hC : 0 < C) (hT : 0 ≤ T) (Bsave : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ A B : ℝ, Real.exp (a*L) ≤ A → 0 ≤ B → B ≤ Real.exp (C*L) →
      ∀ (r : ℕ), 0 < r → (r : ℝ) ≤ L^T →
      ∀ χ : DirichletCharacter ℂ r, χ ≠ 1 → ∀ v : ℝ, |v| ≤ L^T →
        ‖∑ p ∈ primeBand A B, harmonicMellinWeight v p*χ (p : ZMod r)‖ ≤ L^(-Bsave) := by
  classical
  have ha2 : 0 < a/2 := by positivity
  filter_upwards [eventually_prime_interval_mellin_power_bound hZ ha2 hT (Bsave+2),
    eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (2*Real.log 2/a),
    eventually_ge_atTop (C/Real.log 2+1)] with L hprime hL1 hLa hLc
  have hL : 0 < L := zero_lt_one.trans_le hL1
  intro A B hA hB hBmax r hr hrT χ hχ v hv
  have hA0 : 0 ≤ A := (Real.exp_pos _).le.trans hA
  let F := primeBand A B
  let w := fun p : ℕ => harmonicMellinWeight v p*χ (p : ZMod r)
  have hFpos : ∀ p ∈ F, 0 < p := fun p hp => ((mem_primeBand_iff hA0 hB p).mp hp).1.pos
  have hFlow : ∀ p ∈ F, Real.exp (a*L) < (p : ℝ) := fun p hp =>
    hA.trans_lt ((mem_primeBand_iff hA0 hB p).mp hp).2.1
  have hFupper : ∀ p ∈ F, p ≤ ⌊Real.exp (C*L)⌋₊ := fun p hp =>
    Nat.le_floor (((mem_primeBand_iff hA0 hB p).mp hp).2.2.trans hBmax)
  have hcount : ((dyadicNatIndices F).card : ℝ) ≤ L^2 := by
    have hraw := dyadicNatIndices_card_le_log F ⌊Real.exp (C*L)⌋₊ hFupper
    have hNpos : 0 < ⌊Real.exp (C*L)⌋₊ := Nat.floor_pos.mpr (Real.one_le_exp (by positivity))
    have hlog : Real.log (⌊Real.exp (C*L)⌋₊ : ℝ) ≤ C*L := by
      simpa only [Real.log_exp] using Real.log_le_log (Nat.cast_pos.mpr hNpos)
        (Nat.floor_le (Real.exp_pos _).le)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    calc
      _ ≤ Real.log (⌊Real.exp (C*L)⌋₊ : ℝ)/Real.log 2+1 := hraw
      _ ≤ (C*L)/Real.log 2+1 := add_le_add (div_le_div_of_nonneg_right hlog hlog2.le) le_rfl
      _ ≤ (C*L)/Real.log 2+L := add_le_add le_rfl hL1
      _ = (C/Real.log 2+1)*L := by ring
      _ ≤ L*L := mul_le_mul_of_nonneg_right hLc hL.le
      _ = L^2 := (pow_two L).symm
  have htwo : 2 ≤ Real.exp ((a/2)*L) := by
    apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)).mp
    have hh := (div_le_iff₀ ha).mp hLa
    nlinarith
  have hexp : 2*Real.exp ((a/2)*L) ≤ Real.exp (a*L) := by
    have hm := mul_le_mul_of_nonneg_right htwo (Real.exp_pos ((a/2)*L)).le
    have he : Real.exp ((a/2)*L)*Real.exp ((a/2)*L) = Real.exp (a*L) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rwa [he] at hm
  have hbucket : ∀ k ∈ dyadicNatIndices F, ‖∑ p ∈ dyadicNatBucket F k, w p‖ ≤ L^(-(Bsave+2)) := by
    intro k hk
    obtain ⟨p, hp⟩ := (dyadicNatBucket_nonempty_iff F k).mpr hk
    have hpb := dyadicNatBucket_bounds F hFpos hp
    have hpF := (mem_dyadicNatBucket F k p).mp hp |>.1
    let Y : ℝ := (2 : ℝ)^k
    have hY0 : 0 < Y := by positivity
    have hYlow : Real.exp ((a/2)*L) ≤ Y := by
      have hpY : (p : ℝ) < 2*Y := by
        have hh : (p : ℝ) < (2 : ℝ)^(k+1) := by exact_mod_cast hpb.2
        simpa only [pow_succ, Y, mul_comm] using hh
      have hpL := hFlow p hpF
      nlinarith
    let lo := max ⌊A⌋₊ (2^k-1)
    let hi := min ⌊B⌋₊ (2^(k+1)-1)
    have hrepr : dyadicNatBucket F k = (Ioc lo hi).filter Nat.Prime := dyadic_prime_band_bucket A B k
    have hpI : p ∈ Ioc lo hi := (mem_filter.mp (hrepr ▸ hp)).1
    have hlohi : lo ≤ hi := (mem_Ioc.mp hpI).1.le.trans (mem_Ioc.mp hpI).2
    have hYm : Y ≤ (lo+1 : ℕ) := by
      have hkpos : 0 < 2^k := by positivity
      have hh : 2^k ≤ lo+1 := by dsimp [lo]; omega
      dsimp [Y]
      exact_mod_cast hh
    have hhiY : (hi : ℝ) ≤ 2*Y := by
      have hh : hi ≤ 2^(k+1) := (min_le_right _ _).trans (Nat.sub_le _ _)
      have hhR : (hi : ℝ) ≤ (2 : ℝ)^(k+1) := by exact_mod_cast hh
      simpa only [pow_succ, Y, mul_comm] using hhR
    rw [hrepr]
    exact hprime Y hYlow r hr hrT χ hχ v hv lo hi hlohi hYm hhiY
  change ‖∑ p ∈ F, w p‖ ≤ _
  rw [← sum_dyadicNatBuckets F w]
  calc
    _ ≤ ∑ k ∈ dyadicNatIndices F, ‖∑ p ∈ dyadicNatBucket F k, w p‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ dyadicNatIndices F, L^(-(Bsave+2)) := sum_le_sum hbucket
    _ = ((dyadicNatIndices F).card : ℝ)*L^(-(Bsave+2)) := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ L^2*L^(-(Bsave+2)) := mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = L^(-Bsave) := by
      rw [← Real.rpow_natCast L 2, ← Real.rpow_add hL]
      congr 1
      norm_num

theorem exists_candidate_character_relative_power_bound
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q : ℝ} {r : ℕ}
    (hc : 0 < c) (hr : 0 < r) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcenter : (11/5 : ℝ) * (r : ℝ) * c = 1) (B : ℝ) :
    ∃ J : ℕ, ∀ᶠ L : ℝ in atTop, ∀ jStar : ℕ, J < jStar →
      ∀ (f : ℕ), 0 < f → (f : ℝ) ≤ Real.exp L →
      ∀ χ : DirichletCharacter ℂ f, χ ≠ 1 →
      ∀ (m : ℕ), m ≠ 0 → (m : ℝ) ≤ Real.exp L →
        ‖∑ u ∈ (arithmeticProductWindow 1 (Real.exp L)).filter (fun u => u.Coprime m),
          (candidateCoefficient c L q r jStar u : ℂ) * χ (u : ZMod f)‖ ≤
          candidateCoefficientWindowMass c L q r jStar * L^(-B) := by
  obtain ⟨V, hV, hrest⟩ := exists_candidate_Q_rest_harmonic_upper hc r hr
  obtain ⟨K, hK, J, hlower⟩ :=
    exists_candidate_coefficient_window_mass_lower hc hr hq0 hq1 hcenter
  refine ⟨J, ?_⟩
  filter_upwards [eventually_candidate_character_cancellation hZ hc (B+2), hrest, hlower,
    eventually_candidate_one_marked_mass_ge_one hc hq0 hq1.le,
    eventually_ge_atTop ((16*V)/K), eventually_gt_atTop (0 : ℝ)] with
      L hcancel hrestL hlowerL hPone hlarge hL
  intro jStar hj f hf hfL χ hχ m hm hmL
  have hj0 : 0 < jStar := (Nat.zero_le J).trans_lt hj
  have hP : 0 ≤ candidateOneMarkedHarmonicMass c L q := zero_le_one.trans hPone
  have hQ : 0 ≤ candidateQHarmonicMass c L r jStar := by
    apply tsum_nonneg
    intro n
    exact div_nonneg (candidate_Q_weight_nonneg c L r jStar n) (Nat.cast_nonneg n)
  have hconst : 16*V ≤ K*L := by
    simpa only [mul_comm L K] using (div_le_iff₀ hK).mp hlarge
  have hpowers : L^(-(B+2)) = L^(-B) / L^2 := by
    rw [show -(B+2) = -B - 2 by ring, Real.rpow_sub hL, Real.rpow_two]
  calc
    _ ≤ (16*Real.exp L) * L^(-(B+2)) * candidateOneMarkedHarmonicMass c L q *
        candidateQRestHarmonicMass c L r jStar hr :=
      hcancel q hq0 r jStar hr hj0 f hf hfL χ hχ m hm hmL
    _ ≤ (16*Real.exp L) * L^(-(B+2)) * candidateOneMarkedHarmonicMass c L q *
        (V * candidateQHarmonicMass c L r jStar) :=
      mul_le_mul_of_nonneg_left (hrestL jStar hj0) (by positivity)
    _ = (16*V) * (Real.exp L * candidateOneMarkedHarmonicMass c L q *
        candidateQHarmonicMass c L r jStar * L^(-(B+2))) := by ring
    _ ≤ (K*L) * (Real.exp L * candidateOneMarkedHarmonicMass c L q *
        candidateQHarmonicMass c L r jStar * L^(-(B+2))) :=
      mul_le_mul_of_nonneg_right hconst (by positivity)
    _ = (K * (Real.exp L/L) * candidateOneMarkedHarmonicMass c L q *
        candidateQHarmonicMass c L r jStar) * L^(-B) := by
      rw [hpowers]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (hlowerL jStar hj) (Real.rpow_nonneg hL.le _)

theorem eventually_exponential_rough_test_mellin_bound (hZ : PrimitiveZeroFreeRightOf (23 / 24))
    {γ C T : ℝ} (hγ : 0 < γ) (hC : 0 < C) (hT : 0 ≤ T) (Bsave : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ U V : ℝ, 1 ≤ U → 0 ≤ V → V ≤ Real.exp (C*L) →
      ∀ (r : ℕ), 0 < r → (r : ℝ) ≤ L^T →
      ∀ χ : DirichletCharacter ℂ r, χ ≠ 1 → ∀ v : ℝ, |v| ≤ L^T →
        ‖∑ n ∈ roughBand U V (Real.exp (γ*L)),
          harmonicMellinWeight v n*χ (n : ZMod r)‖ ≤ L^(-Bsave) := by
  classical
  filter_upwards [eventually_prime_mellin_band_power_bound hZ hγ hC hT (Bsave+2),
    eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (C+2)] with L hprime hL1 hLc
  have hL : 0 < L := zero_lt_one.trans_le hL1
  intro U V hU hV hVmax r hr hrT χ hχ v hv
  by_cases hV1 : 1 ≤ V
  swap
  · have hVU : V ≤ U := by linarith
    simp only [roughBand, Ioc_eq_empty_of_le (Nat.floor_le_floor hVU), filter_empty, sum_empty, norm_zero]
    positivity
  let z := Real.exp (γ*L)
  let w := fun n : ℕ => harmonicMellinWeight v n*χ (n : ZMod r)
  have hwprod : ∀ p m : ℕ, 0 < p → 0 < m → w (p*m) = w p*w m := by
    intro p m hp hm
    dsimp [w]
    rw [Nat.cast_mul, harmonic_mellin_weight_mul v (Nat.cast_pos.mpr hp) (Nat.cast_pos.mpr hm),
      Nat.cast_mul, map_mul]
    ring
  have hwnorm : ∀ m : ℕ, 0 < m → ‖w m‖ ≤ 1/(m : ℝ) := by
    intro m hm
    dsimp [w]
    rw [norm_mul, norm_harmonic_mellin_weight v (Nat.cast_pos.mpr hm)]
    exact mul_le_of_le_one_right (by positivity) (χ.norm_le_one _)
  have hfirst : ‖∑ p ∈ primeBand (max U z) V, w p‖ ≤ L^(-(Bsave+2)) :=
    hprime _ V (le_max_right _ _) hV hVmax r hr hrT χ hχ v hv
  have hinner : ∀ m ∈ roughBand 1 V z,
      ‖∑ p ∈ (primeBand z (m.minFac : ℝ)).filter
        (fun p : ℕ => U < (m : ℝ)*(p : ℝ) ∧ (m : ℝ)*(p : ℝ) ≤ V), w (p*m)‖ ≤
          (1/(m : ℝ))*L^(-(Bsave+2)) := by
    intro m hm
    have hm0 := roughBand_pos hm
    have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm0
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm0
    let P := (primeBand z (m.minFac : ℝ)).filter
      (fun p : ℕ => U < (m : ℝ)*(p : ℝ) ∧ (m : ℝ)*(p : ℝ) ≤ V)
    have hsum : (∑ p ∈ P, w (p*m)) = (∑ p ∈ P, w p)*w m := by
      rw [sum_mul]
      apply sum_congr rfl
      intro p hp
      exact hwprod p m ((mem_filter.mp (mem_filter.mp hp).1).2.pos) hm0
    have hPbound : ‖∑ p ∈ P, w p‖ ≤ L^(-(Bsave+2)) := by
      dsimp [P]
      rw [primeBand_product_interval (Real.exp_pos _).le (Nat.cast_nonneg _) hmR (by linarith) hV]
      apply hprime _ _ (le_max_left _ _) (le_min (Nat.cast_nonneg _) (div_nonneg hV hmR.le))
        _ r hr hrT χ hχ v hv
      exact (min_le_right _ _).trans ((div_le_self hV hm1).trans hVmax)
    change ‖∑ p ∈ P, w (p*m)‖ ≤ _
    rw [hsum, norm_mul]
    have hmul := mul_le_mul hPbound (hwnorm m hm0) (norm_nonneg _) (by positivity)
    exact hmul.trans_eq (mul_comm _ _)
  have hlogV : Real.log V ≤ C*L := by
    simpa only [Real.log_exp] using Real.log_le_log (zero_lt_one.trans_le hV1) hVmax
  have hmass : (∑ m ∈ roughBand 1 V z, 1/(m : ℝ)) ≤ 1+C*L :=
    (roughBandHarmonic_le_log hV1).trans (add_le_add le_rfl hlogV)
  have hscale : 2+C*L ≤ L^2 := by
    have hh := mul_le_mul_of_nonneg_right hLc hL.le
    nlinarith
  change ‖∑ n ∈ roughBand U V z, w n‖ ≤ _
  rw [weighted_rough_band_cofactor_identity hU hV (Real.exp_pos _).le w]
  calc
    _ ≤ ‖∑ p ∈ primeBand (max U z) V, w p‖+
        ‖∑ m ∈ roughBand 1 V z,
          ∑ p ∈ (primeBand z (m.minFac : ℝ)).filter
            (fun p : ℕ => U < (m : ℝ)*(p : ℝ) ∧ (m : ℝ)*(p : ℝ) ≤ V), w (p*m)‖ := norm_add_le _ _
    _ ≤ L^(-(Bsave+2))+∑ m ∈ roughBand 1 V z, (1/(m : ℝ))*L^(-(Bsave+2)) := by
      apply add_le_add hfirst
      exact (norm_sum_le _ _).trans (sum_le_sum hinner)
    _ = (1+∑ m ∈ roughBand 1 V z, 1/(m : ℝ))*L^(-(Bsave+2)) := by rw [← sum_mul]; ring
    _ ≤ (2+C*L)*L^(-(Bsave+2)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    _ ≤ L^2*L^(-(Bsave+2)) := mul_le_mul_of_nonneg_right hscale (by positivity)
    _ = L^(-Bsave) := by
      rw [← Real.rpow_natCast L 2, ← Real.rpow_add hL]
      congr 1
      norm_num

theorem exists_candidate_small_conductor_relative_power_bound
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q : ℝ} {r : ℕ}
    (hc : 0 < c) (hr : 0 < r) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcenter : (11/5 : ℝ) * (r : ℝ) * c = 1) (A B : ℝ) :
    ∃ J : ℕ, ∀ᶠ L : ℝ in atTop, ∀ jStar : ℕ, J < jStar →
      ∀ N R : ℕ, (N : ℝ) ≤ Real.exp L → (R : ℝ) ≤ L^A →
        candidateSmallPrimitiveTypeIMass c L q r jStar N R ≤
          candidateCoefficientWindowMass c L q r jStar * L^(-B) := by
  obtain ⟨J, hnorm⟩ := exists_candidate_character_relative_power_bound
    hZ hc hr hq0 hq1 hcenter (A+B+2)
  refine ⟨J, ?_⟩
  filter_upwards [hnorm, eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (Real.log 2),
    eventually_ge_atTop (4*primeEulerProductUpperConstant)] with L hnormL hL1 hlog2 hlarge
  intro jStar hj N R hN hR
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  let XA := candidateCoefficientWindowMass c L q r jStar
  have hXA : 0 ≤ XA := by
    apply sum_nonneg
    intro u _
    exact candidate_coefficient_nonneg c L hq0 r jStar u
  have hweight : 0 ≤ XA * L^(-(A+B+2)) := by positivity
  have hD : 1 ≤ Real.exp L := by
    exact (Real.one_le_exp_iff).mpr hL.le
  have hbound := candidate_small_primitive_mass_le c L q r jStar N R
    (fun _ => XA * L^(-(A+B+2))) (fun _ _ => hweight) hD hN (by
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
  have hcard : ((Icc 2 R).card : ℝ) ≤ L^A := (Nat.cast_le.mpr hcardN).trans hR
  have hsum : (∑ _f ∈ Icc 2 R, XA * L^(-(A+B+2))) ≤
      L^A * (XA * L^(-(A+B+2))) := by
    simp only [sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard hweight
  calc
    _ ≤ ((2*primeEulerProductUpperConstant) * Real.log (2*Real.exp L)) *
        ∑ _f ∈ Icc 2 R, XA * L^(-(A+B+2)) := hbound
    _ ≤ ((2*primeEulerProductUpperConstant) * (2*L)) *
        (L^A * (XA * L^(-(A+B+2)))) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hlog (by positivity [primeEulerProductUpperConstant_pos])
      · exact hsum
      · exact sum_nonneg (fun _ _ => hweight)
      · positivity [primeEulerProductUpperConstant_pos]
    _ = (4*primeEulerProductUpperConstant*L) * (L^A * (XA * L^(-(A+B+2)))) := by ring
    _ ≤ (L*L) * (L^A * (XA * L^(-(A+B+2)))) := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_right hlarge hL.le
      · positivity
    _ = XA * ((L^A * L^(2 : ℝ)) * L^(-(A+B+2))) := by rw [Real.rpow_two]; ring
    _ = XA * L^(-B) := by
      rw [← Real.rpow_add hL, ← Real.rpow_add hL]
      congr 2
      ring

theorem eventually_prime_grouped_actual_comparison
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) (c κ s z v D : ℝ)
    (hc : 0 < c) (hκ : 0 ≤ κ) (hs : 0 ≤ s) (hz : 0 ≤ z) (hD : 0 ≤ D) :
    let A₀ := D + 2 * (s + 1)
    let q := 2 * κ + (s + 1) + 2 * A₀ + 3
    let w := 4 * q + max z q + A₀ + 2
    let x := (s + w + 2) + 2 * A₀ + 2
    ∀ᶠ L : ℝ in atTop,
    let Q := ⌊L ^ q⌋₊
    let h := L ^ (-w)
    let ξ := L ^ (-x)
    ∀ {G : Type u} [Fintype G] [DecidableEq G]
      {I : G → Type u} [∀ g, Fintype (I g)] [∀ g, DecidableEq (I g)],
    ∀ (P : G → Finset ℕ) (V : G → ℝ),
    (∀ g, 0 < V g) →
    (∀ g p, p ∈ P g → p.Prime ∧ Q < p) →
    (∀ g, ∑ p ∈ P g, 1 / (p : ℝ) = V g) →
    (∀ g, L ^ (-v) ≤ V g) →
    (∀ g, ∃ a b : ℝ, P g = primeBand a b ∧ Real.exp (L ^ c) ≤ a ∧ 0 ≤ b) →
    ∀ (probes tails : ∀ g, Finset (I g)),
    (∀ g, Disjoint (probes g) (tails g)) →
    ∀ m ell : ℕ, 0 < m →
    (∀ g, (probes g).card = m) → (∀ g, (tails g).card = ell) →
    ∀ r t : Finset G, Disjoint r t →
    ∀ active : Finset (Sigma I), activeᶜ = univ.sigma tails →
    (∀ U ∈ cleanNonemptySubsets (r.sigma probes) ∪ cleanNonemptySubsets (t.sigma probes),
      ∀ a : (∀ i : U, P i.1.1), Real.log (∏ i : U, (a i).val : ℕ) ≤ L ^ s) →
    (∀ U ∈ cleanNonemptySubsets (r.sigma probes) ∪ cleanNonemptySubsets (t.sigma probes),
      ∀ n : ℕ, (∑ a ∈ univ.filter (fun a : (∀ i : U, P i.1.1) => (∏ i : U, (a i).val : ℕ) = n),
        finiteProductWeight (physicalLabelLaw (P := fun i : U => P i.1.1) (fun i => V i.1.1)) a)
          ≤ L ^ κ / (n : ℝ)) →
    ∀ ζ Θ : ℝ, |ζ| ≤ L ^ z →
    ∀ f g : (∀ g, I g → P g) → ℂ,
    (∀ a, finiteGroupSlotSymmetric a f) → (∀ a, finiteGroupSlotSymmetric a g) →
    let kept := fun U : Finset (Sigma I) => primeProductRetainedCells
      (fun i : U => P i.1.1) (fun i => V i.1.1) h ξ
    ‖cleanRawPairing (finiteProductWeight (fun a : Sigma I => physicalLabelLaw V a.1))
            (primeActivePhase (fun a : Sigma I => P a.1) active ζ Θ)
        (finiteGroupedTailTest (physicalLabelLaw V) tails f)
        (finiteGroupedTailTest (physicalLabelLaw V) tails g) -
      ∑ A ∈ cleanNonemptySubsets (r.sigma probes), ∑ B ∈ cleanNonemptySubsets (t.sigma probes),
        (-1 : ℂ) ^ (A.card + B.card) *
          cleanKernelPairing (finiteProductWeight (fun a : Sigma I => physicalLabelLaw V a.1))
            (primeAsymmetricComparisonKernel (fun a : Sigma I => P a.1) (fun a => V a.1)
              active Q h kept kept ζ Θ A B)
            (finiteGroupedTailTest (physicalLabelLaw V) tails f)
            (finiteGroupedTailTest (physicalLabelLaw V) tails g)‖ ≤
      (Real.sqrt (((ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ r.card) +
        Real.sqrt (((ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ t.card) +
        (3 : ℝ) ^ ((r.sigma probes).card + (t.sigma probes).card) * L ^ (-D)) *
        Real.sqrt (finiteWeightedEnergy (finiteProductWeight
          (fun g => finiteProductWeight (fun _ : I g => physicalLabelLaw V g))) f) *
        Real.sqrt (finiteWeightedEnergy (finiteProductWeight
          (fun g => finiteProductWeight (fun _ : I g => physicalLabelLaw V g))) g) := by
  intro A₀ q w x
  filter_upwards [eventually_prime_arbitrary_test_comparison.{u} hZ c κ s z v D hc hκ hs hz hD,
    eventually_gt_atTop (0 : ℝ)] with L hcomp hL
  intro Q h ξ G _ _ I _ _ P V hV hP hmass hVlower hband probes tails hpt
    m ell hm hp ht r t hrt active hactive hlog hatom ζ Θ hζ f g hf hg kept
  apply prime_grouped_block_bound_of_free_tuple_estimates P V hV
    (fun a p hp => (hP a p hp).1.pos) hmass probes tails hpt m ell hm hp ht
    r t hrt active hactive Q h kept kept ζ Θ f g hf hg (L ^ (-D)) (by positivity)
  intro A hA B hB α fA gB
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr ((clean_mem_nonempty_subsets _ _).mp hA).1
  obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr ((clean_mem_nonempty_subsets _ _).mp hB).1
  obtain ⟨a₀, a₁, hPa, ha₀, ha₁⟩ := hband a.1
  obtain ⟨b₀, b₁, hPb, hb₀, hb₁⟩ := hband b.1
  have he := hcomp (fun i : A => P i.1.1) (fun i => V i.1.1) ⟨a, ha⟩
    (fun i : B => P i.1.1) (fun i => V i.1.1) ⟨b, hb⟩
    (fun i => hV i.1.1) (fun i => hV i.1.1)
    (fun i => hP i.1.1) (fun i => hP i.1.1)
    (fun i => hmass i.1.1) (fun i => hmass i.1.1)
    (hVlower a.1) (hVlower b.1) a₀ a₁ b₀ b₁ hPa hPb ha₀ ha₁ hb₀ hb₁
    (hlog A (mem_union_left _ hA)) (hlog B (mem_union_right _ hB))
    (hatom A (mem_union_left _ hA)) (hatom B (mem_union_right _ hB)) fA gB α ζ hζ
  have hEA : 0 ≤ ∑ a : (∀ i : A, P i.1.1),
      finiteProductWeight (physicalLabelLaw (P := fun i : A => P i.1.1) (fun i => V i.1.1)) a *
        ‖fA a‖ ^ 2 := by
    apply sum_nonneg
    intro a _
    apply mul_nonneg _ (sq_nonneg _)
    exact prod_nonneg (fun i _ => physical_label_law_nonneg (P := fun i : A => P i.1.1) (fun i : A => V i.1.1)
      (fun i => (hV i.1.1).le) i (a i))
  dsimp only at he
  rw [Real.sqrt_mul hEA] at he
  simpa only [finiteTwoKernelPairingError, finiteWeightedEnergy, mul_assoc] using he

theorem eventually_prime_grouped_disjoint_pool_comparison
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) (c s z a v D ε : ℝ) (m : ℕ)
    (hc : 0 < c) (hs : 0 ≤ s) (hz : 0 ≤ z) (ha : 0 ≤ a)
    (hv : 0 < v) (hD : 0 ≤ D) (hε : 0 < ε) (hm : 0 < m) :
    let κ := a * Real.log (primeFiberFactorBound v m)
    let s' := s + ε
    let A₀ := D + 2 * (s' + 1)
    let q := 2 * κ + (s' + 1) + 2 * A₀ + 3
    let w := 4 * q + max z q + A₀ + 2
    let x := (s' + w + 2) + 2 * A₀ + 2
    ∀ᶠ L : ℝ in atTop,
    let Q := ⌊L ^ q⌋₊
    let h := L ^ (-w)
    let ξ := L ^ (-x)
    ∀ {G : Type u} [Fintype G] [DecidableEq G]
      {I : G → Type u} [∀ g, Fintype (I g)] [∀ g, DecidableEq (I g)],
    ∀ (P : G → Finset ℕ) (V : G → ℝ),
    Pairwise (fun g h => Disjoint (P g) (P h)) →
    (∀ g p, p ∈ P g → p.Prime ∧ Q < p) →
    (∀ g, ∑ p ∈ P g, 1 / (p : ℝ) = V g) →
    (∀ g, v ≤ V g) →
    (∀ g p, p ∈ P g → Real.log p ≤ L ^ s) →
    (Fintype.card G : ℝ) ≤ a * Real.log L →
    (∀ g, ∃ a b : ℝ, P g = primeBand a b ∧ Real.exp (L ^ c) ≤ a ∧ 0 ≤ b) →
    ∀ (probes tails : ∀ g, Finset (I g)),
    (∀ g, Disjoint (probes g) (tails g)) →
    ∀ ell : ℕ,
    (∀ g, (probes g).card = m) → (∀ g, (tails g).card = ell) →
    ∀ r t : Finset G, Disjoint r t →
    ∀ active : Finset (Sigma I), activeᶜ = univ.sigma tails →
    ∀ ζ Θ : ℝ, |ζ| ≤ L ^ z →
    ∀ f g : (∀ g, I g → P g) → ℂ,
    (∀ a, finiteGroupSlotSymmetric a f) → (∀ a, finiteGroupSlotSymmetric a g) →
    let kept := fun U : Finset (Sigma I) => primeProductRetainedCells
      (fun i : U => P i.1.1) (fun i => V i.1.1) h ξ
    ‖cleanRawPairing (finiteProductWeight (fun a : Sigma I => physicalLabelLaw V a.1))
            (primeActivePhase (fun a : Sigma I => P a.1) active ζ Θ)
        (finiteGroupedTailTest (physicalLabelLaw V) tails f)
        (finiteGroupedTailTest (physicalLabelLaw V) tails g) -
      ∑ A ∈ cleanNonemptySubsets (r.sigma probes), ∑ B ∈ cleanNonemptySubsets (t.sigma probes),
        (-1 : ℂ) ^ (A.card + B.card) *
          cleanKernelPairing (finiteProductWeight (fun a : Sigma I => physicalLabelLaw V a.1))
            (primeAsymmetricComparisonKernel (fun a : Sigma I => P a.1) (fun a => V a.1)
              active Q h kept kept ζ Θ A B)
            (finiteGroupedTailTest (physicalLabelLaw V) tails f)
            (finiteGroupedTailTest (physicalLabelLaw V) tails g)‖ ≤
      (Real.sqrt (((ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ r.card) +
        Real.sqrt (((ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ t.card) +
        (3 : ℝ) ^ ((r.sigma probes).card + (t.sigma probes).card) * L ^ (-D)) *
        Real.sqrt (finiteWeightedEnergy (finiteProductWeight
          (fun g => finiteProductWeight (fun _ : I g => physicalLabelLaw V g))) f) *
        Real.sqrt (finiteWeightedEnergy (finiteProductWeight
          (fun g => finiteProductWeight (fun _ : I g => physicalLabelLaw V g))) g) := by
  intro κ s' A₀ q w x
  have hκ : 0 ≤ a * Real.log (primeFiberFactorBound v m) :=
    mul_nonneg ha (Real.log_nonneg (one_le_primeFiberFactorBound v m))
  filter_upwards [eventually_prime_grouped_actual_comparison.{u} hZ c
    (a * Real.log (primeFiberFactorBound v m)) (s + ε) z 1 D hc hκ
    (add_nonneg hs hε.le) hz hD,
    eventually_prime_subset_product_log_rpow a s ε m hs hε,
    eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (1 / v)]
    with L hcomp hlogs hL hlarge
  intro Q h ξ G _ _ I _ _ P V hdisj hP hmass hV hlog hcard hband
    probes tails hpt ell hp ht r t hrt active hactive ζ Θ hζ f g hf hg kept
  have hVpos (g : G) : 0 < V g := hv.trans_le (hV g)
  have hVlower (g : G) : L ^ (-1 : ℝ) ≤ V g := by
    have hb := one_div_le_one_div_of_le (one_div_pos.mpr hv) hlarge
    have hb' : 1 / L ≤ v := by simpa only [one_div_one_div] using hb
    simpa only [Real.rpow_neg_one, one_div] using hb'.trans (hV g)
  have hprime (g : G) (p : ℕ) (hp : p ∈ P g) : p.Prime := (hP g p hp).1
  have hpos (g : G) (p : ℕ) (hp : p ∈ P g) : 0 < p := (hprime g p hp).pos
  have hm' (g : G) : (probes g).card ≤ m := (hp g).le
  apply hcomp P V hVpos hP hmass hVlower hband probes tails hpt m ell hm hp ht
    r t hrt active hactive ?_ ?_ ζ Θ hζ f g hf hg
  · intro U hU b
    rcases mem_union.mp hU with hU | hU
    · exact hlogs P r probes hm' hpos hlog hcard U
        ((clean_mem_nonempty_subsets _ _).mp hU).2 b
    · exact hlogs P t probes hm' hpos hlog hcard U
        ((clean_mem_nonempty_subsets _ _).mp hU).2 b
  · intro U hU n
    rcases mem_union.mp hU with hU | hU
    · exact prime_subset_physical_atom_rpow P V hprime hdisj r probes m hv hL hV hm'
        hcard U ((clean_mem_nonempty_subsets _ _).mp hU).2 n
    · exact prime_subset_physical_atom_rpow P V hprime hdisj t probes m hv hL hV hm'
        hcard U ((clean_mem_nonempty_subsets _ _).mp hU).2 n

theorem eventually_repeated_big_prime_disjoint_pool_comparison
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) (c s z a v D ε : ℝ) (m : ℕ)
    (hc : 0 < c) (hs : 0 ≤ s) (hz : 0 ≤ z) (ha : 0 ≤ a)
    (hv : 0 < v) (hD : 0 ≤ D) (hε : 0 < ε) (hm : 0 < m) :
    let κ := a * Real.log (primeFiberFactorBound v m)
    let s' := s + ε
    let A₀ := D + 2 * (s' + 1)
    let q := 2 * κ + (s' + 1) + 2 * A₀ + 3
    let w := 4 * q + max z q + A₀ + 2
    let x := (s' + w + 2) + 2 * A₀ + 2
    ∀ᶠ L : ℝ in atTop,
    let Q := ⌊L ^ q⌋₊
    let h := L ^ (-w)
    let ξ := L ^ (-x)
    ∀ {G : Type} [Fintype G] [DecidableEq G] (J ell : ℕ),
    ∀ (P : G → Finset ℕ) (V : G → ℝ),
    Pairwise (fun g h => Disjoint (P g) (P h)) →
    (∀ g p, p ∈ P g → p.Prime ∧ Q < p) →
    (∀ g, ∑ p ∈ P g, 1 / (p : ℝ) = V g) →
    (∀ g, v ≤ V g) →
    (∀ g p, p ∈ P g → Real.log p ≤ L ^ s) →
    (Fintype.card G : ℝ) ≤ a * Real.log L →
    (∀ g, ∃ a b : ℝ, P g = primeBand a b ∧ Real.exp (L ^ c) ≤ a ∧ 0 ≤ b) →
    ∀ probes : G → Finset (Fin J), (∀ g, (probes g).card = m) →
    ∀ r t : Finset G, Disjoint r t →
    ∀ ζ Θ : ℝ, |ζ| ≤ L ^ z →
    ∀ f g : RepeatedBigLists P J ell → ℂ,
    f ∈ repeatedBigSymmetricSubspace → g ∈ repeatedBigSymmetricSubspace →
    let slots := fun g => (probes g).map (Function.Embedding.inl (β := Fin ell))
    let kept := fun U : Finset (RepeatedBigFlatIndex G J ell) => primeProductRetainedCells
      (fun i : U => P i.1.1) (fun i => V i.1.1) h ξ
    ‖cleanKernelPairing (repeatedBigActiveMass V (fun _ _ => 1))
        (repeatedBigPrimeRawRow P V ζ Θ) f g -
      ∑ A ∈ cleanNonemptySubsets (r.sigma slots), ∑ B ∈ cleanNonemptySubsets (t.sigma slots),
        (-1 : ℂ) ^ (A.card + B.card) *
          cleanKernelPairing (repeatedBigActiveMass V (fun _ _ => 1))
            (repeatedBigPrimeComparisonRow P V A B Q h kept kept ζ Θ) f g‖ ≤
      (Real.sqrt (((ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ r.card) +
        Real.sqrt (((ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ t.card) +
        (3 : ℝ) ^ ((r.sigma slots).card + (t.sigma slots).card) * L ^ (-D)) *
        Real.sqrt (finiteWeightedEnergy (repeatedBigActiveMass V (fun _ _ => 1)) f) *
        Real.sqrt (finiteWeightedEnergy (repeatedBigActiveMass V (fun _ _ => 1)) g) := by
  intro κ s' A₀ q w x
  filter_upwards [eventually_prime_grouped_disjoint_pool_comparison.{0}
    hZ c s z a v D ε m hc hs hz ha hv hD hε hm] with L hcomp
  intro Q h ξ G _ _ J ell P V hdisj hP hmass hV hlog hcard hband
    probes hp r t hrt ζ Θ hζ f g hf hg slots kept
  have hVpos (j : G) : 0 < V j := hv.trans_le (hV j)
  have hPpos (j : G) (p : ℕ) (hp : p ∈ P j) : 0 < p := (hP j p hp).1.pos
  have hμ (j : G) (p : P j) : physicalLabelLaw V j p ≠ 0 := by
    unfold physicalLabelLaw
    apply div_ne_zero one_ne_zero
    exact mul_ne_zero (hVpos j).ne' (by exact_mod_cast (hPpos j p.val p.property).ne')
  have hslots (j : G) : Disjoint (slots j) (repeatedBigPrimeTailSlots J ell) := by
    apply disjoint_left.mpr
    intro i hi ht
    rcases mem_map.mp hi with ⟨k, _, rfl⟩
    rcases mem_map.mp ht with ⟨l, _, he⟩
    cases he
  have hcount (j : G) : (slots j).card = m := by
    simpa only [slots, card_map] using hp j
  have htailcount (j : G) : (repeatedBigPrimeTailSlots J ell).card = ell := by
    simp only [repeatedBigPrimeTailSlots, card_map, card_univ, Fintype.card_fin]
  have hbound := hcomp P V hdisj hP hmass hV hlog hcard hband slots
    (fun _ => repeatedBigPrimeTailSlots J ell) hslots ell hcount htailcount
    r t hrt (repeatedBigFlatActive J ell) (repeatedBigPrimeTailSlots_compl J ell)
    ζ Θ hζ f g ((repeated_big_symmetric_iff_group_slot_symmetric f).mp hf)
      ((repeated_big_symmetric_iff_group_slot_symmetric g).mp hg)
  have hraw := repeated_big_prime_raw_pairing P V
    (fun j => physical_label_law_sum V j (hVpos j) (hmass j)) hμ ζ Θ f g
  change cleanKernelPairing (repeatedBigActiveMass V (fun _ _ => 1))
    (repeatedBigPrimeRawRow P V ζ Θ) f g = _ at hraw
  have hsub (u : Finset G) : u.sigma slots ⊆ repeatedBigFlatActive J ell := by
    rintro ⟨j, i⟩ hi
    rcases mem_map.mp (mem_sigma.mp hi).2 with ⟨k, _, rfl⟩
    exact repeatedBigFlatActive_mem_inl J ell j k
  have hrt' : Disjoint (r.sigma slots) (t.sigma slots) := by
    apply disjoint_left.mpr
    intro i hi hj
    exact disjoint_left.mp hrt (mem_sigma.mp hi).1 (mem_sigma.mp hj).1
  have hpair (A : Finset (RepeatedBigFlatIndex G J ell))
      (hA : A ∈ cleanNonemptySubsets (r.sigma slots))
      (B : Finset (RepeatedBigFlatIndex G J ell))
      (hB : B ∈ cleanNonemptySubsets (t.sigma slots)) :
      cleanKernelPairing (repeatedBigActiveMass V (fun _ _ => 1))
          (repeatedBigPrimeComparisonRow P V A B Q h kept kept ζ Θ) f g =
        cleanKernelPairing
          (finiteProductWeight (fun i : RepeatedBigFlatIndex G J ell => physicalLabelLaw V i.1))
          (primeAsymmetricComparisonKernel (fun i : RepeatedBigFlatIndex G J ell => P i.1)
            (fun i => V i.1) (repeatedBigFlatActive J ell) Q h kept kept ζ Θ A B)
          (finiteGroupedTailTest (physicalLabelLaw V) (fun _ => repeatedBigPrimeTailSlots J ell) f)
          (finiteGroupedTailTest (physicalLabelLaw V) (fun _ => repeatedBigPrimeTailSlots J ell) g) := by
    have ha := ((clean_mem_nonempty_subsets _ _).mp hA).2
    have hb := ((clean_mem_nonempty_subsets _ _).mp hB).2
    simpa only [finiteGroupedTailTest, repeatedBigPrimeTailSlots_compl] using
      repeated_big_prime_comparison_pairing_tail_eq P V hVpos hPpos hmass A B
        (ha.trans (hsub r)) (hb.trans (hsub t)) (hrt'.mono ha hb)
        Q h kept kept ζ Θ f g
  have hsum :
      (∑ A ∈ cleanNonemptySubsets (r.sigma slots), ∑ B ∈ cleanNonemptySubsets (t.sigma slots),
        (-1 : ℂ) ^ (A.card + B.card) *
          cleanKernelPairing (repeatedBigActiveMass V (fun _ _ => 1))
            (repeatedBigPrimeComparisonRow P V A B Q h kept kept ζ Θ) f g) =
      ∑ A ∈ cleanNonemptySubsets (r.sigma slots), ∑ B ∈ cleanNonemptySubsets (t.sigma slots),
        (-1 : ℂ) ^ (A.card + B.card) *
          cleanKernelPairing
            (finiteProductWeight (fun i : RepeatedBigFlatIndex G J ell => physicalLabelLaw V i.1))
            (primeAsymmetricComparisonKernel (fun i : RepeatedBigFlatIndex G J ell => P i.1)
              (fun i => V i.1) (repeatedBigFlatActive J ell) Q h kept kept ζ Θ A B)
            (finiteGroupedTailTest (physicalLabelLaw V) (fun _ => repeatedBigPrimeTailSlots J ell) f)
            (finiteGroupedTailTest (physicalLabelLaw V) (fun _ => repeatedBigPrimeTailSlots J ell) g) := by
    apply sum_congr rfl
    intro A hA
    apply sum_congr rfl
    intro B hB
    rw [hpair A hA B hB]
  rw [hraw, hsum, repeated_big_active_mass_product V]
  exact hbound

theorem exists_candidate_typeI_remainder_bound_of_large
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q θ : ℝ} {r : ℕ}
    (hc : 0 < c) (hr : 0 < r) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcenter : (11/5 : ℝ) * (r : ℝ) * c = 1) (hθ : θ ≤ 1)
    (hlarge : ∀ B : ℝ, ∀ᶠ L : ℝ in atTop, ∀ jStar : ℕ, 0 < jStar →
      ∀ N : ℕ, (N : ℝ) ≤ Real.exp (θ * L) →
        candidateLargePrimitiveTypeIMass c L q r jStar N ⌊Real.exp ((c/512)*L)⌋₊ ≤
          Real.exp L * L^(-B)) (D : ℝ) :
    ∃ J : ℕ, ∀ᶠ L : ℝ in atTop, ∀ jStar : ℕ, J < jStar →
      ∀ N : ℕ, (N : ℝ) ≤ Real.exp (θ * L) →
        (∑ d ∈ oddSquarefreeModuli N,
          |shiftedTotientSieveRemainder (arithmeticProductWindow 1 (Real.exp L))
            (candidateCoefficient c L q r jStar) d|) ≤
          Real.exp L * L^(-D) + candidateCoefficientWindowMass c L q r jStar *
            ((16 * primeEulerProductUpperConstant) * L^(-18 : ℝ)) := by
  obtain ⟨C, _, hmass⟩ :=
    exists_candidate_coefficient_mass_polynomial_upper_uniform hc hr hq0 hq1.le
  obtain ⟨J, hsmall⟩ :=
    exists_candidate_exponential_conductor_range_power_bound hZ hc hr hq0 hq1 hcenter (C + D + 1)
  refine ⟨J, ?_⟩
  filter_upwards [hmass, hsmall, hlarge (D + 1),
    eventually_candidate_typeI_remainder_le_primitive hc,
    eventually_ge_atTop (2 : ℝ)] with L hm hs hl hrem hL
  intro jStar hj N hN
  have hjpos : 0 < jStar := lt_of_le_of_lt (Nat.zero_le _) hj
  have hL0 : 0 ≤ L := by linarith
  have hN' : (N : ℝ) ≤ Real.exp L := hN.trans
    (Real.exp_le_exp.mpr (by nlinarith only [hθ, hL0]))
  have hR : (⌊Real.exp ((c/512)*L)⌋₊ : ℝ) ≤ Real.exp ((c/512)*L) :=
    Nat.floor_le (Real.exp_pos _).le
  have hprim := candidate_primitive_typeI_mass_bound_of_split c L q C D
    r jStar N ⌊Real.exp ((c/512)*L)⌋₊ hL (hm jStar hjpos)
    (hs jStar hj N _ hN' hR) (hl jStar hjpos N hN)
  exact (hrem q hq0 r jStar N hN').trans (add_le_add hprim le_rfl)

theorem exists_candidate_typeI_remainder_power_bound
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q θ : ℝ} {r : ℕ}
    (hc : 0 < c) (hr : 0 < r) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcenter : (11/5 : ℝ) * (r : ℝ) * c = 1) (hθ : θ < 1/2) (D : ℝ) :
    ∃ J : ℕ, ∀ᶠ L : ℝ in atTop, ∀ jStar : ℕ, J < jStar →
      ∀ N : ℕ, (N : ℝ) ≤ Real.exp (θ * L) →
        (∑ d ∈ oddSquarefreeModuli N,
          |shiftedTotientSieveRemainder (arithmeticProductWindow 1 (Real.exp L))
            (candidateCoefficient c L q r jStar) d|) ≤
          Real.exp L * L^(-D) + candidateCoefficientWindowMass c L q r jStar *
            ((16 * primeEulerProductUpperConstant) * L^(-18 : ℝ)) := by
  apply exists_candidate_typeI_remainder_bound_of_large hZ hc hr hq0 hq1 hcenter
    (by linarith : θ ≤ 1) ?_ D
  intro B
  exact eventually_candidate_large_primitive_power_saving hc hr hcenter hq0 hq1 hθ B

theorem eventually_repeated_big_prime_projected_norm_le
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) (c s z a v D ε : ℝ) (m : ℕ)
    (hc : 0 < c) (hs : 0 ≤ s) (hz : 0 ≤ z) (ha : 0 ≤ a)
    (hv : 0 < v) (hD : 0 ≤ D) (hε : 0 < ε) (hm : 0 < m) :
    let κ := a * Real.log (primeFiberFactorBound v m)
    let s' := s + ε
    let A₀ := D + 2 * (s' + 1)
    let q := 2 * κ + (s' + 1) + 2 * A₀ + 3
    let w := 4 * q + max z q + A₀ + 2
    let x := (s' + w + 2) + 2 * A₀ + 2
    ∀ᶠ L : ℝ in atTop,
    let Q := ⌊L ^ q⌋₊
    let h := L ^ (-w)
    let ξ := L ^ (-x)
    ∀ {G : Type} [Fintype G] [DecidableEq G] (J ell : ℕ),
    ∀ (P : G → Finset ℕ) (V : G → ℝ),
    Pairwise (fun g h => Disjoint (P g) (P h)) →
    (∀ g p, p ∈ P g → p.Prime ∧ Q < p) →
    (∀ g, ∑ p ∈ P g, 1 / (p : ℝ) = V g) →
    (∀ g, v ≤ V g) →
    (∀ g p, p ∈ P g → Real.log p ≤ L ^ s) →
    (Fintype.card G : ℝ) ≤ a * Real.log L →
    (∀ g, ∃ a b : ℝ, P g = primeBand a b ∧ Real.exp (L ^ c) ≤ a ∧ 0 ≤ b) →
    ∀ probes : G → Finset (Fin J), (∀ g, (probes g).card = m) →
    ∀ r t : Finset G, Disjoint r t →
    ∀ ζ Θ : ℝ, |ζ| ≤ L ^ z →
    ∀ u : RepeatedBigLists P J ell → ℂ, u ∈ repeatedBigSymmetricSubspace →
    let slots := fun g => (probes g).map (Function.Embedding.inl (β := Fin ell))
    let kept := fun U : Finset (RepeatedBigFlatIndex G J ell) => primeProductRetainedCells
      (fun i : U => P i.1.1) (fun i => V i.1.1) h ξ
    cleanActiveNorm (repeatedBigActiveMass V (fun _ _ => 1))
      (repeatedBigSymmetrizeLinear (fun source => ∑ target,
        repeatedBigPrimeDifferenceKernel P V probes r t Q h kept ζ Θ source target * u target)) ≤
      (Real.sqrt (((ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ r.card) +
        Real.sqrt (((ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ t.card) +
        (3 : ℝ) ^ ((r.sigma slots).card + (t.sigma slots).card) * L ^ (-D)) *
        cleanActiveNorm (repeatedBigActiveMass V (fun _ _ => 1)) u := by
  intro κ s' A₀ q w x
  filter_upwards [eventually_repeated_big_prime_disjoint_pool_comparison
    hZ c s z a v D ε m hc hs hz ha hv hD hε hm, eventually_gt_atTop (0 : ℝ)] with L hcomp hL
  intro Q h ξ G _ _ J ell P V hdisj hP hmass hV hlog hcard hband
    probes hp r t hrt ζ Θ hζ u hu slots kept
  apply repeated_big_kernel_norm_le_of_bilinear V (fun j => (hv.trans_le (hV j)).le)
    (repeatedBigPrimeDifferenceKernel P V probes r t Q h kept ζ Θ) (by positivity) _ u hu
  intro f g hf hg
  rw [repeated_big_prime_difference_pairing]
  exact hcomp J ell P V hdisj hP hmass hV hlog hcard hband probes hp r t hrt ζ Θ hζ f g hf hg

theorem eventually_prime_proxy_character_discrepancy (hZ : PrimitiveZeroFreeRightOf (23 / 24))
    {a S T Bsave : ℝ} (ha : 0 < a) (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hprecision : T+Bsave+2 ≤ S) :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ, Real.exp (a*L) ≤ Y →
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), (r : ℝ) ≤ L^T →
      ∀ v : ℝ, |v| ≤ L^T → ∀ m n : ℕ, m ≤ n → Y ≤ (m+1 : ℕ) → (n : ℝ) ≤ 2*Y →
        ‖∑ i ∈ Ioc m n,
          (((if i.Prime then 1 else 0 : ℝ)-primeLogarithmicProxy L S i : ℝ) : ℂ)*
            harmonicMellinWeight v i*χ (i : ZMod r)‖ ≤ L^(-Bsave) := by
  filter_upwards [eventually_prime_proxy_mellin_difference_bound ha hS hT hprecision,
    eventually_prime_logarithmic_proxy_principal_identity ha S T,
    eventually_prime_interval_mellin_power_bound hZ ha hT (Bsave+1),
    eventually_prime_logarithmic_proxy_mellin_power_bound ha hS hT (Bsave+1),
    eventually_ge_atTop (2 : ℝ)] with L hprincipal hidentity hprime hproxy hL2
  have hL : 0 < L := by linarith
  intro Y hY r hr χ hrT v hv m n hmn hYm hn
  have hrpos : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  by_cases hχ : χ = 1
  · subst χ
    have heq : (∑ i ∈ Ioc m n,
        (((if i.Prime then 1 else 0 : ℝ)-primeLogarithmicProxy L S i : ℝ) : ℂ)*
          harmonicMellinWeight v i*(1 : DirichletCharacter ℂ r) (i : ZMod r)) =
        ∑ i ∈ Ioc m n,
          (((if i.Prime then 1 else 0 : ℝ)-primeLogarithmicProxy L S i : ℝ) : ℂ)*
            harmonicMellinWeight v i := by
      apply sum_congr rfl
      intro i hi
      have hiY : Real.exp (a*L) ≤ (i : ℝ) := hY.trans (hYm.trans (Nat.cast_le.mpr (mem_Ioc.mp hi).1))
      have hiid := hidentity i hiY r hrpos hrT
      calc
        _ = ((((if i.Prime then 1 else 0 : ℝ)-primeLogarithmicProxy L S i : ℝ) : ℂ)*
            (1 : DirichletCharacter ℂ r) (i : ZMod r))*harmonicMellinWeight v i := by ring
        _ = _ := by rw [hiid]
    rw [heq]
    exact hprincipal Y hY v hv m n hmn hYm hn
  · have hp := hprime Y hY r hrpos hrT χ hχ v hv m n hmn hYm hn
    have hb := hproxy Y hY r χ hχ hrT v hv m n hmn hYm hn
    have heq : (∑ i ∈ Ioc m n,
        (((if i.Prime then 1 else 0 : ℝ)-primeLogarithmicProxy L S i : ℝ) : ℂ)*
          harmonicMellinWeight v i*χ (i : ZMod r)) =
        (∑ i ∈ (Ioc m n).filter Nat.Prime, harmonicMellinWeight v i*χ (i : ZMod r))-
        ∑ i ∈ Ioc m n, (primeLogarithmicProxy L S i : ℂ)*
          harmonicMellinWeight v i*χ (i : ZMod r) := by
      simp only [sum_filter, Complex.ofReal_sub, sub_mul, sum_sub_distrib]
      congr 1
      apply sum_congr rfl
      intro i _
      by_cases hi : i.Prime <;> simp [hi]
    rw [heq]
    apply (norm_sub_le _ _).trans
    apply (add_le_add hp hb).trans
    have he : L^(-(Bsave+1)) = L^(-Bsave)/L := by
      rw [show -(Bsave+1) = -Bsave+(-1) by ring, Real.rpow_add hL, Real.rpow_neg_one]
      ring
    rw [he, ← add_div]
    apply (div_le_iff₀ hL).mpr
    nlinarith [mul_le_mul_of_nonneg_left hL2 (Real.rpow_nonneg hL.le (-Bsave))]

theorem eventually_rough_test_proxy_character_discrepancy (hZ : PrimitiveZeroFreeRightOf (23 / 24))
    {a γ C S T Bsave : ℝ} (ha : 0 < a) (hγ : 0 < γ) (hC : 0 < C)
    (hS : 0 ≤ S) (hT : 0 ≤ T) (hprecision : T+Bsave+2 ≤ S) :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ, Real.exp (a*L) ≤ Y → Y ≤ Real.exp (C*L) →
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), (r : ℝ) ≤ L^T →
      ∀ v : ℝ, |v| ≤ L^T → ∀ m n : ℕ, m ≤ n → Y ≤ (m+1 : ℕ) → (n : ℝ) ≤ 2*Y →
        ‖∑ i ∈ Ioc m n,
          ((roughTestIndicator γ L i-roughTestLogarithmicProxy γ L S i : ℝ) : ℂ)*
            harmonicMellinWeight v i*χ (i : ZMod r)‖ ≤ L^(-Bsave) := by
  classical
  have hC1 : 0 < C+1 := by linarith
  filter_upwards [eventually_rough_test_proxy_mellin_difference_bound ha hγ hS hT hprecision,
    eventually_rough_test_proxy_principal_identity hγ S T,
    eventually_exponential_rough_test_mellin_bound hZ hγ hC1 hT (Bsave+1),
    eventually_rough_test_logarithmic_proxy_mellin_power_bound ha hγ hS hT (Bsave+1),
    eventually_ge_atTop (2 : ℝ), eventually_ge_atTop (2/a)]
    with L hprincipal hidentity hrough hproxy hL2 hLa
  have hL : 0 < L := by linarith
  intro Y hY hYup r hr χ hrT v hv m n hmn hYm hn
  have hrpos : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hY3 : 3 ≤ Y := by
    have hLa' := (div_le_iff₀ ha).mp hLa
    have hexp := Real.add_one_le_exp (a*L)
    nlinarith
  have hm1 : 1 ≤ (m : ℝ) := by
    push_cast at hYm
    linarith
  have hnexp : (n : ℝ) ≤ Real.exp ((C+1)*L) := by
    have htwo : 2 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
    calc
      _ ≤ 2*Y := hn
      _ ≤ 2*Real.exp (C*L) := mul_le_mul_of_nonneg_left hYup (by norm_num)
      _ ≤ Real.exp L*Real.exp (C*L) := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = Real.exp ((C+1)*L) := by rw [← Real.exp_add]; congr 1; ring
  by_cases hχ : χ = 1
  · subst χ
    have heq : (∑ i ∈ Ioc m n,
        ((roughTestIndicator γ L i-roughTestLogarithmicProxy γ L S i : ℝ) : ℂ)*
          harmonicMellinWeight v i*(1 : DirichletCharacter ℂ r) (i : ZMod r)) =
        ∑ i ∈ Ioc m n,
          ((roughTestIndicator γ L i-roughTestLogarithmicProxy γ L S i : ℝ) : ℂ)*
            harmonicMellinWeight v i := by
      apply sum_congr rfl
      intro i hi
      have hi0 : 0 < i := lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp hi).1
      have hiid := hidentity i hi0 r hrpos hrT
      calc
        _ = (((roughTestIndicator γ L i-roughTestLogarithmicProxy γ L S i : ℝ) : ℂ)*
            (1 : DirichletCharacter ℂ r) (i : ZMod r))*harmonicMellinWeight v i := by ring
        _ = _ := by rw [hiid]
    rw [heq]
    exact hprincipal Y hY v hv m n hmn hYm hn
  · have hp := hrough (m : ℝ) (n : ℝ) hm1 (Nat.cast_nonneg _) hnexp r hrpos hrT χ hχ v hv
    have hb := hproxy Y hY r χ hχ hrT v hv m n hmn hYm hn
    have heq : (∑ i ∈ Ioc m n,
        ((roughTestIndicator γ L i-roughTestLogarithmicProxy γ L S i : ℝ) : ℂ)*
          harmonicMellinWeight v i*χ (i : ZMod r)) =
        (∑ i ∈ roughBand (m : ℝ) (n : ℝ) (Real.exp (γ*L)), harmonicMellinWeight v i*χ (i : ZMod r))-
        ∑ i ∈ Ioc m n, (roughTestLogarithmicProxy γ L S i : ℂ)*
          harmonicMellinWeight v i*χ (i : ZMod r) := by
      simp only [roughBand, Nat.floor_natCast, sum_filter, Complex.ofReal_sub, sub_mul, sum_sub_distrib]
      congr 1
      apply sum_congr rfl
      intro i _
      by_cases hi : exponentialRoughTest γ L i
      · simp only [roughTestIndicator, if_pos hi, Complex.ofReal_one, one_mul]
        unfold exponentialRoughTest at hi
        rw [if_pos hi]
      · simp only [roughTestIndicator, if_neg hi, Complex.ofReal_zero, zero_mul]
        unfold exponentialRoughTest at hi
        rw [if_neg hi]
    rw [heq]
    apply (norm_sub_le _ _).trans
    apply (add_le_add hp hb).trans
    have he : L^(-(Bsave+1)) = L^(-Bsave)/L := by
      rw [show -(Bsave+1) = -Bsave+(-1) by ring, Real.rpow_add hL, Real.rpow_neg_one]
      ring
    rw [he, ← add_div]
    apply (div_le_iff₀ hL).mpr
    nlinarith [mul_le_mul_of_nonneg_left hL2 (Real.rpow_nonneg hL.le (-Bsave))]

theorem eventually_repeated_big_prime_pattern_norm_le
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) (c s z a v D ε : ℝ) (m : ℕ)
    (hc : 0 < c) (hs : 0 ≤ s) (hz : 0 ≤ z) (ha : 0 ≤ a)
    (hv : 0 < v) (hD : 0 ≤ D) (hε : 0 < ε) (hm : 0 < m) :
    let κ := a * Real.log (primeFiberFactorBound v m)
    let s' := s + ε
    let A₀ := D + 2 * (s' + 1)
    let q := 2 * κ + (s' + 1) + 2 * A₀ + 3
    let w := 4 * q + max z q + A₀ + 2
    let x := (s' + w + 2) + 2 * A₀ + 2
    ∀ᶠ L : ℝ in atTop,
    let Q := ⌊L ^ q⌋₊
    let h := L ^ (-w)
    let ξ := L ^ (-x)
    ∀ {G : Type} [Fintype G] [DecidableEq G] (J ell : ℕ),
    ∀ (P : G → Finset ℕ) (V : G → ℝ),
    Pairwise (fun g h => Disjoint (P g) (P h)) →
    (∀ g p, p ∈ P g → p.Prime ∧ Q < p) →
    (∀ g, ∑ p ∈ P g, 1 / (p : ℝ) = V g) →
    (∀ g, v ≤ V g) →
    (∀ g p, p ∈ P g → Real.log p ≤ L ^ s) →
    (Fintype.card G : ℝ) ≤ a * Real.log L →
    (∀ g, ∃ a b : ℝ, P g = primeBand a b ∧ Real.exp (L ^ c) ≤ a ∧ 0 ≤ b) →
    ∀ probes : G → Finset (Fin J), (∀ g, (probes g).card = m) →
    ∀ r t : Finset G, ∀ hrt : Disjoint r t,
    ∀ ζ Θ : ℝ, |ζ| ≤ L ^ z →
    ∀ u : RepeatedBigLists P J ell → ℂ, u ∈ repeatedBigSymmetricSubspace →
    let slots := fun g => (probes g).map (Function.Embedding.inl (β := Fin ell))
    let kept := fun U : Finset (RepeatedBigFlatIndex G J ell) => primeProductRetainedCells
      (fun i : U => P i.1.1) (fun i => V i.1.1) h ξ
    cleanActiveNorm (repeatedBigActiveMass V (fun _ _ => 1))
      (repeatedBigSymmetrizeLinear (fun source => ∑ target,
        (∑ i : RepeatedBigPrimePatternIndex (ell := ell) probes r t,
          ∑ aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t i),
            repeatedBigPrimePatternWeight probes r t i *
              repeatedBigUnbannedKernel V (fun _ _ => 1)
                (repeatedBigPrimePatternCut probes r t i) ζ
                (repeatedBigPrimePatternKernel P V probes r t hrt Q h kept i)
                aux source target *
              physicalReturnPhase Θ
                (repeatedBigD (repeatedBigPrimePatternCut probes r t i) source aux)) * u target)) ≤
      (Real.sqrt (((ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ r.card) +
        Real.sqrt (((ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ t.card) +
        (3 : ℝ) ^ ((r.sigma slots).card + (t.sigma slots).card) * L ^ (-D)) *
        cleanActiveNorm (repeatedBigActiveMass V (fun _ _ => 1)) u := by
  intro κ s' A₀ q w x
  filter_upwards [eventually_repeated_big_prime_projected_norm_le
    hZ c s z a v D ε m hc hs hz ha hv hD hε hm] with L hnorm
  intro Q h ξ G _ _ J ell P V hdisj hP hmass hV hlog hcard hband
    probes hp r t hrt ζ Θ hζ u hu slots kept
  have hb := hnorm J ell P V hdisj hP hmass hV hlog hcard hband
    probes hp r t hrt ζ Θ hζ u hu
  simpa only [repeated_big_prime_pattern_family_kernel] using hb

theorem exists_candidate_prime_band_rough_mass_estimate (hZ : PrimitiveZeroFreeRightOf (23 / 24)) :
    ∃ K : ℝ, 0 < K ∧ ∀ (c q b a v : ℝ) (r h : ℕ),
      0 < c → 0 < r → 0 ≤ q → q < 1 →
      (11/5 : ℝ)*(r : ℝ)*c = 1 →
      0 < b → b ≤ a → a ≤ v → 1 ≤ h → Even h →
      v+b*(4*(h : ℝ)+2) < 1/2 →
      ∃ J : ℕ, ∀ jStar : ℕ, J < jStar → ∀ᶠ L : ℝ in atTop,
        |candidatePrimeBandRoughMass c L q r jStar
            (Real.exp (a*L)) (Real.exp (v*L)) (Real.exp (b*L)) -
          candidateCoefficientWindowMass c L q r jStar *
            shiftedPrimeAvoidanceProduct (Real.exp (b*L)) *
              (∑ p ∈ primeBand (Real.exp (a*L)) (Real.exp (v*L)),
                1 / ((p : ℝ)-1))| ≤
          candidateCoefficientWindowMass c L q r jStar *
            shiftedPrimeAvoidanceProduct (Real.exp (b*L)) *
              (∑ p ∈ primeBand (Real.exp (a*L)) (Real.exp (v*L)),
                1 / ((p : ℝ)-1)) * K * Real.exp (-(h : ℝ)) +
          candidateCoefficientWindowMass c L q r jStar *
            ((1+16*primeEulerProductUpperConstant)*L^(-18 : ℝ)) := by
  classical
  obtain ⟨K, hK, hsieve⟩ := exists_summed_external_odd_prime_shifted_sieve
  refine ⟨K, hK, ?_⟩
  intro c q b a v r h hc hr hq0 hq1 hcenter hb hba hav hh heven hlevel
  let theta : ℝ := (v+b*(4*(h : ℝ)+2)+1/2)/2
  have htheta : theta < 1/2 := by dsimp [theta]; linarith only [hlevel]
  have ha : 0 < a := hb.trans_le hba
  have hv : 0 < v := ha.trans_le hav
  have hgap : v+b*(4*(h : ℝ)+2) < theta := by
    dsimp [theta]; linarith only [hlevel]
  have hbase : 0 ≤ v+b*(4*(h : ℝ)+2) := by positivity
  obtain ⟨J, hdist⟩ := exists_candidate_relative_typeI_remainder_power_bound
    hZ hc hr hq0 hq1 hcenter htheta (18 : ℝ)
  refine ⟨J, ?_⟩
  intro jStar hj
  filter_upwards [hdist jStar hj, eventually_exp_le_floor_exp hbase hgap,
    eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (Real.log 2/a)]
    with L hd hscale hL hLa
  let N : ℕ := ⌊Real.exp (theta*L)⌋₊
  let P : Finset ℕ := (primeBand 0 (Real.exp (b*L))).erase 2
  let Q : Finset ℕ := primeBand (Real.exp (a*L)) (Real.exp (v*L))
  have hz : 1 < Real.exp (b*L) := Real.one_lt_exp_iff.mpr (mul_pos hb hL)
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
    have hpmax := small_prime_pool_le (Real.exp_pos (b*L)).le (mem_of_mem_erase hpP)
    have hcut : Real.exp (b*L) ≤ Real.exp (a*L) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hba hL.le)
    exact (not_lt_of_ge (hpmax.trans hcut)) (hQlower p hp)
  have hprodlevel : ∀ p ∈ Q, ∀ d ∈ blockSieveModuli P
      ((Real.exp (b*L))^(4*(h : ℝ)+2)), p*d ≤ N := by
    intro p hp d hd
    have hdmax := (block_sieve_modulus_properties P hP _ hd).2.1
    have hprod : (p : ℝ)*(d : ℝ) ≤ Real.exp ((v+b*(4*(h : ℝ)+2))*L) := by
      calc
        _ ≤ Real.exp (v*L)*((Real.exp (b*L))^(4*(h : ℝ)+2)) :=
          mul_le_mul (hQupper p hp) hdmax (Nat.cast_nonneg d) (Real.exp_pos _).le
        _ = _ := by
          rw [← Real.exp_mul, ← Real.exp_add]
          congr 1
          ring
    exact_mod_cast hprod.trans hscale
  have hs := hsieve P Q (arithmeticProductWindow 1 (Real.exp L))
    (candidateCoefficient c L q r jStar) N hz hh heven hP
    (fun p hp => (mem_erase.mp hp).1)
    (fun p hp => small_prime_pool_le (Real.exp_pos _).le (mem_of_mem_erase hp))
    hQ hQodd hout (fun u _ => candidate_coefficient_nonneg c L hq0 r jStar u) hprodlevel
  have hmass : (∑ p ∈ Q, ∑ u ∈ (arithmeticProductWindow 1 (Real.exp L)).filter
      (fun u => p ∣ 2*u+1 ∧ ∀ q ∈ P, ¬q ∣ 2*u+1),
      candidateCoefficient c L q r jStar u) =
      candidatePrimeBandRoughMass c L q r jStar
        (Real.exp (a*L)) (Real.exp (v*L)) (Real.exp (b*L)) := by
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

theorem eventually_repeated_big_prime_clean_norm_le
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) (c s z a v D ε : ℝ) (m : ℕ)
    (hc : 0 < c) (hs : 0 ≤ s) (hz : 0 ≤ z) (ha : 0 ≤ a)
    (hv : 0 < v) (hD : 0 ≤ D) (hε : 0 < ε) (hm : 0 < m) :
    let κ := a * Real.log (primeFiberFactorBound v m)
    let s' := s + ε
    let A₀ := D + 2 * (s' + 1)
    let q := 2 * κ + (s' + 1) + 2 * A₀ + 3
    let w := 4 * q + max z q + A₀ + 2
    let x := (s' + w + 2) + 2 * A₀ + 2
    ∀ᶠ L : ℝ in atTop,
    let Q := ⌊L ^ q⌋₊
    let h := L ^ (-w)
    let ξ := L ^ (-x)
    ∀ {G : Type} [Fintype G] [DecidableEq G] (J ell : ℕ),
    ∀ (P : G → Finset ℕ) (V : G → ℝ),
    Pairwise (fun g h => Disjoint (P g) (P h)) →
    (∀ g p, p ∈ P g → p.Prime ∧ Q < p) →
    (∀ g, ∑ p ∈ P g, 1 / (p : ℝ) = V g) →
    (∀ g, v ≤ V g) →
    (∀ g p, p ∈ P g → Real.log p ≤ L ^ s) →
    (Fintype.card G : ℝ) ≤ a * Real.log L →
    (∀ g, ∃ a b : ℝ, P g = primeBand a b ∧ Real.exp (L ^ c) ≤ a ∧ 0 ≤ b) →
    ∀ probes : G → Finset (Fin J), (∀ g, (probes g).card = m) →
    ∀ r t : Finset G, ∀ hrt : Disjoint r t,
    ∀ ζ θ : ℝ, |ζ| ≤ L ^ z →
    let slots := fun g => (probes g).map (Function.Embedding.inl (β := Fin ell))
    let kept := fun U : Finset (RepeatedBigFlatIndex G J ell) => primeProductRetainedCells
      (fun i : U => P i.1.1) (fun i => V i.1.1) h ξ
    let C := repeatedBigPrimePatternCut (ell := ell) probes r t
    let K := repeatedBigPrimePatternKernel P V probes r t hrt Q h kept
    let weights := repeatedBigPrimePatternWeight (ell := ell) probes r t
    let bounds := repeatedBigPrimePatternBound (ell := ell) probes r t Q ξ
    ∀ (b : ∀ g, P g → ℝ), (∀ g p, 0 < b g p) →
    ∀ T Pmin : ℝ, 0 ≤ T → 0 < Pmin →
    (∀ g (p : P g), Pmin ≤ (p.val : ℝ)) →
    (∀ g (p : P g), b g p = 1 - T / (p.val : ℝ)) →
    (∀ i, ((2 * ∑ g, (ell + (C i g).card) : ℕ) : ℝ) * T / Pmin ≤ 1 / 2) →
    ∀ (S : Type) [Fintype S] (Ps : S → Finset ℕ) (N : G → ℕ) (k : ℤ)
      (p : FixedOrderedMemoryLabels P N),
    ∀ [∀ q : PhysicalPrime Ps, NeZero q.2.val] [∀ g j, NeZero (p g j).val],
    ∀ (d : PhysicalSharedLists Ps J)
      (f : RepeatedBigLists P J ell → (PhysicalResidues Ps × FixedOrderedResidues p) → ℂ),
    cleanWeightedNorm (repeatedBigActiveMass V b)
      (cleanActiveMap repeatedBigSymmetrizeLinear
        (cleanHybridPatternCoreAction V b C ζ θ k p
          (fun i source target aux => weights i * K i source target aux) d
          (cleanActiveMap repeatedBigSymmetrizeLinear f))) ≤
      (Real.sqrt (((ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ r.card) +
        Real.sqrt (((ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ t.card) +
        (3 : ℝ) ^ ((r.sigma slots).card + (t.sigma slots).card) * L ^ (-D) +
        ∑ i, repeatedBigPatternError (ell := ell) V (C i) T Pmin (bounds i)) *
        cleanWeightedNorm (repeatedBigActiveMass V b) f := by
  intro κ s' A₀ q w x
  filter_upwards [eventually_repeated_big_prime_pattern_norm_le
    hZ c s z a v D ε m hc hs hz ha hv hD hε hm, eventually_gt_atTop (0 : ℝ)] with L hnorm hL
  intro Q h ξ G _ dG
  cases Subsingleton.elim dG (Classical.typeDecidableEq G)
  intro J ell P V hdisj hP hmass hV hlog hcard hband
    probes hp r t hrt ζ θ hζ slots kept C K weights bounds b hbpos T Pmin hT hPmin
    hpmin hb hsmall S _ Ps N k p _ _ d f
  have hξ : 0 < ξ := Real.rpow_pos_of_pos hL _
  have hKbound : ∀ i source target aux, ‖K i source target aux‖ ≤ bounds i := by
    intro i source target aux
    exact repeated_big_prime_pattern_kernel_norm_le
      P V probes r t hrt Q h ξ hξ i source target aux
  have hideal : ∀ (Θ : ℝ) (u : RepeatedBigLists P J ell → ℂ),
      u ∈ repeatedBigSymmetricSubspace →
      cleanActiveNorm (repeatedBigActiveMass V (fun _ _ => 1))
        (repeatedBigSymmetrizeLinear (fun source => ∑ target,
          (∑ i, ∑ aux, weights i * repeatedBigUnbannedKernel V (fun _ _ => 1)
            (C i) ζ (K i) aux source target *
              physicalReturnPhase Θ (repeatedBigD (C i) source aux)) * u target)) ≤
        (Real.sqrt (((ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ r.card) +
          Real.sqrt (((ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ t.card) +
          (3 : ℝ) ^ ((r.sigma slots).card + (t.sigma slots).card) * L ^ (-D)) *
            cleanActiveNorm (repeatedBigActiveMass V (fun _ _ => 1)) u := by
    intro Θ u hu
    exact hnorm J ell P V hdisj hP hmass hV hlog hcard hband
      probes hp r t hrt ζ Θ hζ u hu
  have hbound := clean_hybrid_symmetric_pattern_norm_le_of_unbanned
    (I := RepeatedBigPrimePatternIndex (ell := ell) probes r t)
    (S := S) (G := G) (Ps := Ps) (Pb := P) (J := J) (ell := ell) (N := N)
    V (fun j => hv.trans_le (hV j)) hmass b hbpos C ζ θ k p K weights bounds
    (fun i => repeated_big_prime_pattern_bound_nonneg probes r t Q ξ i)
    hKbound
    hT hPmin hpmin hb hsmall d
    (Real.sqrt (((ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ r.card) +
      Real.sqrt (((ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ t.card) +
      (3 : ℝ) ^ ((r.sigma slots).card + (t.sigma slots).card) * L ^ (-D))
    (by positivity) hideal f
  refine hbound.trans ?_
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply add_le_add le_rfl
  apply sum_le_sum
  intro i _
  rw [show ‖weights i‖ = 1 from repeated_big_prime_pattern_weight_norm probes r t i, one_mul]

theorem eventually_repeated_big_prime_initial_clean_norm_le
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) (c s z a v D ε : ℝ) (m : ℕ)
    (hc : 0 < c) (hs : 0 ≤ s) (hz : 0 ≤ z) (ha : 0 ≤ a)
    (hv : 0 < v) (hD : 0 ≤ D) (hε : 0 < ε) (hm : 0 < m) :
    let κ := a * Real.log (primeFiberFactorBound v m)
    let s' := s + ε
    let A₀ := D + 2 * (s' + 1)
    let q := 2 * κ + (s' + 1) + 2 * A₀ + 3
    let w := 4 * q + max z q + A₀ + 2
    let x := (s' + w + 2) + 2 * A₀ + 2
    ∀ᶠ L : ℝ in atTop,
    let Q := ⌊L ^ q⌋₊
    let h := L ^ (-w)
    let ξ := L ^ (-x)
    ∀ {G : Type} [Fintype G] [DecidableEq G] (J ell : ℕ),
    ∀ (P : G → Finset ℕ) (V : G → ℝ),
    Pairwise (fun g h => Disjoint (P g) (P h)) →
    (∀ g p, p ∈ P g → p.Prime ∧ Q < p) →
    (∀ g, ∑ p ∈ P g, 1 / (p : ℝ) = V g) →
    (∀ g, v ≤ V g) →
    (∀ g p, p ∈ P g → Real.log p ≤ L ^ s) →
    (Fintype.card G : ℝ) ≤ a * Real.log L →
    (∀ g, ∃ a b : ℝ, P g = primeBand a b ∧ Real.exp (L ^ c) ≤ a ∧ 0 ≤ b) →
    ∀ probes : G → Finset (Fin J), (∀ g, (probes g).card = m) →
    ∀ r t : Finset G, ∀ hrt : Disjoint r t,
    ∀ ζ θ : ℝ, |ζ| ≤ L ^ z →
    ∀ F : ∀ g, Finset (P g),
    let slots := fun g => (probes g).map (Function.Embedding.inl (β := Fin ell))
    let kept := fun U : Finset (RepeatedBigFlatIndex G J ell) => primeProductRetainedCells
      (fun i : U => P i.1.1) (fun i => V i.1.1) h ξ
    let C := repeatedBigPrimePatternCut (ell := ell) probes r t
    let K₀ := repeatedBigPrimePatternKernel P V probes r t hrt Q h kept
    let K := fun i => cleanInitialBirthKernel F (C i) (K₀ i)
    let weights := repeatedBigPrimePatternWeight (ell := ell) probes r t
    let bounds := repeatedBigPrimePatternBound (ell := ell) probes r t Q ξ
    ∀ (b : ∀ g, P g → ℝ), (∀ g p, 0 < b g p) →
    ∀ T Pmin : ℝ, 0 ≤ T → 0 < Pmin →
    (∀ g (p : P g), Pmin ≤ (p.val : ℝ)) →
    (∀ g (p : P g), b g p = 1 - T / (p.val : ℝ)) →
    (∀ i, ((2 * ∑ g, (ell + (C i g).card) : ℕ) : ℝ) * T / Pmin ≤ 1 / 2) →
    ∀ (S : Type) [Fintype S] (Ps : S → Finset ℕ) (N : G → ℕ) (k : ℤ)
      (p : FixedOrderedMemoryLabels P N),
    ∀ [∀ q : PhysicalPrime Ps, NeZero q.2.val] [∀ g j, NeZero (p g j).val],
    ∀ (d : PhysicalSharedLists Ps J)
      (f : RepeatedBigLists P J ell → (PhysicalResidues Ps × FixedOrderedResidues p) → ℂ),
    cleanWeightedNorm (repeatedBigActiveMass V b)
      (cleanActiveMap repeatedBigSymmetrizeLinear
        (cleanHybridPatternCoreAction V b C ζ θ k p
          (fun i source target aux => weights i * K i source target aux) d
          (cleanActiveMap repeatedBigSymmetrizeLinear f))) ≤
      (Real.sqrt (((ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ r.card) +
        Real.sqrt (((ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ t.card) +
        (3 : ℝ) ^ ((r.sigma slots).card + (t.sigma slots).card) * L ^ (-D) +
        ∑ i, ‖weights i‖ * (bounds i * Real.sqrt
          (repeatedBigInitialForbiddenProbability (ell := ell) V (C i) F Pmin)) +
        ∑ i, repeatedBigPatternError (ell := ell) V (C i) T Pmin (bounds i)) *
        cleanWeightedNorm (repeatedBigActiveMass V b) f := by
  intro κ s' A₀ q w x
  filter_upwards [eventually_repeated_big_prime_pattern_norm_le
    hZ c s z a v D ε m hc hs hz ha hv hD hε hm, eventually_gt_atTop (0 : ℝ)] with L hnorm hL
  intro Q h ξ G _ dG
  cases Subsingleton.elim dG (Classical.typeDecidableEq G)
  intro J ell P V hdisj hP hmass hV hlog hcard hband
    probes hp r t hrt ζ θ hζ F slots kept C K₀ K weights bounds b hbpos T Pmin hT hPmin
    hpmin hb hsmall S _ Ps N k p _ _ d f
  have hξ : 0 < ξ := Real.rpow_pos_of_pos hL _
  have hbounds : ∀ i, 0 ≤ bounds i :=
    fun i => repeated_big_prime_pattern_bound_nonneg probes r t Q ξ i
  have hK₀ : ∀ i source target aux, ‖K₀ i source target aux‖ ≤ bounds i := by
    intro i source target aux
    exact repeated_big_prime_pattern_kernel_norm_le
      P V probes r t hrt Q h ξ hξ i source target aux
  have hK : ∀ i source target aux, ‖K i source target aux‖ ≤ bounds i := by
    intro i source target aux
    dsimp only [K, cleanInitialBirthKernel]
    split_ifs
    · exact hK₀ i source target aux
    · simpa only [norm_zero] using hbounds i
  let M := Real.sqrt (((ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ r.card) +
    Real.sqrt (((ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ t.card) +
    (3 : ℝ) ^ ((r.sigma slots).card + (t.sigma slots).card) * L ^ (-D)
  let Einit := ∑ i, ‖weights i‖ * (bounds i * Real.sqrt
    (repeatedBigInitialForbiddenProbability (ell := ell) V (C i) F Pmin))
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hEinit : 0 ≤ Einit := sum_nonneg fun i _ =>
    mul_nonneg (norm_nonneg _) (mul_nonneg (hbounds i) (Real.sqrt_nonneg _))
  have hideal : ∀ (Θ : ℝ) (u : RepeatedBigLists P J ell → ℂ),
      u ∈ repeatedBigSymmetricSubspace →
      cleanActiveNorm (repeatedBigActiveMass V (fun _ _ => 1))
        (repeatedBigSymmetrizeLinear (fun source => ∑ target,
          (∑ i, ∑ aux, weights i * repeatedBigUnbannedKernel V (fun _ _ => 1)
            (C i) ζ (K₀ i) aux source target *
              physicalReturnPhase Θ (repeatedBigD (C i) source aux)) * u target)) ≤
        M * cleanActiveNorm (repeatedBigActiveMass V (fun _ _ => 1)) u := by
    intro Θ u hu
    exact hnorm J ell P V hdisj hP hmass hV hlog hcard hband
      probes hp r t hrt ζ Θ hζ u hu
  have hmasked := repeated_big_initial_birth_masked_ideal V C F
    (fun g => hv.trans_le (hV g)) hmass ζ K₀ weights bounds hbounds hK₀
    hPmin hpmin M hideal
  have hbound := clean_hybrid_symmetric_pattern_norm_le_of_unbanned
    (I := RepeatedBigPrimePatternIndex (ell := ell) probes r t)
    (S := S) (G := G) (Ps := Ps) (Pb := P) (J := J) (ell := ell) (N := N)
    V (fun j => hv.trans_le (hV j)) hmass b hbpos C ζ θ k p K weights bounds
    hbounds hK hT hPmin hpmin hb hsmall d
    (M + Einit) (add_nonneg hM hEinit) hmasked f
  refine hbound.trans ?_
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply add_le_add le_rfl
  apply sum_le_sum
  intro i _
  rw [show ‖weights i‖ = 1 from repeated_big_prime_pattern_weight_norm probes r t i, one_mul]

theorem exists_candidate_prime_band_rough_mass_density_upper (hZ : PrimitiveZeroFreeRightOf (23 / 24)) :
    ∃ K : ℝ, 0 < K ∧ ∀ (c q b a v : ℝ) (r h : ℕ),
      0 < c → 0 < r → 0 ≤ q → q < 1 →
      (11/5 : ℝ)*(r : ℝ)*c = 1 →
      0 < b → b ≤ a → a ≤ v → 1 ≤ h → Even h →
      v+b*(4*(h : ℝ)+2) < 1/2 →
      ∃ J : ℕ, ∀ jStar : ℕ, J < jStar → ∀ ε : ℝ, 0 < ε → ∀ᶠ L : ℝ in atTop,
        candidatePrimeBandRoughMass c L q r jStar
            (Real.exp (a*L)) (Real.exp (v*L)) (Real.exp (b*L)) ≤
          ((shiftedSieveRatioConstant*Mertens.primeProductLimitConstant/b)*
              Real.log (v/a)*(1+K*Real.exp (-(h : ℝ)))+ε)*
            candidateCoefficientWindowMass c L q r jStar / L := by
  obtain ⟨K, hK, hmass⟩ := exists_candidate_prime_band_rough_mass_estimate hZ
  refine ⟨K, hK, ?_⟩
  intro c q b a v r h hc hr hq0 hq1 hcenter hb hba hav hh heven hlevel
  obtain ⟨J, hJ⟩ := hmass c q b a v r h hc hr hq0 hq1 hcenter hb hba hav hh heven hlevel
  refine ⟨J, ?_⟩
  intro jStar hj ε hε
  have ha : 0 < a := hb.trans_le hba
  have hpow : Tendsto (fun L : ℝ => L^(-17 : ℝ)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 17)
  have hlim := (((exponential_shifted_prime_avoidance_product_tendsto hb).mul
    (exponential_prime_predecessor_reciprocal_tendsto ha hav)).mul_const
      (1+K*Real.exp (-(h : ℝ)))).add
        (hpow.const_mul (1+16*primeEulerProductUpperConstant))
  simp only [mul_zero, add_zero] at hlim
  have hev := hlim.eventually_lt_const (show
    (shiftedSieveRatioConstant*Mertens.primeProductLimitConstant/b)*
        Real.log (v/a)*(1+K*Real.exp (-(h : ℝ))) <
      (shiftedSieveRatioConstant*Mertens.primeProductLimitConstant/b)*
        Real.log (v/a)*(1+K*Real.exp (-(h : ℝ)))+ε by linarith)
  filter_upwards [hJ jStar hj, hev, eventually_gt_atTop (0 : ℝ)] with L hm hd hL
  have hXA : 0 ≤ candidateCoefficientWindowMass c L q r jStar := by
    apply sum_nonneg
    intro u _
    exact candidate_coefficient_nonneg c L hq0 r jStar u
  have hpow_id : L*L^(-18 : ℝ)=L^(-17 : ℝ) := by
    calc
      _ = L^(1 : ℝ)*L^(-18 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hL]; norm_num
  have hupper := (le_abs_self _).trans hm
  have hupper' : candidatePrimeBandRoughMass c L q r jStar
      (Real.exp (a*L)) (Real.exp (v*L)) (Real.exp (b*L)) ≤
      candidateCoefficientWindowMass c L q r jStar *
        shiftedPrimeAvoidanceProduct (Real.exp (b*L)) *
          (∑ p ∈ primeBand (Real.exp (a*L)) (Real.exp (v*L)), 1/((p : ℝ)-1))*
            (1+K*Real.exp (-(h : ℝ))) +
      candidateCoefficientWindowMass c L q r jStar *
        ((1+16*primeEulerProductUpperConstant)*L^(-18 : ℝ)) := by nlinarith
  apply hupper'.trans
  have hscaled := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hd.le hXA) hL.le
  convert hscaled using 1
  field_simp
  rw [← hpow_id]
  ring

theorem eventually_repeated_big_prime_clean_power_bound
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) (c s z a v D ε E beta tau : ℝ)
    (m J ell : ℕ)
    (hc : 0 < c) (hs : 0 ≤ s) (hz : 0 ≤ z) (ha : 0 ≤ a)
    (hv : 0 < v) (hD : 0 ≤ D) (hε : 0 < ε) (htau : 0 ≤ tau)
    (hell : 0 < ell) (hml : ell ≤ m)
    (hgap : beta * Real.log ((ell : ℝ) ^ ell / (m : ℝ) ^ ell) / 2 ≤ -(E + 2))
    (hDgap : (m : ℝ) * a * Real.log 3 + E + 2 ≤ D) :
    let κ := a * Real.log (primeFiberFactorBound v m)
    let s' := s + ε
    let A₀ := D + 2 * (s' + 1)
    let q := 2 * κ + (s' + 1) + 2 * A₀ + 3
    let w := 4 * q + max z q + A₀ + 2
    let x := (s' + w + 2) + 2 * A₀ + 2
    ∀ᶠ L : ℝ in atTop,
    let Q := ⌊L ^ q⌋₊
    let h := L ^ (-w)
    let ξ := L ^ (-x)
    ∀ {G : Type} [Fintype G] [DecidableEq G],
    ∀ (P : G → Finset ℕ) (V : G → ℝ),
    Pairwise (fun g h => Disjoint (P g) (P h)) →
    (∀ g p, p ∈ P g → p.Prime ∧ Q < p) →
    (∀ g, ∑ p ∈ P g, 1 / (p : ℝ) = V g) →
    (∀ g, v ≤ V g) →
    (∀ g p, p ∈ P g → Real.log p ≤ L ^ s) →
    (Fintype.card G : ℝ) ≤ a * Real.log L →
    (∀ g, ∃ a b : ℝ, P g = primeBand a b ∧ Real.exp (L ^ c) ≤ a ∧ 0 ≤ b) →
    ∀ probes : G → Finset (Fin J), (∀ g, (probes g).card = m) →
    ∀ r t : Finset G, ∀ hrt : Disjoint r t,
    beta * Real.log L ≤ (r.card : ℝ) → beta * Real.log L ≤ (t.card : ℝ) →
    ∀ ζ θ : ℝ, |ζ| ≤ L ^ z →
    let kept := fun U : Finset (RepeatedBigFlatIndex G J ell) => primeProductRetainedCells
      (fun i : U => P i.1.1) (fun i => V i.1.1) h ξ
    let C := repeatedBigPrimePatternCut (ell := ell) probes r t
    let K := repeatedBigPrimePatternKernel P V probes r t hrt Q h kept
    let weights := repeatedBigPrimePatternWeight (ell := ell) probes r t
    ∀ (b : ∀ g, P g → ℝ),
    ∀ T Pmin : ℝ, 0 ≤ T → T ≤ L ^ tau → Real.exp (L ^ c) ≤ Pmin →
    (∀ g (p : P g), Pmin ≤ (p.val : ℝ)) →
    (∀ g (p : P g), b g p = 1 - T / (p.val : ℝ)) →
    ∀ (S : Type) [Fintype S] (Ps : S → Finset ℕ) (N : G → ℕ) (k : ℤ)
      (p : FixedOrderedMemoryLabels P N),
    ∀ [∀ q : PhysicalPrime Ps, NeZero q.2.val] [∀ g j, NeZero (p g j).val],
    ∀ (d : PhysicalSharedLists Ps J)
      (f : RepeatedBigLists P J ell → (PhysicalResidues Ps × FixedOrderedResidues p) → ℂ),
    cleanWeightedNorm (repeatedBigActiveMass V b)
      (cleanActiveMap repeatedBigSymmetrizeLinear
        (cleanHybridPatternCoreAction V b C ζ θ k p
          (fun i source target aux => weights i * K i source target aux) d
          (cleanActiveMap repeatedBigSymmetrizeLinear f))) ≤
      L ^ (-E) * cleanWeightedNorm (repeatedBigActiveMass V b) f := by
  intro κ s' A₀ q w x
  have hm : 0 < m := hell.trans_le hml
  have hexp := repeated_big_prime_kernel_exponents_nonneg s z a v D ε m hs hz ha hD hε.le
  have hq : 0 ≤ q := hexp.2.2.2.1
  have hx : 0 ≤ x := hexp.2.2.2.2.2
  filter_upwards [eventually_repeated_big_prime_clean_norm_le
      hZ c s z a v D ε m hc hs hz ha hv hD hε hm,
    eventually_repeated_big_prime_pattern_error_small m J ell ha hq hx htau hv hc (E + 1),
    eventually_repeated_big_baseline_pos (tau := tau) hc,
    eventually_ge_atTop (3 : ℝ)] with L hnorm herr hbaseline hL
  intro Q h ξ G _ dG
  cases Subsingleton.elim dG (Classical.typeDecidableEq G)
  intro P V hdisj hP hmass hV hlog hcard hband probes hp r t hrt hr ht
    ζ θ hζ kept C K weights b T Pmin hT hTmax hPminexp hpmin hb
    S _ Ps N k p _ _ d f
  have hL0 : 0 < L := by linarith
  have hPmin : 0 < Pmin := (Real.exp_pos _).trans_le hPminexp
  have hbpos : ∀ g p, 0 < b g p := by
    intro g p
    rw [hb g p]
    exact (hbaseline T Pmin hT hTmax hPminexp).2 p.val (hpmin g p)
  have hp' : ∀ g, (probes g).card ≤ m := fun g => (hp g).le
  obtain ⟨hsmall, herr'⟩ := herr V probes r t Q ξ T Pmin hrt hp' hcard hV
    (Nat.floor_le (Real.rpow_nonneg hL0.le _)) le_rfl hT hTmax hPminexp
  have hsmall' := repeated_big_prime_pattern_small_of_uniform
    probes r t hp' hT hPmin hsmall
  have hbase := hnorm J ell P V hdisj hP hmass hV hlog hcard hband probes hp r t hrt
    ζ θ hζ b hbpos T Pmin hT hPmin hpmin hb hsmall' S Ps N k p d f
  have htheta : 0 < (ell : ℝ) ^ ell / (m : ℝ) ^ ell := by positivity
  have htheta1 : (ell : ℝ) ^ ell / (m : ℝ) ^ ell ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hml) ell
  have hM := repeated_big_positive_block_bound (E := E + 1) (D := D) m (Fintype.card G) r.card t.card
    ((r.sigma (fun g => (probes g).map (Function.Embedding.inl (β := Fin ell)))).card +
      (t.sigma (fun g => (probes g).map (Function.Embedding.inl (β := Fin ell)))).card)
    hL htheta htheta1 hr ht hcard
    (repeated_big_prime_mapped_probe_card_le probes r t hrt hp')
    (by linarith [hgap]) (by linarith [hDgap])
  have herr'' : (∑ i : RepeatedBigPrimePatternIndex (ell := ell) probes r t,
      repeatedBigPatternError (ell := ell) V (C i) T Pmin
        (repeatedBigPrimePatternBound probes r t Q ξ i)) ≤ L ^ (-(E + 1)) := by
    apply le_trans _ herr'
    apply sum_le_sum
    intro i _
    rw [repeated_big_prime_pattern_weight_norm, one_mul]
    exact le_rfl
  have hsum : L ^ (-(E + 1)) + L ^ (-(E + 1)) ≤ L ^ (-E) := by
    rw [show -(E + 1) = -E - 1 by ring, Real.rpow_sub hL0, Real.rpow_one]
    have hpw := Real.rpow_pos_of_pos hL0 (-E)
    have hdiv : L ^ (-E) / L * L = L ^ (-E) := div_mul_cancel₀ _ hL0.ne'
    apply (mul_le_mul_iff_left₀ hL0).mp
    nlinarith
  apply hbase.trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact (add_le_add hM herr'').trans hsum

theorem eventually_repeated_big_prime_initial_clean_power_bound
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) (c s z a v D ε E beta tau : ℝ)
    (m J ell : ℕ)
    (hc : 0 < c) (hs : 0 ≤ s) (hz : 0 ≤ z) (ha : 0 ≤ a)
    (hv : 0 < v) (hD : 0 ≤ D) (hε : 0 < ε) (htau : 0 ≤ tau)
    (hell : 0 < ell) (hml : ell ≤ m)
    (hgap : beta * Real.log ((ell : ℝ) ^ ell / (m : ℝ) ^ ell) / 2 ≤ -(E + 2))
    (hDgap : (m : ℝ) * a * Real.log 3 + E + 2 ≤ D) :
    let κ := a * Real.log (primeFiberFactorBound v m)
    let s' := s + ε
    let A₀ := D + 2 * (s' + 1)
    let q := 2 * κ + (s' + 1) + 2 * A₀ + 3
    let w := 4 * q + max z q + A₀ + 2
    let x := (s' + w + 2) + 2 * A₀ + 2
    ∀ᶠ L : ℝ in atTop,
    let Q := ⌊L ^ q⌋₊
    let h := L ^ (-w)
    let ξ := L ^ (-x)
    ∀ {G : Type} [Fintype G] [DecidableEq G],
    ∀ (P : G → Finset ℕ) (V : G → ℝ),
    Pairwise (fun g h => Disjoint (P g) (P h)) →
    (∀ g p, p ∈ P g → p.Prime ∧ Q < p) →
    (∀ g, ∑ p ∈ P g, 1 / (p : ℝ) = V g) →
    (∀ g, v ≤ V g) →
    (∀ g p, p ∈ P g → Real.log p ≤ L ^ s) →
    (Fintype.card G : ℝ) ≤ a * Real.log L →
    (∀ g, ∃ a b : ℝ, P g = primeBand a b ∧ Real.exp (L ^ c) ≤ a ∧ 0 ≤ b) →
    ∀ probes : G → Finset (Fin J), (∀ g, (probes g).card = m) →
    ∀ r t : Finset G, ∀ hrt : Disjoint r t,
    beta * Real.log L ≤ (r.card : ℝ) → beta * Real.log L ≤ (t.card : ℝ) →
    ∀ ζ θ : ℝ, |ζ| ≤ L ^ z →
    ∀ F : ∀ g, Finset (P g), (∀ g, (F g).card ≤ J + ell) →
    let kept := fun U : Finset (RepeatedBigFlatIndex G J ell) => primeProductRetainedCells
      (fun i : U => P i.1.1) (fun i => V i.1.1) h ξ
    let C := repeatedBigPrimePatternCut (ell := ell) probes r t
    let K₀ := repeatedBigPrimePatternKernel P V probes r t hrt Q h kept
    let K := fun i => cleanInitialBirthKernel F (C i) (K₀ i)
    let weights := repeatedBigPrimePatternWeight (ell := ell) probes r t
    ∀ (b : ∀ g, P g → ℝ),
    ∀ T Pmin : ℝ, 0 ≤ T → T ≤ L ^ tau → Real.exp (L ^ c) ≤ Pmin →
    (∀ g (p : P g), Pmin ≤ (p.val : ℝ)) →
    (∀ g (p : P g), b g p = 1 - T / (p.val : ℝ)) →
    ∀ (S : Type) [Fintype S] (Ps : S → Finset ℕ) (N : G → ℕ) (k : ℤ)
      (p : FixedOrderedMemoryLabels P N),
    ∀ [∀ q : PhysicalPrime Ps, NeZero q.2.val] [∀ g j, NeZero (p g j).val],
    ∀ (d : PhysicalSharedLists Ps J)
      (f : RepeatedBigLists P J ell → (PhysicalResidues Ps × FixedOrderedResidues p) → ℂ),
    cleanWeightedNorm (repeatedBigActiveMass V b)
      (cleanActiveMap repeatedBigSymmetrizeLinear
        (cleanHybridPatternCoreAction V b C ζ θ k p
          (fun i source target aux => weights i * K i source target aux) d
          (cleanActiveMap repeatedBigSymmetrizeLinear f))) ≤
      L ^ (-E) * cleanWeightedNorm (repeatedBigActiveMass V b) f := by
  intro κ s' A₀ q w x
  have hm : 0 < m := hell.trans_le hml
  have hexp := repeated_big_prime_kernel_exponents_nonneg s z a v D ε m hs hz ha hD hε.le
  have hq : 0 ≤ q := hexp.2.2.2.1
  have hx : 0 ≤ x := hexp.2.2.2.2.2
  filter_upwards [eventually_repeated_big_prime_initial_clean_norm_le
      hZ c s z a v D ε m hc hs hz ha hv hD hε hm,
    eventually_repeated_big_prime_pattern_error_small m J ell ha hq hx htau hv hc (E + 1),
    eventually_repeated_big_initial_error_small m J ell ha hq hx hv hc hml (E + 1),
    eventually_repeated_big_baseline_pos (tau := tau) hc,
    eventually_ge_atTop (3 : ℝ)] with L hnorm herr hinit hbaseline hL
  intro Q h ξ G _ dG
  cases Subsingleton.elim dG (Classical.typeDecidableEq G)
  intro P V hdisj hP hmass hV hlog hcard hband probes hp r t hrt hr ht
    ζ θ hζ F hF kept C K₀ K weights b T Pmin hT hTmax hPminexp hpmin hb
    S _ Ps N k p _ _ d f
  have hL0 : 0 < L := by linarith
  have hPmin : 0 < Pmin := (Real.exp_pos _).trans_le hPminexp
  have hbpos : ∀ g p, 0 < b g p := by
    intro g p
    rw [hb g p]
    exact (hbaseline T Pmin hT hTmax hPminexp).2 p.val (hpmin g p)
  have hp' : ∀ g, (probes g).card ≤ m := fun g => (hp g).le
  obtain ⟨hsmall, herr'⟩ := herr V probes r t Q ξ T Pmin hrt hp' hcard hV
    (Nat.floor_le (Real.rpow_nonneg hL0.le _)) le_rfl hT hTmax hPminexp
  have hsmall' := repeated_big_prime_pattern_small_of_uniform
    probes r t hp' hT hPmin hsmall
  have hbase := hnorm J ell P V hdisj hP hmass hV hlog hcard hband probes hp r t hrt
    ζ θ hζ F b hbpos T Pmin hT hPmin hpmin hb hsmall' S Ps N k p d f
  have htheta : 0 < (ell : ℝ) ^ ell / (m : ℝ) ^ ell := by positivity
  have htheta1 : (ell : ℝ) ^ ell / (m : ℝ) ^ ell ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hml) ell
  have hM := repeated_big_positive_block_bound (E := E + 1) (D := D) m (Fintype.card G) r.card t.card
    ((r.sigma (fun g => (probes g).map (Function.Embedding.inl (β := Fin ell)))).card +
      (t.sigma (fun g => (probes g).map (Function.Embedding.inl (β := Fin ell)))).card)
    hL htheta htheta1 hr ht hcard
    (repeated_big_prime_mapped_probe_card_le probes r t hrt hp')
    (by linarith [hgap]) (by linarith [hDgap])
  have herr'' : (∑ i : RepeatedBigPrimePatternIndex (ell := ell) probes r t,
      repeatedBigPatternError (ell := ell) V (C i) T Pmin
        (repeatedBigPrimePatternBound probes r t Q ξ i)) ≤ L ^ (-(E + 1)) := by
    apply le_trans _ herr'
    apply sum_le_sum
    intro i _
    rw [repeated_big_prime_pattern_weight_norm, one_mul]
    exact le_rfl
  have hI : (∑ i : RepeatedBigPrimePatternIndex (ell := ell) probes r t,
      ‖repeatedBigPrimePatternWeight probes r t i‖ *
        (repeatedBigPrimePatternBound probes r t Q ξ i * Real.sqrt
          (repeatedBigInitialForbiddenProbability (ell := ell) V (C i) F Pmin))) ≤
      L ^ (-(E + 1)) := by
    exact (repeated_big_prime_initial_pattern_error_le V probes r t hrt hp' F hF Q ξ
      hv hV hPmin).trans (hinit (Fintype.card G) Q ξ Pmin hcard
        (Nat.floor_le (Real.rpow_nonneg hL0.le _)) le_rfl hPminexp)
  have hsum : (L ^ (-(E + 1)) + L ^ (-(E + 1))) + L ^ (-(E + 1)) ≤ L ^ (-E) := by
    rw [show -(E + 1) = -E - 1 by ring, Real.rpow_sub hL0, Real.rpow_one]
    have hpw := Real.rpow_pos_of_pos hL0 (-E)
    have hdiv : L ^ (-E) / L * L = L ^ (-E) := div_mul_cancel₀ _ hL0.ne'
    apply (mul_le_mul_iff_left₀ hL0).mp
    nlinarith
  apply hbase.trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact (add_le_add (add_le_add hM hI) herr'').trans hsum

theorem exists_candidate_unbalanced_rough_bin_upper
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q γ a v S M : ℝ} {r : ℕ}
    (hc : 0 < c) (hr : 0 < r) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcenter : (11 / 5 : ℝ) * (r : ℝ) * c = 1)
    (hγ : 0 < γ) (ha : 0 < a) (hav : a ≤ v) (hvhalf : v < 1 / 2)
    (hvγ : v < 1 - γ) (hS : 0 ≤ S) (hM : 0 ≤ M)
    (hdensity : ∀ α ∈ Set.Icc a v, buchstabDensity γ (1 - α) ≤ M) :
    ∃ J : ℕ, ∀ jStar : ℕ, J < jStar → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ L : ℝ in atTop, ∀ (F : Finset (ℕ × ℕ)) (u : ℕ × ℕ → ℕ),
        (∀ w ∈ F, u w ∈ arithmeticProductWindow 1 (Real.exp L) ∧
          w.1 ∈ primeBand (Real.exp (a * L)) (Real.exp (v * L)) ∧ w.1 * w.2 = 2 * u w + 1) →
        (∑ w ∈ F, candidateCoefficient c L q r jStar (u w) * roughTestLogarithmicProxy γ L S w.2) ≤
          (shiftedSieveRatioConstant * M * Real.log (v / a) + ε) *
            candidateCoefficientWindowMass c L q r jStar / L := by
  obtain ⟨J, hJ⟩ := exists_candidate_unbalanced_rough_logarithmic_proxy_upper
    hZ hc hr hq0 hq1 hcenter ha hav hvhalf
  refine ⟨J, ?_⟩
  intro jStar hj ε hε
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

theorem eventually_repeated_big_prime_full_memory_power_bound
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) (c s z a v D ε E beta tau : ℝ)
    (m J ell : ℕ)
    (hc : 0 < c) (hs : 0 ≤ s) (hz : 0 ≤ z) (ha : 0 ≤ a)
    (hv : 0 < v) (hD : 0 ≤ D) (hε : 0 < ε) (htau : 0 ≤ tau)
    (hell : 0 < ell) (hml : ell ≤ m)
    (hgap : beta * Real.log ((ell : ℝ) ^ ell / (m : ℝ) ^ ell) / 2 ≤ -(E + 2))
    (hDgap : (m : ℝ) * a * Real.log 3 + E + 2 ≤ D) :
    let κ := a * Real.log (primeFiberFactorBound v m)
    let s' := s + ε
    let A₀ := D + 2 * (s' + 1)
    let q := 2 * κ + (s' + 1) + 2 * A₀ + 3
    let w := 4 * q + max z q + A₀ + 2
    let x := (s' + w + 2) + 2 * A₀ + 2
    ∀ᶠ L : ℝ in atTop,
    let Q := ⌊L ^ q⌋₊
    let h := L ^ (-w)
    let ξ := L ^ (-x)
    ∀ {G : Type} [Fintype G] [DecidableEq G],
    ∀ (P : G → Finset ℕ) (V : G → ℝ),
    Pairwise (fun g h => Disjoint (P g) (P h)) →
    ∀ hP : ∀ g p, p ∈ P g → p.Prime ∧ Q < p,
    (∀ g, ∑ p ∈ P g, 1 / (p : ℝ) = V g) →
    (∀ g, v ≤ V g) →
    (∀ g p, p ∈ P g → Real.log p ≤ L ^ s) →
    (Fintype.card G : ℝ) ≤ a * Real.log L →
    (∀ g, ∃ a b : ℝ, P g = primeBand a b ∧ Real.exp (L ^ c) ≤ a ∧ 0 ≤ b) →
    ∀ probes : G → Finset (Fin J), (∀ g, (probes g).card = m) →
    ∀ r t : Finset G, ∀ hrt : Disjoint r t,
    beta * Real.log L ≤ (r.card : ℝ) → beta * Real.log L ≤ (t.card : ℝ) →
    ∀ ζ θ : ℝ, |ζ| ≤ L ^ z →
    let kept := fun U : Finset (RepeatedBigFlatIndex G J ell) => primeProductRetainedCells
      (fun i : U => P i.1.1) (fun i => V i.1.1) h ξ
    let C := repeatedBigPrimePatternCut (ell := ell) probes r t
    let K := repeatedBigPrimePatternKernel P V probes r t hrt Q h kept
    let weights := repeatedBigPrimePatternWeight (ell := ell) probes r t
    ∀ (b : ∀ g, P g → ℝ),
    ∀ T Pmin : ℝ, 0 ≤ T → T ≤ L ^ tau → Real.exp (L ^ c) ≤ Pmin →
    (∀ g (p : P g), Pmin ≤ (p.val : ℝ)) →
    (∀ g (p : P g), b g p = 1 - T / (p.val : ℝ)) →
    ∀ (S : Type) [Fintype S] (Ps : S → Finset ℕ) (fullB : ℕ) (k : ℤ)
      (ν : ∀ g, P g → ℝ) (ρ : ℝ),
    (∀ g p, 0 ≤ ν g p) → 0 ≤ ρ → ρ ≤ 1 →
    ∀ [∀ q : PhysicalPrime Ps, NeZero q.2.val] (d : PhysicalSharedLists Ps J),
    let _ : ∀ g (p : P g), NeZero p.val :=
      fun g p => ⟨(hP g p.val p.property).1.pos.ne'⟩
    ∀ f : CleanFullMemoryState P J ell fullB → PhysicalResidues Ps → ℂ,
    cleanWeightedNorm
      (productMemoryWeight (fun g => tiltedPhysicalBirthLaw V g (b g)) (fun g z => ν g z.1))
      (cleanFullMemoryActiveMap
        (cleanFullMemoryPatternDampedAction V b C ζ θ ρ k
          (fun i source target aux => weights i * K i source target aux) d
          (cleanFullMemoryActiveMap f))) ≤
      L ^ (-E) * cleanWeightedNorm
        (productMemoryWeight (fun g => tiltedPhysicalBirthLaw V g (b g)) (fun g z => ν g z.1)) f := by
  intro κ s' A₀ q w x
  filter_upwards [eventually_repeated_big_prime_clean_power_bound
      hZ c s z a v D ε E beta tau m J ell hc hs hz ha hv hD hε htau hell hml hgap hDgap,
    eventually_repeated_big_baseline_pos (tau := tau) hc,
    eventually_gt_atTop (0 : ℝ)] with L hpower hbaseline hL
  intro Q h ξ G _ dG
  cases Subsingleton.elim dG (Classical.typeDecidableEq G)
  intro P V hdisj hP hmass hV hlog hcard hband probes hp r t hrt hr ht
    ζ θ hζ kept C K weights b T Pmin hT hTmax hPminexp hpmin hb
    S _ Ps fullB k ν ρ hν hρ0 hρ1 _ d
  let _ : ∀ g (p : P g), NeZero p.val :=
    fun g p => ⟨(hP g p.val p.property).1.pos.ne'⟩
  intro _ f
  have hbpos : ∀ g p, 0 < b g p := by
    intro g p
    rw [hb g p]
    exact (hbaseline T Pmin hT hTmax hPminexp).2 p.val (hpmin g p)
  apply clean_full_memory_projected_damped_norm_le V b ν
    (fun g => (hv.trans_le (hV g)).le) (fun g p => (hbpos g p).le) hν
    C ζ θ ρ hρ0 hρ1 k (fun i source target aux => weights i * K i source target aux)
    d (L ^ (-E)) (Real.rpow_nonneg hL.le _) _ f
  intro N p u
  exact hpower P V hdisj hP hmass hV hlog hcard hband probes hp r t hrt hr ht
    ζ θ hζ b T Pmin hT hTmax hPminexp hpmin hb
    S Ps (fun g => (N g).val) k p d u

theorem eventually_repeated_big_prime_full_memory_cutoff_power_bound
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) (c s z a v D ε E beta tau : ℝ)
    (m J ell : ℕ)
    (hc : 0 < c) (hs : 0 ≤ s) (hz : 0 ≤ z) (ha : 0 ≤ a)
    (hv : 0 < v) (hD : 0 ≤ D) (hε : 0 < ε) (htau : 0 ≤ tau)
    (hell : 0 < ell) (hml : ell ≤ m)
    (hgap : beta * Real.log ((ell : ℝ) ^ ell / (m : ℝ) ^ ell) / 2 ≤ -(E + 2))
    (hDgap : (m : ℝ) * a * Real.log 3 + E + 2 ≤ D) :
    let κ := a * Real.log (primeFiberFactorBound v m)
    let s' := s + ε
    let A₀ := D + 2 * (s' + 1)
    let q := 2 * κ + (s' + 1) + 2 * A₀ + 3
    let w := 4 * q + max z q + A₀ + 2
    let x := (s' + w + 2) + 2 * A₀ + 2
    ∀ᶠ L : ℝ in atTop,
    let Q := ⌊L ^ q⌋₊
    let h := L ^ (-w)
    let ξ := L ^ (-x)
    ∀ {G : Type} [Fintype G] [DecidableEq G],
    ∀ (P : G → Finset ℕ) (V : G → ℝ),
    Pairwise (fun g h => Disjoint (P g) (P h)) →
    ∀ hP : ∀ g p, p ∈ P g → p.Prime ∧ Q < p,
    (∀ g, ∑ p ∈ P g, 1 / (p : ℝ) = V g) →
    (∀ g, v ≤ V g) →
    (∀ g p, p ∈ P g → Real.log p ≤ L ^ s) →
    (Fintype.card G : ℝ) ≤ a * Real.log L →
    (∀ g, ∃ a b : ℝ, P g = primeBand a b ∧ Real.exp (L ^ c) ≤ a ∧ 0 ≤ b) →
    ∀ probes : G → Finset (Fin J), (∀ g, (probes g).card = m) →
    ∀ r t : Finset G, ∀ hrt : Disjoint r t,
    beta * Real.log L ≤ (r.card : ℝ) → beta * Real.log L ≤ (t.card : ℝ) →
    ∀ ζ θ : ℝ, |ζ| ≤ L ^ z →
    let kept := fun U : Finset (RepeatedBigFlatIndex G J ell) => primeProductRetainedCells
      (fun i : U => P i.1.1) (fun i => V i.1.1) h ξ
    let C := repeatedBigPrimePatternCut (ell := ell) probes r t
    let K := repeatedBigPrimePatternKernel P V probes r t hrt Q h kept
    let weights := repeatedBigPrimePatternWeight (ell := ell) probes r t
    ∀ (b : ∀ g, P g → ℝ),
    ∀ T Pmin : ℝ, 0 ≤ T → T ≤ L ^ tau → Real.exp (L ^ c) ≤ Pmin →
    (∀ g (p : P g), Pmin ≤ (p.val : ℝ)) →
    (∀ g (p : P g), b g p = 1 - T / (p.val : ℝ)) →
    ∀ (S : Type) [Fintype S] (Ps : S → Finset ℕ) (fullB : ℕ) (k : ℤ)
      (ν : ∀ g, P g → ℝ) (ρ : ℝ),
    (∀ g p, 0 ≤ ν g p) → 0 ≤ ρ → ρ ≤ 1 →
    ∀ [∀ q : PhysicalPrime Ps, NeZero q.2.val] (d : PhysicalSharedLists Ps J),
    let _ : ∀ g (p : P g), NeZero p.val :=
      fun g p => ⟨(hP g p.val p.property).1.pos.ne'⟩
    ∀ f : CleanFullMemoryState P J ell fullB → PhysicalResidues Ps → ℂ,
    cleanWeightedNorm
      (productMemoryWeight (fun g => tiltedPhysicalBirthLaw V g (b g)) (fun g z => ν g z.1))
      (cleanFullMemoryCutoff (cleanFullMemoryActiveMap
        (cleanFullMemoryPatternDampedAction V b C ζ θ ρ k
          (fun i source target aux => weights i * K i source target aux) d
          (cleanFullMemoryActiveMap (cleanFullMemoryCutoff f))))) ≤
      L ^ (-E) * cleanWeightedNorm
        (productMemoryWeight (fun g => tiltedPhysicalBirthLaw V g (b g)) (fun g z => ν g z.1)) f := by
  intro κ s' A₀ q w x
  filter_upwards [eventually_repeated_big_prime_full_memory_power_bound
      hZ c s z a v D ε E beta tau m J ell hc hs hz ha hv hD hε htau hell hml hgap hDgap,
    eventually_repeated_big_baseline_pos (tau := tau) hc,
    eventually_gt_atTop (0 : ℝ)] with L hpower hbaseline hL
  intro Q h ξ G _ dG
  cases Subsingleton.elim dG (Classical.typeDecidableEq G)
  intro P V hdisj hP hmass hV hlog hcard hband probes hp r t hrt hr ht
    ζ θ hζ kept C K weights b T Pmin hT hTmax hPminexp hpmin hb
    S _ Ps fullB k ν ρ hν hρ0 hρ1 _ d
  let _ : ∀ g (p : P g), NeZero p.val :=
    fun g p => ⟨(hP g p.val p.property).1.pos.ne'⟩
  intro _ f
  have hbpos : ∀ g p, 0 < b g p := by
    intro g p
    rw [hb g p]
    exact (hbaseline T Pmin hT hTmax hPminexp).2 p.val (hpmin g p)
  apply clean_full_memory_cutoff_sandwich_norm_le
    (fun g => tiltedPhysicalBirthLaw V g (b g)) ν
    (fun g p => tiltedPhysicalBirthLaw_nonneg V g (b g)
      (hv.trans_le (hV g)).le (fun p => (hbpos g p).le) p) hν
    (fun u => cleanFullMemoryActiveMap (cleanFullMemoryPatternDampedAction V b C ζ θ ρ k
      (fun i source target aux => weights i * K i source target aux) d
        (cleanFullMemoryActiveMap u)))
    (L ^ (-E)) (Real.rpow_nonneg hL.le _) _ f
  intro u
  exact hpower P V hdisj hP hmass hV hlog hcard hband probes hp r t hrt hr ht
    ζ θ hζ b T Pmin hT hTmax hPminexp hpmin hb
    S Ps fullB k ν ρ hν hρ0 hρ1 d u

theorem eventually_repeated_big_prime_initial_full_memory_power_bound
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) (c s z a v D ε E beta tau : ℝ)
    (m J ell : ℕ)
    (hc : 0 < c) (hs : 0 ≤ s) (hz : 0 ≤ z) (ha : 0 ≤ a)
    (hv : 0 < v) (hD : 0 ≤ D) (hε : 0 < ε) (htau : 0 ≤ tau)
    (hell : 0 < ell) (hml : ell ≤ m)
    (hgap : beta * Real.log ((ell : ℝ) ^ ell / (m : ℝ) ^ ell) / 2 ≤ -(E + 2))
    (hDgap : (m : ℝ) * a * Real.log 3 + E + 2 ≤ D) :
    let κ := a * Real.log (primeFiberFactorBound v m)
    let s' := s + ε
    let A₀ := D + 2 * (s' + 1)
    let q := 2 * κ + (s' + 1) + 2 * A₀ + 3
    let w := 4 * q + max z q + A₀ + 2
    let x := (s' + w + 2) + 2 * A₀ + 2
    ∀ᶠ L : ℝ in atTop,
    let Q := ⌊L ^ q⌋₊
    let h := L ^ (-w)
    let ξ := L ^ (-x)
    ∀ {G : Type} [Fintype G] [DecidableEq G],
    ∀ (P : G → Finset ℕ) (V : G → ℝ),
    Pairwise (fun g h => Disjoint (P g) (P h)) →
    ∀ hP : ∀ g p, p ∈ P g → p.Prime ∧ Q < p,
    (∀ g, ∑ p ∈ P g, 1 / (p : ℝ) = V g) →
    (∀ g, v ≤ V g) →
    (∀ g p, p ∈ P g → Real.log p ≤ L ^ s) →
    (Fintype.card G : ℝ) ≤ a * Real.log L →
    (∀ g, ∃ a b : ℝ, P g = primeBand a b ∧ Real.exp (L ^ c) ≤ a ∧ 0 ≤ b) →
    ∀ probes : G → Finset (Fin J), (∀ g, (probes g).card = m) →
    ∀ r t : Finset G, ∀ hrt : Disjoint r t,
    beta * Real.log L ≤ (r.card : ℝ) → beta * Real.log L ≤ (t.card : ℝ) →
    ∀ ζ θ : ℝ, |ζ| ≤ L ^ z →
    ∀ F : ∀ g, Finset (P g), (∀ g, (F g).card ≤ J + ell) →
    let kept := fun U : Finset (RepeatedBigFlatIndex G J ell) => primeProductRetainedCells
      (fun i : U => P i.1.1) (fun i => V i.1.1) h ξ
    let C := repeatedBigPrimePatternCut (ell := ell) probes r t
    let K₀ := repeatedBigPrimePatternKernel P V probes r t hrt Q h kept
    let K := fun i => cleanInitialBirthKernel F (C i) (K₀ i)
    let weights := repeatedBigPrimePatternWeight (ell := ell) probes r t
    ∀ (b : ∀ g, P g → ℝ),
    ∀ T Pmin : ℝ, 0 ≤ T → T ≤ L ^ tau → Real.exp (L ^ c) ≤ Pmin →
    (∀ g (p : P g), Pmin ≤ (p.val : ℝ)) →
    (∀ g (p : P g), b g p = 1 - T / (p.val : ℝ)) →
    ∀ (S : Type) [Fintype S] (Ps : S → Finset ℕ) (fullB : ℕ) (k : ℤ)
      (ν : ∀ g, P g → ℝ) (ρ : ℝ),
    (∀ g p, 0 ≤ ν g p) → 0 ≤ ρ → ρ ≤ 1 →
    ∀ [∀ q : PhysicalPrime Ps, NeZero q.2.val] (d : PhysicalSharedLists Ps J),
    let _ : ∀ g (p : P g), NeZero p.val :=
      fun g p => ⟨(hP g p.val p.property).1.pos.ne'⟩
    ∀ f : CleanFullMemoryState P J ell fullB → PhysicalResidues Ps → ℂ,
    cleanWeightedNorm
      (productMemoryWeight (fun g => tiltedPhysicalBirthLaw V g (b g)) (fun g z => ν g z.1))
      (cleanFullMemoryActiveMap
        (cleanFullMemoryPatternDampedAction V b C ζ θ ρ k
          (fun i source target aux => weights i * K i source target aux) d
          (cleanFullMemoryActiveMap f))) ≤
      L ^ (-E) * cleanWeightedNorm
        (productMemoryWeight (fun g => tiltedPhysicalBirthLaw V g (b g)) (fun g z => ν g z.1)) f := by
  intro κ s' A₀ q w x
  filter_upwards [eventually_repeated_big_prime_initial_clean_power_bound
      hZ c s z a v D ε E beta tau m J ell hc hs hz ha hv hD hε htau hell hml hgap hDgap,
    eventually_repeated_big_baseline_pos (tau := tau) hc,
    eventually_gt_atTop (0 : ℝ)] with L hpower hbaseline hL
  intro Q h ξ G _ dG
  cases Subsingleton.elim dG (Classical.typeDecidableEq G)
  intro P V hdisj hP hmass hV hlog hcard hband probes hp r t hrt hr ht
    ζ θ hζ F hF kept C K₀ K weights b T Pmin hT hTmax hPminexp hpmin hb
    S _ Ps fullB k ν ρ hν hρ0 hρ1 _ d
  let _ : ∀ g (p : P g), NeZero p.val :=
    fun g p => ⟨(hP g p.val p.property).1.pos.ne'⟩
  intro _ f
  have hbpos : ∀ g p, 0 < b g p := by
    intro g p
    rw [hb g p]
    exact (hbaseline T Pmin hT hTmax hPminexp).2 p.val (hpmin g p)
  apply clean_full_memory_projected_damped_norm_le V b ν
    (fun g => (hv.trans_le (hV g)).le) (fun g p => (hbpos g p).le) hν
    C ζ θ ρ hρ0 hρ1 k (fun i source target aux => weights i * K i source target aux)
    d (L ^ (-E)) (Real.rpow_nonneg hL.le _) _ f
  intro N p u
  exact hpower P V hdisj hP hmass hV hlog hcard hband probes hp r t hrt hr ht
    ζ θ hζ F hF b T Pmin hT hTmax hPminexp hpmin hb
    S Ps (fun g => (N g).val) k p d u

theorem eventually_repeated_big_prime_initial_full_memory_cutoff_power_bound
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) (c s z a v D ε E beta tau : ℝ)
    (m J ell : ℕ)
    (hc : 0 < c) (hs : 0 ≤ s) (hz : 0 ≤ z) (ha : 0 ≤ a)
    (hv : 0 < v) (hD : 0 ≤ D) (hε : 0 < ε) (htau : 0 ≤ tau)
    (hell : 0 < ell) (hml : ell ≤ m)
    (hgap : beta * Real.log ((ell : ℝ) ^ ell / (m : ℝ) ^ ell) / 2 ≤ -(E + 2))
    (hDgap : (m : ℝ) * a * Real.log 3 + E + 2 ≤ D) :
    let κ := a * Real.log (primeFiberFactorBound v m)
    let s' := s + ε
    let A₀ := D + 2 * (s' + 1)
    let q := 2 * κ + (s' + 1) + 2 * A₀ + 3
    let w := 4 * q + max z q + A₀ + 2
    let x := (s' + w + 2) + 2 * A₀ + 2
    ∀ᶠ L : ℝ in atTop,
    let Q := ⌊L ^ q⌋₊
    let h := L ^ (-w)
    let ξ := L ^ (-x)
    ∀ {G : Type} [Fintype G] [DecidableEq G],
    ∀ (P : G → Finset ℕ) (V : G → ℝ),
    Pairwise (fun g h => Disjoint (P g) (P h)) →
    ∀ hP : ∀ g p, p ∈ P g → p.Prime ∧ Q < p,
    (∀ g, ∑ p ∈ P g, 1 / (p : ℝ) = V g) →
    (∀ g, v ≤ V g) →
    (∀ g p, p ∈ P g → Real.log p ≤ L ^ s) →
    (Fintype.card G : ℝ) ≤ a * Real.log L →
    (∀ g, ∃ a b : ℝ, P g = primeBand a b ∧ Real.exp (L ^ c) ≤ a ∧ 0 ≤ b) →
    ∀ probes : G → Finset (Fin J), (∀ g, (probes g).card = m) →
    ∀ r t : Finset G, ∀ hrt : Disjoint r t,
    beta * Real.log L ≤ (r.card : ℝ) → beta * Real.log L ≤ (t.card : ℝ) →
    ∀ ζ θ : ℝ, |ζ| ≤ L ^ z →
    ∀ F : ∀ g, Finset (P g), (∀ g, (F g).card ≤ J + ell) →
    let kept := fun U : Finset (RepeatedBigFlatIndex G J ell) => primeProductRetainedCells
      (fun i : U => P i.1.1) (fun i => V i.1.1) h ξ
    let C := repeatedBigPrimePatternCut (ell := ell) probes r t
    let K₀ := repeatedBigPrimePatternKernel P V probes r t hrt Q h kept
    let K := fun i => cleanInitialBirthKernel F (C i) (K₀ i)
    let weights := repeatedBigPrimePatternWeight (ell := ell) probes r t
    ∀ (b : ∀ g, P g → ℝ),
    ∀ T Pmin : ℝ, 0 ≤ T → T ≤ L ^ tau → Real.exp (L ^ c) ≤ Pmin →
    (∀ g (p : P g), Pmin ≤ (p.val : ℝ)) →
    (∀ g (p : P g), b g p = 1 - T / (p.val : ℝ)) →
    ∀ (S : Type) [Fintype S] (Ps : S → Finset ℕ) (fullB : ℕ) (k : ℤ)
      (ν : ∀ g, P g → ℝ) (ρ : ℝ),
    (∀ g p, 0 ≤ ν g p) → 0 ≤ ρ → ρ ≤ 1 →
    ∀ [∀ q : PhysicalPrime Ps, NeZero q.2.val] (d : PhysicalSharedLists Ps J),
    let _ : ∀ g (p : P g), NeZero p.val :=
      fun g p => ⟨(hP g p.val p.property).1.pos.ne'⟩
    ∀ f : CleanFullMemoryState P J ell fullB → PhysicalResidues Ps → ℂ,
    cleanWeightedNorm
      (productMemoryWeight (fun g => tiltedPhysicalBirthLaw V g (b g)) (fun g z => ν g z.1))
      (cleanFullMemoryCutoff (cleanFullMemoryActiveMap
        (cleanFullMemoryPatternDampedAction V b C ζ θ ρ k
          (fun i source target aux => weights i * K i source target aux) d
          (cleanFullMemoryActiveMap (cleanFullMemoryCutoff f))))) ≤
      L ^ (-E) * cleanWeightedNorm
        (productMemoryWeight (fun g => tiltedPhysicalBirthLaw V g (b g)) (fun g z => ν g z.1)) f := by
  intro κ s' A₀ q w x
  filter_upwards [eventually_repeated_big_prime_initial_full_memory_power_bound
      hZ c s z a v D ε E beta tau m J ell hc hs hz ha hv hD hε htau hell hml hgap hDgap,
    eventually_repeated_big_baseline_pos (tau := tau) hc,
    eventually_gt_atTop (0 : ℝ)] with L hpower hbaseline hL
  intro Q h ξ G _ dG
  cases Subsingleton.elim dG (Classical.typeDecidableEq G)
  intro P V hdisj hP hmass hV hlog hcard hband probes hp r t hrt hr ht
    ζ θ hζ F hF kept C K₀ K weights b T Pmin hT hTmax hPminexp hpmin hb
    S _ Ps fullB k ν ρ hν hρ0 hρ1 _ d
  let _ : ∀ g (p : P g), NeZero p.val :=
    fun g p => ⟨(hP g p.val p.property).1.pos.ne'⟩
  intro _ f
  have hbpos : ∀ g p, 0 < b g p := by
    intro g p
    rw [hb g p]
    exact (hbaseline T Pmin hT hTmax hPminexp).2 p.val (hpmin g p)
  apply clean_full_memory_cutoff_sandwich_norm_le
    (fun g => tiltedPhysicalBirthLaw V g (b g)) ν
    (fun g p => tiltedPhysicalBirthLaw_nonneg V g (b g)
      (hv.trans_le (hV g)).le (fun p => (hbpos g p).le) p) hν
    (fun u => cleanFullMemoryActiveMap (cleanFullMemoryPatternDampedAction V b C ζ θ ρ k
      (fun i source target aux => weights i * K i source target aux) d
        (cleanFullMemoryActiveMap u)))
    (L ^ (-E)) (Real.rpow_nonneg hL.le _) _ f
  intro u
  exact hpower P V hdisj hP hmass hV hlog hcard hband probes hp r t hrt hr ht
    ζ θ hζ F hF b T Pmin hT hTmax hPminexp hpmin hb
    S Ps fullB k ν ρ hν hρ0 hρ1 d u

theorem eventually_repeated_big_prime_initial_literal_event_power_bound
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) (c s z a v D ε E beta tau : ℝ)
    (m J ell : ℕ)
    (hc : 0 < c) (hs : 0 ≤ s) (hz : 0 ≤ z) (ha : 0 ≤ a)
    (hv : 0 < v) (hD : 0 ≤ D) (hε : 0 < ε) (htau : 0 ≤ tau)
    (hell : 0 < ell) (hml : ell ≤ m)
    (hgap : beta * Real.log ((ell : ℝ) ^ ell / (m : ℝ) ^ ell) / 2 ≤ -(E + 2))
    (hDgap : (m : ℝ) * a * Real.log 3 + E + 2 ≤ D) :
    let κ := a * Real.log (primeFiberFactorBound v m)
    let s' := s + ε
    let A₀ := D + 2 * (s' + 1)
    let q := 2 * κ + (s' + 1) + 2 * A₀ + 3
    let w := 4 * q + max z q + A₀ + 2
    let x := (s' + w + 2) + 2 * A₀ + 2
    ∀ᶠ L : ℝ in atTop,
    let Q := ⌊L ^ q⌋₊
    let h := L ^ (-w)
    let ξ := L ^ (-x)
    ∀ {G : Type} [Fintype G] [DecidableEq G],
    ∀ (P : G → Finset ℕ) (V : G → ℝ),
    Pairwise (fun g h => Disjoint (P g) (P h)) →
    ∀ hP : ∀ g p, p ∈ P g → p.Prime ∧ Q < p,
    (∀ g, ∑ p ∈ P g, 1 / (p : ℝ) = V g) →
    (∀ g, v ≤ V g) →
    (∀ g p, p ∈ P g → Real.log p ≤ L ^ s) →
    (Fintype.card G : ℝ) ≤ a * Real.log L →
    (∀ g, ∃ a b : ℝ, P g = primeBand a b ∧ Real.exp (L ^ c) ≤ a ∧ 0 ≤ b) →
    ∀ probes : G → Finset (Fin J), (∀ g, (probes g).card = m) →
    ∀ r t : Finset G, ∀ hrt : Disjoint r t,
    beta * Real.log L ≤ (r.card : ℝ) → beta * Real.log L ≤ (t.card : ℝ) →
    ∀ ζ θ : ℝ, |ζ| ≤ L ^ z →
    ∀ F : ∀ g, Finset (P g), (∀ g, (F g).card ≤ J + ell) →
    let kept := fun U : Finset (RepeatedBigFlatIndex G J ell) => primeProductRetainedCells
      (fun i : U => P i.1.1) (fun i => V i.1.1) h ξ
    let C := repeatedBigPrimePatternCut (ell := ell) probes r t
    let K₀ := repeatedBigPrimePatternKernel P V probes r t hrt Q h kept
    let weights := repeatedBigPrimePatternWeight (ell := ell) probes r t
    ∀ (b : ∀ g, P g → ℝ),
    ∀ T Pmin : ℝ, 0 ≤ T → T ≤ L ^ tau → Real.exp (L ^ c) ≤ Pmin →
    (∀ g (p : P g), Pmin ≤ (p.val : ℝ)) →
    (∀ g (p : P g), b g p = 1 - T / (p.val : ℝ)) →
    ∀ (S : Type) [Fintype S] (Ps : S → Finset ℕ) (fullB : ℕ) (k : ℤ)
      (ν : ∀ g, P g → ℝ) (ρ : ℝ),
    (∀ g p, 0 ≤ ν g p) → 0 ≤ ρ → ρ ≤ 1 →
    ∀ [∀ q : PhysicalPrime Ps, NeZero q.2.val] (d : PhysicalSharedLists Ps J),
    let _ : ∀ g (p : P g), NeZero p.val :=
      fun g p => ⟨(hP g p.val p.property).1.pos.ne'⟩
    ∀ Dban : ∀ i, SharedActiveLabels (fun g => ↥(P g)) (cleanFullSharedSlots (ell := ell) (C i)) →
      PhysicalAuxLabels P (C i) → G → ℤ,
    ∀ f : CleanFullMemoryState P J ell fullB → PhysicalResidues Ps → ℂ,
    (∀ rs, ProductMemorySymmetric (fun x => f x rs)) →
    cleanWeightedNorm
      (productMemoryWeight (fun g => tiltedPhysicalBirthLaw V g (b g)) (fun g z => ν g z.1))
      (cleanFullMemoryActiveMap (cleanFullMemoryInitialPatternEventAction F V b C ζ θ ρ k Dban
        (fun i source target aux => weights i * K₀ i source target aux) d
        (cleanFullMemoryActiveMap f))) ≤
      L ^ (-E) * cleanWeightedNorm
        (productMemoryWeight (fun g => tiltedPhysicalBirthLaw V g (b g)) (fun g z => ν g z.1)) f := by
  intro κ s' A₀ q w x
  filter_upwards [eventually_repeated_big_prime_initial_full_memory_cutoff_power_bound
    hZ c s z a v D ε E beta tau m J ell hc hs hz ha hv hD hε htau hell hml hgap hDgap]
    with L hpower
  intro Q h ξ G _ dG
  cases Subsingleton.elim dG (Classical.typeDecidableEq G)
  intro P V hdisj hP hmass hV hlog hcard hband probes hp r t hrt hr ht
    ζ θ hζ F hF kept C K₀ weights b T Pmin hT hTmax hPminexp hpmin hb
    S _ Ps fullB k ν ρ hν hρ0 hρ1 _ d
  let _ : ∀ g (p : P g), NeZero p.val :=
    fun g p => ⟨(hP g p.val p.property).1.pos.ne'⟩
  intro _ Dban f hf
  let K := fun i => cleanInitialBirthKernel F (C i) (K₀ i)
  have hK : (fun (i : RepeatedBigPrimePatternIndex (ell := ell) probes r t) =>
      cleanInitialBirthKernel F (C i) (fun source target aux => weights i * K₀ i source target aux)) =
      (fun i source target aux => weights i * K i source target aux) := by
    funext i source target aux
    dsimp only [K, cleanInitialBirthKernel]
    split_ifs <;> simp only [mul_zero]
  rw [clean_full_memory_initial_projected_action F V b C ζ θ ρ k Dban
    (fun i source target aux => weights i * K₀ i source target aux) d f hf]
  erw [hK]
  exact hpower P V hdisj hP hmass hV hlog hcard hband probes hp r t hrt hr ht
    ζ θ hζ F hF b T Pmin hT hTmax hPminexp hpmin hb
    S Ps fullB k ν ρ hν hρ0 hρ1 d f

theorem exists_candidate_unbalanced_rough_finite_bins_upper
    {ι : Type*} [Fintype ι]
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q S : ℝ} {r : ℕ}
    {γ a v M : ι → ℝ}
    (hc : 0 < c) (hr : 0 < r) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcenter : (11 / 5 : ℝ) * (r : ℝ) * c = 1)
    (hγ : ∀ i, 0 < γ i) (ha : ∀ i, 0 < a i) (hav : ∀ i, a i ≤ v i)
    (hvhalf : ∀ i, v i < 1 / 2) (hvγ : ∀ i, v i < 1 - γ i)
    (hS : 0 ≤ S) (hM : ∀ i, 0 ≤ M i)
    (hdensity : ∀ i, ∀ α ∈ Set.Icc (a i) (v i), buchstabDensity (γ i) (1 - α) ≤ M i) :
    ∃ J : ℕ, ∀ jStar : ℕ, J < jStar → ∀ ε : ℝ, 0 < ε →
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
  have hbins := fun i => exists_candidate_unbalanced_rough_bin_upper
    hZ hc hr hq0 hq1 hcenter (hγ i) (ha i) (hav i) (hvhalf i) (hvγ i)
    hS (hM i) (hdensity i)
  choose Js hJs using hbins
  refine ⟨Finset.univ.sup Js, ?_⟩
  intro jStar hj ε hε
  let δ := ε / ((Fintype.card ι : ℝ) + 1)
  have hden : 0 < (Fintype.card ι : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hδeq : ((Fintype.card ι : ℝ) + 1) * δ = ε := by
    dsimp [δ]
    field_simp
  have hδerror : (Fintype.card ι : ℝ) * δ ≤ ε := by nlinarith
  have hbinEvent := fun i => hJs i jStar
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

theorem eventually_repeated_big_prime_initial_mixed_pairing_power_bound
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) (c s z a v D ε E beta tau : ℝ)
    (m J ell : ℕ)
    (hc : 0 < c) (hs : 0 ≤ s) (hz : 0 ≤ z) (ha : 0 ≤ a)
    (hv : 0 < v) (hD : 0 ≤ D) (hε : 0 < ε) (htau : 0 ≤ tau)
    (hell : 0 < ell) (hml : ell ≤ m)
    (hgap : beta * Real.log ((ell : ℝ) ^ ell / (m : ℝ) ^ ell) / 2 ≤ -(E + 2))
    (hDgap : (m : ℝ) * a * Real.log 3 + E + 2 ≤ D)
    (qsmall vsmall : ℝ) (hq0 : 0 ≤ qsmall) (hq1 : qsmall < 1) (hvs : 0 < vsmall) :
    ∃ A : ℝ, 1 ≤ A ∧
    let κ := a * Real.log (primeFiberFactorBound v m)
    let s' := s + ε
    let A₀ := D + 2 * (s' + 1)
    let q := 2 * κ + (s' + 1) + 2 * A₀ + 3
    let w := 4 * q + max z q + A₀ + 2
    let x := (s' + w + 2) + 2 * A₀ + 2
    ∀ᶠ L : ℝ in atTop,
    let Q := ⌊L ^ q⌋₊
    let h := L ^ (-w)
    let ξ := L ^ (-x)
    ∀ {G : Type} [Fintype G] [DecidableEq G],
    ∀ (P : G → Finset ℕ) (V : G → ℝ),
    Pairwise (fun g h => Disjoint (P g) (P h)) →
    ∀ hP : ∀ g p, p ∈ P g → p.Prime ∧ Q < p,
    (∀ g, ∑ p ∈ P g, 1 / (p : ℝ) = V g) →
    (∀ g, v ≤ V g) →
    (∀ g p, p ∈ P g → Real.log p ≤ L ^ s) →
    (Fintype.card G : ℝ) ≤ a * Real.log L →
    (∀ g, ∃ a b : ℝ, P g = primeBand a b ∧ Real.exp (L ^ c) ≤ a ∧ 0 ≤ b) →
    ∀ probes : G → Finset (Fin J), (∀ g, (probes g).card = m) →
    ∀ r t : Finset G, ∀ hrt : Disjoint r t,
    beta * Real.log L ≤ (r.card : ℝ) → beta * Real.log L ≤ (t.card : ℝ) →
    ∀ ζ θ : ℝ, |ζ| ≤ L ^ z →
    ∀ F : ∀ g, Finset (P g), (∀ g, (F g).card ≤ J + ell) →
    let kept := fun U : Finset (RepeatedBigFlatIndex G J ell) => primeProductRetainedCells
      (fun i : U => P i.1.1) (fun i => V i.1.1) h ξ
    let C := repeatedBigPrimePatternCut (ell := ell) probes r t
    let K₀ := repeatedBigPrimePatternKernel P V probes r t hrt Q h kept
    let weights := repeatedBigPrimePatternWeight (ell := ell) probes r t
    ∀ (b : ∀ g, P g → ℝ),
    ∀ T Pmin : ℝ, 0 ≤ T → T ≤ L ^ tau → Real.exp (L ^ c) ≤ Pmin →
    (∀ g (p : P g), Pmin ≤ (p.val : ℝ)) →
    (∀ g (p : P g), b g p = 1 - T / (p.val : ℝ)) →
    ∀ (S : Type) [Fintype S] [DecidableEq S] (Ps : S → Finset ℕ) (fullB : ℕ) (k : ℤ)
      (ν : ∀ g, P g → ℝ) (ρ : ℝ),
    (∀ g p, 0 ≤ ν g p) → 0 ≤ ρ → ρ ≤ 1 →
    ∀ [∀ q : PhysicalPrime Ps, NeZero q.2.val],
    let _ : ∀ g (p : P g), NeZero p.val :=
      fun g p => ⟨(hP g p.val p.property).1.pos.ne'⟩
    ∀ Dban : ∀ i, SharedActiveLabels (fun g => ↥(P g)) (cleanFullSharedSlots (ell := ell) (C i)) →
      PhysicalAuxLabels P (C i) → G → ℤ,
    let W : CleanFullMemoryState P J ell fullB → ℝ := productMemoryWeight (fun g => tiltedPhysicalBirthLaw V g (b g)) (fun g z => ν g z.1)
    let Tclean := fun (d : PhysicalSharedLists Ps J)
        (u : CleanFullMemoryState P J ell fullB → PhysicalResidues Ps → ℂ) =>
      cleanFullMemoryActiveMap (cleanFullMemoryInitialPatternEventAction F V b C ζ θ ρ k Dban
        (fun i source target aux => weights i * K₀ i source target aux) d
        (cleanFullMemoryActiveMap u))
    ∀ (Vs : S → ℝ), (∀ s, vsmall ≤ Vs s) →
    ∀ sourceGate targetGate : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell fullB) → ℂ,
    (∀ s, ‖sourceGate s‖ ≤ 1) → (∀ s, ‖targetGate s‖ ≤ 1) →
    ∀ f output : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell fullB) → ℂ,
    (∀ s, ProductMemorySymmetric (fun x => targetGate (s,x) * f (s,x))) →
    (∀ u : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell fullB) → ℂ,
      (∑ s, (physicalSmallBigMeasure Vs W s : ℂ) * (starRingEnd ℂ) (u s) * output s) =
        ∑ d, ∑ rs, ∑ x, (W x : ℂ) *
          (starRingEnd ℂ) (physicalSmallBigCondition Vs qsmall (fun s => sourceGate s * u s) d x rs) *
          Tclean d (physicalSmallBigCondition Vs qsmall (fun s => targetGate s * f s) d) x rs) →
    physicalSmallBigEnergy Vs W output ≤
      A ^ (2 * Fintype.card S) * (L ^ (-E)) ^ 2 * physicalSmallBigEnergy Vs W f := by
  obtain ⟨A, hA, hbound⟩ := exists_physical_small_big_clean_pairing_energy_bound hq0 hq1 hvs ell
  refine ⟨A, hA, ?_⟩
  intro κ s' A₀ q w x
  filter_upwards [eventually_repeated_big_prime_initial_literal_event_power_bound
      hZ c s z a v D ε E beta tau m J ell hc hs hz ha hv hD hε htau hell hml hgap hDgap,
    eventually_repeated_big_baseline_pos (tau := tau) hc,
    eventually_gt_atTop (0 : ℝ)] with L hpower hbaseline hL
  intro Q h ξ G _ dG
  cases Subsingleton.elim dG (Classical.typeDecidableEq G)
  intro P V hdisj hP hmass hV hlog hcard hband probes hp r t hrt hr ht
    ζ θ hζ F hF kept C K₀ weights b T Pmin hT hTmax hPminexp hpmin hb
    S _ dS
  cases Subsingleton.elim dS (Classical.typeDecidableEq S)
  intro Ps fullB k ν ρ hν hρ0 hρ1 _
  let _ : ∀ g (p : P g), NeZero p.val :=
    fun g p => ⟨(hP g p.val p.property).1.pos.ne'⟩
  intro _ Dban W Tclean Vs hVs sourceGate targetGate hsg htg f output hf hpair
  have hbpos : ∀ g p, 0 < b g p := by
    intro g p
    rw [hb g p]
    exact (hbaseline T Pmin hT hTmax hPminexp).2 p.val (hpmin g p)
  have hW : ∀ x, 0 ≤ W x := productMemoryWeight_nonneg _ _
    (fun g p => tiltedPhysicalBirthLaw_nonneg V g (b g)
      (hv.trans_le (hV g)).le (fun p => (hbpos g p).le) p) (fun g p => hν g p.1)
  apply hbound S (CleanFullMemoryState P J ell fullB) Ps J Vs hVs W hW
    sourceGate targetGate hsg htg (L ^ (-E)) (Real.rpow_nonneg hL.le _)
    f output (fun d => Tclean d (physicalSmallBigCondition Vs qsmall
      (fun s => targetGate s * f s) d)) _ hpair
  intro d
  exact hpower P V hdisj hP hmass hV hlog hcard hband probes hp r t hrt hr ht
    ζ θ hζ F hF b T Pmin hT hTmax hPminexp hpmin hb
    S Ps fullB k ν ρ hν hρ0 hρ1 d Dban _
    (fun rs => physical_small_big_condition_memory_symmetric Vs qsmall _ hf d rs)

theorem exists_uniform_repeated_big_prime_initial_mixed_power_bound
    (qsmall vsmall : ℝ) (ell : ℕ)
    (hq0 : 0 ≤ qsmall) (hq1 : qsmall < 1) (hvs : 0 < vsmall) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀
    (_hZ : PrimitiveZeroFreeRightOf (23 / 24)) (c s z a v D ε E beta tau : ℝ)
    (m J : ℕ)
    (_hc : 0 < c) (_hs : 0 ≤ s) (_hz : 0 ≤ z) (_ha : 0 ≤ a)
    (_hv : 0 < v) (_hD : 0 ≤ D) (_hε : 0 < ε) (_htau : 0 ≤ tau)
    (_hell : 0 < ell) (_hml : ell ≤ m)
    (_hgap : beta * Real.log ((ell : ℝ) ^ ell / (m : ℝ) ^ ell) / 2 ≤ -(E + 2))
    (_hDgap : (m : ℝ) * a * Real.log 3 + E + 2 ≤ D),
    let κ := a * Real.log (primeFiberFactorBound v m)
    let s' := s + ε
    let A₀ := D + 2 * (s' + 1)
    let q := 2 * κ + (s' + 1) + 2 * A₀ + 3
    let w := 4 * q + max z q + A₀ + 2
    let x := (s' + w + 2) + 2 * A₀ + 2
    ∀ᶠ L : ℝ in atTop,
    let Q := ⌊L ^ q⌋₊
    let h := L ^ (-w)
    let ξ := L ^ (-x)
    ∀ {G : Type} [Fintype G] [DecidableEq G],
    ∀ (P : G → Finset ℕ) (V : G → ℝ),
    Pairwise (fun g h => Disjoint (P g) (P h)) →
    ∀ hP : ∀ g p, p ∈ P g → p.Prime ∧ Q < p,
    (∀ g, ∑ p ∈ P g, 1 / (p : ℝ) = V g) →
    (∀ g, v ≤ V g) →
    (∀ g p, p ∈ P g → Real.log p ≤ L ^ s) →
    (Fintype.card G : ℝ) ≤ a * Real.log L →
    (∀ g, ∃ a b : ℝ, P g = primeBand a b ∧ Real.exp (L ^ c) ≤ a ∧ 0 ≤ b) →
    ∀ probes : G → Finset (Fin J), (∀ g, (probes g).card = m) →
    ∀ r t : Finset G, ∀ hrt : Disjoint r t,
    beta * Real.log L ≤ (r.card : ℝ) → beta * Real.log L ≤ (t.card : ℝ) →
    ∀ ζ θ : ℝ, |ζ| ≤ L ^ z →
    ∀ F : ∀ g, Finset (P g), (∀ g, (F g).card ≤ J + ell) →
    let kept := fun U : Finset (RepeatedBigFlatIndex G J ell) => primeProductRetainedCells
      (fun i : U => P i.1.1) (fun i => V i.1.1) h ξ
    let C := repeatedBigPrimePatternCut (ell := ell) probes r t
    let K₀ := repeatedBigPrimePatternKernel P V probes r t hrt Q h kept
    let weights := repeatedBigPrimePatternWeight (ell := ell) probes r t
    ∀ (b : ∀ g, P g → ℝ),
    ∀ T Pmin : ℝ, 0 ≤ T → T ≤ L ^ tau → Real.exp (L ^ c) ≤ Pmin →
    (∀ g (p : P g), Pmin ≤ (p.val : ℝ)) →
    (∀ g (p : P g), b g p = 1 - T / (p.val : ℝ)) →
    ∀ (S : Type) [Fintype S] [DecidableEq S] (Ps : S → Finset ℕ) (fullB : ℕ) (k : ℤ)
      (ν : ∀ g, P g → ℝ) (ρ : ℝ),
    (∀ g p, 0 ≤ ν g p) → 0 ≤ ρ → ρ ≤ 1 →
    ∀ [∀ q : PhysicalPrime Ps, NeZero q.2.val],
    let _ : ∀ g (p : P g), NeZero p.val :=
      fun g p => ⟨(hP g p.val p.property).1.pos.ne'⟩
    ∀ Dban : ∀ i, SharedActiveLabels (fun g => ↥(P g)) (cleanFullSharedSlots (ell := ell) (C i)) →
      PhysicalAuxLabels P (C i) → G → ℤ,
    let W : CleanFullMemoryState P J ell fullB → ℝ := productMemoryWeight (fun g => tiltedPhysicalBirthLaw V g (b g)) (fun g z => ν g z.1)
    let Tclean := fun (d : PhysicalSharedLists Ps J)
        (u : CleanFullMemoryState P J ell fullB → PhysicalResidues Ps → ℂ) =>
      cleanFullMemoryActiveMap (cleanFullMemoryInitialPatternEventAction F V b C ζ θ ρ k Dban
        (fun i source target aux => weights i * K₀ i source target aux) d
        (cleanFullMemoryActiveMap u))
    ∀ (Vs : S → ℝ), (∀ s, vsmall ≤ Vs s) →
    ∀ sourceGate targetGate : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell fullB) → ℂ,
    (∀ s, ‖sourceGate s‖ ≤ 1) → (∀ s, ‖targetGate s‖ ≤ 1) →
    ∀ f output : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell fullB) → ℂ,
    (∀ s, ProductMemorySymmetric (fun x => targetGate (s,x) * f (s,x))) →
    (∀ u : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell fullB) → ℂ,
      (∑ s, (physicalSmallBigMeasure Vs W s : ℂ) * (starRingEnd ℂ) (u s) * output s) =
        ∑ d, ∑ rs, ∑ x, (W x : ℂ) *
          (starRingEnd ℂ) (physicalSmallBigCondition Vs qsmall (fun s => sourceGate s * u s) d x rs) *
          Tclean d (physicalSmallBigCondition Vs qsmall (fun s => targetGate s * f s) d) x rs) →
    physicalSmallBigEnergy Vs W output ≤
      A ^ (2 * Fintype.card S) * (L ^ (-E)) ^ 2 * physicalSmallBigEnergy Vs W f := by
  obtain ⟨A, hA, hbound⟩ := exists_physical_small_big_clean_pairing_energy_bound hq0 hq1 hvs ell
  refine ⟨A, hA, ?_⟩
  intro hZ c s z a v D ε E beta tau m J hc hs hz ha hv hD hε htau hell hml hgap hDgap κ s' A₀ q w x
  filter_upwards [eventually_repeated_big_prime_initial_literal_event_power_bound
      hZ c s z a v D ε E beta tau m J ell hc hs hz ha hv hD hε htau hell hml hgap hDgap,
    eventually_repeated_big_baseline_pos (tau := tau) hc,
    eventually_gt_atTop (0 : ℝ)] with L hpower hbaseline hL
  intro Q h ξ G _ dG
  cases Subsingleton.elim dG (Classical.typeDecidableEq G)
  intro P V hdisj hP hmass hV hlog hcard hband probes hp r t hrt hr ht
    ζ θ hζ F hF kept C K₀ weights b T Pmin hT hTmax hPminexp hpmin hb
    S _ dS
  cases Subsingleton.elim dS (Classical.typeDecidableEq S)
  intro Ps fullB k ν ρ hν hρ0 hρ1 _
  let _ : ∀ g (p : P g), NeZero p.val :=
    fun g p => ⟨(hP g p.val p.property).1.pos.ne'⟩
  intro _ Dban W Tclean Vs hVs sourceGate targetGate hsg htg f output hf hpair
  have hbpos : ∀ g p, 0 < b g p := by
    intro g p
    rw [hb g p]
    exact (hbaseline T Pmin hT hTmax hPminexp).2 p.val (hpmin g p)
  have hW : ∀ x, 0 ≤ W x := productMemoryWeight_nonneg _ _
    (fun g p => tiltedPhysicalBirthLaw_nonneg V g (b g)
      (hv.trans_le (hV g)).le (fun p => (hbpos g p).le) p) (fun g p => hν g p.1)
  apply hbound S (CleanFullMemoryState P J ell fullB) Ps J Vs hVs W hW
    sourceGate targetGate hsg htg (L ^ (-E)) (Real.rpow_nonneg hL.le _)
    f output (fun d => Tclean d (physicalSmallBigCondition Vs qsmall
      (fun s => targetGate s * f s) d)) _ hpair
  intro d
  exact hpower P V hdisj hP hmass hV hlog hcard hband probes hp r t hrt hr ht
    ζ θ hζ F hF b T Pmin hT hTmax hPminexp hpmin hb
    S Ps fullB k ν ρ hν hρ0 hρ1 d Dban _
    (fun rs => physical_small_big_condition_memory_symmetric Vs qsmall _ hf d rs)

theorem exists_physical_mixed_clean_prime_power_bound
    (qsmall vsmall : ℝ) (ell : ℕ)
    (hq0 : 0 ≤ qsmall) (hq1 : qsmall < 1) (hvs : 0 < vsmall) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀
    (_hZ : PrimitiveZeroFreeRightOf (23 / 24)) (c s z a v D ε E beta tau : ℝ)
    (m J : ℕ)
    (_hc : 0 < c) (_hs : 0 ≤ s) (_hz : 0 ≤ z) (_ha : 0 ≤ a)
    (_hv : 0 < v) (_hD : 0 ≤ D) (_hε : 0 < ε) (_htau : 0 ≤ tau)
    (_hell : 0 < ell) (_hml : ell ≤ m)
    (_hgap : beta * Real.log ((ell : ℝ) ^ ell / (m : ℝ) ^ ell) / 2 ≤ -(E + 2))
    (_hDgap : (m : ℝ) * a * Real.log 3 + E + 2 ≤ D),
    let κ := a * Real.log (primeFiberFactorBound v m)
    let s' := s + ε
    let A₀ := D + 2 * (s' + 1)
    let q := 2 * κ + (s' + 1) + 2 * A₀ + 3
    let w := 4 * q + max z q + A₀ + 2
    let x := (s' + w + 2) + 2 * A₀ + 2
    ∀ᶠ L : ℝ in atTop,
    let Q := ⌊L ^ q⌋₊
    let h := L ^ (-w)
    let ξ := L ^ (-x)
    ∀ {G : Type} [Fintype G] [DecidableEq G],
    ∀ (P : G → Finset ℕ) (V : G → ℝ),
    Pairwise (fun g h => Disjoint (P g) (P h)) →
    ∀ hP : ∀ g p, p ∈ P g → p.Prime ∧ Q < p,
    (∀ g, ∑ p ∈ P g, 1 / (p : ℝ) = V g) →
    (∀ g, v ≤ V g) →
    (∀ g p, p ∈ P g → Real.log p ≤ L ^ s) →
    (Fintype.card G : ℝ) ≤ a * Real.log L →
    (∀ g, ∃ a b : ℝ, P g = primeBand a b ∧ Real.exp (L ^ c) ≤ a ∧ 0 ≤ b) →
    ∀ probes : G → Finset (Fin J), (∀ g, (probes g).card = m) →
    ∀ r t : Finset G, ∀ hrt : Disjoint r t,
    beta * Real.log L ≤ (r.card : ℝ) → beta * Real.log L ≤ (t.card : ℝ) →
    ∀ ζ θ : ℝ, |ζ| ≤ L ^ z →
    ∀ F : ∀ g, Finset (P g), (∀ g, (F g).card ≤ J + ell) →
    let kept := fun U : Finset (RepeatedBigFlatIndex G J ell) => primeProductRetainedCells
      (fun i : U => P i.1.1) (fun i => V i.1.1) h ξ
    let C := repeatedBigPrimePatternCut (ell := ell) probes r t
    let K₀ := repeatedBigPrimePatternKernel P V probes r t hrt Q h kept
    let weights := repeatedBigPrimePatternWeight (ell := ell) probes r t
    ∀ (b : ∀ g, P g → ℝ),
    ∀ T Pmin : ℝ, 0 ≤ T → T ≤ L ^ tau → Real.exp (L ^ c) ≤ Pmin →
    (∀ g (p : P g), Pmin ≤ (p.val : ℝ)) →
    (∀ g (p : P g), b g p = 1 - T / (p.val : ℝ)) →
    ∀ (S : Type) [Fintype S] [DecidableEq S] (Ps : S → Finset ℕ) (fullB : ℕ) (k : ℤ)
      (ν : ∀ g, P g → ℝ) (ρ : ℝ),
    (∀ g p, 0 ≤ ν g p) → 0 ≤ ρ → ρ ≤ 1 →
    ∀ [∀ q : PhysicalPrime Ps, NeZero q.2.val],
    let _ : ∀ g (p : P g), NeZero p.val :=
      fun g p => ⟨(hP g p.val p.property).1.pos.ne'⟩
    let W : CleanFullMemoryState P J ell fullB → ℝ := productMemoryWeight (fun g => tiltedPhysicalBirthLaw V g (b g)) (fun g z => ν g z.1)
    ∀ (Vs : S → ℝ), (∀ s, vsmall ≤ Vs s) →
    ∀ sourceGate targetGate : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell fullB) → ℂ,
    (∀ s, ‖sourceGate s‖ ≤ 1) → (∀ s, ‖targetGate s‖ ≤ 1) →
    (∀ s (τ : FullActiveSlotPermutations (fun _ : G => J + ell)),
      sourceGate (s.1, fullActivePermutation τ s.2) = sourceGate s) →
    (∀ s (τ : FullActiveSlotPermutations (fun _ : G => J + ell)),
      targetGate (s.1, fullActivePermutation τ s.2) = targetGate s) →
    ∀ f : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell fullB) → ℂ,
    (∀ s, ProductMemorySymmetric (fun x => targetGate (s,x) * f (s,x))) →
    physicalSmallBigEnergy Vs W
      (physicalSmallBigBigAverage (physicalMixedGatedCleanPatternAction F V b C ζ θ ρ k
        (fun i source target aux => weights i * K₀ i source target aux)
        Vs qsmall sourceGate targetGate (physicalSmallBigBigAverage f))) ≤
      A ^ (2 * Fintype.card S) * (L ^ (-E)) ^ 2 * physicalSmallBigEnergy Vs W f := by
  obtain ⟨A, hA, hbound⟩ := exists_physical_small_big_clean_pairing_energy_bound hq0 hq1 hvs ell
  refine ⟨A, hA, ?_⟩
  intro hZ c s z a v D ε E beta tau m J hc hs hz ha hv hD hε htau hell hml hgap hDgap κ s' A₀ q w x
  filter_upwards [eventually_repeated_big_prime_initial_literal_event_power_bound
      hZ c s z a v D ε E beta tau m J ell hc hs hz ha hv hD hε htau hell hml hgap hDgap,
    eventually_repeated_big_baseline_pos (tau := tau) hc,
    eventually_gt_atTop (0 : ℝ)] with L hpower hbaseline hL
  intro Q h ξ G _ dG
  cases Subsingleton.elim dG (Classical.typeDecidableEq G)
  intro P V hdisj hP hmass hV hlog hcard hband probes hp r t hrt hr ht
    ζ θ hζ F hF kept C K₀ weights b T Pmin hT hTmax hPminexp hpmin hb
    S _ dS
  cases Subsingleton.elim dS (Classical.typeDecidableEq S)
  intro Ps fullB k ν ρ hν hρ0 hρ1 _
  let _ : ∀ g (p : P g), NeZero p.val :=
    fun g p => ⟨(hP g p.val p.property).1.pos.ne'⟩
  intro _ W Vs hVs sourceGate targetGate hsg htg hsgPerm htgPerm f hf
  have hbpos : ∀ g p, 0 < b g p := by
    intro g p
    rw [hb g p]
    exact (hbaseline T Pmin hT hTmax hPminexp).2 p.val (hpmin g p)
  have hW : ∀ x, 0 ≤ W x := productMemoryWeight_nonneg _ _
    (fun g p => tiltedPhysicalBirthLaw_nonneg V g (b g)
      (hv.trans_le (hV g)).le (fun p => (hbpos g p).le) p) (fun g p => hν g p.1)
  let K := fun i source target aux => weights i * K₀ i source target aux
  let output := physicalSmallBigBigAverage (physicalMixedGatedCleanPatternAction F V b C
    ζ θ ρ k K Vs qsmall sourceGate targetGate (physicalSmallBigBigAverage f))
  let Tclean := fun (d : PhysicalSharedLists Ps J)
      (u : CleanFullMemoryState P J ell fullB → PhysicalResidues Ps → ℂ) =>
    cleanFullMemoryActiveMap (cleanFullMemoryInitialPatternEventAction F V b C ζ θ ρ k
      (fun i => canonicalMixedEdgeD (C i) d) K d (cleanFullMemoryActiveMap u))
  have hPs : ∀ s p, p ∈ Ps s → 0 < p := by
    intro s p hp
    exact Nat.pos_of_ne_zero (NeZero.ne (show ℕ from (⟨s, ⟨p, hp⟩⟩ : PhysicalPrime Ps).2.val))
  have hpair (u : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell fullB) → ℂ) :
      (∑ s, (physicalSmallBigMeasure Vs W s : ℂ) * (starRingEnd ℂ) (u s) * output s) =
        ∑ d, ∑ rs, ∑ x, (W x : ℂ) *
          (starRingEnd ℂ) (physicalSmallBigCondition Vs qsmall (fun s => sourceGate s * u s) d x rs) *
          Tclean d (physicalSmallBigCondition Vs qsmall (fun s => targetGate s * f s) d) x rs := by
    exact physical_mixed_gated_clean_pattern_projected_pairing F V b C ζ θ ρ k K Vs
      (fun s => hvs.trans_le (hVs s)) qsmall ν sourceGate targetGate hsgPerm htgPerm
      u f hf hPs (fun g p hp => (hP g p hp).1.pos)
  apply hbound S (CleanFullMemoryState P J ell fullB) Ps J Vs hVs W hW
    sourceGate targetGate hsg htg (L ^ (-E)) (Real.rpow_nonneg hL.le _)
    f output (fun d => Tclean d (physicalSmallBigCondition Vs qsmall
      (fun s => targetGate s * f s) d)) _ hpair
  intro d
  exact hpower P V hdisj hP hmass hV hlog hcard hband probes hp r t hrt hr ht
    ζ θ hζ F hF b T Pmin hT hTmax hPminexp hpmin hb
    S Ps fullB k ν ρ hν hρ0 hρ1 d (fun i => canonicalMixedEdgeD (C i) d) _
    (fun rs => physical_small_big_condition_memory_symmetric Vs qsmall _ hf d rs)

theorem exists_physical_mixed_clean_prime_joint_norm_bound
    (qsmall vsmall : ℝ) (ell : ℕ)
    (hq0 : 0 ≤ qsmall) (hq1 : qsmall < 1) (hvs : 0 < vsmall) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀
    (_hZ : PrimitiveZeroFreeRightOf (23 / 24)) (c s z a v D ε E beta tau : ℝ)
    (m J : ℕ)
    (_hc : 0 < c) (_hs : 0 ≤ s) (_hz : 0 ≤ z) (_ha : 0 ≤ a)
    (_hv : 0 < v) (_hD : 0 ≤ D) (_hε : 0 < ε) (_htau : 0 ≤ tau)
    (_hell : 0 < ell) (_hml : ell ≤ m)
    (_hgap : beta * Real.log ((ell : ℝ) ^ ell / (m : ℝ) ^ ell) / 2 ≤ -(E + 2))
    (_hDgap : (m : ℝ) * a * Real.log 3 + E + 2 ≤ D),
    let κ := a * Real.log (primeFiberFactorBound v m)
    let s' := s + ε
    let A₀ := D + 2 * (s' + 1)
    let q := 2 * κ + (s' + 1) + 2 * A₀ + 3
    let w := 4 * q + max z q + A₀ + 2
    let x := (s' + w + 2) + 2 * A₀ + 2
    ∀ᶠ L : ℝ in atTop,
    let Q := ⌊L ^ q⌋₊
    let h := L ^ (-w)
    let ξ := L ^ (-x)
    ∀ {G : Type} [Fintype G] [DecidableEq G],
    ∀ (P : G → Finset ℕ) (V : G → ℝ),
    Pairwise (fun g h => Disjoint (P g) (P h)) →
    ∀ hP : ∀ g p, p ∈ P g → p.Prime ∧ Q < p,
    (∀ g, ∑ p ∈ P g, 1 / (p : ℝ) = V g) →
    (∀ g, v ≤ V g) →
    (∀ g p, p ∈ P g → Real.log p ≤ L ^ s) →
    (Fintype.card G : ℝ) ≤ a * Real.log L →
    (∀ g, ∃ a b : ℝ, P g = primeBand a b ∧ Real.exp (L ^ c) ≤ a ∧ 0 ≤ b) →
    ∀ probes : G → Finset (Fin J), (∀ g, (probes g).card = m) →
    ∀ r t : Finset G, ∀ hrt : Disjoint r t,
    beta * Real.log L ≤ (r.card : ℝ) → beta * Real.log L ≤ (t.card : ℝ) →
    ∀ ζ θ : ℝ, |ζ| ≤ L ^ z →
    ∀ F : ∀ g, Finset (P g), (∀ g, (F g).card ≤ J + ell) →
    let kept := fun U : Finset (RepeatedBigFlatIndex G J ell) => primeProductRetainedCells
      (fun i : U => P i.1.1) (fun i => V i.1.1) h ξ
    let C := repeatedBigPrimePatternCut (ell := ell) probes r t
    let K₀ := repeatedBigPrimePatternKernel P V probes r t hrt Q h kept
    let weights := repeatedBigPrimePatternWeight (ell := ell) probes r t
    ∀ (b : ∀ g, P g → ℝ),
    ∀ T Pmin : ℝ, 0 ≤ T → T ≤ L ^ tau → Real.exp (L ^ c) ≤ Pmin →
    (∀ g (p : P g), Pmin ≤ (p.val : ℝ)) →
    (∀ g (p : P g), b g p = 1 - T / (p.val : ℝ)) →
    ∀ (S : Type) [Fintype S] [DecidableEq S] (Ps : S → Finset ℕ) (fullB : ℕ) (k : ℤ)
      (ν : ∀ g, P g → ℝ) (ρ : ℝ),
    (∀ g p, 0 ≤ ν g p) → 0 ≤ ρ → ρ ≤ 1 →
    ∀ [∀ q : PhysicalPrime Ps, NeZero q.2.val],
    let _ : ∀ g (p : P g), NeZero p.val :=
      fun g p => ⟨(hP g p.val p.property).1.pos.ne'⟩
    let W : CleanFullMemoryState P J ell fullB → ℝ := productMemoryWeight (fun g => tiltedPhysicalBirthLaw V g (b g)) (fun g z => ν g z.1)
    ∀ (Vs : S → ℝ), (∀ s, vsmall ≤ Vs s) →
    ∀ (Fs : ∀ s, Finset (Ps s))
      (f : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell fullB) → ℂ),
    (∀ s, ProductMemorySymmetric (fun x => f (s,x))) →
    cleanActiveNorm (physicalSmallBigMeasure Vs W)
      (physicalSmallBigJointAverage (physicalMixedGatedCleanPatternAction F V b C ζ θ ρ k
        (fun i source target aux => weights i * K₀ i source target aux)
        Vs qsmall cleanMixedSourceGate (cleanMixedTargetGate Fs) (physicalSmallBigJointAverage f))) ≤
      A ^ Fintype.card S * L ^ (-E) * cleanActiveNorm (physicalSmallBigMeasure Vs W) f := by
  obtain ⟨A, hA, hbound⟩ := exists_physical_mixed_clean_prime_power_bound
    qsmall vsmall ell hq0 hq1 hvs
  refine ⟨A, hA, ?_⟩
  intro hZ c s z a v D ε E beta tau m J hc hs hz ha hv hD hε htau hell hml hgap hDgap κ s' A₀ q w x
  filter_upwards [hbound hZ c s z a v D ε E beta tau m J hc hs hz ha hv hD hε htau
      hell hml hgap hDgap,
    eventually_repeated_big_baseline_pos (tau := tau) hc,
    eventually_gt_atTop (0 : ℝ)] with L hpower hbaseline hL
  intro Q h ξ G _ dG
  cases Subsingleton.elim dG (Classical.typeDecidableEq G)
  intro P V hdisj hP hmass hV hlog hcard hband probes hp r t hrt hr ht
    ζ θ hζ F hF kept C K₀ weights b T Pmin hT hTmax hPminexp hpmin hb
    S _ dS
  cases Subsingleton.elim dS (Classical.typeDecidableEq S)
  intro Ps fullB k ν ρ hν hρ0 hρ1 _
  let _ : ∀ g (p : P g), NeZero p.val :=
    fun g p => ⟨(hP g p.val p.property).1.pos.ne'⟩
  intro _ W Vs hVs Fs f hf
  have hbpos : ∀ g p, 0 < b g p := by
    intro g p
    rw [hb g p]
    exact (hbaseline T Pmin hT hTmax hPminexp).2 p.val (hpmin g p)
  have hW : ∀ x, 0 ≤ W x := productMemoryWeight_nonneg _ _
    (fun g p => tiltedPhysicalBirthLaw_nonneg V g (b g)
      (hv.trans_le (hV g)).le (fun p => (hbpos g p).le) p) (fun g p => hν g p.1)
  have hVs' : ∀ s, 0 < Vs s := fun s => hvs.trans_le (hVs s)
  let K := fun i source target aux => weights i * K₀ i source target aux
  let row := physicalMixedGatedCleanPatternAction (B := fullB) F V b C ζ θ ρ k K
    Vs qsmall cleanMixedSourceGate (cleanMixedTargetGate Fs)
  have hbase := hpower P V hdisj hP hmass hV hlog hcard hband probes hp r t hrt hr ht
    ζ θ hζ F hF b T Pmin hT hTmax hPminexp hpmin hb
    S Ps fullB k ν ρ hν hρ0 hρ1 Vs hVs
    cleanMixedSourceGate (cleanMixedTargetGate Fs)
    clean_mixed_source_gate_norm_le (clean_mixed_target_gate_norm_le Fs)
    clean_mixed_source_gate_big_permutation (clean_mixed_target_gate_big_permutation Fs)
    (physicalSmallBigAverage f)
    (clean_mixed_target_gate_mul_memory_symmetric Fs _
      (physical_small_big_average_memory_symmetric f hf))
  have heq : physicalSmallBigJointAverage (row (physicalSmallBigJointAverage f)) =
      physicalSmallBigAverage (physicalSmallBigBigAverage
        (row (physicalSmallBigBigAverage (physicalSmallBigAverage f)))) := by
    rw [physical_small_big_joint_average_eq_big_small f]
    rfl
  have hnonneg : 0 ≤ A ^ (2 * Fintype.card S) * (L ^ (-E)) ^ 2 :=
    mul_nonneg (pow_nonneg (zero_le_one.trans hA) _) (sq_nonneg _)
  have he : physicalSmallBigEnergy Vs W
      (physicalSmallBigJointAverage (row (physicalSmallBigJointAverage f))) ≤
      A ^ (2 * Fintype.card S) * (L ^ (-E)) ^ 2 * physicalSmallBigEnergy Vs W f := by
    rw [heq]
    exact (physical_small_big_average_energy_le Vs hVs' W hW _).trans
      (hbase.trans (mul_le_mul_of_nonneg_left
        (physical_small_big_average_energy_le Vs hVs' W hW f) hnonneg))
  have hn := physical_small_big_norm_le_of_energy Vs W
    (A ^ Fintype.card S * L ^ (-E)) 1
    (mul_nonneg (pow_nonneg (zero_le_one.trans hA) _) (Real.rpow_nonneg hL.le _))
    zero_le_one f (physicalSmallBigJointAverage (row (physicalSmallBigJointAverage f)))
    (by simpa only [mul_pow, ← pow_mul, Nat.mul_comm, mul_one] using he)
  simp only [Real.sqrt_one, mul_one, row, K] at hn
  convert hn using 1
  all_goals congr 3

theorem exists_candidate_physical_mixed_full_norm_bound
    {qsmall vsmall scale : ℝ} (hq0 : 0 ≤ qsmall) (hq1 : qsmall < 1)
    (hvs : 0 < vsmall) (hscale : 0 < scale) (ell : ℕ) (C₂ : ℝ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀
    (_hZ : PrimitiveZeroFreeRightOf (23 / 24)) (c s z a v D ε E beta tau : ℝ)
    (m J : ℕ)
    (_hc : 0 < c) (_hs : 0 ≤ s) (_hz : 0 ≤ z) (_ha : 0 ≤ a)
    (_hv : 0 < v) (_hD : 0 ≤ D) (_hε : 0 < ε) (_htau : 0 ≤ tau)
    (_hell : 0 < ell) (_hml : ell ≤ m)
    (_hgap : beta * Real.log ((ell : ℝ) ^ ell / (m : ℝ) ^ ell) / 2 ≤ -(E + 2))
    (_hDgap : (m : ℝ) * a * Real.log 3 + E + 2 ≤ D),
    let κ := a * Real.log (primeFiberFactorBound v m)
    let s' := s + ε
    let A₀ := D + 2 * (s' + 1)
    let q := 2 * κ + (s' + 1) + 2 * A₀ + 3
    let w := 4 * q + max z q + A₀ + 2
    let x := (s' + w + 2) + 2 * A₀ + 2
    ∀ᶠ L : ℝ in atTop,
    let Q := ⌊L ^ q⌋₊
    let h := L ^ (-w)
    let ξ := L ^ (-x)
    letI : DecidableEq (CandidateSmallGroup scale L) := Classical.decEq _
    letI : DecidableEq (CandidateBigGroup scale L) := Classical.decEq _
    letI : ∀ p : PhysicalPrime (candidateSmallPool scale L), NeZero p.2.val :=
      candidateSmallPrimeNeZero scale L
    letI : ∀ g p, NeZero (candidateBigModulus scale L g p) := candidateBigModulusNeZero scale L
    letI : ∀ (g : CandidateBigGroup scale L) (p : CandidateBigLabel scale L g), NeZero p.val :=
      fun g p => candidateBigModulusNeZero scale L g p
    let P := fun g : CandidateBigGroup scale L => candidatePBand (scale * L) g.val
    ∀ V : CandidateBigGroup scale L → ℝ,
    Pairwise (fun g h => Disjoint (P g) (P h)) →
    (∀ g p, p ∈ P g → p.Prime ∧ Q < p) →
    (∀ g, ∑ p ∈ P g, 1 / (p : ℝ) = V g) →
    (∀ g, v ≤ V g) →
    (∀ g p, p ∈ P g → Real.log p ≤ L ^ s) →
    (Fintype.card (CandidateBigGroup scale L) : ℝ) ≤ a * Real.log L →
    (∀ g, ∃ a b : ℝ, P g = primeBand a b ∧ Real.exp (L ^ c) ≤ a ∧ 0 ≤ b) →
    ∀ probes : CandidateBigGroup scale L → Finset (Fin J), (∀ g, (probes g).card = m) →
    ∀ r t : Finset (CandidateBigGroup scale L), ∀ hrt : Disjoint r t,
    beta * Real.log L ≤ (r.card : ℝ) → beta * Real.log L ≤ (t.card : ℝ) →
    ∀ ζ θ : ℝ, |ζ| ≤ L ^ z →
    ∀ initial : ∀ g, Finset (P g), (∀ g, (initial g).card ≤ J + ell) →
    ∀ baseline : ∀ g, P g → ℝ,
    ∀ T Pmin : ℝ, 0 ≤ T → T ≤ L ^ tau → Real.exp (L ^ c) ≤ Pmin →
    (∀ g (p : P g), Pmin ≤ (p.val : ℝ)) →
    (∀ g (p : P g), baseline g p = 1 - T / (p.val : ℝ)) →
    (∀ g p, 1 / 2 ≤ baseline g p ∧ baseline g p ≤ 1) →
    ∀ (B : ℕ) (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L ^ C₂ →
    ∀ Vs : CandidateSmallGroup scale L → ℝ, (∀ g, vsmall ≤ Vs g) →
    ∀ ρ u vmax : ℝ, 0 < ρ → ρ < 1 → 1 < u → (∀ g, V g ≤ vmax) →
    ∀ f : PhysicalSmallBigState (candidateSmallPool scale L) J ell
      (CleanFullMemoryState P J ell B) → ℂ,
    (∀ d, ProductMemorySymmetric (fun y => f (d,y))) →
    let μ := fun g => tiltedPhysicalBirthLaw V g (baseline g)
    let W := productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g))
    cleanActiveNorm (physicalSmallBigMeasure Vs W)
      (physicalSmallBigJointAverage (physicalMixedPrimePatternAction V baseline ρ Vs qsmall
        probes r t hrt Q h ξ k initial
        (fun i => physicalMixedFullResidualPhase (repeatedBigPrimePatternCut probes r t i)
          ζ θ k cleanMixedSourceGate (cleanMixedTargetGate (fun _ => ∅)))
        (physicalSmallBigJointAverage f))) ≤
      A ^ (candidateSmallPIndices scale L).card *
        (L ^ (-E) + 2 * repeatedBigFamilyEnvelope (candidateBigPIndices scale L).card m Q ξ *
          Real.sqrt ((B : ℝ) / (((J + ell).choose ell) ^ (candidateSmallPIndices scale L).card : ℕ)) *
          Real.sqrt (unrestrictedEdgeEnergyBound ρ u v vmax (ell + m) ^ (candidateBigPIndices scale L).card)) *
        cleanActiveNorm (physicalSmallBigMeasure Vs W) f := by
  obtain ⟨Ac, hAc, hclean⟩ := exists_physical_mixed_clean_prime_joint_norm_bound
    qsmall vsmall ell hq0 hq1 hvs
  obtain ⟨Ad, hAd, hdirty⟩ := eventually_candidate_physical_mixed_prime_dirty_norm_le
    hq0 hq1 hvs hscale ell C₂
  refine ⟨max Ac Ad, hAc.trans (le_max_left _ _), ?_⟩
  intro hZ c s z a v D ε E beta tau m J hc hs hz ha hv hD hε htau hell hml hgap hDgap κ s' A₀ q w x
  filter_upwards [hclean hZ c s z a v D ε E beta tau m J hc hs hz ha hv hD hε htau
      hell hml hgap hDgap, hdirty, eventually_gt_atTop (0 : ℝ)] with L hcl hdi hL
  intro Q h ξ
  let _ : DecidableEq (CandidateSmallGroup scale L) := Classical.decEq _
  let _ : DecidableEq (CandidateBigGroup scale L) := Classical.decEq _
  let _ : ∀ p : PhysicalPrime (candidateSmallPool scale L), NeZero p.2.val :=
    candidateSmallPrimeNeZero scale L
  let _ : ∀ g p, NeZero (candidateBigModulus scale L g p) := candidateBigModulusNeZero scale L
  let _ : ∀ (g : CandidateBigGroup scale L) (p : CandidateBigLabel scale L g), NeZero p.val :=
    fun g p => candidateBigModulusNeZero scale L g p
  intro P V hdisj hP hmass hV hlog hcard hband probes hp r t hrt hr ht ζ θ hζ
    initial hinitial baseline T Pmin hT hTmax hPmin hpmin hb hbaseline B k hk hkbound
    Vs hVs ρ u vmax hρ0 hρ1 hu hVhi f hf μ W
  have hμ : ∀ g p, 0 ≤ μ g p := fun g p => tiltedPhysicalBirthLaw_nonneg V g (baseline g)
    (hv.trans_le (hV g)).le (fun p => (by norm_num : (0 : ℝ) ≤ 1/2).trans (hbaseline g p).1) p
  have hW : ∀ y, 0 ≤ W y := productMemoryWeight_nonneg μ _ hμ (fun g z => hμ g z.1)
  have hVs0 : ∀ g, 0 < Vs g := fun g => hvs.trans_le (hVs g)
  have hξ : 0 < ξ := Real.rpow_pos_of_pos hL _
  have hc0 := hcl P V hdisj hP hmass hV hlog hcard hband probes hp r t hrt hr ht
    ζ θ hζ initial hinitial baseline T Pmin hT hTmax hPmin hpmin hb
    (CandidateSmallGroup scale L) (candidateSmallPool scale L) B k μ ρ hμ hρ0.le hρ1.le
    Vs hVs (fun _ => ∅) f hf
  have hd0 := hdi J B m probes r t hrt (fun g => (hp g).le) Q h ξ hξ k hk hkbound
    Vs hVs V baseline ρ u v vmax hρ0 hρ1 hu hv hV hVhi hmass hbaseline initial
    (fun i => physicalMixedFullResidualPhase (repeatedBigPrimePatternCut probes r t i)
      ζ θ k cleanMixedSourceGate (cleanMixedTargetGate (fun _ => ∅)))
    (fun i a y e => physical_mixed_concrete_residual_norm_le _ ζ θ k (fun _ => ∅) a y e) f hf
  let C := repeatedBigPrimePatternCut (ell := ell) probes r t
  let kept := fun U : Finset (RepeatedBigFlatIndex (CandidateBigGroup scale L) J ell) =>
    primeProductRetainedCells (fun j : U => P j.val.1) (fun j => V j.val.1) h ξ
  let K := repeatedBigPrimePatternKernel P V probes r t hrt Q h kept
  let clean := physicalSmallBigJointAverage (physicalMixedGatedCleanPatternAction initial V baseline C
    ζ θ ρ k (fun i a b c => repeatedBigPrimePatternWeight probes r t i * K i a b c)
    Vs qsmall cleanMixedSourceGate (cleanMixedTargetGate (fun _ => ∅)) (physicalSmallBigJointAverage f))
  let dirty := physicalSmallBigJointAverage (physicalMixedPrimePatternAction V baseline ρ Vs qsmall
    probes r t hrt Q h ξ k initial
    (fun i => physicalMixedDirtyPhase (C i) k
      (physicalMixedFullResidualPhase (C i) ζ θ k cleanMixedSourceGate (cleanMixedTargetGate (fun _ => ∅))))
    (physicalSmallBigJointAverage f))
  let δ := (B : ℝ) / (((J + ell).choose ell) ^ (candidateSmallPIndices scale L).card : ℕ)
  let Ce := unrestrictedEdgeEnergyBound ρ u v vmax (ell + m) ^ (candidateBigPIndices scale L).card
  let H := repeatedBigFamilyEnvelope (candidateBigPIndices scale L).card m Q ξ
  have hc' : cleanActiveNorm (physicalSmallBigMeasure Vs W) clean ≤
      Ac ^ (candidateSmallPIndices scale L).card * L ^ (-E) * cleanActiveNorm (physicalSmallBigMeasure Vs W) f := by
    simp only [Fintype.card_coe] at hc0
    convert hc0 using 1
    all_goals rfl
  have hd' : cleanActiveNorm (physicalSmallBigMeasure Vs W) dirty ≤
      H * (2 * Real.sqrt δ * Ad ^ (candidateSmallPIndices scale L).card * Real.sqrt Ce) *
        cleanActiveNorm (physicalSmallBigMeasure Vs W) f := hd0
  have heq := physical_mixed_prime_projected_clean_dirty V baseline ρ Vs qsmall probes r t hrt
    Q h ξ ζ θ k initial cleanMixedSourceGate (cleanMixedTargetGate (fun _ => ∅)) f
  have hsum := physical_small_big_clean_rare_norm_le Vs W hVs0 hW f _ clean dirty heq _ _ hc' hd'
  have hcPow : Ac ^ (candidateSmallPIndices scale L).card ≤ (max Ac Ad) ^ (candidateSmallPIndices scale L).card :=
    pow_le_pow_left₀ (zero_le_one.trans hAc) (le_max_left _ _) _
  have hdPow : Ad ^ (candidateSmallPIndices scale L).card ≤ (max Ac Ad) ^ (candidateSmallPIndices scale L).card :=
    pow_le_pow_left₀ (zero_le_one.trans hAd) (le_max_right _ _) _
  have hH : 0 ≤ H := repeated_big_family_envelope_nonneg _ _ _ _
  have hnorm : 0 ≤ cleanActiveNorm (physicalSmallBigMeasure Vs W) f := Real.sqrt_nonneg _
  refine hsum.trans (mul_le_mul_of_nonneg_right ?_ hnorm)
  calc
    Ac ^ (candidateSmallPIndices scale L).card * L ^ (-E) +
        H * (2 * Real.sqrt δ * Ad ^ (candidateSmallPIndices scale L).card * Real.sqrt Ce) ≤
      (max Ac Ad) ^ (candidateSmallPIndices scale L).card * L ^ (-E) +
        H * (2 * Real.sqrt δ * (max Ac Ad) ^ (candidateSmallPIndices scale L).card * Real.sqrt Ce) :=
      add_le_add (mul_le_mul_of_nonneg_right hcPow (Real.rpow_nonneg hL.le _))
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdPow (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
          (Real.sqrt_nonneg _)) hH)
    _ = _ := by ring

theorem exists_candidate_positive_proxy_gap
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q S : ℝ} {r : ℕ}
    (hc : 0 < c) (hr : 0 < r) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcenter : (11 / 5 : ℝ) * (r : ℝ) * c = 1) (hS : 0 ≤ S) :
    ∃ κ qCut b : ℝ, ∃ h N : ℕ, ∃ M : Fin N → ℝ, ∃ J : ℕ,
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
      ∀ jStar : ℕ, J < jStar → ∀ᶠ L : ℝ in atTop,
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
  obtain ⟨Junbal, hunbal⟩ := exists_candidate_unbalanced_rough_finite_bins_upper
    hZ hc hr hq0 hq1 hcenter hstart hstart (fun i => (hbins i).1.le) hend hgap hS
      (fun i => (hbins i).2.1.le) (fun i => (hbins i).2.2)
  obtain ⟨Jpre, hprebound⟩ := hpre c q b r h hc hr hq0 hq1 hcenter hb hh heven hlevel
  refine ⟨κ, qCut, b, h, N, M, max Jpre (max Junbal Jbal), hκ, hκup, hqCut,
    hqCut0, hqCuthalf, hb, hbq, hh, heven, hlevel, hN, hbins, hmesh, ?_⟩
  intro jStar hj
  have hjpre : Jpre < jStar := lt_of_le_of_lt (le_max_left _ _) hj
  have hjunbal : Junbal < jStar := lt_of_le_of_lt
    ((le_max_left Junbal Jbal).trans (le_max_right Jpre _)) hj
  have hjbal : Jbal < jStar := lt_of_le_of_lt
    ((le_max_right Junbal Jbal).trans (le_max_right Jpre _)) hj
  have hd : 0 < shiftedSieveRatioConstant :=
    lt_of_lt_of_le zero_lt_one shifted_sieve_ratio_constant_bounds.1
  have hε : 0 < shiftedSieveRatioConstant / 24 := by positivity
  filter_upwards [hprebound jStar hjpre _ hε, hunbal jStar hjunbal _ hε,
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

theorem exists_candidate_positive_proxy_gap_parameters
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
      ∀ S : ℝ, 0 ≤ S → ∃ J : ℕ, ∀ jStar : ℕ, J < jStar → ∀ᶠ L : ℝ in atTop,
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
  intro S hS
  obtain ⟨Junbal, hunbal⟩ := exists_candidate_unbalanced_rough_finite_bins_upper
    hZ hc hr hq0 hq1 hcenter hstart hstart (fun i => (hbins i).1.le) hend hgap hS
      (fun i => (hbins i).2.1.le) (fun i => (hbins i).2.2)
  obtain ⟨Jpre, hprebound⟩ := hpre c q b r h hc hr hq0 hq1 hcenter hb hh heven hlevel
  refine ⟨max Jpre (max Junbal Jbal), ?_⟩
  intro jStar hj
  have hjpre : Jpre < jStar := lt_of_le_of_lt (le_max_left _ _) hj
  have hjunbal : Junbal < jStar := lt_of_le_of_lt
    ((le_max_left Junbal Jbal).trans (le_max_right Jpre _)) hj
  have hjbal : Jbal < jStar := lt_of_le_of_lt
    ((le_max_right Junbal Jbal).trans (le_max_right Jpre _)) hj
  have hd : 0 < shiftedSieveRatioConstant :=
    lt_of_lt_of_le zero_lt_one shifted_sieve_ratio_constant_bounds.1
  have hε : 0 < shiftedSieveRatioConstant / 24 := by positivity
  filter_upwards [hprebound jStar hjpre _ hε, hunbal jStar hjunbal _ hε,
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

theorem eventually_rough_test_proxy_long_discrepancy (hZ : PrimitiveZeroFreeRightOf (23 / 24))
    {a γ S T B : ℝ} (ha : 0 < a) (hγ : 0 < γ) (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hprecision : T+B+4 ≤ S) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), (r : ℝ) ≤ L^T →
      ∀ t : ℝ, |t| ≤ L^T → ∀ m n : ℕ,
        Real.exp (a*L) ≤ ((m+1 : ℕ) : ℝ) → (n : ℝ) ≤ Real.exp (2*L) →
        ‖∑ i ∈ Ioc m n,
          ((roughTestIndicator γ L i-roughTestLogarithmicProxy γ L S i : ℝ) : ℂ)*
            harmonicMellinWeight t i*χ (i : ZMod r)‖ ≤ L^(-B) := by
  filter_upwards [eventually_rough_test_proxy_character_discrepancy hZ (half_pos ha) hγ
    (by norm_num : (0 : ℝ) < 2) hS hT (Bsave := B+2) (by linarith),
    eventually_exp_half_le_half_exp ha, eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (2/Real.log 2+2)] with L hlocal hhalf hL hLbig
  intro r hr χ hrT t ht m n hm hn
  apply norm_Ioc_sum_le_rpow_of_dyadic (Real.exp_pos (a*L)) hL hLbig _ m n hm hn
  intro Y hY hYU lo hi hlohi hYlo hhi
  exact hlocal Y (hhalf.trans hY) hYU r χ hrT t ht lo hi hlohi hYlo hhi

theorem eventually_prime_proxy_long_discrepancy (hZ : PrimitiveZeroFreeRightOf (23 / 24))
    {a S T B : ℝ} (ha : 0 < a) (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hprecision : T+B+4 ≤ S) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), (r : ℝ) ≤ L^T →
      ∀ t : ℝ, |t| ≤ L^T → ∀ m n : ℕ,
        Real.exp (a*L) ≤ ((m+1 : ℕ) : ℝ) → (n : ℝ) ≤ Real.exp (2*L) →
        ‖∑ i ∈ Ioc m n,
          (((if i.Prime then 1 else 0 : ℝ)-primeLogarithmicProxy L S i : ℝ) : ℂ)*
            harmonicMellinWeight t i*χ (i : ZMod r)‖ ≤ L^(-B) := by
  filter_upwards [eventually_prime_proxy_character_discrepancy hZ (half_pos ha)
    hS hT (Bsave := B+2) (by linarith),
    eventually_exp_half_le_half_exp ha, eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (2/Real.log 2+2)] with L hlocal hhalf hL hLbig
  intro r hr χ hrT t ht m n hm hn
  apply norm_Ioc_sum_le_rpow_of_dyadic (Real.exp_pos (a*L)) hL hLbig _ m n hm hn
  intro Y hY _ lo hi hlohi hYlo hhi
  exact hlocal Y (hhalf.trans hY) r χ hrT t ht lo hi hlohi hYlo hhi

theorem eventually_ambient_rough_interval_typeII_discrepancy_uniform
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {γ vMax S T B : ℝ}
    (hγ : 0 < γ) (hv : vMax < 1) (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hprecision : T+B+4 ≤ S) :
    ∀ᶠ L : ℝ in atTop, ∀ a v : ℝ, v ≤ vMax →
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), (r : ℝ) ≤ L^T →
      ∀ t : ℝ, |t| ≤ L^T → ∀ m n : ℕ,
        ‖∑ i ∈ Ioc m n, (ambientRoughIntervalTypeIIAlpha γ L S a v i : ℂ)*
          harmonicMellinWeight t i*χ (i : ZMod r)‖ ≤ L^(-B) := by
  filter_upwards [eventually_rough_test_proxy_long_discrepancy hZ
    (by linarith : 0 < 1-vMax) hγ hS hT hprecision,
    eventually_ge_atTop (Real.log 33), eventually_ge_atTop (0 : ℝ)] with L hlong hL hL0
  intro a v hvMax r hr χ hrT t ht m n
  have hlower : Real.exp ((1-vMax)*L) ≤ Real.exp ((1-v)*L) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (by linarith) hL0
  have h33 : (33 : ℝ) ≤ Real.exp L := by
    calc
      _ = Real.exp (Real.log 33) := (Real.exp_log (by norm_num)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hL
  have hupper : 33*Real.exp L ≤ Real.exp (2*L) := by
    calc
      _ ≤ Real.exp L*Real.exp L := mul_le_mul_of_nonneg_right h33 (by positivity)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  simp only [ambientRoughIntervalTypeIIAlpha, ambient_rough_cofactor_range_eq_Icc,
    mul_assoc]
  apply norm_typeIIRestrict_Icc_sum_le _ _ _ _ m n (Nat.le_max_left _ _)
    (A := Real.exp ((1-vMax)*L)) (U := Real.exp (2*L))
  · exact hlower.trans ((Nat.le_ceil _).trans (Nat.cast_le.mpr (Nat.le_max_right _ _)))
  · exact (Nat.cast_le.mpr (min_le_left _ _)).trans
      ((Nat.floor_le (by positivity)).trans hupper)
  · intro lo hi hlo hhi
    simpa only [mul_assoc] using hlong r χ hrT t ht lo hi hlo hhi

theorem eventually_ambient_rough_interval_typeII_discrepancy
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {γ v S T B : ℝ}
    (hγ : 0 < γ) (hv : v < 1) (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hprecision : T+B+4 ≤ S) :
    ∀ᶠ L : ℝ in atTop, ∀ a : ℝ,
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), (r : ℝ) ≤ L^T →
      ∀ t : ℝ, |t| ≤ L^T → ∀ m n : ℕ,
        ‖∑ i ∈ Ioc m n, (ambientRoughIntervalTypeIIAlpha γ L S a v i : ℂ)*
          harmonicMellinWeight t i*χ (i : ZMod r)‖ ≤ L^(-B) := by
  filter_upwards [eventually_ambient_rough_interval_typeII_discrepancy_uniform
    hZ hγ hv hS hT hprecision] with L hL
  intro a
  exact hL a v le_rfl

theorem eventually_ambient_prime_typeII_discrepancy
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {S T B : ℝ}
    (hS : 0 ≤ S) (hT : 0 ≤ T) (hprecision : T+B+4 ≤ S) :
    ∀ᶠ L : ℝ in atTop, ∀ κ : ℝ, 0 ≤ κ → κ ≤ 1/50 →
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), (r : ℝ) ≤ L^T →
      ∀ t : ℝ, |t| ≤ L^T → ∀ m n : ℕ,
        ‖∑ i ∈ Ioc m n, (ambientPrimeTypeIIAlpha κ L S i : ℂ)*
          harmonicMellinWeight t i*χ (i : ZMod r)‖ ≤ L^(-B) := by
  filter_upwards [eventually_prime_proxy_long_discrepancy hZ
    (by norm_num : (0 : ℝ) < 2/5) hS hT hprecision,
    eventually_ge_atTop (0 : ℝ)] with L hlong hL
  intro κ hκ hκsmall r hr χ hrT t ht m n
  have hlower : Real.exp ((2/5 : ℝ)*L) ≤
      Real.exp (((1/2 : ℝ)-2*κ)*L) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (by linarith) hL
  have hupper : Real.exp (((1/2 : ℝ)+2*κ)*L) ≤ Real.exp (2*L) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (by linarith) hL
  simp only [ambientPrimeTypeIIAlpha, ambient_balanced_typeII_range_eq_Icc, mul_assoc]
  apply norm_typeIIRestrict_Icc_sum_le _ _ _ _ m n (Nat.le_max_left _ _)
    (A := Real.exp ((2/5 : ℝ)*L)) (U := Real.exp (2*L))
  · exact hlower.trans ((Nat.le_ceil _).trans (Nat.cast_le.mpr (Nat.le_max_right _ _)))
  · exact (Nat.floor_le (by positivity)).trans hupper
  · intro lo hi hlo hhi
    simpa only [mul_assoc] using hlong r χ hrT t ht lo hi hlo hhi

theorem exists_ambient_typeII_character_discrepancy_precision
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {γ vMax : ℝ}
    (hγ : 0 < γ) (hv : vMax < 1) (B : ℝ) (hB : 0 ≤ B) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ᶠ L : ℝ in atTop,
      (∀ a v : ℝ, v ≤ vMax →
        ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), (r : ℝ) ≤ L^B →
        ∀ t : ℝ, |t| ≤ L^B → ∀ m n : ℕ,
          ‖∑ i ∈ Ioc m n, (ambientRoughIntervalTypeIIAlpha γ L S a v i : ℂ)*
            harmonicMellinWeight t i*χ (i : ZMod r)‖ ≤ L^(-B)) ∧
      (∀ κ : ℝ, 0 ≤ κ → κ ≤ 1/50 →
        ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), (r : ℝ) ≤ L^B →
        ∀ t : ℝ, |t| ≤ L^B → ∀ m n : ℕ,
          ‖∑ i ∈ Ioc m n, (ambientPrimeTypeIIAlpha κ L S i : ℂ)*
            harmonicMellinWeight t i*χ (i : ZMod r)‖ ≤ L^(-B)) := by
  have hS : 0 ≤ 2*B+4 := by linarith
  have hprecision : B+B+4 ≤ 2*B+4 := by linarith
  refine ⟨2*B+4, hS, ?_⟩
  filter_upwards [eventually_ambient_rough_interval_typeII_discrepancy_uniform
    hZ hγ hv hS hB hprecision,
    eventually_ambient_prime_typeII_discrepancy hZ hS hB hprecision] with L hrough hprime
  exact ⟨hrough, hprime⟩

theorem candidate_shifted_prime_fraction_of_ambient_replacement
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) (hR : CandidateAmbientReplacement)
    {c q : ℝ} {r : ℕ} (hc : 0<c) (hr : 0<r) (hq0 : 0≤q) (hq1 : q<1)
    (hcenter : (11/5:ℝ)*(r:ℝ)*c=1) :
    ∃ J : ℕ, ∀ jStar : ℕ, J<jStar → ∀ᶠ L : ℝ in atTop,
      (shiftedSieveRatioConstant/4)*candidateCoefficientWindowMass c L q r jStar/L ≤
        ∑ u ∈ (arithmeticProductWindow 1 (Real.exp L)).filter (fun u => (2*u+1).Prime),
          candidateCoefficient c L q r jStar u := by
  classical
  obtain ⟨κ,qCut,b,h,N,M,hκ,hκmax,hqCut,hqCut0,hqCuthalf,hb,hbq,hh,heven,hlevel,hN,hbins,hmesh,hgap⟩ :=
    exists_candidate_positive_proxy_gap_parameters hZ hc hr hq0 hq1 hcenter
  subst qCut
  obtain ⟨S,hS,Jerr,herr⟩ := hR c q r hc hr hq0 hq1 hcenter κ b N hκ hκmax hb hbq hN
  obtain ⟨Jgap,hgapS⟩ := hgap S hS
  refine ⟨max Jerr Jgap,?_⟩
  intro jStar hj
  have hjerr := lt_of_le_of_lt (le_max_left Jerr Jgap) hj
  have hjgap := lt_of_le_of_lt (le_max_right Jerr Jgap) hj
  have hratio : 0<shiftedSieveRatioConstant :=
    lt_of_lt_of_le zero_lt_one shifted_sieve_ratio_constant_bounds.1
  filter_upwards [herr jStar hjerr,hgapS jStar hjgap,
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

theorem eventually_ambient_rough_shifted_discrepancy
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {γ vMax S B0 Cmod B : ℝ}
    (hγ : 0 < γ) (hv : vMax < 1) (hS : 0 ≤ S)
    (hB0 : 0 ≤ B0) (_hCmod : 0 ≤ Cmod)
    (hprecision : max B0 Cmod + B + 6 ≤ S) (σ : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ a v : ℝ, v ≤ vMax →
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), (r : ℝ) ≤ L ^ Cmod →
      ∀ u : ℝ, |u| ≤ L ^ B0 → ∀ m n : ℕ,
        ‖∑ i ∈ Ioc m n, (ambientRoughIntervalTypeIIAlpha γ L S a v i : ℂ) *
          harmonicMellinWeight (u + σ) i * χ (i : ZMod r)‖ ≤ L ^ (-B) := by
  have hx : 0 ≤ max B0 Cmod := hB0.trans (le_max_left _ _)
  have hT : 0 ≤ max B0 Cmod + 2 := by linarith
  filter_upwards [eventually_ambient_rough_interval_typeII_discrepancy_uniform
    hZ hγ hv hS hT (by linarith : (max B0 Cmod + 2) + B + 4 ≤ S),
    eventually_ge_atTop (2 : ℝ), eventually_ge_atTop |σ|] with L hdis hL hσ
  intro a v hv' r hr χ hrange u hu m n
  have hL1 : 1 ≤ L := by linarith
  apply hdis a v hv' r χ _ (u + σ) _ m n
  · exact hrange.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [le_max_right B0 Cmod]))
  · apply abs_add_fixed_le_rpow hL hx _ hσ
    exact hu.trans (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _))

theorem eventually_ambient_prime_shifted_discrepancy
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {S B0 Cmod B : ℝ}
    (hS : 0 ≤ S) (hB0 : 0 ≤ B0) (_hCmod : 0 ≤ Cmod)
    (hprecision : max B0 Cmod + B + 6 ≤ S) (σ : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ κ : ℝ, 0 ≤ κ → κ ≤ 1 / 50 →
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), (r : ℝ) ≤ L ^ Cmod →
      ∀ u : ℝ, |u| ≤ L ^ B0 → ∀ m n : ℕ,
        ‖∑ i ∈ Ioc m n, (ambientPrimeTypeIIAlpha κ L S i : ℂ) *
          harmonicMellinWeight (u + σ) i * χ (i : ZMod r)‖ ≤ L ^ (-B) := by
  have hx : 0 ≤ max B0 Cmod := hB0.trans (le_max_left _ _)
  have hT : 0 ≤ max B0 Cmod + 2 := by linarith
  filter_upwards [eventually_ambient_prime_typeII_discrepancy hZ hS hT
    (by linarith : (max B0 Cmod + 2) + B + 4 ≤ S),
    eventually_ge_atTop (2 : ℝ), eventually_ge_atTop |σ|] with L hdis hL hσ
  intro κ hκ hκ' r hr χ hrange u hu m n
  have hL1 : 1 ≤ L := by linarith
  apply hdis κ hκ hκ' r χ _ (u + σ) _ m n
  · exact hrange.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [le_max_right B0 Cmod]))
  · apply abs_add_fixed_le_rpow hL hx _ hσ
    exact hu.trans (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _))

theorem eventually_ambient_rough_uniform_shift_discrepancy
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {γ vMax S B0 Cmod Sfreq B : ℝ}
    (hγ : 0 < γ) (hv : vMax < 1) (hS : 0 ≤ S) (hB0 : 0 ≤ B0)
    (hprecision : max (max B0 Sfreq) Cmod + B + 5 ≤ S) :
    ∀ᶠ L : ℝ in atTop, ∀ a v : ℝ, v ≤ vMax →
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), (r : ℝ) ≤ L ^ Cmod →
      ∀ u σ : ℝ, |u| ≤ L ^ B0 → |σ| ≤ L ^ Sfreq → ∀ m n : ℕ,
        ‖∑ i ∈ Ioc m n, (ambientRoughIntervalTypeIIAlpha γ L S a v i : ℂ) *
          harmonicMellinWeight (u + σ) i * χ (i : ZMod r)‖ ≤ L ^ (-B) := by
  have hx : 0 ≤ max (max B0 Sfreq) Cmod :=
    hB0.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hT : 0 ≤ max (max B0 Sfreq) Cmod + 1 := by linarith
  filter_upwards [eventually_ambient_rough_interval_typeII_discrepancy_uniform
    hZ hγ hv hS hT (by linarith : (max (max B0 Sfreq) Cmod + 1) + B + 4 ≤ S),
    eventually_ge_atTop (2 : ℝ)] with L hdis hL
  intro a v hv' r hr χ hrange u σ hu hσ m n
  have hL1 : 1 ≤ L := by linarith
  apply hdis a v hv' r χ _ (u + σ) _ m n
  · exact hrange.trans (Real.rpow_le_rpow_of_exponent_le hL1
      (by linarith [le_max_right (max B0 Sfreq) Cmod]))
  · exact (abs_add_le_rpow_max_add_one hL hu hσ).trans
      (Real.rpow_le_rpow_of_exponent_le hL1
        (by linarith [le_max_left (max B0 Sfreq) Cmod]))

theorem eventually_ambient_prime_uniform_shift_discrepancy
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {S B0 Cmod Sfreq B : ℝ}
    (hS : 0 ≤ S) (hB0 : 0 ≤ B0)
    (hprecision : max (max B0 Sfreq) Cmod + B + 5 ≤ S) :
    ∀ᶠ L : ℝ in atTop, ∀ κ : ℝ, 0 ≤ κ → κ ≤ 1 / 50 →
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), (r : ℝ) ≤ L ^ Cmod →
      ∀ u σ : ℝ, |u| ≤ L ^ B0 → |σ| ≤ L ^ Sfreq → ∀ m n : ℕ,
        ‖∑ i ∈ Ioc m n, (ambientPrimeTypeIIAlpha κ L S i : ℂ) *
          harmonicMellinWeight (u + σ) i * χ (i : ZMod r)‖ ≤ L ^ (-B) := by
  have hx : 0 ≤ max (max B0 Sfreq) Cmod :=
    hB0.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hT : 0 ≤ max (max B0 Sfreq) Cmod + 1 := by linarith
  filter_upwards [eventually_ambient_prime_typeII_discrepancy hZ hS hT
    (by linarith : (max (max B0 Sfreq) Cmod + 1) + B + 4 ≤ S),
    eventually_ge_atTop (2 : ℝ)] with L hdis hL
  intro κ hκ hκ' r hr χ hrange u σ hu hσ m n
  have hL1 : 1 ≤ L := by linarith
  apply hdis κ hκ hκ' r χ _ (u + σ) _ m n
  · exact hrange.trans (Real.rpow_le_rpow_of_exponent_le hL1
      (by linarith [le_max_right (max B0 Sfreq) Cmod]))
  · exact (abs_add_le_rpow_max_add_one hL hu hσ).trans
      (Real.rpow_le_rpow_of_exponent_le hL1
        (by linarith [le_max_left (max B0 Sfreq) Cmod]))

theorem candidate_shifted_prime_mass_supply_of_ambient_replacement
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) (hR : CandidateAmbientReplacement) :
    CandidateShiftedPrimeMassSupply := by
  apply candidate_shifted_prime_mass_supply_of_positive_fraction
  intro c q r hc hr hq0 hq1 hcenter
  obtain ⟨J,hJ⟩ := candidate_shifted_prime_fraction_of_ambient_replacement
    hZ hR hc hr hq0 hq1 hcenter
  refine ⟨J,?_⟩
  intro jStar hj
  refine ⟨shiftedSieveRatioConstant/4,?_,hJ jStar hj⟩
  have hratio : 0<shiftedSieveRatioConstant :=
    lt_of_lt_of_le zero_lt_one shifted_sieve_ratio_constant_bounds.1
  positivity

theorem target_of_candidate_ambient_replacement
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) (hR : CandidateAmbientReplacement) :
    fcTypeOfName% "Erdos1057.erdos_1057" :=
  target_of_candidate_prime_mass_and_zero_free
    (candidate_shifted_prime_mass_supply_of_ambient_replacement hZ hR) hZ

theorem eventually_ambient_rough_mellin_low_factor
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {γ vMax S B0 Cmod Sfreq B : ℝ}
    (hγ : 0 < γ) (hv : vMax < 1) (hS : 0 ≤ S) (hB0 : 0 ≤ B0)
    (hprecision : max (max B0 Sfreq) Cmod+B+5 ≤ S) :
    ∀ᶠ L : ℝ in atTop, ∀ a v : ℝ, v ≤ vMax →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), (q : ℝ) ≤ L^Cmod →
      ∀ ν : ℝ, |ν| ≤ L^Sfreq →
        (∀ n : ℕ, 0 < n → ‖ambientRoughMellinCoefficient γ L S a v ν χ n‖ ≤ 1) ∧
        ∀ u : ℝ, |u| ≤ L^B0 → ∀ lo hi : ℕ,
          ‖∑ n ∈ Ioc lo hi, ambientRoughMellinCoefficient γ L S a v ν χ n*
            harmonicMellinWeight u n‖ ≤ L^(-B) := by
  filter_upwards [eventually_ambient_rough_uniform_shift_discrepancy hZ hγ hv hS hB0 hprecision,
    eventually_rough_typeII_restriction_properties hγ] with L hlow hbound
  intro a v hv' q hqInst χ hq ν hν
  constructor
  · intro n hn
    have halpha : ‖(ambientRoughIntervalTypeIIAlpha γ L S a v n : ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_real,Real.norm_eq_abs,ambientRoughIntervalTypeIIAlpha] using
        (hbound S (ambientRoughCofactorRange L a v) n).1
    have hphase : ‖(n : ℂ)^((ν : ℂ)*Complex.I)‖ = 1 := by
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) by simp,
        Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hn)]
      simp
    unfold ambientRoughMellinCoefficient
    rw [norm_mul,norm_mul,hphase,mul_one]
    exact (mul_le_mul halpha (χ.norm_le_one _) (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)
  · intro u hu lo hi
    rw [ambient_rough_mellin_polynomial_eq]
    exact hlow a v hv' q χ hq u ν hu hν lo hi

theorem eventually_ambient_prime_mellin_low_factor
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {S B0 Cmod Sfreq B : ℝ}
    (hS : 0 ≤ S) (hB0 : 0 ≤ B0)
    (hprecision : max (max B0 Sfreq) Cmod+B+5 ≤ S) :
    ∀ᶠ L : ℝ in atTop, ∀ κ : ℝ, 0 ≤ κ → κ ≤ 1/50 →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), (q : ℝ) ≤ L^Cmod →
      ∀ ν : ℝ, |ν| ≤ L^Sfreq →
        (∀ n : ℕ, 0 < n → ‖ambientPrimeMellinCoefficient κ L S ν χ n‖ ≤ 1) ∧
        ∀ u : ℝ, |u| ≤ L^B0 → ∀ lo hi : ℕ,
          ‖∑ n ∈ Ioc lo hi, ambientPrimeMellinCoefficient κ L S ν χ n*
            harmonicMellinWeight u n‖ ≤ L^(-B) := by
  filter_upwards [eventually_ambient_prime_uniform_shift_discrepancy hZ hS hB0 hprecision,
    eventually_balanced_typeII_coefficient_properties S hS] with L hlow hbound
  intro κ hκ hκmax q hqInst χ hq ν hν
  constructor
  · intro n hn
    have halpha : ‖(ambientPrimeTypeIIAlpha κ L S n : ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_real,Real.norm_eq_abs] using
        (hbound κ hκ hκmax n).1
    have hphase : ‖(n : ℂ)^((ν : ℂ)*Complex.I)‖ = 1 := by
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) by simp,
        Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hn)]
      simp
    unfold ambientPrimeMellinCoefficient
    rw [norm_mul,norm_mul,hphase,mul_one]
    exact (mul_le_mul halpha (χ.norm_le_one _) (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)
  · intro u hu lo hi
    rw [ambient_prime_mellin_polynomial_eq]
    exact hlow κ hκ hκmax q χ hq u ν hu hν lo hi

theorem candidate_shifted_prime_fraction_of_fixed_slot_ambient_replacement
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) (hR : CandidateFixedSlotAmbientReplacement)
    {c q : ℝ} {r : ℕ} (hc : 0<c) (hr : 0<r) (hq0 : 0≤q) (hq1 : q<1)
    (hcenter : (11/5:ℝ)*(r:ℝ)*c=1) :
    ∃ J : ℕ, ∀ jStar : ℕ, J<jStar → ∀ᶠ L : ℝ in atTop,
      (shiftedSieveRatioConstant/4)*candidateCoefficientWindowMass c L q r jStar/L ≤
        ∑ u ∈ (arithmeticProductWindow 1 (Real.exp L)).filter (fun u => (2*u+1).Prime),
          candidateCoefficient c L q r jStar u :=
  candidate_shifted_prime_fraction_of_fixed_slot_error_bound hZ hc hr hq0 hq1 hcenter
    (hR c q r hc hr hq0 hq1 hcenter)

theorem exists_ambient_rough_four_factor_integral_decay
    (hZ : PrimitiveZeroFreeRightOf (23 / 24))
    {a beta c d Bcoeff A As H Et aLong γrough vMax : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hbeta : beta < 1) (hc : 0 ≤ c) (hd : 0 < d)
    (hBcoeff : 1 ≤ Bcoeff) (hAs0 : 0 ≤ As) (haLong : 0 < aLong)
    (hγ : 0 < γrough) (hv : vMax < 1)
    (hAs : A+2*Et+21 ≤ 2*As) (hH : A+2*Et+23 ≤ 2*H)
    (Tmod Sshift Cmod Sfreq : ℝ) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ Bsave : ℝ, A+B0+2*Et+7 ≤ 2*Bsave →
      ∀ S : ℝ, 0 ≤ S → max (max B0 Sfreq) Cmod+Bsave+5 ≤ S →
      ∀ᶠ L : ℝ in atTop, ∀ (s : Finset ℕ), (∀ p ∈ s, Nat.Prime p) →
      ∀ (coeff : s → ℂ) (Y P R : ℝ),
      1 ≤ Y → d*L ≤ Real.log Y → Real.log Y ≤ c*L →
      Real.exp (L^a)/2 ≤ P → P ≤ Real.exp (L^beta) →
      0 ≤ R → R ≤ Y → R ≤ Real.exp L →
      (∀ p ∈ s, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*P) →
      (∀ p : s, ‖coeff p‖ ≤ Bcoeff) →
      ∀ (lo hi : ℕ) (F : Finset ℕ) (γT : ℕ → ℂ) (UM UT BT : ℝ),
      0 < UM → 1 ≤ UT → 0 ≤ BT → BT ≤ L^Et →
      (∀ n ∈ F, ‖γT n‖ ≤ BT) →
      (∀ n ∈ Ioc lo hi, UM ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UM) →
      (∀ n ∈ F, UT ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UT) →
      ∀ (aM v ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      v ≤ vMax → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (UQ Alo Blo σ : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      Real.exp (aLong*L) ≤ UQ → UQ ≤ Alo → Alo ≤ Blo → Blo ≤ 2*UQ →
      (q : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      R ≤ UQ*UM*UT/2 → Y^(3/5 : ℝ) ≤ UM*UT/2 → Real.log (8*(UQ*UM*UT)) ≤ c*L →
      (∫ u in Set.Icc (-R) R,
        ‖primeReciprocalPolynomial s coeff u *
          (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)), harmonicMellinWeight (u+σ) n*χ (n : ZMod q))*
          (∑ n ∈ Ioc lo hi, ambientRoughMellinCoefficient γrough L S aM v ν χM n*harmonicMellinWeight u n)*
          (∑ n ∈ F, γT n*harmonicMellinWeight u n)‖^2) ≤ L^(-A) := by
  obtain ⟨B0,hB0,hmain⟩ := exists_literal_four_factor_integral_decay
    (E := Et) ha ha1 hbeta hc hd hBcoeff hAs0 haLong hAs hH Tmod Sshift
  refine ⟨B0,hB0,?_⟩
  intro Bsave hsave S hS hprecision
  filter_upwards [hmain Bsave hsave,
    eventually_ambient_rough_mellin_low_factor hZ hγ hv hS hB0.le hprecision]
    with L hdecay hlow
  intro s hs coeff Y P R hY hYlo hYhi hPlo hPhi hR hRY hRX hsp hcoeff
    lo hi F γT UM UT BT hUM hUT hBT hBTpow hγT hMband hFband
    aM v ν qM hqMInst χM hvM hqM hν UQ Alo Blo σ q hqInst χ hUQ hQA hAB hBQ hq hσ
    hmeanScale hresScale hlog
  have hM := hlow aM v hvM qM χM hqM ν hν
  apply hdecay s hs coeff Y P R hY hYlo hYhi hPlo hPhi hR hRY hRX hsp hcoeff
    (Ioc lo hi) F (ambientRoughMellinCoefficient γrough L S aM v ν χM) γT
    UM UT 1 BT hUM hUT zero_le_one hBT (by simpa only [one_mul] using hBTpow) hBTpow
    (fun n hn => hM.1 n ((Nat.zero_le lo).trans_lt (mem_Ioc.mp hn).1))
    hγT hMband hFband UQ Alo Blo σ q χ hUQ hQA hAB hBQ hq hσ hmeanScale hresScale hlog
  intro u _ hu
  exact hM.2 u hu lo hi

theorem exists_ambient_prime_four_factor_integral_decay
    (hZ : PrimitiveZeroFreeRightOf (23 / 24))
    {a beta c d Bcoeff A As H Et aLong : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hbeta : beta < 1) (hc : 0 ≤ c) (hd : 0 < d)
    (hBcoeff : 1 ≤ Bcoeff) (hAs0 : 0 ≤ As) (haLong : 0 < aLong)
    (hAs : A+2*Et+21 ≤ 2*As) (hH : A+2*Et+23 ≤ 2*H)
    (Tmod Sshift Cmod Sfreq : ℝ) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ Bsave : ℝ, A+B0+2*Et+7 ≤ 2*Bsave →
      ∀ S : ℝ, 0 ≤ S → max (max B0 Sfreq) Cmod+Bsave+5 ≤ S →
      ∀ᶠ L : ℝ in atTop, ∀ (s : Finset ℕ), (∀ p ∈ s, Nat.Prime p) →
      ∀ (coeff : s → ℂ) (Y P R : ℝ),
      1 ≤ Y → d*L ≤ Real.log Y → Real.log Y ≤ c*L →
      Real.exp (L^a)/2 ≤ P → P ≤ Real.exp (L^beta) →
      0 ≤ R → R ≤ Y → R ≤ Real.exp L →
      (∀ p ∈ s, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*P) →
      (∀ p : s, ‖coeff p‖ ≤ Bcoeff) →
      ∀ (lo hi : ℕ) (F : Finset ℕ) (γT : ℕ → ℂ) (UM UT BT : ℝ),
      0 < UM → 1 ≤ UT → 0 ≤ BT → BT ≤ L^Et →
      (∀ n ∈ F, ‖γT n‖ ≤ BT) →
      (∀ n ∈ Ioc lo hi, UM ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UM) →
      (∀ n ∈ F, UT ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UT) →
      ∀ (κM ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      0 ≤ κM → κM ≤ 1/50 → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (UQ Alo Blo σ : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      Real.exp (aLong*L) ≤ UQ → UQ ≤ Alo → Alo ≤ Blo → Blo ≤ 2*UQ →
      (q : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      R ≤ UQ*UM*UT/2 → Y^(3/5 : ℝ) ≤ UM*UT/2 → Real.log (8*(UQ*UM*UT)) ≤ c*L →
      (∫ u in Set.Icc (-R) R,
        ‖primeReciprocalPolynomial s coeff u *
          (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)), harmonicMellinWeight (u+σ) n*χ (n : ZMod q))*
          (∑ n ∈ Ioc lo hi, ambientPrimeMellinCoefficient κM L S ν χM n*harmonicMellinWeight u n)*
          (∑ n ∈ F, γT n*harmonicMellinWeight u n)‖^2) ≤ L^(-A) := by
  obtain ⟨B0,hB0,hmain⟩ := exists_literal_four_factor_integral_decay
    (E := Et) ha ha1 hbeta hc hd hBcoeff hAs0 haLong hAs hH Tmod Sshift
  refine ⟨B0,hB0,?_⟩
  intro Bsave hsave S hS hprecision
  filter_upwards [hmain Bsave hsave,
    eventually_ambient_prime_mellin_low_factor hZ hS hB0.le hprecision]
    with L hdecay hlow
  intro s hs coeff Y P R hY hYlo hYhi hPlo hPhi hR hRY hRX hsp hcoeff
    lo hi F γT UM UT BT hUM hUT hBT hBTpow hγT hMband hFband
    κM ν qM hqMInst χM hκ hκmax hqM hν UQ Alo Blo σ q hqInst χ hUQ hQA hAB hBQ hq hσ
    hmeanScale hresScale hlog
  have hM := hlow κM hκ hκmax qM χM hqM ν hν
  apply hdecay s hs coeff Y P R hY hYlo hYhi hPlo hPhi hR hRY hRX hsp hcoeff
    (Ioc lo hi) F (ambientPrimeMellinCoefficient κM L S ν χM) γT
    UM UT 1 BT hUM hUT zero_le_one hBT (by simpa only [one_mul] using hBTpow) hBTpow
    (fun n hn => hM.1 n ((Nat.zero_le lo).trans_lt (mem_Ioc.mp hn).1))
    hγT hMband hFband UQ Alo Blo σ q χ hUQ hQA hAB hBQ hq hσ hmeanScale hresScale hlog
  intro u _ hu
  exact hM.2 u hu lo hi

theorem candidate_shifted_prime_mass_supply_of_fixed_slot_ambient_replacement
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) (hR : CandidateFixedSlotAmbientReplacement) :
    CandidateShiftedPrimeMassSupply := by
  apply candidate_shifted_prime_mass_supply_of_positive_fraction
  intro c q r hc hr hq0 hq1 hcenter
  obtain ⟨J,hJ⟩ := candidate_shifted_prime_fraction_of_fixed_slot_ambient_replacement
    hZ hR hc hr hq0 hq1 hcenter
  refine ⟨J,?_⟩
  intro jStar hj
  refine ⟨shiftedSieveRatioConstant/4,?_,hJ jStar hj⟩
  have hratio : 0<shiftedSieveRatioConstant :=
    lt_of_lt_of_le zero_lt_one shifted_sieve_ratio_constant_bounds.1
  positivity

theorem target_of_candidate_fixed_slot_ambient_replacement
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) (hR : CandidateFixedSlotAmbientReplacement) :
    fcTypeOfName% "Erdos1057.erdos_1057" :=
  target_of_candidate_prime_mass_and_zero_free
    (candidate_shifted_prime_mass_supply_of_fixed_slot_ambient_replacement hZ hR) hZ

theorem exists_ambient_prime_four_factor_integral_decay_log_radius
    (hZ : PrimitiveZeroFreeRightOf (23 / 24))
    {a beta c d Bcoeff A As H Et aLong : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hbeta : beta < 1) (hc : 0 ≤ c) (hd : 0 < d)
    (hBcoeff : 1 ≤ Bcoeff) (hAs0 : 0 ≤ As) (haLong : 0 < aLong)
    (hAs : A+2*Et+21 ≤ 2*As) (hH : A+2*Et+23 ≤ 2*H)
    (Tmod Sshift Cmod Sfreq : ℝ) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ Bsave : ℝ, A+B0+2*Et+7 ≤ 2*Bsave →
      ∀ S : ℝ, 0 ≤ S → max (max B0 Sfreq) Cmod+Bsave+5 ≤ S →
      ∀ᶠ L : ℝ in atTop, ∀ (s : Finset ℕ), (∀ p ∈ s, Nat.Prime p) →
      ∀ (coeff : s → ℂ) (Y P R : ℝ),
      1 ≤ Y → d*L ≤ Real.log Y → Real.log Y ≤ c*L →
      Real.exp (L^a)/2 ≤ P → P ≤ Real.exp (L^beta) →
      0 ≤ R → R ≤ Y →
      (∀ p ∈ s, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*P) →
      (∀ p : s, ‖coeff p‖ ≤ Bcoeff) →
      ∀ (lo hi : ℕ) (F : Finset ℕ) (γT : ℕ → ℂ) (UM UT BT : ℝ),
      0 < UM → 1 ≤ UT → 0 ≤ BT → BT ≤ L^Et →
      (∀ n ∈ F, ‖γT n‖ ≤ BT) →
      (∀ n ∈ Ioc lo hi, UM ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UM) →
      (∀ n ∈ F, UT ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UT) →
      ∀ (κM ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      0 ≤ κM → κM ≤ 1/50 → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (UQ Alo Blo σ : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      Real.exp (aLong*L) ≤ UQ → UQ ≤ Alo → Alo ≤ Blo → Blo ≤ 2*UQ →
      (q : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      R ≤ UQ*UM*UT/2 → Y^(3/5 : ℝ) ≤ UM*UT/2 → Real.log (8*(UQ*UM*UT)) ≤ c*L →
      (∫ u in Set.Icc (-R) R,
        ‖primeReciprocalPolynomial s coeff u *
          (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)), harmonicMellinWeight (u+σ) n*χ (n : ZMod q))*
          (∑ n ∈ Ioc lo hi, ambientPrimeMellinCoefficient κM L S ν χM n*harmonicMellinWeight u n)*
          (∑ n ∈ F, γT n*harmonicMellinWeight u n)‖^2) ≤ L^(-A) := by
  obtain ⟨B0,hB0,hmain⟩ := exists_literal_four_factor_integral_decay_log_radius
    (E := Et) ha ha1 hbeta hc hd hBcoeff hAs0 haLong hAs hH Tmod Sshift
  refine ⟨B0,hB0,?_⟩
  intro Bsave hsave S hS hprecision
  filter_upwards [hmain Bsave hsave,
    eventually_ambient_prime_mellin_low_factor hZ hS hB0.le hprecision]
    with L hdecay hlow
  intro s hs coeff Y P R hY hYlo hYhi hPlo hPhi hR hRY hsp hcoeff
    lo hi F γT UM UT BT hUM hUT hBT hBTpow hγT hMband hFband
    κM ν qM hqMInst χM hκ hκmax hqM hν UQ Alo Blo σ q hqInst χ hUQ hQA hAB hBQ hq hσ
    hmeanScale hresScale hlog
  have hM := hlow κM hκ hκmax qM χM hqM ν hν
  apply hdecay s hs coeff Y P R hY hYlo hYhi hPlo hPhi hR hRY hsp hcoeff
    (Ioc lo hi) F (ambientPrimeMellinCoefficient κM L S ν χM) γT
    UM UT 1 BT hUM hUT zero_le_one hBT (by simpa only [one_mul] using hBTpow) hBTpow
    (fun n hn => hM.1 n ((Nat.zero_le lo).trans_lt (mem_Ioc.mp hn).1))
    hγT hMband hFband UQ Alo Blo σ q χ hUQ hQA hAB hBQ hq hσ hmeanScale hresScale hlog
  intro u _ hu
  exact hM.2 u hu lo hi

theorem exists_ambient_rough_four_factor_integral_decay_log_radius
    (hZ : PrimitiveZeroFreeRightOf (23 / 24))
    {a beta c d Bcoeff A As H Et aLong γrough vMax : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hbeta : beta < 1) (hc : 0 ≤ c) (hd : 0 < d)
    (hBcoeff : 1 ≤ Bcoeff) (hAs0 : 0 ≤ As) (haLong : 0 < aLong)
    (hγ : 0 < γrough) (hv : vMax < 1)
    (hAs : A+2*Et+21 ≤ 2*As) (hH : A+2*Et+23 ≤ 2*H)
    (Tmod Sshift Cmod Sfreq : ℝ) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ Bsave : ℝ, A+B0+2*Et+7 ≤ 2*Bsave →
      ∀ S : ℝ, 0 ≤ S → max (max B0 Sfreq) Cmod+Bsave+5 ≤ S →
      ∀ᶠ L : ℝ in atTop, ∀ (s : Finset ℕ), (∀ p ∈ s, Nat.Prime p) →
      ∀ (coeff : s → ℂ) (Y P R : ℝ),
      1 ≤ Y → d*L ≤ Real.log Y → Real.log Y ≤ c*L →
      Real.exp (L^a)/2 ≤ P → P ≤ Real.exp (L^beta) →
      0 ≤ R → R ≤ Y →
      (∀ p ∈ s, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*P) →
      (∀ p : s, ‖coeff p‖ ≤ Bcoeff) →
      ∀ (lo hi : ℕ) (F : Finset ℕ) (γT : ℕ → ℂ) (UM UT BT : ℝ),
      0 < UM → 1 ≤ UT → 0 ≤ BT → BT ≤ L^Et →
      (∀ n ∈ F, ‖γT n‖ ≤ BT) →
      (∀ n ∈ Ioc lo hi, UM ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UM) →
      (∀ n ∈ F, UT ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UT) →
      ∀ (aM v ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      v ≤ vMax → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (UQ Alo Blo σ : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      Real.exp (aLong*L) ≤ UQ → UQ ≤ Alo → Alo ≤ Blo → Blo ≤ 2*UQ →
      (q : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      R ≤ UQ*UM*UT/2 → Y^(3/5 : ℝ) ≤ UM*UT/2 → Real.log (8*(UQ*UM*UT)) ≤ c*L →
      (∫ u in Set.Icc (-R) R,
        ‖primeReciprocalPolynomial s coeff u *
          (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)), harmonicMellinWeight (u+σ) n*χ (n : ZMod q))*
          (∑ n ∈ Ioc lo hi, ambientRoughMellinCoefficient γrough L S aM v ν χM n*harmonicMellinWeight u n)*
          (∑ n ∈ F, γT n*harmonicMellinWeight u n)‖^2) ≤ L^(-A) := by
  obtain ⟨B0,hB0,hmain⟩ := exists_literal_four_factor_integral_decay_log_radius
    (E := Et) ha ha1 hbeta hc hd hBcoeff hAs0 haLong hAs hH Tmod Sshift
  refine ⟨B0,hB0,?_⟩
  intro Bsave hsave S hS hprecision
  filter_upwards [hmain Bsave hsave,
    eventually_ambient_rough_mellin_low_factor hZ hγ hv hS hB0.le hprecision]
    with L hdecay hlow
  intro s hs coeff Y P R hY hYlo hYhi hPlo hPhi hR hRY hsp hcoeff
    lo hi F γT UM UT BT hUM hUT hBT hBTpow hγT hMband hFband
    aM v ν qM hqMInst χM hvM hqM hν UQ Alo Blo σ q hqInst χ hUQ hQA hAB hBQ hq hσ
    hmeanScale hresScale hlog
  have hM := hlow aM v hvM qM χM hqM ν hν
  apply hdecay s hs coeff Y P R hY hYlo hYhi hPlo hPhi hR hRY hsp hcoeff
    (Ioc lo hi) F (ambientRoughMellinCoefficient γrough L S aM v ν χM) γT
    UM UT 1 BT hUM hUT zero_le_one hBT (by simpa only [one_mul] using hBTpow) hBTpow
    (fun n hn => hM.1 n ((Nat.zero_le lo).trans_lt (mem_Ioc.mp hn).1))
    hγT hMband hFband UQ Alo Blo σ q χ hUQ hQA hAB hBQ hq hσ hmeanScale hresScale hlog
  intro u _ hu
  exact hM.2 u hu lo hi

theorem exists_original_selected_rough_integral_decay
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q cLog d A aLong γrough vMax : ℝ}
    (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1) (hcLog : 0 ≤ cLog) (hd : 0 < d)
    (haLong : 0 < aLong)
    (hγ : 0 < γrough) (hv : vMax < 1)
    (T : ℕ) (Tmod Sshift Cmod Sfreq : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B As H : ℝ, 0 ≤ As →
      A+2*(C+B)+21 ≤ 2*As → A+2*(C+B)+23 ≤ 2*H →
      ∃ B0 : ℝ, 0 < B0 ∧ ∀ Bsave : ℝ, A+B0+2*(C+B)+7 ≤ 2*Bsave →
      ∀ S : ℝ, 0 ≤ S → max (max B0 Sfreq) Cmod+Bsave+5 ≤ S →
      ∀ᶠ L : ℝ in atTop,
      ∀ (r jStar : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (tmarks umarks : candidatePIndices c L → ℕ) (big : Finset (candidatePIndices c L))
        (b : GroupMarkedLists (fun g : big => candidatePBand (c*L) g.val.val)
          (fun g : big => umarks g.val) → ℂ) (κ : ℕ → ℂ),
      (∀ g, tmarks g ≤ T) → (∀ l, ‖b l‖ ≤ L^B) → (∀ n, ‖κ n‖ ≤ 1) →
      ∀ (g : ℕ), g ∈ candidateSmallPIndices c L →
      ∀ (s : Finset ℕ) (Y P R : ℝ), s ⊆ candidatePBand (c*L) g → s.Nonempty →
      1 ≤ Y → d*L ≤ Real.log Y → Real.log Y ≤ cLog*L →
      0 ≤ R → R ≤ Y → R ≤ Real.exp L →
      (∀ p ∈ s, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*P) →
      ∀ (qP qT : ℕ) (χP : DirichletCharacter ℂ qP) (χT : DirichletCharacter ℂ qT)
        (τP τT : ℝ) (lo hi : ℕ) (F : Finset ℕ) (UM UT : ℝ),
      0 < UM → 1 ≤ UT →
      (∀ n ∈ Ioc lo hi, UM ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UM) →
      (∀ n ∈ F, UT ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UT) →
      ∀ (aM v ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      v ≤ vMax → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (UQ Alo Blo σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      Real.exp (aLong*L) ≤ UQ → UQ ≤ Alo → Alo ≤ Blo → Blo ≤ 2*UQ →
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      R ≤ UQ*UM*UT/2 → Y^(3/5 : ℝ) ≤ UM*UT/2 → Real.log (8*(UQ*UM*UT)) ≤ cLog*L →
      (∫ u in Set.Icc (-R) R,
        ‖(∑ p ∈ s, (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
            (χP (p : ZMod qP)*typeIIPhase τP p)*harmonicMellinWeight u p) *
          (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
            typeIIPhase σ n*χQ (n : ZMod qQ)*harmonicMellinWeight u n)*
          (∑ n ∈ Ioc lo hi, (ambientRoughIntervalTypeIIAlpha γrough L S aM v n : ℂ)*
            χM (n : ZMod qM)*typeIIPhase ν n*harmonicMellinWeight u n)*
          (∑ n ∈ F, candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
            tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n) n*
              harmonicMellinWeight u n)‖^2) ≤ L^(-A) := by
  obtain ⟨C,hC,hres⟩ := exists_candidate_selected_residual_power_bound hc hq0 hq1 T
  obtain ⟨Bcoeff,hBcoeff,hsmall⟩ := exists_candidate_small_prime_factor_data hc
  refine ⟨C,hC,?_⟩
  intro B As H hAs0 hAs hH
  obtain ⟨B0,hB0,hmain⟩ := exists_ambient_rough_four_factor_integral_decay
    (a := (1/10 : ℝ)) (beta := (1/5 : ℝ)) (Et := C+B) hZ
    (by norm_num) (by norm_num) (by norm_num) hcLog hd hBcoeff hAs0 haLong hγ hv
    hAs hH Tmod Sshift Cmod Sfreq
  refine ⟨B0,hB0,?_⟩
  intro Bsave hsave S hS hprecision
  filter_upwards [hmain Bsave hsave S hS hprecision,hres,hsmall,eventually_gt_atTop (0 : ℝ)]
    with L hdecay hresL hsmallL hL
  intro r jStar hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ g hg s Y P R hs hne
    hY hYlo hYhi hR hRY hRX hsp qP qT χP χT τP τT lo hi F UM UT hUM hUT hMband hFband
    aM v ν qM hqMInst χM hvM hqM hν UQ Alo Blo σ qQ hqQInst χQ hUQ hQA hAB hBQ hqQ hσ
    hmeanScale hresScale hlog
  obtain ⟨hsprime,hPlo,hPhi,hcoeff⟩ := hsmallL g hg s P hs hne hsp
  have hT := hresL B r jStar hr hj take hkeep ξ tmarks umarks big b κ
    (fun n => χT (n : ZMod qT)*typeIIPhase τT n) ht hb hκ
    (fun n => character_typeIIPhase_norm_le χT τT n)
  have hbound := hdecay s hsprime
    (fun p => (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
      (χP (p.val : ZMod qP)*typeIIPhase τP p.val))
    Y P R hY hYlo hYhi hPlo hPhi hR hRY hRX hsp
    (hcoeff (fun n => χP (n : ZMod qP)*typeIIPhase τP n)
      (fun n _ => character_typeIIPhase_norm_le χP τP n))
    lo hi F (candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
      tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n))
    UM UT (L^(C+B)) hUM hUT (Real.rpow_nonneg hL.le _) le_rfl
    (fun n _ => hT n) hMband hFband
    aM v ν qM χM hvM hqM hν UQ Alo Blo σ qQ χQ hUQ hQA hAB hBQ hqQ hσ
    hmeanScale hresScale hlog
  have hQeq (u : ℝ) :
      (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
        typeIIPhase σ n*χQ (n : ZMod qQ)*harmonicMellinWeight u n) =
      ∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
        harmonicMellinWeight (u+σ) n*χQ (n : ZMod qQ) := by
    apply sum_congr rfl
    intro n _
    rw [mul_right_comm,typeIIPhase_harmonic_mellin_shift]
  have hMeq (u : ℝ) :
      (∑ n ∈ Ioc lo hi, (ambientRoughIntervalTypeIIAlpha γrough L S aM v n : ℂ)*
        χM (n : ZMod qM)*typeIIPhase ν n*harmonicMellinWeight u n) =
      ∑ n ∈ Ioc lo hi, ambientRoughMellinCoefficient γrough L S aM v ν χM n*harmonicMellinWeight u n := by
    apply sum_congr rfl
    intro n hn
    rw [ambient_rough_original_phase_coefficient γrough L S aM v ν χM
      ((Nat.zero_le lo).trans_lt (mem_Ioc.mp hn).1)]
  have hPeq (u : ℝ) := prime_reciprocal_polynomial_eq_harmonic_sum s
    (fun n : ℕ => (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
      (χP (n : ZMod qP)*typeIIPhase τP n)) u
  simpa only [hPeq,hQeq,hMeq] using hbound

theorem exists_original_selected_prime_integral_decay
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q cLog d A aLong : ℝ}
    (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1) (hcLog : 0 ≤ cLog) (hd : 0 < d)
    (haLong : 0 < aLong)
    (T : ℕ) (Tmod Sshift Cmod Sfreq : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B As H : ℝ, 0 ≤ As →
      A+2*(C+B)+21 ≤ 2*As → A+2*(C+B)+23 ≤ 2*H →
      ∃ B0 : ℝ, 0 < B0 ∧ ∀ Bsave : ℝ, A+B0+2*(C+B)+7 ≤ 2*Bsave →
      ∀ S : ℝ, 0 ≤ S → max (max B0 Sfreq) Cmod+Bsave+5 ≤ S →
      ∀ᶠ L : ℝ in atTop,
      ∀ (r jStar : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (tmarks umarks : candidatePIndices c L → ℕ) (big : Finset (candidatePIndices c L))
        (b : GroupMarkedLists (fun g : big => candidatePBand (c*L) g.val.val)
          (fun g : big => umarks g.val) → ℂ) (κ : ℕ → ℂ),
      (∀ g, tmarks g ≤ T) → (∀ l, ‖b l‖ ≤ L^B) → (∀ n, ‖κ n‖ ≤ 1) →
      ∀ (g : ℕ), g ∈ candidateSmallPIndices c L →
      ∀ (s : Finset ℕ) (Y P R : ℝ), s ⊆ candidatePBand (c*L) g → s.Nonempty →
      1 ≤ Y → d*L ≤ Real.log Y → Real.log Y ≤ cLog*L →
      0 ≤ R → R ≤ Y → R ≤ Real.exp L →
      (∀ p ∈ s, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*P) →
      ∀ (qP qT : ℕ) (χP : DirichletCharacter ℂ qP) (χT : DirichletCharacter ℂ qT)
        (τP τT : ℝ) (lo hi : ℕ) (F : Finset ℕ) (UM UT : ℝ),
      0 < UM → 1 ≤ UT →
      (∀ n ∈ Ioc lo hi, UM ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UM) →
      (∀ n ∈ F, UT ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UT) →
      ∀ (κM ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      0 ≤ κM → κM ≤ 1/50 → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (UQ Alo Blo σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      Real.exp (aLong*L) ≤ UQ → UQ ≤ Alo → Alo ≤ Blo → Blo ≤ 2*UQ →
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      R ≤ UQ*UM*UT/2 → Y^(3/5 : ℝ) ≤ UM*UT/2 → Real.log (8*(UQ*UM*UT)) ≤ cLog*L →
      (∫ u in Set.Icc (-R) R,
        ‖(∑ p ∈ s, (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
            (χP (p : ZMod qP)*typeIIPhase τP p)*harmonicMellinWeight u p) *
          (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
            typeIIPhase σ n*χQ (n : ZMod qQ)*harmonicMellinWeight u n)*
          (∑ n ∈ Ioc lo hi, (ambientPrimeTypeIIAlpha κM L S n : ℂ)*
            χM (n : ZMod qM)*typeIIPhase ν n*harmonicMellinWeight u n)*
          (∑ n ∈ F, candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
            tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n) n*
              harmonicMellinWeight u n)‖^2) ≤ L^(-A) := by
  obtain ⟨C,hC,hres⟩ := exists_candidate_selected_residual_power_bound hc hq0 hq1 T
  obtain ⟨Bcoeff,hBcoeff,hsmall⟩ := exists_candidate_small_prime_factor_data hc
  refine ⟨C,hC,?_⟩
  intro B As H hAs0 hAs hH
  obtain ⟨B0,hB0,hmain⟩ := exists_ambient_prime_four_factor_integral_decay
    (a := (1/10 : ℝ)) (beta := (1/5 : ℝ)) (Et := C+B) hZ
    (by norm_num) (by norm_num) (by norm_num) hcLog hd hBcoeff hAs0 haLong
    hAs hH Tmod Sshift Cmod Sfreq
  refine ⟨B0,hB0,?_⟩
  intro Bsave hsave S hS hprecision
  filter_upwards [hmain Bsave hsave S hS hprecision,hres,hsmall,eventually_gt_atTop (0 : ℝ)]
    with L hdecay hresL hsmallL hL
  intro r jStar hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ g hg s Y P R hs hne
    hY hYlo hYhi hR hRY hRX hsp qP qT χP χT τP τT lo hi F UM UT hUM hUT hMband hFband
    κM ν qM hqMInst χM hκM hκmax hqM hν UQ Alo Blo σ qQ hqQInst χQ hUQ hQA hAB hBQ hqQ hσ
    hmeanScale hresScale hlog
  obtain ⟨hsprime,hPlo,hPhi,hcoeff⟩ := hsmallL g hg s P hs hne hsp
  have hT := hresL B r jStar hr hj take hkeep ξ tmarks umarks big b κ
    (fun n => χT (n : ZMod qT)*typeIIPhase τT n) ht hb hκ
    (fun n => character_typeIIPhase_norm_le χT τT n)
  have hbound := hdecay s hsprime
    (fun p => (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
      (χP (p.val : ZMod qP)*typeIIPhase τP p.val))
    Y P R hY hYlo hYhi hPlo hPhi hR hRY hRX hsp
    (hcoeff (fun n => χP (n : ZMod qP)*typeIIPhase τP n)
      (fun n _ => character_typeIIPhase_norm_le χP τP n))
    lo hi F (candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
      tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n))
    UM UT (L^(C+B)) hUM hUT (Real.rpow_nonneg hL.le _) le_rfl
    (fun n _ => hT n) hMband hFband
    κM ν qM χM hκM hκmax hqM hν UQ Alo Blo σ qQ χQ hUQ hQA hAB hBQ hqQ hσ
    hmeanScale hresScale hlog
  have hQeq (u : ℝ) :
      (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
        typeIIPhase σ n*χQ (n : ZMod qQ)*harmonicMellinWeight u n) =
      ∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
        harmonicMellinWeight (u+σ) n*χQ (n : ZMod qQ) := by
    apply sum_congr rfl
    intro n _
    rw [mul_right_comm,typeIIPhase_harmonic_mellin_shift]
  have hMeq (u : ℝ) :
      (∑ n ∈ Ioc lo hi, (ambientPrimeTypeIIAlpha κM L S n : ℂ)*
        χM (n : ZMod qM)*typeIIPhase ν n*harmonicMellinWeight u n) =
      ∑ n ∈ Ioc lo hi, ambientPrimeMellinCoefficient κM L S ν χM n*harmonicMellinWeight u n := by
    apply sum_congr rfl
    intro n hn
    rw [ambient_prime_original_phase_coefficient κM L S ν χM
      ((Nat.zero_le lo).trans_lt (mem_Ioc.mp hn).1)]
  have hPeq (u : ℝ) := prime_reciprocal_polynomial_eq_harmonic_sum s
    (fun n : ℕ => (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
      (χP (n : ZMod qP)*typeIIPhase τP n)) u
  simpa only [hPeq,hQeq,hMeq] using hbound

theorem exists_original_filtered_rough_integral_decay
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q cLog d A aLong γrough vMax : ℝ}
    (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1) (hcLog : 0 ≤ cLog) (hd : 0 < d)
    (haLong : 0 < aLong)
    (hγ : 0 < γrough) (hv : vMax < 1)
    (T : ℕ) (Tmod Sshift Cmod Sfreq : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B As H : ℝ, 0 ≤ As →
      A+2*(C+B)+21 ≤ 2*As → A+2*(C+B)+23 ≤ 2*H →
      ∃ B0 : ℝ, 0 < B0 ∧ ∀ Bsave : ℝ, A+B0+2*(C+B)+7 ≤ 2*Bsave →
      ∀ S : ℝ, 0 ≤ S → max (max B0 Sfreq) Cmod+Bsave+5 ≤ S →
      ∀ᶠ L : ℝ in atTop,
      ∀ (r jStar : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (tmarks umarks : candidatePIndices c L → ℕ) (big : Finset (candidatePIndices c L))
        (b : GroupMarkedLists (fun g : big => candidatePBand (c*L) g.val.val)
          (fun g : big => umarks g.val) → ℂ) (κ : ℕ → ℂ),
      (∀ g, tmarks g ≤ T) → (∀ l, ‖b l‖ ≤ L^B) → (∀ n, ‖κ n‖ ≤ 1) →
      ∀ (g : ℕ), g ∈ candidateSmallPIndices c L →
      ∀ (s : Finset ℕ) (Y P R : ℝ), s ⊆ candidatePBand (c*L) g → s.Nonempty →
      1 ≤ Y → d*L ≤ Real.log Y → Real.log Y ≤ cLog*L →
      0 ≤ R → R ≤ Y → R ≤ Real.exp L →
      (∀ p ∈ s, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*P) →
      ∀ (qP qT : ℕ) (χP : DirichletCharacter ℂ qP) (χT : DirichletCharacter ℂ qT)
        (τP τT : ℝ) (lo hi : ℕ) (F : Finset ℕ) (UM UT : ℝ),
      0 < UM → 1 ≤ UT →
      (∀ n ∈ Ioc lo hi, UM ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UM) →
      (∀ n ∈ F, UT ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UT) →
      ∀ (aM v ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      v ≤ vMax → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (UQ Alo Blo σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      Real.exp (aLong*L) ≤ UQ → UQ ≤ Alo → Alo ≤ Blo → Blo ≤ 2*UQ →
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      R ≤ UQ*UM*UT/2 → Y^(3/5 : ℝ) ≤ UM*UT/2 → Real.log (8*(UQ*UM*UT)) ≤ cLog*L →
      (∫ u in Set.Icc (-R) R,
        ‖(∑ p ∈ s, (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
            (χP (p : ZMod qP)*typeIIPhase τP p)*harmonicMellinWeight u p) *
          (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
            typeIIPhase σ n*χQ (n : ZMod qQ)*harmonicMellinWeight u n)*
          (∑ n ∈ (Ioc lo hi).filter (fun n =>
              (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ) ≠ 0),
            (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ)*
              χM (n : ZMod qM)*typeIIPhase ν n*harmonicMellinWeight u n)*
          (∑ n ∈ F, candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
            tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n) n*
              harmonicMellinWeight u n)‖^2) ≤ L^(-A) := by
  simpa only [typeIIRestrict_nonzero_phase_mellin_sum] using
    (exists_original_selected_rough_integral_decay (A := A) hZ hc hq0 hq1 hcLog hd haLong hγ hv T Tmod Sshift Cmod Sfreq)

theorem exists_original_filtered_prime_integral_decay
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q cLog d A aLong : ℝ}
    (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1) (hcLog : 0 ≤ cLog) (hd : 0 < d)
    (haLong : 0 < aLong)
    (T : ℕ) (Tmod Sshift Cmod Sfreq : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B As H : ℝ, 0 ≤ As →
      A+2*(C+B)+21 ≤ 2*As → A+2*(C+B)+23 ≤ 2*H →
      ∃ B0 : ℝ, 0 < B0 ∧ ∀ Bsave : ℝ, A+B0+2*(C+B)+7 ≤ 2*Bsave →
      ∀ S : ℝ, 0 ≤ S → max (max B0 Sfreq) Cmod+Bsave+5 ≤ S →
      ∀ᶠ L : ℝ in atTop,
      ∀ (r jStar : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (tmarks umarks : candidatePIndices c L → ℕ) (big : Finset (candidatePIndices c L))
        (b : GroupMarkedLists (fun g : big => candidatePBand (c*L) g.val.val)
          (fun g : big => umarks g.val) → ℂ) (κ : ℕ → ℂ),
      (∀ g, tmarks g ≤ T) → (∀ l, ‖b l‖ ≤ L^B) → (∀ n, ‖κ n‖ ≤ 1) →
      ∀ (g : ℕ), g ∈ candidateSmallPIndices c L →
      ∀ (s : Finset ℕ) (Y P R : ℝ), s ⊆ candidatePBand (c*L) g → s.Nonempty →
      1 ≤ Y → d*L ≤ Real.log Y → Real.log Y ≤ cLog*L →
      0 ≤ R → R ≤ Y → R ≤ Real.exp L →
      (∀ p ∈ s, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*P) →
      ∀ (qP qT : ℕ) (χP : DirichletCharacter ℂ qP) (χT : DirichletCharacter ℂ qT)
        (τP τT : ℝ) (lo hi : ℕ) (F : Finset ℕ) (UM UT : ℝ),
      0 < UM → 1 ≤ UT →
      (∀ n ∈ Ioc lo hi, UM ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UM) →
      (∀ n ∈ F, UT ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UT) →
      ∀ (κM ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      0 ≤ κM → κM ≤ 1/50 → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (UQ Alo Blo σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      Real.exp (aLong*L) ≤ UQ → UQ ≤ Alo → Alo ≤ Blo → Blo ≤ 2*UQ →
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      R ≤ UQ*UM*UT/2 → Y^(3/5 : ℝ) ≤ UM*UT/2 → Real.log (8*(UQ*UM*UT)) ≤ cLog*L →
      (∫ u in Set.Icc (-R) R,
        ‖(∑ p ∈ s, (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
            (χP (p : ZMod qP)*typeIIPhase τP p)*harmonicMellinWeight u p) *
          (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
            typeIIPhase σ n*χQ (n : ZMod qQ)*harmonicMellinWeight u n)*
          (∑ n ∈ (Ioc lo hi).filter (fun n =>
              (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ) ≠ 0),
            (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ)*
              χM (n : ZMod qM)*typeIIPhase ν n*harmonicMellinWeight u n)*
          (∑ n ∈ F, candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
            tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n) n*
              harmonicMellinWeight u n)‖^2) ≤ L^(-A) := by
  simpa only [typeIIRestrict_nonzero_phase_mellin_sum] using
    (exists_original_selected_prime_integral_decay (A := A) hZ hc hq0 hq1 hcLog hd haLong T Tmod Sshift Cmod Sfreq)

theorem exists_original_filtered_rough_integral_precision
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q cLog d A aLong γrough vMax : ℝ}
    (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1) (hcLog : 0 ≤ cLog) (hd : 0 < d)
    (haLong : 0 < aLong)
    (hγ : 0 < γrough) (hv : vMax < 1)
    (T : ℕ) (Tmod Sshift Cmod Sfreq : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, ∃ S₀ : ℝ, 0 ≤ S₀ ∧
      ∀ S : ℝ, S₀ ≤ S →
      ∀ᶠ L : ℝ in atTop,
      ∀ (r jStar : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (tmarks umarks : candidatePIndices c L → ℕ) (big : Finset (candidatePIndices c L))
        (b : GroupMarkedLists (fun g : big => candidatePBand (c*L) g.val.val)
          (fun g : big => umarks g.val) → ℂ) (κ : ℕ → ℂ),
      (∀ g, tmarks g ≤ T) → (∀ l, ‖b l‖ ≤ L^B) → (∀ n, ‖κ n‖ ≤ 1) →
      ∀ (g : ℕ), g ∈ candidateSmallPIndices c L →
      ∀ (s : Finset ℕ) (Y P R : ℝ), s ⊆ candidatePBand (c*L) g → s.Nonempty →
      1 ≤ Y → d*L ≤ Real.log Y → Real.log Y ≤ cLog*L →
      0 ≤ R → R ≤ Y → R ≤ Real.exp L →
      (∀ p ∈ s, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*P) →
      ∀ (qP qT : ℕ) (χP : DirichletCharacter ℂ qP) (χT : DirichletCharacter ℂ qT)
        (τP τT : ℝ) (lo hi : ℕ) (F : Finset ℕ) (UM UT : ℝ),
      0 < UM → 1 ≤ UT →
      (∀ n ∈ Ioc lo hi, UM ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UM) →
      (∀ n ∈ F, UT ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UT) →
      ∀ (aM v ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      v ≤ vMax → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (UQ Alo Blo σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      Real.exp (aLong*L) ≤ UQ → UQ ≤ Alo → Alo ≤ Blo → Blo ≤ 2*UQ →
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      R ≤ UQ*UM*UT/2 → Y^(3/5 : ℝ) ≤ UM*UT/2 → Real.log (8*(UQ*UM*UT)) ≤ cLog*L →
      (∫ u in Set.Icc (-R) R,
        ‖(∑ p ∈ s, (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
            (χP (p : ZMod qP)*typeIIPhase τP p)*harmonicMellinWeight u p) *
          (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
            typeIIPhase σ n*χQ (n : ZMod qQ)*harmonicMellinWeight u n)*
          (∑ n ∈ (Ioc lo hi).filter (fun n =>
              (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ) ≠ 0),
            (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ)*
              χM (n : ZMod qM)*typeIIPhase ν n*harmonicMellinWeight u n)*
          (∑ n ∈ F, candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
            tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n) n*
              harmonicMellinWeight u n)‖^2) ≤ L^(-A) := by
  obtain ⟨C, hC, hdecay⟩ := exists_original_filtered_rough_integral_decay (A := A)
    hZ hc hq0 hq1 hcLog hd haLong hγ hv T Tmod Sshift Cmod Sfreq
  refine ⟨C, hC, ?_⟩
  intro B
  let X := max 0 ((A+2*(C+B)+23)/2)
  have hX : 0 ≤ X := le_max_left _ _
  have hXlower : (A+2*(C+B)+23)/2 ≤ X := le_max_right _ _
  obtain ⟨B0, hB0, hbound⟩ := hdecay B X X hX (by linarith) (by linarith)
  let Bsave := (A+B0+2*(C+B)+7)/2
  have hsave : A+B0+2*(C+B)+7 ≤ 2*Bsave := by dsimp [Bsave]; linarith
  refine ⟨max 0 (max (max B0 Sfreq) Cmod+Bsave+5), le_max_left _ _, ?_⟩
  intro S hS
  exact hbound Bsave hsave S ((le_max_left _ _).trans hS) ((le_max_right _ _).trans hS)

theorem exists_original_filtered_prime_integral_precision
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q cLog d A aLong : ℝ}
    (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1) (hcLog : 0 ≤ cLog) (hd : 0 < d)
    (haLong : 0 < aLong)
    (T : ℕ) (Tmod Sshift Cmod Sfreq : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, ∃ S₀ : ℝ, 0 ≤ S₀ ∧
      ∀ S : ℝ, S₀ ≤ S →
      ∀ᶠ L : ℝ in atTop,
      ∀ (r jStar : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (tmarks umarks : candidatePIndices c L → ℕ) (big : Finset (candidatePIndices c L))
        (b : GroupMarkedLists (fun g : big => candidatePBand (c*L) g.val.val)
          (fun g : big => umarks g.val) → ℂ) (κ : ℕ → ℂ),
      (∀ g, tmarks g ≤ T) → (∀ l, ‖b l‖ ≤ L^B) → (∀ n, ‖κ n‖ ≤ 1) →
      ∀ (g : ℕ), g ∈ candidateSmallPIndices c L →
      ∀ (s : Finset ℕ) (Y P R : ℝ), s ⊆ candidatePBand (c*L) g → s.Nonempty →
      1 ≤ Y → d*L ≤ Real.log Y → Real.log Y ≤ cLog*L →
      0 ≤ R → R ≤ Y → R ≤ Real.exp L →
      (∀ p ∈ s, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*P) →
      ∀ (qP qT : ℕ) (χP : DirichletCharacter ℂ qP) (χT : DirichletCharacter ℂ qT)
        (τP τT : ℝ) (lo hi : ℕ) (F : Finset ℕ) (UM UT : ℝ),
      0 < UM → 1 ≤ UT →
      (∀ n ∈ Ioc lo hi, UM ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UM) →
      (∀ n ∈ F, UT ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UT) →
      ∀ (κM ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      0 ≤ κM → κM ≤ 1/50 → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (UQ Alo Blo σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      Real.exp (aLong*L) ≤ UQ → UQ ≤ Alo → Alo ≤ Blo → Blo ≤ 2*UQ →
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      R ≤ UQ*UM*UT/2 → Y^(3/5 : ℝ) ≤ UM*UT/2 → Real.log (8*(UQ*UM*UT)) ≤ cLog*L →
      (∫ u in Set.Icc (-R) R,
        ‖(∑ p ∈ s, (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
            (χP (p : ZMod qP)*typeIIPhase τP p)*harmonicMellinWeight u p) *
          (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
            typeIIPhase σ n*χQ (n : ZMod qQ)*harmonicMellinWeight u n)*
          (∑ n ∈ (Ioc lo hi).filter (fun n =>
              (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ) ≠ 0),
            (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ)*
              χM (n : ZMod qM)*typeIIPhase ν n*harmonicMellinWeight u n)*
          (∑ n ∈ F, candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
            tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n) n*
              harmonicMellinWeight u n)‖^2) ≤ L^(-A) := by
  obtain ⟨C, hC, hdecay⟩ := exists_original_filtered_prime_integral_decay (A := A)
    hZ hc hq0 hq1 hcLog hd haLong T Tmod Sshift Cmod Sfreq
  refine ⟨C, hC, ?_⟩
  intro B
  let X := max 0 ((A+2*(C+B)+23)/2)
  have hX : 0 ≤ X := le_max_left _ _
  have hXlower : (A+2*(C+B)+23)/2 ≤ X := le_max_right _ _
  obtain ⟨B0, hB0, hbound⟩ := hdecay B X X hX (by linarith) (by linarith)
  let Bsave := (A+B0+2*(C+B)+7)/2
  have hsave : A+B0+2*(C+B)+7 ≤ 2*Bsave := by dsimp [Bsave]; linarith
  refine ⟨max 0 (max (max B0 Sfreq) Cmod+Bsave+5), le_max_left _ _, ?_⟩
  intro S hS
  exact hbound Bsave hsave S ((le_max_left _ _).trans hS) ((le_max_right _ _).trans hS)

theorem exists_original_filtered_prime_integral_precision_with_residual_multiplier
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q cLog d A aLong : ℝ}
    (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1) (hcLog : 0 ≤ cLog) (hd : 0 < d)
    (haLong : 0 < aLong)
    (T : ℕ) (Tmod Sshift Cmod Sfreq : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, ∃ S₀ : ℝ, 0 ≤ S₀ ∧
      ∀ S : ℝ, S₀ ≤ S →
      ∀ᶠ L : ℝ in atTop,
      ∀ (r jStar : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (tmarks umarks : candidatePIndices c L → ℕ) (big : Finset (candidatePIndices c L))
        (b : GroupMarkedLists (fun g : big => candidatePBand (c*L) g.val.val)
          (fun g : big => umarks g.val) → ℂ) (κ ρ : ℕ → ℂ),
      (∀ g, tmarks g ≤ T) → (∀ l, ‖b l‖ ≤ L^B) → (∀ n, ‖κ n‖ ≤ 1) → (∀ n, ‖ρ n‖ ≤ 1) →
      ∀ (g : ℕ), g ∈ candidateSmallPIndices c L →
      ∀ (s : Finset ℕ) (Y P R : ℝ), s ⊆ candidatePBand (c*L) g → s.Nonempty →
      1 ≤ Y → d*L ≤ Real.log Y → Real.log Y ≤ cLog*L →
      0 ≤ R → R ≤ Y → R ≤ Real.exp L →
      (∀ p ∈ s, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*P) →
      ∀ (qP qT : ℕ) (χP : DirichletCharacter ℂ qP) (χT : DirichletCharacter ℂ qT)
        (τP τT : ℝ) (lo hi : ℕ) (F : Finset ℕ) (UM UT : ℝ),
      0 < UM → 1 ≤ UT →
      (∀ n ∈ Ioc lo hi, UM ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UM) →
      (∀ n ∈ F, UT ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UT) →
      ∀ (κM ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      0 ≤ κM → κM ≤ 1/50 → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (UQ Alo Blo σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      Real.exp (aLong*L) ≤ UQ → UQ ≤ Alo → Alo ≤ Blo → Blo ≤ 2*UQ →
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      R ≤ UQ*UM*UT/2 → Y^(3/5 : ℝ) ≤ UM*UT/2 → Real.log (8*(UQ*UM*UT)) ≤ cLog*L →
      (∫ u in Set.Icc (-R) R,
        ‖(∑ p ∈ s, (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
            (χP (p : ZMod qP)*typeIIPhase τP p)*harmonicMellinWeight u p) *
          (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
            typeIIPhase σ n*χQ (n : ZMod qQ)*harmonicMellinWeight u n)*
          (∑ n ∈ (Ioc lo hi).filter (fun n =>
              (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ) ≠ 0),
            (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ)*
              χM (n : ZMod qM)*typeIIPhase ν n*harmonicMellinWeight u n)*
          (∑ n ∈ F, candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
            tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n*ρ n) n*
              harmonicMellinWeight u n)‖^2) ≤ L^(-A) := by
  obtain ⟨C,hC,hres⟩ := exists_candidate_selected_residual_power_bound hc hq0 hq1 T
  obtain ⟨Bcoeff,hBcoeff,hsmall⟩ := exists_candidate_small_prime_factor_data hc
  refine ⟨C,hC,?_⟩
  intro B
  let X := max 0 ((A+2*(C+B)+23)/2)
  have hAs0 : 0 ≤ X := le_max_left _ _
  have hX : (A+2*(C+B)+23)/2 ≤ X := le_max_right _ _
  have hAs : A+2*(C+B)+21 ≤ 2*X := by linarith
  have hH : A+2*(C+B)+23 ≤ 2*X := by linarith
  obtain ⟨B0,hB0,hmain⟩ := exists_ambient_prime_four_factor_integral_decay
    (a := (1/10 : ℝ)) (beta := (1/5 : ℝ)) (Et := C+B) hZ
    (by norm_num) (by norm_num) (by norm_num) hcLog hd hBcoeff hAs0 haLong
    hAs hH Tmod Sshift Cmod Sfreq
  let Bsave := (A+B0+2*(C+B)+7)/2
  have hsave : A+B0+2*(C+B)+7 ≤ 2*Bsave := by dsimp [Bsave]; linarith
  refine ⟨max 0 (max (max B0 Sfreq) Cmod+Bsave+5), le_max_left _ _, ?_⟩
  intro S hS0
  have hS : 0 ≤ S := (le_max_left _ _).trans hS0
  have hprecision : max (max B0 Sfreq) Cmod+Bsave+5 ≤ S := (le_max_right _ _).trans hS0
  filter_upwards [hmain Bsave hsave S hS hprecision,hres,hsmall,eventually_gt_atTop (0 : ℝ)]
    with L hdecay hresL hsmallL hL
  intro r jStar hr hj take hkeep ξ tmarks umarks big b κ ρ ht hb hκ hρ g hg s Y P R hs hne
    hY hYlo hYhi hR hRY hRX hsp qP qT χP χT τP τT lo hi F UM UT hUM hUT hMband hFband
    κM ν qM hqMInst χM hκM hκmax hqM hν UQ Alo Blo σ qQ hqQInst χQ hUQ hQA hAB hBQ hqQ hσ
    hmeanScale hresScale hlog
  obtain ⟨hsprime,hPlo,hPhi,hcoeff⟩ := hsmallL g hg s P hs hne hsp
  have hT := hresL B r jStar hr hj take hkeep ξ tmarks umarks big b κ
    (fun n => χT (n : ZMod qT)*typeIIPhase τT n*ρ n) ht hb hκ
    (fun n => by
      rw [norm_mul]
      exact (mul_le_mul (character_typeIIPhase_norm_le χT τT n) (hρ n)
        (norm_nonneg _) zero_le_one).trans_eq (mul_one 1))
  have hbound := hdecay s hsprime
    (fun p => (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
      (χP (p.val : ZMod qP)*typeIIPhase τP p.val))
    Y P R hY hYlo hYhi hPlo hPhi hR hRY hRX hsp
    (hcoeff (fun n => χP (n : ZMod qP)*typeIIPhase τP n)
      (fun n _ => character_typeIIPhase_norm_le χP τP n))
    lo hi F (candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
      tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n*ρ n))
    UM UT (L^(C+B)) hUM hUT (Real.rpow_nonneg hL.le _) le_rfl
    (fun n _ => hT n) hMband hFband
    κM ν qM χM hκM hκmax hqM hν UQ Alo Blo σ qQ χQ hUQ hQA hAB hBQ hqQ hσ
    hmeanScale hresScale hlog
  have hQeq (u : ℝ) :
      (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
        typeIIPhase σ n*χQ (n : ZMod qQ)*harmonicMellinWeight u n) =
      ∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
        harmonicMellinWeight (u+σ) n*χQ (n : ZMod qQ) := by
    apply sum_congr rfl
    intro n _
    rw [mul_right_comm,typeIIPhase_harmonic_mellin_shift]
  have hMeq (u : ℝ) :
      (∑ n ∈ Ioc lo hi, (ambientPrimeTypeIIAlpha κM L S n : ℂ)*
        χM (n : ZMod qM)*typeIIPhase ν n*harmonicMellinWeight u n) =
      ∑ n ∈ Ioc lo hi, ambientPrimeMellinCoefficient κM L S ν χM n*harmonicMellinWeight u n := by
    apply sum_congr rfl
    intro n hn
    rw [ambient_prime_original_phase_coefficient κM L S ν χM
      ((Nat.zero_le lo).trans_lt (mem_Ioc.mp hn).1)]
  have hPeq (u : ℝ) := prime_reciprocal_polynomial_eq_harmonic_sum s
    (fun n : ℕ => (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
      (χP (n : ZMod qP)*typeIIPhase τP n)) u
  simpa only [typeIIRestrict_nonzero_phase_mellin_sum,hPeq,hQeq,hMeq] using hbound

theorem exists_original_filtered_rough_integral_precision_with_residual_multiplier
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q cLog d A aLong γrough vMax : ℝ}
    (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1) (hcLog : 0 ≤ cLog) (hd : 0 < d)
    (haLong : 0 < aLong)
    (hγ : 0 < γrough) (hv : vMax < 1)
    (T : ℕ) (Tmod Sshift Cmod Sfreq : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, ∃ S₀ : ℝ, 0 ≤ S₀ ∧
      ∀ S : ℝ, S₀ ≤ S →
      ∀ᶠ L : ℝ in atTop,
      ∀ (r jStar : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (tmarks umarks : candidatePIndices c L → ℕ) (big : Finset (candidatePIndices c L))
        (b : GroupMarkedLists (fun g : big => candidatePBand (c*L) g.val.val)
          (fun g : big => umarks g.val) → ℂ) (κ ρ : ℕ → ℂ),
      (∀ g, tmarks g ≤ T) → (∀ l, ‖b l‖ ≤ L^B) → (∀ n, ‖κ n‖ ≤ 1) → (∀ n, ‖ρ n‖ ≤ 1) →
      ∀ (g : ℕ), g ∈ candidateSmallPIndices c L →
      ∀ (s : Finset ℕ) (Y P R : ℝ), s ⊆ candidatePBand (c*L) g → s.Nonempty →
      1 ≤ Y → d*L ≤ Real.log Y → Real.log Y ≤ cLog*L →
      0 ≤ R → R ≤ Y → R ≤ Real.exp L →
      (∀ p ∈ s, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*P) →
      ∀ (qP qT : ℕ) (χP : DirichletCharacter ℂ qP) (χT : DirichletCharacter ℂ qT)
        (τP τT : ℝ) (lo hi : ℕ) (F : Finset ℕ) (UM UT : ℝ),
      0 < UM → 1 ≤ UT →
      (∀ n ∈ Ioc lo hi, UM ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UM) →
      (∀ n ∈ F, UT ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UT) →
      ∀ (aM v ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      v ≤ vMax → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (UQ Alo Blo σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      Real.exp (aLong*L) ≤ UQ → UQ ≤ Alo → Alo ≤ Blo → Blo ≤ 2*UQ →
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      R ≤ UQ*UM*UT/2 → Y^(3/5 : ℝ) ≤ UM*UT/2 → Real.log (8*(UQ*UM*UT)) ≤ cLog*L →
      (∫ u in Set.Icc (-R) R,
        ‖(∑ p ∈ s, (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
            (χP (p : ZMod qP)*typeIIPhase τP p)*harmonicMellinWeight u p) *
          (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
            typeIIPhase σ n*χQ (n : ZMod qQ)*harmonicMellinWeight u n)*
          (∑ n ∈ (Ioc lo hi).filter (fun n =>
              (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ) ≠ 0),
            (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ)*
              χM (n : ZMod qM)*typeIIPhase ν n*harmonicMellinWeight u n)*
          (∑ n ∈ F, candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
            tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n*ρ n) n*
              harmonicMellinWeight u n)‖^2) ≤ L^(-A) := by
  obtain ⟨C,hC,hres⟩ := exists_candidate_selected_residual_power_bound hc hq0 hq1 T
  obtain ⟨Bcoeff,hBcoeff,hsmall⟩ := exists_candidate_small_prime_factor_data hc
  refine ⟨C,hC,?_⟩
  intro B
  let X := max 0 ((A+2*(C+B)+23)/2)
  have hAs0 : 0 ≤ X := le_max_left _ _
  have hX : (A+2*(C+B)+23)/2 ≤ X := le_max_right _ _
  have hAs : A+2*(C+B)+21 ≤ 2*X := by linarith
  have hH : A+2*(C+B)+23 ≤ 2*X := by linarith
  obtain ⟨B0,hB0,hmain⟩ := exists_ambient_rough_four_factor_integral_decay
    (a := (1/10 : ℝ)) (beta := (1/5 : ℝ)) (Et := C+B) hZ
    (by norm_num) (by norm_num) (by norm_num) hcLog hd hBcoeff hAs0 haLong hγ hv
    hAs hH Tmod Sshift Cmod Sfreq
  let Bsave := (A+B0+2*(C+B)+7)/2
  have hsave : A+B0+2*(C+B)+7 ≤ 2*Bsave := by dsimp [Bsave]; linarith
  refine ⟨max 0 (max (max B0 Sfreq) Cmod+Bsave+5), le_max_left _ _, ?_⟩
  intro S hS0
  have hS : 0 ≤ S := (le_max_left _ _).trans hS0
  have hprecision : max (max B0 Sfreq) Cmod+Bsave+5 ≤ S := (le_max_right _ _).trans hS0
  filter_upwards [hmain Bsave hsave S hS hprecision,hres,hsmall,eventually_gt_atTop (0 : ℝ)]
    with L hdecay hresL hsmallL hL
  intro r jStar hr hj take hkeep ξ tmarks umarks big b κ ρ ht hb hκ hρ g hg s Y P R hs hne
    hY hYlo hYhi hR hRY hRX hsp qP qT χP χT τP τT lo hi F UM UT hUM hUT hMband hFband
    aM v ν qM hqMInst χM hvM hqM hν UQ Alo Blo σ qQ hqQInst χQ hUQ hQA hAB hBQ hqQ hσ
    hmeanScale hresScale hlog
  obtain ⟨hsprime,hPlo,hPhi,hcoeff⟩ := hsmallL g hg s P hs hne hsp
  have hT := hresL B r jStar hr hj take hkeep ξ tmarks umarks big b κ
    (fun n => χT (n : ZMod qT)*typeIIPhase τT n*ρ n) ht hb hκ
    (fun n => by
      rw [norm_mul]
      exact (mul_le_mul (character_typeIIPhase_norm_le χT τT n) (hρ n)
        (norm_nonneg _) zero_le_one).trans_eq (mul_one 1))
  have hbound := hdecay s hsprime
    (fun p => (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
      (χP (p.val : ZMod qP)*typeIIPhase τP p.val))
    Y P R hY hYlo hYhi hPlo hPhi hR hRY hRX hsp
    (hcoeff (fun n => χP (n : ZMod qP)*typeIIPhase τP n)
      (fun n _ => character_typeIIPhase_norm_le χP τP n))
    lo hi F (candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
      tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n*ρ n))
    UM UT (L^(C+B)) hUM hUT (Real.rpow_nonneg hL.le _) le_rfl
    (fun n _ => hT n) hMband hFband
    aM v ν qM χM hvM hqM hν UQ Alo Blo σ qQ χQ hUQ hQA hAB hBQ hqQ hσ
    hmeanScale hresScale hlog
  have hQeq (u : ℝ) :
      (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
        typeIIPhase σ n*χQ (n : ZMod qQ)*harmonicMellinWeight u n) =
      ∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
        harmonicMellinWeight (u+σ) n*χQ (n : ZMod qQ) := by
    apply sum_congr rfl
    intro n _
    rw [mul_right_comm,typeIIPhase_harmonic_mellin_shift]
  have hMeq (u : ℝ) :
      (∑ n ∈ Ioc lo hi, (ambientRoughIntervalTypeIIAlpha γrough L S aM v n : ℂ)*
        χM (n : ZMod qM)*typeIIPhase ν n*harmonicMellinWeight u n) =
      ∑ n ∈ Ioc lo hi, ambientRoughMellinCoefficient γrough L S aM v ν χM n*harmonicMellinWeight u n := by
    apply sum_congr rfl
    intro n hn
    rw [ambient_rough_original_phase_coefficient γrough L S aM v ν χM
      ((Nat.zero_le lo).trans_lt (mem_Ioc.mp hn).1)]
  have hPeq (u : ℝ) := prime_reciprocal_polynomial_eq_harmonic_sum s
    (fun n : ℕ => (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
      (χP (n : ZMod qP)*typeIIPhase τP n)) u
  simpa only [typeIIRestrict_nonzero_phase_mellin_sum,hPeq,hQeq,hMeq] using hbound

theorem exists_original_filtered_prime_integral_precision_with_residual_multiplier_log_radius
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q cLog d A aLong : ℝ}
    (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1) (hcLog : 0 ≤ cLog) (hd : 0 < d)
    (haLong : 0 < aLong)
    (T : ℕ) (Tmod Sshift Cmod Sfreq : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, ∃ S₀ : ℝ, 0 ≤ S₀ ∧
      ∀ S : ℝ, S₀ ≤ S →
      ∀ᶠ L : ℝ in atTop,
      ∀ (r jStar : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (tmarks umarks : candidatePIndices c L → ℕ) (big : Finset (candidatePIndices c L))
        (b : GroupMarkedLists (fun g : big => candidatePBand (c*L) g.val.val)
          (fun g : big => umarks g.val) → ℂ) (κ ρ : ℕ → ℂ),
      (∀ g, tmarks g ≤ T) → (∀ l, ‖b l‖ ≤ L^B) → (∀ n, ‖κ n‖ ≤ 1) → (∀ n, ‖ρ n‖ ≤ 1) →
      ∀ (g : ℕ), g ∈ candidateSmallPIndices c L →
      ∀ (s : Finset ℕ) (Y P R : ℝ), s ⊆ candidatePBand (c*L) g → s.Nonempty →
      1 ≤ Y → d*L ≤ Real.log Y → Real.log Y ≤ cLog*L →
      0 ≤ R → R ≤ Y →
      (∀ p ∈ s, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*P) →
      ∀ (qP qT : ℕ) (χP : DirichletCharacter ℂ qP) (χT : DirichletCharacter ℂ qT)
        (τP τT : ℝ) (lo hi : ℕ) (F : Finset ℕ) (UM UT : ℝ),
      0 < UM → 1 ≤ UT →
      (∀ n ∈ Ioc lo hi, UM ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UM) →
      (∀ n ∈ F, UT ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UT) →
      ∀ (κM ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      0 ≤ κM → κM ≤ 1/50 → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (UQ Alo Blo σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      Real.exp (aLong*L) ≤ UQ → UQ ≤ Alo → Alo ≤ Blo → Blo ≤ 2*UQ →
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      R ≤ UQ*UM*UT/2 → Y^(3/5 : ℝ) ≤ UM*UT/2 → Real.log (8*(UQ*UM*UT)) ≤ cLog*L →
      (∫ u in Set.Icc (-R) R,
        ‖(∑ p ∈ s, (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
            (χP (p : ZMod qP)*typeIIPhase τP p)*harmonicMellinWeight u p) *
          (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
            typeIIPhase σ n*χQ (n : ZMod qQ)*harmonicMellinWeight u n)*
          (∑ n ∈ (Ioc lo hi).filter (fun n =>
              (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ) ≠ 0),
            (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ)*
              χM (n : ZMod qM)*typeIIPhase ν n*harmonicMellinWeight u n)*
          (∑ n ∈ F, candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
            tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n*ρ n) n*
              harmonicMellinWeight u n)‖^2) ≤ L^(-A) := by
  obtain ⟨C,hC,hres⟩ := exists_candidate_selected_residual_power_bound hc hq0 hq1 T
  obtain ⟨Bcoeff,hBcoeff,hsmall⟩ := exists_candidate_small_prime_factor_data hc
  refine ⟨C,hC,?_⟩
  intro B
  let X := max 0 ((A+2*(C+B)+23)/2)
  have hAs0 : 0 ≤ X := le_max_left _ _
  have hX : (A+2*(C+B)+23)/2 ≤ X := le_max_right _ _
  have hAs : A+2*(C+B)+21 ≤ 2*X := by linarith
  have hH : A+2*(C+B)+23 ≤ 2*X := by linarith
  obtain ⟨B0,hB0,hmain⟩ := exists_ambient_prime_four_factor_integral_decay_log_radius
    (a := (1/10 : ℝ)) (beta := (1/5 : ℝ)) (Et := C+B) hZ
    (by norm_num) (by norm_num) (by norm_num) hcLog hd hBcoeff hAs0 haLong
    hAs hH Tmod Sshift Cmod Sfreq
  let Bsave := (A+B0+2*(C+B)+7)/2
  have hsave : A+B0+2*(C+B)+7 ≤ 2*Bsave := by dsimp [Bsave]; linarith
  refine ⟨max 0 (max (max B0 Sfreq) Cmod+Bsave+5), le_max_left _ _, ?_⟩
  intro S hS0
  have hS : 0 ≤ S := (le_max_left _ _).trans hS0
  have hprecision : max (max B0 Sfreq) Cmod+Bsave+5 ≤ S := (le_max_right _ _).trans hS0
  filter_upwards [hmain Bsave hsave S hS hprecision,hres,hsmall,eventually_gt_atTop (0 : ℝ)]
    with L hdecay hresL hsmallL hL
  intro r jStar hr hj take hkeep ξ tmarks umarks big b κ ρ ht hb hκ hρ g hg s Y P R hs hne
    hY hYlo hYhi hR hRY hsp qP qT χP χT τP τT lo hi F UM UT hUM hUT hMband hFband
    κM ν qM hqMInst χM hκM hκmax hqM hν UQ Alo Blo σ qQ hqQInst χQ hUQ hQA hAB hBQ hqQ hσ
    hmeanScale hresScale hlog
  obtain ⟨hsprime,hPlo,hPhi,hcoeff⟩ := hsmallL g hg s P hs hne hsp
  have hT := hresL B r jStar hr hj take hkeep ξ tmarks umarks big b κ
    (fun n => χT (n : ZMod qT)*typeIIPhase τT n*ρ n) ht hb hκ
    (fun n => by
      rw [norm_mul]
      exact (mul_le_mul (character_typeIIPhase_norm_le χT τT n) (hρ n)
        (norm_nonneg _) zero_le_one).trans_eq (mul_one 1))
  have hbound := hdecay s hsprime
    (fun p => (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
      (χP (p.val : ZMod qP)*typeIIPhase τP p.val))
    Y P R hY hYlo hYhi hPlo hPhi hR hRY hsp
    (hcoeff (fun n => χP (n : ZMod qP)*typeIIPhase τP n)
      (fun n _ => character_typeIIPhase_norm_le χP τP n))
    lo hi F (candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
      tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n*ρ n))
    UM UT (L^(C+B)) hUM hUT (Real.rpow_nonneg hL.le _) le_rfl
    (fun n _ => hT n) hMband hFband
    κM ν qM χM hκM hκmax hqM hν UQ Alo Blo σ qQ χQ hUQ hQA hAB hBQ hqQ hσ
    hmeanScale hresScale hlog
  have hQeq (u : ℝ) :
      (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
        typeIIPhase σ n*χQ (n : ZMod qQ)*harmonicMellinWeight u n) =
      ∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
        harmonicMellinWeight (u+σ) n*χQ (n : ZMod qQ) := by
    apply sum_congr rfl
    intro n _
    rw [mul_right_comm,typeIIPhase_harmonic_mellin_shift]
  have hMeq (u : ℝ) :
      (∑ n ∈ Ioc lo hi, (ambientPrimeTypeIIAlpha κM L S n : ℂ)*
        χM (n : ZMod qM)*typeIIPhase ν n*harmonicMellinWeight u n) =
      ∑ n ∈ Ioc lo hi, ambientPrimeMellinCoefficient κM L S ν χM n*harmonicMellinWeight u n := by
    apply sum_congr rfl
    intro n hn
    rw [ambient_prime_original_phase_coefficient κM L S ν χM
      ((Nat.zero_le lo).trans_lt (mem_Ioc.mp hn).1)]
  have hPeq (u : ℝ) := prime_reciprocal_polynomial_eq_harmonic_sum s
    (fun n : ℕ => (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
      (χP (n : ZMod qP)*typeIIPhase τP n)) u
  simpa only [typeIIRestrict_nonzero_phase_mellin_sum,hPeq,hQeq,hMeq] using hbound

theorem exists_original_filtered_rough_integral_precision_with_residual_multiplier_log_radius
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q cLog d A aLong γrough vMax : ℝ}
    (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1) (hcLog : 0 ≤ cLog) (hd : 0 < d)
    (haLong : 0 < aLong)
    (hγ : 0 < γrough) (hv : vMax < 1)
    (T : ℕ) (Tmod Sshift Cmod Sfreq : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, ∃ S₀ : ℝ, 0 ≤ S₀ ∧
      ∀ S : ℝ, S₀ ≤ S →
      ∀ᶠ L : ℝ in atTop,
      ∀ (r jStar : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (tmarks umarks : candidatePIndices c L → ℕ) (big : Finset (candidatePIndices c L))
        (b : GroupMarkedLists (fun g : big => candidatePBand (c*L) g.val.val)
          (fun g : big => umarks g.val) → ℂ) (κ ρ : ℕ → ℂ),
      (∀ g, tmarks g ≤ T) → (∀ l, ‖b l‖ ≤ L^B) → (∀ n, ‖κ n‖ ≤ 1) → (∀ n, ‖ρ n‖ ≤ 1) →
      ∀ (g : ℕ), g ∈ candidateSmallPIndices c L →
      ∀ (s : Finset ℕ) (Y P R : ℝ), s ⊆ candidatePBand (c*L) g → s.Nonempty →
      1 ≤ Y → d*L ≤ Real.log Y → Real.log Y ≤ cLog*L →
      0 ≤ R → R ≤ Y →
      (∀ p ∈ s, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*P) →
      ∀ (qP qT : ℕ) (χP : DirichletCharacter ℂ qP) (χT : DirichletCharacter ℂ qT)
        (τP τT : ℝ) (lo hi : ℕ) (F : Finset ℕ) (UM UT : ℝ),
      0 < UM → 1 ≤ UT →
      (∀ n ∈ Ioc lo hi, UM ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UM) →
      (∀ n ∈ F, UT ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UT) →
      ∀ (aM v ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      v ≤ vMax → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (UQ Alo Blo σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      Real.exp (aLong*L) ≤ UQ → UQ ≤ Alo → Alo ≤ Blo → Blo ≤ 2*UQ →
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      R ≤ UQ*UM*UT/2 → Y^(3/5 : ℝ) ≤ UM*UT/2 → Real.log (8*(UQ*UM*UT)) ≤ cLog*L →
      (∫ u in Set.Icc (-R) R,
        ‖(∑ p ∈ s, (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
            (χP (p : ZMod qP)*typeIIPhase τP p)*harmonicMellinWeight u p) *
          (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
            typeIIPhase σ n*χQ (n : ZMod qQ)*harmonicMellinWeight u n)*
          (∑ n ∈ (Ioc lo hi).filter (fun n =>
              (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ) ≠ 0),
            (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ)*
              χM (n : ZMod qM)*typeIIPhase ν n*harmonicMellinWeight u n)*
          (∑ n ∈ F, candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
            tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n*ρ n) n*
              harmonicMellinWeight u n)‖^2) ≤ L^(-A) := by
  obtain ⟨C,hC,hres⟩ := exists_candidate_selected_residual_power_bound hc hq0 hq1 T
  obtain ⟨Bcoeff,hBcoeff,hsmall⟩ := exists_candidate_small_prime_factor_data hc
  refine ⟨C,hC,?_⟩
  intro B
  let X := max 0 ((A+2*(C+B)+23)/2)
  have hAs0 : 0 ≤ X := le_max_left _ _
  have hX : (A+2*(C+B)+23)/2 ≤ X := le_max_right _ _
  have hAs : A+2*(C+B)+21 ≤ 2*X := by linarith
  have hH : A+2*(C+B)+23 ≤ 2*X := by linarith
  obtain ⟨B0,hB0,hmain⟩ := exists_ambient_rough_four_factor_integral_decay_log_radius
    (a := (1/10 : ℝ)) (beta := (1/5 : ℝ)) (Et := C+B) hZ
    (by norm_num) (by norm_num) (by norm_num) hcLog hd hBcoeff hAs0 haLong hγ hv
    hAs hH Tmod Sshift Cmod Sfreq
  let Bsave := (A+B0+2*(C+B)+7)/2
  have hsave : A+B0+2*(C+B)+7 ≤ 2*Bsave := by dsimp [Bsave]; linarith
  refine ⟨max 0 (max (max B0 Sfreq) Cmod+Bsave+5), le_max_left _ _, ?_⟩
  intro S hS0
  have hS : 0 ≤ S := (le_max_left _ _).trans hS0
  have hprecision : max (max B0 Sfreq) Cmod+Bsave+5 ≤ S := (le_max_right _ _).trans hS0
  filter_upwards [hmain Bsave hsave S hS hprecision,hres,hsmall,eventually_gt_atTop (0 : ℝ)]
    with L hdecay hresL hsmallL hL
  intro r jStar hr hj take hkeep ξ tmarks umarks big b κ ρ ht hb hκ hρ g hg s Y P R hs hne
    hY hYlo hYhi hR hRY hsp qP qT χP χT τP τT lo hi F UM UT hUM hUT hMband hFband
    aM v ν qM hqMInst χM hvM hqM hν UQ Alo Blo σ qQ hqQInst χQ hUQ hQA hAB hBQ hqQ hσ
    hmeanScale hresScale hlog
  obtain ⟨hsprime,hPlo,hPhi,hcoeff⟩ := hsmallL g hg s P hs hne hsp
  have hT := hresL B r jStar hr hj take hkeep ξ tmarks umarks big b κ
    (fun n => χT (n : ZMod qT)*typeIIPhase τT n*ρ n) ht hb hκ
    (fun n => by
      rw [norm_mul]
      exact (mul_le_mul (character_typeIIPhase_norm_le χT τT n) (hρ n)
        (norm_nonneg _) zero_le_one).trans_eq (mul_one 1))
  have hbound := hdecay s hsprime
    (fun p => (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
      (χP (p.val : ZMod qP)*typeIIPhase τP p.val))
    Y P R hY hYlo hYhi hPlo hPhi hR hRY hsp
    (hcoeff (fun n => χP (n : ZMod qP)*typeIIPhase τP n)
      (fun n _ => character_typeIIPhase_norm_le χP τP n))
    lo hi F (candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
      tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n*ρ n))
    UM UT (L^(C+B)) hUM hUT (Real.rpow_nonneg hL.le _) le_rfl
    (fun n _ => hT n) hMband hFband
    aM v ν qM χM hvM hqM hν UQ Alo Blo σ qQ χQ hUQ hQA hAB hBQ hqQ hσ
    hmeanScale hresScale hlog
  have hQeq (u : ℝ) :
      (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
        typeIIPhase σ n*χQ (n : ZMod qQ)*harmonicMellinWeight u n) =
      ∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
        harmonicMellinWeight (u+σ) n*χQ (n : ZMod qQ) := by
    apply sum_congr rfl
    intro n _
    rw [mul_right_comm,typeIIPhase_harmonic_mellin_shift]
  have hMeq (u : ℝ) :
      (∑ n ∈ Ioc lo hi, (ambientRoughIntervalTypeIIAlpha γrough L S aM v n : ℂ)*
        χM (n : ZMod qM)*typeIIPhase ν n*harmonicMellinWeight u n) =
      ∑ n ∈ Ioc lo hi, ambientRoughMellinCoefficient γrough L S aM v ν χM n*harmonicMellinWeight u n := by
    apply sum_congr rfl
    intro n hn
    rw [ambient_rough_original_phase_coefficient γrough L S aM v ν χM
      ((Nat.zero_le lo).trans_lt (mem_Ioc.mp hn).1)]
  have hPeq (u : ℝ) := prime_reciprocal_polynomial_eq_harmonic_sum s
    (fun n : ℕ => (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
      (χP (n : ZMod qP)*typeIIPhase τP n)) u
  simpa only [typeIIRestrict_nonzero_phase_mellin_sum,hPeq,hQeq,hMeq] using hbound

theorem exists_rational_filtered_prime_integral_precision
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q cLog d A aLong : ℝ}
    (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1) (hcLog : 0 ≤ cLog) (hd : 0 < d)
    (haLong : 0 < aLong)
    (T : ℕ) (Tmod Sshift Cmod Sfreq Rmod : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, ∃ S₀ : ℝ, 0 ≤ S₀ ∧
      ∀ S : ℝ, S₀ ≤ S →
      ∀ᶠ L : ℝ in atTop,
      ∀ (r jStar : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (tmarks umarks : candidatePIndices c L → ℕ) (big : Finset (candidatePIndices c L))
        (b : GroupMarkedLists (fun g : big => candidatePBand (c*L) g.val.val)
          (fun g : big => umarks g.val) → ℂ) (κ : ℕ → ℂ),
      (∀ g, tmarks g ≤ T) → (∀ l, ‖b l‖ ≤ L^B) → (∀ n, ‖κ n‖ ≤ 1) →
      ∀ (g : ℕ), g ∈ candidateSmallPIndices c L →
      ∀ (s : Finset ℕ) (Y P R : ℝ), s ⊆ candidatePBand (c*L) g → s.Nonempty →
      1 ≤ Y → d*L ≤ Real.log Y → Real.log Y ≤ cLog*L →
      0 ≤ R → R ≤ Y → R ≤ Real.exp L →
      (∀ p ∈ s, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*P) →
      ∀ (qP qT : ℕ) (χP : DirichletCharacter ℂ qP) (χT : DirichletCharacter ℂ qT)
        (τP τT : ℝ) (lo hi : ℕ) (F : Finset ℕ) (UM UT : ℝ),
      0 < UM → 1 ≤ UT →
      (∀ n ∈ Ioc lo hi, UM ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UM) →
      (∀ n ∈ F, UT ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UT) →
      ∀ (κM ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      0 ≤ κM → κM ≤ 1/50 → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (UQ Alo Blo σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      Real.exp (aLong*L) ≤ UQ → UQ ≤ Alo → Alo ≤ Blo → Blo ≤ 2*UQ →
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      R ≤ UQ*UM*UT/2 → Y^(3/5 : ℝ) ≤ UM*UT/2 → Real.log (8*(UQ*UM*UT)) ≤ cLog*L →
      ∀ (qRat dRat : ℕ), 0 < qRat → 0 < dRat → dRat ∣ qRat →
      (qRat : ℝ) ≤ L^Rmod →
      ∀ ψ : AddChar (Additive (ZMod (qRat/dRat))ˣ) ℂ,
      (∫ u in Set.Icc (-R) R,
        ‖(∑ p ∈ s, (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
            (rationalProductCharacter qRat dRat χP ψ (p : ZMod (qP*(qRat/dRat)))*typeIIPhase τP p)*harmonicMellinWeight u p) *
          (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
            typeIIPhase σ n*rationalProductCharacter qRat dRat χQ ψ (n : ZMod (qQ*(qRat/dRat)))*harmonicMellinWeight u n)*
          (∑ n ∈ (Ioc lo hi).filter (fun n =>
              (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ) ≠ 0),
            (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ)*
              rationalProductCharacter qRat dRat χM ψ (n : ZMod (qM*(qRat/dRat)))*typeIIPhase ν n*harmonicMellinWeight u n)*
          (∑ n ∈ F, candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
            tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n*rationalResidualGcdMultiplier qRat dRat ψ n) n*
              harmonicMellinWeight u n)‖^2) ≤ L^(-A) := by
  obtain ⟨C,hC,hmain⟩ := exists_original_filtered_prime_integral_precision_with_residual_multiplier
    (A := A) hZ hc hq0 hq1 hcLog hd haLong T (Tmod+Rmod) Sshift (Cmod+Rmod) Sfreq
  refine ⟨C,hC,?_⟩
  intro B
  obtain ⟨S₀,hS₀,hbound⟩ := hmain B
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [hbound S hS,eventually_gt_atTop (0 : ℝ)] with L hdecay hL
  intro r jStar hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ g hg s Y P R hs hne
    hY hYlo hYhi hR hRY hRX hsp qP qT χP χT τP τT lo hi F UM UT hUM hUT hMband hFband
    κM ν qM hqMInst χM hκM hκmax hqM hν UQ Alo Blo σ qQ hqQInst χQ hUQ hQA hAB hBQ hqQ hσ
    hmeanScale hresScale hlog qRat dRat hqRat0 hdRat hdvd hqRat ψ
  have hquot : 0 < qRat/dRat := Nat.div_pos (Nat.le_of_dvd hqRat0 hdvd) hdRat
  exact @hdecay r jStar hr hj take hkeep ξ tmarks umarks big b κ
    (rationalResidualGcdMultiplier qRat dRat ψ) ht hb hκ
    (rational_residual_gcd_multiplier_norm_le qRat dRat ψ) g hg s Y P R hs hne
    hY hYlo hYhi hR hRY hRX hsp (qP*(qRat/dRat)) qT
    (rationalProductCharacter qRat dRat χP ψ) χT τP τT lo hi F UM UT hUM hUT hMband hFband
    κM ν (qM*(qRat/dRat)) ⟨mul_ne_zero (NeZero.ne qM) hquot.ne'⟩
    (rationalProductCharacter qRat dRat χM ψ) hκM hκmax
    (rational_product_modulus_power_bound hL hqM hqRat) hν UQ Alo Blo σ (qQ*(qRat/dRat)) ⟨mul_ne_zero (NeZero.ne qQ) hquot.ne'⟩
    (rationalProductCharacter qRat dRat χQ ψ) hUQ hQA hAB hBQ
    (rational_product_modulus_power_bound hL hqQ hqRat) hσ hmeanScale hresScale hlog

theorem exists_rational_filtered_rough_integral_precision
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q cLog d A aLong γrough vMax : ℝ}
    (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1) (hcLog : 0 ≤ cLog) (hd : 0 < d)
    (haLong : 0 < aLong)
    (hγ : 0 < γrough) (hv : vMax < 1)
    (T : ℕ) (Tmod Sshift Cmod Sfreq Rmod : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, ∃ S₀ : ℝ, 0 ≤ S₀ ∧
      ∀ S : ℝ, S₀ ≤ S →
      ∀ᶠ L : ℝ in atTop,
      ∀ (r jStar : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (tmarks umarks : candidatePIndices c L → ℕ) (big : Finset (candidatePIndices c L))
        (b : GroupMarkedLists (fun g : big => candidatePBand (c*L) g.val.val)
          (fun g : big => umarks g.val) → ℂ) (κ : ℕ → ℂ),
      (∀ g, tmarks g ≤ T) → (∀ l, ‖b l‖ ≤ L^B) → (∀ n, ‖κ n‖ ≤ 1) →
      ∀ (g : ℕ), g ∈ candidateSmallPIndices c L →
      ∀ (s : Finset ℕ) (Y P R : ℝ), s ⊆ candidatePBand (c*L) g → s.Nonempty →
      1 ≤ Y → d*L ≤ Real.log Y → Real.log Y ≤ cLog*L →
      0 ≤ R → R ≤ Y → R ≤ Real.exp L →
      (∀ p ∈ s, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*P) →
      ∀ (qP qT : ℕ) (χP : DirichletCharacter ℂ qP) (χT : DirichletCharacter ℂ qT)
        (τP τT : ℝ) (lo hi : ℕ) (F : Finset ℕ) (UM UT : ℝ),
      0 < UM → 1 ≤ UT →
      (∀ n ∈ Ioc lo hi, UM ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UM) →
      (∀ n ∈ F, UT ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UT) →
      ∀ (aM v ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      v ≤ vMax → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (UQ Alo Blo σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      Real.exp (aLong*L) ≤ UQ → UQ ≤ Alo → Alo ≤ Blo → Blo ≤ 2*UQ →
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      R ≤ UQ*UM*UT/2 → Y^(3/5 : ℝ) ≤ UM*UT/2 → Real.log (8*(UQ*UM*UT)) ≤ cLog*L →
      ∀ (qRat dRat : ℕ), 0 < qRat → 0 < dRat → dRat ∣ qRat →
      (qRat : ℝ) ≤ L^Rmod →
      ∀ ψ : AddChar (Additive (ZMod (qRat/dRat))ˣ) ℂ,
      (∫ u in Set.Icc (-R) R,
        ‖(∑ p ∈ s, (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
            (rationalProductCharacter qRat dRat χP ψ (p : ZMod (qP*(qRat/dRat)))*typeIIPhase τP p)*harmonicMellinWeight u p) *
          (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
            typeIIPhase σ n*rationalProductCharacter qRat dRat χQ ψ (n : ZMod (qQ*(qRat/dRat)))*harmonicMellinWeight u n)*
          (∑ n ∈ (Ioc lo hi).filter (fun n =>
              (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ) ≠ 0),
            (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ)*
              rationalProductCharacter qRat dRat χM ψ (n : ZMod (qM*(qRat/dRat)))*typeIIPhase ν n*harmonicMellinWeight u n)*
          (∑ n ∈ F, candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
            tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n*rationalResidualGcdMultiplier qRat dRat ψ n) n*
              harmonicMellinWeight u n)‖^2) ≤ L^(-A) := by
  obtain ⟨C,hC,hmain⟩ := exists_original_filtered_rough_integral_precision_with_residual_multiplier
    (A := A) hZ hc hq0 hq1 hcLog hd haLong hγ hv T (Tmod+Rmod) Sshift (Cmod+Rmod) Sfreq
  refine ⟨C,hC,?_⟩
  intro B
  obtain ⟨S₀,hS₀,hbound⟩ := hmain B
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [hbound S hS,eventually_gt_atTop (0 : ℝ)] with L hdecay hL
  intro r jStar hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ g hg s Y P R hs hne
    hY hYlo hYhi hR hRY hRX hsp qP qT χP χT τP τT lo hi F UM UT hUM hUT hMband hFband
    aM v ν qM hqMInst χM hvM hqM hν UQ Alo Blo σ qQ hqQInst χQ hUQ hQA hAB hBQ hqQ hσ
    hmeanScale hresScale hlog qRat dRat hqRat0 hdRat hdvd hqRat ψ
  have hquot : 0 < qRat/dRat := Nat.div_pos (Nat.le_of_dvd hqRat0 hdvd) hdRat
  exact @hdecay r jStar hr hj take hkeep ξ tmarks umarks big b κ
    (rationalResidualGcdMultiplier qRat dRat ψ) ht hb hκ
    (rational_residual_gcd_multiplier_norm_le qRat dRat ψ) g hg s Y P R hs hne
    hY hYlo hYhi hR hRY hRX hsp (qP*(qRat/dRat)) qT
    (rationalProductCharacter qRat dRat χP ψ) χT τP τT lo hi F UM UT hUM hUT hMband hFband
    aM v ν (qM*(qRat/dRat)) ⟨mul_ne_zero (NeZero.ne qM) hquot.ne'⟩
    (rationalProductCharacter qRat dRat χM ψ) hvM
    (rational_product_modulus_power_bound hL hqM hqRat) hν UQ Alo Blo σ (qQ*(qRat/dRat)) ⟨mul_ne_zero (NeZero.ne qQ) hquot.ne'⟩
    (rationalProductCharacter qRat dRat χQ ψ) hUQ hQA hAB hBQ
    (rational_product_modulus_power_bound hL hqQ hqRat) hσ hmeanScale hresScale hlog

theorem exists_rational_filtered_prime_integral_precision_log_radius
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q cLog d A aLong : ℝ}
    (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1) (hcLog : 0 ≤ cLog) (hd : 0 < d)
    (haLong : 0 < aLong)
    (T : ℕ) (Tmod Sshift Cmod Sfreq Rmod : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, ∃ S₀ : ℝ, 0 ≤ S₀ ∧
      ∀ S : ℝ, S₀ ≤ S →
      ∀ᶠ L : ℝ in atTop,
      ∀ (r jStar : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (tmarks umarks : candidatePIndices c L → ℕ) (big : Finset (candidatePIndices c L))
        (b : GroupMarkedLists (fun g : big => candidatePBand (c*L) g.val.val)
          (fun g : big => umarks g.val) → ℂ) (κ : ℕ → ℂ),
      (∀ g, tmarks g ≤ T) → (∀ l, ‖b l‖ ≤ L^B) → (∀ n, ‖κ n‖ ≤ 1) →
      ∀ (g : ℕ), g ∈ candidateSmallPIndices c L →
      ∀ (s : Finset ℕ) (Y P R : ℝ), s ⊆ candidatePBand (c*L) g → s.Nonempty →
      1 ≤ Y → d*L ≤ Real.log Y → Real.log Y ≤ cLog*L →
      0 ≤ R → R ≤ Y →
      (∀ p ∈ s, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*P) →
      ∀ (qP qT : ℕ) (χP : DirichletCharacter ℂ qP) (χT : DirichletCharacter ℂ qT)
        (τP τT : ℝ) (lo hi : ℕ) (F : Finset ℕ) (UM UT : ℝ),
      0 < UM → 1 ≤ UT →
      (∀ n ∈ Ioc lo hi, UM ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UM) →
      (∀ n ∈ F, UT ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UT) →
      ∀ (κM ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      0 ≤ κM → κM ≤ 1/50 → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (UQ Alo Blo σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      Real.exp (aLong*L) ≤ UQ → UQ ≤ Alo → Alo ≤ Blo → Blo ≤ 2*UQ →
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      R ≤ UQ*UM*UT/2 → Y^(3/5 : ℝ) ≤ UM*UT/2 → Real.log (8*(UQ*UM*UT)) ≤ cLog*L →
      ∀ (qRat dRat : ℕ), 0 < qRat → 0 < dRat → dRat ∣ qRat →
      (qRat : ℝ) ≤ L^Rmod →
      ∀ ψ : AddChar (Additive (ZMod (qRat/dRat))ˣ) ℂ,
      (∫ u in Set.Icc (-R) R,
        ‖(∑ p ∈ s, (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
            (rationalProductCharacter qRat dRat χP ψ (p : ZMod (qP*(qRat/dRat)))*typeIIPhase τP p)*harmonicMellinWeight u p) *
          (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
            typeIIPhase σ n*rationalProductCharacter qRat dRat χQ ψ (n : ZMod (qQ*(qRat/dRat)))*harmonicMellinWeight u n)*
          (∑ n ∈ (Ioc lo hi).filter (fun n =>
              (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ) ≠ 0),
            (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ)*
              rationalProductCharacter qRat dRat χM ψ (n : ZMod (qM*(qRat/dRat)))*typeIIPhase ν n*harmonicMellinWeight u n)*
          (∑ n ∈ F, candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
            tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n*rationalResidualGcdMultiplier qRat dRat ψ n) n*
              harmonicMellinWeight u n)‖^2) ≤ L^(-A) := by
  obtain ⟨C,hC,hmain⟩ := exists_original_filtered_prime_integral_precision_with_residual_multiplier_log_radius
    (A := A) hZ hc hq0 hq1 hcLog hd haLong T (Tmod+Rmod) Sshift (Cmod+Rmod) Sfreq
  refine ⟨C,hC,?_⟩
  intro B
  obtain ⟨S₀,hS₀,hbound⟩ := hmain B
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [hbound S hS,eventually_gt_atTop (0 : ℝ)] with L hdecay hL
  intro r jStar hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ g hg s Y P R hs hne
    hY hYlo hYhi hR hRY hsp qP qT χP χT τP τT lo hi F UM UT hUM hUT hMband hFband
    κM ν qM hqMInst χM hκM hκmax hqM hν UQ Alo Blo σ qQ hqQInst χQ hUQ hQA hAB hBQ hqQ hσ
    hmeanScale hresScale hlog qRat dRat hqRat0 hdRat hdvd hqRat ψ
  have hquot : 0 < qRat/dRat := Nat.div_pos (Nat.le_of_dvd hqRat0 hdvd) hdRat
  exact @hdecay r jStar hr hj take hkeep ξ tmarks umarks big b κ
    (rationalResidualGcdMultiplier qRat dRat ψ) ht hb hκ
    (rational_residual_gcd_multiplier_norm_le qRat dRat ψ) g hg s Y P R hs hne
    hY hYlo hYhi hR hRY hsp (qP*(qRat/dRat)) qT
    (rationalProductCharacter qRat dRat χP ψ) χT τP τT lo hi F UM UT hUM hUT hMband hFband
    κM ν (qM*(qRat/dRat)) ⟨mul_ne_zero (NeZero.ne qM) hquot.ne'⟩
    (rationalProductCharacter qRat dRat χM ψ) hκM hκmax
    (rational_product_modulus_power_bound hL hqM hqRat) hν UQ Alo Blo σ (qQ*(qRat/dRat)) ⟨mul_ne_zero (NeZero.ne qQ) hquot.ne'⟩
    (rationalProductCharacter qRat dRat χQ ψ) hUQ hQA hAB hBQ
    (rational_product_modulus_power_bound hL hqQ hqRat) hσ hmeanScale hresScale hlog

theorem exists_rational_filtered_rough_integral_precision_log_radius
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q cLog d A aLong γrough vMax : ℝ}
    (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1) (hcLog : 0 ≤ cLog) (hd : 0 < d)
    (haLong : 0 < aLong)
    (hγ : 0 < γrough) (hv : vMax < 1)
    (T : ℕ) (Tmod Sshift Cmod Sfreq Rmod : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, ∃ S₀ : ℝ, 0 ≤ S₀ ∧
      ∀ S : ℝ, S₀ ≤ S →
      ∀ᶠ L : ℝ in atTop,
      ∀ (r jStar : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (tmarks umarks : candidatePIndices c L → ℕ) (big : Finset (candidatePIndices c L))
        (b : GroupMarkedLists (fun g : big => candidatePBand (c*L) g.val.val)
          (fun g : big => umarks g.val) → ℂ) (κ : ℕ → ℂ),
      (∀ g, tmarks g ≤ T) → (∀ l, ‖b l‖ ≤ L^B) → (∀ n, ‖κ n‖ ≤ 1) →
      ∀ (g : ℕ), g ∈ candidateSmallPIndices c L →
      ∀ (s : Finset ℕ) (Y P R : ℝ), s ⊆ candidatePBand (c*L) g → s.Nonempty →
      1 ≤ Y → d*L ≤ Real.log Y → Real.log Y ≤ cLog*L →
      0 ≤ R → R ≤ Y →
      (∀ p ∈ s, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*P) →
      ∀ (qP qT : ℕ) (χP : DirichletCharacter ℂ qP) (χT : DirichletCharacter ℂ qT)
        (τP τT : ℝ) (lo hi : ℕ) (F : Finset ℕ) (UM UT : ℝ),
      0 < UM → 1 ≤ UT →
      (∀ n ∈ Ioc lo hi, UM ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UM) →
      (∀ n ∈ F, UT ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UT) →
      ∀ (aM v ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      v ≤ vMax → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (UQ Alo Blo σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      Real.exp (aLong*L) ≤ UQ → UQ ≤ Alo → Alo ≤ Blo → Blo ≤ 2*UQ →
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      R ≤ UQ*UM*UT/2 → Y^(3/5 : ℝ) ≤ UM*UT/2 → Real.log (8*(UQ*UM*UT)) ≤ cLog*L →
      ∀ (qRat dRat : ℕ), 0 < qRat → 0 < dRat → dRat ∣ qRat →
      (qRat : ℝ) ≤ L^Rmod →
      ∀ ψ : AddChar (Additive (ZMod (qRat/dRat))ˣ) ℂ,
      (∫ u in Set.Icc (-R) R,
        ‖(∑ p ∈ s, (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
            (rationalProductCharacter qRat dRat χP ψ (p : ZMod (qP*(qRat/dRat)))*typeIIPhase τP p)*harmonicMellinWeight u p) *
          (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
            typeIIPhase σ n*rationalProductCharacter qRat dRat χQ ψ (n : ZMod (qQ*(qRat/dRat)))*harmonicMellinWeight u n)*
          (∑ n ∈ (Ioc lo hi).filter (fun n =>
              (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ) ≠ 0),
            (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ)*
              rationalProductCharacter qRat dRat χM ψ (n : ZMod (qM*(qRat/dRat)))*typeIIPhase ν n*harmonicMellinWeight u n)*
          (∑ n ∈ F, candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
            tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n*rationalResidualGcdMultiplier qRat dRat ψ n) n*
              harmonicMellinWeight u n)‖^2) ≤ L^(-A) := by
  obtain ⟨C,hC,hmain⟩ := exists_original_filtered_rough_integral_precision_with_residual_multiplier_log_radius
    (A := A) hZ hc hq0 hq1 hcLog hd haLong hγ hv T (Tmod+Rmod) Sshift (Cmod+Rmod) Sfreq
  refine ⟨C,hC,?_⟩
  intro B
  obtain ⟨S₀,hS₀,hbound⟩ := hmain B
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [hbound S hS,eventually_gt_atTop (0 : ℝ)] with L hdecay hL
  intro r jStar hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ g hg s Y P R hs hne
    hY hYlo hYhi hR hRY hsp qP qT χP χT τP τT lo hi F UM UT hUM hUT hMband hFband
    aM v ν qM hqMInst χM hvM hqM hν UQ Alo Blo σ qQ hqQInst χQ hUQ hQA hAB hBQ hqQ hσ
    hmeanScale hresScale hlog qRat dRat hqRat0 hdRat hdvd hqRat ψ
  have hquot : 0 < qRat/dRat := Nat.div_pos (Nat.le_of_dvd hqRat0 hdvd) hdRat
  exact @hdecay r jStar hr hj take hkeep ξ tmarks umarks big b κ
    (rationalResidualGcdMultiplier qRat dRat ψ) ht hb hκ
    (rational_residual_gcd_multiplier_norm_le qRat dRat ψ) g hg s Y P R hs hne
    hY hYlo hYhi hR hRY hsp (qP*(qRat/dRat)) qT
    (rationalProductCharacter qRat dRat χP ψ) χT τP τT lo hi F UM UT hUM hUT hMband hFband
    aM v ν (qM*(qRat/dRat)) ⟨mul_ne_zero (NeZero.ne qM) hquot.ne'⟩
    (rationalProductCharacter qRat dRat χM ψ) hvM
    (rational_product_modulus_power_bound hL hqM hqRat) hν UQ Alo Blo σ (qQ*(qRat/dRat)) ⟨mul_ne_zero (NeZero.ne qQ) hquot.ne'⟩
    (rationalProductCharacter qRat dRat χQ ψ) hUQ hQA hAB hBQ
    (rational_product_modulus_power_bound hL hqQ hqRat) hσ hmeanScale hresScale hlog

theorem exists_rational_shifted_filtered_prime_integral_precision
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q cLog d A aLong : ℝ}
    (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1) (hcLog : 0 ≤ cLog) (hd : 0 < d)
    (haLong : 0 < aLong)
    (T : ℕ) (Tmod Sshift Cmod Sfreq Rmod W : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, ∃ S₀ : ℝ, 0 ≤ S₀ ∧
      ∀ S : ℝ, S₀ ≤ S →
      ∀ᶠ L : ℝ in atTop,
      ∀ (r jStar : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (tmarks umarks : candidatePIndices c L → ℕ) (big : Finset (candidatePIndices c L))
        (b : GroupMarkedLists (fun g : big => candidatePBand (c*L) g.val.val)
          (fun g : big => umarks g.val) → ℂ) (κ : ℕ → ℂ),
      (∀ g, tmarks g ≤ T) → (∀ l, ‖b l‖ ≤ L^B) → (∀ n, ‖κ n‖ ≤ 1) →
      ∀ (g : ℕ), g ∈ candidateSmallPIndices c L →
      ∀ (s : Finset ℕ) (Y P R : ℝ), s ⊆ candidatePBand (c*L) g → s.Nonempty →
      1 ≤ Y → d*L ≤ Real.log Y → Real.log Y ≤ cLog*L →
      0 ≤ R → R ≤ Y → R ≤ Real.exp L →
      (∀ p ∈ s, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*P) →
      ∀ (qP qT : ℕ) (χP : DirichletCharacter ℂ qP) (χT : DirichletCharacter ℂ qT)
        (τP τT : ℝ) (lo hi : ℕ) (F : Finset ℕ) (UM UT : ℝ),
      0 < UM → 1 ≤ UT →
      (∀ n ∈ Ioc lo hi, UM ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UM) →
      (∀ n ∈ F, UT ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UT) →
      ∀ (κM ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      0 ≤ κM → κM ≤ 1/50 → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (UQ Alo Blo σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      Real.exp (aLong*L) ≤ UQ → UQ ≤ Alo → Alo ≤ Blo → Blo ≤ 2*UQ →
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      R ≤ UQ*UM*UT/2 → Y^(3/5 : ℝ) ≤ UM*UT/2 → Real.log (8*(UQ*UM*UT)) ≤ cLog*L →
      ∀ (qRat dRat : ℕ), 0 < qRat → 0 < dRat → dRat ∣ qRat →
      (qRat : ℝ) ≤ L^Rmod →
      ∀ ψ : AddChar (Additive (ZMod (qRat/dRat))ˣ) ℂ,
      ∀ w : ℝ, |w| ≤ L^W →
      (∫ u in Set.Icc (-R) R,
        ‖(∑ p ∈ s, (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
            (rationalProductCharacter qRat dRat χP ψ (p : ZMod (qP*(qRat/dRat)))*typeIIPhase τP p)*harmonicMellinWeight (u+w) p) *
          (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
            typeIIPhase σ n*rationalProductCharacter qRat dRat χQ ψ (n : ZMod (qQ*(qRat/dRat)))*harmonicMellinWeight (u+w) n)*
          (∑ n ∈ (Ioc lo hi).filter (fun n =>
              (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ) ≠ 0),
            (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ)*
              rationalProductCharacter qRat dRat χM ψ (n : ZMod (qM*(qRat/dRat)))*typeIIPhase ν n*harmonicMellinWeight (u+w) n)*
          (∑ n ∈ F, candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
            tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n*rationalResidualGcdMultiplier qRat dRat ψ n) n*
              harmonicMellinWeight (u+w) n)‖^2) ≤ L^(-A) := by
  obtain ⟨C,hC,hmain⟩ := exists_rational_filtered_prime_integral_precision
    (A := A) hZ hc hq0 hq1 hcLog hd haLong T Tmod (max Sshift W+1) Cmod
      (max Sfreq W+1) Rmod
  refine ⟨C,hC,?_⟩
  intro B
  obtain ⟨S₀,hS₀,hbound⟩ := hmain B
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [hbound S hS,eventually_add_frequency_power_bound Sfreq W,
    eventually_add_frequency_power_bound Sshift W] with L hdecay hfreq hshift
  intro r jStar hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ g hg s Y P R hs hne
    hY hYlo hYhi hR hRY hRX hsp qP qT χP χT τP τT lo hi F UM UT hUM hUT hMband hFband
    κM ν qM hqMInst χM hκM hκmax hqM hν UQ Alo Blo σ qQ hqQInst χQ hUQ hQA hAB hBQ hqQ hσ
    hmeanScale hresScale hlog qRat dRat hqRat0 hdRat hdvd hqRat ψ w hw
  have hresult := @hdecay r jStar hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ
    g hg s Y P R hs hne hY hYlo hYhi hR hRY hRX hsp qP qT χP χT (τP+w) (τT+w)
    lo hi F UM UT hUM hUT hMband hFband κM (ν+w) qM hqMInst χM hκM hκmax hqM
    (hfreq ν w hν hw) UQ Alo Blo (σ+w) qQ hqQInst χQ hUQ hQA hAB hBQ hqQ
    (hshift σ w hσ hw) hmeanScale hresScale hlog qRat dRat hqRat0 hdRat hdvd hqRat ψ
  have hP (u : ℝ) :
      (∑ p ∈ s, (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
        (rationalProductCharacter qRat dRat χP ψ (p : ZMod (qP*(qRat/dRat)))*
          typeIIPhase (τP+w) p)*harmonicMellinWeight u p) =
      ∑ p ∈ s, (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
        (rationalProductCharacter qRat dRat χP ψ (p : ZMod (qP*(qRat/dRat)))*
          typeIIPhase τP p)*harmonicMellinWeight (u+w) p := by
    apply sum_congr rfl
    intro p _
    simpa only [mul_assoc,mul_one] using rational_phase_harmonic_common_shift
      ((1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
        rationalProductCharacter qRat dRat χP ψ (p : ZMod (qP*(qRat/dRat)))) 1 τP u w p
  have hQ (u : ℝ) :
      (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
        typeIIPhase (σ+w) n*rationalProductCharacter qRat dRat χQ ψ
          (n : ZMod (qQ*(qRat/dRat)))*harmonicMellinWeight u n) =
      ∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
        typeIIPhase σ n*rationalProductCharacter qRat dRat χQ ψ
          (n : ZMod (qQ*(qRat/dRat)))*harmonicMellinWeight (u+w) n := by
    apply sum_congr rfl
    intro n _
    simpa only [one_mul] using rational_phase_harmonic_common_shift 1
      (rationalProductCharacter qRat dRat χQ ψ (n : ZMod (qQ*(qRat/dRat)))) σ u w n
  have hM (u : ℝ) :
      (∑ n ∈ (Ioc lo hi).filter (fun n =>
          (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ) ≠ 0),
        (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ)*
          rationalProductCharacter qRat dRat χM ψ (n : ZMod (qM*(qRat/dRat)))*
          typeIIPhase (ν+w) n*harmonicMellinWeight u n) =
      ∑ n ∈ (Ioc lo hi).filter (fun n =>
          (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ) ≠ 0),
        (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ)*
          rationalProductCharacter qRat dRat χM ψ (n : ZMod (qM*(qRat/dRat)))*
          typeIIPhase ν n*harmonicMellinWeight (u+w) n := by
    apply sum_congr rfl
    intro n _
    simpa only [mul_one] using rational_phase_harmonic_common_shift
      ((typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ)*
        rationalProductCharacter qRat dRat χM ψ (n : ZMod (qM*(qRat/dRat)))) 1 ν u w n
  have hT (u : ℝ) :
      (∑ n ∈ F, candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
        tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase (τT+w) n*
          rationalResidualGcdMultiplier qRat dRat ψ n) n*harmonicMellinWeight u n) =
      ∑ n ∈ F, candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
        tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n*
          rationalResidualGcdMultiplier qRat dRat ψ n) n*harmonicMellinWeight (u+w) n := by
    apply sum_congr rfl
    intro n _
    unfold candidateSelectedResidualCoefficient
    dsimp only
    rw [typeIIPhase_add, ← typeIIPhase_harmonic_mellin_shift w u n]
    ring
  simpa only [hP,hQ,hM,hT] using hresult

theorem exists_rational_shifted_filtered_rough_integral_precision
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q cLog d A aLong γrough vMax : ℝ}
    (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1) (hcLog : 0 ≤ cLog) (hd : 0 < d)
    (haLong : 0 < aLong)
    (hγ : 0 < γrough) (hv : vMax < 1)
    (T : ℕ) (Tmod Sshift Cmod Sfreq Rmod W : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, ∃ S₀ : ℝ, 0 ≤ S₀ ∧
      ∀ S : ℝ, S₀ ≤ S →
      ∀ᶠ L : ℝ in atTop,
      ∀ (r jStar : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (tmarks umarks : candidatePIndices c L → ℕ) (big : Finset (candidatePIndices c L))
        (b : GroupMarkedLists (fun g : big => candidatePBand (c*L) g.val.val)
          (fun g : big => umarks g.val) → ℂ) (κ : ℕ → ℂ),
      (∀ g, tmarks g ≤ T) → (∀ l, ‖b l‖ ≤ L^B) → (∀ n, ‖κ n‖ ≤ 1) →
      ∀ (g : ℕ), g ∈ candidateSmallPIndices c L →
      ∀ (s : Finset ℕ) (Y P R : ℝ), s ⊆ candidatePBand (c*L) g → s.Nonempty →
      1 ≤ Y → d*L ≤ Real.log Y → Real.log Y ≤ cLog*L →
      0 ≤ R → R ≤ Y → R ≤ Real.exp L →
      (∀ p ∈ s, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*P) →
      ∀ (qP qT : ℕ) (χP : DirichletCharacter ℂ qP) (χT : DirichletCharacter ℂ qT)
        (τP τT : ℝ) (lo hi : ℕ) (F : Finset ℕ) (UM UT : ℝ),
      0 < UM → 1 ≤ UT →
      (∀ n ∈ Ioc lo hi, UM ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UM) →
      (∀ n ∈ F, UT ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UT) →
      ∀ (aM v ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      v ≤ vMax → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (UQ Alo Blo σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      Real.exp (aLong*L) ≤ UQ → UQ ≤ Alo → Alo ≤ Blo → Blo ≤ 2*UQ →
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      R ≤ UQ*UM*UT/2 → Y^(3/5 : ℝ) ≤ UM*UT/2 → Real.log (8*(UQ*UM*UT)) ≤ cLog*L →
      ∀ (qRat dRat : ℕ), 0 < qRat → 0 < dRat → dRat ∣ qRat →
      (qRat : ℝ) ≤ L^Rmod →
      ∀ ψ : AddChar (Additive (ZMod (qRat/dRat))ˣ) ℂ,
      ∀ w : ℝ, |w| ≤ L^W →
      (∫ u in Set.Icc (-R) R,
        ‖(∑ p ∈ s, (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
            (rationalProductCharacter qRat dRat χP ψ (p : ZMod (qP*(qRat/dRat)))*typeIIPhase τP p)*harmonicMellinWeight (u+w) p) *
          (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
            typeIIPhase σ n*rationalProductCharacter qRat dRat χQ ψ (n : ZMod (qQ*(qRat/dRat)))*harmonicMellinWeight (u+w) n)*
          (∑ n ∈ (Ioc lo hi).filter (fun n =>
              (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ) ≠ 0),
            (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ)*
              rationalProductCharacter qRat dRat χM ψ (n : ZMod (qM*(qRat/dRat)))*typeIIPhase ν n*harmonicMellinWeight (u+w) n)*
          (∑ n ∈ F, candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
            tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n*rationalResidualGcdMultiplier qRat dRat ψ n) n*
              harmonicMellinWeight (u+w) n)‖^2) ≤ L^(-A) := by
  obtain ⟨C,hC,hmain⟩ := exists_rational_filtered_rough_integral_precision
    (A := A) hZ hc hq0 hq1 hcLog hd haLong hγ hv
    T Tmod (max Sshift W+1) Cmod (max Sfreq W+1) Rmod
  refine ⟨C,hC,?_⟩
  intro B
  obtain ⟨S₀,hS₀,hbound⟩ := hmain B
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [hbound S hS, eventually_add_frequency_power_bound Sshift W,
    eventually_add_frequency_power_bound Sfreq W] with L hdecay hshift hfreq
  intro r jStar hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ g hg s Y P R hs hne
    hY hYlo hYhi hR hRY hRX hsp qP qT χP χT τP τT lo hi F UM UT hUM hUT hMband hFband
    aM v ν qM hqMInst χM hvM hqM hν UQ Alo Blo σ qQ hqQInst χQ hUQ hQA hAB hBQ hqQ hσ
    hmeanScale hresScale hlog qRat dRat hqRat0 hdRat hdvd hqRat ψ w hw
  have hraw := @hdecay r jStar hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ
    g hg s Y P R hs hne hY hYlo hYhi hR hRY hRX hsp
    qP qT χP χT (τP+w) (τT+w) lo hi F UM UT hUM hUT hMband hFband
    aM v (ν+w) qM hqMInst χM hvM hqM (hfreq ν w hν hw)
    UQ Alo Blo (σ+w) qQ hqQInst χQ hUQ hQA hAB hBQ hqQ (hshift σ w hσ hw)
    hmeanScale hresScale hlog qRat dRat hqRat0 hdRat hdvd hqRat ψ
  have heP (u : ℝ) :
      (∑ p ∈ s, (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
        (rationalProductCharacter qRat dRat χP ψ (p : ZMod (qP*(qRat/dRat)))*typeIIPhase (τP+w) p)*
          harmonicMellinWeight u p) =
      ∑ p ∈ s, (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
        (rationalProductCharacter qRat dRat χP ψ (p : ZMod (qP*(qRat/dRat)))*typeIIPhase τP p)*
          harmonicMellinWeight (u+w) p := by
    apply sum_congr rfl
    intro p _
    simpa only [mul_one, mul_assoc] using rational_phase_harmonic_common_shift
      ((1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
        rationalProductCharacter qRat dRat χP ψ (p : ZMod (qP*(qRat/dRat)))) 1 τP u w p
  have heQ (u : ℝ) :
      (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
        typeIIPhase (σ+w) n*rationalProductCharacter qRat dRat χQ ψ (n : ZMod (qQ*(qRat/dRat)))*
          harmonicMellinWeight u n) =
      ∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
        typeIIPhase σ n*rationalProductCharacter qRat dRat χQ ψ (n : ZMod (qQ*(qRat/dRat)))*
          harmonicMellinWeight (u+w) n := by
    apply sum_congr rfl
    intro n _
    simpa only [one_mul] using rational_phase_harmonic_common_shift 1
      (rationalProductCharacter qRat dRat χQ ψ (n : ZMod (qQ*(qRat/dRat)))) σ u w n
  have heM (u : ℝ) :
      (∑ n ∈ (Ioc lo hi).filter (fun n =>
          (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ) ≠ 0),
        (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ)*
          rationalProductCharacter qRat dRat χM ψ (n : ZMod (qM*(qRat/dRat)))*typeIIPhase (ν+w) n*
            harmonicMellinWeight u n) =
      ∑ n ∈ (Ioc lo hi).filter (fun n =>
          (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ) ≠ 0),
        (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ)*
          rationalProductCharacter qRat dRat χM ψ (n : ZMod (qM*(qRat/dRat)))*typeIIPhase ν n*
            harmonicMellinWeight (u+w) n := by
    apply sum_congr rfl
    intro n _
    simpa only [mul_one] using rational_phase_harmonic_common_shift
      ((typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ)*
        rationalProductCharacter qRat dRat χM ψ (n : ZMod (qM*(qRat/dRat)))) 1 ν u w n
  have heT (u : ℝ) :
      (∑ n ∈ F, candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
        tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase (τT+w) n*
          rationalResidualGcdMultiplier qRat dRat ψ n) n*harmonicMellinWeight u n) =
      ∑ n ∈ F, candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
        tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n*
          rationalResidualGcdMultiplier qRat dRat ψ n) n*harmonicMellinWeight (u+w) n := by
    apply sum_congr rfl
    intro n _
    unfold candidateSelectedResidualCoefficient
    dsimp only
    rw [typeIIPhase_add, ← typeIIPhase_harmonic_mellin_shift w u n]
    ring
  simpa only [heP, heQ, heM, heT] using hraw

theorem exists_rational_shifted_filtered_prime_integral_precision_log_radius
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q cLog d A aLong : ℝ}
    (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1) (hcLog : 0 ≤ cLog) (hd : 0 < d)
    (haLong : 0 < aLong)
    (T : ℕ) (Tmod Sshift Cmod Sfreq Rmod W : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, ∃ S₀ : ℝ, 0 ≤ S₀ ∧
      ∀ S : ℝ, S₀ ≤ S →
      ∀ᶠ L : ℝ in atTop,
      ∀ (r jStar : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (tmarks umarks : candidatePIndices c L → ℕ) (big : Finset (candidatePIndices c L))
        (b : GroupMarkedLists (fun g : big => candidatePBand (c*L) g.val.val)
          (fun g : big => umarks g.val) → ℂ) (κ : ℕ → ℂ),
      (∀ g, tmarks g ≤ T) → (∀ l, ‖b l‖ ≤ L^B) → (∀ n, ‖κ n‖ ≤ 1) →
      ∀ (g : ℕ), g ∈ candidateSmallPIndices c L →
      ∀ (s : Finset ℕ) (Y P R : ℝ), s ⊆ candidatePBand (c*L) g → s.Nonempty →
      1 ≤ Y → d*L ≤ Real.log Y → Real.log Y ≤ cLog*L →
      0 ≤ R → R ≤ Y →
      (∀ p ∈ s, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*P) →
      ∀ (qP qT : ℕ) (χP : DirichletCharacter ℂ qP) (χT : DirichletCharacter ℂ qT)
        (τP τT : ℝ) (lo hi : ℕ) (F : Finset ℕ) (UM UT : ℝ),
      0 < UM → 1 ≤ UT →
      (∀ n ∈ Ioc lo hi, UM ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UM) →
      (∀ n ∈ F, UT ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UT) →
      ∀ (κM ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      0 ≤ κM → κM ≤ 1/50 → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (UQ Alo Blo σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      Real.exp (aLong*L) ≤ UQ → UQ ≤ Alo → Alo ≤ Blo → Blo ≤ 2*UQ →
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      R ≤ UQ*UM*UT/2 → Y^(3/5 : ℝ) ≤ UM*UT/2 → Real.log (8*(UQ*UM*UT)) ≤ cLog*L →
      ∀ (qRat dRat : ℕ), 0 < qRat → 0 < dRat → dRat ∣ qRat →
      (qRat : ℝ) ≤ L^Rmod →
      ∀ ψ : AddChar (Additive (ZMod (qRat/dRat))ˣ) ℂ,
      ∀ w : ℝ, |w| ≤ L^W →
      (∫ u in Set.Icc (-R) R,
        ‖(∑ p ∈ s, (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
            (rationalProductCharacter qRat dRat χP ψ (p : ZMod (qP*(qRat/dRat)))*typeIIPhase τP p)*harmonicMellinWeight (u+w) p) *
          (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
            typeIIPhase σ n*rationalProductCharacter qRat dRat χQ ψ (n : ZMod (qQ*(qRat/dRat)))*harmonicMellinWeight (u+w) n)*
          (∑ n ∈ (Ioc lo hi).filter (fun n =>
              (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ) ≠ 0),
            (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ)*
              rationalProductCharacter qRat dRat χM ψ (n : ZMod (qM*(qRat/dRat)))*typeIIPhase ν n*harmonicMellinWeight (u+w) n)*
          (∑ n ∈ F, candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
            tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n*rationalResidualGcdMultiplier qRat dRat ψ n) n*
              harmonicMellinWeight (u+w) n)‖^2) ≤ L^(-A) := by
  obtain ⟨C,hC,hmain⟩ := exists_rational_filtered_prime_integral_precision_log_radius
    (A := A) hZ hc hq0 hq1 hcLog hd haLong T Tmod (max Sshift W+1) Cmod
      (max Sfreq W+1) Rmod
  refine ⟨C,hC,?_⟩
  intro B
  obtain ⟨S₀,hS₀,hbound⟩ := hmain B
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [hbound S hS,eventually_add_frequency_power_bound Sfreq W,
    eventually_add_frequency_power_bound Sshift W] with L hdecay hfreq hshift
  intro r jStar hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ g hg s Y P R hs hne
    hY hYlo hYhi hR hRY hsp qP qT χP χT τP τT lo hi F UM UT hUM hUT hMband hFband
    κM ν qM hqMInst χM hκM hκmax hqM hν UQ Alo Blo σ qQ hqQInst χQ hUQ hQA hAB hBQ hqQ hσ
    hmeanScale hresScale hlog qRat dRat hqRat0 hdRat hdvd hqRat ψ w hw
  have hresult := @hdecay r jStar hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ
    g hg s Y P R hs hne hY hYlo hYhi hR hRY hsp qP qT χP χT (τP+w) (τT+w)
    lo hi F UM UT hUM hUT hMband hFband κM (ν+w) qM hqMInst χM hκM hκmax hqM
    (hfreq ν w hν hw) UQ Alo Blo (σ+w) qQ hqQInst χQ hUQ hQA hAB hBQ hqQ
    (hshift σ w hσ hw) hmeanScale hresScale hlog qRat dRat hqRat0 hdRat hdvd hqRat ψ
  have hP (u : ℝ) :
      (∑ p ∈ s, (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
        (rationalProductCharacter qRat dRat χP ψ (p : ZMod (qP*(qRat/dRat)))*
          typeIIPhase (τP+w) p)*harmonicMellinWeight u p) =
      ∑ p ∈ s, (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
        (rationalProductCharacter qRat dRat χP ψ (p : ZMod (qP*(qRat/dRat)))*
          typeIIPhase τP p)*harmonicMellinWeight (u+w) p := by
    apply sum_congr rfl
    intro p _
    simpa only [mul_assoc,mul_one] using rational_phase_harmonic_common_shift
      ((1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
        rationalProductCharacter qRat dRat χP ψ (p : ZMod (qP*(qRat/dRat)))) 1 τP u w p
  have hQ (u : ℝ) :
      (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
        typeIIPhase (σ+w) n*rationalProductCharacter qRat dRat χQ ψ
          (n : ZMod (qQ*(qRat/dRat)))*harmonicMellinWeight u n) =
      ∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
        typeIIPhase σ n*rationalProductCharacter qRat dRat χQ ψ
          (n : ZMod (qQ*(qRat/dRat)))*harmonicMellinWeight (u+w) n := by
    apply sum_congr rfl
    intro n _
    simpa only [one_mul] using rational_phase_harmonic_common_shift 1
      (rationalProductCharacter qRat dRat χQ ψ (n : ZMod (qQ*(qRat/dRat)))) σ u w n
  have hM (u : ℝ) :
      (∑ n ∈ (Ioc lo hi).filter (fun n =>
          (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ) ≠ 0),
        (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ)*
          rationalProductCharacter qRat dRat χM ψ (n : ZMod (qM*(qRat/dRat)))*
          typeIIPhase (ν+w) n*harmonicMellinWeight u n) =
      ∑ n ∈ (Ioc lo hi).filter (fun n =>
          (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ) ≠ 0),
        (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ)*
          rationalProductCharacter qRat dRat χM ψ (n : ZMod (qM*(qRat/dRat)))*
          typeIIPhase ν n*harmonicMellinWeight (u+w) n := by
    apply sum_congr rfl
    intro n _
    simpa only [mul_one] using rational_phase_harmonic_common_shift
      ((typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ)*
        rationalProductCharacter qRat dRat χM ψ (n : ZMod (qM*(qRat/dRat)))) 1 ν u w n
  have hT (u : ℝ) :
      (∑ n ∈ F, candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
        tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase (τT+w) n*
          rationalResidualGcdMultiplier qRat dRat ψ n) n*harmonicMellinWeight u n) =
      ∑ n ∈ F, candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
        tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n*
          rationalResidualGcdMultiplier qRat dRat ψ n) n*harmonicMellinWeight (u+w) n := by
    apply sum_congr rfl
    intro n _
    unfold candidateSelectedResidualCoefficient
    dsimp only
    rw [typeIIPhase_add, ← typeIIPhase_harmonic_mellin_shift w u n]
    ring
  simpa only [hP,hQ,hM,hT] using hresult

theorem exists_rational_shifted_filtered_rough_integral_precision_log_radius
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q cLog d A aLong γrough vMax : ℝ}
    (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1) (hcLog : 0 ≤ cLog) (hd : 0 < d)
    (haLong : 0 < aLong)
    (hγ : 0 < γrough) (hv : vMax < 1)
    (T : ℕ) (Tmod Sshift Cmod Sfreq Rmod W : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, ∃ S₀ : ℝ, 0 ≤ S₀ ∧
      ∀ S : ℝ, S₀ ≤ S →
      ∀ᶠ L : ℝ in atTop,
      ∀ (r jStar : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (tmarks umarks : candidatePIndices c L → ℕ) (big : Finset (candidatePIndices c L))
        (b : GroupMarkedLists (fun g : big => candidatePBand (c*L) g.val.val)
          (fun g : big => umarks g.val) → ℂ) (κ : ℕ → ℂ),
      (∀ g, tmarks g ≤ T) → (∀ l, ‖b l‖ ≤ L^B) → (∀ n, ‖κ n‖ ≤ 1) →
      ∀ (g : ℕ), g ∈ candidateSmallPIndices c L →
      ∀ (s : Finset ℕ) (Y P R : ℝ), s ⊆ candidatePBand (c*L) g → s.Nonempty →
      1 ≤ Y → d*L ≤ Real.log Y → Real.log Y ≤ cLog*L →
      0 ≤ R → R ≤ Y →
      (∀ p ∈ s, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*P) →
      ∀ (qP qT : ℕ) (χP : DirichletCharacter ℂ qP) (χT : DirichletCharacter ℂ qT)
        (τP τT : ℝ) (lo hi : ℕ) (F : Finset ℕ) (UM UT : ℝ),
      0 < UM → 1 ≤ UT →
      (∀ n ∈ Ioc lo hi, UM ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UM) →
      (∀ n ∈ F, UT ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UT) →
      ∀ (aM v ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      v ≤ vMax → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (UQ Alo Blo σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      Real.exp (aLong*L) ≤ UQ → UQ ≤ Alo → Alo ≤ Blo → Blo ≤ 2*UQ →
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      R ≤ UQ*UM*UT/2 → Y^(3/5 : ℝ) ≤ UM*UT/2 → Real.log (8*(UQ*UM*UT)) ≤ cLog*L →
      ∀ (qRat dRat : ℕ), 0 < qRat → 0 < dRat → dRat ∣ qRat →
      (qRat : ℝ) ≤ L^Rmod →
      ∀ ψ : AddChar (Additive (ZMod (qRat/dRat))ˣ) ℂ,
      ∀ w : ℝ, |w| ≤ L^W →
      (∫ u in Set.Icc (-R) R,
        ‖(∑ p ∈ s, (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
            (rationalProductCharacter qRat dRat χP ψ (p : ZMod (qP*(qRat/dRat)))*typeIIPhase τP p)*harmonicMellinWeight (u+w) p) *
          (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
            typeIIPhase σ n*rationalProductCharacter qRat dRat χQ ψ (n : ZMod (qQ*(qRat/dRat)))*harmonicMellinWeight (u+w) n)*
          (∑ n ∈ (Ioc lo hi).filter (fun n =>
              (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ) ≠ 0),
            (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ)*
              rationalProductCharacter qRat dRat χM ψ (n : ZMod (qM*(qRat/dRat)))*typeIIPhase ν n*harmonicMellinWeight (u+w) n)*
          (∑ n ∈ F, candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
            tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n*rationalResidualGcdMultiplier qRat dRat ψ n) n*
              harmonicMellinWeight (u+w) n)‖^2) ≤ L^(-A) := by
  obtain ⟨C,hC,hmain⟩ := exists_rational_filtered_rough_integral_precision_log_radius
    (A := A) hZ hc hq0 hq1 hcLog hd haLong hγ hv
    T Tmod (max Sshift W+1) Cmod (max Sfreq W+1) Rmod
  refine ⟨C,hC,?_⟩
  intro B
  obtain ⟨S₀,hS₀,hbound⟩ := hmain B
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [hbound S hS, eventually_add_frequency_power_bound Sshift W,
    eventually_add_frequency_power_bound Sfreq W] with L hdecay hshift hfreq
  intro r jStar hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ g hg s Y P R hs hne
    hY hYlo hYhi hR hRY hsp qP qT χP χT τP τT lo hi F UM UT hUM hUT hMband hFband
    aM v ν qM hqMInst χM hvM hqM hν UQ Alo Blo σ qQ hqQInst χQ hUQ hQA hAB hBQ hqQ hσ
    hmeanScale hresScale hlog qRat dRat hqRat0 hdRat hdvd hqRat ψ w hw
  have hraw := @hdecay r jStar hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ
    g hg s Y P R hs hne hY hYlo hYhi hR hRY hsp
    qP qT χP χT (τP+w) (τT+w) lo hi F UM UT hUM hUT hMband hFband
    aM v (ν+w) qM hqMInst χM hvM hqM (hfreq ν w hν hw)
    UQ Alo Blo (σ+w) qQ hqQInst χQ hUQ hQA hAB hBQ hqQ (hshift σ w hσ hw)
    hmeanScale hresScale hlog qRat dRat hqRat0 hdRat hdvd hqRat ψ
  have heP (u : ℝ) :
      (∑ p ∈ s, (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
        (rationalProductCharacter qRat dRat χP ψ (p : ZMod (qP*(qRat/dRat)))*typeIIPhase (τP+w) p)*
          harmonicMellinWeight u p) =
      ∑ p ∈ s, (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
        (rationalProductCharacter qRat dRat χP ψ (p : ZMod (qP*(qRat/dRat)))*typeIIPhase τP p)*
          harmonicMellinWeight (u+w) p := by
    apply sum_congr rfl
    intro p _
    simpa only [mul_one, mul_assoc] using rational_phase_harmonic_common_shift
      ((1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
        rationalProductCharacter qRat dRat χP ψ (p : ZMod (qP*(qRat/dRat)))) 1 τP u w p
  have heQ (u : ℝ) :
      (∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
        typeIIPhase (σ+w) n*rationalProductCharacter qRat dRat χQ ψ (n : ZMod (qQ*(qRat/dRat)))*
          harmonicMellinWeight u n) =
      ∑ n ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
        typeIIPhase σ n*rationalProductCharacter qRat dRat χQ ψ (n : ZMod (qQ*(qRat/dRat)))*
          harmonicMellinWeight (u+w) n := by
    apply sum_congr rfl
    intro n _
    simpa only [one_mul] using rational_phase_harmonic_common_shift 1
      (rationalProductCharacter qRat dRat χQ ψ (n : ZMod (qQ*(qRat/dRat)))) σ u w n
  have heM (u : ℝ) :
      (∑ n ∈ (Ioc lo hi).filter (fun n =>
          (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ) ≠ 0),
        (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ)*
          rationalProductCharacter qRat dRat χM ψ (n : ZMod (qM*(qRat/dRat)))*typeIIPhase (ν+w) n*
            harmonicMellinWeight u n) =
      ∑ n ∈ (Ioc lo hi).filter (fun n =>
          (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ) ≠ 0),
        (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ)*
          rationalProductCharacter qRat dRat χM ψ (n : ZMod (qM*(qRat/dRat)))*typeIIPhase ν n*
            harmonicMellinWeight (u+w) n := by
    apply sum_congr rfl
    intro n _
    simpa only [mul_one] using rational_phase_harmonic_common_shift
      ((typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ)*
        rationalProductCharacter qRat dRat χM ψ (n : ZMod (qM*(qRat/dRat)))) 1 ν u w n
  have heT (u : ℝ) :
      (∑ n ∈ F, candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
        tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase (τT+w) n*
          rationalResidualGcdMultiplier qRat dRat ψ n) n*harmonicMellinWeight u n) =
      ∑ n ∈ F, candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
        tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n*
          rationalResidualGcdMultiplier qRat dRat ψ n) n*harmonicMellinWeight (u+w) n := by
    apply sum_congr rfl
    intro n _
    unfold candidateSelectedResidualCoefficient
    dsimp only
    rw [typeIIPhase_add, ← typeIIPhase_harmonic_mellin_shift w u n]
    ring
  simpa only [heP, heQ, heM, heT] using hraw

theorem exists_rational_prime_box_integral_precision
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q cLog d A aLong : ℝ}
    (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1) (hcLog : 0 ≤ cLog) (hd : 0 < d)
    (haLong : 0 < aLong)
    (T : ℕ) (Tmod Sshift Cmod Sfreq Rmod W : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, ∃ S₀ : ℝ, 0 ≤ S₀ ∧
      ∀ S : ℝ, S₀ ≤ S →
      ∀ᶠ L : ℝ in atTop,
      ∀ (r jStar : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (tmarks umarks : candidatePIndices c L → ℕ) (big : Finset (candidatePIndices c L))
        (b : GroupMarkedLists (fun g : big => candidatePBand (c*L) g.val.val)
          (fun g : big => umarks g.val) → ℂ) (κ : ℕ → ℂ),
      (∀ g, tmarks g ≤ T) → (∀ l, ‖b l‖ ≤ L^B) → (∀ n, ‖κ n‖ ≤ 1) →
      ∀ (g : ℕ), g ∈ candidateSmallPIndices c L →
      ∀ (s : Finset ℕ) (Y P R : ℝ), s ⊆ candidatePBand (c*L) g → s.Nonempty →
      1 ≤ Y → d*L ≤ Real.log Y → Real.log Y ≤ cLog*L →
      0 ≤ R → R ≤ Y →
      (∀ p ∈ s, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*P) →
      ∀ (qP qT : ℕ) (χP : DirichletCharacter ℂ qP) (χT : DirichletCharacter ℂ qT)
        (τP τT : ℝ) (lo hi : ℕ) (F : Finset ℕ) (UM UT : ℝ),
      0 < UM → 1 ≤ UT →
      (∀ n ∈ Ioc lo hi, UM ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UM) →
      (∀ n ∈ F, UT ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UT) →
      ∀ (κM ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      0 ≤ κM → κM ≤ 1/50 → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (UQ Alo Blo σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      Real.exp (aLong*L) ≤ UQ → UQ ≤ Alo → Alo ≤ Blo → Blo ≤ 2*UQ →
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      R ≤ UQ*UM*UT/2 → Y^(3/5 : ℝ) ≤ UM*UT/2 → Real.log (8*(UQ*UM*UT)) ≤ cLog*L →
      ∀ qRat : ℕ, 0 < qRat → (qRat : ℝ) ≤ L^Rmod → ∀ aRat : ℤ,
      ∀ w : ℝ, |w| ≤ L^W →
      (∫ u in Set.Icc (-R) R,
        ‖rationalFourBoxKernelSum qRat aRat s
          (roughBand Alo Blo (Real.exp (Real.sqrt L)))
          ((Ioc lo hi).filter (fun n =>
            (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ) ≠ 0)) F
          (fun p => (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
            (χP (p : ZMod qP)*typeIIPhase τP p))
          (fun n => typeIIPhase σ n*χQ (n : ZMod qQ))
          (fun n => (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ)*
            χM (n : ZMod qM)*typeIIPhase ν n)
          (candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
            tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n))
          (fun n => harmonicMellinWeight (u+w) n)‖^2) ≤ L^(-A) := by
  obtain ⟨C,hC,hmain⟩ := exists_rational_shifted_filtered_prime_integral_precision_log_radius
    (A := A+3*Rmod) hZ hc hq0 hq1 hcLog hd haLong T Tmod Sshift Cmod Sfreq Rmod W
  refine ⟨C,hC,?_⟩
  intro B
  obtain ⟨S₀,hS₀,hbound⟩ := hmain B
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [hbound S hS, eventually_rational_candidate_P_properties hc Rmod,
    eventually_rational_rough_Q_properties Rmod,
    eventually_rational_prime_M_properties S Rmod (hS₀.trans hS),
    eventually_gt_atTop (0 : ℝ)] with L hdecay hP hQ hM hL
  intro r jStar hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ g hg s Y P R hs hne
    hY hYlo hYhi hR hRY hsp qP qT χP χT τP τT lo hi F UM UT hUM hUT hMband hFband
    κM ν qM hqMInst χM hκM hκmax hqM hν UQ Alo Blo σ qQ hqQInst χQ hUQ hQA hAB hBQ hqQ hσ
    hmeanScale hresScale hlog qRat hqRat0 hqRat aRat w hw
  let δ : ℕ → ℂ := fun p => (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
    (χP (p : ZMod qP)*typeIIPhase τP p)
  let α : ℕ → ℂ := fun n => typeIIPhase σ n*χQ (n : ZMod qQ)
  let β : ℕ → ℂ := fun n => (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ)*
    χM (n : ZMod qM)*typeIIPhase ν n
  let γ := candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
    tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n)
  have hp := hP g (Finset.mem_union_left _ hg) qRat hqRat0 hqRat
  have hq := hQ Alo Blo qRat hqRat0 hqRat
  have hm := hM κM hκM hκmax lo hi qRat hqRat0 hqRat
  have hFpos : ∀ n ∈ F, 0 < n := by
    intro n hn
    have hnR : (0 : ℝ) < n := zero_lt_one.trans_le (hUT.trans (hFband n hn).1)
    exact_mod_cast hnR
  have hbox := rational_harmonic_box_energy_le hqRat0 aRat s
    (roughBand Alo Blo (Real.exp (Real.sqrt L)))
    ((Ioc lo hi).filter (fun n =>
      (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ) ≠ 0)) F δ α β γ
    (fun p hp' => (hp p (hs hp')).2) (fun n hn => (hq n hn).2)
    (fun n hn => (hm.2 n hn).2)
    (fun p hp' => (hp p (hs hp')).1.pos) (fun n hn => (hq n hn).1)
    (fun n hn => (hm.2 n hn).1) hFpos (-R) R (L^(-(A+3*Rmod))) w
    (Real.rpow_nonneg hL.le _) (by
      intro dRat hdRat ψ
      have hb := @hdecay r jStar hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ
        g hg s Y P R hs hne hY hYlo hYhi hR hRY hsp qP qT χP χT τP τT
        lo hi F UM UT hUM hUT hMband hFband κM ν qM hqMInst χM hκM hκmax hqM hν
        UQ Alo Blo σ qQ hqQInst χQ hUQ hQA hAB hBQ hqQ hσ
        hmeanScale hresScale hlog qRat dRat hqRat0 (Nat.pos_of_mem_divisors hdRat)
        (Nat.dvd_of_mem_divisors hdRat) hqRat ψ w hw
      simpa only [δ,α,β,γ,rational_normalized_phase_twist,rational_phase_left_twist,
        rational_weighted_phase_twist,candidate_selected_rational_multiplier] using hb)
  exact hbox.trans (rational_box_cubic_cost hL hqRat)

theorem exists_rational_rough_box_integral_precision
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q cLog d A aLong γrough vMax : ℝ}
    (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1) (hcLog : 0 ≤ cLog) (hd : 0 < d)
    (haLong : 0 < aLong)
    (hγ : 0 < γrough) (hv : vMax < 1)
    (T : ℕ) (Tmod Sshift Cmod Sfreq Rmod W : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, ∃ S₀ : ℝ, 0 ≤ S₀ ∧
      ∀ S : ℝ, S₀ ≤ S →
      ∀ᶠ L : ℝ in atTop,
      ∀ (r jStar : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (tmarks umarks : candidatePIndices c L → ℕ) (big : Finset (candidatePIndices c L))
        (b : GroupMarkedLists (fun g : big => candidatePBand (c*L) g.val.val)
          (fun g : big => umarks g.val) → ℂ) (κ : ℕ → ℂ),
      (∀ g, tmarks g ≤ T) → (∀ l, ‖b l‖ ≤ L^B) → (∀ n, ‖κ n‖ ≤ 1) →
      ∀ (g : ℕ), g ∈ candidateSmallPIndices c L →
      ∀ (s : Finset ℕ) (Y P R : ℝ), s ⊆ candidatePBand (c*L) g → s.Nonempty →
      1 ≤ Y → d*L ≤ Real.log Y → Real.log Y ≤ cLog*L →
      0 ≤ R → R ≤ Y →
      (∀ p ∈ s, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*P) →
      ∀ (qP qT : ℕ) (χP : DirichletCharacter ℂ qP) (χT : DirichletCharacter ℂ qT)
        (τP τT : ℝ) (lo hi : ℕ) (F : Finset ℕ) (UM UT : ℝ),
      0 < UM → 1 ≤ UT →
      (∀ n ∈ Ioc lo hi, UM ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UM) →
      (∀ n ∈ F, UT ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UT) →
      ∀ (aM v ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      v ≤ vMax → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (UQ Alo Blo σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      Real.exp (aLong*L) ≤ UQ → UQ ≤ Alo → Alo ≤ Blo → Blo ≤ 2*UQ →
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      R ≤ UQ*UM*UT/2 → Y^(3/5 : ℝ) ≤ UM*UT/2 → Real.log (8*(UQ*UM*UT)) ≤ cLog*L →
      ∀ qRat : ℕ, 0 < qRat → (qRat : ℝ) ≤ L^Rmod → ∀ aRat : ℤ,
      ∀ w : ℝ, |w| ≤ L^W →
      (∫ u in Set.Icc (-R) R,
        ‖rationalFourBoxKernelSum qRat aRat s
          (roughBand Alo Blo (Real.exp (Real.sqrt L)))
          ((Ioc lo hi).filter (fun n =>
            (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ) ≠ 0)) F
          (fun p => (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
            (χP (p : ZMod qP)*typeIIPhase τP p))
          (fun n => typeIIPhase σ n*χQ (n : ZMod qQ))
          (fun n => (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ)*
            χM (n : ZMod qM)*typeIIPhase ν n)
          (candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
            tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n))
          (fun n => harmonicMellinWeight (u+w) n)‖^2) ≤ L^(-A) := by
  obtain ⟨C,hC,hmain⟩ := exists_rational_shifted_filtered_rough_integral_precision_log_radius
    (A := A+3*Rmod) hZ hc hq0 hq1 hcLog hd haLong hγ hv T Tmod Sshift Cmod Sfreq Rmod W
  refine ⟨C,hC,?_⟩
  intro B
  obtain ⟨S₀,hS₀,hbound⟩ := hmain B
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [hbound S hS, eventually_rational_candidate_P_properties hc Rmod,
    eventually_rational_rough_Q_properties Rmod,
    eventually_rational_rough_M_properties hγ Rmod,
    eventually_gt_atTop (0 : ℝ)] with L hdecay hP hQ hM hL
  intro r jStar hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ g hg s Y P R hs hne
    hY hYlo hYhi hR hRY hsp qP qT χP χT τP τT lo hi F UM UT hUM hUT hMband hFband
    aM v ν qM hqMInst χM hvM hqM hν UQ Alo Blo σ qQ hqQInst χQ hUQ hQA hAB hBQ hqQ hσ
    hmeanScale hresScale hlog qRat hqRat0 hqRat aRat w hw
  let δ : ℕ → ℂ := fun p => (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
    (χP (p : ZMod qP)*typeIIPhase τP p)
  let α : ℕ → ℂ := fun n => typeIIPhase σ n*χQ (n : ZMod qQ)
  let β : ℕ → ℂ := fun n => (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ)*
    χM (n : ZMod qM)*typeIIPhase ν n
  let γ := candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
    tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n)
  have hp := hP g (Finset.mem_union_left _ hg) qRat hqRat0 hqRat
  have hq := hQ Alo Blo qRat hqRat0 hqRat
  have hm := hM S aM v lo hi qRat hqRat0 hqRat
  have hFpos : ∀ n ∈ F, 0 < n := by
    intro n hn
    have hnR : (0 : ℝ) < n := zero_lt_one.trans_le (hUT.trans (hFband n hn).1)
    exact_mod_cast hnR
  have hbox := rational_harmonic_box_energy_le hqRat0 aRat s
    (roughBand Alo Blo (Real.exp (Real.sqrt L)))
    ((Ioc lo hi).filter (fun n =>
      (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ) ≠ 0)) F δ α β γ
    (fun p hp' => (hp p (hs hp')).2) (fun n hn => (hq n hn).2)
    (fun n hn => (hm.2 n hn).2)
    (fun p hp' => (hp p (hs hp')).1.pos) (fun n hn => (hq n hn).1)
    (fun n hn => (hm.2 n hn).1) hFpos (-R) R (L^(-(A+3*Rmod))) w
    (Real.rpow_nonneg hL.le _) (by
      intro dRat hdRat ψ
      have hb := @hdecay r jStar hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ
        g hg s Y P R hs hne hY hYlo hYhi hR hRY hsp qP qT χP χT τP τT
        lo hi F UM UT hUM hUT hMband hFband aM v ν qM hqMInst χM hvM hqM hν
        UQ Alo Blo σ qQ hqQInst χQ hUQ hQA hAB hBQ hqQ hσ
        hmeanScale hresScale hlog qRat dRat hqRat0 (Nat.pos_of_mem_divisors hdRat)
        (Nat.dvd_of_mem_divisors hdRat) hqRat ψ w hw
      simpa only [δ,α,β,γ,rational_normalized_phase_twist,rational_phase_left_twist,
        rational_weighted_phase_twist,candidate_selected_rational_multiplier] using hb)
  exact hbox.trans (rational_box_cubic_cost hL hqRat)

theorem exists_rational_prime_cutoff_integral_precision
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q cLog d A aLong : ℝ}
    (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1) (hcLog : 0 ≤ cLog) (hd : 0 < d)
    (haLong : 0 < aLong)
    (T : ℕ) (Tmod Sshift Cmod Sfreq Rmod W : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, ∃ S₀ : ℝ, 0 ≤ S₀ ∧
      ∀ S : ℝ, S₀ ≤ S →
      ∀ᶠ L : ℝ in atTop,
      ∀ (r jStar : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (tmarks umarks : candidatePIndices c L → ℕ) (big : Finset (candidatePIndices c L))
        (b : GroupMarkedLists (fun g : big => candidatePBand (c*L) g.val.val)
          (fun g : big => umarks g.val) → ℂ) (κ : ℕ → ℂ),
      (∀ g, tmarks g ≤ T) → (∀ l, ‖b l‖ ≤ L^B) → (∀ n, ‖κ n‖ ≤ 1) →
      ∀ (g : ℕ), g ∈ candidateSmallPIndices c L →
      ∀ (s : Finset ℕ) (Y P R : ℝ), s ⊆ candidatePBand (c*L) g → s.Nonempty →
      1 ≤ Y → d*L ≤ Real.log Y → Real.log Y ≤ cLog*L →
      0 ≤ R → R ≤ Y →
      (∀ p ∈ s, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*P) →
      ∀ (qP qT : ℕ) (χP : DirichletCharacter ℂ qP) (χT : DirichletCharacter ℂ qT)
        (τP τT : ℝ) (lo hi : ℕ) (F : Finset ℕ) (UM UT : ℝ),
      0 < UM → 1 ≤ UT →
      (∀ n ∈ Ioc lo hi, UM ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UM) →
      (∀ n ∈ F, UT ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UT) →
      ∀ (κM ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      0 ≤ κM → κM ≤ 1/50 → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (UQ Alo Blo σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      Real.exp (aLong*L) ≤ UQ → UQ ≤ Alo → Alo ≤ Blo → Blo ≤ 2*UQ →
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      R ≤ UQ*UM*UT/2 → Y^(3/5 : ℝ) ≤ UM*UT/2 → Real.log (8*(UQ*UM*UT)) ≤ cLog*L →
      (∀ p ∈ s, ∀ z ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
        ∀ m ∈ (Ioc lo hi).filter (fun n =>
          (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ) ≠ 0),
        ∀ n ∈ F, Y/128 ≤ ((p*z*m*n : ℕ) : ℝ) ∧
          ((p*z*m*n : ℕ) : ℝ) ≤ 64*Real.exp 2*Y) →
      ∀ qRat : ℕ, 0 < qRat → (qRat : ℝ) ≤ L^Rmod → ∀ aRat : ℤ,
      ∀ w : ℝ, |w| ≤ L^W →
      (∫ u in Set.Icc (-R) R,
        ‖rationalFourBoxKernelSum qRat aRat s
          (roughBand Alo Blo (Real.exp (Real.sqrt L)))
          ((Ioc lo hi).filter (fun n =>
            (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ) ≠ 0)) F
          (fun p => (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
            (χP (p : ZMod qP)*typeIIPhase τP p))
          (fun n => typeIIPhase σ n*χQ (n : ZMod qQ))
          (fun n => (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ)*
            χM (n : ZMod qM)*typeIIPhase ν n)
          (candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
            tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n))
          (fun n => ((harmonicCommonCutoff ((n : ℝ)/Y)/(n : ℝ) : ℝ) : ℂ)*
            physicalMellinPhase (u+w) (n : ℝ))‖^2) ≤ L^(-A) := by
  obtain ⟨C,hC,hres⟩ := exists_candidate_selected_residual_power_bound hc hq0 hq1 T
  obtain ⟨Bcoeff,hBcoeff,hsmall⟩ := exists_candidate_small_prime_factor_data hc
  obtain ⟨_,_,hmain⟩ := exists_rational_shifted_filtered_prime_integral_precision_log_radius
    (A := A+3*Rmod+1) hZ hc hq0 hq1 hcLog hd haLong T Tmod Sshift Cmod Sfreq Rmod
      (max W 1+1)
  refine ⟨C,hC,?_⟩
  intro B
  obtain ⟨S₀,hS₀,hbound⟩ := hmain B
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [hbound S hS,hres,hsmall,
    eventually_rational_candidate_P_properties hc Rmod,
    eventually_rational_rough_Q_properties Rmod,
    eventually_rational_prime_M_properties S Rmod (hS₀.trans hS),
    eventually_rational_normalized_full_box_precision (E := C+B+1)
      (by norm_num : (0 : ℝ) < 1) hcLog (A+3*Rmod),
    eventually_harmonic_mellin_frequency_bound W 1,
    eventually_ge_atTop (max 1 Bcoeff)] with L hdecay hresL hsmallL hP hQ hM hcut hfreq hLbound
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hLbound
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hBL : Bcoeff ≤ L := (le_max_right _ _).trans hLbound
  intro r jStar hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ g hg s Y P R hs hne
    hY hYlo hYhi hR hRY hsp qP qT χP χT τP τT lo hi F UM UT hUM hUT hMband hFband
    κM ν qM hqMInst χM hκM hκmax hqM hν UQ Alo Blo σ qQ hqQInst χQ hUQ hQA hAB hBQ hqQ hσ
    hmeanScale hresScale hlog hgeom qRat hqRat0 hqRat aRat w hw
  let δ : ℕ → ℂ := fun p => (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
    (χP (p : ZMod qP)*typeIIPhase τP p)
  let α : ℕ → ℂ := fun n => typeIIPhase σ n*χQ (n : ZMod qQ)
  let β : ℕ → ℂ := fun n => (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ)*
    χM (n : ZMod qM)*typeIIPhase ν n
  let γ := candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
    tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n)
  have hp := hP g (Finset.mem_union_left _ hg) qRat hqRat0 hqRat
  have hq := hQ Alo Blo qRat hqRat0 hqRat
  have hm := hM κM hκM hκmax lo hi qRat hqRat0 hqRat
  have hFpos : ∀ n ∈ F, 0 < n := by
    intro n hn
    have hnR : (0 : ℝ) < n := zero_lt_one.trans_le (hUT.trans (hFband n hn).1)
    exact_mod_cast hnR
  have hδ : ∀ p ∈ s, ‖δ p‖ ≤ Bcoeff := by
    obtain ⟨_,_,_,hcoeff⟩ := hsmallL g hg s P hs hne hsp
    intro p hp'
    exact hcoeff (fun n => χP (n : ZMod qP)*typeIIPhase τP n)
      (fun n _ => character_typeIIPhase_norm_le χP τP n) ⟨p,hp'⟩
  have hα : ∀ n, ‖α n‖ ≤ 1 := by
    intro n
    simpa only [α,mul_comm] using character_typeIIPhase_norm_le χQ σ n
  have hβ : ∀ n, ‖β n‖ ≤ 1 := by
    intro n
    dsimp only [β]
    rw [mul_assoc,norm_mul]
    exact (mul_le_mul (hm.1 n) (character_typeIIPhase_norm_le χM ν n)
      (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)
  have hγ : ∀ n, ‖γ n‖ ≤ L^(C+B) := hresL B r jStar hr hj take hkeep ξ
    tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n)
    ht hb hκ (character_typeIIPhase_norm_le χT τT)
  have hprod : Bcoeff*1*1*L^(C+B) ≤ L^(C+B+1) := by
    calc
      _ ≤ L*L^(C+B) := by simpa only [mul_one] using
        mul_le_mul_of_nonneg_right hBL (Real.rpow_nonneg hL.le (C+B))
      _ = _ := by rw [Real.rpow_add hL (C+B) 1, Real.rpow_one]; ring
  have hRL : R ≤ L*Y := hRY.trans (le_mul_of_one_le_left (zero_le_one.trans hY) hL1)
  have hbox := hcut qRat hqRat0 aRat Y hY hYhi s
    (roughBand Alo Blo (Real.exp (Real.sqrt L)))
    ((Ioc lo hi).filter (fun n =>
      (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ) ≠ 0)) F
    δ α β γ Bcoeff 1 1 (L^(C+B)) (zero_le_one.trans hBcoeff) zero_le_one zero_le_one
    (Real.rpow_nonneg hL.le _) hprod
    (fun p hp' => (hp p (hs hp')).1.pos) (fun n hn => (hq n hn).1)
    (fun n hn => (hm.2 n hn).1) hFpos
    (fun p hp' => (hp p (hs hp')).2) (fun n hn => (hq n hn).2)
    (fun n hn => (hm.2 n hn).2) hδ (fun n _ => hα n) (fun n _ => hβ n)
    (fun n _ => hγ n) hgeom R w hR hRL (by
      intro dRat hdRat ψ u hu
      have hw' : |w+2*Real.pi*u| ≤ L^(max W 1+1) := by
        have hh := hfreq w 0 u hw (by simpa only [abs_zero] using Real.rpow_nonneg hL.le W)
          (by simpa only [Real.norm_eq_abs] using hu)
        simpa only [add_zero,abs_neg] using hh
      have hb' := @hdecay r jStar hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ
        g hg s Y P R hs hne hY hYlo hYhi hR hRY hsp qP qT χP χT τP τT
        lo hi F UM UT hUM hUT hMband hFband κM ν qM hqMInst χM hκM hκmax hqM hν
        UQ Alo Blo σ qQ hqQInst χQ hUQ hQA hAB hBQ hqQ hσ
        hmeanScale hresScale hlog qRat dRat hqRat0 (Nat.pos_of_mem_divisors hdRat)
        (Nat.dvd_of_mem_divisors hdRat) hqRat ψ (w+2*Real.pi*u) hw'
      simpa only [δ,α,β,γ,rational_normalized_phase_twist,rational_phase_left_twist,
        rational_weighted_phase_twist,candidate_selected_rational_multiplier,add_assoc] using hb')
  exact hbox.trans (rational_box_cubic_cost hL hqRat)

theorem exists_rational_rough_cutoff_integral_precision
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q cLog d A aLong γrough vMax ρ : ℝ}
    (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1) (hcLog : 0 ≤ cLog) (hd : 0 < d)
    (haLong : 0 < aLong)
    (hγ : 0 < γrough) (hv : vMax < 1) (hρ : 0 < ρ)
    (T : ℕ) (Tmod Sshift Cmod Sfreq Rmod W : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, ∃ S₀ : ℝ, 0 ≤ S₀ ∧
      ∀ S : ℝ, S₀ ≤ S →
      ∀ᶠ L : ℝ in atTop,
      ∀ (r jStar : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (tmarks umarks : candidatePIndices c L → ℕ) (big : Finset (candidatePIndices c L))
        (b : GroupMarkedLists (fun g : big => candidatePBand (c*L) g.val.val)
          (fun g : big => umarks g.val) → ℂ) (κ : ℕ → ℂ),
      (∀ g, tmarks g ≤ T) → (∀ l, ‖b l‖ ≤ L^B) → (∀ n, ‖κ n‖ ≤ 1) →
      ∀ (g : ℕ), g ∈ candidateSmallPIndices c L →
      ∀ (s : Finset ℕ) (Y P R : ℝ), s ⊆ candidatePBand (c*L) g → s.Nonempty →
      1 ≤ Y → d*L ≤ Real.log Y → Real.log Y ≤ cLog*L →
      0 ≤ R → R ≤ Y →
      (∀ p ∈ s, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*P) →
      ∀ (qP qT : ℕ) (χP : DirichletCharacter ℂ qP) (χT : DirichletCharacter ℂ qT)
        (τP τT : ℝ) (lo hi : ℕ) (F : Finset ℕ) (UM UT : ℝ),
      0 < UM → 1 ≤ UT →
      (∀ n ∈ Ioc lo hi, UM ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UM) →
      (∀ n ∈ F, UT ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UT) →
      ∀ (aM v ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      v ≤ vMax → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (UQ Alo Blo σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      Real.exp (aLong*L) ≤ UQ → UQ ≤ Alo → Alo ≤ Blo → Blo ≤ 2*UQ →
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      R ≤ UQ*UM*UT/2 → Y^(3/5 : ℝ) ≤ UM*UT/2 → Real.log (8*(UQ*UM*UT)) ≤ cLog*L →
      (∀ p ∈ s, ∀ nQ ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
        ∀ nM ∈ (Ioc lo hi).filter (fun n =>
          (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ) ≠ 0),
        ∀ nT ∈ F, Y/128 ≤ ((p*nQ*nM*nT : ℕ) : ℝ) ∧
          ((p*nQ*nM*nT : ℕ) : ℝ) ≤ 64*Real.exp 2*Y) →
      ∀ qRat : ℕ, 0 < qRat → (qRat : ℝ) ≤ L^Rmod → ∀ aRat : ℤ,
      ∀ w : ℝ, |w| ≤ L^W →
      (∫ u in Set.Icc (-R) R,
        ‖rationalFourBoxKernelSum qRat aRat s
          (roughBand Alo Blo (Real.exp (Real.sqrt L)))
          ((Ioc lo hi).filter (fun n =>
            (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ) ≠ 0)) F
          (fun p => (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
            (χP (p : ZMod qP)*typeIIPhase τP p))
          (fun n => typeIIPhase σ n*χQ (n : ZMod qQ))
          (fun n => (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ)*
            χM (n : ZMod qM)*typeIIPhase ν n)
          (candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
            tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n))
          (fun n => ((harmonicCommonCutoff ((n : ℝ)/Y)/(n : ℝ) : ℝ) : ℂ)*
            physicalMellinPhase (u+w) (n : ℝ))‖^2) ≤ L^(-A) := by
  obtain ⟨C,hC,hmain⟩ := exists_rational_shifted_filtered_rough_integral_precision_log_radius
    (A := A+3*Rmod+1) hZ hc hq0 hq1 hcLog hd haLong hγ hv
    T Tmod Sshift Cmod Sfreq Rmod (max W ρ+1)
  obtain ⟨Cres,_,hres⟩ := exists_candidate_selected_residual_power_bound hc hq0 hq1 T
  obtain ⟨vpool,_,hvpool,_,hpool⟩ := exists_candidate_P_pool_bounds hc
  refine ⟨C,hC,?_⟩
  intro B
  obtain ⟨S₀,hS₀,hbound⟩ := hmain B
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [hbound S hS, eventually_rational_candidate_P_properties hc Rmod,
    eventually_rational_rough_Q_properties Rmod,
    eventually_rational_rough_M_properties hγ Rmod,
    hres, hpool, eventually_ge_atTop (1/vpool), eventually_ge_atTop (1 : ℝ),
    eventually_harmonic_mellin_frequency_bound W ρ,
    eventually_rational_normalized_full_box_precision (E := Cres+B+1) hρ hcLog (A+3*Rmod)]
    with L hdecay hP hQ hM hres hpool hpoolInv hL1 hfreq hcutoff
  have hL : 0 < L := zero_lt_one.trans_le hL1
  intro r jStar hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ g hg s Y P R hs hne
    hY hYlo hYhi hR hRY hsp qP qT χP χT τP τT lo hi F UM UT hUM hUT hMband hFband
    aM v ν qM hqMInst χM hvM hqM hν UQ Alo Blo σ qQ hqQInst χQ hUQ hQA hAB hBQ hqQ hσ
    hmeanScale hresScale hlog hgeom qRat hqRat0 hqRat aRat w hw
  let δ : ℕ → ℂ := fun p => (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
    (χP (p : ZMod qP)*typeIIPhase τP p)
  let α : ℕ → ℂ := fun n => typeIIPhase σ n*χQ (n : ZMod qQ)
  let β : ℕ → ℂ := fun n => (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ)*
    χM (n : ZMod qM)*typeIIPhase ν n
  let γ := candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
    tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n)
  have hp := hP g (Finset.mem_union_left _ hg) qRat hqRat0 hqRat
  have hq := hQ Alo Blo qRat hqRat0 hqRat
  have hm := hM S aM v lo hi qRat hqRat0 hqRat
  have hFpos : ∀ n ∈ F, 0 < n := by
    intro n hn
    have hnR : (0 : ℝ) < n := zero_lt_one.trans_le (hUT.trans (hFband n hn).1)
    exact_mod_cast hnR
  have hδ : ∀ n, ‖δ n‖ ≤ L := by
    intro n
    have hvM := (hpool.2.2.2.2.2 g (Finset.mem_union_left _ hg)).1
    have hmass : 0 < ∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ) := hvpool.trans_le hvM
    calc
      ‖δ n‖ ≤ ‖(1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))‖*1 := by
        dsimp only [δ]
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (character_typeIIPhase_norm_le χP τP n) (norm_nonneg _)
      _ = 1/(∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) := by
        simp only [norm_div,norm_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hmass,mul_one]
      _ ≤ 1/vpool := one_div_le_one_div_of_le hvpool hvM
      _ ≤ L := hpoolInv
  have hα : ∀ n, ‖α n‖ ≤ 1 := by
    intro n
    simpa only [α,norm_mul,typeIIPhase_norm,one_mul] using χQ.norm_le_one (n : ZMod qQ)
  have hβ : ∀ n, ‖β n‖ ≤ 1 := by
    intro n
    simpa only [β,norm_mul,typeIIPhase_norm,mul_one,one_mul] using
      mul_le_mul (hm.1 n) (χM.norm_le_one (n : ZMod qM)) (norm_nonneg _) zero_le_one
  have hγcap : ∀ n, ‖γ n‖ ≤ L^(Cres+B) :=
    hres B r jStar hr hj take hkeep ξ tmarks umarks big b κ _ ht hb hκ
      (fun n => character_typeIIPhase_norm_le χT τT n)
  have hcap : L*1*1*L^(Cres+B) ≤ L^(Cres+B+1) := by
    rw [mul_one,mul_one,Real.rpow_add hL (Cres+B) 1,Real.rpow_one]
    exact le_of_eq (mul_comm _ _)
  have hbox := hcutoff qRat hqRat0 aRat Y hY hYhi s
    (roughBand Alo Blo (Real.exp (Real.sqrt L)))
    ((Ioc lo hi).filter (fun n =>
      (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ) ≠ 0))
    F δ α β γ L 1 1 (L^(Cres+B)) hL.le zero_le_one zero_le_one
    (Real.rpow_nonneg hL.le _) hcap
    (fun p hp' => (hp p (hs hp')).1.pos) (fun n hn => (hq n hn).1)
    (fun n hn => (hm.2 n hn).1) hFpos
    (fun p hp' => (hp p (hs hp')).2) (fun n hn => (hq n hn).2)
    (fun n hn => (hm.2 n hn).2)
    (fun n _ => hδ n) (fun n _ => hα n) (fun n _ => hβ n) (fun n _ => hγcap n)
    hgeom R w hR (hRY.trans (le_mul_of_one_le_left (zero_le_one.trans hY) hL1)) (by
      intro dRat hdRat ψ u hu
      have hshift : |w+2*Real.pi*u| ≤ L^(max W ρ+1) := by
        have hf := hfreq w 0 u hw (by simpa using Real.rpow_nonneg hL.le W)
          (by simpa only [Real.norm_eq_abs] using hu)
        simpa only [add_zero,abs_neg] using hf
      have henergy := @hdecay r jStar hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ
        g hg s Y P R hs hne hY hYlo hYhi hR hRY hsp qP qT χP χT τP τT
        lo hi F UM UT hUM hUT hMband hFband aM v ν qM hqMInst χM hvM hqM hν
        UQ Alo Blo σ qQ hqQInst χQ hUQ hQA hAB hBQ hqQ hσ
        hmeanScale hresScale hlog qRat dRat hqRat0 (Nat.pos_of_mem_divisors hdRat)
        (Nat.dvd_of_mem_divisors hdRat) hqRat ψ (w+2*Real.pi*u) hshift
      simpa only [δ,α,β,γ,rational_normalized_phase_twist,rational_phase_left_twist,
        rational_weighted_phase_twist,candidate_selected_rational_multiplier,add_assoc] using henergy)
  exact hbox.trans (rational_box_cubic_cost hL hqRat)

end Bounty.WeakZeroFree
