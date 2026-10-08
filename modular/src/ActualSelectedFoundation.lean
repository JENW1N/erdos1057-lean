import ActualSelectedInputs

/-! Fixed parameters, finite selections, and original cap estimates in one coherent input environment. -/

open scoped Topology BigOperators Classical

-- Source module: MixedFullScalarBudget
section

/- Absorb the complete clean and dirty prefactor before iterating signed edges. -/

open Finset Filter
namespace Bounty

theorem exists_candidate_mixed_full_scalar_budget {scale : ℝ} (hs : 0 < scale)
    (ell : ℕ) (hell : 0 < ell) (J₀ : ℕ) (A C K G : ℝ)
    (hA : 0 ≤ A) (hK : 0 ≤ K) :
    ∃ J : ℕ, J₀ ≤ J ∧ ∀ᶠ L : ℝ in atTop, ∀ F : ℝ, F ≤ L^C →
      A^(candidateSmallPIndices scale L).card *
        (L^(-(G+candidateMixedRareCostExponent A 1+1)) +
          2*F*Real.sqrt ((⌈L^2⌉₊ : ℝ)/
            (((J+ell).choose ell)^(candidateSmallPIndices scale L).card : ℕ))*
            Real.sqrt (K^(candidateBigPIndices scale L).card)) ≤ L^(-G) := by
  obtain ⟨J,hJ,_,hrare⟩ := exists_candidate_mixed_rare_parameter hs ell hell J₀ A K C G hA hK
  refine ⟨J,hJ,?_⟩
  filter_upwards [hrare,eventually_candidate_mixed_conditioning_cost_le hs,
    eventually_gt_atTop (0 : ℝ)] with L hr hc hL
  intro F hF
  have hAcost : A^(candidateSmallPIndices scale L).card ≤
      L^candidateMixedRareCostExponent A 1 := by
    simpa only [one_pow, Real.sqrt_one, mul_one] using hc A 1 hA (by norm_num)
  have hclean : A^(candidateSmallPIndices scale L).card *
      L^(-(G+candidateMixedRareCostExponent A 1+1)) ≤ L^(-(G+1)) := by
    calc
      _ ≤ L^candidateMixedRareCostExponent A 1 *
          L^(-(G+candidateMixedRareCostExponent A 1+1)) :=
        mul_le_mul_of_nonneg_right hAcost (Real.rpow_nonneg hL.le _)
      _ = _ := by rw [← Real.rpow_add hL]; congr 1; ring
  have hdirty : A^(candidateSmallPIndices scale L).card *
      (2*F*Real.sqrt ((⌈L^2⌉₊ : ℝ)/
        (((J+ell).choose ell)^(candidateSmallPIndices scale L).card : ℕ))*
        Real.sqrt (K^(candidateBigPIndices scale L).card)) ≤
      2*L^C*(A^(candidateSmallPIndices scale L).card*
        Real.sqrt (K^(candidateBigPIndices scale L).card))*
        Real.sqrt ((⌈L^2⌉₊ : ℝ)/
          (((J+ell).choose ell)^(candidateSmallPIndices scale L).card : ℕ)) := by
    calc
      _ ≤ A^(candidateSmallPIndices scale L).card *
          (2*L^C*Real.sqrt ((⌈L^2⌉₊ : ℝ)/
            (((J+ell).choose ell)^(candidateSmallPIndices scale L).card : ℕ))*
            Real.sqrt (K^(candidateBigPIndices scale L).card)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hF (by norm_num))
              (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)) (pow_nonneg hA _)
      _ = _ := by ring
  rw [mul_add]
  exact (add_le_add hclean hdirty).trans hr.2

end Bounty

end


-- Source module: RootLowRankBudget
section

/- One fixed omission parameter controls all costs in the original low-rank word bound. -/

open Finset Filter
namespace Bounty

theorem exists_candidate_root_low_rank_budget {scale : ℝ} (hs : 0 < scale)
    (ell : ℕ) (hell : 0 < ell) (J₀ : ℕ) (A Cbad C K Kghost G : ℝ)
    (hA : 0 ≤ A) (hCbad : 0 ≤ Cbad) (hK : 0 ≤ K) (hKghost : 0 ≤ Kghost) (hG : 0 ≤ G) :
    ∃ J : ℕ, J₀ ≤ J ∧ ∀ᶠ L : ℝ in atTop,
      ∀ F : ℝ, 0 ≤ F → F ≤ L^C → ∀ cap : ℕ, cap ≤ Nat.ceil (L^2) →
      let small := (candidateSmallPIndices scale L).card
      let big := (candidateBigPIndices scale L).card
      let decay := A^small * (L^(-(G+candidateMixedRareCostExponent A 1+1)) +
        2*F*Real.sqrt ((cap : ℝ)/(((J+ell).choose ell)^small : ℕ))*Real.sqrt (K^big))
      decay ≤ L^(-G) ∧
      max decay (F*Cbad^small*Real.sqrt (K^big)) ≤
        L^(max 0 (C+candidateMixedRareCostExponent Cbad K)) ∧
      Real.sqrt (Kghost^big) ≤ L^(max 0 (candidateMixedRareCostExponent 1 Kghost)) ∧
      (2 : ℝ)^((J+ell)*big) ≤
        L^(max 0 (candidateMixedRareCostExponent 1 ((2 : ℝ)^(2*(J+ell))))) := by
  obtain ⟨J,hJ,hbudget⟩ := exists_candidate_mixed_full_scalar_budget hs ell hell J₀ A C K G hA hK
  refine ⟨J,hJ,?_⟩
  filter_upwards [hbudget, eventually_candidate_mixed_conditioning_cost_le hs,
    eventually_ge_atTop (1 : ℝ)] with L hbudget hcost hL
  intro F hF0 hF cap hcap small big decay
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hsqrt : Real.sqrt ((cap : ℝ)/(((J+ell).choose ell)^small : ℕ)) ≤
      Real.sqrt ((Nat.ceil (L^2) : ℝ)/(((J+ell).choose ell)^small : ℕ)) := by
    exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (Nat.cast_le.mpr hcap) (Nat.cast_nonneg _))
  have hdecay : decay ≤ L^(-G) := by
    apply le_trans ?_ (hbudget F hF)
    apply mul_le_mul_of_nonneg_left ?_ (pow_nonneg hA _)
    apply add_le_add (le_refl _)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsqrt (by positivity)) (Real.sqrt_nonneg _)
  have hbad : F*Cbad^small*Real.sqrt (K^big) ≤
      L^(C+candidateMixedRareCostExponent Cbad K) := by
    calc
      _ = F*(Cbad^small*Real.sqrt (K^big)) := by ring
      _ ≤ L^C*L^(candidateMixedRareCostExponent Cbad K) :=
        mul_le_mul hF (hcost Cbad K hCbad hK)
          (mul_nonneg (pow_nonneg hCbad _) (Real.sqrt_nonneg _)) (Real.rpow_nonneg hL0.le _)
      _ = _ := (Real.rpow_add hL0 _ _).symm
  have hghost : Real.sqrt (Kghost^big) ≤ L^(candidateMixedRareCostExponent 1 Kghost) := by
    simpa only [one_pow, one_mul] using hcost 1 Kghost (by norm_num) hKghost
  have hmass : (2 : ℝ)^((J+ell)*big) ≤
      L^(candidateMixedRareCostExponent 1 ((2 : ℝ)^(2*(J+ell)))) := by
    have hm := hcost 1 ((2 : ℝ)^(2*(J+ell))) (by norm_num) (by positivity)
    simp only [one_pow, one_mul] at hm
    have heq : Real.sqrt (((2 : ℝ)^(2*(J+ell)))^big) = (2 : ℝ)^((J+ell)*big) := by
      rw [← pow_mul, show 2*(J+ell)*big = ((J+ell)*big)*2 by ring, pow_mul,
        Real.sqrt_sq (by positivity)]
    rwa [heq] at hm
  refine ⟨hdecay, max_le ?_ ?_, ?_, ?_⟩
  · exact hdecay.trans (Real.rpow_le_rpow_of_exponent_le hL
      ((neg_nonpos.mpr hG).trans (le_max_left _ _)))
  · exact hbad.trans (Real.rpow_le_rpow_of_exponent_le hL (le_max_right _ _))
  · exact hghost.trans (Real.rpow_le_rpow_of_exponent_le hL (le_max_right _ _))
  · exact hmass.trans (Real.rpow_le_rpow_of_exponent_le hL (le_max_right _ _))

end Bounty

end


-- Source module: RootSelectedFamilyEnvelope
section

/- A fixed probe count gives a candidate family envelope independent of the omission parameter. -/

open Finset Filter
namespace Bounty

theorem eventually_candidate_big_family_envelope {scale q x : ℝ}
    (hs : 0 < scale) (hq : 0 ≤ q) (hx : 0 ≤ x) (m : ℕ) :
    let a : ℝ := 2 / (5 * Real.log 2)
    let C : ℝ := (m : ℝ) * a * Real.log 2 + 4*q + 2*x + 1
    ∀ᶠ L : ℝ in atTop, ∀ (Q : ℕ) (ξ : ℝ),
      (Q : ℝ) ≤ L^q → L^(-x) ≤ ξ →
      0 ≤ repeatedBigFamilyEnvelope (candidateBigPIndices scale L).card m Q ξ ∧
      repeatedBigFamilyEnvelope (candidateBigPIndices scale L).card m Q ξ ≤ L^C := by
  intro a C
  obtain ⟨v, V, _, _, hpools⟩ := exists_candidate_P_pool_bounds hs
  filter_upwards [hpools, eventually_ge_atTop (2 : ℝ)] with L hpools hL
  intro Q ξ hQ hξ
  have hL0 : 0 < L := by linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hcard : ((candidateBigPIndices scale L).card : ℝ) ≤ a * Real.log L := by
    apply (Nat.cast_le.mpr (card_le_card
      (show candidateBigPIndices scale L ⊆ candidatePIndices scale L from subset_union_right))).trans
    exact hpools.2.2.2.1
  refine ⟨repeated_big_family_envelope_nonneg _ _ _ _, ?_⟩
  calc
    _ ≤ 2 * L^((m : ℝ)*a*Real.log 2 + 4*q + 2*x) :=
      repeated_big_family_envelope_le _ m Q (by linarith) ha hq hx hcard hQ hξ
    _ ≤ L * L^((m : ℝ)*a*Real.log 2 + 4*q + 2*x) :=
      mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hL0.le _)
    _ = L^C := by rw [mul_comm, ← Real.rpow_add_one hL0.ne']

end Bounty

end


-- Source module: MixedFullParameterOrder
section

/- The clean accuracy and probe count precede envelope costs and the omission parameter. -/

open Finset Filter
namespace Bounty

theorem exists_candidate_mixed_full_parameter_order {scale beta : ℝ}
    (hs : 0 < scale) (hbeta : 0 < beta) (ell : ℕ) (hell : 0 < ell)
    (A a G : ℝ) (hA : 0 ≤ A) :
    ∃ (E : ℝ) (m : ℕ) (D : ℝ),
      E = G+candidateMixedRareCostExponent A 1+1 ∧ ell ≤ m ∧ 0 ≤ D ∧
      beta*Real.log ((ell : ℝ)^ell/(m : ℝ)^ell)/2 ≤ -(E+2) ∧
      (m : ℝ)*a*Real.log 3+E+2 ≤ D ∧
      ∀ (C K : ℝ), 0 ≤ K → ∀ J₀ : ℕ, ∃ J : ℕ, max m J₀ ≤ J ∧
        ∀ᶠ L : ℝ in atTop, ∀ F : ℝ, F ≤ L^C →
          A^(candidateSmallPIndices scale L).card *
            (L^(-E) + 2*F*Real.sqrt ((⌈L^2⌉₊ : ℝ)/
              (((J+ell).choose ell)^(candidateSmallPIndices scale L).card : ℕ))*
              Real.sqrt (K^(candidateBigPIndices scale L).card)) ≤ L^(-G) := by
  let E := G+candidateMixedRareCostExponent A 1+1
  obtain ⟨m,D,hm,hD,hgap,hDgap⟩ := exists_repeated_big_clean_parameters ell hell a E hbeta
  refine ⟨E,m,D,rfl,hm,hD,hgap,hDgap,?_⟩
  intro C K hK J₀
  exact exists_candidate_mixed_full_scalar_budget hs ell hell (max m J₀) A C K G hA hK

end Bounty

end


-- Source module: RootSelectedParameterOrder
section

/- Choose the clean accuracy and frequency exponents before the fixed omission parameter. -/

open Finset Filter
namespace Bounty

theorem exists_candidate_selected_parameter_order {scale beta : ℝ}
    (hs : 0 < scale) (hbeta : 0 < beta) (ell : ℕ) (hell : 0 < ell)
    (A Cbad Ework s z ε ρ u v vmax Kghost : ℝ)
    (hA : 0 ≤ A) (hCbad : 0 ≤ Cbad) (hEwork : 0 ≤ Ework)
    (hs' : 0 ≤ s) (hz : 0 ≤ z) (hε : 0 < ε) (hKghost : 0 ≤ Kghost) :
    let a : ℝ := 2 / (5 * Real.log 2)
    let Cv := max 0 (candidateMixedRareCostExponent 1 Kghost)
    let G := Ework + Cv + 2
    0 ≤ G ∧ Ework + Cv + 2 ≤ G ∧
    ∃ (E : ℝ) (m : ℕ) (D : ℝ),
      E = G + candidateMixedRareCostExponent A 1 + 1 ∧
      ell ≤ m ∧ 0 ≤ D ∧
      beta * Real.log ((ell : ℝ)^ell / (m : ℝ)^ell) / 2 ≤ -(E+2) ∧
      (m : ℝ)*a*Real.log 3 + E+2 ≤ D ∧
      let κ := a * Real.log (primeFiberFactorBound v m)
      let s₁ := s + ε
      let A₀ := D + 2*(s₁+1)
      let q := 2*κ + (s₁+1) + 2*A₀ + 3
      let w := 4*q + max z q + A₀ + 2
      let x := (s₁+w+2) + 2*A₀ + 2
      let C := (m : ℝ)*a*Real.log 2 + 4*q + 2*x + 1
      let Kedge := unrestrictedEdgeEnergyBound ρ u v vmax (ell+m)
      let Ca := max 0 (C + candidateMixedRareCostExponent Cbad Kedge)
      0 ≤ q ∧ 0 ≤ w ∧ 0 ≤ x ∧ 0 ≤ C ∧ 0 ≤ Ca ∧ 0 ≤ Cv ∧
      ∀ J₀ : ℕ, ∃ J : ℕ, max m J₀ ≤ J ∧
        let Ch := max 0 (candidateMixedRareCostExponent 1 ((2 : ℝ)^(2*(J+ell))))
        0 ≤ Ch ∧ ∀ᶠ L : ℝ in atTop,
          let Q := ⌊L^q⌋₊
          let ξ := L^(-x)
          let small := (candidateSmallPIndices scale L).card
          let big := (candidateBigPIndices scale L).card
          let F := repeatedBigFamilyEnvelope big m Q ξ
          0 ≤ F ∧ F ≤ L^C ∧ ∀ cap : ℕ, cap ≤ Nat.ceil (L^2) →
            let decay := A^small * (L^(-E) +
              2*F*Real.sqrt ((cap : ℝ)/(((J+ell).choose ell)^small : ℕ))*Real.sqrt (Kedge^big))
            decay ≤ L^(-G) ∧ max decay (F*Cbad^small*Real.sqrt (Kedge^big)) ≤ L^Ca ∧
              Real.sqrt (Kghost^big) ≤ L^Cv ∧ (2 : ℝ)^((J+ell)*big) ≤ L^Ch := by
  intro a Cv G
  have hG : 0 ≤ G := by dsimp [G]; positivity
  refine ⟨hG,le_rfl,?_⟩
  let E := G + candidateMixedRareCostExponent A 1 + 1
  have ha : 0 ≤ a := by dsimp [a]; positivity
  obtain ⟨m,D,hm,hD,hgap,hDgap⟩ := exists_repeated_big_clean_parameters ell hell a E hbeta
  refine ⟨E,m,D,rfl,hm,hD,hgap,hDgap,?_⟩
  intro κ s₁ A₀ q w x C Kedge Ca
  have hexp := repeated_big_prime_kernel_exponents_nonneg s z a v D ε m hs' hz ha hD hε.le
  have hq : 0 ≤ q := hexp.2.2.2.1
  have hw : 0 ≤ w := hexp.2.2.2.2.1
  have hx : 0 ≤ x := hexp.2.2.2.2.2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨hq,hw,hx,hC,le_max_left _ _,le_max_left _ _,?_⟩
  intro J₀
  have hKedge : 0 ≤ Kedge := unrestrictedEdgeEnergyBound_nonneg ρ u v vmax (ell+m)
  obtain ⟨J,hJ,hbudget⟩ := exists_candidate_root_low_rank_budget hs ell hell (max m J₀)
    A Cbad C Kedge Kghost G hA hCbad hKedge hKghost hG
  refine ⟨J,hJ,?_⟩
  intro Ch
  refine ⟨le_max_left _ _,?_⟩
  filter_upwards [hbudget, eventually_candidate_big_family_envelope hs hq hx m,
    eventually_gt_atTop (0 : ℝ)] with L hbudget hfamily hL
  intro Q ξ small big F
  have hF := hfamily Q ξ (Nat.floor_le (Real.rpow_nonneg hL.le _)) le_rfl
  refine ⟨hF.1,hF.2,?_⟩
  intro cap hcap
  exact hbudget F hF.1 hF.2 cap hcap

end Bounty

end


-- Source module: RootGhostParameters
section

/- Fixed admissible ghost parameters for the actual one-half endpoint schedule. -/

namespace Bounty

theorem root_ghost_scalar_budget {q W vmax : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 3/4)
    (hvmax : 0 ≤ vmax) (hW0 : 0 ≤ W) (hW : W ≤ 2*vmax+1) :
    q/(9/10 : ℝ)^2 + (((1-q)*W)/(9/10 : ℝ))/(100*(vmax+1)) ≤ 1 := by
  have hq : q/(9/10 : ℝ)^2 ≤ 25/27 := by
    apply (div_le_iff₀ (by norm_num)).2
    nlinarith
  have hmul : (1-q)*W ≤ W := by nlinarith
  have hterm : (((1-q)*W)/(9/10 : ℝ))/(100*(vmax+1)) ≤ 1/45 := by
    rw [div_div]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith
  linarith

theorem physical_endpoint_half_schedule_le_three_quarters (edges j : ℕ) :
    physicalEndpointSchedule (1/2) edges j ≤ (3/4 : ℝ) := by
  have hs : Real.sqrt (1/2 : ℝ) ≤ 3/4 := by
    apply (Real.sqrt_le_iff).2
    norm_num
  unfold physicalEndpointSchedule
  split_ifs
  · exact hs
  · norm_num

theorem physical_endpoint_half_ghost_budgets {vmax : ℝ} (hvmax : 0 ≤ vmax)
    (edges : ℕ) :
    1 < 100*(vmax+1) ∧ ∀ j : ℕ,
      physicalEndpointSchedule (1/2) edges j/(9/10 : ℝ)^2 +
        ((1-physicalEndpointSchedule (1/2) edges j)/(9/10 : ℝ))/(100*(vmax+1)) ≤ 1 ∧
      ∀ V : ℝ, 0 ≤ V → V ≤ vmax →
        physicalEndpointSchedule (1/2) edges j/(9/10 : ℝ)^2 +
          (((1-physicalEndpointSchedule (1/2) edges j)*(2*V))/(9/10 : ℝ))/(100*(vmax+1)) ≤ 1 := by
  refine ⟨by linarith, fun j => ?_⟩
  have hq0 := (physical_endpoint_schedule_unit (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) ≤ 1) edges j).1
  have hq1 := physical_endpoint_half_schedule_le_three_quarters edges j
  constructor
  · simpa only [mul_one] using root_ghost_scalar_budget hq0 hq1 hvmax
      (show (0 : ℝ) ≤ 1 by norm_num) (show (1 : ℝ) ≤ 2*vmax+1 by linarith)
  · intro V hV0 hV
    exact root_ghost_scalar_budget hq0 hq1 hvmax (by positivity) (by linarith)

end Bounty

end


-- Source module: FiniteGroupSplit
section

/- Two disjoint finite selections each containing at least one quarter of the pool. -/

open Finset
namespace Bounty

theorem exists_disjoint_quarter_subsets {G : Type*} [DecidableEq G]
    (s : Finset G) (hs : 2 ≤ s.card) :
    ∃ r t : Finset G, r ⊆ s ∧ t ⊆ s ∧ Disjoint r t ∧
      s.card ≤ 4 * r.card ∧ s.card ≤ 4 * t.card := by
  obtain ⟨r, hrs, hr⟩ := exists_subset_card_eq (Nat.div_le_self s.card 2)
  refine ⟨r, s \ r, hrs, sdiff_subset, ?_, ?_, ?_⟩
  · exact disjoint_left.mpr (fun _ hi hj => (mem_sdiff.mp hj).2 hi)
  · omega
  · rw [card_sdiff_of_subset hrs, hr]
    omega

end Bounty

end


-- Source module: RootProbeSelection
section

/- A common initial probe set chosen without reference to any analytic datum. -/

namespace Bounty

theorem exists_uniform_card_probes (G : Type*) {m J : ℕ} (hmJ : m ≤ J) :
    ∃ probes : G → Finset (Fin J), (∀ g, (probes g).card = m) ∧
      ∀ g h, probes g = probes h := by
  refine ⟨fun _ => Finset.univ.map (Fin.castLEEmb hmJ), ?_, ?_⟩
  · intro g
    simp
  · intro g h
    rfl

end Bounty

end


-- Source module: CandidateRootSelection
section

/- Disjoint logarithmically large big-prime group families for the selected root moment. -/

open Filter Finset
open scoped Classical
namespace Bounty

theorem candidate_selection_beta_pos : 0 < (1 / (80 * Real.log 2) : ℝ) := by
  positivity

theorem eventually_candidate_disjoint_big_selections {scale : ℝ} (hscale : 0 < scale) :
    ∀ᶠ L : ℝ in atTop,
      ∃ r t : Finset (candidatePIndices scale L), Disjoint r t ∧
        (∀ g ∈ r ∪ t, g.val ∈ candidateBigPIndices scale L) ∧
        (1 / (80 * Real.log 2)) * Real.log L ≤ (r.card : ℝ) ∧
        (1 / (80 * Real.log 2)) * Real.log L ≤ (t.card : ℝ) := by
  obtain ⟨v, V, _, _, hpool⟩ := exists_candidate_P_pool_bounds hscale
  filter_upwards [hpool, Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (40 * Real.log 2))] with L hpool hlog
  let emb : (candidateBigPIndices scale L) ↪ (candidatePIndices scale L) :=
    ⟨fun i => ⟨i.val, mem_union_right _ i.property⟩,
      fun a b h => Subtype.ext (congrArg (fun x : candidatePIndices scale L => x.val) h)⟩
  let pool := (candidateBigPIndices scale L).attach.map emb
  have hcard : pool.card = (candidateBigPIndices scale L).card := by
    simp [pool]
  have hmem : ∀ g ∈ pool, g.val ∈ candidateBigPIndices scale L := by
    intro g hg
    obtain ⟨i, _, rfl⟩ := mem_map.mp hg
    exact i.property
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbig := hpool.2.2.1
  have htwo : (2 : ℝ) ≤ (pool.card : ℝ) := by
    rw [hcard]
    calc
      2 = (1 / (20 * Real.log 2)) * (40 * Real.log 2) := by field_simp; ring
      _ ≤ (1 / (20 * Real.log 2)) * Real.log L :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ _ := hbig
  obtain ⟨r, t, hr, ht, hrt, hrc, htc⟩ :=
    exists_disjoint_quarter_subsets pool (by exact_mod_cast htwo)
  have hrc' : (pool.card : ℝ) ≤ 4 * (r.card : ℝ) := by exact_mod_cast hrc
  have htc' : (pool.card : ℝ) ≤ 4 * (t.card : ℝ) := by exact_mod_cast htc
  have hcoef : (1 / (20 * Real.log 2) : ℝ) = 4 * (1 / (80 * Real.log 2)) := by ring
  rw [← hcard, hcoef] at hbig
  refine ⟨r, t, hrt, ?_, ?_, ?_⟩
  · intro g hg
    exact hmem g ((mem_union.mp hg).elim (hr ·) (ht ·))
  · nlinarith
  · nlinarith

end Bounty

end


-- Source module: CandidateBigBandEndpoints
section

/- Actual endpoint bounds for every selected big candidate band. -/

open Filter Finset
namespace Bounty

theorem eventually_candidate_big_band_endpoints {scale : ℝ} (hscale : 0 < scale) :
    ∀ᶠ L : ℝ in atTop, ∀ j ∈ candidateBigPIndices scale L,
      ∃ a b : ℝ, candidatePBand (scale * L) j = primeBand a b ∧
        Real.exp (L ^ (3/10 : ℝ)) ≤ a ∧ b ≤ Real.exp (L ^ (2/5 : ℝ)) ∧ 0 ≤ b := by
  have hind := eventually_geometric_log_indices_nonneg
    (α := (3/10 : ℝ)) (β := (2/5 : ℝ)) (c₃ := (3/2 : ℝ)) (c₄ := (9/5 : ℝ))
    (by norm_num) (by norm_num) hscale (by norm_num) (by norm_num)
  filter_upwards [hind, eventually_gt_atTop (0 : ℝ)] with L hind hL
  intro j hj
  obtain ⟨hlo, hhi⟩ := dyadic_scale_bounds_of_mem (mul_pos hscale hL)
    (by norm_num : (0 : ℝ) < 3/2) (by norm_num : (0 : ℝ) < 9/5)
    (Real.rpow_pos_of_pos hL (3/10 : ℝ)) (Real.rpow_pos_of_pos hL (2/5 : ℝ)) hind.2 hj
  exact ⟨Real.exp ((3/2) * (scale * L) / 2^j), Real.exp ((9/5) * (scale * L) / 2^j),
    rfl, Real.exp_le_exp.mpr hlo, Real.exp_le_exp.mpr hhi, (Real.exp_pos _).le⟩

end Bounty

end


-- Source module: CandidateBigCleanGroups
section

/- Concrete big-group data for the clean prime row with c=1/4 and s=1/2. -/

open Filter Finset
open scoped Classical
namespace Bounty

theorem exists_candidate_big_clean_group_data {scale : ℝ} (hscale : 0 < scale) :
    ∃ v V : ℝ, 0 < v ∧ 0 < V ∧ ∀ᶠ L : ℝ in atTop,
      let G := candidateBigPIndices scale L
      let P := fun g : G => candidatePBand (scale * L) g.val
      1 ≤ L ∧ (Fintype.card G : ℝ) ≤ (2 / (5 * Real.log 2)) * Real.log L ∧
      Pairwise (fun g h : G => Disjoint (P g) (P h)) ∧
      (∀ g, v ≤ ∑ p ∈ P g, 1 / (p : ℝ)) ∧
      (∀ g, (∑ p ∈ P g, 1 / (p : ℝ)) ≤ V) ∧
      (∀ g, ∃ a b : ℝ, P g = primeBand a b ∧ Real.exp (L ^ (1/4 : ℝ)) ≤ a ∧ 0 ≤ b) ∧
      (∀ g p, p ∈ P g → p.Prime ∧ Real.log (p : ℝ) ≤ L ^ (1/2 : ℝ) ∧
        Real.exp (L ^ (1/4 : ℝ)) ≤ (p : ℝ)) := by
  obtain ⟨v, V, hv, hV, hpool⟩ := exists_candidate_P_pool_bounds hscale
  refine ⟨v, V, hv, hV, ?_⟩
  filter_upwards [hpool, eventually_candidate_big_band_endpoints hscale] with L hp hb
  intro G P
  have hL := hp.1
  have hsub : candidateBigPIndices scale L ⊆ candidatePIndices scale L := subset_union_right
  have hcard : ((candidateBigPIndices scale L).card : ℝ) ≤
      ((candidatePIndices scale L).card : ℝ) := by exact_mod_cast card_le_card hsub
  have hlo : Real.exp (L ^ (1/4 : ℝ)) ≤ Real.exp (L ^ (3/10 : ℝ)) :=
    Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hL (by norm_num))
  have hhi : Real.exp (L ^ (2/5 : ℝ)) ≤ Real.exp (L ^ (1/2 : ℝ)) :=
    Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hL (by norm_num))
  refine ⟨hL, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (by simpa only [Fintype.card_coe] using hcard.trans hp.2.2.2.1)
  · intro g h hgh
    exact hp.2.2.2.2.1 (fun heq => hgh (Subtype.ext heq))
  · intro g
    exact (hp.2.2.2.2.2 g.val (hsub g.property)).1
  · intro g
    exact (hp.2.2.2.2.2 g.val (hsub g.property)).2.1
  · intro g
    obtain ⟨a, b, heq, ha, _, hb0⟩ := hb g.val g.property
    exact ⟨a, b, heq, hlo.trans ha, hb0⟩
  · intro g p hpg
    obtain ⟨a, b, heq, ha, hbhi, hb0⟩ := hb g.val g.property
    have ha0 := (Real.exp_pos _).le.trans ha
    change p ∈ candidatePBand (scale * L) g.val at hpg
    rw [heq] at hpg
    obtain ⟨hprime, hpa, hpb⟩ := (mem_primeBand_iff ha0 hb0 p).mp hpg
    refine ⟨hprime, ?_, (hlo.trans ha).trans hpa.le⟩
    calc
      Real.log (p : ℝ) ≤ Real.log (Real.exp (L ^ (1/2 : ℝ))) :=
        Real.log_le_log (by exact_mod_cast hprime.pos) (hpb.trans (hbhi.trans hhi))
      _ = _ := Real.log_exp _

end Bounty

end


-- Source module: RootCapMomentBound
section

/- A linear working memory cap absorbs sublinear path costs at the original moment power. -/

open Filter
namespace Bounty

theorem eventually_root_cap_moment_bound {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop, ∀ b lost : ℕ, L ≤ (b : ℝ) →
      (lost : ℝ) ≤ A*L^(13/25 : ℝ)*Real.log L →
      ((2 : ℝ)^(b+1-lost))⁻¹ * Real.exp (A*L^(13/25 : ℝ)*Real.log L) ≤
        (L^(-D))^(2*Nat.ceil (L^(13/25 : ℝ))) := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hC : 0 ≤ A*(1+Real.log 2)+4*D := by positivity
  filter_upwards [eventually_scaled_log_power hC
    (by norm_num : (13/25 : ℝ) < 1) hlog, eventually_ge_atTop (1 : ℝ)] with L hbudget hL
  intro b lost hb hlost
  rw [Real.rpow_one] at hbudget
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hP : 1 ≤ L^(13/25 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hceil : (Nat.ceil (L^(13/25 : ℝ)) : ℝ) ≤ 2*L^(13/25 : ℝ) := by
    have h := Nat.ceil_lt_add_one (Real.rpow_nonneg hL0.le (13/25 : ℝ))
    linarith
  have hAge : A ≤ A*(1+Real.log 2)+4*D := by nlinarith
  have hAX : A*L^(13/25 : ℝ)*Real.log L ≤ L := by
    calc
      _ ≤ (A*(1+Real.log 2)+4*D)*L^(13/25 : ℝ)*Real.log L := by gcongr
      _ ≤ Real.log 2*L := hbudget
      _ ≤ L := by
        have htwo : Real.log 2 ≤ 1 := by
          have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
          linarith
        nlinarith
  have hlb : lost ≤ b+1 := by
    have hle : (lost : ℝ) ≤ b := hlost.trans (hAX.trans hb)
    exact Nat.le_succ_of_le (by exact_mod_cast hle)
  have hsub : ((b+1-lost : ℕ) : ℝ) = (b : ℝ)+1-lost := by
    rw [Nat.cast_sub hlb, Nat.cast_add, Nat.cast_one]
  have hexp : -(Real.log 2*((b : ℝ)+1-lost)) +
      A*L^(13/25 : ℝ)*Real.log L ≤
      Real.log L*(-D*(2*(Nat.ceil (L^(13/25 : ℝ)) : ℝ))) := by
    have hneg : -D*(2*(Nat.ceil (L^(13/25 : ℝ)) : ℝ))*Real.log L ≥
        -4*D*L^(13/25 : ℝ)*Real.log L := by
      have hmul := mul_le_mul_of_nonneg_right hceil (mul_nonneg hD hlogL)
      nlinarith
    have hbl := mul_le_mul_of_nonneg_left hb hlog.le
    have hll := mul_le_mul_of_nonneg_left hlost hlog.le
    nlinarith
  rw [← Real.rpow_natCast (2 : ℝ) (b+1-lost), Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    ← Real.exp_neg, ← Real.exp_add, hsub]
  have hright : (L^(-D))^(2*Nat.ceil (L^(13/25 : ℝ))) =
      Real.exp (Real.log L*(-D*(2*(Nat.ceil (L^(13/25 : ℝ)) : ℝ)))) := by
    rw [← Real.rpow_natCast (L^(-D)) (2*Nat.ceil (L^(13/25 : ℝ))),
      ← Real.rpow_mul hL0.le]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (Real.rpow_def_of_pos hL0 (-D*((2*Nat.ceil (L^(13/25 : ℝ)) : ℕ) : ℝ)))
  rw [hright]
  apply Real.exp_le_exp.mpr
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hexp

end Bounty

end


-- Source module: RootCapEnvelope
section

/- Scalar polynomial envelopes for the original cap error. -/



/- Fixed per-group costs are polynomial when the number of groups is logarithmic. -/

namespace Bounty

theorem constant_pow_le_rpow_of_log_bound {a L C : ℝ} (ha : 1 ≤ a)
    (hL : 0 < L) (n : ℕ) (hn : (n : ℝ) ≤ C*Real.log L) :
    a^n ≤ L^(C*Real.log a) := by
  calc
    _ = Real.exp (Real.log a*(n : ℝ)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (zero_lt_one.trans_le ha)]
    _ ≤ Real.exp (Real.log a*(C*Real.log L)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn (Real.log_nonneg ha))
    _ = _ := by rw [Real.rpow_def_of_pos hL]; congr 1; ring

end Bounty


/- A polynomial cost per step is absorbed at the original moment power. -/

open Filter
namespace Bounty

theorem eventually_root_cap_polynomial_moment_bound {A C H D : ℝ}
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop, ∀ b lost n : ℕ, L ≤ (b : ℝ) →
      (lost : ℝ) ≤ A*L^(13/25 : ℝ)*Real.log L →
      (n : ℝ) ≤ C*L^(13/25 : ℝ) →
      ((2 : ℝ)^(b+1-lost))⁻¹ * L^(H*((n : ℝ)+1)) ≤
        (L^(-D))^(2*Nat.ceil (L^(13/25 : ℝ))) := by
  let K := max A (H*(C+1))
  have hK : 0 ≤ K := hA.trans (le_max_left _ _)
  filter_upwards [eventually_root_cap_moment_bound hK hD,
    eventually_ge_atTop (1 : ℝ)] with L hmain hL
  intro b lost n hb hlost hn
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hP : 1 ≤ L^(13/25 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hlost' : (lost : ℝ) ≤ K*L^(13/25 : ℝ)*Real.log L := by
    apply hlost.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hL0.le _)) hlog
  have hexponent : H*((n : ℝ)+1) ≤ K*L^(13/25 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left (show (n : ℝ)+1 ≤ (C+1)*L^(13/25 : ℝ) by nlinarith) hH
    have hk := mul_le_mul_of_nonneg_right (le_max_right A (H*(C+1))) (Real.rpow_nonneg hL0.le (13/25 : ℝ))
    dsimp only [K]
    nlinarith
  have hpower : L^(H*((n : ℝ)+1)) ≤ Real.exp (K*L^(13/25 : ℝ)*Real.log L) := by
    calc
      _ = Real.exp (Real.log L*(H*((n : ℝ)+1))) := Real.rpow_def_of_pos hL0 _
      _ ≤ Real.exp (Real.log L*(K*L^(13/25 : ℝ))) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hexponent hlog)
      _ = _ := by congr 1; ring
  exact (mul_le_mul_of_nonneg_left hpower (by positivity)).trans (hmain b lost hb hlost')

end Bounty


/- Polynomial bounds for the original phase, step-energy product and initial mass. -/

namespace Bounty

theorem nonnegative_list_product_le_rpow {α : Type*} {L E : ℝ} (hL : 0 < L)
    (steps : List α) (f : α → ℝ)
    (hf : ∀ x ∈ steps, 0 ≤ f x ∧ f x ≤ L^E) :
    (steps.map f).prod ≤ L^(E*(steps.length : ℝ)) := by
  induction steps with
  | nil => simp
  | cons x xs ih =>
    have hx := hf x (by simp)
    have hxs : ∀ y ∈ xs, 0 ≤ f y ∧ f y ≤ L^E := fun y hy => hf y (by simp [hy])
    have hp : 0 ≤ (xs.map f).prod := by
      apply List.prod_nonneg
      intro y hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      exact (hxs z hz).1
    simp only [List.map_cons, List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ L^E * L^(E*(xs.length : ℝ)) :=
        mul_le_mul hx.2 (ih hxs) hp (Real.rpow_nonneg hL.le E)
      _ = _ := by rw [← Real.rpow_add hL]; congr 1; ring

theorem root_polynomial_energy_envelope {α : Type*} {L B E M H mass : ℝ}
    (hL : 1 ≤ L) (hB : 0 ≤ B) (hE : 0 ≤ E) (hM : 0 ≤ M)
    (hH : 0 ≤ H) (hHpow : H ≤ L^B) (hmass : 0 ≤ mass) (hmasspow : mass ≤ L^M)
    (steps : List α) (f : α → ℝ)
    (hf : ∀ x ∈ steps, 0 ≤ f x ∧ f x ≤ L^E) :
    H^steps.length * Real.sqrt (steps.map f).prod * mass ≤
      L^((B+E+M)*((steps.length : ℝ)+1)) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hpow : H^steps.length ≤ L^(B*(steps.length : ℝ)) := by
    calc
      _ ≤ (L^B)^steps.length := pow_le_pow_left₀ hH hHpow _
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
  have hprod := nonnegative_list_product_le_rpow hL0 steps f hf
  have hone : 1 ≤ L^(E*(steps.length : ℝ)) :=
    Real.one_le_rpow hL (mul_nonneg hE (Nat.cast_nonneg _))
  have hsqrt : Real.sqrt (steps.map f).prod ≤ L^(E*(steps.length : ℝ)) :=
    (Real.sqrt_le_sqrt hprod).trans (Real.sqrt_le_self_iff.mpr (Or.inr hone))
  calc
    _ ≤ L^(B*(steps.length : ℝ))*L^(E*(steps.length : ℝ))*L^M :=
      mul_le_mul (mul_le_mul hpow hsqrt (Real.sqrt_nonneg _) (Real.rpow_nonneg hL0.le _))
        hmasspow hmass (mul_nonneg (Real.rpow_nonneg hL0.le _) (Real.rpow_nonneg hL0.le _))
    _ = L^(B*(steps.length : ℝ)+E*(steps.length : ℝ)+M) := by
      rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le hL
      have hn : 0 ≤ (steps.length : ℝ) := Nat.cast_nonneg _
      nlinarith

end Bounty


/- The original scalar cap error is absorbed once its phase, energies and mass are polynomial. -/

open Filter
namespace Bounty

theorem eventually_root_cap_weighted_moment_bound {A C B E M D : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E) (hM : 0 ≤ M) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop, ∀ (b lost : ℕ), L ≤ (b : ℝ) →
      (lost : ℝ) ≤ A*L^(13/25 : ℝ)*Real.log L →
      ∀ (α : Type) (steps : List α) (f : α → ℝ),
      (steps.length : ℝ) ≤ C*L^(13/25 : ℝ) →
      (∀ x ∈ steps, 0 ≤ f x ∧ f x ≤ L^E) →
      ∀ H mass : ℝ, 0 ≤ H → H ≤ L^B → 0 ≤ mass → mass ≤ L^M →
      H^steps.length * ((2 : ℝ)^(b+1-lost))⁻¹ * Real.sqrt (steps.map f).prod * mass ≤
        (L^(-D))^(2*Nat.ceil (L^(13/25 : ℝ))) := by
  filter_upwards [eventually_root_cap_polynomial_moment_bound (C := C) hA
    (show 0 ≤ B+E+M by positivity) hD, eventually_ge_atTop (1 : ℝ)] with L hbound hL
  intro b lost hb hlost α steps f hn hf H mass hH hHpow hmass hmasspow
  have he := root_polynomial_energy_envelope hL hB hE hM hH hHpow hmass hmasspow steps f hf
  calc
    _ = ((2 : ℝ)^(b+1-lost))⁻¹ * (H^steps.length * Real.sqrt (steps.map f).prod * mass) := by ring
    _ ≤ ((2 : ℝ)^(b+1-lost))⁻¹ * L^((B+E+M)*((steps.length : ℝ)+1)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ _ := hbound b lost steps.length hb hlost hn

end Bounty

end


-- Source module: PhysicalMixedWordPathsExtra
section

/- Actual mixed-word paths and their maximum total pending memory. -/

namespace Bounty
section
variable {H K S G I : Type} [Fintype S] [Fintype G] [DecidableEq G]
  {Ps : S → Finset ℕ} {P : G → Type} [∀ g, Fintype (P g)]
  (n : ∀ g, P g → ℕ) {J ell : ℕ} {M : G → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ) (A : I → Type)
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J → SharedActiveLabels P (shared i) → A i → G → ℤ)
  (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)

abbrev PhysicalMixedWordPath (steps : List (Option (H ⊕ K)))
    (s : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B) :=
  FiniteEventPath (PhysicalMixedWordEvent (V := H) (J := J) (ell := ell) n shared B A Δ D)
    (physicalMixedWordTarget n shared B A Δ D kbig) steps s

noncomputable def physicalMixedWordPeak (steps : List (Option (H ⊕ K)))
    (s : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B)
    (p : PhysicalMixedWordPath n shared B A Δ D kbig steps s) : ℕ :=
  finiteEventPathMaximum (PhysicalMixedWordEvent (V := H) (J := J) (ell := ell) n shared B A Δ D)
    (physicalMixedWordTarget n shared B A Δ D kbig)
    (fun s => productTotalMemory s.2) steps s p
end
end Bounty

end


-- Source module: PhysicalMixedWordPositive
section

/- Positive comparison rows for actual mixed words, with an explicit pattern sum. -/

open Finset
open scoped Classical
namespace Bounty
section
variable {H K S G I : Type} [Fintype S] [Fintype G] [DecidableEq G]
  {Ps : S → Finset ℕ} {P : G → Type} [∀ g, Fintype (P g)]
  (n : ∀ g, P g → ℕ) {J ell : ℕ} {M : G → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ) (A : I → Type)
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J → SharedActiveLabels P (shared i) → A i → G → ℤ)
  (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)
  (ω : ∀ i, A i → ℝ) (μ : ∀ g, P g → ℝ)
  (qghost : H → ℝ) (ρ : ℝ) (Vedge Vghost : G → ℝ) (Vs : S → ℝ) (qsmall : ℝ)

noncomputable def physicalMixedWordPositiveWeight (tag : Option (H ⊕ K))
    (s : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B)
    (e : PhysicalMixedWordEvent n shared B A Δ D tag s) : ℝ :=
  |physicalMixedWordWeight n shared B A Δ D kbig (fun i _ => ω i) μ qghost ρ
    (match tag with | some (.inl _) => Vghost | _ => Vedge) Vs (fun _ => qsmall) tag s e|

omit [∀ g, Fintype (P g)] in
theorem physical_mixed_word_edge_weight_nonneg
    (hVs : ∀ s, 0 < Vs s) (hω : ∀ i a, 0 ≤ ω i a)
    (hμ : ∀ g p, 0 ≤ μ g p) (hρ : 0 ≤ ρ) (hV : ∀ g, 0 ≤ Vedge g)
    (k : K) (s : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B)
    (e : PhysicalMixedWordEvent n shared B A Δ D (some (.inr k) : Option (H ⊕ K)) s) :
    0 ≤ physicalMixedWordWeight n shared B A Δ D kbig (fun i _ => ω i) μ qghost ρ
      Vedge Vs (fun _ => qsmall) (some (.inr k)) s e := by
  apply mul_nonneg (hω e.1 e.2.1)
  apply physical_small_big_positive_weight_nonneg Vs hVs
  intro r d x ev
  exact physical_small_big_full_weight_nonneg n (shared e.1) B
    (fun d c => Δ k e.1 d c e.2.1) (fun d c => D k e.1 d c e.2.1)
    μ ρ Vedge hμ hρ hV r d x ev

variable [Fintype I] [∀ i, Fintype (A i)] [∀ g p, NeZero (n g p)]

noncomputable def physicalMixedWordPositiveAction (tag : Option (H ⊕ K))
    (F : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B → ℂ) :=
  let _ : ∀ tag s, Fintype (PhysicalMixedWordEvent (V := H) (ell := ell) n shared B A Δ D tag s) :=
    physicalMixedWordEventFintype n shared B A Δ D
  finiteLocalEventAction (PhysicalMixedWordEvent (ell := ell) n shared B A Δ D)
    (physicalMixedWordPositiveWeight n shared B A Δ D kbig ω μ qghost ρ Vedge Vghost Vs qsmall)
    (physicalMixedWordTarget n shared B A Δ D kbig) tag F

theorem physical_mixed_word_positive_edge_eq
    (hVs : ∀ s, 0 < Vs s) (hω : ∀ i a, 0 ≤ ω i a)
    (hμ : ∀ g p, 0 ≤ μ g p) (hρ : 0 ≤ ρ) (hV : ∀ g, 0 ≤ Vedge g)
    (k : K) (F : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B → ℂ) :
    physicalMixedWordPositiveAction n shared B A Δ D kbig ω μ qghost ρ Vedge Vghost Vs qsmall
      (some (.inr k)) F =
    fun s => ∑ i, physicalSmallBigPathPositiveAction n shared B A (Δ k) (D k) (kbig k)
      ω μ qghost ρ Vedge Vghost Vs qsmall (some (.inr i)) F s := by
  funext s
  simp_rw [physical_small_big_path_positive_edge_eq n shared B A (Δ k) (D k) (kbig k)
    ω μ qghost ρ Vedge Vghost Vs qsmall hVs hω hμ hρ hV]
  unfold physicalMixedWordPositiveAction finiteLocalEventAction
  dsimp only [physicalMixedWordEventFintype, PhysicalMixedWordEvent, PhysicalMixedWordEdge]
  simp only [Fintype.sum_sigma]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro a _
  unfold physicalSmallBigFullPhasedAction physicalSmallBigPhasedAction
  rw [mul_sum]
  apply sum_congr rfl
  intro e _
  have hw := physical_mixed_word_edge_weight_nonneg n shared B A Δ D kbig ω μ qghost ρ
    Vedge Vs qsmall hVs hω hμ hρ hV k s ⟨i, a, e⟩
  dsimp only [physicalMixedWordPositiveWeight]
  rw [abs_of_nonneg hw]
  simp only [physicalMixedWordWeight, physicalMixedWordTarget, Complex.ofReal_mul, mul_one]
  ring
end
end Bounty

end


-- Source module: PhysicalMixedWordVaryingGhost
section

/- Signed mixed paths with a separate ghost birth parameter. This permits
the doubled-ghost comparison while keeping every edge weight unchanged. -/

open Finset
open scoped Classical

namespace Bounty

section
variable {H K S G I : Type} [Fintype S] [Fintype G] [DecidableEq G]
  {Ps : S → Finset ℕ} {P : G → Type} [∀ g, Fintype (P g)]
  (n : ∀ g, P g → ℕ) {J ell : ℕ} {M : G → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ) (A : I → Type)
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J → SharedActiveLabels P (shared i) → A i → G → ℤ)
  (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)
  (ω : ∀ i, A i → ℝ) (μ : ∀ g, P g → ℝ)
  (qghost : H → ℝ) (ρ : ℝ) (Vedge Vghost : G → ℝ) (Vs : S → ℝ) (qsmall : ℝ)

noncomputable def physicalMixedWordVaryingGhostWeight (tag : Option (H ⊕ K))
    (s : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B))
    (e : PhysicalMixedWordEvent (V := H) (J := J) (ell := ell) n shared B A Δ D tag s) : ℝ :=
  physicalMixedWordWeight n shared B A Δ D kbig (fun i _ => ω i) μ qghost ρ
    (match tag with | some (.inl _) => Vghost | _ => Vedge) Vs (fun _ => qsmall) tag s e

omit [∀ g, Fintype (P g)] in
theorem physical_mixed_word_varying_ghost_weight_same (tag : Option (H ⊕ K))
    (s : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B))
    (e : PhysicalMixedWordEvent (V := H) (J := J) (ell := ell) n shared B A Δ D tag s) :
    physicalMixedWordVaryingGhostWeight n shared B A Δ D kbig ω μ qghost ρ
      Vedge Vedge Vs qsmall tag s e =
    physicalMixedWordWeight n shared B A Δ D kbig (fun i _ => ω i) μ qghost ρ
      Vedge Vs (fun _ => qsmall) tag s e := by
  cases tag with
  | none => rfl
  | some tag => cases tag <;> rfl

variable [Fintype I] [∀ g p, NeZero (n g p)] [∀ i, Fintype (A i)]

noncomputable def physicalMixedWordVaryingGhostAction (steps : List (Option (H ⊕ K)))
    (phase : ∀ s, PhysicalMixedWordPath n shared B A Δ D kbig steps s → ℂ)
    (f : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) → ℂ) :=
  let _ : ∀ (tag : Option (H ⊕ K)) s,
      Fintype (PhysicalMixedWordEvent (V := H) (J := J) (ell := ell) n shared B A Δ D tag s) :=
    physicalMixedWordEventFintype (V := H) (J := J) (ell := ell) n shared B A Δ D
  finiteEventPathAction (PhysicalMixedWordEvent (V := H) (J := J) (ell := ell) n shared B A Δ D)
    (physicalMixedWordTarget n shared B A Δ D kbig)
    (physicalMixedWordVaryingGhostWeight n shared B A Δ D kbig ω μ qghost ρ
      Vedge Vghost Vs qsmall) steps phase f

theorem physical_mixed_word_varying_ghost_action_same (steps : List (Option (H ⊕ K)))
    (phase : ∀ s, PhysicalMixedWordPath n shared B A Δ D kbig steps s → ℂ)
    (f : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) → ℂ) :
    physicalMixedWordVaryingGhostAction n shared B A Δ D kbig ω μ qghost ρ
      Vedge Vedge Vs qsmall steps phase f =
    physicalMixedWordPathAction n shared B A Δ D kbig (fun i _ => ω i) μ qghost ρ
      Vedge Vs (fun _ => qsmall) steps phase f := by
  have hw : physicalMixedWordVaryingGhostWeight (J := J) (ell := ell) n shared B A Δ D kbig
      ω μ qghost ρ Vedge Vedge Vs qsmall =
      physicalMixedWordWeight (J := J) (ell := ell) n shared B A Δ D kbig
        (fun i _ => ω i) μ qghost ρ Vedge Vs (fun _ => qsmall) := by
    funext tag s e
    exact physical_mixed_word_varying_ghost_weight_same n shared B A Δ D kbig
      ω μ qghost ρ Vedge Vs qsmall tag s e
  unfold physicalMixedWordVaryingGhostAction physicalMixedWordPathAction
  rw [hw]

theorem physical_mixed_word_varying_ghost_path_norm_le_positive_list
    (steps : List (Option (H ⊕ K)))
    (phase : ∀ s, PhysicalMixedWordPath n shared B A Δ D kbig steps s → ℂ)
    (hphase : ∀ s p, ‖phase s p‖ ≤ 1)
    (f : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) → ℂ)
    (s : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)) :
    ‖physicalMixedWordVaryingGhostAction n shared B A Δ D kbig ω μ qghost ρ
      Vedge Vghost Vs qsmall steps phase f s‖ ≤
    (finiteOperatorListAction
      (physicalMixedWordPositiveAction n shared B A Δ D kbig ω μ qghost ρ
        Vedge Vghost Vs qsmall) steps (complexNormEnvelope f) s).re := by
  let _ : ∀ (tag : Option (H ⊕ K)) s,
      Fintype (PhysicalMixedWordEvent (V := H) (J := J) (ell := ell) n shared B A Δ D tag s) :=
    physicalMixedWordEventFintype (V := H) (J := J) (ell := ell) n shared B A Δ D
  exact finite_event_path_norm_le_abs_list_re (PhysicalMixedWordEvent (V := H) (J := J) (ell := ell) n shared B A Δ D)
    (physicalMixedWordTarget n shared B A Δ D kbig)
    (physicalMixedWordVaryingGhostWeight n shared B A Δ D kbig ω μ qghost ρ
      Vedge Vghost Vs qsmall) steps phase hphase f s

end
end Bounty

end


-- Source module: PhysicalMixedWordComposition
section

/- Whole-path energy from positive local mixed-word estimates. -/

open Finset
open scoped Classical
namespace Bounty

theorem physical_mixed_word_varying_ghost_path_energy_of_local
    {H K S G I : Type} [Fintype S] [Fintype G] [DecidableEq G] [Fintype I]
    {Ps : S → Finset ℕ} [∀ p : PhysicalPrime Ps, NeZero p.2.val]
    {P : G → Type} [∀ g, Fintype (P g)]
    (n : ∀ g, P g → ℕ) [∀ g p, NeZero (n g p)] {J ell : ℕ} {M : G → ℕ}
    (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ) (A : I → Type) [∀ i, Fintype (A i)]
    (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J → SharedActiveLabels P (shared i) → A i → G → ℤ)
    (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)
    (ω : ∀ i, A i → ℝ) (μ : ∀ g, P g → ℝ)
    (qghost : H → ℝ) (ρ : ℝ) (Vedge Vghost : G → ℝ) (Vs : S → ℝ) (qsmall : ℝ)
    (hVs : ∀ s, 0 < Vs s) (hμ : ∀ g p, 0 ≤ μ g p)
    (C : Option (H ⊕ K) → ℝ) (hC : ∀ tag, 0 ≤ C tag)
    (hpreserve : ∀ tag (F : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) → ℂ), (∀ s, ProductMemorySymmetric (fun x => F (s, x))) →
      ∀ s, ProductMemorySymmetric (fun x =>
        physicalMixedWordPositiveAction n shared B A Δ D kbig ω μ qghost ρ
          Vedge Vghost Vs qsmall tag F (s, x)))
    (hlocal : ∀ tag (F : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) → ℂ), (∀ s, ProductMemorySymmetric (fun x => F (s, x))) →
      physicalSmallBigEnergy Vs (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g)))
        (physicalMixedWordPositiveAction n shared B A Δ D kbig ω μ qghost ρ
          Vedge Vghost Vs qsmall tag F) ≤ C tag *
      physicalSmallBigEnergy Vs (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g))) F)
    (steps : List (Option (H ⊕ K)))
    (phase : ∀ s, PhysicalMixedWordPath n shared B A Δ D kbig steps s → ℂ)
    (hphase : ∀ s p, ‖phase s p‖ ≤ 1)
    (f : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) → ℂ)
    (hf : ∀ s, ProductMemorySymmetric (fun x => f (s, x))) :
    physicalSmallBigEnergy Vs (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g)))
      (physicalMixedWordVaryingGhostAction n shared B A Δ D kbig ω μ qghost ρ
        Vedge Vghost Vs qsmall steps phase f) ≤
      (steps.map C).prod *
        physicalSmallBigEnergy Vs (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g))) f := by
  rw [← physical_small_big_energy_eq, ← physical_small_big_energy_eq]
  apply finiteWeightedEnergy_le_of_envelope_domination
    (physicalSmallBigMeasure Vs (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g))))
    (physical_small_big_measure_nonneg Vs hVs _
      (productMemoryWeight_nonneg μ _ hμ (fun g z => hμ g z.1))) f _
    (finiteOperatorListAction
      (physicalMixedWordPositiveAction n shared B A Δ D kbig ω μ qghost ρ
        Vedge Vghost Vs qsmall) steps)
  · intro s
    exact (physical_mixed_word_varying_ghost_path_norm_le_positive_list n shared B A Δ D
      kbig ω μ qghost ρ Vedge Vghost Vs qsmall steps phase hphase f s).trans (Complex.re_le_norm _)
  · apply finite_operator_list_energy_le _
      (fun F => ∀ s, ProductMemorySymmetric (fun x => F (s, x))) _ hpreserve C hC
    · intro tag F hF
      simpa only [physical_small_big_energy_eq] using hlocal tag F hF
    · intro s
      exact complexNormEnvelope_memory_symmetric (fun x => f (s, x)) (hf s)

end Bounty

end


-- Source module: PhysicalMixedWordPositiveIdentities
section

/- The mixed-word ghost and permutation comparisons retain their original rows. -/

open Finset
open scoped Classical
namespace Bounty
section
variable {H K S G I : Type} [Fintype S] [Fintype G] [dG : DecidableEq G]
  {Ps : S → Finset ℕ} {P : G → Type} [∀ g, Fintype (P g)]
  (n : ∀ g, P g → ℕ) {J ell : ℕ} {M : G → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ) (A : I → Type)
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J → SharedActiveLabels P (shared i) → A i → G → ℤ)
  (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)
  (ω : ∀ i, A i → ℝ) (μ : ∀ g, P g → ℝ)
  (qghost : H → ℝ) (ρ : ℝ) (Vedge Vghost : G → ℝ) (Vs : S → ℝ) (qsmall : ℝ)

variable [Fintype I] [∀ i, Fintype (A i)] [∀ g p, NeZero (n g p)]

theorem physical_mixed_word_positive_ghost_eq
    (hμ : ∀ g p, 0 ≤ μ g p) (j : H) (hq : 0 ≤ qghost j)
    (F : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) → ℂ) :
    physicalMixedWordPositiveAction n shared B A Δ D kbig ω μ qghost ρ
      Vedge Vghost Vs qsmall (some (.inl j)) F =
    physicalSmallBigGhostAction (fun g => physicalGhostRetention (n g) (qghost j) ρ)
      (fun g z => |physicalGhostTermination (n g) (qghost j) ρ z|)
      (fun g z => |physicalGhostBirth (n g) (qghost j) ρ (Vghost g) z|)
      (fun g => unrestrictedResidueWeight (μ g)) M B (fun _ _ => 1) F := by
  funext s
  rw [physical_small_big_ghost_eq_event_sum]
  unfold physicalMixedWordPositiveAction finiteLocalEventAction
  apply sum_congr
  · exact congrArg (fun i : Fintype _ => @Finset.univ _ i) (Subsingleton.elim _ _)
  · intro e _
    change CoupledGhostEvent M B s.2 at e
    simp only [physicalMixedWordPositiveWeight, physicalMixedWordWeight,
      physicalMixedWordTarget, mul_one]
    rw [coupledGhostJointEventWeight_abs]
    · intro g z
      unfold physicalGhostRetention
      split_ifs
      · exact div_nonneg hq (sq_nonneg ρ)
      · exact zero_le_one
    · intro g z
      exact hμ g z.1

theorem physical_mixed_word_positive_permutation_eq [dS : DecidableEq S]
    (F : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) → ℂ) :
    physicalMixedWordPositiveAction n shared B A Δ D kbig ω μ qghost ρ
      Vedge Vghost Vs qsmall none F = physicalSmallBigJointAverage F := by
  cases Subsingleton.elim dS (Classical.typeDecidableEq S)
  cases Subsingleton.elim dG (Classical.typeDecidableEq G)
  funext s
  rw [physical_small_big_joint_average_eq_sum]
  unfold physicalMixedWordPositiveAction finiteLocalEventAction
  apply sum_congr
  · exact congrArg (fun i : Fintype _ => @Finset.univ _ i) (Subsingleton.elim _ _)
  · intro e _
    change PhysicalPermutations S J ell × FullActiveSlotPermutations M at e
    dsimp only [physicalMixedWordPositiveWeight, physicalMixedWordWeight,
      physicalMixedWordTarget]
    erw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card (PhysicalPermutations S J ell))))
      (fullActivePermutationWeight_nonneg M e.2))]
    congr 3

end
end Bounty

end


-- Source module: FiniteSumEnergyBound
section

/- A finite-sum energy bound for combining pattern-indexed operators. -/

open Finset
namespace Bounty

theorem finite_weighted_energy_sum_le {X I : Type*} [Fintype X] [Fintype I]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (F : I → X → ℂ) :
    finiteWeightedEnergy w (fun x => ∑ i, F i x) ≤
      (Fintype.card I : ℝ) * ∑ i, finiteWeightedEnergy w (F i) := by
  unfold finiteWeightedEnergy
  calc
    _ ≤ ∑ x, w x * ((Fintype.card I : ℝ) * ∑ i, ‖F i x‖ ^ 2) := by
      apply sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (hw x)
      simpa only [card_univ] using finite_complex_sum_norm_sq_le_card univ (fun i => F i x)
    _ = _ := by
      simp_rw [mul_left_comm (w _) (Fintype.card I : ℝ), mul_sum]
      rw [sum_comm]

end Bounty

end


-- Source module: PhysicalMixedWordLocalEnergy
section

/- The actual mixed edge gains only the explicit squared pattern count. -/

open Finset
open scoped Classical
namespace Bounty

theorem exists_physical_mixed_word_edge_energy_bound
    {qsmall vs : ℝ} (hq0 : 0 ≤ qsmall) (hq1 : qsmall < 1) (hvs : 0 < vs) (ell : ℕ) :
    ∃ Ccond : ℝ, 1 ≤ Ccond ∧ ∀ (H K S G I : Type) [Fintype I] [Fintype S] [DecidableEq S]
      [Fintype G] [DecidableEq G]
      (Ps : S → Finset ℕ) [∀ p : PhysicalPrime Ps, NeZero p.2.val]
      (P : G → Type) [∀ g, Fintype (P g)] (n : ∀ g, P g → ℕ)
      [∀ g p, NeZero (n g p)] (J : ℕ) (M : G → ℕ)
      (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ) (A : I → Type) [∀ i, Fintype (A i)]
      (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J → SharedActiveLabels P (shared i) → A i → G → ℤ)
      (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)
      (ω : ∀ i, A i → ℝ) (μ : ∀ g, P g → ℝ) (qghost : H → ℝ) (ρ : ℝ)
      (Vedge Vghost : G → ℝ) (Vs : S → ℝ), (∀ s, vs ≤ Vs s) →
      (∀ k a, 0 ≤ ω k a) → (∀ k, ∑ a, ω k a ≤ 1) →
      ∀ (v vmin vmax : ℝ), 0 < ρ → ρ < 1 → 1 < v → 0 < vmin →
      (∀ g, vmin ≤ Vedge g) → (∀ g, Vedge g ≤ vmax) →
      (∀ g p, 0 ≤ μ g p) → (∀ g, ∑ p, μ g p ≤ 2) →
      ∀ (T : ℕ), (∀ i g, (shared i g)ᶜ.card ≤ T) →
      ∀ (k : K) (F : PhysicalSmallBigState Ps J ell
        (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) → ℂ),
      (∀ s, ProductMemorySymmetric (fun x => F (s, x))) →
      physicalSmallBigEnergy Vs (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g)))
        (physicalMixedWordPositiveAction n shared B A Δ D kbig ω μ qghost ρ
          Vedge Vghost Vs qsmall (some (.inr k)) F) ≤
        (Fintype.card I : ℝ) ^ 2 *
          (Ccond ^ (2 * Fintype.card S) * unrestrictedEdgeEnergyBound ρ v vmin vmax T ^ Fintype.card G) *
          physicalSmallBigEnergy Vs (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g))) F := by
  obtain ⟨Ccond, hCcond, hbound⟩ := exists_physical_small_big_path_edge_energy_bound hq0 hq1 hvs ell
  refine ⟨Ccond, hCcond, ?_⟩
  intro H K S G I _ _ dS _ dG
  cases Subsingleton.elim dS (Classical.typeDecidableEq S)
  cases Subsingleton.elim dG (Classical.typeDecidableEq G)
  intro Ps _ P _ n _ J M shared B A _ Δ D kbig ω μ qghost ρ Vedge Vghost Vs hVs
    hω hωmass v vmin vmax hρ0 hρ1 hv hvmin hVlo hVhi hμ hmass T ht k F hF
  have hVs' : ∀ s, 0 < Vs s := fun s => hvs.trans_le (hVs s)
  erw [physical_mixed_word_positive_edge_eq n shared B A Δ D kbig ω μ qghost ρ
    Vedge Vghost Vs qsmall hVs' hω hμ hρ0.le (fun g => (hvmin.trans_le (hVlo g)).le) k F]
  have hs := finite_weighted_energy_sum_le
    (physicalSmallBigMeasure Vs (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g))))
    (physical_small_big_measure_nonneg Vs hVs' _
      (productMemoryWeight_nonneg μ _ hμ (fun g z => hμ g z.1)))
    (fun i => physicalSmallBigPathPositiveAction n shared B A (Δ k) (D k) (kbig k)
      ω μ qghost ρ Vedge Vghost Vs qsmall (some (.inr i)) F)
  simp only [physical_small_big_energy_eq] at hs
  refine hs.trans ?_
  calc
    _ ≤ (Fintype.card I : ℝ) * ∑ _i : I,
        (Ccond ^ (2 * Fintype.card S) * unrestrictedEdgeEnergyBound ρ v vmin vmax T ^ Fintype.card G) *
          physicalSmallBigEnergy Vs (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g))) F := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply sum_le_sum
      intro i _
      exact hbound H I S G Ps P n J M shared B A (Δ k) (D k) (kbig k)
        ω μ qghost ρ Vedge Vghost Vs hVs hω hωmass v vmin vmax hρ0 hρ1 hv hvmin
        hVlo hVhi hμ hmass T ht i F hF
    _ = _ := by
      simp only [sum_const, card_univ, nsmul_eq_mul]
      ring_nf
      rfl

end Bounty

end


-- Source module: PhysicalMixedWordEnergy
section

/- Whole-path mixed-word energy with arbitrary bounded phase and terminal memory symmetry. -/

open Finset
open scoped Classical
namespace Bounty

noncomputable def physicalMixedWordStepEnergy {H K : Type}
    (A ρ v vmin vmaxEdge vmaxGhost : ℝ) (T smallGroups bigGroups patternCount : ℕ) : Option (H ⊕ K) → ℝ
  | none => 1
  | some (.inl _) => physicalGhostUniformEnergyBound ρ vmaxGhost v ^ bigGroups
  | some (.inr _) => (patternCount : ℝ) ^ 2 *
      (A ^ (2 * smallGroups) * unrestrictedEdgeEnergyBound ρ v vmin vmaxEdge T ^ bigGroups)

theorem physical_mixed_word_step_energy_nonneg {H K : Type}
    (A ρ v vmin vmaxEdge vmaxGhost : ℝ) (T smallGroups bigGroups patternCount : ℕ) (hA : 0 ≤ A)
    (tag : Option (H ⊕ K)) :
    0 ≤ physicalMixedWordStepEnergy A ρ v vmin vmaxEdge vmaxGhost T smallGroups bigGroups patternCount tag := by
  cases tag with
  | none => exact zero_le_one
  | some tag =>
    cases tag with
    | inl j => exact pow_nonneg (Real.exp_pos _).le _
    | inr k => exact mul_nonneg (sq_nonneg _) (mul_nonneg (pow_nonneg hA _)
        (pow_nonneg (unrestrictedEdgeEnergyBound_nonneg ρ v vmin vmaxEdge T) _))

theorem exists_physical_mixed_word_path_energy_bound
    {qsmall vs : ℝ} (hq0 : 0 ≤ qsmall) (hq1 : qsmall < 1) (hvs : 0 < vs) (ell : ℕ) :
    ∃ Ccond : ℝ, 1 ≤ Ccond ∧ ∀ (H K S G I : Type) [Fintype I] [Fintype S] [DecidableEq S]
      [Fintype G] [DecidableEq G]
      (Ps : S → Finset ℕ) [∀ p : PhysicalPrime Ps, NeZero p.2.val]
      (P : G → Type) [∀ g, Fintype (P g)] (n : ∀ g, P g → ℕ)
      [∀ g p, NeZero (n g p)] (J : ℕ) (M : G → ℕ)
      (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ) (A : I → Type) [∀ i, Fintype (A i)]
      (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J → SharedActiveLabels P (shared i) → A i → G → ℤ)
      (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)
      (ω : ∀ i, A i → ℝ) (μ : ∀ g, P g → ℝ) (qghost : H → ℝ) (ρ : ℝ)
      (Vedge Vghost : G → ℝ) (Vs : S → ℝ), (∀ s, vs ≤ Vs s) →
      (∀ k a, 0 ≤ ω k a) → (∀ k, ∑ a, ω k a ≤ 1) →
      ∀ (v vmin vmaxEdge vmaxGhost : ℝ), 0 < ρ → ρ < 1 → 1 < v → 0 < vmin →
      (∀ g, vmin ≤ Vedge g) → (∀ g, Vedge g ≤ vmaxEdge) →
      (∀ g, 0 ≤ Vghost g) → (∀ g, Vghost g ≤ vmaxGhost) →
      (∀ g p, 0 < μ g p) → (∀ g, ∑ p, μ g p ≤ 2) →
      (∀ j, 0 ≤ qghost j) → (∀ j, qghost j ≤ 1) →
      (∀ j, qghost j / ρ ^ 2 + ((1 - qghost j) / ρ) / v ≤ 1) →
      (∀ j g, qghost j / ρ ^ 2 + ((1 - qghost j) * Vghost g / ρ) / v ≤ 1) →
      ∀ (T : ℕ), (∀ k g, (shared k g)ᶜ.card ≤ T) →
      ∀ (steps : List (Option (H ⊕ K)))
        (phase : ∀ s, PhysicalMixedWordPath n shared B A Δ D kbig steps s → ℂ),
      (∀ s p, ‖phase s p‖ ≤ 1) →
      ∀ (f : PhysicalSmallBigState Ps J ell
        (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) → ℂ),
      (∀ s, ProductMemorySymmetric (fun x => f (s, x))) →
      physicalSmallBigEnergy Vs (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g)))
        (physicalMixedWordVaryingGhostAction n shared B A Δ D kbig ω μ qghost ρ
          Vedge Vghost Vs qsmall steps phase f) ≤
        (steps.map (physicalMixedWordStepEnergy Ccond ρ v vmin vmaxEdge vmaxGhost
          T (Fintype.card S) (Fintype.card G) (Fintype.card I))).prod *
        physicalSmallBigEnergy Vs (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g))) f := by
  obtain ⟨Ccond, hCcond, hedge⟩ := exists_physical_mixed_word_edge_energy_bound hq0 hq1 hvs ell
  refine ⟨Ccond, hCcond, ?_⟩
  intro H K S G I _ _ dS _ dG
  cases Subsingleton.elim dS (Classical.typeDecidableEq S)
  cases Subsingleton.elim dG (Classical.typeDecidableEq G)
  intro Ps _ P _ n _ J M shared B A _ Δ D kbig ω μ qghost ρ Vedge Vghost Vs hVs
    hω hωmass v vmin vmaxEdge vmaxGhost hρ0 hρ1 hv hvmin hVlo hVhi hVg0 hVghi hμ hmass
    hqg0 hqg1 hD hC T ht steps phase hphase f hf
  have hVs0 : ∀ s, 0 < Vs s := fun s => hvs.trans_le (hVs s)
  have hμ0 : ∀ g p, 0 ≤ μ g p := fun g p => (hμ g p).le
  have hVe0 : ∀ g, 0 ≤ Vedge g := fun g => (hvmin.trans_le (hVlo g)).le
  apply physical_mixed_word_varying_ghost_path_energy_of_local n shared B A Δ D kbig
    ω μ qghost ρ Vedge Vghost Vs qsmall hVs0 hμ0
    (physicalMixedWordStepEnergy Ccond ρ v vmin vmaxEdge vmaxGhost T (Fintype.card S) (Fintype.card G) (Fintype.card I))
    (physical_mixed_word_step_energy_nonneg Ccond ρ v vmin vmaxEdge vmaxGhost T
      (Fintype.card S) (Fintype.card G) (Fintype.card I) (zero_le_one.trans hCcond))
    ?_ ?_ steps phase hphase f hf
  · intro tag F hF
    cases tag with
    | none =>
      erw [physical_mixed_word_positive_permutation_eq]
      exact physical_small_big_joint_average_memory_symmetric F hF
    | some tag =>
      cases tag with
      | inl j =>
        erw [physical_mixed_word_positive_ghost_eq n shared B A Δ D kbig
          ω μ qghost ρ Vedge Vghost Vs qsmall hμ0 j (hqg0 j) F]
        exact physical_small_big_ghost_one_memory_symmetric _ _ _ _ M B F hF
      | inr k =>
        erw [physical_mixed_word_positive_edge_eq n shared B A Δ D kbig
          ω μ qghost ρ Vedge Vghost Vs qsmall hVs0 hω hμ0 hρ0.le hVe0 k F]
        intro small x g σ
        dsimp only
        apply sum_congr rfl
        intro i _
        exact physical_small_big_path_positive_edge_symmetric n shared B A (Δ k) (D k) (kbig k)
          ω μ qghost ρ Vedge Vghost Vs qsmall hVs0 hω hμ0 hρ0.le hVe0 i F hF small x g σ
  · intro tag F hF
    cases tag with
    | none =>
      erw [physical_mixed_word_positive_permutation_eq]
      simp only [physicalMixedWordStepEnergy, one_mul]
      convert physical_small_big_joint_average_energy_le Vs hVs0 μ
          (fun g => unrestrictedResidueWeight (μ g)) hμ0 (fun g z => hμ0 g z.1) F using 1 <;> rfl
    | some tag =>
      cases tag with
      | inl j =>
        erw [physical_mixed_word_positive_ghost_eq n shared B A Δ D kbig
          ω μ qghost ρ Vedge Vghost Vs qsmall hμ0 j (hqg0 j) F]
        exact physical_small_big_absolute_ghost_energy_le_uniform n Vs hVs0 μ (qghost j) ρ Vghost v vmaxGhost
          M B hμ hmass (hqg0 j) (hqg1 j) hρ0 hVg0 hVghi (zero_lt_one.trans hv) (hD j) (hC j) F hF
      | inr k =>
        exact hedge H K S G I Ps P n J M shared B A Δ D kbig ω μ qghost ρ
          Vedge Vghost Vs hVs hω hωmass v vmin vmaxEdge hρ0 hρ1 hv hvmin hVlo hVhi
          hμ0 hmass T ht k F hF

end Bounty

end


-- Source module: RootCapCostParameters
section

/- Concrete group, energy, and mass parameters for the original cap error. -/


/- Fixed group costs and initial masses have polynomial growth. -/

open Finset
namespace Bounty

theorem root_group_energy_polynomial {L D C P a e g : ℝ}
    (hL : 1 ≤ L) (hD : 1 ≤ D) (hP : 0 ≤ P)
    (ha : 0 ≤ a) (haD : a ≤ D) (he : 0 ≤ e) (heD : e ≤ D)
    (hg : 0 ≤ g) (hgD : g ≤ D) (s m p : ℕ)
    (hs : (s : ℝ) ≤ C*Real.log L) (hm : (m : ℝ) ≤ C*Real.log L)
    (hp : (p : ℝ) ≤ L^P) :
    g^m ≤ L^(2*P+3*C*Real.log D) ∧
      (p : ℝ)^2*(a^(2*s)*e^m) ≤ L^(2*P+3*C*Real.log D) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hCm : 0 ≤ C*Real.log L := (Nat.cast_nonneg m).trans hm
  have hthree : (m : ℝ) ≤ (3*C)*Real.log L := by nlinarith
  have htotal : ((2*s+m : ℕ) : ℝ) ≤ (3*C)*Real.log L := by
    push_cast
    nlinarith
  have hbase := constant_pow_le_rpow_of_log_bound hD hL0 (2*s+m) htotal
  have hgm := constant_pow_le_rpow_of_log_bound hD hL0 m hthree
  have hplain : L^((3*C)*Real.log D) ≤ L^(2*P+3*C*Real.log D) :=
    Real.rpow_le_rpow_of_exponent_le hL (by nlinarith)
  constructor
  · exact (pow_le_pow_left₀ hg hgD m).trans (hgm.trans hplain)
  · have hp2 : (p : ℝ)^2 ≤ L^(2*P) := by
      calc
        _ ≤ (L^P)^2 := pow_le_pow_left₀ (Nat.cast_nonneg p) hp 2
        _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; ring
    have hprod : a^(2*s)*e^m ≤ D^(2*s+m) := by
      rw [pow_add]
      exact mul_le_mul (pow_le_pow_left₀ ha haD _) (pow_le_pow_left₀ he heD _)
        (pow_nonneg he _) (pow_nonneg (zero_le_one.trans hD) _)
    calc
      _ ≤ L^(2*P)*L^((3*C)*Real.log D) :=
        mul_le_mul hp2 (hprod.trans hbase) (mul_nonneg (pow_nonneg ha _) (pow_nonneg he _))
          (Real.rpow_nonneg hL0.le _)
      _ = _ := by rw [← Real.rpow_add hL0]

theorem root_initial_mass_polynomial {G : Type*} [Fintype G] {L C : ℝ}
    (hL : 0 < L) (k : ℕ) (mass : G → ℝ)
    (hmass : ∀ g, 0 ≤ mass g ∧ mass g ≤ 2)
    (hgroups : (Fintype.card G : ℝ) ≤ C*Real.log L) :
    (∏ g, mass g^k) ≤ L^((C*(k : ℝ))*Real.log 2) := by
  have hexp : ((k*Fintype.card G : ℕ) : ℝ) ≤ (C*(k : ℝ))*Real.log L := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hgroups (Nat.cast_nonneg k)]
  calc
    _ ≤ ∏ _g : G, (2 : ℝ)^k := by
      apply Finset.prod_le_prod₀
      · intro g _; exact pow_nonneg (hmass g).1 k
      · intro g _; exact pow_le_pow_left₀ (hmass g).1 (hmass g).2 k
    _ = (2 : ℝ)^(k*Fintype.card G) := by simp [← pow_mul]
    _ ≤ _ := constant_pow_le_rpow_of_log_bound (by norm_num) hL _ hexp

theorem root_moment_length_and_loss {L C : ℝ} (hL : 1 ≤ L)
    (M T : ℕ) (hM : (M : ℝ) ≤ C*Real.log L) :
    (4*(2*Nat.ceil (L^(13/25 : ℝ)))+1 : ℕ) ≤ 17*L^(13/25 : ℝ) ∧
    ((2*Nat.ceil (L^(13/25 : ℝ))*(T*M) : ℕ) : ℝ) ≤
      (4*(T : ℝ)*C)*L^(13/25 : ℝ)*Real.log L := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hP : 1 ≤ L^(13/25 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hceil : (Nat.ceil (L^(13/25 : ℝ)) : ℝ) ≤ 2*L^(13/25 : ℝ) := by
    have h := Nat.ceil_lt_add_one (Real.rpow_nonneg hL0.le (13/25 : ℝ))
    linarith
  constructor
  · push_cast
    nlinarith
  · push_cast
    have hTm := mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg T)
    have hfirst := mul_le_mul_of_nonneg_right hceil
      (mul_nonneg (Nat.cast_nonneg T) (Nat.cast_nonneg M))
    have hsecond := mul_le_mul_of_nonneg_left hTm (Real.rpow_nonneg hL0.le (13/25 : ℝ))
    nlinarith

end Bounty


/- Polynomial bounds for the actual mixed-word step energies. -/

namespace Bounty

theorem physical_mixed_word_step_energy_polynomial {H K : Type}
    {L D C P A ρ v vmin vmaxEdge vmaxGhost : ℝ}
    (hL : 1 ≤ L) (hD : 1 ≤ D) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hA : 0 ≤ A) (hAD : A ≤ D)
    (hghost : physicalGhostUniformEnergyBound ρ vmaxGhost v ≤ D)
    (T s m p : ℕ) (hedge : unrestrictedEdgeEnergyBound ρ v vmin vmaxEdge T ≤ D)
    (hs : (s : ℝ) ≤ C*Real.log L) (hm : (m : ℝ) ≤ C*Real.log L)
    (hp : (p : ℝ) ≤ L^P) (tag : Option (H ⊕ K)) :
    0 ≤ physicalMixedWordStepEnergy A ρ v vmin vmaxEdge vmaxGhost T s m p tag ∧
    physicalMixedWordStepEnergy A ρ v vmin vmaxEdge vmaxGhost T s m p tag ≤
      L^(2*P+3*C*Real.log D) := by
  refine ⟨physical_mixed_word_step_energy_nonneg A ρ v vmin vmaxEdge vmaxGhost T s m p hA tag, ?_⟩
  have hcost := root_group_energy_polynomial hL hD hP hA hAD
    (unrestrictedEdgeEnergyBound_nonneg ρ v vmin vmaxEdge T) hedge
    (Real.exp_pos _).le hghost s m p hs hm hp
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  cases tag with
  | none => exact Real.one_le_rpow hL (by positivity)
  | some tag =>
    cases tag with
    | inl j => exact hcost.1
    | inr k => exact hcost.2

end Bounty


/- Absorption of the actual mixed-word cap cost at the original moment power. -/

open Filter
namespace Bounty

theorem full_memory_edge_count_le_length {H K : Type*}
    (steps : List (Option (H ⊕ K))) : fullMemoryEdgeCount steps ≤ steps.length := by
  induction steps with
  | nil => simp [fullMemoryEdgeCount]
  | cons x xs ih =>
    have hx : fullMemoryEdgeIndicator x ≤ 1 := by
      cases x with
      | none => simp [fullMemoryEdgeIndicator]
      | some x => cases x <;> simp [fullMemoryEdgeIndicator]
    simpa [fullMemoryEdgeCount, List.length_cons, Nat.add_comm] using Nat.add_le_add hx ih

theorem eventually_root_mixed_cap_cost_bound
    {D C P B F A ρ v vmin vmaxEdge vmaxGhost : ℝ}
    (hD : 1 ≤ D) (hC : 0 ≤ C) (hP : 0 ≤ P) (hB : 0 ≤ B) (hF : 0 ≤ F)
    (hA : 0 ≤ A) (hAD : A ≤ D)
    (hghost : physicalGhostUniformEnergyBound ρ vmaxGhost v ≤ D)
    (T k : ℕ) (hedge : unrestrictedEdgeEnergyBound ρ v vmin vmaxEdge T ≤ D) :
    ∀ᶠ L : ℝ in atTop, ∀ b s m p : ℕ, L ≤ (b : ℝ) →
      (s : ℝ) ≤ C*Real.log L → (m : ℝ) ≤ C*Real.log L → (p : ℝ) ≤ L^P →
      ∀ (H K : Type) (steps : List (Option (H ⊕ K))),
      (steps.length : ℝ) ≤ 17*L^(13/25 : ℝ) →
      ∀ phaseBound : ℝ, 0 ≤ phaseBound → phaseBound ≤ L^B →
      ∀ mass : Fin m → ℝ, (∀ g, 0 ≤ mass g ∧ mass g ≤ 2) →
      phaseBound^steps.length * ((2 : ℝ)^(b+1-fullMemoryEdgeCount steps*(T*m)))⁻¹ *
        Real.sqrt (steps.map (physicalMixedWordStepEnergy A ρ v vmin vmaxEdge vmaxGhost T s m p)).prod *
        (∏ g, mass g^k) ≤ (L^(-F))^(2*Nat.ceil (L^(13/25 : ℝ))) := by
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hE : 0 ≤ 2*P+3*C*Real.log D := by positivity
  have hM : 0 ≤ (C*(k : ℝ))*Real.log 2 := by positivity
  have hLoss : 0 ≤ 17*(T : ℝ)*C := by positivity
  filter_upwards [eventually_root_cap_weighted_moment_bound
    (C := 17) hLoss hB hE hM hF, eventually_ge_atTop (1 : ℝ)] with L hmain hL
  intro b s m p hb hs hm hp H K steps hlen phaseBound hphase hphasepow mass hmass
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hmasspow : (∏ g, mass g^k) ≤ L^((C*(k : ℝ))*Real.log 2) :=
    root_initial_mass_polynomial hL0 k mass hmass (by simpa using hm)
  have hmass0 : 0 ≤ ∏ g, mass g^k := Finset.prod_nonneg fun g _ => pow_nonneg (hmass g).1 k
  have hcount : (fullMemoryEdgeCount steps : ℝ) ≤ 17*L^(13/25 : ℝ) :=
    (Nat.cast_le.mpr (full_memory_edge_count_le_length steps)).trans hlen
  have hloss : ((fullMemoryEdgeCount steps*(T*m) : ℕ) : ℝ) ≤
      (17*(T : ℝ)*C)*L^(13/25 : ℝ)*Real.log L := by
    push_cast
    have hTm := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg T)
    have hfirst := mul_le_mul_of_nonneg_right hcount
      (mul_nonneg (Nat.cast_nonneg T) (Nat.cast_nonneg m))
    have hsecond := mul_le_mul_of_nonneg_left hTm
      (show 0 ≤ 17*L^(13/25 : ℝ) by positivity)
    nlinarith
  exact hmain b (fullMemoryEdgeCount steps*(T*m)) hb hloss _ steps _ hlen
    (fun x _ => physical_mixed_word_step_energy_polynomial hL hD hC hP hA hAD
      hghost T s m p hedge hs hm hp x) phaseBound (∏ g, mass g^k) hphase hphasepow hmass0 hmasspow

end Bounty

end


-- Source module: PhysicalGroupResidueReadout
section

/- Exact reindexing of the original selected-group residue average into
the residue vectors used by the mixed-state measure. -/

open Finset
open scoped Classical
namespace Bounty

noncomputable def physicalGroupResidueVectorEquiv
    {G : Type*} [Fintype G] (P : G → Finset ℕ) (groups : Finset G) :
    PhysicalGroupResidues P groups ≃ PhysicalResidues (fun g : ↥groups => P g.val) where
  toFun := physicalGroupResidueVector
  invFun r a := r ((physicalPrimeGroupEquiv P groups).symm a)
  left_inv r := by funext a; rfl
  right_inv r := by funext a; rfl

theorem physical_group_residue_vector_sum
    {G : Type*} [Fintype G] (P : G → Finset ℕ) (groups : Finset G)
    [Fintype (PhysicalGroupResidues P groups)]
    [Fintype (PhysicalResidues (fun g : ↥groups => P g.val))]
    (F : PhysicalResidues (fun g : ↥groups => P g.val) → ℂ) :
    (∑ r : PhysicalGroupResidues P groups, F (physicalGroupResidueVector r)) = ∑ r, F r :=
  (physicalGroupResidueVectorEquiv P groups).sum_comp F

theorem physical_group_residue_factor_eq
    {G : Type*} [Fintype G] (P : G → Finset ℕ) (groups : Finset G) :
    (∏ a : ↥(physicalPrimeGroups P groups), 1 / (a.val.2.val : ℝ)) =
      ∏ p : PhysicalPrime (fun g : ↥groups => P g.val), 1 / (p.2.val : ℝ) :=
  ((physicalPrimeGroupEquiv P groups).prod_comp (fun a => 1 / (a.val.2.val : ℝ))).symm

theorem physical_group_residue_weighted_sum
    {G : Type*} [Fintype G] (P : G → Finset ℕ) (groups : Finset G)
    [Fintype (PhysicalGroupResidues P groups)]
    [Fintype (PhysicalResidues (fun g : ↥groups => P g.val))]
    (F : PhysicalResidues (fun g : ↥groups => P g.val) → ℂ) :
    (∑ r : PhysicalGroupResidues P groups,
      ((∏ a : ↥(physicalPrimeGroups P groups), 1 / (a.val.2.val : ℝ) : ℝ) : ℂ) *
        F (physicalGroupResidueVector r)) =
    ∑ r : PhysicalResidues (fun g : ↥groups => P g.val),
      ((∏ p : PhysicalPrime (fun g : ↥groups => P g.val), 1 / (p.2.val : ℝ) : ℝ) : ℂ) * F r := by
  rw [physical_group_residue_factor_eq, ← mul_sum, physical_group_residue_vector_sum, mul_sum]

end Bounty

end


-- Source module: MixedInitialVacuumPairing
section

/- Exact injective initial marks and an arbitrary bounded boundary phase
are controlled in the product measure, without imposing symmetry on the phase. -/

open Finset
open scoped Classical
namespace Bounty

theorem mixed_initial_vacuum_pairing_le
    {T G : Type*} [Fintype T] [Fintype G] [DecidableEq G]
    {P : G → Finset ℕ} {Z : G → Type*} [∀ g, Fintype (Z g)] {J ell B : ℕ}
    (C : G → Finset (Fin J)) (ω : T → ℝ)
    (hω : ∀ t, 0 ≤ ω t) (hωsum : ∑ t, ω t ≤ 1)
    (μ : ∀ g, P g → ℝ) (ν : ∀ g, Z g → ℝ)
    (hμ : ∀ g p, 0 ≤ μ g p) (hν : ∀ g z, 0 ≤ ν g z)
    (empty : ∀ g, BoundedOrderedTuple (Z g) B) (hempty : ∀ g, (empty g).1.val = 0)
    (boundary : T → ProductBoundedOrderedState (fun g => ↥(P g)) Z (fun _ => J + ell) B → ℂ)
    (hb : ∀ t x, ‖boundary t x‖ ≤ 1)
    (F : T × ProductBoundedOrderedState (fun g => ↥(P g)) Z (fun _ => J + ell) B → ℂ) :
    ‖∑ t, (ω t : ℂ) * ∑ L : PhysicalMarkLists P J ell,
      ((∏ g, ∏ i : PhysicalSlots J ell, μ g (L g i) : ℝ) : ℂ) *
        (boundary t (physicalFullMemoryState C L empty) * F (t, physicalFullMemoryState C L empty))‖ ≤
      Real.sqrt (∏ g, (∑ p, μ g p) ^ (J + ell)) *
        cleanActiveNorm (fun s => ω s.1 * productMemoryWeight μ ν s.2) F := by
  let mass := ∏ g, (∑ p, μ g p) ^ (J + ell)
  have hm : 0 ≤ mass := prod_nonneg fun g _ => pow_nonneg (sum_nonneg fun p _ => hμ g p) _
  let value := fun t => ∑ L : PhysicalMarkLists P J ell,
    ((∏ g, ∏ i : PhysicalSlots J ell, μ g (L g i) : ℝ) : ℂ) *
      (boundary t (physicalFullMemoryState C L empty) * F (t, physicalFullMemoryState C L empty))
  have he (t : T) : 0 ≤ finiteWeightedEnergy (productMemoryWeight μ ν) (fun x => F (t, x)) :=
    sum_nonneg fun x _ => mul_nonneg (productMemoryWeight_nonneg μ ν hμ hν x) (sq_nonneg _)
  have hlocal (t : T) : ‖value t‖ ^ 2 ≤
      mass * finiteWeightedEnergy (productMemoryWeight μ ν) (fun x => F (t, x)) := by
    have henergy := (physical_full_state_energy_le C μ ν hμ hν
      (fun x => boundary t x * F (t, x))).trans
      (finiteWeightedEnergy_le_of_norm_le (productMemoryWeight μ ν)
        (productMemoryWeight_nonneg μ ν hμ hν)
        (fun x => boundary t x * F (t, x)) (fun x => F (t, x))
        (fun x => by
          rw [norm_mul]
          exact (mul_le_mul_of_nonneg_right (hb t x) (norm_nonneg _)).trans_eq (one_mul _)))
    exact (physical_mark_vacuum_pairing_energy_le μ ν hμ hν empty hempty
      (fun L q => boundary t (physicalFullMemoryState C L q) * F (t, physicalFullMemoryState C L q))).trans
      ((mul_le_mul_of_nonneg_left henergy (physical_mark_mass_nonneg μ hμ)).trans
        (mul_le_mul_of_nonneg_right (physical_mark_mass_le μ hμ) (he t)))
  have henergy : finiteWeightedEnergy (fun s => ω s.1 * productMemoryWeight μ ν s.2) F =
      ∑ t, ω t * finiteWeightedEnergy (productMemoryWeight μ ν) (fun x => F (t, x)) := by
    unfold finiteWeightedEnergy
    rw [Fintype.sum_prod_type]
    simp only [mul_assoc, mul_sum]
  have hsq : ‖∑ t, (ω t : ℂ) * value t‖ ^ 2 ≤
      mass * finiteWeightedEnergy (fun s => ω s.1 * productMemoryWeight μ ν s.2) F := by
    refine (finite_weighted_sum_cauchy univ ω (fun t _ => hω t) value).trans ?_
    calc
      (∑ t, ω t) * ∑ t, ω t * ‖value t‖ ^ 2 ≤ ∑ t, ω t * ‖value t‖ ^ 2 := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hωsum
          (sum_nonneg fun t _ => mul_nonneg (hω t) (sq_nonneg _))
      _ ≤ ∑ t, ω t * (mass * finiteWeightedEnergy (productMemoryWeight μ ν) (fun x => F (t, x))) :=
        sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hlocal t) (hω t)
      _ = _ := by rw [henergy, mul_sum]; apply sum_congr rfl; intro t _; ring
  have hs := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hm] at hs
  exact hs

end Bounty

end


-- Source module: PhysicalSmallBigVacuumMass
section

/- The terminal empty-memory vector has only the unrestricted active mass;
normalized small residues contribute at most one. -/

open Finset
open scoped Classical
namespace Bounty

theorem finite_product_vacuum_norm
    {T G : Type*} [Fintype T] [Fintype G] [DecidableEq G]
    {P Z : G → Type*} [∀ g, Fintype (P g)] [∀ g, Fintype (Z g)]
    (ω : T → ℝ) (μ : ∀ g, P g → ℝ) (ν : ∀ g, Z g → ℝ) (M : G → ℕ) (B : ℕ) :
    cleanActiveNorm (fun s : T × ProductBoundedOrderedState P Z M B =>
      ω s.1 * productMemoryWeight μ ν s.2) (fun s => fullMemoryVacuum s.2) =
      Real.sqrt ((∑ t, ω t) * ∏ g, (∑ p, μ g p) ^ M g) := by
  unfold cleanActiveNorm
  congr 1
  rw [Fintype.sum_prod_type]
  simp only [mul_assoc, ← mul_sum]
  change (∑ t, ω t * finiteWeightedEnergy (productMemoryWeight μ ν)
    (fullMemoryVacuum (M := M) (B := B))) = _
  rw [fullMemoryVacuum_energy, sum_mul]

theorem physical_small_big_normalized_vacuum_norm_le
    {S G : Type*} [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
    {Ps : S → Finset ℕ} [∀ p : PhysicalPrime Ps, NeZero p.2.val]
    {P Z : G → Type*} [∀ g, Fintype (P g)] [∀ g, Fintype (Z g)]
    {J ell : ℕ} (Vs : S → ℝ) (hVs : ∀ s, 0 < Vs s)
    (hMass : ∀ s, ∑ p ∈ Ps s, 1 / (p : ℝ) = Vs s)
    (μ : ∀ g, P g → ℝ) (ν : ∀ g, Z g → ℝ) (hμ : ∀ g p, 0 ≤ μ g p)
    (M : G → ℕ) (B : ℕ) :
    cleanActiveNorm (physicalSmallBigNormalizedMeasure (P := Ps) (J := J) (ell := ell) Vs
      (productMemoryWeight μ ν)) (fun s => fullMemoryVacuum (M := M) (B := B) s.2) ≤
      Real.sqrt (∏ g, (∑ p, μ g p) ^ M g) := by
  change cleanActiveNorm (fun s : PhysicalBareResidueState Ps J ell ×
    ProductBoundedOrderedState P Z M B => physicalResidueInitialMass Vs s.1 *
      productMemoryWeight μ ν s.2) (fun s => fullMemoryVacuum s.2) ≤ _
  rw [finite_product_vacuum_norm (fun s : PhysicalBareResidueState Ps J ell =>
    physicalResidueInitialMass Vs s) μ ν M B]
  apply Real.sqrt_le_sqrt
  exact (mul_le_mul_of_nonneg_right (physical_residue_initial_mass_total Vs hVs hMass)
    (prod_nonneg fun g _ => pow_nonneg (sum_nonneg fun p _ => hμ g p) _)).trans_eq (one_mul _)

end Bounty

end


-- Source module: PhysicalSmallBigInitialReadout
section

/- The original normalized small-residue average and injective initial big
marks admit a scalar readout with one unrestricted active-mass factor. -/

open Finset
open scoped Classical
namespace Bounty
section Readout
variable {S G : Type*} [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
  {Ps : S → Finset ℕ} [∀ p : PhysicalPrime Ps, NeZero p.2.val]
  {P : G → Finset ℕ} {Z : G → Type*} [∀ g, Fintype (Z g)] {J ell B : ℕ}
  (Vs : S → ℝ) (C : G → Finset (Fin J))
  (μ : ∀ g, P g → ℝ) (ν : ∀ g, Z g → ℝ)
  (empty : ∀ g, BoundedOrderedTuple (Z g) B)
  (boundary : PhysicalBareResidueState Ps J ell →
    ProductBoundedOrderedState (fun g => ↥(P g)) Z (fun _ => J + ell) B → ℂ)
  (F : PhysicalSmallBigState Ps J ell
    (ProductBoundedOrderedState (fun g => ↥(P g)) Z (fun _ => J + ell) B) → ℂ)

noncomputable def physicalSmallBigInitialReadout : ℂ :=
  ∑ s : PhysicalBareResidueState Ps J ell, (physicalResidueInitialMass Vs s : ℂ) *
    ∑ L : PhysicalMarkLists P J ell,
      ((∏ g, ∏ i : PhysicalSlots J ell, μ g (L g i) : ℝ) : ℂ) *
        (boundary s (physicalFullMemoryState C L empty) * F (s, physicalFullMemoryState C L empty))

theorem physical_small_big_initial_readout_norm_le
    (hVs : ∀ s, 0 < Vs s) (hMass : ∀ s, ∑ p ∈ Ps s, 1 / (p : ℝ) = Vs s)
    (hμ : ∀ g p, 0 ≤ μ g p) (hν : ∀ g z, 0 ≤ ν g z)
    (hempty : ∀ g, (empty g).1.val = 0) (hb : ∀ s x, ‖boundary s x‖ ≤ 1) :
    ‖physicalSmallBigInitialReadout Vs C μ empty boundary F‖ ≤
      Real.sqrt (∏ g, (∑ p, μ g p) ^ (J + ell)) *
        cleanActiveNorm (physicalSmallBigNormalizedMeasure Vs (productMemoryWeight μ ν)) F :=
  mixed_initial_vacuum_pairing_le C (fun s : PhysicalBareResidueState Ps J ell => physicalResidueInitialMass Vs s)
    (physical_residue_initial_mass_nonneg Vs hVs) (physical_residue_initial_mass_total Vs hVs hMass)
    μ ν hμ hν empty hempty boundary hb F

theorem physical_small_big_initial_readout_operator_bound
    (hVs : ∀ s, 0 < Vs s) (hMass : ∀ s, ∑ p ∈ Ps s, 1 / (p : ℝ) = Vs s)
    (hμ : ∀ g p, 0 ≤ μ g p) (hν : ∀ g z, 0 ≤ ν g z)
    (hempty : ∀ g, (empty g).1.val = 0) (hb : ∀ s x, ‖boundary s x‖ ≤ 1)
    {K : ℝ} (hK : 0 ≤ K)
    (hF : cleanActiveNorm (physicalSmallBigNormalizedMeasure Vs (productMemoryWeight μ ν)) F ≤
      K * cleanActiveNorm (physicalSmallBigNormalizedMeasure (P := Ps) (J := J) (ell := ell)
        Vs (productMemoryWeight μ ν)) (fun s => fullMemoryVacuum (M := fun _ => J + ell) (B := B) s.2)) :
    ‖physicalSmallBigInitialReadout Vs C μ empty boundary F‖ ≤
      K * ∏ g, (∑ p, μ g p) ^ (J + ell) := by
  let mass := ∏ g, (∑ p, μ g p) ^ (J + ell)
  have hm : 0 ≤ mass := prod_nonneg fun g _ => pow_nonneg (sum_nonneg fun p _ => hμ g p) _
  have hv := physical_small_big_normalized_vacuum_norm_le (J := J) (ell := ell) Vs hVs hMass μ ν hμ (fun _ => J + ell) B
  have h := physical_small_big_initial_readout_norm_le Vs C μ ν empty boundary F hVs hMass hμ hν hempty hb
  refine h.trans ((mul_le_mul_of_nonneg_left hF (Real.sqrt_nonneg _)).trans ?_)
  calc
    _ ≤ Real.sqrt mass * (K * Real.sqrt mass) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv hK) (Real.sqrt_nonneg _)
    _ = K * mass := by nlinarith [Real.sq_sqrt hm]

end Readout
end Bounty

end


-- Source module: PhysicalResidueComplexReadout
section

/- The exact complex readout of a function supported on valid small
residue/mark states, retaining the original uniform residue factor. -/

open Finset
open scoped Classical
namespace Bounty

theorem physical_residue_complex_sum_of_supported
    {S : Type*} [Fintype S] [DecidableEq S]
    {P : S → Finset ℕ} [∀ p : PhysicalPrime P, NeZero p.2.val] {J ell : ℕ}
    (V : S → ℝ) (F : PhysicalResidues P → PhysicalMarkLists P J ell → ℂ)
    (hF : ∀ r L, ¬ physicalResidueMarksValid r L → F r L = 0) :
    (∑ s : PhysicalBareResidueState P J ell, (physicalResidueInitialMass V s : ℂ) * F s.1 s.2) =
      (physicalStateMass V J ell : ℂ) * ∑ r : PhysicalResidues P,
        ((∏ p : PhysicalPrime P, 1 / (p.2.val : ℝ) : ℝ) : ℂ) * ∑ L : PhysicalMarkLists P J ell, F r L := by
  have hpoint (r : PhysicalResidues P) (L : PhysicalMarkLists P J ell) :
      (physicalResidueInitialMass V (r, L) : ℂ) * F r L =
        (physicalStateMass V J ell : ℂ) *
          (((∏ p : PhysicalPrime P, 1 / (p.2.val : ℝ) : ℝ) : ℂ) * F r L) := by
    by_cases h : physicalResidueMarksValid r L
    · rw [physical_residue_initial_mass_of_valid V r L h, Complex.ofReal_mul, mul_assoc]
    · rw [hF r L h, mul_zero, mul_zero, mul_zero]
  rw [Fintype.sum_prod_type]
  simp only [hpoint, mul_sum]

end Bounty

end


-- Source module: PhysicalSmallBigRawReadout
section

/- The original normalized small-residue average and injective initial big
marks admit a scalar readout with one unrestricted active-mass factor. -/

open Finset
open scoped Classical
namespace Bounty
section Readout
variable {S G : Type*} [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
  {Ps : S → Finset ℕ} [∀ p : PhysicalPrime Ps, NeZero p.2.val]
  {P : G → Finset ℕ} {Z : G → Type*} [∀ g, Fintype (Z g)] {J ell B : ℕ}
  (Vs : S → ℝ) (C : G → Finset (Fin J))
  (μ : ∀ g, P g → ℝ) (ν : ∀ g, Z g → ℝ)
  (empty : ∀ g, BoundedOrderedTuple (Z g) B)
  (boundary : PhysicalBareResidueState Ps J ell →
    ProductBoundedOrderedState (fun g => ↥(P g)) Z (fun _ => J + ell) B → ℂ)
  (F : PhysicalSmallBigState Ps J ell
    (ProductBoundedOrderedState (fun g => ↥(P g)) Z (fun _ => J + ell) B) → ℂ)

omit [∀ g, Fintype (Z g)] in
theorem physical_small_big_initial_readout_eq_raw
    (hF : ∀ r L x, ¬ physicalResidueMarksValid r L → F ((r, L), x) = 0) :
    physicalSmallBigInitialReadout Vs C μ empty boundary F =
      (physicalStateMass Vs J ell : ℂ) * ∑ r : PhysicalResidues Ps,
        ((∏ p : PhysicalPrime Ps, 1 / (p.2.val : ℝ) : ℝ) : ℂ) *
        ∑ Ls : PhysicalMarkLists Ps J ell, ∑ Lb : PhysicalMarkLists P J ell,
          ((∏ g, ∏ i : PhysicalSlots J ell, μ g (Lb g i) : ℝ) : ℂ) *
            (boundary (r, Ls) (physicalFullMemoryState C Lb empty) *
              F ((r, Ls), physicalFullMemoryState C Lb empty)) := by
  unfold physicalSmallBigInitialReadout
  refine physical_residue_complex_sum_of_supported Vs
    (fun r Ls => ∑ Lb : PhysicalMarkLists P J ell,
      ((∏ g, ∏ i : PhysicalSlots J ell, μ g (Lb g i) : ℝ) : ℂ) *
        (boundary (r, Ls) (physicalFullMemoryState C Lb empty) *
          F ((r, Ls), physicalFullMemoryState C Lb empty))) ?_
  intro r L h
  apply sum_eq_zero
  intro Lb _
  rw [hF r L _ h, mul_zero, mul_zero]

end Readout
end Bounty

end


-- Source module: PhysicalRootScalarReadout
section

/- The normalized original root scalar is its exact mixed-state readout. -/

open Finset Classical
namespace Bounty
section Scalar
variable {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
  [∀ z : PhysicalPrime P, NeZero z.2.val]
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
  (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
  (V : Fin N → ℝ) (q : ℝ) (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ)
  (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
    PhysicalAuxLabels P (C i) → ℂ)
  (θ : ℝ)
  (β : PhysicalPrime P → ℝ) (ρ : ℝ)
  (hP : ∀ g a, a ∈ P g → Nat.Prime a)
  (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))

noncomputable def physicalRootScalarVectorAction
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e) : ℂ :=
  physicalRootMixedAction (n := n) groups e patterns C hC k V q ζ K
    ((physicalGroupResidueVectorEquiv P groupsᶜ).symm s.1.1) θ
    (fun (g : Fin M) (z : P (e.symm g).val) => β ⟨(e.symm g).val, z⟩)
    (fun j => physicalEndpointSchedule q (n + 1) j.val) ρ
    (fun (s : ↥groupsᶜ) => hP s.val) (fun (g : Fin M) => hP (e.symm g).val)
    (physical_root_group_pools_disjoint groups e hdis)
    fullMemoryVacuum s.1.2 s.2

theorem physical_root_mixed_scalar_average_eq_readout
    (hF : ∀ r L x, ¬ physicalResidueMarksValid r L →
      physicalRootScalarVectorAction (n := n) (B := B)
        groups e patterns C hC V q ζ k K θ β ρ hP hdis ((r, L), x) = 0) :
    letI : ∀ z : PhysicalPrime (fun s : ↥groupsᶜ => P s.val), NeZero z.2.val :=
      fun z => inferInstanceAs (NeZero (⟨z.1.val, z.2⟩ : PhysicalPrime P).2.val)
    (∑ r : PhysicalGroupResidues P groupsᶜ,
      ((∏ a : ↥(physicalPrimeGroups P groupsᶜ), 1 / (a.val.2.val : ℝ) : ℝ) : ℂ) *
        physicalRootMixedScalar (n := n) (B := B)
          groups e patterns C hC V q ζ k K r θ β ρ hP hdis) =
      physicalSmallBigInitialReadout
        (fun s : ↥groupsᶜ => V s.val) (fun _ : Fin M => ∅)
        (fun (g : Fin M) (z : P (e.symm g).val) => β ⟨(e.symm g).val, z⟩ / V (e.symm g).val)
        (fun g => fullEmptyBoundedMemory
          (UnrestrictedResidueParticle (fun z : P (e.symm g).val => z.val)) B)
        (fun _ _ => 1)
        (physicalRootScalarVectorAction (n := n) (B := B)
          groups e patterns C hC V q ζ k K θ β ρ hP hdis) := by
  let : ∀ z : PhysicalPrime (fun s : ↥groupsᶜ => P s.val), NeZero z.2.val :=
    fun z => inferInstanceAs (NeZero (⟨z.1.val, z.2⟩ : PhysicalPrime P).2.val)
  let ψ : PhysicalResidues (fun s : ↥groupsᶜ => P s.val) → ℂ := fun r =>
    (physicalStateMass (fun s : ↥groupsᶜ => V s.val) J ell : ℂ) *
      ∑ Ls : PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell,
        ∑ Lb : PhysicalMarkLists (fun g : Fin M => P (e.symm g).val) J ell,
          ((∏ g, ∏ i : PhysicalSlots J ell,
            β ⟨(e.symm g).val, Lb g i⟩ / V (e.symm g).val : ℝ) : ℂ) *
            physicalRootScalarVectorAction (n := n) (B := B)
              groups e patterns C hC V q ζ k K θ β ρ hP hdis
              ((r, Ls), physicalFullMemoryState (fun _ : Fin M => ∅) Lb
                (fun g => fullEmptyBoundedMemory
                  (UnrestrictedResidueParticle (fun z : P (e.symm g).val => z.val)) B))
  calc
    _ = ∑ r : PhysicalResidues (fun s : ↥groupsᶜ => P s.val),
        ((∏ p : PhysicalPrime (fun s : ↥groupsᶜ => P s.val),
          1 / (p.2.val : ℝ) : ℝ) : ℂ) * ψ r :=
      physical_group_residue_weighted_sum P groupsᶜ ψ
    _ = _ := by
      rw [physical_small_big_initial_readout_eq_raw _ _ _ _ _ _ hF]
      dsimp only [ψ]
      simp only [one_mul]
      conv_rhs => rw [mul_sum]
      apply sum_congr rfl
      intro r _
      exact mul_left_comm _ _ _

end Scalar
end Bounty

end


-- Source module: PhysicalRootCapAction
section

/- The original root scalar vector uses the genuine mixed word at every cap. -/

open Finset Classical
namespace Bounty
section Scalar
variable {I : Type} {N M J ell n b B : ℕ} {P : Fin N → Finset ℕ}
  [∀ z : PhysicalPrime P, NeZero z.2.val]
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
  (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
  (V : Fin N → ℝ) (q : ℝ) (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ)
  (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
    PhysicalAuxLabels P (C i) → ℂ)
  (θ : ℝ)
  (β : PhysicalPrime P → ℝ) (ρ : ℝ)
  (hP : ∀ g a, a ∈ P g → Nat.Prime a)
  (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))

theorem physical_root_scalar_vector_action_unfold
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e) :
    letI : ∀ g (z : P (e.symm g).val), NeZero z.val :=
      fun g z => inferInstanceAs (NeZero (⟨(e.symm g).val, z⟩ : PhysicalPrime P).2.val)
    physicalRootScalarVectorAction (n := n) (B := B)
      groups e patterns C hC V q ζ k K θ β ρ hP hdis s =
    physicalMixedWordPathAction (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) B
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (i : patterns) _ aux => physicalAuxMass (fun g => V (e.symm g).val) (fun g => C i.val (e.symm g).val) aux)
    (fun g p => β ⟨(e.symm g).val, p⟩ / V (e.symm g).val)
    (fun j => physicalEndpointSchedule q (n + 1) j.val) ρ (fun g => V (e.symm g).val)
    (fun s : ↥groupsᶜ => V s.val) (fun _ => q) ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
    (physicalRootMixedPhase groups e patterns C hC k V ζ K θ
      (fun g p => β ⟨(e.symm g).val, p⟩) ρ
      (fun s => hP s.val) (fun g => hP (e.symm g).val)
      (physical_root_group_pools_disjoint groups e hdis))
    (fun s => fullMemoryVacuum s.2) s := by
  let : ∀ g (z : P (e.symm g).val), NeZero z.val :=
    fun g z => inferInstanceAs (NeZero (⟨(e.symm g).val, z⟩ : PhysicalPrime P).2.val)
  unfold physicalRootScalarVectorAction physicalRootMixedAction
  dsimp only
  have hr : physicalGroupResidueVector ((physicalGroupResidueVectorEquiv P groupsᶜ).symm s.1.1) = s.1.1 :=
    (physicalGroupResidueVectorEquiv P groupsᶜ).apply_symm_apply s.1.1
  rw [hr]

end Scalar
end Bounty

end


-- Source module: PhysicalFullPhaseCap
section

/- Exact cap coherence of physical edge phases and original coefficients on nonzero support. -/

open Finset
open scoped Classical
namespace Bounty

section Edge
variable {N J ell b B : ℕ} {P : Fin N → Finset ℕ}
  (C : Fin N → Finset (Fin J)) (k : ℤ) (h : b ≤ B)
  (L R : PhysicalMarkLists P J ell) (H : (g : Fin N) → Finset (P g))
  (q : (g : Fin N) → BoundedOrderedTuple (UnrestrictedResidueParticle (fun p : P g => p.val)) b)

theorem physical_full_edge_phase_cap
    (a : PhysicalFullEdgeEvent C k (physicalFullMemoryState C L q)) :
    physicalFullEdgePhase C k L R H (fun g => boundedMemoryCapEmbed h (q g)) a =
      physicalFullEdgePhase C k L R H q a := rfl

variable (ω : ∀ _c : SharedActiveLabels (fun g => P g)
    (fun g => physicalFullSharedIndices (ell := ell) (C g)), PhysicalAuxLabels P C → ℝ)
  (μ : (g : Fin N) → P g → ℝ) (ρ : ℝ) (V : Fin N → ℝ)

theorem physical_full_endpoint_phase_cap
    (a : PhysicalFullEdgeEvent C k (physicalFullMemoryState C L q))
    (hw : fullActiveEdgeEventWeight (fun g (p : P g) => p.val)
      (fun g => physicalFullSharedIndices (ell := ell) (C g)) b (fun _ => PhysicalAuxLabels P C)
      (physicalFullEdgeDelta C k) (physicalFullEdgeD C) ω μ ρ V
      (physicalFullMemoryState C L q) a ≠ 0) :
    physicalFullEndpointPhase C k L H (fun g => boundedMemoryCapEmbed h (q g)) ω μ ρ V a =
      physicalFullEndpointPhase C k L H q ω μ ρ V a := by
  have hb := fullActiveEdgeEventWeight_cap_of_ne_zero (fun g (p : P g) => p.val)
    (fun g => physicalFullSharedIndices (ell := ell) (C g)) (fun _ => PhysicalAuxLabels P C)
    (physicalFullEdgeDelta C k) (physicalFullEdgeD C) h
    (physicalFullMemoryState C L q) ω μ ρ V a hw
  have hwB := ne_of_eq_of_ne hb.symm hw
  unfold physicalFullEndpointPhase
  erw [if_neg hwB, if_neg hw]
  rfl

end Edge

section Global
variable {N J ell b B : ℕ} {P : Fin N → Finset ℕ}
  (C : Fin N → Finset (Fin J)) (k : ℤ) (h : b ≤ B)
  (H : (g : Fin N) → Finset (P g))
  (ω : ∀ _c : SharedActiveLabels (fun g => P g)
    (fun g => physicalFullSharedIndices (ell := ell) (C g)), PhysicalAuxLabels P C → ℝ)
  (μ : (g : Fin N) → P g → ℝ) (ρ : ℝ) (V : Fin N → ℝ)

theorem physical_full_global_edge_phase_cap
    (x : PhysicalFullBoundedState P J ell b) (a : PhysicalFullEdgeEvent C k x)
    (hw : fullActiveEdgeEventWeight (fun g (p : P g) => p.val)
      (fun g => physicalFullSharedIndices (ell := ell) (C g)) b (fun _ => PhysicalAuxLabels P C)
      (physicalFullEdgeDelta C k) (physicalFullEdgeD C) ω μ ρ V x a ≠ 0) :
    physicalFullGlobalEdgePhase C k H ω μ ρ V (productStateCapEmbed h x) a =
      physicalFullGlobalEdgePhase C k H ω μ ρ V x a := by
  by_cases hx : FullActiveInjective x
  · obtain ⟨⟨L, q⟩, hL⟩ := (physicalFullStateEquiv C).surjective ⟨x, hx⟩
    have he : physicalFullMemoryState C L q = x := congrArg Subtype.val hL
    subst x
    change physicalFullGlobalEdgePhase C k H ω μ ρ V
      (physicalFullMemoryState C L (fun g => boundedMemoryCapEmbed h (q g))) a = _
    exact (physical_full_global_edge_phase_encode (B := B) C k H ω μ ρ V L
      (fun g => boundedMemoryCapEmbed h (q g)) a).trans
      ((physical_full_endpoint_phase_cap C k h L H q ω μ ρ V a hw).trans
        (physical_full_global_edge_phase_encode (B := b) C k H ω μ ρ V L q a).symm)
  · have hxB : ¬ FullActiveInjective (productStateCapEmbed h x) := hx
    unfold physicalFullGlobalEdgePhase
    erw [dif_neg hxB, dif_neg hx]

end Global

section Combined
variable {I K : Type} {N J ell b B : ℕ} {P : Fin N → Finset ℕ}
  (C : K → Fin N → Finset (Fin J)) (k : K → ℤ) (h : b ≤ B)
  (ω : ∀ j, SharedActiveLabels (fun g => P g)
    (fun g => physicalFullSharedIndices (ell := ell) (C j g)) → PhysicalAuxLabels P (C j) → ℝ)
  (β : (g : Fin N) → P g → ℝ) (ρ : ℝ) (V : Fin N → ℝ)
  (ζ : K → ℝ)
  (coeff : ∀ j, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell → PhysicalAuxLabels P (C j) → ℂ)
  (retention : I → ℝ)

theorem physical_full_key_coefficient_phase_cap
    (tag : Option (I ⊕ K)) (x : PhysicalFullBoundedState P J ell b)
    (a : PhysicalFullLedgerEvent C k tag ((fun _ => ∅), x))
    (hw : fullPermutationMixedEventWeight (fun g (p : P g) => p.val)
      (fun j g => physicalFullSharedIndices (ell := ell) (C j g)) b
      (fun j _ => PhysicalAuxLabels P (C j))
      (fun j => physicalFullEdgeDelta (C j) (k j)) (fun j => physicalFullEdgeD (C j))
      ω (fun g p => β g p / V g) retention ρ V tag x a ≠ 0) :
    physicalFullKeyCoefficientPhase C k ζ coeff tag (productStateCapEmbed h x)
      (fullPermutationMixedEventCapEmbed (fun g (p : P g) => p.val)
        (fun j g => physicalFullSharedIndices (ell := ell) (C j g))
        (fun j _ => PhysicalAuxLabels P (C j))
        (fun j => physicalFullEdgeDelta (C j) (k j)) (fun j => physicalFullEdgeD (C j)) h tag x a) =
      physicalFullKeyCoefficientPhase C k ζ coeff tag x a := by
  cases tag with
  | none => rfl
  | some tag =>
    cases tag with
    | inl j => rfl
    | inr j =>
      dsimp only [physicalFullKeyCoefficientPhase, fullPermutationMixedEventCapEmbed]
      have ht := fullActiveEdgeEventTarget_cap_of_weight_ne_zero (fun g (p : P g) => p.val)
        (fun g => physicalFullSharedIndices (ell := ell) (C j g))
        (fun _ => PhysicalAuxLabels P (C j)) (physicalFullEdgeDelta (C j) (k j))
        (physicalFullEdgeD (C j)) h x (ω j) (fun g p => β g p / V g) ρ V a hw
      exact congrArg (fun y : PhysicalFullBoundedState P J ell B =>
        physicalActiveCoefficient (C j) (C j) (C j) (ζ j) (coeff j)
          (fun g => (x g).1) (fun g => (y g).1) a.1) ht.symm

end Combined
end Bounty

end


-- Source module: PhysicalFullLedgerPhaseCap
section

/- Exact phase and ledger transport with all original event data retained. -/

open scoped Classical
namespace Bounty

section Ledger
variable {I K : Type} {N J ell b B : ℕ} {P : Fin N → Finset ℕ}
  (C : K → Fin N → Finset (Fin J)) (k : K → ℤ) (h : b ≤ B)
  (ω : ∀ j, SharedActiveLabels (fun g => P g)
    (fun g => physicalFullSharedIndices (ell := ell) (C j g)) → PhysicalAuxLabels P (C j) → ℝ)
  (β : (g : Fin N) → P g → ℝ) (ρ : ℝ) (V : Fin N → ℝ)
  (retention : I → ℝ)

theorem physical_full_ledger_event_phase_cap
    (tag : Option (I ⊕ K)) (H : (g : Fin N) → Finset (P g))
    (x : PhysicalFullBoundedState P J ell b)
    (a : PhysicalFullLedgerEvent C k tag (H, x))
    (hw : fullPermutationMixedEventWeight (fun g (p : P g) => p.val)
      (fun j g => physicalFullSharedIndices (ell := ell) (C j g)) b
      (fun j _ => PhysicalAuxLabels P (C j))
      (fun j => physicalFullEdgeDelta (C j) (k j)) (fun j => physicalFullEdgeD (C j))
      ω (fun g p => β g p / V g) retention ρ V tag x a ≠ 0) :
    physicalFullLedgerEventPhase C k ω β ρ V tag (H, productStateCapEmbed h x)
      (fullPermutationMixedEventCapEmbed (fun g (p : P g) => p.val)
        (fun j g => physicalFullSharedIndices (ell := ell) (C j g))
        (fun j _ => PhysicalAuxLabels P (C j))
        (fun j => physicalFullEdgeDelta (C j) (k j)) (fun j => physicalFullEdgeD (C j)) h tag x a) =
      physicalFullLedgerEventPhase C k ω β ρ V tag (H, x) a := by
  cases tag with
  | none => rfl
  | some tag =>
    cases tag with
    | inl j => rfl
    | inr j =>
      exact physical_full_global_edge_phase_cap (C j) (k j) h H (ω j)
        (fun g p => β g p / V g) ρ V x a hw

theorem physical_full_combined_phase_cap
    (ζ : K → ℝ)
    (coeff : ∀ j, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell → PhysicalAuxLabels P (C j) → ℂ)
    (tag : Option (I ⊕ K)) (H : (g : Fin N) → Finset (P g))
    (x : PhysicalFullBoundedState P J ell b)
    (a : PhysicalFullLedgerEvent C k tag (H, x))
    (hw : fullPermutationMixedEventWeight (fun g (p : P g) => p.val)
      (fun j g => physicalFullSharedIndices (ell := ell) (C j g)) b
      (fun j _ => PhysicalAuxLabels P (C j))
      (fun j => physicalFullEdgeDelta (C j) (k j)) (fun j => physicalFullEdgeD (C j))
      ω (fun g p => β g p / V g) retention ρ V tag x a ≠ 0) :
    physicalFullCombinedPhase C k ω β ρ V ζ coeff tag H (productStateCapEmbed h x)
      (fullPermutationMixedEventCapEmbed (fun g (p : P g) => p.val)
        (fun j g => physicalFullSharedIndices (ell := ell) (C j g))
        (fun j _ => PhysicalAuxLabels P (C j))
        (fun j => physicalFullEdgeDelta (C j) (k j)) (fun j => physicalFullEdgeD (C j)) h tag x a) =
      physicalFullCombinedPhase C k ω β ρ V ζ coeff tag H x a := by
  unfold physicalFullCombinedPhase
  rw [physical_full_ledger_event_phase_cap C k h ω β ρ V retention tag H x a hw,
    physical_full_key_coefficient_phase_cap C k h ω β ρ V ζ coeff retention tag x a hw]

end Ledger

section Update
variable {I K : Type} {N b B : ℕ} {P : Fin N → Type}
  [∀ g, DecidableEq (P g)]
  (n : ∀ g, P g → ℕ) {M : Fin N → ℕ}
  (S : K → ∀ g, Finset (Fin (M g)))
  (A : ∀ k, SharedActiveLabels P (S k) → Type)
  (Δ D : ∀ k c, A k c → Fin N → ℤ) (h : b ≤ B)
  (ω : ∀ k c, A k c → ℝ) (μ : ∀ g, P g → ℝ)
  (q : I → ℝ) (ρ : ℝ) (V : Fin N → ℝ)

theorem full_mixed_ledger_update_cap
    (tag : Option (I ⊕ K)) (H : (g : Fin N) → Finset (P g))
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M b)
    (a : FullPermutationMixedEvent n S b A Δ D tag x)
    (hw : fullPermutationMixedEventWeight n S b A Δ D ω μ q ρ V tag x a ≠ 0) :
    fullMixedLedgerUpdate n S B A Δ D tag H (productStateCapEmbed h x)
      (fullPermutationMixedEventCapEmbed n S A Δ D h tag x a) =
      fullMixedLedgerUpdate n S b A Δ D tag H x a := by
  cases tag with
  | none => rfl
  | some tag =>
    cases tag with
    | inl j => rfl
    | inr j =>
      dsimp only [fullMixedLedgerUpdate, fullPermutationMixedEventCapEmbed]
      unfold fullEdgeLedgerUpdate
      rw [← fullActiveEdgeEventTarget_cap_of_weight_ne_zero n (S j) (A j) (Δ j) (D j)
        h x (ω j) μ ρ V a hw]
      rfl

end Update
end Bounty

end


-- Source module: FullParameterCap
section

/- Effective parameter transport commutes with the literal memory-cap embedding. -/

open scoped Classical
namespace Bounty

section Parameter
variable {I K G : Type*} {P : G → Type*}
  (n : ∀ g, P g → ℕ) {M : G → ℕ}
  (S : K → ∀ g, Finset (Fin (M g)))
  (A : ∀ k, SharedActiveLabels P (S k) → Type*)
  (Δ Δ' D D' : ∀ k c, A k c → G → ℤ)
  (hΔ : ∀ k, Δ k = Δ' k)
  (hD : ∀ k c a g p, ((n g p : ℤ) ∣ D k c a g ↔ (n g p : ℤ) ∣ D' k c a g))
  {b B : ℕ} (h : b ≤ B)

theorem full_permutation_parameter_event_cap
    (tag : Option (I ⊕ K))
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M b)
    (a : FullPermutationMixedEvent n S b A Δ D tag x) :
    fullPermutationParameterEventEquiv n S B A Δ Δ' D D' hΔ hD tag (productStateCapEmbed h x)
      (fullPermutationMixedEventCapEmbed n S A Δ D h tag x a) =
    fullPermutationMixedEventCapEmbed n S A Δ' D' h tag x
      (fullPermutationParameterEventEquiv n S b A Δ Δ' D D' hΔ hD tag x a) := by
  have he : Δ = Δ' := funext hΔ
  subst Δ'
  cases tag with
  | none => rfl
  | some tag =>
    cases tag with
    | inl j => rfl
    | inr j =>
      rfl

end Parameter

end Bounty

end


-- Source module: PhysicalEffectivePhaseCap
section

/- Exact phase and ledger transport with all original event data retained. -/

open scoped Classical
namespace Bounty

section Effective
variable {S K I : Type} [Fintype S] {N J ell b B : ℕ}
  {Ps : S → Finset ℕ} {P : Fin N → Finset ℕ}
  (hPs : ∀ s p, p ∈ Ps s → Nat.Prime p)
  (hP : ∀ g p, p ∈ P g → Nat.Prime p)
  (hdis : ∀ s g, Disjoint (Ps s) (P g))
  (C : K → Fin N → Finset (Fin J)) (d : K → PhysicalSharedLists Ps J)
  (k : K → ℤ) (h : b ≤ B)
  (ω : ∀ j, SharedActiveLabels (fun g => P g)
    (fun g => physicalFullSharedIndices (ell := ell) (C j g)) → PhysicalAuxLabels P (C j) → ℝ)
  (β : (g : Fin N) → P g → ℝ) (ρ : ℝ) (V : Fin N → ℝ) (retention : I → ℝ)
  (ζ : K → ℝ)
  (coeff : ∀ j, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell → PhysicalAuxLabels P (C j) → ℂ)

theorem physical_effective_combined_phase_cap
    (tag : Option (I ⊕ K)) (H : (g : Fin N) → Finset (P g))
    (x : PhysicalFullBoundedState P J ell b)
    (a : FullPermutationMixedEvent (fun g (p : P g) => p.val)
      (fun j g => physicalFullSharedIndices (ell := ell) (C j g)) b
      (fun j _ => PhysicalAuxLabels P (C j))
      (fun j => physicalMixedEdgeDelta (C j) (k j) (d j))
      (fun j => physicalMixedEdgeD (C j) (d j)) tag x)
    (hw : fullPermutationMixedEventWeight (fun g (p : P g) => p.val)
      (fun j g => physicalFullSharedIndices (ell := ell) (C j g)) b
      (fun j _ => PhysicalAuxLabels P (C j))
      (fun j => physicalMixedEdgeDelta (C j) (k j) (d j))
      (fun j => physicalMixedEdgeD (C j) (d j))
      ω (fun g p => β g p / V g) retention ρ V tag x a ≠ 0) :
    physicalFullCombinedPhase C (fun j => k j * (physicalSharedProduct (d j) : ℕ))
      ω β ρ V ζ coeff tag H (productStateCapEmbed h x)
      (physicalMixedEffectiveBigEventEquiv hPs hP hdis C d k B tag (productStateCapEmbed h x)
        (fullPermutationMixedEventCapEmbed (fun g (p : P g) => p.val)
          (fun j g => physicalFullSharedIndices (ell := ell) (C j g))
          (fun j _ => PhysicalAuxLabels P (C j))
          (fun j => physicalMixedEdgeDelta (C j) (k j) (d j))
          (fun j => physicalMixedEdgeD (C j) (d j)) h tag x a)) =
    physicalFullCombinedPhase C (fun j => k j * (physicalSharedProduct (d j) : ℕ))
      ω β ρ V ζ coeff tag H x
      (physicalMixedEffectiveBigEventEquiv hPs hP hdis C d k b tag x a) := by
  unfold physicalMixedEffectiveBigEventEquiv
  rw [full_permutation_parameter_event_cap]
  apply physical_full_combined_phase_cap C (fun j => k j * (physicalSharedProduct (d j) : ℕ))
    h ω β ρ V retention ζ coeff tag H x
  rw [full_permutation_parameter_weight]
  exact hw

end Effective
end Bounty

end


-- Source module: PhysicalMixedProjectionSupport
section

/- Exact phase and ledger transport with all original event data retained. -/

open scoped Classical
namespace Bounty
section Projection
variable {S G I V K : Type} [Fintype S] [Fintype G] [DecidableEq G]
  {Ps : S → Finset ℕ} {P : G → Type}
  (n : ∀ g, P g → ℕ) {J ell : ℕ} {M : G → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (A : I → Type)
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J → SharedActiveLabels P (shared i) → A i → G → ℤ)
  (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)
  (ω : ∀ i, SharedActiveLabels P (shared i) → A i → ℝ)
  (μ : ∀ g, P g → ℝ) (qghost : V → ℝ) (ρ : ℝ) (Vb : G → ℝ)
  (Vs : S → ℝ) (qedge : K → ℝ)

theorem physical_mixed_big_projection_weight_ne_zero
    (tag : Option (V ⊕ K))
    (s : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B)
    (a : PhysicalMixedWordEvent n shared B A Δ D tag s)
    (hw : physicalMixedWordWeight n shared B A Δ D kbig ω μ qghost ρ Vb Vs qedge tag s a ≠ 0) :
    fullPermutationMixedEventWeight n
      (fun key : PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K) => shared key.2.1) B
      (fun key _ => A key.2.1)
      (fun key c a => Δ key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)
      (fun key c a => D key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)
      (fun key => ω key.2.1) μ qghost ρ Vb
      (physicalMixedBigEventTag n shared B A Δ D tag s a) s.2
      (physicalMixedBigEventProjection n shared B A Δ D tag s a) ≠ 0 := by
  cases tag with
  | none => exact (mul_ne_zero_iff.mp hw).2
  | some tag =>
    cases tag with
    | inl j => exact hw
    | inr k =>
      erw [physical_mixed_word_edge_weight_factor] at hw
      exact (mul_ne_zero_iff.mp hw).2

end Projection
end Bounty

end


-- Source module: PhysicalMixedWordCapSupport
section

/- Supported event transport preserves every small coordinate while changing
the big-memory cap. Target agreement is asserted only at nonzero weight. -/

open Finset
open scoped Classical

namespace Bounty

section
variable {H K S G I : Type} [Fintype S] [Fintype G] [DecidableEq G] {Ps : S → Finset ℕ} {P : G → Type} [∀ g, Fintype (P g)]
  (n : ∀ g, P g → ℕ) {J ell : ℕ} {M : G → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (A : I → Type)
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J → SharedActiveLabels P (shared i) → A i → G → ℤ)
  {b B : ℕ} (h : b ≤ B)

def physicalMixedWordCapEmbed (tag : Option (H ⊕ K))
    (s : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M b)) :
    PhysicalMixedWordEvent n shared b A Δ D tag s →
      PhysicalMixedWordEvent n shared B A Δ D tag (physicalSmallBigCapEmbed h s) :=
  match tag with
  | none => id
  | some (.inl _) => coupledGhostEventCapEmbed h s.2
  | some (.inr k) => fun e => ⟨e.1, e.2.1, (e.2.2.1,
      fullActiveEdgeEventCapEquiv n (shared e.1) (fun _ => Unit)
        (fun c _ => Δ k e.1 (physicalSharedPrefix s.1.2) c e.2.1)
        (fun c _ => D k e.1 (physicalSharedPrefix s.1.2) c e.2.1) h s.2 e.2.2.2)⟩

omit [Fintype S] [Fintype G] [DecidableEq G] [∀ g, Fintype (P g)] in
theorem physicalMixedWordCapEmbed_injective (tag : Option (H ⊕ K))
    (s : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M b)) :
    Function.Injective (physicalMixedWordCapEmbed n shared A Δ D h tag s) := by
  cases tag with
  | none => exact Function.injective_id
  | some tag =>
    cases tag with
    | inl j => exact coupledGhostEventCapEmbed_injective h s.2
    | inr k =>
      intro e f he
      exact he

variable (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)
  (ω : ∀ i, SharedActiveLabels P (shared i) → A i → ℝ) (μ : ∀ g, P g → ℝ)
  (qghost : H → ℝ) (ρ : ℝ) (V : G → ℝ) (Vs : S → ℝ) (qedge : K → ℝ)

omit [∀ g, Fintype (P g)] in
theorem physicalMixedWordCapEmbed_target (tag : Option (H ⊕ K))
    (s : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M b))
    (e : PhysicalMixedWordEvent n shared b A Δ D tag s)
    (hw : physicalMixedWordWeight n shared b A Δ D kbig ω μ qghost ρ V Vs qedge tag s e ≠ 0) :
    physicalMixedWordTarget n shared B A Δ D kbig tag (physicalSmallBigCapEmbed h s)
        (physicalMixedWordCapEmbed n shared A Δ D h tag s e) =
      physicalSmallBigCapEmbed h (physicalMixedWordTarget n shared b A Δ D kbig tag s e) := by
  cases tag with
  | none => rfl
  | some tag =>
    cases tag with
    | inl j =>
      exact Prod.ext rfl (coupledGhostEventCapEmbed_target_of_ne_zero h
        (fun g => physicalGhostRetention (n g) (qghost j) ρ)
        (fun g => physicalGhostTermination (n g) (qghost j) ρ)
        (fun g => physicalGhostBirth (n g) (qghost j) ρ (V g))
        (fun g => unrestrictedResidueWeight (μ g)) s.2 e hw)
    | inr k =>
      have hb : fullActiveEdgeEventWeight n (shared e.1) b (fun _ => Unit)
          (fun c _ => Δ k e.1 (physicalSharedPrefix s.1.2) c e.2.1)
          (fun c _ => D k e.1 (physicalSharedPrefix s.1.2) c e.2.1)
          (fun _ _ => 1) μ ρ V s.2 e.2.2.2 ≠ 0 := by
        intro hz
        apply hw
        simp only [physicalMixedWordWeight, physicalSmallBigPositiveWeight,
          physicalSmallBigFullWeight, hz, mul_zero, ite_self]
      exact Prod.ext rfl ((fullActiveEdgeEventTarget_cap_of_weight_ne_zero n (shared e.1) (fun _ => Unit)
        (fun c _ => Δ k e.1 (physicalSharedPrefix s.1.2) c e.2.1)
        (fun c _ => D k e.1 (physicalSharedPrefix s.1.2) c e.2.1) h s.2
        (fun _ _ => 1) μ ρ V e.2.2.2 hb).symm)

omit [∀ g, Fintype (P g)] in
theorem physicalMixedWordCapEmbed_weight (tag : Option (H ⊕ K))
    (s : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M b))
    (hs : productTotalMemory s.2 ≤ b) (e : PhysicalMixedWordEvent n shared b A Δ D tag s) :
    physicalMixedWordWeight n shared b A Δ D kbig ω μ qghost ρ V Vs qedge tag s e =
      if productTotalMemory (physicalMixedWordTarget n shared B A Δ D kbig tag
          (physicalSmallBigCapEmbed h s) (physicalMixedWordCapEmbed n shared A Δ D h tag s e)).2 ≤ b
      then physicalMixedWordWeight n shared B A Δ D kbig ω μ qghost ρ V Vs qedge tag
        (physicalSmallBigCapEmbed h s) (physicalMixedWordCapEmbed n shared A Δ D h tag s e)
      else 0 := by
  cases tag with
  | none =>
      change _ = if productTotalMemory (fullActivePermutation e.2 (productStateCapEmbed h s.2)) ≤ b then _ else _
      rw [fullActivePermutation_total_memory, productStateCapEmbed_totalMemory, if_pos hs]
      rfl
  | some tag =>
    cases tag with
    | inl j =>
      exact coupledGhostEventCapEmbed_weight h
        (fun g => physicalGhostRetention (n g) (qghost j) ρ)
        (fun g => physicalGhostTermination (n g) (qghost j) ρ)
        (fun g => physicalGhostBirth (n g) (qghost j) ρ (V g))
        (fun g => unrestrictedResidueWeight (μ g)) s.2 hs e
    | inr k =>
      have he := fullActiveEdgeEventWeight_cap n (shared e.1) (fun _ => Unit)
        (fun c _ => Δ k e.1 (physicalSharedPrefix s.1.2) c e.2.1)
        (fun c _ => D k e.1 (physicalSharedPrefix s.1.2) c e.2.1) h s.2
        (fun _ _ => 1) μ ρ V hs e.2.2.2
      dsimp only [physicalMixedWordWeight, physicalMixedWordTarget, physicalSmallBigTarget,
        physicalSmallBigFullTarget, physicalSmallBigPositiveWeight, physicalSmallBigFullWeight,
        physicalMixedWordCapEmbed, physicalSmallBigCapEmbed]
      rw [he]
      (split_ifs <;> simp_all only [mul_zero]); rfl

omit [∀ g, Fintype (P g)] in
theorem physicalMixedWordCapEmbed_surjective_of_ne_zero (tag : Option (H ⊕ K))
    (s : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M b))
    (e : PhysicalMixedWordEvent n shared B A Δ D tag (physicalSmallBigCapEmbed h s))
    (hw : physicalMixedWordWeight n shared B A Δ D kbig ω μ qghost ρ V Vs qedge tag
      (physicalSmallBigCapEmbed h s) e ≠ 0)
    (ht : productTotalMemory (physicalMixedWordTarget n shared B A Δ D kbig tag
      (physicalSmallBigCapEmbed h s) e).2 ≤ b) :
    ∃ d : PhysicalMixedWordEvent n shared b A Δ D tag s,
      physicalMixedWordCapEmbed n shared A Δ D h tag s d = e := by
  cases tag with
  | none => exact ⟨e, rfl⟩
  | some tag =>
    cases tag with
    | inl j =>
      exact coupledGhostEventCapEmbed_surjective_of_ne_zero h
        (fun g => physicalGhostRetention (n g) (qghost j) ρ)
        (fun g => physicalGhostTermination (n g) (qghost j) ρ)
        (fun g => physicalGhostBirth (n g) (qghost j) ρ (V g))
        (fun g => unrestrictedResidueWeight (μ g)) s.2 e hw ht
    | inr k => exact ⟨e, rfl⟩

omit [∀ g, Fintype (P g)] in
theorem physicalMixedWord_supported_target (tag : Option (H ⊕ K))
    (s : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M b))
    (hs : productTotalMemory s.2 ≤ b) (e : PhysicalMixedWordEvent n shared b A Δ D tag s)
    (hw : physicalMixedWordWeight n shared b A Δ D kbig ω μ qghost ρ V Vs qedge tag s e ≠ 0) :
    productTotalMemory (physicalMixedWordTarget n shared b A Δ D kbig tag s e).2 ≤ b := by
  cases tag with
  | none => exact (fullActivePermutation_total_memory e.2 s.2).le.trans hs
  | some tag =>
    cases tag with
    | inl j =>
      exact (coupledGhostJointEventWeight_support
        (fun g => physicalGhostRetention (n g) (qghost j) ρ)
        (fun g => physicalGhostTermination (n g) (qghost j) ρ)
        (fun g => physicalGhostBirth (n g) (qghost j) ρ (V g))
        (fun g => unrestrictedResidueWeight (μ g)) s.2 e hw).1.2
    | inr k =>
      have hb : fullActiveEdgeEventWeight n (shared e.1) b (fun _ => Unit)
          (fun c _ => Δ k e.1 (physicalSharedPrefix s.1.2) c e.2.1)
          (fun c _ => D k e.1 (physicalSharedPrefix s.1.2) c e.2.1)
          (fun _ _ => 1) μ ρ V s.2 e.2.2.2 ≠ 0 := by
        intro hz
        apply hw
        simp only [physicalMixedWordWeight, physicalSmallBigPositiveWeight,
          physicalSmallBigFullWeight, hz, mul_zero, ite_self]
      rw [fullActiveEdgeEventWeight_full_caps] at hb
      by_contra ht
      exact hb (if_neg (fun hc => ht hc.2))

omit [∀ g, Fintype (P g)] in
theorem physicalMixedWordCapEmbed_support (k : Option (H ⊕ K))
    (s : PhysicalSmallBigState Ps J ell (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M b))
    (hs : productTotalMemory s.2 ≤ b) (e : PhysicalMixedWordEvent n shared b A Δ D k s) :
    physicalMixedWordWeight n shared b A Δ D kbig ω μ qghost ρ V Vs qedge k s e ≠ 0 ↔
      physicalMixedWordWeight n shared B A Δ D kbig ω μ qghost ρ V Vs qedge k (physicalSmallBigCapEmbed h s)
        (physicalMixedWordCapEmbed n shared A Δ D h k s e) ≠ 0 ∧
      productTotalMemory (physicalMixedWordTarget n shared B A Δ D kbig k (physicalSmallBigCapEmbed h s)
        (physicalMixedWordCapEmbed n shared A Δ D h k s e)).2 ≤ b := by
  rw [physicalMixedWordCapEmbed_weight n shared A Δ D h kbig ω μ qghost ρ V Vs qedge k s hs e]
  split_ifs <;> simp_all

omit [∀ g, Fintype (P g)] in
theorem physicalMixedWordCapEmbed_weight_of_ne_zero (k : Option (H ⊕ K))
    (s : PhysicalSmallBigState Ps J ell (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M b))
    (hs : productTotalMemory s.2 ≤ b) (e : PhysicalMixedWordEvent n shared b A Δ D k s)
    (hw : physicalMixedWordWeight n shared b A Δ D kbig ω μ qghost ρ V Vs qedge k s e ≠ 0) :
    physicalMixedWordWeight n shared B A Δ D kbig ω μ qghost ρ V Vs qedge k (physicalSmallBigCapEmbed h s)
      (physicalMixedWordCapEmbed n shared A Δ D h k s e) =
      physicalMixedWordWeight n shared b A Δ D kbig ω μ qghost ρ V Vs qedge k s e := by
  have ht := ((physicalMixedWordCapEmbed_support n shared A Δ D h kbig ω μ qghost ρ V Vs qedge k s hs e).mp hw).2
  exact ((physicalMixedWordCapEmbed_weight n shared A Δ D h kbig ω μ qghost ρ V Vs qedge k s hs e).trans (if_pos ht)).symm

noncomputable def physicalMixedWordCapSupportEquiv (k : Option (H ⊕ K))
    (s : PhysicalSmallBigState Ps J ell (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M b))
    (hs : productTotalMemory s.2 ≤ b) :
    {e : PhysicalMixedWordEvent n shared b A Δ D k s //
      physicalMixedWordWeight n shared b A Δ D kbig ω μ qghost ρ V Vs qedge k s e ≠ 0} ≃
    {e : PhysicalMixedWordEvent n shared B A Δ D k (physicalSmallBigCapEmbed h s) //
      physicalMixedWordWeight n shared B A Δ D kbig ω μ qghost ρ V Vs qedge k (physicalSmallBigCapEmbed h s) e ≠ 0 ∧
      productTotalMemory (physicalMixedWordTarget n shared B A Δ D kbig k (physicalSmallBigCapEmbed h s) e).2 ≤ b} :=
  Equiv.ofBijective (fun e => ⟨physicalMixedWordCapEmbed n shared A Δ D h k s e.val,
    (physicalMixedWordCapEmbed_support n shared A Δ D h kbig ω μ qghost ρ V Vs qedge k s hs e.val).mp e.property⟩) ⟨by
      intro e f hef
      apply Subtype.ext
      exact physicalMixedWordCapEmbed_injective n shared A Δ D h k s (congrArg Subtype.val hef), by
    intro e
    obtain ⟨d, hd⟩ := physicalMixedWordCapEmbed_surjective_of_ne_zero n shared A Δ D h kbig ω μ qghost ρ V Vs qedge k s e.val
      e.property.1 e.property.2
    have hw := (physicalMixedWordCapEmbed_support n shared A Δ D h kbig ω μ qghost ρ V Vs qedge k s hs d).mpr
      (by simpa only [hd] using e.property)
    exact ⟨⟨d, hw⟩, Subtype.ext hd⟩⟩

omit [∀ g, Fintype (P g)] in
theorem physicalMixedWordCapSupportEquiv_apply (k : Option (H ⊕ K))
    (s : PhysicalSmallBigState Ps J ell (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M b))
    (hs : productTotalMemory s.2 ≤ b)
    (e : {e : PhysicalMixedWordEvent n shared b A Δ D k s //
      physicalMixedWordWeight n shared b A Δ D kbig ω μ qghost ρ V Vs qedge k s e ≠ 0}) :
    (physicalMixedWordCapSupportEquiv n shared A Δ D h kbig ω μ qghost ρ V Vs qedge k s hs e).val =
      physicalMixedWordCapEmbed n shared A Δ D h k s e.val := rfl

omit [∀ g, Fintype (P g)] in
theorem physicalMixedWordCapSupportEquiv_target (k : Option (H ⊕ K))
    (s : PhysicalSmallBigState Ps J ell (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M b))
    (hs : productTotalMemory s.2 ≤ b)
    (e : {e : PhysicalMixedWordEvent n shared b A Δ D k s //
      physicalMixedWordWeight n shared b A Δ D kbig ω μ qghost ρ V Vs qedge k s e ≠ 0}) :
    physicalSmallBigCapEmbed h (physicalMixedWordTarget n shared b A Δ D kbig k s e.val) =
      physicalMixedWordTarget n shared B A Δ D kbig k (physicalSmallBigCapEmbed h s)
        (physicalMixedWordCapSupportEquiv n shared A Δ D h kbig ω μ qghost ρ V Vs qedge k s hs e).val := by
  exact (physicalMixedWordCapEmbed_target n shared A Δ D h kbig ω μ qghost ρ V Vs qedge k s e.val e.property).symm

omit [∀ g, Fintype (P g)] in
theorem physicalMixedWordCapSupportEquiv_weight (k : Option (H ⊕ K))
    (s : PhysicalSmallBigState Ps J ell (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M b))
    (hs : productTotalMemory s.2 ≤ b)
    (e : {e : PhysicalMixedWordEvent n shared b A Δ D k s //
      physicalMixedWordWeight n shared b A Δ D kbig ω μ qghost ρ V Vs qedge k s e ≠ 0}) :
    physicalMixedWordWeight n shared B A Δ D kbig ω μ qghost ρ V Vs qedge k (physicalSmallBigCapEmbed h s)
        (physicalMixedWordCapSupportEquiv n shared A Δ D h kbig ω μ qghost ρ V Vs qedge k s hs e).val =
      physicalMixedWordWeight n shared b A Δ D kbig ω μ qghost ρ V Vs qedge k s e.val := by
  exact physicalMixedWordCapEmbed_weight_of_ne_zero n shared A Δ D h kbig ω μ qghost ρ V Vs qedge k s hs e.val e.property

end
end Bounty

end


-- Source module: PhysicalRootLocalPhaseCap
section

/- Exact phase and ledger transport with all original event data retained. -/

open scoped Classical
namespace Bounty
section Root
variable {I : Type} {N M J ell n b B : ℕ} {P : Fin N → Finset ℕ}
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
  (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
  (k : ℕ → I → ℤ) (h : b ≤ B) (V : Fin N → ℝ) (q : ℝ) (ζ : ℕ → I → ℝ)
  (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
    PhysicalAuxLabels P (C i) → ℂ)
  (θ : ℝ) (β : (g : Fin M) → P (e.symm g).val → ℝ)
  (retention : Fin (n + 2) → ℝ) (ρ : ℝ)
  (hPs : ∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p)
  (hPb : ∀ (g : Fin M) p, p ∈ P (e.symm g).val → Nat.Prime p)
  (hdis : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (e.symm g).val))

noncomputable def physicalRootMixedCapWeight :=
  physicalMixedWordWeight (Ps := fun s : ↥groupsᶜ => P s.val) (ell := ell) (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) B
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (i : patterns) _ aux => physicalAuxMass (fun g => V (e.symm g).val) (fun g => C i.val (e.symm g).val) aux)
    (fun g p => β g p / V (e.symm g).val) retention ρ (fun g => V (e.symm g).val) (fun s : ↥groupsᶜ => V s.val) (fun _ => q)

theorem physical_root_mixed_local_phase_cap
    (tag : Option (Fin (n + 2) ⊕ Fin (n + 1)))
    (H : (g : Fin M) → Finset (P (e.symm g).val))
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := b) groups e)
    (a : PhysicalRootMixedEvent groups e patterns C k tag s)
    (hw : physicalRootMixedCapWeight groups e patterns C k V q β retention ρ tag s a ≠ 0) :
    physicalRootMixedLocalPhase groups e patterns C hC k V ζ K θ β ρ hPs hPb hdis tag H (physicalSmallBigCapEmbed h s)
      (physicalMixedWordCapEmbed (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val))
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val)) h tag s a) =
      physicalRootMixedLocalPhase groups e patterns C hC k V ζ K θ β ρ hPs hPb hdis tag H s a := by
  have hp := physical_mixed_big_projection_weight_ne_zero (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) b
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (i : patterns) _ aux => physicalAuxMass (fun g => V (e.symm g).val) (fun g => C i.val (e.symm g).val) aux)
    (fun g p => β g p / V (e.symm g).val) retention ρ (fun g => V (e.symm g).val) (fun s : ↥groupsᶜ => V s.val) (fun _ => q) tag s a hw
  cases tag with
  | none => rfl
  | some tag =>
    cases tag with
    | inl j => rfl
    | inr j =>
      exact physical_effective_combined_phase_cap hPs hPb hdis
        (fun key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val) (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) => fun g => C key.2.1.val (e.symm g).val)
        (fun key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val) (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) => physicalSharedPrefix key.2.2.1)
        (fun key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val) (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) => k (n - key.1.val) key.2.1.val) h
        (fun (key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val) (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1))) _ aux => physicalAuxMass (fun g => V (e.symm g).val) (fun g => C key.2.1.val (e.symm g).val) aux) β ρ (fun g => V (e.symm g).val) retention (fun _ => 0)
        (physicalRootKeyCoefficient groups e patterns C hC ζ k K θ)
        _ H s.2 _ hp

theorem physical_root_mixed_birth_update_cap
    (tag : Option (Fin (n + 2) ⊕ Fin (n + 1)))
    (H : (g : Fin M) → Finset (P (e.symm g).val))
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := b) groups e)
    (a : PhysicalRootMixedEvent groups e patterns C k tag s)
    (hw : physicalRootMixedCapWeight groups e patterns C k V q β retention ρ tag s a ≠ 0) :
    physicalRootMixedBirthUpdate (n := n) groups e patterns C k tag H (physicalSmallBigCapEmbed h s)
      (physicalMixedWordCapEmbed (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val))
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val)) h tag s a) =
      physicalRootMixedBirthUpdate (n := n) groups e patterns C k tag H s a := by
  have hp := physical_mixed_big_projection_weight_ne_zero (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) b
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (i : patterns) _ aux => physicalAuxMass (fun g => V (e.symm g).val) (fun g => C i.val (e.symm g).val) aux)
    (fun g p => β g p / V (e.symm g).val) retention ρ (fun g => V (e.symm g).val) (fun s : ↥groupsᶜ => V s.val) (fun _ => q) tag s a hw
  cases tag with
  | none => rfl
  | some tag =>
    cases tag with
    | inl j => rfl
    | inr j =>
      exact full_mixed_ledger_update_cap (fun g (p : P (e.symm g).val) => p.val)
        (fun key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val) (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) => fun g => physicalFullSharedIndices (ell := ell) (C key.2.1.val (e.symm g).val))
        (fun (key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val) (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1))) _ => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C key.2.1.val (e.symm g).val))
        (fun (key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val) (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1))) => physicalMixedEdgeDelta (fun g => C key.2.1.val (e.symm g).val) (k (n - key.1.val) key.2.1.val) (physicalSharedPrefix key.2.2.1))
        (fun (key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val) (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1))) => physicalMixedEdgeD (fun g => C key.2.1.val (e.symm g).val) (physicalSharedPrefix key.2.2.1)) h
        (fun (key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val) (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1))) _ aux => physicalAuxMass (fun g => V (e.symm g).val) (fun g => C key.2.1.val (e.symm g).val) aux) (fun g p => β g p / V (e.symm g).val) retention ρ (fun g => V (e.symm g).val) _ H s.2 _ hp

end Root
end Bounty

end


-- Source module: DeterministicLedgerCapTransport
section

/- Exact phase and ledger transport with all original event data retained. -/

open scoped Classical
namespace Bounty

theorem deterministic_ledger_phase_invariant_equiv
    {K L X Y : Type*} (E : K → X → Type*) (F : K → Y → Type*)
    (t : ∀ k x, E k x → X) (u : ∀ k y, F k y → Y)
    (e : X → Y) (P : X → Prop)
    (closed : ∀ k x, P x → ∀ a, P (t k x a))
    (δ : ∀ k x, P x → E k x ≃ F k (e x))
    (ht : ∀ k x (hx : P x) a, e (t k x a) = u k (e x) (δ k x hx a))
    (v : ∀ k, L → (x : X) → E k x → L)
    (w : ∀ k, L → (y : Y) → F k y → L)
    (hv : ∀ k l x (hx : P x) a, w k l (e x) (δ k x hx a) = v k l x a)
    (phase : ∀ k, L → (x : X) → E k x → ℂ)
    (phase' : ∀ k, L → (y : Y) → F k y → ℂ)
    (hp : ∀ k l x (hx : P x) a, phase' k l (e x) (δ k x hx a) = phase k l x a)
    (ks : List K) (l : L) (x : X) (hx : P x) (p : FiniteEventPath E t ks x) :
    deterministicLedgerPhase F u w phase' ks l (e x)
        (finiteInvariantPathEquiv E F t u e P closed δ ht ks x hx p) =
      deterministicLedgerPhase E t v phase ks l x p := by
  induction ks generalizing l x with
  | nil => rfl
  | cons k ks ih =>
    rcases p with ⟨a, p⟩
    change phase' k l (e x) (δ k x hx a) *
      deterministicLedgerPhase F u w phase' ks (w k l (e x) (δ k x hx a)) _
        (cast (congrArg (FiniteEventPath F u ks) (ht k x hx a))
          (finiteInvariantPathEquiv E F t u e P closed δ ht ks (t k x a) (closed k x hx a) p)) = _
    rw [hp, hv, deterministic_ledger_phase_cast F u w phase' ks _ (ht k x hx a), ih]
    rfl

theorem deterministic_ledger_phase_selected_forget
    {K L X : Type*} (E : K → X → Type*) (t : ∀ k x, E k x → X)
    (Q : ∀ k x, E k x → Prop)
    (v : ∀ k, L → (x : X) → E k x → L)
    (phase : ∀ k, L → (x : X) → E k x → ℂ)
    (ks : List K) (l : L) (x : X)
    (p : FiniteEventPath (FiniteSelectedEvent E Q) (finiteSelectedTarget E t Q) ks x) :
    deterministicLedgerPhase E t v phase ks l x (finiteSelectedPathForget E t Q ks x p) =
      deterministicLedgerPhase (FiniteSelectedEvent E Q) (finiteSelectedTarget E t Q)
        (fun k l x a => v k l x a.val) (fun k l x a => phase k l x a.val) ks l x p := by
  induction ks generalizing l x with
  | nil => rfl
  | cons k ks ih =>
    rcases p with ⟨a, p⟩
    exact congrArg (phase k l x a.val * ·) (ih _ _ p)

theorem deterministic_ledger_phase_nonzero_lift
    {K L X : Type*} (E : K → X → Type*) (t : ∀ k x, E k x → X)
    (w : ∀ k x, E k x → ℝ)
    (v : ∀ k, L → (x : X) → E k x → L)
    (phase : ∀ k, L → (x : X) → E k x → ℂ)
    (ks : List K) (l : L) (x : X) (p : FiniteEventPath E t ks x)
    (hp : finiteEventPathWeight E t w ks x p ≠ 0) :
    deterministicLedgerPhase (FiniteNonzeroEvent E w) (finiteNonzeroTarget E t w)
        (fun k l x a => v k l x a.val) (fun k l x a => phase k l x a.val)
        ks l x (finiteNonzeroPathLift E t w ks x p hp) =
      deterministicLedgerPhase E t v phase ks l x p := by
  induction ks generalizing l x with
  | nil => rfl
  | cons k ks ih =>
    rcases p with ⟨a, p⟩
    exact congrArg (phase k l x a * ·) (ih _ _ p (mul_ne_zero_iff.mp hp).2)

theorem finite_supported_path_phase_ledger
    {K L X Y : Type*} (E : K → X → Type*) (F : K → Y → Type*)
    (t : ∀ k x, E k x → X) (u : ∀ k y, F k y → Y)
    (weight : ∀ k x, E k x → ℝ) (Q : ∀ k y, F k y → Prop)
    (e : X → Y) (P : X → Prop)
    (closed : ∀ k x, P x → ∀ a : FiniteNonzeroEvent E weight k x, P (t k x a.val))
    (δ : ∀ k x, P x → FiniteNonzeroEvent E weight k x ≃ FiniteSelectedEvent F Q k (e x))
    (ht : ∀ k x (hx : P x) a, e (t k x a.val) = u k (e x) (δ k x hx a).val)
    (v : ∀ k, L → (x : X) → E k x → L)
    (w : ∀ k, L → (y : Y) → F k y → L)
    (hv : ∀ k l x (hx : P x) a, w k l (e x) (δ k x hx a).val = v k l x a.val)
    (phase : ∀ k, L → (x : X) → E k x → ℂ)
    (phase' : ∀ k, L → (y : Y) → F k y → ℂ)
    (hphase : ∀ k l x (hx : P x) a, phase' k l (e x) (δ k x hx a).val = phase k l x a.val)
    (ks : List K) (l : L) (x : X) (hx : P x) (p : FiniteEventPath E t ks x)
    (hp : finiteEventPathWeight E t weight ks x p ≠ 0) :
    finiteSupportedPathPhase E F t u weight Q e P closed δ ht ks
      (fun y p => deterministicLedgerPhase F u w phase' ks l y p) x p =
      deterministicLedgerPhase E t v phase ks l x p := by
  unfold finiteSupportedPathPhase
  rw [dif_pos hx, dif_pos hp]
  dsimp only
  erw [deterministic_ledger_phase_selected_forget]
  erw [deterministic_ledger_phase_invariant_equiv
    (FiniteNonzeroEvent E weight) (FiniteSelectedEvent F Q)
    (finiteNonzeroTarget E t weight) (finiteSelectedTarget F u Q)
    e P closed δ ht (fun k l x a => v k l x a.val) (fun k l y a => w k l y a.val)
    hv (fun k l x a => phase k l x a.val) (fun k l y a => phase' k l y a.val) hphase]
  exact deterministic_ledger_phase_nonzero_lift E t weight v phase ks l x p hp

end Bounty

end


-- Source module: PhysicalMixedWordCapTransport
section

/- Exact moving-small-state transport between big-memory caps. -/
open Finset Classical
namespace Bounty
section
variable {H K S G I : Type} {Ps : S → Finset ℕ} {P : G → Type}
  [Fintype S] [Fintype G] [DecidableEq G] [∀ g, Fintype (P g)]
  (n : ∀ g, P g → ℕ) {J ell : ℕ} {M : G → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (A : I → Type)
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J → SharedActiveLabels P (shared i) → A i → G → ℤ)
  {b B : ℕ} (h : b ≤ B)
  (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)
  (ω : ∀ i, SharedActiveLabels P (shared i) → A i → ℝ) (μ : ∀ g, P g → ℝ)
  (qghost : H → ℝ) (ρ : ℝ) (V : G → ℝ) (Vs : S → ℝ) (qedge : K → ℝ)

noncomputable def physicalMixedWordCapPhase
    (steps : List (Option (H ⊕ K)))
    (phase : ∀ s, PhysicalMixedWordPath (ell := ell) n shared B A Δ D kbig steps s → ℂ) :
    ∀ s, PhysicalMixedWordPath (ell := ell) n shared b A Δ D kbig steps s → ℂ :=
  finiteSupportedPathPhase
    (PhysicalMixedWordEvent (V := H) (ell := ell) n shared b A Δ D) (PhysicalMixedWordEvent (V := H) (ell := ell) n shared B A Δ D)
    (physicalMixedWordTarget n shared b A Δ D kbig)
    (physicalMixedWordTarget n shared B A Δ D kbig)
    (physicalMixedWordWeight n shared b A Δ D kbig ω μ qghost ρ V Vs qedge)
    (finiteSafeEventPredicate (PhysicalMixedWordEvent (V := H) (ell := ell) n shared B A Δ D)
      (physicalMixedWordTarget n shared B A Δ D kbig)
      (physicalMixedWordWeight n shared B A Δ D kbig ω μ qghost ρ V Vs qedge)
      (fun s => productTotalMemory s.2) b)
    (physicalSmallBigCapEmbed h) (fun s => productTotalMemory s.2 ≤ b)
    (fun k s hs e => physicalMixedWord_supported_target n shared A Δ D
      kbig ω μ qghost ρ V Vs qedge k s hs e.val e.property)
    (physicalMixedWordCapSupportEquiv n shared A Δ D h kbig ω μ qghost ρ V Vs qedge)
    (physicalMixedWordCapSupportEquiv_target n shared A Δ D h kbig ω μ qghost ρ V Vs qedge)
    steps phase

omit [∀ g, Fintype (P g)] in
theorem physical_mixed_word_cap_phase_norm_le
    (steps : List (Option (H ⊕ K)))
    (phase : ∀ s, PhysicalMixedWordPath (ell := ell) n shared B A Δ D kbig steps s → ℂ)
    (hphase : ∀ s p, ‖phase s p‖ ≤ 1)
    (s : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M b))
    (p : PhysicalMixedWordPath (ell := ell) n shared b A Δ D kbig steps s) :
    ‖physicalMixedWordCapPhase n shared A Δ D h kbig ω μ qghost ρ V Vs qedge steps phase s p‖ ≤ 1 := by
  exact finite_supported_path_phase_norm_le _ _ _ _ _ _ _ _ _ _ _ steps phase hphase s p

variable [Fintype I] [∀ g p, NeZero (n g p)] [∀ i, Fintype (A i)]

theorem physical_mixed_word_cap_path_action
    (steps : List (Option (H ⊕ K)))
    (phase : ∀ s, PhysicalMixedWordPath (ell := ell) n shared B A Δ D kbig steps s → ℂ)
    (f : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) → ℂ)
    (s : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M b))
    (hs : productTotalMemory s.2 ≤ b) :
    physicalMixedWordPathAction n shared b A Δ D kbig ω μ qghost ρ V Vs qedge steps
        (physicalMixedWordCapPhase n shared A Δ D h kbig ω μ qghost ρ V Vs qedge steps phase)
        (fun s => f (physicalSmallBigCapEmbed h s)) s =
      physicalMixedWordPathAction n shared B A Δ D kbig ω μ qghost ρ V Vs qedge steps
        (fun s p => if physicalMixedWordPeak n shared B A Δ D kbig steps s p ≤ b then phase s p else 0)
        f (physicalSmallBigCapEmbed h s) := by
  let _ : ∀ (k : Option (H ⊕ K)) s, Fintype (PhysicalMixedWordEvent (V := H) (ell := ell) n shared b A Δ D k s) :=
    physicalMixedWordEventFintype (V := H) (ell := ell) n shared b A Δ D
  let _ : ∀ (k : Option (H ⊕ K)) s, Fintype (PhysicalMixedWordEvent (V := H) (ell := ell) n shared B A Δ D k s) :=
    physicalMixedWordEventFintype (V := H) (ell := ell) n shared B A Δ D
  exact finite_safe_path_action_transport
    (PhysicalMixedWordEvent (V := H) (ell := ell) n shared b A Δ D) (PhysicalMixedWordEvent (V := H) (ell := ell) n shared B A Δ D)
    (physicalMixedWordTarget n shared b A Δ D kbig)
    (physicalMixedWordTarget n shared B A Δ D kbig)
    (physicalMixedWordWeight n shared b A Δ D kbig ω μ qghost ρ V Vs qedge)
    (physicalMixedWordWeight n shared B A Δ D kbig ω μ qghost ρ V Vs qedge)
    (fun s => productTotalMemory s.2) b (physicalSmallBigCapEmbed h) (fun s => productTotalMemory s.2 ≤ b)
    (fun k s hs e => physicalMixedWord_supported_target n shared A Δ D
      kbig ω μ qghost ρ V Vs qedge k s hs e.val e.property)
    (physicalMixedWordCapSupportEquiv n shared A Δ D h kbig ω μ qghost ρ V Vs qedge)
    (physicalMixedWordCapSupportEquiv_target n shared A Δ D h kbig ω μ qghost ρ V Vs qedge)
    (physicalMixedWordCapSupportEquiv_weight n shared A Δ D h kbig ω μ qghost ρ V Vs qedge)
    steps phase f s hs hs
end
end Bounty

end


-- Source module: PhysicalRootMixedPhaseCap
section

/- The genuine root mixed phase commutes with increasing memory caps on its original nonzero support. -/

open scoped Classical
namespace Bounty
section Root
variable {I : Type} {N M J ell n b B : ℕ} {P : Fin N → Finset ℕ}
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
  (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
  (k : ℕ → I → ℤ) (h : b ≤ B) (V : Fin N → ℝ) (q : ℝ) (ζ : ℕ → I → ℝ)
  (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
    PhysicalAuxLabels P (C i) → ℂ)
  (θ : ℝ) (β : (g : Fin M) → P (e.symm g).val → ℝ)
  (retention : Fin (n + 2) → ℝ) (ρ : ℝ)
  (hPs : ∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p)
  (hPb : ∀ (g : Fin M) p, p ∈ P (e.symm g).val → Nat.Prime p)
  (hdis : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (e.symm g).val))

noncomputable def physicalRootTransportedMixedPhase :=
  physicalMixedWordCapPhase (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val))
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val)) h
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (i : patterns) _ aux => physicalAuxMass (fun g => V (e.symm g).val) (fun g => C i.val (e.symm g).val) aux)
    (fun g p => β g p / V (e.symm g).val) retention ρ (fun g => V (e.symm g).val) (fun s : ↥groupsᶜ => V s.val) (fun _ => q)
    ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) (physicalRootMixedPhase groups e patterns C hC k V ζ K θ β ρ hPs hPb hdis)

theorem physical_root_mixed_phase_cap
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := b) groups e)
    (hs : productTotalMemory s.2 ≤ b)
    (path : PhysicalRootMixedPath (n := n) groups e patterns C k s)
    (hw : finiteEventPathWeight (PhysicalRootMixedEvent (B := b) groups e patterns C k) (physicalRootMixedTarget (B := b) groups e patterns C k)
      (physicalRootMixedCapWeight groups e patterns C k V q β retention ρ) ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) s path ≠ 0) :
    physicalRootTransportedMixedPhase groups e patterns C hC k h V q ζ K θ β retention ρ hPs hPb hdis s path =
      physicalRootMixedPhase groups e patterns C hC k V ζ K θ β ρ hPs hPb hdis s path := by
  have hh := finite_supported_path_phase_ledger
    (PhysicalRootMixedEvent (B := b) groups e patterns C k) (PhysicalRootMixedEvent (B := B) groups e patterns C k)
    (physicalRootMixedTarget (B := b) groups e patterns C k) (physicalRootMixedTarget (B := B) groups e patterns C k)
    (physicalRootMixedCapWeight groups e patterns C k V q β retention ρ)
    (finiteSafeEventPredicate (PhysicalRootMixedEvent (B := B) groups e patterns C k) (physicalRootMixedTarget (B := B) groups e patterns C k)
      (physicalRootMixedCapWeight groups e patterns C k V q β retention ρ (B := B)) (fun t => productTotalMemory t.2) b)
    (physicalSmallBigCapEmbed h) (fun t => productTotalMemory t.2 ≤ b)
    (fun tag t ht a => physicalMixedWord_supported_target (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val))
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
      (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (i : patterns) _ aux => physicalAuxMass (fun g => V (e.symm g).val) (fun g => C i.val (e.symm g).val) aux)
    (fun g p => β g p / V (e.symm g).val) retention ρ (fun g => V (e.symm g).val) (fun s : ↥groupsᶜ => V s.val) (fun _ => q) tag t ht a.val a.property)
    (physicalMixedWordCapSupportEquiv (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val))
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val)) h
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (i : patterns) _ aux => physicalAuxMass (fun g => V (e.symm g).val) (fun g => C i.val (e.symm g).val) aux)
    (fun g p => β g p / V (e.symm g).val) retention ρ (fun g => V (e.symm g).val) (fun s : ↥groupsᶜ => V s.val) (fun _ => q))
    (physicalMixedWordCapSupportEquiv_target (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val))
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val)) h
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (i : patterns) _ aux => physicalAuxMass (fun g => V (e.symm g).val) (fun g => C i.val (e.symm g).val) aux)
    (fun g p => β g p / V (e.symm g).val) retention ρ (fun g => V (e.symm g).val) (fun s : ↥groupsᶜ => V s.val) (fun _ => q))
    (physicalRootMixedBirthUpdate (n := n) groups e patterns C k (B := b)) (physicalRootMixedBirthUpdate (n := n) groups e patterns C k (B := B))
    (fun tag H t _ a => physical_root_mixed_birth_update_cap groups e patterns C k h V q β retention ρ tag H t a.val a.property)
    (physicalRootMixedLocalPhase groups e patterns C hC k V ζ K θ β ρ hPs hPb hdis (B := b)) (physicalRootMixedLocalPhase groups e patterns C hC k V ζ K θ β ρ hPs hPb hdis (B := B))
    (fun tag H t _ a => physical_root_mixed_local_phase_cap groups e patterns C hC k h V q ζ K θ β retention ρ hPs hPb hdis tag H t a.val a.property)
    ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) (fullActiveInitialLedger s.2) s hs path hw
  unfold physicalRootTransportedMixedPhase physicalMixedWordCapPhase finiteSupportedPathPhase
  erw [dif_pos hs, dif_pos hw]
  dsimp only
  erw [physical_root_mixed_phase_history, physical_root_mixed_phase_history]
  unfold physicalRootMixedHistory
  unfold finiteSupportedPathPhase at hh
  erw [dif_pos hs, dif_pos hw] at hh
  exact hh

theorem physical_root_mixed_phase_cap_weighted
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := b) groups e)
    (hs : productTotalMemory s.2 ≤ b)
    (path : PhysicalRootMixedPath (n := n) groups e patterns C k s) :
    (finiteEventPathWeight (PhysicalRootMixedEvent (B := b) groups e patterns C k) (physicalRootMixedTarget (B := b) groups e patterns C k)
      (physicalRootMixedCapWeight groups e patterns C k V q β retention ρ) ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) s path : ℂ) *
      physicalRootTransportedMixedPhase groups e patterns C hC k h V q ζ K θ β retention ρ hPs hPb hdis s path =
    (finiteEventPathWeight (PhysicalRootMixedEvent (B := b) groups e patterns C k) (physicalRootMixedTarget (B := b) groups e patterns C k)
      (physicalRootMixedCapWeight groups e patterns C k V q β retention ρ) ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) s path : ℂ) *
      physicalRootMixedPhase groups e patterns C hC k V ζ K θ β ρ hPs hPb hdis s path := by
  by_cases hw : finiteEventPathWeight (PhysicalRootMixedEvent (B := b) groups e patterns C k) (physicalRootMixedTarget (B := b) groups e patterns C k)
    (physicalRootMixedCapWeight groups e patterns C k V q β retention ρ) ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) s path = 0
  · simp only [hw, Complex.ofReal_zero, zero_mul]
  · rw [physical_root_mixed_phase_cap groups e patterns C hC k h V q ζ K θ β retention ρ hPs hPb hdis s hs path hw]

theorem physical_root_mixed_phase_cap_action
    [∀ tag s, Fintype (PhysicalRootMixedEvent (P := P) (ell := ell) (n := n) (B := b) groups e patterns C k tag s)]
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := b) groups e)
    (hs : productTotalMemory s.2 ≤ b)
    (F : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := b) groups e → ℂ) :
    finiteEventPathAction (PhysicalRootMixedEvent (P := P) (ell := ell) (n := n) (B := b) groups e patterns C k)
      (physicalRootMixedTarget (B := b) groups e patterns C k)
      (physicalRootMixedCapWeight groups e patterns C k V q β retention ρ)
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
      (physicalRootTransportedMixedPhase groups e patterns C hC k h V q ζ K θ β retention ρ hPs hPb hdis) F s =
    finiteEventPathAction (PhysicalRootMixedEvent (P := P) (ell := ell) (n := n) (B := b) groups e patterns C k)
      (physicalRootMixedTarget (B := b) groups e patterns C k)
      (physicalRootMixedCapWeight groups e patterns C k V q β retention ρ)
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
      (physicalRootMixedPhase groups e patterns C hC k V ζ K θ β ρ hPs hPb hdis) F s := by
  unfold finiteEventPathAction
  apply Finset.sum_congr rfl
  intro path _
  exact congrArg (fun z : ℂ => z * F (finiteEventPathTerminal
    (PhysicalRootMixedEvent (P := P) (ell := ell) (n := n) (B := b) groups e patterns C k)
    (physicalRootMixedTarget (B := b) groups e patterns C k)
    ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) s path))
    (physical_root_mixed_phase_cap_weighted groups e patterns C hC k h V q ζ K θ β retention ρ hPs hPb hdis s hs path)

end Root
end Bounty

end


-- Source module: PhysicalMixedCapEnvelope
section

/- A bounded original path phase is normalized without changing the cap comparison. -/

open Finset
open scoped Classical
namespace Bounty
section
variable {H K S G I : Type} {Ps : S → Finset ℕ} {P : G → Type}
  [Fintype S] [Fintype G] [DecidableEq G] [∀ g, Fintype (P g)]
  (n : ∀ g, P g → ℕ) {J ell : ℕ} {M : G → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (A : I → Type)
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J → SharedActiveLabels P (shared i) → A i → G → ℤ)
  {b B : ℕ} (h : b ≤ B)
  (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)
  (ω : ∀ i, SharedActiveLabels P (shared i) → A i → ℝ) (μ : ∀ g, P g → ℝ)
  (qghost : H → ℝ) (ρ : ℝ) (V : G → ℝ) (Vs : S → ℝ) (qedge : K → ℝ)


omit [∀ g, Fintype (P g)] in
theorem physical_mixed_word_cap_phase_normalize
    (steps : List (Option (H ⊕ K)))
    (phase : ∀ s, PhysicalMixedWordPath (ell := ell) n shared B A Δ D kbig steps s → ℂ)
    (c : ℝ) (hphase : ∀ s p, ‖phase s p‖ ≤ c)
    (s : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M b))
    (p : PhysicalMixedWordPath (ell := ell) n shared b A Δ D kbig steps s) :
    physicalMixedWordCapPhase n shared A Δ D h kbig ω μ qghost ρ V Vs qedge steps phase s p =
      (c : ℂ) * physicalMixedWordCapPhase n shared A Δ D h kbig ω μ qghost ρ V Vs qedge steps
        (fun s p => phase s p / (c : ℂ)) s p := by
  unfold physicalMixedWordCapPhase finiteSupportedPathPhase
  split_ifs
  · exact (real_bound_mul_div_eq (hphase _ _)).symm
  · simp only [mul_zero]
  · simp only [mul_zero]

variable [Fintype I] [∀ g p, NeZero (n g p)] [∀ i, Fintype (A i)]

noncomputable def physicalMixedWordCapDifferenceValue
    (steps : List (Option (H ⊕ K)))
    (phase : ∀ s, PhysicalMixedWordPath (ell := ell) n shared B A Δ D kbig steps s → ℂ)
    (f : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) → ℂ)
    (s : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M b)) : ℂ :=
  physicalMixedWordPathAction n shared B A Δ D kbig ω μ qghost ρ V Vs qedge steps phase f
      (physicalSmallBigCapEmbed h s) -
    physicalMixedWordPathAction n shared b A Δ D kbig ω μ qghost ρ V Vs qedge steps
      (physicalMixedWordCapPhase n shared A Δ D h kbig ω μ qghost ρ V Vs qedge steps phase)
      (fun x => f (physicalSmallBigCapEmbed h x)) s

theorem physical_mixed_word_cap_difference_normalize
    (steps : List (Option (H ⊕ K)))
    (phase : ∀ s, PhysicalMixedWordPath (ell := ell) n shared B A Δ D kbig steps s → ℂ)
    (c : ℝ) (hphase : ∀ s p, ‖phase s p‖ ≤ c)
    (f : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) → ℂ)
    (s : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M b)) :
    physicalMixedWordCapDifferenceValue n shared A Δ D h kbig ω μ qghost ρ V Vs qedge steps phase f s =
      (c : ℂ) * physicalMixedWordCapDifferenceValue n shared A Δ D h kbig ω μ qghost ρ V Vs qedge
        steps (fun s p => phase s p / (c : ℂ)) f s := by
  let : ∀ (tag : Option (H ⊕ K)) s,
      Fintype (PhysicalMixedWordEvent (V := H) (J := J) (ell := ell) n shared B A Δ D tag s) :=
    physicalMixedWordEventFintype (V := H) (J := J) (ell := ell) n shared B A Δ D
  let : ∀ (tag : Option (H ⊕ K)) s,
      Fintype (PhysicalMixedWordEvent (V := H) (J := J) (ell := ell) n shared b A Δ D tag s) :=
    physicalMixedWordEventFintype (V := H) (J := J) (ell := ell) n shared b A Δ D
  have hp : physicalMixedWordCapPhase n shared A Δ D h kbig ω μ qghost ρ V Vs qedge steps phase =
      fun s p => (c : ℂ) * physicalMixedWordCapPhase n shared A Δ D h kbig ω μ qghost ρ V Vs qedge steps
        (fun s p => phase s p / (c : ℂ)) s p := by
    funext s p
    exact physical_mixed_word_cap_phase_normalize n shared A Δ D h kbig ω μ qghost ρ V Vs qedge
      steps phase c hphase s p
  unfold physicalMixedWordCapDifferenceValue
  rw [hp]
  unfold physicalMixedWordPathAction
  rw [finite_event_path_phase_normalize _ _ _ _ phase c hphase,
    finite_event_path_phase_mul]
  ring

variable [∀ p : PhysicalPrime Ps, NeZero p.2.val]

theorem physical_mixed_word_cap_energy_envelope
    (steps : List (Option (H ⊕ K)))
    (f : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) → ℂ)
    (L : ℕ) (Denergy : ℝ)
    (henergy : ∀ phase : ∀ s, PhysicalMixedWordPath (ell := ell) n shared B A Δ D kbig steps s → ℂ,
      (∀ s p, ‖phase s p‖ ≤ 1) →
      physicalSmallBigEnergy Vs (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g)))
        (fun s => if productTotalMemory s.2 ≤ L then
          physicalMixedWordCapDifferenceValue n shared A Δ D h kbig ω μ qghost ρ V Vs qedge
            steps phase f s else 0) ≤ Denergy)
    (phase : ∀ s, PhysicalMixedWordPath (ell := ell) n shared B A Δ D kbig steps s → ℂ)
    (c : ℝ) (hc : 0 ≤ c) (hphase : ∀ s p, ‖phase s p‖ ≤ c) :
    physicalSmallBigEnergy Vs (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g)))
      (fun s => if productTotalMemory s.2 ≤ L then
        physicalMixedWordCapDifferenceValue n shared A Δ D h kbig ω μ qghost ρ V Vs qedge
          steps phase f s else 0) ≤ c ^ 2 * Denergy := by
  have he := henergy (fun s p => phase s p / (c : ℂ))
    (fun s p => norm_div_real_bound_le_one hc (hphase s p))
  have hfun : (fun s => if productTotalMemory s.2 ≤ L then
        physicalMixedWordCapDifferenceValue n shared A Δ D h kbig ω μ qghost ρ V Vs qedge
          steps phase f s else 0) =
      fun s => (c : ℂ) * (if productTotalMemory s.2 ≤ L then
        physicalMixedWordCapDifferenceValue n shared A Δ D h kbig ω μ qghost ρ V Vs qedge
          steps (fun s p => phase s p / (c : ℂ)) f s else 0) := by
    funext s
    split_ifs
    · exact physical_mixed_word_cap_difference_normalize n shared A Δ D h kbig ω μ qghost ρ V Vs qedge
        steps phase c hphase f s
    · simp only [mul_zero]
  rw [hfun, ← physical_small_big_energy_eq, finiteWeightedEnergy_const_mul,
    physical_small_big_energy_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left he (sq_nonneg c)
end
end Bounty

end


-- Source module: PhysicalRootCapActionCoherence
section

/- The genuine root vector difference is the cap-transport difference on supported sources. -/

open Finset Classical
namespace Bounty
section Scalar
variable {I : Type} {N M J ell n b B : ℕ} {P : Fin N → Finset ℕ}
  [∀ z : PhysicalPrime P, NeZero z.2.val]
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
  (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
  (V : Fin N → ℝ) (q : ℝ) (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ)
  (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
    PhysicalAuxLabels P (C i) → ℂ)
  (θ : ℝ)
  (β : PhysicalPrime P → ℝ) (ρ : ℝ)
  (hP : ∀ g a, a ∈ P g → Nat.Prime a)
  (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))

theorem physical_root_scalar_cap_difference_eq
    (h : b ≤ B)
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := b) groups e)
    (hs : productTotalMemory s.2 ≤ b) :
    letI : ∀ g (z : P (e.symm g).val), NeZero z.val :=
      fun g z => inferInstanceAs (NeZero (⟨(e.symm g).val, z⟩ : PhysicalPrime P).2.val)
    physicalRootScalarVectorAction (n := n) (B := B)
        groups e patterns C hC V q ζ k K θ β ρ hP hdis (physicalSmallBigCapEmbed h s) -
      physicalRootScalarVectorAction (n := n) (B := b)
        groups e patterns C hC V q ζ k K θ β ρ hP hdis s =
    physicalMixedWordCapDifferenceValue (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val))
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val)) h
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (i : patterns) _ aux => physicalAuxMass (fun g => V (e.symm g).val) (fun g => C i.val (e.symm g).val) aux)
    (fun g p => β ⟨(e.symm g).val, p⟩ / V (e.symm g).val)
    (fun j => physicalEndpointSchedule q (n + 1) j.val) ρ (fun g => V (e.symm g).val)
    (fun s : ↥groupsᶜ => V s.val) (fun _ => q) ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
    (physicalRootMixedPhase (B := B) groups e patterns C hC k V ζ K θ
      (fun g p => β ⟨(e.symm g).val, p⟩) ρ
      (fun s => hP s.val) (fun g => hP (e.symm g).val)
      (physical_root_group_pools_disjoint groups e hdis))
    (fun s => fullMemoryVacuum s.2) s := by
  let : ∀ g (z : P (e.symm g).val), NeZero z.val :=
    fun g z => inferInstanceAs (NeZero (⟨(e.symm g).val, z⟩ : PhysicalPrime P).2.val)
  let : ∀ tag s, Fintype (PhysicalRootMixedEvent (P := P) (ell := ell) (n := n) (B := b)
      groups e patterns C k tag s) :=
    physicalMixedWordEventFintype (ell := ell)
      (fun g (p : P (e.symm g).val) => p.val)
      (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) b
      (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
      (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
      (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
  rw [physical_root_scalar_vector_action_unfold,
    physical_root_scalar_vector_action_unfold]
  unfold physicalMixedWordCapDifferenceValue
  congr 1
  exact (physical_root_mixed_phase_cap_action groups e patterns C hC k h V q ζ K θ
    (fun g p => β ⟨(e.symm g).val, p⟩)
    (fun j => physicalEndpointSchedule q (n + 1) j.val) ρ
    (fun s => hP s.val) (fun g => hP (e.symm g).val)
    (physical_root_group_pools_disjoint groups e hdis) s hs
    (fun t => fullMemoryVacuum t.2)).symm

end Scalar
end Bounty

end


-- Source module: PhysicalCapPhaseNorm
section

/- Norm bounds for the unchanged original root phase, with its birth ledger and coefficients. -/

open Finset
open scoped Classical
namespace Bounty

theorem deterministic_ledger_phase_norm_bound
    {K L X : Type*} (E : K → X → Type*)
    (target : ∀ k x, E k x → X) (update : ∀ k, L → (x : X) → E k x → L)
    (phase : ∀ k, L → (x : X) → E k x → ℂ)
    (H : ℝ) (hH : 0 ≤ H) (hphase : ∀ k l x e, ‖phase k l x e‖ ≤ H)
    (ks : List K) (l : L) (x : X) (p : FiniteEventPath E target ks x) :
    ‖deterministicLedgerPhase E target update phase ks l x p‖ ≤ H ^ ks.length := by
  induction ks generalizing l x with
  | nil => simp only [deterministicLedgerPhase, norm_one, List.length_nil, pow_zero, le_refl]
  | cons k ks ih =>
    rcases p with ⟨e, p⟩
    simp only [deterministicLedgerPhase, norm_mul, List.length_cons, pow_succ]
    calc
      _ ≤ H * H ^ ks.length := mul_le_mul (hphase k l x e)
        (ih _ _ p) (norm_nonneg _) hH
      _ = _ := mul_comm _ _

theorem physical_active_coefficient_norm_bound
    {N J ell : ℕ} {P : Fin N → Finset ℕ}
    (before after C : Fin N → Finset (Fin J)) (ζ : ℝ)
    (K : PhysicalMarkLists P J ell → PhysicalMarkLists P J ell → PhysicalAuxLabels P C → ℂ)
    (H : ℝ) (hH : 0 ≤ H) (hK : ∀ L R a, ‖K L R a‖ ≤ H)
    (s t : (g : Fin N) → Fin (J + ell) → ↥(P g)) (a : PhysicalAuxLabels P C) :
    ‖physicalActiveCoefficient before after C ζ K s t a‖ ≤ H := by
  unfold physicalActiveCoefficient
  split_ifs
  · rw [norm_mul, physical_phase_norm, mul_one]
    exact hK _ _ _
  all_goals simpa only [norm_zero] using hH

section Combined
variable {I K : Type} {N J ell B : ℕ} {P : Fin N → Finset ℕ}
  (C : K → Fin N → Finset (Fin J)) (k : K → ℤ)
  (ω : ∀ j, SharedActiveLabels (fun g => ↥(P g))
    (fun g => physicalFullSharedIndices (ell := ell) (C j g)) → PhysicalAuxLabels P (C j) → ℝ)
  (β : (g : Fin N) → P g → ℝ) (ρ : ℝ) (V : Fin N → ℝ)
  (ζ : K → ℝ)
  (coeff : ∀ j, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell → PhysicalAuxLabels P (C j) → ℂ)
  (H : ℝ) (hH : 1 ≤ H) (hcoeff : ∀ j L R a, ‖coeff j L R a‖ ≤ H)

include hH hcoeff in
theorem physical_full_key_coefficient_norm_bound
    (tag : Option (I ⊕ K)) (x : PhysicalFullBoundedState P J ell B)
    (e : PhysicalFullLedgerEvent C k tag (fullActiveInitialLedger x, x)) :
    ‖physicalFullKeyCoefficientPhase C k ζ coeff tag x e‖ ≤ H := by
  cases tag with
  | none => simpa only [physicalFullKeyCoefficientPhase, norm_one] using hH
  | some tag => cases tag with
    | inl j => simpa only [physicalFullKeyCoefficientPhase, norm_one] using hH
    | inr j =>
      exact physical_active_coefficient_norm_bound _ _ _ _ _ H (le_trans zero_le_one hH)
        (hcoeff j) _ _ _

include hH hcoeff in
theorem physical_full_combined_phase_norm_bound
    (tag : Option (I ⊕ K)) (ledger : (g : Fin N) → Finset (P g))
    (x : PhysicalFullBoundedState P J ell B)
    (e : PhysicalFullLedgerEvent C k tag (ledger, x)) :
    ‖physicalFullCombinedPhase C k ω β ρ V ζ coeff tag ledger x e‖ ≤ H := by
  rw [physicalFullCombinedPhase, norm_mul]
  exact (mul_le_mul (physical_full_ledger_event_phase_norm_le C k ω β ρ V tag (ledger, x) e)
    (physical_full_key_coefficient_norm_bound C k ζ coeff H hH hcoeff tag x e)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul H)
end Combined

section Root
variable {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
  (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
  (k : ℕ → I → ℤ) (V : Fin N → ℝ) (ζ : ℕ → I → ℝ)
  (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
    PhysicalAuxLabels P (C i) → ℂ)
  (θ : ℝ) (β : (g : Fin M) → P (e.symm g).val → ℝ) (ρ : ℝ)
  (hPs : ∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p)
  (hPb : ∀ (g : Fin M) p, p ∈ P (e.symm g).val → Nat.Prime p)
  (hdis : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (e.symm g).val))


theorem physical_root_key_coefficient_norm_bound
    (H : ℝ)
    (hK : ∀ t < n + 1, ∀ i ∈ patterns, ∀ L R a, ‖K t i L R a‖ ≤ H)
    (key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val)
      (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)))
    (L R : PhysicalMarkLists (fun g => P (e.symm g).val) J ell)
    (a : PhysicalAuxLabels (fun g => P (e.symm g).val)
      (fun g => C key.2.1.val (e.symm g).val)) :
    ‖physicalRootKeyCoefficient groups e patterns C hC ζ k K θ key L R a‖ ≤ H := by
  unfold physicalRootKeyCoefficient physicalGroupReindexedCoefficient
    physicalCoupledBigCoefficient physicalLocalFourierCoefficient
  simp only [norm_mul, physical_phase_norm, mul_one]
  have hp : ∀ θ h, ‖physicalReturnPhase θ h‖ = 1 := by
    intro θ h
    unfold physicalReturnPhase
    simp [Complex.norm_exp, Complex.mul_re]
  rw [hp, mul_one]
  exact hK _ (by omega) _ key.2.1.property _ _ _

theorem physical_root_mixed_local_phase_norm_bound
    (H : ℝ) (hH : 1 ≤ H)
    (hK : ∀ t < n + 1, ∀ i ∈ patterns, ∀ L R a, ‖K t i L R a‖ ≤ H) :
    ∀ tag ledger x event,
      ‖physicalRootMixedLocalPhase (n := n) (B := B) groups e patterns C hC k V ζ K θ β ρ
        hPs hPb hdis tag ledger x event‖ ≤ H := by
  intro tag ledger x event
  unfold physicalRootMixedLocalPhase physicalMixedBigEventPullback
    physicalRootPlannedLocalPhase physicalRootEffectiveLocalPhase
  dsimp only
  apply physical_full_combined_phase_norm_bound
  · exact hH
  · intro key L R a
    exact physical_root_key_coefficient_norm_bound groups e patterns C hC k ζ K θ H hK key L R a

theorem physical_root_mixed_phase_norm_bound
    (H : ℝ) (hH : 1 ≤ H)
    (hK : ∀ t < n + 1, ∀ i ∈ patterns, ∀ L R a, ‖K t i L R a‖ ≤ H)
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e)
    (path : PhysicalRootMixedPath (n := n) groups e patterns C k s) :
    ‖physicalRootMixedPhase groups e patterns C hC k V ζ K θ β ρ hPs hPb hdis s path‖ ≤
      H ^ (4 * (n + 1) + 1) := by
  rw [physical_root_mixed_phase_history]
  unfold physicalRootMixedHistory
  have h := deterministic_ledger_phase_norm_bound
    (PhysicalRootMixedEvent groups e patterns C k)
    (physicalRootMixedTarget groups e patterns C k)
    (physicalRootMixedBirthUpdate (n := n) groups e patterns C k)
    (physicalRootMixedLocalPhase groups e patterns C hC k V ζ K θ β ρ hPs hPb hdis)
    H (le_trans zero_le_one hH)
    (physical_root_mixed_local_phase_norm_bound groups e patterns C hC k V ζ K θ β ρ
      hPs hPb hdis H hH hK) _ (fullActiveInitialLedger s.2) s path
  simpa only [List.length_map, List.length_range] using h

theorem physical_root_mixed_phase_norm_le_one
    (hK : ∀ t < n + 1, ∀ i ∈ patterns, ∀ L R a, ‖K t i L R a‖ ≤ 1)
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e)
    (path : PhysicalRootMixedPath (n := n) groups e patterns C k s) :
    ‖physicalRootMixedPhase groups e patterns C hC k V ζ K θ β ρ hPs hPb hdis s path‖ ≤ 1 := by
  simpa only [one_pow] using physical_root_mixed_phase_norm_bound groups e patterns C hC k
    V ζ K θ β ρ hPs hPb hdis 1 le_rfl hK s path

end Root
end Bounty

end


-- Source module: PhysicalMixedWordCapDifference
section

/- Exact moving-small-state transport between big-memory caps. -/
open Finset Classical
namespace Bounty
section
variable {H K S G I : Type} {Ps : S → Finset ℕ} {P : G → Type}
  [Fintype S] [Fintype G] [DecidableEq G] [∀ g, Fintype (P g)]
  (n : ∀ g, P g → ℕ) {J ell : ℕ} {M : G → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (A : I → Type)
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J → SharedActiveLabels P (shared i) → A i → G → ℤ)
  {b B : ℕ} (h : b ≤ B)
  (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)
  (ω : ∀ i, SharedActiveLabels P (shared i) → A i → ℝ) (μ : ∀ g, P g → ℝ)
  (qghost : H → ℝ) (ρ : ℝ) (V : G → ℝ) (Vs : S → ℝ) (qedge : K → ℝ)

variable [Fintype I] [∀ g p, NeZero (n g p)] [∀ i, Fintype (A i)]
  (steps : List (Option (H ⊕ K)))
  (phase : ∀ s, PhysicalMixedWordPath (ell := ell) n shared B A Δ D kbig steps s → ℂ)
  (f : PhysicalSmallBigState Ps J ell
    (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) → ℂ)

theorem physical_mixed_word_cap_difference
    (s : PhysicalSmallBigState Ps J ell (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M b))
    (hs : productTotalMemory s.2 ≤ b) :
    physicalMixedWordPathAction n shared B A Δ D kbig ω μ qghost ρ V Vs qedge steps phase f (physicalSmallBigCapEmbed h s) -
      physicalMixedWordPathAction n shared b A Δ D kbig ω μ qghost ρ V Vs qedge steps
        (physicalMixedWordCapPhase n shared A Δ D h kbig ω μ qghost ρ V Vs qedge steps phase)
        (fun s => f (physicalSmallBigCapEmbed h s)) s =
      physicalMixedWordPathAction n shared B A Δ D kbig ω μ qghost ρ V Vs qedge steps
        (fun s p => if b < physicalMixedWordPeak n shared B A Δ D kbig steps s p then phase s p else 0)
        f (physicalSmallBigCapEmbed h s) := by
  rw [physical_mixed_word_cap_path_action n shared A Δ D h kbig ω μ qghost ρ V Vs qedge steps phase f s hs]
  let _ : ∀ (k : Option (H ⊕ K)) s, Fintype (PhysicalMixedWordEvent (V := H) (ell := ell) n shared B A Δ D k s) :=
    physicalMixedWordEventFintype (V := H) (ell := ell) n shared B A Δ D
  exact finite_event_path_action_sub_safe (PhysicalMixedWordEvent (V := H) (ell := ell) n shared B A Δ D)
    (physicalMixedWordTarget n shared B A Δ D kbig)
    (physicalMixedWordWeight n shared B A Δ D kbig ω μ qghost ρ V Vs qedge)
    (fun s => productTotalMemory s.2) b steps phase f (physicalSmallBigCapEmbed h s)

theorem physical_mixed_word_cap_difference_mask
    (inputCap : ℕ) (hIb : inputCap ≤ b)
    (s : PhysicalSmallBigState Ps J ell (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M b)) :
    (if productTotalMemory s.2 ≤ inputCap then
      physicalMixedWordPathAction n shared B A Δ D kbig ω μ qghost ρ V Vs qedge steps phase f (physicalSmallBigCapEmbed h s) -
        physicalMixedWordPathAction n shared b A Δ D kbig ω μ qghost ρ V Vs qedge steps
          (physicalMixedWordCapPhase n shared A Δ D h kbig ω μ qghost ρ V Vs qedge steps phase)
          (fun s => f (physicalSmallBigCapEmbed h s)) s
      else 0) =
      physicalMixedWordPathAction n shared B A Δ D kbig ω μ qghost ρ V Vs qedge steps
        (fun s p => if productTotalMemory s.2 ≤ inputCap ∧
          b < physicalMixedWordPeak n shared B A Δ D kbig steps s p then phase s p else 0)
        f (physicalSmallBigCapEmbed h s) := by
  by_cases hs : productTotalMemory s.2 ≤ inputCap
  · rw [if_pos hs, physical_mixed_word_cap_difference n shared A Δ D h kbig ω μ qghost ρ V Vs qedge steps phase f s (hs.trans hIb)]
    unfold physicalMixedWordPathAction finiteEventPathAction
    apply sum_congr rfl
    intro p _
    simp only [physicalSmallBigCapEmbed, productStateCapEmbed_totalMemory, hs, true_and]
    rfl
  · rw [if_neg hs]
    unfold physicalMixedWordPathAction finiteEventPathAction
    simp only [physicalSmallBigCapEmbed, productStateCapEmbed_totalMemory, hs, false_and, if_false, mul_zero, zero_mul, sum_const_zero]

end
end Bounty

end


-- Source module: PhysicalMixedWordBirthGrowth
section

/- Exact ghost-birth counts and memory growth for paths with moving small states. -/
open Finset Classical
namespace Bounty
section
variable {H K S G I : Type} {Ps : S → Finset ℕ} {P : G → Type}
  [Fintype S] [Fintype G] [DecidableEq G] [∀ g, Fintype (P g)]
  (n : ∀ g, P g → ℕ) {J ell : ℕ} {M : G → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ) (A : I → Type)
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J → SharedActiveLabels P (shared i) → A i → G → ℤ)
  (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)

def physicalMixedWordEventBirthCount :
    ∀ (tag : Option (H ⊕ K)) (s : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)),
      PhysicalMixedWordEvent n shared B A Δ D tag s → ℕ
  | none, _, _ => 0
  | some (.inl _), _, e => ∑ g, (e g).1.val
  | some (.inr _), _, _ => 0

noncomputable def physicalMixedWordPathBirthCount (steps : List (Option (H ⊕ K)))
    (s : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B))
    (p : PhysicalMixedWordPath (ell := ell) n shared B A Δ D kbig steps s) : ℕ :=
  finiteEventPathCount (PhysicalMixedWordEvent n shared B A Δ D)
    (physicalMixedWordTarget n shared B A Δ D kbig)
    (physicalMixedWordEventBirthCount n shared B A Δ D) steps s p

omit [DecidableEq G] [∀ g, Fintype (P g)] in
theorem physical_mixed_word_event_memory_le (T : ℕ) (ht : ∀ k g, (shared k g)ᶜ.card ≤ T)
    (tag : Option (H ⊕ K))
    (s : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B))
    (e : PhysicalMixedWordEvent n shared B A Δ D tag s) :
    productTotalMemory (physicalMixedWordTarget n shared B A Δ D kbig tag s e).2 ≤
      productTotalMemory s.2 + physicalMixedWordEventBirthCount n shared B A Δ D tag s e +
        fullMemoryEdgeIndicator tag * (T * Fintype.card G) := by
  cases tag with
  | none =>
    simpa only [physicalMixedWordTarget, physicalMixedWordEventBirthCount,
      fullMemoryEdgeIndicator, Nat.add_zero, Nat.zero_mul] using
      (fullActivePermutation_total_memory e.2 s.2).le
  | some tag =>
    cases tag with
    | inl j =>
      exact (coupledGhostJointEventTarget_memory_le M B s.2 e).trans (by simp only
        [physicalMixedWordEventBirthCount, fullMemoryEdgeIndicator, Nat.zero_mul, Nat.add_zero, le_refl])
    | inr k =>
      have he := fullActiveEdgeEventTarget_memory_le n (fun _ : Unit => shared e.1) B
        (fun _ _ => Unit)
        (fun _ c _ => Δ k e.1 (physicalSharedPrefix s.1.2) c e.2.1)
        (fun _ c _ => D k e.1 (physicalSharedPrefix s.1.2) c e.2.1)
        () s.2 e.2.2.2
      have hc : (∑ g, (shared e.1 g)ᶜ.card) ≤ T * Fintype.card G := by
        calc
          _ ≤ ∑ _g : G, T := sum_le_sum fun g _ => ht e.1 g
          _ = _ := by simp only [sum_const, card_univ, smul_eq_mul, mul_comm]
      exact he.trans (by simpa only [physicalMixedWordEventBirthCount, fullMemoryEdgeIndicator,
        Nat.add_zero, Nat.one_mul] using Nat.add_le_add_left hc (productTotalMemory s.2))

omit [DecidableEq G] [∀ g, Fintype (P g)] in
theorem physical_mixed_word_path_peak_le (T : ℕ) (ht : ∀ k g, (shared k g)ᶜ.card ≤ T)
    (steps : List (Option (H ⊕ K)))
    (s : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B))
    (p : PhysicalMixedWordPath (ell := ell) n shared B A Δ D kbig steps s) :
    physicalMixedWordPeak n shared B A Δ D kbig steps s p ≤
      productTotalMemory s.2 + physicalMixedWordPathBirthCount n shared B A Δ D kbig steps s p +
        fullMemoryEdgeCount steps * (T * Fintype.card G) := by
  induction steps generalizing s with
  | nil =>
    simp only [physicalMixedWordPeak, finiteEventPathMaximum, physicalMixedWordPathBirthCount,
      finiteEventPathCount, fullMemoryEdgeCount, List.map_nil, List.sum_nil,
      Nat.add_zero, Nat.zero_mul, le_refl]
  | cons tag steps ih =>
    rcases p with ⟨e, p⟩
    have he := physical_mixed_word_event_memory_le n shared B A Δ D kbig T ht tag s e
    have hp := ih (physicalMixedWordTarget n shared B A Δ D kbig tag s e) p
    change max (productTotalMemory s.2)
      (physicalMixedWordPeak n shared B A Δ D kbig steps _ p) ≤
        productTotalMemory s.2 +
          (physicalMixedWordEventBirthCount n shared B A Δ D tag s e +
            physicalMixedWordPathBirthCount n shared B A Δ D kbig steps _ p) +
          (fullMemoryEdgeIndicator tag + fullMemoryEdgeCount steps) * (T * Fintype.card G)
    rw [add_mul]
    omega

omit [DecidableEq G] [∀ g, Fintype (P g)] in
theorem physical_mixed_word_exceeds_implies_births
    (T : ℕ) (ht : ∀ k g, (shared k g)ᶜ.card ≤ T)
    (steps : List (Option (H ⊕ K)))
    (s : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B))
    (p : PhysicalMixedWordPath (ell := ell) n shared B A Δ D kbig steps s) (threshold : ℕ)
    (hlarge : threshold < physicalMixedWordPeak n shared B A Δ D kbig steps s p) :
    threshold + 1 - productTotalMemory s.2 - fullMemoryEdgeCount steps * (T * Fintype.card G) ≤
      physicalMixedWordPathBirthCount n shared B A Δ D kbig steps s p := by
  have he := physical_mixed_word_path_peak_le n shared B A Δ D kbig T ht steps s p
  omega
end
end Bounty

end


-- Source module: PhysicalMixedWordBirthTail
section

/- Exact marking of ghost births with moving small states. Edge weights,
residue shifts, and all cap indicators are unchanged. -/
open Finset Classical
namespace Bounty
section
variable {H K S G I : Type} {Ps : S → Finset ℕ} {P : G → Type}
  [Fintype S] [Fintype G] [DecidableEq G] [∀ g, Fintype (P g)]
  (n : ∀ g, P g → ℕ) {J ell : ℕ} {M : G → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ) (A : I → Type)
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J → SharedActiveLabels P (shared i) → A i → G → ℤ)
  (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)
  (ω : ∀ i, A i → ℝ) (μ : ∀ g, P g → ℝ)
  (qghost : H → ℝ) (ρ : ℝ) (V : G → ℝ) (Vs : S → ℝ) (qsmall a : ℝ)

omit [∀ g, Fintype (P g)] in
theorem physical_mixed_word_ghost_scale_event (tag : Option (H ⊕ K))
    (s : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B))
    (e : PhysicalMixedWordEvent n shared B A Δ D tag s) :
    physicalMixedWordVaryingGhostWeight n shared B A Δ D kbig ω μ qghost ρ
        V (fun g => a * V g) Vs qsmall tag s e =
      a ^ physicalMixedWordEventBirthCount n shared B A Δ D tag s e *
        physicalMixedWordWeight n shared B A Δ D kbig (fun i _ => ω i) μ qghost ρ V Vs (fun _ => qsmall) tag s e := by
  cases tag with
  | none => simp only [physicalMixedWordVaryingGhostWeight, physicalMixedWordEventBirthCount,
      pow_zero, one_mul]
  | some tag =>
    cases tag with
    | inl j =>
      change coupledGhostJointEventWeight
          (fun g => physicalGhostRetention (n g) (qghost j) ρ)
          (fun g => physicalGhostTermination (n g) (qghost j) ρ)
          (fun g z => physicalGhostBirth (n g) (qghost j) ρ (a * V g) z)
          (fun g => unrestrictedResidueWeight (μ g)) M B s.2 e =
        a ^ (∑ g, (e g).1.val) *
          coupledGhostJointEventWeight
            (fun g => physicalGhostRetention (n g) (qghost j) ρ)
            (fun g => physicalGhostTermination (n g) (qghost j) ρ)
            (fun g => physicalGhostBirth (n g) (qghost j) ρ (V g))
            (fun g => unrestrictedResidueWeight (μ g)) M B s.2 e
      simp_rw [physicalGhostBirth_scale]
      exact coupledGhostJointEventWeight_birth_scale
        (fun g => physicalGhostRetention (n g) (qghost j) ρ)
        (fun g => physicalGhostTermination (n g) (qghost j) ρ)
        (fun g => physicalGhostBirth (n g) (qghost j) ρ (V g))
        (fun g => unrestrictedResidueWeight (μ g)) a M B s.2 e
    | inr k => simp only [physicalMixedWordVaryingGhostWeight, physicalMixedWordEventBirthCount,
        pow_zero, one_mul]

omit [∀ g, Fintype (P g)] in
theorem physical_mixed_word_ghost_scale_path (steps : List (Option (H ⊕ K)))
    (s : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B))
    (p : PhysicalMixedWordPath (ell := ell) n shared B A Δ D kbig steps s) :
    finiteEventPathWeight (PhysicalMixedWordEvent n shared B A Δ D)
        (physicalMixedWordTarget n shared B A Δ D kbig)
        (physicalMixedWordVaryingGhostWeight n shared B A Δ D kbig ω μ qghost ρ
          V (fun g => a * V g) Vs qsmall) steps s p =
      a ^ physicalMixedWordPathBirthCount n shared B A Δ D kbig steps s p *
        finiteEventPathWeight (PhysicalMixedWordEvent n shared B A Δ D)
          (physicalMixedWordTarget n shared B A Δ D kbig)
          (physicalMixedWordWeight n shared B A Δ D kbig (fun i _ => ω i) μ qghost ρ V Vs (fun _ => qsmall))
          steps s p :=
  finite_event_path_weight_eq_pow_mul (PhysicalMixedWordEvent n shared B A Δ D)
    (physicalMixedWordTarget n shared B A Δ D kbig)
    (physicalMixedWordWeight n shared B A Δ D kbig (fun i _ => ω i) μ qghost ρ V Vs (fun _ => qsmall))
    (physicalMixedWordVaryingGhostWeight n shared B A Δ D kbig ω μ qghost ρ
      V (fun g => a * V g) Vs qsmall)
    (physicalMixedWordEventBirthCount n shared B A Δ D) a
    (physical_mixed_word_ghost_scale_event n shared B A Δ D kbig ω μ qghost ρ V Vs qsmall a)
    steps s p
end
end Bounty


/- Exact exponential extraction for any whole-path mask forcing births. -/
open Finset Classical
namespace Bounty
section
variable {H K S G I : Type} {Ps : S → Finset ℕ} {P : G → Type}
  [Fintype S] [Fintype G] [DecidableEq G] [Fintype I] [∀ g, Fintype (P g)]
  (n : ∀ g, P g → ℕ) [∀ g p, NeZero (n g p)] {J ell : ℕ} {M : G → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ) (A : I → Type) [∀ i, Fintype (A i)]
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J → SharedActiveLabels P (shared i) → A i → G → ℤ)
  (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)
  (ω : ∀ i, A i → ℝ) (μ : ∀ g, P g → ℝ)
  (qghost : H → ℝ) (ρ : ℝ) (V : G → ℝ) (Vs : S → ℝ) (qsmall : ℝ)
  (steps : List (Option (H ⊕ K)))
  (allowed : ∀ s, PhysicalMixedWordPath (ell := ell) n shared B A Δ D kbig steps s → Prop)
  (phase : ∀ s, PhysicalMixedWordPath (ell := ell) n shared B A Δ D kbig steps s → ℂ)

theorem physical_mixed_word_birth_tail_action (a : ℝ) (ha : 0 < a) (r : ℕ)
    (hallowed : ∀ s p, allowed s p → r ≤ physicalMixedWordPathBirthCount n shared B A Δ D kbig steps s p)
    (f : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) → ℂ)
    (s : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)) :
    physicalMixedWordPathAction n shared B A Δ D kbig (fun i _ => ω i) μ qghost ρ V Vs (fun _ => qsmall) steps
        (fun s p => if allowed s p then phase s p else 0) f s =
      (((a ^ r)⁻¹ : ℝ) : ℂ) *
        physicalMixedWordVaryingGhostAction n shared B A Δ D kbig ω μ qghost ρ
          V (fun g => a * V g) Vs qsmall steps
          (fun s p => countTailPhase a r (physicalMixedWordPathBirthCount n shared B A Δ D kbig steps s p)
            (if allowed s p then phase s p else 0)) f s := by
  let _ : ∀ (tag : Option (H ⊕ K)) s,
      Fintype (PhysicalMixedWordEvent (V := H) (ell := ell) n shared B A Δ D tag s) :=
    physicalMixedWordEventFintype n shared B A Δ D
  have he := finite_event_path_counted_tail_eq
    (PhysicalMixedWordEvent (V := H) (ell := ell) n shared B A Δ D)
    (physicalMixedWordTarget n shared B A Δ D kbig)
    (physicalMixedWordWeight n shared B A Δ D kbig (fun i _ => ω i) μ qghost ρ V Vs (fun _ => qsmall))
    (physicalMixedWordVaryingGhostWeight n shared B A Δ D kbig ω μ qghost ρ
      V (fun g => a * V g) Vs qsmall)
    steps (physicalMixedWordPathBirthCount n shared B A Δ D kbig steps) ha
    (physical_mixed_word_ghost_scale_path n shared B A Δ D kbig ω μ qghost ρ V Vs qsmall a steps)
    r (fun s p => if allowed s p then phase s p else 0) f s
  have hphase : (fun s p => if r ≤ physicalMixedWordPathBirthCount n shared B A Δ D kbig steps s p
      then (if allowed s p then phase s p else 0) else 0) =
      (fun s p => if allowed s p then phase s p else 0) := by
    funext s p
    by_cases h : allowed s p
    · simp only [h, if_true, hallowed s p h]
    · simp only [h, if_false, ite_self]
  rw [hphase] at he
  exact he

omit [Fintype I] [∀ g p, NeZero (n g p)] [∀ i, Fintype (A i)]
  [DecidableEq G] [∀ g, Fintype (P g)] in
theorem physical_mixed_word_birth_tail_phase_norm (a : ℝ) (ha : 1 ≤ a) (r : ℕ)
    (hphase : ∀ s p, ‖phase s p‖ ≤ 1)
    (s : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B))
    (p : PhysicalMixedWordPath (ell := ell) n shared B A Δ D kbig steps s) :
    ‖countTailPhase a r (physicalMixedWordPathBirthCount n shared B A Δ D kbig steps s p)
      (if allowed s p then phase s p else 0)‖ ≤ 1 := by
  apply countTailPhase_norm_le_one ha
  split_ifs
  · exact hphase s p
  · simp only [norm_zero, zero_le_one]
end
end Bounty

end


-- Source module: PhysicalMixedWordCapEnergy
section

/- Actual cap truncation on the genuine mixed state, including moving small
labels and residues. The only symmetry assumption is on the terminal test's
big pending-memory coordinates. All path masks remain inside the phase. -/
open Finset Classical
namespace Bounty

theorem exists_physical_mixed_word_cap_difference_energy_bound
    {qsmall vs : ℝ} (hq0 : 0 ≤ qsmall) (hq1 : qsmall < 1) (hvs : 0 < vs) (ell : ℕ) :
    ∃ Ccond : ℝ, 1 ≤ Ccond ∧ ∀ (H K S G Pat : Type) [Fintype Pat] [Fintype S] [DecidableEq S]
      [Fintype G] [DecidableEq G]
      (Ps : S → Finset ℕ) [∀ p : PhysicalPrime Ps, NeZero p.2.val]
      (P : G → Type) [∀ g, Fintype (P g)] (n : ∀ g, P g → ℕ)
      [∀ g p, NeZero (n g p)] (J : ℕ) (M : G → ℕ)
      (shared : Pat → ∀ g, Finset (Fin (M g))) (b B : ℕ) (h : b ≤ B)
      (A : Pat → Type) [∀ i, Fintype (A i)]
      (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J → SharedActiveLabels P (shared i) → A i → G → ℤ)
      (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)
      (ω : ∀ i, A i → ℝ) (μ : ∀ g, P g → ℝ) (qghost : H → ℝ) (ρ : ℝ)
      (V : G → ℝ) (Vs : S → ℝ), (∀ s, vs ≤ Vs s) →
      (∀ k a, 0 ≤ ω k a) → (∀ k, ∑ a, ω k a ≤ 1) →
      ∀ (v vmin vmax : ℝ), 0 < ρ → ρ < 1 → 1 < v → 0 < vmin →
      (∀ g, vmin ≤ V g) → (∀ g, V g ≤ vmax) →
      (∀ g p, 0 < μ g p) → (∀ g, ∑ p, μ g p ≤ 2) →
      (∀ j, 0 ≤ qghost j) → (∀ j, qghost j ≤ 1) →
      (∀ j, qghost j / ρ ^ 2 + ((1 - qghost j) / ρ) / v ≤ 1) →
      (∀ j g, qghost j / ρ ^ 2 + ((1 - qghost j) * (2 * V g) / ρ) / v ≤ 1) →
      ∀ (T : ℕ), (∀ k g, (shared k g)ᶜ.card ≤ T) →
      ∀ (steps : List (Option (H ⊕ K))) (I : ℕ), I ≤ b →
      ∀ (phase : ∀ s, PhysicalMixedWordPath (ell := ell) n shared B A Δ D kbig steps s → ℂ),
      (∀ s p, ‖phase s p‖ ≤ 1) →
      ∀ (f : PhysicalSmallBigState Ps J ell
        (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) → ℂ),
      (∀ s, ProductMemorySymmetric (fun x => f (s, x))) →
      physicalSmallBigEnergy Vs (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g)))
        (fun s : PhysicalSmallBigState Ps J ell
          (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M b) =>
          if productTotalMemory s.2 ≤ I then
            physicalMixedWordPathAction n shared B A Δ D kbig (fun i _ => ω i) μ qghost ρ V Vs (fun _ => qsmall)
              steps phase f (physicalSmallBigCapEmbed h s) -
            physicalMixedWordPathAction n shared b A Δ D kbig (fun i _ => ω i) μ qghost ρ V Vs (fun _ => qsmall) steps
              (physicalMixedWordCapPhase n shared A Δ D h kbig (fun i _ => ω i) μ qghost ρ V Vs (fun _ => qsmall) steps phase)
              (fun x => f (physicalSmallBigCapEmbed h x)) s
          else 0) ≤
        ((2 : ℝ) ^ (b + 1 - I - fullMemoryEdgeCount steps * (T * Fintype.card G)))⁻¹ ^ 2 *
        (steps.map (physicalMixedWordStepEnergy Ccond ρ v vmin vmax (2 * vmax)
          T (Fintype.card S) (Fintype.card G) (Fintype.card Pat))).prod *
        physicalSmallBigEnergy Vs (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g))) f := by
  obtain ⟨Ccond, hCcond, henergy⟩ := exists_physical_mixed_word_path_energy_bound hq0 hq1 hvs ell
  refine ⟨Ccond, hCcond, ?_⟩
  intro H K S G Pat _ _ dS _ dG
  cases Subsingleton.elim dS (Classical.typeDecidableEq S)
  cases Subsingleton.elim dG (Classical.typeDecidableEq G)
  intro Ps _ P _ n _ J M shared b B h A _ Δ D kbig ω μ qghost ρ V Vs hVs
    hω hωmass v vmin vmax hρ0 hρ1 hv hvmin hVlo hVhi hμ hmass
    hqg0 hqg1 hD hC T ht steps I hIb phase hphase f hf
  have hVs0 : ∀ s, 0 < Vs s := fun s => hvs.trans_le (hVs s)
  let r := b + 1 - I - fullMemoryEdgeCount steps * (T * Fintype.card G)
  let allowed : ∀ s, PhysicalMixedWordPath (ell := ell) n shared B A Δ D kbig steps s → Prop := fun s p => productTotalMemory s.2 ≤ I ∧
    b < physicalMixedWordPeak n shared B A Δ D kbig steps s p
  have hallowed : ∀ s p, allowed s p →
      r ≤ physicalMixedWordPathBirthCount n shared B A Δ D kbig steps s p := by
    intro s p hp
    have hg := physical_mixed_word_exceeds_implies_births n shared B A Δ D kbig T ht steps s p b hp.2
    dsimp only [allowed] at hp
    dsimp only [r]
    omega
  let χ := fun s p => countTailPhase 2 r
    (physicalMixedWordPathBirthCount n shared B A Δ D kbig steps s p)
    (if allowed s p then phase s p else 0)
  have hχ : ∀ s p, ‖χ s p‖ ≤ 1 := by
    intro s p
    apply countTailPhase_norm_le_one (by norm_num)
    split_ifs
    · exact hphase s p
    · simp only [norm_zero, zero_le_one]
  have he := henergy H K S G Pat Ps P n J M shared B A Δ D kbig ω μ qghost ρ
    V (fun g => 2 * V g) Vs hVs hω hωmass v vmin vmax (2 * vmax)
    hρ0 hρ1 hv hvmin hVlo hVhi
    (fun g => mul_nonneg (by norm_num) (hvmin.trans_le (hVlo g)).le)
    (fun g => mul_le_mul_of_nonneg_left (hVhi g) (by norm_num))
    hμ hmass hqg0 hqg1 hD hC T ht steps χ hχ f hf
  have heq : physicalMixedWordPathAction n shared B A Δ D kbig (fun i _ => ω i) μ qghost ρ V Vs (fun _ => qsmall) steps
      (fun s p => if allowed s p then phase s p else 0) f =
      fun s => ((((2 : ℝ) ^ r)⁻¹ : ℝ) : ℂ) *
        physicalMixedWordVaryingGhostAction n shared B A Δ D kbig ω μ qghost ρ
          V (fun g => 2 * V g) Vs qsmall steps χ f s := by
    funext s
    have hh := physical_mixed_word_birth_tail_action n shared B A Δ D kbig ω μ qghost ρ V Vs qsmall
      steps allowed phase 2 (by norm_num) r hallowed f s
    convert hh using 1
    · apply congrArg (fun ψ => physicalMixedWordPathAction n shared B A Δ D kbig (fun i _ => ω i) μ qghost ρ V Vs (fun _ => qsmall) steps ψ f s)
      funext y p
      split_ifs <;> rfl
    · apply congrArg (fun ψ => ((((2 : ℝ) ^ r)⁻¹ : ℝ) : ℂ) *
        physicalMixedWordVaryingGhostAction n shared B A Δ D kbig ω μ qghost ρ
          V (fun g => 2 * V g) Vs qsmall steps ψ f s)
      funext y p
      dsimp only [χ]
      split_ifs <;> rfl
  have htail : physicalSmallBigEnergy Vs (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g)))
      (physicalMixedWordPathAction n shared B A Δ D kbig (fun i _ => ω i) μ qghost ρ V Vs (fun _ => qsmall) steps
        (fun s p => if allowed s p then phase s p else 0) f) ≤
      ((2 : ℝ) ^ r)⁻¹ ^ 2 *
        (steps.map (physicalMixedWordStepEnergy Ccond ρ v vmin vmax (2 * vmax)
          T (Fintype.card S) (Fintype.card G) (Fintype.card Pat))).prod *
        physicalSmallBigEnergy Vs (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g))) f := by
    rw [heq, ← physical_small_big_energy_eq, finiteWeightedEnergy_const_mul,
      physical_small_big_energy_eq]
    have hc : ‖((((2 : ℝ) ^ r)⁻¹ : ℝ) : ℂ)‖ = ((2 : ℝ) ^ r)⁻¹ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hc, mul_assoc]
    exact mul_le_mul_of_nonneg_left he (sq_nonneg _)
  have hdiff :
      (fun s : PhysicalSmallBigState Ps J ell
        (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M b) =>
        if productTotalMemory s.2 ≤ I then
          physicalMixedWordPathAction n shared B A Δ D kbig (fun i _ => ω i) μ qghost ρ V Vs (fun _ => qsmall) steps phase f
              (physicalSmallBigCapEmbed h s) -
          physicalMixedWordPathAction n shared b A Δ D kbig (fun i _ => ω i) μ qghost ρ V Vs (fun _ => qsmall) steps
            (physicalMixedWordCapPhase n shared A Δ D h kbig (fun i _ => ω i) μ qghost ρ V Vs (fun _ => qsmall) steps phase)
            (fun x => f (physicalSmallBigCapEmbed h x)) s
        else 0) =
      (fun s => physicalMixedWordPathAction n shared B A Δ D kbig (fun i _ => ω i) μ qghost ρ V Vs (fun _ => qsmall) steps
        (fun y p => if allowed y p then phase y p else 0) f (physicalSmallBigCapEmbed h s)) := by
    funext s
    exact physical_mixed_word_cap_difference_mask n shared A Δ D h kbig (fun i _ => ω i) μ qghost ρ V Vs (fun _ => qsmall)
      steps phase f I hIb s
  erw [hdiff]
  exact (physical_small_big_cap_pullback_energy_le h Vs hVs0 μ
    (fun g => unrestrictedResidueWeight (μ g)) (fun g p => (hμ g p).le)
    (fun g z => (hμ g z.1).le) _).trans htail

end Bounty

end


-- Source module: PhysicalRootCapEnergy
section

/- Quantitative cap truncation for the unchanged original root scalar vector. -/

open Finset
open scoped Classical
namespace Bounty

noncomputable def physicalMixedCapConditioningConstant
    (q vs : ℝ) (ell : ℕ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hvs : 0 < vs) : ℝ :=
  Classical.choose (exists_physical_mixed_word_cap_difference_energy_bound hq0 hq1 hvs ell)

theorem physical_mixed_cap_conditioning_constant_ge_one
    (q vs : ℝ) (ell : ℕ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hvs : 0 < vs) :
    1 ≤ physicalMixedCapConditioningConstant q vs ell hq0 hq1 hvs :=
  (Classical.choose_spec (exists_physical_mixed_word_cap_difference_energy_bound hq0 hq1 hvs ell)).1

section Scalar
variable {I : Type} {N M J ell n b B : ℕ} {P : Fin N → Finset ℕ}
  [∀ z : PhysicalPrime P, NeZero z.2.val]
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
  (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
  (V : Fin N → ℝ) (q : ℝ) (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ)
  (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
    PhysicalAuxLabels P (C i) → ℂ)
  (θ : ℝ)
  (β : PhysicalPrime P → ℝ) (ρ : ℝ)
  (hP : ∀ g a, a ∈ P g → Nat.Prime a)
  (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))

theorem physical_root_scalar_cap_energy_bound
    (h : b ≤ B) (vs : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hvs : 0 < vs)
    (hVs : ∀ s : ↥groupsᶜ, vs ≤ V s.val)
    (hV : ∀ g, 0 < V g) (hMass : ∀ g, ∑ p ∈ P g, 1 / (p : ℝ) = V g)
    (v vmin vmax : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hv : 1 < v) (hvmin : 0 < vmin)
    (hVlo : ∀ g : Fin M, vmin ≤ V (e.symm g).val)
    (hVhi : ∀ g : Fin M, V (e.symm g).val ≤ vmax)
    (hμ : ∀ (g : Fin M) (p : P (e.symm g).val), 0 < β ⟨(e.symm g).val, p⟩ / V (e.symm g).val)
    (hmass : ∀ g : Fin M, ∑ p : P (e.symm g).val, β ⟨(e.symm g).val, p⟩ / V (e.symm g).val ≤ 2)
    (hqg0 : ∀ j : Fin (n + 2), 0 ≤ physicalEndpointSchedule q (n + 1) j.val)
    (hqg1 : ∀ j : Fin (n + 2), physicalEndpointSchedule q (n + 1) j.val ≤ 1)
    (hD : ∀ j : Fin (n + 2), physicalEndpointSchedule q (n + 1) j.val / ρ ^ 2 +
      ((1 - physicalEndpointSchedule q (n + 1) j.val) / ρ) / v ≤ 1)
    (hCghost : ∀ (j : Fin (n + 2)) (g : Fin M), physicalEndpointSchedule q (n + 1) j.val / ρ ^ 2 +
      ((1 - physicalEndpointSchedule q (n + 1) j.val) * (2 * V (e.symm g).val) / ρ) / v ≤ 1)
    (T : ℕ) (hT : ∀ (i : patterns) (g : Fin M),
      (physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val))ᶜ.card ≤ T)
    (H : ℝ) (hH : 1 ≤ H)
    (hK : ∀ t < n + 1, ∀ i ∈ patterns, ∀ L R a, ‖K t i L R a‖ ≤ H) :
    letI : ∀ z : PhysicalPrime (fun s : ↥groupsᶜ => P s.val), NeZero z.2.val :=
      fun z => inferInstanceAs (NeZero (⟨z.1.val, z.2⟩ : PhysicalPrime P).2.val)
    letI : ∀ g (z : P (e.symm g).val), NeZero z.val :=
      fun g z => inferInstanceAs (NeZero (⟨(e.symm g).val, z⟩ : PhysicalPrime P).2.val)
    physicalSmallBigEnergy (fun s : ↥groupsᶜ => V s.val) (productMemoryWeight (fun g p => β ⟨(e.symm g).val, p⟩ / V (e.symm g).val)
      (fun g => unrestrictedResidueWeight (fun p => β ⟨(e.symm g).val, p⟩ / V (e.symm g).val)))
      (fun s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := b) groups e =>
        if productTotalMemory s.2 ≤ 0 then physicalRootScalarVectorAction (n := n) (B := B)
          groups e patterns C hC V q ζ k K θ β ρ hP hdis (physicalSmallBigCapEmbed h s) -
        physicalRootScalarVectorAction (n := n) (B := b)
          groups e patterns C hC V q ζ k K θ β ρ hP hdis s else 0) ≤
      (H ^ (4 * (n + 1) + 1)) ^ 2 * ((((2 : ℝ) ^ (b + 1 - fullMemoryEdgeCount ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) * (T * M)))⁻¹) ^ 2 * (((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))).map (physicalMixedWordStepEnergy (physicalMixedCapConditioningConstant q vs ell hq0 hq1 hvs)
          ρ v vmin vmax (2 * vmax) T (Fintype.card ↥groupsᶜ) M (Fintype.card ↥patterns))).prod) *
      (physicalSmallBigEnergy (fun s : ↥groupsᶜ => V s.val) (productMemoryWeight (fun g p => β ⟨(e.symm g).val, p⟩ / V (e.symm g).val)
      (fun g => unrestrictedResidueWeight (fun p => β ⟨(e.symm g).val, p⟩ / V (e.symm g).val)))
        (fun s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e => fullMemoryVacuum s.2)) := by
  let : ∀ z : PhysicalPrime (fun s : ↥groupsᶜ => P s.val), NeZero z.2.val :=
    fun z => inferInstanceAs (NeZero (⟨z.1.val, z.2⟩ : PhysicalPrime P).2.val)
  let : ∀ g (z : P (e.symm g).val), NeZero z.val :=
    fun g z => inferInstanceAs (NeZero (⟨(e.symm g).val, z⟩ : PhysicalPrime P).2.val)
  have hcore := (Classical.choose_spec
    (exists_physical_mixed_word_cap_difference_energy_bound hq0 hq1 hvs ell)).2
  have henergy := fun phase hphase => hcore (Fin (n + 2)) (Fin (n + 1)) (↥groupsᶜ) (Fin M) (↥patterns)
    (fun s : ↥groupsᶜ => P s.val) (fun g => ↥(P (e.symm g).val)) (fun g (p : P (e.symm g).val) => p.val) J (fun _ => J + ell)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) b B h
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (i : patterns) aux => physicalAuxMass (fun g => V (e.symm g).val) (fun g => C i.val (e.symm g).val) aux) (fun g p => β ⟨(e.symm g).val, p⟩ / V (e.symm g).val) (fun j => physicalEndpointSchedule q (n + 1) j.val) ρ (fun g => V (e.symm g).val) (fun s : ↥groupsᶜ => V s.val) hVs
    (fun i a => physical_aux_mass_nonneg _ _ (fun g => (hV (e.symm g).val).le) a)
    (fun i => (physical_aux_mass_sum _ _ (fun g => hV (e.symm g).val)
      (fun g => hMass (e.symm g).val)).le)
    v vmin vmax hρ0 hρ1 hv hvmin hVlo hVhi hμ hmass hqg0 hqg1 hD hCghost T hT
    ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) 0 (Nat.zero_le b) phase hphase (fun t => fullMemoryVacuum t.2)
    (fun _ => fullMemoryVacuum_symmetric)
  have he := physical_mixed_word_cap_energy_envelope (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val))
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val)) h
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (i : patterns) _ aux => physicalAuxMass (fun g => V (e.symm g).val) (fun g => C i.val (e.symm g).val) aux)
    (fun g p => β ⟨(e.symm g).val, p⟩ / V (e.symm g).val) (fun j => physicalEndpointSchedule q (n + 1) j.val) ρ (fun g => V (e.symm g).val) (fun s : ↥groupsᶜ => V s.val) (fun _ => q)
    ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) (fun t => fullMemoryVacuum t.2) 0
    ((((2 : ℝ) ^ (b + 1 - fullMemoryEdgeCount ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) * (T * M)))⁻¹) ^ 2 * (((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))).map (physicalMixedWordStepEnergy (physicalMixedCapConditioningConstant q vs ell hq0 hq1 hvs)
          ρ v vmin vmax (2 * vmax) T (Fintype.card ↥groupsᶜ) M (Fintype.card ↥patterns))).prod *
      (physicalSmallBigEnergy (fun s : ↥groupsᶜ => V s.val) (productMemoryWeight (fun g p => β ⟨(e.symm g).val, p⟩ / V (e.symm g).val)
      (fun g => unrestrictedResidueWeight (fun p => β ⟨(e.symm g).val, p⟩ / V (e.symm g).val)))
        (fun s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e => fullMemoryVacuum s.2)))
    (by intro phase hphase; simpa only [Nat.sub_zero, Fintype.card_fin,
      physicalMixedCapConditioningConstant, physicalMixedWordCapDifferenceValue] using henergy phase hphase)
    (physicalRootMixedPhase (B := B) groups e patterns C hC k V ζ K θ (fun g p => β ⟨(e.symm g).val, p⟩) ρ
        (fun s => hP s.val) (fun g => hP (e.symm g).val)
        (physical_root_group_pools_disjoint groups e hdis)) (H ^ (4 * (n + 1) + 1)) (pow_nonneg (zero_le_one.trans hH) _)
    (physical_root_mixed_phase_norm_bound groups e patterns C hC k V ζ K θ (fun g p => β ⟨(e.symm g).val, p⟩) ρ
      (fun s => hP s.val) (fun g => hP (e.symm g).val)
      (physical_root_group_pools_disjoint groups e hdis) H hH hK)
  have hfun : (fun s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := b) groups e =>
      if productTotalMemory s.2 ≤ 0 then physicalRootScalarVectorAction (n := n) (B := B)
          groups e patterns C hC V q ζ k K θ β ρ hP hdis (physicalSmallBigCapEmbed h s) -
        physicalRootScalarVectorAction (n := n) (B := b)
          groups e patterns C hC V q ζ k K θ β ρ hP hdis s else 0) =
    (fun s => if productTotalMemory s.2 ≤ 0 then physicalMixedWordCapDifferenceValue (fun g (p : P (e.symm g).val) => p.val)
      (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val))
      (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
      (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
      (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val)) h
      (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
      (fun (i : patterns) _ aux => physicalAuxMass (fun g => V (e.symm g).val) (fun g => C i.val (e.symm g).val) aux)
      (fun g p => β ⟨(e.symm g).val, p⟩ / V (e.symm g).val) (fun j => physicalEndpointSchedule q (n + 1) j.val) ρ (fun g => V (e.symm g).val) (fun s : ↥groupsᶜ => V s.val) (fun _ => q)
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) (physicalRootMixedPhase (B := B) groups e patterns C hC k V ζ K θ (fun g p => β ⟨(e.symm g).val, p⟩) ρ
        (fun s => hP s.val) (fun g => hP (e.symm g).val)
        (physical_root_group_pools_disjoint groups e hdis)) (fun t => fullMemoryVacuum t.2) s else 0) := by
    funext s
    split_ifs with hs
    · exact physical_root_scalar_cap_difference_eq groups e patterns C hC V q ζ k K θ β ρ hP hdis h s
        (hs.trans (Nat.zero_le b))
    · rfl
  rw [hfun]
  simpa only [mul_assoc] using he

end Scalar
end Bounty

end


-- Source module: PhysicalCapNormalizedEnergy
section

/- The same small-residue normalization transports energy between distinct memory caps. -/

open Finset
open scoped Classical

namespace Bounty

theorem physical_small_big_normalized_cross_energy_le
    {S X Y : Type*} [Fintype S] [DecidableEq S] [Fintype X] [Fintype Y]
    {P : S → Finset ℕ} [∀ p : PhysicalPrime P, NeZero p.2.val] {J ell : ℕ}
    (V : S → ℝ) (WX : X → ℝ) (WY : Y → ℝ)
    (F : PhysicalSmallBigState P J ell X → ℂ)
    (output : PhysicalSmallBigState P J ell Y → ℂ) (K : ℝ)
    (h : physicalSmallBigEnergy V WY output ≤ K * physicalSmallBigEnergy V WX F) :
    finiteWeightedEnergy (physicalSmallBigNormalizedMeasure V WY) output ≤
      K * finiteWeightedEnergy (physicalSmallBigNormalizedMeasure V WX) F := by
  rw [physical_small_big_normalized_energy_eq, physical_small_big_normalized_energy_eq]
  calc
    _ ≤ (∏ p : PhysicalPrime P, (1 : ℝ) / p.2.val) *
        (K * physicalSmallBigEnergy V WX F) :=
      mul_le_mul_of_nonneg_left h (physical_small_residue_factor_pos (P := P)).le
    _ = _ := by ring

theorem physical_small_big_normalized_cross_norm_le
    {S X Y : Type*} [Fintype S] [DecidableEq S] [Fintype X] [Fintype Y]
    {P : S → Finset ℕ} [∀ p : PhysicalPrime P, NeZero p.2.val] {J ell : ℕ}
    (V : S → ℝ) (WX : X → ℝ) (WY : Y → ℝ)
    (F : PhysicalSmallBigState P J ell X → ℂ)
    (output : PhysicalSmallBigState P J ell Y → ℂ)
    (H K : ℝ) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (h : physicalSmallBigEnergy V WY output ≤
      H ^ 2 * K * physicalSmallBigEnergy V WX F) :
    cleanActiveNorm (physicalSmallBigNormalizedMeasure V WY) output ≤
      H * Real.sqrt K * cleanActiveNorm (physicalSmallBigNormalizedMeasure V WX) F := by
  have he := physical_small_big_normalized_cross_energy_le V WX WY F output (H ^ 2 * K) h
  have hs := Real.sqrt_le_sqrt he
  rw [Real.sqrt_mul (mul_nonneg (sq_nonneg H) hK),
    Real.sqrt_mul (sq_nonneg H), Real.sqrt_sq hH] at hs
  exact hs

end Bounty

end


-- Source module: PhysicalCapInitialReadout
section

/- A cap-error energy bound gives the original normalized initial readout estimate. -/

open Finset
open scoped Classical

namespace Bounty

section Readout
variable {S G : Type*} [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
  {Ps : S → Finset ℕ} [∀ p : PhysicalPrime Ps, NeZero p.2.val]
  {P : G → Finset ℕ} {Z : G → Type*} [∀ g, Fintype (Z g)] {J ell b B : ℕ}
  (Vs : S → ℝ) (C : G → Finset (Fin J))
  (μ : ∀ g, P g → ℝ) (ν : ∀ g, Z g → ℝ)
  (empty : ∀ g, BoundedOrderedTuple (Z g) b)
  (boundary : PhysicalBareResidueState Ps J ell →
    ProductBoundedOrderedState (fun g => ↥(P g)) Z (fun _ => J + ell) b → ℂ)
  (output : PhysicalSmallBigState Ps J ell
    (ProductBoundedOrderedState (fun g => ↥(P g)) Z (fun _ => J + ell) b) → ℂ)

theorem physical_cap_initial_readout_le_of_energy
    (hVs : ∀ s, 0 < Vs s) (hMass : ∀ s, ∑ p ∈ Ps s, 1 / (p : ℝ) = Vs s)
    (hμ : ∀ g p, 0 ≤ μ g p) (hν : ∀ g z, 0 ≤ ν g z)
    (hempty : ∀ g, (empty g).1.val = 0) (hb : ∀ s x, ‖boundary s x‖ ≤ 1)
    (H K : ℝ) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (he : physicalSmallBigEnergy Vs (productMemoryWeight μ ν) output ≤
      H ^ 2 * K * physicalSmallBigEnergy Vs (productMemoryWeight μ ν)
        (fun s : PhysicalSmallBigState Ps J ell
          (ProductBoundedOrderedState (fun g => ↥(P g)) Z (fun _ => J + ell) B) =>
          fullMemoryVacuum s.2)) :
    ‖physicalSmallBigInitialReadout Vs C μ empty boundary output‖ ≤
      H * Real.sqrt K * ∏ g, (∑ p, μ g p) ^ (J + ell) := by
  let mass := ∏ g, (∑ p, μ g p) ^ (J + ell)
  have hm : 0 ≤ mass := prod_nonneg fun g _ => pow_nonneg (sum_nonneg fun p _ => hμ g p) _
  have hn := physical_small_big_normalized_cross_norm_le Vs
    (productMemoryWeight μ ν) (productMemoryWeight μ ν)
    (fun s : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState (fun g => ↥(P g)) Z (fun _ => J + ell) B) =>
      fullMemoryVacuum s.2) output H K hH hK he
  have hv := physical_small_big_normalized_vacuum_norm_le (J := J) (ell := ell) Vs hVs hMass μ ν hμ
    (fun _ => J + ell) B
  have hr := physical_small_big_initial_readout_norm_le Vs C μ ν empty boundary output
    hVs hMass hμ hν hempty hb
  refine hr.trans ((mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _)).trans ?_)
  calc
    _ ≤ Real.sqrt mass * (H * Real.sqrt K * Real.sqrt mass) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hv (mul_nonneg hH (Real.sqrt_nonneg K)))
        (Real.sqrt_nonneg mass)
    _ = H * Real.sqrt K * (Real.sqrt mass) ^ 2 := by ring
    _ = H * Real.sqrt K * mass := by rw [Real.sq_sqrt hm]

omit [∀ g, Fintype (Z g)] in
theorem physical_cap_initial_readout_mask
    (hempty : ∀ g, (empty g).1.val = 0) (I : ℕ) :
    physicalSmallBigInitialReadout Vs C μ empty boundary
      (fun s => if productTotalMemory s.2 ≤ I then output s else 0) =
      physicalSmallBigInitialReadout Vs C μ empty boundary output := by
  unfold physicalSmallBigInitialReadout
  apply sum_congr rfl
  intro s _
  congr 1
  apply sum_congr rfl
  intro L _
  have ht : productTotalMemory (physicalFullMemoryState C L empty) ≤ I := by
    simp only [physical_full_memory_state_total, hempty, sum_const_zero, Nat.zero_le]
  dsimp only
  rw [if_pos ht]

theorem physical_cap_initial_readout_le_of_masked_energy
    (hVs : ∀ s, 0 < Vs s) (hMass : ∀ s, ∑ p ∈ Ps s, 1 / (p : ℝ) = Vs s)
    (hμ : ∀ g p, 0 ≤ μ g p) (hν : ∀ g z, 0 ≤ ν g z)
    (hempty : ∀ g, (empty g).1.val = 0) (hb : ∀ s x, ‖boundary s x‖ ≤ 1)
    (H K : ℝ) (hH : 0 ≤ H) (hK : 0 ≤ K) (I : ℕ)
    (he : physicalSmallBigEnergy Vs (productMemoryWeight μ ν)
        (fun s => if productTotalMemory s.2 ≤ I then output s else 0) ≤
      H ^ 2 * K * physicalSmallBigEnergy Vs (productMemoryWeight μ ν)
        (fun s : PhysicalSmallBigState Ps J ell
          (ProductBoundedOrderedState (fun g => ↥(P g)) Z (fun _ => J + ell) B) =>
          fullMemoryVacuum s.2)) :
    ‖physicalSmallBigInitialReadout Vs C μ empty boundary output‖ ≤
      H * Real.sqrt K * ∏ g, (∑ p, μ g p) ^ (J + ell) := by
  rw [← physical_cap_initial_readout_mask Vs C μ empty boundary output hempty I]
  exact physical_cap_initial_readout_le_of_energy Vs C μ ν empty boundary
    (fun s => if productTotalMemory s.2 ≤ I then output s else 0)
    hVs hMass hμ hν hempty hb H K hH hK he

end Readout
end Bounty

end


-- Source module: PhysicalMixedPathSupport
section

/- Invalid source states have zero weight on every path containing an edge,
so arbitrary whole-path decorations retain the same support. -/

open Finset
open scoped Classical
namespace Bounty
section Paths
variable {S G I V K : Type} [Fintype S] [Fintype G] [DecidableEq G]
  [Fintype I] {Ps : S → Finset ℕ} {P : G → Type} [∀ g, Fintype (P g)]
  (n : ∀ g, P g → ℕ) [∀ g p, NeZero (n g p)] {J ell : ℕ} {M : G → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (A : I → Type) [∀ i, Fintype (A i)]
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J → SharedActiveLabels P (shared i) → A i → G → ℤ)
  (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)
  (ω : ∀ i, SharedActiveLabels P (shared i) → A i → ℝ)
  (μ : ∀ g, P g → ℝ) (qghost : V → ℝ) (ρ : ℝ) (Vb : G → ℝ)
  (Vs : S → ℝ) (qedge : K → ℝ)

omit [Fintype I] [∀ g, Fintype (P g)] [∀ i, Fintype (A i)] [∀ g p, NeZero (n g p)] in
theorem physical_mixed_word_path_weight_invalid
    (tags : List (Option (V ⊕ K))) (hedge : ∃ k, some (.inr k) ∈ tags)
    (s : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B)
    (p : FiniteEventPath (PhysicalMixedWordEvent (ell := ell) n shared B A Δ D)
      (physicalMixedWordTarget n shared B A Δ D kbig) tags s)
    (h : ¬ physicalResidueMarksValid s.1.1 s.1.2) :
    finiteEventPathWeight (PhysicalMixedWordEvent (ell := ell) n shared B A Δ D)
      (physicalMixedWordTarget n shared B A Δ D kbig)
      (physicalMixedWordWeight n shared B A Δ D kbig ω μ qghost ρ Vb Vs qedge) tags s p = 0 := by
  induction tags generalizing s with
  | nil =>
    rcases hedge with ⟨k, hk⟩
    exact False.elim (List.not_mem_nil hk)
  | cons tag tags ih =>
    rcases p with ⟨ev, p⟩
    cases tag with
    | none =>
      rcases hedge with ⟨k, hk⟩
      have hmem := (List.mem_cons.mp hk).resolve_left (by intro hbad; cases hbad)
      have ht : ¬ physicalResidueMarksValid
          (physicalMixedWordTarget n shared B A Δ D kbig none s ev).1.1
          (physicalMixedWordTarget n shared B A Δ D kbig none s ev).1.2 := by
        change ¬ physicalResidueMarksValid s.1.1 (physicalPermuteLabels ev.1 s.1.2)
        rwa [physical_residue_marks_valid_permute]
      exact mul_eq_zero_of_right _ (ih ⟨k, hmem⟩ _ p ht)
    | some tag =>
      cases tag with
      | inl j =>
        rcases hedge with ⟨k, hk⟩
        have hmem := (List.mem_cons.mp hk).resolve_left (by intro hbad; cases hbad)
        exact mul_eq_zero_of_right _ (ih ⟨k, hmem⟩ _ p h)
      | inr k =>
        simp only [finiteEventPathWeight, physicalMixedWordWeight,
          physicalSmallBigPositiveWeight, physicalResidueVertexWeight, if_neg h,
          zero_mul, mul_zero, ite_self]

theorem physical_mixed_word_path_action_invalid
    (tags : List (Option (V ⊕ K))) (hedge : ∃ k, some (.inr k) ∈ tags)
    (pathPhase : ∀ s, FiniteEventPath (PhysicalMixedWordEvent (ell := ell) n shared B A Δ D)
      (physicalMixedWordTarget n shared B A Δ D kbig) tags s → ℂ)
    (F : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B → ℂ)
    (s : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B)
    (h : ¬ physicalResidueMarksValid s.1.1 s.1.2) :
    physicalMixedWordPathAction n shared B A Δ D kbig ω μ qghost ρ Vb Vs qedge tags pathPhase F s = 0 := by
  unfold physicalMixedWordPathAction finiteEventPathAction
  apply sum_eq_zero
  intro p _
  rw [physical_mixed_word_path_weight_invalid n shared B A Δ D kbig ω μ qghost ρ Vb Vs qedge tags hedge s p h]
  simp only [Complex.ofReal_zero, zero_mul]

end Paths
end Bounty

end


-- Source module: PhysicalRootCapSourceSupport
section

/- Invalid small sources vanish for the genuine whole-path root phase at every cap. -/

open Finset
open scoped Classical
namespace Bounty
section Action
variable {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
  [∀ z : PhysicalPrime P, NeZero z.2.val]
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
  (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
  (k : ℕ → I → ℤ)

  (V : Fin N → ℝ) (q : ℝ) (ζ : ℕ → I → ℝ)
  (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
    PhysicalAuxLabels P (C i) → ℂ)
  (r : PhysicalGroupResidues P groupsᶜ) (θ : ℝ)
  (β : (g : Fin M) → P (e.symm g).val → ℝ)
  (retention : Fin (n + 2) → ℝ) (ρ : ℝ)

  (hPs : ∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p)
  (hPb : ∀ (g : Fin M) p, p ∈ P (e.symm g).val → Nat.Prime p)
  (hdis : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (e.symm g).val))


theorem physical_root_mixed_action_invalid
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (L : PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B)
    (hinvalid : ¬ physicalResidueMarksValid (physicalGroupResidueVector r) L) :
    physicalRootMixedAction groups e patterns C hC k V q ζ K r θ β retention ρ
      hPs hPb hdis f L x = 0 := by
  let _ : ∀ g (z : P (e.symm g).val), NeZero z.val :=
    fun g z => inferInstanceAs (NeZero (⟨(e.symm g).val, z⟩ : PhysicalPrime P).2.val)
  unfold physicalRootMixedAction
  dsimp only
  apply physical_mixed_word_path_action_invalid
  · refine ⟨(0 : Fin (n + 1)), List.mem_map.mpr ⟨2, ?_, ?_⟩⟩
    · simp only [List.mem_range]; omega
    · simpa using physical_selected_fine_tag_edge (0 : Fin (n + 1))
  · exact hinvalid
end Action
section Scalar
variable {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
  [∀ z : PhysicalPrime P, NeZero z.2.val]
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
  (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
  (V : Fin N → ℝ) (q : ℝ) (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ)
  (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
    PhysicalAuxLabels P (C i) → ℂ)
  (θ : ℝ)
  (β : PhysicalPrime P → ℝ) (ρ : ℝ)
  (hP : ∀ g a, a ∈ P g → Nat.Prime a)
  (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))


theorem physical_root_scalar_vector_action_invalid
    (r : PhysicalResidues (fun s : ↥groupsᶜ => P s.val))
    (L : PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B)
    (hinvalid : ¬ physicalResidueMarksValid r L) :
    physicalRootScalarVectorAction (n := n) (B := B)
      groups e patterns C hC V q ζ k K θ β ρ hP hdis ((r, L), x) = 0 := by
  unfold physicalRootScalarVectorAction
  apply physical_root_mixed_action_invalid
  change ¬ physicalResidueMarksValid
    ((physicalGroupResidueVectorEquiv P groupsᶜ)
      ((physicalGroupResidueVectorEquiv P groupsᶜ).symm r)) L
  simpa only [Equiv.apply_symm_apply] using hinvalid

end Scalar
end Bounty

end


-- Source module: PhysicalCapReadoutAlgebra
section

/- Exact initial-readout subtraction and transport between empty-memory caps. -/

open Finset
open scoped Classical
namespace Bounty
section
variable {S G : Type*} [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
  {Ps : S → Finset ℕ} [∀ p : PhysicalPrime Ps, NeZero p.2.val]
  {P : G → Finset ℕ} {Z : G → Type*} {J ell b B : ℕ}
  (Vs : S → ℝ) (C : G → Finset (Fin J)) (μ : ∀ g, P g → ℝ)

theorem physical_small_big_initial_readout_sub
    (empty : ∀ g, BoundedOrderedTuple (Z g) b)
    (boundary : PhysicalBareResidueState Ps J ell →
      ProductBoundedOrderedState (fun g => ↥(P g)) Z (fun _ => J + ell) b → ℂ)
    (F G : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState (fun g => ↥(P g)) Z (fun _ => J + ell) b) → ℂ) :
    physicalSmallBigInitialReadout Vs C μ empty boundary (fun s => F s - G s) =
      physicalSmallBigInitialReadout Vs C μ empty boundary F -
        physicalSmallBigInitialReadout Vs C μ empty boundary G := by
  simp only [physicalSmallBigInitialReadout, mul_sub, sum_sub_distrib]

theorem physical_small_big_initial_readout_cap_pullback
    (h : b ≤ B)
    (F : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState (fun g => ↥(P g)) Z (fun _ => J + ell) B) → ℂ) :
    physicalSmallBigInitialReadout Vs C μ (fun g => fullEmptyBoundedMemory (Z g) b)
      (fun _ _ => 1) (fun s => F (physicalSmallBigCapEmbed h s)) =
    physicalSmallBigInitialReadout Vs C μ (fun g => fullEmptyBoundedMemory (Z g) B)
      (fun _ _ => 1) F := rfl

theorem physical_small_big_initial_readout_cap_sub
    (h : b ≤ B)
    (F : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState (fun g => ↥(P g)) Z (fun _ => J + ell) B) → ℂ)
    (G : PhysicalSmallBigState Ps J ell
      (ProductBoundedOrderedState (fun g => ↥(P g)) Z (fun _ => J + ell) b) → ℂ) :
    physicalSmallBigInitialReadout Vs C μ (fun g => fullEmptyBoundedMemory (Z g) b)
      (fun _ _ => 1) (fun s => F (physicalSmallBigCapEmbed h s) - G s) =
    physicalSmallBigInitialReadout Vs C μ (fun g => fullEmptyBoundedMemory (Z g) B)
      (fun _ _ => 1) F -
    physicalSmallBigInitialReadout Vs C μ (fun g => fullEmptyBoundedMemory (Z g) b)
      (fun _ _ => 1) G := by
  rw [physical_small_big_initial_readout_sub,
    physical_small_big_initial_readout_cap_pullback]
end
end Bounty

end


-- Source module: PhysicalRootCapScalarDifference
section

/- The exact original normalized root scalar difference is a mixed cap readout. -/

open Finset Classical
namespace Bounty
section Scalar
variable {I : Type} {N M J ell n b B : ℕ} {P : Fin N → Finset ℕ}
  [∀ z : PhysicalPrime P, NeZero z.2.val]
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
  (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
  (V : Fin N → ℝ) (q : ℝ) (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ)
  (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
    PhysicalAuxLabels P (C i) → ℂ)
  (θ : ℝ)
  (β : PhysicalPrime P → ℝ) (ρ : ℝ)
  (hP : ∀ g a, a ∈ P g → Nat.Prime a)
  (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))

noncomputable def physicalRootNormalizedMixedScalar : ℂ :=
  ∑ r : PhysicalGroupResidues P groupsᶜ,
    ((∏ a : ↥(physicalPrimeGroups P groupsᶜ), 1 / (a.val.2.val : ℝ) : ℝ) : ℂ) *
      physicalRootMixedScalar (n := n) (B := B)
        groups e patterns C hC V q ζ k K r θ β ρ hP hdis

theorem physical_root_normalized_mixed_scalar_eq_readout :
    letI : ∀ z : PhysicalPrime (fun s : ↥groupsᶜ => P s.val), NeZero z.2.val :=
      fun z => inferInstanceAs (NeZero (⟨z.1.val, z.2⟩ : PhysicalPrime P).2.val)
    physicalRootNormalizedMixedScalar (n := n) (B := B)
      groups e patterns C hC V q ζ k K θ β ρ hP hdis =
    physicalSmallBigInitialReadout
      (fun s : ↥groupsᶜ => V s.val) (fun _ : Fin M => ∅)
      (fun (g : Fin M) (z : P (e.symm g).val) => β ⟨(e.symm g).val, z⟩ / V (e.symm g).val)
      (fun g => fullEmptyBoundedMemory
        (UnrestrictedResidueParticle (fun z : P (e.symm g).val => z.val)) B)
      (fun _ _ => 1)
      (physicalRootScalarVectorAction (n := n) (B := B)
        groups e patterns C hC V q ζ k K θ β ρ hP hdis) := by
  exact physical_root_mixed_scalar_average_eq_readout groups e patterns C hC V q ζ k K θ β ρ hP hdis
    (physical_root_scalar_vector_action_invalid groups e patterns C hC V q ζ k K θ β ρ hP hdis)

theorem physical_root_normalized_mixed_scalar_cap_sub (h : b ≤ B) :
    letI : ∀ z : PhysicalPrime (fun s : ↥groupsᶜ => P s.val), NeZero z.2.val :=
      fun z => inferInstanceAs (NeZero (⟨z.1.val, z.2⟩ : PhysicalPrime P).2.val)
    physicalRootNormalizedMixedScalar (n := n) (B := B)
        groups e patterns C hC V q ζ k K θ β ρ hP hdis -
      physicalRootNormalizedMixedScalar (n := n) (B := b)
        groups e patterns C hC V q ζ k K θ β ρ hP hdis =
    physicalSmallBigInitialReadout
      (fun s : ↥groupsᶜ => V s.val) (fun _ : Fin M => ∅)
      (fun (g : Fin M) (z : P (e.symm g).val) => β ⟨(e.symm g).val, z⟩ / V (e.symm g).val)
      (fun g => fullEmptyBoundedMemory
        (UnrestrictedResidueParticle (fun z : P (e.symm g).val => z.val)) b)
      (fun _ _ => 1)
      (fun s => physicalRootScalarVectorAction (n := n) (B := B)
          groups e patterns C hC V q ζ k K θ β ρ hP hdis (physicalSmallBigCapEmbed h s) -
        physicalRootScalarVectorAction (n := n) (B := b)
          groups e patterns C hC V q ζ k K θ β ρ hP hdis s) := by
  let : ∀ z : PhysicalPrime (fun s : ↥groupsᶜ => P s.val), NeZero z.2.val :=
    fun z => inferInstanceAs (NeZero (⟨z.1.val, z.2⟩ : PhysicalPrime P).2.val)
  have hlarge := physical_root_normalized_mixed_scalar_eq_readout
    (P := P) (J := J) (ell := ell) (n := n) (B := B)
    groups e patterns C hC V q ζ k K θ β ρ hP hdis
  have hsmall := physical_root_normalized_mixed_scalar_eq_readout
    (P := P) (J := J) (ell := ell) (n := n) (B := b)
    groups e patterns C hC V q ζ k K θ β ρ hP hdis
  exact (congrArg₂ (fun x y : ℂ => x - y) hlarge hsmall).trans
    (physical_small_big_initial_readout_cap_sub
      (S := ↥groupsᶜ) (Ps := fun s : ↥groupsᶜ => P s.val)
      (P := fun g : Fin M => P (e.symm g).val)
      (Z := fun g : Fin M => UnrestrictedResidueParticle
        (fun z : P (e.symm g).val => z.val))
      (J := J) (ell := ell) (b := b) (B := B)
      (fun s : ↥groupsᶜ => V s.val) (fun _ : Fin M => ∅)
      (fun (g : Fin M) (z : P (e.symm g).val) => β ⟨(e.symm g).val, z⟩ / V (e.symm g).val)
      h (physicalRootScalarVectorAction (n := n) (B := B)
        groups e patterns C hC V q ζ k K θ β ρ hP hdis)
      (physicalRootScalarVectorAction (n := n) (B := b)
        groups e patterns C hC V q ζ k K θ β ρ hP hdis)).symm

end Scalar
end Bounty

end


-- Source module: PhysicalRootCapScalarBound
section

/- The unchanged normalized root scalar obeys the quantitative memory-cap bound. -/

open Finset
open scoped Classical
namespace Bounty

section Scalar
variable {I : Type} {N M J ell n b B : ℕ} {P : Fin N → Finset ℕ}
  [∀ z : PhysicalPrime P, NeZero z.2.val]
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
  (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
  (V : Fin N → ℝ) (q : ℝ) (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ)
  (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
    PhysicalAuxLabels P (C i) → ℂ)
  (θ : ℝ)
  (β : PhysicalPrime P → ℝ) (ρ : ℝ)
  (hP : ∀ g a, a ∈ P g → Nat.Prime a)
  (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))

theorem physical_root_normalized_mixed_scalar_cap_bound
    (h : b ≤ B) (vs : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hvs : 0 < vs)
    (hVs : ∀ s : ↥groupsᶜ, vs ≤ V s.val)
    (hV : ∀ g, 0 < V g) (hMass : ∀ g, ∑ p ∈ P g, 1 / (p : ℝ) = V g)
    (v vmin vmax : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hv : 1 < v) (hvmin : 0 < vmin)
    (hVlo : ∀ g : Fin M, vmin ≤ V (e.symm g).val)
    (hVhi : ∀ g : Fin M, V (e.symm g).val ≤ vmax)
    (hμ : ∀ (g : Fin M) (p : P (e.symm g).val), 0 < β ⟨(e.symm g).val, p⟩ / V (e.symm g).val)
    (hmass : ∀ g : Fin M, ∑ p : P (e.symm g).val, β ⟨(e.symm g).val, p⟩ / V (e.symm g).val ≤ 2)
    (hqg0 : ∀ j : Fin (n + 2), 0 ≤ physicalEndpointSchedule q (n + 1) j.val)
    (hqg1 : ∀ j : Fin (n + 2), physicalEndpointSchedule q (n + 1) j.val ≤ 1)
    (hD : ∀ j : Fin (n + 2), physicalEndpointSchedule q (n + 1) j.val / ρ ^ 2 +
      ((1 - physicalEndpointSchedule q (n + 1) j.val) / ρ) / v ≤ 1)
    (hCghost : ∀ (j : Fin (n + 2)) (g : Fin M), physicalEndpointSchedule q (n + 1) j.val / ρ ^ 2 +
      ((1 - physicalEndpointSchedule q (n + 1) j.val) * (2 * V (e.symm g).val) / ρ) / v ≤ 1)
    (T : ℕ) (hT : ∀ (i : patterns) (g : Fin M),
      (physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val))ᶜ.card ≤ T)
    (H : ℝ) (hH : 1 ≤ H)
    (hK : ∀ t < n + 1, ∀ i ∈ patterns, ∀ L R a, ‖K t i L R a‖ ≤ H) :
    ‖physicalRootNormalizedMixedScalar (n := n) (B := B)
        groups e patterns C hC V q ζ k K θ β ρ hP hdis -
      physicalRootNormalizedMixedScalar (n := n) (B := b)
        groups e patterns C hC V q ζ k K θ β ρ hP hdis‖ ≤
      H ^ (4 * (n + 1) + 1) *
        ((2 : ℝ) ^ (b + 1 - fullMemoryEdgeCount
          ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) * (T * M)))⁻¹ *
        Real.sqrt ((((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))).map
          (physicalMixedWordStepEnergy (physicalMixedCapConditioningConstant q vs ell hq0 hq1 hvs)
            ρ v vmin vmax (2 * vmax) T (Fintype.card ↥groupsᶜ) M (Fintype.card ↥patterns))).prod) *
        ∏ g : Fin M, (∑ p : P (e.symm g).val,
          β ⟨(e.symm g).val, p⟩ / V (e.symm g).val) ^ (J + ell) := by
  let : ∀ z : PhysicalPrime (fun s : ↥groupsᶜ => P s.val), NeZero z.2.val :=
    fun z => inferInstanceAs (NeZero (⟨z.1.val, z.2⟩ : PhysicalPrime P).2.val)
  let : ∀ g (z : P (e.symm g).val), NeZero z.val :=
    fun g z => inferInstanceAs (NeZero (⟨(e.symm g).val, z⟩ : PhysicalPrime P).2.val)
  let steps := (List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))
  let E := (steps.map (physicalMixedWordStepEnergy
    (physicalMixedCapConditioningConstant q vs ell hq0 hq1 hvs)
    ρ v vmin vmax (2 * vmax) T (Fintype.card ↥groupsᶜ) M (Fintype.card ↥patterns))).prod
  let loss := ((2 : ℝ) ^ (b + 1 - fullMemoryEdgeCount steps * (T * M)))⁻¹
  have hE : 0 ≤ E := by
    apply List.prod_nonneg
    intro x hx
    obtain ⟨tag, _, rfl⟩ := List.mem_map.mp hx
    exact physical_mixed_word_step_energy_nonneg _ _ _ _ _ _ _ _ _ _
      (zero_le_one.trans (physical_mixed_cap_conditioning_constant_ge_one q vs ell hq0 hq1 hvs)) tag
  have hloss : 0 ≤ loss := inv_nonneg.mpr (pow_nonneg (by norm_num) _)
  have he := physical_root_scalar_cap_energy_bound groups e patterns C hC V q ζ k K θ β ρ hP hdis
    h vs hq0 hq1 hvs hVs hV hMass v vmin vmax hρ0 hρ1 hv hvmin hVlo hVhi hμ hmass
    hqg0 hqg1 hD hCghost T hT H hH hK
  have hr := physical_cap_initial_readout_le_of_masked_energy (J := J) (ell := ell) (b := b) (B := B)
    (fun s : ↥groupsᶜ => V s.val) (fun _ : Fin M => ∅)
    (fun (g : Fin M) (p : P (e.symm g).val) => β ⟨(e.symm g).val, p⟩ / V (e.symm g).val)
    (fun g => unrestrictedResidueWeight
      (fun p => β ⟨(e.symm g).val, p⟩ / V (e.symm g).val))
    (fun g => fullEmptyBoundedMemory
      (UnrestrictedResidueParticle (fun z : P (e.symm g).val => z.val)) b)
    (fun _ _ => 1)
    (fun s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := b) groups e =>
      physicalRootScalarVectorAction (n := n) (B := B)
        groups e patterns C hC V q ζ k K θ β ρ hP hdis (physicalSmallBigCapEmbed h s) -
      physicalRootScalarVectorAction (n := n) (B := b)
        groups e patterns C hC V q ζ k K θ β ρ hP hdis s)
    (fun s => hV s.val) (fun s => hMass s.val)
    (fun g p => (hμ g p).le) (fun g z => (hμ g z.1).le)
    (fun _ => rfl) (by intro s x; simp only [norm_one, le_refl])
    (H ^ (4 * (n + 1) + 1)) (loss ^ 2 * E)
    (pow_nonneg (zero_le_one.trans hH) _) (mul_nonneg (sq_nonneg loss) hE) 0 he
  apply (congrArg norm (physical_root_normalized_mixed_scalar_cap_sub
    groups e patterns C hC V q ζ k K θ β ρ hP hdis h)).le.trans
  simpa only [Real.sqrt_mul (sq_nonneg loss), Real.sqrt_sq hloss, mul_assoc] using hr

end Scalar
end Bounty

end


-- Source module: OriginalRootCapError
section

/- The original scalar cap error decays at the original root-moment power. -/

open Finset Filter
open scoped Classical
namespace Bounty

theorem eventually_original_root_scalar_cap_error
    {q vs ρ v vmin vmax CG PG HG F : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hvs : 0 < vs)
    (hCG : 0 ≤ CG) (hPG : 0 ≤ PG) (hHG : 0 ≤ HG) (hF : 0 ≤ F)
    (J ell T : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      let n := 2*Nat.ceil (L^(13/25 : ℝ))-1
      ∀ (I : Type) (N M b B : ℕ) (P : Fin N → Finset ℕ)
        [∀ z : PhysicalPrime P, NeZero z.2.val]
        (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
        (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
        (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
        (V : Fin N → ℝ) (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ)
        (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
          PhysicalAuxLabels P (C i) → ℂ)
        (θ : ℝ) (β : PhysicalPrime P → ℝ)
        (hP : ∀ g a, a ∈ P g → Nat.Prime a)
        (hdis : Pairwise (fun g h => Disjoint (P g) (P h))),
      L ≤ (b : ℝ) → b ≤ B →
      (Fintype.card ↥groupsᶜ : ℝ) ≤ CG*Real.log L →
      (M : ℝ) ≤ CG*Real.log L → (Fintype.card ↥patterns : ℝ) ≤ L^PG →
      (∀ s : ↥groupsᶜ, vs ≤ V s.val) →
      (∀ g, 0 < V g) → (∀ g, ∑ p ∈ P g, 1/(p : ℝ) = V g) →
      0 < ρ → ρ < 1 → 1 < v → 0 < vmin →
      (∀ g : Fin M, vmin ≤ V (e.symm g).val) →
      (∀ g : Fin M, V (e.symm g).val ≤ vmax) →
      (∀ (g : Fin M) (p : P (e.symm g).val), 0 < β ⟨(e.symm g).val, p⟩ / V (e.symm g).val) →
      (∀ g : Fin M, ∑ p : P (e.symm g).val, β ⟨(e.symm g).val, p⟩ / V (e.symm g).val ≤ 2) →
      (∀ j : Fin (n+2), 0 ≤ physicalEndpointSchedule q (n+1) j.val) →
      (∀ j : Fin (n+2), physicalEndpointSchedule q (n+1) j.val ≤ 1) →
      (∀ j : Fin (n+2), physicalEndpointSchedule q (n+1) j.val / ρ^2 +
        ((1-physicalEndpointSchedule q (n+1) j.val)/ρ)/v ≤ 1) →
      (∀ (j : Fin (n+2)) (g : Fin M), physicalEndpointSchedule q (n+1) j.val / ρ^2 +
        ((1-physicalEndpointSchedule q (n+1) j.val)*(2*V (e.symm g).val)/ρ)/v ≤ 1) →
      (∀ (i : patterns) (g : Fin M),
        (physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val))ᶜ.card ≤ T) →
      ∀ H : ℝ, 1 ≤ H → H ≤ L^HG →
      (∀ t < n+1, ∀ i ∈ patterns, ∀ L R a, ‖K t i L R a‖ ≤ H) →
      ‖physicalRootNormalizedMixedScalar (n := n) (B := B)
          groups e patterns C hC V q ζ k K θ β ρ hP hdis -
        physicalRootNormalizedMixedScalar (n := n) (B := b)
          groups e patterns C hC V q ζ k K θ β ρ hP hdis‖ ≤
        (L^(-F))^(2*Nat.ceil (L^(13/25 : ℝ))) := by
  let A := physicalMixedCapConditioningConstant q vs ell hq0 hq1 hvs
  let D := max 1 (max A (max (physicalGhostUniformEnergyBound ρ (2*vmax) v)
    (unrestrictedEdgeEnergyBound ρ v vmin vmax T)))
  have hD : 1 ≤ D := le_max_left _ _
  have hA : 0 ≤ A := zero_le_one.trans
    (physical_mixed_cap_conditioning_constant_ge_one q vs ell hq0 hq1 hvs)
  have hAD : A ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hgD : physicalGhostUniformEnergyBound ρ (2*vmax) v ≤ D :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have heD : unrestrictedEdgeEnergyBound ρ v vmin vmax T ≤ D :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  filter_upwards [eventually_root_mixed_cap_cost_bound hD hCG hPG hHG hF hA hAD hgD T (J+ell) heD,
    eventually_ge_atTop (1 : ℝ)] with L hcost hL
  intro n I N M b B P _ groups e patterns C hC V ζ k K θ β hP hdis hb hbb
    hs hm hp hVs hV hMass hρ0 hρ1 hv hvmin hVlo hVhi hμ hmass hqg0 hqg1 hDghost hCghost hT H hH hHpow hK
  have hpower : 1 ≤ L^(13/25 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hr : 1 ≤ Nat.ceil (L^(13/25 : ℝ)) := by
    have h := hpower.trans (Nat.le_ceil (L^(13/25 : ℝ)))
    exact_mod_cast h
  have hn : n+1 = 2*Nat.ceil (L^(13/25 : ℝ)) := by dsimp only [n]; omega
  let steps := (List.range (4*(n+1)+1)).map (physicalSelectedFineTag (n+1))
  have hlen : (steps.length : ℝ) ≤ 17*L^(13/25 : ℝ) := by
    simpa only [steps, List.length_map, List.length_range, hn] using
      (root_moment_length_and_loss hL M T hm).1
  have hbound := hcost b (Fintype.card ↥groupsᶜ) M (Fintype.card ↥patterns) hb hs hm hp
    _ _ steps hlen H (zero_le_one.trans hH) hHpow
    (fun g : Fin M => ∑ p : P (e.symm g).val, β ⟨(e.symm g).val, p⟩ / V (e.symm g).val)
    (fun g => ⟨sum_nonneg (fun p _ => (hμ g p).le), hmass g⟩)
  apply (physical_root_normalized_mixed_scalar_cap_bound groups e patterns C hC V q ζ k K θ β ρ hP hdis
    hbb vs hq0 hq1 hvs hVs hV hMass v vmin vmax hρ0 hρ1 hv hvmin hVlo hVhi hμ hmass
    hqg0 hqg1 hDghost hCghost T hT H hH hK).trans
  simpa only [steps, List.length_map, List.length_range, A] using hbound

end Bounty

end
