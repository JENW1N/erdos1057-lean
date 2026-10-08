import ActualCandidateNumberedInputs

/-! The actual half-endpoint high-rank estimate in the common candidate environment. -/

open scoped Topology BigOperators Classical

-- Source module: ActualRootHalfParameters
section

/- The literal half-endpoint weights supply the mass, atom, and ghost
hypotheses of the original high-rank forest estimate. -/

open scoped BigOperators Classical

namespace Bounty

theorem actual_root_half_parameters
    {G : Type*} (P : G → Finset ℕ) (V : G → ℝ) (edges : ℕ)
    (L vmin vmax : ℝ) (hvmin : 0 < vmin) (hvmax : 0 ≤ vmax)
    (hVmin : ∀ g, vmin ≤ V g) (hVmax : ∀ g, V g ≤ vmax)
    (hMass : ∀ g, ∑ p ∈ P g, 1 / (p : ℝ) = V g)
    (hsize : ∀ g (p : P g), 2 * (edges + 1) ≤ p.val)
    (hprime : ∀ g (p : P g), Real.exp (L ^ (3/10 : ℝ)) ≤ (p.val : ℝ)) :
    let v := 100 * (vmax + 1)
    let η := (2 / vmin) * Real.exp (-(L ^ (3/10 : ℝ)))
    let ε := max (2 / vmin) (2 * vmax * v / ((9/10 : ℝ) * vmin)) *
      Real.exp (-(L ^ (3/10 : ℝ)))
    1 < v ∧ 0 < η ∧ η ≤ ε ∧ 0 < ε ∧
      (∀ g (p : P g),
        0 < ((p.val : ℝ) * physicalEndpointBaseline (1/2) edges p.val)⁻¹ / V g ∧
        ((p.val : ℝ) * physicalEndpointBaseline (1/2) edges p.val)⁻¹ / V g ≤ η) ∧
      (∀ g, (∑ p : P g,
        ((p.val : ℝ) * physicalEndpointBaseline (1/2) edges p.val)⁻¹ / V g) ≤ 2) ∧
      (∀ j : ℕ,
        0 ≤ physicalEndpointSchedule (1/2) edges j ∧
        physicalEndpointSchedule (1/2) edges j ≤ 1 ∧
        physicalEndpointSchedule (1/2) edges j / (9/10 : ℝ)^2 +
          ((1 - physicalEndpointSchedule (1/2) edges j) / (9/10 : ℝ)) / v ≤ 1 ∧
        ∀ g,
          physicalEndpointSchedule (1/2) edges j / (9/10 : ℝ)^2 +
            (((1 - physicalEndpointSchedule (1/2) edges j) * V g) / (9/10 : ℝ)) / v ≤ 1 ∧
          physicalEndpointSchedule (1/2) edges j / (9/10 : ℝ)^2 +
            (((1 - physicalEndpointSchedule (1/2) edges j) * (2 * V g)) / (9/10 : ℝ)) / v ≤ 1) ∧
      (∀ (j : ℕ) g,
        |(1 - physicalEndpointSchedule (1/2) edges j) * V g / (9/10 : ℝ)| * η * v ≤ ε) := by
  intro v η ε
  have hq0 : (0 : ℝ) ≤ 1/2 := by norm_num
  have hq1 : (1/2 : ℝ) ≤ 1 := by norm_num
  have hVpos : ∀ g, 0 < V g := fun g => hvmin.trans_le (hVmin g)
  have hv : 1 < v := by dsimp only [v]; linarith
  have hr := root_birth_rarity_envelope_bounds (L := L) (vmax := vmax)
    (ρ := (9/10 : ℝ)) (v := v) hvmin (by norm_num) (by linarith)
  have hs (j : ℕ) := physical_endpoint_schedule_unit hq0 hq1 edges j
  have hghost := physical_endpoint_half_ghost_budgets hvmax edges
  refine ⟨hv, hr.1, hr.2.1, hr.2.2.1, ?_, ?_, ?_, ?_⟩
  · intro g p
    refine ⟨physical_root_endpoint_weight_pos V (1/2) edges hq0 hq1 hVpos hsize g p, ?_⟩
    have hp0 : 0 < p.val := by have := hsize g p; omega
    exact physical_root_reciprocal_atom_bound p.val hvmin (hVmin g)
      (physical_endpoint_baseline_bounds hq0 hq1 edges p.val hp0 (hsize g p)).1
      (hprime g p)
  · exact physical_root_endpoint_weight_sum_le_two V (1/2) edges hq0 hq1 hVpos hMass hsize
  · intro j
    refine ⟨(hs j).1, (hs j).2, (hghost.2 j).1, ?_⟩
    intro g
    refine ⟨?_, (hghost.2 j).2 (V g) (hVpos g).le (hVmax g)⟩
    exact root_ghost_scalar_budget (hs j).1
      (physical_endpoint_half_schedule_le_three_quarters edges j) hvmax
      (hVpos g).le ((hVmax g).trans (by linarith))
  · intro j g
    exact hr.2.2.2 _ (V g) (hs j).1 (hs j).2 (hVmin g) (hVmax g)

end Bounty

end


-- Source module: ActualRootHalfRankPower
section

/- The original forest contribution for the literal half-endpoint law has
a polynomial prefactor and the explicit prime-atom rarity power. -/

open Finset
open scoped Classical
namespace Bounty

theorem exists_physical_root_half_high_rank_power {vs vmin vmax : ℝ}
    (hvs : 0 < vs) (hvmin : 0 < vmin) (hvmax : 0 ≤ vmax) (ell : ℕ) :
    ∃ Ahi : ℝ, 1 ≤ Ahi ∧
    ∀ (I : Type) (N M J n B : ℕ) (P : Fin N → Finset ℕ)
      (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
      [∀ z : PhysicalPrime P, NeZero z.2.val]
      (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
      (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
      (k : ℕ → I → ℤ) (V : Fin N → ℝ) (_i0 : patterns)
      (ζ : ℕ → I → ℝ)
      (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
        PhysicalAuxLabels P (C i) → ℂ)
      (encode : ((g : Fin M) × P (e.symm g).val) → ℤ), Function.Injective encode →
      ∀ (L Cgroup Ccoeff Arow Hkernel : ℝ) (T : ℕ),
      1 ≤ L → 0 ≤ Cgroup → 0 ≤ Ccoeff → 1 ≤ Arow → 1 ≤ Hkernel →
      Real.exp (2 * vmax * (100 * (vmax + 1)) / (9/10 : ℝ)) ≤ Arow →
      unrestrictedEdgeRowBound (9/10) (100 * (vmax + 1)) vmin T ≤ Arow →
      (∀ s : ↥groupsᶜ, vs ≤ V s.val) →
      (∀ g : Fin M, vmin ≤ V (e.symm g).val) →
      (∀ g : Fin M, V (e.symm g).val ≤ vmax) →
      (∀ g, ∑ p ∈ P g, 1 / (p : ℝ) = V g) →
      (∀ g p, p ∈ P g → Nat.Prime p) →
      Pairwise (fun g h => Disjoint (P g) (P h)) →
      (∀ (g : Fin M) (p : P (e.symm g).val), 2 * (n + 2) ≤ p.val) →
      (∀ (g : Fin M) (p : P (e.symm g).val),
        Real.exp (L ^ (3/10 : ℝ)) ≤ (p.val : ℝ)) →
      (∀ (i : patterns) (g : Fin M),
        (physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val))ᶜ.card ≤ T) →
      (M : ℝ) ≤ Cgroup * Real.log L →
      (Ahi ^ groupsᶜ.card * (patterns.card : ℝ)) * Hkernel ≤ L ^ Ccoeff →
      (∀ time < n + 1, ∀ i ∈ patterns, ∀ U W aux, ‖K time i U W aux‖ ≤ Hkernel) →
      let budget := Ccoeff + 4 * Cgroup * Real.log Arow +
        (Cgroup * ((J + ell : ℕ) : ℝ)) * Real.log 2
      let ε := max (2 / vmin)
        (2 * vmax * (100 * (vmax + 1)) / ((9/10 : ℝ) * vmin)) *
          Real.exp (-(L ^ (3/10 : ℝ)))
      0 ≤ budget ∧ 0 < ε ∧ ∀ θ : ℝ,
      ∀ code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B),
      ‖physicalRootForestContribution groups e patterns C hC k V (1/2) ζ K θ
        (fun (g : Fin M) (p : P (e.symm g).val) =>
          ((p.val : ℝ) * physicalEndpointBaseline (1/2) (n + 1) p.val)⁻¹)
        (fun j => physicalEndpointSchedule (1/2) (n + 1) j.val) (9/10) code‖ ≤
        L ^ (budget * (((n + 1 : ℕ) : ℝ) + 1)) * ε ^ birthForestRank code := by
  obtain ⟨Ahi, hAhi, hbound⟩ := exists_physical_root_high_rank_contribution_power_le
    (qmax := (3/4 : ℝ)) (vs := vs) (by norm_num) (by norm_num) hvs ell
  refine ⟨Ahi, hAhi, ?_⟩
  intro I N M J n B P groups e _ patterns C hC k V i0 ζ K encode hinj
    L Cgroup Ccoeff Arow Hkernel T hL hCgroup hCcoeff hArow hHkernel hrowghost hrowedge
    hVs hVmin hVmax hMass hP hdis hsize hprime hT hM hcoeff hK budget ε
  let v := 100 * (vmax + 1)
  let η := (2 / vmin) * Real.exp (-(L ^ (3/10 : ℝ)))
  let β := fun (g : Fin M) (p : P (e.symm g).val) =>
    ((p.val : ℝ) * physicalEndpointBaseline (1/2) (n + 1) p.val)⁻¹
  let retention : Fin (n + 2) → ℝ :=
    fun j => physicalEndpointSchedule (1/2) (n + 1) j.val
  obtain ⟨hv, hη, hηε, hε, hμ, hmass, hret, hghost⟩ :=
    actual_root_half_parameters (fun g : Fin M => P (e.symm g).val)
      (fun g => V (e.symm g).val) (n + 1) L vmin vmax hvmin hvmax
      hVmin hVmax (fun g => hMass (e.symm g).val) hsize hprime
  have hCh : 0 ≤ (Cgroup * ((J + ell : ℕ) : ℝ)) * Real.log 2 := by positivity
  have hbudget : 0 ≤ budget := by
    dsimp only [budget]
    exact add_nonneg (add_nonneg hCcoeff
      (mul_nonneg (mul_nonneg (by norm_num) hCgroup) (Real.log_nonneg hArow))) hCh
  refine ⟨hbudget, hε, ?_⟩
  intro θ code
  have hInitial : (∏ g, (∑ p, β g p / V (e.symm g).val) ^ (J + ell)) ≤
      L ^ ((Cgroup * ((J + ell : ℕ) : ℝ)) * Real.log 2) := by
    apply root_initial_mass_polynomial (zero_lt_one.trans_le hL) (J + ell)
      (fun g => ∑ p, β g p / V (e.symm g).val)
    · intro g
      exact ⟨sum_nonneg (fun p _ => (hμ g p).1.le), hmass g⟩
    · simpa only [Fintype.card_fin] using hM
  have hcross : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (e.symm g).val) :=
    fun s g => hdis (by intro he; exact (e.symm g).property (he ▸ s.property))
  have hsqrt : Real.sqrt (1/2 : ℝ) ≤ 3/4 := by
    apply (Real.sqrt_le_iff).2
    norm_num
  exact @hbound I N M J n B P groups e inferInstance patterns C hC k V (1/2) β retention
    (9/10) hVs hsqrt i0 v vmin (fun _ => η) ε T
    (fun g => hMass (e.symm g).val) (fun g p => (hμ g p).1.le) hmass
    (fun _ => hη.le) (fun g p => (hμ g p).2)
    (fun j g => hghost j.val g) (fun _ => hηε)
    (fun j => (hret j.val).1) (fun j => (hret j.val).2.1)
    (by norm_num) (by norm_num) hv hvmin hVmin (fun j => (hret j.val).2.2.1) hT hε.le
    Hkernel hHkernel ζ K θ hK
    (fun s p hp => hP s.val p hp) (fun g p hp => hP (e.symm g).val p hp) hcross
    (fun s => hMass s.val) encode hinj L Cgroup Ccoeff
    ((Cgroup * ((J + ell : ℕ) : ℝ)) * Real.log 2) Arow vmax
    hL hCgroup hCcoeff hCh hArow hrowghost hrowedge hVmax hM hcoeff hInitial code

end Bounty

end


-- Source module: ActualRootHalfRarity
section

/- Prime size and birth-address rarity for the literal half-schedule length. -/

open Filter

namespace Bounty

theorem eventually_actual_root_half_prime_size :
    ∀ᶠ L : ℝ in atTop, ∀ p : ℕ,
      Real.exp (L ^ (3/10 : ℝ)) ≤ (p : ℝ) →
        2 * (2 * Nat.ceil (L ^ (13/25 : ℝ)) + 1) ≤ p := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_repeated_big_visit_density_le (alpha := 13/25) (tau := 1)
      zero_lt_one (by norm_num),
    eventually_mul_rpow_log_add_le_rpow (a := 0) (b := 3/10) (c := 1)
      (by norm_num) (by norm_num) zero_lt_one 1 (Real.log 2)]
    with L hL hlength hlog
  intro p hp
  have hlen : ((2 * Nat.ceil (L ^ (13/25 : ℝ)) + 1 : ℕ) : ℝ) ≤ L := by
    have ht := hlength (2 * (Nat.ceil (L ^ (13/25 : ℝ)) : ℝ) + 1) le_rfl
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      Real.rpow_one] using ht
  have hexp : 2 * L ≤ Real.exp (L ^ (3/10 : ℝ)) := by
    calc
      2 * L = Real.exp (Real.log L + Real.log 2) := by
        rw [Real.exp_add, Real.exp_log hL,
          Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by
        simpa only [Real.rpow_zero, mul_one, one_mul] using hlog)
  exact_mod_cast (mul_le_mul_of_nonneg_left hlen
    (by norm_num : (0 : ℝ) ≤ 2)).trans (hexp.trans hp)

theorem actual_root_half_length_succ {L : ℝ} (hL : 0 < L) :
    (2 * Nat.ceil (L ^ (13/25 : ℝ)) - 1) + 1 =
      2 * Nat.ceil (L ^ (13/25 : ℝ)) := by
  have hceil : 0 < Nat.ceil (L ^ (13/25 : ℝ)) :=
    Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hL _)
  omega

theorem eventually_actual_root_half_birth_rarity
    (J ell : ℕ) (Cgroup C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop,
      let n := 2 * Nat.ceil (L ^ (13/25 : ℝ)) - 1
      ∀ M : ℕ, (M : ℝ) ≤ Cgroup * Real.log L →
        (Fintype.card (FullMixedCommonBirthAddress
          (fun _ : Fin M => J + ell) (Nat.ceil L)
          ((List.range (4 * (n + 1) + 1)).map
            (physicalSelectedFineTag (n + 1)))) : ℝ) ^ 2 *
          (C * Real.exp (-(L ^ (3/10 : ℝ)))) ≤
            Real.exp (-(L ^ (1/4 : ℝ))) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_root_birth_card_linear_cap J ell Cgroup,
    eventually_root_birth_rarity_gap C] with L hL hcount hgap
  dsimp only
  rw [actual_root_half_length_succ hL]
  intro M hM
  exact hgap _ (hcount M hM) _
    (mul_nonneg hC (Real.exp_pos _).le) le_rfl

end Bounty

end


-- Source module: RootFiniteIntegerEncoding
section

/- Any finite root-label type has an injective integer encoding. -/

namespace Bounty

theorem exists_root_finite_integer_encoding (α : Type*) [Fintype α] :
    ∃ encode : α → ℤ, Function.Injective encode := by
  refine ⟨fun a => ((Fintype.equivFin α) a).val, ?_⟩
  intro a b h
  apply (Fintype.equivFin α).injective
  apply Fin.ext
  exact Int.ofNat.inj h

end Bounty

end


-- Source module: ActualRootHalfHighRank
section

/- The literal half-endpoint moment schedule supplies the high-rank
callback and the birth-dimension rarity bound for the residue estimate. -/

open Finset Filter
open scoped Classical
namespace Bounty

theorem exists_actual_root_half_high_rank_callback {vs vmin vmax : ℝ}
    (hvs : 0 < vs) (hvmin : 0 < vmin) (hvmax : 0 ≤ vmax) (ell : ℕ) :
    ∃ Ahi : ℝ, 1 ≤ Ahi ∧
    ∀ (J T : ℕ) (Cgroup Ccoeff Arow : ℝ),
      0 ≤ Cgroup → 0 ≤ Ccoeff → 1 ≤ Arow →
      Real.exp (2 * vmax * (100 * (vmax + 1)) / (9/10 : ℝ)) ≤ Arow →
      unrestrictedEdgeRowBound (9/10) (100 * (vmax + 1)) vmin T ≤ Arow →
    ∀ᶠ L : ℝ in atTop,
      let n := 2 * Nat.ceil (L ^ (13/25 : ℝ)) - 1
      let ε := max (2 / vmin)
        (2 * vmax * (100 * (vmax + 1)) / ((9/10 : ℝ) * vmin)) *
          Real.exp (-(L ^ (3/10 : ℝ)))
      let budget := Ccoeff + 4 * Cgroup * Real.log Arow +
        (Cgroup * ((J + ell : ℕ) : ℝ)) * Real.log 2
      ∀ (I : Type) (N M : ℕ) (P : Fin N → Finset ℕ)
        (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
        [∀ z : PhysicalPrime P, NeZero z.2.val]
        (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
        (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
        (k : ℕ → I → ℤ) (V : Fin N → ℝ) (_i0 : patterns)
        (ζ : ℕ → I → ℝ)
        (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
          PhysicalAuxLabels P (C i) → ℂ),
        ∀ Hkernel : ℝ, 1 ≤ Hkernel →
        (∀ s : ↥groupsᶜ, vs ≤ V s.val) →
        (∀ g : Fin M, vmin ≤ V (e.symm g).val) →
        (∀ g : Fin M, V (e.symm g).val ≤ vmax) →
        (∀ g, ∑ p ∈ P g, 1 / (p : ℝ) = V g) →
        (∀ g p, p ∈ P g → Nat.Prime p) →
        Pairwise (fun g h => Disjoint (P g) (P h)) →
        (∀ (g : Fin M) (p : P (e.symm g).val),
          Real.exp (L ^ (3/10 : ℝ)) ≤ (p.val : ℝ)) →
        (∀ (i : patterns) (g : Fin M),
          (physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val))ᶜ.card ≤ T) →
        (M : ℝ) ≤ Cgroup * Real.log L →
        (Ahi ^ groupsᶜ.card * (patterns.card : ℝ)) * Hkernel ≤ L ^ Ccoeff →
        (∀ time < n + 1, ∀ i ∈ patterns, ∀ U W aux, ‖K time i U W aux‖ ≤ Hkernel) →
        let m := Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell)
          (Nat.ceil L) ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))
        0 ≤ budget ∧ 0 < ε ∧ (m : ℝ) ≤ L ^ (6 : ℝ) ∧
          (m : ℝ) ^ 2 * ε ≤ Real.exp (-(L ^ (1/4 : ℝ))) ∧
        ∀ θ : ℝ, ∀ code : BirthForestCode m,
        ‖physicalRootForestContribution groups e patterns C hC k V (1/2) ζ K θ
          (fun (g : Fin M) (p : P (e.symm g).val) =>
            ((p.val : ℝ) * physicalEndpointBaseline (1/2) (n + 1) p.val)⁻¹)
          (fun j => physicalEndpointSchedule (1/2) (n + 1) j.val) (9/10) code‖ ≤
          L ^ (budget * (((n + 1 : ℕ) : ℝ) + 1)) * ε ^ birthForestRank code := by
  obtain ⟨Ahi, hAhi, hbound⟩ := exists_physical_root_half_high_rank_power hvs hvmin hvmax ell
  refine ⟨Ahi, hAhi, ?_⟩
  intro J T Cgroup Ccoeff Arow hCgroup hCcoeff hArow hrowghost hrowedge
  let rarity := max (2 / vmin)
    (2 * vmax * (100 * (vmax + 1)) / ((9/10 : ℝ) * vmin))
  have hrarity : 0 ≤ rarity := by
    exact le_trans (by positivity : (0 : ℝ) ≤ 2 / vmin) (le_max_left _ _)
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_actual_root_half_prime_size,
    eventually_actual_root_half_birth_rarity J ell Cgroup rarity hrarity,
    eventually_root_birth_card_linear_cap J ell Cgroup]
    with L hL hsizeL hrare hcount
  intro n ε budget I N M P groups e _ patterns C hC k V i0 ζ K
    Hkernel hHkernel hVs hVmin hVmax hMass hP hdis hprime hT hM hcoeff hK m
  have hn : n + 1 = 2 * Nat.ceil (L ^ (13/25 : ℝ)) :=
    actual_root_half_length_succ (zero_lt_one.trans_le hL)
  have hsize : ∀ (g : Fin M) (p : P (e.symm g).val), 2 * (n + 2) ≤ p.val := by
    intro g p
    have hh := hsizeL p.val (hprime g p)
    have hstep : n + 2 = 2 * Nat.ceil (L ^ (13/25 : ℝ)) + 1 := by omega
    simpa only [hstep] using hh
  obtain ⟨encode, hinj⟩ := exists_root_finite_integer_encoding
    ((g : Fin M) × P (e.symm g).val)
  have hpower := @hbound I N M J n (Nat.ceil L) P groups e inferInstance patterns C hC
    k V i0 ζ K encode hinj L Cgroup Ccoeff Arow Hkernel T
    hL hCgroup hCcoeff hArow hHkernel hrowghost hrowedge hVs hVmin hVmax hMass hP hdis
    hsize hprime hT hM hcoeff hK
  refine ⟨hpower.1, hpower.2.1, ?_, ?_, hpower.2.2⟩
  · dsimp only [m]
    rw [hn]
    exact (hcount M hM).trans_eq (Real.rpow_natCast L 6).symm
  · exact hrare M hM

end Bounty

end
