import ActualSelectedHighRank

/-! The exact challenge target, using the actual candidate residue bound. -/

open scoped Topology BigOperators Classical

-- Source module: CandidateNumberedResidueTransfer
section

/- Finite selections and exact group reindexing recover the original selected model. -/

open Finset Filter
open scoped Classical
namespace Bounty

def CandidateUniformNumberedResidueBounds (scale : ℝ) : Prop :=
  ∀ E z K : ℝ, 0 ≤ E → 0 ≤ z → 0 ≤ K →
    ∃ (m J : ℕ) (w x q : ℝ), m ≤ J ∧ 0 ≤ w ∧ 0 ≤ x ∧ 0 ≤ q ∧
    ∀ᶠ L : ℝ in atTop,
      ∀ {N : ℕ} (index : Fin N ≃ ↥(candidatePIndices scale L)),
      let P := candidateRootPools scale L index
      let V := fun g => ∑ p ∈ P g, 1/(p : ℝ)
      ∀ (probes : Fin N → Finset (Fin J)), (∀ g, (probes g).card = m) →
      ∀ r t : Finset (Fin N), ∀ hrt : Disjoint r t,
      r ⊆ candidateRootBigGroups scale L index → t ⊆ candidateRootBigGroups scale L index →
      (1/(80*Real.log 2))*Real.log L ≤ (r.card : ℝ) →
      (1/(80*Real.log 2))*Real.log L ≤ (t.card : ℝ) →
      ∀ [∀ p : PhysicalPrime P, NeZero p.2.val],
      ∀ ζ : ℝ, |ζ| ≤ L^z →
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L K : ℤ))
        (typeIIAdmissibleDeterminantBound L K : ℤ), k ≠ 0 →
      let Q := ⌊L^q⌋₊
      let patterns := (univ : Finset (RepeatedBigPrimePatternIndex (ell := 1) probes r t))
      let cuts := repeatedBigPrimePatternCut (ell := 1) probes r t
      let ζt := fun time (_ : RepeatedBigPrimePatternIndex (ell := 1) probes r t) =>
        if time%2=0 then -ζ else ζ
      let kt := fun time (_ : RepeatedBigPrimePatternIndex (ell := 1) probes r t) =>
        if time%2=0 then -k else k
      let Kt := fun time a u v aux => if time%2=0 then
        (starRingEnd ℂ) (physicalRootPrimeKernel P V probes r t hrt Q (L^(-w)) (L^(-x)) a v u aux)
        else physicalRootPrimeKernel P V probes r t hrt Q (L^(-w)) (L^(-x)) a u v aux
      ‖physicalRootResidueModel V patterns cuts (1/2) ζt kt Kt
        (2*Nat.ceil (L^(13/25 : ℝ))-1)‖ ≤
        2*L^(-(E+1)*(2*Nat.ceil (L^(13/25 : ℝ)) : ℕ))

theorem candidate_selected_residue_bounds_of_uniform_numbered {scale : ℝ}
    (hscale : 0 < scale) (h : CandidateUniformNumberedResidueBounds scale) :
    CandidateSelectedResidueBounds scale := by
  intro E z K hE hz hK
  obtain ⟨m,J,w,x,q,hmJ,hw,hx,hq,hnum⟩ := h E z K hE hz hK
  refine ⟨J,w,x,q,hw,hx,hq,?_⟩
  filter_upwards [hnum,eventually_candidate_disjoint_big_selections hscale,
    eventually_ge_atTop (1 : ℝ)] with L hnum hselect hL
  intro S P V
  obtain ⟨r,t,hrt,hbig,hr,ht⟩ := hselect
  obtain ⟨probes,hprobes,_⟩ := exists_uniform_card_probes S hmJ
  let Q := ⌊L^q⌋₊
  refine ⟨probes,r,t,hrt,Q,hbig,Nat.floor_le (Real.rpow_nonneg (by linarith) _),?_⟩
  intro inst ζ hζ k hk hk0
  let e : S ≃ Fin S.card := Fintype.equivFinOfCardEq (Fintype.card_coe S)
  let : ∀ p : PhysicalPrime (candidateRootPools scale L e.symm), NeZero p.2.val :=
    fun p => inst ⟨e.symm p.1,p.2⟩
  have hrbig : r.map e.toEmbedding ⊆ candidateRootBigGroups scale L e.symm := by
    intro g hg
    obtain ⟨i,hi,rfl⟩ := mem_map.mp hg
    apply (candidate_root_big_groups_mem scale L e.symm _).mpr
    simpa only [Equiv.toEmbedding_apply, Equiv.symm_apply_apply] using hbig i (mem_union_left _ hi)
  have htbig : t.map e.toEmbedding ⊆ candidateRootBigGroups scale L e.symm := by
    intro g hg
    obtain ⟨i,hi,rfl⟩ := mem_map.mp hg
    apply (candidate_root_big_groups_mem scale L e.symm _).mpr
    simpa only [Equiv.toEmbedding_apply, Equiv.symm_apply_apply] using hbig i (mem_union_right _ hi)
  have hn := hnum e.symm (fun g => probes (e.symm g)) (fun g => hprobes _)
    (r.map e.toEmbedding) (t.map e.toEmbedding) ((disjoint_map e.toEmbedding).mpr hrt)
    hrbig htbig (by simpa only [card_map] using hr) (by simpa only [card_map] using ht)
    ζ hζ k hk hk0
  have heq := physical_root_prime_residue_model_finset_reindex S P J 1 V probes r t hrt Q
    (L^(-w)) (L^(-x)) (1/2) (fun time => if time%2=0 then -ζ else ζ)
    (fun time => if time%2=0 then -k else k) (2*Nat.ceil (L^(13/25 : ℝ))-1)
  dsimp only at heq
  exact (congrArg (fun z : ℂ => ‖z‖) heq).le.trans hn

end Bounty

end


-- Source module: CandidateOriginalSchedules
section

/- Original determinant and alternating schedules at the selected moment length. -/

open Filter Finset
namespace Bounty

theorem original_determinant_natAbs_le {L K : ℝ} (hL : 3 ≤ L) (hK : 0 ≤ K)
    {k : ℤ} (hk : k ∈ Icc (-(typeIIAdmissibleDeterminantBound L K : ℤ))
      (typeIIAdmissibleDeterminantBound L K : ℤ)) :
    (k.natAbs : ℝ) ≤ L ^ (K+89) := by
  have hL0 : 0 < L := by linarith
  have hkabs : |k| ≤ (typeIIAdmissibleDeterminantBound L K : ℤ) := abs_le.mpr (mem_Icc.mp hk)
  have hknat : k.natAbs ≤ typeIIAdmissibleDeterminantBound L K := by
    rw [← Int.natCast_natAbs] at hkabs
    exact_mod_cast hkabs
  calc
    _ ≤ (typeIIAdmissibleDeterminantBound L K : ℝ) := by exact_mod_cast hknat
    _ ≤ 3 * L^(K+88) := determinant_bound_le_three_rpow_public (by linarith) hK
    _ ≤ L * L^(K+88) := mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hL0.le _)
    _ = L^(K+89) := by rw [mul_comm, ← Real.rpow_add_one hL0.ne']; congr 1; ring

theorem original_alternating_schedule_bounds {L K z ζ : ℝ}
    (hL : 3 ≤ L) (hK : 0 ≤ K) (hζ : |ζ| ≤ L^z)
    {k : ℤ} (hk : k ∈ Icc (-(typeIIAdmissibleDeterminantBound L K : ℤ))
      (typeIIAdmissibleDeterminantBound L K : ℤ)) (hk0 : k ≠ 0) (time : ℕ) :
    |if time%2=0 then -ζ else ζ| ≤ L^z ∧
      (if time%2=0 then -k else k) ≠ 0 ∧
      ((if time%2=0 then -k else k).natAbs : ℝ) ≤ L^(K+89) := by
  have hkn := original_determinant_natAbs_le hL hK hk
  split_ifs <;> simpa only [abs_neg, neg_ne_zero, Int.natAbs_neg] using And.intro hζ (And.intro hk0 hkn)

theorem eventually_original_root_length_data :
    ∀ᶠ L : ℝ in atTop,
      let n := 2*Nat.ceil (L^(13/25 : ℝ))-1
      n+1 = 2*Nat.ceil (L^(13/25 : ℝ)) ∧
      L^(1/2 : ℝ) ≤ ((n+1 : ℕ) : ℝ) ∧
      ((n+2 : ℕ) : ℝ) ≤ L ∧
      0 ≤ ∑ j ∈ range (n+2), (1-physicalEndpointSchedule (1/2) (n+1) j) ∧
      (∑ j ∈ range (n+2), (1-physicalEndpointSchedule (1/2) (n+1) j)) ≤ L ∧
      L ≤ (Nat.ceil L : ℝ) ∧ Nat.ceil L ≤ Nat.ceil (L^2) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_repeated_big_visit_density_le (alpha := 13/25) (tau := 1)
      zero_lt_one (by norm_num)] with L hL hlength
  intro n
  have hpow : 1 ≤ L^(13/25 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hceil : 1 ≤ Nat.ceil (L^(13/25 : ℝ)) := by
    exact_mod_cast hpow.trans (Nat.le_ceil _)
  have hn : n+1 = 2*Nat.ceil (L^(13/25 : ℝ)) := by dsimp [n]; omega
  have hn2 : ((n+2 : ℕ) : ℝ) ≤ L := by
    have hh := hlength (2*(Nat.ceil (L^(13/25 : ℝ)) : ℝ)+1) le_rfl
    rw [show n+2 = 2*Nat.ceil (L^(13/25 : ℝ))+1 by omega]
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Real.rpow_one] using hh
  refine ⟨hn, ?_, hn2, ?_, ?_, Nat.le_ceil _, ?_⟩
  · calc
      _ ≤ L^(13/25 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
      _ ≤ (Nat.ceil (L^(13/25 : ℝ)) : ℝ) := Nat.le_ceil _
      _ ≤ ((n+1 : ℕ) : ℝ) := by rw [hn]; push_cast; nlinarith [show (0 : ℝ) ≤ (Nat.ceil (L^(13/25 : ℝ)) : ℝ) from Nat.cast_nonneg _]
  · exact physical_endpoint_damping_sum_nonneg (by norm_num) (by norm_num) (n+1)
  · exact (physical_endpoint_damping_sum_le (by norm_num) (by norm_num) (n+1)).trans
      (by push_cast at hn2 ⊢; linarith)
  · exact Nat.ceil_mono (by nlinarith)

end Bounty

end


-- Source module: CandidateNumberedBaseline
section

/- The literal endpoint baseline meets the scalar model's positive-mass hypotheses. -/

open Filter Finset
namespace Bounty

theorem eventually_candidate_numbered_baseline_data {scale vmin vmax : ℝ}
    (hvmin : 0 < vmin) :
    ∀ᶠ L : ℝ in atTop,
      ∀ {N M : ℕ} (index : Fin N ≃ ↥(candidatePIndices scale L))
        (reindex : {g // g ∉ (candidateRootBigGroups scale L index)ᶜ} ≃ Fin M),
      let P := candidateRootPools scale L index
      let groups := candidateRootBigGroups scale L index
      CandidateNumberedPoolBounds scale L vmin vmax P groups reindex →
      let n := 2*Nat.ceil (L^(13/25 : ℝ))-1
      let V := fun i => ∑ p ∈ P i, 1/(p : ℝ)
      let beta := fun (g : Fin M) (p : P (reindex.symm g).val) =>
        ((p.val : ℝ)*physicalEndpointBaseline (1/2) (n+1) p.val)⁻¹ / V (reindex.symm g).val
      (∀ (g : Fin M) (p : P (reindex.symm g).val), 2*(n+2) ≤ p.val) ∧
      (∀ (g : Fin M) (p : P (reindex.symm g).val),
        1/2 ≤ physicalEndpointBaseline (1/2) (n+1) p.val ∧
          physicalEndpointBaseline (1/2) (n+1) p.val ≤ 1) ∧
      (∀ g p, 0 < beta g p) ∧ (∀ g, (∑ p, beta g p) ≤ 2) ∧
      ∀ J : ℕ, (∏ g, (∑ p, beta g p)^(J+1)) ≤ (2 : ℝ)^((J+1)*M) := by
  filter_upwards [eventually_original_root_length_data,
    eventually_mul_rpow_le_exp_rpow 1 2 (c := (1/4 : ℝ)) (by norm_num)] with L hlen hexp
  intro N M index reindex P groups hd n V beta
  have hsize : ∀ (g : Fin M) (p : P (reindex.symm g).val), 2*(n+2) ≤ p.val := by
    intro g p
    have hlow := hd.big_lower g p.val p.property
    have hn : ((n+2 : ℕ) : ℝ) ≤ L := hlen.2.2.1
    simp only [Real.rpow_one] at hexp
    have hh : (2 : ℝ)*((n+2 : ℕ) : ℝ) ≤ (p.val : ℝ) := by linarith
    exact_mod_cast hh
  have hbase : ∀ (g : Fin M) (p : P (reindex.symm g).val),
      1/2 ≤ physicalEndpointBaseline (1/2) (n+1) p.val ∧
        physicalEndpointBaseline (1/2) (n+1) p.val ≤ 1 := by
    intro g p
    exact physical_endpoint_baseline_bounds (by norm_num) (by norm_num) (n+1) p.val
      (hd.prime _ p.val p.property).pos (by simpa only [Nat.add_assoc] using hsize g p)
  have hpos : ∀ g p, 0 < beta g p := by
    intro g p
    exact physical_endpoint_beta_pos (P := fun g : Fin M => P (reindex.symm g).val) (fun g : Fin M => V (reindex.symm g).val)
      (1/2) (n+1) (by norm_num) (by norm_num) g
      (hvmin.trans_le (hd.mass_lower _)) p (hd.prime _ p.val p.property).pos (by simpa only [Nat.add_assoc] using hsize g p)
  have hmass : ∀ g, (∑ p, beta g p) ≤ 2 := by
    intro g
    exact (physical_endpoint_beta_mass_bounds (P := fun g : Fin M => P (reindex.symm g).val) (fun g : Fin M => V (reindex.symm g).val)
      (1/2) (n+1) (by norm_num) (by norm_num) g
      (hvmin.trans_le (hd.mass_lower _)) rfl
      (fun p => (hd.prime _ p.val p.property).pos) (by simpa only [Nat.add_assoc] using hsize g)).2
  refine ⟨hsize,hbase,hpos,hmass,?_⟩
  intro J
  calc
    _ ≤ ∏ _g : Fin M, (2 : ℝ)^(J+1) := by
      apply Finset.prod_le_prod₀
      · intro g _
        exact pow_nonneg (sum_nonneg (fun p _ => (hpos g p).le)) _
      · intro g _
        exact pow_le_pow_left₀ (sum_nonneg (fun p _ => (hpos g p).le)) (hmass g) _
    _ = _ := by simp only [prod_const, card_univ, Fintype.card_fin, ← pow_mul]

theorem eventually_candidate_numbered_group_card {scale : ℝ} (hscale : 0 < scale) :
    ∀ᶠ L : ℝ in atTop, ∀ {N : ℕ} (_index : Fin N ≃ ↥(candidatePIndices scale L)),
      (N : ℝ) ≤ (2/(5*Real.log 2))*Real.log L ∧
      ∀ groups : Finset (Fin N),
        (Fintype.card ↥groupsᶜ : ℝ) ≤ (2/(5*Real.log 2))*Real.log L := by
  obtain ⟨v,V,_,_,hp⟩ := exists_candidate_P_pool_bounds hscale
  filter_upwards [hp] with L hp
  intro N index
  have hcard : N = (candidatePIndices scale L).card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_congr index
  have hn : (N : ℝ) ≤ (2/(5*Real.log 2))*Real.log L := by
    rw [hcard]
    exact hp.2.2.2.1
  refine ⟨hn,?_⟩
  intro groups
  apply le_trans _ hn
  have hh : Fintype.card ↥groupsᶜ ≤ N := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using card_le_univ groupsᶜ
  exact_mod_cast hh

end Bounty

end


-- Source module: CandidateNumberedPrimeData
section

/- Strong big-prime size and all-pool determinant avoidance after numbering. -/

open Finset Filter
namespace Bounty

theorem eventually_candidate_numbered_prime_data {scale K : ℝ}
    (hscale : 0 < scale) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop,
      ∀ {N M : ℕ} (index : Fin N ≃ ↥(candidatePIndices scale L))
        (reindex : {g // g ∉ (candidateRootBigGroups scale L index)ᶜ} ≃ Fin M),
      let P := candidateRootPools scale L index
      (∀ (g : Fin M) (p : P (reindex.symm g).val),
        Real.exp (L^(3/10 : ℝ)) ≤ (p.val : ℝ)) ∧
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L K : ℤ))
        (typeIIAdmissibleDeterminantBound L K : ℤ), k ≠ 0 →
      ∀ time (g : Fin N) p, p ∈ P g → ¬ (p : ℤ) ∣ (if time%2=0 then -k else k) := by
  obtain ⟨_,_,_,_,hbig⟩ := eventually_candidate_P_groups
    (α := (3/10 : ℝ)) (β := (2/5 : ℝ)) hscale (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [hbig,eventually_candidate_root_prime_avoidance hscale hK] with L hb hk
  intro N M index reindex P
  refine ⟨?_,?_⟩
  · intro g p
    have hg : (index (reindex.symm g).val).val ∈ candidateBigPIndices scale L := by
      apply (candidate_root_big_groups_mem scale L index _).mp
      simpa only [mem_compl, not_not] using (reindex.symm g).property
    exact ((hb.2.2.2 _ hg).2.2 p.val p.property).2.1.le
  · intro k hmem hk0 time g p hp
    have hh := hk (index g).val (index g).property p hp k hmem hk0
    split_ifs <;> simpa only [dvd_neg] using hh

end Bounty

end


-- Source module: CandidateRootFullEnvelope
section

/- A common polynomial bound for the full pattern count and every signed kernel. -/

open Finset
open scoped Classical
namespace Bounty

theorem candidate_root_full_kernel_envelope
    {L a q x : ℝ} (hL : 2 ≤ L) (ha : 0 ≤ a) (hq : 0 ≤ q) (hx : 0 ≤ x)
    {N J ell : ℕ} (hN : (N : ℝ) ≤ a*Real.log L)
    (P : Fin N → Finset ℕ) (V : Fin N → ℝ)
    (probes : Fin N → Finset (Fin J)) (r t : Finset (Fin N)) (hrt : Disjoint r t)
    (Q : ℕ) (hQ : (Q : ℝ) ≤ L^q) (h : ℝ) :
    let C := (J : ℝ)*a*Real.log 2+4*q+2*x+1
    let H := repeatedBigFamilyEnvelope N J Q (L^(-x))
    0 ≤ C ∧ 1 ≤ H ∧ H ≤ L^C ∧
      ∀ time (i : RepeatedBigPrimePatternIndex (ell := ell) probes r t) U W aux,
        ‖if time%2=0 then
          (starRingEnd ℂ) (physicalRootPrimeKernel P V probes r t hrt Q h (L^(-x)) i W U aux)
          else physicalRootPrimeKernel P V probes r t hrt Q h (L^(-x)) i U W aux‖ ≤ H := by
  intro C H
  have hL0 : 0 < L := by linarith
  have henv (Q' : ℕ) (ξ : ℝ) (hQ' : (Q' : ℝ) ≤ L^q) (hξ : L^(-x) ≤ ξ) :
      repeatedBigFamilyEnvelope N J Q' ξ ≤ L^C := by
    calc
      _ ≤ 2*L^((J : ℝ)*a*Real.log 2+4*q+2*x) :=
        repeated_big_family_envelope_le N J Q' (by linarith) ha hq hx hN hQ' hξ
      _ ≤ L*L^((J : ℝ)*a*Real.log 2+4*q+2*x) :=
        mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hL0.le _)
      _ = L^C := by rw [mul_comm, ← Real.rpow_add_one hL0.ne']
  refine ⟨by dsimp [C]; positivity, repeated_big_family_envelope_ge_one N J Q _,
    henv Q _ hQ le_rfl, ?_⟩
  intro time i U W aux
  simpa only [Fintype.card_fin] using physical_root_alternating_prime_kernel_norm_le_family
    P V probes r t hrt Q h (L^(-x)) (Real.rpow_pos_of_pos hL0 _) time i U W aux

end Bounty

end


-- Source module: CandidateActualResidue
section

/- The actual candidate prime pool satisfies the selected original residue estimate. -/

open Filter Finset
open scoped Classical
namespace Bounty

theorem candidate_uniform_numbered_residue_bounds {scale : ℝ} (hscale : 0 < scale) :
    CandidateUniformNumberedResidueBounds scale := by
  intro Et z K hEt hz hK
  obtain ⟨vmin,vmax,hvmin,hvmax,hpool,horder⟩ :=
    exists_candidate_numbered_edge_parameter_order hscale
  obtain ⟨A,Cbad,hA,hCbad,horder⟩ := horder (K+89)
  obtain ⟨hG,hgain,E,m,D,hE,hm,hD,hgap,hDgap,hq,hw,hx,hC,hCa,hCv,hJ⟩ :=
    horder Et z 1 hEt hz zero_le_one
  let a : ℝ := 2/(5*Real.log 2)
  let u := 100*(vmax+1)
  let Kghost := physicalGhostUniformEnergyBound (9/10) vmax u
  let Cv := max 0 (candidateMixedRareCostExponent 1 Kghost)
  let G := Et+1+Cv+2
  let κ := a*Real.log (primeFiberFactorBound vmin m)
  let A₀ := D+2*((1/2 : ℝ)+1/2+1)
  let q := 2*κ+((1/2 : ℝ)+1/2+1)+2*A₀+3
  let w := 4*q+max z q+A₀+2
  let x := ((1/2 : ℝ)+1/2+w+2)+2*A₀+2
  let C := (m : ℝ)*a*Real.log 2+4*q+2*x+1
  let Kedge := unrestrictedEdgeEnergyBound (9/10) u vmin vmax (1+m)
  let Ca := max 0 (C+candidateMixedRareCostExponent Cbad Kedge)
  have hG0 : 0 ≤ G := hG
  have hCa0 : 0 ≤ Ca := hCa
  have hGC0 : 0 ≤ G+Ca := add_nonneg hG0 hCa0
  obtain ⟨J,hJ,hCh,hbudget⟩ := hJ 0
  let Ch := max 0 (candidateMixedRareCostExponent 1 ((2 : ℝ)^(2*(J+1))))
  have hmJ : m ≤ J := (le_max_left _ _).trans hJ
  obtain ⟨Ahi,hAhi,hhigh⟩ := exists_actual_root_half_high_rank_callback hvmin hvmin hvmax.le 1
  let PG := (m : ℝ)*a*Real.log 2+1
  let HG := (J : ℝ)*a*Real.log 2+4*q+2*x+1
  let Ccoeff := a*Real.log Ahi+PG+HG
  let Arow := max 1 (max (Real.exp (2*vmax*u/(9/10 : ℝ)))
    (unrestrictedEdgeRowBound (9/10) u vmin (1+m)))
  let budget := Ccoeff+4*a*Real.log Arow+(a*((J+1 : ℕ) : ℝ))*Real.log 2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hPG : 0 ≤ PG := by dsimp [PG]; positivity
  have hHG : 0 ≤ HG := by dsimp [HG]; positivity
  have hCcoeff : 0 ≤ Ccoeff := by
    exact add_nonneg (add_nonneg (mul_nonneg ha (Real.log_nonneg hAhi)) hPG) hHG
  have hArow : 1 ≤ Arow := le_max_left _ _
  have hrowghost : Real.exp (2*vmax*u/(9/10 : ℝ)) ≤ Arow :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hrowedge : unrestrictedEdgeRowBound (9/10) u vmin (1+m) ≤ Arow :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hb : 0 ≤ budget := by
    exact add_nonneg (add_nonneg hCcoeff
      (mul_nonneg (mul_nonneg (by norm_num) ha) (Real.log_nonneg hArow)))
      (mul_nonneg (mul_nonneg ha (Nat.cast_nonneg _)) (by positivity))
  have hu : 1 < u := by dsimp [u]; linarith
  have hmodel := eventually_physical_root_residue_of_edge_costs_and_cap
    (budget := budget) (E := Et) (G := G) (Cv := Cv) (Ca := Ca) (Ch := Ch)
    (q := (1/2 : ℝ)) (vs := vmin) (ρ := (9/10 : ℝ)) (v := u)
    (vmin := vmin) (vmax := vmax) (CG := a) (PG := PG) (HG := HG)
    hb hEt (add_nonneg hGC0 (by norm_num)) hgain (by norm_num) (by norm_num) hvmin
    (by norm_num) (by norm_num) hu hvmin ha hPG hHG J 1 (1+m)
  refine ⟨m,J,w,x,q,hmJ,hw,hx,hq,?_⟩
  filter_upwards [hbudget,hpool,hmodel,
    hhigh J (1+m) a Ccoeff Arow ha hCcoeff hArow hrowghost hrowedge,
    eventually_original_root_length_data,
    eventually_candidate_numbered_baseline_data (scale := scale) (vmax := vmax) hvmin,
    eventually_candidate_numbered_group_card hscale,
    eventually_candidate_numbered_prime_data hscale hK,
    eventually_ge_atTop (3 : ℝ)] with L hbudget hpool hmodel hhigh hlength hbase hcount hprime hL
  intro N index P V probes hprobes rN tN hrtN hrN htN hrsize htsize inst ζ hζ k hk hk0
  let groups := candidateRootBigGroups scale L index
  let M := groups.card
  let reindex : {g // g ∉ groupsᶜ} ≃ Fin M :=
    Fintype.equivFinOfCardEq (by simp only [mem_compl, not_not, Fintype.card_coe, M])
  have hd := hpool index reindex
  obtain ⟨r,t,hr,ht,hrcard,htcard,hrt⟩ :=
    physical_reindexed_big_subsets_pullback groups reindex rN tN hrN htN hrtN
  subst rN
  subst tN
  let f := physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex
  let I := RepeatedBigPrimePatternIndex (ell := 1) probes (r.map f) (t.map f)
  let patterns : Finset I := univ
  let cuts := repeatedBigPrimePatternCut (ell := 1) probes (r.map f) (t.map f)
  have hcut : ∀ i : patterns, ∀ s : ↥groupsᶜ, cuts i.val s.val = ∅ :=
    fun i s => physical_root_prime_full_pattern_small_cut groups reindex probes r t i.val s
  let n := 2*Nat.ceil (L^(13/25 : ℝ))-1
  let Q := ⌊L^q⌋₊
  let ζt := fun time => if time%2=0 then -ζ else ζ
  let kt := fun time => if time%2=0 then -k else k
  let ζroot := fun time (_ : I) => ζt time
  let kroot := fun time (_ : I) => kt time
  let Kt := fun time (i : I) (U W : PhysicalMarkLists P J 1) (aux : PhysicalAuxLabels P (cuts i)) =>
    if time%2=0 then
      (starRingEnd ℂ) (physicalRootPrimeKernel P V probes (r.map f) (t.map f)
        ((disjoint_map f).mpr hrt) Q (L^(-w)) (L^(-x)) i W U aux)
      else physicalRootPrimeKernel P V probes (r.map f) (t.map f)
        ((disjoint_map f).mpr hrt) Q (L^(-w)) (L^(-x)) i U W aux
  let baseline := fun p : PhysicalPrime P => physicalEndpointBaseline (1/2) (n+1) p.2.val
  let b := Nat.ceil L
  let B := max (physicalPrimeGroups P groups).card b
  let Hkernel := repeatedBigFamilyEnvelope N J Q (L^(-x))
  let eps := max (2/vmin) (2*vmax*u/((9/10 : ℝ)*vmin))*Real.exp (-(L^(3/10 : ℝ)))
  let Afore := L^(budget*(((n+1 : ℕ) : ℝ)+1))
  let Hinitial := (2 : ℝ)^((J+1)*M)
  let F := repeatedBigFamilyEnvelope M m Q (L^(-x))
  let decay := A^groupsᶜ.card*(L^(-E)+2*F*Real.sqrt ((b : ℝ)/(((J+1).choose 1)^groupsᶜ.card : ℕ))*Real.sqrt (Kedge^M))
  let excess := max decay (F*Cbad^groupsᶜ.card*Real.sqrt (Kedge^M))
  have hL0 : 0 < L := by linarith
  have hL2 : 2 ≤ L := by linarith
  have hn : n+1 = 2*Nat.ceil (L^(13/25 : ℝ)) := hlength.1
  have hv : ∀ g, 0 < V g := fun g => hvmin.trans_le (hd.mass_lower g)
  have hMass : ∀ g, ∑ p ∈ P g, 1/(p : ℝ) = V g := fun _ => rfl
  have hN : (N : ℝ) ≤ a*Real.log L := (hcount index).1
  have hsmall : (Fintype.card ↥groupsᶜ : ℝ) ≤ a*Real.log L := (hcount index).2 groups
  have hQ : (Q : ℝ) ≤ L^q := Nat.floor_le (Real.rpow_nonneg hL0.le _)
  have hkernel := candidate_root_full_kernel_envelope (ell := 1) hL2 ha hq hx hN P V probes
    (r.map f) (t.map f) ((disjoint_map f).mpr hrt) Q hQ (L^(-w))
  have hHkernel : 1 ≤ Hkernel := hkernel.2.1
  have hHkernelPow : Hkernel ≤ L^HG := hkernel.2.2.1
  have hKbound : ∀ time < n+1, ∀ i ∈ patterns, ∀ U W aux, ‖Kt time i U W aux‖ ≤ Hkernel :=
    fun time _ i _ U W aux => hkernel.2.2.2 time i U W aux
  have hpatterns : (Fintype.card ↥patterns : ℝ) ≤ L^PG := by
    simpa only [patterns, Fintype.card_coe, card_univ] using repeated_big_prime_pattern_card_power
      (ell := 1) probes (r.map f) (t.map f) ((disjoint_map f).mpr hrt)
      (fun g => (hprobes g).le) hL2 ha (by simpa only [Fintype.card_fin] using hN)
  have hcoeff : (Ahi^groupsᶜ.card*(patterns.card : ℝ))*Hkernel ≤ L^Ccoeff := by
    simpa only [patterns, card_univ, Fintype.card_coe] using root_prime_high_rank_coefficient_power
      (ell := 1) probes (r.map f) (t.map f) ((disjoint_map f).mpr hrt)
      (fun g => (hprobes g).le) groupsᶜ.card hL2 ha hAhi (zero_le_one.trans hHkernel)
      (by simpa only [Fintype.card_fin] using hN)
      (by simpa only [Fintype.card_coe] using hsmall) hHkernelPow
  have hT : ∀ (i : patterns) (g : Fin M),
      (physicalFullSharedIndices (ell := 1) (cuts i.val (reindex.symm g).val))ᶜ.card ≤ 1+m := by
    intro i g
    rw [physical_full_unshared_indices_card]
    exact Nat.add_le_add_left (repeated_big_prime_pattern_cut_card_le probes (r.map f) (t.map f)
      (fun g => (hprobes g).le) i.val (reindex.symm g).val) 1
  have hrare := hhigh I N M P groups reindex patterns cuts hcut kroot V
    ⟨Sum.inl (), mem_univ _⟩ ζroot Kt Hkernel hHkernel
    (fun s => hd.mass_lower s.val) (fun g => hd.mass_lower _) (fun g => hd.mass_upper _)
    hMass hd.prime hd.disjoint (hprime index reindex).1 hT hd.big_card_le hcoeff hKbound
  have hbas := hbase index reindex hd
  let : ∀ g (p : P (reindex.symm g).val), NeZero p.val :=
    fun g p => inst ⟨(reindex.symm g).val,p⟩
  let : ∀ z : PhysicalPrime (fun s : ↥groupsᶜ => P s.val), NeZero z.2.val :=
    fun z => inst ⟨z.1.val,z.2⟩
  let hPs := fun (s : ↥groupsᶜ) p hp => hd.prime s.val p hp
  let hPb := fun (g : Fin M) p hp => hd.prime (reindex.symm g).val p hp
  have hcross : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (reindex.symm g).val) :=
    fun s g => hd.disjoint (by intro he; exact (reindex.symm g).property (he ▸ s.property))
  obtain ⟨encode,hinj⟩ := exists_root_finite_integer_encoding ((g : Fin M) × P (reindex.symm g).val)
  have hcost := hbudget.1 (N := N) (M := M) (n := n) (B := b) index reindex hPs hPb hcross
    probes (fun g => hprobes _) r t hrt
    (by simpa only [card_map] using hrsize) (by simpa only [card_map] using htsize)
    ζt kt
  have hsmallcard : groupsᶜ.card = (candidateSmallPIndices scale L).card := hd.small_card
  have hnum := hbudget.2.2.2 b hlength.2.2.2.2.2.2
  have hdecay : decay ≤ L^(-G) := by
    simpa only [decay,F,Kedge,b,hsmallcard,hd.big_card] using hnum.1
  have hexcess : excess ≤ L^Ca := by
    simpa only [excess,decay,F,Kedge,b,hsmallcard,hd.big_card] using hnum.2.1
  have hvisit : Real.sqrt (Kghost^M) ≤ L^Cv := by simpa only [hd.big_card] using hnum.2.2.1
  have hinitial : Hinitial ≤ L^Ch := by simpa only [Hinitial,hd.big_card] using hnum.2.2.2
  have hghost := physical_endpoint_half_low_rank_ghost_budgets hvmax.le (n+1)
  have hghost2 := physical_endpoint_half_ghost_budgets hvmax.le (n+1)
  have hresult := hmodel I N M b B P groups reindex V patterns cuts hcut ζroot kroot Kt hv hd.prime hd.disjoint
    (fun time _ i _ g p hp => (hprime index reindex).2 k hk hk0 time g p hp)
    baseline (fun p _ => rfl) (le_max_left _ _) encode hinj
    (fun p hp => by
      have hg : p.1 ∉ groupsᶜ := by simpa only [mem_compl, not_not] using hp
      have hh := hbas.1 (reindex ⟨p.1,hg⟩)
      change ∀ p' : P (reindex.symm (reindex ⟨p.1,hg⟩)).val, 2*(n+2) ≤ p'.val at hh
      rw [reindex.symm_apply_apply] at hh
      exact hh p.2)
    hlength.2.1 hrare.2.2.1 Hinitial Afore eps
    (by positivity) hinitial (Real.rpow_nonneg hL0.le _) le_rfl hrare.2.1.le hrare.2.2.2.1
    decay excess hbas.2.2.1 hbas.2.2.2.1 (fun g => hd.mass_upper _)
    (fun _ => rfl)
    (fun j => (physical_endpoint_schedule_unit (by norm_num) (by norm_num) (n+1) j.val).1)
    (fun j => (physical_endpoint_schedule_unit (by norm_num) (by norm_num) (n+1) j.val).2)
    (fun j => (hghost.2 j.val).1)
    (fun j g => (hghost.2 j.val).2 _ (hv _).le (hd.mass_upper _))
    hGC0 hdecay hexcess hvisit (hbas.2.2.2.2 J)
    (fun θ _ code ν j F hF => physical_root_projected_prime_edge_memory_symmetric
      groups reindex V probes r t hrt Q (L^(-w)) (L^(-x)) ζt kt θ
      (fun g p => baseline ⟨(reindex.symm g).val,p⟩) (9/10) hPs hPb hcross
      (1/2) (fun j => physicalEndpointSchedule (1/2) (n+1) j.val) code encode ν j F hF)
    (fun θ _ code ν j F hF => (hcost θ
      (fun j => (original_alternating_schedule_bounds hL hK hζ hk hk0 (n-j.val)).1)
      (fun j => (original_alternating_schedule_bounds hL hK hζ hk hk0 (n-j.val)).2.1)
      (fun j => (original_alternating_schedule_bounds hL hK hζ hk hk0 (n-j.val)).2.2)
      (fun g p => baseline ⟨(reindex.symm g).val,p⟩)
      (∑ j ∈ range (n+2), (1-physicalEndpointSchedule (1/2) (n+1) j))
      hlength.2.2.2.1 (by simpa only [Real.rpow_one] using hlength.2.2.2.2.1)
      (fun _ _ => rfl) hbas.2.1
      (fun j => physicalEndpointSchedule (1/2) (n+1) j.val) code encode ν).2.2 j F hF)
    (fun θ _ code _ => hrare.2.2.2.2 θ code)
    hlength.2.2.2.2.2.1 (le_max_right _ _) hsmall hd.big_card_le hpatterns
    (fun s => hd.mass_lower s.val) hMass (fun g => hd.mass_lower _)
    (fun j g => (hghost2.2 j.val).2 _ (hv _).le (hd.mass_upper _)) hT Hkernel hHkernel hHkernelPow hKbound
  have hn' : 2*Nat.ceil (L^(13/25 : ℝ))-1+1 = 2*Nat.ceil (L^(13/25 : ℝ)) := hn
  simpa only [hn',neg_mul] using hresult

theorem candidate_selected_residue_bounds {scale : ℝ} (hscale : 0 < scale) :
    CandidateSelectedResidueBounds scale :=
  candidate_selected_residue_bounds_of_uniform_numbered hscale
    (candidate_uniform_numbered_residue_bounds hscale)

end Bounty

end


namespace Bounty

theorem target : fcTypeOfName% "Erdos1057.erdos_1057" := by
  apply WeakZeroFree.target_of_selected_residue_bounds
  intro c hc
  exact candidate_selected_residue_bounds hc

end Bounty
