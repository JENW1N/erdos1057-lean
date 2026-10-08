import ActualSelectedResidueCore

/-! Actual numbered candidate input estimates in the common residue environment. -/

open scoped Topology BigOperators Classical

-- Source module: CandidateNumberedPoolBounds
section

/- Uniform candidate-pool facts after an arbitrary finite enumeration. -/

open Filter Finset
open scoped Classical
namespace Bounty

structure CandidateNumberedPoolBounds (scale L vmin vmax : ℝ) {N M : ℕ}
    (P : Fin N → Finset ℕ) (groups : Finset (Fin N))
    (reindex : {g // g ∉ groupsᶜ} ≃ Fin M) : Prop where
  one_le : 1 ≤ L
  small_card : groupsᶜ.card = (candidateSmallPIndices scale L).card
  big_card : M = (candidateBigPIndices scale L).card
  disjoint : Pairwise (fun i j => Disjoint (P i) (P j))
  mass_lower : ∀ i, vmin ≤ ∑ p ∈ P i, 1 / (p : ℝ)
  mass_upper : ∀ i, (∑ p ∈ P i, 1 / (p : ℝ)) ≤ vmax
  prime : ∀ i p, p ∈ P i → p.Prime
  big_card_le : (M : ℝ) ≤ (2 / (5 * Real.log 2)) * Real.log L
  big_band : ∀ g : Fin M, ∃ a b : ℝ, P (reindex.symm g).val = primeBand a b ∧
    Real.exp (L ^ (1/4 : ℝ)) ≤ a ∧ 0 ≤ b
  big_log : ∀ (g : Fin M) p, p ∈ P (reindex.symm g).val →
    Real.log (p : ℝ) ≤ L ^ (1/2 : ℝ)
  big_lower : ∀ (g : Fin M) p, p ∈ P (reindex.symm g).val →
    Real.exp (L ^ (1/4 : ℝ)) ≤ (p : ℝ)

theorem exists_candidate_numbered_pool_bounds {scale : ℝ} (hscale : 0 < scale) :
    ∃ vmin vmax : ℝ, 0 < vmin ∧ 0 < vmax ∧ ∀ᶠ L : ℝ in atTop,
      ∀ {N M : ℕ} (E : Fin N ≃ ↥(candidatePIndices scale L))
        (e : {g // g ∉ (candidateRootBigGroups scale L E)ᶜ} ≃ Fin M),
      CandidateNumberedPoolBounds scale L vmin vmax
        (candidateRootPools scale L E) (candidateRootBigGroups scale L E) e := by
  obtain ⟨vmin,vmax,hvmin,hvmax,hpool⟩ := exists_candidate_P_pool_bounds hscale
  refine ⟨vmin,vmax,hvmin,hvmax,?_⟩
  filter_upwards [hpool, eventually_candidate_big_band_endpoints hscale,
    eventually_candidate_small_big_indices_disjoint hscale] with L hp hb hd
  intro N M E e
  let P := candidateRootPools scale L E
  let groups := candidateRootBigGroups scale L E
  have hM : M = (candidateBigPIndices scale L).card := by
    have hc := Fintype.card_congr e
    have hce : Fintype.card {g // g ∉ groupsᶜ} = groups.card := by
      simp only [mem_compl, not_not, Fintype.card_coe]
    rw [Fintype.card_fin] at hc
    exact hc.symm.trans (hce.trans (candidate_root_big_groups_card scale L E))
  have hbig (g : Fin M) : (E (e.symm g).val).val ∈ candidateBigPIndices scale L := by
    apply (candidate_root_big_groups_mem scale L E _).mp
    simpa only [mem_compl, not_not] using (e.symm g).property
  have hlo : Real.exp (L ^ (1/4 : ℝ)) ≤ Real.exp (L ^ (3/10 : ℝ)) :=
    Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hp.1 (by norm_num))
  have hhi : Real.exp (L ^ (2/5 : ℝ)) ≤ Real.exp (L ^ (1/2 : ℝ)) :=
    Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hp.1 (by norm_num))
  refine ⟨hp.1, candidate_root_small_groups_card scale L E hd, hM, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact hp.2.2.2.2.1 (fun h => hij (E.injective (Subtype.ext h)))
  · intro i
    exact (hp.2.2.2.2.2 (E i).val (E i).property).1
  · intro i
    exact (hp.2.2.2.2.2 (E i).val (E i).property).2.1
  · intro i p hpi
    exact ((hp.2.2.2.2.2 (E i).val (E i).property).2.2 p hpi).1
  · rw [hM]
    have hc : ((candidateBigPIndices scale L).card : ℝ) ≤
        ((candidatePIndices scale L).card : ℝ) := by
      exact_mod_cast card_le_card (show candidateBigPIndices scale L ⊆
        candidatePIndices scale L from subset_union_right)
    exact hc.trans hp.2.2.2.1
  · intro g
    obtain ⟨a,b,heq,ha,_,hb0⟩ := hb _ (hbig g)
    exact ⟨a,b,heq,hlo.trans ha,hb0⟩
  · intro g p hpg
    obtain ⟨a,b,heq,ha,hbhi,hb0⟩ := hb _ (hbig g)
    change p ∈ candidatePBand (scale * L) (E (e.symm g).val).val at hpg
    rw [heq] at hpg
    obtain ⟨hprime,_,hpb⟩ := (mem_primeBand_iff ((Real.exp_pos _).le.trans ha) hb0 p).mp hpg
    calc
      Real.log (p : ℝ) ≤ Real.log (Real.exp (L ^ (1/2 : ℝ))) :=
        Real.log_le_log (by exact_mod_cast hprime.pos) (hpb.trans (hbhi.trans hhi))
      _ = _ := Real.log_exp _
  · intro g p hpg
    obtain ⟨a,b,heq,ha,_,hb0⟩ := hb _ (hbig g)
    change p ∈ candidatePBand (scale * L) (E (e.symm g).val).val at hpg
    rw [heq] at hpg
    exact (hlo.trans ha).trans
      ((mem_primeBand_iff ((Real.exp_pos _).le.trans ha) hb0 p).mp hpg).2.1.le

end Bounty

end


-- Source module: CandidateNumberedProjectedCosts
section

/- The literal projected root edges for the actual numbered candidate pool. -/

open Finset Filter
open scoped Topology BigOperators Classical
namespace Bounty

def CandidateNumberedProjectedEdgeCosts
    (scale L vmin vmax A Cbad E z C₂ tau q w x : ℝ) (m J : ℕ) : Prop :=
    let Q := ⌊L ^ q⌋₊
    let h := L ^ (-w)
    let ξ := L ^ (-x)
    ∀ {N M n B : ℕ} (index : Fin N ≃ ↥(candidatePIndices scale L)),
    let P := candidateRootPools scale L index
    let groups := candidateRootBigGroups scale L index
    ∀ (reindex : {g // g ∉ groupsᶜ} ≃ Fin M),
    ∀ [∀ z : PhysicalPrime P, NeZero z.2.val]
      [∀ z : PhysicalPrime (fun a : ↥groupsᶜ => P a.val), NeZero z.2.val]
      [∀ g (p : P (reindex.symm g).val), NeZero p.val],
    ∀ (hPs : ∀ (a : ↥groupsᶜ) p, p ∈ P a.val → Nat.Prime p)
      (hPb : ∀ (g : Fin M) p, p ∈ P (reindex.symm g).val → Nat.Prime p)
      (hcross : ∀ (a : ↥groupsᶜ) (g : Fin M), Disjoint (P a.val) (P (reindex.symm g).val)),
    let V := fun i => ∑ p ∈ P i, 1 / (p : ℝ)
    ∀ probes : Fin N → Finset (Fin J), (∀ g : Fin M, (probes (reindex.symm g).val).card = m) →
    ∀ r t : Finset (Fin M), ∀ hrt : Disjoint r t,
    (1 / (80 * Real.log 2)) * Real.log L ≤ (r.card : ℝ) → (1 / (80 * Real.log 2)) * Real.log L ≤ (t.card : ℝ) →
    ∀ (ζ : ℕ → ℝ) (k : ℕ → ℤ) (θ : ℝ),
    (∀ j : Fin (n + 1), |ζ (n-j.val)| ≤ L ^ z) →
    (∀ j : Fin (n + 1), k (n-j.val) ≠ 0) →
    (∀ j : Fin (n + 1), ((k (n-j.val)).natAbs : ℝ) ≤ L ^ C₂) →
    ∀ baseline : (g : Fin M) → P (reindex.symm g).val → ℝ,
    ∀ T : ℝ, 0 ≤ T → T ≤ L ^ tau →
    (∀ (g : Fin M) (p : P (reindex.symm g).val), baseline g p = 1 - T / (p.val : ℝ)) →
    (∀ g p, 1 / 2 ≤ baseline g p ∧ baseline g p ≤ 1) →
    ∀ (retention : Fin (n + 2) → ℝ)
      (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := 1) (n := n) (B := B))
      (encode : ((g : Fin M) × P (reindex.symm g).val) → ℤ)
      (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + 1) B
          ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
        Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + 1) B
          ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) → ℝ),
    let f := physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex
    let patterns := (univ : Finset (RepeatedBigPrimePatternIndex (ell := 1)
      probes (r.map f) (t.map f)))
    let C := repeatedBigPrimePatternCut (ell := 1) probes (r.map f) (t.map f)
    let ζroot := fun time (_ : RepeatedBigPrimePatternIndex (ell := 1)
      probes (r.map f) (t.map f)) => ζ time
    let kroot := fun time (_ : RepeatedBigPrimePatternIndex (ell := 1)
      probes (r.map f) (t.map f)) => k time
    let β := fun (g : Fin M) (p : P (reindex.symm g).val) =>
      ((p.val : ℝ)*baseline g p)⁻¹
    let hC : ∀ i : patterns, ∀ a : ↥groupsᶜ, C i.val a.val = ∅ :=
      fun i a => physical_root_prime_full_pattern_small_cut groups reindex probes r t i.val a
    let K := fun (time : ℕ)
      (i : RepeatedBigPrimePatternIndex (ell := 1) probes (r.map f) (t.map f))
      (L R : PhysicalMarkLists P J 1) (aux : PhysicalAuxLabels P (C i)) =>
      if time % 2 = 0 then
        (starRingEnd ℂ) (physicalRootPrimeKernel P V probes (r.map f) (t.map f)
          ((Finset.disjoint_map f).mpr hrt) Q h ξ i R L aux)
      else physicalRootPrimeKernel P V probes (r.map f) (t.map f)
        ((Finset.disjoint_map f).mpr hrt) Q h ξ i L R aux
    let row := physicalRootFourierRow groups reindex patterns C hC kroot V (1/2) ζroot K θ β retention (9/10)
      hPs hPb hcross code encode ν
    let Wroot := physicalSmallBigMeasure (fun a : ↥groupsᶜ => V a.val)
      (productMemoryWeight (fun g p => β g p / V (reindex.symm g).val)
        (fun g => unrestrictedResidueWeight (fun p => β g p / V (reindex.symm g).val)))
    let decay := A ^ groupsᶜ.card *
      (L ^ (-E) + 2 * repeatedBigFamilyEnvelope M m Q ξ *
        Real.sqrt ((B : ℝ) / (((J + 1).choose 1) ^ groupsᶜ.card : ℕ)) *
        Real.sqrt (unrestrictedEdgeEnergyBound (9/10) (100*(vmax+1)) vmin vmax (1 + m) ^ M))
    let excess := max decay (repeatedBigFamilyEnvelope M m Q ξ * Cbad ^ groupsᶜ.card *
      Real.sqrt (unrestrictedEdgeEnergyBound (9/10) (100*(vmax+1)) vmin vmax (1 + m) ^ M))
    0 < decay ∧ decay ≤ excess ∧
      ∀ (j : Fin (n + 1))
        (F : PhysicalRootMixedState (P := P) (J := J) (ell := 1) (B := B) groups reindex → ℂ),
      (∀ d, ProductMemorySymmetric (fun x => F (d,x))) →
      cleanActiveNorm Wroot (row none (row (some (.inr j)) (row none F))) ≤
        (if j ∈ physicalSelectedAffectedEdges (fun _ : Fin M => J + 1) B (n + 1) code
          then excess else decay) * cleanActiveNorm Wroot F

theorem exists_candidate_numbered_projected_edge_costs {scale : ℝ} (hscale : 0 < scale) :
    ∃ vmin vmax : ℝ, 0 < vmin ∧ 0 < vmax ∧
      (∀ᶠ L : ℝ in atTop, ∀ {N M : ℕ} (index : Fin N ≃ ↥(candidatePIndices scale L))
        (reindex : {g // g ∉ (candidateRootBigGroups scale L index)ᶜ} ≃ Fin M),
        CandidateNumberedPoolBounds scale L vmin vmax
          (candidateRootPools scale L index) (candidateRootBigGroups scale L index) reindex) ∧
      ∀ C₂ : ℝ, ∃ A Cbad : ℝ, 1 ≤ A ∧ 1 ≤ Cbad ∧
      ∀ (E D z tau : ℝ) (m J : ℕ), 0 ≤ D → 0 ≤ z → 0 ≤ tau → 1 ≤ m →
      (1 / (80 * Real.log 2)) * Real.log (((1 : ℕ) : ℝ)^1 / (m : ℝ)^1) / 2 ≤ -(E+2) →
      (m : ℝ)*(2 / (5 * Real.log 2))*Real.log 3+E+2 ≤ D →
      let κ := (2 / (5 * Real.log 2)) * Real.log (primeFiberFactorBound vmin m)
      let s₁ : ℝ := 1/2+1/2
      let A₀ := D+2*(s₁+1)
      let q := 2*κ+(s₁+1)+2*A₀+3
      let w := 4*q+max z q+A₀+2
      let x := (s₁+w+2)+2*A₀+2
      ∀ᶠ L : ℝ in atTop,
        CandidateNumberedProjectedEdgeCosts scale L vmin vmax A Cbad E z C₂ tau q w x m J := by
  obtain ⟨vmin,vmax,hvmin,hvmax,hpool⟩ := exists_candidate_numbered_pool_bounds hscale
  refine ⟨vmin,vmax,hvmin,hvmax,hpool,?_⟩
  intro C₂
  obtain ⟨A,Cbad,hA,hCbad,hcost⟩ := WeakZeroFree.actual_exists_realized_root_projected_edge_costs
    (qsmall := (1/2 : ℝ)) (by norm_num) (by norm_num) hvmin hscale 1 C₂
  refine ⟨A,Cbad,hA,hCbad,?_⟩
  intro E D z tau m J hD hz htau hm hgap hDgap κ s₁ A₀ q w x
  have ha : (0 : ℝ) ≤ 2 / (5 * Real.log 2) := by positivity
  have hactual := hcost (1/4) (1/2) z (2/(5*Real.log 2)) vmin D (1/2) E
    (1/(80*Real.log 2)) tau m J (by norm_num) (by norm_num) hz ha hvmin hD
    (by norm_num) htau (by norm_num) hm hgap hDgap
  filter_upwards [hactual,hpool,
    eventually_mul_rpow_le_exp_rpow q 2 (c := (1/4 : ℝ)) (by norm_num)] with L hc hp hq
  let Q := ⌊L ^ q⌋₊
  intro N M n B index P groups reindex _ _ _ hPs hPb hcross V
    probes hprobes r t hrt hr ht ζ k θ hζ hk hkmax baseline T hT hTmax hbaseline hbaselineBounds
  have hd := hp index reindex
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hd.one_le
  have hinj : Function.Injective (fun g : Fin M => (reindex.symm g).val) := by
    intro g h heq
    exact reindex.symm.injective (Subtype.ext heq)
  have hbdis : Pairwise (fun g h : Fin M => Disjoint (P (reindex.symm g).val)
      (P (reindex.symm h).val)) := hd.disjoint.comp_of_injective hinj
  have hprime : ∀ (g : Fin M) p, p ∈ P (reindex.symm g).val → p.Prime ∧ Q < p := by
    intro g p hp
    refine ⟨hd.prime _ p hp, ?_⟩
    have hpow : 0 < L^q := Real.rpow_pos_of_pos hLpos _
    have hfloor : (Q : ℝ) ≤ L^q := Nat.floor_le hpow.le
    have hlow := hd.big_lower g p hp
    have hlt : (Q : ℝ) < (p : ℝ) := by linarith
    exact_mod_cast hlt
  exact hc P groups reindex hPs hPb hcross
    (candidateRootMixedPoolRealization scale L index reindex) V hbdis hprime
    (fun _ => rfl) (fun g => hd.mass_lower _) hd.big_log hd.big_card_le hd.big_band
    probes hprobes r t hrt hr ht ζ k θ hζ hk hkmax baseline T (Real.exp (L^(1/4 : ℝ)))
    hT hTmax le_rfl (fun g p => hd.big_lower g p.val p.property) hbaseline hbaselineBounds
    (fun a => hd.mass_lower a.val) (9/10) (100*(vmax+1)) vmax (by norm_num) (by norm_num)
    (by linarith) (fun g => hd.mass_upper _)

end Bounty

end


-- Source module: CandidateNumberedEdgeParameters
section

/- Fix all candidate edge exponents before the eventual scale and root data. -/

open Filter Finset
namespace Bounty

theorem exists_candidate_numbered_edge_parameter_order {scale : ℝ} (hscale : 0 < scale) :
    ∃ vmin vmax : ℝ, 0 < vmin ∧ 0 < vmax ∧
      (∀ᶠ L : ℝ in atTop, ∀ {N M : ℕ} (index : Fin N ≃ ↥(candidatePIndices scale L))
        (reindex : {g // g ∉ (candidateRootBigGroups scale L index)ᶜ} ≃ Fin M),
        CandidateNumberedPoolBounds scale L vmin vmax
          (candidateRootPools scale L index) (candidateRootBigGroups scale L index) reindex) ∧
      ∀ C₂ : ℝ, ∃ A Cbad : ℝ, 1 ≤ A ∧ 1 ≤ Cbad ∧
      let Kghost := physicalGhostUniformEnergyBound (9/10) vmax (100*(vmax+1))
      ∀ Etarget z tau : ℝ, 0 ≤ Etarget → 0 ≤ z → 0 ≤ tau →
    let a : ℝ := 2 / (5 * Real.log 2)
    let Cv := max 0 (candidateMixedRareCostExponent 1 Kghost)
    let G := Etarget + 1 + Cv + 2
    0 ≤ G ∧ Etarget + 1 + Cv + 2 ≤ G ∧
    ∃ (E : ℝ) (m : ℕ) (D : ℝ),
      E = G + candidateMixedRareCostExponent A 1 + 1 ∧
      1 ≤ m ∧ 0 ≤ D ∧
      (1 / (80 * Real.log 2)) * Real.log (((1 : ℕ) : ℝ)^1 / (m : ℝ)^1) / 2 ≤ -(E+2) ∧
      (m : ℝ)*a*Real.log 3 + E+2 ≤ D ∧
      let κ := a * Real.log (primeFiberFactorBound vmin m)
      let s₁ := (1/2 : ℝ) + 1/2
      let A₀ := D + 2*(s₁+1)
      let q := 2*κ + (s₁+1) + 2*A₀ + 3
      let w := 4*q + max z q + A₀ + 2
      let x := (s₁+w+2) + 2*A₀ + 2
      let C := (m : ℝ)*a*Real.log 2 + 4*q + 2*x + 1
      let Kedge := unrestrictedEdgeEnergyBound (9/10) (100*(vmax+1)) vmin vmax (1+m)
      let Ca := max 0 (C + candidateMixedRareCostExponent Cbad Kedge)
      0 ≤ q ∧ 0 ≤ w ∧ 0 ≤ x ∧ 0 ≤ C ∧ 0 ≤ Ca ∧ 0 ≤ Cv ∧
      ∀ J₀ : ℕ, ∃ J : ℕ, max m J₀ ≤ J ∧
        let Ch := max 0 (candidateMixedRareCostExponent 1 ((2 : ℝ)^(2*(J+1))))
        0 ≤ Ch ∧ ∀ᶠ L : ℝ in atTop,
          CandidateNumberedProjectedEdgeCosts scale L vmin vmax A Cbad E z C₂ tau q w x m J ∧
          let Q := ⌊L^q⌋₊
          let ξ := L^(-x)
          let small := (candidateSmallPIndices scale L).card
          let big := (candidateBigPIndices scale L).card
          let F := repeatedBigFamilyEnvelope big m Q ξ
          0 ≤ F ∧ F ≤ L^C ∧ ∀ cap : ℕ, cap ≤ Nat.ceil (L^2) →
            let decay := A^small * (L^(-E) +
              2*F*Real.sqrt ((cap : ℝ)/(((J+1).choose 1)^small : ℕ))*Real.sqrt (Kedge^big))
            decay ≤ L^(-G) ∧ max decay (F*Cbad^small*Real.sqrt (Kedge^big)) ≤ L^Ca ∧
              Real.sqrt (Kghost^big) ≤ L^Cv ∧ (2 : ℝ)^((J+1)*big) ≤ L^Ch := by
  obtain ⟨vmin,vmax,hvmin,hvmax,hpool,hcost⟩ :=
    exists_candidate_numbered_projected_edge_costs hscale
  refine ⟨vmin,vmax,hvmin,hvmax,hpool,?_⟩
  intro C₂
  obtain ⟨A,Cbad,hA,hCbad,hcost⟩ := hcost C₂
  refine ⟨A,Cbad,hA,hCbad,?_⟩
  intro Kghost Etarget z tau hEt hz ht a Cv G
  have hKghost : 0 ≤ Kghost := (Real.exp_pos _).le
  have hs := exists_candidate_selected_parameter_order hscale candidate_selection_beta_pos
    1 (by norm_num) A Cbad (Etarget+1) (1/2) z (1/2) (9/10) (100*(vmax+1))
    vmin vmax Kghost (by linarith) (by linarith) (by linarith) (by norm_num) hz
    (by norm_num) hKghost
  obtain ⟨hG,hgain,E,m,D,hE,hm,hD,hgap,hDgap,hs⟩ := hs
  refine ⟨hG,hgain,E,m,D,hE,hm,hD,hgap,hDgap,?_⟩
  intro κ s₁ A₀ q w x C Kedge Ca
  obtain ⟨hq,hw,hx,hC,hCa,hCv,hs⟩ := hs
  refine ⟨hq,hw,hx,hC,hCa,hCv,?_⟩
  intro J₀
  obtain ⟨J,hJ,hCh,hbudget⟩ := hs J₀
  refine ⟨J,hJ,hCh,?_⟩
  exact (hcost E D z tau m J hD hz ht hm hgap hDgap).and hbudget

end Bounty

end
