import ActualSelectedFoundation

/-! Original-data residue interfaces, reindexing, and finite endpoint bounds. -/

open scoped Topology BigOperators Classical

-- Source module: PhysicalRootMixedForests
section

/- The original mixed root action is a signed sum of common forests,
with the entire small-plan and signed pattern sum inside each forest term. -/

open Finset Classical
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

noncomputable def physicalRootMixedForestAction
    (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (L : PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B) : ℂ :=
  let _ := physicalMixedSmallPlanFintype (Ps := (fun s : ↥groupsᶜ => P s.val))
    (J := J) (ell := ell) (I := patterns) ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
  ∑ sp : PhysicalMixedSmallPlan (Ps := (fun s : ↥groupsᶜ => P s.val)) (J := J) (ell := ell)
      (I := patterns) ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))),
    physicalRootCommonForestAction groups e patterns C hC k (L, sp) V q ζ K r θ β retention ρ code f x

include hPs hPb hdis in
theorem physical_root_mixed_action_forests
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ) (hinj : Function.Injective encode)
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (L : PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B)
    (hx : FullActiveInjective x)
    (hcover : FullMixedLedgerCovers (fun g (p : P (e.symm g).val) => p.val) B
      (fullActiveInitialLedger x, x)) :
    physicalRootMixedAction groups e patterns C hC k V q ζ K r θ β retention ρ hPs hPb hdis f L x =
      ∑ code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B),
        (-1 : ℂ) ^ birthForestRank code *
          physicalRootMixedForestAction groups e patterns C hC k V q ζ K r θ β retention ρ code f L x := by
  let _ := physicalMixedSmallPlanFintype (Ps := (fun s : ↥groupsᶜ => P s.val))
    (J := J) (ell := ell) (I := patterns) ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
  rw [physical_root_mixed_action_eq_plan_sum]
  simp_rw [physical_root_effective_common_forests groups e patterns C hC k _ V q ζ K r θ β retention ρ
    encode hinj f x hx hcover]
  rw [sum_comm]
  apply sum_congr rfl
  intro code _
  unfold physicalRootMixedForestAction
  rw [mul_sum]

end Action
end Bounty

end


-- Source module: PhysicalRootForestScalar
section

/- The literal original root scalar, including initial mark weights, is a signed common-forest sum. -/

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
  (r : PhysicalGroupResidues P groupsᶜ) (θ : ℝ)
  (β : PhysicalPrime P → ℝ) (ρ : ℝ)
  (hP : ∀ g a, a ∈ P g → Nat.Prime a)
  (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))

noncomputable def physicalRootForestScalar : ℂ :=
  (physicalStateMass (fun s : ↥groupsᶜ => V s.val) J ell : ℂ) *
  ∑ Ls : PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell,
    ∑ Lb : PhysicalMarkLists (fun g => P (e.symm g).val) J ell,
      ((∏ g, ∏ s : PhysicalSlots J ell,
        β ⟨(e.symm g).val, Lb g s⟩ / V (e.symm g).val : ℝ) : ℂ) *
      ∑ code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B),
        (-1 : ℂ) ^ birthForestRank code *
        physicalRootMixedForestAction (n := n) groups e patterns C hC k V q ζ K r θ
          (fun (g : Fin M) (z : P (e.symm g).val) => β ⟨(e.symm g).val, z⟩)
          (fun j => physicalEndpointSchedule q (n + 1) j.val) ρ code
          fullMemoryVacuum Ls (physicalFullMemoryState (fun _ => ∅) Lb
            (fun g => fullEmptyBoundedMemory (UnrestrictedResidueParticle (fun z : P (e.symm g).val => z.val)) B))

theorem physical_root_mixed_scalar_forests
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ) (hinj : Function.Injective encode) :
    physicalRootMixedScalar (n := n) (B := B) groups e patterns C hC V q ζ k K r θ β ρ hP hdis =
      physicalRootForestScalar (n := n) (B := B) groups e patterns C hC V q ζ k K r θ β ρ := by
  unfold physicalRootMixedScalar physicalRootForestScalar
  congr 1
  apply sum_congr rfl
  intro Ls _
  apply sum_congr rfl
  intro Lb _
  congr 1
  apply physical_root_mixed_action_forests _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ encode hinj
  · exact physical_full_state_injective _ _ _
  · exact physical_full_empty_initial_ledger_covers _ _

end Scalar
end Bounty

end


-- Source module: PhysicalSmallBigReadoutNorm
section

/- Passing an operator estimate to the original normalized readout does
not introduce a factor for the number of small residue classes. -/

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

theorem physical_small_big_readout_of_unnormalized_norm
    (hVs : ∀ s, 0 < Vs s) (hMass : ∀ s, ∑ p ∈ Ps s, 1 / (p : ℝ) = Vs s)
    (hμ : ∀ g p, 0 ≤ μ g p) (hν : ∀ g z, 0 ≤ ν g z)
    (hempty : ∀ g, (empty g).1.val = 0) (hb : ∀ s x, ‖boundary s x‖ ≤ 1)
    {K : ℝ} (hK : 0 ≤ K)
    (hF : cleanActiveNorm (physicalSmallBigMeasure Vs (productMemoryWeight μ ν)) F ≤
      K * cleanActiveNorm (physicalSmallBigMeasure (P := Ps) (J := J) (ell := ell)
        Vs (productMemoryWeight μ ν)) (fun s => fullMemoryVacuum (M := fun _ => J + ell) (B := B) s.2)) :
    ‖physicalSmallBigInitialReadout Vs C μ empty boundary F‖ ≤
      K * ∏ g, (∑ p, μ g p) ^ (J + ell) := by
  apply physical_small_big_initial_readout_operator_bound Vs C μ ν empty boundary F
    hVs hMass hμ hν hempty hb hK
  rw [physical_small_big_normalized_norm_eq, physical_small_big_normalized_norm_eq]
  calc
    _ ≤ Real.sqrt (∏ p : PhysicalPrime Ps, (1 : ℝ) / p.2.val) *
        (K * cleanActiveNorm (physicalSmallBigMeasure Vs (productMemoryWeight μ ν))
          (fun s => fullMemoryVacuum (M := fun _ => J + ell) (B := B) s.2)) :=
      mul_le_mul_of_nonneg_left hF (Real.sqrt_nonneg _)
    _ = _ := by ring

end Readout
end Bounty

end


-- Source module: PhysicalRootFourierReadout
section

/- The actual local root Fourier word is the exact sum over its original
planned big actions, with every small factor and coefficient retained. -/

open Finset
open scoped Classical
namespace Bounty
section Root
variable {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
  [∀ z : PhysicalPrime P, NeZero z.2.val]
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
  (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
  (k : ℕ → I → ℤ)

  (V : Fin N → ℝ) (q : ℝ) (ζ : ℕ → I → ℝ)
  (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
    PhysicalAuxLabels P (C i) → ℂ)
  (θ : ℝ)
  (β : (g : Fin M) → P (e.symm g).val → ℝ)
  (retention : Fin (n + 2) → ℝ) (ρ : ℝ)

  (hPs : ∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p)
  (hPb : ∀ (g : Fin M) p, p ∈ P (e.symm g).val → Nat.Prime p)
  (hdis : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (e.symm g).val))


variable (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ)
    (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) → ℝ)

noncomputable def physicalRootFourierVectorAction
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ) :
    PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e → ℂ :=
  finiteOperatorListAction
    (physicalRootFourierRow groups e patterns C hC k V q ζ K θ β retention ρ hPs hPb hdis
      code encode ν)
    ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
    (fun s => f s.2)

noncomputable def physicalRootFourierBoundary
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B) : ℂ :=
  fullMixedCommonBoundaryMultiplier (fun _ : Fin M => J + ell) B
    ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) code ν encode
    (fullMixedCommonInitialPrime x)

omit [∀ z : PhysicalPrime P, NeZero z.2.val] in
theorem physical_root_fourier_boundary_norm_le
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B) :
    ‖physicalRootFourierBoundary groups e code encode ν x‖ ≤ 1 :=
  full_mixed_common_boundary_multiplier_norm_le _ _ _ _ _ _ _

variable [∀ z : PhysicalPrime (fun s : ↥groupsᶜ => P s.val), NeZero z.2.val]

noncomputable def physicalRootFourierReadout : ℂ :=
  physicalSmallBigInitialReadout (fun s : ↥groupsᶜ => V s.val) (fun _ : Fin M => ∅)
    (fun g p => β g p / V (e.symm g).val)
    (fun g => fullEmptyBoundedMemory
      (UnrestrictedResidueParticle (fun z : P (e.symm g).val => z.val)) B)
    (fun _ => physicalRootFourierBoundary groups e code encode ν)
    (physicalRootFourierVectorAction groups e patterns C hC k V q ζ K θ β retention ρ
      hPs hPb hdis code encode ν fullMemoryVacuum)

variable [∀ g (z : P (e.symm g).val), NeZero z.val]

theorem physical_root_fourier_readout_norm_le
    (hVs : ∀ s : ↥groupsᶜ, 0 < V s.val)
    (hMass : ∀ s : ↥groupsᶜ, ∑ p ∈ P s.val, 1 / (p : ℝ) = V s.val)
    (hμ : ∀ g p, 0 ≤ β g p / V (e.symm g).val)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hF : cleanActiveNorm
      (physicalSmallBigMeasure (fun s : ↥groupsᶜ => V s.val)
        (productMemoryWeight (fun g p => β g p / V (e.symm g).val)
          (fun g => unrestrictedResidueWeight (fun p => β g p / V (e.symm g).val))))
      (physicalRootFourierVectorAction groups e patterns C hC k V q ζ K θ β retention ρ
        hPs hPb hdis code encode ν fullMemoryVacuum) ≤
      bound * cleanActiveNorm
        (physicalSmallBigMeasure (P := fun s : ↥groupsᶜ => P s.val) (J := J) (ell := ell)
          (fun s : ↥groupsᶜ => V s.val)
          (productMemoryWeight (fun g p => β g p / V (e.symm g).val)
            (fun g => unrestrictedResidueWeight (fun p => β g p / V (e.symm g).val))))
        (fun s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e =>
          fullMemoryVacuum s.2)) :
    ‖physicalRootFourierReadout groups e patterns C hC k V q ζ K θ β retention ρ hPs hPb hdis
      code encode ν‖ ≤ bound * ∏ g, (∑ p, β g p / V (e.symm g).val) ^ (J + ell) := by
  apply physical_small_big_readout_of_unnormalized_norm
    (fun s : ↥groupsᶜ => V s.val) (fun _ : Fin M => ∅)
    (fun g p => β g p / V (e.symm g).val)
    (fun g => unrestrictedResidueWeight (fun p => β g p / V (e.symm g).val))
    _ _ _ hVs hMass hμ
  · intro g z
    exact hμ g z.1
  · intro g
    rfl
  · intro s x
    exact physical_root_fourier_boundary_norm_le groups e code encode ν x
  · exact hbound
  · exact hF

end Root
end Bounty

end


-- Source module: PhysicalMixedWordSupport
section

/- An actual edge annihilates invalid small source states. Ghosts and
permutations preserve this support, with arbitrary local decorations. -/

open Finset
open scoped Classical
namespace Bounty
section Support
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
  (phase : ∀ tag s, PhysicalMixedWordEvent (ell := ell) n shared B A Δ D tag s → ℂ)

theorem physical_mixed_word_row_edge_invalid (k : K)
    (F : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B → ℂ)
    (s : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B)
    (h : ¬ physicalResidueMarksValid s.1.1 s.1.2) :
    physicalMixedWordRow n shared B A Δ D kbig ω μ qghost ρ Vb Vs qedge phase
      (some (.inr k)) F s = 0 := by
  unfold physicalMixedWordRow finiteLocalPhasedRow
  apply sum_eq_zero
  intro e _
  simp only [physicalMixedWordWeight, physicalSmallBigPositiveWeight,
    physicalResidueVertexWeight, if_neg h, zero_mul, mul_zero, ite_self,
    Complex.ofReal_zero]

theorem physical_mixed_word_row_preserves_valid_support (tag : Option (V ⊕ K))
    (F : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B → ℂ)
    (hF : ∀ s, ¬ physicalResidueMarksValid s.1.1 s.1.2 → F s = 0)
    (s : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B)
    (h : ¬ physicalResidueMarksValid s.1.1 s.1.2) :
    physicalMixedWordRow n shared B A Δ D kbig ω μ qghost ρ Vb Vs qedge phase
      tag F s = 0 := by
  cases tag with
  | none =>
    unfold physicalMixedWordRow finiteLocalPhasedRow
    apply sum_eq_zero
    intro e _
    rw [hF _ (by
      change ¬ physicalResidueMarksValid s.1.1 (physicalPermuteLabels e.1 s.1.2)
      rwa [physical_residue_marks_valid_permute])]
    exact mul_zero _
  | some tag =>
    cases tag with
    | inl j =>
      unfold physicalMixedWordRow finiteLocalPhasedRow
      apply sum_eq_zero
      intro e _
      rw [hF (physicalMixedWordTarget n shared B A Δ D kbig (some (.inl j)) s e) h]
      exact mul_zero _
    | inr k =>
      exact physical_mixed_word_row_edge_invalid n shared B A Δ D kbig ω μ qghost ρ Vb Vs qedge phase k F s h

theorem physical_mixed_word_action_invalid
    (tags : List (Option (V ⊕ K)))
    (hedge : ∃ k, some (.inr k) ∈ tags)
    (F : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B → ℂ)
    (s : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B)
    (h : ¬ physicalResidueMarksValid s.1.1 s.1.2) :
    finiteOperatorListAction
      (physicalMixedWordRow n shared B A Δ D kbig ω μ qghost ρ Vb Vs qedge phase)
      tags F s = 0 := by
  induction tags generalizing s with
  | nil =>
    rcases hedge with ⟨k, hk⟩
    exact False.elim (List.not_mem_nil hk)
  | cons tag tags ih =>
    rcases hedge with ⟨k, hk⟩
    rcases List.mem_cons.mp hk with heq | hmem
    · subst tag
      exact physical_mixed_word_row_edge_invalid n shared B A Δ D kbig ω μ qghost ρ Vb Vs qedge phase k _ s h
    · exact physical_mixed_word_row_preserves_valid_support n shared B A Δ D kbig ω μ qghost ρ Vb Vs qedge phase tag _
        (fun t ht => ih ⟨k, hmem⟩ t ht) s h

end Support
end Bounty

end


-- Source module: PhysicalRootFourierSupport
section

/- The exact original Fourier word has valid small source support. -/

open Finset
open scoped Classical
namespace Bounty
section Root
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


variable (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ)
    (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) → ℝ)

theorem physical_root_fourier_word_invalid
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (L : PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B)
    (h : ¬ physicalResidueMarksValid (physicalGroupResidueVector r) L) :
    physicalRootFourierWord groups e patterns C hC k V q ζ K r θ β retention ρ
      hPs hPb hdis code encode ν f L x = 0 := by
  unfold physicalRootFourierWord
  apply @physical_mixed_word_action_invalid
    ↥groupsᶜ (Fin M) ↥patterns (Fin (n + 2)) (Fin (n + 1))
    _ _ _ _ (fun a : ↥groupsᶜ => P a.val) (fun g => ↥(P (e.symm g).val))
    _ (fun _ p => p.val)
    (fun g p => inferInstanceAs (NeZero (⟨(e.symm g).val, p⟩ : PhysicalPrime P).2.val))
  · refine ⟨⟨0, Nat.zero_lt_succ n⟩, List.mem_map.mpr ⟨2, ?_, ?_⟩⟩
    · apply List.mem_range.mpr
      omega
    · have hi : 2 < 4 * (n + 1) + 1 := by omega
      simp only [physicalSelectedFineTag, dif_pos hi]
      rfl
  · exact h

end Root
end Bounty

end


-- Source module: PhysicalRootFourierAction
section

/- The initial common Fourier factor is a boundary multiplier outside
the exact effective root path action. -/

open Finset
open scoped Classical
namespace Bounty
section Root
variable {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
  [∀ z : PhysicalPrime P, NeZero z.2.val]
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
  (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
  (k : ℕ → I → ℤ)
  (pl : PhysicalRootSmallPlan (P := P) (J := J) (ell := ell) (n := n) groups patterns)
  (V : Fin N → ℝ) (q : ℝ) (ζ : ℕ → I → ℝ)
  (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
    PhysicalAuxLabels P (C i) → ℂ)
  (r : PhysicalGroupResidues P groupsᶜ) (θ : ℝ)
  (β : (g : Fin M) → P (e.symm g).val → ℝ)
  (retention : Fin (n + 2) → ℝ) (ρ : ℝ)

noncomputable def physicalRootEffectiveFourierAction
    (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ)
    (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) → ℝ)
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B) : ℂ :=
  let _ : ∀ g (z : P (e.symm g).val), NeZero z.val :=
    fun g z => inferInstanceAs (NeZero (⟨(e.symm g).val, z⟩ : PhysicalPrime P).2.val)
  let Cb := fun key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val)
    (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      fun g => C key.2.1.val (e.symm g).val
  let kb := fun key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val)
    (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      k (n - key.1.val) key.2.1.val * (physicalSharedProduct (physicalSharedPrefix key.2.2.1) : ℕ)
  let steps := physicalMixedBigSteps
    ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) pl.1 pl.2
  let sizes := fun g (p : P (e.symm g).val) => p.val
  let shared := fun key g => physicalFullSharedIndices (ell := ell) (Cb key g)
  let aux := fun key (_ : SharedActiveLabels (fun g => ↥(P (e.symm g).val)) (shared key)) =>
    PhysicalAuxLabels (fun g => P (e.symm g).val) (Cb key)
  let delta := fun key => physicalFullEdgeDelta (P := fun g => P (e.symm g).val) (ell := ell) (Cb key) (kb key)
  let displacement := fun key => physicalFullEdgeD (P := fun g => P (e.symm g).val) (ell := ell) (Cb key)
  let omega := fun key (_ : SharedActiveLabels (fun g => ↥(P (e.symm g).val)) (shared key)) (a : PhysicalAuxLabels (fun g => P (e.symm g).val) (Cb key)) =>
    physicalAuxMass (fun g => V (e.symm g).val) (Cb key) a
  let _ := fullPermutationMixedEventFintype (J := Fin (n + 2)) sizes shared B aux delta displacement
  let _ := finiteEventPathFintype (FullPermutationMixedEvent sizes shared B aux delta displacement)
    (fullPermutationMixedEventTarget sizes shared B aux delta displacement) steps x
  fullPermutationMixedPathAction sizes shared B aux delta displacement omega
    (fun g p => β g p / V (e.symm g).val) retention ρ (fun g => V (e.symm g).val) steps
    (fun y path => physicalEffectivePlanSmallFactor (fun (i : patterns) g => C i.val (e.symm g).val)
        (fun (j : Fin (n + 1)) (i : patterns) => k (n - j.val) i.val) B
        (fun s : ↥groupsᶜ => V s.val) (fun _ => q)
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
        (physicalGroupResidueVector r) pl.1 pl.2 y path *
      finiteEventLocalPhase (FullPermutationMixedEvent sizes shared B aux delta displacement)
        (fullPermutationMixedEventTarget sizes shared B aux delta displacement)
        (physicalRootEffectiveFourierPhase groups e patterns C hC k V ζ K θ β ρ code encode ν)
        steps y path) f x

theorem physical_root_plan_fourier_action
    (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ)
    (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) → ℝ)
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B) :
    physicalRootPlanFourierIntegrand groups e patterns C hC k pl V q ζ K r θ β retention ρ
      code encode ν f x =
    fullMixedCommonBoundaryMultiplier (fun _ : Fin M => J + ell) B
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
      code ν encode (fullMixedCommonInitialPrime x) *
      physicalRootEffectiveFourierAction groups e patterns C hC k pl V q ζ K r θ β retention ρ
        code encode ν f x := by
  unfold physicalRootPlanFourierIntegrand physicalRootEffectiveFourierAction
    fullPermutationMixedPathAction finiteEventPathAction physicalRootEffectiveFourierPhase
  dsimp only
  rw [mul_sum]
  apply sum_congr rfl
  intro path _
  ring

end Root
end Bounty

end


-- Source module: PhysicalRootPlanIntegrable
section

/- Integrability of the literal root Fourier integrand retains the exact
path-dependent small-plan factor. -/

open Finset MeasureTheory
open scoped Classical
namespace Bounty
section Root
variable {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
  [∀ z : PhysicalPrime P, NeZero z.2.val]
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
  (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
  (k : ℕ → I → ℤ)
  (pl : PhysicalRootSmallPlan (P := P) (J := J) (ell := ell) (n := n) groups patterns)
  (V : Fin N → ℝ) (q : ℝ) (ζ : ℕ → I → ℝ)
  (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
    PhysicalAuxLabels P (C i) → ℂ)
  (r : PhysicalGroupResidues P groupsᶜ) (θ : ℝ)
  (β : (g : Fin M) → P (e.symm g).val → ℝ)
  (retention : Fin (n + 2) → ℝ) (ρ : ℝ)

theorem physical_root_plan_fourier_integrable
    (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ)
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B) :
    Integrable (fun ν => physicalRootPlanFourierIntegrand groups e patterns C hC k pl V q ζ K r θ β retention ρ
      code encode ν f x) (birthFourierCubeMeasure (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))))) := by
  let _ : ∀ g (z : P (e.symm g).val), NeZero z.val :=
    fun g z => inferInstanceAs (NeZero (⟨(e.symm g).val, z⟩ : PhysicalPrime P).2.val)
  let Cb := fun key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val)
    (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      fun g => C key.2.1.val (e.symm g).val
  let kb := fun key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val)
    (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      k (n - key.1.val) key.2.1.val * (physicalSharedProduct (physicalSharedPrefix key.2.2.1) : ℕ)
  let steps := physicalMixedBigSteps
    ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) pl.1 pl.2
  let sizes := fun g (p : P (e.symm g).val) => p.val
  let shared := fun key g => physicalFullSharedIndices (ell := ell) (Cb key g)
  let aux := fun key (_ : SharedActiveLabels (fun g => ↥(P (e.symm g).val)) (shared key)) =>
    PhysicalAuxLabels (fun g => P (e.symm g).val) (Cb key)
  let delta := fun key => physicalFullEdgeDelta (P := fun g => P (e.symm g).val) (ell := ell) (Cb key) (kb key)
  let displacement := fun key => physicalFullEdgeD (P := fun g => P (e.symm g).val) (ell := ell) (Cb key)
  let omega := fun key (_ : SharedActiveLabels (fun g => ↥(P (e.symm g).val)) (shared key)) (a : PhysicalAuxLabels (fun g => P (e.symm g).val) (Cb key)) =>
    physicalAuxMass (fun g => V (e.symm g).val) (Cb key) a
  let _ := fullPermutationMixedEventFintype (J := Fin (n + 2)) sizes shared B aux delta displacement
  let _ := finiteEventPathFintype (FullPermutationMixedEvent sizes shared B aux delta displacement)
    (fullPermutationMixedEventTarget sizes shared B aux delta displacement) steps x
  let F := fun path : FullPermutationMixedPath sizes shared B aux delta displacement steps x =>
    physicalEffectivePlanSmallFactor (fun (i : patterns) g => C i.val (e.symm g).val)
      (fun (j : Fin (n + 1)) (i : patterns) => k (n - j.val) i.val) B
      (fun s : ↥groupsᶜ => V s.val) (fun _ => q)
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
      (physicalGroupResidueVector r) pl.1 pl.2 x path *
    f (finiteEventPathTerminal (FullPermutationMixedEvent sizes shared B aux delta displacement)
      (fullPermutationMixedEventTarget sizes shared B aux delta displacement) steps x path)
  exact physical_selected_plan_fourier_integrable sizes shared B aux delta displacement
    (physicalFullCombinedEdgePhase Cb kb omega β ρ (fun g => V (e.symm g).val) (fun _ => 0)
          (physicalRootKeyCoefficient groups e patterns C hC ζ k K θ)) omega (fun g p => β g p / V (e.symm g).val) retention ρ (fun g => V (e.symm g).val)
    pl.1 pl.2 univ (fun _ => x) (fun path => path) F encode code

end Root
end Bounty

end


-- Source module: PhysicalRootMixedFourier
section

/- The original root forest action places its complete small-plan sum
inside the common Fourier integral. -/

open Finset MeasureTheory
open scoped Classical
namespace Bounty
section Root
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


noncomputable def physicalRootMixedFourierIntegrand
    (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ)
    (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) → ℝ)
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (L : PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B) : ℂ :=
  let _ := physicalMixedSmallPlanFintype (Ps := (fun s : ↥groupsᶜ => P s.val))
    (J := J) (ell := ell) (I := patterns) ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
  ∑ sp : PhysicalMixedSmallPlan (Ps := (fun s : ↥groupsᶜ => P s.val)) (J := J) (ell := ell)
      (I := patterns) ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))),
    physicalRootPlanFourierIntegrand groups e patterns C hC k (L, sp) V q ζ K r θ β retention ρ code encode ν f x

theorem physical_root_mixed_forest_fourier
    (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ) (hinj : Function.Injective encode)
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (L : PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B) :
    physicalRootMixedForestAction groups e patterns C hC k V q ζ K r θ β retention ρ code f L x =
      ∫ ν, physicalRootMixedFourierIntegrand groups e patterns C hC k V q ζ K r θ β retention ρ
        code encode ν f L x ∂birthFourierCubeMeasure (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) := by
  let _ := physicalMixedSmallPlanFintype (Ps := (fun s : ↥groupsᶜ => P s.val))
    (J := J) (ell := ell) (I := patterns) ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
  dsimp only [physicalRootMixedForestAction, physicalRootMixedFourierIntegrand]
  rw [integral_finsetSum]
  · apply sum_congr rfl
    intro sp _
    exact physical_root_common_forest_fourier groups e patterns C hC k (L, sp) V q ζ K r θ β retention ρ
      code encode hinj f x
  · intro sp _
    exact physical_root_plan_fourier_integrable groups e patterns C hC k (L, sp) V q ζ K r θ β retention ρ
      code encode f x

end Root
end Bounty

end


-- Source module: PhysicalMixedEffectiveLocal
section

/- The actual physical effective-parameter equivalence transports arbitrary
ordinary local phases to the original big-event paths. -/

namespace Bounty
section Effective
variable {S K V : Type} [Fintype S] {N J ell : ℕ}
  {Ps : S → Finset ℕ} {P : Fin N → Finset ℕ}
  (hPs : ∀ s p, p ∈ Ps s → Nat.Prime p)
  (hP : ∀ g p, p ∈ P g → Nat.Prime p)
  (hdis : ∀ s g, Disjoint (Ps s) (P g))
  (C : K → Fin N → Finset (Fin J)) (d : K → PhysicalSharedLists Ps J)
  (k : K → ℤ) (B : ℕ)

theorem physical_mixed_effective_big_local_phase
    (phase : ∀ (tag : Option (V ⊕ K)), (x : PhysicalFullBoundedState P J ell B) →
      FullPermutationMixedEvent (fun g (p : P g) => p.val)
        (fun key g => physicalFullSharedIndices (ell := ell) (C key g)) B
        (fun key _ => PhysicalAuxLabels P (C key))
        (fun key => physicalFullEdgeDelta (C key) (k key * (physicalSharedProduct (d key) : ℕ)))
        (fun key => physicalFullEdgeD (C key)) tag x → ℂ)
    (steps : List (Option (V ⊕ K)))
    (x : PhysicalFullBoundedState P J ell B)
    (p : FullPermutationMixedPath (fun g (p : P g) => p.val)
      (fun key g => physicalFullSharedIndices (ell := ell) (C key g)) B
      (fun key _ => PhysicalAuxLabels P (C key))
      (fun key => physicalMixedEdgeDelta (C key) (k key) (d key))
      (fun key => physicalMixedEdgeD (C key) (d key)) steps x) :
    finiteEventLocalPhase
      (FullPermutationMixedEvent (fun g (p : P g) => p.val)
        (fun key g => physicalFullSharedIndices (ell := ell) (C key g)) B
        (fun key _ => PhysicalAuxLabels P (C key))
        (fun key => physicalFullEdgeDelta (C key) (k key * (physicalSharedProduct (d key) : ℕ)))
        (fun key => physicalFullEdgeD (C key)))
      (fullPermutationMixedEventTarget (fun g (p : P g) => p.val)
        (fun key g => physicalFullSharedIndices (ell := ell) (C key g)) B
        (fun key _ => PhysicalAuxLabels P (C key))
        (fun key => physicalFullEdgeDelta (C key) (k key * (physicalSharedProduct (d key) : ℕ)))
        (fun key => physicalFullEdgeD (C key)))
      phase steps x (physicalMixedEffectiveBigPathEquiv hPs hP hdis C d k B steps x p) =
    finiteEventLocalPhase
      (FullPermutationMixedEvent (fun g (p : P g) => p.val)
        (fun key g => physicalFullSharedIndices (ell := ell) (C key g)) B
        (fun key _ => PhysicalAuxLabels P (C key))
        (fun key => physicalMixedEdgeDelta (C key) (k key) (d key))
        (fun key => physicalMixedEdgeD (C key) (d key)))
      (fullPermutationMixedEventTarget (fun g (p : P g) => p.val)
        (fun key g => physicalFullSharedIndices (ell := ell) (C key g)) B
        (fun key _ => PhysicalAuxLabels P (C key))
        (fun key => physicalMixedEdgeDelta (C key) (k key) (d key))
        (fun key => physicalMixedEdgeD (C key) (d key)))
      (fun tag x e => phase tag x
        (physicalMixedEffectiveBigEventEquiv hPs hP hdis C d k B tag x e)) steps x p := by
  unfold physicalMixedEffectiveBigPathEquiv physicalMixedEffectiveBigEventEquiv
  exact finite_event_local_phase_equiv _ _ _ _ id _ _ _ _ (fun _ _ _ => rfl) steps x p

end Effective
end Bounty

end


-- Source module: PhysicalMixedEffectiveLocalAction
section

/- Exact transport of the original planned action, retaining its small factor
and an arbitrary effective local phase at every event. -/

open scoped Classical
namespace Bounty

theorem physical_mixed_effective_local_action
    {S I V K : Type} [Fintype S] {N J ell : ℕ}
    {Ps : S → Finset ℕ} {P : Fin N → Finset ℕ}
    [∀ g, ∀ p : P g, NeZero p.val]
    (hPs : ∀ s p, p ∈ Ps s → Nat.Prime p)
    (hP : ∀ g p, p ∈ P g → Nat.Prime p)
    (hdis : ∀ s g, Disjoint (Ps s) (P g))
    (C : I → Fin N → Finset (Fin J)) (k : K → I → ℤ) (B : ℕ)
    (ω : ∀ i, SharedActiveLabels (fun g => P g)
      (fun g => physicalFullSharedIndices (ell := ell) (C i g)) →
        PhysicalAuxLabels P (C i) → ℝ)
    (μ : ∀ g, P g → ℝ) (q : V → ℝ) (ρ : ℝ) (Vb : Fin N → ℝ)
    (Vs : S → ℝ) (qedge : K → ℝ)
    (ks : List (Option (V ⊕ K))) (r : PhysicalResidues Ps)
    (L : PhysicalMarkLists Ps J ell)
    (pl : PhysicalMixedSmallPlan (Ps := Ps) (J := J) (ell := ell) (I := I) ks) :
    let Cb := fun z : PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell)
      (I := I) (K := K) => C z.2.1
    let db := fun z : PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell)
      (I := I) (K := K) => physicalSharedPrefix z.2.2.1
    let kb := fun z : PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell)
      (I := I) (K := K) => k z.1 z.2.1
    let steps := physicalMixedBigSteps ks L pl
    ∀ (phase : ∀ (tag : Option (V ⊕ PhysicalMixedBigKey (Ps := Ps) (J := J)
          (ell := ell) (I := I) (K := K))),
        (x : PhysicalFullBoundedState P J ell B) →
        FullPermutationMixedEvent (fun g (p : P g) => p.val)
          (fun z g => physicalFullSharedIndices (ell := ell) (Cb z g)) B
          (fun z _ => PhysicalAuxLabels P (Cb z))
          (fun z => physicalFullEdgeDelta (Cb z) (kb z * (physicalSharedProduct (db z) : ℕ)))
          (fun z => physicalFullEdgeD (Cb z)) tag x → ℂ)
      (f : PhysicalFullBoundedState P J ell B → ℂ),
    physicalMixedPlannedBigAction (fun g (p : P g) => p.val)
      (fun i g => physicalFullSharedIndices (ell := ell) (C i g)) B
      (fun i => PhysicalAuxLabels P (C i))
      (fun t i => physicalMixedEdgeDelta (C i) (k t i))
      (fun _ i => physicalMixedEdgeD (C i)) ω μ q ρ Vb ks L pl
      (fun x p =>
        (physicalMixedPlanSmallFactor (fun g (p : P g) => p.val)
          (fun i g => physicalFullSharedIndices (ell := ell) (C i g)) B
          (fun i => PhysicalAuxLabels P (C i))
          (fun t i => physicalMixedEdgeDelta (C i) (k t i))
          (fun _ i => physicalMixedEdgeD (C i))
          (fun t i => physicalMixedBigStep (C i) (k t i)) Vs qedge ks r L pl x p : ℂ) *
        finiteEventLocalPhase
          (FullPermutationMixedEvent (fun g (p : P g) => p.val)
            (fun z g => physicalFullSharedIndices (ell := ell) (Cb z g)) B
            (fun z _ => PhysicalAuxLabels P (Cb z))
            (fun z => physicalMixedEdgeDelta (Cb z) (kb z) (db z))
            (fun z => physicalMixedEdgeD (Cb z) (db z)))
          (fullPermutationMixedEventTarget (fun g (p : P g) => p.val)
            (fun z g => physicalFullSharedIndices (ell := ell) (Cb z g)) B
            (fun z _ => PhysicalAuxLabels P (Cb z))
            (fun z => physicalMixedEdgeDelta (Cb z) (kb z) (db z))
            (fun z => physicalMixedEdgeD (Cb z) (db z)))
          (fun tag x e => phase tag x
            (physicalMixedEffectiveBigEventEquiv hPs hP hdis Cb db kb B tag x e))
          steps x p) f =
    fullPermutationMixedPathAction (fun g (p : P g) => p.val)
      (fun z g => physicalFullSharedIndices (ell := ell) (Cb z g)) B
      (fun z _ => PhysicalAuxLabels P (Cb z))
      (fun z => physicalFullEdgeDelta (Cb z) (kb z * (physicalSharedProduct (db z) : ℕ)))
      (fun z => physicalFullEdgeD (Cb z)) (fun z => ω z.2.1) μ q ρ Vb steps
      (fun x p => physicalEffectivePlanSmallFactor C k B Vs qedge ks r L pl x p *
        finiteEventLocalPhase
          (FullPermutationMixedEvent (fun g (p : P g) => p.val)
            (fun z g => physicalFullSharedIndices (ell := ell) (Cb z g)) B
            (fun z _ => PhysicalAuxLabels P (Cb z))
            (fun z => physicalFullEdgeDelta (Cb z) (kb z * (physicalSharedProduct (db z) : ℕ)))
            (fun z => physicalFullEdgeD (Cb z)))
          (fullPermutationMixedEventTarget (fun g (p : P g) => p.val)
            (fun z g => physicalFullSharedIndices (ell := ell) (Cb z g)) B
            (fun z _ => PhysicalAuxLabels P (Cb z))
            (fun z => physicalFullEdgeDelta (Cb z) (kb z * (physicalSharedProduct (db z) : ℕ)))
            (fun z => physicalFullEdgeD (Cb z)))
          phase steps x p) f := by
  intro Cb db kb steps phase f
  refine (physical_mixed_planned_effective_action hPs hP hdis C k B
    ω μ q ρ Vb ks L pl _ f).trans ?_
  apply congrArg (fun phase' =>
    fullPermutationMixedPathAction (fun g (p : P g) => p.val)
      (fun z g => physicalFullSharedIndices (ell := ell) (Cb z g)) B
      (fun z _ => PhysicalAuxLabels P (Cb z))
      (fun z => physicalFullEdgeDelta (Cb z) (kb z * (physicalSharedProduct (db z) : ℕ)))
      (fun z => physicalFullEdgeD (Cb z)) (fun z => ω z.2.1) μ q ρ Vb steps phase' f)
  funext x p
  rw [physical_mixed_plan_small_factor_effective_pullback C k B hPs hP hdis]
  congr 1
  have h := physical_mixed_effective_big_local_phase hPs hP hdis Cb db kb B
    phase steps x ((physicalMixedEffectiveBigPathEquiv hPs hP hdis Cb db kb B steps x).symm p)
  simpa only [Equiv.apply_symm_apply] using h.symm

end Bounty

end


-- Source module: PhysicalRootFourierComposition
section

/- The original root forest is an integral of the actual mixed operator
word, with its exact initial boundary multiplier and original coefficients. -/

open Finset MeasureTheory
open scoped Classical
namespace Bounty
section Root
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


variable (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ)
    (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) → ℝ)

theorem physical_root_fourier_planned_eq_effective
    (pl : PhysicalRootSmallPlan (P := P) (J := J) (ell := ell) (n := n) groups patterns)
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B) :
    physicalRootFourierPlannedAction groups e patterns C hC k V q ζ K r θ β retention ρ hPs hPb hdis
      code encode ν pl f x =
    physicalRootEffectiveFourierAction groups e patterns C hC k pl V q ζ K r θ β retention ρ
      code encode ν f x := by
  let _ : ∀ g (z : P (e.symm g).val), NeZero z.val :=
    fun g z => inferInstanceAs (NeZero (⟨(e.symm g).val, z⟩ : PhysicalPrime P).2.val)
  have h := physical_mixed_effective_local_action hPs hPb hdis
    (fun (i : patterns) g => C i.val (e.symm g).val)
    (fun (j : Fin (n + 1)) (i : patterns) => k (n - j.val) i.val) B
    (fun (i : patterns) _ a => physicalAuxMass (fun g => V (e.symm g).val)
      (fun g => C i.val (e.symm g).val) a)
    (fun g p => β g p / V (e.symm g).val) retention ρ (fun g => V (e.symm g).val)
    (fun s : ↥groupsᶜ => V s.val) (fun _ => q) ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
    (physicalGroupResidueVector r) pl.1 pl.2
    (physicalRootEffectiveFourierPhase groups e patterns C hC k V ζ K θ β ρ code encode ν) f
  exact congrFun h x

theorem physical_root_mixed_fourier_word
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (L : PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B) :
    physicalRootMixedFourierIntegrand groups e patterns C hC k V q ζ K r θ β retention ρ
      code encode ν f L x =
    fullMixedCommonBoundaryMultiplier (fun _ : Fin M => J + ell) B
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) code ν encode (fullMixedCommonInitialPrime x) *
      physicalRootFourierWord groups e patterns C hC k V q ζ K r θ β retention ρ hPs hPb hdis
        code encode ν f L x := by
  let _ := physicalMixedSmallPlanFintype (Ps := (fun s : ↥groupsᶜ => P s.val))
    (J := J) (ell := ell) (I := patterns) ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
  unfold physicalRootMixedFourierIntegrand
  rw [physical_root_fourier_word_eq_plans, mul_sum]
  apply sum_congr rfl
  intro sp _
  rw [physical_root_plan_fourier_action, physical_root_fourier_planned_eq_effective]

theorem physical_root_forest_eq_integral_word
    (hinj : Function.Injective encode)
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (L : PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B) :
    physicalRootMixedForestAction groups e patterns C hC k V q ζ K r θ β retention ρ code f L x =
      ∫ ν, fullMixedCommonBoundaryMultiplier (fun _ : Fin M => J + ell) B
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) code ν encode (fullMixedCommonInitialPrime x) *
        physicalRootFourierWord groups e patterns C hC k V q ζ K r θ β retention ρ hPs hPb hdis
          code encode ν f L x ∂birthFourierCubeMeasure (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) := by
  rw [physical_root_mixed_forest_fourier groups e patterns C hC k V q ζ K r θ β retention ρ
    code encode hinj f L x]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with ν
  exact physical_root_mixed_fourier_word groups e patterns C hC k V q ζ K r θ β retention ρ
    hPs hPb hdis code encode ν f L x

end Root
end Bounty

end


-- Source module: PhysicalRootFourierVectorSupport
section

/- The actual local root Fourier word is the exact sum over its original
planned big actions, with every small factor and coefficient retained. -/

open Finset
open scoped Classical
namespace Bounty
section Root
variable {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
  [∀ z : PhysicalPrime P, NeZero z.2.val]
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
  (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
  (k : ℕ → I → ℤ)

  (V : Fin N → ℝ) (q : ℝ) (ζ : ℕ → I → ℝ)
  (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
    PhysicalAuxLabels P (C i) → ℂ)
  (θ : ℝ)
  (β : (g : Fin M) → P (e.symm g).val → ℝ)
  (retention : Fin (n + 2) → ℝ) (ρ : ℝ)

  (hPs : ∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p)
  (hPb : ∀ (g : Fin M) p, p ∈ P (e.symm g).val → Nat.Prime p)
  (hdis : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (e.symm g).val))


variable (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ)
    (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) → ℝ)

theorem physical_root_fourier_vector_invalid
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (r : PhysicalResidues (fun s : ↥groupsᶜ => P s.val))
    (L : PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B)
    (h : ¬ physicalResidueMarksValid r L) :
    physicalRootFourierVectorAction groups e patterns C hC k V q ζ K θ β retention ρ
      hPs hPb hdis code encode ν f ((r, L), x) = 0 := by
  have hv : physicalGroupResidueVector ((physicalGroupResidueVectorEquiv P groupsᶜ).symm r) = r :=
      (physicalGroupResidueVectorEquiv P groupsᶜ).apply_symm_apply r
  have hz := physical_root_fourier_word_invalid groups e patterns C hC k V q ζ K
    ((physicalGroupResidueVectorEquiv P groupsᶜ).symm r) θ β retention ρ
    hPs hPb hdis code encode ν f L x (by simpa only [hv] using h)
  rw [physical_root_fourier_word_rows, hv] at hz
  exact hz

include hPs hPb hdis in
theorem physical_root_mixed_forest_invalid
    (hinj : Function.Injective encode)
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (r : PhysicalGroupResidues P groupsᶜ)
    (L : PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B)
    (h : ¬ physicalResidueMarksValid (physicalGroupResidueVector r) L) :
    physicalRootMixedForestAction groups e patterns C hC k V q ζ K r θ β retention ρ
      code f L x = 0 := by
  rw [physical_root_forest_eq_integral_word groups e patterns C hC k V q ζ K r θ β retention ρ
    hPs hPb hdis code encode hinj f L x]
  simp only [physical_root_fourier_word_invalid groups e patterns C hC k V q ζ K r θ β retention ρ
    hPs hPb hdis code encode _ f L x h, mul_zero, MeasureTheory.integral_zero]

end Root
end Bounty

end


-- Source module: PhysicalRootInitialScalar
section

/- The original weighted scalar, including the full small-residue average,
is a normalized initial readout whenever the integrand has its true support. -/

open Finset
open scoped Classical
namespace Bounty
section Scalar
variable {N M J ell B : ℕ} {P : Fin N → Finset ℕ}
  [∀ z : PhysicalPrime P, NeZero z.2.val]
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  (V : Fin N → ℝ) (β : (g : Fin M) → P (e.symm g).val → ℝ)

noncomputable def physicalRootInitialScalar
    (F : PhysicalGroupResidues P groupsᶜ →
      PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell →
      PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ) : ℂ :=
  ∑ r : PhysicalGroupResidues P groupsᶜ,
    ((∏ a : ↥(physicalPrimeGroups P groupsᶜ), 1 / (a.val.2.val : ℝ) : ℝ) : ℂ) *
      ((physicalStateMass (fun s : ↥groupsᶜ => V s.val) J ell : ℂ) *
        ∑ Ls : PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell,
          ∑ Lb : PhysicalMarkLists (fun g => P (e.symm g).val) J ell,
            ((∏ g, ∏ i : PhysicalSlots J ell, β g (Lb g i) / V (e.symm g).val : ℝ) : ℂ) *
              F r Ls (physicalFullMemoryState (fun _ : Fin M => ∅) Lb
                (fun g => fullEmptyBoundedMemory
                  (UnrestrictedResidueParticle (fun z : P (e.symm g).val => z.val)) B)))

variable [∀ z : PhysicalPrime (fun s : ↥groupsᶜ => P s.val), NeZero z.2.val]

theorem physical_root_initial_scalar_eq_readout
    (boundary : PhysicalBareResidueState (fun s : ↥groupsᶜ => P s.val) J ell →
      PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (F : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e → ℂ)
    (hF : ∀ r L x, ¬ physicalResidueMarksValid r L → F ((r, L), x) = 0) :
    physicalRootInitialScalar groups e V β
      (fun r L x => boundary (physicalGroupResidueVector r, L) x *
        F ((physicalGroupResidueVector r, L), x)) =
      physicalSmallBigInitialReadout (fun s : ↥groupsᶜ => V s.val) (fun _ : Fin M => ∅)
        (fun g p => β g p / V (e.symm g).val)
        (fun g => fullEmptyBoundedMemory
          (UnrestrictedResidueParticle (fun z : P (e.symm g).val => z.val)) B)
        boundary F := by
  let ψ : PhysicalResidues (fun s : ↥groupsᶜ => P s.val) → ℂ := fun r =>
    (physicalStateMass (fun s : ↥groupsᶜ => V s.val) J ell : ℂ) *
      ∑ Ls : PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell,
        ∑ Lb : PhysicalMarkLists (fun g => P (e.symm g).val) J ell,
          ((∏ g, ∏ i : PhysicalSlots J ell, β g (Lb g i) / V (e.symm g).val : ℝ) : ℂ) *
            (boundary (r, Ls) (physicalFullMemoryState (fun _ : Fin M => ∅) Lb
              (fun g => fullEmptyBoundedMemory
                (UnrestrictedResidueParticle (fun z : P (e.symm g).val => z.val)) B)) *
              F ((r, Ls), physicalFullMemoryState (fun _ : Fin M => ∅) Lb
                (fun g => fullEmptyBoundedMemory
                  (UnrestrictedResidueParticle (fun z : P (e.symm g).val => z.val)) B)))
  calc
    _ = ∑ r : PhysicalResidues (fun s : ↥groupsᶜ => P s.val),
        ((∏ p : PhysicalPrime (fun s : ↥groupsᶜ => P s.val),
          1 / (p.2.val : ℝ) : ℝ) : ℂ) * ψ r :=
      physical_group_residue_weighted_sum P groupsᶜ ψ
    _ = _ := by
      rw [physical_small_big_initial_readout_eq_raw _ _ _ _ _ _ hF]
      dsimp only [ψ]
      conv_rhs => rw [mul_sum]
      apply sum_congr rfl
      intro r _
      exact mul_left_comm _ _ _

end Scalar
end Bounty

end


-- Source module: PhysicalRootInitialIntegral
section

/- The original weighted scalar, including the full small-residue average,
is a normalized initial readout whenever the integrand has its true support. -/

open Finset MeasureTheory
open scoped Classical
namespace Bounty
section Scalar
variable {N M J ell B : ℕ} {P : Fin N → Finset ℕ}
  [∀ z : PhysicalPrime P, NeZero z.2.val]
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  (V : Fin N → ℝ) (β : (g : Fin M) → P (e.symm g).val → ℝ)

theorem physical_root_initial_scalar_integral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : Ω → PhysicalGroupResidues P groupsᶜ →
      PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell →
      PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (hF : ∀ r L x, Integrable (fun ω => F ω r L x) μ) :
    (∫ ω, physicalRootInitialScalar groups e V β (F ω) ∂μ) =
      physicalRootInitialScalar groups e V β (fun r L x => ∫ ω, F ω r L x ∂μ) := by
  unfold physicalRootInitialScalar
  rw [integral_finsetSum]
  · apply sum_congr rfl
    intro r _
    rw [integral_const_mul, integral_const_mul, integral_finsetSum]
    · congr 2
      apply sum_congr rfl
      intro Ls _
      rw [integral_finsetSum]
      · apply sum_congr rfl
        intro Lb _
        exact integral_const_mul _ _
      · intro Lb _
        exact (hF r Ls _).const_mul _
    · intro Ls _
      exact integrable_finsetSum _ (fun Lb _ => (hF r Ls _).const_mul _)
  · intro r _
    exact (integrable_finsetSum _ (fun Ls _ =>
      integrable_finsetSum _ (fun Lb _ => (hF r Ls _).const_mul _))).const_mul _ |>.const_mul _

end Scalar
end Bounty

end


-- Source module: PhysicalRootMixedIntegrable
section

/- The original root forest action places its complete small-plan sum
inside the common Fourier integral. -/

open Finset MeasureTheory
open scoped Classical
namespace Bounty
section Root
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


theorem physical_root_mixed_fourier_integrable
    (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ)
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (L : PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B) :
    Integrable (fun ν => physicalRootMixedFourierIntegrand groups e patterns C hC k V q ζ K r θ β retention ρ
      code encode ν f L x) (birthFourierCubeMeasure (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))))) := by
  let _ := physicalMixedSmallPlanFintype (Ps := (fun s : ↥groupsᶜ => P s.val))
    (J := J) (ell := ell) (I := patterns) ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
  unfold physicalRootMixedFourierIntegrand
  apply integrable_finsetSum
  intro sp _
  exact physical_root_plan_fourier_integrable groups e patterns C hC k (L, sp) V q ζ K r θ β retention ρ
    code encode f x

end Root
end Bounty

end


-- Source module: PhysicalRootWordIntegrable
section

/- The original root forest is an integral of the actual mixed operator
word, with its exact initial boundary multiplier and original coefficients. -/

open Finset MeasureTheory
open scoped Classical
namespace Bounty
section Root
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


variable (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ)
    (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) → ℝ)

theorem physical_root_fourier_word_integrable
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (L : PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B) :
    Integrable (fun ν => fullMixedCommonBoundaryMultiplier (fun _ : Fin M => J + ell) B
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) code ν encode
      (fullMixedCommonInitialPrime x) *
      physicalRootFourierWord groups e patterns C hC k V q ζ K r θ β retention ρ hPs hPb hdis
        code encode ν f L x) (birthFourierCubeMeasure (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))))) := by
  have h := physical_root_mixed_fourier_integrable groups e patterns C hC k V q ζ K r θ β retention ρ
    code encode f L x
  exact h.congr (Filter.Eventually.of_forall fun ν =>
    physical_root_mixed_fourier_word groups e patterns C hC k V q ζ K r θ β retention ρ
      hPs hPb hdis code encode ν f L x)

end Root
end Bounty

end


-- Source module: PhysicalRootForestContribution
section

/- The actual local root Fourier word is the exact sum over its original
planned big actions, with every small factor and coefficient retained. -/

open Finset MeasureTheory
open scoped Classical
namespace Bounty
section Root
variable {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
  [∀ z : PhysicalPrime P, NeZero z.2.val]
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
  (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
  (k : ℕ → I → ℤ)

  (V : Fin N → ℝ) (q : ℝ) (ζ : ℕ → I → ℝ)
  (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
    PhysicalAuxLabels P (C i) → ℂ)
  (θ : ℝ)
  (β : (g : Fin M) → P (e.symm g).val → ℝ)
  (retention : Fin (n + 2) → ℝ) (ρ : ℝ)

  (hPs : ∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p)
  (hPb : ∀ (g : Fin M) p, p ∈ P (e.symm g).val → Nat.Prime p)
  (hdis : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (e.symm g).val))


variable (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ)
    (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) → ℝ)

noncomputable def physicalRootForestContribution : ℂ :=
  physicalRootInitialScalar groups e V β
    (fun r L x => physicalRootMixedForestAction groups e patterns C hC k V q ζ K r θ β retention ρ
      code fullMemoryVacuum L x)

noncomputable def physicalRootFourierContribution : ℂ :=
  physicalRootInitialScalar groups e V β
    (fun r L x => physicalRootFourierBoundary groups e code encode ν x *
      physicalRootFourierWord groups e patterns C hC k V q ζ K r θ β retention ρ hPs hPb hdis
        code encode ν fullMemoryVacuum L x)

theorem physical_root_forest_contribution_integral
    (hinj : Function.Injective encode) :
    physicalRootForestContribution groups e patterns C hC k V q ζ K θ β retention ρ code =
      ∫ ν, physicalRootFourierContribution groups e patterns C hC k V q ζ K θ β retention ρ
        hPs hPb hdis code encode ν ∂birthFourierCubeMeasure
          (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
            ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
          Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
            ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) := by
  unfold physicalRootForestContribution physicalRootFourierContribution
  rw [physical_root_initial_scalar_integral]
  · congr 1
    funext r L x
    exact physical_root_forest_eq_integral_word groups e patterns C hC k V q ζ K r θ β retention ρ
      hPs hPb hdis code encode hinj fullMemoryVacuum L x
  · intro r L x
    exact physical_root_fourier_word_integrable groups e patterns C hC k V q ζ K r θ β retention ρ
      hPs hPb hdis code encode fullMemoryVacuum L x

variable [∀ z : PhysicalPrime (fun s : ↥groupsᶜ => P s.val), NeZero z.2.val]

theorem physical_root_fourier_contribution_eq_readout :
    physicalRootFourierContribution groups e patterns C hC k V q ζ K θ β retention ρ
      hPs hPb hdis code encode ν =
      physicalRootFourierReadout groups e patterns C hC k V q ζ K θ β retention ρ
        hPs hPb hdis code encode ν := by
  exact physical_root_initial_scalar_eq_readout groups e V β
    (fun _ => physicalRootFourierBoundary groups e code encode ν)
    (physicalRootFourierVectorAction groups e patterns C hC k V q ζ K θ β retention ρ
      hPs hPb hdis code encode ν fullMemoryVacuum)
      (physical_root_fourier_vector_invalid groups e patterns C hC k V q ζ K θ β retention ρ
        hPs hPb hdis code encode ν fullMemoryVacuum)

theorem physical_root_forest_contribution_norm_le
    (hinj : Function.Injective encode)
    {bound : ℝ} (hbound : ∀ ν,
      ‖physicalRootFourierReadout groups e patterns C hC k V q ζ K θ β retention ρ
        hPs hPb hdis code encode ν‖ ≤ bound) :
    ‖physicalRootForestContribution groups e patterns C hC k V q ζ K θ β retention ρ code‖ ≤ bound := by
  let _ : IsProbabilityMeasure (birthFourierCubeMeasure
    (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
    Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))))) :=
    birthFourierCubeMeasure_probability _
  rw [physical_root_forest_contribution_integral groups e patterns C hC k V q ζ K θ β retention ρ
    hPs hPb hdis code encode hinj]
  simpa using norm_integral_le_of_norm_le_const
    (μ := birthFourierCubeMeasure
      (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))))
    (Filter.Eventually.of_forall fun ν =>
    (congrArg norm (physical_root_fourier_contribution_eq_readout groups e patterns C hC k V q ζ K
      θ β retention ρ hPs hPb hdis code encode ν)).trans_le (hbound ν))

end Root
end Bounty

end


-- Source module: PhysicalRootInitialLinear
section

/- The original weighted scalar, including the full small-residue average,
is a normalized initial readout whenever the integrand has its true support. -/

open Finset
open scoped Classical
namespace Bounty
section Scalar
variable {N M J ell B : ℕ} {P : Fin N → Finset ℕ}
  [∀ z : PhysicalPrime P, NeZero z.2.val]
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  (V : Fin N → ℝ) (β : (g : Fin M) → P (e.symm g).val → ℝ)

theorem physical_root_initial_scalar_add
    (F G : PhysicalGroupResidues P groupsᶜ →
      PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell →
      PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ) :
    physicalRootInitialScalar groups e V β (fun r L x => F r L x + G r L x) =
      physicalRootInitialScalar groups e V β F + physicalRootInitialScalar groups e V β G := by
  simp only [physicalRootInitialScalar, mul_add, sum_add_distrib]

theorem physical_root_initial_scalar_const_mul (c : ℂ)
    (F : PhysicalGroupResidues P groupsᶜ →
      PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell →
      PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ) :
    physicalRootInitialScalar groups e V β (fun r L x => c * F r L x) =
      c * physicalRootInitialScalar groups e V β F := by
  have hm (a b : ℂ) : a * (c * b) = c * (a * b) := mul_left_comm a c b
  simp only [physicalRootInitialScalar, hm, ← mul_sum]

theorem physical_root_initial_scalar_finset_sum
    {T : Type*} (s : Finset T)
    (F : T → PhysicalGroupResidues P groupsᶜ →
      PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell →
      PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ) :
    physicalRootInitialScalar groups e V β (fun r L x => ∑ t ∈ s, F t r L x) =
      ∑ t ∈ s, physicalRootInitialScalar groups e V β (F t) := by
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty, physicalRootInitialScalar, mul_zero, sum_const_zero]
  | @insert t s ht ih =>
    simp only [sum_insert ht]
    rw [physical_root_initial_scalar_add, ih]

theorem physical_root_initial_scalar_weighted_sum
    {T : Type*} [Fintype T] (a : T → ℂ)
    (F : T → PhysicalGroupResidues P groupsᶜ →
      PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell →
      PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ) :
    physicalRootInitialScalar groups e V β (fun r L x => ∑ t, a t * F t r L x) =
      ∑ t, a t * physicalRootInitialScalar groups e V β (F t) := by
  rw [physical_root_initial_scalar_finset_sum]
  apply sum_congr rfl
  intro t _
  exact physical_root_initial_scalar_const_mul groups e V β (a t) (F t)

end Scalar
end Bounty

end


-- Source module: PhysicalRootOriginalForestSum
section

/- The literal original root scalar, including initial mark weights, is a signed common-forest sum. -/

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

theorem physical_root_original_scalar_forest_sum
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ) (hinj : Function.Injective encode) :
    (∑ r : PhysicalGroupResidues P groupsᶜ,
      ((∏ a : ↥(physicalPrimeGroups P groupsᶜ), 1 / (a.val.2.val : ℝ) : ℝ) : ℂ) *
        physicalRootMixedScalar (n := n) (B := B)
          groups e patterns C hC V q ζ k K r θ β ρ hP hdis) =
      ∑ code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B),
        (-1 : ℂ) ^ birthForestRank code *
          physicalRootForestContribution groups e patterns C hC k V q ζ K θ
            (fun (g : Fin M) (z : P (e.symm g).val) => β ⟨(e.symm g).val, z⟩)
            (fun j => physicalEndpointSchedule q (n + 1) j.val) ρ code := by
  calc
    _ = ∑ r : PhysicalGroupResidues P groupsᶜ,
        ((∏ a : ↥(physicalPrimeGroups P groupsᶜ), 1 / (a.val.2.val : ℝ) : ℝ) : ℂ) *
          physicalRootForestScalar (n := n) (B := B)
            groups e patterns C hC V q ζ k K r θ β ρ := by
      apply sum_congr rfl
      intro r _
      rw [physical_root_mixed_scalar_forests groups e patterns C hC V q ζ k K r θ β ρ hP hdis encode hinj]
    _ = _ := by
      exact physical_root_initial_scalar_weighted_sum groups e V
        (fun (g : Fin M) (z : P (e.symm g).val) => β ⟨(e.symm g).val, z⟩)
        (fun code => (-1 : ℂ) ^ birthForestRank code)
        (fun code r L x => physicalRootMixedForestAction groups e patterns C hC k V q ζ K r θ
          (fun (g : Fin M) (z : P (e.symm g).val) => β ⟨(e.symm g).val, z⟩)
          (fun j => physicalEndpointSchedule q (n + 1) j.val) ρ code fullMemoryVacuum L x)

end Scalar
end Bounty

end


-- Source module: PhysicalRootTwoRegime
section

/- The two rank regimes bound the actual original averaged root scalar,
with a threshold uniform over all finite root data satisfying the budgets. -/

open Finset Filter
open scoped Classical
namespace Bounty

theorem eventually_physical_root_scalar_two_regime
    {a c budget E G Cv Ca dimension Ch : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hbudget : 0 ≤ budget) (hE : 0 ≤ E)
    (hdimension : 0 ≤ dimension) (hD : 0 ≤ G + Ca + dimension)
    (hgain : E + Cv + 2 ≤ G) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (I : Type) (N M J ell n B : ℕ) (P : Fin N → Finset ℕ)
      [∀ z : PhysicalPrime P, NeZero z.2.val]
      (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
      (V : Fin N → ℝ) (patterns : Finset I)
      (cuts : I → Fin N → Finset (Fin J))
      (hcuts : ∀ i : patterns, ∀ g : ↥groupsᶜ, cuts i.val g.val = ∅)
      (q : ℝ) (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ)
      (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
        PhysicalAuxLabels P (cuts i) → ℂ)
      (θ : ℝ) (beta : PhysicalPrime P → ℝ) (ρ : ℝ)
      (hP : ∀ g p, p ∈ P g → Nat.Prime p)
      (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))
      (encode : ((g : Fin M) × P (e.symm g).val) → ℤ)
      (_hinj : Function.Injective encode),
      let m := Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))
      let F : BirthForestCode m → ℂ := fun code =>
        physicalRootForestContribution groups e patterns cuts hcuts k V q ζ K θ
          (fun (g : Fin M) (p : P (e.symm g).val) => beta ⟨(e.symm g).val, p⟩)
          (fun j => physicalEndpointSchedule q (n + 1) j.val) ρ code
      L ^ a ≤ ((n + 1 : ℕ) : ℝ) →
      ∀ b H A ε : ℝ, L ^ c ≤ b → (m : ℝ) ≤ L ^ dimension →
        0 ≤ H → H ≤ L ^ Ch → 0 ≤ A → A ≤ L ^ (budget * (((n + 1 : ℕ) : ℝ) + 1)) →
        0 ≤ ε → (m : ℝ) ^ 2 * ε ≤ Real.exp (-b) →
        let cutoff := Nat.ceil (((2 * budget + (E + 1) + 1) * ((n + 1 : ℕ) : ℝ) * Real.log L) / b)
        (∀ code, birthForestRank code < cutoff →
          ‖F code‖ ≤ H * L ^ ((-G + Cv) * ((n + 1 : ℕ) : ℝ) + Cv +
            2 * birthForestRank code * (G + Ca))) →
        (∀ code, cutoff ≤ birthForestRank code → ‖F code‖ ≤ A * ε ^ birthForestRank code) →
        ‖∑ r : PhysicalGroupResidues P groupsᶜ,
          ((∏ p : ↥(physicalPrimeGroups P groupsᶜ), 1 / (p.val.2.val : ℝ) : ℝ) : ℂ) *
            physicalRootMixedScalar (n := n) (B := B)
              groups e patterns cuts hcuts V q ζ k K r θ beta ρ hP hdis‖ ≤
          L ^ (-(E * ((n + 1 : ℕ) : ℝ))) := by
  filter_upwards [eventually_birthForest_two_regime_power_saving
    ha hc hbudget hE hdimension hD hgain] with L hL
  intro I N M J ell n B P inst groups e V patterns cuts hcuts q ζ k K θ beta ρ hP hdis encode hinj
    m F hN b H A ε hb hm hH hHb hA hAb hε hεb cutoff hlow hhigh
  have hbound := hL (n + 1) m hN b H A ε hb hm hH hHb hA hAb hε hεb F hlow hhigh
  rw [physical_root_original_scalar_forest_sum groups e patterns cuts hcuts V q ζ k K θ beta ρ
    hP hdis encode hinj]
  exact hbound

end Bounty

end


-- Source module: PhysicalRootNormalizedIntegral
section

/- Exact commutation of the normalized small-residue sum with interval integration. -/

open Finset MeasureTheory
open scoped Classical
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
  (β : PhysicalPrime P → ℝ) (ρ : ℝ)
  (hP : ∀ g a, a ∈ P g → Nat.Prime a)
  (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))

theorem physical_root_normalized_mixed_scalar_integral
    (a c : ℝ)
    (hint : ∀ r : PhysicalGroupResidues P groupsᶜ,
      IntervalIntegrable (fun θ => physicalRootMixedScalar
        (P := P) (J := J) (ell := ell) (n := n) (B := B)
        groups e patterns C hC V q ζ k K r θ β ρ hP hdis) volume a c) :
    (∫ θ in a..c, physicalRootNormalizedMixedScalar
        (P := P) (J := J) (ell := ell) (n := n) (B := B)
        groups e patterns C hC V q ζ k K θ β ρ hP hdis) =
      ∑ r : PhysicalGroupResidues P groupsᶜ,
        ((∏ p : ↥(physicalPrimeGroups P groupsᶜ), 1 / (p.val.2.val : ℝ) : ℝ) : ℂ) *
          ∫ θ in a..c, physicalRootMixedScalar
            (P := P) (J := J) (ell := ell) (n := n) (B := B)
            groups e patterns C hC V q ζ k K r θ β ρ hP hdis := by
  unfold physicalRootNormalizedMixedScalar
  rw [intervalIntegral.integral_finsetSum (fun r _ => (hint r).const_mul _)]
  apply Finset.sum_congr rfl
  intro r _
  exact intervalIntegral.integral_const_mul _ _

end Scalar
end Bounty

end


-- Source module: PhysicalRootScalarRho
section

/- At a saturated memory cap, the original root scalar is independent of
the nonzero auxiliary ghost parameter, also after normalized residue averaging. -/

open Finset
open scoped Classical
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
  (r : PhysicalGroupResidues P groupsᶜ) (θ : ℝ)
  (β : PhysicalPrime P → ℝ) (ρ ρ' : ℝ)
  (hP : ∀ g a, a ∈ P g → Nat.Prime a)
  (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))

theorem physical_root_mixed_scalar_rho_eq
    (hk : ∀ t < n + 1, ∀ i ∈ patterns, ∀ g a, a ∈ P g → ¬ (a : ℤ) ∣ k t i)
    (hV : ∀ g, V g ≠ 0) (hρ : ρ ≠ 0) (hρ' : ρ' ≠ 0)
    (hB : (physicalPrimeGroups P groups).card ≤ B) (hq : 0 ≤ q) :
    physicalRootMixedScalar (n := n) (B := B)
        groups e patterns C hC V q ζ k K r θ β ρ hP hdis =
      physicalRootMixedScalar (n := n) (B := B)
        groups e patterns C hC V q ζ k K r θ β ρ' hP hdis := by
  exact (physical_root_small_plan_eq_mixed_scalar (n := n) (B := B)
    groups e patterns C hC V q ζ k K r θ β ρ hP hdis hk hV hρ hB hq).symm.trans
    (physical_root_small_plan_eq_mixed_scalar (n := n) (B := B)
      groups e patterns C hC V q ζ k K r θ β ρ' hP hdis hk hV hρ' hB hq)

theorem physical_root_normalized_mixed_scalar_rho_eq
    (hk : ∀ t < n + 1, ∀ i ∈ patterns, ∀ g a, a ∈ P g → ¬ (a : ℤ) ∣ k t i)
    (hV : ∀ g, V g ≠ 0) (hρ : ρ ≠ 0) (hρ' : ρ' ≠ 0)
    (hB : (physicalPrimeGroups P groups).card ≤ B) (hq : 0 ≤ q) :
    physicalRootNormalizedMixedScalar (n := n) (B := B)
        groups e patterns C hC V q ζ k K θ β ρ hP hdis =
      physicalRootNormalizedMixedScalar (n := n) (B := B)
        groups e patterns C hC V q ζ k K θ β ρ' hP hdis := by
  unfold physicalRootNormalizedMixedScalar
  apply sum_congr rfl
  intro r _
  exact congrArg (fun z : ℂ =>
    ((∏ a : ↥(physicalPrimeGroups P groupsᶜ), 1 / (a.val.2.val : ℝ) : ℝ) : ℂ) * z)
    (physical_root_mixed_scalar_rho_eq groups e patterns C hC V q ζ k K r θ β ρ ρ'
      hP hdis hk hV hρ hρ' hB hq)

end Scalar
end Bounty

end


-- Source module: PhysicalRootThetaRegularity
section

/- Theta regularity for the original mixed root scalar and its exact weighted
small-residue average, obtained from the finite small-plan representation. -/

open Finset MeasureTheory
open scoped Classical
namespace Bounty

section SmallPlan
variable {I : Type} {N J ell n : ℕ} {P : Fin N → Finset ℕ}
  [∀ a : PhysicalPrime P, NeZero a.2.val]
  (groups : Finset (Fin N)) (patterns : Finset I)
  (C : I → Fin N → Finset (Fin J))
  (V : Fin N → ℝ) (q : ℝ) (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ)
  (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
    PhysicalAuxLabels P (C i) → ℂ)
  (β : PhysicalPrime P → ℝ) (B : ℕ) (r : PhysicalGroupResidues P groupsᶜ)

theorem physical_root_mixed_path_integrand_theta_continuous
    (L : PhysicalMarkLists P J ell)
    (p : Fin (n + 1) → PhysicalEdgeLabels P J ell patterns C × PhysicalMarkLists P J ell) :
    Continuous (fun θ : ℝ =>
      physicalRootMixedPathIntegrand groups patterns C V q ζ k K β B r θ L p) := by
  unfold physicalRootMixedPathIntegrand
  exact ((continuous_const.mul
    (physical_memory_fourier_walk_scalar_continuous V patterns C ζ k K
      (finitePathLabels p) (finitePathMarks L p) (n + 1))).mul continuous_const).mul continuous_const

theorem physical_root_small_plan_sum_theta_continuous
    (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅) :
    Continuous (fun θ : ℝ =>
      physicalRootSmallPlanSum (n := n) groups patterns C hC V q ζ k K β B r θ) := by
  unfold physicalRootSmallPlanSum physicalRootSmallPlanSumCore
  apply continuous_finsetSum
  intro x _
  exact physical_root_mixed_path_integrand_theta_continuous
    groups patterns C V q ζ k K β B r _ _
end SmallPlan

section Scalar
variable {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
  [∀ a : PhysicalPrime P, NeZero a.2.val]
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
  (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
  (V : Fin N → ℝ) (q : ℝ) (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ)
  (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
    PhysicalAuxLabels P (C i) → ℂ)
  (β : PhysicalPrime P → ℝ) (ρ : ℝ)
  (hP : ∀ g a, a ∈ P g → Nat.Prime a)
  (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))
  (hk : ∀ t < n + 1, ∀ i ∈ patterns, ∀ g a, a ∈ P g → ¬ (a : ℤ) ∣ k t i)
  (hV : ∀ g, V g ≠ 0) (hρ : ρ ≠ 0)
  (hB : (physicalPrimeGroups P groups).card ≤ B) (hq : 0 ≤ q)

include hk hV hρ hB hq

theorem physical_root_mixed_scalar_theta_continuous
    (r : PhysicalGroupResidues P groupsᶜ) :
    Continuous (fun θ : ℝ => physicalRootMixedScalar (n := n) (B := B)
      groups e patterns C hC V q ζ k K r θ β ρ hP hdis) := by
  apply (physical_root_small_plan_sum_theta_continuous
    groups patterns C V q ζ k K β B r hC).congr
  intro θ
  exact physical_root_small_plan_eq_mixed_scalar
    groups e patterns C hC V q ζ k K r θ β ρ hP hdis hk hV hρ hB hq

theorem physical_root_mixed_scalar_theta_intervalIntegrable
    (r : PhysicalGroupResidues P groupsᶜ) (a b : ℝ) :
    IntervalIntegrable (fun θ : ℝ => physicalRootMixedScalar (n := n) (B := B)
      groups e patterns C hC V q ζ k K r θ β ρ hP hdis) volume a b :=
  (physical_root_mixed_scalar_theta_continuous
    groups e patterns C hC V q ζ k K β ρ hP hdis hk hV hρ hB hq r).intervalIntegrable a b

theorem physical_root_normalized_mixed_scalar_theta_continuous :
    Continuous (fun θ : ℝ => physicalRootNormalizedMixedScalar (n := n) (B := B)
      groups e patterns C hC V q ζ k K θ β ρ hP hdis) := by
  unfold physicalRootNormalizedMixedScalar
  apply continuous_finsetSum
  intro r _
  exact continuous_const.mul (physical_root_mixed_scalar_theta_continuous
    groups e patterns C hC V q ζ k K β ρ hP hdis hk hV hρ hB hq r)

theorem physical_root_normalized_mixed_scalar_theta_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (fun θ : ℝ => physicalRootNormalizedMixedScalar (n := n) (B := B)
      groups e patterns C hC V q ζ k K θ β ρ hP hdis) volume a b :=
  (physical_root_normalized_mixed_scalar_theta_continuous
    groups e patterns C hC V q ζ k K β ρ hP hdis hk hV hρ hB hq).intervalIntegrable a b
end Scalar
end Bounty

end


-- Source module: PhysicalRootNormalizedIntegralFormula
section

/- The original residue model is exactly the baseline product times the integral
of the original normalized root scalar at any nonzero auxiliary ghost parameter. -/

open Finset MeasureTheory
open scoped Classical
namespace Bounty

theorem physical_root_residue_model_normalized_mixed_integral
    {I : Type} {N M J ell n : ℕ} {P : Fin N → Finset ℕ}
    [∀ a : PhysicalPrime P, NeZero a.2.val]
    (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
    (V : Fin N → ℝ) (patterns : Finset I)
    (C : I → Fin N → Finset (Fin J))
    (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
    (q : ℝ) (hq : 0 ≤ q) (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ)
    (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
      PhysicalAuxLabels P (C i) → ℂ)
    (hV : ∀ g, 0 < V g) (hP : ∀ g a, a ∈ P g → Nat.Prime a)
    (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))
    (hk : ∀ t < n + 1, ∀ i ∈ patterns, ∀ g a, a ∈ P g → ¬ (a : ℤ) ∣ k t i)
    (baseline : PhysicalPrime P → ℝ)
    (hb : ∀ a : PhysicalPrime P, a.1 ∈ groups →
      baseline a = 1 - (∑ j ∈ range (n + 2), (1 - physicalEndpointSchedule q (n + 1) j)) / a.2.val)
    (hb0 : ∀ a : PhysicalPrime P, a.1 ∈ groups → baseline a ≠ 0)
    (B : ℕ) (hB : (physicalPrimeGroups P groups).card ≤ B)
    (ρ : ℝ) (hρ : ρ ≠ 0) :
    physicalRootResidueModel V patterns C q ζ k K n =
      (∏ a ∈ physicalPrimeGroups P groups, baseline a : ℝ) *
        ∫ θ : ℝ in (0 : ℝ)..1,
          physicalRootNormalizedMixedScalar
            (P := P) (J := J) (ell := ell) (n := n) (B := B)
            groups e patterns C hC V q ζ k K θ
            (fun a => ((a.2.val : ℝ) * baseline a)⁻¹) ρ hP hdis := by
  refine (physical_root_residue_model_mixed_action
    groups e V patterns C hC q hq ζ k K hV hP hdis hk baseline hb hb0 B hB).trans ?_
  apply congrArg (fun z : ℂ => ((∏ a ∈ physicalPrimeGroups P groups, baseline a : ℝ) : ℂ) * z)
  trans (∫ θ : ℝ in (0 : ℝ)..1,
    physicalRootNormalizedMixedScalar
      (P := P) (J := J) (ell := ell) (n := n) (B := B)
      groups e patterns C hC V q ζ k K θ
      (fun a => ((a.2.val : ℝ) * baseline a)⁻¹) 1 hP hdis)
  · exact (physical_root_normalized_mixed_scalar_integral
      (P := P) (J := J) (ell := ell) (n := n) (B := B)
      groups e patterns C hC V q ζ k K
      (fun a => ((a.2.val : ℝ) * baseline a)⁻¹) 1 hP hdis 0 1
      (fun r => physical_root_mixed_scalar_theta_intervalIntegrable
        (P := P) (J := J) (ell := ell) (n := n) (B := B)
        groups e patterns C hC V q ζ k K
        (fun a => ((a.2.val : ℝ) * baseline a)⁻¹) 1 hP hdis hk
        (fun g => ne_of_gt (hV g)) one_ne_zero hB hq r 0 1)).symm
  · apply congrArg (fun f : ℝ → ℂ => ∫ θ : ℝ in (0 : ℝ)..1, f θ)
    funext θ
    exact physical_root_normalized_mixed_scalar_rho_eq
      (P := P) (J := J) (ell := ell) (n := n) (B := B)
      groups e patterns C hC V q ζ k K θ
      (fun a => ((a.2.val : ℝ) * baseline a)⁻¹) 1 ρ hP hdis hk
      (fun g => ne_of_gt (hV g)) one_ne_zero hρ hB hq

end Bounty

end


-- Source module: PhysicalRootThetaNorm
section

/- The unit theta interval and the endpoint baseline preserve a uniform bound. -/

open Finset MeasureTheory
open scoped Classical
namespace Bounty

theorem physical_root_theta_integral_norm_le
    (F : ℝ → ℂ) (A t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hF : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖F θ‖ ≤ A) :
    ‖(t : ℂ) * ∫ θ : ℝ in (0 : ℝ)..1, F θ‖ ≤ A := by
  calc
    _ = t * ‖∫ θ : ℝ in (0 : ℝ)..1, F θ‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    _ ≤ 1 * ‖∫ θ : ℝ in (0 : ℝ)..1, F θ‖ :=
      mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
    _ = ‖∫ θ : ℝ in (0 : ℝ)..1, F θ‖ := one_mul _
    _ ≤ A := by
      simpa only [sub_zero, abs_one, mul_one] using
        (intervalIntegral.norm_integral_le_of_norm_le_const
          (a := (0 : ℝ)) (b := 1) (fun θ hθ => hF θ (by
            have hθ' : θ ∈ Set.Ioc (0 : ℝ) 1 := by
              simpa only [Set.uIoc_of_le zero_le_one] using hθ
            exact ⟨hθ'.1.le, hθ'.2⟩)))

theorem physical_root_endpoint_baseline_product_bounds
    {N : ℕ} {P : Fin N → Finset ℕ} (groups : Finset (Fin N))
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ)
    (hP : ∀ g a, a ∈ P g → Nat.Prime a)
    (hsize : ∀ a : PhysicalPrime P, a.1 ∈ groups → 2 * (n + 2) ≤ a.2.val) :
    0 < ∏ a ∈ physicalPrimeGroups P groups,
        physicalEndpointBaseline q (n + 1) a.2.val ∧
      (∏ a ∈ physicalPrimeGroups P groups,
        physicalEndpointBaseline q (n + 1) a.2.val) ≤ 1 := by
  classical
  apply memory_baseline_prod_bounds
  intro a ha
  apply physical_endpoint_baseline_bounds hq0 hq1 (n + 1) a.2.val
    (hP a.1 a.2.val a.2.property).pos
  have hag : a.1 ∈ groups := by
    simpa only [physicalPrimeGroups, mem_filter, mem_univ, true_and] using ha
  simpa only [Nat.add_assoc] using hsize a hag

end Bounty

end


-- Source module: PhysicalRootNormalizedIntegralNorm
section

/- A uniform bound on the exact normalized root scalar bounds the residue model. -/

open Finset MeasureTheory
open scoped Classical
namespace Bounty

section Model
variable {I : Type} {N M J ell n : ℕ} {P : Fin N → Finset ℕ}
  [∀ a : PhysicalPrime P, NeZero a.2.val]
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  (V : Fin N → ℝ) (patterns : Finset I)
  (C : I → Fin N → Finset (Fin J))
  (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
  (q : ℝ) (hq : 0 ≤ q) (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ)
  (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
    PhysicalAuxLabels P (C i) → ℂ)
  (hV : ∀ g, 0 < V g) (hP : ∀ g a, a ∈ P g → Nat.Prime a)
  (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))
  (hk : ∀ t < n + 1, ∀ i ∈ patterns, ∀ g a, a ∈ P g → ¬ (a : ℤ) ∣ k t i)
  (baseline : PhysicalPrime P → ℝ)
  (hb : ∀ a : PhysicalPrime P, a.1 ∈ groups →
    baseline a = 1 - (∑ j ∈ range (n + 2), (1 - physicalEndpointSchedule q (n + 1) j)) / a.2.val)
  (B : ℕ) (hB : (physicalPrimeGroups P groups).card ≤ B)
  (ρ : ℝ) (hρ : ρ ≠ 0)

include hq hV hk hb hB hρ

theorem physical_root_residue_model_norm_le_of_normalized_mixed_scalar
    (hb0 : ∀ a : PhysicalPrime P, a.1 ∈ groups → baseline a ≠ 0)
    (hprod0 : 0 ≤ ∏ a ∈ physicalPrimeGroups P groups, baseline a)
    (hprod1 : (∏ a ∈ physicalPrimeGroups P groups, baseline a) ≤ 1)
    (A : ℝ)
    (hscalar : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      ‖physicalRootNormalizedMixedScalar
        (P := P) (J := J) (ell := ell) (n := n) (B := B)
        groups e patterns C hC V q ζ k K θ
        (fun a => ((a.2.val : ℝ) * baseline a)⁻¹) ρ hP hdis‖ ≤ A) :
    ‖physicalRootResidueModel V patterns C q ζ k K n‖ ≤ A := by
  rw [physical_root_residue_model_normalized_mixed_integral
    groups e V patterns C hC q hq ζ k K hV hP hdis hk baseline hb hb0 B hB ρ hρ]
  exact physical_root_theta_integral_norm_le _ A _ hprod0 hprod1 hscalar

theorem physical_root_residue_model_norm_le_of_large_primes
    (hq1 : q ≤ 1)
    (hsize : ∀ a : PhysicalPrime P, a.1 ∈ groups → 2 * (n + 2) ≤ a.2.val)
    (A : ℝ)
    (hscalar : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      ‖physicalRootNormalizedMixedScalar
        (P := P) (J := J) (ell := ell) (n := n) (B := B)
        groups e patterns C hC V q ζ k K θ
        (fun a => ((a.2.val : ℝ) * baseline a)⁻¹) ρ hP hdis‖ ≤ A) :
    ‖physicalRootResidueModel V patterns C q ζ k K n‖ ≤ A := by
  classical
  have hb0 : ∀ a : PhysicalPrime P, a.1 ∈ groups → baseline a ≠ 0 := by
    intro a ha
    rw [hb a ha]
    change physicalEndpointBaseline q (n + 1) a.2.val ≠ 0
    exact ne_of_gt (physical_endpoint_baseline_pos hq hq1 (n + 1) a.2.val
      (hP a.1 a.2.val a.2.property).pos (hsize a ha))
  have hprod : (∏ a ∈ physicalPrimeGroups P groups, baseline a) =
      ∏ a ∈ physicalPrimeGroups P groups, physicalEndpointBaseline q (n + 1) a.2.val := by
    apply prod_congr rfl
    intro a ha
    apply hb a
    simpa only [physicalPrimeGroups, mem_filter, mem_univ, true_and] using ha
  have hbounds := physical_root_endpoint_baseline_product_bounds groups q hq hq1 n hP hsize
  rw [← hprod] at hbounds
  exact physical_root_residue_model_norm_le_of_normalized_mixed_scalar
    groups e V patterns C hC q hq ζ k K hV hP hdis hk baseline hb B hB ρ hρ
    hb0 hbounds.1.le hbounds.2 A hscalar

theorem physical_root_residue_model_norm_le_of_working_cap
    (hq1 : q ≤ 1)
    (hsize : ∀ a : PhysicalPrime P, a.1 ∈ groups → 2 * (n + 2) ≤ a.2.val)
    (b : ℕ) (capError workingBound : ℝ)
    (hcap : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      ‖physicalRootNormalizedMixedScalar
          (P := P) (J := J) (ell := ell) (n := n) (B := B)
          groups e patterns C hC V q ζ k K θ
          (fun a => ((a.2.val : ℝ) * baseline a)⁻¹) ρ hP hdis -
        physicalRootNormalizedMixedScalar
          (P := P) (J := J) (ell := ell) (n := n) (B := b)
          groups e patterns C hC V q ζ k K θ
          (fun a => ((a.2.val : ℝ) * baseline a)⁻¹) ρ hP hdis‖ ≤ capError)
    (hworking : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      ‖physicalRootNormalizedMixedScalar
        (P := P) (J := J) (ell := ell) (n := n) (B := b)
        groups e patterns C hC V q ζ k K θ
        (fun a => ((a.2.val : ℝ) * baseline a)⁻¹) ρ hP hdis‖ ≤ workingBound) :
    ‖physicalRootResidueModel V patterns C q ζ k K n‖ ≤ capError + workingBound := by
  apply physical_root_residue_model_norm_le_of_large_primes
    groups e V patterns C hC q hq ζ k K hV hP hdis hk baseline hb B hB ρ hρ hq1 hsize
  intro θ hθ
  have htriangle := norm_add_le
    (physicalRootNormalizedMixedScalar
        (P := P) (J := J) (ell := ell) (n := n) (B := B)
        groups e patterns C hC V q ζ k K θ
        (fun a => ((a.2.val : ℝ) * baseline a)⁻¹) ρ hP hdis -
      physicalRootNormalizedMixedScalar
        (P := P) (J := J) (ell := ell) (n := n) (B := b)
        groups e patterns C hC V q ζ k K θ
        (fun a => ((a.2.val : ℝ) * baseline a)⁻¹) ρ hP hdis)
    (physicalRootNormalizedMixedScalar
      (P := P) (J := J) (ell := ell) (n := n) (B := b)
      groups e patterns C hC V q ζ k K θ
      (fun a => ((a.2.val : ℝ) * baseline a)⁻¹) ρ hP hdis)
  rw [sub_add_cancel] at htriangle
  exact htriangle.trans (add_le_add (hcap θ hθ) (hworking θ hθ))

end Model
end Bounty

end


-- Source module: PhysicalRootResidueTwoRegime
section

/- The two forest regimes and the original-cap comparison give the literal
residue-model bound, uniformly over all root data after the threshold. -/

open Finset Filter
open scoped Classical
namespace Bounty

theorem eventually_physical_root_residue_two_regime
    {budget E G Cv Ca Ch : ℝ}
    (hbudget : 0 ≤ budget) (hE : 0 ≤ E)
    (hD : 0 ≤ G + Ca + 6) (hgain : E + 1 + Cv + 2 ≤ G) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (I : Type) (N M J ell n b B : ℕ) (P : Fin N → Finset ℕ)
      [∀ z : PhysicalPrime P, NeZero z.2.val]
      (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
      (V : Fin N → ℝ) (patterns : Finset I)
      (C : I → Fin N → Finset (Fin J))
      (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
      (q : ℝ) (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ)
      (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
        PhysicalAuxLabels P (C i) → ℂ)
      (_hV : ∀ g, 0 < V g) (hP : ∀ g p, p ∈ P g → Nat.Prime p)
      (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))
      (_hk : ∀ time < n + 1, ∀ i ∈ patterns, ∀ g p, p ∈ P g → ¬ (p : ℤ) ∣ k time i)
      (baseline : PhysicalPrime P → ℝ)
      (_hb : ∀ p : PhysicalPrime P, p.1 ∈ groups →
        baseline p = 1 - (∑ j ∈ range (n + 2), (1 - physicalEndpointSchedule q (n + 1) j)) / p.2.val)
      (_hB : (physicalPrimeGroups P groups).card ≤ B)
      (ρ : ℝ) (_hρ : ρ ≠ 0)
      (encode : ((g : Fin M) × P (e.symm g).val) → ℤ)
      (_hinj : Function.Injective encode),
      let beta := fun p : PhysicalPrime P => ((p.2.val : ℝ) * baseline p)⁻¹
      let m := Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) b
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))
      let F := fun (θ : ℝ) (code : BirthForestCode m) =>
        physicalRootForestContribution groups e patterns C hC k V q ζ K θ
          (fun (g : Fin M) (p : P (e.symm g).val) => beta ⟨(e.symm g).val, p⟩)
          (fun j => physicalEndpointSchedule q (n + 1) j.val) ρ code
      let err := L ^ (-((E + 1) * ((n + 1 : ℕ) : ℝ)))
      0 ≤ q → q ≤ 1 →
      (∀ p : PhysicalPrime P, p.1 ∈ groups → 2 * (n + 2) ≤ p.2.val) →
      L ^ (1/2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) → (m : ℝ) ≤ L ^ (6 : ℝ) →
      ∀ H A ε : ℝ,
        0 ≤ H → H ≤ L ^ Ch → 0 ≤ A →
        A ≤ L ^ (budget * (((n + 1 : ℕ) : ℝ) + 1)) →
        0 ≤ ε → (m : ℝ) ^ 2 * ε ≤ Real.exp (-(L ^ (1/4 : ℝ))) →
        let cutoff := Nat.ceil (((2 * budget + ((E + 1) + 1) + 1) *
          ((n + 1 : ℕ) : ℝ) * Real.log L) / L ^ (1/4 : ℝ))
        (∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ code, birthForestRank code < cutoff →
          ‖F θ code‖ ≤ H * L ^ ((-G + Cv) * ((n + 1 : ℕ) : ℝ) + Cv +
            2 * birthForestRank code * (G + Ca))) →
        (∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ code, cutoff ≤ birthForestRank code →
          ‖F θ code‖ ≤ A * ε ^ birthForestRank code) →
        (∀ θ ∈ Set.Icc (0 : ℝ) 1,
          ‖physicalRootNormalizedMixedScalar (n := n) (B := B)
              groups e patterns C hC V q ζ k K θ beta ρ hP hdis -
            physicalRootNormalizedMixedScalar (n := n) (B := b)
              groups e patterns C hC V q ζ k K θ beta ρ hP hdis‖ ≤ err) →
        ‖physicalRootResidueModel V patterns C q ζ k K n‖ ≤ 2 * err := by
  filter_upwards [eventually_physical_root_scalar_two_regime
    (a := 1/2) (c := 1/4) (dimension := 6) (Ch := Ch)
    (by norm_num) (by norm_num) hbudget (by linarith : 0 ≤ E + 1)
    (by norm_num) hD hgain] with L hscalar
  intro I N M J ell n b B P _ groups e V patterns C hC q ζ k K hV hP hdis hk
    baseline hb hB ρ hρ encode hinj beta m F err hq0 hq1 hsize hN hm H A ε
    hH hHb hA hAb hε hεb cutoff hlow hhigh hcap
  have hworking : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      ‖physicalRootNormalizedMixedScalar (n := n) (B := b)
        groups e patterns C hC V q ζ k K θ beta ρ hP hdis‖ ≤ err := by
    intro θ hθ
    exact hscalar I N M J ell n b P groups e V patterns C hC q ζ k K θ beta ρ
      hP hdis encode hinj hN (L ^ (1/4 : ℝ)) H A ε le_rfl hm hH hHb hA hAb hε hεb
      (hlow θ hθ) (hhigh θ hθ)
  have h := physical_root_residue_model_norm_le_of_working_cap
    groups e V patterns C hC q hq0 ζ k K hV hP hdis hk baseline hb B hB ρ hρ
    hq1 hsize b err err hcap hworking
  simpa only [two_mul] using h

end Bounty

end


-- Source module: PhysicalRootFourierGhost
section

/- The actual local root Fourier word is the exact sum over its original
planned big actions, with every small factor and coefficient retained. -/

open Finset
open scoped Classical
namespace Bounty
section Root
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


variable (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ)
    (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) → ℝ)

variable [∀ g (p : P (e.symm g).val), NeZero p.val]

theorem physical_root_fourier_ghost_row
    (j : Fin (n + 2))
    (f : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e → ℂ) :
    physicalRootFourierRow groups e patterns C hC k V q ζ K θ β retention ρ hPs hPb hdis
      code encode ν (some (.inl j)) f =
    physicalSmallBigGhostAction
      (fun g => physicalGhostRetention (fun p : P (e.symm g).val => p.val) (retention j) ρ)
      (fun g => physicalGhostTermination (fun p : P (e.symm g).val => p.val) (retention j) ρ)
      (fun g => physicalGhostBirth (fun p : P (e.symm g).val => p.val) (retention j) ρ (V (e.symm g).val))
      (fun g => unrestrictedResidueWeight (fun p => β g p / V (e.symm g).val))
      (fun _ : Fin M => J + ell) B
      (physicalSmallBigGhostBirthPhase (fun _ : Fin M => J + ell) B
        (physicalSelectedGhostFourierObservable code ν encode j)) f := by
  funext s
  unfold physicalRootFourierRow
  rw [physical_mixed_word_row_ghost]
  unfold physicalSmallBigGhostAction
  rw [coupled_ghost_cutoff_eq_joint_event_sum]
  apply Finset.sum_congr
  · ext ev
    simp only [Finset.mem_univ]
  · intro ev _
    erw [physical_root_fourier_ghost_factor, physical_root_fourier_ghost_observable]

theorem physical_root_fourier_ghost_row_symmetric
    (j : Fin (n + 2))
    (f : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e → ℂ)
    (hf : ∀ s, ProductMemorySymmetric (fun x => f (s, x))) :
    ∀ s, ProductMemorySymmetric (fun x =>
      physicalRootFourierRow groups e patterns C hC k V q ζ K θ β retention ρ hPs hPb hdis
        code encode ν (some (.inl j)) f (s, x)) := by
  rw [physical_root_fourier_ghost_row]
  exact physical_small_big_ghost_birth_memory_symmetric _ _ _ _ _ _ _ f hf

end Root
end Bounty

end


-- Source module: PhysicalSelectedGhostFourierEnergy
section

/- The actual selected ghost Fourier phase satisfies the original ghost
energy estimate on the genuine mixed small/big measure. -/

open scoped Classical
namespace Bounty
section Ghost
variable {S : Type} [Fintype S] {N J ell n B : ℕ}
  {Ps : S → Finset ℕ} [∀ p : PhysicalPrime Ps, NeZero p.2.val]
  {P : Fin N → Finset ℕ} [∀ g (p : P g), NeZero p.val]
  (Vs : S → ℝ) (hVs : ∀ s, 0 < Vs s) (μ : ∀ g, P g → ℝ)
  (q ρ : ℝ) (V : Fin N → ℝ) (v vmax : ℝ)
  (hμ : ∀ g p, 0 < μ g p) (hmass : ∀ g, ∑ p, μ g p ≤ 2)
  (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ)
  (hV : ∀ g, 0 ≤ V g) (hVmax : ∀ g, V g ≤ vmax) (hv : 0 < v)
  (hD : q / ρ ^ 2 + ((1 - q) / ρ) / v ≤ 1)
  (hC : ∀ g, q / ρ ^ 2 + ((1 - q) * V g / ρ) / v ≤ 1)
  (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress
    (fun _ : Fin N => J + ell) B ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)))))
  (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress
      (fun _ : Fin N => J + ell) B ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)))) ×
    Fin (Fintype.card (FullMixedCommonBirthAddress
      (fun _ : Fin N => J + ell) B ((List.range (4 * n + 1)).map (physicalSelectedFineTag n))))) → ℝ)
  (encode : ((g : Fin N) × P g) → ℤ) (j : Fin (n + 1))
  (f : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B) → ℂ)
  (hf : ∀ s, ProductMemorySymmetric (fun x => f (s, x)))

include hVs hμ hmass hq0 hq1 hρ hV hVmax hv hD hC hf in
theorem physical_selected_ghost_fourier_energy_le :
    physicalSmallBigEnergy Vs (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g)))
      (physicalSmallBigGhostAction
        (fun g => physicalGhostRetention (fun p : P g => p.val) q ρ)
        (fun g => physicalGhostTermination (fun p : P g => p.val) q ρ)
        (fun g => physicalGhostBirth (fun p : P g => p.val) q ρ (V g))
        (fun g => unrestrictedResidueWeight (μ g)) (fun _ : Fin N => J + ell) B
        (physicalSmallBigGhostBirthPhase (fun _ : Fin N => J + ell) B
          (physicalSelectedGhostFourierObservable code ν encode j)) f) ≤
      physicalGhostUniformEnergyBound ρ vmax v ^ N *
        physicalSmallBigEnergy Vs (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g))) f := by
  simpa only [Fintype.card_fin] using
    physical_small_big_ghost_phase_energy_le_uniform (fun g (p : P g) => p.val)
      Vs hVs μ q ρ V v vmax (fun _ : Fin N => J + ell) B
      hμ hmass hq0 hq1 hρ hV hVmax hv hD hC
      (physicalSmallBigGhostBirthPhase (fun _ : Fin N => J + ell) B
        (physicalSelectedGhostFourierObservable code ν encode j))
      (fun s e => physical_selected_ghost_fourier_observable_norm_le code ν encode j s.1
        (fun g => (s.2 g).1) (fun g => ⟨(e g).1.val, (e g).2.2⟩)) f hf

include hVs hμ hmass hq0 hq1 hρ hV hVmax hv hD hC hf in
theorem physical_selected_ghost_fourier_norm_le :
    cleanActiveNorm (physicalSmallBigMeasure Vs
      (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g))))
      (physicalSmallBigGhostAction
        (fun g => physicalGhostRetention (fun p : P g => p.val) q ρ)
        (fun g => physicalGhostTermination (fun p : P g => p.val) q ρ)
        (fun g => physicalGhostBirth (fun p : P g => p.val) q ρ (V g))
        (fun g => unrestrictedResidueWeight (μ g)) (fun _ : Fin N => J + ell) B
        (physicalSmallBigGhostBirthPhase (fun _ : Fin N => J + ell) B
          (physicalSelectedGhostFourierObservable code ν encode j)) f) ≤
      Real.sqrt (physicalGhostUniformEnergyBound ρ vmax v ^ N) *
        cleanActiveNorm (physicalSmallBigMeasure Vs
          (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g)))) f := by
  have h := physical_selected_ghost_fourier_energy_le Vs hVs μ q ρ V v vmax
    hμ hmass hq0 hq1 hρ hV hVmax hv hD hC code ν encode j f hf
  have hs := Real.sqrt_le_sqrt h
  have hK : 0 ≤ physicalGhostUniformEnergyBound ρ vmax v ^ N :=
    pow_nonneg (Real.exp_pos _).le _
  rwa [Real.sqrt_mul hK,
    physical_small_big_sqrt_energy_eq_norm, physical_small_big_sqrt_energy_eq_norm] at hs

end Ghost
end Bounty

end


-- Source module: PhysicalRootSelectedGhostNorm
section

/- The actual local root Fourier word is the exact sum over its original
planned big actions, with every small factor and coefficient retained. -/

open Finset
open scoped Classical
namespace Bounty

theorem clean_active_norm_fintype_eq {X : Type*} (a b : Fintype X)
    (w : X → ℝ) (f : X → ℂ) :
    @cleanActiveNorm X a w f = @cleanActiveNorm X b w f := by
  cases Subsingleton.elim a b
  rfl

section Root
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


variable (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ)
    (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) → ℝ)

variable [∀ g (p : P (e.symm g).val), NeZero p.val]

variable [∀ z : PhysicalPrime (fun s : ↥groupsᶜ => P s.val), NeZero z.2.val]
  (hVs : ∀ s : ↥groupsᶜ, 0 < V s.val)
  (v vmax : ℝ)
  (hμ : ∀ g p, 0 < β g p / V (e.symm g).val)
  (hmass : ∀ g, ∑ p, β g p / V (e.symm g).val ≤ 2)
  (hρ : 0 < ρ) (hV : ∀ g : Fin M, 0 ≤ V (e.symm g).val)
  (hVmax : ∀ g : Fin M, V (e.symm g).val ≤ vmax) (hv : 0 < v)

omit [∀ z : PhysicalPrime P, NeZero z.2.val] in
include hVs hμ hmass hρ hV hVmax hv in
theorem physical_root_selected_ghost_norm_le
    (j : Fin (n + 2))
    (hq0 : 0 ≤ retention j) (hq1 : retention j ≤ 1)
    (hD : retention j / ρ ^ 2 + ((1 - retention j) / ρ) / v ≤ 1)
    (hbirth : ∀ g : Fin M,
      retention j / ρ ^ 2 + ((1 - retention j) * V (e.symm g).val / ρ) / v ≤ 1)
    (f : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e → ℂ)
    (hf : ∀ s, ProductMemorySymmetric (fun x => f (s, x))) :
    cleanActiveNorm (physicalSmallBigMeasure (fun s : ↥groupsᶜ => V s.val)
      (productMemoryWeight (fun g p => β g p / V (e.symm g).val)
        (fun g => unrestrictedResidueWeight (fun p => β g p / V (e.symm g).val))))
      (physicalSmallBigGhostAction
        (fun g => physicalGhostRetention (fun p : P (e.symm g).val => p.val) (retention j) ρ)
        (fun g => physicalGhostTermination (fun p : P (e.symm g).val => p.val) (retention j) ρ)
        (fun g => physicalGhostBirth (fun p : P (e.symm g).val => p.val) (retention j) ρ (V (e.symm g).val))
        (fun g => unrestrictedResidueWeight (fun p => β g p / V (e.symm g).val))
        (fun _ : Fin M => J + ell) B
        (physicalSmallBigGhostBirthPhase (fun _ : Fin M => J + ell) B
          (physicalSelectedGhostFourierObservable code ν encode j)) f) ≤
      Real.sqrt (physicalGhostUniformEnergyBound ρ vmax v ^ M) *
        cleanActiveNorm (physicalSmallBigMeasure (fun s : ↥groupsᶜ => V s.val)
          (productMemoryWeight (fun g p => β g p / V (e.symm g).val)
            (fun g => unrestrictedResidueWeight (fun p => β g p / V (e.symm g).val)))) f := by
  convert physical_selected_ghost_fourier_norm_le
    (S := ↥groupsᶜ) (Ps := fun s => P s.val) (P := fun g => P (e.symm g).val)
    (N := M) (n := n + 1) (J := J) (ell := ell) (B := B) (fun s : ↥groupsᶜ => V s.val) hVs
    (fun g p => β g p / V (e.symm g).val) (retention j) ρ (fun g => V (e.symm g).val)
    v vmax hμ hmass hq0 hq1 hρ hV hVmax hv hD hbirth code ν encode j f hf using 1
  · exact clean_active_norm_fintype_eq _ _ _ _
  · apply congrArg (fun y : ℝ => Real.sqrt (physicalGhostUniformEnergyBound ρ vmax v ^ M) * y)
    exact clean_active_norm_fintype_eq _ _ _ _

end Root
end Bounty

end


-- Source module: PhysicalRootFourierGhostNorm
section

/- The actual local root Fourier word is the exact sum over its original
planned big actions, with every small factor and coefficient retained. -/

open Finset
open scoped Classical
namespace Bounty
section Root
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


variable (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ)
    (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) → ℝ)

variable [∀ g (p : P (e.symm g).val), NeZero p.val]

variable [∀ z : PhysicalPrime (fun s : ↥groupsᶜ => P s.val), NeZero z.2.val]
  (hVs : ∀ s : ↥groupsᶜ, 0 < V s.val)
  (v vmax : ℝ)
  (hμ : ∀ g p, 0 < β g p / V (e.symm g).val)
  (hmass : ∀ g, ∑ p, β g p / V (e.symm g).val ≤ 2)
  (hρ : 0 < ρ) (hV : ∀ g : Fin M, 0 ≤ V (e.symm g).val)
  (hVmax : ∀ g : Fin M, V (e.symm g).val ≤ vmax) (hv : 0 < v)

include hVs hμ hmass hρ hV hVmax hv in
theorem physical_root_fourier_ghost_row_norm_le
    (j : Fin (n + 2))
    (hq0 : 0 ≤ retention j) (hq1 : retention j ≤ 1)
    (hD : retention j / ρ ^ 2 + ((1 - retention j) / ρ) / v ≤ 1)
    (hbirth : ∀ g : Fin M,
      retention j / ρ ^ 2 + ((1 - retention j) * V (e.symm g).val / ρ) / v ≤ 1)
    (f : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e → ℂ)
    (hf : ∀ s, ProductMemorySymmetric (fun x => f (s, x))) :
    cleanActiveNorm (physicalSmallBigMeasure (fun s : ↥groupsᶜ => V s.val)
      (productMemoryWeight (fun g p => β g p / V (e.symm g).val)
        (fun g => unrestrictedResidueWeight (fun p => β g p / V (e.symm g).val))))
      (physicalRootFourierRow groups e patterns C hC k V q ζ K θ β retention ρ hPs hPb hdis
        code encode ν (some (.inl j)) f) ≤
      Real.sqrt (physicalGhostUniformEnergyBound ρ vmax v ^ M) *
        cleanActiveNorm (physicalSmallBigMeasure (fun s : ↥groupsᶜ => V s.val)
          (productMemoryWeight (fun g p => β g p / V (e.symm g).val)
            (fun g => unrestrictedResidueWeight (fun p => β g p / V (e.symm g).val)))) f := by
  let w : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e → ℝ := physicalSmallBigMeasure (fun s : ↥groupsᶜ => V s.val)
    (productMemoryWeight (fun g p => β g p / V (e.symm g).val)
      (fun g => unrestrictedResidueWeight (fun p => β g p / V (e.symm g).val)))
  have heq := physical_root_fourier_ghost_row (n := n) (J := J) (ell := ell) (B := B) groups e patterns C hC k V q ζ K θ β retention ρ
    hPs hPb hdis code encode ν j f
  have hg := physical_root_selected_ghost_norm_le groups e V β retention ρ code encode ν
    hVs v vmax hμ hmass hρ hV hVmax hv j hq0 hq1 hD hbirth f hf
  exact (congrArg (cleanActiveNorm w) heq).le.trans hg

end Root
end Bounty

end


-- Source module: PhysicalSelectedInterleaving
section

/- The original selected word alternates visits with fully projected edges,
including its final visit. -/

namespace Bounty
section Operators
variable {X : Type*} {n : ℕ}
  (row : Option (Fin (n + 1) ⊕ Fin n) → (X → ℂ) → X → ℂ)

noncomputable def physicalSelectedVisitOperator (i : ℕ) (f : X → ℂ) : X → ℂ :=
  if h : i < n + 1 then row (some (.inl ⟨i, h⟩)) f else f

noncomputable def physicalSelectedEdgeOperator (i : ℕ) (f : X → ℂ) : X → ℂ :=
  if h : i < n then row none (row (some (.inr ⟨i, h⟩)) (row none f)) else f

theorem physical_selected_operator_word_interleaved (f : X → ℂ) :
    finiteOperatorListAction row
      ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) f =
    finiteRowComposition (S := fun _ => X)
      (fun i u => physicalSelectedVisitOperator row i (physicalSelectedEdgeOperator row i u)) n
      (physicalSelectedVisitOperator row n f) := by
  have hcut (i : ℕ) : finiteRowBlockCut (fun _ => 4) i = 4 * i := by
    induction i with
    | zero => rfl
    | succ i ih => simp only [finiteRowBlockCut, ih]; omega
  have hlast : row (physicalSelectedFineTag n (4 * n)) f = physicalSelectedVisitOperator row n f := by
    have ht := physical_selected_fine_tag_visit (Fin.last n)
    change physicalSelectedFineTag n (4 * n) = some (.inl (Fin.last n)) at ht
    rw [ht]
    simp only [physicalSelectedVisitOperator, Nat.lt_succ_self, dif_pos]
    rfl
  rw [finite_operator_list_action_map, ← finite_row_composition_eq_operator_list,
    finite_row_composition_succ, hlast]
  have hg := finite_row_grouped_composition (S := fun _ => X)
    (fun i => row (physicalSelectedFineTag n i)) (fun _ => 4) n
    (physicalSelectedVisitOperator row n f)
  rw [hcut n] at hg
  rw [← hg]
  apply finite_row_composition_congr_before
  intro i hi u
  unfold finiteRowGrouped
  rw [hcut i]
  change row (physicalSelectedFineTag n (4 * i))
    (row (physicalSelectedFineTag n (4 * i + 1))
      (row (physicalSelectedFineTag n (4 * i + 2))
        (row (physicalSelectedFineTag n (4 * i + 3)) u))) = _
  rw [physical_selected_fine_tag_visit (⟨i, by omega⟩ : Fin (n + 1)),
    physical_selected_fine_tag_before_edge (⟨i, hi⟩ : Fin n),
    physical_selected_fine_tag_edge (⟨i, hi⟩ : Fin n),
    physical_selected_fine_tag_after_edge (⟨i, hi⟩ : Fin n)]
  simp only [physicalSelectedVisitOperator, physicalSelectedEdgeOperator,
    dif_pos hi, dif_pos (show i < n + 1 by omega)]

end Operators
end Bounty

end


-- Source module: SelectedWordNorm
section

/- Norm propagation across every original selected edge, with loss charged
only to the deduplicated exceptional edges and all visits included. -/

open Finset
open scoped Classical
namespace Bounty

theorem finite_row_function_norm_le {X : Type*}
    (normFn : (X → ℂ) → ℝ) (S : (X → ℂ) → Prop)
    (row : ℕ → (X → ℂ) → X → ℂ) (c : ℕ → ℝ) (n : ℕ)
    (hc : ∀ i < n, 0 ≤ c i)
    (hpres : ∀ i < n, ∀ f, S f → S (row i f))
    (hrow : ∀ i < n, ∀ f, S f → normFn (row i f) ≤ c i * normFn f)
    (f : X → ℂ) (hf : S f) :
    S (finiteRowComposition (S := fun _ => X) row n f) ∧
      normFn (finiteRowComposition (S := fun _ => X) row n f) ≤
        (∏ i ∈ range n, c i) * normFn f := by
  induction n generalizing f with
  | zero => simpa only [finiteRowComposition, range_zero, prod_empty, one_mul] using And.intro hf (le_refl _)
  | succ n ih =>
    have h := ih (fun i hi => hc i (Nat.lt_succ_of_lt hi))
      (fun i hi => hpres i (Nat.lt_succ_of_lt hi))
      (fun i hi => hrow i (Nat.lt_succ_of_lt hi)) (row n f)
      (hpres n (Nat.lt_succ_self n) f hf)
    refine ⟨h.1, h.2.trans ?_⟩
    rw [prod_range_succ, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hrow n (Nat.lt_succ_self n) f hf)
      (prod_nonneg fun i hi => hc i (Nat.lt_succ_of_lt (mem_range.mp hi)))

theorem function_interleaved_norm_le {X : Type*}
    (normFn : (X → ℂ) → ℝ) (S : (X → ℂ) → Prop)
    (E G : ℕ → (X → ℂ) → X → ℂ) (c : ℕ → ℝ) (n : ℕ) {M : ℝ}
    (hM : 0 ≤ M) (hc : ∀ i < n, 0 ≤ c i)
    (hEpres : ∀ i < n, ∀ f, S f → S (E i f))
    (hGpres : ∀ i ≤ n, ∀ f, S f → S (G i f))
    (hE : ∀ i < n, ∀ f, S f → normFn (E i f) ≤ c i * normFn f)
    (hG : ∀ i ≤ n, ∀ f, S f → normFn (G i f) ≤ M * normFn f)
    (f : X → ℂ) (hf : S f) :
    S (finiteRowComposition (S := fun _ => X) (fun i u => G i (E i u)) n (G n f)) ∧
      normFn (finiteRowComposition (S := fun _ => X) (fun i u => G i (E i u)) n (G n f)) ≤
        M ^ (n + 1) * (∏ i ∈ range n, c i) * normFn f := by
  have h := finite_row_function_norm_le normFn S (fun i u => G i (E i u))
    (fun i => M * c i) n (fun i hi => mul_nonneg hM (hc i hi))
    (fun i hi u hu => hGpres i (Nat.le_of_lt hi) _ (hEpres i hi u hu))
    (fun i hi u hu => (hG i (Nat.le_of_lt hi) _ (hEpres i hi u hu)).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hE i hi u hu) hM))
    (G n f) (hGpres n le_rfl f hf)
  refine ⟨h.1, h.2.trans ?_⟩
  calc
    (∏ i ∈ range n, M * c i) * normFn (G n f) ≤
        (∏ i ∈ range n, M * c i) * (M * normFn f) :=
      mul_le_mul_of_nonneg_left (hG n le_rfl f hf)
        (prod_nonneg fun i hi => mul_nonneg hM (hc i (mem_range.mp hi)))
    _ = _ := by
      rw [prod_mul_distrib]
      simp only [prod_const, card_range, pow_succ]
      ring

theorem selected_word_low_rank_norm_le {X : Type*} {n : ℕ}
    (normFn : (X → ℂ) → ℝ) (hnorm : ∀ f, 0 ≤ normFn f) (S : (X → ℂ) → Prop)
    (row : Option (Fin (n + 1) ⊕ Fin n) → (X → ℂ) → X → ℂ)
    (bad : Finset (Fin n)) (r : ℕ) {q A M : ℝ}
    (hq : 0 < q) (hA : q ≤ A) (hM : 0 ≤ M) (hbad : bad.card ≤ 2 * r)
    (hEpres : ∀ j : Fin n, ∀ f, S f → S (row none (row (some (.inr j)) (row none f))))
    (hGpres : ∀ j : Fin (n + 1), ∀ f, S f → S (row (some (.inl j)) f))
    (hE : ∀ j : Fin n, ∀ f, S f →
      normFn (row none (row (some (.inr j)) (row none f))) ≤
        (if j ∈ bad then A else q) * normFn f)
    (hG : ∀ j : Fin (n + 1), ∀ f, S f → normFn (row (some (.inl j)) f) ≤ M * normFn f)
    (f : X → ℂ) (hf : S f) :
    S (finiteOperatorListAction row ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) f) ∧
      normFn (finiteOperatorListAction row ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) f) ≤
        (M ^ (n + 1) * q ^ n * (A / q) ^ (2 * r)) * normFn f := by
  let c : ℕ → ℝ := fun i => if i ∈ bad.image Fin.val then A else q
  have hc (i : Fin n) : c i.val = if i ∈ bad then A else q := by
    simp only [c, mem_image, Fin.val_inj, exists_eq_right]
  have h := function_interleaved_norm_le normFn S
    (physicalSelectedEdgeOperator row) (physicalSelectedVisitOperator row) c n hM
    (fun _ _ => ite_nonneg (hq.le.trans hA) hq.le)
    (fun i hi u hu => by simpa only [physicalSelectedEdgeOperator, dif_pos hi] using hEpres ⟨i, hi⟩ u hu)
    (fun i hi u hu => by simpa only [physicalSelectedVisitOperator, dif_pos (Nat.lt_succ_of_le hi)] using hGpres ⟨i, Nat.lt_succ_of_le hi⟩ u hu)
    (fun i hi u hu => by simpa only [physicalSelectedEdgeOperator, dif_pos hi, hc ⟨i, hi⟩] using hE ⟨i, hi⟩ u hu)
    (fun i hi u hu => by simpa only [physicalSelectedVisitOperator, dif_pos (Nat.lt_succ_of_le hi)] using hG ⟨i, Nat.lt_succ_of_le hi⟩ u hu) f hf
  rw [← physical_selected_operator_word_interleaved] at h
  have hprod : (∏ i ∈ range n, c i) = q ^ n * (A / q) ^ bad.card := by
    rw [← Fin.prod_univ_eq_prod_range]
    simp_rw [hc]
    exact edge_scalar_product_eq bad hq.ne'
  refine ⟨h.1, h.2.trans ?_⟩
  rw [hprod, ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (hnorm f)
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (pow_nonneg hM _) (pow_nonneg hq.le _))
  exact pow_le_pow_right₀ ((le_div_iff₀ hq).mpr (by simpa only [one_mul] using hA)) hbad

end Bounty

end


-- Source module: PhysicalRootFourierNorm
section

/- The actual local root Fourier word is the exact sum over its original
planned big actions, with every small factor and coefficient retained. -/

open Finset
open scoped Classical
namespace Bounty
section Root
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


variable (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ)
    (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) → ℝ)

theorem physical_root_fourier_word_norm_le
    (normFn : (PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e → ℂ) → ℝ)
    (hnorm : ∀ f, 0 ≤ normFn f)
    (S : (PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e → ℂ) → Prop)
    {decay excess visit : ℝ} (hdecay : 0 < decay) (hexcess : decay ≤ excess) (hvisit : 0 ≤ visit) :
    let row := physicalRootFourierRow groups e patterns C hC k V q ζ K θ β retention ρ hPs hPb hdis
      code encode ν
    let bad := physicalSelectedAffectedEdges (fun _ : Fin M => J + ell) B (n + 1) code
    (∀ j : Fin (n + 1), ∀ f, S f → S (row none (row (some (.inr j)) (row none f)))) →
    (∀ j : Fin (n + 2), ∀ f, S f → S (row (some (.inl j)) f)) →
    (∀ j : Fin (n + 1), ∀ f, S f →
      normFn (row none (row (some (.inr j)) (row none f))) ≤
        (if j ∈ bad then excess else decay) * normFn f) →
    (∀ j : Fin (n + 2), ∀ f, S f → normFn (row (some (.inl j)) f) ≤ visit * normFn f) →
    ∀ f, S f →
      S (finiteOperatorListAction row
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) f) ∧
      normFn (finiteOperatorListAction row
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) f) ≤
        (visit ^ (n + 2) * decay ^ (n + 1) * (excess / decay) ^ (2 * birthForestRank code)) * normFn f := by
  intro row bad hEpres hGpres hE hG f hf
  exact selected_word_low_rank_norm_le normFn hnorm S row bad (birthForestRank code)
    hdecay hexcess hvisit (physical_selected_affected_edges_card _ _ _ code)
    hEpres hGpres hE hG f hf

end Root
end Bounty

end


-- Source module: PhysicalRootFourierEvolution
section

/- The actual local root Fourier word is the exact sum over its original
planned big actions, with every small factor and coefficient retained. -/

open Finset
open scoped Classical
namespace Bounty
section Root
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


variable (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ)
    (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) → ℝ)

variable [∀ g (p : P (e.symm g).val), NeZero p.val]

variable [∀ z : PhysicalPrime (fun s : ↥groupsᶜ => P s.val), NeZero z.2.val]
  (hVs : ∀ s : ↥groupsᶜ, 0 < V s.val)
  (v vmax : ℝ)
  (hμ : ∀ g p, 0 < β g p / V (e.symm g).val)
  (hmass : ∀ g, ∑ p, β g p / V (e.symm g).val ≤ 2)
  (hρ : 0 < ρ) (hV : ∀ g : Fin M, 0 ≤ V (e.symm g).val)
  (hVmax : ∀ g : Fin M, V (e.symm g).val ≤ vmax) (hv : 0 < v)

include hVs hμ hmass hρ hV hVmax hv in
theorem physical_root_fourier_evolution_norm_le
    (hret0 : ∀ j, 0 ≤ retention j) (hret1 : ∀ j, retention j ≤ 1)
    (hD : ∀ j, retention j / ρ ^ 2 + ((1 - retention j) / ρ) / v ≤ 1)
    (hbirth : ∀ j (g : Fin M),
      retention j / ρ ^ 2 + ((1 - retention j) * V (e.symm g).val / ρ) / v ≤ 1)
    {decay excess : ℝ} (hdecay : 0 < decay) (hexcess : decay ≤ excess) :
    let row := physicalRootFourierRow groups e patterns C hC k V q ζ K θ β retention ρ hPs hPb hdis
      code encode ν
    let w : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e → ℝ := physicalSmallBigMeasure (fun s : ↥groupsᶜ => V s.val)
      (productMemoryWeight (fun g p => β g p / V (e.symm g).val)
        (fun g => unrestrictedResidueWeight (fun p => β g p / V (e.symm g).val)))
    let symmetric := fun f : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e → ℂ =>
      ∀ s, ProductMemorySymmetric (fun x => f (s, x))
    (∀ j : Fin (n + 1), ∀ f, symmetric f → symmetric (row none (row (some (.inr j)) (row none f)))) →
    (∀ j : Fin (n + 1), ∀ f, symmetric f →
      cleanActiveNorm w (row none (row (some (.inr j)) (row none f))) ≤
        (if j ∈ physicalSelectedAffectedEdges (fun _ : Fin M => J + ell) B (n + 1) code
          then excess else decay) * cleanActiveNorm w f) →
    ∀ f, symmetric f →
      symmetric (finiteOperatorListAction row
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) f) ∧
      cleanActiveNorm w (finiteOperatorListAction row
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) f) ≤
        (Real.sqrt (physicalGhostUniformEnergyBound ρ vmax v ^ M) ^ (n + 2) *
          decay ^ (n + 1) * (excess / decay) ^ (2 * birthForestRank code)) * cleanActiveNorm w f := by
  intro row w symmetric hEpres hE f hf
  exact physical_root_fourier_word_norm_le groups e patterns C hC k V q ζ K θ β retention ρ
    hPs hPb hdis code encode ν (cleanActiveNorm w) (fun _ => Real.sqrt_nonneg _) symmetric
    hdecay hexcess (Real.sqrt_nonneg _)
    hEpres
    (fun j u hu => physical_root_fourier_ghost_row_symmetric groups e patterns C hC k V q ζ K θ β retention ρ
      hPs hPb hdis code encode ν j u hu)
    hE
    (fun j u hu => physical_root_fourier_ghost_row_norm_le groups e patterns C hC k V q ζ K θ β retention ρ
      hPs hPb hdis code encode ν hVs v vmax hμ hmass hρ hV hVmax hv j (hret0 j) (hret1 j) (hD j)
      (hbirth j) u hu) f hf

end Root
end Bounty

end


-- Source module: PhysicalRootFourierLowRank
section

/- The actual local root Fourier word is the exact sum over its original
planned big actions, with every small factor and coefficient retained. -/

open Finset
open scoped Classical
namespace Bounty
section Root
variable {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
  [∀ z : PhysicalPrime P, NeZero z.2.val]
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
  (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
  (k : ℕ → I → ℤ)

  (V : Fin N → ℝ) (q : ℝ) (ζ : ℕ → I → ℝ)
  (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
    PhysicalAuxLabels P (C i) → ℂ)
  (θ : ℝ)
  (β : (g : Fin M) → P (e.symm g).val → ℝ)
  (retention : Fin (n + 2) → ℝ) (ρ : ℝ)

  (hPs : ∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p)
  (hPb : ∀ (g : Fin M) p, p ∈ P (e.symm g).val → Nat.Prime p)
  (hdis : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (e.symm g).val))


variable (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ)
    (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) → ℝ)

variable [∀ g (p : P (e.symm g).val), NeZero p.val]

variable [∀ z : PhysicalPrime (fun s : ↥groupsᶜ => P s.val), NeZero z.2.val]
  (hVs : ∀ s : ↥groupsᶜ, 0 < V s.val)
  (v vmax : ℝ)
  (hμ : ∀ g p, 0 < β g p / V (e.symm g).val)
  (hmass : ∀ g, ∑ p, β g p / V (e.symm g).val ≤ 2)
  (hρ : 0 < ρ) (hV : ∀ g : Fin M, 0 ≤ V (e.symm g).val)
  (hVmax : ∀ g : Fin M, V (e.symm g).val ≤ vmax) (hv : 0 < v)

include hVs hμ hmass hρ hV hVmax hv in
theorem physical_root_fourier_low_rank_readout_le
    (hMass : ∀ s : ↥groupsᶜ, ∑ p ∈ P s.val, 1 / (p : ℝ) = V s.val)
    (hret0 : ∀ j, 0 ≤ retention j) (hret1 : ∀ j, retention j ≤ 1)
    (hD : ∀ j, retention j / ρ ^ 2 + ((1 - retention j) / ρ) / v ≤ 1)
    (hbirth : ∀ j (g : Fin M),
      retention j / ρ ^ 2 + ((1 - retention j) * V (e.symm g).val / ρ) / v ≤ 1)
    {decay excess : ℝ} (hdecay : 0 < decay) (hexcess : decay ≤ excess) :
    let row := physicalRootFourierRow groups e patterns C hC k V q ζ K θ β retention ρ hPs hPb hdis
      code encode ν
    let w : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e → ℝ := physicalSmallBigMeasure (fun s : ↥groupsᶜ => V s.val)
      (productMemoryWeight (fun g p => β g p / V (e.symm g).val)
        (fun g => unrestrictedResidueWeight (fun p => β g p / V (e.symm g).val)))
    let symmetric := fun f : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e → ℂ =>
      ∀ s, ProductMemorySymmetric (fun x => f (s, x))
    (∀ j : Fin (n + 1), ∀ f, symmetric f → symmetric (row none (row (some (.inr j)) (row none f)))) →
    (∀ j : Fin (n + 1), ∀ f, symmetric f →
      cleanActiveNorm w (row none (row (some (.inr j)) (row none f))) ≤
        (if j ∈ physicalSelectedAffectedEdges (fun _ : Fin M => J + ell) B (n + 1) code
          then excess else decay) * cleanActiveNorm w f) →
    ‖physicalRootFourierReadout groups e patterns C hC k V q ζ K θ β retention ρ
      hPs hPb hdis code encode ν‖ ≤
        (Real.sqrt (physicalGhostUniformEnergyBound ρ vmax v ^ M) ^ (n + 2) *
          decay ^ (n + 1) * (excess / decay) ^ (2 * birthForestRank code)) *
          ∏ g, (∑ p, β g p / V (e.symm g).val) ^ (J + ell) := by
  intro row w symmetric hEpres hE
  have hEv := physical_root_fourier_evolution_norm_le groups e patterns C hC k V q ζ K θ β retention ρ
    hPs hPb hdis code encode ν hVs v vmax hμ hmass hρ hV hVmax hv
    hret0 hret1 hD hbirth hdecay hexcess hEpres hE
    (fun s => fullMemoryVacuum s.2) (fun _ => fullMemoryVacuum_symmetric)
  apply physical_root_fourier_readout_norm_le groups e patterns C hC k V q ζ K θ β retention ρ
    hPs hPb hdis code encode ν hVs hMass (fun g p => (hμ g p).le)
  · exact mul_nonneg
      (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (pow_nonneg hdecay.le _))
      (pow_nonneg (div_nonneg (hdecay.le.trans hexcess) hdecay.le) _)
  · exact hEv.2

end Root
end Bounty

end


-- Source module: PhysicalRootForestLowRank
section

/- The actual local root Fourier word is the exact sum over its original
planned big actions, with every small factor and coefficient retained. -/

open Finset
open scoped Classical
namespace Bounty
section Root
variable {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
  [∀ z : PhysicalPrime P, NeZero z.2.val]
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
  (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
  (k : ℕ → I → ℤ)

  (V : Fin N → ℝ) (q : ℝ) (ζ : ℕ → I → ℝ)
  (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
    PhysicalAuxLabels P (C i) → ℂ)
  (θ : ℝ)
  (β : (g : Fin M) → P (e.symm g).val → ℝ)
  (retention : Fin (n + 2) → ℝ) (ρ : ℝ)

  (hPs : ∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p)
  (hPb : ∀ (g : Fin M) p, p ∈ P (e.symm g).val → Nat.Prime p)
  (hdis : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (e.symm g).val))


variable (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ)
    (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) → ℝ)

variable [∀ g (p : P (e.symm g).val), NeZero p.val]

variable [∀ z : PhysicalPrime (fun s : ↥groupsᶜ => P s.val), NeZero z.2.val]
  (hVs : ∀ s : ↥groupsᶜ, 0 < V s.val)
  (v vmax : ℝ)
  (hμ : ∀ g p, 0 < β g p / V (e.symm g).val)
  (hmass : ∀ g, ∑ p, β g p / V (e.symm g).val ≤ 2)
  (hρ : 0 < ρ) (hV : ∀ g : Fin M, 0 ≤ V (e.symm g).val)
  (hVmax : ∀ g : Fin M, V (e.symm g).val ≤ vmax) (hv : 0 < v)

include hVs hμ hmass hρ hV hVmax hv in
theorem physical_root_low_rank_forest_contribution_le
    (hinj : Function.Injective encode)
    (hMass : ∀ s : ↥groupsᶜ, ∑ p ∈ P s.val, 1 / (p : ℝ) = V s.val)
    (hret0 : ∀ j, 0 ≤ retention j) (hret1 : ∀ j, retention j ≤ 1)
    (hD : ∀ j, retention j / ρ ^ 2 + ((1 - retention j) / ρ) / v ≤ 1)
    (hbirth : ∀ j (g : Fin M),
      retention j / ρ ^ 2 + ((1 - retention j) * V (e.symm g).val / ρ) / v ≤ 1)
    {decay excess : ℝ} (hdecay : 0 < decay) (hexcess : decay ≤ excess) :
    let row := physicalRootFourierRow groups e patterns C hC k V q ζ K θ β retention ρ hPs hPb hdis
      code encode
    let w : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e → ℝ := physicalSmallBigMeasure (fun s : ↥groupsᶜ => V s.val)
      (productMemoryWeight (fun g p => β g p / V (e.symm g).val)
        (fun g => unrestrictedResidueWeight (fun p => β g p / V (e.symm g).val)))
    let symmetric := fun f : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e → ℂ =>
      ∀ s, ProductMemorySymmetric (fun x => f (s, x))
    (∀ ν, ∀ j : Fin (n + 1), ∀ f, symmetric f → symmetric (row ν none (row ν (some (.inr j)) (row ν none f)))) →
    (∀ ν, ∀ j : Fin (n + 1), ∀ f, symmetric f →
      cleanActiveNorm w (row ν none (row ν (some (.inr j)) (row ν none f))) ≤
        (if j ∈ physicalSelectedAffectedEdges (fun _ : Fin M => J + ell) B (n + 1) code
          then excess else decay) * cleanActiveNorm w f) →
    ‖physicalRootForestContribution groups e patterns C hC k V q ζ K θ β retention ρ code‖ ≤
        (Real.sqrt (physicalGhostUniformEnergyBound ρ vmax v ^ M) ^ (n + 2) *
          decay ^ (n + 1) * (excess / decay) ^ (2 * birthForestRank code)) *
          ∏ g, (∑ p, β g p / V (e.symm g).val) ^ (J + ell) := by
  intro row w symmetric hEpres hE
  apply physical_root_forest_contribution_norm_le groups e patterns C hC k V q ζ K θ β retention ρ
    hPs hPb hdis code encode hinj
  intro ν
  exact physical_root_fourier_low_rank_readout_le groups e patterns C hC k V q ζ K θ β retention ρ
    hPs hPb hdis code encode ν hVs v vmax hμ hmass hρ hV hVmax hv
    hMass hret0 hret1 hD hbirth hdecay hexcess (hEpres ν) (hE ν)

end Root
end Bounty

end


-- Source module: RootLowRankPower
section

/- The exact low-rank word cost has the exponent required by the
finite forest head estimate. -/

namespace Bounty

theorem root_low_rank_cost_power_le
    {L visit mass H G Ca Cv : ℝ} (N r : ℕ)
    (hL : 0 < L) (hvisit : 0 ≤ visit) (hv : visit ≤ L ^ Cv)
    (hmass : 0 ≤ mass) (hM : mass ≤ H) :
    (visit ^ (N + 1) * (L ^ (-G)) ^ N *
      (L ^ Ca / L ^ (-G)) ^ (2 * r)) * mass ≤
        H * L ^ ((-G + Cv) * N + Cv + 2 * r * (G + Ca)) := by
  have hq : 0 ≤ (L ^ (-G)) ^ N := pow_nonneg (Real.rpow_pos_of_pos hL _).le _
  have ha : 0 ≤ (L ^ Ca / L ^ (-G)) ^ (2 * r) :=
    pow_nonneg (div_nonneg (Real.rpow_pos_of_pos hL _).le
      (Real.rpow_pos_of_pos hL _).le) _
  have hc : visit ^ (N + 1) * (L ^ (-G)) ^ N * (L ^ Ca / L ^ (-G)) ^ (2 * r) ≤
      (L ^ Cv) ^ (N + 1) * (L ^ (-G)) ^ N * (L ^ Ca / L ^ (-G)) ^ (2 * r) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hvisit hv _) hq) ha
  have hp (a : ℝ) (k : ℕ) : (L ^ a) ^ k = L ^ (a * k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
  calc
    _ ≤ ((L ^ Cv) ^ (N + 1) * (L ^ (-G)) ^ N *
        (L ^ Ca / L ^ (-G)) ^ (2 * r)) * H :=
      mul_le_mul hc hM hmass
        (mul_nonneg (mul_nonneg (pow_nonneg (Real.rpow_pos_of_pos hL _).le _) hq) ha)
    _ = L ^ (Cv * (N + 1 : ℕ) + (-G) * N + (Ca - (-G)) * (2 * r : ℕ)) * H := by
      rw [← Real.rpow_sub hL, hp, hp, hp, ← Real.rpow_add hL, ← Real.rpow_add hL]
    _ = _ := by
      rw [mul_comm]
      congr 2
      push_cast
      ring

end Bounty

end


-- Source module: PhysicalRootLowRankPower
section

/- Convert the actual Fourier edge costs to the exact polynomial low-rank
exponent used by the common-forest two-regime estimate. -/

open Finset
open scoped Classical
namespace Bounty
section Root
variable {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
  [∀ z : PhysicalPrime P, NeZero z.2.val]
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
  (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
  (k : ℕ → I → ℤ)

  (V : Fin N → ℝ) (q : ℝ) (ζ : ℕ → I → ℝ)
  (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
    PhysicalAuxLabels P (C i) → ℂ)
  (θ : ℝ)
  (β : (g : Fin M) → P (e.symm g).val → ℝ)
  (retention : Fin (n + 2) → ℝ) (ρ : ℝ)

  (hPs : ∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p)
  (hPb : ∀ (g : Fin M) p, p ∈ P (e.symm g).val → Nat.Prime p)
  (hdis : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (e.symm g).val))


variable (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ)
    (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) → ℝ)

variable [∀ g (p : P (e.symm g).val), NeZero p.val]

variable [∀ z : PhysicalPrime (fun s : ↥groupsᶜ => P s.val), NeZero z.2.val]
  (hVs : ∀ s : ↥groupsᶜ, 0 < V s.val)
  (v vmax : ℝ)
  (hμ : ∀ g p, 0 < β g p / V (e.symm g).val)
  (hmass : ∀ g, ∑ p, β g p / V (e.symm g).val ≤ 2)
  (hρ : 0 < ρ) (hV : ∀ g : Fin M, 0 ≤ V (e.symm g).val)
  (hVmax : ∀ g : Fin M, V (e.symm g).val ≤ vmax) (hv : 0 < v)

include hVs hμ hmass hρ hV hVmax hv in
theorem physical_root_low_rank_forest_contribution_power_le
    (hinj : Function.Injective encode)
    (hMass : ∀ s : ↥groupsᶜ, ∑ p ∈ P s.val, 1 / (p : ℝ) = V s.val)
    (hret0 : ∀ j, 0 ≤ retention j) (hret1 : ∀ j, retention j ≤ 1)
    (hD : ∀ j, retention j / ρ ^ 2 + ((1 - retention j) / ρ) / v ≤ 1)
    (hbirth : ∀ j (g : Fin M),
      retention j / ρ ^ 2 + ((1 - retention j) * V (e.symm g).val / ρ) / v ≤ 1)
    {L G Ca Cv H decay excess : ℝ} (hL : 1 ≤ L) (hexponent : 0 ≤ G + Ca)
    (hdecay : decay ≤ L ^ (-G)) (hexcess : excess ≤ L ^ Ca)
    (hvisit : Real.sqrt (physicalGhostUniformEnergyBound ρ vmax v ^ M) ≤ L ^ Cv)
    (hinitial : (∏ g, (∑ p, β g p / V (e.symm g).val) ^ (J + ell)) ≤ H) :
    let row := physicalRootFourierRow groups e patterns C hC k V q ζ K θ β retention ρ hPs hPb hdis
      code encode
    let w : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e → ℝ :=
      physicalSmallBigMeasure (fun s : ↥groupsᶜ => V s.val)
        (productMemoryWeight (fun g p => β g p / V (e.symm g).val)
          (fun g => unrestrictedResidueWeight (fun p => β g p / V (e.symm g).val)))
    let symmetric := fun f : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e → ℂ =>
      ∀ s, ProductMemorySymmetric (fun x => f (s, x))
    (∀ ν, ∀ j : Fin (n + 1), ∀ f, symmetric f →
      symmetric (row ν none (row ν (some (.inr j)) (row ν none f)))) →
    (∀ ν, ∀ j : Fin (n + 1), ∀ f, symmetric f →
      cleanActiveNorm w (row ν none (row ν (some (.inr j)) (row ν none f))) ≤
        (if j ∈ physicalSelectedAffectedEdges (fun _ : Fin M => J + ell) B (n + 1) code
          then excess else decay) * cleanActiveNorm w f) →
    ‖physicalRootForestContribution groups e patterns C hC k V q ζ K θ β retention ρ code‖ ≤
      H * L ^ ((-G + Cv) * ((n + 1 : ℕ) : ℝ) + Cv + 2 * birthForestRank code * (G + Ca)) := by
  intro row w symmetric hEpres hE
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have horder : L ^ (-G) ≤ L ^ Ca :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hword := physical_root_low_rank_forest_contribution_le groups e patterns C hC k V q ζ K θ
    β retention ρ hPs hPb hdis code encode hVs v vmax hμ hmass hρ hV hVmax hv hinj
    hMass hret0 hret1 hD hbirth (Real.rpow_pos_of_pos hL0 (-G)) horder hEpres
    (fun ν j f hf => (hE ν j f hf).trans (mul_le_mul_of_nonneg_right (by
      by_cases hj : j ∈ physicalSelectedAffectedEdges (fun _ : Fin M => J + ell) B (n + 1) code
      · simpa only [if_pos hj] using hexcess
      · simpa only [if_neg hj] using hdecay) (Real.sqrt_nonneg _)))
  have hm0 : 0 ≤ ∏ g, (∑ p, β g p / V (e.symm g).val) ^ (J + ell) :=
    prod_nonneg (fun g _ => pow_nonneg (sum_nonneg (fun p _ => (hμ g p).le)) _)
  exact hword.trans (root_low_rank_cost_power_le (n + 1) (birthForestRank code)
    hL0 (Real.sqrt_nonneg _) hvisit hm0 hinitial)

end Root
end Bounty

end


-- Source module: PhysicalRootResidueEdgeCosts
section

/- Explicit projected edge costs, the high-rank estimate, and the cap
comparison give the literal original residue-model bound. -/

open Finset Filter
open scoped Classical
namespace Bounty

theorem eventually_physical_root_residue_of_edge_costs
    {budget E G Cv Ca Ch : ℝ}
    (hbudget : 0 ≤ budget) (hE : 0 ≤ E)
    (hD : 0 ≤ G + Ca + 6) (hgain : E + 1 + Cv + 2 ≤ G) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (I : Type) (N M J ell n b B : ℕ) (P : Fin N → Finset ℕ)
      [∀ z : PhysicalPrime P, NeZero z.2.val]
      (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
      (V : Fin N → ℝ) (patterns : Finset I)
      (C : I → Fin N → Finset (Fin J))
      (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
      (q : ℝ) (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ)
      (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
        PhysicalAuxLabels P (C i) → ℂ)
      (_hV : ∀ g, 0 < V g) (hP : ∀ g p, p ∈ P g → Nat.Prime p)
      (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))
      (_hk : ∀ time < n + 1, ∀ i ∈ patterns, ∀ g p, p ∈ P g → ¬ (p : ℤ) ∣ k time i)
      (baseline : PhysicalPrime P → ℝ)
      (_hb : ∀ p : PhysicalPrime P, p.1 ∈ groups →
        baseline p = 1 - (∑ j ∈ range (n + 2), (1 - physicalEndpointSchedule q (n + 1) j)) / p.2.val)
      (_hB : (physicalPrimeGroups P groups).card ≤ B)
      (ρ : ℝ) (_hρ : ρ ≠ 0)
      (encode : ((g : Fin M) × P (e.symm g).val) → ℤ)
      (_hinj : Function.Injective encode),
      let beta := fun p : PhysicalPrime P => ((p.2.val : ℝ) * baseline p)⁻¹
      let m := Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) b
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))
      let F := fun (θ : ℝ) (code : BirthForestCode m) =>
        physicalRootForestContribution groups e patterns C hC k V q ζ K θ
          (fun (g : Fin M) (p : P (e.symm g).val) => beta ⟨(e.symm g).val, p⟩)
          (fun j => physicalEndpointSchedule q (n + 1) j.val) ρ code
      let err := L ^ (-((E + 1) * ((n + 1 : ℕ) : ℝ)))
      0 ≤ q → q ≤ 1 →
      (∀ p : PhysicalPrime P, p.1 ∈ groups → 2 * (n + 2) ≤ p.2.val) →
      L ^ (1/2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) → (m : ℝ) ≤ L ^ (6 : ℝ) →
      ∀ H A ε : ℝ,
        0 ≤ H → H ≤ L ^ Ch → 0 ≤ A →
        A ≤ L ^ (budget * (((n + 1 : ℕ) : ℝ) + 1)) →
        0 ≤ ε → (m : ℝ) ^ 2 * ε ≤ Real.exp (-(L ^ (1/4 : ℝ))) →
        let cutoff := Nat.ceil (((2 * budget + ((E + 1) + 1) + 1) *
          ((n + 1 : ℕ) : ℝ) * Real.log L) / L ^ (1/4 : ℝ))
        ∀ v vmax decay excess : ℝ,
        (∀ g p, 0 < beta ⟨(e.symm g).val, p⟩ / V (e.symm g).val) →
        (∀ g, ∑ p, beta ⟨(e.symm g).val, p⟩ / V (e.symm g).val ≤ 2) →
        0 < ρ → 0 < v → (∀ g : Fin M, V (e.symm g).val ≤ vmax) →
        (∀ s : ↥groupsᶜ, ∑ p ∈ P s.val, 1 / (p : ℝ) = V s.val) →
        (∀ j : Fin (n + 2), 0 ≤ physicalEndpointSchedule q (n + 1) j.val) →
        (∀ j : Fin (n + 2), physicalEndpointSchedule q (n + 1) j.val ≤ 1) →
        (∀ j : Fin (n + 2), physicalEndpointSchedule q (n + 1) j.val / ρ ^ 2 +
          ((1 - physicalEndpointSchedule q (n + 1) j.val) / ρ) / v ≤ 1) →
        (∀ (j : Fin (n + 2)) (g : Fin M), physicalEndpointSchedule q (n + 1) j.val / ρ ^ 2 +
          ((1 - physicalEndpointSchedule q (n + 1) j.val) * V (e.symm g).val / ρ) / v ≤ 1) →
        0 ≤ G + Ca → decay ≤ L ^ (-G) → excess ≤ L ^ Ca →
        Real.sqrt (physicalGhostUniformEnergyBound ρ vmax v ^ M) ≤ L ^ Cv →
        (∏ g, (∑ p, beta ⟨(e.symm g).val, p⟩ / V (e.symm g).val) ^ (J + ell)) ≤ H →
        let : ∀ g (p : P (e.symm g).val), NeZero p.val :=
          fun g p => inferInstanceAs (NeZero (⟨(e.symm g).val, p⟩ : PhysicalPrime P).2.val)
        let : ∀ z : PhysicalPrime (fun s : ↥groupsᶜ => P s.val), NeZero z.2.val :=
          fun z => inferInstanceAs (NeZero (⟨z.1.val, z.2⟩ : PhysicalPrime P).2.val)
        let hPs := fun (s : ↥groupsᶜ) p hp => hP s.val p hp
        let hPb := fun (g : Fin M) p hp => hP (e.symm g).val p hp
        let hcross : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (e.symm g).val) :=
          fun s g => hdis (by intro he; exact (e.symm g).property (he ▸ s.property))
        let row := fun θ (code : BirthForestCode m) =>
          physicalRootFourierRow groups e patterns C hC k V q ζ K θ
            (fun (g : Fin M) (p : P (e.symm g).val) => beta ⟨(e.symm g).val, p⟩)
            (fun j => physicalEndpointSchedule q (n + 1) j.val) ρ hPs hPb hcross code encode
        let w := physicalSmallBigMeasure (fun s : ↥groupsᶜ => V s.val)
          (productMemoryWeight (fun g p => beta ⟨(e.symm g).val, p⟩ / V (e.symm g).val)
            (fun g => unrestrictedResidueWeight
              (fun p => beta ⟨(e.symm g).val, p⟩ / V (e.symm g).val)))
        let symmetric := fun f : PhysicalRootMixedState
            (P := P) (J := J) (ell := ell) (B := b) groups e → ℂ =>
          ∀ s, ProductMemorySymmetric (fun x => f (s, x))
        (∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ code ν, ∀ j : Fin (n + 1), ∀ f, symmetric f →
          symmetric (row θ code ν none (row θ code ν (some (.inr j)) (row θ code ν none f)))) →
        (∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ code ν, ∀ j : Fin (n + 1), ∀ f, symmetric f →
          cleanActiveNorm w (row θ code ν none (row θ code ν (some (.inr j)) (row θ code ν none f))) ≤
            (if j ∈ physicalSelectedAffectedEdges (fun _ : Fin M => J + ell) b (n + 1) code
              then excess else decay) * cleanActiveNorm w f) →
        (∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ code, cutoff ≤ birthForestRank code →
          ‖F θ code‖ ≤ A * ε ^ birthForestRank code) →
        (∀ θ ∈ Set.Icc (0 : ℝ) 1,
          ‖physicalRootNormalizedMixedScalar (n := n) (B := B)
              groups e patterns C hC V q ζ k K θ beta ρ hP hdis -
            physicalRootNormalizedMixedScalar (n := n) (B := b)
              groups e patterns C hC V q ζ k K θ beta ρ hP hdis‖ ≤ err) →
        ‖physicalRootResidueModel V patterns C q ζ k K n‖ ≤ 2 * err := by
  filter_upwards [eventually_physical_root_residue_two_regime
    (Ch := Ch) hbudget hE hD hgain, eventually_ge_atTop (1 : ℝ)] with L hmodel hL
  intro I N M J ell n b B P _ groups e V patterns C hC q ζ k K hV hP hdis hk
    baseline hb hB ρ hρ encode hinj beta m F err hq0 hq1 hsize hN hm H A ε
    hH hHb hA hAb hε hεb cutoff v vmax decay excess hμ hmass hρ0 hv hVmax hSmallMass
    hret0 hret1 hDghost hbirth hexponent hdecay hexcess hvisit hinitial
    instBig instSmall hPs hPb hcross row w symmetric hEpres hEdge hhigh hcap
  let : ∀ g (p : P (e.symm g).val), NeZero p.val :=
    fun g p => inferInstanceAs (NeZero (⟨(e.symm g).val, p⟩ : PhysicalPrime P).2.val)
  let : ∀ z : PhysicalPrime (fun s : ↥groupsᶜ => P s.val), NeZero z.2.val :=
    fun z => inferInstanceAs (NeZero (⟨z.1.val, z.2⟩ : PhysicalPrime P).2.val)
  apply hmodel I N M J ell n b B P groups e V patterns C hC q ζ k K hV hP hdis hk
    baseline hb hB ρ hρ encode hinj hq0 hq1 hsize hN hm H A ε hH hHb hA hAb hε hεb
    _ hhigh hcap
  intro θ hθ code _
  exact physical_root_low_rank_forest_contribution_power_le groups e patterns C hC k V q ζ K θ
    (fun (g : Fin M) (p : P (e.symm g).val) => beta ⟨(e.symm g).val, p⟩)
    (fun j => physicalEndpointSchedule q (n + 1) j.val) ρ hPs hPb hcross code encode
    (fun s => hV s.val) v vmax hμ hmass hρ0 (fun g => (hV (e.symm g).val).le) hVmax hv
    hinj hSmallMass hret0 hret1 hDghost hbirth hL hexponent hdecay hexcess hvisit hinitial
    (hEpres θ hθ code) (hEdge θ hθ code)

end Bounty

end


-- Source module: PhysicalRootResidueCap
section

/- The original-cap comparison is discharged from explicit polynomial
budgets, leaving the edge costs and high-rank forest estimate. -/

open Finset Filter
open scoped Classical
namespace Bounty

theorem eventually_physical_root_residue_of_edge_costs_and_cap
    {budget E G Cv Ca Ch q vs ρ v vmin vmax CG PG HG : ℝ}
    (hbudget : 0 ≤ budget) (hE : 0 ≤ E)
    (hD : 0 ≤ G + Ca + 6) (hgain : E + 1 + Cv + 2 ≤ G)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hvs : 0 < vs)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hv : 1 < v) (hvmin : 0 < vmin)
    (hCG : 0 ≤ CG) (hPG : 0 ≤ PG) (hHG : 0 ≤ HG) (J ell T : ℕ) :
    ∀ᶠ L : ℝ in atTop,
    let n := 2 * Nat.ceil (L ^ (13/25 : ℝ)) - 1
    ∀ (I : Type) (N M b B : ℕ) (P : Fin N → Finset ℕ)
      [∀ z : PhysicalPrime P, NeZero z.2.val]
      (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
      (V : Fin N → ℝ) (patterns : Finset I)
      (C : I → Fin N → Finset (Fin J))
      (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
      (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ)
      (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
        PhysicalAuxLabels P (C i) → ℂ)
      (_hV : ∀ g, 0 < V g) (hP : ∀ g p, p ∈ P g → Nat.Prime p)
      (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))
      (_hk : ∀ time < n + 1, ∀ i ∈ patterns, ∀ g p, p ∈ P g → ¬ (p : ℤ) ∣ k time i)
      (baseline : PhysicalPrime P → ℝ)
      (_hb : ∀ p : PhysicalPrime P, p.1 ∈ groups →
        baseline p = 1 - (∑ j ∈ range (n + 2), (1 - physicalEndpointSchedule q (n + 1) j)) / p.2.val)
      (_hB : (physicalPrimeGroups P groups).card ≤ B)
      (encode : ((g : Fin M) × P (e.symm g).val) → ℤ)
      (_hinj : Function.Injective encode),
      let beta := fun p : PhysicalPrime P => ((p.2.val : ℝ) * baseline p)⁻¹
      let m := Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) b
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))
      let F := fun (θ : ℝ) (code : BirthForestCode m) =>
        physicalRootForestContribution groups e patterns C hC k V q ζ K θ
          (fun (g : Fin M) (p : P (e.symm g).val) => beta ⟨(e.symm g).val, p⟩)
          (fun j => physicalEndpointSchedule q (n + 1) j.val) ρ code
      let err := L ^ (-((E + 1) * ((n + 1 : ℕ) : ℝ)))
      (∀ p : PhysicalPrime P, p.1 ∈ groups → 2 * (n + 2) ≤ p.2.val) →
      L ^ (1/2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) → (m : ℝ) ≤ L ^ (6 : ℝ) →
      ∀ H A ε : ℝ,
        0 ≤ H → H ≤ L ^ Ch → 0 ≤ A →
        A ≤ L ^ (budget * (((n + 1 : ℕ) : ℝ) + 1)) →
        0 ≤ ε → (m : ℝ) ^ 2 * ε ≤ Real.exp (-(L ^ (1/4 : ℝ))) →
        let cutoff := Nat.ceil (((2 * budget + ((E + 1) + 1) + 1) *
          ((n + 1 : ℕ) : ℝ) * Real.log L) / L ^ (1/4 : ℝ))
        ∀ decay excess : ℝ,
        (∀ g p, 0 < beta ⟨(e.symm g).val, p⟩ / V (e.symm g).val) →
        (∀ g, ∑ p, beta ⟨(e.symm g).val, p⟩ / V (e.symm g).val ≤ 2) →
        (∀ g : Fin M, V (e.symm g).val ≤ vmax) →
        (∀ s : ↥groupsᶜ, ∑ p ∈ P s.val, 1 / (p : ℝ) = V s.val) →
        (∀ j : Fin (n + 2), 0 ≤ physicalEndpointSchedule q (n + 1) j.val) →
        (∀ j : Fin (n + 2), physicalEndpointSchedule q (n + 1) j.val ≤ 1) →
        (∀ j : Fin (n + 2), physicalEndpointSchedule q (n + 1) j.val / ρ ^ 2 +
          ((1 - physicalEndpointSchedule q (n + 1) j.val) / ρ) / v ≤ 1) →
        (∀ (j : Fin (n + 2)) (g : Fin M), physicalEndpointSchedule q (n + 1) j.val / ρ ^ 2 +
          ((1 - physicalEndpointSchedule q (n + 1) j.val) * V (e.symm g).val / ρ) / v ≤ 1) →
        0 ≤ G + Ca → decay ≤ L ^ (-G) → excess ≤ L ^ Ca →
        Real.sqrt (physicalGhostUniformEnergyBound ρ vmax v ^ M) ≤ L ^ Cv →
        (∏ g, (∑ p, beta ⟨(e.symm g).val, p⟩ / V (e.symm g).val) ^ (J + ell)) ≤ H →
        let : ∀ g (p : P (e.symm g).val), NeZero p.val :=
          fun g p => inferInstanceAs (NeZero (⟨(e.symm g).val, p⟩ : PhysicalPrime P).2.val)
        let : ∀ z : PhysicalPrime (fun s : ↥groupsᶜ => P s.val), NeZero z.2.val :=
          fun z => inferInstanceAs (NeZero (⟨z.1.val, z.2⟩ : PhysicalPrime P).2.val)
        let hPs := fun (s : ↥groupsᶜ) p hp => hP s.val p hp
        let hPb := fun (g : Fin M) p hp => hP (e.symm g).val p hp
        let hcross : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (e.symm g).val) :=
          fun s g => hdis (by intro he; exact (e.symm g).property (he ▸ s.property))
        let row := fun θ (code : BirthForestCode m) =>
          physicalRootFourierRow groups e patterns C hC k V q ζ K θ
            (fun (g : Fin M) (p : P (e.symm g).val) => beta ⟨(e.symm g).val, p⟩)
            (fun j => physicalEndpointSchedule q (n + 1) j.val) ρ hPs hPb hcross code encode
        let w := physicalSmallBigMeasure (fun s : ↥groupsᶜ => V s.val)
          (productMemoryWeight (fun g p => beta ⟨(e.symm g).val, p⟩ / V (e.symm g).val)
            (fun g => unrestrictedResidueWeight
              (fun p => beta ⟨(e.symm g).val, p⟩ / V (e.symm g).val)))
        let symmetric := fun f : PhysicalRootMixedState
            (P := P) (J := J) (ell := ell) (B := b) groups e → ℂ =>
          ∀ s, ProductMemorySymmetric (fun x => f (s, x))
        (∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ code ν, ∀ j : Fin (n + 1), ∀ f, symmetric f →
          symmetric (row θ code ν none (row θ code ν (some (.inr j)) (row θ code ν none f)))) →
        (∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ code ν, ∀ j : Fin (n + 1), ∀ f, symmetric f →
          cleanActiveNorm w (row θ code ν none (row θ code ν (some (.inr j)) (row θ code ν none f))) ≤
            (if j ∈ physicalSelectedAffectedEdges (fun _ : Fin M => J + ell) b (n + 1) code
              then excess else decay) * cleanActiveNorm w f) →
        (∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ code, cutoff ≤ birthForestRank code →
          ‖F θ code‖ ≤ A * ε ^ birthForestRank code) →
        L ≤ (b : ℝ) → b ≤ B →
        (Fintype.card ↥groupsᶜ : ℝ) ≤ CG * Real.log L →
        (M : ℝ) ≤ CG * Real.log L → (Fintype.card ↥patterns : ℝ) ≤ L ^ PG →
        (∀ s : ↥groupsᶜ, vs ≤ V s.val) →
        (∀ g, ∑ p ∈ P g, 1 / (p : ℝ) = V g) →
        (∀ g : Fin M, vmin ≤ V (e.symm g).val) →
        (∀ (j : Fin (n + 2)) (g : Fin M), physicalEndpointSchedule q (n + 1) j.val / ρ ^ 2 +
          ((1 - physicalEndpointSchedule q (n + 1) j.val) * (2 * V (e.symm g).val) / ρ) / v ≤ 1) →
        (∀ (i : patterns) (g : Fin M),
          (physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val))ᶜ.card ≤ T) →
        ∀ Hkernel : ℝ, 1 ≤ Hkernel → Hkernel ≤ L ^ HG →
        (∀ time < n + 1, ∀ i ∈ patterns, ∀ U W aux, ‖K time i U W aux‖ ≤ Hkernel) →
        ‖physicalRootResidueModel V patterns C q ζ k K n‖ ≤ 2 * err := by
  filter_upwards [eventually_physical_root_residue_of_edge_costs
    (Ch := Ch) hbudget hE hD hgain,
    eventually_original_root_scalar_cap_error (ρ := ρ) (v := v) (vmin := vmin) (vmax := vmax)
      hq0 hq1 hvs hCG hPG hHG (by linarith : 0 ≤ E + 1) J ell T,
    eventually_ge_atTop (1 : ℝ)] with L hmodel hcap hL
  intro n I N M b B P _ groups e V patterns C hC ζ k K hV hP hdis hk
    baseline hb hB encode hinj beta m F err hsize hN hm H A ε
    hH hHb hA hAb hε hεb cutoff decay excess hμ hmass hVmax hSmallMass
    hret0 hret1 hDghost hbirth hexponent hdecay hexcess hvisit hinitial
    instBig instSmall hPs hPb hcross row w symmetric hEpres hEdge hhigh
    hbL hbB hsmallLog hbigLog hpatterns hVs hMass hVmin hCghost hT Hkernel hHkernel hHkernelPow hK
  have hceil : 1 ≤ Nat.ceil (L ^ (13/25 : ℝ)) := by
    have hpow : 1 ≤ L ^ (13/25 : ℝ) := Real.one_le_rpow hL (by norm_num)
    have hh := hpow.trans (Nat.le_ceil (L ^ (13/25 : ℝ)))
    exact_mod_cast hh
  have hn : n + 1 = 2 * Nat.ceil (L ^ (13/25 : ℝ)) := by dsimp only [n]; omega
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hpower : (L ^ (-(E + 1))) ^ (2 * Nat.ceil (L ^ (13/25 : ℝ))) = err := by
    dsimp only [err]
    rw [hn, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    congr 1
    ring
  apply hmodel I N M J ell n b B P groups e V patterns C hC q ζ k K hV hP hdis hk
    baseline hb hB ρ hρ0.ne' encode hinj hq0 hq1.le hsize hN hm H A ε hH hHb hA hAb hε hεb
    v vmax decay excess hμ hmass hρ0 (zero_lt_one.trans hv) hVmax hSmallMass
    hret0 hret1 hDghost hbirth hexponent hdecay hexcess hvisit hinitial
    hEpres hEdge hhigh
  intro θ _
  exact (hcap I N M b B P groups e patterns C hC V ζ k K θ beta hP hdis
    hbL hbB hsmallLog hbigLog hpatterns hVs hV hMass hρ0 hρ1 hv hvmin hVmin hVmax
    hμ hmass hret0 hret1 hDghost hCghost hT Hkernel hHkernel hHkernelPow hK).trans_eq hpower

end Bounty

end


-- Source module: SmallCompletionRow
section

/- Uniform positive row bounds for the actual small-completion kernel.
The translated residue may depend arbitrarily on the big event. -/

open Finset
open scoped Classical
namespace Bounty

theorem physical_small_vertex_le_one {G : Type*} [Fintype G]
    {P : G → Finset ℕ} {J ell : ℕ} (L : PhysicalMarkLists P J ell)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (r : PhysicalResidues P) :
    physicalResidueVertexWeight L q r ≤ 1 := by
  unfold physicalResidueVertexWeight
  split_ifs
  · exact prod_le_one₀ (fun _ _ => pow_nonneg hq0 _)
      (fun _ _ => pow_le_one₀ hq0 hq1)
  · exact zero_le_one

theorem exists_physical_small_completion_row_bound {qmax v : ℝ}
    (hqmax0 : 0 ≤ qmax) (hqmax1 : qmax < 1) (hv : 0 < v) (ell : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (G : Type) [Fintype G]
      (P : G → Finset ℕ) (J : ℕ) (V : G → ℝ), (∀ g, v ≤ V g) →
      ∀ (q : ℝ), 0 ≤ q → q ≤ qmax →
      ∀ (r r' : PhysicalResidues P) (L : PhysicalMarkLists P J ell),
      (∑ R : PhysicalMarkLists P J ell,
        if physicalSharedPrefix L = physicalSharedPrefix R then
          physicalCompletionMass V (fun _ => (∅ : Finset (Fin J))) ell *
            (physicalResidueVertexWeight L q r * physicalResidueVertexWeight R q r')
        else 0) ≤ A ^ Fintype.card G := by
  obtain ⟨A, hA, hbound⟩ := exists_small_completion_energy_bound hqmax0 hqmax1 hv ell
  refine ⟨A, hA, ?_⟩
  intro G _ P J V hV q hq0 hqmax r r' L
  let C := physicalCompletionMass V (fun _ => (∅ : Finset (Fin J))) ell
  let d := physicalSharedPrefix L
  let F := (univ : Finset (PhysicalMarkLists P J ell)).filter
    (fun R => physicalResidueMarksValid r' R ∧ physicalSharedPrefix R = d)
  let w := ∏ g, q ^ (physicalResidueOmega P g r' - (J + ell))
  have hC : 0 ≤ C := (physical_completion_mass_pos V _ ell
    (fun g => hv.trans_le (hV g))).le
  have hleft1 : physicalResidueVertexWeight L q r ≤ 1 :=
    physical_small_vertex_le_one L hq0 (hqmax.trans hqmax1.le) r
  have hsum : (∑ R : PhysicalMarkLists P J ell,
        if physicalSharedPrefix L = physicalSharedPrefix R then
          C * (physicalResidueVertexWeight L q r * physicalResidueVertexWeight R q r')
        else 0) = C * physicalResidueVertexWeight L q r * w * (F.card : ℝ) := by
    calc
      _ = ∑ R ∈ F, C * physicalResidueVertexWeight L q r * w := by
        rw [sum_filter]
        apply sum_congr rfl
        intro R _
        simp only [physicalResidueVertexWeight, d, w]
        by_cases hp : physicalSharedPrefix L = physicalSharedPrefix R
        · by_cases hr : physicalResidueMarksValid r' R
          · simp only [hp, hr, if_true, and_self, mul_assoc]
          · simp only [hp, hr, if_true, if_false, false_and, mul_zero]
        · have hp' : ¬physicalSharedPrefix R = physicalSharedPrefix L := Ne.symm hp
          simp only [hp, hp', if_false, and_false]
      _ = _ := by rw [sum_const, nsmul_eq_mul]; ring
  rw [show (∑ R : PhysicalMarkLists P J ell,
        if physicalSharedPrefix L = physicalSharedPrefix R then
          physicalCompletionMass V (fun _ => (∅ : Finset (Fin J))) ell *
            (physicalResidueVertexWeight L q r * physicalResidueVertexWeight R q r')
        else 0) = C * physicalResidueVertexWeight L q r * w * (F.card : ℝ) from hsum]
  by_cases hF : F.Nonempty
  · obtain ⟨R, hR⟩ := hF
    have hvalid : physicalResidueMarksValid r' R := (mem_filter.mp hR).2.1
    have hd : physicalResidueSharedValid r' d := by
      rw [← (mem_filter.mp hR).2.2]
      exact physical_shared_prefix_valid r' ⟨R, hvalid⟩
    have hc : (F.card : ℝ) = ∏ g, ((physicalResidueOmega P g r' - J).descFactorial ell : ℝ) := by
      have hc := physical_residue_shared_filter_card P J ell r' d
      rw [if_pos hd] at hc
      exact_mod_cast hc
    have hw : w ≤ ∏ g, qmax ^ (physicalResidueOmega P g r' - (J + ell)) := by
      apply prod_le_prod₀
      · intro g _
        exact pow_nonneg hq0 _
      · intro g _
        exact pow_le_pow_left₀ hq0 hqmax _
    calc
      _ ≤ C * 1 * (∏ g, qmax ^ (physicalResidueOmega P g r' - (J + ell))) * (F.card : ℝ) := by
        gcongr
      _ = C * (∏ g, qmax ^ (physicalResidueOmega P g r' - (J + ell))) *
          (∏ g, ((physicalResidueOmega P g r' - J).descFactorial ell : ℝ)) := by rw [hc, mul_one]
      _ ≤ _ := hbound G J V hV (fun g => physicalResidueOmega P g r')
        (physical_residue_slots_le_omega P J ell r' ⟨R, hvalid⟩)
  · rw [not_nonempty_iff_eq_empty.mp hF, card_empty, Nat.cast_zero, mul_zero]
    exact pow_nonneg (zero_le_one.trans hA) _

end Bounty

end


-- Source module: SmallCompletionSelectedRow
section

/- Summing the genuine small kernel preserves every nonnegative selector
on the big event, including the causal birth-forest selector. -/

open Finset
open scoped Classical
namespace Bounty

theorem exists_physical_small_selected_row_bound {qmax v : ℝ}
    (hqmax0 : 0 ≤ qmax) (hqmax1 : qmax < 1) (hv : 0 < v) (ell : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (G : Type) [Fintype G]
      (P : G → Finset ℕ) (J : ℕ) (V : G → ℝ), (∀ g, v ≤ V g) →
      ∀ (q : ℝ), 0 ≤ q → q ≤ qmax →
      ∀ (E : Type) [Fintype E] (r : PhysicalResidues P)
        (r' : E → PhysicalResidues P) (L : PhysicalMarkLists P J ell)
        (selector : E → ℝ), (∀ e, 0 ≤ selector e) →
      (∑ e : E, ∑ R : PhysicalMarkLists P J ell,
        (if physicalSharedPrefix L = physicalSharedPrefix R then
          physicalCompletionMass V (fun _ => (∅ : Finset (Fin J))) ell *
            (physicalResidueVertexWeight L q r * physicalResidueVertexWeight R q (r' e))
        else 0) * selector e) ≤ A ^ Fintype.card G * ∑ e : E, selector e := by
  obtain ⟨A, hA, hrow⟩ := exists_physical_small_completion_row_bound hqmax0 hqmax1 hv ell
  refine ⟨A, hA, ?_⟩
  intro G _ P J V hV q hq0 hqmax E _ r r' L selector hselector
  rw [mul_sum]
  apply sum_le_sum
  intro e _
  rw [← sum_mul]
  exact mul_le_mul_of_nonneg_right
    (hrow G P J V hV q hq0 hqmax r (r' e) L) (hselector e)

end Bounty

end


-- Source module: SmallBigSelectedRow
section

/- The original mixed edge preserves any nonnegative big-event selector
when its outgoing small marks are summed. -/

open Finset
open scoped Classical
namespace Bounty

theorem exists_physical_small_big_selected_row_bound {qmax v : ℝ}
    (hqmax0 : 0 ≤ qmax) (hqmax1 : qmax < 1) (hv : 0 < v) (ell : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (S X : Type) [Fintype S]
      (Ps : S → Finset ℕ) (J : ℕ) (Vs : S → ℝ), (∀ g, v ≤ Vs g) →
      ∀ (q : ℝ), Real.sqrt q ≤ qmax →
      ∀ (E : PhysicalSharedLists Ps J → X → Type) [∀ d x, Fintype (E d x)]
        (a : PhysicalResidues Ps → ∀ d x, E d x → ℝ) (k : X → ℤ)
        (s : PhysicalSmallBigState Ps J ell X)
        (selector : E (physicalSharedPrefix s.1.2) s.2 → ℝ),
      (∀ e, 0 ≤ selector e) →
      (∑ e : PhysicalSmallBigEvent E s,
        |physicalSmallBigPositiveWeight Vs q E a k s e| * selector e.2) ≤
      A ^ Fintype.card S * ∑ e : E (physicalSharedPrefix s.1.2) s.2,
        |a s.1.1 (physicalSharedPrefix s.1.2) s.2 e| * selector e := by
  obtain ⟨A, hA, hrow⟩ := exists_physical_small_selected_row_bound hqmax0 hqmax1 hv ell
  refine ⟨A, hA, ?_⟩
  intro S X _ Ps J Vs hVs q hq E _ a k s selector hselector
  have hVs0 : ∀ g, 0 < Vs g := fun g => hv.trans_le (hVs g)
  have hC : 0 ≤ physicalCompletionMass Vs (fun _ => (∅ : Finset (Fin J))) ell :=
    (physical_completion_mass_pos Vs _ ell hVs0).le
  have hnonneg (R : PhysicalMarkLists Ps J ell) :
      0 ≤ physicalCompletionMass Vs (fun _ => (∅ : Finset (Fin J))) ell *
        (physicalResidueVertexWeight s.1.2 (Real.sqrt q) s.1.1 *
          physicalResidueVertexWeight R (Real.sqrt q)
            (physicalTranslateResidues s.1.1
              (k s.2 * (physicalSharedProduct (physicalSharedPrefix s.1.2) : ℕ)))) :=
    mul_nonneg hC (mul_nonneg
      (physical_residue_vertex_weight_nonneg _ (Real.sqrt_nonneg q) _)
      (physical_residue_vertex_weight_nonneg _ (Real.sqrt_nonneg q) _))
  have hb := hrow S Ps J Vs hVs (Real.sqrt q) (Real.sqrt_nonneg q) hq
    (E (physicalSharedPrefix s.1.2) s.2) s.1.1
    (fun _ => physicalTranslateResidues s.1.1
      (k s.2 * (physicalSharedProduct (physicalSharedPrefix s.1.2) : ℕ))) s.1.2
    (fun e => |a s.1.1 (physicalSharedPrefix s.1.2) s.2 e| * selector e)
    (fun e => mul_nonneg (abs_nonneg _) (hselector e))
  refine le_trans (le_of_eq ?_) hb
  rw [show (∑ e : PhysicalSmallBigEvent E s,
      |physicalSmallBigPositiveWeight Vs q E a k s e| * selector e.2) =
      ∑ R : PhysicalMarkLists Ps J ell,
        ∑ e : E (physicalSharedPrefix s.1.2) s.2,
          |physicalSmallBigPositiveWeight Vs q E a k s (R, e)| * selector e by
    exact Fintype.sum_prod_type _]
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  apply sum_congr rfl
  intro R _
  unfold physicalSmallBigPositiveWeight
  split_ifs
  · rw [abs_mul, abs_of_nonneg (hnonneg R), mul_assoc]
  · simp only [abs_zero, zero_mul]

end Bounty

end


-- Source module: PhysicalMixedSelectedEdgeRow
section

/- Selected rows of the literal original mixed edge. The outgoing small
marks are summed while every pattern, auxiliary and big-event selector stays. -/

open Finset
open scoped Classical
namespace Bounty

theorem exists_physical_mixed_selected_edge_row_bound {qmax vs : ℝ}
    (hqmax0 : 0 ≤ qmax) (hqmax1 : qmax < 1) (hvs : 0 < vs) (ell : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (S G I V K : Type) [Fintype S] [Fintype G] [DecidableEq G]
      [Fintype I] (Ps : S → Finset ℕ) (P : G → Type) [∀ g, Fintype (P g)]
      (n : ∀ g, P g → ℕ) [∀ g p, NeZero (n g p)] (J : ℕ) (M : G → ℕ)
      (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ)
      (A : I → Type) [∀ i, Fintype (A i)]
      (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J → SharedActiveLabels P (shared i) → A i → G → ℤ)
      (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)
      (ω : ∀ i, SharedActiveLabels P (shared i) → A i → ℝ)
      (μ : ∀ g, P g → ℝ) (qghost : V → ℝ) (ρ : ℝ) (Vb : G → ℝ)
      (Vs : S → ℝ) (qedge : K → ℝ), (∀ s, vs ≤ Vs s) →
      ∀ (k : K), Real.sqrt (qedge k) ≤ qmax →
      ∀ (s : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B)
      (selector : ∀ i a, PhysicalSmallBigFullEvent n (shared i) B
        (fun d c => Δ k i d c a) (fun d c => D k i d c a)
        (physicalSharedPrefix s.1.2) s.2 → ℝ),
      (∀ i a e, 0 ≤ selector i a e) →
      (∑ e : PhysicalMixedWordEdge n shared B A Δ D k s,
        |physicalMixedWordWeight n shared B A Δ D kbig ω μ qghost ρ Vb Vs qedge
          (some (.inr k)) s e| * selector e.1 e.2.1 e.2.2.2) ≤
      C ^ Fintype.card S * ∑ i, ∑ a,
        |ω i (productActiveMemorySplit (shared i) B s.2).1 a| *
        ∑ e : PhysicalSmallBigFullEvent n (shared i) B
          (fun d c => Δ k i d c a) (fun d c => D k i d c a)
          (physicalSharedPrefix s.1.2) s.2,
          |physicalSmallBigFullWeight n (shared i) B
            (fun d c => Δ k i d c a) (fun d c => D k i d c a) μ ρ Vb
            s.1.1 (physicalSharedPrefix s.1.2) s.2 e| * selector i a e := by
  obtain ⟨C, hC, hrow⟩ := exists_physical_small_big_selected_row_bound hqmax0 hqmax1 hvs ell
  refine ⟨C, hC, ?_⟩
  intro S G I V K _ _ _ _ Ps P _ n _ J M shared B A _ Δ D kbig ω μ qghost ρ Vb Vs qedge hVs k hq s selector hselector
  rw [show (∑ e : PhysicalMixedWordEdge n shared B A Δ D k s,
      |physicalMixedWordWeight n shared B A Δ D kbig ω μ qghost ρ Vb Vs qedge
        (some (.inr k)) s e| * selector e.1 e.2.1 e.2.2.2) =
      ∑ i, ∑ a, ∑ e : PhysicalSmallBigEvent
        (PhysicalSmallBigFullEvent n (shared i) B
          (fun d c => Δ k i d c a) (fun d c => D k i d c a)) s,
        |physicalMixedWordWeight n shared B A Δ D kbig ω μ qghost ρ Vb Vs qedge
          (some (.inr k)) s ⟨i,a,e⟩| * selector i a e.2 by
    exact (Fintype.sum_sigma _).trans (sum_congr rfl fun _ _ => Fintype.sum_sigma _)]
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  rw [mul_sum]
  apply sum_le_sum
  intro a _
  have hb := hrow S
    (ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    Ps J Vs hVs (qedge k) hq
    (PhysicalSmallBigFullEvent n (shared i) B
      (fun d c => Δ k i d c a) (fun d c => D k i d c a))
    (physicalSmallBigFullWeight n (shared i) B
      (fun d c => Δ k i d c a) (fun d c => D k i d c a) μ ρ Vb)
    (fun x => kbig k i (productActiveMemorySplit (shared i) B x).1 a)
    s (selector i a) (hselector i a)
  calc
    _ = |ω i (productActiveMemorySplit (shared i) B s.2).1 a| *
        ∑ e : PhysicalSmallBigEvent (PhysicalSmallBigFullEvent n (shared i) B
          (fun d c => Δ k i d c a) (fun d c => D k i d c a)) s,
          |physicalSmallBigPositiveWeight Vs (qedge k) _
            (physicalSmallBigFullWeight n (shared i) B
              (fun d c => Δ k i d c a) (fun d c => D k i d c a) μ ρ Vb)
            (fun x => kbig k i (productActiveMemorySplit (shared i) B x).1 a) s e| *
            selector i a e.2 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro e _
      simp only [physicalMixedWordWeight, abs_mul, mul_assoc]
    _ ≤ |ω i (productActiveMemorySplit (shared i) B s.2).1 a| *
        (C ^ Fintype.card S * _) := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = _ := by ring

end Bounty

end


-- Source module: FullMixedShapeHistory
section

/- Causal common-forest history is determined by the capacity shape and the
current optional birth labels, not by the decorated event key. -/

open scoped Classical
namespace Bounty
section Shape
variable {Z : Type*} {N : ℕ} (M : Fin N → ℕ)

noncomputable def fullMixedShapeHistoryWrite (s : FullMixedCommonShapeData N)
    (u : Fin s.1) (label : FullMixedShapeLocalAddress s u → Option Z)
    (history : Fin (Fintype.card (FullMixedCommonShapeAddress M s)) → Option Z)
    (i : Fin (Fintype.card (FullMixedCommonShapeAddress M s))) : Option Z :=
  match fullMixedCommonShapeOrder M s i with
  | .inl _ => history i
  | .inr a => if h : a.1 = u then
      label (cast (congrArg (FullMixedShapeLocalAddress s) h) a.2)
    else history i

noncomputable def fullMixedShapeHistoryGain (s : FullMixedCommonShapeData N)
    (code : BirthForestCode (Fintype.card (FullMixedCommonShapeAddress M s)))
    (u : Fin s.1) (label : FullMixedShapeLocalAddress s u → Option Z)
    (history : Fin (Fintype.card (FullMixedCommonShapeAddress M s)) → Option Z) : ℝ :=
  if birthForestStageCondition (fullMixedShapeIndexStage M s) u.succ
    (fullMixedShapeHistoryWrite M s u label history) code then 1 else 0

theorem full_mixed_shape_history_gain_nonneg (s : FullMixedCommonShapeData N)
    (code : BirthForestCode (Fintype.card (FullMixedCommonShapeAddress M s)))
    (u : Fin s.1) (label : FullMixedShapeLocalAddress s u → Option Z)
    (history : Fin (Fintype.card (FullMixedCommonShapeAddress M s)) → Option Z) :
    0 ≤ fullMixedShapeHistoryGain M s code u label history := by
  unfold fullMixedShapeHistoryGain
  split_ifs <;> norm_num

theorem full_mixed_shape_history_write_heq
    {s t : FullMixedCommonShapeData N} (h : s = t)
    {u : Fin s.1} {v : Fin t.1} (huv : HEq u v)
    {label : FullMixedShapeLocalAddress s u → Option Z}
    {label' : FullMixedShapeLocalAddress t v → Option Z} (hl : HEq label label')
    {history : Fin (Fintype.card (FullMixedCommonShapeAddress M s)) → Option Z}
    {history' : Fin (Fintype.card (FullMixedCommonShapeAddress M t)) → Option Z}
    (hh : HEq history history') :
    HEq (fullMixedShapeHistoryWrite M s u label history)
      (fullMixedShapeHistoryWrite M t v label' history') := by
  cases h
  cases eq_of_heq huv
  cases eq_of_heq hl
  cases eq_of_heq hh
  rfl

theorem full_mixed_shape_history_gain_eq
    {s t : FullMixedCommonShapeData N} (h : s = t)
    {code : BirthForestCode (Fintype.card (FullMixedCommonShapeAddress M s))}
    {code' : BirthForestCode (Fintype.card (FullMixedCommonShapeAddress M t))}
    (hc : HEq code code')
    {u : Fin s.1} {v : Fin t.1} (huv : HEq u v)
    {label : FullMixedShapeLocalAddress s u → Option Z}
    {label' : FullMixedShapeLocalAddress t v → Option Z} (hl : HEq label label')
    {history : Fin (Fintype.card (FullMixedCommonShapeAddress M s)) → Option Z}
    {history' : Fin (Fintype.card (FullMixedCommonShapeAddress M t)) → Option Z}
    (hh : HEq history history') :
    fullMixedShapeHistoryGain M s code u label history =
      fullMixedShapeHistoryGain M t code' v label' history' := by
  cases h
  cases eq_of_heq hc
  cases eq_of_heq huv
  cases eq_of_heq hl
  cases eq_of_heq hh
  rfl

end Shape
section Original
variable {I K : Type*} {N : ℕ} {P : Fin N → Type*} {M : Fin N → ℕ}
  (n : ∀ g, P g → ℕ) (S : K → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (A : ∀ k, SharedActiveLabels P (S k) → Type*)
  (Δ D : ∀ k c, A k c → Fin N → ℤ) (steps : List (Option (I ⊕ K)))

theorem full_mixed_common_history_write_shape (u : Fin steps.length)
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (e : FullPermutationMixedEvent n S B A Δ D (steps.get u) x)
    (history : Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) → Option (Sigma P)) :
    fullMixedCommonHistoryWrite n S B A Δ D steps u x e history =
      fullMixedShapeHistoryWrite M (fullMixedCommonShape M B steps) u
        (fullMixedCommonEventBirthLabel n S B A Δ D (steps.get u) x e) history := by
  funext i
  unfold fullMixedCommonHistoryWrite fullMixedCommonAddressWrite fullMixedShapeHistoryWrite
  rw [full_mixed_common_order_shape]
  cases h : fullMixedCommonShapeOrder M (fullMixedCommonShape M B steps) i with
  | inl a =>
    dsimp only
    have hi : (fullMixedCommonShapeOrder M (fullMixedCommonShape M B steps)).symm (.inl a) = i := by
      rw [← h]
      exact (fullMixedCommonShapeOrder M (fullMixedCommonShape M B steps)).symm_apply_apply i
    exact congrArg history hi
  | inr a =>
    dsimp only
    have hi : (fullMixedCommonShapeOrder M (fullMixedCommonShape M B steps)).symm (.inr a) = i := by
      rw [← h]
      exact (fullMixedCommonShapeOrder M (fullMixedCommonShape M B steps)).symm_apply_apply i
    split_ifs <;> first | rfl | contradiction | exact congrArg history hi

theorem full_mixed_common_history_gain_shape
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
    (u : Fin steps.length)
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (e : FullPermutationMixedEvent n S B A Δ D (steps.get u) x)
    (history : Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) → Option (Sigma P)) :
    fullMixedCommonForestHistoryGain n S B A Δ D steps code u.val (steps.get u) x e history =
      fullMixedShapeHistoryGain M (fullMixedCommonShape M B steps) code u
        (fullMixedCommonEventBirthLabel n S B A Δ D (steps.get u) x e) history := by
  rw [full_mixed_common_forest_history_gain_owner,
    full_mixed_common_history_write_shape, full_mixed_index_stage_shape]
  rfl

end Original
end Bounty

end


-- Source module: PhysicalCommonHistoryGain
section

/- The common forest history on the original schedule, evaluated on a
current decorated big event. Outgoing small marks do not affect this gain. -/

open scoped Classical
namespace Bounty
section History
variable {S I V K : Type} {N : ℕ}
  {Ps : S → Finset ℕ} {P : Fin N → Type}
  (n : ∀ g, P g → ℕ) {J ell : ℕ} {M : Fin N → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (A : I → Type)
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J →
    SharedActiveLabels P (shared i) → A i → Fin N → ℤ)

noncomputable def physicalDecoratedCommonLocalLabel
    (tag : Option (V ⊕ PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K)))
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (e : PhysicalMixedDecoratedBigEvent n shared B A Δ D tag x) :
    FullMixedCommonLocalAddress M B (physicalMixedBigTagErase tag) → Option (Sigma P) :=
  fun a => fullMixedCommonEventBirthLabel n
    (fun key : PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K) => shared key.2.1) B
    (fun key _ => A key.2.1)
    (fun key c a => Δ key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)
    (fun key c a => D key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)
    tag x e (physicalMixedTagBirthAddressEquiv M B tag a)

noncomputable def physicalDecoratedCommonHistoryWrite
    (steps : List (Option (V ⊕ K))) (t : ℕ)
    (tag : Option (V ⊕ PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K)))
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (e : PhysicalMixedDecoratedBigEvent n shared B A Δ D tag x)
    (history : Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) → Option (Sigma P)) :
    Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) → Option (Sigma P) :=
  if ht : t < steps.length then
    if htag : physicalMixedBigTagErase tag = steps.get ⟨t, ht⟩ then
      fullMixedShapeHistoryWrite M (fullMixedCommonShape M B steps) ⟨t, ht⟩
        (fun a => physicalDecoratedCommonLocalLabel n shared B A Δ D tag x e
          (cast (congrArg (FullMixedCommonLocalAddress M B) htag.symm) a)) history
    else history
  else history

noncomputable def physicalDecoratedCommonHistoryGain
    (steps : List (Option (V ⊕ K)))
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
    (t : ℕ)
    (tag : Option (V ⊕ PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K)))
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (e : PhysicalMixedDecoratedBigEvent n shared B A Δ D tag x)
    (history : Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) → Option (Sigma P)) : ℝ :=
  if ht : t < steps.length then
    if physicalMixedBigTagErase tag = steps.get ⟨t, ht⟩ then
      if birthForestStageCondition (fullMixedCommonIndexStage M B steps) (Fin.succ ⟨t, ht⟩)
        (physicalDecoratedCommonHistoryWrite n shared B A Δ D steps t tag x e history) code
      then 1 else 0
    else 0
  else 0

theorem physical_decorated_common_history_write_owner
    (steps : List (Option (V ⊕ K)))
    (u : Fin steps.length)
    (tag : Option (V ⊕ PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K)))
    (htag : physicalMixedBigTagErase tag = steps.get u)
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (e : PhysicalMixedDecoratedBigEvent n shared B A Δ D tag x)
    (history : Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) → Option (Sigma P)) :
    physicalDecoratedCommonHistoryWrite n shared B A Δ D steps u.val tag x e history =
      fullMixedShapeHistoryWrite M (fullMixedCommonShape M B steps) u
        (fun a => physicalDecoratedCommonLocalLabel n shared B A Δ D tag x e
          (cast (congrArg (FullMixedCommonLocalAddress M B) htag.symm) a)) history := by
  unfold physicalDecoratedCommonHistoryWrite
  rw [dif_pos u.isLt]
  exact dif_pos htag

theorem physical_decorated_common_history_gain_owner
    (steps : List (Option (V ⊕ K)))
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
    (u : Fin steps.length)
    (tag : Option (V ⊕ PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K)))
    (htag : physicalMixedBigTagErase tag = steps.get u)
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (e : PhysicalMixedDecoratedBigEvent n shared B A Δ D tag x)
    (history : Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) → Option (Sigma P)) :
    physicalDecoratedCommonHistoryGain n shared B A Δ D steps code u.val tag x e history =
      fullMixedShapeHistoryGain M (fullMixedCommonShape M B steps) code u
        (fun a => physicalDecoratedCommonLocalLabel n shared B A Δ D tag x e
          (cast (congrArg (FullMixedCommonLocalAddress M B) htag.symm) a)) history := by
  unfold physicalDecoratedCommonHistoryGain
  rw [dif_pos u.isLt, if_pos htag,
    physical_decorated_common_history_write_owner n shared B A Δ D steps u tag htag,
    full_mixed_index_stage_shape]
  rfl

theorem physical_decorated_common_history_gain_nonneg
    (steps : List (Option (V ⊕ K)))
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
    (t : ℕ)
    (tag : Option (V ⊕ PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K)))
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (e : PhysicalMixedDecoratedBigEvent n shared B A Δ D tag x)
    (history : Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) → Option (Sigma P)) :
    0 ≤ physicalDecoratedCommonHistoryGain n shared B A Δ D steps code t tag x e history := by
  unfold physicalDecoratedCommonHistoryGain
  split_ifs <;> norm_num

theorem physical_decorated_common_history_gain_small_target_independent
    (steps : List (Option (V ⊕ K)))
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
    (t : ℕ) (k : K) (i : I) (L R R' : PhysicalMarkLists Ps J ell)
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (e : PhysicalMixedDecoratedBigEvent (V := V) n shared B A Δ D (some (.inr (k, i, L, R))) x)
    (history : Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) → Option (Sigma P)) :
    physicalDecoratedCommonHistoryGain n shared B A Δ D steps code t
      (some (.inr (k, i, L, R))) x e history =
    physicalDecoratedCommonHistoryGain n shared B A Δ D steps code t
      (some (.inr (k, i, L, R'))) x e history := by
  rfl

end History
end Bounty

end


-- Source module: FullMixedShapeHistorySeed
section

/- Initial common birth histories depend only on the common capacity shape. -/

namespace Bounty
section Seed
variable {N : ℕ} {P : Fin N → Type*} {M : Fin N → ℕ}
  (n : ∀ g, P g → ℕ) (B : ℕ)

noncomputable def fullMixedShapeHistorySeed (shape : FullMixedCommonShapeData N)
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (history : Fin (Fintype.card (FullMixedCommonShapeAddress M shape)) → Option (Sigma P))
    (i : Fin (Fintype.card (FullMixedCommonShapeAddress M shape))) : Option (Sigma P) :=
  match fullMixedCommonShapeOrder M shape i with
  | .inl a => some (fullMixedCommonInitialPrime x a)
  | .inr _ => history i

theorem full_mixed_shape_history_seed_heq
    {shape shape' : FullMixedCommonShapeData N} (h : shape = shape')
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    {history : Fin (Fintype.card (FullMixedCommonShapeAddress M shape)) → Option (Sigma P)}
    {history' : Fin (Fintype.card (FullMixedCommonShapeAddress M shape')) → Option (Sigma P)}
    (hh : HEq history history') :
    HEq (fullMixedShapeHistorySeed n B shape x history)
      (fullMixedShapeHistorySeed n B shape' x history') := by
  cases h
  cases eq_of_heq hh
  rfl

theorem full_mixed_common_history_seed_shape {I K : Type*}
    (steps : List (Option (I ⊕ K)))
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (history : Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) → Option (Sigma P)) :
    fullMixedCommonHistorySeed n B steps x history =
      fullMixedShapeHistorySeed n B (fullMixedCommonShape M B steps) x history := by
  funext i
  unfold fullMixedCommonHistorySeed fullMixedShapeHistorySeed
  rw [full_mixed_common_order_shape]
  cases fullMixedCommonShapeOrder M (fullMixedCommonShape M B steps) i <;> rfl

end Seed
end Bounty

end


-- Source module: PhysicalPlanHistoryTransport
section

/- Equal common shapes identify the fixed-plan history with the original
schedule history, including the actual optional prime labels. -/

namespace Bounty
section Transport
variable {S I V K : Type} {N : ℕ}
  {Ps : S → Finset ℕ} {P : Fin N → Type}
  (n : ∀ g, P g → ℕ) {J ell : ℕ} {M : Fin N → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (A : I → Type)
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J →
    SharedActiveLabels P (shared i) → A i → Fin N → ℤ)

noncomputable def physicalDecoratedPlanHistoryUpdate
    (tags : List (Option (V ⊕ PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K)))) :=
  fullMixedCommonStepHistoryUpdate n
    (fun key : PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K) => shared key.2.1) B
    (fun key _ => A key.2.1)
    (fun key c a => Δ key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)
    (fun key c a => D key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a) tags

noncomputable def physicalDecoratedPlanHistoryGain
    (tags : List (Option (V ⊕ PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K))))
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B tags))) :=
  fullMixedCommonForestHistoryGain n
    (fun key : PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K) => shared key.2.1) B
    (fun key _ => A key.2.1)
    (fun key c a => Δ key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)
    (fun key c a => D key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a) tags code

variable (tags : List (Option (V ⊕ PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K))))
  (steps : List (Option (V ⊕ K)))
  (hshape : fullMixedCommonShape M B tags = fullMixedCommonShape M B steps)
  (u : Fin tags.length) (v : Fin steps.length) (huv : HEq u v)
  (htag : physicalMixedBigTagErase (tags.get u) = steps.get v)
  (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
  (e : PhysicalMixedDecoratedBigEvent n shared B A Δ D (tags.get u) x)
  (history : Fin (Fintype.card (FullMixedCommonBirthAddress M B tags)) → Option (Sigma P))
  (history' : Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) → Option (Sigma P))
  (hh : HEq history history')

include hshape huv htag hh in
theorem physical_plan_history_update_heq :
    HEq (physicalDecoratedPlanHistoryUpdate n shared B A Δ D tags u.val (tags.get u) x e history)
      (physicalDecoratedCommonHistoryWrite n shared B A Δ D steps v.val (tags.get u) x e history') := by
  unfold physicalDecoratedPlanHistoryUpdate
  rw [full_mixed_common_step_history_update_owner, full_mixed_common_history_write_shape,
    physical_decorated_common_history_write_owner n shared B A Δ D steps v (tags.get u) htag]
  apply full_mixed_shape_history_write_heq M hshape huv _ hh
  exact (physical_mixed_erased_birth_label_heq M B (tags.get u) _).trans
    (birth_label_precomp_cast_heq _ (physicalDecoratedCommonLocalLabel n shared B A Δ D (tags.get u) x e)).symm

include hshape huv htag hh in
theorem physical_plan_history_gain_eq
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B tags)))
    (code' : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
    (hc : HEq code code') :
    physicalDecoratedPlanHistoryGain n shared B A Δ D tags code u.val (tags.get u) x e history =
      physicalDecoratedCommonHistoryGain n shared B A Δ D steps code' v.val (tags.get u) x e history' := by
  unfold physicalDecoratedPlanHistoryGain
  rw [full_mixed_common_history_gain_shape,
    physical_decorated_common_history_gain_owner n shared B A Δ D steps code' v (tags.get u) htag]
  apply full_mixed_shape_history_gain_eq M hshape hc huv _ hh
  exact (physical_mixed_erased_birth_label_heq M B (tags.get u) _).trans
    (birth_label_precomp_cast_heq _ (physicalDecoratedCommonLocalLabel n shared B A Δ D (tags.get u) x e)).symm

end Transport
end Bounty

end


-- Source module: FullMixedShapeSelectedCount
section

/- Selected child counts, like the history itself, depend only on the
common birth shape and the transported forest code. -/

open scoped Classical
namespace Bounty
section Count
variable {N : ℕ} (M : Fin N → ℕ)

def fullMixedShapeBirthGroup (shape : FullMixedCommonShapeData N) :
    FullMixedCommonShapeAddress M shape → Fin N
  | .inl a => a.1
  | .inr a => a.2.1

noncomputable def fullMixedShapeSelectedCount (shape : FullMixedCommonShapeData N)
    (code : BirthForestCode (Fintype.card (FullMixedCommonShapeAddress M shape)))
    (u : Fin shape.1) (g : Fin N) : ℕ :=
  (Finset.univ.filter (fun i => fullMixedShapeIndexStage M shape i = u.succ ∧
    fullMixedShapeBirthGroup M shape (fullMixedCommonShapeOrder M shape i) = g ∧
    code i ≠ none)).card

theorem full_mixed_shape_selected_count_heq
    {shape shape' : FullMixedCommonShapeData N} (h : shape = shape')
    {code : BirthForestCode (Fintype.card (FullMixedCommonShapeAddress M shape))}
    {code' : BirthForestCode (Fintype.card (FullMixedCommonShapeAddress M shape'))}
    (hc : HEq code code') {u : Fin shape.1} {v : Fin shape'.1} (huv : HEq u v) (g : Fin N) :
    fullMixedShapeSelectedCount M shape code u g =
      fullMixedShapeSelectedCount M shape' code' v g := by
  cases h
  cases eq_of_heq hc
  cases eq_of_heq huv
  rfl

theorem full_mixed_common_selected_count_shape {I K : Type*} (B : ℕ)
    (steps : List (Option (I ⊕ K)))
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
    (u : Fin steps.length) (g : Fin N) :
    fullMixedCommonSelectedCount M B steps code u g =
      fullMixedShapeSelectedCount M (fullMixedCommonShape M B steps) code u g := by
  unfold fullMixedCommonSelectedCount fullMixedShapeSelectedCount
  congr 2
  funext i
  rw [full_mixed_index_stage_shape, full_mixed_common_order_shape]
  cases fullMixedCommonShapeOrder M (fullMixedCommonShape M B steps) i <;> rfl

end Count
end Bounty

end


-- Source module: PhysicalDecoratedSelectedRow
section

/- The uniform big-event row bound on the original common history. The
current pattern and small prefix remain parameters of the actual kernel. -/

open Finset
open scoped Classical
namespace Bounty
section Row
variable {S I V K : Type} {N : ℕ}
  {Ps : S → Finset ℕ} {P : Fin N → Type} [∀ g, Fintype (P g)] [∀ g, DecidableEq (P g)]
  (n : ∀ g, P g → ℕ) [∀ g p, NeZero (n g p)] {J ell : ℕ} {M : Fin N → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (A : I → Type) [∀ i, Fintype (A i)]
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J →
    SharedActiveLabels P (shared i) → A i → Fin N → ℤ)
  (ω : ∀ i, SharedActiveLabels P (shared i) → A i → ℝ)
  (μ : ∀ g, P g → ℝ) (q : V → ℝ) (ρ v vmin : ℝ) (Vb η : Fin N → ℝ) (β : ℝ)

noncomputable abbrev physicalDecoratedBigEventFintype :=
  fullPermutationMixedEventFintype (J := V) n
    (fun key : PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K) => shared key.2.1) B
    (fun key _ => A key.2.1)
    (fun key c a => Δ key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)
    (fun key c a => D key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)

noncomputable def physicalDecoratedBigWeight :=
  fullPermutationMixedEventWeight (J := V) n
    (fun key : PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K) => shared key.2.1) B
    (fun key _ => A key.2.1)
    (fun key c a => Δ key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)
    (fun key c a => D key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)
    (fun key c a => ω key.2.1 c a) μ q ρ Vb

omit [∀ g, DecidableEq (P g)] in
theorem physical_decorated_length_row_factor
    (T : ℕ) (tag : Option (V ⊕ PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K))) :
    fullMixedLengthRowFactor μ q ρ v vmin Vb T tag =
      fullMixedLengthRowFactor μ q ρ v vmin Vb T (physicalMixedBigTagErase tag) := by
  cases tag with
  | none => rfl
  | some tag => cases tag <;> rfl

theorem physical_decorated_common_owner_row_le
    (hω : ∀ i c a, 0 ≤ ω i c a) (hωmass : ∀ i c, ∑ a, ω i c a ≤ 1)
    (hμ : ∀ g p, 0 ≤ μ g p) (hmass : ∀ g, ∑ p, μ g p ≤ 2)
    (hη : ∀ g, 0 ≤ η g) (hμatom : ∀ g p, μ g p ≤ η g)
    (hghostAtom : ∀ j g, (|(1 - q j) * Vb g / ρ| * η g) * v ≤ β)
    (hedgeAtom : ∀ g, η g ≤ β)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j ≤ 1)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hv : 1 < v) (hvmin : 0 < vmin)
    (hV : ∀ g, vmin ≤ Vb g)
    (hD : ∀ j, q j / ρ ^ 2 + ((1 - q j) / ρ) / v ≤ 1)
    (T : ℕ) (ht : ∀ i g, (shared i g)ᶜ.card ≤ T)
    (tags : List (Option (V ⊕ PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K))))
    (steps : List (Option (V ⊕ K)))
    (hshape : fullMixedCommonShape M B tags = fullMixedCommonShape M B steps)
    (u : Fin tags.length) (u' : Fin steps.length) (huu' : HEq u u')
    (htag : physicalMixedBigTagErase (tags.get u) = steps.get u')
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B tags)))
    (code' : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps))) (hc : HEq code code')
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (history : Fin (Fintype.card (FullMixedCommonBirthAddress M B tags)) → Option (Sigma P))
    (history' : Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) → Option (Sigma P))
    (hh : HEq history history') :
    let _ := physicalDecoratedBigEventFintype (V := V) (ell := ell) n shared B A Δ D
    (∑ e : PhysicalMixedDecoratedBigEvent n shared B A Δ D (tags.get u) x,
      |physicalDecoratedBigWeight n shared B A Δ D ω μ q ρ Vb (tags.get u) x e| *
        physicalDecoratedCommonHistoryGain n shared B A Δ D steps code' u'.val (tags.get u) x e history' *
        productLengthLyapunov v (physicalMixedDecoratedBigTarget n shared B A Δ D (tags.get u) x e)) ≤
      (β ^ (∑ g, fullMixedCommonSelectedCount M B steps code' u' g) *
        fullMixedLengthRowFactor μ q ρ v vmin Vb T (steps.get u')) * productLengthLyapunov v x := by
  let _ := physicalDecoratedBigEventFintype (V := V) (ell := ell) n shared B A Δ D
  have hb := full_mixed_common_owner_stage_row_le n
    (fun key : PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K) => shared key.2.1) B
    (fun key _ => A key.2.1)
    (fun key c a => Δ key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)
    (fun key c a => D key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)
    (fun key c a => ω key.2.1 c a) μ q ρ v vmin Vb η β tags code
    (fun key => hω key.2.1) (fun key => hωmass key.2.1)
    hμ hmass hη hμatom hghostAtom hedgeAtom hq0 hq1 hρ0 hρ1 hv hvmin hV hD T
    (fun key => ht key.2.1) u (tags.get u) rfl x history
  have hg : ∀ e, physicalDecoratedPlanHistoryGain n shared B A Δ D tags code u.val (tags.get u) x e history =
      physicalDecoratedCommonHistoryGain n shared B A Δ D steps code' u'.val (tags.get u) x e history' :=
    fun e => physical_plan_history_gain_eq n shared B A Δ D tags steps hshape u u' huu' htag x e history history' hh code code' hc
  have hcount : ∀ g, fullMixedCommonSelectedCount M B tags code u g =
      fullMixedCommonSelectedCount M B steps code' u' g := by
    intro g
    rw [full_mixed_common_selected_count_shape, full_mixed_common_selected_count_shape]
    exact full_mixed_shape_selected_count_heq M hshape hc huu' g
  change (∑ e, |physicalDecoratedBigWeight n shared B A Δ D ω μ q ρ Vb (tags.get u) x e| *
      physicalDecoratedPlanHistoryGain n shared B A Δ D tags code u.val (tags.get u) x e history *
      productLengthLyapunov v (physicalMixedDecoratedBigTarget n shared B A Δ D (tags.get u) x e)) ≤ _ at hb
  simp_rw [hg] at hb
  simpa only [hcount, physical_decorated_length_row_factor μ q ρ v vmin Vb, htag] using hb

end Row
end Bounty

end


-- Source module: FiniteRowReindex
section

/- Elementary finite-row reindexing, independent of event implementation types. -/

open Finset
namespace Bounty

theorem finite_sum_sigma_any {A : Type*} {E : A → Type*}
    [Fintype A] [∀ a, Fintype (E a)] (inst : Fintype (Sigma E)) (f : Sigma E → ℝ) :
    @Finset.sum (Sigma E) ℝ _ (@Finset.univ _ inst) f = ∑ a, ∑ e : E a, f ⟨a,e⟩ := by
  have hi : inst = (Sigma.instFintype : Fintype (Sigma E)) := Subsingleton.elim _ _
  rw [hi]
  exact Fintype.sum_sigma f

theorem finite_sum_ulift_any {A : Type*} [Fintype A]
    (inst : Fintype (ULift A)) (f : ULift A → ℝ) :
    (∑ a : A, f (ULift.up a)) = @Finset.sum (ULift A) ℝ _ (@Finset.univ _ inst) f := by
  let _ := inst
  exact (Equiv.ulift.symm.sum_comp f)

theorem finite_abs_aux_unit_row {A : Type*} {E : A → Type*}
    [Fintype A] [∀ a, Fintype (E a)]
    (inst : Fintype (Sigma E)) (w : A → ℝ) (v : ∀ a, E a → ℝ) (f : Sigma E → ℝ) :
    @Finset.sum (Sigma E) ℝ _ (@Finset.univ _ inst) (fun e => |w e.1 * v e.1 e.2| * f e) =
      ∑ a : A, |w a| * ∑ e : (Σ _u : Unit, E a), |1 * v a e.2| * f ⟨a,e.2⟩ := by
  rw [finite_sum_sigma_any]
  simp only [Fintype.sum_sigma, Fintype.sum_unique, one_mul, abs_mul, mul_sum, mul_assoc]

end Bounty

end


-- Source module: PhysicalDecoratedEdgeReindex
section

/- Removing the auxiliary singleton from the literal big edge preserves
any selector on the retained decorated big event. -/

open Finset
open scoped Classical
namespace Bounty
section Reindex
variable {S I V K : Type} {N : ℕ}
  {Ps : S → Finset ℕ} {P : Fin N → Type} [∀ g, Fintype (P g)]
  (n : ∀ g, P g → ℕ) [∀ g p, NeZero (n g p)] {J ell : ℕ} {M : Fin N → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (A : I → Type) [∀ i, Fintype (A i)]
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J →
    SharedActiveLabels P (shared i) → A i → Fin N → ℤ)
  (ω : ∀ i, SharedActiveLabels P (shared i) → A i → ℝ)
  (μ : ∀ g, P g → ℝ) (q : V → ℝ) (ρ : ℝ) (Vb : Fin N → ℝ)


theorem physical_decorated_edge_row_reindex
    (k : K) (i : I) (L : PhysicalMarkLists Ps J ell)
    (r : PhysicalResidues Ps)
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (selector : PhysicalMixedDecoratedBigEvent (V := V) n shared B A Δ D (some (.inr (k, i, L, L))) x → ℝ) :
    let _ := physicalDecoratedBigEventFintype (V := V) (ell := ell) n shared B A Δ D
    (∑ e : PhysicalMixedDecoratedBigEvent (V := V) n shared B A Δ D (some (.inr (k, i, L, L))) x,
      |physicalDecoratedBigWeight n shared B A Δ D ω μ q ρ Vb (some (.inr (k, i, L, L))) x e| * selector e) =
      ∑ a : A i, |ω i (productActiveMemorySplit (shared i) B x).1 a| *
        ∑ e : PhysicalSmallBigFullEvent n (shared i) B
          (fun d c => Δ k i d c a) (fun d c => D k i d c a) (physicalSharedPrefix L) x,
          |physicalSmallBigFullWeight n (shared i) B
            (fun d c => Δ k i d c a) (fun d c => D k i d c a) μ ρ Vb r (physicalSharedPrefix L) x e| *
              selector ⟨a, e.2⟩ := by
  let _ := physicalDecoratedBigEventFintype (V := V) (ell := ell) n shared B A Δ D
  exact finite_abs_aux_unit_row _ (fun a => ω i (productActiveMemorySplit (shared i) B x).1 a)
    (fun a e => unrestrictedJointCutoffEventWeight n
      (Δ k i (physicalSharedPrefix L) (productActiveMemorySplit (shared i) B x).1 a)
      (D k i (physicalSharedPrefix L) (productActiveMemorySplit (shared i) B x).1 a)
      μ ρ Vb (fun g => (shared i g)ᶜ.card) B (productActiveMemorySplit (shared i) B x).2 e) selector

end Reindex
end Bounty

end


-- Source module: PhysicalMixedHistoryGain
section

/- The original mixed history is evaluated on the actual retained big event. -/

namespace Bounty
section Gain
variable {S I V K : Type} {N : ℕ}
  {Ps : S → Finset ℕ} {P : Fin N → Type}
  (n : ∀ g, P g → ℕ) {J ell : ℕ} {M : Fin N → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (A : I → Type)
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J →
    SharedActiveLabels P (shared i) → A i → Fin N → ℤ)

noncomputable def physicalMixedCommonHistoryGain
    (steps : List (Option (V ⊕ K)))
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
    (t : ℕ) (tag : Option (V ⊕ K))
    (s : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B)
    (e : PhysicalMixedWordEvent n shared B A Δ D tag s)
    (history : Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) → Option (Sigma P)) : ℝ :=
  physicalMixedBigEventPullback n shared B A Δ D
    (fun tag history x e => physicalDecoratedCommonHistoryGain n shared B A Δ D steps code t tag x e history)
    tag history s e

theorem physical_mixed_common_history_gain_nonneg
    (steps : List (Option (V ⊕ K)))
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
    (t : ℕ) (tag : Option (V ⊕ K))
    (s : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B)
    (e : PhysicalMixedWordEvent n shared B A Δ D tag s)
    (history : Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) → Option (Sigma P)) :
    0 ≤ physicalMixedCommonHistoryGain n shared B A Δ D steps code t tag s e history :=
  physical_decorated_common_history_gain_nonneg n shared B A Δ D steps code t _ _ _ _

theorem physical_mixed_common_history_gain_edge
    (steps : List (Option (V ⊕ K)))
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
    (t : ℕ) (k : K)
    (s : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B)
    (e : PhysicalMixedWordEdge n shared B A Δ D k s)
    (history : Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) → Option (Sigma P)) :
    physicalMixedCommonHistoryGain n shared B A Δ D steps code t (some (.inr k)) s e history =
      physicalDecoratedCommonHistoryGain n shared B A Δ D steps code t
        (some (.inr (k, e.1, s.1.2, s.1.2))) s.2 ⟨e.2.1, e.2.2.2.2⟩ history := by
  rfl

end Gain
end Bounty

end


-- Source module: PhysicalMixedSelectedHistoryEdge
section

/- The complete small ledger can be summed in a chronological selected edge
row, retaining the actual forest history and all big events. -/

open Finset
open scoped Classical
namespace Bounty

theorem exists_physical_mixed_history_edge_bound {qmax vs : ℝ}
    (hqmax0 : 0 ≤ qmax) (hqmax1 : qmax < 1) (hvs : 0 < vs) (ell : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (S I V K : Type) (N : ℕ) [Fintype S]
      [Fintype I] (Ps : S → Finset ℕ) (P : Fin N → Type) [∀ g, Fintype (P g)]
      (n : ∀ g, P g → ℕ) [∀ g p, NeZero (n g p)] (J : ℕ) (M : Fin N → ℕ)
      (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ)
      (A : I → Type) [∀ i, Fintype (A i)]
      (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J → SharedActiveLabels P (shared i) → A i → Fin N → ℤ)
      (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)
      (ω : ∀ i, SharedActiveLabels P (shared i) → A i → ℝ)
      (μ : ∀ g, P g → ℝ) (qghost : V → ℝ) (ρ : ℝ) (Vb : Fin N → ℝ)
      (Vs : S → ℝ) (qedge : K → ℝ), (∀ s, vs ≤ Vs s) →
      ∀ (k : K), Real.sqrt (qedge k) ≤ qmax →
      ∀ (s : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B)
      (steps : List (Option (V ⊕ K)))
      (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
      (t : ℕ) (history : Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) → Option (Sigma P))
      (v : ℝ), 0 ≤ v → ∀ bound : ℝ,
      (let _ := physicalDecoratedBigEventFintype (V := V) (ell := ell) n shared B A Δ D
      ∀ i : I, (∑ e : PhysicalMixedDecoratedBigEvent (V := V) n shared B A Δ D (some (.inr (k, i, s.1.2, s.1.2))) s.2,
        |physicalDecoratedBigWeight n shared B A Δ D ω μ qghost ρ Vb (some (.inr (k, i, s.1.2, s.1.2))) s.2 e| *
          physicalDecoratedCommonHistoryGain n shared B A Δ D steps code t (some (.inr (k, i, s.1.2, s.1.2))) s.2 e history *
          productLengthLyapunov v (physicalMixedDecoratedBigTarget (V := V) n shared B A Δ D (some (.inr (k, i, s.1.2, s.1.2))) s.2 e)) ≤ bound) →
      (∑ e : PhysicalMixedWordEdge n shared B A Δ D k s,
        |physicalMixedWordWeight n shared B A Δ D kbig ω μ qghost ρ Vb Vs qedge (some (.inr k)) s e| *
          physicalMixedCommonHistoryGain n shared B A Δ D steps code t (some (.inr k)) s e history *
          productLengthLyapunov v (physicalMixedWordTarget (V := V) n shared B A Δ D kbig (some (.inr k)) s e).2) ≤
        C ^ Fintype.card S * ((Fintype.card I : ℝ) * bound) := by
  obtain ⟨C, hC, hrow⟩ := exists_physical_mixed_selected_edge_row_bound hqmax0 hqmax1 hvs ell
  refine ⟨C, hC, ?_⟩
  intro S I V K N _ _ Ps P _ n _ J M shared B A _ Δ D kbig ω μ qghost ρ Vb Vs qedge hVs k hq s steps code t history v hv bound hbig
  let _ := physicalDecoratedBigEventFintype (V := V) (ell := ell) n shared B A Δ D
  let selector := fun (i : I) (a : A i) (e : PhysicalSmallBigFullEvent n (shared i) B
      (fun d c => Δ k i d c a) (fun d c => D k i d c a) (physicalSharedPrefix s.1.2) s.2) =>
    physicalDecoratedCommonHistoryGain n shared B A Δ D steps code t
      (some (.inr (k, i, s.1.2, s.1.2))) s.2 ⟨a, e.2⟩ history *
    productLengthLyapunov v (physicalMixedDecoratedBigTarget (V := V) n shared B A Δ D
      (some (.inr (k, i, s.1.2, s.1.2))) s.2 ⟨a, e.2⟩)
  have hsel : ∀ i a e, 0 ≤ selector i a e := by
    intro i a e
    exact mul_nonneg (physical_decorated_common_history_gain_nonneg n shared B A Δ D steps code t _ _ _ _)
      (productLengthLyapunov_nonneg hv _)
  have hs := hrow S (Fin N) I V K Ps P n J M shared B A Δ D kbig ω μ qghost ρ Vb Vs qedge
    hVs k hq s selector hsel
  have hleft : (∑ e : PhysicalMixedWordEdge n shared B A Δ D k s,
      |physicalMixedWordWeight n shared B A Δ D kbig ω μ qghost ρ Vb Vs qedge (some (.inr k)) s e| *
        physicalMixedCommonHistoryGain n shared B A Δ D steps code t (some (.inr k)) s e history *
        productLengthLyapunov v (physicalMixedWordTarget (V := V) n shared B A Δ D kbig (some (.inr k)) s e).2) =
      ∑ e : PhysicalMixedWordEdge n shared B A Δ D k s,
        |physicalMixedWordWeight n shared B A Δ D kbig ω μ qghost ρ Vb Vs qedge (some (.inr k)) s e| * selector e.1 e.2.1 e.2.2.2 := by
    apply sum_congr rfl
    intro e _
    rw [physical_mixed_common_history_gain_edge]
    exact mul_assoc _ _ _
  rw [hleft]
  refine hs.trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg (le_trans (by norm_num) hC) _))
  calc
    _ = ∑ i : I, ∑ e : PhysicalMixedDecoratedBigEvent (V := V) n shared B A Δ D (some (.inr (k, i, s.1.2, s.1.2))) s.2,
        |physicalDecoratedBigWeight n shared B A Δ D ω μ qghost ρ Vb (some (.inr (k, i, s.1.2, s.1.2))) s.2 e| *
          physicalDecoratedCommonHistoryGain n shared B A Δ D steps code t (some (.inr (k, i, s.1.2, s.1.2))) s.2 e history *
          productLengthLyapunov v (physicalMixedDecoratedBigTarget (V := V) n shared B A Δ D (some (.inr (k, i, s.1.2, s.1.2))) s.2 e) := by
      apply sum_congr rfl
      intro i _
      symm
      simp_rw [mul_assoc]
      exact physical_decorated_edge_row_reindex n shared B A Δ D ω μ qghost ρ Vb k i s.1.2 s.1.1 s.2 _
    _ ≤ ∑ _i : I, bound := sum_le_sum (fun i _ => hbig i)
    _ = _ := by simp

end Bounty

end


-- Source module: FullMixedShapeMap
section

/- Relabeling ghost and edge keys preserves the chronological common birth
shape and its selected child counts. -/

namespace Bounty
section Map
variable {I K I' K' : Type*} {N : ℕ} (M : Fin N → ℕ) (B : ℕ)
  (f : I → I') (g : K → K')

theorem full_mixed_common_shape_map (steps : List (Option (I ⊕ K))) :
    fullMixedCommonShape M B (steps.map (Option.map (Sum.map f g))) =
      fullMixedCommonShape M B steps := by
  induction steps with
  | nil =>
    apply congrArg (Sigma.mk 0)
    funext u
    exact Fin.elim0 u
  | cons tag steps ih =>
    simp only [List.map_cons, full_mixed_common_shape_cons, ih]
    cases tag with
    | none => rfl
    | some tag => cases tag <;> rfl

end Map
end Bounty

end


-- Source module: PhysicalHistoryTemplate
section

/- A fixed pattern and current small prefix provide a representative big
schedule with exactly the original common birth shape. -/

namespace Bounty
section Template
variable {S I V K : Type} {Ps : S → Finset ℕ} {J ell N : ℕ}
  (M : Fin N → ℕ) (B : ℕ) (i : I) (L : PhysicalMarkLists Ps J ell)

def physicalHistoryTemplateTag : Option (V ⊕ K) →
    Option (V ⊕ PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K)) :=
  Option.map (Sum.map id (fun k => (k, i, L, L)))

theorem physical_history_template_tag_erase (tag : Option (V ⊕ K)) :
    physicalMixedBigTagErase (physicalHistoryTemplateTag i L tag) = tag := by
  cases tag with
  | none => rfl
  | some tag => cases tag <;> rfl

def physicalHistoryTemplateSteps (steps : List (Option (V ⊕ K))) :=
  steps.map (physicalHistoryTemplateTag i L)

theorem physical_history_template_shape (steps : List (Option (V ⊕ K))) :
    fullMixedCommonShape M B (physicalHistoryTemplateSteps i L steps) =
      fullMixedCommonShape M B steps :=
  full_mixed_common_shape_map M B id (fun k => (k, i, L, L)) steps

theorem physical_history_template_length (steps : List (Option (V ⊕ K))) :
    (physicalHistoryTemplateSteps i L steps).length = steps.length := List.length_map _

theorem physical_history_template_position (steps : List (Option (V ⊕ K)))
    (u : Fin steps.length) :
    (physicalHistoryTemplateSteps i L steps).get
      (Fin.cast (physical_history_template_length i L steps).symm u) =
      physicalHistoryTemplateTag i L (steps.get u) := by
  simp only [physicalHistoryTemplateSteps, List.get_eq_getElem, List.getElem_map]
  rfl

end Template
end Bounty

end


-- Source module: PhysicalHistoryTemplateRow
section

/- A current pattern and small prefix can be inserted into the uniform big
row without changing the original history, code or selected-child count. -/

open Finset
open scoped Classical
namespace Bounty
section TemplateRow
variable {S I V K : Type} {N : ℕ}
  {Ps : S → Finset ℕ} {P : Fin N → Type} [∀ g, Fintype (P g)] [∀ g, DecidableEq (P g)]
  (n : ∀ g, P g → ℕ) [∀ g p, NeZero (n g p)] {J ell : ℕ} {M : Fin N → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (A : I → Type) [∀ i, Fintype (A i)]
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J →
    SharedActiveLabels P (shared i) → A i → Fin N → ℤ)
  (ω : ∀ i, SharedActiveLabels P (shared i) → A i → ℝ)
  (μ : ∀ g, P g → ℝ) (q : V → ℝ) (ρ v vmin : ℝ) (Vb η : Fin N → ℝ) (β : ℝ)


theorem physical_history_template_owner_row_le
    (hω : ∀ i c a, 0 ≤ ω i c a) (hωmass : ∀ i c, ∑ a, ω i c a ≤ 1)
    (hμ : ∀ g p, 0 ≤ μ g p) (hmass : ∀ g, ∑ p, μ g p ≤ 2)
    (hη : ∀ g, 0 ≤ η g) (hμatom : ∀ g p, μ g p ≤ η g)
    (hghostAtom : ∀ j g, (|(1 - q j) * Vb g / ρ| * η g) * v ≤ β)
    (hedgeAtom : ∀ g, η g ≤ β)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j ≤ 1)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hv : 1 < v) (hvmin : 0 < vmin)
    (hV : ∀ g, vmin ≤ Vb g)
    (hD : ∀ j, q j / ρ ^ 2 + ((1 - q j) / ρ) / v ≤ 1)
    (T : ℕ) (ht : ∀ i g, (shared i g)ᶜ.card ≤ T)
    (i : I) (L : PhysicalMarkLists Ps J ell)
    (steps : List (Option (V ⊕ K))) (u : Fin steps.length)
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (history : Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) → Option (Sigma P)) :
    let _ := physicalDecoratedBigEventFintype (V := V) (ell := ell) n shared B A Δ D
    (∑ e : PhysicalMixedDecoratedBigEvent n shared B A Δ D (physicalHistoryTemplateTag i L (steps.get u)) x,
      |physicalDecoratedBigWeight n shared B A Δ D ω μ q ρ Vb (physicalHistoryTemplateTag i L (steps.get u)) x e| *
        physicalDecoratedCommonHistoryGain n shared B A Δ D steps code u.val (physicalHistoryTemplateTag i L (steps.get u)) x e history *
        productLengthLyapunov v (physicalMixedDecoratedBigTarget n shared B A Δ D (physicalHistoryTemplateTag i L (steps.get u)) x e)) ≤
      (β ^ (∑ g, fullMixedCommonSelectedCount M B steps code u g) *
        fullMixedLengthRowFactor μ q ρ v vmin Vb T (steps.get u)) * productLengthLyapunov v x := by
  let _ := physicalDecoratedBigEventFintype (V := V) (ell := ell) n shared B A Δ D
  let tags := physicalHistoryTemplateSteps i L steps
  have hs := physical_history_template_shape M B i L steps
  have hlen := physical_history_template_length i L steps
  let uold := Fin.cast hlen.symm u
  have hu : HEq uold u := (Fin.heq_ext_iff hlen).2 rfl
  have htag : physicalMixedBigTagErase (tags.get uold) = steps.get u := by
    rw [physical_history_template_position, physical_history_template_tag_erase]
  let oldcode := cast (congrArg (fun s => BirthForestCode (Fintype.card (FullMixedCommonShapeAddress M s))) hs.symm) code
  let oldhistory := cast (congrArg (fun s => Fin (Fintype.card (FullMixedCommonShapeAddress M s)) → Option (Sigma P)) hs.symm) history
  have hc : HEq oldcode code := cast_heq _ _
  have hh : HEq oldhistory history := cast_heq _ _
  have hb := physical_decorated_common_owner_row_le n shared B A Δ D ω μ q ρ v vmin Vb η β
    hω hωmass hμ hmass hη hμatom hghostAtom hedgeAtom hq0 hq1 hρ0 hρ1 hv hvmin hV hD T ht
    tags steps hs uold u hu htag oldcode code hc x oldhistory history hh
  let row (tag : Option (V ⊕ PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K))) : ℝ :=
    ∑ e : PhysicalMixedDecoratedBigEvent n shared B A Δ D tag x,
      |physicalDecoratedBigWeight n shared B A Δ D ω μ q ρ Vb tag x e| *
        physicalDecoratedCommonHistoryGain n shared B A Δ D steps code u.val tag x e history *
        productLengthLyapunov v (physicalMixedDecoratedBigTarget n shared B A Δ D tag x e)
  change row (tags.get uold) ≤ _ at hb
  change row (physicalHistoryTemplateTag i L (steps.get u)) ≤ _
  have htag' : tags.get uold = physicalHistoryTemplateTag i L (steps.get u) :=
    physical_history_template_position i L steps u
  rwa [htag'] at hb

end TemplateRow
end Bounty

end


-- Source module: PhysicalMixedNonedgeRows
section

/- Permutation and ghost events leave no additional small completion sum.
Their literal selected rows equal the corresponding big-event row. -/

open Finset
open scoped Classical
namespace Bounty
section Nonedge
variable {S I V K : Type} [Fintype S] {N : ℕ}
  {Ps : S → Finset ℕ} {P : Fin N → Type} [∀ g, Fintype (P g)]
  (n : ∀ g, P g → ℕ) [∀ g p, NeZero (n g p)] {J ell : ℕ} {M : Fin N → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (A : I → Type) [∀ i, Fintype (A i)]
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J →
    SharedActiveLabels P (shared i) → A i → Fin N → ℤ)
  (ω : ∀ i, SharedActiveLabels P (shared i) → A i → ℝ)
  (μ : ∀ g, P g → ℝ) (q : V → ℝ) (ρ : ℝ) (Vb : Fin N → ℝ)

  (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)
  (Vs : S → ℝ) (qedge : K → ℝ)

theorem physical_mixed_ghost_selected_row_eq
    (j : V) (s : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B)
    (selector : PhysicalMixedDecoratedBigEvent (Ps := Ps) (J := J) (ell := ell) n shared B A Δ D (some (.inl j)) s.2 → ℝ) :
    let _ := physicalDecoratedBigEventFintype (V := V) (ell := ell) n shared B A Δ D
    (∑ e : CoupledGhostEvent M B s.2,
      |physicalMixedWordWeight n shared B A Δ D kbig ω μ q ρ Vb Vs qedge (some (.inl j)) s e| * selector (ULift.up e)) =
      ∑ e : PhysicalMixedDecoratedBigEvent (Ps := Ps) (J := J) (ell := ell) n shared B A Δ D (some (.inl j)) s.2,
        |physicalDecoratedBigWeight n shared B A Δ D ω μ q ρ Vb (some (.inl j)) s.2 e| * selector e := by
  let _ := physicalDecoratedBigEventFintype (V := V) (ell := ell) n shared B A Δ D
  simp only [physicalMixedWordWeight, physicalDecoratedBigWeight, fullPermutationMixedEventWeight,
    fullMixedMemoryEventWeight]
  exact finite_sum_ulift_any (A := CoupledGhostEvent M B s.2) _
    (fun e => |coupledGhostJointEventWeight
      (fun g => physicalGhostRetention (n g) (q j) ρ)
      (fun g => physicalGhostTermination (n g) (q j) ρ)
      (fun g => physicalGhostBirth (n g) (q j) ρ (Vb g))
      (fun g => unrestrictedResidueWeight (μ g)) M B s.2 e.down| * selector e)

theorem physical_mixed_permutation_selected_row_eq
    (s : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B)
    (selector : PhysicalMixedDecoratedBigEvent (V := V) (Ps := Ps) (J := J) (ell := ell) n shared B A Δ D none s.2 → ℝ) :
    let _ := physicalDecoratedBigEventFintype (V := V) (ell := ell) n shared B A Δ D
    (∑ e : PhysicalPermutations S J ell × FullActiveSlotPermutations M,
      |physicalMixedWordWeight n shared B A Δ D kbig ω μ q ρ Vb Vs qedge none s e| * selector (ULift.up e.2)) =
      ∑ e : PhysicalMixedDecoratedBigEvent (V := V) (Ps := Ps) (J := J) (ell := ell) n shared B A Δ D none s.2,
        |physicalDecoratedBigWeight n shared B A Δ D ω μ q ρ Vb none s.2 e| * selector e := by
  let _ := physicalDecoratedBigEventFintype (V := V) (ell := ell) n shared B A Δ D
  have hc : (Fintype.card (PhysicalPermutations S J ell) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [physicalMixedWordWeight, physicalDecoratedBigWeight, fullPermutationMixedEventWeight,
    Fintype.sum_prod_type, abs_mul, abs_inv, Nat.abs_cast, mul_assoc,
    ← mul_sum, sum_const, nsmul_eq_mul, card_univ]
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  exact finite_sum_ulift_any (A := FullActiveSlotPermutations M) _
    (fun e => |fullActivePermutationWeight M e.down| * selector e)

end Nonedge
end Bounty

end


-- Source module: PhysicalMixedForestRowFactor
section

/- The small-ledger row cost is paid once per original edge. Forest rank
still supplies one full rarity factor per selected child. -/

open Finset
open scoped Classical
namespace Bounty

def physicalMixedSmallRowFactor {V K : Type*} (C : ℝ) (smallGroups patterns : ℕ) :
    Option (V ⊕ K) → ℝ
  | none => 1
  | some (.inl _) => 1
  | some (.inr _) => C ^ smallGroups * patterns

theorem physical_mixed_small_row_factor_nonneg {V K : Type*} {C : ℝ}
    (hC : 0 ≤ C) (smallGroups patterns : ℕ) (tag : Option (V ⊕ K)) :
    0 ≤ physicalMixedSmallRowFactor C smallGroups patterns tag := by
  cases tag with
  | none => exact zero_le_one
  | some tag =>
    cases tag with
    | inl _ => exact zero_le_one
    | inr _ => exact mul_nonneg (pow_nonneg hC _) (Nat.cast_nonneg _)

section Product
variable {V K : Type*} {N : ℕ} {P : Fin N → Type*} [∀ g, Fintype (P g)]
  (M : Fin N → ℕ) (B : ℕ) (steps : List (Option (V ⊕ K)))
  (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
  (μ : ∀ g, P g → ℝ) (q : V → ℝ) (ρ v vmin : ℝ) (Vb : Fin N → ℝ)
  (T : ℕ) (β C : ℝ) (smallGroups patterns : ℕ)

noncomputable def physicalMixedCommonForestRowFactor (t : ℕ) (tag : Option (V ⊕ K)) : ℝ :=
  physicalMixedSmallRowFactor C smallGroups patterns tag *
    fullMixedCommonForestRowFactor M B steps code μ q ρ v vmin Vb T β t tag

theorem physical_mixed_common_forest_row_factor_nonneg
    (hβ : 0 ≤ β) (hC : 0 ≤ C) (hρ : ρ < 1) (hv : 0 ≤ v)
    (t : ℕ) (tag : Option (V ⊕ K)) :
    0 ≤ physicalMixedCommonForestRowFactor M B steps code μ q ρ v vmin Vb T β C smallGroups patterns t tag :=
  mul_nonneg (physical_mixed_small_row_factor_nonneg hC _ _ _)
    (full_mixed_common_forest_row_factor_nonneg M B steps code μ q ρ v vmin Vb T β hβ hρ hv t tag)

theorem physical_mixed_common_forest_row_factor_product
    (hcode : ∀ i, fullMixedCommonIndexStage M B steps i = 0 → code i = none) :
    finiteEventIndexedProduct
      (physicalMixedCommonForestRowFactor M B steps code μ q ρ v vmin Vb T β C smallGroups patterns) 0 steps =
      β ^ birthForestRank code *
        (steps.map (physicalMixedSmallRowFactor C smallGroups patterns)).prod *
        (steps.map (fullMixedLengthRowFactor μ q ρ v vmin Vb T)).prod := by
  rw [finite_event_indexed_product_eq_prod]
  simp only [Nat.zero_add, physicalMixedCommonForestRowFactor, fullMixedCommonForestRowFactor,
    prod_mul_distrib, prod_pow_eq_pow_sum,
    full_mixed_common_selected_at_sum M B steps code hcode]
  rw [← List.prod_ofFn, ← List.prod_ofFn]
  have hs : (List.ofFn fun x => physicalMixedSmallRowFactor C smallGroups patterns (steps.get x)) =
      steps.map (physicalMixedSmallRowFactor C smallGroups patterns) := by
    apply List.ext_get
    · simp
    · intro n hn hm
      simp
  have hb : (List.ofFn fun x => fullMixedLengthRowFactor μ q ρ v vmin Vb T (steps.get x)) =
      steps.map (fullMixedLengthRowFactor μ q ρ v vmin Vb T) := by
    apply List.ext_get
    · simp
    · intro n hn hm
      simp
  rw [hs, hb]
  ring

end Product
end Bounty

end


-- Source module: PhysicalMixedOwnerRows
section

/- Uniform chronological rows for the literal original mixed word. The
small completion cost is independent of J and the history retains all births. -/

open Finset
open scoped Classical
namespace Bounty

theorem exists_physical_mixed_owner_row_bound {qmax vs : ℝ}
    (hqmax0 : 0 ≤ qmax) (hqmax1 : qmax < 1) (hvs : 0 < vs) (ell : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (S I V K : Type) (N : ℕ) [Fintype S]
      [Fintype I] (Ps : S → Finset ℕ) (P : Fin N → Type) [∀ g, Fintype (P g)] [∀ g, DecidableEq (P g)]
      (n : ∀ g, P g → ℕ) [∀ g p, NeZero (n g p)] (J : ℕ) (M : Fin N → ℕ)
      (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ)
      (A : I → Type) [∀ i, Fintype (A i)]
      (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J → SharedActiveLabels P (shared i) → A i → Fin N → ℤ)
      (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)
      (ω : ∀ i, SharedActiveLabels P (shared i) → A i → ℝ)
      (μ : ∀ g, P g → ℝ) (qghost : V → ℝ) (ρ : ℝ) (Vb : Fin N → ℝ)
      (Vs : S → ℝ) (qedge : K → ℝ), (∀ s, vs ≤ Vs s) →
      (∀ k, Real.sqrt (qedge k) ≤ qmax) →
      ∀ (_i0 : I) (v vmin : ℝ) (η : Fin N → ℝ) (β : ℝ) (T : ℕ),
      (∀ i c a, 0 ≤ ω i c a) → (∀ i c, ∑ a, ω i c a ≤ 1) →
      (∀ g p, 0 ≤ μ g p) → (∀ g, ∑ p, μ g p ≤ 2) →
      (∀ g, 0 ≤ η g) → (∀ g p, μ g p ≤ η g) →
      (∀ j g, (|(1 - qghost j) * Vb g / ρ| * η g) * v ≤ β) →
      (∀ g, η g ≤ β) →
      (∀ j, 0 ≤ qghost j) → (∀ j, qghost j ≤ 1) →
      0 < ρ → ρ < 1 → 1 < v → 0 < vmin →
      (∀ g, vmin ≤ Vb g) →
      (∀ j, qghost j / ρ ^ 2 + ((1 - qghost j) / ρ) / v ≤ 1) →
      (∀ i g, (shared i g)ᶜ.card ≤ T) →
      ∀ (steps : List (Option (V ⊕ K)))
      (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
      (u : Fin steps.length) (tag : Option (V ⊕ K)), steps.get u = tag →
      ∀ (s : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B)
      (history : Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) → Option (Sigma P)),
      let _ := physicalMixedWordEventFintype (V := V) (ell := ell) n shared B A Δ D
      (∑ e : PhysicalMixedWordEvent n shared B A Δ D tag s,
        |physicalMixedWordWeight n shared B A Δ D kbig ω μ qghost ρ Vb Vs qedge tag s e| *
          physicalMixedCommonHistoryGain n shared B A Δ D steps code u.val tag s e history *
          productLengthLyapunov v (physicalMixedWordTarget n shared B A Δ D kbig tag s e).2) ≤
        physicalMixedCommonForestRowFactor M B steps code μ qghost ρ v vmin Vb T β C
          (Fintype.card S) (Fintype.card I) u.val tag * productLengthLyapunov v s.2 := by
  obtain ⟨C, hC, hmix⟩ := exists_physical_mixed_history_edge_bound hqmax0 hqmax1 hvs ell
  refine ⟨C, hC, ?_⟩
  intro S I V K N _ _ Ps P _ _ n _ J M shared B A _ Δ D kbig ω μ qghost ρ Vb Vs qedge hVs hqedge
    i0 v vmin η β T hω hωmass hμ hmass hη hμatom hghost hedge hq0 hq1 hρ0 hρ1 hv hvmin hV hD ht
    steps code u tag htag s history
  let _ := physicalMixedWordEventFintype (V := V) (ell := ell) n shared B A Δ D
  let _ := physicalDecoratedBigEventFintype (V := V) (ell := ell) n shared B A Δ D
  let bigrow (tag : Option (V ⊕ PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K))) : ℝ :=
    ∑ e : PhysicalMixedDecoratedBigEvent n shared B A Δ D tag s.2,
      |physicalDecoratedBigWeight n shared B A Δ D ω μ qghost ρ Vb tag s.2 e| *
        physicalDecoratedCommonHistoryGain n shared B A Δ D steps code u.val tag s.2 e history *
        productLengthLyapunov v (physicalMixedDecoratedBigTarget n shared B A Δ D tag s.2 e)
  have hbig (i : I) :
      (∑ e : PhysicalMixedDecoratedBigEvent n shared B A Δ D (physicalHistoryTemplateTag i s.1.2 tag) s.2,
        |physicalDecoratedBigWeight n shared B A Δ D ω μ qghost ρ Vb (physicalHistoryTemplateTag i s.1.2 tag) s.2 e| *
          physicalDecoratedCommonHistoryGain n shared B A Δ D steps code u.val (physicalHistoryTemplateTag i s.1.2 tag) s.2 e history *
          productLengthLyapunov v (physicalMixedDecoratedBigTarget n shared B A Δ D (physicalHistoryTemplateTag i s.1.2 tag) s.2 e)) ≤
        (β ^ (∑ g, fullMixedCommonSelectedCount M B steps code u g) *
          fullMixedLengthRowFactor μ qghost ρ v vmin Vb T tag) * productLengthLyapunov v s.2 := by
    subst tag
    exact physical_history_template_owner_row_le n shared B A Δ D ω μ qghost ρ v vmin Vb η β
      hω hωmass hμ hmass hη hμatom hghost hedge hq0 hq1 hρ0 hρ1 hv hvmin hV hD T ht
      i s.1.2 steps u code s.2 history
  cases tag with
  | none =>
    have hb := hbig i0
    change bigrow none ≤ _ at hb
    have heq := physical_mixed_permutation_selected_row_eq n shared B A Δ D ω μ qghost ρ Vb
      kbig Vs qedge s (fun e =>
        physicalDecoratedCommonHistoryGain n shared B A Δ D steps code u.val none s.2 e history *
          productLengthLyapunov v (physicalMixedDecoratedBigTarget n shared B A Δ D none s.2 e))
    simp only [← mul_assoc] at heq
    change _ = bigrow none at heq
    exact heq.le.trans (by
      simpa only [physicalMixedCommonForestRowFactor, physicalMixedSmallRowFactor,
        fullMixedCommonForestRowFactor, full_mixed_common_selected_at_owner, one_mul] using hb)
  | some tag =>
    cases tag with
    | inl j =>
      have hb := hbig i0
      change bigrow (some (.inl j)) ≤ _ at hb
      have heq := physical_mixed_ghost_selected_row_eq n shared B A Δ D ω μ qghost ρ Vb
        kbig Vs qedge j s (fun e =>
          physicalDecoratedCommonHistoryGain n shared B A Δ D steps code u.val (some (.inl j)) s.2 e history *
            productLengthLyapunov v (physicalMixedDecoratedBigTarget n shared B A Δ D (some (.inl j)) s.2 e))
      simp only [← mul_assoc] at heq
      change _ = bigrow (some (.inl j)) at heq
      exact heq.le.trans (by
        simpa only [physicalMixedCommonForestRowFactor, physicalMixedSmallRowFactor,
          fullMixedCommonForestRowFactor, full_mixed_common_selected_at_owner, one_mul] using hb)
    | inr k =>
      have hb := hmix S I V K N Ps P n J M shared B A Δ D kbig ω μ qghost ρ Vb Vs qedge
        hVs k (hqedge k) s steps code u.val history v (zero_lt_one.trans hv).le
        ((β ^ (∑ g, fullMixedCommonSelectedCount M B steps code u g) *
          fullMixedLengthRowFactor μ qghost ρ v vmin Vb T (some (.inr k))) * productLengthLyapunov v s.2)
        (fun i => hbig i)
      refine hb.trans_eq ?_
      simp only [physicalMixedCommonForestRowFactor, physicalMixedSmallRowFactor,
        fullMixedCommonForestRowFactor, full_mixed_common_selected_at_owner]
      ring

end Bounty

end


-- Source module: PhysicalMixedHistorySchedule
section

/- The pulled-back common history vanishes away from the original clock. -/

namespace Bounty
section Schedule
variable {S I V K : Type} {N : ℕ}
  {Ps : S → Finset ℕ} {P : Fin N → Type}
  (n : ∀ g, P g → ℕ) {J ell : ℕ} {M : Fin N → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (A : I → Type)
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J →
    SharedActiveLabels P (shared i) → A i → Fin N → ℤ)
  (steps : List (Option (V ⊕ K)))
  (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
  (t : ℕ) (tag : Option (V ⊕ K))
  (s : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B)
  (e : PhysicalMixedWordEvent n shared B A Δ D tag s)
  (history : Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) → Option (Sigma P))

theorem physical_mixed_common_history_gain_after (ht : ¬t < steps.length) :
    physicalMixedCommonHistoryGain n shared B A Δ D steps code t tag s e history = 0 := by
  unfold physicalMixedCommonHistoryGain physicalMixedBigEventPullback physicalDecoratedCommonHistoryGain
  dsimp only
  rw [dif_neg ht]

theorem physical_mixed_common_history_gain_other (ht : t < steps.length)
    (htag : tag ≠ steps.get ⟨t, ht⟩) :
    physicalMixedCommonHistoryGain n shared B A Δ D steps code t tag s e history = 0 := by
  unfold physicalMixedCommonHistoryGain physicalMixedBigEventPullback physicalDecoratedCommonHistoryGain
  dsimp only
  rw [dif_pos ht, physical_mixed_big_event_tag_erase, if_neg htag]

end Schedule
end Bounty

end


-- Source module: PhysicalMixedHistoryIntegral
section

/- Chronological selected rows iterate on the original mixed paths, with
all small factors retained and the full forest-rank rarity power. -/

open Finset
open scoped Classical
namespace Bounty
section Integral
variable {S I V K : Type} [Fintype S] [Fintype I] {N : ℕ}
  {Ps : S → Finset ℕ} {P : Fin N → Type} [∀ g, Fintype (P g)]
  (n : ∀ g, P g → ℕ) [∀ g p, NeZero (n g p)] {J ell : ℕ} {M : Fin N → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (A : I → Type) [∀ i, Fintype (A i)]
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J → SharedActiveLabels P (shared i) → A i → Fin N → ℤ)
  (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)
  (ω : ∀ i, SharedActiveLabels P (shared i) → A i → ℝ)
  (μ : ∀ g, P g → ℝ) (qghost : V → ℝ) (ρ : ℝ) (Vb : Fin N → ℝ)
  (Vs : S → ℝ) (qedge : K → ℝ)
  (steps : List (Option (V ⊕ K)))
  (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))

noncomputable def physicalMixedCommonHistoryUpdate
    (t : ℕ) (tag : Option (V ⊕ K))
    (s : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B)
    (e : PhysicalMixedWordEvent n shared B A Δ D tag s)
    (history : Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) → Option (Sigma P)) :=
  physicalMixedBigEventPullback n shared B A Δ D
    (fun tag history x e => physicalDecoratedCommonHistoryWrite n shared B A Δ D steps t tag x e history)
    tag history s e

variable (v vmin β C : ℝ) (T : ℕ)

noncomputable def physicalMixedHistoryRow (t : ℕ) (tag : Option (V ⊕ K))
    (s : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B)
    (history : Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) → Option (Sigma P)) : ℝ :=
  let _ := physicalMixedWordEventFintype (V := V) (ell := ell) n shared B A Δ D
  ∑ e : PhysicalMixedWordEvent n shared B A Δ D tag s,
    |physicalMixedWordWeight n shared B A Δ D kbig ω μ qghost ρ Vb Vs qedge tag s e| *
      physicalMixedCommonHistoryGain n shared B A Δ D steps code t tag s e history *
      productLengthLyapunov v (physicalMixedWordTarget n shared B A Δ D kbig tag s e).2

theorem physical_mixed_history_integral_le_rank
    (hβ : 0 ≤ β) (hC : 0 ≤ C) (hρ : ρ < 1) (hv : 0 ≤ v)
    (hcode : ∀ i, fullMixedCommonIndexStage M B steps i = 0 → code i = none)
    (howner : ∀ (u : Fin steps.length) (tag : Option (V ⊕ K)), steps.get u = tag →
      ∀ s history,
      physicalMixedHistoryRow (ell := ell) n shared B A Δ D kbig ω μ qghost ρ Vb Vs qedge steps code v u.val tag s history ≤
        physicalMixedCommonForestRowFactor M B steps code μ qghost ρ v vmin Vb T β C
          (Fintype.card S) (Fintype.card I) u.val tag * productLengthLyapunov v s.2)
    (s : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B)
    (history : Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) → Option (Sigma P))
    (F : FiniteEventPath (PhysicalMixedWordEvent n shared B A Δ D)
      (physicalMixedWordTarget n shared B A Δ D kbig) steps s → ℝ)
    {L : ℝ} (hL : 0 ≤ L)
    (hF : ∀ p, F p ≤ L * productLengthLyapunov v
      (finiteEventPathTerminal (PhysicalMixedWordEvent n shared B A Δ D)
        (physicalMixedWordTarget n shared B A Δ D kbig) steps s p).2) :
    let _ := physicalMixedWordEventFintype (V := V) (ell := ell) n shared B A Δ D
    finiteEventPathIntegral (PhysicalMixedWordEvent n shared B A Δ D)
      (physicalMixedWordTarget n shared B A Δ D kbig)
      (fun tag s e => |physicalMixedWordWeight n shared B A Δ D kbig ω μ qghost ρ Vb Vs qedge tag s e|)
      steps s (fun p => finiteEventHistoryFactor
        (PhysicalMixedWordEvent n shared B A Δ D) (physicalMixedWordTarget n shared B A Δ D kbig)
        (physicalMixedCommonHistoryUpdate n shared B A Δ D steps)
        (physicalMixedCommonHistoryGain n shared B A Δ D steps code) 0 steps s p history * F p) ≤
      β ^ birthForestRank code *
        (steps.map (physicalMixedSmallRowFactor C (Fintype.card S) (Fintype.card I))).prod *
        (steps.map (fullMixedLengthRowFactor μ qghost ρ v vmin Vb T)).prod *
        (L * productLengthLyapunov v s.2) := by
  let _ := physicalMixedWordEventFintype (V := V) (ell := ell) n shared B A Δ D
  have hfactor := physical_mixed_common_forest_row_factor_nonneg M B steps code μ qghost ρ v vmin Vb T β C
    (Fintype.card S) (Fintype.card I) hβ hC hρ hv
  have hrow : ∀ t tag s history,
      physicalMixedHistoryRow (ell := ell) n shared B A Δ D kbig ω μ qghost ρ Vb Vs qedge steps code v t tag s history ≤
        physicalMixedCommonForestRowFactor M B steps code μ qghost ρ v vmin Vb T β C
          (Fintype.card S) (Fintype.card I) t tag * productLengthLyapunov v s.2 := by
    intro t tag s history
    have hn := mul_nonneg (hfactor t tag) (productLengthLyapunov_nonneg hv s.2)
    by_cases ht : t < steps.length
    · by_cases htag : steps.get ⟨t, ht⟩ = tag
      · exact howner ⟨t, ht⟩ tag htag s history
      · have hz : ∀ e, physicalMixedCommonHistoryGain n shared B A Δ D steps code t tag s e history = 0 :=
          fun e => physical_mixed_common_history_gain_other n shared B A Δ D steps code t tag s e history ht (Ne.symm htag)
        simpa only [physicalMixedHistoryRow, hz, mul_zero, zero_mul, sum_const_zero] using hn
    · have hz : ∀ e, physicalMixedCommonHistoryGain n shared B A Δ D steps code t tag s e history = 0 :=
        fun e => physical_mixed_common_history_gain_after n shared B A Δ D steps code t tag s e history ht
      simpa only [physicalMixedHistoryRow, hz, mul_zero, zero_mul, sum_const_zero] using hn
  have hb := finite_event_history_integral_le_rows
    (PhysicalMixedWordEvent n shared B A Δ D) (physicalMixedWordTarget n shared B A Δ D kbig)
    (fun tag s e => |physicalMixedWordWeight n shared B A Δ D kbig ω μ qghost ρ Vb Vs qedge tag s e|)
    (physicalMixedCommonHistoryUpdate n shared B A Δ D steps)
    (physicalMixedCommonHistoryGain n shared B A Δ D steps code)
    (fun _ _ _ => abs_nonneg _) (physical_mixed_common_history_gain_nonneg n shared B A Δ D steps code)
    (fun s => productLengthLyapunov v s.2)
    (physicalMixedCommonForestRowFactor M B steps code μ qghost ρ v vmin Vb T β C (Fintype.card S) (Fintype.card I))
    hfactor hrow 0 steps s history F hL hF
  rw [physical_mixed_common_forest_row_factor_product M B steps code μ qghost ρ v vmin Vb T β C
    (Fintype.card S) (Fintype.card I) hcode] at hb
  exact hb

end Integral
end Bounty

end


-- Source module: PhysicalMixedActualHistoryBound
section

/- A genuine original mixed-path rank bound from the arithmetic atom and
small-completion assumptions, with no remaining row-bound hypothesis. -/

open Finset
open scoped Classical
namespace Bounty

theorem exists_physical_mixed_history_integral_bound {qmax vs : ℝ}
    (hqmax0 : 0 ≤ qmax) (hqmax1 : qmax < 1) (hvs : 0 < vs) (ell : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (S I V K : Type) (N : ℕ) [Fintype S]
      [Fintype I] (Ps : S → Finset ℕ) (P : Fin N → Type) [∀ g, Fintype (P g)] [∀ g, DecidableEq (P g)]
      (n : ∀ g, P g → ℕ) [∀ g p, NeZero (n g p)] (J : ℕ) (M : Fin N → ℕ)
      (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ)
      (A : I → Type) [∀ i, Fintype (A i)]
      (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J → SharedActiveLabels P (shared i) → A i → Fin N → ℤ)
      (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)
      (ω : ∀ i, SharedActiveLabels P (shared i) → A i → ℝ)
      (μ : ∀ g, P g → ℝ) (qghost : V → ℝ) (ρ : ℝ) (Vb : Fin N → ℝ)
      (Vs : S → ℝ) (qedge : K → ℝ), (∀ s, vs ≤ Vs s) →
      (∀ k, Real.sqrt (qedge k) ≤ qmax) →
      ∀ (_i0 : I) (v vmin : ℝ) (η : Fin N → ℝ) (β : ℝ) (T : ℕ),
      (∀ i c a, 0 ≤ ω i c a) → (∀ i c, ∑ a, ω i c a ≤ 1) →
      (∀ g p, 0 ≤ μ g p) → (∀ g, ∑ p, μ g p ≤ 2) →
      (∀ g, 0 ≤ η g) → (∀ g p, μ g p ≤ η g) →
      (∀ j g, (|(1 - qghost j) * Vb g / ρ| * η g) * v ≤ β) →
      (∀ g, η g ≤ β) →
      (∀ j, 0 ≤ qghost j) → (∀ j, qghost j ≤ 1) →
      0 < ρ → ρ < 1 → 1 < v → 0 < vmin →
      (∀ g, vmin ≤ Vb g) →
      (∀ j, qghost j / ρ ^ 2 + ((1 - qghost j) / ρ) / v ≤ 1) →
      (∀ i g, (shared i g)ᶜ.card ≤ T) →
      0 ≤ β →
      ∀ (steps : List (Option (V ⊕ K)))
      (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
      (_hcode : ∀ i, fullMixedCommonIndexStage M B steps i = 0 → code i = none)
      (s : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B)
      (history : Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) → Option (Sigma P))
      (F : FiniteEventPath (PhysicalMixedWordEvent n shared B A Δ D)
        (physicalMixedWordTarget n shared B A Δ D kbig) steps s → ℝ)
      (Lbound : ℝ), 0 ≤ Lbound →
      (∀ p, F p ≤ Lbound * productLengthLyapunov v
        (finiteEventPathTerminal (PhysicalMixedWordEvent n shared B A Δ D)
          (physicalMixedWordTarget n shared B A Δ D kbig) steps s p).2) →
      let _ := physicalMixedWordEventFintype (V := V) (ell := ell) n shared B A Δ D
      finiteEventPathIntegral (PhysicalMixedWordEvent n shared B A Δ D)
        (physicalMixedWordTarget n shared B A Δ D kbig)
        (fun tag s e => |physicalMixedWordWeight n shared B A Δ D kbig ω μ qghost ρ Vb Vs qedge tag s e|)
        steps s (fun p => finiteEventHistoryFactor
          (PhysicalMixedWordEvent n shared B A Δ D) (physicalMixedWordTarget n shared B A Δ D kbig)
          (physicalMixedCommonHistoryUpdate n shared B A Δ D steps)
          (physicalMixedCommonHistoryGain n shared B A Δ D steps code) 0 steps s p history * F p) ≤
        β ^ birthForestRank code *
          (steps.map (physicalMixedSmallRowFactor C (Fintype.card S) (Fintype.card I))).prod *
          (steps.map (fullMixedLengthRowFactor μ qghost ρ v vmin Vb T)).prod *
          (Lbound * productLengthLyapunov v s.2) := by
  obtain ⟨C, hC, howner⟩ := exists_physical_mixed_owner_row_bound hqmax0 hqmax1 hvs ell
  refine ⟨C, hC, ?_⟩
  intro S I V K N _ _ Ps P _ _ n _ J M shared B A _ Δ D kbig ω μ qghost ρ Vb Vs qedge hVs hqedge
    i0 v vmin η β T hω hωmass hμ hmass hη hμatom hghost hedge hq0 hq1 hρ0 hρ1 hv hvmin hV hD ht
    hβ steps code hcode s history F Lbound hL hF
  exact physical_mixed_history_integral_le_rank n shared B A Δ D kbig ω μ qghost ρ Vb Vs qedge
    steps code v vmin β C T hβ (le_trans zero_le_one hC) hρ1 (zero_lt_one.trans hv).le hcode
    (fun u tag htag s history => howner S I V K N Ps P n J M shared B A Δ D kbig ω μ qghost ρ Vb Vs qedge
      hVs hqedge i0 v vmin η β T hω hωmass hμ hmass hη hμatom hghost hedge hq0 hq1 hρ0 hρ1 hv hvmin hV hD ht
      steps code u tag htag s history)
    s history F hL hF

end Bounty

end


-- Source module: PhysicalRootHistoryIntegral
section

/- The original root data in the absolute common-history integral. -/

open Finset
open scoped Classical
namespace Bounty
section Integral
variable {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  [∀ g (p : P (e.symm g).val), NeZero p.val]
  (patterns : Finset I) (C : I → Fin N → Finset (Fin J)) (k : ℕ → I → ℤ)
  (V : Fin N → ℝ) (q : ℝ) (β : (g : Fin M) → P (e.symm g).val → ℝ)
  (retention : Fin (n + 2) → ℝ) (ρ : ℝ)

noncomputable def physicalRootHistoryIntegral
    (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e)
    (history : Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) →
      Option ((g : Fin M) × P (e.symm g).val))
    (F : PhysicalRootMixedPath (n := n) groups e patterns C k s → ℝ) : ℝ :=
  @finiteEventPathIntegral _ _ (PhysicalRootMixedEvent groups e patterns C k)
    (physicalMixedWordEventFintype
      (fun g (p : P (e.symm g).val) => p.val)
      (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) B
      (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
      (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
      (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val)))
    (physicalRootMixedTarget groups e patterns C k)
    (fun tag s ev => |physicalMixedWordWeight
      (fun g (p : P (e.symm g).val) => p.val)
      (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) B
      (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
      (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
      (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
      (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
      (fun (i : patterns) _ aux => physicalAuxMass (fun g => V (e.symm g).val) (fun g => C i.val (e.symm g).val) aux)
      (fun g p => β g p / V (e.symm g).val) retention ρ (fun g => V (e.symm g).val)
      (fun s : ↥groupsᶜ => V s.val) (fun _ => q) tag s ev|)
    ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) s
    (fun p => finiteEventHistoryFactor (PhysicalRootMixedEvent groups e patterns C k)
      (physicalRootMixedTarget groups e patterns C k)
      (physicalMixedCommonHistoryUpdate
        (fun g (p : P (e.symm g).val) => p.val)
        (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) B
        (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
        (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
        (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))
      (physicalMixedCommonHistoryGain
        (fun g (p : P (e.symm g).val) => p.val)
        (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) B
        (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
        (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
        (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) code)
      0 ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) s p history * F p)

end Integral
end Bounty

end


-- Source module: PhysicalRootScaledHistoryBound
section

/- Original history integration with an arbitrary nonnegative terminal bound.
The small-row constant is independent of that bound and the mark count. -/

open Finset
open scoped Classical
namespace Bounty

theorem exists_physical_root_scaled_history_integral_bound {qmax vs : ℝ}
    (hqmax0 : 0 ≤ qmax) (hqmax1 : qmax < 1) (hvs : 0 < vs) (ell : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧
    ∀ (I : Type) (N M J n B : ℕ) (P : Fin N → Finset ℕ)
      (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
      [∀ g (p : P (e.symm g).val), NeZero p.val]
      (patterns : Finset I) (C : I → Fin N → Finset (Fin J)) (k : ℕ → I → ℤ)
      (V : Fin N → ℝ) (q : ℝ) (β : (g : Fin M) → P (e.symm g).val → ℝ)
      (retention : Fin (n + 2) → ℝ) (ρ : ℝ),
      (∀ s : ↥groupsᶜ, vs ≤ V s.val) → Real.sqrt q ≤ qmax →
      ∀ (_i0 : patterns) (v vmin : ℝ) (η : Fin M → ℝ) (τ : ℝ) (T : ℕ),
      (∀ g, ∑ p ∈ P (e.symm g).val, 1 / (p : ℝ) = V (e.symm g).val) →
      (∀ g p, 0 ≤ β g p / V (e.symm g).val) →
      (∀ g, ∑ p, β g p / V (e.symm g).val ≤ 2) →
      (∀ g, 0 ≤ η g) → (∀ g p, β g p / V (e.symm g).val ≤ η g) →
      (∀ j g, (|(1 - retention j) * V (e.symm g).val / ρ| * η g) * v ≤ τ) →
      (∀ g, η g ≤ τ) → (∀ j, 0 ≤ retention j) → (∀ j, retention j ≤ 1) →
      0 < ρ → ρ < 1 → 1 < v → 0 < vmin →
      (∀ g, vmin ≤ V (e.symm g).val) →
      (∀ j, retention j / ρ ^ 2 + ((1 - retention j) / ρ) / v ≤ 1) →
      (∀ (i : patterns) g, (physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val))ᶜ.card ≤ T) →
      0 ≤ τ →
      ∀ (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B)),
      (∀ i, fullMixedCommonIndexStage (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) i = 0 → code i = none) →
      ∀ (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e)
      (history : Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) →
        Option ((g : Fin M) × P (e.symm g).val))
      (F : PhysicalRootMixedPath (n := n) groups e patterns C k s → ℝ)
      (Lbound : ℝ), 0 ≤ Lbound →
      (∀ p, F p ≤ Lbound) →
      physicalRootHistoryIntegral groups e patterns C k V q β retention ρ code s history F ≤
        τ ^ birthForestRank code *
          (((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))).map
            (physicalMixedSmallRowFactor A groupsᶜ.card patterns.card)).prod *
          (((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))).map
            (fullMixedLengthRowFactor (fun g p => β g p / V (e.symm g).val)
              retention ρ v vmin (fun g => V (e.symm g).val) T)).prod *
          (Lbound * productLengthLyapunov v s.2) := by
  obtain ⟨A, hA, hbound⟩ := exists_physical_mixed_history_integral_bound hqmax0 hqmax1 hvs ell
  refine ⟨A, hA, ?_⟩
  intro I N M J n B P groups e _ patterns C k V q β retention ρ hVs hq i0 v vmin η τ T
    hMass hμ hmass hη hμatom hghost hedge hq0 hq1 hρ0 hρ1 hv hvmin hV hD ht hτ
    code hcode s history F Lbound hL hF
  have hVpos : ∀ g, 0 < V (e.symm g).val := fun g => hvmin.trans_le (hV g)
  have h := hbound ↥groupsᶜ ↥patterns (Fin (n + 2)) (Fin (n + 1)) M
    (fun s => P s.val) (fun g => ↥(P (e.symm g).val))
    (fun g (p : P (e.symm g).val) => p.val) J (fun _ => J + ell)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) B
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (i : patterns) _ aux => physicalAuxMass (fun g => V (e.symm g).val) (fun g => C i.val (e.symm g).val) aux)
    (fun g p => β g p / V (e.symm g).val) retention ρ (fun g => V (e.symm g).val)
    (fun s : ↥groupsᶜ => V s.val) (fun _ => q) hVs (fun _ => hq) i0 v vmin η τ T
    (fun i _ a => physical_aux_mass_nonneg _ _ (fun g => (hVpos g).le) a)
    (fun i _ => (physical_aux_mass_sum _ _ hVpos hMass).le)
    hμ hmass hη hμatom hghost hedge hq0 hq1 hρ0 hρ1 hv hvmin hV hD ht hτ
    ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) code hcode s history F Lbound
    hL (fun p => (hF p).trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (productLengthLyapunov_one_le hv.le _) hL))
  simp only [Fintype.card_coe] at h
  convert h using 1
  rfl

end Bounty

end


-- Source module: PhysicalRootForestData
section

/- The exact local residual on an original root mixed path. Small-prime
factors are deliberately retained in the original real path weight. -/

open scoped Classical
namespace Bounty
section Root
variable {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
  (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
  (k : ℕ → I → ℤ)
  (pl : PhysicalRootSmallPlan (P := P) (J := J) (ell := ell) (n := n) groups patterns)
  (V : Fin N → ℝ) (q : ℝ) (ζ : ℕ → I → ℝ)
  (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
    PhysicalAuxLabels P (C i) → ℂ)
  (r : PhysicalGroupResidues P groupsᶜ) (θ : ℝ)
  (β : (g : Fin M) → P (e.symm g).val → ℝ)
  (retention : Fin (n + 2) → ℝ) (ρ : ℝ)

noncomputable def physicalRootEffectiveForestResidual
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B)
    (path : PhysicalEffectivePlannedBigPath
      (fun (i : patterns) g => C i.val (e.symm g).val)
      (fun (j : Fin (n + 1)) (i : patterns) => k (n - j.val) i.val) B
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
      pl.1 pl.2 x) : ℂ :=
  let Cb := fun key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val)
    (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      fun g => C key.2.1.val (e.symm g).val
  let kb := fun key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val)
    (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      k (n - key.1.val) key.2.1.val * (physicalSharedProduct (physicalSharedPrefix key.2.2.1) : ℕ)
  let steps := physicalMixedBigSteps
    ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) pl.1 pl.2
  let sizes := fun g (p : P (e.symm g).val) => p.val
  let shared := fun key g => physicalFullSharedIndices (ell := ell) (Cb key g)
  let aux := fun key (_ : SharedActiveLabels (fun g => ↥(P (e.symm g).val)) (shared key)) =>
    PhysicalAuxLabels (fun g => P (e.symm g).val) (Cb key)
  let delta := fun key => physicalFullEdgeDelta (P := fun g => P (e.symm g).val) (ell := ell) (Cb key) (kb key)
  let displacement := fun key => physicalFullEdgeD (P := fun g => P (e.symm g).val) (ell := ell) (Cb key)
  let omega := fun key (_ : SharedActiveLabels (fun g => ↥(P (e.symm g).val)) (shared key)) (a : PhysicalAuxLabels (fun g => P (e.symm g).val) (Cb key)) =>
    physicalAuxMass (fun g => V (e.symm g).val) (Cb key) a
  finiteEventLocalPhase (FullPermutationMixedEvent sizes shared B aux delta displacement)
    (fullPermutationMixedEventTarget sizes shared B aux delta displacement)
    (fullMixedBirthResidualPhase sizes shared B aux delta displacement
      (physicalFullCombinedEdgePhase Cb kb omega β ρ (fun g => V (e.symm g).val) (fun _ => 0)
        (physicalRootKeyCoefficient groups e patterns C hC ζ k K θ))) steps x path

variable
  (hPs : ∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p)
  (hPb : ∀ (g : Fin M) p, p ∈ P (e.symm g).val → Nat.Prime p)
  (hdis : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (e.symm g).val))

noncomputable def physicalRootForestResidual
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e)
    (path : PhysicalRootMixedPath (n := n) groups e patterns C k s) : ℂ :=
  let z := physicalRootMixedPackingEquiv groups e patterns C k s.1.1 s.1.2 s.2 path
  physicalRootEffectiveForestResidual groups e patterns C hC k (s.1.2, z.1)
    V ζ K θ β ρ s.2
    (physicalRootPlannedEffectiveEquiv groups e patterns C k hPs hPb hdis
      (s.1.2, z.1) s.2 z.2)

noncomputable def physicalRootForestHistoryFactor
    (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e)
    (path : PhysicalRootMixedPath (n := n) groups e patterns C k s) : ℝ :=
  let sizes := fun g (p : P (e.symm g).val) => p.val
  let shared := fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)
  let aux := fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val)
    (fun g => C i.val (e.symm g).val)
  let delta := fun (j : Fin (n + 1)) (i : patterns) =>
    physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val)
  let displacement := fun (_ : Fin (n + 1)) (i : patterns) =>
    physicalMixedEdgeD (fun g => C i.val (e.symm g).val)
  let steps := (List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))
  finiteEventHistoryFactor (PhysicalRootMixedEvent groups e patterns C k)
    (physicalRootMixedTarget groups e patterns C k)
    (physicalMixedCommonHistoryUpdate sizes shared B aux delta displacement steps)
    (physicalMixedCommonHistoryGain sizes shared B aux delta displacement steps code)
    0 steps s path (fullMixedCommonHistorySeed sizes B steps s.2 (fun _ => none))

noncomputable def physicalRootForestOriginalWeight
    (tag : Option (Fin (n + 2) ⊕ Fin (n + 1)))
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e)
    (event : PhysicalRootMixedEvent groups e patterns C k tag s) : ℝ :=
  physicalMixedWordWeight (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) B
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (i : patterns) _ aux => physicalAuxMass (fun g => V (e.symm g).val) (fun g => C i.val (e.symm g).val) aux)
    (fun g p => β g p / V (e.symm g).val) retention ρ (fun g => V (e.symm g).val)
    (fun s : ↥groupsᶜ => V s.val) (fun _ => q) tag s event

end Root
end Bounty

end


-- Source module: IndexedHistoryRelation
section

/- Chronological history comparisons need update agreement only at the actual
scheduled tag. This permits fixed-plan histories to share one original clock. -/

namespace Bounty

theorem finite_event_history_factor_rel_on
    {K X H H' : Type*} (E : K → X → Type*) (target : ∀ k x, E k x → X)
    (update : ∀ (_t : ℕ) k x, E k x → H → H)
    (update' : ∀ (_t : ℕ) k x, E k x → H' → H')
    (gain : ∀ (_t : ℕ) k x, E k x → H → ℝ)
    (gain' : ∀ (_t : ℕ) k x, E k x → H' → ℝ)
    (R : H → H' → Prop) (Good : ℕ → K → Prop)
    (hupdate : ∀ t k x e h h', Good t k → R h h' →
      R (update t k x e h) (update' t k x e h'))
    (hgain : ∀ t k x e h h', Good t k → R h h' →
      gain t k x e h = gain' t k x e h')
    (t : ℕ) (ks : List K)
    (hks : ∀ u : Fin ks.length, Good (t + u.val) (ks.get u))
    (x : X) (p : FiniteEventPath E target ks x) (h : H) (h' : H') (hh : R h h') :
    finiteEventHistoryFactor E target update gain t ks x p h =
      finiteEventHistoryFactor E target update' gain' t ks x p h' := by
  induction ks generalizing t x h h' with
  | nil => rfl
  | cons k ks ih =>
    rcases p with ⟨e,p⟩
    have hk : Good t k := by simpa using hks ⟨0, by simp⟩
    have htail : ∀ u : Fin ks.length, Good (t + 1 + u.val) (ks.get u) := by
      intro u
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hks u.succ
    simp only [finiteEventHistoryFactor]
    rw [hgain t k x e h h' hk hh]
    exact congrArg (gain' t k x e h' * ·)
      (ih (t + 1) htail _ p _ _ (hupdate t k x e h h' hk hh))

end Bounty

end


-- Source module: PhysicalPlanHistoryFactor
section

/- The original common history and the fixed small-plan history give exactly
the same causal factor along every decorated big path. -/

namespace Bounty
section Factor
variable {S I V K : Type} {N : ℕ}
  {Ps : S → Finset ℕ} {P : Fin N → Type}
  (n : ∀ g, P g → ℕ) {J ell : ℕ} {M : Fin N → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (A : I → Type)
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J →
    SharedActiveLabels P (shared i) → A i → Fin N → ℤ)

theorem physical_plan_common_history_factor
    (tags : List (Option (V ⊕ PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K))))
    (steps : List (Option (V ⊕ K)))
    (hshape : fullMixedCommonShape M B tags = fullMixedCommonShape M B steps)
    (htags : ∀ u : Fin tags.length, physicalMixedBigTagErase (tags.get u) =
      steps.get (Fin.cast (congrArg Sigma.fst hshape) u))
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B tags)))
    (code' : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
    (hc : HEq code code')
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (p : FiniteEventPath (PhysicalMixedDecoratedBigEvent n shared B A Δ D)
      (physicalMixedDecoratedBigTarget n shared B A Δ D) tags x)
    (history : Fin (Fintype.card (FullMixedCommonBirthAddress M B tags)) → Option (Sigma P))
    (history' : Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) → Option (Sigma P))
    (hh : HEq history history') :
    finiteEventHistoryFactor (PhysicalMixedDecoratedBigEvent n shared B A Δ D)
      (physicalMixedDecoratedBigTarget n shared B A Δ D)
      (physicalDecoratedPlanHistoryUpdate n shared B A Δ D tags)
      (physicalDecoratedPlanHistoryGain n shared B A Δ D tags code)
      0 tags x p history =
    finiteEventHistoryFactor (PhysicalMixedDecoratedBigEvent n shared B A Δ D)
      (physicalMixedDecoratedBigTarget n shared B A Δ D)
      (physicalDecoratedCommonHistoryWrite n shared B A Δ D steps)
      (physicalDecoratedCommonHistoryGain n shared B A Δ D steps code')
      0 tags x p history' := by
  refine finite_event_history_factor_rel_on
    (PhysicalMixedDecoratedBigEvent n shared B A Δ D)
    (physicalMixedDecoratedBigTarget n shared B A Δ D)
    (physicalDecoratedPlanHistoryUpdate n shared B A Δ D tags)
    (physicalDecoratedCommonHistoryWrite n shared B A Δ D steps)
    (physicalDecoratedPlanHistoryGain n shared B A Δ D tags code)
    (physicalDecoratedCommonHistoryGain n shared B A Δ D steps code')
    (fun h h' => HEq h h') (fun t tag => ∃ u : Fin tags.length, u.val = t ∧ tags.get u = tag)
    ?_ ?_ 0 tags ?_ x p history history' hh
  · intro t tag x e h h' ht hh
    rcases ht with ⟨u, rfl, rfl⟩
    have huv : HEq u (Fin.cast (congrArg Sigma.fst hshape) u) :=
      (Fin.heq_ext_iff (congrArg Sigma.fst hshape)).2 rfl
    exact physical_plan_history_update_heq n shared B A Δ D tags steps hshape u
      (Fin.cast (congrArg Sigma.fst hshape) u) huv (htags u) x e h h' hh
  · intro t tag x e h h' ht hh
    rcases ht with ⟨u, rfl, rfl⟩
    have huv : HEq u (Fin.cast (congrArg Sigma.fst hshape) u) :=
      (Fin.heq_ext_iff (congrArg Sigma.fst hshape)).2 rfl
    exact physical_plan_history_gain_eq n shared B A Δ D tags steps hshape u
      (Fin.cast (congrArg Sigma.fst hshape) u) huv (htags u) x e h h' hh code code' hc
  · intro u
    exact ⟨u, (Nat.zero_add _).symm, rfl⟩

end Factor
end Bounty

end


-- Source module: PhysicalPlanHistoryMask
section

/- Exact compatibility masks can be evaluated by the single original
schedule history even after fixing a small plan. -/

open scoped Classical
namespace Bounty
section Mask
variable {S I V K : Type} {N : ℕ}
  {Ps : S → Finset ℕ} {P : Fin N → Type}
  (n : ∀ g, P g → ℕ) {J ell : ℕ} {M : Fin N → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (A : I → Type)
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J →
    SharedActiveLabels P (shared i) → A i → Fin N → ℤ)

theorem physical_plan_common_history_mask
    (steps : List (Option (V ⊕ K))) (L : PhysicalMarkLists Ps J ell)
    (pl : PhysicalMixedSmallPlan (I := I) steps)
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
    (hcode : ∀ i, fullMixedCommonIndexStage M B (physicalMixedBigSteps steps L pl) i = 0 →
      (physicalMixedCommonForestEquiv M B steps L pl).symm code i = none)
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (p : FiniteEventPath (PhysicalMixedDecoratedBigEvent n shared B A Δ D)
      (physicalMixedDecoratedBigTarget n shared B A Δ D) (physicalMixedBigSteps steps L pl) x)
    (history : Fin (Fintype.card (FullMixedCommonBirthAddress M B (physicalMixedBigSteps steps L pl))) → Option (Sigma P))
    (history' : Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) → Option (Sigma P))
    (hh : HEq history history') :
    finiteEventHistoryFactor (PhysicalMixedDecoratedBigEvent n shared B A Δ D)
      (physicalMixedDecoratedBigTarget n shared B A Δ D)
      (physicalDecoratedCommonHistoryWrite n shared B A Δ D steps)
      (physicalDecoratedCommonHistoryGain n shared B A Δ D steps code)
      0 (physicalMixedBigSteps steps L pl) x p
      (fullMixedCommonHistorySeed n B steps x history') =
    if birthForestCompatible
      (fun i => fullMixedCommonBirthPerformed n
        (fun key : PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K) => shared key.2.1) B
        (fun key _ => A key.2.1)
        (fun key c a => Δ key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)
        (fun key c a => D key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)
        (physicalMixedBigSteps steps L pl) x p
        (fullMixedCommonBirthOrder M B (physicalMixedBigSteps steps L pl) i))
      (fun i => fullMixedCommonBirthLabel n
        (fun key : PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K) => shared key.2.1) B
        (fun key _ => A key.2.1)
        (fun key c a => Δ key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)
        (fun key c a => D key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)
        (physicalMixedBigSteps steps L pl) x p
        (fullMixedCommonBirthOrder M B (physicalMixedBigSteps steps L pl) i))
      ((physicalMixedCommonForestEquiv M B steps L pl).symm code)
    then 1 else 0 := by
  have hs := physical_mixed_big_common_shape M B steps L pl
  have hc : HEq ((physicalMixedCommonForestEquiv M B steps L pl).symm code) code :=
    cast_heq _ code
  have hhseed : HEq
      (fullMixedCommonHistorySeed n B (physicalMixedBigSteps steps L pl) x history)
      (fullMixedCommonHistorySeed n B steps x history') := by
    rw [full_mixed_common_history_seed_shape, full_mixed_common_history_seed_shape]
    exact full_mixed_shape_history_seed_heq n B hs x hh
  have hfactor := physical_plan_common_history_factor n shared B A Δ D
    (physicalMixedBigSteps steps L pl) steps hs
    (physical_mixed_big_tag_at_position M B steps L pl)
    ((physicalMixedCommonForestEquiv M B steps L pl).symm code) code hc x p
    (fullMixedCommonHistorySeed n B (physicalMixedBigSteps steps L pl) x history)
    (fullMixedCommonHistorySeed n B steps x history') hhseed
  rw [← hfactor]
  exact full_mixed_common_forest_history_factor n _ B _ _ _
    (physicalMixedBigSteps steps L pl) _ hcode x p history

end Mask
end Bounty

end


-- Source module: IndexedHistoryPacking
section

/- Time-indexed real history factors commute with the original small-plan
packing. The small ledger and all big path choices remain unchanged. -/

open scoped Classical
namespace Bounty

theorem finite_event_history_factor_eq_complex_ledger
    {K X H : Type*} (E : K → X → Type*)
    (target : ∀ k x, E k x → X)
    (update : ∀ (_t : ℕ) k x, E k x → H → H)
    (gain : ∀ (_t : ℕ) k x, E k x → H → ℝ)
    (t : ℕ) (steps : List K) (x : X) (p : FiniteEventPath E target steps x) (h : H) :
    (finiteEventHistoryFactor E target update gain t steps x p h : ℂ) =
      deterministicLedgerPhase E target
        (fun k (th : ℕ × H) x e => (th.1 + 1, update th.1 k x e th.2))
        (fun k (th : ℕ × H) x e => (gain th.1 k x e th.2 : ℂ)) steps (t, h) x p := by
  induction steps generalizing t x h with
  | nil => rfl
  | cons k steps ih =>
    rcases p with ⟨e, p⟩
    simp only [finiteEventHistoryFactor, deterministicLedgerPhase, Complex.ofReal_mul]
    exact congrArg ((gain t k x e h : ℂ) * ·) (ih (t + 1) _ p _)

section Packing
variable {S G I V K H : Type} [Fintype S]
  {Ps : S → Finset ℕ} {P : G → Type}
  (n : ∀ g, P g → ℕ)
  {J ell : ℕ} {M : G → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (A : I → Type)
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J →
    SharedActiveLabels P (shared i) → A i → G → ℤ)
  (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)
  (update : ∀ (_t : ℕ) tag,
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) →
    PhysicalMixedDecoratedBigEvent (V := V) (ell := ell) n shared B A Δ D tag x → H → H)
  (gain : ∀ (_t : ℕ) tag,
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) →
    PhysicalMixedDecoratedBigEvent (V := V) (ell := ell) n shared B A Δ D tag x → H → ℝ)

theorem physical_mixed_indexed_history_pack
    (t : ℕ) (ks : List (Option (V ⊕ K))) (h : H)
    (r : PhysicalResidues Ps) (L : PhysicalMarkLists Ps J ell)
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (z : Σ pl : PhysicalMixedSmallPlan (I := I) ks,
      PhysicalMixedPlannedBigPath n shared B A Δ D ks L pl x) :
    finiteEventHistoryFactor
      (PhysicalMixedWordEvent n shared B A Δ D)
      (physicalMixedWordTarget n shared B A Δ D kbig)
      (fun t tag s e h => physicalMixedBigEventPullback n shared B A Δ D
        (fun tag h x e => update t tag x e h) tag h s e)
      (fun t tag s e h => physicalMixedBigEventPullback n shared B A Δ D
        (fun tag h x e => gain t tag x e h) tag h s e)
      t ks ((r, L), x) (physicalMixedPathPack n shared B A Δ D kbig ks r L x z) h =
    finiteEventHistoryFactor
      (PhysicalMixedDecoratedBigEvent n shared B A Δ D)
      (physicalMixedDecoratedBigTarget n shared B A Δ D)
      update gain t (physicalMixedBigSteps ks L z.1) x z.2 h := by
  apply Complex.ofReal_injective
  rw [finite_event_history_factor_eq_complex_ledger]
  exact (physical_mixed_projected_history_pack n shared B A Δ D kbig
    (fun tag (th : ℕ × H) x e => (th.1 + 1, update th.1 tag x e th.2))
    (fun tag (th : ℕ × H) x e => (gain th.1 tag x e th.2 : ℂ)) ks (t, h) r L x z).trans
    (finite_event_history_factor_eq_complex_ledger
      (PhysicalMixedDecoratedBigEvent n shared B A Δ D)
      (physicalMixedDecoratedBigTarget n shared B A Δ D) update gain t
      (physicalMixedBigSteps ks L z.1) x z.2 h).symm

end Packing
end Bounty

end


-- Source module: PhysicalCommonHistoryPacking
section

/- The exact original mixed path and the fixed small-plan path have the same
seeded forest-history factor. Every outgoing small choice remains in the path. -/

namespace Bounty
section Packing
variable {S I V K : Type} [Fintype S] {N : ℕ}
  {Ps : S → Finset ℕ} {P : Fin N → Type}
  (n : ∀ g, P g → ℕ) {J ell : ℕ} {M : Fin N → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (A : I → Type)
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J →
    SharedActiveLabels P (shared i) → A i → Fin N → ℤ)
  (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)

theorem physical_mixed_common_history_pack
    (steps : List (Option (V ⊕ K)))
    (r : PhysicalResidues Ps) (L : PhysicalMarkLists Ps J ell)
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (z : Σ pl : PhysicalMixedSmallPlan (I := I) steps,
      PhysicalMixedPlannedBigPath n shared B A Δ D steps L pl x)
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
    (history : Fin (Fintype.card (FullMixedCommonBirthAddress M B (physicalMixedBigSteps steps L z.1))) → Option (Sigma P))
    (history' : Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) → Option (Sigma P))
    (hh : HEq history history') :
    finiteEventHistoryFactor
      (PhysicalMixedWordEvent n shared B A Δ D)
      (physicalMixedWordTarget n shared B A Δ D kbig)
      (fun t tag s e h => physicalMixedBigEventPullback n shared B A Δ D
        (fun tag h x e => physicalDecoratedCommonHistoryWrite n shared B A Δ D steps t tag x e h) tag h s e)
      (fun t tag s e h => physicalMixedBigEventPullback n shared B A Δ D
        (fun tag h x e => physicalDecoratedCommonHistoryGain n shared B A Δ D steps code t tag x e h) tag h s e)
      0 steps ((r, L), x) (physicalMixedPathPack n shared B A Δ D kbig steps r L x z)
      (fullMixedCommonHistorySeed n B steps x history') =
    finiteEventHistoryFactor (PhysicalMixedDecoratedBigEvent n shared B A Δ D)
      (physicalMixedDecoratedBigTarget n shared B A Δ D)
      (physicalDecoratedPlanHistoryUpdate n shared B A Δ D (physicalMixedBigSteps steps L z.1))
      (physicalDecoratedPlanHistoryGain n shared B A Δ D (physicalMixedBigSteps steps L z.1)
        ((physicalMixedCommonForestEquiv M B steps L z.1).symm code))
      0 (physicalMixedBigSteps steps L z.1) x z.2
      (fullMixedCommonHistorySeed n B (physicalMixedBigSteps steps L z.1) x history) := by
  rw [physical_mixed_indexed_history_pack]
  have hs := physical_mixed_big_common_shape M B steps L z.1
  have hc : HEq ((physicalMixedCommonForestEquiv M B steps L z.1).symm code) code := cast_heq _ code
  have hhseed : HEq
      (fullMixedCommonHistorySeed n B (physicalMixedBigSteps steps L z.1) x history)
      (fullMixedCommonHistorySeed n B steps x history') := by
    rw [full_mixed_common_history_seed_shape, full_mixed_common_history_seed_shape]
    exact full_mixed_shape_history_seed_heq n B hs x hh
  exact (physical_plan_common_history_factor n shared B A Δ D
    (physicalMixedBigSteps steps L z.1) steps hs
    (physical_mixed_big_tag_at_position M B steps L z.1)
    ((physicalMixedCommonForestEquiv M B steps L z.1).symm code) code hc x z.2
    (fullMixedCommonHistorySeed n B (physicalMixedBigSteps steps L z.1) x history)
    (fullMixedCommonHistorySeed n B steps x history') hhseed).symm

end Packing
end Bounty

end


-- Source module: FullMixedShapeInitialCondition
section

/- The no-initial-child condition transports with the common forest code. -/

namespace Bounty

theorem full_mixed_shape_initial_condition_iff {N : ℕ} (M : Fin N → ℕ)
    {shape shape' : FullMixedCommonShapeData N} (hs : shape = shape')
    {code : BirthForestCode (Fintype.card (FullMixedCommonShapeAddress M shape))}
    {code' : BirthForestCode (Fintype.card (FullMixedCommonShapeAddress M shape'))}
    (hc : HEq code code') :
    (∀ i, fullMixedShapeIndexStage M shape i = 0 → code i = none) ↔
      (∀ i, fullMixedShapeIndexStage M shape' i = 0 → code' i = none) := by
  cases hs
  cases eq_of_heq hc
  rfl

theorem physical_mixed_plan_initial_condition_iff
    {S I V K : Type} {Ps : S → Finset ℕ} {J ell N : ℕ}
    (M : Fin N → ℕ) (B : ℕ) (steps : List (Option (V ⊕ K)))
    (L : PhysicalMarkLists Ps J ell) (pl : PhysicalMixedSmallPlan (I := I) steps)
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps))) :
    (∀ i, fullMixedCommonIndexStage M B (physicalMixedBigSteps steps L pl) i = 0 →
      ((physicalMixedCommonForestEquiv M B steps L pl).symm code) i = none) ↔
      (∀ i, fullMixedCommonIndexStage M B steps i = 0 → code i = none) := by
  rw [full_mixed_index_stage_shape, full_mixed_index_stage_shape]
  exact full_mixed_shape_initial_condition_iff M
    (physical_mixed_big_common_shape M B steps L pl) (cast_heq _ code)

end Bounty

end


-- Source module: PhysicalMixedPackedHistoryMask
section

/- The original mixed path carries exactly the compatibility mask of its
fixed small-plan path, with the original common forest code and history. -/

open scoped Classical
namespace Bounty

section PackedMask
variable {S I V K : Type} [Fintype S] {N : ℕ}
  {Ps : S → Finset ℕ} {P : Fin N → Type}
  (n : ∀ g, P g → ℕ) {J ell : ℕ} {M : Fin N → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (A : I → Type)
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J →
    SharedActiveLabels P (shared i) → A i → Fin N → ℤ)
  (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)

theorem physical_mixed_packed_history_mask
    (steps : List (Option (V ⊕ K)))
    (r : PhysicalResidues Ps) (L : PhysicalMarkLists Ps J ell)
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (z : Σ pl : PhysicalMixedSmallPlan (I := I) steps,
      PhysicalMixedPlannedBigPath n shared B A Δ D steps L pl x)
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
    (hcode : ∀ i, fullMixedCommonIndexStage M B steps i = 0 → code i = none)
    (history : Fin (Fintype.card (FullMixedCommonBirthAddress M B
      (physicalMixedBigSteps steps L z.1))) → Option (Sigma P))
    (history' : Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) → Option (Sigma P))
    (hh : HEq history history') :
    finiteEventHistoryFactor
      (PhysicalMixedWordEvent n shared B A Δ D)
      (physicalMixedWordTarget n shared B A Δ D kbig)
      (fun t tag s e h => physicalMixedBigEventPullback n shared B A Δ D
        (fun tag h x e => physicalDecoratedCommonHistoryWrite n shared B A Δ D
          steps t tag x e h) tag h s e)
      (physicalMixedCommonHistoryGain n shared B A Δ D steps code)
      0 steps ((r, L), x) (physicalMixedPathPack n shared B A Δ D kbig steps r L x z)
      (fullMixedCommonHistorySeed n B steps x history') =
    if birthForestCompatible
      (fun i => fullMixedCommonBirthPerformed n
        (fun key : PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell)
          (I := I) (K := K) => shared key.2.1) B
        (fun key _ => A key.2.1)
        (fun key c a => Δ key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)
        (fun key c a => D key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)
        (physicalMixedBigSteps steps L z.1) x z.2
        (fullMixedCommonBirthOrder M B (physicalMixedBigSteps steps L z.1) i))
      (fun i => fullMixedCommonBirthLabel n
        (fun key : PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell)
          (I := I) (K := K) => shared key.2.1) B
        (fun key _ => A key.2.1)
        (fun key c a => Δ key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)
        (fun key c a => D key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)
        (physicalMixedBigSteps steps L z.1) x z.2
        (fullMixedCommonBirthOrder M B (physicalMixedBigSteps steps L z.1) i))
      ((physicalMixedCommonForestEquiv M B steps L z.1).symm code)
    then 1 else 0 := by
  have hplan := (physical_mixed_plan_initial_condition_iff M B steps L z.1 code).2 hcode
  have hpack := physical_mixed_indexed_history_pack n shared B A Δ D kbig
    (physicalDecoratedCommonHistoryWrite n shared B A Δ D steps)
    (physicalDecoratedCommonHistoryGain n shared B A Δ D steps code)
    0 steps (fullMixedCommonHistorySeed n B steps x history') r L x z
  exact hpack.trans (physical_plan_common_history_mask n shared B A Δ D
    steps L z.1 code hplan x z.2 history history' hh)

end PackedMask
end Bounty

end


-- Source module: PhysicalPackedHistoryZeroSeed
section

/- The exact packed forest mask with the empty common history. -/

open scoped Classical
namespace Bounty

section ZeroSeed
variable {S I V K : Type} [Fintype S] {N : ℕ}
  {Ps : S → Finset ℕ} {P : Fin N → Type}
  (n : ∀ g, P g → ℕ) {J ell : ℕ} {M : Fin N → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (A : I → Type)
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J →
    SharedActiveLabels P (shared i) → A i → Fin N → ℤ)
  (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)
  (steps : List (Option (V ⊕ K)))
  (r : PhysicalResidues Ps) (L : PhysicalMarkLists Ps J ell)
  (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
  (z : Σ pl : PhysicalMixedSmallPlan (I := I) steps,
    PhysicalMixedPlannedBigPath n shared B A Δ D steps L pl x)
  (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))

theorem physical_mixed_packed_history_zero_seed
    (hcode : ∀ i, fullMixedCommonIndexStage M B steps i = 0 → code i = none) :
    finiteEventHistoryFactor
      (PhysicalMixedWordEvent n shared B A Δ D)
      (physicalMixedWordTarget n shared B A Δ D kbig)
      (fun t tag s e h => physicalMixedBigEventPullback n shared B A Δ D
        (fun tag h x e => physicalDecoratedCommonHistoryWrite n shared B A Δ D
          steps t tag x e h) tag h s e)
      (physicalMixedCommonHistoryGain n shared B A Δ D steps code)
      0 steps ((r, L), x) (physicalMixedPathPack n shared B A Δ D kbig steps r L x z)
      (fullMixedCommonHistorySeed n B steps x (fun _ => none)) =
    if birthForestCompatible
      (fun i => fullMixedCommonBirthPerformed n
        (fun key : PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell)
          (I := I) (K := K) => shared key.2.1) B
        (fun key _ => A key.2.1)
        (fun key c a => Δ key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)
        (fun key c a => D key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)
        (physicalMixedBigSteps steps L z.1) x z.2
        (fullMixedCommonBirthOrder M B (physicalMixedBigSteps steps L z.1) i))
      (fun i => fullMixedCommonBirthLabel n
        (fun key : PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell)
          (I := I) (K := K) => shared key.2.1) B
        (fun key _ => A key.2.1)
        (fun key c a => Δ key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)
        (fun key c a => D key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)
        (physicalMixedBigSteps steps L z.1) x z.2
        (fullMixedCommonBirthOrder M B (physicalMixedBigSteps steps L z.1) i))
      ((physicalMixedCommonForestEquiv M B steps L z.1).symm code)
    then 1 else 0 := by
  have hnone (a b : ℕ) (h : a = b) :
      HEq (fun _ : Fin a => (none : Option (Sigma P)))
        (fun _ : Fin b => (none : Option (Sigma P))) := by
    subst b
    rfl
  exact physical_mixed_packed_history_mask n shared B A Δ D kbig steps r L x z code
    hcode (fun _ => none) (fun _ => none)
    (hnone _ _ (physical_mixed_big_common_card M B steps L z.1))

theorem physical_mixed_packed_history_zero_seed_nonneg
    (hcode : ∀ i, fullMixedCommonIndexStage M B steps i = 0 → code i = none) :
    0 ≤ finiteEventHistoryFactor
      (PhysicalMixedWordEvent n shared B A Δ D)
      (physicalMixedWordTarget n shared B A Δ D kbig)
      (fun t tag s e h => physicalMixedBigEventPullback n shared B A Δ D
        (fun tag h x e => physicalDecoratedCommonHistoryWrite n shared B A Δ D
          steps t tag x e h) tag h s e)
      (physicalMixedCommonHistoryGain n shared B A Δ D steps code)
      0 steps ((r, L), x) (physicalMixedPathPack n shared B A Δ D kbig steps r L x z)
      (fullMixedCommonHistorySeed n B steps x (fun _ => none)) := by
  rw [physical_mixed_packed_history_zero_seed n shared B A Δ D kbig steps r L x z code hcode]
  split_ifs <;> norm_num

end ZeroSeed
end Bounty

end


-- Source module: PhysicalRootForestPacking
section

/- Packing identities for the unchanged root residual and common-history mask. -/

open scoped Classical
namespace Bounty
section Root
variable {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
  (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
  (k : ℕ → I → ℤ)
  (pl : PhysicalRootSmallPlan (P := P) (J := J) (ell := ell) (n := n) groups patterns)
  (V : Fin N → ℝ) (q : ℝ) (ζ : ℕ → I → ℝ)
  (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
    PhysicalAuxLabels P (C i) → ℂ)
  (r : PhysicalGroupResidues P groupsᶜ) (θ : ℝ)
  (β : (g : Fin M) → P (e.symm g).val → ℝ)
  (retention : Fin (n + 2) → ℝ) (ρ : ℝ)

variable
  (hPs : ∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p)
  (hPb : ∀ (g : Fin M) p, p ∈ P (e.symm g).val → Nat.Prime p)
  (hdis : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (e.symm g).val))

theorem physical_root_forest_residual_pack
    (r0 : PhysicalResidues (fun t : ↥groupsᶜ => P t.val))
    (L : PhysicalMarkLists (fun t : ↥groupsᶜ => P t.val) J ell)
    (sp : PhysicalMixedSmallPlan (Ps := fun t : ↥groupsᶜ => P t.val)
      (J := J) (ell := ell) (I := patterns)
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B)
    (path : PhysicalRootPlannedPath groups e patterns C k (L, sp) x) :
    physicalRootForestResidual groups e patterns C hC k V ζ K θ β ρ hPs hPb hdis
      ((r0, L), x) ((physicalRootMixedPackingEquiv groups e patterns C k r0 L x).symm ⟨sp, path⟩) =
    physicalRootEffectiveForestResidual groups e patterns C hC k (L, sp) V ζ K θ β ρ x
      (physicalRootPlannedEffectiveEquiv groups e patterns C k hPs hPb hdis (L, sp) x path) := by
  unfold physicalRootForestResidual
  have h := (physicalRootMixedPackingEquiv groups e patterns C k r0 L x).apply_symm_apply ⟨sp, path⟩
  exact congrArg (fun z : Σ sp : PhysicalMixedSmallPlan
      (Ps := fun s : ↥groupsᶜ => P s.val) (J := J) (ell := ell) (I := patterns)
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))),
      PhysicalRootPlannedPath groups e patterns C k (L, sp) x =>
    physicalRootEffectiveForestResidual groups e patterns C hC k (L, z.1) V ζ K θ β ρ x
      (physicalRootPlannedEffectiveEquiv groups e patterns C k hPs hPb hdis (L, z.1) x z.2)) h

theorem physical_root_forest_history_nonneg
    (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (hcode : ∀ i, fullMixedCommonIndexStage (fun _ : Fin M => J + ell) B
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) i = 0 → code i = none)
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e)
    (path : PhysicalRootMixedPath (n := n) groups e patterns C k s) :
    0 ≤ physicalRootForestHistoryFactor groups e patterns C k code s path := by
  let z := physicalRootMixedPackingEquiv groups e patterns C k s.1.1 s.1.2 s.2 path
  have h := physical_mixed_packed_history_zero_seed_nonneg
    (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) B
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
    s.1.1 s.1.2 s.2 z code hcode
  change 0 ≤ physicalRootForestHistoryFactor groups e patterns C k code s
    ((physicalRootMixedPackingEquiv groups e patterns C k s.1.1 s.1.2 s.2).symm z) at h
  have hz : (physicalRootMixedPackingEquiv groups e patterns C k s.1.1 s.1.2 s.2).symm z = path :=
    (physicalRootMixedPackingEquiv groups e patterns C k s.1.1 s.1.2 s.2).symm_apply_apply path
  rw [hz] at h
  exact h

end Root
end Bounty

end


-- Source module: FullPermutationCommonPathBirth
section

/- Effective parameters preserve every initial and event birth label on the actual path. -/

open scoped Classical
namespace Bounty
section Birth
variable {J K : Type*} {N : ℕ} {P : Fin N → Type*}
  (n : ∀ g, P g → ℕ) {M : Fin N → ℕ}
  (S : K → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (A : ∀ k, SharedActiveLabels P (S k) → Type*)
  (Δ Δ' D D' : ∀ k c, A k c → Fin N → ℤ)
  (hΔ : ∀ k, Δ k = Δ' k)
  (hD : ∀ k c a g p, ((n g p : ℤ) ∣ D k c a g ↔ (n g p : ℤ) ∣ D' k c a g))

theorem full_permutation_parameter_common_path_label
    (steps : List (Option (J ⊕ K)))
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (p : FullPermutationMixedPath n S B A Δ D steps x)
    (a : FullMixedCommonStepAddress M B steps) :
    fullMixedCommonPathBirthLabel n S B A Δ' D' steps x
      (fullPermutationParameterPathEquiv n S B A Δ Δ' D D' hΔ hD steps x p) a =
      fullMixedCommonPathBirthLabel n S B A Δ D steps x p a := by
  rcases a with ⟨i, a⟩
  rw [full_mixed_common_path_label_occurrence, full_mixed_common_path_label_occurrence]
  have hh := finite_event_path_equiv_occurrence
    (FullPermutationMixedEvent n S B A Δ D) (FullPermutationMixedEvent n S B A Δ' D')
    (fullPermutationMixedEventTarget n S B A Δ D) (fullPermutationMixedEventTarget n S B A Δ' D')
    id (fullPermutationParameterEventEquiv n S B A Δ Δ' D D' hΔ hD)
    (fun tag x e => (full_permutation_parameter_target n S B A Δ Δ' D D' hΔ hD tag x e).symm)
    steps x p i
  change finiteEventPathOccurrence _ _ steps x
    (fullPermutationParameterPathEquiv n S B A Δ Δ' D D' hΔ hD steps x p) i = _ at hh
  rw [hh]
  dsimp only
  exact full_permutation_parameter_common_birth_label n S B A Δ Δ' D D' hΔ hD _ _ _ a

theorem full_permutation_parameter_common_total_label
    (steps : List (Option (J ⊕ K)))
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (p : FullPermutationMixedPath n S B A Δ D steps x)
    (a : FullMixedCommonBirthAddress M B steps) :
    fullMixedCommonBirthLabel n S B A Δ' D' steps x
      (fullPermutationParameterPathEquiv n S B A Δ Δ' D D' hΔ hD steps x p) a =
      fullMixedCommonBirthLabel n S B A Δ D steps x p a := by
  cases a with
  | inl a => rfl
  | inr a =>
    exact full_permutation_parameter_common_path_label n S B A Δ Δ' D D' hΔ hD steps x p a

end Birth
end Bounty

end


-- Source module: PhysicalEffectiveForestMask
section

/- Effective parameters preserve the full forest compatibility mask,
including performed guards and the original prime labels. -/

namespace Bounty

section Parameters
variable {J K : Type*} {N : ℕ} {P : Fin N → Type*}
  (n : ∀ g, P g → ℕ) {M : Fin N → ℕ}
  (S : K → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (A : ∀ k, SharedActiveLabels P (S k) → Type*)
  (Δ Δ' D D' : ∀ k c, A k c → Fin N → ℤ)
  (hΔ : ∀ k, Δ k = Δ' k)
  (hD : ∀ k c a g p, ((n g p : ℤ) ∣ D k c a g ↔ (n g p : ℤ) ∣ D' k c a g))

theorem full_permutation_parameter_forest_compatible
    (steps : List (Option (J ⊕ K)))
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (p : FullPermutationMixedPath n S B A Δ D steps x)
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps))) :
    birthForestCompatible
      (fullMixedCommonIndexedPerformed n S B A Δ' D' steps x
        (fullPermutationParameterPathEquiv n S B A Δ Δ' D D' hΔ hD steps x p))
      (fun i => fullMixedCommonBirthLabel n S B A Δ' D' steps x
        (fullPermutationParameterPathEquiv n S B A Δ Δ' D D' hΔ hD steps x p)
        (fullMixedCommonBirthOrder M B steps i)) code ↔
    birthForestCompatible
      (fullMixedCommonIndexedPerformed n S B A Δ D steps x p)
      (fun i => fullMixedCommonBirthLabel n S B A Δ D steps x p
        (fullMixedCommonBirthOrder M B steps i)) code := by
  have hl :
      (fun i => fullMixedCommonBirthLabel n S B A Δ' D' steps x
        (fullPermutationParameterPathEquiv n S B A Δ Δ' D D' hΔ hD steps x p)
        (fullMixedCommonBirthOrder M B steps i)) =
      (fun i => fullMixedCommonBirthLabel n S B A Δ D steps x p
        (fullMixedCommonBirthOrder M B steps i)) := by
    funext i
    exact full_permutation_parameter_common_total_label n S B A Δ Δ' D D' hΔ hD
      steps x p (fullMixedCommonBirthOrder M B steps i)
  have hp :
      fullMixedCommonIndexedPerformed n S B A Δ' D' steps x
        (fullPermutationParameterPathEquiv n S B A Δ Δ' D D' hΔ hD steps x p) =
      fullMixedCommonIndexedPerformed n S B A Δ D steps x p := by
    funext i
    exact congrArg (fun z : Option (Sigma P) => z.isSome = true) (congrFun hl i)
  rw [hl, hp]

end Parameters

section Physical
variable {S K V : Type*} [Fintype S] {N J ell : ℕ}
  {Ps : S → Finset ℕ} {P : Fin N → Finset ℕ}
  (hPs : ∀ s p, p ∈ Ps s → Nat.Prime p)
  (hP : ∀ g p, p ∈ P g → Nat.Prime p)
  (hdis : ∀ s g, Disjoint (Ps s) (P g))
  (C : K → Fin N → Finset (Fin J)) (d : K → PhysicalSharedLists Ps J)
  (k : K → ℤ) (B : ℕ)

theorem physical_mixed_effective_forest_compatible
    (steps : List (Option (V ⊕ K)))
    (x : PhysicalFullBoundedState P J ell B)
    (p : FullPermutationMixedPath (fun g (p : P g) => p.val)
      (fun key g => physicalFullSharedIndices (ell := ell) (C key g)) B
      (fun key _ => PhysicalAuxLabels P (C key))
      (fun key => physicalMixedEdgeDelta (C key) (k key) (d key))
      (fun key => physicalMixedEdgeD (C key) (d key)) steps x)
    (code : BirthForestCode (Fintype.card
      (FullMixedCommonBirthAddress (fun _ : Fin N => J + ell) B steps))) :
    birthForestCompatible
      (fullMixedCommonIndexedPerformed (fun g (p : P g) => p.val)
        (fun key g => physicalFullSharedIndices (ell := ell) (C key g)) B
        (fun key _ => PhysicalAuxLabels P (C key))
        (fun key => physicalFullEdgeDelta (C key) (k key * (physicalSharedProduct (d key) : ℕ)))
        (fun key => physicalFullEdgeD (C key)) steps x
        (physicalMixedEffectiveBigPathEquiv hPs hP hdis C d k B steps x p))
      (fun i => fullMixedCommonBirthLabel (fun g (p : P g) => p.val)
        (fun key g => physicalFullSharedIndices (ell := ell) (C key g)) B
        (fun key _ => PhysicalAuxLabels P (C key))
        (fun key => physicalFullEdgeDelta (C key) (k key * (physicalSharedProduct (d key) : ℕ)))
        (fun key => physicalFullEdgeD (C key)) steps x
        (physicalMixedEffectiveBigPathEquiv hPs hP hdis C d k B steps x p)
        (fullMixedCommonBirthOrder (fun _ : Fin N => J + ell) B steps i)) code ↔
    birthForestCompatible
      (fullMixedCommonIndexedPerformed (fun g (p : P g) => p.val)
        (fun key g => physicalFullSharedIndices (ell := ell) (C key g)) B
        (fun key _ => PhysicalAuxLabels P (C key))
        (fun key => physicalMixedEdgeDelta (C key) (k key) (d key))
        (fun key => physicalMixedEdgeD (C key) (d key)) steps x p)
      (fun i => fullMixedCommonBirthLabel (fun g (p : P g) => p.val)
        (fun key g => physicalFullSharedIndices (ell := ell) (C key g)) B
        (fun key _ => PhysicalAuxLabels P (C key))
        (fun key => physicalMixedEdgeDelta (C key) (k key) (d key))
        (fun key => physicalMixedEdgeD (C key) (d key)) steps x p
        (fullMixedCommonBirthOrder (fun _ : Fin N => J + ell) B steps i)) code := by
  exact full_permutation_parameter_forest_compatible _ _ B _ _ _ _ _
    (fun key => funext fun c => funext fun a => funext fun g =>
      physical_mixed_delta_effective_big_step (C key) (d key) (k key) c a g)
    (fun key c a g p => physical_mixed_dilation_divisibility hPs hP hdis (C key) (d key) c a g p)
    steps x p code

end Physical
end Bounty

end


-- Source module: PhysicalRootForestPlanned
section

/- The fixed-plan root forest is the original planned big action, retaining
its exact small factor, compatibility mask, and effective residual. -/

open Finset
open scoped Classical
namespace Bounty

section Root
variable {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
  (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
  (k : ℕ → I → ℤ)
  (pl : PhysicalRootSmallPlan (P := P) (J := J) (ell := ell) (n := n) groups patterns)

noncomputable def physicalRootPlannedForestCompatible
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
      (physicalMixedBigSteps ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) pl.1 pl.2))))
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B)
    (path : PhysicalRootPlannedPath groups e patterns C k pl x) : Prop :=
  let Cb := fun key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val)
    (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      fun g => C key.2.1.val (e.symm g).val
  let db := fun key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val)
    (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      physicalSharedPrefix key.2.2.1
  let kb := fun key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val)
    (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      k (n - key.1.val) key.2.1.val
  let steps := physicalMixedBigSteps
    ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) pl.1 pl.2
  let sizes := fun g (p : P (e.symm g).val) => p.val
  let shared := fun key g => physicalFullSharedIndices (ell := ell) (Cb key g)
  let aux := fun key (_ : SharedActiveLabels (fun g => ↥(P (e.symm g).val)) (shared key)) =>
    PhysicalAuxLabels (fun g => P (e.symm g).val) (Cb key)
  let delta := fun key => physicalMixedEdgeDelta (Cb key) (kb key) (db key)
  let displacement := fun key => physicalMixedEdgeD (Cb key) (db key)
  birthForestCompatible
    (fullMixedCommonIndexedPerformed sizes shared B aux delta displacement steps x path)
    (fun i => fullMixedCommonBirthLabel sizes shared B aux delta displacement steps x path
      (fullMixedCommonBirthOrder (fun _ : Fin M => J + ell) B steps i)) code

variable [∀ z : PhysicalPrime P, NeZero z.2.val]
  [∀ g (p : P (e.symm g).val), NeZero p.val]
  (V : Fin N → ℝ) (q : ℝ) (ζ : ℕ → I → ℝ)
  (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
    PhysicalAuxLabels P (C i) → ℂ)
  (r : PhysicalGroupResidues P groupsᶜ) (θ : ℝ)
  (β : (g : Fin M) → P (e.symm g).val → ℝ)
  (retention : Fin (n + 2) → ℝ) (ρ : ℝ)

theorem physical_root_effective_forest_eq_planned_action
    (hPs : ∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p)
    (hPb : ∀ (g : Fin M) p, p ∈ P (e.symm g).val → Nat.Prime p)
    (hdis : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (e.symm g).val))
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
      (physicalMixedBigSteps ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) pl.1 pl.2))))
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B) :
    physicalRootEffectiveForestAction groups e patterns C hC k pl V q ζ K r θ β retention ρ code f x =
    physicalMixedPlannedBigAction (fun g (p : P (e.symm g).val) => p.val)
      (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) B
      (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
      (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
      (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
      (fun (i : patterns) _ a => physicalAuxMass (fun g => V (e.symm g).val) (fun g => C i.val (e.symm g).val) a)
      (fun g p => β g p / V (e.symm g).val) retention ρ (fun g => V (e.symm g).val)
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) pl.1 pl.2
      (fun y path =>
        (physicalMixedPlanSmallFactor (fun g (p : P (e.symm g).val) => p.val)
          (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) B
          (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
          (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
          (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
          (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
          (fun s : ↥groupsᶜ => V s.val) (fun _ => q)
          ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
          (physicalGroupResidueVector r) pl.1 pl.2 y path : ℂ) *
        (if physicalRootPlannedForestCompatible groups e patterns C k pl code y path then 1 else 0) *
        physicalRootEffectiveForestResidual groups e patterns C hC k pl V ζ K θ β ρ y
          (physicalRootPlannedEffectiveEquiv groups e patterns C k hPs hPb hdis pl y path)) f x := by
  rw [physical_mixed_planned_effective_action hPs hPb hdis]
  dsimp only
  unfold physicalRootEffectiveForestAction fullPermutationMixedPathAction finiteEventPathAction
    birthForestPathSum
  dsimp only
  apply Finset.sum_congr
  · exact congrArg (fun inst : Fintype _ => @Finset.univ _ inst) (Subsingleton.elim _ _)
  · intro path _
    rw [physical_mixed_plan_small_factor_effective_pullback]
    have hmask := physical_mixed_effective_forest_compatible hPs hPb hdis
      (fun key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val)
        (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
          fun g => C key.2.1.val (e.symm g).val)
      (fun key => physicalSharedPrefix key.2.2.1)
      (fun key => k (n - key.1.val) key.2.1.val) B
      (physicalMixedBigSteps ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) pl.1 pl.2)
      x ((physicalRootPlannedEffectiveEquiv groups e patterns C k hPs hPb hdis pl x).symm path) code
    simp only [physicalRootPlannedEffectiveEquiv, Equiv.apply_symm_apply] at hmask ⊢
    unfold physicalRootPlannedForestCompatible
    dsimp only
    rw [← hmask]
    unfold fullMixedCommonResidualWeight physicalRootEffectiveForestResidual
    dsimp only
    split_ifs <;> ring

end Root
end Bounty

end


-- Source module: FinitePathMaskedNorm
section

/- Absolute domination of a real-masked complex path action, with all
original path weights retained inside the integral. -/

open scoped Classical
namespace Bounty

theorem finite_event_path_action_mask_norm_le
    {K X : Type} (E : K → X → Type) [∀ k x, Fintype (E k x)]
    (target : ∀ k x, E k x → X) (weight : ∀ k x, E k x → ℝ)
    (steps : List K) (mask : ∀ x, FiniteEventPath E target steps x → ℝ)
    (residual : ∀ x, FiniteEventPath E target steps x → ℂ)
    (f : X → ℂ) (x : X) (hmask : ∀ p, 0 ≤ mask x p) :
    ‖finiteEventPathAction E target weight steps
      (fun x p => (mask x p : ℂ) * residual x p) f x‖ ≤
    finiteEventPathIntegral E target (fun k x e => |weight k x e|) steps x
      (fun p => mask x p * (‖residual x p‖ * ‖f (finiteEventPathTerminal E target steps x p)‖)) := by
  unfold finiteEventPathAction finiteEventPathIntegral
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro p _
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hmask p), ← finite_event_path_weight_abs]
  exact le_of_eq (by ring)

end Bounty

end


-- Source module: PhysicalRootForestIntegral
section

/- Exact original forest-to-history action and absolute integral domination. -/

open Finset
open scoped Classical
namespace Bounty
section Root
variable {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  [∀ z : PhysicalPrime P, NeZero z.2.val]
  [∀ g (p : P (e.symm g).val), NeZero p.val]
  (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
  (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
  (k : ℕ → I → ℤ)
  (pl : PhysicalRootSmallPlan (P := P) (J := J) (ell := ell) (n := n) groups patterns)
  (V : Fin N → ℝ) (q : ℝ) (ζ : ℕ → I → ℝ)
  (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
    PhysicalAuxLabels P (C i) → ℂ)
  (r : PhysicalGroupResidues P groupsᶜ) (θ : ℝ)
  (β : (g : Fin M) → P (e.symm g).val → ℝ)
  (retention : Fin (n + 2) → ℝ) (ρ : ℝ)

variable
  (hPs : ∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p)
  (hPb : ∀ (g : Fin M) p, p ∈ P (e.symm g).val → Nat.Prime p)
  (hdis : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (e.symm g).val))

theorem physical_root_mixed_forest_eq_history_action
    (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (hcode : ∀ i, fullMixedCommonIndexStage (fun _ : Fin M => J + ell) B
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) i = 0 → code i = none)
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (L : PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B) :
    physicalRootMixedForestAction groups e patterns C hC k V q ζ K r θ β retention ρ code f L x =
    @finiteEventPathAction _ _ (PhysicalRootMixedEvent groups e patterns C k)
      (physicalMixedWordEventFintype (fun g (p : P (e.symm g).val) => p.val)
      (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) B
      (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
      (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
      (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val)))
      (physicalRootMixedTarget groups e patterns C k)
      (physicalRootForestOriginalWeight groups e patterns C k V q β retention ρ)
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) (fun s p => (physicalRootForestHistoryFactor groups e patterns C k code s p : ℂ) *
        physicalRootForestResidual groups e patterns C hC k V ζ K θ β ρ hPs hPb hdis s p) (fun s => f s.2) ((physicalGroupResidueVector r, L), x) := by
  symm
  unfold physicalRootMixedForestAction
  change physicalMixedWordPathAction (fun g (p : P (e.symm g).val) => p.val)
      (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) B
      (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
      (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
      (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
      (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
      (fun (i : patterns) _ aux => physicalAuxMass (fun g => V (e.symm g).val) (fun g => C i.val (e.symm g).val) aux)
      (fun g p => β g p / V (e.symm g).val) retention ρ (fun g => V (e.symm g).val)
      (fun s : ↥groupsᶜ => V s.val) (fun _ => q) ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) (fun s p => (physicalRootForestHistoryFactor groups e patterns C k code s p : ℂ) *
        physicalRootForestResidual groups e patterns C hC k V ζ K θ β ρ hPs hPb hdis s p) (fun s => f s.2) ((physicalGroupResidueVector r, L), x) = _
  rw [physical_mixed_paths_eq_original_big_paths]
  apply Finset.sum_congr rfl
  intro sp _
  unfold physicalRootCommonForestAction
  rw [physical_root_effective_forest_eq_planned_action groups e patterns C hC k (L, sp)
    V q ζ K r θ β retention ρ hPs hPb hdis]
  unfold physicalMixedPlannedBigAction fullPermutationMixedPathAction finiteEventPathAction
  apply Finset.sum_congr
  · exact congrArg (fun inst : Fintype _ => @Finset.univ _ inst) (Subsingleton.elim _ _)
  · intro path _
    dsimp only
    have hm := physical_mixed_packed_history_zero_seed
      (fun g (p : P (e.symm g).val) => p.val)
      (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) B
      (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
      (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
      (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
      (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) (physicalGroupResidueVector r) L x ⟨sp, path⟩ code hcode
    change physicalRootForestHistoryFactor groups e patterns C k code ((physicalGroupResidueVector r, L), x)
      ((physicalRootMixedPackingEquiv groups e patterns C k (physicalGroupResidueVector r) L x).symm ⟨sp, path⟩) =
      if physicalRootPlannedForestCompatible groups e patterns C k (L, sp)
        ((physicalMixedCommonForestEquiv (fun _ : Fin M => J + ell) B ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) L sp).symm code) x path
      then 1 else 0 at hm
    have hr := physical_root_forest_residual_pack groups e patterns C hC k V ζ K θ β ρ
      hPs hPb hdis (physicalGroupResidueVector r) L sp x path
    have ht := physical_mixed_planned_big_terminal
      (fun g (p : P (e.symm g).val) => p.val)
      (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) B
      (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
      (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
      (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
      (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) (physicalGroupResidueVector r) L sp x path
    change _ = _ at hr
    erw [hm, hr, ht]
    dsimp only [physicalMixedPlannedBigTerminal]
    split_ifs <;> simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, zero_mul]
    ring

theorem physical_root_mixed_forest_norm_le_history_integral
    (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (hcode : ∀ i, fullMixedCommonIndexStage (fun _ : Fin M => J + ell) B
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) i = 0 → code i = none)
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (L : PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B) :
    ‖physicalRootMixedForestAction groups e patterns C hC k V q ζ K r θ β retention ρ code f L x‖ ≤
    physicalRootHistoryIntegral groups e patterns C k V q β retention ρ code
      ((physicalGroupResidueVector r, L), x)
      (fullMixedCommonHistorySeed (fun g (p : P (e.symm g).val) => p.val) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) x (fun _ => none))
      (fun p => ‖physicalRootForestResidual groups e patterns C hC k V ζ K θ β ρ hPs hPb hdis
          ((physicalGroupResidueVector r, L), x) p‖ *
        ‖f (finiteEventPathTerminal (PhysicalRootMixedEvent groups e patterns C k)
          (physicalRootMixedTarget groups e patterns C k) ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) ((physicalGroupResidueVector r, L), x) p).2‖) := by
  rw [physical_root_mixed_forest_eq_history_action groups e patterns C hC k V q ζ K r θ β retention ρ
    hPs hPb hdis code hcode]
  exact @finite_event_path_action_mask_norm_le _ _ (PhysicalRootMixedEvent groups e patterns C k)
    (physicalMixedWordEventFintype (fun g (p : P (e.symm g).val) => p.val)
      (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) B
      (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
      (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
      (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val)))
    (physicalRootMixedTarget groups e patterns C k)
    (physicalRootForestOriginalWeight groups e patterns C k V q β retention ρ)
    ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
    (physicalRootForestHistoryFactor groups e patterns C k code)
    (physicalRootForestResidual groups e patterns C hC k V ζ K θ β ρ hPs hPb hdis)
    (fun s => f s.2) ((physicalGroupResidueVector r, L), x)
    (physical_root_forest_history_nonneg groups e patterns C k code hcode ((physicalGroupResidueVector r, L), x))

end Root
end Bounty

end


-- Source module: PhysicalRootCoefficientBound
section

/- Unit bounds for the original root coefficient. The local Fourier factors
have modulus one; no small-group weight is included in, or removed from, this
coefficient. The active-endpoint gates and birth-ledger gates are retained. -/

open scoped Classical
namespace Bounty

theorem physical_full_key_coefficient_phase_norm_le
    {I T : Type} {N J ell B : ℕ} {P : Fin N → Finset ℕ}
    (C : I → Fin N → Finset (Fin J)) (k : I → ℤ) (ζ : I → ℝ)
    (coeff : ∀ i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
      PhysicalAuxLabels P (C i) → ℂ)
    (hcoeff : ∀ i L R a, ‖coeff i L R a‖ ≤ 1)
    (tag : Option (T ⊕ I)) (x : PhysicalFullBoundedState P J ell B)
    (ev : PhysicalFullLedgerEvent C k tag (fullActiveInitialLedger x, x)) :
    ‖physicalFullKeyCoefficientPhase C k ζ coeff tag x ev‖ ≤ 1 := by
  cases tag with
  | none => exact le_of_eq norm_one
  | some tag =>
    cases tag with
    | inl t => exact le_of_eq norm_one
    | inr i =>
      exact physical_active_coefficient_norm_le _ _ _ _ _ (hcoeff i) _ _ _

theorem physical_full_combined_edge_phase_norm_le
    {I : Type} {N J ell B : ℕ} {P : Fin N → Finset ℕ}
    (C : I → Fin N → Finset (Fin J)) (k : I → ℤ)
    (ω : ∀ i, SharedActiveLabels (fun g => ↥(P g))
      (fun g => physicalFullSharedIndices (ell := ell) (C i g)) →
      PhysicalAuxLabels P (C i) → ℝ)
    (β : (g : Fin N) → P g → ℝ) (ρ : ℝ) (V : Fin N → ℝ) (ζ : I → ℝ)
    (coeff : ∀ i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
      PhysicalAuxLabels P (C i) → ℂ)
    (hcoeff : ∀ i L R a, ‖coeff i L R a‖ ≤ 1)
    (i : I) (H : (g : Fin N) → Finset (P g))
    (x : PhysicalFullBoundedState P J ell B) (ev : PhysicalFullEdgeEvent (C i) (k i) x) :
    ‖physicalFullCombinedEdgePhase C k ω β ρ V ζ coeff i H x ev‖ ≤ 1 := by
  rw [physicalFullCombinedEdgePhase, norm_mul]
  exact mul_le_one₀ (physical_full_global_edge_phase_norm_le _ _ _ _ _ _ _ _ _)
    (norm_nonneg _) (physical_active_coefficient_norm_le _ _ _ _ _ (hcoeff i) _ _ _)

theorem physical_root_key_coefficient_norm_le
    {I : Type} {N M J ell n : ℕ} {P : Fin N → Finset ℕ}
    (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
    (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
    (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
    (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ)
    (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
      PhysicalAuxLabels P (C i) → ℂ) (θ : ℝ)
    (hK : ∀ time < n + 1, ∀ i ∈ patterns, ∀ L R a, ‖K time i L R a‖ ≤ 1)
    (key : PhysicalMixedBigKey (Ps := fun g : ↥groupsᶜ => P g.val)
      (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)))
    (L R : PhysicalMarkLists (fun g => P (e.symm g).val) J ell)
    (a : PhysicalAuxLabels (fun g => P (e.symm g).val)
      (fun g => C key.2.1.val (e.symm g).val)) :
    ‖physicalRootKeyCoefficient groups e patterns C hC ζ k K θ key L R a‖ ≤ 1 := by
  simp only [physicalRootKeyCoefficient, physicalGroupReindexedCoefficient,
    physicalCoupledBigCoefficient, physicalLocalFourierCoefficient,
    norm_mul, physical_phase_norm, physicalReturnPhase_norm, mul_one]
  exact hK _ (Nat.lt_succ_of_le (Nat.sub_le _ _)) _ key.2.1.property _ _ _

end Bounty

end


-- Source module: PhysicalRootCoefficientEnvelope
section

/- General coefficient envelopes preserve the original phases and gates. -/

open scoped Classical
namespace Bounty

theorem physical_active_coefficient_norm_le_envelope
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

theorem physical_full_combined_edge_phase_norm_le_envelope
    {I : Type} {N J ell B : ℕ} {P : Fin N → Finset ℕ}
    (C : I → Fin N → Finset (Fin J)) (k : I → ℤ)
    (ω : ∀ i, SharedActiveLabels (fun g => ↥(P g))
      (fun g => physicalFullSharedIndices (ell := ell) (C i g)) →
      PhysicalAuxLabels P (C i) → ℝ)
    (β : (g : Fin N) → P g → ℝ) (ρ : ℝ) (V : Fin N → ℝ) (ζ : I → ℝ)
    (coeff : ∀ i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
      PhysicalAuxLabels P (C i) → ℂ)
    (H : ℝ) (hH : 0 ≤ H) (hcoeff : ∀ i L R a, ‖coeff i L R a‖ ≤ H)
    (i : I) (ledger : (g : Fin N) → Finset (P g))
    (x : PhysicalFullBoundedState P J ell B) (ev : PhysicalFullEdgeEvent (C i) (k i) x) :
    ‖physicalFullCombinedEdgePhase C k ω β ρ V ζ coeff i ledger x ev‖ ≤ H := by
  rw [physicalFullCombinedEdgePhase, norm_mul]
  simpa only [one_mul] using
    mul_le_mul (physical_full_global_edge_phase_norm_le _ _ _ _ _ _ _ _ _)
      (physical_active_coefficient_norm_le_envelope _ _ _ _ _ H hH (hcoeff i) _ _ _)
      (norm_nonneg _) (show (0 : ℝ) ≤ 1 by norm_num)

theorem physical_root_key_coefficient_norm_le_envelope
    {I : Type} {N M J ell n : ℕ} {P : Fin N → Finset ℕ}
    (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
    (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
    (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
    (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ)
    (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
      PhysicalAuxLabels P (C i) → ℂ) (θ : ℝ)
    (H : ℝ)
    (hK : ∀ time < n + 1, ∀ i ∈ patterns, ∀ L R a, ‖K time i L R a‖ ≤ H)
    (key : PhysicalMixedBigKey (Ps := fun g : ↥groupsᶜ => P g.val)
      (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)))
    (L R : PhysicalMarkLists (fun g => P (e.symm g).val) J ell)
    (a : PhysicalAuxLabels (fun g => P (e.symm g).val)
      (fun g => C key.2.1.val (e.symm g).val)) :
    ‖physicalRootKeyCoefficient groups e patterns C hC ζ k K θ key L R a‖ ≤ H := by
  simp only [physicalRootKeyCoefficient, physicalGroupReindexedCoefficient,
    physicalCoupledBigCoefficient, physicalLocalFourierCoefficient,
    norm_mul, physical_phase_norm, physicalReturnPhase_norm, mul_one]
  exact hK _ (Nat.lt_succ_of_le (Nat.sub_le _ _)) _ key.2.1.property _ _ _

end Bounty

end


-- Source module: PhysicalSelectedSmallRowProduct
section

/- The original small-row cost is paid exactly once per selected edge. -/

namespace Bounty

theorem physical_block_small_row_product {V K : Type}
    (A : ℝ) (smallGroups patterns : ℕ) (bs : List (V × K)) (last : V) :
    ((physicalBlockFineSteps bs last).map
      (physicalMixedSmallRowFactor A smallGroups patterns)).prod =
      (A ^ smallGroups * patterns) ^ bs.length := by
  induction bs with
  | nil => simp [physicalBlockFineSteps, physicalMixedSmallRowFactor]
  | cons b bs ih =>
    simpa [physicalBlockFineSteps, physicalMixedSmallRowFactor, pow_succ, mul_comm]
      using congrArg (fun x : ℝ => (A ^ smallGroups * patterns) * x) ih

theorem physical_selected_small_row_product (A : ℝ) (smallGroups patterns n : ℕ) :
    (((List.range (4 * n + 1)).map (physicalSelectedFineTag n)).map
      (physicalMixedSmallRowFactor A smallGroups patterns)).prod =
      (A ^ smallGroups * patterns) ^ n := by
  rw [physical_selected_fine_block_schedule]
  simpa using physical_block_small_row_product A smallGroups patterns
    (List.ofFn (fun j : Fin n => (j.castSucc, j))) (Fin.last n)

end Bounty

end


-- Source module: FullMixedResidualEnvelope
section

/- A local coefficient envelope is charged exactly on the big-edge tags.
Permutation and ghost tags retain their unit contribution. -/

namespace Bounty

theorem finite_event_local_phase_norm_le_product
    {K X : Type} (E : K → X → Type) (target : ∀ k x, E k x → X)
    (phase : ∀ k x, E k x → ℂ) (b : K → ℝ)
    (hb : ∀ k, 0 ≤ b k) (hphase : ∀ k x e, ‖phase k x e‖ ≤ b k)
    (steps : List K) (x : X) (p : FiniteEventPath E target steps x) :
    ‖finiteEventLocalPhase E target phase steps x p‖ ≤ (steps.map b).prod := by
  induction steps generalizing x with
  | nil => simp only [finiteEventLocalPhase, norm_one, List.map_nil, List.prod_nil, le_refl]
  | cons k ks ih =>
    rcases p with ⟨e, p⟩
    simp only [finiteEventLocalPhase, norm_mul, List.map_cons, List.prod_cons]
    exact mul_le_mul (hphase k x e) (ih _ p) (norm_nonneg _) (hb k)

section Residual
variable {J K : Type} {N : ℕ} {P : Fin N → Type}
  (n : (g : Fin N) → P g → ℕ) {M : Fin N → ℕ}
  (S : K → (g : Fin N) → Finset (Fin (M g))) (B : ℕ)
  (A : ∀ k, SharedActiveLabels P (S k) → Type)
  (Δ D : ∀ k c, A k c → Fin N → ℤ)
  (edgePhase : ∀ k, ((g : Fin N) → Finset (P g)) →
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) →
    FullActiveEdgeEvent n (S k) B (A k) (Δ k) (D k) x → ℂ)

theorem full_mixed_common_residual_path_norm_le_envelope
    (H : ℝ) (hH : 0 ≤ H)
    (hphase : ∀ k x e, ‖edgePhase k (fun _ => ∅) x e‖ ≤ H)
    (steps : List (Option (J ⊕ K)))
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (p : FullPermutationMixedPath n S B A Δ D steps x) :
    ‖finiteEventLocalPhase (FullPermutationMixedEvent n S B A Δ D)
      (fullPermutationMixedEventTarget n S B A Δ D)
      (fullMixedBirthResidualPhase n S B A Δ D edgePhase) steps x p‖ ≤
      (steps.map (physicalMixedSmallRowFactor H 1 1)).prod := by
  apply finite_event_local_phase_norm_le_product
  · exact physical_mixed_small_row_factor_nonneg hH 1 1
  · intro tag y e
    cases tag with
    | none => exact le_of_eq (norm_one : ‖(1 : ℂ)‖ = 1)
    | some tag =>
      cases tag with
      | inl j => exact le_of_eq (norm_one : ‖(1 : ℂ)‖ = 1)
      | inr k => simpa only [fullMixedBirthResidualPhase, physicalMixedSmallRowFactor, pow_one, Nat.cast_one, mul_one]
          using hphase k y e

end Residual

theorem physical_mixed_planned_envelope_product
    {S I V K : Type} {Ps : S → Finset ℕ} {J ell : ℕ}
    (H : ℝ) (steps : List (Option (V ⊕ K)))
    (L : PhysicalMarkLists Ps J ell)
    (pl : PhysicalMixedSmallPlan (Ps := Ps) (J := J) (ell := ell) (I := I) steps) :
    ((physicalMixedBigSteps steps L pl).map (physicalMixedSmallRowFactor H 1 1)).prod =
      (steps.map (physicalMixedSmallRowFactor H 1 1)).prod := by
  have h := congrArg (fun ks : List (Option (V ⊕ K)) =>
      (ks.map (physicalMixedSmallRowFactor H 1 1)).prod)
    (physical_mixed_big_steps_tags steps L pl)
  rw [List.map_map] at h
  convert h using 2
  apply List.map_congr_left
  intro tag _
  cases tag with
  | none => rfl
  | some tag => cases tag <;> rfl

end Bounty

end


-- Source module: PhysicalRootForestResidualEnvelope
section

/- An envelope H is paid exactly n+1 times in the original root residual.
All small-group factors remain in the original mixed path weight. -/

open scoped Classical
namespace Bounty
section Root
variable {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
  (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
  (k : ℕ → I → ℤ) (V : Fin N → ℝ) (ζ : ℕ → I → ℝ)
  (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
    PhysicalAuxLabels P (C i) → ℂ)
  (θ : ℝ) (β : (g : Fin M) → P (e.symm g).val → ℝ) (ρ : ℝ)
  (H : ℝ) (hH : 0 ≤ H)
  (hK : ∀ time < n + 1, ∀ i ∈ patterns, ∀ L R a, ‖K time i L R a‖ ≤ H)

include hH hK in
theorem physical_root_effective_forest_residual_norm_le_envelope :
    ∀ pl x path,
      ‖physicalRootEffectiveForestResidual (n := n) (B := B)
        groups e patterns C hC k pl V ζ K θ β ρ x path‖ ≤ H ^ (n + 1) := by
  intro pl x path
  let Cb := fun key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val)
    (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      fun g => C key.2.1.val (e.symm g).val
  let kb := fun key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val)
    (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      k (n - key.1.val) key.2.1.val * (physicalSharedProduct (physicalSharedPrefix key.2.2.1) : ℕ)
  let steps := physicalMixedBigSteps
    ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) pl.1 pl.2
  let sizes := fun g (p : P (e.symm g).val) => p.val
  let shared := fun key g => physicalFullSharedIndices (ell := ell) (Cb key g)
  let aux := fun key (_ : SharedActiveLabels (fun g => ↥(P (e.symm g).val)) (shared key)) =>
    PhysicalAuxLabels (fun g => P (e.symm g).val) (Cb key)
  let delta := fun key => physicalFullEdgeDelta (P := fun g => P (e.symm g).val) (ell := ell) (Cb key) (kb key)
  let displacement := fun key => physicalFullEdgeD (P := fun g => P (e.symm g).val) (ell := ell) (Cb key)
  let omega := fun key (_ : SharedActiveLabels (fun g => ↥(P (e.symm g).val)) (shared key)) (a : PhysicalAuxLabels (fun g => P (e.symm g).val) (Cb key)) =>
    physicalAuxMass (fun g => V (e.symm g).val) (Cb key) a
  have hphase : ∀ key y ev,
      ‖physicalFullCombinedEdgePhase (B := B) Cb kb omega β ρ (fun g => V (e.symm g).val) (fun _ => 0)
        (physicalRootKeyCoefficient groups e patterns C hC ζ k K θ) key (fun _ => ∅) y ev‖ ≤ H := by
    intro key y ev
    exact physical_full_combined_edge_phase_norm_le_envelope Cb kb omega β ρ
      (fun g => V (e.symm g).val) (fun _ => 0)
      (physicalRootKeyCoefficient groups e patterns C hC ζ k K θ) H hH
      (physical_root_key_coefficient_norm_le_envelope groups e patterns C hC ζ k K θ H hK)
      key (fun _ => ∅) y ev
  have h := full_mixed_common_residual_path_norm_le_envelope sizes shared B aux delta displacement
    (physicalFullCombinedEdgePhase (B := B) Cb kb omega β ρ (fun g => V (e.symm g).val) (fun _ => 0)
      (physicalRootKeyCoefficient groups e patterns C hC ζ k K θ)) H hH hphase steps x path
  have hp : (steps.map (physicalMixedSmallRowFactor H 1 1)).prod = H ^ (n + 1) := by
    dsimp only [steps]
    rw [physical_mixed_planned_envelope_product, physical_selected_small_row_product]
    simp only [pow_one, Nat.cast_one, mul_one]
  exact h.trans_eq hp

variable
  (hPs : ∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p)
  (hPb : ∀ (g : Fin M) p, p ∈ P (e.symm g).val → Nat.Prime p)
  (hdis : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (e.symm g).val))

include hH hK in
theorem physical_root_forest_residual_norm_le_envelope :
    ∀ s path,
      ‖physicalRootForestResidual (n := n) (B := B)
        groups e patterns C hC k V ζ K θ β ρ hPs hPb hdis s path‖ ≤ H ^ (n + 1) := by
  intro s path
  unfold physicalRootForestResidual
  exact physical_root_effective_forest_residual_norm_le_envelope
    groups e patterns C hC k V ζ K θ β ρ H hH hK _ _ _

end Root
end Bounty

end


-- Source module: PhysicalRootForestEnvelopeRankBound
section

/- Full rank decay for the original root action with a uniform coefficient
envelope H. Its cost is paid once per actual edge. -/

open Finset
open scoped Classical
namespace Bounty

theorem exists_physical_root_forest_envelope_rank_bound {qmax vs : ℝ}
    (hqmax0 : 0 ≤ qmax) (hqmax1 : qmax < 1) (hvs : 0 < vs) (ell : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧
    ∀ (I : Type) (N M J n B : ℕ) (P : Fin N → Finset ℕ)
      (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
      [∀ z : PhysicalPrime P, NeZero z.2.val]
      [∀ g (p : P (e.symm g).val), NeZero p.val]
      (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
      (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅) (k : ℕ → I → ℤ)
      (V : Fin N → ℝ) (q : ℝ) (β : (g : Fin M) → P (e.symm g).val → ℝ)
      (retention : Fin (n + 2) → ℝ) (ρ : ℝ),
      (∀ s : ↥groupsᶜ, vs ≤ V s.val) → Real.sqrt q ≤ qmax →
      ∀ (_i0 : patterns) (v vmin : ℝ) (η : Fin M → ℝ) (τ : ℝ) (T : ℕ),
      (∀ g, ∑ p ∈ P (e.symm g).val, 1 / (p : ℝ) = V (e.symm g).val) →
      (∀ g p, 0 ≤ β g p / V (e.symm g).val) →
      (∀ g, ∑ p, β g p / V (e.symm g).val ≤ 2) →
      (∀ g, 0 ≤ η g) → (∀ g p, β g p / V (e.symm g).val ≤ η g) →
      (∀ j g, (|(1 - retention j) * V (e.symm g).val / ρ| * η g) * v ≤ τ) →
      (∀ g, η g ≤ τ) → (∀ j, 0 ≤ retention j) → (∀ j, retention j ≤ 1) →
      0 < ρ → ρ < 1 → 1 < v → 0 < vmin →
      (∀ g, vmin ≤ V (e.symm g).val) →
      (∀ j, retention j / ρ ^ 2 + ((1 - retention j) / ρ) / v ≤ 1) →
      (∀ (i : patterns) g, (physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val))ᶜ.card ≤ T) →
      0 ≤ τ →
      ∀ (H : ℝ), 1 ≤ H → ∀ (ζ : ℕ → I → ℝ)
      (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
        PhysicalAuxLabels P (C i) → ℂ) (θ : ℝ),
      (∀ time < n + 1, ∀ i ∈ patterns, ∀ L R a, ‖K time i L R a‖ ≤ H) →
      (∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p) →
      (∀ (g : Fin M) p, p ∈ P (e.symm g).val → Nat.Prime p) →
      (∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (e.symm g).val)) →
      ∀ (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B)),
      (∀ i, fullMixedCommonIndexStage (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) i = 0 → code i = none) →
      ∀ (r : PhysicalGroupResidues P groupsᶜ)
      (L : PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell)
      (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B)
      (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ),
      (∀ y, ‖f y‖ ≤ 1) →
      ‖physicalRootMixedForestAction groups e patterns C hC k V q ζ K r θ β retention ρ code f L x‖ ≤
        τ ^ birthForestRank code *
          (((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))).map
            (physicalMixedSmallRowFactor A groupsᶜ.card patterns.card)).prod *
          (((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))).map
            (fullMixedLengthRowFactor (fun g p => β g p / V (e.symm g).val)
              retention ρ v vmin (fun g => V (e.symm g).val) T)).prod *
          (H ^ (n + 1) * productLengthLyapunov v x) := by
  obtain ⟨A, hA, hbound⟩ := exists_physical_root_scaled_history_integral_bound hqmax0 hqmax1 hvs ell
  refine ⟨A, hA, ?_⟩
  intro I N M J n B P groups e _ _ patterns C hC k V q β retention ρ hVs hq i0 v vmin η τ T
    hMass hμ hmass hη hμatom hghost hedge hq0 hq1 hρ0 hρ1 hv hvmin hV hD ht hτ
    H hH ζ K θ hK hPs hPb hdis code hcode r L x f hf
  apply (physical_root_mixed_forest_norm_le_history_integral groups e patterns C hC k V q ζ K
    r θ β retention ρ hPs hPb hdis code hcode f L x).trans
  apply hbound I N M J n B P groups e patterns C k V q β retention ρ hVs hq
    i0 v vmin η τ T hMass hμ hmass hη hμatom hghost hedge hq0 hq1 hρ0 hρ1 hv hvmin hV hD ht hτ
    code hcode
  · exact pow_nonneg (zero_le_one.trans hH) _
  · intro path
    simpa only [mul_one] using mul_le_mul
      (physical_root_forest_residual_norm_le_envelope groups e patterns C hC k V ζ K θ β ρ
        H (zero_le_one.trans hH) hK hPs hPb hdis _ path)
      (hf _) (norm_nonneg _) (pow_nonneg (zero_le_one.trans hH) (n + 1))

end Bounty

end


-- Source module: PhysicalRootForestInitialZero
section

/- An initial child link cannot occur in a compatible forest when the
original initial active labels are injective. -/

open scoped Classical
namespace Bounty

section Root
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

theorem physical_root_mixed_forest_eq_zero_of_initial_child
    (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (hbad : ¬ ∀ i, fullMixedCommonIndexStage (fun _ : Fin M => J + ell) B
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) i = 0 →
      code i = none)
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (L : PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B)
    (hx : FullActiveInjective x) :
    physicalRootMixedForestAction groups e patterns C hC k V q ζ K r θ β retention ρ
      code f L x = 0 := by
  unfold physicalRootMixedForestAction
  apply Finset.sum_eq_zero
  intro sp _
  unfold physicalRootCommonForestAction physicalRootEffectiveForestAction birthForestPathSum
  dsimp only
  apply Finset.sum_eq_zero
  intro path _
  apply if_neg
  intro hc
  apply hbad
  apply (physical_mixed_plan_initial_condition_iff (fun _ : Fin M => J + ell) B
    ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) L sp code).mp
  exact full_mixed_common_compatible_initial_child_none
    (fun g (p : P (e.symm g).val) => p.val) _ B _ _ _ _ x path hx _ hc

end Root
end Bounty

end


-- Source module: PhysicalRootHistoryBoundary
section

/- The original empty-memory boundary contributes no length factor. -/

open Finset
open scoped Classical
namespace Bounty

theorem full_memory_vacuum_norm_le_one {G : Type*} {P Z : G → Type*}
    {M : G → ℕ} {B : ℕ} (s : ProductBoundedOrderedState P Z M B) :
    ‖fullMemoryVacuum s‖ ≤ 1 := by
  unfold fullMemoryVacuum
  split <;> simp

theorem physical_full_empty_length_lyapunov {G : Type*} [Fintype G]
    {P : G → Finset ℕ} {Z : G → Type*} {J ell B : ℕ}
    (C : G → Finset (Fin J)) (L : PhysicalMarkLists P J ell) (v : ℝ) :
    productLengthLyapunov v
      (physicalFullMemoryState C L (fun g => fullEmptyBoundedMemory (Z g) B)) = 1 := by
  apply productLengthLyapunov_empty
  simp only [physical_full_memory_state_total, fullEmptyBoundedMemory, sum_const_zero]

end Bounty

end


-- Source module: PhysicalRootEmptyForestEnvelope
section

/- Every original root forest at empty memory with a coefficient envelope.
The restored H^(n+1) cost does not alter the full rank decay. -/

open Finset
open scoped Classical
namespace Bounty

theorem exists_physical_root_empty_forest_envelope_rank_bound {qmax vs : ℝ}
    (hqmax0 : 0 ≤ qmax) (hqmax1 : qmax < 1) (hvs : 0 < vs) (ell : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧
    ∀ (I : Type) (N M J n B : ℕ) (P : Fin N → Finset ℕ)
      (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
      [∀ z : PhysicalPrime P, NeZero z.2.val]
      (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
      (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅) (k : ℕ → I → ℤ)
      (V : Fin N → ℝ) (q : ℝ) (β : (g : Fin M) → P (e.symm g).val → ℝ)
      (retention : Fin (n + 2) → ℝ) (ρ : ℝ),
      (∀ s : ↥groupsᶜ, vs ≤ V s.val) → Real.sqrt q ≤ qmax →
      ∀ (_i0 : patterns) (v vmin : ℝ) (η : Fin M → ℝ) (τ : ℝ) (T : ℕ),
      (∀ g, ∑ p ∈ P (e.symm g).val, 1 / (p : ℝ) = V (e.symm g).val) →
      (∀ g p, 0 ≤ β g p / V (e.symm g).val) →
      (∀ g, ∑ p, β g p / V (e.symm g).val ≤ 2) →
      (∀ g, 0 ≤ η g) → (∀ g p, β g p / V (e.symm g).val ≤ η g) →
      (∀ j g, (|(1 - retention j) * V (e.symm g).val / ρ| * η g) * v ≤ τ) →
      (∀ g, η g ≤ τ) → (∀ j, 0 ≤ retention j) → (∀ j, retention j ≤ 1) →
      0 < ρ → ρ < 1 → 1 < v → 0 < vmin →
      (∀ g, vmin ≤ V (e.symm g).val) →
      (∀ j, retention j / ρ ^ 2 + ((1 - retention j) / ρ) / v ≤ 1) →
      (∀ (i : patterns) g, (physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val))ᶜ.card ≤ T) →
      0 ≤ τ →
      ∀ (H : ℝ), 1 ≤ H → ∀ (ζ : ℕ → I → ℝ)
      (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
        PhysicalAuxLabels P (C i) → ℂ) (θ : ℝ),
      (∀ time < n + 1, ∀ i ∈ patterns, ∀ L R a, ‖K time i L R a‖ ≤ H) →
      (∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p) →
      (∀ (g : Fin M) p, p ∈ P (e.symm g).val → Nat.Prime p) →
      (∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (e.symm g).val)) →
      ∀ (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B)),
      ∀ (r : PhysicalGroupResidues P groupsᶜ)
      (L : PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell)
      (Lb : PhysicalMarkLists (fun g => P (e.symm g).val) J ell),
      ‖physicalRootMixedForestAction groups e patterns C hC k V q ζ K r θ β retention ρ code
        fullMemoryVacuum L (physicalFullMemoryState (fun _ : Fin M => ∅) Lb
          (fun g => fullEmptyBoundedMemory
            (UnrestrictedResidueParticle (fun p : P (e.symm g).val => p.val)) B))‖ ≤
        τ ^ birthForestRank code *
          (A ^ groupsᶜ.card * (patterns.card : ℝ)) ^ (n + 1) *
          (((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))).map
            (fullMixedLengthRowFactor (fun g p => β g p / V (e.symm g).val)
              retention ρ v vmin (fun g => V (e.symm g).val) T)).prod * H ^ (n + 1) := by
  obtain ⟨A, hA, hbound⟩ := exists_physical_root_forest_envelope_rank_bound hqmax0 hqmax1 hvs ell
  refine ⟨A, hA, ?_⟩
  intro I N M J n B P groups e _ patterns C hC k V q β retention ρ hVs hq i0 v vmin η τ T
    hMass hμ hmass hη hμatom hghost hedge hq0 hq1 hρ0 hρ1 hv hvmin hV hD ht hτ
    H hH ζ K θ hK hPs hPb hdis code r L Lb
  by_cases hcode : ∀ i, fullMixedCommonIndexStage (fun _ : Fin M => J + ell) B
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) i = 0 → code i = none
  · have h := @hbound I N M J n B P groups e inferInstance
      (fun g p => inferInstanceAs (NeZero (⟨(e.symm g).val, p⟩ : PhysicalPrime P).2.val))
      patterns C hC k V q β retention ρ hVs hq
      i0 v vmin η τ T hMass hμ hmass hη hμatom hghost hedge hq0 hq1 hρ0 hρ1 hv hvmin hV hD ht hτ
      H hH ζ K θ hK hPs hPb hdis code hcode r L
      (physicalFullMemoryState (fun _ : Fin M => ∅) Lb
        (fun g => fullEmptyBoundedMemory
          (UnrestrictedResidueParticle (fun p : P (e.symm g).val => p.val)) B))
      fullMemoryVacuum full_memory_vacuum_norm_le_one
    simpa only [physical_full_empty_length_lyapunov, mul_one,
      physical_selected_small_row_product] using h
  · rw [physical_root_mixed_forest_eq_zero_of_initial_child groups e patterns C hC k V q ζ K
      r θ β retention ρ code hcode fullMemoryVacuum L _
        (physical_full_state_injective _ Lb _), norm_zero]
    apply mul_nonneg
    · apply mul_nonneg
      · exact mul_nonneg (pow_nonneg hτ _)
          (pow_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hA) _) (Nat.cast_nonneg _)) _)
      · apply List.prod_nonneg
        intro a ha
        obtain ⟨tag, _, rfl⟩ := List.mem_map.mp ha
        exact fullMixedLengthRowFactor_nonneg _ _ _ _ _ _ _ hρ1 (zero_lt_one.trans hv).le tag
    · exact pow_nonneg (zero_le_one.trans hH) _

end Bounty

end


-- Source module: PhysicalSmallBigBoundedReadout
section

/- A bound at the actual initial injective marks passes directly to the
normalized scalar. This also covers pointwise high-rank forest estimates. -/

open Finset
open scoped Classical
namespace Bounty
section Readout
variable {S G : Type*} [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
  {Ps : S → Finset ℕ} [∀ p : PhysicalPrime Ps, NeZero p.2.val]
  {P : G → Finset ℕ} {Z : G → Type*} {J ell B : ℕ}
  (Vs : S → ℝ) (C : G → Finset (Fin J))
  (μ : ∀ g, P g → ℝ)
  (empty : ∀ g, BoundedOrderedTuple (Z g) B)
  (boundary : PhysicalBareResidueState Ps J ell →
    ProductBoundedOrderedState (fun g => ↥(P g)) Z (fun _ => J + ell) B → ℂ)
  (F : PhysicalSmallBigState Ps J ell
    (ProductBoundedOrderedState (fun g => ↥(P g)) Z (fun _ => J + ell) B) → ℂ)

theorem physical_small_big_initial_readout_of_pointwise_bound
    (hVs : ∀ s, 0 < Vs s) (hMass : ∀ s, ∑ p ∈ Ps s, 1 / (p : ℝ) = Vs s)
    (hμ : ∀ g p, 0 ≤ μ g p)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hF : ∀ s L, ‖boundary s (physicalFullMemoryState C L empty) *
      F (s, physicalFullMemoryState C L empty)‖ ≤ bound) :
    ‖physicalSmallBigInitialReadout Vs C μ empty boundary F‖ ≤
      bound * ∏ g, (∑ p, μ g p) ^ (J + ell) := by
  let mass := ∏ g, (∑ p, μ g p) ^ (J + ell)
  have hm : 0 ≤ mass := prod_nonneg fun g _ => pow_nonneg (sum_nonneg fun p _ => hμ g p) _
  have hb (s : PhysicalBareResidueState Ps J ell) :
      ‖∑ L : PhysicalMarkLists P J ell,
        ((∏ g, ∏ i : PhysicalSlots J ell, μ g (L g i) : ℝ) : ℂ) *
          (boundary s (physicalFullMemoryState C L empty) *
            F (s, physicalFullMemoryState C L empty))‖ ≤ bound * mass := by
    calc
      _ ≤ ∑ L : PhysicalMarkLists P J ell,
          (∏ g, ∏ i : PhysicalSlots J ell, μ g (L g i)) * bound := by
        apply (norm_sum_le _ _).trans
        apply sum_le_sum
        intro L _
        have hw : 0 ≤ ∏ g, ∏ i : PhysicalSlots J ell, μ g (L g i) :=
          prod_nonneg fun g _ => prod_nonneg fun i _ => hμ g (L g i)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
        exact mul_le_mul_of_nonneg_left (hF s L) hw
      _ = bound * physicalMarkMass (J := J) (ell := ell) μ := by
        rw [← sum_mul]
        exact mul_comm _ _
      _ ≤ bound * mass := mul_le_mul_of_nonneg_left (physical_mark_mass_le μ hμ) hbound
  unfold physicalSmallBigInitialReadout
  calc
    _ ≤ ∑ s : PhysicalBareResidueState Ps J ell,
        physicalResidueInitialMass Vs s * (bound * mass) := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro s _
      have hs := physical_residue_initial_mass_nonneg Vs hVs s
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
      exact mul_le_mul_of_nonneg_left (hb s) hs
    _ = (∑ s : PhysicalBareResidueState Ps J ell, physicalResidueInitialMass Vs s) *
        (bound * mass) := (sum_mul _ _ _).symm
    _ ≤ 1 * (bound * mass) := mul_le_mul_of_nonneg_right
      (physical_residue_initial_mass_total Vs hVs hMass) (mul_nonneg hbound hm)
    _ = bound * mass := one_mul _

end Readout
end Bounty

end


-- Source module: PhysicalRootBoundedInitial
section

/- The original weighted scalar, including the full small-residue average,
is a normalized initial readout whenever the integrand has its true support. -/

open Finset
open scoped Classical
namespace Bounty
section Scalar
variable {N M J ell B : ℕ} {P : Fin N → Finset ℕ}
  [∀ z : PhysicalPrime P, NeZero z.2.val]
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  (V : Fin N → ℝ) (β : (g : Fin M) → P (e.symm g).val → ℝ)

variable [∀ z : PhysicalPrime (fun s : ↥groupsᶜ => P s.val), NeZero z.2.val]

theorem physical_root_initial_scalar_of_pointwise_bound
    (hVs : ∀ s : ↥groupsᶜ, 0 < V s.val)
    (hMass : ∀ s : ↥groupsᶜ, ∑ p ∈ P s.val, 1 / (p : ℝ) = V s.val)
    (hμ : ∀ g p, 0 ≤ β g p / V (e.symm g).val)
    (boundary : PhysicalBareResidueState (fun s : ↥groupsᶜ => P s.val) J ell →
      PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (F : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e → ℂ)
    (hF : ∀ r L x, ¬ physicalResidueMarksValid r L → F ((r, L), x) = 0)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hpoint : ∀ s L,
      ‖boundary s (physicalFullMemoryState (fun _ : Fin M => ∅) L
        (fun g => fullEmptyBoundedMemory
          (UnrestrictedResidueParticle (fun z : P (e.symm g).val => z.val)) B)) *
        F (s, physicalFullMemoryState (fun _ : Fin M => ∅) L
          (fun g => fullEmptyBoundedMemory
            (UnrestrictedResidueParticle (fun z : P (e.symm g).val => z.val)) B))‖ ≤ bound) :
    ‖physicalRootInitialScalar groups e V β
      (fun r L x => boundary (physicalGroupResidueVector r, L) x *
        F ((physicalGroupResidueVector r, L), x))‖ ≤
      bound * ∏ g, (∑ p, β g p / V (e.symm g).val) ^ (J + ell) := by
  rw [physical_root_initial_scalar_eq_readout groups e V β boundary F hF]
  exact physical_small_big_initial_readout_of_pointwise_bound
    (fun s : ↥groupsᶜ => V s.val) (fun _ : Fin M => ∅)
    (fun g p => β g p / V (e.symm g).val) _ boundary F hVs hMass hμ hbound hpoint

end Scalar
end Bounty

end


-- Source module: PhysicalRootForestPointwise
section

/- The actual local root Fourier word is the exact sum over its original
planned big actions, with every small factor and coefficient retained. -/

open Finset MeasureTheory
open scoped Classical
namespace Bounty
section Root
variable {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
  [∀ z : PhysicalPrime P, NeZero z.2.val]
  (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
  (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
  (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
  (k : ℕ → I → ℤ)

  (V : Fin N → ℝ) (q : ℝ) (ζ : ℕ → I → ℝ)
  (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
    PhysicalAuxLabels P (C i) → ℂ)
  (θ : ℝ)
  (β : (g : Fin M) → P (e.symm g).val → ℝ)
  (retention : Fin (n + 2) → ℝ) (ρ : ℝ)

  (hPs : ∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p)
  (hPb : ∀ (g : Fin M) p, p ∈ P (e.symm g).val → Nat.Prime p)
  (hdis : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (e.symm g).val))


variable (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ)
    (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) → ℝ)

variable [∀ z : PhysicalPrime (fun s : ↥groupsᶜ => P s.val), NeZero z.2.val]

include hPs hPb hdis in
theorem physical_root_forest_contribution_of_pointwise_bound
    (hinj : Function.Injective encode)
    (hVs : ∀ s : ↥groupsᶜ, 0 < V s.val)
    (hMass : ∀ s : ↥groupsᶜ, ∑ p ∈ P s.val, 1 / (p : ℝ) = V s.val)
    (hμ : ∀ g p, 0 ≤ β g p / V (e.symm g).val)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hpoint : ∀ r Ls Lb,
      ‖physicalRootMixedForestAction groups e patterns C hC k V q ζ K r θ β retention ρ
        code fullMemoryVacuum Ls (physicalFullMemoryState (fun _ : Fin M => ∅) Lb
          (fun g => fullEmptyBoundedMemory
            (UnrestrictedResidueParticle (fun z : P (e.symm g).val => z.val)) B))‖ ≤ bound) :
    ‖physicalRootForestContribution groups e patterns C hC k V q ζ K θ β retention ρ code‖ ≤
      bound * ∏ g, (∑ p, β g p / V (e.symm g).val) ^ (J + ell) := by
  let F : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e → ℂ :=
    fun s => physicalRootMixedForestAction groups e patterns C hC k V q ζ K
      ((physicalGroupResidueVectorEquiv P groupsᶜ).symm s.1.1) θ β retention ρ
      code fullMemoryVacuum s.1.2 s.2
  have hF : ∀ r L x, ¬ physicalResidueMarksValid r L → F ((r, L), x) = 0 := by
    intro r L x hr
    have hv : physicalGroupResidueVector ((physicalGroupResidueVectorEquiv P groupsᶜ).symm r) = r :=
      (physicalGroupResidueVectorEquiv P groupsᶜ).apply_symm_apply r
    exact physical_root_mixed_forest_invalid groups e patterns C hC k V q ζ K θ β retention ρ
      hPs hPb hdis code encode hinj fullMemoryVacuum
      ((physicalGroupResidueVectorEquiv P groupsᶜ).symm r) L x
      (by simpa only [hv] using hr)
  have h := physical_root_initial_scalar_of_pointwise_bound groups e V β hVs hMass hμ
    (fun _ _ => 1) F hF hbound (fun s L => by
      simpa only [one_mul] using hpoint ((physicalGroupResidueVectorEquiv P groupsᶜ).symm s.1) s.2 L)
  have hr (r : PhysicalGroupResidues P groupsᶜ) :
      (physicalGroupResidueVectorEquiv P groupsᶜ).symm (physicalGroupResidueVector r) = r :=
    (physicalGroupResidueVectorEquiv P groupsᶜ).symm_apply_apply r
  simpa only [physicalRootForestContribution, F, one_mul, hr] using h

end Root
end Bounty

end


-- Source module: PhysicalRootHighRankContribution
section

/- The exact empty-memory high-rank estimate transfers to the original
normalized forest contribution with only its initial big-state mass. -/

open Finset
open scoped Classical
namespace Bounty

theorem exists_physical_root_high_rank_contribution_bound {qmax vs : ℝ}
    (hqmax0 : 0 ≤ qmax) (hqmax1 : qmax < 1) (hvs : 0 < vs) (ell : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧
    ∀ (I : Type) (N M J n B : ℕ) (P : Fin N → Finset ℕ)
      (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
      [∀ z : PhysicalPrime P, NeZero z.2.val]
      (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
      (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅) (k : ℕ → I → ℤ)
      (V : Fin N → ℝ) (q : ℝ) (β : (g : Fin M) → P (e.symm g).val → ℝ)
      (retention : Fin (n + 2) → ℝ) (ρ : ℝ),
      (∀ s : ↥groupsᶜ, vs ≤ V s.val) → Real.sqrt q ≤ qmax →
      ∀ (_i0 : patterns) (v vmin : ℝ) (η : Fin M → ℝ) (τ : ℝ) (T : ℕ),
      (∀ g, ∑ p ∈ P (e.symm g).val, 1 / (p : ℝ) = V (e.symm g).val) →
      (∀ g p, 0 ≤ β g p / V (e.symm g).val) →
      (∀ g, ∑ p, β g p / V (e.symm g).val ≤ 2) →
      (∀ g, 0 ≤ η g) → (∀ g p, β g p / V (e.symm g).val ≤ η g) →
      (∀ j g, (|(1 - retention j) * V (e.symm g).val / ρ| * η g) * v ≤ τ) →
      (∀ g, η g ≤ τ) → (∀ j, 0 ≤ retention j) → (∀ j, retention j ≤ 1) →
      0 < ρ → ρ < 1 → 1 < v → 0 < vmin →
      (∀ g, vmin ≤ V (e.symm g).val) →
      (∀ j, retention j / ρ ^ 2 + ((1 - retention j) / ρ) / v ≤ 1) →
      (∀ (i : patterns) g, (physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val))ᶜ.card ≤ T) →
      0 ≤ τ →
      ∀ (H : ℝ), 1 ≤ H → ∀ (ζ : ℕ → I → ℝ)
      (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
        PhysicalAuxLabels P (C i) → ℂ) (θ : ℝ),
      (∀ time < n + 1, ∀ i ∈ patterns, ∀ L R a, ‖K time i L R a‖ ≤ H) →
      (∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p) →
      (∀ (g : Fin M) p, p ∈ P (e.symm g).val → Nat.Prime p) →
      (∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (e.symm g).val)) →
      (∀ s : ↥groupsᶜ, ∑ p ∈ P s.val, 1 / (p : ℝ) = V s.val) →
      ∀ (encode : ((g : Fin M) × P (e.symm g).val) → ℤ), Function.Injective encode →
      ∀ (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B)),
      ‖physicalRootForestContribution groups e patterns C hC k V q ζ K θ β retention ρ code‖ ≤
        (τ ^ birthForestRank code *
          (A ^ groupsᶜ.card * (patterns.card : ℝ)) ^ (n + 1) *
          (((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))).map
            (fullMixedLengthRowFactor (fun g p => β g p / V (e.symm g).val)
              retention ρ v vmin (fun g => V (e.symm g).val) T)).prod * H ^ (n + 1)) *
          ∏ g, (∑ p, β g p / V (e.symm g).val) ^ (J + ell) := by
  obtain ⟨A, hA, hbound⟩ := exists_physical_root_empty_forest_envelope_rank_bound
    hqmax0 hqmax1 hvs ell
  refine ⟨A, hA, ?_⟩
  intro I N M J n B P groups e _ patterns C hC k V q β retention ρ hVs hq i0 v vmin η τ T
    hMass hμ hmass hη hμatom hghost hedge hq0 hq1 hρ0 hρ1 hv hvmin hV hD ht hτ
    H hH ζ K θ hK hPs hPb hdis hSmallMass encode hinj code
  let : ∀ z : PhysicalPrime (fun s : ↥groupsᶜ => P s.val), NeZero z.2.val :=
    fun z => inferInstanceAs (NeZero (⟨z.1.val, z.2⟩ : PhysicalPrime P).2.val)
  have hpoint := @hbound I N M J n B P groups e inferInstance patterns C hC k V q β
    retention ρ hVs hq i0 v vmin η τ T hMass hμ hmass hη hμatom hghost hedge
    hq0 hq1 hρ0 hρ1 hv hvmin hV hD ht hτ H hH ζ K θ hK hPs hPb hdis code
  apply physical_root_forest_contribution_of_pointwise_bound groups e patterns C hC k V q ζ K
    θ β retention ρ hPs hPb hdis code encode hinj
    (fun s => hvs.trans_le (hVs s)) hSmallMass hμ _ hpoint
  apply mul_nonneg
  · apply mul_nonneg
    · exact mul_nonneg (pow_nonneg hτ _)
        (pow_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hA) _) (Nat.cast_nonneg _)) _)
    · apply List.prod_nonneg
      intro a ha
      obtain ⟨tag, _, rfl⟩ := List.mem_map.mp ha
      exact fullMixedLengthRowFactor_nonneg _ _ _ _ _ _ _ hρ1 (zero_lt_one.trans hv).le tag
  · exact pow_nonneg (zero_le_one.trans hH) _

end Bounty

end


-- Source module: RootHighRankRowProduct
section

/- Uniform fixed-base bounds for the exact big-state row product retained
by the original high-rank forest estimate. -/

open Finset
namespace Bounty

theorem full_mixed_length_row_factor_le_uniform
    {J K G : Type*} [Fintype G] {P : G → Type*} [∀ g, Fintype (P g)]
    (μ : ∀ g, P g → ℝ) (q : J → ℝ) (ρ v vmin vmax : ℝ) (V : G → ℝ) (T : ℕ)
    (hmass : ∀ g, ∑ p, μ g p ≤ 2) (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j ≤ 1)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hv : 0 ≤ v)
    (hV0 : ∀ g, 0 ≤ V g) (hVmax : ∀ g, V g ≤ vmax)
    {A : ℝ} (hA : 1 ≤ A) (hghost : Real.exp (2 * vmax * v / ρ) ≤ A)
    (hedge : unrestrictedEdgeRowBound ρ v vmin T ≤ A)
    (tag : Option (J ⊕ K)) :
    fullMixedLengthRowFactor μ q ρ v vmin V T tag ≤ A ^ Fintype.card G := by
  cases tag with
  | none => exact one_le_pow₀ hA
  | some tag =>
    cases tag with
    | inl j =>
      change (∏ g, Real.exp ((|(1 - q j) * V g / ρ| * ∑ p, μ g p) * v)) ≤ _
      calc
        _ ≤ ∏ _g : G, A := by
          apply prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le)
          intro g _
          apply le_trans (Real.exp_le_exp.mpr ?_) hghost
          have hbase0 : 0 ≤ (1 - q j) * V g / ρ :=
            div_nonneg (mul_nonneg (sub_nonneg.mpr (hq1 j)) (hV0 g)) hρ0.le
          have hbase : |(1 - q j) * V g / ρ| ≤ vmax / ρ := by
            rw [abs_of_nonneg hbase0]
            apply div_le_div_of_nonneg_right _ hρ0.le
            calc
              (1 - q j) * V g ≤ 1 * V g :=
                mul_le_mul_of_nonneg_right (by linarith [hq0 j]) (hV0 g)
              _ ≤ vmax := by simpa only [one_mul] using hVmax g
          calc
            _ ≤ (|(1 - q j) * V g / ρ| * 2) * v :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (hmass g) (abs_nonneg _)) hv
            _ ≤ ((vmax / ρ) * 2) * v := by gcongr
            _ = _ := by ring
        _ = A ^ Fintype.card G := by simp
    | inr k =>
      exact pow_le_pow_left₀ (unrestricted_edge_row_bound_nonneg hρ1 hv T) hedge _

theorem full_mixed_length_row_product_le_uniform
    {J K G : Type*} [Fintype G] {P : G → Type*} [∀ g, Fintype (P g)]
    (μ : ∀ g, P g → ℝ) (q : J → ℝ) (ρ v vmin vmax : ℝ) (V : G → ℝ) (T : ℕ)
    (hmass : ∀ g, ∑ p, μ g p ≤ 2) (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j ≤ 1)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hv : 0 ≤ v)
    (hV0 : ∀ g, 0 ≤ V g) (hVmax : ∀ g, V g ≤ vmax)
    {A : ℝ} (hA : 1 ≤ A) (hghost : Real.exp (2 * vmax * v / ρ) ≤ A)
    (hedge : unrestrictedEdgeRowBound ρ v vmin T ≤ A)
    (steps : List (Option (J ⊕ K))) :
    (steps.map (fullMixedLengthRowFactor μ q ρ v vmin V T)).prod ≤
      (A ^ Fintype.card G) ^ steps.length := by
  induction steps with
  | nil => simp
  | cons tag steps ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    rw [mul_comm ((A ^ Fintype.card G) ^ steps.length)]
    apply mul_le_mul
      (full_mixed_length_row_factor_le_uniform μ q ρ v vmin vmax V T
        hmass hq0 hq1 hρ0 hρ1 hv hV0 hVmax hA hghost hedge tag) ih
    · exact List.prod_nonneg (fun x hx => by
        obtain ⟨tag, _, rfl⟩ := List.mem_map.mp hx
        exact fullMixedLengthRowFactor_nonneg μ q ρ v vmin V T hρ1 hv tag)
    · exact pow_nonneg (zero_le_one.trans hA) _

end Bounty

end


-- Source module: RootHighRankCostPower
section

/- Polynomial budgets for the exact high-rank row product and the
remaining coefficient and initial-mass factors. -/

namespace Bounty

theorem root_high_rank_row_power_le {L C A : ℝ} (M N : ℕ)
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hA : 1 ≤ A)
    (hM : (M : ℝ) ≤ C * Real.log L) :
    (A ^ M) ^ (4 * N + 1) ≤ L ^ ((4 * C * Real.log A) * ((N : ℝ) + 1)) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hb := repeated_big_group_energy_cost_le M hL0 hA0 hM
  rw [max_eq_right hA] at hb
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  calc
    _ ≤ (L ^ (C * Real.log A)) ^ (4 * N + 1) :=
      pow_le_pow_left₀ (pow_nonneg hA0 M) hb _
    _ = L ^ ((C * Real.log A) * (4 * N + 1 : ℕ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le hL
      push_cast
      nlinarith [mul_nonneg hC hlogA]

theorem root_high_rank_total_cost_power_le {L C D E coeff rows mass : ℝ} (N : ℕ)
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hcoeff0 : 0 ≤ coeff) (hrows0 : 0 ≤ rows) (hmass0 : 0 ≤ mass)
    (hcoeff : coeff ≤ L ^ C)
    (hrows : rows ≤ L ^ (D * ((N : ℝ) + 1))) (hmass : mass ≤ L ^ E) :
    (coeff ^ N * rows) * mass ≤ L ^ ((C + D + E) * ((N : ℝ) + 1)) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  calc
    _ ≤ ((L ^ C) ^ N * L ^ (D * ((N : ℝ) + 1))) * L ^ E :=
      mul_le_mul (mul_le_mul (pow_le_pow_left₀ hcoeff0 hcoeff N) hrows hrows0
        (pow_nonneg (Real.rpow_nonneg hL0.le _) N)) hmass hmass0
          (mul_nonneg (pow_nonneg (Real.rpow_nonneg hL0.le _) N) (Real.rpow_nonneg hL0.le _))
    _ = L ^ (C * N + D * ((N : ℝ) + 1) + E) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le,
        ← Real.rpow_add hL0, ← Real.rpow_add hL0]
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le hL
      nlinarith [mul_nonneg hE (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

end Bounty

end


-- Source module: RootHighRankEnvelopePower
section

/- The coefficient envelope, row cost, and initial mass share one
polynomial budget without changing the rank decay. -/

namespace Bounty

theorem root_high_rank_envelope_cost_power_le
    {L C D E coeff envelope rows mass tau : ℝ} (N rank : ℕ)
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hcoeff0 : 0 ≤ coeff) (henvelope0 : 0 ≤ envelope)
    (hrows0 : 0 ≤ rows) (hmass0 : 0 ≤ mass) (htau : 0 ≤ tau)
    (hcoeff : coeff * envelope ≤ L ^ C)
    (hrows : rows ≤ L ^ (D * ((N : ℝ) + 1))) (hmass : mass ≤ L ^ E) :
    (tau ^ rank * coeff ^ N * rows * envelope ^ N) * mass ≤
      L ^ ((C + D + E) * ((N : ℝ) + 1)) * tau ^ rank := by
  calc
    _ = (((coeff * envelope) ^ N * rows) * mass) * tau ^ rank := by
      rw [mul_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (root_high_rank_total_cost_power_le N hL hC hE
        (mul_nonneg hcoeff0 henvelope0) hrows0 hmass0 hcoeff hrows hmass)
      (pow_nonneg htau rank)

end Bounty

end


-- Source module: PhysicalRootHighRankPower
section

/- The original high-rank forest contribution has a polynomial prefactor
and retains the full rank power of the rare-birth bound. -/

open Finset
open scoped Classical
namespace Bounty

theorem exists_physical_root_high_rank_contribution_power_le {qmax vs : ℝ}
    (hqmax0 : 0 ≤ qmax) (hqmax1 : qmax < 1) (hvs : 0 < vs) (ell : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧
    ∀ (I : Type) (N M J n B : ℕ) (P : Fin N → Finset ℕ)
      (groups : Finset (Fin N)) (e : {g // g ∉ groupsᶜ} ≃ Fin M)
      [∀ z : PhysicalPrime P, NeZero z.2.val]
      (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
      (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅) (k : ℕ → I → ℤ)
      (V : Fin N → ℝ) (q : ℝ) (β : (g : Fin M) → P (e.symm g).val → ℝ)
      (retention : Fin (n + 2) → ℝ) (ρ : ℝ),
      (∀ s : ↥groupsᶜ, vs ≤ V s.val) → Real.sqrt q ≤ qmax →
      ∀ (_i0 : patterns) (v vmin : ℝ) (η : Fin M → ℝ) (τ : ℝ) (T : ℕ),
      (∀ g, ∑ p ∈ P (e.symm g).val, 1 / (p : ℝ) = V (e.symm g).val) →
      (∀ g p, 0 ≤ β g p / V (e.symm g).val) →
      (∀ g, ∑ p, β g p / V (e.symm g).val ≤ 2) →
      (∀ g, 0 ≤ η g) → (∀ g p, β g p / V (e.symm g).val ≤ η g) →
      (∀ j g, (|(1 - retention j) * V (e.symm g).val / ρ| * η g) * v ≤ τ) →
      (∀ g, η g ≤ τ) → (∀ j, 0 ≤ retention j) → (∀ j, retention j ≤ 1) →
      0 < ρ → ρ < 1 → 1 < v → 0 < vmin →
      (∀ g, vmin ≤ V (e.symm g).val) →
      (∀ j, retention j / ρ ^ 2 + ((1 - retention j) / ρ) / v ≤ 1) →
      (∀ (i : patterns) g, (physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val))ᶜ.card ≤ T) →
      0 ≤ τ →
      ∀ (H : ℝ), 1 ≤ H → ∀ (ζ : ℕ → I → ℝ)
      (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
        PhysicalAuxLabels P (C i) → ℂ) (θ : ℝ),
      (∀ time < n + 1, ∀ i ∈ patterns, ∀ L R a, ‖K time i L R a‖ ≤ H) →
      (∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p) →
      (∀ (g : Fin M) p, p ∈ P (e.symm g).val → Nat.Prime p) →
      (∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (e.symm g).val)) →
      (∀ s : ↥groupsᶜ, ∑ p ∈ P s.val, 1 / (p : ℝ) = V s.val) →
      ∀ (encode : ((g : Fin M) × P (e.symm g).val) → ℤ), Function.Injective encode →
      ∀ (L Cgroup Ccoeff Ch Arow vmax : ℝ),
      1 ≤ L → 0 ≤ Cgroup → 0 ≤ Ccoeff → 0 ≤ Ch → 1 ≤ Arow →
      Real.exp (2 * vmax * v / ρ) ≤ Arow → unrestrictedEdgeRowBound ρ v vmin T ≤ Arow →
      (∀ g : Fin M, V (e.symm g).val ≤ vmax) → (M : ℝ) ≤ Cgroup * Real.log L →
      (A ^ groupsᶜ.card * (patterns.card : ℝ)) * H ≤ L ^ Ccoeff →
      (∏ g, (∑ p, β g p / V (e.symm g).val) ^ (J + ell)) ≤ L ^ Ch →
      ∀ (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B)),
      ‖physicalRootForestContribution groups e patterns C hC k V q ζ K θ β retention ρ code‖ ≤
        L ^ ((Ccoeff + 4 * Cgroup * Real.log Arow + Ch) * (((n + 1 : ℕ) : ℝ) + 1)) *
          τ ^ birthForestRank code := by
  obtain ⟨A, hA, hbound⟩ := exists_physical_root_high_rank_contribution_bound
    hqmax0 hqmax1 hvs ell
  refine ⟨A, hA, ?_⟩
  intro I N M J n B P groups e _ patterns C hC k V q β retention ρ hVs hq i0 v vmin η τ T
    hMass hμ hmass hη hμatom hghost hedge hq0 hq1 hρ0 hρ1 hv hvmin hV hD ht hτ
    H hH ζ K θ hK hPs hPb hdis hSmallMass encode hinj
    L Cgroup Ccoeff Ch Arow vmax hL hCgroup hCcoeff hCh hArow hrowghost hrowedge hVmax
    hM hcoeff hInitial code
  let steps := (List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))
  let rows := (steps.map (fullMixedLengthRowFactor
    (fun g p => β g p / V (e.symm g).val) retention ρ v vmin
      (fun g => V (e.symm g).val) T)).prod
  have hrows0 : 0 ≤ rows := by
    apply List.prod_nonneg
    intro a ha
    obtain ⟨tag, _, rfl⟩ := List.mem_map.mp ha
    exact fullMixedLengthRowFactor_nonneg _ _ _ _ _ _ _ hρ1 (zero_lt_one.trans hv).le tag
  have hrow1 : rows ≤ (Arow ^ M) ^ (4 * (n + 1) + 1) := by
    have hh := full_mixed_length_row_product_le_uniform
      (fun g p => β g p / V (e.symm g).val) retention ρ v vmin vmax
      (fun g => V (e.symm g).val) T hmass hq0 hq1 hρ0 hρ1 (zero_lt_one.trans hv).le
      (fun g => (hvmin.trans_le (hV g)).le) hVmax hArow hrowghost hrowedge steps
    simpa only [steps, List.length_map, List.length_range, Fintype.card_fin] using hh
  have hrows := hrow1.trans (root_high_rank_row_power_le M (n + 1) hL hCgroup hArow hM)
  have hcost := root_high_rank_envelope_cost_power_le (n + 1) (birthForestRank code)
    hL hCcoeff hCh
    (mul_nonneg (pow_nonneg (zero_le_one.trans hA) _) (Nat.cast_nonneg _))
    (zero_le_one.trans hH) hrows0
    (prod_nonneg (fun g _ => pow_nonneg (sum_nonneg (fun p _ => hμ g p)) _))
    hτ hcoeff hrows hInitial
  exact (@hbound I N M J n B P groups e inferInstance patterns C hC k V q β
    retention ρ hVs hq i0 v vmin η τ T hMass hμ hmass hη hμatom hghost hedge
    hq0 hq1 hρ0 hρ1 hv hvmin hV hD ht hτ H hH ζ K θ hK hPs hPb hdis
    hSmallMass encode hinj code).trans hcost

end Bounty

end


-- Source module: RootPrimePatternPower
section

/- The literal pattern count and high-rank coefficient prefactor have
fixed polynomial costs for logarithmically many root groups. -/

open Finset
open scoped Classical
namespace Bounty

theorem repeated_big_prime_pattern_card_power
    {G : Type*} [Fintype G] [DecidableEq G] {J ell m : ℕ}
    (probes : G → Finset (Fin J)) (r t : Finset G) (hrt : Disjoint r t)
    (hp : ∀ g, (probes g).card ≤ m) {L a : ℝ} (hL : 2 ≤ L) (ha : 0 ≤ a)
    (hgroups : (Fintype.card G : ℝ) ≤ a * Real.log L) :
    (Fintype.card (RepeatedBigPrimePatternIndex (ell := ell) probes r t) : ℝ) ≤
      L ^ ((m : ℝ) * a * Real.log 2 + 1) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hcard : Fintype.card (RepeatedBigPrimePatternIndex (ell := ell) probes r t) ≤
      1 + 2 ^ (m * Fintype.card G) := by
    simpa only [RepeatedBigPrimePatternIndex, Fintype.card_sum, Fintype.card_unit] using
      Nat.add_le_add_left (repeated_big_prime_pattern_pair_card_le_groups
        (ell := ell) probes r t hrt hp) 1
  have hcardR : (Fintype.card (RepeatedBigPrimePatternIndex (ell := ell) probes r t) : ℝ) ≤
      1 + (2 : ℝ) ^ (m * Fintype.card G) := by exact_mod_cast hcard
  have hpow := repeated_big_log_count_pow_le (L := L) (a := a) (b := 2)
    m (Fintype.card G) hL0 (by norm_num) hgroups
  have he : 0 ≤ (m : ℝ) * a * Real.log 2 := by positivity
  have hone : 1 ≤ L ^ ((m : ℝ) * a * Real.log 2) := Real.one_le_rpow hL1 he
  calc
    _ ≤ 1 + L ^ ((m : ℝ) * a * Real.log 2) := hcardR.trans (add_le_add (le_refl _) hpow)
    _ ≤ 2 * L ^ ((m : ℝ) * a * Real.log 2) := by linarith
    _ ≤ L * L ^ ((m : ℝ) * a * Real.log 2) :=
      mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hL0.le _)
    _ = _ := by rw [mul_comm, ← Real.rpow_add_one hL0.ne']

theorem root_prime_high_rank_coefficient_power
    {G : Type*} [Fintype G] [DecidableEq G] {J ell m : ℕ}
    (probes : G → Finset (Fin J)) (r t : Finset G) (hrt : Disjoint r t)
    (hp : ∀ g, (probes g).card ≤ m) (small : ℕ)
    {L a A H C : ℝ} (hL : 2 ≤ L) (ha : 0 ≤ a) (hA : 1 ≤ A) (hH0 : 0 ≤ H)
    (hgroups : (Fintype.card G : ℝ) ≤ a * Real.log L)
    (hsmall : (small : ℝ) ≤ a * Real.log L) (hH : H ≤ L ^ C) :
    (A ^ small * (Fintype.card (RepeatedBigPrimePatternIndex (ell := ell) probes r t) : ℝ)) * H ≤
      L ^ (a * Real.log A + ((m : ℝ) * a * Real.log 2 + 1) + C) := by
  have hL0 : 0 < L := by linarith
  have hbase := repeated_big_group_energy_cost_le small hL0 (zero_le_one.trans hA) hsmall
  rw [max_eq_right hA] at hbase
  have hpatterns := repeated_big_prime_pattern_card_power (ell := ell) probes r t hrt hp hL ha hgroups
  calc
    _ ≤ (L ^ (a * Real.log A) * L ^ ((m : ℝ) * a * Real.log 2 + 1)) * L ^ C :=
      mul_le_mul (mul_le_mul hbase hpatterns (Nat.cast_nonneg _) (Real.rpow_nonneg hL0.le _))
        hH hH0 (mul_nonneg (Real.rpow_nonneg hL0.le _) (Real.rpow_nonneg hL0.le _))
    _ = _ := by rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]

end Bounty

end


-- Source module: PhysicalRootPrimeUniform
section

/- A single positive envelope bounds every literal alternating prime
kernel, including the even-time adjoint. -/

open Finset
open scoped Classical
namespace Bounty

theorem repeated_big_family_envelope_ge_one (s m Q : ℕ) (ξ : ℝ) :
    1 ≤ repeatedBigFamilyEnvelope s m Q ξ := by
  unfold repeatedBigFamilyEnvelope
  have h : 0 ≤ (2 : ℝ) ^ (m * s) * (((Q * Q : ℕ) : ℝ) / ξ) ^ 2 := by positivity
  linarith

theorem physical_root_alternating_prime_kernel_norm_le_family
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ) (probes : G → Finset (Fin J))
    (r t : Finset G) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ) (hξ : 0 < ξ)
    (time : ℕ) (i : RepeatedBigPrimePatternIndex (ell := ell) probes r t)
    (L R : PhysicalMarkLists P J ell)
    (aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t i)) :
    ‖if time % 2 = 0 then
        (starRingEnd ℂ) (physicalRootPrimeKernel P V probes r t hrt Q h ξ i R L aux)
      else physicalRootPrimeKernel P V probes r t hrt Q h ξ i L R aux‖ ≤
      repeatedBigFamilyEnvelope (Fintype.card G) J Q ξ := by
  have hsum : repeatedBigPrimePatternBound probes r t Q ξ i ≤
      repeatedBigFamilyEnvelope (Fintype.card G) J Q ξ := by
    apply le_trans (single_le_sum (fun j _ =>
      repeated_big_prime_pattern_bound_nonneg probes r t Q ξ j) (mem_univ i))
    exact repeated_big_prime_pattern_bound_sum_le_envelope probes r t hrt Q ξ
  split_ifs
  · simpa only [starRingEnd_apply, norm_star] using
      (physical_root_prime_kernel_norm_le P V probes r t hrt Q h ξ hξ i R L aux).trans hsum
  · exact (physical_root_prime_kernel_norm_le P V probes r t hrt Q h ξ hξ i L R aux).trans hsum

end Bounty

end


-- Source module: PhysicalGroupResidueProducts
section

/- Reindexing physical groups preserves the exact product of local residue averages. -/

open Finset
open scoped Classical
namespace Bounty

theorem physical_pool_expectation_group_reindex
    {G H : Type*} [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
    (e : G ≃ H) (P : G → Finset ℕ) (J ell : ℕ)
    [∀ p : PhysicalPrime P, NeZero p.2.val]
    [∀ p : PhysicalPrime (fun h => P (e.symm h)), NeZero p.2.val]
    (visits : Finset ℕ) (L : ℕ → PhysicalMarkLists P J ell)
    (offset : ℕ → ℤ) (η : ℕ → ℝ) :
    poolPathResidueExpectation
        (fun v : PhysicalPrime (fun h => P (e.symm h)) => v.2.val) univ visits
        (fun v => visits.filter (fun j =>
          v ∈ physicalMarkedPrimes (physicalMarkGroupReindex e P J ell (L j))))
        (fun v j => -(offset j : ZMod v.2.val)) η =
      poolPathResidueExpectation (fun v : PhysicalPrime P => v.2.val) univ visits
        (fun v => visits.filter (fun j => v ∈ physicalMarkedPrimes (L j)))
        (fun v j => -(offset j : ZMod v.2.val)) η := by
  let : ∀ (g : G) (p : P g), NeZero p.val :=
    fun g p => inferInstanceAs (NeZero (⟨g, p⟩ : PhysicalPrime P).2.val)
  unfold poolPathResidueExpectation
  simp only [Fintype.prod_sigma, mem_physical_marked_primes]
  exact Equiv.prod_comp e.symm (fun g : G =>
    ∏ p : P g, (∑ z : ZMod p.val, activeResidueWeight visits
      (visits.filter (fun j => p.val ∈ physicalGroupMarks (L j) g))
      (fun j => -(offset j : ZMod p.val)) η z) / (p.val : ℝ))

end Bounty

end


-- Source module: PhysicalFinitePathGroupReindex
section

/- Reindexing the original finite paths preserves every label, offset and coefficient. -/

open Finset
open scoped Classical
namespace Bounty
section Reindex
variable {G H I : Type*} (e : G ≃ H) (P : G → Finset ℕ) (J ell : ℕ)
  (patterns : Finset I) (C : I → G → Finset (Fin J))

def physicalFinitePathGroupReindex (r : ℕ) :
    (Fin (r + 1) → PhysicalEdgeLabels P J ell patterns C × PhysicalMarkLists P J ell) ≃
      (Fin (r + 1) →
        PhysicalEdgeLabels (fun h => P (e.symm h)) J ell patterns (fun i h => C i (e.symm h)) ×
          PhysicalMarkLists (fun h => P (e.symm h)) J ell) :=
  Equiv.piCongrRight (fun _ => Equiv.prodCongr
    (physicalEdgeGroupReindex e P J ell patterns C) (physicalMarkGroupReindex e P J ell))

theorem physical_finite_path_labels_group_reindex (r : ℕ)
    (p : Fin (r + 1) → PhysicalEdgeLabels P J ell patterns C × PhysicalMarkLists P J ell) :
    finitePathLabels (physicalFinitePathGroupReindex e P J ell patterns C r p) =
      fun j => physicalEdgeGroupReindex e P J ell patterns C (finitePathLabels p j) := by
  funext j
  unfold finitePathLabels
  split <;> rfl

theorem physical_finite_path_marks_group_reindex (r : ℕ)
    (L : PhysicalMarkLists P J ell)
    (p : Fin (r + 1) → PhysicalEdgeLabels P J ell patterns C × PhysicalMarkLists P J ell) :
    finitePathMarks (physicalMarkGroupReindex e P J ell L)
      (physicalFinitePathGroupReindex e P J ell patterns C r p) =
      fun j => physicalMarkGroupReindex e P J ell (finitePathMarks L p j) := by
  funext j
  cases j with
  | zero => rfl
  | succ j =>
    simp only [finitePathMarks]
    split_ifs <;> rfl

variable [Fintype G] [Fintype H]

theorem physical_bare_offset_group_reindex (k : ℕ → I → ℤ)
    (a : ℕ → PhysicalEdgeLabels P J ell patterns C)
    (L : ℕ → PhysicalMarkLists P J ell) (edges j : ℕ) :
    physicalBareOffset (fun i h => C i (e.symm h)) k
      (fun t => physicalEdgeGroupReindex e P J ell patterns C (a t))
      (fun t => physicalMarkGroupReindex e P J ell (L t)) edges j =
      physicalBareOffset C k a L edges j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [physicalBareOffset, ih, physical_bare_step_group_reindex]

theorem physical_finite_bare_offset_group_reindex (r : ℕ) (k : ℕ → I → ℤ)
    (L : PhysicalMarkLists P J ell)
    (p : Fin (r + 1) → PhysicalEdgeLabels P J ell patterns C × PhysicalMarkLists P J ell)
    (edges j : ℕ) :
    physicalBareOffset (fun i h => C i (e.symm h)) k
      (finitePathLabels (physicalFinitePathGroupReindex e P J ell patterns C r p))
      (finitePathMarks (physicalMarkGroupReindex e P J ell L)
        (physicalFinitePathGroupReindex e P J ell patterns C r p)) edges j =
      physicalBareOffset C k (finitePathLabels p) (finitePathMarks L p) edges j := by
  rw [physical_finite_path_labels_group_reindex, physical_finite_path_marks_group_reindex]
  exact physical_bare_offset_group_reindex e P J ell patterns C k _ _ edges j

variable [DecidableEq G] [DecidableEq H]

theorem physical_bare_walk_scalar_group_reindex (V : G → ℝ) (ζ : ℕ → I → ℝ)
    (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
      PhysicalAuxLabels P (C i) → ℂ)
    (a : ℕ → PhysicalEdgeLabels P J ell patterns C)
    (L : ℕ → PhysicalMarkLists P J ell) (edges : ℕ) :
    physicalBareWalkScalar (fun h => V (e.symm h)) patterns (fun i h => C i (e.symm h)) ζ
      (fun t i => physicalGroupReindexedCoefficient e (C i) (K t i))
      (fun t => physicalEdgeGroupReindex e P J ell patterns C (a t))
      (fun t => physicalMarkGroupReindex e P J ell (L t)) edges =
      physicalBareWalkScalar V patterns C ζ K a L edges := by
  unfold physicalBareWalkScalar
  apply prod_congr rfl
  intro j _
  exact physical_bare_labeled_group_reindex e P J ell patterns C V (ζ _) (K _) _ _ _

theorem physical_finite_return_scalar_group_reindex (V : G → ℝ)
    (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ)
    (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
      PhysicalAuxLabels P (C i) → ℂ)
    (r : ℕ) (L : PhysicalMarkLists P J ell)
    (p : Fin (r + 1) → PhysicalEdgeLabels P J ell patterns C × PhysicalMarkLists P J ell) :
    physicalFiniteReturnScalar (fun h => V (e.symm h)) patterns (fun i h => C i (e.symm h)) ζ k
      (fun t i => physicalGroupReindexedCoefficient e (C i) (K t i)) r
      (physicalMarkGroupReindex e P J ell L)
      (physicalFinitePathGroupReindex e P J ell patterns C r p) =
      physicalFiniteReturnScalar V patterns C ζ k K r L p := by
  unfold physicalFiniteReturnScalar physicalBareReturnScalar
  rw [physical_finite_path_labels_group_reindex, physical_finite_path_marks_group_reindex,
    physical_bare_offset_group_reindex, physical_bare_walk_scalar_group_reindex]

end Reindex
end Bounty

end


-- Source module: PhysicalFiniteVertexGroupReindex
section

/- The original finite-path residue expectation is unchanged by group reindexing. -/

open Finset
open scoped Classical
namespace Bounty

theorem physical_finite_vertex_expectation_group_reindex
    {G H I : Type*} [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
    (e : G ≃ H) (P : G → Finset ℕ) (J ell : ℕ)
    [∀ p : PhysicalPrime P, NeZero p.2.val]
    [∀ p : PhysicalPrime (fun h => P (e.symm h)), NeZero p.2.val]
    (patterns : Finset I) (C : I → G → Finset (Fin J))
    (q : ℝ) (k : ℕ → I → ℤ) (r : ℕ) (L : PhysicalMarkLists P J ell)
    (p : Fin (r + 1) → PhysicalEdgeLabels P J ell patterns C × PhysicalMarkLists P J ell) :
    physicalFiniteVertexExpectation (fun i h => C i (e.symm h)) q k r
        (physicalMarkGroupReindex e P J ell L)
        (physicalFinitePathGroupReindex e P J ell patterns C r p) =
      physicalFiniteVertexExpectation C q k r L p := by
  simp only [physicalFiniteVertexExpectation, physical_finite_path_labels_group_reindex,
    physical_finite_path_marks_group_reindex, physical_bare_offset_group_reindex]
  exact physical_pool_expectation_group_reindex e P J ell (range (r + 2))
    (finitePathMarks L p)
    (physicalBareOffset C k (finitePathLabels p) (finitePathMarks L p) (r + 1))
    (fun j => 1 - physicalEndpointSchedule q (r + 1) j)

end Bounty

end


-- Source module: PhysicalRootResidueGroupReindex
section

/- The original residue model is invariant under an equivalence of its group index. -/

open Finset
open scoped Classical
namespace Bounty

theorem physical_root_residue_model_group_reindex
    {G H I : Type*} [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
    (e : G ≃ H) (P : G → Finset ℕ) (J ell : ℕ)
    [∀ p : PhysicalPrime P, NeZero p.2.val]
    [∀ p : PhysicalPrime (fun h => P (e.symm h)), NeZero p.2.val]
    (V : G → ℝ) (patterns : Finset I) (C : I → G → Finset (Fin J))
    (q : ℝ) (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ)
    (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
      PhysicalAuxLabels P (C i) → ℂ) (r : ℕ) :
    physicalRootResidueModel (fun h => V (e.symm h)) patterns (fun i h => C i (e.symm h))
      q ζ k (fun t i => physicalGroupReindexedCoefficient e (C i) (K t i)) r =
      physicalRootResidueModel V patterns C q ζ k K r := by
  let _ : Fintype (PhysicalEdgeLabels P J ell patterns C) := inferInstance
  let _ : Fintype (PhysicalEdgeLabels (fun h => P (e.symm h)) J ell patterns
    (fun i h => C i (e.symm h))) := inferInstance
  unfold physicalRootResidueModel
  rw [physical_state_mass_group_reindex]
  apply congrArg (fun z : ℂ => (physicalStateMass V J ell : ℂ) * z)
  rw [← Equiv.sum_comp (physicalMarkGroupReindex e P J ell)]
  apply sum_congr rfl
  intro L _
  rw [← Equiv.sum_comp (physicalFinitePathGroupReindex e P J ell patterns C r)]
  apply sum_congr rfl
  intro p _
  rw [physical_finite_return_scalar_group_reindex,
    physical_finite_vertex_expectation_group_reindex]

theorem physical_root_residue_model_equiv_fin
    {G I : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (J ell : ℕ)
    [inst : ∀ p : PhysicalPrime P, NeZero p.2.val]
    (V : G → ℝ) (patterns : Finset I) (C : I → G → Finset (Fin J))
    (q : ℝ) (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ)
    (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
      PhysicalAuxLabels P (C i) → ℂ) (r : ℕ) :
    let e := Fintype.equivFin G
    letI : ∀ p : PhysicalPrime (fun h => P (e.symm h)), NeZero p.2.val :=
      fun p => inst ⟨e.symm p.1, p.2⟩
    physicalRootResidueModel V patterns C q ζ k K r =
      physicalRootResidueModel (fun h => V (e.symm h)) patterns (fun i h => C i (e.symm h))
        q ζ k (fun t i => physicalGroupReindexedCoefficient e (C i) (K t i)) r := by
  let e := Fintype.equivFin G
  let : ∀ p : PhysicalPrime (fun h => P (e.symm h)), NeZero p.2.val :=
    fun p => inst ⟨e.symm p.1, p.2⟩
  exact (physical_root_residue_model_group_reindex e P J ell V patterns C q ζ k K r).symm

theorem physical_root_residue_model_group_reindex_norm_le
    {G H I : Type*} [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
    (e : G ≃ H) (P : G → Finset ℕ) (J ell : ℕ)
    [∀ p : PhysicalPrime P, NeZero p.2.val]
    [∀ p : PhysicalPrime (fun h => P (e.symm h)), NeZero p.2.val]
    (V : G → ℝ) (patterns : Finset I) (C : I → G → Finset (Fin J))
    (q : ℝ) (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ)
    (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
      PhysicalAuxLabels P (C i) → ℂ) (r : ℕ) (bound : ℝ)
    (hbound : ‖physicalRootResidueModel (fun h => V (e.symm h)) patterns
      (fun i h => C i (e.symm h)) q ζ k
      (fun t i => physicalGroupReindexedCoefficient e (C i) (K t i)) r‖ ≤ bound) :
    ‖physicalRootResidueModel V patterns C q ζ k K r‖ ≤ bound := by
  rw [physical_root_residue_model_group_reindex e P J ell V patterns C q ζ k K r] at hbound
  exact hbound

end Bounty

end


-- Source module: PhysicalPatternReindex
section

/- Exact transport of auxiliary labels and original edges under a pattern equivalence. -/

open Finset
open scoped Classical
namespace Bounty

section Aux
variable {G : Type*} (P : G → Finset ℕ) {J : ℕ}
  (C C' : G → Finset (Fin J)) (hC : ∀ g, C' g = C g)

def physicalAuxCutEquiv : PhysicalAuxLabels P C ≃ PhysicalAuxLabels P C' where
  toFun a g j := a g ⟨j.val, by simpa only [hC g] using j.property⟩
  invFun a g j := a g ⟨j.val, by simpa only [hC g] using j.property⟩
  left_inv a := by funext g j; rfl
  right_inv a := by funext g j; rfl

theorem physical_D_aux_cut_equiv [Fintype G] {ell : ℕ}
    (L : PhysicalMarkLists P J ell) (a : PhysicalAuxLabels P C) :
    physicalD C' L (physicalAuxCutEquiv P C C' hC a) = physicalD C L a := by
  have he : C' = C := funext hC
  subst C'
  rfl

theorem physical_bare_pattern_aux_cut_equiv [Fintype G] [DecidableEq G] {ell : ℕ}
    (V : G → ℝ) (ζ ζ' : ℝ) (hζ : ζ' = ζ)
    (K : PhysicalMarkLists P J ell → PhysicalMarkLists P J ell → PhysicalAuxLabels P C → ℂ)
    (K' : PhysicalMarkLists P J ell → PhysicalMarkLists P J ell → PhysicalAuxLabels P C' → ℂ)
    (hK : ∀ L R a, K' L R (physicalAuxCutEquiv P C C' hC a) = K L R a)
    (a : PhysicalAuxLabels P C) (L R : PhysicalMarkLists P J ell) :
    physicalBarePatternScalar V C' ζ' K' (physicalAuxCutEquiv P C C' hC a) L R =
      physicalBarePatternScalar V C ζ K a L R := by
  have he : C' = C := funext hC
  subst C'
  subst ζ'
  have heK : K' = K := by
    funext L R a
    exact hK L R a
  rw [heK]
  rfl

end Aux

section Pattern
variable {G I I' : Type*} [Fintype I] [Fintype I']
  (f : I ≃ I') (P : G → Finset ℕ) (J ell : ℕ)
  (C : I → G → Finset (Fin J)) (C' : I' → G → Finset (Fin J))
  (hC : ∀ i g, C' (f i) g = C i g)

def physicalPatternSubtypeEquiv : ↥(univ : Finset I) ≃ ↥(univ : Finset I') where
  toFun i := ⟨f i.val, mem_univ _⟩
  invFun i := ⟨f.symm i.val, mem_univ _⟩
  left_inv i := by apply Subtype.ext; exact f.symm_apply_apply i.val
  right_inv i := by apply Subtype.ext; exact f.apply_symm_apply i.val

def physicalEdgePatternEquiv :
    PhysicalEdgeLabels P J ell univ C ≃ PhysicalEdgeLabels P J ell univ C' :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _)
    (Equiv.sigmaCongr (physicalPatternSubtypeEquiv f)
      (fun i => physicalAuxCutEquiv P (C i.val) (C' (f i.val)) (hC i.val))))

theorem physical_bare_step_pattern_equiv [Fintype G]
    (k : I → ℤ) (k' : I' → ℤ) (hk : ∀ i, k' (f i) = k i)
    (a : PhysicalEdgeLabels P J ell univ C) (L : PhysicalMarkLists P J ell) :
    physicalBareStep C' k' (physicalEdgePatternEquiv f P J ell C C' hC a) L =
      physicalBareStep C k a L := by
  change k' (f a.2.2.1.val) *
    (physicalD (C' (f a.2.2.1.val)) (physicalPermuteLabels a.1 L)
      (physicalAuxCutEquiv P (C a.2.2.1.val) (C' (f a.2.2.1.val))
        (hC a.2.2.1.val) a.2.2.2) : ℕ) = _
  rw [hk, physical_D_aux_cut_equiv]
  rfl

theorem physical_bare_labeled_scalar_pattern_equiv [Fintype G] [DecidableEq G]
    (V : G → ℝ) (ζ : I → ℝ) (ζ' : I' → ℝ) (hζ : ∀ i, ζ' (f i) = ζ i)
    (K : ∀ i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell → PhysicalAuxLabels P (C i) → ℂ)
    (K' : ∀ i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell → PhysicalAuxLabels P (C' i) → ℂ)
    (hK : ∀ i L R a, K' (f i) L R
      (physicalAuxCutEquiv P (C i) (C' (f i)) (hC i) a) = K i L R a)
    (a : PhysicalEdgeLabels P J ell univ C) (L R : PhysicalMarkLists P J ell) :
    physicalBareLabeledScalar V univ C' ζ' K'
      (physicalEdgePatternEquiv f P J ell C C' hC a) L R =
      physicalBareLabeledScalar V univ C ζ K a L R := by
  unfold physicalBareLabeledScalar
  congr 1
  exact physical_bare_pattern_aux_cut_equiv P _ _ (hC a.2.2.1.val) V _ _
    (hζ a.2.2.1.val) _ _ (hK a.2.2.1.val) _ _ _

end Pattern
end Bounty

end


-- Source module: PhysicalRootResiduePatternReindex
section

/- Exact reindexing of the pattern sum in the original root residue model. -/

open Finset
open scoped Classical
namespace Bounty
section Reindex
variable {G I I' : Type*} [Fintype I] [Fintype I']
  (f : I ≃ I') (P : G → Finset ℕ) (J ell : ℕ)
  (C : I → G → Finset (Fin J)) (C' : I' → G → Finset (Fin J))
  (hC : ∀ i g, C' (f i) g = C i g)

def physicalFinitePathPatternEquiv (r : ℕ) :
    (Fin (r + 1) → PhysicalEdgeLabels P J ell univ C × PhysicalMarkLists P J ell) ≃
      (Fin (r + 1) → PhysicalEdgeLabels P J ell univ C' × PhysicalMarkLists P J ell) :=
  Equiv.piCongrRight (fun _ => Equiv.prodCongr
    (physicalEdgePatternEquiv f P J ell C C' hC) (Equiv.refl _))

theorem physical_finite_path_labels_pattern_equiv (r : ℕ)
    (p : Fin (r + 1) → PhysicalEdgeLabels P J ell univ C × PhysicalMarkLists P J ell) :
    finitePathLabels (physicalFinitePathPatternEquiv f P J ell C C' hC r p) =
      fun j => physicalEdgePatternEquiv f P J ell C C' hC (finitePathLabels p j) := by
  funext j
  unfold finitePathLabels
  split <;> rfl

theorem physical_finite_path_marks_pattern_equiv (r : ℕ)
    (L : PhysicalMarkLists P J ell)
    (p : Fin (r + 1) → PhysicalEdgeLabels P J ell univ C × PhysicalMarkLists P J ell) :
    finitePathMarks L (physicalFinitePathPatternEquiv f P J ell C C' hC r p) =
      finitePathMarks L p := by
  funext j
  cases j with
  | zero => rfl
  | succ j =>
    simp only [finitePathMarks]
    split_ifs <;> rfl

variable [Fintype G]

theorem physical_bare_offset_pattern_equiv
    (k : ℕ → I → ℤ) (k' : ℕ → I' → ℤ) (hk : ∀ t i, k' t (f i) = k t i)
    (a : ℕ → PhysicalEdgeLabels P J ell univ C)
    (L : ℕ → PhysicalMarkLists P J ell) (edges j : ℕ) :
    physicalBareOffset C' k'
      (fun t => physicalEdgePatternEquiv f P J ell C C' hC (a t)) L edges j =
      physicalBareOffset C k a L edges j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [physicalBareOffset, ih,
      physical_bare_step_pattern_equiv f P J ell C C' hC _ _ (hk _)]

variable [DecidableEq G]

theorem physical_bare_walk_scalar_pattern_equiv (V : G → ℝ)
    (ζ : ℕ → I → ℝ) (ζ' : ℕ → I' → ℝ) (hζ : ∀ t i, ζ' t (f i) = ζ t i)
    (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
      PhysicalAuxLabels P (C i) → ℂ)
    (K' : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
      PhysicalAuxLabels P (C' i) → ℂ)
    (hK : ∀ t i L R a, K' t (f i) L R
      (physicalAuxCutEquiv P (C i) (C' (f i)) (hC i) a) = K t i L R a)
    (a : ℕ → PhysicalEdgeLabels P J ell univ C)
    (L : ℕ → PhysicalMarkLists P J ell) (edges : ℕ) :
    physicalBareWalkScalar V univ C' ζ' K'
      (fun t => physicalEdgePatternEquiv f P J ell C C' hC (a t)) L edges =
      physicalBareWalkScalar V univ C ζ K a L edges := by
  unfold physicalBareWalkScalar
  apply prod_congr rfl
  intro j _
  exact physical_bare_labeled_scalar_pattern_equiv f P J ell C C' hC V _ _
    (hζ _) _ _ (hK _) _ _ _

theorem physical_finite_return_scalar_pattern_equiv (V : G → ℝ)
    (ζ : ℕ → I → ℝ) (ζ' : ℕ → I' → ℝ) (hζ : ∀ t i, ζ' t (f i) = ζ t i)
    (k : ℕ → I → ℤ) (k' : ℕ → I' → ℤ) (hk : ∀ t i, k' t (f i) = k t i)
    (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
      PhysicalAuxLabels P (C i) → ℂ)
    (K' : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
      PhysicalAuxLabels P (C' i) → ℂ)
    (hK : ∀ t i L R a, K' t (f i) L R
      (physicalAuxCutEquiv P (C i) (C' (f i)) (hC i) a) = K t i L R a)
    (r : ℕ) (L : PhysicalMarkLists P J ell)
    (p : Fin (r + 1) → PhysicalEdgeLabels P J ell univ C × PhysicalMarkLists P J ell) :
    physicalFiniteReturnScalar V univ C' ζ' k' K' r L
      (physicalFinitePathPatternEquiv f P J ell C C' hC r p) =
      physicalFiniteReturnScalar V univ C ζ k K r L p := by
  unfold physicalFiniteReturnScalar physicalBareReturnScalar
  rw [physical_finite_path_labels_pattern_equiv, physical_finite_path_marks_pattern_equiv,
    physical_bare_offset_pattern_equiv f P J ell C C' hC k k' hk,
    physical_bare_walk_scalar_pattern_equiv f P J ell C C' hC V ζ ζ' hζ K K' hK]

variable [∀ p : PhysicalPrime P, NeZero p.2.val]

theorem physical_finite_vertex_expectation_pattern_equiv (q : ℝ)
    (k : ℕ → I → ℤ) (k' : ℕ → I' → ℤ) (hk : ∀ t i, k' t (f i) = k t i)
    (r : ℕ) (L : PhysicalMarkLists P J ell)
    (p : Fin (r + 1) → PhysicalEdgeLabels P J ell univ C × PhysicalMarkLists P J ell) :
    physicalFiniteVertexExpectation C' q k' r L
      (physicalFinitePathPatternEquiv f P J ell C C' hC r p) =
      physicalFiniteVertexExpectation C q k r L p := by
  unfold physicalFiniteVertexExpectation
  simp only [physical_finite_path_labels_pattern_equiv, physical_finite_path_marks_pattern_equiv,
    physical_bare_offset_pattern_equiv f P J ell C C' hC k k' hk]

theorem physical_root_residue_model_pattern_equiv (V : G → ℝ) (q : ℝ)
    (ζ : ℕ → I → ℝ) (ζ' : ℕ → I' → ℝ) (hζ : ∀ t i, ζ' t (f i) = ζ t i)
    (k : ℕ → I → ℤ) (k' : ℕ → I' → ℤ) (hk : ∀ t i, k' t (f i) = k t i)
    (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
      PhysicalAuxLabels P (C i) → ℂ)
    (K' : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
      PhysicalAuxLabels P (C' i) → ℂ)
    (hK : ∀ t i L R a, K' t (f i) L R
      (physicalAuxCutEquiv P (C i) (C' (f i)) (hC i) a) = K t i L R a)
    (r : ℕ) :
    physicalRootResidueModel V univ C' q ζ' k' K' r =
      physicalRootResidueModel V univ C q ζ k K r := by
  let _ : Fintype (PhysicalEdgeLabels P J ell univ C) := inferInstance
  let _ : Fintype (PhysicalEdgeLabels P J ell univ C') := inferInstance
  unfold physicalRootResidueModel
  apply congrArg (fun z : ℂ => (physicalStateMass V J ell : ℂ) * z)
  apply sum_congr rfl
  intro L _
  rw [← Equiv.sum_comp (physicalFinitePathPatternEquiv f P J ell C C' hC r)]
  apply sum_congr rfl
  intro p _
  rw [physical_finite_return_scalar_pattern_equiv f P J ell C C' hC V ζ ζ' hζ k k' hk K K' hK,
    physical_finite_vertex_expectation_pattern_equiv f P J ell C C' hC q k k' hk]

end Reindex
end Bounty

end


-- Source module: PhysicalRootPrimeGroupReindex
section

/- Group reindexing of the original root prime kernel, with the original
pattern index retained at the outer interface. -/

open scoped Classical
namespace Bounty

section Reindex
variable {G H : Type*} [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
  {J ell : ℕ} (e : G ≃ H) (P : G → Finset ℕ)
  (probes : G → Finset (Fin J)) (r t : Finset H)

noncomputable def physicalRootPrimeGroupAux
    (i : RepeatedBigPrimePatternIndex (ell := ell) probes
      (r.map e.symm.toEmbedding) (t.map e.symm.toEmbedding))
    (a : PhysicalAuxLabels (fun g => P (e.symm g))
      (fun g => repeatedBigPrimePatternCut probes
        (r.map e.symm.toEmbedding) (t.map e.symm.toEmbedding) i (e.symm g))) :
    PhysicalAuxLabels (fun g => P (e.symm g))
      (repeatedBigPrimePatternCut (fun g => probes (e.symm g)) r t
        ((repeatedBigPrimePatternEquiv e.symm.toEmbedding probes r t).symm i)) :=
  fun g j => a g ⟨j.val, by
    exact (congrArg (fun s : Finset (Fin J) => j.val ∈ s)
      (repeated_big_prime_pattern_equiv_symm_cut e.symm.toEmbedding probes r t i g)).mp
        j.property⟩

theorem physical_group_reindexed_root_prime_kernel
    (V : G → ℝ) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (i : RepeatedBigPrimePatternIndex (ell := ell) probes
      (r.map e.symm.toEmbedding) (t.map e.symm.toEmbedding))
    (L R : PhysicalMarkLists (fun g => P (e.symm g)) J ell)
    (a : PhysicalAuxLabels (fun g => P (e.symm g))
      (fun g => repeatedBigPrimePatternCut probes
        (r.map e.symm.toEmbedding) (t.map e.symm.toEmbedding) i (e.symm g))) :
    physicalGroupReindexedCoefficient e
      (repeatedBigPrimePatternCut probes
        (r.map e.symm.toEmbedding) (t.map e.symm.toEmbedding) i)
      (physicalRootPrimeKernel P V probes
        (r.map e.symm.toEmbedding) (t.map e.symm.toEmbedding)
        ((Finset.disjoint_map e.symm.toEmbedding).mpr hrt) Q h ξ i) L R a =
    physicalRootPrimeKernel (fun g => P (e.symm g)) (fun g => V (e.symm g))
      (fun g => probes (e.symm g)) r t hrt Q h ξ
      ((repeatedBigPrimePatternEquiv e.symm.toEmbedding probes r t).symm i) L R
      (physicalRootPrimeGroupAux e P probes r t i a) := by
  let C := repeatedBigPrimePatternCut probes
    (r.map e.symm.toEmbedding) (t.map e.symm.toEmbedding) i
  have hL : (fun g => ((physicalMarkGroupReindex e P J ell).symm L) (e.symm g)) = L :=
    (physicalMarkGroupReindex e P J ell).apply_symm_apply L
  have hR : (fun g => ((physicalMarkGroupReindex e P J ell).symm R) (e.symm g)) = R :=
    (physicalMarkGroupReindex e P J ell).apply_symm_apply R
  have ha : (fun g => ((physicalAuxGroupReindex e P J C).symm a) (e.symm g)) = a :=
    (physicalAuxGroupReindex e P J C).apply_symm_apply a
  have hk := physical_root_prime_kernel_equiv e.symm.toEmbedding P V probes r t hrt Q h ξ i
    ((physicalMarkGroupReindex e P J ell).symm L)
    ((physicalMarkGroupReindex e P J ell).symm R)
    ((physicalAuxGroupReindex e P J C).symm a)
  unfold physicalGroupReindexedCoefficient
  refine hk.trans ?_
  simp only [Equiv.toEmbedding_apply]
  rw [hL, hR]
  apply congrArg (physicalRootPrimeKernel (fun g => P (e.symm g))
    (fun g => V (e.symm g)) (fun g => probes (e.symm g)) r t hrt Q h ξ
    ((repeatedBigPrimePatternEquiv e.symm.toEmbedding probes r t).symm i) L R)
  funext g j
  exact congrFun (congrFun ha g) ⟨j.val, by
    exact (congrArg (fun s : Finset (Fin J) => j.val ∈ s)
      (repeated_big_prime_pattern_equiv_symm_cut e.symm.toEmbedding probes r t i g)).mp
        j.property⟩

end Reindex
end Bounty

end


-- Source module: PhysicalRootPrimeOriginalGroupReindex
section

/- The kernel bridge with arbitrary original group subsets. All inverse-map
equalities and dependent pattern casts are discharged in this module. -/

open scoped Classical
namespace Bounty

section Maps
variable {G H : Type*} [DecidableEq G] [DecidableEq H] {J ell : ℕ}
  (e : G ≃ H) (probes : G → Finset (Fin J))
  (rG tG : Finset G) (rH tH : Finset H)
  (hr : rH.map e.symm.toEmbedding = rG) (ht : tH.map e.symm.toEmbedding = tG)

noncomputable def physicalRootPrimePatternEquivOfMaps :
    RepeatedBigPrimePatternIndex (ell := ell) probes rG tG ≃
      RepeatedBigPrimePatternIndex (ell := ell) (fun g => probes (e.symm g)) rH tH := by
  subst rG
  subst tG
  exact (repeatedBigPrimePatternEquiv e.symm.toEmbedding probes rH tH).symm

theorem physical_root_prime_pattern_equiv_of_maps_cut
    (i : RepeatedBigPrimePatternIndex (ell := ell) probes rG tG) (g : H) :
    repeatedBigPrimePatternCut (fun g => probes (e.symm g)) rH tH
      (physicalRootPrimePatternEquivOfMaps e probes rG tG rH tH hr ht i) g =
      repeatedBigPrimePatternCut probes rG tG i (e.symm g) := by
  subst rG
  subst tG
  exact repeated_big_prime_pattern_equiv_symm_cut e.symm.toEmbedding probes rH tH i g

noncomputable def physicalRootPrimeAuxOfMaps (P : G → Finset ℕ)
    (i : RepeatedBigPrimePatternIndex (ell := ell) probes rG tG)
    (a : PhysicalAuxLabels (fun g => P (e.symm g))
      (fun g => repeatedBigPrimePatternCut probes rG tG i (e.symm g))) :
    PhysicalAuxLabels (fun g => P (e.symm g))
      (repeatedBigPrimePatternCut (fun g => probes (e.symm g)) rH tH
        (physicalRootPrimePatternEquivOfMaps e probes rG tG rH tH hr ht i)) :=
  fun g j => a g ⟨j.val, by
    exact (congrArg (fun s : Finset (Fin J) => j.val ∈ s)
      (physical_root_prime_pattern_equiv_of_maps_cut e probes rG tG rH tH hr ht i g)).mp
        j.property⟩

theorem physical_group_reindexed_root_prime_kernel_of_maps
    [Fintype G] [Fintype H] (P : G → Finset ℕ) (V : G → ℝ)
    (hrtG : Disjoint rG tG) (hrtH : Disjoint rH tH) (Q : ℕ) (h ξ : ℝ)
    (i : RepeatedBigPrimePatternIndex (ell := ell) probes rG tG)
    (L R : PhysicalMarkLists (fun g => P (e.symm g)) J ell)
    (a : PhysicalAuxLabels (fun g => P (e.symm g))
      (fun g => repeatedBigPrimePatternCut probes rG tG i (e.symm g))) :
    physicalGroupReindexedCoefficient e (repeatedBigPrimePatternCut probes rG tG i)
      (physicalRootPrimeKernel P V probes rG tG hrtG Q h ξ i) L R a =
    physicalRootPrimeKernel (fun g => P (e.symm g)) (fun g => V (e.symm g))
      (fun g => probes (e.symm g)) rH tH hrtH Q h ξ
      (physicalRootPrimePatternEquivOfMaps e probes rG tG rH tH hr ht i) L R
      (physicalRootPrimeAuxOfMaps e probes rG tG rH tH hr ht P i a) := by
  subst rG
  subst tG
  exact physical_group_reindexed_root_prime_kernel e P probes rH tH V hrtH Q h ξ i L R a

end Maps

section Original
variable {G H : Type*} [DecidableEq G] [DecidableEq H] {J ell : ℕ}
  (e : G ≃ H) (probes : G → Finset (Fin J)) (r t : Finset G)

noncomputable def physicalRootPrimeGroupPattern :
    RepeatedBigPrimePatternIndex (ell := ell) probes r t ≃
      RepeatedBigPrimePatternIndex (ell := ell) (fun g => probes (e.symm g))
        (r.map e.toEmbedding) (t.map e.toEmbedding) :=
  physicalRootPrimePatternEquivOfMaps e probes r t (r.map e.toEmbedding) (t.map e.toEmbedding)
    (by simp [Finset.map_map]) (by simp [Finset.map_map])

noncomputable def physicalRootPrimeGroupOriginalAux (P : G → Finset ℕ)
    (i : RepeatedBigPrimePatternIndex (ell := ell) probes r t)
    (a : PhysicalAuxLabels (fun g => P (e.symm g))
      (fun g => repeatedBigPrimePatternCut probes r t i (e.symm g))) :
    PhysicalAuxLabels (fun g => P (e.symm g))
      (repeatedBigPrimePatternCut (fun g => probes (e.symm g))
        (r.map e.toEmbedding) (t.map e.toEmbedding) (physicalRootPrimeGroupPattern e probes r t i)) :=
  physicalRootPrimeAuxOfMaps e probes r t (r.map e.toEmbedding) (t.map e.toEmbedding)
    (by simp [Finset.map_map]) (by simp [Finset.map_map]) P i a

theorem physical_root_prime_group_pattern_cut
    (i : RepeatedBigPrimePatternIndex (ell := ell) probes r t) (g : H) :
    repeatedBigPrimePatternCut (fun g => probes (e.symm g))
      (r.map e.toEmbedding) (t.map e.toEmbedding) (physicalRootPrimeGroupPattern e probes r t i) g =
      repeatedBigPrimePatternCut probes r t i (e.symm g) :=
  physical_root_prime_pattern_equiv_of_maps_cut e probes r t
    (r.map e.toEmbedding) (t.map e.toEmbedding)
    (by simp [Finset.map_map]) (by simp [Finset.map_map]) i g

theorem physical_group_reindexed_root_prime_kernel_original
    [Fintype G] [Fintype H] (P : G → Finset ℕ) (V : G → ℝ)
    (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (i : RepeatedBigPrimePatternIndex (ell := ell) probes r t)
    (L R : PhysicalMarkLists (fun g => P (e.symm g)) J ell)
    (a : PhysicalAuxLabels (fun g => P (e.symm g))
      (fun g => repeatedBigPrimePatternCut probes r t i (e.symm g))) :
    physicalGroupReindexedCoefficient e (repeatedBigPrimePatternCut probes r t i)
      (physicalRootPrimeKernel P V probes r t hrt Q h ξ i) L R a =
    physicalRootPrimeKernel (fun g => P (e.symm g)) (fun g => V (e.symm g))
      (fun g => probes (e.symm g)) (r.map e.toEmbedding) (t.map e.toEmbedding)
      ((Finset.disjoint_map e.toEmbedding).mpr hrt) Q h ξ
      (physicalRootPrimeGroupPattern e probes r t i) L R
      (physicalRootPrimeGroupOriginalAux e probes r t P i a) :=
  physical_group_reindexed_root_prime_kernel_of_maps e probes r t
    (r.map e.toEmbedding) (t.map e.toEmbedding)
    (by simp [Finset.map_map]) (by simp [Finset.map_map]) P V hrt
    ((Finset.disjoint_map e.toEmbedding).mpr hrt) Q h ξ i L R a

end Original
end Bounty

end


-- Source module: PhysicalRootAlternatingGroupReindex
section

/- The alternating adjoint convention of the actual residual survives
group reindexing without changing its outer pattern index. -/

open scoped Classical
namespace Bounty

theorem physical_group_reindexed_alternating_root_prime_kernel
    {G H : Type*} [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
    {J ell : ℕ} (e : G ≃ H) (P : G → Finset ℕ)
    (probes : G → Finset (Fin J)) (r t : Finset G)
    (V : G → ℝ) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ) (time : ℕ)
    (i : RepeatedBigPrimePatternIndex (ell := ell) probes r t)
    (L R : PhysicalMarkLists (fun g => P (e.symm g)) J ell)
    (a : PhysicalAuxLabels (fun g => P (e.symm g))
      (fun g => repeatedBigPrimePatternCut probes r t i (e.symm g))) :
    physicalGroupReindexedCoefficient e
      (repeatedBigPrimePatternCut probes r t i)
      (fun x y aux => if time % 2 = 0 then
        (starRingEnd ℂ) (physicalRootPrimeKernel P V probes r t hrt Q h ξ i y x aux)
        else physicalRootPrimeKernel P V probes r t hrt Q h ξ i x y aux) L R a =
    if time % 2 = 0 then
      (starRingEnd ℂ) (physicalRootPrimeKernel
        (fun g => P (e.symm g)) (fun g => V (e.symm g))
        (fun g => probes (e.symm g)) (r.map e.toEmbedding) (t.map e.toEmbedding)
        ((Finset.disjoint_map e.toEmbedding).mpr hrt) Q h ξ
        (physicalRootPrimeGroupPattern e probes r t i) R L
        (physicalRootPrimeGroupOriginalAux e probes r t P i a))
    else physicalRootPrimeKernel
      (fun g => P (e.symm g)) (fun g => V (e.symm g))
      (fun g => probes (e.symm g)) (r.map e.toEmbedding) (t.map e.toEmbedding)
      ((Finset.disjoint_map e.toEmbedding).mpr hrt) Q h ξ
      (physicalRootPrimeGroupPattern e probes r t i) L R
      (physicalRootPrimeGroupOriginalAux e probes r t P i a) := by
  by_cases ht : time % 2 = 0
  · simp only [ht, if_true]
    exact congrArg (starRingEnd ℂ)
      (physical_group_reindexed_root_prime_kernel_original e probes r t P V hrt Q h ξ i R L a)
  · simp only [ht, if_false]
    exact physical_group_reindexed_root_prime_kernel_original e probes r t P V hrt Q h ξ i L R a

end Bounty

end


-- Source module: PhysicalRootPrimeResidueReindex
section

/- The literal alternating prime-kernel residue model is unchanged by numbering
its groups and transporting its full pattern sum. -/

open Finset
open scoped Classical
namespace Bounty

theorem physical_root_prime_residue_model_group_reindex
    {G H : Type*} [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
    (e : G ≃ H) (P : G → Finset ℕ) (J ell : ℕ)
    [∀ p : PhysicalPrime P, NeZero p.2.val]
    [∀ p : PhysicalPrime (fun g => P (e.symm g)), NeZero p.2.val]
    (V : G → ℝ) (probes : G → Finset (Fin J)) (r t : Finset G)
    (hrt : Disjoint r t) (Q : ℕ) (h ξ q : ℝ)
    (ζ : ℕ → ℝ) (k : ℕ → ℤ) (n : ℕ) :
    physicalRootResidueModel V
        (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
        (repeatedBigPrimePatternCut probes r t) q
        (fun time _ => ζ time) (fun time _ => k time)
        (fun time i x y aux => if time % 2 = 0 then
          (starRingEnd ℂ) (physicalRootPrimeKernel P V probes r t hrt Q h ξ i y x aux)
          else physicalRootPrimeKernel P V probes r t hrt Q h ξ i x y aux) n =
      physicalRootResidueModel (fun g => V (e.symm g))
        (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell)
          (fun g => probes (e.symm g)) (r.map e.toEmbedding) (t.map e.toEmbedding)))
        (repeatedBigPrimePatternCut (fun g => probes (e.symm g))
          (r.map e.toEmbedding) (t.map e.toEmbedding)) q
        (fun time _ => ζ time) (fun time _ => k time)
        (fun time i x y aux => if time % 2 = 0 then
          (starRingEnd ℂ) (physicalRootPrimeKernel
            (fun g => P (e.symm g)) (fun g => V (e.symm g))
            (fun g => probes (e.symm g)) (r.map e.toEmbedding) (t.map e.toEmbedding)
            ((Finset.disjoint_map e.toEmbedding).mpr hrt) Q h ξ i y x aux)
          else physicalRootPrimeKernel
            (fun g => P (e.symm g)) (fun g => V (e.symm g))
            (fun g => probes (e.symm g)) (r.map e.toEmbedding) (t.map e.toEmbedding)
            ((Finset.disjoint_map e.toEmbedding).mpr hrt) Q h ξ i x y aux) n := by
  let C0 := repeatedBigPrimePatternCut (ell := ell) probes r t
  let C1 := repeatedBigPrimePatternCut (ell := ell) (fun g => probes (e.symm g))
    (r.map e.toEmbedding) (t.map e.toEmbedding)
  let K0 := fun (time : ℕ) (i : RepeatedBigPrimePatternIndex (ell := ell) probes r t)
      (x y : PhysicalMarkLists P J ell) (aux : PhysicalAuxLabels P (C0 i)) =>
    if time % 2 = 0 then
      (starRingEnd ℂ) (physicalRootPrimeKernel P V probes r t hrt Q h ξ i y x aux)
      else physicalRootPrimeKernel P V probes r t hrt Q h ξ i x y aux
  let K1 := fun (time : ℕ) (i : RepeatedBigPrimePatternIndex (ell := ell)
      (fun g => probes (e.symm g)) (r.map e.toEmbedding) (t.map e.toEmbedding))
      (x y : PhysicalMarkLists (fun g => P (e.symm g)) J ell)
      (aux : PhysicalAuxLabels (fun g => P (e.symm g)) (C1 i)) =>
    if time % 2 = 0 then
      (starRingEnd ℂ) (physicalRootPrimeKernel
        (fun g => P (e.symm g)) (fun g => V (e.symm g))
        (fun g => probes (e.symm g)) (r.map e.toEmbedding) (t.map e.toEmbedding)
        ((Finset.disjoint_map e.toEmbedding).mpr hrt) Q h ξ i y x aux)
      else physicalRootPrimeKernel
        (fun g => P (e.symm g)) (fun g => V (e.symm g))
        (fun g => probes (e.symm g)) (r.map e.toEmbedding) (t.map e.toEmbedding)
        ((Finset.disjoint_map e.toEmbedding).mpr hrt) Q h ξ i x y aux
  change physicalRootResidueModel V univ C0 q (fun time _ => ζ time)
    (fun time _ => k time) K0 n =
      physicalRootResidueModel (fun g => V (e.symm g)) univ C1 q
        (fun time _ => ζ time) (fun time _ => k time) K1 n
  rw [← physical_root_residue_model_group_reindex e P J ell V univ C0 q
    (fun time _ => ζ time) (fun time _ => k time) K0 n]
  symm
  apply physical_root_residue_model_pattern_equiv
    (physicalRootPrimeGroupPattern e probes r t) (fun g => P (e.symm g)) J ell
    (fun i g => C0 i (e.symm g)) C1
    (physical_root_prime_group_pattern_cut e probes r t)
    (fun g => V (e.symm g)) q
    (fun time _ => ζ time) (fun time _ => ζ time) (fun _ _ => rfl)
    (fun time _ => k time) (fun time _ => k time) (fun _ _ => rfl)
    (fun time i => physicalGroupReindexedCoefficient e (C0 i) (K0 time i)) K1
  intro time i x y aux
  have haux :
      physicalAuxCutEquiv (fun g => P (e.symm g))
        (fun g => C0 i (e.symm g))
        (C1 ((physicalRootPrimeGroupPattern e probes r t) i))
        (physical_root_prime_group_pattern_cut e probes r t i) aux =
      physicalRootPrimeGroupOriginalAux e probes r t P i aux := by
    funext g j
    rfl
  rw [haux]
  exact (physical_group_reindexed_alternating_root_prime_kernel
    e P probes r t V hrt Q h ξ time i x y aux).symm

theorem physical_root_prime_residue_model_finset_reindex
    (S : Finset ℕ) (P : S → Finset ℕ) (J ell : ℕ)
    [inst : ∀ p : PhysicalPrime P, NeZero p.2.val]
    (V : S → ℝ) (probes : S → Finset (Fin J)) (r t : Finset S)
    (hrt : Disjoint r t) (Q : ℕ) (h ξ q : ℝ)
    (ζ : ℕ → ℝ) (k : ℕ → ℤ) (n : ℕ) :
    let e : S ≃ Fin S.card := Fintype.equivFinOfCardEq (Fintype.card_coe S)
    letI : ∀ p : PhysicalPrime (fun g => P (e.symm g)), NeZero p.2.val :=
      fun p => inst ⟨e.symm p.1, p.2⟩
    physicalRootResidueModel V
        (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes r t))
        (repeatedBigPrimePatternCut probes r t) q
        (fun time _ => ζ time) (fun time _ => k time)
        (fun time i x y aux => if time % 2 = 0 then
          (starRingEnd ℂ) (physicalRootPrimeKernel P V probes r t hrt Q h ξ i y x aux)
          else physicalRootPrimeKernel P V probes r t hrt Q h ξ i x y aux) n =
      physicalRootResidueModel (fun g => V (e.symm g))
        (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell)
          (fun g => probes (e.symm g)) (r.map e.toEmbedding) (t.map e.toEmbedding)))
        (repeatedBigPrimePatternCut (fun g => probes (e.symm g))
          (r.map e.toEmbedding) (t.map e.toEmbedding)) q
        (fun time _ => ζ time) (fun time _ => k time)
        (fun time i x y aux => if time % 2 = 0 then
          (starRingEnd ℂ) (physicalRootPrimeKernel
            (fun g => P (e.symm g)) (fun g => V (e.symm g))
            (fun g => probes (e.symm g)) (r.map e.toEmbedding) (t.map e.toEmbedding)
            ((Finset.disjoint_map e.toEmbedding).mpr hrt) Q h ξ i y x aux)
          else physicalRootPrimeKernel
            (fun g => P (e.symm g)) (fun g => V (e.symm g))
            (fun g => probes (e.symm g)) (r.map e.toEmbedding) (t.map e.toEmbedding)
            ((Finset.disjoint_map e.toEmbedding).mpr hrt) Q h ξ i x y aux) n := by
  let e : S ≃ Fin S.card := Fintype.equivFinOfCardEq (Fintype.card_coe S)
  let : ∀ p : PhysicalPrime (fun g => P (e.symm g)), NeZero p.2.val :=
    fun p => inst ⟨e.symm p.1, p.2⟩
  exact physical_root_prime_residue_model_group_reindex e P J ell V probes r t hrt Q h ξ q ζ k n

end Bounty

end


-- Source module: PhysicalRootEndpointWeights
section

/- Exact normalized endpoint weights are positive and have group mass at most two. -/

open Finset
open scoped Classical
namespace Bounty

section Weights
variable {G : Type*} {P : G → Finset ℕ}
  (V : G → ℝ) (q : ℝ) (edges : ℕ)
  (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hV : ∀ g, 0 < V g)
  (hMass : ∀ g, ∑ p ∈ P g, 1 / (p : ℝ) = V g)
  (hsize : ∀ g (p : P g), 2 * (edges + 1) ≤ p.val)

include hq0 hq1 hV hsize

theorem physical_root_endpoint_weight_pos (g : G) (p : P g) :
    0 < ((p.val : ℝ) * physicalEndpointBaseline q edges p.val)⁻¹ / V g := by
  exact physical_endpoint_beta_pos V q edges hq0 hq1 g (hV g) p
    (by have := hsize g p; omega) (hsize g p)

include hMass

theorem physical_root_endpoint_weight_sum_bounds (g : G) :
    1 ≤ ∑ p : P g, ((p.val : ℝ) * physicalEndpointBaseline q edges p.val)⁻¹ / V g ∧
      (∑ p : P g, ((p.val : ℝ) * physicalEndpointBaseline q edges p.val)⁻¹ / V g) ≤ 2 := by
  exact physical_endpoint_beta_mass_bounds V q edges hq0 hq1 g (hV g) (hMass g)
    (fun p => by have := hsize g p; omega) (hsize g)

theorem physical_root_endpoint_weight_sum_le_two (g : G) :
    (∑ p : P g, ((p.val : ℝ) * physicalEndpointBaseline q edges p.val)⁻¹ / V g) ≤ 2 :=
  (physical_root_endpoint_weight_sum_bounds V q edges hq0 hq1 hV hMass hsize g).2

theorem physical_root_endpoint_weight_product_le_two_pow [Fintype G] (J ell : ℕ) :
    (∏ g, (∑ p : P g,
      ((p.val : ℝ) * physicalEndpointBaseline q edges p.val)⁻¹ / V g) ^ (J + ell)) ≤
      (2 : ℝ) ^ ((J + ell) * Fintype.card G) := by
  have hnonneg : ∀ g, 0 ≤ ∑ p : P g,
      ((p.val : ℝ) * physicalEndpointBaseline q edges p.val)⁻¹ / V g :=
    fun g => le_trans zero_le_one
      (physical_root_endpoint_weight_sum_bounds V q edges hq0 hq1 hV hMass hsize g).1
  calc
    _ ≤ ∏ _g : G, (2 : ℝ) ^ (J + ell) := by
      apply prod_le_prod₀
      · intro g _
        exact pow_nonneg (hnonneg g) _
      · intro g _
        exact pow_le_pow_left₀ (hnonneg g)
          (physical_root_endpoint_weight_sum_le_two V q edges hq0 hq1 hV hMass hsize g) _
    _ = (2 : ℝ) ^ ((J + ell) * Fintype.card G) := by
      rw [prod_const, card_univ, ← pow_mul]

end Weights
end Bounty

end


-- Source module: PhysicalRootBigSubsetPullback
section

/- Every subset of the selected big groups has an exact pullback to their finite index. -/

open Finset
open scoped Classical
namespace Bounty

section Pullback
variable {G H : Type*} [Fintype G] [Fintype H] [DecidableEq G]
  (groups : Finset G) (e : {g // g ∉ groupsᶜ} ≃ H)

theorem physical_reindexed_big_univ_map :
    (univ : Finset H).map (physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) e) =
      groups := by
  ext g
  constructor
  · intro hg
    obtain ⟨h, _, hh⟩ := mem_map.mp hg
    have hm : (e.symm h).val ∈ groups := by
      simpa only [mem_compl, not_not] using (e.symm h).property
    change (e.symm h).val = g at hh
    exact hh ▸ hm
  · intro hg
    let g' : {g // g ∉ groupsᶜ} := ⟨g, by simpa only [mem_compl, not_not] using hg⟩
    refine mem_map.mpr ⟨e g', mem_univ _, ?_⟩
    change (e.symm (e g')).val = g
    rw [e.symm_apply_apply]

theorem physical_reindexed_big_subsets_pullback
    (rN tN : Finset G) (hrN : rN ⊆ groups) (htN : tN ⊆ groups)
    (hrt : Disjoint rN tN) :
    ∃ r t : Finset H,
      r.map (physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) e) = rN ∧
      t.map (physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) e) = tN ∧
      r.card = rN.card ∧ t.card = tN.card ∧ Disjoint r t := by
  let f := physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) e
  have hu : (univ : Finset H).map f = groups := physical_reindexed_big_univ_map groups e
  have hr' : rN ⊆ (univ : Finset H).map f := by simpa only [hu] using hrN
  have ht' : tN ⊆ (univ : Finset H).map f := by simpa only [hu] using htN
  obtain ⟨r, _, hr⟩ := subset_map_iff.mp hr'
  obtain ⟨t, _, ht⟩ := subset_map_iff.mp ht'
  refine ⟨r, t, hr.symm, ht.symm, ?_, ?_, ?_⟩
  · rw [hr, card_map]
  · rw [ht, card_map]
  · apply (disjoint_map f).mp
    simpa only [← hr, ← ht] using hrt

end Pullback
end Bounty

end


-- Source module: RootGhostLowRank
section

/- The fixed damping and tilt also satisfy the ordinary low-rank birth inequality. -/

namespace Bounty

theorem physical_endpoint_half_low_rank_ghost_budgets {vmax : ℝ} (hvmax : 0 ≤ vmax)
    (edges : ℕ) :
    1 < 100*(vmax+1) ∧ ∀ j : ℕ,
      physicalEndpointSchedule (1/2) edges j/(9/10 : ℝ)^2 +
        ((1-physicalEndpointSchedule (1/2) edges j)/(9/10 : ℝ))/(100*(vmax+1)) ≤ 1 ∧
      ∀ V : ℝ, 0 ≤ V → V ≤ vmax →
        physicalEndpointSchedule (1/2) edges j/(9/10 : ℝ)^2 +
          (((1-physicalEndpointSchedule (1/2) edges j)*V)/(9/10 : ℝ))/(100*(vmax+1)) ≤ 1 := by
  obtain ⟨hu, h⟩ := physical_endpoint_half_ghost_budgets hvmax edges
  refine ⟨hu, fun j => ⟨(h j).1, ?_⟩⟩
  intro V hV0 hV
  have hhalf0 : 0 ≤ V/2 := by positivity
  have hhalf : V/2 ≤ vmax := by linarith
  have htwo : 2*(V/2) = V := by ring
  simpa only [htwo] using (h j).2 (V/2) hhalf0 hhalf

end Bounty

end


-- Source module: CandidateRootPrimeAvoidance
section

/- No candidate prime divides a nonzero original determinant shift once
the common large parameter is sufficiently large. -/

open Finset Filter
namespace Bounty

theorem eventually_candidate_root_prime_avoidance {scale K : ℝ}
    (hscale : 0 < scale) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop, ∀ i ∈ candidatePIndices scale L,
      ∀ p ∈ candidatePBand (scale * L) i,
      ∀ k ∈ Icc (-(typeIIAdmissibleDeterminantBound L K : ℤ))
        (typeIIAdmissibleDeterminantBound L K : ℤ),
      k ≠ 0 → ¬ (p : ℤ) ∣ k := by
  obtain ⟨v, V, _, _, hpools⟩ := exists_candidate_P_pool_bounds hscale
  filter_upwards [hpools, eventually_ge_atTop (3 : ℝ),
    eventually_mul_rpow_log_add_le_rpow (a := 0) (b := 1/10) (c := 1)
      (by norm_num) (by norm_num) zero_lt_one (K+88) (Real.log 3)] with L hpools hL hlog
  intro i hi p hp k hk hk0 hdiv
  have hL0 : 0 < L := by linarith
  have hprime := ((hpools.2.2.2.2.2 i hi).2.2 p hp).2.1
  have hexp : 3 * L ^ (K+88) ≤ Real.exp (L ^ (1/10 : ℝ)) := by
    calc
      _ = Real.exp ((K+88)*Real.log L+Real.log 3) := by
        rw [Real.exp_add, mul_comm (K+88) (Real.log L), ← Real.rpow_def_of_pos hL0, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by
        simpa only [Real.rpow_zero, mul_one, one_mul] using hlog)
  have hdet := determinant_bound_le_three_rpow_public (by linarith : 1 ≤ L) hK
  have hkdet : |(k : ℝ)| ≤ (typeIIAdmissibleDeterminantBound L K : ℝ) := by
    apply abs_le.mpr
    constructor
    · exact_mod_cast (mem_Icc.mp hk).1
    · exact_mod_cast (mem_Icc.mp hk).2
  have hkprime : |(k : ℝ)| < (p : ℝ) := hkdet.trans_lt ((hdet.trans hexp).trans_lt hprime)
  have hkprimeZ : |k| < (p : ℤ) := by exact_mod_cast hkprime
  have hpdvd : (p : ℤ) ∣ |k| := (dvd_abs (p : ℤ) k).mpr hdiv
  exact (not_le_of_gt hkprimeZ) (Int.le_of_dvd (abs_pos.mpr hk0) hpdvd)

end Bounty

end


-- Source module: RootBirthRarityGap
section

/- A fixed exponential prime-atom bound absorbs the square of the actual
polynomial birth dimension with a smaller stretched-exponential exponent. -/

open Filter
namespace Bounty

theorem eventually_root_birth_rarity_gap (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℕ, (m : ℝ) ≤ L ^ 6 →
      ∀ β : ℝ, 0 ≤ β → β ≤ C * Real.exp (-(L ^ (3/10 : ℝ))) →
        (m : ℝ) ^ 2 * β ≤ Real.exp (-(L ^ (1/4 : ℝ))) := by
  let D := max C 1
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right C 1)
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_mul_rpow_log_add_le_rpow (a := 0) (b := 1/4) (c := 1)
      (by norm_num) (by norm_num) zero_lt_one 12 (Real.log D),
    eventually_mul_rpow_add_le_mul_rpow (a := 1/4) (b := 3/10) (c := 1)
      (by norm_num) (by norm_num) zero_lt_one 2 0] with L hL hlog hpower
  simp only [Real.rpow_zero, mul_one, one_mul] at hlog
  simp only [add_zero, one_mul] at hpower
  have hexp : D * L ^ 12 * Real.exp (-(L ^ (3/10 : ℝ))) ≤
      Real.exp (-(L ^ (1/4 : ℝ))) := by
    have he : Real.exp (Real.log D + 12 * Real.log L - L ^ (3/10 : ℝ)) =
        D * L ^ 12 * Real.exp (-(L ^ (3/10 : ℝ))) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_log hD]
      congr 2
      rw [show (12 : ℝ) = (12 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log hL]
    rw [← he]
    exact Real.exp_le_exp.mpr (by linarith)
  intro m hm β hβ hβC
  have hm2 : (m : ℝ) ^ 2 ≤ L ^ 12 := by
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg m) hm 2
    simpa only [← pow_mul] using hp
  have hβD : β ≤ D * Real.exp (-(L ^ (3/10 : ℝ))) :=
    hβC.trans (mul_le_mul_of_nonneg_right (le_max_left C 1) (Real.exp_pos _).le)
  calc
    _ ≤ L ^ 12 * β := mul_le_mul_of_nonneg_right hm2 hβ
    _ ≤ L ^ 12 * (D * Real.exp (-(L ^ (3/10 : ℝ)))) :=
      mul_le_mul_of_nonneg_left hβD (pow_nonneg hL.le _)
    _ = D * L ^ 12 * Real.exp (-(L ^ (3/10 : ℝ))) := by ring
    _ ≤ _ := hexp

end Bounty

end


-- Source module: PhysicalSelectedBirthCount
section

/- The actual selected-word birth allocation has polynomial dimension
when its cap, slot count, group count, and edge count do. -/

open scoped Classical
namespace Bounty

theorem physical_selected_birth_card_polynomial
    (M T B N : ℕ) {L : ℝ} (hL : 4 ≤ L)
    (hM : (M : ℝ) ≤ L) (hT : (T : ℝ) ≤ L)
    (hB : (B : ℝ) ≤ L ^ 2) (hN : (N : ℝ) ≤ L) :
    (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => T) B
      ((List.range (4 * N + 1)).map (physicalSelectedFineTag N))) : ℝ) ≤ L ^ 6 := by
  have hL0 : 0 ≤ L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hLL : L ≤ L ^ 2 := by nlinarith
  have hmax : max (B : ℝ) (T : ℝ) ≤ L ^ 2 := max_le hB (hT.trans hLL)
  have hc := full_mixed_common_birth_card_le (fun _ : Fin M => T) B T
    (fun _ => le_rfl) ((List.range (4 * N + 1)).map (physicalSelectedFineTag N))
  simp only [List.length_map, List.length_range] at hc
  have hc' : (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => T) B
      ((List.range (4 * N + 1)).map (physicalSelectedFineTag N))) : ℝ) ≤
      (M : ℝ) * T + (4 * (N : ℝ) + 1) * ((M : ℝ) * max (B : ℝ) (T : ℝ)) := by
    exact_mod_cast hc
  have hprod : (M : ℝ) * T ≤ L * L :=
    mul_le_mul hM hT (Nat.cast_nonneg _) hL0
  have hfac : (M : ℝ) * max (B : ℝ) (T : ℝ) ≤ L * L ^ 2 :=
    mul_le_mul hM hmax (le_max_of_le_left (Nat.cast_nonneg _)) hL0
  have hlen : 4 * (N : ℝ) + 1 ≤ 5 * L := by linarith
  have hterm : (4 * (N : ℝ) + 1) * ((M : ℝ) * max (B : ℝ) (T : ℝ)) ≤
      (5 * L) * (L * L ^ 2) :=
    mul_le_mul hlen hfac (mul_nonneg (Nat.cast_nonneg _)
      (le_max_of_le_left (Nat.cast_nonneg _))) (by positivity)
  have h24 : L ^ 2 ≤ L ^ 4 := by
    calc
      L ^ 2 = 1 * L ^ 2 := by ring
      _ ≤ L ^ 2 * L ^ 2 := mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg L)
      _ = L ^ 4 := by ring
  have h46 : 6 * L ^ 4 ≤ L ^ 6 := by
    calc
      _ ≤ L ^ 2 * L ^ 4 := mul_le_mul_of_nonneg_right (by nlinarith) (pow_nonneg hL0 4)
      _ = _ := by ring
  exact hc'.trans ((add_le_add hprod hterm).trans (by nlinarith))

end Bounty

end


-- Source module: PhysicalSelectedBirthAsymptotics
section

/- The literal moment schedule and a linear working cap have polynomially
many common birth addresses, uniformly over logarithmically many groups. -/

open Filter
namespace Bounty

theorem eventually_physical_selected_birth_card_polynomial (T : ℕ) (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ M N B : ℕ,
      (M : ℝ) ≤ C * Real.log L →
      (N : ℝ) ≤ 2 * (Nat.ceil (L ^ (13/25 : ℝ)) : ℝ) + 1 →
      (B : ℝ) ≤ L ^ 2 →
      (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => T) B
        ((List.range (4 * N + 1)).map (physicalSelectedFineTag N))) : ℝ) ≤ L ^ 6 := by
  filter_upwards [eventually_ge_atTop (4 : ℝ), eventually_ge_atTop (T : ℝ),
    eventually_log_times_rpow_lt (a := 0) (b := 1) zero_lt_one C,
    eventually_repeated_big_visit_density_le (alpha := 13/25) (tau := 1)
      zero_lt_one (by norm_num)] with L hL hT hgroups hedges
  intro M N B hM hN hB
  have hM' : C * Real.log L < L := by
    simpa only [Real.rpow_zero, Real.rpow_one, mul_one] using hgroups
  have hN' : (N : ℝ) ≤ L := by
    simpa only [Real.rpow_one] using hedges N hN
  exact physical_selected_birth_card_polynomial M T B N hL (hM.trans hM'.le) hT hB hN'

theorem eventually_root_birth_card_linear_cap (J ell : ℕ) (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ M : ℕ, (M : ℝ) ≤ C * Real.log L →
      (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) (Nat.ceil L)
        ((List.range (4 * (2 * Nat.ceil (L ^ (13/25 : ℝ))) + 1)).map
          (physicalSelectedFineTag (2 * Nat.ceil (L ^ (13/25 : ℝ)))))) : ℝ) ≤ L ^ 6 := by
  filter_upwards [eventually_physical_selected_birth_card_polynomial (J + ell) C,
    eventually_ge_atTop (4 : ℝ)] with L hcount hL
  intro M hM
  apply hcount M (2 * Nat.ceil (L ^ (13/25 : ℝ))) (Nat.ceil L) hM
  · push_cast
    linarith
  · have hceil := Nat.ceil_lt_add_one (by linarith : 0 ≤ L)
    nlinarith

end Bounty

end


-- Source module: CandidateRootBirthRarity
section

/- Actual candidate root atoms and the original endpoint schedule supply
one common rarity parameter, including the required forest dimension loss. -/

open Filter
namespace Bounty

theorem eventually_candidate_root_birth_rarity
    {scale q vmin vmax ρ v : ℝ} (hscale : 0 < scale) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hvmin : 0 < vmin) (hρ : 0 < ρ) (hv : 0 ≤ v)
    (J ell : ℕ) (C : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      let η := (2 / vmin) * Real.exp (-(L ^ (3/10 : ℝ)))
      let β := max (2 / vmin) (2 * vmax * v / (ρ * vmin)) *
        Real.exp (-(L ^ (3/10 : ℝ)))
      0 < η ∧ η ≤ β ∧ 0 < β ∧
        (∀ i ∈ candidateBigPIndices scale L, ∀ p ∈ candidatePBand (scale * L) i,
          ∀ V : ℝ, vmin ≤ V →
            ((p : ℝ) * physicalEndpointBaseline q (2 * Nat.ceil (L ^ (13/25 : ℝ))) p)⁻¹ / V ≤ η) ∧
        (∀ j : ℕ, ∀ V : ℝ, vmin ≤ V → V ≤ vmax →
          |(1 - physicalEndpointSchedule q (2 * Nat.ceil (L ^ (13/25 : ℝ))) j) * V / ρ| * η * v ≤ β) ∧
        ∀ M : ℕ, (M : ℝ) ≤ C * Real.log L →
          (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) (Nat.ceil L)
            ((List.range (4 * (2 * Nat.ceil (L ^ (13/25 : ℝ))) + 1)).map
              (physicalSelectedFineTag (2 * Nat.ceil (L ^ (13/25 : ℝ)))))) : ℝ) ^ 2 * β ≤
            Real.exp (-(L ^ (1/4 : ℝ))) := by
  filter_upwards [eventually_candidate_root_birth_atoms hscale hq0 hq1 hvmin,
    eventually_root_birth_card_linear_cap J ell C,
    eventually_root_birth_rarity_gap (max (2 / vmin) (2 * vmax * v / (ρ * vmin)))]
    with L hatom hcount hgap
  intro η β
  have hb := root_birth_rarity_envelope_bounds (L := L) (vmax := vmax) hvmin hρ hv
  refine ⟨hb.1, hb.2.1, hb.2.2.1, hatom, ?_, ?_⟩
  · intro j V hVmin hVmax
    have hqj := physical_endpoint_schedule_unit hq0 hq1 (2 * Nat.ceil (L ^ (13/25 : ℝ))) j
    exact hb.2.2.2 _ V hqj.1 hqj.2 hVmin hVmax
  · intro M hM
    exact hgap _ (hcount M hM) β hb.2.2.1.le le_rfl

end Bounty

end
