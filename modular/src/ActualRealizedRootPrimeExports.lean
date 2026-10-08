import ActualAnalyticExports

/-! Actual realized candidate norms and original root Fourier edge costs. -/

section

/- Actual zero-free signed prime norm exports, with one coherent aggregate dependency. -/

section

/- Aggregate-compatible signed-prime helper overlay. -/

open scoped Topology BigOperators Classical

-- Original module: PhysicalMixedNormConjugation

/- Conjugation preserves the real weighted norm and pending symmetry,
and commutes with the exact joint endpoint average. -/

open Finset
open scoped Classical

namespace Bounty

theorem clean_active_norm_conj {X : Type*} [Fintype X]
    (w : X → ℝ) (f : X → ℂ) :
    cleanActiveNorm w (fun x => (starRingEnd ℂ) (f x)) = cleanActiveNorm w f := by
  simp only [cleanActiveNorm, starRingEnd_apply, norm_star]

theorem physical_small_big_joint_average_conj
    {S G : Type*} [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
    {Ps : S → Finset ℕ} {P Z : G → Type*} {J ell : ℕ} {M : G → ℕ} {B : ℕ}
    (f : PhysicalSmallBigState Ps J ell (ProductBoundedOrderedState P Z M B) → ℂ) :
    physicalSmallBigJointAverage (fun x => (starRingEnd ℂ) (f x)) =
      fun x => (starRingEnd ℂ) (physicalSmallBigJointAverage f x) := by
  funext s
  rw [physical_small_big_joint_average_eq_sum, physical_small_big_joint_average_eq_sum]
  simp only [map_sum, map_mul, Complex.conj_ofReal]

theorem product_memory_symmetric_conj
    {G : Type*} [DecidableEq G] {P Z : G → Type*} {M : G → ℕ} {B : ℕ}
    (f : ProductBoundedOrderedState P Z M B → ℂ) (hf : ProductMemorySymmetric f) :
    ProductMemorySymmetric (fun x => (starRingEnd ℂ) (f x)) := by
  intro x g τ
  exact congrArg (starRingEnd ℂ) (hf x g τ)

end Bounty


-- Original module: PhysicalMixedSignedPrimeAction

/- The chronological prime family retains the conjugated, endpoint-swapped
kernel at even times. The supplied displacement and residual are unchanged. -/

open Finset
open scoped Classical

namespace Bounty

section
variable {S G : Type} [Fintype S] [Fintype G] [DecidableEq G]
  {Ps : S → Finset ℕ} {P : G → Finset ℕ} {J ell B : ℕ}

noncomputable def physicalMixedSignedPrimePatternAction
    (V : G → ℝ) (baseline : ∀ g, P g → ℝ) (ρ : ℝ) (Vs : S → ℝ) (q : ℝ)
    (probes : G → Finset (Fin J)) (r t : Finset G) (hrt : Disjoint r t)
    (Q : ℕ) (h ξ : ℝ) (time : ℕ) (k : ℤ) (initial : ∀ g, Finset (P g))
    (φ : ∀ i : RepeatedBigPrimePatternIndex (ell := ell) probes r t,
      ∀ a (s : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B)),
        PhysicalMixedCoefficientEvent (repeatedBigPrimePatternCut probes r t i) k a s → ℂ)
    (f : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B) → ℂ) :=
  let kept := fun U : Finset (RepeatedBigFlatIndex G J ell) => primeProductRetainedCells
    (fun j : U => P j.val.1) (fun j => V j.val.1) h ξ
  ∑ i : RepeatedBigPrimePatternIndex (ell := ell) probes r t,
    physicalMixedCoefficientAction (repeatedBigPrimePatternCut probes r t i) k V baseline ρ Vs q initial
      (fun a s e =>
        (if time % 2 = 0 then
          (starRingEnd ℂ) (repeatedBigPrimePatternWeight probes r t i *
            repeatedBigPrimePatternKernel P V probes r t hrt Q h kept i
              (physicalMixedRepeatedLabels (repeatedBigPrimePatternCut probes r t i)
                (physicalMixedCoefficientTarget (repeatedBigPrimePatternCut probes r t i) k a s e).2)
              (physicalMixedRepeatedLabels (repeatedBigPrimePatternCut probes r t i) s.2) a)
        else repeatedBigPrimePatternWeight probes r t i *
          repeatedBigPrimePatternKernel P V probes r t hrt Q h kept i
            (physicalMixedRepeatedLabels (repeatedBigPrimePatternCut probes r t i) s.2)
            (physicalMixedRepeatedLabels (repeatedBigPrimePatternCut probes r t i)
              (physicalMixedCoefficientTarget (repeatedBigPrimePatternCut probes r t i) k a s e).2) a) *
        φ i a s e) f

theorem physical_mixed_signed_prime_pattern_action_of_odd
    (V : G → ℝ) (baseline : ∀ g, P g → ℝ) (ρ : ℝ) (Vs : S → ℝ) (q : ℝ)
    (probes : G → Finset (Fin J)) (r t : Finset G) (hrt : Disjoint r t)
    (Q : ℕ) (h ξ : ℝ) (time : ℕ) (htime : time % 2 ≠ 0)
    (k : ℤ) (initial : ∀ g, Finset (P g))
    (φ : ∀ i : RepeatedBigPrimePatternIndex (ell := ell) probes r t,
      ∀ a (s : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B)),
        PhysicalMixedCoefficientEvent (repeatedBigPrimePatternCut probes r t i) k a s → ℂ)
    (f : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B) → ℂ) :
    physicalMixedSignedPrimePatternAction V baseline ρ Vs q probes r t hrt Q h ξ time k initial φ f =
      physicalMixedPrimePatternAction V baseline ρ Vs q probes r t hrt Q h ξ k initial φ f := by
  simp only [physicalMixedSignedPrimePatternAction, if_neg htime, physicalMixedPrimePatternAction]

theorem physical_mixed_signed_prime_pattern_action_of_even
    (V : G → ℝ) (baseline : ∀ g, P g → ℝ) (ρ : ℝ) (Vs : S → ℝ) (q : ℝ)
    (probes : G → Finset (Fin J)) (r t : Finset G) (hrt : Disjoint r t)
    (Q : ℕ) (h ξ : ℝ) (time : ℕ) (htime : time % 2 = 0)
    (k : ℤ) (initial : ∀ g, Finset (P g))
    (φ : ∀ i : RepeatedBigPrimePatternIndex (ell := ell) probes r t,
      ∀ a (s : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B)),
        PhysicalMixedCoefficientEvent (repeatedBigPrimePatternCut probes r t i) k a s → ℂ)
    (f : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B) → ℂ) :
    physicalMixedSignedPrimePatternAction V baseline ρ Vs q probes r t hrt Q h ξ time k initial φ f =
      let kept := fun U : Finset (RepeatedBigFlatIndex G J ell) => primeProductRetainedCells
        (fun j : U => P j.val.1) (fun j => V j.val.1) h ξ
      ∑ i : RepeatedBigPrimePatternIndex (ell := ell) probes r t,
        physicalMixedCoefficientAction (repeatedBigPrimePatternCut probes r t i) k V baseline ρ Vs q initial
          (fun a s e =>
            (starRingEnd ℂ) (repeatedBigPrimePatternWeight probes r t i *
              repeatedBigPrimePatternKernel P V probes r t hrt Q h kept i
                (physicalMixedRepeatedLabels (repeatedBigPrimePatternCut probes r t i)
                  (physicalMixedCoefficientTarget (repeatedBigPrimePatternCut probes r t i) k a s e).2)
                (physicalMixedRepeatedLabels (repeatedBigPrimePatternCut probes r t i) s.2) a) *
            φ i a s e) f := by
  simp only [physicalMixedSignedPrimePatternAction, if_pos htime]

end
end Bounty


-- Original module: PhysicalMixedSignedPrimeNorm

/- A uniform projected norm bound for the signed prime family in both time
parities. The original auxiliary law, initial exclusion and two endpoint
averages are retained. -/

open Finset
open scoped Classical

namespace Bounty

theorem exists_physical_mixed_signed_prime_pattern_projected_norm_bound
    {q vs : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hvs : 0 < vs) (ell : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (S G : Type) [Fintype S] [DecidableEq S]
      [Fintype G] [DecidableEq G] (Ps : S → Finset ℕ)
      [∀ p : PhysicalPrime Ps, NeZero p.2.val] (P : G → Finset ℕ)
      [∀ g (p : P g), NeZero p.val] (J B m : ℕ)
      (V : G → ℝ) (baseline : ∀ g, P g → ℝ) (ρ : ℝ) (Vs : S → ℝ)
      (probes : G → Finset (Fin J)) (r t : Finset G) (hrt : Disjoint r t),
      (∀ g, (probes g).card ≤ m) → ∀ (Q : ℕ) (h ξ : ℝ), 0 < ξ →
      ∀ (time : ℕ) (k : ℤ) (initial : ∀ g, Finset (P g)), (∀ s, vs ≤ Vs s) →
      (∀ g, ∑ p ∈ P g, 1 / (p : ℝ) = V g) →
      (∀ g p, 1 / 2 ≤ baseline g p ∧ baseline g p ≤ 1) →
      ∀ (v vmin vmax : ℝ), 0 < ρ → ρ < 1 → 1 < v → 0 < vmin →
      (∀ g, vmin ≤ V g) → (∀ g, V g ≤ vmax) →
      ∀ (φ : ∀ i : RepeatedBigPrimePatternIndex (ell := ell) probes r t,
        ∀ a (s : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B)),
          PhysicalMixedCoefficientEvent (repeatedBigPrimePatternCut probes r t i) k a s → ℂ),
      (∀ i a s e, ‖φ i a s e‖ ≤ 1) →
      ∀ f : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B) → ℂ,
      (∀ s, ProductMemorySymmetric (fun x => f (s,x))) →
      let μ := fun g => tiltedPhysicalBirthLaw V g (baseline g)
      let W := productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g))
      cleanActiveNorm (physicalSmallBigMeasure Vs W)
        (physicalSmallBigJointAverage (physicalMixedSignedPrimePatternAction V baseline ρ Vs q
          probes r t hrt Q h ξ time k initial φ (physicalSmallBigJointAverage f))) ≤
      repeatedBigFamilyEnvelope (Fintype.card G) m Q ξ * A ^ Fintype.card S *
        Real.sqrt (unrestrictedEdgeEnergyBound ρ v vmin vmax (ell + m) ^ Fintype.card G) *
          cleanActiveNorm (physicalSmallBigMeasure Vs W) f := by
  obtain ⟨A, hA, hbound⟩ := exists_physical_mixed_coefficient_projected_norm_bound hq0 hq1 hvs ell
  refine ⟨A, hA, ?_⟩
  intro S G _ dS _ dG
  cases Subsingleton.elim dS (Classical.typeDecidableEq S)
  cases Subsingleton.elim dG (Classical.typeDecidableEq G)
  intro Ps _ P _ J B m V baseline ρ Vs probes r t hrt hp Q h ξ hξ time k initial hVs hMass hbaseline
    v vmin vmax hρ0 hρ1 hv hvmin hVlo hVhi φ hφ f hf μ W
  let C := repeatedBigPrimePatternCut (ell := ell) probes r t
  let kept := fun U : Finset (RepeatedBigFlatIndex G J ell) => primeProductRetainedCells
    (fun j : U => P j.val.1) (fun j => V j.val.1) h ξ
  let K := repeatedBigPrimePatternKernel P V probes r t hrt Q h kept
  let b := repeatedBigPrimePatternBound (ell := ell) probes r t Q ξ
  let Ψ := fun i a s (e : PhysicalMixedCoefficientEvent (B := B) (C i) k a s) =>
    (if time % 2 = 0 then
      (starRingEnd ℂ) (repeatedBigPrimePatternWeight probes r t i * K i
        (physicalMixedRepeatedLabels (C i) (physicalMixedCoefficientTarget (C i) k a s e).2)
        (physicalMixedRepeatedLabels (C i) s.2) a)
    else repeatedBigPrimePatternWeight probes r t i * K i
      (physicalMixedRepeatedLabels (C i) s.2)
      (physicalMixedRepeatedLabels (C i) (physicalMixedCoefficientTarget (C i) k a s e).2) a) *
      φ i a s e
  have hb : ∀ i, 0 ≤ b i := repeated_big_prime_pattern_bound_nonneg probes r t Q ξ
  have hΨ : ∀ i a s e, ‖Ψ i a s e‖ ≤ b i := by
    intro i a s e
    dsimp only [Ψ]
    split_ifs
    · rw [norm_mul, starRingEnd_apply, norm_star, norm_mul,
        repeated_big_prime_pattern_weight_norm, one_mul]
      exact (mul_le_mul_of_nonneg_right
        (repeated_big_prime_pattern_kernel_norm_le P V probes r t hrt Q h ξ hξ i _ _ a)
        (norm_nonneg _)).trans
          ((mul_le_mul_of_nonneg_left (hφ i a s e) (hb i)).trans_eq (mul_one _))
    · rw [norm_mul, norm_mul, repeated_big_prime_pattern_weight_norm, one_mul]
      exact (mul_le_mul_of_nonneg_right
        (repeated_big_prime_pattern_kernel_norm_le P V probes r t hrt Q h ξ hξ i _ _ a)
        (norm_nonneg _)).trans
          ((mul_le_mul_of_nonneg_left (hφ i a s e) (hb i)).trans_eq (mul_one _))
  have hsum : ∑ i, b i ≤ repeatedBigFamilyEnvelope (Fintype.card G) m Q ξ := by
    apply (repeated_big_prime_pattern_bound_sum_le (ell := ell) probes r t hp Q ξ).trans
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    apply Nat.mul_le_mul_left
    rw [← card_union_of_disjoint hrt]
    exact card_le_univ _
  have hμ : ∀ g p, 0 ≤ μ g p := fun g p =>
    tiltedPhysicalBirthLaw_nonneg V g (baseline g) (hvmin.trans_le (hVlo g)).le
      (fun p => (by norm_num : (0 : ℝ) ≤ 1/2).trans (hbaseline g p).1) p
  have hW : ∀ x, 0 ≤ W x := productMemoryWeight_nonneg μ _ hμ (fun g z => hμ g z.1)
  let u := fun i => physicalSmallBigJointAverage
    (physicalMixedCoefficientAction (C i) k V baseline ρ Vs q initial (Ψ i)
      (physicalSmallBigJointAverage f))
  have heq : physicalSmallBigJointAverage (physicalMixedSignedPrimePatternAction V baseline ρ Vs q
      probes r t hrt Q h ξ time k initial φ (physicalSmallBigJointAverage f)) = ∑ i, u i :=
    physical_small_big_joint_average_sum _
  calc
    _ = cleanActiveNorm (physicalSmallBigMeasure Vs W) (∑ i, u i) := by
      congr 1
    _ ≤ ∑ i, cleanActiveNorm (physicalSmallBigMeasure Vs W) (u i) :=
      clean_active_norm_sum_le _
        (physical_small_big_measure_nonneg Vs (fun s => hvs.trans_le (hVs s)) W hW) univ u
    _ ≤ ∑ i, b i * A ^ Fintype.card S *
        Real.sqrt (unrestrictedEdgeEnergyBound ρ v vmin vmax (ell + m) ^ Fintype.card G) *
        cleanActiveNorm (physicalSmallBigMeasure Vs W) f := by
      apply sum_le_sum
      intro i _
      exact hbound S G Ps P J B (C i) k V baseline ρ Vs initial hVs hMass hbaseline
        v vmin vmax hρ0 hρ1 hv hvmin hVlo hVhi (ell+m)
        (fun g => Nat.add_le_add_left (repeated_big_prime_pattern_cut_card_le probes r t hp i g) ell)
        (Ψ i) (b i) (hb i) (hΨ i) f hf
    _ = (∑ i, b i) * A ^ Fintype.card S *
        Real.sqrt (unrestrictedEdgeEnergyBound ρ v vmin vmax (ell + m) ^ Fintype.card G) *
        cleanActiveNorm (physicalSmallBigMeasure Vs W) f := by rw [sum_mul, sum_mul, sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsum (pow_nonneg (zero_le_one.trans hA) _))
        (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

end Bounty


-- Original module: PhysicalMixedSignedPrimeSymmetry

/- Pending-memory symmetry for both chronological prime-kernel orientations.
The event factor must be invariant under the actual memory-event reindexing. -/

open Finset Classical
namespace Bounty
section
variable {S G : Type} [Fintype S] [Fintype G] [dG : DecidableEq G]
  {Ps : S → Finset ℕ} {P : G → Finset ℕ}
  [∀ g (p : P g), NeZero p.val] {J ell B : ℕ}

theorem physical_mixed_signed_prime_pattern_memory_symmetric
    (V : G → ℝ) (baseline : ∀ g, P g → ℝ) (ρ : ℝ) (Vs : S → ℝ) (q : ℝ)
    (probes : G → Finset (Fin J)) (r t : Finset G) (hrt : Disjoint r t)
    (Q : ℕ) (h ξ : ℝ) (time : ℕ) (k : ℤ) (initial : ∀ g, Finset (P g))
    (φ : ∀ i : RepeatedBigPrimePatternIndex (ell := ell) probes r t,
      ∀ a (s : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B)),
        PhysicalMixedCoefficientEvent (repeatedBigPrimePatternCut probes r t i) k a s → ℂ)
    (hφ : ∀ i a (s : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B))
      (τ : ∀ g, Equiv.Perm (Fin (s.2 g).2.1.val))
      (e : PhysicalMixedCoefficientEvent (repeatedBigPrimePatternCut probes r t i) k a s),
      φ i a (s.1, productMemoryReindex s.2 τ)
        (physicalMixedCoefficientReindex (repeatedBigPrimePatternCut probes r t i) k a s τ e) = φ i a s e)
    (f : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B) → ℂ)
    (hf : ∀ s, ProductMemorySymmetric (fun x => f (s,x))) :
    ∀ s, ProductMemorySymmetric (fun x =>
      physicalMixedSignedPrimePatternAction V baseline ρ Vs q probes r t hrt Q h ξ time k initial φ f (s,x)) := by
  cases Subsingleton.elim dG (Classical.typeDecidableEq G)
  intro s x g τ
  unfold physicalMixedSignedPrimePatternAction
  simp only [Finset.sum_apply]
  apply sum_congr rfl
  intro i _
  apply physical_mixed_coefficient_signed_memory_symmetric _ _ _ _ _ _ _ _ _ _ f hf s x g τ
  intro a y σ e
  rw [physical_mixed_target_labels_reindex, hφ i a y σ e]
  rfl

variable [DecidableEq S]

theorem physical_mixed_signed_prime_concrete_birth_projected_memory_symmetric
    (V : G → ℝ) (baseline : ∀ g, P g → ℝ) (ρ : ℝ) (Vs : S → ℝ) (q : ℝ)
    (probes : G → Finset (Fin J)) (r t : Finset G) (hrt : Disjoint r t)
    (Q : ℕ) (h ξ ζ θ : ℝ) (time : ℕ) (k : ℤ) (initial : ∀ g, Finset (P g)) (Fs : ∀ g, Finset (Ps g))
    (Φ : ∀ i : RepeatedBigPrimePatternIndex (ell := ell) probes r t,
      PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t i) →
      PhysicalBareResidueState Ps J ell → PhysicalBareResidueState Ps J ell →
      (∀ g, Fin (J + ell) → P g) → (∀ g, Fin (J + ell) → P g) →
      (∀ g, EdgeDrawObservation (P g)
        (physicalFullSharedIndices (ell := ell) (repeatedBigPrimePatternCut probes r t i g))ᶜ.card) → ℂ)
    (f : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B) → ℂ)
    (hf : ∀ s, ProductMemorySymmetric (fun x => f (s,x))) :
    ∀ s, ProductMemorySymmetric (fun x => physicalSmallBigJointAverage
      (physicalMixedSignedPrimePatternAction V baseline ρ Vs q probes r t hrt Q h ξ time k initial
        (fun i a y e => physicalMixedFullResidualPhase (repeatedBigPrimePatternCut probes r t i) ζ θ k
          cleanMixedSourceGate (cleanMixedTargetGate Fs) a y e *
          physicalMixedCoefficientObservablePhase (repeatedBigPrimePatternCut probes r t i) k a (Φ i a) y e)
        (physicalSmallBigJointAverage f)) (s,x)) := by
  apply physical_small_big_joint_average_memory_symmetric
  apply physical_mixed_signed_prime_pattern_memory_symmetric
  · intro i a y σ e
    exact congrArg₂ (fun u v : ℂ => u * v)
      (physical_mixed_concrete_residual_reindex _ ζ θ k Fs a y σ e)
      (physical_mixed_coefficient_observable_reindex _ k a (Φ i a) y σ e)
  · exact physical_small_big_joint_average_memory_symmetric f hf

end
end Bounty


-- Original module: PhysicalMixedCutTransport

/- Exact transport of mixed coefficient rows along equality of their cuts.
The original auxiliary labels, events, and arbitrary decorations are retained. -/

open Finset
open scoped Classical

namespace Bounty

section
variable {S G : Type} [Fintype S] [Fintype G] [DecidableEq G]
  {Ps : S → Finset ℕ} {P : G → Finset ℕ} {J ell B : ℕ}
  {C D : G → Finset (Fin J)}

def physicalAuxCutTransport (h : C = D) (a : PhysicalAuxLabels P C) :
    PhysicalAuxLabels P D := h ▸ a

def physicalMixedEventCutTransport (h : C = D) (k : ℤ)
    {a : PhysicalAuxLabels P C}
    {s : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B)}
    (e : PhysicalMixedCoefficientEvent C k a s) :
    PhysicalMixedCoefficientEvent D k (physicalAuxCutTransport h a) s := by
  subst D
  exact e

def physicalMixedPhaseCutTransport (h : C = D) (k : ℤ)
    (φ : ∀ a (s : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B)),
      PhysicalMixedCoefficientEvent C k a s → ℂ) :
    ∀ a (s : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B)),
      PhysicalMixedCoefficientEvent D k a s → ℂ := h ▸ φ

omit [Fintype G] [DecidableEq G] in
theorem physical_aux_cut_transport_apply (h : C = D) (a : PhysicalAuxLabels P C)
    (g : G) (j : D g) :
    physicalAuxCutTransport h a g j = a g ⟨j.val, by rw [h]; exact j.property⟩ := by
  subst D
  rfl

omit [DecidableEq G] in
theorem physical_mixed_phase_cut_transport_apply (h : C = D) (k : ℤ)
    (φ : ∀ a (s : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B)),
      PhysicalMixedCoefficientEvent C k a s → ℂ)
    (a : PhysicalAuxLabels P C)
    (s : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B))
    (e : PhysicalMixedCoefficientEvent C k a s) :
    physicalMixedPhaseCutTransport h k φ (physicalAuxCutTransport h a) s
      (physicalMixedEventCutTransport h k e) = φ a s e := by
  subst D
  rfl

omit [DecidableEq G] in
theorem physical_mixed_phase_cut_transport_apply_reverse (h : C = D) (k : ℤ)
    (φ : ∀ a (s : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B)),
      PhysicalMixedCoefficientEvent C k a s → ℂ)
    (a : PhysicalAuxLabels P D)
    (s : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B))
    (e : PhysicalMixedCoefficientEvent D k a s) :
    physicalMixedPhaseCutTransport h k φ a s e =
      φ (physicalAuxCutTransport h.symm a) s (physicalMixedEventCutTransport h.symm k e) := by
  subst D
  rfl

omit [DecidableEq G] in
theorem physical_mixed_target_cut_transport (h : C = D) (k : ℤ)
    (a : PhysicalAuxLabels P C)
    (s : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B))
    (e : PhysicalMixedCoefficientEvent C k a s) :
    physicalMixedCoefficientTarget D k (physicalAuxCutTransport h a) s
      (physicalMixedEventCutTransport h k e) = physicalMixedCoefficientTarget C k a s e := by
  subst D
  rfl

omit [Fintype G] [DecidableEq G] in
theorem physical_mixed_repeated_labels_cut_transport (h : C = D)
    (s : CleanFullMemoryState P J ell B) :
    physicalMixedRepeatedLabels D s = physicalMixedRepeatedLabels C s := by
  subst D
  rfl

omit [DecidableEq G] in
theorem physical_mixed_residual_cut_transport (h : C = D) (ζ θ : ℝ) (k : ℤ)
    (sourceGate targetGate : PhysicalSmallBigState Ps J ell
      (CleanFullMemoryState P J ell B) → ℂ)
    (a : PhysicalAuxLabels P C)
    (s : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B))
    (e : PhysicalMixedCoefficientEvent C k a s) :
    physicalMixedFullResidualPhase D ζ θ k sourceGate targetGate
      (physicalAuxCutTransport h a) s (physicalMixedEventCutTransport h k e) =
    physicalMixedFullResidualPhase C ζ θ k sourceGate targetGate a s e := by
  subst D
  rfl

omit [DecidableEq G] in
theorem physical_mixed_phase_cut_transport_mul (h : C = D) (k : ℤ)
    (φ ψ : ∀ a (s : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B)),
      PhysicalMixedCoefficientEvent C k a s → ℂ) :
    physicalMixedPhaseCutTransport h k (fun a s e => φ a s e * ψ a s e) =
      fun a s e => physicalMixedPhaseCutTransport h k φ a s e *
        physicalMixedPhaseCutTransport h k ψ a s e := by
  subst D
  rfl

omit [DecidableEq G] in
theorem physical_mixed_phase_cut_transport_kernel_residual (h : C = D)
    (K : RepeatedBigLists P J ell → RepeatedBigLists P J ell → PhysicalAuxLabels P D → ℂ)
    (ζ θ : ℝ) (k : ℤ)
    (sourceGate targetGate : PhysicalSmallBigState Ps J ell
      (CleanFullMemoryState P J ell B) → ℂ)
    (decoration : ∀ a (s : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B)),
      PhysicalMixedCoefficientEvent C k a s → ℂ) :
    physicalMixedPhaseCutTransport h k (fun a s e =>
      K (physicalMixedRepeatedLabels C s.2)
        (physicalMixedRepeatedLabels C (physicalMixedCoefficientTarget C k a s e).2)
        (physicalAuxCutTransport h a) *
      physicalMixedFullResidualPhase C ζ θ k sourceGate targetGate a s e * decoration a s e) =
    fun a s e =>
      K (physicalMixedRepeatedLabels D s.2)
        (physicalMixedRepeatedLabels D (physicalMixedCoefficientTarget D k a s e).2) a *
      physicalMixedFullResidualPhase D ζ θ k sourceGate targetGate a s e *
        physicalMixedPhaseCutTransport h k decoration a s e := by
  subst D
  rfl

theorem physical_mixed_coefficient_action_cut_transport (h : C = D) (k : ℤ)
    (V : G → ℝ) (baseline : ∀ g, P g → ℝ) (ρ : ℝ) (Vs : S → ℝ) (q : ℝ)
    (initial : ∀ g, Finset (P g))
    (φ : ∀ a (s : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B)),
      PhysicalMixedCoefficientEvent C k a s → ℂ)
    (f : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B) → ℂ) :
    physicalMixedCoefficientAction D k V baseline ρ Vs q initial
      (physicalMixedPhaseCutTransport h k φ) f =
    physicalMixedCoefficientAction C k V baseline ρ Vs q initial φ f := by
  subst D
  rfl

theorem physical_mixed_coefficient_sum_reindex_cut
    {I K : Type} [Fintype I] [Fintype K] (index : I ≃ K)
    (cuts : K → G → Finset (Fin J)) (cuts' : I → G → Finset (Fin J))
    (hcuts : ∀ i, cuts (index i) = cuts' i) (k : K → ℤ)
    (V : G → ℝ) (baseline : ∀ g, P g → ℝ) (ρ : ℝ) (Vs : S → ℝ) (q : ℝ)
    (initial : ∀ g, Finset (P g))
    (φ : ∀ i a (s : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B)),
      PhysicalMixedCoefficientEvent (cuts i) (k i) a s → ℂ)
    (f : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B) → ℂ)
    (s : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B)) :
    (∑ i : K, physicalMixedCoefficientAction (cuts i) (k i) V baseline ρ Vs q initial
      (φ i) f s) =
    ∑ i : I, physicalMixedCoefficientAction (cuts' i) (k (index i)) V baseline ρ Vs q initial
      (physicalMixedPhaseCutTransport (hcuts i) (k (index i)) (φ (index i))) f s := by
  rw [← index.sum_comp]
  apply sum_congr rfl
  intro i _
  exact congrFun (physical_mixed_coefficient_action_cut_transport (hcuts i) (k (index i))
    V baseline ρ Vs q initial (φ (index i)) f).symm s

end
end Bounty


-- Original module: PhysicalMixedCutReindex

/- Transport along an equality of cuts preserves the precise event-factor
invariance needed by the signed mixed coefficient action. -/

open scoped Classical
namespace Bounty

section
variable {S G : Type} [Fintype S] [Fintype G] [DecidableEq G]
  {Ps : S → Finset ℕ} {P : G → Finset ℕ}
  [∀ g (p : P g), NeZero p.val] {J ell B : ℕ}
  {C D : G → Finset (Fin J)}

omit [DecidableEq G] [∀ g (p : P g), NeZero p.val] in
theorem physical_mixed_phase_cut_transport_reindex
    (h : C = D) (k : ℤ)
    (φ : ∀ a (s : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B)),
      PhysicalMixedCoefficientEvent C k a s → ℂ)
    (hφ : ∀ a (s : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B))
      (τ : ∀ g, Equiv.Perm (Fin (s.2 g).2.1.val))
      (e : PhysicalMixedCoefficientEvent C k a s),
      φ a (s.1, productMemoryReindex s.2 τ) (physicalMixedCoefficientReindex C k a s τ e) =
        φ a s e)
    (a : PhysicalAuxLabels P D)
    (s : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B))
    (τ : ∀ g, Equiv.Perm (Fin (s.2 g).2.1.val))
    (e : PhysicalMixedCoefficientEvent D k a s) :
    physicalMixedPhaseCutTransport h k φ a (s.1, productMemoryReindex s.2 τ)
      (physicalMixedCoefficientReindex D k a s τ e) =
        physicalMixedPhaseCutTransport h k φ a s e := by
  subst D
  exact hφ a s τ e

end
end Bounty
end

section

/- Complex conjugation of the actual clean row. All real weights, cutoffs,
auxiliary labels, and the supplied displacement remain unchanged. -/

open Finset
open scoped Classical
namespace Bounty

theorem physical_return_phase_conj (θ : ℝ) (h : ℤ) :
    (starRingEnd ℂ) (physicalReturnPhase θ h) = physicalReturnPhase (-θ) h := by
  unfold physicalReturnPhase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
    map_intCast, Complex.ofReal_neg]
  ring

section
variable {S G : Type} [Fintype S] [Fintype G] [DecidableEq G]
  {Ps : S → Finset ℕ} {P : G → Finset ℕ} {J ell B : ℕ}

theorem physical_mixed_coefficient_action_conj
    (C : G → Finset (Fin J)) (k : ℤ)
    (V : G → ℝ) (baseline : ∀ g, P g → ℝ) (ρ : ℝ) (Vs : S → ℝ) (q : ℝ)
    (initial : ∀ g, Finset (P g))
    (Φ : ∀ a (s : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B)),
      PhysicalMixedCoefficientEvent C k a s → ℂ)
    (f : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B) → ℂ)
    (s : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B)) :
    (starRingEnd ℂ) (physicalMixedCoefficientAction C k V baseline ρ Vs q initial Φ f s) =
      physicalMixedCoefficientAction C k V baseline ρ Vs q initial
        (fun a y e => (starRingEnd ℂ) (Φ a y e)) (fun y => (starRingEnd ℂ) (f y)) s := by
  simp only [physicalMixedCoefficientAction, physicalSmallBigFullPhasedAction,
    physicalSmallBigPhasedAction, map_sum, map_mul, Complex.conj_ofReal,
    apply_ite, map_zero]

omit [DecidableEq G] in
theorem physical_mixed_concrete_residual_conj
    (C : G → Finset (Fin J)) (ζ θ : ℝ) (k : ℤ) (Fs : ∀ g, Finset (Ps g))
    (a : PhysicalAuxLabels P C)
    (s : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B))
    (e : PhysicalMixedCoefficientEvent C k a s) :
    (starRingEnd ℂ) (physicalMixedFullResidualPhase C ζ θ k
      cleanMixedSourceGate (cleanMixedTargetGate Fs) a s e) =
    physicalMixedFullResidualPhase C (-ζ) (-θ) k
      cleanMixedSourceGate (cleanMixedTargetGate Fs) a s e := by
  unfold physicalMixedFullResidualPhase
  dsimp only
  split_ifs <;> simp only [map_mul, map_zero,
    cleanMixedSourceGate_conj, cleanMixedTargetGate_conj,
    ← physical_phase_reverse, physical_return_phase_conj]

theorem physical_mixed_gated_clean_action_conj
    (initial : ∀ g, Finset (P g)) (V : G → ℝ) (baseline : ∀ g, P g → ℝ)
    (C : G → Finset (Fin J)) (ζ θ ρ : ℝ) (k : ℤ)
    (K : RepeatedBigLists P J ell → RepeatedBigLists P J ell → PhysicalAuxLabels P C → ℂ)
    (Vs : S → ℝ) (q : ℝ) (Fs : ∀ g, Finset (Ps g))
    (f : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B) → ℂ)
    (s : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B)) :
    (starRingEnd ℂ) (physicalMixedGatedCleanAction initial V baseline C ζ θ ρ k K
      Vs q cleanMixedSourceGate (cleanMixedTargetGate Fs) f s) =
    physicalMixedGatedCleanAction initial V baseline C (-ζ) (-θ) ρ k
      (fun L R a => (starRingEnd ℂ) (K L R a)) Vs q
      cleanMixedSourceGate (cleanMixedTargetGate Fs) (fun y => (starRingEnd ℂ) (f y)) s := by
  rw [← physical_mixed_clean_coefficient_action_eq_gated initial V baseline C ζ θ ρ k K
    Vs q cleanMixedSourceGate (cleanMixedTargetGate Fs) f s]
  rw [physical_mixed_coefficient_action_conj]
  rw [← physical_mixed_clean_coefficient_action_eq_gated initial V baseline C (-ζ) (-θ) ρ k
    (fun L R a => (starRingEnd ℂ) (K L R a)) Vs q
    cleanMixedSourceGate (cleanMixedTargetGate Fs) (fun y => (starRingEnd ℂ) (f y)) s]
  congr 1
  funext a y e
  split_ifs <;> simp only [map_mul, map_zero, physical_mixed_concrete_residual_conj]

theorem physical_mixed_gated_clean_pattern_conj
    {I : Type} [Fintype I]
    (initial : ∀ g, Finset (P g)) (V : G → ℝ) (baseline : ∀ g, P g → ℝ)
    (C : I → G → Finset (Fin J)) (ζ θ ρ : ℝ) (k : ℤ)
    (K : ∀ i, RepeatedBigLists P J ell → RepeatedBigLists P J ell → PhysicalAuxLabels P (C i) → ℂ)
    (Vs : S → ℝ) (q : ℝ) (Fs : ∀ g, Finset (Ps g))
    (f : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B) → ℂ)
    (s : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B)) :
    (starRingEnd ℂ) (physicalMixedGatedCleanPatternAction initial V baseline C ζ θ ρ k K
      Vs q cleanMixedSourceGate (cleanMixedTargetGate Fs) f s) =
    physicalMixedGatedCleanPatternAction initial V baseline C (-ζ) (-θ) ρ k
      (fun i L R a => (starRingEnd ℂ) (K i L R a)) Vs q
      cleanMixedSourceGate (cleanMixedTargetGate Fs) (fun y => (starRingEnd ℂ) (f y)) s := by
  simp only [physicalMixedGatedCleanPatternAction, map_sum,
    physical_mixed_gated_clean_action_conj]

end
end Bounty
end

section

/- Swapping the two comparison groups is a bijective pattern reindexing.
It reverses the kernel endpoints while preserving the original auxiliary labels. -/

open Finset
open scoped Classical
namespace Bounty

noncomputable def repeatedBigPrimePatternSwapEquiv
    {G : Type} [DecidableEq G] {J ell : ℕ}
    (probes : G → Finset (Fin J)) (r t : Finset G) :
    RepeatedBigPrimePatternIndex (ell := ell) probes r t ≃
      RepeatedBigPrimePatternIndex (ell := ell) probes t r :=
  Equiv.sumCongr (Equiv.refl Unit) (Equiv.prodComm _ _)

theorem repeated_big_aux_cut_swap
    {G : Type} [DecidableEq G] {J ell : ℕ}
    (A B : Finset (RepeatedBigFlatIndex G J ell)) :
    repeatedBigAuxCut B A = repeatedBigAuxCut A B := by
  funext g
  simp only [repeatedBigAuxCut, union_comm B A]

theorem repeated_big_prime_pattern_swap_cut
    {G : Type} [DecidableEq G] {J ell : ℕ}
    (probes : G → Finset (Fin J)) (r t : Finset G)
    (i : RepeatedBigPrimePatternIndex (ell := ell) probes r t) :
    repeatedBigPrimePatternCut probes t r (repeatedBigPrimePatternSwapEquiv probes r t i) =
      repeatedBigPrimePatternCut probes r t i := by
  cases i with
  | inl u => rfl
  | inr ab => exact repeated_big_aux_cut_swap ab.1.val ab.2.val

theorem repeated_big_prime_pattern_swap_weight
    {G : Type} [DecidableEq G] {J ell : ℕ}
    (probes : G → Finset (Fin J)) (r t : Finset G)
    (i : RepeatedBigPrimePatternIndex (ell := ell) probes r t) :
    repeatedBigPrimePatternWeight probes t r (repeatedBigPrimePatternSwapEquiv probes r t i) =
      repeatedBigPrimePatternWeight probes r t i := by
  cases i with
  | inl u => rfl
  | inr ab =>
    change -(-1 : ℂ) ^ (ab.2.val.card + ab.1.val.card) =
      -(-1 : ℂ) ^ (ab.1.val.card + ab.2.val.card)
    rw [Nat.add_comm]

theorem repeated_big_aux_split_swap
    {G : Type} [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (A B : Finset (RepeatedBigFlatIndex G J ell))
    (hU : ∀ g (j : Fin ell), (⟨g, Sum.inr j⟩ : RepeatedBigFlatIndex G J ell) ∉ A ∪ B)
    (hU' : ∀ g (j : Fin ell), (⟨g, Sum.inr j⟩ : RepeatedBigFlatIndex G J ell) ∉ B ∪ A)
    (hAB : Disjoint A B) (a : PhysicalAuxLabels P (repeatedBigAuxCut A B)) :
    repeatedBigAuxSplitEquiv P B A hU' hAB.symm
      (physicalAuxCutTransport (repeated_big_aux_cut_swap A B).symm a) =
    ((repeatedBigAuxSplitEquiv P A B hU hAB a).2,
      (repeatedBigAuxSplitEquiv P A B hU hAB a).1) := by
  apply Prod.ext
  · funext x
    rcases x with ⟨⟨g, j | j⟩, hx⟩
    · change physicalAuxCutTransport (repeated_big_aux_cut_swap A B).symm a g
        ⟨j, (mem_repeatedBigAuxCut B A g j).mpr (mem_union_left A hx)⟩ =
        a g ⟨j, (mem_repeatedBigAuxCut A B g j).mpr (mem_union_right A hx)⟩
      rw [physical_aux_cut_transport_apply]
    · exact (hU g j (mem_union_right A hx)).elim
  · funext x
    rcases x with ⟨⟨g, j | j⟩, hx⟩
    · change physicalAuxCutTransport (repeated_big_aux_cut_swap A B).symm a g
        ⟨j, (mem_repeatedBigAuxCut B A g j).mpr (mem_union_right B hx)⟩ =
        a g ⟨j, (mem_repeatedBigAuxCut A B g j).mpr (mem_union_left B hx)⟩
      rw [physical_aux_cut_transport_apply]
    · exact (hU g j (mem_union_left B hx)).elim

theorem repeated_big_prime_coefficient_swap
    {G : Type} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ) (A B : Finset (RepeatedBigFlatIndex G J ell))
    (hU : ∀ g (j : Fin ell), (⟨g, Sum.inr j⟩ : RepeatedBigFlatIndex G J ell) ∉ A ∪ B)
    (hU' : ∀ g (j : Fin ell), (⟨g, Sum.inr j⟩ : RepeatedBigFlatIndex G J ell) ∉ B ∪ A)
    (hAB : Disjoint A B) (Q : ℕ) (h : ℝ) (keptA keptB : Finset ℤ)
    (L R : RepeatedBigLists P J ell) (a : PhysicalAuxLabels P (repeatedBigAuxCut A B)) :
    repeatedBigPrimeCoefficient P V B A hU' hAB.symm Q h keptB keptA L R
      (physicalAuxCutTransport (repeated_big_aux_cut_swap A B).symm a) =
    repeatedBigPrimeCoefficient P V A B hU hAB Q h keptA keptB R L a := by
  unfold repeatedBigPrimeCoefficient
  rw [repeated_big_aux_split_swap P A B hU hU' hAB a]
  exact mul_comm _ _

theorem repeated_big_prime_pattern_swap_kernel
    {G : Type} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ) (probes : G → Finset (Fin J))
    (r t : Finset G) (hrt : Disjoint r t) (Q : ℕ) (h : ℝ)
    (kept : Finset (RepeatedBigFlatIndex G J ell) → Finset ℤ)
    (i : RepeatedBigPrimePatternIndex (ell := ell) probes r t)
    (L R : RepeatedBigLists P J ell)
    (a : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t i)) :
    repeatedBigPrimePatternKernel P V probes t r hrt.symm Q h kept
      (repeatedBigPrimePatternSwapEquiv probes r t i) L R
      (physicalAuxCutTransport (repeated_big_prime_pattern_swap_cut probes r t i).symm a) =
    repeatedBigPrimePatternKernel P V probes r t hrt Q h kept i R L a := by
  cases i with
  | inl u => rfl
  | inr ab =>
    exact repeated_big_prime_coefficient_swap P V ab.1.val ab.2.val _ _ _ Q h
      (kept ab.1.val) (kept ab.2.val) L R a

theorem repeated_big_prime_pattern_swap_weighted_kernel
    {G : Type} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ) (probes : G → Finset (Fin J))
    (r t : Finset G) (hrt : Disjoint r t) (Q : ℕ) (h : ℝ)
    (kept : Finset (RepeatedBigFlatIndex G J ell) → Finset ℤ)
    (i : RepeatedBigPrimePatternIndex (ell := ell) probes r t)
    (L R : RepeatedBigLists P J ell)
    (a : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t i)) :
    repeatedBigPrimePatternWeight probes t r (repeatedBigPrimePatternSwapEquiv probes r t i) *
      repeatedBigPrimePatternKernel P V probes t r hrt.symm Q h kept
        (repeatedBigPrimePatternSwapEquiv probes r t i) L R
        (physicalAuxCutTransport (repeated_big_prime_pattern_swap_cut probes r t i).symm a) =
    repeatedBigPrimePatternWeight probes r t i *
      repeatedBigPrimePatternKernel P V probes r t hrt Q h kept i R L a :=
  congrArg₂ (fun z w : ℂ => z * w)
    (repeated_big_prime_pattern_swap_weight probes r t i)
    (repeated_big_prime_pattern_swap_kernel P V probes r t hrt Q h kept i L R a)

end Bounty
end

section

/- The even full prime row is complex conjugation of the ordinary swapped
pattern family. This preserves the supplied displacement, all weights, and gates. -/

open Finset
open scoped Classical
namespace Bounty

section
variable {S G : Type} [Fintype S] [Fintype G] [DecidableEq G]
  {Ps : S → Finset ℕ} {P : G → Finset ℕ} {J ell B : ℕ}

omit [Fintype G] [DecidableEq G] in
private theorem aux_cut_transport_inverse {C D : G → Finset (Fin J)}
    (h : C = D) (a : PhysicalAuxLabels P C) :
    physicalAuxCutTransport h.symm (physicalAuxCutTransport h a) = a := by
  subst D
  rfl

private theorem coefficient_kernel_cut_transport {C D : G → Finset (Fin J)}
    (hcut : C = D) (k : ℤ)
    (V : G → ℝ) (baseline : ∀ g, P g → ℝ) (ρ : ℝ) (Vs : S → ℝ) (q : ℝ)
    (initial : ∀ g, Finset (P g))
    (K : RepeatedBigLists P J ell → RepeatedBigLists P J ell → PhysicalAuxLabels P D → ℂ)
    (ζ θ : ℝ) (Fs : ∀ g, Finset (Ps g))
    (f : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B) → ℂ) :
    physicalMixedCoefficientAction C k V baseline ρ Vs q initial
      (fun a y e => K (physicalMixedRepeatedLabels C y.2)
        (physicalMixedRepeatedLabels C (physicalMixedCoefficientTarget C k a y e).2)
        (physicalAuxCutTransport hcut a) *
        physicalMixedFullResidualPhase C ζ θ k cleanMixedSourceGate (cleanMixedTargetGate Fs) a y e) f =
    physicalMixedCoefficientAction D k V baseline ρ Vs q initial
      (fun a y e => K (physicalMixedRepeatedLabels D y.2)
        (physicalMixedRepeatedLabels D (physicalMixedCoefficientTarget D k a y e).2) a *
        physicalMixedFullResidualPhase D ζ θ k cleanMixedSourceGate (cleanMixedTargetGate Fs) a y e) f := by
  subst D
  rfl

theorem physical_mixed_signed_prime_even_eq_conj_swapped
    (V : G → ℝ) (baseline : ∀ g, P g → ℝ) (ρ : ℝ) (Vs : S → ℝ) (q : ℝ)
    (probes : G → Finset (Fin J)) (r t : Finset G) (hrt : Disjoint r t)
    (Q : ℕ) (h ξ ζ θ : ℝ) (time : ℕ) (htime : time % 2 = 0)
    (k : ℤ) (initial : ∀ g, Finset (P g)) (Fs : ∀ g, Finset (Ps g))
    (f : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B) → ℂ) :
    physicalMixedSignedPrimePatternAction V baseline ρ Vs q probes r t hrt Q h ξ time k initial
      (fun i => physicalMixedFullResidualPhase (repeatedBigPrimePatternCut probes r t i)
        ζ θ k cleanMixedSourceGate (cleanMixedTargetGate Fs)) f =
    fun s => (starRingEnd ℂ)
      (physicalMixedPrimePatternAction V baseline ρ Vs q probes t r hrt.symm Q h ξ k initial
        (fun i => physicalMixedFullResidualPhase (repeatedBigPrimePatternCut probes t r i)
          (-ζ) (-θ) k cleanMixedSourceGate (cleanMixedTargetGate Fs))
        (fun y => (starRingEnd ℂ) (f y)) s) := by
  funext s
  rw [physical_mixed_signed_prime_pattern_action_of_even V baseline ρ Vs q
    probes r t hrt Q h ξ time htime k initial]
  symm
  simp only [physicalMixedPrimePatternAction, Finset.sum_apply, map_sum]
  rw [← (repeatedBigPrimePatternSwapEquiv (ell := ell) probes r t).sum_comp]
  apply sum_congr rfl
  intro i _
  rw [physical_mixed_coefficient_action_conj]
  have hstar (z : ℂ) : (starRingEnd ℂ) ((starRingEnd ℂ) z) = z := star_star z
  simp only [map_mul, physical_mixed_concrete_residual_conj, neg_neg, hstar]
  let kept := fun U : Finset (RepeatedBigFlatIndex G J ell) => primeProductRetainedCells
    (fun j : U => P j.val.1) (fun j => V j.val.1) h ξ
  let hcut := repeated_big_prime_pattern_swap_cut (ell := ell) probes r t i
  let K := fun (L R : RepeatedBigLists P J ell)
      (a : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t i)) =>
    (starRingEnd ℂ) (repeatedBigPrimePatternWeight probes r t i *
      repeatedBigPrimePatternKernel P V probes r t hrt Q h kept i R L a)
  have hK (L R : RepeatedBigLists P J ell)
      (a : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes t r
        (repeatedBigPrimePatternSwapEquiv probes r t i))) :
      (starRingEnd ℂ) (repeatedBigPrimePatternWeight probes t r
          (repeatedBigPrimePatternSwapEquiv probes r t i)) *
        (starRingEnd ℂ) (repeatedBigPrimePatternKernel P V probes t r hrt.symm Q h kept
          (repeatedBigPrimePatternSwapEquiv probes r t i) L R a) =
      K L R (physicalAuxCutTransport hcut a) := by
    have hb := repeated_big_prime_pattern_swap_weighted_kernel P V probes r t hrt Q h kept
      i L R (physicalAuxCutTransport hcut a)
    rw [aux_cut_transport_inverse] at hb
    simpa only [K, map_mul] using congrArg (starRingEnd ℂ) hb
  trans physicalMixedCoefficientAction
    (repeatedBigPrimePatternCut probes t r (repeatedBigPrimePatternSwapEquiv probes r t i))
    k V baseline ρ Vs q initial
    (fun a y e => K
      (physicalMixedRepeatedLabels
        (repeatedBigPrimePatternCut probes t r (repeatedBigPrimePatternSwapEquiv probes r t i)) y.2)
      (physicalMixedRepeatedLabels
        (repeatedBigPrimePatternCut probes t r (repeatedBigPrimePatternSwapEquiv probes r t i))
        (physicalMixedCoefficientTarget
          (repeatedBigPrimePatternCut probes t r (repeatedBigPrimePatternSwapEquiv probes r t i))
          k a y e).2)
      (physicalAuxCutTransport hcut a) *
      physicalMixedFullResidualPhase
        (repeatedBigPrimePatternCut probes t r (repeatedBigPrimePatternSwapEquiv probes r t i))
        ζ θ k cleanMixedSourceGate (cleanMixedTargetGate Fs) a y e) f s
  · congr 1
    funext a y e
    exact congrArg (fun z : ℂ => z * physicalMixedFullResidualPhase
      (repeatedBigPrimePatternCut probes t r (repeatedBigPrimePatternSwapEquiv probes r t i))
      ζ θ k cleanMixedSourceGate (cleanMixedTargetGate Fs) a y e) (hK _ _ a)
  · simpa only [K, map_mul] using congrFun
      (coefficient_kernel_cut_transport hcut k V baseline ρ Vs q initial K ζ θ Fs f) s

end
end Bounty
end

section

/- The actual candidate full norm bound for both chronological parities.
The ordinary analytic bound already includes the dirty contribution. -/

open Finset Filter
open scoped Topology BigOperators Classical

namespace Bounty.WeakZeroFree

theorem actual_exists_candidate_physical_mixed_signed_full_norm_bound
    {qsmall vsmall scale : ℝ} (hq0 : 0 ≤ qsmall) (hq1 : qsmall < 1)
    (hvs : 0 < vsmall) (hscale : 0 < scale) (ell : ℕ) (C₂ : ℝ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀
    (c s z a v D ε E beta tau : ℝ)
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
    let P := fun g : CandidateBigGroup scale L => candidatePBand (scale * L) g.val
    ∀ [DecidableEq (CandidateSmallGroup scale L)]
      [DecidableEq (CandidateBigGroup scale L)]
      [∀ p : PhysicalPrime (candidateSmallPool scale L), NeZero p.2.val]
      [∀ (g : CandidateBigGroup scale L) (p : P g), NeZero p.val],
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
    ∀ (B time : ℕ) (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L ^ C₂ →
    ∀ Vs : CandidateSmallGroup scale L → ℝ, (∀ g, vsmall ≤ Vs g) →
    ∀ ρ u vmax : ℝ, 0 < ρ → ρ < 1 → 1 < u → (∀ g, V g ≤ vmax) →
    ∀ f : PhysicalSmallBigState (candidateSmallPool scale L) J ell
      (CleanFullMemoryState P J ell B) → ℂ,
    (∀ d, ProductMemorySymmetric (fun y => f (d,y))) →
    let μ := fun g => tiltedPhysicalBirthLaw V g (baseline g)
    let W := productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g))
    cleanActiveNorm (physicalSmallBigMeasure Vs W)
      (physicalSmallBigJointAverage (physicalMixedSignedPrimePatternAction V baseline ρ Vs qsmall
        probes r t hrt Q h ξ time k initial
        (fun i => physicalMixedFullResidualPhase (repeatedBigPrimePatternCut probes r t i)
          ζ θ k cleanMixedSourceGate (cleanMixedTargetGate (fun _ => ∅)))
        (physicalSmallBigJointAverage f))) ≤
      A ^ (candidateSmallPIndices scale L).card *
        (L ^ (-E) + 2 * repeatedBigFamilyEnvelope (candidateBigPIndices scale L).card m Q ξ *
          Real.sqrt ((B : ℝ) / (((J + ell).choose ell) ^ (candidateSmallPIndices scale L).card : ℕ)) *
          Real.sqrt (unrestrictedEdgeEnergyBound ρ u v vmax (ell + m) ^ (candidateBigPIndices scale L).card)) *
        cleanActiveNorm (physicalSmallBigMeasure Vs W) f := by
  obtain ⟨A, hA, hbound⟩ :=
    actual_exists_candidate_physical_mixed_full_norm_bound hq0 hq1 hvs hscale ell C₂
  refine ⟨A, hA, ?_⟩
  intro c s z a v D ε E beta tau m J hc hs hz ha hv hD hε htau hell hml hgap hDgap
    κ s' A₀ q w x
  filter_upwards [hbound c s z a v D ε E beta tau m J hc hs hz ha hv hD hε htau
    hell hml hgap hDgap] with L hL
  intro Q h ξ P dS dG pS pG
  cases Subsingleton.elim dS (fun a b => Subtype.instDecidableEq a b)
  cases Subsingleton.elim dG (fun a b => Subtype.instDecidableEq a b)
  have hsmall : Classical.decEq (CandidateSmallGroup scale L) =
      (fun a b => Subtype.instDecidableEq a b) := Subsingleton.elim _ _
  have hbig : Classical.decEq (CandidateBigGroup scale L) =
      (fun a b => Subtype.instDecidableEq a b) := Subsingleton.elim _ _
  rw [hsmall, hbig] at hL
  intro V hdis hprime hmass hV hlog hcard hband probes hprobes
  have hbase := hL V hdis hprime hmass hV hlog hcard hband probes hprobes
  intro r t hrt hr ht ζ θ hζ initial hinitial baseline T Pmin hT hTmax hPmin
    hPlow hbaseline hbaselineBounds B time k hk hkmax Vs hVs ρ u vmax hρ0 hρ1 hu hVhi
    f hf μ W
  by_cases htime : time % 2 = 0
  · have hb := hbase t r hrt.symm ht hr (-ζ) (-θ)
      (by simpa only [abs_neg] using hζ) initial hinitial baseline T Pmin
      hT hTmax hPmin hPlow hbaseline hbaselineBounds B k hk hkmax Vs hVs
      ρ u vmax hρ0 hρ1 hu hVhi (fun y => (starRingEnd ℂ) (f y))
      (fun d => product_memory_symmetric_conj (fun y => f (d,y)) (hf d))
    rw [physical_mixed_signed_prime_even_eq_conj_swapped (htime := htime),
      ← physical_small_big_joint_average_conj f,
      physical_small_big_joint_average_conj, clean_active_norm_conj]
    simpa only [clean_active_norm_conj] using hb
  · rw [physical_mixed_signed_prime_pattern_action_of_odd (htime := htime)]
    exact hbase r t hrt hr ht ζ θ hζ initial hinitial baseline T Pmin
      hT hTmax hPmin hPlow hbaseline hbaselineBounds B k hk hkmax Vs hVs
      ρ u vmax hρ0 hρ1 hu hVhi f hf

end Bounty.WeakZeroFree
end
end

section

/- Root Fourier bridge bodies on the coherent actual-Z dependency boundary. -/

section

-- Original source module: DeterministicLedgerPhaseMultiplication

/- History and current-event phases multiply inside the same deterministic ledger. -/

namespace Bounty
section Multiplication
variable {K L X : Type*} (E : K → X → Type*)
  (target : ∀ k x, E k x → X) (update : ∀ k, L → (x : X) → E k x → L)

theorem deterministic_ledger_phase_mul
    (a b : ∀ k, L → (x : X) → E k x → ℂ)
    (ks : List K) (l : L) (x : X) (p : FiniteEventPath E target ks x) :
    deterministicLedgerPhase E target update (fun k l x e => a k l x e * b k l x e) ks l x p =
      deterministicLedgerPhase E target update a ks l x p *
      deterministicLedgerPhase E target update b ks l x p := by
  induction ks generalizing l x with
  | nil => simp only [deterministicLedgerPhase, mul_one]
  | cons k ks ih =>
    rcases p with ⟨e, p⟩
    simp only [deterministicLedgerPhase, ih]
    ring

theorem deterministic_ledger_phase_mul_local
    (a : ∀ k, L → (x : X) → E k x → ℂ) (b : ∀ k x, E k x → ℂ)
    (ks : List K) (l : L) (x : X) (p : FiniteEventPath E target ks x) :
    deterministicLedgerPhase E target update (fun k l x e => a k l x e * b k x e) ks l x p =
      deterministicLedgerPhase E target update a ks l x p *
      finiteEventLocalPhase E target b ks x p := by
  rw [deterministic_ledger_phase_mul, deterministic_ledger_local_phase]

end Multiplication
end Bounty

end

section

-- Original source module: PhysicalFullCombinedPhase

/- The original birth-history phase and original coefficient share one
local phase on the existing deterministic birth ledger. -/

open scoped Classical
namespace Bounty
section Combined
variable {I K : Type} {N J ell B : ℕ} {P : Fin N → Finset ℕ}
  (C : K → Fin N → Finset (Fin J)) (k : K → ℤ)
  (ω : ∀ j, SharedActiveLabels (fun g => ↥(P g))
    (fun g => physicalFullSharedIndices (ell := ell) (C j g)) → PhysicalAuxLabels P (C j) → ℝ)
  (β : (g : Fin N) → P g → ℝ) (ρ : ℝ) (V : Fin N → ℝ)
  (ζ : K → ℝ)
  (coeff : ∀ j, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell → PhysicalAuxLabels P (C j) → ℂ)

noncomputable def physicalFullCombinedPhase
    (tag : Option (I ⊕ K)) (H : (g : Fin N) → Finset (P g))
    (x : PhysicalFullBoundedState P J ell B)
    (e : PhysicalFullLedgerEvent C k tag (H, x)) : ℂ :=
  physicalFullLedgerEventPhase C k ω β ρ V tag (H, x) e *
    physicalFullKeyCoefficientPhase C k ζ coeff tag x e

theorem physical_full_combined_history
    (steps : List (Option (I ⊕ K))) (x : PhysicalFullBoundedState P J ell B)
    (p : FullPermutationMixedPath (fun g (p : P g) => p.val)
      (fun j g => physicalFullSharedIndices (ell := ell) (C j g)) B
      (fun j _ => PhysicalAuxLabels P (C j))
      (fun j => physicalFullEdgeDelta (C j) (k j)) (fun j => physicalFullEdgeD (C j)) steps x) :
    deterministicLedgerPhase
      (FullPermutationMixedEvent (fun g (p : P g) => p.val)
        (fun j g => physicalFullSharedIndices (ell := ell) (C j g)) B
        (fun j _ => PhysicalAuxLabels P (C j))
        (fun j => physicalFullEdgeDelta (C j) (k j)) (fun j => physicalFullEdgeD (C j)))
      (fullPermutationMixedEventTarget (fun g (p : P g) => p.val)
        (fun j g => physicalFullSharedIndices (ell := ell) (C j g)) B
        (fun j _ => PhysicalAuxLabels P (C j))
        (fun j => physicalFullEdgeDelta (C j) (k j)) (fun j => physicalFullEdgeD (C j)))
      (fullMixedLedgerUpdate (fun g (p : P g) => p.val)
        (fun j g => physicalFullSharedIndices (ell := ell) (C j g)) B
        (fun j _ => PhysicalAuxLabels P (C j))
        (fun j => physicalFullEdgeDelta (C j) (k j)) (fun j => physicalFullEdgeD (C j)))
      (physicalFullCombinedPhase C k ω β ρ V ζ coeff)
      steps (fullActiveInitialLedger x) x p =
    physicalFullHistoryPhase C k ω β ρ V steps x p *
      finiteEventLocalPhase
        (FullPermutationMixedEvent (fun g (p : P g) => p.val)
          (fun j g => physicalFullSharedIndices (ell := ell) (C j g)) B
          (fun j _ => PhysicalAuxLabels P (C j))
          (fun j => physicalFullEdgeDelta (C j) (k j)) (fun j => physicalFullEdgeD (C j)))
        (fullPermutationMixedEventTarget (fun g (p : P g) => p.val)
          (fun j g => physicalFullSharedIndices (ell := ell) (C j g)) B
          (fun j _ => PhysicalAuxLabels P (C j))
          (fun j => physicalFullEdgeDelta (C j) (k j)) (fun j => physicalFullEdgeD (C j)))
        (physicalFullKeyCoefficientPhase C k ζ coeff) steps x p := by
  unfold physicalFullCombinedPhase physicalFullHistoryPhase
  exact deterministic_ledger_phase_mul_local _ _ _ _ _ steps (fullActiveInitialLedger x) x p

end Combined
end Bounty

end

section

-- Original source module: PhysicalRootEffectiveHistory

/- The actual root remainder is one deterministic birth-ledger phase,
including its original local coefficient. -/

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

noncomputable def physicalRootEffectiveLocalPhase :=
  let Cb := fun key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val)
    (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      fun g => C key.2.1.val (e.symm g).val
  let kb := fun key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val)
    (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      k (n - key.1.val) key.2.1.val * (physicalSharedProduct (physicalSharedPrefix key.2.2.1) : ℕ)
  physicalFullCombinedPhase (I := Fin (n + 2)) (B := B) Cb kb
    (fun key _ aux => physicalAuxMass (fun g => V (e.symm g).val) (Cb key) aux)
    β ρ (fun g => V (e.symm g).val) (fun _ => 0)
    (physicalRootKeyCoefficient groups e patterns C hC ζ k K θ)

noncomputable def physicalRootEffectiveHistory
    (pl : PhysicalRootSmallPlan (P := P) (J := J) (ell := ell) (n := n) groups patterns)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B)
    (path : PhysicalEffectivePlannedBigPath
      (fun (i : patterns) g => C i.val (e.symm g).val)
      (fun (j : Fin (n + 1)) (i : patterns) => k (n - j.val) i.val) B
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) pl.1 pl.2 x) : ℂ :=
  let Cb := fun key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val)
    (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      fun g => C key.2.1.val (e.symm g).val
  let kb := fun key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val)
    (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      k (n - key.1.val) key.2.1.val * (physicalSharedProduct (physicalSharedPrefix key.2.2.1) : ℕ)
  deterministicLedgerPhase
    (FullPermutationMixedEvent (fun g (p : P (e.symm g).val) => p.val)
      (fun key g => physicalFullSharedIndices (ell := ell) (Cb key g)) B
      (fun key _ => PhysicalAuxLabels (fun g => P (e.symm g).val) (Cb key))
      (fun key => physicalFullEdgeDelta (Cb key) (kb key)) (fun key => physicalFullEdgeD (Cb key)))
    (fullPermutationMixedEventTarget (fun g (p : P (e.symm g).val) => p.val)
      (fun key g => physicalFullSharedIndices (ell := ell) (Cb key g)) B
      (fun key _ => PhysicalAuxLabels (fun g => P (e.symm g).val) (Cb key))
      (fun key => physicalFullEdgeDelta (Cb key) (kb key)) (fun key => physicalFullEdgeD (Cb key)))
    (fullMixedLedgerUpdate (fun g (p : P (e.symm g).val) => p.val)
      (fun key g => physicalFullSharedIndices (ell := ell) (Cb key g)) B
      (fun key _ => PhysicalAuxLabels (fun g => P (e.symm g).val) (Cb key))
      (fun key => physicalFullEdgeDelta (Cb key) (kb key)) (fun key => physicalFullEdgeD (Cb key)))
    (physicalRootEffectiveLocalPhase (n := n) groups e patterns C hC k V ζ K θ β ρ)
    (physicalMixedBigSteps ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) pl.1 pl.2)
    (fullActiveInitialLedger x) x path

theorem physical_root_effective_remainder_history
    (pl : PhysicalRootSmallPlan (P := P) (J := J) (ell := ell) (n := n) groups patterns)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B)
    (path : PhysicalEffectivePlannedBigPath
      (fun (i : patterns) g => C i.val (e.symm g).val)
      (fun (j : Fin (n + 1)) (i : patterns) => k (n - j.val) i.val) B
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) pl.1 pl.2 x) :
    physicalRootEffectiveRemainder groups e patterns C hC k pl V ζ K θ β ρ x path =
      physicalRootEffectiveHistory groups e patterns C hC k V ζ K θ β ρ pl x path := by
  unfold physicalRootEffectiveRemainder physicalRootEffectiveHistory
    physicalRootEffectiveLocalPhase physicalEffectivePlanCoefficientPhase
  dsimp only
  exact (physical_full_combined_history _ _ _ _ _ _ _ _ _ x path).symm

end Root
end Bounty

end

section

-- Original source module: PhysicalFullCombinedBirthPhase

/- The original combined root phase has exactly the physical birth factor.
Its empty-ledger extension is a local coefficient on the original event. -/

open scoped Classical
namespace Bounty
section Combined
variable {I K : Type} {N J ell B : ℕ} {P : Fin N → Finset ℕ}
  (C : K → Fin N → Finset (Fin J)) (k : K → ℤ)
  (ω : ∀ j, SharedActiveLabels (fun g => ↥(P g))
    (fun g => physicalFullSharedIndices (ell := ell) (C j g)) → PhysicalAuxLabels P (C j) → ℝ)
  (β : (g : Fin N) → P g → ℝ) (ρ : ℝ) (V : Fin N → ℝ)
  (ζ : K → ℝ)
  (coeff : ∀ j, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell → PhysicalAuxLabels P (C j) → ℂ)

noncomputable def physicalFullCombinedEdgePhase
    (j : K) (H : (g : Fin N) → Finset (P g)) (x : PhysicalFullBoundedState P J ell B)
    (e : PhysicalFullEdgeEvent (C j) (k j) x) : ℂ :=
  physicalFullGlobalEdgePhase (C j) (k j) H (ω j) (fun g p => β g p / V g) ρ V x e *
    physicalActiveCoefficient (C j) (C j) (C j) (ζ j) (coeff j)
      (fun g => (x g).1)
      (fun g => (fullActiveEdgeEventTarget (fun g (p : P g) => p.val)
        (fun g => physicalFullSharedIndices (ell := ell) (C j g)) B
        (fun _ => PhysicalAuxLabels P (C j)) (physicalFullEdgeDelta (C j) (k j))
        (physicalFullEdgeD (C j)) x e g).1) e.1

theorem physical_full_combined_phase_eq_ledger
    (tag : Option (I ⊕ K)) (H : (g : Fin N) → Finset (P g))
    (x : PhysicalFullBoundedState P J ell B) (e : PhysicalFullLedgerEvent C k tag (H,x)) :
    physicalFullCombinedPhase C k ω β ρ V ζ coeff tag H x e =
      fullMixedLedgerPhase (fun g (p : P g) => p.val)
        (fun j g => physicalFullSharedIndices (ell := ell) (C j g)) B
        (fun j _ => PhysicalAuxLabels P (C j))
        (fun j => physicalFullEdgeDelta (C j) (k j)) (fun j => physicalFullEdgeD (C j))
        (physicalFullCombinedEdgePhase C k ω β ρ V ζ coeff) tag (H,x) e := by
  cases tag with
  | none => simp only [physicalFullCombinedPhase, physicalFullKeyCoefficientPhase, mul_one]; rfl
  | some tag =>
    cases tag with
    | inl j => simp only [physicalFullCombinedPhase, physicalFullKeyCoefficientPhase, mul_one]; rfl
    | inr j => rfl

theorem physical_full_combined_edge_birth_factor
    (j : K) (H : (g : Fin N) → Finset (P g)) (x : PhysicalFullBoundedState P J ell B)
    (e : PhysicalFullEdgeEvent (C j) (k j) x) :
    physicalFullCombinedEdgePhase C k ω β ρ V ζ coeff j H x e =
      (if FullMixedLocalBirthAvoids (J := I) (fun g (p : P g) => p.val)
          (fun j g => physicalFullSharedIndices (ell := ell) (C j g)) B
          (fun j _ => PhysicalAuxLabels P (C j))
          (fun j => physicalFullEdgeDelta (C j) (k j)) (fun j => physicalFullEdgeD (C j))
          H (some (.inr j)) x e ∧
        FullMixedLocalBirthDistinct (J := I) (fun g (p : P g) => p.val)
          (fun j g => physicalFullSharedIndices (ell := ell) (C j g)) B
          (fun j _ => PhysicalAuxLabels P (C j))
          (fun j => physicalFullEdgeDelta (C j) (k j)) (fun j => physicalFullEdgeD (C j))
          (some (.inr j)) x e then 1 else 0) *
        physicalFullCombinedEdgePhase C k ω β ρ V ζ coeff j (fun _ => ∅) x e := by
  erw [full_mixed_edge_birth_avoids_iff, full_mixed_edge_birth_distinct_iff]
  unfold physicalFullCombinedEdgePhase
  rw [physical_full_global_birth_factor (C j) (k j) H (ω j) (fun g p => β g p / V g) ρ V x e]
  rw [mul_assoc]
  split_ifs <;> rfl

end Combined
end Bounty

end

section

-- Original source module: PhysicalFullCombinedInduced

/- The exact original combined history is the induced physical ledger phase
used by the existing common-address forest expansion. -/

open scoped Classical
namespace Bounty
section Combined
variable {I K : Type} {N J ell B : ℕ} {P : Fin N → Finset ℕ}
  (C : K → Fin N → Finset (Fin J)) (k : K → ℤ)
  (ω : ∀ j, SharedActiveLabels (fun g => ↥(P g))
    (fun g => physicalFullSharedIndices (ell := ell) (C j g)) → PhysicalAuxLabels P (C j) → ℝ)
  (β : (g : Fin N) → P g → ℝ) (ρ : ℝ) (V : Fin N → ℝ)
  (ζ : K → ℝ)
  (coeff : ∀ j, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell → PhysicalAuxLabels P (C j) → ℂ)

noncomputable def physicalFullCombinedInducedPhase (steps : List (Option (I ⊕ K))) :=
  fullMixedLedgerInducedPhase (fun g (p : P g) => p.val)
    (fun j g => physicalFullSharedIndices (ell := ell) (C j g)) B
    (fun j _ => PhysicalAuxLabels P (C j))
    (fun j => physicalFullEdgeDelta (C j) (k j)) (fun j => physicalFullEdgeD (C j))
    steps fullActiveInitialLedger
    (finiteEventLocalPhase (PhysicalFullLedgerEvent C k) (physicalFullLedgerEventTarget C k)
      (fullMixedLedgerPhase (fun g (p : P g) => p.val)
        (fun j g => physicalFullSharedIndices (ell := ell) (C j g)) B
        (fun j _ => PhysicalAuxLabels P (C j))
        (fun j => physicalFullEdgeDelta (C j) (k j)) (fun j => physicalFullEdgeD (C j))
        (physicalFullCombinedEdgePhase C k ω β ρ V ζ coeff)) steps)

theorem physical_full_combined_induced (steps : List (Option (I ⊕ K)))
    (x : PhysicalFullBoundedState P J ell B)
    (p : FullPermutationMixedPath (fun g (p : P g) => p.val)
      (fun j g => physicalFullSharedIndices (ell := ell) (C j g)) B
      (fun j _ => PhysicalAuxLabels P (C j))
      (fun j => physicalFullEdgeDelta (C j) (k j)) (fun j => physicalFullEdgeD (C j)) steps x) :
    deterministicLedgerPhase
      (FullPermutationMixedEvent (fun g (p : P g) => p.val)
        (fun j g => physicalFullSharedIndices (ell := ell) (C j g)) B
        (fun j _ => PhysicalAuxLabels P (C j))
        (fun j => physicalFullEdgeDelta (C j) (k j)) (fun j => physicalFullEdgeD (C j)))
      (fullPermutationMixedEventTarget (fun g (p : P g) => p.val)
        (fun j g => physicalFullSharedIndices (ell := ell) (C j g)) B
        (fun j _ => PhysicalAuxLabels P (C j))
        (fun j => physicalFullEdgeDelta (C j) (k j)) (fun j => physicalFullEdgeD (C j)))
      (fullMixedLedgerUpdate (fun g (p : P g) => p.val)
        (fun j g => physicalFullSharedIndices (ell := ell) (C j g)) B
        (fun j _ => PhysicalAuxLabels P (C j))
        (fun j => physicalFullEdgeDelta (C j) (k j)) (fun j => physicalFullEdgeD (C j)))
      (physicalFullCombinedPhase C k ω β ρ V ζ coeff)
      steps (fullActiveInitialLedger x) x p =
      physicalFullCombinedInducedPhase C k ω β ρ V ζ coeff steps x p := by
  have hphase : (fun tag (s : FullMixedLedgerState (fun g (p : P g) => p.val)
      (M := fun _ => J + ell) B) e =>
      physicalFullCombinedPhase C k ω β ρ V ζ coeff tag s.1 s.2 e) =
      fullMixedLedgerPhase (J := I) (fun g (p : P g) => p.val)
        (fun j g => physicalFullSharedIndices (ell := ell) (C j g)) B
        (fun j _ => PhysicalAuxLabels P (C j))
        (fun j => physicalFullEdgeDelta (C j) (k j)) (fun j => physicalFullEdgeD (C j))
        (physicalFullCombinedEdgePhase C k ω β ρ V ζ coeff) := by
    funext tag s e
    exact physical_full_combined_phase_eq_ledger C k ω β ρ V ζ coeff tag s.1 s.2 e
  rw [deterministic_ledger_phase_eq_lifted, hphase]
  rfl

end Combined
end Bounty

end

section

-- Original source module: PhysicalRootEffectiveInduced

/- The original root remainder is exactly the combined induced phase used
by common birth-forest restoration, before small-plan averaging. -/

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

theorem physical_root_effective_remainder_induced
    (pl : PhysicalRootSmallPlan (P := P) (J := J) (ell := ell) (n := n) groups patterns)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B)
    (path : PhysicalEffectivePlannedBigPath
      (fun (i : patterns) g => C i.val (e.symm g).val)
      (fun (j : Fin (n + 1)) (i : patterns) => k (n - j.val) i.val) B
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) pl.1 pl.2 x) :
    let Cb := fun key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val)
      (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
        fun g => C key.2.1.val (e.symm g).val
    let kb := fun key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val)
      (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
        k (n - key.1.val) key.2.1.val * (physicalSharedProduct (physicalSharedPrefix key.2.2.1) : ℕ)
    let steps := physicalMixedBigSteps
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) pl.1 pl.2
    physicalRootEffectiveRemainder groups e patterns C hC k pl V ζ K θ β ρ x path =
      physicalFullCombinedInducedPhase Cb kb
        (fun key _ aux => physicalAuxMass (fun g => V (e.symm g).val) (Cb key) aux)
        β ρ (fun g => V (e.symm g).val) (fun _ => 0)
        (physicalRootKeyCoefficient groups e patterns C hC ζ k K θ) steps x path := by
  dsimp only
  rw [physical_root_effective_remainder_history]
  unfold physicalRootEffectiveHistory physicalRootEffectiveLocalPhase
  dsimp only
  exact physical_full_combined_induced _ _ _ _ _ _ _ _ _ x path

end Root
end Bounty

end

section

-- Original source module: PhysicalFullCombinedForests

/- The literal weighted combined phase is restored from common birth forests.
Global distinctness is outside the local residual operators. -/

open Finset
open scoped Classical
namespace Bounty
section Combined
variable {I K Ω : Type} {N J ell B : ℕ} {P : Fin N → Finset ℕ}
  (C : K → Fin N → Finset (Fin J)) (k : K → ℤ)
  (ω : ∀ j, SharedActiveLabels (fun g => ↥(P g))
    (fun g => physicalFullSharedIndices (ell := ell) (C j g)) → PhysicalAuxLabels P (C j) → ℝ)
  (β : (g : Fin N) → P g → ℝ) (q : I → ℝ) (ρ : ℝ) (V : Fin N → ℝ)
  (ζ : K → ℝ)
  (coeff : ∀ j, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell → PhysicalAuxLabels P (C j) → ℂ)
  (steps : List (Option (I ⊕ K)))

theorem physical_full_combined_forest_expansion
    (paths : Finset Ω) (x : Ω → PhysicalFullBoundedState P J ell B)
    (p : ∀ a, FullPermutationMixedPath (fun g (p : P g) => p.val)
      (fun j g => physicalFullSharedIndices (ell := ell) (C j g)) B
      (fun j _ => PhysicalAuxLabels P (C j))
      (fun j => physicalFullEdgeDelta (C j) (k j)) (fun j => physicalFullEdgeD (C j)) steps (x a))
    (hx : ∀ a ∈ paths, FullActiveInjective (x a))
    (hcover : ∀ a ∈ paths, FullMixedLedgerCovers (fun g (p : P g) => p.val) B
      (fullActiveInitialLedger (x a), x a))
    (F : Ω → ℂ) (encode : ((g : Fin N) × P g) → ℤ) (hinj : Function.Injective encode) :
    let sizes := fun g (p : P g) => p.val
    let shared := fun j g => physicalFullSharedIndices (ell := ell) (C j g)
    let aux := fun j (_ : SharedActiveLabels (fun g => ↥(P g)) (shared j)) => PhysicalAuxLabels P (C j)
    let delta := fun j => physicalFullEdgeDelta (C j) (k j)
    let displacement := fun j => physicalFullEdgeD (C j)
    (∑ a ∈ paths, F a *
      (finiteEventPathWeight (FullPermutationMixedEvent sizes shared B aux delta displacement)
        (fullPermutationMixedEventTarget sizes shared B aux delta displacement)
        (fullPermutationMixedEventWeight sizes shared B aux delta displacement ω
          (fun g p => β g p / V g) q ρ V) steps (x a) (p a) : ℂ) *
      physicalFullCombinedInducedPhase C k ω β ρ V ζ coeff steps (x a) (p a)) =
    ∑ code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin N => J + ell) B steps)),
      (-1 : ℂ) ^ birthForestRank code * birthForestPathSum paths
        (fun a => F a * fullMixedCommonResidualWeight sizes shared B aux delta displacement
          (physicalFullCombinedEdgePhase C k ω β ρ V ζ coeff) ω
          (fun g p => β g p / V g) q ρ V steps (x a) (p a))
        (fun a => fullMixedCommonIndexedPerformed sizes shared B aux delta displacement steps (x a) (p a))
        (fun a => fullMixedCommonIndexedValue sizes shared B aux delta displacement steps encode (x a) (p a)) code := by
  dsimp only
  exact full_mixed_common_ledger_forest_expansion (fun g (p : P g) => p.val)
    (fun j g => physicalFullSharedIndices (ell := ell) (C j g)) B
    (fun j _ => PhysicalAuxLabels P (C j))
    (fun j => physicalFullEdgeDelta (C j) (k j)) (fun j => physicalFullEdgeD (C j))
    (physicalFullCombinedEdgePhase C k ω β ρ V ζ coeff) ω (fun g p => β g p / V g) q ρ V steps
    (physical_full_combined_edge_birth_factor C k ω β ρ V ζ coeff)
    paths x p hx hcover F encode hinj

end Combined
end Bounty

end

section

-- Original source module: PhysicalRootEffectiveForests

/- The original fixed-plan root contribution is the exact signed sum of
common birth forests. Its local residual has no cumulative ledger argument. -/

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

noncomputable def physicalRootEffectiveForestAction
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
      (physicalMixedBigSteps ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) pl.1 pl.2))))
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
  birthForestPathSum univ
    (fun path =>
      physicalEffectivePlanSmallFactor (fun (i : patterns) g => C i.val (e.symm g).val)
        (fun (j : Fin (n + 1)) (i : patterns) => k (n - j.val) i.val) B
        (fun s : ↥groupsᶜ => V s.val) (fun _ => q)
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
        (physicalGroupResidueVector r) pl.1 pl.2 x path *
      f (finiteEventPathTerminal (FullPermutationMixedEvent sizes shared B aux delta displacement)
        (fullPermutationMixedEventTarget sizes shared B aux delta displacement) steps x path) *
      fullMixedCommonResidualWeight sizes shared B aux delta displacement
        (physicalFullCombinedEdgePhase Cb kb omega β ρ (fun g => V (e.symm g).val) (fun _ => 0)
          (physicalRootKeyCoefficient groups e patterns C hC ζ k K θ))
        omega (fun g p => β g p / V (e.symm g).val) retention ρ (fun g => V (e.symm g).val) steps x path)
    (fullMixedCommonIndexedPerformed sizes shared B aux delta displacement steps x)
    (fun path i => fullMixedCommonBirthLabel sizes shared B aux delta displacement steps x path
      (fullMixedCommonBirthOrder (fun _ : Fin M => J + ell) B steps i)) code

theorem physical_root_effective_path_sum_forests
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ) (hinj : Function.Injective encode)
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B)
    (hx : FullActiveInjective x)
    (hcover : FullMixedLedgerCovers (fun g (p : P (e.symm g).val) => p.val) B
      (fullActiveInitialLedger x, x)) :
    physicalRootEffectivePathSum groups e patterns C hC k pl V q ζ K r θ β retention ρ f x =
      ∑ code, (-1 : ℂ) ^ birthForestRank code *
        physicalRootEffectiveForestAction groups e patterns C hC k pl V q ζ K r θ β retention ρ code f x := by
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
  have h := physical_full_combined_forest_expansion Cb kb omega β retention ρ
    (fun g => V (e.symm g).val) (fun _ => 0)
    (physicalRootKeyCoefficient groups e patterns C hC ζ k K θ) steps
    univ (fun _ : FullPermutationMixedPath sizes shared B aux delta displacement steps x => x)
    (fun path => path) (fun _ _ => hx) (fun _ _ => hcover) F encode hinj
  dsimp only at h
  calc
    _ = ∑ path : FullPermutationMixedPath sizes shared B aux delta displacement steps x,
        F path *
          (finiteEventPathWeight (FullPermutationMixedEvent sizes shared B aux delta displacement)
            (fullPermutationMixedEventTarget sizes shared B aux delta displacement)
            (fullPermutationMixedEventWeight sizes shared B aux delta displacement omega
              (fun g p => β g p / V (e.symm g).val) retention ρ (fun g => V (e.symm g).val)) steps x path : ℂ) *
          physicalFullCombinedInducedPhase Cb kb omega β ρ (fun g => V (e.symm g).val) (fun _ => 0)
            (physicalRootKeyCoefficient groups e patterns C hC ζ k K θ) steps x path := by
      rw [physical_root_effective_path_action]
      unfold fullPermutationMixedPathAction finiteEventPathAction
      apply sum_congr
      · exact congrArg (fun inst : Fintype _ => @Finset.univ _ inst) (Subsingleton.elim _ _)
      · intro path _
        rw [physical_root_effective_phase_factor, physical_root_effective_remainder_induced]
        dsimp only [F]
        ring
    _ = _ := by
      rw [h]
      apply sum_congr rfl
      intro code _
      apply congrArg (fun z : ℂ => (-1 : ℂ) ^ birthForestRank code * z)
      unfold physicalRootEffectiveForestAction birthForestPathSum
      apply sum_congr rfl
      intro path _
      have hc := optional_forest_encoding_iff
        (fullMixedCommonIndexedPerformed sizes shared B aux delta displacement steps x path)
        (fun i => fullMixedCommonBirthLabel sizes shared B aux delta displacement steps x path
          (fullMixedCommonBirthOrder (fun _ : Fin M => J + ell) B steps i))
        (fun _ h => h) encode hinj code
      change birthForestCompatible _ (fullMixedCommonIndexedValue sizes shared B aux delta displacement
        steps encode x path) code ↔ _ at hc
      rw [hc]

end Root
end Bounty

end

section

-- Original source module: FullMixedCommonShape

/- Common birth addresses depend only on the capacities at each stage,
not on the decorated edge key or the chosen pattern. -/

namespace Bounty
section Shape
variable {I K : Type*} {N : ℕ} (M : Fin N → ℕ) (B : ℕ)

abbrev FullMixedCommonShapeData (N : ℕ) := (n : ℕ) × (Fin n → Fin N → ℕ)

def fullMixedCommonShape (steps : List (Option (I ⊕ K))) : FullMixedCommonShapeData N :=
  ⟨steps.length, fun i => fullMixedCommonCapacity M B (steps.get i)⟩

def fullMixedCommonShapeCons (c : Fin N → ℕ) (s : FullMixedCommonShapeData N) :
    FullMixedCommonShapeData N :=
  ⟨s.1 + 1, Fin.cases c s.2⟩

theorem full_mixed_common_shape_cons (tag : Option (I ⊕ K)) (steps : List (Option (I ⊕ K))) :
    fullMixedCommonShape M B (tag :: steps) =
      fullMixedCommonShapeCons (fullMixedCommonCapacity M B tag) (fullMixedCommonShape M B steps) := by
  apply congrArg (Sigma.mk (steps.length + 1))
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

abbrev FullMixedCommonShapeAddress (s : FullMixedCommonShapeData N) :=
  FullMixedCommonInitialAddress M ⊕ ((i : Fin s.1) × ((g : Fin N) × Fin (s.2 i g)))

theorem full_mixed_common_address_shape (steps : List (Option (I ⊕ K))) :
    FullMixedCommonBirthAddress M B steps =
      FullMixedCommonShapeAddress M (fullMixedCommonShape M B steps) := rfl

theorem full_mixed_common_address_eq_of_shape {I' K' : Type*}
    (steps : List (Option (I ⊕ K))) (steps' : List (Option (I' ⊕ K')))
    (h : fullMixedCommonShape M B steps = fullMixedCommonShape M B steps') :
    FullMixedCommonBirthAddress M B steps = FullMixedCommonBirthAddress M B steps' :=
  congrArg (FullMixedCommonShapeAddress M) h

end Shape
end Bounty

end

section

-- Original source module: PhysicalMixedCommonShape

/- Fixing a small plan does not change the common birth-slot shape. -/

namespace Bounty
section Shape
variable {S I V K : Type} {Ps : S → Finset ℕ} {J ell N : ℕ}
  (M : Fin N → ℕ) (B : ℕ)

theorem physical_mixed_big_common_shape
    (ks : List (Option (V ⊕ K))) (L : PhysicalMarkLists Ps J ell)
    (pl : PhysicalMixedSmallPlan (I := I) ks) :
    fullMixedCommonShape M B (physicalMixedBigSteps ks L pl) =
      fullMixedCommonShape M B ks := by
  induction ks generalizing L with
  | nil =>
    apply congrArg (Sigma.mk 0)
    funext i
    exact Fin.elim0 i
  | cons tag ks ih =>
    cases tag with
    | none =>
      rcases pl with ⟨σ, pl⟩
      simp only [physicalMixedBigSteps, full_mixed_common_shape_cons]
      exact congrArg (fullMixedCommonShapeCons (fun _ => 0)) (ih _ pl)
    | some tag =>
      cases tag with
      | inl j =>
        simp only [physicalMixedBigSteps, full_mixed_common_shape_cons]
        exact congrArg (fullMixedCommonShapeCons (fun _ => B)) (ih _ pl)
      | inr k =>
        rcases pl with ⟨⟨i, R⟩, pl⟩
        simp only [physicalMixedBigSteps, full_mixed_common_shape_cons]
        exact congrArg (fullMixedCommonShapeCons M) (ih _ pl)

theorem physical_mixed_big_common_address
    (ks : List (Option (V ⊕ K))) (L : PhysicalMarkLists Ps J ell)
    (pl : PhysicalMixedSmallPlan (I := I) ks) :
    FullMixedCommonBirthAddress M B (physicalMixedBigSteps ks L pl) =
      FullMixedCommonBirthAddress M B ks :=
  full_mixed_common_address_eq_of_shape M B _ _
    (physical_mixed_big_common_shape M B ks L pl)

end Shape
end Bounty

end

section

-- Original source module: FullMixedCommonShapeOrder

/- The existing chronological enumeration is also a function only of
stage capacities. This keeps one forest index through small-plan summation. -/

namespace Bounty
section Shape
variable {N : ℕ} (M : Fin N → ℕ)

abbrev FullMixedCommonShapeLexAddress (s : FullMixedCommonShapeData N) :=
  Lex ((Lex ((g : Fin N) × Fin (M g))) ⊕
    (Lex ((i : Fin s.1) × Lex ((g : Fin N) × Fin (s.2 i g)))))

def fullMixedCommonShapeLexEquiv (s : FullMixedCommonShapeData N) :
    FullMixedCommonShapeLexAddress M s ≃ FullMixedCommonShapeAddress M s where
  toFun a := match ofLex a with
    | .inl b => .inl (ofLex b)
    | .inr b => .inr ⟨(ofLex b).1, ofLex (ofLex b).2⟩
  invFun a := toLex (match a with
    | .inl b => .inl (toLex b)
    | .inr b => .inr (toLex ⟨b.1, toLex b.2⟩))
  left_inv a := by cases a <;> rfl
  right_inv a := by cases a <;> rfl

noncomputable def fullMixedCommonShapeOrder (s : FullMixedCommonShapeData N) :
    Fin (Fintype.card (FullMixedCommonShapeAddress M s)) ≃ FullMixedCommonShapeAddress M s :=
  (Fintype.orderIsoFinOfCardEq (FullMixedCommonShapeLexAddress M s)
    (Fintype.card_congr (fullMixedCommonShapeLexEquiv M s))).toEquiv.trans
      (fullMixedCommonShapeLexEquiv M s)

theorem full_mixed_common_order_shape {I K : Type*} (B : ℕ)
    (steps : List (Option (I ⊕ K))) :
    fullMixedCommonBirthOrder M B steps =
      fullMixedCommonShapeOrder M (fullMixedCommonShape M B steps) := by
  unfold fullMixedCommonBirthOrder fullMixedCommonShapeOrder
  congr 1
  apply Equiv.ext
  intro a
  cases a <;> rfl

theorem full_mixed_common_order_heq_of_shape {I K I' K' : Type*} (B : ℕ)
    (steps : List (Option (I ⊕ K))) (steps' : List (Option (I' ⊕ K')))
    (h : fullMixedCommonShape M B steps = fullMixedCommonShape M B steps') :
    HEq (fullMixedCommonBirthOrder M B steps) (fullMixedCommonBirthOrder M B steps') := by
  rw [full_mixed_common_order_shape, full_mixed_common_order_shape]
  change HEq (fullMixedCommonShapeOrder M (fullMixedCommonShape M B steps))
    (fullMixedCommonShapeOrder M (fullMixedCommonShape M B steps'))
  generalize fullMixedCommonShape M B steps = s at h ⊢
  generalize fullMixedCommonShape M B steps' = t at h ⊢
  cases h
  rfl

end Shape
end Bounty

end

section

-- Original source module: PhysicalMixedCommonForests

/- The fixed-plan and original schedules use the same forest code space
and the same chronological order, preserving each forest rank. -/

open scoped Classical
namespace Bounty
section Shape
variable {S I V K : Type} {Ps : S → Finset ℕ} {J ell N : ℕ}
  (M : Fin N → ℕ) (B : ℕ)
  (ks : List (Option (V ⊕ K))) (L : PhysicalMarkLists Ps J ell)
  (pl : PhysicalMixedSmallPlan (I := I) ks)

theorem physical_mixed_big_common_order :
    HEq (fullMixedCommonBirthOrder M B (physicalMixedBigSteps ks L pl))
      (fullMixedCommonBirthOrder M B ks) :=
  full_mixed_common_order_heq_of_shape M B _ _
    (physical_mixed_big_common_shape M B ks L pl)

theorem physical_mixed_big_common_card :
    Fintype.card (FullMixedCommonBirthAddress M B (physicalMixedBigSteps ks L pl)) =
      Fintype.card (FullMixedCommonBirthAddress M B ks) :=
  Fintype.card_congr (Equiv.cast (physical_mixed_big_common_address M B ks L pl))

noncomputable def physicalMixedCommonForestEquiv :
    BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B (physicalMixedBigSteps ks L pl))) ≃
      BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B ks)) :=
  Equiv.cast (congrArg BirthForestCode (physical_mixed_big_common_card M B ks L pl))

theorem birth_forest_rank_cast {m n : ℕ} (h : m = n) (code : BirthForestCode m) :
    birthForestRank ((Equiv.cast (congrArg BirthForestCode h)) code) = birthForestRank code := by
  cases h
  rfl

theorem physical_mixed_common_forest_rank
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B ks))) :
    birthForestRank ((physicalMixedCommonForestEquiv M B ks L pl).symm code) = birthForestRank code :=
  birth_forest_rank_cast (physical_mixed_big_common_card M B ks L pl).symm code

end Shape
end Bounty

end

section

-- Original source module: PhysicalMixedCommonForestSum

/- Signed forest reindexing preserves the coefficient before any norm is taken. -/

open scoped Classical
namespace Bounty
section Shape
variable {S I V K : Type} {Ps : S → Finset ℕ} {J ell N : ℕ}
  (M : Fin N → ℕ) (B : ℕ)
  (ks : List (Option (V ⊕ K))) (L : PhysicalMarkLists Ps J ell)
  (pl : PhysicalMixedSmallPlan (I := I) ks)

theorem physical_mixed_common_forest_sum
    (F : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B (physicalMixedBigSteps ks L pl))) → ℂ) :
    (∑ code, (-1 : ℂ) ^ birthForestRank code * F code) =
      ∑ code, (-1 : ℂ) ^ birthForestRank code *
        F ((physicalMixedCommonForestEquiv M B ks L pl).symm code) := by
  calc
    _ = ∑ code, (-1 : ℂ) ^ birthForestRank ((physicalMixedCommonForestEquiv M B ks L pl).symm code) *
        F ((physicalMixedCommonForestEquiv M B ks L pl).symm code) :=
      (Equiv.sum_comp (physicalMixedCommonForestEquiv M B ks L pl).symm
        (fun code => (-1 : ℂ) ^ birthForestRank code * F code)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro code _
      rw [physical_mixed_common_forest_rank]

end Shape
end Bounty

end

section

-- Original source module: PhysicalRootCommonForests

/- The fixed-plan root forest expansion uses one plan-independent forest index. -/

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

abbrev PhysicalRootCommonForestCode :=
  BirthForestCode (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
    ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))

noncomputable def physicalRootCommonForestAction
    (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B) : ℂ :=
  physicalRootEffectiveForestAction groups e patterns C hC k pl V q ζ K r θ β retention ρ
    ((physicalMixedCommonForestEquiv (fun _ : Fin M => J + ell) B
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) pl.1 pl.2).symm code) f x

theorem physical_root_effective_common_forests
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ) (hinj : Function.Injective encode)
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B)
    (hx : FullActiveInjective x)
    (hcover : FullMixedLedgerCovers (fun g (p : P (e.symm g).val) => p.val) B
      (fullActiveInitialLedger x, x)) :
    physicalRootEffectivePathSum groups e patterns C hC k pl V q ζ K r θ β retention ρ f x =
      ∑ code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B),
        (-1 : ℂ) ^ birthForestRank code *
          physicalRootCommonForestAction groups e patterns C hC k pl V q ζ K r θ β retention ρ code f x := by
  rw [physical_root_effective_path_sum_forests groups e patterns C hC k pl V q ζ K r θ β retention ρ
    encode hinj f x hx hcover]
  exact physical_mixed_common_forest_sum (fun _ : Fin M => J + ell) B
    ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) pl.1 pl.2
    (fun code => physicalRootEffectiveForestAction groups e patterns C hC k pl V q ζ K r θ β retention ρ code f x)

end Root
end Bounty

end

section

-- Original source module: FullMixedShapeStage

/- Common forest ownership depends only on the stage-capacity shape. -/

namespace Bounty
section Stage
variable {N : ℕ} (M : Fin N → ℕ)

noncomputable def fullMixedShapeIndexStage (s : FullMixedCommonShapeData N)
    (i : Fin (Fintype.card (FullMixedCommonShapeAddress M s))) : Fin (s.1 + 1) :=
  match fullMixedCommonShapeOrder M s i with
  | .inl _ => 0
  | .inr a => a.1.succ

theorem full_mixed_index_stage_shape {I K : Type*} (B : ℕ)
    (steps : List (Option (I ⊕ K))) :
    fullMixedCommonIndexStage M B steps =
      fullMixedShapeIndexStage M (fullMixedCommonShape M B steps) := by
  funext i
  unfold fullMixedCommonIndexStage fullMixedShapeIndexStage
  rw [full_mixed_common_order_shape]
  cases fullMixedCommonShapeOrder M (fullMixedCommonShape M B steps) i <;> rfl

theorem full_mixed_index_stage_heq_of_shape {I K I' K' : Type*} (B : ℕ)
    (steps : List (Option (I ⊕ K))) (steps' : List (Option (I' ⊕ K')))
    (h : fullMixedCommonShape M B steps = fullMixedCommonShape M B steps') :
    HEq (fullMixedCommonIndexStage M B steps) (fullMixedCommonIndexStage M B steps') := by
  rw [full_mixed_index_stage_shape, full_mixed_index_stage_shape]
  have hh (s t : FullMixedCommonShapeData N) (heq : s = t) :
      HEq (fullMixedShapeIndexStage M s) (fullMixedShapeIndexStage M t) := by
    cases heq
    rfl
  exact hh _ _ h

end Stage
end Bounty

end

section

-- Original source module: FullMixedCommonLocalMultiplier

/- A common forest operation multiplier reads only the optional prime labels at its own original event slots. -/

open Classical
namespace Bounty
section Local
variable {J K Z : Type*} {N : ℕ} (M : Fin N → ℕ) (B : ℕ)
  (steps : List (Option (J ⊕ K)))

noncomputable def fullMixedCommonOwnerLabels (u : Fin steps.length)
    (label : FullMixedCommonLocalAddress M B (steps.get u) → Option Z)
    (i : Fin (Fintype.card (FullMixedCommonBirthAddress M B steps))) : Option Z :=
  match fullMixedCommonBirthOrder M B steps i with
  | .inl _ => none
  | .inr a => if h : a.1 = u then label
      (cast (congrArg (fun v : Fin steps.length => FullMixedCommonLocalAddress M B (steps.get v)) h) a.2)
    else none

noncomputable def fullMixedCommonLocalOperationMultiplier
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
    (θ : (Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress M B steps))) → ℝ)
    (encode : Z → ℤ) (u : Fin steps.length)
    (label : FullMixedCommonLocalAddress M B (steps.get u) → Option Z) : ℂ :=
  birthForestOperationMultiplier code (fullMixedCommonIndexStage M B steps) θ
    (fun i => (fullMixedCommonOwnerLabels M B steps u label i).isSome = true)
    (fun i => ((fullMixedCommonOwnerLabels M B steps u label i).map encode).getD 0) u.succ

theorem full_mixed_common_local_multiplier_norm_le
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
    (θ : (Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress M B steps))) → ℝ)
    (encode : Z → ℤ) (u : Fin steps.length)
    (label : FullMixedCommonLocalAddress M B (steps.get u) → Option Z) :
    ‖fullMixedCommonLocalOperationMultiplier M B steps code θ encode u label‖ ≤ 1 :=
  birthForestOperationMultiplier_norm_le_one _ _ _ _ _ _

theorem full_mixed_common_local_multiplier_untouched
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
    (θ : (Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress M B steps))) → ℝ)
    (encode : Z → ℤ) (u : Fin steps.length)
    (label : FullMixedCommonLocalAddress M B (steps.get u) → Option Z)
    (hu : u.succ ∉ birthForestAffectedOperations code (fullMixedCommonIndexStage M B steps)) :
    fullMixedCommonLocalOperationMultiplier M B steps code θ encode u label = 1 :=
  birthForestOperationMultiplier_eq_one _ _ _ _ _ _ hu

end Local

section Original
variable {J K : Type*} {N : ℕ} {P : Fin N → Type*} {M : Fin N → ℕ}
  (n : (g : Fin N) → P g → ℕ) (S : K → (g : Fin N) → Finset (Fin (M g))) (B : ℕ)
  (A : ∀ k, SharedActiveLabels P (S k) → Type*)
  (Δ D : ∀ k c, A k c → Fin N → ℤ) (steps : List (Option (J ⊕ K)))

theorem full_mixed_common_history_write_eq_owner_labels (u : Fin steps.length)
    (s : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (e : FullPermutationMixedEvent n S B A Δ D (steps.get u) s) :
    fullMixedCommonHistoryWrite n S B A Δ D steps u s e (fun _ => none) =
      fullMixedCommonOwnerLabels M B steps u
        (fullMixedCommonEventBirthLabel n S B A Δ D (steps.get u) s e) := by
  funext i
  unfold fullMixedCommonHistoryWrite fullMixedCommonOwnerLabels
  cases fullMixedCommonBirthOrder M B steps i <;> rfl

end Original
end Bounty

end

section

-- Original source module: FullMixedCommonPathMultiplier

/- Each common Fourier operation factor is the exact multiplier of the actual source/event occurrence on the original path. -/

namespace Bounty
section Path
variable {J K : Type*} {N : ℕ} {P : Fin N → Type*} {M : Fin N → ℕ}
  (n : (g : Fin N) → P g → ℕ) (S : K → (g : Fin N) → Finset (Fin (M g))) (B : ℕ)
  (A : ∀ k, SharedActiveLabels P (S k) → Type*)
  (Δ D : ∀ k c, A k c → Fin N → ℤ) (steps : List (Option (J ⊕ K)))
  (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
  (p : FullPermutationMixedPath n S B A Δ D steps x)

theorem full_mixed_common_owner_labels_on_path (u : Fin steps.length)
    (i : Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)))
    (hi : fullMixedCommonIndexStage M B steps i = u.succ) :
    let e := finiteEventPathOccurrence (FullPermutationMixedEvent n S B A Δ D)
      (fullPermutationMixedEventTarget n S B A Δ D) steps x p u
    fullMixedCommonOwnerLabels M B steps u
      (fullMixedCommonEventBirthLabel n S B A Δ D (steps.get u) e.1 e.2) i =
      fullMixedCommonBirthLabel n S B A Δ D steps x p (fullMixedCommonBirthOrder M B steps i) := by
  obtain ⟨a, ha⟩ := (full_mixed_common_index_stage_succ_iff M B steps u i).mp hi
  dsimp only
  unfold fullMixedCommonOwnerLabels
  rw [ha]
  simp only [cast_eq, full_mixed_common_new_label]
  exact (full_mixed_common_path_label_occurrence n S B A Δ D steps x p u a).symm

theorem full_mixed_common_local_multiplier_on_path
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
    (θ : (Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress M B steps))) → ℝ)
    (encode : Sigma P → ℤ) (u : Fin steps.length) :
    let e := finiteEventPathOccurrence (FullPermutationMixedEvent n S B A Δ D)
      (fullPermutationMixedEventTarget n S B A Δ D) steps x p u
    fullMixedCommonLocalOperationMultiplier M B steps code θ encode u
      (fullMixedCommonEventBirthLabel n S B A Δ D (steps.get u) e.1 e.2) =
      birthForestOperationMultiplier code (fullMixedCommonIndexStage M B steps) θ
        (fullMixedCommonIndexedPerformed n S B A Δ D steps x p)
        (fullMixedCommonIndexedValue n S B A Δ D steps encode x p) u.succ := by
  dsimp only [fullMixedCommonLocalOperationMultiplier]
  apply birth_forest_operation_multiplier_congr_on_owner
  · intro i hi
    change (_ = true) ↔ (_ = true)
    rw [full_mixed_common_owner_labels_on_path n S B A Δ D steps x p u i hi]
  · intro i hi
    rw [full_mixed_common_owner_labels_on_path n S B A Δ D steps x p u i hi]
    rfl

end Path
end Bounty

end

section

-- Original source module: FullMixedCommonBoundaryMultiplier

/- The common initial-label phase stays at the boundary; all subsequent factors belong to their actual original events. -/

open Finset Classical
namespace Bounty
section Boundary
variable {J K Z : Type*} {N : ℕ} (M : Fin N → ℕ) (B : ℕ)
  (steps : List (Option (J ⊕ K)))
  (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
  (θ : (Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) ×
    Fin (Fintype.card (FullMixedCommonBirthAddress M B steps))) → ℝ)
  (encode : Z → ℤ) (initial : FullMixedCommonInitialAddress M → Z)

noncomputable def fullMixedCommonBoundaryMultiplier : ℂ :=
  birthForestOperationMultiplier code (fullMixedCommonIndexStage M B steps) θ
    (fun _ => True) (fun i => match fullMixedCommonBirthOrder M B steps i with
      | .inl a => encode (initial a)
      | .inr _ => 0) 0

theorem full_mixed_common_boundary_multiplier_norm_le :
    ‖fullMixedCommonBoundaryMultiplier M B steps code θ encode initial‖ ≤ 1 :=
  birthForestOperationMultiplier_norm_le_one _ _ _ _ _ _
end Boundary

section Original
variable {J K : Type*} {N : ℕ} {P : Fin N → Type*} {M : Fin N → ℕ}
  (n : (g : Fin N) → P g → ℕ) (S : K → (g : Fin N) → Finset (Fin (M g))) (B : ℕ)
  (A : ∀ k, SharedActiveLabels P (S k) → Type*)
  (Δ D : ∀ k c, A k c → Fin N → ℤ) (steps : List (Option (J ⊕ K)))
  (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
  (p : FullPermutationMixedPath n S B A Δ D steps x)
  (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
  (θ : (Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) ×
    Fin (Fintype.card (FullMixedCommonBirthAddress M B steps))) → ℝ)
  (encode : Sigma P → ℤ)

theorem full_mixed_common_boundary_multiplier_on_path :
    fullMixedCommonBoundaryMultiplier M B steps code θ encode (fullMixedCommonInitialPrime x) =
      birthForestOperationMultiplier code (fullMixedCommonIndexStage M B steps) θ
        (fullMixedCommonIndexedPerformed n S B A Δ D steps x p)
        (fullMixedCommonIndexedValue n S B A Δ D steps encode x p) 0 := by
  apply birth_forest_operation_multiplier_congr_on_owner
  · intro i hi
    obtain ⟨a, ha⟩ := (full_mixed_common_index_stage_zero_iff M B steps i).mp hi
    change True ↔ (fullMixedCommonBirthLabel n S B A Δ D steps x p (fullMixedCommonBirthOrder M B steps i)).isSome = true
    rw [ha, full_mixed_common_initial_label]
    simp only [Option.isSome_some]
  · intro i hi
    obtain ⟨a, ha⟩ := (full_mixed_common_index_stage_zero_iff M B steps i).mp hi
    change (match fullMixedCommonBirthOrder M B steps i with
      | .inl a => encode (fullMixedCommonInitialPrime x a)
      | .inr _ => 0) = _
    unfold fullMixedCommonIndexedValue
    rw [ha, full_mixed_common_initial_label]
    rfl

theorem full_mixed_common_boundary_event_product :
    fullMixedCommonBoundaryMultiplier M B steps code θ encode (fullMixedCommonInitialPrime x) *
      (∏ u : Fin steps.length,
        let e := finiteEventPathOccurrence (FullPermutationMixedEvent n S B A Δ D)
          (fullPermutationMixedEventTarget n S B A Δ D) steps x p u
        fullMixedCommonLocalOperationMultiplier M B steps code θ encode u
          (fullMixedCommonEventBirthLabel n S B A Δ D (steps.get u) e.1 e.2)) =
      if ∀ i ∈ birthForestTouched code, fullMixedCommonIndexedPerformed n S B A Δ D steps x p i then
        ∏ i, physicalReturnPhase (birthForestLocalFrequency code θ i)
          (fullMixedCommonIndexedValue n S B A Δ D steps encode x p i) else 0 := by
  simp_rw [full_mixed_common_local_multiplier_on_path n S B A Δ D steps x p code θ encode]
  rw [full_mixed_common_boundary_multiplier_on_path n S B A Δ D steps x p code θ encode,
    ← Fin.prod_univ_succ]
  exact birthForestOperationMultiplier_product _ _ _ _ _

end Original
end Bounty

end

section

-- Original source module: FullMixedShapeBoundary

/- The initial Fourier multiplier depends only on the common birth shape,
so fixing a small plan does not change its boundary factor. -/

namespace Bounty
section Boundary
variable {Z : Type*} {N : ℕ} (M : Fin N → ℕ)

noncomputable def fullMixedShapeBoundaryMultiplier (s : FullMixedCommonShapeData N)
    (code : BirthForestCode (Fintype.card (FullMixedCommonShapeAddress M s)))
    (θ : (Fin (Fintype.card (FullMixedCommonShapeAddress M s)) ×
      Fin (Fintype.card (FullMixedCommonShapeAddress M s))) → ℝ)
    (encode : Z → ℤ) (initial : FullMixedCommonInitialAddress M → Z) : ℂ :=
  birthForestOperationMultiplier code (fullMixedShapeIndexStage M s) θ
    (fun _ => True) (fun i => match fullMixedCommonShapeOrder M s i with
      | .inl a => encode (initial a)
      | .inr _ => 0) 0

theorem full_mixed_boundary_multiplier_shape {I K : Type*} (B : ℕ)
    (steps : List (Option (I ⊕ K))) :
    fullMixedCommonBoundaryMultiplier (Z := Z) M B steps =
      fullMixedShapeBoundaryMultiplier M (fullMixedCommonShape M B steps) := by
  funext code θ encode initial
  unfold fullMixedCommonBoundaryMultiplier fullMixedShapeBoundaryMultiplier
  rw [full_mixed_index_stage_shape]
  congr 1
  funext i
  rw [full_mixed_common_order_shape]
  cases fullMixedCommonShapeOrder M (fullMixedCommonShape M B steps) i <;> rfl

theorem full_mixed_boundary_multiplier_heq_of_shape {I K I' K' : Type*} (B : ℕ)
    (steps : List (Option (I ⊕ K))) (steps' : List (Option (I' ⊕ K')))
    (h : fullMixedCommonShape M B steps = fullMixedCommonShape M B steps') :
    HEq (fullMixedCommonBoundaryMultiplier (Z := Z) M B steps)
      (fullMixedCommonBoundaryMultiplier (Z := Z) M B steps') := by
  rw [full_mixed_boundary_multiplier_shape, full_mixed_boundary_multiplier_shape]
  have hh (s t : FullMixedCommonShapeData N) (heq : s = t) :
      HEq (fullMixedShapeBoundaryMultiplier (Z := Z) M s)
        (fullMixedShapeBoundaryMultiplier (Z := Z) M t) := by
    cases heq
    rfl
  exact hh _ _ h

end Boundary
end Bounty

end

section

-- Original source module: FullMixedShapeLocal

/- Local birth multipliers depend on stage capacities and their optional
prime labels, with no dependence on the decorated edge key. -/

open Classical
namespace Bounty
section Local
variable {Z : Type*} {N : ℕ} (M : Fin N → ℕ)

abbrev FullMixedShapeLocalAddress (s : FullMixedCommonShapeData N) (u : Fin s.1) :=
  (g : Fin N) × Fin (s.2 u g)

noncomputable def fullMixedShapeOwnerLabels (s : FullMixedCommonShapeData N) (u : Fin s.1)
    (label : FullMixedShapeLocalAddress s u → Option Z)
    (i : Fin (Fintype.card (FullMixedCommonShapeAddress M s))) : Option Z :=
  match fullMixedCommonShapeOrder M s i with
  | .inl _ => none
  | .inr a => if h : a.1 = u then
      label (cast (congrArg (FullMixedShapeLocalAddress s) h) a.2)
    else none

noncomputable def fullMixedShapeLocalOperationMultiplier (s : FullMixedCommonShapeData N)
    (code : BirthForestCode (Fintype.card (FullMixedCommonShapeAddress M s)))
    (θ : (Fin (Fintype.card (FullMixedCommonShapeAddress M s)) ×
      Fin (Fintype.card (FullMixedCommonShapeAddress M s))) → ℝ)
    (encode : Z → ℤ) (u : Fin s.1) (label : FullMixedShapeLocalAddress s u → Option Z) : ℂ :=
  birthForestOperationMultiplier code (fullMixedShapeIndexStage M s) θ
    (fun i => (fullMixedShapeOwnerLabels M s u label i).isSome = true)
    (fun i => ((fullMixedShapeOwnerLabels M s u label i).map encode).getD 0) u.succ

theorem full_mixed_owner_labels_shape {I K : Type*} (B : ℕ)
    (steps : List (Option (I ⊕ K))) (u : Fin steps.length)
    (label : FullMixedCommonLocalAddress M B (steps.get u) → Option Z) :
    fullMixedCommonOwnerLabels M B steps u label =
      fullMixedShapeOwnerLabels M (fullMixedCommonShape M B steps) u label := by
  funext i
  unfold fullMixedCommonOwnerLabels fullMixedShapeOwnerLabels
  rw [full_mixed_common_order_shape]
  cases fullMixedCommonShapeOrder M (fullMixedCommonShape M B steps) i with
  | inl a => rfl
  | inr a =>
    dsimp only
    split_ifs <;> first | rfl | contradiction

theorem full_mixed_local_multiplier_shape {I K : Type*} (B : ℕ)
    (steps : List (Option (I ⊕ K))) :
    fullMixedCommonLocalOperationMultiplier (Z := Z) M B steps =
      fullMixedShapeLocalOperationMultiplier M (fullMixedCommonShape M B steps) := by
  funext code θ encode u label
  unfold fullMixedCommonLocalOperationMultiplier fullMixedShapeLocalOperationMultiplier
  rw [full_mixed_index_stage_shape, full_mixed_owner_labels_shape]
  rfl

theorem full_mixed_local_multiplier_heq_of_shape {I K I' K' : Type*} (B : ℕ)
    (steps : List (Option (I ⊕ K))) (steps' : List (Option (I' ⊕ K')))
    (h : fullMixedCommonShape M B steps = fullMixedCommonShape M B steps') :
    HEq (fullMixedCommonLocalOperationMultiplier (Z := Z) M B steps)
      (fullMixedCommonLocalOperationMultiplier (Z := Z) M B steps') := by
  rw [full_mixed_local_multiplier_shape, full_mixed_local_multiplier_shape]
  have hh (s t : FullMixedCommonShapeData N) (heq : s = t) :
      HEq (fullMixedShapeLocalOperationMultiplier (Z := Z) M s)
        (fullMixedShapeLocalOperationMultiplier (Z := Z) M t) := by
    cases heq
    rfl
  exact hh _ _ h

end Local
end Bounty

end

section

-- Original source module: BirthFourierCardTransport

/- Identical finite birth cardinalities give an exact transport of the
Fourier cube, including its integral. -/

open MeasureTheory
namespace Bounty

def birthFourierFrequencyCast {m n : ℕ} (h : m = n)
    (θ : (Fin n × Fin n) → ℝ) : (Fin m × Fin m) → ℝ :=
  fun ij => θ (Fin.cast h ij.1, Fin.cast h ij.2)

theorem birth_fourier_frequency_cast_refl {n : ℕ} (θ : (Fin n × Fin n) → ℝ) :
    birthFourierFrequencyCast rfl θ = θ := rfl

theorem birth_fourier_integral_card_transport {m n : ℕ} (h : m = n)
    (F : ((Fin m × Fin m) → ℝ) → ℂ) :
    (∫ θ, F θ ∂birthFourierCubeMeasure (Fin m × Fin m)) =
      ∫ θ, F (birthFourierFrequencyCast h θ) ∂birthFourierCubeMeasure (Fin n × Fin n) := by
  cases h
  rfl

end Bounty

end

section

-- Original source module: FullMixedShapeMultiplierCast

/- Equal chronological birth shapes transport the code, Fourier
frequency, boundary factor, and every local factor together. -/

namespace Bounty
section Cast
variable {Z : Type*} {N : ℕ} (M : Fin N → ℕ)

def fullMixedShapeLocalAddressCast {s t : FullMixedCommonShapeData N}
    (h : s = t) (u : Fin s.1) :
    FullMixedShapeLocalAddress s u ≃
      FullMixedShapeLocalAddress t (Fin.cast (congrArg Sigma.fst h) u) := by
  cases h
  exact Equiv.refl _

theorem full_mixed_shape_boundary_cast {s t : FullMixedCommonShapeData N} (h : s = t)
    (code : BirthForestCode (Fintype.card (FullMixedCommonShapeAddress M t)))
    (θ : (Fin (Fintype.card (FullMixedCommonShapeAddress M t)) ×
      Fin (Fintype.card (FullMixedCommonShapeAddress M t))) → ℝ)
    (encode : Z → ℤ) (initial : FullMixedCommonInitialAddress M → Z) :
    fullMixedShapeBoundaryMultiplier M s
      (cast (congrArg (fun q => BirthForestCode (Fintype.card (FullMixedCommonShapeAddress M q))) h.symm) code)
      (birthFourierFrequencyCast (congrArg (fun q => Fintype.card (FullMixedCommonShapeAddress M q)) h) θ)
      encode initial = fullMixedShapeBoundaryMultiplier M t code θ encode initial := by
  cases h
  rfl

theorem full_mixed_shape_local_cast {s t : FullMixedCommonShapeData N} (h : s = t)
    (code : BirthForestCode (Fintype.card (FullMixedCommonShapeAddress M t)))
    (θ : (Fin (Fintype.card (FullMixedCommonShapeAddress M t)) ×
      Fin (Fintype.card (FullMixedCommonShapeAddress M t))) → ℝ)
    (encode : Z → ℤ) (u : Fin s.1) (label : FullMixedShapeLocalAddress s u → Option Z) :
    fullMixedShapeLocalOperationMultiplier M s
      (cast (congrArg (fun q => BirthForestCode (Fintype.card (FullMixedCommonShapeAddress M q))) h.symm) code)
      (birthFourierFrequencyCast (congrArg (fun q => Fintype.card (FullMixedCommonShapeAddress M q)) h) θ)
      encode u label =
    fullMixedShapeLocalOperationMultiplier M t code θ encode (Fin.cast (congrArg Sigma.fst h) u)
      (fun a => label ((fullMixedShapeLocalAddressCast h u).symm a)) := by
  cases h
  rfl

end Cast
end Bounty

end

section

-- Original source module: PhysicalMixedShapeMultiplier

/- The actual decorated big schedule uses the original common boundary
and local multipliers after the canonical code and frequency transport. -/

namespace Bounty
section Mixed
variable {Z : Type*} {S I V K : Type} {Ps : S → Finset ℕ} {J ell N : ℕ}
  (M : Fin N → ℕ) (B : ℕ)
  (ks : List (Option (V ⊕ K))) (L : PhysicalMarkLists Ps J ell)
  (pl : PhysicalMixedSmallPlan (I := I) ks)
  (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B ks)))
  (θ : (Fin (Fintype.card (FullMixedCommonBirthAddress M B ks)) ×
    Fin (Fintype.card (FullMixedCommonBirthAddress M B ks))) → ℝ)
  (encode : Z → ℤ)

noncomputable def physicalMixedCommonFrequency :
    (Fin (Fintype.card (FullMixedCommonBirthAddress M B (physicalMixedBigSteps ks L pl))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress M B (physicalMixedBigSteps ks L pl)))) → ℝ :=
  birthFourierFrequencyCast (physical_mixed_big_common_card M B ks L pl) θ

theorem physical_mixed_common_boundary_multiplier
    (initial : FullMixedCommonInitialAddress M → Z) :
    fullMixedCommonBoundaryMultiplier M B (physicalMixedBigSteps ks L pl)
      ((physicalMixedCommonForestEquiv M B ks L pl).symm code)
      (physicalMixedCommonFrequency M B ks L pl θ) encode initial =
    fullMixedCommonBoundaryMultiplier M B ks code θ encode initial := by
  rw [full_mixed_boundary_multiplier_shape, full_mixed_boundary_multiplier_shape]
  exact full_mixed_shape_boundary_cast M (physical_mixed_big_common_shape M B ks L pl)
    code θ encode initial

theorem physical_mixed_common_local_multiplier
    (u : Fin (physicalMixedBigSteps ks L pl).length)
    (label : FullMixedCommonLocalAddress M B ((physicalMixedBigSteps ks L pl).get u) → Option Z) :
    fullMixedCommonLocalOperationMultiplier M B (physicalMixedBigSteps ks L pl)
      ((physicalMixedCommonForestEquiv M B ks L pl).symm code)
      (physicalMixedCommonFrequency M B ks L pl θ) encode u label =
    fullMixedCommonLocalOperationMultiplier M B ks code θ encode
      (Fin.cast (congrArg Sigma.fst (physical_mixed_big_common_shape M B ks L pl)) u)
      (fun a => label ((fullMixedShapeLocalAddressCast
        (physical_mixed_big_common_shape M B ks L pl) u).symm a)) := by
  rw [full_mixed_local_multiplier_shape, full_mixed_local_multiplier_shape]
  exact full_mixed_shape_local_cast M (physical_mixed_big_common_shape M B ks L pl)
    code θ encode u label

end Mixed
end Bounty

end

section

-- Original source module: PhysicalMixedBigEventProjection

/- A mixed event determines its actual decorated big event at the current
small source and target. This projection keeps the original full event. -/

open scoped Classical
namespace Bounty
section Projection
variable {S G I V K : Type} [Fintype S]
  {Ps : S → Finset ℕ} {P : G → Type}
  (n : ∀ g, P g → ℕ) {J ell : ℕ} {M : G → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (A : I → Type)
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J →
    SharedActiveLabels P (shared i) → A i → G → ℤ)

abbrev PhysicalMixedDecoratedBigEvent :=
  FullPermutationMixedEvent (J := V) n
    (fun key : PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K) => shared key.2.1) B
    (fun key _ => A key.2.1)
    (fun key c a => Δ key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)
    (fun key c a => D key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)

noncomputable def physicalMixedBigEventTag :
    (tag : Option (V ⊕ K)) →
    (s : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B) →
    PhysicalMixedWordEvent n shared B A Δ D tag s →
    Option (V ⊕ PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K))
  | none, _, _ => none
  | some (.inl j), _, _ => some (.inl j)
  | some (.inr k), s, e => some (.inr (k, e.1, s.1.2, e.2.2.1))

noncomputable def physicalMixedBigEventProjection :
    (tag : Option (V ⊕ K)) →
    (s : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B) →
    (e : PhysicalMixedWordEvent n shared B A Δ D tag s) →
    PhysicalMixedDecoratedBigEvent n shared B A Δ D
      (physicalMixedBigEventTag n shared B A Δ D tag s e) s.2
  | none, _, e => ULift.up e.2
  | some (.inl _), _, e => ULift.up e
  | some (.inr _), _, e => ⟨e.2.1, e.2.2.2.2⟩

variable (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)

theorem physical_mixed_big_event_target
    (tag : Option (V ⊕ K))
    (s : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B)
    (e : PhysicalMixedWordEvent n shared B A Δ D tag s) :
    fullPermutationMixedEventTarget n
      (fun key : PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K) => shared key.2.1) B
      (fun key _ => A key.2.1)
      (fun key c a => Δ key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)
      (fun key c a => D key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)
      (physicalMixedBigEventTag n shared B A Δ D tag s e) s.2
      (physicalMixedBigEventProjection n shared B A Δ D tag s e) =
    (physicalMixedWordTarget n shared B A Δ D kbig tag s e).2 := by
  cases tag with
  | none => rfl
  | some tag => cases tag <;> rfl

end Projection
end Bounty

end

section

-- Original source module: PhysicalMixedTagErasure

/- Erasing the small-plan decoration recovers each original event tag
and preserves its full-slot birth addresses. -/

namespace Bounty
section Tags
variable {S I V K : Type} {Ps : S → Finset ℕ} {J ell : ℕ}

def physicalMixedBigTagErase :
    Option (V ⊕ PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K)) →
      Option (V ⊕ K)
  | none => none
  | some (.inl j) => some (.inl j)
  | some (.inr key) => some (.inr key.1)

theorem physical_mixed_big_steps_erase
    (ks : List (Option (V ⊕ K))) (L : PhysicalMarkLists Ps J ell)
    (pl : PhysicalMixedSmallPlan (I := I) ks) :
    (physicalMixedBigSteps ks L pl).map physicalMixedBigTagErase = ks := by
  induction ks generalizing L with
  | nil => rfl
  | cons tag ks ih =>
    cases tag with
    | none =>
      rcases pl with ⟨σ, pl⟩
      simp only [physicalMixedBigSteps, List.map_cons, physicalMixedBigTagErase, ih]
    | some tag =>
      cases tag with
      | inl j =>
        simp only [physicalMixedBigSteps, List.map_cons, physicalMixedBigTagErase]
        exact congrArg (List.cons (some (.inl j))) (ih L pl)
      | inr k =>
        rcases pl with ⟨⟨i, R⟩, pl⟩
        simp only [physicalMixedBigSteps, List.map_cons, physicalMixedBigTagErase, ih]

theorem physical_mixed_big_tag_capacity {N : ℕ} (M : Fin N → ℕ) (B : ℕ)
    (tag : Option (V ⊕ PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K))) :
    fullMixedCommonCapacity M B (physicalMixedBigTagErase tag) = fullMixedCommonCapacity M B tag := by
  cases tag with
  | none => rfl
  | some tag => cases tag <;> rfl

def physicalMixedTagBirthAddressEquiv {N : ℕ} (M : Fin N → ℕ) (B : ℕ)
    (tag : Option (V ⊕ PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K))) :
    FullMixedCommonLocalAddress M B (physicalMixedBigTagErase tag) ≃
      FullMixedCommonLocalAddress M B tag := by
  cases tag with
  | none => exact Equiv.refl _
  | some tag => cases tag <;> exact Equiv.refl _

end Tags
section Events
variable {S G I V K : Type} [Fintype S]
  {Ps : S → Finset ℕ} {P : G → Type}
  (n : ∀ g, P g → ℕ) {J ell : ℕ} {M : G → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (A : I → Type)
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J →
    SharedActiveLabels P (shared i) → A i → G → ℤ)

omit [Fintype S] in
theorem physical_mixed_big_event_tag_erase
    (tag : Option (V ⊕ K))
    (s : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B)
    (e : PhysicalMixedWordEvent n shared B A Δ D tag s) :
    physicalMixedBigTagErase (physicalMixedBigEventTag n shared B A Δ D tag s e) = tag := by
  cases tag with
  | none => rfl
  | some tag => cases tag <;> rfl

end Events
end Bounty

end

section

-- Original source module: PhysicalMixedTagPositions

/- Erasing a decorated tag commutes with reading its chronological
position, and transports its optional birth labels without change. -/

namespace Bounty

theorem list_map_get_cast {α β : Type*} (f : α → β) (xs : List α) (ys : List β)
    (h : xs.map f = ys) (hlen : xs.length = ys.length) (u : Fin xs.length) :
    f (xs.get u) = ys.get (Fin.cast hlen u) := by
  subst ys
  simp only [List.get_eq_getElem, List.getElem_map]
  rfl

section Tags
variable {S I V K Z : Type} {Ps : S → Finset ℕ} {J ell N : ℕ}
  (M : Fin N → ℕ) (B : ℕ)

theorem physical_mixed_big_tag_at_position
    (ks : List (Option (V ⊕ K))) (L : PhysicalMarkLists Ps J ell)
    (pl : PhysicalMixedSmallPlan (I := I) ks)
    (u : Fin (physicalMixedBigSteps ks L pl).length) :
    physicalMixedBigTagErase ((physicalMixedBigSteps ks L pl).get u) =
      ks.get (Fin.cast (congrArg Sigma.fst (physical_mixed_big_common_shape M B ks L pl)) u) :=
  list_map_get_cast physicalMixedBigTagErase _ _
    (physical_mixed_big_steps_erase ks L pl)
    (congrArg Sigma.fst (physical_mixed_big_common_shape M B ks L pl)) u

theorem physical_mixed_erased_birth_label_heq
    (tag : Option (V ⊕ PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K)))
    (label : FullMixedCommonLocalAddress M B tag → Option Z) :
    HEq label (fun a => label (physicalMixedTagBirthAddressEquiv M B tag a)) := by
  cases tag with
  | none => rfl
  | some tag => cases tag <;> rfl

end Tags
end Bounty

end

section

-- Original source module: FullMixedCommonTaggedMultiplier

/- Known ghost and edge tags retain the exact common forest multiplier at their chronological occurrence. -/

namespace Bounty
section Tagged
variable {J K Z : Type*} {N : ℕ} (M : Fin N → ℕ) (B : ℕ)
  (steps : List (Option (J ⊕ K)))
  (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
  (θ : (Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) ×
    Fin (Fintype.card (FullMixedCommonBirthAddress M B steps))) → ℝ)
  (encode : Z → ℤ) (u : Fin steps.length) (tag : Option (J ⊕ K)) (htag : steps.get u = tag)

noncomputable def fullMixedCommonTaggedOperationMultiplier
    (label : FullMixedCommonLocalAddress M B tag → Option Z) : ℂ :=
  fullMixedCommonLocalOperationMultiplier M B steps code θ encode u
    (fun a => label (cast (congrArg (FullMixedCommonLocalAddress M B) htag) a))

theorem full_mixed_common_tagged_multiplier_norm_le
    (label : FullMixedCommonLocalAddress M B tag → Option Z) :
    ‖fullMixedCommonTaggedOperationMultiplier M B steps code θ encode u tag htag label‖ ≤ 1 :=
  full_mixed_common_local_multiplier_norm_le M B steps code θ encode u _

end Tagged

section Event
variable {J K : Type*} {N : ℕ} {P : Fin N → Type*} {M : Fin N → ℕ}
  (n : (g : Fin N) → P g → ℕ) (S : K → (g : Fin N) → Finset (Fin (M g))) (B : ℕ)
  (A : ∀ k, SharedActiveLabels P (S k) → Type*)
  (Δ D : ∀ k c, A k c → Fin N → ℤ) (steps : List (Option (J ⊕ K)))
  (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
  (θ : (Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) ×
    Fin (Fintype.card (FullMixedCommonBirthAddress M B steps))) → ℝ)
  (encode : Sigma P → ℤ) (u : Fin steps.length) (tag : Option (J ⊕ K)) (htag : steps.get u = tag)

theorem full_mixed_common_tagged_multiplier_event
    (s : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (e : FullPermutationMixedEvent n S B A Δ D tag s) :
    fullMixedCommonTaggedOperationMultiplier M B steps code θ encode u tag htag
      (fullMixedCommonEventBirthLabel n S B A Δ D tag s e) =
      fullMixedCommonLocalOperationMultiplier M B steps code θ encode u
        (fullMixedCommonEventBirthLabel n S B A Δ D (steps.get u) s
          (fullMixedTaggedOwnerEvent n S B A Δ D steps u tag htag s e)) := by
  subst tag
  rfl

end Event
end Bounty

end

section

-- Original source module: FullMixedTaggedShapeTransport

/- Tagged local factors transport across equal birth shapes whenever
their occurrence and optional-label function agree heterogeneously. -/

namespace Bounty

theorem birth_label_precomp_cast_heq {α β : Type} {Z : Type*} (h : α = β) (f : β → Z) :
    HEq (fun a => f (cast h a)) f := by
  cases h
  rfl

theorem full_mixed_shape_address_symm_heq {N : ℕ} {s t : FullMixedCommonShapeData N}
    (h : s = t) (u : Fin s.1)
    (a : FullMixedShapeLocalAddress t (Fin.cast (congrArg Sigma.fst h) u)) :
    HEq ((fullMixedShapeLocalAddressCast h u).symm a) a := by
  cases h
  rfl

section Local
variable {Z I K I' K' : Type*} {N : ℕ} (M : Fin N → ℕ) (B : ℕ)
  (steps : List (Option (I ⊕ K))) (steps' : List (Option (I' ⊕ K')))
  (h : fullMixedCommonShape M B steps = fullMixedCommonShape M B steps')
  (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps')))
  (θ : (Fin (Fintype.card (FullMixedCommonBirthAddress M B steps')) ×
    Fin (Fintype.card (FullMixedCommonBirthAddress M B steps'))) → ℝ)
  (encode : Z → ℤ)

theorem full_mixed_local_multiplier_shape_heq
    (u : Fin steps.length) (v : Fin steps'.length)
    (huv : Fin.cast (congrArg Sigma.fst h) u = v)
    (label : FullMixedCommonLocalAddress M B (steps.get u) → Option Z)
    (label' : FullMixedCommonLocalAddress M B (steps'.get v) → Option Z)
    (hl : HEq label label') :
    fullMixedCommonLocalOperationMultiplier M B steps
      (cast (congrArg (fun q => BirthForestCode (Fintype.card (FullMixedCommonShapeAddress M q))) h.symm) code)
      (birthFourierFrequencyCast (congrArg (fun q => Fintype.card (FullMixedCommonShapeAddress M q)) h) θ)
      encode u label =
    fullMixedCommonLocalOperationMultiplier M B steps' code θ encode v label' := by
  subst v
  rw [full_mixed_local_multiplier_shape, full_mixed_local_multiplier_shape]
  refine (full_mixed_shape_local_cast M h code θ encode u label).trans ?_
  congr 1
  funext a
  exact congr_heq hl (full_mixed_shape_address_symm_heq h u a)

theorem full_mixed_tagged_multiplier_shape_heq
    (u : Fin steps.length) (v : Fin steps'.length)
    (huv : Fin.cast (congrArg Sigma.fst h) u = v)
    (tag : Option (I ⊕ K)) (tag' : Option (I' ⊕ K'))
    (htag : steps.get u = tag) (htag' : steps'.get v = tag')
    (label : FullMixedCommonLocalAddress M B tag → Option Z)
    (label' : FullMixedCommonLocalAddress M B tag' → Option Z)
    (hl : HEq label label') :
    fullMixedCommonTaggedOperationMultiplier M B steps
      (cast (congrArg (fun q => BirthForestCode (Fintype.card (FullMixedCommonShapeAddress M q))) h.symm) code)
      (birthFourierFrequencyCast (congrArg (fun q => Fintype.card (FullMixedCommonShapeAddress M q)) h) θ)
      encode u tag htag label =
    fullMixedCommonTaggedOperationMultiplier M B steps' code θ encode v tag' htag' label' := by
  unfold fullMixedCommonTaggedOperationMultiplier
  apply full_mixed_local_multiplier_shape_heq M B steps steps' h code θ encode u v huv
  exact (birth_label_precomp_cast_heq _ label).trans
    (hl.trans (birth_label_precomp_cast_heq _ label').symm)

end Local
end Bounty

end

section

-- Original source module: PhysicalSelectedBirthPositions

/- Each birth-carrying tag in the actual fine schedule has a unique
position. This lets local forest multipliers depend on the original tag. -/

namespace Bounty

theorem physical_selected_fine_tag_visit {n : ℕ} (j : Fin (n + 1)) :
    physicalSelectedFineTag n (4 * j.val) = some (.inl j) := by
  have hj := j.isLt
  have hi : 4 * j.val < 4 * n + 1 := by omega
  have h0 : (4 * j.val) % 4 = 0 := by omega
  have hd : (4 * j.val) / 4 = j.val := by omega
  simp only [physicalSelectedFineTag, dif_pos hi, dif_pos h0]
  apply congrArg (fun k : Fin (n + 1) => some (Sum.inl k))
  exact Fin.ext hd

theorem physical_selected_fine_tag_edge {n : ℕ} (j : Fin n) :
    physicalSelectedFineTag n (4 * j.val + 2) = some (.inr j) := by
  have hj := j.isLt
  have hi : 4 * j.val + 2 < 4 * n + 1 := by omega
  have h0 : ¬ (4 * j.val + 2) % 4 = 0 := by omega
  have h2 : (4 * j.val + 2) % 4 = 2 := by omega
  have hd : (4 * j.val + 2) / 4 = j.val := by omega
  simp only [physicalSelectedFineTag, dif_pos hi, dif_neg h0, dif_pos h2]
  apply congrArg (fun k : Fin n => some (Sum.inr k))
  exact Fin.ext hd

theorem physical_selected_fine_visit_position {n i : ℕ} (j : Fin (n + 1))
    (h : physicalSelectedFineTag n i = some (.inl j)) : i = 4 * j.val := by
  unfold physicalSelectedFineTag at h
  split_ifs at h with hi h0 h2
  · have hv := congrArg Fin.val (Sum.inl.inj (Option.some.inj h))
    dsimp only at hv
    omega
  · cases h

theorem physical_selected_fine_edge_position {n i : ℕ} (j : Fin n)
    (h : physicalSelectedFineTag n i = some (.inr j)) : i = 4 * j.val + 2 := by
  unfold physicalSelectedFineTag at h
  split_ifs at h with hi h0 h2
  · cases h
  · have hv := congrArg Fin.val (Sum.inr.inj (Option.some.inj h))
    dsimp only at hv
    omega

def physicalSelectedVisitPosition {n : ℕ} (j : Fin (n + 1)) :
    Fin ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)).length :=
  ⟨4 * j.val, by simp only [List.length_map, List.length_range]; omega⟩

def physicalSelectedEdgePosition {n : ℕ} (j : Fin n) :
    Fin ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)).length :=
  ⟨4 * j.val + 2, by simp only [List.length_map, List.length_range]; omega⟩

theorem physical_selected_visit_get {n : ℕ} (j : Fin (n + 1)) :
    ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)).get
      (physicalSelectedVisitPosition j) = some (.inl j) := by
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range,
    physicalSelectedVisitPosition, physical_selected_fine_tag_visit]

theorem physical_selected_edge_get {n : ℕ} (j : Fin n) :
    ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)).get
      (physicalSelectedEdgePosition j) = some (.inr j) := by
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range,
    physicalSelectedEdgePosition, physical_selected_fine_tag_edge]

end Bounty

end

section

-- Original source module: FullMixedEmptyMultiplier

/- A permutation occurrence has no birth slots and hence no forest factor. -/

open Finset
open scoped Classical
namespace Bounty
section Empty
variable {J K Z : Type*} {N : ℕ} (M : Fin N → ℕ) (B : ℕ)
  (steps : List (Option (J ⊕ K)))
  (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
  (u : Fin steps.length) (htag : steps.get u = none)

include htag

theorem full_mixed_empty_operation_unaffected :
    u.succ ∉ birthForestAffectedOperations code (fullMixedCommonIndexStage M B steps) := by
  let _ : DecidableEq (Fin (steps.length + 1)) := fun a b => Classical.propDecidable (a = b)
  intro h
  unfold birthForestAffectedOperations at h
  obtain ⟨i, _, hi⟩ := mem_image.mp h
  obtain ⟨a, _⟩ := (full_mixed_common_index_stage_succ_iff M B steps u i).mp hi
  let az : FullMixedCommonLocalAddress (J := J) (K := K) M B none :=
    cast (congrArg (FullMixedCommonLocalAddress M B) htag) a
  exact Fin.elim0 az.2

theorem full_mixed_empty_operation_multiplier
    (θ : (Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress M B steps))) → ℝ)
    (encode : Z → ℤ)
    (label : FullMixedCommonLocalAddress M B (steps.get u) → Option Z) :
    fullMixedCommonLocalOperationMultiplier M B steps code θ encode u label = 1 :=
  full_mixed_common_local_multiplier_untouched M B steps code θ encode u label
    (full_mixed_empty_operation_unaffected M B steps code u htag)

end Empty
end Bounty

end

section

-- Original source module: PhysicalSelectedBirthMultiplier

/- The actual fine-schedule forest factor is an ordinary local tag
multiplier. Its permutation factors are exactly one. -/

namespace Bounty
section Multiplier
variable {Z : Type*} {N : ℕ} (M : Fin N → ℕ) (B n : ℕ)
  (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B
    ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)))))
  (θ : (Fin (Fintype.card (FullMixedCommonBirthAddress M B
      ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)))) ×
    Fin (Fintype.card (FullMixedCommonBirthAddress M B
      ((List.range (4 * n + 1)).map (physicalSelectedFineTag n))))) → ℝ)
  (encode : Z → ℤ)

noncomputable def physicalSelectedBirthMultiplier :
    (tag : Option (Fin (n + 1) ⊕ Fin n)) →
      (FullMixedCommonLocalAddress M B tag → Option Z) → ℂ
  | none, _ => 1
  | some (.inl j), label =>
    fullMixedCommonTaggedOperationMultiplier M B
      ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) code θ encode
      (physicalSelectedVisitPosition j) (some (.inl j)) (physical_selected_visit_get j) label
  | some (.inr j), label =>
    fullMixedCommonTaggedOperationMultiplier M B
      ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) code θ encode
      (physicalSelectedEdgePosition j) (some (.inr j)) (physical_selected_edge_get j) label

theorem physical_selected_birth_multiplier_norm_le
    (tag : Option (Fin (n + 1) ⊕ Fin n))
    (label : FullMixedCommonLocalAddress M B tag → Option Z) :
    ‖physicalSelectedBirthMultiplier M B n code θ encode tag label‖ ≤ 1 := by
  cases tag with
  | none => exact (norm_one : ‖(1 : ℂ)‖ = 1).le
  | some tag =>
    cases tag with
    | inl j =>
      exact full_mixed_common_tagged_multiplier_norm_le M B _ code θ encode
        (physicalSelectedVisitPosition j) _ (physical_selected_visit_get j) label
    | inr j =>
      exact full_mixed_common_tagged_multiplier_norm_le M B _ code θ encode
        (physicalSelectedEdgePosition j) _ (physical_selected_edge_get j) label

theorem physical_selected_birth_multiplier_tagged
    (u : Fin ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)).length)
    (tag : Option (Fin (n + 1) ⊕ Fin n))
    (htag : ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)).get u = tag)
    (label : FullMixedCommonLocalAddress M B tag → Option Z) :
    physicalSelectedBirthMultiplier M B n code θ encode tag label =
      fullMixedCommonTaggedOperationMultiplier M B
        ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) code θ encode u tag htag label := by
  cases tag with
  | none =>
    dsimp only [physicalSelectedBirthMultiplier, fullMixedCommonTaggedOperationMultiplier]
    exact (full_mixed_empty_operation_multiplier M B _ code u htag θ encode _).symm
  | some tag =>
    cases tag with
    | inl j =>
      have hu : u = physicalSelectedVisitPosition j := by
        apply Fin.ext
        change u.val = 4 * j.val
        apply physical_selected_fine_visit_position j
        simpa only [List.get_eq_getElem, List.getElem_map, List.getElem_range] using htag
      subst u
      rfl
    | inr j =>
      have hu : u = physicalSelectedEdgePosition j := by
        apply Fin.ext
        change u.val = 4 * j.val + 2
        apply physical_selected_fine_edge_position j
        simpa only [List.get_eq_getElem, List.getElem_map, List.getElem_range] using htag
      subst u
      rfl

theorem physical_selected_birth_multiplier_at_occurrence
    (u : Fin ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)).length)
    (label : FullMixedCommonLocalAddress M B
      (((List.range (4 * n + 1)).map (physicalSelectedFineTag n)).get u) → Option Z) :
    physicalSelectedBirthMultiplier M B n code θ encode
        (((List.range (4 * n + 1)).map (physicalSelectedFineTag n)).get u) label =
      fullMixedCommonLocalOperationMultiplier M B
        ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) code θ encode u label :=
  physical_selected_birth_multiplier_tagged M B n code θ encode u _ rfl label

end Multiplier
end Bounty

end

section

-- Original source module: PhysicalSelectedPlannedBirth

/- Every fixed-plan birth factor on the actual selected schedule equals
the plan-independent multiplier for its original event tag. -/

namespace Bounty
section Planned
variable {Z S I : Type} {Ps : S → Finset ℕ} {J ell N : ℕ}
  (M : Fin N → ℕ) (B n : ℕ)
  (L : PhysicalMarkLists Ps J ell)
  (pl : PhysicalMixedSmallPlan (I := I)
    ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)))
  (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B
    ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)))))
  (θ : (Fin (Fintype.card (FullMixedCommonBirthAddress M B
      ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)))) ×
    Fin (Fintype.card (FullMixedCommonBirthAddress M B
      ((List.range (4 * n + 1)).map (physicalSelectedFineTag n))))) → ℝ)
  (encode : Z → ℤ)

theorem physical_selected_planned_birth_multiplier
    (u : Fin (physicalMixedBigSteps
      ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl).length)
    (tag : Option (Fin (n + 1) ⊕
      PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := Fin n)))
    (htag : (physicalMixedBigSteps
      ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl).get u = tag)
    (label : FullMixedCommonLocalAddress M B tag → Option Z) :
    fullMixedCommonTaggedOperationMultiplier M B
      (physicalMixedBigSteps ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl)
      ((physicalMixedCommonForestEquiv M B
        ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl).symm code)
      (physicalMixedCommonFrequency M B
        ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl θ)
      encode u tag htag label =
    physicalSelectedBirthMultiplier M B n code θ encode (physicalMixedBigTagErase tag)
      (fun a => label (physicalMixedTagBirthAddressEquiv M B tag a)) := by
  let ks := (List.range (4 * n + 1)).map (physicalSelectedFineTag n)
  let v : Fin ks.length :=
    Fin.cast (congrArg Sigma.fst (physical_mixed_big_common_shape M B ks L pl)) u
  have hv : ks.get v = physicalMixedBigTagErase tag := by
    calc
      _ = physicalMixedBigTagErase ((physicalMixedBigSteps ks L pl).get u) :=
        (physical_mixed_big_tag_at_position M B ks L pl u).symm
      _ = _ := congrArg physicalMixedBigTagErase htag
  have h := full_mixed_tagged_multiplier_shape_heq M B
    (physicalMixedBigSteps ks L pl) ks (physical_mixed_big_common_shape M B ks L pl)
    code θ encode u v rfl tag (physicalMixedBigTagErase tag) htag hv label
    (fun a => label (physicalMixedTagBirthAddressEquiv M B tag a))
    (physical_mixed_erased_birth_label_heq M B tag label)
  exact h.trans (physical_selected_birth_multiplier_tagged M B n code θ encode v
    (physicalMixedBigTagErase tag) hv
    (fun a => label (physicalMixedTagBirthAddressEquiv M B tag a))).symm

end Planned
end Bounty

end

section

-- Original source module: FullMixedCommonForestRows

/- Common forest Fourier rows have no root-dependent avoidance gate; the initial phase remains a separate boundary multiplier. -/

open Finset Classical
namespace Bounty
section Phase
variable {J K : Type*} {N : ℕ} {P : Fin N → Type*} {M : Fin N → ℕ}
  (n : (g : Fin N) → P g → ℕ) (S : K → (g : Fin N) → Finset (Fin (M g))) (B : ℕ)
  (A : ∀ k, SharedActiveLabels P (S k) → Type*)
  (Δ D : ∀ k c, A k c → Fin N → ℤ) (steps : List (Option (J ⊕ K)))
  (residual : ∀ (tag : Option (J ⊕ K)) s, FullPermutationMixedEvent n S B A Δ D tag s → ℂ)
  (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
  (θ : (Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) ×
    Fin (Fintype.card (FullMixedCommonBirthAddress M B steps))) → ℝ)
  (encode : Sigma P → ℤ)

noncomputable def fullMixedCommonForestStagePhase (u : Fin steps.length)
    (s : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (e : FullPermutationMixedEvent n S B A Δ D (steps.get u) s) : ℂ :=
  residual (steps.get u) s e * fullMixedCommonLocalOperationMultiplier M B steps code θ encode u
    (fullMixedCommonEventBirthLabel n S B A Δ D (steps.get u) s e)

theorem full_mixed_common_forest_stage_norm_le
    (hresidual : ∀ tag s e, ‖residual tag s e‖ ≤ 1) (u : Fin steps.length)
    (s : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (e : FullPermutationMixedEvent n S B A Δ D (steps.get u) s) :
    ‖fullMixedCommonForestStagePhase n S B A Δ D steps residual code θ encode u s e‖ ≤ 1 := by
  rw [fullMixedCommonForestStagePhase, norm_mul]
  exact mul_le_one₀ (hresidual _ _ _) (norm_nonneg _)
    (full_mixed_common_local_multiplier_norm_le M B steps code θ encode u _)

theorem full_mixed_common_forest_stage_untouched (u : Fin steps.length)
    (hu : u.succ ∉ birthForestAffectedOperations code (fullMixedCommonIndexStage M B steps))
    (s : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (e : FullPermutationMixedEvent n S B A Δ D (steps.get u) s) :
    fullMixedCommonForestStagePhase n S B A Δ D steps residual code θ encode u s e = residual (steps.get u) s e := by
  rw [fullMixedCommonForestStagePhase, full_mixed_common_local_multiplier_untouched M B steps code θ encode u _ hu, mul_one]

variable [∀ g, Fintype (P g)] [∀ g p, NeZero (n g p)] [∀ k c, Fintype (A k c)]
  (ω : ∀ k c, A k c → ℝ) (μ : ∀ g, P g → ℝ) (q : J → ℝ) (ρ : ℝ) (V : Fin N → ℝ)

noncomputable def fullMixedCommonForestStageRow (u : Fin steps.length)
    (f : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B → ℂ)
    (s : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) : ℂ :=
  let _ := fullPermutationMixedEventFintype n S B A Δ D (steps.get u) s
  ∑ e : FullPermutationMixedEvent n S B A Δ D (steps.get u) s,
    (fullPermutationMixedEventWeight n S B A Δ D ω μ q ρ V (steps.get u) s e : ℂ) *
      fullMixedCommonForestStagePhase n S B A Δ D steps residual code θ encode u s e *
      f (fullPermutationMixedEventTarget n S B A Δ D (steps.get u) s e)

end Phase
end Bounty

end

section

-- Original source module: PhysicalSelectedDecoratedPhase

/- All fixed-plan Fourier factors on the selected schedule are a
single ordinary decorated local phase, suitable for small-plan packing. -/

open Finset
namespace Bounty
section Phase
variable {S I : Type} {Ps : S → Finset ℕ} {J ell N n : ℕ} {P : Fin N → Type}
  (sizes : ∀ g, P g → ℕ) {M : Fin N → ℕ}

variable (shared : (PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := Fin n)) → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (aux : ∀ k, SharedActiveLabels P (shared k) → Type)
  (Δ D : ∀ k c, aux k c → Fin N → ℤ)
  (residual : ∀ (tag : Option (Fin (n + 1) ⊕ (PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := Fin n)))) x,
    FullPermutationMixedEvent sizes shared B aux Δ D tag x → ℂ)
  (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B
    ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)))))
  (θ : (Fin (Fintype.card (FullMixedCommonBirthAddress M B
      ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)))) ×
    Fin (Fintype.card (FullMixedCommonBirthAddress M B
      ((List.range (4 * n + 1)).map (physicalSelectedFineTag n))))) → ℝ)
  (encode : Sigma P → ℤ)

noncomputable def physicalSelectedDecoratedPhase
    (tag : Option (Fin (n + 1) ⊕ (PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := Fin n))))
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (sizes g)) M B)
    (event : FullPermutationMixedEvent sizes shared B aux Δ D tag x) : ℂ :=
  residual tag x event * physicalSelectedBirthMultiplier M B n code θ encode
    (physicalMixedBigTagErase tag)
    (fun a => fullMixedCommonEventBirthLabel (J := Fin (n + 1)) (K := (PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := Fin n))) (P := P) (M := M) sizes shared B aux Δ D tag x event
      (physicalMixedTagBirthAddressEquiv M B tag a))

theorem physical_selected_decorated_phase_at_position
    (L : PhysicalMarkLists Ps J ell)
    (pl : PhysicalMixedSmallPlan (I := I)
      ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)))
    (u : Fin (physicalMixedBigSteps
      ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl).length)
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (sizes g)) M B)
    (event : FullPermutationMixedEvent sizes shared B aux Δ D
      ((physicalMixedBigSteps ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl).get u) x) :
    fullMixedCommonForestStagePhase (J := Fin (n + 1)) (K := (PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := Fin n))) (P := P) (M := M) sizes shared B aux Δ D
      (physicalMixedBigSteps ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl)
      residual ((physicalMixedCommonForestEquiv M B
        ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl).symm code)
      (physicalMixedCommonFrequency M B
        ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl θ) encode u x event =
    physicalSelectedDecoratedPhase sizes shared B aux Δ D residual code θ encode _ x event := by
  unfold fullMixedCommonForestStagePhase physicalSelectedDecoratedPhase
  apply congrArg (fun z : ℂ => residual _ x event * z)
  exact physical_selected_planned_birth_multiplier M B n L pl code θ encode u _ rfl
    (fullMixedCommonEventBirthLabel (J := Fin (n + 1)) (K := (PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := Fin n))) (P := P) (M := M) sizes shared B aux Δ D _ x event)

theorem physical_selected_decorated_phase_product
    (L : PhysicalMarkLists Ps J ell)
    (pl : PhysicalMixedSmallPlan (I := I)
      ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)))
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (sizes g)) M B)
    (p : FullPermutationMixedPath sizes shared B aux Δ D
      (physicalMixedBigSteps ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl) x) :
    (∏ u : Fin (physicalMixedBigSteps
        ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl).length,
      let event := finiteEventPathOccurrence (FullPermutationMixedEvent sizes shared B aux Δ D)
        (fullPermutationMixedEventTarget sizes shared B aux Δ D)
        (physicalMixedBigSteps ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl) x p u
      fullMixedCommonForestStagePhase (J := Fin (n + 1)) (K := (PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := Fin n))) (P := P) (M := M) sizes shared B aux Δ D
        (physicalMixedBigSteps ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl)
        residual ((physicalMixedCommonForestEquiv M B
          ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl).symm code)
        (physicalMixedCommonFrequency M B
          ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl θ) encode u event.1 event.2) =
    finiteEventLocalPhase (FullPermutationMixedEvent sizes shared B aux Δ D)
      (fullPermutationMixedEventTarget sizes shared B aux Δ D)
      (physicalSelectedDecoratedPhase sizes shared B aux Δ D residual code θ encode)
      (physicalMixedBigSteps ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl) x p := by
  rw [finite_event_local_phase_occurrences]
  apply prod_congr rfl
  intro u _
  exact physical_selected_decorated_phase_at_position sizes shared B aux Δ D residual
    code θ encode L pl u _ _

end Phase
end Bounty

end

section

-- Original source module: FullMixedCommonPhaseProduct

/- The exact phase product keeps the common initial phase at the boundary and attaches every later phase to its original event. -/

open Finset Classical
namespace Bounty
section Product
variable {J K : Type*} {N : ℕ} {P : Fin N → Type*} {M : Fin N → ℕ}
  (n : (g : Fin N) → P g → ℕ) (S : K → (g : Fin N) → Finset (Fin (M g))) (B : ℕ)
  (A : ∀ k, SharedActiveLabels P (S k) → Type*)
  (Δ D : ∀ k c, A k c → Fin N → ℤ) (steps : List (Option (J ⊕ K)))
  (residual : ∀ (tag : Option (J ⊕ K)) s, FullPermutationMixedEvent n S B A Δ D tag s → ℂ)
  (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
  (θ : (Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) ×
    Fin (Fintype.card (FullMixedCommonBirthAddress M B steps))) → ℝ)
  (encode : Sigma P → ℤ)
  (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
  (p : FullPermutationMixedPath n S B A Δ D steps x)

theorem full_mixed_common_phase_product :
    fullMixedCommonBoundaryMultiplier M B steps code θ encode (fullMixedCommonInitialPrime x) *
      (∏ u : Fin steps.length,
        let e := finiteEventPathOccurrence (FullPermutationMixedEvent n S B A Δ D)
          (fullPermutationMixedEventTarget n S B A Δ D) steps x p u
        fullMixedCommonForestStagePhase n S B A Δ D steps residual code θ encode u e.1 e.2) =
      finiteEventLocalPhase (FullPermutationMixedEvent n S B A Δ D)
        (fullPermutationMixedEventTarget n S B A Δ D) residual steps x p *
      (if ∀ i ∈ birthForestTouched code, fullMixedCommonIndexedPerformed n S B A Δ D steps x p i then
        ∏ i, physicalReturnPhase (birthForestLocalFrequency code θ i)
          (fullMixedCommonIndexedValue n S B A Δ D steps encode x p i) else 0) := by
  simp only [fullMixedCommonForestStagePhase]
  rw [prod_mul_distrib, ← finite_event_local_phase_occurrences]
  rw [mul_left_comm]
  rw [full_mixed_common_boundary_event_product n S B A Δ D steps x p code θ encode]

end Product
end Bounty

end

section

-- Original source module: FullMixedWeightedForestFourier

/- Common forest Fourier expansion with an arbitrary path-dependent
factor. In particular, the exact small-plan factor stays inside the sum. -/

open Finset Classical MeasureTheory
namespace Bounty
section Weighted
variable {I K Ω : Type*} {N : ℕ} {P : Fin N → Type*}
  (n : ∀ g, P g → ℕ) {M : Fin N → ℕ}
  (S : K → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (A : ∀ k, SharedActiveLabels P (S k) → Type*)
  (Δ D : ∀ k c, A k c → Fin N → ℤ)
  (edgePhase : ∀ k, ((g : Fin N) → Finset (P g)) →
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) →
    FullActiveEdgeEvent n (S k) B (A k) (Δ k) (D k) x → ℂ)
  (ω : ∀ k c, A k c → ℝ) (μ : ∀ g, P g → ℝ) (q : I → ℝ) (ρ : ℝ) (V : Fin N → ℝ)
  (steps : List (Option (I ⊕ K)))

theorem full_mixed_weighted_forest_fourier
    (paths : Finset Ω)
    (x : Ω → ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (p : ∀ a, FullPermutationMixedPath n S B A Δ D steps (x a)) (F : Ω → ℂ)
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
    (encode : Sigma P → ℤ) :
    birthForestPathSum paths
      (fun a => F a * fullMixedCommonResidualWeight n S B A Δ D edgePhase ω μ q ρ V steps (x a) (p a))
      (fun a => fullMixedCommonIndexedPerformed n S B A Δ D steps (x a) (p a))
      (fun a => fullMixedCommonIndexedValue n S B A Δ D steps encode (x a) (p a)) code =
    ∫ θ, ∑ a ∈ paths,
      F a * (finiteEventPathWeight (FullPermutationMixedEvent n S B A Δ D)
        (fullPermutationMixedEventTarget n S B A Δ D)
        (fullPermutationMixedEventWeight n S B A Δ D ω μ q ρ V) steps (x a) (p a) : ℂ) *
      fullMixedCommonBoundaryMultiplier M B steps code θ encode (fullMixedCommonInitialPrime (x a)) *
      (∏ u : Fin steps.length,
        let event := finiteEventPathOccurrence (FullPermutationMixedEvent n S B A Δ D)
          (fullPermutationMixedEventTarget n S B A Δ D) steps (x a) (p a) u
        fullMixedCommonForestStagePhase n S B A Δ D steps
          (fullMixedBirthResidualPhase n S B A Δ D edgePhase) code θ encode u event.1 event.2)
      ∂birthFourierCubeMeasure (Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) ×
        Fin (Fintype.card (FullMixedCommonBirthAddress M B steps))) := by
  rw [← birthForestPathSum_fourier_integral]
  apply integral_congr_ae
  filter_upwards [] with θ
  apply sum_congr rfl
  intro a _
  have hp := congrArg
    (fun z : ℂ => F a * (finiteEventPathWeight (FullPermutationMixedEvent n S B A Δ D)
      (fullPermutationMixedEventTarget n S B A Δ D)
      (fullPermutationMixedEventWeight n S B A Δ D ω μ q ρ V) steps (x a) (p a) : ℂ) * z)
    (full_mixed_common_phase_product n S B A Δ D steps
      (fullMixedBirthResidualPhase n S B A Δ D edgePhase) code θ encode (x a) (p a))
  unfold fullMixedCommonResidualWeight
  split_ifs at hp ⊢ <;> convert hp.symm using 1 <;> ring

end Weighted
end Bounty

end

section

-- Original source module: BirthForestFourierIntegrable

/- Forest Fourier integrands are integrable even with arbitrary finite
path weights. This permits the actual small-plan sum inside one integral. -/

open Finset MeasureTheory
open scoped Classical
namespace Bounty

theorem birth_forest_fourier_integrable {Ω : Type*} {n : ℕ}
    (paths : Finset Ω) (w : Ω → ℂ) (performed : Ω → Fin n → Prop)
    (f : Ω → Fin n → ℤ) (code : BirthForestCode n) :
    Integrable (fun θ : (Fin n × Fin n) → ℝ =>
      ∑ a ∈ paths, if ∀ i ∈ birthForestTouched code, performed a i then
        w a * ∏ i, physicalReturnPhase (birthForestLocalFrequency code θ i) (f a i) else 0)
      (birthFourierCubeMeasure (Fin n × Fin n)) := by
  apply integrable_finsetSum
  intro a _
  by_cases h : ∀ i ∈ birthForestTouched code, performed a i
  · simp only [if_pos h]
    have hi := (birth_fourier_cube_phase_integrable (birthForestEdgeDifference code (f a))).const_mul (w a)
    simpa only [birthForestEdgeDifference_phase_product] using hi
  · simp only [if_neg h]
    exact integrable_zero _ _ _

theorem birth_fourier_integrable_card_transport {m n : ℕ} (h : m = n)
    (F : ((Fin m × Fin m) → ℝ) → ℂ)
    (hF : Integrable F (birthFourierCubeMeasure (Fin m × Fin m))) :
    Integrable (fun θ => F (birthFourierFrequencyCast h θ))
      (birthFourierCubeMeasure (Fin n × Fin n)) := by
  cases h
  exact hF

end Bounty

end

section

-- Original source module: FullMixedWeightedFourierIntegrable

/- The exact weighted local Fourier sum is integrable, allowing all
small-plan and pattern sums to remain inside its common integral. -/

open Finset Classical MeasureTheory
namespace Bounty
section Weighted
variable {I K Ω : Type*} {N : ℕ} {P : Fin N → Type*}
  (n : ∀ g, P g → ℕ) {M : Fin N → ℕ}
  (S : K → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (A : ∀ k, SharedActiveLabels P (S k) → Type*)
  (Δ D : ∀ k c, A k c → Fin N → ℤ)
  (edgePhase : ∀ k, ((g : Fin N) → Finset (P g)) →
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) →
    FullActiveEdgeEvent n (S k) B (A k) (Δ k) (D k) x → ℂ)
  (ω : ∀ k c, A k c → ℝ) (μ : ∀ g, P g → ℝ) (q : I → ℝ) (ρ : ℝ) (V : Fin N → ℝ)
  (steps : List (Option (I ⊕ K)))


theorem full_mixed_weighted_fourier_integrable
    (paths : Finset Ω)
    (x : Ω → ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (p : ∀ a, FullPermutationMixedPath n S B A Δ D steps (x a)) (F : Ω → ℂ)
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B steps)))
    (encode : Sigma P → ℤ) :
    Integrable (fun θ => ∑ a ∈ paths,
      F a * (finiteEventPathWeight (FullPermutationMixedEvent n S B A Δ D)
        (fullPermutationMixedEventTarget n S B A Δ D)
        (fullPermutationMixedEventWeight n S B A Δ D ω μ q ρ V) steps (x a) (p a) : ℂ) *
      fullMixedCommonBoundaryMultiplier M B steps code θ encode (fullMixedCommonInitialPrime (x a)) *
      (∏ u : Fin steps.length,
        let event := finiteEventPathOccurrence (FullPermutationMixedEvent n S B A Δ D)
          (fullPermutationMixedEventTarget n S B A Δ D) steps (x a) (p a) u
        fullMixedCommonForestStagePhase n S B A Δ D steps
          (fullMixedBirthResidualPhase n S B A Δ D edgePhase) code θ encode u event.1 event.2))
      (birthFourierCubeMeasure (Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)) ×
        Fin (Fintype.card (FullMixedCommonBirthAddress M B steps)))) := by
  have hi := birth_forest_fourier_integrable paths
    (fun a => F a * fullMixedCommonResidualWeight n S B A Δ D edgePhase ω μ q ρ V steps (x a) (p a))
    (fun a => fullMixedCommonIndexedPerformed n S B A Δ D steps (x a) (p a))
    (fun a => fullMixedCommonIndexedValue n S B A Δ D steps encode (x a) (p a)) code
  apply hi.congr
  filter_upwards [] with θ
  apply sum_congr rfl
  intro a _
  have hp := congrArg
    (fun z : ℂ => F a * (finiteEventPathWeight (FullPermutationMixedEvent n S B A Δ D)
      (fullPermutationMixedEventTarget n S B A Δ D)
      (fullPermutationMixedEventWeight n S B A Δ D ω μ q ρ V) steps (x a) (p a) : ℂ) * z)
    (full_mixed_common_phase_product n S B A Δ D steps
      (fullMixedBirthResidualPhase n S B A Δ D edgePhase) code θ encode (x a) (p a))
  unfold fullMixedCommonResidualWeight
  split_ifs at hp ⊢ <;> convert hp.symm using 1 <;> ring

end Weighted
end Bounty

end

section

-- Original source module: OptionalForestPathEncoding

/- An injective integer encoding preserves each optional-label forest
path sum, including arbitrary path-dependent weights. -/

open Finset
open scoped Classical
namespace Bounty

theorem optional_forest_path_sum_encoding {Ω α : Type*} {m : ℕ}
    (paths : Finset Ω) (w : Ω → ℂ)
    (performed : Ω → Fin m → Prop) (label : Ω → Fin m → Option α)
    (hp : ∀ a ∈ paths, ∀ i, performed a i → (label a i).isSome = true)
    (encode : α → ℤ) (hinj : Function.Injective encode) (code : BirthForestCode m) :
    birthForestPathSum paths w performed label code =
      birthForestPathSum paths w performed (fun a i => ((label a i).map encode).getD 0) code := by
  unfold birthForestPathSum
  apply sum_congr rfl
  intro a ha
  rw [optional_forest_encoding_iff (performed a) (label a) (hp a ha) encode hinj code]

end Bounty

end

section

-- Original source module: PhysicalSelectedPlanFourier

/- Each optional-label forest on an actual fixed small plan has an
exact Fourier expansion on the common original cube. The arbitrary
path factor stays inside the sum. -/

open Finset MeasureTheory
open scoped Classical
namespace Bounty
section Fourier
variable {S I Ω : Type} {Ps : S → Finset ℕ} {J ell N n : ℕ} {P : Fin N → Type}
  (sizes : ∀ g, P g → ℕ) {M : Fin N → ℕ}

variable (shared : (PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := Fin n)) → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (aux : ∀ k, SharedActiveLabels P (shared k) → Type)
  (Δ D : ∀ k c, aux k c → Fin N → ℤ)
  (edgePhase : ∀ k, ((g : Fin N) → Finset (P g)) →
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (sizes g)) M B) →
    FullActiveEdgeEvent sizes (shared k) B (aux k) (Δ k) (D k) x → ℂ)
  (ω : ∀ k c, aux k c → ℝ) (μ : ∀ g, P g → ℝ)
  (q : Fin (n + 1) → ℝ) (ρ : ℝ) (V : Fin N → ℝ)

theorem physical_selected_plan_forest_fourier
    (L : PhysicalMarkLists Ps J ell)
    (pl : PhysicalMixedSmallPlan (I := I)
      ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)))
    (paths : Finset Ω)
    (x : Ω → ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (sizes g)) M B)
    (p : ∀ a, FullPermutationMixedPath sizes shared B aux Δ D
      (physicalMixedBigSteps ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl) (x a))
    (F : Ω → ℂ) (encode : Sigma P → ℤ) (hinj : Function.Injective encode)
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B
      ((List.range (4 * n + 1)).map (physicalSelectedFineTag n))))) :
    let ks := (List.range (4 * n + 1)).map (physicalSelectedFineTag n)
    let steps := physicalMixedBigSteps ks L pl
    birthForestPathSum paths
      (fun a => F a * fullMixedCommonResidualWeight sizes shared B aux Δ D edgePhase ω μ q ρ V steps (x a) (p a))
      (fun a => fullMixedCommonIndexedPerformed sizes shared B aux Δ D steps (x a) (p a))
      (fun a i => fullMixedCommonBirthLabel sizes shared B aux Δ D steps (x a) (p a)
        (fullMixedCommonBirthOrder M B steps i))
      ((physicalMixedCommonForestEquiv M B ks L pl).symm code) =
    ∫ θ, ∑ a ∈ paths,
      F a * (finiteEventPathWeight (FullPermutationMixedEvent sizes shared B aux Δ D)
        (fullPermutationMixedEventTarget sizes shared B aux Δ D)
        (fullPermutationMixedEventWeight sizes shared B aux Δ D ω μ q ρ V) steps (x a) (p a) : ℂ) *
      fullMixedCommonBoundaryMultiplier M B ks code θ encode (fullMixedCommonInitialPrime (x a)) *
      finiteEventLocalPhase (FullPermutationMixedEvent sizes shared B aux Δ D)
        (fullPermutationMixedEventTarget sizes shared B aux Δ D)
        (physicalSelectedDecoratedPhase sizes shared B aux Δ D
          (fullMixedBirthResidualPhase sizes shared B aux Δ D edgePhase) code θ encode)
        steps (x a) (p a)
      ∂birthFourierCubeMeasure (Fin (Fintype.card (FullMixedCommonBirthAddress M B ks)) ×
        Fin (Fintype.card (FullMixedCommonBirthAddress M B ks))) := by
  dsimp only
  have henc := optional_forest_path_sum_encoding paths
    (fun a => F a * fullMixedCommonResidualWeight sizes shared B aux Δ D edgePhase ω μ q ρ V
      (physicalMixedBigSteps ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl) (x a) (p a))
    (fun a => fullMixedCommonIndexedPerformed sizes shared B aux Δ D
      (physicalMixedBigSteps ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl) (x a) (p a))
    (fun a i => fullMixedCommonBirthLabel sizes shared B aux Δ D
      (physicalMixedBigSteps ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl) (x a) (p a)
      (fullMixedCommonBirthOrder M B
        (physicalMixedBigSteps ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl) i))
    (fun _ _ _ hi => hi) encode hinj ((physicalMixedCommonForestEquiv M B
      ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl).symm code)
  rw [henc]
  change birthForestPathSum paths _ _
    (fun a => fullMixedCommonIndexedValue sizes shared B aux Δ D
      (physicalMixedBigSteps ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl)
      encode (x a) (p a)) _ = _
  rw [full_mixed_weighted_forest_fourier]
  rw [birth_fourier_integral_card_transport (physical_mixed_big_common_card M B
    ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl)]
  apply integral_congr_ae
  filter_upwards [] with θ
  apply sum_congr rfl
  intro a _
  change _ * fullMixedCommonBoundaryMultiplier M B _ _
    (physicalMixedCommonFrequency M B
      ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl θ) _ _ * _ = _
  rw [physical_mixed_common_boundary_multiplier]
  congr 1
  exact physical_selected_decorated_phase_product sizes shared B aux Δ D
    (fullMixedBirthResidualPhase sizes shared B aux Δ D edgePhase) code θ encode L pl (x a) (p a)

theorem physical_selected_plan_fourier_integrable
    (L : PhysicalMarkLists Ps J ell)
    (pl : PhysicalMixedSmallPlan (I := I)
      ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)))
    (paths : Finset Ω)
    (x : Ω → ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (sizes g)) M B)
    (p : ∀ a, FullPermutationMixedPath sizes shared B aux Δ D
      (physicalMixedBigSteps ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl) (x a))
    (F : Ω → ℂ) (encode : Sigma P → ℤ)
    (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B
      ((List.range (4 * n + 1)).map (physicalSelectedFineTag n))))) :
    let ks := (List.range (4 * n + 1)).map (physicalSelectedFineTag n)
    let steps := physicalMixedBigSteps ks L pl
    Integrable (fun θ => ∑ a ∈ paths,
      F a * (finiteEventPathWeight (FullPermutationMixedEvent sizes shared B aux Δ D)
        (fullPermutationMixedEventTarget sizes shared B aux Δ D)
        (fullPermutationMixedEventWeight sizes shared B aux Δ D ω μ q ρ V) steps (x a) (p a) : ℂ) *
      fullMixedCommonBoundaryMultiplier M B ks code θ encode (fullMixedCommonInitialPrime (x a)) *
      finiteEventLocalPhase (FullPermutationMixedEvent sizes shared B aux Δ D)
        (fullPermutationMixedEventTarget sizes shared B aux Δ D)
        (physicalSelectedDecoratedPhase sizes shared B aux Δ D
          (fullMixedBirthResidualPhase sizes shared B aux Δ D edgePhase) code θ encode)
        steps (x a) (p a))
      (birthFourierCubeMeasure (Fin (Fintype.card (FullMixedCommonBirthAddress M B ks)) ×
        Fin (Fintype.card (FullMixedCommonBirthAddress M B ks)))) := by
  dsimp only
  have hn := full_mixed_weighted_fourier_integrable sizes shared B aux Δ D edgePhase ω μ q ρ V
    (physicalMixedBigSteps ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl)
    paths x p F ((physicalMixedCommonForestEquiv M B
      ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl).symm code) encode
  have hc := birth_fourier_integrable_card_transport (physical_mixed_big_common_card M B
    ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl) _ hn
  apply hc.congr
  filter_upwards [] with θ
  apply sum_congr rfl
  intro a _
  change _ * fullMixedCommonBoundaryMultiplier M B _ _
    (physicalMixedCommonFrequency M B
      ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) L pl θ) _ _ * _ = _
  rw [physical_mixed_common_boundary_multiplier]
  congr 1
  exact physical_selected_decorated_phase_product sizes shared B aux Δ D
    (fullMixedBirthResidualPhase sizes shared B aux Δ D edgePhase) code θ encode L pl (x a) (p a)

end Fourier
end Bounty

end

section

-- Original source module: PhysicalRootPlanFourier

/- The original fixed-plan root forest is the exact common-cube Fourier
integral, retaining its actual small-plan factor and original coefficient. -/

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

noncomputable def physicalRootPlanFourierIntegrand
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
  let F := fun path : FullPermutationMixedPath sizes shared B aux delta displacement steps x =>
    physicalEffectivePlanSmallFactor (fun (i : patterns) g => C i.val (e.symm g).val)
      (fun (j : Fin (n + 1)) (i : patterns) => k (n - j.val) i.val) B
      (fun s : ↥groupsᶜ => V s.val) (fun _ => q)
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
      (physicalGroupResidueVector r) pl.1 pl.2 x path *
    f (finiteEventPathTerminal (FullPermutationMixedEvent sizes shared B aux delta displacement)
      (fullPermutationMixedEventTarget sizes shared B aux delta displacement) steps x path)
  ∑ path : FullPermutationMixedPath sizes shared B aux delta displacement steps x,
    F path * (finiteEventPathWeight (FullPermutationMixedEvent sizes shared B aux delta displacement)
      (fullPermutationMixedEventTarget sizes shared B aux delta displacement)
      (fullPermutationMixedEventWeight sizes shared B aux delta displacement omega
        (fun g p => β g p / V (e.symm g).val) retention ρ (fun g => V (e.symm g).val)) steps x path : ℂ) *
    fullMixedCommonBoundaryMultiplier (fun _ : Fin M => J + ell) B
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
      code ν encode (fullMixedCommonInitialPrime x) *
    finiteEventLocalPhase (FullPermutationMixedEvent sizes shared B aux delta displacement)
      (fullPermutationMixedEventTarget sizes shared B aux delta displacement)
      (physicalSelectedDecoratedPhase sizes shared B aux delta displacement
        (fullMixedBirthResidualPhase sizes shared B aux delta displacement (physicalFullCombinedEdgePhase Cb kb omega β ρ (fun g => V (e.symm g).val) (fun _ => 0)
          (physicalRootKeyCoefficient groups e patterns C hC ζ k K θ)))
        code ν encode) steps x path

theorem physical_root_common_forest_fourier
    (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ) (hinj : Function.Injective encode)
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B) :
    physicalRootCommonForestAction groups e patterns C hC k pl V q ζ K r θ β retention ρ code f x =
      ∫ ν, physicalRootPlanFourierIntegrand groups e patterns C hC k pl V q ζ K r θ β retention ρ
        code encode ν f x ∂birthFourierCubeMeasure (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) := by
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
  exact physical_selected_plan_forest_fourier sizes shared B aux delta displacement
    (physicalFullCombinedEdgePhase Cb kb omega β ρ (fun g => V (e.symm g).val) (fun _ => 0)
          (physicalRootKeyCoefficient groups e patterns C hC ζ k K θ)) omega (fun g p => β g p / V (e.symm g).val) retention ρ (fun g => V (e.symm g).val)
    pl.1 pl.2 univ (fun _ => x) (fun path => path) F encode hinj code

end Root
end Bounty

end

section

-- Original source module: FullPermutationParameterLedger

/- Exact edge-parameter transport preserves the original cumulative birth
ledger. Effective local phases therefore pull back to the same raw ledger. -/

open scoped Classical
namespace Bounty
section Ledger
variable {J K : Type*} {N : ℕ} {P : Fin N → Type*}
  [∀ g, DecidableEq (P g)]
  (n : ∀ g, P g → ℕ) {M : Fin N → ℕ}
  (S : K → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (A : ∀ k, SharedActiveLabels P (S k) → Type*)
  (Δ Δ' D D' : ∀ k c, A k c → Fin N → ℤ)
  (hΔ : ∀ k, Δ k = Δ' k)
  (hD : ∀ k c a g p, ((n g p : ℤ) ∣ D k c a g ↔ (n g p : ℤ) ∣ D' k c a g))

theorem full_permutation_parameter_ledger_update
    (tag : Option (J ⊕ K)) (H : (g : Fin N) → Finset (P g))
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (e : FullPermutationMixedEvent n S B A Δ D tag x) :
    fullMixedLedgerUpdate n S B A Δ' D' tag H x
      (fullPermutationParameterEventEquiv n S B A Δ Δ' D D' hΔ hD tag x e) =
    fullMixedLedgerUpdate n S B A Δ D tag H x e := by
  cases tag with
  | none => rfl
  | some tag =>
    cases tag with
    | inl j => rfl
    | inr k =>
      dsimp only [fullMixedLedgerUpdate, fullPermutationParameterEventEquiv]
      unfold fullEdgeLedgerUpdate
      erw [full_active_parameter_target]

theorem full_permutation_parameter_ledger_phase
    (phase : ∀ (tag : Option (J ⊕ K)), ((g : Fin N) → Finset (P g)) →
      (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) →
      FullPermutationMixedEvent n S B A Δ' D' tag x → ℂ)
    (steps : List (Option (J ⊕ K))) (H : (g : Fin N) → Finset (P g))
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (p : FiniteEventPath (FullPermutationMixedEvent n S B A Δ D)
      (fullPermutationMixedEventTarget n S B A Δ D) steps x) :
    deterministicLedgerPhase (FullPermutationMixedEvent n S B A Δ' D')
      (fullPermutationMixedEventTarget n S B A Δ' D')
      (fullMixedLedgerUpdate n S B A Δ' D') phase steps H x
      (fullPermutationParameterPathEquiv n S B A Δ Δ' D D' hΔ hD steps x p) =
    deterministicLedgerPhase (FullPermutationMixedEvent n S B A Δ D)
      (fullPermutationMixedEventTarget n S B A Δ D)
      (fullMixedLedgerUpdate n S B A Δ D)
      (fun tag H x e => phase tag H x
        (fullPermutationParameterEventEquiv n S B A Δ Δ' D D' hΔ hD tag x e)) steps H x p :=
  deterministic_ledger_phase_equiv _ _ _ _ id _ _ _ _
    (full_permutation_parameter_ledger_update n S B A Δ Δ' D D' hΔ hD)
    _ _ (fun _ _ _ _ => rfl) steps H x p

end Ledger
end Bounty

end

section

-- Original source module: PhysicalMixedEffectiveLedger

/- The actual mixed-to-effective parameter equivalence preserves the
finite-set birth ledger and pulls effective local phases back exactly. -/

open scoped Classical
namespace Bounty
section Effective
variable {S K V : Type} [Fintype S] {N J ell : ℕ}
  {Ps : S → Finset ℕ} {P : Fin N → Finset ℕ}
  (hPs : ∀ s p, p ∈ Ps s → Nat.Prime p)
  (hP : ∀ g p, p ∈ P g → Nat.Prime p)
  (hdis : ∀ s g, Disjoint (Ps s) (P g))
  (C : K → Fin N → Finset (Fin J)) (d : K → PhysicalSharedLists Ps J)
  (k : K → ℤ) (B : ℕ)

noncomputable def physicalMixedEffectiveBigEventEquiv
    (tag : Option (V ⊕ K))
    (x : PhysicalFullBoundedState P J ell B) :
    FullPermutationMixedEvent (fun g (p : P g) => p.val)
      (fun key g => physicalFullSharedIndices (ell := ell) (C key g)) B
      (fun key _ => PhysicalAuxLabels P (C key))
      (fun key => physicalMixedEdgeDelta (C key) (k key) (d key))
      (fun key => physicalMixedEdgeD (C key) (d key)) tag x ≃
    FullPermutationMixedEvent (fun g (p : P g) => p.val)
      (fun key g => physicalFullSharedIndices (ell := ell) (C key g)) B
      (fun key _ => PhysicalAuxLabels P (C key))
      (fun key => physicalFullEdgeDelta (C key) (k key * (physicalSharedProduct (d key) : ℕ)))
      (fun key => physicalFullEdgeD (C key)) tag x :=
  fullPermutationParameterEventEquiv _ _ B _ _ _ _ _
    (fun key => funext fun c => funext fun a => funext fun g =>
      physical_mixed_delta_effective_big_step (C key) (d key) (k key) c a g)
    (fun key c a g p => physical_mixed_dilation_divisibility hPs hP hdis (C key) (d key) c a g p)
    tag x

theorem physical_mixed_effective_big_ledger_phase
    (phase : ∀ (tag : Option (V ⊕ K)), ((g : Fin N) → Finset (P g)) →
      (x : PhysicalFullBoundedState P J ell B) →
      FullPermutationMixedEvent (fun g (p : P g) => p.val)
        (fun key g => physicalFullSharedIndices (ell := ell) (C key g)) B
        (fun key _ => PhysicalAuxLabels P (C key))
        (fun key => physicalFullEdgeDelta (C key) (k key * (physicalSharedProduct (d key) : ℕ)))
        (fun key => physicalFullEdgeD (C key)) tag x → ℂ)
    (steps : List (Option (V ⊕ K))) (H : (g : Fin N) → Finset (P g))
    (x : PhysicalFullBoundedState P J ell B)
    (p : FullPermutationMixedPath (fun g (p : P g) => p.val)
      (fun key g => physicalFullSharedIndices (ell := ell) (C key g)) B
      (fun key _ => PhysicalAuxLabels P (C key))
      (fun key => physicalMixedEdgeDelta (C key) (k key) (d key))
      (fun key => physicalMixedEdgeD (C key) (d key)) steps x) :
    deterministicLedgerPhase
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
      (fullMixedLedgerUpdate (fun g (p : P g) => p.val)
        (fun key g => physicalFullSharedIndices (ell := ell) (C key g)) B
        (fun key _ => PhysicalAuxLabels P (C key))
        (fun key => physicalFullEdgeDelta (C key) (k key * (physicalSharedProduct (d key) : ℕ)))
        (fun key => physicalFullEdgeD (C key)))
      phase steps H x (physicalMixedEffectiveBigPathEquiv hPs hP hdis C d k B steps x p) =
    deterministicLedgerPhase
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
      (fullMixedLedgerUpdate (fun g (p : P g) => p.val)
        (fun key g => physicalFullSharedIndices (ell := ell) (C key g)) B
        (fun key _ => PhysicalAuxLabels P (C key))
        (fun key => physicalMixedEdgeDelta (C key) (k key) (d key))
        (fun key => physicalMixedEdgeD (C key) (d key)))
      (fun tag H x e => phase tag H x
        (physicalMixedEffectiveBigEventEquiv hPs hP hdis C d k B tag x e)) steps H x p :=
  full_permutation_parameter_ledger_phase _ _ B _ _ _ _ _
    (fun key => funext fun c => funext fun a => funext fun g =>
      physical_mixed_delta_effective_big_step (C key) (d key) (k key) c a g)
    (fun key c a g p => physical_mixed_dilation_divisibility hPs hP hdis (C key) (d key) c a g p)
    phase steps H x p

end Effective
end Bounty

end

section

-- Original source module: PhysicalMixedProjectedHistory

/- Local decorated big phases, with their actual deterministic state update,
pull back through small-plan packing to local mixed-event phases. -/

open scoped Classical
namespace Bounty
section History
variable {S G I V K : Type} [Fintype S]
  {Ps : S → Finset ℕ} {P : G → Type}
  (n : ∀ g, P g → ℕ) {J ell : ℕ} {M : G → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (A : I → Type)
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J →
    SharedActiveLabels P (shared i) → A i → G → ℤ)

noncomputable def physicalMixedDecoratedBigTarget :=
  fullPermutationMixedEventTarget (J := V) n
    (fun key : PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K) => shared key.2.1) B
    (fun key _ => A key.2.1)
    (fun key c a => Δ key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)
    (fun key c a => D key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)

noncomputable def physicalMixedBigEventPullback {H T : Type*}
    (F : ∀ tag, H →
      (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) →
      PhysicalMixedDecoratedBigEvent (V := V) (ell := ell) n shared B A Δ D tag x → T)
    (tag : Option (V ⊕ K)) (h : H)
    (s : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B)
    (e : PhysicalMixedWordEvent n shared B A Δ D tag s) : T :=
  F (physicalMixedBigEventTag n shared B A Δ D tag s e) h s.2
    (physicalMixedBigEventProjection n shared B A Δ D tag s e)

variable (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)
  {H : Type*}
  (update : ∀ tag, H →
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) →
    PhysicalMixedDecoratedBigEvent (V := V) (ell := ell) n shared B A Δ D tag x → H)
  (phase : ∀ tag, H →
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) →
    PhysicalMixedDecoratedBigEvent (V := V) (ell := ell) n shared B A Δ D tag x → ℂ)

theorem physical_mixed_projected_history_pack
    (ks : List (Option (V ⊕ K))) (h : H)
    (r : PhysicalResidues Ps) (L : PhysicalMarkLists Ps J ell)
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (z : Σ pl : PhysicalMixedSmallPlan (I := I) ks,
      PhysicalMixedPlannedBigPath n shared B A Δ D ks L pl x) :
    deterministicLedgerPhase
      (PhysicalMixedWordEvent n shared B A Δ D)
      (physicalMixedWordTarget n shared B A Δ D kbig)
      (physicalMixedBigEventPullback n shared B A Δ D update)
      (physicalMixedBigEventPullback n shared B A Δ D phase)
      ks h ((r, L), x) (physicalMixedPathPack n shared B A Δ D kbig ks r L x z) =
    deterministicLedgerPhase
      (PhysicalMixedDecoratedBigEvent n shared B A Δ D)
      (physicalMixedDecoratedBigTarget n shared B A Δ D)
      update phase (physicalMixedBigSteps ks L z.1) h x z.2 := by
  induction ks generalizing h r L x with
  | nil => rcases z with ⟨⟨⟩, ⟨⟩⟩; rfl
  | cons tag ks ih =>
    cases tag with
    | none =>
      rcases z with ⟨⟨σ, pl⟩, ⟨⟨τ⟩, p⟩⟩
      dsimp only [physicalMixedPathPack, physicalMixedBigSteps, deterministicLedgerPhase,
        physicalMixedBigEventPullback, physicalMixedBigEventTag, physicalMixedBigEventProjection]
      erw [ih]
      rfl
    | some tag =>
      cases tag with
      | inl j =>
        rcases z with ⟨pl, ⟨⟨e⟩, p⟩⟩
        dsimp only [physicalMixedPathPack, physicalMixedBigSteps, deterministicLedgerPhase,
          physicalMixedBigEventPullback, physicalMixedBigEventTag, physicalMixedBigEventProjection]
        erw [ih]
        rfl
      | inr k =>
        rcases z with ⟨⟨⟨i, R⟩, pl⟩, ⟨⟨a, e⟩, p⟩⟩
        dsimp only [physicalMixedPathPack, physicalMixedBigSteps, deterministicLedgerPhase,
          physicalMixedBigEventPullback, physicalMixedBigEventTag, physicalMixedBigEventProjection]
        erw [ih]
        rfl

theorem physical_mixed_projected_history_unpack
    (ks : List (Option (V ⊕ K))) (h : H)
    (r : PhysicalResidues Ps) (L : PhysicalMarkLists Ps J ell)
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (p : FiniteEventPath (PhysicalMixedWordEvent n shared B A Δ D)
      (physicalMixedWordTarget n shared B A Δ D kbig) ks ((r, L), x)) :
    deterministicLedgerPhase
      (PhysicalMixedWordEvent n shared B A Δ D)
      (physicalMixedWordTarget n shared B A Δ D kbig)
      (physicalMixedBigEventPullback n shared B A Δ D update)
      (physicalMixedBigEventPullback n shared B A Δ D phase) ks h ((r, L), x) p =
    let z := physicalMixedPathUnpack n shared B A Δ D kbig ks r L x p
    deterministicLedgerPhase
      (PhysicalMixedDecoratedBigEvent n shared B A Δ D)
      (physicalMixedDecoratedBigTarget n shared B A Δ D)
      update phase (physicalMixedBigSteps ks L z.1) h x z.2 := by
  have hp := physical_mixed_projected_history_pack n shared B A Δ D kbig update phase ks h r L x
    (physicalMixedPathUnpack n shared B A Δ D kbig ks r L x p)
  rw [physical_mixed_path_pack_unpack] at hp
  exact hp

end History
end Bounty

end

section

-- Original source module: PhysicalRootPlannedHistory

/- The exact root planned remainder uses the original raw birth ledger and
local phases transported through the actual effective event equivalence. -/

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
  (hPs : ∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p)
  (hPb : ∀ (g : Fin M) p, p ∈ P (e.symm g).val → Nat.Prime p)
  (hdis : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (e.symm g).val))

noncomputable def physicalRootPlannedLocalPhase
    (tag : Option (Fin (n + 2) ⊕ PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val) (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1))))
    (H : (g : Fin M) → Finset (P (e.symm g).val))
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B)
    (event : PhysicalMixedDecoratedBigEvent (fun g (p : P (e.symm g).val) => p.val)
      (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) B
      (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
      (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
      (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val)) tag x) : ℂ :=
  physicalRootEffectiveLocalPhase (n := n) groups e patterns C hC k V ζ K θ β ρ tag H x
    (physicalMixedEffectiveBigEventEquiv hPs hPb hdis
      (fun key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val) (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) => fun g => C key.2.1.val (e.symm g).val)
      (fun key => physicalSharedPrefix key.2.2.1)
      (fun key => k (n - key.1.val) key.2.1.val) B tag x event)

noncomputable def physicalRootPlannedHistory
    (pl : PhysicalRootSmallPlan (P := P) (J := J) (ell := ell) (n := n) groups patterns)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B)
    (path : PhysicalRootPlannedPath groups e patterns C k pl x) : ℂ :=
  deterministicLedgerPhase
    (PhysicalMixedDecoratedBigEvent (fun g (p : P (e.symm g).val) => p.val)
      (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) B
      (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
      (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
      (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val)))
    (physicalMixedDecoratedBigTarget (fun g (p : P (e.symm g).val) => p.val)
      (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) B
      (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
      (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
      (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val)))
    (fullMixedLedgerUpdate (fun g (p : P (e.symm g).val) => p.val)
      (fun key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val) (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) => fun g => physicalFullSharedIndices (ell := ell) (C key.2.1.val (e.symm g).val)) B
      (fun key _ => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C key.2.1.val (e.symm g).val))
      (fun key => physicalMixedEdgeDelta (fun g => C key.2.1.val (e.symm g).val)
        (k (n - key.1.val) key.2.1.val) (physicalSharedPrefix key.2.2.1))
      (fun key => physicalMixedEdgeD (fun g => C key.2.1.val (e.symm g).val) (physicalSharedPrefix key.2.2.1)))
    (physicalRootPlannedLocalPhase groups e patterns C hC k V ζ K θ β ρ hPs hPb hdis)
    (physicalMixedBigSteps ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) pl.1 pl.2)
    (fullActiveInitialLedger x) x path

theorem physical_root_planned_remainder_history
    (pl : PhysicalRootSmallPlan (P := P) (J := J) (ell := ell) (n := n) groups patterns)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B)
    (path : PhysicalRootPlannedPath groups e patterns C k pl x) :
    physicalRootPlannedRemainder groups e patterns C hC k pl V ζ K θ β ρ hPs hPb hdis x path =
      physicalRootPlannedHistory groups e patterns C hC k V ζ K θ β ρ hPs hPb hdis pl x path := by
  unfold physicalRootPlannedRemainder
  rw [physical_root_effective_remainder_history]
  unfold physicalRootEffectiveHistory physicalRootPlannedHistory physicalRootPlannedLocalPhase
    physicalMixedDecoratedBigTarget
  dsimp only
  exact physical_mixed_effective_big_ledger_phase hPs hPb hdis _ _ _ B _ _ _ x path

end Root
end Bounty

end

section

-- Original source module: PhysicalMixedProjectedLocal

/- Ordinary decorated big-event phases pack through the actual small
plan equivalence, without adding a history variable. -/

open scoped Classical
namespace Bounty
section Local
variable {S G I V K : Type} [Fintype S]
  {Ps : S → Finset ℕ} {P : G → Type}
  (n : ∀ g, P g → ℕ) {J ell : ℕ} {M : G → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (A : I → Type)
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J →
    SharedActiveLabels P (shared i) → A i → G → ℤ)

noncomputable def physicalMixedBigLocalPullback
    (phase : ∀ tag,
      (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) →
      PhysicalMixedDecoratedBigEvent (V := V) (ell := ell) n shared B A Δ D tag x → ℂ)
    (tag : Option (V ⊕ K))
    (s : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B)
    (e : PhysicalMixedWordEvent n shared B A Δ D tag s) : ℂ :=
  phase (physicalMixedBigEventTag n shared B A Δ D tag s e) s.2
    (physicalMixedBigEventProjection n shared B A Δ D tag s e)

variable (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)
  (phase : ∀ tag,
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) →
    PhysicalMixedDecoratedBigEvent (V := V) (ell := ell) n shared B A Δ D tag x → ℂ)

theorem physical_mixed_projected_local_pack
    (ks : List (Option (V ⊕ K)))
    (r : PhysicalResidues Ps) (L : PhysicalMarkLists Ps J ell)
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (z : Σ pl : PhysicalMixedSmallPlan (I := I) ks,
      PhysicalMixedPlannedBigPath n shared B A Δ D ks L pl x) :
    finiteEventLocalPhase (PhysicalMixedWordEvent n shared B A Δ D)
      (physicalMixedWordTarget n shared B A Δ D kbig)
      (physicalMixedBigLocalPullback n shared B A Δ D phase)
      ks ((r, L), x) (physicalMixedPathPack n shared B A Δ D kbig ks r L x z) =
    finiteEventLocalPhase (PhysicalMixedDecoratedBigEvent n shared B A Δ D)
      (physicalMixedDecoratedBigTarget n shared B A Δ D)
      phase (physicalMixedBigSteps ks L z.1) x z.2 := by
  induction ks generalizing r L x with
  | nil => rcases z with ⟨⟨⟩, ⟨⟩⟩; rfl
  | cons tag ks ih =>
    cases tag with
    | none =>
      rcases z with ⟨⟨σ, pl⟩, ⟨⟨τ⟩, p⟩⟩
      dsimp only [physicalMixedPathPack, physicalMixedBigSteps, finiteEventLocalPhase,
        physicalMixedBigLocalPullback, physicalMixedBigEventTag, physicalMixedBigEventProjection]
      erw [ih]
      rfl
    | some tag =>
      cases tag with
      | inl j =>
        rcases z with ⟨pl, ⟨⟨e⟩, p⟩⟩
        dsimp only [physicalMixedPathPack, physicalMixedBigSteps, finiteEventLocalPhase,
          physicalMixedBigLocalPullback, physicalMixedBigEventTag, physicalMixedBigEventProjection]
        erw [ih]
        rfl
      | inr k =>
        rcases z with ⟨⟨⟨i, R⟩, pl⟩, ⟨⟨a, e⟩, p⟩⟩
        dsimp only [physicalMixedPathPack, physicalMixedBigSteps, finiteEventLocalPhase,
          physicalMixedBigLocalPullback, physicalMixedBigEventTag, physicalMixedBigEventProjection]
        erw [ih]
        rfl

theorem physical_mixed_projected_local_unpack
    (ks : List (Option (V ⊕ K)))
    (r : PhysicalResidues Ps) (L : PhysicalMarkLists Ps J ell)
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (p : FiniteEventPath (PhysicalMixedWordEvent n shared B A Δ D)
      (physicalMixedWordTarget n shared B A Δ D kbig) ks ((r, L), x)) :
    finiteEventLocalPhase (PhysicalMixedWordEvent n shared B A Δ D)
      (physicalMixedWordTarget n shared B A Δ D kbig)
      (physicalMixedBigLocalPullback n shared B A Δ D phase) ks ((r, L), x) p =
    let z := physicalMixedPathUnpack n shared B A Δ D kbig ks r L x p
    finiteEventLocalPhase (PhysicalMixedDecoratedBigEvent n shared B A Δ D)
      (physicalMixedDecoratedBigTarget n shared B A Δ D)
      phase (physicalMixedBigSteps ks L z.1) x z.2 := by
  have hp := physical_mixed_projected_local_pack n shared B A Δ D kbig phase ks r L x
    (physicalMixedPathUnpack n shared B A Δ D kbig ks r L x p)
  rw [physical_mixed_path_pack_unpack] at hp
  exact hp

end Local
end Bounty

end

section

-- Original source module: PhysicalRootFourierPhases

/- Ordinary local Fourier phases for the exact root coefficient, first on
effective events, then on planned events and the actual mixed word. -/

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
variable (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ)
    (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) → ℝ)

noncomputable def physicalRootEffectiveFourierPhase :=
  let Cb := fun key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val)
    (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      fun g => C key.2.1.val (e.symm g).val
  let kb := fun key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val)
    (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      k (n - key.1.val) key.2.1.val * (physicalSharedProduct (physicalSharedPrefix key.2.2.1) : ℕ)
  let sizes := fun g (p : P (e.symm g).val) => p.val
  let shared := fun key g => physicalFullSharedIndices (ell := ell) (Cb key g)
  let aux := fun key (_ : SharedActiveLabels (fun g => ↥(P (e.symm g).val)) (shared key)) =>
    PhysicalAuxLabels (fun g => P (e.symm g).val) (Cb key)
  let delta := fun key => physicalFullEdgeDelta (P := fun g => P (e.symm g).val) (ell := ell) (Cb key) (kb key)
  let displacement := fun key => physicalFullEdgeD (P := fun g => P (e.symm g).val) (ell := ell) (Cb key)
  let omega := fun key (_ : SharedActiveLabels (fun g => ↥(P (e.symm g).val)) (shared key)) (a : PhysicalAuxLabels (fun g => P (e.symm g).val) (Cb key)) =>
    physicalAuxMass (fun g => V (e.symm g).val) (Cb key) a
  physicalSelectedDecoratedPhase sizes shared B aux delta displacement
    (fullMixedBirthResidualPhase sizes shared B aux delta displacement
      (physicalFullCombinedEdgePhase Cb kb omega β ρ (fun g => V (e.symm g).val) (fun _ => 0)
        (physicalRootKeyCoefficient groups e patterns C hC ζ k K θ))) code ν encode

variable (hPs : ∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p)
  (hPb : ∀ (g : Fin M) p, p ∈ P (e.symm g).val → Nat.Prime p)
  (hdis : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (e.symm g).val))

noncomputable def physicalRootPlannedFourierPhase
    (tag : Option (Fin (n + 2) ⊕ PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val) (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1))))
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B)
    (event : PhysicalMixedDecoratedBigEvent (fun g (p : P (e.symm g).val) => p.val)
      (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) B
      (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
      (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
      (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val)) tag x) : ℂ :=
  physicalRootEffectiveFourierPhase (n := n) groups e patterns C hC k V ζ K θ β ρ code encode ν tag x
    (physicalMixedEffectiveBigEventEquiv hPs hPb hdis
      (fun key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val) (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) => fun g => C key.2.1.val (e.symm g).val)
      (fun key => physicalSharedPrefix key.2.2.1)
      (fun key => k (n - key.1.val) key.2.1.val) B tag x event)

noncomputable def physicalRootMixedFourierPhase :=
  physicalMixedBigLocalPullback (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) B
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
    (physicalRootPlannedFourierPhase (n := n) groups e patterns C hC k V ζ K θ β ρ code encode ν hPs hPb hdis)

end Root
end Bounty

end

section

-- Original source module: PhysicalMixedProjectedRows

/- The actual mixed operator word packs exactly into the small-plan sum
of original big paths with ordinary decorated local phases. -/

open Finset
open scoped Classical
namespace Bounty
section Rows
variable {S G I V K : Type} [Fintype S] [Fintype G] [DecidableEq G] [Fintype I]
  {Ps : S → Finset ℕ} {P : G → Type} [∀ g, Fintype (P g)]
  (n : ∀ g, P g → ℕ) [∀ g p, NeZero (n g p)] {J ell : ℕ} {M : G → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (A : I → Type) [∀ i, Fintype (A i)]
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J → SharedActiveLabels P (shared i) → A i → G → ℤ)
  (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)
  (ω : ∀ i, SharedActiveLabels P (shared i) → A i → ℝ)
  (μ : ∀ g, P g → ℝ) (qghost : V → ℝ) (ρ : ℝ) (Vb : G → ℝ)
  (Vs : S → ℝ) (qedge : K → ℝ)

theorem physical_mixed_projected_rows
    (phase : ∀ tag,
      (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) →
      PhysicalMixedDecoratedBigEvent (V := V) (ell := ell) n shared B A Δ D tag x → ℂ)
    (ks : List (Option (V ⊕ K)))
    (f : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B → ℂ)
    (r : PhysicalResidues Ps) (L : PhysicalMarkLists Ps J ell)
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) :
    let _ := physicalMixedSmallPlanFintype (Ps := Ps) (J := J) (ell := ell) (I := I) ks
    finiteOperatorListAction
      (physicalMixedWordRow n shared B A Δ D kbig ω μ qghost ρ Vb Vs qedge
        (physicalMixedBigLocalPullback n shared B A Δ D phase)) ks (fun s => f s.2) ((r, L), x) =
    ∑ pl : PhysicalMixedSmallPlan (Ps := Ps) (J := J) (ell := ell) (I := I) ks,
      physicalMixedPlannedBigAction n shared B A Δ D ω μ qghost ρ Vb ks L pl
        (fun y p => (physicalMixedPlanSmallFactor n shared B A Δ D kbig Vs qedge ks r L pl y p : ℂ) *
          finiteEventLocalPhase (PhysicalMixedDecoratedBigEvent n shared B A Δ D)
            (physicalMixedDecoratedBigTarget n shared B A Δ D)
            phase (physicalMixedBigSteps ks L pl) y p) f x := by
  let _ := physicalMixedSmallPlanFintype (Ps := Ps) (J := J) (ell := ell) (I := I) ks
  rw [physical_mixed_word_eq_original_big_paths]
  apply sum_congr rfl
  intro pl _
  unfold physicalMixedPlannedBigAction fullPermutationMixedPathAction finiteEventPathAction
  apply sum_congr rfl
  intro p _
  dsimp only
  have hp := physical_mixed_projected_local_pack n shared B A Δ D kbig phase ks r L x ⟨pl, p⟩
  have ht := physical_mixed_planned_big_terminal n shared B A Δ D kbig ks r L pl x p
  erw [hp, ht]
  dsimp only [physicalMixedPlannedBigTerminal]
  ring

end Rows
end Bounty

end

section

-- Original source module: PhysicalRootFourierWord

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

noncomputable def physicalRootFourierPlannedAction
    (pl : PhysicalRootSmallPlan (P := P) (J := J) (ell := ell) (n := n) groups patterns)
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ) :=
  let _ : ∀ g (z : P (e.symm g).val), NeZero z.val :=
    fun g z => inferInstanceAs (NeZero (⟨(e.symm g).val, z⟩ : PhysicalPrime P).2.val)
  physicalMixedPlannedBigAction (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val))
    B
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
    (fun (i : patterns) _ a => physicalAuxMass (fun g => V (e.symm g).val) (fun g => C i.val (e.symm g).val) a) (fun g p => β g p / V (e.symm g).val) retention ρ (fun g => V (e.symm g).val) ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) pl.1 pl.2
    (fun y p => (physicalMixedPlanSmallFactor (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val))
    B
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
      (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val)) (fun s : ↥groupsᶜ => V s.val) (fun _ => q) ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
      (physicalGroupResidueVector r) pl.1 pl.2 y p : ℂ) *
      finiteEventLocalPhase (PhysicalMixedDecoratedBigEvent (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val))
    B
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val)))
        (physicalMixedDecoratedBigTarget (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val))
    B
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))) (physicalRootPlannedFourierPhase groups e patterns C hC k V ζ K θ β ρ code encode ν hPs hPb hdis)
        (physicalMixedBigSteps ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) pl.1 pl.2) y p) f

noncomputable def physicalRootFourierWord
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (L : PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B) : ℂ :=
  let _ : ∀ g (z : P (e.symm g).val), NeZero z.val :=
    fun g z => inferInstanceAs (NeZero (⟨(e.symm g).val, z⟩ : PhysicalPrime P).2.val)
  finiteOperatorListAction (physicalMixedWordRow (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val))
    B
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val)) (fun (i : patterns) _ a => physicalAuxMass (fun g => V (e.symm g).val) (fun g => C i.val (e.symm g).val) a) (fun g p => β g p / V (e.symm g).val) retention ρ (fun g => V (e.symm g).val) (fun s : ↥groupsᶜ => V s.val) (fun _ => q) (physicalRootMixedFourierPhase groups e patterns C hC k V ζ K θ β ρ code encode ν hPs hPb hdis))
    ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))) (fun s => f s.2) ((physicalGroupResidueVector r, L), x)

theorem physical_root_fourier_word_eq_plans
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (L : PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B) :
  let _ := physicalMixedSmallPlanFintype (Ps := (fun s : ↥groupsᶜ => P s.val))
    (J := J) (ell := ell) (I := patterns) ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
  physicalRootFourierWord groups e patterns C hC k V q ζ K r θ β retention ρ hPs hPb hdis
    code encode ν f L x =
  ∑ sp : PhysicalMixedSmallPlan (Ps := (fun s : ↥groupsᶜ => P s.val)) (J := J) (ell := ell)
      (I := patterns) ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))),
    physicalRootFourierPlannedAction groups e patterns C hC k V q ζ K r θ β retention ρ hPs hPb hdis
      code encode ν (L, sp) f x := by
  let _ : ∀ g (z : P (e.symm g).val), NeZero z.val :=
    fun g z => inferInstanceAs (NeZero (⟨(e.symm g).val, z⟩ : PhysicalPrime P).2.val)
  let _ := physicalMixedSmallPlanFintype (Ps := (fun s : ↥groupsᶜ => P s.val))
    (J := J) (ell := ell) (I := patterns) ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
  exact physical_mixed_projected_rows (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val))
    B
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val)) (fun (i : patterns) _ a => physicalAuxMass (fun g => V (e.symm g).val) (fun g => C i.val (e.symm g).val) a) (fun g p => β g p / V (e.symm g).val) retention ρ (fun g => V (e.symm g).val) (fun s : ↥groupsᶜ => V s.val) (fun _ => q) (physicalRootPlannedFourierPhase groups e patterns C hC k V ζ K θ β ρ code encode ν hPs hPb hdis) ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
    f (physicalGroupResidueVector r) L x

end Root
end Bounty

end

section

-- Original source module: PhysicalMixedBirthHistory

/- Mixed events carry the original finite-set birth ledger through their
actual decorated big events. No event choices are added. -/

open scoped Classical
namespace Bounty
section Birth
variable {S I V K : Type} [Fintype S] {N : ℕ}
  {Ps : S → Finset ℕ} {P : Fin N → Type}
  [∀ g, DecidableEq (P g)]
  (n : ∀ g, P g → ℕ) {J ell : ℕ} {M : Fin N → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (A : I → Type)
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J →
    SharedActiveLabels P (shared i) → A i → Fin N → ℤ)

noncomputable def physicalMixedBirthLedgerUpdate :=
  physicalMixedBigEventPullback (V := V) (ell := ell) n shared B A Δ D
    (fullMixedLedgerUpdate n
      (fun key : PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K) => shared key.2.1) B
      (fun key _ => A key.2.1)
      (fun key c a => Δ key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)
      (fun key c a => D key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a))

variable (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)
  (phase : ∀ tag, ((g : Fin N) → Finset (P g)) →
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B) →
    PhysicalMixedDecoratedBigEvent (V := V) (ell := ell) n shared B A Δ D tag x → ℂ)

theorem physical_mixed_birth_history_pack
    (ks : List (Option (V ⊕ K))) (H : (g : Fin N) → Finset (P g))
    (r : PhysicalResidues Ps) (L : PhysicalMarkLists Ps J ell)
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (z : Σ pl : PhysicalMixedSmallPlan (I := I) ks,
      PhysicalMixedPlannedBigPath n shared B A Δ D ks L pl x) :
    deterministicLedgerPhase
      (PhysicalMixedWordEvent n shared B A Δ D)
      (physicalMixedWordTarget n shared B A Δ D kbig)
      (physicalMixedBirthLedgerUpdate n shared B A Δ D)
      (physicalMixedBigEventPullback n shared B A Δ D phase)
      ks H ((r, L), x) (physicalMixedPathPack n shared B A Δ D kbig ks r L x z) =
    deterministicLedgerPhase
      (PhysicalMixedDecoratedBigEvent n shared B A Δ D)
      (physicalMixedDecoratedBigTarget n shared B A Δ D)
      (fullMixedLedgerUpdate n
        (fun key : PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K) => shared key.2.1) B
        (fun key _ => A key.2.1)
        (fun key c a => Δ key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)
        (fun key c a => D key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a))
      phase (physicalMixedBigSteps ks L z.1) H x z.2 :=
  physical_mixed_projected_history_pack n shared B A Δ D kbig _ phase ks H r L x z

theorem physical_mixed_birth_local_phase_pack
    (ks : List (Option (V ⊕ K))) (H : (g : Fin N) → Finset (P g))
    (r : PhysicalResidues Ps) (L : PhysicalMarkLists Ps J ell)
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (z : Σ pl : PhysicalMixedSmallPlan (I := I) ks,
      PhysicalMixedPlannedBigPath n shared B A Δ D ks L pl x) :
    finiteEventLocalPhase
      (fun tag (s : ((g : Fin N) → Finset (P g)) ×
        PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B) =>
        PhysicalMixedWordEvent n shared B A Δ D tag s.2)
      (finiteLedgerEventTarget (PhysicalMixedWordEvent n shared B A Δ D)
        (physicalMixedWordTarget n shared B A Δ D kbig)
        (physicalMixedBirthLedgerUpdate n shared B A Δ D))
      (fun tag s => physicalMixedBigEventPullback n shared B A Δ D phase tag s.1 s.2)
      ks (H, ((r, L), x))
      ((finiteLedgerEventPathEquiv (PhysicalMixedWordEvent n shared B A Δ D)
        (physicalMixedWordTarget n shared B A Δ D kbig)
        (physicalMixedBirthLedgerUpdate n shared B A Δ D) ks H ((r, L), x)).symm
        (physicalMixedPathPack n shared B A Δ D kbig ks r L x z)) =
    deterministicLedgerPhase
      (PhysicalMixedDecoratedBigEvent n shared B A Δ D)
      (physicalMixedDecoratedBigTarget n shared B A Δ D)
      (fullMixedLedgerUpdate n
        (fun key : PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := K) => shared key.2.1) B
        (fun key _ => A key.2.1)
        (fun key c a => Δ key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a)
        (fun key c a => D key.1 key.2.1 (physicalSharedPrefix key.2.2.1) c a))
      phase (physicalMixedBigSteps ks L z.1) H x z.2 := by
  rw [← deterministic_ledger_phase_eq_lifted]
  exact physical_mixed_birth_history_pack n shared B A Δ D kbig phase ks H r L x z

end Birth
end Bounty

end

section

-- Original source module: PhysicalRootMixedHistory

/- The actual whole-path root phase is realized by local mixed-event
phases on the original deterministic finite-set birth ledger. -/

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
  (hPs : ∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p)
  (hPb : ∀ (g : Fin M) p, p ∈ P (e.symm g).val → Nat.Prime p)
  (hdis : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (e.symm g).val))

noncomputable def physicalRootMixedBirthUpdate :=
  physicalMixedBirthLedgerUpdate (V := Fin (n + 2))
    (Ps := fun s : ↥groupsᶜ => P s.val) (J := J) (ell := ell)
    (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) B
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))

noncomputable def physicalRootMixedLocalPhase :=
  physicalMixedBigEventPullback (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) B
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
    (physicalRootPlannedLocalPhase (n := n) groups e patterns C hC k V ζ K θ β ρ hPs hPb hdis)

noncomputable def physicalRootMixedHistory
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e)
    (path : PhysicalRootMixedPath (n := n) groups e patterns C k s) : ℂ :=
  deterministicLedgerPhase
    (PhysicalRootMixedEvent groups e patterns C k)
    (physicalRootMixedTarget groups e patterns C k)
    (physicalRootMixedBirthUpdate (n := n) groups e patterns C k)
    (physicalRootMixedLocalPhase groups e patterns C hC k V ζ K θ β ρ hPs hPb hdis)
    ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
    (fullActiveInitialLedger s.2) s path

theorem physical_root_mixed_phase_history
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e)
    (path : PhysicalRootMixedPath (n := n) groups e patterns C k s) :
    physicalRootMixedPhase groups e patterns C hC k V ζ K θ β ρ hPs hPb hdis s path =
      physicalRootMixedHistory groups e patterns C hC k V ζ K θ β ρ hPs hPb hdis s path := by
  unfold physicalRootMixedPhase
  dsimp only
  erw [physical_root_planned_remainder_history]
  unfold physicalRootPlannedHistory physicalRootMixedHistory physicalRootMixedBirthUpdate
    physicalRootMixedLocalPhase physicalMixedBirthLedgerUpdate
    physicalRootMixedPackingEquiv physicalMixedPathPackingEquiv
  dsimp only
  exact (physical_mixed_projected_history_unpack (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) B
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val)) _ _ _ _ _ _ _ path).symm

theorem physical_root_mixed_phase_local
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e)
    (path : PhysicalRootMixedPath (n := n) groups e patterns C k s) :
    physicalRootMixedPhase groups e patterns C hC k V ζ K θ β ρ hPs hPb hdis s path =
    finiteEventLocalPhase
      (fun tag (t : ((g : Fin M) → Finset (P (e.symm g).val)) ×
        PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e) =>
        PhysicalRootMixedEvent groups e patterns C k tag t.2)
      (finiteLedgerEventTarget (PhysicalRootMixedEvent groups e patterns C k)
        (physicalRootMixedTarget groups e patterns C k)
        (physicalRootMixedBirthUpdate (n := n) groups e patterns C k))
      (fun tag t => physicalRootMixedLocalPhase groups e patterns C hC k V ζ K θ β ρ hPs hPb hdis tag t.1 t.2)
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
      (fullActiveInitialLedger s.2, s)
      ((finiteLedgerEventPathEquiv (PhysicalRootMixedEvent groups e patterns C k)
        (physicalRootMixedTarget groups e patterns C k)
        (physicalRootMixedBirthUpdate (n := n) groups e patterns C k)
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
        (fullActiveInitialLedger s.2) s).symm path) := by
  rw [physical_root_mixed_phase_history]
  unfold physicalRootMixedHistory
  exact deterministic_ledger_phase_eq_lifted _ _ _ _ _ _ _ path

end Root
end Bounty

end

section

-- Original source module: PhysicalSelectedBirthExceptions

/- A rank-r common forest changes at most 2r original edge factors.
Every other selected edge retains its exact untwisted local operator. -/

open Finset
open scoped Classical
namespace Bounty
section Exceptions
variable {Z : Type*} {N : ℕ} (M : Fin N → ℕ) (B n : ℕ)
  (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B
    ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)))))

noncomputable def physicalSelectedAffectedEdges : Finset (Fin n) :=
  univ.filter (fun j => (physicalSelectedEdgePosition j).succ ∈
    birthForestAffectedOperations code
      (fullMixedCommonIndexStage M B ((List.range (4 * n + 1)).map (physicalSelectedFineTag n))))

theorem physical_selected_edge_operation_injective :
    Function.Injective (fun j : Fin n => (physicalSelectedEdgePosition j).succ) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 4 * i.val + 2 + 1 = 4 * j.val + 2 + 1 at hv
  omega

theorem physical_selected_affected_edges_card :
    (physicalSelectedAffectedEdges M B n code).card ≤ 2 * birthForestRank code := by
  apply le_trans _ (birthForestAffectedOperations_card_le code
    (fullMixedCommonIndexStage M B ((List.range (4 * n + 1)).map (physicalSelectedFineTag n))))
  apply card_le_card_of_injOn (fun j : Fin n => (physicalSelectedEdgePosition j).succ)
  · intro j hj
    exact (mem_filter.mp hj).2
  · exact (physical_selected_edge_operation_injective n).injOn

theorem physical_selected_edge_multiplier_untouched
    (θ : (Fin (Fintype.card (FullMixedCommonBirthAddress M B
        ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress M B
        ((List.range (4 * n + 1)).map (physicalSelectedFineTag n))))) → ℝ)
    (encode : Z → ℤ) (j : Fin n)
    (hj : j ∉ physicalSelectedAffectedEdges M B n code)
    (label : FullMixedCommonLocalAddress M B (some (.inr j) : Option (Fin (n + 1) ⊕ Fin n)) → Option Z) :
    physicalSelectedBirthMultiplier M B n code θ encode (some (.inr j)) label = 1 := by
  have hu : (physicalSelectedEdgePosition j).succ ∉ birthForestAffectedOperations code
      (fullMixedCommonIndexStage M B ((List.range (4 * n + 1)).map (physicalSelectedFineTag n))) := by
    intro h
    exact hj (mem_filter.mpr ⟨mem_univ j, h⟩)
  unfold physicalSelectedBirthMultiplier fullMixedCommonTaggedOperationMultiplier
  exact full_mixed_common_local_multiplier_untouched M B _ code θ encode
    (physicalSelectedEdgePosition j) _ hu

end Exceptions
end Bounty

end

section

-- Original source module: PhysicalRootFourierMultiplier

/- Ordinary local Fourier phases for the exact root coefficient, first on
effective events, then on planned events and the actual mixed word. -/

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
variable (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ)
    (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) → ℝ)

noncomputable def physicalRootEffectiveFourierMultiplier :=
  let Cb := fun key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val)
    (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      fun g => C key.2.1.val (e.symm g).val
  let kb := fun key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val)
    (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      k (n - key.1.val) key.2.1.val * (physicalSharedProduct (physicalSharedPrefix key.2.2.1) : ℕ)
  let sizes := fun g (p : P (e.symm g).val) => p.val
  let shared := fun key g => physicalFullSharedIndices (ell := ell) (Cb key g)
  let aux := fun key (_ : SharedActiveLabels (fun g => ↥(P (e.symm g).val)) (shared key)) =>
    PhysicalAuxLabels (fun g => P (e.symm g).val) (Cb key)
  let delta := fun key => physicalFullEdgeDelta (P := fun g => P (e.symm g).val) (ell := ell) (Cb key) (kb key)
  let displacement := fun key => physicalFullEdgeD (P := fun g => P (e.symm g).val) (ell := ell) (Cb key)
  physicalSelectedDecoratedPhase sizes shared B aux delta displacement
    (fun _ _ _ => 1) code ν encode

variable (hPs : ∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p)
  (hPb : ∀ (g : Fin M) p, p ∈ P (e.symm g).val → Nat.Prime p)
  (hdis : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (e.symm g).val))

noncomputable def physicalRootPlannedFourierMultiplier
    (tag : Option (Fin (n + 2) ⊕ PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val) (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1))))
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B)
    (event : PhysicalMixedDecoratedBigEvent (fun g (p : P (e.symm g).val) => p.val)
      (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) B
      (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
      (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
      (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val)) tag x) : ℂ :=
  physicalRootEffectiveFourierMultiplier (n := n) groups e patterns C k code encode ν tag x
    (physicalMixedEffectiveBigEventEquiv hPs hPb hdis
      (fun key : PhysicalMixedBigKey (Ps := fun s : ↥groupsᶜ => P s.val) (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) => fun g => C key.2.1.val (e.symm g).val)
      (fun key => physicalSharedPrefix key.2.2.1)
      (fun key => k (n - key.1.val) key.2.1.val) B tag x event)

noncomputable def physicalRootMixedFourierMultiplier :=
  physicalMixedBigLocalPullback (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) B
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
    (physicalRootPlannedFourierMultiplier (n := n) groups e patterns C k code encode ν hPs hPb hdis)

end Root
end Bounty

end

section

-- Original source module: PhysicalRootFourierLocal

/- Ordinary local Fourier phases for the exact root coefficient, first on
effective events, then on planned events and the actual mixed word. -/

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
variable (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ)
    (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) → ℝ)

variable (hPs : ∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p)
  (hPb : ∀ (g : Fin M) p, p ∈ P (e.symm g).val → Nat.Prime p)
  (hdis : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (e.symm g).val))

theorem physical_root_fourier_multiplier_norm_le
    (tag : Option (Fin (n + 2) ⊕ Fin (n + 1)))
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e)
    (ev : PhysicalRootMixedEvent groups e patterns C k tag s) :
    ‖physicalRootMixedFourierMultiplier groups e patterns C k code encode ν hPs hPb hdis tag s ev‖ ≤ 1 := by
  unfold physicalRootMixedFourierMultiplier physicalMixedBigLocalPullback
    physicalRootPlannedFourierMultiplier physicalRootEffectiveFourierMultiplier
  dsimp only [physicalSelectedDecoratedPhase]
  simp only [one_mul]
  exact physical_selected_birth_multiplier_norm_le _ _ _ _ _ _ _ _

theorem physical_root_fourier_edge_factor
    (j : Fin (n + 1))
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e)
    (ev : PhysicalRootMixedEvent groups e patterns C k (some (.inr j)) s) :
    physicalRootMixedFourierPhase groups e patterns C hC k V ζ K θ β ρ code encode ν hPs hPb hdis
        (some (.inr j)) s ev =
      physicalRootMixedLocalPhase groups e patterns C hC k V ζ K θ β ρ hPs hPb hdis
        (some (.inr j)) (fun _ => ∅) s ev *
      physicalRootMixedFourierMultiplier groups e patterns C k code encode ν hPs hPb hdis
        (some (.inr j)) s ev := by
  unfold physicalRootMixedFourierPhase physicalRootMixedFourierMultiplier
    physicalMixedBigLocalPullback physicalRootPlannedFourierPhase
    physicalRootPlannedFourierMultiplier physicalRootEffectiveFourierPhase
    physicalRootEffectiveFourierMultiplier physicalRootMixedLocalPhase
    physicalMixedBigEventPullback physicalRootPlannedLocalPhase physicalRootEffectiveLocalPhase
  dsimp only [physicalSelectedDecoratedPhase]
  simp only [one_mul]
  rfl

theorem physical_root_fourier_ghost_factor
    (j : Fin (n + 2))
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e)
    (ev : PhysicalRootMixedEvent groups e patterns C k (some (.inl j)) s) :
    physicalRootMixedFourierPhase groups e patterns C hC k V ζ K θ β ρ code encode ν hPs hPb hdis
        (some (.inl j)) s ev =
      physicalRootMixedFourierMultiplier groups e patterns C k code encode ν hPs hPb hdis
        (some (.inl j)) s ev := by
  rfl

theorem physical_root_fourier_permutation_factor
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e)
    (ev : PhysicalRootMixedEvent groups e patterns C k none s) :
    physicalRootMixedFourierPhase groups e patterns C hC k V ζ K θ β ρ code encode ν hPs hPb hdis
        none s ev = 1 := by
  change (1 : ℂ) * 1 = 1
  exact mul_one _

theorem physical_root_fourier_edge_multiplier_untouched
    (j : Fin (n + 1))
    (hj : j ∉ physicalSelectedAffectedEdges (fun _ : Fin M => J + ell) B (n + 1) code)
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e)
    (ev : PhysicalRootMixedEvent groups e patterns C k (some (.inr j)) s) :
    physicalRootMixedFourierMultiplier groups e patterns C k code encode ν hPs hPb hdis
        (some (.inr j)) s ev = 1 := by
  unfold physicalRootMixedFourierMultiplier physicalMixedBigLocalPullback
    physicalRootPlannedFourierMultiplier physicalRootEffectiveFourierMultiplier
  dsimp only [physicalSelectedDecoratedPhase]
  simp only [one_mul]
  exact physical_selected_edge_multiplier_untouched _ _ _ code ν encode j hj _

theorem physical_root_fourier_edge_untouched
    (j : Fin (n + 1))
    (hj : j ∉ physicalSelectedAffectedEdges (fun _ : Fin M => J + ell) B (n + 1) code)
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e)
    (ev : PhysicalRootMixedEvent groups e patterns C k (some (.inr j)) s) :
    physicalRootMixedFourierPhase groups e patterns C hC k V ζ K θ β ρ code encode ν hPs hPb hdis
        (some (.inr j)) s ev =
      physicalRootMixedLocalPhase groups e patterns C hC k V ζ K θ β ρ hPs hPb hdis
        (some (.inr j)) (fun _ => ∅) s ev := by
  rw [physical_root_fourier_edge_factor,
    physical_root_fourier_edge_multiplier_untouched groups e patterns C k code encode ν hPs hPb hdis j hj,
    mul_one]

end Root
end Bounty

end

section

-- Original source module: PhysicalSelectedOperatorGrouping

/- Exact grouping of the selected operator word into ghost visits and
edges sandwiched by the two original permutation averages. -/

namespace Bounty

theorem finite_operator_list_action_map {I K X : Type*}
    (row : I → (X → ℂ) → X → ℂ) (tag : K → I) (ks : List K) (f : X → ℂ) :
    finiteOperatorListAction row (ks.map tag) f =
      finiteOperatorListAction (fun k => row (tag k)) ks f := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.map_cons, finiteOperatorListAction, ih]

theorem physical_selected_fine_tag_before_edge {n : ℕ} (j : Fin n) :
    physicalSelectedFineTag n (4 * j.val + 1) = none := by
  have hi : 4 * j.val + 1 < 4 * n + 1 := by omega
  have h0 : ¬ (4 * j.val + 1) % 4 = 0 := by omega
  have h2 : ¬ (4 * j.val + 1) % 4 = 2 := by omega
  simp only [physicalSelectedFineTag, dif_pos hi, dif_neg h0, dif_neg h2]

theorem physical_selected_fine_tag_after_edge {n : ℕ} (j : Fin n) :
    physicalSelectedFineTag n (4 * j.val + 3) = none := by
  have hi : 4 * j.val + 3 < 4 * n + 1 := by omega
  have h0 : ¬ (4 * j.val + 3) % 4 = 0 := by omega
  have h2 : ¬ (4 * j.val + 3) % 4 = 2 := by omega
  simp only [physicalSelectedFineTag, dif_pos hi, dif_neg h0, dif_neg h2]

section Grouped
variable {X : Type*} {n : ℕ}
  (row : Option (Fin (n + 1) ⊕ Fin n) → (X → ℂ) → X → ℂ)

theorem physical_selected_operator_grouped_visit (j : Fin (n + 1)) (f : X → ℂ) :
    finiteRowGrouped (S := fun _ => X) (fun i => row (physicalSelectedFineTag n i))
      visitThreeBlockLength (2 * j.val) f = row (some (.inl j)) f := by
  unfold finiteRowGrouped
  rw [visit_three_block_cut_even, visit_three_block_length_even, finite_row_segment_one,
    physical_selected_fine_tag_visit]

theorem physical_selected_operator_grouped_edge (j : Fin n) (f : X → ℂ) :
    finiteRowGrouped (S := fun _ => X) (fun i => row (physicalSelectedFineTag n i))
      visitThreeBlockLength (2 * j.val + 1) f =
      row none (row (some (.inr j)) (row none f)) := by
  unfold finiteRowGrouped
  rw [visit_three_block_cut_odd, visit_three_block_length_odd, finite_row_segment_three]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  rw [physical_selected_fine_tag_before_edge, physical_selected_fine_tag_edge,
    physical_selected_fine_tag_after_edge]

theorem physical_selected_operator_word_grouped (f : X → ℂ) :
    finiteOperatorListAction row
      ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)) f =
    finiteRowComposition (S := fun _ => X)
      (finiteRowGrouped (S := fun _ => X) (fun i => row (physicalSelectedFineTag n i))
        visitThreeBlockLength) (2 * n + 1) f := by
  rw [finite_operator_list_action_map, ← finite_row_composition_eq_operator_list]
  exact (finite_row_visit_three_grouping_constant _ n f).symm

end Grouped
end Bounty

end

section

-- Original source module: PhysicalRootFourierRows

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

noncomputable def physicalRootFourierRow :
    Option (Fin (n + 2) ⊕ Fin (n + 1)) →
      (PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e → ℂ) →
      PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e → ℂ :=
  let _ : ∀ g (z : P (e.symm g).val), NeZero z.val :=
    fun g z => inferInstanceAs (NeZero (⟨(e.symm g).val, z⟩ : PhysicalPrime P).2.val)
  physicalMixedWordRow (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val))
    B
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val)) (fun (i : patterns) _ a => physicalAuxMass (fun g => V (e.symm g).val) (fun g => C i.val (e.symm g).val) a) (fun g p => β g p / V (e.symm g).val) retention ρ (fun g => V (e.symm g).val) (fun s : ↥groupsᶜ => V s.val) (fun _ => q) (physicalRootMixedFourierPhase groups e patterns C hC k V ζ K θ β ρ code encode ν hPs hPb hdis)

theorem physical_root_fourier_word_rows
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (L : PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B) :
    physicalRootFourierWord groups e patterns C hC k V q ζ K r θ β retention ρ hPs hPb hdis
      code encode ν f L x =
    finiteOperatorListAction
      (physicalRootFourierRow (n := n) groups e patterns C hC k V q ζ K θ β retention ρ hPs hPb hdis
        code encode ν)
      ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
      (fun s => f s.2) ((physicalGroupResidueVector r, L), x) := rfl


end Root
end Bounty

end

section

-- Original source module: PhysicalMixedRowAverage

/- Every row is the actual signed ghost row, the two permutation averages,
or the sum of actual mixed full actions over one pattern and one auxiliary. -/

open Finset
open scoped Classical
namespace Bounty
section Rows
variable {S G I V K : Type} [Fintype S] [Fintype G] [dG : DecidableEq G]
  [Fintype I] [dS : DecidableEq S] {Ps : S → Finset ℕ} {P : G → Type} [∀ g, Fintype (P g)]
  (n : ∀ g, P g → ℕ) [∀ g p, NeZero (n g p)] {J ell : ℕ} {M : G → ℕ}
  (shared : I → ∀ g, Finset (Fin (M g))) (B : ℕ)
  (A : I → Type) [∀ i, Fintype (A i)]
  (Δ D : ∀ _k : K, ∀ i, PhysicalSharedLists Ps J → SharedActiveLabels P (shared i) → A i → G → ℤ)
  (kbig : ∀ _k : K, ∀ i, SharedActiveLabels P (shared i) → A i → ℤ)
  (ω : ∀ i, SharedActiveLabels P (shared i) → A i → ℝ)
  (μ : ∀ g, P g → ℝ) (qghost : V → ℝ) (ρ : ℝ) (Vb : G → ℝ)
  (Vs : S → ℝ) (qedge : K → ℝ)
  (phase : ∀ tag s, PhysicalMixedWordEvent (ell := ell) n shared B A Δ D tag s → ℂ)

theorem physical_mixed_word_row_joint_average
    (hphase : ∀ s e, phase none s e = 1)
    (F : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B → ℂ)
    (s : PhysicalMixedWordState (Ps := Ps) (J := J) (ell := ell) (M := M) n B) :
    physicalMixedWordRow n shared B A Δ D kbig ω μ qghost ρ Vb Vs qedge phase none F s =
      physicalSmallBigJointAverage F s := by
  cases Subsingleton.elim dS (Classical.typeDecidableEq S)
  cases Subsingleton.elim dG (Classical.typeDecidableEq G)
  unfold physicalMixedWordRow finiteLocalPhasedRow
  rw [physical_small_big_joint_average_eq_sum]
  let _ := physicalMixedWordEventFintype (ell := ell) (V := V) n shared B A Δ D
  apply Finset.sum_congr
  · ext ev
    exact iff_of_true (@Finset.mem_univ _ _ ev) (@Finset.mem_univ _ _ ev)
  · intro ev _
    simp only [physicalMixedWordWeight, physicalMixedWordTarget]
    erw [hphase, mul_one]
    rfl
end Rows
end Bounty

end

section

-- Original source module: PhysicalRootFourierPermutation

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

theorem physical_root_fourier_permutation_row
    (f : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e → ℂ) :
    physicalRootFourierRow (n := n) groups e patterns C hC k V q ζ K θ β retention ρ hPs hPb hdis
      code encode ν none f =
      physicalSmallBigJointAverage (S := ↥groupsᶜ) (G := Fin M)
        (Ps := fun s => P s.val) (P := fun g => ↥(P (e.symm g).val))
        (Z := fun g => UnrestrictedResidueParticle (fun p : P (e.symm g).val => p.val))
        (J := J) (ell := ell) (M := fun _ => J + ell) (B := B) f := by
  funext s
  exact physical_mixed_word_row_joint_average (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val))
    B
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val)) (fun (i : patterns) _ a => physicalAuxMass (fun g => V (e.symm g).val) (fun g => C i.val (e.symm g).val) a) (fun g p => β g p / V (e.symm g).val) retention ρ (fun g => V (e.symm g).val) (fun s : ↥groupsᶜ => V s.val) (fun _ => q) (physicalRootMixedFourierPhase groups e patterns C hC k V ζ K θ β ρ code encode ν hPs hPb hdis)
    (fun y ev => physical_root_fourier_permutation_factor groups e patterns C hC k V ζ K θ β ρ
      code encode ν hPs hPb hdis y ev) f s

end Root
end Bounty

end
end

section

/- Root Fourier bridge bodies on the coherent actual-Z dependency boundary. -/

section

-- Original source module: PhysicalRootEdgeParameters

/- Named actual big-edge data keep dependent root coefficient statements small. -/

open scoped Classical
namespace Bounty
section Root
variable {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
  (groups : Finset (Fin N)) (reindex : {g // g ∉ groupsᶜ} ≃ Fin M)
  (patterns : Finset I) (C : I → Fin N → Finset (Fin J)) (k : ℕ → I → ℤ)
  (j : Fin (n + 1))
  (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups reindex)
  (ev : PhysicalRootMixedEvent groups reindex patterns C k (some (.inr j)) s)

noncomputable def physicalRootEdgeKey :
    PhysicalMixedBigKey (Ps := fun g : ↥groupsᶜ => P g.val)
      (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) :=
  (j, ev.1, s.1.2, ev.2.2.1)

variable (hPs : ∀ (g : ↥groupsᶜ) p, p ∈ P g.val → Nat.Prime p)
  (hPb : ∀ (g : Fin M) p, p ∈ P (reindex.symm g).val → Nat.Prime p)
  (hdis : ∀ (g : ↥groupsᶜ) (h : Fin M), Disjoint (P g.val) (P (reindex.symm h).val))

noncomputable def physicalRootEffectiveEdgeEvent :
    PhysicalFullEdgeEvent (fun g => C ev.1.val (reindex.symm g).val)
      (k (n - j.val) ev.1.val * (physicalSharedProduct (physicalSharedPrefix s.1.2) : ℕ)) s.2 :=
  let key := physicalRootEdgeKey groups reindex patterns C k j s ev
  let cuts := fun z : PhysicalMixedBigKey (Ps := fun g : ↥groupsᶜ => P g.val)
    (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      fun g => C z.2.1.val (reindex.symm g).val
  let prefixes := fun z : PhysicalMixedBigKey (Ps := fun g : ↥groupsᶜ => P g.val)
    (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      physicalSharedPrefix z.2.2.1
  let steps := fun z : PhysicalMixedBigKey (Ps := fun g : ↥groupsᶜ => P g.val)
    (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      k (n - z.1.val) z.2.1.val
  physicalMixedEffectiveBigEventEquiv hPs hPb hdis cuts prefixes steps B
    (some (.inr key) : Option (Fin (n + 2) ⊕ _)) s.2 ⟨ev.2.1, ev.2.2.2.2⟩

noncomputable def physicalRootEffectiveEdgeWeight
    (V : Fin N → ℝ) (β : (g : Fin M) → P (reindex.symm g).val → ℝ) (ρ : ℝ) : ℝ :=
  let cut := fun g => C ev.1.val (reindex.symm g).val
  let step := k (n - j.val) ev.1.val *
    (physicalSharedProduct (physicalSharedPrefix s.1.2) : ℕ)
  fullActiveEdgeEventWeight (fun g (p : P (reindex.symm g).val) => p.val)
    (fun g => physicalFullSharedIndices (cut g)) B
    (fun _ => PhysicalAuxLabels (fun g => P (reindex.symm g).val) cut)
    (physicalFullEdgeDelta cut step) (physicalFullEdgeD cut)
    (fun _ aux => physicalAuxMass (fun g => V (reindex.symm g).val) cut aux)
    (fun g p => β g p / V (reindex.symm g).val) ρ (fun g => V (reindex.symm g).val)
    s.2 (physicalRootEffectiveEdgeEvent groups reindex patterns C k j s ev hPs hPb hdis)

end Root
end Bounty

end

section

-- Original source module: PhysicalEffectiveCoefficientTransport

/- Effective big-event transport preserves the original active endpoints and
auxiliary draw used by the full key coefficient. -/

open scoped Classical
namespace Bounty
section Effective
variable {S K V : Type} [Fintype S] {N J ell : ℕ}
  {Ps : S → Finset ℕ} {P : Fin N → Finset ℕ}
  (hPs : ∀ s p, p ∈ Ps s → Nat.Prime p)
  (hP : ∀ g p, p ∈ P g → Nat.Prime p)
  (hdis : ∀ s g, Disjoint (Ps s) (P g))
  (C : K → Fin N → Finset (Fin J)) (d : K → PhysicalSharedLists Ps J)
  (k : K → ℤ) (B : ℕ)

theorem physical_mixed_effective_big_target
    (tag : Option (V ⊕ K)) (x : PhysicalFullBoundedState P J ell B)
    (e : FullPermutationMixedEvent (fun g (p : P g) => p.val)
      (fun key g => physicalFullSharedIndices (ell := ell) (C key g)) B
      (fun key _ => PhysicalAuxLabels P (C key))
      (fun key => physicalMixedEdgeDelta (C key) (k key) (d key))
      (fun key => physicalMixedEdgeD (C key) (d key)) tag x) :
    fullPermutationMixedEventTarget (fun g (p : P g) => p.val)
      (fun key g => physicalFullSharedIndices (ell := ell) (C key g)) B
      (fun key _ => PhysicalAuxLabels P (C key))
      (fun key => physicalFullEdgeDelta (C key)
        (k key * (physicalSharedProduct (d key) : ℕ)))
      (fun key => physicalFullEdgeD (C key)) tag x
      (physicalMixedEffectiveBigEventEquiv hPs hP hdis C d k B tag x e) =
    fullPermutationMixedEventTarget (fun g (p : P g) => p.val)
      (fun key g => physicalFullSharedIndices (ell := ell) (C key g)) B
      (fun key _ => PhysicalAuxLabels P (C key))
      (fun key => physicalMixedEdgeDelta (C key) (k key) (d key))
      (fun key => physicalMixedEdgeD (C key) (d key)) tag x e :=
  full_permutation_parameter_target _ _ B _ _ _ _ _
    (fun key => funext fun c => funext fun a => funext fun g =>
      physical_mixed_delta_effective_big_step (C key) (d key) (k key) c a g)
    (fun key c a g p =>
      physical_mixed_dilation_divisibility hPs hP hdis (C key) (d key) c a g p)
    tag x e

theorem physical_mixed_effective_big_auxiliary
    (key : K) (x : PhysicalFullBoundedState P J ell B)
    (e : FullPermutationMixedEvent (fun g (p : P g) => p.val)
      (fun key g => physicalFullSharedIndices (ell := ell) (C key g)) B
      (fun key _ => PhysicalAuxLabels P (C key))
      (fun key => physicalMixedEdgeDelta (C key) (k key) (d key))
      (fun key => physicalMixedEdgeD (C key) (d key))
      (some (.inr key) : Option (V ⊕ K)) x) :
    (physicalMixedEffectiveBigEventEquiv hPs hP hdis C d k B
      (some (.inr key) : Option (V ⊕ K)) x e).1 = e.1 :=
  full_active_parameter_auxiliary _ _ B _ _ _ _ _
    (funext fun c => funext fun a => funext fun g =>
      physical_mixed_delta_effective_big_step (C key) (d key) (k key) c a g)
    (fun c a g p =>
      physical_mixed_dilation_divisibility hPs hP hdis (C key) (d key) c a g p)
    x e

theorem physical_mixed_effective_key_coefficient
    (ζ : K → ℝ)
    (coeff : ∀ key, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
      PhysicalAuxLabels P (C key) → ℂ)
    (key : K) (x : PhysicalFullBoundedState P J ell B)
    (e : FullPermutationMixedEvent (fun g (p : P g) => p.val)
      (fun key g => physicalFullSharedIndices (ell := ell) (C key g)) B
      (fun key _ => PhysicalAuxLabels P (C key))
      (fun key => physicalMixedEdgeDelta (C key) (k key) (d key))
      (fun key => physicalMixedEdgeD (C key) (d key))
      (some (.inr key) : Option (V ⊕ K)) x) :
    physicalFullKeyCoefficientPhase C
      (fun key => k key * (physicalSharedProduct (d key) : ℕ)) ζ coeff
      (some (.inr key) : Option (V ⊕ K)) x
      (physicalMixedEffectiveBigEventEquiv hPs hP hdis C d k B
        (some (.inr key) : Option (V ⊕ K)) x e) =
    physicalActiveCoefficient (C key) (C key) (C key) (ζ key) (coeff key)
      (fun g => (x g).1)
      (fun g => (fullPermutationMixedEventTarget (fun g (p : P g) => p.val)
        (fun key g => physicalFullSharedIndices (ell := ell) (C key g)) B
        (fun key _ => PhysicalAuxLabels P (C key))
        (fun key => physicalMixedEdgeDelta (C key) (k key) (d key))
        (fun key => physicalMixedEdgeD (C key) (d key))
        (some (.inr key) : Option (V ⊕ K)) x e g).1) e.1 := by
  dsimp only [physicalFullKeyCoefficientPhase]
  rw [physical_mixed_effective_big_target, physical_mixed_effective_big_auxiliary]

end Effective
end Bounty

end

section

-- Original source module: PhysicalRootEdgeTransport

/- The named actual root edge preserves its target and auxiliary draw. -/

open scoped Classical
namespace Bounty
section Root
variable {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
  (groups : Finset (Fin N)) (reindex : {g // g ∉ groupsᶜ} ≃ Fin M)
  (patterns : Finset I) (C : I → Fin N → Finset (Fin J)) (k : ℕ → I → ℤ)
  (j : Fin (n + 1))
  (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups reindex)
  (ev : PhysicalRootMixedEvent groups reindex patterns C k (some (.inr j)) s)
  (hPs : ∀ (g : ↥groupsᶜ) p, p ∈ P g.val → Nat.Prime p)
  (hPb : ∀ (g : Fin M) p, p ∈ P (reindex.symm g).val → Nat.Prime p)
  (hdis : ∀ (g : ↥groupsᶜ) (h : Fin M), Disjoint (P g.val) (P (reindex.symm h).val))

theorem physical_root_effective_edge_auxiliary :
    (physicalRootEffectiveEdgeEvent groups reindex patterns C k j s ev hPs hPb hdis).1 =
      ev.2.1 := by
  unfold physicalRootEffectiveEdgeEvent
  exact physical_mixed_effective_big_auxiliary hPs hPb hdis _ _ _ B _ _ _

theorem physical_root_effective_edge_target :
    let cut := fun g => C ev.1.val (reindex.symm g).val
    let step := k (n - j.val) ev.1.val
    fullActiveEdgeEventTarget (fun g (p : P (reindex.symm g).val) => p.val)
      (fun g => physicalFullSharedIndices (cut g)) B
      (fun _ => PhysicalAuxLabels (fun g => P (reindex.symm g).val) cut)
      (physicalFullEdgeDelta cut (step * (physicalSharedProduct (physicalSharedPrefix s.1.2) : ℕ)))
      (physicalFullEdgeD cut) s.2
      (physicalRootEffectiveEdgeEvent groups reindex patterns C k j s ev hPs hPb hdis) =
    (physicalMixedCoefficientTarget cut step ev.2.1 s ev.2.2).2 := by
  intro cut step
  let key := physicalRootEdgeKey groups reindex patterns C k j s ev
  let cuts := fun z : PhysicalMixedBigKey (Ps := fun g : ↥groupsᶜ => P g.val)
    (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      fun g => C z.2.1.val (reindex.symm g).val
  let prefixes := fun z : PhysicalMixedBigKey (Ps := fun g : ↥groupsᶜ => P g.val)
    (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      physicalSharedPrefix z.2.2.1
  let steps := fun z : PhysicalMixedBigKey (Ps := fun g : ↥groupsᶜ => P g.val)
    (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      k (n - z.1.val) z.2.1.val
  have ht := physical_mixed_effective_big_target hPs hPb hdis cuts prefixes steps B
    (some (.inr key) : Option (Fin (n + 2) ⊕ _)) s.2 ⟨ev.2.1, ev.2.2.2.2⟩
  exact ht

end Root
end Bounty

end

section

-- Original source module: PhysicalRootLocalCoefficientTransport

/- A root mixed event uses its actual pattern, auxiliary draw, and mixed endpoint. -/

open scoped Classical
namespace Bounty

theorem physical_root_mixed_local_coefficient_transport
    {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
    (groups : Finset (Fin N)) (reindex : {g // g ∉ groupsᶜ} ≃ Fin M)
    (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
    (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
    (k : ℕ → I → ℤ) (V : Fin N → ℝ) (ζ : ℕ → I → ℝ)
    (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
      PhysicalAuxLabels P (C i) → ℂ)
    (θ : ℝ) (β : (g : Fin M) → P (reindex.symm g).val → ℝ) (ρ : ℝ)
    (hPs : ∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p)
    (hPb : ∀ (g : Fin M) p, p ∈ P (reindex.symm g).val → Nat.Prime p)
    (hdis : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (reindex.symm g).val))
    (j : Fin (n + 1)) (H : (g : Fin M) → Finset (P (reindex.symm g).val))
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups reindex)
    (ev : PhysicalRootMixedEvent groups reindex patterns C k (some (.inr j)) s) :
    let key : PhysicalMixedBigKey (Ps := fun g : ↥groupsᶜ => P g.val)
      (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) :=
      (j, ev.1, s.1.2, ev.2.2.1)
    let cuts := fun z : PhysicalMixedBigKey (Ps := fun g : ↥groupsᶜ => P g.val)
      (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      fun g => C z.2.1.val (reindex.symm g).val
    let prefixes := fun z : PhysicalMixedBigKey (Ps := fun g : ↥groupsᶜ => P g.val)
      (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      physicalSharedPrefix z.2.2.1
    let steps := fun z : PhysicalMixedBigKey (Ps := fun g : ↥groupsᶜ => P g.val)
      (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      k (n - z.1.val) z.2.1.val
    let effective := physicalMixedEffectiveBigEventEquiv hPs hPb hdis cuts prefixes steps B
      (some (.inr key) : Option (Fin (n + 2) ⊕ _)) s.2 ⟨ev.2.1, ev.2.2.2.2⟩
    let target := physicalMixedCoefficientTarget (cuts key) (steps key) ev.2.1 s ev.2.2
    physicalRootMixedLocalPhase groups reindex patterns C hC k V ζ K θ β ρ hPs hPb hdis
      (some (.inr j)) H s ev =
      physicalFullGlobalEdgePhase (cuts key)
        (steps key * (physicalSharedProduct (prefixes key) : ℕ)) H
        (fun _ aux => physicalAuxMass (fun g => V (reindex.symm g).val) (cuts key) aux)
        (fun g p => β g p / V (reindex.symm g).val) ρ (fun g => V (reindex.symm g).val)
        s.2 effective *
      physicalActiveCoefficient (cuts key) (cuts key) (cuts key) 0
        (physicalRootKeyCoefficient groups reindex patterns C hC ζ k K θ key)
        (fun g => (s.2 g).1) (fun g => (target.2 g).1) ev.2.1 := by
  dsimp only [physicalRootMixedLocalPhase, physicalMixedBigEventPullback,
    physicalMixedBigEventTag, physicalMixedBigEventProjection, physicalRootPlannedLocalPhase,
    physicalRootEffectiveLocalPhase]
  rw [physicalFullCombinedPhase]
  erw [physical_mixed_effective_key_coefficient]
  rfl

end Bounty

end

section

-- Original source module: FullLedgerActualTarget

/- Nonzero event weights identify the ledger phase at its actual target. -/

open Finset
open scoped Classical

namespace Bounty

theorem bounded_ledger_phase_at_target {P : Type*} [DecidableEq P]
    (n : P → ℕ) (Δ D : ℤ) (t B : ℕ) (target : Fin t → P) (H : Finset P)
    (μ : P → ℝ) (ρ V : ℝ)
    (s : BoundedOrderedState P (UnrestrictedResidueParticle n) t B)
    (e : UnrestrictedBoundedEvent n Δ D t B s)
    (hw : unrestrictedBoundedEventWeight n Δ D μ ρ V t B s e ≠ 0)
    (ht : (unrestrictedBoundedEventTarget n Δ D t B s e).1 = target) :
    globalBirthBoundedEdgePhase n Δ D t B target H s
      e.1 e.2.1 e.2.2.1 e.2.2.2 =
      if ∀ i, e.2.2.2 i ∉ H then 1 else 0 := by
  have hout : (unrestrictedEdgeOutput s.1 s.2.2 (unrestrictedResidueSeed n)
      (unrestrictedResidueTransport n Δ) e.1 e.2.1 e.2.2.1).1 ≤ B := by
    by_contra h
    exact hw (by simp only [unrestrictedBoundedEventWeight, h, and_false, if_false])
  have ht' : unrestrictedEdgeTarget s.2.2 Sigma.fst e.2.1 e.2.2.1 e.2.2.2 = target := by
    simpa only [unrestrictedBoundedEventTarget, dif_pos hout] using ht
  simp only [globalBirthBoundedEdgePhase, ht', true_and]

theorem full_ledger_phase_at_target
    {N : ℕ} {P : Fin N → Type*} [∀ g, Fintype (P g)] [∀ g, DecidableEq (P g)]
    (n : (g : Fin N) → P g → ℕ) {M : Fin N → ℕ}
    (S : (g : Fin N) → Finset (Fin (M g))) (B : ℕ)
    (A : SharedActiveLabels P S → Type*) [∀ c, Fintype (A c)]
    (Δ D : ∀ c, A c → Fin N → ℤ)
    (target : (g : Fin N) → Fin (S g)ᶜ.card → P g)
    (H : (g : Fin N) → Finset (P g))
    (ω : ∀ c, A c → ℝ) (μ : (g : Fin N) → P g → ℝ) (ρ : ℝ) (V : Fin N → ℝ)
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (e : FullActiveEdgeEvent n S B A Δ D x)
    (hw : fullActiveEdgeEventWeight n S B A Δ D ω μ ρ V x e ≠ 0)
    (ht : ∀ g,
      ((productActiveMemorySplit S B (fullActiveEdgeEventTarget n S B A Δ D x e)).2 g).1 =
        target g) :
    fullEdgeLedgerPhase n S B A Δ D target H x e =
      if ∀ g i, (e.2 g).2.2.2 i ∉ H g then 1 else 0 := by
  have he (g : Fin N) :
      globalBirthBoundedEdgePhase (n g)
        (Δ (productActiveMemorySplit S B x).1 e.1 g)
        (D (productActiveMemorySplit S B x).1 e.1 g) (S g)ᶜ.card B (target g) (H g)
        ((productActiveMemorySplit S B x).2 g)
        (e.2 g).1 (e.2 g).2.1 (e.2 g).2.2.1 (e.2 g).2.2.2 =
      if ∀ i, (e.2 g).2.2.2 i ∉ H g then 1 else 0 := by
    apply bounded_ledger_phase_at_target _ _ _ _ _ _ _ (μ g) ρ (V g)
      _ _ (full_edge_ledger_local_weight_ne_zero n S B A Δ D ω μ ρ V x e hw g)
    simpa only [fullActiveEdgeEventTarget, Equiv.apply_symm_apply,
      unrestrictedJointEventTarget] using ht g
  unfold fullEdgeLedgerPhase
  simp_rw [he]
  by_cases h : ∀ g i, (e.2 g).2.2.2 i ∉ H g
  · simp only [if_pos h, if_pos (h _), prod_const_one]
  · rw [if_neg h]
    obtain ⟨g, hg⟩ := not_forall.mp h
    exact prod_eq_zero (mem_univ g) (if_neg hg)

end Bounty

end

section

-- Original source module: PhysicalEndpointActualTarget

/- The physical endpoint sum selects its actual target on contributing events. -/

open Finset
open scoped Classical

namespace Bounty

section Physical
variable {N J ell B : ℕ} {P : Fin N → Finset ℕ}
  (C : Fin N → Finset (Fin J)) (k : ℤ) (L R : PhysicalMarkLists P J ell)
  (H : (g : Fin N) → Finset (P g))
  (q qR : (g : Fin N) → BoundedOrderedTuple
    (UnrestrictedResidueParticle (fun p : P g => p.val)) B)
  (ω : ∀ _c : SharedActiveLabels (fun g => P g)
    (fun g => physicalFullSharedIndices (ell := ell) (C g)), PhysicalAuxLabels P C → ℝ)
  (μ : (g : Fin N) → P g → ℝ) (ρ : ℝ) (V : Fin N → ℝ)
  (e : PhysicalFullEdgeEvent C k (physicalFullMemoryState C L q))

theorem physical_full_edge_phase_at_target
    (hw : fullActiveEdgeEventWeight (fun g (p : P g) => p.val)
      (fun g => physicalFullSharedIndices (C g)) B (fun _ => PhysicalAuxLabels P C)
      (physicalFullEdgeDelta C k) (physicalFullEdgeD C) ω μ ρ V
      (physicalFullMemoryState C L q) e ≠ 0)
    (ht : fullActiveEdgeEventTarget (fun g (p : P g) => p.val)
      (fun g => physicalFullSharedIndices (C g)) B (fun _ => PhysicalAuxLabels P C)
      (physicalFullEdgeDelta C k) (physicalFullEdgeD C)
      (physicalFullMemoryState C L q) e = physicalFullMemoryState C R qR) :
    physicalFullEdgePhase C k L R H q e =
      if physicalListAdmissible C e.1 L R ∧ (∀ g i, (e.2 g).2.2.2 i ∉ H g)
      then 1 else 0 := by
  by_cases ha : physicalListAdmissible C e.1 L R
  · simp only [physicalFullEdgePhase, ha, true_and]
    apply full_ledger_phase_at_target _ _ _ _ _ _ _ _ ω μ ρ V _ e hw
    intro g
    rw [ht, physical_full_memory_state_unshared, physical_full_memory_state_unshared]
  · simp only [physicalFullEdgePhase, ha, false_and, if_false]

theorem physical_full_endpoint_phase_at_target
    (hw : fullActiveEdgeEventWeight (fun g (p : P g) => p.val)
      (fun g => physicalFullSharedIndices (C g)) B (fun _ => PhysicalAuxLabels P C)
      (physicalFullEdgeDelta C k) (physicalFullEdgeD C) ω μ ρ V
      (physicalFullMemoryState C L q) e ≠ 0)
    (ht : fullActiveEdgeEventTarget (fun g (p : P g) => p.val)
      (fun g => physicalFullSharedIndices (C g)) B (fun _ => PhysicalAuxLabels P C)
      (physicalFullEdgeDelta C k) (physicalFullEdgeD C)
      (physicalFullMemoryState C L q) e = physicalFullMemoryState C R qR) :
    physicalFullEndpointPhase C k L H q ω μ ρ V e =
      if physicalListAdmissible C e.1 L R ∧ (∀ g i, (e.2 g).2.2.2 i ∉ H g)
      then 1 else 0 := by
  unfold physicalFullEndpointPhase
  rw [if_neg hw, sum_eq_single R]
  · exact physical_full_edge_phase_at_target C k L R H q qR ω μ ρ V e hw ht
  · intro T _ hTR
    by_contra hn
    have hy := physical_full_edge_target_of_nonzero C k L T H q ω μ ρ V e hw hn
    exact hTR (physical_full_state_labels_of_eq C T R _ _ (hy.symm.trans ht))
  · simp only [mem_univ, not_true_eq_false, false_implies]

theorem physical_full_endpoint_phase_zero_of_target_not_injective
    (hy : ¬ FullActiveInjective
      (fullActiveEdgeEventTarget (fun g (p : P g) => p.val)
        (fun g => physicalFullSharedIndices (C g)) B (fun _ => PhysicalAuxLabels P C)
        (physicalFullEdgeDelta C k) (physicalFullEdgeD C)
        (physicalFullMemoryState C L q) e)) :
    physicalFullEndpointPhase C k L H q ω μ ρ V e = 0 := by
  unfold physicalFullEndpointPhase
  split_ifs with hw
  · rfl
  · apply sum_eq_zero
    intro T _
    by_contra hn
    have ht := physical_full_edge_target_of_nonzero C k L T H q ω μ ρ V e hw hn
    apply hy
    rw [ht]
    exact physical_full_state_injective C T _

end Physical
end Bounty

end

section

-- Original source module: PhysicalGlobalActualTarget

/- The global physical phase is determined by its actual contributing target. -/

open scoped Classical

namespace Bounty

section Physical
variable {N J ell B : ℕ} {P : Fin N → Finset ℕ}
  (C : Fin N → Finset (Fin J)) (k : ℤ)
  (H : (g : Fin N) → Finset (P g))
  (ω : ∀ _c : SharedActiveLabels (fun g => P g)
    (fun g => physicalFullSharedIndices (ell := ell) (C g)), PhysicalAuxLabels P C → ℝ)
  (μ : (g : Fin N) → P g → ℝ) (ρ : ℝ) (V : Fin N → ℝ)

theorem physical_full_global_phase_at_target
    (x : PhysicalFullBoundedState P J ell B) (hx : FullActiveInjective x)
    (e : PhysicalFullEdgeEvent C k x)
    (hw : fullActiveEdgeEventWeight (fun g (p : P g) => p.val)
      (fun g => physicalFullSharedIndices (C g)) B (fun _ => PhysicalAuxLabels P C)
      (physicalFullEdgeDelta C k) (physicalFullEdgeD C) ω μ ρ V x e ≠ 0)
    (R : PhysicalMarkLists P J ell)
    (qR : (g : Fin N) → BoundedOrderedTuple
      (UnrestrictedResidueParticle (fun p : P g => p.val)) B)
    (ht : fullActiveEdgeEventTarget (fun g (p : P g) => p.val)
      (fun g => physicalFullSharedIndices (C g)) B (fun _ => PhysicalAuxLabels P C)
      (physicalFullEdgeDelta C k) (physicalFullEdgeD C) x e = physicalFullMemoryState C R qR) :
    physicalFullGlobalEdgePhase C k H ω μ ρ V x e =
      if physicalListAdmissible C e.1 (physicalFullStateLabels C x hx) R ∧
        (∀ g i, (e.2 g).2.2.2 i ∉ H g) then 1 else 0 := by
  have hencoded (L : PhysicalMarkLists P J ell)
      (q : (g : Fin N) → BoundedOrderedTuple
        (UnrestrictedResidueParticle (fun p : P g => p.val)) B)
      (e : PhysicalFullEdgeEvent C k (physicalFullMemoryState C L q))
      (hw : fullActiveEdgeEventWeight (fun g (p : P g) => p.val)
        (fun g => physicalFullSharedIndices (C g)) B (fun _ => PhysicalAuxLabels P C)
        (physicalFullEdgeDelta C k) (physicalFullEdgeD C) ω μ ρ V
        (physicalFullMemoryState C L q) e ≠ 0)
      (ht : fullActiveEdgeEventTarget (fun g (p : P g) => p.val)
        (fun g => physicalFullSharedIndices (C g)) B (fun _ => PhysicalAuxLabels P C)
        (physicalFullEdgeDelta C k) (physicalFullEdgeD C)
        (physicalFullMemoryState C L q) e = physicalFullMemoryState C R qR) :
      physicalFullGlobalEdgePhase C k H ω μ ρ V (physicalFullMemoryState C L q) e =
        if physicalListAdmissible C e.1 L R ∧ (∀ g i, (e.2 g).2.2.2 i ∉ H g)
        then 1 else 0 := by
    rw [physical_full_global_edge_phase_encode]
    exact physical_full_endpoint_phase_at_target C k L R H q qR ω μ ρ V e hw ht
  have he := hencoded (physicalFullStateLabels C x hx) (fun g => (x g).2)
  rw [physical_full_state_encode_labels C x hx] at he
  exact he e hw ht

theorem physical_full_global_phase_zero_of_target_not_injective
    (x : PhysicalFullBoundedState P J ell B) (e : PhysicalFullEdgeEvent C k x)
    (hy : ¬ FullActiveInjective
      (fullActiveEdgeEventTarget (fun g (p : P g) => p.val)
        (fun g => physicalFullSharedIndices (C g)) B (fun _ => PhysicalAuxLabels P C)
        (physicalFullEdgeDelta C k) (physicalFullEdgeD C) x e)) :
    physicalFullGlobalEdgePhase C k H ω μ ρ V x e = 0 := by
  by_cases hx : FullActiveInjective x
  · have hencoded (L : PhysicalMarkLists P J ell)
        (q : (g : Fin N) → BoundedOrderedTuple
          (UnrestrictedResidueParticle (fun p : P g => p.val)) B)
        (e : PhysicalFullEdgeEvent C k (physicalFullMemoryState C L q))
        (hy : ¬ FullActiveInjective
          (fullActiveEdgeEventTarget (fun g (p : P g) => p.val)
            (fun g => physicalFullSharedIndices (C g)) B (fun _ => PhysicalAuxLabels P C)
            (physicalFullEdgeDelta C k) (physicalFullEdgeD C)
            (physicalFullMemoryState C L q) e)) :
        physicalFullGlobalEdgePhase C k H ω μ ρ V (physicalFullMemoryState C L q) e = 0 := by
      rw [physical_full_global_edge_phase_encode]
      exact physical_full_endpoint_phase_zero_of_target_not_injective C k L H q ω μ ρ V e hy
    have he := hencoded (physicalFullStateLabels C x hx) (fun g => (x g).2)
    rw [physical_full_state_encode_labels C x hx] at he
    exact he e hy
  · simp only [physicalFullGlobalEdgePhase, dif_neg hx]

end Physical
end Bounty

end

section

-- Original source module: PhysicalSharedTargetCompatibility

/- Actual full-state targets preserve the shared physical labels. -/

open Finset

namespace Bounty

theorem physical_shared_compatible_of_full_memory_state_shared
    {G : Type*} {P : G → Finset ℕ} {Z : G → Type*} {J ell B : ℕ}
    (C : G → Finset (Fin J)) (L R : PhysicalMarkLists P J ell)
    (q r : ∀ g, BoundedOrderedTuple (Z g) B)
    (hshared :
      (productActiveMemorySplit (fun g => physicalFullSharedIndices (C g)) B
        (physicalFullMemoryState C L q)).1 =
      (productActiveMemorySplit (fun g => physicalFullSharedIndices (C g)) B
        (physicalFullMemoryState C R r)).1) :
    physicalSharedCompatible C L R := by
  classical
  intro g s hs
  let j := (physicalFullSlotIndex (ell := ell) (C g)).symm (Sum.inl s)
  have hj : j ∈ physicalFullSharedIndices (C g) := by
    apply (physical_full_slot_index_shared_iff (C g) j).mp
    rw [show physicalFullSlotIndex (C g) j = Sum.inl s from
      (physicalFullSlotIndex (C g)).apply_symm_apply _]
    exact (physical_mem_shared_slots_iff (C g) _).mpr ⟨s, hs, rfl⟩
  have he := congrFun (congrFun hshared g)
    ((physicalFullSharedIndices (C g)).equivFin ⟨j, hj⟩)
  change L g (physicalFullSlotIndex (C g)
      (((physicalFullSharedIndices (C g)).equivFin.symm
        ((physicalFullSharedIndices (C g)).equivFin ⟨j, hj⟩)).val)) =
    R g (physicalFullSlotIndex (C g)
      (((physicalFullSharedIndices (C g)).equivFin.symm
        ((physicalFullSharedIndices (C g)).equivFin ⟨j, hj⟩)).val)) at he
  simpa only [Equiv.symm_apply_apply, j, Equiv.apply_symm_apply] using he

theorem physical_full_event_target_shared_compatible
    {N J ell B : ℕ} {P : Fin N → Finset ℕ}
    (C : Fin N → Finset (Fin J)) (k : ℤ)
    (x : PhysicalFullBoundedState P J ell B) (hx : FullActiveInjective x)
    (e : PhysicalFullEdgeEvent C k x)
    (hy : FullActiveInjective (fullActiveEdgeEventTarget
      (fun g (p : P g) => p.val) (fun g => physicalFullSharedIndices (C g)) B
      (fun _ => PhysicalAuxLabels P C) (physicalFullEdgeDelta C k)
      (physicalFullEdgeD C) x e)) :
    physicalSharedCompatible C (physicalFullStateLabels C x hx)
      (physicalFullStateLabels C (fullActiveEdgeEventTarget
        (fun g (p : P g) => p.val) (fun g => physicalFullSharedIndices (C g)) B
        (fun _ => PhysicalAuxLabels P C) (physicalFullEdgeDelta C k)
        (physicalFullEdgeD C) x e) hy) := by
  apply physical_shared_compatible_of_full_memory_state_shared C _ _
    (fun g => (x g).2)
    (fun g => (fullActiveEdgeEventTarget
      (fun g (p : P g) => p.val) (fun g => physicalFullSharedIndices (C g)) B
      (fun _ => PhysicalAuxLabels P C) (physicalFullEdgeDelta C k)
      (physicalFullEdgeD C) x e g).2)
  rw [physical_full_state_encode_labels, physical_full_state_encode_labels]
  exact (fullActiveEdgeEventTarget_shared _ _ _ _ _ _ x e).symm

end Bounty

end

section

-- Original source module: PhysicalWeightedActualCoefficient

/- Exact weighted removal of the endpoint sum retains the two auxiliary bans. -/

open Finset
open scoped Classical

namespace Bounty

theorem physical_weighted_global_active_coefficient
    {N J ell B : ℕ} {P : Fin N → Finset ℕ}
    (C : Fin N → Finset (Fin J)) (k : ℤ)
    (ω : ∀ _c : SharedActiveLabels (fun g => P g)
      (fun g => physicalFullSharedIndices (ell := ell) (C g)), PhysicalAuxLabels P C → ℝ)
    (μ : (g : Fin N) → P g → ℝ) (ρ : ℝ) (V : Fin N → ℝ) (ζ : ℝ)
    (K : PhysicalMarkLists P J ell → PhysicalMarkLists P J ell → PhysicalAuxLabels P C → ℂ)
    (x : PhysicalFullBoundedState P J ell B) (e : PhysicalFullEdgeEvent C k x) :
    let y := fullActiveEdgeEventTarget (fun g (p : P g) => p.val)
      (fun g => physicalFullSharedIndices (C g)) B (fun _ => PhysicalAuxLabels P C)
      (physicalFullEdgeDelta C k) (physicalFullEdgeD C) x e
    let W := fullActiveEdgeEventWeight (fun g (p : P g) => p.val)
      (fun g => physicalFullSharedIndices (C g)) B (fun _ => PhysicalAuxLabels P C)
      (physicalFullEdgeDelta C k) (physicalFullEdgeD C) ω μ ρ V x e
    let source : RepeatedBigLists P J ell :=
      fun g j => (x g).1 ((physicalFullSlotIndex (C g)).symm j)
    let target : RepeatedBigLists P J ell :=
      fun g j => (y g).1 ((physicalFullSlotIndex (C g)).symm j)
    let coeff := physicalActiveCoefficient C C C ζ K (fun g => (x g).1) (fun g => (y g).1) e.1
    (W : ℂ) * (physicalFullGlobalEdgePhase C k (fun _ => ∅) ω μ ρ V x e * coeff) =
      (W : ℂ) * ((if repeatedBigAuxAvoids C e.1 source ∧ repeatedBigAuxAvoids C e.1 target
        then (1 : ℂ) else 0) * coeff) := by
  intro y W source target coeff
  by_cases hw : W = 0
  · simp only [hw, Complex.ofReal_zero, zero_mul]
  · by_cases hx : FullActiveInjective x
    · by_cases hy : FullActiveInjective y
      · have ht : y = physicalFullMemoryState C (physicalFullStateLabels C y hy)
            (fun g => (y g).2) := (physical_full_state_encode_labels C y hy).symm
        have hs := physical_full_event_target_shared_compatible C k x hx e hy
        have hp := physical_full_global_phase_at_target C k (fun _ => ∅) ω μ ρ V
          x hx e hw (physicalFullStateLabels C y hy) (fun g => (y g).2) ht
        have hs' : physicalSharedCompatible C (physicalFullStateLabels C x hx)
            (physicalFullStateLabels C y hy) := hs
        have hgate : physicalListAdmissible C e.1 (physicalFullStateLabels C x hx)
            (physicalFullStateLabels C y hy) ↔
            repeatedBigAuxAvoids C e.1 source ∧ repeatedBigAuxAvoids C e.1 target :=
          ⟨fun h => h.2, fun h => ⟨hs', h⟩⟩
        have hnone : ∀ g i, (e.2 g).2.2.2 i ∉ (∅ : Finset (P g)) :=
          fun _ _ => Finset.notMem_empty _
        have hp' : physicalFullGlobalEdgePhase C k (fun _ => ∅) ω μ ρ V x e =
            if repeatedBigAuxAvoids C e.1 source ∧ repeatedBigAuxAvoids C e.1 target
              then (1 : ℂ) else 0 := by
          simpa only [hnone, not_false_eq_true, forall_true_iff, and_true, hgate] using hp
        rw [hp']
      · have hc : coeff = 0 := by
          dsimp only [coeff]
          unfold physicalActiveCoefficient
          change (∀ g, Function.Injective (x g).1) at hx
          change ¬ (∀ g, Function.Injective (y g).1) at hy
          rw [dif_pos hx, dif_neg hy]
        simp only [hc, mul_zero]
    · have hc : coeff = 0 := by
        dsimp only [coeff]
        unfold physicalActiveCoefficient
        change ¬ (∀ g, Function.Injective (x g).1) at hx
        rw [dif_neg hx]
      simp only [hc, mul_zero]

end Bounty

end

section

-- Original source module: PhysicalRootWeightedEmptyCoefficient

/- The actual weighted big-edge residual is its exact auxiliary-gated active coefficient. -/

open scoped Classical
namespace Bounty

theorem physical_root_mixed_weighted_empty_coefficient
    {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
    (groups : Finset (Fin N)) (reindex : {g // g ∉ groupsᶜ} ≃ Fin M)
    (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
    (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
    (k : ℕ → I → ℤ) (V : Fin N → ℝ) (ζ : ℕ → I → ℝ)
    (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
      PhysicalAuxLabels P (C i) → ℂ)
    (θ : ℝ) (β : (g : Fin M) → P (reindex.symm g).val → ℝ) (ρ : ℝ)
    (hPs : ∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p)
    (hPb : ∀ (g : Fin M) p, p ∈ P (reindex.symm g).val → Nat.Prime p)
    (hdis : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (reindex.symm g).val))
    (j : Fin (n + 1))
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups reindex)
    (ev : PhysicalRootMixedEvent groups reindex patterns C k (some (.inr j)) s) :
    let cut := fun g => C ev.1.val (reindex.symm g).val
    let target := physicalMixedCoefficientTarget cut (k (n - j.val) ev.1.val) ev.2.1 s ev.2.2
    let W := physicalRootEffectiveEdgeWeight groups reindex patterns C k j s ev hPs hPb hdis V β ρ
    (W : ℂ) * physicalRootMixedLocalPhase groups reindex patterns C hC k V ζ K θ β ρ
      hPs hPb hdis (some (.inr j)) (fun _ => ∅) s ev =
      (W : ℂ) * ((if repeatedBigAuxAvoids cut ev.2.1 (physicalMixedRepeatedLabels cut s.2) ∧
        repeatedBigAuxAvoids cut ev.2.1 (physicalMixedRepeatedLabels cut target.2)
        then (1 : ℂ) else 0) *
      physicalActiveCoefficient cut cut cut 0
        (physicalRootKeyCoefficient groups reindex patterns C hC ζ k K θ
          (physicalRootEdgeKey groups reindex patterns C k j s ev))
        (fun g => (s.2 g).1) (fun g => (target.2 g).1) ev.2.1) := by
  intro cut target W
  have ht := physical_root_effective_edge_target groups reindex patterns C k j s ev hPs hPb hdis
  have ha := physical_root_effective_edge_auxiliary groups reindex patterns C k j s ev hPs hPb hdis
  have hw := physical_weighted_global_active_coefficient cut
    (k (n - j.val) ev.1.val * (physicalSharedProduct (physicalSharedPrefix s.1.2) : ℕ))
    (fun _ aux => physicalAuxMass (fun g => V (reindex.symm g).val) cut aux)
    (fun g p => β g p / V (reindex.symm g).val) ρ (fun g => V (reindex.symm g).val) 0
    (physicalRootKeyCoefficient groups reindex patterns C hC ζ k K θ
      (physicalRootEdgeKey groups reindex patterns C k j s ev)) s.2
    (physicalRootEffectiveEdgeEvent groups reindex patterns C k j s ev hPs hPb hdis)
  dsimp only at hw ht
  rw [ht, ha] at hw
  rw [physical_root_mixed_local_coefficient_transport]
  exact hw

end Bounty

end

section

-- Original source module: PhysicalCoupledFourierCoefficient

/- Exact original coefficient and phase factors after splitting and reindexing groups. -/

open scoped Classical
namespace Bounty

theorem physical_coupled_fourier_coefficient
    {G I : Type*} [Fintype G] {P : G → Finset ℕ} {J ell : ℕ}
    (small : G → Prop) (C : I → G → Finset (Fin J))
    (k : ℕ → I → ℤ)
    (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
      PhysicalAuxLabels P (C i) → ℂ)
    (ζ θ : ℝ) (t : ℕ) (i : I)
    (Ls Rs : PhysicalMarkLists (fun g : {g // small g} => P g.val) J ell)
    (aSmall : PhysicalAuxLabels (fun g : {g // small g} => P g.val)
      (fun g => C i g.val))
    (Lb Rb : PhysicalMarkLists (fun g : {g // ¬small g} => P g.val) J ell)
    (aBig : PhysicalAuxLabels (fun g : {g // ¬small g} => P g.val)
      (fun g => C i g.val)) :
    let L := (physicalMarkGroupSplit small P J ell).symm (Ls, Lb)
    let R := (physicalMarkGroupSplit small P J ell).symm (Rs, Rb)
    let a := (physicalAuxGroupSplit small P J (C i)).symm (aSmall, aBig)
    physicalCoupledBigCoefficient small (C i) ζ
      (physicalLocalFourierCoefficient C k K θ t i) Ls Rs aSmall Lb Rb aBig =
      K t i L R a * physicalPhase ζ (physicalD (C i) L a) *
        physicalReturnPhase θ (k t i * (physicalD (C i) L a : ℕ)) := by
  dsimp only
  let L := (physicalMarkGroupSplit small P J ell).symm (Ls, Lb)
  let a := (physicalAuxGroupSplit small P J (C i)).symm (aSmall, aBig)
  have hL := (physicalMarkGroupSplit small P J ell).apply_symm_apply (Ls, Lb)
  have ha := (physicalAuxGroupSplit small P J (C i)).apply_symm_apply (aSmall, aBig)
  have hLs : (fun g : {g // small g} => L g.val) = Ls := congrArg Prod.fst hL
  have hLb : (fun g : {g // ¬small g} => L g.val) = Lb := congrArg Prod.snd hL
  have has : (fun g : {g // small g} => a g.val) = aSmall := congrArg Prod.fst ha
  have hab : (fun g : {g // ¬small g} => a g.val) = aBig := congrArg Prod.snd ha
  have hD := physical_D_group_split small (C i) a L
  rw [hLs, hLb, has, hab] at hD
  change _ = K t i L _ a * physicalPhase ζ (physicalD (C i) L a) * _
  unfold physicalCoupledBigCoefficient physicalLocalFourierCoefficient
  change K t i L _ a * physicalReturnPhase θ (k t i * (physicalD (C i) L a : ℕ)) *
    physicalPhase ζ _ = _
  rw [← hD]
  ring

theorem physical_reindexed_coupled_fourier_coefficient
    {G H I : Type*} [Fintype G] [Fintype H]
    {P : G → Finset ℕ} {J ell B : ℕ}
    (small : G → Prop) (reindex : {g // ¬small g} ≃ H)
    (C : I → G → Finset (Fin J)) (k : ℕ → I → ℤ)
    (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
      PhysicalAuxLabels P (C i) → ℂ)
    (ζ θ : ℝ) (t : ℕ) (i : I) (hC : ∀ g, small g → C i g = ∅)
    (Ls Rs : PhysicalMarkLists (fun g : {g // small g} => P g.val) J ell)
    (aSmall : PhysicalAuxLabels (fun g : {g // small g} => P g.val)
      (fun g => C i g.val))
    (Lb Rb : PhysicalMarkLists (fun g => P (reindex.symm g).val) J ell)
    (aBig : PhysicalAuxLabels (fun g => P (reindex.symm g).val)
      (fun g => C i (reindex.symm g).val))
    {Z : H → Type*} (memory : ∀ g, BoundedOrderedTuple (Z g) B) :
    let Cb := fun g => C i (reindex.symm g).val
    let Lold := (physicalMarkGroupReindex reindex (fun g => P g.val) J ell).symm Lb
    let Rold := (physicalMarkGroupReindex reindex (fun g => P g.val) J ell).symm Rb
    let aold := (physicalAuxGroupReindex reindex (fun g => P g.val) J
      (fun g => C i g.val)).symm aBig
    let L := (physicalMarkGroupSplit small P J ell).symm (Ls, Lold)
    let R := (physicalMarkGroupSplit small P J ell).symm (Rs, Rold)
    let a := (physicalAuxGroupSplit small P J (C i)).symm (aSmall, aold)
    let cp := (productActiveMemorySplit (fun g => physicalFullSharedIndices (Cb g)) B
      (physicalFullMemoryState Cb Lb memory)).1
    let d := physicalSharedPrefix Ls
    physicalGroupReindexedCoefficient reindex (fun g => C i g.val)
      (physicalCoupledBigCoefficient small (C i) ζ
        (physicalLocalFourierCoefficient C k K θ t i) Ls Rs aSmall) Lb Rb aBig =
      K t i L R a * physicalPhase ζ (physicalMixedSharedD Cb d cp aBig) *
        physicalReturnPhase θ
          (physicalMixedBigStep Cb (k t i) cp aBig * (physicalSharedProduct d : ℕ)) := by
  dsimp only
  let Lold := (physicalMarkGroupReindex reindex (fun g => P g.val) J ell).symm Lb
  let aold := (physicalAuxGroupReindex reindex (fun g => P g.val) J
    (fun g => C i g.val)).symm aBig
  let L := (physicalMarkGroupSplit small P J ell).symm (Ls, Lold)
  let a := (physicalAuxGroupSplit small P J (C i)).symm (aSmall, aold)
  have hL := (physicalMarkGroupSplit small P J ell).apply_symm_apply (Ls, Lold)
  have ha := (physicalAuxGroupSplit small P J (C i)).apply_symm_apply (aSmall, aold)
  have hLs : (fun g : {g // small g} => L g.val) = Ls := congrArg Prod.fst hL
  have hLb : (fun g : {g // ¬small g} => L g.val) = Lold := congrArg Prod.snd hL
  have hab : (fun g : {g // ¬small g} => a g.val) = aold := congrArg Prod.snd ha
  have hD := physical_mixed_shared_D_reindexed small reindex (C i) hC a L memory
  rw [hLs, hLb, hab] at hD
  simp only [Lold, aold, Equiv.apply_symm_apply] at hD
  unfold physicalGroupReindexedCoefficient
  rw [physical_coupled_fourier_coefficient, physical_mixed_step_factor, hD]

end Bounty

end

section

-- Original source module: PhysicalRootKeyMixedCoefficient

/- The actual root key retains precisely the original coefficient and two mixed phases. -/

open scoped Classical
namespace Bounty

theorem physical_root_key_mixed_coefficient
    {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
    (groups : Finset (Fin N)) (reindex : {g // g ∉ groupsᶜ} ≃ Fin M)
    (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
    (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
    (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ)
    (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
      PhysicalAuxLabels P (C i) → ℂ) (θ : ℝ)
    (key : PhysicalMixedBigKey (Ps := fun g : ↥groupsᶜ => P g.val)
      (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)))
    (Lb Rb : PhysicalMarkLists (fun g => P (reindex.symm g).val) J ell)
    (aBig : PhysicalAuxLabels (fun g => P (reindex.symm g).val)
      (fun g => C key.2.1.val (reindex.symm g).val))
    {Z : Fin M → Type*} (memory : ∀ g, BoundedOrderedTuple (Z g) B) :
    let i := key.2.1.val
    let t := n - key.1.val
    let Cb := fun g => C i (reindex.symm g).val
    let Lold := (physicalMarkGroupReindex reindex (fun g => P g.val) J ell).symm Lb
    let Rold := (physicalMarkGroupReindex reindex (fun g => P g.val) J ell).symm Rb
    let aold := (physicalAuxGroupReindex reindex (fun g => P g.val) J
      (fun g => C i g.val)).symm aBig
    let L := (physicalMarkGroupSplit (fun g => g ∈ groupsᶜ) P J ell).symm
      (key.2.2.1, Lold)
    let R := (physicalMarkGroupSplit (fun g => g ∈ groupsᶜ) P J ell).symm
      (key.2.2.2, Rold)
    let a := (physicalAuxGroupSplit (fun g => g ∈ groupsᶜ) P J (C i)).symm
      (physicalEmptyAuxLabels (fun g : ↥groupsᶜ => C i g.val) (hC key.2.1), aold)
    let cp := (productActiveMemorySplit (fun g => physicalFullSharedIndices (Cb g)) B
      (physicalFullMemoryState Cb Lb memory)).1
    let d := physicalSharedPrefix key.2.2.1
    physicalRootKeyCoefficient groups reindex patterns C hC ζ k K θ key Lb Rb aBig =
      K t i L R a * physicalPhase (ζ t i) (physicalMixedSharedD Cb d cp aBig) *
        physicalReturnPhase θ
          (physicalMixedBigStep Cb (k t i) cp aBig * (physicalSharedProduct d : ℕ)) := by
  have h := physical_reindexed_coupled_fourier_coefficient (fun g => g ∈ groupsᶜ)
    reindex C k K (ζ (n - key.1.val) key.2.1.val) θ (n - key.1.val) key.2.1.val
    (fun g hg => hC key.2.1 ⟨g, hg⟩) key.2.2.1 key.2.2.2
    (physicalEmptyAuxLabels (fun g : ↥groupsᶜ => C key.2.1.val g.val) (hC key.2.1))
    Lb Rb aBig memory
  dsimp only [physicalRootKeyCoefficient] at h ⊢
  convert h using 1
  congr <;> exact Subsingleton.elim _ _

end Bounty

end

section

-- Original source module: PhysicalRootKeyProductCoefficient

/- The root-key phases use the exact small-prefix product times the big divisor. -/

open scoped Classical
namespace Bounty

theorem physical_root_key_product_coefficient
    {I : Type} {N M J ell n : ℕ} {P : Fin N → Finset ℕ}
    (groups : Finset (Fin N)) (reindex : {g // g ∉ groupsᶜ} ≃ Fin M)
    (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
    (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ, C i.val g.val = ∅)
    (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ)
    (K : ∀ (_ : ℕ) i, PhysicalMarkLists P J ell → PhysicalMarkLists P J ell →
      PhysicalAuxLabels P (C i) → ℂ) (θ : ℝ)
    (key : PhysicalMixedBigKey (Ps := fun g : ↥groupsᶜ => P g.val)
      (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)))
    (Lb Rb : PhysicalMarkLists (fun g => P (reindex.symm g).val) J ell)
    (aBig : PhysicalAuxLabels (fun g => P (reindex.symm g).val)
      (fun g => C key.2.1.val (reindex.symm g).val)) :
    let i := key.2.1.val
    let t := n - key.1.val
    let Cb := fun g => C i (reindex.symm g).val
    let Lold := (physicalMarkGroupReindex reindex (fun g => P g.val) J ell).symm Lb
    let Rold := (physicalMarkGroupReindex reindex (fun g => P g.val) J ell).symm Rb
    let aold := (physicalAuxGroupReindex reindex (fun g => P g.val) J
      (fun g => C i g.val)).symm aBig
    let L := (physicalMarkGroupSplit (fun g => g ∈ groupsᶜ) P J ell).symm
      (key.2.2.1, Lold)
    let R := (physicalMarkGroupSplit (fun g => g ∈ groupsᶜ) P J ell).symm
      (key.2.2.2, Rold)
    let a := (physicalAuxGroupSplit (fun g => g ∈ groupsᶜ) P J (C i)).symm
      (physicalEmptyAuxLabels (fun g : ↥groupsᶜ => C i g.val) (hC key.2.1), aold)
    let ds := physicalSharedProduct (physicalSharedPrefix key.2.2.1)
    physicalRootKeyCoefficient groups reindex patterns C hC ζ k K θ key Lb Rb aBig =
      K t i L R a * physicalPhase (ζ t i) (ds * physicalD Cb Lb aBig) *
        physicalReturnPhase θ
          (k t i * (ds * physicalD Cb Lb aBig : ℕ)) := by
  let memory : ∀ _g : Fin M, BoundedOrderedTuple Unit 0 :=
    fun _ => ⟨0, fun j => Fin.elim0 j⟩
  have h := physical_root_key_mixed_coefficient groups reindex patterns C hC ζ k K θ
    key Lb Rb aBig memory
  dsimp only at h ⊢
  simpa only [physical_mixed_step_factor, physical_mixed_shared_D_at_state] using h

end Bounty

end

section

-- Original source module: RepeatedBigFlatTransport

/- Flat prime coordinates and auxiliary cuts under an injective group map. -/

open Finset
open scoped Classical
namespace Bounty

def physicalPrimeFlatEmbedding {G H : Type*} {J ell : ℕ} (e : H ↪ G) :
    RepeatedBigFlatIndex H J ell ↪ RepeatedBigFlatIndex G J ell :=
  e.sigmaMap (fun _ => Function.Embedding.refl _)

theorem repeated_big_flat_embedding_apply {G H : Type*} {J ell : ℕ} (e : H ↪ G)
    (g : H) (s : PhysicalSlots J ell) :
    physicalPrimeFlatEmbedding e ⟨g,s⟩ = ⟨e g,s⟩ := rfl

theorem repeated_big_aux_cut_map {G H : Type*} [DecidableEq G] [DecidableEq H]
    {J ell : ℕ} (e : H ↪ G) (A B : Finset (RepeatedBigFlatIndex H J ell)) (g : H) :
    repeatedBigAuxCut (A.map (physicalPrimeFlatEmbedding e))
      (B.map (physicalPrimeFlatEmbedding e)) (e g) = repeatedBigAuxCut A B g := by
  ext j
  rw [mem_repeatedBigAuxCut, mem_repeatedBigAuxCut, ← map_union]
  change physicalPrimeFlatEmbedding e ⟨g,Sum.inl j⟩ ∈ (A ∪ B).map (physicalPrimeFlatEmbedding e) ↔ _
  exact mem_map' _

theorem repeated_big_aux_cut_map_outside {G H : Type*} [DecidableEq G] [DecidableEq H]
    {J ell : ℕ} (e : H ↪ G) (A B : Finset (RepeatedBigFlatIndex H J ell))
    (g : G) (hg : g ∉ Set.range e) :
    repeatedBigAuxCut (A.map (physicalPrimeFlatEmbedding e))
      (B.map (physicalPrimeFlatEmbedding e)) g = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro j hj
  rw [mem_repeatedBigAuxCut, ← map_union] at hj
  obtain ⟨x, _, hx⟩ := mem_map.mp hj
  exact hg ⟨x.1, congrArg Sigma.fst hx⟩

theorem repeated_big_probe_sigma_map {G H : Type*} [DecidableEq G] [DecidableEq H]
    {J ell : ℕ} (e : H ↪ G) (probes : G → Finset (Fin J)) (r : Finset H) :
    (r.sigma (repeatedBigPrimeProbeSlots (ell := ell) (fun g => probes (e g)))).map
      (physicalPrimeFlatEmbedding e) =
        (r.map e).sigma (repeatedBigPrimeProbeSlots (ell := ell) probes) := by
  ext x
  rcases x with ⟨g,s⟩
  constructor
  · intro hx
    obtain ⟨⟨a,t⟩, hat, hx⟩ := mem_map.mp hx
    have he : e a = g := congrArg Sigma.fst hx
    subst g
    have ht : t = s := congrArg (fun x : RepeatedBigFlatIndex G J ell => x.2) hx
    subst s
    exact mem_sigma.mpr ⟨mem_map.mpr ⟨a,(mem_sigma.mp hat).1,rfl⟩,(mem_sigma.mp hat).2⟩
  · intro hx
    obtain ⟨hg,hs⟩ := mem_sigma.mp hx
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hg
    exact mem_map.mpr ⟨⟨a,s⟩,mem_sigma.mpr ⟨ha,hs⟩,rfl⟩

end Bounty

end

section

-- Original source module: PhysicalPrimeKernelTransport

/- Prime-product cells and their comparison kernel are unchanged by a
reindexing of the original prime coordinates. -/

open Finset
open scoped BigOperators Classical
namespace Bounty

theorem prime_product_labels_reindex
    {I T : Type*} [Fintype I] [Fintype T]
    (e : I ≃ T) (P : T → Finset ℕ) (x : ∀ j, P j) :
    (∏ i, (x (e i)).val) = ∏ j, (x j).val :=
  e.prod_comp (fun j => (x j).val)

theorem prime_product_weight_reindex
    {I T : Type*} [Fintype I] [Fintype T]
    (e : I ≃ T) (P : T → Finset ℕ) (V : T → ℝ) (x : ∀ j, P j) :
    finiteProductWeight (physicalLabelLaw (P := fun i => P (e i)) (fun i => V (e i)))
      (fun i => x (e i)) = finiteProductWeight (physicalLabelLaw (P := P) V) x := by
  change (∏ i, physicalLabelLaw V (e i) (x (e i))) = ∏ j, physicalLabelLaw V j (x j)
  exact e.prod_comp (fun j => physicalLabelLaw V j (x j))

theorem prime_product_cell_mass_reindex
    {I T : Type*} [Fintype I] [Fintype T] [DecidableEq I] [DecidableEq T]
    (e : I ≃ T) (P : T → Finset ℕ) (V : T → ℝ) (h : ℝ) (d : ℤ) :
    finiteCellMass
      (finiteProductWeight (physicalLabelLaw (P := fun i => P (e i)) (fun i => V (e i))))
      (fun x => upperLogCell h (Real.log (∏ i, (x i).val : ℕ))) d =
    finiteCellMass (finiteProductWeight (physicalLabelLaw (P := P) V))
      (fun x => upperLogCell h (Real.log (∏ j, (x j).val : ℕ))) d := by
  unfold finiteCellMass
  rw [← (Equiv.piCongrLeft (fun j => ↥(P j)) e).symm.sum_comp]
  apply sum_congr rfl
  intro x _
  change (if upperLogCell h (Real.log (∏ i, (x (e i)).val : ℕ)) = d then
    finiteProductWeight (physicalLabelLaw (P := fun i => P (e i)) (fun i => V (e i)))
      (fun i => x (e i)) else 0) = _
  rw [prime_product_labels_reindex, prime_product_weight_reindex]

theorem prime_product_retained_cells_reindex
    {I T : Type*} [Fintype I] [Fintype T] [DecidableEq I] [DecidableEq T]
    (e : I ≃ T) (P : T → Finset ℕ) (V : T → ℝ) (h ξ : ℝ) :
    primeProductRetainedCells (fun i => P (e i)) (fun i => V (e i)) h ξ =
      primeProductRetainedCells P V h ξ := by
  have hocc :
      finiteOccupiedCells (fun x : (∀ i, P (e i)) =>
        upperLogCell h (Real.log (∏ i, (x i).val : ℕ))) =
      finiteOccupiedCells (fun x : (∀ j, P j) =>
        upperLogCell h (Real.log (∏ j, (x j).val : ℕ))) := by
    ext d
    simp only [finiteOccupiedCells, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨Equiv.piCongrLeft (fun j => ↥(P j)) e x, ?_⟩
      rw [← prime_product_labels_reindex e P]
      simpa only [Equiv.piCongrLeft_apply_apply] using hx
    · rintro ⟨x, hx⟩
      exact ⟨fun i => x (e i), by simpa only [prime_product_labels_reindex] using hx⟩
  unfold primeProductRetainedCells finiteRetainedCells
  simp only [hocc, prime_product_cell_mass_reindex]

theorem prime_product_ideal_kernel_reindex
    {I T : Type*} [Fintype I] [Fintype T] [DecidableEq I] [DecidableEq T]
    (e : I ≃ T) (P : T → Finset ℕ) (V : T → ℝ)
    (Q : ℕ) (h : ℝ) (kept : Finset ℤ) (x y : ∀ j, P j) :
    primeProductIdealKernel (fun i => P (e i)) (fun i => V (e i)) Q h kept
      (fun i => x (e i)) (fun i => y (e i)) =
      primeProductIdealKernel P V Q h kept x y := by
  unfold primeProductIdealKernel finiteCellFrameKernel finiteMeasureFrameKernel
  simp only [prime_product_labels_reindex, prime_product_cell_mass_reindex]

theorem prime_product_retained_kernel_reindex
    {I T : Type*} [Fintype I] [Fintype T] [DecidableEq I] [DecidableEq T]
    (e : I ≃ T) (P : T → Finset ℕ) (V : T → ℝ)
    (Q : ℕ) (h ξ : ℝ) (x y : ∀ j, P j) :
    primeProductIdealKernel (fun i => P (e i)) (fun i => V (e i)) Q h
      (primeProductRetainedCells (fun i => P (e i)) (fun i => V (e i)) h ξ)
      (fun i => x (e i)) (fun i => y (e i)) =
      primeProductIdealKernel P V Q h (primeProductRetainedCells P V h ξ) x y := by
  rw [prime_product_retained_cells_reindex, prime_product_ideal_kernel_reindex]

theorem prime_product_retained_kernel_reindex_star_swapped
    {I T : Type*} [Fintype I] [Fintype T] [DecidableEq I] [DecidableEq T]
    (e : I ≃ T) (P : T → Finset ℕ) (V : T → ℝ)
    (Q : ℕ) (h ξ : ℝ) (x y : ∀ j, P j) :
    star (primeProductIdealKernel (fun i => P (e i)) (fun i => V (e i)) Q h
      (primeProductRetainedCells (fun i => P (e i)) (fun i => V (e i)) h ξ)
      (fun i => y (e i)) (fun i => x (e i))) =
      star (primeProductIdealKernel P V Q h (primeProductRetainedCells P V h ξ) y x) :=
  congrArg star (prime_product_retained_kernel_reindex e P V Q h ξ y x)

theorem physical_prime_flat_map_avoids_tail
    {H G : Type*} [DecidableEq H] [DecidableEq G] {J ell : ℕ}
    (f : H ↪ G) (A B : Finset (RepeatedBigFlatIndex H J ell))
    (hU : ∀ g (j : Fin ell), (⟨g, Sum.inr j⟩ : RepeatedBigFlatIndex H J ell) ∉ A ∪ B) :
    ∀ g (j : Fin ell), (⟨g, Sum.inr j⟩ : RepeatedBigFlatIndex G J ell) ∉
      A.map (physicalPrimeFlatEmbedding f) ∪ B.map (physicalPrimeFlatEmbedding f) := by
  intro g j hj
  rw [← map_union] at hj
  rcases mem_map.mp hj with ⟨⟨g', s⟩, hs, he⟩
  have he' : s = Sum.inr j := congrArg (fun i : RepeatedBigFlatIndex G J ell => i.2) he
  subst s
  exact hU g' j hs

theorem repeated_big_prime_coefficient_map_split
    {H G : Type*} [Fintype H] [Fintype G] [DecidableEq H] [DecidableEq G]
    {J ell : ℕ} (f : H ↪ G) (P : G → Finset ℕ) (V : G → ℝ)
    (A B : Finset (RepeatedBigFlatIndex H J ell))
    (hU : ∀ g (j : Fin ell), (⟨g, Sum.inr j⟩ : RepeatedBigFlatIndex H J ell) ∉ A ∪ B)
    (hAB : Disjoint A B) (Q : ℕ) (h ξ : ℝ)
    (source target : RepeatedBigLists P J ell)
    (a : ∀ i : A.map (physicalPrimeFlatEmbedding f), P i.val.1)
    (b : ∀ i : B.map (physicalPrimeFlatEmbedding f), P i.val.1) :
    repeatedBigPrimeCoefficient (fun g => P (f g)) (fun g => V (f g)) A B hU hAB Q h
      (primeProductRetainedCells (fun i : A => P (f i.val.1)) (fun i => V (f i.val.1)) h ξ)
      (primeProductRetainedCells (fun i : B => P (f i.val.1)) (fun i => V (f i.val.1)) h ξ)
      (fun g => source (f g)) (fun g => target (f g))
      ((repeatedBigAuxSplitEquiv (fun g => P (f g)) A B hU hAB).symm
        (fun i => a (Finset.equivMap (physicalPrimeFlatEmbedding f) A i),
         fun i => b (Finset.equivMap (physicalPrimeFlatEmbedding f) B i))) =
    repeatedBigPrimeCoefficient P V
      (A.map (physicalPrimeFlatEmbedding f)) (B.map (physicalPrimeFlatEmbedding f))
      (physical_prime_flat_map_avoids_tail f A B hU) ((disjoint_map _).mpr hAB) Q h
      (primeProductRetainedCells
        (fun i : A.map (physicalPrimeFlatEmbedding f) => P i.val.1) (fun i => V i.val.1) h ξ)
      (primeProductRetainedCells
        (fun i : B.map (physicalPrimeFlatEmbedding f) => P i.val.1) (fun i => V i.val.1) h ξ)
      source target
      ((repeatedBigAuxSplitEquiv P (A.map (physicalPrimeFlatEmbedding f))
        (B.map (physicalPrimeFlatEmbedding f))
        (physical_prime_flat_map_avoids_tail f A B hU) ((disjoint_map _).mpr hAB)).symm (a, b)) := by
  erw [repeated_big_prime_coefficient_split, repeated_big_prime_coefficient_split]
  apply congrArg₂ (fun x y : ℂ => x * y)
  · exact prime_product_retained_kernel_reindex
      (Finset.equivMap (physicalPrimeFlatEmbedding f) A)
      (fun i => P i.val.1) (fun i => V i.val.1) Q h ξ a
      (finiteCoordinateRestrict (A.map (physicalPrimeFlatEmbedding f))
        (repeatedBigFlatEquiv P J ell target))
  · exact prime_product_retained_kernel_reindex
      (Finset.equivMap (physicalPrimeFlatEmbedding f) B)
      (fun i => P i.val.1) (fun i => V i.val.1) Q h ξ b
      (finiteCoordinateRestrict (B.map (physicalPrimeFlatEmbedding f))
        (repeatedBigFlatEquiv P J ell source))

noncomputable def physicalPrimeAuxPullback
    {H G : Type*} [DecidableEq H] [DecidableEq G] {J ell : ℕ}
    (f : H ↪ G) (P : G → Finset ℕ) (A B : Finset (RepeatedBigFlatIndex H J ell))
    (aux : PhysicalAuxLabels P (repeatedBigAuxCut
      (A.map (physicalPrimeFlatEmbedding f)) (B.map (physicalPrimeFlatEmbedding f)))) :
    PhysicalAuxLabels (fun g => P (f g)) (repeatedBigAuxCut A B) :=
  fun g j => aux (f g) ⟨j.val, by rw [repeated_big_aux_cut_map]; exact j.property⟩

theorem physical_prime_aux_pullback_split
    {H G : Type*} [DecidableEq H] [DecidableEq G] {J ell : ℕ}
    (f : H ↪ G) (P : G → Finset ℕ) (A B : Finset (RepeatedBigFlatIndex H J ell))
    (hU : ∀ g (j : Fin ell), (⟨g, Sum.inr j⟩ : RepeatedBigFlatIndex H J ell) ∉ A ∪ B)
    (hAB : Disjoint A B)
    (aux : PhysicalAuxLabels P (repeatedBigAuxCut
      (A.map (physicalPrimeFlatEmbedding f)) (B.map (physicalPrimeFlatEmbedding f)))) :
    repeatedBigAuxSplitEquiv (fun g => P (f g)) A B hU hAB
      (physicalPrimeAuxPullback f P A B aux) =
    (fun i => (repeatedBigAuxSplitEquiv P (A.map (physicalPrimeFlatEmbedding f))
      (B.map (physicalPrimeFlatEmbedding f)) (physical_prime_flat_map_avoids_tail f A B hU)
      ((disjoint_map _).mpr hAB) aux).1 (Finset.equivMap (physicalPrimeFlatEmbedding f) A i),
     fun i => (repeatedBigAuxSplitEquiv P (A.map (physicalPrimeFlatEmbedding f))
      (B.map (physicalPrimeFlatEmbedding f)) (physical_prime_flat_map_avoids_tail f A B hU)
      ((disjoint_map _).mpr hAB) aux).2 (Finset.equivMap (physicalPrimeFlatEmbedding f) B i)) := by
  apply Prod.ext
  · funext i
    rcases i with ⟨⟨g, j | j⟩, hi⟩
    · rfl
    · exact False.elim (hU g j (mem_union_left B hi))
  · funext i
    rcases i with ⟨⟨g, j | j⟩, hi⟩
    · rfl
    · exact False.elim (hU g j (mem_union_right A hi))

theorem repeated_big_prime_coefficient_map
    {H G : Type*} [Fintype H] [Fintype G] [DecidableEq H] [DecidableEq G]
    {J ell : ℕ} (f : H ↪ G) (P : G → Finset ℕ) (V : G → ℝ)
    (A B : Finset (RepeatedBigFlatIndex H J ell))
    (hU : ∀ g (j : Fin ell), (⟨g, Sum.inr j⟩ : RepeatedBigFlatIndex H J ell) ∉ A ∪ B)
    (hAB : Disjoint A B) (Q : ℕ) (h ξ : ℝ)
    (source target : RepeatedBigLists P J ell)
    (aux : PhysicalAuxLabels P (repeatedBigAuxCut
      (A.map (physicalPrimeFlatEmbedding f)) (B.map (physicalPrimeFlatEmbedding f)))) :
    repeatedBigPrimeCoefficient (fun g => P (f g)) (fun g => V (f g)) A B hU hAB Q h
      (primeProductRetainedCells (fun i : A => P (f i.val.1)) (fun i => V (f i.val.1)) h ξ)
      (primeProductRetainedCells (fun i : B => P (f i.val.1)) (fun i => V (f i.val.1)) h ξ)
      (fun g => source (f g)) (fun g => target (f g)) (physicalPrimeAuxPullback f P A B aux) =
    repeatedBigPrimeCoefficient P V
      (A.map (physicalPrimeFlatEmbedding f)) (B.map (physicalPrimeFlatEmbedding f))
      (physical_prime_flat_map_avoids_tail f A B hU) ((disjoint_map _).mpr hAB) Q h
      (primeProductRetainedCells
        (fun i : A.map (physicalPrimeFlatEmbedding f) => P i.val.1) (fun i => V i.val.1) h ξ)
      (primeProductRetainedCells
        (fun i : B.map (physicalPrimeFlatEmbedding f) => P i.val.1) (fun i => V i.val.1) h ξ)
      source target aux := by
  unfold repeatedBigPrimeCoefficient
  erw [physical_prime_aux_pullback_split]
  apply congrArg₂ (fun x y : ℂ => x * y)
  · exact prime_product_retained_kernel_reindex
      (Finset.equivMap (physicalPrimeFlatEmbedding f) A)
      (fun i => P i.val.1) (fun i => V i.val.1) Q h ξ
      (repeatedBigAuxSplitEquiv P (A.map (physicalPrimeFlatEmbedding f))
        (B.map (physicalPrimeFlatEmbedding f)) (physical_prime_flat_map_avoids_tail f A B hU)
        ((disjoint_map _).mpr hAB) aux).1
      (finiteCoordinateRestrict (A.map (physicalPrimeFlatEmbedding f))
        (repeatedBigFlatEquiv P J ell target))
  · exact prime_product_retained_kernel_reindex
      (Finset.equivMap (physicalPrimeFlatEmbedding f) B)
      (fun i => P i.val.1) (fun i => V i.val.1) Q h ξ
      (repeatedBigAuxSplitEquiv P (A.map (physicalPrimeFlatEmbedding f))
        (B.map (physicalPrimeFlatEmbedding f)) (physical_prime_flat_map_avoids_tail f A B hU)
        ((disjoint_map _).mpr hAB) aux).2
      (finiteCoordinateRestrict (B.map (physicalPrimeFlatEmbedding f))
        (repeatedBigFlatEquiv P J ell source))

end Bounty

end

section

-- Original source module: RepeatedBigPatternTransport

/- Exact transport of the raw and comparison pattern family under a group embedding. -/

open Finset
open scoped Classical
namespace Bounty

theorem clean_nonempty_subset_map {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (e : X ↪ Y) {U A : Finset X} (hA : A ∈ cleanNonemptySubsets U) :
    A.map e ∈ cleanNonemptySubsets (U.map e) := by
  rw [clean_mem_nonempty_subsets] at hA ⊢
  exact ⟨fun h => hA.1 ((map_eq_empty.mp h)), map_subset_map.mpr hA.2⟩

noncomputable def repeatedBigPrimePatternPairMap {G H : Type*} [DecidableEq G] [DecidableEq H]
    {J ell : ℕ} (e : H ↪ G) (probes : G → Finset (Fin J)) (r t : Finset H)
    (ab : RepeatedBigPrimePatternPair (ell := ell) (fun g => probes (e g)) r t) :
    RepeatedBigPrimePatternPair (ell := ell) probes (r.map e) (t.map e) :=
  (⟨ab.1.val.map (physicalPrimeFlatEmbedding e), by
      rw [← repeated_big_probe_sigma_map]
      exact clean_nonempty_subset_map (physicalPrimeFlatEmbedding e) ab.1.property⟩,
   ⟨ab.2.val.map (physicalPrimeFlatEmbedding e), by
      rw [← repeated_big_probe_sigma_map]
      exact clean_nonempty_subset_map (physicalPrimeFlatEmbedding e) ab.2.property⟩)

theorem repeated_big_prime_pattern_pair_map_card
    {G H : Type*} [DecidableEq G] [DecidableEq H] {J ell : ℕ}
    (e : H ↪ G) (probes : G → Finset (Fin J)) (r t : Finset H)
    (ab : RepeatedBigPrimePatternPair (ell := ell) (fun g => probes (e g)) r t) :
    (repeatedBigPrimePatternPairMap e probes r t ab).1.val.card = ab.1.val.card ∧
      (repeatedBigPrimePatternPairMap e probes r t ab).2.val.card = ab.2.val.card := by
  simp only [repeatedBigPrimePatternPairMap, card_map, and_self]

noncomputable def repeatedBigPrimePatternMap {G H : Type*} [DecidableEq G] [DecidableEq H]
    {J ell : ℕ} (e : H ↪ G) (probes : G → Finset (Fin J)) (r t : Finset H) :
    RepeatedBigPrimePatternIndex (ell := ell) (fun g => probes (e g)) r t →
      RepeatedBigPrimePatternIndex (ell := ell) probes (r.map e) (t.map e)
  | .inl u => .inl u
  | .inr ab => .inr (repeatedBigPrimePatternPairMap e probes r t ab)

theorem repeated_big_prime_pattern_map_weight
    {G H : Type*} [DecidableEq G] [DecidableEq H] {J ell : ℕ}
    (e : H ↪ G) (probes : G → Finset (Fin J)) (r t : Finset H)
    (i : RepeatedBigPrimePatternIndex (ell := ell) (fun g => probes (e g)) r t) :
    repeatedBigPrimePatternWeight probes (r.map e) (t.map e)
      (repeatedBigPrimePatternMap e probes r t i) =
        repeatedBigPrimePatternWeight (fun g => probes (e g)) r t i := by
  cases i <;> simp [repeatedBigPrimePatternMap, repeatedBigPrimePatternPairMap, repeatedBigPrimePatternWeight]

theorem repeated_big_prime_pattern_map_cut
    {G H : Type*} [DecidableEq G] [DecidableEq H] {J ell : ℕ}
    (e : H ↪ G) (probes : G → Finset (Fin J)) (r t : Finset H)
    (i : RepeatedBigPrimePatternIndex (ell := ell) (fun g => probes (e g)) r t) (g : H) :
    repeatedBigPrimePatternCut probes (r.map e) (t.map e)
      (repeatedBigPrimePatternMap e probes r t i) (e g) =
        repeatedBigPrimePatternCut (fun g => probes (e g)) r t i g := by
  cases i with
  | inl u => rfl
  | inr ab => exact repeated_big_aux_cut_map e ab.1.val ab.2.val g

theorem repeated_big_prime_pattern_map_cut_outside
    {G H : Type*} [DecidableEq G] [DecidableEq H] {J ell : ℕ}
    (e : H ↪ G) (probes : G → Finset (Fin J)) (r t : Finset H)
    (i : RepeatedBigPrimePatternIndex (ell := ell) (fun g => probes (e g)) r t)
    (g : G) (hg : g ∉ Set.range e) :
    repeatedBigPrimePatternCut probes (r.map e) (t.map e)
      (repeatedBigPrimePatternMap e probes r t i) g = ∅ := by
  cases i with
  | inl u => rfl
  | inr ab => exact repeated_big_aux_cut_map_outside e ab.1.val ab.2.val g hg

theorem repeated_big_prime_pattern_map_injective
    {G H : Type*} [DecidableEq G] [DecidableEq H] {J ell : ℕ}
    (e : H ↪ G) (probes : G → Finset (Fin J)) (r t : Finset H) :
    Function.Injective (repeatedBigPrimePatternMap (ell := ell) e probes r t) := by
  intro i j hij
  cases i with
  | inl u =>
    cases j with
    | inl v => exact congrArg Sum.inl (Subsingleton.elim u v)
    | inr ab => simp [repeatedBigPrimePatternMap] at hij
  | inr ab =>
    cases j with
    | inl u => simp [repeatedBigPrimePatternMap] at hij
    | inr cd =>
      apply congrArg Sum.inr
      have he := Sum.inr.inj hij
      apply Prod.ext
      · apply Subtype.ext
        exact map_injective (physicalPrimeFlatEmbedding e) (congrArg (fun x => x.1.val) he)
      · apply Subtype.ext
        exact map_injective (physicalPrimeFlatEmbedding e) (congrArg (fun x => x.2.val) he)

theorem repeated_big_prime_pattern_map_surjective
    {G H : Type*} [DecidableEq G] [DecidableEq H] {J ell : ℕ}
    (e : H ↪ G) (probes : G → Finset (Fin J)) (r t : Finset H) :
    Function.Surjective (repeatedBigPrimePatternMap (ell := ell) e probes r t) := by
  intro i
  cases i with
  | inl u => exact ⟨.inl u,rfl⟩
  | inr ab =>
    have ha := (clean_mem_nonempty_subsets _ _).mp ab.1.property
    have hb := (clean_mem_nonempty_subsets _ _).mp ab.2.property
    have ha' : ab.1.val ⊆ (r.sigma (repeatedBigPrimeProbeSlots (ell := ell)
        (fun g => probes (e g)))).map (physicalPrimeFlatEmbedding e) := by
      simpa only [repeated_big_probe_sigma_map] using ha.2
    have hb' : ab.2.val ⊆ (t.sigma (repeatedBigPrimeProbeSlots (ell := ell)
        (fun g => probes (e g)))).map (physicalPrimeFlatEmbedding e) := by
      simpa only [repeated_big_probe_sigma_map] using hb.2
    obtain ⟨A,hA,hAe⟩ := subset_map_iff.mp ha'
    obtain ⟨B,hB,hBe⟩ := subset_map_iff.mp hb'
    have hAn : A ≠ ∅ := by intro h; exact ha.1 (by simp [hAe,h])
    have hBn : B ≠ ∅ := by intro h; exact hb.1 (by simp [hBe,h])
    refine ⟨.inr (⟨A,(clean_mem_nonempty_subsets _ _).mpr ⟨hAn,hA⟩⟩,
      ⟨B,(clean_mem_nonempty_subsets _ _).mpr ⟨hBn,hB⟩⟩),?_⟩
    apply congrArg Sum.inr
    apply Prod.ext
    · exact Subtype.ext hAe.symm
    · exact Subtype.ext hBe.symm

noncomputable def repeatedBigPrimePatternEquiv
    {G H : Type*} [DecidableEq G] [DecidableEq H] {J ell : ℕ}
    (e : H ↪ G) (probes : G → Finset (Fin J)) (r t : Finset H) :
    RepeatedBigPrimePatternIndex (ell := ell) (fun g => probes (e g)) r t ≃
      RepeatedBigPrimePatternIndex (ell := ell) probes (r.map e) (t.map e) :=
  Equiv.ofBijective (repeatedBigPrimePatternMap e probes r t)
    ⟨repeated_big_prime_pattern_map_injective e probes r t,
      repeated_big_prime_pattern_map_surjective e probes r t⟩

theorem repeated_big_prime_pattern_equiv_apply
    {G H : Type*} [DecidableEq G] [DecidableEq H] {J ell : ℕ}
    (e : H ↪ G) (probes : G → Finset (Fin J)) (r t : Finset H)
    (i : RepeatedBigPrimePatternIndex (ell := ell) (fun g => probes (e g)) r t) :
    repeatedBigPrimePatternEquiv e probes r t i = repeatedBigPrimePatternMap e probes r t i := rfl

theorem repeated_big_prime_pattern_equiv_symm_cut
    {G H : Type*} [DecidableEq G] [DecidableEq H] {J ell : ℕ}
    (e : H ↪ G) (probes : G → Finset (Fin J)) (r t : Finset H)
    (i : RepeatedBigPrimePatternIndex (ell := ell) probes (r.map e) (t.map e)) (g : H) :
    repeatedBigPrimePatternCut (fun g => probes (e g)) r t
      ((repeatedBigPrimePatternEquiv e probes r t).symm i) g =
        repeatedBigPrimePatternCut probes (r.map e) (t.map e) i (e g) := by
  have h := repeated_big_prime_pattern_map_cut e probes r t
    ((repeatedBigPrimePatternEquiv e probes r t).symm i) g
  rw [← repeated_big_prime_pattern_equiv_apply, Equiv.apply_symm_apply] at h
  exact h.symm

theorem repeated_big_prime_pattern_equiv_symm_weight
    {G H : Type*} [DecidableEq G] [DecidableEq H] {J ell : ℕ}
    (e : H ↪ G) (probes : G → Finset (Fin J)) (r t : Finset H)
    (i : RepeatedBigPrimePatternIndex (ell := ell) probes (r.map e) (t.map e)) :
    repeatedBigPrimePatternWeight (fun g => probes (e g)) r t
      ((repeatedBigPrimePatternEquiv e probes r t).symm i) =
        repeatedBigPrimePatternWeight probes (r.map e) (t.map e) i := by
  have h := repeated_big_prime_pattern_map_weight e probes r t
    ((repeatedBigPrimePatternEquiv e probes r t).symm i)
  rw [← repeated_big_prime_pattern_equiv_apply, Equiv.apply_symm_apply] at h
  exact h.symm

end Bounty

end

section

-- Original source module: PhysicalPrimeKernelAdjoint

/- The even Gram coefficient retains its conjugated, endpoint-swapped kernel. -/

open scoped Classical
namespace Bounty

theorem repeated_big_prime_pattern_weight_conj
    {G : Type*} [DecidableEq G] {J ell : ℕ}
    (probes : G → Finset (Fin J)) (r t : Finset G)
    (i : RepeatedBigPrimePatternIndex (ell := ell) probes r t) :
    (starRingEnd ℂ) (repeatedBigPrimePatternWeight probes r t i) =
      repeatedBigPrimePatternWeight probes r t i := by
  cases i <;> simp only [repeatedBigPrimePatternWeight, map_one, map_neg, map_pow]

theorem physical_root_prime_kernel_conj_swap
    {G : Type*} [Fintype G] [DecidableEq G] {J ell : ℕ}
    (P : G → Finset ℕ) (V : G → ℝ) (probes : G → Finset (Fin J))
    (r t : Finset G) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (i : RepeatedBigPrimePatternIndex (ell := ell) probes r t)
    (L R : PhysicalMarkLists P J ell)
    (aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes r t i)) :
    (starRingEnd ℂ) (physicalRootPrimeKernel P V probes r t hrt Q h ξ i R L aux) =
      repeatedBigPrimePatternWeight probes r t i *
        (starRingEnd ℂ) (repeatedBigPrimePatternKernel P V probes r t hrt Q h
          (fun U : Finset (RepeatedBigFlatIndex G J ell) =>
            primeProductRetainedCells (fun j : U => P j.val.1) (fun j => V j.val.1) h ξ)
          i (fun g s => R g s) (fun g s => L g s) aux) := by
  rw [physicalRootPrimeKernel, map_mul, repeated_big_prime_pattern_weight_conj]

end Bounty

end

section

-- Original source module: PhysicalRootPrimeKernelTransport

/- The actual signed root prime kernel restricts exactly to its mapped big groups. -/

open scoped Classical
namespace Bounty

noncomputable def physicalPrimePatternAuxPullback
    {H G : Type*} [DecidableEq H] [DecidableEq G] {J ell : ℕ}
    (f : H ↪ G) (P : G → Finset ℕ) (probes : G → Finset (Fin J))
    (r t : Finset H)
    (i : RepeatedBigPrimePatternIndex (ell := ell) (fun g => probes (f g)) r t)
    (aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes (r.map f) (t.map f)
      (repeatedBigPrimePatternMap f probes r t i))) :
    PhysicalAuxLabels (fun g => P (f g))
      (repeatedBigPrimePatternCut (fun g => probes (f g)) r t i) :=
  fun g j => aux (f g) ⟨j.val, by rw [repeated_big_prime_pattern_map_cut]; exact j.property⟩

theorem repeated_big_prime_pattern_kernel_map
    {H G : Type*} [Fintype H] [Fintype G] [DecidableEq H] [DecidableEq G]
    {J ell : ℕ} (f : H ↪ G) (P : G → Finset ℕ) (V : G → ℝ)
    (probes : G → Finset (Fin J)) (r t : Finset H) (hrt : Disjoint r t)
    (Q : ℕ) (h ξ : ℝ)
    (i : RepeatedBigPrimePatternIndex (ell := ell) (fun g => probes (f g)) r t)
    (source target : RepeatedBigLists P J ell)
    (aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes (r.map f) (t.map f)
      (repeatedBigPrimePatternMap f probes r t i))) :
    repeatedBigPrimePatternKernel (fun g => P (f g)) (fun g => V (f g))
      (fun g => probes (f g)) r t hrt Q h
      (fun U : Finset (RepeatedBigFlatIndex H J ell) =>
        primeProductRetainedCells (fun j : U => P (f j.val.1)) (fun j => V (f j.val.1)) h ξ)
      i (fun g => source (f g)) (fun g => target (f g))
      (physicalPrimePatternAuxPullback f P probes r t i aux) =
    repeatedBigPrimePatternKernel P V probes (r.map f) (t.map f) ((Finset.disjoint_map f).mpr hrt)
      Q h (fun U : Finset (RepeatedBigFlatIndex G J ell) =>
        primeProductRetainedCells (fun j : U => P j.val.1) (fun j => V j.val.1) h ξ)
      (repeatedBigPrimePatternMap f probes r t i) source target aux := by
  cases i with
  | inl u => rfl
  | inr ab =>
    have hv := repeated_big_prime_pattern_pair_valid (fun g => probes (f g)) r t hrt ab
    exact repeated_big_prime_coefficient_map f P V ab.1.val ab.2.val
      (repeated_big_active_pair_avoids_tail hv.1 hv.2.1) hv.2.2 Q h ξ source target aux

theorem physical_root_prime_kernel_map
    {H G : Type*} [Fintype H] [Fintype G] [DecidableEq H] [DecidableEq G]
    {J ell : ℕ} (f : H ↪ G) (P : G → Finset ℕ) (V : G → ℝ)
    (probes : G → Finset (Fin J)) (r t : Finset H) (hrt : Disjoint r t)
    (Q : ℕ) (h ξ : ℝ)
    (i : RepeatedBigPrimePatternIndex (ell := ell) (fun g => probes (f g)) r t)
    (L R : PhysicalMarkLists P J ell)
    (aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes (r.map f) (t.map f)
      (repeatedBigPrimePatternMap f probes r t i))) :
    physicalRootPrimeKernel (fun g => P (f g)) (fun g => V (f g))
      (fun g => probes (f g)) r t hrt Q h ξ i (fun g => L (f g)) (fun g => R (f g))
      (physicalPrimePatternAuxPullback f P probes r t i aux) =
    physicalRootPrimeKernel P V probes (r.map f) (t.map f) ((Finset.disjoint_map f).mpr hrt)
      Q h ξ (repeatedBigPrimePatternMap f probes r t i) L R aux := by
  unfold physicalRootPrimeKernel
  rw [repeated_big_prime_pattern_map_weight]
  exact congrArg (fun z => repeatedBigPrimePatternWeight (fun g => probes (f g)) r t i * z)
    (repeated_big_prime_pattern_kernel_map f P V probes r t hrt Q h ξ i
      (fun g s => L g s) (fun g s => R g s) aux)

theorem physical_root_prime_kernel_map_conj_swap
    {H G : Type*} [Fintype H] [Fintype G] [DecidableEq H] [DecidableEq G]
    {J ell : ℕ} (f : H ↪ G) (P : G → Finset ℕ) (V : G → ℝ)
    (probes : G → Finset (Fin J)) (r t : Finset H) (hrt : Disjoint r t)
    (Q : ℕ) (h ξ : ℝ)
    (i : RepeatedBigPrimePatternIndex (ell := ell) (fun g => probes (f g)) r t)
    (L R : PhysicalMarkLists P J ell)
    (aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes (r.map f) (t.map f)
      (repeatedBigPrimePatternMap f probes r t i))) :
    (starRingEnd ℂ) (physicalRootPrimeKernel (fun g => P (f g)) (fun g => V (f g))
      (fun g => probes (f g)) r t hrt Q h ξ i (fun g => R (f g)) (fun g => L (f g))
      (physicalPrimePatternAuxPullback f P probes r t i aux)) =
    (starRingEnd ℂ) (physicalRootPrimeKernel P V probes (r.map f) (t.map f)
      ((Finset.disjoint_map f).mpr hrt) Q h ξ (repeatedBigPrimePatternMap f probes r t i) R L aux) :=
  congrArg (starRingEnd ℂ) (physical_root_prime_kernel_map f P V probes r t hrt Q h ξ i R L aux)

theorem physical_root_prime_kernel_equiv
    {H G : Type*} [Fintype H] [Fintype G] [DecidableEq H] [DecidableEq G]
    {J ell : ℕ} (f : H ↪ G) (P : G → Finset ℕ) (V : G → ℝ)
    (probes : G → Finset (Fin J)) (r t : Finset H) (hrt : Disjoint r t)
    (Q : ℕ) (h ξ : ℝ)
    (i : RepeatedBigPrimePatternIndex (ell := ell) probes (r.map f) (t.map f))
    (L R : PhysicalMarkLists P J ell)
    (aux : PhysicalAuxLabels P (repeatedBigPrimePatternCut probes (r.map f) (t.map f) i)) :
    physicalRootPrimeKernel P V probes (r.map f) (t.map f) ((Finset.disjoint_map f).mpr hrt)
      Q h ξ i L R aux =
    physicalRootPrimeKernel (fun g => P (f g)) (fun g => V (f g))
      (fun g => probes (f g)) r t hrt Q h ξ
      ((repeatedBigPrimePatternEquiv f probes r t).symm i)
      (fun g => L (f g)) (fun g => R (f g))
      (fun g j => aux (f g) ⟨j.val, by
        rw [← repeated_big_prime_pattern_equiv_symm_cut]
        exact j.property⟩) := by
  obtain ⟨i, rfl⟩ := repeated_big_prime_pattern_map_surjective f probes r t i
  have hinv : (repeatedBigPrimePatternEquiv f probes r t).symm
      (repeatedBigPrimePatternMap f probes r t i) = i :=
    (repeatedBigPrimePatternEquiv f probes r t).symm_apply_apply i
  have hc
      (u v : RepeatedBigPrimePatternIndex (ell := ell) (fun g => probes (f g)) r t)
      (huv : u = v)
      (au : PhysicalAuxLabels (fun g => P (f g))
        (repeatedBigPrimePatternCut (fun g => probes (f g)) r t u))
      (av : PhysicalAuxLabels (fun g => P (f g))
        (repeatedBigPrimePatternCut (fun g => probes (f g)) r t v))
      (ha : ∀ g (x : ↥(repeatedBigPrimePatternCut (fun g => probes (f g)) r t u g)),
        au g x = av g ⟨x.val, by rw [← huv]; exact x.property⟩) :
      physicalRootPrimeKernel (fun g => P (f g)) (fun g => V (f g))
        (fun g => probes (f g)) r t hrt Q h ξ u (fun g => L (f g)) (fun g => R (f g)) au =
      physicalRootPrimeKernel (fun g => P (f g)) (fun g => V (f g))
        (fun g => probes (f g)) r t hrt Q h ξ v (fun g => L (f g)) (fun g => R (f g)) av := by
    subst v
    apply congrArg (fun a => physicalRootPrimeKernel (fun g => P (f g)) (fun g => V (f g))
      (fun g => probes (f g)) r t hrt Q h ξ u (fun g => L (f g)) (fun g => R (f g)) a)
    funext g x
    exact ha g x
  refine (physical_root_prime_kernel_map f P V probes r t hrt Q h ξ i L R aux).symm.trans
    (hc i _ hinv.symm _ _ ?_)
  intro g x
  rfl

end Bounty

end

section

-- Original source module: PhysicalMergedBigRestriction

/- Restricting merged original labels and auxiliary draws to reindexed big groups. -/

open scoped Classical
namespace Bounty

theorem physical_merged_mark_reindex
    {G H : Type*} {P : G → Finset ℕ} {J ell : ℕ}
    (small : G → Prop) (e : {g // ¬small g} ≃ H)
    (Ls : PhysicalMarkLists (fun g : {g // small g} => P g.val) J ell)
    (Lb : PhysicalMarkLists (fun g => P (e.symm g).val) J ell) :
    (fun g => ((physicalMarkGroupSplit small P J ell).symm
      (Ls, (physicalMarkGroupReindex e (fun g => P g.val) J ell).symm Lb))
        (e.symm g).val) = Lb := by
  have h := congrArg Prod.snd ((physicalMarkGroupSplit small P J ell).apply_symm_apply
    (Ls, (physicalMarkGroupReindex e (fun g => P g.val) J ell).symm Lb))
  funext g
  exact (congrFun h (e.symm g)).trans
    (congrFun ((physicalMarkGroupReindex e (fun g => P g.val) J ell).apply_symm_apply Lb) g)

theorem physical_merged_aux_reindex
    {G H : Type*} {P : G → Finset ℕ} {J : ℕ}
    (small : G → Prop) (e : {g // ¬small g} ≃ H) (C : G → Finset (Fin J))
    (as : PhysicalAuxLabels (fun g : {g // small g} => P g.val) (fun g => C g.val))
    (ab : PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C (e.symm g).val)) :
    (fun g => ((physicalAuxGroupSplit small P J C).symm
      (as, (physicalAuxGroupReindex e (fun g => P g.val) J (fun g => C g.val)).symm ab))
        (e.symm g).val) = ab := by
  have h := congrArg Prod.snd ((physicalAuxGroupSplit small P J C).apply_symm_apply
    (as, (physicalAuxGroupReindex e (fun g => P g.val) J (fun g => C g.val)).symm ab))
  funext g
  exact (congrFun h (e.symm g)).trans
    (congrFun ((physicalAuxGroupReindex e (fun g => P g.val) J
      (fun g => C g.val)).apply_symm_apply ab) g)

end Bounty

end

section

-- Original source module: PhysicalMergedPrimeKernel

/- The original prime kernel on merged endpoints is exactly its big-group kernel. -/

open scoped Classical
namespace Bounty

noncomputable def physicalReindexedBigEmbedding {G H : Type*}
    (small : G → Prop) (e : {g // ¬small g} ≃ H) : H ↪ G :=
  ⟨fun h => (e.symm h).val, fun _ _ h => e.symm.injective (Subtype.ext h)⟩

theorem physical_root_prime_kernel_merged
    {G H : Type*} [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
    {J ell : ℕ} (P : G → Finset ℕ) (V : G → ℝ)
    (small : G → Prop) (e : {g // ¬small g} ≃ H)
    (probes : G → Finset (Fin J)) (r t : Finset H) (hrt : Disjoint r t)
    (Q : ℕ) (h ξ : ℝ)
    (i : RepeatedBigPrimePatternIndex (ell := ell) (fun g => probes (e.symm g).val) r t)
    (Ls Rs : PhysicalMarkLists (fun g : {g // small g} => P g.val) J ell)
    (Lb Rb : PhysicalMarkLists (fun g => P (e.symm g).val) J ell)
    (aSmall : PhysicalAuxLabels (fun g : {g // small g} => P g.val)
      (fun g => repeatedBigPrimePatternCut probes
        (r.map (physicalReindexedBigEmbedding small e)) (t.map (physicalReindexedBigEmbedding small e))
        (repeatedBigPrimePatternMap (physicalReindexedBigEmbedding small e) probes r t i) g.val))
    (aBig : PhysicalAuxLabels (fun g => P (e.symm g).val)
      (fun g => repeatedBigPrimePatternCut probes
        (r.map (physicalReindexedBigEmbedding small e)) (t.map (physicalReindexedBigEmbedding small e))
        (repeatedBigPrimePatternMap (physicalReindexedBigEmbedding small e) probes r t i) (e.symm g).val)) :
    let f := physicalReindexedBigEmbedding small e
    let C := repeatedBigPrimePatternCut probes (r.map f) (t.map f)
      (repeatedBigPrimePatternMap f probes r t i)
    let L := (physicalMarkGroupSplit small P J ell).symm
      (Ls, (physicalMarkGroupReindex e (fun g => P g.val) J ell).symm Lb)
    let R := (physicalMarkGroupSplit small P J ell).symm
      (Rs, (physicalMarkGroupReindex e (fun g => P g.val) J ell).symm Rb)
    let a := (physicalAuxGroupSplit small P J C).symm
      (aSmall, (physicalAuxGroupReindex e (fun g => P g.val) J (fun g => C g.val)).symm aBig)
    physicalRootPrimeKernel P V probes (r.map f) (t.map f) ((Finset.disjoint_map f).mpr hrt)
      Q h ξ (repeatedBigPrimePatternMap f probes r t i) L R a =
    physicalRootPrimeKernel (fun g => P (e.symm g).val) (fun g => V (e.symm g).val)
      (fun g => probes (e.symm g).val) r t hrt Q h ξ i Lb Rb
      (fun g j => aBig g ⟨j.val, by
        change j.val ∈ repeatedBigPrimePatternCut probes (r.map f) (t.map f)
          (repeatedBigPrimePatternMap f probes r t i) (f g)
        erw [repeated_big_prime_pattern_map_cut]
        exact j.property⟩) := by
  dsimp only
  let f := physicalReindexedBigEmbedding small e
  let C := repeatedBigPrimePatternCut probes (r.map f) (t.map f)
    (repeatedBigPrimePatternMap f probes r t i)
  let L := (physicalMarkGroupSplit small P J ell).symm
    (Ls, (physicalMarkGroupReindex e (fun g => P g.val) J ell).symm Lb)
  let R := (physicalMarkGroupSplit small P J ell).symm
    (Rs, (physicalMarkGroupReindex e (fun g => P g.val) J ell).symm Rb)
  let a := (physicalAuxGroupSplit small P J C).symm
    (aSmall, (physicalAuxGroupReindex e (fun g => P g.val) J (fun g => C g.val)).symm aBig)
  have hm := physical_root_prime_kernel_map f P V probes r t hrt Q h ξ i L R a
  have hL : (fun g => L (f g)) = Lb := physical_merged_mark_reindex small e Ls Lb
  have hR : (fun g => R (f g)) = Rb := physical_merged_mark_reindex small e Rs Rb
  rw [hL, hR] at hm
  rw [← hm]
  congr 1
  funext g j
  exact congrFun (congrFun (physical_merged_aux_reindex small e C aSmall aBig) g)
    ⟨j.val, by
      change j.val ∈ repeatedBigPrimePatternCut probes (r.map f) (t.map f)
        (repeatedBigPrimePatternMap f probes r t i) (f g)
      erw [repeated_big_prime_pattern_map_cut]
      exact j.property⟩

theorem physical_root_prime_kernel_merged_equiv
    {G H : Type*} [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
    {J ell : ℕ} (P : G → Finset ℕ) (V : G → ℝ)
    (small : G → Prop) (e : {g // ¬small g} ≃ H)
    (probes : G → Finset (Fin J)) (r t : Finset H) (hrt : Disjoint r t)
    (Q : ℕ) (h ξ : ℝ)
    (i : RepeatedBigPrimePatternIndex (ell := ell) probes
      (r.map (physicalReindexedBigEmbedding small e)) (t.map (physicalReindexedBigEmbedding small e)))
    (Ls Rs : PhysicalMarkLists (fun g : {g // small g} => P g.val) J ell)
    (Lb Rb : PhysicalMarkLists (fun g => P (e.symm g).val) J ell)
    (aSmall : PhysicalAuxLabels (fun g : {g // small g} => P g.val)
      (fun g => repeatedBigPrimePatternCut probes
        (r.map (physicalReindexedBigEmbedding small e)) (t.map (physicalReindexedBigEmbedding small e)) i g.val))
    (aBig : PhysicalAuxLabels (fun g => P (e.symm g).val)
      (fun g => repeatedBigPrimePatternCut probes
        (r.map (physicalReindexedBigEmbedding small e)) (t.map (physicalReindexedBigEmbedding small e)) i
          (e.symm g).val)) :
    let f := physicalReindexedBigEmbedding small e
    let C := repeatedBigPrimePatternCut probes (r.map f) (t.map f) i
    let L := (physicalMarkGroupSplit small P J ell).symm
      (Ls, (physicalMarkGroupReindex e (fun g => P g.val) J ell).symm Lb)
    let R := (physicalMarkGroupSplit small P J ell).symm
      (Rs, (physicalMarkGroupReindex e (fun g => P g.val) J ell).symm Rb)
    let a := (physicalAuxGroupSplit small P J C).symm
      (aSmall, (physicalAuxGroupReindex e (fun g => P g.val) J (fun g => C g.val)).symm aBig)
    physicalRootPrimeKernel P V probes (r.map f) (t.map f) ((Finset.disjoint_map f).mpr hrt)
      Q h ξ i L R a =
    physicalRootPrimeKernel (fun g => P (e.symm g).val) (fun g => V (e.symm g).val)
      (fun g => probes (e.symm g).val) r t hrt Q h ξ
      ((repeatedBigPrimePatternEquiv f probes r t).symm i) Lb Rb
      (fun g j => aBig g ⟨j.val, by
        change j.val ∈ repeatedBigPrimePatternCut probes (r.map f) (t.map f) i (f g)
        rw [← repeated_big_prime_pattern_equiv_symm_cut]
        exact j.property⟩) := by
  dsimp only
  let f := physicalReindexedBigEmbedding small e
  let C := repeatedBigPrimePatternCut probes (r.map f) (t.map f) i
  let L := (physicalMarkGroupSplit small P J ell).symm
    (Ls, (physicalMarkGroupReindex e (fun g => P g.val) J ell).symm Lb)
  let R := (physicalMarkGroupSplit small P J ell).symm
    (Rs, (physicalMarkGroupReindex e (fun g => P g.val) J ell).symm Rb)
  let a := (physicalAuxGroupSplit small P J C).symm
    (aSmall, (physicalAuxGroupReindex e (fun g => P g.val) J (fun g => C g.val)).symm aBig)
  have hm := physical_root_prime_kernel_equiv f P V probes r t hrt Q h ξ i L R a
  have hL : (fun g => L (f g)) = Lb := physical_merged_mark_reindex small e Ls Lb
  have hR : (fun g => R (f g)) = Rb := physical_merged_mark_reindex small e Rs Rb
  rw [hL, hR] at hm
  rw [hm]
  congr 1
  funext g j
  exact congrFun (congrFun (physical_merged_aux_reindex small e C aSmall aBig) g)
    ⟨j.val, by
      change j.val ∈ repeatedBigPrimePatternCut probes (r.map f) (t.map f) i (f g)
      rw [← repeated_big_prime_pattern_equiv_symm_cut]
      exact j.property⟩

end Bounty

end

section

-- Original source module: PhysicalRootPrimeKeyCoefficient

/- The chronological root key retains its exact prime kernel, including
the conjugated, reversed-endpoint branch, and both original phase factors. -/

open scoped Classical
namespace Bounty

theorem physical_root_prime_key_coefficient
    {I : Type} {N M J ell n : ℕ} {P : Fin N → Finset ℕ}
    (groups : Finset (Fin N)) (reindex : {g // g ∉ groupsᶜ} ≃ Fin M)
    (V : Fin N → ℝ) (probes : Fin N → Finset (Fin J))
    (r t : Finset (Fin M)) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (patterns : Finset I)
    (iota : I → RepeatedBigPrimePatternIndex (ell := ell) probes
      (r.map (physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex))
      (t.map (physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex)))
    (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ,
      repeatedBigPrimePatternCut probes
        (r.map (physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex))
        (t.map (physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex))
        (iota i.val) g.val = ∅)
    (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ) (θ : ℝ)
    (key : PhysicalMixedBigKey (Ps := fun g : ↥groupsᶜ => P g.val)
      (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)))
    (Lb Rb : PhysicalMarkLists (fun g => P (reindex.symm g).val) J ell)
    (aBig : PhysicalAuxLabels (fun g => P (reindex.symm g).val)
      (fun g => repeatedBigPrimePatternCut probes
        (r.map (physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex))
        (t.map (physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex))
        (iota key.2.1.val) (reindex.symm g).val)) :
    let f := physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex
    let C := fun i => repeatedBigPrimePatternCut probes (r.map f) (t.map f) (iota i)
    let K := fun (time : ℕ) (i : I) (L R : PhysicalMarkLists P J ell)
      (aux : PhysicalAuxLabels P (C i)) =>
      if time % 2 = 0 then
        (starRingEnd ℂ) (physicalRootPrimeKernel P V probes (r.map f) (t.map f)
          ((Finset.disjoint_map f).mpr hrt) Q h ξ (iota i) R L aux)
      else physicalRootPrimeKernel P V probes (r.map f) (t.map f)
        ((Finset.disjoint_map f).mpr hrt) Q h ξ (iota i) L R aux
    let i := key.2.1.val
    let time := n - key.1.val
    let smallPattern := (repeatedBigPrimePatternEquiv f probes r t).symm (iota i)
    let aRestricted : PhysicalAuxLabels (fun g => P (reindex.symm g).val)
      (repeatedBigPrimePatternCut (fun g => probes (reindex.symm g).val) r t smallPattern) :=
      fun g j => aBig g ⟨j.val, by
        change j.val ∈ repeatedBigPrimePatternCut probes (r.map f) (t.map f) (iota i) (f g)
        rw [← repeated_big_prime_pattern_equiv_symm_cut]
        exact j.property⟩
    let kernel := fun L R => physicalRootPrimeKernel
      (fun g => P (reindex.symm g).val) (fun g => V (reindex.symm g).val)
      (fun g => probes (reindex.symm g).val) r t hrt Q h ξ smallPattern L R aRestricted
    let ds := physicalSharedProduct (physicalSharedPrefix key.2.2.1)
    physicalRootKeyCoefficient groups reindex patterns C hC ζ k K θ key Lb Rb aBig =
      (if time % 2 = 0 then (starRingEnd ℂ) (kernel Rb Lb) else kernel Lb Rb) *
        physicalPhase (ζ time i) (ds * physicalD (fun g => C i (reindex.symm g).val) Lb aBig) *
        physicalReturnPhase θ
          (k time i * (ds * physicalD (fun g => C i (reindex.symm g).val) Lb aBig : ℕ)) := by
  dsimp only
  rw [physical_root_key_product_coefficient]
  let f := physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex
  let C := fun i => repeatedBigPrimePatternCut probes (r.map f) (t.map f) (iota i)
  let aSmall : PhysicalAuxLabels (fun g : ↥groupsᶜ => P g.val)
      (fun g => C key.2.1.val g.val) := physicalEmptyAuxLabels
    (fun g : ↥groupsᶜ => C key.2.1.val g.val) (hC key.2.1)
  have ho := physical_root_prime_kernel_merged_equiv P V (fun g => g ∈ groupsᶜ) reindex
    probes r t hrt Q h ξ (iota key.2.1.val) key.2.2.1 key.2.2.2 Lb Rb aSmall aBig
  have he := physical_root_prime_kernel_merged_equiv P V (fun g => g ∈ groupsᶜ) reindex
    probes r t hrt Q h ξ (iota key.2.1.val) key.2.2.2 key.2.2.1 Rb Lb aSmall aBig
  split_ifs
  · erw [he]
  · erw [ho]

end Bounty

end

section

-- Original source module: PhysicalMixedActiveResidual

/- The actual injective endpoint coefficient has precisely the concrete mixed residual. -/

open scoped Classical
namespace Bounty

theorem physical_mixed_active_coefficient_residual
    {S : Type} [Fintype S] {N J ell B : ℕ}
    {Ps : S → Finset ℕ} {P : Fin N → Finset ℕ}
    (C : Fin N → Finset (Fin J)) (ζ θ : ℝ) (k : ℤ)
    (K : RepeatedBigLists P J ell → RepeatedBigLists P J ell →
      PhysicalAuxLabels P C → ℂ)
    (a : PhysicalAuxLabels P C)
    (s : PhysicalSmallBigState Ps J ell (CleanFullMemoryState P J ell B))
    (e : PhysicalMixedCoefficientEvent C k a s) :
    let source := physicalMixedRepeatedLabels C s.2
    let targetState := physicalMixedCoefficientTarget C k a s e
    let target := physicalMixedRepeatedLabels C targetState.2
    let ds := physicalSharedProduct (physicalSharedPrefix s.1.2)
    (if repeatedBigAuxAvoids C a source ∧ repeatedBigAuxAvoids C a target
      then (1 : ℂ) else 0) *
      physicalActiveCoefficient C C C 0
        (fun L R aux => K (fun g j => L g j) (fun g j => R g j) aux *
          physicalPhase ζ (ds * physicalD C L aux) *
          physicalReturnPhase θ (k * (ds * physicalD C L aux : ℕ)))
        (fun g => (s.2 g).1) (fun g => (targetState.2 g).1) a =
      K source target a * physicalMixedFullResidualPhase C ζ θ k
        cleanMixedSourceGate (cleanMixedTargetGate (fun _ => ∅)) a s e := by
  dsimp only
  let y := physicalMixedCoefficientTarget C k a s e
  by_cases hs : ∀ g, Function.Injective (s.2 g).1
  · by_cases ht : ∀ g, Function.Injective (y.2 g).1
    · let L := physicalActiveMarkLabels C (fun g => (s.2 g).1) hs
      have hstate : physicalFullMemoryState C L (fun g => (s.2 g).2) = s.2 := by
        funext g
        apply Prod.ext
        · funext j
          change (s.2 g).1 ((physicalFullSlotIndex (C g)).symm
            (physicalFullSlotIndex (C g) j)) = (s.2 g).1 j
          rw [Equiv.symm_apply_apply]
        · rfl
      have hD := physical_mixed_shared_D_at_state C (physicalSharedPrefix s.1.2)
        L (fun g => (s.2 g).2) a
      rw [hstate] at hD
      have hsource : (fun g j => L g j) = physicalMixedRepeatedLabels C s.2 := rfl
      have htarget : (fun g j =>
          physicalActiveMarkLabels C (fun g => (y.2 g).1) ht g j) =
          physicalMixedRepeatedLabels C y.2 := rfl
      change _ = K (physicalMixedRepeatedLabels C s.2) (physicalMixedRepeatedLabels C y.2) a * _
      unfold physicalActiveCoefficient
      rw [dif_pos hs, dif_pos ht, physical_phase_zero_frequency, mul_one]
      change _ * (K (fun g j => L g j) _ a * _ * _) = _
      rw [hsource, htarget, ← hD]
      unfold physicalMixedFullResidualPhase
      dsimp only
      rw [physical_mixed_step_factor]
      have hsg : cleanMixedSourceGate s = 1 := if_pos hs
      have htg : cleanMixedTargetGate (fun _ => ∅) y = 1 :=
        if_pos ⟨ht, fun _ _ => Finset.notMem_empty _⟩
      change _ = K _ _ a * (if _ then (starRingEnd ℂ) (cleanMixedSourceGate s) * _ * _ *
        cleanMixedTargetGate (fun _ => ∅) y else 0)
      rw [hsg, htg, map_one, one_mul, mul_one]
      split_ifs <;> simp only [one_mul, zero_mul, mul_zero, mul_assoc]
    · have htg : cleanMixedTargetGate (fun _ => ∅) y = 0 :=
        if_neg (fun h => ht h.1)
      unfold physicalActiveCoefficient
      rw [dif_pos hs, dif_neg ht, mul_zero]
      unfold physicalMixedFullResidualPhase
      dsimp only
      change 0 = _ * (if _ then _ * _ * _ * cleanMixedTargetGate (fun _ => ∅) y else 0)
      rw [htg]
      split_ifs <;> simp only [mul_zero]
  · have hsg : cleanMixedSourceGate s = 0 := if_neg hs
    unfold physicalActiveCoefficient
    rw [dif_neg hs, mul_zero]
    unfold physicalMixedFullResidualPhase
    dsimp only
    rw [hsg, map_zero, zero_mul, zero_mul, zero_mul]
    split_ifs <;> simp only [mul_zero]

end Bounty

end

section

-- Original source module: PhysicalRootPrimeLocalResidual

/- The original weighted root local phase is its signed prime kernel and mixed residual. -/

open scoped Classical
namespace Bounty

theorem physical_root_prime_weighted_local_residual
    {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
    (groups : Finset (Fin N)) (reindex : {g // g ∉ groupsᶜ} ≃ Fin M)
    (V : Fin N → ℝ) (probes : Fin N → Finset (Fin J))
    (r t : Finset (Fin M)) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (patterns : Finset I)
    (iota : I → RepeatedBigPrimePatternIndex (ell := ell) probes
      (r.map (physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex))
      (t.map (physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex)))
    (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ,
      repeatedBigPrimePatternCut probes
        (r.map (physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex))
        (t.map (physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex))
        (iota i.val) g.val = ∅)
    (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ) (θ : ℝ)
    (β : (g : Fin M) → P (reindex.symm g).val → ℝ) (ρ : ℝ)
    (hPs : ∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p)
    (hPb : ∀ (g : Fin M) p, p ∈ P (reindex.symm g).val → Nat.Prime p)
    (hdis : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (reindex.symm g).val)) :
    let f := physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex
    let C := fun i => repeatedBigPrimePatternCut probes (r.map f) (t.map f) (iota i)
    let K := fun (time : ℕ) (i : I) (L R : PhysicalMarkLists P J ell)
      (aux : PhysicalAuxLabels P (C i)) =>
      if time % 2 = 0 then
        (starRingEnd ℂ) (physicalRootPrimeKernel P V probes (r.map f) (t.map f)
          ((Finset.disjoint_map f).mpr hrt) Q h ξ (iota i) R L aux)
      else physicalRootPrimeKernel P V probes (r.map f) (t.map f)
        ((Finset.disjoint_map f).mpr hrt) Q h ξ (iota i) L R aux
    ∀ (j : Fin (n + 1))
      (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups reindex)
      (ev : PhysicalRootMixedEvent groups reindex patterns C k (some (.inr j)) s),
    let cut := fun g => C ev.1.val (reindex.symm g).val
    let target := physicalMixedCoefficientTarget cut (k (n - j.val) ev.1.val) ev.2.1 s ev.2.2
    let W := physicalRootEffectiveEdgeWeight groups reindex patterns C k j s ev hPs hPb hdis V β ρ
    let time := n - j.val
    let smallPattern := (repeatedBigPrimePatternEquiv f probes r t).symm (iota ev.1.val)
    let restrictedAux : PhysicalAuxLabels (fun g => P (reindex.symm g).val)
        (repeatedBigPrimePatternCut (fun g => probes (reindex.symm g).val) r t smallPattern) :=
      fun g a => ev.2.1 g ⟨a.val, by
        change a.val ∈ repeatedBigPrimePatternCut probes (r.map f) (t.map f) (iota ev.1.val) (f g)
        rw [← repeated_big_prime_pattern_equiv_symm_cut]
        exact a.property⟩
    let source := physicalMixedRepeatedLabels cut s.2
    let targetLabels := physicalMixedRepeatedLabels cut target.2
    let kernel := fun L R =>
      repeatedBigPrimePatternWeight (fun g => probes (reindex.symm g).val) r t smallPattern *
      repeatedBigPrimePatternKernel (fun g => P (reindex.symm g).val)
        (fun g => V (reindex.symm g).val) (fun g => probes (reindex.symm g).val)
        r t hrt Q h (fun U : Finset (RepeatedBigFlatIndex (Fin M) J ell) =>
          primeProductRetainedCells (fun a : U => P (reindex.symm a.val.1).val)
            (fun a => V (reindex.symm a.val.1).val) h ξ)
        smallPattern L R restrictedAux
    let signedKernel := if time % 2 = 0 then (starRingEnd ℂ) (kernel targetLabels source)
      else kernel source targetLabels
    (W : ℂ) * physicalRootMixedLocalPhase groups reindex patterns C hC k V ζ K θ β ρ
      hPs hPb hdis (some (.inr j)) (fun _ => ∅) s ev =
      (W : ℂ) * (signedKernel *
        physicalMixedFullResidualPhase cut (ζ time ev.1.val) θ (k time ev.1.val)
          cleanMixedSourceGate (cleanMixedTargetGate (fun _ => ∅)) ev.2.1 s ev.2.2) := by
  intro f C K j s ev cut target W
    time smallPattern restrictedAux source targetLabels kernel signedKernel
  let key := physicalRootEdgeKey groups reindex patterns C k j s ev
  have hw := physical_root_mixed_weighted_empty_coefficient groups reindex patterns C hC
    k V ζ K θ β ρ hPs hPb hdis j s ev
  let kernelAll := fun (L R : RepeatedBigLists (fun g => P (reindex.symm g).val) J ell)
      (aux : PhysicalAuxLabels (fun g => P (reindex.symm g).val) cut) =>
    let aRestricted : PhysicalAuxLabels (fun g => P (reindex.symm g).val)
        (repeatedBigPrimePatternCut (fun g => probes (reindex.symm g).val) r t smallPattern) :=
      fun g a => aux g ⟨a.val, by
        change a.val ∈ repeatedBigPrimePatternCut probes (r.map f) (t.map f) (iota ev.1.val) (f g)
        rw [← repeated_big_prime_pattern_equiv_symm_cut]
        exact a.property⟩
    let value := fun L R =>
      repeatedBigPrimePatternWeight (fun g => probes (reindex.symm g).val) r t smallPattern *
      repeatedBigPrimePatternKernel (fun g => P (reindex.symm g).val)
        (fun g => V (reindex.symm g).val) (fun g => probes (reindex.symm g).val)
        r t hrt Q h (fun U : Finset (RepeatedBigFlatIndex (Fin M) J ell) =>
          primeProductRetainedCells (fun a : U => P (reindex.symm a.val.1).val)
            (fun a => V (reindex.symm a.val.1).val) h ξ)
        smallPattern L R aRestricted
    if time % 2 = 0 then (starRingEnd ℂ) (value R L) else value L R
  have hk : physicalRootKeyCoefficient groups reindex patterns C hC ζ k K θ key =
      fun L R aux => kernelAll (fun g a => L g a) (fun g a => R g a) aux *
        physicalPhase (ζ time ev.1.val)
          (physicalSharedProduct (physicalSharedPrefix s.1.2) * physicalD cut L aux) *
        physicalReturnPhase θ (k time ev.1.val *
          (physicalSharedProduct (physicalSharedPrefix s.1.2) * physicalD cut L aux : ℕ)) := by
    funext L R aux
    exact physical_root_prime_key_coefficient groups reindex V probes r t hrt Q h ξ
      patterns iota hC ζ k θ key L R aux
  dsimp only at hw
  rw [hk] at hw
  have hr := physical_mixed_active_coefficient_residual cut
    (ζ time ev.1.val) θ (k time ev.1.val) kernelAll ev.2.1 s ev.2.2
  dsimp only at hr
  rw [hr] at hw
  exact hw

end Bounty

end

section

-- Original source module: PhysicalEffectiveWeightTransport

/- Effective big-event transport preserves the exact full event weight. -/

open scoped Classical
namespace Bounty
section Effective
variable {S K V : Type} [Fintype S] {N J ell : ℕ}
  {Ps : S → Finset ℕ} {P : Fin N → Finset ℕ}
  (hPs : ∀ s p, p ∈ Ps s → Nat.Prime p)
  (hP : ∀ g p, p ∈ P g → Nat.Prime p)
  (hdis : ∀ s g, Disjoint (Ps s) (P g))
  (C : K → Fin N → Finset (Fin J)) (d : K → PhysicalSharedLists Ps J)
  (k : K → ℤ) (B : ℕ)

theorem physical_mixed_effective_big_weight
    (ω : ∀ key, SharedActiveLabels (fun g => P g)
      (fun g => physicalFullSharedIndices (ell := ell) (C key g)) →
        PhysicalAuxLabels P (C key) → ℝ)
    (μ : ∀ g, P g → ℝ) (ρ : ℝ) (Vb : Fin N → ℝ)
    (key : K) (x : PhysicalFullBoundedState P J ell B)
    (e : FullPermutationMixedEvent (fun g (p : P g) => p.val)
      (fun key g => physicalFullSharedIndices (ell := ell) (C key g)) B
      (fun key _ => PhysicalAuxLabels P (C key))
      (fun key => physicalMixedEdgeDelta (C key) (k key) (d key))
      (fun key => physicalMixedEdgeD (C key) (d key))
      (some (.inr key) : Option (V ⊕ K)) x) :
    fullActiveEdgeEventWeight (fun g (p : P g) => p.val)
      (fun g => physicalFullSharedIndices (C key g)) B
      (fun _ => PhysicalAuxLabels P (C key))
      (physicalFullEdgeDelta (C key) (k key * (physicalSharedProduct (d key) : ℕ)))
      (physicalFullEdgeD (C key)) (ω key) μ ρ Vb x
      (physicalMixedEffectiveBigEventEquiv hPs hP hdis C d k B
        (some (.inr key) : Option (V ⊕ K)) x e) =
    fullActiveEdgeEventWeight (fun g (p : P g) => p.val)
      (fun g => physicalFullSharedIndices (C key g)) B
      (fun _ => PhysicalAuxLabels P (C key))
      (physicalMixedEdgeDelta (C key) (k key) (d key))
      (physicalMixedEdgeD (C key) (d key)) (ω key) μ ρ Vb x e :=
  full_active_parameter_weight _ _ B _ _ _ _ _
    (funext fun c => funext fun a => funext fun g =>
      physical_mixed_delta_effective_big_step (C key) (d key) (k key) c a g)
    (fun c a g p =>
      physical_mixed_dilation_divisibility hPs hP hdis (C key) (d key) c a g p)
    (ω key) μ ρ Vb x e

end Effective
end Bounty

end

section

-- Original source module: DeterministicLedgerRows

/- A deterministic history phase is exactly a word of local rows on the
augmented state. The initial ledger may depend on the starting state. -/

open Finset
namespace Bounty

theorem deterministic_ledger_rows_eq_paths
    {K L X : Type*} (E : K → X → Type*) [∀ k x, Fintype (E k x)]
    (target : ∀ k x, E k x → X) (update : ∀ k, L → (x : X) → E k x → L)
    (phase : ∀ k, L → (x : X) → E k x → ℂ)
    (weight : ∀ k x, E k x → ℝ) (initial : X → L)
    (ks : List K) (F : X → ℂ) (x : X) :
    finiteOperatorListAction
      (finiteLocalPhasedRow (fun k (s : L × X) => E k s.2)
        (finiteLedgerEventTarget E target update)
        (fun k s => phase k s.1 s.2) (fun k s => weight k s.2)) ks
      (fun s => F s.2) (initial x, x) =
    finiteEventPathAction E target weight ks
      (fun y p => deterministicLedgerPhase E target update phase ks (initial y) y p) F x := by
  classical
  rw [finite_phased_rows_eq_event_paths, finite_ledger_event_path_action_memory]
  unfold finiteEventPathAction
  apply sum_congr rfl
  intro p _
  dsimp only
  rw [← deterministic_ledger_phase_eq_lifted]

end Bounty

end

section

-- Original source module: PhysicalRootMixedLedgerWord

/- The literal mixed action is a word of local rows on the original birth ledger. -/

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

noncomputable def physicalRootMixedLedgerWord
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (L : PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B) : ℂ :=
  let _ : ∀ g (z : P (e.symm g).val), NeZero z.val :=
    fun g z => inferInstanceAs (NeZero (⟨(e.symm g).val, z⟩ : PhysicalPrime P).2.val)
  let _ : ∀ tag s, Fintype (PhysicalRootMixedEvent (n := n) (B := B) (ell := ell) groups e patterns C k tag s) :=
    physicalMixedWordEventFintype (V := Fin (n + 2))
    (Ps := fun s : ↥groupsᶜ => P s.val) (J := J) (ell := ell) (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) B
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
  let weight := physicalMixedWordWeight
    (Ps := fun s : ↥groupsᶜ => P s.val) (J := J) (ell := ell) (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) B
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (i : patterns) _ aux => physicalAuxMass (fun g => V (e.symm g).val) (fun g => C i.val (e.symm g).val) aux)
    (fun g p => β g p / V (e.symm g).val) retention ρ (fun g => V (e.symm g).val)
    (fun s : ↥groupsᶜ => V s.val) (fun _ => q)
  finiteOperatorListAction
    (finiteLocalPhasedRow
      (fun tag (t : ((g : Fin M) → Finset (P (e.symm g).val)) ×
        PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e) =>
        PhysicalRootMixedEvent groups e patterns C k tag t.2)
      (finiteLedgerEventTarget (PhysicalRootMixedEvent groups e patterns C k)
        (physicalRootMixedTarget groups e patterns C k)
        (physicalRootMixedBirthUpdate (n := n) groups e patterns C k))
      (fun tag t => physicalRootMixedLocalPhase groups e patterns C hC k V ζ K θ β ρ hPs hPb hdis tag t.1 t.2)
      (fun tag t => weight tag t.2))
    ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))
    (fun t => f t.2.2)
    (fullActiveInitialLedger x, ((physicalGroupResidueVector r, L), x))

theorem physical_root_mixed_action_eq_ledger_word
    (f : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B → ℂ)
    (L : PhysicalMarkLists (fun s : ↥groupsᶜ => P s.val) J ell)
    (x : PhysicalFullBoundedState (fun g => P (e.symm g).val) J ell B) :
    physicalRootMixedAction groups e patterns C hC k V q ζ K r θ β retention ρ hPs hPb hdis f L x =
      physicalRootMixedLedgerWord groups e patterns C hC k V q ζ K r θ β retention ρ hPs hPb hdis f L x := by
  let _ : ∀ g (z : P (e.symm g).val), NeZero z.val :=
    fun g z => inferInstanceAs (NeZero (⟨(e.symm g).val, z⟩ : PhysicalPrime P).2.val)
  let _ : ∀ tag s, Fintype (PhysicalRootMixedEvent (n := n) (B := B) (ell := ell) groups e patterns C k tag s) :=
    physicalMixedWordEventFintype (V := Fin (n + 2))
    (Ps := fun s : ↥groupsᶜ => P s.val) (J := J) (ell := ell) (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) B
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
  let weight := physicalMixedWordWeight
    (Ps := fun s : ↥groupsᶜ => P s.val) (J := J) (ell := ell) (fun g (p : P (e.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (e.symm g).val)) B
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (e.symm g).val) (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD (fun g => C i.val (e.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep (fun g => C i.val (e.symm g).val) (k (n - j.val) i.val))
    (fun (i : patterns) _ aux => physicalAuxMass (fun g => V (e.symm g).val) (fun g => C i.val (e.symm g).val) aux)
    (fun g p => β g p / V (e.symm g).val) retention ρ (fun g => V (e.symm g).val)
    (fun s : ↥groupsᶜ => V s.val) (fun _ => q)
  unfold physicalRootMixedLedgerWord
  dsimp only
  erw [deterministic_ledger_rows_eq_paths
    (PhysicalRootMixedEvent (n := n) groups e patterns C k)
    (physicalRootMixedTarget groups e patterns C k)
    (physicalRootMixedBirthUpdate (n := n) groups e patterns C k)
    (physicalRootMixedLocalPhase groups e patterns C hC k V ζ K θ β ρ hPs hPb hdis)
    weight (fun s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e => fullActiveInitialLedger s.2)
    _ (fun s => f s.2) ((physicalGroupResidueVector r, L), x)]
  unfold physicalRootMixedAction physicalMixedWordPathAction
  dsimp only
  unfold finiteEventPathAction
  apply sum_congr
  · exact congrArg (fun i : Fintype _ => @Finset.univ _ i) (Subsingleton.elim _ _)
  · intro path _
    dsimp only
    erw [physical_root_mixed_phase_history]
    rfl

end Action
end Bounty

end

section

-- Original source module: PhysicalRootMixedWeightTransport

/- The original root row retains its small factor under effective big-event transport. -/

open scoped Classical
namespace Bounty

theorem physical_root_mixed_word_weight_effective
    {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
    (groups : Finset (Fin N)) (reindex : {g // g ∉ groupsᶜ} ≃ Fin M)
    (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
    (k : ℕ → I → ℤ) (V : Fin N → ℝ) (q : ℝ)
    (β : (g : Fin M) → P (reindex.symm g).val → ℝ)
    (retention : Fin (n + 2) → ℝ) (ρ : ℝ)
    (hPs : ∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p)
    (hPb : ∀ (g : Fin M) p, p ∈ P (reindex.symm g).val → Nat.Prime p)
    (hdis : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (reindex.symm g).val))
    (j : Fin (n + 1))
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups reindex)
    (ev : PhysicalRootMixedEvent groups reindex patterns C k (some (.inr j)) s) :
    let shared := fun (i : patterns) g =>
      physicalFullSharedIndices (ell := ell) (C i.val (reindex.symm g).val)
    let aux := fun (i : patterns) =>
      PhysicalAuxLabels (fun g => P (reindex.symm g).val) (fun g => C i.val (reindex.symm g).val)
    let Δ := fun (j : Fin (n + 1)) (i : patterns) =>
      physicalMixedEdgeDelta (Ps := fun g : ↥groupsᶜ => P g.val)
        (P := fun g => P (reindex.symm g).val)
        (ell := ell) (fun g => C i.val (reindex.symm g).val) (k (n-j.val) i.val)
    let D := fun (_ : Fin (n + 1)) (i : patterns) =>
      physicalMixedEdgeD (Ps := fun g : ↥groupsᶜ => P g.val)
        (P := fun g => P (reindex.symm g).val)
        (ell := ell) (fun g => C i.val (reindex.symm g).val)
    let kbig := fun (j : Fin (n + 1)) (i : patterns) =>
      physicalMixedBigStep (P := fun g => P (reindex.symm g).val) (ell := ell)
        (fun g => C i.val (reindex.symm g).val) (k (n-j.val) i.val)
    let weights := fun (i : patterns)
        (_ : SharedActiveLabels (fun g => P (reindex.symm g).val) (shared i)) a =>
      physicalAuxMass (fun g => V (reindex.symm g).val) (fun g => C i.val (reindex.symm g).val) a
    let key : PhysicalMixedBigKey (Ps := fun g : ↥groupsᶜ => P g.val)
      (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) :=
      (j, ev.1, s.1.2, ev.2.2.1)
    let cuts := fun z : PhysicalMixedBigKey (Ps := fun g : ↥groupsᶜ => P g.val)
      (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      fun g => C z.2.1.val (reindex.symm g).val
    let prefixes := fun z : PhysicalMixedBigKey (Ps := fun g : ↥groupsᶜ => P g.val)
      (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      physicalSharedPrefix z.2.2.1
    let steps := fun z : PhysicalMixedBigKey (Ps := fun g : ↥groupsᶜ => P g.val)
      (J := J) (ell := ell) (I := patterns) (K := Fin (n + 1)) =>
      k (n-z.1.val) z.2.1.val
    let effective := physicalMixedEffectiveBigEventEquiv hPs hPb hdis cuts prefixes steps B
      (some (.inr key) : Option (Fin (n + 2) ⊕ _)) s.2 ⟨ev.2.1, ev.2.2.2.2⟩
    let W := fullActiveEdgeEventWeight (fun g (p : P (reindex.symm g).val) => p.val)
      (fun g => physicalFullSharedIndices (cuts key g)) B
      (fun _ => PhysicalAuxLabels (fun g => P (reindex.symm g).val) (cuts key))
      (physicalFullEdgeDelta (cuts key) (steps key * (physicalSharedProduct (prefixes key) : ℕ)))
      (physicalFullEdgeD (cuts key)) (weights ev.1)
      (fun g p => β g p / V (reindex.symm g).val) ρ
      (fun g => V (reindex.symm g).val) s.2 effective
    physicalMixedWordWeight
      (Ps := fun g : ↥groupsᶜ => P g.val) (J := J) (ell := ell)
      (fun g (p : P (reindex.symm g).val) => p.val) shared B aux Δ D kbig
      weights (fun g p => β g p / V (reindex.symm g).val) retention ρ
      (fun g => V (reindex.symm g).val) (fun g : ↥groupsᶜ => V g.val) (fun _ => q)
      (some (.inr j)) s ev =
    physicalMixedSmallWeight (V := Fin (n + 2))
      (fun g (p : P (reindex.symm g).val) => p.val) shared B aux Δ D kbig
      (fun g : ↥groupsᶜ => V g.val) (fun _ => q) (some (.inr j)) s ev * W := by
  intro shared aux Δ D kbig weights key cuts prefixes steps effective W
  have hf := physical_mixed_word_edge_weight_factor
    (Ps := fun g : ↥groupsᶜ => P g.val) (J := J) (ell := ell)
    (fun g (p : P (reindex.symm g).val) => p.val) shared B aux Δ D kbig
    (fun g : ↥groupsᶜ => V g.val) (fun _ => q)
    weights (fun g p => β g p / V (reindex.symm g).val) retention ρ
    (fun g => V (reindex.symm g).val) j s ev
  apply hf.trans
  congr 1
  exact (physical_mixed_effective_big_weight hPs hPb hdis cuts prefixes steps B
    (fun z _ a => physicalAuxMass (fun g => V (reindex.symm g).val) (cuts z) a)
    (fun g p => β g p / V (reindex.symm g).val) ρ
    (fun g => V (reindex.symm g).val) key s.2
    (show FullPermutationMixedEvent _ _ B _ _ _
      (some (.inr key) : Option (Fin (n + 2) ⊕ _)) s.2 from
        ⟨ev.2.1, ev.2.2.2.2⟩)).symm

end Bounty

end

section

-- Original source module: PhysicalRootSummedRow

/- Exact finite row interfaces for the original root weights. -/

open Finset
open scoped Classical
namespace Bounty
section Root
variable {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
  (groups : Finset (Fin N)) (reindex : {g // g ∉ groupsᶜ} ≃ Fin M)
  (patterns : Finset I) (C : I → Fin N → Finset (Fin J)) (k : ℕ → I → ℤ)
  (V : Fin N → ℝ) (q : ℝ) (β : (g : Fin M) → P (reindex.symm g).val → ℝ)
  (retention : Fin (n + 2) → ℝ) (ρ : ℝ)

noncomputable def physicalRootOriginalWeight :=
  physicalMixedWordWeight (Ps := fun g : ↥groupsᶜ => P g.val) (ell := ell)
    (fun g (p : P (reindex.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (reindex.symm g).val)) B
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (reindex.symm g).val)
      (fun g => C i.val (reindex.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta
      (fun g => C i.val (reindex.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD
      (fun g => C i.val (reindex.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep
      (fun g => C i.val (reindex.symm g).val) (k (n - j.val) i.val))
    (fun (i : patterns) _ a => physicalAuxMass (fun g => V (reindex.symm g).val)
      (fun g => C i.val (reindex.symm g).val) a)
    (fun g p => β g p / V (reindex.symm g).val) retention ρ
    (fun g => V (reindex.symm g).val) (fun s : ↥groupsᶜ => V s.val) (fun _ => q)

noncomputable def physicalRootOriginalSmallWeight :=
  physicalMixedSmallWeight (Ps := fun g : ↥groupsᶜ => P g.val) (ell := ell) (V := Fin (n + 2))
    (fun g (p : P (reindex.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (reindex.symm g).val)) B
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (reindex.symm g).val)
      (fun g => C i.val (reindex.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta
      (fun g => C i.val (reindex.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD
      (fun g => C i.val (reindex.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep
      (fun g => C i.val (reindex.symm g).val) (k (n - j.val) i.val))
    (fun s : ↥groupsᶜ => V s.val) (fun _ => q)

variable [∀ g (p : P (reindex.symm g).val), NeZero p.val]

noncomputable def physicalRootOriginalRow
    (phase : ∀ tag s, PhysicalRootMixedEvent groups reindex patterns C k tag s → ℂ) :=
  physicalMixedWordRow
    (fun g (p : P (reindex.symm g).val) => p.val)
    (fun (i : patterns) g => physicalFullSharedIndices (ell := ell) (C i.val (reindex.symm g).val)) B
    (fun (i : patterns) => PhysicalAuxLabels (fun g => P (reindex.symm g).val)
      (fun g => C i.val (reindex.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedEdgeDelta
      (fun g => C i.val (reindex.symm g).val) (k (n - j.val) i.val))
    (fun (_ : Fin (n + 1)) (i : patterns) => physicalMixedEdgeD
      (fun g => C i.val (reindex.symm g).val))
    (fun (j : Fin (n + 1)) (i : patterns) => physicalMixedBigStep
      (fun g => C i.val (reindex.symm g).val) (k (n - j.val) i.val))
    (fun (i : patterns) _ a => physicalAuxMass (fun g => V (reindex.symm g).val)
      (fun g => C i.val (reindex.symm g).val) a)
    (fun g p => β g p / V (reindex.symm g).val) retention ρ
    (fun g => V (reindex.symm g).val) (fun s : ↥groupsᶜ => V s.val) (fun _ => q) phase

variable (hPs : ∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p)
  (hPb : ∀ (g : Fin M) p, p ∈ P (reindex.symm g).val → Nat.Prime p)
  (hdis : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (reindex.symm g).val))

omit [∀ g (p : P (reindex.symm g).val), NeZero p.val] in
theorem physical_root_original_edge_weight_factor
    (j : Fin (n + 1))
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups reindex)
    (ev : PhysicalRootMixedEvent groups reindex patterns C k (some (.inr j)) s) :
    physicalRootOriginalWeight groups reindex patterns C k V q β retention ρ
      (some (.inr j)) s ev =
    physicalRootOriginalSmallWeight groups reindex patterns C k V q (some (.inr j)) s ev *
      physicalRootEffectiveEdgeWeight groups reindex patterns C k j s ev hPs hPb hdis V β ρ :=
  physical_root_mixed_word_weight_effective groups reindex patterns C k V q β retention ρ
    hPs hPb hdis j s ev

theorem physical_root_original_edge_row_congr
    (φ ψ : ∀ tag s, PhysicalRootMixedEvent groups reindex patterns C k tag s → ℂ)
    (j : Fin (n + 1))
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups reindex)
    (hphase : ∀ ev : PhysicalRootMixedEvent groups reindex patterns C k (some (.inr j)) s,
      (physicalRootEffectiveEdgeWeight groups reindex patterns C k j s ev hPs hPb hdis V β ρ : ℂ) *
        φ (some (.inr j)) s ev =
      (physicalRootEffectiveEdgeWeight groups reindex patterns C k j s ev hPs hPb hdis V β ρ : ℂ) *
        ψ (some (.inr j)) s ev)
    (F : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups reindex → ℂ) :
    physicalRootOriginalRow groups reindex patterns C k V q β retention ρ φ (some (.inr j)) F s =
    physicalRootOriginalRow groups reindex patterns C k V q β retention ρ ψ (some (.inr j)) F s := by
  unfold physicalRootOriginalRow physicalMixedWordRow finiteLocalPhasedRow
  apply Finset.sum_congr rfl
  intro ev _
  change (physicalRootOriginalWeight groups reindex patterns C k V q β retention ρ
      (some (.inr j)) s ev : ℂ) * φ (some (.inr j)) s ev * _ =
    (physicalRootOriginalWeight groups reindex patterns C k V q β retention ρ
      (some (.inr j)) s ev : ℂ) * ψ (some (.inr j)) s ev * _
  rw [physical_root_original_edge_weight_factor groups reindex patterns C k V q β retention ρ
    hPs hPb hdis j s ev]
  simp only [Complex.ofReal_mul, mul_assoc]
  rw [← mul_assoc _ (φ (some (.inr j)) s ev), hphase ev,
    mul_assoc _ (ψ (some (.inr j)) s ev)]

end Root
end Bounty

end

section

-- Original source module: PhysicalRootPrimeRowPhase

/- The signed prime coefficient on each exact original root mixed event. -/

open scoped Classical
namespace Bounty

noncomputable def physicalRootPrimeRowPhase
    {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
    (groups : Finset (Fin N)) (reindex : {g // g ∉ groupsᶜ} ≃ Fin M)
    (V : Fin N → ℝ) (probes : Fin N → Finset (Fin J))
    (r t : Finset (Fin M)) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (patterns : Finset I)
    (iota : I → RepeatedBigPrimePatternIndex (ell := ell) probes
      (r.map (physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex))
      (t.map (physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex)))
    (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ) (θ : ℝ) :
    let f := physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex
    let C := fun i => repeatedBigPrimePatternCut probes (r.map f) (t.map f) (iota i)
    ∀ tag s, PhysicalRootMixedEvent (P := P) (ell := ell) (n := n) (B := B)
      groups reindex patterns C k tag s → ℂ := by
  intro f C tag s ev
  cases tag with
  | none => exact 1
  | some tag =>
    cases tag with
    | inl v => exact 1
    | inr j =>
      exact
        let cut := fun g => C ev.1.val (reindex.symm g).val
        let target := physicalMixedCoefficientTarget cut (k (n - j.val) ev.1.val) ev.2.1 s ev.2.2
        let time := n - j.val
        let smallPattern := (repeatedBigPrimePatternEquiv f probes r t).symm (iota ev.1.val)
        let restrictedAux : PhysicalAuxLabels (fun g => P (reindex.symm g).val)
            (repeatedBigPrimePatternCut (fun g => probes (reindex.symm g).val) r t smallPattern) :=
          fun g a => ev.2.1 g ⟨a.val, by
            change a.val ∈ repeatedBigPrimePatternCut probes (r.map f) (t.map f) (iota ev.1.val) (f g)
            rw [← repeated_big_prime_pattern_equiv_symm_cut]
            exact a.property⟩
        let source := physicalMixedRepeatedLabels cut s.2
        let targetLabels := physicalMixedRepeatedLabels cut target.2
        let kernel := fun L R =>
          repeatedBigPrimePatternWeight (fun g => probes (reindex.symm g).val) r t smallPattern *
          repeatedBigPrimePatternKernel (fun g => P (reindex.symm g).val)
            (fun g => V (reindex.symm g).val) (fun g => probes (reindex.symm g).val)
            r t hrt Q h (fun U : Finset (RepeatedBigFlatIndex (Fin M) J ell) =>
              primeProductRetainedCells (fun a : U => P (reindex.symm a.val.1).val)
                (fun a => V (reindex.symm a.val.1).val) h ξ)
            smallPattern L R restrictedAux
        let signedKernel := if time % 2 = 0 then (starRingEnd ℂ) (kernel targetLabels source)
          else kernel source targetLabels
        signedKernel * physicalMixedFullResidualPhase cut (ζ time ev.1.val) θ (k time ev.1.val)
          cleanMixedSourceGate (cleanMixedTargetGate (fun _ => ∅)) ev.2.1 s ev.2.2

theorem physical_root_prime_row_phase_weighted
    {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
    (groups : Finset (Fin N)) (reindex : {g // g ∉ groupsᶜ} ≃ Fin M)
    (V : Fin N → ℝ) (probes : Fin N → Finset (Fin J))
    (r t : Finset (Fin M)) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (patterns : Finset I)
    (iota : I → RepeatedBigPrimePatternIndex (ell := ell) probes
      (r.map (physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex))
      (t.map (physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex)))
    (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ,
      repeatedBigPrimePatternCut probes
        (r.map (physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex))
        (t.map (physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex))
        (iota i.val) g.val = ∅)
    (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ) (θ : ℝ)
    (β : (g : Fin M) → P (reindex.symm g).val → ℝ) (ρ : ℝ)
    (hPs : ∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p)
    (hPb : ∀ (g : Fin M) p, p ∈ P (reindex.symm g).val → Nat.Prime p)
    (hdis : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (reindex.symm g).val)) :
    let f := physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex
    let C := fun i => repeatedBigPrimePatternCut probes (r.map f) (t.map f) (iota i)
    let K := fun (time : ℕ) (i : I) (L R : PhysicalMarkLists P J ell)
      (aux : PhysicalAuxLabels P (C i)) =>
      if time % 2 = 0 then
        (starRingEnd ℂ) (physicalRootPrimeKernel P V probes (r.map f) (t.map f)
          ((Finset.disjoint_map f).mpr hrt) Q h ξ (iota i) R L aux)
      else physicalRootPrimeKernel P V probes (r.map f) (t.map f)
        ((Finset.disjoint_map f).mpr hrt) Q h ξ (iota i) L R aux
    ∀ (j : Fin (n + 1))
      (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups reindex)
      (ev : PhysicalRootMixedEvent groups reindex patterns C k (some (.inr j)) s),
    let W := physicalRootEffectiveEdgeWeight groups reindex patterns C k j s ev hPs hPb hdis V β ρ
    (W : ℂ) * physicalRootMixedLocalPhase groups reindex patterns C hC k V ζ K θ β ρ
      hPs hPb hdis (some (.inr j)) (fun _ => ∅) s ev =
    (W : ℂ) * physicalRootPrimeRowPhase groups reindex V probes r t hrt Q h ξ patterns iota
      ζ k θ (some (.inr j)) s ev := by
  intro f C K j s ev W
  exact physical_root_prime_weighted_local_residual groups reindex V probes r t hrt Q h ξ
    patterns iota hC ζ k θ β ρ hPs hPb hdis j s ev

theorem physical_root_prime_edge_row_phase
    {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
    (groups : Finset (Fin N)) (reindex : {g // g ∉ groupsᶜ} ≃ Fin M)
    (V : Fin N → ℝ) (probes : Fin N → Finset (Fin J))
    (r t : Finset (Fin M)) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (patterns : Finset I)
    (iota : I → RepeatedBigPrimePatternIndex (ell := ell) probes
      (r.map (physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex))
      (t.map (physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex)))
    (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ,
      repeatedBigPrimePatternCut probes
        (r.map (physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex))
        (t.map (physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex))
        (iota i.val) g.val = ∅)
    (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ) (θ : ℝ)
    (β : (g : Fin M) → P (reindex.symm g).val → ℝ) (ρ : ℝ)
    (hPs : ∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p)
    (hPb : ∀ (g : Fin M) p, p ∈ P (reindex.symm g).val → Nat.Prime p)
    (hdis : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (reindex.symm g).val))
    [∀ g (p : P (reindex.symm g).val), NeZero p.val]
    (q : ℝ) (retention : Fin (n + 2) → ℝ) :
    let f := physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex
    let C := fun i => repeatedBigPrimePatternCut probes (r.map f) (t.map f) (iota i)
    let K := fun (time : ℕ) (i : I) (L R : PhysicalMarkLists P J ell)
      (aux : PhysicalAuxLabels P (C i)) =>
      if time % 2 = 0 then
        (starRingEnd ℂ) (physicalRootPrimeKernel P V probes (r.map f) (t.map f)
          ((Finset.disjoint_map f).mpr hrt) Q h ξ (iota i) R L aux)
      else physicalRootPrimeKernel P V probes (r.map f) (t.map f)
        ((Finset.disjoint_map f).mpr hrt) Q h ξ (iota i) L R aux
    ∀ (decoration : ∀ tag s, PhysicalRootMixedEvent groups reindex patterns C k tag s → ℂ)
      (j : Fin (n + 1))
      (F : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups reindex → ℂ)
      (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups reindex),
    physicalRootOriginalRow groups reindex patterns C k V q β retention ρ
      (fun tag y ev => physicalRootMixedLocalPhase groups reindex patterns C hC k V ζ K θ β ρ
        hPs hPb hdis tag (fun _ => ∅) y ev * decoration tag y ev) (some (.inr j)) F s =
    physicalRootOriginalRow groups reindex patterns C k V q β retention ρ
      (fun tag y ev => physicalRootPrimeRowPhase groups reindex V probes r t hrt Q h ξ
        patterns iota ζ k θ tag y ev * decoration tag y ev) (some (.inr j)) F s := by
  intro f C K decoration j F s
  apply physical_root_original_edge_row_congr groups reindex patterns C k V q β retention ρ
    hPs hPb hdis
  intro ev
  rw [← mul_assoc, ← mul_assoc]
  exact congrArg (fun z => z * decoration (some (.inr j)) s ev)
    (physical_root_prime_row_phase_weighted groups reindex V probes r t hrt Q h ξ
      patterns iota hC ζ k θ β ρ hPs hPb hdis j s ev)

end Bounty

end

section

-- Original source module: PhysicalRootActionSum

/- The original root edge row is exactly the finite sum of the mixed
coefficient actions, with the same auxiliary weights and local phase. -/

open Finset
open scoped Classical

namespace Bounty

theorem physical_root_original_edge_row_eq_actions
    {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
    (groups : Finset (Fin N)) (reindex : {g // g ∉ groupsᶜ} ≃ Fin M)
    (patterns : Finset I) (C : I → Fin N → Finset (Fin J)) (k : ℕ → I → ℤ)
    (V : Fin N → ℝ) (q : ℝ) (β : (g : Fin M) → P (reindex.symm g).val → ℝ)
    (retention : Fin (n + 2) → ℝ) (ρ : ℝ)
    [∀ g (p : P (reindex.symm g).val), NeZero p.val]
    (φ : ∀ tag s, PhysicalRootMixedEvent (P := P) (ell := ell) (n := n) (B := B)
      groups reindex patterns C k tag s → ℂ)
    (baseline : (g : Fin M) → P (reindex.symm g).val → ℝ)
    (hμ : ∀ g p, β g p / V (reindex.symm g).val =
      tiltedPhysicalBirthLaw (P := fun g => P (reindex.symm g).val)
        (fun g => V (reindex.symm g).val) g (baseline g) p)
    (j : Fin (n + 1))
    (F : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B)
      groups reindex → ℂ)
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B)
      groups reindex) :
    physicalRootOriginalRow groups reindex patterns C k V q β retention ρ φ
      (some (.inr j)) F s =
    ∑ i : patterns,
      physicalMixedCoefficientAction (fun g => C i.val (reindex.symm g).val)
        (k (n-j.val) i.val) (fun g => V (reindex.symm g).val) baseline ρ
        (fun a : ↥groupsᶜ => V a.val) q (fun _ => ∅)
        (fun a y ev => φ (some (.inr j)) y ⟨i,a,ev⟩) F s := by
  unfold physicalRootOriginalRow
  rw [physical_mixed_word_row_edge]
  have hμfun : (fun g p => β g p / V (reindex.symm g).val) =
      (fun g => tiltedPhysicalBirthLaw (P := fun g => P (reindex.symm g).val)
        (fun g => V (reindex.symm g).val) g
        (baseline g)) := by
    funext g p
    exact hμ g p
  rw [hμfun]
  simp only [physicalMixedCoefficientAction, Finset.notMem_empty, not_false_eq_true,
    forall_true_iff, if_true]

end Bounty

end

section

-- Original source module: PhysicalRootTiltedLaw

/- The reciprocal residue coefficient in the original root normalization
induces exactly the tilted physical birth law. -/

namespace Bounty

theorem physical_root_tilted_birth_law {G : Type*} {P : G → Finset ℕ}
    (V : G → ℝ) (baseline : ∀ g, P g → ℝ) :
    ∀ g (p : P g), ((p.val : ℝ)*baseline g p)⁻¹ / V g =
      tiltedPhysicalBirthLaw V g (baseline g) p := by
  intro g p
  unfold tiltedPhysicalBirthLaw physicalLabelLaw
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

end Bounty

end

section

-- Original source module: PhysicalRootPrimeActionSum

/- The actual reciprocal residue coefficient identifies the original prime
root row with the sum of mixed coefficient actions, retaining every decoration. -/

open Finset
open scoped Classical
namespace Bounty

theorem physical_root_prime_edge_row_eq_actions
    {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
    (groups : Finset (Fin N)) (reindex : {g // g ∉ groupsᶜ} ≃ Fin M)
    (V : Fin N → ℝ) (probes : Fin N → Finset (Fin J))
    (r t : Finset (Fin M)) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (patterns : Finset I)
    (iota : I → RepeatedBigPrimePatternIndex (ell := ell) probes
      (r.map (physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex))
      (t.map (physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex)))
    (hC : ∀ i : patterns, ∀ g : ↥groupsᶜ,
      repeatedBigPrimePatternCut probes
        (r.map (physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex))
        (t.map (physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex))
        (iota i.val) g.val = ∅)
    (ζ : ℕ → I → ℝ) (k : ℕ → I → ℤ) (θ : ℝ)
    (baseline : (g : Fin M) → P (reindex.symm g).val → ℝ) (ρ : ℝ)
    (hPs : ∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p)
    (hPb : ∀ (g : Fin M) p, p ∈ P (reindex.symm g).val → Nat.Prime p)
    (hdis : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (reindex.symm g).val))
    [∀ g (p : P (reindex.symm g).val), NeZero p.val]
    (q : ℝ) (retention : Fin (n + 2) → ℝ) :
    let β := fun (g : Fin M) (p : P (reindex.symm g).val) =>
      ((p.val : ℝ)*baseline g p)⁻¹
    let f := physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex
    let C := fun i => repeatedBigPrimePatternCut probes (r.map f) (t.map f) (iota i)
    let K := fun (time : ℕ) (i : I) (L R : PhysicalMarkLists P J ell)
      (aux : PhysicalAuxLabels P (C i)) =>
      if time % 2 = 0 then
        (starRingEnd ℂ) (physicalRootPrimeKernel P V probes (r.map f) (t.map f)
          ((Finset.disjoint_map f).mpr hrt) Q h ξ (iota i) R L aux)
      else physicalRootPrimeKernel P V probes (r.map f) (t.map f)
        ((Finset.disjoint_map f).mpr hrt) Q h ξ (iota i) L R aux
    ∀ (decoration : ∀ tag s, PhysicalRootMixedEvent groups reindex patterns C k tag s → ℂ)
      (j : Fin (n + 1))
      (F : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups reindex → ℂ)
      (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups reindex),
    physicalRootOriginalRow groups reindex patterns C k V q β retention ρ
      (fun tag y ev => physicalRootMixedLocalPhase groups reindex patterns C hC k V ζ K θ β ρ
        hPs hPb hdis tag (fun _ => ∅) y ev * decoration tag y ev) (some (.inr j)) F s =
    ∑ i : patterns,
      physicalMixedCoefficientAction (fun g => C i.val (reindex.symm g).val)
        (k (n-j.val) i.val) (fun g => V (reindex.symm g).val) baseline ρ
        (fun a : ↥groupsᶜ => V a.val) q (fun _ => ∅)
        (fun a y ev => physicalRootPrimeRowPhase groups reindex V probes r t hrt Q h ξ
          patterns iota ζ k θ (some (.inr j)) y ⟨i,a,ev⟩ *
          decoration (some (.inr j)) y ⟨i,a,ev⟩) F s := by
  intro β f C K decoration j F s
  exact (physical_root_prime_edge_row_phase groups reindex V probes r t hrt Q h ξ
    patterns iota hC ζ k θ β ρ hPs hPb hdis q retention decoration j F s).trans
      (physical_root_original_edge_row_eq_actions groups reindex patterns C k V q β retention ρ
        (fun tag y ev => physicalRootPrimeRowPhase groups reindex V probes r t hrt Q h ξ
          patterns iota ζ k θ tag y ev * decoration tag y ev)
        baseline (physical_root_tilted_birth_law (P := fun g => P (reindex.symm g).val)
          (fun g => V (reindex.symm g).val) baseline) j F s)

end Bounty

end

section

-- Original source module: PhysicalRootPatternEnumeration

/- The full original prime pattern family is exactly the native big-group
family. Small groups have empty cuts throughout that family. -/

open Finset
open scoped Classical
namespace Bounty

noncomputable def physicalRootPrimeFullPatternEquiv
    {N M J ell : ℕ} (groups : Finset (Fin N))
    (reindex : {g // g ∉ groupsᶜ} ≃ Fin M)
    (probes : Fin N → Finset (Fin J)) (r t : Finset (Fin M)) :
    let f := physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex
    RepeatedBigPrimePatternIndex (ell := ell) (fun g => probes (reindex.symm g).val) r t ≃
      ↥(univ : Finset (RepeatedBigPrimePatternIndex (ell := ell) probes (r.map f) (t.map f))) := by
  intro f
  let e := repeatedBigPrimePatternEquiv (ell := ell) f probes r t
  exact
    { toFun := fun i => ⟨e i, mem_univ _⟩
      invFun := fun i => e.symm i.val
      left_inv := fun i => e.symm_apply_apply i
      right_inv := fun i => Subtype.ext (e.apply_symm_apply i.val) }

theorem physical_root_prime_full_pattern_cut
    {N M J ell : ℕ} (groups : Finset (Fin N))
    (reindex : {g // g ∉ groupsᶜ} ≃ Fin M)
    (probes : Fin N → Finset (Fin J)) (r t : Finset (Fin M))
    (i : RepeatedBigPrimePatternIndex (ell := ell) (fun g => probes (reindex.symm g).val) r t) :
    let f := physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex
    (fun g => repeatedBigPrimePatternCut probes (r.map f) (t.map f)
      (physicalRootPrimeFullPatternEquiv groups reindex probes r t i).val (reindex.symm g).val) =
      repeatedBigPrimePatternCut (fun g => probes (reindex.symm g).val) r t i := by
  intro f
  funext g
  exact repeated_big_prime_pattern_map_cut f probes r t i g

theorem physical_root_prime_full_pattern_small_cut
    {N M J ell : ℕ} (groups : Finset (Fin N))
    (reindex : {g // g ∉ groupsᶜ} ≃ Fin M)
    (probes : Fin N → Finset (Fin J)) (r t : Finset (Fin M)) :
    let f := physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex
    ∀ (i : RepeatedBigPrimePatternIndex (ell := ell) probes (r.map f) (t.map f))
      (g : ↥groupsᶜ), repeatedBigPrimePatternCut probes (r.map f) (t.map f) i g.val = ∅ := by
  intro f i g
  have hg : g.val ∉ Set.range f := by
    rintro ⟨j, hj⟩
    apply (reindex.symm j).property
    change f j ∈ groupsᶜ
    rw [hj]
    exact g.property
  have h := repeated_big_prime_pattern_map_cut_outside f probes r t
    ((repeatedBigPrimePatternEquiv f probes r t).symm i) g.val hg
  rw [← repeated_big_prime_pattern_equiv_apply, Equiv.apply_symm_apply] at h
  exact h

end Bounty

end

section

-- Original source module: PhysicalRootNativePrimePhase

/- The exact full root prime phase, expressed in the native pattern family.
The original event decoration is transported, without any matching premise. -/

open Finset
open scoped Classical

namespace Bounty

private theorem aux_index_value_congr
    {I G : Type} {P : G → Finset ℕ} {J : ℕ}
    (cuts : I → G → Finset (Fin J))
    (F : ∀ i, PhysicalAuxLabels P (cuts i) → ℂ)
    {i j : I} (hij : i = j)
    (a : PhysicalAuxLabels P (cuts i)) (b : PhysicalAuxLabels P (cuts j))
    (hab : ∀ g (x : cuts i g), a g x = b g ⟨x.val, by rw [← hij]; exact x.property⟩) :
    F i a = F j b := by
  subst j
  apply congrArg (F i)
  funext g x
  exact hab g x

theorem physical_root_native_prime_phase
    {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
    (groups : Finset (Fin N)) (reindex : {g // g ∉ groupsᶜ} ≃ Fin M)
    (V : Fin N → ℝ) (probes : Fin N → Finset (Fin J))
    (r t : Finset (Fin M)) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (ζ : ℕ → ℝ) (k : ℕ → ℤ) (θ : ℝ) (j : Fin (n + 1))
    (i : RepeatedBigPrimePatternIndex (ell := ell)
      (fun g => probes (reindex.symm g).val) r t) :
    let emb := physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex
    let index := physicalRootPrimeFullPatternEquiv (ell := ell) groups reindex probes r t
    let oldCut := fun g => repeatedBigPrimePatternCut probes (r.map emb) (t.map emb)
      (index i).val (reindex.symm g).val
    let nativeCut := repeatedBigPrimePatternCut (fun g => probes (reindex.symm g).val) r t i
    let hcut : oldCut = nativeCut := physical_root_prime_full_pattern_cut groups reindex probes r t i
    let kernel := fun L R (a : PhysicalAuxLabels (fun g => P (reindex.symm g).val) nativeCut) =>
      let value := fun L R =>
        repeatedBigPrimePatternWeight (fun g => probes (reindex.symm g).val) r t i *
        repeatedBigPrimePatternKernel (fun g => P (reindex.symm g).val)
          (fun g => V (reindex.symm g).val) (fun g => probes (reindex.symm g).val)
          r t hrt Q h (fun U : Finset (RepeatedBigFlatIndex (Fin M) J ell) =>
            primeProductRetainedCells (fun z : U => P (reindex.symm z.val.1).val)
              (fun z => V (reindex.symm z.val.1).val) h ξ) i L R a
      if (n - j.val) % 2 = 0 then (starRingEnd ℂ) (value R L) else value L R
    ∀ (decoration : ∀ a
      (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups reindex),
      PhysicalMixedCoefficientEvent oldCut (k (n - j.val)) a s → ℂ),
    physicalMixedPhaseCutTransport hcut (k (n - j.val))
      (fun a s e => physicalRootPrimeRowPhase (P := P) (ell := ell) (n := n) (B := B)
        groups reindex V probes r t hrt Q h ξ univ id
        (fun time _ => ζ time) (fun time _ => k time) θ (some (.inr j)) s ⟨index i, a, e⟩ *
        decoration a s e) =
    fun a s e =>
      kernel (physicalMixedRepeatedLabels nativeCut s.2)
        (physicalMixedRepeatedLabels nativeCut
          (physicalMixedCoefficientTarget nativeCut (k (n - j.val)) a s e).2) a *
      physicalMixedFullResidualPhase nativeCut (ζ (n - j.val)) θ (k (n - j.val))
        cleanMixedSourceGate (cleanMixedTargetGate (fun _ => ∅)) a s e *
      physicalMixedPhaseCutTransport hcut (k (n - j.val)) decoration a s e := by
  intro emb index oldCut nativeCut hcut kernel decoration
  let base := fun (p : RepeatedBigPrimePatternIndex (ell := ell)
      (fun g => probes (reindex.symm g).val) r t) L R
      (a : PhysicalAuxLabels (fun g => P (reindex.symm g).val)
        (repeatedBigPrimePatternCut (fun g => probes (reindex.symm g).val) r t p)) =>
    repeatedBigPrimePatternWeight (fun g => probes (reindex.symm g).val) r t p *
    repeatedBigPrimePatternKernel (fun g => P (reindex.symm g).val)
      (fun g => V (reindex.symm g).val) (fun g => probes (reindex.symm g).val)
      r t hrt Q h (fun U : Finset (RepeatedBigFlatIndex (Fin M) J ell) =>
        primeProductRetainedCells (fun z : U => P (reindex.symm z.val.1).val)
          (fun z => V (reindex.symm z.val.1).val) h ξ) p L R a
  have hphase :
      (fun a s e => physicalRootPrimeRowPhase (P := P) (ell := ell) (n := n) (B := B)
        groups reindex V probes r t hrt Q h ξ univ id
        (fun time _ => ζ time) (fun time _ => k time) θ (some (.inr j)) s ⟨index i, a, e⟩ *
        decoration a s e) =
      (fun a s e => kernel (physicalMixedRepeatedLabels oldCut s.2)
        (physicalMixedRepeatedLabels oldCut
          (physicalMixedCoefficientTarget oldCut (k (n - j.val)) a s e).2)
        (physicalAuxCutTransport hcut a) *
        physicalMixedFullResidualPhase oldCut (ζ (n - j.val)) θ (k (n - j.val))
          cleanMixedSourceGate (cleanMixedTargetGate (fun _ => ∅)) a s e * decoration a s e) := by
    funext a s e
    let p := (repeatedBigPrimePatternEquiv emb probes r t).symm (index i).val
    have hp : p = i := (repeatedBigPrimePatternEquiv emb probes r t).symm_apply_apply i
    let a' : PhysicalAuxLabels (fun g => P (reindex.symm g).val)
        (repeatedBigPrimePatternCut (fun g => probes (reindex.symm g).val) r t p) :=
      fun g x => a g ⟨x.val, by
        change x.val ∈ repeatedBigPrimePatternCut probes (r.map emb) (t.map emb) (index i).val (emb g)
        rw [← repeated_big_prime_pattern_equiv_symm_cut]
        exact x.property⟩
    have hb (L R : RepeatedBigLists (fun g => P (reindex.symm g).val) J ell) :
        base p L R a' = base i L R (physicalAuxCutTransport hcut a) := by
      apply aux_index_value_congr
        (repeatedBigPrimePatternCut (fun g => probes (reindex.symm g).val) r t)
        (fun p a => base p L R a) hp a' (physicalAuxCutTransport hcut a)
      intro g x
      rw [physical_aux_cut_transport_apply]
    let L := physicalMixedRepeatedLabels oldCut s.2
    let R := physicalMixedRepeatedLabels oldCut
      (physicalMixedCoefficientTarget oldCut (k (n - j.val)) a s e).2
    have hsigned :
        (if (n - j.val) % 2 = 0 then (starRingEnd ℂ) (base p R L a') else base p L R a') =
        kernel L R (physicalAuxCutTransport hcut a) := by
      dsimp only [kernel]
      split_ifs
      · exact congrArg (starRingEnd ℂ) (hb R L)
      · exact hb L R
    exact congrArg (fun z => z *
      physicalMixedFullResidualPhase oldCut (ζ (n - j.val)) θ (k (n - j.val))
        cleanMixedSourceGate (cleanMixedTargetGate (fun _ => ∅)) a s e * decoration a s e) hsigned
  exact (congrArg (physicalMixedPhaseCutTransport hcut (k (n - j.val))) hphase).trans
    (physical_mixed_phase_cut_transport_kernel_residual hcut kernel (ζ (n - j.val)) θ
      (k (n - j.val)) cleanMixedSourceGate (cleanMixedTargetGate (fun _ => ∅)) decoration)

end Bounty

end

section

-- Original source module: PhysicalRootSignedPrimeAction

/- The full original prime-pattern edge row is the native signed prime-family
action, with its exact original event decoration and reciprocal birth law. -/

open Finset
open scoped Classical
namespace Bounty

theorem physical_root_full_prime_edge_eq_signed_action
    {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
    (groups : Finset (Fin N)) (reindex : {g // g ∉ groupsᶜ} ≃ Fin M)
    (V : Fin N → ℝ) (probes : Fin N → Finset (Fin J))
    (r t : Finset (Fin M)) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (ζ : ℕ → ℝ) (k : ℕ → ℤ) (θ : ℝ)
    (baseline : (g : Fin M) → P (reindex.symm g).val → ℝ) (ρ : ℝ)
    (hPs : ∀ (a : ↥groupsᶜ) p, p ∈ P a.val → Nat.Prime p)
    (hPb : ∀ (g : Fin M) p, p ∈ P (reindex.symm g).val → Nat.Prime p)
    (hdis : ∀ (a : ↥groupsᶜ) (g : Fin M), Disjoint (P a.val) (P (reindex.symm g).val))
    [∀ g (p : P (reindex.symm g).val), NeZero p.val]
    (q : ℝ) (retention : Fin (n + 2) → ℝ) :
    let f := physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex
    let patterns := (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell)
      probes (r.map f) (t.map f)))
    let C := repeatedBigPrimePatternCut (ell := ell) probes (r.map f) (t.map f)
    let ζroot := fun time (_ : RepeatedBigPrimePatternIndex (ell := ell)
      probes (r.map f) (t.map f)) => ζ time
    let kroot := fun time (_ : RepeatedBigPrimePatternIndex (ell := ell)
      probes (r.map f) (t.map f)) => k time
    let β := fun (g : Fin M) (p : P (reindex.symm g).val) =>
      ((p.val : ℝ)*baseline g p)⁻¹
    let hC : ∀ i : patterns, ∀ a : ↥groupsᶜ, C i.val a.val = ∅ :=
      fun i a => physical_root_prime_full_pattern_small_cut groups reindex probes r t i.val a
    let K := fun (time : ℕ)
      (i : RepeatedBigPrimePatternIndex (ell := ell) probes (r.map f) (t.map f))
      (L R : PhysicalMarkLists P J ell) (aux : PhysicalAuxLabels P (C i)) =>
      if time % 2 = 0 then
        (starRingEnd ℂ) (physicalRootPrimeKernel P V probes (r.map f) (t.map f)
          ((Finset.disjoint_map f).mpr hrt) Q h ξ i R L aux)
      else physicalRootPrimeKernel P V probes (r.map f) (t.map f)
        ((Finset.disjoint_map f).mpr hrt) Q h ξ i L R aux
    ∀ (decoration : ∀ tag s, PhysicalRootMixedEvent (P := P) (ell := ell) (n := n) (B := B)
      groups reindex patterns C kroot tag s → ℂ)
      (j : Fin (n + 1))
      (F : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups reindex → ℂ)
      (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups reindex),
    physicalRootOriginalRow groups reindex patterns C kroot V q β retention ρ
      (fun tag y ev => physicalRootMixedLocalPhase groups reindex patterns C hC kroot V
        ζroot K θ β ρ hPs hPb hdis tag (fun _ => ∅) y ev * decoration tag y ev)
      (some (.inr j)) F s =
    physicalMixedSignedPrimePatternAction (fun g => V (reindex.symm g).val) baseline ρ
      (fun a : ↥groupsᶜ => V a.val) q (fun g => probes (reindex.symm g).val)
      r t hrt Q h ξ (n-j.val) (k (n-j.val)) (fun _ => ∅)
      (fun i a y ev =>
        physicalMixedFullResidualPhase
          (repeatedBigPrimePatternCut (fun g => probes (reindex.symm g).val) r t i)
          (ζ (n-j.val)) θ (k (n-j.val)) cleanMixedSourceGate
          (cleanMixedTargetGate (fun _ => ∅)) a y ev *
        physicalMixedPhaseCutTransport
          (physical_root_prime_full_pattern_cut groups reindex probes r t i) (k (n-j.val))
          (fun a y ev => decoration (some (.inr j)) y
            ⟨physicalRootPrimeFullPatternEquiv groups reindex probes r t i,a,ev⟩) a y ev) F s := by
  intro f patterns C ζroot kroot β hC K decoration j F s
  erw [physical_root_prime_edge_row_eq_actions groups reindex V probes r t hrt Q h ξ
    patterns id hC ζroot kroot θ baseline ρ hPs hPb hdis q retention decoration j F s]
  erw [physical_mixed_coefficient_sum_reindex_cut
    (physicalRootPrimeFullPatternEquiv groups reindex probes r t)
    (fun i : patterns => fun g => C i.val (reindex.symm g).val)
    (repeatedBigPrimePatternCut (fun g => probes (reindex.symm g).val) r t)
    (fun i => physical_root_prime_full_pattern_cut groups reindex probes r t i)
    (fun _ => k (n-j.val)) (fun g => V (reindex.symm g).val) baseline ρ
    (fun a : ↥groupsᶜ => V a.val) q (fun _ => ∅)
    (fun i a y ev => physicalRootPrimeRowPhase groups reindex V probes r t hrt Q h ξ
      patterns id ζroot kroot θ (some (.inr j)) y ⟨i,a,ev⟩ *
      decoration (some (.inr j)) y ⟨i,a,ev⟩) F s]
  unfold physicalMixedSignedPrimePatternAction
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun phase => physicalMixedCoefficientAction
    (repeatedBigPrimePatternCut (fun g => probes (reindex.symm g).val) r t i)
    (k (n-j.val)) (fun g => V (reindex.symm g).val) baseline ρ
    (fun a : ↥groupsᶜ => V a.val) q (fun _ => ∅) phase F s)
  have hphase := physical_root_native_prime_phase groups reindex V probes r t hrt Q h ξ
    ζ k θ j i (fun a y ev => decoration (some (.inr j)) y
      ⟨physicalRootPrimeFullPatternEquiv groups reindex probes r t i,a,ev⟩)
  funext a y ev
  simpa only [mul_assoc] using congrFun (congrFun (congrFun hphase a) y) ev

end Bounty

end
end

section

/- Root Fourier bridge bodies on the coherent actual-Z dependency boundary. -/

section

-- Original source module: PhysicalRootFourierProjection

/- The exact original Fourier edge before its outer and inner projections. -/

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

theorem physical_root_fourier_edge_eq_original_row
    (j : Fin (n + 1))
    (f : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e → ℂ) :
    physicalRootFourierRow groups e patterns C hC k V q ζ K θ β retention ρ hPs hPb hdis
      code encode ν (some (.inr j)) f =
    physicalRootOriginalRow groups e patterns C k V q β retention ρ
      (fun tag s ev =>
        physicalRootMixedLocalPhase groups e patterns C hC k V ζ K θ β ρ hPs hPb hdis
          tag (fun _ => ∅) s ev *
        physicalRootMixedFourierMultiplier groups e patterns C k code encode ν hPs hPb hdis
          tag s ev) (some (.inr j)) f := by
  funext s
  unfold physicalRootFourierRow physicalRootOriginalRow physicalMixedWordRow finiteLocalPhasedRow
  apply Finset.sum_congr rfl
  intro ev _
  rw [physical_root_fourier_edge_factor groups e patterns C hC k V ζ K θ β ρ
    code encode ν hPs hPb hdis j s ev]

end Root
end Bounty

end

section

-- Original source module: PhysicalRootProjectedPrimeEdge

/- The original projected Fourier prime edge equals the native signed family,
with the exact pulled-back Fourier multiplier and both joint averages retained. -/

open Finset
open scoped Classical
namespace Bounty

theorem physical_root_projected_prime_edge_eq_signed_action
    {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
    [∀ z : PhysicalPrime P, NeZero z.2.val]
    (groups : Finset (Fin N)) (reindex : {g // g ∉ groupsᶜ} ≃ Fin M)
    (V : Fin N → ℝ) (probes : Fin N → Finset (Fin J))
    (r t : Finset (Fin M)) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (ζ : ℕ → ℝ) (k : ℕ → ℤ) (θ : ℝ)
    (baseline : (g : Fin M) → P (reindex.symm g).val → ℝ) (ρ : ℝ)
    (hPs : ∀ (a : ↥groupsᶜ) p, p ∈ P a.val → Nat.Prime p)
    (hPb : ∀ (g : Fin M) p, p ∈ P (reindex.symm g).val → Nat.Prime p)
    (hdis : ∀ (a : ↥groupsᶜ) (g : Fin M), Disjoint (P a.val) (P (reindex.symm g).val))
    [∀ g (p : P (reindex.symm g).val), NeZero p.val]
    (q : ℝ) (retention : Fin (n + 2) → ℝ)
    (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (reindex.symm g).val) → ℤ)
    (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) → ℝ) :
    let f := physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex
    let patterns := (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell)
      probes (r.map f) (t.map f)))
    let C := repeatedBigPrimePatternCut (ell := ell) probes (r.map f) (t.map f)
    let ζroot := fun time (_ : RepeatedBigPrimePatternIndex (ell := ell)
      probes (r.map f) (t.map f)) => ζ time
    let kroot := fun time (_ : RepeatedBigPrimePatternIndex (ell := ell)
      probes (r.map f) (t.map f)) => k time
    let β := fun (g : Fin M) (p : P (reindex.symm g).val) =>
      ((p.val : ℝ)*baseline g p)⁻¹
    let hC : ∀ i : patterns, ∀ a : ↥groupsᶜ, C i.val a.val = ∅ :=
      fun i a => physical_root_prime_full_pattern_small_cut groups reindex probes r t i.val a
    let K := fun (time : ℕ)
      (i : RepeatedBigPrimePatternIndex (ell := ell) probes (r.map f) (t.map f))
      (L R : PhysicalMarkLists P J ell) (aux : PhysicalAuxLabels P (C i)) =>
      if time % 2 = 0 then
        (starRingEnd ℂ) (physicalRootPrimeKernel P V probes (r.map f) (t.map f)
          ((Finset.disjoint_map f).mpr hrt) Q h ξ i R L aux)
      else physicalRootPrimeKernel P V probes (r.map f) (t.map f)
        ((Finset.disjoint_map f).mpr hrt) Q h ξ i L R aux
    let decoration := physicalRootMixedFourierMultiplier groups reindex patterns C kroot
      code encode ν hPs hPb hdis
    let row := physicalRootFourierRow groups reindex patterns C hC kroot V q ζroot K θ β retention ρ
      hPs hPb hdis code encode ν
    ∀ (j : Fin (n + 1))
      (F : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups reindex → ℂ),
    row none (row (some (.inr j)) (row none F)) =
    physicalSmallBigJointAverage (
    physicalMixedSignedPrimePatternAction (fun g => V (reindex.symm g).val) baseline ρ
      (fun a : ↥groupsᶜ => V a.val) q (fun g => probes (reindex.symm g).val)
      r t hrt Q h ξ (n-j.val) (k (n-j.val)) (fun _ => ∅)
      (fun i a y ev =>
        physicalMixedFullResidualPhase
          (repeatedBigPrimePatternCut (fun g => probes (reindex.symm g).val) r t i)
          (ζ (n-j.val)) θ (k (n-j.val)) cleanMixedSourceGate
          (cleanMixedTargetGate (fun _ => ∅)) a y ev *
        physicalMixedPhaseCutTransport
          (physical_root_prime_full_pattern_cut groups reindex probes r t i) (k (n-j.val))
          (fun a y ev => decoration (some (.inr j)) y
            ⟨physicalRootPrimeFullPatternEquiv groups reindex probes r t i,a,ev⟩) a y ev) (physicalSmallBigJointAverage F)) := by
  intro f patterns C ζroot kroot β hC K decoration row j F
  dsimp only [row]
  simp only [physical_root_fourier_permutation_row]
  apply congrArg physicalSmallBigJointAverage
  rw [physical_root_fourier_edge_eq_original_row]
  funext s
  exact physical_root_full_prime_edge_eq_signed_action groups reindex V probes r t hrt Q h ξ
    ζ k θ baseline ρ hPs hPb hdis q retention decoration j (physicalSmallBigJointAverage F) s

end Bounty

end

section

-- Original source module: PhysicalRootUntouchedPrimeEdge

/- An unaffected original projected Fourier edge has exactly the native residual;
its original Fourier multiplier is one after the exact cut transport. -/

open Finset
open scoped Classical
namespace Bounty

theorem physical_root_untouched_prime_edge_eq_signed_action
    {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
    [∀ z : PhysicalPrime P, NeZero z.2.val]
    (groups : Finset (Fin N)) (reindex : {g // g ∉ groupsᶜ} ≃ Fin M)
    (V : Fin N → ℝ) (probes : Fin N → Finset (Fin J))
    (r t : Finset (Fin M)) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (ζ : ℕ → ℝ) (k : ℕ → ℤ) (θ : ℝ)
    (baseline : (g : Fin M) → P (reindex.symm g).val → ℝ) (ρ : ℝ)
    (hPs : ∀ (a : ↥groupsᶜ) p, p ∈ P a.val → Nat.Prime p)
    (hPb : ∀ (g : Fin M) p, p ∈ P (reindex.symm g).val → Nat.Prime p)
    (hdis : ∀ (a : ↥groupsᶜ) (g : Fin M), Disjoint (P a.val) (P (reindex.symm g).val))
    [∀ g (p : P (reindex.symm g).val), NeZero p.val]
    (q : ℝ) (retention : Fin (n + 2) → ℝ)
    (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (reindex.symm g).val) → ℤ)
    (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) → ℝ) :
    let f := physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex
    let patterns := (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell)
      probes (r.map f) (t.map f)))
    let C := repeatedBigPrimePatternCut (ell := ell) probes (r.map f) (t.map f)
    let ζroot := fun time (_ : RepeatedBigPrimePatternIndex (ell := ell)
      probes (r.map f) (t.map f)) => ζ time
    let kroot := fun time (_ : RepeatedBigPrimePatternIndex (ell := ell)
      probes (r.map f) (t.map f)) => k time
    let β := fun (g : Fin M) (p : P (reindex.symm g).val) =>
      ((p.val : ℝ)*baseline g p)⁻¹
    let hC : ∀ i : patterns, ∀ a : ↥groupsᶜ, C i.val a.val = ∅ :=
      fun i a => physical_root_prime_full_pattern_small_cut groups reindex probes r t i.val a
    let K := fun (time : ℕ)
      (i : RepeatedBigPrimePatternIndex (ell := ell) probes (r.map f) (t.map f))
      (L R : PhysicalMarkLists P J ell) (aux : PhysicalAuxLabels P (C i)) =>
      if time % 2 = 0 then
        (starRingEnd ℂ) (physicalRootPrimeKernel P V probes (r.map f) (t.map f)
          ((Finset.disjoint_map f).mpr hrt) Q h ξ i R L aux)
      else physicalRootPrimeKernel P V probes (r.map f) (t.map f)
        ((Finset.disjoint_map f).mpr hrt) Q h ξ i L R aux
    let row := physicalRootFourierRow groups reindex patterns C hC kroot V q ζroot K θ β retention ρ
      hPs hPb hdis code encode ν
    ∀ (j : Fin (n + 1)),
      j ∉ physicalSelectedAffectedEdges (fun _ : Fin M => J + ell) B (n + 1) code →
      ∀ (F : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups reindex → ℂ),
    row none (row (some (.inr j)) (row none F)) =
    physicalSmallBigJointAverage (
    physicalMixedSignedPrimePatternAction (fun g => V (reindex.symm g).val) baseline ρ
      (fun a : ↥groupsᶜ => V a.val) q (fun g => probes (reindex.symm g).val)
      r t hrt Q h ξ (n-j.val) (k (n-j.val)) (fun _ => ∅)
      (fun i a y ev =>
        physicalMixedFullResidualPhase
          (repeatedBigPrimePatternCut (fun g => probes (reindex.symm g).val) r t i)
          (ζ (n-j.val)) θ (k (n-j.val)) cleanMixedSourceGate
          (cleanMixedTargetGate (fun _ => ∅)) a y ev) (physicalSmallBigJointAverage F)) := by
  intro f patterns C ζroot kroot β hC K row j hj F
  refine (physical_root_projected_prime_edge_eq_signed_action groups reindex V probes r t hrt
    Q h ξ ζ k θ baseline ρ hPs hPb hdis q retention code encode ν j F).trans ?_
  apply congrArg physicalSmallBigJointAverage
  congr 1
  funext i a y ev
  rw [physical_mixed_phase_cut_transport_apply_reverse]
  erw [physical_root_fourier_edge_multiplier_untouched groups reindex patterns C kroot
    code encode ν hPs hPb hdis j hj]
  exact mul_one _

end Bounty

end

section

-- Original source module: PhysicalSelectedFourierObservable

/- The selected Fourier factors are observables of fresh edge draws and
ordered ghost births, with no access to retained memory ordering. -/

open scoped Classical
namespace Bounty
section Observable
variable {S : Type} {N J ell n B : ℕ} {Ps : S → Finset ℕ}
  {P : Fin N → Finset ℕ}
  (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress
    (fun _ : Fin N => J + ell) B ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)))))
  (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress
      (fun _ : Fin N => J + ell) B ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)))) ×
    Fin (Fintype.card (FullMixedCommonBirthAddress
      (fun _ : Fin N => J + ell) B ((List.range (4 * n + 1)).map (physicalSelectedFineTag n))))) → ℝ)
  (encode : ((g : Fin N) × P g) → ℤ)

noncomputable def physicalSelectedEdgeFourierObservable
    (C : Fin N → Finset (Fin J)) (j : Fin n) :
    PhysicalBareResidueState Ps J ell → PhysicalBareResidueState Ps J ell →
    (∀ g, Fin (J + ell) → P g) → (∀ g, Fin (J + ell) → P g) →
    (∀ g, EdgeDrawObservation (P g) (physicalFullSharedIndices (ell := ell) (C g))ᶜ.card) → ℂ :=
  fun _ _ _ _ draw => physicalSelectedBirthMultiplier (fun _ : Fin N => J + ell) B n
    code ν encode (some (.inr j))
    (commonForestEdgeLabels (fun (_ : Fin n) g => physicalFullSharedIndices (ell := ell) (C g)) B j draw)

theorem physical_selected_edge_fourier_observable_norm_le
    (C : Fin N → Finset (Fin J)) (j : Fin n)
    (s t : PhysicalBareResidueState Ps J ell)
    (x y : ∀ g, Fin (J + ell) → P g)
    (draw : ∀ g, EdgeDrawObservation (P g) (physicalFullSharedIndices (ell := ell) (C g))ᶜ.card) :
    ‖physicalSelectedEdgeFourierObservable code ν encode C j s t x y draw‖ ≤ 1 :=
  physical_selected_birth_multiplier_norm_le _ _ _ _ _ _ _ _

noncomputable def physicalSelectedGhostFourierObservable (j : Fin (n + 1)) :
    PhysicalBareResidueState Ps J ell → (∀ g, Fin (J + ell) → P g) →
    (∀ g, FiniteOrderedTuple (UnrestrictedResidueParticle (fun p : P g => p.val))) → ℂ :=
  fun _ _ born => physicalSelectedBirthMultiplier (fun _ : Fin N => J + ell) B n
    code ν encode (some (.inl j))
    (fun a => if h : a.2.val < (born a.1).1 then some ⟨a.1, ((born a.1).2 ⟨a.2.val, h⟩).1⟩
      else none)

theorem physical_selected_ghost_fourier_observable_norm_le
    (j : Fin (n + 1)) (s : PhysicalBareResidueState Ps J ell)
    (active : ∀ g, Fin (J + ell) → P g)
    (born : ∀ g, FiniteOrderedTuple (UnrestrictedResidueParticle (fun p : P g => p.val))) :
    ‖physicalSelectedGhostFourierObservable code ν encode j s active born‖ ≤ 1 :=
  physical_selected_birth_multiplier_norm_le _ _ _ _ _ _ _ _

end Observable
end Bounty

end

section

-- Original source module: FullPermutationCommonBirth

/- The effective-parameter equivalence preserves the actual newly born
prime labels, including the common full-slot padding by none. -/

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

theorem full_permutation_parameter_birth_data
    (tag : Option (J ⊕ K))
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (e : FullPermutationMixedEvent n S B A Δ D tag x)
    (a : FullMixedLocalBirthAddress S B tag) :
    fullMixedEventBornData n S B A Δ' D' tag x
      (fullPermutationParameterEventEquiv n S B A Δ Δ' D D' hΔ hD tag x e) a =
      fullMixedEventBornData n S B A Δ D tag x e a := by
  have he : Δ = Δ' := funext hΔ
  subst Δ'
  cases tag with
  | none => exact Fin.elim0 a.2
  | some tag => cases tag <;> rfl

theorem full_permutation_parameter_birth_label
    (tag : Option (J ⊕ K))
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (e : FullPermutationMixedEvent n S B A Δ D tag x)
    (a : FullMixedLocalBirthAddress S B tag) :
    fullMixedEventBirthLabel n S B A Δ' D' tag x
      (fullPermutationParameterEventEquiv n S B A Δ Δ' D D' hΔ hD tag x e) a =
      fullMixedEventBirthLabel n S B A Δ D tag x e a := by
  unfold fullMixedEventBirthLabel
  rw [full_permutation_parameter_birth_data]

theorem full_permutation_parameter_common_birth_label
    (tag : Option (J ⊕ K))
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (n g)) M B)
    (e : FullPermutationMixedEvent n S B A Δ D tag x)
    (a : FullMixedCommonLocalAddress M B tag) :
    fullMixedCommonEventBirthLabel n S B A Δ' D' tag x
      (fullPermutationParameterEventEquiv n S B A Δ Δ' D D' hΔ hD tag x e) a =
      fullMixedCommonEventBirthLabel n S B A Δ D tag x e a := by
  rw [full_mixed_common_event_label_extension, full_mixed_common_event_label_extension]
  apply congrArg (fun f => optionalBirthExtension (fullMixedCommonLocalEmbedding S B tag) f a)
  funext b
  exact full_permutation_parameter_birth_label n S B A Δ Δ' D D' hΔ hD tag x e b

end Birth
end Bounty

end

section

-- Original source module: FiniteEventOccurrenceEquiv

/- Reading the owning event commutes with an exact event-path equivalence. -/

namespace Bounty
universe uK uX uY uE uF

theorem finite_event_path_occurrence_cast {K : Type uK} {X : Type uX}
    (E : K → X → Type uE) (t : ∀ k x, E k x → X) (ks : List K)
    {x y : X} (h : x = y) (p : FiniteEventPath E t ks x) (i : Fin ks.length) :
    finiteEventPathOccurrence E t ks y (cast (congrArg (FiniteEventPath E t ks) h) p) i =
      finiteEventPathOccurrence E t ks x p i := by
  cases h
  rfl

theorem finite_event_path_equiv_occurrence {K : Type uK} {X : Type uX} {Y : Type uY}
    (E : K → X → Type uE) (F : K → Y → Type uF)
    (t : ∀ k x, E k x → X) (u : ∀ k y, F k y → Y)
    (e : X → Y) (δ : ∀ k x, E k x ≃ F k (e x))
    (ht : ∀ k x a, e (t k x a) = u k (e x) (δ k x a))
    (ks : List K) (x : X) (p : FiniteEventPath E t ks x) (i : Fin ks.length) :
    finiteEventPathOccurrence F u ks (e x) (finiteEventPathEquiv E F t u e δ ht ks x p) i =
      let a := finiteEventPathOccurrence E t ks x p i
      ⟨e a.1, δ (ks.get i) a.1 a.2⟩ := by
  induction ks generalizing x with
  | nil => exact Fin.elim0 i
  | cons k ks ih =>
    rcases p with ⟨a, p⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change finiteEventPathOccurrence F u ks _
        (cast (congrArg (FiniteEventPath F u ks) (ht k x a))
          (finiteEventPathEquiv E F t u e δ ht ks (t k x a) p)) j = _
      rw [finite_event_path_occurrence_cast F u ks (ht k x a)]
      exact ih _ p j

end Bounty

end

section

-- Original source module: FiniteLocalPhaseEquiv

/- An exact event equivalence transports the complete ordinary local
phase product, including every source state along the path. -/

open Finset
namespace Bounty

theorem finite_event_local_phase_equiv
    {K X Y : Type*} (E : K → X → Type*) (F : K → Y → Type*)
    (t : ∀ k x, E k x → X) (u : ∀ k y, F k y → Y)
    (e : X → Y) (δ : ∀ k x, E k x ≃ F k (e x))
    (ht : ∀ k x a, e (t k x a) = u k (e x) (δ k x a))
    (phase : ∀ k x, E k x → ℂ) (phase' : ∀ k y, F k y → ℂ)
    (hp : ∀ k x a, phase' k (e x) (δ k x a) = phase k x a)
    (ks : List K) (x : X) (p : FiniteEventPath E t ks x) :
    finiteEventLocalPhase F u phase' ks (e x) (finiteEventPathEquiv E F t u e δ ht ks x p) =
      finiteEventLocalPhase E t phase ks x p := by
  rw [finite_event_local_phase_occurrences, finite_event_local_phase_occurrences]
  apply prod_congr rfl
  intro i _
  rw [finite_event_path_equiv_occurrence]
  exact hp _ _ _

end Bounty

end

section

-- Original source module: PhysicalSelectedParameterPhase

/- Effective event parameters preserve the selected Fourier birth
factor while the original residual phase is pulled back exactly. -/

namespace Bounty
section Parameter
variable {S I : Type} {Ps : S → Finset ℕ} {J ell N n : ℕ} {P : Fin N → Type}
  (sizes : ∀ g, P g → ℕ) {M : Fin N → ℕ}
  (shared : PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := Fin n) →
    ∀ g, Finset (Fin (M g))) (B : ℕ)
  (aux : ∀ k, SharedActiveLabels P (shared k) → Type)
  (Δ Δ' D D' : ∀ k c, aux k c → Fin N → ℤ)
  (hΔ : ∀ k, Δ k = Δ' k)
  (hD : ∀ k c a g p, ((sizes g p : ℤ) ∣ D k c a g ↔ (sizes g p : ℤ) ∣ D' k c a g))
  (residual : ∀ (tag : Option (Fin (n + 1) ⊕
      PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := Fin n))) x,
    FullPermutationMixedEvent sizes shared B aux Δ' D' tag x → ℂ)
  (code : BirthForestCode (Fintype.card (FullMixedCommonBirthAddress M B
    ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)))))
  (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress M B
      ((List.range (4 * n + 1)).map (physicalSelectedFineTag n)))) ×
    Fin (Fintype.card (FullMixedCommonBirthAddress M B
      ((List.range (4 * n + 1)).map (physicalSelectedFineTag n))))) → ℝ)
  (encode : Sigma P → ℤ)

theorem physical_selected_parameter_decorated_phase
    (tag : Option (Fin (n + 1) ⊕
      PhysicalMixedBigKey (Ps := Ps) (J := J) (ell := ell) (I := I) (K := Fin n)))
    (x : ProductBoundedOrderedState P (fun g => UnrestrictedResidueParticle (sizes g)) M B)
    (event : FullPermutationMixedEvent sizes shared B aux Δ D tag x) :
    physicalSelectedDecoratedPhase sizes shared B aux Δ' D' residual code ν encode tag x
      (fullPermutationParameterEventEquiv sizes shared B aux Δ Δ' D D' hΔ hD tag x event) =
    physicalSelectedDecoratedPhase sizes shared B aux Δ D
      (fun tag x event => residual tag x
        (fullPermutationParameterEventEquiv sizes shared B aux Δ Δ' D D' hΔ hD tag x event))
      code ν encode tag x event := by
  unfold physicalSelectedDecoratedPhase
  congr 1
  apply congrArg (physicalSelectedBirthMultiplier M B n code ν encode (physicalMixedBigTagErase tag))
  funext a
  exact full_permutation_parameter_common_birth_label sizes shared B aux Δ Δ' D D'
    hΔ hD tag x event _

end Parameter
end Bounty

end

section

-- Original source module: PhysicalRootFourierObservable

/- Ordinary local Fourier phases for the exact root coefficient, first on
effective events, then on planned events and the actual mixed word. -/

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
variable (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (e.symm g).val) → ℤ)
    (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) → ℝ)

variable (hPs : ∀ (s : ↥groupsᶜ) p, p ∈ P s.val → Nat.Prime p)
  (hPb : ∀ (g : Fin M) p, p ∈ P (e.symm g).val → Nat.Prime p)
  (hdis : ∀ (s : ↥groupsᶜ) (g : Fin M), Disjoint (P s.val) (P (e.symm g).val))

theorem physical_root_fourier_edge_observable
    (j : Fin (n + 1))
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e)
    (ev : PhysicalRootMixedEvent groups e patterns C k (some (.inr j)) s) :
    physicalRootMixedFourierMultiplier groups e patterns C k code encode ν hPs hPb hdis
        (some (.inr j)) s ev =
    physicalMixedCoefficientObservablePhase (fun g => C ev.1.val (e.symm g).val)
      (k (n - j.val) ev.1.val) ev.2.1
      (physicalSelectedEdgeFourierObservable code ν encode
        (fun g => C ev.1.val (e.symm g).val) j) s ev.2.2 := by
  unfold physicalRootMixedFourierMultiplier physicalMixedBigLocalPullback
    physicalRootPlannedFourierMultiplier physicalRootEffectiveFourierMultiplier
  dsimp only [physicalSelectedDecoratedPhase]
  simp only [one_mul]
  unfold physicalMixedEffectiveBigEventEquiv
  simp_rw [full_permutation_parameter_common_birth_label]
  dsimp only [physicalMixedBigEventTag, physicalMixedBigEventProjection,
    physicalMixedBigTagErase, physicalMixedTagBirthAddressEquiv, Equiv.refl_apply]
  erw [full_mixed_common_edge_labels_eq_observation]
  rfl

theorem physical_root_fourier_ghost_observable
    (j : Fin (n + 2))
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups e)
    (ev : PhysicalRootMixedEvent groups e patterns C k (some (.inl j)) s) :
    physicalRootMixedFourierMultiplier groups e patterns C k code encode ν hPs hPb hdis
        (some (.inl j)) s ev =
    physicalSmallBigGhostBirthPhase (fun _ : Fin M => J + ell) B
      (physicalSelectedGhostFourierObservable code ν encode j) s ev := by
  unfold physicalRootMixedFourierMultiplier physicalMixedBigLocalPullback
    physicalRootPlannedFourierMultiplier physicalRootEffectiveFourierMultiplier
  dsimp only [physicalSelectedDecoratedPhase]
  simp only [one_mul]
  unfold physicalMixedEffectiveBigEventEquiv
  simp_rw [full_permutation_parameter_common_birth_label]
  dsimp only [physicalMixedBigEventTag, physicalMixedBigEventProjection,
    physicalMixedBigTagErase, physicalMixedTagBirthAddressEquiv, Equiv.refl_apply]
  erw [full_mixed_common_ghost_labels_eq_observation]
  rfl

end Root
end Bounty

end

section

-- Original source module: PhysicalRootFourierReindex

/- The actual root Fourier multiplier is invariant under the exact
pending-memory event reindexing on each original big edge. -/

open scoped Classical
namespace Bounty

theorem physical_root_fourier_edge_reindex
    {I : Type} {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
    (groups : Finset (Fin N)) (index : {g // g ∉ groupsᶜ} ≃ Fin M)
    (patterns : Finset I) (C : I → Fin N → Finset (Fin J))
    (k : ℕ → I → ℤ)
    [∀ g (p : P (index.symm g).val), NeZero p.val]
    (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (index.symm g).val) → ℤ)
    (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) → ℝ)
    (hPs : ∀ (a : ↥groupsᶜ) p, p ∈ P a.val → Nat.Prime p)
    (hPb : ∀ (g : Fin M) p, p ∈ P (index.symm g).val → Nat.Prime p)
    (hdis : ∀ (a : ↥groupsᶜ) (g : Fin M), Disjoint (P a.val) (P (index.symm g).val))
    (j : Fin (n + 1))
    (s : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups index)
    (τ : ∀ g, Equiv.Perm (Fin (s.2 g).2.1.val))
    (ev : PhysicalRootMixedEvent groups index patterns C k (some (.inr j)) s) :
    physicalRootMixedFourierMultiplier groups index patterns C k code encode ν hPs hPb hdis
      (some (.inr j)) (s.1, productMemoryReindex s.2 τ)
      ⟨ev.1, ev.2.1, physicalMixedCoefficientReindex
        (fun g => C ev.1.val (index.symm g).val) (k (n - j.val) ev.1.val) ev.2.1 s τ ev.2.2⟩ =
    physicalRootMixedFourierMultiplier groups index patterns C k code encode ν hPs hPb hdis
      (some (.inr j)) s ev := by
  refine (physical_root_fourier_edge_observable groups index patterns C k code encode ν
    hPs hPb hdis j (s.1, productMemoryReindex s.2 τ)
    ⟨ev.1, ev.2.1, physicalMixedCoefficientReindex
      (fun g => C ev.1.val (index.symm g).val) (k (n - j.val) ev.1.val) ev.2.1 s τ ev.2.2⟩).trans ?_
  exact (physical_mixed_coefficient_observable_reindex
    (fun g => C ev.1.val (index.symm g).val) (k (n - j.val) ev.1.val) ev.2.1
    (physicalSelectedEdgeFourierObservable code ν encode
      (fun g => C ev.1.val (index.symm g).val) j) s τ ev.2.2).trans
    (physical_root_fourier_edge_observable groups index patterns C k code encode ν
      hPs hPb hdis j s ev).symm

end Bounty

end

section

-- Original source module: PhysicalRootProjectedPrimeSymmetry

/- The exact projected root Fourier prime edge preserves pending-memory symmetry,
for both chronological kernel orientations and the original Fourier multiplier. -/

open Finset
open scoped Classical
namespace Bounty

theorem physical_root_projected_prime_edge_memory_symmetric
    {N M J ell n B : ℕ} {P : Fin N → Finset ℕ}
    [∀ z : PhysicalPrime P, NeZero z.2.val]
    (groups : Finset (Fin N)) (reindex : {g // g ∉ groupsᶜ} ≃ Fin M)
    (V : Fin N → ℝ) (probes : Fin N → Finset (Fin J))
    (r t : Finset (Fin M)) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (ζ : ℕ → ℝ) (k : ℕ → ℤ) (θ : ℝ)
    (baseline : (g : Fin M) → P (reindex.symm g).val → ℝ) (ρ : ℝ)
    (hPs : ∀ (a : ↥groupsᶜ) p, p ∈ P a.val → Nat.Prime p)
    (hPb : ∀ (g : Fin M) p, p ∈ P (reindex.symm g).val → Nat.Prime p)
    (hdis : ∀ (a : ↥groupsᶜ) (g : Fin M), Disjoint (P a.val) (P (reindex.symm g).val))
    [∀ g (p : P (reindex.symm g).val), NeZero p.val]
    (q : ℝ) (retention : Fin (n + 2) → ℝ)
    (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (reindex.symm g).val) → ℤ)
    (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) → ℝ) :
    let f := physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex
    let patterns := (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell)
      probes (r.map f) (t.map f)))
    let C := repeatedBigPrimePatternCut (ell := ell) probes (r.map f) (t.map f)
    let ζroot := fun time (_ : RepeatedBigPrimePatternIndex (ell := ell)
      probes (r.map f) (t.map f)) => ζ time
    let kroot := fun time (_ : RepeatedBigPrimePatternIndex (ell := ell)
      probes (r.map f) (t.map f)) => k time
    let β := fun (g : Fin M) (p : P (reindex.symm g).val) =>
      ((p.val : ℝ)*baseline g p)⁻¹
    let hC : ∀ i : patterns, ∀ a : ↥groupsᶜ, C i.val a.val = ∅ :=
      fun i a => physical_root_prime_full_pattern_small_cut groups reindex probes r t i.val a
    let K := fun (time : ℕ)
      (i : RepeatedBigPrimePatternIndex (ell := ell) probes (r.map f) (t.map f))
      (L R : PhysicalMarkLists P J ell) (aux : PhysicalAuxLabels P (C i)) =>
      if time % 2 = 0 then
        (starRingEnd ℂ) (physicalRootPrimeKernel P V probes (r.map f) (t.map f)
          ((Finset.disjoint_map f).mpr hrt) Q h ξ i R L aux)
      else physicalRootPrimeKernel P V probes (r.map f) (t.map f)
        ((Finset.disjoint_map f).mpr hrt) Q h ξ i L R aux
    let row := physicalRootFourierRow groups reindex patterns C hC kroot V q ζroot K θ β retention ρ
      hPs hPb hdis code encode ν
    ∀ (j : Fin (n + 1))
      (F : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups reindex → ℂ),
      (∀ s, ProductMemorySymmetric (fun x => F (s,x))) →
      ∀ s, ProductMemorySymmetric (fun x =>
        row none (row (some (.inr j)) (row none F)) (s,x)) := by
  intro f patterns C ζroot kroot β hC K row j F hF
  have hedge := physical_root_projected_prime_edge_eq_signed_action
    groups reindex V probes r t hrt Q h ξ ζ k θ baseline ρ hPs hPb hdis
    q retention code encode ν j F
  change row none (row (some (.inr j)) (row none F)) = _ at hedge
  rw [hedge]
  apply physical_small_big_joint_average_memory_symmetric
  apply physical_mixed_signed_prime_pattern_memory_symmetric
  · intro i a y τ ev
    apply congrArg₂ (fun z w : ℂ => z * w)
    · exact physical_mixed_concrete_residual_reindex _ (ζ (n-j.val)) θ
        (k (n-j.val)) (fun _ => ∅) a y τ ev
    · apply physical_mixed_phase_cut_transport_reindex
      intro a' y' τ' ev'
      exact physical_root_fourier_edge_reindex groups reindex patterns C kroot
        code encode ν hPs hPb hdis j y' τ'
        ⟨physicalRootPrimeFullPatternEquiv groups reindex probes r t i, a', ev'⟩
  · exact physical_small_big_joint_average_memory_symmetric F hF

end Bounty

end

section

-- Original source module: PhysicalRootProjectedPrimeNorm

/- A uniform bound for every projected original Fourier prime edge, in its
actual small-residue and reciprocal-birth measure. The constant is chosen
before all root dimensions, prime pools, and Fourier data. -/

open Finset
open scoped Classical
namespace Bounty

theorem exists_physical_root_projected_prime_edge_norm_bound
    {q vs : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hvs : 0 < vs) (ell : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀
    {N M J n B : ℕ} {P : Fin N → Finset ℕ}
    [∀ z : PhysicalPrime P, NeZero z.2.val]
    (groups : Finset (Fin N)) (reindex : {g // g ∉ groupsᶜ} ≃ Fin M)
    [∀ z : PhysicalPrime (fun a : ↥groupsᶜ => P a.val), NeZero z.2.val]
    (V : Fin N → ℝ) (probes : Fin N → Finset (Fin J))
    (r t : Finset (Fin M)) (hrt : Disjoint r t) (Q : ℕ) (h ξ : ℝ)
    (ζ : ℕ → ℝ) (k : ℕ → ℤ) (θ : ℝ)
    (baseline : (g : Fin M) → P (reindex.symm g).val → ℝ) (ρ : ℝ)
    (hPs : ∀ (a : ↥groupsᶜ) p, p ∈ P a.val → Nat.Prime p)
    (hPb : ∀ (g : Fin M) p, p ∈ P (reindex.symm g).val → Nat.Prime p)
    (hdis : ∀ (a : ↥groupsᶜ) (g : Fin M), Disjoint (P a.val) (P (reindex.symm g).val))
    [∀ g (p : P (reindex.symm g).val), NeZero p.val]
    (retention : Fin (n + 2) → ℝ)
    (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
    (encode : ((g : Fin M) × P (reindex.symm g).val) → ℤ)
    (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
      Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
        ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) → ℝ),
    let f := physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex
    let patterns := (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell)
      probes (r.map f) (t.map f)))
    let C := repeatedBigPrimePatternCut (ell := ell) probes (r.map f) (t.map f)
    let ζroot := fun time (_ : RepeatedBigPrimePatternIndex (ell := ell)
      probes (r.map f) (t.map f)) => ζ time
    let kroot := fun time (_ : RepeatedBigPrimePatternIndex (ell := ell)
      probes (r.map f) (t.map f)) => k time
    let β := fun (g : Fin M) (p : P (reindex.symm g).val) =>
      ((p.val : ℝ)*baseline g p)⁻¹
    let hC : ∀ i : patterns, ∀ a : ↥groupsᶜ, C i.val a.val = ∅ :=
      fun i a => physical_root_prime_full_pattern_small_cut groups reindex probes r t i.val a
    let K := fun (time : ℕ)
      (i : RepeatedBigPrimePatternIndex (ell := ell) probes (r.map f) (t.map f))
      (L R : PhysicalMarkLists P J ell) (aux : PhysicalAuxLabels P (C i)) =>
      if time % 2 = 0 then
        (starRingEnd ℂ) (physicalRootPrimeKernel P V probes (r.map f) (t.map f)
          ((Finset.disjoint_map f).mpr hrt) Q h ξ i R L aux)
      else physicalRootPrimeKernel P V probes (r.map f) (t.map f)
        ((Finset.disjoint_map f).mpr hrt) Q h ξ i L R aux
    let row := physicalRootFourierRow groups reindex patterns C hC kroot V q ζroot K θ β retention ρ
      hPs hPb hdis code encode ν
    ∀ (m : ℕ), (∀ g : Fin M, (probes (reindex.symm g).val).card ≤ m) →
    0 < ξ → (∀ a : ↥groupsᶜ, vs ≤ V a.val) →
    (∀ g : Fin M, ∑ p ∈ P (reindex.symm g).val, 1 / (p : ℝ) = V (reindex.symm g).val) →
    (∀ g p, 1 / 2 ≤ baseline g p ∧ baseline g p ≤ 1) →
    ∀ (v vmin vmax : ℝ), 0 < ρ → ρ < 1 → 1 < v → 0 < vmin →
    (∀ g : Fin M, vmin ≤ V (reindex.symm g).val) →
    (∀ g : Fin M, V (reindex.symm g).val ≤ vmax) →
    ∀ (j : Fin (n + 1))
      (F : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups reindex → ℂ),
    (∀ s, ProductMemorySymmetric (fun x => F (s,x))) →
    let w := physicalSmallBigMeasure (fun a : ↥groupsᶜ => V a.val)
      (productMemoryWeight (fun g p => β g p / V (reindex.symm g).val)
        (fun g => unrestrictedResidueWeight (fun p => β g p / V (reindex.symm g).val)))
    cleanActiveNorm w (row none (row (some (.inr j)) (row none F))) ≤
      repeatedBigFamilyEnvelope M m Q ξ * A ^ groupsᶜ.card *
        Real.sqrt (unrestrictedEdgeEnergyBound ρ v vmin vmax (ell + m) ^ M) *
          cleanActiveNorm w F := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_physical_mixed_signed_prime_pattern_projected_norm_bound hq0 hq1 hvs ell
  refine ⟨A, hA, ?_⟩
  intro N M J n B P _ groups reindex _ V probes r t hrt Q h ξ ζ k θ baseline ρ hPs hPb hdis _
    retention code encode ν f patterns C ζroot kroot β hC K row
    m hprobes hξ hVs hmass hbaseline v vmin vmax hρ0 hρ1 hv hvmin hVlo hVhi j F hF w
  let decoration := physicalRootMixedFourierMultiplier groups reindex patterns C kroot
    code encode ν hPs hPb hdis
  have hrow := physical_root_projected_prime_edge_eq_signed_action groups reindex V probes r t
    hrt Q h ξ ζ k θ baseline ρ hPs hPb hdis q retention code encode ν j F
  change row none (row (some (.inr j)) (row none F)) = _ at hrow
  rw [hrow]
  have hμ : (fun (g : Fin M) (p : P (reindex.symm g).val) => β g p / V (reindex.symm g).val) =
      (fun g => tiltedPhysicalBirthLaw (P := fun g : Fin M => P (reindex.symm g).val)
        (fun g => V (reindex.symm g).val) g (baseline g)) := by
    funext g p
    exact physical_root_tilted_birth_law (fun g => V (reindex.symm g).val) baseline g p
  dsimp only [w]
  have hμpoint (g : Fin M) (p : P (reindex.symm g).val) :
      β g p / V (reindex.symm g).val =
        tiltedPhysicalBirthLaw (P := fun g : Fin M => P (reindex.symm g).val)
          (fun g => V (reindex.symm g).val) g (baseline g) p :=
    congrFun (congrFun hμ g) p
  simp_rw [hμpoint]
  have hb := hbound ↥groupsᶜ (Fin M) (fun a : ↥groupsᶜ => P a.val)
    (fun g => P (reindex.symm g).val) J B m (fun g => V (reindex.symm g).val) baseline ρ
    (fun a : ↥groupsᶜ => V a.val) (fun g => probes (reindex.symm g).val) r t hrt hprobes
    Q h ξ hξ (n-j.val) (k (n-j.val)) (fun _ => ∅) hVs hmass hbaseline
    v vmin vmax hρ0 hρ1 hv hvmin hVlo hVhi
    (fun i a y ev =>
      physicalMixedFullResidualPhase
        (repeatedBigPrimePatternCut (fun g => probes (reindex.symm g).val) r t i)
        (ζ (n-j.val)) θ (k (n-j.val)) cleanMixedSourceGate
        (cleanMixedTargetGate (fun _ => ∅)) a y ev *
      physicalMixedPhaseCutTransport
        (physical_root_prime_full_pattern_cut groups reindex probes r t i) (k (n-j.val))
        (fun a y ev => decoration (some (.inr j)) y
          ⟨physicalRootPrimeFullPatternEquiv groups reindex probes r t i,a,ev⟩) a y ev)
    (by
      intro i a y ev
      apply physical_mixed_concrete_residual_mul_norm_le
      rw [physical_mixed_phase_cut_transport_apply_reverse]
      exact physical_root_fourier_multiplier_norm_le groups reindex patterns C kroot
        code encode ν hPs hPb hdis _ _ _) F hF
  simpa only [Fintype.card_fin, Fintype.card_coe] using hb

end Bounty

end
end

section

/- Pool-preserving realizations of the original candidate prime groups.
The arithmetic proof follows CandidateOmissionParameters and
CandidatePromotionRarity; no state-space transport is required. -/

open Finset Filter
open scoped Classical Topology

namespace Bounty

structure CandidateMixedPoolRealization {S G : Type}
    (scale L : ℝ) (Ps : S → Finset ℕ) (P : G → Finset ℕ) where
  smallIndex : S ↪ CandidateSmallGroup scale L
  bigIndex : G → CandidateBigGroup scale L
  smallPool_eq : ∀ s, Ps s = candidateSmallPool scale L (smallIndex s)
  bigPool_eq : ∀ g, P g = candidatePBand (scale * L) (bigIndex g).val

theorem eventually_realized_candidate_omission_arithmetic
    {scale : ℝ} (hscale : 0 < scale) (ell : ℕ) (C₂ : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (S G : Type) [Fintype S]
      (Ps : S → Finset ℕ) (P : G → Finset ℕ)
      (_R : CandidateMixedPoolRealization scale L Ps P),
      (∀ s p, p ∈ Ps s → p.Prime) ∧
      Pairwise (fun s t => Disjoint (Ps s) (Ps t)) ∧
      ∀ (J : ℕ) (labels : PhysicalMarkLists Ps J ell) (g : G) (p : P g),
        p.val.Prime ∧ ∀ k : ℤ, k ≠ 0 → (k.natAbs : ℝ) ≤ L ^ C₂ →
        ¬ (p.val : ℤ) ∣ k ∧
        ∀ A : PrimeOmissionChoices (physicalGroupMarks labels) ell,
          primeOmissionProduct (physicalGroupMarks labels) ell A < p.val := by
  filter_upwards [eventually_candidate_omission_bounds hscale ell C₂,
    eventually_gt_atTop (0 : ℝ)] with L hL hpos
  intro S G _ Ps P R
  have hsmall (s : S) : (R.smallIndex s).val ∈ candidateSmallPIndices scale L :=
    (R.smallIndex s).property
  have hbig (g : G) : (R.bigIndex g).val ∈ candidateBigPIndices scale L :=
    (R.bigIndex g).property
  have hcard : Fintype.card S ≤ (candidateSmallPIndices scale L).card := by
    simpa only [CandidateSmallGroup, Fintype.card_coe] using
      Fintype.card_le_of_injective R.smallIndex R.smallIndex.injective
  refine ⟨?_, ?_, ?_⟩
  · intro s p hp
    rw [R.smallPool_eq s] at hp
    exact hL.2.2.2.2.1 _ (mem_union_left _ (hsmall s)) p hp
  · intro s t hst
    rw [R.smallPool_eq s, R.smallPool_eq t]
    exact hL.2.2.2.2.2 (fun he => hst (R.smallIndex.injective (Subtype.ext he)))
  · intro J labels g p
    have hp : p.val ∈ candidatePBand (scale * L) (R.bigIndex g).val := by
      rw [← R.bigPool_eq g]
      exact p.property
    have hbp := hL.2.2.2.1 _ (hbig g) p.val hp
    refine ⟨hbp.1, ?_⟩
    intro k hk hkb
    refine ⟨physical_pending_step_not_dvd_of_bounds (Int.natAbs_pos.mpr hk)
      (hkb.trans_lt hL.2.1) hbp.2.le, ?_⟩
    intro A
    have hb := prime_omission_product_real_le_pow (physicalGroupMarks labels) ell
      (fun s q hq => hL.2.2.1 _ (hsmall s) q (by
        change q ∈ candidateSmallPool scale L (R.smallIndex s)
        rw [← R.smallPool_eq s]
        exact physical_group_marks_subset labels s hq)) A
    have hpw : (Real.exp (L ^ (1/5 : ℝ))) ^ (ell * Fintype.card S) ≤
        (Real.exp (L ^ (1/5 : ℝ))) ^ (ell * (candidateSmallPIndices scale L).card) :=
      pow_le_pow_right₀ (Real.one_le_exp (Real.rpow_nonneg hpos.le _))
        (Nat.mul_le_mul_left ell hcard)
    exact_mod_cast ((hb.trans hpw).trans_lt hL.1).trans hbp.2

end Bounty
end

section

/- Indicator probability is independent of finite enumeration and decision
procedures. This isolates the permutation enumeration transport. -/

open Finset
open scoped Classical

namespace Bounty

theorem uniform_indicator_probability_le_of_fraction {T : Type*}
    (fa fb : Fintype T) (pred : T → Prop) (d₁ d₂ : DecidablePred pred)
    {b : ℝ}
    (h : ((@Finset.filter T pred d₁ (@Finset.univ T fa)).card : ℝ) /
      (@Fintype.card T fa : ℝ) ≤ b) :
    (∑ x ∈ @Finset.univ T fb,
      @ite ℝ (pred x) (d₂ x) (1 / (@Fintype.card T fb : ℝ)) 0) ≤ b := by
  cases Subsingleton.elim fb fa
  cases Subsingleton.elim d₁ (fun x => Classical.propDecidable (pred x))
  cases Subsingleton.elim d₂ (fun x => Classical.propDecidable (pred x))
  exact (le_of_eq (@uniform_indicator_probability_eq T fa pred)).trans h

end Bounty
end

section

/- Original candidate omission rarity on arbitrary pool-preserving group
indices. This is CandidatePromotionRarity and CandidateMixedReverseRarity
with the original finite groups realized directly in the target types. -/

open Finset Filter
open scoped Classical Topology

namespace Bounty

theorem eventually_realized_candidate_mixed_eligibility_probability_le
    {scale : ℝ} (hscale : 0 < scale) (ell : ℕ) (C₂ : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (S G : Type) [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
        (Ps : S → Finset ℕ) (P : G → Finset ℕ)
        (_R : CandidateMixedPoolRealization scale L Ps P) (J B : ℕ)
        (M : G → ℕ) (shared : ∀ g, Finset (Fin (M g)))
        (D_B : SharedActiveLabels (fun g => ↥(P g)) shared → ℕ)
        (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L ^ C₂ →
      ∀ s : PhysicalSmallBigState Ps J ell
        (ProductBoundedOrderedState (fun g => ↥(P g))
          (fun g => UnrestrictedResidueParticle (fun p : P g => p.val)) M B),
      productTotalMemory s.2 ≤ B →
      (∑ σ : PhysicalPermutations S J ell,
        if physicalSmallBigEligible (fun g (p : P g) => p.val) shared B
          (fun d c _ => -(k * (D_B c * physicalSharedProduct d : ℕ)))
          (fun d c _ => (D_B c * physicalSharedProduct d : ℕ))
          (physicalSmallBigPermutation σ s)
        then 1 / (Fintype.card (PhysicalPermutations S J ell) : ℝ)
        else 0) ≤ (B : ℝ) / (((J + ell).choose ell) ^ Fintype.card S : ℕ) := by
  filter_upwards [eventually_realized_candidate_omission_arithmetic hscale ell C₂]
    with L hL
  intro S G _ dS _ _ Ps P R J B M shared D_B k hk hkb s hB
  cases Subsingleton.elim dS (Classical.decEq S)
  obtain ⟨hPs, hdis, harith⟩ := hL S G Ps P R
  simp only [physical_small_big_eligible_permute_iff]
  let pred := fun σ : PhysicalPermutations S J ell =>
    ∃ g, (unrestrictedResidueEligible (fun p : P g => p.val)
      (-(k * (smallSourcePermutationDilation s.1.2
        (D_B (productActiveMemorySplit shared B s.2).1) σ : ℤ)))
      (smallSourcePermutationDilation s.1.2
        (D_B (productActiveMemorySplit shared B s.2).1) σ) (s.2 g).2.2).Nonempty
  have h := small_source_pending_eligible_fraction_le s.1.2 hPs hdis
    (fun g (p : P g) => p.val) s.2
    (D_B (productActiveMemorySplit shared B s.2).1) k
    (fun g j => (harith J s.1.2 g ((s.2 g).2.2 j).1).1)
    (fun g j => ((harith J s.1.2 g ((s.2 g).2.2 j).1).2 k hk hkb).1)
    (fun g j => ((harith J s.1.2 g ((s.2 g).2.2 j).1).2 k hk hkb).2)
  change (∑ σ : PhysicalPermutations S J ell,
    if pred σ then (1 : ℝ) / Fintype.card (PhysicalPermutations S J ell) else 0) ≤ _
  exact uniform_indicator_probability_le_of_fraction _ _ pred _ _
    (h.trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr hB) (Nat.cast_nonneg _)))

theorem eventually_realized_candidate_mixed_reverse_eligibility_probability_le
    {scale : ℝ} (hscale : 0 < scale) (ell : ℕ) (C₂ : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (S G : Type) [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
        (Ps : S → Finset ℕ) (P : G → Finset ℕ)
        (_R : CandidateMixedPoolRealization scale L Ps P) (J B : ℕ)
        (M : G → ℕ) (shared : ∀ g, Finset (Fin (M g)))
        (D_B : SharedActiveLabels (fun g => ↥(P g)) shared → ℕ)
        (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L ^ C₂ →
      ∀ s : PhysicalSmallBigState Ps J ell
        (ProductBoundedOrderedState (fun g => ↥(P g))
          (fun g => UnrestrictedResidueParticle (fun p : P g => p.val)) M B),
      productTotalMemory s.2 ≤ B →
      (∑ σ : PhysicalPermutations S J ell,
        if physicalSmallBigEligible (fun g (p : P g) => p.val) shared B
          (fun d c _ => -(-(k * (D_B c * physicalSharedProduct d : ℕ))))
          (fun d c _ => (D_B c * physicalSharedProduct d : ℕ))
          (physicalSmallBigPermutation σ s)
        then 1 / (Fintype.card (PhysicalPermutations S J ell) : ℝ)
        else 0) ≤ (B : ℝ) / (((J + ell).choose ell) ^ Fintype.card S : ℕ) := by
  filter_upwards [eventually_realized_candidate_mixed_eligibility_probability_le hscale ell C₂]
    with L hL
  intro S G _ _ _ _ Ps P R J B M shared D_B k hk hkb s hB
  have he : (fun (d : PhysicalSharedLists Ps J)
      (c : SharedActiveLabels (fun g => ↥(P g)) shared) (_ : G) =>
      -(-(k * (D_B c * physicalSharedProduct d : ℕ)))) =
      (fun d c _ => -((-k) * (D_B c * physicalSharedProduct d : ℕ))) := by
    funext d c g
    ring
  rw [he]
  exact hL S G Ps P R J B M shared D_B (-k) (neg_ne_zero.mpr hk)
    (by simpa only [Int.natAbs_neg] using hkb) s hB

end Bounty
end

section

/- The exact uniform small-slot average preserves a cap depending only
on the big state. Separating this identity keeps full event types opaque. -/

open Finset
open scoped Classical

namespace Bounty

theorem physical_small_big_average_cap_eq
    {S X : Type*} [Fintype S] [DecidableEq S]
    {Ps : S → Finset ℕ} {J ell : ℕ}
    (f : PhysicalSmallBigState Ps J ell X → ℂ) (cap : X → Prop)
    (dCap : DecidablePred cap)
    (hf : ∀ s, f s = @ite ℂ (cap s.2) (dCap s.2) (f s) 0) :
    physicalSmallBigAverage f = fun s =>
      ∑ σ : PhysicalPermutations S J ell,
        ((1 / (Fintype.card (PhysicalPermutations S J ell) : ℝ) : ℝ) : ℂ) *
          (@ite ℂ (cap s.2) (dCap s.2) (f (physicalSmallBigPermutation σ s)) 0) := by
  funext s
  rw [physical_small_big_average_uniform (inferInstance)]
  apply sum_congr rfl
  intro σ _
  apply congrArg (fun z : ℂ =>
    ((1 / (Fintype.card (PhysicalPermutations S J ell) : ℝ) : ℝ) : ℂ) * z)
  exact hf (physicalSmallBigPermutation σ s)

end Bounty
end

section

/- Uniform small-slot averaging of the generic promotion estimate.
Only the actual eligibility probability remains as the finite input. -/

open Finset Filter
open scoped Classical Topology

namespace Bounty

theorem exists_physical_small_big_uniform_promotion_energy_bound
    {q vs : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hvs : 0 < vs) (ell : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ (S G : Type) [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
        (Ps : S → Finset ℕ) [∀ p : PhysicalPrime Ps, NeZero p.2.val]
        (P : G → Finset ℕ) [∀ g (p : P g), NeZero p.val],
      ∀ J B : ℕ,
      ∀ M : G → ℕ,
      ∀ shared : ∀ g, Finset (Fin (M g)),
      ∀ D_B : SharedActiveLabels ((fun g => ↥(P g))) shared → ℕ,
      ∀ k : ℤ,
      ∀ Vs : S → ℝ, (∀ g, vs ≤ Vs g) →
      ∀ μ : ∀ g, (fun g => ↥(P g)) g → ℝ, ∀ ρ : ℝ,
      ∀ V : G → ℝ,
      ∀ v vmin vmax : ℝ, 0 < ρ → ρ < 1 → 1 < v → 0 < vmin →
      (∀ g, vmin ≤ V g) → (∀ g, V g ≤ vmax) →
      (∀ g p, 0 ≤ μ g p) → (∀ g, ∑ p, μ g p ≤ 2) →
      ∀ T : ℕ, (∀ g, (shared g)ᶜ.card ≤ T) →
      ∀ Φ : ∀ s : PhysicalSmallBigState (Ps) J ell
        (ProductBoundedOrderedState ((fun g => ↥(P g)))
          (fun g => UnrestrictedResidueParticle ((fun g (p : P g) => p.val) g)) M B),
        PhysicalSmallBigEvent (PhysicalSmallBigFullEvent ((fun g (p : P g) => p.val)) shared B
          (fun d c _ => -(k * (D_B c * physicalSharedProduct d : ℕ)))
          (fun d c _ => (D_B c * physicalSharedProduct d : ℕ))) s → ℂ,
      ∀ H : ℝ, 0 ≤ H → (∀ s e, ‖Φ s e‖ ≤ H) →
      ∀ δ : ℝ, 0 ≤ δ →
      (∀ s : PhysicalSmallBigState Ps J ell
        (ProductBoundedOrderedState (fun g => ↥(P g))
          (fun g => UnrestrictedResidueParticle (fun p : P g => p.val)) M B),
        productTotalMemory s.2 ≤ B →
        (∑ σ : PhysicalPermutations S J ell,
          if physicalSmallBigEligible (fun g (p : P g) => p.val) shared B
            (fun d c _ => -(k * (D_B c * physicalSharedProduct d : ℕ)))
            (fun d c _ => (D_B c * physicalSharedProduct d : ℕ))
            (physicalSmallBigPermutation σ s)
          then 1 / (Fintype.card (PhysicalPermutations S J ell) : ℝ) else 0) ≤ δ) →
      ∀ F : PhysicalSmallBigState (Ps) J ell
        (ProductBoundedOrderedState ((fun g => ↥(P g)))
          (fun g => UnrestrictedResidueParticle ((fun g (p : P g) => p.val) g)) M B) → ℂ,
      (∀ s, ProductMemorySymmetric (fun x => F (s, x))) →
      physicalSmallBigEnergy Vs (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g)))
        (physicalSmallBigAverage (fun s =>
          physicalSmallBigFullPhasedAction ((fun g (p : P g) => p.val)) shared B
            (fun d c _ => -(k * (D_B c * physicalSharedProduct d : ℕ)))
            (fun d c _ => (D_B c * physicalSharedProduct d : ℕ)) μ ρ V
            (fun c => k * D_B c) Vs q
            (fun y e => if ∃ g, (e.2.2 g).2.1.Nonempty then Φ y e else 0) F s)) ≤
      δ *
        (H ^ 2 * (A ^ (2 * (Fintype.card S)) *
          unrestrictedEdgeEnergyBound ρ v vmin vmax T ^ (Fintype.card G))) *
        physicalSmallBigEnergy Vs (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g))) F := by
  obtain ⟨A, hA, hbound⟩ := exists_physical_small_big_promotion_average_energy_bound hq0 hq1 hvs ell
  refine ⟨A, hA, ?_⟩
  intro S G _ _ _ _ Ps _ P _ J B M shared D_B k Vs hVs μ ρ V v vmin vmax hρ0 hρ1 hv hvmin hVlo hVhi
    hμ hmass T ht Φ H hH hΦ δ hδ hrare F hF
  let aux : PhysicalAuxLabels (Ps) (fun _ => (∅ : Finset (Fin J))) :=
    fun _ j => False.elim ((Finset.notMem_empty j.val) j.property)
  let π : PhysicalPermutations (S) J ell → ℝ :=
    fun _ => 1 / (Fintype.card (PhysicalPermutations (S) J ell) : ℝ)
  have hπ : ∀ σ, 0 ≤ π σ := fun _ => one_div_nonneg.mpr (Nat.cast_nonneg _)
  have hπmass : ∑ σ, π σ ≤ 1 := by
    simp only [π, sum_const, card_univ, nsmul_eq_mul, mul_one_div]
    exact div_self_le_one _
  have h := hbound (S) (G)
    (PhysicalPermutations (S) J ell)
    (Ps) ((fun g => ↥(P g))) ((fun g (p : P g) => p.val))
    J M shared B
    (fun _ d c _ => -(k * (D_B c * physicalSharedProduct d : ℕ)))
    (fun _ d c _ => (D_B c * physicalSharedProduct d : ℕ)) μ ρ V (fun _ c => k * D_B c)
    Vs hVs aux v vmin vmax hρ0 hρ1 hv hvmin hVlo hVhi hμ hmass T ht π hπ hπmass
    (fun σ => σ) (fun s => productTotalMemory s.2 ≤ B) (fun _ => Φ) H hH (fun _ => hΦ)
    δ hδ hrare F hF
  have he := physical_small_big_average_cap_eq (S := S) (Ps := Ps) (J := J) (ell := ell)
    (fun s => physicalSmallBigFullPhasedAction (fun g (p : P g) => p.val) shared B
      (fun d c _ => -(k * (D_B c * physicalSharedProduct d : ℕ)))
      (fun d c _ => (D_B c * physicalSharedProduct d : ℕ)) μ ρ V (fun c => k * D_B c) Vs q
      (fun y e => if ∃ g, (e.2.2 g).2.1.Nonempty then Φ y e else 0) F s)
    (fun x => productTotalMemory x ≤ B)
    (fun x => Classical.propDecidable (productTotalMemory x ≤ B))
    (by
      intro s
      by_cases hs : productTotalMemory s.2 ≤ B
      · simp only [hs, if_true]
      · simp only [hs, if_false]
        exact physical_small_big_full_phased_zero_above_cap (fun g (p : P g) => p.val) shared B
          _ _ μ ρ V (fun c => k * D_B c) Vs q _ F s hs)
  dsimp only [π] at h
  exact (le_of_eq (congrArg
    (physicalSmallBigEnergy Vs (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g))))
    he)).trans h

end Bounty
end

section

/- Original proof: CandidateMixedPromotionEnergy.lean. Generalized only to pool-preserving group realizations. -/

/- The actual candidate-pool mixed promotion estimate. The scalar omission
probability and all per-choice operator bounds are discharged. A fixed
auxiliary draw is absorbed into the arbitrary retained-big-label factor. -/

open Finset Filter
open scoped Classical Topology

namespace Bounty

theorem eventually_realized_candidate_mixed_promotion_energy_le
    {q vs scale : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hvs : 0 < vs) (hscale : 0 < scale)
    (ell : ℕ) (C₂ : ℝ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (S G : Type) [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
        (Ps : S → Finset ℕ) [∀ p : PhysicalPrime Ps, NeZero p.2.val]
        (P : G → Finset ℕ) [∀ g (p : P g), NeZero p.val]
        (_R : CandidateMixedPoolRealization scale L Ps P),
      ∀ J B : ℕ,
      ∀ M : G → ℕ,
      ∀ shared : ∀ g, Finset (Fin (M g)),
      ∀ D_B : SharedActiveLabels ((fun g => ↥(P g))) shared → ℕ,
      ∀ k : ℤ, k ≠ 0 → (k.natAbs : ℝ) ≤ L ^ C₂ →
      ∀ Vs : S → ℝ, (∀ g, vs ≤ Vs g) →
      ∀ μ : ∀ g, (fun g => ↥(P g)) g → ℝ, ∀ ρ : ℝ,
      ∀ V : G → ℝ,
      ∀ v vmin vmax : ℝ, 0 < ρ → ρ < 1 → 1 < v → 0 < vmin →
      (∀ g, vmin ≤ V g) → (∀ g, V g ≤ vmax) →
      (∀ g p, 0 ≤ μ g p) → (∀ g, ∑ p, μ g p ≤ 2) →
      ∀ T : ℕ, (∀ g, (shared g)ᶜ.card ≤ T) →
      ∀ Φ : ∀ s : PhysicalSmallBigState (Ps) J ell
        (ProductBoundedOrderedState ((fun g => ↥(P g)))
          (fun g => UnrestrictedResidueParticle ((fun g (p : P g) => p.val) g)) M B),
        PhysicalSmallBigEvent (PhysicalSmallBigFullEvent ((fun g (p : P g) => p.val)) shared B
          (fun d c _ => -(k * (D_B c * physicalSharedProduct d : ℕ)))
          (fun d c _ => (D_B c * physicalSharedProduct d : ℕ))) s → ℂ,
      ∀ H : ℝ, 0 ≤ H → (∀ s e, ‖Φ s e‖ ≤ H) →
      ∀ F : PhysicalSmallBigState (Ps) J ell
        (ProductBoundedOrderedState ((fun g => ↥(P g)))
          (fun g => UnrestrictedResidueParticle ((fun g (p : P g) => p.val) g)) M B) → ℂ,
      (∀ s, ProductMemorySymmetric (fun x => F (s, x))) →
      physicalSmallBigEnergy Vs (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g)))
        (physicalSmallBigAverage (fun s =>
          physicalSmallBigFullPhasedAction ((fun g (p : P g) => p.val)) shared B
            (fun d c _ => -(k * (D_B c * physicalSharedProduct d : ℕ)))
            (fun d c _ => (D_B c * physicalSharedProduct d : ℕ)) μ ρ V
            (fun c => k * D_B c) Vs q
            (fun y e => if ∃ g, (e.2.2 g).2.1.Nonempty then Φ y e else 0) F s)) ≤
      ((B : ℝ) / (((J + ell).choose ell) ^ (Fintype.card S) : ℕ)) *
        (H ^ 2 * (A ^ (2 * (Fintype.card S)) *
          unrestrictedEdgeEnergyBound ρ v vmin vmax T ^ (Fintype.card G))) *
        physicalSmallBigEnergy Vs (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g))) F := by
  obtain ⟨A, hA, hbound⟩ := exists_physical_small_big_uniform_promotion_energy_bound hq0 hq1 hvs ell
  refine ⟨A, hA, ?_⟩
  filter_upwards [eventually_realized_candidate_mixed_eligibility_probability_le hscale ell C₂] with L hL
  intro S G _ _ _ _ Ps _ P _ R J B M shared D_B k hk hkbound Vs hVs μ ρ V v vmin vmax
    hρ0 hρ1 hv hvmin hVlo hVhi hμ hmass T ht Φ H hH hΦ F hF
  exact hbound S G Ps P J B M shared D_B k Vs hVs μ ρ V v vmin vmax
    hρ0 hρ1 hv hvmin hVlo hVhi hμ hmass T ht Φ H hH hΦ
    ((B : ℝ) / (((J + ell).choose ell) ^ Fintype.card S : ℕ))
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (hL S G Ps P R J B M shared D_B k hk hkbound) F hF

end Bounty
end

section

/- Original proof: CandidateMixedStorageEnergy.lean. Generalized only to pool-preserving group realizations. -/

/- Candidate-prime arithmetic supplies reverse eligibility rarity for the
literal mixed storage operator with both small-slot averages. The small
measure is the original residue-valid measure, and big labels may repeat. -/

open Finset Filter
open scoped Classical Topology

namespace Bounty

theorem eventually_realized_candidate_mixed_storage_energy_le
    {q vs scale : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hvs : 0 < vs) (hscale : 0 < scale)
    (ell : ℕ) (C₂ : ℝ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (S G : Type) [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
        (Ps : S → Finset ℕ) [∀ p : PhysicalPrime Ps, NeZero p.2.val]
        (P : G → Finset ℕ) [∀ g (p : P g), NeZero p.val]
        (_R : CandidateMixedPoolRealization scale L Ps P),
      ∀ J B : ℕ,
      ∀ M : G → ℕ,
      ∀ shared : ∀ g, Finset (Fin (M g)),
      ∀ D_B : SharedActiveLabels ((fun g => ↥(P g))) shared → ℕ,
      ∀ k : ℤ, k ≠ 0 → (k.natAbs : ℝ) ≤ L ^ C₂ →
      ∀ Vs : S → ℝ, (∀ g, vs ≤ Vs g) →
      ∀ aux : PhysicalAuxLabels (Ps) (fun _ => (∅ : Finset (Fin J))),
      ∀ μ : ∀ g, (fun g => ↥(P g)) g → ℝ, ∀ ρ : ℝ,
      ∀ V : G → ℝ,
      ∀ v vmin vmax : ℝ, 0 < ρ → ρ < 1 → 1 < v → 0 < vmin →
      (∀ g, vmin ≤ V g) → (∀ g, V g ≤ vmax) →
      (∀ g p, 0 ≤ μ g p) → (∀ g, ∑ p, μ g p ≤ 2) →
      ∀ T : ℕ, (∀ g, (shared g)ᶜ.card ≤ T) →
      ∀ F : PhysicalSmallBigState (Ps) J ell
        (ProductBoundedOrderedState ((fun g => ↥(P g)))
          (fun g => UnrestrictedResidueParticle ((fun g (p : P g) => p.val) g)) M B) → ℂ,
      (∀ s, ProductMemorySymmetric (fun x => F (s, x))) →
      physicalSmallBigEnergy Vs (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g)))
        (physicalSmallBigAverage (physicalSmallBigStorageAction ((fun g (p : P g) => p.val)) shared B
          (fun d c _ => -(k * (D_B c * physicalSharedProduct d : ℕ)))
          (fun d c _ => (D_B c * physicalSharedProduct d : ℕ)) μ ρ V
          (fun c => k * D_B c) Vs q aux (physicalSmallBigAverage F))) ≤
      ((B : ℝ) / (((J + ell).choose ell) ^ (Fintype.card S) : ℕ)) *
        (A ^ (2 * (Fintype.card S)) *
          unrestrictedEdgeEnergyBound ρ v vmin vmax T ^ (Fintype.card G)) *
        physicalSmallBigEnergy Vs (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g))) F := by
  obtain ⟨A, hA, hbound⟩ := exists_physical_small_big_storage_sandwich_energy_bound hq0 hq1 hvs ell
  refine ⟨A, hA, ?_⟩
  filter_upwards [eventually_realized_candidate_mixed_reverse_eligibility_probability_le hscale ell C₂] with L hL
  intro S G _ dS _ dG Ps _ P _ R
  cases Subsingleton.elim dS (Classical.decEq S)
  cases Subsingleton.elim dG (Classical.decEq G)
  intro J B M shared D_B k hk hkbound Vs hVs aux μ ρ V v vmin vmax hρ0 hρ1 hv hvmin
    hVlo hVhi hμ hmass T ht F hF
  have h := hbound (S) (G)
    (Ps) ((fun g => ↥(P g))) ((fun g (p : P g) => p.val))
    J M shared B
    (fun d c _ => -(k * (D_B c * physicalSharedProduct d : ℕ)))
    (fun d c _ => (D_B c * physicalSharedProduct d : ℕ)) μ ρ V (fun c => k * D_B c)
    Vs hVs aux v vmin vmax hρ0 hρ1 hv hvmin hVlo hVhi hμ hmass T ht
    ((B : ℝ) / (((J + ell).choose ell) ^ (Fintype.card S) : ℕ))
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (by
      intro s hs
      have hh := hL S G Ps P R J B M shared D_B k hk hkbound s hs
      refine le_trans (le_of_eq ?_) hh
      exact uniform_indicator_probability_fintype_eq _ _ _) F hF
  exact h

end Bounty
end

section

/- Original proof: CandidateMixedDirtyEnergy.lean. Generalized only to pool-preserving group realizations. -/

/- The full candidate mixed dirty estimate, with the genuine small-state
measure, arbitrary bounded endpoint coefficient, and both small-slot
averages. Actual promotion and storage bounds are discharged separately. -/

open Finset Filter
open scoped Classical Topology

namespace Bounty

theorem eventually_realized_candidate_mixed_dirty_energy_le
    {q vs scale : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hvs : 0 < vs) (hscale : 0 < scale)
    (ell : ℕ) (C₂ : ℝ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (S G : Type) [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
        (Ps : S → Finset ℕ) [∀ p : PhysicalPrime Ps, NeZero p.2.val]
        (P : G → Finset ℕ) [∀ g (p : P g), NeZero p.val]
        (_R : CandidateMixedPoolRealization scale L Ps P),
      ∀ J B : ℕ,
      ∀ M : G → ℕ,
      ∀ shared : ∀ g, Finset (Fin (M g)),
      ∀ D_B : SharedActiveLabels ((fun g => ↥(P g))) shared → ℕ,
      ∀ k : ℤ, k ≠ 0 → (k.natAbs : ℝ) ≤ L ^ C₂ →
      ∀ Vs : S → ℝ, (∀ g, vs ≤ Vs g) →
      ∀ μ : ∀ g, (fun g => ↥(P g)) g → ℝ, ∀ ρ : ℝ,
      ∀ V : G → ℝ,
      ∀ v vmin vmax : ℝ, 0 < ρ → ρ < 1 → 1 < v → 0 < vmin →
      (∀ g, vmin ≤ V g) → (∀ g, V g ≤ vmax) →
      (∀ g p, 0 ≤ μ g p) → (∀ g, ∑ p, μ g p ≤ 2) →
      ∀ T : ℕ, (∀ g, (shared g)ᶜ.card ≤ T) →
      ∀ Φ : ∀ s : PhysicalSmallBigState (Ps) J ell
        (ProductBoundedOrderedState ((fun g => ↥(P g)))
          (fun g => UnrestrictedResidueParticle ((fun g (p : P g) => p.val) g)) M B),
        PhysicalSmallBigEvent (PhysicalSmallBigFullEvent ((fun g (p : P g) => p.val)) shared B
          (fun d c _ => -(k * (D_B c * physicalSharedProduct d : ℕ)))
          (fun d c _ => (D_B c * physicalSharedProduct d : ℕ))) s → ℂ,
      (∀ s e, ‖Φ s e‖ ≤ 1) →
      ∀ F : PhysicalSmallBigState (Ps) J ell
        (ProductBoundedOrderedState ((fun g => ↥(P g)))
          (fun g => UnrestrictedResidueParticle ((fun g (p : P g) => p.val) g)) M B) → ℂ,
      (∀ s, ProductMemorySymmetric (fun x => F (s, x))) →
      physicalSmallBigEnergy Vs (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g)))
        (physicalSmallBigAverage (fun s =>
          physicalSmallBigFullPhasedAction ((fun g (p : P g) => p.val)) shared B
            (fun d c _ => -(k * (D_B c * physicalSharedProduct d : ℕ)))
            (fun d c _ => (D_B c * physicalSharedProduct d : ℕ)) μ ρ V
            (fun c => k * D_B c) Vs q
            (fun y e => if ¬ (∀ g, (e.2.2 g).1 = ∅ ∧ (e.2.2 g).2.1 = ∅) then Φ y e else 0)
            (physicalSmallBigAverage F) s)) ≤
      4 * ((B : ℝ) / (((J + ell).choose ell) ^ (Fintype.card S) : ℕ)) *
        (A ^ (2 * (Fintype.card S)) *
          unrestrictedEdgeEnergyBound ρ v vmin vmax T ^ (Fintype.card G)) *
        physicalSmallBigEnergy Vs (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g))) F := by
  obtain ⟨Ap, hAp, hp⟩ := eventually_realized_candidate_mixed_promotion_energy_le hq0 hq1 hvs hscale ell C₂
  obtain ⟨As, hAs, hs⟩ := eventually_realized_candidate_mixed_storage_energy_le hq0 hq1 hvs hscale ell C₂
  refine ⟨max Ap As, hAp.trans (le_max_left _ _), ?_⟩
  filter_upwards [hp, hs] with L hpL hsL
  intro S G _ _ _ _ Ps _ P _ R J B M shared D_B k hk hkbound Vs hVs μ ρ V v vmin vmax hρ0 hρ1 hv hvmin hVlo hVhi
    hμ hmass T ht Φ hΦ F hF
  let W : ProductBoundedOrderedState ((fun g => ↥(P g)))
      (fun g => UnrestrictedResidueParticle ((fun g (p : P g) => p.val) g)) M B → ℝ :=
    productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g))
  let env := complexNormEnvelope (physicalSmallBigAverage F)
  let δ : ℝ := (B : ℝ) / (((J + ell).choose ell) ^ (Fintype.card S) : ℕ)
  let C : ℝ := unrestrictedEdgeEnergyBound ρ v vmin vmax T ^ (Fintype.card G)
  let K : ℝ := (max Ap As) ^ (2 * (Fintype.card S)) * C
  let aux : PhysicalAuxLabels (Ps) (fun _ => (∅ : Finset (Fin J))) :=
    fun _ j => False.elim ((Finset.notMem_empty j.val) j.property)
  have hVs' : ∀ s, 0 < Vs s := fun s => hvs.trans_le (hVs s)
  have hW : ∀ x, 0 ≤ W x := productMemoryWeight_nonneg μ _ hμ (fun g z => hμ g z.1)
  have hδ : 0 ≤ δ := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hC : 0 ≤ C := pow_nonneg (unrestrictedEdgeEnergyBound_nonneg ρ v vmin vmax T) _
  have hmax : 0 ≤ max Ap As := (zero_le_one.trans hAp).trans (le_max_left _ _)
  have henv : ∀ s, ProductMemorySymmetric (fun x => env (s, x)) := by
    intro s x g τ
    exact congrArg (fun z : ℂ => (‖z‖ : ℂ))
      (physical_small_big_average_memory_symmetric F hF s x g τ)
  have henvfix : physicalSmallBigAverage env = env := physical_small_big_average_envelope_fixed F
  have henvE : physicalSmallBigEnergy Vs W env ≤ physicalSmallBigEnergy Vs W F :=
    physical_small_big_average_envelope_energy_le Vs hVs' W hW F
  have henv0 : 0 ≤ physicalSmallBigEnergy Vs W env := by
    rw [← physical_small_big_energy_eq]
    exact sum_nonneg fun s _ => mul_nonneg
      (physical_small_big_measure_nonneg Vs hVs' W hW s) (sq_nonneg _)
  have upgrade (a : ℝ) (ha : 0 ≤ a) (haA : a ≤ max Ap As)
      (out : PhysicalSmallBigState (Ps) J ell
        (ProductBoundedOrderedState ((fun g => ↥(P g)))
          (fun g => UnrestrictedResidueParticle ((fun g (p : P g) => p.val) g)) M B) → ℂ)
      (hout : physicalSmallBigEnergy Vs W out ≤
        δ * (a ^ (2 * (Fintype.card S)) * C) * physicalSmallBigEnergy Vs W env) :
      physicalSmallBigEnergy Vs W out ≤ δ * K * physicalSmallBigEnergy Vs W F := by
    apply hout.trans
    refine mul_le_mul ?_ henvE henv0 ?_
    · exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha haA _) hC) hδ
    · exact mul_nonneg hδ (mul_nonneg (pow_nonneg hmax _) hC)
  have hprom := hpL S G Ps P R J B M shared D_B k hk hkbound Vs hVs μ ρ V v vmin vmax
    hρ0 hρ1 hv hvmin hVlo hVhi hμ hmass T ht (fun _ _ => 1) 1 zero_le_one
    (by intros; simp only [norm_one, le_refl]) env henv
  simp only [one_pow, one_mul] at hprom
  have hstore := hsL S G Ps P R J B M shared D_B k hk hkbound Vs hVs aux μ ρ V v vmin vmax
    hρ0 hρ1 hv hvmin hVlo hVhi hμ hmass T ht env henv
  rw [henvfix] at hstore
  exact physical_small_big_dirty_energy_of_components Vs W hVs' hW F _ _ _ δ K
    (physical_small_big_averaged_dirty_domination ((fun g (p : P g) => p.val)) shared B
      (fun d c _ => -(k * (D_B c * physicalSharedProduct d : ℕ)))
      (fun d c _ => (D_B c * physicalSharedProduct d : ℕ)) μ ρ V
      (fun c => k * D_B c) Vs q aux hVs' hμ hρ0.le (fun g => (hvmin.trans_le (hVlo g)).le)
      Φ hΦ (physicalSmallBigAverage F))
    (upgrade Ap (zero_le_one.trans hAp) (le_max_left _ _) _ hprom)
    (upgrade As (zero_le_one.trans hAs) (le_max_right _ _) _ hstore)

end Bounty
end

section

/- Original proof: CandidateMixedAuxiliaryDirtyEnergy.lean. Generalized only to pool-preserving group realizations. -/

/- Independent auxiliary subprobability averaging of the actual candidate
mixed dirty operator. Both small-slot projections and all event masks remain
literal, with no per-auxiliary norm hypothesis in the conclusion. -/

open Finset Filter
open scoped Classical Topology

namespace Bounty

theorem eventually_realized_candidate_mixed_auxiliary_dirty_energy_le
    {q vs scale : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hvs : 0 < vs) (hscale : 0 < scale)
    (ell : ℕ) (C₂ : ℝ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (S G : Type) [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
        (Ps : S → Finset ℕ) [∀ p : PhysicalPrime Ps, NeZero p.2.val]
        (P : G → Finset ℕ) [∀ g (p : P g), NeZero p.val]
        (_R : CandidateMixedPoolRealization scale L Ps P),
      ∀ J B : ℕ,
      ∀ M : G → ℕ,
      ∀ shared : ∀ g, Finset (Fin (M g)),
      ∀ (Q : Type) [Fintype Q],
      ∀ π : Q → ℝ, (∀ a, 0 ≤ π a) → (∑ a, π a ≤ 1) →
      ∀ D_B : Q → SharedActiveLabels ((fun g => ↥(P g))) shared → ℕ,
      ∀ k : ℤ, k ≠ 0 → (k.natAbs : ℝ) ≤ L ^ C₂ →
      ∀ Vs : S → ℝ, (∀ g, vs ≤ Vs g) →
      ∀ μ : ∀ g, (fun g => ↥(P g)) g → ℝ, ∀ ρ : ℝ,
      ∀ V : G → ℝ,
      ∀ v vmin vmax : ℝ, 0 < ρ → ρ < 1 → 1 < v → 0 < vmin →
      (∀ g, vmin ≤ V g) → (∀ g, V g ≤ vmax) →
      (∀ g p, 0 ≤ μ g p) → (∀ g, ∑ p, μ g p ≤ 2) →
      ∀ T : ℕ, (∀ g, (shared g)ᶜ.card ≤ T) →
      ∀ Φ : ∀ a : Q, ∀ s : PhysicalSmallBigState (Ps) J ell
        (ProductBoundedOrderedState ((fun g => ↥(P g)))
          (fun g => UnrestrictedResidueParticle ((fun g (p : P g) => p.val) g)) M B),
        PhysicalSmallBigEvent (PhysicalSmallBigFullEvent ((fun g (p : P g) => p.val)) shared B
          (fun d c _ => -(k * (D_B a c * physicalSharedProduct d : ℕ)))
          (fun d c _ => (D_B a c * physicalSharedProduct d : ℕ))) s → ℂ,
      (∀ a s e, ‖Φ a s e‖ ≤ 1) →
      ∀ F : PhysicalSmallBigState (Ps) J ell
        (ProductBoundedOrderedState ((fun g => ↥(P g)))
          (fun g => UnrestrictedResidueParticle ((fun g (p : P g) => p.val) g)) M B) → ℂ,
      (∀ s, ProductMemorySymmetric (fun x => F (s, x))) →
      physicalSmallBigEnergy Vs (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g)))
        (physicalSmallBigAverage (fun s => ∑ a, (π a : ℂ) *
          physicalSmallBigFullPhasedAction ((fun g (p : P g) => p.val)) shared B
            (fun d c _ => -(k * (D_B a c * physicalSharedProduct d : ℕ)))
            (fun d c _ => (D_B a c * physicalSharedProduct d : ℕ)) μ ρ V
            (fun c => k * D_B a c) Vs q
            (fun y e => if ¬ (∀ g, (e.2.2 g).1 = ∅ ∧ (e.2.2 g).2.1 = ∅) then Φ a y e else 0)
            (physicalSmallBigAverage F) s)) ≤
      4 * ((B : ℝ) / (((J + ell).choose ell) ^ (Fintype.card S) : ℕ)) *
        (A ^ (2 * (Fintype.card S)) *
          unrestrictedEdgeEnergyBound ρ v vmin vmax T ^ (Fintype.card G)) *
        physicalSmallBigEnergy Vs (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g))) F := by
  obtain ⟨A, hA, hbound⟩ := eventually_realized_candidate_mixed_dirty_energy_le hq0 hq1 hvs hscale ell C₂
  refine ⟨A, hA, ?_⟩
  filter_upwards [hbound] with L hL
  intro S G _ _ _ _ Ps _ P _ R J B M shared Q _ π hπ hπmass D_B k hk hkbound Vs hVs μ ρ V v vmin vmax
    hρ0 hρ1 hv hvmin hVlo hVhi hμ hmass T ht Φ hΦ F hF
  rw [physical_small_big_average_weighted_sum]
  apply physical_small_big_auxiliary_energy_bound Vs (fun s => hvs.trans_le (hVs s))
    (productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g)))
    (productMemoryWeight_nonneg μ _ hμ (fun g z => hμ g z.1)) π hπ hπmass _ F _
  · exact mul_nonneg (mul_nonneg (by norm_num) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      (mul_nonneg (pow_nonneg (zero_le_one.trans hA) _)
        (pow_nonneg (unrestrictedEdgeEnergyBound_nonneg ρ v vmin vmax T) _))
  · intro a
    exact hL S G Ps P R J B M shared (D_B a) k hk hkbound Vs hVs μ ρ V v vmin vmax
      hρ0 hρ1 hv hvmin hVlo hVhi hμ hmass T ht (Φ a) (hΦ a) F hF

end Bounty
end

section

/- Original proof: CandidatePhysicalMixedDirtyEnergy.lean. Generalized only to pool-preserving group realizations. -/

/- The candidate mixed dirty estimate with the original physical auxiliary
law, concrete mixed displacement and divisor, and tilted physical birth law.
Both small-slot projections, endpoint phases, and memory cutoffs are retained. -/

open Finset Filter
open scoped Classical Topology

namespace Bounty

theorem eventually_realized_candidate_physical_mixed_dirty_energy_le
    {q vs scale : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hvs : 0 < vs) (hscale : 0 < scale)
    (ell : ℕ) (C₂ : ℝ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (S G : Type) [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
        (Ps : S → Finset ℕ) [∀ p : PhysicalPrime Ps, NeZero p.2.val]
        (P : G → Finset ℕ) [∀ g (p : P g), NeZero p.val]
        (_R : CandidateMixedPoolRealization scale L Ps P),
      ∀ J B : ℕ,
      ∀ C : G → Finset (Fin J),
      ∀ k : ℤ, k ≠ 0 → (k.natAbs : ℝ) ≤ L ^ C₂ →
      ∀ Vs : S → ℝ, (∀ g, vs ≤ Vs g) →
      ∀ V : G → ℝ,
      ∀ baseline : ∀ g, (fun g => ↥(P g)) g → ℝ,
      ∀ ρ v vmin vmax : ℝ, 0 < ρ → ρ < 1 → 1 < v → 0 < vmin →
      (∀ g, vmin ≤ V g) → (∀ g, V g ≤ vmax) →
      (∀ g : G, ∑ p ∈ P g, 1 / (p : ℝ) = V g) →
      (∀ g p, 1 / 2 ≤ baseline g p ∧ baseline g p ≤ 1) →
      ∀ T : ℕ, (∀ g, ell + (C g).card ≤ T) →
      ∀ Φ : ∀ a : PhysicalAuxLabels
        (P) C,
        ∀ s : PhysicalSmallBigState (Ps) J ell
          (ProductBoundedOrderedState ((fun g => ↥(P g)))
            (fun g => UnrestrictedResidueParticle ((fun g (p : P g) => p.val) g))
            (fun _ => J + ell) B),
        PhysicalSmallBigEvent (PhysicalSmallBigFullEvent ((fun g (p : P g) => p.val))
          (fun g => physicalFullSharedIndices (ell := ell) (C g)) B
          (fun d c g => physicalMixedEdgeDelta C k d c a g)
          (fun d c g => physicalMixedEdgeD C d c a g)) s → ℂ,
      (∀ a s e, ‖Φ a s e‖ ≤ 1) →
      ∀ F : PhysicalSmallBigState (Ps) J ell
        (ProductBoundedOrderedState ((fun g => ↥(P g)))
          (fun g => UnrestrictedResidueParticle ((fun g (p : P g) => p.val) g))
          (fun _ => J + ell) B) → ℂ,
      (∀ s, ProductMemorySymmetric (fun x => F (s, x))) →
      physicalSmallBigEnergy Vs
        (productMemoryWeight (P := (fun g => ↥(P g)))
          (Z := fun g => UnrestrictedResidueParticle ((fun g (p : P g) => p.val) g))
          (t := fun _ => J + ell) (B := B) (fun g => tiltedPhysicalBirthLaw (P := P) V g (baseline g))
          (fun g => unrestrictedResidueWeight (tiltedPhysicalBirthLaw (P := P) V g (baseline g))))
        (physicalSmallBigAverage (fun s => ∑ a, (physicalAuxMass V C a : ℂ) *
          physicalSmallBigFullPhasedAction ((fun g (p : P g) => p.val))
            (fun g => physicalFullSharedIndices (ell := ell) (C g)) B
            (fun d c g => physicalMixedEdgeDelta C k d c a g)
            (fun d c g => physicalMixedEdgeD C d c a g)
            (fun g => tiltedPhysicalBirthLaw (P := P) V g (baseline g)) ρ V
            (fun c => physicalMixedBigStep C k c a) Vs q
            (fun y e => if ¬ (∀ g, (e.2.2 g).1 = ∅ ∧ (e.2.2 g).2.1 = ∅) then Φ a y e else 0)
            (physicalSmallBigAverage F) s)) ≤
      4 * ((B : ℝ) / (((J + ell).choose ell) ^ (Fintype.card S) : ℕ)) *
        (A ^ (2 * (Fintype.card S)) *
          unrestrictedEdgeEnergyBound ρ v vmin vmax T ^ (Fintype.card G)) *
        physicalSmallBigEnergy Vs
          (productMemoryWeight (P := (fun g => ↥(P g)))
          (Z := fun g => UnrestrictedResidueParticle ((fun g (p : P g) => p.val) g))
          (t := fun _ => J + ell) (B := B) (fun g => tiltedPhysicalBirthLaw (P := P) V g (baseline g))
            (fun g => unrestrictedResidueWeight (tiltedPhysicalBirthLaw (P := P) V g (baseline g)))) F := by
  obtain ⟨A, hA, hbound⟩ :=
    eventually_realized_candidate_mixed_auxiliary_dirty_energy_le hq0 hq1 hvs hscale ell C₂
  refine ⟨A, hA, ?_⟩
  filter_upwards [hbound] with L hL
  intro S G _ _ _ _ Ps _ P _ R J B C k hk hkbound Vs hVs V baseline ρ v vmin vmax hρ0 hρ1 hv hvmin hVlo hVhi hMass hbaseline T ht
  have hV : ∀ g, 0 < V g := fun g => hvmin.trans_le (hVlo g)
  have hμ : ∀ g p, 0 ≤ tiltedPhysicalBirthLaw (P := P) V g (baseline g) p := by
    intro g p
    exact tiltedPhysicalBirthLaw_nonneg (P := P) V g (baseline g) (hV g).le
      (fun p => (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (hbaseline g p).1) p
  have hmass : ∀ g, ∑ p, tiltedPhysicalBirthLaw (P := P) V g (baseline g) p ≤ 2 := fun g =>
    (tiltedPhysicalBirthLaw_sum_bounds (P := P) V g (baseline g) (hV g) (hMass g) (hbaseline g)).2
  have hdelta : physicalMixedEdgeDelta (Ps := Ps)
      (P := P) (ell := ell) C k =
      fun d c a _ => -(k * (physicalFullSharedD C c a * physicalSharedProduct d : ℕ)) := by
    funext d c a g
    exact physical_mixed_edge_delta_big_first C k d c a g
  have hdivisor : physicalMixedEdgeD (Ps := Ps)
      (P := P) (ell := ell) C =
      fun d c a _ => ((physicalFullSharedD C c a * physicalSharedProduct d : ℕ) : ℤ) := by
    funext d c a g
    exact physical_mixed_edge_D_big_first C d c a g
  rw [hdelta, hdivisor]
  simp only [physicalMixedBigStep]
  exact hL S G Ps P R J B (fun _ => J + ell) (fun g => physicalFullSharedIndices (ell := ell) (C g))
    (PhysicalAuxLabels (P) C)
    (physicalAuxMass V C) (physical_aux_mass_nonneg V C (fun g => (hV g).le))
    (physical_aux_mass_sum V C hV hMass).le (fun a c => physicalFullSharedD C c a)
    k hk hkbound Vs hVs (fun g => tiltedPhysicalBirthLaw (P := P) V g (baseline g)) ρ V
    v vmin vmax hρ0 hρ1 hv hvmin hVlo hVhi hμ hmass T
    (fun g => by simpa only [physical_full_unshared_indices_card] using ht g)

end Bounty
end

section

/- The actual candidate dirty row in the same two-sided joint projection
as the signed prime family. No auxiliary or local norm premise remains. -/

open Finset Filter
open scoped Classical Topology
namespace Bounty

theorem eventually_realized_candidate_physical_mixed_dirty_projected_norm_le
    {q vs scale : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hvs : 0 < vs) (hscale : 0 < scale)
    (ell : ℕ) (C₂ : ℝ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (S G : Type) [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
        (Ps : S → Finset ℕ) [∀ p : PhysicalPrime Ps, NeZero p.2.val]
        (P : G → Finset ℕ) [∀ g (p : P g), NeZero p.val]
        (_R : CandidateMixedPoolRealization scale L Ps P),
      ∀ J B : ℕ,
      ∀ (C : G → Finset (Fin J)) (k : ℤ),
      k ≠ 0 → (k.natAbs : ℝ) ≤ L ^ C₂ →
      ∀ Vs : S → ℝ, (∀ g, vs ≤ Vs g) →
      ∀ (V : G → ℝ)
        (baseline : ∀ g, P g → ℝ) (ρ v vmin vmax : ℝ),
      0 < ρ → ρ < 1 → 1 < v → 0 < vmin →
      (∀ g, vmin ≤ V g) → (∀ g, V g ≤ vmax) →
      (∀ g : G, ∑ p ∈ P g, 1 / (p : ℝ) = V g) →
      (∀ g p, 1 / 2 ≤ baseline g p ∧ baseline g p ≤ 1) →
      ∀ T : ℕ, (∀ g, ell + (C g).card ≤ T) →
      ∀ (initial : ∀ g, Finset (P g))
        (Ψ : ∀ a (s : PhysicalSmallBigState Ps J ell
          (CleanFullMemoryState P J ell B)),
          PhysicalMixedCoefficientEvent C k a s → ℂ),
      (∀ a s e, ‖Ψ a s e‖ ≤ 1) →
      ∀ f : PhysicalSmallBigState Ps J ell
        (CleanFullMemoryState P J ell B) → ℂ,
      (∀ s, ProductMemorySymmetric (fun x => f (s,x))) →
      let μ := fun g => tiltedPhysicalBirthLaw
        (P := P) V g (baseline g)
      let W := productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g))
      cleanActiveNorm (physicalSmallBigMeasure Vs W)
        (physicalSmallBigJointAverage (physicalMixedCoefficientAction C k V baseline ρ Vs q initial
          (physicalMixedDirtyPhase C k Ψ) (physicalSmallBigJointAverage f))) ≤
      2 * Real.sqrt ((B : ℝ) / (((J + ell).choose ell) ^ Fintype.card S : ℕ)) *
        A ^ Fintype.card S *
        Real.sqrt (unrestrictedEdgeEnergyBound ρ v vmin vmax T ^ Fintype.card G) *
        cleanActiveNorm (physicalSmallBigMeasure Vs W) f := by
  obtain ⟨A, hA, hbound⟩ := eventually_realized_candidate_physical_mixed_dirty_energy_le hq0 hq1 hvs hscale ell C₂
  refine ⟨A, hA, ?_⟩
  filter_upwards [hbound] with L hL
  intro S G _ dS _ dG Ps _ P _ R
  cases Subsingleton.elim dS (Classical.decEq S)
  cases Subsingleton.elim dG (Classical.decEq G)
  intro J B C k hk hkbound Vs hVs V baseline ρ v vmin vmax hρ0 hρ1 hv hvmin hVlo hVhi
    hMass hbaseline T ht initial Ψ hΨ f hf μ W
  have hVs0 : ∀ g, 0 < Vs g := fun g => hvs.trans_le (hVs g)
  have hV : ∀ g, 0 < V g := fun g => hvmin.trans_le (hVlo g)
  have hμ : ∀ g p, 0 ≤ μ g p := fun g p =>
    tiltedPhysicalBirthLaw_nonneg (P := P) V g (baseline g) (hV g).le
      (fun p => (by norm_num : (0 : ℝ) ≤ 1/2).trans (hbaseline g p).1) p
  let fb := physicalSmallBigBigAverage f
  have hfb : ∀ s, ProductMemorySymmetric (fun x => fb (s,x)) :=
    fun s => fullActiveAverage_symmetric (fun x => f (s,x)) (hf s)
  let Φ := fun a s (e : PhysicalMixedCoefficientEvent C k a s) =>
    if ∀ g i, (e.2.2 g).2.2.2 i ∉ initial g then Ψ a s e else 0
  have hΦ : ∀ a s e, ‖Φ a s e‖ ≤ 1 := by
    intro a s e
    dsimp only [Φ]
    split_ifs
    · exact hΨ a s e
    · simp only [norm_zero, zero_le_one]
  have hc := hL S G Ps P R J B C k hk hkbound Vs hVs V baseline ρ v vmin vmax
    hρ0 hρ1 hv hvmin hVlo hVhi hMass hbaseline T ht Φ hΦ fb hfb
  let u := physicalMixedCoefficientAction C k V baseline ρ Vs q initial
    (physicalMixedDirtyPhase C k Ψ) (physicalSmallBigJointAverage f)
  have he : physicalSmallBigEnergy Vs W (physicalSmallBigAverage u) ≤
      4 * ((B : ℝ) / (((J + ell).choose ell) ^ Fintype.card S : ℕ)) *
        (A ^ (2 * Fintype.card S) *
          unrestrictedEdgeEnergyBound ρ v vmin vmax T ^ Fintype.card G) *
        physicalSmallBigEnergy Vs W fb := by
    dsimp only [u]
    rw [physical_mixed_dirty_coefficient_action_eq]
    exact hc
  have hin : physicalSmallBigEnergy Vs W fb ≤ physicalSmallBigEnergy Vs W f := by
    convert physical_small_big_big_average_energy_le Vs hVs0 μ
      (fun g => unrestrictedResidueWeight (μ g)) hμ (fun g z => hμ g z.1) f using 1
  have hout : physicalSmallBigEnergy Vs W (physicalSmallBigJointAverage u) ≤
      physicalSmallBigEnergy Vs W (physicalSmallBigAverage u) := by
    rw [physical_small_big_joint_average_eq_big_small]
    convert physical_small_big_big_average_energy_le Vs hVs0 μ
      (fun g => unrestrictedResidueWeight (μ g)) hμ (fun g z => hμ g z.1)
      (physicalSmallBigAverage u) using 1
  let δ : ℝ := (B : ℝ) / (((J + ell).choose ell) ^ Fintype.card S : ℕ)
  let K : ℝ := unrestrictedEdgeEnergyBound ρ v vmin vmax T ^ Fintype.card G
  have hδ : 0 ≤ δ := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hK : 0 ≤ K := pow_nonneg (unrestrictedEdgeEnergyBound_nonneg ρ v vmin vmax T) _
  have hcoef : 0 ≤ 4 * δ * (A ^ (2 * Fintype.card S) * K) :=
    mul_nonneg (mul_nonneg (by norm_num) hδ)
      (mul_nonneg (pow_nonneg (zero_le_one.trans hA) _) hK)
  have henergy := hout.trans (he.trans (mul_le_mul_of_nonneg_left hin hcoef))
  have hp : (A ^ Fintype.card S) ^ 2 =
      A ^ (2 * Fintype.card S) := by rw [← pow_mul, Nat.mul_comm]
  have hcoefeq : (2 * Real.sqrt δ * A ^ Fintype.card S) ^ 2 * K =
      4 * δ * (A ^ (2 * Fintype.card S) * K) := by
    rw [mul_pow, mul_pow, hp, Real.sq_sqrt hδ]
    ring
  apply physical_small_big_norm_le_of_energy Vs W
    (2 * Real.sqrt δ * A ^ Fintype.card S) K
    (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (pow_nonneg (zero_le_one.trans hA) _)) hK f _
  rw [hcoefeq]
  convert henergy using 1

end Bounty
end

section

/- The actual signed prime-family dirty contribution, with both small and
big endpoint projections, the original auxiliary law, and a fixed initial
fresh-birth gate. The coefficient budget is proved from the prime family. -/

open Finset Filter
open scoped Classical Topology
namespace Bounty

theorem eventually_realized_candidate_physical_mixed_prime_dirty_norm_le
    {q vs scale : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hvs : 0 < vs) (hscale : 0 < scale)
    (ell : ℕ) (C₂ : ℝ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (S G : Type) [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
        (Ps : S → Finset ℕ) [∀ p : PhysicalPrime Ps, NeZero p.2.val]
        (P : G → Finset ℕ) [∀ g (p : P g), NeZero p.val]
        (_R : CandidateMixedPoolRealization scale L Ps P),
      ∀ J B m : ℕ,
      ∀ (probes : G → Finset (Fin J))
        (r t : Finset G) (hrt : Disjoint r t),
      (∀ g, (probes g).card ≤ m) →
      ∀ (Q : ℕ) (h ξ : ℝ), 0 < ξ → ∀ k : ℤ, k ≠ 0 → (k.natAbs : ℝ) ≤ L ^ C₂ →
      ∀ Vs : S → ℝ, (∀ g, vs ≤ Vs g) →
      ∀ (V : G → ℝ)
        (baseline : ∀ g, P g → ℝ) (ρ v vmin vmax : ℝ),
      0 < ρ → ρ < 1 → 1 < v → 0 < vmin →
      (∀ g, vmin ≤ V g) → (∀ g, V g ≤ vmax) →
      (∀ g : G, ∑ p ∈ P g, 1 / (p : ℝ) = V g) →
      (∀ g p, 1 / 2 ≤ baseline g p ∧ baseline g p ≤ 1) →
      ∀ (initial : ∀ g, Finset (P g))
        (φ : ∀ i : RepeatedBigPrimePatternIndex (ell := ell) probes r t,
          ∀ a (s : PhysicalSmallBigState Ps J ell
            (CleanFullMemoryState P J ell B)),
            PhysicalMixedCoefficientEvent (repeatedBigPrimePatternCut probes r t i) k a s → ℂ),
      (∀ i a s e, ‖φ i a s e‖ ≤ 1) →
      ∀ f : PhysicalSmallBigState Ps J ell
        (CleanFullMemoryState P J ell B) → ℂ,
      (∀ s, ProductMemorySymmetric (fun x => f (s,x))) →
      let μ := fun g => tiltedPhysicalBirthLaw
        (P := P) V g (baseline g)
      let W := productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g))
      cleanActiveNorm (physicalSmallBigMeasure Vs W)
        (physicalSmallBigJointAverage (physicalMixedPrimePatternAction V baseline ρ Vs q
          probes r t hrt Q h ξ k initial
          (fun i => physicalMixedDirtyPhase (repeatedBigPrimePatternCut probes r t i) k (φ i))
          (physicalSmallBigJointAverage f))) ≤
      repeatedBigFamilyEnvelope (Fintype.card G) m Q ξ *
        (2 * Real.sqrt ((B : ℝ) / (((J + ell).choose ell) ^ Fintype.card S : ℕ)) *
          A ^ Fintype.card S *
          Real.sqrt (unrestrictedEdgeEnergyBound ρ v vmin vmax (ell + m) ^ Fintype.card G)) *
        cleanActiveNorm (physicalSmallBigMeasure Vs W) f := by
  obtain ⟨A, hA, hbound⟩ := eventually_realized_candidate_physical_mixed_dirty_projected_norm_le
    hq0 hq1 hvs hscale ell C₂
  refine ⟨A, hA, ?_⟩
  filter_upwards [hbound] with L hL
  intro S G _ dS _ dG Ps _ P _ R
  cases Subsingleton.elim dS (Classical.decEq S)
  cases Subsingleton.elim dG (Classical.decEq G)
  intro J B m probes r t hrt hp Q h ξ hξ k hk hkbound Vs hVs V baseline ρ v vmin vmax
    hρ0 hρ1 hv hvmin hVlo hVhi hMass hbaseline initial φ hφ f hf μ W
  have hμ : ∀ g p, 0 ≤ μ g p := fun g p =>
    tiltedPhysicalBirthLaw_nonneg (P := P) V g (baseline g) (hvmin.trans_le (hVlo g)).le
      (fun p => (by norm_num : (0 : ℝ) ≤ 1/2).trans (hbaseline g p).1) p
  have hW : ∀ x, 0 ≤ W x := productMemoryWeight_nonneg μ _ hμ (fun g z => hμ g z.1)
  have hw := physical_small_big_measure_nonneg (P := Ps)
    (J := J) (ell := ell) Vs (fun s => hvs.trans_le (hVs s)) W hW
  let cost := 2 * Real.sqrt ((B : ℝ) / (((J + ell).choose ell) ^ Fintype.card S : ℕ)) *
    A ^ Fintype.card S *
    Real.sqrt (unrestrictedEdgeEnergyBound ρ v vmin vmax (ell + m) ^ Fintype.card G)
  have hcost : 0 ≤ cost := mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (pow_nonneg (zero_le_one.trans hA) _))
    (Real.sqrt_nonneg _)
  have hfinal := physical_mixed_prime_dirty_norm_of_rows V baseline ρ Vs q probes r t hrt hp
    Q h ξ hξ k initial φ hφ (physicalSmallBigMeasure Vs W) hw cost hcost f
    (fun C hC Ψ hΨ => hL S G Ps P R J B C k hk hkbound Vs hVs V baseline ρ v vmin vmax
      hρ0 hρ1 hv hvmin hVlo hVhi hMass hbaseline (ell+m)
      (fun g => Nat.add_le_add_left (hC g) ell) initial Ψ hΨ f hf)
  exact hfinal

end Bounty
end

section

/- The actual candidate prime family, with its original fresh-birth gate,
auxiliary law, and both full endpoint averages. The clean and dirty bounds
are evaluated in the same tilted mixed measure. The analytic input is the
proved actual zero-free theorem; no local operator bound is assumed. -/

open Finset Filter
open scoped Classical

namespace Bounty.WeakZeroFree

theorem actual_exists_realized_candidate_physical_mixed_full_norm_bound
    {qsmall vsmall scale : ℝ} (hq0 : 0 ≤ qsmall) (hq1 : qsmall < 1)
    (hvs : 0 < vsmall) (hscale : 0 < scale) (ell : ℕ) (C₂ : ℝ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀
    (c s z a v D ε E beta tau : ℝ)
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
    ∀ (S G : Type) [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
      (Ps : S → Finset ℕ) [∀ p : PhysicalPrime Ps, NeZero p.2.val]
      (P : G → Finset ℕ) [∀ g (p : P g), NeZero p.val]
      (_R : CandidateMixedPoolRealization scale L Ps P),
    ∀ V : G → ℝ,
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
    ∀ initial : ∀ g, Finset (P g), (∀ g, (initial g).card ≤ J + ell) →
    ∀ baseline : ∀ g, P g → ℝ,
    ∀ T Pmin : ℝ, 0 ≤ T → T ≤ L ^ tau → Real.exp (L ^ c) ≤ Pmin →
    (∀ g (p : P g), Pmin ≤ (p.val : ℝ)) →
    (∀ g (p : P g), baseline g p = 1 - T / (p.val : ℝ)) →
    (∀ g p, 1 / 2 ≤ baseline g p ∧ baseline g p ≤ 1) →
    ∀ (B : ℕ) (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L ^ C₂ →
    ∀ Vs : S → ℝ, (∀ g, vsmall ≤ Vs g) →
    ∀ ρ u vmax : ℝ, 0 < ρ → ρ < 1 → 1 < u → (∀ g, V g ≤ vmax) →
    ∀ f : PhysicalSmallBigState Ps J ell
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
      A ^ Fintype.card S *
        (L ^ (-E) + 2 * repeatedBigFamilyEnvelope (Fintype.card G) m Q ξ *
          Real.sqrt ((B : ℝ) / (((J + ell).choose ell) ^ Fintype.card S : ℕ)) *
          Real.sqrt (unrestrictedEdgeEnergyBound ρ u v vmax (ell + m) ^ Fintype.card G)) *
        cleanActiveNorm (physicalSmallBigMeasure Vs W) f := by
  obtain ⟨Ac, hAc, hclean⟩ := exists_physical_mixed_clean_prime_joint_norm_bound
    qsmall vsmall ell hq0 hq1 hvs
  obtain ⟨Ad, hAd, hdirty⟩ := eventually_realized_candidate_physical_mixed_prime_dirty_norm_le
    hq0 hq1 hvs hscale ell C₂
  refine ⟨max Ac Ad, hAc.trans (le_max_left _ _), ?_⟩
  intro c s z a v D ε E beta tau m J hc hs hz ha hv hD hε htau hell hml hgap hDgap κ s' A₀ q w x
  filter_upwards [hclean actual_zero_free c s z a v D ε E beta tau m J hc hs hz ha hv hD hε htau
      hell hml hgap hDgap, hdirty, eventually_gt_atTop (0 : ℝ)] with L hcl hdi hL
  intro Q h ξ S G _ dS _ dG Ps _ P _ R
  cases Subsingleton.elim dS (Classical.decEq S)
  cases Subsingleton.elim dG (Classical.decEq G)
  intro V hdisj hP hmass hV hlog hcard hband probes hp r t hrt hr ht ζ θ hζ
    initial hinitial baseline T Pmin hT hTmax hPmin hpmin hb hbaseline B k hk hkbound
    Vs hVs ρ u vmax hρ0 hρ1 hu hVhi f hf μ W
  have hμ : ∀ g p, 0 ≤ μ g p := fun g p => tiltedPhysicalBirthLaw_nonneg V g (baseline g)
    (hv.trans_le (hV g)).le (fun p => (by norm_num : (0 : ℝ) ≤ 1/2).trans (hbaseline g p).1) p
  have hW : ∀ y, 0 ≤ W y := productMemoryWeight_nonneg μ _ hμ (fun g z => hμ g z.1)
  have hVs0 : ∀ g, 0 < Vs g := fun g => hvs.trans_le (hVs g)
  have hξ : 0 < ξ := Real.rpow_pos_of_pos hL _
  have hc0 := hcl P V hdisj hP hmass hV hlog hcard hband probes hp r t hrt hr ht
    ζ θ hζ initial hinitial baseline T Pmin hT hTmax hPmin hpmin hb
    S Ps B k μ ρ hμ hρ0.le hρ1.le
    Vs hVs (fun _ => ∅) f hf
  have hd0 := hdi S G Ps P R J B m probes r t hrt (fun g => (hp g).le) Q h ξ hξ k hk hkbound
    Vs hVs V baseline ρ u v vmax hρ0 hρ1 hu hv hV hVhi hmass hbaseline initial
    (fun i => physicalMixedFullResidualPhase (repeatedBigPrimePatternCut probes r t i)
      ζ θ k cleanMixedSourceGate (cleanMixedTargetGate (fun _ => ∅)))
    (fun i a y e => physical_mixed_concrete_residual_norm_le _ ζ θ k (fun _ => ∅) a y e) f hf
  let C := repeatedBigPrimePatternCut (ell := ell) probes r t
  let kept := fun U : Finset (RepeatedBigFlatIndex G J ell) =>
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
  let δ := (B : ℝ) / (((J + ell).choose ell) ^ Fintype.card S : ℕ)
  let Ce := unrestrictedEdgeEnergyBound ρ u v vmax (ell + m) ^ Fintype.card G
  let H := repeatedBigFamilyEnvelope (Fintype.card G) m Q ξ
  have hc' : cleanActiveNorm (physicalSmallBigMeasure Vs W) clean ≤
      Ac ^ Fintype.card S * L ^ (-E) * cleanActiveNorm (physicalSmallBigMeasure Vs W) f := by
    convert hc0 using 1
    all_goals rfl
  have hd' : cleanActiveNorm (physicalSmallBigMeasure Vs W) dirty ≤
      H * (2 * Real.sqrt δ * Ad ^ Fintype.card S * Real.sqrt Ce) *
        cleanActiveNorm (physicalSmallBigMeasure Vs W) f := hd0
  have heq := physical_mixed_prime_projected_clean_dirty V baseline ρ Vs qsmall probes r t hrt
    Q h ξ ζ θ k initial cleanMixedSourceGate (cleanMixedTargetGate (fun _ => ∅)) f
  have hsum := physical_small_big_clean_rare_norm_le Vs W hVs0 hW f _ clean dirty heq _ _ hc' hd'
  have hcPow : Ac ^ Fintype.card S ≤ (max Ac Ad) ^ Fintype.card S :=
    pow_le_pow_left₀ (zero_le_one.trans hAc) (le_max_left _ _) _
  have hdPow : Ad ^ Fintype.card S ≤ (max Ac Ad) ^ Fintype.card S :=
    pow_le_pow_left₀ (zero_le_one.trans hAd) (le_max_right _ _) _
  have hH : 0 ≤ H := repeated_big_family_envelope_nonneg _ _ _ _
  have hnorm : 0 ≤ cleanActiveNorm (physicalSmallBigMeasure Vs W) f := Real.sqrt_nonneg _
  refine hsum.trans (mul_le_mul_of_nonneg_right ?_ hnorm)
  calc
    Ac ^ Fintype.card S * L ^ (-E) +
        H * (2 * Real.sqrt δ * Ad ^ Fintype.card S * Real.sqrt Ce) ≤
      (max Ac Ad) ^ Fintype.card S * L ^ (-E) +
        H * (2 * Real.sqrt δ * (max Ac Ad) ^ Fintype.card S * Real.sqrt Ce) :=
      add_le_add (mul_le_mul_of_nonneg_right hcPow (Real.rpow_nonneg hL.le _))
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdPow (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
          (Real.sqrt_nonneg _)) hH)
    _ = _ := by ring

end Bounty.WeakZeroFree
end

section

/- Original proof: ActualSignedPrimeFullNorm.lean. Same signed parity argument for realized candidate pools. -/

/- The actual candidate full norm bound for both chronological parities.
The ordinary analytic bound already includes the dirty contribution. -/

open Finset Filter
open scoped Topology BigOperators Classical

namespace Bounty.WeakZeroFree

theorem actual_exists_realized_candidate_physical_mixed_signed_full_norm_bound
    {qsmall vsmall scale : ℝ} (hq0 : 0 ≤ qsmall) (hq1 : qsmall < 1)
    (hvs : 0 < vsmall) (hscale : 0 < scale) (ell : ℕ) (C₂ : ℝ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀
    (c s z a v D ε E beta tau : ℝ)
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
    ∀ (S G : Type) [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
      (Ps : S → Finset ℕ) [∀ p : PhysicalPrime Ps, NeZero p.2.val]
      (P : G → Finset ℕ) [∀ g (p : P g), NeZero p.val]
      (_R : CandidateMixedPoolRealization scale L Ps P),
    ∀ V : G → ℝ,
    Pairwise (fun g h => Disjoint (P g) (P h)) →
    (∀ g p, p ∈ P g → p.Prime ∧ Q < p) →
    (∀ g, ∑ p ∈ P g, 1 / (p : ℝ) = V g) →
    (∀ g, v ≤ V g) →
    (∀ g p, p ∈ P g → Real.log p ≤ L ^ s) →
    (Fintype.card (G) : ℝ) ≤ a * Real.log L →
    (∀ g, ∃ a b : ℝ, P g = primeBand a b ∧ Real.exp (L ^ c) ≤ a ∧ 0 ≤ b) →
    ∀ probes : G → Finset (Fin J), (∀ g, (probes g).card = m) →
    ∀ r t : Finset (G), ∀ hrt : Disjoint r t,
    beta * Real.log L ≤ (r.card : ℝ) → beta * Real.log L ≤ (t.card : ℝ) →
    ∀ ζ θ : ℝ, |ζ| ≤ L ^ z →
    ∀ initial : ∀ g, Finset (P g), (∀ g, (initial g).card ≤ J + ell) →
    ∀ baseline : ∀ g, P g → ℝ,
    ∀ T Pmin : ℝ, 0 ≤ T → T ≤ L ^ tau → Real.exp (L ^ c) ≤ Pmin →
    (∀ g (p : P g), Pmin ≤ (p.val : ℝ)) →
    (∀ g (p : P g), baseline g p = 1 - T / (p.val : ℝ)) →
    (∀ g p, 1 / 2 ≤ baseline g p ∧ baseline g p ≤ 1) →
    ∀ (B time : ℕ) (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L ^ C₂ →
    ∀ Vs : S → ℝ, (∀ g, vsmall ≤ Vs g) →
    ∀ ρ u vmax : ℝ, 0 < ρ → ρ < 1 → 1 < u → (∀ g, V g ≤ vmax) →
    ∀ f : PhysicalSmallBigState (Ps) J ell
      (CleanFullMemoryState P J ell B) → ℂ,
    (∀ d, ProductMemorySymmetric (fun y => f (d,y))) →
    let μ := fun g => tiltedPhysicalBirthLaw V g (baseline g)
    let W := productMemoryWeight μ (fun g => unrestrictedResidueWeight (μ g))
    cleanActiveNorm (physicalSmallBigMeasure Vs W)
      (physicalSmallBigJointAverage (physicalMixedSignedPrimePatternAction V baseline ρ Vs qsmall
        probes r t hrt Q h ξ time k initial
        (fun i => physicalMixedFullResidualPhase (repeatedBigPrimePatternCut probes r t i)
          ζ θ k cleanMixedSourceGate (cleanMixedTargetGate (fun _ => ∅)))
        (physicalSmallBigJointAverage f))) ≤
      A ^ (Fintype.card S) *
        (L ^ (-E) + 2 * repeatedBigFamilyEnvelope (Fintype.card G) m Q ξ *
          Real.sqrt ((B : ℝ) / (((J + ell).choose ell) ^ (Fintype.card S) : ℕ)) *
          Real.sqrt (unrestrictedEdgeEnergyBound ρ u v vmax (ell + m) ^ (Fintype.card G))) *
        cleanActiveNorm (physicalSmallBigMeasure Vs W) f := by
  obtain ⟨A, hA, hbound⟩ :=
    actual_exists_realized_candidate_physical_mixed_full_norm_bound hq0 hq1 hvs hscale ell C₂
  refine ⟨A, hA, ?_⟩
  intro c s z a v D ε E beta tau m J hc hs hz ha hv hD hε htau hell hml hgap hDgap
    κ s' A₀ q w x
  filter_upwards [hbound c s z a v D ε E beta tau m J hc hs hz ha hv hD hε htau
    hell hml hgap hDgap] with L hL
  intro Q h ξ S G _ dS _ dG Ps _ P _ R
  cases Subsingleton.elim dS (Classical.decEq S)
  cases Subsingleton.elim dG (Classical.decEq G)
  intro V hdis hprime hmass hV hlog hcard hband probes hprobes
  have hbase := hL S G Ps P R V hdis hprime hmass hV hlog hcard hband probes hprobes
  intro r t hrt hr ht ζ θ hζ initial hinitial baseline T Pmin hT hTmax hPmin
    hPlow hbaseline hbaselineBounds B time k hk hkmax Vs hVs ρ u vmax hρ0 hρ1 hu hVhi
    f hf μ W
  by_cases htime : time % 2 = 0
  · have hb := hbase t r hrt.symm ht hr (-ζ) (-θ)
      (by simpa only [abs_neg] using hζ) initial hinitial baseline T Pmin
      hT hTmax hPmin hPlow hbaseline hbaselineBounds B k hk hkmax Vs hVs
      ρ u vmax hρ0 hρ1 hu hVhi (fun y => (starRingEnd ℂ) (f y))
      (fun d => product_memory_symmetric_conj (fun y => f (d,y)) (hf d))
    rw [physical_mixed_signed_prime_even_eq_conj_swapped (htime := htime),
      ← physical_small_big_joint_average_conj f,
      physical_small_big_joint_average_conj, clean_active_norm_conj]
    simpa only [clean_active_norm_conj] using hb
  · rw [physical_mixed_signed_prime_pattern_action_of_odd (htime := htime)]
    exact hbase r t hrt hr ht ζ θ hζ initial hinitial baseline T Pmin
      hT hTmax hPmin hPlow hbaseline hbaselineBounds B k hk hkmax Vs hVs
      ρ u vmax hρ0 hρ1 hu hVhi f hf

end Bounty.WeakZeroFree
end

section

/- The literal root enumeration of the candidate pools supplies the finite
pool realization needed by the mixed norm estimates. -/

open Finset
open scoped Classical
namespace Bounty

noncomputable def candidateRootBigGroups {N : ℕ} (scale L : ℝ)
    (E : Fin N ≃ ↥(candidatePIndices scale L)) : Finset (Fin N) :=
  univ.filter (fun i => (E i).val ∈ candidateBigPIndices scale L)

noncomputable def candidateRootPools {N : ℕ} (scale L : ℝ)
    (E : Fin N ≃ ↥(candidatePIndices scale L)) : Fin N → Finset ℕ :=
  fun i => candidatePBand (scale * L) (E i).val

theorem candidate_root_big_groups_mem {N : ℕ} (scale L : ℝ)
    (E : Fin N ≃ ↥(candidatePIndices scale L)) (i : Fin N) :
    i ∈ candidateRootBigGroups scale L E ↔ (E i).val ∈ candidateBigPIndices scale L := by
  simp only [candidateRootBigGroups, mem_filter, mem_univ, true_and]

noncomputable def candidateRootMixedPoolRealization {N M : ℕ} (scale L : ℝ)
    (E : Fin N ≃ ↥(candidatePIndices scale L))
    (e : {g // g ∉ (candidateRootBigGroups scale L E)ᶜ} ≃ Fin M) :
    CandidateMixedPoolRealization scale L
      (fun a : ↥(candidateRootBigGroups scale L E)ᶜ => candidateRootPools scale L E a.val)
      (fun g : Fin M => candidateRootPools scale L E (e.symm g).val) where
  smallIndex :=
    { toFun := fun a => ⟨(E a.val).val, by
        have hnot : (E a.val).val ∉ candidateBigPIndices scale L := by
          intro h
          exact (mem_compl.mp a.property) ((candidate_root_big_groups_mem scale L E a.val).mpr h)
        have hmem := (E a.val).property
        change (E a.val).val ∈ candidateSmallPIndices scale L ∪ candidateBigPIndices scale L at hmem
        exact (mem_union.mp hmem).resolve_right hnot⟩
      inj' := by
        intro a b hab
        apply Subtype.ext
        apply E.injective
        apply Subtype.ext
        exact congrArg (fun z : CandidateSmallGroup scale L => z.val) hab }
  bigIndex := fun g => ⟨(E (e.symm g).val).val, by
    apply (candidate_root_big_groups_mem scale L E (e.symm g).val).mp
    simpa only [mem_compl, not_not] using (e.symm g).property⟩
  smallPool_eq := fun _ => rfl
  bigPool_eq := fun _ => rfl

theorem candidate_root_big_groups_card {N : ℕ} (scale L : ℝ)
    (E : Fin N ≃ ↥(candidatePIndices scale L)) :
    (candidateRootBigGroups scale L E).card = (candidateBigPIndices scale L).card := by
  apply card_bij (fun i _ => (E i).val)
  · intro i hi
    exact (candidate_root_big_groups_mem scale L E i).mp hi
  · intro i _ j _ hij
    exact E.injective (Subtype.ext hij)
  · intro j hj
    refine ⟨E.symm ⟨j, mem_union_right _ hj⟩, ?_, ?_⟩
    · apply (candidate_root_big_groups_mem scale L E _).mpr
      simpa only [Equiv.apply_symm_apply] using hj
    · simp only [Equiv.apply_symm_apply]

theorem candidate_root_small_groups_card {N : ℕ} (scale L : ℝ)
    (E : Fin N ≃ ↥(candidatePIndices scale L))
    (hdis : Disjoint (candidateSmallPIndices scale L) (candidateBigPIndices scale L)) :
    (candidateRootBigGroups scale L E)ᶜ.card = (candidateSmallPIndices scale L).card := by
  apply card_bij (fun i _ => (E i).val)
  · intro i hi
    have hmem := (E i).property
    change (E i).val ∈ candidateSmallPIndices scale L ∪ candidateBigPIndices scale L at hmem
    apply (mem_union.mp hmem).resolve_right
    intro hb
    exact (mem_compl.mp hi) ((candidate_root_big_groups_mem scale L E i).mpr hb)
  · intro i _ j _ hij
    exact E.injective (Subtype.ext hij)
  · intro j hj
    refine ⟨E.symm ⟨j, mem_union_left _ hj⟩, ?_, ?_⟩
    · apply mem_compl.mpr
      intro hb
      have hb' := (candidate_root_big_groups_mem scale L E _).mp hb
      simp only [Equiv.apply_symm_apply] at hb'
      exact disjoint_left.mp hdis hj hb'
    · simp only [Equiv.apply_symm_apply]

end Bounty
end

section

/- The actual signed full norm bound applied to an untouched original root
Fourier edge, in its genuine reciprocal-birth measure. -/

open Finset Filter
open scoped Topology BigOperators Classical
namespace Bounty.WeakZeroFree

theorem actual_exists_realized_root_projected_good_norm_bound
    {qsmall vsmall scale : ℝ} (hq0 : 0 ≤ qsmall) (hq1 : qsmall < 1)
    (hvs : 0 < vsmall) (hscale : 0 < scale) (ell : ℕ) (C₂ : ℝ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀
    (c s z a v D ε E beta tau : ℝ)
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
    ∀ {N M n B : ℕ} (P : Fin N → Finset ℕ)
      [∀ z : PhysicalPrime P, NeZero z.2.val]
      (groups : Finset (Fin N)) (reindex : {g // g ∉ groupsᶜ} ≃ Fin M)
      [∀ z : PhysicalPrime (fun a : ↥groupsᶜ => P a.val), NeZero z.2.val]
      [∀ g (p : P (reindex.symm g).val), NeZero p.val]
      (hPs : ∀ (a : ↥groupsᶜ) p, p ∈ P a.val → Nat.Prime p)
      (hPb : ∀ (g : Fin M) p, p ∈ P (reindex.symm g).val → Nat.Prime p)
      (hcross : ∀ (a : ↥groupsᶜ) (g : Fin M), Disjoint (P a.val) (P (reindex.symm g).val))
      (_R : CandidateMixedPoolRealization scale L (fun a : ↥groupsᶜ => P a.val)
        (fun g : Fin M => P (reindex.symm g).val)) (V : Fin N → ℝ),
    Pairwise (fun g h : Fin M => Disjoint (P (reindex.symm g).val) (P (reindex.symm h).val)) →
    (∀ (g : Fin M) p, p ∈ P (reindex.symm g).val → p.Prime ∧ Q < p) →
    (∀ g : Fin M, ∑ p ∈ P (reindex.symm g).val, 1 / (p : ℝ) = V (reindex.symm g).val) →
    (∀ g : Fin M, v ≤ V (reindex.symm g).val) →
    (∀ (g : Fin M) p, p ∈ P (reindex.symm g).val → Real.log p ≤ L ^ s) →
    (M : ℝ) ≤ a * Real.log L →
    (∀ g : Fin M, ∃ a b : ℝ, P (reindex.symm g).val = primeBand a b ∧
      Real.exp (L ^ c) ≤ a ∧ 0 ≤ b) →
    ∀ probes : Fin N → Finset (Fin J), (∀ g : Fin M, (probes (reindex.symm g).val).card = m) →
    ∀ r t : Finset (Fin M), ∀ hrt : Disjoint r t,
    beta * Real.log L ≤ (r.card : ℝ) → beta * Real.log L ≤ (t.card : ℝ) →
    ∀ (ζ : ℕ → ℝ) (k : ℕ → ℤ) (θ : ℝ) (j : Fin (n + 1)),
    |ζ (n-j.val)| ≤ L ^ z → k (n-j.val) ≠ 0 → ((k (n-j.val)).natAbs : ℝ) ≤ L ^ C₂ →
    ∀ baseline : (g : Fin M) → P (reindex.symm g).val → ℝ,
    ∀ T Pmin : ℝ, 0 ≤ T → T ≤ L ^ tau → Real.exp (L ^ c) ≤ Pmin →
    (∀ (g : Fin M) (p : P (reindex.symm g).val), Pmin ≤ (p.val : ℝ)) →
    (∀ (g : Fin M) (p : P (reindex.symm g).val), baseline g p = 1 - T / (p.val : ℝ)) →
    (∀ g p, 1 / 2 ≤ baseline g p ∧ baseline g p ≤ 1) →
    (∀ a : ↥groupsᶜ, vsmall ≤ V a.val) →
    ∀ ρ u vmax : ℝ, 0 < ρ → ρ < 1 → 1 < u → (∀ g : Fin M, V (reindex.symm g).val ≤ vmax) →
    ∀ (retention : Fin (n + 2) → ℝ)
      (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
      (encode : ((g : Fin M) × P (reindex.symm g).val) → ℤ)
      (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
          ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
        Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
          ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) → ℝ),
    j ∉ physicalSelectedAffectedEdges (fun _ : Fin M => J + ell) B (n + 1) code →
    ∀ F : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups reindex → ℂ,
    (∀ d, ProductMemorySymmetric (fun x => F (d,x))) →
    let f := physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex
    let patterns := (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell)
      probes (r.map f) (t.map f)))
    let C := repeatedBigPrimePatternCut (ell := ell) probes (r.map f) (t.map f)
    let ζroot := fun time (_ : RepeatedBigPrimePatternIndex (ell := ell)
      probes (r.map f) (t.map f)) => ζ time
    let kroot := fun time (_ : RepeatedBigPrimePatternIndex (ell := ell)
      probes (r.map f) (t.map f)) => k time
    let β := fun (g : Fin M) (p : P (reindex.symm g).val) =>
      ((p.val : ℝ)*baseline g p)⁻¹
    let hC : ∀ i : patterns, ∀ a : ↥groupsᶜ, C i.val a.val = ∅ :=
      fun i a => physical_root_prime_full_pattern_small_cut groups reindex probes r t i.val a
    let K := fun (time : ℕ)
      (i : RepeatedBigPrimePatternIndex (ell := ell) probes (r.map f) (t.map f))
      (L R : PhysicalMarkLists P J ell) (aux : PhysicalAuxLabels P (C i)) =>
      if time % 2 = 0 then
        (starRingEnd ℂ) (physicalRootPrimeKernel P V probes (r.map f) (t.map f)
          ((Finset.disjoint_map f).mpr hrt) Q h ξ i R L aux)
      else physicalRootPrimeKernel P V probes (r.map f) (t.map f)
        ((Finset.disjoint_map f).mpr hrt) Q h ξ i L R aux
    let row := physicalRootFourierRow groups reindex patterns C hC kroot V qsmall ζroot K θ β retention ρ
      hPs hPb hcross code encode ν
    let Wroot := physicalSmallBigMeasure (fun a : ↥groupsᶜ => V a.val)
      (productMemoryWeight (fun g p => β g p / V (reindex.symm g).val)
        (fun g => unrestrictedResidueWeight (fun p => β g p / V (reindex.symm g).val)))
    cleanActiveNorm Wroot (row none (row (some (.inr j)) (row none F))) ≤
      A ^ groupsᶜ.card *
        (L ^ (-E) + 2 * repeatedBigFamilyEnvelope M m Q ξ *
          Real.sqrt ((B : ℝ) / (((J + ell).choose ell) ^ groupsᶜ.card : ℕ)) *
          Real.sqrt (unrestrictedEdgeEnergyBound ρ u v vmax (ell + m) ^ M)) *
        cleanActiveNorm Wroot F := by
  obtain ⟨A, hA, hbound⟩ :=
    actual_exists_realized_candidate_physical_mixed_signed_full_norm_bound
      hq0 hq1 hvs hscale ell C₂
  refine ⟨A, hA, ?_⟩
  intro c s z a v D ε E beta tau m J hc hs hz ha hv hD hε htau hell hml hgap hDgap
    κ s' A₀ q w x
  filter_upwards [hbound c s z a v D ε E beta tau m J hc hs hz ha hv hD hε htau
    hell hml hgap hDgap] with L hL
  intro Q h ξ N M n B P _ groups reindex _ _ hPs hPb hcross R V hbdis hprime hmass hV
    hlog hcard hband probes hprobes r t hrt hr ht ζ k θ j hζ hk hkmax baseline T Pmin
    hT hTmax hPmin hPlow hbaseline hbaselineBounds hVs ρ u vmax hρ0 hρ1 hu hVhi
    retention code encode ν hj F hF f patterns C ζroot kroot β hC K row Wroot
  have hb := hL ↥groupsᶜ (Fin M) (fun a : ↥groupsᶜ => P a.val)
    (fun g => P (reindex.symm g).val) R (fun g => V (reindex.symm g).val)
    hbdis hprime hmass hV hlog (by simpa only [Fintype.card_fin] using hcard) hband
    (fun g => probes (reindex.symm g).val) hprobes r t hrt hr ht (ζ (n-j.val)) θ hζ
    (fun _ => ∅) (fun _ => by simp only [card_empty]; exact Nat.zero_le _)
    baseline T Pmin hT hTmax hPmin hPlow hbaseline hbaselineBounds B (n-j.val)
    (k (n-j.val)) hk hkmax (fun a : ↥groupsᶜ => V a.val) hVs ρ u vmax hρ0 hρ1 hu hVhi F hF
  have hrow := physical_root_untouched_prime_edge_eq_signed_action groups reindex V probes r t
    hrt Q h ξ ζ k θ baseline ρ hPs hPb hcross qsmall retention code encode ν j hj F
  change row none (row (some (.inr j)) (row none F)) = _ at hrow
  rw [hrow]
  dsimp only [Wroot]
  have hμpoint (g : Fin M) (p : P (reindex.symm g).val) :
      β g p / V (reindex.symm g).val =
        tiltedPhysicalBirthLaw (P := fun g : Fin M => P (reindex.symm g).val)
          (fun g => V (reindex.symm g).val) g (baseline g) p :=
    physical_root_tilted_birth_law (fun g => V (reindex.symm g).val) baseline g p
  simp_rw [hμpoint]
  simpa only [Fintype.card_fin, Fintype.card_coe] using hb

end Bounty.WeakZeroFree
end

section

/- The actual projected root edges satisfy the piecewise cost condition used
by the Fourier word estimate. Both constants precede all analytic windows and
root data, and the excess is explicitly at least the positive decay. -/

open Finset Filter
open scoped Topology BigOperators Classical
namespace Bounty.WeakZeroFree

theorem actual_exists_realized_root_projected_edge_costs
    {qsmall vsmall scale : ℝ} (hq0 : 0 ≤ qsmall) (hq1 : qsmall < 1)
    (hvs : 0 < vsmall) (hscale : 0 < scale) (ell : ℕ) (C₂ : ℝ) :
    ∃ A Cbad : ℝ, 1 ≤ A ∧ 1 ≤ Cbad ∧ ∀
    (c s z a v D ε E beta tau : ℝ)
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
    ∀ {N M n B : ℕ} (P : Fin N → Finset ℕ)
      [∀ z : PhysicalPrime P, NeZero z.2.val]
      (groups : Finset (Fin N)) (reindex : {g // g ∉ groupsᶜ} ≃ Fin M)
      [∀ z : PhysicalPrime (fun a : ↥groupsᶜ => P a.val), NeZero z.2.val]
      [∀ g (p : P (reindex.symm g).val), NeZero p.val]
      (hPs : ∀ (a : ↥groupsᶜ) p, p ∈ P a.val → Nat.Prime p)
      (hPb : ∀ (g : Fin M) p, p ∈ P (reindex.symm g).val → Nat.Prime p)
      (hcross : ∀ (a : ↥groupsᶜ) (g : Fin M), Disjoint (P a.val) (P (reindex.symm g).val))
      (_R : CandidateMixedPoolRealization scale L (fun a : ↥groupsᶜ => P a.val)
        (fun g : Fin M => P (reindex.symm g).val)) (V : Fin N → ℝ),
    Pairwise (fun g h : Fin M => Disjoint (P (reindex.symm g).val) (P (reindex.symm h).val)) →
    (∀ (g : Fin M) p, p ∈ P (reindex.symm g).val → p.Prime ∧ Q < p) →
    (∀ g : Fin M, ∑ p ∈ P (reindex.symm g).val, 1 / (p : ℝ) = V (reindex.symm g).val) →
    (∀ g : Fin M, v ≤ V (reindex.symm g).val) →
    (∀ (g : Fin M) p, p ∈ P (reindex.symm g).val → Real.log p ≤ L ^ s) →
    (M : ℝ) ≤ a * Real.log L →
    (∀ g : Fin M, ∃ a b : ℝ, P (reindex.symm g).val = primeBand a b ∧
      Real.exp (L ^ c) ≤ a ∧ 0 ≤ b) →
    ∀ probes : Fin N → Finset (Fin J), (∀ g : Fin M, (probes (reindex.symm g).val).card = m) →
    ∀ r t : Finset (Fin M), ∀ hrt : Disjoint r t,
    beta * Real.log L ≤ (r.card : ℝ) → beta * Real.log L ≤ (t.card : ℝ) →
    ∀ (ζ : ℕ → ℝ) (k : ℕ → ℤ) (θ : ℝ),
    (∀ j : Fin (n + 1), |ζ (n-j.val)| ≤ L ^ z) →
    (∀ j : Fin (n + 1), k (n-j.val) ≠ 0) →
    (∀ j : Fin (n + 1), ((k (n-j.val)).natAbs : ℝ) ≤ L ^ C₂) →
    ∀ baseline : (g : Fin M) → P (reindex.symm g).val → ℝ,
    ∀ T Pmin : ℝ, 0 ≤ T → T ≤ L ^ tau → Real.exp (L ^ c) ≤ Pmin →
    (∀ (g : Fin M) (p : P (reindex.symm g).val), Pmin ≤ (p.val : ℝ)) →
    (∀ (g : Fin M) (p : P (reindex.symm g).val), baseline g p = 1 - T / (p.val : ℝ)) →
    (∀ g p, 1 / 2 ≤ baseline g p ∧ baseline g p ≤ 1) →
    (∀ a : ↥groupsᶜ, vsmall ≤ V a.val) →
    ∀ ρ u vmax : ℝ, 0 < ρ → ρ < 1 → 1 < u → (∀ g : Fin M, V (reindex.symm g).val ≤ vmax) →
    ∀ (retention : Fin (n + 2) → ℝ)
      (code : PhysicalRootCommonForestCode (M := M) (J := J) (ell := ell) (n := n) (B := B))
      (encode : ((g : Fin M) × P (reindex.symm g).val) → ℤ)
      (ν : (Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
          ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1))))) ×
        Fin (Fintype.card (FullMixedCommonBirthAddress (fun _ : Fin M => J + ell) B
          ((List.range (4 * (n + 1) + 1)).map (physicalSelectedFineTag (n + 1)))))) → ℝ),
    let f := physicalReindexedBigEmbedding (fun g => g ∈ groupsᶜ) reindex
    let patterns := (univ : Finset (RepeatedBigPrimePatternIndex (ell := ell)
      probes (r.map f) (t.map f)))
    let C := repeatedBigPrimePatternCut (ell := ell) probes (r.map f) (t.map f)
    let ζroot := fun time (_ : RepeatedBigPrimePatternIndex (ell := ell)
      probes (r.map f) (t.map f)) => ζ time
    let kroot := fun time (_ : RepeatedBigPrimePatternIndex (ell := ell)
      probes (r.map f) (t.map f)) => k time
    let β := fun (g : Fin M) (p : P (reindex.symm g).val) =>
      ((p.val : ℝ)*baseline g p)⁻¹
    let hC : ∀ i : patterns, ∀ a : ↥groupsᶜ, C i.val a.val = ∅ :=
      fun i a => physical_root_prime_full_pattern_small_cut groups reindex probes r t i.val a
    let K := fun (time : ℕ)
      (i : RepeatedBigPrimePatternIndex (ell := ell) probes (r.map f) (t.map f))
      (L R : PhysicalMarkLists P J ell) (aux : PhysicalAuxLabels P (C i)) =>
      if time % 2 = 0 then
        (starRingEnd ℂ) (physicalRootPrimeKernel P V probes (r.map f) (t.map f)
          ((Finset.disjoint_map f).mpr hrt) Q h ξ i R L aux)
      else physicalRootPrimeKernel P V probes (r.map f) (t.map f)
        ((Finset.disjoint_map f).mpr hrt) Q h ξ i L R aux
    let row := physicalRootFourierRow groups reindex patterns C hC kroot V qsmall ζroot K θ β retention ρ
      hPs hPb hcross code encode ν
    let Wroot := physicalSmallBigMeasure (fun a : ↥groupsᶜ => V a.val)
      (productMemoryWeight (fun g p => β g p / V (reindex.symm g).val)
        (fun g => unrestrictedResidueWeight (fun p => β g p / V (reindex.symm g).val)))
    let decay := A ^ groupsᶜ.card *
      (L ^ (-E) + 2 * repeatedBigFamilyEnvelope M m Q ξ *
        Real.sqrt ((B : ℝ) / (((J + ell).choose ell) ^ groupsᶜ.card : ℕ)) *
        Real.sqrt (unrestrictedEdgeEnergyBound ρ u v vmax (ell + m) ^ M))
    let excess := max decay (repeatedBigFamilyEnvelope M m Q ξ * Cbad ^ groupsᶜ.card *
      Real.sqrt (unrestrictedEdgeEnergyBound ρ u v vmax (ell + m) ^ M))
    0 < decay ∧ decay ≤ excess ∧
      ∀ (j : Fin (n + 1))
        (F : PhysicalRootMixedState (P := P) (J := J) (ell := ell) (B := B) groups reindex → ℂ),
      (∀ d, ProductMemorySymmetric (fun x => F (d,x))) →
      cleanActiveNorm Wroot (row none (row (some (.inr j)) (row none F))) ≤
        (if j ∈ physicalSelectedAffectedEdges (fun _ : Fin M => J + ell) B (n + 1) code
          then excess else decay) * cleanActiveNorm Wroot F := by
  obtain ⟨A, hA, hgood⟩ := actual_exists_realized_root_projected_good_norm_bound
    hq0 hq1 hvs hscale ell C₂
  obtain ⟨Cbad, hCbad, hbad⟩ := exists_physical_root_projected_prime_edge_norm_bound
    hq0 hq1 hvs ell
  refine ⟨A, Cbad, hA, hCbad, ?_⟩
  intro c s z a v D ε E beta tau m J hc hs hz ha hv hD hε htau hell hml hgap hDgap
    κ s' A₀ q w x
  filter_upwards [hgood c s z a v D ε E beta tau m J hc hs hz ha hv hD hε htau
    hell hml hgap hDgap, eventually_gt_atTop (0 : ℝ)] with L hL hLpos
  intro Q h ξ N M n B P _ groups reindex _ _ hPs hPb hcross R V hbdis hprime hmass hV
    hlog hcard hband probes hprobes r t hrt hr ht ζ k θ hζ hk hkmax baseline T Pmin
    hT hTmax hPmin hPlow hbaseline hbaselineBounds hVs ρ u vmax hρ0 hρ1 hu hVhi
    retention code encode ν f patterns C ζroot kroot β hC K row Wroot decay excess
  have hdecay : 0 < decay := by
    apply mul_pos (pow_pos (lt_of_lt_of_le zero_lt_one hA) _)
    apply add_pos_of_pos_of_nonneg (Real.rpow_pos_of_pos hLpos _)
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (repeated_big_family_envelope_nonneg M m Q ξ))
        (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  refine ⟨hdecay, le_max_left _ _, ?_⟩
  intro j F hF
  by_cases hj : j ∈ physicalSelectedAffectedEdges (fun _ : Fin M => J + ell) B (n + 1) code
  · rw [if_pos hj]
    have hb := hbad groups reindex V probes r t hrt Q h ξ ζ k θ baseline ρ
      hPs hPb hcross retention code encode ν m (fun g => (hprobes g).le)
      (Real.rpow_pos_of_pos hLpos _) hVs hmass hbaselineBounds
      u v vmax hρ0 hρ1 hu hv hV hVhi j F hF
    change cleanActiveNorm Wroot (row none (row (some (.inr j)) (row none F))) ≤
      (repeatedBigFamilyEnvelope M m Q ξ * Cbad ^ groupsᶜ.card *
        Real.sqrt (unrestrictedEdgeEnergyBound ρ u v vmax (ell + m) ^ M)) *
        cleanActiveNorm Wroot F at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _))
  · rw [if_neg hj]
    exact hL P groups reindex hPs hPb hcross R V hbdis hprime hmass hV hlog hcard hband
      probes hprobes r t hrt hr ht ζ k θ j (hζ j) (hk j) (hkmax j) baseline T Pmin
      hT hTmax hPmin hPlow hbaseline hbaselineBounds hVs ρ u vmax hρ0 hρ1 hu hVhi
      retention code encode ν hj F hF

end Bounty.WeakZeroFree
end
