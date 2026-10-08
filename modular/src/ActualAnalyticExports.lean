import WeakAnalyticLeaves

/-! Actual zero-free specializations of the full-memory and mixed norm estimates. -/

open Finset Filter
open scoped Topology BigOperators Classical

namespace Bounty.WeakZeroFree

theorem actual_eventually_repeated_big_prime_full_memory_power_bound
    (c s z a v D ε E beta tau : ℝ)
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
  exact eventually_repeated_big_prime_full_memory_power_bound actual_zero_free c s z a v D ε E beta tau m J ell
    hc hs hz ha hv hD hε htau hell hml hgap hDgap

theorem actual_eventually_repeated_big_prime_full_memory_cutoff_power_bound
    (c s z a v D ε E beta tau : ℝ)
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
  exact eventually_repeated_big_prime_full_memory_cutoff_power_bound actual_zero_free c s z a v D ε E beta tau m J ell
    hc hs hz ha hv hD hε htau hell hml hgap hDgap

theorem actual_eventually_repeated_big_prime_initial_full_memory_power_bound
    (c s z a v D ε E beta tau : ℝ)
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
  exact eventually_repeated_big_prime_initial_full_memory_power_bound actual_zero_free c s z a v D ε E beta tau m J ell
    hc hs hz ha hv hD hε htau hell hml hgap hDgap

theorem actual_eventually_repeated_big_prime_initial_full_memory_cutoff_power_bound
    (c s z a v D ε E beta tau : ℝ)
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
  exact eventually_repeated_big_prime_initial_full_memory_cutoff_power_bound actual_zero_free c s z a v D ε E beta tau m J ell
    hc hs hz ha hv hD hε htau hell hml hgap hDgap

theorem actual_exists_candidate_physical_mixed_full_norm_bound
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
  obtain ⟨A, hA, h⟩ := exists_candidate_physical_mixed_full_norm_bound hq0 hq1 hvs hscale ell C₂
  exact ⟨A, hA, h actual_zero_free⟩

end Bounty.WeakZeroFree
