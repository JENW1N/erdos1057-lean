import WeakAnalyticLeaves

/-! Actual source and cell estimates using the verified weaker zero-free theorem. -/

open scoped Topology BigOperators Classical

-- Source module: CandidateRetainedBoxScales

/- The actual small-prime and rough factors supply the retained common-window scales.
The local width is an explicit upstream input; no desired integral scale is assumed. -/

open Finset Filter

namespace Bounty

theorem eventually_common_cell_exponential_lower {b : ℝ} (hb : 0 < b) :
    ∀ᶠ L : ℝ in atTop, ∀ Z H d : ℝ, 0 < Z → d ≤ Real.exp 2*H →
      Real.exp (b*L) ≤ Z*d/2 → Real.exp ((b/2)*L) ≤ Z*H := by
  filter_upwards [eventually_ge_atTop (4/b)] with L hL
  intro Z H d hZ hcell hlower
  have hgap := (div_le_iff₀ hb).mp hL
  have he : Real.exp 2*Real.exp ((b/2)*L) ≤ Real.exp (b*L) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hgap]
  have hm := mul_le_mul_of_nonneg_left hcell hZ.le
  have hh : Real.exp 2*Real.exp ((b/2)*L) ≤ Real.exp 2*(Z*H) := by
    nlinarith only [he,hlower,hm,Real.exp_pos (b*L)]
  exact (mul_le_mul_iff_right₀ (Real.exp_pos 2)).mp hh

theorem exists_actual_retained_box_scales {c b cLog : ℝ} (hc : 0 < c) (hb : 0 < b) :
    ∃ J : ℕ, ∀ jStar : ℕ, J < jStar → ∃ aLong : ℝ, 0 < aLong ∧
      ∀ᶠ L : ℝ in atTop, ∀ g ∈ candidateSmallPIndices c L,
      ∀ Y P UQ UM UT Hlocal R : ℝ,
      Real.exp (b*L) ≤ Y → Real.log Y ≤ cLog*L →
      0 < UQ → 0 < UM → 0 < UT → 0 < Hlocal →
      4096*P*L ≤ Hlocal → R ≤ 2*L*Y/Hlocal →
      ∀ p q m t : ℕ, p ∈ candidatePBand (c*L) g → q ∈ candidateRoughBand c L jStar →
      P ≤ (p : ℝ) → (p : ℝ) ≤ 2*P →
      UQ < (q : ℝ) → (q : ℝ) ≤ 2*UQ →
      UM ≤ (m : ℝ) → (m : ℝ) ≤ 2*UM →
      UT ≤ (t : ℝ) → (t : ℝ) ≤ 2*UT →
      p*q*m*t ∈ (harmonicCommonSupport Y).image Int.natAbs →
      1 ≤ P ∧ Real.exp (aLong*L) ≤ UQ ∧ R ≤ Y ∧
        R ≤ UQ*UM*UT/2 ∧ Y^(3/5 : ℝ) ≤ UM*UT/2 ∧
        Real.log (8*(UQ*UM*UT)) ≤ (cLog+1)*L := by
  obtain ⟨J,hJ⟩ := exists_candidate_long_rough_dyadic_window hc (show 0 < b/5 by positivity)
  refine ⟨J,?_⟩
  intro jStar hj
  obtain ⟨aLong,haLong,hrough⟩ := hJ jStar hj
  obtain ⟨Bcoeff,hBcoeff,hsmall⟩ := exists_candidate_small_prime_factor_data hc
  refine ⟨aLong,haLong,?_⟩
  filter_upwards [hrough,hsmall,
    eventually_four_factor_residual_scale (beta := (1/5 : ℝ)) (d := b)
      (eta := b/5) (C := 256) (by norm_num) hb (by linarith) (by norm_num),
    eventually_ge_atTop (Real.log 32+2),eventually_ge_atTop (1 : ℝ)]
    with L hroughL hsmallL hresidual hlogconst hL
  intro g hg Y P UQ UM UT Hlocal R hYlo hYlog hQ hM hT hH hwidth hR
    p q m t hp hq hpLo hpHi hqLo hqHi hmLo hmHi htLo htHi hprod
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hY : 0 < Y := (Real.exp_pos _).trans_le hYlo
  have hYlower : b*L ≤ Real.log Y := (Real.le_log_iff_exp_le hY).mpr hYlo
  have hs : ({p} : Finset ℕ) ⊆ candidatePBand (c*L) g := by simpa only [singleton_subset_iff]
  have hsp : ∀ n ∈ ({p} : Finset ℕ), P ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*P := by
    intro n hn
    have he : n = p := mem_singleton.mp hn
    simpa only [he] using And.intro hpLo hpHi
  obtain ⟨_,hPlower,hPupper,_⟩ := hsmallL g hg {p} P hs (singleton_nonempty p) hsp
  have hP1 : 1 ≤ P := by
    have hpow : 1 ≤ L^(1/10 : ℝ) := Real.one_le_rpow hL (by norm_num)
    have he := Real.add_one_le_exp (L^(1/10 : ℝ))
    linarith
  have hP : 0 < P := zero_lt_one.trans_le hP1
  have hQne : ((candidateRoughBand c L jStar).filter
      (fun n : ℕ => UQ < (n : ℝ) ∧ (n : ℝ) ≤ 2*UQ)).Nonempty :=
    ⟨q,mem_filter.mpr ⟨hq,hqLo,hqHi⟩⟩
  obtain ⟨hQlong,hQshort,_⟩ := hroughL UQ hQ hQne
  have hproduct := (mem_harmonic_common_natural_support hY).mp hprod
  have hlow : P*UQ*UM*UT ≤ ((p*q*m*t : ℕ) : ℝ) := by
    push_cast
    gcongr
  have hhigh : ((p*q*m*t : ℕ) : ℝ) ≤ 16*(P*UQ*UM*UT) := by
    push_cast
    calc
      _ ≤ (2*P)*(2*UQ)*(2*UM)*(2*UT) := by gcongr
      _ = _ := by ring
  have hmean : Y/(256*P) ≤ UQ*UM*UT/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 256*P)).mpr
    nlinarith only [hproduct.1.trans hhigh]
  have hres : Y/(256*P*UQ) ≤ UM*UT/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 256*P*UQ)).mpr
    nlinarith only [hproduct.1.trans hhigh]
  have htime : 2*L*Y/Hlocal ≤ Y/(256*P) := by
    apply (div_le_div_iff₀ hH (by positivity : 0 < 256*P)).mpr
    have hw : 512*P*L ≤ Hlocal := by nlinarith only [hwidth, mul_nonneg hP.le hL0.le]
    nlinarith only [mul_le_mul_of_nonneg_left hw hY.le]
  have htriple : UQ*UM*UT ≤ 4*Real.exp 2*Y := by
    have hm : UQ*UM*UT ≤ P*(UQ*UM*UT) := le_mul_of_one_le_left (by positivity) hP1
    nlinarith only [hm,hlow,hproduct.2]
  have hlog : Real.log (8*(UQ*UM*UT)) ≤ (cLog+1)*L := by
    have hh := Real.log_le_log (by positivity : 0 < 8*(UQ*UM*UT))
      (show 8*(UQ*UM*UT) ≤ 32*Real.exp 2*Y by nlinarith only [htriple])
    rw [Real.log_mul (by positivity : (32*Real.exp 2 : ℝ) ≠ 0) hY.ne',
      Real.log_mul (by norm_num : (32 : ℝ) ≠ 0) (Real.exp_ne_zero 2),Real.log_exp] at hh
    nlinarith only [hh,hYlog,hlogconst]
  have hRY : R ≤ Y := (hR.trans htime).trans
    (div_le_self hY.le (show 1 ≤ 256*P by linarith))
  exact ⟨hP1,hQlong,hRY,hR.trans (htime.trans hmean),
    hresidual Y P UQ (UM*UT/2) hY hP hQ hYlower hPupper hQshort hres,hlog⟩

end Bounty


-- Source module: ActualRetainedPrimeBoxPrecision

/- The original prime cutoff estimate on a retained box, with its integral scales derived from actual factor support. -/

open Finset Filter MeasureTheory

namespace Bounty.WeakZeroFree

theorem exists_actual_retained_prime_cutoff_integral_precision
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q cLog d : ℝ}
    (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1) (hcLog : 0 ≤ cLog) (hd : 0 < d)
    : ∃ J : ℕ, ∀ jStar : ℕ, J < jStar →
      ∀ (A : ℝ) (T : ℕ) (Tmod Sshift Cmod Sfreq Rmod W : ℝ),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, ∃ S₀ : ℝ, 0 ≤ S₀ ∧
      ∀ S : ℝ, S₀ ≤ S →
      ∀ᶠ L : ℝ in atTop,
      ∀ (r : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (tmarks umarks : candidatePIndices c L → ℕ) (big : Finset (candidatePIndices c L))
        (b : GroupMarkedLists (fun g : big => candidatePBand (c*L) g.val.val)
          (fun g : big => umarks g.val) → ℂ) (κ : ℕ → ℂ),
      (∀ g, tmarks g ≤ T) → (∀ l, ‖b l‖ ≤ L^B) → (∀ n, ‖κ n‖ ≤ 1) →
      ∀ (g : ℕ), g ∈ candidateSmallPIndices c L →
      ∀ (s : Finset ℕ) (Y P R Hlocal : ℝ), s ⊆ candidatePBand (c*L) g →
      1 ≤ Y → Real.exp (d*L) ≤ Y → Real.log Y ≤ cLog*L →
      0 ≤ R → 0 < Hlocal → 4096*P*L ≤ Hlocal → R ≤ 2*L*Y/Hlocal →
      (∀ p ∈ s, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*P) →
      ∀ (qP qT : ℕ) (χP : DirichletCharacter ℂ qP) (χT : DirichletCharacter ℂ qT)
        (τP τT : ℝ) (lo hi : ℕ) (F : Finset ℕ) (UM UT : ℝ),
      0 < UM → 1 ≤ UT →
      (∀ n ∈ Ioc lo hi, UM ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UM) →
      (∀ n ∈ F, UT ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UT) →
      ∀ (κM ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      0 ≤ κM → κM ≤ 1/50 → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (UQ Alo Blo σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      0 < UQ → UQ ≤ Alo → Alo ≤ Blo → Blo ≤ 2*UQ →
      roughBand Alo Blo (Real.exp (Real.sqrt L)) ⊆ candidateRoughBand c L jStar →
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      (∃ p ∈ s, ∃ z ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
        ∃ m ∈ (Ioc lo hi).filter (fun n =>
          (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ) ≠ 0),
        ∃ n ∈ F, p*z*m*n ∈ (harmonicCommonSupport Y).image Int.natAbs) →
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
  obtain ⟨J,hgeometry⟩ := exists_actual_retained_box_scales hc hd
  refine ⟨J,?_⟩
  intro jStar hjStar A T Tmod Sshift Cmod Sfreq Rmod W
  obtain ⟨aLong,haLong,hscales⟩ := hgeometry jStar hjStar
  obtain ⟨C,hC,hmain⟩ := exists_rational_prime_cutoff_integral_precision
    (cLog := cLog+1) (d := d) (A := A) hZ hc hq0 hq1 (by linarith) hd haLong
      T Tmod Sshift Cmod Sfreq Rmod W
  refine ⟨C,hC,?_⟩
  intro B
  obtain ⟨S₀,hS₀,hbound⟩ := hmain B
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [hbound S hS,hscales,eventually_gt_atTop (0 : ℝ)]
    with L hdecay hscale hL
  intro r hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ g hg s Y P R Hlocal hs
    hY hYlo hYhi hR hHlocal hwidth hRwidth hsp
    qP qT χP χT τP τT lo hi F UM UT hUM hUT hMband hFband
    κM ν qM hqMInst χM hκM hκmax hqM hν UQ Alo Blo σ qQ hqQInst χQ
    hUQ hQA hAB hBQ hQsubset hqQ hσ hwitness hprod qRat hqRat0 hqRat aRat w hw
  obtain ⟨p,hp,z,hz,m,hm,n,hn,hwindow⟩ := hwitness
  have hzReal := (mem_roughBand_real_iff (hUQ.le.trans hQA)
    (hUQ.le.trans (hQA.trans hAB)) z).mp hz
  have hgeometryL := hscale g hg Y P UQ UM UT Hlocal R hYlo hYhi
    hUQ hUM (zero_lt_one.trans_le hUT) hHlocal hwidth hRwidth
    p z m n (hs hp) (hQsubset hz) (hsp p hp).1 (hsp p hp).2
    (hQA.trans_lt hzReal.1) (hzReal.2.1.trans hBQ)
    (hMband m (mem_filter.mp hm).1).1 (hMband m (mem_filter.mp hm).1).2
    (hFband n hn).1 (hFband n hn).2 hwindow
  have hYloglo : d*L ≤ Real.log Y :=
    (Real.le_log_iff_exp_le (zero_lt_one.trans_le hY)).mpr hYlo
  have hYloghi : Real.log Y ≤ (cLog+1)*L := by nlinarith only [hYhi,hL]
  exact @hdecay r jStar hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ
    g hg s Y P R hs ⟨p,hp⟩ hY hYloglo hYloghi hR hgeometryL.2.2.1 hsp
    qP qT χP χT τP τT lo hi F UM UT hUM hUT hMband hFband
    κM ν qM hqMInst χM hκM hκmax hqM hν UQ Alo Blo σ qQ hqQInst χQ
    hgeometryL.2.1 hQA hAB hBQ hqQ hσ hgeometryL.2.2.2.1
    hgeometryL.2.2.2.2.1 hgeometryL.2.2.2.2.2 hprod qRat hqRat0 hqRat aRat w hw

end Bounty.WeakZeroFree


-- Source module: ActualRetainedRoughBoxPrecision

/- The original rough cutoff estimate on a retained box, with its integral scales derived from actual factor support. -/

open Finset Filter MeasureTheory

namespace Bounty.WeakZeroFree

theorem exists_actual_retained_rough_cutoff_integral_precision
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q cLog d γrough vMax ρ : ℝ}
    (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1) (hcLog : 0 ≤ cLog) (hd : 0 < d)
    (hγ : 0 < γrough) (hv : vMax < 1) (hρ : 0 < ρ)
    : ∃ J : ℕ, ∀ jStar : ℕ, J < jStar →
      ∀ (A : ℝ) (T : ℕ) (Tmod Sshift Cmod Sfreq Rmod W : ℝ),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, ∃ S₀ : ℝ, 0 ≤ S₀ ∧
      ∀ S : ℝ, S₀ ≤ S →
      ∀ᶠ L : ℝ in atTop,
      ∀ (r : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (tmarks umarks : candidatePIndices c L → ℕ) (big : Finset (candidatePIndices c L))
        (b : GroupMarkedLists (fun g : big => candidatePBand (c*L) g.val.val)
          (fun g : big => umarks g.val) → ℂ) (κ : ℕ → ℂ),
      (∀ g, tmarks g ≤ T) → (∀ l, ‖b l‖ ≤ L^B) → (∀ n, ‖κ n‖ ≤ 1) →
      ∀ (g : ℕ), g ∈ candidateSmallPIndices c L →
      ∀ (s : Finset ℕ) (Y P R Hlocal : ℝ), s ⊆ candidatePBand (c*L) g →
      1 ≤ Y → Real.exp (d*L) ≤ Y → Real.log Y ≤ cLog*L →
      0 ≤ R → 0 < Hlocal → 4096*P*L ≤ Hlocal → R ≤ 2*L*Y/Hlocal →
      (∀ p ∈ s, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*P) →
      ∀ (qP qT : ℕ) (χP : DirichletCharacter ℂ qP) (χT : DirichletCharacter ℂ qT)
        (τP τT : ℝ) (lo hi : ℕ) (F : Finset ℕ) (UM UT : ℝ),
      0 < UM → 1 ≤ UT →
      (∀ n ∈ Ioc lo hi, UM ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UM) →
      (∀ n ∈ F, UT ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*UT) →
      ∀ (aM v ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      v ≤ vMax → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (UQ Alo Blo σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      0 < UQ → UQ ≤ Alo → Alo ≤ Blo → Blo ≤ 2*UQ →
      roughBand Alo Blo (Real.exp (Real.sqrt L)) ⊆ candidateRoughBand c L jStar →
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      (∃ p ∈ s, ∃ z ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
        ∃ m ∈ (Ioc lo hi).filter (fun n =>
          (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ) ≠ 0),
        ∃ n ∈ F, p*z*m*n ∈ (harmonicCommonSupport Y).image Int.natAbs) →
      (∀ p ∈ s, ∀ z ∈ roughBand Alo Blo (Real.exp (Real.sqrt L)),
        ∀ m ∈ (Ioc lo hi).filter (fun n =>
          (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ) ≠ 0),
        ∀ n ∈ F, Y/128 ≤ ((p*z*m*n : ℕ) : ℝ) ∧
          ((p*z*m*n : ℕ) : ℝ) ≤ 64*Real.exp 2*Y) →
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
  obtain ⟨J,hgeometry⟩ := exists_actual_retained_box_scales hc hd
  refine ⟨J,?_⟩
  intro jStar hjStar A T Tmod Sshift Cmod Sfreq Rmod W
  obtain ⟨aLong,haLong,hscales⟩ := hgeometry jStar hjStar
  obtain ⟨C,hC,hmain⟩ := exists_rational_rough_cutoff_integral_precision
    (cLog := cLog+1) (d := d) (A := A) hZ hc hq0 hq1 (by linarith) hd haLong hγ hv hρ
      T Tmod Sshift Cmod Sfreq Rmod W
  refine ⟨C,hC,?_⟩
  intro B
  obtain ⟨S₀,hS₀,hbound⟩ := hmain B
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [hbound S hS,hscales,eventually_gt_atTop (0 : ℝ)]
    with L hdecay hscale hL
  intro r hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ g hg s Y P R Hlocal hs
    hY hYlo hYhi hR hHlocal hwidth hRwidth hsp
    qP qT χP χT τP τT lo hi F UM UT hUM hUT hMband hFband
    aM v ν qM hqMInst χM hvM hqM hν UQ Alo Blo σ qQ hqQInst χQ
    hUQ hQA hAB hBQ hQsubset hqQ hσ hwitness hprod qRat hqRat0 hqRat aRat w hw
  obtain ⟨p,hp,z,hz,m,hm,n,hn,hwindow⟩ := hwitness
  have hzReal := (mem_roughBand_real_iff (hUQ.le.trans hQA)
    (hUQ.le.trans (hQA.trans hAB)) z).mp hz
  have hgeometryL := hscale g hg Y P UQ UM UT Hlocal R hYlo hYhi
    hUQ hUM (zero_lt_one.trans_le hUT) hHlocal hwidth hRwidth
    p z m n (hs hp) (hQsubset hz) (hsp p hp).1 (hsp p hp).2
    (hQA.trans_lt hzReal.1) (hzReal.2.1.trans hBQ)
    (hMband m (mem_filter.mp hm).1).1 (hMband m (mem_filter.mp hm).1).2
    (hFband n hn).1 (hFband n hn).2 hwindow
  have hYloglo : d*L ≤ Real.log Y :=
    (Real.le_log_iff_exp_le (zero_lt_one.trans_le hY)).mpr hYlo
  have hYloghi : Real.log Y ≤ (cLog+1)*L := by nlinarith only [hYhi,hL]
  exact @hdecay r jStar hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ
    g hg s Y P R hs ⟨p,hp⟩ hY hYloglo hYloghi hR hgeometryL.2.2.1 hsp
    qP qT χP χT τP τT lo hi F UM UT hUM hUT hMband hFband
    aM v ν qM hqMInst χM hvM hqM hν UQ Alo Blo σ qQ hqQInst χQ
    hgeometryL.2.1 hQA hAB hBQ hqQ hσ hgeometryL.2.2.2.1
    hgeometryL.2.2.2.2.1 hgeometryL.2.2.2.2.2 hprod qRat hqRat0 hqRat aRat w hw

end Bounty.WeakZeroFree


-- Source module: FourBoxNonzeroSupport

/- Finite four-factor boxes retain their original coefficients when zero
coordinates are removed. Nonzero boxes have literal nonzero product witnesses. -/

open Finset

namespace Bounty

theorem four_box_kernel_sum_filter_nonzero (D A B C : Finset ℕ)
    (δ α β γ H : ℕ → ℂ) :
    fourBoxKernelSum (D.filter (fun n => δ n ≠ 0)) (A.filter (fun n => α n ≠ 0))
      (B.filter (fun n => β n ≠ 0)) (C.filter (fun n => γ n ≠ 0)) δ α β γ H =
    fourBoxKernelSum D A B C δ α β γ H := by
  classical
  unfold fourBoxKernelSum
  rw [sum_filter]
  apply sum_congr rfl
  intro d _
  by_cases hd : δ d = 0
  · simp [hd]
  · rw [if_pos hd, sum_filter]
    apply sum_congr rfl
    intro a _
    by_cases ha : α a = 0
    · simp [ha]
    · rw [if_pos ha, sum_filter]
      apply sum_congr rfl
      intro b _
      by_cases hb : β b = 0
      · simp [hb]
      · rw [if_pos hb, sum_filter]
        apply sum_congr rfl
        intro c _
        by_cases hc : γ c = 0
        · simp [hc]
        · rw [if_pos hc]

theorem four_box_kernel_sum_nonzero_witness (D A B C : Finset ℕ)
    (δ α β γ H : ℕ → ℂ) (hne : fourBoxKernelSum D A B C δ α β γ H ≠ 0) :
    ∃ d ∈ D, ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C,
      δ d ≠ 0 ∧ α a ≠ 0 ∧ β b ≠ 0 ∧ γ c ≠ 0 ∧ H (d*a*b*c) ≠ 0 := by
  unfold fourBoxKernelSum at hne
  obtain ⟨d,hd,hdne⟩ := exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨a,ha,hane⟩ := exists_ne_zero_of_sum_ne_zero hdne
  obtain ⟨b,hb,hbne⟩ := exists_ne_zero_of_sum_ne_zero hane
  obtain ⟨c,hc,hcne⟩ := exists_ne_zero_of_sum_ne_zero hbne
  simp only [mul_ne_zero_iff] at hcne
  exact ⟨d,hd,a,ha,b,hb,c,hc,hcne.1.1.1.1,hcne.1.1.1.2,
    hcne.1.1.2,hcne.1.2,hcne.2⟩

theorem four_box_kernel_sum_eq_zero_of_no_nonzero_product (D A B C : Finset ℕ)
    (δ α β γ H : ℕ → ℂ)
    (hzero : ¬∃ d ∈ D, ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C,
      δ d ≠ 0 ∧ α a ≠ 0 ∧ β b ≠ 0 ∧ γ c ≠ 0) :
    fourBoxKernelSum D A B C δ α β γ H = 0 := by
  by_contra hne
  obtain ⟨d,hd,a,ha,b,hb,c,hc,hδ,hα,hβ,hγ,_⟩ :=
    four_box_kernel_sum_nonzero_witness D A B C δ α β γ H hne
  exact hzero ⟨d,hd,a,ha,b,hb,c,hc,hδ,hα,hβ,hγ⟩

theorem four_box_kernel_sum_swap_middle (D A B C : Finset ℕ)
    (δ α β γ H : ℕ → ℂ) :
    fourBoxKernelSum D A B C δ α β γ H =
      fourBoxKernelSum D B A C δ β α γ H := by
  unfold fourBoxKernelSum
  apply sum_congr rfl
  intro d _
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro c _
  have hn : d*a*b*c = d*b*a*c := by ring
  rw [hn]
  ring

end Bounty


-- Source module: ActualCutoffBoxWitness

/- Nonzero normalized rational boxes have actual coefficient witnesses in the common window. -/

open Finset

namespace Bounty

theorem rational_cutoff_box_nonzero_witness {Y : ℝ} (hY : 0 < Y)
    (r : ℕ) (k : ℤ) (D A B C : Finset ℕ) (δ α β γ : ℕ → ℂ) (t : ℝ)
    (hne : rationalFourBoxKernelSum r k D A B C δ α β γ
      (fun n => ((harmonicCommonCutoff ((n : ℝ)/Y)/(n : ℝ) : ℝ) : ℂ)*
        physicalMellinPhase t (n : ℝ)) ≠ 0) :
    ∃ d ∈ D, ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C,
      δ d ≠ 0 ∧ α a ≠ 0 ∧ β b ≠ 0 ∧ γ c ≠ 0 ∧
      d*a*b*c ∈ (harmonicCommonSupport Y).image Int.natAbs := by
  obtain ⟨d,hd,a,ha,b,hb,c,hc,hδ,hα,hβ,hγ,hH⟩ :=
    four_box_kernel_sum_nonzero_witness D A B C δ α β γ _ hne
  have hcut : harmonicCommonCutoff (((d*a*b*c : ℕ) : ℝ)/Y) ≠ 0 := by
    intro hz
    apply hH
    simp only [hz,zero_div,Complex.ofReal_zero,zero_mul]
  have hs := harmonic_common_cutoff_scaled_support hY hcut
  exact ⟨d,hd,a,ha,b,hb,c,hc,hδ,hα,hβ,hγ,
    (mem_harmonic_common_natural_support hY).mpr ⟨hs.1.le,hs.2.le⟩⟩

theorem rational_cutoff_box_eq_zero_of_no_supported_product {Y : ℝ} (hY : 0 < Y)
    (r : ℕ) (k : ℤ) (D A B C : Finset ℕ) (δ α β γ : ℕ → ℂ)
    (hzero : ¬∃ d ∈ D, ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C,
      δ d ≠ 0 ∧ α a ≠ 0 ∧ β b ≠ 0 ∧ γ c ≠ 0 ∧
      d*a*b*c ∈ (harmonicCommonSupport Y).image Int.natAbs) (t : ℝ) :
    rationalFourBoxKernelSum r k D A B C δ α β γ
      (fun n => ((harmonicCommonCutoff ((n : ℝ)/Y)/(n : ℝ) : ℝ) : ℂ)*
        physicalMellinPhase t (n : ℝ)) = 0 := by
  by_contra hne
  exact hzero (rational_cutoff_box_nonzero_witness hY r k D A B C δ α β γ t hne)

end Bounty


-- Source module: ActualDyadicFactorSupport

/- Exact dyadic clipping of the original rough and Type II factors, retaining the finite cap. -/

open Finset

namespace Bounty

theorem dyadicNatBucket_Icc_filter_roughBand_eq (N k : ℕ) (A B W : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (dyadicNatBucket (Icc 1 N) k).filter (fun n => n ∈ roughBand A B W) =
      roughBand (max A (originalDyadicBase k))
        (min B (min (N : ℝ) (2*originalDyadicBase k))) W := by
  classical
  rw [dyadicNatBucket_eq_real_interval (Icc 1 N) (fun n hn => (mem_Icc.mp hn).1)]
  ext n
  have hbase := originalDyadicBase_pos k
  have hupper : 0 ≤ min B (min (N : ℝ) (2*originalDyadicBase k)) := by positivity
  simp only [mem_filter, mem_Icc, mem_roughBand_real_iff hA hB,
    mem_roughBand_real_iff (le_max_of_le_left hA) hupper, max_lt_iff, le_min_iff]
  constructor
  · rintro ⟨⟨⟨hn1, hnN⟩, hnlo, hnhi⟩, hnA, hnB, hnrough⟩
    exact ⟨⟨hnA, hnlo⟩, ⟨hnB, by exact_mod_cast hnN, hnhi⟩, hnrough⟩
  · rintro ⟨⟨hnA, hnlo⟩, ⟨hnB, hnN, hnhi⟩, hnrough⟩
    have hnpos : 0 < n := by exact_mod_cast (hA.trans_lt hnA)
    exact ⟨⟨⟨hnpos, by exact_mod_cast hnN⟩, hnlo, hnhi⟩, hnA, hnB, hnrough⟩

theorem typeIIRestrict_dyadicNatBucket_Icc_Ioc (N k lo hi : ℕ) (f : ℕ → ℝ) :
    typeIIRestrict (dyadicNatBucket (Icc 1 N) k) (typeIIRestrict (Ioc lo hi) f) =
      typeIIRestrict
        (Ioc (max lo ((2 : ℕ)^k-1)) (min hi (min N ((2 : ℕ)^(k+1)-1)))) f := by
  rw [dyadicNatBucket_Icc_eq_Ioc]
  funext n
  simp only [typeIIRestrict, mem_Ioc, max_lt_iff, le_min_iff]
  split_ifs <;> simp_all

theorem dyadicNatBucket_Icc_filter_typeIIRestrict_ne_zero (N k lo hi : ℕ) (f : ℕ → ℝ) :
    (dyadicNatBucket (Icc 1 N) k).filter (fun n => (typeIIRestrict (Ioc lo hi) f n : ℂ) ≠ 0) =
      (Ioc (max lo ((2 : ℕ)^k-1)) (min hi (min N ((2 : ℕ)^(k+1)-1)))).filter
        (fun n => (typeIIRestrict
          (Ioc (max lo ((2 : ℕ)^k-1)) (min hi (min N ((2 : ℕ)^(k+1)-1)))) f n : ℂ) ≠ 0) := by
  classical
  rw [dyadicNatBucket_Icc_eq_Ioc]
  ext n
  simp only [mem_filter, ne_eq, Complex.ofReal_eq_zero, typeIIRestrict_ne_zero_iff,
    mem_Ioc, max_lt_iff, le_min_iff]
  tauto

theorem mem_clipped_dyadic_Ioc_real_bounds (N k lo hi n : ℕ)
    (hn : n ∈ Ioc (max lo ((2 : ℕ)^k-1)) (min hi (min N ((2 : ℕ)^(k+1)-1)))) :
    originalDyadicBase k < (n : ℝ) ∧ (n : ℝ) ≤ 2*originalDyadicBase k := by
  have hbucket : n ∈ dyadicNatBucket (Icc 1 N) k := by
    rw [dyadicNatBucket_Icc_eq_Ioc]
    simp only [mem_Ioc, max_lt_iff, le_min_iff] at hn ⊢
    exact ⟨hn.1.2, hn.2.2⟩
  rw [dyadicNatBucket_eq_real_interval (Icc 1 N) (fun m hm => (mem_Icc.mp hm).1)] at hbucket
  exact (mem_filter.mp hbucket).2

theorem dyadicNatBucket_Icc_roughBand_nonempty_endpoints (N k : ℕ) (A B W : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hne : ((dyadicNatBucket (Icc 1 N) k).filter (fun n => n ∈ roughBand A B W)).Nonempty) :
    max A (originalDyadicBase k) ≤ min B (min (N : ℝ) (2*originalDyadicBase k)) := by
  rw [dyadicNatBucket_Icc_filter_roughBand_eq N k A B W hA hB] at hne
  obtain ⟨n, hn⟩ := hne
  have hbase := originalDyadicBase_pos k
  have hupper : 0 ≤ min B (min (N : ℝ) (2*originalDyadicBase k)) := by positivity
  have hb := (mem_roughBand_real_iff (le_max_of_le_left hA) hupper n).mp hn
  exact hb.1.le.trans hb.2.1

end Bounty


-- Source module: ActualDyadicRationalBox

/- Exact support clipping and coordinate reordering for the original rational box. -/

open Finset

namespace Bounty

theorem actual_dyadic_rational_box_eq
    (N kP kM kQ kT lo hi r : ℕ) (aRat : ℤ) (Pband : Finset ℕ)
    (A B W : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (f : ℕ → ℝ) (δ θM θQ γ H : ℕ → ℂ) :
    rationalFourBoxKernelSum r aRat
      (dyadicNatBucket (Icc 1 N) kP) (dyadicNatBucket (Icc 1 N) kM)
      (dyadicNatBucket (Icc 1 N) kQ) (dyadicNatBucket (Icc 1 N) kT)
      (fun p => if p ∈ Pband then δ p else 0)
      (fun m => (typeIIRestrict (Ioc lo hi) f m : ℂ)*θM m)
      (fun q => if q ∈ roughBand A B W then θQ q else 0) γ H =
    rationalFourBoxKernelSum r aRat
      ((dyadicNatBucket (Icc 1 N) kP).filter (fun p => p ∈ Pband))
      (roughBand (max A (originalDyadicBase kQ))
        (min B (min (N : ℝ) (2*originalDyadicBase kQ))) W)
      ((Ioc (max lo ((2 : ℕ)^kM-1)) (min hi (min N ((2 : ℕ)^(kM+1)-1)))).filter
        (fun m => (typeIIRestrict
          (Ioc (max lo ((2 : ℕ)^kM-1)) (min hi (min N ((2 : ℕ)^(kM+1)-1)))) f m : ℂ) ≠ 0))
      (dyadicNatBucket (Icc 1 N) kT) δ θQ
      (fun m => (typeIIRestrict
        (Ioc (max lo ((2 : ℕ)^kM-1)) (min hi (min N ((2 : ℕ)^(kM+1)-1)))) f m : ℂ)*θM m)
      γ H := by
  classical
  have hM (m : ℕ) (hm : m ∈ dyadicNatBucket (Icc 1 N) kM) :
      typeIIRestrict
        (Ioc (max lo ((2 : ℕ)^kM-1)) (min hi (min N ((2 : ℕ)^(kM+1)-1)))) f m =
      typeIIRestrict (Ioc lo hi) f m := by
    have h := congrFun (typeIIRestrict_dyadicNatBucket_Icc_Ioc N kM lo hi f) m
    simpa only [typeIIRestrict, if_pos hm] using h.symm
  unfold rationalFourBoxKernelSum
  rw [four_box_kernel_sum_swap_middle]
  rw [← dyadicNatBucket_Icc_filter_roughBand_eq N kQ A B W hA hB,
    ← dyadicNatBucket_Icc_filter_typeIIRestrict_ne_zero N kM lo hi f]
  simp only [fourBoxKernelSum, sum_filter]
  apply sum_congr rfl
  intro p hp
  by_cases hpP : p ∈ Pband
  · simp only [hpP, if_true]
    apply sum_congr rfl
    intro q hq
    by_cases hqQ : q ∈ roughBand A B W
    · simp only [hqQ, if_true]
      apply sum_congr rfl
      intro m hm
      rw [hM m hm]
      by_cases hm0 : (typeIIRestrict (Ioc lo hi) f m : ℂ) = 0
      · simp only [hm0, ne_eq, not_true_eq_false, if_false, zero_mul, mul_zero,
          sum_const_zero]
      · simp only [hm0, ne_eq, not_false_eq_true, if_true]
    · simp only [hqQ, if_false, mul_zero, zero_mul, sum_const_zero]
  · simp only [hpP, if_false, zero_mul, sum_const_zero]

end Bounty


-- Source module: ActualDyadicPrimeBoxPrecision

/- The original masked dyadic prime box has arbitrary precision after the actual
common-cell width is imposed; its support and integral scales are derived. -/

open Finset Filter MeasureTheory

namespace Bounty.WeakZeroFree

theorem exists_actual_dyadic_prime_cutoff_integral_precision
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q cLog d : ℝ}
    (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1) (hcLog : 0 ≤ cLog) (hd : 0 < d) :
    ∃ J : ℕ, ∀ jStar : ℕ, J < jStar →
      ∀ (A : ℝ) (T : ℕ) (Tmod Sshift Cmod Sfreq Rmod W : ℝ),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, ∃ S₀ : ℝ, 0 ≤ S₀ ∧
      ∀ S : ℝ, S₀ ≤ S →
      ∀ᶠ L : ℝ in atTop,
      ∀ (r : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (tmarks umarks : candidatePIndices c L → ℕ) (big : Finset (candidatePIndices c L))
        (b : GroupMarkedLists (fun g : big => candidatePBand (c*L) g.val.val)
          (fun g : big => umarks g.val) → ℂ) (κ : ℕ → ℂ),
      (∀ g, tmarks g ≤ T) → (∀ l, ‖b l‖ ≤ L^B) → (∀ n, ‖κ n‖ ≤ 1) →
      ∀ (g : ℕ), g ∈ candidateSmallPIndices c L →
      ∀ (N kP kM kQ kT : ℕ) (Y R Hlocal : ℝ),
      1 ≤ Y → Real.exp (d*L) ≤ Y → Real.log Y ≤ cLog*L →
      0 ≤ R → 0 < Hlocal → 4096*Real.exp (L^(1/5 : ℝ))*L ≤ Hlocal →
      R ≤ 2*L*Y/Hlocal →
      ∀ (qP qT : ℕ) (χP : DirichletCharacter ℂ qP) (χT : DirichletCharacter ℂ qT)
        (τP τT : ℝ) (lo hi : ℕ),
      ∀ (κM ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      0 ≤ κM → κM ≤ 1/50 → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      ∀ qRat : ℕ, 0 < qRat → (qRat : ℝ) ≤ L^Rmod → ∀ aRat : ℤ,
      ∀ w : ℝ, |w| ≤ L^W →
      (∫ u in Set.Icc (-R) R,
        ‖rationalFourBoxKernelSum qRat aRat
          (dyadicNatBucket (Icc 1 N) kP) (dyadicNatBucket (Icc 1 N) kM)
          (dyadicNatBucket (Icc 1 N) kQ) (dyadicNatBucket (Icc 1 N) kT)
          (fun p => if p ∈ candidatePBand (c*L) g then
            (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
              (χP (p : ZMod qP)*typeIIPhase τP p) else 0)
          (fun n => (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ)*
            (χM (n : ZMod qM)*typeIIPhase ν n))
          (fun n => if n ∈ candidateRoughBand c L jStar then
            typeIIPhase σ n*χQ (n : ZMod qQ) else 0)
          (candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
            tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n))
          (fun n => ((harmonicCommonCutoff ((n : ℝ)/Y)/(n : ℝ) : ℝ) : ℂ)*
            physicalMellinPhase (u+w) (n : ℝ))‖^2) ≤ L^(-A) := by
  classical
  obtain ⟨J,hmain⟩ := exists_actual_retained_prime_cutoff_integral_precision
    hZ hc hq0 hq1 hcLog hd
  obtain ⟨Bcoeff,hBcoeff,hsmall⟩ := exists_candidate_small_prime_factor_data hc
  refine ⟨J,?_⟩
  intro jStar hjStar A T Tmod Sshift Cmod Sfreq Rmod W
  obtain ⟨C,hC,hprecision⟩ := hmain jStar hjStar A T Tmod Sshift Cmod Sfreq Rmod W
  refine ⟨C,hC,?_⟩
  intro B
  obtain ⟨S₀,hS₀,hbound⟩ := hprecision B
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [hbound S hS,hsmall,eventually_gt_atTop (0 : ℝ)] with L hdecay hsmallL hL
  intro r hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ g hg
    N kP kM kQ kT Y R Hlocal hY hYlo hYhi hR hHlocal hwidth hRwidth
    qP qT χP χT τP τT lo hi κM ν qM hqMInst χM hκM hκmax hqM hν
    σ qQ hqQInst χQ hqQ hσ qRat hqRat0 hqRat aRat w hw
  let PP := dyadicNatBucket (Icc 1 N) kP
  let QQ := dyadicNatBucket (Icc 1 N) kQ
  let MM := dyadicNatBucket (Icc 1 N) kM
  let TT := dyadicNatBucket (Icc 1 N) kT
  let a0 := Real.exp (c*L/2^jStar)
  let b0 := Real.exp ((6/5 : ℝ)*c*L/2^jStar)
  let qlo := max a0 (originalDyadicBase kQ)
  let qhi := min b0 (min (N : ℝ) (2*originalDyadicBase kQ))
  let ml := max lo ((2 : ℕ)^kM-1)
  let mh := min hi (min N ((2 : ℕ)^(kM+1)-1))
  let f := ambientPrimeTypeIIAlpha κM L S
  let ps := PP.filter (fun p => p ∈ candidatePBand (c*L) g)
  let qs := roughBand qlo qhi (Real.exp (Real.sqrt L))
  let ms := (Ioc ml mh).filter (fun n => (typeIIRestrict (Ioc ml mh) f n : ℂ) ≠ 0)
  let δ : ℕ → ℂ := fun p => (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
    (χP (p : ZMod qP)*typeIIPhase τP p)
  let α : ℕ → ℂ := fun n => typeIIPhase σ n*χQ (n : ZMod qQ)
  let β : ℕ → ℂ := fun n => (typeIIRestrict (Ioc ml mh) f n : ℂ)*
    (χM (n : ZMod qM)*typeIIPhase ν n)
  let γ := candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
    tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n)
  have heq (u : ℝ) := actual_dyadic_rational_box_eq N kP kM kQ kT lo hi qRat aRat
    (candidatePBand (c*L) g) a0 b0 (Real.exp (Real.sqrt L))
    (Real.exp_pos _).le (Real.exp_pos _).le f δ
    (fun n => χM (n : ZMod qM)*typeIIPhase ν n) α γ
    (fun n => ((harmonicCommonCutoff ((n : ℝ)/Y)/(n : ℝ) : ℝ) : ℂ)*
      physicalMellinPhase (u+w) (n : ℝ))
  change (∫ u in Set.Icc (-R) R,
    ‖rationalFourBoxKernelSum qRat aRat PP MM QQ TT
      (fun p => if p ∈ candidatePBand (c*L) g then δ p else 0)
      (fun n => (typeIIRestrict (Ioc lo hi) f n : ℂ)*
        (χM (n : ZMod qM)*typeIIPhase ν n))
      (fun n => if n ∈ roughBand a0 b0 (Real.exp (Real.sqrt L)) then α n else 0) γ
      (fun n => ((harmonicCommonCutoff ((n : ℝ)/Y)/(n : ℝ) : ℝ) : ℂ)*
        physicalMellinPhase (u+w) (n : ℝ))‖^2) ≤ L^(-A)
  suffices hgoal : (∫ u in Set.Icc (-R) R,
      ‖rationalFourBoxKernelSum qRat aRat ps qs ms TT δ α β γ
        (fun n => ((harmonicCommonCutoff ((n : ℝ)/Y)/(n : ℝ) : ℝ) : ℂ)*
          physicalMellinPhase (u+w) (n : ℝ))‖^2) ≤ L^(-A) by
    calc
      _ = (∫ u in Set.Icc (-R) R,
        ‖rationalFourBoxKernelSum qRat aRat ps qs ms TT δ α β γ
          (fun n => ((harmonicCommonCutoff ((n : ℝ)/Y)/(n : ℝ) : ℝ) : ℂ)*
            physicalMellinPhase (u+w) (n : ℝ))‖^2) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun u =>
            congrArg (fun z : ℂ => ‖z‖^2) (heq u))
      _ ≤ _ := hgoal
  by_cases hex : ∃ p ∈ ps, ∃ z ∈ qs, ∃ m ∈ ms, ∃ n ∈ TT,
      δ p ≠ 0 ∧ α z ≠ 0 ∧ β m ≠ 0 ∧ γ n ≠ 0 ∧
      p*z*m*n ∈ (harmonicCommonSupport Y).image Int.natAbs
  · obtain ⟨p,hp,z,hz,m,hm,n,hn,_,_,_,_,hwindow⟩ := hex
    have hqs : qs = QQ.filter (fun n => n ∈ candidateRoughBand c L jStar) := by
      exact (dyadicNatBucket_Icc_filter_roughBand_eq N kQ a0 b0
        (Real.exp (Real.sqrt L)) (Real.exp_pos _).le (Real.exp_pos _).le).symm
    have hms : ms = MM.filter (fun n => (typeIIRestrict (Ioc lo hi) f n : ℂ) ≠ 0) :=
      (dyadicNatBucket_Icc_filter_typeIIRestrict_ne_zero N kM lo hi f).symm
    have hpband : ps ⊆ candidatePBand (c*L) g := fun x hx => (mem_filter.mp hx).2
    have hpP : ps ⊆ PP := filter_subset _ _
    have hQbucket : qs ⊆ QQ := by rw [hqs]; exact filter_subset _ _
    have hmM : ms ⊆ MM := by rw [hms]; exact filter_subset _ _
    have hqband : qs ⊆ candidateRoughBand c L jStar := by
      intro x hx
      exact (mem_filter.mp (hqs ▸ hx)).2
    have hsp : ∀ x ∈ ps, originalDyadicBase kP ≤ (x : ℝ) ∧
        (x : ℝ) ≤ 2*originalDyadicBase kP := by
      intro x hx
      have hx' := hpP hx
      change x ∈ dyadicNatBucket (Icc 1 N) kP at hx'
      rw [dyadicNatBucket_eq_real_interval (Icc 1 N)
        (fun n hn => (mem_Icc.mp hn).1)] at hx'
      exact ⟨(mem_filter.mp hx').2.1.le,(mem_filter.mp hx').2.2⟩
    have hMband : ∀ x ∈ Ioc ml mh, originalDyadicBase kM ≤ (x : ℝ) ∧
        (x : ℝ) ≤ 2*originalDyadicBase kM := by
      intro x hx
      have h := mem_clipped_dyadic_Ioc_real_bounds N kM lo hi x hx
      exact ⟨h.1.le,h.2⟩
    have hTband : ∀ x ∈ TT, (2 : ℝ)^kT ≤ (x : ℝ) ∧ (x : ℝ) ≤ 2*(2 : ℝ)^kT := by
      intro x hx
      obtain ⟨hl,hu⟩ := dyadicNatBucket_bounds (Icc 1 N) (fun n hn => (mem_Icc.mp hn).1) hx
      constructor
      · exact_mod_cast hl
      · have hu' : (x : ℝ) ≤ (2 : ℝ)^(kT+1) := by exact_mod_cast hu.le
        simpa only [pow_succ,mul_comm] using hu'
    have hQorder : qlo ≤ qhi := dyadicNatBucket_Icc_roughBand_nonempty_endpoints
      N kQ a0 b0 (Real.exp (Real.sqrt L)) (Real.exp_pos _).le (Real.exp_pos _).le
      ⟨z,by change z ∈ QQ.filter (fun n => n ∈ candidateRoughBand c L jStar); rw [← hqs]; exact hz⟩
    have hPupper := (hsmallL g hg ps (originalDyadicBase kP) hpband ⟨p,hp⟩ hsp).2.2.1
    have hwidthP : 4096*originalDyadicBase kP*L ≤ Hlocal :=
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPupper (by norm_num)) hL.le).trans hwidth
    have hretained : retainedFourDyadicBox ((harmonicCommonSupport Y).image Int.natAbs)
        N kP kQ kM kT := ⟨p,hpP hp,z,hQbucket hz,m,hmM hm,n,hn,hwindow⟩
    have hprod : ∀ p ∈ ps, ∀ z ∈ qs, ∀ m ∈ ms, ∀ n ∈ TT,
        Y/128 ≤ ((p*z*m*n : ℕ) : ℝ) ∧ ((p*z*m*n : ℕ) : ℝ) ≤ 64*Real.exp 2*Y := by
      intro p hp z hz m hm n hn
      exact retained_harmonic_four_dyadic_product_bounds (zero_lt_one.trans_le hY)
        hretained (hpP hp) (hQbucket hz) (hmM hm) hn
    have hresult := @hdecay r hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ g hg
      ps Y (originalDyadicBase kP) R Hlocal hpband hY hYlo hYhi hR hHlocal hwidthP hRwidth hsp
      qP qT χP χT τP τT ml mh TT (originalDyadicBase kM) ((2 : ℝ)^kT)
      (originalDyadicBase_pos kM) (one_le_pow₀ (by norm_num)) hMband hTband
      κM ν qM hqMInst χM hκM hκmax hqM hν
      (originalDyadicBase kQ) qlo qhi σ qQ hqQInst χQ (originalDyadicBase_pos kQ)
      (le_max_right _ _) hQorder (min_le_of_right_le (min_le_right _ _)) hqband hqQ hσ
      ⟨p,hp,z,hz,m,hm,n,hn,hwindow⟩ hprod qRat hqRat0 hqRat aRat w hw
    simpa only [ps,qs,ms,TT,δ,α,β,γ,f,mul_assoc] using hresult
  · have hz (u : ℝ) := rational_cutoff_box_eq_zero_of_no_supported_product
      (zero_lt_one.trans_le hY) qRat aRat ps qs ms TT δ α β γ hex (u+w)
    simp_rw [hz]
    simpa only [norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0),integral_zero]
      using (Real.rpow_nonneg hL.le (-A))

end Bounty.WeakZeroFree


-- Source module: ActualDyadicRoughBoxPrecision

/- The original masked dyadic rough box has arbitrary precision after the actual
common-cell width is imposed; its support and integral scales are derived. -/

open Finset Filter MeasureTheory

namespace Bounty.WeakZeroFree

theorem exists_actual_dyadic_rough_cutoff_integral_precision
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q cLog d γrough vMax ρ : ℝ}
    (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1) (hcLog : 0 ≤ cLog) (hd : 0 < d)
    (hγ : 0 < γrough) (hv : vMax < 1) (hρ : 0 < ρ) :
    ∃ J : ℕ, ∀ jStar : ℕ, J < jStar →
      ∀ (A : ℝ) (T : ℕ) (Tmod Sshift Cmod Sfreq Rmod W : ℝ),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, ∃ S₀ : ℝ, 0 ≤ S₀ ∧
      ∀ S : ℝ, S₀ ≤ S →
      ∀ᶠ L : ℝ in atTop,
      ∀ (r : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (tmarks umarks : candidatePIndices c L → ℕ) (big : Finset (candidatePIndices c L))
        (b : GroupMarkedLists (fun g : big => candidatePBand (c*L) g.val.val)
          (fun g : big => umarks g.val) → ℂ) (κ : ℕ → ℂ),
      (∀ g, tmarks g ≤ T) → (∀ l, ‖b l‖ ≤ L^B) → (∀ n, ‖κ n‖ ≤ 1) →
      ∀ (g : ℕ), g ∈ candidateSmallPIndices c L →
      ∀ (N kP kM kQ kT : ℕ) (Y R Hlocal : ℝ),
      1 ≤ Y → Real.exp (d*L) ≤ Y → Real.log Y ≤ cLog*L →
      0 ≤ R → 0 < Hlocal → 4096*Real.exp (L^(1/5 : ℝ))*L ≤ Hlocal →
      R ≤ 2*L*Y/Hlocal →
      ∀ (qP qT : ℕ) (χP : DirichletCharacter ℂ qP) (χT : DirichletCharacter ℂ qT)
        (τP τT : ℝ) (lo hi : ℕ),
      ∀ (aM v ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      v ≤ vMax → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      ∀ qRat : ℕ, 0 < qRat → (qRat : ℝ) ≤ L^Rmod → ∀ aRat : ℤ,
      ∀ w : ℝ, |w| ≤ L^W →
      (∫ u in Set.Icc (-R) R,
        ‖rationalFourBoxKernelSum qRat aRat
          (dyadicNatBucket (Icc 1 N) kP) (dyadicNatBucket (Icc 1 N) kM)
          (dyadicNatBucket (Icc 1 N) kQ) (dyadicNatBucket (Icc 1 N) kT)
          (fun p => if p ∈ candidatePBand (c*L) g then
            (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
              (χP (p : ZMod qP)*typeIIPhase τP p) else 0)
          (fun n => (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM v) n : ℂ)*
            (χM (n : ZMod qM)*typeIIPhase ν n))
          (fun n => if n ∈ candidateRoughBand c L jStar then
            typeIIPhase σ n*χQ (n : ZMod qQ) else 0)
          (candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
            tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n))
          (fun n => ((harmonicCommonCutoff ((n : ℝ)/Y)/(n : ℝ) : ℝ) : ℂ)*
            physicalMellinPhase (u+w) (n : ℝ))‖^2) ≤ L^(-A) := by
  classical
  obtain ⟨J,hmain⟩ := exists_actual_retained_rough_cutoff_integral_precision
    hZ hc hq0 hq1 hcLog hd hγ hv hρ
  obtain ⟨Bcoeff,hBcoeff,hsmall⟩ := exists_candidate_small_prime_factor_data hc
  refine ⟨J,?_⟩
  intro jStar hjStar A T Tmod Sshift Cmod Sfreq Rmod W
  obtain ⟨C,hC,hprecision⟩ := hmain jStar hjStar A T Tmod Sshift Cmod Sfreq Rmod W
  refine ⟨C,hC,?_⟩
  intro B
  obtain ⟨S₀,hS₀,hbound⟩ := hprecision B
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [hbound S hS,hsmall,eventually_gt_atTop (0 : ℝ)] with L hdecay hsmallL hL
  intro r hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ g hg
    N kP kM kQ kT Y R Hlocal hY hYlo hYhi hR hHlocal hwidth hRwidth
    qP qT χP χT τP τT lo hi aM v ν qM hqMInst χM hvM hqM hν
    σ qQ hqQInst χQ hqQ hσ qRat hqRat0 hqRat aRat w hw
  let PP := dyadicNatBucket (Icc 1 N) kP
  let QQ := dyadicNatBucket (Icc 1 N) kQ
  let MM := dyadicNatBucket (Icc 1 N) kM
  let TT := dyadicNatBucket (Icc 1 N) kT
  let a0 := Real.exp (c*L/2^jStar)
  let b0 := Real.exp ((6/5 : ℝ)*c*L/2^jStar)
  let qlo := max a0 (originalDyadicBase kQ)
  let qhi := min b0 (min (N : ℝ) (2*originalDyadicBase kQ))
  let ml := max lo ((2 : ℕ)^kM-1)
  let mh := min hi (min N ((2 : ℕ)^(kM+1)-1))
  let f := ambientRoughIntervalTypeIIAlpha γrough L S aM v
  let ps := PP.filter (fun p => p ∈ candidatePBand (c*L) g)
  let qs := roughBand qlo qhi (Real.exp (Real.sqrt L))
  let ms := (Ioc ml mh).filter (fun n => (typeIIRestrict (Ioc ml mh) f n : ℂ) ≠ 0)
  let δ : ℕ → ℂ := fun p => (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
    (χP (p : ZMod qP)*typeIIPhase τP p)
  let α : ℕ → ℂ := fun n => typeIIPhase σ n*χQ (n : ZMod qQ)
  let β : ℕ → ℂ := fun n => (typeIIRestrict (Ioc ml mh) f n : ℂ)*
    (χM (n : ZMod qM)*typeIIPhase ν n)
  let γ := candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
    tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n)
  have heq (u : ℝ) := actual_dyadic_rational_box_eq N kP kM kQ kT lo hi qRat aRat
    (candidatePBand (c*L) g) a0 b0 (Real.exp (Real.sqrt L))
    (Real.exp_pos _).le (Real.exp_pos _).le f δ
    (fun n => χM (n : ZMod qM)*typeIIPhase ν n) α γ
    (fun n => ((harmonicCommonCutoff ((n : ℝ)/Y)/(n : ℝ) : ℝ) : ℂ)*
      physicalMellinPhase (u+w) (n : ℝ))
  change (∫ u in Set.Icc (-R) R,
    ‖rationalFourBoxKernelSum qRat aRat PP MM QQ TT
      (fun p => if p ∈ candidatePBand (c*L) g then δ p else 0)
      (fun n => (typeIIRestrict (Ioc lo hi) f n : ℂ)*
        (χM (n : ZMod qM)*typeIIPhase ν n))
      (fun n => if n ∈ roughBand a0 b0 (Real.exp (Real.sqrt L)) then α n else 0) γ
      (fun n => ((harmonicCommonCutoff ((n : ℝ)/Y)/(n : ℝ) : ℝ) : ℂ)*
        physicalMellinPhase (u+w) (n : ℝ))‖^2) ≤ L^(-A)
  suffices hgoal : (∫ u in Set.Icc (-R) R,
      ‖rationalFourBoxKernelSum qRat aRat ps qs ms TT δ α β γ
        (fun n => ((harmonicCommonCutoff ((n : ℝ)/Y)/(n : ℝ) : ℝ) : ℂ)*
          physicalMellinPhase (u+w) (n : ℝ))‖^2) ≤ L^(-A) by
    calc
      _ = (∫ u in Set.Icc (-R) R,
        ‖rationalFourBoxKernelSum qRat aRat ps qs ms TT δ α β γ
          (fun n => ((harmonicCommonCutoff ((n : ℝ)/Y)/(n : ℝ) : ℝ) : ℂ)*
            physicalMellinPhase (u+w) (n : ℝ))‖^2) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun u =>
            congrArg (fun z : ℂ => ‖z‖^2) (heq u))
      _ ≤ _ := hgoal
  by_cases hex : ∃ p ∈ ps, ∃ z ∈ qs, ∃ m ∈ ms, ∃ n ∈ TT,
      δ p ≠ 0 ∧ α z ≠ 0 ∧ β m ≠ 0 ∧ γ n ≠ 0 ∧
      p*z*m*n ∈ (harmonicCommonSupport Y).image Int.natAbs
  · obtain ⟨p,hp,z,hz,m,hm,n,hn,_,_,_,_,hwindow⟩ := hex
    have hqs : qs = QQ.filter (fun n => n ∈ candidateRoughBand c L jStar) := by
      exact (dyadicNatBucket_Icc_filter_roughBand_eq N kQ a0 b0
        (Real.exp (Real.sqrt L)) (Real.exp_pos _).le (Real.exp_pos _).le).symm
    have hms : ms = MM.filter (fun n => (typeIIRestrict (Ioc lo hi) f n : ℂ) ≠ 0) :=
      (dyadicNatBucket_Icc_filter_typeIIRestrict_ne_zero N kM lo hi f).symm
    have hpband : ps ⊆ candidatePBand (c*L) g := fun x hx => (mem_filter.mp hx).2
    have hpP : ps ⊆ PP := filter_subset _ _
    have hQbucket : qs ⊆ QQ := by rw [hqs]; exact filter_subset _ _
    have hmM : ms ⊆ MM := by rw [hms]; exact filter_subset _ _
    have hqband : qs ⊆ candidateRoughBand c L jStar := by
      intro x hx
      exact (mem_filter.mp (hqs ▸ hx)).2
    have hsp : ∀ x ∈ ps, originalDyadicBase kP ≤ (x : ℝ) ∧
        (x : ℝ) ≤ 2*originalDyadicBase kP := by
      intro x hx
      have hx' := hpP hx
      change x ∈ dyadicNatBucket (Icc 1 N) kP at hx'
      rw [dyadicNatBucket_eq_real_interval (Icc 1 N)
        (fun n hn => (mem_Icc.mp hn).1)] at hx'
      exact ⟨(mem_filter.mp hx').2.1.le,(mem_filter.mp hx').2.2⟩
    have hMband : ∀ x ∈ Ioc ml mh, originalDyadicBase kM ≤ (x : ℝ) ∧
        (x : ℝ) ≤ 2*originalDyadicBase kM := by
      intro x hx
      have h := mem_clipped_dyadic_Ioc_real_bounds N kM lo hi x hx
      exact ⟨h.1.le,h.2⟩
    have hTband : ∀ x ∈ TT, (2 : ℝ)^kT ≤ (x : ℝ) ∧ (x : ℝ) ≤ 2*(2 : ℝ)^kT := by
      intro x hx
      obtain ⟨hl,hu⟩ := dyadicNatBucket_bounds (Icc 1 N) (fun n hn => (mem_Icc.mp hn).1) hx
      constructor
      · exact_mod_cast hl
      · have hu' : (x : ℝ) ≤ (2 : ℝ)^(kT+1) := by exact_mod_cast hu.le
        simpa only [pow_succ,mul_comm] using hu'
    have hQorder : qlo ≤ qhi := dyadicNatBucket_Icc_roughBand_nonempty_endpoints
      N kQ a0 b0 (Real.exp (Real.sqrt L)) (Real.exp_pos _).le (Real.exp_pos _).le
      ⟨z,by change z ∈ QQ.filter (fun n => n ∈ candidateRoughBand c L jStar); rw [← hqs]; exact hz⟩
    have hPupper := (hsmallL g hg ps (originalDyadicBase kP) hpband ⟨p,hp⟩ hsp).2.2.1
    have hwidthP : 4096*originalDyadicBase kP*L ≤ Hlocal :=
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPupper (by norm_num)) hL.le).trans hwidth
    have hretained : retainedFourDyadicBox ((harmonicCommonSupport Y).image Int.natAbs)
        N kP kQ kM kT := ⟨p,hpP hp,z,hQbucket hz,m,hmM hm,n,hn,hwindow⟩
    have hprod : ∀ p ∈ ps, ∀ z ∈ qs, ∀ m ∈ ms, ∀ n ∈ TT,
        Y/128 ≤ ((p*z*m*n : ℕ) : ℝ) ∧ ((p*z*m*n : ℕ) : ℝ) ≤ 64*Real.exp 2*Y := by
      intro p hp z hz m hm n hn
      exact retained_harmonic_four_dyadic_product_bounds (zero_lt_one.trans_le hY)
        hretained (hpP hp) (hQbucket hz) (hmM hm) hn
    have hresult := @hdecay r hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ g hg
      ps Y (originalDyadicBase kP) R Hlocal hpband hY hYlo hYhi hR hHlocal hwidthP hRwidth hsp
      qP qT χP χT τP τT ml mh TT (originalDyadicBase kM) ((2 : ℝ)^kT)
      (originalDyadicBase_pos kM) (one_le_pow₀ (by norm_num)) hMband hTband
      aM v ν qM hqMInst χM hvM hqM hν
      (originalDyadicBase kQ) qlo qhi σ qQ hqQInst χQ (originalDyadicBase_pos kQ)
      (le_max_right _ _) hQorder (min_le_of_right_le (min_le_right _ _)) hqband hqQ hσ
      ⟨p,hp,z,hz,m,hm,n,hn,hwindow⟩ hprod qRat hqRat0 hqRat aRat w hw
    simpa only [ps,qs,ms,TT,δ,α,β,γ,f,mul_assoc] using hresult
  · have hz (u : ℝ) := rational_cutoff_box_eq_zero_of_no_supported_product
      (zero_lt_one.trans_le hY) qRat aRat ps qs ms TT δ α β γ hex (u+w)
    simp_rw [hz]
    simpa only [norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0),integral_zero]
      using (Real.rpow_nonneg hL.le (-A))

end Bounty.WeakZeroFree


-- Source module: ActualSourceBoxBridge

/- Exact rational-center identification and compact-interval integrability for
full dyadic boxes in the common harmonic source. The Fourier sign is positive. -/

open Finset MeasureTheory

namespace Bounty

theorem common_source_four_dyadic_box_eq_rational
    (N : ℕ) (δ α β γ : ℕ → ℂ) (Y a v : ℝ) (aRat : ℤ) (qRat : ℕ)
    (t : ℝ) (i j k l : ℕ) :
    fourDyadicBoxSum N δ α β γ
      (commonSourceBoxKernel Y a v ((aRat : ℝ)/qRat) t) i j k l =
    rationalFourBoxKernelSum qRat aRat
      (dyadicNatBucket (Icc 1 N) i) (dyadicNatBucket (Icc 1 N) j)
      (dyadicNatBucket (Icc 1 N) k) (dyadicNatBucket (Icc 1 N) l) δ α β γ
      (fun n => ((harmonicCommonCutoff ((n : ℝ)/Y)/(n : ℝ) : ℝ) : ℂ)*
        physicalMellinPhase (t+(-(a+v))) (n : ℝ)) := by
  have ht : t-a-v = t+(-(a+v)) := by ring
  simp only [fourDyadicBoxSum,commonSourceBoxKernel,rationalFourBoxKernelSum,
    fourBoxKernelSum,Complex.ofReal_div,Complex.ofReal_natCast,ht,mul_assoc]

theorem continuous_common_source_four_dyadic_box
    (N : ℕ) (δ α β γ : ℕ → ℂ) (Y a v center : ℝ) (i j k l : ℕ) :
    Continuous (fun t => fourDyadicBoxSum N δ α β γ
      (commonSourceBoxKernel Y a v center t) i j k l) := by
  unfold fourDyadicBoxSum commonSourceBoxKernel physicalMellinPhase
  fun_prop

theorem common_source_four_dyadic_box_integrable_norm_sq
    (N : ℕ) (δ α β γ : ℕ → ℂ) (Y a v center R : ℝ) (i j k l : ℕ) :
    Integrable (fun t => ‖fourDyadicBoxSum N δ α β γ
      (commonSourceBoxKernel Y a v center t) i j k l‖^2)
      (volume.restrict {t : ℝ | |t| ≤ R}) := by
  have hset : {t : ℝ | |t| ≤ R} = Set.Icc (-R) R := by
    ext t
    exact (abs_le : |t| ≤ R ↔ -R ≤ t ∧ t ≤ R)
  rw [hset]
  exact ((continuous_common_source_four_dyadic_box N δ α β γ Y a v center i j k l).norm.pow 2).integrableOn_Icc

end Bounty


-- Source module: ActualPrimeSourceFourier

/- Rational-centered Fourier decay for the original prime source, with explicit
source energy and exact convolution identification retained as inputs. -/

open Finset Filter MeasureTheory

namespace Bounty.WeakZeroFree

theorem exists_actual_prime_source_fourier_precision
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q d : ℝ}
    (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1) (hd : 0 < d) :
    ∃ J : ℕ, ∀ jStar : ℕ, J < jStar →
      ∀ (A E : ℝ) (T : ℕ) (Tmod Sshift Cmod Sfreq Rmod W : ℝ),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, ∃ S₀ : ℝ, 0 ≤ S₀ ∧
      ∀ S : ℝ, S₀ ≤ S →
      ∀ᶠ L : ℝ in atTop,
      ∀ (r : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (tmarks umarks : candidatePIndices c L → ℕ) (big : Finset (candidatePIndices c L))
        (b : GroupMarkedLists (fun g : big => candidatePBand (c*L) g.val.val)
          (fun g : big => umarks g.val) → ℂ) (κ : ℕ → ℂ),
      (∀ g, tmarks g ≤ T) → (∀ l, ‖b l‖ ≤ L^B) → (∀ n, ‖κ n‖ ≤ 1) →
      ∀ (g : ℕ), g ∈ candidateSmallPIndices c L →
      ∀ (Y H Z a v : ℝ) (F : ℤ → ℂ),
      Real.exp (d*L) ≤ Y → Real.log Y ≤ 6*L →
      4096*Real.exp (L^(1/5 : ℝ))*L ≤ H → H ≤ Real.exp ((d/2)*L) →
      0 < Z → |a| ≤ L^W → |v| ≤ L^W →
      ∀ (qP qT : ℕ) (χP : DirichletCharacter ℂ qP) (χT : DirichletCharacter ℂ qT)
        (τP τT : ℝ) (lo hi : ℕ),
      ∀ (κM ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      0 ≤ κM → κM ≤ 1/50 → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      ∀ qRat : ℕ, 0 < qRat → (qRat : ℝ) ≤ L^Rmod → ∀ aRat : ℤ,
      let δ : ℕ → ℂ := fun p => if p ∈ candidatePBand (c*L) g then
        (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
          (χP (p : ZMod qP)*typeIIPhase τP p) else 0
      let α : ℕ → ℂ := fun n =>
        (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ)*
          (χM (n : ZMod qM)*typeIIPhase ν n)
      let β : ℕ → ℂ := fun n => if n ∈ candidateRoughBand c L jStar then
        typeIIPhase σ n*χQ (n : ZMod qQ) else 0
      let γ := candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
        tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n)
      (∀ n ∈ (harmonicCommonSupport Y).image Int.natAbs,
        F n = endpointFourConvolution δ α β γ n) →
      (∑ n ∈ harmonicCommonSupport Y, ‖harmonicCellSource Y Z a v F n‖^2) ≤ Y*L^E →
      (∫ x in Set.Icc ((aRat : ℝ)/qRat-1/H) ((aRat : ℝ)/qRat+1/H),
        ‖finiteFourierSum (harmonicCommonSupport Y) (harmonicCellSource Y Z a v F) x‖^2)
        ≤ Y*L^(-A) := by
  obtain ⟨J,hmain⟩ := exists_actual_dyadic_prime_cutoff_integral_precision
    (cLog := 6) hZ hc hq0 hq1 (by norm_num) hd
  refine ⟨J,?_⟩
  intro jStar hjStar A E T Tmod Sshift Cmod Sfreq Rmod W
  obtain ⟨D,hD,hfourier⟩ := eventually_common_source_fourier_of_boxes hd A E
  obtain ⟨C,hC,hprecision⟩ := hmain jStar hjStar D T Tmod Sshift Cmod Sfreq Rmod (W+1)
  refine ⟨C,hC,?_⟩
  intro B
  obtain ⟨S₀,hS₀,hbound⟩ := hprecision B
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [hbound S hS,hfourier,eventually_ge_atTop (2 : ℝ)] with L hdecay hsource hL
  intro r hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ g hg
    Y H Z a v F hYlo hYhi hwidth hHupper hZpos ha hv
    qP qT χP χT τP τT lo hi κM ν qM hqMInst χM hκM hκmax hqM hν
    σ qQ hqQInst χQ hqQ hσ qRat hqRat0 hqRat aRat δ α β γ hF hEs
  have hLpos : 0 < L := by linarith
  have hY1 : 1 ≤ Y :=
    (Real.one_le_exp (mul_nonneg hd.le hLpos.le)).trans hYlo
  have hYpos : 0 < Y := zero_lt_one.trans_le hY1
  have hexp : 1 ≤ Real.exp (L^(1/5 : ℝ)) :=
    Real.one_le_exp (Real.rpow_nonneg hLpos.le _)
  have hH1 : 1 ≤ H := by
    calc
      1 ≤ 4096*1*2 := by norm_num
      _ ≤ 4096*Real.exp (L^(1/5 : ℝ))*L :=
        mul_le_mul (mul_le_mul_of_nonneg_left hexp (by norm_num)) hL (by norm_num) (by positivity)
      _ ≤ H := hwidth
  have hHpos : 0 < H := zero_lt_one.trans_le hH1
  have hw : |-(a+v)| ≤ L^(W+1) := by
    rw [abs_neg,Real.rpow_add hLpos,Real.rpow_one]
    calc
      |a+v| ≤ |a|+|v| := abs_add_le a v
      _ ≤ L^W+L^W := add_le_add ha hv
      _ = L^W*2 := by ring
      _ ≤ L^W*L := mul_le_mul_of_nonneg_left hL (Real.rpow_nonneg hLpos.le W)
  have hR : 0 ≤ L*Y/H := (div_pos (mul_pos hLpos hYpos) hHpos).le
  have hRwidth : L*Y/H ≤ 2*L*Y/H := by
    calc
      L*Y/H ≤ 2*(L*Y/H) := by linarith
      _ = 2*L*Y/H := by ring
  apply hsource Y H Z a v ((aRat : ℝ)/qRat) F δ α β γ
    hYlo hYhi hH1 hHupper hZpos hF hEs
  · intro i hiIdx j hjIdx k hk l hl hretained
    exact common_source_four_dyadic_box_integrable_norm_sq
      _ δ α β γ Y a v ((aRat : ℝ)/qRat) (L*Y/H) i j k l
  · intro i hiIdx j hjIdx k hk l hl hretained
    let N := ⌈4*Real.exp 2*Y⌉₊
    have hb := @hdecay r hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ g hg
      N i j k l Y (L*Y/H) H hY1 hYlo hYhi hR hHpos hwidth hRwidth
      qP qT χP χT τP τT lo hi κM ν qM hqMInst χM hκM hκmax hqM hν
      σ qQ hqQInst χQ hqQ hσ qRat hqRat0 hqRat aRat (-(a+v)) hw
    have hset : {t : ℝ | |t| ≤ L*Y/H} = Set.Icc (-(L*Y/H)) (L*Y/H) := by
      ext t
      simp only [Set.mem_ofPred_eq,Set.mem_Icc,abs_le]
    rw [hset]
    calc
      _ = (∫ t in Set.Icc (-(L*Y/H)) (L*Y/H),
        ‖rationalFourBoxKernelSum qRat aRat
          (dyadicNatBucket (Icc 1 N) i) (dyadicNatBucket (Icc 1 N) j)
          (dyadicNatBucket (Icc 1 N) k) (dyadicNatBucket (Icc 1 N) l)
          δ α β γ
          (fun n => ((harmonicCommonCutoff ((n : ℝ)/Y)/(n : ℝ) : ℝ) : ℂ)*
            physicalMellinPhase (t+(-(a+v))) (n : ℝ))‖^2) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun t => congrArg (fun z : ℂ => ‖z‖^2)
            (common_source_four_dyadic_box_eq_rational N δ α β γ Y a v aRat qRat t i j k l))
      _ ≤ L^(-D) := hb

end Bounty.WeakZeroFree


-- Source module: ActualRoughSourceFourier

/- Rational-centered source Fourier decay for the original rough coefficient,
with the source energy and exact endpoint convolution retained explicitly. -/

open Finset Filter MeasureTheory

namespace Bounty.WeakZeroFree

theorem exists_actual_rough_source_fourier_precision
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c q d γrough vMax ρ : ℝ}
    (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1) (hd : 0 < d)
    (hγ : 0 < γrough) (hv : vMax < 1) (hρ : 0 < ρ) :
    ∃ J : ℕ, ∀ jStar : ℕ, J < jStar →
      ∀ (A E : ℝ) (T : ℕ) (Tmod Sshift Cmod Sfreq Rmod W : ℝ),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, ∃ S₀ : ℝ, 0 ≤ S₀ ∧
      ∀ S : ℝ, S₀ ≤ S →
      ∀ᶠ L : ℝ in atTop,
      ∀ (r : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (tmarks umarks : candidatePIndices c L → ℕ) (big : Finset (candidatePIndices c L))
        (b : GroupMarkedLists (fun g : big => candidatePBand (c*L) g.val.val)
          (fun g : big => umarks g.val) → ℂ) (κ : ℕ → ℂ),
      (∀ g, tmarks g ≤ T) → (∀ l, ‖b l‖ ≤ L^B) → (∀ n, ‖κ n‖ ≤ 1) →
      ∀ (g : ℕ), g ∈ candidateSmallPIndices c L →
      ∀ (Y H Z a v : ℝ) (F : ℤ → ℂ),
      Real.exp (d*L) ≤ Y → Real.log Y ≤ 6*L →
      4096*Real.exp (L^(1/5 : ℝ))*L ≤ H → H ≤ Real.exp ((d/2)*L) →
      0 < Z → |a| ≤ L^W → |v| ≤ L^W →
      ∀ (qP qT : ℕ) (χP : DirichletCharacter ℂ qP) (χT : DirichletCharacter ℂ qT)
        (τP τT : ℝ) (lo hi : ℕ),
      ∀ (aM vM ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      vM ≤ vMax → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      ∀ qRat : ℕ, 0 < qRat → (qRat : ℝ) ≤ L^Rmod → ∀ aRat : ℤ,
      let δ : ℕ → ℂ := fun p => if p ∈ candidatePBand (c*L) g then
        (1/(((∑ p ∈ candidatePBand (c*L) g, 1/(p : ℝ)) : ℝ) : ℂ))*
          (χP (p : ZMod qP)*typeIIPhase τP p) else 0
      let α : ℕ → ℂ := fun n =>
        (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM vM) n : ℂ)*
          (χM (n : ZMod qM)*typeIIPhase ν n)
      let β : ℕ → ℂ := fun n => if n ∈ candidateRoughBand c L jStar then
        typeIIPhase σ n*χQ (n : ZMod qQ) else 0
      let γ := candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
        tmarks umarks big b κ (fun n => χT (n : ZMod qT)*typeIIPhase τT n)
      (∀ n ∈ (harmonicCommonSupport Y).image Int.natAbs,
        F n = endpointFourConvolution δ α β γ n) →
      (∑ n ∈ harmonicCommonSupport Y, ‖harmonicCellSource Y Z a v F n‖^2) ≤ Y*L^E →
      (∫ x in Set.Icc ((aRat : ℝ)/qRat-1/H) ((aRat : ℝ)/qRat+1/H),
        ‖finiteFourierSum (harmonicCommonSupport Y) (harmonicCellSource Y Z a v F) x‖^2)
        ≤ Y*L^(-A) := by
  obtain ⟨J,hmain⟩ := exists_actual_dyadic_rough_cutoff_integral_precision
    (cLog := 6) hZ hc hq0 hq1 (by norm_num) hd hγ hv hρ
  refine ⟨J,?_⟩
  intro jStar hjStar A E T Tmod Sshift Cmod Sfreq Rmod W
  obtain ⟨D,hAD,hsource⟩ := eventually_common_source_fourier_of_boxes hd A E
  obtain ⟨C,hC,hprecision⟩ := hmain jStar hjStar D T Tmod Sshift Cmod Sfreq Rmod (W+1)
  refine ⟨C,hC,?_⟩
  intro B
  obtain ⟨S₀,hS₀,hbound⟩ := hprecision B
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [hbound S hS,hsource,eventually_ge_atTop (2 : ℝ)] with L hbox hsource hL
  intro r hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ g hg
    Y H Z a v F hY hlog hwidth hHu hZpos ha hvPhase
    qP qT χP χT τP τT lo hi aM vM ν qM hqMInst χM hvM hqM hν
    σ qQ hqQInst χQ hqQ hσ qRat hqRat0 hqRat aRat δ α β γ hF hEs
  have hLp : 0 < L := by linarith
  have hY1 : 1 ≤ Y := (Real.one_le_exp (by positivity : 0 ≤ d*L)).trans hY
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hexp : 1 ≤ Real.exp (L^(1/5 : ℝ)) :=
    Real.one_le_exp (Real.rpow_nonneg hLp.le _)
  have hH : 1 ≤ H := by
    nlinarith [mul_le_mul_of_nonneg_right hexp hLp.le]
  have hHp : 0 < H := zero_lt_one.trans_le hH
  have hR : 0 ≤ L*Y/H := by positivity
  have hRwidth : L*Y/H ≤ 2*L*Y/H := by
    apply div_le_div_of_nonneg_right _ hHp.le
    nlinarith [mul_nonneg hLp.le hYp.le]
  have hw : |-(a+v)| ≤ L^(W+1) := by
    rw [abs_neg,Real.rpow_add hLp,Real.rpow_one]
    have hp : 0 < L^W := Real.rpow_pos_of_pos hLp W
    exact (abs_add_le a v).trans ((add_le_add ha hvPhase).trans (by nlinarith [mul_le_mul_of_nonneg_left hL hp.le]))
  apply hsource Y H Z a v ((aRat : ℝ)/qRat) F δ α β γ hY hlog hH hHu hZpos hF hEs
  · intro kP hkP kM hkM kQ hkQ kT hkT hretained
    exact common_source_four_dyadic_box_integrable_norm_sq
      ⌈4*Real.exp 2*Y⌉₊ δ α β γ Y a v ((aRat : ℝ)/qRat) (L*Y/H) kP kM kQ kT
  · intro kP hkP kM hkM kQ hkQ kT hkT hretained
    have h := @hbox r hr hj take hkeep ξ tmarks umarks big b κ ht hb hκ g hg
      ⌈4*Real.exp 2*Y⌉₊ kP kM kQ kT Y (L*Y/H) H
      hY1 hY hlog hR hHp hwidth hRwidth
      qP qT χP χT τP τT lo hi aM vM ν qM hqMInst χM hvM hqM hν
      σ qQ hqQInst χQ hqQ hσ qRat hqRat0 hqRat aRat (-(a+v)) hw
    have hset : {t : ℝ | |t| ≤ L*Y/H} = Set.Icc (-(L*Y/H)) (L*Y/H) := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_Icc, abs_le]
    rw [hset]
    have heq (t : ℝ) := congrArg (fun z : ℂ => ‖z‖^2)
      (common_source_four_dyadic_box_eq_rational ⌈4*Real.exp 2*Y⌉₊ δ α β γ
        Y a v aRat qRat t kP kM kQ kT)
    exact (le_of_eq_of_le (integral_congr_ae (Filter.Eventually.of_forall heq)) h)

end Bounty.WeakZeroFree


-- Source module: ActualSelectedSourceEnergy

/- The original selected endpoint has polynomial source and target energy,
with the actual candidate rough factor and normalized residual coefficient. -/

open Finset Filter
open scoped ComplexConjugate

namespace Bounty

theorem exists_actual_selected_source_energy {c : ℝ} (hc : 0 < c)
    (J ell : ℕ) (Cb : ℝ) :
    ∃ E : ℝ, ∀ᶠ L : ℝ in atTop,
      ∀ (r jStar : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (cut : candidatePIndices c L → Finset (Fin J))
        (big : Finset (candidatePIndices c L)) (g : candidatePIndices c L) (k : ℕ),
      ell+(cut g).card = k+1 → g ∉ big →
      ∀ (b₀ : GroupMarkedLists (fun j : big => candidatePBand (c*L) j.val.val)
          (fun j : big => ell+(cut j.val).card) → ℂ),
      (∀ l, ‖b₀ l‖ ≤ L^Cb) →
      ∀ (α θQ : ℕ → ℂ),
      (∀ n, ¬ Disjoint n.primeFactors
        ((candidatePIndices c L).biUnion (candidatePBand (c*L))) → α n = 0) →
      (∀ n, ‖α n‖ ≤ 1) → (∀ n, ‖θQ n‖ ≤ 1) →
      ∀ Y : ℝ, 1 ≤ Y → Real.log Y ≤ 6*L → ∀ Z a b v : ℝ,
      let P := fun j : candidatePIndices c L => candidatePBand (c*L) j.val
      let mass := fun j : candidatePIndices c L => ∑ p ∈ P j, 1/(p : ℝ)
      let marks := fun j : candidatePIndices c L => ell+(cut j).card
      let pool := (candidatePIndices c L).biUnion (candidatePBand (c*L))
      let β := fun n => if n ∈ candidateRoughBand c L jStar then θQ n else 0
      let γ := fun n => conj (candidateResidualPrimeCoefficient c L r jStar hr hj
        take hkeep (candidateAllocationFourierTwist c L r jStar take ξ) n)
      let F := fun n : ℤ => selectedPeeledEndpoint P (1/2) mass marks g k big b₀
        pool α β γ n.natAbs
      (∑ n ∈ harmonicCommonSupport Y, ‖harmonicCellSource Y Z a v F n‖^2) ≤ Y*L^E ∧
      (∑ n ∈ harmonicCommonSupport Y, ‖harmonicCellTarget Y b F n‖^2) ≤ Y*L^E := by
  classical
  obtain ⟨E,hE⟩ := exists_candidate_harmonic_single_energy hc J ell Cb 0
  refine ⟨E,?_⟩
  filter_upwards [hE,eventually_candidate_P_pool_below_rough_cutoff hc,
    eventually_ge_atTop (0 : ℝ)] with L henergy hpool hL
  intro r jStar hr hj take hkeep ξ cut big g k hk hg b₀ hb₀ α θQ hfree hα hθQ
    Y hY hlog Z a b v
  let β : ℕ → ℂ := fun n => if n ∈ candidateRoughBand c L jStar then θQ n else 0
  let γ : ℕ → ℂ := fun n => conj (candidateResidualPrimeCoefficient c L r jStar hr hj
    take hkeep (candidateAllocationFourierTwist c L r jStar take ξ) n)
  have hβfree (n : ℕ) (hn : ¬ Disjoint n.primeFactors
      ((candidatePIndices c L).biUnion (candidatePBand (c*L)))) : β n = 0 := by
    have hout : n ∉ candidateRoughBand c L jStar := by
      intro hmem
      exact hn (prime_factors_disjoint_of_rough hpool (mem_filter.mp hmem).2)
    exact if_neg hout
  have hβ (n : ℕ) : ‖β n‖ ≤ 1 := by
    dsimp only [β]
    split_ifs
    · exact hθQ n
    · simp only [norm_zero,zero_le_one]
  have hγ (n : ℕ) : ‖γ n‖ ≤ 1 := by
    dsimp only [γ]
    rw [Complex.norm_conj]
    exact norm_candidate_residual_prime_coefficient_le_one (mul_nonneg hc.le hL)
      hr hj take hkeep (candidateAllocationFourierTwist c L r jStar take ξ)
      (fun slot p hp => (candidate_allocation_fourier_twist_norm c L r jStar take ξ slot
        (Nat.pos_of_ne_zero (candidate_Q_slot_nonzero c L r jStar slot hp))).le) n
  have h := henergy (candidatePIndices c L) (subset_refl _) cut big g k hk hg b₀ hb₀
    ((candidatePIndices c L).biUnion (candidatePBand (c*L)))
    (fun j p hp => mem_biUnion.mpr ⟨j.val,j.property,hp⟩) α β γ
    hfree hβfree (by simpa only [Real.rpow_zero] using hα)
    (by simpa only [Real.rpow_zero] using hβ)
    (by simpa only [Real.rpow_zero] using hγ) Y hY hlog Z a b v
  exact h.2

end Bounty


-- Source module: ActualSourceFactorProperties

/- Unit bounds and prime-pool support for the literal twisted source factor. -/

open Finset Filter

namespace Bounty

theorem restricted_twisted_source_properties (pool I : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ 1)
    (hfree : ∀ n, f n ≠ 0 → Disjoint n.primeFactors pool)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (ν : ℝ) :
    (∀ n, ‖(typeIIRestrict I f n : ℂ)*(χ (n : ZMod q)*typeIIPhase ν n)‖ ≤ 1) ∧
    (∀ n, ¬ Disjoint n.primeFactors pool →
      (typeIIRestrict I f n : ℂ)*(χ (n : ZMod q)*typeIIPhase ν n) = 0) := by
  constructor
  · intro n
    have hb : ‖(typeIIRestrict I f n : ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_real,Real.norm_eq_abs] using
        typeIIRestrict_abs_le zero_le_one (fun n _ => hf n) n
    rw [norm_mul,norm_mul,typeIIPhase_norm,mul_one]
    exact (mul_le_mul hb (χ.norm_le_one _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · intro n hn
    have hz : f n = 0 := by
      by_contra hne
      exact hn (hfree n hne)
    simp only [typeIIRestrict,hz,ite_self,Complex.ofReal_zero,zero_mul]

theorem eventually_actual_prime_source_factor_properties {c : ℝ} (hc : 0 < c)
    (S : ℝ) (hS : 0 ≤ S) :
    ∀ᶠ L : ℝ in atTop, ∀ κ : ℝ, 0 ≤ κ → κ ≤ 1/50 →
      ∀ (I : Finset ℕ) (q : ℕ) (χ : DirichletCharacter ℂ q) (ν : ℝ),
      (∀ n, ‖(typeIIRestrict I (ambientPrimeTypeIIAlpha κ L S) n : ℂ)*
        (χ (n : ZMod q)*typeIIPhase ν n)‖ ≤ 1) ∧
      (∀ n, ¬ Disjoint n.primeFactors
        ((candidatePIndices c L).biUnion (candidatePBand (c*L))) →
        (typeIIRestrict I (ambientPrimeTypeIIAlpha κ L S) n : ℂ)*
          (χ (n : ZMod q)*typeIIPhase ν n) = 0) := by
  filter_upwards [eventually_balanced_typeII_coefficient_properties S hS,
    eventually_ambient_prime_endpoint_group_free hc S hS] with L hbound hfree
  intro κ hκ hκmax I q χ ν
  exact restricted_twisted_source_properties _ I _
    (fun n => (hbound κ hκ hκmax n).1)
    (fun n hn => (hfree κ hκ hκmax n hn).2) q χ ν

theorem eventually_actual_rough_source_factor_properties {c γ : ℝ}
    (hc : 0 < c) (hγ : 0 < γ) :
    ∀ᶠ L : ℝ in atTop, ∀ S a v : ℝ,
      ∀ (I : Finset ℕ) (q : ℕ) (χ : DirichletCharacter ℂ q) (ν : ℝ),
      (∀ n, ‖(typeIIRestrict I (ambientRoughIntervalTypeIIAlpha γ L S a v) n : ℂ)*
        (χ (n : ZMod q)*typeIIPhase ν n)‖ ≤ 1) ∧
      (∀ n, ¬ Disjoint n.primeFactors
        ((candidatePIndices c L).biUnion (candidatePBand (c*L))) →
        (typeIIRestrict I (ambientRoughIntervalTypeIIAlpha γ L S a v) n : ℂ)*
          (χ (n : ZMod q)*typeIIPhase ν n) = 0) := by
  filter_upwards [eventually_ambient_rough_interval_typeII_properties hγ,
    eventually_ambient_rough_endpoint_group_free hc hγ] with L hbound hfree
  intro S a v I q χ ν
  exact restricted_twisted_source_properties _ I _
    (fun n => (hbound S a v n).1)
    (fun n hn => (hfree S a v n hn).2) q χ ν

end Bounty


-- Source module: ActualPeeledSourceEnergy

/- Polynomial source and target energy for the exact prime and rough peeled endpoints. -/

open Finset Filter
open scoped ComplexConjugate
namespace Bounty

theorem exists_actual_prime_peeled_source_energy {c : ℝ} (hc : 0 < c)
    (J ell : ℕ) (Cb : ℝ) :
    ∃ E : ℝ, ∀ S : ℝ, 0 ≤ S → ∀ᶠ L : ℝ in atTop,
      ∀ (r jStar : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (cut : candidatePIndices c L → Finset (Fin J))
        (big : Finset (candidatePIndices c L)) (g : candidatePIndices c L) (k : ℕ),
      ell+(cut g).card = k+1 → g ∉ big →
      ∀ (b₀ : GroupMarkedLists (fun j : big => candidatePBand (c*L) j.val.val)
          (fun j : big => ell+(cut j.val).card) → ℂ),
      (∀ l, ‖b₀ l‖ ≤ L^Cb) →
      ∀ (lo hi : ℕ) (κ ν : ℝ) (qM : ℕ) (χM : DirichletCharacter ℂ qM),
      0 ≤ κ → κ ≤ 1/50 →
      ∀ (σ : ℝ) (qQ : ℕ) (χQ : DirichletCharacter ℂ qQ),
      let α := fun n => (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κ L S) n : ℂ)*
        (χM (n : ZMod qM)*typeIIPhase ν n)
      let θQ := fun n => typeIIPhase σ n*χQ (n : ZMod qQ)
      ∀ Y : ℝ, 1 ≤ Y → Real.log Y ≤ 6*L → ∀ Z a b v : ℝ,
      let P := fun j : candidatePIndices c L => candidatePBand (c*L) j.val
      let mass := fun j : candidatePIndices c L => ∑ p ∈ P j, 1/(p : ℝ)
      let marks := fun j : candidatePIndices c L => ell+(cut j).card
      let pool := (candidatePIndices c L).biUnion (candidatePBand (c*L))
      let β := fun n => if n ∈ candidateRoughBand c L jStar then θQ n else 0
      let γ := fun n => conj (candidateResidualPrimeCoefficient c L r jStar hr hj
        take hkeep (candidateAllocationFourierTwist c L r jStar take ξ) n)
      let F := fun n : ℤ => selectedPeeledEndpoint P (1/2) mass marks g k big b₀
        pool α β γ n.natAbs
      (∑ n ∈ harmonicCommonSupport Y, ‖harmonicCellSource Y Z a v F n‖^2) ≤ Y*L^E ∧
      (∑ n ∈ harmonicCommonSupport Y, ‖harmonicCellTarget Y b F n‖^2) ≤ Y*L^E := by
  classical
  obtain ⟨E,hE⟩ := exists_actual_selected_source_energy hc J ell Cb
  refine ⟨E,?_⟩
  intro S hS
  filter_upwards [hE,eventually_actual_prime_source_factor_properties hc S hS]
    with L henergy hfactor
  intro r jStar hr hj take hkeep ξ cut big g k hk hg b₀ hb₀
    lo hi κ ν qM χM hκ hκmax σ qQ χQ
  have hp := hfactor κ hκ hκmax (Ioc lo hi) qM χM ν
  have hθ (n : ℕ) : ‖typeIIPhase σ n*χQ (n : ZMod qQ)‖ ≤ 1 := by
    rw [norm_mul,typeIIPhase_norm,one_mul]
    exact χQ.norm_le_one _
  exact henergy r jStar hr hj take hkeep ξ cut big g k hk hg b₀ hb₀
    (fun n => (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κ L S) n : ℂ)*
      (χM (n : ZMod qM)*typeIIPhase ν n))
    (fun n => typeIIPhase σ n*χQ (n : ZMod qQ)) hp.2 hp.1 hθ

theorem exists_actual_rough_peeled_source_energy {c γrough : ℝ} (hc : 0 < c) (hγ : 0 < γrough)
    (J ell : ℕ) (Cb : ℝ) :
    ∃ E : ℝ, ∀ᶠ L : ℝ in atTop,
      ∀ (r jStar : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (cut : candidatePIndices c L → Finset (Fin J))
        (big : Finset (candidatePIndices c L)) (g : candidatePIndices c L) (k : ℕ),
      ell+(cut g).card = k+1 → g ∉ big →
      ∀ (b₀ : GroupMarkedLists (fun j : big => candidatePBand (c*L) j.val.val)
          (fun j : big => ell+(cut j.val).card) → ℂ),
      (∀ l, ‖b₀ l‖ ≤ L^Cb) →
      ∀ (lo hi : ℕ) (S aM vM ν : ℝ) (qM : ℕ) (χM : DirichletCharacter ℂ qM),
      ∀ (σ : ℝ) (qQ : ℕ) (χQ : DirichletCharacter ℂ qQ),
      let α := fun n => (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM vM) n : ℂ)*
        (χM (n : ZMod qM)*typeIIPhase ν n)
      let θQ := fun n => typeIIPhase σ n*χQ (n : ZMod qQ)
      ∀ Y : ℝ, 1 ≤ Y → Real.log Y ≤ 6*L → ∀ Z a b v : ℝ,
      let P := fun j : candidatePIndices c L => candidatePBand (c*L) j.val
      let mass := fun j : candidatePIndices c L => ∑ p ∈ P j, 1/(p : ℝ)
      let marks := fun j : candidatePIndices c L => ell+(cut j).card
      let pool := (candidatePIndices c L).biUnion (candidatePBand (c*L))
      let β := fun n => if n ∈ candidateRoughBand c L jStar then θQ n else 0
      let γ := fun n => conj (candidateResidualPrimeCoefficient c L r jStar hr hj
        take hkeep (candidateAllocationFourierTwist c L r jStar take ξ) n)
      let F := fun n : ℤ => selectedPeeledEndpoint P (1/2) mass marks g k big b₀
        pool α β γ n.natAbs
      (∑ n ∈ harmonicCommonSupport Y, ‖harmonicCellSource Y Z a v F n‖^2) ≤ Y*L^E ∧
      (∑ n ∈ harmonicCommonSupport Y, ‖harmonicCellTarget Y b F n‖^2) ≤ Y*L^E := by
  classical
  obtain ⟨E,hE⟩ := exists_actual_selected_source_energy hc J ell Cb
  refine ⟨E,?_⟩
  filter_upwards [hE,eventually_actual_rough_source_factor_properties hc hγ]
    with L henergy hfactor
  intro r jStar hr hj take hkeep ξ cut big g k hk hg b₀ hb₀
    lo hi S aM vM ν qM χM σ qQ χQ
  have hp := hfactor S aM vM (Ioc lo hi) qM χM ν
  have hθ (n : ℕ) : ‖typeIIPhase σ n*χQ (n : ZMod qQ)‖ ≤ 1 := by
    rw [norm_mul,typeIIPhase_norm,one_mul]
    exact χQ.norm_le_one _
  exact henergy r jStar hr hj take hkeep ξ cut big g k hk hg b₀ hb₀
    (fun n => (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM vM) n : ℂ)*
      (χM (n : ZMod qM)*typeIIPhase ν n))
    (fun n => typeIIPhase σ n*χQ (n : ZMod qQ)) hp.2 hp.1 hθ

end Bounty


-- Source module: ActualPeeledEndpoint

/- The literal candidate peeled endpoint has exactly the residual coefficient
used in the original four-factor analytic estimates. -/

open Finset
open scoped ComplexConjugate

namespace Bounty

theorem candidate_selected_peeled_endpoint_eq_four_convolution
    (c L q : ℝ) (r jStar : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
    (take : Fin ((candidateQIndices c L).card*r) → Bool)
    (hkeep : take ((candidateAllocationOrder c L r).symm
      (candidateRoughSlot c L r jStar hr hj)) = false)
    (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
    (marks : candidatePIndices c L → ℕ) (g : candidatePIndices c L) (k : ℕ)
    (big : Finset (candidatePIndices c L))
    (b : GroupMarkedLists (fun g : big => candidatePBand (c*L) g.val.val)
      (fun g : big => marks g.val) → ℂ) (α β : ℕ → ℂ) (n : ℕ) :
    selectedPeeledEndpoint
      (fun g : candidatePIndices c L => candidatePBand (c*L) g.val) q
      (fun g => ∑ p ∈ candidatePBand (c*L) g.val, 1/(p : ℝ)) marks g k big b
      ((candidatePIndices c L).biUnion (candidatePBand (c*L))) α β
      (fun m => conj (candidateResidualPrimeCoefficient c L r jStar hr hj take hkeep
        (candidateAllocationFourierTwist c L r jStar take ξ) m)) n =
    endpointFourConvolution
      (fun p => if p ∈ candidatePBand (c*L) g.val
        then 1/(((∑ p ∈ candidatePBand (c*L) g.val, 1/(p : ℝ)) : ℝ) : ℂ) else 0) α β
      (candidateSelectedResidualCoefficient c L q r jStar hr hj take hkeep ξ
        (Function.update marks g k) marks big b (fun _ => 1) (fun _ => 1)) n := by
  classical
  unfold selectedPeeledEndpoint
  congr 1
  funext m
  simp only [candidateSelectedResidualCoefficient,mul_one]

end Bounty


-- Source module: ActualPeeledPrimeSourceFourier

/- Fourier precision for the literal original peeled prime source. Its energy
and four-factor convolution identity are supplied by the proved candidate APIs. -/

open Finset Filter MeasureTheory
open scoped ComplexConjugate

namespace Bounty.WeakZeroFree

theorem exists_actual_peeled_prime_source_fourier_precision
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    ∃ J : ℕ, ∀ jStar : ℕ, J < jStar →
      ∀ (A : ℝ) (Jprobe ell : ℕ) (Cb Tmod Sshift Cmod Sfreq Rmod W : ℝ),
    ∃ S₀ : ℝ, 0 ≤ S₀ ∧ ∀ S : ℝ, S₀ ≤ S →
      ∀ᶠ L : ℝ in atTop,
      ∀ (r : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (cut : candidatePIndices c L → Finset (Fin Jprobe))
        (big : Finset (candidatePIndices c L)) (g : candidatePIndices c L) (k : ℕ),
      ell+(cut g).card = k+1 → g ∉ big → g.val ∈ candidateSmallPIndices c L →
      ∀ (b₀ : GroupMarkedLists (fun j : big => candidatePBand (c*L) j.val.val)
          (fun j : big => ell+(cut j.val).card) → ℂ),
      (∀ l, ‖b₀ l‖ ≤ L^Cb) →
      ∀ (lo hi : ℕ) (κM ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      0 ≤ κM → κM ≤ 1/50 → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      ∀ (Y H Z a v : ℝ),
      Real.exp (d*L) ≤ Y → Real.log Y ≤ 6*L →
      4096*Real.exp (L^(1/5 : ℝ))*L ≤ H → H ≤ Real.exp ((d/2)*L) →
      0 < Z → |a| ≤ L^W → |v| ≤ L^W →
      ∀ qRat : ℕ, 0 < qRat → (qRat : ℝ) ≤ L^Rmod → ∀ aRat : ℤ,
      let P := fun j : candidatePIndices c L => candidatePBand (c*L) j.val
      let mass := fun j : candidatePIndices c L => ∑ p ∈ P j, 1/(p : ℝ)
      let marks := fun j : candidatePIndices c L => ell+(cut j).card
      let pool := (candidatePIndices c L).biUnion (candidatePBand (c*L))
      let α := fun n => (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ)*
        (χM (n : ZMod qM)*typeIIPhase ν n)
      let β := fun n => if n ∈ candidateRoughBand c L jStar then
        typeIIPhase σ n*χQ (n : ZMod qQ) else 0
      let γ := fun n => conj (candidateResidualPrimeCoefficient c L r jStar hr hj
        take hkeep (candidateAllocationFourierTwist c L r jStar take ξ) n)
      let F := fun n : ℤ => selectedPeeledEndpoint P (1/2) mass marks g k big b₀
        pool α β γ n.natAbs
      (∫ x in Set.Icc ((aRat : ℝ)/qRat-1/H) ((aRat : ℝ)/qRat+1/H),
        ‖finiteFourierSum (harmonicCommonSupport Y) (harmonicCellSource Y Z a v F) x‖^2)
        ≤ Y*L^(-A) := by
  classical
  obtain ⟨J,hmain⟩ := exists_actual_prime_source_fourier_precision
    (q := (1/2 : ℝ)) hZ hc (by norm_num) (by norm_num) hd
  refine ⟨J,?_⟩
  intro jStar hjStar A Jprobe ell Cb Tmod Sshift Cmod Sfreq Rmod W
  obtain ⟨E,henergy⟩ := exists_actual_prime_peeled_source_energy hc Jprobe ell Cb
  obtain ⟨C,hC,hprecision⟩ := hmain jStar hjStar A E (ell+Jprobe)
    Tmod Sshift Cmod Sfreq Rmod W
  obtain ⟨S₀,hS₀,hbound⟩ := hprecision Cb
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [hbound S hS,henergy S (hS₀.trans hS),eventually_ge_atTop (1 : ℝ)]
    with L hdecay henergyL hL
  intro r hr hj take hkeep ξ cut big g k hk hg hgSmall b₀ hb₀
    lo hi κM ν qM hqMInst χM hκM hκmax hqM hν
    σ qQ hqQInst χQ hqQ hσ Y H Z a v hYlo hYhi hwidth hHupper hZpos ha hv
    qRat hqRat0 hqRat aRat P mass marks pool α β γ F
  have hcard (j : candidatePIndices c L) : (cut j).card ≤ Jprobe := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (cut j)
  have hkbound : k ≤ ell+Jprobe := by
    have := hcard g
    omega
  have ht : ∀ j, Function.update marks g k j ≤ ell+Jprobe := by
    intro j
    by_cases hjg : j = g
    · subst j
      simpa only [Function.update_self] using hkbound
    · simpa only [Function.update_of_ne hjg] using Nat.add_le_add_left (hcard j) ell
  have hchar (n : ℕ) : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 := by
    rw [Subsingleton.elim (n : ZMod 1) 1]
    exact map_one _
  have hY1 : 1 ≤ Y :=
    (Real.one_le_exp (mul_nonneg hd.le (zero_le_one.trans hL))).trans hYlo
  have hresult := @hdecay r hr hj take hkeep ξ (Function.update marks g k) marks big b₀
    (fun _ => 1) ht hb₀ (by intro n; simp only [norm_one,le_refl]) g.val hgSmall
    Y H Z a v F hYlo hYhi hwidth hHupper hZpos ha hv
    1 1 (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) 0 0 lo hi
    κM ν qM hqMInst χM hκM hκmax hqM hν
    σ qQ hqQInst χQ hqQ hσ qRat hqRat0 hqRat aRat
  apply hresult
  · intro n hn
    have h := candidate_selected_peeled_endpoint_eq_four_convolution c L (1/2) r jStar
      hr hj take hkeep ξ marks g k big b₀ α β n
    simpa only [F,P,mass,marks,pool,γ,Int.natAbs_natCast,hchar,typeIIPhase_zero,mul_one] using h
  · have he := henergyL r jStar hr hj take hkeep ξ cut big g k hk hg b₀ hb₀
      lo hi κM ν qM χM hκM hκmax σ qQ χQ Y hY1 hYhi Z a 0 v
    exact he.1

end Bounty.WeakZeroFree


-- Source module: ActualPeeledRoughSourceFourier

/- Rational-centered Fourier decay for the original peeled rough endpoint,
with its coefficient identity and source energy discharged. -/

open Finset Filter MeasureTheory
open scoped ComplexConjugate

namespace Bounty.WeakZeroFree

theorem exists_actual_peeled_rough_source_fourier_precision
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c d γrough vMax ρ : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hγ : 0 < γrough) (hv : vMax < 1) (hρ : 0 < ρ) :
    ∃ J : ℕ, ∀ jStar : ℕ, J < jStar →
      ∀ (A : ℝ) (Jprobe ell : ℕ) (Cb Tmod Sshift Cmod Sfreq Rmod W : ℝ),
    ∃ S₀ : ℝ, 0 ≤ S₀ ∧ ∀ S : ℝ, S₀ ≤ S → ∀ᶠ L : ℝ in atTop,
      ∀ (r : ℕ) (hr : 0 < r) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*r) → Bool)
        (hkeep : take ((candidateAllocationOrder c L r).symm
          (candidateRoughSlot c L r jStar hr hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L r jStar) → ℝ)
        (cut : candidatePIndices c L → Finset (Fin Jprobe))
        (big : Finset (candidatePIndices c L)) (g : candidatePIndices c L) (k : ℕ),
      ell+(cut g).card = k+1 → g ∉ big → g.val ∈ candidateSmallPIndices c L →
      ∀ (b₀ : GroupMarkedLists (fun j : big => candidatePBand (c*L) j.val.val)
        (fun j : big => ell+(cut j.val).card) → ℂ),
      (∀ l, ‖b₀ l‖ ≤ L^Cb) →
      ∀ (lo hi : ℕ) (aM vM ν : ℝ) (qM : ℕ) [NeZero qM] (χM : DirichletCharacter ℂ qM),
      vM ≤ vMax → (qM : ℝ) ≤ L^Cmod → |ν| ≤ L^Sfreq →
      ∀ (σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      ∀ (Y H Z a v : ℝ),
      Real.exp (d*L) ≤ Y → Real.log Y ≤ 6*L →
      4096*Real.exp (L^(1/5 : ℝ))*L ≤ H → H ≤ Real.exp ((d/2)*L) →
      0 < Z → |a| ≤ L^W → |v| ≤ L^W →
      ∀ qRat : ℕ, 0 < qRat → (qRat : ℝ) ≤ L^Rmod → ∀ aRat : ℤ,
      let P := fun j : candidatePIndices c L => candidatePBand (c*L) j.val
      let mass := fun j : candidatePIndices c L => ∑ p ∈ P j, 1/(p : ℝ)
      let marks := fun j : candidatePIndices c L => ell+(cut j).card
      let pool := (candidatePIndices c L).biUnion (candidatePBand (c*L))
      let α := fun n =>
        (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM vM) n : ℂ)*
          (χM (n : ZMod qM)*typeIIPhase ν n)
      let β := fun n => if n ∈ candidateRoughBand c L jStar then
        typeIIPhase σ n*χQ (n : ZMod qQ) else 0
      let γ := fun n => conj (candidateResidualPrimeCoefficient c L r jStar hr hj
        take hkeep (candidateAllocationFourierTwist c L r jStar take ξ) n)
      let F := fun n : ℤ => selectedPeeledEndpoint P (1/2) mass marks g k big b₀
        pool α β γ n.natAbs
      (∫ x in Set.Icc ((aRat : ℝ)/qRat-1/H) ((aRat : ℝ)/qRat+1/H),
        ‖finiteFourierSum (harmonicCommonSupport Y) (harmonicCellSource Y Z a v F) x‖^2)
        ≤ Y*L^(-A) := by
  classical
  obtain ⟨J,hmain⟩ := exists_actual_rough_source_fourier_precision
    (q := 1/2) hZ hc (by norm_num) (by norm_num) hd hγ hv hρ
  refine ⟨J,?_⟩
  intro jStar hjStar A Jprobe ell Cb Tmod Sshift Cmod Sfreq Rmod W
  obtain ⟨E,henergy⟩ := exists_actual_rough_peeled_source_energy hc hγ Jprobe ell Cb
  obtain ⟨C,hC,hprecision⟩ := hmain jStar hjStar A E (ell+Jprobe)
    Tmod Sshift Cmod Sfreq Rmod W
  obtain ⟨S₀,hS₀,hbound⟩ := hprecision Cb
  refine ⟨S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [hbound S hS,henergy,eventually_ge_atTop (1 : ℝ)] with L hsource henergy hL
  intro r hr hj take hkeep ξ cut big g k hk hgb hg b₀ hb₀
    lo hi aM vM ν qM hqMInst χM hvM hqM hν σ qQ hqQInst χQ hqQ hσ
    Y H Z a v hY hlog hwidth hHu hZpos ha hvPhase
    qRat hqRat0 hqRat aRat P mass marks pool α β γ F
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hY1 : 1 ≤ Y := (Real.one_le_exp (mul_nonneg hd.le hLp.le)).trans hY
  have hcard (j : candidatePIndices c L) : (cut j).card ≤ Jprobe := by
    simpa using (Finset.card_le_univ (cut j))
  have ht : ∀ j, Function.update marks g k j ≤ ell+Jprobe := by
    intro j
    by_cases h : j = g
    · subst j
      rw [Function.update_self]
      have hcg := hcard g
      omega
    · rw [Function.update_of_ne h]
      exact Nat.add_le_add_left (hcard j) ell
  have hc1 (n : ℕ) : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 := by
    rw [Subsingleton.elim (n : ZMod 1) 1]
    exact map_one _
  have hEs : (∑ n ∈ harmonicCommonSupport Y, ‖harmonicCellSource Y Z a v F n‖^2) ≤ Y*L^E :=
    (henergy r jStar hr hj take hkeep ξ cut big g k hk hgb b₀ hb₀
      lo hi S aM vM ν qM χM σ qQ χQ Y hY1 hlog Z a 0 v).1
  apply @hsource r hr hj take hkeep ξ (Function.update marks g k) marks big b₀
    (fun _ => 1) ht hb₀ (by intro n; simp) g.val hg Y H Z a v F
    hY hlog hwidth hHu hZpos ha hvPhase
    1 1 (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) 0 0 lo hi
    aM vM ν qM hqMInst χM hvM hqM hν σ qQ hqQInst χQ hqQ hσ
    qRat hqRat0 hqRat aRat
  · intro n hn
    have h := candidate_selected_peeled_endpoint_eq_four_convolution c L (1/2)
      r jStar hr hj take hkeep ξ marks g k big b₀ α β n
    simpa only [F,P,mass,marks,pool,γ,Int.natAbs_natCast,hc1,typeIIPhase_zero,mul_one] using h
  · exact hEs

end Bounty.WeakZeroFree


-- Source module: ActualSourceCellScale

/- Actual occupied comparison cells simultaneously supply the source size and
local Fourier width, with a genuine lower bound on the auxiliary product. -/

open Finset Filter
open scoped Classical

namespace Bounty

theorem eventually_actual_occupied_source_cell_scale {c b : ℝ}
    (hc : 0 < c) (hb : 0 < b) (J : ℕ) (K q : ℝ) (hq : 0 ≤ q) :
    ∀ᶠ L : ℝ in atTop, ∀ (S : Finset ℕ), S ⊆ candidatePIndices c L →
      let P := fun g : S => candidatePBand (c*L) g.val
      ∀ (ell : ℕ) (probes : S → Finset (Fin J)) (r t : Finset S)
        (A B : Finset (RepeatedBigFlatIndex S J ell)),
        A ⊆ r.sigma (repeatedBigPrimeProbeSlots probes) → A.Nonempty →
        B ⊆ t.sigma (repeatedBigPrimeProbeSlots probes) → B.Nonempty →
        (∃ i : A, i.val.1.val ∈ candidateBigPIndices c L) →
      ∀ (Q : ℕ) (h : ℝ), 0 < h → h ≤ 1 →
      ∀ (d e : ℤ) (χ ψ : BoundedPrimitiveCharacter Q) (ζ : ℝ)
        (x : ∀ i : A, P i.val.1) (y : ∀ i : B, P i.val.1),
        (starRingEnd ℂ) (primeProductCellCharacter (fun i : A => P i.val.1) h d χ x) *
          physicalPhase ζ (∏ i, (x i).val) ≠ 0 →
        (starRingEnd ℂ) (primeProductCellCharacter (fun i : B => P i.val.1) h e ψ y) *
          physicalPhase ζ (∏ i, (y i).val) ≠ 0 →
      ∀ (k : ℤ), k ≠ 0 → |(k : ℝ)| ≤ L^K →
      ∀ Z : ℝ, 0 < Z →
        Real.exp (2*b*L) ≤ Z*((((∏ i, (x i).val)*(∏ i, (y i).val)) : ℕ) : ℝ)/2 →
        let HA := Real.exp (((d : ℝ)-1)*h)
        let HB := Real.exp (((e : ℝ)-1)*h)
        let Y := Z*(HA*HB)
        let Hlocal := |(k : ℝ)| *(HA*HB)/L^q
        Real.exp (b*L) ≤ Y ∧ 1 ≤ Y ∧ 1 ≤ Hlocal ∧
          4096*Real.exp (L^(1/5 : ℝ))*L ≤ Hlocal ∧
          Hlocal ≤ Real.exp ((b/2)*L) := by
  filter_upwards [eventually_candidate_big_cell_local_scale hc hb J K q hq,
    eventually_common_cell_exponential_lower (b := 2*b) (by positivity),
    eventually_ge_atTop (1 : ℝ)] with L hlocal hsize hL
  intro S hS P ell probes r t A B hA hAne hB hBne hAbig Q h hh hh1
    d e χ ψ ζ x y hx hy k hk hkK Z hZ hproduct
  have hwidth := hlocal S hS ell probes r t A B hA hAne hB hBne hAbig
    Q h hh hh1 d e χ ψ ζ ⟨x,hx⟩ ⟨y,hy⟩ k hk hkK
    (Real.exp (L^(1/5 : ℝ))) (le_refl _)
  have hposA : 0 < ∏ i : A, (x i).val := by
    apply Finset.prod_pos
    intro i _
    exact ((mem_dyadicPrimeBand_iff (c*L) (3/2) (9/5) i.val.1.val (x i).val).mp
      (x i).property).1.pos
  have hposB : 0 < ∏ i : B, (y i).val := by
    apply Finset.prod_pos
    intro i _
    exact ((mem_dyadicPrimeBand_iff (c*L) (3/2) (9/5) i.val.1.val (y i).val).mp
      (y i).property).1.pos
  have hcharA : primeProductCellCharacter (fun i : A => P i.val.1) h d χ x ≠ 0 := by
    intro hz
    exact hx (by rw [hz,map_zero,zero_mul])
  have hcharB : primeProductCellCharacter (fun i : B => P i.val.1) h e ψ y ≠ 0 := by
    intro hz
    exact hy (by rw [hz,map_zero,zero_mul])
  have hcell := harmonic_cell_product_bounds hh hh1 hposA hposB
    (prime_cell_character_mem (fun i : A => P i.val.1) h d χ x hcharA)
    (prime_cell_character_mem (fun i : B => P i.val.1) h e ψ y hcharB)
  have hY := hsize Z (harmonicCellProductScale h d e)
    (((∏ i : A, (x i).val)*(∏ i : B, (y i).val) : ℕ) : ℝ)
    hZ hcell.2 hproduct
  have hbhalf : (2*b)/2 = b := by ring
  rw [hbhalf] at hY
  have hYone : 1 ≤ Z*harmonicCellProductScale h d e :=
    (Real.one_le_exp (mul_nonneg hb.le (zero_le_one.trans hL))).trans hY
  have hExp : 1 ≤ Real.exp (L^(1/5 : ℝ)) :=
    Real.one_le_exp (Real.rpow_nonneg (zero_le_one.trans hL) _)
  have hbase : 1 ≤ Real.exp (L^(1/5 : ℝ))*L := by
    simpa only [one_mul] using mul_le_mul hExp hL zero_le_one (Real.exp_nonneg _)
  have hHone : 1 ≤ |(k : ℝ)| *
      (Real.exp (((d : ℝ)-1)*h)*Real.exp (((e : ℝ)-1)*h))/L^q := by
    have hw := hwidth.1
    simp only [mul_assoc] at hw
    nlinarith only [hbase,hw]
  exact ⟨hY,hYone,hHone,by simpa only [mul_assoc] using hwidth.1,
    by simpa only [mul_assoc] using hwidth.2⟩

end Bounty


-- Source module: ActualEmptyCellSum

/- Empty original cell tests make the literal auxiliary harmonic sum zero,
without any source-energy or positive-scale hypothesis. -/

open Finset
open scoped Classical

namespace Bounty

private theorem cell_character_zero_of_no_phased_support
    {I : Type*} [Fintype I] (P : I → Finset ℕ) (Q : ℕ) (h : ℝ) (d : ℤ)
    (χ : BoundedPrimitiveCharacter Q) (ζ : ℝ)
    (hnone : ¬∃ x : (∀ i, P i),
      (starRingEnd ℂ) (primeProductCellCharacter P h d χ x) *
        physicalPhase ζ (∏ i, (x i).val) ≠ 0)
    (x : ∀ i, P i) :
    (starRingEnd ℂ) (primeProductCellCharacter P h d χ x) = 0 := by
  have hz : (starRingEnd ℂ) (primeProductCellCharacter P h d χ x) *
      physicalPhase ζ (∏ i, (x i).val) = 0 := by
    by_contra hne
    exact hnone ⟨x,hne⟩
  apply norm_eq_zero.mp
  have hn := congrArg (fun z : ℂ => ‖z‖) hz
  simpa only [norm_mul,physical_phase_norm,mul_one,norm_zero] using hn

theorem candidate_cell_aux_sum_eq_zero_of_no_left
    {S : Finset ℕ} {J ell : ℕ} (P : S → Finset ℕ) (V : S → ℝ)
    (A B : Finset (RepeatedBigFlatIndex S J ell))
    (hU : ∀ (g : S) (j : Fin ell),
      (⟨g, Sum.inr j⟩ : RepeatedBigFlatIndex S J ell) ∉ A ∪ B)
    (hAB : Disjoint A B) (k : ℤ) (Q : ℕ) (h : ℝ) (d e : ℤ)
    (χ ψ : BoundedPrimitiveCharacter Q) (Y Z a b v : ℝ) (F₀ G₀ : ℤ → ℂ)
    (hnone : ¬∃ x : (∀ i : A, P i.val.1),
      (starRingEnd ℂ) (primeProductCellCharacter (fun i : A => P i.val.1) h d χ x) *
        physicalPhase (-(a+b+2*Real.pi*v)) (∏ i, (x i).val) ≠ 0) :
    (∑ aux : PhysicalAuxLabels P (repeatedBigAuxCut A B),
      (physicalAuxMass V (repeatedBigAuxCut A B) aux : ℂ) *
        ((starRingEnd ℂ) (primeProductCellCharacter (fun i : A => P i.val.1) h d χ
            (repeatedBigAuxSplitEquiv P A B hU hAB aux).1) *
          (starRingEnd ℂ) (primeProductCellCharacter (fun i : B => P i.val.1) h e ψ
            (repeatedBigAuxSplitEquiv P A B hU hAB aux).2)) *
        physicalPhase (-(a+b+2*Real.pi*v)) (physicalFreeFactor (repeatedBigAuxCut A B) aux) *
        harmonicCellPairing Y Z a b (2*Real.pi*v)
          (k*(physicalFreeFactor (repeatedBigAuxCut A B) aux : ℤ)) F₀ G₀) = 0 := by
  apply sum_eq_zero
  intro aux _
  have hz := cell_character_zero_of_no_phased_support
    (fun i : A => P i.val.1) Q h d χ (-(a+b+2*Real.pi*v)) hnone
    (repeatedBigAuxSplitEquiv P A B hU hAB aux).1
  simp only [hz,zero_mul,mul_zero]

theorem candidate_cell_aux_sum_eq_zero_of_no_right
    {S : Finset ℕ} {J ell : ℕ} (P : S → Finset ℕ) (V : S → ℝ)
    (A B : Finset (RepeatedBigFlatIndex S J ell))
    (hU : ∀ (g : S) (j : Fin ell),
      (⟨g, Sum.inr j⟩ : RepeatedBigFlatIndex S J ell) ∉ A ∪ B)
    (hAB : Disjoint A B) (k : ℤ) (Q : ℕ) (h : ℝ) (d e : ℤ)
    (χ ψ : BoundedPrimitiveCharacter Q) (Y Z a b v : ℝ) (F₀ G₀ : ℤ → ℂ)
    (hnone : ¬∃ x : (∀ i : B, P i.val.1),
      (starRingEnd ℂ) (primeProductCellCharacter (fun i : B => P i.val.1) h e ψ x) *
        physicalPhase (-(a+b+2*Real.pi*v)) (∏ i, (x i).val) ≠ 0) :
    (∑ aux : PhysicalAuxLabels P (repeatedBigAuxCut A B),
      (physicalAuxMass V (repeatedBigAuxCut A B) aux : ℂ) *
        ((starRingEnd ℂ) (primeProductCellCharacter (fun i : A => P i.val.1) h d χ
            (repeatedBigAuxSplitEquiv P A B hU hAB aux).1) *
          (starRingEnd ℂ) (primeProductCellCharacter (fun i : B => P i.val.1) h e ψ
            (repeatedBigAuxSplitEquiv P A B hU hAB aux).2)) *
        physicalPhase (-(a+b+2*Real.pi*v)) (physicalFreeFactor (repeatedBigAuxCut A B) aux) *
        harmonicCellPairing Y Z a b (2*Real.pi*v)
          (k*(physicalFreeFactor (repeatedBigAuxCut A B) aux : ℤ)) F₀ G₀) = 0 := by
  apply sum_eq_zero
  intro aux _
  have hz := cell_character_zero_of_no_phased_support
    (fun i : B => P i.val.1) Q h e ψ (-(a+b+2*Real.pi*v)) hnone
    (repeatedBigAuxSplitEquiv P A B hU hAB aux).2
  simp only [hz,zero_mul,mul_zero]

end Bounty


-- Source module: ActualPrimeCellLocalEnergy

/- The original prime peeled endpoints satisfy the comparison-cell estimate.
The source and target energies and rational local source bound are discharged. -/

open Finset Filter MeasureTheory
open scoped ComplexConjugate

namespace Bounty.WeakZeroFree

theorem exists_actual_prime_cell_local_energy_decay
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c dSource : ℝ}
    (hc : 0 < c) (hdSource : 0 < dSource) :
    ∃ J : ℕ, ∀ jStar : ℕ, J < jStar →
      ∀ (D : ℝ) (Jprobe ell : ℕ) (Cb K Tmod Sshift Cmod Sfreq W : ℝ), 0 ≤ K →
    ∃ q : ℝ, 0 ≤ q ∧ ∃ S₀ : ℝ, 0 ≤ S₀ ∧
      ∀ S : ℝ, S₀ ≤ S → ∀ᶠ L : ℝ in atTop,
      ∀ (rQ : ℕ) (hrQ : 0 < rQ) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*rQ) → Bool)
        (hkeep : take ((candidateAllocationOrder c L rQ).symm
          (candidateRoughSlot c L rQ jStar hrQ hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L rQ jStar) → ℝ)
        (cut : candidatePIndices c L → Finset (Fin Jprobe))
        (big : Finset (candidatePIndices c L)) (g : candidatePIndices c L) (kPeel : ℕ),
      ell+(cut g).card = kPeel+1 → g ∉ big → g.val ∈ candidateSmallPIndices c L →
      ∀ (b₀ b₁ : GroupMarkedLists (fun j : big => candidatePBand (c*L) j.val.val)
        (fun j : big => ell+(cut j.val).card) → ℂ),
      (∀ l, ‖b₀ l‖ ≤ L^Cb) → (∀ l, ‖b₁ l‖ ≤ L^Cb) →
      ∀ (lo hi : ℕ) (κM ν₀ ν₁ : ℝ) (qM : ℕ) [NeZero qM]
        (χM : DirichletCharacter ℂ qM),
      0 ≤ κM → κM ≤ 1/50 → (qM : ℝ) ≤ L^Cmod →
      |ν₀| ≤ L^Sfreq → |ν₁| ≤ L^Sfreq →
      ∀ (σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      let P₀ := fun j : candidatePIndices c L => candidatePBand (c*L) j.val
      let mass := fun j : candidatePIndices c L => ∑ p ∈ P₀ j, 1/(p : ℝ)
      let marks := fun j : candidatePIndices c L => ell+(cut j).card
      let pool := (candidatePIndices c L).biUnion (candidatePBand (c*L))
      let α₀ := fun n => (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ)*
        (χM (n : ZMod qM)*typeIIPhase ν₀ n)
      let α₁ := fun n => (typeIIRestrict (Ioc lo hi) (ambientPrimeTypeIIAlpha κM L S) n : ℂ)*
        (χM (n : ZMod qM)*typeIIPhase ν₁ n)
      let β := fun n => if n ∈ candidateRoughBand c L jStar then
        typeIIPhase σ n*χQ (n : ZMod qQ) else 0
      let γ := fun n => conj (candidateResidualPrimeCoefficient c L rQ jStar hrQ hj
        take hkeep (candidateAllocationFourierTwist c L rQ jStar take ξ) n)
      let F₀ := fun n : ℤ => selectedPeeledEndpoint P₀ (1/2) mass marks g kPeel big b₀
        pool α₀ β γ n.natAbs
      let G₀ := fun n : ℤ => selectedPeeledEndpoint P₀ (1/2) mass marks g kPeel big b₁
        pool α₁ β γ n.natAbs
      ∀ (groups : Finset ℕ), groups ⊆ candidatePIndices c L →
      let P := fun j : groups => candidatePBand (c*L) j.val
      let V := fun j : groups => ∑ p ∈ P j, 1/(p : ℝ)
      ∀ (probes : groups → Finset (Fin Jprobe)) (r t : Finset groups)
        (A B : Finset (RepeatedBigFlatIndex groups Jprobe ell)),
      A ⊆ r.sigma (repeatedBigPrimeProbeSlots probes) → A.Nonempty →
      B ⊆ t.sigma (repeatedBigPrimeProbeSlots probes) → B.Nonempty →
      (∃ i : A, i.val.1.val ∈ candidateBigPIndices c L) →
      ∀ (hU : ∀ j (i : Fin ell),
          (⟨j, Sum.inr i⟩ : RepeatedBigFlatIndex groups Jprobe ell) ∉ A ∪ B)
        (hAB : Disjoint A B) (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L^K →
      ∀ (Q : ℕ) (h : ℝ), 0 < h → h ≤ 1 →
      ∀ (d e : ℤ) (χ ψ : BoundedPrimitiveCharacter Q) (a b v Z : ℝ),
      0 < Z → |a| ≤ L^W → |2*Real.pi*v| ≤ L^W →
      let HA := Real.exp (((d : ℝ)-1)*h)
      let HB := Real.exp (((e : ℝ)-1)*h)
      let Y := Z*(HA*HB)
      Real.log Y ≤ 6*L →
      (∀ (x : ∀ i : A, P i.val.1) (y : ∀ i : B, P i.val.1),
        (starRingEnd ℂ) (primeProductCellCharacter (fun i : A => P i.val.1) h d χ x) *
          physicalPhase (-(a+b+2*Real.pi*v)) (∏ i, (x i).val) ≠ 0 →
        (starRingEnd ℂ) (primeProductCellCharacter (fun i : B => P i.val.1) h e ψ y) *
          physicalPhase (-(a+b+2*Real.pi*v)) (∏ i, (y i).val) ≠ 0 →
        Real.exp (2*dSource*L) ≤
          Z*((((∏ i, (x i).val)*(∏ i, (y i).val)) : ℕ) : ℝ)/2) →
      ‖∑ aux : PhysicalAuxLabels P (repeatedBigAuxCut A B),
        (physicalAuxMass V (repeatedBigAuxCut A B) aux : ℂ) *
          ((starRingEnd ℂ) (primeProductCellCharacter (fun i : A => P i.val.1) h d χ
              (repeatedBigAuxSplitEquiv P A B hU hAB aux).1) *
            (starRingEnd ℂ) (primeProductCellCharacter (fun i : B => P i.val.1) h e ψ
              (repeatedBigAuxSplitEquiv P A B hU hAB aux).2)) *
          physicalPhase (-(a+b+2*Real.pi*v)) (physicalFreeFactor (repeatedBigAuxCut A B) aux) *
          harmonicCellPairing Y Z a b (2*Real.pi*v)
            (k*(physicalFreeFactor (repeatedBigAuxCut A B) aux : ℤ)) F₀ G₀‖
        ≤ Y*L^(-D) := by
  classical
  obtain ⟨J,hsource⟩ := exists_actual_peeled_prime_source_fourier_precision hZ hc hdSource
  refine ⟨J,?_⟩
  intro jStar hjStar D Jprobe ell Cb K Tmod Sshift Cmod Sfreq W hK
  obtain ⟨E,henergy⟩ := exists_actual_prime_peeled_source_energy hc Jprobe ell Cb
  obtain ⟨q,hq,hcell⟩ := exists_candidate_cell_local_energy_decay hc Jprobe D E K hK
  obtain ⟨S₀,hS₀,hfourier⟩ := hsource jStar hjStar
    ((2*D+E+2)+2*q+K+1) Jprobe ell Cb Tmod Sshift Cmod Sfreq (K+q) W
  refine ⟨q,hq,S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [henergy S (hS₀.trans hS),hfourier S hS,hcell,
    eventually_actual_occupied_source_cell_scale hc hdSource Jprobe K q hq,
    eventually_ge_atTop (1 : ℝ)] with L he hf hcell hscale hL
  intro rQ hrQ hj take hkeep ξ cut big g kPeel hkPeel hgb hgSmall b₀ b₁ hb₀ hb₁
    lo hi κM ν₀ ν₁ qM hqMInst χM hκM hκmax hqM hν₀ hν₁
    σ qQ hqQInst χQ hqQ hσ P₀ mass marks pool α₀ α₁ β γ F₀ G₀
    groups hgroups P V probes r t A B hA hAne hB hBne hAbig hU hAB k hk hkB
    Q h hh hh1 d e χ ψ a b v Z hZpos ha hv HA HB Y hlog hproduct
  have hYpos : 0 < Y := mul_pos hZpos (mul_pos (Real.exp_pos _) (Real.exp_pos _))
  have hnonneg : 0 ≤ Y*L^(-D) := mul_nonneg hYpos.le
    (Real.rpow_nonneg (zero_le_one.trans hL) _)
  by_cases hx : ∃ x : (∀ i : A, P i.val.1),
      (starRingEnd ℂ) (primeProductCellCharacter (fun i : A => P i.val.1) h d χ x) *
        physicalPhase (-(a+b+2*Real.pi*v)) (∏ i, (x i).val) ≠ 0
  · by_cases hy : ∃ y : (∀ i : B, P i.val.1),
        (starRingEnd ℂ) (primeProductCellCharacter (fun i : B => P i.val.1) h e ψ y) *
          physicalPhase (-(a+b+2*Real.pi*v)) (∏ i, (y i).val) ≠ 0
    · obtain ⟨x,hx0⟩ := hx
      obtain ⟨y,hy0⟩ := hy
      have hkAbs : |(k : ℝ)| ≤ L^K := by
        simpa only [Nat.cast_natAbs,Int.cast_abs] using hkB
      have hs := hscale groups hgroups ell probes r t A B hA hAne hB hBne hAbig
        Q h hh hh1 d e χ ψ (-(a+b+2*Real.pi*v)) x y hx0 hy0 k hk hkAbs
        Z hZpos (hproduct x y hx0 hy0)
      have he₀ := he rQ jStar hrQ hj take hkeep ξ cut big g kPeel hkPeel hgb b₀ hb₀
        lo hi κM ν₀ qM χM hκM hκmax σ qQ χQ Y hs.2.1 hlog Z a b (2*Real.pi*v)
      have he₁ := he rQ jStar hrQ hj take hkeep ξ cut big g kPeel hkPeel hgb b₁ hb₁
        lo hi κM ν₁ qM χM hκM hκmax σ qQ χQ Y hs.2.1 hlog Z a b (2*Real.pi*v)
      apply hcell groups hgroups ell probes r t A B hA hAne hB hBne hU hAB
        k hk hkB Q h hh hh1 d e χ ψ a b v Y Z F₀ G₀ hYpos he₀.1 he₁.2
      intro _ _ qRat hqRat0 hqRat aRat
      exact @hf rQ hrQ hj take hkeep ξ cut big g kPeel hkPeel hgb hgSmall b₀ hb₀
        lo hi κM ν₀ qM hqMInst χM hκM hκmax hqM hν₀
        σ qQ hqQInst χQ hqQ hσ Y (|(k : ℝ)| *(HA*HB)/L^q) Z a (2*Real.pi*v)
        hs.1 hlog hs.2.2.2.1 hs.2.2.2.2 hZpos ha hv qRat hqRat0 hqRat aRat
    · rw [candidate_cell_aux_sum_eq_zero_of_no_right P V A B hU hAB k Q h d e χ ψ Y Z a b v F₀ G₀ hy, norm_zero]
      exact hnonneg
  · rw [candidate_cell_aux_sum_eq_zero_of_no_left P V A B hU hAB k Q h d e χ ψ Y Z a b v F₀ G₀ hx, norm_zero]
    exact hnonneg

end Bounty.WeakZeroFree


-- Source module: ActualRoughCellLocalEnergy

/- The original rough peeled endpoints satisfy the comparison-cell estimate.
The source and target energies and rational local source bound are discharged. -/

open Finset Filter MeasureTheory
open scoped ComplexConjugate

namespace Bounty.WeakZeroFree

theorem exists_actual_rough_cell_local_energy_decay
    (hZ : PrimitiveZeroFreeRightOf (23 / 24)) {c dSource γrough vMax ρ : ℝ}
    (hc : 0 < c) (hdSource : 0 < dSource)
    (hγ : 0 < γrough) (hv : vMax < 1) (hρ : 0 < ρ) :
    ∃ J : ℕ, ∀ jStar : ℕ, J < jStar →
      ∀ (D : ℝ) (Jprobe ell : ℕ) (Cb K Tmod Sshift Cmod Sfreq W : ℝ), 0 ≤ K →
    ∃ q : ℝ, 0 ≤ q ∧ ∃ S₀ : ℝ, 0 ≤ S₀ ∧
      ∀ S : ℝ, S₀ ≤ S → ∀ᶠ L : ℝ in atTop,
      ∀ (rQ : ℕ) (hrQ : 0 < rQ) (hj : jStar ∈ candidateQIndices c L)
        (take : Fin ((candidateQIndices c L).card*rQ) → Bool)
        (hkeep : take ((candidateAllocationOrder c L rQ).symm
          (candidateRoughSlot c L rQ jStar hrQ hj)) = false)
        (ξ : ActiveAllocationIndex (candidateAllocationActive c L rQ jStar) → ℝ)
        (cut : candidatePIndices c L → Finset (Fin Jprobe))
        (big : Finset (candidatePIndices c L)) (g : candidatePIndices c L) (kPeel : ℕ),
      ell+(cut g).card = kPeel+1 → g ∉ big → g.val ∈ candidateSmallPIndices c L →
      ∀ (b₀ b₁ : GroupMarkedLists (fun j : big => candidatePBand (c*L) j.val.val)
        (fun j : big => ell+(cut j.val).card) → ℂ),
      (∀ l, ‖b₀ l‖ ≤ L^Cb) → (∀ l, ‖b₁ l‖ ≤ L^Cb) →
      ∀ (lo hi : ℕ) (aM vM ν₀ ν₁ : ℝ) (qM : ℕ) [NeZero qM]
        (χM : DirichletCharacter ℂ qM),
      vM ≤ vMax → (qM : ℝ) ≤ L^Cmod →
      |ν₀| ≤ L^Sfreq → |ν₁| ≤ L^Sfreq →
      ∀ (σ : ℝ) (qQ : ℕ) [NeZero qQ] (χQ : DirichletCharacter ℂ qQ),
      (qQ : ℝ) ≤ L^Tmod → |σ| ≤ L^Sshift →
      let P₀ := fun j : candidatePIndices c L => candidatePBand (c*L) j.val
      let mass := fun j : candidatePIndices c L => ∑ p ∈ P₀ j, 1/(p : ℝ)
      let marks := fun j : candidatePIndices c L => ell+(cut j).card
      let pool := (candidatePIndices c L).biUnion (candidatePBand (c*L))
      let α₀ := fun n => (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM vM) n : ℂ)*
        (χM (n : ZMod qM)*typeIIPhase ν₀ n)
      let α₁ := fun n => (typeIIRestrict (Ioc lo hi) (ambientRoughIntervalTypeIIAlpha γrough L S aM vM) n : ℂ)*
        (χM (n : ZMod qM)*typeIIPhase ν₁ n)
      let β := fun n => if n ∈ candidateRoughBand c L jStar then
        typeIIPhase σ n*χQ (n : ZMod qQ) else 0
      let γ := fun n => conj (candidateResidualPrimeCoefficient c L rQ jStar hrQ hj
        take hkeep (candidateAllocationFourierTwist c L rQ jStar take ξ) n)
      let F₀ := fun n : ℤ => selectedPeeledEndpoint P₀ (1/2) mass marks g kPeel big b₀
        pool α₀ β γ n.natAbs
      let G₀ := fun n : ℤ => selectedPeeledEndpoint P₀ (1/2) mass marks g kPeel big b₁
        pool α₁ β γ n.natAbs
      ∀ (groups : Finset ℕ), groups ⊆ candidatePIndices c L →
      let P := fun j : groups => candidatePBand (c*L) j.val
      let V := fun j : groups => ∑ p ∈ P j, 1/(p : ℝ)
      ∀ (probes : groups → Finset (Fin Jprobe)) (r t : Finset groups)
        (A B : Finset (RepeatedBigFlatIndex groups Jprobe ell)),
      A ⊆ r.sigma (repeatedBigPrimeProbeSlots probes) → A.Nonempty →
      B ⊆ t.sigma (repeatedBigPrimeProbeSlots probes) → B.Nonempty →
      (∃ i : A, i.val.1.val ∈ candidateBigPIndices c L) →
      ∀ (hU : ∀ j (i : Fin ell),
          (⟨j, Sum.inr i⟩ : RepeatedBigFlatIndex groups Jprobe ell) ∉ A ∪ B)
        (hAB : Disjoint A B) (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L^K →
      ∀ (Q : ℕ) (h : ℝ), 0 < h → h ≤ 1 →
      ∀ (d e : ℤ) (χ ψ : BoundedPrimitiveCharacter Q) (a b v Z : ℝ),
      0 < Z → |a| ≤ L^W → |2*Real.pi*v| ≤ L^W →
      let HA := Real.exp (((d : ℝ)-1)*h)
      let HB := Real.exp (((e : ℝ)-1)*h)
      let Y := Z*(HA*HB)
      Real.log Y ≤ 6*L →
      (∀ (x : ∀ i : A, P i.val.1) (y : ∀ i : B, P i.val.1),
        (starRingEnd ℂ) (primeProductCellCharacter (fun i : A => P i.val.1) h d χ x) *
          physicalPhase (-(a+b+2*Real.pi*v)) (∏ i, (x i).val) ≠ 0 →
        (starRingEnd ℂ) (primeProductCellCharacter (fun i : B => P i.val.1) h e ψ y) *
          physicalPhase (-(a+b+2*Real.pi*v)) (∏ i, (y i).val) ≠ 0 →
        Real.exp (2*dSource*L) ≤
          Z*((((∏ i, (x i).val)*(∏ i, (y i).val)) : ℕ) : ℝ)/2) →
      ‖∑ aux : PhysicalAuxLabels P (repeatedBigAuxCut A B),
        (physicalAuxMass V (repeatedBigAuxCut A B) aux : ℂ) *
          ((starRingEnd ℂ) (primeProductCellCharacter (fun i : A => P i.val.1) h d χ
              (repeatedBigAuxSplitEquiv P A B hU hAB aux).1) *
            (starRingEnd ℂ) (primeProductCellCharacter (fun i : B => P i.val.1) h e ψ
              (repeatedBigAuxSplitEquiv P A B hU hAB aux).2)) *
          physicalPhase (-(a+b+2*Real.pi*v)) (physicalFreeFactor (repeatedBigAuxCut A B) aux) *
          harmonicCellPairing Y Z a b (2*Real.pi*v)
            (k*(physicalFreeFactor (repeatedBigAuxCut A B) aux : ℤ)) F₀ G₀‖
        ≤ Y*L^(-D) := by
  classical
  obtain ⟨J,hsource⟩ := exists_actual_peeled_rough_source_fourier_precision hZ hc hdSource hγ hv hρ
  refine ⟨J,?_⟩
  intro jStar hjStar D Jprobe ell Cb K Tmod Sshift Cmod Sfreq W hK
  obtain ⟨E,henergy⟩ := exists_actual_rough_peeled_source_energy hc hγ Jprobe ell Cb
  obtain ⟨q,hq,hcell⟩ := exists_candidate_cell_local_energy_decay hc Jprobe D E K hK
  obtain ⟨S₀,hS₀,hfourier⟩ := hsource jStar hjStar
    ((2*D+E+2)+2*q+K+1) Jprobe ell Cb Tmod Sshift Cmod Sfreq (K+q) W
  refine ⟨q,hq,S₀,hS₀,?_⟩
  intro S hS
  filter_upwards [henergy,hfourier S hS,hcell,
    eventually_actual_occupied_source_cell_scale hc hdSource Jprobe K q hq,
    eventually_ge_atTop (1 : ℝ)] with L he hf hcell hscale hL
  intro rQ hrQ hj take hkeep ξ cut big g kPeel hkPeel hgb hgSmall b₀ b₁ hb₀ hb₁
    lo hi aM vM ν₀ ν₁ qM hqMInst χM hvM hqM hν₀ hν₁
    σ qQ hqQInst χQ hqQ hσ P₀ mass marks pool α₀ α₁ β γ F₀ G₀
    groups hgroups P V probes r t A B hA hAne hB hBne hAbig hU hAB k hk hkB
    Q h hh hh1 d e χ ψ a b v Z hZpos ha hv HA HB Y hlog hproduct
  have hYpos : 0 < Y := mul_pos hZpos (mul_pos (Real.exp_pos _) (Real.exp_pos _))
  have hnonneg : 0 ≤ Y*L^(-D) := mul_nonneg hYpos.le
    (Real.rpow_nonneg (zero_le_one.trans hL) _)
  by_cases hx : ∃ x : (∀ i : A, P i.val.1),
      (starRingEnd ℂ) (primeProductCellCharacter (fun i : A => P i.val.1) h d χ x) *
        physicalPhase (-(a+b+2*Real.pi*v)) (∏ i, (x i).val) ≠ 0
  · by_cases hy : ∃ y : (∀ i : B, P i.val.1),
        (starRingEnd ℂ) (primeProductCellCharacter (fun i : B => P i.val.1) h e ψ y) *
          physicalPhase (-(a+b+2*Real.pi*v)) (∏ i, (y i).val) ≠ 0
    · obtain ⟨x,hx0⟩ := hx
      obtain ⟨y,hy0⟩ := hy
      have hkAbs : |(k : ℝ)| ≤ L^K := by
        simpa only [Nat.cast_natAbs,Int.cast_abs] using hkB
      have hs := hscale groups hgroups ell probes r t A B hA hAne hB hBne hAbig
        Q h hh hh1 d e χ ψ (-(a+b+2*Real.pi*v)) x y hx0 hy0 k hk hkAbs
        Z hZpos (hproduct x y hx0 hy0)
      have he₀ := he rQ jStar hrQ hj take hkeep ξ cut big g kPeel hkPeel hgb b₀ hb₀
        lo hi S aM vM ν₀ qM χM σ qQ χQ Y hs.2.1 hlog Z a b (2*Real.pi*v)
      have he₁ := he rQ jStar hrQ hj take hkeep ξ cut big g kPeel hkPeel hgb b₁ hb₁
        lo hi S aM vM ν₁ qM χM σ qQ χQ Y hs.2.1 hlog Z a b (2*Real.pi*v)
      apply hcell groups hgroups ell probes r t A B hA hAne hB hBne hU hAB
        k hk hkB Q h hh hh1 d e χ ψ a b v Y Z F₀ G₀ hYpos he₀.1 he₁.2
      intro _ _ qRat hqRat0 hqRat aRat
      exact @hf rQ hrQ hj take hkeep ξ cut big g kPeel hkPeel hgb hgSmall b₀ hb₀
        lo hi aM vM ν₀ qM hqMInst χM hvM hqM hν₀
        σ qQ hqQInst χQ hqQ hσ Y (|(k : ℝ)| *(HA*HB)/L^q) Z a (2*Real.pi*v)
        hs.1 hlog hs.2.2.2.1 hs.2.2.2.2 hZpos ha hv qRat hqRat0 hqRat aRat
    · rw [candidate_cell_aux_sum_eq_zero_of_no_right P V A B hU hAB k Q h d e χ ψ Y Z a b v F₀ G₀ hy, norm_zero]
      exact hnonneg
  · rw [candidate_cell_aux_sum_eq_zero_of_no_left P V A B hU hAB k Q h d e χ ψ Y Z a b v F₀ G₀ hx, norm_zero]
    exact hnonneg

end Bounty.WeakZeroFree
