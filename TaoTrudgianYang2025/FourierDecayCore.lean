module
public import Mathlib

@[expose] public section
set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Set
open scoped FourierTransform ContDiff Topology
namespace RiemannZeta.GuthMaynard
theorem integrable_iteratedDeriv_of_complex
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (j : ℕ) :
    Integrable (iteratedDeriv j f) := by
  have hcont : Continuous (iteratedDeriv j f) :=
    hf.continuous_iteratedDeriv j
      (WithTop.coe_le_coe.mpr (le_of_lt (ENat.natCast_lt_top j)))
  have hcomp : HasCompactSupport (iteratedDeriv j f) := by
    have haux : ∀ k : ℕ, HasCompactSupport (iteratedDeriv k f) := by
      intro k
      induction k with
      | zero => simpa using hfc
      | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv
    exact haux j
  exact hcont.integrable_of_hasCompactSupport hcomp

/-- Fourier integration by parts for a complex-valued smooth compactly
supported function.  Mathlib's `(2π)^j` normalization is discarded using
`2π ≥ 1`, leaving the source-friendly factor `|ξ|^j`. -/
theorem abs_pow_mul_norm_fourier_complex_le
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (j : ℕ) (ξ : ℝ) :
    |ξ| ^ j * ‖𝓕 f ξ‖ ≤ ∫ x : ℝ, ‖iteratedDeriv j f x‖ := by
  have hall : ∀ n : ℕ, n ≤ (⊤ : ℕ∞) →
      Integrable (iteratedDeriv n f) := by
    intro n _hn
    exact integrable_iteratedDeriv_of_complex f hf hfc n
  have hjtop : j ≤ (⊤ : ℕ∞) := le_of_lt (ENat.natCast_lt_top j)
  have hpoint := congrFun (Real.fourier_iteratedDeriv hf hall hjtop) ξ
  have hfactor :
      ‖(2 * Real.pi * Complex.I * (ξ : ℂ)) ^ j‖ =
        (2 * Real.pi * |ξ|) ^ j := by
    rw [norm_pow, norm_mul, norm_mul]
    simp [abs_of_nonneg Real.pi_pos.le]
  have hnormeq := congrArg norm hpoint
  rw [norm_smul, hfactor] at hnormeq
  have hbase : |ξ| ≤ 2 * Real.pi * |ξ| := by
    nlinarith [abs_nonneg ξ, Real.pi_gt_three]
  have hpow : |ξ| ^ j ≤ (2 * Real.pi * |ξ|) ^ j :=
    pow_le_pow_left₀ (abs_nonneg ξ) hbase j
  calc
    |ξ| ^ j * ‖𝓕 f ξ‖ ≤
        (2 * Real.pi * |ξ|) ^ j * ‖𝓕 f ξ‖ :=
      mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ = ‖𝓕 (iteratedDeriv j f) ξ‖ := hnormeq.symm
    _ ≤ ∫ x : ℝ, ‖iteratedDeriv j f x‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm
        𝐞 MeasureTheory.volume (innerₗ ℝ) (iteratedDeriv j f) ξ

theorem one_add_abs_fourier_decay_of_support_of_bounds_order
    {f : ℝ → ℂ} {C D K₀ Kp : ℝ} (p : ℕ)
    (hf : ContDiff ℝ ∞ f) (hCD : C ≤ D)
    (hSupport : Function.support f ⊆ Set.Icc C D)
    (hK₀ : 0 ≤ K₀) (hKp : 0 ≤ Kp)
    (hBound₀ : ∀ u : ℝ, ‖iteratedDeriv 0 f u‖ ≤ K₀)
    (hBoundp : ∀ u : ℝ, ‖iteratedDeriv p f u‖ ≤ Kp) :
    ∀ ξ : ℝ, (1 + |ξ|) ^ p * ‖𝓕 f ξ‖ ≤
      (2 : ℝ) ^ p * (D - C) * (K₀ + Kp) := by
  have hCompact : HasCompactSupport f := by
    apply HasCompactSupport.intro isCompact_Icc
    intro u hu
    by_contra hne
    exact hu (hSupport (by simpa only [Function.mem_support] using hne))
  have derivativeSupport (j : ℕ) :
      Function.support (iteratedDeriv j f) ⊆ Set.Icc C D := by
    have hTsupport : tsupport (iteratedDeriv j f) ⊆ tsupport f := by
      induction j with
      | zero => simp
      | succ j ih =>
          rw [iteratedDeriv_succ]
          exact tsupport_deriv_subset.trans ih
    exact (subset_tsupport _).trans <|
      hTsupport.trans (closure_minimal hSupport isClosed_Icc)
  have integralBound (j : ℕ) (K : ℝ)
      (hBound : ∀ u : ℝ, ‖iteratedDeriv j f u‖ ≤ K) :
      ∫ u : ℝ, ‖iteratedDeriv j f u‖ ≤ (D - C) * K := by
    have hIntegralEq :
        (∫ u : ℝ, ‖iteratedDeriv j f u‖) =
          ∫ u in Set.Icc C D, ‖iteratedDeriv j f u‖ := by
      rw [← MeasureTheory.integral_indicator measurableSet_Icc]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with u
      by_cases hu : u ∈ Set.Icc C D
      · simp [Set.indicator_of_mem hu]
      · have hz : iteratedDeriv j f u = 0 := by
          by_contra hne
          exact hu (derivativeSupport j (by
            simpa only [Function.mem_support] using hne))
        simp [Set.indicator_of_notMem hu, hz]
    have hNonneg : 0 ≤ ∫ u in Set.Icc C D,
        ‖iteratedDeriv j f u‖ :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc fun _ _ => norm_nonneg _
    have hSetBound := MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (μ := MeasureTheory.volume) (s := Set.Icc C D) (C := K)
      (f := fun u : ℝ => ‖iteratedDeriv j f u‖)
      measure_Icc_lt_top fun u _hu => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact hBound u
    have hMeasure : (MeasureTheory.volume (Set.Icc C D)).toReal = D - C := by
      rw [Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hCD)]
    rw [hIntegralEq]
    calc
      (∫ u in Set.Icc C D, ‖iteratedDeriv j f u‖) =
          ‖∫ u in Set.Icc C D, ‖iteratedDeriv j f u‖‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hNonneg]
      _ ≤ K * (MeasureTheory.volume (Set.Icc C D)).toReal := hSetBound
      _ = (D - C) * K := by rw [hMeasure]; ring
  have hZero (ξ : ℝ) : ‖𝓕 f ξ‖ ≤ (D - C) * K₀ := by
    have h := abs_pow_mul_norm_fourier_complex_le f hf hCompact 0 ξ
    simpa using h.trans (integralBound 0 K₀ hBound₀)
  have hHigh (ξ : ℝ) :
      |ξ| ^ p * ‖𝓕 f ξ‖ ≤ (D - C) * Kp :=
    (abs_pow_mul_norm_fourier_complex_le f hf hCompact p ξ).trans
      (integralBound p Kp hBoundp)
  intro ξ
  by_cases hξ : |ξ| ≤ 1
  · have hWeight : (1 + |ξ|) ^ p ≤ (2 : ℝ) ^ p := by
      exact pow_le_pow_left₀ (by positivity) (by linarith) p
    calc
      (1 + |ξ|) ^ p * ‖𝓕 f ξ‖ ≤
          (2 : ℝ) ^ p * ((D - C) * K₀) :=
        mul_le_mul hWeight (hZero ξ) (norm_nonneg _) (by positivity)
      _ ≤ (2 : ℝ) ^ p * (D - C) * (K₀ + Kp) := by
        have hLen : 0 ≤ D - C := sub_nonneg.mpr hCD
        have hmono : K₀ ≤ K₀ + Kp := le_add_of_nonneg_right hKp
        calc
          (2 : ℝ) ^ p * ((D - C) * K₀) =
              ((2 : ℝ) ^ p * (D - C)) * K₀ := by ring
          _ ≤ ((2 : ℝ) ^ p * (D - C)) * (K₀ + Kp) :=
            mul_le_mul_of_nonneg_left hmono (mul_nonneg (by positivity) hLen)
  · have hξOne : 1 ≤ |ξ| := le_of_lt (lt_of_not_ge hξ)
    have hWeight : (1 + |ξ|) ^ p ≤ (2 : ℝ) ^ p * |ξ| ^ p := by
      have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |ξ|)
        (by linarith : 1 + |ξ| ≤ 2 * |ξ|) p
      simpa [mul_pow] using hp
    calc
      (1 + |ξ|) ^ p * ‖𝓕 f ξ‖ ≤
          ((2 : ℝ) ^ p * |ξ| ^ p) * ‖𝓕 f ξ‖ :=
        mul_le_mul_of_nonneg_right hWeight (norm_nonneg _)
      _ = (2 : ℝ) ^ p * (|ξ| ^ p * ‖𝓕 f ξ‖) := by ring
      _ ≤ (2 : ℝ) ^ p * ((D - C) * Kp) :=
        mul_le_mul_of_nonneg_left (hHigh ξ) (by positivity)
      _ ≤ (2 : ℝ) ^ p * (D - C) * (K₀ + Kp) := by
        have hLen : 0 ≤ D - C := sub_nonneg.mpr hCD
        have hmono : Kp ≤ K₀ + Kp := le_add_of_nonneg_left hK₀
        calc
          (2 : ℝ) ^ p * ((D - C) * Kp) =
              ((2 : ℝ) ^ p * (D - C)) * Kp := by ring
          _ ≤ ((2 : ℝ) ^ p * (D - C)) * (K₀ + Kp) :=
            mul_le_mul_of_nonneg_left hmono (mul_nonneg (by positivity) hLen)

end RiemannZeta.GuthMaynard
