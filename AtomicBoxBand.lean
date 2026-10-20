module
public import BoxTimeDensity
public import AtomicRadialBound

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped FourierTransform
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement

theorem log_ten_le_three : Real.log 10 ≤ 3 := by
  have hh : (3/2:ℝ) ≤ Real.exp (1/2) := by linarith [Real.add_one_le_exp (1/2:ℝ)]
  have he1 : Real.exp 1 = (Real.exp (1/2))^2 := by
    calc
      _ = Real.exp ((1/2:ℝ)+1/2) := congrArg Real.exp (by norm_num)
      _ = _ := by rw [Real.exp_add,pow_two]
  have h1 : (9/4:ℝ) ≤ Real.exp 1 := by nlinarith [sq_nonneg (Real.exp (1/2)-3/2)]
  have he3 : Real.exp 3=(Real.exp 1)^3 := by
    rw [show (3:ℝ)=1+1+1 by norm_num,Real.exp_add,Real.exp_add]
    ring
  apply (Real.log_le_iff_le_exp (by norm_num : (0:ℝ)<10)).mpr
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 9/4) h1 3
  rw [he3]
  norm_num at hp ⊢
  linarith

/-- Every logarithmic ratio frequency used by the [1/2,5] cutoff lies
inside the fixed box Fourier band. -/
theorem mellin_frequency_ratio_band {v : ℝ} (hv : v ∈ Icc (1/10:ℝ) 10) :
    |mellinFrequency v| ≤ 1/2 := by
  have hvp : 0 < v := lt_of_lt_of_le (by norm_num) hv.1
  have hu := Real.log_le_log hvp hv.2
  have hl := Real.log_le_log (by norm_num : (0:ℝ)<1/10) hv.1
  rw [one_div,Real.log_inv] at hl
  have hp : 0 < 2*Real.pi := by positivity
  unfold mellinFrequency
  apply abs_le.mpr
  constructor
  · apply (le_div_iff₀ hp).mpr
    nlinarith [log_ten_le_three,Real.pi_gt_three]
  · apply (div_le_iff₀ hp).mpr
    nlinarith [log_ten_le_three,Real.pi_gt_three]

/-- Atomic triple Fourier magnitudes are controlled after radial
cancellation, with a uniform factor eight independent of T,L and W. -/
theorem atomic_ratio_box_domination (W : Finset ℝ) {p : ℝ × ℝ}
    (hp : p ∈ GuthMaynard.Improvement.AtomicCubic.ratioBox) :
    ‖GuthMaynard.Improvement.AtomicCubic.ratioFourierProduct
      (measureFourier (finiteTimeMeasure W)) p‖ ≤
      8*‖GuthMaynard.Improvement.ratioFourierProduct (boxTimeDensity W) p‖ := by
  have hv := mellin_frequency_ratio_band hp.1
  have hy := mellin_frequency_ratio_band hp.2
  have h₁ : |-mellinFrequency p.1| ≤ 1 := by rw [abs_neg]; linarith
  have h₂ : |mellinFrequency p.1-mellinFrequency p.2| ≤ 1 :=
    (abs_sub _ _).trans (by linarith)
  have h₃ : |mellinFrequency p.2| ≤ 1 := by linarith
  have hb₁ := box_time_fourier_domination W h₁
  have hb₂ := box_time_fourier_domination W h₂
  have hb₃ := box_time_fourier_domination W h₃
  simp only [GuthMaynard.Improvement.AtomicCubic.ratioFourierProduct,
    GuthMaynard.Improvement.ratioFourierProduct,norm_mul]
  calc
    _ ≤ (2*‖𝓕 (fun t => (boxTimeDensity W t:ℂ)) (-mellinFrequency p.1)‖)*
        (2*‖𝓕 (fun t => (boxTimeDensity W t:ℂ)) (mellinFrequency p.1-mellinFrequency p.2)‖)*
        (2*‖𝓕 (fun t => (boxTimeDensity W t:ℂ)) (mellinFrequency p.2)‖) := by gcongr
    _ = _ := by ring

end Montgomery.RationalMoment
