import GuthMaynard.Improvement.OrdinaryFourierL2
import GuthMaynard.Improvement.SmoothingFourier
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace GuthMaynard.Improvement

/-- Ordinary real L1/L2 input has a square-integrable literal Fourier transform. -/
theorem ordinary_real_fourier_square_integrable {μ : ℝ → ℝ}
    (h1 : Integrable μ) (h2 : Integrable (fun x => μ x^2)) :
    Integrable (fun ξ => ‖𝓕 (fun x => (μ x : ℂ)) ξ‖^2) := by
  have hc1 := Complex.ofRealCLM.integrable_comp h1
  have hc2 : MemLp (fun x => (μ x : ℂ)) 2 := by
    apply (memLp_two_iff_integrable_sq_norm hc1.aestronglyMeasurable).mpr
    simpa using h2
  exact (memLp_two_iff_integrable_sq_norm
    (ordinary_fourier_memLp hc1 hc2).aestronglyMeasurable).mp
      (ordinary_fourier_memLp hc1 hc2)

/-- Exact ordinary-real Plancherel. Compact support and smoothness are unnecessary. -/
theorem ordinary_real_fourier_integral_square {μ : ℝ → ℝ}
    (h1 : Integrable μ) (h2 : Integrable (fun x => μ x^2)) :
    (∫ ξ, ‖𝓕 (fun x => (μ x : ℂ)) ξ‖^2) = ∫ x, μ x^2 := by
  have hc1 := Complex.ofRealCLM.integrable_comp h1
  have hc2 : MemLp (fun x => (μ x : ℂ)) 2 := by
    apply (memLp_two_iff_integrable_sq_norm hc1.aestronglyMeasurable).mpr
    simpa using h2
  simpa using ordinary_fourier_integral_sq hc1 hc2

/-- The fourth moment is integrable for every nonnegative ordinary L1/L2 input. -/
theorem ordinary_real_fourier_fourth_integrable {μ : ℝ → ℝ}
    (h0 : ∀ x, 0 ≤ μ x) (h1 : Integrable μ)
    (h2 : Integrable (fun x => μ x^2)) :
    Integrable (fun ξ => ‖𝓕 (fun x => (μ x : ℂ)) ξ‖^4) := by
  have hc : Continuous (𝓕 (fun x => (μ x : ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (Complex.ofRealCLM.integrable_comp h1)
  apply ((ordinary_real_fourier_square_integrable h1 h2).const_mul ((∫ x, μ x)^2)).mono'
    ((hc.norm.pow 4).aestronglyMeasurable)
  filter_upwards [] with ξ
  simp only [Pi.pow_apply, Real.norm_eq_abs, abs_pow, abs_norm]
  have hb := fourier_nonneg_mass h0 ξ
  have hm : 0 ≤ ∫ x, μ x := MeasureTheory.integral_nonneg h0
  nlinarith [sq_nonneg (‖𝓕 (fun x => (μ x : ℂ)) ξ‖),
    mul_nonneg (sq_nonneg (‖𝓕 (fun x => (μ x : ℂ)) ξ‖))
      (show 0 ≤ (∫ x, μ x)^2 - ‖𝓕 (fun x => (μ x : ℂ)) ξ‖^2 by nlinarith [norm_nonneg (𝓕 (fun x => (μ x : ℂ)) ξ)])]

/-- Actual fourth-moment bound with exact homogeneous mass and L2 factors. -/
theorem ordinary_real_fourier_integral_fourth {μ : ℝ → ℝ}
    (h0 : ∀ x, 0 ≤ μ x) (h1 : Integrable μ)
    (h2 : Integrable (fun x => μ x^2)) :
    (∫ ξ, ‖𝓕 (fun x => (μ x : ℂ)) ξ‖^4) ≤ (∫ x, μ x)^2*(∫ x, μ x^2) := by
  calc
    _ ≤ ∫ ξ, (∫ x, μ x)^2*‖𝓕 (fun x => (μ x : ℂ)) ξ‖^2 := by
      apply integral_mono (ordinary_real_fourier_fourth_integrable h0 h1 h2)
        ((ordinary_real_fourier_square_integrable h1 h2).const_mul _)
      intro ξ
      have hb := fourier_nonneg_mass h0 ξ
      have hm : 0 ≤ ∫ x, μ x := MeasureTheory.integral_nonneg h0
      have hn := norm_nonneg (𝓕 (fun x => (μ x : ℂ)) ξ)
      nlinarith [mul_nonneg (sq_nonneg (‖𝓕 (fun x => (μ x : ℂ)) ξ‖))
        (show 0 ≤ (∫ x, μ x)^2 - ‖𝓕 (fun x => (μ x : ℂ)) ξ‖^2 by nlinarith)]
    _ = _ := by rw [integral_const_mul, ordinary_real_fourier_integral_square h1 h2]

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.ordinary_real_fourier_square_integrable
#print axioms GuthMaynard.Improvement.ordinary_real_fourier_integral_square
#print axioms GuthMaynard.Improvement.ordinary_real_fourier_fourth_integrable
#print axioms GuthMaynard.Improvement.ordinary_real_fourier_integral_fourth
