module
public import RetunedActualDensity

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density

theorem twelfth_middle_window (σ : ℝ) (hl : 25/32 ≤ σ) (hr : σ ≤ 5/6) :
    QuadraticWindow σ (4/(12*σ-3)) := by
  have hD : 0 < 12*σ-3 := by linarith
  refine {
    sigma_low := by linarith
    sigma_high := by linarith
    a_low := by apply (le_div_iff₀ hD).mpr; linarith
    a_high := by apply (div_lt_iff₀ hD).mpr; linarith
    first := by rw [div_mul_eq_mul_div]; apply (le_div_iff₀ hD).mpr; linarith
    second := by rw [div_mul_eq_mul_div]; apply (le_div_iff₀ hD).mpr; linarith
  }

theorem twelfth_right_window (σ : ℝ) (hl : 5/6 ≤ σ) (hr : σ < 1) :
    QuadraticWindow σ (2/(3*σ+1)) := by
  have hD : 0 < 3*σ+1 := by linarith
  refine {
    sigma_low := by linarith
    sigma_high := hr
    a_low := by apply (le_div_iff₀ hD).mpr; linarith
    a_high := by apply (div_lt_iff₀ hD).mpr; linarith
    first := by rw [div_mul_eq_mul_div]; apply (le_div_iff₀ hD).mpr; linarith
    second := by rw [div_mul_eq_mul_div]; apply (le_div_iff₀ hD).mpr; linarith
  }

/-- A separately stated provable continuation. Its exponent is weaker than
the intended HB-tail branches and is not claimed to complete those targets. -/
theorem density_twelfth_middle {σ ε : ℝ}
    (hl : 25/32 ≤ σ) (hr : σ ≤ 5/6) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(4*(1-σ)/(4*σ-1)+ε) := by
  have hw := twelfth_middle_window σ hl hr
  have hD : 0 < 12*σ-3 := by linarith
  have hD' : 0 < 4*σ-1 := by linarith
  have h12 : 2 ≤ (4/(12*σ-3))*(6*σ-3/2) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hD).mpr
    linarith
  have he : 3*(4/(12*σ-3))*(1-σ)=4*(1-σ)/(4*σ-1) := by field_simp; ring
  simpa only [he] using density_of_twelfth_window hw (by linarith) h12 hε

/-- Unconditional actual-zero continuation supplied by the existing native
moment and new quadratic count. This is not the stronger pictured dashed formula. -/
theorem density_twelfth_right {σ ε : ℝ} (hl : 5/6 ≤ σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(6*(1-σ)/(3*σ+1)+ε) := by
  by_cases hr : σ < 1
  · have hw := twelfth_right_window σ hl hr
    have hD : 0 < 3*σ+1 := by linarith
    have h12 : 2 ≤ (2/(3*σ+1))*(6*σ-3/2) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hD).mpr
      linarith
    have he : 3*(2/(3*σ+1))*(1-σ)=6*(1-σ)/(3*σ+1) := by ring
    simpa only [he] using density_of_twelfth_window hw (by linarith) h12 hε
  · refine ⟨1,by norm_num,?_⟩
    intro T hT
    rw [zetaDensityCount_eq_zero_of_one_le (le_of_not_gt hr)]
    simp only [Nat.cast_zero,one_mul]
    positivity

end Montgomery.RationalMoment.RightDetector
