module
public import QuadraticPolynomialCount

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

/-- Exact parameters for solid right branch first; this is not a density conclusion. -/
theorem right_quadratic_window_first (σ : ℝ) (hl : (7/9:ℝ) ≤ σ) (hr : σ ≤ (29359/37574:ℝ)) :
    QuadraticWindow σ (1/(11*σ-7)) := by
  have hD : 0 < (11*σ-7) := by linarith
  refine {
    sigma_low := by linarith
    sigma_high := by linarith
    a_low := by
      apply (le_div_iff₀ hD).mpr
      linarith
    a_high := by
      apply (div_lt_iff₀ hD).mpr
      linarith
    first := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hD).mpr
      linarith
    second := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hD).mpr
      linarith
  }

/-- Exact parameters for solid right branch second; this is not a density conclusion. -/
theorem right_quadratic_window_second (σ : ℝ) (hl : (29359/37574:ℝ) ≤ σ) (hr : σ ≤ (1015/1294:ℝ)) :
    QuadraticWindow σ (4744/(14610*σ-3849)) := by
  have hD : 0 < (14610*σ-3849) := by linarith
  refine {
    sigma_low := by linarith
    sigma_high := by linarith
    a_low := by
      apply (le_div_iff₀ hD).mpr
      linarith
    a_high := by
      apply (div_lt_iff₀ hD).mpr
      linarith
    first := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hD).mpr
      linarith
    second := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hD).mpr
      linarith
  }

/-- Exact parameters for solid right branch third; this is not a density conclusion. -/
theorem right_quadratic_window_third (σ : ℝ) (hl : (1015/1294:ℝ) ≤ σ) (hr : σ ≤ (353/447:ℝ)) :
    QuadraticWindow σ (6154/(19062*σ-5079)) := by
  have hD : 0 < (19062*σ-5079) := by linarith
  refine {
    sigma_low := by linarith
    sigma_high := by linarith
    a_low := by
      apply (le_div_iff₀ hD).mpr
      linarith
    a_high := by
      apply (div_lt_iff₀ hD).mpr
      linarith
    first := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hD).mpr
      linarith
    second := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hD).mpr
      linarith
  }

/-- Exact parameters for solid right branch fourth; this is not a density conclusion. -/
theorem right_quadratic_window_fourth (σ : ℝ) (hl : (353/447:ℝ) ≤ σ) (hr : σ ≤ (467/586:ℝ)) :
    QuadraticWindow σ (3782/(11808*σ-3195)) := by
  have hD : 0 < (11808*σ-3195) := by linarith
  refine {
    sigma_low := by linarith
    sigma_high := by linarith
    a_low := by
      apply (le_div_iff₀ hD).mpr
      linarith
    a_high := by
      apply (div_lt_iff₀ hD).mpr
      linarith
    first := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hD).mpr
      linarith
    second := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hD).mpr
      linarith
  }

/-- Exact parameters for solid right branch fifth; this is not a density conclusion. -/
theorem right_quadratic_window_fifth (σ : ℝ) (hl : (467/586:ℝ) ≤ σ) (hr : σ ≤ (4/5:ℝ)) :
    QuadraticWindow σ (2168/(6846*σ-1893)) := by
  have hD : 0 < (6846*σ-1893) := by linarith
  refine {
    sigma_low := by linarith
    sigma_high := by linarith
    a_low := by
      apply (le_div_iff₀ hD).mpr
      linarith
    a_high := by
      apply (div_lt_iff₀ hD).mpr
      linarith
    first := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hD).mpr
      linarith
    second := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hD).mpr
      linarith
  }

end Montgomery.RationalMoment
