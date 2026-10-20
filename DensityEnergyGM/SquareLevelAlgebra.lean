module
public import DensityEnergyGM.LargeValuesS2

@[expose] public section

set_option autoImplicit false
namespace GuthMaynard.NativeMoment

/-- Exact amplitude normalization for the square-level application. -/
theorem square_level_inverse_power (U D : ℝ) (hU : 0 < U) (hD : 0 < D) :
    (U ^ 2 / D) ^ (-2 : ℝ) = D ^ 2 * U ^ (-4 : ℝ) := by
  rw [Real.rpow_neg (div_nonneg (sq_nonneg U) hD.le),
    Real.rpow_two, Real.rpow_neg hU.le]
  norm_num
  field_simp

/-- Exact fourth inverse power, retaining the required eighth amplitude power. -/
theorem square_level_inverse_four (U D : ℝ) (hU : 0 < U) (hD : 0 < D) :
    (U ^ 2 / D) ^ (-4 : ℝ) = D ^ 4 * U ^ (-8 : ℝ) := by
  rw [Real.rpow_neg (div_nonneg (sq_nonneg U) hD.le),
    Real.rpow_neg hU.le]
  norm_num
  field_simp

end GuthMaynard.NativeMoment
