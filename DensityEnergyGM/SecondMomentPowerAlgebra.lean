module
public import DensityEnergyGM.ClippedRadicalIntegral
public import Mathlib.Analysis.MeanInequalitiesPow

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Montgomery.RationalMoment

theorem double_sqrt_eq_quarter_rpow {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (Real.sqrt x) = x ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  norm_num

theorem geometric_double_sqrt_eq_rpow {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) :
    Real.sqrt (Real.sqrt K * Real.sqrt B) =
      K ^ (1 / 4 : ℝ) * B ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_mul (Real.sqrt_nonneg K), double_sqrt_eq_quarter_rpow hK,
    double_sqrt_eq_quarter_rpow hB]

theorem second_moment_quarter_shape {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T) :
    (M ^ (36 / 5 : ℝ) + (2 * T) * M ^ (24 / 5 : ℝ)) ^ (1 / 4 : ℝ) ≤
      M ^ (9 / 5 : ℝ) + (2 : ℝ) ^ (1 / 4 : ℝ) *
        T ^ (1 / 4 : ℝ) * M ^ (6 / 5 : ℝ) := by
  calc
    _ ≤ (M ^ (36 / 5 : ℝ)) ^ (1 / 4 : ℝ) +
        ((2 * T) * M ^ (24 / 5 : ℝ)) ^ (1 / 4 : ℝ) :=
      Real.rpow_add_le_add_rpow (by positivity) (by positivity) (by norm_num) (by norm_num)
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0 ≤ 2 * T) (by positivity),
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hT,
        ← Real.rpow_mul hM, ← Real.rpow_mul hM]
      norm_num

theorem energy_height_rpow {E C T : ℝ} (δ p : ℝ)
    (hE : 0 ≤ E) (hC : 0 ≤ C) (hT : 0 ≤ T) :
    (E * C * (2 * T) ^ δ) ^ p =
      E ^ p * C ^ p * (2 : ℝ) ^ (δ * p) * T ^ (δ * p) := by
  rw [Real.mul_rpow (mul_nonneg hE hC) (by positivity), Real.mul_rpow hE hC,
    ← Real.rpow_mul (by positivity : 0 ≤ 2 * T),
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hT]
  ring

end Montgomery.RationalMoment
