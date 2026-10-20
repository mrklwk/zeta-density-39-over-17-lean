module
public import DensityEnergyGM.SquareLevelAlgebra

@[expose] public section

set_option autoImplicit false
namespace GuthMaynard.NativeMoment

theorem rpow_double_square_bound {q x a : ℝ}
    (hq : 0 ≤ q) (hx : 0 ≤ x) (hqx : q ≤ 2 * x ^ 2)
    (ha : 0 ≤ a) (ha4 : a ≤ 4) :
    q ^ a ≤ 16 * x ^ (2 * a) := by
  have htwo : (2 : ℝ) ^ a ≤ 16 := by
    calc
      (2 : ℝ) ^ a ≤ (2 : ℝ) ^ (4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) ha4
      _ = 16 := by norm_num
  calc
    q ^ a ≤ (2 * x ^ 2) ^ a := Real.rpow_le_rpow hq hqx ha
    _ = (2 : ℝ) ^ a * x ^ (2 * a) := by
      rw [Real.mul_rpow (by norm_num) (sq_nonneg x),
        ← Real.rpow_natCast x 2, ← Real.rpow_mul hx]
      norm_num
    _ ≤ 16 * x ^ (2 * a) :=
      mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hx _)

theorem square_level_shape_bound {q x U D T K : ℝ}
    (hq : 0 ≤ q) (hx : 0 ≤ x) (hqx : q ≤ 2 * x ^ 2)
    (hU : 0 < U) (hD : 0 < D) (hT : 0 ≤ T) (_hK : 0 ≤ K)
    (hD2 : D ^ 2 ≤ K) (hD4 : D ^ 4 ≤ K) :
    q ^ 2 * (U ^ 2 / D) ^ (-2 : ℝ) +
      q ^ (18 / 5 : ℝ) * (U ^ 2 / D) ^ (-4 : ℝ) +
      T * q ^ (12 / 5 : ℝ) * (U ^ 2 / D) ^ (-4 : ℝ) ≤
        16 * K * (x ^ 4 * U ^ (-4 : ℝ) +
          x ^ (36 / 5 : ℝ) * U ^ (-8 : ℝ) +
          T * x ^ (24 / 5 : ℝ) * U ^ (-8 : ℝ)) := by
  have hq2 : q ^ 2 ≤ 16 * x ^ 4 := by
    convert rpow_double_square_bound hq hx hqx
      (by norm_num : (0 : ℝ) ≤ 2) (by norm_num) using 1 <;> norm_num
  have hq18 : q ^ (18 / 5 : ℝ) ≤ 16 * x ^ (36 / 5 : ℝ) := by
    convert rpow_double_square_bound hq hx hqx
      (by norm_num : (0 : ℝ) ≤ 18 / 5) (by norm_num) using 1
    norm_num
  have hq12 : q ^ (12 / 5 : ℝ) ≤ 16 * x ^ (24 / 5 : ℝ) := by
    convert rpow_double_square_bound hq hx hqx
      (by norm_num : (0 : ℝ) ≤ 12 / 5) (by norm_num) using 1
    norm_num
  rw [square_level_inverse_power U D hU hD, square_level_inverse_four U D hU hD]
  have h4 : 0 ≤ U ^ (-4 : ℝ) := Real.rpow_nonneg hU.le _
  have h8 : 0 ≤ U ^ (-8 : ℝ) := Real.rpow_nonneg hU.le _
  have h1 := mul_le_mul hq2 hD2 (sq_nonneg D) (by positivity : 0 ≤ 16 * x ^ 4)
  have h2 := mul_le_mul hq18 hD4 (pow_nonneg hD.le 4)
    (mul_nonneg (by norm_num) (Real.rpow_nonneg hx _))
  have h3 := mul_le_mul hq12 hD4 (pow_nonneg hD.le 4)
    (mul_nonneg (by norm_num) (Real.rpow_nonneg hx _))
  have h1' := mul_le_mul_of_nonneg_right h1 h4
  have h2' := mul_le_mul_of_nonneg_right h2 h8
  have h3' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 h8) hT
  nlinarith

end GuthMaynard.NativeMoment
