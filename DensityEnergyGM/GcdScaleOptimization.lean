module
public import DensityEnergyGM.SecondMomentPowerAlgebra

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Montgomery.RationalMoment

theorem min_le_geometric_rpow {a b w : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    min a b ≤ a ^ w * b ^ (1 - w) := by
  have haId : a ^ w * a ^ (1 - w) = a := by
    rw [← Real.rpow_add ha, show w + (1 - w) = 1 by ring, Real.rpow_one]
  have hbId : b ^ w * b ^ (1 - w) = b := by
    rw [← Real.rpow_add hb, show w + (1 - w) = 1 by ring, Real.rpow_one]
  by_cases hab : a ≤ b
  · rw [min_eq_left hab]
    calc
      a = a ^ w * a ^ (1 - w) := haId.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow ha.le hab (by linarith)) (Real.rpow_nonneg ha.le w)
  · rw [min_eq_right (le_of_not_ge hab)]
    calc
      b = b ^ w * b ^ (1 - w) := hbId.symm
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hb.le (le_of_not_ge hab) hw0)
        (Real.rpow_nonneg hb.le (1 - w))

theorem rpow_half_sq {x : ℝ} (hx : 0 ≤ x) (p : ℝ) :
    (x ^ (p / 2)) ^ 2 = x ^ p := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  ring

/-- Exact pointwise optimization for every positive scale, including
when the transition H/K lies outside the allowed scale interval. -/
theorem gcd_scale_sqrt_min {M H K q : ℝ}
    (hM : 0 < M) (hH : 0 < H) (hK : 0 < K) (hq0 : 1 ≤ q) (hq1 : q ≤ 2) :
    Real.sqrt (M ^ q * min (M * K) H) ≤
      M * H ^ ((q - 1) / 2) * K ^ ((2 - q) / 2) := by
  have hMin := min_le_geometric_rpow (mul_pos hM hK) hH
    (show 0 ≤ 2 - q by linarith) (show 2 - q ≤ 1 by linarith)
  have hWeight : 1 - (2 - q) = q - 1 := by ring
  rw [hWeight] at hMin
  have hMprod : M ^ q * M ^ (2 - q) = M ^ 2 := by
    rw [← Real.rpow_add hM, show q + (2 - q) = 2 by ring]
    norm_num
  have hShape : M ^ q * ((M * K) ^ (2 - q) * H ^ (q - 1)) =
      (M * H ^ ((q - 1) / 2) * K ^ ((2 - q) / 2)) ^ 2 := by
    rw [Real.mul_rpow hM.le hK.le, mul_pow, mul_pow,
      rpow_half_sq hH.le, rpow_half_sq hK.le]
    calc
      M ^ q * (M ^ (2 - q) * K ^ (2 - q) * H ^ (q - 1)) =
          (M ^ q * M ^ (2 - q)) * (H ^ (q - 1) * K ^ (2 - q)) := by ring
      _ = _ := by rw [hMprod]; ring
  have hBound := mul_le_mul_of_nonneg_left hMin (Real.rpow_nonneg hM.le q)
  rw [hShape] at hBound
  have hInside : 0 ≤ M ^ q * min (M * K) H := by positivity
  have hSq := Real.sq_sqrt hInside
  have hRoot := Real.sqrt_nonneg (M ^ q * min (M * K) H)
  have hRight : 0 ≤ M * H ^ ((q - 1) / 2) * K ^ ((2 - q) / 2) := by positivity
  nlinarith

end Montgomery.RationalMoment
