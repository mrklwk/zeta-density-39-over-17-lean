module
public import DensityEnergyGM.GcdScaleOptimization

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Montgomery.RationalMoment

theorem sqrt_add_le_sum {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sq_sqrt (add_nonneg ha hb),
    Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg (a + b),
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

theorem sqrt_rpow_half {x : ℝ} (hx : 0 ≤ x) (p : ℝ) :
    Real.sqrt (x ^ p) = x ^ (p / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  congr 1
  ring

theorem gcd_scale_coefficient_sqrt_min {c M H K q : ℝ}
    (hc : 0 ≤ c) (hM : 0 < M) (hH : 0 < H) (hK : 0 < K)
    (hq0 : 1 ≤ q) (hq1 : q ≤ 2) :
    Real.sqrt (c * M ^ q * min (M * K) H) ≤
      Real.sqrt c * M * H ^ ((q - 1) / 2) * K ^ ((2 - q) / 2) := by
  calc
    _ = Real.sqrt c * Real.sqrt (M ^ q * min (M * K) H) := by
      rw [← Real.sqrt_mul hc]
      congr 1
      ring
    _ ≤ Real.sqrt c * (M * H ^ ((q - 1) / 2) * K ^ ((2 - q) / 2)) :=
      mul_le_mul_of_nonneg_left (gcd_scale_sqrt_min hM hH hK hq0 hq1)
        (Real.sqrt_nonneg c)
    _ = _ := by ring

/-- The three exact q=2,9/5,6/5 monomials of the proved sharp moment
after optimizing the same coprime fourth-moment minimum. -/
theorem sharp_second_shape_sqrt_min {M T R E H K : ℝ}
    (hM : 0 < M) (hT : 0 ≤ T) (hR : 0 ≤ R) (hE : 0 ≤ E)
    (hH : 0 < H) (hK : 0 < K) :
    Real.sqrt ((M ^ 2 * E ^ (1 / 2 : ℝ) +
      R * E ^ (1 / 4 : ℝ) * (M ^ (9 / 5 : ℝ) + T ^ (1 / 4 : ℝ) * M ^ (6 / 5 : ℝ))) *
        min (M * K) H) ≤
      M * (E ^ (1 / 4 : ℝ) * H ^ (1 / 2 : ℝ) +
        R ^ (1 / 2 : ℝ) * E ^ (1 / 8 : ℝ) * H ^ (2 / 5 : ℝ) * K ^ (1 / 10 : ℝ) +
        R ^ (1 / 2 : ℝ) * E ^ (1 / 8 : ℝ) * T ^ (1 / 8 : ℝ) *
          H ^ (1 / 10 : ℝ) * K ^ (2 / 5 : ℝ)) := by
  let D := min (M * K) H
  let X := E ^ (1 / 2 : ℝ) * M ^ (2 : ℝ) * D
  let Y := (R * E ^ (1 / 4 : ℝ)) * M ^ (9 / 5 : ℝ) * D
  let Z := (R * E ^ (1 / 4 : ℝ) * T ^ (1 / 4 : ℝ)) * M ^ (6 / 5 : ℝ) * D
  have hX : 0 ≤ X := by dsimp only [X, D]; positivity
  have hY : 0 ≤ Y := by dsimp only [Y, D]; positivity
  have hZ : 0 ≤ Z := by dsimp only [Z, D]; positivity
  have hShape : (M ^ 2 * E ^ (1 / 2 : ℝ) +
      R * E ^ (1 / 4 : ℝ) * (M ^ (9 / 5 : ℝ) + T ^ (1 / 4 : ℝ) * M ^ (6 / 5 : ℝ))) *
        min (M * K) H = X + Y + Z := by
    dsimp only [X, Y, Z, D]
    norm_num
    ring
  have hRootE : Real.sqrt (E ^ (1 / 2 : ℝ)) = E ^ (1 / 4 : ℝ) := by
    rw [sqrt_rpow_half hE]
    norm_num
  have hRootR : Real.sqrt (R * E ^ (1 / 4 : ℝ)) =
      R ^ (1 / 2 : ℝ) * E ^ (1 / 8 : ℝ) := by
    rw [Real.sqrt_mul hR, Real.sqrt_eq_rpow, sqrt_rpow_half hE]
    norm_num
  have hRootT : Real.sqrt (R * E ^ (1 / 4 : ℝ) * T ^ (1 / 4 : ℝ)) =
      R ^ (1 / 2 : ℝ) * E ^ (1 / 8 : ℝ) * T ^ (1 / 8 : ℝ) := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ R * E ^ (1 / 4 : ℝ)), hRootR,
      sqrt_rpow_half hT]
    norm_num
  have hFirst := gcd_scale_coefficient_sqrt_min (c := E ^ (1 / 2 : ℝ))
    (q := 2) (by positivity) hM hH hK (by norm_num) (by norm_num)
  have hSecond := gcd_scale_coefficient_sqrt_min (c := R * E ^ (1 / 4 : ℝ))
    (q := 9 / 5) (by positivity) hM hH hK (by norm_num) (by norm_num)
  have hThird := gcd_scale_coefficient_sqrt_min
    (c := R * E ^ (1 / 4 : ℝ) * T ^ (1 / 4 : ℝ))
    (q := 6 / 5) (by positivity) hM hH hK (by norm_num) (by norm_num)
  rw [hRootE] at hFirst
  rw [hRootR] at hSecond
  rw [hRootT] at hThird
  norm_num at hFirst hSecond hThird
  rw [hShape]
  calc
    _ ≤ Real.sqrt (X + Y) + Real.sqrt Z := sqrt_add_le_sum (add_nonneg hX hY) hZ
    _ ≤ (Real.sqrt X + Real.sqrt Y) + Real.sqrt Z := by
      linarith [sqrt_add_le_sum hX hY]
    _ ≤ _ := by
      simpa! only [X, Y, Z, D, Real.rpow_two, mul_add, add_mul, add_assoc, add_comm,
        add_left_comm, mul_assoc, mul_comm, mul_left_comm] using
        add_le_add (add_le_add hFirst hSecond) hThird

end Montgomery.RationalMoment
