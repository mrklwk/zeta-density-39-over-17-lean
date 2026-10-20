module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.SecondDerivativeScale

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                            

noncomputable section
namespace TaoTrudgianYang2025

theorem third_derivative_rpow_scale {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) :
    1 ≤ μ^(-(1:ℝ)/3) ∧
      (μ^(-(1:ℝ)/3))^3*μ = 1 ∧
      Real.sqrt (μ^(-(1:ℝ)/3)) = μ^(-(1:ℝ)/6) ∧
      1/Real.sqrt (μ^(-(1:ℝ)/3)) = μ^((1:ℝ)/6) := by
  have hR := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hμ hμ1
    (show -(1:ℝ)/3 ≤ 0 by norm_num)
  have hcube : (μ^(-(1:ℝ)/3))^3*μ = 1 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hμ.le]
    norm_num
    rw [Real.rpow_neg_one,inv_mul_cancel₀ hμ.ne']
  have hs : Real.sqrt (μ^(-(1:ℝ)/3)) = μ^(-(1:ℝ)/6) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul hμ.le]
    congr 1
    norm_num
  refine ⟨hR,hcube,hs,?_⟩
  rw [hs,show -(1:ℝ)/6 = -((1:ℝ)/6) by ring,Real.rpow_neg hμ.le]
  simp

end TaoTrudgianYang2025
