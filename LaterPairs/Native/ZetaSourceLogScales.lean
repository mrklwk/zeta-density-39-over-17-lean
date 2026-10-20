module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.ZetaMomentKernel

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

 
                                                           

                                                                       
                                                                    
                                                                


noncomputable section

open Complex Filter
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem eventually_const_log_pow_le_rpow (C : ℝ) (hC : 0 ≤ C) (k : ℕ)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, C * (Real.log T) ^ k ≤ T ^ η := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (k : ℝ) hη).const_mul_left C
  filter_upwards [hsmall.bound (by norm_num : (0 : ℝ) < 1), eventually_ge_atTop (1 : ℝ)] with T h hT
  simpa only [Real.rpow_natCast, Real.norm_eq_abs, one_mul,
    abs_of_nonneg (mul_nonneg hC (pow_nonneg (Real.log_nonneg hT) k)),
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ T) η)] using h

end TaoTrudgianYang2025
