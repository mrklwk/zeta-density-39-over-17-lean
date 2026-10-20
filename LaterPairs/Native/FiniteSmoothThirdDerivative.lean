module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.ContinuousThirdDerivative
public import LaterPairs.Native.FiniteSmoothTaylor

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                               

noncomputable section
open Set GafniTao
open scoped ContDiff
namespace TaoTrudgianYang2025

theorem hasDerivAt_iteratedDeriv_finite
    {F : ℝ → ℝ} {x : ℝ} {n j : ℕ} (hj : j < n)
    (hF : ContDiffAt ℝ n F x) :
    HasDerivAt (iteratedDeriv j F) (iteratedDeriv (j+1) F x) x := by
  have hh : ContDiffAt ℝ (1+j) F x := hF.of_le (by
    exact_mod_cast (show 1+j ≤ n by omega))
  have hd := contDiffAt_iteratedDeriv_finite (n := 1) (j := j) hh
  simpa only [iteratedDeriv_succ] using hd.differentiableAt_one.hasDerivAt

end TaoTrudgianYang2025
