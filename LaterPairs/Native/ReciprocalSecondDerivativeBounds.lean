module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

 
                                        

                                                                     
                                                                         


noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology ContDiff

namespace TaoTrudgianYang2025

theorem iteratedDeriv_two_real_inv {g : ℝ → ℝ} {x : ℝ}
    (hg : ContDiffAt ℝ 2 g x) (hne : g x ≠ 0) :
    iteratedDeriv 2 (fun y => (g y)⁻¹) x =
      2 * (deriv g x) ^ 2 / (g x) ^ 3 - iteratedDeriv 2 g x / (g x) ^ 2 := by
  have he : deriv (fun y => (g y)⁻¹) =ᶠ[𝓝 x] fun y => -deriv g y / (g y) ^ 2 := by
    filter_upwards [hg.eventually (by norm_num), hg.continuousAt.eventually_ne hne] with y hgy hy
    exact deriv_fun_inv'' (hgy.differentiableAt (by norm_num)) hy
  have hd := (hg.differentiableAt (by norm_num)).hasDerivAt
  have hdd := ((hg.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have h := (hdd.neg.div (hd.pow 2) (pow_ne_zero 2 hne)).deriv
  change deriv (fun y => -deriv g y / (g y) ^ 2) x = _ at h
  dsimp only [Pi.neg_apply, Pi.pow_apply] at h
  rw [iteratedDeriv_succ, iteratedDeriv_one, he.deriv_eq, h]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp
  ring

end TaoTrudgianYang2025
