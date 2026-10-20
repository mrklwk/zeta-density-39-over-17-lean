module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.ZetaMomentKernel
public import LaterPairs.Native.ZetaSourceLogScales

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

 
                                             

                                                                 
                                                                         
                                                                    


noncomputable section

open Complex MeasureTheory Set
open scoped ContDiff

namespace TaoTrudgianYang2025

structure IntervalC1Bound (f : ℝ → ℂ) (a b M : ℝ) : Prop where
  nonneg : 0 ≤ M
  smooth : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 f x
  norm_le : ∀ x ∈ Icc a b, ‖f x‖ ≤ M
  variation_le : (∫ x in a..b, ‖deriv f x‖) ≤ M

theorem intervalC1Bound_const (c : ℂ) (a b : ℝ) :
    IntervalC1Bound (fun _ : ℝ => c) a b ‖c‖ := by
  refine ⟨norm_nonneg _, fun _ _ => contDiffAt_const, fun _ _ => le_rfl, ?_⟩
  simp only [deriv_const, norm_zero, intervalIntegral.integral_zero, norm_nonneg]

end TaoTrudgianYang2025
