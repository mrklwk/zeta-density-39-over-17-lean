module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

 
                                     

                                                              
                                                               
                                                             


noncomputable section

open Complex Set
open scoped ContDiff

namespace TaoTrudgianYang2025

structure IntervalC2Bound (f : ℝ → ℂ) (a b M R : ℝ) : Prop where
  nonneg : 0 ≤ M
  scale_nonneg : 0 ≤ R
  smooth : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 f x
  norm_le : ∀ x ∈ Icc a b, ‖f x‖ ≤ M
  deriv_le : ∀ x ∈ Icc a b, ‖deriv f x‖ ≤ M * R
  second_le : ∀ x ∈ Icc a b, ‖iteratedDeriv 2 f x‖ ≤ M * R ^ 2

end TaoTrudgianYang2025
