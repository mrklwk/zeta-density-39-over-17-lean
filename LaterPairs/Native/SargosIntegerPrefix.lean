module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.SargosPrefixFourthMajorant

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                                      

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargos_sum_Icc_eq_range {A : Type*} [AddCommMonoid A] (a b : ℤ) (f : ℤ → A) :
    (∑ y ∈ Finset.Icc a b, f y) = ∑ j ∈ Finset.range (b+1-a).toNat, f (a+j) := by
  rw [Int.Icc_eq_finset_map,Finset.sum_map]
  rfl

end TaoTrudgianYang2025
