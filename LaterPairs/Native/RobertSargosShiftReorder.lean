module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.RobertSargosWeightedShift

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                         

noncomputable section
open GafniTao
open scoped BigOperators
namespace TaoTrudgianYang2025

theorem robertSargos_shifted_correlation_m_sum (f : ℝ → ℝ) (M H Q N : ℕ) (q r : ℤ) :
    robertSargosShiftedCorrelation f M H Q N q r =
      (N:ℂ)⁻¹*∑ m ∈ robertSargosCommonMInterval M H Q N,
        ∑ h ∈ robertSargosHOverlap H r, ∑ n ∈ Finset.Icc (1:ℤ) N,
          fordAdditiveCharacter
            (robertSargosSymmetricDifference f (m+n+q) h-
              robertSargosSymmetricDifference f (m+n) (h+r)) := by
  unfold robertSargosShiftedCorrelation
  congr 1
  calc
    _ = ∑ h ∈ robertSargosHOverlap H r, ∑ n ∈ Finset.Icc (1:ℤ) N,
        ∑ m ∈ robertSargosCommonMInterval M H Q N,
          fordAdditiveCharacter
            (robertSargosSymmetricDifference f (m+n+q) h-
              robertSargosSymmetricDifference f (m+n) (h+r)) := Finset.sum_comm
    _ = ∑ h ∈ robertSargosHOverlap H r,
        ∑ m ∈ robertSargosCommonMInterval M H Q N, ∑ n ∈ Finset.Icc (1:ℤ) N,
          fordAdditiveCharacter
            (robertSargosSymmetricDifference f (m+n+q) h-
              robertSargosSymmetricDifference f (m+n) (h+r)) := by
      apply Finset.sum_congr rfl
      intro h _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

end TaoTrudgianYang2025
