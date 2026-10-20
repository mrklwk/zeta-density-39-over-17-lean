module
public import LaterPairs.Native.SquareProductCount

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace TaoTrudgianYang2025.CubicJointCount
open Expdb
open scoped NNReal

/-- Genuine A image of the native Sargos-D pair, used in the third new pair's
remaining beta cover. All analytic estimates are supplied by the native source. -/
theorem exponentPair_sargosAD_bourgain : ExponentPair (9/217) (1461/1736) := by
  convert exponentPair_sargosD_bourgain.aProcess using 1 <;> norm_num

theorem exponentSumGrowthExponent_le_sargosAD_bourgain
    {α : ℝ≥0} (hα : (α:ℝ) ≤ 1) :
    exponentSumGrowthExponent α ≤ 9/217+(1389/1736)*(α:ℝ) := by
  have h := exponentSumGrowthExponent_le_exponentPairLine_closed
    exponentPair_sargosAD_bourgain α hα
  convert h using 1
  unfold exponentPairLine
  ring
end TaoTrudgianYang2025.CubicJointCount
