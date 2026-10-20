module
public import LaterPairs.Native.SquareProductCount
public import TaoTrudgianYang2025.ExponentPairBProcess
public import LaterPairs.PhysicalSharpActualDensity
public import LaterPairs.PhysicalTargetWindows
public import LaterPairs.SharpTargetTailBudgets

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace TaoTrudgianYang2025

/-- The exact B A image of the native new Trudgian--Yang pair. -/
theorem exponentPair_BATYnew2 : ExponentPair (107193/345640) (47947/86410) := by
  convert CubicJointCount.exponentPair_aTrudgianYang_first.bProcess using 1 <;> norm_num
end TaoTrudgianYang2025

namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density.Stronger MathCollab.Density

/-- Full closed later row6 for actual symmetric zeta zeros with analytic
multiplicity. Every analytic input comes from the native proofs. -/
theorem density_sharp_row6 {σ ε : ℝ}
    (hlo : 1959705/2298302 ≤ σ) (hhi : σ ≤ 6482825/7570038) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : ℝ,2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤
        C*T^(597962*(1-σ)/(729216*σ-257415)+ε) := by
  obtain ⟨hf,hs⟩ := sharp_row6_tail_budgets hlo hhi
  simpa only [sharp_row6_density_exponent] using
    density_of_pair_sharp_window TaoTrudgianYang2025.exponentPair_BATYnew2
    (by norm_num) (physicalDetectorWindow_row6 hlo hhi)
    (sharpCountWindow_row6 hlo hhi) hf hs hε
end Montgomery.RationalMoment.RightDetector.Physical
