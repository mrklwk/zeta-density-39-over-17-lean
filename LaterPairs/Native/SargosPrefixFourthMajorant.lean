module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.SargosPrefixMass

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                         

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

theorem norm_sargosFinitePrefix_le_fourierMajorant {N H : ℕ} [NeZero N]
    (f : ZMod N → ℂ) (hH : H ≤ N) :
    ‖sargosFinitePrefix f H‖ ≤ ∑ k : ZMod N, sargosPrefixMajorant k*‖ZMod.dft f k‖ := by
  rw [sargosFinitePrefix_eq_fourier]
  calc
    _ ≤ ∑ k : ZMod N, ‖sargosPrefixKernel H k*ZMod.dft f k‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_sargosPrefixKernel_le_majorant hH k)
        (norm_nonneg _)

end TaoTrudgianYang2025
