module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.AtkinsonNaturalAmplitude
public import LaterPairs.Native.IntervalAmplitudeBounds
public import LaterPairs.Native.ReciprocalSecondDerivativeBounds

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

 
                                                      

                                                                          
                                                                     
                                                             


noncomputable section

open Complex
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem norm_sum_mul_le_discrete_parts (w a : ℕ → ℂ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, w n*a n‖ ≤
      ‖w (N-1)‖*‖∑ n ∈ Finset.range N, a n‖+
        ∑ n ∈ Finset.range (N-1),
          ‖w (n+1)-w n‖*‖∑ k ∈ Finset.range (n+1), a k‖ := by
  have he := Finset.sum_range_by_parts w a N
  simp only [smul_eq_mul] at he
  rw [he]
  apply (norm_sub_le _ _).trans
  rw [norm_mul]
  exact add_le_add le_rfl ((norm_sum_le _ _).trans_eq (by simp only [norm_mul]))

end TaoTrudgianYang2025
