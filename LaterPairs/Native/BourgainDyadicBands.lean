module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.DyadicMomentCutoff
public import LaterPairs.Native.ZetaMomentKernel

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

 
                                                                 

                                                                        
                                                                         
                  


open MeasureTheory Set
open scoped Interval Classical

noncomputable section

namespace TaoTrudgianYang2025

                                                                   
                                                      
theorem exists_bourgain_dyadic_amplitude {a x : ℝ} (hx : a ≤ x)
    {J : ℕ} (hupper : x < a*(2 : ℝ)^J) :
    ∃ j ∈ Finset.range J, a*(2 : ℝ)^j ≤ x ∧ x < 2*(a*(2 : ℝ)^j) := by
  induction J with
  | zero => simp only [pow_zero, mul_one] at hupper; exact False.elim (not_lt_of_ge hx hupper)
  | succ J ih =>
    by_cases h : x < a*(2 : ℝ)^J
    · obtain ⟨j, hj, hlo, hhi⟩ := ih h
      exact ⟨j, Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp hj) (Nat.lt_succ_self J)),
        hlo, hhi⟩
    · refine ⟨J, Finset.mem_range.mpr (Nat.lt_succ_self J), le_of_not_gt h, ?_⟩
      convert hupper using 1
      rw [pow_succ]
      ring

                                                                       
                                                             
end TaoTrudgianYang2025
