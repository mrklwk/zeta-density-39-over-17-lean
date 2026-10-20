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

open GafniTao Set

namespace TaoTrudgianYang2025

theorem sargos_character_sub_norm_le (x y : ℝ) :
    ‖fordAdditiveCharacter y-fordAdditiveCharacter x‖ ≤ 2*Real.pi*|y-x| := by
  have he : fordAdditiveCharacter y-fordAdditiveCharacter x =
      fordAdditiveCharacter x*(fordAdditiveCharacter (y-x)-1) := by
    rw [mul_sub,mul_one,← fordAdditiveCharacter_add,show x+(y-x) = y by ring]
  rw [he,norm_mul,sargos_character_norm,one_mul]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi*(y-x))
  have hp : Complex.I*((2*Real.pi*(y-x) : ℝ) : ℂ) =
      2*Real.pi*Complex.I*((y-x : ℝ) : ℂ) := by push_cast; ring
  rw [hp] at h
  simpa only [fordAdditiveCharacter,Real.norm_eq_abs,abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2*Real.pi)] using h

end TaoTrudgianYang2025
