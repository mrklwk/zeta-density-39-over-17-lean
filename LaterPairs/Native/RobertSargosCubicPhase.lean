module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.FiniteSmoothTaylor
public import LaterPairs.Native.RobertSargosFourthGeometry

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                 
                                                                
                                                 

noncomputable section
open scoped ContDiff
namespace TaoTrudgianYang2025

def robertSargosSymmetricDifference (f : ℝ → ℝ) (m h : ℝ) : ℝ :=
  f (m+h)-f (m-h)

def robertSargosCubicRemainder (f : ℝ → ℝ) (m y : ℝ) : ℝ :=
  f (m+y)-finiteTaylorPolynomial f 3 m (m+y)

def robertSargosMixedRemainder (f : ℝ → ℝ) (m r q h n : ℝ) : ℝ :=
  robertSargosCubicRemainder f m (n+q+h)-
    robertSargosCubicRemainder f m (n+q-h)-
    robertSargosCubicRemainder f m (n+h+r)+
    robertSargosCubicRemainder f m (n-h-r)

theorem robertSargos_cubic_polynomial (f : ℝ → ℝ) (m y : ℝ) :
    finiteTaylorPolynomial f 3 m (m+y) =
      f m+deriv f m*y+iteratedDeriv 2 f m*y^2/2+
        iteratedDeriv 3 f m*y^3/6 := by
  norm_num [finiteTaylorPolynomial,taylor_within_apply,Finset.sum_range_succ,
    iteratedDerivWithin_univ,iteratedDeriv_zero,iteratedDeriv_one,smul_eq_mul]
  ring

theorem robertSargos_mixed_taylor_identity (f : ℝ → ℝ) (m r q h n : ℝ) :
    robertSargosSymmetricDifference f (m+n+q) h-
      robertSargosSymmetricDifference f (m+n) (h+r) =
      -2*r*deriv f m+2*iteratedDeriv 2 f m*robertSargosLinear (-r) q h n+
        iteratedDeriv 3 f m*robertSargosTaylorQuadratic r q h n-
        r^3/3*iteratedDeriv 3 f m+robertSargosMixedRemainder f m r q h n := by
  unfold robertSargosSymmetricDifference robertSargosMixedRemainder
    robertSargosCubicRemainder
  simp only [robertSargos_cubic_polynomial,robertSargosLinear,robertSargosTaylorQuadratic]
  rw [show m+n+q+h = m+(n+q+h) by ring,
    show m+n+q-h = m+(n+q-h) by ring,
    show m+n+(h+r) = m+(n+h+r) by ring,
    show m+n-(h+r) = m+(n-h-r) by ring]
  ring

end TaoTrudgianYang2025
