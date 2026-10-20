module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                    
                                                                     
                                                                        

noncomputable section
namespace TaoTrudgianYang2025

def robertSargosLinear (r q h n : ℝ) : ℝ := r*n+h*q

def robertSargosQuadratic (r q h n : ℝ) : ℝ :=
  r*n^2+2*h*q*n+h*q^2

def robertSargosReduced (r q₁ q₂ h₁ h₂ d : ℝ) : ℝ :=
  r*d^2+2*h₁*q₁*d+h₁*q₁^2-h₂*q₂^2

def robertSargosTaylorQuadratic (r q h n : ℝ) : ℝ :=
  h*q^2+2*h*q*n-r*n^2-r*h^2-r^2*h

theorem robertSargos_reduced_symmetric {r q₁ q₂ h₁ h₂ d : ℝ}
    (h : r*d+h₁*q₁-h₂*q₂ = 0) :
    robertSargosReduced r q₁ q₂ h₁ h₂ d =
      (h₁*q₁+h₂*q₂)*d+h₁*q₁^2-h₂*q₂^2 := by
  unfold robertSargosReduced
  nlinarith only [mul_eq_zero_of_left h d]

theorem robertSargos_reduced_factor {r q₁ q₂ h₁ h₂ d : ℝ}
    (h : r*d+h₁*q₁-h₂*q₂ = 0) :
    r*robertSargosReduced r q₁ q₂ h₁ h₂ d =
      h₂*(h₂-r)*q₂^2-h₁*(h₁-r)*q₁^2 := by
  unfold robertSargosReduced
  have he : r*d = h₂*q₂-h₁*q₁ := by linarith only [h]
  calc
    r*(r*d^2+2*h₁*q₁*d+h₁*q₁^2-h₂*q₂^2) =
        (r*d)^2+2*h₁*q₁*(r*d)+r*h₁*q₁^2-r*h₂*q₂^2 := by ring
    _ = _ := by rw [he]; ring

end TaoTrudgianYang2025
