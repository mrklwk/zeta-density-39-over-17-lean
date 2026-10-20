module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.RobertSargosSevenSystem

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                           
                                                               
                                                                   

noncomputable section
namespace TaoTrudgianYang2025

structure RobertSargosTaylorSystem (R H Q N E : ℝ) (p : RobertSargosSevenPoint) : Prop where
  r_ne_zero : p.r ≠ 0
  r_bound : |(p.r:ℝ)| ≤ R
  q₁_support : |(p.q₁:ℝ)| ∈ Set.Icc Q (2*Q)
  q₂_support : |(p.q₂:ℝ)| ∈ Set.Icc Q (2*Q)
  h₁_support : (p.h₁:ℝ) ∈ Set.Icc H (2*H)
  h₂_support : (p.h₂:ℝ) ∈ Set.Icc H (2*H)
  n₁_support : (p.n₁:ℝ) ∈ Set.Icc 1 N
  n₂_support : (p.n₂:ℝ) ∈ Set.Icc 1 N
  same_sign : 0 < p.q₁*p.q₂
  linear : p.h₁*p.q₁-p.r*p.n₁ = p.h₂*p.q₂-p.r*p.n₂
  near : |robertSargosTaylorQuadratic p.r p.q₁ p.h₁ p.n₁-
    robertSargosTaylorQuadratic p.r p.q₂ p.h₂ p.n₂| ≤ E

def robertSargosReverseR (p : RobertSargosSevenPoint) : RobertSargosSevenPoint :=
  ⟨-p.r,p.q₁,p.q₂,p.h₁,p.h₂,p.n₁,p.n₂⟩

theorem robertSargos_reverseR_involution (p : RobertSargosSevenPoint) :
    robertSargosReverseR (robertSargosReverseR p) = p := by
  cases p
  simp [robertSargosReverseR]

theorem robertSargos_reverseR_injective : Function.Injective robertSargosReverseR :=
  Function.LeftInverse.injective robertSargos_reverseR_involution

end TaoTrudgianYang2025
