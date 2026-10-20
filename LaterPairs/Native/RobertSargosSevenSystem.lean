module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.RobertSargosReducedSystem

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                        
                                                                        

noncomputable section
namespace TaoTrudgianYang2025

structure RobertSargosSevenPoint where
  r : ℤ
  q₁ : ℤ
  q₂ : ℤ
  h₁ : ℤ
  h₂ : ℤ
  n₁ : ℤ
  n₂ : ℤ
  deriving DecidableEq

structure RobertSargosSevenSystem (R H Q N δ : ℝ) (p : RobertSargosSevenPoint) : Prop where
  r_ne_zero : p.r ≠ 0
  r_bound : |(p.r:ℝ)| ≤ R
  q₁_support : |(p.q₁:ℝ)| ∈ Set.Icc Q (2*Q)
  q₂_support : |(p.q₂:ℝ)| ∈ Set.Icc Q (2*Q)
  h₁_support : (p.h₁:ℝ) ∈ Set.Icc H (2*H)
  h₂_support : (p.h₂:ℝ) ∈ Set.Icc H (2*H)
  n₁_support : (p.n₁:ℝ) ∈ Set.Icc 1 N
  n₂_support : (p.n₂:ℝ) ∈ Set.Icc 1 N
  same_sign : 0 < p.q₁*p.q₂
  linear : p.r*p.n₁+p.h₁*p.q₁ = p.r*p.n₂+p.h₂*p.q₂
  near : |robertSargosQuadratic p.r p.q₁ p.h₁ p.n₁-
    robertSargosQuadratic p.r p.q₂ p.h₂ p.n₂| ≤ δ*H*Q^2

def robertSargosDisplacementPoint (p : RobertSargosSevenPoint) : RobertSargosPoint :=
  ⟨p.r,p.q₁,p.q₂,p.h₁,p.h₂,p.n₁-p.n₂⟩

def robertSargosSevenRestore (q : RobertSargosPoint) (n : ℤ) : RobertSargosSevenPoint :=
  ⟨q.r,q.q₁,q.q₂,q.h₁,q.h₂,q.d+n,n⟩

theorem robertSargos_seven_restore (p : RobertSargosSevenPoint) :
    robertSargosSevenRestore (robertSargosDisplacementPoint p) p.n₂ = p := by
  cases p
  simp [robertSargosSevenRestore,robertSargosDisplacementPoint]

theorem robertSargos_displacement_joint_injective {p q : RobertSargosSevenPoint}
    (hd : robertSargosDisplacementPoint p = robertSargosDisplacementPoint q)
    (hn : p.n₂ = q.n₂) : p = q := by
  calc
    p = robertSargosSevenRestore (robertSargosDisplacementPoint p) p.n₂ :=
      (robertSargos_seven_restore p).symm
    _ = robertSargosSevenRestore (robertSargosDisplacementPoint q) q.n₂ := by rw [hd,hn]
    _ = q := robertSargos_seven_restore q

end TaoTrudgianYang2025
