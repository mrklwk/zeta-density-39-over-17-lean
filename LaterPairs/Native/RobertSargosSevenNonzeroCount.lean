module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.RobertSargosReducedCount
public import LaterPairs.Native.RobertSargosSevenMultiplicity

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                    

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_quadratic_difference {r q₁ q₂ h₁ h₂ n₁ n₂ : ℝ}
    (h : robertSargosLinear r q₁ h₁ n₁ = robertSargosLinear r q₂ h₂ n₂) :
    robertSargosQuadratic r q₁ h₁ n₁-robertSargosQuadratic r q₂ h₂ n₂ =
      robertSargosReduced r q₁ q₂ h₁ h₂ (n₁-n₂) := by
  have hl : r*(n₁-n₂)+h₁*q₁-h₂*q₂ = 0 := by
    unfold robertSargosLinear at h
    linarith
  unfold robertSargosQuadratic robertSargosReduced
  nlinarith only [mul_eq_zero_of_left hl (2*n₂)]


theorem RobertSargosSevenSystem.linear_real {R H Q N δ : ℝ}
    {p : RobertSargosSevenPoint} (h : RobertSargosSevenSystem R H Q N δ p) :
    robertSargosLinear p.r p.q₁ p.h₁ p.n₁ =
      robertSargosLinear p.r p.q₂ p.h₂ p.n₂ := by
  unfold robertSargosLinear
  exact_mod_cast h.linear

theorem RobertSargosSevenSystem.to_reduced {R H Q N δ : ℝ}
    {p : RobertSargosSevenPoint} (h : RobertSargosSevenSystem R H Q N δ p)
    (hne : p.n₁ ≠ p.n₂) :
    RobertSargosReducedSystem R H Q δ (robertSargosDisplacementPoint p) := by
  refine ⟨h.r_ne_zero,h.r_bound,h.q₁_support,h.q₂_support,h.h₁_support,
    h.h₂_support,h.same_sign,sub_ne_zero.mpr hne,?_,?_⟩
  · change p.r*(p.n₁-p.n₂)+p.h₁*p.q₁-p.h₂*p.q₂ = 0
    nlinarith only [h.linear]
  · change |robertSargosReduced p.r p.q₁ p.q₂ p.h₁ p.h₂ ((p.n₁-p.n₂:ℤ):ℝ)| ≤
      δ*H*Q^2
    rw [Int.cast_sub,← robertSargos_quadratic_difference h.linear_real]
    exact h.near



theorem exists_robertSargos_seven_nonzero_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset RobertSargosSevenPoint) (R H Q N δ : ℝ),
      1 ≤ R → 1 ≤ H → 1 ≤ Q → 1 ≤ N → 0 ≤ δ → R ≤ H/2 →
      (∀ p ∈ S, RobertSargosSevenSystem R H Q N δ p) →
      (∀ p ∈ S, p.n₁ ≠ p.n₂) →
      (S.card:ℝ) ≤ C*(R*N*H*Q)^(1+ε)*(1+δ*Q) := by
  classical
  obtain ⟨C,hC,hcount⟩ := exists_robertSargos_reduced_count ε hε
  refine ⟨C,hC,?_⟩
  intro S R H Q N δ hR hH hQ hN hδ hRH hmem hne
  have hN0 : 0 ≤ N := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hB : 0 ≤ R*H*Q := by positivity
  have ht : ∀ p ∈ S.image robertSargosDisplacementPoint,
      RobertSargosReducedSystem R H Q δ p := by
    intro q hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    exact (hmem p hp).to_reduced (hne p hp)
  have hb := hcount _ R H Q δ hR hH hQ hδ hRH ht
  calc
    _ ≤ N*((S.image robertSargosDisplacementPoint).card:ℝ) :=
      robertSargos_seven_card_le_displacement_image S hN hmem
    _ ≤ N*(C*(R*H*Q)^(1+ε)*(1+δ*Q)) := mul_le_mul_of_nonneg_left hb hN0
    _ = C*(N*(R*H*Q)^(1+ε))*(1+δ*Q) := by ring
    _ ≤ C*(N*(R*H*Q))^(1+ε)*(1+δ*Q) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (robertSargos_count_multiplicity_algebra hN hB hε.le) hC.le) (by positivity)
    _ = _ := by rw [show N*(R*H*Q) = R*N*H*Q from by ring]

end TaoTrudgianYang2025

