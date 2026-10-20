module
public import WrittenDensity.RightZero
public import TraceAlternatives.CurrentDensityCurve

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Montgomery.WrittenDensity
open MathCollab.Density

/-- A uniform actual-count consequence, with the constant preceding every height. -/
def DensityBound (σ p ε : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
    (zetaDensityCount σ T : ℝ) ≤ C*T^(p+ε)

theorem density_weaken {σ p q ε : ℝ} (h : DensityBound σ p ε)
    (hpq : p ≤ q) : DensityBound σ q ε := by
  obtain ⟨C,hC,h⟩ := h
  refine ⟨C,hC,?_⟩
  intro T hT
  exact (h T hT).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T) (by linarith)) hC.le)

theorem density_literal {σ p ε : ℝ} (h : DensityBound σ p ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ,ρ∈F ↔ _root_.riemannZeta ρ=0 ∧ 0<ρ.re ∧ ρ.re<1 ∧
        σ≤ρ.re ∧ |ρ.im|≤T) →
      ((∑ ρ∈F,analyticOrderNatAt _root_.riemannZeta ρ : ℕ):ℝ) ≤ C*T^(p+ε) := by
  obtain ⟨C,hC,h⟩ := h
  refine ⟨C,hC,?_⟩
  intro T hT F hF
  have he : F=zetaZeroFinset σ (-T) T := by
    ext ρ
    rw [hF,mem_zetaDensityFinset]
    simp only [IsNontrivialZetaZero,and_assoc]
  simpa only [he,zetaDensityCount,zetaSlabCount,zetaMultiplicity] using h T hT

/-- Rational enclosures used only to compare the exact algebraic source endpoint. -/
theorem source_transition_endpoint_bounds :
    (3132/4000 : ℝ) ≤ (201+Real.sqrt 145)/272 ∧
    (201+Real.sqrt 145)/272 ≤ (3133/4000 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 145)
  have hn := Real.sqrt_nonneg (145:ℝ)
  constructor <;> nlinarith

end Montgomery.WrittenDensity
