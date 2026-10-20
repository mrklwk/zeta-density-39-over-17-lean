module
public import ZeroFreeDensityBridge

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Montgomery.WrittenDensity
open MathCollab.Density

/-- Actual zero-free count supplies every real exponent on the strict
right half-plane. This is a count consequence, not the source analytic route. -/
theorem density_of_actual_zero {σ p ε : ℝ} (hσ : (7/8 : ℝ) < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T : ℝ) ≤ C*T^(p+ε) := by
  refine ⟨1,by norm_num,?_⟩
  intro T hT
  rw [Montgomery.ZeroFreeHatching.actual_density_count_zero hσ,Nat.cast_zero]
  positivity

/-- Literal counterpart on the exact Mathlib zeta and analytic orders. -/
theorem literal_density_of_actual_zero {σ p ε : ℝ} (hσ : (7/8 : ℝ) < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ,ρ∈F ↔ _root_.riemannZeta ρ=0 ∧ 0<ρ.re ∧ ρ.re<1 ∧
        σ≤ρ.re ∧ |ρ.im|≤T) →
      ((∑ ρ∈F,analyticOrderNatAt _root_.riemannZeta ρ : ℕ):ℝ) ≤ C*T^(p+ε) := by
  refine ⟨1,by norm_num,?_⟩
  intro T hT F hF
  rw [Montgomery.ZeroFreeHatching.literal_density_count_zero σ T hσ F hF,Nat.cast_zero]
  positivity

/-- Full printed last October2 mixed density interval. It follows here
from the independently checked actual7/8 nonvanishing theorem; the original
coefficient-one and reflection proof has its own implementation status. -/
theorem oct2_mixed_five {σ ε : ℝ} (hσ : (23/26 : ℝ) ≤ σ)
    (_hσ' : σ < 1) (_hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T : ℝ) ≤ C*T^(6*(1-σ)/(σ+3)+ε) :=
  density_of_actual_zero (by linarith)

theorem literal_oct2_mixed_five {σ ε : ℝ} (hσ : (23/26 : ℝ) ≤ σ)
    (_hσ' : σ < 1) (_hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ,ρ∈F ↔ _root_.riemannZeta ρ=0 ∧ 0<ρ.re ∧ ρ.re<1 ∧
        σ≤ρ.re ∧ |ρ.im|≤T) →
      ((∑ ρ∈F,analyticOrderNatAt _root_.riemannZeta ρ : ℕ):ℝ) ≤
        C*T^(6*(1-σ)/(σ+3)+ε) :=
  literal_density_of_actual_zero (by linarith)

/-- The older expanded D2 maximum's final piece, with its full source domain. -/
theorem v7_D2_three {σ ε : ℝ} (hσ : (51/58 : ℝ) ≤ σ)
    (_hσ' : σ < 1) (_hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T : ℝ) ≤ C*T^(42*(1-σ)/(13*σ+15)+ε) :=
  density_of_actual_zero (by linarith)

end Montgomery.WrittenDensity
