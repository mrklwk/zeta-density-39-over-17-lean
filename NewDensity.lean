module
public import RefinedDensity

@[expose] public section

open Real Complex MathCollab.Density GuthMaynard.Improvement
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace Montgomery.NewDensity

/-- A complete actual-zero density curve. The upper-middle branch is new
relative to the recorded Palomar repository interface. -/
def exponent (σ : ℝ) : ℝ :=
  if σ ≤ 9/13 then 3*(1-σ)/(2-σ)
  else if σ ≤ 3/4 then 18*(1-σ)/(7*σ+3)
  else 3*(1-σ)/(2*σ)

/-- Counts the actual zeros of mathlib's zeta function, with analytic
multiplicity, both ordinate signs and closed height and real-part boundaries.
The constant may depend on sigma and epsilon, and precedes all heights. -/
theorem density {σ ε : ℝ} (hσ : 1/2 ≤ σ) (_hσ' : σ ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T : ℝ) ≤ C*T^(exponent σ+ε) := by
  unfold exponent
  split_ifs with h₁ h₂
  · exact ingham_lower_density σ hσ h₁ ε hε
  · exact Montgomery.Refined.refined_density_middle (by linarith) h₂ hε
  · exact Stronger.stronger_density_bound_native (by linarith) hε

theorem endpoint {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount (3/4) T : ℝ) ≤ C*T^((6/11:ℝ)+ε) := by
  have h := density (σ:=(3/4:ℝ)) (by norm_num) (by norm_num) hε
  norm_num [exponent] at h ⊢
  exact h

/-- This compares actual exponents, rather than only normalized coefficients. -/
theorem strict_improvement {σ : ℝ} (hσ : 5/7 < σ) (hσ' : σ ≤ 3/4) :
    exponent σ < combinedDensityExponent σ := by
  have h₁ : ¬σ ≤ 9/13 := by linarith
  have h₂ : ¬σ ≤ 5/7 := by linarith
  simpa [exponent,combinedDensityExponent,h₁,h₂,hσ',shortDensityExponent] using
    Montgomery.Refined.refined_strict_improvement hσ hσ'

theorem endpoint_gains :
    (9/16:ℝ)-6/11 = 3/176 ∧ (5/9:ℝ)-6/11 = 1/99 ∧
    (6/11:ℝ) < 5/9 ∧ (6/11:ℝ) < 9/16 := by norm_num

end Montgomery.NewDensity
#print axioms Montgomery.NewDensity.density
#print axioms Montgomery.NewDensity.endpoint
#print axioms Montgomery.NewDensity.strict_improvement
