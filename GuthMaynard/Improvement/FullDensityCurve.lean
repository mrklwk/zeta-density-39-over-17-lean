module
public import GuthMaynard.Improvement.GlobalDensity
public import GuthMaynard.Improvement.UpperCurveDensity
public import MathCollab.Density.DensityTheorem

@[expose] public section

open MathCollab.Density
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- The proved density exponent on the critical half-strip. At sigma=3/4
we use the closed upper-window estimate; the audited coefficient-two theorem
requires a strict inequality. No uniformity in sigma is part of this definition. -/
def fullDensityExponent (σ : ℝ) : ℝ :=
  if σ ≤ 9/13 then 3*(1-σ)/(2-σ)
  else if σ ≤ 5/7 then 18*(1-σ)/(7*σ+3)
  else if σ ≤ 3/4 then (9/4)*(1-σ)
  else 2*(1-σ)

/-- The full proved curve for the actual zero count, with analytic multiplicity
and both ordinate signs. The constant may depend on sigma and epsilon. -/
theorem full_density_curve {σ ε : ℝ}
    (hσ : 1/2 ≤ σ) (_hσ' : σ ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(fullDensityExponent σ+ε) := by
  unfold fullDensityExponent
  split_ifs with h₁ h₂ h₃
  · exact ingham_lower_density σ hσ h₁ ε hε
  · exact short_density (by linarith) h₂ hε
  · exact upper_curve_density (by linarith) h₃ hε
  · exact zeta_density_bound (by linarith) hε

/-- Both interior joins agree exactly. The value at 3/4 retains the closed
upper-window exponent, rather than using the strict coefficient-two theorem. -/
theorem full_density_curve_endpoints :
    fullDensityExponent (1/2) = 1 ∧
    fullDensityExponent (9/13) = 12/17 ∧
    fullDensityExponent (5/7) = 9/14 ∧
    fullDensityExponent (3/4) = 9/16 ∧
    fullDensityExponent 1 = 0 := by
  norm_num [fullDensityExponent]

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.full_density_curve
#print axioms GuthMaynard.Improvement.full_density_curve_endpoints
