module
public import GuthMaynard.Improvement.WeakUpperDensity
public import GuthMaynard.Improvement.GlobalDensityConditional
public import MathCollab.Density.DensityTheorem

@[expose] public section

open MathCollab.Density
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- The padded middle-range estimate closes the interval through sigma=3/4;
above it the preserved, verified density theorem removes any upper-GM premise.
Only the lower Ingham input remains. -/
theorem global_density_fixed_sigma_of_ingham
    (hingham : InghamLowerDensity)
    {σ ε : ℝ} (hσ : 1/2 ≤ σ) (hσ' : σ ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^((39/17)*(1-σ)+ε) := by
  by_cases hlow : σ ≤ 9/13
  · obtain ⟨C,hC,hbound⟩ := hingham σ hσ hlow ε hε
    refine ⟨C,hC,?_⟩
    intro T hT
    exact (hbound T hT).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T)
        (by linarith [(global_density_coefficient_comparisons (σ:=σ)).1 hσ hlow])) hC.le)
  by_cases hmid : σ ≤ 5/7
  · obtain ⟨C,hC,hbound⟩ := short_density
      (le_of_not_ge hlow) hmid hε
    refine ⟨C,hC,?_⟩
    intro T hT
    exact (hbound T hT).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T)
        (by linarith [(global_density_coefficient_comparisons (σ:=σ)).2.1 (le_of_not_ge hlow) hmid])) hC.le)
  by_cases hupper : σ ≤ 3/4
  · exact upper_density (le_of_not_ge hmid) hupper hε
  · obtain ⟨C,hC,hbound⟩ := zeta_density_bound (lt_of_not_ge hupper) hε
    refine ⟨C,hC,?_⟩
    intro T hT
    exact (hbound T hT).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T)
        (by nlinarith)) hC.le)

/-- Actual global39/17, uniform in sigma, with no published upper-GM input.
The lower Ingham premise remains explicit and unasserted here. -/
theorem global_density_uniform_of_ingham
    (hingham : InghamLowerDensity)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1/2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^((39/17)*(1-σ)+ε) := by
  apply zetaDensityCount_uniform_of_fixed_sigma (show (0:ℝ)<39/17 by norm_num) _ hε
  intro σ hσ hσ' ε hε
  exact global_density_fixed_sigma_of_ingham hingham hσ hσ' hε

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.global_density_fixed_sigma_of_ingham
#print axioms GuthMaynard.Improvement.global_density_uniform_of_ingham
