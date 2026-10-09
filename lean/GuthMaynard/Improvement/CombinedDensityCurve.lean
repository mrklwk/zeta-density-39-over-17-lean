import GuthMaynard.Improvement.FullCurveLeftUniform
import MathCollab.Density.Stronger.NativeDensity

open MathCollab.Density
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- The combined curve adds the native twelfth-moment density theorem strictly
above 3/4. The count is the identical MathCollab actual-zero multiplicity count. -/
def combinedDensityExponent (σ : ℝ) : ℝ :=
  if σ ≤ 9/13 then 3*(1-σ)/(2-σ)
  else if σ ≤ 5/7 then 18*(1-σ)/(7*σ+3)
  else if σ ≤ 3/4 then (9/4)*(1-σ)
  else 3*(1-σ)/(2*σ)

theorem combined_density_curve {σ ε : ℝ}
    (hσ : 1/2 ≤ σ) (_hσ' : σ ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(combinedDensityExponent σ+ε) := by
  unfold combinedDensityExponent
  split_ifs with h₁ h₂ h₃
  · exact ingham_lower_density σ hσ h₁ ε hε
  · exact short_density (by linarith) h₂ hε
  · exact upper_curve_density (by linarith) h₃ hε
  · exact Stronger.stronger_density_bound_native (by linarith) hε

theorem combined_density_curve_endpoints :
    combinedDensityExponent (1/2) = 1 ∧
    combinedDensityExponent (9/13) = 12/17 ∧
    combinedDensityExponent (5/7) = 9/14 ∧
    combinedDensityExponent (3/4) = 9/16 ∧
    combinedDensityExponent 1 = 0 := by
  norm_num [combinedDensityExponent]

theorem combinedDensityExponent_eq_full_of_le {σ : ℝ} (hσ : σ ≤ 3/4) :
    combinedDensityExponent σ = fullDensityExponent σ := by
  simp only [combinedDensityExponent,fullDensityExponent,ite_eq_left hσ]

/-- A single constant works on the closed left interval together with every
closed right interval separated from the strict 3/4 boundary by delta>0.
The constant may depend on epsilon and delta, but precedes sigma and height. -/
theorem combined_density_curve_uniform_away_boundary {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1/2 ≤ σ → σ ≤ 1 →
      (σ ≤ 3/4 ∨ 3/4+δ ≤ σ) → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(combinedDensityExponent σ+ε) := by
  obtain ⟨C₁,hC₁,hleft⟩ := full_density_curve_uniform_left hε
  by_cases ha : (3/4:ℝ)+δ < 1
  · obtain ⟨C₂,hC₂,hright⟩ := density_curve_uniform_on_interval
      (a:=(3/4:ℝ)+δ) (b:=1) (K:=4) (f:=fun σ => 3*(1-σ)/(2*σ)) ha
      (by norm_num) (fun _ _ hx hxy hy => stronger_curve_modulus (by linarith) hxy hy)
      (fun _ hx _ _ he => Stronger.stronger_density_bound_native (by linarith) he) hε
    refine ⟨C₁+C₂,by positivity,?_⟩
    intro σ T hσ hσ' hcases hT
    rcases hcases with hs | hs
    · rw [combinedDensityExponent_eq_full_of_le hs]
      exact (hleft σ T hσ hs hT).trans
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    · have hh : combinedDensityExponent σ = 3*(1-σ)/(2*σ) := by
        simp only [combinedDensityExponent,ite_eq_right (show ¬σ ≤ 9/13 by linarith),
          ite_eq_right (show ¬σ ≤ 5/7 by linarith),ite_eq_right (show ¬σ ≤ 3/4 by linarith)]
      rw [hh]
      exact (hright σ T hs hσ' hT).trans
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · refine ⟨C₁,hC₁,?_⟩
    intro σ T hσ _hσ' hcases hT
    rcases hcases with hs | hs
    · rw [combinedDensityExponent_eq_full_of_le hs]
      exact hleft σ T hσ hs hT
    · rw [zetaDensityCount_zero_of_one_le (show 1 ≤ σ by linarith)]
      simp only [Nat.cast_zero]
      positivity

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.combined_density_curve
#print axioms GuthMaynard.Improvement.combined_density_curve_endpoints
#print axioms GuthMaynard.Improvement.combined_density_curve_uniform_away_boundary
