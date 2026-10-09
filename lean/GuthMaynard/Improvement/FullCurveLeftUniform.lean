import GuthMaynard.Improvement.CurveModulus

open MathCollab.Density
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- On the entire closed left interval the exact piecewise curve has one
constant before sigma and height. Its two interior joins cause no loss. -/
theorem full_density_curve_uniform_left {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1/2 ≤ σ → σ ≤ 3/4 → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(fullDensityExponent σ+ε) := by
  obtain ⟨C₁,hC₁,h₁⟩ := density_curve_uniform_on_interval
    (a:=(1/2:ℝ)) (b:=9/13) (K:=4) (f:=fun σ => 3*(1-σ)/(2-σ))
    (by norm_num) (by norm_num) (fun _ _ hx hxy hy => ingham_curve_modulus hx hxy hy)
    ingham_lower_density hε
  obtain ⟨C₂,hC₂,h₂⟩ := density_curve_uniform_on_interval
    (a:=(9/13:ℝ)) (b:=5/7) (K:=4) (f:=fun σ => 18*(1-σ)/(7*σ+3))
    (by norm_num) (by norm_num) (fun _ _ hx hxy hy => short_curve_modulus hx hxy hy)
    (fun _ hx hy _ he => short_density hx hy he) hε
  obtain ⟨C₃,hC₃,h₃⟩ := density_curve_uniform_on_interval
    (a:=(5/7:ℝ)) (b:=3/4) (K:=4) (f:=fun σ => (9/4)*(1-σ))
    (by norm_num) (by norm_num) (by intros; linarith)
    (fun _ hx hy _ he => upper_curve_density hx hy he) hε
  refine ⟨C₁+C₂+C₃,by positivity,?_⟩
  intro σ T hσ hσ' hT
  unfold fullDensityExponent
  split_ifs with h₁σ h₂σ
  · exact (h₁ σ T hσ h₁σ hT).trans
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · exact (h₂ σ T (by linarith) h₂σ hT).trans
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · exact (h₃ σ T (by linarith) hσ' hT).trans
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.full_density_curve_uniform_left
