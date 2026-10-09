import GuthMaynard.Improvement.CombinedDensityCurve

set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- The stronger right-hand exponent lies strictly below its limiting value
1/2. This does not assert an estimate at the excluded boundary. -/
theorem combined_curve_right_lt_half {σ : ℝ} (hσ : 3/4 < σ) :
    combinedDensityExponent σ < 1/2 := by
  simp only [combinedDensityExponent,ite_eq_right (show ¬σ ≤ 9/13 by linarith),
    ite_eq_right (show ¬σ ≤ 5/7 by linarith),ite_eq_right (not_le.mpr hσ)]
  apply (div_lt_iff₀ (by linarith : 0 < 2*σ)).mpr
  linarith

/-- No finite one-sided Lipschitz constant crosses the strict boundary.
Consequently the closed-interval finite-grid lemma cannot be applied to the
whole combined exponent. This is not a claim that uniform density is false. -/
theorem combined_curve_boundary_modulus_obstruction (K : ℝ) :
    ∃ σ : ℝ, 3/4 < σ ∧ σ ≤ 1 ∧
      combinedDensityExponent σ+K*(σ-3/4) < combinedDensityExponent (3/4) := by
  let δ : ℝ := 1/(64*(|K|+1))
  have hd : 0 < 64*(|K|+1) := by positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ' : δ ≤ 1/64 := by
    dsimp [δ]
    apply (div_le_iff₀ hd).mpr
    nlinarith [abs_nonneg K]
  have hKδ : K*δ ≤ 1/64 := by
    dsimp [δ]
    rw [mul_one_div]
    apply (div_le_iff₀ hd).mpr
    nlinarith [le_abs_self K]
  refine ⟨3/4+δ,by linarith,by linarith,?_⟩
  have hr := combined_curve_right_lt_half (show (3/4:ℝ)<3/4+δ by linarith)
  have he : combinedDensityExponent (3/4) = 9/16 := by
    norm_num [combinedDensityExponent]
  rw [he]
  have hs : (3/4+δ:ℝ)-3/4 = δ := by ring
  rw [hs]
  linarith

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.combined_curve_right_lt_half
#print axioms GuthMaynard.Improvement.combined_curve_boundary_modulus_obstruction
