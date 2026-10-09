module
public import GuthMaynard.Improvement.CurveBoundaryAudit

@[expose] public section

open scoped BigOperators
set_option autoImplicit false
noncomputable section

/-- Literal statement check: a finite set containing exactly the actual zeros,
raw mathlib zeta and analytic multiplicity, and the fully expanded exponent. -/
theorem literal_combined_curve (σ ε : ℝ) (hσ : 1/2 ≤ σ) (hσ' : σ ≤ 1)
    (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt riemannZeta ρ : ℕ):ℝ) ≤
        C*T^((if σ ≤ 9/13 then 3*(1-σ)/(2-σ)
          else if σ ≤ 5/7 then 18*(1-σ)/(7*σ+3)
          else if σ ≤ 3/4 then (9/4)*(1-σ) else 3*(1-σ)/(2*σ))+ε) := by
  obtain ⟨C,hC,h⟩ := GuthMaynard.Improvement.combined_density_curve hσ hσ' hε
  refine ⟨C,hC,?_⟩
  intro T hT F hF
  have he : F = MathCollab.Density.zetaZeroFinset σ (-T) T := by
    ext ρ
    rw [hF,MathCollab.Density.mem_zetaDensityFinset]
    simp only [MathCollab.Density.IsNontrivialZetaZero, and_assoc]
  simpa only [he,MathCollab.Density.zetaDensityCount,MathCollab.Density.zetaSlabCount,
    MathCollab.Density.zetaMultiplicity,GuthMaynard.Improvement.combinedDensityExponent] using h T hT

#print axioms literal_combined_curve

/-- Explicit uniformity domain, including the epsilon/delta order. -/
theorem literal_uniform_away_boundary (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1/2 ≤ σ → σ ≤ 1 →
      (σ ≤ 3/4 ∨ 3/4+δ ≤ σ) → 2 ≤ T →
      (MathCollab.Density.zetaDensityCount σ T:ℝ) ≤
        C*T^((if σ ≤ 9/13 then 3*(1-σ)/(2-σ)
          else if σ ≤ 5/7 then 18*(1-σ)/(7*σ+3)
          else if σ ≤ 3/4 then (9/4)*(1-σ) else 3*(1-σ)/(2*σ))+ε) := by
  exact GuthMaynard.Improvement.combined_density_curve_uniform_away_boundary hδ hε

#print axioms literal_uniform_away_boundary

example (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1/2 ≤ σ → σ ≤ 1 → 2 ≤ T → (MathCollab.Density.zetaDensityCount σ T : ℝ) ≤ C*T^((39/17)*(1-σ)+ε) := GuthMaynard.Improvement.global_density_uniform hε
#print axioms GuthMaynard.Improvement.global_density_uniform
#print axioms GuthMaynard.Improvement.full_density_curve_uniform_left
#print axioms GuthMaynard.Improvement.combined_curve_boundary_modulus_obstruction
example : GuthMaynard.Improvement.upperCurveSplit (18/25) = 6/7 := by norm_num [GuthMaynard.Improvement.upperCurveSplit]
