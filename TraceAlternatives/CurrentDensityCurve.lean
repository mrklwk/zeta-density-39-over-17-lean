module
public import TraceAlternatives.FullDashedLiteral

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.CurrentDensity
open MathCollab.Density Montgomery.RationalMoment.RightDetector.Physical

/-- Cumulative actual-zero exponent. The completed eight-piece gain enters
at its exact old joining point; all preserved outer ranges stay available. -/
def exponent (σ : ℝ) : ℝ :=
  if 163/198≤σ ∧ σ≤7/8 then fullDashedExponent σ
  else Montgomery.PeakTailDensity.exponent σ

theorem density {σ ε : ℝ} (hlo : 1/2≤σ) (hhi : σ≤1) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ T : ℝ, 2≤T →
      (zetaDensityCount σ T:ℝ)≤C*T^(exponent σ+ε) := by
  by_cases h : 163/198≤σ ∧ σ≤7/8
  · simpa only [exponent,ite_eq_left h] using density_full_dashed (by linarith [h.1]) h.2 hε
  · simpa only [exponent,ite_eq_right h] using Montgomery.PeakTailDensity.density hlo hhi hε

theorem exponent_le_preserved (σ : ℝ) :
    exponent σ≤Montgomery.PeakTailDensity.exponent σ := by
  by_cases h : 163/198≤σ ∧ σ≤7/8
  · rw [exponent,ite_eq_left h]
    by_cases hj : σ=163/198
    · subst σ
      exact le_of_eq fullDashedExponent_preserved_join
    · exact (fullDashedExponent_lt_preserved (lt_of_le_of_ne h.1 (Ne.symm hj)) h.2).le
  · rw [exponent,ite_eq_right h]

theorem exponent_lt_preserved {σ : ℝ} (hlo : 163/198<σ) (hhi : σ≤7/8) :
    exponent σ<Montgomery.PeakTailDensity.exponent σ := by
  rw [exponent,ite_eq_left ⟨hlo.le,hhi⟩]
  exact fullDashedExponent_lt_preserved hlo hhi

theorem literal_density (σ ε : ℝ) (hlo : 1/2≤σ) (hhi : σ≤1) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ T : ℝ, 2≤T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ∈F ↔ riemannZeta ρ=0 ∧ 0<ρ.re ∧ ρ.re<1 ∧ σ≤ρ.re ∧ |ρ.im|≤T) →
      ((∑ ρ∈F, analyticOrderNatAt riemannZeta ρ : ℕ):ℝ)≤C*T^(exponent σ+ε) := by
  obtain ⟨C,hC,h⟩ := density hlo hhi hε
  refine ⟨C,hC,?_⟩
  intro T hT F hF
  have he : F=zetaZeroFinset σ (-T) T := by
    ext ρ
    rw [hF,mem_zetaDensityFinset]
    simp only [IsNontrivialZetaZero,and_assoc]
  simpa only [he,zetaDensityCount,zetaSlabCount,zetaMultiplicity] using h T hT

end Montgomery.CurrentDensity
