module
public import TraceAlternatives.FullDashedComparisons

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density

/-- Literal analytic-order sum for actual mathlib zeta zeros, including
both ordinate signs and the closed ordinate cutoff. -/
theorem literal_density_full_dashed (σ ε : ℝ) (hlo : 4/5≤σ) (hhi : σ≤7/8)
    (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ T : ℝ, 2≤T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ∈F ↔ riemannZeta ρ=0 ∧ 0<ρ.re ∧ ρ.re<1 ∧
        σ≤ρ.re ∧ |ρ.im|≤T) →
      ((∑ ρ∈F, analyticOrderNatAt riemannZeta ρ : ℕ):ℝ) ≤
        C*T^(fullDashedExponent σ+ε) := by
  obtain ⟨C,hC,h⟩ := density_full_dashed hlo hhi hε
  refine ⟨C,hC,?_⟩
  intro T hT F hF
  have he : F=zetaZeroFinset σ (-T) T := by
    ext ρ
    rw [hF,mem_zetaDensityFinset]
    simp only [IsNontrivialZetaZero,and_assoc]
  simpa only [he,zetaDensityCount,zetaSlabCount,zetaMultiplicity] using h T hT

end Montgomery.RationalMoment.RightDetector.Physical
