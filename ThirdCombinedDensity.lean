module
public import AdjacentZeroDensity
public import ThirdZeroDensity
public import TwoTermCombinedDensity

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MathCollab.Density
namespace Montgomery.ThirdDensity

/-- All three orange branches are complete on their closed intervals. -/
def exponent (σ : ℝ) : ℝ :=
  if σ ≤ 5/7 then Montgomery.TwoTermDensity.exponent σ
  else if σ ≤ 113/153 then 12*(1-σ)/(9*σ-1)
  else if σ ≤ 3/4 then 255*(1-σ)/(153*σ+7)
  else Montgomery.TwoTermDensity.exponent σ

theorem density {σ ε : ℝ} (hσ : 1/2 ≤ σ) (hσ' : σ ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(exponent σ+ε) := by
  unfold exponent
  split_ifs with h₁ h₂ h₃
  · exact Montgomery.TwoTermDensity.density hσ hσ' hε
  · exact Montgomery.RationalMoment.adjacent_density_second (by linarith) h₂ hε
  · exact Montgomery.RationalMoment.third_density_segment (by linarith) h₃ hε
  · exact Montgomery.TwoTermDensity.density hσ hσ' hε

theorem endpoints : exponent (5/7)=12/19 ∧ exponent (113/153)=5/9 ∧
    exponent (3/4)=255/487 := by
  norm_num [exponent,Montgomery.TwoTermDensity.exponent,Montgomery.NewDensity.exponent]

/-- The exact actual-zeta semantic statement, including all strip zeros,
analytic multiplicities, both ordinate signs and closed cutoffs. -/
theorem literal_density (σ ε : ℝ) (hσ : 1/2 ≤ σ) (hσ' : σ ≤ 1)
    (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ riemannZeta ρ=0 ∧ 0<ρ.re ∧ ρ.re<1 ∧
        σ≤ρ.re ∧ |ρ.im|≤T) →
      ((∑ ρ ∈ F, analyticOrderNatAt riemannZeta ρ : ℕ):ℝ) ≤
        C*T^(exponent σ+ε) := by
  obtain ⟨C,hC,h⟩ := density hσ hσ' hε
  refine ⟨C,hC,?_⟩
  intro T hT F hF
  have he : F=zetaZeroFinset σ (-T) T := by
    ext ρ
    rw [hF,mem_zetaDensityFinset]
    simp only [IsNontrivialZetaZero,and_assoc]
  simpa only [he,zetaDensityCount,zetaSlabCount,zetaMultiplicity] using h T hT

end Montgomery.ThirdDensity
