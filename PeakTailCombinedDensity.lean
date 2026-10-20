module
public import RightSolidActualDensity
public import DashedInitialActualDensity
public import RetunedTwelfthContinuation
public import ThirdCombinedDensity
public import TwoTermCombinedDensity

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MathCollab.Density
namespace Montgomery.PeakTailDensity

/-- Completed left branches, five solid branches, two dashed branches and the
endpoint monotonicity consequence; then the native-twelfth continuation. -/
def exponent (σ : ℝ) : ℝ :=
  if σ ≤ 7/9 then Montgomery.ThirdDensity.exponent σ
  else if σ ≤ 4/5 then 3*Montgomery.RationalMoment.rightSolidLengthExponent σ*(1-σ)
  else if σ ≤ 289/358 then 2168*(1-σ)/(2282*σ-631)
  else if σ ≤ 163/198 then 566*(1-σ)/(606*σ-173)
  else if σ ≤ 491/596 then 35/114
  else if σ ≤ 5/6 then 4*(1-σ)/(4*σ-1)
  else 6*(1-σ)/(3*σ+1)

theorem density {σ ε : ℝ} (hσ : 1/2 ≤ σ) (hσ' : σ ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(exponent σ+ε) := by
  unfold exponent
  split_ifs with h₁ h₂ h₃ h₄ h₅ h₆
  · exact Montgomery.ThirdDensity.density hσ hσ' hε
  · exact Montgomery.RationalMoment.RightDetector.density_right_solid (by linarith) h₂ hε
  · exact Montgomery.RationalMoment.RightDetector.density_dashed_first (by linarith) h₃ hε
  · exact Montgomery.RationalMoment.RightDetector.density_dashed_second (by linarith) h₄ hε
  · obtain ⟨C,hC,hb⟩ := Montgomery.RationalMoment.RightDetector.density_dashed_second_plateau hε
    exact ⟨C,hC,hb σ (by linarith)⟩
  · exact Montgomery.RationalMoment.RightDetector.density_twelfth_middle (by linarith) h₆ hε
  · exact Montgomery.RationalMoment.RightDetector.density_twelfth_right (by linarith) hε

theorem endpoints : exponent (3/4)=255/487 ∧ exponent (39/50)=33/79 ∧
    exponent (4/5)=2168/5973 ∧ exponent (289/358)=69/200 ∧
    exponent (163/198)=35/114 ∧ exponent (491/596)=35/114 ∧ exponent (5/6)=2/7 ∧ exponent (7/8)=6/29 := by
  norm_num [exponent,Montgomery.ThirdDensity.exponent,Montgomery.TwoTermDensity.exponent,
    Montgomery.NewDensity.exponent,Montgomery.RationalMoment.rightSolidLengthExponent]

/-- Actual mathlib zeta zeros with analytic multiplicity, both ordinate signs
and closed cutoffs. All analytic inputs are discharged in the proof. -/
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

end Montgomery.PeakTailDensity
