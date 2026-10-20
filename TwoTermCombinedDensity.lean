module
public import TwoTermZeroDensity
public import NewDensity
public import DraftCurveComparison

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MathCollab.Density
namespace Montgomery.TwoTermDensity

/-- Strongest assembled curve from the new two-term branches and the
previous complete curve. The constant plateau follows by monotonicity. -/
def exponent (σ : ℝ) : ℝ :=
  if σ ≤ 12/17 then Montgomery.NewDensity.exponent σ
  else if σ ≤ 5/7 then 6*(1-σ)/(8*σ-3)
  else if σ ≤ 21/29 then 12*(1-σ)/(9*σ-1)
  else if σ ≤ 27/37 then 3/5
  else Montgomery.NewDensity.exponent σ

/-- Monotonicity transports the actual endpoint count, with no analytic
estimate or zero-free-region assumption. -/
theorem plateau {σ ε : ℝ} (hσ : 21/29 ≤ σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(3/5+ε) := by
  obtain ⟨C,hC,h⟩ := (Montgomery.RationalMoment.two_term_density_endpoints hε).2
  refine ⟨C,hC,?_⟩
  intro T hT
  exact (show (zetaDensityCount σ T:ℝ) ≤ (zetaDensityCount (21/29) T:ℝ) by
    exact_mod_cast zetaDensityCount_mono hσ le_rfl).trans (h T hT)

/-- Unconditional complete density curve for the same actual zeta zeros,
with analytic multiplicity, both signs and closed boundaries. -/
theorem density {σ ε : ℝ} (hσ : 1/2 ≤ σ) (hσ' : σ ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(exponent σ+ε) := by
  unfold exponent
  split_ifs with h₁ h₂ h₃ h₄
  · exact Montgomery.NewDensity.density hσ hσ' hε
  · exact Montgomery.RationalMoment.two_term_density_first (by linarith) h₂ hε
  · exact Montgomery.RationalMoment.two_term_density_second (by linarith) h₃ hε
  · exact plateau (by linarith) hε
  · exact Montgomery.NewDensity.density hσ hσ' hε

/-- Strict gains over the preceding 651-root complete curve on precisely
this open interval. The old curve resumes at 27/37. -/
theorem strict_improvement {σ : ℝ} (hσ : 12/17 < σ) (hσ' : σ < 27/37) :
    exponent σ < Montgomery.NewDensity.exponent σ := by
  have h₀ : ¬σ ≤ 9/13 := by linarith
  have h₁ : ¬σ ≤ 12/17 := by linarith
  have h₄ : σ ≤ 3/4 := by linarith
  simp only [exponent,ite_eq_right h₁,Montgomery.NewDensity.exponent,
    ite_eq_right h₀,ite_eq_left h₄]
  split_ifs with h₂ h₃ h₅
  · have hh := Montgomery.DraftCurveComparison.left1_strict σ hσ h₂
    convert hh using 1 <;> ring
  · have hh := Montgomery.DraftCurveComparison.left2_strict σ (by linarith) (by linarith)
    convert hh using 1 <;> ring
  · apply (lt_div_iff₀ (show 0 < 7*σ+3 by linarith)).mpr
    linarith
  · linarith

theorem endpoints : exponent (12/17) = 2/3 ∧ exponent (5/7) = 12/19 ∧
    exponent (21/29) = 3/5 ∧ exponent (27/37) = 3/5 ∧
    exponent (3/4) = 6/11 := by
  norm_num [exponent,Montgomery.NewDensity.exponent]


/-- The new complete curve never worsens the preceding complete curve. -/
theorem nonworsening {σ : ℝ} : exponent σ ≤ Montgomery.NewDensity.exponent σ := by
  by_cases hl : σ ≤ 12/17
  · simp only [exponent,ite_eq_left hl,le_refl]
  by_cases hr : σ < 27/37
  · exact (strict_improvement (lt_of_not_ge hl) hr).le
  by_cases he : σ = 27/37
  · subst σ
    norm_num [exponent,Montgomery.NewDensity.exponent]
  · have hh : 27/37 < σ := by
      rcases lt_or_eq_of_le (le_of_not_gt hr) with hh | hh
      · exact hh
      · exact False.elim (he hh.symm)
    simp only [exponent,ite_eq_right hl,
      ite_eq_right (show ¬σ ≤ 5/7 by linarith),
      ite_eq_right (show ¬σ ≤ 21/29 by linarith),
      ite_eq_right (show ¬σ ≤ 27/37 by linarith),le_refl]

/-- Comparison against the recorded Palomar interface, retaining its exact
piecewise exponent. The old improvement near 3/4 is also preserved. -/
theorem strict_improvement_over_Palomar {σ : ℝ}
    (hσ : 12/17 < σ) (hσ' : σ ≤ 3/4) :
    exponent σ < GuthMaynard.Improvement.combinedDensityExponent σ := by
  by_cases hs : σ ≤ 5/7
  · have he : Montgomery.NewDensity.exponent σ =
        GuthMaynard.Improvement.combinedDensityExponent σ := by
      simp only [Montgomery.NewDensity.exponent,GuthMaynard.Improvement.combinedDensityExponent,
        ite_eq_right (show ¬σ ≤ 9/13 by linarith),ite_eq_left hs,ite_eq_left hσ']
    exact (strict_improvement hσ (by linarith)).trans_eq he
  · exact nonworsening.trans_lt (Montgomery.NewDensity.strict_improvement (by linarith) hσ')

/-- Literal semantic expansion: no abstract zero-count object is substituted. -/
theorem literal_density (σ ε : ℝ) (hσ : 1/2 ≤ σ) (hσ' : σ ≤ 1)
    (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt riemannZeta ρ : ℕ):ℝ) ≤
        C*T^(exponent σ+ε) := by
  obtain ⟨C,hC,h⟩ := density hσ hσ' hε
  refine ⟨C,hC,?_⟩
  intro T hT F hF
  have he : F = zetaZeroFinset σ (-T) T := by
    ext ρ
    rw [hF,mem_zetaDensityFinset]
    simp only [IsNontrivialZetaZero,and_assoc]
  simpa only [he,zetaDensityCount,zetaSlabCount,zetaMultiplicity] using h T hT

end Montgomery.TwoTermDensity
