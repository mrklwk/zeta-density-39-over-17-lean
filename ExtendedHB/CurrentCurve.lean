module
public import ExtendedHB.ActualDensity

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Montgomery.ExtendedHB
open MathCollab.Density

theorem current_exponent_right {σ : ℝ} (hlo : 15/17 ≤ σ) :
    Montgomery.CurrentDensity.exponent σ = 6*(1-σ)/(3*σ+1) := by
  have hnot : ¬(163/198≤σ ∧ σ≤7/8) := by intro h; linarith [h.2]
  simp only [Montgomery.CurrentDensity.exponent,ite_eq_right hnot,Montgomery.PeakTailDensity.exponent]
  rw [ite_eq_right (by linarith),ite_eq_right (by linarith),ite_eq_right (by linarith),
    ite_eq_right (by linarith),ite_eq_right (by linarith),ite_eq_right (by linarith)]

theorem hb_strict_improvement {σ : ℝ} (hlo : 15/17 < σ) (hhi : σ < 1) :
    3*(1-σ)/(10*σ-7) < Montgomery.CurrentDensity.exponent σ := by
  rw [current_exponent_right hlo.le]
  apply (div_lt_div_iff₀ (by linarith : 0 < 10*σ-7) (by linarith : 0 < 3*σ+1)).mpr
  have h := mul_pos (by linarith : 0 < 1-σ) (by linarith : 0 < 17*σ-15)
  nlinarith only [h]

theorem right_strict_improvement {σ : ℝ} (hlo : 17/19 ≤ σ) (hhi : σ < 1) :
    6*(1-σ)/(σ+3) < Montgomery.CurrentDensity.exponent σ := by
  rw [current_exponent_right (by linarith)]
  apply (div_lt_div_iff₀ (by linarith : 0 < σ+3) (by linarith : 0 < 3*σ+1)).mpr
  have h := sq_pos_of_pos (by linarith : 0 < 1-σ)
  nlinarith only [h]

theorem hb_retained_join :
    3*(1-(15/17:ℝ))/(10*(15/17)-7) = Montgomery.CurrentDensity.exponent (15/17) := by
  rw [current_exponent_right (by norm_num)]
  norm_num

theorem right_join :
    3*(1-(17/19:ℝ))/(10*(17/19)-7) = 6*(1-(17/19))/(17/19+3) := by norm_num

/-- Extend the exact completed curve only when the new exponent improves it. -/
def exponent (σ : ℝ) : ℝ :=
  if 15/17≤σ ∧ σ≤17/19 then 3*(1-σ)/(10*σ-7)
  else if 17/19≤σ ∧ σ≤1 then 6*(1-σ)/(σ+3)
  else Montgomery.CurrentDensity.exponent σ

theorem cumulative_density {σ ε : ℝ} (hlo : 1/2 ≤ σ) (hhi : σ ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(exponent σ+ε) := by
  unfold exponent
  split_ifs with h₁ h₂
  · exact density (by linarith [h₁.1]) h₁.2 hε
  · exact density_right_closed h₂.1 h₂.2 hε
  · exact Montgomery.CurrentDensity.density hlo hhi hε

theorem exponent_le_current {σ : ℝ} (hhi : σ ≤ 1) :
    exponent σ ≤ Montgomery.CurrentDensity.exponent σ := by
  unfold exponent
  split_ifs with h₁ h₂
  · by_cases hj : σ=15/17
    · subst σ
      exact hb_retained_join.le
    · exact (hb_strict_improvement (lt_of_le_of_ne h₁.1 (Ne.symm hj)) (by linarith [h₁.2])).le
  · by_cases hj : σ=1
    · subst σ
      rw [current_exponent_right (by norm_num)]
      norm_num
    · exact (right_strict_improvement h₂.1 (lt_of_le_of_ne hhi hj)).le
  · exact le_refl _

theorem exponent_lt_current {σ : ℝ} (hlo : 15/17 < σ) (hhi : σ < 1) :
    exponent σ < Montgomery.CurrentDensity.exponent σ := by
  unfold exponent
  split_ifs with h₁ h₂
  · exact hb_strict_improvement hlo hhi
  · exact right_strict_improvement h₂.1 hhi
  · exact False.elim (h₂ ⟨by have := not_and.mp h₁ hlo.le; linarith,hhi.le⟩)

theorem literal_cumulative_density (σ ε : ℝ) (hlo : 1/2 ≤ σ) (hhi : σ ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ∈F ↔ riemannZeta ρ=0 ∧ 0<ρ.re ∧ ρ.re<1 ∧ σ≤ρ.re ∧ |ρ.im|≤T) →
      ((∑ ρ∈F, analyticOrderNatAt riemannZeta ρ : ℕ):ℝ) ≤ C*T^(exponent σ+ε) := by
  obtain ⟨C,hC,h⟩ := cumulative_density hlo hhi hε
  refine ⟨C,hC,?_⟩
  intro T hT F hF
  have he : F=zetaZeroFinset σ (-T) T := by
    ext ρ
    rw [hF,mem_zetaDensityFinset]
    simp only [IsNontrivialZetaZero,and_assoc]
  simpa only [he,zetaDensityCount,zetaSlabCount,zetaMultiplicity] using h T hT

theorem endpoints : exponent (15/17)=6/31 ∧ exponent (17/19)=6/37 ∧
    exponent (9/10)=2/13 ∧ exponent 1=0 := by norm_num [exponent]

/-- The continuation does not assert the stronger published HB exponent. -/
theorem right_above_full_hb {σ : ℝ} (hlo : 17/19 < σ) (hhi : σ < 1) :
    3*(1-σ)/(10*σ-7) < 6*(1-σ)/(σ+3) := by
  apply (div_lt_div_iff₀ (by linarith : 0 < 10*σ-7) (by linarith : 0 < σ+3)).mpr
  have h := mul_pos (by linarith : 0 < 1-σ) (by linarith : 0 < 19*σ-17)
  nlinarith only [h]

end Montgomery.ExtendedHB
