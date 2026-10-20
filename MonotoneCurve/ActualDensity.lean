module
public import ExtendedHB.CurrentCurve

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Montgomery.MonotoneCurve
open MathCollab.Density

/-- The closed last endpoint remains a uniform bound at every larger real part.
This uses monotonicity of the actual analytic-multiplicity zero count. -/
theorem seven_eighths_right_uniform {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 7/8 ≤ σ → ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T : ℝ) ≤ C * T ^ ((1086/5537 : ℝ) + ε) := by
  obtain ⟨C, hC, h⟩ :=
    Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row8
      (σ := (7/8 : ℝ)) (by norm_num) le_rfl hε
  refine ⟨C, hC, ?_⟩
  intro σ hσ T hT
  have hm : (zetaDensityCount σ T : ℝ) ≤ (zetaDensityCount (7/8) T : ℝ) := by
    exact_mod_cast zetaDensityCount_mono hσ (le_refl T)
  apply hm.trans
  convert h T hT using 1
  norm_num

/-- Pointwise minimum with the proved endpoint continuation. -/
def exponent (σ : ℝ) : ℝ :=
  if 7/8 ≤ σ then min (1086/5537) (Montgomery.ExtendedHB.exponent σ)
  else Montgomery.ExtendedHB.exponent σ

theorem density {σ ε : ℝ} (hlo : 1/2 ≤ σ) (hhi : σ ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T : ℝ) ≤ C * T ^ (exponent σ + ε) := by
  unfold exponent
  split_ifs with hσ
  · by_cases hc : (1086/5537 : ℝ) ≤ Montgomery.ExtendedHB.exponent σ
    · rw [min_eq_left hc]
      obtain ⟨C, hC, h⟩ := seven_eighths_right_uniform hε
      exact ⟨C, hC, h σ hσ⟩
    · rw [min_eq_right (le_of_not_ge hc)]
      exact Montgomery.ExtendedHB.cumulative_density hlo hhi hε
  · exact Montgomery.ExtendedHB.cumulative_density hlo hhi hε

theorem exponent_le_extended (σ : ℝ) :
    exponent σ ≤ Montgomery.ExtendedHB.exponent σ := by
  unfold exponent
  split_ifs
  · exact min_le_right _ _
  · exact le_rfl

private theorem extended_right_background {σ : ℝ}
    (hlo : (7/8 : ℝ) < σ) (hhi : σ < 15/17) :
    Montgomery.ExtendedHB.exponent σ = 6*(1-σ)/(3*σ+1) := by
  have h₁ : ¬(15/17 ≤ σ ∧ σ ≤ 17/19) := by intro h; linarith [h.1]
  have h₂ : ¬(17/19 ≤ σ ∧ σ ≤ 1) := by intro h; linarith [h.1]
  have h₃ : ¬(163/198 ≤ σ ∧ σ ≤ 7/8) := by intro h; linarith [h.2]
  simp only [Montgomery.ExtendedHB.exponent, ite_eq_right h₁, ite_eq_right h₂,
    Montgomery.CurrentDensity.exponent, ite_eq_right h₃, Montgomery.PeakTailDensity.exponent]
  rw [ite_eq_right (by linarith), ite_eq_right (by linarith),
    ite_eq_right (by linarith), ite_eq_right (by linarith),
    ite_eq_right (by linarith), ite_eq_right (by linarith)]

theorem plateau {σ : ℝ} (hlo : 7/8 ≤ σ) (hhi : σ ≤ 1339/1520) :
    exponent σ = (1086/5537 : ℝ) := by
  unfold exponent
  rw [ite_eq_left hlo]
  apply min_eq_left
  by_cases he : σ = 7/8
  · subst σ
    norm_num [Montgomery.ExtendedHB.exponent, Montgomery.CurrentDensity.exponent,
      Montgomery.RationalMoment.RightDetector.Physical.fullDashedExponent,
      Montgomery.RationalMoment.RightDetector.Physical.sharpLaterExponent]
  · rw [extended_right_background (lt_of_le_of_ne hlo (Ne.symm he)) (by linarith)]
    apply (le_div_iff₀ (by linarith : 0 < 3*σ+1)).mpr
    linarith

theorem strict_plateau_gain {σ : ℝ} (hlo : 7/8 < σ) (hhi : σ < 1339/1520) :
    exponent σ < Montgomery.ExtendedHB.exponent σ := by
  rw [plateau hlo.le hhi.le, extended_right_background hlo (by linarith)]
  apply (lt_div_iff₀ (by linarith : 0 < 3*σ+1)).mpr
  linarith

theorem plateau_join :
    6*(1-(1339/1520 : ℝ))/(3*(1339/1520)+1) = 1086/5537 := by norm_num

theorem literal_density (σ ε : ℝ) (hlo : 1/2 ≤ σ) (hhi : σ ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, _root_.analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (exponent σ + ε) := by
  obtain ⟨C, hC, h⟩ := density hlo hhi hε
  refine ⟨C, hC, ?_⟩
  intro T hT F hF
  have he : F = zetaZeroFinset σ (-T) T := by
    ext ρ
    rw [hF, mem_zetaDensityFinset]
    simp only [IsNontrivialZetaZero, and_assoc]
  simpa only [he, zetaDensityCount, zetaSlabCount, zetaMultiplicity] using h T hT

end Montgomery.MonotoneCurve
