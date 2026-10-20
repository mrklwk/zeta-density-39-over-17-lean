module
public import NativeBHBPeakTails
public import PairActualDensity
public import RightSolidTailBudgets

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger MathCollab.Density TaoTrudgianYang2025

theorem rightSolid_native_pair (σ : ℝ) :
    ExponentPair (rightSolidTailK σ) (rightSolidTailL σ) := by
  unfold rightSolidTailK rightSolidTailL
  split_ifs
  · exact exponentPair_BHB10
  · exact exponentPair_BHB9
  · exact exponentPair_BHB8
  · exact exponentPair_BHB7

theorem rightSolid_pair_parameters (σ : ℝ) :
    0 < rightSolidTailK σ ∧ 2+4*rightSolidTailL σ/rightSolidTailK σ ≤ 7 := by
  unfold rightSolidTailK rightSolidTailL
  split_ifs <;> norm_num

/-- All five solid right-hand bounds for actual zeta zeros with multiplicity.
The native BHB pairs, physical peak tails and both detector branches are supplied. -/
theorem density_right_solid {σ ε : ℝ}
    (hl : 7/9 ≤ σ) (hr : σ ≤ 4/5) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : ℝ,2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(3*rightSolidLengthExponent σ*(1-σ)+ε) := by
  have hw := right_solid_quadratic_window hl hr
  have hparams := rightSolid_pair_parameters σ
  have hbudgets := rightSolid_tail_budgets hl hr
  have hθ := rightSolid_detector_exponent_lower hl hr
  exact density_of_pair_tail_window (rightSolid_native_pair σ) hparams.1 hparams.2
    hw hl (by norm_num at hθ ⊢; linarith) hbudgets.1 hbudgets.2 hε

theorem density_right_solid_first {σ ε : ℝ}
    (hl : 7/9 ≤ σ) (hr : σ ≤ 29359/37574) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : ℝ,2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(3*(1-σ)/(11*σ-7)+ε) := by
  have hh := density_right_solid hl (hr.trans (by norm_num : (29359:ℝ)/37574 ≤ 4/5)) hε
  simpa only [rightSolidLengthExponent,ite_eq_left hr,
    show 3*(1/(11*σ-7))*(1-σ)=3*(1-σ)/(11*σ-7) by ring] using hh

theorem density_right_solid_second {σ ε : ℝ}
    (hl : 29359/37574 ≤ σ) (hr : σ ≤ 1015/1294) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : ℝ,2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(4744*(1-σ)/(4870*σ-1283)+ε) := by
  have hh := density_right_solid (by linarith : (7:ℝ)/9 ≤ σ)
    (hr.trans (by norm_num : (1015:ℝ)/1294 ≤ 4/5)) hε
  have he : 3*rightSolidLengthExponent σ*(1-σ)=4744*(1-σ)/(4870*σ-1283) := by
    unfold rightSolidLengthExponent
    simp only [ite_eq_left hr]
    split_ifs with h₁
    · have hσ : σ=29359/37574 := le_antisymm h₁ hl
      rw [hσ]
      norm_num
    · rw [show 14610*σ-3849=3*(4870*σ-1283) by ring]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
  simpa only [he] using hh

theorem density_right_solid_third {σ ε : ℝ}
    (hl : 1015/1294 ≤ σ) (hr : σ ≤ 353/447) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : ℝ,2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(6154*(1-σ)/(6354*σ-1693)+ε) := by
  have hh := density_right_solid (by linarith : (7:ℝ)/9 ≤ σ)
    (hr.trans (by norm_num : (353:ℝ)/447 ≤ 4/5)) hε
  have h₁ : ¬σ ≤ (29359:ℝ)/37574 := by linarith
  have he : 3*rightSolidLengthExponent σ*(1-σ)=6154*(1-σ)/(6354*σ-1693) := by
    unfold rightSolidLengthExponent
    rw [ite_eq_right h₁]
    simp only [ite_eq_left hr]
    split_ifs with h₂
    · have hσ : σ=1015/1294 := le_antisymm h₂ hl
      rw [hσ]
      norm_num
    · rw [show 19062*σ-5079=3*(6354*σ-1693) by ring]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
  simpa only [he] using hh

theorem density_right_solid_fourth {σ ε : ℝ}
    (hl : 353/447 ≤ σ) (hr : σ ≤ 467/586) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : ℝ,2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(3782*(1-σ)/(3936*σ-1065)+ε) := by
  have hh := density_right_solid (by linarith : (7:ℝ)/9 ≤ σ)
    (hr.trans (by norm_num : (467:ℝ)/586 ≤ 4/5)) hε
  have h₁ : ¬σ ≤ (29359:ℝ)/37574 := by linarith
  have h₂ : ¬σ ≤ (1015:ℝ)/1294 := by linarith
  have he : 3*rightSolidLengthExponent σ*(1-σ)=3782*(1-σ)/(3936*σ-1065) := by
    unfold rightSolidLengthExponent
    rw [ite_eq_right h₁,ite_eq_right h₂]
    simp only [ite_eq_left hr]
    split_ifs with h₃
    · have hσ : σ=353/447 := le_antisymm h₃ hl
      rw [hσ]
      norm_num
    · rw [show 11808*σ-3195=3*(3936*σ-1065) by ring]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
  simpa only [he] using hh

theorem density_right_solid_fifth {σ ε : ℝ}
    (hl : 467/586 ≤ σ) (hr : σ ≤ 4/5) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : ℝ,2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(2168*(1-σ)/(2282*σ-631)+ε) := by
  have hh := density_right_solid (by linarith : (7:ℝ)/9 ≤ σ) hr hε
  have h₁ : ¬σ ≤ (29359:ℝ)/37574 := by linarith
  have h₂ : ¬σ ≤ (1015:ℝ)/1294 := by linarith
  have h₃ : ¬σ ≤ (353:ℝ)/447 := by linarith
  have he : 3*rightSolidLengthExponent σ*(1-σ)=2168*(1-σ)/(2282*σ-631) := by
    unfold rightSolidLengthExponent
    rw [ite_eq_right h₁,ite_eq_right h₂,ite_eq_right h₃]
    split_ifs with h₄
    · have hσ : σ=467/586 := le_antisymm h₄ hl
      rw [hσ]
      norm_num
    · rw [show 6846*σ-1893=3*(2282*σ-631) by ring]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
  simpa only [he] using hh
end Montgomery.RationalMoment.RightDetector
