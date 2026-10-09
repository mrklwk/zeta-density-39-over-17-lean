import GuthMaynard.Improvement.ShortDensityConditional
import GuthMaynard.Improvement.ShortDensityUniform

open MathCollab.Density
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- Explicit classical input on the actual multiplicity count. Constants may
 depend on sigma and epsilon; this definition asserts no proof of Ingham. -/
def InghamLowerDensity : Prop :=
  ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 9/13 → ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(3*(1-σ)/(2-σ)+ε)

/-- Explicit published Guth–Maynard input, restricted to the needed range.
 The endpoint sigma=1 is handled by the actual count, not this premise. -/
def GuthMaynardUpperDensity : Prop :=
  ∀ σ : ℝ, 5/7 ≤ σ → σ < 1 → ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(15*(1-σ)/(3+5*σ)+ε)

/-- The actual nontrivial-zero count vanishes on and beyond Re=1. -/
theorem zetaDensityCount_zero_of_one_le {σ : ℝ} (hσ : 1 ≤ σ) (T : ℝ) :
    zetaDensityCount σ T = 0 := by
  unfold zetaDensityCount zetaSlabCount
  apply Finset.sum_eq_zero
  intro ρ hρ
  have h := mem_zetaZeroFinset.mp hρ
  exact False.elim (not_le_of_gt h.1.2.2 (hσ.trans h.2.1))

/-- Exact coefficient comparisons covering the entire critical half-strip. -/
theorem global_density_coefficient_comparisons {σ : ℝ} :
    (1/2 ≤ σ → σ ≤ 9/13 → 3*(1-σ)/(2-σ) ≤ (39/17)*(1-σ)) ∧
    (9/13 ≤ σ → σ ≤ 5/7 → 18*(1-σ)/(7*σ+3) ≤ (39/17)*(1-σ)) ∧
    (5/7 ≤ σ → σ ≤ 1 → 15*(1-σ)/(3+5*σ) ≤ (39/17)*(1-σ)) := by
  constructor
  · intro hlo hhi
    apply (div_le_iff₀ (by linarith : 0 < 2-σ)).mpr
    nlinarith [mul_nonneg (show 0 ≤ 1-σ by linarith) (show 0 ≤ 9/13-σ by linarith)]
  constructor
  · intro hlo hhi
    apply (div_le_iff₀ (by linarith : 0 < 7*σ+3)).mpr
    nlinarith [mul_nonneg (show 0 ≤ 1-σ by linarith) (show 0 ≤ σ-9/13 by linarith)]
  · intro hlo hhi
    apply (div_le_iff₀ (by linarith : 0 < 3+5*σ)).mpr
    nlinarith [mul_nonneg (show 0 ≤ 1-σ by linarith) (show 0 ≤ σ-5/7 by linarith)]

/-- Global fixed-sigma coefficient39/17, conditional on exactly the actual
short Mobius fourth moment and the two displayed classical density inputs.
The existential constant may depend on sigma and epsilon. -/
theorem global_density_fixed_sigma_of_inputs
    (hmoment : ShortMobiusFourthMoment) (hingham : InghamLowerDensity)
    (hgm : GuthMaynardUpperDensity) {σ ε : ℝ}
    (hσ : 1/2 ≤ σ) (hσ' : σ ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^((39/17)*(1-σ)+ε) := by
  by_cases hlow : σ ≤ 9/13
  · obtain ⟨C,hC,hbound⟩ := hingham σ hσ hlow ε hε
    refine ⟨C,hC,?_⟩
    intro T hT
    exact (hbound T hT).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T)
        (by linarith [(global_density_coefficient_comparisons (σ:=σ)).1 hσ hlow])) hC.le)
  by_cases hmid : σ ≤ 5/7
  · obtain ⟨C,hC,hbound⟩ := short_density_of_fourth_moment hmoment (le_of_not_ge hlow) hmid hε
    refine ⟨C,hC,?_⟩
    intro T hT
    exact (hbound T hT).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T)
        (by linarith [(global_density_coefficient_comparisons (σ:=σ)).2.1 (le_of_not_ge hlow) hmid])) hC.le)
  by_cases hone : σ < 1
  · obtain ⟨C,hC,hbound⟩ := hgm σ (le_of_not_ge hmid) hone ε hε
    refine ⟨C,hC,?_⟩
    intro T hT
    exact (hbound T hT).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T)
        (by linarith [(global_density_coefficient_comparisons (σ:=σ)).2.2 (le_of_not_ge hmid) hσ'])) hC.le)
  · refine ⟨1,by norm_num,?_⟩
    intro T _hT
    rw [zetaDensityCount_zero_of_one_le (le_of_not_gt hone)]
    simp only [Nat.cast_zero, one_mul]
    exact Real.rpow_nonneg (by linarith) _

/-- The global coefficient39/17 with the constant uniform in sigma. All three
 analytic inputs remain explicit; finite-grid monotonicity spends epsilon. -/
theorem global_density_uniform_of_inputs
    (hmoment : ShortMobiusFourthMoment) (hingham : InghamLowerDensity)
    (hgm : GuthMaynardUpperDensity) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1/2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^((39/17)*(1-σ)+ε) := by
  apply zetaDensityCount_uniform_of_fixed_sigma (show (0:ℝ)<39/17 by norm_num) _ hε
  intro σ hσ hσ' ε hε
  exact global_density_fixed_sigma_of_inputs hmoment hingham hgm hσ hσ' hε

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.zetaDensityCount_zero_of_one_le
#print axioms GuthMaynard.Improvement.global_density_coefficient_comparisons
#print axioms GuthMaynard.Improvement.global_density_fixed_sigma_of_inputs
#print GuthMaynard.Improvement.InghamLowerDensity
#print GuthMaynard.Improvement.GuthMaynardUpperDensity

#print axioms GuthMaynard.Improvement.global_density_uniform_of_inputs
