import GuthMaynard.Improvement.CombinedDensityCurve
open GuthMaynard.Improvement
set_option autoImplicit false
noncomputable section

theorem envelope_bound (σ : ℝ) (hlo : 1/2 ≤ σ) (hhi : σ < 1) :
    combinedDensityExponent σ ≤ (39/17)*(1-σ) := by
  have hp : 0 < 1-σ := by linarith
  unfold combinedDensityExponent
  split_ifs with h1 h2 h3
  · apply (div_le_iff₀ (show 0 < 2-σ by linarith)).mpr
    nlinarith [mul_nonneg hp.le (show 0 ≤ 9/13-σ by linarith)]
  · apply (div_le_iff₀ (show 0 < 7*σ+3 by linarith)).mpr
    nlinarith [mul_nonneg hp.le (show 0 ≤ σ-9/13 by linarith)]
  · nlinarith
  · apply (div_le_iff₀ (show 0 < 2*σ by linarith)).mpr
    nlinarith [mul_nonneg hp.le (show 0 ≤ σ-3/4 by linarith)]

theorem coefficient_maximum :
    (∀ σ : ℝ, 1/2 ≤ σ → σ < 1 →
      combinedDensityExponent σ/(1-σ) ≤ 39/17) ∧
    combinedDensityExponent (9/13)/(1-9/13) = 39/17 := by
  constructor
  · intro σ hlo hhi
    exact (div_le_iff₀ (show 0 < 1-σ by linarith)).mpr (envelope_bound σ hlo hhi)
  · norm_num [combinedDensityExponent]

example : combinedDensityExponent (9/13) > (9/4)*(1-9/13) := by
  norm_num [combinedDensityExponent]
#print axioms coefficient_maximum


def abstractCoefficient (σ : ℝ) : ℝ :=
  if σ ≤ 9/13 then 3/(2-σ)
  else if σ ≤ 5/7 then 18/(7*σ+3)
  else if σ ≤ 3/4 then 9/4
  else 3/(2*σ)

theorem coefficient_times_gap (σ : ℝ) :
    abstractCoefficient σ * (1-σ) = combinedDensityExponent σ := by
  unfold abstractCoefficient combinedDensityExponent
  split_ifs <;> ring

theorem abstract_coefficient_maximum :
    (∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 1 → abstractCoefficient σ ≤ 39/17) ∧
    abstractCoefficient (9/13) = 39/17 := by
  constructor
  · intro σ hlo hhi
    by_cases h : σ < 1
    · have hb := envelope_bound σ hlo h
      rw [← coefficient_times_gap σ] at hb
      exact (mul_le_mul_iff_left₀ (show 0 < 1-σ by linarith)).mp hb
    · have he : σ = 1 := by linarith
      subst σ
      norm_num [abstractCoefficient]
  · norm_num [abstractCoefficient]

example : abstractCoefficient 1 = 3/2 ∧
    abstractCoefficient 1 * (1-1) = combinedDensityExponent 1 := by
  constructor
  · norm_num [abstractCoefficient]
  · exact coefficient_times_gap 1
#print axioms coefficient_times_gap
#print axioms abstract_coefficient_maximum
