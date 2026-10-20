module
public import GuthMaynard.Improvement.LogModulated

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff FourierTransform
namespace GuthMaynard.Improvement

/-- Actual integration by parts with explicit polynomial time growth. -/
theorem logModulated_fourier_power {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hs : ∀ x, x ∉ Icc l u → a x = 0) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ξ : ℝ,
      |ξ|^n*‖𝓕 (logModulated a s) ξ‖ ≤ C*(1+|s|)^n := by
  obtain ⟨C,hC,hb⟩ := logModulated_global_deriv ha hl hs n
  refine ⟨(u-l)*C+1,by positivity,?_⟩
  intro s ξ
  have hz : ∀ x, x ∉ Icc l u → logModulated a s x = 0 := by
    intro x hx; simp [logModulated,hs x hx]
  calc
    _ ≤ (u-l)*(C*(1+|s|)^n) := compact_fourier_power_bound
      (logModulated_smooth ha hl hs s) hlu hz n (by positivity) (hb s) ξ
    _ ≤ ((u-l)*C+1)*(1+|s|)^n := by nlinarith [pow_nonneg (by positivity : 0 ≤ 1+|s|) n]

/-- One-plus-frequency bound for the actual modulated cutoff. The fixed
constant precedes time and frequency; its time cost is explicit. -/
theorem logModulated_fourier_decay {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hs : ∀ x, x ∉ Icc l u → a x = 0) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ξ : ℝ,
      (1+|ξ|)^n*‖𝓕 (logModulated a s) ξ‖ ≤ C*(1+|s|)^n := by
  obtain ⟨D₀,hD₀,h₀⟩ := logModulated_fourier_power ha hl hlu hs 0
  obtain ⟨Dₙ,hDₙ,hₙ⟩ := logModulated_fourier_power ha hl hlu hs n
  refine ⟨2^n*(D₀+Dₙ),by positivity,?_⟩
  intro s ξ
  have hz : ‖𝓕 (logModulated a s) ξ‖ ≤ D₀ := by simpa using h₀ s ξ
  have hn := hₙ s ξ
  have hs1 : 1 ≤ (1+|s|)^n := one_le_pow₀ (by linarith [abs_nonneg s])
  by_cases hx : |ξ| ≤ 1
  · calc
      _ ≤ 2^n*D₀ := mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) n) hz (norm_nonneg _) (by positivity)
      _ ≤ (2^n*D₀)*(1+|s|)^n := by nlinarith [mul_nonneg (show 0 ≤ (2:ℝ)^n*D₀ by positivity) (sub_nonneg.mpr hs1)]
      _ ≤ _ := by gcongr; linarith
  · have hx' : 1 ≤ |ξ| := (lt_of_not_ge hx).le
    calc
      _ ≤ (2*|ξ|)^n*‖𝓕 (logModulated a s) ξ‖ := by gcongr; linarith
      _ = 2^n*(|ξ|^n*‖𝓕 (logModulated a s) ξ‖) := by rw [mul_pow]; ring
      _ ≤ 2^n*(Dₙ*(1+|s|)^n) := mul_le_mul_of_nonneg_left hn (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ (2:ℝ)^n*D₀ by positivity) (pow_nonneg (by positivity : 0 ≤ 1+|s|) n)]

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.logModulated_fourier_power
#print axioms GuthMaynard.Improvement.logModulated_fourier_decay
