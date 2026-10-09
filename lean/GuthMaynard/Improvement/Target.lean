import Mathlib

/-! Literal middle-range target. The proof is in `MiddleLargeValues`. -/
set_option autoImplicit false

namespace GuthMaynard.Improvement

noncomputable def boundedPolynomial (N : ℝ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
    a n * Complex.exp (((t * Real.log ((n : ℝ) / N) : ℝ) : ℂ) * Complex.I)

/-- One constant precedes all scales, coefficient families, heights, interval
translates and finite separated point sets. The historical name is retained;
`middle_range_large_values` proves this proposition in `MiddleLargeValues`. -/
def CandidateMiddleRangeEstimate : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (N T V t₀ : ℝ) (a : ℕ → ℂ) (W : Finset ℝ),
      2 ≤ N →
      N ^ (6 / 5 : ℝ) ≤ T → T ≤ N ^ (5 / 3 : ℝ) →
      0 < V →
      (∀ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, ‖a n‖ ≤ 1) →
      (∀ t ∈ W, t₀ ≤ t ∧ t ≤ t₀ + T) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t - u|) →
      (∀ t ∈ W, V ≤ ‖boundedPolynomial N a t‖) →
      (W.card : ℝ) ≤ C * N ^ ε *
        (N ^ 2 / V ^ 2 + N ^ (18 / 7 : ℝ) * T ^ (6 / 7 : ℝ) / V ^ 4)

end GuthMaynard.Improvement

#print GuthMaynard.Improvement.CandidateMiddleRangeEstimate
