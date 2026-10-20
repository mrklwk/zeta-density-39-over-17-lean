module
public import GeneralCenteredTrace

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
namespace Montgomery.RationalMoment

/-- The mixed trace for the actual centered matrix has the required L^2
scale. No moment, reflection, Schur, or matrix-norm estimate is assumed. -/
theorem centered_mixed_trace_general (w : MathCollab.Density.ReflectionCutoff)
    {K : ℕ} (hK : 1 ≤ K) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ L : ℝ, 1 < T → 1 ≤ L → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      ‖Matrix.trace (cutoffContinuousMatrix w L W*cutoffCenteredMatrix w L W*
        cutoffCenteredMatrix w L W)‖ ≤ C*T^η*L*adjacentCenteredBudget K T L W.card := by
  obtain ⟨B,hB,hschur⟩ := cutoff_continuous_schur w
  obtain ⟨C,hC,hbound⟩ := centered_energy_general (reflectionSquare w) hK hη
  refine ⟨1+B*C,by positivity,?_⟩
  intro T t₀ L hT hL W hW hsep
  have hLp : 0 ≤ L := by linarith
  obtain ⟨hrow,hcol⟩ := hschur L hLp W hsep
  have hh := matrix_mixed_trace_schur (cutoffContinuousMatrix w L W) (cutoffCenteredMatrix w L W)
    (mul_nonneg hB hLp) hrow hcol
  have he : (∑ t : W, ∑ u : W, ‖cutoffCenteredMatrix w L W t u‖^2) =
      ∑ t ∈ W, ∑ u ∈ W, ‖MathCollab.Density.hKernel (reflectionSquare w) L (t-u)‖^2 := by
    simp only [cutoff_centered_entry]
    rw [Finset.sum_coe_sort W (fun t => ∑ u : W,
      ‖MathCollab.Density.hKernel (reflectionSquare w) L (t-(u:ℝ))‖^2)]
    apply sum_congr rfl
    intro t _
    exact Finset.sum_coe_sort W (fun u =>
      ‖MathCollab.Density.hKernel (reflectionSquare w) L (t-u)‖^2)
  rw [he] at hh
  calc
    _ ≤ (B*L)*(∑ t ∈ W, ∑ u ∈ W, ‖MathCollab.Density.hKernel (reflectionSquare w) L (t-u)‖^2) := hh
    _ ≤ (B*L)*(C*T^η*adjacentCenteredBudget K T L W.card) := by
      apply mul_le_mul_of_nonneg_left (hbound T t₀ L hT hL W hW hsep) (by positivity)
    _ = (B*C)*T^η*L*adjacentCenteredBudget K T L W.card := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (adjacentCenteredBudget_nonneg K (by linarith) hLp (Nat.cast_nonneg _))
      gcongr
      linarith

end Montgomery.RationalMoment
