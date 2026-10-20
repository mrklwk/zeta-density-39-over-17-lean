module
public import GuthMaynard.Improvement.SmoothingFourier

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped SchwartzMap FourierTransform ContDiff
namespace GuthMaynard.Improvement

def kernelBump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
def compactKernel : ℝ → ℝ := kernelBump.normed volume

theorem compactKernel_nonneg (x : ℝ) : 0 ≤ compactKernel x :=
  kernelBump.nonneg_normed (μ := volume) x

theorem compactKernel_integrable : Integrable compactKernel :=
  kernelBump.integrable_normed

theorem compactKernel_mass : ∫ x, compactKernel x = 1 :=
  kernelBump.integral_normed

theorem compactKernel_smooth : ContDiff ℝ ∞ compactKernel :=
  kernelBump.contDiff_normed

theorem compactKernel_compact : HasCompactSupport compactKernel :=
  kernelBump.hasCompactSupport_normed

theorem compactKernel_zero {x : ℝ} (hx : 2 ≤ |x|) : compactKernel x = 0 := by
  have hs := kernelBump.support_normed_eq (μ := volume)
  have hn : x ∉ Function.support compactKernel := by
    rw [show Function.support compactKernel = Metric.ball 0 2 from hs]
    simpa [Metric.mem_ball, Real.dist_eq, not_lt] using hx
  simpa [Function.support] using hn

theorem compactKernel_bound : ∃ B : ℝ, 0 < B ∧ ∀ x, ‖compactKernel x‖ ≤ B := by
  refine ⟨(∫ x, kernelBump x)⁻¹, inv_pos.mpr kernelBump.integral_pos, ?_⟩
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (compactKernel_nonneg x)]
  change kernelBump x / (∫ y, kernelBump y) ≤ _
  simpa [one_div] using div_le_div_of_nonneg_right kernelBump.le_one
    kernelBump.integral_pos.le

theorem compactKernel_schwartz : ∃ ψ : 𝓢(ℝ, ℂ),
    (ψ : ℝ → ℂ) = fun x => (compactKernel x : ℂ) := by
  have hc : HasCompactSupport (fun x => (compactKernel x : ℂ)) :=
    compactKernel_compact.comp_left (g := Complex.ofReal) (by simp)
  have hd : ContDiff ℝ ∞ (fun x => (compactKernel x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp compactKernel_smooth
  exact ⟨hc.toSchwartzMap hd, rfl⟩

/-- The fixed kernel and its Schwartz representative are constructed, so no
analytic kernel premise remains in this exact restricted-mass decay result. -/
theorem compact_masked_fourier_bound (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → ∀ A : Set ℝ,
      MeasurableSet A → ∀ r : ℝ → ℝ, Integrable (fun x => r x ^ 2) → ∀ ξ : ℝ,
      |ξ| ^ j * ‖𝓕 (fun x => (squareSmoothing (scaledKernel compactKernel δ)
        (A.indicator r) x : ℂ)) ξ‖ ≤ δ⁻¹ ^ j * C * (∫ x in A, r x ^ 2) := by
  obtain ⟨ψ, hψ⟩ := compactKernel_schwartz
  exact masked_scaled_fourier_bound compactKernel ψ hψ compactKernel_integrable j

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.compactKernel_nonneg
#print axioms GuthMaynard.Improvement.compactKernel_integrable
#print axioms GuthMaynard.Improvement.compactKernel_mass
#print axioms GuthMaynard.Improvement.compactKernel_smooth
#print axioms GuthMaynard.Improvement.compactKernel_compact
#print axioms GuthMaynard.Improvement.compactKernel_zero
#print axioms GuthMaynard.Improvement.compactKernel_bound
#print axioms GuthMaynard.Improvement.compactKernel_schwartz
#print axioms GuthMaynard.Improvement.compact_masked_fourier_bound
