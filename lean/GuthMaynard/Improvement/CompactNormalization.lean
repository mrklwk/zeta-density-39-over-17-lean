import GuthMaynard.Improvement.CompactKernel
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace GuthMaynard.Improvement

/-- Support propagation is pointwise, and imposes no smoothness on the input. -/
theorem smooth_support_interval {κ g : ℝ → ℝ} {a b h x : ℝ}
    (hκ : ∀ t, h < |t| → κ t = 0)
    (hg : ∀ y, y ∉ Set.Icc a b → g y = 0)
    (hx : x ∉ Set.Icc (a-h) (b+h)) : smooth κ g x = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  by_cases hy : y ∈ Set.Icc a b
  · have ht : h < |x-y| := by
      by_contra hn
      have hh := abs_le.mp (le_of_not_gt hn)
      exact hx ⟨by linarith [hy.1], by linarith [hy.2]⟩
    simp [hκ (x-y) ht]
  · simp [hg y hy]

theorem scaled_compactKernel_zero {δ x : ℝ} (hδ : 0 < δ)
    (hx : 2*δ < |x|) : scaledKernel compactKernel δ x = 0 := by
  have ht : 2 ≤ |x/δ| := by
    rw [abs_div, abs_of_pos hδ]
    exact (le_div_iff₀ hδ).mpr hx.le
  simp [scaledKernel, compactKernel_zero ht]

/-- Mass is bounded by the actual output on its support, with no inverse
input mass. U may be any pointwise upper bound for the smoothed function. -/
theorem compact_smoothing_mass_le {g : ℝ → ℝ} {a b δ U : ℝ}
    (hg : Integrable g) (hg0 : ∀ x, 0 ≤ g x)
    (hδ : 0 < δ) (hab : a ≤ b)
    (hs : ∀ y, y ∉ Set.Icc a b → g y = 0)
    (hU : ∀ x, smooth (scaledKernel compactKernel δ) g x ≤ U) :
    (∫ x, g x) ≤ (b-a+4*δ)*U := by
  let F := smooth (scaledKernel compactKernel δ) g
  have hF0 : ∀ x, 0 ≤ F x := smooth_nonneg
    (scaledKernel_nonneg compactKernel_nonneg hδ) hg0
  have hz : ∀ x, x ∉ Set.Icc (a-2*δ) (b+2*δ) → F x = 0 := by
    intro x hx
    exact smooth_support_interval (fun t ht => scaled_compactKernel_zero hδ ht) hs hx
  have hi : (∫ x in Set.Icc (a-2*δ) (b+2*δ), F x) = ∫ x, g x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    exact smooth_mass (scaledKernel_integrable compactKernel_integrable hδ) hg
      (scaledKernel_mass hδ compactKernel_mass)
  have hn := norm_setIntegral_le_of_norm_le_const
    (μ := volume) (f := F) (s := Set.Icc (a-2*δ) (b+2*δ))
    isCompact_Icc.measure_lt_top (fun x _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hF0 x)]
      exact hU x)
  rw [hi, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg hg0),
    Real.volume_real_Icc_of_le (by linarith)] at hn
  nlinarith

/-- Normalized Fourier decay, uniform over delta<=1 and every input on a
fixed interval. U is any actual bound for the smoothed output. -/
theorem compact_smoothing_normalized_fourier {a b : ℝ} (hab : a ≤ b) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ g : ℝ → ℝ,
      Integrable g → (∀ x, 0 ≤ g x) →
      (∀ y, y ∉ Set.Icc a b → g y = 0) → ∀ U : ℝ,
      (∀ x, smooth (scaledKernel compactKernel δ) g x ≤ U) → ∀ ξ : ℝ,
      |ξ|^j * ‖𝓕 (fun x => (smooth (scaledKernel compactKernel δ) g x : ℂ)) ξ‖ ≤
        δ⁻¹^j * C * U := by
  obtain ⟨ψ, hψ⟩ := compactKernel_schwartz
  obtain ⟨C, hC, h⟩ := scaled_smooth_power_bound compactKernel ψ hψ compactKernel_integrable j
  refine ⟨C*(b-a+4), mul_pos hC (by linarith), ?_⟩
  intro δ hδ hδ1 g hg hg0 hs U hU ξ
  have hU0 : 0 ≤ U := (smooth_nonneg
    (scaledKernel_nonneg compactKernel_nonneg hδ) hg0 0).trans (hU 0)
  have hm := compact_smoothing_mass_le hg hg0 hδ hab hs hU
  have hm' : (∫ x, g x) ≤ (b-a+4)*U := hm.trans (by nlinarith)
  have hp : 0 ≤ δ⁻¹^j*C := by positivity
  calc
    _ ≤ δ⁻¹^j*C*(∫ x, g x) := h δ hδ g hg hg0 ξ
    _ ≤ δ⁻¹^j*C*((b-a+4)*U) := mul_le_mul_of_nonneg_left hm' hp
    _ = _ := by ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.smooth_support_interval
#print axioms GuthMaynard.Improvement.scaled_compactKernel_zero
#print axioms GuthMaynard.Improvement.compact_smoothing_mass_le

#print axioms GuthMaynard.Improvement.compact_smoothing_normalized_fourier
