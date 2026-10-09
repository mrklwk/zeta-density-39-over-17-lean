module
public import GuthMaynard.Improvement.FixedCutoffs
public import GuthMaynard.Improvement.SourceDirichletPairing
public import GuthMaynard.Improvement.SourceCutoffConvolution
public import GuthMaynard.Improvement.ReflectedBandMeanValue
public import MathCollab.Density.Packing

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped FourierTransform SchwartzMap ContDiff
namespace GuthMaynard.Improvement

/-- The existing fixed bump, now used on the frequency line. -/
def sourceReproducingBump : 𝓢(ℝ,ℂ) :=
  (fixedTimeCutoff_compact.comp_left
    (show (Complex.ofRealCLM : ℝ → ℂ) 0 = 0 by rfl)).toSchwartzMap
      (show ContDiff ℝ ∞ (Complex.ofRealCLM ∘ fixedTimeCutoff) by
        exact Complex.ofRealCLM.contDiff.comp fixedTimeCutoff_smooth)

/-- One fixed actual Schwartz reproducing kernel, independent of every source. -/
def sourceReproducingKernel : 𝓢(ℝ,ℂ) := 𝓕⁻ sourceReproducingBump

theorem sourceReproducingKernel_fourier (ξ : ℝ) :
    𝓕 (sourceReproducingKernel : ℝ → ℂ) ξ = (fixedTimeCutoff ξ:ℂ) := by
  change (𝓕 (𝓕⁻ sourceReproducingBump) : 𝓢(ℝ,ℂ)) ξ = _
  rw [FourierTransform.fourier_fourierInv_eq]
  rfl

/-- A finite source frequency lies inside the fixed reproducing plateau. -/
theorem source_reproducing_frequency {N : ℝ} (hN : 0 < N) {n : ℕ}
    (hn : n ∈ sourceRatioIndices N) :
    -mellinFrequency ((n:ℝ)/N) ∈ Icc (-1:ℝ) 2 := by
  obtain ⟨hn1,hn2⟩ := (sourceRatioIndices_mem hN.le n).mp hn
  have hx0 : 0 < (n:ℝ)/N := div_pos (hN.trans hn1) hN
  have hx1 : 1 ≤ (n:ℝ)/N := (le_div_iff₀ hN).mpr (by linarith)
  have hx2 : (n:ℝ)/N ≤ 2 := (div_le_iff₀ hN).mpr (by linarith)
  have hl0 := Real.log_nonneg hx1
  have hl1 : Real.log ((n:ℝ)/N) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos hx0
    linarith
  have hd : 0 < 2*Real.pi := by positivity
  have hf0 : 0 ≤ mellinFrequency ((n:ℝ)/N) := div_nonneg hl0 hd.le
  have hf1 : mellinFrequency ((n:ℝ)/N) ≤ 1 :=
    (div_le_one hd).mpr (by nlinarith [Real.pi_gt_three])
  constructor <;> linarith

/-- A translated kernel reproduces one exponential by ordinary Fourier
integration; this never applies inversion to the nonintegrable exponential. -/
theorem source_kernel_phase_integral (κ : ℝ → ℂ) (ξ w : ℝ) :
    (∫ t, κ (t-w)*phase (t*ξ)) = phase (w*ξ)*𝓕 κ (-ξ) := by
  have he := integral_add_right_eq_self (μ := volume) (fun t => κ (t-w)*phase (t*ξ)) w
  rw [← he]
  simp only [add_sub_cancel_right]
  simp_rw [add_mul,phase_add]
  calc
    _ = phase (w*ξ)*(∫ t, phase (t*ξ)*κ t) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      ring
    _ = _ := by
      rw [fourier_eq_phase_integral]
      simp only [neg_neg,mul_comm ξ]

/-- The actual convolution integrand is L1 even though the source itself
need not be L1 on the full time line. -/
theorem source_reproducing_integrable (N : ℝ) (a : ℕ → ℂ) (w : ℝ) :
    Integrable (fun t => sourceReproducingKernel (t-w)*boundedPolynomial N a t) := by
  obtain ⟨hc,hb⟩ := boundedPolynomial_regular N a
  have hi : Integrable (fun t => sourceReproducingKernel (t-w)) :=
    sourceReproducingKernel.integrable.comp_sub_right w
  exact hi.mul_bdd hc.aestronglyMeasurable (Filter.Eventually.of_forall hb)

/-- Literal fixed-kernel reproduction of the actual bounded source,
proved term by term using only the Schwartz kernel's inversion theorem. -/
theorem boundedPolynomial_reproduce {N : ℝ} (hN : 0 < N) (a : ℕ → ℂ) (w : ℝ) :
    boundedPolynomial N a w = ∫ t, sourceReproducingKernel (t-w)*boundedPolynomial N a t := by
  have he (t : ℝ) : boundedPolynomial N a t =
      ∑ n ∈ sourceRatioIndices N, a n*phase (t*mellinFrequency ((n:ℝ)/N)) := by
    simp only [boundedPolynomial,sourceRatioIndices,mellinFrequency_phase]
  have hi (n : ℕ) : Integrable (fun t => sourceReproducingKernel (t-w)*
      (a n*phase (t*mellinFrequency ((n:ℝ)/N)))) := by
    apply (sourceReproducingKernel.integrable.comp_sub_right w).mul_bdd
    · have hp := phase_measurable
      apply Measurable.aestronglyMeasurable
      fun_prop
    · filter_upwards with t
      simp only [norm_mul,phase_norm,mul_one]
      exact le_rfl
  simp_rw [he,Finset.mul_sum]
  rw [integral_finsetSum _ (fun n _ => hi n)]
  apply Finset.sum_congr rfl
  intro n hn
  have hc : (∫ t, sourceReproducingKernel (t-w)*(a n*phase (t*mellinFrequency ((n:ℝ)/N)))) =
      a n*(∫ t, sourceReproducingKernel (t-w)*phase (t*mellinFrequency ((n:ℝ)/N))) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    ring
  rw [hc,source_kernel_phase_integral,sourceReproducingKernel_fourier,
    fixedTimeCutoff_one (source_reproducing_frequency hN hn)]
  simp only [Complex.ofReal_one,mul_one]

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.sourceReproducingKernel_fourier
#print axioms GuthMaynard.Improvement.source_reproducing_frequency
#print axioms GuthMaynard.Improvement.source_kernel_phase_integral
#print axioms GuthMaynard.Improvement.source_reproducing_integrable
#print axioms GuthMaynard.Improvement.boundedPolynomial_reproduce
