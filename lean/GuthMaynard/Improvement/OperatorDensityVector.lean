import GuthMaynard.Improvement.OperatorPositiveCompact
import GuthMaynard.Improvement.OrdinaryFourierL2
set_option autoImplicit false
noncomputable section
open MeasureTheory InnerProductSpace
open scoped InnerProductSpace FourierTransform
namespace GuthMaynard.Improvement

/-- The actual L2 representative has its ordinary squared-norm integral. -/
theorem operator_L2_integral_sq (ν : Measure ℝ) (f : Lp ℂ 2 ν) :
    (∫ t, ‖f t‖^2 ∂ν) = ‖f‖^2 := by
  have hh := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) f
  rw [L2.inner_def] at hh
  simp only [inner_self_eq_norm_sq_to_K] at hh
  exact_mod_cast hh

/-- Multiplying an actual density-L2 vector by its density produces ordinary L1 data. -/
theorem operator_density_vector_integrable {μ : ℝ → ℝ}
    [IsFiniteMeasure (timeMeasure μ)] (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t)
    (f : Lp ℂ 2 (timeMeasure μ)) : Integrable (fun t => (μ t:ℂ)*f t) := by
  have hi : Integrable (fun t => f t) (timeMeasure μ) := (Lp.memLp f).integrable (by norm_num)
  have hh := (integrable_withDensity_iff_integrable_smul' hm.ennreal_ofReal
    (Filter.Eventually.of_forall fun t => ENNReal.ofReal_lt_top)).mp hi
  simpa only [ENNReal.toReal_ofReal (h0 _), Complex.real_smul] using hh

/-- Bounded ordinary density gives the crucial B, rather than total-mass, L2 cost. -/
theorem operator_density_vector_L2 {μ : ℝ → ℝ}
    [IsFiniteMeasure (timeMeasure μ)] (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t)
    {B : ℝ} (_hB : 0 ≤ B) (hb : ∀ t, μ t ≤ B) (f : Lp ℂ 2 (timeMeasure μ)) :
    MemLp (fun t => (μ t:ℂ)*f t) 2 ∧
      (∫ t, ‖(μ t:ℂ)*f t‖^2) ≤ B*‖f‖^2 := by
  have hi := operator_density_vector_integrable hm h0 f
  have hs : Integrable (fun t => ‖f t‖^2) (timeMeasure μ) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hw : Integrable (fun t => μ t*‖f t‖^2) := by
    have hh := (integrable_withDensity_iff_integrable_smul' hm.ennreal_ofReal
      (Filter.Eventually.of_forall fun t => ENNReal.ofReal_lt_top)).mp hs
    simpa only [ENNReal.toReal_ofReal (h0 _), smul_eq_mul] using hh
  have he : (∫ t, μ t*‖f t‖^2) = ‖f‖^2 := by
    rw [← operator_L2_integral_sq (timeMeasure μ) f]
    change (∫ t, μ t*‖f t‖^2) =
      ∫ t, ‖f t‖^2 ∂volume.withDensity (fun t => ENNReal.ofReal (μ t))
    rw [integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
      (Filter.Eventually.of_forall fun t => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (h0 _), smul_eq_mul]
  have hp (t : ℝ) : ‖(μ t:ℂ)*f t‖^2 ≤ B*(μ t*‖f t‖^2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h0 t), mul_pow]
    nlinarith [mul_le_mul_of_nonneg_right (hb t) (mul_nonneg (h0 t) (sq_nonneg ‖f t‖))]
  have hg : Integrable (fun t => ‖(μ t:ℂ)*f t‖^2) := by
    apply (hw.const_mul B).mono' (hi.aestronglyMeasurable.norm.pow 2)
    filter_upwards with t
    simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_pow, abs_norm] using hp t
  refine ⟨(memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mpr hg, ?_⟩
  calc
    _ ≤ ∫ t, B*(μ t*‖f t‖^2) := integral_mono hg (hw.const_mul B) hp
    _ = B*‖f‖^2 := by rw [integral_const_mul, he]

/-- Actual phase pairing is the literal Fourier transform of the density-weighted vector. -/
theorem operator_density_phase_pairing {μ : ℝ → ℝ}
    [IsFiniteMeasure (timeMeasure μ)] (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t)
    (f : Lp ℂ 2 (timeMeasure μ)) (ξ : ℝ) :
    inner ℂ (operatorPhase (timeMeasure μ) ξ) f = 𝓕 (fun t => (μ t:ℂ)*f t) ξ := by
  rw [L2.inner_def]
  have he : (∫ t, inner ℂ ((operatorPhase (timeMeasure μ) ξ) t) (f t) ∂timeMeasure μ) =
      ∫ t, phase (-ξ*t)*f t ∂timeMeasure μ := by
    apply integral_congr_ae
    filter_upwards [operator_phase_coe (timeMeasure μ) ξ] with t ht
    rw [ht]
    simp only [RCLike.inner_apply, operator_phase_conj]
    rw [show -(t*ξ) = -ξ*t by ring]
    ring
  rw [he]
  change (∫ t, phase (-ξ*t)*f t ∂volume.withDensity (fun t => ENNReal.ofReal (μ t))) = _
  rw [integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
    (Filter.Eventually.of_forall fun t => ENNReal.ofReal_lt_top), fourier_eq_phase_integral]
  apply integral_congr_ae
  filter_upwards with t
  simp only [ENNReal.toReal_ofReal (h0 _), Complex.real_smul]
  ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.operator_L2_integral_sq
#print axioms GuthMaynard.Improvement.operator_density_vector_integrable
#print axioms GuthMaynard.Improvement.operator_density_vector_L2
#print axioms GuthMaynard.Improvement.operator_density_phase_pairing
