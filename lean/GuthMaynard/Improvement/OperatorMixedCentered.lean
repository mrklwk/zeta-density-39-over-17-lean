import GuthMaynard.Improvement.OperatorMixedTrace
set_option autoImplicit false
noncomputable section
open MeasureTheory Set InnerProductSpace
namespace GuthMaynard.Improvement

/-- Compact-frequency presentation of the actual continuous operator. -/
theorem operator_continuous_frequency (ν : Measure ℝ) [IsFiniteMeasure ν]
    {a : ℝ → ℝ} {l u : ℝ} (hs : ∀ x, x ∉ Icc l u → a x = 0) (L : ℝ) :
    operatorContinuous ν a L = operatorFrequency ν (volume.restrict (Icc l u))
      (fun x => ((L*a x:ℝ):ℂ)) mellinFrequency := by
  unfold operatorContinuous operatorFrequency operatorIntegral
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  simp [hs x hx]

/-- Its spatial kernel retains the exact outside scale factor. -/
theorem continuous_frequencyKernel {a : ℝ → ℝ} {l u : ℝ}
    (hs : ∀ x, x ∉ Icc l u → a x = 0) (L s : ℝ) :
    frequencyKernel (volume.restrict (Icc l u)) (fun x => ((L*a x:ℝ):ℂ)) mellinFrequency s =
      (L:ℂ)*(∫ x, logModulated (fun x => (a x:ℂ)) s x) := by
  unfold frequencyKernel
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hs x hx])]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [logModulated_eq_phase]
  push_cast
  ring

/-- Literal mixed trace of continuous times centered squared, with its
independently specified spatial kernel. -/
theorem operator_centered_mixed (ν : Measure ℝ) [IsFiniteMeasure ν]
    {a : ℝ → ℝ} (ha : Measurable a) (hi : Integrable a) {B l u L : ℝ}
    (hB : 0 ≤ B) (hb : ∀ x, |a x| ≤ B) (hl : 0 < l) (hL : 0 < L)
    (hs : ∀ x, x ∉ Icc l u → a x = 0)
    {ι : Type*} [Countable ι] (b : HilbertBasis ι ℂ (Lp ℂ 2 ν)) :
    operatorDiagonalTrace b (operatorContinuous ν a L*
      (operatorDiscrete ν a L l u-operatorContinuous ν a L)^2) =
      kernelMixed ν (fun s => (L:ℂ)*∫ x, logModulated (fun x => (a x:ℂ)) s x)
        (centeredKernel (fun x => (a x:ℂ)) l u L) := by
  rw [← operator_centered_eq ν hi hl hL hs,operator_continuous_frequency ν hs L]
  have hm : Measurable mellinFrequency := by unfold mellinFrequency; fun_prop
  have hc : ∀ x, ‖((L*a x:ℝ):ℂ)‖ ≤ L*B := by
    intro x
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos hL]
    exact mul_le_mul_of_nonneg_left (hb x) hL.le
  rw [operator_frequency_mixed ν (volume.restrict (Icc l u))
    (operatorCenteredMeasure l u L) (by fun_prop)
    (operator_centered_amplitude_measurable ha L) hm operator_centered_frequency_measurable
    (mul_nonneg hL.le hB) (mul_nonneg (by positivity) hB) hc
    (operator_centered_amplitude_bound hB hb L) b]
  congr 1
  · funext s
    exact continuous_frequencyKernel hs L s
  · funext s
    exact operator_centered_frequencyKernel ha hi hl hL hs s

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.operator_continuous_frequency
#print axioms GuthMaynard.Improvement.continuous_frequencyKernel
#print axioms GuthMaynard.Improvement.operator_centered_mixed
