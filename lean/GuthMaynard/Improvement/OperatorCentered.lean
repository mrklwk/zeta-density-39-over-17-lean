module
public import GuthMaynard.Improvement.OperatorCubic
public import GuthMaynard.Improvement.CenteredKernelBridge

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set InnerProductSpace
open scoped InnerProductSpace
namespace GuthMaynard.Improvement

/-- Negative atoms encode the discrete part disjointly from the positive
continuous cutoff. This is a finite positive measure, not a signed measure. -/
def operatorCenteredMeasure (l u L : ℝ) : Measure ℝ :=
  (∑ m ∈ Finset.Icc ⌈l*L⌉ ⌊u*L⌋, Measure.dirac (-((m:ℝ)/L))) + volume.restrict (Icc l u)

instance operatorCenteredMeasure_finite (l u L : ℝ) :
    IsFiniteMeasure (operatorCenteredMeasure l u L) := by
  unfold operatorCenteredMeasure
  infer_instance

def operatorCenteredAmplitude (a : ℝ → ℝ) (L x : ℝ) : ℂ :=
  if x < 0 then (a (-x):ℂ) else -(L:ℂ)*(a x:ℂ)

def operatorCenteredFrequency (x : ℝ) : ℝ := mellinFrequency |x|

theorem operator_centered_amplitude_measurable {a : ℝ → ℝ}
    (ha : Measurable a) (L : ℝ) : Measurable (operatorCenteredAmplitude a L) := by
  unfold operatorCenteredAmplitude
  apply Measurable.ite (measurableSet_lt measurable_id measurable_const) <;> fun_prop

theorem operator_centered_frequency_measurable : Measurable operatorCenteredFrequency := by
  unfold operatorCenteredFrequency mellinFrequency
  fun_prop

theorem operator_centered_amplitude_bound {a : ℝ → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hb : ∀ x, |a x| ≤ B) (L x : ℝ) :
    ‖operatorCenteredAmplitude a L x‖ ≤ (1+|L|)*B := by
  unfold operatorCenteredAmplitude
  split_ifs
  · rw [Complex.norm_real,Real.norm_eq_abs]
    nlinarith [hb (-x),abs_nonneg L]
  · rw [norm_mul,norm_neg,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
    nlinarith [mul_le_mul_of_nonneg_left (hb x) (abs_nonneg L)]

/-- Exact integral over the actual finite positive presentation measure. -/
theorem operator_centered_measure_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (F : ℝ → E) (l u L : ℝ)
    (hi : IntegrableOn F (Icc l u)) :
    (∫ x, F x ∂operatorCenteredMeasure l u L) =
      (∑ m ∈ Finset.Icc ⌈l*L⌉ ⌊u*L⌋, F (-((m:ℝ)/L))) + ∫ x in Icc l u, F x := by
  have hd : ∀ m ∈ Finset.Icc ⌈l*L⌉ ⌊u*L⌋,
      Integrable F (Measure.dirac (-((m:ℝ)/L))) := by
    intro m hm
    exact integrable_dirac (by simp)
  rw [operatorCenteredMeasure,integral_add_measure (integrable_finsetSum_measure.mpr hd) hi,
    integral_finsetSum_measure hd]
  simp

theorem operator_centered_sample_pos {l u L : ℝ} (hl : 0 < l) (hL : 0 < L)
    {m : ℤ} (hm : m ∈ Finset.Icc ⌈l*L⌉ ⌊u*L⌋) : 0 < (m:ℝ)/L := by
  have hh : l*L ≤ (m:ℝ) := Int.ceil_le.mp (Finset.mem_Icc.mp hm).1
  exact div_pos ((mul_pos hl hL).trans_le hh) hL

/-- The scalar kernel of the signed-amplitude positive-measure presentation
is literally the full centered kernel, without Poisson expansion. -/
theorem operator_centered_frequencyKernel {a : ℝ → ℝ} (ha : Measurable a)
    (hi : Integrable a) {l u L : ℝ} (hl : 0 < l) (hL : 0 < L)
    (hs : ∀ x, x ∉ Icc l u → a x = 0) (s : ℝ) :
    frequencyKernel (operatorCenteredMeasure l u L) (operatorCenteredAmplitude a L)
      operatorCenteredFrequency s = centeredKernel (fun x => (a x:ℂ)) l u L s := by
  let F : ℝ → ℂ := fun x => operatorCenteredAmplitude a L x*phase (s*operatorCenteredFrequency x)
  have hj : Integrable (fun x => ((L*a x:ℝ):ℂ)*phase (s*mellinFrequency x)) := by
    apply ((hi.const_mul L).norm).mono'
    · have hp := phase_measurable
      have hf : Measurable mellinFrequency := by unfold mellinFrequency; fun_prop
      exact ((Complex.measurable_ofReal.comp (measurable_const.mul ha)).mul
        (hp.comp (measurable_const.mul hf))).aestronglyMeasurable
    · filter_upwards with x
      simp only [norm_mul,phase_norm,mul_one,Complex.norm_real]
      exact le_rfl
  have he (x : ℝ) (hx : x ∈ Icc l u) : F x = -(((L*a x:ℝ):ℂ)*phase (s*mellinFrequency x)) := by
    have hx0 : 0 < x := hl.trans_le hx.1
    simp [F,operatorCenteredAmplitude,operatorCenteredFrequency,not_lt.mpr hx0.le,abs_of_pos hx0]
  have hFi : IntegrableOn F (Icc l u) := hj.neg.integrableOn.congr (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact (he x hx).symm)
  change (∫ x, F x ∂operatorCenteredMeasure l u L) = _
  rw [operator_centered_measure_integral F l u L hFi]
  have hsum : (∑ m ∈ Finset.Icc ⌈l*L⌉ ⌊u*L⌋, F (-((m:ℝ)/L))) =
      ∑ m ∈ Finset.Icc ⌈l*L⌉ ⌊u*L⌋, logModulated (fun x => (a x:ℂ)) s ((m:ℝ)/L) := by
    apply Finset.sum_congr rfl
    intro m hm
    have hp := operator_centered_sample_pos hl hL hm
    rw [logModulated_eq_phase]
    simp [F,operatorCenteredAmplitude,operatorCenteredFrequency,neg_neg,neg_lt_zero.mpr hp,abs_neg,abs_of_pos hp]
  rw [hsum]
  unfold centeredKernel
  rw [show (∫ x in Icc l u, F x) = ∫ x in Icc l u,
    -(((L*a x:ℝ):ℂ)*phase (s*mellinFrequency x)) from integral_congr_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact he x hx)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (by
    intro x hx
    simp [hs x hx]),integral_neg]
  simp_rw [logModulated_eq_phase,Complex.ofReal_mul,mul_assoc]
  rw [integral_const_mul]
  ring

/-- The positive-measure signed-amplitude presentation is exactly the
constructed finite discrete operator minus its continuous correction. -/
theorem operator_centered_eq (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a : ℝ → ℝ} (hi : Integrable a) {l u L : ℝ} (hl : 0 < l) (hL : 0 < L)
    (hs : ∀ x, x ∉ Icc l u → a x = 0) :
    operatorFrequency μ (operatorCenteredMeasure l u L) (operatorCenteredAmplitude a L)
      operatorCenteredFrequency = operatorDiscrete μ a L l u-operatorContinuous μ a L := by
  let F := fun x => rankOne ℂ
    (operatorCenteredAmplitude a L x • operatorPhase μ (operatorCenteredFrequency x))
    (operatorPhase μ (operatorCenteredFrequency x))
  let J := fun x => rankOne ℂ (((L*a x:ℝ):ℂ) • operatorPhase μ (mellinFrequency x))
    (operatorPhase μ (mellinFrequency x))
  have hj : Integrable J := operator_continuous_integrable μ hi L
  have he (x : ℝ) (hx : x ∈ Icc l u) : F x = -J x := by
    have hx0 : 0 < x := hl.trans_le hx.1
    apply ContinuousLinearMap.ext
    intro v
    simp [F,J,operatorCenteredAmplitude,operatorCenteredFrequency,
      not_lt.mpr hx0.le,abs_of_pos hx0,rankOne_apply,smul_smul]
  have hFi : IntegrableOn F (Icc l u) := hj.neg.integrableOn.congr (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact (he x hx).symm)
  change (∫ x, F x ∂operatorCenteredMeasure l u L) = _
  rw [operator_centered_measure_integral F l u L hFi]
  have hsum : (∑ m ∈ Finset.Icc ⌈l*L⌉ ⌊u*L⌋, F (-((m:ℝ)/L))) =
      operatorDiscrete μ a L l u := by
    apply Finset.sum_congr rfl
    intro m hm
    have hp := operator_centered_sample_pos hl hL hm
    apply ContinuousLinearMap.ext
    intro v
    simp only [F,operatorCenteredAmplitude,operatorCenteredFrequency,
      ite_eq_left (neg_lt_zero.mpr hp),neg_neg,abs_neg,abs_of_pos hp,rankOne_apply,smul_apply]
    exact smul_comm _ _ _
  rw [hsum,sub_eq_add_neg]
  congr 1
  rw [show (∫ x in Icc l u, F x) = ∫ x in Icc l u, -J x from
    integral_congr_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact he x hx)]
  rw [integral_neg,setIntegral_eq_integral_of_forall_compl_eq_zero (by
    intro x hx
    simp [J,hs x hx])]
  rfl

/-- Actual centered operator cubic trace equals the literal centered time
kernel cubic. Only a given countable Hilbert basis remains explicit. -/
theorem operator_centered_cubic (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a : ℝ → ℝ} (ha : Measurable a) (hi : Integrable a)
    {l u L B : ℝ} (hl : 0 < l) (hL : 0 < L) (hB : 0 ≤ B)
    (hb : ∀ x, |a x| ≤ B) (hs : ∀ x, x ∉ Icc l u → a x = 0)
    {ι : Type*} [Countable ι] (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) :
    operatorDiagonalTrace b ((operatorDiscrete μ a L l u-operatorContinuous μ a L)^3) =
      kernelCubic μ (centeredKernel (fun x => (a x:ℂ)) l u L) := by
  have htrace := operator_frequency_cubic μ (operatorCenteredMeasure l u L)
    (operator_centered_amplitude_measurable ha L) operator_centered_frequency_measurable
    (show 0 ≤ (1+|L|)*B by positivity) (operator_centered_amplitude_bound hB hb L) b
  rw [operator_centered_eq μ hi hl hL hs] at htrace
  have hk : frequencyKernel (operatorCenteredMeasure l u L) (operatorCenteredAmplitude a L)
      operatorCenteredFrequency = centeredKernel (fun x => (a x:ℂ)) l u L := by
    funext s
    exact operator_centered_frequencyKernel ha hi hl hL hs s
  simpa only [hk] using htrace

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.operator_centered_amplitude_measurable
#print axioms GuthMaynard.Improvement.operator_centered_frequency_measurable
#print axioms GuthMaynard.Improvement.operator_centered_amplitude_bound
#print axioms GuthMaynard.Improvement.operator_centered_measure_integral
#print axioms GuthMaynard.Improvement.operator_centered_sample_pos
#print axioms GuthMaynard.Improvement.operator_centered_frequencyKernel

#print axioms GuthMaynard.Improvement.operator_centered_eq
#print axioms GuthMaynard.Improvement.operator_centered_cubic
