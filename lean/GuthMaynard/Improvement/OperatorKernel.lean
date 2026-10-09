import GuthMaynard.Improvement.OperatorPhase
set_option autoImplicit false
noncomputable section
open MeasureTheory Set InnerProductSpace
open scoped InnerProductSpace
namespace GuthMaynard.Improvement

/-- Actual finite integer cutoff operator. The phase orientation gives
kernel phase((t-u)*mellinFrequency(m/L)). -/
def operatorDiscrete (ν : Measure ℝ) [IsFiniteMeasure ν]
    (a : ℝ → ℝ) (L l u : ℝ) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν :=
  ∑ m ∈ Finset.Icc ⌈l*L⌉ ⌊u*L⌋, (a ((m:ℝ)/L):ℂ) •
    rankOne ℂ (operatorPhase ν (mellinFrequency ((m:ℝ)/L)))
      (operatorPhase ν (mellinFrequency ((m:ℝ)/L)))

/-- Actual continuous cutoff operator, with the full outside L incorporated
in the signed weight. All integrability is proved below from ordinary L1. -/
def operatorContinuous (ν : Measure ℝ) [IsFiniteMeasure ν]
    (a : ℝ → ℝ) (L : ℝ) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν :=
  operatorIntegral volume
    (fun x => ((L*a x:ℝ):ℂ) • operatorPhase ν (mellinFrequency x))
    (fun x => operatorPhase ν (mellinFrequency x))

theorem operator_mellin_phase_measurable (ν : Measure ℝ) [IsFiniteMeasure ν] :
    AEStronglyMeasurable (fun x => operatorPhase ν (mellinFrequency x)) volume := by
  apply (operator_phase_continuous ν).comp_aestronglyMeasurable
  have hm : Measurable mellinFrequency := by unfold mellinFrequency; fun_prop
  exact hm.aestronglyMeasurable

theorem operator_weighted_phase_measurable (ν : Measure ℝ) [IsFiniteMeasure ν]
    {a : ℝ → ℝ} (hi : Integrable a) (L : ℝ) :
    AEStronglyMeasurable (fun x => ((L*a x:ℝ):ℂ) • operatorPhase ν (mellinFrequency x)) volume := by
  exact ((Complex.continuous_ofReal.comp_aestronglyMeasurable
    (hi.aestronglyMeasurable.const_mul L))).smul (operator_mellin_phase_measurable ν)

/-- The nuclear norm-product condition is derived, not assumed. -/
theorem operator_continuous_norm_product (ν : Measure ℝ) [IsFiniteMeasure ν]
    {a : ℝ → ℝ} (hi : Integrable a) (L : ℝ) :
    Integrable (fun x => ‖((L*a x:ℝ):ℂ) • operatorPhase ν (mellinFrequency x)‖ *
      ‖operatorPhase ν (mellinFrequency x)‖) := by
  have he (x : ℝ) : ‖((L*a x:ℝ):ℂ) • operatorPhase ν (mellinFrequency x)‖ *
      ‖operatorPhase ν (mellinFrequency x)‖ = ‖L*a x‖*ν.real univ := by
    rw [norm_smul,Complex.norm_real]
    rw [mul_assoc,← pow_two,operator_phase_norm_sq]
  simp_rw [he]
  exact (hi.const_mul L).norm.mul_const _

theorem operator_continuous_integrable (ν : Measure ℝ) [IsFiniteMeasure ν]
    {a : ℝ → ℝ} (hi : Integrable a) (L : ℝ) :
    Integrable (fun x => rankOne ℂ
      (((L*a x:ℝ):ℂ) • operatorPhase ν (mellinFrequency x))
      (operatorPhase ν (mellinFrequency x))) :=
  operatorIntegral_integrable volume (operator_weighted_phase_measurable ν hi L)
    (operator_mellin_phase_measurable ν) (operator_continuous_norm_product ν hi L)

/-- Matrix coefficients of the constructed continuous operator. -/
theorem operator_continuous_pairing (ν : Measure ℝ) [IsFiniteMeasure ν]
    {a : ℝ → ℝ} (hi : Integrable a) (L : ℝ) (z w : Lp ℂ 2 ν) :
    inner ℂ z (operatorContinuous ν a L w) =
      ∫ x, ((L*a x:ℝ):ℂ)*inner ℂ z (operatorPhase ν (mellinFrequency x))*
        inner ℂ (operatorPhase ν (mellinFrequency x)) w := by
  rw [operatorContinuous,operatorIntegral_pairing volume
    (operator_weighted_phase_measurable ν hi L) (operator_mellin_phase_measurable ν)
    (operator_continuous_norm_product ν hi L)]
  apply integral_congr_ae
  filter_upwards with x
  rw [inner_smul_right]

/-- Independent diagonal trace of the constructed continuous operator.
A countable Hilbert basis remains an explicit argument; existence of a
spectral basis is not asserted. -/
theorem operator_continuous_trace (ν : Measure ℝ) [IsFiniteMeasure ν]
    {a : ℝ → ℝ} (hi : Integrable a) (L : ℝ)
    {ι : Type*} [Countable ι] (b : HilbertBasis ι ℂ (Lp ℂ 2 ν)) :
    operatorDiagonalTrace b (operatorContinuous ν a L) =
      ∫ x, ((L*a x:ℝ):ℂ)*(ν.real univ:ℂ) := by
  rw [operatorContinuous,operatorIntegral_trace volume b
    (operator_weighted_phase_measurable ν hi L) (operator_mellin_phase_measurable ν)
    (operator_continuous_norm_product ν hi L)]
  apply integral_congr_ae
  filter_upwards with x
  rw [inner_smul_right,inner_self_eq_norm_sq_to_K]
  congr 1
  change (‖operatorPhase ν (mellinFrequency x)‖:ℂ)^2 = (ν.real univ:ℂ)
  exact_mod_cast operator_phase_norm_sq ν (mellinFrequency x)

/-- Actual finite discrete matrix coefficients, with the exact integer cutoff. -/
theorem operator_discrete_pairing (ν : Measure ℝ) [IsFiniteMeasure ν]
    (a : ℝ → ℝ) (L l u : ℝ) (z w : Lp ℂ 2 ν) :
    inner ℂ z (operatorDiscrete ν a L l u w) =
      ∑ m ∈ Finset.Icc ⌈l*L⌉ ⌊u*L⌋, (a ((m:ℝ)/L):ℂ)*
        inner ℂ z (operatorPhase ν (mellinFrequency ((m:ℝ)/L)))*
        inner ℂ (operatorPhase ν (mellinFrequency ((m:ℝ)/L))) w := by
  simp only [operatorDiscrete,sum_apply,
    smul_apply,inner_sum,inner_smul_right,rankOne_apply]
  apply Finset.sum_congr rfl
  intro m hm
  ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.operator_mellin_phase_measurable
#print axioms GuthMaynard.Improvement.operator_weighted_phase_measurable
#print axioms GuthMaynard.Improvement.operator_continuous_norm_product
#print axioms GuthMaynard.Improvement.operator_continuous_integrable
#print axioms GuthMaynard.Improvement.operator_continuous_pairing

#print axioms GuthMaynard.Improvement.operator_continuous_trace
#print axioms GuthMaynard.Improvement.operator_discrete_pairing
