module
public import GuthMaynard.Improvement.CubicTimeMeasure
public import GuthMaynard.Improvement.OperatorTrace

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate FourierTransform
namespace GuthMaynard.Improvement

/-- Literal frequency feature in the actual time L2 space. -/
theorem operator_phase_memLp (ν : Measure ℝ) [IsFiniteMeasure ν] (ξ : ℝ) :
    MemLp (fun t => phase (t*ξ)) 2 ν := by
  apply MemLp.of_bound (C := 1)
  · exact (phase_measurable.comp (measurable_id.mul_const ξ)).aestronglyMeasurable
  · filter_upwards with t
    exact (phase_norm _).le

def operatorPhase (ν : Measure ℝ) [IsFiniteMeasure ν] (ξ : ℝ) : Lp ℂ 2 ν :=
  (operator_phase_memLp ν ξ).toLp (fun t => phase (t*ξ))

theorem operator_phase_coe (ν : Measure ℝ) [IsFiniteMeasure ν] (ξ : ℝ) :
    operatorPhase ν ξ =ᵐ[ν] (fun t => phase (t*ξ)) :=
  (operator_phase_memLp ν ξ).coeFn_toLp

theorem operator_phase_conj (s : ℝ) : conj (phase s) = phase (-s) := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]
  push_cast
  ring

/-- Orientation agrees with mathlib's conjugate-linear first slot. -/
theorem operator_phase_pairing (ν : Measure ℝ) [IsFiniteMeasure ν] (ξ ζ : ℝ) :
    inner ℂ (operatorPhase ν ξ) (operatorPhase ν ζ) = measureFourier ν (ξ-ζ) := by
  rw [L2.inner_def]
  unfold measureFourier
  apply integral_congr_ae
  filter_upwards [operator_phase_coe ν ξ,operator_phase_coe ν ζ] with t ht₁ ht₂
  rw [ht₁,ht₂,RCLike.inner_apply,operator_phase_conj,← phase_add]
  congr 1
  ring

theorem operator_phase_norm_sq (ν : Measure ℝ) [IsFiniteMeasure ν] (ξ : ℝ) :
    ‖operatorPhase ν ξ‖^2 = ν.real univ := by
  have hh := operator_phase_pairing ν ξ ξ
  rw [inner_self_eq_norm_sq_to_K,sub_self] at hh
  simp [measureFourier,phase,Complex.real_smul] at hh
  exact_mod_cast hh

theorem operator_phase_norm (ν : Measure ℝ) [IsFiniteMeasure ν] (ξ : ℝ) :
    ‖operatorPhase ν ξ‖ = Real.sqrt (ν.real univ) := by
  rw [← operator_phase_norm_sq ν ξ,Real.sqrt_sq (norm_nonneg _)]

/-- Parameter continuity of the literal scalar pairing, from domination by one. -/
theorem operator_measureFourier_continuous (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Continuous (measureFourier ν) := by
  apply continuous_of_dominated (bound := fun _ => 1)
  · intro ξ
    exact (phase_measurable.comp (measurable_const.mul measurable_id)).aestronglyMeasurable
  · intro ξ
    filter_upwards with t
    exact (phase_norm _).le
  · exact integrable_const _
  · filter_upwards with t
    unfold phase
    fun_prop

theorem operator_phase_continuous (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Continuous (operatorPhase ν) := by
  apply continuous_iff_continuousAt.mpr
  intro ζ
  apply (tendsto_iff_dist_tendsto_zero).mpr
  have hid (ξ : ℝ) : dist (operatorPhase ν ξ) (operatorPhase ν ζ) =
      Real.sqrt (ν.real univ-2*(measureFourier ν (ξ-ζ)).re+ν.real univ) := by
    have hh := norm_sub_sq (𝕜 := ℂ) (operatorPhase ν ξ) (operatorPhase ν ζ)
    rw [operator_phase_norm_sq,operator_phase_norm_sq,operator_phase_pairing] at hh
    change ‖operatorPhase ν ξ-operatorPhase ν ζ‖^2 = ν.real univ-2*(measureFourier ν (ξ-ζ)).re+ν.real univ at hh
    rw [dist_eq_norm,← hh,Real.sqrt_sq (norm_nonneg _)]
  simp_rw [hid]
  have hc : Continuous (fun ξ => Real.sqrt (ν.real univ-2*(measureFourier ν (ξ-ζ)).re+ν.real univ)) := by
    have hh : Continuous (fun ξ => measureFourier ν (ξ-ζ)) :=
      (operator_measureFourier_continuous ν).comp (continuous_id.sub continuous_const)
    fun_prop
  simpa only [← hid ζ,dist_self] using hc.tendsto ζ

/-- Ordinary nonnegative time densities instantiate the Hilbert features
with their exact mass, including mass zero. -/
theorem operator_time_phase_norm {μ : ℝ → ℝ} (hm : Measurable μ)
    (h0 : ∀ t, 0 ≤ μ t) (hi : Integrable μ) (ξ : ℝ) :
    let := timeMeasure_finite hi
    ‖operatorPhase (timeMeasure μ) ξ‖ = Real.sqrt (∫ t, μ t) := by
  let := timeMeasure_finite hi
  rw [operator_phase_norm,timeMeasure_mass hm h0]

theorem operator_time_phase_pairing {μ : ℝ → ℝ} (hm : Measurable μ)
    (h0 : ∀ t, 0 ≤ μ t) (hi : Integrable μ) (ξ ζ : ℝ) :
    let := timeMeasure_finite hi
    inner ℂ (operatorPhase (timeMeasure μ) ξ) (operatorPhase (timeMeasure μ) ζ) =
      𝓕 (fun t => (μ t:ℂ)) (ξ-ζ) := by
  let := timeMeasure_finite hi
  rw [operator_phase_pairing,measureFourier_timeMeasure hm h0]

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.operator_phase_memLp
#print axioms GuthMaynard.Improvement.operator_phase_coe
#print axioms GuthMaynard.Improvement.operator_phase_conj
#print axioms GuthMaynard.Improvement.operator_phase_pairing
#print axioms GuthMaynard.Improvement.operator_phase_norm_sq
#print axioms GuthMaynard.Improvement.operator_phase_norm
#print axioms GuthMaynard.Improvement.operator_measureFourier_continuous
#print axioms GuthMaynard.Improvement.operator_phase_continuous
#print axioms GuthMaynard.Improvement.operator_time_phase_norm
#print axioms GuthMaynard.Improvement.operator_time_phase_pairing
