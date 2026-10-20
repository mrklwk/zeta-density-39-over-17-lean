module
public import TwoPowerTailTransfer

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger MathCollab.Density
theorem critical_excess_integral_le_two_tails_interval {L U v A D q : ℝ}
    (hv : 0 < v) (hq : 1 < q)
    (htail : ∀ u : ℝ,v ≤ u →
      volume.real {t : ℝ | t ∈ Icc L U ∧ u ≤ zetaMomentCriticalNorm t} ≤
        A*u^(-6:ℝ)+D*u^(-q)) :
    (∫ t in Icc L U,criticalExcess v t) ≤
      (A/5)*v^(-5:ℝ)+(D/(q-1))*v^(1-q) := by
  let μ : Measure ℝ := volume.restrict (Icc L U)
  have he : Integrable (criticalExcess v) μ :=
    (criticalExcess_continuous v).continuousOn.integrableOn_compact isCompact_Icc
  have h₆ := shifted_power_tail_integral hv (by norm_num : (1:ℝ)<6)
  have hq' := shifted_power_tail_integral hv hq
  have hi : IntegrableOn (fun t : ℝ => A*(v+t)^(-6:ℝ)+D*(v+t)^(-q)) (Ioi 0) :=
    (h₆.1.const_mul A).add (hq'.1.const_mul D)
  have hb : (∫ t in Icc L U,criticalExcess v t) ≤
      ∫ t in Ioi 0,A*(v+t)^(-6:ℝ)+D*(v+t)^(-q) := by
    change (∫ t,criticalExcess v t ∂μ) ≤ _
    rw [he.integral_eq_integral_meas_le (Eventually.of_forall (criticalExcess_nonneg v))]
    apply integral_mono_of_nonneg (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)) hi
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have htp : 0 < t := ht
    have hset : {x : ℝ | t ≤ criticalExcess v x}={x : ℝ | v+t ≤ zetaMomentCriticalNorm x} := by
      ext x
      simp only [mem_ofPred_eq,criticalExcess,le_max_iff]
      constructor
      · rintro (h|h) <;> linarith
      · intro h; exact Or.inl (by linarith)
    have hm : MeasurableSet {x : ℝ | v+t ≤ zetaMomentCriticalNorm x} :=
      measurableSet_le measurable_const continuous_zetaMomentCriticalNorm.measurable
    rw [hset]
    change (μ {x : ℝ | v+t ≤ zetaMomentCriticalNorm x}).toReal ≤ _
    dsimp only [μ]
    rw [Measure.restrict_apply hm]
    have hset' : {x : ℝ | v+t ≤ zetaMomentCriticalNorm x} ∩ Icc L U=
        {x : ℝ | x ∈ Icc L U ∧ v+t ≤ zetaMomentCriticalNorm x} := by ext x; simp only [mem_inter_iff,mem_ofPred_eq,and_comm]
    rw [hset']
    exact htail (v+t) (by linarith)
  apply hb.trans_eq
  rw [integral_add (h₆.1.const_mul A) (hq'.1.const_mul D),integral_const_mul,
    integral_const_mul,h₆.2,hq'.2]
  norm_num
  ring


end Montgomery.RationalMoment.RightDetector
