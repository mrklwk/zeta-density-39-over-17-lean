module
public import ActualCriticalTailReduction
public import Mathlib.MeasureTheory.Integral.Layercake

@[expose] public section

open MeasureTheory Set Filter
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger MathCollab.Density

theorem shifted_power_tail_integral {v p : ℝ} (hv : 0 < v) (hp : 1 < p) :
    IntegrableOn (fun t : ℝ => (v+t)^(-p)) (Ioi 0) ∧
    (∫ t in Ioi 0,(v+t)^(-p))=v^(1-p)/(p-1) := by
  have hpre : (fun x : ℝ => x+v) ⁻¹' Ioi v=Ioi 0 := by
    ext x
    simp only [mem_preimage,mem_Ioi]
    constructor <;> intro h <;> linarith
  have hmp := measurePreserving_add_right (volume:Measure ℝ) v
  have he := (MeasurableEquiv.addRight v).measurableEmbedding
  have hi := (hmp.integrableOn_comp_preimage he).mpr
    (integrableOn_Ioi_rpow_of_lt (by linarith : -p < -1) hv)
  have hval := hmp.setIntegral_preimage_emb he (fun x : ℝ => x^(-p)) (Ioi v)
  rw [hpre] at hi hval
  have hex : -p+1=1-p := by ring
  rw [integral_Ioi_rpow_of_lt (by linarith : -p < -1) hv,hex] at hval
  constructor
  · simpa only [Function.comp_def,add_comm] using hi
  · calc
      _ = ∫ t in Ioi 0,(t+v)^(-p) := by congr 1; funext t; rw [add_comm]
      _ = -v^(1-p)/(1-p) := hval
      _ = _ := by rw [show (1:ℝ)-p=-(p-1) by ring,neg_div_neg_eq]

/-- Layer-cake transfer of two actual critical-zeta volume tails. This is
only a transfer lemma: its displayed tail premise still needs a producer. -/
theorem critical_excess_integral_le_two_tails {T v A D q : ℝ}
    (hv : 0 < v) (hq : 1 < q)
    (htail : ∀ u : ℝ,v ≤ u →
      volume.real {t : ℝ | t ∈ Icc 0 (3*T) ∧ u ≤ zetaMomentCriticalNorm t} ≤
        A*u^(-6:ℝ)+D*u^(-q)) :
    (∫ t in Icc 0 (3*T),criticalExcess v t) ≤
      (A/5)*v^(-5:ℝ)+(D/(q-1))*v^(1-q) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 (3*T))
  have he : Integrable (criticalExcess v) μ :=
    (criticalExcess_continuous v).continuousOn.integrableOn_compact isCompact_Icc
  have h₆ := shifted_power_tail_integral hv (by norm_num : (1:ℝ)<6)
  have hq' := shifted_power_tail_integral hv hq
  have hi : IntegrableOn (fun t : ℝ => A*(v+t)^(-6:ℝ)+D*(v+t)^(-q)) (Ioi 0) :=
    (h₆.1.const_mul A).add (hq'.1.const_mul D)
  have hb : (∫ t in Icc 0 (3*T),criticalExcess v t) ≤
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
    have hset' : {x : ℝ | v+t ≤ zetaMomentCriticalNorm x} ∩ Icc 0 (3*T)=
        {x : ℝ | x ∈ Icc 0 (3*T) ∧ v+t ≤ zetaMomentCriticalNorm x} := by ext x; simp only [mem_inter_iff,mem_ofPred_eq,and_comm]
    rw [hset']
    exact htail (v+t) (by linarith)
  apply hb.trans_eq
  rw [integral_add (h₆.1.const_mul A) (hq'.1.const_mul D),integral_const_mul,
    integral_const_mul,h₆.2,hq'.2]
  norm_num
  ring

/-- The actual weighted means inherit a proved pair of physical volume tails.
The tail estimate is deliberately visible; this is not a final density root. -/
theorem separated_weightedCriticalMean_two_tail_count {T B A D q : ℝ}
    (hT : 1 ≤ T) (hB : 0 < B) (hfar : 48*Real.pi*T^(-125:ℝ) ≤ B)
    (hq : 1 < q)
    (htail : ∀ u : ℝ,B/(4*Real.pi) ≤ u →
      volume.real {t : ℝ | t ∈ Icc 0 (3*T) ∧ u ≤ zetaMomentCriticalNorm t} ≤
        A*u^(-6:ℝ)+D*u^(-q))
    (U : Finset ℝ) (hU : oneSeparated U)
    (hslab : ∀ u ∈ U,u ∈ Icc T (2*T))
    (hmean : ∀ u ∈ U,B ≤ weightedCriticalMean 128 u) :
    (U.card:ℝ)*B ≤ 2*separationMass*
      ((A/5)*(B/(4*Real.pi))^(-5:ℝ)+
        (D/(q-1))*(B/(4*Real.pi))^(1-q)) := by
  exact (separated_weightedCriticalMean_excess_count hT hB hfar U hU hslab hmean).trans
    (mul_le_mul_of_nonneg_left
      (critical_excess_integral_le_two_tails (by positivity : 0 < B/(4*Real.pi)) hq htail)
      (mul_nonneg (by norm_num) separationMass_nonneg))

end Montgomery.RationalMoment.RightDetector
