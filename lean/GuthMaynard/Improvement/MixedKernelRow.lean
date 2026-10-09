import GuthMaynard.Improvement.OperatorMixedTrace
import GuthMaynard.Improvement.MixedKernelYoung
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- Actual mixed kernel estimate from a row budget. Evenness is required
only of the norm of K, and no operator positivity or commutation appears. -/
theorem kernelMixed_row_bound (ν : Measure ℝ) [IsFiniteMeasure ν]
    {C K : ℝ → ℂ} {ψ : ℝ → ℝ} {L Q B D : ℝ}
    (hC : Measurable C) (hK : Measurable K) (hψ : Measurable ψ)
    (hL : 0 ≤ L) (hQ : 0 ≤ Q) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hψ0 : ∀ s, 0 ≤ ψ s) (hψD : ∀ s, ψ s ≤ D)
    (hKB : ∀ s, ‖K s‖ ≤ B) (hCψ : ∀ s, ‖C s‖ ≤ L*ψ s)
    (hKe : ∀ s, ‖K (-s)‖ = ‖K s‖)
    (hrow : ∀ᵐ u ∂ν, (∫ v, ‖K (u-v)‖^2 ∂ν) ≤ Q) :
    ‖kernelMixed ν C K‖ ≤ L*Q*(∫ u, ∫ v, ψ (u-v) ∂ν ∂ν) := by
  have hCb (s : ℝ) : ‖C s‖ ≤ L*D := (hCψ s).trans (mul_le_mul_of_nonneg_left (hψD s) hL)
  have hk (u : ℝ) : Integrable (fun v => ‖K (u-v)‖^2) ν := by
    apply (integrable_const (B^2)).mono' (by apply Measurable.aestronglyMeasurable; fun_prop)
    filter_upwards [] with v
    simpa only [Real.norm_eq_abs,abs_pow,abs_norm] using pow_le_pow_left₀ (norm_nonneg _) (hKB (u-v)) 2
  have hψone (u : ℝ) : Integrable (fun v => ψ (u-v)) ν := by
    apply (integrable_const D).mono' (by apply Measurable.aestronglyMeasurable; fun_prop)
    filter_upwards [] with v
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hψ0 _)] using hψD (u-v)
  have hψpair : Integrable (fun p : ℝ × ℝ => ψ (p.1-p.2)) (ν.prod ν) := by
    apply (integrable_const D).mono' (by apply Measurable.aestronglyMeasurable; fun_prop)
    filter_upwards [] with p
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hψ0 _)] using hψD (p.1-p.2)
  have hpoint (u v t : ℝ) : ‖C (u-v)*K (v-t)*K (t-u)‖ ≤ L*D*B^2 := by
    simp only [norm_mul]
    calc
      _ ≤ (L*D)*B*B := mul_le_mul (mul_le_mul (hCb _) (hKB _) (norm_nonneg _) (mul_nonneg hL hD))
        (hKB _) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have htri : Integrable (fun t : Triple => C (t.1-t.2.1)*K (t.2.1-t.2.2)*K (t.2.2-t.1)) (tripleMeasure ν) := by
    let : IsFiniteMeasure (tripleMeasure ν) := by unfold tripleMeasure; infer_instance
    apply (integrable_const (L*D*B^2)).mono' (by apply Measurable.aestronglyMeasurable; fun_prop)
    exact Filter.Eventually.of_forall (fun t => hpoint t.1 t.2.1 t.2.2)
  have hpair (u : ℝ) : Integrable (fun p : ℝ × ℝ => C (u-p.1)*K (p.1-p.2)*K (p.2-u)) (ν.prod ν) := by
    apply (integrable_const (L*D*B^2)).mono' (by apply Measurable.aestronglyMeasurable; fun_prop)
    exact Filter.Eventually.of_forall (fun p => hpoint u p.1 p.2)
  have he : kernelMixed ν C K = ∫ u, ∫ v, ∫ t, C (u-v)*K (v-t)*K (t-u) ∂ν ∂ν ∂ν := by
    rw [kernelMixed,tripleMeasure,integral_prod _ htri]
    apply integral_congr_ae
    filter_upwards with u
    exact integral_prod _ (hpair u)
  have hinner (u v : ℝ) (hu : (∫ t, ‖K (u-t)‖^2 ∂ν) ≤ Q)
      (hv : (∫ t, ‖K (v-t)‖^2 ∂ν) ≤ Q) :
      ‖∫ t, C (u-v)*K (v-t)*K (t-u) ∂ν‖ ≤ (L*Q)*ψ (u-v) := by
    have hb : ‖∫ t, C (u-v)*K (v-t)*K (t-u) ∂ν‖ ≤
        ‖C (u-v)‖*((∫ t, ‖K (v-t)‖^2 ∂ν)+(∫ t, ‖K (u-t)‖^2 ∂ν))/2 := by
      have hh := norm_integral_le_of_norm_le
        ((((hk v).add (hk u)).const_mul ‖C (u-v)‖).div_const 2)
        (Filter.Eventually.of_forall (fun t => show ‖C (u-v)*K (v-t)*K (t-u)‖ ≤
          ‖C (u-v)‖*(‖K (v-t)‖^2+‖K (u-t)‖^2)/2 from by
          have hn : ‖K (t-u)‖ = ‖K (u-t)‖ := by simpa only [neg_sub] using hKe (u-t)
          rw [norm_mul,norm_mul,hn]
          nlinarith [mul_nonneg (norm_nonneg (C (u-v))) (sq_nonneg (‖K (v-t)‖-‖K (u-t)‖))]))
      simpa only [Pi.add_apply,integral_div,integral_const_mul,integral_add (hk v) (hk u)] using hh
    calc
      _ ≤ ‖C (u-v)‖*((∫ t, ‖K (v-t)‖^2 ∂ν)+(∫ t, ‖K (u-t)‖^2 ∂ν))/2 := hb
      _ ≤ ‖C (u-v)‖*Q := by nlinarith [norm_nonneg (C (u-v))]
      _ ≤ (L*ψ (u-v))*Q := mul_le_mul_of_nonneg_right (hCψ _) hQ
      _ = _ := by ring
  rw [he]
  have hout := norm_integral_le_of_norm_le
    (f := fun u => ∫ v, ∫ t, C (u-v)*K (v-t)*K (t-u) ∂ν ∂ν)
    ((hψpair.const_mul (L*Q)).integral_prod_left)
    (by
      filter_upwards [hrow] with u hu
      apply norm_integral_le_of_norm_le ((hψone u).const_mul (L*Q))
      filter_upwards [hrow] with v hv
      exact hinner u v hu hv)
  simpa only [integral_const_mul] using hout

/-- Ordinary source rows on the literal support suffice for the time-measure
row premise. The complement has zero density and is not silently bounded. -/
theorem timeMeasure_row_of_support {μ : ℝ → ℝ} (hm : Measurable μ)
    (h0 : ∀ t, 0 ≤ μ t) {K : ℝ → ℂ} {Q : ℝ}
    (hrow : ∀ u ∈ Function.support μ, (∫ v, μ v*‖K (u-v)‖^2) ≤ Q) :
    ∀ᵐ u ∂timeMeasure μ, (∫ v, ‖K (u-v)‖^2 ∂timeMeasure μ) ≤ Q := by
  apply (ae_withDensity_iff hm.ennreal_ofReal).mpr
  filter_upwards with u
  intro hu
  have hum : u ∈ Function.support μ := by
    intro hz
    simp [hz] at hu
  have hh := hrow u hum
  simpa only [timeMeasure,integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),ENNReal.toReal_ofReal (h0 _),smul_eq_mul] using hh

/-- Actual ordinary mixed-cycle estimate with the sole quantitative kernel
input exposed as a row bound on support μ. -/
theorem kernelMixed_time_row_bound {μ ψ : ℝ → ℝ} {C K : ℝ → ℂ} {L Q B D : ℝ}
    (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t) (hi : Integrable μ)
    (h2 : Integrable (fun t => μ t^2))
    (hC : Measurable C) (hK : Measurable K) (hψ : Measurable ψ) (hψi : Integrable ψ)
    (hL : 0 ≤ L) (hQ : 0 ≤ Q) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hψ0 : ∀ s, 0 ≤ ψ s) (hψD : ∀ s, ψ s ≤ D)
    (hKB : ∀ s, ‖K s‖ ≤ B) (hCψ : ∀ s, ‖C s‖ ≤ L*ψ s)
    (hKe : ∀ s, ‖K (-s)‖ = ‖K s‖)
    (hrow : ∀ u ∈ Function.support μ, (∫ v, μ v*‖K (u-v)‖^2) ≤ Q) :
    ‖kernelMixed (timeMeasure μ) C K‖ ≤ L*Q*(∫ s, ψ s)*(∫ t, μ t^2) := by
  let := timeMeasure_finite hi
  calc
    _ ≤ L*Q*(∫ u, ∫ v, ψ (u-v) ∂timeMeasure μ ∂timeMeasure μ) :=
      kernelMixed_row_bound (timeMeasure μ) hC hK hψ hL hQ hB hD hψ0 hψD hKB hCψ hKe
        (timeMeasure_row_of_support hm h0 hrow)
    _ ≤ L*Q*((∫ s, ψ s)*(∫ t, μ t^2)) :=
      mul_le_mul_of_nonneg_left (mixed_timeMeasure_young hm h0 h2 hψ hψ0 hψi) (mul_nonneg hL hQ)
    _ = _ := by ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.kernelMixed_row_bound
#print axioms GuthMaynard.Improvement.timeMeasure_row_of_support
#print axioms GuthMaynard.Improvement.kernelMixed_time_row_bound
