module
public import GuthMaynard.Improvement.CubicTimeMeasure
public import GuthMaynard.Improvement.Smoothing

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- The actual L2 Young pairing follows from 2ab≤a²+b² and translation
invariance. No convolution norm estimate is assumed. -/
theorem mixed_young_pairing {μ ψ : ℝ → ℝ}
    (hμm : Measurable μ) (hμ0 : ∀ t, 0 ≤ μ t) (hμ2 : Integrable (fun t => μ t^2))
    (hψm : Measurable ψ) (hψ0 : ∀ t, 0 ≤ ψ t) (hψi : Integrable ψ) :
    Integrable (fun p : ℝ × ℝ => ψ (p.1-p.2)*μ p.1*μ p.2) (volume.prod volume) ∧
    (∫ p : ℝ × ℝ, ψ (p.1-p.2)*μ p.1*μ p.2 ∂volume.prod volume) ≤
      (∫ s, ψ s)*(∫ t, μ t^2) := by
  have hr : Integrable (fun p : ℝ × ℝ => μ p.2^2*ψ (p.1-p.2)) (volume.prod volume) :=
    hμ2.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hψi
  have hn : Integrable (fun s : ℝ => ψ (-s)) := by
    simpa using hψi.comp_mul_left' (by norm_num : (-1:ℝ) ≠ 0)
  have hl : Integrable (fun p : ℝ × ℝ => μ p.1^2*ψ (p.1-p.2)) (volume.prod volume) := by
    simpa [Function.comp_def,neg_sub] using
      (hμ2.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hn).swap
  have hmajor : Integrable (fun p : ℝ × ℝ =>
      (μ p.1^2*ψ (p.1-p.2)+μ p.2^2*ψ (p.1-p.2))/2) (volume.prod volume) := (hl.add hr).div_const 2
  have hpos (p : ℝ × ℝ) : 0 ≤ ψ (p.1-p.2)*μ p.1*μ p.2 := mul_nonneg (mul_nonneg (hψ0 _) (hμ0 _)) (hμ0 _)
  have hp (p : ℝ × ℝ) : ψ (p.1-p.2)*μ p.1*μ p.2 ≤
      (μ p.1^2*ψ (p.1-p.2)+μ p.2^2*ψ (p.1-p.2))/2 := by
    nlinarith [mul_nonneg (hψ0 (p.1-p.2)) (sq_nonneg (μ p.1-μ p.2))]
  have hi : Integrable (fun p : ℝ × ℝ => ψ (p.1-p.2)*μ p.1*μ p.2) (volume.prod volume) := by
    apply hmajor.mono' (by fun_prop)
    filter_upwards [] with p
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hpos p)] using hp p
  have hil : (∫ p : ℝ × ℝ, μ p.1^2*ψ (p.1-p.2) ∂volume.prod volume) = (∫ t, μ t^2)*(∫ s, ψ s) := by
    rw [integral_prod _ hl]
    simp_rw [integral_const_mul,integral_sub_left_eq_self]
    exact integral_mul_const _ _
  have hir : (∫ p : ℝ × ℝ, μ p.2^2*ψ (p.1-p.2) ∂volume.prod volume) = (∫ t, μ t^2)*(∫ s, ψ s) := by
    rw [integral_prod _ hr,integral_integral_swap hr]
    simp_rw [integral_const_mul,integral_sub_right_eq_self]
    exact integral_mul_const _ _
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ p : ℝ × ℝ, (μ p.1^2*ψ (p.1-p.2)+μ p.2^2*ψ (p.1-p.2))/2 ∂volume.prod volume :=
      integral_mono hi hmajor hp
    _ = _ := by rw [integral_div,integral_add hl hr,hil,hir]; ring

/-- Ordinary density form of the same actual Young pairing. -/
theorem mixed_timeMeasure_young {μ ψ : ℝ → ℝ}
    (hμm : Measurable μ) (hμ0 : ∀ t, 0 ≤ μ t) (hμ2 : Integrable (fun t => μ t^2))
    (hψm : Measurable ψ) (hψ0 : ∀ t, 0 ≤ ψ t) (hψi : Integrable ψ) :
    (∫ u, ∫ t, ψ (u-t) ∂timeMeasure μ ∂timeMeasure μ) ≤
      (∫ s, ψ s)*(∫ t, μ t^2) := by
  obtain ⟨hi,hb⟩ := mixed_young_pairing hμm hμ0 hμ2 hψm hψ0 hψi
  have he : (∫ u, ∫ t, ψ (u-t) ∂timeMeasure μ ∂timeMeasure μ) =
      ∫ p : ℝ × ℝ, ψ (p.1-p.2)*μ p.1*μ p.2 ∂volume.prod volume := by
    simp_rw [timeMeasure,integral_withDensity_eq_integral_toReal_smul hμm.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),ENNReal.toReal_ofReal (hμ0 _),smul_eq_mul]
    rw [integral_prod _ hi]
    apply integral_congr_ae
    filter_upwards with u
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    ring
  rw [he]
  exact hb

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.mixed_young_pairing
#print axioms GuthMaynard.Improvement.mixed_timeMeasure_young
