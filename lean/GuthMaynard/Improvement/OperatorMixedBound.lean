module
public import GuthMaynard.Improvement.OperatorMixedCentered
public import GuthMaynard.Improvement.MixedKernelRow
public import GuthMaynard.Improvement.MixedCutoffEnvelope

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- Actual mixed trace estimate. The row budget is the sole quantitative
analytic premise; the cutoff envelope is proved integrable above. -/
theorem operator_mixed_bound (w : MathCollab.Density.ReflectionCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : ℝ → ℝ) (hm : Measurable μ)
      (h0 : ∀ t, 0 ≤ μ t) (hi : Integrable μ) (h2 : Integrable (fun t => μ t^2))
      (L Q : ℝ), 1 ≤ L → 0 ≤ Q →
      (∀ u ∈ Function.support μ, (∫ v, μ v*
        ‖centeredKernel (fun x => (w x:ℂ)) (1/2) 5 L (u-v)‖^2) ≤ Q) →
      ∀ (ι : Type) [Countable ι], letI := timeMeasure_finite hi
      ∀ b : HilbertBasis ι ℂ (Lp ℂ 2 (timeMeasure μ)),
      ‖operatorDiagonalTrace b (operatorContinuous (timeMeasure μ) w L*
        (operatorDiscrete (timeMeasure μ) w L (1/2) 5-operatorContinuous (timeMeasure μ) w L)^2)‖ ≤
        C*L*Q*(∫ t, μ t^2) := by
  let P := ∫ s, ‖mixedCutoffKernel w s‖
  have hP : 0 ≤ P := integral_nonneg (fun s => norm_nonneg _)
  refine ⟨1+P,by positivity,?_⟩
  intro μ hm h0 hi h2 L Q hL hQ hrow ι hι b
  let := timeMeasure_finite hi
  have hLp : 0 < L := by linarith
  have hs : ∀ x, x ∉ Icc (1/2:ℝ) 5 → w x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hh => hx (w.support hh))
  have hsc : ∀ x, x ∉ Icc (1/2:ℝ) 5 → (w x:ℂ) = 0 := by
    intro x hx
    simp [hs x hx]
  have hwi : Integrable (fun x => w x) := w.smooth.continuous.integrable_of_hasCompactSupport
    (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) w.support)
  obtain ⟨B,hb⟩ := isCompact_Icc.exists_bound_of_continuousOn w.smooth.continuous.continuousOn
  have hwB (x : ℝ) : |w x| ≤ max 0 B := by
    by_cases hx : x ∈ Icc (1/2:ℝ) 5
    · exact (hb x hx).trans (le_max_right _ _)
    · simp only [hs x hx,abs_zero]; exact le_max_left _ _
  rw [operator_centered_mixed (timeMeasure μ) w.smooth.continuous.measurable hwi
    (le_max_left 0 B) hwB (by norm_num : (0:ℝ)<1/2) hLp hs b]
  obtain ⟨D,hD,hDb⟩ := centeredKernel_uniform_bound w.complex_smooth
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)≤5) hsc
  have hc : Measurable (mixedCutoffKernel w) := mixedCutoffKernel_measurable w
  have hbound := kernelMixed_time_row_bound hm h0 hi h2
    (C := fun s => (L:ℂ)*mixedCutoffKernel w s)
    (K := centeredKernel (fun x => (w x:ℂ)) (1/2) 5 L)
    (ψ := fun s => ‖mixedCutoffKernel w s‖)
    (by fun_prop) (centeredKernel_measurable w.complex_smooth.continuous.measurable _ _ _)
    hc.norm (mixedCutoffKernel_integrable w).norm hLp.le hQ (mul_nonneg hD hLp.le)
    (integral_nonneg (fun x => norm_nonneg (w x:ℂ))) (fun s => norm_nonneg _)
    (mixedCutoffKernel_bound w) (fun s => hDb L s hL)
    (fun s => by simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hLp]; exact le_rfl)
    (centeredKernel_norm_neg w hLp) hrow
  calc
    _ ≤ L*Q*P*(∫ t, μ t^2) := hbound
    _ ≤ (1+P)*L*Q*(∫ t, μ t^2) := by
      have hn : 0 ≤ L*Q*(∫ t, μ t^2) := mul_nonneg (mul_nonneg hLp.le hQ) (integral_nonneg (fun t => sq_nonneg (μ t)))
      calc
        _ ≤ L*Q*P*(∫ t, μ t^2)+L*Q*(∫ t, μ t^2) := le_add_of_nonneg_right hn
        _ = _ := by ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.operator_mixed_bound
