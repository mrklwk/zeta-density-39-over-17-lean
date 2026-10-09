import GuthMaynard.Improvement.ReflectionNear
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- The continuous spatial kernel without its outside L. -/
def mixedCutoffKernel (w : MathCollab.Density.ReflectionCutoff) (s : ℝ) : ℂ :=
  ∫ x, logModulated (fun x => (w x:ℂ)) s x

theorem mixedCutoffKernel_eq (w : MathCollab.Density.ReflectionCutoff) (s : ℝ) :
    mixedCutoffKernel w s = MathCollab.Density.cutoffIntegral w s := by
  unfold mixedCutoffKernel MathCollab.Density.cutoffIntegral
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    have hz : w x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => by
      have hp := (w.support hh).1
      exact hx (by change 0 < x; linarith))
    simp [hz])]
  apply integral_congr_ae
  filter_upwards with x
  unfold logModulated MathCollab.Density.dirichletPhase
  congr 2
  push_cast
  ring

/-- This actual fixed-cutoff envelope is integrable, not an analytic premise. -/
theorem mixedCutoffKernel_integrable (w : MathCollab.Density.ReflectionCutoff) :
    Integrable (mixedCutoffKernel w) := by
  have hi := MathCollab.Density.integrable_mellin_line_one w.complex_smooth w.complex_support
  change Integrable (MathCollab.Density.mellinLine (fun x => (w x:ℂ))) at hi
  exact hi.congr (Filter.Eventually.of_forall (fun s =>
    (MathCollab.Density.mellinLine_eq_cutoffIntegral w s).trans (mixedCutoffKernel_eq w s).symm))

theorem mixedCutoffKernel_measurable (w : MathCollab.Density.ReflectionCutoff) :
    Measurable (mixedCutoffKernel w) := by
  exact (logModulated_measurable w.complex_smooth.continuous.measurable).stronglyMeasurable.integral_prod_right'.measurable

theorem mixedCutoffKernel_bound (w : MathCollab.Density.ReflectionCutoff) (s : ℝ) :
    ‖mixedCutoffKernel w s‖ ≤ ∫ x, ‖(w x:ℂ)‖ := by
  have hi : Integrable (fun x => (w x:ℂ)) := w.complex_smooth.continuous.integrable_of_hasCompactSupport
    (MathCollab.Density.compactSupport_of_cutoff_support w.complex_support)
  apply norm_integral_le_of_norm_le hi.norm
  filter_upwards with x
  simp only [logModulated_eq_phase,norm_mul,phase_norm,mul_one]
  exact le_rfl

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.mixedCutoffKernel_eq
#print axioms GuthMaynard.Improvement.mixedCutoffKernel_integrable
#print axioms GuthMaynard.Improvement.mixedCutoffKernel_measurable
#print axioms GuthMaynard.Improvement.mixedCutoffKernel_bound
