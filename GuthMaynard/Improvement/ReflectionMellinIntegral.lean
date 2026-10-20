module
public import GuthMaynard.Improvement.ReflectionNear

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- Actual weighted reflected energy is jointly integrable for every finite
time measure. The Mellin integral is not truncated or treated formally. -/
theorem reflection_mellin_integrable (w : MathCollab.Density.ReflectionCutoff)
    (ν : Measure ℝ) [IsFiniteMeasure ν] (L H u : ℝ) :
    Integrable (fun z : ℝ × ℝ =>
      ‖MathCollab.Density.mellinLine (fun x => (w x:ℂ)) z.2‖ *
        ‖MathCollab.Density.bandPhaseSum L H (z.1-u) z.2‖^2) (ν.prod volume) := by
  have hW := MathCollab.Density.integrable_mellin_line_one w.complex_smooth w.complex_support
  have hb : Measurable (fun z : ℝ × ℝ =>
      MathCollab.Density.bandPhaseSum L H (z.1-u) z.2) := by
    unfold MathCollab.Density.bandPhaseSum MathCollab.Density.dirichletPhase
    fun_prop
  apply (hW.norm.comp_snd ν).mul_bdd (hb.aestronglyMeasurable.norm.pow 2)
    (c := ((MathCollab.Density.reflectionBand L H).card:ℝ)^2)
  filter_upwards with z
  simp only [Pi.pow_apply,Real.norm_eq_abs]
  rw [abs_of_nonneg (sq_nonneg (‖MathCollab.Density.bandPhaseSum L H (z.1-u) z.2‖))]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (MathCollab.Density.norm_bandPhaseSum_le L H (z.1-u) z.2) 2

/-- Fubini retains the actual Mellin weight. A uniform inner time-energy
budget is the sole estimate premise of this assembly helper. -/
theorem reflection_mellin_integral_bound (w : MathCollab.Density.ReflectionCutoff)
    (ν : Measure ℝ) [IsFiniteMeasure ν] (L H u B : ℝ)
    (hB : ∀ r : ℝ, (∫ t, ‖MathCollab.Density.bandPhaseSum L H (t-u) r‖^2 ∂ν) ≤ B) :
    (∫ t, (∫ r, ‖MathCollab.Density.mellinLine (fun x => (w x:ℂ)) r‖ *
      ‖MathCollab.Density.bandPhaseSum L H (t-u) r‖^2) ∂ν) ≤
      MathCollab.Density.mellinMass w*B := by
  have hi := reflection_mellin_integrable w ν L H u
  have hW := MathCollab.Density.integrable_mellin_line_one w.complex_smooth w.complex_support
  rw [integral_integral_swap hi]
  simp_rw [integral_const_mul]
  change (∫ r, _) ≤ (∫ r, ‖MathCollab.Density.mellinLine (fun x => (w x:ℂ)) r‖)*B
  rw [← integral_mul_const]
  apply integral_mono_ae
  · simpa only [integral_const_mul] using hi.integral_prod_right
  · exact hW.norm.mul_const B
  · filter_upwards with r
    exact mul_le_mul_of_nonneg_left (hB r) (norm_nonneg _)

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.reflection_mellin_integrable
#print axioms GuthMaynard.Improvement.reflection_mellin_integral_bound
