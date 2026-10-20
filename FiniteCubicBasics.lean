module
public import SignedAmplifiedMoment
public import GuthMaynard.Improvement.CenteredCubicApprox

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Set
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement

def finiteTimeMeasure (W : Finset ℝ) : Measure ℝ := ∑ t ∈ W, Measure.dirac t

instance finite_time_measure_finite (W : Finset ℝ) : IsFiniteMeasure (finiteTimeMeasure W) := by
  unfold finiteTimeMeasure
  infer_instance

theorem finite_time_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (W : Finset ℝ) (f : ℝ → E) : (∫ t, f t ∂finiteTimeMeasure W) = ∑ t ∈ W, f t := by
  rw [finiteTimeMeasure,integral_finsetSum_measure (fun t _ => integrable_dirac (by simp))]
  simp

theorem finite_time_fourier (W : Finset ℝ) (ξ : ℝ) :
    measureFourier (finiteTimeMeasure W) ξ =
      ∑ t ∈ W, GuthMaynard.Improvement.phase (-ξ*t) := by
  exact finite_time_integral W _

def finiteCubic (W : Finset ℝ) (K : ℝ → ℂ) : ℂ :=
  ∑ t ∈ W, ∑ u ∈ W, ∑ v ∈ W, K (t-u)*K (u-v)*K (v-t)

theorem finite_cubic_trace (w : MathCollab.Density.ReflectionCutoff) (L : ℝ) (W : Finset ℝ) :
    Matrix.trace (cutoffCenteredMatrix w L W^3) =
      finiteCubic W (MathCollab.Density.hKernel (reflectionSquare w) L) := by
  rw [pow_succ,pow_two]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,sum_mul,cutoff_centered_entry]
  conv_lhs =>
    arg 2
    ext t
    rw [sum_comm]
  rw [sum_coe_sort W (fun t => ∑ u : W, ∑ v : W,
    MathCollab.Density.hKernel (reflectionSquare w) L (t-(u:ℝ))*
      MathCollab.Density.hKernel (reflectionSquare w) L ((u:ℝ)-v)*
      MathCollab.Density.hKernel (reflectionSquare w) L ((v:ℝ)-t))]
  apply sum_congr rfl
  intro t _
  rw [sum_coe_sort W (fun u => ∑ v : W,
    MathCollab.Density.hKernel (reflectionSquare w) L (t-u)*
      MathCollab.Density.hKernel (reflectionSquare w) L (u-(v:ℝ))*
      MathCollab.Density.hKernel (reflectionSquare w) L ((v:ℝ)-t))]
  apply sum_congr rfl
  intro u _
  exact sum_coe_sort W (fun v =>
    MathCollab.Density.hKernel (reflectionSquare w) L (t-u)*
      MathCollab.Density.hKernel (reflectionSquare w) L (u-v)*
      MathCollab.Density.hKernel (reflectionSquare w) L (v-t))

theorem finite_time_mass (W : Finset ℝ) : (finiteTimeMeasure W).real univ = (W.card:ℝ) := by
  have hh := finite_time_integral W (fun _ => (1:ℝ))
  simpa only [integral_const,smul_eq_mul,mul_one,Finset.sum_const,nsmul_eq_mul] using hh

/-- The atomic cubic is the literal ordered triple sum, including all
repeated indices. No diagonal or short difference is removed. -/
theorem finite_cubic_integral (W : Finset ℝ) {K : ℝ → ℂ} (hK : Measurable K)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ s, ‖K s‖ ≤ B) :
    kernelCubic (finiteTimeMeasure W) K = finiteCubic W K := by
  have hi := kernelCubic_integrable (finiteTimeMeasure W) hK hB hb
  have hip (t : ℝ) : Integrable (fun p : ℝ × ℝ => K (t-p.1)*K (p.1-p.2)*K (p.2-t))
      ((finiteTimeMeasure W).prod (finiteTimeMeasure W)) := by
    apply (integrable_const (B^3)).mono' (by fun_prop)
    filter_upwards with p
    simp only [norm_mul]
    calc
      _ ≤ B*B*B := by gcongr <;> exact hb _
      _ = _ := by ring
  rw [kernelCubic,tripleMeasure,integral_prod _ hi]
  simp_rw [integral_prod _ (hip _),finite_time_integral]
  rfl

end Montgomery.RationalMoment
