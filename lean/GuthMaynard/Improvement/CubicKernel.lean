import GuthMaynard.Improvement.SecondKernelError
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace GuthMaynard.Improvement

abbrev Triple := ℝ × (ℝ × ℝ)
def tripleMeasure (μ : Measure ℝ) : Measure Triple := μ.prod (μ.prod μ)
def kernelCubic (μ : Measure ℝ) (K : ℝ → ℂ) : ℂ :=
  ∫ t, K (t.1-t.2.1)*K (t.2.1-t.2.2)*K (t.2.2-t.1) ∂tripleMeasure μ
def measureFourier (μ : Measure ℝ) (u : ℝ) : ℂ := ∫ t, phase (-u*t) ∂μ
def frequencyKernel (ν : Measure ℝ) (A : ℝ → ℂ) (f : ℝ → ℝ) (s : ℝ) : ℂ :=
  ∫ x, A x*phase (s*f x) ∂ν

theorem phase_measurable : Measurable phase := by unfold phase; fun_prop

theorem triple_product_integral (μ : Measure ℝ) [SFinite μ] (f g h : ℝ → ℂ) :
    (∫ t : Triple, f t.1*g t.2.1*h t.2.2 ∂tripleMeasure μ) =
      (∫ x, f x ∂μ)*(∫ x, g x ∂μ)*(∫ x, h x ∂μ) := by
  simp_rw [mul_assoc]
  rw [tripleMeasure, integral_prod_mul f (fun z : ℝ × ℝ => g z.1*h z.2),integral_prod_mul g h]

/-- The exact six-variable integrand before Fubini. -/
def cubicIntegrand (A : ℝ → ℂ) (f : ℝ → ℝ) (x t : Triple) : ℂ :=
  (A x.1*phase ((t.1-t.2.1)*f x.1))*
  (A x.2.1*phase ((t.2.1-t.2.2)*f x.2.1))*
  (A x.2.2*phase ((t.2.2-t.1)*f x.2.2))

theorem cubicIntegrand_measurable {A : ℝ → ℂ} {f : ℝ → ℝ}
    (hA : Measurable A) (hf : Measurable f) :
    Measurable (fun p : Triple × Triple => cubicIntegrand A f p.1 p.2) := by
  unfold cubicIntegrand
  have hp := phase_measurable
  fun_prop

/-- Absolute six-variable integrability follows from finite measures and
bounded amplitude, not an assumed interchange of divergent integrals. -/
theorem cubicIntegrand_integrable (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {A : ℝ → ℂ} {f : ℝ → ℝ} {B : ℝ} (hA : Measurable A) (hf : Measurable f)
    (hB : 0 ≤ B) (hb : ∀ x, ‖A x‖ ≤ B) :
    Integrable (fun p : Triple × Triple => cubicIntegrand A f p.1 p.2)
      ((tripleMeasure ν).prod (tripleMeasure μ)) := by
  let : IsFiniteMeasure (tripleMeasure μ) := by unfold tripleMeasure; infer_instance
  let : IsFiniteMeasure (tripleMeasure ν) := by unfold tripleMeasure; infer_instance
  apply (integrable_const (B^3)).mono' (cubicIntegrand_measurable hA hf).aestronglyMeasurable
  filter_upwards with p
  simp only [cubicIntegrand,norm_mul,phase_norm,mul_one]
  calc
    _ ≤ B*B*B := mul_le_mul (mul_le_mul (hb _) (hb _) (norm_nonneg _) hB) (hb _) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem cubicIntegrand_time_integral (μ : Measure ℝ) [SFinite μ]
    (A : ℝ → ℂ) (f : ℝ → ℝ) (x : Triple) :
    (∫ t, cubicIntegrand A f x t ∂tripleMeasure μ) =
      (A x.1*A x.2.1*A x.2.2)*
        (measureFourier μ (f x.2.2-f x.1)*measureFourier μ (f x.1-f x.2.1)*
          measureFourier μ (f x.2.1-f x.2.2)) := by
  have hid : ∀ t, cubicIntegrand A f x t = (A x.1*A x.2.1*A x.2.2)*
      (phase (-(f x.2.2-f x.1)*t.1)*phase (-(f x.1-f x.2.1)*t.2.1)*
        phase (-(f x.2.1-f x.2.2)*t.2.2)) := by
    intro t
    unfold cubicIntegrand
    have hp : phase ((t.1-t.2.1)*f x.1)*phase ((t.2.1-t.2.2)*f x.2.1)*
        phase ((t.2.2-t.1)*f x.2.2) =
      phase (-(f x.2.2-f x.1)*t.1)*phase (-(f x.1-f x.2.1)*t.2.1)*
        phase (-(f x.2.1-f x.2.2)*t.2.2) := by
      rw [← phase_add,← phase_add,← phase_add,← phase_add]
      congr 1
      ring
    calc
      _ = (A x.1*A x.2.1*A x.2.2)*
        (phase ((t.1-t.2.1)*f x.1)*phase ((t.2.1-t.2.2)*f x.2.1)*phase ((t.2.2-t.1)*f x.2.2)) := by ring
      _ = _ := by rw [hp]
  simp_rw [hid]
  rw [integral_const_mul, triple_product_integral μ
    (fun t => phase (-(f x.2.2-f x.1)*t)) (fun t => phase (-(f x.1-f x.2.1)*t))
    (fun t => phase (-(f x.2.1-f x.2.2)*t))]
  rfl

/-- Exact cubic Fourier formula for the actual integral kernel. This is a
kernel integral identity; identifying it with an operator trace is separate. -/
theorem frequencyKernel_cubic (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {A : ℝ → ℂ} {f : ℝ → ℝ} {B : ℝ} (hA : Measurable A) (hf : Measurable f)
    (hB : 0 ≤ B) (hb : ∀ x, ‖A x‖ ≤ B) :
    kernelCubic μ (frequencyKernel ν A f) =
      ∫ x : Triple, (A x.1*A x.2.1*A x.2.2)*
        (measureFourier μ (f x.2.2-f x.1)*measureFourier μ (f x.1-f x.2.1)*
          measureFourier μ (f x.2.1-f x.2.2)) ∂tripleMeasure ν := by
  let : IsFiniteMeasure (tripleMeasure μ) := by unfold tripleMeasure; infer_instance
  let : IsFiniteMeasure (tripleMeasure ν) := by unfold tripleMeasure; infer_instance
  have hswap := integral_integral_swap (μ := tripleMeasure ν) (ν := tripleMeasure μ)
    (f := fun x t => cubicIntegrand A f x t) (cubicIntegrand_integrable μ ν hA hf hB hb)
  have hx : ∀ t : Triple, (∫ x, cubicIntegrand A f x t ∂tripleMeasure ν) =
      frequencyKernel ν A f (t.1-t.2.1)*frequencyKernel ν A f (t.2.1-t.2.2)*
        frequencyKernel ν A f (t.2.2-t.1) := by
    intro t
    exact triple_product_integral ν (fun x => A x*phase ((t.1-t.2.1)*f x))
      (fun x => A x*phase ((t.2.1-t.2.2)*f x)) (fun x => A x*phase ((t.2.2-t.1)*f x))
  simp_rw [hx,cubicIntegrand_time_integral] at hswap
  exact hswap.symm

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.phase_measurable
#print axioms GuthMaynard.Improvement.triple_product_integral
#print axioms GuthMaynard.Improvement.cubicIntegrand_measurable
#print axioms GuthMaynard.Improvement.cubicIntegrand_integrable
#print axioms GuthMaynard.Improvement.cubicIntegrand_time_integral
#print axioms GuthMaynard.Improvement.frequencyKernel_cubic
