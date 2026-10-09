import GuthMaynard.Improvement.CubicKernel
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace GuthMaynard.Improvement

def mellinFrequency (x : ℝ) : ℝ := Real.log x/(2*Real.pi)
def retainedAmplitude (a : ℝ → ℂ) (L : ℝ) (S : Finset ℤ) (x : ℝ) : ℂ :=
  (L:ℂ)*(∑ m ∈ S, a x*phase (-L*(m:ℝ)*x))
def retainedPoissonKernel (ν : Measure ℝ) (a : ℝ → ℂ) (L : ℝ) (S : Finset ℤ) : ℝ → ℂ :=
  frequencyKernel ν (retainedAmplitude a L S) mellinFrequency

theorem retainedAmplitude_measurable {a : ℝ → ℂ} (ha : Measurable a) (L : ℝ) (S : Finset ℤ) :
    Measurable (retainedAmplitude a L S) := by
  unfold retainedAmplitude
  have hp := phase_measurable
  fun_prop

theorem retainedAmplitude_bound {a : ℝ → ℂ} {B : ℝ} (_hB : 0 ≤ B)
    (hb : ∀ x, ‖a x‖ ≤ B) (L : ℝ) (S : Finset ℤ) (x : ℝ) :
    ‖retainedAmplitude a L S x‖ ≤ |L| *S.card*B := by
  unfold retainedAmplitude
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ |L| *(∑ m ∈ S, ‖a x*phase (-L*(m:ℝ)*x)‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (abs_nonneg _)
    _ ≤ |L| *(∑ _m ∈ S, B) := by gcongr; simp only [norm_mul,phase_norm,mul_one]; exact hb x
    _ = _ := by simp [mul_assoc]

/-- This is literally the finite sum of the retained Poisson integrals,
with the factor L and both phase normalizations explicit. -/
theorem retainedPoissonKernel_expanded (ν : Measure ℝ) [IsFiniteMeasure ν]
    {a : ℝ → ℂ} {B : ℝ} (ha : Measurable a) (hb : ∀ x, ‖a x‖ ≤ B)
    (L : ℝ) (S : Finset ℤ) (s : ℝ) :
    retainedPoissonKernel ν a L S s = (L:ℂ)*∑ m ∈ S,
      ∫ x, a x*phase (s*mellinFrequency x-L*(m:ℝ)*x) ∂ν := by
  have hp := phase_measurable
  have hf : Measurable mellinFrequency := by unfold mellinFrequency; fun_prop
  have hi : ∀ m ∈ S, Integrable (fun x => a x*phase (s*mellinFrequency x-L*(m:ℝ)*x)) ν := by
    intro m _
    apply (integrable_const B).mono' (by fun_prop)
    filter_upwards with x
    simpa only [norm_mul,phase_norm,mul_one] using hb x
  have hid : ∀ x, retainedAmplitude a L S x*phase (s*mellinFrequency x) =
      (L:ℂ)*∑ m ∈ S, a x*phase (s*mellinFrequency x-L*(m:ℝ)*x) := by
    intro x
    unfold retainedAmplitude
    rw [mul_assoc,Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    rw [mul_assoc,← phase_add]
    congr 2
    ring
  unfold retainedPoissonKernel frequencyKernel
  simp_rw [hid]
  rw [integral_const_mul,integral_finsetSum S hi]

/-- Exact logarithmic normalization on the positive frequency support. -/
theorem mellinFrequency_sub {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    mellinFrequency y-mellinFrequency x = Real.log (y/x)/(2*Real.pi) := by
  rw [Real.log_div hy.ne' hx.ne']
  unfold mellinFrequency
  ring

/-- Exact cubic identity for the retained nonzero Poisson kernel. S is any
finite set (in application, the nonzero truncation). No trace identity or
Poisson truncation estimate is assumed or claimed in this statement. -/
theorem retainedPoissonKernel_cubic (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {a : ℝ → ℂ} {B : ℝ} (ha : Measurable a) (hB : 0 ≤ B) (hb : ∀ x, ‖a x‖ ≤ B)
    (L : ℝ) (S : Finset ℤ) :
    kernelCubic μ (retainedPoissonKernel ν a L S) =
      ∫ x : Triple, (retainedAmplitude a L S x.1*retainedAmplitude a L S x.2.1*
        retainedAmplitude a L S x.2.2)*
        (measureFourier μ (mellinFrequency x.2.2-mellinFrequency x.1)*
          measureFourier μ (mellinFrequency x.1-mellinFrequency x.2.1)*
          measureFourier μ (mellinFrequency x.2.1-mellinFrequency x.2.2)) ∂tripleMeasure ν := by
  exact frequencyKernel_cubic μ ν (retainedAmplitude_measurable ha L S)
    (by unfold mellinFrequency; fun_prop) (by positivity)
    (retainedAmplitude_bound hB hb L S)

/-- Exact expansion retains every mode and the full L^3 prefactor before
any absolute value or discarded-mode estimate is taken. -/
theorem retainedAmplitude_product (a : ℝ → ℂ) (L : ℝ) (S : Finset ℤ) (x : Triple) :
    retainedAmplitude a L S x.1*retainedAmplitude a L S x.2.1*retainedAmplitude a L S x.2.2 =
      (L:ℂ)^3*(∑ m₁ ∈ S, ∑ m₂ ∈ S, ∑ m₃ ∈ S,
        (a x.1*a x.2.1*a x.2.2)*phase (-L*((m₁:ℝ)*x.1+(m₂:ℝ)*x.2.1+(m₃:ℝ)*x.2.2))) := by
  unfold retainedAmplitude
  calc
    _ = (L:ℂ)^3*((∑ m ∈ S, a x.1*phase (-L*(m:ℝ)*x.1))*
      (∑ m ∈ S, a x.2.1*phase (-L*(m:ℝ)*x.2.1))*
      (∑ m ∈ S, a x.2.2*phase (-L*(m:ℝ)*x.2.2))) := by ring
    _ = _ := by
      congr 1
      rw [Finset.sum_mul_sum,Finset.sum_mul]
      simp_rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro m₁ _
      apply Finset.sum_congr rfl
      intro m₂ _
      apply Finset.sum_congr rfl
      intro m₃ _
      have hp : phase (-L*(m₁:ℝ)*x.1)*phase (-L*(m₂:ℝ)*x.2.1)*phase (-L*(m₃:ℝ)*x.2.2) =
          phase (-L*((m₁:ℝ)*x.1+(m₂:ℝ)*x.2.1+(m₃:ℝ)*x.2.2)) := by
        rw [← phase_add,← phase_add]
        congr 1
        ring
      calc
        _ = (a x.1*a x.2.1*a x.2.2)*(phase (-L*(m₁:ℝ)*x.1)*phase (-L*(m₂:ℝ)*x.2.1)*phase (-L*(m₃:ℝ)*x.2.2)) := by ring
        _ = _ := by rw [hp]

/-- Exact 2*pi normalization: the time phase is x^(is) on positive x,
expressed using exp and log without a complex-power branch convention. -/
theorem mellinFrequency_phase (s x : ℝ) :
    phase (s*mellinFrequency x) = Complex.exp (((s*Real.log x:ℝ):ℂ)*Complex.I) := by
  unfold phase mellinFrequency
  have hh : 2*Real.pi*(s*(Real.log x/(2*Real.pi))) = s*Real.log x := by
    field_simp
  rw [hh]

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.retainedAmplitude_measurable
#print axioms GuthMaynard.Improvement.retainedAmplitude_bound
#print axioms GuthMaynard.Improvement.retainedPoissonKernel_cubic

#print axioms GuthMaynard.Improvement.retainedPoissonKernel_expanded
#print axioms GuthMaynard.Improvement.mellinFrequency_sub

#print axioms GuthMaynard.Improvement.retainedAmplitude_product

#print axioms GuthMaynard.Improvement.mellinFrequency_phase
