import GuthMaynard.Improvement.OperatorCentered
import GuthMaynard.Improvement.OperatorTraceConvergence
set_option autoImplicit false
noncomputable section
open MeasureTheory InnerProductSpace
open scoped InnerProductSpace
namespace GuthMaynard.Improvement

/-- Independently defined mixed scalar kernel cycle. -/
def kernelMixed (μ : Measure ℝ) (C K : ℝ → ℂ) : ℂ :=
  ∫ t : Triple, C (t.1-t.2.1)*K (t.2.1-t.2.2)*K (t.2.2-t.1) ∂tripleMeasure μ

/-- Actual mixed nuclear cycle; the product need not be self-adjoint. -/
theorem operatorIntegral_mixed_cycle {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [Countable ι]
    (ν₀ ν₁ : Measure ℝ) (b : HilbertBasis ι ℂ E)
    {x₀ y₀ x₁ y₁ : ℝ → E}
    (hx₀ : AEStronglyMeasurable x₀ ν₀) (hy₀ : AEStronglyMeasurable y₀ ν₀)
    (hi₀ : Integrable (fun a => ‖x₀ a‖*‖y₀ a‖) ν₀)
    (hx₁ : AEStronglyMeasurable x₁ ν₁) (hy₁ : AEStronglyMeasurable y₁ ν₁)
    (hi₁ : Integrable (fun a => ‖x₁ a‖*‖y₁ a‖) ν₁) :
    operatorDiagonalTrace b (operatorIntegral ν₀ x₀ y₀*(operatorIntegral ν₁ x₁ y₁)^2) =
      ∫ a, ∫ c, ∫ d, inner ℂ (y₀ a) (x₁ c)*inner ℂ (y₁ c) (x₁ d)*
        inner ℂ (y₁ d) (x₀ a) ∂ν₁ ∂ν₁ ∂ν₀ := by
  rw [operatorIntegral_trace_right ν₀ b _ hx₀ hy₀ hi₀]
  simp only [pow_two,mul_apply_eq_comp]
  apply integral_congr_ae
  filter_upwards with a
  rw [operatorIntegral_pairing ν₁ hx₁ hy₁ hi₁]
  apply integral_congr_ae
  filter_upwards with c
  rw [operatorIntegral_pairing ν₁ hx₁ hy₁ hi₁,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with d
  exact (mul_assoc _ _ _).symm

def mixedFrequencyIntegrand (A B : ℝ → ℂ) (f g : ℝ → ℝ) (x t : Triple) : ℂ :=
  (A x.1*phase ((t.1-t.2.1)*f x.1))*
  (B x.2.1*phase ((t.2.1-t.2.2)*g x.2.1))*
  (B x.2.2*phase ((t.2.2-t.1)*g x.2.2))

theorem mixedFrequencyIntegrand_measurable {A B : ℝ → ℂ} {f g : ℝ → ℝ}
    (hA : Measurable A) (hB : Measurable B) (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun p : Triple × Triple => mixedFrequencyIntegrand A B f g p.1 p.2) := by
  unfold mixedFrequencyIntegrand
  have hp := phase_measurable
  fun_prop

theorem mixedFrequencyIntegrand_integrable (μ ν₀ ν₁ : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁]
    {A B : ℝ → ℂ} {f g : ℝ → ℝ} {B₀ B₁ : ℝ}
    (hA : Measurable A) (hB : Measurable B) (hf : Measurable f) (hg : Measurable g)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hbA : ∀ x, ‖A x‖ ≤ B₀) (hbB : ∀ x, ‖B x‖ ≤ B₁) :
    Integrable (fun p : Triple × Triple => mixedFrequencyIntegrand A B f g p.1 p.2)
      ((ν₀.prod (ν₁.prod ν₁)).prod (tripleMeasure μ)) := by
  let : IsFiniteMeasure (tripleMeasure μ) := by unfold tripleMeasure; infer_instance
  apply (integrable_const (B₀*B₁^2)).mono'
    (mixedFrequencyIntegrand_measurable hA hB hf hg).aestronglyMeasurable
  filter_upwards with p
  simp only [mixedFrequencyIntegrand,norm_mul,phase_norm,mul_one]
  calc
    _ ≤ B₀*B₁*B₁ := mul_le_mul (mul_le_mul (hbA _) (hbB _) (norm_nonneg _) hB₀)
      (hbB _) (norm_nonneg _) (mul_nonneg hB₀ hB₁)
    _ = _ := by ring

/-- Time integration of the absolute-integrable six-variable mixed integrand. -/
theorem mixedFrequencyIntegrand_time_integral (μ : Measure ℝ) [SFinite μ]
    (A B : ℝ → ℂ) (f g : ℝ → ℝ) (x : Triple) :
    (∫ t, mixedFrequencyIntegrand A B f g x t ∂tripleMeasure μ) =
      (A x.1*B x.2.1*B x.2.2)*
        (measureFourier μ (g x.2.2-f x.1)*measureFourier μ (f x.1-g x.2.1)*
          measureFourier μ (g x.2.1-g x.2.2)) := by
  have hid : ∀ t, mixedFrequencyIntegrand A B f g x t = (A x.1*B x.2.1*B x.2.2)*
      (phase (-(g x.2.2-f x.1)*t.1)*phase (-(f x.1-g x.2.1)*t.2.1)*
        phase (-(g x.2.1-g x.2.2)*t.2.2)) := by
    intro t
    unfold mixedFrequencyIntegrand
    have hp : phase ((t.1-t.2.1)*f x.1)*phase ((t.2.1-t.2.2)*g x.2.1)*
        phase ((t.2.2-t.1)*g x.2.2) =
      phase (-(g x.2.2-f x.1)*t.1)*phase (-(f x.1-g x.2.1)*t.2.1)*
        phase (-(g x.2.1-g x.2.2)*t.2.2) := by
      rw [← phase_add,← phase_add,← phase_add,← phase_add]
      congr 1
      ring
    calc
      _ = (A x.1*B x.2.1*B x.2.2)*
        (phase ((t.1-t.2.1)*f x.1)*phase ((t.2.1-t.2.2)*g x.2.1)*phase ((t.2.2-t.1)*g x.2.2)) := by ring
      _ = _ := by rw [hp]
  simp_rw [hid]
  rw [integral_const_mul,triple_product_integral μ
    (fun t => phase (-(g x.2.2-f x.1)*t)) (fun t => phase (-(f x.1-g x.2.1)*t))
    (fun t => phase (-(g x.2.1-g x.2.2)*t))]
  rfl

/-- Actual mixed scalar Fourier identity, with Fubini justified by finite
measures and bounded measurable amplitudes. -/
theorem frequencyKernel_mixed (μ ν₀ ν₁ : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁]
    {A B : ℝ → ℂ} {f g : ℝ → ℝ} {B₀ B₁ : ℝ}
    (hA : Measurable A) (hB : Measurable B) (hf : Measurable f) (hg : Measurable g)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hbA : ∀ x, ‖A x‖ ≤ B₀) (hbB : ∀ x, ‖B x‖ ≤ B₁) :
    kernelMixed μ (frequencyKernel ν₀ A f) (frequencyKernel ν₁ B g) =
      ∫ x : Triple, (A x.1*B x.2.1*B x.2.2)*
        (measureFourier μ (g x.2.2-f x.1)*measureFourier μ (f x.1-g x.2.1)*
          measureFourier μ (g x.2.1-g x.2.2)) ∂ν₀.prod (ν₁.prod ν₁) := by
  let : IsFiniteMeasure (tripleMeasure μ) := by unfold tripleMeasure; infer_instance
  have hswap := integral_integral_swap (μ := ν₀.prod (ν₁.prod ν₁)) (ν := tripleMeasure μ)
    (f := fun x t => mixedFrequencyIntegrand A B f g x t)
    (mixedFrequencyIntegrand_integrable μ ν₀ ν₁ hA hB hf hg hB₀ hB₁ hbA hbB)
  have hx (t : Triple) : (∫ x, mixedFrequencyIntegrand A B f g x t ∂ν₀.prod (ν₁.prod ν₁)) =
      frequencyKernel ν₀ A f (t.1-t.2.1)*frequencyKernel ν₁ B g (t.2.1-t.2.2)*
        frequencyKernel ν₁ B g (t.2.2-t.1) := by
    have hh := integral_prod_mul (μ := ν₀) (ν := ν₁.prod ν₁)
      (fun x => A x*phase ((t.1-t.2.1)*f x))
      (fun x : ℝ × ℝ => (B x.1*phase ((t.2.1-t.2.2)*g x.1))*(B x.2*phase ((t.2.2-t.1)*g x.2)))
    rw [integral_prod_mul (μ := ν₁) (ν := ν₁)
      (fun y => B y*phase ((t.2.1-t.2.2)*g y))
      (fun z => B z*phase ((t.2.2-t.1)*g z))] at hh
    simpa only [mixedFrequencyIntegrand,frequencyKernel,mul_assoc] using hh
  simp_rw [hx,mixedFrequencyIntegrand_time_integral] at hswap
  exact hswap.symm

/-- The actual ambient Hilbert-basis mixed trace equals the independently
specified time-kernel cycle. No operator commutation or positivity is assumed. -/
theorem operator_frequency_mixed (μ ν₀ ν₁ : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁]
    {A B : ℝ → ℂ} {f g : ℝ → ℝ} {B₀ B₁ : ℝ}
    (hA : Measurable A) (hB : Measurable B) (hf : Measurable f) (hg : Measurable g)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hbA : ∀ x, ‖A x‖ ≤ B₀) (hbB : ∀ x, ‖B x‖ ≤ B₁)
    {ι : Type*} [Countable ι] (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) :
    operatorDiagonalTrace b (operatorFrequency μ ν₀ A f*(operatorFrequency μ ν₁ B g)^2) =
      kernelMixed μ (frequencyKernel ν₀ A f) (frequencyKernel ν₁ B g) := by
  let : IsFiniteMeasure (tripleMeasure μ) := by unfold tripleMeasure; infer_instance
  obtain ⟨hx₀,hy₀,hi₀⟩ := operator_frequency_inputs μ ν₀ hA hf hB₀ hbA
  obtain ⟨hx₁,hy₁,hi₁⟩ := operator_frequency_inputs μ ν₁ hB hg hB₁ hbB
  rw [operatorFrequency,operatorFrequency,
    operatorIntegral_mixed_cycle ν₀ ν₁ b hx₀ hy₀ hi₀ hx₁ hy₁ hi₁,
    frequencyKernel_mixed μ ν₀ ν₁ hA hB hf hg hB₀ hB₁ hbA hbB]
  let Q : Triple → ℂ := fun x => (A x.1*B x.2.1*B x.2.2)*
    (measureFourier μ (g x.2.2-f x.1)*measureFourier μ (f x.1-g x.2.1)*
      measureFourier μ (g x.2.1-g x.2.2))
  have hQ : Integrable Q (ν₀.prod (ν₁.prod ν₁)) := by
    have hi := (mixedFrequencyIntegrand_integrable μ ν₀ ν₁ hA hB hf hg hB₀ hB₁ hbA hbB).integral_prod_left
    simpa only [mixedFrequencyIntegrand_time_integral] using hi
  change _ = ∫ x, Q x ∂ν₀.prod (ν₁.prod ν₁)
  rw [integral_prod _ hQ]
  apply integral_congr_ae
  filter_upwards [hQ.prod_right_ae] with x hxQ
  rw [integral_prod _ hxQ]
  apply integral_congr_ae
  filter_upwards with y
  apply integral_congr_ae
  filter_upwards with z
  simp only [inner_smul_right,operator_phase_pairing,Q]
  ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.operatorIntegral_mixed_cycle
#print axioms GuthMaynard.Improvement.mixedFrequencyIntegrand_measurable
#print axioms GuthMaynard.Improvement.mixedFrequencyIntegrand_integrable
#print axioms GuthMaynard.Improvement.mixedFrequencyIntegrand_time_integral
#print axioms GuthMaynard.Improvement.frequencyKernel_mixed
#print axioms GuthMaynard.Improvement.operator_frequency_mixed
