module
public import GuthMaynard.Improvement.RatioFourierBridge
public import GuthMaynard.Improvement.OrdinaryFourierMoments

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped FourierTransform
namespace GuthMaynard.Improvement

/-- Measurable compact ratio input, equal to the literal Fourier magnitude
on the selected interval. No smoothness is required or asserted. -/
def ratioFourierInput (μ : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ :=
  (Icc a b).indicator (fun v => ‖𝓕 (fun t => (μ t : ℂ)) (mellinFrequency v)‖)

theorem ratioFourierInput_measurable {μ : ℝ → ℝ} (h1 : Integrable μ) (a b : ℝ) :
    Measurable (ratioFourierInput μ a b) := by
  have hc : Continuous (𝓕 (fun t => (μ t : ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (Complex.ofRealCLM.integrable_comp h1)
  exact ((hc.measurable.norm).comp (by unfold mellinFrequency; fun_prop)).indicator
    measurableSet_Icc

theorem ratioFourierInput_nonneg (μ : ℝ → ℝ) (a b v : ℝ) :
    0 ≤ ratioFourierInput μ a b v := by
  unfold ratioFourierInput
  exact indicator_nonneg (fun _ _ => norm_nonneg _) _

theorem ratioFourierInput_on {μ : ℝ → ℝ} {a b v : ℝ} (hv : v ∈ Icc a b) :
    ratioFourierInput μ a b v = ‖𝓕 (fun t => (μ t : ℂ)) (mellinFrequency v)‖ :=
  indicator_of_mem hv _

theorem ratioFourierInput_off {μ : ℝ → ℝ} {a b v : ℝ} (hv : v ∉ Icc a b) :
    ratioFourierInput μ a b v = 0 := indicator_of_notMem hv _

/-- Every positive ordinary Fourier moment transfers through the compact
logarithmic coordinate with its measurable mask exactly retained. -/
theorem ratioFourierInput_masked_moment {μ : ℝ → ℝ} {a b : ℝ} {A : Set ℝ}
    {n : ℕ} (hn : n ≠ 0) (ha : 0 < a) (hab : a ≤ b)
    (hA : MeasurableSet A)
    (hF : Integrable (fun ξ => ‖𝓕 (fun t => (μ t : ℂ)) ξ‖^n)) :
    IntegrableOn (fun v => ratioFourierInput μ a b v^n) (mellinFrequency ⁻¹' A) ∧
    (∫ v in mellinFrequency ⁻¹' A, ratioFourierInput μ a b v^n) ≤
      (2*Real.pi*b)*(∫ ξ in A, ‖𝓕 (fun t => (μ t : ℂ)) ξ‖^n) := by
  let w : ℝ → ℝ := (Icc a b).indicator (fun _ => 1)
  have hw : Measurable w := measurable_const.indicator measurableSet_Icc
  have hw0 : ∀ v, 0 ≤ w v := by intro v; exact indicator_nonneg (by intros; norm_num) _
  have hw1 : ∀ v, w v ≤ 1 := by intro v; by_cases hv : v ∈ Icc a b <;> simp [w,hv]
  have hws : ∀ v, v ∉ Icc a b → w v = 0 := by intro v hv; simp [w,hv]
  have hp := mellin_compact_mask_integral ha hab (by norm_num : (0:ℝ) ≤ 1)
    hw hw0 hw1 hws hA hF (fun ξ => pow_nonneg (norm_nonneg _) _)
  have hpre : MeasurableSet (mellinFrequency ⁻¹' A) :=
    hA.preimage (by unfold mellinFrequency; fun_prop)
  have he : (fun v => w v*A.indicator (fun ξ => ‖𝓕 (fun t => (μ t : ℂ)) ξ‖^n)
      (mellinFrequency v)) =
      (mellinFrequency ⁻¹' A).indicator (fun v => ratioFourierInput μ a b v^n) := by
    funext v
    by_cases hv : v ∈ Icc a b <;> by_cases hm : mellinFrequency v ∈ A <;>
      simp [w,ratioFourierInput,hv,hm,hn]
  rw [he] at hp
  refine ⟨(integrable_indicator_iff hpre).mp hp.1, ?_⟩
  rw [integral_indicator hpre] at hp
  convert hp.2 using 1
  ring

/-- Actual L2 input, including a zero or degenerate ratio interval. -/
theorem ratioFourierInput_square_integrable {μ : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (h1 : Integrable μ)
    (h2 : Integrable (fun t => μ t^2)) :
    Integrable (fun v => ratioFourierInput μ a b v^2) := by
  simpa using (ratioFourierInput_masked_moment (by norm_num : (2:ℕ) ≠ 0)
    ha hab MeasurableSet.univ (ordinary_real_fourier_square_integrable h1 h2)).1

theorem ratioFourierInput_fourth_integrable {μ : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (h0 : ∀ t, 0 ≤ μ t) (h1 : Integrable μ)
    (h2 : Integrable (fun t => μ t^2)) :
    Integrable (fun v => ratioFourierInput μ a b v^4) := by
  simpa using (ratioFourierInput_masked_moment (by norm_num : (4:ℕ) ≠ 0)
    ha hab MeasurableSet.univ (ordinary_real_fourier_fourth_integrable h0 h1 h2)).1

/-- Mask-sensitive second moment for ordinary input; A is not enlarged. -/
theorem ratioFourierInput_masked_square {μ : ℝ → ℝ} {a b : ℝ} {A : Set ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hA : MeasurableSet A)
    (h1 : Integrable μ) (h2 : Integrable (fun t => μ t^2)) :
    (∫ v in mellinFrequency ⁻¹' A, ratioFourierInput μ a b v^2) ≤
      (2*Real.pi*b)*(∫ ξ in A, ‖𝓕 (fun t => (μ t : ℂ)) ξ‖^2) :=
  (ratioFourierInput_masked_moment (by norm_num) ha hab hA
    (ordinary_real_fourier_square_integrable h1 h2)).2

/-- The analogous fourth moment retains exactly the same Fourier mask. -/
theorem ratioFourierInput_masked_fourth {μ : ℝ → ℝ} {a b : ℝ} {A : Set ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hA : MeasurableSet A)
    (h0 : ∀ t, 0 ≤ μ t) (h1 : Integrable μ) (h2 : Integrable (fun t => μ t^2)) :
    (∫ v in mellinFrequency ⁻¹' A, ratioFourierInput μ a b v^4) ≤
      (2*Real.pi*b)*(∫ ξ in A, ‖𝓕 (fun t => (μ t : ℂ)) ξ‖^4) :=
  (ratioFourierInput_masked_moment (by norm_num) ha hab hA
    (ordinary_real_fourier_fourth_integrable h0 h1 h2)).2

/-- The global second moment has the original density's exact L2 budget. -/
theorem ratioFourierInput_integral_square {μ : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (h1 : Integrable μ)
    (h2 : Integrable (fun t => μ t^2)) :
    (∫ v, ratioFourierInput μ a b v^2) ≤ (2*Real.pi*b)*(∫ t, μ t^2) := by
  simpa [ordinary_real_fourier_integral_square h1 h2] using
    ratioFourierInput_masked_square ha hab MeasurableSet.univ h1 h2

/-- Global fourth moment with the ordinary homogeneous mass/L2 budget. -/
theorem ratioFourierInput_integral_fourth {μ : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (h0 : ∀ t, 0 ≤ μ t) (h1 : Integrable μ)
    (h2 : Integrable (fun t => μ t^2)) :
    (∫ v, ratioFourierInput μ a b v^4) ≤
      (2*Real.pi*b)*((∫ t, μ t)^2*(∫ t, μ t^2)) := by
  have hp := ratioFourierInput_masked_fourth ha hab MeasurableSet.univ h0 h1 h2
  simp only [preimage_univ,setIntegral_univ] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left
    (ordinary_real_fourier_integral_fourth h0 h1 h2) (by have hb := ha.trans_le hab; positivity))

/-- Pointwise mass control includes the cut-off region and zero input. -/
theorem ratioFourierInput_le_mass {μ : ℝ → ℝ} (h0 : ∀ t, 0 ≤ μ t)
    (a b v : ℝ) : ratioFourierInput μ a b v ≤ ∫ t, μ t := by
  by_cases hv : v ∈ Icc a b
  · rw [ratioFourierInput_on hv]
    exact fourier_nonneg_mass h0 _
  · rw [ratioFourierInput_off hv]
    exact integral_nonneg h0

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.ratioFourierInput_measurable
#print axioms GuthMaynard.Improvement.ratioFourierInput_nonneg
#print axioms GuthMaynard.Improvement.ratioFourierInput_on
#print axioms GuthMaynard.Improvement.ratioFourierInput_off
#print axioms GuthMaynard.Improvement.ratioFourierInput_masked_moment
#print axioms GuthMaynard.Improvement.ratioFourierInput_square_integrable
#print axioms GuthMaynard.Improvement.ratioFourierInput_fourth_integrable
#print axioms GuthMaynard.Improvement.ratioFourierInput_masked_square
#print axioms GuthMaynard.Improvement.ratioFourierInput_masked_fourth

#print axioms GuthMaynard.Improvement.ratioFourierInput_integral_square
#print axioms GuthMaynard.Improvement.ratioFourierInput_integral_fourth
#print axioms GuthMaynard.Improvement.ratioFourierInput_le_mass
