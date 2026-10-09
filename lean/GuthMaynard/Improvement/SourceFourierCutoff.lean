module
public import GuthMaynard.Improvement.OrdinaryFourierMoments
public import GuthMaynard.Improvement.RatioFourierBridge

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped FourierTransform ComplexConjugate
namespace GuthMaynard.Improvement

def sourceFourierSet (μ : ℝ → ℝ) (Λ : ℝ) : Set ℝ :=
  {ξ | Λ < ‖𝓕 (fun t => (μ t:ℂ)) ξ‖}
def sourceFourierCut (μ : ℝ → ℝ) (Λ : ℝ) : ℝ → ℂ :=
  (sourceFourierSet μ Λ).indicator (𝓕 (fun t => (μ t:ℂ)))
def sourceFourierMass (μ : ℝ → ℝ) (Λ : ℝ) : ℝ :=
  ∫ ξ in sourceFourierSet μ Λ, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^2
def sourceFourierSignal (μ : ℝ → ℝ) (Λ : ℝ) : ℝ → ℂ := 𝓕⁻ (sourceFourierCut μ Λ)

theorem sourceFourierSet_measurable {μ : ℝ → ℝ} (h1 : Integrable μ) (Λ : ℝ) :
    MeasurableSet (sourceFourierSet μ Λ) := by
  have hc : Continuous (𝓕 (fun t => (μ t:ℂ))) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ (Complex.ofRealCLM.integrable_comp h1)
  exact measurableSet_lt measurable_const hc.measurable.norm

theorem sourceFourierCut_square {μ : ℝ → ℝ} (Λ : ℝ) :
    (fun ξ => ‖sourceFourierCut μ Λ ξ‖^2) =
      (sourceFourierSet μ Λ).indicator (fun ξ => ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^2) := by
  funext ξ
  by_cases hξ : ξ ∈ sourceFourierSet μ Λ <;> simp [sourceFourierCut,hξ]

/-- The actual exceptional frequency cutoff is both L1 and L2. -/
theorem sourceFourierCut_integrability {μ : ℝ → ℝ} (h1 : Integrable μ)
    (h2 : Integrable (fun t => μ t^2)) {Λ : ℝ} (hΛ : 0 < Λ) :
    Integrable (sourceFourierCut μ Λ) ∧ MemLp (sourceFourierCut μ Λ) 2 ∧
      (∫ ξ, ‖sourceFourierCut μ Λ ξ‖) ≤ sourceFourierMass μ Λ/Λ := by
  have hA := sourceFourierSet_measurable h1 Λ
  have hc : Continuous (𝓕 (fun t => (μ t:ℂ))) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ (Complex.ofRealCLM.integrable_comp h1)
  have hm : Measurable (sourceFourierCut μ Λ) := hc.measurable.indicator hA
  have hi2 : Integrable (fun ξ => ‖sourceFourierCut μ Λ ξ‖^2) := by
    rw [sourceFourierCut_square]
    exact (ordinary_real_fourier_square_integrable h1 h2).indicator hA
  have hp : ∀ ξ, ‖sourceFourierCut μ Λ ξ‖ ≤ Λ⁻¹*‖sourceFourierCut μ Λ ξ‖^2 := by
    intro ξ
    by_cases hξ : ξ ∈ sourceFourierSet μ Λ
    · have he : sourceFourierCut μ Λ ξ = 𝓕 (fun t => (μ t:ℂ)) ξ := indicator_of_mem hξ _
      rw [he]
      have hval : Λ < ‖𝓕 (fun t => (μ t:ℂ)) ξ‖ := hξ
      rw [inv_mul_eq_div]
      apply (le_div_iff₀ hΛ).mpr
      nlinarith [norm_nonneg (𝓕 (fun t => (μ t:ℂ)) ξ)]
    · simp [sourceFourierCut,hξ]
  have hi1 : Integrable (sourceFourierCut μ Λ) := (hi2.const_mul Λ⁻¹).mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall hp)
  refine ⟨hi1,(memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr hi2,?_⟩
  calc
    _ ≤ ∫ ξ, Λ⁻¹*‖sourceFourierCut μ Λ ξ‖^2 := integral_mono hi1.norm (hi2.const_mul _) hp
    _ = _ := by
      rw [integral_const_mul,sourceFourierCut_square,integral_indicator hA]
      unfold sourceFourierMass
      ring

/-- The exceptional set retains the literal first Fourier moment. -/
theorem sourceFourierCut_restricted_l1 {μ : ℝ → ℝ} (h1 : Integrable μ)
    (h2 : Integrable (fun t => μ t^2)) {Λ : ℝ} (hΛ : 0 < Λ) :
    (∫ ξ in sourceFourierSet μ Λ, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖) ≤
      sourceFourierMass μ Λ/Λ := by
  have he : (fun ξ => ‖sourceFourierCut μ Λ ξ‖) =
      (sourceFourierSet μ Λ).indicator (fun ξ => ‖𝓕 (fun t => (μ t:ℂ)) ξ‖) := by
    funext ξ
    by_cases hξ : ξ ∈ sourceFourierSet μ Λ <;> simp [sourceFourierCut,hξ]
  have hb := (sourceFourierCut_integrability h1 h2 hΛ).2.2
  rwa [he,integral_indicator (sourceFourierSet_measurable h1 Λ)] at hb

/-- Literal inverse Plancherel on L1/L2, obtained from the forward L2
compatibility by reflection. No L1 premise on the inverse transform. -/
theorem ordinary_inverse_fourier_l2 {f : ℝ → ℂ} (h1 : Integrable f) (h2 : MemLp f 2) :
    MemLp (𝓕⁻ f) 2 ∧ (∫ x, ‖𝓕⁻ f x‖^2) = ∫ ξ, ‖f ξ‖^2 := by
  have hn1 : Integrable (fun x => f (-x)) := by simpa using (integrable_comp_mul_left_iff _ (by norm_num : (-1:ℝ) ≠ 0)).mpr h1
  have hn2i : Integrable (fun x => ‖f (-x)‖^2) := by
    have hi := (memLp_two_iff_integrable_sq_norm h2.aestronglyMeasurable).mp h2
    simpa using (integrable_comp_mul_left_iff _ (by norm_num : (-1:ℝ) ≠ 0)).mpr hi
  have hn2 : MemLp (fun x => f (-x)) 2 := (memLp_two_iff_integrable_sq_norm hn1.aestronglyMeasurable).mpr hn2i
  rw [Real.fourierInv_eq_fourier_comp_neg]
  refine ⟨ordinary_fourier_memLp hn1 hn2,?_⟩
  rw [ordinary_fourier_integral_sq hn1 hn2]
  simpa using Measure.integral_comp_mul_left (fun ξ => ‖f ξ‖^2) (-1)

theorem sourceFourierSignal_l2 {μ : ℝ → ℝ} (h1 : Integrable μ)
    (h2 : Integrable (fun t => μ t^2)) {Λ : ℝ} (hΛ : 0 < Λ) :
    MemLp (sourceFourierSignal μ Λ) 2 ∧
      (∫ t, ‖sourceFourierSignal μ Λ t‖^2) = sourceFourierMass μ Λ := by
  obtain ⟨hi,hp,_⟩ := sourceFourierCut_integrability h1 h2 hΛ
  obtain ⟨hg,he⟩ := ordinary_inverse_fourier_l2 hi hp
  refine ⟨hg,?_⟩
  rw [sourceFourierSignal,he,sourceFourierCut_square,integral_indicator (sourceFourierSet_measurable h1 Λ)]
  rfl

theorem sourceFourierSignal_bound {μ : ℝ → ℝ} (h1 : Integrable μ)
    (h2 : Integrable (fun t => μ t^2)) {Λ : ℝ} (hΛ : 0 < Λ) (t : ℝ) :
    ‖sourceFourierSignal μ Λ t‖ ≤ sourceFourierMass μ Λ/Λ := by
  rw [sourceFourierSignal,Real.fourierInv_eq_fourier_neg]
  exact (VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
    (innerₗ ℝ) _ (-t)).trans (sourceFourierCut_integrability h1 h2 hΛ).2.2

/-- Hermitian symmetry of the literal cutoff; the threshold set is symmetric. -/
theorem sourceFourierCut_conj (μ : ℝ → ℝ) (Λ ξ : ℝ) :
    sourceFourierCut μ Λ (-ξ) = conj (sourceFourierCut μ Λ ξ) := by
  have hs : -ξ ∈ sourceFourierSet μ Λ ↔ ξ ∈ sourceFourierSet μ Λ := realDensity_level_symmetry μ Λ ξ
  by_cases hξ : ξ ∈ sourceFourierSet μ Λ
  · simp only [sourceFourierCut,indicator_of_mem hξ,indicator_of_mem (hs.mpr hξ),realDensity_fourier_conj]
  · simp [sourceFourierCut,hξ,hs]

theorem sourceFourierSignal_integral (μ : ℝ → ℝ) (Λ t : ℝ) :
    sourceFourierSignal μ Λ t = ∫ ξ, phase (t*ξ)*sourceFourierCut μ Λ ξ := by
  rw [sourceFourierSignal,Real.fourierInv_eq_fourier_neg,fourier_eq_phase_integral]
  simp only [neg_neg]

/-- The inverse signal is genuinely real-valued, by Hermitian symmetry.
No L1 premise on the time signal is used. -/
theorem sourceFourierSignal_conj (μ : ℝ → ℝ) (Λ t : ℝ) :
    conj (sourceFourierSignal μ Λ t) = sourceFourierSignal μ Λ t := by
  have hp : ∀ s : ℝ, conj (phase s) = phase (-s) := by
    intro s
    unfold phase
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]
    push_cast
    ring
  rw [sourceFourierSignal_integral,← integral_conj]
  calc
    _ = ∫ ξ, phase (t*(-ξ))*sourceFourierCut μ Λ (-ξ) := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [map_mul,hp,sourceFourierCut_conj]
      congr 2
      ring
    _ = ∫ ξ, phase (t*ξ)*sourceFourierCut μ Λ ξ := by
      simpa using Measure.integral_comp_mul_left (fun ξ => phase (t*ξ)*sourceFourierCut μ Λ ξ) (-1)


theorem sourceFourierSignal_real (μ : ℝ → ℝ) (Λ t : ℝ) :
    ((sourceFourierSignal μ Λ t).re : ℂ) = sourceFourierSignal μ Λ t := by
  have hh := congrArg Complex.im (sourceFourierSignal_conj μ Λ t)
  apply Complex.ext
  · simp
  · simp only [Complex.ofReal_im,Complex.conj_im] at hh ⊢
    linarith

/-- The actual ordinary density/signal product is integrable from L2-L2,
without asserting that the signal is L1. -/
theorem sourceFourierSignal_pair_integrable {μ : ℝ → ℝ} (h1 : Integrable μ)
    (h2 : Integrable (fun t => μ t^2)) {Λ : ℝ} (hΛ : 0 < Λ) :
    Integrable (fun t => (μ t:ℂ)*sourceFourierSignal μ Λ t) := by
  have hc1 := Complex.ofRealCLM.integrable_comp h1
  have hm : MemLp (fun t => (μ t:ℂ)) 2 := by
    apply (memLp_two_iff_integrable_sq_norm hc1.aestronglyMeasurable).mpr
    simpa using h2
  exact hm.integrable_mul (sourceFourierSignal_l2 h1 h2 hΛ).1

/-- Exact ordinary pairing with the literal inverse signal. The proof uses
L1 frequency-space Fubini; it does not assume the ordinary Fourier integral
of the possibly non-L1 time signal exists. -/
theorem sourceFourierSignal_pairing {μ : ℝ → ℝ} (h1 : Integrable μ)
    (h2 : Integrable (fun t => μ t^2)) {Λ : ℝ} (hΛ : 0 < Λ) :
    (∫ t, (μ t:ℂ)*sourceFourierSignal μ Λ t) = (sourceFourierMass μ Λ:ℂ) := by
  have hc1 := Complex.ofRealCLM.integrable_comp h1
  have hcut := (sourceFourierCut_integrability h1 h2 hΛ).1
  have hn : Integrable (fun ξ => sourceFourierCut μ Λ (-ξ)) := by
    simpa using (integrable_comp_mul_left_iff _ (by norm_num : (-1:ℝ) ≠ 0)).mpr hcut
  have hpair : (∫ ξ, 𝓕 (fun t => (μ t:ℂ)) ξ * sourceFourierCut μ Λ (-ξ)) =
      ∫ t, (μ t:ℂ)*sourceFourierSignal μ Λ t := by
    simpa [sourceFourierSignal,Real.fourierInv_eq_fourier_comp_neg,Real.fourier_eq,
      VectorFourier.fourierIntegral,real_inner_comm] using
      VectorFourier.integral_bilin_fourierIntegral_eq_flip
        (ContinuousLinearMap.mul ℂ ℂ) (μ := volume) (ν := volume) (L := innerₗ ℝ)
        Real.continuous_fourierChar continuous_inner hc1 hn
  rw [← hpair]
  have he : (fun ξ => 𝓕 (fun t => (μ t:ℂ)) ξ * sourceFourierCut μ Λ (-ξ)) =
      (sourceFourierSet μ Λ).indicator (fun ξ => (‖𝓕 (fun t => (μ t:ℂ)) ξ‖^2:ℂ)) := by
    funext ξ
    rw [sourceFourierCut_conj]
    by_cases hξ : ξ ∈ sourceFourierSet μ Λ
    · simp only [sourceFourierCut,indicator_of_mem hξ,Complex.mul_conj']
    · simp [sourceFourierCut,hξ]
  rw [he,integral_indicator (sourceFourierSet_measurable h1 Λ)]
  norm_cast

/-- Real-valued form of the exact density/signal pairing. -/
theorem sourceFourierSignal_real_pairing {μ : ℝ → ℝ} (h1 : Integrable μ)
    (h2 : Integrable (fun t => μ t^2)) {Λ : ℝ} (hΛ : 0 < Λ) :
    (∫ t, μ t * (sourceFourierSignal μ Λ t).re) = sourceFourierMass μ Λ := by
  have he := congrArg Complex.re (sourceFourierSignal_pairing h1 h2 hΛ)
  have hi := integral_re (sourceFourierSignal_pair_integrable h1 h2 hΛ)
  change (∫ t, ((μ t:ℂ)*sourceFourierSignal μ Λ t).re) =
    (∫ t, (μ t:ℂ)*sourceFourierSignal μ Λ t).re at hi
  simpa using hi.trans he

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.sourceFourierSet_measurable
#print axioms GuthMaynard.Improvement.sourceFourierCut_square
#print axioms GuthMaynard.Improvement.sourceFourierCut_integrability
#print axioms GuthMaynard.Improvement.ordinary_inverse_fourier_l2
#print axioms GuthMaynard.Improvement.sourceFourierSignal_l2
#print axioms GuthMaynard.Improvement.sourceFourierSignal_bound
#print axioms GuthMaynard.Improvement.sourceFourierCut_conj

#print axioms GuthMaynard.Improvement.sourceFourierSignal_integral
#print axioms GuthMaynard.Improvement.sourceFourierSignal_conj
#print axioms GuthMaynard.Improvement.sourceFourierSignal_real
#print axioms GuthMaynard.Improvement.sourceFourierSignal_pair_integrable
#print axioms GuthMaynard.Improvement.sourceFourierSignal_pairing

#print axioms GuthMaynard.Improvement.sourceFourierCut_restricted_l1
#print axioms GuthMaynard.Improvement.sourceFourierSignal_real_pairing
