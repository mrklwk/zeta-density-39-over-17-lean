import GuthMaynard.Improvement.SourceFourierCutoff
import GuthMaynard.Improvement.SecondKernelError
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped FourierTransform Convolution ContDiff SchwartzMap
namespace GuthMaynard.Improvement

/-- Multiplication by an ordinary integrable function and a literal inverse
L1 Fourier integral has the expected convolution transform, pointwise. -/
theorem source_cutoff_fourier_convolution {χ f : ℝ → ℂ}
    (hχ : Integrable χ) (hf : Integrable f) (ξ : ℝ) :
    𝓕 (fun t => χ t * 𝓕⁻ f t) ξ = ∫ η, f η * 𝓕 χ (ξ-η) := by
  let q : ℝ → ℂ := fun t => phase (-ξ*t)*χ t
  have hq : Integrable q := by
    apply hχ.norm.mono' ((show Continuous (fun t : ℝ => phase (-ξ*t)) by
      unfold phase; fun_prop).aestronglyMeasurable.mul hχ.aestronglyMeasurable)
    filter_upwards [] with t
    simp [phase_norm]
  have hn : Integrable (fun η => f (-η)) := by
    simpa using hf.comp_mul_left' (by norm_num : (-1:ℝ) ≠ 0)
  have hpair : (∫ η, 𝓕 q η * f (-η)) = ∫ t, q t * 𝓕⁻ f t := by
    simpa [Real.fourierInv_eq_fourier_comp_neg,Real.fourier_eq,
      VectorFourier.fourierIntegral,real_inner_comm] using
      VectorFourier.integral_bilin_fourierIntegral_eq_flip
        (ContinuousLinearMap.mul ℂ ℂ) (μ := volume) (ν := volume) (L := innerₗ ℝ)
        Real.continuous_fourierChar continuous_inner hq hn
  have hshift : ∀ η, 𝓕 q η = 𝓕 χ (ξ+η) := by
    intro η
    rw [fourier_eq_phase_integral,fourier_eq_phase_integral]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp [q]
    rw [← mul_assoc,← phase_add]
    congr 2
    ring
  calc
    _ = ∫ t, q t * 𝓕⁻ f t := by
      rw [fourier_eq_phase_integral]
      apply integral_congr_ae
      filter_upwards [] with t
      dsimp [q]
      ring
    _ = ∫ η, 𝓕 q η * f (-η) := hpair.symm
    _ = ∫ η, 𝓕 χ (ξ+η) * f (-η) := by simp_rw [hshift]
    _ = ∫ η, 𝓕 χ (ξ-η) * f η := by
      simpa [sub_eq_add_neg] using
        Measure.integral_comp_mul_left (fun η => 𝓕 χ (ξ-η)*f η) (-1)
    _ = _ := by apply integral_congr_ae; filter_upwards [] with η; ring

/-- L1 norm bound for the actual cutoff convolution. -/
theorem source_cutoff_fourier_l1 {χ f : ℝ → ℂ}
    (hχ : Integrable χ) (hf : Integrable f) (hFχ : Integrable (𝓕 χ)) :
    Integrable (𝓕 (fun t => χ t * 𝓕⁻ f t)) ∧
      (∫ ξ, ‖𝓕 (fun t => χ t * 𝓕⁻ f t) ξ‖) ≤
        (∫ ξ, ‖𝓕 χ ξ‖) * (∫ η, ‖f η‖) := by
  have he : 𝓕 (fun t => χ t * 𝓕⁻ f t) = f ⋆[ContinuousLinearMap.mul ℂ ℂ] 𝓕 χ := by
    funext ξ
    exact source_cutoff_fourier_convolution hχ hf ξ
  have hi := hf.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hFχ
  rw [he]
  refine ⟨hi,?_⟩
  have hni := hf.norm.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hFχ.norm
  calc
    _ ≤ ∫ ξ, ((fun η => ‖f η‖) ⋆[ContinuousLinearMap.mul ℝ ℝ] (fun η => ‖𝓕 χ η‖)) ξ := by
      apply integral_mono hi.norm hni
      intro ξ
      simpa [convolution_def,norm_mul] using
        norm_integral_le_integral_norm (fun η => f η * 𝓕 χ (ξ-η))
    _ = _ := by rw [integral_convolution _ hf.norm hFχ.norm]; simp [mul_comm]

/-- Spatial cutoff of the actual exceptional signal: L1, L2 contraction,
and exact retained frequency mass in both Fourier estimates. -/
theorem source_cutoff_signal_bounds {μ : ℝ → ℝ} (h1 : Integrable μ)
    (h2 : Integrable (fun t => μ t^2)) {Λ : ℝ} (hΛ : 0 < Λ)
    {χ : ℝ → ℂ} (hχ : Integrable χ) (hχb : ∀ t, ‖χ t‖ ≤ 1)
    (hFχ : Integrable (𝓕 χ)) :
    Integrable (fun t => χ t * sourceFourierSignal μ Λ t) ∧
    MemLp (fun t => χ t * sourceFourierSignal μ Λ t) 2 ∧
    (∫ t, ‖χ t * sourceFourierSignal μ Λ t‖^2) ≤ sourceFourierMass μ Λ ∧
    Integrable (𝓕 (fun t => χ t * sourceFourierSignal μ Λ t)) ∧
    (∫ ξ, ‖𝓕 (fun t => χ t * sourceFourierSignal μ Λ t) ξ‖) ≤
      (∫ ξ, ‖𝓕 χ ξ‖) * (sourceFourierMass μ Λ/Λ) := by
  obtain ⟨hg,he⟩ := sourceFourierSignal_l2 h1 h2 hΛ
  have hms := hχ.aestronglyMeasurable.mul hg.aestronglyMeasurable
  have hi1 : Integrable (fun t => χ t * sourceFourierSignal μ Λ t) := by
    apply (hχ.norm.mul_const (sourceFourierMass μ Λ/Λ)).mono' hms
    filter_upwards [] with t
    simp only [Pi.mul_apply, norm_mul]
    exact mul_le_mul_of_nonneg_left (sourceFourierSignal_bound h1 h2 hΛ t) (norm_nonneg _)
  have hgi := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hp : ∀ t, ‖χ t * sourceFourierSignal μ Λ t‖^2 ≤ ‖sourceFourierSignal μ Λ t‖^2 := by
    intro t
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_right (hχb t) (norm_nonneg (sourceFourierSignal μ Λ t))
  have hi2 : Integrable (fun t => ‖χ t * sourceFourierSignal μ Λ t‖^2) := by
    apply hgi.mono' (hms.norm.pow 2)
    filter_upwards [] with t
    simpa only [Pi.pow_apply,Pi.mul_apply,Real.norm_eq_abs,abs_pow,abs_norm] using hp t
  obtain ⟨hFi,hFb⟩ := source_cutoff_fourier_l1 hχ
    (sourceFourierCut_integrability h1 h2 hΛ).1 hFχ
  refine ⟨hi1,(memLp_two_iff_integrable_sq_norm hms).mpr hi2,?_,hFi,?_⟩
  · rw [← he]
    exact integral_mono hi2 hgi hp
  · exact hFb.trans (mul_le_mul_of_nonneg_left
      (sourceFourierCut_integrability h1 h2 hΛ).2.2
      (integral_nonneg (fun ξ => norm_nonneg (𝓕 χ ξ))))

/-- Fourier L1 norm is exactly invariant under positive spatial dilation. -/
theorem source_cutoff_scaled_fourier_l1 (χ : ℝ → ℂ) {T : ℝ} (hT : 0 < T) :
    (∫ ξ, ‖𝓕 (fun t => χ (t/T)) ξ‖) = ∫ ξ, ‖𝓕 χ ξ‖ := by
  have hf : scaledModulated χ T 0 = fun t => χ (t/T) := by
    funext t
    simp [scaledModulated,phase]
  have he : ∀ ξ, 𝓕 (fun t => χ (t/T)) ξ = T • 𝓕 χ (T*ξ) := by
    intro ξ
    simpa [hf] using fourier_scaledModulated χ hT 0 ξ
  simp_rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos hT]
  rw [integral_const_mul,Measure.integral_comp_mul_left (fun ξ => ‖𝓕 χ ξ‖) T]
  simp [abs_of_pos hT,ne_of_gt hT]

/-- Smooth compact real cutoffs supply every premise of the ordinary
convolution bounds, uniformly under positive dilation. -/
theorem source_smooth_scaled_cutoff_bounds {μ : ℝ → ℝ} (h1 : Integrable μ)
    (h2 : Integrable (fun t => μ t^2)) {Λ : ℝ} (hΛ : 0 < Λ)
    {χ : ℝ → ℝ} (hχd : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχ0 : ∀ t, 0 ≤ χ t) (hχ1 : ∀ t, χ t ≤ 1) {T : ℝ} (hT : 0 < T) :
    Integrable (fun t => (χ (t/T):ℂ) * sourceFourierSignal μ Λ t) ∧
    MemLp (fun t => (χ (t/T):ℂ) * sourceFourierSignal μ Λ t) 2 ∧
    (∫ t, ‖(χ (t/T):ℂ) * sourceFourierSignal μ Λ t‖^2) ≤ sourceFourierMass μ Λ ∧
    Integrable (𝓕 (fun t => (χ (t/T):ℂ) * sourceFourierSignal μ Λ t)) ∧
    (∫ ξ, ‖𝓕 (fun t => (χ (t/T):ℂ) * sourceFourierSignal μ Λ t) ξ‖) ≤
      (∫ ξ, ‖𝓕 (fun t => (χ t:ℂ)) ξ‖) * (sourceFourierMass μ Λ/Λ) := by
  let ψ : 𝓢(ℝ,ℂ) := (hχc.comp_left
    (show (Complex.ofRealCLM : ℝ → ℂ) 0 = 0 by rfl)).toSchwartzMap
      (show ContDiff ℝ ∞ (Complex.ofRealCLM ∘ χ) by fun_prop)
  have hχi : Integrable (fun t => (χ t:ℂ)) := ψ.integrable
  have hF : Integrable (𝓕 (fun t => (χ t:ℂ))) := by
    simpa only [SchwartzMap.fourier_coe] using (𝓕 ψ).integrable
  have hs : Integrable (fun t => (χ (t/T):ℂ)) := by
    simpa [div_eq_mul_inv,mul_comm] using hχi.comp_mul_left' (inv_ne_zero (ne_of_gt hT))
  have he : (𝓕 (fun t => (χ (t/T):ℂ))) = fun ξ => T • 𝓕 (fun t => (χ t:ℂ)) (T*ξ) := by
    funext ξ
    have hf : scaledModulated (fun t => (χ t:ℂ)) T 0 = fun t => (χ (t/T):ℂ) := by
      funext t
      simp [scaledModulated,phase]
    simpa [hf] using fourier_scaledModulated (fun t => (χ t:ℂ)) hT 0 ξ
  have hFs : Integrable (𝓕 (fun t => (χ (t/T):ℂ))) := by
    rw [he]
    exact (hF.comp_mul_left' (ne_of_gt hT)).smul T
  have hb : ∀ t, ‖(χ (t/T):ℂ)‖ ≤ 1 := by
    intro t
    simpa [Complex.norm_real,abs_of_nonneg (hχ0 (t/T))] using hχ1 (t/T)
  have hout := source_cutoff_signal_bounds h1 h2 hΛ hs hb hFs
  rw [source_cutoff_scaled_fourier_l1 (fun t => (χ t:ℂ)) hT] at hout
  exact hout

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.source_cutoff_fourier_convolution
#print axioms GuthMaynard.Improvement.source_cutoff_fourier_l1
#print axioms GuthMaynard.Improvement.source_cutoff_signal_bounds
#print axioms GuthMaynard.Improvement.source_cutoff_scaled_fourier_l1

#print axioms GuthMaynard.Improvement.source_smooth_scaled_cutoff_bounds
