module
public import GuthMaynard.Improvement.SmoothingScale
public import GuthMaynard.Improvement.PoissonReduction

@[expose] public section

/-! Fourier transfer for actual real smoothing. Constants precede the signal
and the smoothing width; no positive lower bound on its mass is required. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped FourierTransform Convolution SchwartzMap
namespace GuthMaynard.Improvement

theorem complex_smooth (κ g : ℝ → ℝ) :
    (fun x => (smooth κ g x : ℂ)) =
      (fun x => (g x : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ] (fun x => (κ x : ℂ)) := by
  funext x
  simp only [smooth, convolution, ContinuousLinearMap.mul_apply', ← integral_complex_ofReal,
    Complex.ofReal_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  ring

theorem fourier_smooth {κ g : ℝ → ℝ} (hκ : Integrable κ) (hg : Integrable g) (ξ : ℝ) :
    𝓕 (fun x => (smooth κ g x : ℂ)) ξ =
      𝓕 (fun x => (g x : ℂ)) ξ * 𝓕 (fun x => (κ x : ℂ)) ξ := by
  rw [complex_smooth]
  exact Real.fourier_mul_convolution_eq (Complex.ofRealCLM.integrable_comp hg)
    (Complex.ofRealCLM.integrable_comp hκ) ξ

theorem fourier_nonneg_mass {g : ℝ → ℝ} (hg : ∀ x, 0 ≤ g x) (ξ : ℝ) :
    ‖𝓕 (fun x => (g x : ℂ)) ξ‖ ≤ ∫ x, g x := by
  have h := VectorFourier.norm_fourierIntegral_le_integral_norm
    Real.fourierChar volume (innerₗ ℝ) (fun x : ℝ => (g x : ℂ)) ξ
  simpa only [Real.fourier_eq, VectorFourier.fourierIntegral, innerₗ_apply_apply, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (hg _)] using h

theorem fourier_smooth_mass_bound {κ g : ℝ → ℝ}
    (hκ : Integrable κ) (hg : Integrable g) (hg0 : ∀ x, 0 ≤ g x) (ξ : ℝ) :
    ‖𝓕 (fun x => (smooth κ g x : ℂ)) ξ‖ ≤
      (∫ x, g x) * ‖𝓕 (fun x => (κ x : ℂ)) ξ‖ := by
  rw [fourier_smooth hκ hg, norm_mul]
  exact mul_le_mul_of_nonneg_right (fourier_nonneg_mass hg0 ξ) (norm_nonneg _)

theorem fourier_scaledKernel (φ : ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ) (ξ : ℝ) :
    𝓕 (fun x => (scaledKernel φ δ x : ℂ)) ξ =
      𝓕 (fun x => (φ x : ℂ)) (δ * ξ) := by
  have heq : (fun x => (scaledKernel φ δ x : ℂ)) =
      (fun x => (δ⁻¹ : ℂ) * scaledModulated (fun y => (φ y : ℂ)) δ 0 x) := by
    funext x
    simp [scaledKernel, scaledModulated, phase]
  rw [heq, fourier_constant_mul, fourier_scaledModulated _ hδ]
  simp [sub_zero, Complex.real_smul, hδ.ne']

/-- The exact real scaled smoothing identity and its original mass factor. -/
theorem fourier_scaled_smooth_mass_bound {φ g : ℝ → ℝ} {δ : ℝ}
    (hφ : Integrable φ) (hg : Integrable g) (hg0 : ∀ x, 0 ≤ g x)
    (hδ : 0 < δ) (ξ : ℝ) :
    ‖𝓕 (fun x => (smooth (scaledKernel φ δ) g x : ℂ)) ξ‖ ≤
      (∫ x, g x) * ‖𝓕 (fun x => (φ x : ℂ)) (δ * ξ)‖ := by
  simpa only [fourier_scaledKernel φ hδ] using
    fourier_smooth_mass_bound (scaledKernel_integrable hφ hδ) hg hg0 ξ

/-- Fixed-kernel rapid decay, with the constant chosen before every frequency. -/
theorem schwartz_fourier_power_bound (φ : 𝓢(ℝ, ℂ)) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ, |ξ| ^ j * ‖𝓕 (φ : ℝ → ℂ) ξ‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := (𝓕 φ).decay j 0
  refine ⟨C, hC, ?_⟩
  intro ξ
  simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, SchwartzMap.fourier_coe] using h ξ

/-- No decay constant depends on delta. The displayed frequency weight keeps
its dependence exactly, including near frequency zero. -/
theorem schwartz_scaled_frequency_bound (φ : 𝓢(ℝ, ℂ)) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → ∀ ξ : ℝ,
      |ξ| ^ j * ‖𝓕 (φ : ℝ → ℂ) (δ * ξ)‖ ≤ δ⁻¹ ^ j * C := by
  obtain ⟨C, hC, h⟩ := schwartz_fourier_power_bound φ j
  refine ⟨C, hC, ?_⟩
  intro δ hδ ξ
  have hh := mul_le_mul_of_nonneg_left (h (δ * ξ)) (pow_nonneg (inv_nonneg.mpr hδ.le) j)
  have heq : δ⁻¹ ^ j * (|δ * ξ| ^ j * ‖𝓕 (φ : ℝ → ℂ) (δ * ξ)‖) =
      |ξ| ^ j * ‖𝓕 (φ : ℝ → ℂ) (δ * ξ)‖ := by
    rw [abs_mul, abs_of_pos hδ, mul_pow]
    rw [← mul_assoc, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hδ.ne']
    simp
  rw [heq] at hh
  exact hh

/-- Actual scaled smoothing has uniform rapid decay weighted by the exact
input mass. The Schwartz representative is fixed before delta and g. -/
theorem scaled_smooth_power_bound (φ : ℝ → ℝ) (ψ : 𝓢(ℝ, ℂ))
    (hψ : (ψ : ℝ → ℂ) = fun x => (φ x : ℂ)) (hφ : Integrable φ) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → ∀ g : ℝ → ℝ,
      Integrable g → (∀ x, 0 ≤ g x) → ∀ ξ : ℝ,
      |ξ| ^ j * ‖𝓕 (fun x => (smooth (scaledKernel φ δ) g x : ℂ)) ξ‖ ≤
        δ⁻¹ ^ j * C * (∫ x, g x) := by
  obtain ⟨C, hC, h⟩ := schwartz_scaled_frequency_bound ψ j
  refine ⟨C, hC, ?_⟩
  intro δ hδ g hg hg0 ξ
  have hm : 0 ≤ ∫ x, g x := integral_nonneg hg0
  have h1 := mul_le_mul_of_nonneg_left
    (fourier_scaled_smooth_mass_bound hφ hg hg0 hδ ξ) (pow_nonneg (abs_nonneg ξ) j)
  have h2 := mul_le_mul_of_nonneg_right (h δ hδ ξ) hm
  rw [hψ] at h2
  calc
    _ ≤ |ξ| ^ j * ((∫ x, g x) * ‖𝓕 (fun x => (φ x : ℂ)) (δ * ξ)‖) := h1
    _ = (|ξ| ^ j * ‖𝓕 (fun x => (φ x : ℂ)) (δ * ξ)‖) * (∫ x, g x) := by ring
    _ ≤ _ := h2

/-- Measurable masks require no boundary regularity and no mass lower bound. -/
theorem masked_scaled_fourier_bound (φ : ℝ → ℝ) (ψ : 𝓢(ℝ, ℂ))
    (hψ : (ψ : ℝ → ℂ) = fun x => (φ x : ℂ)) (hφ : Integrable φ) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → ∀ A : Set ℝ,
      MeasurableSet A → ∀ r : ℝ → ℝ, Integrable (fun x => r x ^ 2) → ∀ ξ : ℝ,
      |ξ| ^ j * ‖𝓕 (fun x => (squareSmoothing (scaledKernel φ δ) (A.indicator r) x : ℂ)) ξ‖ ≤
        δ⁻¹ ^ j * C * (∫ x in A, r x ^ 2) := by
  obtain ⟨C, hC, h⟩ := scaled_smooth_power_bound φ ψ hψ hφ j
  refine ⟨C, hC, ?_⟩
  intro δ hδ A hA r hr ξ
  have heq : squareSmoothing (scaledKernel φ δ) (A.indicator r) =
      smooth (scaledKernel φ δ) (A.indicator (fun x => r x ^ 2)) := by
    funext x
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ A <;> simp [hy]
  rw [heq]
  have hg0 : ∀ x, 0 ≤ A.indicator (fun y => r y ^ 2) x := by
    intro x
    by_cases hx : x ∈ A <;> simp [hx, sq_nonneg]
  simpa only [integral_indicator hA] using h δ hδ _ (hr.indicator hA) hg0 ξ

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.complex_smooth
#print axioms GuthMaynard.Improvement.fourier_smooth
#print axioms GuthMaynard.Improvement.fourier_nonneg_mass
#print axioms GuthMaynard.Improvement.fourier_smooth_mass_bound
#print axioms GuthMaynard.Improvement.schwartz_fourier_power_bound
#print axioms GuthMaynard.Improvement.schwartz_scaled_frequency_bound

#print axioms GuthMaynard.Improvement.fourier_scaledKernel
#print axioms GuthMaynard.Improvement.fourier_scaled_smooth_mass_bound

#print axioms GuthMaynard.Improvement.scaled_smooth_power_bound
#print axioms GuthMaynard.Improvement.masked_scaled_fourier_bound
