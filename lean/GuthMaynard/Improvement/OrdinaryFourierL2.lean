module
public import Mathlib.Analysis.Fourier.LpSpace

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff
namespace GuthMaynard.Improvement

/-- The literal integral Fourier transform agrees almost everywhere with the
Hilbert-space Fourier transform for ordinary L1/L2 functions. -/
theorem ordinary_fourier_ae_L2 {f : ℝ → ℂ} (h1 : Integrable f)
    (h2 : MemLp f 2) :
    ((𝓕 (h2.toLp f) : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume] 𝓕 f := by
  have hcont : Continuous (𝓕 f) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ h1
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕 (h2.toLp f))).locallyIntegrable (by norm_num))
    hcont.locallyIntegrable
  intro g hg hc
  let G : 𝓢(ℝ, ℂ) := (hc.comp_left (show (Complex.ofRealCLM : ℝ → ℂ) 0 = 0 by rfl)).toSchwartzMap
    (show ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) by fun_prop)
  have hd := congrArg (fun d : TemperedDistribution ℝ ℂ => d G)
    (Lp.fourier_toTemperedDistribution_eq (h2.toLp f))
  have hd' : (∫ x, (𝓕 G) x * f x) =
      ∫ x, G x * (𝓕 (h2.toLp f)) x := by
    simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
      smul_eq_mul] at hd
    calc
      _ = ∫ x, (𝓕 G) x * (h2.toLp f) x := by
        apply integral_congr_ae
        filter_upwards [h2.coeFn_toLp] with x hx
        rw [hx]
      _ = _ := hd
  have hpair : (∫ x, (𝓕 G) x * f x) = ∫ x, G x * (𝓕 f) x := by
    simpa [SchwartzMap.fourier_coe, Real.fourier_eq,
      VectorFourier.fourierIntegral, real_inner_comm] using VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (ContinuousLinearMap.mul ℂ ℂ) (μ := volume) (ν := volume) (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner G.integrable h1
  calc
    _ = ∫ x, G x * (𝓕 (h2.toLp f)) x := by simp [G, Complex.real_smul]
    _ = ∫ x, (𝓕 G) x * f x := hd'.symm
    _ = ∫ x, G x * (𝓕 f) x := hpair
    _ = _ := by simp [G, Complex.real_smul]

/-- Square integrability of the actual integral Fourier transform. -/
theorem ordinary_fourier_memLp {f : ℝ → ℂ} (h1 : Integrable f)
    (h2 : MemLp f 2) : MemLp (𝓕 f) 2 :=
  (Lp.memLp (𝓕 (h2.toLp f))).ae_eq (ordinary_fourier_ae_L2 h1 h2)

set_option maxHeartbeats 800000 in
/-- Literal-integral Plancherel, with no regularity assumption on f. -/
theorem ordinary_fourier_integral_sq {f : ℝ → ℂ} (h1 : Integrable f)
    (h2 : MemLp f 2) : (∫ ξ, ‖𝓕 f ξ‖^2) = ∫ x, ‖f x‖^2 := by
  have h := Lp.inner_fourier_eq (h2.toLp f) (h2.toLp f)
  rw [L2.inner_def, L2.inner_def] at h
  simp only [inner_self_eq_norm_sq_to_K] at h
  have he : (∫ ξ, (‖𝓕 f ξ‖^2 : ℂ)) = ∫ x, (‖f x‖^2 : ℂ) := by
    calc
      _ = ∫ ξ, (‖(𝓕 (h2.toLp f) : Lp ℂ 2 volume) ξ‖^2 : ℂ) := by
        apply integral_congr_ae
        filter_upwards [ordinary_fourier_ae_L2 h1 h2] with ξ hξ
        rw [hξ]
      _ = ∫ x, (‖(h2.toLp f) x‖^2 : ℂ) := h
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [h2.coeFn_toLp] with x hx
        rw [hx]
  exact_mod_cast he

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.ordinary_fourier_ae_L2
#print axioms GuthMaynard.Improvement.ordinary_fourier_memLp
#print axioms GuthMaynard.Improvement.ordinary_fourier_integral_sq
