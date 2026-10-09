module
/- Actual short-detector critical-line input, using the audited zeta and
mollifier bounds. This file does not assume a fourth moment. -/
public import GuthMaynard.Improvement.ShortDetectorIdentity
public import MathCollab.Density.BandEnergy

@[expose] public section
set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Set Filter MathCollab.Density
open scoped Topology
namespace GuthMaynard.Improvement

def shortTwistedNorm (H t : ℝ) : ℝ :=
  ‖riemannZeta ((1/2:ℂ)+(t:ℂ)*I)*zetaMollifier (2*H^((1:ℝ)/100)) ((1/2:ℂ)+(t:ℂ)*I)‖

theorem shortTwistedNorm_continuous (H : ℝ) : Continuous (shortTwistedNorm H) := by
  apply Continuous.norm
  apply Continuous.mul
  · apply continuous_iff_continuousAt.mpr
    intro t
    apply ContinuousAt.comp' (differentiableAt_riemannZeta ?_).continuousAt (by fun_prop)
    intro hh
    have hr := congrArg Complex.re hh
    norm_num at hr
  · apply continuous_iff_continuousAt.mpr
    intro t
    exact ContinuousAt.comp' (differentiableAt_zetaMollifier _ _).continuousAt (by fun_prop)

theorem shortTwistedNorm_bound (H t : ℝ) :
    shortTwistedNorm H t ≤ 4*(⌊2*H^((1:ℝ)/100)⌋₊:ℝ)*(1+|t|) := by
  have hz := norm_riemannZeta_critical_le_linear t
  have hm := norm_zetaMollifier_le_cutoff (2*H^((1:ℝ)/100))
    (s := (1/2:ℂ)+(t:ℂ)*I) (by norm_num)
  unfold shortTwistedNorm
  rw [norm_mul]
  convert mul_le_mul hz hm (norm_nonneg _) (by positivity) using 1; ring

/-- Exact norm identity: the real power of Y retains the actual beta. -/
theorem short_detector_kernel_norm {ρ : ℂ} {Y : ℝ} (hY : 0 < Y) (H t : ℝ) :
    ‖detectorKernel ρ (2*H^((1:ℝ)/100)) Y (((1/2-ρ.re:ℝ):ℂ)+(t:ℂ)*I)‖ =
      Y^(1/2-ρ.re)*‖Complex.Gamma (((1/2-ρ.re:ℝ):ℂ)+(t:ℂ)*I)‖*
        shortTwistedNorm H (ρ.im+t) := by
  have he : ρ+(((1/2-ρ.re:ℝ):ℂ)+(t:ℂ)*I) = (1/2:ℂ)+((ρ.im+t:ℝ):ℂ)*I := by
    apply Complex.ext <;> simp
  unfold detectorKernel shortTwistedNorm
  rw [he,norm_mul,norm_mul,norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hY]
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,mul_zero,zero_mul,sub_self,add_zero]
  ring

/-- Weighted fourth Hölder proved from two audited Cauchy--Schwarz estimates.
Every moment used is explicitly integrable, preventing default-integral artifacts. -/
theorem short_weighted_fourth_holder {g F : ℝ → ℝ} (hg0 : ∀ t, 0 ≤ g t)
    (hg : Integrable g) (hgf : Integrable (fun t => g t*F t))
    (hgf2 : Integrable (fun t => g t*(F t)^2))
    (hgf4 : Integrable (fun t => g t*(F t)^4)) :
    (∫ t, g t*F t)^4 ≤ (∫ t,g t)^3*(∫ t,g t*(F t)^4) := by
  have hfirst := weighted_integral_sq_le hg0 hg hgf hgf2
  have hsecond := weighted_integral_sq_le (f := fun t => (F t)^2) hg0 hg hgf2
    (by simpa only [← pow_mul] using hgf4)
  have h0 : 0 ≤ ∫ t,g t := integral_nonneg hg0
  have h2 : 0 ≤ ∫ t,g t*(F t)^2 := integral_nonneg (fun t => mul_nonneg (hg0 t) (sq_nonneg _))
  have hh := pow_le_pow_left₀ (sq_nonneg _) hfirst 2
  have hs := mul_le_mul_of_nonneg_left hsecond (sq_nonneg (∫ t,g t))
  simp only [← pow_mul] at hh hs
  nlinarith

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.shortTwistedNorm_continuous
#print axioms GuthMaynard.Improvement.shortTwistedNorm_bound
#print axioms GuthMaynard.Improvement.short_detector_kernel_norm
#print axioms GuthMaynard.Improvement.short_weighted_fourth_holder
