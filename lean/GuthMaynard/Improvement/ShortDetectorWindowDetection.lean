import GuthMaynard.Improvement.ShortGammaPacking
import MathCollab.Density.DetectorError
set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Set Filter MathCollab.Density
open scoped Topology
namespace GuthMaynard.Improvement

/-- A large actual contour integral forces actual local fourth-moment mass.
The constant and eventual height precede sigma and every representative. -/
theorem short_detector_window_fourth :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ H : ℝ in atTop, ∀ σ : ℝ, ∀ ρ : ℂ,
      9/13 ≤ σ → σ ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ 2*H →
      (1/3:ℝ) ≤ ‖detectorIntegral ρ (2*H^((1:ℝ)/100)) (H^((1:ℝ)/2))‖ →
      1 ≤ A*H^(1-2*σ)*(∫ t in Icc (-(H/2)) (H/2),
        ‖Complex.Gamma (((1/2-ρ.re:ℝ):ℂ)+(t:ℂ)*I)‖*
        (shortTwistedNorm H (ρ.im+t))^4) := by
  obtain ⟨G,hG,hholder⟩ := short_gamma_window_holder
  refine ⟨6^4*G^3,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ),
    short_detector_ordinate_tail_eventually_small (show (0:ℝ) < 1/6 by norm_num)] with H hH htail
  intro σ ρ hσ hσβ hβ' hγ hlarge
  have hn : 0 < H := by linarith
  have hβ : 9/13 ≤ ρ.re := hσ.trans hσβ
  let Y := H^((1:ℝ)/2)
  let K := fun t : ℝ => detectorKernel ρ (2*H^((1:ℝ)/100)) Y (((1/2-ρ.re:ℝ):ℂ)+(t:ℂ)*I)
  let g := fun t : ℝ => ‖Complex.Gamma (((1/2-ρ.re:ℝ):ℂ)+(t:ℂ)*I)‖
  let F := fun t : ℝ => shortTwistedNorm H (ρ.im+t)
  let S := Icc (-(H/2)) (H/2)
  have hy : 0 < Y := by dsimp [Y]; positivity
  have hi : Integrable K := short_integrable_detectorKernel_left hy hβ hβ'
  have hc : ‖((1/(2*Real.pi):ℝ):ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity)]
    apply (div_le_one (by positivity)).mpr
    linarith [Real.pi_gt_three]
  have hnorm : ‖detectorIntegral ρ (2*H^((1:ℝ)/100)) Y‖ ≤ ∫ t, ‖K t‖ := by
    unfold detectorIntegral
    rw [norm_mul]
    exact (mul_le_mul hc (norm_integral_le_integral_norm K) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hcomp : Sᶜ = {t : ℝ | H/2 < |t|} := by
    ext t
    change (¬ t ∈ Icc (-(H/2)) (H/2)) ↔ H/2 < |t|
    rw [← not_le,abs_le]
    rfl
  have hsplit := integral_add_compl (show MeasurableSet S from measurableSet_Icc) hi.norm
  have hsmall : (∫ t in Sᶜ, ‖K t‖) < 1/6 := by
    rw [hcomp]
    exact htail ρ hβ hβ' hγ
  have hnear : (1/6:ℝ) ≤ ∫ t in S, ‖K t‖ := by linarith
  have heq : (∫ t in S, ‖K t‖) = Y^(1/2-ρ.re)*(∫ t in S, g t*F t) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    rw [short_detector_kernel_norm hy]
    dsimp only [g,F]
    ring
  rw [heq] at hnear
  have hh := hholder ρ.re H ρ.im (H/2) hβ hβ'
  have hpow := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/6) hnear 4
  rw [mul_pow] at hpow
  have hYpow : (Y^(1/2-ρ.re))^4 ≤ H^(1-2*σ) := by
    dsimp [Y]
    rw [← Real.rpow_natCast,← Real.rpow_mul hn.le,← Real.rpow_mul hn.le]
    apply Real.rpow_le_rpow_of_exponent_le hH
    nlinarith
  have hj : 0 ≤ ∫ t in S, g t*(F t)^4 := integral_nonneg (fun t => by dsimp [g,F,shortTwistedNorm]; positivity)
  have hmul := mul_le_mul_of_nonneg_left hh (show 0 ≤ (Y^(1/2-ρ.re))^4 by positivity)
  have hscale := mul_le_mul_of_nonneg_right hYpow (show 0 ≤ G^3*(∫ t in S,g t*(F t)^4) by positivity)
  change (1:ℝ) ≤ 6^4*G^3*H^(1-2*σ)*(∫ t in S,g t*(F t)^4)
  change (∫ t in S,g t*F t)^4 ≤ G^3*(∫ t in S,g t*(F t)^4) at hh
  change (Y^(1/2-ρ.re))^4*(∫ t in S,g t*F t)^4 ≤
    (Y^(1/2-ρ.re))^4*(G^3*(∫ t in S,g t*(F t)^4)) at hmul
  nlinarith

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.short_detector_window_fourth
