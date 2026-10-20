module
public import RetunedDetectorParameters

@[expose] public section

open Real Complex MeasureTheory Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger
open MathCollab.Density

/-- The actual contour detector is uniformly small for the stronger curve's
parameters. The Weyl input is proved and discharged; no moment is assumed. -/
theorem detector_eventually_small {σ a δ ε : ℝ}
    (hw : QuadraticWindow σ a) (hsigma : 7/9 ≤ σ) (hδ : δ ≤ 1/8) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ,
      σ ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T →
      riemannZeta ρ = 0 →
      ‖smoothedDetector ρ (detectorX δ T) (1 / detectorY a T)‖ < ε := by
  obtain ⟨C, hC, hW⟩ := actual_zeta_weyl_input (by norm_num : (0 : ℝ) < 1/96)
  obtain ⟨A, hA, hbound⟩ := uniform_detector_integral_bound
  have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/96)).const_mul (A*C)
  simp only [mul_zero] at ht
  have hsmall : ∀ᶠ T : ℝ in atTop, A*C*T^(-1/48+1/96 : ℝ) < ε/2 := by
    have hexp : (-1/48+1/96 : ℝ) = -(1/96 : ℝ) := by norm_num
    rw [hexp]
    exact ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε/2))
  have hp := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).const_mul 72
  simp only [mul_zero] at hp
  have hpole : ∀ᶠ T : ℝ in atTop, 72*T^3*Real.exp (-T) < ε/2 := by
    simpa only [mul_zero, mul_assoc] using
      hp.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε/2))
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsmall, hpole] with T hT hs hp
  intro ρ hβ hβ' hγ hγ' hzero
  have hTpos : 0 < T := by linarith
  have hX : 0 ≤ detectorX δ T := Real.rpow_nonneg hTpos.le _
  have hXT : detectorX δ T ≤ T := by
    simpa [detectorX] using Real.rpow_le_rpow_of_exponent_le hT
      (show δ ≤ 1 by linarith)
  have hY : 1 ≤ detectorY a T := Real.one_le_rpow hT (smoothingExponent_pos hw).le
  have hYT : detectorY a T ≤ T := by
    simpa [detectorY] using Real.rpow_le_rpow_of_exponent_le hT
      (smoothingExponent_lt_one hw).le
  have hb : 3/4 ≤ ρ.re := hw.sigma_low.le.trans hβ
  have hi := hbound (1/6+1/96) C T (detectorX δ T) (detectorY a T) ρ
    (by norm_num) (by norm_num) hC.le hT hX (by linarith) hb hβ'.le hγ' hW
  have hscale := mul_le_mul_of_nonneg_left
    (detector_error_scale (η := 1/96) hw hsigma hδ hT hβ) (show 0 ≤ A*C by positivity)
  have hint : ‖detectorIntegral ρ (detectorX δ T) (detectorY a T)‖ < ε/2 :=
    (hi.trans (by simpa only [mul_assoc] using hscale)).trans_lt hs
  have hr := (norm_residue_le hT hX hXT hY hYT hb hβ'.le hγ hγ').trans_lt hp
  rw [smoothedDetector_contour_identity hY hb hβ' hzero]
  change ‖detectorResidue ρ (detectorX δ T) (detectorY a T) +
    detectorIntegral ρ (detectorX δ T) (detectorY a T)‖ < ε
  exact (norm_add_le _ _).trans_lt (by linarith)

/-- Uniform detection of every actual zero in the slab, with the exact new
parameters and the same ordinate. This does not yet choose a smooth dyadic block. -/
theorem detectorTail_eventually_large {σ a δ : ℝ}
    (hw : QuadraticWindow σ a) (hsigma : 7/9 ≤ σ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/8) :
    ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ,
      σ ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T →
      riemannZeta ρ = 0 →
      (1/2 : ℝ) ≤ ‖detectorTail ρ (detectorX δ T) (detectorY a T)‖ := by
  have hy : ∀ᶠ T : ℝ in atTop, 4 ≤ detectorY a T :=
    (tendsto_rpow_atTop (smoothingExponent_pos hw)).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hy,
    detector_eventually_small hw hsigma hδ' (by norm_num : (0 : ℝ) < 1/4)] with T hT hY hs
  intro ρ hβ hβ' hγ hγ' hzero
  have hX : 1 ≤ detectorX δ T := Real.one_le_rpow hT hδ
  have hd := detectorTail_decomposition hX (show 0 < detectorY a T by linarith)
    (show 0 ≤ ρ.re by linarith)
  have he : (3/4 : ℝ) ≤ Real.exp (-1 / detectorY a T) := by
    have hexp := Real.add_one_le_exp (-1 / detectorY a T)
    have hinv : 1 / detectorY a T ≤ (1/4 : ℝ) :=
      (div_le_iff₀ (by linarith : 0 < detectorY a T)).2 (by linarith)
    rw [neg_div] at hexp ⊢
    linarith
  have hn : ‖(Real.exp (-1 / detectorY a T) : ℂ)‖ ≤
      ‖smoothedDetector ρ (detectorX δ T) (1 / detectorY a T)‖ +
        ‖detectorTail ρ (detectorX δ T) (detectorY a T)‖ := by
    have hh : (Real.exp (-1 / detectorY a T) : ℂ) =
        smoothedDetector ρ (detectorX δ T) (1 / detectorY a T) -
          detectorTail ρ (detectorX δ T) (detectorY a T) := by rw [← hd]; ring
    rw [hh]
    exact norm_sub_le _ _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hn
  have hm := hs ρ hβ hβ' hγ hγ' hzero
  linarith


end Montgomery.RationalMoment.RightDetector
