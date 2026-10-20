module
public import RetunedInitialDetector
public import MathCollab.Density.Stronger.SmoothDetector

@[expose] public section

open Real Complex MeasureTheory Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger

/-- All-zero smooth dyadic detection for the stronger parameters, with no
Weyl or moment premise. The finite list is chosen before rho varies. -/
theorem smoothDetector_eventually_large {σ a δ : ℝ}
    (hw : QuadraticWindow σ a) (hsigma : 7/9 ≤ σ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/8) :
    ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ,
      σ ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T →
      riemannZeta ρ = 0 →
      ∃ j ∈ smoothScaleIndices (detectorY a T*(Real.log T)^2),
        detectorX δ T/2 < (2 : ℝ)^j ∧
        (1/(24*Real.log T) : ℝ) ≤
          ‖smoothDetectorBlock ρ (detectorX δ T) (detectorY a T) j‖ := by
  filter_upwards [eventually_ge_atTop (4 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 16,
    log_sq_eventually_le_height, detectorTail_eventually_large hw hsigma hδ hδ']
    with T hT hlog hlogSq hdetect
  intro ρ hβ hβ' hγ hγ' hzero
  have hTpos : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hX : 0 ≤ detectorX δ T := Real.rpow_nonneg hTpos.le _
  have hXT : detectorX δ T ≤ T := by
    simpa only [detectorX, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT1 (show δ ≤ 1 by linarith)
  have hY : 1 ≤ detectorY a T := Real.one_le_rpow hT1 (smoothingExponent_pos hw).le
  have hYT : detectorY a T ≤ T := by
    simpa only [detectorY, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT1 (smoothingExponent_lt_one hw).le
  have hR : 1 ≤ detectorY a T*(Real.log T)^2 := by nlinarith
  have hRT : detectorY a T*(Real.log T)^2 ≤ T^2 := by
    calc
      _ ≤ T*T := mul_le_mul hYT hlogSq (sq_nonneg _) hTpos.le
      _ = _ := by ring
  have htail := smoothDetectorBlock_scale_tail_le_two_rpow hT1 hlog hX hXT hY hYT
    (show 0 ≤ ρ.re by linarith)
  have hsmall : 2*T^(-2 : ℝ) ≤ (1/4 : ℝ) := by
    have he : 2*T^(-2 : ℝ) = 2/T^2 := by
      rw [Real.rpow_neg hTpos.le, Real.rpow_two]
      ring
    rw [he]
    apply (div_le_iff₀ (sq_pos_of_pos hTpos)).mpr
    nlinarith
  obtain ⟨j, hj, hscale, hheight⟩ := exists_smoothDetectorBlock
    (show 0 < detectorY a T by linarith) (show 0 ≤ ρ.re by linarith) hR
    (by norm_num : (0 : ℝ) < 1/2) (hdetect ρ hβ hβ' hγ hγ' hzero)
    (by simpa only [show (1/2 : ℝ)/2 = 1/4 by norm_num] using htail.trans hsmall)
  refine ⟨j, hj, hscale, ?_⟩
  have hcard := smoothScaleIndices_card_le_log hT1 (by linarith) hR hRT
  have hcpos : (0 : ℝ) < (smoothScaleIndices (detectorY a T*(Real.log T)^2)).card := by
    exact_mod_cast Finset.card_pos.mpr (smoothScaleIndices_nonempty hR)
  calc
    (1/(24*Real.log T) : ℝ) ≤
        (1/2)/(2*(smoothScaleIndices (detectorY a T*(Real.log T)^2)).card) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      linarith
    _ ≤ _ := hheight


end Montgomery.RationalMoment.RightDetector
