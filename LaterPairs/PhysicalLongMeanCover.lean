module
public import LaterPairs.PhysicalShortPoweredFamily
public import RetunedLongMeanCover
public import RetunedShortPoweredFamily
public import MathCollab.Density.Stronger.LongMeanCounting

@[expose] public section

open Real Complex Filter MeasureTheory
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density.Stronger
open MathCollab.Density

/-- The actual-zero dichotomy with the long alternative expressed as a
critical-line mean. Both alternatives keep the original ordinate. -/
theorem smooth_long_mean_or_short_powered_cover {σ a δ η : ℝ}
    (hw : PhysicalDetectorWindow σ a) (hδ : 0 < δ) (hδ' : δ ≤ 1/8) (hη : 0 < η)
    (A : ℕ) (hA : 3 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ,
      σ ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T → riemannZeta ρ = 0 →
      ((detectorY a T)^((σ-1/2)/2) ≤
        48*C*Real.sqrt (detectorX δ T)*Real.log T*weightedCriticalMean A ρ.im) ∨
      (∃ q ∈ smoothPoweredIndices a δ T,
        (smoothPoweredFamilyScale q : ℝ)^σ*T^(-2*η) ≤
          ‖detectingPolynomial (smoothPoweredFamilyScale q)
            (smoothPoweredFamilyCoefficient η a δ T q) ρ.im‖) := by
  have hσ := hw.sigma_low
  obtain ⟨C,hC,hm⟩ := smoothMollifierBlock_eventually_detects_mean smoothDyadicWeight_contDiff
    (by norm_num : (0:ℝ)<5/8) (by norm_num : (0:ℝ)<3/2) smoothDyadicWeight_tsupport A hA
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ), hm, log_sq_eventually_le_height,
    smooth_long_or_short_powered_cover hw hδ hδ' hη] with T hT hmean hlogSq hcover
  intro ρ hβ hβ' hγ hγ' hzero
  rcases hcover ρ hβ hβ' hγ hγ' hzero with ⟨j,hj,hlong,hlarge⟩ | hshort
  · apply Or.inl
    have hTp : 0 < T := by linarith
    have hT1 : 1 ≤ T := by linarith
    have hlog : 0 < Real.log T := Real.log_pos (by linarith)
    have hjpos : 0 < j := smoothDetectorBlock_index_pos
      (show smoothDetectorBlock ρ (detectorX δ T) (detectorY a T) j ≠ 0 by
        intro hz
        rw [hz,norm_zero] at hlarge
        have : 0 < 1/(24*Real.log T) := by positivity
        linarith)
    have hN : 2 ≤ (2 : ℝ)^j := by
      have hh := zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) (show (1:ℤ) ≤ j by omega)
      simpa using hh
    have hX : 0 ≤ detectorX δ T := Real.rpow_nonneg hTp.le _
    have hXT : detectorX δ T ≤ T := by
      simpa only [detectorX,Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hT1 (show δ ≤ 1 by linarith)
    have hYp : 0 < detectorY a T := Real.rpow_pos_of_pos hTp _
    have hYT : detectorY a T ≤ T := by
      simpa only [detectorY,Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hT1 (smoothingExponent_lt_one_physical hw).le
    have hNT : (2 : ℝ)^j ≤ T^2 := by
      apply (mem_smoothScaleIndices.mp hj).2.trans
      calc
        _ ≤ T*T := mul_le_mul hYT hlogSq (sq_nonneg _) hTp.le
        _ = _ := by ring
    have hlong' : Real.sqrt (detectorY a T) ≤ (2 : ℝ)^j := by
      have he : Real.sqrt (detectorY a T) = T^(smoothingExponent a/2) := by
        rw [Real.sqrt_eq_rpow,detectorY,← Real.rpow_mul hTp.le]
        congr 1
        ring
      rw [he]
      exact hlong.le
    apply weightedCriticalMean_long_scale (by linarith) (by linarith) hYp
      (by linarith : 1/2 ≤ σ) hβ hlong'
    apply hmean ρ (detectorX δ T) ((2 : ℝ)^j) ((2 : ℝ)^j/detectorY a T)
      (hw.sigma_low.le.trans hβ) hβ' hγ hX hXT (by linarith) hNT (by positivity)
    rw [← smoothDetectorBlock_eq_smoothMollifierBlock (detectorX δ T) hYp (by linarith) hN]
    exact hlarge
  · exact Or.inr hshort


end Montgomery.RationalMoment.RightDetector.Physical
