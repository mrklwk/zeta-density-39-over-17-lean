module
public import RetunedLongMultiplicity
public import MathCollab.Density.Stronger.NativeMoment

@[expose] public section

open Real Complex Filter MeasureTheory Set
open scoped BigOperators Topology
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger MathCollab.Density

/-- The native actual-zeta twelfth moment closes the long branch whenever
its exact numerical budget holds. No analytic moment premise remains. -/
theorem smoothLongZeroCount_twelfth {σ a δ η ε : ℝ}
    (hw : QuadraticWindow σ a) (hsigma : 7/9 ≤ σ)
    (hδ : 0 < δ) (hδcap : δ ≤ 1/8) (hδε : δ ≤ ε/100)
    (hη : 0 < η) (hε : 0 < ε) (h12 : 2 ≤ a*(6*σ-3/2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      (smoothLongZeroCount η σ a δ T:ℝ) ≤ C*T^(3*a*(1-σ)+ε) := by
  have hquarter : 0 < ε/4 := by positivity
  obtain ⟨C,hC,hraw⟩ := smoothLongZeroCount_physical_moment_reduction hw hsigma hδ hδcap hη
  obtain ⟨D,hD,hmoment⟩ := zeta_twelfth_physical_native (ε/4) hquarter
  refine ⟨C*(D+1),by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ),hraw,hmoment,
    log_pow_eventually_le_rpow 13 hquarter] with T hT hr hm hlog
  have hTp : 0 < T := by linarith
  have hXp : 0 ≤ detectorX δ T := Real.rpow_nonneg hTp.le _
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have hYp : 0 < detectorY a T := by unfold detectorY; positivity
  have htail : T^(-113:ℝ) ≤ T^(2+ε/4) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have hbracket : (∫ t in Icc 0 (3*T),zetaMomentCriticalNorm t^12)+T^(-113:ℝ) ≤
      (D+1)*T^(2+ε/4) := by nlinarith only [hm,htail]
  have hpre : (smoothLongZeroCount η σ a δ T:ℝ)*(detectorY a T)^(6*σ-3) ≤
      C*(D+1)*((detectorX δ T)^6*(Real.log T)^13*T^(2+ε/4)) := by
    exact hr.trans ((mul_le_mul_of_nonneg_left hbracket (by positivity)).trans_eq (by ring))
  have hid : (detectorX δ T)^6*T^(2+ε/4)/(detectorY a T)^(6*σ-3)=
      T^(6*δ+2+ε/4-(3*a/2)*(6*σ-3)) := by
    rw [detectorX,detectorY,smoothingExponent,← Real.rpow_mul_natCast hTp.le,
      ← Real.rpow_mul hTp.le,← Real.rpow_add hTp,← Real.rpow_sub hTp]
    congr 1
    norm_num
    ring
  have hscalar : (detectorX δ T)^6*(Real.log T)^13*T^(2+ε/4)/(detectorY a T)^(6*σ-3) ≤
      T^(3*a*(1-σ)+ε) := by
    calc
      _ = (Real.log T)^13*((detectorX δ T)^6*T^(2+ε/4)/(detectorY a T)^(6*σ-3)) := by ring
      _ ≤ T^(ε/4)*((detectorX δ T)^6*T^(2+ε/4)/(detectorY a T)^(6*σ-3)) := by gcongr
      _ = T^(ε/4)*T^(6*δ+2+ε/4-(3*a/2)*(6*σ-3)) := by rw [hid]
      _ = T^(ε/4+(6*δ+2+ε/4-(3*a/2)*(6*σ-3))) := by rw [← Real.rpow_add hTp]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT (by nlinarith only [h12,hδε,hε])
  have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hYp (6*σ-3))).mpr hpre
  have hm := mul_le_mul_of_nonneg_left hscalar (show 0 ≤ C*(D+1) by positivity)
  exact hh.trans (by simpa only [mul_div_assoc] using hm)

end Montgomery.RationalMoment.RightDetector
