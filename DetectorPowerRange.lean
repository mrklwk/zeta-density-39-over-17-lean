module
public import CriticalTailThreshold
public import RightSolidPolynomialCounts

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter MathCollab.Density.Stronger MathCollab.Density
namespace Montgomery.RationalMoment.RightDetector

/-- Whole-interval lower bound, including every closed join, for the exact detector exponent. -/
theorem rightSolid_detector_exponent_lower {σ : ℝ}
    (hl : 7/9 ≤ σ) (_hr : σ ≤ 4/5) :
    (881/6659:ℝ) ≤ (3*rightSolidLengthExponent σ/4)*(σ-1/2) := by
  unfold rightSolidLengthExponent
  split_ifs with h₁ h₂ h₃ h₄
  · have hd : 0 < 4*(11*σ-7) := by linarith
    have he : (3*(1/(11*σ-7))/4)*(σ-1/2) =
        (3*(σ-1/2))/(4*(11*σ-7)) := by field_simp
    rw [he]
    apply (le_div_iff₀ hd).mpr
    nlinarith
  · have hd : 0 < 4*(14610*σ-3849) := by linarith
    have he : (3*(4744/(14610*σ-3849))/4)*(σ-1/2) =
        (3*4744*(σ-1/2))/(4*(14610*σ-3849)) := by field_simp
    rw [he]
    apply (le_div_iff₀ hd).mpr
    nlinarith
  · have hd : 0 < 4*(19062*σ-5079) := by linarith
    have he : (3*(6154/(19062*σ-5079))/4)*(σ-1/2) =
        (3*6154*(σ-1/2))/(4*(19062*σ-5079)) := by field_simp
    rw [he]
    apply (le_div_iff₀ hd).mpr
    nlinarith
  · have hd : 0 < 4*(11808*σ-3195) := by linarith
    have he : (3*(3782/(11808*σ-3195))/4)*(σ-1/2) =
        (3*3782*(σ-1/2))/(4*(11808*σ-3195)) := by field_simp
    rw [he]
    apply (le_div_iff₀ hd).mpr
    nlinarith
  · have hd : 0 < 4*(6846*σ-1893) := by linarith
    have he : (3*(2168/(6846*σ-1893))/4)*(σ-1/2) =
        (3*2168*(σ-1/2))/(4*(6846*σ-1893)) := by field_simp
    rw [he]
    apply (le_div_iff₀ hd).mpr
    nlinarith

/-- The literal detector dominates any power below its exact exponent after denominator loss. -/
theorem criticalMeanThreshold_dominates_power {C σ a δ q K : ℝ}
    (hC : 0 < C) (_hK : 0 < K)
    (hmargin : q+δ/2 < (3*a/4)*(σ-1/2)) :
    ∀ᶠ T : ℝ in atTop, K*T^q ≤ criticalMeanThreshold C σ a δ T := by
  let e : ℝ := ((3*a/4)*(σ-1/2)-q-δ/2)/3
  have he : 0 < e := by dsimp [e]; linarith
  have hconst := (tendsto_rpow_atTop he).eventually
    (eventually_ge_atTop (48*C*K))
  filter_upwards [hconst,log_pow_eventually_le_rpow 1 he,
    eventually_ge_atTop (2:ℝ)] with T hc hlog hT
  have hTp : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hsqrt : Real.sqrt (detectorX δ T)=T^(δ/2) := by
    rw [Real.sqrt_eq_rpow,detectorX,← Real.rpow_mul hTp.le]
    congr 1
    ring
  have hYpow : (detectorY a T)^((σ-1/2)/2)=T^((3*a/4)*(σ-1/2)) := by
    rw [detectorY,smoothingExponent,← Real.rpow_mul hTp.le]
    congr 1
    ring
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  unfold criticalMeanThreshold
  apply (le_div_iff₀ (by have := Real.log_pos (by linarith : 1<T); unfold detectorX; positivity)).mpr
  rw [hsqrt,hYpow]
  calc
    _ = (48*C*K)*T^q*T^(δ/2)*Real.log T := by ring
    _ ≤ T^e*T^q*T^(δ/2)*T^e := by gcongr; simpa only [pow_one] using hlog
    _ = T^(q+δ/2+2*e) := by
      rw [← Real.rpow_add hTp,← Real.rpow_add hTp,← Real.rpow_add hTp]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT1 (by dsimp [e]; linarith)

/-- The physical [0,3T] tail threshold satisfies the restricted BHB amplitude range. -/
theorem rightSolid_physical_threshold_range {C σ δ η : ℝ}
    (hC : 0 < C) (hl : 7/9 ≤ σ) (hr : σ ≤ 4/5)
    (hroom : η+δ/2 < 389/53272) :
    ∀ᶠ T : ℝ in atTop,
      (3*T)^(1/8+η) ≤ criticalMeanThreshold C σ (rightSolidLengthExponent σ) δ T/(4*Real.pi) := by
  have hm : (1/8+η)+δ/2 < (3*rightSolidLengthExponent σ/4)*(σ-1/2) := by
    have hh := rightSolid_detector_exponent_lower hl hr
    norm_num at hh ⊢
    linarith
  have hc := criticalMeanThreshold_dominates_power hC
    (show 0 < 4*Real.pi*(3:ℝ)^(1/8+η) by positivity) hm
  filter_upwards [hc,eventually_ge_atTop (0:ℝ)] with T h hT
  apply (le_div_iff₀ (by positivity : 0 < 4*Real.pi)).mpr
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hT]
  convert h using 1
  ring
end Montgomery.RationalMoment.RightDetector
