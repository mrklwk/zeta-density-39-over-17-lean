module
public import RetunedDetectorParameters

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector

/-- Numeric contour-detector conditions, independent of the old polynomial
counting inequalities in QuadraticWindow. -/
structure PhysicalDetectorWindow (σ a : ℝ) : Prop where
  sigma_low : 3/4 < σ
  sigma_high : σ < 1
  a_low : 1/2 ≤ a
  a_high : a < 2/3
  threshold : 1/8 < (3*a/4)*(σ-1/2)

theorem smoothingExponent_pos_physical {σ a : ℝ} (hw : PhysicalDetectorWindow σ a) :
    0 < smoothingExponent a := by unfold smoothingExponent; linarith [hw.a_low]

theorem smoothingExponent_lt_one_physical {σ a : ℝ} (hw : PhysicalDetectorWindow σ a) :
    smoothingExponent a < 1 := by unfold smoothingExponent; linarith [hw.a_high]

/-- The physical threshold supplies the actual contour saving directly. -/
theorem detector_error_scale_physical {σ a δ T β η : ℝ}
    (hw : PhysicalDetectorWindow σ a)
    (hδ : δ ≤ 1/8) (hT : 1 ≤ T) (hβ : σ ≤ β) :
    Real.sqrt (MathCollab.Density.Stronger.detectorX δ T)*(detectorY a T)^(1/2-β)*T^(1/6+η) ≤
      T^(-1/48+η) := by
  have hTp : 0 < T := by linarith
  have ha : 0 < a := by linarith [hw.a_low]
  have hsprod : 1/4 ≤ (3*a/2)*(σ-1/2) := by nlinarith only [hw.threshold]
  have hmono := mul_le_mul_of_nonneg_left hβ (show 0 ≤ 3*a/2 by positivity)
  have hproduct : 1/4 ≤ smoothingExponent a*(β-1/2) := by
    unfold smoothingExponent
    nlinarith only [hsprod,hmono]
  have hsqrt : Real.sqrt (MathCollab.Density.Stronger.detectorX δ T)=T^(δ/2) := by
    rw [MathCollab.Density.Stronger.detectorX,Real.sqrt_eq_rpow,← Real.rpow_mul hTp.le]
    congr 1
    ring
  rw [hsqrt,detectorY,← Real.rpow_mul hTp.le,← Real.rpow_add hTp,← Real.rpow_add hTp]
  apply Real.rpow_le_rpow_of_exponent_le hT
  nlinarith only [hproduct,hδ]

end Montgomery.RationalMoment.RightDetector
