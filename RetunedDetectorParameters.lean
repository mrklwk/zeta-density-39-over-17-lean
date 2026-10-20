module
public import QuadraticWindow
public import MathCollab.Density.Stronger.InitialDetector

@[expose] public section

open Filter
open scoped Topology
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger

def smoothingExponent (a : ℝ) : ℝ := 3*a/2

def detectorY (a T : ℝ) : ℝ := T^(smoothingExponent a)

theorem smoothingExponent_pos {σ a : ℝ} (hw : QuadraticWindow σ a) :
    0 < smoothingExponent a := by unfold smoothingExponent; linarith [hw.a_low]

theorem smoothingExponent_lt_one {σ a : ℝ} (hw : QuadraticWindow σ a) :
    smoothingExponent a < 1 := by unfold smoothingExponent; linarith [hw.a_high]

/-- The initial all-zero contour detector works at the retuned upper length
3a/2. The right-hand polynomial parameter conditions supply its real saving. -/
theorem detector_error_scale {σ a δ T β η : ℝ}
    (hw : QuadraticWindow σ a) (hs : 7/9 ≤ σ)
    (hδ : δ ≤ 1/8) (hT : 1 ≤ T) (hβ : σ ≤ β) :
    Real.sqrt (detectorX δ T)*(detectorY a T)^(1/2-β)*T^(1/6+η) ≤
      T^(-1/48+η) := by
  have hTp : 0 < T := by linarith
  have ha : 0 < a := by linarith [hw.a_low]
  have hm := mul_nonneg ha.le (show 0 ≤ 9*σ-7 by linarith only [hs])
  have hsprod : 1/4 ≤ (3*a/2)*(σ-1/2) := by nlinarith only [hw.first,hm]
  have hmono := mul_le_mul_of_nonneg_left hβ (show 0 ≤ 3*a/2 by positivity)
  have hproduct : 1/4 ≤ smoothingExponent a*(β-1/2) := by
    unfold smoothingExponent
    nlinarith only [hsprod,hmono]
  have hsqrt : Real.sqrt (detectorX δ T)=T^(δ/2) := by
    rw [detectorX,Real.sqrt_eq_rpow,← Real.rpow_mul hTp.le]
    congr 1
    ring
  rw [hsqrt,detectorY,← Real.rpow_mul hTp.le,← Real.rpow_add hTp,← Real.rpow_add hTp]
  apply Real.rpow_le_rpow_of_exponent_le hT
  nlinarith only [hproduct,hδ]

end Montgomery.RationalMoment.RightDetector
