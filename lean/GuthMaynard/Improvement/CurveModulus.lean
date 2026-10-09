import GuthMaynard.Improvement.FullDensityCurve
import GuthMaynard.Improvement.CurveUniformization

set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- A one-sided modulus on the closed Ingham interval. -/
theorem ingham_curve_modulus {x y : ℝ}
    (_hx : 1/2 ≤ x) (hxy : x ≤ y) (hy : y ≤ 9/13) :
    3*(1-x)/(2-x) ≤ 3*(1-y)/(2-y)+4*(y-x) := by
  have hx0 : 0 < 2-x := by linarith
  have hy0 : 0 < 2-y := by linarith
  have hp : 1 ≤ (2-x)*(2-y) := by
    have hh := mul_le_mul (show (1:ℝ) ≤ 2-x by linarith)
      (show (1:ℝ) ≤ 2-y by linarith) (by norm_num : (0:ℝ) ≤ 1) hx0.le
    norm_num at hh ⊢
    exact hh
  have he : 3*(1-x)/(2-x)-3*(1-y)/(2-y) = 3*(y-x)/((2-x)*(2-y)) := by
    field_simp
    ring
  have hh : 3*(y-x)/((2-x)*(2-y)) ≤ 3*(y-x) :=
    div_le_self (by nlinarith) hp
  rw [← he] at hh
  linarith

/-- A one-sided modulus on the closed short-density interval. -/
theorem short_curve_modulus {x y : ℝ}
    (hx : 9/13 ≤ x) (hxy : x ≤ y) (_hy : y ≤ 5/7) :
    18*(1-x)/(7*x+3) ≤ 18*(1-y)/(7*y+3)+4*(y-x) := by
  have hx0 : 0 < 7*x+3 := by linarith
  have hy0 : 0 < 7*y+3 := by linarith
  have hp : 49 ≤ (7*x+3)*(7*y+3) := by
    have hh := mul_le_mul (show (7:ℝ) ≤ 7*x+3 by linarith)
      (show (7:ℝ) ≤ 7*y+3 by linarith) (by norm_num : (0:ℝ) ≤ 7) hx0.le
    norm_num at hh
    exact hh
  have he : 18*(1-x)/(7*x+3)-18*(1-y)/(7*y+3) =
      180*(y-x)/((7*x+3)*(7*y+3)) := by
    field_simp
    ring
  have hh : 180*(y-x)/((7*x+3)*(7*y+3)) ≤ 4*(y-x) := by
    apply (div_le_iff₀ (mul_pos hx0 hy0)).mpr
    have hm := mul_le_mul_of_nonneg_right
      (show (180:ℝ) ≤ 4*((7*x+3)*(7*y+3)) by linarith) (sub_nonneg.mpr hxy)
    nlinarith
  rw [← he] at hh
  linarith

/-- A one-sided modulus for the stronger density exponent, bounded away from zero. -/
theorem stronger_curve_modulus {x y : ℝ}
    (hx : 3/4 ≤ x) (hxy : x ≤ y) (_hy : y ≤ 1) :
    3*(1-x)/(2*x) ≤ 3*(1-y)/(2*y)+4*(y-x) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hp : (3/4:ℝ)*(3/4) ≤ x*y :=
    mul_le_mul hx (by linarith) (by norm_num) hx0.le
  have he : 3*(1-x)/(2*x)-3*(1-y)/(2*y) = 3*(y-x)/(2*x*y) := by
    field_simp
    ring
  have hh : 3*(y-x)/(2*x*y) ≤ 4*(y-x) := by
    apply (div_le_iff₀ (by positivity : 0 < 2*x*y)).mpr
    have hm := mul_le_mul_of_nonneg_right
      (show (3:ℝ) ≤ 4*(2*x*y) by nlinarith) (sub_nonneg.mpr hxy)
    nlinarith
  rw [← he] at hh
  linarith

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.ingham_curve_modulus
#print axioms GuthMaynard.Improvement.short_curve_modulus
#print axioms GuthMaynard.Improvement.stronger_curve_modulus
