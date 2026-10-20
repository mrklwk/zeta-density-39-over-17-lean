module
public import WrittenDensity.AllWritten
public import GuthMaynard.Improvement.CurveUniformization

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Montgomery.WrittenDensity

/-- Uniform modulus for all linear fractional source exponents after their
positive denominator has been normalized to be at least one. -/
theorem linear_fraction_modulus {a b c d x y : ℝ}
    (hxy : x ≤ y) (hx : 1 ≤ c+d*x) (hy : 1 ≤ c+d*y)
    (hdet : 0 ≤ a*d-b*c) :
    (a+b*x)/(c+d*x) ≤ (a+b*y)/(c+d*y)+(a*d-b*c+1)*(y-x) := by
  have hx0 : 0 < c+d*x := by linarith
  have hy0 : 0 < c+d*y := by linarith
  have hp : 1 ≤ (c+d*x)*(c+d*y) := by
    have h := mul_le_mul hx hy (by norm_num : (0:ℝ) ≤ 1) hx0.le
    simpa only [one_mul] using h
  have he : (a+b*x)/(c+d*x)-(a+b*y)/(c+d*y) =
      (a*d-b*c)*(y-x)/((c+d*x)*(c+d*y)) := by
    rw [div_sub_div _ _ hx0.ne' hy0.ne']
    congr 1
    ring
  have hnum : 0 ≤ (a*d-b*c)*(y-x) := mul_nonneg hdet (sub_nonneg.mpr hxy)
  have hh : (a*d-b*c)*(y-x)/((c+d*x)*(c+d*y)) ≤ (a*d-b*c+1)*(y-x) := by
    apply (div_le_iff₀ (mul_pos hx0 hy0)).mpr
    have hm := mul_le_mul_of_nonneg_right hp hnum
    have hm' := mul_le_mul_of_nonneg_right hp (sub_nonneg.mpr hxy)
    nlinarith only [hm,hm',hxy]
  rw [← he] at hh
  linarith

end Montgomery.WrittenDensity
