module
public import Mathlib

@[expose] public section
set_option autoImplicit false
namespace GuthMaynard.Improvement

/-- Exact strip-to-window conversion, including a negative denominator. -/
theorem cubic_strip_window {m₁ m₂ m₃ v y h : ℝ} (hm₂ : m₂ ≠ 0) :
    |m₁*v+m₂*y+m₃| ≤ h ↔ |y-(-(m₁*v+m₃)/m₂)| ≤ h/|m₂| := by
  have hid : y-(-(m₁*v+m₃)/m₂) = (m₁*v+m₂*y+m₃)/m₂ := by field_simp; ring
  rw [hid,abs_div]
  exact (div_le_div_iff_of_pos_right (abs_pos.mpr hm₂)).symm

/-- Inversion interchanges the original slope and translation exactly. -/
theorem cubic_affine_inversion {m₁ m₂ m₃ v : ℝ} (hm₂ : m₂ ≠ 0) (hv : v ≠ 0) :
    (-(m₁*v+m₃)/m₂)/v = -(m₃*(1/v)+m₁)/m₂ := by
  field_simp
  ring

/-- The negative-denominator box is sent to a positive denominator by
reversing all three modes; no sign of a Fourier factor is changed here. -/
theorem cubic_negative_denominator {m₁ m₂ m₃ v : ℝ} (hm₂ : m₂ < 0) :
    -(m₁*v+m₃)/m₂ = (m₁*v+m₃)/|m₂| := by
  rw [abs_of_neg hm₂]
  ring

/-- Quantitative cancellation bound on the actual compact ratio domain. -/
theorem cubic_strip_outer_bound {m₁ m₂ m₃ v y a b h : ℝ}
    (ha : 0 < a) (hav : a ≤ v) (hvb : v ≤ b) (hay : a ≤ y) (hyb : y ≤ b)
    (hstrip : |m₁*v+m₂*y+m₃| ≤ h) :
    a*|m₁| ≤ b*|m₂|+|m₃|+h ∧ |m₃| ≤ b*|m₁|+b*|m₂|+h := by
  have hv : 0 < v := ha.trans_le hav
  have hy : 0 < y := ha.trans_le hay
  have hsub : ∀ u w : ℝ, |u-w| ≤ |u|+|w| := fun u w => by
    simpa only [sub_eq_add_neg,abs_neg] using abs_add_le u (-w)
  have h₁ : |m₁*v| ≤ |m₁*v+m₂*y+m₃|+|m₂*y|+|m₃| := by
    calc
      _ = |(m₁*v+m₂*y+m₃)-(m₂*y)-m₃| := by congr 1; ring
      _ ≤ |m₁*v+m₂*y+m₃|+|m₂*y|+|m₃| := (hsub _ _).trans (by linarith [hsub (m₁*v+m₂*y+m₃) (m₂*y)])
  have h₃ : |m₃| ≤ |m₁*v+m₂*y+m₃|+|m₁*v|+|m₂*y| := by
    calc
      _ = |(m₁*v+m₂*y+m₃)-(m₁*v)-(m₂*y)| := by congr 1; ring
      _ ≤ |m₁*v+m₂*y+m₃|+|m₁*v|+|m₂*y| := (hsub _ _).trans (by linarith [hsub (m₁*v+m₂*y+m₃) (m₁*v)])
  rw [abs_mul,abs_of_pos hv,abs_mul,abs_of_pos hy] at h₁ h₃
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hav (abs_nonneg m₁),mul_le_mul_of_nonneg_left hyb (abs_nonneg m₂)]
  · nlinarith [mul_le_mul_of_nonneg_left hvb (abs_nonneg m₁),mul_le_mul_of_nonneg_left hyb (abs_nonneg m₂)]

/-- In the genuinely unequal denominator regime, both numerator modes are
comparable. Constants and the required strip width are explicit. -/
theorem cubic_small_denominator_outer_comparable {m₁ m₂ m₃ v y a b h : ℝ}
    (ha : 0 < a) (hav : a ≤ v) (hvb : v ≤ b) (hay : a ≤ y) (hyb : y ≤ b)
    (hstrip : |m₁*v+m₂*y+m₃| ≤ h)
    (hsmall : b*|m₂| ≤ a*|m₁|/4) (hthin : h ≤ a*|m₁|/4) :
    (a/2)*|m₁| ≤ |m₃| ∧ |m₃| ≤ (b+a/2)*|m₁| := by
  obtain ⟨h₁,h₃⟩ := cubic_strip_outer_bound ha hav hvb hay hyb hstrip
  constructor <;> nlinarith

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.cubic_strip_window
#print axioms GuthMaynard.Improvement.cubic_affine_inversion
#print axioms GuthMaynard.Improvement.cubic_negative_denominator
#print axioms GuthMaynard.Improvement.cubic_strip_outer_bound
#print axioms GuthMaynard.Improvement.cubic_small_denominator_outer_comparable
