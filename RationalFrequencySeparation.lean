module
public import RationalGcdDecomposition

@[expose] public section

/-! Unconditional logarithmic separation of distinct rational frequencies.
This supplies the spacing input for a finite-height mean-square argument;
the mean-square transfer itself is not asserted here. -/
set_option autoImplicit false
noncomputable section

namespace Montgomery.RationalMoment

theorem ordered_ratio_gap {a b c d : ℕ} (hb : 0 < b) (hd : 0 < d)
    {H : ℝ} (hbH : (b : ℝ) ≤ H) (hdH : (d : ℝ) ≤ H)
    (hlt : (a : ℝ) / b < (c : ℝ) / d) :
    1 / H ^ 2 ≤ (c : ℝ) / d - (a : ℝ) / b := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hH : 0 < H := hbR.trans_le hbH
  have hcross : a * d < c * b := by
    exact_mod_cast (div_lt_div_iff₀ hbR hdR).mp hlt
  have hgap : (1 : ℝ) ≤ (c : ℝ) * b - (a : ℝ) * d := by
    have hh : (a : ℝ) * d + 1 ≤ (c : ℝ) * b := by
      exact_mod_cast Nat.add_one_le_iff.mpr hcross
    linarith
  have he : ((c : ℝ) / d - (a : ℝ) / b) * (b * d) = c * b - a * d := by
    field_simp
  have hprod : (b : ℝ) * d ≤ H ^ 2 := by
    nlinarith [mul_le_mul hbH hdH hdR.le hH.le]
  apply (div_le_iff₀ (sq_pos_of_pos hH)).mpr
  calc
    1 ≤ ((c : ℝ) / d - (a : ℝ) / b) * (b * d) := by rw [he]; exact hgap
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (sub_nonneg.mpr hlt.le)

/-- A logarithmic gap controls the original gap with the upper endpoint U. -/
theorem ordered_log_gap {x y U : ℝ} (hx : 0 < x) (hxy : x < y) (hyU : y ≤ U) :
    (y - x) / U ≤ Real.log y - Real.log x := by
  have hy : 0 < y := hx.trans hxy
  have hU : 0 < U := hy.trans_le hyU
  have hlog : 0 ≤ Real.log y - Real.log x :=
    sub_nonneg.mpr (Real.log_le_log hx hxy.le)
  have hh := Real.log_le_sub_one_of_pos (div_pos hx hy)
  rw [Real.log_div hx.ne' hy.ne'] at hh
  have hb : y - x ≤ y * (Real.log y - Real.log x) := by
    have hm := mul_le_mul_of_nonneg_right hh hy.le
    simp only [sub_mul, div_mul_cancel₀ _ hy.ne', one_mul] at hm
    nlinarith
  exact (div_le_iff₀ hU).mpr
    (hb.trans (by nlinarith [mul_le_mul_of_nonneg_right hyU hlog]))

/-- Denominator height H and ratio bound U give spacing at least 1/(U H²).
No separation estimate is a premise; only distinct positive reduced pairs. -/
theorem rational_log_separation {p q : ℕ × ℕ}
    (hp : 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2)
    (hq : 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2)
    (hpq : p ≠ q) {H U : ℝ}
    (hpH : (p.2 : ℝ) ≤ H) (hqH : (q.2 : ℝ) ≤ H)
    (hpU : (p.1 : ℝ) / p.2 ≤ U) (hqU : (q.1 : ℝ) / q.2 ≤ U) :
    1 / (U * H ^ 2) ≤
      |Real.log ((p.1 : ℝ) / p.2) - Real.log ((q.1 : ℝ) / q.2)| := by
  have hp0 : (0 : ℝ) < (p.1 : ℝ) / p.2 :=
    div_pos (by exact_mod_cast hp.1) (by exact_mod_cast hp.2.1)
  have hq0 : (0 : ℝ) < (q.1 : ℝ) / q.2 :=
    div_pos (by exact_mod_cast hq.1) (by exact_mod_cast hq.2.1)
  have hU : 0 < U := hp0.trans_le hpU
  have hne : (p.1 : ℝ) / p.2 ≠ (q.1 : ℝ) / q.2 := by
    intro he
    apply hpq
    apply pair_ratio_injective hp.2.1 hq.2.1 hp.2.2 hq.2.2
    unfold pairRatio
    apply Rat.cast_injective (α := ℝ)
    simpa only [Rat.cast_div, Rat.cast_natCast] using he
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hg := ordered_ratio_gap hp.2.1 hq.2.1 hpH hqH hlt
    have hl := ordered_log_gap hp0 hlt hqU
    rw [abs_sub_comm, abs_of_nonneg
      (sub_nonneg.mpr (Real.log_le_log hp0 hlt.le))]
    calc
      _ = (1 / H ^ 2) / U := by ring
      _ ≤ _ := (div_le_div_of_nonneg_right hg hU.le).trans hl
  · have hg := ordered_ratio_gap hq.2.1 hp.2.1 hqH hpH hgt
    have hl := ordered_log_gap hq0 hgt hpU
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hq0 hgt.le))]
    calc
      _ = (1 / H ^ 2) / U := by ring
      _ ≤ _ := (div_le_div_of_nonneg_right hg hU.le).trans hl

end Montgomery.RationalMoment

#print axioms Montgomery.RationalMoment.ordered_ratio_gap
#print axioms Montgomery.RationalMoment.ordered_log_gap
#print axioms Montgomery.RationalMoment.rational_log_separation
