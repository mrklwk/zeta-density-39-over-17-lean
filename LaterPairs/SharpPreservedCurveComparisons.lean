module
public import LaterPairs.SharpPalomarComparisons
public import PeakTailCombinedDensity

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

/-- The already proved native-twelfth continuation in the range of the new
sharp rows. This refers to the actual preserved density-curve definition. -/
theorem preserved_peak_tail_exponent_on_sharp_rows {σ : ℝ} (hs : 5/6 < σ) :
    Montgomery.PeakTailDensity.exponent σ = 6*(1-σ)/(3*σ+1) := by
  simp only [Montgomery.PeakTailDensity.exponent,
    ite_eq_right (show ¬ σ ≤ 7/9 by linarith),
    ite_eq_right (show ¬ σ ≤ 4/5 by linarith),
    ite_eq_right (show ¬ σ ≤ 289/358 by linarith),
    ite_eq_right (show ¬ σ ≤ 163/198 by linarith),
    ite_eq_right (show ¬ σ ≤ 491/596 by linarith),
    ite_eq_right (show ¬ σ ≤ 5/6 by linarith)]

/-- The target row6 strictly improves the complete preserved curve,
which already improves the recorded Palomar curve in this range. -/
theorem sharp_row6_preserved_exponent_comparison {σ : ℝ}
    (hlo : 1959705/2298302 ≤ σ) (hhi : σ ≤ 6482825/7570038) :
    597962*(1-σ)/(729216*σ-257415) < Montgomery.PeakTailDensity.exponent σ := by
  rw [preserved_peak_tail_exponent_on_sharp_rows (by linarith)]
  have hs : 0 < σ := by linarith
  have hg : 0 < 1-σ := by linarith
  have hd : 0 < 729216*σ-257415 := by linarith
  apply (div_lt_div_iff₀ hd (show 0 < 3*σ+1 by positivity)).mpr
  have hm : 597962*(3*σ+1) < 6*(729216*σ-257415) := by linarith
  have hh := mul_lt_mul_of_pos_left hm hg
  nlinarith only [hh]

/-- The target row7 strictly improves the complete preserved curve,
which already improves the recorded Palomar curve in this range. -/
theorem sharp_row7_preserved_exponent_comparison {σ : ℝ}
    (hlo : 6482825/7570038 ≤ σ) (hhi : σ ≤ 2905/3354) :
    16504356*(1-σ)/(20732766*σ-7623595) < Montgomery.PeakTailDensity.exponent σ := by
  rw [preserved_peak_tail_exponent_on_sharp_rows (by linarith)]
  have hs : 0 < σ := by linarith
  have hg : 0 < 1-σ := by linarith
  have hd : 0 < 20732766*σ-7623595 := by linarith
  apply (div_lt_div_iff₀ hd (show 0 < 3*σ+1 by positivity)).mpr
  have hm : 16504356*(3*σ+1) < 6*(20732766*σ-7623595) := by linarith
  have hh := mul_lt_mul_of_pos_left hm hg
  nlinarith only [hh]

/-- The target row8 strictly improves the complete preserved curve,
which already improves the recorded Palomar curve in this range. -/
theorem sharp_row8_preserved_exponent_comparison {σ : ℝ}
    (hlo : 2905/3354 ≤ σ) (hhi : σ ≤ 7/8) :
    2172*(1-σ)/(2742*σ-1015) < Montgomery.PeakTailDensity.exponent σ := by
  rw [preserved_peak_tail_exponent_on_sharp_rows (by linarith)]
  have hs : 0 < σ := by linarith
  have hg : 0 < 1-σ := by linarith
  have hd : 0 < 2742*σ-1015 := by linarith
  apply (div_lt_div_iff₀ hd (show 0 < 3*σ+1 by positivity)).mpr
  have hm : 2172*(3*σ+1) < 6*(2742*σ-1015) := by linarith
  have hh := mul_lt_mul_of_pos_left hm hg
  nlinarith only [hh]

end Montgomery.RationalMoment
