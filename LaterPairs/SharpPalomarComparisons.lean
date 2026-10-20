module
public import LaterPairs.SharpTargetTailBudgets

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

/-- Strict comparison with the recorded Palomar exponent on the entire
closed row6. This is an exponent comparison, not an analytic premise. -/
theorem sharp_row6_palomar_exponent_comparison {σ : ℝ}
    (hlo : 1959705/2298302 ≤ σ) (hhi : σ ≤ 6482825/7570038) :
    597962*(1-σ)/(729216*σ-257415) < 3*(1-σ)/(2*σ) := by
  have hs : 0 < σ := by linarith
  have hg : 0 < 1-σ := by linarith
  have hd : 0 < 729216*σ-257415 := by linarith
  apply (div_lt_div_iff₀ hd (show 0 < 2*σ by positivity)).mpr
  have hm : 2*597962*σ < 3*(729216*σ-257415) := by linarith
  have hh := mul_lt_mul_of_pos_left hm hg
  nlinarith only [hh]

/-- Strict comparison with the recorded Palomar exponent on the entire
closed row7. This is an exponent comparison, not an analytic premise. -/
theorem sharp_row7_palomar_exponent_comparison {σ : ℝ}
    (hlo : 6482825/7570038 ≤ σ) (hhi : σ ≤ 2905/3354) :
    16504356*(1-σ)/(20732766*σ-7623595) < 3*(1-σ)/(2*σ) := by
  have hs : 0 < σ := by linarith
  have hg : 0 < 1-σ := by linarith
  have hd : 0 < 20732766*σ-7623595 := by linarith
  apply (div_lt_div_iff₀ hd (show 0 < 2*σ by positivity)).mpr
  have hm : 2*16504356*σ < 3*(20732766*σ-7623595) := by linarith
  have hh := mul_lt_mul_of_pos_left hm hg
  nlinarith only [hh]

/-- Strict comparison with the recorded Palomar exponent on the entire
closed row8. This is an exponent comparison, not an analytic premise. -/
theorem sharp_row8_palomar_exponent_comparison {σ : ℝ}
    (hlo : 2905/3354 ≤ σ) (hhi : σ ≤ 7/8) :
    2172*(1-σ)/(2742*σ-1015) < 3*(1-σ)/(2*σ) := by
  have hs : 0 < σ := by linarith
  have hg : 0 < 1-σ := by linarith
  have hd : 0 < 2742*σ-1015 := by linarith
  apply (div_lt_div_iff₀ hd (show 0 < 2*σ by positivity)).mpr
  have hm : 2*2172*σ < 3*(2742*σ-1015) := by linarith
  have hh := mul_lt_mul_of_pos_left hm hg
  nlinarith only [hh]

end Montgomery.RationalMoment
