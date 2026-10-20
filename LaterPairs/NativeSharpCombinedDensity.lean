module
public import LaterPairs.NativeSharpRows78
public import LaterPairs.NativeSharpRow5Suffix

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density.Stronger MathCollab.Density

/-- The exact requested exponents on the explicitly covered later intervals.
The first branch is used only on the proved row5 suffix. -/
def sharpLaterExponent (σ : ℝ) : ℝ :=
  if σ ≤ 1959705/2298302 then 3066*(1-σ)/(3616*σ-1215)
  else if σ ≤ 6482825/7570038 then 597962*(1-σ)/(729216*σ-257415)
  else if σ ≤ 2905/3354 then 16504356*(1-σ)/(20732766*σ-7623595)
  else 2172*(1-σ)/(2742*σ-1015)

theorem sharpLaterExponent_join5 :
    3066*(1-(1959705/2298302:ℝ))/(3616*(1959705/2298302)-1215) =
    597962*(1-(1959705/2298302:ℝ))/(729216*(1959705/2298302)-257415) := by norm_num

theorem sharpLaterExponent_join6 :
    597962*(1-(6482825/7570038:ℝ))/(729216*(6482825/7570038)-257415) =
    16504356*(1-(6482825/7570038:ℝ))/(20732766*(6482825/7570038)-7623595) := by norm_num

theorem sharpLaterExponent_join7 :
    16504356*(1-(2905/3354:ℝ))/(20732766*(2905/3354)-7623595) =
    2172*(1-(2905/3354:ℝ))/(2742*(2905/3354)-1015) := by norm_num

/-- Actual symmetric zeros with analytic multiplicity on the precise proved
closed span; no conclusion outside this span is implied. -/
theorem density_sharp_later_combined {σ ε : ℝ}
    (hlo : 5553/6526 ≤ σ) (hhi : σ ≤ 7/8) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(sharpLaterExponent σ+ε) := by
  by_cases h5 : σ ≤ 1959705/2298302
  · simpa only [sharpLaterExponent,ite_eq_left h5] using
      density_sharp_row5_suffix hlo h5 hε
  by_cases h6 : σ ≤ 6482825/7570038
  · simpa only [sharpLaterExponent,ite_eq_right h5,ite_eq_left h6] using
      density_sharp_row6 (le_of_not_ge h5) h6 hε
  by_cases h7 : σ ≤ 2905/3354
  · simpa only [sharpLaterExponent,ite_eq_right h5,ite_eq_right h6,ite_eq_left h7] using
      density_sharp_row7 (le_of_not_ge h6) h7 hε
  · simpa only [sharpLaterExponent,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7] using
      density_sharp_row8 (le_of_not_ge h7) hhi hε

theorem sharpLaterExponent_lt_preserved {σ : ℝ}
    (hlo : 5553/6526 ≤ σ) (hhi : σ ≤ 7/8) :
    sharpLaterExponent σ < Montgomery.PeakTailDensity.exponent σ := by
  by_cases h5 : σ ≤ 1959705/2298302
  · simpa only [sharpLaterExponent,ite_eq_left h5] using
      sharp_row5_suffix_preserved_exponent_comparison hlo h5
  by_cases h6 : σ ≤ 6482825/7570038
  · simpa only [sharpLaterExponent,ite_eq_right h5,ite_eq_left h6] using
      sharp_row6_preserved_exponent_comparison (le_of_not_ge h5) h6
  by_cases h7 : σ ≤ 2905/3354
  · simpa only [sharpLaterExponent,ite_eq_right h5,ite_eq_right h6,ite_eq_left h7] using
      sharp_row7_preserved_exponent_comparison (le_of_not_ge h6) h7
  · simpa only [sharpLaterExponent,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7] using
      sharp_row8_preserved_exponent_comparison (le_of_not_ge h7) hhi

theorem sharpLaterExponent_lt_palomar {σ : ℝ}
    (hlo : 5553/6526 ≤ σ) (hhi : σ ≤ 7/8) :
    sharpLaterExponent σ < 3*(1-σ)/(2*σ) := by
  by_cases h5 : σ ≤ 1959705/2298302
  · simpa only [sharpLaterExponent,ite_eq_left h5] using
      sharp_row5_suffix_palomar_exponent_comparison hlo h5
  by_cases h6 : σ ≤ 6482825/7570038
  · simpa only [sharpLaterExponent,ite_eq_right h5,ite_eq_left h6] using
      sharp_row6_palomar_exponent_comparison (le_of_not_ge h5) h6
  by_cases h7 : σ ≤ 2905/3354
  · simpa only [sharpLaterExponent,ite_eq_right h5,ite_eq_right h6,ite_eq_left h7] using
      sharp_row7_palomar_exponent_comparison (le_of_not_ge h6) h7
  · simpa only [sharpLaterExponent,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7] using
      sharp_row8_palomar_exponent_comparison (le_of_not_ge h7) hhi

end Montgomery.RationalMoment.RightDetector.Physical
