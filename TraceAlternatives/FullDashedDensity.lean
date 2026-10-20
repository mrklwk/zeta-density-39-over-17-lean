module
public import TraceAlternatives.NativeUniversalRows45
public import LaterPairs.NativeSharpCombinedDensity
public import DashedInitialActualDensity

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density

/-- The exact eight original orange dashed pieces, now with unconditional
actual-zero consumers on every full closed segment. -/
def fullDashedExponent (σ : ℝ) : ℝ :=
  if σ ≤ 289/358 then 2168*(1-σ)/(2282*σ-631)
  else if σ ≤ 163/198 then 566*(1-σ)/(606*σ-173)
  else if σ ≤ 7873/9370 then 31544*(1-σ)/(35670*σ-11203)
  else if σ ≤ 2018/2375 then 1261710*(1-σ)/(1447460*σ-465509)
  else sharpLaterExponent σ

theorem fullDashedExponent_join1 :
    2168*(1-(289/358:ℝ))/(2282*(289/358)-631) =
    566*(1-(289/358:ℝ))/(606*(289/358)-173) := by norm_num

theorem fullDashedExponent_join2 :
    566*(1-(163/198:ℝ))/(606*(163/198)-173) =
    31544*(1-(163/198:ℝ))/(35670*(163/198)-11203) := by norm_num

theorem fullDashedExponent_join3 :
    31544*(1-(7873/9370:ℝ))/(35670*(7873/9370)-11203) =
    1261710*(1-(7873/9370:ℝ))/(1447460*(7873/9370)-465509) := by norm_num

theorem fullDashedExponent_join4 :
    1261710*(1-(2018/2375:ℝ))/(1447460*(2018/2375)-465509) =
    3066*(1-(2018/2375:ℝ))/(3616*(2018/2375)-1215) := by norm_num

/-- The full requested eight-piece span, with all exact exponents, actual
symmetric zeta-zero analytic multiplicity and every real height T>=2. -/
theorem density_full_dashed {σ ε : ℝ}
    (hlo : 4/5 ≤ σ) (hhi : σ ≤ 7/8) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ T : ℝ, 2≤T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(fullDashedExponent σ+ε) := by
  by_cases h1 : σ ≤ 289/358
  · simpa only [fullDashedExponent,ite_eq_left h1] using density_dashed_first hlo h1 hε
  by_cases h2 : σ ≤ 163/198
  · simpa only [fullDashedExponent,ite_eq_right h1,ite_eq_left h2] using
      density_dashed_second (le_of_not_ge h1) h2 hε
  by_cases h3 : σ ≤ 7873/9370
  · simpa only [fullDashedExponent,ite_eq_right h1,ite_eq_right h2,ite_eq_left h3] using
      density_cube_row3 (le_of_not_ge h2) h3 hε
  by_cases h4 : σ ≤ 2018/2375
  · simpa only [fullDashedExponent,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_left h4] using
      density_universal_row4 (le_of_not_ge h3) h4 hε
  by_cases h5 : σ ≤ 1959705/2298302
  · simpa only [fullDashedExponent,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,
      sharpLaterExponent,ite_eq_left h5] using density_universal_row5 (le_of_not_ge h4) h5 hε
  by_cases h6 : σ ≤ 6482825/7570038
  · simpa only [fullDashedExponent,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,
      sharpLaterExponent,ite_eq_right h5,ite_eq_left h6] using density_sharp_row6 (le_of_not_ge h5) h6 hε
  by_cases h7 : σ ≤ 2905/3354
  · simpa only [fullDashedExponent,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,
      sharpLaterExponent,ite_eq_right h5,ite_eq_right h6,ite_eq_left h7] using
      density_sharp_row7 (le_of_not_ge h6) h7 hε
  · simpa only [fullDashedExponent,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,
      sharpLaterExponent,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7] using
      density_sharp_row8 (le_of_not_ge h7) hhi hε

end Montgomery.RationalMoment.RightDetector.Physical
