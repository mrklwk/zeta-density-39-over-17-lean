module
public import Mathlib

@[expose] public section
set_option autoImplicit false
namespace Montgomery.DraftCurveComparison
/- Comparisons of explicit candidate exponents. No analytic input is assumed or proved here.
The imported rows retain the conditional status of their source notes. -/
theorem left1_strict (s : ℝ) (hl : (12/17:ℝ) < s) (hr : s ≤ (5/7:ℝ)) :
    ((6/1:ℝ)/((8/1:ℝ)*s+(-3/1:ℝ)))*(1-s) < ((18/1:ℝ)/((7/1:ℝ)*s+(3/1:ℝ)))*(1-s) := by
  have hd : 0 < (8/1:ℝ)*s+(-3/1:ℝ) := by linarith
  have he : 0 < (7/1:ℝ)*s+(3/1:ℝ) := by linarith
  apply mul_lt_mul_of_pos_right _ (by linarith : 0 < 1-s)
  apply (div_lt_div_iff₀ hd he).mpr
  nlinarith
theorem left2_strict (s : ℝ) (hl : (5/7:ℝ) ≤ s) (hr : s ≤ (113/153:ℝ)) :
    ((12/1:ℝ)/((9/1:ℝ)*s+(-1/1:ℝ)))*(1-s) < ((18/1:ℝ)/((7/1:ℝ)*s+(3/1:ℝ)))*(1-s) := by
  have hd : 0 < (9/1:ℝ)*s+(-1/1:ℝ) := by linarith
  have he : 0 < (7/1:ℝ)*s+(3/1:ℝ) := by linarith
  apply mul_lt_mul_of_pos_right _ (by linarith : 0 < 1-s)
  apply (div_lt_div_iff₀ hd he).mpr
  nlinarith
theorem left3_strict (s : ℝ) (hl : (113/153:ℝ) ≤ s) (hr : s ≤ (3/4:ℝ)) :
    ((255/1:ℝ)/((153/1:ℝ)*s+(7/1:ℝ)))*(1-s) < ((18/1:ℝ)/((7/1:ℝ)*s+(3/1:ℝ)))*(1-s) := by
  have hd : 0 < (153/1:ℝ)*s+(7/1:ℝ) := by linarith
  have he : 0 < (7/1:ℝ)*s+(3/1:ℝ) := by linarith
  apply mul_lt_mul_of_pos_right _ (by linarith : 0 < 1-s)
  apply (div_lt_div_iff₀ hd he).mpr
  nlinarith
theorem right1_strict (s : ℝ) (hl : (7/9:ℝ) < s) (hr : s ≤ (29359/37574:ℝ)) :
    ((3/1:ℝ)/((11/1:ℝ)*s+(-7/1:ℝ)))*(1-s) < ((3/1:ℝ)/((2/1:ℝ)*s+(0/1:ℝ)))*(1-s) := by
  have hd : 0 < (11/1:ℝ)*s+(-7/1:ℝ) := by linarith
  have he : 0 < (2/1:ℝ)*s+(0/1:ℝ) := by linarith
  apply mul_lt_mul_of_pos_right _ (by linarith : 0 < 1-s)
  apply (div_lt_div_iff₀ hd he).mpr
  nlinarith
theorem right2_strict (s : ℝ) (hl : (29359/37574:ℝ) ≤ s) (hr : s ≤ (1015/1294:ℝ)) :
    ((4744/1:ℝ)/((4870/1:ℝ)*s+(-1283/1:ℝ)))*(1-s) < ((3/1:ℝ)/((2/1:ℝ)*s+(0/1:ℝ)))*(1-s) := by
  have hd : 0 < (4870/1:ℝ)*s+(-1283/1:ℝ) := by linarith
  have he : 0 < (2/1:ℝ)*s+(0/1:ℝ) := by linarith
  apply mul_lt_mul_of_pos_right _ (by linarith : 0 < 1-s)
  apply (div_lt_div_iff₀ hd he).mpr
  nlinarith
theorem right3_strict (s : ℝ) (hl : (1015/1294:ℝ) ≤ s) (hr : s ≤ (353/447:ℝ)) :
    ((6154/1:ℝ)/((6354/1:ℝ)*s+(-1693/1:ℝ)))*(1-s) < ((3/1:ℝ)/((2/1:ℝ)*s+(0/1:ℝ)))*(1-s) := by
  have hd : 0 < (6354/1:ℝ)*s+(-1693/1:ℝ) := by linarith
  have he : 0 < (2/1:ℝ)*s+(0/1:ℝ) := by linarith
  apply mul_lt_mul_of_pos_right _ (by linarith : 0 < 1-s)
  apply (div_lt_div_iff₀ hd he).mpr
  nlinarith
theorem right4_strict (s : ℝ) (hl : (353/447:ℝ) ≤ s) (hr : s ≤ (467/586:ℝ)) :
    ((3782/1:ℝ)/((3936/1:ℝ)*s+(-1065/1:ℝ)))*(1-s) < ((3/1:ℝ)/((2/1:ℝ)*s+(0/1:ℝ)))*(1-s) := by
  have hd : 0 < (3936/1:ℝ)*s+(-1065/1:ℝ) := by linarith
  have he : 0 < (2/1:ℝ)*s+(0/1:ℝ) := by linarith
  apply mul_lt_mul_of_pos_right _ (by linarith : 0 < 1-s)
  apply (div_lt_div_iff₀ hd he).mpr
  nlinarith
theorem right5_strict (s : ℝ) (hl : (467/586:ℝ) ≤ s) (hr : s ≤ (4/5:ℝ)) :
    ((2168/1:ℝ)/((2282/1:ℝ)*s+(-631/1:ℝ)))*(1-s) < ((3/1:ℝ)/((2/1:ℝ)*s+(0/1:ℝ)))*(1-s) := by
  have hd : 0 < (2282/1:ℝ)*s+(-631/1:ℝ) := by linarith
  have he : 0 < (2/1:ℝ)*s+(0/1:ℝ) := by linarith
  apply mul_lt_mul_of_pos_right _ (by linarith : 0 < 1-s)
  apply (div_lt_div_iff₀ hd he).mpr
  nlinarith
theorem imported1_strict (s : ℝ) (hl : (4/5:ℝ) ≤ s) (hr : s ≤ (289/358:ℝ)) :
    ((2168/1:ℝ)/((2282/1:ℝ)*s+(-631/1:ℝ)))*(1-s) < ((3/1:ℝ)/((2/1:ℝ)*s+(0/1:ℝ)))*(1-s) := by
  have hd : 0 < (2282/1:ℝ)*s+(-631/1:ℝ) := by linarith
  have he : 0 < (2/1:ℝ)*s+(0/1:ℝ) := by linarith
  apply mul_lt_mul_of_pos_right _ (by linarith : 0 < 1-s)
  apply (div_lt_div_iff₀ hd he).mpr
  nlinarith
theorem imported2_strict (s : ℝ) (hl : (289/358:ℝ) ≤ s) (hr : s ≤ (163/198:ℝ)) :
    ((566/1:ℝ)/((606/1:ℝ)*s+(-173/1:ℝ)))*(1-s) < ((3/1:ℝ)/((2/1:ℝ)*s+(0/1:ℝ)))*(1-s) := by
  have hd : 0 < (606/1:ℝ)*s+(-173/1:ℝ) := by linarith
  have he : 0 < (2/1:ℝ)*s+(0/1:ℝ) := by linarith
  apply mul_lt_mul_of_pos_right _ (by linarith : 0 < 1-s)
  apply (div_lt_div_iff₀ hd he).mpr
  nlinarith
theorem imported3_strict (s : ℝ) (hl : (163/198:ℝ) ≤ s) (hr : s ≤ (7873/9370:ℝ)) :
    ((31544/1:ℝ)/((35670/1:ℝ)*s+(-11203/1:ℝ)))*(1-s) < ((3/1:ℝ)/((2/1:ℝ)*s+(0/1:ℝ)))*(1-s) := by
  have hd : 0 < (35670/1:ℝ)*s+(-11203/1:ℝ) := by linarith
  have he : 0 < (2/1:ℝ)*s+(0/1:ℝ) := by linarith
  apply mul_lt_mul_of_pos_right _ (by linarith : 0 < 1-s)
  apply (div_lt_div_iff₀ hd he).mpr
  nlinarith
theorem imported4_strict (s : ℝ) (hl : (7873/9370:ℝ) ≤ s) (hr : s ≤ (2018/2375:ℝ)) :
    ((1261710/1:ℝ)/((1447460/1:ℝ)*s+(-465509/1:ℝ)))*(1-s) < ((3/1:ℝ)/((2/1:ℝ)*s+(0/1:ℝ)))*(1-s) := by
  have hd : 0 < (1447460/1:ℝ)*s+(-465509/1:ℝ) := by linarith
  have he : 0 < (2/1:ℝ)*s+(0/1:ℝ) := by linarith
  apply mul_lt_mul_of_pos_right _ (by linarith : 0 < 1-s)
  apply (div_lt_div_iff₀ hd he).mpr
  nlinarith
theorem imported5_strict (s : ℝ) (hl : (2018/2375:ℝ) ≤ s) (hr : s ≤ (1959705/2298302:ℝ)) :
    ((3066/1:ℝ)/((3616/1:ℝ)*s+(-1215/1:ℝ)))*(1-s) < ((3/1:ℝ)/((2/1:ℝ)*s+(0/1:ℝ)))*(1-s) := by
  have hd : 0 < (3616/1:ℝ)*s+(-1215/1:ℝ) := by linarith
  have he : 0 < (2/1:ℝ)*s+(0/1:ℝ) := by linarith
  apply mul_lt_mul_of_pos_right _ (by linarith : 0 < 1-s)
  apply (div_lt_div_iff₀ hd he).mpr
  nlinarith
theorem imported6_strict (s : ℝ) (hl : (1959705/2298302:ℝ) ≤ s) (hr : s ≤ (6482825/7570038:ℝ)) :
    ((597962/1:ℝ)/((729216/1:ℝ)*s+(-257415/1:ℝ)))*(1-s) < ((3/1:ℝ)/((2/1:ℝ)*s+(0/1:ℝ)))*(1-s) := by
  have hd : 0 < (729216/1:ℝ)*s+(-257415/1:ℝ) := by linarith
  have he : 0 < (2/1:ℝ)*s+(0/1:ℝ) := by linarith
  apply mul_lt_mul_of_pos_right _ (by linarith : 0 < 1-s)
  apply (div_lt_div_iff₀ hd he).mpr
  nlinarith
theorem imported7_strict (s : ℝ) (hl : (6482825/7570038:ℝ) ≤ s) (hr : s ≤ (2905/3354:ℝ)) :
    ((16504356/1:ℝ)/((20732766/1:ℝ)*s+(-7623595/1:ℝ)))*(1-s) < ((3/1:ℝ)/((2/1:ℝ)*s+(0/1:ℝ)))*(1-s) := by
  have hd : 0 < (20732766/1:ℝ)*s+(-7623595/1:ℝ) := by linarith
  have he : 0 < (2/1:ℝ)*s+(0/1:ℝ) := by linarith
  apply mul_lt_mul_of_pos_right _ (by linarith : 0 < 1-s)
  apply (div_lt_div_iff₀ hd he).mpr
  nlinarith
theorem imported8_strict (s : ℝ) (hl : (2905/3354:ℝ) ≤ s) (hr : s ≤ (7/8:ℝ)) :
    ((2172/1:ℝ)/((2742/1:ℝ)*s+(-1015/1:ℝ)))*(1-s) < ((3/1:ℝ)/((2/1:ℝ)*s+(0/1:ℝ)))*(1-s) := by
  have hd : 0 < (2742/1:ℝ)*s+(-1015/1:ℝ) := by linarith
  have he : 0 < (2/1:ℝ)*s+(0/1:ℝ) := by linarith
  apply mul_lt_mul_of_pos_right _ (by linarith : 0 < 1-s)
  apply (div_lt_div_iff₀ hd he).mpr
  nlinarith
end Montgomery.DraftCurveComparison
#print axioms Montgomery.DraftCurveComparison.left1_strict
#print axioms Montgomery.DraftCurveComparison.right1_strict
#print axioms Montgomery.DraftCurveComparison.imported8_strict
