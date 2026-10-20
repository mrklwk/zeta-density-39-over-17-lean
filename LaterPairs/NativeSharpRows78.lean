module
public import LaterPairs.Native.HuxleyCore
public import LaterPairs.NativeSharpRow6

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace TaoTrudgianYang2025
open Expdb

theorem exponentPair_taoTrudgianYang_firstNew : ExponentPair (89/1282) (997/1282) := by
  apply exponentPair_of_beta_bound_half
    (by norm_num [InExponentPairTriangle]) (by norm_num)
  intro α hhalf
  have hα : (α:ℝ) ≤ 1 := by linarith only [hhalf]
  by_cases h0 : (α:ℝ) ≤ 861996/2811205
  · have h := CubicJointCount.exponentSumGrowthExponent_le_trudgianYang_sixthRow hα
    unfold exponentPairLine
    linarith only [h,h0]
  by_cases hr0 : (α:ℝ) ≤ 87/275
  · have h := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_seventhRow (α:=α) (by linarith only [lt_of_not_ge h0]) hr0
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge h0,hr0]
  by_cases hr1 : (α:ℝ) ≤ 423/1295
  · have h := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_eighthRow (α:=α) (by linarith only [lt_of_not_ge hr0]) hr1
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr0,hr1]
  by_cases hr2 : (α:ℝ) ≤ 227/601
  · have h := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_ninthRow (α:=α) (by linarith only [lt_of_not_ge hr1]) hr2
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr1,hr2]
  by_cases hr3 : (α:ℝ) ≤ 12/31
  · have h := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_tenthRow (α:=α) (by linarith only [lt_of_not_ge hr2]) hr3
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr2,hr3]
  by_cases hr4 : (α:ℝ) ≤ 1508/3825
  · have h := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_eleventhRow (α:=α) (by linarith only [lt_of_not_ge hr3]) hr4
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr3,hr4]
  have h := CubicJointCount.exponentSumGrowthExponent_le_sargosD_bourgain (α:=α) hα
  unfold exponentPairLine at h ⊢
  linarith only [h,lt_of_not_ge hr4]

/-- The second new pair in the published theorem, with every beta input discharged. -/
theorem exponentPair_taoTrudgianYang_secondNew : ExponentPair (652397/9713986) (7599781/9713986) := by
  apply exponentPair_of_beta_bound_half
    (by norm_num [InExponentPairTriangle]) (by norm_num)
  intro α hhalf
  have hα : (α:ℝ) ≤ 1 := by linarith only [hhalf]
  by_cases h0 : (α:ℝ) ≤ 861996/2811205
  · have h := CubicJointCount.exponentSumGrowthExponent_le_trudgianYang_sixthRow hα
    unfold exponentPairLine
    linarith only [h,h0]
  by_cases hr0 : (α:ℝ) ≤ 87/275
  · have h := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_seventhRow (α:=α) (by linarith only [lt_of_not_ge h0]) hr0
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge h0,hr0]
  by_cases hr1 : (α:ℝ) ≤ 423/1295
  · have h := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_eighthRow (α:=α) (by linarith only [lt_of_not_ge hr0]) hr1
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr0,hr1]
  by_cases hr2 : (α:ℝ) ≤ 227/601
  · have h := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_ninthRow (α:=α) (by linarith only [lt_of_not_ge hr1]) hr2
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr1,hr2]
  by_cases hr3 : (α:ℝ) ≤ 12/31
  · have h := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_tenthRow (α:=α) (by linarith only [lt_of_not_ge hr2]) hr3
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr2,hr3]
  by_cases hr4 : (α:ℝ) ≤ 1508/3825
  · have h := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_eleventhRow (α:=α) (by linarith only [lt_of_not_ge hr3]) hr4
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr3,hr4]
  have h := CubicJointCount.exponentSumGrowthExponent_le_sargosD_bourgain (α:=α) hα
  unfold exponentPairLine at h ⊢
  linarith only [h,lt_of_not_ge hr4]

/-- Exact B image of the second native new TTY pair. -/
theorem exponentPair_BTTY2 : ExponentPair (1371394/4856993) (2754695/4856993) := by
  convert exponentPair_taoTrudgianYang_secondNew.bProcess using 1 <;> norm_num

/-- Exact B image of the first native new TTY pair. -/
theorem exponentPair_BTTY1 : ExponentPair (178/641) (365/641) := by
  convert exponentPair_taoTrudgianYang_firstNew.bProcess using 1 <;> norm_num
end TaoTrudgianYang2025

namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density.Stronger MathCollab.Density

/-- Full closed later row7 for actual symmetric zeros with analytic multiplicity. -/
theorem density_sharp_row7 {σ ε : ℝ}
    (hlo : 6482825/7570038 ≤ σ) (hhi : σ ≤ 2905/3354) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : ℝ,2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤
        C*T^(16504356*(1-σ)/(20732766*σ-7623595)+ε) := by
  obtain ⟨hf,hs⟩ := sharp_row7_tail_budgets hlo hhi
  simpa only [sharp_row7_density_exponent] using
    density_of_pair_sharp_window TaoTrudgianYang2025.exponentPair_BTTY2
      (by norm_num) (physicalDetectorWindow_row7 hlo hhi)
      (sharpCountWindow_row7 hlo hhi) hf hs hε

/-- Full closed later row8 for actual symmetric zeros with analytic multiplicity. -/
theorem density_sharp_row8 {σ ε : ℝ}
    (hlo : 2905/3354 ≤ σ) (hhi : σ ≤ 7/8) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : ℝ,2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(2172*(1-σ)/(2742*σ-1015)+ε) := by
  obtain ⟨hf,hs⟩ := sharp_row8_tail_budgets hlo hhi
  simpa only [sharp_row8_density_exponent] using
    density_of_pair_sharp_window TaoTrudgianYang2025.exponentPair_BTTY1
      (by norm_num) (physicalDetectorWindow_row8 hlo hhi)
      (sharpCountWindow_row8 hlo hhi) hf hs hε
end Montgomery.RationalMoment.RightDetector.Physical
