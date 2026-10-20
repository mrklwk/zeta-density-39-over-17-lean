module
public import LaterPairs.Native.HuxleyCore
public import LaterPairs.Native.SquareProductCount
public import LaterPairs.HeathBrownRows
public import LaterPairs.RestrictedPeakTail
public import TaoTrudgianYang2025.BetaHalfDuality
public import TaoTrudgianYang2025.ExponentPairBProcess

@[expose] public section
set_option autoImplicit false
noncomputable section
open Expdb Filter Finset
open scoped NNReal
open MathCollab.Density MathCollab.Density.Stronger MathCollab.Density.Stronger.Peaks
namespace TaoTrudgianYang2025
private theorem taoTrudgianYang_fourthNew_half_beta
    {α : ℝ≥0} (hhalf : (α:ℝ)≤1/2) :
    Expdb.exponentSumGrowthExponent α≤89/3478+(7441/8695)*(α:ℝ) := by
  by_cases hpos : 0<(α:ℝ)
  swap
  · have hz : α=0 := NNReal.coe_injective (le_antisymm (le_of_not_gt hpos) α.coe_nonneg)
    subst α
    rw [exponentSumGrowthExponent_zero]
    norm_num
  by_cases h7 : (α:ℝ)≤1/6
  · have hh := exponentSumGrowthExponent_le_heathBrown_of_derivative
      GafniTao.heathBrownKthDerivativeTheorem_native (by norm_num : 3≤(7:ℕ)) hpos
    apply hh.trans
    rw [heathBrownBetaBound_eq_max (by norm_num : 3≤(7:ℕ))]
    norm_num [heathBrownDerivativeExponent,heathBrownInverseExponent]
    refine ⟨?_,?_,?_⟩ <;> linarith only [h7,α.coe_nonneg]
  by_cases h6 : (α:ℝ)≤3/13
  · have hh := exponentSumGrowthExponent_le_heathBrown_of_derivative
      GafniTao.heathBrownKthDerivativeTheorem_native (by norm_num : 3≤(6:ℕ)) hpos
    apply hh.trans
    rw [heathBrownBetaBound_eq_max (by norm_num : 3≤(6:ℕ))]
    norm_num [heathBrownDerivativeExponent,heathBrownInverseExponent]
    refine ⟨?_,?_,?_⟩ <;> linarith only [lt_of_not_ge h7,h6]
  by_cases h5 : (α:ℝ)≤1/4
  · have hh := exponentSumGrowthExponent_le_heathBrown_firstRow h5
    linarith only [hh,lt_of_not_ge h6]
  by_cases hlo : (α:ℝ)≤890/3277
  · have hh := exponentSumGrowthExponent_le_heathBrown_secondRow (le_of_not_ge h5) hlo
    linarith only [hh,hlo]
  by_cases hhi : (α:ℝ)≤17604372/60424193
  · exact HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_fourthPair_shortRange
      (le_of_not_ge hlo) hhi
  have hh := CubicJointCount.exponentSumGrowthExponent_le_trudgianYang_sixthRow
    (α:=α) (by linarith only [hhalf])
  linarith only [hh,lt_of_not_ge hhi]


/-- The fourth new analytic exponent pair, obtained from complete beta
coverage, not from a rational triangle certificate or an assumed pair. -/
theorem exponentPair_taoTrudgianYang_fourthNew :
    ExponentPair (89/3478) (15327/17390) := by
  apply exponentPair_of_beta_bound_half
    (by norm_num [InExponentPairTriangle]) (by norm_num)
  intro α hhalf
  have hh := taoTrudgianYang_fourthNew_half_beta hhalf
  unfold exponentPairLine
  linarith only [hh]


/-- Exact B-process image of the genuine native TTY4 analytic pair. -/
theorem exponentPair_BTTY4 : ExponentPair (3316/8695) (914/1739) := by
  convert exponentPair_taoTrudgianYang_fourthNew.bProcess using 1 <;> norm_num

/-- Actual critical-zeta peak tail from the native pair and native zeta sources. -/
theorem critical_peak_tail_BTTY4 {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ H : ℝ in atTop, ∀ V : ℝ,0 < V → H^(1/8+η) ≤ V →
      ∀ W : Finset ℝ,oneSeparated W →
        (∀ t ∈ W,H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W,V ≤ zetaMomentCriticalNorm t) →
        (W.card:ℝ) ≤ H^ε*(H/V^6+H^((3943:ℝ)/1658)/V^((24467:ℝ)/1658)) := by
  simpa only [show (1:ℝ)+(914/1739)/(3316/8695)=3943/1658 by norm_num,
    show (4:ℝ)+(2+4*(914/1739))/(3316/8695)=24467/1658 by norm_num] using
    exponentPair_BTTY4.restricted_critical_peak_tail_general (by norm_num) hη hε
end TaoTrudgianYang2025
