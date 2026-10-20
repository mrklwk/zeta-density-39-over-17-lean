module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaReflectionEnvelope
public import TaoTrudgianYang2025.BetaClosedDuality

@[expose] public section

/-!
# Closed half-interval criterion for actual analytic exponent pairs

For a candidate whose affine slope is at least one half, the proved beta
reflection supplies the other half of the interval. This is a consumer
of the actual growth exponent, not membership in a candidate polygon.
-/

noncomputable section

open Expdb
open scoped NNReal

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

theorem exponentPairLine_reflected_le {k l α : ℝ}
    (hslope : 1/2 ≤ l-k) (hα : 1/2 ≤ α) :
    1/2-(1-α)+exponentPairLine k l (1-α) ≤ exponentPairLine k l α := by
  have h := mul_nonneg (show 0 ≤ 2*α-1 by linarith)
    (show 0 ≤ l-k-1/2 by linarith)
  unfold exponentPairLine
  nlinarith only [h]

theorem exponentPair_of_beta_bound_half {k l : ℝ}
    (htri : InExponentPairTriangle k l) (hslope : 1/2 ≤ l-k)
    (hbeta : ∀ α : ℝ≥0, (α:ℝ) ≤ 1/2 →
      exponentSumGrowthExponent α ≤ exponentPairLine k l α) :
    ExponentPair k l := by
  apply (exponentPair_iff_beta_bound htri).mpr
  intro α hα
  by_cases hhalf : (α:ℝ) ≤ 1/2
  · exact hbeta α hhalf
  · have hαNN : α ≤ 1 := by exact_mod_cast hα
    let γ : ℝ≥0 := 1-α
    have hγreal : (γ:ℝ) = 1-(α:ℝ) := NNReal.coe_sub hαNN
    have hγhalf : (γ:ℝ) ≤ 1/2 := by rw [hγreal]; linarith
    have hγ : (γ:ℝ) ≤ 1 := by linarith
    have hγNN : γ ≤ 1 := by exact_mod_cast hγ
    have hdouble : (1-γ:ℝ≥0) = α := by
      apply NNReal.coe_injective
      rw [NNReal.coe_sub hγNN,hγreal]
      norm_num
    have hinput : IsExponentSumBoundNonAsymptotic γ (exponentPairLine k l γ) :=
      exponentSumGrowthExponent_le_iff_nonAsymptotic.mp (hbeta γ hγhalf)
    have hlinepos : 0 ≤ exponentPairLine k l γ := by
      unfold exponentPairLine
      have hm := mul_nonneg (show 0 ≤ l-k by linarith) γ.coe_nonneg
      linarith [htri.1]
    have hn : 0 ≤ exponentPairLine k l γ+1/2-(γ:ℝ) := by linarith
    have hout := exponentSumGrowthExponent_le_iff_nonAsymptotic.mpr
      (isExponentSumBoundNonAsymptotic_reflect_nonnegative hγ hinput hn)
    rw [hdouble] at hout
    calc
      exponentSumGrowthExponent α ≤ exponentPairLine k l γ+1/2-(γ:ℝ) := hout
      _ ≤ exponentPairLine k l α := by
        have hb := exponentPairLine_reflected_le hslope (le_of_not_ge hhalf)
        rw [hγreal]
        linarith

theorem exponentPair_iff_beta_bound_half {k l : ℝ}
    (htri : InExponentPairTriangle k l) (hslope : 1/2 ≤ l-k) :
    ExponentPair k l ↔ ∀ α : ℝ≥0, (α:ℝ) ≤ 1/2 →
      exponentSumGrowthExponent α ≤ exponentPairLine k l α := by
  constructor
  · intro h α hα
    exact exponentSumGrowthExponent_le_exponentPairLine_closed h α (by linarith)
  · exact exponentPair_of_beta_bound_half htri hslope

end TaoTrudgianYang2025

