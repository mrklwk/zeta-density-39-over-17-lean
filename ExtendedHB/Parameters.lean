module
public import TraceAlternatives.PhysicalUniversalActualDensity
public import NativeBHBPeakTails

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.ExtendedHB
open Montgomery.RationalMoment Montgomery.RationalMoment.RightDetector

/-- The exact scale for the extended Heath--Brown exponent. -/
def lengthExponent (σ : ℝ) : ℝ := 1/(10*σ-7)

theorem denominator_pos {σ : ℝ} (hlo : 7/8 ≤ σ) : 0 < 10*σ-7 := by
  linarith

theorem physicalWindow {σ : ℝ} (hlo : 7/8 ≤ σ) (hhi : σ ≤ 17/19) :
    PhysicalDetectorWindow σ (lengthExponent σ) := by
  have hd := denominator_pos hlo
  refine ⟨by linarith,by linarith,?_,?_,?_⟩
  · exact (le_div_iff₀ hd).mpr (by linarith)
  · exact (div_lt_iff₀ hd).mpr (by linarith)
  · change 1/8 < (3*(1/(10*σ-7))/4)*(σ-1/2)
    have he : (3*(1/(10*σ-7))/4)*(σ-1/2) = (3*(σ-1/2)/4)/(10*σ-7) := by ring
    rw [he]
    exact (lt_div_iff₀ hd).mpr (by linarith)

theorem universalTraceMargin {σ x : ℝ} (hlo : 7/8 ≤ σ) (hhi : σ ≤ 17/19)
    (hx : lengthExponent σ ≤ x) (j : Fin 3) (i : Fin 5) :
    0 ≤ universalTraceEnergyMargin σ (lengthExponent σ) x j i := by
  have hd := denominator_pos hlo
  have he := universalTraceEnergyMargin_affine_length σ 1 10 7 1 hd.ne' j i
  simp only [one_mul] at he
  have hbase : 0 ≤ universalTraceEnergyMargin σ (lengthExponent σ) (lengthExponent σ) j i := by
    rw [lengthExponent,he]
    apply div_nonneg _ hd.le
    fin_cases j <;> fin_cases i <;>
      norm_num [universalTraceA,universalTraceB,universalTraceG,universalTraceD,
        gmEnergyU,gmEnergyV,gmEnergyW,gmEnergyR] <;> linarith
  exact hbase.trans (universalTraceEnergyMargin_mono_length (by linarith) hx j i)

theorem universalWindow {σ : ℝ} (hlo : 7/8 ≤ σ) (hhi : σ ≤ 17/19) :
    UniversalCountWindow σ (lengthExponent σ) := by
  have hd := denominator_pos hlo
  have hw := physicalWindow hlo hhi
  refine ⟨by linarith,hw.sigma_high,hw.a_low,hw.a_high,?_,?_⟩
  · exact fun x hx j i => universalTraceMargin hlo hhi hx j i
  · intro x hx
    have hbase : 51/100 ≤ (lengthExponent σ)*(7*σ/2-2) := by
      rw [lengthExponent,div_mul_eq_mul_div]
      exact (le_div_iff₀ hd).mpr (by linarith)
    have hmono := mul_le_mul_of_nonneg_left hx (show 0 ≤ 5*σ-7/2 by linarith)
    unfold universalLowMargin
    nlinarith only [hbase,hmono]

theorem longTailFirst {σ : ℝ} (hlo : 7/8 ≤ σ) (hhi : σ ≤ 17/19) :
    1-6*((3*lengthExponent σ/4)*(σ-1/2)) ≤ 3*lengthExponent σ*(1-σ) := by
  have hd := denominator_pos hlo
  have hnum : 10*σ-7-(9/2)*(σ-1/2) ≤ 3*(1-σ) := by linarith
  have hh := div_le_div_of_nonneg_right hnum hd.le
  convert hh using 1 <;> unfold lengthExponent <;> field_simp; ring

theorem longTailSecond {σ : ℝ} (hlo : 7/8 ≤ σ) (hhi : σ ≤ 17/19) :
    1+(51/100)/(13/30)-(4+(2+4*(51/100))/(13/30))*
      ((3*lengthExponent σ/4)*(σ-1/2)) ≤ 3*lengthExponent σ*(1-σ) := by
  have hd := denominator_pos hlo
  have hnum : (1+(51/100)/(13/30))*(10*σ-7)-
      (3/4)*(4+(2+4*(51/100))/(13/30))*(σ-1/2) ≤ 3*(1-σ) := by
    norm_num
    linarith
  have hh := div_le_div_of_nonneg_right hnum hd.le
  convert hh using 1 <;> unfold lengthExponent <;> field_simp

end Montgomery.ExtendedHB
