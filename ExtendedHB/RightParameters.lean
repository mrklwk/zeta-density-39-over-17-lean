module
public import ExtendedHB.Parameters

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.ExtendedHB
open Montgomery.RationalMoment Montgomery.RationalMoment.RightDetector

/-- Continuation forced by the two binding universal trace margins. -/
def rightLengthExponent (σ : ℝ) : ℝ := 2/(σ+3)

theorem rightPhysicalWindow {σ : ℝ} (hlo : 17/19 ≤ σ) (hhi : σ < 1) :
    PhysicalDetectorWindow σ (rightLengthExponent σ) := by
  have hd : 0 < σ+3 := by linarith
  refine ⟨by linarith,hhi,?_,?_,?_⟩
  · exact (le_div_iff₀ hd).mpr (by linarith)
  · exact (div_lt_iff₀ hd).mpr (by linarith)
  · change 1/8 < (3*(2/(σ+3))/4)*(σ-1/2)
    have he : (3*(2/(σ+3))/4)*(σ-1/2) = (3*(σ-1/2)/2)/(σ+3) := by ring
    rw [he]
    exact (lt_div_iff₀ hd).mpr (by linarith)

theorem rightUniversalTraceMargin {σ x : ℝ} (hlo : 17/19 ≤ σ)
    (hx : rightLengthExponent σ ≤ x) (j : Fin 3) (i : Fin 5) :
    0 ≤ universalTraceEnergyMargin σ (rightLengthExponent σ) x j i := by
  have hd : 0 < σ+3 := by linarith
  have he := universalTraceEnergyMargin_affine_length σ 2 1 (-3) 1 (by linarith : 1*σ-(-3) ≠ 0) j i
  simp only [one_mul,sub_neg_eq_add] at he
  have hbase : 0 ≤ universalTraceEnergyMargin σ (rightLengthExponent σ) (rightLengthExponent σ) j i := by
    rw [rightLengthExponent,he]
    apply div_nonneg _ hd.le
    fin_cases j <;> fin_cases i <;>
      norm_num [universalTraceA,universalTraceB,universalTraceG,universalTraceD,
        gmEnergyU,gmEnergyV,gmEnergyW,gmEnergyR] <;> linarith
  exact hbase.trans (universalTraceEnergyMargin_mono_length (by linarith) hx j i)

theorem rightUniversalWindow {σ : ℝ} (hlo : 17/19 ≤ σ) (hhi : σ < 1) :
    UniversalCountWindow σ (rightLengthExponent σ) := by
  have hd : 0 < σ+3 := by linarith
  have hw := rightPhysicalWindow hlo hhi
  refine ⟨by linarith,hhi,hw.a_low,hw.a_high,?_,?_⟩
  · exact fun x hx j i => rightUniversalTraceMargin hlo hx j i
  · intro x hx
    have hbase : 51/100 ≤ (rightLengthExponent σ)*(7*σ/2-2) := by
      rw [rightLengthExponent,div_mul_eq_mul_div]
      exact (le_div_iff₀ hd).mpr (by linarith)
    have hmono := mul_le_mul_of_nonneg_left hx (show 0 ≤ 5*σ-7/2 by linarith)
    unfold universalLowMargin
    nlinarith only [hbase,hmono]

theorem rightLongTailFirst {σ : ℝ} (hlo : 17/19 ≤ σ) :
    1-6*((3*rightLengthExponent σ/4)*(σ-1/2)) ≤ 3*rightLengthExponent σ*(1-σ) := by
  have hd : 0 < σ+3 := by linarith
  have hnum : σ+3-9*(σ-1/2) ≤ 6*(1-σ) := by linarith
  have hh := div_le_div_of_nonneg_right hnum hd.le
  convert hh using 1 <;> unfold rightLengthExponent <;> field_simp <;> ring

theorem rightLongTailSecond {σ : ℝ} (hlo : 17/19 ≤ σ) :
    1+(51/100)/(13/30)-(4+(2+4*(51/100))/(13/30))*
      ((3*rightLengthExponent σ/4)*(σ-1/2)) ≤ 3*rightLengthExponent σ*(1-σ) := by
  have hd : 0 < σ+3 := by linarith
  have hnum : (1+(51/100)/(13/30))*(σ+3)-
      (3/2)*(4+(2+4*(51/100))/(13/30))*(σ-1/2) ≤ 6*(1-σ) := by
    norm_num
    linarith
  have hh := div_le_div_of_nonneg_right hnum hd.le
  convert hh using 1 <;> unfold rightLengthExponent <;> field_simp <;> ring

end Montgomery.ExtendedHB
