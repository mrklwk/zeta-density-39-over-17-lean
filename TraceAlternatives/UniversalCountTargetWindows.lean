module
public import TraceAlternatives.UniversalCountBudgets

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

theorem universalTraceEnergyMargin_affine_length (σ P Q C t : ℝ)
    (hd : Q*σ-C ≠ 0) (j : Fin 3) (i : Fin 5) :
    universalTraceEnergyMargin σ (P/(Q*σ-C)) (t*(P/(Q*σ-C))) j i =
      ((2-universalTraceB j-universalTraceG j-universalTraceD j*gmEnergyR i)*3*P*(1-σ)-
        (universalTraceA j+universalTraceD j*gmEnergyV i)*(Q*σ-C)+
        ((4-2*universalTraceB j-universalTraceD j*gmEnergyW i)*σ-3+universalTraceB j-
          universalTraceD j*gmEnergyU i)*t*P)/(Q*σ-C) := by
  unfold universalTraceEnergyMargin
  field_simp
  ring

/-- Every sharp-trace/five-energy monomial fits the entire unperturbed
fullrow4 length rectangle, including both closed sigma joins. -/
theorem universalTraceEnergyMargin_row4 {σ x : ℝ}
    (hlo : 7873/9370 ≤ σ) (hhi : σ ≤ 2018/2375)
    (hx : 1261710/(4342380*σ-1396527) ≤ x)
    (hx' : x ≤ 3*(1261710/(4342380*σ-1396527))/2) (j : Fin 3) (i : Fin 5) :
    0 ≤ universalTraceEnergyMargin σ (1261710/(4342380*σ-1396527)) x j i := by
  have hd : 0 < 4342380*σ-1396527 := by linarith
  apply universalTraceEnergyMargin_of_endpoints j i hx hx'
  · have he := universalTraceEnergyMargin_affine_length σ 1261710 4342380 1396527 1 hd.ne' j i
    simp only [one_mul] at he
    rw [he]
    apply div_nonneg _ hd.le
    fin_cases j <;> fin_cases i <;>
      norm_num [universalTraceA,universalTraceB,universalTraceG,universalTraceD,gmEnergyU,gmEnergyV,gmEnergyW,gmEnergyR] <;>
      linarith
  · have he := universalTraceEnergyMargin_affine_length σ 1261710 4342380 1396527 (3/2) hd.ne' j i
    have hm : 3*(1261710/(4342380*σ-1396527))/2 = (3/2)*(1261710/(4342380*σ-1396527)) := by ring
    rw [hm,he]
    apply div_nonneg _ hd.le
    fin_cases j <;> fin_cases i <;>
      norm_num [universalTraceA,universalTraceB,universalTraceG,universalTraceD,gmEnergyU,gmEnergyV,gmEnergyW,gmEnergyR] <;>
      linarith

/-- Every sharp-trace/five-energy monomial fits the entire unperturbed
fullrow5 length rectangle, including both closed sigma joins. -/
theorem universalTraceEnergyMargin_row5 {σ x : ℝ}
    (hlo : 2018/2375 ≤ σ) (hhi : σ ≤ 1959705/2298302)
    (hx : 3066/(10848*σ-3645) ≤ x)
    (hx' : x ≤ 3*(3066/(10848*σ-3645))/2) (j : Fin 3) (i : Fin 5) :
    0 ≤ universalTraceEnergyMargin σ (3066/(10848*σ-3645)) x j i := by
  have hd : 0 < 10848*σ-3645 := by linarith
  apply universalTraceEnergyMargin_of_endpoints j i hx hx'
  · have he := universalTraceEnergyMargin_affine_length σ 3066 10848 3645 1 hd.ne' j i
    simp only [one_mul] at he
    rw [he]
    apply div_nonneg _ hd.le
    fin_cases j <;> fin_cases i <;>
      norm_num [universalTraceA,universalTraceB,universalTraceG,universalTraceD,gmEnergyU,gmEnergyV,gmEnergyW,gmEnergyR] <;>
      linarith
  · have he := universalTraceEnergyMargin_affine_length σ 3066 10848 3645 (3/2) hd.ne' j i
    have hm : 3*(3066/(10848*σ-3645))/2 = (3/2)*(3066/(10848*σ-3645)) := by ring
    rw [hm,he]
    apply div_nonneg _ hd.le
    fin_cases j <;> fin_cases i <;>
      norm_num [universalTraceA,universalTraceB,universalTraceG,universalTraceD,gmEnergyU,gmEnergyV,gmEnergyW,gmEnergyR] <;>
      linarith


def universalLowMargin (σ a x : ℝ) : ℝ :=
  3*a*(1-σ)/2-1/2+(5*σ-7/2)*x

theorem universalLowMargin_row4 {σ x : ℝ} (hlo : 7873/9370 ≤ σ) (_hhi : σ ≤ 2018/2375)
    (hx : 1261710/(4342380*σ-1396527) ≤ x) :
    1/100 ≤ universalLowMargin σ (1261710/(4342380*σ-1396527)) x := by
  have hd : 0 < 4342380*σ-1396527 := by linarith
  have hBase : 51/100 ≤ (1261710/(4342380*σ-1396527))*(7*σ/2-2) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hd).mpr
    linarith
  have hMono := mul_le_mul_of_nonneg_left hx (show 0 ≤ 5*σ-7/2 by linarith)
  unfold universalLowMargin
  nlinarith only [hBase,hMono]

theorem universalLowMargin_row5 {σ x : ℝ} (hlo : 2018/2375 ≤ σ) (_hhi : σ ≤ 1959705/2298302)
    (hx : 3066/(10848*σ-3645) ≤ x) :
    1/100 ≤ universalLowMargin σ (3066/(10848*σ-3645)) x := by
  have hd : 0 < 10848*σ-3645 := by linarith
  have hBase : 51/100 ≤ (3066/(10848*σ-3645))*(7*σ/2-2) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hd).mpr
    linarith
  have hMono := mul_le_mul_of_nonneg_left hx (show 0 ≤ 5*σ-7/2 by linarith)
  unfold universalLowMargin
  nlinarith only [hBase,hMono]

end Montgomery.RationalMoment
