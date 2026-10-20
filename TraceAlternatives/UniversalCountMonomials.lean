module
public import TraceAlternatives.UniversalCountBudgets
public import DensityEnergyGM.SharpCountMonomials

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Montgomery.RationalMoment

/-- A nonnegative exact zero-loss margin controls the perturbed amplitude;
the explicit cost is at most T^(16delta). -/
theorem universalExpandedTerm_budget {T R σ a x δ ell : ℝ}
    (hT : 1 ≤ T) (hR : 0 < R) (hδ : 0 ≤ δ)
    (j : Fin 3) (i : Fin 5)
    (hell : 3*a*(1-σ)+(2*σ-1)*x ≤ ell)
    (hm : 0 ≤ universalTraceEnergyMargin σ a x j i) :
    (T^x)^3*T^(universalTraceA j)*(T^ell)^(universalTraceB j)*R^(universalTraceG j)*
      (gmEnergyTerm T (T^x) (T^(σ*x-2*δ)) R i)^(universalTraceD j) ≤
      T^(16*δ)*(T^(3*a*(1-σ)))^(2-universalTraceG j-universalTraceD j*gmEnergyR i)*
        (T^(σ*x-2*δ))^4*R^(universalTraceG j+universalTraceD j*gmEnergyR i) := by
  have hTp : 0 < T := by linarith
  have hB : universalTraceB j ≤ 0 := by fin_cases j <;> norm_num [universalTraceB]
  have hAmp : -2*universalTraceD j*gmEnergyW i ≤ 8 := by
    fin_cases j <;> fin_cases i <;> norm_num [universalTraceD,gmEnergyW]
  have hLoss := mul_nonneg hδ (show 0 ≤ 8+2*universalTraceD j*gmEnergyW i by linarith)
  have hEll := mul_le_mul_of_nonpos_right hell hB
  have hExp : 3*x+universalTraceA j+ell*universalTraceB j+
      (x*gmEnergyU i+gmEnergyV i+(σ*x-2*δ)*gmEnergyW i)*universalTraceD j ≤
      16*δ+3*a*(1-σ)*(2-universalTraceG j-universalTraceD j*gmEnergyR i)+(σ*x-2*δ)*4 := by
    unfold universalTraceEnergyMargin at hm
    nlinarith only [hm,hLoss,hEll]
  unfold gmEnergyTerm
  rw [gmExpandedTerm_log_identity hTp hR]
  have hrpow := Real.rpow_le_rpow_of_exponent_le hT hExp
  have h := mul_le_mul_of_nonneg_right hrpow
    (Real.rpow_nonneg hR.le (universalTraceG j+universalTraceD j*gmEnergyR i))
  convert h using 1
  · congr 2
    ring
  · rw [← Real.rpow_mul hTp.le,← Real.rpow_mul_natCast hTp.le]
    repeat rw [← Real.rpow_add hTp]
    norm_num

end Montgomery.RationalMoment
