module
public import TraceAlternatives.CubeCountBudgets
public import DensityEnergyGM.SharpCountMonomials

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Montgomery.RationalMoment

/-- A nonnegative exact zero-loss margin controls the perturbed amplitude;
the explicit cost is at most T^(16delta). -/
theorem cubeExpandedTerm_budget {T R σ a x δ ell : ℝ}
    (hT : 1 ≤ T) (hR : 0 < R) (hδ : 0 ≤ δ)
    (j : Fin 2) (i : Fin 5)
    (hell : 3*a*(1-σ)+(2*σ-1)*x ≤ ell)
    (hm : 0 ≤ cubeTraceEnergyMargin σ a x j i) :
    (T^x)^3*T^(cubeTraceA j)*(T^ell)^(cubeTraceB j)*R^(cubeTraceG j)*
      (gmEnergyTerm T (T^x) (T^(σ*x-2*δ)) R i)^(cubeTraceD j) ≤
      T^(16*δ)*(T^(3*a*(1-σ)))^(2-cubeTraceG j-cubeTraceD j*gmEnergyR i)*
        (T^(σ*x-2*δ))^4*R^(cubeTraceG j+cubeTraceD j*gmEnergyR i) := by
  have hTp : 0 < T := by linarith
  have hB : cubeTraceB j ≤ 0 := by fin_cases j <;> norm_num [cubeTraceB]
  have hAmp : -2*cubeTraceD j*gmEnergyW i ≤ 8 := by
    fin_cases j <;> fin_cases i <;> norm_num [cubeTraceD,gmEnergyW]
  have hLoss := mul_nonneg hδ (show 0 ≤ 8+2*cubeTraceD j*gmEnergyW i by linarith)
  have hEll := mul_le_mul_of_nonpos_right hell hB
  have hExp : 3*x+cubeTraceA j+ell*cubeTraceB j+
      (x*gmEnergyU i+gmEnergyV i+(σ*x-2*δ)*gmEnergyW i)*cubeTraceD j ≤
      16*δ+3*a*(1-σ)*(2-cubeTraceG j-cubeTraceD j*gmEnergyR i)+(σ*x-2*δ)*4 := by
    unfold cubeTraceEnergyMargin at hm
    nlinarith only [hm,hLoss,hEll]
  unfold gmEnergyTerm
  rw [gmExpandedTerm_log_identity hTp hR]
  have hrpow := Real.rpow_le_rpow_of_exponent_le hT hExp
  have h := mul_le_mul_of_nonneg_right hrpow
    (Real.rpow_nonneg hR.le (cubeTraceG j+cubeTraceD j*gmEnergyR i))
  convert h using 1
  · congr 2
    ring
  · rw [← Real.rpow_mul hTp.le,← Real.rpow_mul_natCast hTp.le]
    repeat rw [← Real.rpow_add hTp]
    norm_num

end Montgomery.RationalMoment
