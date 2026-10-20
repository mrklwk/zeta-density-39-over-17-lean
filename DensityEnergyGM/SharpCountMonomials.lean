module
public import DensityEnergyGM.SharpCountEnergyExpansion

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Montgomery.RationalMoment

/-- Real power substitution, retaining every amplitude-loss factor. -/
theorem gmExpandedTerm_log_identity {T R : ℝ} (hT : 0 < T) (hR : 0 < R)
    (σ x δ ell A B g d u v w r : ℝ) :
    (T^x)^3*T^A*(T^ell)^B*R^g*
      ((T^x)^u*T^v*(T^(σ*x-2*δ))^w*R^r)^d =
    T^(3*x+A+ell*B+(x*u+v+(σ*x-2*δ)*w)*d)*R^(g+r*d) := by
  rw [Real.mul_rpow (by positivity : 0 ≤ (T^x)^u*T^v*(T^(σ*x-2*δ))^w) (by positivity : 0 ≤ R^r),
    Real.mul_rpow (by positivity : 0 ≤ (T^x)^u*T^v) (by positivity),
    Real.mul_rpow (by positivity : 0 ≤ (T^x)^u) (by positivity)]
  simp only [← Real.rpow_mul hT.le,← Real.rpow_mul hR.le]
  rw [← Real.rpow_mul_natCast hT.le]
  norm_num only [Nat.cast_ofNat]
  have he :
      T^(x*3)*T^A*T^(ell*B)*R^g*
        (T^(x*u*d)*T^(v*d)*T^((σ*x-2*δ)*w*d)*R^(r*d)) =
      (T^(x*3)*T^A*T^(ell*B)*T^(x*u*d)*T^(v*d)*T^((σ*x-2*δ)*w*d))*
        (R^g*R^(r*d)) := by ring
  rw [he]
  repeat rw [← Real.rpow_add hT]
  rw [← Real.rpow_add hR]
  congr 2
  ring

/-- A nonnegative exact zero-loss margin controls the perturbed amplitude;
the explicit cost is at most T^(16delta). -/
theorem gmExpandedTerm_budget {T R σ a x δ ell : ℝ}
    (hT : 1 ≤ T) (hR : 0 < R) (hδ : 0 ≤ δ)
    (j : Fin 3) (i : Fin 5)
    (hell : 3*a*(1-σ)+(2*σ-1)*x ≤ ell)
    (hm : 0 ≤ gmTraceEnergyMargin σ a x j i) :
    (T^x)^3*T^(gmTraceA j)*(T^ell)^(gmTraceB j)*R^(gmTraceG j)*
      (gmEnergyTerm T (T^x) (T^(σ*x-2*δ)) R i)^(gmTraceD j) ≤
      T^(16*δ)*(T^(3*a*(1-σ)))^(2-gmTraceG j-gmTraceD j*gmEnergyR i)*
        (T^(σ*x-2*δ))^4*R^(gmTraceG j+gmTraceD j*gmEnergyR i) := by
  have hTp : 0 < T := by linarith
  have hB : gmTraceB j ≤ 0 := by fin_cases j <;> norm_num [gmTraceB]
  have hAmp : -2*gmTraceD j*gmEnergyW i ≤ 8 := by
    fin_cases j <;> fin_cases i <;> norm_num [gmTraceD,gmEnergyW]
  have hLoss := mul_nonneg hδ (show 0 ≤ 8+2*gmTraceD j*gmEnergyW i by linarith)
  have hEll := mul_le_mul_of_nonpos_right hell hB
  have hExp : 3*x+gmTraceA j+ell*gmTraceB j+
      (x*gmEnergyU i+gmEnergyV i+(σ*x-2*δ)*gmEnergyW i)*gmTraceD j ≤
      16*δ+3*a*(1-σ)*(2-gmTraceG j-gmTraceD j*gmEnergyR i)+(σ*x-2*δ)*4 := by
    unfold gmTraceEnergyMargin at hm
    nlinarith only [hm,hLoss,hEll]
  unfold gmEnergyTerm
  rw [gmExpandedTerm_log_identity hTp hR]
  have hrpow := Real.rpow_le_rpow_of_exponent_le hT hExp
  have h := mul_le_mul_of_nonneg_right hrpow
    (Real.rpow_nonneg hR.le (gmTraceG j+gmTraceD j*gmEnergyR i))
  convert h using 1
  · congr 2
    ring
  · rw [← Real.rpow_mul hTp.le,← Real.rpow_mul_natCast hTp.le]
    repeat rw [← Real.rpow_add hTp]
    norm_num

end Montgomery.RationalMoment
