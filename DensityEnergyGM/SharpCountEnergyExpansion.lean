module
public import DensityEnergyGM.SharpCountBudgets

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment

def gmEnergyTerm (T N V R : ℝ) (i : Fin 5) : ℝ :=
  N^(gmEnergyU i)*T^(gmEnergyV i)*V^(gmEnergyW i)*R^(gmEnergyR i)

theorem gmEnergyTerm_nonneg {T N V R : ℝ}
    (hT : 0 ≤ T) (hN : 0 ≤ N) (hV : 0 ≤ V) (hR : 0 ≤ R) (i : Fin 5) :
    0 ≤ gmEnergyTerm T N V R i := by unfold gmEnergyTerm; positivity

theorem fiveTermEnergyExpression_eq_sum (T N V R : ℝ) :
    fiveTermEnergyExpression T N V R = ∑ i : Fin 5, gmEnergyTerm T N V R i := by
  norm_num [fiveTermEnergyExpression,gmEnergyTerm,Fin.sum_univ_succ,
    gmEnergyU,gmEnergyV,gmEnergyW,gmEnergyR,Real.rpow_natCast]
  ring

/-- Fractional trace powers preserve every one of the five actual energy terms. -/
theorem gmEnergy_fractional_expansion {T N V R E C η d : ℝ}
    (hT : 0 ≤ T) (hN : 0 ≤ N) (hV : 0 ≤ V) (hR : 0 ≤ R)
    (hE : 0 ≤ E) (hC : 0 ≤ C) (hd : 0 < d) (hd1 : d ≤ 1)
    (hbound : E ≤ C*T^η*fiveTermEnergyExpression T N V R) :
    E^d ≤ C^d*T^(η*d)*∑ i : Fin 5, (gmEnergyTerm T N V R i)^d := by
  have hSum := fiveTermEnergyExpression_nonneg hT hN hV hR
  have h := Real.rpow_le_rpow hE hbound hd.le
  rw [Real.mul_rpow (by positivity : 0 ≤ C*T^η) hSum,
    Real.mul_rpow hC (Real.rpow_nonneg hT η),← Real.rpow_mul hT,
    fiveTermEnergyExpression_eq_sum] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (finite_sum_rpow_le_sum_rpow univ (gmEnergyTerm T N V R)
      (fun i _ => gmEnergyTerm_nonneg hT hN hV hR i) hd hd1) (by positivity))

end Montgomery.RationalMoment
