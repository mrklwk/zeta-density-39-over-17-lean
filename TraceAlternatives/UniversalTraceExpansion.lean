module
public import TraceAlternatives.UniversalQuadraticLargeValues
public import TraceAlternatives.UniversalCountBudgets

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment

theorem universalTraceExpression_eq {T N L R E : ℝ} (hL : 0<L) :
    (N^3/L)*universalCenteredBudget T L R E =
    N^3*T^(1/2:ℝ)*L^(-1/2:ℝ)*R^2+
    ∑ j : Fin 3, N^3*T^(universalTraceA j)*L^(universalTraceB j)*
      R^(universalTraceG j)*E^(universalTraceD j) := by
  have hPow (a : ℝ) : L^a*L⁻¹=L^(a-1) := by
    rw [← Real.rpow_neg_one,← Real.rpow_add hL]
    congr 1
  have hHalf := hPow (1/2)
  have hThird := hPow (2/3)
  norm_num only [show (1/2-1:ℝ)= -1/2 by norm_num] at hHalf
  norm_num only [show (2/3-1:ℝ)= -1/3 by norm_num] at hThird
  conv_rhs => norm_num [Fin.sum_univ_succ,universalTraceA,universalTraceB,universalTraceG,universalTraceD]
  unfold universalCenteredBudget
  rw [div_eq_mul_inv]
  rw [show N^3*L⁻¹*(T*E^(1/2:ℝ)+T^(1/2:ℝ)*L^(1/2:ℝ)*R^2+
      T^(1/2:ℝ)*L^(2/3:ℝ)*R*E^(1/4:ℝ)+T^(9/16:ℝ)*L^(1/2:ℝ)*R^(19/12:ℝ)*E^(5/48:ℝ)) =
      N^3*T*L⁻¹*E^(1/2:ℝ)+N^3*T^(1/2:ℝ)*(L^(1/2:ℝ)*L⁻¹)*R^2+
      N^3*T^(1/2:ℝ)*(L^(2/3:ℝ)*L⁻¹)*R*E^(1/4:ℝ)+
      N^3*T^(9/16:ℝ)*(L^(1/2:ℝ)*L⁻¹)*R^(19/12:ℝ)*E^(5/48:ℝ) by ring]
  rw [hHalf,hThird]
  simp only [Real.rpow_neg_one]
  ring

end Montgomery.RationalMoment
