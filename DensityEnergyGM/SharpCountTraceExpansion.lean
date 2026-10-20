module
public import DensityEnergyGM.SharpCountMonomials

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset
namespace Montgomery.RationalMoment

theorem fractional_constant_le_one_add {C d : ℝ}
    (hC : 0 ≤ C) (hd : 0 ≤ d) (hd1 : d ≤ 1) : C^d ≤ 1+C := by
  by_cases hC1 : 1 ≤ C
  · have h := Real.rpow_le_self_of_one_le hC1 hd1
    linarith
  · have h := Real.rpow_le_one hC (le_of_not_ge hC1) hd
    linarith

/-- All fifteen actual trace/energy terms are retained and normalized to
one common positive count gap, including the full amplitude perturbation. -/
theorem gmTraceEnergy_common_bound {T R E C σ a x δ ell η : ℝ}
    (hT : 1 ≤ T) (hC : 0 ≤ C) (hE : 0 ≤ E) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hSR : T^(3*a*(1-σ)) ≤ R)
    (hell : 3*a*(1-σ)+(2*σ-1)*x ≤ ell)
    (hm : ∀ j : Fin 3, ∀ i : Fin 5, 0 ≤ gmTraceEnergyMargin σ a x j i)
    (hEnergy : E ≤ C*T^η*fiveTermEnergyExpression T (T^x) (T^(σ*x-2*δ)) R) :
    (∑ j : Fin 3, (T^x)^3*T^(gmTraceA j)*(T^ell)^(gmTraceB j)*
      R^(gmTraceG j)*E^(gmTraceD j)) ≤
      15*(1+C)*T^η*(T^(16*δ)*(T^(3*a*(1-σ)))^(1/4:ℝ)*
        R^(7/4:ℝ)*(T^(σ*x-2*δ))^4) := by
  have hTp : 0 < T := by linarith
  have hS : 0 < T^(3*a*(1-σ)) := by positivity
  have hR : 0 < R := hS.trans_le hSR
  let M := T^(16*δ)*(T^(3*a*(1-σ)))^(1/4:ℝ)*R^(7/4:ℝ)*(T^(σ*x-2*δ))^4
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hj (j : Fin 3) : (T^x)^3*T^(gmTraceA j)*(T^ell)^(gmTraceB j)*
      R^(gmTraceG j)*E^(gmTraceD j) ≤ (1+C)*T^η*(5*M) := by
    have hd : 0 < gmTraceD j := by fin_cases j <;> norm_num [gmTraceD]
    have hd1 : gmTraceD j ≤ 1 := by fin_cases j <;> norm_num [gmTraceD]
    have hExp := gmEnergy_fractional_expansion hTp.le (by positivity) (by positivity)
      hR.le hE hC hd hd1 hEnergy
    let F := (T^x)^3*T^(gmTraceA j)*(T^ell)^(gmTraceB j)*R^(gmTraceG j)
    have hF : 0 ≤ F := by dsimp [F]; positivity
    have hCoeff : C^(gmTraceD j)*T^(η*gmTraceD j) ≤ (1+C)*T^η := by
      apply mul_le_mul (fractional_constant_le_one_add hC hd.le hd1)
        (Real.rpow_le_rpow_of_exponent_le hT (by nlinarith)) (by positivity) (by positivity)
    have hEach (i : Fin 5) : F*(gmEnergyTerm T (T^x) (T^(σ*x-2*δ)) R i)^(gmTraceD j) ≤ M := by
      have hMono := gmExpandedTerm_budget hT hR hδ j i hell (hm j i)
      have hDom := sublinear_monomial_domination hS hSR
        (show gmTraceG j+gmTraceD j*gmEnergyR i ≤ 2-(1/4:ℝ) by
          have h := gmTraceEnergy_sublinearity j i
          linarith)
      have hDom' := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hDom (by positivity : 0 ≤ (T^(σ*x-2*δ))^4))
        (by positivity : 0 ≤ T^(16*δ))
      have hId : 2-gmTraceG j-gmTraceD j*gmEnergyR i =
          2-(gmTraceG j+gmTraceD j*gmEnergyR i) := by ring
      rw [hId] at hMono
      exact hMono.trans (by dsimp [M]; nlinarith only [hDom'])
    calc
      _ = F*E^(gmTraceD j) := by rfl
      _ ≤ F*(C^(gmTraceD j)*T^(η*gmTraceD j)*
          ∑ i : Fin 5, (gmEnergyTerm T (T^x) (T^(σ*x-2*δ)) R i)^(gmTraceD j)) :=
        mul_le_mul_of_nonneg_left hExp hF
      _ = (C^(gmTraceD j)*T^(η*gmTraceD j))*
          ∑ i : Fin 5, F*(gmEnergyTerm T (T^x) (T^(σ*x-2*δ)) R i)^(gmTraceD j) := by
        rw [← mul_sum]
        ring
      _ ≤ ((1+C)*T^η)*∑ i : Fin 5, F*(gmEnergyTerm T (T^x) (T^(σ*x-2*δ)) R i)^(gmTraceD j) :=
        mul_le_mul_of_nonneg_right hCoeff (sum_nonneg (fun i _ =>
          mul_nonneg hF (Real.rpow_nonneg
            (gmEnergyTerm_nonneg hTp.le (by positivity) (by positivity) hR.le i) _)))
      _ ≤ ((1+C)*T^η)*∑ _i : Fin 5, M := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_le_sum (fun i _ => hEach i)
      _ = _ := by norm_num
  calc
    _ ≤ ∑ _j : Fin 3, (1+C)*T^η*(5*M) := sum_le_sum (fun j _ => hj j)
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; dsimp [M]; ring

end Montgomery.RationalMoment
