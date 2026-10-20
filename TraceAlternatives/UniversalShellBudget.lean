module
public import TraceAlternatives.UniversalCenteredReflection

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

def universalCenteredBudget (T L R E : ℝ) : ℝ :=
  T*E^(1/2:ℝ)+T^(1/2:ℝ)*L^(1/2:ℝ)*R^2+
  T^(1/2:ℝ)*L^(2/3:ℝ)*R*E^(1/4:ℝ)+
  T^(9/16:ℝ)*L^(1/2:ℝ)*R^(19/12:ℝ)*E^(5/48:ℝ)

theorem universalCenteredBudget_nonneg {T L R E : ℝ}
    (hT : 0 ≤ T) (hL : 0 ≤ L) (hR : 0 ≤ R) (hE : 0 ≤ E) :
    0 ≤ universalCenteredBudget T L R E := by
  unfold universalCenteredBudget
  positivity

/-- Exact physical conversion of a short-source monomial to a shell.
Only nonnegative powers of H are enlarged to the allowed upper endpoint. -/
theorem universal_shell_monomial {T L H b s : ℝ}
    (hT : 0 < T) (hL : 0 < L) (hH : 0 < H) (hHT : H ≤ 2*T)
    (hs : 1 ≤ s) (hs2 : s ≤ 2) :
    L^2/H*T^b*(H/L)^s  ≤  2*T^(b+s-1)*L^(2-s) := by
  have hId : L^2/H*(H/L)^s = H^(s-1)*L^(2-s) := by
    rw [Real.div_rpow hH.le hL.le,Real.rpow_sub hH,Real.rpow_sub hL,
      Real.rpow_one,Real.rpow_two]
    field_simp
  have hHPow : H^(s-1)  ≤  2*T^(s-1) := by
    calc
      _  ≤  (2*T)^(s-1) := Real.rpow_le_rpow hH.le hHT (by linarith)
      _ = (2:ℝ)^(s-1)*T^(s-1) := Real.mul_rpow (by norm_num) hT.le
      _  ≤  _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
          (by linarith : s-1 ≤ 1)
        simpa only [Real.rpow_one] using hh
  calc
    _ = T^b*(L^2/H*(H/L)^s) := by ring
    _ = T^b*(H^(s-1)*L^(2-s)) := by rw [hId]
    _  ≤  T^b*((2*T^(s-1))*L^(2-s)) := by gcongr
    _ = 2*T^(b+s-1)*L^(2-s) := by
      rw [show b+s-1=b+(s-1) by ring,Real.rpow_add hT]
      ring

theorem universal_shell_budget_le {T L H R E : ℝ}
    (hT : 0 < T) (hL : 0 < L) (hH : 0 < H) (hHT : H ≤ 2*T)
    (hR : 0 ≤ R) (hE : 0 ≤ E) :
    L^2/H*universalLocalReflectionBudget T L H R E  ≤ 
      2*universalCenteredBudget T L R E := by
  have h1 := universal_shell_monomial (b:=0) (s:=3/2) hT hL hH hHT (by norm_num) (by norm_num)
  have h2 := universal_shell_monomial (b:=0) (s:=2) hT hL hH hHT (by norm_num) (by norm_num)
  have h3 := universal_shell_monomial (b:=1/6) (s:=4/3) hT hL hH hHT (by norm_num) (by norm_num)
  have h4 := universal_shell_monomial (b:=1/16) (s:=3/2) hT hL hH hHT (by norm_num) (by norm_num)
  norm_num only [Real.rpow_zero,Real.rpow_ofNat,mul_one,Real.rpow_one,
    show (0+3/2-1:ℝ)=1/2 by norm_num,show (2-3/2:ℝ)=1/2 by norm_num,
    show (0+2-1:ℝ)=1 by norm_num,show (2-2:ℝ)=0 by norm_num] at h1 h2
  norm_num only [show (1/6+4/3-1:ℝ)=1/2 by norm_num,show (2-4/3:ℝ)=2/3 by norm_num] at h3
  norm_num only [show (1/16+3/2-1:ℝ)=9/16 by norm_num,show (2-3/2:ℝ)=1/2 by norm_num] at h4
  have ha := mul_le_mul_of_nonneg_right h1 (sq_nonneg R)
  have hb := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hE (1/2))
  have hc := mul_le_mul_of_nonneg_right h3 (by positivity : (0:ℝ) ≤ R*E^(1/4:ℝ))
  have hd := mul_le_mul_of_nonneg_right h4 (by positivity : (0:ℝ) ≤ R^(19/12:ℝ)*E^(5/48:ℝ))
  unfold universalLocalReflectionBudget universalShortProfile universalShortSublinearProfile universalCenteredBudget
  nlinarith only [ha,hb,hc,hd]

end Montgomery.RationalMoment
