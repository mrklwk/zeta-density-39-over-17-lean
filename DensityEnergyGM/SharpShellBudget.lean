module
public import DensityEnergyGM.SharpCenteredReflection

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

def sharpCenteredBudget (T L R E : ℝ) : ℝ :=
  T*E^(1/2:ℝ)+T^(4/5:ℝ)*L^(1/5:ℝ)*R*E^(1/4:ℝ)+
    T^(9/20:ℝ)*L^(4/5:ℝ)*R*E^(1/4:ℝ)

theorem sharpCenteredBudget_nonneg {T L R E : ℝ}
    (hT : 0≤T) (hL : 0≤L) (hR : 0≤R) (hE : 0≤E) :
    0 ≤ sharpCenteredBudget T L R E := by
  unfold sharpCenteredBudget
  positivity

theorem sharp_shell_scale {H L : ℝ} (hH : 0<H) (hL : 0<L) (q : ℝ) :
    L^2/H*(H/L)^q = H^(q-1)*L^(2-q) := by
  rw [Real.div_rpow hH.le hL.le,Real.rpow_sub hH,Real.rpow_sub hL,
    Real.rpow_one,Real.rpow_two]
  ring

theorem sharp_small_height_rpow {T H a : ℝ} (hT : 0<T) (hH : 0≤H)
    (hHT : H≤2*T) (ha : 0≤a) (ha1 : a≤1) : H^a≤2*T^a := by
  calc
    _ ≤ (2*T)^a := Real.rpow_le_rpow hH hHT ha
    _ = (2:ℝ)^a*T^a := Real.mul_rpow (by norm_num) hT.le
    _ ≤ 2*T^a := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) ha1
      norm_num at h
      exact h

/-- Exact scale conversion from the sharp short-polynomial profile to the
three physical centered-trace powers. -/
theorem sharp_shell_budget_le {T L H R E : ℝ}
    (hT : 0<T) (hL : 0<L) (hH : 0<H) (hHT : H≤2*T)
    (hR : 0≤R) (hE : 0≤E) :
    L^2/H*sharpLocalReflectionBudget T L H R E ≤
      2*sharpCenteredBudget T L R E := by
  have h2 := sharp_shell_scale hH hL (2:ℝ)
  have h9 := sharp_shell_scale hH hL (9/5:ℝ)
  have h6 := sharp_shell_scale hH hL (6/5:ℝ)
  norm_num at h2 h9 h6
  have hTpow : T^(1/4:ℝ)*T^(1/5:ℝ)=T^(9/20:ℝ) := by
    rw [← Real.rpow_add hT]
    norm_num
  have hTpow' : T^(1/4:ℝ)*(2*T^(1/5:ℝ))=2*T^(9/20:ℝ) := by
    calc
      _ = 2*(T^(1/4:ℝ)*T^(1/5:ℝ)) := by ring
      _ = _ := by rw [hTpow]
  calc
    _ = (L^2/H*(H/L)^2)*E^(1/2:ℝ)+R*E^(1/4:ℝ)*
        ((L^2/H*(H/L)^(9/5:ℝ))+T^(1/4:ℝ)*(L^2/H*(H/L)^(6/5:ℝ))) := by
      unfold sharpLocalReflectionBudget
      ring
    _ = H*E^(1/2:ℝ)+R*E^(1/4:ℝ)*
        (H^(4/5:ℝ)*L^(1/5:ℝ)+T^(1/4:ℝ)*(H^(1/5:ℝ)*L^(4/5:ℝ))) := by
      rw [h2,h9,h6]
    _ ≤ (2*T)*E^(1/2:ℝ)+R*E^(1/4:ℝ)*
        ((2*T^(4/5:ℝ))*L^(1/5:ℝ)+T^(1/4:ℝ)*((2*T^(1/5:ℝ))*L^(4/5:ℝ))) := by
      gcongr
      · exact sharp_small_height_rpow hT hH.le hHT (by norm_num) (by norm_num)
      · exact sharp_small_height_rpow hT hH.le hHT (by norm_num) (by norm_num)
    _ = 2*sharpCenteredBudget T L R E := by
      rw [← mul_assoc (T^(1/4:ℝ)) (2*T^(1/5:ℝ)),hTpow']
      unfold sharpCenteredBudget
      ring

end Montgomery.RationalMoment
