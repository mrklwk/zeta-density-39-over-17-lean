module
public import TraceAlternatives.UniversalCountTargetWindows
public import DensityEnergyGM.SharpCountScale

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

/-- The retained quadratic-cardinality term has a genuine uniform height
saving on the intended rows; the amplitude loss is paid explicitly. -/
theorem universal_low_trace_budget {T σ a x δ ell : ℝ}
    (hT : 1≤T) (hδ : δ≤1/1800)
    (hell : 3*a*(1-σ)+(2*σ-1)*x≤ell)
    (hm : 1/100≤universalLowMargin σ a x) :
    T^δ*(T^x)^3*T^(1/2:ℝ)*(T^ell)^(-1/2:ℝ) ≤
      T^(-1/200:ℝ)*((T^x)^σ*T^(-2*δ))^4 := by
  have hTp : 0<T := by linarith
  rw [gm_amplitude_log_identity hTp]
  repeat rw [← Real.rpow_mul_natCast hTp.le]
  rw [← Real.rpow_mul hTp.le]
  repeat rw [← Real.rpow_add hTp]
  apply Real.rpow_le_rpow_of_exponent_le hT
  unfold universalLowMargin at hm
  norm_num
  linarith

/-- Upfront finite height threshold for absorbing the retained R² term. -/
theorem universal_low_coefficient_small {A T : ℝ} (hA : 0<A)
    (hT : 2≤T) (hLarge : (2*A)^200≤T) :
    A*T^(-1/200:ℝ)≤1/2 := by
  have hTp : 0<T := by linarith
  have hh := Real.rpow_le_rpow (pow_nonneg (by positivity : (0:ℝ)≤2*A) 200)
    hLarge (by norm_num : (0:ℝ)≤1/200)
  rw [← Real.rpow_natCast_mul (by positivity : (0:ℝ)≤2*A)] at hh
  norm_num at hh
  rw [show (-1/200:ℝ)= -(1/200:ℝ) by norm_num,Real.rpow_neg hTp.le]
  change A/T^(1/200:ℝ)≤1/2
  exact (div_le_iff₀ (by positivity : 0<T^(1/200:ℝ))).mpr (by linarith)

end Montgomery.RationalMoment
