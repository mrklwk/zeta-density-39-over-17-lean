module
public import TraceAlternatives.UniversalSecondMoment

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

theorem universalShortProfile_mono {T T' M M' R E : ℝ}
    (hT : 0≤T) (hTT : T≤T') (hM : 0≤M) (hMM : M≤M')
    (hR : 0≤R) (hE : 0≤E) :
    universalShortProfile T M R E ≤ universalShortProfile T' M' R E := by
  have hTnon : 0≤T' := hT.trans hTT
  unfold universalShortProfile universalShortSublinearProfile
  gcongr

theorem universalShortProfile_scale {D T M R E : ℝ}
    (hD : 1≤D) (hT : 0≤T) (hM : 0≤M) (hR : 0≤R) (hE : 0≤E) :
    universalShortProfile (D*T) (D*M) R E ≤ D^3*universalShortProfile T M R E := by
  have hDp : 0<D := by linarith
  have hPow {a : ℝ} (ha : a≤3) : D^a≤D^3 := by
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_le hD ha
  have h1 := hPow (by norm_num : (3/2:ℝ)≤3)
  have h2 := hPow (by norm_num : (2:ℝ)≤3)
  have h3 := hPow (by norm_num : (1/6+4/3:ℝ)≤3)
  have h4 := hPow (by norm_num : (1/16+3/2:ℝ)≤3)
  unfold universalShortProfile universalShortSublinearProfile
  simp only [Real.mul_rpow hDp.le hM,Real.mul_rpow hDp.le hT,mul_pow]
  have ha := mul_le_mul_of_nonneg_right h1 (by positivity : (0:ℝ)≤M^(3/2:ℝ)*R^2)
  have hb := mul_le_mul_of_nonneg_right h2 (by positivity : (0:ℝ)≤M^2*E^(1/2:ℝ))
  have hc := mul_le_mul_of_nonneg_right h3 (by positivity : (0:ℝ)≤T^(1/6:ℝ)*M^(4/3:ℝ)*R*E^(1/4:ℝ))
  have hd := mul_le_mul_of_nonneg_right h4 (by positivity : (0:ℝ)≤T^(1/16:ℝ)*M^(3/2:ℝ)*R^(19/12:ℝ)*E^(5/48:ℝ))
  rw [Real.rpow_add hDp] at hc hd
  norm_num only [Real.rpow_ofNat] at hb
  nlinarith only [ha,hb,hc,hd]

end Montgomery.RationalMoment
