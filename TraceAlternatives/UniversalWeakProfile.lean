module
public import TraceAlternatives.WeakCountMonomial
public import DensityEnergyGM.SharpCountTraceExpansion

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace Montgomery.RationalMoment

def universalShortSublinearProfile (T M R E : ℝ) : ℝ :=
  M^2*E^(1/2:ℝ)+T^(1/6:ℝ)*M^(4/3:ℝ)*R*E^(1/4:ℝ)+
    T^(1/16:ℝ)*M^(3/2:ℝ)*R^(19/12:ℝ)*E^(5/48:ℝ)

theorem universalShortSublinearProfile_nonneg {T M R E : ℝ}
    (hT : 0≤T) (hM : 0≤M) (hR : 0≤R) (hE : 0≤E) :
    0≤universalShortSublinearProfile T M R E := by
  unfold universalShortSublinearProfile
  positivity

/-- Every term in the proved quadratic weak level count gives its exact
weighted short-S2 profile. Constants stay uniform in amplitude and data. -/
theorem universal_weak_level_profile {T M R E K U mass : ℝ}
    (hT : 0≤T) (hM : 0≤M) (hR : 0≤R) (hE : 0≤E) (hK : 0≤K)
    (hU : 0<U) (hmass : 0 ≤ mass) (hmassR : mass≤R^2)
    (hSq : mass^2 ≤ E*K*(M^4*U^(-4:ℝ)+
      T^(2/3:ℝ)*M^(16/3:ℝ)*U^(-8:ℝ)+
      T^(3/5:ℝ)*M^(72/5:ℝ)*U^(-96/5:ℝ))) :
    U^2*mass ≤ (1+3*K)*universalShortSublinearProfile T M R E := by
  let B1 : ℝ := M^4*U^(-4:ℝ)
  let B2 : ℝ := T^(2/3:ℝ)*M^(16/3:ℝ)*U^(-8:ℝ)
  let B3 : ℝ := T^(3/5:ℝ)*M^(72/5:ℝ)*U^(-96/5:ℝ)
  have hC : 0≤3*K := by positivity
  have hF1 : 0≤M^2*E^(1/2:ℝ) := by positivity
  have hF2 : 0≤T^(1/6:ℝ)*M^(4/3:ℝ)*R*E^(1/4:ℝ) := by positivity
  have hF3 : 0≤T^(1/16:ℝ)*M^(3/2:ℝ)*R^(19/12:ℝ)*E^(5/48:ℝ) := by positivity
  have hCase1 (hh : mass^2 ≤ 3*E*K*B1) :
      U^2*mass ≤ (1+3*K)*universalShortSublinearProfile T M R E := by
    have hSq' : mass^2 ≤ (3*K)*E*M^(4:ℝ)*T^(0:ℝ)*U^(-(4:ℝ)) := by
      convert hh using 1
      dsimp only [B1]
      norm_num only [Real.rpow_zero,Real.rpow_ofNat,mul_one]
      ring
    have hBound := weak_count_monomial_bound hR hE hC hM hT hU hmass
      (by norm_num : (4:ℝ)≤(4:ℝ)) hmassR hSq'
    have hNorm : U^2*mass ≤ (3*K)^(1/2:ℝ)*(M^2*E^(1/2:ℝ)) := by
      convert hBound using 1; norm_num; ring
    have hCoeff : (3*K)^(1/2:ℝ) ≤ 1+3*K :=
      fractional_constant_le_one_add hC (by norm_num) (by norm_num)
    calc
      _ ≤ (3*K)^(1/2:ℝ)*(M^2*E^(1/2:ℝ)) := hNorm
      _ ≤ (1+3*K)*(M^2*E^(1/2:ℝ)) := mul_le_mul_of_nonneg_right hCoeff hF1
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        unfold universalShortSublinearProfile
        linarith
  have hCase2 (hh : mass^2 ≤ 3*E*K*B2) :
      U^2*mass ≤ (1+3*K)*universalShortSublinearProfile T M R E := by
    have hSq' : mass^2 ≤ (3*K)*E*M^(16/3:ℝ)*T^(2/3:ℝ)*U^(-(8:ℝ)) := by
      convert hh using 1
      dsimp only [B2]
      norm_num only [Real.rpow_zero,Real.rpow_ofNat,mul_one]
      ring
    have hBound := weak_count_monomial_bound hR hE hC hM hT hU hmass
      (by norm_num : (4:ℝ)≤(8:ℝ)) hmassR hSq'
    have hNorm : U^2*mass ≤ (3*K)^(1/4:ℝ)*(T^(1/6:ℝ)*M^(4/3:ℝ)*R*E^(1/4:ℝ)) := by
      convert hBound using 1; norm_num; ring
    have hCoeff : (3*K)^(1/4:ℝ) ≤ 1+3*K :=
      fractional_constant_le_one_add hC (by norm_num) (by norm_num)
    calc
      _ ≤ (3*K)^(1/4:ℝ)*(T^(1/6:ℝ)*M^(4/3:ℝ)*R*E^(1/4:ℝ)) := hNorm
      _ ≤ (1+3*K)*(T^(1/6:ℝ)*M^(4/3:ℝ)*R*E^(1/4:ℝ)) := mul_le_mul_of_nonneg_right hCoeff hF2
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        unfold universalShortSublinearProfile
        linarith
  have hCase3 (hh : mass^2 ≤ 3*E*K*B3) :
      U^2*mass ≤ (1+3*K)*universalShortSublinearProfile T M R E := by
    have hSq' : mass^2 ≤ (3*K)*E*M^(72/5:ℝ)*T^(3/5:ℝ)*U^(-(96/5:ℝ)) := by
      convert hh using 1
      dsimp only [B3]
      norm_num only [Real.rpow_zero,Real.rpow_ofNat,mul_one]
      ring
    have hBound := weak_count_monomial_bound hR hE hC hM hT hU hmass
      (by norm_num : (4:ℝ)≤(96/5:ℝ)) hmassR hSq'
    have hNorm : U^2*mass ≤ (3*K)^(5/48:ℝ)*(T^(1/16:ℝ)*M^(3/2:ℝ)*R^(19/12:ℝ)*E^(5/48:ℝ)) := by
      convert hBound using 1; norm_num; ring
    have hCoeff : (3*K)^(5/48:ℝ) ≤ 1+3*K :=
      fractional_constant_le_one_add hC (by norm_num) (by norm_num)
    calc
      _ ≤ (3*K)^(5/48:ℝ)*(T^(1/16:ℝ)*M^(3/2:ℝ)*R^(19/12:ℝ)*E^(5/48:ℝ)) := hNorm
      _ ≤ (1+3*K)*(T^(1/16:ℝ)*M^(3/2:ℝ)*R^(19/12:ℝ)*E^(5/48:ℝ)) := mul_le_mul_of_nonneg_right hCoeff hF3
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        unfold universalShortSublinearProfile
        linarith
  by_cases h1 : mass^2 ≤ 3*E*K*B1
  · exact hCase1 h1
  by_cases h2 : mass^2 ≤ 3*E*K*B2
  · exact hCase2 h2
  have h3 : mass^2 ≤ 3*E*K*B3 := by
    change mass^2 ≤ E*K*(B1+B2+B3) at hSq
    nlinarith only [hSq,lt_of_not_ge h1,lt_of_not_ge h2]
  exact hCase3 h3

end Montgomery.RationalMoment
