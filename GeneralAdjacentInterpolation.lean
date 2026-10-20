module
public import GeneralAdjacentCover

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace Montgomery.RationalMoment

/-- Geometric interpolation of two adjacent literal moment powers. -/
theorem adjacent_log_interpolation {U T H R : ℝ} {j : ℕ}
    (hj : 1 ≤ j) (hU : 0 < U) (hT : 0 < T) (hH : 0 < H) (hR : 0 < R)
    (h₁ : U^j ≤ 2*T*R^(2*j-1))
    (h₂ : U^(j+1) ≤ 2*H^(2*(j+1))*R^(2*j+1)) :
    Real.log U ≤ Real.log 2+Real.log H+Real.log T/(2*(j:ℝ))+
      (2-(2*(j:ℝ)+1)/(2*j*(j+1)))*Real.log R := by
  have hjr : (1:ℝ) ≤ j := by exact_mod_cast hj
  have hjp : (0:ℝ) < j := by linarith
  have hj1 : 0 < (j:ℝ)+1 := by linarith
  have hl₁ := Real.log_le_log (pow_pos hU j) h₁
  have hl₂ := Real.log_le_log (pow_pos hU (j+1)) h₂
  simp (disch := positivity) only [Real.log_mul,Real.log_pow] at hl₁ hl₂
  push_cast [Nat.cast_sub (show 1 ≤ 2*j by omega)] at hl₁ hl₂
  have hw := add_le_add
    (mul_le_mul_of_nonneg_left hl₁ (show 0 ≤ 1/(2*(j:ℝ)) by positivity))
    (mul_le_mul_of_nonneg_left hl₂ (show 0 ≤ 1/(2*((j:ℝ)+1)) by positivity))
  have hb : Real.log U ≤
      ((2*(j:ℝ)+1)/(2*j*(j+1)))*Real.log 2+Real.log H+
        Real.log T/(2*(j:ℝ))+(2-(2*(j:ℝ)+1)/(2*j*(j+1)))*Real.log R := by
    convert hw using 1 <;> field_simp <;> ring
  have hc : (2*(j:ℝ)+1)/(2*j*(j+1)) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 2*(j:ℝ)*(j+1))).mpr
    nlinarith [sq_nonneg ((j:ℝ)-1)]
  have hh := mul_le_mul_of_nonneg_right hc (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
  linarith only [hb,hh]

/-- An adjacent pair at any order j>=K gives the K-envelope, including
the linear-in-height term when the logarithmic remainder is negative. -/
theorem adjacent_pair_envelope {U T H R : ℝ} {K j : ℕ}
    (hK : 1 ≤ K) (hKj : K ≤ j) (hU : 0 < U) (hT : 0 < T)
    (hH : 0 < H) (hR : 1 ≤ R)
    (h₁ : U^j ≤ 2*T*R^(2*j-1))
    (h₂ : U^(j+1) ≤ 2*H^(2*(j+1))*R^(2*j+1)) :
    U ≤ 2*(H*R^2+H*T^(1/(2*(K:ℝ)))*
      R^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))) := by
  have hkp : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hkj : (K:ℝ) ≤ j := by exact_mod_cast hKj
  have hrp : 0 < R := by linarith
  have hl := adjacent_log_interpolation (hK.trans hKj) hU hT hH hrp h₁ h₂
  have hc := adjacent_log_remainder hkp hkj (Real.log_nonneg hR) (t:=Real.log T)
  dsimp only at hc
  let d := Real.log T/(2*(K:ℝ))-
    (2*(K:ℝ)+1)/(2*K*(K+1))*Real.log R
  by_cases hd : 0 ≤ d
  · rw [max_eq_right hd] at hc
    have hu : U ≤ 2*H*T^(1/(2*(K:ℝ)))*R^(2-(2*(K:ℝ)+1)/(2*K*(K+1))) := by
      apply (Real.log_le_log_iff hU (by positivity)).mp
      simp (disch := positivity) only [Real.log_mul,Real.log_rpow]
      dsimp [d] at hc
      calc
        Real.log U ≤ Real.log 2+Real.log H+2*Real.log R+
            (Real.log T/(2*(j:ℝ))-(2*(j:ℝ)+1)/(2*j*(j+1))*Real.log R) := by
          convert hl using 1; ring
        _ ≤ Real.log 2+Real.log H+2*Real.log R+
            (Real.log T/(2*(K:ℝ))-(2*(K:ℝ)+1)/(2*K*(K+1))*Real.log R) := by gcongr
        _ = _ := by ring
    exact hu.trans (by
      have hh : 0 ≤ H*R^2 := by positivity
      linarith)
  · rw [max_eq_left (le_of_not_ge hd)] at hc
    have hu : U ≤ 2*H*R^2 := by
      apply (Real.log_le_log_iff hU (by positivity)).mp
      simp (disch := positivity) only [Real.log_mul,Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      nlinarith only [hl,hc]
    exact hu.trans (by
      have hh : 0 ≤ H*T^(1/(2*(K:ℝ)))*R^(2-(2*(K:ℝ)+1)/(2*K*(K+1))) := by positivity
      linarith)

theorem adjacent_high_moment {U H R : ℝ} {K : ℕ}
    (hK : 1 ≤ K) (hU : 0 < U) (hH : 0 < H) (hR : 0 < R)
    (hm : U^K ≤ 2*H^(2*K)*R^(2*K-1)) :
    U ≤ 2*H^2*R^(2-1/(K:ℝ)) := by
  have hkp : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hk1 : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hl := Real.log_le_log (pow_pos hU K) hm
  simp (disch := positivity) only [Real.log_mul,Real.log_pow] at hl
  push_cast [Nat.cast_sub (show 1 ≤ 2*K by omega)] at hl
  apply (Real.log_le_log_iff hU (by positivity)).mp
  simp (disch := positivity) only [Real.log_mul,Real.log_pow,Real.log_rpow]
  apply (mul_le_mul_iff_right₀ hkp).mp
  have hh := mul_le_mul_of_nonneg_right (show 0 ≤ (K:ℝ)-1 by linarith)
    (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
  have hb : (K:ℝ)*Real.log U ≤
      (K:ℝ)*Real.log 2+2*(K:ℝ)*Real.log H+(2*(K:ℝ)-1)*Real.log R := by
    linarith only [hl,hh]
  convert hb using 1; field_simp; ring

end Montgomery.RationalMoment
