module
public import RationalDyadicShortRange

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Montgomery.RationalMoment

theorem adjacent_rpow_nat {x : ℝ} (hx : 0 ≤ x) (a : ℝ) (n : ℕ) :
    (x^a)^n = x^(a*(n:ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]

/-- Exact scalar interpolation of moments two and three. The hypotheses
are scalar inequalities; this lemma alone is not a zero-density theorem. -/
theorem adjacent_two_three {U T H R : ℝ}
    (hU : 0 ≤ U) (hT : 0 ≤ T) (hH : 0 ≤ H) (hR : 0 ≤ R)
    (h2 : U^2 ≤ 2*T*R^3) (h3 : U^3 ≤ 2*H^6*R^5) :
    U ≤ 2*H*T^((1:ℝ)/4)*R^((19:ℝ)/12) := by
  have hprod := mul_le_mul
    (pow_le_pow_left₀ (by positivity : 0 ≤ U^2) h2 3)
    (pow_le_pow_left₀ (by positivity : 0 ≤ U^3) h3 2)
    (by positivity : 0 ≤ (U^3)^2) (by positivity : 0 ≤ (2*T*R^3)^3)
  have hh : U^12 ≤ 32*H^12*T^3*R^19 := by nlinarith only [hprod]
  have hp : (2*H*T^((1:ℝ)/4)*R^((19:ℝ)/12))^12 =
      4096*H^12*T^3*R^19 := by
    simp only [mul_pow, adjacent_rpow_nat hT, adjacent_rpow_nat hR]
    norm_num
  apply (pow_le_pow_iff_left₀ hU (by positivity) (by norm_num : (12:ℕ) ≠ 0)).mp
  rw [hp]
  exact hh.trans (by nlinarith [mul_nonneg (by positivity : 0 ≤ H^12*T^3) (pow_nonneg hR 19)])

/-- Exact scalar interpolation of moments three and four, keeping the
cardinality condition needed to compare it with the k=2 envelope. -/
theorem adjacent_three_four {U T H R : ℝ}
    (hU : 0 ≤ U) (hT : 0 ≤ T) (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hRT : R^3 ≤ T^2)
    (h3 : U^3 ≤ 2*T*R^5) (h4 : U^4 ≤ 2*H^8*R^7) :
    U ≤ 2*H*T^((1:ℝ)/4)*R^((19:ℝ)/12) := by
  have hprod := mul_le_mul
    (pow_le_pow_left₀ (by positivity : 0 ≤ U^3) h3 4)
    (pow_le_pow_left₀ (by positivity : 0 ≤ U^4) h4 3)
    (by positivity : 0 ≤ (U^4)^3) (by positivity : 0 ≤ (2*T*R^5)^4)
  have hh : U^24 ≤ 128*H^24*T^4*R^41 := by nlinarith only [hprod]
  have hr : 128*H^24*T^4*R^41 ≤ 128*H^24*T^6*R^38 := by
    have hm := mul_le_mul_of_nonneg_left hRT
      (by positivity : 0 ≤ 128*H^24*T^4*R^38)
    convert hm using 1 <;> ring
  have hp : (2*H*T^((1:ℝ)/4)*R^((19:ℝ)/12))^24 =
      16777216*H^24*T^6*R^38 := by
    simp only [mul_pow, adjacent_rpow_nat hT, adjacent_rpow_nat hR]
    norm_num
  apply (pow_le_pow_iff_left₀ hU (by positivity) (by norm_num : (24:ℕ) ≠ 0)).mp
  rw [hp]
  exact (hh.trans hr).trans (by
    have hn : 0 ≤ H^24*T^6*R^38 := by positivity
    nlinarith only [hn])

/-- A finite three-moment envelope, on the precise range where the fourth
moment dominates its time term. No analytic estimate is asserted here. -/
theorem adjacent_moment_envelope {U T H R : ℝ}
    (hU : 0 ≤ U) (hT : 0 ≤ T) (hH : 0 ≤ H) (hR : 0 ≤ R)
    (h8 : T ≤ H^8) (hRT : R^3 ≤ T^2)
    (h2 : U^2 ≤ (T+H^4)*R^3)
    (h3 : U^3 ≤ (T+H^6)*R^5)
    (h4 : U^4 ≤ (T+H^8)*R^7) :
    U ≤ 2*(H^2*R^((3:ℝ)/2)+H*T^((1:ℝ)/4)*R^((19:ℝ)/12)) := by
  by_cases hH4 : T ≤ H^4
  · have hh : U^2 ≤ 2*H^4*R^3 := h2.trans (by gcongr; linarith)
    have hp : (2*H^2*R^((3:ℝ)/2))^2 = 4*H^4*R^3 := by
      norm_num [mul_pow, adjacent_rpow_nat hR, ← pow_mul]
    have hu : U ≤ 2*H^2*R^((3:ℝ)/2) := by
      apply (pow_le_pow_iff_left₀ hU (by positivity) (by norm_num : (2:ℕ) ≠ 0)).mp
      rw [hp]
      nlinarith [mul_nonneg (pow_nonneg hH 4) (pow_nonneg hR 3)]
    exact hu.trans (by
      have hh : 0 ≤ H*T^((1:ℝ)/4)*R^((19:ℝ)/12) := by positivity
      nlinarith)
  · have h2' : U^2 ≤ 2*T*R^3 := h2.trans (by gcongr; linarith)
    by_cases hH6 : T ≤ H^6
    · have hu := adjacent_two_three hU hT hH hR h2'
        (h3.trans (by gcongr; linarith))
      exact hu.trans (by
        have hh : 0 ≤ H^2*R^((3:ℝ)/2) := by positivity
        nlinarith)
    · have hu := adjacent_three_four hU hT hH hR hRT
        (h3.trans (by gcongr; linarith)) (h4.trans (by gcongr; linarith))
      exact hu.trans (by
        have hh : 0 ≤ H^2*R^((3:ℝ)/2) := by positivity
        nlinarith)

end Montgomery.RationalMoment
