module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

/-- Uniform coefficient and power normalization for a genuine integer
square. All powers and ranges are explicit. -/
theorem square_level_monomial_le {q M T U D P s v r : ℝ}
    (hq : 0 ≤ q) (hM : 0 < M) (hT : 0 < T) (hU : 0 < U) (hD : 0 < D)
    (hP : 1 ≤ P) (hqM : q ≤ 2*M^2) (hDP : D ≤ P)
    (hs : 0 ≤ s) (hs8 : s ≤ 8) (_hv : 0 ≤ v) (hv1 : v ≤ 1)
    (hr : 0 ≤ r) (hr10 : r ≤ 10) :
    q^s*(2*T)^v*(U^2/D)^(-r) ≤
      512*P^10*T^v*M^(2*s)*U^(-2*r) := by
  have hPp : 0 < P := by linarith
  have hqPow : q^s ≤ 256*M^(2*s) := by
    calc
      _ ≤ (2*M^2)^s := Real.rpow_le_rpow hq hqM hs
      _ = (2:ℝ)^s*M^(2*s) := by
        rw [Real.mul_rpow (by norm_num) (sq_nonneg M),← Real.rpow_natCast_mul hM.le]
        norm_num only [Nat.cast_ofNat]
      _ ≤ 256*M^(2*s) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hs8
        norm_num at hh
        exact hh
  have hTPow : (2*T)^v ≤ 2*T^v := by
    rw [Real.mul_rpow (by norm_num) hT.le]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hv1
    norm_num at hh
    exact hh
  have hDPow : D^r ≤ P^10 := by
    exact (Real.rpow_le_rpow hD.le hDP hr).trans
      (by simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_le hP hr10)
  have hInv : (U^2/D)^(-r) = D^r*U^(-2*r) := by
    rw [Real.div_rpow (sq_nonneg U) hD.le,
      Real.rpow_neg hD.le,div_inv_eq_mul,← Real.rpow_natCast_mul hU.le]
    norm_num only [Nat.cast_ofNat]
    ring_nf
  rw [hInv]
  calc
    _ ≤ (256*M^(2*s))*(2*T^v)*(P^10*U^(-2*r)) := by gcongr
    _ = _ := by ring

end Montgomery.RationalMoment
