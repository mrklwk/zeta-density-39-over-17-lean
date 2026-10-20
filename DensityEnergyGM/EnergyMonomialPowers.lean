module
public import DensityEnergyGM.SecondMomentPowerAlgebra

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Montgomery.RationalMoment

theorem energy_monomial_rpow {K N T R V : ℝ} (δ α β γ q : ℝ)
    (hK : 0 ≤ K) (hN : 0 ≤ N) (hT : 0 ≤ T) (hR : 0 ≤ R) (hV : 0 ≤ V) :
    (K * T ^ δ * N ^ α * T ^ β * R ^ γ / V ^ 2) ^ q =
      K ^ q * T ^ (δ * q) *
        (N ^ (α * q) * T ^ (β * q) * V ^ (-2 * q) * R ^ (γ * q)) := by
  rw [Real.div_rpow (by positivity) (sq_nonneg V),
    Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hK (by positivity)]
  rw [← Real.rpow_mul hT, ← Real.rpow_mul hN, ← Real.rpow_mul hT, ← Real.rpow_mul hR,
    ← Real.rpow_natCast V 2, ← Real.rpow_mul hV, div_eq_mul_inv, ← Real.rpow_neg hV]
  have hExp : -((2 : ℝ) * q) = -2 * q := by ring
  simp only [Nat.cast_ofNat]
  rw [hExp]
  ring

end Montgomery.RationalMoment
