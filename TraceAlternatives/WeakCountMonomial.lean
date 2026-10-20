module
public import TraceAlternatives.WeakPowerInterpolation

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Montgomery.RationalMoment

/-- An exact weak-count monomial-to-weighted-square conversion. The weight
mass uses its true bound R² and true squared-cell energy E. -/
theorem weak_count_monomial_bound {R E K M T U mass a b w : ℝ}
    (hR : 0 ≤ R) (hE : 0 ≤ E) (hK : 0 ≤ K) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hU : 0 < U) (hMass : 0 ≤ mass) (hw : 4 ≤ w)
    (hMassR : mass ≤ R^2)
    (hSq : mass^2 ≤ K*E*M^a*T^b*U^(-w)) :
    U^2*mass ≤ K^(2/w)*E^(2/w)*M^(2*a/w)*T^(2*b/w)*R^(2-8/w) := by
  have hwp : 0 < w := by linarith
  let Z := K*E*M^a*T^b
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  let D := Z^(1/2:ℝ)
  have hD : 0 ≤ D := Real.rpow_nonneg hZ _
  have hRoot : mass ≤ D*U^(-(w/2)) := by
    have hh := Real.rpow_le_rpow (sq_nonneg mass) hSq (by norm_num : (0:ℝ)≤1/2)
    have hMassId : (mass^2)^(1/2:ℝ)=mass := by
      rw [← Real.rpow_natCast_mul hMass]
      norm_num
    change (mass^2)^(1/2:ℝ) ≤ (Z*U^(-w))^(1/2:ℝ) at hh
    rw [hMassId,Real.mul_rpow hZ (Real.rpow_nonneg hU.le (-w)),← Real.rpow_mul hU.le] at hh
    rw [show (-w)*(1/2:ℝ)=-(w/2) by ring] at hh
    exact hh
  have hθ0 : 0 ≤ 4/w := by positivity
  have hθ1 : 4/w ≤ 1 := (div_le_one hwp).mpr hw
  have hpθ : (w/2)*(4/w)=2 := by field_simp; ring
  have hh := weak_power_square_mass_bound (sq_nonneg R) hD hU hθ0 hθ1 hpθ hMassR hRoot
  have hId : (R^2)^(1-4/w)*D^(4/w) =
      K^(2/w)*E^(2/w)*M^(2*a/w)*T^(2*b/w)*R^(2-8/w) := by
    have hRId : (R^2)^(1-4/w)=R^(2-8/w) := by
      rw [← Real.rpow_natCast_mul hR]
      congr 1
      ring
    have hDId : D^(4/w) = K^(2/w)*E^(2/w)*M^(2*a/w)*T^(2*b/w) := by
      dsimp only [D]
      rw [← Real.rpow_mul hZ]
      have hExp : (1/2:ℝ)*(4/w)=2/w := by ring
      rw [hExp]
      dsimp only [Z]
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity),Real.mul_rpow hK hE,
        ← Real.rpow_mul hM,← Real.rpow_mul hT]
      rw [show a*(2/w)=2*a/w by ring,show b*(2/w)=2*b/w by ring]
    rw [hRId,hDId]
    ring
  exact hh.trans_eq hId

end Montgomery.RationalMoment
