module
public import LaterPairs.PairPhysicalExcess
public import DetectorPowerRange

@[expose] public section
set_option autoImplicit false
noncomputable section
open Real Filter MeasureTheory Set
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger MathCollab.Density
open TaoTrudgianYang2025

/-- The actual complementary zeros obey the two native pair-tail budgets.
The numerical slack accounts explicitly for the detector denominator and logarithm. -/
theorem smoothLongZeroCount_pair_tail_general {k l σ a δ η q ε : ℝ}
    (hpair : ExponentPair k l) (hk : 0 < k)
    (hw : QuadraticWindow σ a) (hsigma : 7/9 ≤ σ)
    (hδ : 0 < δ) (hδcap : δ ≤ 1/8) (hη : 0 < η) (hε : 0 < ε)
    (hq : 1/8 < q) (hmargin : q+δ/2 < (3*a/4)*(σ-1/2))
    (hfirst : 1-6*q ≤ 3*a*(1-σ)+ε/2)
    (hsecond : 1+l/k-(4+(2+4*l)/k)*q ≤ 3*a*(1-σ)+ε/2) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ T : ℝ in atTop,
      (smoothLongZeroCount η σ a δ T:ℝ) ≤ C*T^(3*a*(1-σ)+ε) := by
  let b : ℝ := 4+(2+4*l)/k
  let ξ : ℝ := (q-1/8)/2
  have hξ : 0 < ξ := by dsimp [ξ]; linarith
  have hqξ : 1/8+ξ < q := by dsimp [ξ]; linarith
  have hquarter : 0 < ε/4 := by positivity
  have hl : 0 < l := lt_of_lt_of_le (by norm_num) hpair.inTriangle.2.2.1
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨Cm,D,hCm,hD,hraw⟩ := smoothLongZeroCount_excess_reduction hw hsigma hδ hδcap hη
  obtain ⟨A,hA,htail⟩ := hpair.critical_physical_excess_general hk hξ hquarter
  have hpower := criticalMeanThreshold_dominates_power hCm
    (show 0 < 4*Real.pi by positivity) hmargin
  have hrange := criticalMeanThreshold_dominates_power hCm
    (show 0 < 4*Real.pi*(3:ℝ)^(1/8+ξ) by positivity)
    (show (1/8+ξ)+δ/2 < (3*a/4)*(σ-1/2) by linarith)
  let C : ℝ := 2*D*A/(4*Real.pi)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [hraw,htail,hpower,hrange,eventually_ge_atTop (2:ℝ),
    log_pow_eventually_le_rpow 1 hquarter] with T hr ht hp hv hT hlogT
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  let v : ℝ := criticalMeanThreshold Cm σ a δ T/(4*Real.pi)
  have hpv : T^q ≤ v := (le_div_iff₀ (by positivity : 0 < 4*Real.pi)).mpr
    (by simpa only [mul_comm] using hp)
  have hv0 : 0 < v := lt_of_lt_of_le (Real.rpow_pos_of_pos hT0 q) hpv
  have hvphys : (3*T)^(1/8+ξ) ≤ v := by
    apply (le_div_iff₀ (by positivity : 0 < 4*Real.pi)).mpr
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hT0.le]
    convert hv using 1
    ring
  have ht' := ht v hv0 hvphys
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hv6 : v^(-6:ℝ) ≤ T^(-6*q) := by
    calc
      _ ≤ (T^q)^(-6:ℝ) := Real.rpow_le_rpow_of_nonpos (by positivity) hpv (by norm_num)
      _ = _ := by rw [← Real.rpow_mul hT0.le]; congr 1; ring
  have hvb : v^(-b) ≤ T^(-b*q) := by
    calc
      _ ≤ (T^q)^(-b) := Real.rpow_le_rpow_of_nonpos (by positivity) hpv (by linarith)
      _ = _ := by rw [← Real.rpow_mul hT0.le]; congr 1; ring
  have hx : T*v^(-6:ℝ) ≤ T^(3*a*(1-σ)+ε/2) := by
    calc
      _ ≤ T*T^(-6*q) := mul_le_mul_of_nonneg_left hv6 hT0.le
      _ = T^(1-6*q) := by
        rw [show 1-6*q=1+(-6*q) by ring,Real.rpow_add hT0,Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT1 hfirst
  have hy : T^(1+l/k)*v^(-b) ≤ T^(3*a*(1-σ)+ε/2) := by
    calc
      _ ≤ T^(1+l/k)*T^(-b*q) := mul_le_mul_of_nonneg_left hvb (by positivity)
      _ = T^(1+l/k-b*q) := by
        convert (Real.rpow_add hT0 (1+l/k) (-b*q)).symm using 1
        ring_nf
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT1 hsecond
  have hid1 : v^(-5:ℝ)=v*v^(-6:ℝ) := by
    rw [show (-5:ℝ)=1+(-6) by norm_num,Real.rpow_add hv0,Real.rpow_one]
  have hid2 : v^(-3-(2+4*l)/k)=v*v^(-b) := by
    rw [show -3-(2+4*l)/k=1+(-b) by dsimp [b]; ring,
      Real.rpow_add hv0,Real.rpow_one]
  have hB : criticalMeanThreshold Cm σ a δ T=4*Real.pi*v := by dsimp [v]; field_simp
  have hpre : (smoothLongZeroCount η σ a δ T:ℝ) ≤
      (D*A/(4*Real.pi))*Real.log T*T^(ε/4)*(T*v^(-6:ℝ)+T^(1+l/k)*v^(-b)) := by
    have hh := hr.trans (mul_le_mul_of_nonneg_left ht' (by positivity : 0 ≤ D*Real.log T))
    rw [hB,hid1,hid2] at hh
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < 4*Real.pi*v)).mp
    convert hh using 1 <;> field_simp
  calc
    _ ≤ (D*A/(4*Real.pi))*Real.log T*T^(ε/4)*
        (T*v^(-6:ℝ)+T^(1+l/k)*v^(-b)) := hpre
    _ ≤ (D*A/(4*Real.pi))*T^(ε/4)*T^(ε/4)*
        (T^(3*a*(1-σ)+ε/2)+T^(3*a*(1-σ)+ε/2)) := by
      gcongr
      simpa only [pow_one] using hlogT
    _ = C*T^(3*a*(1-σ)+ε) := by
      dsimp only [C]
      rw [show T^(3*a*(1-σ)+ε/2)+T^(3*a*(1-σ)+ε/2)=2*T^(3*a*(1-σ)+ε/2) by ring]
      have he : ε/4+ε/4+(3*a*(1-σ)+ε/2)=3*a*(1-σ)+ε := by ring
      calc
        _ = (2*D*A/(4*Real.pi))*((T^(ε/4)*T^(ε/4))*T^(3*a*(1-σ)+ε/2)) := by ring
        _ = _ := by rw [← Real.rpow_add hT0,← Real.rpow_add hT0,he]
end Montgomery.RationalMoment.RightDetector
