module
public import LaterPairs.PairSlabExcess
public import TwoTermDyadic
public import ExcessCompactPrefix

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
namespace TaoTrudgianYang2025
open MathCollab.Density MathCollab.Density.Stronger
open Montgomery.CriticalPeak Montgomery.RationalMoment.RightDetector

/-- Both physical excess terms, with constants uniform before height and amplitude. -/
theorem ExponentPair.critical_physical_excess_general {k l η ε : ℝ}
    (hpair : ExponentPair k l) (hk : 0 < k)
    (hη : 0 < η) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ v : ℝ,
      0 < v → (3*T)^(1/8+η) ≤ v →
      (∫ t in Icc 0 (3*T),criticalExcess v t) ≤
        C*T^ε*(T*v^(-5:ℝ)+T^(1+l/k)*v^(-3-(2+4*l)/k)) := by
  have hl : 0 < l := lt_of_lt_of_le (by norm_num) hpair.inTriangle.2.2.1
  have hden : 0 < 3+(2+4*l)/k := by positivity
  have hp : 1 ≤ 1+ε := by linarith
  have hr : 1 ≤ 1+l/k+ε := by have hh := div_pos hl hk; linarith
  obtain ⟨B₀,hB₀⟩ := eventually_atTop.mp (hpair.critical_slab_excess_general hk hη hε)
  let B : ℝ := max B₀ 1
  have hB : 1 ≤ B := le_max_right _ _
  have hB0 : 0 ≤ B := by linarith
  obtain ⟨M,hM⟩ := criticalExcess_compact_prefix hB0
  let C₁ : ℝ := (2/5)*(6:ℝ)^(1+ε)
  let C₂ : ℝ := (2/(3+(2+4*l)/k))*(6:ℝ)^(1+l/k+ε)
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  have hC₂ : 0 < C₂ := by dsimp [C₂]; positivity
  refine ⟨C₁+C₂,by positivity,?_⟩
  have hq : 0 < (1/8:ℝ)+η := by linarith
  have hsmall := (tendsto_rpow_atTop hq).eventually (eventually_ge_atTop M)
  filter_upwards [hsmall,eventually_ge_atTop B] with T hsmall hT
  intro v hv hvrange
  have hT1 : 1 ≤ T := hB.trans hT
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < 3*T := by positivity
  have hvM : M ≤ v := hsmall.trans ((Real.rpow_le_rpow hT0.le (by linarith) hq.le).trans hvrange)
  have hpref := hM v hvM
  have hdyad : ∀ H : ℝ,B ≤ H → H ≤ 3*T →
      (∫ t in H..2*H,criticalExcess v t) ≤
        ((2/5)*v^(-5:ℝ))*H^(1+ε)+
          ((2/(3+(2+4*l)/k))*v^(-3-(2+4*l)/k))*H^(1+l/k+ε) := by
    intro H hBH hHT
    have hH1 : 1 ≤ H := hB.trans hBH
    have hH0 : 0 < H := by linarith
    have hvH : H^(1/8+η) ≤ v :=
      (Real.rpow_le_rpow hH0.le hHT hq.le).trans hvrange
    have hs := hB₀ H (((le_max_left _ _).trans hBH)) v hv hvH
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : H ≤ 2*H)] at hs
    convert hs using 1
    ring
  have hh := integral_zero_le_of_two_dyadic_powers (criticalExcess v)
    (criticalExcess_continuous v) (criticalExcess_nonneg v)
    hp hr hB (by linarith : B ≤ 3*T)
    (by positivity : 0 ≤ (2/5)*v^(-5:ℝ))
    (by positivity : 0 ≤ (2/(3+(2+4*l)/k))*v^(-3-(2+4*l)/k)) hpref hdyad
  have hTp1 : T^(1+ε)=T*T^ε := by rw [Real.rpow_add hT0,Real.rpow_one]
  have hTpr : T^(1+l/k+ε)=T^(1+l/k)*T^ε := Real.rpow_add hT0 _ _
  have hx : 0 ≤ T*v^(-5:ℝ) := by positivity
  have hy : 0 ≤ T^(1+l/k)*v^(-3-(2+4*l)/k) := by positivity
  calc
    (∫ t in Icc 0 (3*T),criticalExcess v t) = ∫ t in 0..3*T,criticalExcess v t := by
      rw [integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hL0.le]
    _ ≤ ((2/5)*v^(-5:ℝ))*(2:ℝ)^(1+ε)*(3*T)^(1+ε)+
        ((2/(3+(2+4*l)/k))*v^(-3-(2+4*l)/k))*(2:ℝ)^(1+l/k+ε)*(3*T)^(1+l/k+ε) := hh
    _ = C₁*T^ε*(T*v^(-5:ℝ))+C₂*T^ε*(T^(1+l/k)*v^(-3-(2+4*l)/k)) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hT0.le,
        Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hT0.le,hTp1,hTpr]
      dsimp only [C₁,C₂]
      rw [show (6:ℝ)=2*3 by norm_num,
        Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (0:ℝ) ≤ 3),
        Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (0:ℝ) ≤ 3)]
      ring
    _ ≤ (C₁+C₂)*T^ε*(T*v^(-5:ℝ)+T^(1+l/k)*v^(-3-(2+4*l)/k)) := by
      have hxy := mul_nonneg (mul_nonneg hC₁.le (Real.rpow_pos_of_pos hT0 ε).le) hy
      have hyx := mul_nonneg (mul_nonneg hC₂.le (Real.rpow_pos_of_pos hT0 ε).le) hx
      nlinarith
end TaoTrudgianYang2025
