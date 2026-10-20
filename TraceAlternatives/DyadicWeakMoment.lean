module
public import DensityEnergyGM.DifferenceLayerCake
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset
namespace Montgomery.RationalMoment

/-- A finite dyadic weak-moment argument. The number of levels is controlled
by the logarithm of the height, independently of the finite set and weights. -/
theorem finite_dyadic_weighted_square_bound {ι : Type*} (S : Finset ι)
    (r v : ι → ℝ) {T B : ℝ} (hT : 2 ≤ T) (hB : 0 ≤ B)
    (hr : ∀ i ∈ S, 0 ≤ r i) (hv : ∀ i ∈ S, 0 ≤ v i)
    (hvT : ∀ i ∈ S, v i ≤ T)
    (hWeak : ∀ U : ℝ, 1 ≤ U →
      U^2 * (∑ i ∈ S.filter (fun i => U ≤ v i), r i) ≤ B) :
    (∑ i ∈ S, r i * v i ^ 2) ≤
      (2+Real.logb 2 T)*((∑ i ∈ S, r i)+4*B) := by
  classical
  have hTp : 0 < T := by linarith
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogT : 0 ≤ Real.logb 2 T := by
    unfold Real.logb
    exact div_nonneg (Real.log_nonneg (by linarith)) hlogtwo.le
  let K : ℕ := ⌈Real.logb 2 T⌉₊+1
  have hK : (K:ℝ) ≤ 2+Real.logb 2 T := by
    have hh := Nat.ceil_lt_add_one hlogT
    dsimp only [K]
    push_cast
    linarith
  have hD : 1 ≤ 2+Real.logb 2 T := by linarith
  have hPoint : ∀ i ∈ S, r i*v i^2 ≤
      r i+4*∑ j ∈ range K, (2:ℝ)^(2*j)*(if (2:ℝ)^j ≤ v i then r i else 0) := by
    intro i hi
    have hri := hr i hi
    have hsum : 0 ≤ ∑ j ∈ range K,
        (2:ℝ)^(2*j)*(if (2:ℝ)^j ≤ v i then r i else 0) := by positivity
    by_cases hlow : v i ≤ 1
    · have hh : r i*v i^2 ≤ r i := by
        have hv0 := hv i hi
        have hr0 := hr i hi
        have hp : v i^2 ≤ 1 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hp hr0]
      linarith
    have hvp : 0 < v i := by linarith
    have hlv : 0 ≤ Real.logb 2 (v i) := by
      unfold Real.logb
      exact div_nonneg (Real.log_nonneg (by linarith)) hlogtwo.le
    let j : ℕ := ⌊Real.logb 2 (v i)⌋₊
    have hjlo : (j:ℝ) ≤ Real.logb 2 (v i) := Nat.floor_le hlv
    have hjhi : Real.logb 2 (v i) < (j:ℝ)+1 := Nat.lt_floor_add_one _
    have hvId : (2:ℝ)^(Real.logb 2 (v i))=v i :=
      Real.rpow_logb (by norm_num) (by norm_num) hvp
    have hPowlo : (2:ℝ)^j ≤ v i := by
      have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hjlo
      simpa only [Real.rpow_natCast,hvId] using hh
    have hPowhi : v i < 2*(2:ℝ)^j := by
      have hh := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) hjhi
      rw [hvId,Real.rpow_add (by norm_num),Real.rpow_natCast,Real.rpow_one] at hh
      nlinarith
    have hlmono : Real.logb 2 (v i) ≤ Real.logb 2 T := by
      unfold Real.logb
      exact div_le_div_of_nonneg_right (Real.log_le_log hvp (hvT i hi)) hlogtwo.le
    have hjK : j < K := by
      have hh : (j:ℝ) ≤ (⌈Real.logb 2 T⌉₊:ℝ) :=
        hjlo.trans (hlmono.trans (Nat.le_ceil _))
      have hn : j ≤ ⌈Real.logb 2 T⌉₊ := by exact_mod_cast hh
      dsimp only [K]
      omega
    have hterm : (2:ℝ)^(2*j)*r i ≤ ∑ j ∈ range K,
        (2:ℝ)^(2*j)*(if (2:ℝ)^j ≤ v i then r i else 0) := by
      have hh := single_le_sum (f := fun j =>
        (2:ℝ)^(2*j)*(if (2:ℝ)^j ≤ v i then r i else 0))
        (fun j hj => by positivity) (mem_range.mpr hjK)
      simpa only [ite_eq_left hPowlo] using hh
    have hSquare : r i*v i^2 ≤ 4*((2:ℝ)^(2*j)*r i) := by
      have hh := pow_le_pow_left₀ (hv i hi) hPowhi.le 2
      rw [mul_pow,← pow_mul, Nat.mul_comm j 2] at hh
      norm_num at hh
      nlinarith [mul_le_mul_of_nonneg_left hh (hr i hi)]
    nlinarith [hr i hi]
  have hRegroup : (∑ i ∈ S, (r i+4*(∑ j ∈ range K,
      (2:ℝ)^(2*j)*(if (2:ℝ)^j ≤ v i then r i else 0)))) =
      (∑ i ∈ S, r i)+4*∑ j ∈ range K,
        ((2:ℝ)^j)^2*(∑ i ∈ S.filter (fun i => (2:ℝ)^j ≤ v i), r i) := by
    rw [sum_add_distrib,← mul_sum,sum_comm]
    congr 2
    apply sum_congr rfl
    intro j hj
    rw [← mul_sum]
    simp only [sum_filter]
    rw [← pow_mul,Nat.mul_comm j 2]
  calc
    _ ≤ ∑ i ∈ S, (r i+4*(∑ j ∈ range K,
        (2:ℝ)^(2*j)*(if (2:ℝ)^j ≤ v i then r i else 0))) := sum_le_sum hPoint
    _ = _ := hRegroup
    _ ≤ (∑ i ∈ S, r i)+4*∑ _j ∈ range K, B := by
      gcongr with j hj
      exact hWeak _ (one_le_pow₀ (by norm_num))
    _ = (∑ i ∈ S, r i)+4*(K:ℝ)*B := by simp; ring
    _ ≤ (2+Real.logb 2 T)*(∑ i ∈ S, r i)+4*(2+Real.logb 2 T)*B := by
      apply add_le_add
      · exact le_mul_of_one_le_left (sum_nonneg hr) hD
      · gcongr
    _ = _ := by ring

end Montgomery.RationalMoment
