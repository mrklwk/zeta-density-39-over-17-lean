module
public import RationalMomentDuality
public import Mathlib.Analysis.MeanInequalities

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Finset
namespace Montgomery.RationalMoment

/-- Three-factor Hölder with the actual first and second cell-weight sums.
This is a finite inequality, without any spectral positivity assumption. -/
theorem weighted_cube_holder {ι : Type*} (S : Finset ι) (r v : ι → ℝ)
    (hr : ∀ i ∈ S, 0 ≤ r i) (hv : ∀ i ∈ S, 0 ≤ v i) :
    (∑ i ∈ S, r i * v i ^ 2) ≤
      (∑ i ∈ S, r i) ^ (1 / 3 : ℝ) *
        (∑ i ∈ S, r i ^ 2) ^ (1 / 3 : ℝ) *
          (∑ i ∈ S, v i ^ 6) ^ (1 / 3 : ℝ) := by
  have hsumr : 0 ≤ ∑ i ∈ S, r i := sum_nonneg hr
  have hsumr2 : 0 ≤ ∑ i ∈ S, r i ^ 2 := sum_nonneg (fun i _ => sq_nonneg _)
  have hsumr32 : 0 ≤ ∑ i ∈ S, r i ^ (3 / 2 : ℝ) :=
    sum_nonneg (fun i hi => Real.rpow_nonneg (hr i hi) _)
  have hCauchy := Real.inner_le_Lp_mul_Lq_of_nonneg S
    (f := fun i => Real.sqrt (r i)) (g := r)
    (p := 2) (q := 2) (by norm_num [Real.holderConjugate_iff])
    (fun i _ => Real.sqrt_nonneg _) hr
  have hProd : ∀ i ∈ S, Real.sqrt (r i) * r i = r i ^ (3 / 2 : ℝ) := by
    intro i hi
    by_cases hz : r i = 0
    · simp [hz]
    have hp : 0 < r i := lt_of_le_of_ne (hr i hi) (Ne.symm hz)
    rw [Real.sqrt_eq_rpow]
    calc
      _ = r i ^ (1 / 2 : ℝ) * r i ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = r i ^ ((1 / 2 : ℝ) + 1) := (Real.rpow_add hp _ _).symm
      _ = _ := by norm_num
  have hC : (∑ i ∈ S, r i ^ (3 / 2 : ℝ)) ≤
      (∑ i ∈ S, r i) ^ (1 / 2 : ℝ) * (∑ i ∈ S, r i ^ 2) ^ (1 / 2 : ℝ) := by
    simp only [Real.rpow_two] at hCauchy
    rw [sum_congr rfl hProd] at hCauchy
    have hSqrt : (∑ i ∈ S, Real.sqrt (r i) ^ 2) = ∑ i ∈ S, r i :=
      sum_congr rfl (fun i hi => Real.sq_sqrt (hr i hi))
    rw [hSqrt] at hCauchy
    exact hCauchy
  have hRoot : (∑ i ∈ S, r i ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
      (∑ i ∈ S, r i) ^ (1 / 3 : ℝ) * (∑ i ∈ S, r i ^ 2) ^ (1 / 3 : ℝ) := by
    have hh := Real.rpow_le_rpow hsumr32 hC (by norm_num : (0 : ℝ) ≤ 2 / 3)
    rw [Real.mul_rpow (Real.rpow_nonneg hsumr _) (Real.rpow_nonneg hsumr2 _),
      ← Real.rpow_mul hsumr, ← Real.rpow_mul hsumr2] at hh
    norm_num at hh
    exact hh
  have hHolder := Real.inner_le_Lp_mul_Lq_of_nonneg S
    (f := r) (g := fun i => v i ^ 2)
    (p := 3 / 2) (q := 3) (by norm_num [Real.holderConjugate_iff])
    hr (fun i _ => sq_nonneg _)
  have hH : (∑ i ∈ S, r i * v i ^ 2) ≤
      (∑ i ∈ S, r i ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) *
        (∑ i ∈ S, v i ^ 6) ^ (1 / 3 : ℝ) := by
    simpa only [one_div_div, div_one, Real.rpow_ofNat, Real.rpow_natCast, ← pow_mul, Nat.reduceMul] using hHolder
  exact hH.trans (mul_le_mul_of_nonneg_right hRoot
    (Real.rpow_nonneg (sum_nonneg (fun i _ => pow_nonneg (hv i ‹_›) _)) _))

end Montgomery.RationalMoment
