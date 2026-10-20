module
public import RationalMomentDuality
public import Mathlib.Analysis.MeanInequalitiesPow

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset
namespace Montgomery.RationalMoment

theorem finite_nonneg_power_mean {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i) {k : ℕ} (hk : 0 < k) :
    (∑ i ∈ S, f i) ≤ (S.card : ℝ) ^ (1 - 1 / (k : ℝ)) *
      (∑ i ∈ S, (f i) ^ k) ^ (1 / (k : ℝ)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hSum : 0 ≤ ∑ i ∈ S, f i := sum_nonneg hf
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg S
    (p := (k : ℝ)) (by exact_mod_cast hk) hf
  simp only [Real.rpow_natCast] at h
  have hRoot := Real.rpow_le_rpow (pow_nonneg hSum k) h (by positivity : 0 ≤ (k : ℝ)⁻¹)
  rw [Real.pow_rpow_inv_natCast hSum hk.ne',
    Real.mul_rpow (by positivity : 0 ≤ (S.card : ℝ) ^ ((k : ℝ) - 1))
      (sum_nonneg (fun i hi => pow_nonneg (hf i hi) k)),
    ← Real.rpow_mul (Nat.cast_nonneg S.card)] at hRoot
  have hExp : ((k : ℝ) - 1) * (k : ℝ)⁻¹ = 1 - 1 / (k : ℝ) := by
    field_simp
  simpa only [hExp, one_div] using hRoot

theorem ordered_difference_power_mean (A : Finset ℕ) (a : ℕ → ℂ)
    (W : Finset ℝ) {k : ℕ} (hk : 0 < k) :
    (∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ A, a n * phase n (t - u)‖ ^ 2) ≤
      (W.card : ℝ) ^ (2 - 2 / (k : ℝ)) *
        (∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ A, a n * phase n (t - u)‖ ^ (2 * k)) ^
          (1 / (k : ℝ)) := by
  have h := finite_nonneg_power_mean (W ×ˢ W)
    (fun p => ‖∑ n ∈ A, a n * phase n (p.1 - p.2)‖ ^ 2)
    (fun _ _ => sq_nonneg _) hk
  simp only [sum_product, ← pow_mul, card_product, Nat.cast_mul] at h
  have hCard : ((W.card : ℝ) * W.card) ^ (1 - 1 / (k : ℝ)) =
      (W.card : ℝ) ^ (2 - 2 / (k : ℝ)) := by
    rw [← pow_two, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg W.card)]
    congr 1
    norm_num
    ring
  rw [hCard] at h
  exact h

theorem powered_energy_root_shape {X R Z : ℝ} (hX : 0 < X) (hR : 0 < R)
    (hZ : 0 ≤ Z) {k : ℕ} (hk : 0 < k) :
    R ^ (2 - 2 / (k : ℝ)) *
      ((((2 * X) ^ k) ^ 2 * R + (2 * X) ^ k * Real.sqrt Z) ^ (1 / (k : ℝ))) ≤
        4 * (X ^ 2 * R ^ (2 - 1 / (k : ℝ)) +
          X * Z ^ (1 / (2 * (k : ℝ))) * R ^ (2 - 2 / (k : ℝ))) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hq0 : 0 ≤ 1 / (k : ℝ) := by positivity
  have hq1 : 1 / (k : ℝ) ≤ 1 := by
    exact (div_le_one hkR).mpr (by exact_mod_cast hk)
  have hH : 0 < (2 * X) ^ k := by positivity
  have hRoot : ((2 * X) ^ k) ^ (1 / (k : ℝ)) = 2 * X := by
    simpa only [one_div] using Real.pow_rpow_inv_natCast (by positivity : 0 ≤ 2 * X) hk.ne'
  have hDouble : (((2 * X) ^ k) ^ 2) ^ (1 / (k : ℝ)) = (2 * X) ^ 2 := by
    rw [← Real.rpow_natCast_mul hH.le]
    have hExp : ((2 : ℕ) : ℝ) * (1 / (k : ℝ)) = (1 / (k : ℝ)) * (2 : ℕ) := by ring
    rw [hExp, Real.rpow_mul_natCast hH.le, hRoot]
  have hSqrt : (Real.sqrt Z) ^ (1 / (k : ℝ)) = Z ^ (1 / (2 * (k : ℝ))) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hZ]
    congr 1
    ring
  have hSplit := Real.rpow_add_le_add_rpow
    (show 0 ≤ ((2 * X) ^ k) ^ 2 * R by positivity)
    (show 0 ≤ (2 * X) ^ k * Real.sqrt Z by positivity) hq0 hq1
  have hInner :
      ((((2 * X) ^ k) ^ 2 * R + (2 * X) ^ k * Real.sqrt Z) ^ (1 / (k : ℝ))) ≤
        (2 * X) ^ 2 * R ^ (1 / (k : ℝ)) + 2 * X * Z ^ (1 / (2 * (k : ℝ))) := by
    simpa only [Real.mul_rpow (sq_nonneg ((2 * X) ^ k)) hR.le,
      Real.mul_rpow hH.le (Real.sqrt_nonneg Z), hDouble, hRoot, hSqrt] using hSplit
  have h := mul_le_mul_of_nonneg_left hInner
    (Real.rpow_nonneg hR.le (2 - 2 / (k : ℝ)))
  have hRexp : R ^ (2 - 2 / (k : ℝ)) * R ^ (1 / (k : ℝ)) =
      R ^ (2 - 1 / (k : ℝ)) := by
    rw [← Real.rpow_add hR]
    congr 1
    ring
  have hId : R ^ (2 - 2 / (k : ℝ)) *
      ((2 * X) ^ 2 * R ^ (1 / (k : ℝ)) + 2 * X * Z ^ (1 / (2 * (k : ℝ)))) =
        4 * (X ^ 2 * R ^ (2 - 1 / (k : ℝ))) +
          2 * (X * Z ^ (1 / (2 * (k : ℝ))) * R ^ (2 - 2 / (k : ℝ))) := by
    calc
      _ = (2 * X) ^ 2 * (R ^ (2 - 2 / (k : ℝ)) * R ^ (1 / (k : ℝ))) +
          2 * (X * Z ^ (1 / (2 * (k : ℝ))) * R ^ (2 - 2 / (k : ℝ))) := by ring
      _ = _ := by rw [hRexp]; ring
  rw [hId] at h
  have hNonneg : 0 ≤ X * Z ^ (1 / (2 * (k : ℝ))) * R ^ (2 - 2 / (k : ℝ)) := by positivity
  linarith

end Montgomery.RationalMoment
