module
public import DensityEnergyGM.RealDyadicPowerBlocks

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Finset
namespace Montgomery.RationalMoment

theorem polynomial_height_scaled_second_energy
    (B δ : ℝ) (hB : 0 < B) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ X D : ℝ, 2 ≤ T → 0 < X → X ≤ T ^ B → 0 < D →
      ∀ A : Finset ℕ, (∀ n ∈ A, 0 < n ∧ X < n ∧ (n : ℝ) ≤ 2 * X) →
      ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀ + T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t - u|) →
      ∀ a : ℕ → ℂ, (∀ n ∈ A, ‖a n‖ ≤ D) →
      (∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ A, a n * phase n (t - u)‖ ^ 2) ≤
        C * T ^ δ * D ^ 2 * (X ^ 2 * (W.card : ℝ) +
          X * Real.sqrt (T * (discreteAdditiveEnergy W : ℝ))) := by
  obtain ⟨C, hC, hBase⟩ := polynomial_height_dirichlet_second_energy B δ hB hδ
  refine ⟨C, hC, ?_⟩
  intro T t₀ X D hT hX hXT hD A hA W hW hSep a ha
  let b : ℕ → ℂ := fun n => a n / (D : ℂ)
  have hb : ∀ n ∈ A, ‖b n‖ ≤ 1 := by
    intro n hn
    dsimp only [b]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
    exact (div_le_one hD).mpr (ha n hn)
  have hEq (v : ℝ) : (∑ n ∈ A, a n * phase n v) =
      (D : ℂ) * ∑ n ∈ A, b n * phase n v := by
    rw [mul_sum]
    apply sum_congr rfl
    intro n _
    dsimp only [b]
    field_simp [Complex.ofReal_ne_zero.mpr hD.ne']
  have hMoment : (∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ A, a n * phase n (t - u)‖ ^ 2) =
      D ^ 2 * ∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ A, b n * phase n (t - u)‖ ^ 2 := by
    simp_rw [hEq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD, mul_pow]
    simp only [mul_sum]
  rw [hMoment]
  have h := mul_le_mul_of_nonneg_left (hBase T t₀ X hT hX hXT A hA W hW hSep b hb)
    (sq_nonneg D)
  exact h.trans_eq (by ring)

theorem powered_length_height {B T X : ℝ} (_hB : 0 < B) (hT : 2 ≤ T)
    (hX : 0 < X) (hXT : X ≤ T ^ B) (k : ℕ) :
    (2 * X) ^ k ≤ T ^ ((k : ℝ) * (B + 1)) := by
  have hTp : 0 < T := by linarith
  have hScale : 2 * X ≤ T ^ (B + 1) := by
    rw [Real.rpow_add hTp, Real.rpow_one]
    nlinarith [mul_le_mul hT hXT hX.le hTp.le]
  calc
    _ ≤ (T ^ (B + 1)) ^ k := pow_le_pow_left₀ (by positivity) hScale k
    _ = _ := by rw [← Real.rpow_mul_natCast hTp.le]; congr 1; ring

/-- The complete ordered 2k-th difference moment. Every powered block is
included, and the original additive energy is retained throughout. -/
theorem powered_dirichlet_difference_energy
    (k : ℕ) (B δ ν : ℝ) (hk : 0 < k) (hB : 0 < B) (hδ : 0 < δ) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ X : ℝ, 2 ≤ T → 0 < X → X ≤ T ^ B →
      ∀ A : Finset ℕ, (∀ n ∈ A, 0 < n ∧ X < n ∧ (n : ℝ) ≤ 2 * X) →
      ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀ + T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t - u|) →
      ∀ a : ℕ → ℂ, (∀ n ∈ A, ‖a n‖ ≤ 1) →
      (∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ A, a n * phase n (t - u)‖ ^ (2 * k)) ≤
        C * T ^ δ * ((2 * X) ^ k) ^ (2 * ν) *
          (((2 * X) ^ k) ^ 2 * (W.card : ℝ) +
            (2 * X) ^ k * Real.sqrt (T * (discreteAdditiveEnergy W : ℝ))) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨D, hD, hCoeff⟩ := finite_support_power_coeff_bound_uniform k ν hν
  obtain ⟨C₀, hC₀, hBase⟩ := polynomial_height_scaled_second_energy
    ((k : ℝ) * (B + 1)) δ (by positivity) hδ
  refine ⟨(k : ℝ) ^ 2 * C₀ * D ^ 2, by positivity, ?_⟩
  intro T t₀ X hT hX hXT A hA W hW hSep a ha
  let H : ℝ := (2 * X) ^ k
  let S := finiteSupportProducts A k
  let b := finiteSupportPowerCoeff A k a
  let F : ℕ → ℝ := fun r => ∑ t ∈ W, ∑ u ∈ W,
    ‖∑ m ∈ realDyadicSupport S (2 ^ r * X ^ k), b m * phase m (t - u)‖ ^ 2
  have hH : 0 < H := by dsimp only [H]; positivity
  have hHT := powered_length_height hB hT hX hXT k
  have hBlock : ∀ r ∈ range k, F r ≤
      C₀ * T ^ δ * (D * H ^ ν) ^ 2 *
        (H ^ 2 * (W.card : ℝ) + H * Real.sqrt (T * (discreteAdditiveEnergy W : ℝ))) := by
    intro r hr
    let Y : ℝ := 2 ^ r * X ^ k
    have hY : 0 < Y := by dsimp only [Y]; positivity
    have hYH : Y ≤ H := by
      dsimp only [Y, H]
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (mem_range.mp hr).le)
        (pow_nonneg hX.le k)
    have hGeom : ∀ m ∈ realDyadicSupport S Y, 0 < m ∧ Y < m ∧ (m : ℝ) ≤ 2 * Y := by
      intro m hm
      have h := (mem_filter.mp hm).2
      exact ⟨by exact_mod_cast (hY.trans h.1), h⟩
    have hCoeffBlock : ∀ m ∈ realDyadicSupport S Y, ‖b m‖ ≤ D * H ^ ν := by
      intro m hm
      have hProd := (mem_filter.mp hm).1
      have hBounds := finite_support_products_bounds hX (fun n hn => (hA n hn).2) hk hProd
      exact (hCoeff A a ha m (hGeom m hm).1).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hBounds.2 hν.le) hD.le)
    have h := hBase T t₀ Y (D * H ^ ν) hT hY (hYH.trans hHT) (by positivity)
      (realDyadicSupport S Y) hGeom W hW hSep b hCoeffBlock
    change F r ≤ _ at h
    have hMono : Y ^ 2 * (W.card : ℝ) +
        Y * Real.sqrt (T * (discreteAdditiveEnergy W : ℝ)) ≤
        H ^ 2 * (W.card : ℝ) + H * Real.sqrt (T * (discreteAdditiveEnergy W : ℝ)) :=
      add_le_add
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hY.le hYH 2) (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_right hYH (Real.sqrt_nonneg _))
    exact h.trans (mul_le_mul_of_nonneg_left hMono (by positivity))
  have hRecombine : (∑ t ∈ W, ∑ u ∈ W,
      ‖∑ n ∈ A, a n * phase n (t - u)‖ ^ (2 * k)) ≤
      (k : ℝ) * ∑ r ∈ range k, F r := by
    calc
      _ ≤ ∑ t ∈ W, ∑ u ∈ W, (k : ℝ) *
          ∑ r ∈ range k, ‖∑ m ∈ realDyadicSupport S (2 ^ r * X ^ k),
            b m * phase m (t - u)‖ ^ 2 := by
        apply sum_le_sum
        intro t _
        apply sum_le_sum
        intro u _
        exact finite_support_power_second_le_blocks hX A hA a hk (t - u)
      _ = _ := by
        simp_rw [← mul_sum]
        congr 1
        dsimp only [F]
        calc
          _ = ∑ t ∈ W, ∑ r ∈ range k, ∑ u ∈ W,
              ‖∑ m ∈ realDyadicSupport S (2 ^ r * X ^ k), b m * phase m (t - u)‖ ^ 2 := by
            apply sum_congr rfl
            intro t _
            rw [sum_comm]
          _ = _ := sum_comm
  calc
    _ ≤ (k : ℝ) * ∑ r ∈ range k, F r := hRecombine
    _ ≤ (k : ℝ) * ∑ _r ∈ range k,
        C₀ * T ^ δ * (D * H ^ ν) ^ 2 *
          (H ^ 2 * (W.card : ℝ) + H * Real.sqrt (T * (discreteAdditiveEnergy W : ℝ))) := by
      exact mul_le_mul_of_nonneg_left (sum_le_sum hBlock) hkR.le
    _ = _ := by
      simp only [sum_const, card_range, nsmul_eq_mul, mul_pow]
      rw [← Real.rpow_mul_natCast hH.le]
      norm_num only [Nat.cast_ofNat]
      rw [show ν * 2 = 2 * ν by ring]
      dsimp only [H]
      ring_nf

end Montgomery.RationalMoment
