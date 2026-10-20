module
public import DensityEnergyGM.BasicPairSecondEnergy

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset
namespace Montgomery.RationalMoment

/-- Absorb the literal gcd logarithm at any fixed polynomial height. -/
theorem polynomial_height_log_loss (B δ : ℝ) (hB : 0 < B) (hδ : 0 < δ)
    {T X : ℝ} (hT : 1 ≤ T) (hX : 0 < X) (hXT : X ≤ T ^ B) :
    1 + Real.log ⌊2 * X⌋₊ ≤
      (1 + (2 : ℝ) ^ (δ / B) / (δ / B)) * T ^ δ := by
  have hTp : 0 < T := by linarith
  have hq : 0 < δ / B := div_pos hδ hB
  have hOne : 1 ≤ T ^ δ := Real.one_le_rpow hT hδ.le
  have hFloor : (⌊2 * X⌋₊ : ℝ) ≤ 2 * T ^ B :=
    (Nat.floor_le (by positivity)).trans (by gcongr)
  have hLog : Real.log ⌊2 * X⌋₊ ≤
      ((2 : ℝ) ^ (δ / B) * T ^ δ) / (δ / B) := by
    calc
      _ ≤ (⌊2 * X⌋₊ : ℝ) ^ (δ / B) / (δ / B) :=
        Real.log_natCast_le_rpow_div _ hq
      _ ≤ (2 * T ^ B) ^ (δ / B) / (δ / B) := by gcongr
      _ = _ := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity),
          ← Real.rpow_mul hTp.le]
        congr 3
        field_simp
  calc
    _ ≤ T ^ δ + ((2 : ℝ) ^ (δ / B) * T ^ δ) / (δ / B) := add_le_add hOne hLog
    _ = _ := by ring

/-- The exact energy-sensitive second moment at every fixed polynomial
height. All constants precede the data; no amplitude or cardinality cutoff. -/
theorem polynomial_height_dirichlet_second_energy
    (B δ : ℝ) (hB : 0 < B) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ X : ℝ, 2 ≤ T → 0 < X → X ≤ T ^ B →
      ∀ A : Finset ℕ, (∀ n ∈ A, 0 < n ∧ X < n ∧ (n : ℝ) ≤ 2 * X) →
      ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀ + T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t - u|) →
      ∀ a : ℕ → ℂ, (∀ n ∈ A, ‖a n‖ ≤ 1) →
      (∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ A, a n * phase n (t - u)‖ ^ 2) ≤
        C * T ^ δ * (X ^ 2 * (W.card : ℝ) +
          X * Real.sqrt (T * (discreteAdditiveEnergy W : ℝ))) := by
  obtain ⟨C₀, hC₀, hBase⟩ := basic_dirichlet_difference_energy
  let L : ℝ := 1 + (2 : ℝ) ^ (δ / B) / (δ / B)
  have hL : 0 < L := by dsimp only [L]; positivity
  refine ⟨C₀ * L, by positivity, ?_⟩
  intro T t₀ X hT hX hXT A hA W hW hSep a ha
  have hTp : 0 < T := by linarith
  have hLoss := polynomial_height_log_loss B δ hB hδ (by linarith) hX hXT
  change 1 + Real.log ⌊2 * X⌋₊ ≤ L * T ^ δ at hLoss
  have hLone : 1 ≤ L := by
    have h : 0 ≤ (2 : ℝ) ^ (δ / B) / (δ / B) := by positivity
    dsimp only [L]
    linarith
  have hLossOne : 1 ≤ L * T ^ δ := by
    exact one_le_mul_of_one_le_of_one_le hLone
      (Real.one_le_rpow (by linarith) hδ.le)
  have hFirst : X ^ 2 * (W.card : ℝ) ≤
      (L * T ^ δ) * (X ^ 2 * (W.card : ℝ)) :=
    le_mul_of_one_le_left (by positivity) hLossOne
  have hSecond := mul_le_mul_of_nonneg_left hLoss
    (show 0 ≤ X * Real.sqrt (T * (discreteAdditiveEnergy W : ℝ)) by positivity)
  have h := hBase T t₀ X (by linarith) hX A hA W hW hSep a ha
  calc
    _ ≤ C₀ * (X ^ 2 * (W.card : ℝ) +
        X * Real.sqrt (T * (discreteAdditiveEnergy W : ℝ)) *
          (1 + Real.log ⌊2 * X⌋₊)) := h
    _ ≤ C₀ * ((L * T ^ δ) * (X ^ 2 * (W.card : ℝ)) +
        X * Real.sqrt (T * (discreteAdditiveEnergy W : ℝ)) * (L * T ^ δ)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hFirst hSecond) hC₀.le
    _ = _ := by ring

end Montgomery.RationalMoment
