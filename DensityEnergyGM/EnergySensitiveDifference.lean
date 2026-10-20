module
public import DensityEnergyGM.PoweredDifferenceEnergy
public import DensityEnergyGM.EnergyPowerMean

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Finset
namespace Montgomery.RationalMoment

/-- The full energy-sensitive difference estimate (Eq.4), with arbitrary
real length of fixed polynomial height, arbitrary translated interval, and
the unchanged complete ordered tolerance-one energy. -/
theorem energy_sensitive_dirichlet_difference
    (k : ℕ) (B ε : ℝ) (hk : 0 < k) (hB : 0 < B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ X : ℝ, 2 ≤ T → 0 < X → X ≤ T ^ B →
      ∀ A : Finset ℕ, (∀ n ∈ A, 0 < n ∧ X < n ∧ (n : ℝ) ≤ 2 * X) →
      ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀ + T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t - u|) →
      ∀ a : ℕ → ℂ, (∀ n ∈ A, ‖a n‖ ≤ 1) →
      (∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ A, a n * phase n (t - u)‖ ^ 2) ≤
        C * T ^ ε *
          (X ^ 2 * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
            X * (T * (discreteAdditiveEnergy W : ℝ)) ^ (1 / (2 * (k : ℝ))) *
              (W.card : ℝ) ^ (2 - 2 / (k : ℝ))) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  let δ : ℝ := (k : ℝ) * ε / 2
  let ν : ℝ := ε / (4 * B)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hν : 0 < ν := by dsimp only [ν]; positivity
  obtain ⟨C₀, hC₀, hPower⟩ := powered_dirichlet_difference_energy k B δ ν hk hB hδ hν
  let D : ℝ := C₀ ^ (1 / (k : ℝ)) * (2 : ℝ) ^ (2 * ν)
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨4 * D, by positivity, ?_⟩
  intro T t₀ X hT hX hXT A hA W hW hSep a ha
  have hTp : 0 < T := by linarith
  by_cases hEmpty : W = ∅
  · subst W
    simp only [sum_empty]
    positivity
  have hR : (0 : ℝ) < W.card := by exact_mod_cast card_pos.mpr (nonempty_iff_ne_empty.mpr hEmpty)
  let R : ℝ := W.card
  let Z : ℝ := T * (discreteAdditiveEnergy W : ℝ)
  let H : ℝ := (2 * X) ^ k
  let Q : ℝ := H ^ 2 * R + H * Real.sqrt Z
  let S : ℝ := X ^ 2 * R ^ (2 - 1 / (k : ℝ)) +
    X * Z ^ (1 / (2 * (k : ℝ))) * R ^ (2 - 2 / (k : ℝ))
  have hH : 0 < H := by dsimp only [H]; positivity
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q, R]; positivity
  have hS : 0 ≤ S := by dsimp only [S, R]; positivity
  have hMean := ordered_difference_power_mean A a W hk
  have hPowered := hPower T t₀ X hT hX hXT A hA W hW hSep a ha
  change (∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ A, a n * phase n (t - u)‖ ^ (2 * k)) ≤
    C₀ * T ^ δ * H ^ (2 * ν) * Q at hPowered
  have hRoot := Real.rpow_le_rpow
    (sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) _)))
    hPowered (by positivity : 0 ≤ 1 / (k : ℝ))
  have hHRoot : (H ^ (2 * ν)) ^ (1 / (k : ℝ)) = (2 * X) ^ (2 * ν) := by
    rw [← Real.rpow_mul hH.le]
    dsimp only [H]
    rw [← Real.rpow_natCast_mul (by positivity : 0 ≤ 2 * X)]
    congr 1
    field_simp
  have hRootId : (C₀ * T ^ δ * H ^ (2 * ν) * Q) ^ (1 / (k : ℝ)) =
      C₀ ^ (1 / (k : ℝ)) * T ^ (δ / (k : ℝ)) * (2 * X) ^ (2 * ν) *
        Q ^ (1 / (k : ℝ)) := by
    rw [Real.mul_rpow (by positivity : 0 ≤ C₀ * T ^ δ * H ^ (2 * ν)) hQ,
      Real.mul_rpow (by positivity : 0 ≤ C₀ * T ^ δ) (by positivity),
      Real.mul_rpow hC₀.le (by positivity), ← Real.rpow_mul hTp.le, hHRoot]
    congr 3
    ring_nf
  have hShape : R ^ (2 - 2 / (k : ℝ)) * Q ^ (1 / (k : ℝ)) ≤ 4 * S :=
    powered_energy_root_shape hX hR hZ hk
  have hLoss : T ^ (δ / (k : ℝ)) * (2 * X) ^ (2 * ν) ≤
      (2 : ℝ) ^ (2 * ν) * T ^ ε := by
    have hXPower := Real.rpow_le_rpow hX.le hXT (by positivity : 0 ≤ 2 * ν)
    have hBudget : δ / (k : ℝ) + B * (2 * ν) = ε := by
      dsimp only [δ, ν]
      field_simp
      ring_nf
    calc
      _ = (2 : ℝ) ^ (2 * ν) * (T ^ (δ / (k : ℝ)) * X ^ (2 * ν)) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hX.le]
        ring_nf
      _ ≤ (2 : ℝ) ^ (2 * ν) * (T ^ (δ / (k : ℝ)) * (T ^ B) ^ (2 * ν)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hXPower (by positivity)) (by positivity)
      _ = _ := by rw [← Real.rpow_mul hTp.le, ← Real.rpow_add hTp, hBudget]
  have hCommon : C₀ ^ (1 / (k : ℝ)) * T ^ (δ / (k : ℝ)) * (2 * X) ^ (2 * ν) ≤
      D * T ^ ε := by
    have h := mul_le_mul_of_nonneg_left hLoss (by positivity : 0 ≤ C₀ ^ (1 / (k : ℝ)))
    exact (by simpa only [D, mul_assoc] using h)
  change _ ≤ (4 * D) * T ^ ε * S
  calc
    _ ≤ R ^ (2 - 2 / (k : ℝ)) *
        (C₀ * T ^ δ * H ^ (2 * ν) * Q) ^ (1 / (k : ℝ)) :=
      hMean.trans (mul_le_mul_of_nonneg_left hRoot (by positivity))
    _ = (C₀ ^ (1 / (k : ℝ)) * T ^ (δ / (k : ℝ)) * (2 * X) ^ (2 * ν)) *
        (R ^ (2 - 2 / (k : ℝ)) * Q ^ (1 / (k : ℝ))) := by rw [hRootId]; ring
    _ ≤ (D * T ^ ε) * (4 * S) := mul_le_mul hCommon hShape (by positivity) (by positivity)
    _ = _ := by ring_nf

/-- Include the zero-length case: positivity of the integer support forces
it to be empty. This is the closed nonnegative-length version of Eq.4. -/
theorem energy_sensitive_dirichlet_difference_nonneg
    (k : ℕ) (B ε : ℝ) (hk : 0 < k) (hB : 0 < B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ X : ℝ, 2 ≤ T → 0 ≤ X → X ≤ T ^ B →
      ∀ A : Finset ℕ, (∀ n ∈ A, 0 < n ∧ X < n ∧ (n : ℝ) ≤ 2 * X) →
      ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀ + T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t - u|) →
      ∀ a : ℕ → ℂ, (∀ n ∈ A, ‖a n‖ ≤ 1) →
      (∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ A, a n * phase n (t - u)‖ ^ 2) ≤
        C * T ^ ε *
          (X ^ 2 * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
            X * (T * (discreteAdditiveEnergy W : ℝ)) ^ (1 / (2 * (k : ℝ))) *
              (W.card : ℝ) ^ (2 - 2 / (k : ℝ))) := by
  obtain ⟨C, hC, hBound⟩ := energy_sensitive_dirichlet_difference k B ε hk hB hε
  refine ⟨C, hC, ?_⟩
  intro T t₀ X hT hX hXT A hA W hW hSep a ha
  rcases lt_or_eq_of_le hX with hXp | hZero
  · exact hBound T t₀ X hT hXp hXT A hA W hW hSep a ha
  · have hEmpty : A = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro n hn
      have hp : (0 : ℝ) < n := by exact_mod_cast (hA n hn).1
      have hu := (hA n hn).2.2
      rw [← hZero] at hu
      linarith
    rw [hEmpty]
    simp only [sum_empty, norm_zero, zero_pow (by norm_num : 2 ≠ 0), sum_const_zero]
    positivity

end Montgomery.RationalMoment
