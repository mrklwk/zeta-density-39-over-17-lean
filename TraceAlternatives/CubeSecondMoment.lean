module
public import TraceAlternatives.DifferenceCubeSampling
public import TraceAlternatives.WeightedCube

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

/-- Exact cube-root shape behind mixed trace16. -/
theorem cube_second_moment_shape {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T) :
    (M ^ 6 + T * M ^ 3) ^ (1 / 3 : ℝ) ≤ M ^ 2 + T ^ (1 / 3 : ℝ) * M := by
  have h6 : (M ^ 6) ^ (1 / 3 : ℝ) = M ^ 2 := by
    rw [← Real.rpow_natCast_mul hM]
    norm_num [Real.rpow_ofNat]
  have h3 : (M ^ 3) ^ (1 / 3 : ℝ) = M := by
    rw [← Real.rpow_natCast_mul hM]
    norm_num
  have hh := Real.rpow_add_le_add_rpow (pow_nonneg hM 6)
    (mul_nonneg hT (pow_nonneg hM 3))
    (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 / 3 : ℝ) ≤ 1)
  simpa only [h6, Real.mul_rpow hT (pow_nonneg hM 3), h3] using hh

/-- The missing actual short S2 source for mixed trace16. The only inputs
are literal finite support, unit coefficients, the short-scale range and
membership in the height interval. No separation of W is required. -/
theorem actual_second_moment_cube_native (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ℕ) (T : ℝ) (a : ℕ → ℂ) (W : Finset ℝ),
        0 < M → 2 ≤ T → (M : ℝ) ^ 2 ≤ T →
        (∀ n ∈ Ioc M (2 * M), ‖a n‖ ≤ 1) → InBaseInterval T W →
        (∑ t ∈ W, ∑ u ∈ W, ‖dirichletPoly M a (t - u)‖ ^ 2) ≤
          C * T ^ ε * ((M : ℝ) ^ 2 + T ^ (1 / 3 : ℝ) * M) *
            (W.card : ℝ) ^ (2 / 3 : ℝ) *
              (discreteAdditiveEnergy W : ℝ) ^ (1 / 3 : ℝ) := by
  classical
  obtain ⟨C₀, hC₀, hMoment⟩ := difference_peak_sixth_moment_native (3 * ε) (by positivity)
  refine ⟨C₀ ^ (1 / 3 : ℝ), by positivity, ?_⟩
  intro M T a W hM hT hMT ha hBase
  have hTp : 0 < T := by linarith
  obtain ⟨p, hrep⟩ := exists_difference_peak_representatives W (fun t => ‖dirichletPoly M a t‖)
  let S := differenceFloorSupport W
  let r : ℤ → ℝ := fun j => differenceFloorCount W j
  let v : ℤ → ℝ := fun j => ‖dirichletPoly M a ((p j).1 - (p j).2)‖
  have hr : ∀ j ∈ S, 0 ≤ r j := fun _ _ => Nat.cast_nonneg _
  have hv : ∀ j ∈ S, 0 ≤ v j := fun _ _ => norm_nonneg _
  have hWeights : (∑ j ∈ S, r j) = (W.card : ℝ) ^ 2 := by
    dsimp only [S, r]
    exact_mod_cast sum_differenceFloorCount W
  have hEnergy : (∑ j ∈ S, r j ^ 2) ≤ (discreteAdditiveEnergy W : ℝ) := by
    dsimp only [S, r]
    exact_mod_cast differenceFloor_energy_le W
  have hSix : (∑ j ∈ S, v j ^ 6) ≤
      C₀ * T ^ (3 * ε) * ((M : ℝ) ^ 6 + T * (M : ℝ) ^ 3) :=
    hMoment M T a W hM hT hMT ha hBase p (fun j hj => ⟨(hrep j hj).1, (hrep j hj).2.1⟩)
  have hRoot : (∑ j ∈ S, v j ^ 6) ^ (1 / 3 : ℝ) ≤
      C₀ ^ (1 / 3 : ℝ) * T ^ ε * ((M : ℝ) ^ 2 + T ^ (1 / 3 : ℝ) * M) := by
    have hh := Real.rpow_le_rpow (sum_nonneg (fun j hj => pow_nonneg (hv j hj) 6))
      hSix (by norm_num : (0 : ℝ) ≤ 1 / 3)
    have hId : (C₀ * T ^ (3 * ε) * ((M : ℝ) ^ 6 + T * (M : ℝ) ^ 3)) ^ (1 / 3 : ℝ) =
        C₀ ^ (1 / 3 : ℝ) * T ^ ε *
          ((M : ℝ) ^ 6 + T * (M : ℝ) ^ 3) ^ (1 / 3 : ℝ) := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow hC₀.le (by positivity), ← Real.rpow_mul hTp.le]
      rw [show (3 * ε) * (1 / 3 : ℝ) = ε by ring]
    rw [hId] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (cube_second_moment_shape (Nat.cast_nonneg M) hTp.le) (by positivity))
  have hHolder := weighted_cube_holder S r v hr hv
  rw [hWeights, ← Real.rpow_natCast_mul (Nat.cast_nonneg W.card)] at hHolder
  norm_num only [show (2 : ℝ) * (1 / 3) = 2 / 3 by norm_num] at hHolder
  have hBound : (∑ j ∈ S, r j * v j ^ 2) ≤
      (W.card : ℝ) ^ (2 / 3 : ℝ) *
        (discreteAdditiveEnergy W : ℝ) ^ (1 / 3 : ℝ) *
          (C₀ ^ (1 / 3 : ℝ) * T ^ ε * ((M : ℝ) ^ 2 + T ^ (1 / 3 : ℝ) * M)) := by
    apply hHolder.trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (sum_nonneg (fun j hj => sq_nonneg (r j))) hEnergy (by norm_num))
        (by positivity)
    · exact hRoot
    · positivity
    · positivity
  have hOriginal : (∑ t ∈ W, ∑ u ∈ W, ‖dirichletPoly M a (t - u)‖ ^ 2) ≤
      ∑ j ∈ S, r j * v j ^ 2 := by
    calc
      _ = ∑ q ∈ differenceOrdinatePairs W, ‖dirichletPoly M a (q.1 - q.2)‖ ^ 2 := by
        rw [differenceOrdinatePairs, sum_product]
      _ ≤ ∑ q ∈ differenceOrdinatePairs W, v (differenceFloor q) ^ 2 := by
        apply sum_le_sum
        intro q hq
        have hj : differenceFloor q ∈ differenceFloorSupport W := mem_image.mpr ⟨q, hq, rfl⟩
        exact pow_le_pow_left₀ (norm_nonneg _) ((hrep _ hj).2.2 q hq rfl) 2
      _ = _ := sum_differenceFloor_values W (fun j => v j ^ 2)
  exact hOriginal.trans (hBound.trans_eq (by ring))

end Montgomery.RationalMoment
