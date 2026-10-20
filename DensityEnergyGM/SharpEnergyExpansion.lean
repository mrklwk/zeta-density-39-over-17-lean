module
public import DensityEnergyGM.SharpEnergyReduction

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Finset GuthMaynard.NativeMoment GuthMaynard.Improvement
namespace Montgomery.RationalMoment

def expandedSharpCubicProfile (T : ℝ) (W : Finset ℝ) : ℝ :=
  let R : ℝ := W.card
  let E : ℝ := discreteAdditiveEnergy W
  T ^ (1 / 2 : ℝ) * E ^ (3 / 4 : ℝ) +
    T ^ (9 / 20 : ℝ) * R ^ (3 / 5 : ℝ) * E ^ (3 / 5 : ℝ) +
    T ^ (9 / 40 : ℝ) * R ^ (21 / 10 : ℝ) * E ^ (9 / 40 : ℝ) +
    2 * T ^ (17 / 40 : ℝ) * R ^ (9 / 10 : ℝ) * E ^ (21 / 40 : ℝ)

theorem sharp_cubic_profile_expansion {T R E : ℝ}
    (hT : 1 ≤ T) (hR : 0 < R) (hE : 0 < E) :
    let K := R ^ 4 + T ^ (1 / 2 : ℝ) * R * E ^ (3 / 4 : ℝ)
    E ^ (1 / 4 : ℝ) * (T * E) ^ (1 / 2 : ℝ) +
      R ^ (1 / 2 : ℝ) * E ^ (1 / 8 : ℝ) * (T * E) ^ (2 / 5 : ℝ) * K ^ (1 / 10 : ℝ) +
      R ^ (1 / 2 : ℝ) * E ^ (1 / 8 : ℝ) * T ^ (1 / 8 : ℝ) *
        (T * E) ^ (1 / 10 : ℝ) * K ^ (2 / 5 : ℝ) ≤
    T ^ (1 / 2 : ℝ) * E ^ (3 / 4 : ℝ) +
      T ^ (9 / 20 : ℝ) * R ^ (3 / 5 : ℝ) * E ^ (3 / 5 : ℝ) +
      T ^ (9 / 40 : ℝ) * R ^ (21 / 10 : ℝ) * E ^ (9 / 40 : ℝ) +
      2 * T ^ (17 / 40 : ℝ) * R ^ (9 / 10 : ℝ) * E ^ (21 / 40 : ℝ) := by
  let K := R ^ 4 + T ^ (1 / 2 : ℝ) * R * E ^ (3 / 4 : ℝ)
  let B := R ^ (1 / 2 : ℝ) * E ^ (1 / 8 : ℝ) * (T * E) ^ (2 / 5 : ℝ)
  let C := R ^ (1 / 2 : ℝ) * E ^ (1 / 8 : ℝ) * T ^ (1 / 8 : ℝ) * (T * E) ^ (1 / 10 : ℝ)
  have hTpos : 0 < T := by linarith
  have hR4a : (R ^ 4) ^ (1 / 10 : ℝ) = R ^ (2 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    norm_num
  have hR4b : (R ^ 4) ^ (2 / 5 : ℝ) = R ^ (8 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    norm_num
  have hOtherA : (T ^ (1 / 2 : ℝ) * R * E ^ (3 / 4 : ℝ)) ^ (1 / 10 : ℝ) =
      T ^ (1 / 20 : ℝ) * R ^ (1 / 10 : ℝ) * E ^ (3 / 40 : ℝ) := by
    rw [Real.mul_rpow (by positivity) (by positivity : 0 ≤ E ^ (3 / 4 : ℝ)),
      Real.mul_rpow (by positivity) hR.le, ← Real.rpow_mul hTpos.le,
      ← Real.rpow_mul hE.le]
    norm_num
  have hOtherB : (T ^ (1 / 2 : ℝ) * R * E ^ (3 / 4 : ℝ)) ^ (2 / 5 : ℝ) =
      T ^ (1 / 5 : ℝ) * R ^ (2 / 5 : ℝ) * E ^ (3 / 10 : ℝ) := by
    rw [Real.mul_rpow (by positivity) (by positivity : 0 ≤ E ^ (3 / 4 : ℝ)),
      Real.mul_rpow (by positivity) hR.le, ← Real.rpow_mul hTpos.le,
      ← Real.rpow_mul hE.le]
    norm_num
  have hKa : K ^ (1 / 10 : ℝ) ≤ R ^ (2 / 5 : ℝ) +
      T ^ (1 / 20 : ℝ) * R ^ (1 / 10 : ℝ) * E ^ (3 / 40 : ℝ) := by
    have h := Real.rpow_add_le_add_rpow (by positivity : 0 ≤ R ^ 4)
      (by positivity : 0 ≤ T ^ (1 / 2 : ℝ) * R * E ^ (3 / 4 : ℝ))
      (by norm_num : (0 : ℝ) ≤ 1 / 10) (by norm_num : (1 / 10 : ℝ) ≤ 1)
    rw [hR4a, hOtherA] at h
    exact h
  have hKb : K ^ (2 / 5 : ℝ) ≤ R ^ (8 / 5 : ℝ) +
      T ^ (1 / 5 : ℝ) * R ^ (2 / 5 : ℝ) * E ^ (3 / 10 : ℝ) := by
    have h := Real.rpow_add_le_add_rpow (by positivity : 0 ≤ R ^ 4)
      (by positivity : 0 ≤ T ^ (1 / 2 : ℝ) * R * E ^ (3 / 4 : ℝ))
      (by norm_num : (0 : ℝ) ≤ 2 / 5) (by norm_num : (2 / 5 : ℝ) ≤ 1)
    rw [hR4b, hOtherB] at h
    exact h
  have hE34 : E ^ (3 / 4 : ℝ) = E ^ (1 / 4 : ℝ) * E ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hE]; congr 1; norm_num
  have hR9 : R ^ (9 / 10 : ℝ) = R ^ (1 / 2 : ℝ) * R ^ (2 / 5 : ℝ) := by
    rw [← Real.rpow_add hR]; congr 1; norm_num
  have hE21a : E ^ (21 / 40 : ℝ) = E ^ (1 / 8 : ℝ) * E ^ (2 / 5 : ℝ) := by
    rw [← Real.rpow_add hE]; congr 1; norm_num
  have hT9 : T ^ (9 / 20 : ℝ) = T ^ (2 / 5 : ℝ) * T ^ (1 / 20 : ℝ) := by
    rw [← Real.rpow_add hTpos]; congr 1; norm_num
  have hR3 : R ^ (3 / 5 : ℝ) = R ^ (1 / 2 : ℝ) * R ^ (1 / 10 : ℝ) := by
    rw [← Real.rpow_add hR]; congr 1; norm_num
  have hE3 : E ^ (3 / 5 : ℝ) = E ^ (1 / 8 : ℝ) * E ^ (2 / 5 : ℝ) * E ^ (3 / 40 : ℝ) := by
    rw [← Real.rpow_add hE, ← Real.rpow_add hE]; congr 1; norm_num
  have hT9q : T ^ (9 / 40 : ℝ) = T ^ (1 / 8 : ℝ) * T ^ (1 / 10 : ℝ) := by
    rw [← Real.rpow_add hTpos]; congr 1; norm_num
  have hR21 : R ^ (21 / 10 : ℝ) = R ^ (1 / 2 : ℝ) * R ^ (8 / 5 : ℝ) := by
    rw [← Real.rpow_add hR]; congr 1; norm_num
  have hE9q : E ^ (9 / 40 : ℝ) = E ^ (1 / 8 : ℝ) * E ^ (1 / 10 : ℝ) := by
    rw [← Real.rpow_add hE]; congr 1; norm_num
  have hT17 : T ^ (17 / 40 : ℝ) = T ^ (1 / 8 : ℝ) * T ^ (1 / 10 : ℝ) * T ^ (1 / 5 : ℝ) := by
    rw [← Real.rpow_add hTpos, ← Real.rpow_add hTpos]; congr 1; norm_num
  have hE21b : E ^ (21 / 40 : ℝ) = E ^ (1 / 8 : ℝ) * E ^ (1 / 10 : ℝ) * E ^ (3 / 10 : ℝ) := by
    rw [← Real.rpow_add hE, ← Real.rpow_add hE]; congr 1; norm_num
  have hA : E ^ (1 / 4 : ℝ) * (T * E) ^ (1 / 2 : ℝ) = T ^ (1 / 2 : ℝ) * E ^ (3 / 4 : ℝ) := by
    rw [Real.mul_rpow hTpos.le hE.le, hE34]; ring
  have hB1 : B * R ^ (2 / 5 : ℝ) = T ^ (2 / 5 : ℝ) * R ^ (9 / 10 : ℝ) * E ^ (21 / 40 : ℝ) := by
    dsimp only [B]
    rw [Real.mul_rpow hTpos.le hE.le, hR9, hE21a]; ring
  have hB2 : B * (T ^ (1 / 20 : ℝ) * R ^ (1 / 10 : ℝ) * E ^ (3 / 40 : ℝ)) =
      T ^ (9 / 20 : ℝ) * R ^ (3 / 5 : ℝ) * E ^ (3 / 5 : ℝ) := by
    dsimp only [B]
    rw [Real.mul_rpow hTpos.le hE.le, hT9, hR3, hE3]; ring
  have hC1 : C * R ^ (8 / 5 : ℝ) = T ^ (9 / 40 : ℝ) * R ^ (21 / 10 : ℝ) * E ^ (9 / 40 : ℝ) := by
    dsimp only [C]
    rw [Real.mul_rpow hTpos.le hE.le, hT9q, hR21, hE9q]; ring
  have hC2 : C * (T ^ (1 / 5 : ℝ) * R ^ (2 / 5 : ℝ) * E ^ (3 / 10 : ℝ)) =
      T ^ (17 / 40 : ℝ) * R ^ (9 / 10 : ℝ) * E ^ (21 / 40 : ℝ) := by
    dsimp only [C]
    rw [Real.mul_rpow hTpos.le hE.le, hT17, hR9, hE21b]; ring
  have hBbound := mul_le_mul_of_nonneg_left hKa (show 0 ≤ B by dsimp only [B]; positivity)
  have hCbound := mul_le_mul_of_nonneg_left hKb (show 0 ≤ C by dsimp only [C]; positivity)
  rw [mul_add, hB1, hB2] at hBbound
  rw [mul_add, hC1, hC2] at hCbound
  have hCompare : T ^ (2 / 5 : ℝ) * R ^ (9 / 10 : ℝ) * E ^ (21 / 40 : ℝ) ≤
      T ^ (17 / 40 : ℝ) * R ^ (9 / 10 : ℝ) * E ^ (21 / 40 : ℝ) := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hT (by norm_num : (2 / 5 : ℝ) ≤ 17 / 40))
      (by positivity)) (by positivity)
  change E ^ (1 / 4 : ℝ) * (T * E) ^ (1 / 2 : ℝ) + B * K ^ (1 / 10 : ℝ) + C * K ^ (2 / 5 : ℝ) ≤ _
  rw [hA]
  linarith

theorem sharpCubicProfile_le_expanded {T : ℝ} (hT : 1 ≤ T) (W : Finset ℝ) :
    sharpCubicProfile T W ≤ expandedSharpCubicProfile T W := by
  by_cases hW : W.Nonempty
  · have hR : (0 : ℝ) < W.card := by exact_mod_cast Finset.card_pos.mpr hW
    have hE : (0 : ℝ) < discreteAdditiveEnergy W := by
      have h := card_sq_le_approxAddEnergy (by norm_num : (0 : ℝ) ≤ 1) W
      rw [native_approx_energy_eq] at h
      have hd : (W.card : ℝ) ^ 2 ≤ (discreteAdditiveEnergy W : ℝ) := by exact_mod_cast h
      nlinarith
    exact sharp_cubic_profile_expansion hT hR hE
  · have he : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
    subst W
    norm_num [sharpCubicProfile, expandedSharpCubicProfile, discreteAdditiveEnergy]

/-- The actual energy inequality with five explicit sublinear powers.
This is the input to solving for E, not an assumed energy estimate. -/
theorem discrete_energy_sublinear_native (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T N : ℝ) (a : ℕ → ℂ) (W : Finset ℝ) (V : ℝ),
        T₀ ≤ T → 0 < N → T ≤ N ^ 2 → N ≤ T →
        (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
        0 < V → (∀ t ∈ W, V ≤ ‖boundedPolynomial N a t‖) →
        IsSeparated 1 W → InBaseInterval T W →
        let E : ℝ := discreteAdditiveEnergy W
        let R : ℝ := W.card
        E * V ^ 2 ≤ C * T ^ ε *
          (N ^ 2 * R ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) +
            N * T ^ (1 / 2 : ℝ) * E ^ (3 / 4 : ℝ) +
            N * T ^ (9 / 20 : ℝ) * R ^ (3 / 5 : ℝ) * E ^ (3 / 5 : ℝ) +
            N * T ^ (9 / 40 : ℝ) * R ^ (21 / 10 : ℝ) * E ^ (9 / 40 : ℝ) +
            2 * N * T ^ (17 / 40 : ℝ) * R ^ (9 / 10 : ℝ) * E ^ (21 / 40 : ℝ)) := by
  obtain ⟨C, T₀, hC, hT₀, h⟩ := discrete_energy_sharp_profile_native ε hε
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T N a W V hT hN hTN hNT ha hV hValues hSep hBase
  have hTtwo : 2 ≤ T := hT₀.trans hT
  have hProfile := sharpCubicProfile_le_expanded (by linarith : 1 ≤ T) W
  have hActual := h T N a W V hT hN hTN hNT ha hV hValues hSep hBase
  apply hActual.trans
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc
    _ ≤ N ^ 2 * Real.sqrt (W.card : ℝ) * Real.sqrt (discreteAdditiveEnergy W : ℝ) +
        N * expandedSharpCubicProfile T W := by gcongr
    _ = _ := by
      simp only [expandedSharpCubicProfile, Real.sqrt_eq_rpow]
      ring

end Montgomery.RationalMoment
