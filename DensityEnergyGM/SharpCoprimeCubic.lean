module
public import DensityEnergyGM.RealScaleFourthMoment
public import DensityEnergyGM.GcdSharpShape

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Finset GuthMaynard.NativeMoment GuthMaynard.Improvement
namespace Montgomery.RationalMoment

def sharpCubicProfile (T : ℝ) (W : Finset ℝ) : ℝ :=
  let R : ℝ := W.card
  let E : ℝ := discreteAdditiveEnergy W
  let K : ℝ := R ^ 4 + T ^ (1 / 2 : ℝ) * R * E ^ (3 / 4 : ℝ)
  E ^ (1 / 4 : ℝ) * (T * E) ^ (1 / 2 : ℝ) +
    R ^ (1 / 2 : ℝ) * E ^ (1 / 8 : ℝ) * (T * E) ^ (2 / 5 : ℝ) * K ^ (1 / 10 : ℝ) +
    R ^ (1 / 2 : ℝ) * E ^ (1 / 8 : ℝ) * T ^ (1 / 8 : ℝ) *
      (T * E) ^ (1 / 10 : ℝ) * K ^ (2 / 5 : ℝ)

theorem sharpCubicProfile_nonneg {T : ℝ} (hT : 0 ≤ T) (W : Finset ℝ) :
    0 ≤ sharpCubicProfile T W := by
  dsimp only [sharpCubicProfile]
  positivity

theorem finite_cubic_le_sqrt_second_fourth {ι : Type*} (Q : Finset ι) (f : ι → ℝ) :
    (∑ q ∈ Q, f q ^ 3) ≤ Real.sqrt (∑ q ∈ Q, f q ^ 2) *
      Real.sqrt (∑ q ∈ Q, f q ^ 4) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Q f (fun q => f q ^ 2)
  have hFour : (∑ q ∈ Q, (f q ^ 2) ^ 2) = ∑ q ∈ Q, f q ^ 4 := by
    apply Finset.sum_congr rfl
    intro q hq
    ring
  rw [hFour] at h
  calc
    _ = ∑ q ∈ Q, f q * f q ^ 2 := by
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ _ := h

/-- Unconditional reduced cubic bound at every exact short real scale.
The scale dependence is exactly M, permitting a harmonic gcd sum. -/
theorem real_scale_coprime_cubic_sharp_native (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (M T : ℝ) (Q : Finset (ℕ × ℕ)) (W : Finset ℝ),
        0 < M → T₀ ≤ T → M ^ 2 ≤ T →
        (∀ q ∈ Q, 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2 ∧
          M < q.1 ∧ (q.1 : ℝ) ≤ 2 * M ∧ M < q.2 ∧ (q.2 : ℝ) ≤ 2 * M) →
        IsSeparated 1 W → InBaseInterval T W →
        (∑ q ∈ Q, ‖gmR W ((q.1 : ℝ) / q.2)‖ ^ 3) ≤
          C * T ^ ε * M * sharpCubicProfile T W := by
  obtain ⟨C₂, T₂, hC₂, hT₂, hSecond⟩ := real_scale_ratio_second_sharp_native ε hε
  obtain ⟨C₄, T₄, hC₄, hT₄, hFourth⟩ := real_scale_coprime_fourth_min_native ε hε
  let C : ℝ := Real.sqrt (C₂ * C₄)
  have hC : 0 < C := Real.sqrt_pos.mpr (mul_pos hC₂ hC₄)
  refine ⟨C, max T₂ T₄, hC, hT₂.trans (le_max_left _ _), ?_⟩
  intro M T Q W hM hT hMT hQ hSep hBase
  have hTtwo : 2 ≤ T := hT₂.trans ((le_max_left _ _).trans hT)
  have hTpos : 0 < T := by linarith
  by_cases hW : W.Nonempty
  swap
  · have he : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
    subst W
    simp only [gmR, Finset.sum_empty, norm_zero, zero_pow (by omega : 3 ≠ 0),
      Finset.sum_const_zero]
    exact mul_nonneg (by positivity) (sharpCubicProfile_nonneg hTpos.le ∅)
  let R : ℝ := W.card
  let E : ℝ := discreteAdditiveEnergy W
  let K : ℝ := R ^ 4 + T ^ (1 / 2 : ℝ) * R * E ^ (3 / 4 : ℝ)
  let H : ℝ := T * E
  let S : ℝ := M ^ 2 * E ^ (1 / 2 : ℝ) +
    R * E ^ (1 / 4 : ℝ) * (M ^ (9 / 5 : ℝ) + T ^ (1 / 4 : ℝ) * M ^ (6 / 5 : ℝ))
  let D : ℝ := min (M * K) H
  have hR : 0 < R := by dsimp only [R]; exact_mod_cast Finset.card_pos.mpr hW
  have hE : 0 < E := by
    have h := card_sq_le_approxAddEnergy (by norm_num : (0 : ℝ) ≤ 1) W
    rw [native_approx_energy_eq] at h
    have hRdiag : R ^ 2 ≤ E := by dsimp only [R, E]; exact_mod_cast h
    nlinarith
  have hK : 0 < K := by dsimp only [K]; positivity
  have hH : 0 < H := mul_pos hTpos hE
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  let f : ℕ × ℕ → ℝ := fun q => ‖gmR W ((q.1 : ℝ) / q.2)‖
  have hQsub : Q ⊆ (sourceRatioIndices M) ×ˢ (sourceRatioIndices M) := by
    intro q hq
    obtain ⟨h1, h2, hcop, hl1, hu1, hl2, hu2⟩ := hQ q hq
    exact Finset.mem_product.mpr
      ⟨(sourceRatioIndices_mem hM.le q.1).mpr ⟨hl1, hu1⟩,
        (sourceRatioIndices_mem hM.le q.2).mpr ⟨hl2, hu2⟩⟩
  have hSecondQ : (∑ q ∈ Q, f q ^ 2) ≤ C₂ * T ^ ε * S := by
    have hSub : (∑ q ∈ Q, f q ^ 2) ≤ finiteRatioSecond (sourceRatioIndices M) W := by
      simpa only [finiteRatioSecond, Finset.sum_product] using
        (Finset.sum_le_sum_of_subset_of_nonneg hQsub (fun q hq hnot => sq_nonneg (f q)))
    exact hSub.trans (hSecond M T W hM ((le_max_left _ _).trans hT) hMT hSep hBase)
  have hFourthQ : (∑ q ∈ Q, f q ^ 4) ≤ C₄ * T ^ ε * D :=
    hFourth M T Q W hM ((le_max_right _ _).trans hT) hMT hQ hSep hBase
  have hCS : (∑ q ∈ Q, f q ^ 3) ≤
      Real.sqrt ((C₂ * T ^ ε * S) * (C₄ * T ^ ε * D)) := by
    have h := finite_cubic_le_sqrt_second_fourth Q f
    rw [← Real.sqrt_mul (Finset.sum_nonneg fun q hq => sq_nonneg (f q))] at h
    exact h.trans (Real.sqrt_le_sqrt (mul_le_mul hSecondQ hFourthQ
      (Finset.sum_nonneg fun q hq => pow_nonneg (norm_nonneg _) 4) (by positivity)))
  have hFactor : Real.sqrt ((C₂ * T ^ ε * S) * (C₄ * T ^ ε * D)) =
      C * T ^ ε * Real.sqrt (S * D) := by
    have hShape : (C₂ * T ^ ε * S) * (C₄ * T ^ ε * D) =
        (C * T ^ ε) ^ 2 * (S * D) := by
      rw [mul_pow, show C ^ 2 = C₂ * C₄ from Real.sq_sqrt (by positivity)]
      ring
    rw [hShape, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hOptimized : Real.sqrt (S * D) ≤ M * sharpCubicProfile T W := by
    exact sharp_second_shape_sqrt_min hM hTpos.le hR.le hE.le hH hK
  change (∑ q ∈ Q, f q ^ 3) ≤ C * T ^ ε * M * sharpCubicProfile T W
  calc
    _ ≤ C * T ^ ε * Real.sqrt (S * D) := hCS.trans_eq hFactor
    _ ≤ C * T ^ ε * (M * sharpCubicProfile T W) :=
      mul_le_mul_of_nonneg_left hOptimized (by positivity)
    _ = _ := by ring

end Montgomery.RationalMoment
