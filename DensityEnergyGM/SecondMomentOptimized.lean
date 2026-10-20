module
public import DensityEnergyGM.SecondMomentIntegral
public import DensityEnergyGM.ClippedRadicalIntegral
public import DensityEnergyGM.CoprimeFourthNative

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset MeasureTheory GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

/-- The actual ordered second-difference moment, with the optimized fourth
root and the explicit logarithmic cost. No analytic estimate is a premise. -/
theorem actual_second_moment_optimized_log (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 1 ≤ C ∧ 2 ≤ T₀ ∧
      ∀ (M : ℕ) (T : ℝ) (a : ℕ → ℂ) (W : Finset ℝ),
        0 < M → T₀ ≤ T → (M : ℝ) ^ 2 ≤ T →
        (∀ n ∈ Ioc M (2 * M), ‖a n‖ ≤ 1) →
        IsSeparated 1 W → InBaseInterval T W → W.Nonempty →
        let E : ℝ := discreteAdditiveEnergy W
        let K : ℝ := E * C * (2 * T) ^ ε
        let B : ℝ := (M : ℝ) ^ (36 / 5 : ℝ) +
          (2 * T) * (M : ℝ) ^ (24 / 5 : ℝ)
        (∑ t ∈ W, ∑ u ∈ W, ‖dirichletPoly M a (t - u)‖ ^ 2) ≤
          2 * (W.card : ℝ) * Real.sqrt (Real.sqrt K * Real.sqrt B) +
            3 * Real.sqrt K * (M : ℝ) ^ 2 * Real.log T := by
  obtain ⟨C₀, T₁, hC₀, hT₁, hActual⟩ := actual_second_moment_integral_native ε hε
  let C := max 1 C₀
  refine ⟨C, max 2 T₁, le_max_left _ _, le_max_left _ _, ?_⟩
  intro M T a W hM hT hMT ha hSep hBase hW
  let R : ℝ := W.card
  let E : ℝ := discreteAdditiveEnergy W
  let B : ℝ := (M : ℝ) ^ (36 / 5 : ℝ) + (2 * T) * (M : ℝ) ^ (24 / 5 : ℝ)
  let K : ℝ := E * C * (2 * T) ^ ε
  have hTtwo : 2 ≤ T := (le_max_left _ _).trans hT
  have hTone : 1 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hR : 0 < R := by dsimp only [R]; exact_mod_cast Finset.card_pos.mpr hW
  have hRone : 1 ≤ R := by dsimp only [R]; exact_mod_cast Finset.card_pos.mpr hW
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hEdiag : R ^ 2 ≤ E := by
    have h := card_sq_le_approxAddEnergy (by norm_num : (0 : ℝ) ≤ 1) W
    rw [native_approx_energy_eq] at h
    dsimp only [R, E]
    exact_mod_cast h
  have hEone : 1 ≤ E := by nlinarith
  have hB : 1 ≤ B := by
    have h := Real.one_le_rpow hMone (by norm_num : (0 : ℝ) ≤ 36 / 5)
    have hOther : 0 ≤ (2 * T) * (M : ℝ) ^ (24 / 5 : ℝ) := by positivity
    dsimp only [B]
    linarith
  have hK : 1 ≤ K := by
    have hPow : 1 ≤ (2 * T) ^ ε := Real.one_le_rpow (by linarith) hε.le
    have hC : 1 ≤ C := le_max_left _ _
    dsimp only [K]
    have hEC : 1 ≤ E * C := by nlinarith
    nlinarith
  have hFirst : (∑ t ∈ W, ∑ u ∈ W, ‖dirichletPoly M a (t - u)‖ ^ 2) ≤
      ∫ s in Set.Ioc 0 ((M : ℝ) ^ 2),
        clippedRadicalTail R (E * C₀ * (2 * T) ^ ε) ((M : ℝ) ^ 2) B s := by
    convert hActual M T a W hM ((le_max_right _ _).trans hT) hMT ha hBase using 1
    congr 1
    ext s
    dsimp only [clippedRadicalTail, R, E, B]
    congr 1
    congr 1
    ring
  have hEnlarge :
      (∫ s in Set.Ioc 0 ((M : ℝ) ^ 2),
        clippedRadicalTail R (E * C₀ * (2 * T) ^ ε) ((M : ℝ) ^ 2) B s) ≤
      ∫ s in Set.Ioc 0 ((M : ℝ) ^ 2),
        clippedRadicalTail R K ((M : ℝ) ^ 2) B s := by
    apply integral_mono (clippedRadicalTail_integrable _ _ _ _ _)
      (clippedRadicalTail_integrable _ _ _ _ _)
    intro s
    apply clippedRadicalTail_mono ?_ (by linarith)
    dsimp only [K]
    gcongr
    exact le_max_right _ _
  have hCap := clipped_radical_integral_log_bound hR hK (sq_nonneg (M : ℝ)) hB
    (sq_pos_of_pos hMpos) hMT (gmSeparated_card_le_two_height hTone hSep hBase) hTtwo
  exact hFirst.trans (hEnlarge.trans hCap)

end Montgomery.RationalMoment
