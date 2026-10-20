module
public import DensityEnergyGM.SecondMomentSharp

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

theorem coefficient_one_difference_eq_ratio_second (M : ℕ) (W : Finset ℝ) :
    (∑ t ∈ W, ∑ u ∈ W, ‖dirichletPoly M (fun _ => (1 : ℂ)) (t - u)‖ ^ 2) =
      gmDiscreteRatioMoment 2 M W := by
  rw [gmDiscreteRatioMoment_eq_iterated,
    ← sourceCoefficientOne_differenceMoment_eq_gmR_ratioMoment]
  have hone : conjugateCoeffs (fun _ => (1 : ℂ)) = fun _ => (1 : ℂ) := by
    funext n
    exact star_one ℂ
  simp_rw [norm_sourceDirichletPoly_eq_dirichletPoly_conjugateCoeffs, hone]

/-- Literal all-pairs ratio second moment, obtained from the proved sharp
difference estimate by the exact finite Gram identity. -/
theorem ratio_second_moment_sharp_native (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (M : ℕ) (T : ℝ) (W : Finset ℝ),
        0 < M → T₀ ≤ T → (M : ℝ) ^ 2 ≤ T →
        IsSeparated 1 W → InBaseInterval T W →
        gmDiscreteRatioMoment 2 M W ≤ C * T ^ ε *
          ((M : ℝ) ^ 2 * (discreteAdditiveEnergy W : ℝ) ^ (1 / 2 : ℝ) +
            (W.card : ℝ) * (discreteAdditiveEnergy W : ℝ) ^ (1 / 4 : ℝ) *
              ((M : ℝ) ^ (9 / 5 : ℝ) +
                T ^ (1 / 4 : ℝ) * (M : ℝ) ^ (6 / 5 : ℝ))) := by
  obtain ⟨C, T₀, hC, hT₀, h⟩ := actual_second_moment_sharp_native ε hε
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro M T W hM hT hMT hSep hBase
  rw [← coefficient_one_difference_eq_ratio_second]
  exact h M T (fun _ => 1) W hM hT hMT (by simp) hSep hBase

theorem coprime_second_moment_le_full (M : ℕ) (W : Finset ℝ) :
    (∑ p ∈ nativeCoprimePairs M, ‖gmR W ((p.1 : ℝ) / p.2)‖ ^ 2) ≤
      gmDiscreteRatioMoment 2 M W := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro p hp hnot
  exact sq_nonneg _

/-- Reduced fractions remain in the fourth factor of this Cauchy step. -/
theorem coprime_third_moment_le_sqrt (M : ℕ) (W : Finset ℝ) :
    (∑ p ∈ nativeCoprimePairs M, ‖gmR W ((p.1 : ℝ) / p.2)‖ ^ 3) ≤
      Real.sqrt (gmDiscreteRatioMoment 2 M W) *
        Real.sqrt (nativeCoprimeFourth M W) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt (nativeCoprimePairs M)
    (fun p => ‖gmR W ((p.1 : ℝ) / p.2)‖)
    (fun p => ‖gmR W ((p.1 : ℝ) / p.2)‖ ^ 2)
  have hThree : (∑ p ∈ nativeCoprimePairs M, ‖gmR W ((p.1 : ℝ) / p.2)‖ ^ 3) =
      ∑ p ∈ nativeCoprimePairs M,
        ‖gmR W ((p.1 : ℝ) / p.2)‖ * ‖gmR W ((p.1 : ℝ) / p.2)‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro p hp
    ring
  have hFour : (∑ p ∈ nativeCoprimePairs M, (‖gmR W ((p.1 : ℝ) / p.2)‖ ^ 2) ^ 2) =
      nativeCoprimeFourth M W := by
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [← hThree, hFour] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (Real.sqrt_le_sqrt (coprime_second_moment_le_full M W)) (Real.sqrt_nonneg _))

end Montgomery.RationalMoment
