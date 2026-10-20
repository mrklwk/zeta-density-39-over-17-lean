module
public import DensityEnergyGM.DifferenceLayerCake

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset MeasureTheory GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

theorem sqrt_inverse_four {s : ℝ} (hs : 0 < s) :
    (Real.sqrt s) ^ (-4 : ℝ) = 1 / s ^ 2 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hs.le]
  norm_num

theorem sqrt_inverse_eight {s : ℝ} (hs : 0 < s) :
    (Real.sqrt s) ^ (-8 : ℝ) = 1 / s ^ 4 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hs.le]
  norm_num

/-- Unconditional actual second-moment integral reduction. Both the
native weak estimate and its actual maximizing representatives are supplied
inside the proof. The integral has the exact critical 1/s and 1/s^2 scales. -/
theorem actual_second_moment_integral_native (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (M : ℕ) (T : ℝ) (a : ℕ → ℂ) (W : Finset ℝ),
        0 < M → T₀ ≤ T → (M : ℝ) ^ 2 ≤ T →
        (∀ n ∈ Ioc M (2 * M), ‖a n‖ ≤ 1) → InBaseInterval T W →
        (∑ t ∈ W, ∑ u ∈ W, ‖dirichletPoly M a (t - u)‖ ^ 2) ≤
          ∫ s in Set.Ioc 0 ((M : ℝ) ^ 2),
            min ((W.card : ℝ) ^ 2)
              (Real.sqrt ((discreteAdditiveEnergy W : ℝ) *
                (C * (2 * T) ^ ε *
                  ((M : ℝ) ^ 4 / s ^ 2 +
                    ((M : ℝ) ^ (36 / 5 : ℝ) +
                      (2 * T) * (M : ℝ) ^ (24 / 5 : ℝ)) / s ^ 4)))) := by
  obtain ⟨C, T₀, hC, hT₀, hWeak⟩ := difference_cell_weighted_level_native ε hε
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro M T a W hM hT hMT ha hBase
  obtain ⟨p, hrep, hmass⟩ := hWeak M T a W hM hT hMT ha hBase
  let H : ℝ → ℝ := fun s =>
    ∑ j ∈ (differenceFloorSupport W).filter (fun j =>
      s ≤ ‖dirichletPoly M a ((p j).1 - (p j).2)‖ ^ 2),
      (differenceFloorCount W j : ℝ)
  let G : ℝ → ℝ := fun s => min ((W.card : ℝ) ^ 2)
    (Real.sqrt ((discreteAdditiveEnergy W : ℝ) *
      (C * (2 * T) ^ ε * ((M : ℝ) ^ 4 / s ^ 2 +
        ((M : ℝ) ^ (36 / 5 : ℝ) +
          (2 * T) * (M : ℝ) ^ (24 / 5 : ℝ)) / s ^ 4))))
  have hGmeas : Measurable G := by dsimp only [G]; fun_prop
  have hG0 : ∀ s, 0 ≤ G s := fun s =>
    le_min (sq_nonneg _) (Real.sqrt_nonneg _)
  have hfinite : volume (Set.Ioc (0 : ℝ) ((M : ℝ) ^ 2)) < ⊤ := by simp
  let : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) ((M : ℝ) ^ 2))) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfinite⟩
  have hGint : IntegrableOn G (Set.Ioc 0 ((M : ℝ) ^ 2)) := by
    apply (integrable_const ((W.card : ℝ) ^ 2)).mono' hGmeas.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro s
    rw [Real.norm_eq_abs, abs_of_nonneg (hG0 s)]
    exact min_le_left _ _
  have hUpper : ∀ s : ℝ, 0 < s → H s ≤ G s := by
    intro s hs
    have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
    have h := hmass (Real.sqrt s) hsqrt
    have hfilter : (differenceFloorSupport W).filter (fun j =>
        Real.sqrt s ≤ ‖dirichletPoly M a ((p j).1 - (p j).2)‖) =
      (differenceFloorSupport W).filter (fun j =>
        s ≤ ‖dirichletPoly M a ((p j).1 - (p j).2)‖ ^ 2) := by
      apply Finset.filter_congr
      intro j hj
      have hn := norm_nonneg (dirichletPoly M a ((p j).1 - (p j).2))
      have hsq := Real.sq_sqrt hs.le
      constructor <;> intro hh <;> nlinarith
    rw [hfilter, sqrt_inverse_four hs, sqrt_inverse_eight hs] at h
    have hshape : (M : ℝ) ^ 4 * (1 / s ^ 2) +
        (M : ℝ) ^ (36 / 5 : ℝ) * (1 / s ^ 4) +
        (2 * T) * (M : ℝ) ^ (24 / 5 : ℝ) * (1 / s ^ 4) =
      (M : ℝ) ^ 4 / s ^ 2 +
        ((M : ℝ) ^ (36 / 5 : ℝ) +
          (2 * T) * (M : ℝ) ^ (24 / 5 : ℝ)) / s ^ 4 := by ring
    rw [hshape] at h
    exact h
  have hIntegral : (∫ s in Set.Ioc 0 ((M : ℝ) ^ 2), H s) ≤
      ∫ s in Set.Ioc 0 ((M : ℝ) ^ 2), G s := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun s =>
        Finset.sum_nonneg fun j hj => Nat.cast_nonneg _
    · exact hGint
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact hUpper s hs.1
  exact (difference_second_moment_le_peak_integral a W p ha hrep).trans hIntegral

end Montgomery.RationalMoment
