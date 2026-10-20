module
public import DensityEnergyGM.DifferenceLevelCount
public import DensityEnergyGM.FiniteLayerCake

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset MeasureTheory GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

theorem norm_negative_polynomial_le_scale {M : ℕ} (a : ℕ → ℂ) (t : ℝ)
    (ha : ∀ n ∈ Ioc M (2 * M), ‖a n‖ ≤ 1) :
    ‖dirichletPoly M a t‖ ≤ M := by
  have h := norm_sourceDirichletPoly_le_scale (conjugateCoeffs a) t (by
    intro n hn
    rw [norm_conjugateCoeffs]
    exact ha n hn)
  simpa only [norm_sourceDirichletPoly_conjugateCoeffs] using h

/-- Exact regrouping by unit difference cells, retaining all pair weights. -/
theorem sum_differenceFloor_values (W : Finset ℝ) (g : ℤ → ℝ) :
    (∑ q ∈ differenceOrdinatePairs W, g (differenceFloor q)) =
      ∑ j ∈ differenceFloorSupport W, (differenceFloorCount W j : ℝ) * g j := by
  have hmaps : ∀ q ∈ differenceOrdinatePairs W,
      differenceFloor q ∈ differenceFloorSupport W := by
    intro q hq
    exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
  have h := Finset.sum_fiberwise_of_maps_to' hmaps g
  simpa only [Finset.sum_const, nsmul_eq_mul, differenceFloorCount] using h.symm

/-- The actual second difference moment is bounded by the literal weighted
layer-cake integral of any actual maximizing representatives. -/
theorem difference_second_moment_le_peak_integral {M : ℕ} (a : ℕ → ℂ)
    (W : Finset ℝ) (p : ℤ → ℝ × ℝ)
    (ha : ∀ n ∈ Ioc M (2 * M), ‖a n‖ ≤ 1)
    (hrep : ∀ j ∈ differenceFloorSupport W,
      p j ∈ differenceOrdinatePairs W ∧ differenceFloor (p j) = j ∧
        ∀ q ∈ differenceOrdinatePairs W, differenceFloor q = j →
          ‖dirichletPoly M a (q.1 - q.2)‖ ≤
            ‖dirichletPoly M a ((p j).1 - (p j).2)‖) :
    (∑ t ∈ W, ∑ u ∈ W, ‖dirichletPoly M a (t - u)‖ ^ 2) ≤
      ∫ s in Set.Ioc 0 ((M : ℝ) ^ 2),
        ∑ j ∈ (differenceFloorSupport W).filter (fun j =>
          s ≤ ‖dirichletPoly M a ((p j).1 - (p j).2)‖ ^ 2),
          (differenceFloorCount W j : ℝ) := by
  classical
  let S := differenceFloorSupport W
  let f : ℤ → ℝ := fun j => ‖dirichletPoly M a ((p j).1 - (p j).2)‖ ^ 2
  have hLayer := finite_weighted_layer_cake
    (fun j : S => differenceFloorCount W j) (fun j : S => f j)
    (by intro j; exact sq_nonneg _)
    (by
      intro j
      exact pow_le_pow_left₀ (norm_nonneg _)
        (norm_negative_polynomial_le_scale a _ ha) 2)
  have hLayer' : (∑ j ∈ S, (differenceFloorCount W j : ℝ) * f j) =
      ∫ s in Set.Ioc 0 ((M : ℝ) ^ 2),
        ∑ j ∈ S.filter (fun j => s ≤ f j), (differenceFloorCount W j : ℝ) := by
    have hsum : (∑ j : S, (differenceFloorCount W j : ℝ) * f j) =
        ∑ j ∈ S, (differenceFloorCount W j : ℝ) * f j :=
      Finset.sum_coe_sort S (fun j => (differenceFloorCount W j : ℝ) * f j)
    rw [hsum] at hLayer
    refine hLayer.trans ?_
    apply integral_congr_ae
    filter_upwards with s
    simp only [Finset.sum_filter] 
    exact Finset.sum_coe_sort S
      (fun j => if s ≤ f j then (differenceFloorCount W j : ℝ) else 0)
  calc
    (∑ t ∈ W, ∑ u ∈ W, ‖dirichletPoly M a (t - u)‖ ^ 2) =
        ∑ q ∈ differenceOrdinatePairs W, ‖dirichletPoly M a (q.1 - q.2)‖ ^ 2 := by
      rw [differenceOrdinatePairs, Finset.sum_product]
    _ ≤ ∑ q ∈ differenceOrdinatePairs W, f (differenceFloor q) := by
      apply Finset.sum_le_sum
      intro q hq
      have hmem : differenceFloor q ∈ S := Finset.mem_image.mpr ⟨q, hq, rfl⟩
      exact pow_le_pow_left₀ (norm_nonneg _)
        ((hrep (differenceFloor q) hmem).2.2 q hq rfl) 2
    _ = ∑ j ∈ S, (differenceFloorCount W j : ℝ) * f j := sum_differenceFloor_values W f
    _ = _ := hLayer'

end Montgomery.RationalMoment
