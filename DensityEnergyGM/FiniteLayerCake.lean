module
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Finset MeasureTheory
namespace Montgomery.RationalMoment

/-- Finite layer cake with the closed upper level set. The integral starts
at zero, where including the boundary changes no mass. -/
theorem finite_layer_cake {ι : Type*} [Fintype ι] (f : ι → ℝ) {B : ℝ}
    (hf0 : ∀ i, 0 ≤ f i) (hfB : ∀ i, f i ≤ B) :
    (∑ i, f i) = ∫ u in Set.Ioc 0 B,
      (((Finset.univ.filter fun i => u ≤ f i).card) : ℝ) := by
  classical
  let : MeasurableSpace ι := ⊤
  let : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  have hInt : Integrable f Measure.count := integrable_count_iff.mpr Summable.of_finite
  have h := hInt.integral_eq_integral_Ioc_meas_le
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hfB)
  rw [integral_count] at h
  refine h.trans ?_
  apply integral_congr_ae
  filter_upwards with u
  have hset : {i : ι | u ≤ f i} =
      (Finset.univ.filter fun i => u ≤ f i : Finset ι) := by
    ext i
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
  rw [Measure.real, hset, Measure.count_apply_finset, ENNReal.toReal_natCast]

/-- Natural occupancy weights are expanded into a finite family of copies,
so the weighted layer cake is the literal finite integral identity. -/
theorem finite_weighted_layer_cake {ι : Type*} [Fintype ι]
    (r : ι → ℕ) (f : ι → ℝ) {B : ℝ}
    (hf0 : ∀ i, 0 ≤ f i) (hfB : ∀ i, f i ≤ B) :
    (∑ i, (r i : ℝ) * f i) = ∫ u in Set.Ioc 0 B,
      ∑ i ∈ (Finset.univ.filter fun i => u ≤ f i), (r i : ℝ) := by
  classical
  have h := finite_layer_cake (fun p : (Σ i, Fin (r i)) => f p.1)
    (fun p => hf0 p.1) (fun p => hfB p.1)
  have hsum : (∑ p : (Σ i, Fin (r i)), f p.1) = ∑ i, (r i : ℝ) * f i := by
    rw [Fintype.sum_sigma]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hsum] at h
  refine h.trans ?_
  apply integral_congr_ae
  filter_upwards with u
  calc
    (((Finset.univ.filter fun p : (Σ i, Fin (r i)) => u ≤ f p.1).card) : ℝ) =
        ∑ p : (Σ i, Fin (r i)), if u ≤ f p.1 then (1 : ℝ) else 0 := by
      simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
        Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    _ = ∑ i, ∑ _j : Fin (r i), if u ≤ f i then (1 : ℝ) else 0 := by
      rw [Fintype.sum_sigma]
    _ = ∑ i, if u ≤ f i then (r i : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hui : u ≤ f i <;> simp only [hui, ↓reduceIte, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, mul_zero]
    _ = ∑ i ∈ (Finset.univ.filter fun i => u ≤ f i), (r i : ℝ) := by
      rw [Finset.sum_filter]

end Montgomery.RationalMoment
