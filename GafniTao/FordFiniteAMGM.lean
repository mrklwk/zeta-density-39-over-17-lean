module
public import Mathlib

@[expose] public section
open Finset
noncomputable section
namespace GafniTao
theorem ford_norm_sum_sq_le_card_mul_sum_norm_sq
    {α : Type*} (B : Finset α) (V : α → ℂ) :
    ‖∑ b ∈ B, V b‖ ^ 2 ≤
      (B.card : ℝ) * ∑ b ∈ B, ‖V b‖ ^ 2 := by
  have htri : ‖∑ b ∈ B, V b‖ ≤ ∑ b ∈ B, ‖V b‖ := norm_sum_le B V
  calc
    ‖∑ b ∈ B, V b‖ ^ 2 ≤ (∑ b ∈ B, ‖V b‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    _ ≤ (B.card : ℝ) * ∑ b ∈ B, ‖V b‖ ^ 2 := by
      simpa using
        (sq_sum_le_card_mul_sum_sq (s := B) (f := fun b => ‖V b‖))

end GafniTao
