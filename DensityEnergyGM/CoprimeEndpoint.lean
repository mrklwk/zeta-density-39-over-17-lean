module
public import DensityEnergyGM.CoprimeFourthNative

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

theorem coprime_fourth_insert_product_le {A : Finset ℕ} {e : ℕ}
    (heA : e ∉ A) (W : Finset ℝ) :
    (∑ p ∈ ((insert e A) ×ˢ (insert e A)).filter (fun p => Nat.Coprime p.1 p.2),
      ‖gmR W ((p.1 : ℝ) / p.2)‖ ^ 4) ≤
    (∑ p ∈ (A ×ˢ A).filter (fun p => Nat.Coprime p.1 p.2),
      ‖gmR W ((p.1 : ℝ) / p.2)‖ ^ 4) +
        (2 * (A.card : ℝ) + 1) * (W.card : ℝ) ^ 4 := by
  let H : ℕ → ℕ → ℝ := fun n m =>
    if Nat.Coprime n m then ‖gmR W ((n : ℝ) / m)‖ ^ 4 else 0
  have hH : ∀ n m, H n m ≤ (W.card : ℝ) ^ 4 := by
    intro n m
    dsimp only [H]
    split_ifs
    · exact pow_le_pow_left₀ (norm_nonneg _) (norm_gmR_le_card_all W _) 4
    · positivity
  have hRow : (∑ m ∈ A, H e m) ≤ (A.card : ℝ) * (W.card : ℝ) ^ 4 := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      (Finset.sum_le_sum fun m hm => hH e m)
  have hCol : (∑ n ∈ A, H n e) ≤ (A.card : ℝ) * (W.card : ℝ) ^ 4 := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      (Finset.sum_le_sum fun n hn => hH n e)
  simp only [Finset.sum_filter, Finset.sum_product]
  change (∑ n ∈ insert e A, ∑ m ∈ insert e A, H n m) ≤
    (∑ n ∈ A, ∑ m ∈ A, H n m) + (2 * (A.card : ℝ) + 1) * (W.card : ℝ) ^ 4
  simp only [Finset.sum_insert heA, Finset.sum_add_distrib]
  linarith [hH e e]

end Montgomery.RationalMoment
