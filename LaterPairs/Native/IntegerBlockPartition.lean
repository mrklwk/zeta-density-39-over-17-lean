module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.ContinuousPhaseWeyl

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                      

noncomputable section
namespace TaoTrudgianYang2025

theorem sum_range_mul_blocks {A : Type*} [AddCommMonoid A]
    (f : ℕ → A) (K L : ℕ) :
    (∑ n ∈ Finset.range (K*L), f n) =
      ∑ k ∈ Finset.range K, ∑ j ∈ Finset.range L, f (k*L+j) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Nat.succ_mul,Finset.sum_range_add,ih,Finset.sum_range_succ]

theorem sum_range_euclidean_blocks {A : Type*} [AddCommMonoid A]
    (f : ℕ → A) (N L : ℕ) :
    (∑ n ∈ Finset.range N, f n) =
      (∑ k ∈ Finset.range (N/L), ∑ j ∈ Finset.range L, f (k*L+j))+
        ∑ j ∈ Finset.range (N%L), f ((N/L)*L+j) := by
  conv_lhs => rw [← Nat.div_add_mod' N L]
  rw [Finset.sum_range_add,sum_range_mul_blocks]

theorem norm_sum_range_of_block_bounds
    (f : ℕ → ℂ) (N L : ℕ) {B : ℝ}
    (hb : ∀ k < N/L, ‖∑ j ∈ Finset.range L, f (k*L+j)‖ ≤ B)
    (ht : ‖∑ j ∈ Finset.range (N%L), f ((N/L)*L+j)‖ ≤ B) :
    ‖∑ n ∈ Finset.range N, f n‖ ≤ ((N/L:ℕ)+1:ℝ)*B := by
  rw [sum_range_euclidean_blocks f N L]
  calc
    _ ≤ ‖∑ k ∈ Finset.range (N/L), ∑ j ∈ Finset.range L, f (k*L+j)‖+
        ‖∑ j ∈ Finset.range (N%L), f ((N/L)*L+j)‖ := norm_add_le _ _
    _ ≤ (∑ k ∈ Finset.range (N/L), ‖∑ j ∈ Finset.range L, f (k*L+j)‖)+B :=
      add_le_add (norm_sum_le _ _) ht
    _ ≤ (∑ _k ∈ Finset.range (N/L), B)+B := by
      apply add_le_add_left
      exact Finset.sum_le_sum (fun k hk => hb k (Finset.mem_range.mp hk))
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring

end TaoTrudgianYang2025
