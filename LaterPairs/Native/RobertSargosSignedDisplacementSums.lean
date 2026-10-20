module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.RobertSargosDisplacementSums

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                       
                                    

noncomputable section
namespace TaoTrudgianYang2025

theorem sum_integer_natAbs_le_twice
    (S : Finset ℤ) (f : ℕ → ℝ) {N : ℕ}
    (hf : ∀ n ∈ Finset.Icc 1 N, 0 ≤ f n)
    (hmem : ∀ d ∈ S, d.natAbs ∈ Finset.Icc 1 N) :
    (∑ d ∈ S, f d.natAbs) ≤ 2*∑ n ∈ Finset.Icc 1 N, f n := by
  classical
  have hcard : ∀ n : ℕ, (S.filter (fun d => d.natAbs = n)).card ≤ 2 := by
    intro n
    have hsub : S.filter (fun d => d.natAbs = n) ⊆ {(n:ℤ),-(n:ℤ)} := by
      intro d hd
      simpa only [Finset.mem_insert,Finset.mem_singleton] using
        Int.natAbs_eq_iff.mp (Finset.mem_filter.mp hd).2
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  calc
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ _d ∈ S.filter (fun d => d.natAbs = n), f n :=
      (Finset.sum_fiberwise_of_maps_to' hmem f).symm
    _ ≤ ∑ n ∈ Finset.Icc 1 N, 2*f n := by
      apply Finset.sum_le_sum
      intro n hn
      simp only [Finset.sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard n) (hf n hn)
    _ = _ := by rw [Finset.mul_sum]

end TaoTrudgianYang2025
