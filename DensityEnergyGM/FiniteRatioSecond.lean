module
public import DensityEnergyGM.RatioMomentSharp

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

def finiteRatioSecond (A : Finset ℕ) (W : Finset ℝ) : ℝ :=
  ∑ n ∈ A, ∑ m ∈ A, ‖gmR W ((n : ℝ) / m)‖ ^ 2

theorem finiteRatioSecond_nonneg (A : Finset ℕ) (W : Finset ℝ) :
    0 ≤ finiteRatioSecond A W := by
  exact Finset.sum_nonneg fun n hn => Finset.sum_nonneg fun m hm => sq_nonneg _

theorem finiteRatioSecond_mono {A B : Finset ℕ} (hAB : A ⊆ B) (W : Finset ℝ) :
    finiteRatioSecond A W ≤ finiteRatioSecond B W := by
  apply (Finset.sum_le_sum fun n hn =>
    Finset.sum_le_sum_of_subset_of_nonneg hAB (fun m hm hnot => sq_nonneg _)).trans
  exact Finset.sum_le_sum_of_subset_of_nonneg hAB
    (fun n hn hnot => Finset.sum_nonneg fun m hm => sq_nonneg _)

theorem finiteRatioSecond_eq_difference (A : Finset ℕ) (W : Finset ℝ)
    (hA : ∀ n ∈ A, 0 < n) :
    finiteRatioSecond A W = heathBrownDifferenceMoment A W (fun _ => 1) := by
  have h : heathBrownDifferenceMoment A W (fun _ => 1) =
      ∑ n ∈ A, ∑ m ∈ A, heathBrownMajorantKernel W n m := by
    simpa only [Complex.ofReal_one, one_mul] using
      heathBrownDifferenceMoment_ofReal_eq_kernel_sum A W (fun _ => (1 : ℝ))
  rw [h]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  exact (heathBrownMajorantKernel_eq_norm_gmR_ratio W n m (hA n hn) (hA m hm)).symm

theorem finiteRatioSecond_insert_le {A : Finset ℕ} {e : ℕ}
    (heA : e ∉ A) (he : 0 < e) (hA : ∀ n ∈ A, 0 < n) (W : Finset ℝ) :
    finiteRatioSecond (insert e A) W ≤
      2 * finiteRatioSecond A W + 2 * (W.card : ℝ) ^ 2 := by
  rw [finiteRatioSecond_eq_difference _ _ (by
    intro n hn
    rcases Finset.mem_insert.mp hn with rfl | hn
    · exact he
    · exact hA n hn), finiteRatioSecond_eq_difference _ _ hA]
  have hPhase : ∀ t : ℝ, ‖heathBrownPhase e t‖ = 1 := by
    intro t
    rw [heathBrownPhase, Complex.norm_natCast_cpow_of_pos he]
    simp
  have hPoint : ∀ t u : ℝ,
      ‖heathBrownDifferencePolynomial (insert e A) (fun _ => 1) t u‖ ^ 2 ≤
        2 * ‖heathBrownDifferencePolynomial A (fun _ => 1) t u‖ ^ 2 + 2 := by
    intro t u
    rw [heathBrownDifferencePolynomial, Finset.sum_insert heA]
    simp only [one_mul]
    have hDef : heathBrownDifferencePolynomial A (fun _ => 1) t u =
        ∑ n ∈ A, heathBrownPhase n t * star (heathBrownPhase n u) := by
      simp only [heathBrownDifferencePolynomial, one_mul]
    rw [← hDef]
    have hnorm := norm_add_le (heathBrownPhase e t * star (heathBrownPhase e u))
      (heathBrownDifferencePolynomial A (fun _ => 1) t u)
    rw [norm_mul, norm_star, hPhase, hPhase, one_mul] at hnorm
    have hnonneg := norm_nonneg
      (heathBrownPhase e t * star (heathBrownPhase e u) +
        heathBrownDifferencePolynomial A (fun _ => 1) t u)
    nlinarith [sq_nonneg (‖heathBrownDifferencePolynomial A (fun _ => 1) t u‖ - 1)]
  calc
    _ ≤ ∑ t ∈ W, ∑ u ∈ W,
        (2 * ‖heathBrownDifferencePolynomial A (fun _ => 1) t u‖ ^ 2 + 2) := by
      apply Finset.sum_le_sum
      intro t ht
      exact Finset.sum_le_sum fun u hu => hPoint t u
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, nsmul_eq_mul, heathBrownDifferenceMoment]
      ring

end Montgomery.RationalMoment
