module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import MathCollab.Density.Stronger.Atkinson.SeparatedReciprocal
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.AdditiveEnergy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

 
                                                                

                                                                      
                                                                   
                                                                            


noncomputable section

open Finset MeasureTheory Set
open scoped BigOperators

namespace TaoTrudgianYang2025

def zetaMomentKernel (t u : ℝ) : ℝ := 1 / (1 + |u - t|)

theorem zetaMomentKernel_pos (t u : ℝ) : 0 < zetaMomentKernel t u := by
  unfold zetaMomentKernel
  positivity

theorem sum_zetaMomentKernel_le_harmonic
    (W : Finset ℝ) (u : ℝ) (N : ℕ)
    (hSep : MathCollab.Density.Stronger.Atkinson.IsSeparated 1 W)
    (hRange : ∀ t ∈ W, |t - u| ≤ N) :
    (∑ t ∈ W, zetaMomentKernel t u) ≤ 1 + 2 * (harmonic (N + 1) : ℝ) := by
  let S := W.erase u
  let shell : ℝ → ℕ := fun t => ⌊|t - u|⌋₊
  have hmaps : ∀ t ∈ S, shell t ∈ Finset.range (N + 1) := by
    intro t ht
    have hr := hRange t (Finset.mem_of_mem_erase ht)
    have hfloor : ((shell t : ℕ) : ℝ) ≤ (N : ℝ) :=
      (Nat.floor_le (abs_nonneg _)).trans hr
    have : shell t ≤ N := by exact_mod_cast hfloor
    simpa only [Finset.mem_range] using Nat.lt_succ_of_le this
  have hoff : (∑ t ∈ S, zetaMomentKernel t u) ≤ 2 * (harmonic (N + 1) : ℝ) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun t => zetaMomentKernel t u)]
    calc
      _ ≤ ∑ k ∈ Finset.range (N + 1), 2 * (1 / ((k : ℝ) + 1)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hcard : ({t ∈ S | shell t = k}).card ≤ 2 := by
          apply le_trans (Finset.card_le_card ?_)
            (MathCollab.Density.Stronger.Atkinson.separated_annulus_card_le_two W u k hSep)
          intro t ht
          obtain ⟨htS, htk⟩ := Finset.mem_filter.mp ht
          have htW := Finset.mem_erase.mp htS
          apply Finset.mem_filter.mpr
          refine ⟨htW.2, htW.1, ?_, ?_⟩
          · rw [← htk]
            exact Nat.floor_le (abs_nonneg _)
          · rw [← htk]
            exact Nat.lt_floor_add_one _
        calc
          _ ≤ ∑ _t ∈ {t ∈ S | shell t = k}, 1 / ((k : ℝ) + 1) := by
            apply Finset.sum_le_sum
            intro t ht
            have htk := (Finset.mem_filter.mp ht).2
            have hl : (k : ℝ) ≤ |t - u| := by
              rw [← htk]
              exact Nat.floor_le (abs_nonneg _)
            unfold zetaMomentKernel
            rw [abs_sub_comm u t]
            apply one_div_le_one_div_of_le (by positivity)
            linarith
          _ = (({t ∈ S | shell t = k}).card : ℝ) * (1 / ((k : ℝ) + 1)) := by simp
          _ ≤ 2 * (1 / ((k : ℝ) + 1)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast hcard
      _ = 2 * (harmonic (N + 1) : ℝ) := by
        rw [harmonic]
        push_cast
        simp only [inv_eq_one_div]
        rw [Finset.mul_sum]
  by_cases hu : u ∈ W
  · rw [← Finset.sum_erase_add _ _ hu]
    have heq : zetaMomentKernel u u = 1 := by simp [zetaMomentKernel]
    rw [heq]
    dsimp [S] at hoff
    linarith
  · have hS : S = W := by simpa only [S] using (Finset.erase_eq_of_notMem hu)
    rw [hS] at hoff
    linarith

theorem sum_zetaMomentKernel_le_log
    (W : Finset ℝ) (u : ℝ) (N : ℕ)
    (hSep : MathCollab.Density.Stronger.Atkinson.IsSeparated 1 W)
    (hRange : ∀ t ∈ W, |t - u| ≤ N) :
    (∑ t ∈ W, zetaMomentKernel t u) ≤ 3 + 2 * Real.log (N + 1) := by
  have h := sum_zetaMomentKernel_le_harmonic W u N hSep hRange
  have hh := harmonic_le_one_add_log (N + 1)
  push_cast at hh
  linarith

                                                                   
                      
end TaoTrudgianYang2025
