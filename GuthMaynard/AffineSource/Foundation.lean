module
/- Isolated from Scott McColm, smccolm/Lean pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1. MIT-0. See notes/guth-maynard-affine-reuse-audit.md. -/
public import Mathlib
public import MathCollab.Density.DivisorGrowth

@[expose] public section
open Complex Finset Filter FourierTransform MeasureTheory Real Set
open scoped ContDiff FourierTransform Topology
namespace RiemannZeta.GuthMaynard

noncomputable def dfiUnitRedundantBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

noncomputable def gmIntDecayProfile (q : ℕ) (m : ℤ) : ℝ :=
  if m = 0 then 0 else 1 / |(m : ℝ)| ^ q

theorem summable_gmIntDecayProfile {q : ℕ} (hq : 2 ≤ q) :
    Summable (gmIntDecayProfile q) := by
  have hs : Summable (fun m : ℤ => |1 / (m : ℝ) ^ q|) := by
    rw [summable_abs_iff]
    exact Real.summable_one_div_int_pow.mpr (lt_of_lt_of_le (by norm_num) hq)
  apply Summable.of_nonneg_of_le (fun m => by
    simp only [gmIntDecayProfile]
    split_ifs
    · exact le_rfl
    · positivity) (fun m => ?_) hs
  by_cases hm : m = 0
  · simp [gmIntDecayProfile, hm]
  · simp only [gmIntDecayProfile, ite_false, hm, abs_div, abs_one, abs_pow]
    exact le_rfl

noncomputable def gmCubicLocalBump (x : ℝ) : ℝ :=
  dfiUnitRedundantBump (x / 2)

theorem gmCubicLocalBump_nonneg (x : ℝ) : 0 ≤ gmCubicLocalBump x :=
  dfiUnitRedundantBump.nonneg

theorem gmCubicLocalBump_one {x : ℝ} (hx : |x| ≤ 1) :
    gmCubicLocalBump x = 1 := by
  unfold gmCubicLocalBump
  apply dfiUnitRedundantBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq]
  rw [sub_zero, show dfiUnitRedundantBump.rIn = (1 / 2 : ℝ) by rfl]
  rw [abs_div]
  norm_num
  linarith

theorem gmCubicLocalBump_le_one (x : ℝ) : gmCubicLocalBump x ≤ 1 :=
  dfiUnitRedundantBump.le_one

theorem gmCubicLocalBump_eq_zero_of_two_le_abs
    {x : ℝ} (hx : 2 ≤ |x|) : gmCubicLocalBump x = 0 := by
  by_contra hne
  have hsupp : x / 2 ∈ Function.support dfiUnitRedundantBump := by
    exact hne
  rw [dfiUnitRedundantBump.support_eq, Metric.mem_ball, Real.dist_eq] at hsupp
  simp only [sub_zero, show dfiUnitRedundantBump.rOut = (1 : ℝ) by rfl] at hsupp
  have habs : |x / 2| = |x| / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [habs] at hsupp
  linarith

def gmCubicSmoothingSupport (B v : ℝ) : Set ℝ :=
  Set.Icc (v - 2 / B) (v + 2 / B) ∩ Set.Icc (1 / 8 : ℝ) (33 / 8)

theorem norm_sum_sq_le_card_mul_sum_norm_sq {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℂ) :
    ‖∑ i ∈ s, a i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖a i‖ ^ 2 := by
  calc
    ‖∑ i ∈ s, a i‖ ^ 2 ≤ (∑ i ∈ s, ‖a i‖) ^ 2 := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, ‖a i‖ ^ 2 := by
      exact sq_sum_le_card_mul_sum_sq

def DivisorCountBoundProp : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε

theorem divisorCountBound_native : DivisorCountBoundProp := by
  intro ε hε
  obtain ⟨C,hC,h⟩ := MathCollab.Density.divisor_card_subpower hε
  exact ⟨C,by linarith,h⟩

end RiemannZeta.GuthMaynard
