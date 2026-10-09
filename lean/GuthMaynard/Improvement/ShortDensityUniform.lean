import MathCollab.Density.ZetaCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic

open Finset MathCollab.Density
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- Uniformization for the actual multiplicity-weighted zero count. The
fixed-sigma hypothesis is explicit; no density estimate is postulated.
A finite grid spends half of epsilon, while the other half is supplied to
the fixed-sigma estimate. The resulting constant precedes sigma and height. -/
theorem zetaDensityCount_uniform_of_fixed_sigma {c : ℝ} (hc : 0 < c)
    (hfixed : ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
        (zetaDensityCount σ T:ℝ) ≤ C*T^(c*(1-σ)+ε))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1/2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(c*(1-σ)+ε) := by
  classical
  obtain ⟨n,hn⟩ := exists_nat_gt (c/ε)
  have hn0 : 0 < (n:ℝ) := (div_pos hc hε).trans hn
  have hcn : c < (n:ℝ)*ε := (div_lt_iff₀ hε).mp hn
  let grid := fun j : Fin (n+1) => (1/2:ℝ)+(j:ℕ)/(2*(n:ℝ))
  have hg (j : Fin (n+1)) : 1/2 ≤ grid j ∧ grid j ≤ 1 := by
    have hj : (j:ℕ) ≤ n := Nat.le_of_lt_succ j.isLt
    have hjr : ((j:ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast hj
    dsimp [grid]
    constructor
    · have hd : (0:ℝ) ≤ ((j:ℕ):ℝ)/(2*(n:ℝ)) := by positivity
      linarith
    · have hd : ((j:ℕ):ℝ)/(2*(n:ℝ)) ≤ 1/2 :=
        (div_le_iff₀ (by positivity)).mpr (by nlinarith)
      linarith
  have hex (j : Fin (n+1)) := hfixed (grid j) (hg j).1 (hg j).2 (ε/2) (by positivity)
  choose C hC hbound using hex
  let B : ℝ := 1+∑ j : Fin (n+1),C j
  have hsum : 0 ≤ ∑ j : Fin (n+1),C j := Finset.sum_nonneg (fun j _ => (hC j).le)
  refine ⟨B,by dsimp [B]; positivity,?_⟩
  intro σ T hσ hσ' hT
  let x : ℝ := (2*σ-1)*(n:ℝ)
  have hx : 0 ≤ x := mul_nonneg (by linarith) hn0.le
  have hxn : x ≤ (n:ℝ) := by dsimp [x]; nlinarith
  have hjn : ⌊x⌋₊ ≤ n := by
    exact_mod_cast (Nat.floor_le hx).trans hxn
  let j : Fin (n+1) := ⟨⌊x⌋₊,Nat.lt_succ_of_le hjn⟩
  have hjlow : grid j ≤ σ := by
    have hh := Nat.floor_le hx
    dsimp [grid,j,x] at *
    have hd : (⌊(2*σ-1)*(n:ℝ)⌋₊:ℝ)/(2*(n:ℝ)) ≤ σ-1/2 :=
      (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    linarith
  have hjgap : σ-grid j ≤ 1/(2*(n:ℝ)) := by
    have hh := Nat.lt_floor_add_one x
    have hne : 2*(n:ℝ) ≠ 0 := by positivity
    dsimp [grid,j]
    apply (le_div_iff₀ (by positivity)).mpr
    field_simp [hne]
    dsimp [x] at hh
    nlinarith
  have hmesh : c*(σ-grid j) ≤ ε/2 := by
    have hdivide : c*(1/(2*(n:ℝ))) ≤ ε/2 := by
      apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
      have he : c*(1/(2*(n:ℝ)))*2 = c/(n:ℝ) := by field_simp
      rw [he]
      exact (div_le_iff₀ hn0).mpr (by linarith)
    exact (mul_le_mul_of_nonneg_left hjgap hc.le).trans hdivide
  have hexp : c*(1-grid j)+ε/2 ≤ c*(1-σ)+ε := by nlinarith
  have hmono : (zetaDensityCount σ T:ℝ) ≤ (zetaDensityCount (grid j) T:ℝ) := by
    exact_mod_cast zetaDensityCount_mono hjlow (le_refl T)
  have hCB : C j ≤ B := by
    have hh : C j ≤ ∑ i : Fin (n+1),C i :=
      Finset.single_le_sum (fun i _ => (hC i).le) (Finset.mem_univ j)
    dsimp [B]
    linarith
  calc
    _ ≤ C j*T^(c*(1-grid j)+ε/2) := hmono.trans (hbound j T hT)
    _ ≤ C j*T^(c*(1-σ)+ε) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith) hexp) (hC j).le
    _ ≤ B*T^(c*(1-σ)+ε) := mul_le_mul_of_nonneg_right hCB (by positivity)

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.zetaDensityCount_uniform_of_fixed_sigma
