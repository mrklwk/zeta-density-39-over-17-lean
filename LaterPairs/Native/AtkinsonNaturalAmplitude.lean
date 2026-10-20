module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

 
                                                                  

                                                              
                                                                      
                                                              


noncomputable section

open Complex Set Filter
open scoped ContDiff Topology

namespace TaoTrudgianYang2025

theorem IntervalC2Bound.comp_div {f : ℝ → ℂ} {a b M R c : ℝ}
    (hf : IntervalC2Bound f a b M R) (hc : 0 < c) :
    IntervalC2Bound (fun y => f (y / c)) (c * a) (c * b) M (R / c) := by
  have hmem {y : ℝ} (hy : y ∈ Icc (c * a) (c * b)) : y / c ∈ Icc a b := by
    constructor
    · apply (le_div_iff₀ hc).2; nlinarith [hy.1]
    · apply (div_le_iff₀ hc).2; nlinarith [hy.2]
  have hg : ContDiff ℝ 2 (fun y : ℝ => y / c) := by fun_prop
  have hderiv : deriv (fun y : ℝ => y / c) = fun _ => 1 / c := by
    funext y
    exact ((hasDerivAt_id y).div_const c).deriv
  have hsecond (y : ℝ) : iteratedDeriv 2 (fun z : ℝ => z / c) y = 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv, deriv_const]
  refine ⟨hf.nonneg, div_nonneg hf.scale_nonneg hc.le,
    fun y hy => (hf.smooth (y / c) (hmem hy)).comp y hg.contDiffAt,
    fun y hy => hf.norm_le (y / c) (hmem hy), ?_, ?_⟩
  · intro y hy
    have hd : HasDerivAt (fun z => f (z / c)) ((1 / c : ℝ) • deriv f (y / c)) y :=
      ((hf.smooth (y / c) (hmem hy)).differentiableAt (by norm_num)).hasDerivAt.scomp
        y ((hasDerivAt_id y).div_const c)
    rw [hd.deriv, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / c)]
    apply (mul_le_mul_of_nonneg_left (hf.deriv_le (y / c) (hmem hy)) (by positivity)).trans_eq
    ring
  · intro y hy
    rw [iteratedDeriv_two_comp_real (g := fun z => z / c)
      (hf.smooth (y / c) (hmem hy)) hg.contDiffAt,
      hderiv, hsecond, zero_smul, add_zero, norm_smul, Real.norm_eq_abs, abs_pow, sq_abs]
    apply (mul_le_mul_of_nonneg_left (hf.second_le (y / c) (hmem hy)) (sq_nonneg (1 / c))).trans_eq
    ring

end TaoTrudgianYang2025
