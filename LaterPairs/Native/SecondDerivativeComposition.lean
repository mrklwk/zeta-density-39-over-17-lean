module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.IntervalSecondDerivativeBounds

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

 
                                                             

                                                             
                                                           


noncomputable section

open Complex Filter Set Topology
open scoped ContDiff

namespace TaoTrudgianYang2025

theorem iteratedDeriv_two_comp_real {f : ℝ → ℂ} {g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f (g x)) (hg : ContDiffAt ℝ 2 g x) :
    iteratedDeriv 2 (fun y => f (g y)) x =
      (deriv g x) ^ 2 • iteratedDeriv 2 f (g x) +
        iteratedDeriv 2 g x • deriv f (g x) := by
  have he : deriv (fun y => f (g y)) =ᶠ[𝓝 x]
      fun y => deriv g y • deriv f (g y) := by
    filter_upwards [hg.eventually (by norm_num),
      hg.continuousAt.eventually (hf.eventually (by norm_num))] with y hgy hfy
    exact (hfy.differentiableAt (by norm_num)).hasDerivAt.scomp
      y (hgy.differentiableAt (by norm_num)).hasDerivAt |>.deriv
  have hdg := ((hg.derivWithin (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasDerivAt
  have hdf := ((hf.derivWithin (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasDerivAt
  have h := hdg.smul (hdf.scomp x (hg.differentiableAt (by norm_num)).hasDerivAt)
  have h' : HasDerivAt (fun y => deriv g y • deriv f (g y))
      ((deriv g x)^2 • iteratedDeriv 2 f (g x) +
        iteratedDeriv 2 g x • deriv f (g x)) x := by
    convert h using 1
    · rfl
    · simp only [iteratedDeriv_succ, iteratedDeriv_zero, pow_two, mul_smul,
        Function.comp_apply]
  rw [iteratedDeriv_succ, iteratedDeriv_one, he.deriv_eq]
  exact h'.deriv

theorem IntervalC2Bound.congr_of_eventuallyEq {f g : ℝ → ℂ} {a b M R : ℝ}
    (hf : IntervalC2Bound f a b M R)
    (he : ∀ x ∈ Icc a b, f =ᶠ[𝓝 x] g) :
    IntervalC2Bound g a b M R := by
  refine ⟨hf.nonneg, hf.scale_nonneg, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (hf.smooth x hx).congr_of_eventuallyEq (he x hx).symm
  · intro x hx
    rw [← (he x hx).eq_of_nhds]
    exact hf.norm_le x hx
  · intro x hx
    rw [← (he x hx).deriv_eq]
    exact hf.deriv_le x hx
  · intro x hx
    rw [← (he x hx).iteratedDeriv_eq 2]
    exact hf.second_le x hx

end TaoTrudgianYang2025
