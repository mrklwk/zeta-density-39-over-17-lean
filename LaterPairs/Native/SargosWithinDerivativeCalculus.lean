module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.SargosDualTentWindow
public import LaterPairs.Native.SargosInitialInterval
public import LaterPairs.Native.SargosLocalAffineJets
public import LaterPairs.Native.SargosSourceDifferencing

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                                       

noncomputable section

open Set Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025

theorem sargos_iteratedDerivWithin_comp_order (i j : ℕ) (f : ℝ → ℝ) (s : Set ℝ) :
    iteratedDerivWithin i (iteratedDerivWithin j f s) s = iteratedDerivWithin (i+j) f s := by
  ext x
  simp only [iteratedDerivWithin_eq_iterate,Function.iterate_add_apply]
  rw [show iteratedDerivWithin j f s = (fun g : ℝ → ℝ => derivWithin g s)^[j] f from
    funext (fun y => iteratedDerivWithin_eq_iterate)]

theorem sargos_contDiffOn_iteratedDerivWithin {f : ℝ → ℝ} {s : Set ℝ}
    (hf : ContDiffOn ℝ ∞ f s) (hs : UniqueDiffOn ℝ s) (n : ℕ) :
    ContDiffOn ℝ ∞ (iteratedDerivWithin n f s) s := by
  induction n with
  | zero => simpa only [iteratedDerivWithin_zero] using hf
  | succ n hn =>
      rw [iteratedDerivWithin_succ]
      exact hn.derivWithin hs (by simp)

end TaoTrudgianYang2025
