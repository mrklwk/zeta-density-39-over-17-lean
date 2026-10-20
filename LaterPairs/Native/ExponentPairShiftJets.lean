module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import TaoTrudgianYang2025.ModelEndpointEntry
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.ExponentPairShiftPhase

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

 
                                                               

                                                               
                                                                       
                                                          


noncomputable section

open Set Expdb Filter
open scoped ContDiff Topology

namespace TaoTrudgianYang2025

theorem modelPhase_iteratedDeriv_succ_parameter (σ : ℝ) {u : ℝ}
    (hu : 0 < u) (p : ℕ) :
    iteratedDeriv (p+1) (modelPhase σ) u =
      -σ*iteratedDeriv p (modelPhase (σ+1)) u := by
  have he : deriv (modelPhase σ) =ᶠ[𝓝 u] fun x => -σ*modelPhase (σ+1) x := by
    filter_upwards [isOpen_Ioi.mem_nhds hu] with x hx
    have hd := (Real.hasDerivAt_rpow_const (Or.inl hx.ne') (p := -σ)).deriv
    change deriv (fun y : ℝ => y^(-σ)) x = -σ*x^(-(σ+1))
    simpa only [show -σ-1 = -(σ+1) by ring] using hd
  rw [iteratedDeriv_succ',he.iteratedDeriv_eq p,iteratedDeriv_const_mul_field]

theorem aProcessShiftPhase_iteratedDeriv
    {F : ℝ → ℝ} {η u : ℝ}
    (hF : ContDiffOn ℝ ∞ F phaseInterval) (hη : 0 ≤ η) (hη₁ : η < 1)
    (hu : u ∈ Ioo (1 : ℝ) 2) (σ : ℝ) (n : ℕ) :
    iteratedDeriv n (aProcessShiftPhase F σ η) u =
      (1-η)^n/(σ*η) *
        (iteratedDeriv n F (aProcessShiftPoint η 0 u)-
         iteratedDeriv n F (aProcessShiftPoint η 1 u)) := by
  have hi (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      aProcessShiftPoint η t u ∈ Ioo (1 : ℝ) 2 :=
    aProcessShiftPoint_mem_Ioo hη hη₁ ht hu
  have hc (G : ℝ → ℝ) (hG : ContDiffOn ℝ ∞ G phaseInterval)
      (x : ℝ) (hx : x ∈ Ioo (1 : ℝ) 2) :
      iteratedDerivWithin n G phaseInterval x = iteratedDeriv n G x := by
    apply iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_phaseInterval
    · exact ((hG x ⟨hx.1.le,hx.2.le⟩).contDiffAt
        (mem_of_superset (isOpen_Ioo.mem_nhds hx) Ioo_subset_Icc_self)).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
    · exact ⟨hx.1.le,hx.2.le⟩
  have h := aProcessShiftPhase_iteratedDerivWithin hF hη hη₁.le
    (u := u) ⟨hu.1.le,hu.2.le⟩ σ n
  rw [hc _ (aProcessShiftPhase_contDiffOn hF hη hη₁.le σ) _ hu,
    hc _ hF _ (hi 0 (by norm_num)),hc _ hF _ (hi 1 (by norm_num))] at h
  exact h

end TaoTrudgianYang2025
