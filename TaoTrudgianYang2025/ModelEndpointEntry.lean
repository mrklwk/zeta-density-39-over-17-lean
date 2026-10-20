module
public import Mathlib
public import Expdb.ExponentialSums.PhaseFunctions

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set Filter Expdb
open scoped Topology ContDiff
namespace TaoTrudgianYang2025
theorem approximateModelPhase_of_interior_bounds
    {F : ℝ → ℝ} {σ ε : ℝ} {P : ℕ}
    (hF : ContDiffOn ℝ ∞ F phaseInterval)
    (hb : ∀ u ∈ Ioo (1 : ℝ) 2, ∀ p ≤ P,
      |iteratedDeriv (p+1) F u-iteratedDeriv p (modelPhase σ) u| ≤ ε) :
    IsApproximateModelPhaseFunction F σ P ε := by
  refine ⟨hF,?_⟩
  intro p hp u
  have hc : ContinuousOn (fun x =>
      ‖iteratedDerivWithin (p+1) F phaseInterval x-
        iteratedDerivWithin p (modelPhase σ) phaseInterval x‖) phaseInterval :=
    ((hF.continuousOn_iteratedDerivWithin
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl (p+1)) uniqueDiffOn_phaseInterval).sub
      (continuousOn_iteratedDerivWithin_modelPhase σ p)).norm
  have hi : ∀ x ∈ Ioo (1 : ℝ) 2,
      ‖iteratedDerivWithin (p+1) F phaseInterval x-
        iteratedDerivWithin p (modelPhase σ) phaseInterval x‖ ≤ ε := by
    intro x hx
    have hxI : x ∈ phaseInterval := ⟨hx.1.le,hx.2.le⟩
    have hxN : phaseInterval ∈ 𝓝 x :=
      mem_of_superset (isOpen_Ioo.mem_nhds hx) Ioo_subset_Icc_self
    have hf : ContDiffAt ℝ (p+1) F x :=
      (hF x hxI).contDiffAt hxN |>.of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl (p+1))
    have hm : ContDiffAt ℝ p (modelPhase σ) x :=
      Real.contDiffAt_rpow_const_of_ne (zero_lt_one.trans hx.1).ne'
    rw [iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_phaseInterval hf hxI,
      iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_phaseInterval hm hxI,Real.norm_eq_abs]
    exact hb x hx p hp
  have hcl : closure (Ioo (1 : ℝ) 2) = phaseInterval := by
    rw [closure_Ioo (by norm_num : (1 : ℝ) ≠ 2)]
    rfl
  exact le_on_closure hi (by simpa only [hcl] using hc) continuousOn_const
    (by simpa only [hcl] using u.property)


end TaoTrudgianYang2025
