module
public import Mathlib
public import TaoTrudgianYang2025.ExponentPair

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set Expdb
open scoped ContDiff
namespace TaoTrudgianYang2025
def modelPhaseJetCoefficient (σ : ℝ) (p : ℕ) : ℝ :=
  |(descPochhammer ℝ p).eval (-σ)|

theorem modelPhaseJetCoefficient_nonneg (σ : ℝ) (p : ℕ) :
    0 ≤ modelPhaseJetCoefficient σ p :=
  abs_nonneg _

theorem approximateModelPhase_iteratedDeriv_error
    {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) (p : ℕ) (hp : p ≤ P) :
    |iteratedDeriv (p+1) F u - iteratedDeriv p (modelPhase σ) u| ≤ δ := by
  have he := hF.2 p hp ⟨u, hu.1.le, hu.2.le⟩
  have hc : ContDiffAt ℝ (p+1) F u :=
    (hF.1.contDiffAt (Icc_mem_nhds hu.1 hu.2)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl (p+1))
  have hm : ContDiffAt ℝ p (modelPhase σ) u :=
    Real.contDiffAt_rpow_const_of_ne (zero_lt_one.trans hu.1).ne'
  change ‖iteratedDerivWithin (p+1) F phaseInterval u -
    iteratedDerivWithin p (modelPhase σ) phaseInterval u‖ ≤ δ at he
  rw [iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_phaseInterval hc
    ⟨hu.1.le,hu.2.le⟩, iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_phaseInterval hm
    ⟨hu.1.le,hu.2.le⟩, Real.norm_eq_abs] at he
  exact he


end TaoTrudgianYang2025
