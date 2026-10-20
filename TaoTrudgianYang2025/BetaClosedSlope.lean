module
public import Mathlib
public import TaoTrudgianYang2025.ExponentPair

@[expose] public section
open Set Filter Expdb
open scoped ContDiff Topology
noncomputable section
namespace TaoTrudgianYang2025
def modelPhaseClosedSlope (F : ℝ → ℝ) : ℝ → ℝ :=
  derivWithin F phaseInterval

theorem modelPhaseClosedSlope_eq_deriv {F : ℝ → ℝ} {u : ℝ}
    (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseClosedSlope F u = deriv F u :=
  derivWithin_of_mem_nhds (Icc_mem_nhds hu.1 hu.2)

theorem modelPhaseClosedSlope_eventuallyEq_deriv {F : ℝ → ℝ} {u : ℝ}
    (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseClosedSlope F =ᶠ[𝓝 u] deriv F := by
  filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
  exact modelPhaseClosedSlope_eq_deriv hv

theorem modelPhaseClosedSlope_continuousOn {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ) :
    ContinuousOn (modelPhaseClosedSlope F) (Icc (1 : ℝ) 2) :=
  hF.1.continuousOn_derivWithin uniqueDiffOn_phaseInterval (by simp)

theorem modelPhaseClosedSlope_model_error {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    {u : ℝ} (hu : u ∈ phaseInterval) :
    |modelPhaseClosedSlope F u-u^(-σ)| ≤ δ := by
  have he := hF.2 0 (Nat.zero_le P) ⟨u,hu⟩
  change ‖iteratedDerivWithin 1 F phaseInterval u-modelPhase σ u‖ ≤ δ at he
  simpa only [iteratedDerivWithin_one,modelPhaseClosedSlope,modelPhase,Real.norm_eq_abs] using he

end TaoTrudgianYang2025
