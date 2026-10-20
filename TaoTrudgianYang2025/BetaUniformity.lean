module
public import Mathlib
public import TaoTrudgianYang2025.ExponentPair

@[expose] public section
open Set Filter Expdb
open scoped ContDiff Topology
noncomputable section
namespace TaoTrudgianYang2025
theorem approximateModelPhase_mono {F : ℝ → ℝ} {σ δ₀ δ₁ : ℝ} {P₀ P₁ : ℕ}
    (h : IsApproximateModelPhaseFunction F σ P₁ δ₀)
    (hP : P₀ ≤ P₁) (hδ : δ₀ ≤ δ₁) :
    IsApproximateModelPhaseFunction F σ P₀ δ₁ := by
  refine ⟨h.1, ?_⟩
  intro p hp u
  exact (h.2 p (hp.trans hP) u).trans hδ

end TaoTrudgianYang2025
