module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaSlopeInverse
public import TaoTrudgianYang2025.BetaClosedSlope
public import Mathlib

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set Filter Expdb
open scoped Topology ContDiff
namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth
theorem modelPhaseClosedSlope_drop {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {u v : ℝ} (hu : u ∈ Icc (1 : ℝ) 2) (hv : v ∈ Icc (1 : ℝ) 2)
    (huv : u ≤ v) :
    modelPhaseCurvatureLower σ*(v-u) ≤ modelPhaseClosedSlope F u-modelPhaseClosedSlope F v := by
  have hd : DifferentiableOn ℝ (modelPhaseClosedSlope F) (interior (Icc (1 : ℝ) 2)) := by
    intro x hx
    have hx' : x ∈ Ioo (1 : ℝ) 2 := by simpa only [interior_Icc] using hx
    exact (((approximateModelPhase_deriv_contDiffAt hF hx').differentiableAt (by simp)).congr_of_eventuallyEq (modelPhaseClosedSlope_eventuallyEq_deriv hx')).differentiableWithinAt
  have hb : ∀ x ∈ interior (Icc (1 : ℝ) 2),
      deriv (modelPhaseClosedSlope F) x ≤ -modelPhaseCurvatureLower σ := by
    intro x hx
    have hx' : x ∈ Ioo (1 : ℝ) 2 := by simpa only [interior_Icc] using hx
    rw [(modelPhaseClosedSlope_eventuallyEq_deriv hx').deriv_eq]
    have h := (approximateModelPhase_curvature_deriv_bounds hσ hδ hF hx').1
    linarith
  have h := (convex_Icc (1 : ℝ) 2).image_sub_le_mul_sub_of_deriv_le
    (modelPhaseClosedSlope_continuousOn hF) hd hb u hu v hv huv
  linarith

theorem modelPhaseClosedSlope_strictAntiOn {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) :
    StrictAntiOn (modelPhaseClosedSlope F) (Icc (1 : ℝ) 2) := by
  intro u hu v hv huv
  have hd := modelPhaseClosedSlope_drop hσ hδ hF hu hv huv.le
  have hp := mul_pos (modelPhaseCurvatureLower_pos hσ) (sub_pos.mpr huv)
  linarith

theorem modelPhaseSlopeRange_eq_endpoint_Ioo {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) :
    modelPhaseSlopeRange F = Ioo (modelPhaseClosedSlope F 2) (modelPhaseClosedSlope F 1) := by
  have hm := modelPhaseClosedSlope_strictAntiOn hσ hδ hF
  ext v
  constructor
  · rintro ⟨u,hu,rfl⟩
    rw [← modelPhaseClosedSlope_eq_deriv hu]
    exact ⟨hm ⟨hu.1.le,hu.2.le⟩ (by norm_num) hu.2,
      hm (by norm_num) ⟨hu.1.le,hu.2.le⟩ hu.1⟩
  · intro hv
    obtain ⟨u,hu,he⟩ := intermediate_value_Ioo' (by norm_num : (1 : ℝ) ≤ 2)
      (modelPhaseClosedSlope_continuousOn hF) hv
    exact ⟨u,hu,(modelPhaseClosedSlope_eq_deriv hu).symm.trans he⟩

theorem modelPhaseClosedSlope_deriv_bounds {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseClosedSlope F 2 ≤ deriv F u ∧ deriv F u ≤ modelPhaseClosedSlope F 1 := by
  have hm := (modelPhaseClosedSlope_strictAntiOn hσ hδ hF).antitoneOn
  rw [← modelPhaseClosedSlope_eq_deriv hu]
  exact ⟨hm ⟨hu.1.le,hu.2.le⟩ (by norm_num) hu.2.le,
    hm (by norm_num) ⟨hu.1.le,hu.2.le⟩ hu.1.le⟩


end TaoTrudgianYang2025
