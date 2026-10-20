module
public import IntervalExcessTransfer

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger

theorem criticalExcess_compact_prefix {B : ℝ} (hB : 0 ≤ B) :
    ∃ M : ℝ, ∀ v : ℝ, M ≤ v → (∫ t in 0..B,criticalExcess v t)=0 := by
  obtain ⟨M,hM⟩ := isCompact_Icc.bddAbove_image
    continuous_zetaMomentCriticalNorm.continuousOn
  refine ⟨M,?_⟩
  intro v hv
  have hz : Set.EqOn (criticalExcess v) (fun _ => (0:ℝ)) (Set.uIcc 0 B) := by
    intro t ht
    rw [uIcc_of_le hB] at ht
    have hb : zetaMomentCriticalNorm t ≤ M := hM ⟨t,ht,rfl⟩
    unfold criticalExcess
    exact max_eq_right (by linarith)
  rw [intervalIntegral.integral_congr hz]
  simp
end Montgomery.RationalMoment.RightDetector
