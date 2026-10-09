import GuthMaynard.Improvement.ShortTypeIICount
import GuthMaynard.Improvement.WeakShortMoment
set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Set Filter MathCollab.Density
open scoped Topology
namespace GuthMaynard.Improvement

/-- The ordinary fourth moment and a crude mollifier bound suffice, with a fixed
1/25 loss. Constants precede sigma, height and every finite family. -/
theorem weak_short_typeII_count
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C H₀ : ℝ, 0 < C ∧ 2 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H → ∀ σ : ℝ,
      ∀ (W : Finset ℝ) (ρ : ℝ → ℂ), 9/13 ≤ σ →
      oneSeparated W → (∀ u ∈ W,u ∈ Icc H (2*H)) →
      (∀ u ∈ W,(ρ u).im=u ∧ σ ≤ (ρ u).re ∧ (ρ u).re ≤ 1) →
      (∀ u ∈ W,(1/3:ℝ) ≤ ‖detectorIntegral (ρ u) (2*H^((1:ℝ)/100)) (H^((1:ℝ)/2))‖) →
      (W.card:ℝ) ≤ C*H^(2-2*σ+1/25+ε) := by
  obtain ⟨A,hA,ha⟩ := short_typeII_count_by_moment
  obtain ⟨H₁,hH₁⟩ := eventually_atTop.mp ha
  obtain ⟨B,H₂,hB,hH₂,hb⟩ := weak_short_moment hε
  refine ⟨A*B,max 2 (max H₁ H₂),by positivity,le_max_left _ _,?_⟩
  intro H hH σ W ρ hσ hsep hw hρ hlarge
  have hH1 : H₁ ≤ H := (le_max_left _ _).trans ((le_max_right _ _).trans hH)
  have hH2 : H₂ ≤ H := (le_max_right _ _).trans ((le_max_right _ _).trans hH)
  have hn : 0 < H := by linarith [hH₂]
  have hc := hH₁ H hH1 σ W ρ hσ hsep hw hρ hlarge
  have hm := hb H hH2
  change (∫ t in Icc (H/2) (3*H),(shortTwistedNorm H t)^4) ≤ B*H^(1+1/25+ε) at hm
  calc
    _ ≤ A*H^(1-2*σ)*(B*H^(1+1/25+ε)) := hc.trans (mul_le_mul_of_nonneg_left hm (by positivity))
    _ = (A*B)*(H^(1-2*σ)*H^(1+1/25+ε)) := by ring
    _ = _ := by rw [← Real.rpow_add hn]; congr 2; ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.weak_short_typeII_count
