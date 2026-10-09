import GuthMaynard.Improvement.OperatorMixedBound
import GuthMaynard.Improvement.ReflectionSourceRow
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- Actual source mixed trace with every row estimate discharged. The
constant is uniform before scales, source coefficients, density and basis. -/
theorem operator_source_mixed (w : MathCollab.Density.ReflectionCutoff)
    {ε A p : ℝ} (hε : 0 < ε) (hA : 1 ≤ A) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ N L T t₀ : ℝ,
      2 ≤ N → N ≤ L → 0 ≤ T → T ≤ A*N^p →
      ∀ (a : ℕ → ℂ) (μ : ℝ → ℝ),
      (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) → Measurable μ →
      (hi : Integrable μ) → Integrable (fun t => μ t^2) → (∀ t, 0 ≤ μ t) →
      Function.support μ ⊆ Icc t₀ (t₀+T) →
      (∀ t, μ t ≤ ‖boundedPolynomial N a t‖^2) →
      let _ : IsFiniteMeasure (timeMeasure μ) := timeMeasure_finite hi
      ∀ (ι : Type) [Countable ι] (b : HilbertBasis ι ℂ (Lp ℂ 2 (timeMeasure μ))),
      ‖operatorDiagonalTrace b (operatorContinuous (timeMeasure μ) w L*
        (operatorDiscrete (timeMeasure μ) w L (1/2) 5-operatorContinuous (timeMeasure μ) w L)^2)‖ ≤
        C*N^ε*L^2*N*T*(∫ t, μ t^2) := by
  obtain ⟨D,hD,hmix⟩ := operator_mixed_bound w
  obtain ⟨R,hR,hrow⟩ := centered_source_row w hε hA hp
  refine ⟨D*R,mul_pos hD hR,?_⟩
  intro N L T t₀ hN hNL hT hupper a μ ha hm hi h2 h0 hs hμ
  let _ : IsFiniteMeasure (timeMeasure μ) := timeMeasure_finite hi
  dsimp only
  intro ι _ b
  have hL : 1 ≤ L := by linarith
  have hQ : 0 ≤ R*N^ε*L*N*T := by positivity
  have hh := hmix μ hm h0 hi h2 L (R*N^ε*L*N*T) hL hQ
    (fun u hu => hrow N L T t₀ u hN hNL hT hupper (hs hu) a μ ha hm hi h0 hs hμ) ι b
  calc
    _ ≤ D*L*(R*N^ε*L*N*T)*(∫ t, μ t^2) := hh
    _ = _ := by ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.operator_source_mixed
