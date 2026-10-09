import GuthMaynard.Improvement.ReflectionSignedShell
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- Uniform actual density-shell bounds for both signs. The subpower and
logarithmic losses have been absorbed; the actual error mass is retained. -/
theorem reflection_signed_shell_budget (w : MathCollab.Density.ReflectionCutoff)
    {q : ℕ} (hq : 1 < q) {ε A p : ℝ} (hε : 0 < ε) (hA : 1 ≤ A) (hp : 0 < p) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 < C ∧ ∀ N L H u : ℝ,
      2 ≤ N → N ≤ L → 0 < H → H ≤ A*N^p → ∀ a : ℕ → ℂ,
      (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
      ∀ (μ : ℝ → ℝ), Measurable μ → Integrable μ → (∀ t, 0 ≤ μ t) →
      (∀ t, μ t ≤ ‖boundedPolynomial N a t‖^2) →
      ∀ S ∈ ({Icc (u+H) (u+2*H),Icc (u-2*H) (u-H)} : Set (Set ℝ)),
      (∫ t, ‖centeredKernel (fun x => (w x:ℂ)) (1/2) 5 L (t-u)‖^2
        ∂(timeMeasure μ).restrict S) ≤
        C*N^ε*L*N*H+2*(K*L/L^q)^2*((timeMeasure μ).restrict S).real univ := by
  obtain ⟨η,D,hη,hD,hraw⟩ := reflected_band_raw_budget hε hA hp
  obtain ⟨K,B,hK,hB,hshell⟩ := reflection_both_shell_density w hq hη
  let F := (1000/Real.pi^2)*MathCollab.Density.mellinMass w^2*B
  have hF : 0 ≤ F := by dsimp [F]; positivity
  refine ⟨K,1+F*D,hK,by positivity,?_⟩
  intro N L H u hN hNL hH hupper a ha μ hm hi h0 hμ S hS
  have hN0 : 0 < N := by linarith
  have hL : 0 < L := hN0.trans_le hNL
  have hh := hshell N L H u hN0 hL hH a ha μ hm hi h0 hμ S hS
  have hb : (1000/Real.pi^2)*MathCollab.Density.mellinMass w^2*(L^2/H)*
      reflectionShellMeanBudget B η N L H ≤ (F*D)*N^ε*L*N*H := by
    have hr := mul_le_mul_of_nonneg_left (hraw N L H hN hNL hH hupper) hF
    dsimp only [reflectionShellMeanBudget,F] at *
    convert hr using 1 <;> ring
  calc
    _ ≤ (F*D)*N^ε*L*N*H+2*(K*L/L^q)^2*((timeMeasure μ).restrict S).real univ :=
      hh.trans (add_le_add hb le_rfl)
    _ ≤ (1+F*D)*N^ε*L*N*H+2*(K*L/L^q)^2*((timeMeasure μ).restrict S).real univ := by
      apply add_le_add _ le_rfl
      have hn : 0 ≤ N^ε*L*N*H := by positivity
      nlinarith

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.reflection_signed_shell_budget
