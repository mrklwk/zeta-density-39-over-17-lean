module
public import GuthMaynard.Improvement.SpectralMassAssembly
public import GuthMaynard.Improvement.OperatorSourceMixed
public import GuthMaynard.Improvement.FixedCutoffs

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- Actual spectral mass estimate with no spectral, amplifier, Schur, row
or mixed-trace premise. The remaining cubic is the literal kernel integral;
all raw subpower factors are displayed explicitly. -/
theorem source_spectral_raw (w : MathCollab.Density.ComparisonCutoff)
    {η ε A p : ℝ} (hη : 0 < η) (hε : 0 < ε) (hA : 1 ≤ A) (hp : 0 < p) :
    ∃ P D R : ℝ, 0 < P ∧ 0 < D ∧ 0 < R ∧ ∀ N L T t₀ : ℝ,
      2 ≤ N → N ≤ L → 0 ≤ T → T ≤ A*N^p →
      ∀ (a : ℕ → ℂ) (μ : ℝ → ℝ),
      (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) → Measurable μ → Integrable μ →
      Integrable (fun t => μ t^2) → (∀ t, 0 ≤ μ t) →
      Function.support μ ⊆ Icc t₀ (t₀+T) → ∀ B : ℝ, 0 ≤ B →
      (∀ t, μ t ≤ min (‖boundedPolynomial N a t‖^2) B) →
      (∫ t, μ t^2)^3 ≤ 4*(P*(1+L)^η*(N+1))^3*
        ((D*L*B)^3+(2*N/L)*
          (‖kernelCubic (timeMeasure μ)
            (centeredKernel (fun x => ((w x^2:ℝ):ℂ)) (1/2) 5 L)‖+
              R*N^ε*L^2*N*T*(∫ t, μ t^2))) := by
  have hs : ∀ x, x ∉ Icc (1/2:ℝ) 5 → w x=0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hh => hx (w.support hh))
  obtain ⟨P,D,hP,hD,hraw⟩ := actual_spectral_mass_bound w.smooth
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)≤1)
    (by norm_num : (4:ℝ)≤5) w.one_on hs hη
  obtain ⟨R,hR,hmix⟩ := operator_source_mixed (squareReflectionCutoff w.toReflectionCutoff)
    hε hA hp
  refine ⟨P,D,R,hP,hD,hR,?_⟩
  intro N L T t₀ hN hNL hT hupper a μ ha hm hi h2 h0 hsupport B hB hμ
  let _ : IsFiniteMeasure (timeMeasure μ) := timeMeasure_finite hi
  obtain ⟨S,hS,⟨b⟩⟩ := operator_countable_hilbertBasis (timeMeasure μ)
  let : Countable S := hS
  have hμD (t : ℝ) : μ t ≤ ‖boundedPolynomial N a t‖^2 :=
    (hμ t).trans (min_le_left _ _)
  have hmixed := hmix N L T t₀ hN hNL hT hupper a μ ha hm hi h2 h0 hsupport hμD S b
  have hreal := Complex.re_le_norm
    (operatorDiagonalTrace b
      (operatorContinuous (timeMeasure μ) (fun x => w x^2) L *
        (operatorDiscrete (timeMeasure μ) (fun x => w x^2) L (1/2) 5-
          operatorContinuous (timeMeasure μ) (fun x => w x^2) L)^2))
  exact (hraw N L (by linarith) hNL a ha μ hm hi h2 h0 B hB hμ S b _
    (hreal.trans hmixed)).2

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.source_spectral_raw
