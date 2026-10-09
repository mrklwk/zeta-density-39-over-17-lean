import GuthMaynard.Improvement.ReflectionMellinIntegral
import GuthMaynard.Improvement.ReflectedBandMeanValue
import GuthMaynard.Improvement.CubicTimeMeasure
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- Integration on an actual positive shell, retaining the full Mellin
weight and the separate discarded-mode error. -/
theorem reflection_shell_integral (w : MathCollab.Density.ReflectionCutoff)
    {A : ℕ} (hA : 1 < A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ν : Measure ℝ) [IsFiniteMeasure ν] (L H u B : ℝ),
      0 < L → 0 < H → (∀ᵐ t ∂ν, t ∈ Icc (u+H) (u+2*H)) →
      (∀ r : ℝ, (∫ t, ‖MathCollab.Density.bandPhaseSum L H (t-u) r‖^2 ∂ν) ≤ B) →
      (∫ t, ‖centeredKernel (fun x => (w x:ℂ)) (1/2) 5 L (t-u)‖^2 ∂ν) ≤
        (1000/Real.pi^2)*MathCollab.Density.mellinMass w^2*(L^2/H)*B+
          2*(K*L/L^A)^2*ν.real univ := by
  obtain ⟨K,hK,hpoint⟩ := centeredKernel_reflection_shell w hA
  refine ⟨K,hK,?_⟩
  intro ν _ L H u B hL hH hsupport hB
  let F := fun t => ∫ r, ‖MathCollab.Density.mellinLine (fun x => (w x:ℂ)) r‖*
    ‖MathCollab.Density.bandPhaseSum L H (t-u) r‖^2
  have hi : Integrable F ν := (reflection_mellin_integrable w ν L H u).integral_prod_left
  let D := (1000/Real.pi^2)*MathCollab.Density.mellinMass w*(L^2/H)
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (mul_nonneg (by positivity) (MathCollab.Density.mellinMass_nonneg w)) (by positivity)
  have hmajor : Integrable (fun t => D*F t+2*(K*L/L^A)^2) ν :=
    (hi.const_mul D).add (integrable_const _)
  calc
    _ ≤ ∫ t, D*F t+2*(K*L/L^A)^2 ∂ν := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => sq_nonneg _)) hmajor
      filter_upwards [hsupport] with t ht
      exact hpoint L H (t-u) hL hH (by linarith [ht.1]) (by linarith [ht.2])
    _ = D*(∫ t, F t ∂ν)+2*(K*L/L^A)^2*ν.real univ := by
      rw [integral_add (hi.const_mul D) (integrable_const _),integral_const_mul,integral_const]
      simp only [smul_eq_mul]
      ring
    _ ≤ D*(MathCollab.Density.mellinMass w*B)+2*(K*L/L^A)^2*ν.real univ :=
      add_le_add (mul_le_mul_of_nonneg_left (reflection_mellin_integral_bound w ν L H u B hB) hD) le_rfl
    _ = _ := by dsimp [D]; ring

/-- Ordinary density domination discharges the shell's time-energy input. -/
theorem reflection_shell_density_energy {μ : ℝ → ℝ} (hm : Measurable μ)
    (h0 : ∀ t, 0 ≤ μ t) {N L H u r : ℝ} (hN : 0 < N) (hL : 0 < L)
    (a : ℕ → ℂ) (hμ : ∀ t, μ t ≤ ‖boundedPolynomial N a t‖^2) :
    (∫ t, ‖MathCollab.Density.bandPhaseSum L H (t-u) r‖^2
      ∂(timeMeasure μ).restrict (Icc (u+H) (u+2*H))) ≤
      ∫ t in Icc (u+H) (u+2*H), ‖boundedPolynomial N a t‖^2*
        ‖MathCollab.Density.bandPhaseSum L H (t-u) r‖^2 := by
  rw [timeMeasure,restrict_withDensity measurableSet_Icc,
    integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (h0 _),smul_eq_mul]
  apply integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun t => mul_nonneg (h0 t) (sq_nonneg _)))
    (reflected_band_product_integrable hN hL H r u a)
  filter_upwards with t
  exact mul_le_mul_of_nonneg_right (hμ t) (sq_nonneg _)

/-- Explicit scalar mean-value budget; packaging keeps the endpoint readable. -/
def reflectionShellMeanBudget (C η N L H : ℝ) : ℝ :=
  let X := reflectedBandLength L H
  let Y := ⌊2*N⌋₊*X
  C*(H+4*(Y:ℝ)*(1+Real.log Y))*(1+2*N*X)^η*(N+1)*X

/-- Actual positive-shell row estimate: only ordinary domination by the
source polynomial remains, with all reflected mean-value inputs derived. -/
theorem reflection_shell_density (w : MathCollab.Density.ReflectionCutoff)
    {A : ℕ} (hA : 1 < A) {η : ℝ} (hη : 0 < η) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 < C ∧ ∀ N L H u : ℝ,
      0 < N → 0 < L → 0 < H → ∀ a : ℕ → ℂ,
      (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
      ∀ (μ : ℝ → ℝ), Measurable μ → Integrable μ → (∀ t, 0 ≤ μ t) →
      (∀ t, μ t ≤ ‖boundedPolynomial N a t‖^2) →
      (∫ t, ‖centeredKernel (fun x => (w x:ℂ)) (1/2) 5 L (t-u)‖^2
        ∂(timeMeasure μ).restrict (Icc (u+H) (u+2*H))) ≤
        (1000/Real.pi^2)*MathCollab.Density.mellinMass w^2*(L^2/H)*
          reflectionShellMeanBudget C η N L H+
          2*(K*L/L^A)^2*((timeMeasure μ).restrict (Icc (u+H) (u+2*H))).real univ := by
  obtain ⟨K,hK,hshell⟩ := reflection_shell_integral w hA
  obtain ⟨C,hC,hmean⟩ := reflected_band_mean_value hη
  refine ⟨K,C,hK,hC,?_⟩
  intro N L H u hN hL hH a ha μ hm hi h0 hμ
  let := timeMeasure_finite hi
  apply hshell ((timeMeasure μ).restrict (Icc (u+H) (u+2*H))) L H u _ hL hH
    (ae_restrict_mem measurableSet_Icc)
  intro r
  exact (reflection_shell_density_energy hm h0 hN hL a hμ).trans
    (hmean N L H r u hN hL hH.le a ha)

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.reflection_shell_integral

#print axioms GuthMaynard.Improvement.reflection_shell_density_energy
#print axioms GuthMaynard.Improvement.reflection_shell_density
