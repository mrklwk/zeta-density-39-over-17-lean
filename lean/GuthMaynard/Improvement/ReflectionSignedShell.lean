import GuthMaynard.Improvement.ReflectionShellIntegral
import GuthMaynard.Improvement.NegativeReflectedBand
import GuthMaynard.Improvement.ReflectedBandBudget
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate
namespace GuthMaynard.Improvement

/-- Actual density-measure negation, including the interval endpoints. -/
theorem reflection_density_negation {μ : ℝ → ℝ} (hm : Measurable μ)
    (h0 : ∀ t, 0 ≤ μ t) (F : ℝ → ℝ) {H : ℝ} (hH : 0 ≤ H) (u : ℝ) :
    (∫ t, F t ∂(timeMeasure μ).restrict (Icc (u-2*H) (u-H))) =
      ∫ t, F (-t) ∂(timeMeasure (fun t => μ (-t))).restrict (Icc (-u+H) (-u+2*H)) := by
  have hm' : Measurable (fun t => μ (-t)) := hm.comp measurable_neg
  simp_rw [timeMeasure,restrict_withDensity measurableSet_Icc,
    integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),
    integral_withDensity_eq_integral_toReal_smul hm'.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),
    ENNReal.toReal_ofReal (h0 _),smul_eq_mul]
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (show u-2*H ≤ u-H by linarith)]
  have he : (fun t => μ t*F t) = fun t => (fun s => μ (-s)*F (-s)) (-t) := by funext t; simp
  rw [he,intervalIntegral.integral_comp_neg (f := fun s => μ (-s)*F (-s))]
  rw [show -(u-H)=-u+H by ring,show -(u-2*H)=-u+2*H by ring,
    intervalIntegral.integral_of_le (show -u+H ≤ -u+2*H by linarith),← integral_Icc_eq_integral_Ioc]

/-- Negation preserves the exact shell density mass. -/
theorem reflection_density_mass_negation {μ : ℝ → ℝ} (hm : Measurable μ)
    (h0 : ∀ t, 0 ≤ μ t) {H : ℝ} (hH : 0 ≤ H) (u : ℝ) :
    ((timeMeasure μ).restrict (Icc (u-2*H) (u-H))).real univ =
      ((timeMeasure (fun t => μ (-t))).restrict (Icc (-u+H) (-u+2*H))).real univ := by
  have he := reflection_density_negation hm h0 (fun _ => 1) hH u
  simpa only [integral_const,smul_eq_mul,mul_one] using he

/-- A negative shell is the same positive shell for the reversed density.
Only norm evenness of the actual centered kernel is used. -/
theorem reflection_kernel_row_negation (w : MathCollab.Density.ReflectionCutoff)
    {μ : ℝ → ℝ} (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t)
    {L H : ℝ} (hL : 0 < L) (hH : 0 ≤ H) (u : ℝ) :
    (∫ t, ‖centeredKernel (fun x => (w x:ℂ)) (1/2) 5 L (t-u)‖^2
      ∂(timeMeasure μ).restrict (Icc (u-2*H) (u-H))) =
    ∫ t, ‖centeredKernel (fun x => (w x:ℂ)) (1/2) 5 L (t-(-u))‖^2
      ∂(timeMeasure (fun t => μ (-t))).restrict (Icc (-u+H) (-u+2*H)) := by
  rw [reflection_density_negation hm h0 _ hH u]
  apply integral_congr_ae
  filter_upwards with t
  rw [show -t-u=-(t-(-u)) by ring,centeredKernel_norm_neg w hL]

/-- Both actual density shells share the same constants and exact error
mass. The reflected mean-value input is fully discharged. -/
theorem reflection_both_shell_density (w : MathCollab.Density.ReflectionCutoff)
    {q : ℕ} (hq : 1 < q) {η : ℝ} (hη : 0 < η) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 < C ∧ ∀ N L H u : ℝ,
      0 < N → 0 < L → 0 < H → ∀ a : ℕ → ℂ,
      (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
      ∀ (μ : ℝ → ℝ), Measurable μ → Integrable μ → (∀ t, 0 ≤ μ t) →
      (∀ t, μ t ≤ ‖boundedPolynomial N a t‖^2) →
      ∀ S ∈ ({Icc (u+H) (u+2*H),Icc (u-2*H) (u-H)} : Set (Set ℝ)),
      (∫ t, ‖centeredKernel (fun x => (w x:ℂ)) (1/2) 5 L (t-u)‖^2
        ∂(timeMeasure μ).restrict S) ≤
        (1000/Real.pi^2)*MathCollab.Density.mellinMass w^2*(L^2/H)*
          reflectionShellMeanBudget C η N L H+
          2*(K*L/L^q)^2*((timeMeasure μ).restrict S).real univ := by
  obtain ⟨K,C,hK,hC,h⟩ := reflection_shell_density w hq hη
  refine ⟨K,C,hK,hC,?_⟩
  intro N L H u hN hL hH a ha μ hm hi h0 hμ S hS
  rcases hS with rfl | hS
  · exact h N L H u hN hL hH a ha μ hm hi h0 hμ
  have he : S = Icc (u-2*H) (u-H) := hS
  subst S
  have hm' : Measurable (fun t => μ (-t)) := hm.comp measurable_neg
  have hi' : Integrable (fun t => μ (-t)) := by
    simpa using hi.comp_mul_left' (by norm_num : (-1:ℝ) ≠ 0)
  have hμ' (t : ℝ) : μ (-t) ≤ ‖boundedPolynomial N (fun n => conj (a n)) t‖^2 := by
    have hh := hμ (-t)
    rw [boundedPolynomial_norm_reverse N a (-t),neg_neg] at hh
    exact hh
  have hh := h N L H (-u) hN hL hH (fun n => conj (a n))
    (fun n hn => by simpa only [RCLike.norm_conj] using ha n hn)
    (fun t => μ (-t)) hm' hi' (fun t => h0 (-t)) hμ'
  rw [reflection_kernel_row_negation w hm h0 hL hH.le u,
    reflection_density_mass_negation hm h0 hH.le u]
  exact hh

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.reflection_density_negation
#print axioms GuthMaynard.Improvement.reflection_density_mass_negation
#print axioms GuthMaynard.Improvement.reflection_kernel_row_negation
#print axioms GuthMaynard.Improvement.reflection_both_shell_density
