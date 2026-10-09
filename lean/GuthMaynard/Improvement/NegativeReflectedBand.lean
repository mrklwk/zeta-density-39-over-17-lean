module
public import GuthMaynard.Improvement.ReflectedBandMeanValue

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Finset
open scoped ComplexConjugate
namespace GuthMaynard.Improvement

/-- Literal coefficient conjugation reverses source time, without changing indices. -/
theorem boundedPolynomial_conjugate_time (N : ℝ) (a : ℕ → ℂ) (t : ℝ) :
    conj (boundedPolynomial N a t) = boundedPolynomial N (fun n => conj (a n)) (-t) := by
  unfold boundedPolynomial
  simp only [map_sum,map_mul]
  apply sum_congr rfl
  intro n _
  rw [← Complex.exp_conj]
  congr 2
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]
  push_cast
  ring

theorem boundedPolynomial_norm_reverse (N : ℝ) (a : ℕ → ℂ) (t : ℝ) :
    ‖boundedPolynomial N a t‖ = ‖boundedPolynomial N (fun n => conj (a n)) (-t)‖ := by
  rw [← boundedPolynomial_conjugate_time,RCLike.norm_conj]

/-- The negative-shell integrand is genuinely integrable; all factors are finite continuous sums. -/
theorem negative_reflected_band_integrable (N L H r u : ℝ) (a : ℕ → ℂ) :
    IntegrableOn (fun t => ‖boundedPolynomial N a t‖^2*
      ‖MathCollab.Density.bandPhaseSum L H (u-t) r‖^2) (Set.Icc (u-2*H) (u-H)) := by
  apply ContinuousOn.integrableOn_Icc
  apply Continuous.continuousOn
  unfold boundedPolynomial MathCollab.Density.bandPhaseSum MathCollab.Density.dirichletPhase
  fun_prop

/-- Actual Lebesgue negation takes the negative shell to the checked positive shell,
with the source coefficients conjugated. -/
theorem negative_reflected_band_integral (N L H r u : ℝ) (hH : 0 ≤ H) (a : ℕ → ℂ) :
    (∫ t in Set.Icc (u-2*H) (u-H), ‖boundedPolynomial N a t‖^2*
      ‖MathCollab.Density.bandPhaseSum L H (u-t) r‖^2) =
    ∫ t in Set.Icc (-u+H) (-u+2*H),
      ‖boundedPolynomial N (fun n => conj (a n)) t‖^2*
        ‖MathCollab.Density.bandPhaseSum L H (t-(-u)) r‖^2 := by
  let f := fun t => ‖boundedPolynomial N (fun n => conj (a n)) t‖^2*
    ‖MathCollab.Density.bandPhaseSum L H (t-(-u)) r‖^2
  have he (t : ℝ) : ‖boundedPolynomial N a t‖^2*
      ‖MathCollab.Density.bandPhaseSum L H (u-t) r‖^2 = f (-t) := by
    dsimp [f]
    rw [boundedPolynomial_norm_reverse,show u-t=-t-(-u) by ring]
  simp_rw [he]
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (show u-2*H ≤ u-H by linarith),
    intervalIntegral.integral_comp_neg]
  rw [show -(u-H)=-u+H by ring,show -(u-2*H)=-u+2*H by ring,
    intervalIntegral.integral_of_le (show -u+H ≤ -u+2*H by linarith),← integral_Icc_eq_integral_Ioc]

/-- Uniform negative-shell mean value reuses the actual positive-shell theorem.
The identical constant works for all translates and Mellin parameters. -/
theorem negative_reflected_band_mean_value {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ N L H r u : ℝ, 0 < N → 0 < L → 0 ≤ H →
      ∀ a : ℕ → ℂ, (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
      let X := reflectedBandLength L H
      let Y := ⌊2*N⌋₊*X
      (∫ t in Set.Icc (u-2*H) (u-H), ‖boundedPolynomial N a t‖^2*
        ‖MathCollab.Density.bandPhaseSum L H (u-t) r‖^2) ≤
        C*(H+4*(Y:ℝ)*(1+Real.log Y))*(1+2*N*X)^η*(N+1)*X := by
  obtain ⟨C,hC,h⟩ := reflected_band_mean_value hη
  refine ⟨C,hC,?_⟩
  intro N L H r u hN hL hH a ha
  dsimp only
  rw [negative_reflected_band_integral N L H r u hH a]
  exact h N L H r (-u) hN hL hH (fun n => conj (a n))
    (fun n hn => by simpa only [RCLike.norm_conj] using ha n hn)

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.boundedPolynomial_conjugate_time
#print axioms GuthMaynard.Improvement.boundedPolynomial_norm_reverse
#print axioms GuthMaynard.Improvement.negative_reflected_band_integrable
#print axioms GuthMaynard.Improvement.negative_reflected_band_integral
#print axioms GuthMaynard.Improvement.negative_reflected_band_mean_value
