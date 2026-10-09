import GuthMaynard.Improvement.SourceQuarticKernel
import GuthMaynard.Improvement.ReflectionNearRow
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- Actual finite polynomial-weighted L1 moments of the fixed kernel. -/
theorem source_quartic_weight_moment (q : ℕ) :
    Integrable (fun s => |s|^q*sourceQuarticWeight s) := by
  simpa only [Real.norm_eq_abs,sourceQuarticWeight] using
    sourceReproducingKernel.integrable_pow_mul volume q

/-- Arbitrary rapid integral-tail decay, from the actual Schwartz moments. -/
theorem source_quartic_weight_tail (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R →
      (∫ s in {s : ℝ | R < |s|}, sourceQuarticWeight s) ≤ C/R^q := by
  let M := ∫ s, |s|^q*sourceQuarticWeight s
  have hM : 0 ≤ M := integral_nonneg (fun s => mul_nonneg (pow_nonneg (abs_nonneg _) _) (norm_nonneg _))
  refine ⟨M+1,by positivity,?_⟩
  intro R hR
  have hi : Integrable sourceQuarticWeight := sourceReproducingKernel.integrable.norm
  have hm : MeasurableSet {s : ℝ | R < |s|} := by measurability
  have hpoint (s : ℝ) (hs : s ∈ {s : ℝ | R < |s|}) :
      sourceQuarticWeight s ≤ (|s|^q*sourceQuarticWeight s)/R^q := by
    apply (le_div_iff₀ (pow_pos hR q)).mpr
    have hh := pow_le_pow_left₀ hR.le (le_of_lt hs) q
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hh (show 0 ≤ sourceQuarticWeight s from norm_nonneg _)
  calc
    _ ≤ ∫ s in {s : ℝ | R < |s|}, (|s|^q*sourceQuarticWeight s)/R^q :=
      setIntegral_mono_on hi.integrableOn ((source_quartic_weight_moment q).div_const _).integrableOn hm hpoint
    _ ≤ ∫ s, (|s|^q*sourceQuarticWeight s)/R^q :=
      setIntegral_le_integral ((source_quartic_weight_moment q).div_const _)
        (Filter.Eventually.of_forall (fun s => by unfold sourceQuarticWeight; positivity))
    _ = M/R^q := integral_div _ _
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (pow_nonneg hR.le q)

/-- Actual quartic polynomial tails; coefficient bounds are used only to
majorize the finite source pointwise, never to assert global L4. -/
theorem source_quartic_polynomial_tail (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N R w : ℝ, 2 ≤ N → 0 < R →
      ∀ a : ℕ → ℂ, (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
      (∫ t in {t : ℝ | R < |t-w|}, sourceQuarticWeight (t-w)*‖boundedPolynomial N a t‖^4) ≤
        C*N^4/R^q := by
  obtain ⟨C,hC,h⟩ := source_quartic_weight_tail q
  refine ⟨16*C,by positivity,?_⟩
  intro N R w hN hR a ha
  have hi : Integrable (fun t => sourceQuarticWeight (t-w)) :=
    (sourceReproducingKernel.integrable.comp_sub_right w).norm
  have hS : MeasurableSet {t : ℝ | R < |t-w|} := by measurability
  have ht : (∫ t in {t : ℝ | R < |t-w|}, sourceQuarticWeight (t-w)) =
      ∫ s in {s : ℝ | R < |s|}, sourceQuarticWeight s := by
    rw [← integral_indicator hS,← integral_indicator (show MeasurableSet {s : ℝ | R < |s|} by measurability)]
    exact integral_sub_right_eq_self (μ := volume) ({s : ℝ | R < |s|}.indicator sourceQuarticWeight) w
  calc
    _ ≤ ∫ t in {t : ℝ | R < |t-w|}, sourceQuarticWeight (t-w)*(16*N^4) := by
      apply setIntegral_mono_on (source_quartic_weighted_integrable N a w 4).integrableOn
        (hi.mul_const _).integrableOn hS
      intro t _
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have hh := pow_le_pow_left₀ (norm_nonneg _) (boundedPolynomial_norm_le_two_mul hN a ha t) 4
      convert hh using 1; ring
    _ = (∫ t in {t : ℝ | R < |t-w|}, sourceQuarticWeight (t-w))*(16*N^4) := integral_mul_const _ _
    _ ≤ (C/R^q)*(16*N^4) := by rw [ht]; exact mul_le_mul_of_nonneg_right (h R hR) (by positivity)
    _ = _ := by ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.source_quartic_weight_moment
#print axioms GuthMaynard.Improvement.source_quartic_weight_tail
#print axioms GuthMaynard.Improvement.source_quartic_polynomial_tail
