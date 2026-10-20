module
public import GuthMaynard.Improvement.SourceDirichletTail
public import GuthMaynard.Improvement.FixedCutoffs
public import GuthMaynard.Improvement.ReflectionNearRow
public import GuthMaynard.Improvement.SeparatedSecondMoment

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- Pointwise domination for the literal truncation, including negative U. -/
theorem source_truncated_domination {β : ℝ → ℝ} {D : ℝ → ℂ}
    (hβ1 : ∀ t, β t ≤ 1) (U t : ℝ) :
    sourceTruncatedDensity β D U t ≤ min (‖D t‖^2) (U^2) := by
  by_cases ht : t ∈ {t | ‖D t‖ ≤ U}
  · have hU : 0 ≤ U := (norm_nonneg _).trans ht
    simp only [sourceTruncatedDensity, indicator_of_mem ht]
    apply le_min
    · nlinarith [sq_nonneg ‖D t‖,hβ1 t]
    · have hh : ‖D t‖^2 ≤ U^2 := pow_le_pow_left₀ (norm_nonneg _) ht 2
      nlinarith [sq_nonneg ‖D t‖,hβ1 t]
  · simp only [sourceTruncatedDensity, indicator_of_notMem ht]
    exact le_min (sq_nonneg _) (sq_nonneg _)

/-- The actual smooth cutoff has support in an interval of length exactly 5T. -/
theorem source_truncated_support {χ : ℝ → ℝ}
    (hs : ∀ t, t ∉ Icc (-2:ℝ) 3 → χ t = 0) {T : ℝ} (hT : 0 < T)
    (D : ℝ → ℂ) (U : ℝ) :
    Function.support (sourceTruncatedDensity (fun t => χ (t/T)) D U) ⊆
      Icc (-2*T) (3*T) := by
  intro t ht
  have hc : χ (t/T) ≠ 0 := by
    intro hz
    apply ht
    by_cases hm : t ∈ {t | ‖D t‖ ≤ U} <;> simp [sourceTruncatedDensity,hm,hz]
  have hh : t/T ∈ Icc (-2:ℝ) 3 := by
    by_contra hn
    exact hc (hs _ hn)
  exact ⟨(le_div_iff₀ hT).mp hh.1,(div_le_iff₀ hT).mp hh.2⟩

/-- All ordinary density hypotheses are discharged for the actual fixed cutoff. -/
theorem fixed_truncated_source_regular {N T : ℝ} (hN : 2 ≤ N) (hT : 0 < T)
    (a : ℕ → ℂ) (ha : ∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) (U : ℝ) :
    let μ := sourceTruncatedDensity (fun t => fixedTimeCutoff (t/T)) (boundedPolynomial N a) U
    Measurable μ ∧ Integrable μ ∧ Integrable (fun t => μ t^2) ∧
      (∀ t, 0 ≤ μ t) ∧ Function.support μ ⊆ Icc (-2*T) (3*T) ∧
      (∀ t, μ t ≤ min (‖boundedPolynomial N a t‖^2) (U^2)) := by
  have hm : Measurable (fun t => fixedTimeCutoff (t/T)) :=
    (fixedTimeCutoff_smooth.continuous.comp (continuous_id.div_const T)).measurable
  have hi : Integrable (fun t => fixedTimeCutoff (t/T)) := by
    simpa [div_eq_mul_inv,mul_comm] using
      (fixedTimeCutoff_smooth.continuous.integrable_of_hasCompactSupport
        fixedTimeCutoff_compact).comp_mul_left' (inv_ne_zero hT.ne')
  obtain ⟨hμm,hμ0,hμi,hμ2,_⟩ := source_density_regular hm hi
    (fun t => (fixedTimeCutoff_bounds (t/T)).1)
    (fun t => (fixedTimeCutoff_bounds (t/T)).2)
    (boundedPolynomial_regular N a).1.measurable
    (boundedPolynomial_norm_le_two_mul hN a ha) U
  refine ⟨hμm,hμi,hμ2,hμ0,?_,?_⟩
  · apply source_truncated_support (χ := fixedTimeCutoff) ?_ hT
    intro t ht
    by_contra hn
    exact ht (fixedTimeCutoff_support (subset_closure hn))
  · exact source_truncated_domination
      (fun t => (fixedTimeCutoff_bounds (t/T)).2) U

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.source_truncated_domination
#print axioms GuthMaynard.Improvement.source_truncated_support
#print axioms GuthMaynard.Improvement.fixed_truncated_source_regular
