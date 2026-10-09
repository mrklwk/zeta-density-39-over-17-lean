import GuthMaynard.Improvement.OperatorDensityVector
import GuthMaynard.Improvement.LogMask
set_option autoImplicit false
noncomputable section
open MeasureTheory InnerProductSpace Set
open scoped InnerProductSpace FourierTransform Topology
namespace GuthMaynard.Improvement

/-- Actual logarithmic frequency substitution and ordinary Plancherel. -/
theorem operator_mellin_plancherel_weight {a : ℝ → ℝ} (ha : Measurable a)
    (ha0 : ∀ x, 0 ≤ a x) {W : ℝ} (hW : 0 ≤ W)
    (hb : ∀ x, 0 < x → x*a x ≤ W) (hz : ∀ x, x ≤ 0 → a x=0)
    {g : ℝ → ℂ} (h1 : Integrable g) (h2 : MemLp g 2) :
    Integrable (fun x => a x*‖𝓕 g (mellinFrequency x)‖^2) ∧
      (∫ x, a x*‖𝓕 g (mellinFrequency x)‖^2) ≤
        (2*Real.pi*W)*(∫ t, ‖g t‖^2) := by
  have hf2 := ordinary_fourier_memLp h1 h2
  have hfi := (memLp_two_iff_integrable_sq_norm hf2.aestronglyMeasurable).mp hf2
  have hscale := hfi.comp_div (by positivity : 2*Real.pi ≠ 0)
  have hh := log_weight_integral ha ha0 hW hb hz hscale (fun _ => sq_nonneg _)
  refine ⟨hh.1, ?_⟩
  calc
    _ ≤ W*(∫ u, ‖𝓕 g (u/(2*Real.pi))‖^2) := hh.2
    _ = (2*Real.pi*W)*(∫ t, ‖g t‖^2) := by
      rw [Measure.integral_comp_div (fun ξ => ‖𝓕 g ξ‖^2) (2*Real.pi), abs_of_pos (by positivity : 0 < 2*Real.pi),
        smul_eq_mul, ordinary_fourier_integral_sq h1 h2]
      ring

/-- The literal C quadratic form is a nonnegative weighted frequency energy. -/
theorem operator_continuous_quadratic {ν : Measure ℝ} [IsFiniteMeasure ν]
    {a : ℝ → ℝ} (hi : Integrable a) (L : ℝ) (f : Lp ℂ 2 ν) :
    (inner ℂ f (operatorContinuous ν a L f)).re =
      L*(∫ x, a x*‖inner ℂ (operatorPhase ν (mellinFrequency x)) f‖^2) := by
  rw [operator_continuous_pairing ν hi L]
  have he (x : ℝ) : ((L*a x:ℝ):ℂ)*inner ℂ f (operatorPhase ν (mellinFrequency x))*
      inner ℂ (operatorPhase ν (mellinFrequency x)) f =
      ((L*(a x*‖inner ℂ (operatorPhase ν (mellinFrequency x)) f‖^2):ℝ):ℂ) := by
    rw [mul_assoc, ← inner_conj_symm f (operatorPhase ν (mellinFrequency x)), Complex.conj_mul']
    push_cast
    ring
  simp_rw [he]
  rw [integral_complex_ofReal, Complex.ofReal_re, integral_const_mul]

/-- Positive quadratic-form control implies the actual operator norm bound. -/
theorem operator_positive_norm_of_quadratic {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (T : E →L[ℂ] E) (hT : T.IsPositive)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ f, (inner ℂ f (T f)).re ≤ M*‖f‖^2) :
    ‖T‖ ≤ M := by
  rw [T.norm_eq_iSup_rayleighQuotient hT.isSymmetric]
  apply ciSup_le
  intro f
  by_cases hf : f=0
  · subst f
    simpa using hM
  have hf2 : 0 < ‖f‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hf)
  have he : T.reApplyInnerSelf f = (inner ℂ f (T f)).re := by
    change RCLike.re (inner ℂ (T f) f) = _
    rw [hT.inner_left_eq_inner_right, RCLike.re_eq_complex_re]
  change |T.reApplyInnerSelf f / ‖f‖^2| ≤ M
  have hn : 0 ≤ (inner ℂ f (T f)).re := by
    simpa only [RCLike.re_eq_complex_re] using hT.re_inner_nonneg_right f
  rw [he, abs_of_nonneg (div_nonneg hn hf2.le)]
  exact (div_le_iff₀ hf2).mpr (hb f)

/-- Actual Schur bound: the constant uses only the weighted fixed cutoff,
not the total density mass or its support length. -/
theorem operator_continuous_schur {μ : ℝ → ℝ} [IsFiniteMeasure (timeMeasure μ)]
    (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t) {B : ℝ}
    (hB : 0 ≤ B) (hb : ∀ t, μ t ≤ B)
    {a : ℝ → ℝ} (ha : Measurable a) (hi : Integrable a) (ha0 : ∀ x, 0 ≤ a x)
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 ≤ L)
    (haw : ∀ x, 0 < x → x*a x ≤ W) (haz : ∀ x, x ≤ 0 → a x=0) :
    ‖operatorContinuous (timeMeasure μ) a L‖ ≤ (2*Real.pi*W)*L*B := by
  apply operator_positive_norm_of_quadratic _
    (operator_continuous_positive (timeMeasure μ) hi ha0 hL) (by positivity)
  intro f
  have hg1 := operator_density_vector_integrable hm h0 f
  obtain ⟨hg2,hgn⟩ := operator_density_vector_L2 hm h0 hB hb f
  have hfreq := operator_mellin_plancherel_weight ha ha0 hW haw haz hg1 hg2
  rw [operator_continuous_quadratic hi L]
  simp_rw [operator_density_phase_pairing hm h0]
  calc
    _ ≤ L*((2*Real.pi*W)*(∫ t, ‖(μ t:ℂ)*f t‖^2)) :=
      mul_le_mul_of_nonneg_left hfreq.2 hL
    _ ≤ L*((2*Real.pi*W)*(B*‖f‖^2)) := by gcongr
    _ = _ := by ring

/-- Fixed compact nonnegative cutoff gives the uniform L B correction bound. -/
theorem operator_continuous_compact_schur {μ : ℝ → ℝ}
    [IsFiniteMeasure (timeMeasure μ)] (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ t, μ t ≤ B)
    {a : ℝ → ℝ} (ha : Measurable a) (hi : Integrable a) (ha0 : ∀ x, 0 ≤ a x)
    {l u A L : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (haA : ∀ x, a x ≤ A) (hs : ∀ x, x ∉ Icc l u → a x=0) :
    ‖operatorContinuous (timeMeasure μ) a L‖ ≤ (2*Real.pi*u*A)*L*B := by
  have hu : 0 ≤ u := hl.le.trans hlu
  have hh := operator_continuous_schur hm h0 hB hb ha hi ha0
    (show 0 ≤ u*A by positivity) hL (fun x hx => ?_) (fun x hx => ?_)
  · simpa only [mul_assoc] using hh
  · by_cases hxI : x ∈ Icc l u
    · exact mul_le_mul hxI.2 (haA x) (ha0 x) hu
    · rw [hs x hxI, mul_zero]
      positivity
  · exact hs x (fun hxI => by linarith [hxI.1])

/-- For a fixed continuous nonnegative compact cutoff the Schur constant is chosen
before every density, density bound, and scale. Ordinary L1 supplies finite time measure. -/
theorem operator_fixed_cutoff_schur {a : ℝ → ℝ} (ha : Continuous a)
    (ha0 : ∀ x, 0 ≤ a x) {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hs : ∀ x, x ∉ Icc l u → a x=0) :
    ∃ D : ℝ, 0 < D ∧ ∀ (μ : ℝ → ℝ) (hm : Measurable μ) (hiμ : Integrable μ),
      (∀ t, 0 ≤ μ t) → ∀ B : ℝ, 0 ≤ B → (∀ t, μ t ≤ B) →
      ∀ L : ℝ, 0 ≤ L →
        let := timeMeasure_finite hiμ
        ‖operatorContinuous (timeMeasure μ) a L‖ ≤ D*L*B := by
  obtain ⟨A,hA⟩ := isCompact_Icc.exists_bound_of_continuousOn ha.continuousOn
  let W := max 0 A
  have hW : 0 ≤ W := le_max_left _ _
  have haW (x : ℝ) : a x ≤ W := by
    by_cases hx : x ∈ Icc l u
    · exact (le_abs_self _).trans ((hA x hx).trans (le_max_right _ _))
    · rw [hs x hx]
      exact hW
  have hai : Integrable a := ha.integrable_of_hasCompactSupport (HasCompactSupport.intro isCompact_Icc hs)
  have hu : 0 ≤ u := hl.le.trans hlu
  refine ⟨2*Real.pi*u*W+1, by positivity, ?_⟩
  intro μ hm hiμ hμ0 B hB hμB L hL
  let := timeMeasure_finite hiμ
  have hh := operator_continuous_compact_schur hm hμ0 hB hμB ha.measurable hai ha0
    hl hlu hW hL haW hs
  exact hh.trans (by nlinarith [mul_nonneg hL hB])

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.operator_mellin_plancherel_weight
#print axioms GuthMaynard.Improvement.operator_continuous_quadratic
#print axioms GuthMaynard.Improvement.operator_positive_norm_of_quadratic
#print axioms GuthMaynard.Improvement.operator_continuous_schur
#print axioms GuthMaynard.Improvement.operator_continuous_compact_schur

#print axioms GuthMaynard.Improvement.operator_fixed_cutoff_schur
