module
public import GuthMaynard.Improvement.OperatorCentered
public import GuthMaynard.Improvement.OperatorKernel

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set InnerProductSpace
open scoped InnerProductSpace ComplexOrder ENNReal
namespace GuthMaynard.Improvement

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem operator_rankOne_compact (x y : E) : IsCompactOperator (rankOne ℂ x y) := by
  rw [rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_dom (innerSL ℂ y)).clm_comp (ContinuousLinearMap.toSpanSingleton ℂ x)

/-- A finite measure integral of compact operators is compact in operator norm. -/
theorem operator_integral_compact {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] {F : α → E →L[ℂ] E}
    (hi : Integrable F ν) (hc : ∀ᵐ x ∂ν, IsCompactOperator (F x)) :
    IsCompactOperator (∫ x, F x ∂ν : E →L[ℂ] E) := by
  let K := (compactOperator (RingHom.id ℂ) E E).restrictScalars ℝ
  by_cases hν : ν = 0
  · subst ν
    simpa using (isCompactOperator_zero : IsCompactOperator (0 : E →L[ℂ] E))
  let : NeZero ν := ⟨hν⟩
  have hav : (⨍ x, F x ∂ν) ∈ K :=
    K.convex.average_mem isClosed_setOfPred_isCompactOperator hc hi
  have hh := K.smul_mem (ν.real univ) hav
  rwa [measure_smul_average] at hh

/-- Positivity survives a Bochner integral; no commutation is required. -/
theorem operator_integral_positive {α : Type*} [MeasurableSpace α]
    (ν : Measure α) {F : α → E →L[ℂ] E} (hi : Integrable F ν)
    (hp : ∀ᵐ x ∂ν, (F x).IsPositive) : (∫ x, F x ∂ν).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff _).2
  have ha (v : E) : Integrable (fun x => F x v) ν :=
    (ContinuousLinearMap.apply ℂ E v).integrable_comp hi
  have hil (v w : E) : (∫ x, inner ℂ (F x v) w ∂ν) =
      inner ℂ (∫ x, F x v ∂ν) w :=
    by
      simp_rw [← inner_conj_symm _ w]
      rw [integral_conj, integral_inner (ha v)]
  constructor
  · intro v w
    change inner ℂ ((∫ x, F x ∂ν : E →L[ℂ] E) v) w =
      inner ℂ v ((∫ x, F x ∂ν : E →L[ℂ] E) w)
    rw [ContinuousLinearMap.integral_apply hi, ContinuousLinearMap.integral_apply hi,
      ← hil v w, ← integral_inner (ha w)]
    apply integral_congr_ae
    filter_upwards [hp] with x hx
    exact hx.inner_left_eq_inner_right v w
  · intro v
    rw [ContinuousLinearMap.integral_apply hi, ← hil v v]
    exact integral_nonneg_of_ae (hp.mono fun x hx => hx.inner_nonneg_left v)

/-- Nonnegative real cutoff gives a positive actual finite integer operator. -/
theorem operator_discrete_positive (ν : Measure ℝ) [IsFiniteMeasure ν]
    {a : ℝ → ℝ} (ha : ∀ x, 0 ≤ a x) (L l u : ℝ) :
    (operatorDiscrete ν a L l u).IsPositive := by
  apply ContinuousLinearMap.isPositive_sum
  intro m hm
  apply (isPositive_rankOne_self _).smul_of_nonneg
  exact_mod_cast ha ((m:ℝ)/L)

/-- Nonnegative real cutoff and scale give a positive actual continuous operator. -/
theorem operator_continuous_positive (ν : Measure ℝ) [IsFiniteMeasure ν]
    {a : ℝ → ℝ} (hi : Integrable a) (ha : ∀ x, 0 ≤ a x) {L : ℝ} (hL : 0 ≤ L) :
    (operatorContinuous ν a L).IsPositive := by
  apply operator_integral_positive volume (operator_continuous_integrable ν hi L)
  filter_upwards with x
  rw [map_smul, smul_apply]
  apply (isPositive_rankOne_self _).smul_of_nonneg
  exact_mod_cast mul_nonneg hL (ha x)

/-- The literal finite integer cutoff is compact, independently of signs. -/
theorem operator_discrete_compact (ν : Measure ℝ) [IsFiniteMeasure ν]
    (a : ℝ → ℝ) (L l u : ℝ) : IsCompactOperator (operatorDiscrete ν a L l u) := by
  change operatorDiscrete ν a L l u ∈ compactOperator (RingHom.id ℂ) _ _
  apply Submodule.sum_mem
  intro m hm
  exact Submodule.smul_mem _ _ (operator_rankOne_compact _ _)

/-- Ordinary compact support and L1 imply compactness of the actual continuous operator. -/
theorem operator_continuous_compact (ν : Measure ℝ) [IsFiniteMeasure ν]
    {a : ℝ → ℝ} (hi : Integrable a) (L l u : ℝ)
    (hs : ∀ x, x ∉ Icc l u → a x = 0) :
    IsCompactOperator (operatorContinuous ν a L) := by
  let F := fun x => rankOne ℂ (((L*a x:ℝ):ℂ) •
    operatorPhase ν (mellinFrequency x)) (operatorPhase ν (mellinFrequency x))
  have he : (∫ x in Icc l u, F x) = operatorContinuous ν a L := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp [F, hs x hx]
  rw [← he]
  apply operator_integral_compact (volume.restrict (Icc l u))
    (operator_continuous_integrable ν hi L).integrableOn
  exact Filter.Eventually.of_forall fun x => operator_rankOne_compact _ _

/-- Only self-adjointness and compactness are asserted for the difference. -/
theorem operator_centered_selfAdjoint_compact (ν : Measure ℝ) [IsFiniteMeasure ν]
    {a : ℝ → ℝ} (hi : Integrable a) (ha : ∀ x, 0 ≤ a x) {L : ℝ} (hL : 0 ≤ L)
    (l u : ℝ) (hs : ∀ x, x ∉ Icc l u → a x = 0) :
    IsSelfAdjoint (operatorDiscrete ν a L l u - operatorContinuous ν a L) ∧
    IsCompactOperator (operatorDiscrete ν a L l u - operatorContinuous ν a L) := by
  refine ⟨(operator_discrete_positive ν ha L l u).isSelfAdjoint.sub
    (operator_continuous_positive ν hi ha hL).isSelfAdjoint, ?_⟩
  exact (operator_discrete_compact ν a L l u).sub
    (operator_continuous_compact ν hi L l u hs)

omit [CompleteSpace E] in
/-- Any orthonormal family in a separable complex Hilbert space has countable index. -/
theorem operator_orthonormal_countable [TopologicalSpace.SeparableSpace E]
    {ι : Type*} {v : ι → E} (hv : Orthonormal ℂ v) : Countable ι := by
  have hd : Pairwise (fun i j => Disjoint (Metric.ball (v i) (1/2:ℝ)) (Metric.ball (v j) (1/2:ℝ))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    have hh := norm_sub_sq (𝕜 := ℂ) (v i) (v j)
    rw [hv.norm_eq_one i, hv.norm_eq_one j, hv.inner_eq_zero hij] at hh
    have hn := norm_nonneg (v i-v j)
    rw [dist_eq_norm]
    simp only [map_zero] at hh
    nlinarith
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨v i, Metric.mem_ball_self (by norm_num)⟩)

/-- The actual L2 space of any finite Borel time measure has a countable Hilbert basis. -/
theorem operator_countable_hilbertBasis (ν : Measure ℝ) [IsFiniteMeasure ν] :
    ∃ (w : Set (Lp ℂ 2 ν)), Countable w ∧ Nonempty (HilbertBasis w ℂ (Lp ℂ 2 ν)) := by
  let : Fact ((2 : ENNReal) ≠ ∞) := ⟨by norm_num⟩
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ (Lp ℂ 2 ν)
  exact ⟨w, operator_orthonormal_countable b.orthonormal, ⟨b⟩⟩

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.operator_rankOne_compact
#print axioms GuthMaynard.Improvement.operator_integral_compact
#print axioms GuthMaynard.Improvement.operator_integral_positive
#print axioms GuthMaynard.Improvement.operator_discrete_positive
#print axioms GuthMaynard.Improvement.operator_continuous_positive

#print axioms GuthMaynard.Improvement.operator_discrete_compact
#print axioms GuthMaynard.Improvement.operator_continuous_compact
#print axioms GuthMaynard.Improvement.operator_centered_selfAdjoint_compact

#print axioms GuthMaynard.Improvement.operator_orthonormal_countable
#print axioms GuthMaynard.Improvement.operator_countable_hilbertBasis
