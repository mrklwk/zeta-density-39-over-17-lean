module
public import Mathlib

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory InnerProductSpace
open scoped InnerProductSpace
namespace GuthMaynard.Improvement

variable {E ι α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


/-- The diagonal sum in a Hilbert basis. Summability and basis independence
are proved below for integral nuclear presentations; neither is part of this definition. -/
def operatorDiagonalTrace (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E) : ℂ :=
  ∑' i, ⟪b i, T (b i)⟫_ℂ

/-- Absolute Bessel bound, valid also for an infinite Hilbert basis. -/
theorem operator_rankOne_diagonal_bound (b : HilbertBasis ι ℂ E) (x y : E)
    (s : Finset ι) :
    ∑ i ∈ s, ‖⟪b i, rankOne ℂ x y (b i)⟫_ℂ‖ ≤ ‖x‖ * ‖y‖ := by
  simp only [rankOne_apply, inner_smul_right, norm_mul]
  simp_rw [norm_inner_symm y]
  calc
    _ ≤ Real.sqrt (∑ i ∈ s, ‖⟪b i, y⟫_ℂ‖ ^ 2) *
        Real.sqrt (∑ i ∈ s, ‖⟪b i, x⟫_ℂ‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt s _ _
    _ ≤ Real.sqrt (‖y‖ ^ 2) * Real.sqrt (‖x‖ ^ 2) := by
      gcongr
      · exact b.orthonormal.sum_inner_products_le y
      · exact b.orthonormal.sum_inner_products_le x
    _ = _ := by rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]; ring

/-- An actual infinite-dimensional rank-one trace formula, via Parseval. -/
theorem operator_rankOne_hasSum (b : HilbertBasis ι ℂ E) (x y : E) :
    HasSum (fun i => ⟪b i, rankOne ℂ x y (b i)⟫_ℂ) ⟪y, x⟫_ℂ := by
  simpa only [rankOne_apply, inner_smul_right] using b.hasSum_inner_mul_inner y x

variable [CompleteSpace E] [MeasurableSpace α] (ν : Measure α)

/-- Bochner integral in the Banach space of bounded operators. -/
def operatorIntegral (x y : α → E) : E →L[ℂ] E :=
  ∫ a, rankOne ℂ (x a) (y a) ∂ν

/-- Nuclear integrability is a norm-product condition, not a trace-identity assumption. -/
theorem operatorIntegral_integrable {x y : α → E}
    (hx : AEStronglyMeasurable x ν) (hy : AEStronglyMeasurable y ν)
    (hxy : Integrable (fun a => ‖x a‖ * ‖y a‖) ν) :
    Integrable (fun a => rankOne ℂ (x a) (y a)) ν := by
  have hc : Continuous (fun p : E × E => rankOne ℂ p.1 p.2) := by
    simp only [rankOne_def]
    exact ((ContinuousLinearMap.smulRightL ℂ E E).continuous.comp
      ((innerSL ℂ).continuous.comp continuous_snd)).clm_apply continuous_fst
  apply hxy.mono' (hc.comp_aestronglyMeasurable (hx.prodMk hy))
  exact Filter.Eventually.of_forall (fun a => (norm_rankOne (x a) (y a)).le)

/-- Trace identification for a continuous nuclear presentation, including
absolute convergence. Its right side is independent of the Hilbert basis. -/
theorem operatorIntegral_hasSum [Countable ι] (b : HilbertBasis ι ℂ E)
    {x y : α → E} (hx : AEStronglyMeasurable x ν) (hy : AEStronglyMeasurable y ν)
    (hxy : Integrable (fun a => ‖x a‖ * ‖y a‖) ν) :
    HasSum (fun i => ⟪b i, operatorIntegral ν x y (b i)⟫_ℂ)
      (∫ a, ⟪y a, x a⟫_ℂ ∂ν) := by
  let F : ι → α → ℂ := fun i a => ⟪b i, rankOne ℂ (x a) (y a) (b i)⟫_ℂ
  have hF : ∀ i, AEStronglyMeasurable (F i) ν := by
    intro i
    dsimp [F]
    simp only [inner_smul_right]
    exact (hy.inner aestronglyMeasurable_const).mul (aestronglyMeasurable_const.inner hx)
  have hs : ∀ a, Summable (fun i => ‖F i a‖) := fun a =>
    summable_of_sum_le (fun i => norm_nonneg _) (operator_rankOne_diagonal_bound b (x a) (y a))
  have hb : Integrable (fun a => ∑' i, ‖F i a‖) ν := by
    apply hxy.mono' (AEStronglyMeasurable.tsum (fun i => (hF i).norm))
    filter_upwards with a
    rw [Real.norm_of_nonneg (tsum_nonneg (fun i => norm_nonneg _))]
    exact (hs a).tsum_le_of_sum_le (operator_rankOne_diagonal_bound b (x a) (y a))
  have hh := hasSum_integral_of_dominated_convergence (fun i a => ‖F i a‖) hF
    (fun i => Filter.Eventually.of_forall (fun a => le_rfl))
    (Filter.Eventually.of_forall hs) hb
    (Filter.Eventually.of_forall (fun a => operator_rankOne_hasSum b (x a) (y a)))
  convert hh using 1
  ext i
  let ev : (E →L[ℂ] E) →L[ℂ] ℂ := (innerSL ℂ (b i)).comp (ContinuousLinearMap.apply ℂ E (b i))
  exact (ev.integral_comp_comm (operatorIntegral_integrable ν hx hy hxy)).symm

/-- The diagonal trace is therefore the nuclear integral, not its definition. -/
theorem operatorIntegral_trace [Countable ι] (b : HilbertBasis ι ℂ E)
    {x y : α → E} (hx : AEStronglyMeasurable x ν) (hy : AEStronglyMeasurable y ν)
    (hxy : Integrable (fun a => ‖x a‖ * ‖y a‖) ν) :
    operatorDiagonalTrace b (operatorIntegral ν x y) = ∫ a, ⟪y a, x a⟫_ℂ ∂ν :=
  (operatorIntegral_hasSum ν b hx hy hxy).tsum_eq

/-- Basis independence on integral nuclear operators, even for differently
indexed countable bases. -/
theorem operatorIntegral_trace_basis_independent {κ : Type*} [Countable ι] [Countable κ]
    (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E)
    {x y : α → E} (hx : AEStronglyMeasurable x ν) (hy : AEStronglyMeasurable y ν)
    (hxy : Integrable (fun a => ‖x a‖ * ‖y a‖) ν) :
    operatorDiagonalTrace b (operatorIntegral ν x y) =
      operatorDiagonalTrace c (operatorIntegral ν x y) := by
  rw [operatorIntegral_trace ν b hx hy hxy, operatorIntegral_trace ν c hx hy hxy]

/-- Integral nuclear presentations form a left ideal under bounded operators. -/
theorem operatorIntegral_comp_left (S : E →L[ℂ] E)
    {x y : α → E} (hx : AEStronglyMeasurable x ν) (hy : AEStronglyMeasurable y ν)
    (hxy : Integrable (fun a => ‖x a‖ * ‖y a‖) ν) :
    S * operatorIntegral ν x y = operatorIntegral ν (fun a => S (x a)) y := by
  let comp : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E) := ContinuousLinearMap.compL ℂ E E E S
  have hh := comp.integral_comp_comm (operatorIntegral_integrable ν hx hy hxy)
  simpa only [operatorIntegral, comp, ContinuousLinearMap.compL_apply,
    comp_rankOne, ContinuousLinearMap.mul_def] using hh.symm

omit [CompleteSpace E] in
/-- The left-ideal norm-product bound is derived, not supplied as a premise. -/
theorem operatorIntegral_comp_integrable (S : E →L[ℂ] E)
    {x y : α → E} (hx : AEStronglyMeasurable x ν) (hy : AEStronglyMeasurable y ν)
    (hxy : Integrable (fun a => ‖x a‖ * ‖y a‖) ν) :
    Integrable (fun a => ‖S (x a)‖ * ‖y a‖) ν := by
  apply (hxy.const_mul ‖S‖).mono' ((S.continuous.comp_aestronglyMeasurable hx).norm.mul hy.norm)
  filter_upwards with a
  dsimp only [Pi.mul_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  calc
    _ ≤ (‖S‖ * ‖x a‖) * ‖y a‖ := mul_le_mul_of_nonneg_right (S.le_opNorm _) (norm_nonneg _)
    _ = _ := mul_assoc _ _ _

/-- Actual cubic operator trace for an integral nuclear presentation. This
is an infinite-dimensional identity, with no positivity or commutation premise. -/
theorem operatorIntegral_cubic_trace [Countable ι] (b : HilbertBasis ι ℂ E)
    {x y : α → E} (hx : AEStronglyMeasurable x ν) (hy : AEStronglyMeasurable y ν)
    (hxy : Integrable (fun a => ‖x a‖ * ‖y a‖) ν) :
    operatorDiagonalTrace b ((operatorIntegral ν x y)^3) =
      ∫ a, ⟪y a, ((operatorIntegral ν x y)^2) (x a)⟫_ℂ ∂ν := by
  rw [pow_succ, operatorIntegral_comp_left ν _ hx hy hxy]
  exact operatorIntegral_trace ν b
    (((operatorIntegral ν x y)^2).continuous.comp_aestronglyMeasurable hx) hy
    (operatorIntegral_comp_integrable ν _ hx hy hxy)

/-- Absolute convergence of the actual operator diagonal, not just of a
formal scalar nuclear expression. -/
theorem operatorIntegral_diagonal_summable_norm [Countable ι] (b : HilbertBasis ι ℂ E)
    {x y : α → E} (hx : AEStronglyMeasurable x ν) (hy : AEStronglyMeasurable y ν)
    (hxy : Integrable (fun a => ‖x a‖ * ‖y a‖) ν) :
    Summable (fun i => ‖⟪b i, operatorIntegral ν x y (b i)⟫_ℂ‖) :=
  (operatorIntegral_hasSum ν b hx hy hxy).summable.norm

/-- Matrix coefficients of the actual operator integral. -/
theorem operatorIntegral_pairing {x y : α → E}
    (hx : AEStronglyMeasurable x ν) (hy : AEStronglyMeasurable y ν)
    (hxy : Integrable (fun a => ‖x a‖ * ‖y a‖) ν) (z w : E) :
    ⟪z, operatorIntegral ν x y w⟫_ℂ =
      ∫ a, ⟪z, x a⟫_ℂ * ⟪y a, w⟫_ℂ ∂ν := by
  let ev : (E →L[ℂ] E) →L[ℂ] ℂ := (innerSL ℂ z).comp (ContinuousLinearMap.apply ℂ E w)
  have hh := ev.integral_comp_comm (operatorIntegral_integrable ν hx hy hxy)
  simpa only [ev, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    innerSL_apply_apply, inner_right_rankOne_apply, operatorIntegral] using hh.symm

/-- Full three-cycle identification, before any change of integration order.
This trace is defined by a Hilbert basis diagonal, not by the cycle integral. -/
theorem operatorIntegral_cubic_cycle [Countable ι] (b : HilbertBasis ι ℂ E)
    {x y : α → E} (hx : AEStronglyMeasurable x ν) (hy : AEStronglyMeasurable y ν)
    (hxy : Integrable (fun a => ‖x a‖ * ‖y a‖) ν) :
    operatorDiagonalTrace b ((operatorIntegral ν x y)^3) =
      ∫ a, ∫ c, ∫ d,
        ⟪y a, x c⟫_ℂ * ⟪y c, x d⟫_ℂ * ⟪y d, x a⟫_ℂ ∂ν ∂ν ∂ν := by
  rw [operatorIntegral_cubic_trace ν b hx hy hxy]
  simp only [pow_two, mul_apply_eq_comp]
  apply integral_congr_ae
  filter_upwards with a
  rw [operatorIntegral_pairing ν hx hy hxy]
  apply integral_congr_ae
  filter_upwards with c
  rw [operatorIntegral_pairing ν hx hy hxy, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with d
  exact (mul_assoc _ _ _).symm

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.operator_rankOne_diagonal_bound
#print axioms GuthMaynard.Improvement.operator_rankOne_hasSum
#print axioms GuthMaynard.Improvement.operatorIntegral_integrable
#print axioms GuthMaynard.Improvement.operatorIntegral_hasSum
#print axioms GuthMaynard.Improvement.operatorIntegral_trace

#print axioms GuthMaynard.Improvement.operatorIntegral_trace_basis_independent
#print axioms GuthMaynard.Improvement.operatorIntegral_comp_left
#print axioms GuthMaynard.Improvement.operatorIntegral_comp_integrable
#print axioms GuthMaynard.Improvement.operatorIntegral_cubic_trace
#print axioms GuthMaynard.Improvement.operatorIntegral_diagonal_summable_norm

#print axioms GuthMaynard.Improvement.operatorIntegral_pairing
#print axioms GuthMaynard.Improvement.operatorIntegral_cubic_cycle
