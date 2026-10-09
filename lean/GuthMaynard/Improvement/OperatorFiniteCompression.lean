import GuthMaynard.Improvement.OperatorTraceConvergence
set_option autoImplicit false
noncomputable section
open MeasureTheory InnerProductSpace Filter Set
open scoped InnerProductSpace Topology
namespace GuthMaynard.Improvement
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable (b : HilbertBasis ι ℂ E)

/-- Finite spaces contain the prescribed witness vectors at every stage. -/
def operatorFiniteSpace (w : Finset E) (s : Finset ι) : Submodule ℂ E := by
  classical
  exact Submodule.span ℂ ((w ∪ s.image b : Finset E) : Set E)

instance operatorFiniteSpace_finiteDimensional (w : Finset E) (s : Finset ι) :
    FiniteDimensional ℂ (operatorFiniteSpace b w s) := by
  classical
  unfold operatorFiniteSpace
  infer_instance

/-- Literal orthogonal finite compression, rather than an assumed approximation. -/
def operatorFiniteProjection (w : Finset E) (s : Finset ι) : E →L[ℂ] E :=
  (operatorFiniteSpace b w s).starProjection

theorem operator_finite_projection_norm (w : Finset E) (s : Finset ι) :
    ‖operatorFiniteProjection b w s‖ ≤ 1 :=
  (operatorFiniteSpace b w s).starProjection_norm_le

theorem operator_finite_projection_idempotent (w : Finset E) (s : Finset ι) :
    operatorFiniteProjection b w s * operatorFiniteProjection b w s =
      operatorFiniteProjection b w s :=
  (operatorFiniteSpace b w s).isIdempotentElem_starProjection

theorem operator_finite_projection_fixes_witness (w : Finset E) (s : Finset ι)
    {v : E} (hv : v ∈ w) : operatorFiniteProjection b w s v = v := by
  classical
  apply Submodule.starProjection_eq_self_iff.mpr
  apply Submodule.subset_span
  exact Finset.mem_union_left _ hv

theorem operator_finite_space_monotone (w : Finset E) : Monotone (operatorFiniteSpace b w) := by
  classical
  intro s t hst
  apply Submodule.span_mono
  exact Finset.coe_subset.mpr (Finset.union_subset_union_right (Finset.image_subset_image hst))

/-- These actual finite projections converge strongly, preserving every witness vector. -/
theorem operator_finite_projection_tendsto (w : Finset E) (v : E) :
    Tendsto (fun s : Finset ι => operatorFiniteProjection b w s v) atTop (𝓝 v) := by
  classical
  apply Submodule.starProjection_tendsto_self (operatorFiniteSpace b w)
    (operator_finite_space_monotone b w) v
  rw [← b.finite_spans_dense]
  apply Submodule.topologicalClosure_mono
  apply iSup_mono
  intro s
  apply Submodule.span_mono
  exact Finset.coe_subset.mpr Finset.subset_union_right

variable [CompleteSpace E]

/-- Genuine nuclear trace limit on the constructed finite spaces; the fixed finite witness
is arbitrary and no spectral conclusion or limit is assumed. -/
theorem operator_finite_compressed_trace_tendsto [Countable ι]
    {α : Type*} [MeasurableSpace α] (ν : Measure α) (w : Finset E) (H : E →L[ℂ] E)
    {x y : α → E} (hx : AEStronglyMeasurable x ν) (hy : AEStronglyMeasurable y ν)
    (hxy : Integrable (fun a => ‖x a‖*‖y a‖) ν) :
    Tendsto (fun s : Finset ι => operatorDiagonalTrace b
      ((operatorFiniteProjection b w s * operatorIntegral ν x y * operatorFiniteProjection b w s)*
        (operatorFiniteProjection b w s * H * operatorFiniteProjection b w s)^2)) atTop
      (𝓝 (operatorDiagonalTrace b ((H^2)*operatorIntegral ν x y))) := by
  exact operatorIntegral_compressed_trace_tendsto ν b H
    (operator_finite_projection_norm b w) (operator_finite_projection_idempotent b w)
    (operator_finite_projection_tendsto b w) hx hy hxy

/-- Actual cubic trace convergence, with the witness included at every finite stage. -/
theorem operator_finite_cubic_trace_tendsto [Countable ι]
    {α : Type*} [MeasurableSpace α] (ν : Measure α) (w : Finset E)
    {x y : α → E} (hx : AEStronglyMeasurable x ν) (hy : AEStronglyMeasurable y ν)
    (hxy : Integrable (fun a => ‖x a‖*‖y a‖) ν) :
    Tendsto (fun s : Finset ι => operatorDiagonalTrace b
      ((operatorFiniteProjection b w s * operatorIntegral ν x y * operatorFiniteProjection b w s)^3))
      atTop (𝓝 (operatorDiagonalTrace b ((operatorIntegral ν x y)^3))) := by
  simpa only [← pow_succ', ← pow_succ] using
    operator_finite_compressed_trace_tendsto b ν w (operatorIntegral ν x y) hx hy hxy

/-- The mixed trace converges as well; no monotonicity of compressed mixed traces is asserted. -/
theorem operator_finite_mixed_trace_tendsto [Countable ι]
    {α : Type*} [MeasurableSpace α] (ν : Measure α) (w : Finset E) (H : E →L[ℂ] E)
    {x y : α → E} (hx : AEStronglyMeasurable x ν) (hy : AEStronglyMeasurable y ν)
    (hxy : Integrable (fun a => ‖x a‖*‖y a‖) ν) :
    Tendsto (fun s : Finset ι => operatorDiagonalTrace b
      ((operatorFiniteProjection b w s * operatorIntegral ν x y * operatorFiniteProjection b w s)*
        (operatorFiniteProjection b w s * H * operatorFiniteProjection b w s)^2)) atTop
      (𝓝 (operatorDiagonalTrace b (operatorIntegral ν x y * H^2))) := by
  have he : operatorDiagonalTrace b ((H^2)*operatorIntegral ν x y) =
      operatorDiagonalTrace b (operatorIntegral ν x y*(H^2)) := by
    rw [operatorIntegral_trace_right ν b (H^2) hx hy hxy,
      operatorIntegral_comp_left ν (H^2) hx hy hxy,
      operatorIntegral_trace ν b ((H^2).continuous.comp_aestronglyMeasurable hx) hy
        (operatorIntegral_comp_integrable ν (H^2) hx hy hxy)]
  rw [← he]
  exact operator_finite_compressed_trace_tendsto b ν w H hx hy hxy

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.operator_finite_projection_norm
#print axioms GuthMaynard.Improvement.operator_finite_projection_idempotent
#print axioms GuthMaynard.Improvement.operator_finite_projection_fixes_witness
#print axioms GuthMaynard.Improvement.operator_finite_space_monotone
#print axioms GuthMaynard.Improvement.operator_finite_projection_tendsto
#print axioms GuthMaynard.Improvement.operator_finite_compressed_trace_tendsto

#print axioms GuthMaynard.Improvement.operator_finite_cubic_trace_tendsto
#print axioms GuthMaynard.Improvement.operator_finite_mixed_trace_tendsto
