module
public import GuthMaynard.Improvement.OperatorPositiveCompact

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory InnerProductSpace Filter
open scoped InnerProductSpace Topology
namespace GuthMaynard.Improvement
variable {E α ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [MeasurableSpace α] [Countable ι]
variable (ν : Measure α) (b : HilbertBasis ι ℂ E)

/-- Right multiplication preserves the actual integral nuclear presentation. -/
theorem operatorIntegral_comp_right (S : E →L[ℂ] E)
    {x y : α → E} (hx : AEStronglyMeasurable x ν) (hy : AEStronglyMeasurable y ν)
    (hxy : Integrable (fun a => ‖x a‖*‖y a‖) ν) :
    operatorIntegral ν x y * S = operatorIntegral ν x (fun a => S.adjoint (y a)) := by
  let comp : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E) :=
    (ContinuousLinearMap.compL ℂ E E E).flip S
  have hh := comp.integral_comp_comm (operatorIntegral_integrable ν hx hy hxy)
  simpa only [operatorIntegral, comp, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, rankOne_comp, ContinuousLinearMap.mul_def] using hh.symm

/-- Cyclic trace movement is proved from rank-one integrals, not postulated. -/
theorem operatorIntegral_trace_right (S : E →L[ℂ] E)
    {x y : α → E} (hx : AEStronglyMeasurable x ν) (hy : AEStronglyMeasurable y ν)
    (hxy : Integrable (fun a => ‖x a‖*‖y a‖) ν) :
    operatorDiagonalTrace b (operatorIntegral ν x y * S) =
      ∫ a, inner ℂ (y a) (S (x a)) ∂ν := by
  have hi : Integrable (fun a => ‖x a‖*‖S.adjoint (y a)‖) ν := by
    have hh := operatorIntegral_comp_integrable ν S.adjoint hy hx (by simpa [mul_comm] using hxy)
    simpa only [mul_comm] using hh
  rw [operatorIntegral_comp_right ν S hx hy hxy,
    operatorIntegral_trace ν b hx (S.adjoint.continuous.comp_aestronglyMeasurable hy) hi]
  simp only [ContinuousLinearMap.adjoint_inner_left]

/-- Strong convergence, with a uniform operator norm bound, suffices for convergence
of left nuclear traces. Operator-norm convergence is not assumed. -/
theorem operatorIntegral_trace_tendsto {β : Type*} {l : Filter β} [l.IsCountablyGenerated]
    {S : β → E →L[ℂ] E} {S₀ : E →L[ℂ] E} {B : ℝ}
    (_hB : 0 ≤ B) (hb : ∀ n, ‖S n‖ ≤ B)
    (hS : ∀ v, Tendsto (fun n => S n v) l (𝓝 (S₀ v)))
    {x y : α → E} (hx : AEStronglyMeasurable x ν) (hy : AEStronglyMeasurable y ν)
    (hxy : Integrable (fun a => ‖x a‖*‖y a‖) ν) :
    Tendsto (fun n => operatorDiagonalTrace b (S n * operatorIntegral ν x y)) l
      (𝓝 (operatorDiagonalTrace b (S₀ * operatorIntegral ν x y))) := by
  have ht (Q : E →L[ℂ] E) : operatorDiagonalTrace b (Q * operatorIntegral ν x y) =
      ∫ a, inner ℂ (y a) (Q (x a)) ∂ν := by
    rw [operatorIntegral_comp_left ν Q hx hy hxy]
    exact operatorIntegral_trace ν b (Q.continuous.comp_aestronglyMeasurable hx) hy
      (operatorIntegral_comp_integrable ν Q hx hy hxy)
  simp_rw [ht]
  apply tendsto_integral_filter_of_dominated_convergence (fun a => B*(‖x a‖*‖y a‖))
  · exact Eventually.of_forall fun n => hy.inner ((S n).continuous.comp_aestronglyMeasurable hx)
  · apply Eventually.of_forall
    intro n
    filter_upwards with a
    calc
      _ ≤ ‖y a‖*‖S n (x a)‖ := norm_inner_le_norm _ _
      _ ≤ ‖y a‖*(B*‖x a‖) := by
        gcongr
        exact ((S n).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hb n) (norm_nonneg _))
      _ = _ := by ring
  · exact hxy.const_mul B
  · exact Eventually.of_forall fun a => tendsto_const_nhds.inner (hS (x a))

omit [CompleteSpace E] in
/-- Uniformly bounded strongly convergent operators also converge on moving vectors. -/
theorem operator_strong_apply_tendsto {β : Type*} {l : Filter β}
    {S : β → E →L[ℂ] E} {S₀ : E →L[ℂ] E} {B : ℝ}
    (hb : ∀ n, ‖S n‖ ≤ B) (hS : ∀ v, Tendsto (fun n => S n v) l (𝓝 (S₀ v)))
    {v : β → E} {v₀ : E} (hv : Tendsto v l (𝓝 v₀)) :
    Tendsto (fun n => S n (v n)) l (𝓝 (S₀ v₀)) := by
  have hd : Tendsto (fun n => S n (v n-v₀)) l (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ((S n).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hb n) (norm_nonneg _)))
    simpa using (tendsto_const_nhds (x := B)).mul
      (hv.sub (tendsto_const_nhds (x := v₀))).norm
  simpa only [map_sub, sub_add_cancel, zero_add] using hd.add (hS v₀)

omit [CompleteSpace E] in
/-- The common compression word tends strongly to H². -/
theorem operator_compression_word_tendsto {β : Type*} {l : Filter β}
    (H : E →L[ℂ] E) {P : β → E →L[ℂ] E}
    (hp : ∀ n, ‖P n‖ ≤ 1) (hP : ∀ v, Tendsto (fun n => P n v) l (𝓝 v)) (v : E) :
    Tendsto (fun n => (P n*H*P n*H*P n) v) l (𝓝 ((H^2) v)) := by
  have hp' : ∀ v, Tendsto (fun n => P n v) l (𝓝 ((1 : E →L[ℂ] E) v)) := hP
  have h₁ := H.continuous.tendsto (v) |>.comp (hP v)
  have h₂ := operator_strong_apply_tendsto hp hp' h₁
  have h₃ := H.continuous.tendsto (H v) |>.comp h₂
  have h₄ := operator_strong_apply_tendsto hp hp' h₃
  simpa only [mul_apply_eq_comp, one_apply_eq_self, pow_two, Function.comp_apply] using h₄

omit [CompleteSpace E] in
/-- Common compression word has a uniform bound, independently of compression rank. -/
theorem operator_compression_word_norm (H P : E →L[ℂ] E) (hp : ‖P‖ ≤ 1) :
    ‖P*H*P*H*P‖ ≤ ‖H‖^2 := by
  calc
    _ ≤ ‖P‖*‖H‖*‖P‖*‖H‖*‖P‖ := by
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
            (norm_mul_le _ _) (norm_nonneg _))) (norm_nonneg _))) (norm_nonneg _))
    _ ≤ 1*‖H‖*1*‖H‖*1 := by gcongr
    _ = _ := by ring

/-- Cyclicity around an actual nuclear factor, with no positivity or commutation. -/
theorem operatorIntegral_trace_sandwich (S R : E →L[ℂ] E)
    {x y : α → E} (hx : AEStronglyMeasurable x ν) (hy : AEStronglyMeasurable y ν)
    (hxy : Integrable (fun a => ‖x a‖*‖y a‖) ν) :
    operatorDiagonalTrace b (S*operatorIntegral ν x y*R) =
      operatorDiagonalTrace b ((R*S)*operatorIntegral ν x y) := by
  rw [operatorIntegral_comp_left ν S hx hy hxy,
    operatorIntegral_trace_right ν b R (S.continuous.comp_aestronglyMeasurable hx) hy
      (operatorIntegral_comp_integrable ν S hx hy hxy),
    operatorIntegral_comp_left ν (R*S) hx hy hxy,
    operatorIntegral_trace ν b ((R*S).continuous.comp_aestronglyMeasurable hx) hy
      (operatorIntegral_comp_integrable ν (R*S) hx hy hxy)]
  rfl

/-- Cubic and mixed compressed traces share this exact nuclear reduction. -/
theorem operatorIntegral_compressed_trace (P H : E →L[ℂ] E) (hP : P*P=P)
    {x y : α → E} (hx : AEStronglyMeasurable x ν) (hy : AEStronglyMeasurable y ν)
    (hxy : Integrable (fun a => ‖x a‖*‖y a‖) ν) :
    operatorDiagonalTrace b ((P*operatorIntegral ν x y*P)*(P*H*P)^2) =
      operatorDiagonalTrace b ((P*H*P*H*P)*operatorIntegral ν x y) := by
  have he : (P*operatorIntegral ν x y*P)*(P*H*P)^2 =
      P*operatorIntegral ν x y*(P*H*P*H*P) := by
    simp only [pow_two, mul_assoc, ← mul_assoc P P, hP]
  rw [he, operatorIntegral_trace_sandwich ν b P (P*H*P*H*P) hx hy hxy]
  congr 2
  simp only [mul_assoc, hP]

/-- Both required compression trace limits follow from strong projection convergence.
Use the nuclear factor H for the cube, and C for the mixed trace. -/
theorem operatorIntegral_compressed_trace_tendsto {β : Type*} {l : Filter β}
    [l.IsCountablyGenerated] (H : E →L[ℂ] E) {P : β → E →L[ℂ] E}
    (hp : ∀ n, ‖P n‖ ≤ 1) (hiP : ∀ n, P n*P n=P n)
    (hP : ∀ v, Tendsto (fun n => P n v) l (𝓝 v))
    {x y : α → E} (hx : AEStronglyMeasurable x ν) (hy : AEStronglyMeasurable y ν)
    (hxy : Integrable (fun a => ‖x a‖*‖y a‖) ν) :
    Tendsto (fun n => operatorDiagonalTrace b
      ((P n*operatorIntegral ν x y*P n)*(P n*H*P n)^2)) l
      (𝓝 (operatorDiagonalTrace b ((H^2)*operatorIntegral ν x y))) := by
  simp_rw [operatorIntegral_compressed_trace ν b _ H (hiP _) hx hy hxy]
  exact operatorIntegral_trace_tendsto ν b (sq_nonneg ‖H‖)
    (fun n => operator_compression_word_norm H (P n) (hp n))
    (operator_compression_word_tendsto H hp hP) hx hy hxy

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.operatorIntegral_comp_right
#print axioms GuthMaynard.Improvement.operatorIntegral_trace_right
#print axioms GuthMaynard.Improvement.operatorIntegral_trace_tendsto

#print axioms GuthMaynard.Improvement.operator_strong_apply_tendsto

#print axioms GuthMaynard.Improvement.operator_compression_word_tendsto

#print axioms GuthMaynard.Improvement.operator_compression_word_norm

#print axioms GuthMaynard.Improvement.operatorIntegral_trace_sandwich

#print axioms GuthMaynard.Improvement.operatorIntegral_compressed_trace

#print axioms GuthMaynard.Improvement.operatorIntegral_compressed_trace_tendsto
