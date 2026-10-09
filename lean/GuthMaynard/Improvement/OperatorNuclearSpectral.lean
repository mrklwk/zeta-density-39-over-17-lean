import GuthMaynard.Improvement.OperatorSpectralComparison
set_option autoImplicit false
noncomputable section
open MeasureTheory InnerProductSpace Filter Set
open scoped InnerProductSpace Topology
namespace GuthMaynard.Improvement
variable {E ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Infinite-dimensional spectral comparison from actual nuclear presentations and an
actual finite orthonormal quadratic witness. Finite eigenbases and both trace limits are
proved dependencies; an infinite eigenbasis is not a premise or construction. -/
theorem operator_nuclear_spectral_comparison [Countable ι] [Fintype κ]
    (b : HilbertBasis ι ℂ E) (G C : E →L[ℂ] E) (hG : G.IsPositive) (hC : C.IsPositive)
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (νH : Measure α) (νC : Measure β)
    {xH yH : α → E} {xC yC : β → E}
    (hxH : AEStronglyMeasurable xH νH) (hyH : AEStronglyMeasurable yH νH)
    (hiH : Integrable (fun t => ‖xH t‖*‖yH t‖) νH)
    (hxC : AEStronglyMeasurable xC νC) (hyC : AEStronglyMeasurable yC νC)
    (hiC : Integrable (fun t => ‖xC t‖*‖yC t‖) νC)
    (hH : G-C=operatorIntegral νH xH yH) (hCI : C=operatorIntegral νC xC yC)
    (v : κ → E) (hv : Orthonormal ℂ v) {k a B : ℝ}
    (hk : (Fintype.card κ:ℝ) ≤ k) (hB : ‖C‖ ≤ B)
    (hw : k*a ≤ ∑ j, (inner ℂ (v j) (G (v j))).re) :
    k*(max (a-B) 0)^3 ≤ ‖operatorDiagonalTrace b ((G-C)^3)‖+
      (operatorDiagonalTrace b (C*(G-C)^2)).re := by
  classical
  let w : Finset E := Finset.univ.image v
  have hwU (s : Finset ι) (j : κ) : v j ∈ operatorFiniteSpace b w s := by
    apply Submodule.subset_span
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem v (Finset.mem_univ j))
  have hf (s : Finset ι) := operator_subspace_spectral_comparison b
    (operatorFiniteSpace b w s) G C hG hC v hv (hwU s) hk hB hw
  have htH := operator_finite_cubic_trace_tendsto b νH w hxH hyH hiH
  rw [← hH] at htH
  have htC := operator_finite_mixed_trace_tendsto b νC w (G-C) hxC hyC hiC
  rw [← hCI] at htC
  have hlim := htH.norm.add (Complex.continuous_re.tendsto _ |>.comp htC)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall hf)

/-- The abstract nuclear input is discharged for the literal discrete and continuous
phase operators using only ordinary cutoff data. The finite witness and correction
operator norm bound are the remaining amplifier/Schur inputs. -/
theorem operator_centered_spectral_comparison (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a : ℝ → ℝ} (ha : Measurable a) (hi : Integrable a) (ha0 : ∀ x, 0 ≤ a x)
    {l u L A : ℝ} (hl : 0 < l) (hL : 0 < L) (hA : 0 ≤ A)
    (haA : ∀ x, |a x| ≤ A) (hs : ∀ x, x ∉ Icc l u → a x = 0)
    {ι κ : Type*} [Countable ι] [Fintype κ] (b : HilbertBasis ι ℂ (Lp ℂ 2 μ))
    (v : κ → Lp ℂ 2 μ) (hv : Orthonormal ℂ v) {k level B : ℝ}
    (hk : (Fintype.card κ:ℝ) ≤ k) (hB : ‖operatorContinuous μ a L‖ ≤ B)
    (hw : k*level ≤ ∑ j, (inner ℂ (v j) (operatorDiscrete μ a L l u (v j))).re) :
    k*(max (level-B) 0)^3 ≤
      ‖operatorDiagonalTrace b ((operatorDiscrete μ a L l u-operatorContinuous μ a L)^3)‖+
      (operatorDiagonalTrace b (operatorContinuous μ a L*
        (operatorDiscrete μ a L l u-operatorContinuous μ a L)^2)).re := by
  obtain ⟨hxH,hyH,hiH⟩ := operator_frequency_inputs μ (operatorCenteredMeasure l u L)
    (operator_centered_amplitude_measurable ha L) operator_centered_frequency_measurable
    (show 0 ≤ (1+|L|)*A by positivity) (operator_centered_amplitude_bound hA haA L)
  exact operator_nuclear_spectral_comparison b (operatorDiscrete μ a L l u)
    (operatorContinuous μ a L) (operator_discrete_positive μ ha0 L l u)
    (operator_continuous_positive μ hi ha0 hL.le)
    (operatorCenteredMeasure l u L) volume hxH hyH hiH
    (operator_weighted_phase_measurable μ hi L) (operator_mellin_phase_measurable μ)
    (operator_continuous_norm_product μ hi L)
    (operator_centered_eq μ hi hl hL hs).symm rfl v hv hk hB hw

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.operator_nuclear_spectral_comparison
#print axioms GuthMaynard.Improvement.operator_centered_spectral_comparison
