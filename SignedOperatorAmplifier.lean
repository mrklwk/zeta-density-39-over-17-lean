module
public import GuthMaynard.Improvement.OperatorNuclearSpectral
public import GuthMaynard.Improvement.SpectralMassAssembly

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory InnerProductSpace Filter Set
open scoped InnerProductSpace Topology
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement

/-- The exact signed cubic comparison is stronger than the older absolute
trace helper. Only diagonal positivity of G and C is needed. -/
theorem finite_diagonal_signed_trace {ι : Type*} [Fintype ι]
    (c e : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (hg : ∀ i, 0 ≤ c i+e i) :
    (∑ i, (max (e i) 0)^3) ≤ (∑ i, (e i)^3)+∑ i, c i*(e i)^2 := by
  have hp (i : ι) : (max (e i) 0)^3 ≤ (e i)^3+c i*(e i)^2 := by
    by_cases he : 0 ≤ e i
    · rw [max_eq_left he]
      nlinarith [mul_nonneg (hc i) (sq_nonneg (e i))]
    · rw [max_eq_right (le_of_not_ge he)]
      nlinarith [mul_nonneg (hg i) (sq_nonneg (e i))]
  exact (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp i)).trans_eq Finset.sum_add_distrib

variable {E ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem operator_finite_signed_spectral_comparison [FiniteDimensional ℂ E]
    [Fintype ι] [Fintype κ] (d : OrthonormalBasis ι ℂ E)
    (G C : E →L[ℂ] E) (hG : G.IsPositive) (hC : C.IsPositive)
    (v : κ → E) (hv : Orthonormal ℂ v) {k a B : ℝ}
    (hk : (Fintype.card κ:ℝ) ≤ k) (hB : ‖C‖ ≤ B)
    (hw : k*a ≤ ∑ j, (inner ℂ (v j) (G (v j))).re) :
    k*(max (a-B) 0)^3 ≤
      (∑ i, inner ℂ (d i) (((G-C)^3) (d i))).re+
      (∑ i, inner ℂ (d i) ((C*(G-C)^2) (d i))).re := by
  let H := G-C
  have hs : H.toLinearMap.IsSymmetric := hG.isSymmetric.sub hC.isSymmetric
  let b := hs.eigenvectorBasis rfl
  let e := hs.eigenvalues rfl
  have he (i : Fin (Module.finrank ℂ E)) : H (b i) = (e i:ℂ) • b i :=
    hs.apply_eigenvectorBasis rfl i
  have hp := finite_operator_positive_cube b H C hs e he v hv hk hB
    (by simpa [H] using hw)
  have hd := finite_diagonal_signed_trace
    (fun i => (inner ℂ (b i) (C (b i))).re) e
    (fun i => (operator_eigenbasis_diagonal_nonneg b G C hG hC e he i).1)
    (fun i => (operator_eigenbasis_diagonal_nonneg b G C hG hC e he i).2)
  have hcubes := operator_eigenbasis_trace_values b H C e he
  have htrace (T : E →L[ℂ] E) :
      (∑ i, inner ℂ (d i) (T (d i))) = ∑ i, inner ℂ (b i) (T (b i)) := by
    exact (LinearMap.trace_eq_sum_inner T.toLinearMap d).symm.trans
      (LinearMap.trace_eq_sum_inner T.toLinearMap b)
  rw [htrace ((G-C)^3), htrace (C*(G-C)^2)]
  change k*(max (a-B) 0)^3 ≤ (∑ i, inner ℂ (b i) ((H^3) (b i))).re+
    (∑ i, inner ℂ (b i) ((C*H^2) (b i))).re
  rw [hcubes.1, hcubes.2, Complex.ofReal_re]
  exact hp.trans hd


theorem operator_subspace_signed_spectral_comparison [CompleteSpace E]
    (b : HilbertBasis ι ℂ E) (U : Submodule ℂ E) [FiniteDimensional ℂ U]
    [Fintype κ] (G C : E →L[ℂ] E) (hG : G.IsPositive) (hC : C.IsPositive)
    (v : κ → E) (hv : Orthonormal ℂ v) (hvU : ∀ j, v j ∈ U)
    {k a B : ℝ} (hk : (Fintype.card κ:ℝ) ≤ k) (hB : ‖C‖ ≤ B)
    (hw : k*a ≤ ∑ j, (inner ℂ (v j) (G (v j))).re) :
    k*(max (a-B) 0)^3 ≤
      (operatorDiagonalTrace b ((U.starProjection*(G-C)*U.starProjection)^3)).re+
      (operatorDiagonalTrace b ((U.starProjection*C*U.starProjection)*
        (U.starProjection*(G-C)*U.starProjection)^2)).re := by
  classical
  let w : κ → U := fun j => ⟨v j,hvU j⟩
  have hwO : Orthonormal ℂ w := by
    rw [orthonormal_iff_ite] at hv ⊢
    exact hv
  let d := stdOrthonormalBasis ℂ U
  have hcG := operator_subspace_compression_positive U hG
  have hcC := operator_subspace_compression_positive U hC
  have hh := operator_finite_signed_spectral_comparison d
    (operatorSubspaceCompression U G) (operatorSubspaceCompression U C) hcG hcC w hwO hk
    ((operator_subspace_compression_norm U C).trans hB)
    (by simpa only [operator_subspace_compression_pairing, w] using hw)
  rw [operator_subspace_cubic_trace b U d, operator_subspace_mixed_trace b U d]
  simpa only [operator_subspace_compression_sub] using hh


theorem operator_nuclear_signed_spectral_comparison [CompleteSpace E] [Countable ι] [Fintype κ]
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
    k*(max (a-B) 0)^3 ≤ (operatorDiagonalTrace b ((G-C)^3)).re+
      (operatorDiagonalTrace b (C*(G-C)^2)).re := by
  classical
  let w : Finset E := Finset.univ.image v
  have hwU (s : Finset ι) (j : κ) : v j ∈ operatorFiniteSpace b w s := by
    apply Submodule.subset_span
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem v (Finset.mem_univ j))
  have hf (s : Finset ι) := operator_subspace_signed_spectral_comparison b
    (operatorFiniteSpace b w s) G C hG hC v hv (hwU s) hk hB hw
  have htH := operator_finite_cubic_trace_tendsto b νH w hxH hyH hiH
  rw [← hH] at htH
  have htC := operator_finite_mixed_trace_tendsto b νC w (G-C) hxC hyC hiC
  rw [← hCI] at htC
  have hlim := (Complex.continuous_re.tendsto _ |>.comp htH).add
    (Complex.continuous_re.tendsto _ |>.comp htC)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall hf)


theorem operator_centered_signed_spectral_comparison (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a : ℝ → ℝ} (ha : Measurable a) (hi : Integrable a) (ha0 : ∀ x, 0 ≤ a x)
    {l u L A : ℝ} (hl : 0 < l) (hL : 0 < L) (hA : 0 ≤ A)
    (haA : ∀ x, |a x| ≤ A) (hs : ∀ x, x ∉ Icc l u → a x = 0)
    {ι κ : Type*} [Countable ι] [Fintype κ] (b : HilbertBasis ι ℂ (Lp ℂ 2 μ))
    (v : κ → Lp ℂ 2 μ) (hv : Orthonormal ℂ v) {k level B : ℝ}
    (hk : (Fintype.card κ:ℝ) ≤ k) (hB : ‖operatorContinuous μ a L‖ ≤ B)
    (hw : k*level ≤ ∑ j, (inner ℂ (v j) (operatorDiscrete μ a L l u (v j))).re) :
    k*(max (level-B) 0)^3 ≤
      (operatorDiagonalTrace b ((operatorDiscrete μ a L l u-operatorContinuous μ a L)^3)).re+
      (operatorDiagonalTrace b (operatorContinuous μ a L*
        (operatorDiscrete μ a L l u-operatorContinuous μ a L)^2)).re := by
  obtain ⟨hxH,hyH,hiH⟩ := operator_frequency_inputs μ (operatorCenteredMeasure l u L)
    (operator_centered_amplitude_measurable ha L) operator_centered_frequency_measurable
    (show 0 ≤ (1+|L|)*A by positivity) (operator_centered_amplitude_bound hA haA L)
  exact operator_nuclear_signed_spectral_comparison b (operatorDiscrete μ a L l u)
    (operatorContinuous μ a L) (operator_discrete_positive μ ha0 L l u)
    (operator_continuous_positive μ hi ha0 hL.le)
    (operatorCenteredMeasure l u L) volume hxH hyH hiH
    (operator_weighted_phase_measurable μ hi L) (operator_mellin_phase_measurable μ)
    (operator_continuous_norm_product μ hi L)
    (operator_centered_eq μ hi hl hL hs).symm rfl v hv hk hB hw


end Montgomery.RationalMoment
