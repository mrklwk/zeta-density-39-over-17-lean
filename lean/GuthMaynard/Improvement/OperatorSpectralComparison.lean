import GuthMaynard.Improvement.OperatorFiniteTrace
import GuthMaynard.Improvement.FiniteOperatorWitness
set_option autoImplicit false
noncomputable section
open MeasureTheory InnerProductSpace Filter Set
open scoped InnerProductSpace Topology
namespace GuthMaynard.Improvement
variable {E ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Powers act by powers of the actual eigenvalue. -/
theorem operator_eigenvector_pow (H : E →L[ℂ] E) {v : E} {e : ℝ}
    (he : H v = (e:ℂ) • v) (n : ℕ) : (H^n) v = (e:ℂ)^n • v := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [pow_succ', mul_apply_eq_comp, hn, map_smul, he, smul_smul, pow_succ]

/-- Cubic and mixed diagonals in an H eigenbasis. C need not preserve its eigenspaces. -/
theorem operator_eigenbasis_trace_values [Fintype ι] (b : OrthonormalBasis ι ℂ E)
    (H C : E →L[ℂ] E) (e : ι → ℝ) (he : ∀ i, H (b i) = (e i:ℂ) • b i) :
    (∑ i, inner ℂ (b i) ((H^3) (b i))) = ((∑ i, (e i)^3 : ℝ):ℂ) ∧
    (∑ i, inner ℂ (b i) ((C*H^2) (b i))).re =
      ∑ i, (inner ℂ (b i) (C (b i))).re*(e i)^2 := by
  constructor
  · rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [operator_eigenvector_pow H (he i), inner_smul_right, inner_self_eq_norm_sq_to_K,
      b.orthonormal.norm_eq_one]
    simp
  · rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_apply_eq_comp, operator_eigenvector_pow H (he i), map_smul, inner_smul_right]
    simp [← Complex.ofReal_pow, Complex.mul_re, mul_comm]

/-- Positive G and C give the required real diagonal comparison for H=G-C. -/
theorem operator_eigenbasis_diagonal_nonneg [Fintype ι] (b : OrthonormalBasis ι ℂ E)
    (G C : E →L[ℂ] E) (hG : G.IsPositive) (hC : C.IsPositive)
    (e : ι → ℝ) (he : ∀ i, (G-C) (b i) = (e i:ℂ) • b i) (i : ι) :
    0 ≤ (inner ℂ (b i) (C (b i))).re ∧
    0 ≤ (inner ℂ (b i) (C (b i))).re+e i := by
  refine ⟨hC.re_inner_nonneg_right _, ?_⟩
  have hg := hG.re_inner_nonneg_right (b i)
  have hv : G (b i) = C (b i)+(e i:ℂ) • b i := by
    have hh := he i
    change G (b i)-C (b i) = _ at hh
    rw [← hh]
    abel
  rw [hv, inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K,
    b.orthonormal.norm_eq_one] at hg
  simpa using hg

/-- Actual finite-dimensional operator spectral comparison, in any finite basis.
The H eigenbasis is constructed using the finite-dimensional spectral theorem. -/
theorem operator_finite_spectral_comparison [FiniteDimensional ℂ E]
    [Fintype ι] [Fintype κ] (d : OrthonormalBasis ι ℂ E)
    (G C : E →L[ℂ] E) (hG : G.IsPositive) (hC : C.IsPositive)
    (v : κ → E) (hv : Orthonormal ℂ v) {k a B : ℝ}
    (hk : (Fintype.card κ:ℝ) ≤ k) (hB : ‖C‖ ≤ B)
    (hw : k*a ≤ ∑ j, (inner ℂ (v j) (G (v j))).re) :
    k*(max (a-B) 0)^3 ≤
      ‖∑ i, inner ℂ (d i) (((G-C)^3) (d i))‖+
      (∑ i, inner ℂ (d i) ((C*(G-C)^2) (d i))).re := by
  let H := G-C
  have hs : H.toLinearMap.IsSymmetric := hG.isSymmetric.sub hC.isSymmetric
  let b := hs.eigenvectorBasis rfl
  let e := hs.eigenvalues rfl
  have he (i : Fin (Module.finrank ℂ E)) : H (b i) = (e i:ℂ) • b i :=
    hs.apply_eigenvectorBasis rfl i
  have hp := finite_operator_positive_cube b H C hs e he v hv hk hB
    (by simpa [H] using hw)
  have hd := finite_diagonal_positive_trace
    (fun i => (inner ℂ (b i) (C (b i))).re) e
    (fun i => (operator_eigenbasis_diagonal_nonneg b G C hG hC e he i).1)
    (fun i => (operator_eigenbasis_diagonal_nonneg b G C hG hC e he i).2)
  have hcubes := operator_eigenbasis_trace_values b H C e he
  have htrace (T : E →L[ℂ] E) :
      (∑ i, inner ℂ (d i) (T (d i))) = ∑ i, inner ℂ (b i) (T (b i)) := by
    exact (LinearMap.trace_eq_sum_inner T.toLinearMap d).symm.trans
      (LinearMap.trace_eq_sum_inner T.toLinearMap b)
  rw [htrace ((G-C)^3), htrace (C*(G-C)^2)]
  change k*(max (a-B) 0)^3 ≤ ‖∑ i, inner ℂ (b i) ((H^3) (b i))‖+
    (∑ i, inner ℂ (b i) ((C*H^2) (b i))).re
  rw [hcubes.1, hcubes.2, Complex.norm_real, Real.norm_eq_abs]
  exact hp.trans hd

/-- Actual finite compression comparison, with ambient trace on the right. -/
theorem operator_subspace_spectral_comparison [CompleteSpace E]
    (b : HilbertBasis ι ℂ E) (U : Submodule ℂ E) [FiniteDimensional ℂ U]
    [Fintype κ] (G C : E →L[ℂ] E) (hG : G.IsPositive) (hC : C.IsPositive)
    (v : κ → E) (hv : Orthonormal ℂ v) (hvU : ∀ j, v j ∈ U)
    {k a B : ℝ} (hk : (Fintype.card κ:ℝ) ≤ k) (hB : ‖C‖ ≤ B)
    (hw : k*a ≤ ∑ j, (inner ℂ (v j) (G (v j))).re) :
    k*(max (a-B) 0)^3 ≤
      ‖operatorDiagonalTrace b ((U.starProjection*(G-C)*U.starProjection)^3)‖+
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
  have hh := operator_finite_spectral_comparison d
    (operatorSubspaceCompression U G) (operatorSubspaceCompression U C) hcG hcC w hwO hk
    ((operator_subspace_compression_norm U C).trans hB)
    (by simpa only [operator_subspace_compression_pairing, w] using hw)
  rw [operator_subspace_cubic_trace b U d, operator_subspace_mixed_trace b U d]
  simpa only [operator_subspace_compression_sub] using hh

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.operator_eigenvector_pow
#print axioms GuthMaynard.Improvement.operator_eigenbasis_trace_values
#print axioms GuthMaynard.Improvement.operator_eigenbasis_diagonal_nonneg

#print axioms GuthMaynard.Improvement.operator_finite_spectral_comparison
#print axioms GuthMaynard.Improvement.operator_subspace_spectral_comparison
