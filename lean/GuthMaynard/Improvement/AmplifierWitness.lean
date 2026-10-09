module
public import GuthMaynard.Improvement.AmplifierOperator

@[expose] public section
set_option autoImplicit false
noncomputable section
open InnerProductSpace
open scoped InnerProductSpace
namespace GuthMaynard.Improvement
variable {E ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Fintype ι] [Fintype κ]

/-- Construct the witness from the actual finite-dimensional range of BA.
No rank, quantitative witness, or Hilbert--Schmidt inequality is assumed. -/
theorem amplifier_range_witness
    (A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ κ)
    (B : EuclideanSpace ℂ κ →L[ℂ] E) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧ ∃ v : Fin r → E,
      Orthonormal ℂ v ∧
      (∑ q : ι, ‖B (A (EuclideanSpace.basisFun ι ℂ q))‖^2) ≤
        ‖A‖^2 * (∑ j, (inner ℂ (v j) (B (B.adjoint (v j)))).re) := by
  classical
  let W := LinearMap.range (B.comp A).toLinearMap
  let b := stdOrthonormalBasis ℂ W
  let v : Fin (Module.finrank ℂ W) → E := fun j => (b j : E)
  have hv : Orthonormal ℂ v := b.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  have hr : Module.finrank ℂ W ≤ Fintype.card ι := by
    exact (B.comp A).toLinearMap.finrank_range_le.trans_eq finrank_euclideanSpace
  refine ⟨Module.finrank ℂ W,hr,v,hv,?_⟩
  have hp (q : ι) : ‖B (A (EuclideanSpace.basisFun ι ℂ q))‖^2 =
      ∑ j, ‖inner ℂ (v j) (B (A (EuclideanSpace.basisFun ι ℂ q)))‖^2 := by
    let y : W := ⟨B (A (EuclideanSpace.basisFun ι ℂ q)),
      ⟨EuclideanSpace.basisFun ι ℂ q,rfl⟩⟩
    exact (b.sum_sq_norm_inner_right y).symm
  simp_rw [hp]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have he : (∑ q : ι, ‖inner ℂ (v j) (B (A (EuclideanSpace.basisFun ι ℂ q)))‖^2) =
      ‖A.adjoint (B.adjoint (v j))‖^2 := by
    simp_rw [← B.adjoint_inner_left,← A.adjoint_inner_left]
    exact (EuclideanSpace.basisFun ι ℂ).sum_sq_norm_inner_left _
  rw [he]
  have hn := A.adjoint.le_opNorm (B.adjoint (v j))
  rw [ContinuousLinearMap.adjoint.norm_map] at hn
  have hg : (inner ℂ (v j) (B (B.adjoint (v j)))).re = ‖B.adjoint (v j)‖^2 := by
    rw [← B.adjoint_inner_left,inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hg,← mul_pow]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg A) (norm_nonneg _))).mpr hn

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.amplifier_range_witness
