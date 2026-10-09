import GuthMaynard.Improvement.FiniteSpectralWitness
set_option autoImplicit false
noncomputable section
open InnerProductSpace
open scoped InnerProductSpace
namespace GuthMaynard.Improvement
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def finiteWitnessWeight (b : OrthonormalBasis ι ℂ E) (v : κ → E) (i : ι) : ℝ :=
  ∑ j, ‖inner ℂ (b i) (v j)‖^2

theorem finiteWitnessWeight_bounds (b : OrthonormalBasis ι ℂ E) {v : κ → E}
    (hv : Orthonormal ℂ v) (i : ι) :
    0 ≤ finiteWitnessWeight b v i ∧ finiteWitnessWeight b v i ≤ 1 := by
  refine ⟨Finset.sum_nonneg (fun _ _ => sq_nonneg _), ?_⟩
  have hh := hv.sum_inner_products_le (s := Finset.univ) (b i)
  unfold finiteWitnessWeight
  simp_rw [norm_inner_symm (b i)]
  simpa only [b.orthonormal.norm_eq_one, one_pow] using hh

theorem finiteWitnessWeight_sum (b : OrthonormalBasis ι ℂ E) {v : κ → E}
    (hv : Orthonormal ℂ v) : ∑ i, finiteWitnessWeight b v i = Fintype.card κ := by
  unfold finiteWitnessWeight
  rw [Finset.sum_comm]
  simp_rw [b.sum_sq_norm_inner_right, hv.norm_eq_one]
  simp

theorem finite_eigenbasis_quadratic (b : OrthonormalBasis ι ℂ E)
    (H : E →L[ℂ] E) (hs : H.toLinearMap.IsSymmetric) (e : ι → ℝ)
    (he : ∀ i, H (b i) = (e i:ℂ) • b i) (v : E) :
    (inner ℂ v (H v)).re = ∑ i, e i*‖inner ℂ (b i) v‖^2 := by
  rw [← b.sum_inner_mul_inner v (H v), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hsi : inner ℂ (H (b i)) v = inner ℂ (b i) (H v) := hs (b i) v
  rw [← hsi, he i, inner_smul_left]
  simp only [Complex.conj_ofReal]
  have hn : (inner ℂ v (b i)*inner ℂ (b i) v).re = ‖inner ℂ (b i) v‖^2 := by
    change RCLike.re (inner ℂ v (b i)*inner ℂ (b i) v) = _
    rw [inner_mul_symm_re_eq_norm (𝕜 := ℂ), norm_mul, norm_inner_symm v (b i), pow_two]
  calc
    _ = ((e i:ℂ)*(inner ℂ v (b i)*inner ℂ (b i) v)).re := by congr 1; ring
    _ = _ := by rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hn]

theorem finite_eigenbasis_witness_sum (b : OrthonormalBasis ι ℂ E)
    (H : E →L[ℂ] E) (hs : H.toLinearMap.IsSymmetric) (e : ι → ℝ)
    (he : ∀ i, H (b i) = (e i:ℂ) • b i) (v : κ → E) :
    (∑ j, (inner ℂ (v j) (H (v j))).re) = ∑ i, finiteWitnessWeight b v i*e i := by
  simp_rw [finite_eigenbasis_quadratic b H hs e he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [finiteWitnessWeight, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- An actual orthonormal witness for G=H+C forces the positive cubic
spectral mass. C enters only through its operator norm at this stage. -/
theorem finite_operator_positive_cube (b : OrthonormalBasis ι ℂ E)
    (H C : E →L[ℂ] E) (hs : H.toLinearMap.IsSymmetric) (e : ι → ℝ)
    (he : ∀ i, H (b i) = (e i:ℂ) • b i) (v : κ → E)
    (hv : Orthonormal ℂ v) {k a B : ℝ} (hk : (Fintype.card κ:ℝ) ≤ k)
    (hB : ‖C‖ ≤ B)
    (hw : k*a ≤ ∑ j, (inner ℂ (v j) ((H+C) (v j))).re) :
    k*(max (a-B) 0)^3 ≤ ∑ i, (max (e i) 0)^3 := by
  have hB0 : 0 ≤ B := (norm_nonneg C).trans hB
  have hc (j : κ) : (inner ℂ (v j) (C (v j))).re ≤ B := by
    calc
      _ ≤ ‖v j‖*‖C (v j)‖ := re_inner_le_norm (𝕜 := ℂ) _ _
      _ ≤ ‖v j‖*(‖C‖*‖v j‖) := mul_le_mul_of_nonneg_left (C.le_opNorm _) (norm_nonneg _)
      _ ≤ B := by simpa only [hv.norm_eq_one, one_mul, mul_one] using hB
  have hcs : (∑ j, (inner ℂ (v j) (C (v j))).re) ≤ k*B := by
    calc
      _ ≤ ∑ _j : κ, B := Finset.sum_le_sum fun j _ => hc j
      _ = (Fintype.card κ:ℝ)*B := by simp
      _ ≤ k*B := mul_le_mul_of_nonneg_right hk hB0
  have hadd : (∑ j, (inner ℂ (v j) ((H+C) (v j))).re) =
      (∑ j, (inner ℂ (v j) (H (v j))).re)+(∑ j, (inner ℂ (v j) (C (v j))).re) := by
    simp only [add_apply, inner_add_right, Complex.add_re, Finset.sum_add_distrib]
  rw [hadd] at hw
  have hwe : k*(a-B) ≤ ∑ i, finiteWitnessWeight b v i*e i := by
    rw [← finite_eigenbasis_witness_sum b H hs e he v]
    linarith
  exact finite_weighted_positive_cube (finiteWitnessWeight b v) e
    (fun i => (finiteWitnessWeight_bounds b hv i).1)
    (fun i => (finiteWitnessWeight_bounds b hv i).2)
    (by rw [finiteWitnessWeight_sum b hv]; exact hk) hwe

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.finiteWitnessWeight_bounds
#print axioms GuthMaynard.Improvement.finiteWitnessWeight_sum
#print axioms GuthMaynard.Improvement.finite_eigenbasis_quadratic
#print axioms GuthMaynard.Improvement.finite_eigenbasis_witness_sum

#print axioms GuthMaynard.Improvement.finite_operator_positive_cube
