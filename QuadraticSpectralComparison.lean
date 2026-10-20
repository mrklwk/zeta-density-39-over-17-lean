module
public import FiniteCutoffOperators

@[expose] public section

set_option autoImplicit false
noncomputable section
open InnerProductSpace
open scoped InnerProductSpace
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement

/-- Weighted square convexity. Signed eigenvalues are retained. -/
theorem finite_weighted_positive_square {ι : Type*} [Fintype ι]
    (α e : ι → ℝ) {k d : ℝ}
    (hα : ∀ i, 0 ≤ α i) (hα1 : ∀ i, α i ≤ 1)
    (hmass : ∑ i, α i ≤ k) (hwitness : k*d ≤ ∑ i, α i*e i) :
    k*(max d 0)^2 ≤ ∑ i, (e i)^2 := by
  by_cases hd : d ≤ 0
  · rw [max_eq_right hd]
    simp only [zero_pow (by decide : 2 ≠ 0),mul_zero]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hdp : 0 < d := lt_of_not_ge hd
  rw [max_eq_left hdp.le]
  have htangent (i : ι) : α i*(2*d*e i-d^2) ≤ α i*(e i)^2 := by
    exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (e i-d)]) (hα i)
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => htangent i)
  have hid : (∑ i, α i*(2*d*e i-d^2)) =
      2*d*(∑ i, α i*e i)-d^2*(∑ i, α i) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,Finset.mul_sum,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
  rw [hid] at hsum
  have hm := mul_le_mul_of_nonneg_left hmass (sq_nonneg d)
  have hl := mul_le_mul_of_nonneg_left hwitness (show 0 ≤ 2*d by positivity)
  have hs : k*d^2 ≤ ∑ i, α i*(e i)^2 := by nlinarith
  exact hs.trans (Finset.sum_le_sum (fun i _ => by
    simpa using mul_le_mul_of_nonneg_right (hα1 i) (sq_nonneg (e i))))

variable {E ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [Fintype ι] [Fintype κ]

/-- An actual orthonormal witness for G=H+C forces the positive cubic
spectral mass. C enters only through its operator norm at this stage. -/
theorem finite_operator_positive_square (b : OrthonormalBasis ι ℂ E)
    (H C : E →L[ℂ] E) (hs : H.toLinearMap.IsSymmetric) (e : ι → ℝ)
    (he : ∀ i, H (b i) = (e i:ℂ) • b i) (v : κ → E)
    (hv : Orthonormal ℂ v) {k a B : ℝ} (hk : (Fintype.card κ:ℝ) ≤ k)
    (hB : ‖C‖ ≤ B)
    (hw : k*a ≤ ∑ j, (inner ℂ (v j) ((H+C) (v j))).re) :
    k*(max (a-B) 0)^2 ≤ ∑ i, (e i)^2 := by
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
  exact finite_weighted_positive_square (finiteWitnessWeight b v) e
    (fun i => (finiteWitnessWeight_bounds b hv i).1)
    (fun i => (finiteWitnessWeight_bounds b hv i).2)
    (by rw [finiteWitnessWeight_sum b hv]; exact hk) hwe


/-- The centered operator is Hermitian; no positivity of H is required. -/
theorem operator_finite_quadratic_comparison [FiniteDimensional ℂ E]
    (d : OrthonormalBasis ι ℂ E)
    (G C : E →L[ℂ] E) (hG : G.IsPositive) (hC : C.IsPositive)
    (v : κ → E) (hv : Orthonormal ℂ v) {k a B : ℝ}
    (hk : (Fintype.card κ:ℝ) ≤ k) (hB : ‖C‖ ≤ B)
    (hw : k*a ≤ ∑ j, (inner ℂ (v j) (G (v j))).re) :
    k*(max (a-B) 0)^2 ≤ (∑ i, inner ℂ (d i) (((G-C)^2) (d i))).re := by
  let H := G-C
  have hs : H.toLinearMap.IsSymmetric := hG.isSymmetric.sub hC.isSymmetric
  let b := hs.eigenvectorBasis rfl
  let e := hs.eigenvalues rfl
  have he (i : Fin (Module.finrank ℂ E)) : H (b i) = (e i:ℂ) • b i :=
    hs.apply_eigenvectorBasis rfl i
  have hp := finite_operator_positive_square b H C hs e he v hv hk hB
    (by simpa [H] using hw)
  have htrace : (∑ i, inner ℂ (d i) ((H^2) (d i))) =
      ∑ i, inner ℂ (b i) ((H^2) (b i)) := by
    exact (LinearMap.trace_eq_sum_inner (H^2).toLinearMap d).symm.trans
      (LinearMap.trace_eq_sum_inner (H^2).toLinearMap b)
  change _ ≤ (∑ i, inner ℂ (d i) ((H^2) (d i))).re
  rw [htrace,Complex.re_sum]
  have hdiag (i : Fin (Module.finrank ℂ E)) :
      (inner ℂ (b i) ((H^2) (b i))).re=(e i)^2 := by
    rw [operator_eigenvector_pow H (he i),inner_smul_right,inner_self_eq_norm_sq_to_K,
      b.orthonormal.norm_eq_one]
    simp [← Complex.ofReal_pow]
  simpa only [hdiag] using hp

end Montgomery.RationalMoment
