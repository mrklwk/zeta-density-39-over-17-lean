import GuthMaynard.Improvement.FiniteSpectral
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- Weighted convexity for positive cubic eigenvalues. The total witness
weight may be strictly less than k; no padding of the Hilbert space is needed. -/
theorem finite_weighted_positive_cube {ι : Type*} [Fintype ι]
    (α e : ι → ℝ) {k d : ℝ}
    (hα : ∀ i, 0 ≤ α i) (hα1 : ∀ i, α i ≤ 1)
    (hmass : ∑ i, α i ≤ k) (hwitness : k*d ≤ ∑ i, α i*e i) :
    k*(max d 0)^3 ≤ ∑ i, (max (e i) 0)^3 := by
  by_cases hd : d ≤ 0
  · rw [max_eq_right hd]
    simp only [zero_pow (by decide : 3 ≠ 0), mul_zero]
    exact Finset.sum_nonneg fun i _ => by positivity
  have hdp : 0 < d := lt_of_not_ge hd
  rw [max_eq_left hdp.le]
  have hlinear : k*d ≤ ∑ i, α i*max (e i) 0 :=
    hwitness.trans (Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (le_max_left _ _) (hα i))
  have htangent (i : ι) :
      α i*(3*d^2*max (e i) 0-2*d^3) ≤ α i*(max (e i) 0)^3 := by
    apply mul_le_mul_of_nonneg_left _ (hα i)
    nlinarith [mul_nonneg (sq_nonneg (max (e i) 0-d))
      (show 0 ≤ max (e i) 0+2*d by positivity)]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => htangent i)
  have hid : (∑ i, α i*(3*d^2*max (e i) 0-2*d^3)) =
      3*d^2*(∑ i, α i*max (e i) 0)-2*d^3*(∑ i, α i) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
  rw [hid] at hsum
  have hm := mul_le_mul_of_nonneg_left hmass (show 0 ≤ 2*d^3 by positivity)
  have hl := mul_le_mul_of_nonneg_left hlinear (show 0 ≤ 3*d^2 by positivity)
  have hcube : k*d^3 ≤ ∑ i, α i*(max (e i) 0)^3 := by nlinarith
  exact hcube.trans (Finset.sum_le_sum fun i _ => by
    simpa using mul_le_mul_of_nonneg_right (hα1 i)
      (show 0 ≤ (max (e i) 0)^3 by positivity))

/-- Only diagonal positivity is needed for the finite negative cube bound.
These hypotheses are supplied by positive G,C in an H-eigenbasis. -/
theorem finite_diagonal_positive_trace {ι : Type*} [Fintype ι]
    (c e : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (hg : ∀ i, 0 ≤ c i+e i) :
    (∑ i, (max (e i) 0)^3) ≤ |∑ i, (e i)^3|+∑ i, c i*(e i)^2 := by
  have hp (i : ι) : (max (e i) 0)^3 ≤ (e i)^3+c i*(e i)^2 := by
    by_cases he : 0 ≤ e i
    · rw [max_eq_left he]
      nlinarith [mul_nonneg (hc i) (sq_nonneg (e i))]
    · rw [max_eq_right (le_of_not_ge he)]
      nlinarith [mul_nonneg (hg i) (sq_nonneg (e i))]
  calc
    _ ≤ ∑ i, ((e i)^3+c i*(e i)^2) := Finset.sum_le_sum fun i _ => hp i
    _ = (∑ i, (e i)^3)+∑ i, c i*(e i)^2 := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (le_abs_self (∑ i, (e i)^3)) le_rfl

/-- Finite spectral comparison from explicit orthogonal-witness weights.
Neither H positivity nor commutation with C appears in the contract. -/
theorem finite_weighted_spectral_comparison {ι : Type*} [Fintype ι]
    (α c e : ι → ℝ) {k v B : ℝ}
    (hα : ∀ i, 0 ≤ α i) (hα1 : ∀ i, α i ≤ 1)
    (hmass : ∑ i, α i ≤ k) (hwitness : k*(v-B) ≤ ∑ i, α i*e i)
    (hc : ∀ i, 0 ≤ c i) (hg : ∀ i, 0 ≤ c i+e i) :
    k*(max (v-B) 0)^3 ≤ |∑ i, (e i)^3|+∑ i, c i*(e i)^2 :=
  (finite_weighted_positive_cube α e hα hα1 hmass hwitness).trans
    (finite_diagonal_positive_trace c e hc hg)

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.finite_weighted_positive_cube
#print axioms GuthMaynard.Improvement.finite_diagonal_positive_trace
#print axioms GuthMaynard.Improvement.finite_weighted_spectral_comparison
