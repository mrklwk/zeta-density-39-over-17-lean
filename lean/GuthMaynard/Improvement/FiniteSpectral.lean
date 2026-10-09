import Mathlib
set_option autoImplicit false
noncomputable section
open Matrix
namespace GuthMaynard.Improvement

/-- Genuine finite-matrix trace comparison in an eigenbasis of H. C need
not be diagonal or commute with H; H need not be positive. The extension to
an infinite compact self-adjoint operator remains a separate obligation. -/
theorem finite_negative_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (eigen : ι → ℝ)
    (hC : C.PosSemidef) (hG : (C+Matrix.diagonal eigen).PosSemidef) :
    (∑ i, (max (-eigen i) 0)^3) ≤ Matrix.trace (C * Matrix.diagonal eigen * Matrix.diagonal eigen) := by
  have hpoint : ∀ i, (max (-eigen i) 0)^3 ≤ C i i*(eigen i)^2 := by
    intro i
    have hc : 0 ≤ C i i := hC.diag_nonneg
    have hg : 0 ≤ C i i+eigen i := by simpa using (hG.diag_nonneg (i := i))
    by_cases hi : eigen i ≤ 0
    · rw [max_eq_left (by linarith)]
      nlinarith [mul_nonneg (sq_nonneg (eigen i)) hg]
    · rw [max_eq_right (by linarith)]
      simpa using mul_nonneg hc (sq_nonneg (eigen i))
  calc
    _ ≤ ∑ i, C i i*(eigen i)^2 := Finset.sum_le_sum (fun i _ => hpoint i)
    _ = _ := by simp [Matrix.trace,Matrix.mul_diagonal,pow_two,mul_assoc]

/-- Finite positive cubic trace is bounded by the absolute signed cubic
trace plus the controlled negative part. No commutation is used. -/
theorem finite_positive_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (eigen : ι → ℝ)
    (hC : C.PosSemidef) (hG : (C+Matrix.diagonal eigen).PosSemidef) :
    (∑ i, (max (eigen i) 0)^3) ≤ |∑ i, (eigen i)^3| +
      Matrix.trace (C * Matrix.diagonal eigen * Matrix.diagonal eigen) := by
  have heq : ∀ i, (max (eigen i) 0)^3 = (eigen i)^3+(max (-eigen i) 0)^3 := by
    intro i
    by_cases hi : 0 ≤ eigen i
    · rw [max_eq_left hi,max_eq_right (by linarith)]; ring
    · rw [max_eq_right (by linarith),max_eq_left (by linarith)]; ring
  simp_rw [heq]
  rw [Finset.sum_add_distrib]
  exact add_le_add (le_abs_self _) (finite_negative_trace C eigen hC hG)

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.finite_negative_trace
#print axioms GuthMaynard.Improvement.finite_positive_trace
