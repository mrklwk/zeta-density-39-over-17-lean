/- Adapted actual short coefficients; generic audited arithmetic and phases reused. -/
import MathCollab.Density.DetectorConvolution
import GuthMaynard.Improvement.ShortFixedDetectorFamily

open Complex Set Filter MathCollab.Density
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- The actual block coefficients as a finite arithmetic function. -/
def shortDetectorBlockCoefficients (T : ℝ) (N j : ℕ) : ArithmeticFunction ℂ where
  toFun n := if n ∈ Finset.Ioc N (2*N) then shortDetectorTaylorCoefficient T N j n else 0
  map_zero' := by simp

theorem shortDetectorBlockCoefficients_apply (T : ℝ) (N j n : ℕ) :
    shortDetectorBlockCoefficients T N j n =
      if n ∈ Finset.Ioc N (2*N) then shortDetectorTaylorCoefficient T N j n else 0 := rfl

theorem shortDetectorBlockCoefficients_norm_le {T : ℝ} {N : ℕ}
    (hT : 0 < T) (hN : 0 < N) (j n : ℕ) :
    ‖shortDetectorBlockCoefficients T N j n‖ ≤ (n.divisors.card : ℝ) := by
  rw [shortDetectorBlockCoefficients_apply]
  split_ifs with hn
  · exact norm_shortDetectorTaylorCoefficient_le hT hN hn j
  · simp

/-- Every nonzero convolution coefficient has the literal product support. -/
theorem shortDetectorBlockCoefficients_pow_support (T : ℝ) (N j k n : ℕ)
    (hn : ((shortDetectorBlockCoefficients T N j)^k) n ≠ 0) :
    0 < n ∧ n ≤ (2*N)^k := by
  induction k generalizing n with
  | zero =>
    simp only [pow_zero, ArithmeticFunction.one_apply] at hn
    split_ifs at hn with he
    · subst n; simp
    · exact False.elim (hn rfl)
  | succ k ih =>
    rw [pow_succ, ArithmeticFunction.mul_apply] at hn
    obtain ⟨p, hp, hmul⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
    have ha : ((shortDetectorBlockCoefficients T N j)^k) p.1 ≠ 0 := left_ne_zero_of_mul hmul
    have hb : shortDetectorBlockCoefficients T N j p.2 ≠ 0 := right_ne_zero_of_mul hmul
    have hmem : p.2 ∈ Finset.Ioc N (2*N) := by
      by_contra h
      exact hb (by simp [shortDetectorBlockCoefficients_apply, h])
    have hi := ih p.1 ha
    have he := (Nat.mem_divisorsAntidiagonal.mp hp).1
    refine ⟨Nat.pos_of_ne_zero (Nat.mem_divisorsAntidiagonal.mp hp).2, ?_⟩
    rw [← he, pow_succ]
    exact Nat.mul_le_mul hi.2 (Finset.mem_Ioc.mp hmem).2

theorem shortDetectorBlockCoefficients_pow_lower {N : ℕ} (hN : 0 < N)
    (T : ℝ) (j k n : ℕ) (hn : ((shortDetectorBlockCoefficients T N j)^(k+1)) n ≠ 0) :
    N^(k+1) < n := by
  induction k generalizing n with
  | zero =>
    simp only [zero_add, pow_one] at hn ⊢
    have hmem : n ∈ Finset.Ioc N (2*N) := by
      by_contra h
      exact hn (by simp [shortDetectorBlockCoefficients_apply, h])
    exact (Finset.mem_Ioc.mp hmem).1
  | succ k ih =>
    rw [pow_succ, ArithmeticFunction.mul_apply] at hn
    obtain ⟨p, hp, hmul⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
    have ha := ih p.1 (left_ne_zero_of_mul hmul)
    have hb : shortDetectorBlockCoefficients T N j p.2 ≠ 0 := right_ne_zero_of_mul hmul
    have hmem : p.2 ∈ Finset.Ioc N (2*N) := by
      by_contra h
      exact hb (by simp [shortDetectorBlockCoefficients_apply, h])
    rw [← (Nat.mem_divisorsAntidiagonal.mp hp).1, pow_succ]
    exact Nat.mul_lt_mul_of_pos_right ha hN |>.trans_le (Nat.mul_le_mul_left _ (Finset.mem_Ioc.mp hmem).1.le)

/-- Finite support, proved for the actual powers, gives absolute convergence. -/
theorem shortDetectorBlockCoefficients_pow_LSeriesSummable (T : ℝ) (N j k : ℕ) (s : ℂ) :
    LSeriesSummable (fun n => ((shortDetectorBlockCoefficients T N j)^k) n) s := by
  unfold LSeriesSummable
  apply summable_of_hasFiniteSupport
  apply Set.Finite.subset (Finset.range ((2*N)^k+1)).finite_toSet
  intro n hn
  apply Finset.mem_range.mpr
  by_contra h
  have hz : ((shortDetectorBlockCoefficients T N j)^k) n = 0 := by
    by_contra hh
    have hi := shortDetectorBlockCoefficients_pow_support T N j k n hh
    omega
  have ht : LSeries.term (fun n => ((shortDetectorBlockCoefficients T N j)^k) n) s n = 0 := by
    rw [LSeries.term_def₀ ((shortDetectorBlockCoefficients T N j)^k).map_zero]
    simp [hz]
  exact hn ht

/-- The finite L-series of the convolution power is the literal k-th power. -/
theorem shortDetectorBlockCoefficients_LSeries_pow (T : ℝ) (N j k : ℕ) (s : ℂ) :
    LSeries (fun n => ((shortDetectorBlockCoefficients T N j)^k) n) s =
      (LSeries (shortDetectorBlockCoefficients T N j) s)^k := by
  induction k with
  | zero =>
    simp only [pow_zero]
    rw [LSeries, tsum_eq_single 1]
    · simp [ArithmeticFunction.one_apply]
    · intro n hn
      simp [LSeries.term_def, ArithmeticFunction.one_apply, hn]
  | succ k ih =>
    rw [pow_succ, ArithmeticFunction.LSeries_mul'
      (shortDetectorBlockCoefficients_pow_LSeriesSummable T N j k s)
      (by simpa using shortDetectorBlockCoefficients_pow_LSeriesSummable T N j 1 s), ih, pow_succ]

end GuthMaynard.Improvement

#print axioms GuthMaynard.Improvement.shortDetectorBlockCoefficients_apply
#print axioms GuthMaynard.Improvement.shortDetectorBlockCoefficients_norm_le
#print axioms GuthMaynard.Improvement.shortDetectorBlockCoefficients_pow_support
#print axioms GuthMaynard.Improvement.shortDetectorBlockCoefficients_pow_lower
#print axioms GuthMaynard.Improvement.shortDetectorBlockCoefficients_pow_LSeriesSummable
#print axioms GuthMaynard.Improvement.shortDetectorBlockCoefficients_LSeries_pow
