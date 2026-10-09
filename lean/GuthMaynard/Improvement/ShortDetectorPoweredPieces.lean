/- Adapted actual short coefficients; generic audited arithmetic and phases reused. -/
import MathCollab.Density.DetectorPoweredPieces
import GuthMaynard.Improvement.ShortDetectorConvolution

open Complex Set Filter MathCollab.Density
open scoped BigOperators Topology ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- Conjugation puts the actual powered coefficients into the positive-phase
convention of `detectingPolynomial`, without changing the zero ordinate. -/
def shortPoweredDetectorCoefficient (T : ℝ) (N j k : ℕ) (n : ℕ) : ℂ :=
  conj (((shortDetectorBlockCoefficients T N j)^k) n)

theorem shortDetectorBlockCoefficients_LSeries (T : ℝ) (N j : ℕ) (s : ℂ) :
    LSeries (shortDetectorBlockCoefficients T N j) s =
      ∑ n ∈ Finset.Ioc N (2*N), shortDetectorTaylorCoefficient T N j n*(n : ℂ)^(-s) := by
  rw [LSeries, tsum_eq_sum (s := Finset.Ioc N (2*N))]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [LSeries.term_def₀ (shortDetectorBlockCoefficients T N j).map_zero,
      shortDetectorBlockCoefficients_apply, ite_eq_left hn]
  · intro n hn
    rw [LSeries.term_def₀ (shortDetectorBlockCoefficients T N j).map_zero,
      shortDetectorBlockCoefficients_apply, ite_eq_right hn, zero_mul]

theorem norm_shortDetectorTaylorPolynomial_LSeries {N : ℕ} (hN : 0 < N)
    (T t : ℝ) (j : ℕ) :
    ‖shortDetectorTaylorPolynomial T N j t‖ =
      ‖LSeries (shortDetectorBlockCoefficients T N j) (Complex.I*(t : ℂ))‖ := by
  rw [shortDetectorTaylorPolynomial, norm_detectingPolynomial_eq_cpow_sum hN,
    shortDetectorBlockCoefficients_LSeries]

theorem shortDetectorBlockCoefficients_pow_LSeries_sum {N k : ℕ} (hN : 0 < N)
    (hk : 0 < k) (T : ℝ) (j : ℕ) (s : ℂ) :
    LSeries (fun n => ((shortDetectorBlockCoefficients T N j)^k) n) s =
      ∑ n ∈ Finset.Ioc (N^k) ((2*N)^k),
        ((shortDetectorBlockCoefficients T N j)^k) n*(n : ℂ)^(-s) := by
  rw [LSeries, tsum_eq_sum (s := Finset.Ioc (N^k) ((2*N)^k))]
  · apply Finset.sum_congr rfl
    intro n _
    rw [LSeries.term_def₀ ((shortDetectorBlockCoefficients T N j)^k).map_zero]
  · intro n hn
    rw [LSeries.term_def₀ ((shortDetectorBlockCoefficients T N j)^k).map_zero]
    have hz : ((shortDetectorBlockCoefficients T N j)^k) n = 0 := by
      by_contra hh
      have hu := (shortDetectorBlockCoefficients_pow_support T N j k n hh).2
      have hl : N^k < n := by
        obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
        exact shortDetectorBlockCoefficients_pow_lower hN T j l n hh
      exact hn (Finset.mem_Ioc.mpr ⟨hl, hu⟩)
    rw [hz, zero_mul]

/-- A powered component is detected on one of its k fixed dyadic pieces,
with exactly the pigeonhole loss k and at the same ordinate t. -/
theorem exists_shortPoweredDetector_piece {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    (T t : ℝ) (j : ℕ) :
    ∃ ℓ ∈ Finset.range k,
      ‖shortDetectorTaylorPolynomial T N j t‖^k/(k : ℝ) ≤
        ‖detectingPolynomial (2^ℓ*N^k) (shortPoweredDetectorCoefficient T N j k) t‖ := by
  let f := fun n : ℕ => ((shortDetectorBlockCoefficients T N j)^k) n*
    (n : ℂ)^(-(Complex.I*(t : ℂ)))
  have he : ‖shortDetectorTaylorPolynomial T N j t‖^k =
      ‖∑ ℓ ∈ Finset.range k, ∑ n ∈ Finset.Ioc (2^ℓ*N^k) (2*(2^ℓ*N^k)), f n‖ := by
    rw [norm_shortDetectorTaylorPolynomial_LSeries hN, ← norm_pow,
      ← shortDetectorBlockCoefficients_LSeries_pow,
      shortDetectorBlockCoefficients_pow_LSeries_sum hN hk, sum_scaled_dyadic_Ioc, mul_pow]
  have hn (ℓ : ℕ) : ‖detectingPolynomial (2^ℓ*N^k) (shortPoweredDetectorCoefficient T N j k) t‖ =
      ‖∑ n ∈ Finset.Ioc (2^ℓ*N^k) (2*(2^ℓ*N^k)), f n‖ := by
    change ‖detectingPolynomial _ (fun n => conj (((shortDetectorBlockCoefficients T N j)^k) n)) t‖ = _
    rw [norm_detectingPolynomial_conj,
      norm_detectingPolynomial_eq_cpow_sum (by positivity)]
  by_contra h
  push Not at h
  have hs : (∑ ℓ ∈ Finset.range k,
      ‖∑ n ∈ Finset.Ioc (2^ℓ*N^k) (2*(2^ℓ*N^k)), f n‖) <
      ‖shortDetectorTaylorPolynomial T N j t‖^k := by
    calc
      _ < ∑ _ℓ ∈ Finset.range k, ‖shortDetectorTaylorPolynomial T N j t‖^k/(k : ℝ) := by
        apply Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr hk⟩
        intro ℓ hℓ
        rw [← hn]
        exact h ℓ hℓ
      _ = _ := by simp; field_simp
  have hb := norm_sum_le (Finset.range k)
    (fun ℓ => ∑ n ∈ Finset.Ioc (2^ℓ*N^k) (2*(2^ℓ*N^k)), f n)
  rw [← he] at hb
  linarith

end GuthMaynard.Improvement

#print axioms GuthMaynard.Improvement.shortDetectorBlockCoefficients_LSeries
#print axioms GuthMaynard.Improvement.norm_shortDetectorTaylorPolynomial_LSeries
#print axioms GuthMaynard.Improvement.shortDetectorBlockCoefficients_pow_LSeries_sum
#print axioms GuthMaynard.Improvement.exists_shortPoweredDetector_piece
