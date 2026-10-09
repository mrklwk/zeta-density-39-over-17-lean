/- Adapted from audited Density proofs; reused scalar Taylor weights unchanged. -/
import GuthMaynard.Improvement.ShortDetectorDyadic

open Complex Set Filter MathCollab.Density
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- The fixed coefficients in the packet's Taylor family. Neither coordinate
of a zero occurs in this definition. -/
def shortDetectorTaylorCoefficient (T : ℝ) (N j n : ℕ) : ℂ :=
  shortDetectorCoefficient T n * (((2*(n : ℝ)/N-3 : ℝ) : ℂ)^j)

def shortDetectorTaylorPolynomial (T : ℝ) (N j : ℕ) (t : ℝ) : ℂ :=
  detectingPolynomial N (shortDetectorTaylorCoefficient T N j) (-t)

theorem norm_shortDetectorTaylorCoefficient_le {T : ℝ} {N n : ℕ}
    (hT : 0 < T) (hN : 0 < N) (hn : n ∈ Finset.Ioc N (2*N)) (j : ℕ) :
    ‖shortDetectorTaylorCoefficient T N j n‖ ≤ (n.divisors.card : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hlo : (N : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1.le
  have hhi : (n : ℝ) ≤ 2*N := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
  have hr : |2*(n : ℝ)/N-3| ≤ 1 := by
    apply abs_le.mpr
    have hl : (2 : ℝ) ≤ 2*(n : ℝ)/N := (le_div_iff₀ hNpos).2 (by linarith)
    have hh : 2*(n : ℝ)/N ≤ 4 := (div_le_iff₀ hNpos).2 (by linarith)
    constructor <;> linarith
  rw [shortDetectorTaylorCoefficient, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hp : |2*(n : ℝ)/N-3|^j ≤ 1 := pow_le_one₀ (abs_nonneg _) hr
  exact (mul_le_mul (shortDetectorCoefficient_norm_le hT n) hp (by positivity) (by positivity)).trans_eq (mul_one _)

/-- Uniform in the Taylor index and ordinate, before any beta approximation. -/
theorem norm_shortDetectorTaylorPolynomial_le {T : ℝ} {N : ℕ}
    (hT : 0 < T) (hN : 0 < N) (j : ℕ) (t : ℝ) :
    ‖shortDetectorTaylorPolynomial T N j t‖ ≤ 2*(N : ℝ)^2 := by
  unfold shortDetectorTaylorPolynomial detectingPolynomial
  calc
    _ ≤ ∑ n ∈ Finset.Ioc N (2*N), ‖shortDetectorTaylorCoefficient T N j n * dirichletPhase ((n : ℝ)/N) (-t)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Ioc N (2*N), (2*(N : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, norm_dirichletPhase, mul_one]
      have hc : (n.divisors.card : ℝ) ≤ n := by exact_mod_cast Nat.card_divisors_le_self n
      have hn' : (n : ℝ) ≤ 2*N := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
      exact (norm_shortDetectorTaylorCoefficient_le hT hN hn j).trans (hc.trans hn')
    _ = _ := by
      simp only [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
      rw [show 2*N-N = N by omega]
      ring

/-- The tail of the actual fixed polynomial family has geometric decay.
Identifying its full weighted series with the beta-dependent block is separate. -/
theorem norm_shortDetectorTaylor_tail_le {T β : ℝ} {N : ℕ}
    (hT : 0 < T) (hN : 0 < N) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (J : ℕ) (t : ℝ) :
    ‖∑' j : ℕ, (detectorTaylorWeight β (j+J) : ℂ)*shortDetectorTaylorPolynomial T N (j+J) t‖ ≤
      3*(N : ℝ)^2*(1/3 : ℝ)^J := by
  have hg := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/3)
    (by norm_num : (1/3 : ℝ) < 1)).mul_left (2*(N : ℝ)^2*(1/3 : ℝ)^J)
  have hb : ∀ j : ℕ, ‖(detectorTaylorWeight β (j+J) : ℂ)*shortDetectorTaylorPolynomial T N (j+J) t‖ ≤
      (2*(N : ℝ)^2*(1/3 : ℝ)^J)*(1/3 : ℝ)^j := by
    intro j
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ (1/3 : ℝ)^(j+J)*(2*(N : ℝ)^2) :=
        mul_le_mul (abs_detectorTaylorWeight_le hβ hβ' _) (norm_shortDetectorTaylorPolynomial_le hT hN _ _)
          (norm_nonneg _) (by positivity)
      _ = _ := by rw [pow_add]; ring
  have hn := hg.summable.of_nonneg_of_le (fun j => norm_nonneg _) hb
  calc
    _ ≤ ∑' j : ℕ, ‖(detectorTaylorWeight β (j+J) : ℂ)*shortDetectorTaylorPolynomial T N (j+J) t‖ := norm_tsum_le_tsum_norm hn
    _ ≤ _ := (hn.tsum_le_tsum hb hg.summable).trans_eq (by rw [hg.tsum_eq]; norm_num; ring)

end GuthMaynard.Improvement

#print axioms GuthMaynard.Improvement.norm_shortDetectorTaylorCoefficient_le
#print axioms GuthMaynard.Improvement.norm_shortDetectorTaylorPolynomial_le
#print axioms GuthMaynard.Improvement.norm_shortDetectorTaylor_tail_le
