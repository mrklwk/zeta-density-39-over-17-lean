/- Adapted from audited Density proofs; reused scalar Taylor weights unchanged. -/
import MathCollab.Density.DetectorBlockExpansion
import GuthMaynard.Improvement.ShortDetectorTaylorFamily

open Complex Set Filter MathCollab.Density
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

def normalizedShortDetectorBlock (ρ : ℂ) (T : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2*N), shortDetectorCoefficient T n *
    ((((n : ℝ)/N)^(-ρ.re) : ℝ) : ℂ)*dirichletPhase ((n : ℝ)/N) (-ρ.im)

/-- Exact rescaling, including the unit phase of N; no ordinate is shifted. -/
theorem shortDetectorBlock_eq_normalized {N : ℕ} (hN : 0 < N) (ρ : ℂ) (T : ℝ) :
    shortDetectorBlock ρ T N = (N : ℂ)^(-ρ)*normalizedShortDetectorBlock ρ T N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [shortDetectorBlock, normalizedShortDetectorBlock, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_trans hN (Finset.mem_Ioc.mp hn).1)
  have hsplit : (n : ℂ)^(-ρ) = (N : ℂ)^(-ρ)*(((n : ℝ)/N : ℝ) : ℂ)^(-ρ) := by
    have hh := Complex.mul_cpow_ofReal_nonneg hNpos.le (div_nonneg hnpos.le hNpos.le) (-ρ)
    have hm : ((N : ℝ) : ℂ)*(((n : ℝ)/N : ℝ) : ℂ) = (n : ℂ) := by
      push_cast
      field_simp [show (N : ℂ) ≠ 0 by exact_mod_cast hN.ne']
    rw [hm, Complex.ofReal_natCast] at hh
    exact hh
  rw [hsplit, cpow_neg_eq_real_phase (div_pos hnpos hNpos)]
  ring

theorem norm_normalizedShortDetectorBlock {N : ℕ} (hN : 0 < N) (ρ : ℂ) (T : ℝ) :
    ‖normalizedShortDetectorBlock ρ T N‖ = (N : ℝ)^ρ.re*‖shortDetectorBlock ρ T N‖ := by
  rw [shortDetectorBlock_eq_normalized hN, norm_mul, Complex.norm_natCast_cpow_of_pos hN, Complex.neg_re]
  rw [← mul_assoc, ← Real.rpow_add (by exact_mod_cast hN : (0 : ℝ) < N)]
  simp

/-- Genuine summation and finite-sum interchange for the fixed Taylor family. -/
theorem hasSum_shortDetectorTaylorPolynomial {N : ℕ} (hN : 0 < N) (ρ : ℂ) (T : ℝ) :
    HasSum (fun j : ℕ => (detectorTaylorWeight ρ.re j : ℂ)*shortDetectorTaylorPolynomial T N j ρ.im)
      ((((3/2 : ℝ)^ρ.re : ℝ) : ℂ)*normalizedShortDetectorBlock ρ T N) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hterm : ∀ n ∈ Finset.Ioc N (2*N),
      HasSum (fun j : ℕ => (detectorTaylorWeight ρ.re j : ℂ)*
        (shortDetectorCoefficient T n * (((2*(n : ℝ)/N-3 : ℝ) : ℂ)^j) *
          dirichletPhase ((n : ℝ)/N) (-ρ.im)))
        ((((3/2 : ℝ)^ρ.re : ℝ) : ℂ)*(shortDetectorCoefficient T n *
          ((((n : ℝ)/N)^(-ρ.re) : ℝ) : ℂ)*dirichletPhase ((n : ℝ)/N) (-ρ.im))) := by
    intro n hn
    have hlo : (1 : ℝ) ≤ (n : ℝ)/N := (le_div_iff₀ hNpos).2 (by simpa using (show (N : ℝ) ≤ n by exact_mod_cast (Finset.mem_Ioc.mp hn).1.le))
    have hhi : (n : ℝ)/N ≤ 2 := (div_le_iff₀ hNpos).2 (by exact_mod_cast (Finset.mem_Ioc.mp hn).2)
    have hs := hasSum_detector_binomial (β := ρ.re) hlo hhi
    have he : (2*((n : ℝ)/N)/3)^(-ρ.re) = (3/2 : ℝ)^ρ.re*((n : ℝ)/N)^(-ρ.re) := by
      rw [show 2*((n : ℝ)/N)/3 = ((n : ℝ)/N)/(3/2) by ring,
        Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (show (0 : ℝ) ≤ 3/2 by norm_num), div_inv_eq_mul]
      ring
    rw [he] at hs
    have hc := (hs.map Complex.ofRealCLM Complex.continuous_ofReal).mul_left
      (shortDetectorCoefficient T n*dirichletPhase ((n : ℝ)/N) (-ρ.im))
    convert hc using 1
    · funext j
      simp only [Function.comp_apply, Complex.ofRealCLM_apply, Complex.ofReal_mul, Complex.ofReal_pow]
      push_cast
      ring
    · simp only [Complex.ofRealCLM_apply, Complex.ofReal_mul]
      ring
  have hs := hasSum_sum hterm
  convert hs using 1
  · funext j
    simp [shortDetectorTaylorPolynomial, detectingPolynomial, shortDetectorTaylorCoefficient, Finset.mul_sum]
  · rw [normalizedShortDetectorBlock, Finset.mul_sum]

/-- The full Taylor combination is at least the beta-rescaled original block. -/
theorem norm_shortDetectorTaylor_tsum_ge {N : ℕ} (hN : 0 < N) {ρ : ℂ} (hβ : 0 ≤ ρ.re) (T : ℝ) :
    (N : ℝ)^ρ.re*‖shortDetectorBlock ρ T N‖ ≤
      ‖∑' j : ℕ, (detectorTaylorWeight ρ.re j : ℂ)*shortDetectorTaylorPolynomial T N j ρ.im‖ := by
  rw [(hasSum_shortDetectorTaylorPolynomial hN ρ T).tsum_eq, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_normalizedShortDetectorBlock hN]
  have hpow : (1 : ℝ) ≤ (3/2 : ℝ)^ρ.re := Real.one_le_rpow (by norm_num) hβ
  nlinarith [show 0 ≤ (N : ℝ)^ρ.re*‖shortDetectorBlock ρ T N‖ by positivity]

end GuthMaynard.Improvement

#print axioms GuthMaynard.Improvement.shortDetectorBlock_eq_normalized
#print axioms GuthMaynard.Improvement.norm_normalizedShortDetectorBlock
#print axioms GuthMaynard.Improvement.hasSum_shortDetectorTaylorPolynomial
#print axioms GuthMaynard.Improvement.norm_shortDetectorTaylor_tsum_ge
