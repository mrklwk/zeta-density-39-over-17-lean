module
public import GuthMaynard.Improvement.ShortDetectorPoweredPieces

@[expose] public section

open Real Complex Set Filter MathCollab.Density
open scoped BigOperators Topology ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- Conjugated genuine convolution coefficients retain uniform divisor growth. -/
theorem shortPoweredDetectorCoefficient_subpower {δ : ℝ} (hδ : 0 < δ)
    {K : ℕ} (hK : 0 < K) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (T : ℝ) (N j k n : ℕ),
      0 < T → 0 < N → k ≤ K → 0 < n →
        ‖shortPoweredDetectorCoefficient T N j k n‖ ≤ A*(n : ℝ)^δ := by
  obtain ⟨C, hC, hd⟩ := divisor_card_subpower (show 0 < δ/(2*K) by positivity)
  refine ⟨C^(2*K), one_le_pow₀ hC, ?_⟩
  intro T N j k n hT hN hk hn
  have hcard : (1 : ℝ) ≤ n.divisors.card := by
    have hc : 0 < n.divisors.card := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn.ne'⟩
    exact_mod_cast hc
  calc
    _ = ‖((shortDetectorBlockCoefficients T N j)^k) n‖ := norm_conj _
    _ ≤ (n.divisors.card : ℝ)^(2*k) := arithmeticFunction_pow_norm_le
      (shortDetectorBlockCoefficients_norm_le hT hN j) k n
    _ ≤ (n.divisors.card : ℝ)^(2*K) := pow_le_pow_right₀ hcard (by omega)
    _ ≤ (C*(n : ℝ)^(δ/(2*K)))^(2*K) := pow_le_pow_left₀ (by positivity) (hd n hn) _
    _ = C^(2*K)*(n : ℝ)^δ := by
      rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
      congr 2
      push_cast
      field_simp [show (K : ℝ) ≠ 0 by exact_mod_cast hK.ne']

/-- One threshold works before all block indices, powers and coefficients. -/
theorem shortPoweredDetectorCoefficient_eventually_le {η : ℝ} (hη : 0 < η)
    {K : ℕ} (hK : 0 < K) :
    ∀ᶠ T : ℝ in atTop, ∀ N j k n : ℕ,
      0 < N → k ≤ K → (n : ℝ) ≤ T^2 →
        ‖shortPoweredDetectorCoefficient T N j k n‖ ≤ T^η := by
  obtain ⟨A, hA, ha⟩ := shortPoweredDetectorCoefficient_subpower (show 0 < η/4 by positivity) hK
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (show 0 < η/2 by positivity)).eventually_ge_atTop A]
    with T hT hlarge
  intro N j k n hN hk hn
  by_cases hn0 : n = 0
  · subst n
    simp [shortPoweredDetectorCoefficient]
    positivity
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hTpos : 0 < T := by linarith
  calc
    _ ≤ A*(n : ℝ)^(η/4) := ha T N j k n hTpos hN hk hnpos
    _ ≤ A*(T^2)^(η/4) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg n) hn (by positivity)) (by linarith)
    _ = A*T^(η/2) := by
      rw [← Real.rpow_natCast_mul hTpos.le]
      congr 1
      congr 1
      norm_num
      ring
    _ ≤ T^(η/2)*T^(η/2) := mul_le_mul_of_nonneg_right hlarge (by positivity)
    _ = T^η := by rw [← Real.rpow_add hTpos]; congr 1; ring

/-- Coefficient normalization is fixed at T and eta, independently of the zero. -/
def shortNormalizedPoweredCoefficient (η T : ℝ) (N j k n : ℕ) : ℂ :=
  shortPoweredDetectorCoefficient T N j k n / ((T^η : ℝ) : ℂ)

theorem shortNormalizedPoweredCoefficient_eventually {η : ℝ} (hη : 0 < η)
    {K : ℕ} (hK : 0 < K) :
    ∀ᶠ T : ℝ in atTop, ∀ N j k n : ℕ,
      0 < N → k ≤ K → (n : ℝ) ≤ T^2 →
        ‖shortNormalizedPoweredCoefficient η T N j k n‖ ≤ 1 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), shortPoweredDetectorCoefficient_eventually_le hη hK]
    with T hT hb
  intro N j k n hN hk hn
  rw [shortNormalizedPoweredCoefficient, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (by linarith) _), div_le_one (by positivity)]
  exact hb N j k n hN hk hn

theorem detectingPolynomial_shortNormalizedPowered (η T t : ℝ) (N j k L : ℕ) :
    detectingPolynomial L (shortNormalizedPoweredCoefficient η T N j k) t =
      detectingPolynomial L (shortPoweredDetectorCoefficient T N j k) t/((T^η : ℝ) : ℂ) := by
  simp only [detectingPolynomial, shortNormalizedPoweredCoefficient, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  ring

end GuthMaynard.Improvement

#print axioms GuthMaynard.Improvement.shortPoweredDetectorCoefficient_subpower
#print axioms GuthMaynard.Improvement.shortPoweredDetectorCoefficient_eventually_le
#print axioms GuthMaynard.Improvement.shortNormalizedPoweredCoefficient_eventually
#print axioms GuthMaynard.Improvement.detectingPolynomial_shortNormalizedPowered
