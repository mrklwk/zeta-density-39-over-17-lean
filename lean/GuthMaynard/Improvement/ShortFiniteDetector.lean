/- Adapted from audited Density.FiniteDetector at eff263d7. Actual short
 parameters and exact Mobius cancellation, without a zero-detection claim. -/
import GuthMaynard.Improvement.ShortDetectorTruncation
open Complex MeasureTheory Set Filter MathCollab.Density
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- Fixed at each scale T: independent of both coordinates of the zero. -/
def shortDetectorCoefficient (T : ℝ) (n : ℕ) : ℂ :=
  if ⌊(2*T^((100:ℝ)⁻¹))⌋₊ < n ∧ n < shortDetectorCutoff T then
    (mollifierCoefficient (2*T^((100:ℝ)⁻¹)) n : ℂ)*(Real.exp (-(n : ℝ)/(T^(1/2:ℝ))) : ℂ)
  else 0

/-- A finite detector with fixed coefficients; its beta dependence remains
in n^(-rho) until the separate Taylor-family reduction. -/
def shortFiniteDetector (ρ : ℂ) (T : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (shortDetectorCutoff T), shortDetectorCoefficient T n*(n : ℂ)^(-ρ)

theorem shortDetectorCoefficient_support {T : ℝ} {n : ℕ}
    (hn : shortDetectorCoefficient T n ≠ 0) :
    ⌊(2*T^((100:ℝ)⁻¹))⌋₊ < n ∧ n < shortDetectorCutoff T := by
  by_contra h
  simp [shortDetectorCoefficient, h] at hn

/-- The cutoff convention retains only X<n<sqrt(T)(log T)^2, including all integer
rounding cases. -/
theorem shortDetectorCoefficient_real_support {T : ℝ} {n : ℕ}
    (hT : 0 < T) (hn : shortDetectorCoefficient T n ≠ 0) :
    (2*T^((100:ℝ)⁻¹)) < (n : ℝ) ∧ (n : ℝ) < T^(1/2:ℝ)*(Real.log T)^2 := by
  have hs := shortDetectorCoefficient_support hn
  exact ⟨(Nat.floor_lt (by positivity)).mp hs.1, Nat.lt_ceil.mp hs.2⟩

theorem shortDetectorCoefficient_norm_le {T : ℝ} (hT : 0 < T) (n : ℕ) :
    ‖shortDetectorCoefficient T n‖ ≤ (n.divisors.card : ℝ) := by
  unfold shortDetectorCoefficient
  split_ifs with h
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-(n : ℝ)/(T^(1/2:ℝ))) ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) (Real.rpow_pos_of_pos hT (1/2:ℝ)).le)
    exact (mul_le_mul (mollifierCoefficient_norm_le _ _) he (by positivity) (by positivity)).trans_eq (mul_one _)
  · simp

theorem shortDetectorX_one_le {T : ℝ} (hT : 1 ≤ T) : 1 ≤ (2*T^((100:ℝ)⁻¹)) := by
  have h := Real.one_le_rpow hT (show (0 : ℝ) ≤ 1/100 by norm_num)
  linarith

theorem short_detectorTerm_finite_split {T : ℝ} (hT : 1 ≤ T) (ρ : ℂ) {n : ℕ}
    (hn : n < shortDetectorCutoff T) :
    detectorTerm ρ (2*T^((100:ℝ)⁻¹)) (T^(1/2:ℝ)) n =
      (if n = 1 then (Real.exp (-1/(T^(1/2:ℝ))) : ℂ) else 0) +
      shortDetectorCoefficient T n*(n : ℂ)^(-ρ) := by
  have hX := shortDetectorX_one_le hT
  by_cases hlow : n ≤ ⌊(2*T^((100:ℝ)⁻¹))⌋₊
  · have hc : shortDetectorCoefficient T n = 0 := by simp [shortDetectorCoefficient, not_lt.mpr hlow]
    rw [hc, zero_mul, add_zero]
    by_cases hn0 : n = 0
    · subst n
      have hz : mollifierCoefficient (2*T^((100:ℝ)⁻¹)) 0 = 0 := by simp [mollifierCoefficient]
      simp [detectorTerm, hz]
    · by_cases hn1 : n = 1
      · subst n
        simp [detectorTerm, mollifierCoefficient_one hX]
      · have hnX : (n : ℝ) ≤ (2*T^((100:ℝ)⁻¹)) := (Nat.cast_le.mpr hlow).trans (Nat.floor_le (by linarith))
        simp [detectorTerm, mollifierCoefficient_vanishes (by omega : 2 ≤ n) hnX, hn1]
  · have hn1 : n ≠ 1 := by
      intro he
      subst n
      exact hlow (Nat.le_floor (by simpa using hX))
    simp only [hn1, ite_false, zero_add]
    rw [shortDetectorCoefficient, ite_eq_left ⟨by omega, hn⟩]
    dsimp [detectorTerm]
    ring

/-- Exact subtraction of n=1 and all cancelled terms, with the logarithmic
cutoff's tail still visible. -/
theorem shortFiniteDetector_decomposition {T : ℝ} (hT : 1 ≤ T)
    (hK : 1 < shortDetectorCutoff T) {ρ : ℂ} (hρ : 0 ≤ ρ.re) :
    (Real.exp (-1/(T^(1/2:ℝ))) : ℂ) + shortFiniteDetector ρ T +
      (∑' n : ℕ, detectorTerm ρ (2*T^((100:ℝ)⁻¹)) (T^(1/2:ℝ)) (n+shortDetectorCutoff T)) =
        smoothedDetector ρ (2*T^((100:ℝ)⁻¹)) (1/(T^(1/2:ℝ))) := by
  have hs := summable_zeta_detector_series (2*T^((100:ℝ)⁻¹)) (Real.rpow_pos_of_pos (by linarith : 0 < T) (1/2:ℝ)) hρ
  have he := hs.sum_add_tsum_nat_add (shortDetectorCutoff T)
  have hsum : ∑ n ∈ Finset.range (shortDetectorCutoff T), detectorTerm ρ (2*T^((100:ℝ)⁻¹)) (T^(1/2:ℝ)) n =
      (Real.exp (-1/(T^(1/2:ℝ))) : ℂ)+shortFiniteDetector ρ T := by
    simp_rw [Finset.sum_congr rfl (fun n hn => short_detectorTerm_finite_split hT ρ (Finset.mem_range.mp hn)), Finset.sum_add_distrib]
    simp [shortFiniteDetector, hK]
  have hfull : (∑' n : ℕ, detectorTerm ρ (2*T^((100:ℝ)⁻¹)) (T^(1/2:ℝ)) n) =
      smoothedDetector ρ (2*T^((100:ℝ)⁻¹)) (1/(T^(1/2:ℝ))) := by
    apply tsum_congr
    intro n
    exact (smoothedDetector_term_eq ρ (2*T^((100:ℝ)⁻¹)) (T^(1/2:ℝ)) n).symm
  change (∑ n ∈ Finset.range (shortDetectorCutoff T), detectorTerm ρ (2*T^((100:ℝ)⁻¹)) (T^(1/2:ℝ)) n) +
    (∑' n : ℕ, detectorTerm ρ (2*T^((100:ℝ)⁻¹)) (T^(1/2:ℝ)) (n+shortDetectorCutoff T)) = (∑' n : ℕ, detectorTerm ρ (2*T^((100:ℝ)⁻¹)) (T^(1/2:ℝ)) n) at he
  rwa [hsum, hfull] at he


end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.shortDetectorCoefficient_support
#print axioms GuthMaynard.Improvement.shortDetectorCoefficient_real_support
#print axioms GuthMaynard.Improvement.shortDetectorCoefficient_norm_le
#print axioms GuthMaynard.Improvement.shortDetectorX_one_le
#print axioms GuthMaynard.Improvement.short_detectorTerm_finite_split
#print axioms GuthMaynard.Improvement.shortFiniteDetector_decomposition
