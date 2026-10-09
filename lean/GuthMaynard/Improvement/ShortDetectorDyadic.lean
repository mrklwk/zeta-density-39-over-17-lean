/- Adapted from audited Density.DetectorDyadic; actual short coefficient support. -/
import MathCollab.Density.DetectorDyadic
import GuthMaynard.Improvement.ShortFiniteDetector

open Complex Set Filter MathCollab.Density
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

def shortDetectorBlock (ρ : ℂ) (T : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2*N), shortDetectorCoefficient T n*(n : ℂ)^(-ρ)

/-- The full finite list is fixed at T, before a zero is considered. -/
def shortDetectorDyadicCount (T : ℝ) : ℕ := Nat.log 2 (shortDetectorCutoff T)+1

theorem shortFiniteDetector_eq_dyadic_sum {T : ℝ} (hT : 1 ≤ T) (ρ : ℂ) :
    shortFiniteDetector ρ T =
      ∑ r ∈ Finset.range (shortDetectorDyadicCount T), shortDetectorBlock ρ T (2^r) := by
  let K := shortDetectorCutoff T
  let L := shortDetectorDyadicCount T
  let f := fun n : ℕ => shortDetectorCoefficient T n*(n : ℂ)^(-ρ)
  have hK : K < 2^L := Nat.lt_pow_succ_log_self (by norm_num) K
  have hX : 1 ≤ ⌊2*T^((100:ℝ)⁻¹)⌋₊ := Nat.le_floor (by
    have hp := Real.one_le_rpow hT (by positivity : (0:ℝ) ≤ (100:ℝ)⁻¹)
    linarith)
  have hs : ∑ n ∈ Finset.range K, f n = ∑ n ∈ Finset.range (2^L+1), f n := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro n hn hn'
    have hz : ¬ n < shortDetectorCutoff T := by simpa [K] using hn'
    simp [f, shortDetectorCoefficient, hz]
  have hi : ∑ n ∈ Finset.Ioc 1 (2^L), f n = ∑ n ∈ Finset.range (2^L+1), f n := by
    apply Finset.sum_subset
    · intro n hn
      exact Finset.mem_range.mpr (by have := (Finset.mem_Ioc.mp hn).2; omega)
    · intro n hn hn'
      have hnlow : n ≤ 1 := by
        have hnr := Finset.mem_range.mp hn
        have hni : ¬ (1 < n ∧ n ≤ 2^L) := by simpa using hn'
        omega
      have hz : ¬ ⌊2*T^((100:ℝ)⁻¹)⌋₊ < n := by omega
      simp [f, shortDetectorCoefficient, hz]
  change (∑ n ∈ Finset.range K, f n) = _
  rw [hs, ← hi, ← sum_dyadic_Ioc f L]
  rfl

/-- Quantitative extraction from the fixed dyadic list, without moving t. -/
theorem exists_short_detector_dyadic_block {T A : ℝ} {ρ : ℂ}
    (hT : 1 ≤ T) (hA : 0 < A) (hlarge : A ≤ ‖shortFiniteDetector ρ T‖) :
    ∃ r ∈ Finset.range (shortDetectorDyadicCount T),
      A/(shortDetectorDyadicCount T : ℝ) ≤ ‖shortDetectorBlock ρ T (2^r)‖ := by
  have hL : 0 < shortDetectorDyadicCount T := by unfold shortDetectorDyadicCount; omega
  have hLreal : (0 : ℝ) < shortDetectorDyadicCount T := by exact_mod_cast hL
  by_contra h
  push Not at h
  have he : (∑ r ∈ Finset.range (shortDetectorDyadicCount T), ‖shortDetectorBlock ρ T (2^r)‖) < A := by
    calc
      _ < ∑ _r ∈ Finset.range (shortDetectorDyadicCount T), A/(shortDetectorDyadicCount T : ℝ) :=
        Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr hL⟩ h
      _ = A := by simp; field_simp
  rw [shortFiniteDetector_eq_dyadic_sum hT ρ] at hlarge
  have hb := norm_sum_le (Finset.range (shortDetectorDyadicCount T)) (fun r => shortDetectorBlock ρ T (2^r))
  linarith

/-- A nonzero block meets the true retained support, giving the packet's
strict lower block scale and its original logarithmic upper scale. -/
theorem shortDetectorBlock_scale_bounds {T : ℝ} {N : ℕ} {ρ : ℂ}
    (hT : 0 < T) (hblock : shortDetectorBlock ρ T N ≠ 0) :
    T^((100:ℝ)⁻¹) < (N : ℝ) ∧ (N : ℝ) < T^(1/2:ℝ)*(Real.log T)^2 := by
  obtain ⟨n, hn, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hblock
  have hc : shortDetectorCoefficient T n ≠ 0 := by
    intro he
    exact hterm (by rw [he, zero_mul])
  have hs := shortDetectorCoefficient_real_support hT hc
  have hlo : (N : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
  have hhi : (n : ℝ) ≤ 2*N := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
  constructor <;> linarith

end GuthMaynard.Improvement

#print axioms GuthMaynard.Improvement.shortFiniteDetector_eq_dyadic_sum
#print axioms GuthMaynard.Improvement.exists_short_detector_dyadic_block
#print axioms GuthMaynard.Improvement.shortDetectorBlock_scale_bounds
