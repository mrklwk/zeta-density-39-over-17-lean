module
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Tactic

@[expose] public section

/-!
Finite duality for the rational-frequency research argument.
The moment inequality is an explicit hypothesis, not an axiom or a proved
hypercontractive estimate. The test coefficients and all finite-sum identities
are constructed in the proof. Empty sets and zero energy are included.
-/
set_option autoImplicit false
noncomputable section
open Finset

namespace Montgomery.RationalMoment

variable {ι τ : Type*}

theorem norm_sum_pow_le (W : Finset τ) (f : τ → ℂ) {p : ℕ} (hp : 1 ≤ p) :
    ‖∑ t ∈ W, f t‖ ^ p ≤ (W.card : ℝ) ^ (p - 1) * ∑ t ∈ W, ‖f t‖ ^ p := by
  have hh := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg W
    (f := fun t => ‖f t‖) (p := (p : ℝ)) (by exact_mod_cast hp)
    (fun _ _ => norm_nonneg _)
  rw [show (p : ℝ) - 1 = ((p - 1 : ℕ) : ℝ) by simp [Nat.cast_sub hp]] at hh
  simp only [Real.rpow_natCast] at hh
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) p).trans hh

/-- The conjugate of the actual row sum realizes the dual pairing exactly. -/
theorem conjugate_pairing (A : Finset ι) (W : Finset τ) (K : ι → τ → ℂ) :
    (∑ t ∈ W, ∑ r ∈ A, star (∑ u ∈ W, K r u) * K r t) =
      ((∑ r ∈ A, ‖∑ t ∈ W, K r t‖ ^ 2 : ℝ) : ℂ) := by
  rw [sum_comm]
  simp only [← mul_sum, Complex.ofReal_sum]
  apply sum_congr rfl
  intro r _
  simpa only [Complex.ofReal_pow, starRingEnd_apply] using Complex.conj_mul' (∑ t ∈ W, K r t)

/-- Exact higher-moment duality for any finite complex kernel.
The conclusion is raised to the integer power `k`, avoiding root conventions.
Only the displayed coefficient moment bound is assumed. -/
theorem energy_pow_le_of_moment (A : Finset ι) (W : Finset τ)
    (K : ι → τ → ℂ) {k : ℕ} (hk : 1 ≤ k) {B : ℝ} (hB : 0 ≤ B)
    (hmoment : ∀ c : ι → ℂ,
      (∑ t ∈ W, ‖∑ r ∈ A, c r * K r t‖ ^ (2 * k)) ≤
        B * (∑ r ∈ A, ‖c r‖ ^ 2) ^ k) :
    (∑ r ∈ A, ‖∑ t ∈ W, K r t‖ ^ 2) ^ k ≤
      (W.card : ℝ) ^ (2 * k - 1) * B := by
  let S : ℝ := ∑ r ∈ A, ‖∑ t ∈ W, K r t‖ ^ 2
  have hS : 0 ≤ S := sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hz : S = 0
  · change S ^ k ≤ _
    rw [hz, zero_pow (by omega : k ≠ 0)]
    positivity
  have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
  let c : ι → ℂ := fun r => star (∑ t ∈ W, K r t)
  have hcoeff : (∑ r ∈ A, ‖c r‖ ^ 2) = S := by
    dsimp only [c, S]
    simp only [norm_star]
  have hpair : ‖∑ t ∈ W, ∑ r ∈ A, c r * K r t‖ = S := by
    rw [show (∑ t ∈ W, ∑ r ∈ A, c r * K r t) = (S : ℂ) from
      conjugate_pairing A W K]
    simp [Real.norm_eq_abs, abs_of_nonneg hS]
  have hh := norm_sum_pow_le W (fun t => ∑ r ∈ A, c r * K r t)
    (show 1 ≤ 2 * k by omega)
  rw [hpair] at hh
  have hm := hmoment c
  rw [hcoeff] at hm
  have hpow : S ^ (2 * k) ≤ ((W.card : ℝ) ^ (2 * k - 1) * B) * S ^ k := by
    calc
      _ ≤ _ := hh.trans (mul_le_mul_of_nonneg_left hm (by positivity))
      _ = _ := by ring
  have heq : S ^ (2 * k) = S ^ k * S ^ k := by
    rw [show 2 * k = k + k by omega, pow_add]
  rw [heq] at hpow
  exact (mul_le_mul_iff_left₀ (pow_pos hSpos k)).mp (by simpa [mul_comm] using hpow)

/-- The literal phase of a positive rational number (also defined for all reals). -/
def phase (r t : ℝ) : ℂ := Complex.exp (((t * Real.log r : ℝ) : ℂ) * Complex.I)

def rationalEnergy (A : Finset ℚ) (W : Finset ℝ) : ℝ :=
  ∑ r ∈ A, ‖∑ t ∈ W, phase r t‖ ^ 2

/-- Specialization to actual rational frequencies, with no level-set loss.
The finite-height moment theorem remains a hypothesis. -/
theorem rational_energy_pow_le (A : Finset ℚ) (W : Finset ℝ)
    {k : ℕ} (hk : 1 ≤ k) {B : ℝ} (hB : 0 ≤ B)
    (hmoment : ∀ c : ℚ → ℂ,
      (∑ t ∈ W, ‖∑ r ∈ A, c r * phase r t‖ ^ (2 * k)) ≤
        B * (∑ r ∈ A, ‖c r‖ ^ 2) ^ k) :
    rationalEnergy A W ^ k ≤ (W.card : ℝ) ^ (2 * k - 1) * B :=
  energy_pow_le_of_moment A W (fun r t => phase r t) hk hB hmoment

end Montgomery.RationalMoment

#print axioms Montgomery.RationalMoment.norm_sum_pow_le
#print axioms Montgomery.RationalMoment.conjugate_pairing
#print axioms Montgomery.RationalMoment.energy_pow_le_of_moment
#print axioms Montgomery.RationalMoment.rational_energy_pow_le
