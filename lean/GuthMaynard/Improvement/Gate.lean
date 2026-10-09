import Mathlib

/-!
Small validated components of the candidate Guth–Maynard improvement.
These are NOT a formalization of the affine lemma or cubic trace theorem.
In particular the finite Cauchy–Schwarz result does not stand for its Lebesgue
integral analogue, Poisson summation, or the measurable-mask smoothing step.
-/

set_option autoImplicit false

namespace GuthMaynard.Improvement

/-- The inner finite sum bound used in the masked box calculation. -/
theorem inner_sum_bound {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    (∑ i ∈ s, Real.sqrt (f i) * Real.sqrt (g i)) ≤
      Real.sqrt (∑ i ∈ s, f i) * Real.sqrt (∑ i ∈ s, g i) :=
  Real.sum_sqrt_mul_sqrt_le s hf hg

/-- Two finite Cauchy–Schwarz steps keep the ORIGINAL first factor r.
Apply this to a masked r; no enlargement of its support is needed. -/
theorem outer_sum_bound {ι : Type*} (s : Finset ι) (r X Y : ι → ℝ)
    (hX : ∀ i, 0 ≤ X i) (hY : ∀ i, 0 ≤ Y i) :
    (∑ i ∈ s, r i * (Real.sqrt (X i) * Real.sqrt (Y i))) ≤
      Real.sqrt (∑ i ∈ s, r i ^ 2) *
        Real.sqrt (Real.sqrt (∑ i ∈ s, X i ^ 2) *
          Real.sqrt (∑ i ∈ s, Y i ^ 2)) := by
  have hfirst := Real.sum_mul_le_sqrt_mul_sqrt s r
    (fun i => Real.sqrt (X i) * Real.sqrt (Y i))
  have hid : (∑ i ∈ s, (Real.sqrt (X i) * Real.sqrt (Y i)) ^ 2) =
      ∑ i ∈ s, X i * Y i := by
    apply Finset.sum_congr rfl
    intro i _
    simp [mul_pow, Real.sq_sqrt (hX i), Real.sq_sqrt (hY i)]
  rw [hid] at hfirst
  exact hfirst.trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (Real.sum_mul_le_sqrt_mul_sqrt s X Y))
    (Real.sqrt_nonneg _))

/-- The last absorption in the unequal-scale argument, with constants explicit. -/
theorem unequal_scale_absorption {R K a b : ℝ}
    (hK : 0 ≤ K) (hKR : K ≤ R) :
    R * K ^ 4 * a * b ≤ R ^ 2 * K ^ 4 * a ^ 2 + R * K ^ 3 * b ^ 2 := by
  have hcross : 0 ≤ K ^ 4 * (R * a - b) ^ 2 := by positivity
  have hrem : 0 ≤ K ^ 4 * (R * a) ^ 2 := by positivity
  have hscale : 0 ≤ (R - K) * K ^ 3 * b ^ 2 := by positivity
  nlinarith

/-- Scalar negative-eigenvalue comparison. c represents <Ce,e>.
The premise h ≤ c follows from G=C+H ≥ 0 on an H-eigenvector.
No commutation or positivity premise for H occurs here. -/
theorem negative_eigenvalue_cube {h c : ℝ} (hhc : h ≤ c) :
    h ^ 3 ≤ h ^ 2 * c := by
  have := mul_le_mul_of_nonneg_left hhc (sq_nonneg h)
  nlinarith

/-- Finite sum over a negative spectrum. The operator identification and
infinite trace limit remain open analytic obligations. -/
theorem negative_spectrum_sum {ι : Type*} (s : Finset ι) (h c : ι → ℝ)
    (hc : ∀ i ∈ s, h i ≤ c i) :
    (∑ i ∈ s, h i ^ 3) ≤ ∑ i ∈ s, h i ^ 2 * c i := by
  exact Finset.sum_le_sum fun i hi => negative_eigenvalue_cube (hc i hi)

/-- Exact exponent identities; tau = log(T)/log(N), with no logarithmic
change of variables asserted by this purely algebraic theorem. -/
theorem scale_identities (τ : ℝ) :
    4 + 2 * τ - (1 + 5 * τ) / 7 = (3 / 2 : ℝ) * ((18 + 6 * τ) / 7) ∧
    5 + (1 + 5 * τ) / 7 + τ = 2 * ((18 + 6 * τ) / 7) ∧
    7 + 3 * τ - 3 * ((18 + 6 * τ) / 7) = (3 * τ - 5) / 7 := by
  constructor
  · ring
  constructor <;> ring

theorem scale_range {τ : ℝ} (hlo : 6 / 5 ≤ τ) (hhi : τ ≤ 5 / 3) :
    1 ≤ (1 + 5 * τ) / 7 ∧ (1 + 5 * τ) / 7 ≤ τ ∧
    (4 / 5) * τ ≤ (1 + 5 * τ) / 7 ∧
    7 + 3 * τ ≤ 3 * ((18 + 6 * τ) / 7) := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem candidate_coefficient_arithmetic :
    (3 : ℚ) / (2 - 9 / 13) = 39 / 17 ∧
    (18 : ℚ) / (3 + 7 * (9 / 13)) = 39 / 17 ∧
    (30 : ℚ) / 13 - 39 / 17 = 3 / 221 := by norm_num

end GuthMaynard.Improvement

#print axioms GuthMaynard.Improvement.inner_sum_bound
#print axioms GuthMaynard.Improvement.outer_sum_bound
#print axioms GuthMaynard.Improvement.unequal_scale_absorption
#print axioms GuthMaynard.Improvement.negative_eigenvalue_cube
#print axioms GuthMaynard.Improvement.negative_spectrum_sum
#print axioms GuthMaynard.Improvement.scale_identities
#print axioms GuthMaynard.Improvement.scale_range
#print axioms GuthMaynard.Improvement.candidate_coefficient_arithmetic
