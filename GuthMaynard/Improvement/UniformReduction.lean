module
public import Mathlib

@[expose] public section

/-! Conditional quantitative closure of the unequal-scale calculation.
The two analytic estimates are explicit premises. This file does NOT prove
the Poisson truncation, divisor bound, or published affine theorem.
-/
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

def unequalScaleBound (R K m n : ℝ) : ℝ :=
  R ^ 2 * K ^ 4 * m ^ 2 + R * K ^ 3 * n ^ 2

/-- Final scale absorption, keeping the prefactor RK before the smaller
affine square average Q. E and H carry the two uniform losses. -/
theorem unequal_reduction_of_estimates {J Q E H R K m n : ℝ}
    (hE : 0 ≤ E) (hH : 1 ≤ H) (hK : 0 ≤ K) (hKR : K ≤ R)
    (hm : 0 ≤ m) (hn : 0 ≤ n)
    (hpoisson : J ≤ E * (R ^ 2 * K ^ 4 * m ^ 2 + R * K * n * Real.sqrt Q))
    (haffine : Q ≤ H * (K ^ 6 * m ^ 2 + K ^ 4 * n ^ 2)) :
    J ≤ 2 * E * Real.sqrt H * unequalScaleBound R K m n := by
  have hR : 0 ≤ R := hK.trans hKR
  have hH0 : 0 ≤ H := by linarith
  have hcross : R * K ^ 4 * m * n ≤ R ^ 2 * K ^ 4 * m ^ 2 + R * K ^ 3 * n ^ 2 := by
    have h1 : 0 ≤ K ^ 4 * (R * m - n) ^ 2 := by positivity
    have h2 : 0 ≤ K ^ 4 * (R * m) ^ 2 := by positivity
    have h3 : 0 ≤ (R - K) * K ^ 3 * n ^ 2 := by positivity
    nlinarith
  have hroot : Real.sqrt Q ≤ Real.sqrt H * (K ^ 3 * m + K ^ 2 * n) := by
    have hsq : K ^ 6 * m ^ 2 + K ^ 4 * n ^ 2 ≤ (K ^ 3 * m + K ^ 2 * n) ^ 2 := by
      have : 0 ≤ K ^ 5 * m * n := by positivity
      nlinarith
    calc
      Real.sqrt Q ≤ Real.sqrt (H * (K ^ 3 * m + K ^ 2 * n) ^ 2) :=
        Real.sqrt_le_sqrt (haffine.trans (mul_le_mul_of_nonneg_left hsq hH0))
      _ = Real.sqrt H * (K ^ 3 * m + K ^ 2 * n) := by
        rw [Real.sqrt_mul hH0, Real.sqrt_sq (by positivity)]
  have hroot1 : 1 ≤ Real.sqrt H := Real.one_le_sqrt.mpr hH
  have hlow : R ^ 2 * K ^ 4 * m ^ 2 ≤
      Real.sqrt H * (R ^ 2 * K ^ 4 * m ^ 2) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hroot1
      (show 0 ≤ R ^ 2 * K ^ 4 * m ^ 2 by positivity)
  have hhigh : R * K * n * Real.sqrt Q ≤
      Real.sqrt H * (R * K ^ 4 * m * n + R * K ^ 3 * n ^ 2) := by
    convert mul_le_mul_of_nonneg_left hroot (show 0 ≤ R * K * n by positivity) using 1
    ring
  have habsorb := mul_le_mul_of_nonneg_left hcross (Real.sqrt_nonneg H)
  apply hpoisson.trans
  have hsum : R ^ 2 * K ^ 4 * m ^ 2 + R * K * n * Real.sqrt Q ≤
      2 * Real.sqrt H * unequalScaleBound R K m n := by
    dsimp [unequalScaleBound]
    nlinarith
  convert mul_le_mul_of_nonneg_left hsum hE using 1
  ring

/-- Uniform epsilon closure. The admissible family and mass functions are fixed
BEFORE epsilon. Q also depends on the internal smoothing/loss parameter η.
For each loss exponent, each input constant precedes every T,R,K,f. The
conclusion constant has that same quantifier order.

To instantiate this with the manuscript, J must be the actual affine square
integral, Q the actual smoothed affine square integral at scale O(K), m=||f||1,
n=||f||2, and admissible must enforce the fixed support/decay constants.
Those analytic instantiations are not supplied by this theorem. -/
theorem uniform_unequal_reduction
    (J : ℝ → ℝ → ℝ → (ℝ → ℝ) → ℝ)
    (Q : ℝ → ℝ → ℝ → ℝ → (ℝ → ℝ) → ℝ)
    (mass normTwo : (ℝ → ℝ) → ℝ) (admissible : ℝ → (ℝ → ℝ) → Prop)
    (hmass : ∀ f, 0 ≤ mass f) (hnorm : ∀ f, 0 ≤ normTwo f)
    (hpoisson : ∀ η : ℝ, 0 < η → ∃ A : ℝ, 1 ≤ A ∧
      ∀ (T R K : ℝ) (f : ℝ → ℝ), 2 ≤ T → 1 ≤ K → K ≤ R → R ≤ T ^ 4 →
        admissible T f →
        J T R K f ≤ A * T ^ η *
          (R ^ 2 * K ^ 4 * (mass f) ^ 2 + R * K * normTwo f * Real.sqrt (Q η T R K f)))
    (haffine : ∀ η : ℝ, 0 < η → ∀ ζ : ℝ, 0 < ζ → ∃ B : ℝ, 1 ≤ B ∧
      ∀ (T R K : ℝ) (f : ℝ → ℝ), 2 ≤ T → 1 ≤ K → K ≤ R → R ≤ T ^ 4 →
        admissible T f →
        Q η T R K f ≤ B * T ^ ζ * (K ^ 6 * (mass f) ^ 2 + K ^ 4 * (normTwo f) ^ 2)) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (T R K : ℝ) (f : ℝ → ℝ), 2 ≤ T → 1 ≤ K → K ≤ R → R ≤ T ^ 4 →
        admissible T f →
        J T R K f ≤ C * T ^ ε * unequalScaleBound R K (mass f) (normTwo f) := by
  intro ε hε
  obtain ⟨A, hA, hP⟩ := hpoisson (ε / 2) (by positivity)
  obtain ⟨B, hB, hG⟩ := haffine (ε / 2) (by positivity) ε hε
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  refine ⟨2 * A * Real.sqrt B, by positivity, ?_⟩
  intro T R K f hT hK hKR hRT hf
  have hT0 : 0 < T := by linarith
  have hTp : 1 ≤ T ^ ε := Real.one_le_rpow (by linarith) hε.le
  have hH : 1 ≤ B * T ^ ε := by nlinarith
  have h := unequal_reduction_of_estimates
    (show 0 ≤ A * T ^ (ε / 2) by positivity) hH (by linarith) hKR
    (hmass f) (hnorm f) (hP T R K f hT hK hKR hRT hf) (hG T R K f hT hK hKR hRT hf)
  have hsqrt : Real.sqrt (B * T ^ ε) = Real.sqrt B * T ^ (ε / 2) := by
    rw [Real.sqrt_mul hB0.le]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT0.le]
    congr 1
    ring
  have hp : T ^ (ε / 2) * T ^ (ε / 2) = T ^ ε := by
    rw [← Real.rpow_add hT0]
    congr 1
    ring
  rw [hsqrt] at h
  calc
    J T R K f ≤ 2 * (A * T ^ (ε / 2)) * (Real.sqrt B * T ^ (ε / 2)) *
        unequalScaleBound R K (mass f) (normTwo f) := h
    _ = 2 * A * Real.sqrt B * T ^ ε * unequalScaleBound R K (mass f) (normTwo f) := by
      rw [← hp]
      ring

end GuthMaynard.Improvement

#print axioms GuthMaynard.Improvement.unequal_reduction_of_estimates
#print axioms GuthMaynard.Improvement.uniform_unequal_reduction

#check @GuthMaynard.Improvement.uniform_unequal_reduction
