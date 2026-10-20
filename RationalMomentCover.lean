module
public import Mathlib

@[expose] public section

/-! A finite, height-independent choice of moment orders in the short-range
argument. This is an exponent-covering theorem, not a moment estimate. -/
set_option autoImplicit false
noncomputable section

namespace Montgomery.RationalMoment

/-- Above the cutoff `δ`, one can choose a moment order from a fixed finite
set. In particular, the moment order need not grow with the height `T`.
The inequalities `1-r ≤ k*m ≤ r` are exactly those needed for both terms
of `(T^(1/k)+M²) R^(2-1/k)` to be at most `M R²` when `R=T^r`, `M=T^m`.
-/
theorem finite_moment_cover {K : ℕ} (hK : 1 ≤ K)
    {r m δ : ℝ} (hδ : 0 < δ) (hδm : δ ≤ m) (hr1 : r ≤ 1)
    (hr : ((K : ℝ) + 1) / (2 * K + 1) ≤ r)
    (hm : m ≤ r / K) :
    ∃ k : ℕ, K ≤ k ∧ k ≤ ⌈1 / δ⌉₊ ∧ 1 - r ≤ (k : ℝ) * m ∧
      (k : ℝ) * m ≤ r := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hmpos : 0 < m := hδ.trans_le hδm
  have hden : (0 : ℝ) < 2 * K + 1 := by positivity
  have hrbudget : (K : ℝ) + 1 ≤ r * (2 * K + 1) := (div_le_iff₀ hden).mp hr
  have hrhalf : (1 : ℝ) / 2 < r := by
    by_contra hn
    have hh : r ≤ 1 / 2 := le_of_not_gt hn
    nlinarith [mul_le_mul_of_nonneg_right hh hden.le]
  have hrpos : 0 < r := by linarith
  let k : ℕ := ⌊r / m⌋₊
  have hKk : K ≤ k := Nat.le_floor ((le_div_iff₀ hmpos).mpr (by
    have hh := (le_div_iff₀ hKpos).mp hm
    nlinarith))
  have hkR : (K : ℝ) ≤ k := by exact_mod_cast hKk
  have hkpos : (0 : ℝ) < k := hKpos.trans_le hkR
  have hfloor : (k : ℝ) * m ≤ r := (le_div_iff₀ hmpos).mp
    (Nat.floor_le (by positivity : 0 ≤ r / m))
  have hnext : r < ((k : ℝ) + 1) * m := (div_lt_iff₀ hmpos).mp
    (Nat.lt_floor_add_one (r / m))
  have hbudget : (k : ℝ) + 1 ≤ r * (2 * k + 1) := by
    nlinarith [mul_nonneg (show 0 ≤ 2 * r - 1 by linarith) (sub_nonneg.mpr hkR)]
  have hlower : 1 - r ≤ (k : ℝ) * m := by
    have hh := mul_lt_mul_of_pos_left hnext hkpos
    nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) + 1 by positivity)
      (show 0 ≤ r * (2 * k + 1) - (k + 1) by linarith)]
  have hkδ : (k : ℝ) * δ ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hδm hkpos.le]
  have hbound : k ≤ ⌈1 / δ⌉₊ := by
    have hh : (k : ℝ) ≤ (⌈1 / δ⌉₊ : ℝ) :=
      ((le_div_iff₀ hδ).mpr hkδ).trans (Nat.le_ceil (1 / δ))
    exact_mod_cast hh
  exact ⟨k, hKk, hbound, hlower, hfloor⟩

/-- The two exponent comparisons are explicit consequences of the cover. -/
theorem moment_exponents {k : ℕ} (hk : 1 ≤ k) {r m : ℝ}
    (hl : 1 - r ≤ (k : ℝ) * m) (hu : (k : ℝ) * m ≤ r) :
    1 / (k : ℝ) + r * (2 - 1 / k) ≤ m + 2 * r ∧
      2 * m + r * (2 - 1 / k) ≤ m + 2 * r := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  constructor
  · apply (mul_le_mul_iff_right₀ hkpos).mp
    field_simp
    nlinarith
  · apply (mul_le_mul_iff_right₀ hkpos).mp
    field_simp
    nlinarith

end Montgomery.RationalMoment

#print axioms Montgomery.RationalMoment.finite_moment_cover
#print axioms Montgomery.RationalMoment.moment_exponents
