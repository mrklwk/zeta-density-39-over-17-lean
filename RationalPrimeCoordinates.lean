module
public import RationalFiniteHeight
public import IntegerFourthMoment
public import MathCollab.Density.DivisorGrowth
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment

/-- Signed prime exponents of a rational in its canonical reduced form. -/
def rationalExponent (r : ℚ) (p : ℕ) : ℤ :=
  (r.num.natAbs.factorization p : ℤ) - (r.den.factorization p : ℤ)

theorem rationalExponent_eq_padicVal (r : ℚ) {p : ℕ} (hp : p.Prime) :
    rationalExponent r p = padicValRat p r := by
  simp only [rationalExponent, padicValRat_def, padicValInt,
    Nat.factorization_def _ hp]

theorem rationalExponent_mul {r s : ℚ} (hr : r ≠ 0) (hs : s ≠ 0) (p : ℕ) :
    rationalExponent (r*s) p = rationalExponent r p + rationalExponent s p := by
  by_cases hp : p.Prime
  · let : Fact p.Prime := ⟨hp⟩
    simp only [rationalExponent_eq_padicVal _ hp]
    exact padicValRat.mul hr hs
  · simp [rationalExponent, Nat.factorization_eq_zero_of_not_prime _ hp]

theorem rationalExponent_product {ι : Type*} (S : Finset ι) (r : ι → ℚ)
    (hr : ∀ i ∈ S, r i ≠ 0) (p : ℕ) :
    rationalExponent (∏ i ∈ S, r i) p = ∑ i ∈ S, rationalExponent (r i) p := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [rationalExponent]
  | @insert i S hi ih =>
    rw [prod_insert hi, sum_insert hi,
      rationalExponent_mul (hr i (mem_insert_self _ _))
        (prod_ne_zero_iff.mpr (fun j hj => hr j (mem_insert_of_mem hj))),
      ih (fun j hj => hr j (mem_insert_of_mem hj))]

/-- Positive rationals are determined by all their signed prime exponents. -/
theorem rationalExponent_injective {r s : ℚ} (hr : 0 < r) (hs : 0 < s)
    (h : ∀ p, rationalExponent r p = rationalExponent s p) : r = s := by
  have hrn : r.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hr.ne')
  have hsn : s.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hs.ne')
  have hc : r.num.natAbs*s.den = s.num.natAbs*r.den := by
    apply Nat.eq_of_factorization_eq (mul_ne_zero hrn s.den_nz) (mul_ne_zero hsn r.den_nz)
    intro p
    rw [Nat.factorization_mul hrn s.den_nz, Nat.factorization_mul hsn r.den_nz]
    simp only [Finsupp.add_apply]
    have hh := h p
    unfold rationalExponent at hh
    omega
  have hpR := positiveRatPair_ratio hr
  have hpS := positiveRatPair_ratio hs
  change (r.num.natAbs : ℚ)/(r.den : ℚ) = r at hpR
  change (s.num.natAbs : ℚ)/(s.den : ℚ) = s at hpS
  rw [← hpR, ← hpS]
  apply (div_eq_div_iff (by positivity) (by positivity)).mpr
  exact_mod_cast hc

theorem rationalExponent_zero_outside {r : ℚ} {p : ℕ}
    (hp : p ∉ r.num.natAbs.primeFactors ∪ r.den.primeFactors) :
    rationalExponent r p = 0 := by
  simp only [mem_union, not_or] at hp
  have hn : r.num.natAbs.factorization p = 0 := by
    simpa only [Nat.support_factorization] using (Finsupp.notMem_support_iff.mp hp.1)
  have hd : r.den.factorization p = 0 := by
    simpa only [Nat.support_factorization] using (Finsupp.notMem_support_iff.mp hp.2)
  simp [rationalExponent, hn, hd]

/-- The one-coordinate weight grows polynomially in the exponent. -/
theorem integerFourthWeight_le (n : ℤ) :
    integerFourthWeight n ≤ ((n.natAbs : ℝ)+1)^6 := by
  by_cases hn : n = 0
  · simp [hn, integerFourthWeight]
  have he : (1 : ℝ) ≤ n.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hn
  have hn2 : (n : ℝ)^2 = (n.natAbs : ℝ)^2 := by
    have heq : (n.natAbs : ℝ) = |(n : ℝ)| := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    rw [heq, sq_abs]
  rw [integerFourthWeight, ite_eq_right hn, hn2]
  have h1 : (n.natAbs : ℝ)^2 ≤ ((n.natAbs : ℝ)+1)^2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have h2 : (16 : ℝ) ≤ ((n.natAbs : ℝ)+1)^4 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by linarith : (2 : ℝ) ≤ n.natAbs+1) 4
    exact (by norm_num : (16 : ℝ) = 2^4).le.trans hh
  have hh := mul_le_mul h2 h1 (sq_nonneg _) (by positivity)
  nlinarith [show (((n.natAbs : ℝ)+1)^4)*(((n.natAbs : ℝ)+1)^2) =
    ((n.natAbs : ℝ)+1)^6 by ring]

theorem rationalExponent_weight_le (r : ℚ) (p : ℕ) :
    integerFourthWeight (rationalExponent r p) ≤
      (((r.num.natAbs.factorization p : ℝ)+1)*((r.den.factorization p : ℝ)+1))^6 := by
  apply (integerFourthWeight_le _).trans
  apply pow_le_pow_left₀ (by positivity)
  have hcast : ((rationalExponent r p).natAbs : ℝ) =
      |(r.num.natAbs.factorization p : ℝ) - (r.den.factorization p : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    simp [rationalExponent]
  rw [hcast]
  have htriangle : |(r.num.natAbs.factorization p : ℝ) - (r.den.factorization p : ℝ)| ≤
      (r.num.natAbs.factorization p : ℝ) + (r.den.factorization p : ℝ) := by
    apply abs_le.mpr
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (r.num.natAbs.factorization p),
      Nat.cast_nonneg (α := ℝ) (r.den.factorization p)]
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (r.num.natAbs.factorization p))
    (Nat.cast_nonneg (α := ℝ) (r.den.factorization p))]

theorem divisor_product_over_superset (n : ℕ) (hn : n ≠ 0) (P : Finset ℕ)
    (hP : n.primeFactors ⊆ P) :
    (∏ p ∈ P, ((n.factorization p : ℝ)+1)) = (n.divisors.card : ℝ) := by
  calc
    _ = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ)+1) := by
      symm
      apply prod_subset hP
      intro p _ hp
      have hz : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
      simp [hz]
    _ = _ := by rw [Nat.card_divisors hn]; push_cast; rfl

/-- Multiplying over the actual prime coordinates costs only divisor weights. -/
theorem rational_prime_weight_bound {r : ℚ} (hr : 0 < r) (P : Finset ℕ)
    (hP : r.num.natAbs.primeFactors ∪ r.den.primeFactors ⊆ P) :
    (∏ p ∈ P, integerFourthWeight (rationalExponent r p)) ≤
      ((r.num.natAbs.divisors.card : ℝ)*(r.den.divisors.card : ℝ))^6 := by
  calc
    _ ≤ ∏ p ∈ P,
        (((r.num.natAbs.factorization p : ℝ)+1)*((r.den.factorization p : ℝ)+1))^6 :=
      prod_le_prod₀ (fun p _ => integerFourthWeight_nonneg _)
        (fun p _ => rationalExponent_weight_le r p)
    _ = ((∏ p ∈ P, ((r.num.natAbs.factorization p : ℝ)+1))*
        (∏ p ∈ P, ((r.den.factorization p : ℝ)+1)))^6 := by
      rw [prod_pow, prod_mul_distrib]
    _ = _ := by
      rw [divisor_product_over_superset _
        (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hr.ne')) P
        (subset_union_left.trans hP),
        divisor_product_over_superset _ r.den_nz P (subset_union_right.trans hP)]

/-- Uniform small-power control of the arithmetic weights. The constants
are selected before the height, rational number and prime-coordinate set. -/
theorem rational_prime_weight_subpower {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (H : ℝ), 1 ≤ H → ∀ (r : ℚ), 0 < r →
      (r.num.natAbs : ℝ) ≤ H → (r.den : ℝ) ≤ H →
      ∀ (P : Finset ℕ), r.num.natAbs.primeFactors ∪ r.den.primeFactors ⊆ P →
      (∏ p ∈ P, integerFourthWeight (rationalExponent r p)) ≤ C*H^η := by
  obtain ⟨D, hD, hd⟩ := MathCollab.Density.divisor_card_subpower
    (show 0 < η/12 by positivity)
  refine ⟨D^12, one_le_pow₀ hD, ?_⟩
  intro H hH r hr hnum hden P hP
  have hn : 0 < r.num.natAbs := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hr.ne')
  have ha : (r.num.natAbs.divisors.card : ℝ) ≤ D*H^(η/12) :=
    (hd _ hn).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hnum (by positivity)) (by linarith))
  have hb : (r.den.divisors.card : ℝ) ≤ D*H^(η/12) :=
    (hd _ r.pos).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hden (by positivity)) (by linarith))
  have hm := mul_le_mul ha hb (Nat.cast_nonneg _) (by positivity)
  have hp := pow_le_pow_left₀ (by positivity) hm 6
  apply (rational_prime_weight_bound hr P hP).trans
  apply hp.trans_eq
  calc
    _ = D^12*(H^(η/12))^12 := by ring
    _ = _ := by
      rw [← Real.rpow_natCast (H^(η/12)) 12, ← Real.rpow_mul (by linarith : 0 ≤ H)]
      congr 2
      ring

end Montgomery.RationalMoment
