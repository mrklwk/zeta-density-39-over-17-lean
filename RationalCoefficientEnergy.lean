module
public import RationalCyclicMoment

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment

/-- Every finite family has a finite prime model and a cyclic modulus that
separates its frequencies. The choices do not enter any analytic constant. -/
theorem finite_rational_prime_model (A : Finset ℚ) :
    ∃ (d : ℕ) (p : Fin d → ℕ) (N : ℕ), 0 < N ∧ Function.Injective p ∧
      (∀ r ∈ A, r.num.natAbs.primeFactors ∪ r.den.primeFactors ⊆ univ.image p) ∧
      (∀ r ∈ A, ∀ j, (rationalExponent r (p j)).natAbs < N) ∧
      (∀ r ∈ A, ∀ s ∈ A, ∀ j,
        (rationalExponent r (p j)-rationalExponent s (p j)).natAbs < N) := by
  let P := A.biUnion (fun r => r.num.natAbs.primeFactors ∪ r.den.primeFactors)
  let p : Fin P.card → ℕ := P.orderEmbOfFin rfl
  let B := A.sup (fun r => univ.sup (fun j => (rationalExponent r (p j)).natAbs))
  let D := A.sup (fun r => A.sup (fun s => univ.sup
    (fun j => (rationalExponent r (p j)-rationalExponent s (p j)).natAbs)))
  refine ⟨P.card, p, B+D+1, by omega, (P.orderEmbOfFin rfl).injective, ?_, ?_, ?_⟩
  · intro r hr q hq
    have hm : q ∈ P := mem_biUnion.mpr ⟨r, hr, hq⟩
    simpa only [p, image_orderEmbOfFin_univ] using hm
  · intro r hr j
    have h1 : (rationalExponent r (p j)).natAbs ≤ B :=
      (le_sup (f := fun j => (rationalExponent r (p j)).natAbs) (mem_univ j)).trans
        (le_sup (f := fun r => univ.sup (fun j => (rationalExponent r (p j)).natAbs)) hr)
    omega
  · intro r hr s hs j
    have h1 : (rationalExponent r (p j)-rationalExponent s (p j)).natAbs ≤ D :=
      (le_sup (f := fun j => (rationalExponent r (p j)-rationalExponent s (p j)).natAbs)
        (mem_univ j)).trans ((le_sup
        (f := fun s => univ.sup (fun j => (rationalExponent r (p j)-rationalExponent s (p j)).natAbs)) hs).trans
        (le_sup (f := fun r => A.sup (fun s => univ.sup
          (fun j => (rationalExponent r (p j)-rationalExponent s (p j)).natAbs))) hr))
    omega

/-- Unconditional fourth-order coefficient energy for positive rational
frequencies, with a divisor weight and constant one. -/
theorem rational_coefficient_energy_two_weighted (A : Finset ℚ)
    (hA : ∀ r ∈ A, 0 < r) (c : ℚ → ℂ) :
    rationalCoefficientEnergy A 2 c ≤
      (∑ r ∈ A, ((r.num.natAbs.divisors.card : ℝ)*(r.den.divisors.card : ℝ))^6*‖c r‖^2)^2 := by
  obtain ⟨d, p, N, hN, hp, hP, hsize, hdiff⟩ :=
    finite_rational_prime_model (A ∪ rationalProducts A 2)
  let : NeZero N := ⟨hN.ne'⟩
  have hm := rational_cyclic_moment_identity (N := N) p A 2 hA
    (fun q hq => hP q (mem_union_right _ hq))
    (fun q hq r hr => hdiff q (mem_union_right _ hq) r (mem_union_right _ hr)) c
  have hh := rational_cyclic_weighted_fourth (N := N) p hp A hA
    (fun r hr => hP r (mem_union_left _ hr))
    (fun r hr => hsize r (mem_union_left _ hr)) c
  norm_num only [show 2*2 = 4 by omega] at hm
  rwa [hm] at hh

theorem rational_divisor_weight_subpower {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (H : ℝ), 1 ≤ H → ∀ (r : ℚ), 0 < r →
      (r.num.natAbs : ℝ) ≤ H → (r.den : ℝ) ≤ H →
      ((r.num.natAbs.divisors.card : ℝ)*(r.den.divisors.card : ℝ))^6 ≤ C*H^η := by
  obtain ⟨D, hD, hd⟩ := MathCollab.Density.divisor_card_subpower (show 0 < η/12 by positivity)
  refine ⟨D^12, one_le_pow₀ hD, ?_⟩
  intro H hH r hr hnum hden
  have ha : (r.num.natAbs.divisors.card : ℝ) ≤ D*H^(η/12) :=
    (hd _ (Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hr.ne'))).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hnum (by positivity)) (by linarith))
  have hb : (r.den.divisors.card : ℝ) ≤ D*H^(η/12) :=
    (hd _ r.pos).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hden (by positivity)) (by linarith))
  have hm := mul_le_mul ha hb (Nat.cast_nonneg _) (by positivity)
  apply (pow_le_pow_left₀ (by positivity) hm 6).trans_eq
  calc
    _ = D^12*(H^(η/12))^12 := by ring
    _ = _ := by
      rw [← Real.rpow_natCast (H^(η/12)) 12, ← Real.rpow_mul (by linarith : 0 ≤ H)]
      congr 2
      ring

/-- The first complete small-power rational coefficient-energy estimate.
It has arbitrary complex coefficients and a constant uniform in the height
and the set of positive reduced fractions. -/
theorem rational_coefficient_energy_two_subpower {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : ℝ), 1 ≤ H → ∀ (A : Finset ℚ),
      (∀ r ∈ A, 0 < r ∧ (r.num.natAbs : ℝ) ≤ H ∧ (r.den : ℝ) ≤ H) →
      ∀ c : ℚ → ℂ, rationalCoefficientEnergy A 2 c ≤
        C*H^η*(∑ r ∈ A, ‖c r‖^2)^2 := by
  obtain ⟨D, hD, hd⟩ := rational_divisor_weight_subpower (show 0 < η/2 by positivity)
  refine ⟨D^2, by positivity, ?_⟩
  intro H hH A hA c
  have he := rational_coefficient_energy_two_weighted A (fun r hr => (hA r hr).1) c
  have hb : (∑ r ∈ A, ((r.num.natAbs.divisors.card : ℝ)*(r.den.divisors.card : ℝ))^6*‖c r‖^2) ≤
      (D*H^(η/2))*(∑ r ∈ A, ‖c r‖^2) := by
    rw [mul_sum]
    exact sum_le_sum (fun r hr => mul_le_mul_of_nonneg_right
      (hd H hH r (hA r hr).1 (hA r hr).2.1 (hA r hr).2.2) (sq_nonneg _))
  apply he.trans ((pow_le_pow_left₀ (by positivity) hb 2).trans_eq _)
  rw [mul_pow, mul_pow, ← Real.rpow_natCast (H^(η/2)) 2,
    ← Real.rpow_mul (by linarith : 0 ≤ H)]
  congr 2
  ring

end Montgomery.RationalMoment
