module
public import RationalPrimeCoordinates
public import CyclicProductMoment

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment

def primeCoordinates {d : ℕ} (p : Fin d → ℕ) (r : ℚ) : Fin d → ℤ :=
  fun j => rationalExponent r (p j)

theorem primeCoordinates_injective_on {d : ℕ} (p : Fin d → ℕ) (A : Finset ℚ)
    (hA : ∀ r ∈ A, 0 < r)
    (hP : ∀ r ∈ A, r.num.natAbs.primeFactors ∪ r.den.primeFactors ⊆ univ.image p) :
    Set.InjOn (primeCoordinates p) (↑A : Set ℚ) := by
  intro r hr s hs hrs
  apply rationalExponent_injective (hA r hr) (hA s hs)
  intro q
  by_cases hq : q ∈ univ.image p
  · obtain ⟨j, _, rfl⟩ := mem_image.mp hq
    exact congrFun hrs j
  · rw [rationalExponent_zero_outside (fun h => hq (hP r hr h)),
      rationalExponent_zero_outside (fun h => hq (hP s hs h))]

def rationalCyclicPhase {N d : ℕ} [NeZero N] (p : Fin d → ℕ)
    (r : ℚ) (x : Fin d → ZMod N) : ℂ := productCyclicPhase (primeCoordinates p r) x

theorem rationalCyclicPhase_mul {N d : ℕ} [NeZero N] (p : Fin d → ℕ)
    {r s : ℚ} (hr : r ≠ 0) (hs : s ≠ 0) (x : Fin d → ZMod N) :
    rationalCyclicPhase p (r*s) x = rationalCyclicPhase p r x*rationalCyclicPhase p s x := by
  simp only [rationalCyclicPhase, productCyclicPhase, primeCoordinates,
    rationalExponent_mul hr hs, cyclicPhase_add, prod_mul_distrib]

theorem rationalCyclicPhase_product {N d : ℕ} [NeZero N] (p : Fin d → ℕ)
    {ι : Type*} (S : Finset ι) (r : ι → ℚ) (hr : ∀ i ∈ S, r i ≠ 0)
    (x : Fin d → ZMod N) :
    (∏ i ∈ S, rationalCyclicPhase p (r i) x) = rationalCyclicPhase p (∏ i ∈ S, r i) x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [rationalCyclicPhase, productCyclicPhase, primeCoordinates,
      rationalExponent, cyclicPhase]
  | @insert i S hi ih =>
    rw [prod_insert hi, prod_insert hi,
      rationalCyclicPhase_mul p (hr i (mem_insert_self _ _))
        (prod_ne_zero_iff.mpr (fun j hj => hr j (mem_insert_of_mem hj))),
      ih (fun j hj => hr j (mem_insert_of_mem hj))]

theorem rational_cyclic_power_expansion {N d : ℕ} [NeZero N] (p : Fin d → ℕ)
    (A : Finset ℚ) (c : ℚ → ℂ) (k : ℕ) (hA : ∀ r ∈ A, 0 < r)
    (x : Fin d → ZMod N) :
    (∑ r ∈ A, c r*rationalCyclicPhase p r x)^k =
      ∑ q ∈ rationalProducts A k, rationalPowerCoefficient A k c q*rationalCyclicPhase p q x := by
  rw [sum_pow']
  have he (v : Fin k → ℚ) (hv : v ∈ rationalTuples A k) :
      (∏ j, c (v j)*rationalCyclicPhase p (v j) x) =
      (∏ j, c (v j))*rationalCyclicPhase p (∏ j, v j) x := by
    rw [prod_mul_distrib, rationalCyclicPhase_product p univ v
      (fun j _ => (hA (v j) (Fintype.mem_piFinset.mp hv j)).ne')]
  have hgroup := sum_fiberwise_of_maps_to
    (show ∀ v ∈ rationalTuples A k, (∏ j, v j) ∈ rationalProducts A k from
      fun v hv => mem_image.mpr ⟨v, hv, rfl⟩)
    (fun v : Fin k → ℚ => (∏ j, c (v j))*rationalCyclicPhase p (∏ j, v j) x)
  change (∑ v ∈ rationalTuples A k, ∏ j, c (v j)*rationalCyclicPhase p (v j) x) = _
  rw [sum_congr rfl he, ← hgroup]
  apply sum_congr rfl
  intro q _
  rw [rationalPowerCoefficient, sum_mul]
  apply sum_congr rfl
  intro v hv
  rw [(mem_filter.mp hv).2]

/-- The arithmetic weighted fourth moment, realized on a finite product of
cyclic groups. No hypercontractivity or torus-moment premise is used. -/
theorem rational_cyclic_weighted_fourth {N d : ℕ} [NeZero N]
    (p : Fin d → ℕ) (hp : Function.Injective p) (A : Finset ℚ)
    (hA : ∀ r ∈ A, 0 < r)
    (hP : ∀ r ∈ A, r.num.natAbs.primeFactors ∪ r.den.primeFactors ⊆ univ.image p)
    (hN : ∀ r ∈ A, ∀ j, (rationalExponent r (p j)).natAbs < N) (c : ℚ → ℂ) :
    (∑ x : Fin d → ZMod N, (∏ _j : Fin d, (N : ℝ)⁻¹) *
      ‖∑ r ∈ A, c r*rationalCyclicPhase p r x‖^4) ≤
      (∑ r ∈ A, ((r.num.natAbs.divisors.card : ℝ)*(r.den.divisors.card : ℝ))^6*‖c r‖^2)^2 := by
  classical
  have hinj : Function.Injective (fun r : A => primeCoordinates p r.val) := by
    intro r s h
    exact Subtype.ext (primeCoordinates_injective_on p A hA hP r.property s.property h)
  have hh := sparse_cyclic_fourth_moment d (fun r : A => primeCoordinates p r.val)
    hinj (fun r j => hN r.val r.property j) (fun r : A => c r.val)
  have hb (r : ℚ) (hr : r ∈ A) :
      (∏ j, integerFourthWeight (rationalExponent r (p j))) ≤
      ((r.num.natAbs.divisors.card : ℝ)*(r.den.divisors.card : ℝ))^6 := by
    have hw := rational_prime_weight_bound (hA r hr) (univ.image p) (hP r hr)
    rwa [prod_image (fun i _ j _ h => hp h)] at hw
  change (∑ x : Fin d → ZMod N, (∏ _j : Fin d, (N : ℝ)⁻¹) *
    ‖∑ r : A, c r.val*rationalCyclicPhase p r.val x‖^4) ≤
    (∑ r : A, (∏ j, integerFourthWeight (rationalExponent r.val (p j)))*‖c r.val‖^2)^2 at hh
  have hpoly (x : Fin d → ZMod N) := sum_coe_sort A (fun r => c r*rationalCyclicPhase p r x)
  have henergy := sum_coe_sort A (fun r =>
    (∏ j, integerFourthWeight (rationalExponent r (p j)))*‖c r‖^2)
  simp_rw [hpoly] at hh
  rw [henergy] at hh
  apply hh.trans
  apply pow_le_pow_left₀ (sum_nonneg (fun r _ => mul_nonneg
    (prod_nonneg (fun j _ => integerFourthWeight_nonneg _)) (sq_nonneg _)))
  exact sum_le_sum (fun r hr => mul_le_mul_of_nonneg_right (hb r hr) (sq_nonneg _))

theorem rational_cyclic_parseval {N d : ℕ} [NeZero N]
    (p : Fin d → ℕ) (A : Finset ℚ) (hA : ∀ r ∈ A, 0 < r)
    (hP : ∀ r ∈ A, r.num.natAbs.primeFactors ∪ r.den.primeFactors ⊆ univ.image p)
    (hN : ∀ r ∈ A, ∀ s ∈ A, ∀ j,
      (rationalExponent r (p j)-rationalExponent s (p j)).natAbs < N) (c : ℚ → ℂ) :
    (∑ x : Fin d → ZMod N, (∏ _j : Fin d, (N : ℝ)⁻¹)*
      ‖∑ r ∈ A, c r*rationalCyclicPhase p r x‖^2) = ∑ r ∈ A, ‖c r‖^2 := by
  apply finite_character_parseval A univ _ _ _ c
  intro r hr s hs
  have hh := productCyclicPhase_orthogonal (primeCoordinates p r) (primeCoordinates p s)
    (hN r hr s hs)
  change _ = if r = s then 1 else 0
  change (∑ x : Fin d → ZMod N, ((∏ _j : Fin d, (N : ℝ)⁻¹ : ℝ) : ℂ)*
    productCyclicPhase (primeCoordinates p r) x*star (productCyclicPhase (primeCoordinates p s) x)) = _
  rw [hh]
  by_cases h : r = s
  · simp [h]
  · have hn : primeCoordinates p r ≠ primeCoordinates p s :=
      fun he => h (primeCoordinates_injective_on p A hA hP hr hs he)
    simp [h, hn]

theorem rational_products_positive (A : Finset ℚ) (k : ℕ) (hA : ∀ r ∈ A, 0 < r) :
    ∀ q ∈ rationalProducts A k, 0 < q := by
  intro q hq
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hq
  exact prod_pos (fun j _ => hA (v j) (Fintype.mem_piFinset.mp hv j))

/-- Exact grouped-product energy is the finite cyclic moment when the modulus
separates the product frequencies. -/
theorem rational_cyclic_moment_identity {N d : ℕ} [NeZero N]
    (p : Fin d → ℕ) (A : Finset ℚ) (k : ℕ) (hA : ∀ r ∈ A, 0 < r)
    (hP : ∀ q ∈ rationalProducts A k,
      q.num.natAbs.primeFactors ∪ q.den.primeFactors ⊆ univ.image p)
    (hN : ∀ q ∈ rationalProducts A k, ∀ r ∈ rationalProducts A k, ∀ j,
      (rationalExponent q (p j)-rationalExponent r (p j)).natAbs < N) (c : ℚ → ℂ) :
    (∑ x : Fin d → ZMod N, (∏ _j : Fin d, (N : ℝ)⁻¹)*
      ‖∑ r ∈ A, c r*rationalCyclicPhase p r x‖^(2*k)) = rationalCoefficientEnergy A k c := by
  have hh := rational_cyclic_parseval p (rationalProducts A k)
    (rational_products_positive A k hA) hP hN (rationalPowerCoefficient A k c)
  change _ = rationalCoefficientEnergy A k c at hh
  rw [← hh]
  apply sum_congr rfl
  intro x _
  rw [← rational_cyclic_power_expansion p A c k hA x, norm_pow, ← pow_mul]
  congr 2
  omega

end Montgomery.RationalMoment
