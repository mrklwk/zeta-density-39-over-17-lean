module
public import DensityEnergyGM.FiniteSupportPowering
public import DensityEnergyGM.PolynomialHeightSecondEnergy

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Finset
namespace Montgomery.RationalMoment

def realDyadicSupport (S : Finset ℕ) (Y : ℝ) : Finset ℕ :=
  S.filter (fun (m : ℕ) => Y < (m : ℝ) ∧ (m : ℝ) ≤ 2 * Y)

/-- Every real wide interval splits into exactly k dyadic pieces, with
all endpoints retained once. The support S is arbitrary and stays finite. -/
theorem real_dyadic_filter_sum {Y : ℝ} (hY : 0 ≤ Y) (S : Finset ℕ)
    (f : ℕ → ℂ) (k : ℕ) :
    (∑ m ∈ S.filter (fun (m : ℕ) => Y < (m : ℝ) ∧ (m : ℝ) ≤ 2 ^ k * Y), f m) =
      ∑ r ∈ range k, ∑ m ∈ realDyadicSupport S (2 ^ r * Y), f m := by
  classical
  induction k with
  | zero =>
      have hEmpty : S.filter (fun (m : ℕ) => Y < (m : ℝ) ∧ (m : ℝ) ≤ 2 ^ 0 * Y) = ∅ := by
        apply filter_eq_empty_iff.mpr
        intro m _ hm
        norm_num at hm
        linarith [hm.1, hm.2]
      rw [hEmpty]
      simp
  | succ k ih =>
      have hOne : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      have hLower : Y ≤ (2 : ℝ) ^ k * Y := le_mul_of_one_le_left hY hOne
      have hUnion : S.filter (fun (m : ℕ) => Y < (m : ℝ) ∧ (m : ℝ) ≤ 2 ^ (k + 1) * Y) =
          S.filter (fun (m : ℕ) => Y < (m : ℝ) ∧ (m : ℝ) ≤ 2 ^ k * Y) ∪
            realDyadicSupport S (2 ^ k * Y) := by
        ext m
        simp only [mem_filter, mem_union, realDyadicSupport, pow_succ]
        constructor
        · intro hm
          by_cases h : (m : ℝ) ≤ 2 ^ k * Y
          · exact Or.inl ⟨hm.1, hm.2.1, h⟩
          · exact Or.inr ⟨hm.1, lt_of_not_ge h, by nlinarith [hm.2.2]⟩
        · intro hm
          rcases hm with hm | hm
          · exact ⟨hm.1, hm.2.1, by nlinarith [hm.2.2, hLower]⟩
          · exact ⟨hm.1, lt_of_le_of_lt hLower hm.2.1, by nlinarith [hm.2.2]⟩
      have hDisjoint : Disjoint
          (S.filter (fun (m : ℕ) => Y < (m : ℝ) ∧ (m : ℝ) ≤ 2 ^ k * Y))
          (realDyadicSupport S (2 ^ k * Y)) := by
        apply disjoint_left.mpr
        intro m hm₁ hm₂
        exact (not_lt_of_ge (mem_filter.mp hm₁).2.2) (mem_filter.mp hm₂).2.1
      rw [hUnion, sum_union hDisjoint, ih, sum_range_succ]

theorem finite_support_power_dyadic_expansion {X : ℝ} (hX : 0 < X)
    (A : Finset ℕ) (hA : ∀ n ∈ A, 0 < n ∧ X < n ∧ (n : ℝ) ≤ 2 * X)
    (a : ℕ → ℂ) {k : ℕ} (hk : 0 < k) (t : ℝ) :
    (∑ n ∈ A, a n * phase n t) ^ k =
      ∑ r ∈ range k, ∑ m ∈ realDyadicSupport (finiteSupportProducts A k) (2 ^ r * X ^ k),
        finiteSupportPowerCoeff A k a m * phase m t := by
  rw [finite_support_power_expansion A a k (fun n hn => (hA n hn).1) t]
  have hFull : (finiteSupportProducts A k).filter
      (fun (m : ℕ) => X ^ k < (m : ℝ) ∧ (m : ℝ) ≤ 2 ^ k * X ^ k) = finiteSupportProducts A k := by
    apply filter_eq_self.mpr
    intro m hm
    have h := finite_support_products_bounds hX (fun n hn => (hA n hn).2) hk hm
    simpa only [mul_pow] using h
  have h := real_dyadic_filter_sum (pow_nonneg hX.le k) (finiteSupportProducts A k)
    (fun m => finiteSupportPowerCoeff A k a m * phase m t) k
  rw [hFull] at h
  exact h

/-- Full-moment recombination: all k powered blocks are retained. -/
theorem finite_support_power_second_le_blocks {X : ℝ} (hX : 0 < X)
    (A : Finset ℕ) (hA : ∀ n ∈ A, 0 < n ∧ X < n ∧ (n : ℝ) ≤ 2 * X)
    (a : ℕ → ℂ) {k : ℕ} (hk : 0 < k) (t : ℝ) :
    ‖∑ n ∈ A, a n * phase n t‖ ^ (2 * k) ≤
      (k : ℝ) * ∑ r ∈ range k,
        ‖∑ m ∈ realDyadicSupport (finiteSupportProducts A k) (2 ^ r * X ^ k),
          finiteSupportPowerCoeff A k a m * phase m t‖ ^ 2 := by
  have h := norm_sum_pow_le (range k)
    (fun r => ∑ m ∈ realDyadicSupport (finiteSupportProducts A k) (2 ^ r * X ^ k),
      finiteSupportPowerCoeff A k a m * phase m t) (p := 2) (by norm_num)
  rw [← finite_support_power_dyadic_expansion hX A hA a hk t] at h
  simpa only [norm_pow, ← pow_mul, mul_comm k 2, card_range, Nat.reduceSub, pow_one] using h

end Montgomery.RationalMoment
