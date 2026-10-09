import Mathlib
set_option autoImplicit false
namespace GuthMaynard.Improvement

/-- Exact multiplicity bound for a nonzero product. A subpower upper bound
for the divisor function is a distinct obligation. -/
theorem product_fiber_card_le_divisors (P : Finset (ℕ × ℕ)) {n : ℕ}
    (hn : n ≠ 0) (hP : ∀ p ∈ P, p.1*p.2=n) : P.card ≤ n.divisors.card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    exact Nat.mem_divisors.mpr ⟨⟨p.2, (hP p hp).symm⟩, hn⟩
  · intro p hp q hq heq
    have hp0 : p.1 ≠ 0 := by
      intro hz
      have he := hP p hp
      simp [hz] at he
      exact hn he.symm
    apply Prod.ext heq
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp0)
    rw [hP p hp, heq, hP q hq]

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.product_fiber_card_le_divisors
