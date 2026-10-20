module
public import RationalCoefficientEnergy

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment

theorem cyclic_probability_mass {N d : ℕ} [NeZero N] :
    (∑ _x : Fin d → ZMod N, ∏ _j : Fin d, (N : ℝ)⁻¹) = 1 := by
  rw [← Fintype.prod_sum (fun (_ : Fin d) (_ : ZMod N) => (N : ℝ)⁻¹)]
  simp [ZMod.card, NeZero.ne N]

theorem rational_coefficient_energy_one (A : Finset ℚ) (hA : ∀ r ∈ A, 0 < r)
    (c : ℚ → ℂ) : rationalCoefficientEnergy A 1 c = ∑ r ∈ A, ‖c r‖^2 := by
  obtain ⟨d, p, N, hN, _, hP, _, hdiff⟩ := finite_rational_prime_model (A ∪ rationalProducts A 1)
  let : NeZero N := ⟨hN.ne'⟩
  have hm := rational_cyclic_moment_identity (N := N) p A 1 hA
    (fun q hq => hP q (mem_union_right _ hq))
    (fun q hq r hr => hdiff q (mem_union_right _ hq) r (mem_union_right _ hr)) c
  have hs := rational_cyclic_parseval (N := N) p A hA
    (fun r hr => hP r (mem_union_left _ hr))
    (fun q hq r hr => hdiff q (mem_union_left _ hq) r (mem_union_left _ hr)) c
  norm_num only [show 2*1 = 2 by omega] at hm
  exact hm.symm.trans hs

theorem rational_coefficient_energy_double (A : Finset ℚ) (k : ℕ)
    (hA : ∀ r ∈ A, 0 < r) (c : ℚ → ℂ) :
    rationalCoefficientEnergy A (2*k) c =
      rationalCoefficientEnergy (rationalProducts A k) 2 (rationalPowerCoefficient A k c) := by
  obtain ⟨d, p, N, hN, _, hP, _, hdiff⟩ := finite_rational_prime_model
    (rationalProducts A (2*k) ∪ rationalProducts (rationalProducts A k) 2)
  let : NeZero N := ⟨hN.ne'⟩
  have hm := rational_cyclic_moment_identity (N := N) p A (2*k) hA
    (fun q hq => hP q (mem_union_left _ hq))
    (fun q hq r hr => hdiff q (mem_union_left _ hq) r (mem_union_left _ hr)) c
  have hs := rational_cyclic_moment_identity (N := N) p (rationalProducts A k) 2
    (rational_products_positive A k hA)
    (fun q hq => hP q (mem_union_right _ hq))
    (fun q hq r hr => hdiff q (mem_union_right _ hq) r (mem_union_right _ hr))
    (rationalPowerCoefficient A k c)
  rw [← hm, ← hs]
  apply sum_congr rfl
  intro x _
  rw [← rational_cyclic_power_expansion p A c k hA x, norm_pow, ← pow_mul]
  congr 2
  omega

/-- A lower moment is bounded by one plus a higher moment in a probability
model. This elementary inequality avoids a separate interpolation theorem. -/
theorem rational_coefficient_energy_le_one_add (A : Finset ℚ) (k m : ℕ)
    (hkm : k ≤ m) (hA : ∀ r ∈ A, 0 < r) (c : ℚ → ℂ) :
    rationalCoefficientEnergy A k c ≤ 1 + rationalCoefficientEnergy A m c := by
  obtain ⟨d, p, N, hN, _, hP, _, hdiff⟩ :=
    finite_rational_prime_model (rationalProducts A k ∪ rationalProducts A m)
  let : NeZero N := ⟨hN.ne'⟩
  have hk := rational_cyclic_moment_identity (N := N) p A k hA
    (fun q hq => hP q (mem_union_left _ hq))
    (fun q hq r hr => hdiff q (mem_union_left _ hq) r (mem_union_left _ hr)) c
  have hm := rational_cyclic_moment_identity (N := N) p A m hA
    (fun q hq => hP q (mem_union_right _ hq))
    (fun q hq r hr => hdiff q (mem_union_right _ hq) r (mem_union_right _ hr)) c
  rw [← hk, ← hm]
  have hpow (z : ℂ) : ‖z‖^(2*k) ≤ 1+‖z‖^(2*m) := by
    by_cases hz : ‖z‖ ≤ 1
    · exact (pow_le_one₀ (norm_nonneg _) hz).trans (by linarith [pow_nonneg (norm_nonneg z) (2*m)])
    · have hh := pow_le_pow_right₀ (le_of_lt (lt_of_not_ge hz))
        (Nat.mul_le_mul_left 2 hkm)
      exact hh.trans (by linarith)
  calc
    _ ≤ ∑ x : Fin d → ZMod N, (∏ _j : Fin d, (N : ℝ)⁻¹)*
        (1+‖∑ r ∈ A, c r*rationalCyclicPhase p r x‖^(2*m)) :=
      sum_le_sum (fun _ _ => mul_le_mul_of_nonneg_left (hpow _) (by positivity))
    _ = _ := by
      simp only [mul_add, mul_one, sum_add_distrib, cyclic_probability_mass]

theorem rational_power_coefficient_smul (A : Finset ℚ) (k : ℕ) (c : ℚ → ℂ) (a : ℂ)
    (r : ℚ) :
    rationalPowerCoefficient A k (fun x => a*c x) r = a^k*rationalPowerCoefficient A k c r := by
  unfold rationalPowerCoefficient
  simp only [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, ← mul_sum]

theorem rational_coefficient_energy_smul (A : Finset ℚ) (k : ℕ) (c : ℚ → ℂ) (a : ℂ) :
    rationalCoefficientEnergy A k (fun x => a*c x) = ‖a‖^(2*k)*rationalCoefficientEnergy A k c := by
  unfold rationalCoefficientEnergy
  simp only [rational_power_coefficient_smul A k c a, norm_mul, norm_pow, mul_pow, ← mul_sum]
  rw [← pow_mul, Nat.mul_comm k 2]

theorem rational_mul_numerator_le {r s : ℚ} (hr : r ≠ 0) (hs : s ≠ 0) :
    (r*s).num.natAbs ≤ r.num.natAbs*s.num.natAbs := by
  have he := congrArg Int.natAbs (Rat.num_mul_num_eq_num_mul_gcd r s)
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at he
  apply Nat.le_of_dvd
  · exact Nat.mul_pos (Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hr))
      (Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hs))
  · exact ⟨_, he⟩

theorem rational_product_numerator {ι : Type*} (S : Finset ι) (r : ι → ℚ)
    (hr : ∀ i ∈ S, r i ≠ 0) :
    (∏ i ∈ S, r i).num.natAbs ≤ ∏ i ∈ S, (r i).num.natAbs := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [prod_insert hi, prod_insert hi]
    exact (rational_mul_numerator_le (hr i (mem_insert_self _ _))
      (prod_ne_zero_iff.mpr (fun j hj => hr j (mem_insert_of_mem hj)))).trans
      (Nat.mul_le_mul_left _ (ih (fun j hj => hr j (mem_insert_of_mem hj))))

theorem rational_product_height (A : Finset ℚ) (k : ℕ) {H : ℝ}
    (hA : ∀ r ∈ A, 0 < r ∧ (r.num.natAbs : ℝ) ≤ H ∧ (r.den : ℝ) ≤ H) :
    ∀ q ∈ rationalProducts A k,
      0 < q ∧ (q.num.natAbs : ℝ) ≤ H^k ∧ (q.den : ℝ) ≤ H^k := by
  intro q hq
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hq
  have hvA (j : Fin k) := hA (v j) (Fintype.mem_piFinset.mp hv j)
  refine ⟨prod_pos (fun j _ => (hvA j).1), ?_, ?_⟩
  · calc
      _ ≤ ((∏ j, (v j).num.natAbs : ℕ) : ℝ) := by
        exact_mod_cast rational_product_numerator univ v (fun j _ => (hvA j).1.ne')
      _ = ∏ j, ((v j).num.natAbs : ℝ) := by push_cast; rfl
      _ ≤ ∏ _j : Fin k, H := prod_le_prod₀ (fun _ _ => by positivity) (fun j _ => (hvA j).2.1)
      _ = H^k := by simp
  · calc
      _ ≤ ((∏ j, (v j).den : ℕ) : ℝ) := by exact_mod_cast rational_product_denominator univ v
      _ = ∏ j, ((v j).den : ℝ) := by push_cast; rfl
      _ ≤ ∏ _j : Fin k, H := prod_le_prod₀ (fun _ _ => by positivity) (fun j _ => (hvA j).2.2)
      _ = H^k := by simp

theorem rational_coefficient_energy_zero (A : Finset ℚ) {k : ℕ} (hk : 0 < k)
    (hA : ∀ r ∈ A, 0 < r) (c : ℚ → ℂ) (hc : ∑ r ∈ A, ‖c r‖^2 = 0) :
    rationalCoefficientEnergy A k c = 0 := by
  have hz (r : ℚ) (hr : r ∈ A) : c r = 0 := by
    have hsum := (sum_eq_zero_iff_of_nonneg (fun r _ => sq_nonneg ‖c r‖)).mp hc r hr
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (c r)]
  obtain ⟨d, p, N, hN, _, hP, _, hdiff⟩ := finite_rational_prime_model (rationalProducts A k)
  let : NeZero N := ⟨hN.ne'⟩
  rw [← rational_cyclic_moment_identity (N := N) p A k hA hP hdiff c]
  apply sum_eq_zero
  intro x _
  have hsum : (∑ r ∈ A, c r*rationalCyclicPhase p r x) = 0 :=
    sum_eq_zero (fun r hr => by rw [hz r hr, zero_mul])
  rw [hsum, norm_zero, zero_pow (by omega : 2*k ≠ 0), mul_zero]

end Montgomery.RationalMoment
