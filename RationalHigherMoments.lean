module
public import RationalEnergyIdentities
public import RationalTransferSubpower

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment

def RationalEnergyBound (k : ℕ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 1 ≤ H → ∀ A : Finset ℚ,
    (∀ r ∈ A, 0 < r ∧ (r.num.natAbs : ℝ) ≤ H ∧ (r.den : ℝ) ≤ H) →
    ∀ c : ℚ → ℂ, rationalCoefficientEnergy A k c ≤ C*H^η*(∑ r ∈ A, ‖c r‖^2)^k

theorem rational_energy_bound_one : RationalEnergyBound 1 := by
  intro η hη
  refine ⟨1, by norm_num, ?_⟩
  intro H hH A hA c
  rw [rational_coefficient_energy_one A (fun r hr => (hA r hr).1) c, pow_one, one_mul]
  exact le_mul_of_one_le_left (sum_nonneg (fun _ _ => sq_nonneg _)) (Real.one_le_rpow hH hη.le)

theorem rational_energy_bound_double {k : ℕ} (hk : 0 < k)
    (hbound : RationalEnergyBound k) : RationalEnergyBound (2*k) := by
  intro η hη
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨C, hC, htwo⟩ := rational_coefficient_energy_two_subpower (show 0 < η/(2*k) by positivity)
  obtain ⟨D, hD, hkbound⟩ := hbound (η/4) (by positivity)
  refine ⟨C*D^2, by positivity, ?_⟩
  intro H hH A hA c
  let S : ℝ := ∑ r ∈ A, ‖c r‖^2
  have hS : 0 ≤ S := sum_nonneg (fun _ _ => sq_nonneg _)
  have hH0 : 0 < H := by linarith
  have he := htwo (H^k) (one_le_pow₀ hH) (rationalProducts A k)
    (rational_product_height A k hA) (rationalPowerCoefficient A k c)
  change rationalCoefficientEnergy (rationalProducts A k) 2 (rationalPowerCoefficient A k c) ≤
    C*(H^k)^(η/(2*k))*(rationalCoefficientEnergy A k c)^2 at he
  have hb := hkbound H hH A hA c
  change rationalCoefficientEnergy A k c ≤ D*H^(η/4)*S^k at hb
  have hE : 0 ≤ rationalCoefficientEnergy A k c := sum_nonneg (fun _ _ => sq_nonneg _)
  have hpow : (H^k)^(η/(2*k))*(H^(η/4))^2 = H^η := by
    rw [← Real.rpow_natCast H k, ← Real.rpow_mul hH0.le,
      ← Real.rpow_natCast (H^(η/4)) 2, ← Real.rpow_mul hH0.le, ← Real.rpow_add hH0]
    congr 1
    field_simp
    ring
  rw [rational_coefficient_energy_double A k (fun r hr => (hA r hr).1) c]
  calc
    _ ≤ C*(H^k)^(η/(2*k))*(rationalCoefficientEnergy A k c)^2 := he
    _ ≤ C*(H^k)^(η/(2*k))*(D*H^(η/4)*S^k)^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hE hb 2) (by positivity)
    _ = (C*D^2)*((H^k)^(η/(2*k))*(H^(η/4))^2)*S^(2*k) := by
      rw [show S^(2*k) = (S^k)^2 by rw [← pow_mul, Nat.mul_comm]]
      ring
    _ = _ := by rw [hpow]

theorem rational_energy_bound_power_two (n : ℕ) : RationalEnergyBound (2^n) := by
  induction n with
  | zero => simpa using rational_energy_bound_one
  | succ n ih =>
    simpa only [pow_succ', Nat.mul_comm] using
      rational_energy_bound_double (pow_pos (by omega : 0 < 2) n) ih

theorem rational_energy_bound_downward {k m : ℕ} (hk : 0 < k) (hkm : k ≤ m)
    (hbound : RationalEnergyBound m) : RationalEnergyBound k := by
  intro η hη
  obtain ⟨D, hD, hd⟩ := hbound η hη
  refine ⟨1+D, by positivity, ?_⟩
  intro H hH A hA c
  let S : ℝ := ∑ r ∈ A, ‖c r‖^2
  have hS : 0 ≤ S := sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hSzero : S = 0
  · rw [rational_coefficient_energy_zero A hk (fun r hr => (hA r hr).1) c hSzero]
    positivity
  have hSp : 0 < S := lt_of_le_of_ne hS (Ne.symm hSzero)
  let a : ℂ := (Real.sqrt S : ℝ)
  let b : ℚ → ℂ := fun r => a⁻¹*c r
  have ha : a ≠ 0 := by dsimp [a]; exact_mod_cast (Real.sqrt_pos.mpr hSp).ne'
  have hanorm : ‖a‖^2 = S := by
    simp only [a, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hS]
  have hb : (∑ r ∈ A, ‖b r‖^2) = 1 := by
    simp only [b, norm_mul, norm_inv, mul_pow, ← mul_sum, inv_pow, hanorm]
    change S⁻¹*S = 1
    exact inv_mul_cancel₀ hSzero
  have hlow := rational_coefficient_energy_le_one_add A k m hkm (fun r hr => (hA r hr).1) b
  have hhigh := hd H hH A hA b
  rw [hb, one_pow, mul_one] at hhigh
  have hHpow : 1 ≤ H^η := Real.one_le_rpow hH hη.le
  have hnormbound : rationalCoefficientEnergy A k b ≤ (1+D)*H^η := by
    nlinarith
  have hc : c = fun r => a*b r := by
    funext r
    dsimp [b]
    rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  have hscale : rationalCoefficientEnergy A k c = S^k*rationalCoefficientEnergy A k b := by
    conv_lhs => rw [hc, rational_coefficient_energy_smul]
    rw [pow_mul, hanorm]
  rw [hscale]
  have hh := mul_le_mul_of_nonneg_left hnormbound (pow_nonneg hS k)
  change _ ≤ (1+D)*H^η*S^k
  nlinarith

/-- All fixed rational moments: a fully quantified small-power estimate for
the exact grouped-product coefficient energy, with arbitrary coefficients. -/
theorem rational_coefficient_energy_subpower {k : ℕ} (hk : 1 ≤ k) : RationalEnergyBound k := by
  apply rational_energy_bound_downward (by omega : 0 < k) (Nat.le_of_lt (Nat.lt_two_pow_self (n := k)))
  exact rational_energy_bound_power_two k

end Montgomery.RationalMoment
