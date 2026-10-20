module
public import RationalHigherMoments

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment

theorem numerator_bound_of_log {r : ℚ} (hr : 0 < r)
    (hlog : |Real.log (r : ℝ)| ≤ 1) :
    (r.num.natAbs : ℝ) ≤ Real.exp 1*(r.den : ℝ) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hrat : (r.num.natAbs : ℝ)/(r.den : ℝ) = (r : ℝ) := by
    have hh := positiveRatPair_ratio hr
    change (r.num.natAbs : ℚ)/(r.den : ℚ) = r at hh
    simpa only [Rat.cast_div, Rat.cast_natCast] using congrArg (fun q : ℚ => (q : ℝ)) hh
  have hval : (r : ℝ) ≤ Real.exp 1 := by
    rw [← Real.exp_log hrR]
    exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) hlog)
  rw [← hrat] at hval
  exact (div_le_iff₀ (by exact_mod_cast r.pos : (0 : ℝ) < r.den)).mp hval

/-- Complete finite-height rational moment theorem. The coefficient-energy
estimate is proved internally, and the constant is uniform in all data after
the fixed moment order and loss. -/
theorem rational_higher_moment {k : ℕ} (hk : 1 ≤ k) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : ℕ), 1 ≤ H → ∀ (T t₀ : ℝ), 0 ≤ T →
      ∀ (A : Finset ℚ) (c : ℚ → ℂ),
      (∀ r ∈ A, 0 < r ∧ r.den ≤ H ∧ |Real.log (r : ℝ)| ≤ 1) →
      ∀ (W : Finset ℝ), (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∑ t ∈ W, ‖∑ r ∈ A, c r*phase r t‖^(2*k)) ≤
        C*(T+(H : ℝ)^(2*k))*(H : ℝ)^η*(∑ r ∈ A, ‖c r‖^2)^k := by
  obtain ⟨C, hC, htransfer⟩ := rational_moment_transfer_subpower hk (show 0 < η/2 by positivity)
  obtain ⟨D, hD, hcoeff⟩ := rational_coefficient_energy_subpower hk (η/2) (by positivity)
  refine ⟨C*D*(Real.exp 1)^(η/2), by positivity, ?_⟩
  intro H hH T t₀ hT A c hA W hW hsep
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hHpos : (0 : ℝ) < H := by linarith
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  have hheight : 1 ≤ Real.exp 1*(H : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr he1) (sub_nonneg.mpr hHR)]
  have hheights : ∀ r ∈ A, 0 < r ∧ (r.num.natAbs : ℝ) ≤ Real.exp 1*(H : ℝ) ∧
      (r.den : ℝ) ≤ Real.exp 1*(H : ℝ) := by
    intro r hr
    have hd : (r.den : ℝ) ≤ H := by exact_mod_cast (hA r hr).2.1
    refine ⟨(hA r hr).1, ?_, ?_⟩
    · exact (numerator_bound_of_log (hA r hr).1 (hA r hr).2.2).trans
        (mul_le_mul_of_nonneg_left hd (Real.exp_pos _).le)
    · exact hd.trans (le_mul_of_one_le_left hHpos.le he1)
  have henergy := hcoeff (Real.exp 1*(H : ℝ)) hheight A hheights c
  have hm := htransfer H hH T t₀ hT A c hA W hW hsep
  have hpow : (H : ℝ)^(η/2)*(H : ℝ)^(η/2) = (H : ℝ)^η := by
    rw [← Real.rpow_add hHpos]
    congr 1
    ring
  calc
    _ ≤ C*(T+(H : ℝ)^(2*k))*(H : ℝ)^(η/2)*rationalCoefficientEnergy A k c := hm
    _ ≤ C*(T+(H : ℝ)^(2*k))*(H : ℝ)^(η/2)*
        (D*(Real.exp 1*(H : ℝ))^(η/2)*(∑ r ∈ A, ‖c r‖^2)^k) :=
      mul_le_mul_of_nonneg_left henergy (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (Real.exp_pos _).le hHpos.le]
      calc
        _ = (C*D*(Real.exp 1)^(η/2))*(T+(H : ℝ)^(2*k))*
            ((H : ℝ)^(η/2)*(H : ℝ)^(η/2))*(∑ r ∈ A, ‖c r‖^2)^k := by ring
        _ = _ := by rw [hpow]

/-- Unconditional dual bound for the literal sum over rational frequencies.
No higher-moment estimate is assumed as a premise. -/
theorem rational_dual_moment {k : ℕ} (hk : 1 ≤ k) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : ℕ), 1 ≤ H → ∀ (T t₀ : ℝ), 0 ≤ T →
      ∀ (A : Finset ℚ),
      (∀ r ∈ A, 0 < r ∧ r.den ≤ H ∧ |Real.log (r : ℝ)| ≤ 1) →
      ∀ (W : Finset ℝ), (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      rationalEnergy A W ^ k ≤
        (W.card : ℝ)^(2*k-1)*(C*(T+(H : ℝ)^(2*k))*(H : ℝ)^η) := by
  obtain ⟨C, hC, hm⟩ := rational_higher_moment hk hη
  refine ⟨C, hC, ?_⟩
  intro H hH T t₀ hT A hA W hW hsep
  apply rational_energy_pow_le A W hk (by positivity)
  intro c
  exact hm H hH T t₀ hT A c hA W hW hsep

end Montgomery.RationalMoment
