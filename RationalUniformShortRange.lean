module
public import RationalShortRange
public import RationalMomentCover

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment

theorem rational_energy_trivial (A : Finset ℚ) (W : Finset ℝ) :
    rationalEnergy A W ≤ (A.card : ℝ)*(W.card : ℝ)^2 := by
  have hphase (r : ℚ) (t : ℝ) : ‖phase r t‖ = 1 := by
    rw [← exponentialPhase_log, exponentialPhase_norm]
  unfold rationalEnergy
  calc
    _ ≤ ∑ _r ∈ A, (W.card : ℝ)^2 := by
      apply sum_le_sum
      intro r _
      apply pow_le_pow_left₀ (norm_nonneg _)
      exact (norm_sum_le _ _).trans_eq (by simp only [hphase, sum_const, nsmul_eq_mul, mul_one])
    _ = _ := by simp

theorem rational_card_le_height (A : Finset ℚ) (H : ℕ)
    (hA : ∀ r ∈ A, 0 < r ∧ r.den ≤ H ∧ |Real.log (r : ℝ)| ≤ 1) :
    A.card ≤ 3*H*H := by
  have hmaps : Set.MapsTo positiveRatPair (↑A : Set ℚ)
      (↑(Icc 1 (3*H) ×ˢ Icc 1 H) : Set (ℕ × ℕ)) := by
    intro r hr
    have hn : (r.num.natAbs : ℝ) ≤ 3*(H : ℝ) := by
      have hd : (r.den : ℝ) ≤ H := by exact_mod_cast (hA r hr).2.1
      exact (numerator_bound_of_log (hA r hr).1 (hA r hr).2.2).trans
        ((mul_le_mul_of_nonneg_left hd (Real.exp_pos _).le).trans
          (mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le (Nat.cast_nonneg _)))
    exact mem_product.mpr ⟨mem_Icc.mpr
      ⟨Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr (hA r hr).1.ne'), by exact_mod_cast hn⟩,
      mem_Icc.mpr ⟨r.pos, (hA r hr).2.1⟩⟩
  have hinj : Set.InjOn positiveRatPair (↑A : Set ℚ) := by
    intro r hr s hs h
    rw [← positiveRatPair_ratio (hA r hr).1, ← positiveRatPair_ratio (hA s hs).1, h]
  simpa using card_le_card_of_injOn positiveRatPair hmaps hinj

/-- A single constant covers the finite set of moment orders selected by
the exponent-covering lemma. -/
theorem rational_energy_finite_cover {K : ℕ} (hK : 1 ≤ K)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ D : ℝ, 0 < D ∧ ∀ (T t₀ r m : ℝ), 1 ≤ T → r ≤ 1 →
      ((K : ℝ)+1)/(2*K+1) ≤ r → δ ≤ m → m ≤ r/K →
      ∀ (H : ℕ), 1 ≤ H → (H : ℝ) = T^m →
      ∀ A : Finset ℚ,
      (∀ q ∈ A, 0 < q ∧ q.den ≤ H ∧ |Real.log (q : ℝ)| ≤ 1) →
      ∀ W : Finset ℝ, (W.card : ℝ) = T^r →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      rationalEnergy A W ≤ D*(H : ℝ)^η*(H : ℝ)*(W.card : ℝ)^2 := by
  choose C hC hbound using (fun n : ℕ => rational_energy_linear_height (k := n+1) (by omega) hη)
  let J := ⌈1/δ⌉₊
  let D := 1+∑ n ∈ range J, C n
  have hD : 0 < D := by
    have hs : 0 ≤ ∑ n ∈ range J, C n := sum_nonneg (fun n _ => (hC n).le)
    dsimp [D]
    linarith
  refine ⟨D, hD, ?_⟩
  intro T t₀ r m hT hr1 hr hδm hm H hH hHpow A hA W hRpow hW hsep
  obtain ⟨k, hKk, hkJ, hlo, hhi⟩ := finite_moment_cover hK hδ hδm hr1 hr hm
  have hk : 1 ≤ k := hK.trans hKk
  have hki : k-1+1 = k := Nat.sub_add_cancel hk
  have hCk : C (k-1) ≤ D := by
    have hh : C (k-1) ≤ ∑ n ∈ range J, C n :=
      single_le_sum (fun n _ => (hC n).le) (mem_range.mpr (by dsimp [J]; omega))
    dsimp [D]
    linarith
  have hHk : (H : ℝ)^k = T^((k : ℝ)*m) := by
    rw [hHpow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ T), mul_comm]
  have hbalance1 : (H : ℝ)^k ≤ W.card := by
    rw [hHk, hRpow]
    exact Real.rpow_le_rpow_of_exponent_le hT hhi
  have hbalance2 : T ≤ (H : ℝ)^k*W.card := by
    rw [hHk, hRpow, ← Real.rpow_add (by linarith : 0 < T)]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT (show 1 ≤ (k : ℝ)*m+r by linarith)
  have hh := hbound (k-1) H hH T t₀ (by linarith) A hA W hW hsep
  rw [hki] at hh
  exact (hh hbalance1 hbalance2).trans (by gcongr)

/-- Complete short-range reduced-rational energy estimate, including very
small heights. The constant is fixed before the height and exponent parameters. -/
theorem rational_energy_short_range {K : ℕ} (hK : 1 ≤ K) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t₀ r m : ℝ), 1 ≤ T → r ≤ 1 →
      ((K : ℝ)+1)/(2*K+1) ≤ r → m ≤ r/K →
      ∀ (H : ℕ), 1 ≤ H → (H : ℝ) = T^m →
      ∀ A : Finset ℚ,
      (∀ q ∈ A, 0 < q ∧ q.den ≤ H ∧ |Real.log (q : ℝ)| ≤ 1) →
      ∀ W : Finset ℝ, (W.card : ℝ) = T^r →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      rationalEnergy A W ≤ C*T^η*(H : ℝ)*(W.card : ℝ)^2 := by
  obtain ⟨D, hD, hcover⟩ := rational_energy_finite_cover hK
    (show 0 < η/2 by positivity) (show 0 < η/2 by positivity)
  refine ⟨3+D, by positivity, ?_⟩
  intro T t₀ r m hT hr1 hr hm H hH hHpow A hA W hRpow hW hsep
  have hTp : 0 < T := by linarith
  have hHR : (0 : ℝ) ≤ H := Nat.cast_nonneg _
  have hW0 : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
  have hhalf : T^(η/2) ≤ T^η := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  by_cases hsmall : m ≤ η/2
  · have hh : (H : ℝ) ≤ T^η := by
      rw [hHpow]
      exact (Real.rpow_le_rpow_of_exponent_le hT hsmall).trans hhalf
    have hcard : (A.card : ℝ) ≤ 3*(H : ℝ)*(H : ℝ) := by
      exact_mod_cast rational_card_le_height A H hA
    calc
      _ ≤ (A.card : ℝ)*(W.card : ℝ)^2 := rational_energy_trivial A W
      _ ≤ (3*(H : ℝ)*(H : ℝ))*(W.card : ℝ)^2 := by gcongr
      _ ≤ (3*T^η*(H : ℝ))*(W.card : ℝ)^2 := by gcongr
      _ ≤ _ := by gcongr; linarith
  · have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have hm1 : m ≤ 1 := by
      have hh := (le_div_iff₀ (by linarith : (0 : ℝ) < K)).mp hm
      by_contra hn
      have hmb : 1 < m := lt_of_not_ge hn
      nlinarith [mul_nonneg (show 0 ≤ m-1 by linarith) (show 0 ≤ (K : ℝ)-1 by linarith)]
    have hHT : (H : ℝ) ≤ T := by
      rw [hHpow]
      simpa using Real.rpow_le_rpow_of_exponent_le hT hm1
    have hh := hcover T t₀ r m hT hr1 hr (le_of_lt (lt_of_not_ge hsmall)) hm
      H hH hHpow A hA W hRpow hW hsep
    have hpow : (H : ℝ)^(η/2) ≤ T^η :=
      (Real.rpow_le_rpow hHR hHT (by positivity)).trans hhalf
    exact hh.trans (by gcongr; linarith)

end Montgomery.RationalMoment
