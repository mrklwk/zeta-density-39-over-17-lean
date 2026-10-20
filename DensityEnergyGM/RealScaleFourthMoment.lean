module
public import DensityEnergyGM.RealScaleSecondMoment
public import DensityEnergyGM.CoprimeEndpoint

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Finset GuthMaynard.NativeMoment GuthMaynard.Improvement
namespace Montgomery.RationalMoment

/-- The complete coprime fourth-moment minimum at the exact real reduced
scale. Both alternatives concern the same finite reduced fraction set. -/
theorem real_scale_coprime_fourth_min_native (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (M T : ℝ) (Q : Finset (ℕ × ℕ)) (W : Finset ℝ),
        0 < M → T₀ ≤ T → M ^ 2 ≤ T →
        (∀ q ∈ Q, 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2 ∧
          M < q.1 ∧ (q.1 : ℝ) ≤ 2 * M ∧ M < q.2 ∧ (q.2 : ℝ) ≤ 2 * M) →
        IsSeparated 1 W → InBaseInterval T W →
        (∑ q ∈ Q, ‖gmR W ((q.1 : ℝ) / q.2)‖ ^ 4) ≤ C * T ^ ε *
          min (M * ((W.card : ℝ) ^ 4 +
            T ^ (1 / 2 : ℝ) * (W.card : ℝ) *
              (discreteAdditiveEnergy W : ℝ) ^ (3 / 4 : ℝ)))
            (T * (discreteAdditiveEnergy W : ℝ)) := by
  obtain ⟨C, T₀, hC, hT₀, hNative⟩ := nativeCoprimeFourth_min ε hε
  let D : ℝ := C + 4 + 28672 * Real.pi
  have hDpos : 0 < D := by dsimp only [D]; positivity
  refine ⟨D, max T₀ 2, hDpos, le_max_right _ _, ?_⟩
  intro M T Q W hM hT hMT hQ hSep hBase
  let R : ℝ := W.card
  let E : ℝ := discreteAdditiveEnergy W
  let K₀ : ℝ := R ^ 4 + T ^ (1 / 2 : ℝ) * R * E ^ (3 / 4 : ℝ)
  let F : ℕ × ℕ → ℝ := fun q => ‖gmR W ((q.1 : ℝ) / q.2)‖ ^ 4
  have hTtwo : 2 ≤ T := (le_max_right _ _).trans hT
  have hTpos : 0 < T := by linarith
  have hPow : 1 ≤ T ^ ε := Real.one_le_rpow (by linarith) hε.le
  have hR0 : 0 ≤ R := Nat.cast_nonneg _
  have hE0 : 0 ≤ E := Nat.cast_nonneg _
  have hK0 : 0 ≤ K₀ := by dsimp only [K₀]; positivity
  have hRfour : R ^ 4 ≤ K₀ := by
    have hp : 0 ≤ T ^ (1 / 2 : ℝ) * R * E ^ (3 / 4 : ℝ) := by positivity
    dsimp only [K₀]; linarith
  have hDlarge : C + 3 ≤ D := by dsimp only [D]; linarith [Real.pi_pos]
  have hDtwo : 2 ≤ D := by dsimp only [D]; linarith [Real.pi_pos]
  have hDpow : D ≤ D * T ^ ε := by nlinarith
  change (∑ q ∈ Q, F q) ≤ D * T ^ ε * min (M * K₀) (T * E)
  have hFirst : (∑ q ∈ Q, F q) ≤ D * T ^ ε * (M * K₀) := by
    by_cases hMone : 1 ≤ M
    · let N : ℕ := ⌊M⌋₊
      let e : ℕ := 2 * N + 1
      have hN : 0 < N := (Nat.one_le_floor_iff M).mpr hMone
      have hNM : (N : ℝ) ≤ M := Nat.floor_le hM.le
      have hNT : (N : ℝ) ^ 2 ≤ T :=
        (pow_le_pow_left₀ (Nat.cast_nonneg N) hNM 2).trans hMT
      have heA : e ∉ dyadicInterval N := by
        intro h
        have hhi := (Finset.mem_Ioc.mp h).2
        dsimp only [e] at hhi
        omega
      have hSub : Q ⊆ ((insert e (dyadicInterval N)) ×ˢ
          (insert e (dyadicInterval N))).filter (fun q => Nat.Coprime q.1 q.2) := by
        intro q hq
        obtain ⟨h1, h2, hcop, hl1, hu1, hl2, hu2⟩ := hQ q hq
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨real_dyadic_indices_subset_floor_insert hM.le
              ((sourceRatioIndices_mem hM.le q.1).mpr ⟨hl1, hu1⟩),
            real_dyadic_indices_subset_floor_insert hM.le
              ((sourceRatioIndices_mem hM.le q.2).mpr ⟨hl2, hu2⟩)⟩, hcop⟩
      have hCover := coprime_fourth_insert_product_le heA W
      have hCard : (dyadicInterval N).card = N := by
        simp only [dyadicInterval, Nat.card_Ioc]
        omega
      rw [hCard] at hCover
      change (∑ q ∈ ((insert e (dyadicInterval N)) ×ˢ
        (insert e (dyadicInterval N))).filter (fun q => Nat.Coprime q.1 q.2), F q) ≤
          nativeCoprimeFourth N W + (2 * (N : ℝ) + 1) * R ^ 4 at hCover
      have hInner : (∑ q ∈ Q, F q) ≤
          nativeCoprimeFourth N W + (2 * (N : ℝ) + 1) * R ^ 4 := by
        exact (Finset.sum_le_sum_of_subset_of_nonneg hSub
          (fun q hq hnot => by dsimp only [F]; positivity)).trans hCover
      have hMain : nativeCoprimeFourth N W ≤ C * T ^ ε * ((N : ℝ) * K₀) := by
        have h := hNative N T W hN ((le_max_left _ _).trans hT) hNT hSep hBase
        exact h.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity))
      have hCorrection : (2 * (N : ℝ) + 1) * R ^ 4 ≤ 3 * M * K₀ := by
        have hm : 2 * (N : ℝ) + 1 ≤ 3 * M := by linarith
        exact mul_le_mul hm hRfour (by positivity) (by positivity)
      have hMainScale : C * T ^ ε * ((N : ℝ) * K₀) ≤ C * T ^ ε * (M * K₀) := by gcongr
      have hLoss : 3 * M * K₀ ≤ 3 * T ^ ε * (M * K₀) := by
        have h := mul_le_mul_of_nonneg_right hPow (mul_nonneg hM.le hK0)
        nlinarith
      have hBound : (∑ q ∈ Q, F q) ≤ (C + 3) * T ^ ε * (M * K₀) := by
        linarith [hMain.trans hMainScale]
      exact hBound.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hDlarge (by positivity)) (mul_nonneg hM.le hK0))
    · by_cases hNonempty : Q.Nonempty
      · obtain ⟨q, hq⟩ := hNonempty
        have hq2 := (hQ q hq).2.2.2.1
        have hqUpper := (hQ q hq).2.2.2.2.1
        have hqOne : (1 : ℝ) ≤ q.1 := by exact_mod_cast (hQ q hq).1
        have hMhalf : (1 / 2 : ℝ) ≤ M := by linarith
        have hSmall : M < 1 := lt_of_not_ge hMone
        have hSub : Q ⊆ {(1, 1)} := by
          intro p hp
          obtain ⟨hp1, hp2, hcop, hl1, hu1, hl2, hu2⟩ := hQ p hp
          have h1 : p.1 < 2 := by exact_mod_cast (show (p.1 : ℝ) < 2 by linarith)
          have h2 : p.2 < 2 := by exact_mod_cast (show (p.2 : ℝ) < 2 by linarith)
          exact Finset.mem_singleton.mpr (Prod.ext (by omega) (by omega))
        have hOne : (∑ p ∈ {(1, 1)}, F p) = R ^ 4 := by simp [F, gmR_one, R]
        have hSum : (∑ p ∈ Q, F p) ≤ R ^ 4 := by
          exact (Finset.sum_le_sum_of_subset_of_nonneg hSub
            (fun p hp hnot => by dsimp only [F]; positivity)).trans_eq hOne
        calc
          _ ≤ R ^ 4 := hSum
          _ ≤ 2 * (M * K₀) := by nlinarith
          _ ≤ _ := mul_le_mul_of_nonneg_right (hDtwo.trans hDpow) (mul_nonneg hM.le hK0)
      · rw [Finset.not_nonempty_iff_eq_empty.mp hNonempty, Finset.sum_empty]
        positivity
  have hShort : (∑ q ∈ Q, F q) ≤ D * T ^ ε * (T * E) := by
    have h := coprime_short_fourth_energy (t₀ := 0) (by linarith) hM hMT Q hQ W
      (by intro t ht; simpa only [zero_add] using hBase t ht)
    have hEq : (∑ q ∈ Q, F q) =
        ∑ q ∈ Q, ‖∑ t ∈ W, phase (pairRatio q) t‖ ^ 4 := by
      apply Finset.sum_congr rfl
      intro q hq
      dsimp only [F]
      rw [native_ratio_sum_eq_phase W
        (div_pos (by exact_mod_cast (hQ q hq).1) (by exact_mod_cast (hQ q hq).2.1))]
      simp only [pairRatio, Rat.cast_div, Rat.cast_natCast]
    have hCoef : 28672 * Real.pi ≤ D * T ^ ε := by
      have hd : 28672 * Real.pi ≤ D := by dsimp only [D]; linarith
      exact hd.trans hDpow
    rw [hEq]
    exact h.trans (by
      have hmul := mul_le_mul_of_nonneg_right hCoef (mul_nonneg hTpos.le hE0)
      dsimp only [E] at hmul
      nlinarith)
  by_cases h : M * K₀ ≤ T * E
  · rw [min_eq_left h]
    exact hFirst
  · rw [min_eq_right (le_of_not_ge h)]
    exact hShort

end Montgomery.RationalMoment
