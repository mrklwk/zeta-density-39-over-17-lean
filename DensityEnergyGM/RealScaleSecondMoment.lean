module
public import DensityEnergyGM.FiniteRatioSecond
public import DensityEnergyGM.DifferenceEnergyGeometry
public import GuthMaynard.Improvement.SourceRatioAssembly

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Finset GuthMaynard.NativeMoment GuthMaynard.Improvement
namespace Montgomery.RationalMoment

theorem real_dyadic_indices_subset_floor_insert {M : ℝ} (hM : 0 ≤ M) :
    sourceRatioIndices M ⊆ insert (2 * ⌊M⌋₊ + 1) (dyadicInterval ⌊M⌋₊) := by
  intro n hn
  obtain ⟨hl, hu⟩ := (sourceRatioIndices_mem hM n).mp hn
  have hfloor := Nat.floor_le hM
  have hupper := Nat.lt_floor_add_one M
  have hnlo : ⌊M⌋₊ < n := by exact_mod_cast hfloor.trans_lt hl
  have hnhiR : (n : ℝ) < 2 * (⌊M⌋₊ : ℝ) + 2 := by linarith
  have hnhi : n < 2 * ⌊M⌋₊ + 2 := by exact_mod_cast hnhiR
  by_cases he : n = 2 * ⌊M⌋₊ + 1
  · exact Finset.mem_insert.mpr (Or.inl he)
  · apply Finset.mem_insert.mpr
    right
    exact Finset.mem_Ioc.mpr ⟨hnlo, by omega⟩

theorem finiteRatioSecond_dyadic (M : ℕ) (W : Finset ℝ) :
    finiteRatioSecond (dyadicInterval M) W = gmDiscreteRatioMoment 2 M W :=
  (gmDiscreteRatioMoment_eq_iterated 2 M W).symm

theorem finiteRatioSecond_singleton_one (W : Finset ℝ) :
    finiteRatioSecond {1} W = (W.card : ℝ) ^ 2 := by
  simp [finiteRatioSecond, gmR_one]

/-- The sharp ratio second moment at the exact positive real scale.
The possible endpoint beyond twice the floor is retained and bounded. -/
theorem real_scale_ratio_second_sharp_native (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (M T : ℝ) (W : Finset ℝ),
        0 < M → T₀ ≤ T → M ^ 2 ≤ T →
        IsSeparated 1 W → InBaseInterval T W →
        finiteRatioSecond (sourceRatioIndices M) W ≤ C * T ^ ε *
          (M ^ 2 * (discreteAdditiveEnergy W : ℝ) ^ (1 / 2 : ℝ) +
            (W.card : ℝ) * (discreteAdditiveEnergy W : ℝ) ^ (1 / 4 : ℝ) *
              (M ^ (9 / 5 : ℝ) + T ^ (1 / 4 : ℝ) * M ^ (6 / 5 : ℝ))) := by
  obtain ⟨C, T₀, hC, hT₀, hNative⟩ := ratio_second_moment_sharp_native ε hε
  refine ⟨2 * C + 16, T₀, by positivity, hT₀, ?_⟩
  intro M T W hM hT hMT hSep hBase
  have hTtwo : 2 ≤ T := hT₀.trans hT
  have hTpos : 0 < T := by linarith
  have hPow : 1 ≤ T ^ ε := Real.one_le_rpow (by linarith) hε.le
  let E : ℝ := discreteAdditiveEnergy W
  let R : ℝ := W.card
  let L : ℝ := R * E ^ (1 / 4 : ℝ) * T ^ (1 / 4 : ℝ)
  let S : ℝ → ℝ := fun x => x ^ 2 * E ^ (1 / 2 : ℝ) +
    R * E ^ (1 / 4 : ℝ) * (x ^ (9 / 5 : ℝ) + T ^ (1 / 4 : ℝ) * x ^ (6 / 5 : ℝ))
  change finiteRatioSecond (sourceRatioIndices M) W ≤ (2 * C + 16) * T ^ ε * S M
  have hL0 : 0 ≤ L := by dsimp only [L, R, E]; positivity
  have hS0 : 0 ≤ S M := by dsimp only [S, R, E]; positivity
  have hEndpoint : R ^ 2 ≤ 4 * L := by
    have h := card_sq_le_four_quarter_height_energy hTtwo hBase
    dsimp only [R, L, E]
    nlinarith
  have hLast : L * M ^ (6 / 5 : ℝ) ≤ S M := by
    have hFirst : 0 ≤ M ^ 2 * E ^ (1 / 2 : ℝ) := by positivity
    have hOther : 0 ≤ R * E ^ (1 / 4 : ℝ) * M ^ (9 / 5 : ℝ) := by
      dsimp only [R, E]; positivity
    dsimp only [L, S]
    nlinarith
  have hSgrow : S M ≤ T ^ ε * S M := by nlinarith
  by_cases hMone : 1 ≤ M
  · let N : ℕ := ⌊M⌋₊
    have hN : 0 < N := (Nat.one_le_floor_iff M).mpr hMone
    have hNM : (N : ℝ) ≤ M := Nat.floor_le hM.le
    have hNT : (N : ℝ) ^ 2 ≤ T :=
      (pow_le_pow_left₀ (Nat.cast_nonneg N) hNM 2).trans hMT
    have hEndNot : 2 * N + 1 ∉ dyadicInterval N := by
      intro h
      have hhi := (Finset.mem_Ioc.mp h).2
      omega
    have hBound := finiteRatioSecond_insert_le hEndNot (by omega : 0 < 2 * N + 1)
      (by intro n hn; exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1) W
    rw [finiteRatioSecond_dyadic] at hBound
    have hFull := finiteRatioSecond_mono (real_dyadic_indices_subset_floor_insert hM.le) W
    have hNative' : gmDiscreteRatioMoment 2 N W ≤ C * T ^ ε * S (N : ℝ) :=
      hNative N T W hN hT hNT hSep hBase
    have hMono : S (N : ℝ) ≤ S M := by
      dsimp only [S]
      gcongr
    have hScale : 1 ≤ M ^ (6 / 5 : ℝ) := Real.one_le_rpow hMone (by norm_num)
    have hLle : L ≤ S M := by nlinarith
    have hEnd : R ^ 2 ≤ 4 * S M := by linarith
    calc
      _ ≤ 2 * gmDiscreteRatioMoment 2 N W + 2 * R ^ 2 := hFull.trans hBound
      _ ≤ 2 * (C * T ^ ε * S M) + 8 * S M := by
        have h := hNative'.trans (mul_le_mul_of_nonneg_left hMono (by positivity))
        linarith
      _ ≤ _ := by nlinarith
  · have hMsmall : M < 1 := lt_of_not_ge hMone
    by_cases hA : (sourceRatioIndices M).Nonempty
    · obtain ⟨n, hn⟩ := hA
      obtain ⟨hnlo, hnhi⟩ := (sourceRatioIndices_mem hM.le n).mp hn
      have hnpos : 0 < n := by exact_mod_cast hM.trans hnlo
      have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
      have hMhalf : (1 / 2 : ℝ) ≤ M := by linarith
      have hSub : sourceRatioIndices M ⊆ {1} := by
        intro m hm
        obtain ⟨hl, hu⟩ := (sourceRatioIndices_mem hM.le m).mp hm
        have hmpos : 0 < m := by exact_mod_cast hM.trans hl
        have hmlt : m < 2 := by exact_mod_cast (show (m : ℝ) < 2 by linarith)
        exact Finset.mem_singleton.mpr (by omega)
      have hScale : (1 / 4 : ℝ) ≤ M ^ (6 / 5 : ℝ) := by
        have hsq : (1 / 4 : ℝ) ≤ M ^ 2 := by nlinarith
        have hp : M ^ (2 : ℝ) ≤ M ^ (6 / 5 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hM hMsmall.le (by norm_num)
        norm_num at hp
        exact hsq.trans hp
      have hLle : L ≤ 4 * S M := by nlinarith
      calc
        _ ≤ finiteRatioSecond {1} W := finiteRatioSecond_mono hSub W
        _ = R ^ 2 := finiteRatioSecond_singleton_one W
        _ ≤ 16 * S M := by linarith
        _ ≤ 16 * T ^ ε * S M := by nlinarith
        _ ≤ _ := by gcongr; linarith
    · rw [Finset.not_nonempty_iff_eq_empty.mp hA]
      simp only [finiteRatioSecond, Finset.sum_empty]
      positivity

end Montgomery.RationalMoment
