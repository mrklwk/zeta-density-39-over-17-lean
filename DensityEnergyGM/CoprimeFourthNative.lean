module
public import DensityEnergyGM.LargeValuesEnergy
public import DensityEnergyGM.CoprimeFourthEnergy

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
open Finset
open GuthMaynard.NativeMoment

namespace Montgomery.RationalMoment

theorem native_approx_energy_eq (W : Finset ℝ) :
    ApproxAddEnergy 1 W = discreteAdditiveEnergy W := rfl

/-- Exact positive-frequency identification, before taking norms. -/
theorem native_ratio_sum_eq_phase (W : Finset ℝ) {r : ℝ} (hr : 0 < r) :
    gmR W r = ∑ t ∈ W, phase r t := by
  unfold gmR phase
  apply Finset.sum_congr rfl
  intro t ht
  rw [abs_of_pos hr, Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr hr.ne')]
  rw [← Complex.ofReal_log hr.le]
  congr 1
  push_cast
  ring

def nativeCoprimePairs (M : ℕ) : Finset (ℕ × ℕ) :=
  (dyadicInterval M ×ˢ dyadicInterval M).filter fun p => Nat.Coprime p.1 p.2

def nativeCoprimeFourth (M : ℕ) (W : Finset ℝ) : ℝ :=
  ∑ p ∈ nativeCoprimePairs M, ‖gmR W ((p.1 : ℝ) / p.2)‖ ^ 4

theorem nativeCoprimeFourth_le_full (M : ℕ) (W : Finset ℝ) :
    nativeCoprimeFourth M W ≤ gmDiscreteRatioMoment 4 M W := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset _ _
  · intro p hp hnot
    exact pow_nonneg (norm_nonneg _) _

theorem nativeCoprimeFourth_le_short_energy
    {T : ℝ} {M : ℕ} (hT : 1 < T) (hM : 0 < M) (hMT : (M : ℝ) ^ 2 ≤ T)
    (W : Finset ℝ) (hW : InBaseInterval T W) :
    nativeCoprimeFourth M W ≤
      (28672 * Real.pi) * T * (discreteAdditiveEnergy W : ℝ) := by
  have hgeom : ∀ p ∈ nativeCoprimePairs M,
      0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 ∧
        (M : ℝ) < p.1 ∧ (p.1 : ℝ) ≤ 2 * M ∧
          (M : ℝ) < p.2 ∧ (p.2 : ℝ) ≤ 2 * M := by
    intro p hp
    obtain ⟨hp, hcop⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    change p.1 ∈ Ioc M (2 * M) at hp1
    change p.2 ∈ Ioc M (2 * M) at hp2
    obtain ⟨hl1, hu1⟩ := Finset.mem_Ioc.mp hp1
    obtain ⟨hl2, hu2⟩ := Finset.mem_Ioc.mp hp2
    refine ⟨hM.trans hl1, hM.trans hl2, hcop, ?_, ?_, ?_, ?_⟩
    · exact_mod_cast hl1
    · exact_mod_cast hu1
    · exact_mod_cast hl2
    · exact_mod_cast hu2
  have hbound := coprime_short_fourth_energy (t₀ := 0) hT (by exact_mod_cast hM)
    hMT (nativeCoprimePairs M) hgeom W (by
      intro t ht
      simpa only [zero_add] using hW t ht)
  have heq : nativeCoprimeFourth M W =
      ∑ p ∈ nativeCoprimePairs M, ‖∑ t ∈ W, phase (pairRatio p) t‖ ^ 4 := by
    apply Finset.sum_congr rfl
    intro p hp
    have hpgeom := hgeom p hp
    rw [native_ratio_sum_eq_phase W
      (div_pos (by exact_mod_cast hpgeom.1) (by exact_mod_cast hpgeom.2.1))]
    simp only [pairRatio, Rat.cast_div, Rat.cast_natCast]
  rw [heq]
  exact hbound

/-- The complete reduced fourth-moment minimum needed by the stronger
energy argument. Both alternatives concern the same actual exponential sum
and the same literal ordered quadruple count. -/
theorem nativeCoprimeFourth_min (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (M : ℕ) (T : ℝ) (W : Finset ℝ),
        0 < M → T₀ ≤ T → (M : ℝ) ^ 2 ≤ T →
        IsSeparated 1 W → InBaseInterval T W →
        nativeCoprimeFourth M W ≤ C * T ^ ε *
          min ((M : ℝ) * ((W.card : ℝ) ^ 4 +
            T ^ (1 / 2 : ℝ) * (W.card : ℝ) *
              (discreteAdditiveEnergy W : ℝ) ^ (3 / 4 : ℝ)))
            (T * (discreteAdditiveEnergy W : ℝ)) := by
  obtain ⟨C₀, T₁, hC₀, hT₁, hFull⟩ := gmDiscreteFourthMoment_native ε hε
  let C : ℝ := 2 * C₀ + 28672 * Real.pi
  refine ⟨C, max T₁ 2, by dsimp only [C]; positivity,
    hT₁.trans (le_max_left _ _), ?_⟩
  intro M T W hM hT hMT hSep hBase
  have hTtwo : 2 ≤ T := (le_max_right _ _).trans hT
  have hTone : 1 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMzero : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hMleT : (M : ℝ) ≤ T := by nlinarith
  have hMroot : (M : ℝ) ≤ Real.sqrt T := by
    nlinarith [Real.sq_sqrt hTpos.le, Real.sqrt_nonneg T]
  have hCbig : 28672 * Real.pi ≤ C := by dsimp only [C]; linarith
  have hCfull : 2 * C₀ ≤ C := by dsimp only [C]; linarith [Real.pi_pos]
  have hTpow : 1 ≤ T ^ ε := Real.one_le_rpow hTone hε.le
  have hEzero : 0 ≤ (discreteAdditiveEnergy W : ℝ) := Nat.cast_nonneg _
  have hShort : nativeCoprimeFourth M W ≤ C * T ^ ε *
      (T * (discreteAdditiveEnergy W : ℝ)) := by
    have h := nativeCoprimeFourth_le_short_energy (by linarith) hM hMT W hBase
    have hc0 : 0 ≤ C := by dsimp only [C]; positivity
    have hcoeff : 28672 * Real.pi ≤ C * T ^ ε := by
      nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hTpow)]
    calc
      _ ≤ (28672 * Real.pi) * T * (discreteAdditiveEnergy W : ℝ) := h
      _ = (28672 * Real.pi) * (T * (discreteAdditiveEnergy W : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hTpos.le hEzero)
  have hFirst : nativeCoprimeFourth M W ≤ C * T ^ ε *
      ((M : ℝ) * ((W.card : ℝ) ^ 4 +
        T ^ (1 / 2 : ℝ) * (W.card : ℝ) *
          (discreteAdditiveEnergy W : ℝ) ^ (3 / 4 : ℝ))) := by
    by_cases hEmpty : W = ∅
    · subst W
      simp [nativeCoprimeFourth, gmR]
    have hRpos : (0 : ℝ) < W.card := by
      exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hEmpty)
    let E : ℝ := discreteAdditiveEnergy W
    have hEpos : 0 < E := by
      have hdiag := card_sq_le_approxAddEnergy (by norm_num : (0 : ℝ) ≤ 1) W
      rw [native_approx_energy_eq] at hdiag
      have hdiagReal : (W.card : ℝ) ^ 2 ≤ E := by
        dsimp only [E]
        exact_mod_cast hdiag
      exact lt_of_lt_of_le (by positivity) hdiagReal
    have hEupper : E ≤ (W.card : ℝ) ^ 4 := by
      have h := approxAddEnergy_le_card_pow_four 1 W
      rw [native_approx_energy_eq] at h
      dsimp only [E]
      exact_mod_cast h
    have hQuarter : E ^ (1 / 4 : ℝ) ≤ (W.card : ℝ) := by
      calc
        E ^ (1 / 4 : ℝ) ≤ ((W.card : ℝ) ^ 4) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow hEpos.le hEupper (by norm_num)
        _ = (W.card : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hRpos.le]
          norm_num
    have hEprod : E = E ^ (3 / 4 : ℝ) * E ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add hEpos]
      norm_num
    have hMiddle : E * (M : ℝ) ^ 2 ≤
        E ^ (3 / 4 : ℝ) * (W.card : ℝ) * T ^ (1 / 2 : ℝ) * M := by
      rw [← Real.sqrt_eq_rpow]
      calc
        E * (M : ℝ) ^ 2 =
            E ^ (3 / 4 : ℝ) * E ^ (1 / 4 : ℝ) * (M : ℝ) * M := by
          rw [← hEprod]
          ring
        _ ≤ E ^ (3 / 4 : ℝ) * (W.card : ℝ) * Real.sqrt T * M := by
          have hpE : 0 ≤ E ^ (3 / 4 : ℝ) := Real.rpow_nonneg hEpos.le _
          have hq := mul_le_mul_of_nonneg_left hQuarter hpE
          have hq' := mul_le_mul_of_nonneg_right hq (mul_nonneg hMzero hMzero)
          have hm := mul_le_mul_of_nonneg_left hMroot
            (mul_nonneg hpE (Nat.cast_nonneg W.card))
          have hm' := mul_le_mul_of_nonneg_right hm hMzero
          nlinarith
    have hFull := hFull M T W hM ((le_max_left _ _).trans hT) hMleT hSep hBase
    rw [native_approx_energy_eq] at hFull
    have hshape : (W.card : ℝ) ^ 4 * M + E * (M : ℝ) ^ 2 +
        E ^ (3 / 4 : ℝ) * (W.card : ℝ) * T ^ (1 / 2 : ℝ) * M ≤
        2 * ((M : ℝ) * ((W.card : ℝ) ^ 4 +
          T ^ (1 / 2 : ℝ) * (W.card : ℝ) * E ^ (3 / 4 : ℝ))) := by
      nlinarith [mul_nonneg hMzero (pow_nonneg hRpos.le 4)]
    calc
      nativeCoprimeFourth M W ≤ gmDiscreteRatioMoment 4 M W := nativeCoprimeFourth_le_full _ _
      _ ≤ C₀ * T ^ ε * ((W.card : ℝ) ^ 4 * M + E * (M : ℝ) ^ 2 +
          E ^ (3 / 4 : ℝ) * (W.card : ℝ) * T ^ (1 / 2 : ℝ) * M) := hFull
      _ ≤ C₀ * T ^ ε * (2 * ((M : ℝ) * ((W.card : ℝ) ^ 4 +
          T ^ (1 / 2 : ℝ) * (W.card : ℝ) * E ^ (3 / 4 : ℝ)))) := by gcongr
      _ ≤ _ := by
        have hcoef := mul_le_mul_of_nonneg_right hCfull (Real.rpow_nonneg hTpos.le ε)
        have hS0 : 0 ≤ (M : ℝ) * ((W.card : ℝ) ^ 4 +
            T ^ (1 / 2 : ℝ) * (W.card : ℝ) * E ^ (3 / 4 : ℝ)) :=
          mul_nonneg hMzero (add_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
            (mul_nonneg (mul_nonneg (Real.rpow_nonneg hTpos.le _)
              (Nat.cast_nonneg _)) (Real.rpow_nonneg hEpos.le _)))
        have hprod := mul_le_mul_of_nonneg_right hcoef hS0
        change C₀ * T ^ ε * (2 * ((M : ℝ) * ((W.card : ℝ) ^ 4 +
            T ^ (1 / 2 : ℝ) * (W.card : ℝ) * E ^ (3 / 4 : ℝ)))) ≤
          C * T ^ ε * ((M : ℝ) * ((W.card : ℝ) ^ 4 +
            T ^ (1 / 2 : ℝ) * (W.card : ℝ) * E ^ (3 / 4 : ℝ)))
        nlinarith
  by_cases h : (M : ℝ) * ((W.card : ℝ) ^ 4 + T ^ (1 / 2 : ℝ) *
      (W.card : ℝ) * (discreteAdditiveEnergy W : ℝ) ^ (3 / 4 : ℝ)) ≤
        T * (discreteAdditiveEnergy W : ℝ)
  · rw [min_eq_left h]
    exact hFirst
  · rw [min_eq_right (le_of_not_ge h)]
    exact hShort

end Montgomery.RationalMoment
