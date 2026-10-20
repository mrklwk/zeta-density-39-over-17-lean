module
public import DensityEnergyGM.CoprimeSamplingSecond
public import DensityEnergyGM.CoprimeFourthNative
public import RationalGcdDecomposition

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Finset GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

/-- The large reduced scales use the true sampled second moment. -/
theorem small_gcd_second_energy :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ N : ℝ, 1 < T → 0 < N →
      ∀ (P : Finset (ℕ × ℕ)),
      (∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
        N < p.1 ∧ (p.1 : ℝ) ≤ 2 * N ∧ N < p.2 ∧ (p.2 : ℝ) ≤ 2 * N ∧
        (pairGcd p : ℝ) < N / Real.sqrt T) →
      ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀ + T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t - u|) →
      (∑ p ∈ P, ‖∑ t ∈ W, phase (pairRatio p) t‖ ^ 2) ≤
        C * (N ^ 2 * (W.card : ℝ) + N * Real.sqrt (T * (discreteAdditiveEnergy W : ℝ))) := by
  let C : ℝ := 2048 * Real.pi
  refine ⟨2 * C, by dsimp only [C]; positivity, ?_⟩
  intro T t₀ N hT hN P hP W hW hSep
  have hTpos : 0 < T := by linarith
  have hRoot : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTpos
  have hC : 0 < C := by dsimp only [C]; positivity
  have hGeom : ∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
      N < p.1 ∧ (p.1 : ℝ) ≤ 2 * N ∧ N < p.2 ∧ (p.2 : ℝ) ≤ 2 * N := by
    intro p hp
    obtain ⟨h1, h2, hl1, hu1, hl2, hu2, hd⟩ := hP p hp
    exact ⟨h1, h2, hl1, hu1, hl2, hu2⟩
  have hd (d : ℕ) (hd : d ∈ gcdValues P) : 0 < d ∧ (d : ℝ) < N / Real.sqrt T := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    exact ⟨Nat.gcd_pos_of_pos_left _ (hP p hp).1, (hP p hp).2.2.2.2.2.2⟩
  have hBlock (d : ℕ) (hd' : d ∈ gcdValues P) :
      (∑ q ∈ reducedFiber P d, ‖∑ t ∈ W, phase (pairRatio q) t‖ ^ 2) ≤
        C * (T + (N / d) ^ 2) * (W.card : ℝ) := by
    have hdPos := (hd d hd').1
    have h := coprime_dyadic_second_energy hT (by positivity : 0 < N / (d : ℝ))
      (reducedFiber P d) (fun q hq => (reduced_fiber_bounds hGeom hq).2) W hW hSep
    have hR0 : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
    dsimp only [C]
    nlinarith [Real.pi_pos, mul_nonneg hR0 hTpos.le]
  have hCount : (gcdValues P).card ≤ ⌊N / Real.sqrt T⌋₊ := by
    apply le_trans (Finset.card_le_card (show gcdValues P ⊆ Icc 1 ⌊N / Real.sqrt T⌋₊ from ?_))
      (by simp)
    intro d hd'
    exact Finset.mem_Icc.mpr ⟨(hd d hd').1, Nat.le_floor (hd d hd').2.le⟩
  have hSum : (∑ d ∈ gcdValues P, (T + (N / d) ^ 2)) ≤ N * Real.sqrt T + 2 * N ^ 2 := by
    have hRec := nat_reciprocal_square_budget (gcdValues P) (fun d hd' => (hd d hd').1.ne')
    have hCountReal : ((gcdValues P).card : ℝ) ≤ N / Real.sqrt T :=
      (by exact_mod_cast hCount : ((gcdValues P).card : ℝ) ≤ ⌊N / Real.sqrt T⌋₊).trans
        (Nat.floor_le (by positivity))
    have hCountHeight : ((gcdValues P).card : ℝ) * T ≤ N * Real.sqrt T := by
      have h := mul_le_mul_of_nonneg_right hCountReal hTpos.le
      have hId : N / Real.sqrt T * T = N * Real.sqrt T := by
        field_simp [hRoot.ne']
        nlinarith [Real.sq_sqrt hTpos.le]
      exact h.trans_eq hId
    have hId : (∑ d ∈ gcdValues P, (T + (N / d) ^ 2)) =
        ((gcdValues P).card : ℝ) * T + N ^ 2 * ∑ d ∈ gcdValues P, ((d : ℝ) ^ 2)⁻¹ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro d hd'
      simp only [div_eq_mul_inv]
      ring
    rw [hId]
    nlinarith [mul_le_mul_of_nonneg_left hRec (sq_nonneg N)]
  have hDiag : (W.card : ℝ) ^ 2 ≤ (discreteAdditiveEnergy W : ℝ) := by
    have h := card_sq_le_approxAddEnergy (by norm_num : (0 : ℝ) ≤ 1) W
    rw [native_approx_energy_eq] at h
    exact_mod_cast h
  have hSqrtE : (W.card : ℝ) ≤ Real.sqrt (discreteAdditiveEnergy W : ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (discreteAdditiveEnergy W) :
      (0 : ℝ) ≤ discreteAdditiveEnergy W), Real.sqrt_nonneg (discreteAdditiveEnergy W : ℝ)]
  have hEnergy : Real.sqrt T * (W.card : ℝ) ≤ Real.sqrt (T * (discreteAdditiveEnergy W : ℝ)) := by
    rw [Real.sqrt_mul hTpos.le]
    exact mul_le_mul_of_nonneg_left hSqrtE hRoot.le
  rw [sum_by_gcd P (fun p hp => (hP p hp).1)
    (fun r : ℚ => ‖∑ t ∈ W, phase (r : ℝ) t‖ ^ 2)]
  calc
    _ ≤ ∑ d ∈ gcdValues P, C * (T + (N / d) ^ 2) * (W.card : ℝ) := Finset.sum_le_sum hBlock
    _ = C * (∑ d ∈ gcdValues P, (T + (N / d) ^ 2)) * (W.card : ℝ) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
    _ ≤ C * (N * Real.sqrt T + 2 * N ^ 2) * (W.card : ℝ) := by gcongr
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hEnergy hN.le
      have hE0 : 0 ≤ N * Real.sqrt (T * (discreteAdditiveEnergy W : ℝ)) := by positivity
      nlinarith

/-- Small reduced scales use the actual fourth-energy bound and finite
Cauchy. Gcd multiplicities have exactly the harmonic cost. -/
theorem large_gcd_second_energy :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ N : ℝ, 1 < T → 0 < N →
      ∀ (P : Finset (ℕ × ℕ)),
      (∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
        N < p.1 ∧ (p.1 : ℝ) ≤ 2 * N ∧ N < p.2 ∧ (p.2 : ℝ) ≤ 2 * N ∧
        N / Real.sqrt T ≤ (pairGcd p : ℝ)) →
      ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀ + T)) →
      (∑ p ∈ P, ‖∑ t ∈ W, phase (pairRatio p) t‖ ^ 2) ≤
        C * N * Real.sqrt (T * (discreteAdditiveEnergy W : ℝ)) *
          (1 + Real.log ⌊2 * N⌋₊) := by
  let C : ℝ := 2 * Real.sqrt (28672 * Real.pi)
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro T t₀ N hT hN P hP W hW
  have hTpos : 0 < T := by linarith
  have hRoot : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTpos
  have hGeom : ∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
      N < p.1 ∧ (p.1 : ℝ) ≤ 2 * N ∧ N < p.2 ∧ (p.2 : ℝ) ≤ 2 * N := by
    intro p hp
    obtain ⟨h1, h2, hl1, hu1, hl2, hu2, hd⟩ := hP p hp
    exact ⟨h1, h2, hl1, hu1, hl2, hu2⟩
  have hBlock : ∀ d ∈ gcdValues P,
      (∑ q ∈ reducedFiber P d, ‖∑ t ∈ W, phase (pairRatio q) t‖ ^ 2) ≤
        (C * Real.sqrt (T * (discreteAdditiveEnergy W : ℝ))) * (N / d) := by
    intro d hd
    obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hd
    have hdPos : 0 < d := he ▸ Nat.gcd_pos_of_pos_left _ (hP p hp).1
    have hdR : (0 : ℝ) < d := by exact_mod_cast hdPos
    have hLower : N / Real.sqrt T ≤ (d : ℝ) := he ▸ (hP p hp).2.2.2.2.2.2
    have hDiv : N / (d : ℝ) ≤ Real.sqrt T := by
      have h := (div_le_iff₀ hRoot).mp hLower
      exact (div_le_iff₀ hdR).mpr (by nlinarith)
    have hRange : (N / (d : ℝ)) ^ 2 ≤ T := by
      nlinarith [Real.sq_sqrt hTpos.le,
        show 0 ≤ N / (d : ℝ) by positivity]
    have h := coprime_short_second_energy hT (by positivity : 0 < N / (d : ℝ)) hRange
      (reducedFiber P d) (fun q hq => (reduced_fiber_bounds hGeom hq).2) W hW
    exact h.trans_eq (by dsimp only [C]; ring)
  have h := pair_energy_le_log P (N := ⌊2 * N⌋₊) (by
    intro p hp
    exact ⟨(hP p hp).1, (Nat.le_floor_iff (by positivity : 0 ≤ 2 * N)).mpr
      (hP p hp).2.2.2.1⟩) W (by dsimp only [C]; positivity) hN.le hBlock
  exact h.trans_eq (by ring)

/-- An all-scale energy-sensitive pair second moment, with the exact
logarithm displayed and no polynomial-height assumption. -/
theorem basic_pair_second_energy :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ N : ℝ, 1 < T → 0 < N →
      ∀ (P : Finset (ℕ × ℕ)),
      (∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
        N < p.1 ∧ (p.1 : ℝ) ≤ 2 * N ∧ N < p.2 ∧ (p.2 : ℝ) ≤ 2 * N) →
      ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀ + T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t - u|) →
      (∑ p ∈ P, ‖∑ t ∈ W, phase (pairRatio p) t‖ ^ 2) ≤
        C * (N ^ 2 * (W.card : ℝ) + N * Real.sqrt (T * (discreteAdditiveEnergy W : ℝ)) *
          (1 + Real.log ⌊2 * N⌋₊)) := by
  obtain ⟨C₁, hC₁, hSmall⟩ := small_gcd_second_energy
  obtain ⟨C₂, hC₂, hLarge⟩ := large_gcd_second_energy
  let C := C₁ + C₂
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro T t₀ N hT hN P hP W hW hSep
  let F : ℕ × ℕ → ℝ := fun p => ‖∑ t ∈ W, phase (pairRatio p) t‖ ^ 2
  let Psmall := P.filter (fun p => (pairGcd p : ℝ) < N / Real.sqrt T)
  let Plarge := P.filter (fun p => N / Real.sqrt T ≤ (pairGcd p : ℝ))
  have hSmallBound := hSmall T t₀ N hT hN Psmall (by
    intro p hp
    obtain ⟨hp, hd⟩ := Finset.mem_filter.mp hp
    obtain ⟨h1, h2, hl1, hu1, hl2, hu2⟩ := hP p hp
    exact ⟨h1, h2, hl1, hu1, hl2, hu2, hd⟩) W hW hSep
  have hLargeBound := hLarge T t₀ N hT hN Plarge (by
    intro p hp
    obtain ⟨hp, hd⟩ := Finset.mem_filter.mp hp
    obtain ⟨h1, h2, hl1, hu1, hl2, hu2⟩ := hP p hp
    exact ⟨h1, h2, hl1, hu1, hl2, hu2, hd⟩) W hW
  have hPartition : (∑ p ∈ P, F p) =
      (∑ p ∈ Psmall, F p) + ∑ p ∈ Plarge, F p := by
    simpa only [Psmall, Plarge, not_lt] using
      (Finset.sum_filter_add_sum_filter_not P (fun p => (pairGcd p : ℝ) < N / Real.sqrt T) F).symm
  have hLog : 0 ≤ Real.log (⌊2 * N⌋₊ : ℝ) := by
    by_cases he : ⌊2 * N⌋₊ = 0
    · simp only [he, Nat.cast_zero, Real.log_zero, le_refl]
    · apply Real.log_nonneg
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr he
  have hY0 : 0 ≤ N * Real.sqrt (T * (discreteAdditiveEnergy W : ℝ)) := by positivity
  have hY : N * Real.sqrt (T * (discreteAdditiveEnergy W : ℝ)) ≤
      N * Real.sqrt (T * (discreteAdditiveEnergy W : ℝ)) * (1 + Real.log ⌊2 * N⌋₊) := by nlinarith
  have hLoss := mul_le_mul_of_nonneg_left hY hC₁.le
  have hOther : 0 ≤ C₂ * (N ^ 2 * (W.card : ℝ)) := by positivity
  change (∑ p ∈ P, F p) ≤ _
  rw [hPartition]
  dsimp only [C]
  nlinarith

/-- Actual arbitrary-coefficient Dirichlet difference moment, with real
dyadic scale and original energy; all sampling and gcd inputs discharged. -/
theorem basic_dirichlet_difference_energy :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ X : ℝ, 1 < T → 0 < X →
      ∀ A : Finset ℕ, (∀ n ∈ A, 0 < n ∧ X < n ∧ (n : ℝ) ≤ 2 * X) →
      ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀ + T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t - u|) →
      ∀ a : ℕ → ℂ, (∀ n ∈ A, ‖a n‖ ≤ 1) →
      (∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ A, a n * phase n (t - u)‖ ^ 2) ≤
        C * (X ^ 2 * (W.card : ℝ) + X * Real.sqrt (T * (discreteAdditiveEnergy W : ℝ)) *
          (1 + Real.log ⌊2 * X⌋₊)) := by
  obtain ⟨C, hC, hPair⟩ := basic_pair_second_energy
  refine ⟨C, hC, ?_⟩
  intro T t₀ X hT hX A hA W hW hSep a ha
  have h := hPair T t₀ X hT hX (A ×ˢ A) (by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨h1, hl1, hu1⟩ := hA p.1 hp1
    obtain ⟨h2, hl2, hu2⟩ := hA p.2 hp2
    exact ⟨h1, h2, hl1, hu1, hl2, hu2⟩) W hW hSep
  simp only [Finset.sum_product, pairRatio, Rat.cast_div, Rat.cast_natCast] at h
  exact (dirichlet_difference_energy_le A (fun n hn => (hA n hn).1) W a ha).trans h

end Montgomery.RationalMoment
