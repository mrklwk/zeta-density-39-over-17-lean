module
public import DensityEnergyGM.SharpCoprimeCubic
public import RationalLargeGcdEnergy

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Finset GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

theorem pair_cubic_le_log (P : Finset (ℕ × ℕ)) {N : ℕ}
    (hP : ∀ p ∈ P, 0 < p.1 ∧ p.1 ≤ N) (W : Finset ℝ)
    {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hblock : ∀ d ∈ gcdValues P,
      (∑ q ∈ reducedFiber P d, ‖∑ t ∈ W, phase (pairRatio q) t‖ ^ 3) ≤ B * (M / d)) :
    (∑ p ∈ P, ‖∑ t ∈ W, phase (pairRatio p) t‖ ^ 3) ≤
      B * M * (1 + Real.log N) := by
  have hSub : gcdValues P ⊆ Finset.Icc 1 N := by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    exact Finset.mem_Icc.mpr ⟨Nat.gcd_pos_of_pos_left _ (hP p hp).1,
      (Nat.gcd_le_left _ (hP p hp).1).trans (hP p hp).2⟩
  have hReciprocal : (∑ d ∈ gcdValues P, (d : ℝ)⁻¹) ≤ 1 + Real.log N := by
    calc
      _ ≤ ∑ d ∈ Finset.Icc 1 N, (d : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hSub (fun d hd hnot => by positivity)
      _ ≤ _ := by
        simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
          using harmonic_le_one_add_log N
  rw [sum_by_gcd P (fun p hp => (hP p hp).1)
    (fun r : ℚ => ‖∑ t ∈ W, phase (r : ℝ) t‖ ^ 3)]
  calc
    _ ≤ ∑ d ∈ gcdValues P, B * (M / d) := Finset.sum_le_sum hblock
    _ = B * M * ∑ d ∈ gcdValues P, (d : ℝ)⁻¹ := by
      simp only [div_eq_mul_inv, ← Finset.mul_sum, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left hReciprocal (mul_nonneg hB hM)

/-- The actual large-gcd cubic contribution with the optimized sharp
profile. The harmonic loss is absorbed before N,P,W vary. -/
theorem large_gcd_cubic_sharp_native (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T N : ℝ) (P : Finset (ℕ × ℕ)) (W : Finset ℝ),
        T₀ ≤ T → 0 < N → T ≤ N ^ 2 → N ≤ T →
        (∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
          N < p.1 ∧ (p.1 : ℝ) ≤ 2 * N ∧ N < p.2 ∧ (p.2 : ℝ) ≤ 2 * N ∧
          N ^ 2 / T ≤ (pairGcd p : ℝ)) →
        IsSeparated 1 W → InBaseInterval T W →
        (∑ p ∈ P, ‖∑ t ∈ W, phase (pairRatio p) t‖ ^ 3) ≤
          C * T ^ ε * N * sharpCubicProfile T W := by
  obtain ⟨C, T₀, hC, hT₀, hCubic⟩ :=
    real_scale_coprime_cubic_sharp_native (ε / 2) (by positivity)
  let L : ℝ := 1 + (4 : ℝ) ^ (ε / 2) / (ε / 2)
  have hL : 0 < L := by dsimp only [L]; positivity
  refine ⟨C * L, T₀, by positivity, hT₀, ?_⟩
  intro T N P W hT hN hTN hNT hP hSep hBase
  have hTtwo : 2 ≤ T := hT₀.trans hT
  have hTpos : 0 < T := by linarith
  have hGeom : ∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
      N < p.1 ∧ (p.1 : ℝ) ≤ 2 * N ∧ N < p.2 ∧ (p.2 : ℝ) ≤ 2 * N := by
    intro p hp
    obtain ⟨h1, h2, hl1, hu1, hl2, hu2, hd⟩ := hP p hp
    exact ⟨h1, h2, hl1, hu1, hl2, hu2⟩
  have hBlock : ∀ d ∈ gcdValues P,
      (∑ q ∈ reducedFiber P d, ‖∑ t ∈ W, phase (pairRatio q) t‖ ^ 3) ≤
        (C * T ^ (ε / 2) * sharpCubicProfile T W) * (N / d) := by
    intro d hd
    obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hd
    have hdPos : 0 < d := he ▸ Nat.gcd_pos_of_pos_left _ (hP p hp).1
    have hdR : (0 : ℝ) < d := by exact_mod_cast hdPos
    have hdLower : N ^ 2 / T ≤ (d : ℝ) := he ▸ (hP p hp).2.2.2.2.2.2
    have hDiv : N / (d : ℝ) ≤ T / N := by
      have hh := div_le_div_of_nonneg_left hN.le (show 0 < N ^ 2 / T by positivity) hdLower
      have hid : N / (N ^ 2 / T) = T / N := by field_simp
      exact hh.trans_eq hid
    have hRange : (N / (d : ℝ)) ^ 2 ≤ T := by
      have hSqrt : T / N ≤ Real.sqrt T := by
        have hNsqrt : Real.sqrt T ≤ N := by
          nlinarith [Real.sq_sqrt hTpos.le, Real.sqrt_nonneg T]
        apply (div_le_iff₀ hN).mpr
        nlinarith [Real.sq_sqrt hTpos.le, Real.sqrt_nonneg T]
      have hBound := hDiv.trans hSqrt
      nlinarith [Real.sq_sqrt hTpos.le, Real.sqrt_nonneg T,
        show 0 ≤ N / (d : ℝ) by positivity]
    have hQ : ∀ q ∈ reducedFiber P d,
        0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2 ∧
          N / d < q.1 ∧ (q.1 : ℝ) ≤ 2 * (N / d) ∧
          N / d < q.2 ∧ (q.2 : ℝ) ≤ 2 * (N / d) :=
      fun q hq => (reduced_fiber_bounds hGeom hq).2
    have h := hCubic (N / d) T (reducedFiber P d) W (by positivity)
      hT hRange hQ hSep hBase
    have hEq : (∑ q ∈ reducedFiber P d, ‖∑ t ∈ W, phase (pairRatio q) t‖ ^ 3) =
        ∑ q ∈ reducedFiber P d, ‖gmR W ((q.1 : ℝ) / q.2)‖ ^ 3 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [native_ratio_sum_eq_phase W
        (div_pos (by exact_mod_cast (hQ q hq).1) (by exact_mod_cast (hQ q hq).2.1))]
      simp only [pairRatio, Rat.cast_div, Rat.cast_natCast]
    rw [hEq]
    exact h.trans_eq (by ring)
  have hBound := pair_cubic_le_log P (N := ⌊2 * N⌋₊) (by
    intro p hp
    exact ⟨(hP p hp).1, (Nat.le_floor_iff (by positivity : 0 ≤ 2 * N)).mpr
      (hP p hp).2.2.2.1⟩) W
      (by
        exact mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hTpos.le _))
          (sharpCubicProfile_nonneg hTpos.le W)) hN.le hBlock
  have hFloor : (⌊2 * N⌋₊ : ℝ) ≤ 4 * T :=
    (Nat.floor_le (by positivity : 0 ≤ 2 * N)).trans (by linarith)
  have hLog := logarithmic_height_loss (by linarith : 1 ≤ T)
    (show 0 < ε / 2 by positivity) ⌊2 * N⌋₊ hFloor
  change 1 + Real.log ⌊2 * N⌋₊ ≤ L * T ^ (ε / 2) at hLog
  have hPower : T ^ (ε / 2) * T ^ (ε / 2) = T ^ ε := by
    rw [← Real.rpow_add hTpos]
    congr 1
    ring
  calc
    _ ≤ (C * T ^ (ε / 2) * sharpCubicProfile T W) * N *
        (1 + Real.log ⌊2 * N⌋₊) := hBound
    _ ≤ (C * T ^ (ε / 2) * sharpCubicProfile T W) * N * (L * T ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_left hLog (by
        exact mul_nonneg (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hTpos.le _))
          (sharpCubicProfile_nonneg hTpos.le W)) hN.le)
    _ = (C * L) * (T ^ (ε / 2) * T ^ (ε / 2)) * N * sharpCubicProfile T W := by ring
    _ = _ := by rw [hPower]

end Montgomery.RationalMoment
