module
public import RationalGeometricShortRange

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment

/-- Fixed dilations of denominator height affect only the constant, even
at the overlap endpoints of two adjacent moments. -/
theorem rational_energy_dilated_overlap {k : ℕ} (hk : 1 ≤ k)
    {η B : ℝ} (hη : 0 < η) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 < D ∧ ∀ (Y : ℝ), 0 < Y → ∀ (H : ℕ), 1 ≤ H →
      (H : ℝ) ≤ B*Y → ∀ (T t₀ : ℝ), 0 ≤ T →
      ∀ (A : Finset ℚ),
      (∀ r ∈ A, 0 < r ∧ r.den ≤ H ∧ |Real.log (r : ℝ)| ≤ 1) →
      ∀ (W : Finset ℝ), (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      Y^k ≤ W.card → T ≤ Y^k*W.card →
      rationalEnergy A W ≤ D*Y^η*Y*(W.card : ℝ)^2 := by
  have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  obtain ⟨C, hC, hdual⟩ := rational_dual_moment hk (show 0 < η*(k : ℝ) by positivity)
  let F := C*(1+B^(2*k))*B^(η*(k : ℝ))
  let D := max 1 F
  have hD : 1 ≤ D := le_max_left _ _
  have hFD : F ≤ D^k := (le_max_right 1 F).trans (by
    simpa only [pow_one] using pow_le_pow_right₀ hD hk)
  refine ⟨D, by linarith, ?_⟩
  intro Y hY H hH hHY T t₀ hT A hA W hW hsep hYR hTR
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hBpos : 0 < B := by linarith
  let R : ℝ := W.card
  have hR : 0 ≤ R := Nat.cast_nonneg _
  have hE : 0 ≤ rationalEnergy A W := sum_nonneg (fun _ _ => sq_nonneg _)
  have htotal : T+(H : ℝ)^(2*k) ≤ (1+B^(2*k))*Y^k*R := by
    have hh := pow_le_pow_left₀ hHpos.le hHY (2*k)
    rw [mul_pow, show Y^(2*k) = Y^k*Y^k by rw [← pow_add]; congr 1; omega] at hh
    have hprod := mul_le_mul_of_nonneg_left hYR (show 0 ≤ B^(2*k)*Y^k by positivity)
    change Y^k ≤ R at hYR
    change T ≤ Y^k*R at hTR
    change B^(2*k)*Y^k*Y^k ≤ B^(2*k)*Y^k*R at hprod
    nlinarith
  have hheight : (H : ℝ)^(η*(k : ℝ)) ≤ B^(η*(k : ℝ))*(Y^η)^k := by
    calc
      _ ≤ (B*Y)^(η*(k : ℝ)) := Real.rpow_le_rpow hHpos.le hHY (by positivity)
      _ = _ := by rw [Real.mul_rpow hBpos.le hY.le, Real.rpow_mul hY.le, Real.rpow_natCast]
  have hRmul : R^(2*k-1)*R = R^(2*k) := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ 2*k)]
  apply (pow_le_pow_iff_left₀ hE (by positivity) (by omega : k ≠ 0)).mp
  calc
    _ ≤ R^(2*k-1)*(C*(T+(H : ℝ)^(2*k))*(H : ℝ)^(η*(k : ℝ))) :=
      hdual H hH T t₀ hT A hA W hW hsep
    _ ≤ R^(2*k-1)*(C*((1+B^(2*k))*Y^k*R)*(B^(η*(k : ℝ))*(Y^η)^k)) := by gcongr
    _ = F*(Y^η)^k*Y^k*R^(2*k) := by
      calc
        _ = F*(Y^η)^k*Y^k*(R^(2*k-1)*R) := by dsimp [F]; ring
        _ = _ := by rw [hRmul]
    _ ≤ D^k*(Y^η)^k*Y^k*R^(2*k) := by gcongr
    _ = _ := by simp only [mul_pow, ← pow_mul]; ring

theorem rational_energy_dilated_cover {K : ℕ} (hK : 1 ≤ K)
    {δ η B : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 < D ∧ ∀ (T t₀ r m : ℝ), 1 ≤ T → r ≤ 1 →
      ((K : ℝ)+1)/(2*K+1) ≤ r → δ ≤ m → m ≤ r/K →
      ∀ (H : ℕ), 1 ≤ H → (H : ℝ) ≤ B*T^m →
      ∀ A : Finset ℚ,
      (∀ q ∈ A, 0 < q ∧ q.den ≤ H ∧ |Real.log (q : ℝ)| ≤ 1) →
      ∀ W : Finset ℝ, (W.card : ℝ) = T^r →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      rationalEnergy A W ≤ D*(T^m)^η*(T^m)*(W.card : ℝ)^2 := by
  choose C hC hbound using (fun n : ℕ => rational_energy_dilated_overlap
    (k := n+1) (by omega) hη hB)
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
  have hTp : 0 < T := by linarith
  have hHk : (T^m)^k = T^((k : ℝ)*m) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hTp.le, mul_comm]
  have hbalance1 : (T^m)^k ≤ W.card := by
    rw [hHk, hRpow]
    exact Real.rpow_le_rpow_of_exponent_le hT hhi
  have hbalance2 : T ≤ (T^m)^k*W.card := by
    rw [hHk, hRpow, ← Real.rpow_add hTp]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT (show 1 ≤ (k : ℝ)*m+r by linarith)
  have hh := hbound (k-1) (T^m) (Real.rpow_pos_of_pos hTp _) H hH hHpow
    T t₀ hTp.le A hA W hW hsep
  rw [hki] at hh
  exact (hh hbalance1 hbalance2).trans (by gcongr)

/-- Uniform real-height short-range theorem, including any fixed dilation
of the denominator bound. The range condition uses the undilated length. -/
theorem rational_energy_dilated_short_range {K : ℕ} (hK : 1 ≤ K)
    {η B : ℝ} (hη : 0 < η) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t₀ M : ℝ), 1 < T → 0 ≤ M →
      ∀ (A : Finset ℚ),
      (∀ q ∈ A, 0 < q ∧ (q.den : ℝ) ≤ B*M ∧ |Real.log (q : ℝ)| ≤ 1) →
      ∀ (W : Finset ℝ), (W.card : ℝ) ≤ T →
      T^(((K : ℝ)+1)/(2*K+1)) ≤ W.card → M^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      rationalEnergy A W ≤ C*T^η*M*(W.card : ℝ)^2 := by
  obtain ⟨D, hD, hcover⟩ := rational_energy_dilated_cover hK
    (show 0 < η/2 by positivity) (show 0 < η/2 by positivity) hB
  refine ⟨3*B^2+D, by positivity, ?_⟩
  intro T t₀ M hT hM A hA W hRT hR hMR hW hsep
  have hTp : 0 < T := by linarith
  have hBp : 0 < B := by linarith
  have hBM : 0 ≤ B*M := mul_nonneg hBp.le hM
  by_cases he : A.Nonempty
  · obtain ⟨q, hq⟩ := he
    have hMpos : 0 < M := by
      have hd : (0 : ℝ) < q.den := by exact_mod_cast q.pos
      nlinarith [(hA q hq).2.1]
    have hH : 1 ≤ ⌊B*M⌋₊ := (show 1 ≤ q.den from q.pos).trans
      ((Nat.le_floor_iff hBM).mpr (hA q hq).2.1)
    have hAf : ∀ q ∈ A, 0 < q ∧ q.den ≤ ⌊B*M⌋₊ ∧ |Real.log (q : ℝ)| ≤ 1 := by
      intro q hq
      exact ⟨(hA q hq).1, (Nat.le_floor_iff hBM).mpr (hA q hq).2.1, (hA q hq).2.2⟩
    have hfH := Nat.floor_le hBM
    have hhalf : T^(η/2) ≤ T^η := Real.rpow_le_rpow_of_exponent_le hT.le (by linarith)
    by_cases hs : M ≤ T^(η/2)
    · have hcard : (A.card : ℝ) ≤ 3*(⌊B*M⌋₊ : ℝ)*(⌊B*M⌋₊ : ℝ) := by
        exact_mod_cast rational_card_le_height A ⌊B*M⌋₊ hAf
      calc
        _ ≤ (A.card : ℝ)*(W.card : ℝ)^2 := rational_energy_trivial A W
        _ ≤ (3*(⌊B*M⌋₊ : ℝ)*(⌊B*M⌋₊ : ℝ))*(W.card : ℝ)^2 := by gcongr
        _ ≤ (3*(B*M)*(B*M))*(W.card : ℝ)^2 := by gcongr
        _ = (3*B^2)*M*M*(W.card : ℝ)^2 := by ring
        _ ≤ (3*B^2)*T^η*M*(W.card : ℝ)^2 := by gcongr; exact hs.trans hhalf
        _ ≤ _ := by gcongr; linarith
    · have hlog : 0 < Real.log T := Real.log_pos hT
      have hRp : (0 : ℝ) < W.card := (Real.rpow_pos_of_pos hTp _).trans_le hR
      have hKp : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
      have hr1 : Real.log W.card / Real.log T ≤ 1 :=
        (div_le_one hlog).mpr (Real.log_le_log hRp hRT)
      have hr : ((K : ℝ)+1)/(2*K+1) ≤ Real.log W.card / Real.log T := by
        apply (le_div_iff₀ hlog).mpr
        simpa only [Real.log_rpow hTp] using
          Real.log_le_log (Real.rpow_pos_of_pos hTp _) hR
      have hm : Real.log M / Real.log T ≤ (Real.log W.card / Real.log T)/K := by
        apply (le_div_iff₀ hKp).mpr
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hlog]
        have hh := Real.log_le_log (pow_pos hMpos K) hMR
        rw [← Real.rpow_natCast, Real.log_rpow hMpos] at hh
        nlinarith
      have hδm : η/2 ≤ Real.log M / Real.log T := by
        apply (le_div_iff₀ hlog).mpr
        simpa only [Real.log_rpow hTp] using
          Real.log_le_log (Real.rpow_pos_of_pos hTp _) (le_of_lt (lt_of_not_ge hs))
      have hpow := rpow_log_quotient hT hMpos
      have hh := hcover T t₀ (Real.log W.card / Real.log T) (Real.log M / Real.log T)
        hT.le hr1 hr hδm hm ⌊B*M⌋₊ hH (by rw [hpow]; exact hfH)
        A hAf W (rpow_log_quotient hT hRp).symm hW hsep
      rw [hpow] at hh
      have hMT : M ≤ T := by
        by_cases hM1 : M ≤ 1
        · exact hM1.trans hT.le
        · have hp : M ≤ M^K := by
            simpa only [pow_one] using pow_le_pow_right₀ (le_of_lt (lt_of_not_ge hM1)) hK
          exact hp.trans (hMR.trans hRT)
      have hp : M^(η/2) ≤ T^η := (Real.rpow_le_rpow hM hMT (by positivity)).trans hhalf
      exact hh.trans (by gcongr; nlinarith [sq_nonneg B])
  · have hAe : A = ∅ := not_nonempty_iff_eq_empty.mp he
    rw [hAe, rationalEnergy, sum_empty]
    positivity

end Montgomery.RationalMoment
