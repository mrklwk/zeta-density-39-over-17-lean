module
public import RationalUniformShortRange

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment

theorem rpow_log_quotient {T x : ℝ} (hT : 1 < T) (hx : 0 < x) :
    T ^ (Real.log x / Real.log T) = x := by
  rw [Real.rpow_def_of_pos (by linarith : 0 < T)]
  rw [mul_div_cancel₀ _ (Real.log_pos hT).ne', Real.exp_log hx]

/-- The short-range estimate in terms of the actual cardinality and integer
height, with no power parametrizations in its assumptions. -/
theorem rational_energy_cardinal_height {K : ℕ} (hK : 1 ≤ K)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t₀ : ℝ), 1 < T →
      ∀ (H : ℕ), 1 ≤ H → ∀ (A : Finset ℚ),
      (∀ q ∈ A, 0 < q ∧ q.den ≤ H ∧ |Real.log (q : ℝ)| ≤ 1) →
      ∀ (W : Finset ℝ), (W.card : ℝ) ≤ T →
      T^(((K : ℝ)+1)/(2*K+1)) ≤ W.card →
      (H : ℝ)^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      rationalEnergy A W ≤ C*T^η*(H : ℝ)*(W.card : ℝ)^2 := by
  obtain ⟨C, hC, hbound⟩ := rational_energy_short_range hK hη
  refine ⟨C, hC, ?_⟩
  intro T t₀ hT H hH A hA W hRT hR hHR hW hsep
  have hTp : 0 < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos hT
  have hHp : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hRp : (0 : ℝ) < W.card := (Real.rpow_pos_of_pos hTp _).trans_le hR
  have hKp : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  apply hbound T t₀ (Real.log W.card / Real.log T)
    (Real.log H / Real.log T) hT.le
  · exact (div_le_one hlog).mpr (Real.log_le_log hRp hRT)
  · apply (le_div_iff₀ hlog).mpr
    simpa only [Real.log_rpow hTp] using Real.log_le_log (Real.rpow_pos_of_pos hTp _) hR
  · apply (le_div_iff₀ hKp).mpr
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hlog]
    have hh := Real.log_le_log (pow_pos hHp K) hHR
    rw [← Real.rpow_natCast, Real.log_rpow hHp] at hh
    nlinarith
  · exact hH
  · exact (rpow_log_quotient hT hHp).symm
  · exact hA
  · exact (rpow_log_quotient hT hRp).symm
  · exact hW
  · exact hsep

/-- Arbitrary real heights are rounded down, so the height condition and the
linear bound incur no rounding factor. Empty rational sets are included. -/
theorem rational_energy_real_height {K : ℕ} (hK : 1 ≤ K)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t₀ H : ℝ), 1 < T → 0 ≤ H →
      ∀ (A : Finset ℚ),
      (∀ q ∈ A, 0 < q ∧ (q.den : ℝ) ≤ H ∧ |Real.log (q : ℝ)| ≤ 1) →
      ∀ (W : Finset ℝ), (W.card : ℝ) ≤ T →
      T^(((K : ℝ)+1)/(2*K+1)) ≤ W.card → H^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      rationalEnergy A W ≤ C*T^η*H*(W.card : ℝ)^2 := by
  obtain ⟨C, hC, hbound⟩ := rational_energy_cardinal_height hK hη
  refine ⟨C, hC, ?_⟩
  intro T t₀ H hT hH A hA W hRT hR hHR hW hsep
  by_cases he : A.Nonempty
  · obtain ⟨q, hq⟩ := he
    have hfloor : 1 ≤ ⌊H⌋₊ := (show 1 ≤ q.den from q.pos).trans
      ((Nat.le_floor_iff hH).mpr (hA q hq).2.1)
    have hAf : ∀ q ∈ A, 0 < q ∧ q.den ≤ ⌊H⌋₊ ∧ |Real.log (q : ℝ)| ≤ 1 := by
      intro q hq
      exact ⟨(hA q hq).1, (Nat.le_floor_iff hH).mpr (hA q hq).2.1, (hA q hq).2.2⟩
    have hfH := Nat.floor_le hH
    have hb := hbound T t₀ hT ⌊H⌋₊ hfloor A hAf W hRT hR
      ((pow_le_pow_left₀ (Nat.cast_nonneg _) hfH K).trans hHR) hW hsep
    exact hb.trans (by gcongr)
  · have hAe : A = ∅ := not_nonempty_iff_eq_empty.mp he
    rw [hAe, rationalEnergy, sum_empty]
    positivity

theorem coprime_pair_den {q : ℕ × ℕ} (hq : 0 < q.2)
    (hc : Nat.Coprime q.1 q.2) : (pairRatio q).den = q.2 := by
  have hh := Rat.den_div_eq_of_coprime (a := (q.1 : ℤ)) (b := (q.2 : ℤ))
    (by exact_mod_cast hq) (by simpa using hc)
  have he : ((pairRatio q).den : ℤ) = q.2 := by simpa only [pairRatio, Int.cast_natCast] using hh
  exact_mod_cast he

theorem dyadic_pair_log {M : ℝ} {q : ℕ × ℕ}
    (hq1 : 0 < q.1) (hq2 : 0 < q.2)
    (hlo1 : M < q.1) (hhi1 : (q.1 : ℝ) ≤ 2*M)
    (hlo2 : M < q.2) (hhi2 : (q.2 : ℝ) ≤ 2*M) :
    |Real.log (pairRatio q : ℝ)| ≤ 1 := by
  have h1 : (0 : ℝ) < q.1 := by exact_mod_cast hq1
  have h2 : (0 : ℝ) < q.2 := by exact_mod_cast hq2
  have h12 : (q.1 : ℝ)/q.2 ≤ 2 := (div_le_iff₀ h2).mpr (by linarith)
  have h21 : (q.2 : ℝ)/q.1 ≤ 2 := (div_le_iff₀ h1).mpr (by linarith)
  have hl2 : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num) using 1
    norm_num
  simp only [pairRatio, Rat.cast_div, Rat.cast_natCast]
  apply abs_le.mpr
  refine ⟨?_, (Real.log_le_log (div_pos h1 h2) h12).trans hl2⟩
  have hh := (Real.log_le_log (div_pos h2 h1) h21).trans hl2
  rw [Real.log_div h2.ne' h1.ne'] at hh
  rw [Real.log_div h1.ne' h2.ne']
  linarith

/-- The actual coprime pairs in an arbitrary real dyadic interval satisfy
the new short-range bound. The constant is uniform in the interval length. -/
theorem coprime_dyadic_energy {K : ℕ} (hK : 1 ≤ K)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t₀ M : ℝ), 1 < T → 0 ≤ M →
      ∀ (Q : Finset (ℕ × ℕ)),
      (∀ q ∈ Q, 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2 ∧
        M < q.1 ∧ (q.1 : ℝ) ≤ 2*M ∧ M < q.2 ∧ (q.2 : ℝ) ≤ 2*M) →
      ∀ (W : Finset ℝ), (W.card : ℝ) ≤ T →
      T^(((K : ℝ)+1)/(2*K+1)) ≤ W.card → (2*M)^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∑ q ∈ Q, ‖∑ t ∈ W, phase (pairRatio q) t‖^2) ≤
        C*T^η*M*(W.card : ℝ)^2 := by
  obtain ⟨C, hC, hbound⟩ := rational_energy_real_height hK hη
  refine ⟨2*C, by positivity, ?_⟩
  intro T t₀ M hT hM Q hQ W hRT hR hMR hW hsep
  rw [reduced_energy_eq_rational_energy Q (fun q hq => ⟨(hQ q hq).2.1, (hQ q hq).2.2.1⟩) W]
  have hrat : ∀ q ∈ Q.image pairRatio, 0 < q ∧ (q.den : ℝ) ≤ 2*M ∧
      |Real.log (q : ℝ)| ≤ 1 := by
    intro r hr
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hr
    obtain ⟨h1, h2, hc, hl1, hu1, hl2, hu2⟩ := hQ q hq
    refine ⟨div_pos (by exact_mod_cast h1) (by exact_mod_cast h2), ?_,
      dyadic_pair_log h1 h2 hl1 hu1 hl2 hu2⟩
    rw [coprime_pair_den h2 hc]
    exact hu2
  have hh := hbound T t₀ (2*M) hT (by positivity) (Q.image pairRatio) hrat
    W hRT hR hMR hW hsep
  convert hh using 1
  ring

end Montgomery.RationalMoment
