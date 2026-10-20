module
public import DensityEnergyGM.SharpPolynomialCount

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Filter Finset GuthMaynard.Improvement GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

/-- Pure numeric conditions for the sharp actual-polynomial count. -/
structure SharpCountWindow (σ a : ℝ) : Prop where
  sigma_low : 4/5 ≤ σ
  sigma_high : σ < 1
  a_low : 1/2 ≤ a
  a_high : a < 2/3
  budgets : ∀ x : ℝ, a ≤ x → ∀ j : Fin 3, ∀ i : Fin 5,
    0 ≤ gmTraceEnergyMargin σ a x j i

theorem sharpCountWindow_row6 {σ : ℝ} (hlo : 1959705/2298302 ≤ σ) (hhi : σ ≤ 6482825/7570038) :
    SharpCountWindow σ (597962/(2187648*σ-772245)) := by
  have hd : 0 < 2187648*σ-772245 := by linarith
  have hσ : 4/5 ≤ σ := by linarith
  have ha : 1/2 ≤ 597962/(2187648*σ-772245) := by
    apply (le_div_iff₀ hd).mpr
    linarith
  refine ⟨hσ,by linarith,ha,?_,?_⟩
  · apply (div_lt_iff₀ hd).mpr
    linarith
  · intro x hxa j i
    have hh := gmTraceEnergyMargin_row6 hlo hhi (le_refl (597962/(2187648*σ-772245)))
      (show 597962/(2187648*σ-772245) ≤ 3*(597962/(2187648*σ-772245))/2 by linarith) j i
    exact hh.trans (gmTraceEnergyMargin_mono_length hσ hxa j i)

theorem sharpCountWindow_row7 {σ : ℝ} (hlo : 6482825/7570038 ≤ σ) (hhi : σ ≤ 2905/3354) :
    SharpCountWindow σ (16504356/(62198298*σ-22870785)) := by
  have hd : 0 < 62198298*σ-22870785 := by linarith
  have hσ : 4/5 ≤ σ := by linarith
  have ha : 1/2 ≤ 16504356/(62198298*σ-22870785) := by
    apply (le_div_iff₀ hd).mpr
    linarith
  refine ⟨hσ,by linarith,ha,?_,?_⟩
  · apply (div_lt_iff₀ hd).mpr
    linarith
  · intro x hxa j i
    have hh := gmTraceEnergyMargin_row7 hlo hhi (le_refl (16504356/(62198298*σ-22870785)))
      (show 16504356/(62198298*σ-22870785) ≤ 3*(16504356/(62198298*σ-22870785))/2 by linarith) j i
    exact hh.trans (gmTraceEnergyMargin_mono_length hσ hxa j i)

theorem sharpCountWindow_row8 {σ : ℝ} (hlo : 2905/3354 ≤ σ) (hhi : σ ≤ 7/8) :
    SharpCountWindow σ (2172/(8226*σ-3045)) := by
  have hd : 0 < 8226*σ-3045 := by linarith
  have hσ : 4/5 ≤ σ := by linarith
  have ha : 1/2 ≤ 2172/(8226*σ-3045) := by
    apply (le_div_iff₀ hd).mpr
    linarith
  refine ⟨hσ,by linarith,ha,?_,?_⟩
  · apply (div_lt_iff₀ hd).mpr
    linarith
  · intro x hxa j i
    have hh := gmTraceEnergyMargin_row8 hlo hhi (le_refl (2172/(8226*σ-3045)))
      (show 2172/(8226*σ-3045) ≤ 3*(2172/(8226*σ-3045))/2 by linarith) j i
    exact hh.trans (gmTraceEnergyMargin_mono_length hσ hxa j i)

/-- The full perturbed short-polynomial window, with all analytic inputs
supplied and only the numeric window remaining as a parameter. -/
theorem sharp_polynomial_count_window_loss {σ a δ : ℝ}
    (hw : SharpCountWindow σ a) (hδ : 0 < δ) (hδa : δ ≤ (1-3*a/2)/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ N : ℝ, 2 ≤ T → T^a ≤ N → N ≤ T^(3*a/2+δ) →
      ∀ b : ℕ → ℂ, (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ*T^(-2*δ) ≤ ‖boundedPolynomial N b t‖) →
      (W.card:ℝ) ≤ C*T^(3*a*(1-σ)+72*δ) :=
  sharp_polynomial_count_loss hw.sigma_low hw.sigma_high hw.a_low hw.a_high hδ hδa hw.budgets

/-- Actual arbitrary bounded coefficients on the whole prescribed length
window, at the final p+epsilon exponent and every realT>=2. -/
theorem sharp_polynomial_count_window {σ a ε : ℝ}
    (hw : SharpCountWindow σ a) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ N : ℝ, 2 ≤ T → T^a ≤ N → N ≤ T^(3*a/2) →
      ∀ b : ℕ → ℂ, (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ ≤ ‖boundedPolynomial N b t‖) →
      (W.card:ℝ) ≤ C*T^(3*a*(1-σ)+ε) := by
  let δ := min (ε/1000) ((1-3*a/2)/4)
  have hδ : 0 < δ := by dsimp [δ]; exact lt_min (by positivity) (by linarith [hw.a_high])
  have hδeps : δ ≤ ε/1000 := min_le_left _ _
  have hδa : δ ≤ (1-3*a/2)/4 := min_le_right _ _
  obtain ⟨C,hC,hBound⟩ := sharp_polynomial_count_window_loss hw hδ (by linarith [hw.a_high])
  refine ⟨C,hC,?_⟩
  intro T t₀ N hT hlo hhi b hb W hW hSep hLarge
  have hT1 : 1 ≤ T := by linarith
  have hTp : 0 < T := by linarith
  have hNp : 0 < N := (Real.rpow_pos_of_pos hTp a).trans_le hlo
  have hhi' := hhi.trans (Real.rpow_le_rpow_of_exponent_le hT1
    (show 3*a/2 ≤ 3*a/2+δ by linarith))
  have hV : N^σ*T^(-2*δ) ≤ N^σ := mul_le_of_le_one_right (by positivity)
    (Real.rpow_le_one_of_one_le_of_nonpos hT1 (by linarith))
  exact (hBound T t₀ N hT hlo hhi' b hb W hW hSep (fun t ht => hV.trans (hLarge t ht))).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)) hC.le)

/-- Unconditional actual-polynomial count on the full closed row6. -/
theorem sharp_polynomial_count_row6 {σ ε : ℝ}
    (hlo : 1959705/2298302 ≤ σ) (hhi : σ ≤ 6482825/7570038) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ N : ℝ, 2 ≤ T →
      T^(597962/(2187648*σ-772245)) ≤ N → N ≤ T^(3*(597962/(2187648*σ-772245))/2) →
      ∀ b : ℕ → ℂ, (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ ≤ ‖boundedPolynomial N b t‖) →
      (W.card:ℝ) ≤ C*T^(3*(597962/(2187648*σ-772245))*(1-σ)+ε) :=
  sharp_polynomial_count_window (sharpCountWindow_row6 hlo hhi) hε

/-- Unconditional actual-polynomial count on the full closed row7. -/
theorem sharp_polynomial_count_row7 {σ ε : ℝ}
    (hlo : 6482825/7570038 ≤ σ) (hhi : σ ≤ 2905/3354) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ N : ℝ, 2 ≤ T →
      T^(16504356/(62198298*σ-22870785)) ≤ N → N ≤ T^(3*(16504356/(62198298*σ-22870785))/2) →
      ∀ b : ℕ → ℂ, (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ ≤ ‖boundedPolynomial N b t‖) →
      (W.card:ℝ) ≤ C*T^(3*(16504356/(62198298*σ-22870785))*(1-σ)+ε) :=
  sharp_polynomial_count_window (sharpCountWindow_row7 hlo hhi) hε

/-- Unconditional actual-polynomial count on the full closed row8. -/
theorem sharp_polynomial_count_row8 {σ ε : ℝ}
    (hlo : 2905/3354 ≤ σ) (hhi : σ ≤ 7/8) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ N : ℝ, 2 ≤ T →
      T^(2172/(8226*σ-3045)) ≤ N → N ≤ T^(3*(2172/(8226*σ-3045))/2) →
      ∀ b : ℕ → ℂ, (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ ≤ ‖boundedPolynomial N b t‖) →
      (W.card:ℝ) ≤ C*T^(3*(2172/(8226*σ-3045))*(1-σ)+ε) :=
  sharp_polynomial_count_window (sharpCountWindow_row8 hlo hhi) hε

end Montgomery.RationalMoment
