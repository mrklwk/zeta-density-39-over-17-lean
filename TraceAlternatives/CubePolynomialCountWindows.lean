module
public import TraceAlternatives.CubePolynomialCount
public import TraceAlternatives.CubeCountTargetWindows

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Filter Finset GuthMaynard.Improvement GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

/-- Pure numeric conditions for the sharp actual-polynomial count. -/
structure CubeCountWindow (σ a : ℝ) : Prop where
  sigma_low : 4/5 ≤ σ
  sigma_high : σ < 1
  a_low : 1/2 ≤ a
  a_high : a < 2/3
  budgets : ∀ x : ℝ, a ≤ x → ∀ j : Fin 2, ∀ i : Fin 5,
    0 ≤ cubeTraceEnergyMargin σ a x j i

theorem cubeCountWindow_row3 {σ : ℝ} (hlo : 163/198 ≤ σ) (hhi : σ ≤ 7873/9370) :
    CubeCountWindow σ (31544/(107010*σ-33609)) := by
  have hd : 0 < 107010*σ-33609 := by linarith
  have hσ : 4/5 ≤ σ := by linarith
  have ha : 1/2 ≤ 31544/(107010*σ-33609) := by
    apply (le_div_iff₀ hd).mpr
    linarith
  refine ⟨hσ,by linarith,ha,?_,?_⟩
  · apply (div_lt_iff₀ hd).mpr
    linarith
  · intro x hxa j i
    have hh := cubeTraceEnergyMargin_row3 hlo hhi (le_refl (31544/(107010*σ-33609)))
      (show 31544/(107010*σ-33609) ≤ 3*(31544/(107010*σ-33609))/2 by linarith) j i
    exact hh.trans (cubeTraceEnergyMargin_mono_length (by linarith : 13/16 ≤ σ) hxa j i)

theorem cubeCountWindow_row4_prefix {σ : ℝ} (hlo : 7873/9370 ≤ σ) (hhi : σ ≤ 745889/886700) :
    CubeCountWindow σ (1261710/(4342380*σ-1396527)) := by
  have hd : 0 < 4342380*σ-1396527 := by linarith
  have hσ : 4/5 ≤ σ := by linarith
  have ha : 1/2 ≤ 1261710/(4342380*σ-1396527) := by
    apply (le_div_iff₀ hd).mpr
    linarith
  refine ⟨hσ,by linarith,ha,?_,?_⟩
  · apply (div_lt_iff₀ hd).mpr
    linarith
  · intro x hxa j i
    have hh := cubeTraceEnergyMargin_row4_prefix hlo hhi (le_refl (1261710/(4342380*σ-1396527)))
      (show 1261710/(4342380*σ-1396527) ≤ 3*(1261710/(4342380*σ-1396527))/2 by linarith) j i
    exact hh.trans (cubeTraceEnergyMargin_mono_length (by linarith : 13/16 ≤ σ) hxa j i)

/-- The full perturbed short-polynomial window, with all analytic inputs
supplied and only the numeric window remaining as a parameter. -/
theorem cube_polynomial_count_window_loss {σ a δ : ℝ}
    (hw : CubeCountWindow σ a) (hδ : 0 < δ) (hδa : δ ≤ (1-3*a/2)/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ N : ℝ, 2 ≤ T → T^a ≤ N → N ≤ T^(3*a/2+δ) →
      ∀ b : ℕ → ℂ, (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ*T^(-2*δ) ≤ ‖boundedPolynomial N b t‖) →
      (W.card:ℝ) ≤ C*T^(3*a*(1-σ)+72*δ) :=
  cube_polynomial_count_loss hw.sigma_low hw.sigma_high hw.a_low hw.a_high hδ hδa hw.budgets

/-- Actual arbitrary bounded coefficients on the whole prescribed length
window, at the final p+epsilon exponent and every realT>=2. -/
theorem cube_polynomial_count_window {σ a ε : ℝ}
    (hw : CubeCountWindow σ a) (hε : 0 < ε) :
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
  obtain ⟨C,hC,hBound⟩ := cube_polynomial_count_window_loss hw hδ (by linarith [hw.a_high])
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


end Montgomery.RationalMoment
