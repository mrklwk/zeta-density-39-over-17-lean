module
public import DensityEnergyGM.FiveTermEnergy
public import GuthMaynard.Improvement.SourceTranslation

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 3200000
noncomputable section
open Finset GuthMaynard.NativeMoment GuthMaynard.Improvement
namespace Montgomery.RationalMoment

def fiveTermEnergyExpression (T N V R : ℝ) : ℝ :=
  N ^ 4 * R * V ^ (-4 : ℝ) + N ^ 4 * T ^ 2 * V ^ (-8 : ℝ) +
    N ^ (5 / 2 : ℝ) * T ^ (9 / 8 : ℝ) * V ^ (-5 : ℝ) * R ^ (3 / 2 : ℝ) +
    N ^ (40 / 31 : ℝ) * T ^ (9 / 31 : ℝ) * V ^ (-80 / 31 : ℝ) * R ^ (84 / 31 : ℝ) +
    N ^ (40 / 19 : ℝ) * T ^ (17 / 19 : ℝ) * V ^ (-80 / 19 : ℝ) * R ^ (36 / 19 : ℝ)

theorem fiveTermEnergyExpression_nonneg {T N V R : ℝ}
    (hT : 0 ≤ T) (hN : 0 ≤ N) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ fiveTermEnergyExpression T N V R := by
  dsimp only [fiveTermEnergyExpression]
  positivity

theorem first_term_le_fiveTermEnergyExpression {T N V R : ℝ}
    (hT : 0 ≤ T) (hN : 0 ≤ N) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    N ^ 4 * R * V ^ (-4 : ℝ) ≤ fiveTermEnergyExpression T N V R := by
  have hRest : 0 ≤ N ^ 4 * T ^ 2 * V ^ (-8 : ℝ) +
      N ^ (5 / 2 : ℝ) * T ^ (9 / 8 : ℝ) * V ^ (-5 : ℝ) * R ^ (3 / 2 : ℝ) +
      N ^ (40 / 31 : ℝ) * T ^ (9 / 31 : ℝ) * V ^ (-80 / 31 : ℝ) * R ^ (84 / 31 : ℝ) +
      N ^ (40 / 19 : ℝ) * T ^ (17 / 19 : ℝ) * V ^ (-80 / 19 : ℝ) * R ^ (36 / 19 : ℝ) := by positivity
  simpa only [fiveTermEnergyExpression, add_assoc] using
    le_add_of_nonneg_right (a := N ^ 4 * R * V ^ (-4 : ℝ)) hRest

theorem bounded_polynomial_norm_le_two_scale {N : ℝ} (hN : 1 ≤ N)
    (a : ℕ → ℂ) (ha : ∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) (t : ℝ) :
    ‖boundedPolynomial N a t‖ ≤ 2 * N := by
  have hCard : ((sourceRatioIndices N).card : ℝ) ≤ N + 1 := by
    have hf : ⌊N⌋₊ ≤ ⌊2 * N⌋₊ := Nat.floor_mono (by linarith)
    rw [sourceRatioIndices, Nat.card_Ioc, Nat.cast_sub hf]
    linarith [Nat.floor_le (by linarith : 0 ≤ 2 * N), Nat.lt_floor_add_one N]
  calc
    _ ≤ ∑ n ∈ sourceRatioIndices N, ‖a n‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro n hn
      simp only [norm_mul, Complex.norm_exp]
      simp
    _ ≤ ∑ _n ∈ sourceRatioIndices N, (1 : ℝ) := Finset.sum_le_sum ha
    _ = ((sourceRatioIndices N).card : ℝ) := by simp
    _ ≤ N + 1 := hCard
    _ ≤ _ := by linarith

/-- Uniform in every real height T>=2; the compact prefix is proved using
actual coefficient and separation bounds, with no new analytic premise. -/
theorem discrete_energy_five_term_base (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T N : ℝ) (a : ℕ → ℂ) (W : Finset ℝ) (V : ℝ),
        2 ≤ T → 0 < N → T ≤ N ^ 2 → N ≤ T →
        (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
        0 < V → (∀ t ∈ W, V ≤ ‖boundedPolynomial N a t‖) →
        IsSeparated 1 W → InBaseInterval T W →
        (discreteAdditiveEnergy W : ℝ) ≤
          C * T ^ ε * fiveTermEnergyExpression T N V (W.card : ℝ) := by
  obtain ⟨C₀, T₀, hC₀, hT₀, hEventual⟩ := discrete_energy_five_term_base_eventual ε hε
  let C : ℝ := C₀ + 128 * T₀ ^ 3
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro T N a W V hT hN hTN hNT ha hV hValues hSep hBase
  have hTpos : 0 < T := by linarith
  have hR0 : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
  have hExpr : 0 ≤ fiveTermEnergyExpression T N V (W.card : ℝ) :=
    fiveTermEnergyExpression_nonneg hTpos.le hN.le hV.le hR0
  by_cases hHeight : T₀ ≤ T
  · have h := hEventual T N a W V hHeight hN hTN hNT ha hV hValues hSep hBase
    change (discreteAdditiveEnergy W : ℝ) ≤ C₀ * T ^ ε *
      fiveTermEnergyExpression T N V (W.card : ℝ) at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show C₀ ≤ C by
        have hp : 0 ≤ 128 * T₀ ^ 3 := by positivity
        dsimp only [C]
        linarith)
        (Real.rpow_nonneg hTpos.le ε)) hExpr)
  · by_cases hW : W.Nonempty
    swap
    · have he : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
      subst W
      simp only [discreteAdditiveEnergy, Finset.product_empty,
        Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg (by positivity) (by
        simpa only [Finset.card_empty, Nat.cast_zero] using hExpr)
    have hNOne : 1 ≤ N := by nlinarith
    obtain ⟨t, ht⟩ := hW
    have hVUpper : V ≤ 2 * N := (hValues t ht).trans
      (bounded_polynomial_norm_le_two_scale hNOne a ha t)
    have hRUpper : (W.card : ℝ) ≤ 2 * T₀ :=
      (gmSeparated_card_le_two_height (by linarith) hSep hBase).trans (by linarith)
    have hEUpper : (discreteAdditiveEnergy W : ℝ) ≤ (W.card : ℝ) ^ 4 := by
      have h := approxAddEnergy_le_card_pow_four 1 W
      rw [native_approx_energy_eq] at h
      exact_mod_cast h
    have hRcube : (W.card : ℝ) ^ 3 ≤ (2 * T₀) ^ 3 :=
      pow_le_pow_left₀ hR0 hRUpper 3
    have hEnergyPrefix : (discreteAdditiveEnergy W : ℝ) ≤ (2 * T₀) ^ 3 * (W.card : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hRcube hR0
      nlinarith
    have hVfour : V ^ 4 ≤ 16 * N ^ 4 := by
      have h := pow_le_pow_left₀ hV.le hVUpper 4
      nlinarith
    have hMain : (W.card : ℝ) ≤ 16 * (N ^ 4 * (W.card : ℝ) * V ^ (-4 : ℝ)) := by
      have h := mul_le_mul_of_nonneg_right hVfour hR0
      have hDiv : (W.card : ℝ) ≤ 16 * N ^ 4 * (W.card : ℝ) / V ^ 4 :=
        (le_div_iff₀ (pow_pos hV 4)).mpr (by nlinarith)
      norm_num
      exact hDiv.trans_eq (by ring)
    have hPrefix : (discreteAdditiveEnergy W : ℝ) ≤
        (128 * T₀ ^ 3) * (N ^ 4 * (W.card : ℝ) * V ^ (-4 : ℝ)) := by
      have h := mul_le_mul_of_nonneg_left hMain (show 0 ≤ (2 * T₀) ^ 3 by positivity)
      nlinarith
    have hPow : 1 ≤ T ^ ε := Real.one_le_rpow (by linarith) hε.le
    have hCoeff : 128 * T₀ ^ 3 ≤ C * T ^ ε := by
      have hc : 128 * T₀ ^ 3 ≤ C := by dsimp only [C]; linarith
      have hg : C ≤ C * T ^ ε := by nlinarith
      exact hc.trans hg
    calc
      _ ≤ (128 * T₀ ^ 3) * (N ^ 4 * (W.card : ℝ) * V ^ (-4 : ℝ)) := hPrefix
      _ ≤ (C * T ^ ε) * (N ^ 4 * (W.card : ℝ) * V ^ (-4 : ℝ)) :=
        mul_le_mul_of_nonneg_right hCoeff (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (first_term_le_fiveTermEnergyExpression hTpos.le hN.le hV.le hR0) (by positivity)

theorem discrete_energy_translateSet (c : ℝ) (W : Finset ℝ) :
    discreteAdditiveEnergy (translateSet c W) = discreteAdditiveEnergy W := by
  have hSet : translateSet c W = gmTranslate (-c) W := by
    simp only [translateSet, gmTranslate, sub_eq_add_neg]
  rw [← native_approx_energy_eq, hSet, approxAddEnergy_translate, native_approx_energy_eq]

/-- Full five-term additive energy on an arbitrary interval of length T,
for every real T>=2 and sqrt(T)<=N<=T. Constants precede the interval
translate, polynomial, amplitude and ordinate set. -/
theorem discrete_energy_five_term_native (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T t₀ N : ℝ) (a : ℕ → ℂ) (W : Finset ℝ) (V : ℝ),
        2 ≤ T → 0 < N → T ≤ N ^ 2 → N ≤ T →
        (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
        0 < V → (∀ t ∈ W, V ≤ ‖boundedPolynomial N a t‖) →
        IsSeparated 1 W → (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀ + T)) →
        (discreteAdditiveEnergy W : ℝ) ≤
          C * T ^ ε * fiveTermEnergyExpression T N V (W.card : ℝ) := by
  obtain ⟨C, hC, hOrigin⟩ := discrete_energy_five_term_base ε hε
  refine ⟨C, hC, ?_⟩
  intro T t₀ N a W V hT hN hTN hNT ha hV hValues hSep hInterval
  have hBase : InBaseInterval T (translateSet t₀ W) := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hlo, hhi⟩ := hInterval u hu
    exact ⟨by linarith, by linarith⟩
  have h := hOrigin T N (translatedSourceCoefficient N t₀ a) (translateSet t₀ W) V
    hT hN hTN hNT (by
      intro n hn
      rw [translatedSourceCoefficient_norm]
      exact ha n hn) hV (by
      intro t ht
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
      rw [boundedPolynomial_translate, sub_add_cancel]
      exact hValues u hu) (isSeparated_translate 1 t₀ W hSep) hBase
  rw [discrete_energy_translateSet, translateSet_card] at h
  exact h

end Montgomery.RationalMoment
