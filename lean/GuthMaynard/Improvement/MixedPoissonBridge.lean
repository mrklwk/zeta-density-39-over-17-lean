module
public import GuthMaynard.Improvement.MixedSourceScales

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace GuthMaynard.Improvement
open RiemannZeta.GuthMaynard

/-- Actual independent-triple two-Poisson reduction, with one divisor constant
chosen before every height, scale and input. All discarded integrals/series
remain explicit. The only analytic input premise is the displayed nth-order
Fourier decay of the original Schwartz input. -/
theorem mixed_two_poisson_raw {ε : ℝ} (hε : 0 < ε) :
    ∃ Cdiv : ℝ, 0 < Cdiv ∧ ∀ (n : ℕ) (T Q Y Ctail : ℝ) (f : 𝓢(ℝ, ℝ)) (M₁ M₂ M₃ R K : ℕ),
      1 ≤ n → ∀ (hT : 1 ≤ T) (hQ : 1 ≤ Q), 0 < Y → 0 ≤ Ctail →
      (∀ x, 0 ≤ f x) → GMAffineIterationSupported f → 0 < M₁ → 0 < M₂ → 0 < M₃ → M₁ ≤ R → M₂ ≤ K → M₃ ≤ R →
      gmAffineFirstPoissonRadius M₁ M₃ Q ≤ Y →
      (∀ ξ : ℝ, ξ ≠ 0 → ‖𝓕 (gmAffineComplexify f) ξ‖ ≤
        Ctail*T^ε*(T/|ξ|)^n*SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f)) →
      gmAffineTransformIntegral f M₁ M₂ M₃ ≤
        (gmAffineRegionIConstant n)^2*Q^3*(R:ℝ)^2*(K:ℝ)^4*(∫ x, f x)^2+
        Cdiv*gmAffineRegionIICoreConstant*(Y+gmAffineFirstPoissonRadius M₁ M₃ Q)^ε*
          Q^3*((R:ℝ)*(K:ℝ))*(Real.sqrt (∫ u, f u^2)*
            Real.sqrt (gmAffineJ (gmAffineTildeSchwartz
              (gmAffineSecondPoissonCutoff T Q M₂ M₃/Q)
              (by
                have ht : 0 < T := zero_lt_one.trans_le hT
                have hq : 0 < Q := zero_lt_one.trans_le hQ
                exact div_pos (gmAffineSecondPoissonCutoff_pos ht hq) hq) f) M₂))+
        gmAffineRegionIITailRawBound ε n T Q Y f M₁ M₂ M₃ Cdiv Ctail+
        gmAffineRegionIIIRawBound n Y f M₁ M₂ M₃ Q := by
  obtain ⟨Cdiv,hCdiv,hcard⟩ := exists_global_card_gmAffineFirstPoissonPairs_middle_real_le hε
  refine ⟨Cdiv,hCdiv,?_⟩
  intro n T Q Y Ctail f M₁ M₂ M₃ R K hn hT hQ hY hCtail hf hsupp h₁ h₂ h₃ h₁R h₂K h₃R hXY hCdecay
  let B := gmAffineSecondPoissonCutoff T Q M₂ M₃
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hBpos : 0 < B := by
    dsimp only [B]
    exact gmAffineSecondPoissonCutoff_pos hTpos hQpos
  have hmiddleBase :=
    integral_gmAffineMiddleFrequencyRegion_fourier_sq_le_sigmaIIReal_add_source_tails_of_constants
      hTpos hCdiv hCtail n f hCdecay h₁ h₂ h₃ hQpos hY.le hBpos
        (hcard h₁ h₃ hQpos hY.le)
        (by dsimp only [B]; exact
          gmAffineSecondPoissonCutoff_width hTpos hQpos)
  have hsigma := norm_gmAffineSigmaIIReal_le_J_add_far
    n hBpos hQpos (show 0 < (8 * M₃ : ℝ) by positivity)
      (by dsimp only [B]; exact
        gmAffineSecondPoissonCutoff_ge_Q hT (zero_le_one.trans hQ))
      h₂ f hf hsupp
  let D : ℝ := Cdiv *
    (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ ε *
      (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3)
  let Z : ℝ := (32 * M₃ : ℝ) *
    SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2
  have hrad : 0 ≤ gmAffineFirstPoissonRadius M₁ M₃ Q := by
    unfold gmAffineFirstPoissonRadius
    positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hmiddle := hmiddleBase.trans (by
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left
      · apply mul_le_mul_of_nonneg_left
        · exact add_le_add hsigma le_rfl
        · exact hZ
      · positivity
    · exact le_rfl)
  have hmiddleRaw :
      (∫ xi in gmAffineMiddleFrequencyRegion
          (gmAffineFirstPoissonRadius M₁ M₃ Q) Y,
        ‖𝓕 (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃) xi‖ ^ 2) ≤
        gmAffineRegionIIRawBound ε n T Q Y hTpos hQpos
          f M₁ M₂ M₃ Cdiv Ctail := by
    dsimp only [B] at hmiddle
    unfold gmAffineRegionIIRawBound
    dsimp only
    convert hmiddle using 1
    all_goals ring_nf
  have hrad0 : 0 ≤ gmAffineFirstPoissonRadius M₁ M₃ Q := by unfold gmAffineFirstPoissonRadius; positivity
  have hlow := (integral_gmAffineLowFrequencyRegion_fourier_sq_le n f h₁ h₂ h₃ hQpos hrad0).trans
    (mixed_source_low_frequency n f hf h₁ h₂ h₃ h₁R h₂K h₃R hQ)
  have hhigh := integral_gmAffineHighFrequencyRegion_fourier_sq_le n hn f h₁ h₂ h₃ hQpos hY
  have hentry := gmAffineTransformIntegral_le_smooth_fourier f hf h₁ h₂ h₃
  rw [integral_gmAffineSmoothTransform_fourier_sq_eq_regions f M₁ M₂ M₃ hXY] at hentry
  have hraw := hentry.trans (add_le_add (add_le_add hlow hmiddleRaw) hhigh)
  rw [gmAffineRegionIIRawBound_eq_core_add_tail] at hraw
  have hcore := mixed_source_retained_core (ε := ε) hTpos hQ hY.le f h₁ h₂ h₃ h₁R h₂K h₃R hCdiv.le
  unfold gmAffineRegionIIIRawBound
  linarith

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.mixed_two_poisson_raw
