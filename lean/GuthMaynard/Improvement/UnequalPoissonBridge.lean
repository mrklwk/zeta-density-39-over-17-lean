module
public import GuthMaynard.Improvement.UnequalSourceScales

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace GuthMaynard.Improvement
open RiemannZeta.GuthMaynard

/-- Actual fixed-triple two-Poisson reduction, with one divisor constant
chosen before every height, scale and input. All discarded integrals/series
remain explicit. The only analytic input premise is the displayed nth-order
Fourier decay of the original Schwartz input. -/
theorem unequal_two_poisson_raw {ε : ℝ} (hε : 0 < ε) :
    ∃ Cdiv : ℝ, 0 < Cdiv ∧ ∀ (n : ℕ) (T Q Y Ctail : ℝ) (f : 𝓢(ℝ, ℝ)) (R K : ℕ),
      1 ≤ n → ∀ (hT : 1 ≤ T) (hQ : 1 ≤ Q), 0 < Y → 0 ≤ Ctail →
      (∀ x, 0 ≤ f x) → GMAffineIterationSupported f → 0 < R → 0 < K →
      gmAffineFirstPoissonRadius R R Q ≤ Y →
      (∀ ξ : ℝ, ξ ≠ 0 → ‖𝓕 (gmAffineComplexify f) ξ‖ ≤
        Ctail*T^ε*(T/|ξ|)^n*SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f)) →
      gmAffineTransformIntegral f R K R ≤
        (gmAffineRegionIConstant n)^2*Q^3*(R:ℝ)^2*(K:ℝ)^4*(∫ x, f x)^2+
        Cdiv*gmAffineRegionIICoreConstant*(Y+gmAffineFirstPoissonRadius R R Q)^ε*
          Q^3*((R:ℝ)*(K:ℝ))*(Real.sqrt (∫ u, f u^2)*
            Real.sqrt (gmAffineJ (gmAffineTildeSchwartz
              (gmAffineSecondPoissonCutoff T Q K R/Q)
              (by
                have ht : 0 < T := zero_lt_one.trans_le hT
                have hq : 0 < Q := zero_lt_one.trans_le hQ
                exact div_pos (gmAffineSecondPoissonCutoff_pos ht hq) hq) f) K))+
        gmAffineRegionIITailRawBound ε n T Q Y f R K R Cdiv Ctail+
        gmAffineRegionIIIRawBound n Y f R K R Q := by
  obtain ⟨Cdiv,hCdiv,hcard⟩ := exists_global_card_gmAffineFirstPoissonPairs_middle_real_le hε
  refine ⟨Cdiv,hCdiv,?_⟩
  intro n T Q Y Ctail f R K hn hT hQ hY hCtail hf hsupp hR hK hXY hCdecay
  let B := gmAffineSecondPoissonCutoff T Q K R
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hBpos : 0 < B := by
    dsimp only [B]
    exact gmAffineSecondPoissonCutoff_pos hTpos hQpos
  have hmiddleBase :=
    integral_gmAffineMiddleFrequencyRegion_fourier_sq_le_sigmaIIReal_add_source_tails_of_constants
      hTpos hCdiv hCtail n f hCdecay hR hK hR hQpos hY.le hBpos
        (hcard hR hR hQpos hY.le)
        (by dsimp only [B]; exact
          gmAffineSecondPoissonCutoff_width hTpos hQpos)
  have hsigma := norm_gmAffineSigmaIIReal_le_J_add_far
    n hBpos hQpos (show 0 < (8 * R : ℝ) by positivity)
      (by dsimp only [B]; exact
        gmAffineSecondPoissonCutoff_ge_Q hT (zero_le_one.trans hQ))
      hK f hf hsupp
  let D : ℝ := Cdiv *
    (Y + gmAffineFirstPoissonRadius R R Q) ^ ε *
      (2 * gmAffineFirstPoissonRadius R R Q + 3)
  let Z : ℝ := (32 * R : ℝ) *
    SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2
  have hrad : 0 ≤ gmAffineFirstPoissonRadius R R Q := by
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
          (gmAffineFirstPoissonRadius R R Q) Y,
        ‖𝓕 (gmAffineSmoothTransformSchwartz f R K R) xi‖ ^ 2) ≤
        gmAffineRegionIIRawBound ε n T Q Y hTpos hQpos
          f R K R Cdiv Ctail := by
    dsimp only [B] at hmiddle
    unfold gmAffineRegionIIRawBound
    dsimp only
    convert hmiddle using 1
    all_goals ring_nf
  have hrad0 : 0 ≤ gmAffineFirstPoissonRadius R R Q := by unfold gmAffineFirstPoissonRadius; positivity
  have hlow := (integral_gmAffineLowFrequencyRegion_fourier_sq_le n f hR hK hR hQpos hrad0).trans
    (unequal_source_low_frequency n f hf hR hK hQ)
  have hhigh := integral_gmAffineHighFrequencyRegion_fourier_sq_le n hn f hR hK hR hQpos hY
  have hentry := gmAffineTransformIntegral_le_smooth_fourier f hf hR hK hR
  rw [integral_gmAffineSmoothTransform_fourier_sq_eq_regions f R K R hXY] at hentry
  have hraw := hentry.trans (add_le_add (add_le_add hlow hmiddleRaw) hhigh)
  rw [gmAffineRegionIIRawBound_eq_core_add_tail] at hraw
  have hcore := unequal_source_retained_core (ε := ε) hTpos hQ hY.le f hR hK hCdiv.le
  unfold gmAffineRegionIIIRawBound
  linarith

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.unequal_two_poisson_raw
