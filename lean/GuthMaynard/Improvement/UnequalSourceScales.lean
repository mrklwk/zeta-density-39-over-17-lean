import GuthMaynard.AffineSource.LargeValuesAffineHeight
/- Unequal-scale refinements of the isolated McColm source, MIT-0.
The integral objects are unchanged; the separate R,K factors are retained. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped SchwartzMap
namespace GuthMaynard.Improvement
open RiemannZeta.GuthMaynard

theorem unequal_source_low_frequency (n : ℕ) (f : 𝓢(ℝ, ℝ))
    (hf : ∀ x, 0 ≤ f x) {R K : ℕ} (hR : 0 < R) (hK : 0 < K)
    {Q : ℝ} (hQ : 1 ≤ Q) :
    2*gmAffineFirstPoissonRadius R R Q*
      (gmAffinePoissonMainEnvelope f R K R Q+gmAffinePoissonFarEnvelope n f R K R Q)^2 ≤
      (gmAffineRegionIConstant n)^2*Q^3*(R:ℝ)^2*(K:ℝ)^4*(∫ x, f x)^2 := by
  have henv := gmAffinePoissonEnvelopes_le_mass n f hf hR hK hR hQ
  have hC := gmAffineRegionIConstant_nonneg n
  have hmass : 0 ≤ ∫ x, f x := integral_nonneg hf
  have hRp : (0:ℝ) < R := by exact_mod_cast hR
  have hrad : 0 ≤ gmAffineFirstPoissonRadius R R Q := by unfold gmAffineFirstPoissonRadius; positivity
  have hsum : 0 ≤ ∑' j : ℤ, gmIntDecayProfile 2 j :=
    tsum_nonneg (fun j => by unfold gmIntDecayProfile; split_ifs <;> positivity)
  have henv0 : 0 ≤ gmAffinePoissonMainEnvelope f R K R Q+gmAffinePoissonFarEnvelope n f R K R Q := by
    unfold gmAffinePoissonMainEnvelope gmAffinePoissonFarEnvelope
    positivity
  calc
    _ ≤ 2*gmAffineFirstPoissonRadius R R Q*
      (gmAffineRegionIConstant n*Q*(K:ℝ)^2*R*(∫ x, f x))^2 := by gcongr
    _ = (1/2:ℝ)*((gmAffineRegionIConstant n)^2*Q^3*(R:ℝ)^2*(K:ℝ)^4*(∫ x, f x)^2) := by
      unfold gmAffineFirstPoissonRadius
      field_simp [hRp.ne']
      ring
    _ ≤ _ := by
      have hh : 0 ≤ (gmAffineRegionIConstant n)^2*Q^3*(R:ℝ)^2*(K:ℝ)^4*(∫ x, f x)^2 := by positivity
      linarith

theorem unequal_source_retained_core {ε T Q Y : ℝ}
    (hT : 0 < T) (hQ : 1 ≤ Q) (hY : 0 ≤ Y) (f : 𝓢(ℝ, ℝ))
    {R K : ℕ} (hR : 0 < R) (hK : 0 < K) {Cdiv : ℝ} (hCdiv : 0 ≤ Cdiv) :
    gmAffineRegionIICoreRawBound ε T Q Y hT (zero_lt_one.trans_le hQ) f R K R Cdiv ≤
      Cdiv*gmAffineRegionIICoreConstant*(Y+gmAffineFirstPoissonRadius R R Q)^ε*
        Q^3*((R:ℝ)*(K:ℝ))*(Real.sqrt (∫ u, f u^2)*
          Real.sqrt (gmAffineJ (gmAffineTildeSchwartz
            (gmAffineSecondPoissonCutoff T Q K R/Q)
            (by unfold gmAffineSecondPoissonCutoff; positivity) f) K)) := by
  have hrad : 0 ≤ gmAffineFirstPoissonRadius R R Q := by unfold gmAffineFirstPoissonRadius; positivity
  have hwindow : 0 ≤ (Y+gmAffineFirstPoissonRadius R R Q)^ε := by positivity
  have hfactor := gmAffineFirstPoissonRadius_card_factor_mul_scale_le hR hR hQ
  have hscale : (2*gmAffineFirstPoissonRadius R R Q+3)*(R:ℝ)*(K:ℝ) ≤ 8*Q*((R:ℝ)*(K:ℝ)) := by
    calc
      _ ≤ (4*Q*((R:ℝ)+R))*(K:ℝ) := mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg K)
      _ = _ := by ring
  let H : ℝ := Real.sqrt (∫ u : ℝ, f u ^ 2) *
    Real.sqrt (gmAffineJ
      (gmAffineTildeSchwartz
        (gmAffineSecondPoissonCutoff T Q K R / Q)
        (by unfold gmAffineSecondPoissonCutoff; positivity) f) K)
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  unfold gmAffineRegionIICoreRawBound gmAffineRegionIICoreConstant
  dsimp only
  change 2 *
      (Cdiv * (Y + gmAffineFirstPoissonRadius R R Q) ^ ε *
        (2 * gmAffineFirstPoissonRadius R R Q + 3)) *
      ((32 * R : ℝ) *
        SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2 *
        (Q * (16 * (K : ℝ) ^ 2 *
          ((Q / (K : ℝ)) * SchwartzMap.seminorm ℝ 0 0
            gmAffineLocalBumpDual) * H))) ≤
    Cdiv * (8192 * SchwartzMap.seminorm ℝ 0 0
        gmAffineLocalBumpDual ^ 3) *
      (Y + gmAffineFirstPoissonRadius R R Q) ^ ε *
      Q ^ 3 * ((R : ℝ) * (K : ℝ)) * H
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  rw [show
    2 *
        (Cdiv * (Y + gmAffineFirstPoissonRadius R R Q) ^ ε *
          (2 * gmAffineFirstPoissonRadius R R Q + 3)) *
        ((32 * R : ℝ) *
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2 *
          (Q * (16 * (K : ℝ) ^ 2 *
            ((Q / (K : ℝ)) * SchwartzMap.seminorm ℝ 0 0
              gmAffineLocalBumpDual) * H))) =
      1024 * Cdiv *
        (Y + gmAffineFirstPoissonRadius R R Q) ^ ε *
        SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 3 * Q ^ 2 *
        ((2 * gmAffineFirstPoissonRadius R R Q + 3) *
          (R : ℝ) * (K : ℝ)) * H by
      field_simp [hKpos.ne']
      ring]
  calc
    1024 * Cdiv *
        (Y + gmAffineFirstPoissonRadius R R Q) ^ ε *
        SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 3 * Q ^ 2 *
        ((2 * gmAffineFirstPoissonRadius R R Q + 3) *
          (R : ℝ) * (K : ℝ)) * H ≤
      1024 * Cdiv *
        (Y + gmAffineFirstPoissonRadius R R Q) ^ ε *
        SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 3 * Q ^ 2 *
        (8 * Q * ((R : ℝ) * (K : ℝ))) * H := by gcongr
    _ = Cdiv * (8192 * SchwartzMap.seminorm ℝ 0 0
          gmAffineLocalBumpDual ^ 3) *
        (Y + gmAffineFirstPoissonRadius R R Q) ^ ε *
        Q ^ 3 * ((R : ℝ) * (K : ℝ)) * H := by ring


end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.unequal_source_low_frequency
#print axioms GuthMaynard.Improvement.unequal_source_retained_core
