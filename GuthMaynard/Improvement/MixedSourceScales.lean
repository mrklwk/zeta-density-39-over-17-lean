module
public import GuthMaynard.Improvement.UnequalSourceScales

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped SchwartzMap
namespace GuthMaynard.Improvement
open RiemannZeta.GuthMaynard

/-- Low frequency with three independent integer shells, bounded separately
by outer scale R and denominator scale K. -/
theorem mixed_source_low_frequency (n : ℕ) (f : 𝓢(ℝ, ℝ))
    (hf : ∀ x, 0 ≤ f x) {M₁ M₂ M₃ R K : ℕ}
    (h₁ : 0 < M₁) (h₂ : 0 < M₂) (h₃ : 0 < M₃)
    (h₁R : M₁ ≤ R) (h₂K : M₂ ≤ K) (h₃R : M₃ ≤ R)
    {Q : ℝ} (hQ : 1 ≤ Q) :
    2*gmAffineFirstPoissonRadius M₁ M₃ Q*
      (gmAffinePoissonMainEnvelope f M₁ M₂ M₃ Q+gmAffinePoissonFarEnvelope n f M₁ M₂ M₃ Q)^2 ≤
      (gmAffineRegionIConstant n)^2*Q^3*(R:ℝ)^2*(K:ℝ)^4*(∫ x, f x)^2 := by
  have henv := gmAffinePoissonEnvelopes_le_mass n f hf h₁ h₂ h₃ hQ
  have h₃p : (0:ℝ) < M₃ := by exact_mod_cast h₃
  have h₁r : (M₁:ℝ) ≤ R := by exact_mod_cast h₁R
  have h₂k : (M₂:ℝ) ≤ K := by exact_mod_cast h₂K
  have h₃r : (M₃:ℝ) ≤ R := by exact_mod_cast h₃R
  have hrad : 0 ≤ gmAffineFirstPoissonRadius M₁ M₃ Q := by unfold gmAffineFirstPoissonRadius; positivity
  have hsum : 0 ≤ ∑' j : ℤ, gmIntDecayProfile 2 j :=
    tsum_nonneg (fun j => by unfold gmIntDecayProfile; split_ifs <;> positivity)
  have henv0 : 0 ≤ gmAffinePoissonMainEnvelope f M₁ M₂ M₃ Q+gmAffinePoissonFarEnvelope n f M₁ M₂ M₃ Q := by
    unfold gmAffinePoissonMainEnvelope gmAffinePoissonFarEnvelope
    positivity
  calc
    _ ≤ 2*gmAffineFirstPoissonRadius M₁ M₃ Q*
      (gmAffineRegionIConstant n*Q*(M₂:ℝ)^2*M₃*(∫ x, f x))^2 := by gcongr
    _ = (1/2:ℝ)*((gmAffineRegionIConstant n)^2*Q^3*((M₁:ℝ)*M₃)*(M₂:ℝ)^4*(∫ x, f x)^2) := by
      unfold gmAffineFirstPoissonRadius
      field_simp [h₃p.ne']
      ring
    _ ≤ (1/2:ℝ)*((gmAffineRegionIConstant n)^2*Q^3*((R:ℝ)*R)*(K:ℝ)^4*(∫ x, f x)^2) := by gcongr
    _ ≤ _ := by
      have hz : 0 ≤ (gmAffineRegionIConstant n)^2*Q^3*(R:ℝ)^2*(K:ℝ)^4*(∫ x, f x)^2 := by positivity
      nlinarith only [hz]

set_option maxHeartbeats 800000 in
/-- Retained core with independent slope and translation scales; the
result uses RK, not the square of a common worst-case scale. -/
theorem mixed_source_retained_core {ε T Q Y : ℝ}
    (hT : 0 < T) (hQ : 1 ≤ Q) (hY : 0 ≤ Y) (f : 𝓢(ℝ, ℝ))
    {M₁ M₂ M₃ R K : ℕ} (h₁ : 0 < M₁) (h₂ : 0 < M₂) (h₃ : 0 < M₃)
    (h₁R : M₁ ≤ R) (h₂K : M₂ ≤ K) (h₃R : M₃ ≤ R)
    {Cdiv : ℝ} (hCdiv : 0 ≤ Cdiv) :
    gmAffineRegionIICoreRawBound ε T Q Y hT (zero_lt_one.trans_le hQ) f M₁ M₂ M₃ Cdiv ≤
      Cdiv*gmAffineRegionIICoreConstant*(Y+gmAffineFirstPoissonRadius M₁ M₃ Q)^ε*
        Q^3*((R:ℝ)*(K:ℝ))*(Real.sqrt (∫ u, f u^2)*
          Real.sqrt (gmAffineJ (gmAffineTildeSchwartz
            (gmAffineSecondPoissonCutoff T Q M₂ M₃/Q)
            (by unfold gmAffineSecondPoissonCutoff; positivity) f) M₂)) := by
  have hrad : 0 ≤ gmAffineFirstPoissonRadius M₁ M₃ Q := by unfold gmAffineFirstPoissonRadius; positivity
  have hwindow : 0 ≤ (Y+gmAffineFirstPoissonRadius M₁ M₃ Q)^ε := by positivity
  have hfactor := gmAffineFirstPoissonRadius_card_factor_mul_scale_le h₁ h₃ hQ
  have h₁r : (M₁:ℝ) ≤ R := by exact_mod_cast h₁R
  have h₂k : (M₂:ℝ) ≤ K := by exact_mod_cast h₂K
  have h₃r : (M₃:ℝ) ≤ R := by exact_mod_cast h₃R
  have hscale : (2*gmAffineFirstPoissonRadius M₁ M₃ Q+3)*(M₃:ℝ)*(M₂:ℝ) ≤ 8*Q*((R:ℝ)*(K:ℝ)) := by
    calc
      _ ≤ (4*Q*((M₁:ℝ)+M₃))*(M₂:ℝ) := mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg M₂)
      _ ≤ (4*Q*((R:ℝ)+R))*(K:ℝ) := by gcongr
      _ = _ := by ring
  let H : ℝ := Real.sqrt (∫ u : ℝ, f u ^ 2) *
    Real.sqrt (gmAffineJ
      (gmAffineTildeSchwartz
        (gmAffineSecondPoissonCutoff T Q M₂ M₃ / Q)
        (by unfold gmAffineSecondPoissonCutoff; positivity) f) M₂)
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  unfold gmAffineRegionIICoreRawBound gmAffineRegionIICoreConstant
  dsimp only
  change 2 *
      (Cdiv * (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ ε *
        (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3)) *
      ((32 * M₃ : ℝ) * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2 *
        (Q * (16 * (M₂ : ℝ) ^ 2 *
          ((Q / (M₂ : ℝ)) * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual) * H))) ≤
    Cdiv * (8192 * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 3) *
      (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ ε * Q ^ 3 * ((R : ℝ) * K) * H
  have h₂p : (0:ℝ) < M₂ := by exact_mod_cast h₂
  calc
    _ = 1024*Cdiv*(Y+gmAffineFirstPoissonRadius M₁ M₃ Q)^ε*
      SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual^3*Q^2*
      ((2*gmAffineFirstPoissonRadius M₁ M₃ Q+3)*(M₃:ℝ)*M₂)*H := by
        field_simp [h₂p.ne']
        ring
    _ ≤ 1024*Cdiv*(Y+gmAffineFirstPoissonRadius M₁ M₃ Q)^ε*
      SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual^3*Q^2*(8*Q*((R:ℝ)*K))*H := by gcongr
    _ = _ := by ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.mixed_source_low_frequency
#print axioms GuthMaynard.Improvement.mixed_source_retained_core
