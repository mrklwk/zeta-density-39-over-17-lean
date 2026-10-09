import MathCollab.Density.DetectorFamilyScales
import GuthMaynard.Improvement.ShortDetectorDyadic
import Mathlib.Analysis.Complex.ExponentialBounds

open Real Set Filter MathCollab.Density
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- A coarse natural-cutoff bound, sufficient for all family counts. -/
theorem shortDetectorCutoff_eventually_le_sq :
    ∀ᶠ T : ℝ in atTop, (shortDetectorCutoff T : ℝ) ≤ T^2 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), firstDetectorCutoff_eventually_le_sq] with T hT hK
  have hr : T^(1/2:ℝ) ≤ T := by
    simpa using Real.rpow_le_rpow_of_exponent_le hT (show (1/2:ℝ) ≤ 1 by norm_num)
  have hc : shortDetectorCutoff T ≤ firstDetectorCutoff T :=
    Nat.ceil_mono (mul_le_mul_of_nonneg_right hr (sq_nonneg _))
  exact (show (shortDetectorCutoff T : ℝ) ≤ firstDetectorCutoff T by exact_mod_cast hc).trans hK

/-- Explicit O(log T) size of the fixed dyadic list. -/
theorem shortDetectorDyadicCount_le_log {T : ℝ} (hT : 1 ≤ T) (hlog : 1 ≤ Real.log T)
    (hK : (shortDetectorCutoff T : ℝ) ≤ T^2) :
    (shortDetectorDyadicCount T : ℝ) ≤ 5*Real.log T := by
  let K := shortDetectorCutoff T
  have hTpos : 0 < T := by linarith
  have hKpos : 0 < K := by
    apply Nat.ceil_pos.mpr
    exact mul_pos (Real.rpow_pos_of_pos hTpos _) (sq_pos_of_pos (by linarith))
  have hp : (2 : ℝ)^(Nat.log 2 K) ≤ (K : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hKpos.ne'
  have hl := (Real.log_le_log (by positivity) hp).trans (Real.log_le_log (by exact_mod_cast hKpos) hK)
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have htwo : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hnonneg : (0 : ℝ) ≤ Nat.log 2 K := by positivity
  have hprod := mul_le_mul_of_nonneg_left htwo hnonneg
  change ((Nat.log 2 K+1 : ℕ) : ℝ) ≤ _
  push_cast
  linarith

/-- All scales are selected before beta, gamma or an actual zero varies. -/
theorem short_detector_family_scales_eventually :
    ∀ᶠ T : ℝ in atTop, 2 ≤ T ∧ 1 ≤ Real.log T ∧
      (shortDetectorCutoff T : ℝ) ≤ T^2 ∧
      (shortDetectorDyadicCount T : ℝ) ≤ 5*Real.log T ∧
      (detectorTaylorCutoff T+1 : ℝ) ≤ 12*Real.log T ∧
      3*T^(-1 : ℝ) ≤ 1/(6*(shortDetectorDyadicCount T : ℝ)) := by
  have ht := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero
  norm_num at ht
  filter_upwards [eventually_ge_atTop (2 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1,
    shortDetectorCutoff_eventually_le_sq, ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1/90 by norm_num))]
    with T hT hlog hK hsmall
  have hD := shortDetectorDyadicCount_le_log (by linarith) hlog hK
  refine ⟨hT, hlog, hK, hD, detectorTaylorCutoff_le_log hlog, ?_⟩
  have hTpos : 0 < T := by linarith
  have hDpos : (0 : ℝ) < shortDetectorDyadicCount T := by unfold shortDetectorDyadicCount; positivity
  rw [Real.rpow_neg_one, ← one_div]
  apply (le_div_iff₀ (by positivity : 0 < 6*(shortDetectorDyadicCount T : ℝ))).2
  have hl : Real.log T < T/90 := (div_lt_iff₀ hTpos).mp hsmall |>.trans_eq (by ring)
  rw [show 3*(1/T)*(6*(shortDetectorDyadicCount T : ℝ)) = 18*(shortDetectorDyadicCount T : ℝ)/T by ring]
  apply (div_le_iff₀ hTpos).2
  nlinarith

end GuthMaynard.Improvement

#print axioms GuthMaynard.Improvement.shortDetectorCutoff_eventually_le_sq
#print axioms GuthMaynard.Improvement.shortDetectorDyadicCount_le_log
#print axioms GuthMaynard.Improvement.short_detector_family_scales_eventually
