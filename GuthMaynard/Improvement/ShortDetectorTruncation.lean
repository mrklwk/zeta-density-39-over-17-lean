module
/- Adapted from audited Density.DetectorTruncation at eff263d7, with actual
 short mollifier X=2H^(1/100) and smoothing Y=H^(1/2). -/
public import MathCollab.Density.DetectorTruncation

@[expose] public section
open Complex MeasureTheory Set Filter MathCollab.Density
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- The short detector cutoff retains precisely n<K, independently of the zero. -/
def shortDetectorCutoff (T : ℝ) : ℕ := ⌈T^(1/2:ℝ)*(Real.log T)^2⌉₊

/-- Quantitative truncation; no zeta or Weyl bound is used. -/
theorem short_norm_detector_tail_le {ρ : ℂ} {T : ℝ}
    (hT : 1 ≤ T) (hlog : 4 ≤ Real.log T) (hρ : 0 ≤ ρ.re) :
    ‖∑' n : ℕ, detectorTerm ρ (2*T^((1:ℝ)/100)) (T^(1/2:ℝ)) (n+shortDetectorCutoff T)‖ ≤
      4*T^(-2 : ℝ) := by
  have hTpos : 0 < T := by linarith
  have hX : 0 ≤ (2*T^((1:ℝ)/100)) := by positivity
  have hXle : (⌊(2*T^((1:ℝ)/100))⌋₊ : ℝ) ≤ 2*T := by
    apply (Nat.floor_le hX).trans
    have h := Real.rpow_le_rpow_of_exponent_le hT (by norm_num : (1/100 : ℝ) ≤ 1)
    simpa using mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
  have hk : T^(1/2:ℝ)*(Real.log T)^2 ≤ (shortDetectorCutoff T : ℝ) := Nat.le_ceil _
  have hexp : Real.exp (-(shortDetectorCutoff T : ℝ)/(T^(1/2:ℝ))) ≤ T^(-4 : ℝ) := by
    rw [Real.rpow_def_of_pos hTpos (-4)]
    apply Real.exp_le_exp.mpr
    have hq : (Real.log T)^2 ≤ (shortDetectorCutoff T : ℝ)/(T^(1/2:ℝ)) := (le_div_iff₀ (Real.rpow_pos_of_pos hTpos (1/2:ℝ))).2 (by nlinarith)
    rw [neg_div]
    nlinarith [mul_nonneg (show 0 ≤ Real.log T by linarith) (show 0 ≤ Real.log T-4 by linarith)]
  calc
    _ ≤ (⌊(2*T^((1:ℝ)/100))⌋₊ : ℝ)*Real.exp (-(shortDetectorCutoff T : ℝ)/(T^(1/2:ℝ)))*(1-Real.exp (-1/(T^(1/2:ℝ))))⁻¹ :=
      norm_detector_tail_le _ _ (Real.rpow_pos_of_pos hTpos _) hρ
    _ ≤ (2*T)*T^(-4 : ℝ)*(2*T) := by
      apply mul_le_mul _ ((detector_geometric_factor_le (Real.one_le_rpow hT (by norm_num : (0:ℝ) ≤ 1/2))).trans (mul_le_mul_of_nonneg_left (show T^(1/2:ℝ) ≤ T by simpa using Real.rpow_le_rpow_of_exponent_le hT (by norm_num : (1/2:ℝ) ≤ 1)) (by norm_num))) (le_of_lt (inv_pos.mpr (sub_pos.mpr (Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) (Real.rpow_pos_of_pos hTpos _)))))) (by positivity)
      exact mul_le_mul hXle hexp (by positivity) (by positivity)
    _ = 4*T^(-2 : ℝ) := by
      have he : T^(-4 : ℝ)*T^2 = T^(-2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hTpos]; norm_num
      nlinarith [he]

/-- One truncation threshold works for every rho with nonnegative real part. -/
theorem short_detector_tail_eventually_small {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ, 0 ≤ ρ.re →
      ‖∑' n : ℕ, detectorTerm ρ (2*T^((1:ℝ)/100)) (T^(1/2:ℝ)) (n+shortDetectorCutoff T)‖ < δ := by
  have ht := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 2 by norm_num)).const_mul 4
  simp only [mul_zero] at ht
  filter_upwards [eventually_ge_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4 : ℝ)),
    ht.eventually (gt_mem_nhds hδ)] with T hT hlog hsmall
  intro ρ hρ
  exact (short_norm_detector_tail_le hT hlog hρ).trans_lt hsmall

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.short_norm_detector_tail_le
#print axioms GuthMaynard.Improvement.short_detector_tail_eventually_small
