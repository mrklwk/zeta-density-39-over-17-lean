module
public import ActualLongTailReduction

@[expose] public section

open Filter
open scoped Topology
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger

/-- The detector threshold eventually exceeds every fixed constant. In
particular, B>=4*pi makes the actual-tail integration threshold B/(4*pi)>=1.
This discharges the small-amplitude range condition for a future tail producer. -/
theorem criticalMeanThreshold_eventually_ge {C σ a δ : ℝ}
    (hC : 0 < C) (hw : QuadraticWindow σ a) (hsigma : 7/9 ≤ σ)
    (hδ : δ ≤ 1/8) (K : ℝ) :
    ∀ᶠ T : ℝ in atTop,K ≤ criticalMeanThreshold C σ a δ T := by
  let M : ℝ := max K 1
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hm := criticalMeanThreshold_eventually (C:=C*M) (mul_pos hC hM) hw hsigma hδ
  filter_upwards [hm,eventually_ge_atTop (2:ℝ)] with T hh hT
  have hTp : 0 < T := by linarith
  have hlog : Real.log T ≠ 0 := (Real.log_pos (by linarith : 1<T)).ne'
  have hX : Real.sqrt (detectorX δ T) ≠ 0 :=
    (Real.sqrt_pos.mpr (Real.rpow_pos_of_pos hTp δ)).ne'
  have he : criticalMeanThreshold C σ a δ T=M*criticalMeanThreshold (C*M) σ a δ T := by
    unfold criticalMeanThreshold
    field_simp [hC.ne',hM.ne',hlog,hX]
  calc
    K ≤ M := le_max_left _ _
    _ = M*1 := by ring
    _ ≤ M*criticalMeanThreshold (C*M) σ a δ T := mul_le_mul_of_nonneg_left hh.1 hM.le
    _ = _ := he.symm

end Montgomery.RationalMoment.RightDetector
