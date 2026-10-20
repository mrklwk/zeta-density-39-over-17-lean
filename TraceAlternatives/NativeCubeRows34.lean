module
public import TraceAlternatives.PhysicalCubeActualDensity
public import LaterPairs.NativeTTY3
public import LaterPairs.TTY4TargetParameters
public import LaterPairs.PhysicalTargetWindows
public import LaterPairs.NativeTTY4Prefix
public import RightSolidTailBudgets

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

/-- Exact pair-tail budgets for original row4; the prefix restriction in the
first consumer below concerns only its current short count. -/
theorem cube_row4_tail_budgets {σ : ℝ}
    (hl : 7873/9370 ≤ σ) (_hr : σ ≤ 2018/2375) :
    let a : ℝ := 1261710/(4342380*σ-1396527)
    1-6*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ) ∧
    1+(186317/351096:ℝ)/(258221/702192)-
      (4+(2+4*(186317/351096))/(258221/702192))*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ) := by
  dsimp only
  have hd : 0 < 4342380*σ-1396527 := by linarith
  norm_num only at *
  apply tail_budgets_of_fraction hd
  · linarith
  · norm_num
    nlinarith

theorem cube_row4_density_exponent {σ : ℝ} :
    3*(1261710/(4342380*σ-1396527))*(1-σ) =
      1261710*(1-σ)/(1447460*σ-465509) := by
  have hd : 4342380*σ-1396527 = 3*(1447460*σ-465509) := by ring
  calc
    _ = (3*1261710/(3*(1447460*σ-465509)))*(1-σ) := by rw [hd]; ring
    _ = (1261710/(1447460*σ-465509))*(1-σ) := by
      rw [mul_div_mul_left _ _ (by norm_num : (3:ℝ) ≠ 0)]
    _ = _ := div_mul_eq_mul_div _ _ _

end Montgomery.RationalMoment

namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density

/-- Full original closed row3, with actual symmetric zeta zeros and analytic
multiplicity at every real T>=2. All analytic inputs are proved internally. -/
theorem density_cube_row3 {σ ε : ℝ}
    (hlo : 163/198 ≤ σ) (hhi : σ ≤ 7873/9370) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(31544*(1-σ)/(35670*σ-11203)+ε) := by
  obtain ⟨_,hf,hs⟩ := tty4_full_target_tail_budgets hlo hhi
  simpa only [tty4_prefix_density_exponent] using
    density_of_pair_cube_window TaoTrudgianYang2025.exponentPair_BTTY4 (by norm_num)
      (physicalDetectorWindow_row3 hlo hhi) (cubeCountWindow_row3 hlo hhi) hf hs hε

/-- An explicitly delimited row4 prefix at its original exponent. It does
not substitute for the still requested full row4 conclusion. -/
theorem density_cube_row4_prefix {σ ε : ℝ}
    (hlo : 7873/9370 ≤ σ) (hhi : σ ≤ 745889/886700) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(1261710*(1-σ)/(1447460*σ-465509)+ε) := by
  have hTop : σ ≤ 2018/2375 := by linarith
  obtain ⟨hf,hs⟩ := cube_row4_tail_budgets hlo hTop
  simpa only [cube_row4_density_exponent] using
    density_of_pair_cube_window TaoTrudgianYang2025.exponentPair_BTTY3 (by norm_num)
      (physicalDetectorWindow_row4 hlo hTop) (cubeCountWindow_row4_prefix hlo hhi) hf hs hε

end Montgomery.RationalMoment.RightDetector.Physical
