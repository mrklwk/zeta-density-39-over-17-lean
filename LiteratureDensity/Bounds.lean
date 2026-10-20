module
public import WrittenDensity.Common

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace Montgomery.LiteratureDensity
open MathCollab.Density Montgomery.WrittenDensity
/-- Exact published-source density conclusion, supplied by native project domination and strict actual zero-freeness. No new mathematics or claim to reprove the original published route. -/
theorem source_extra_baseline_tty_1 {σ ε : ℝ} (_hlo : (1/2) ≤ σ)
    (_hhi : σ ≤ (7/10)) (_hε : 0 < ε) :
    DensityBound σ ((-3 + (3 * σ)) / (-2 + σ)) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  by_cases hc0 : σ ≤ (9/13)
  ·
    have hl : (1/2) ≤ σ := by linarith
    have hh : σ ≤ (9/13) := by linarith
    apply density_weaken (GuthMaynard.Improvement.ingham_lower_density σ (by linarith) (by linarith) ε _hε)
    have hd1 : 0 < (2 + (-1 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 + (-1 * σ)) := by linarith
    have hA : (3:ℝ)/(2 + (-1 * σ)) ≤ 3/(2 + (-1 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ 0 := by
        calc
          0 ≤ 0 := by positivity
          _ = 0 := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    have hpd : ((-2 + σ):ℝ) ≠ 0 := by linarith
    calc
      _ = (3:ℝ)/(2 + (-1 * σ))*(1-σ) := by ring
      _ ≤ 3/(2 + (-1 * σ))*(1-σ) := hp
      _ = ((-3 + (3 * σ)) / (-2 + σ)) := by
        rw [div_mul_eq_mul_div]
        apply (div_eq_div_iff (ne_of_gt hd2) hpd).2
        ring
  have hl : (9/13) ≤ σ := by linarith
  have hh : σ ≤ (7/10) := by linarith
  apply density_weaken (Montgomery.Refined.refined_density_middle (by linarith) (by linarith) _hε)
  have hd1 : 0 < (3 + (7 * σ)) := by linarith
  have hd2 : (0:ℝ) < (2 + (-1 * σ)) := by linarith
  have hA : (18:ℝ)/(3 + (7 * σ)) ≤ 3/(2 + (-1 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (-27 + (39 * σ)) := by
      calc
        0 ≤ 39*(σ-(9/13)) := by positivity
        _ = (-27 + (39 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  have hpd : ((-2 + σ):ℝ) ≠ 0 := by linarith
  calc
    _ = (18:ℝ)/(3 + (7 * σ))*(1-σ) := by ring
    _ ≤ 3/(2 + (-1 * σ))*(1-σ) := hp
    _ = ((-3 + (3 * σ)) / (-2 + σ)) := by
      rw [div_mul_eq_mul_div]
      apply (div_eq_div_iff (ne_of_gt hd2) hpd).2
      ring
/-- Exact published-source density conclusion, supplied by native project domination and strict actual zero-freeness. No new mathematics or claim to reprove the original published route. -/
theorem source_extra_baseline_tty_2 {σ ε : ℝ} (_hlo : (7/10) ≤ σ)
    (_hhi : σ < (19/25)) (_hε : 0 < ε) :
    DensityBound σ ((15 + (-15 * σ)) / (3 + (5 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  by_cases hc0 : σ ≤ (12/17)
  ·
    have hl : (7/10) ≤ σ := by linarith
    have hh : σ ≤ (12/17) := by linarith
    apply density_weaken (Montgomery.Refined.refined_density_middle (by linarith) (by linarith) _hε)
    have hd1 : 0 < (3 + (7 * σ)) := by linarith
    have hd2 : (0:ℝ) < (3 + (5 * σ)) := by linarith
    have hA : (18:ℝ)/(3 + (7 * σ)) ≤ 15/(3 + (5 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-9 + (15 * σ)) := by
        calc
          0 ≤ 255*((12/17)-σ)+270*(σ-(7/10)) := by positivity
          _ = (-9 + (15 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc1 : σ ≤ (5/7)
  ·
    have hl : (12/17) ≤ σ := by linarith
    have hh : σ ≤ (5/7) := by linarith
    apply density_weaken (Montgomery.RationalMoment.two_term_density_first (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-3 + (8 * σ)) := by linarith
    have hd2 : (0:ℝ) < (3 + (5 * σ)) := by linarith
    have hA : (6:ℝ)/(-3 + (8 * σ)) ≤ 15/(3 + (5 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-63 + (90 * σ)) := by
        calc
          0 ≤ 63*((5/7)-σ)+153*(σ-(12/17)) := by positivity
          _ = (-63 + (90 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc2 : σ ≤ (113/153)
  ·
    have hl : (5/7) ≤ σ := by linarith
    have hh : σ ≤ (113/153) := by linarith
    apply density_weaken (Montgomery.RationalMoment.adjacent_density_second (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1 + (9 * σ)) := by linarith
    have hd2 : (0:ℝ) < (3 + (5 * σ)) := by linarith
    have hA : (12:ℝ)/(-1 + (9 * σ)) ≤ 15/(3 + (5 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-51 + (75 * σ)) := by
        calc
          0 ≤ (1377/13)*((113/153)-σ)+(2352/13)*(σ-(5/7)) := by positivity
          _ = (-51 + (75 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc3 : σ ≤ (3/4)
  ·
    have hl : (113/153) ≤ σ := by linarith
    have hh : σ ≤ (3/4) := by linarith
    apply density_weaken (Montgomery.RationalMoment.third_density_segment (by linarith) (by linarith) _hε)
    have hd1 : 0 < (7 + (153 * σ)) := by linarith
    have hd2 : (0:ℝ) < (3 + (5 * σ)) := by linarith
    have hA : (255:ℝ)/(7 + (153 * σ)) ≤ 15/(3 + (5 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-660 + (1020 * σ)) := by
        calc
          0 ≤ 8160*((3/4)-σ)+9180*(σ-(113/153)) := by positivity
          _ = (-660 + (1020 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  have hl : (3/4) ≤ σ := by linarith
  have hh : σ ≤ (19/25) := by linarith
  apply density_weaken (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) _hε)
  have hd1 : 0 < (2 * σ) := by linarith
  have hd2 : (0:ℝ) < (3 + (5 * σ)) := by linarith
  have hA : (3:ℝ)/(2 * σ) ≤ 15/(3 + (5 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (-9 + (15 * σ)) := by
      calc
        0 ≤ 225*((19/25)-σ)+240*(σ-(3/4)) := by positivity
        _ = (-9 + (15 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact published-source density conclusion, supplied by native project domination and strict actual zero-freeness. No new mathematics or claim to reprove the original published route. -/
theorem source_extra_baseline_tty_3 {σ ε : ℝ} (_hlo : (19/25) ≤ σ)
    (_hhi : σ < (127/167)) (_hε : 0 < ε) :
    DensityBound σ ((9 + (-9 * σ)) / (-2 + (8 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  have hl : (19/25) ≤ σ := by linarith
  have hh : σ ≤ (127/167) := by linarith
  apply density_weaken (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) _hε)
  have hd1 : 0 < (2 * σ) := by linarith
  have hd2 : (0:ℝ) < (-2 + (8 * σ)) := by linarith
  have hA : (3:ℝ)/(2 * σ) ≤ 9/(-2 + (8 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (6 + (-6 * σ)) := by
      calc
        0 ≤ 3006*((127/167)-σ)+3000*(σ-(19/25)) := by positivity
        _ = (6 + (-6 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact published-source density conclusion, supplied by native project domination and strict actual zero-freeness. No new mathematics or claim to reprove the original published route. -/
theorem source_extra_baseline_tty_4 {σ ε : ℝ} (_hlo : (127/167) ≤ σ)
    (_hhi : σ < (13/17)) (_hε : 0 < ε) :
    DensityBound σ ((15 + (-15 * σ)) / (-3 + (13 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  have hl : (127/167) ≤ σ := by linarith
  have hh : σ ≤ (13/17) := by linarith
  apply density_weaken (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) _hε)
  have hd1 : 0 < (2 * σ) := by linarith
  have hd2 : (0:ℝ) < (-3 + (13 * σ)) := by linarith
  have hA : (3:ℝ)/(2 * σ) ≤ 15/(-3 + (13 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (9 + (-9 * σ)) := by
      calc
        0 ≤ 510*((13/17)-σ)+501*(σ-(127/167)) := by positivity
        _ = (9 + (-9 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact published-source density conclusion, supplied by native project domination and strict actual zero-freeness. No new mathematics or claim to reprove the original published route. -/
theorem source_extra_baseline_tty_5 {σ ε : ℝ} (_hlo : (13/17) ≤ σ)
    (_hhi : σ < (17/22)) (_hε : 0 < ε) :
    DensityBound σ ((6 + (-6 * σ)) / (-1 + (5 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  have hl : (13/17) ≤ σ := by linarith
  have hh : σ ≤ (17/22) := by linarith
  apply density_weaken (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) _hε)
  have hd1 : 0 < (2 * σ) := by linarith
  have hd2 : (0:ℝ) < (-1 + (5 * σ)) := by linarith
  have hA : (3:ℝ)/(2 * σ) ≤ 6/(-1 + (5 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (3 + (-3 * σ)) := by
      calc
        0 ≤ 88*((17/22)-σ)+85*(σ-(13/17)) := by positivity
        _ = (3 + (-3 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact published-source density conclusion, supplied by native project domination and strict actual zero-freeness. No new mathematics or claim to reprove the original published route. -/
theorem source_extra_baseline_tty_6 {σ ε : ℝ} (_hlo : (17/22) ≤ σ)
    (_hhi : σ < (41/53)) (_hε : 0 < ε) :
    DensityBound σ ((2 + (-2 * σ)) / (-6 + (9 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  have hl : (17/22) ≤ σ := by linarith
  have hh : σ ≤ (41/53) := by linarith
  apply density_weaken (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) _hε)
  have hd1 : 0 < (2 * σ) := by linarith
  have hd2 : (0:ℝ) < (-6 + (9 * σ)) := by linarith
  have hA : (3:ℝ)/(2 * σ) ≤ 2/(-6 + (9 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (18 + (-23 * σ)) := by
      calc
        0 ≤ 265*((41/53)-σ)+242*(σ-(17/22)) := by positivity
        _ = (18 + (-23 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact published-source density conclusion, supplied by native project domination and strict actual zero-freeness. No new mathematics or claim to reprove the original published route. -/
theorem source_extra_baseline_tty_7 {σ ε : ℝ} (_hlo : (41/53) ≤ σ)
    (_hhi : σ < (7/9)) (_hε : 0 < ε) :
    DensityBound σ ((9 + (-9 * σ)) / (-1 + (7 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  have hl : (41/53) ≤ σ := by linarith
  have hh : σ ≤ (7/9) := by linarith
  apply density_weaken (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) _hε)
  have hd1 : 0 < (2 * σ) := by linarith
  have hd2 : (0:ℝ) < (-1 + (7 * σ)) := by linarith
  have hA : (3:ℝ)/(2 * σ) ≤ 9/(-1 + (7 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (3 + (-3 * σ)) := by
      calc
        0 ≤ 162*((7/9)-σ)+159*(σ-(41/53)) := by positivity
        _ = (3 + (-3 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact published-source density conclusion, supplied by native project domination and strict actual zero-freeness. No new mathematics or claim to reprove the original published route. -/
theorem source_extra_baseline_tty_8 {σ ε : ℝ} (_hlo : (7/9) ≤ σ)
    (_hhi : σ < (1867/2347)) (_hε : 0 < ε) :
    DensityBound σ ((9 + (-9 * σ)) / (-8 + (16 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  by_cases hc0 : σ ≤ (29359/37574)
  ·
    have hl : (7/9) ≤ σ := by linarith
    have hh : σ ≤ (29359/37574) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_first (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-7 + (11 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-8 + (16 * σ)) := by linarith
    have hA : (3:ℝ)/(-7 + (11 * σ)) ≤ 9/(-8 + (16 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-39 + (51 * σ)) := by
        calc
          0 ≤ (225444/1213)*((29359/37574)-σ)+(287307/1213)*(σ-(7/9)) := by positivity
          _ = (-39 + (51 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc1 : σ ≤ (1015/1294)
  ·
    have hl : (29359/37574) ≤ σ := by linarith
    have hh : σ ≤ (1015/1294) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_second (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1283 + (4870 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-8 + (16 * σ)) := by linarith
    have hA : (4744:ℝ)/(-1283 + (4870 * σ)) ≤ 9/(-8 + (16 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (26405 + (-32074 * σ)) := by
        calc
          0 ≤ (13769454/31)*((1015/1294)-σ)+(12775160/31)*(σ-(29359/37574)) := by positivity
          _ = (26405 + (-32074 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc2 : σ ≤ (353/447)
  ·
    have hl : (1015/1294) ≤ σ := by linarith
    have hh : σ ≤ (353/447) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_third (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1693 + (6354 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-8 + (16 * σ)) := by linarith
    have hA : (6154:ℝ)/(-1693 + (6354 * σ)) ≤ 9/(-8 + (16 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (33995 + (-41278 * σ)) := by
        calc
          0 ≤ 303960*((353/447)-σ)+262682*(σ-(1015/1294)) := by positivity
          _ = (33995 + (-41278 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  have hl : (353/447) ≤ σ := by linarith
  have hh : σ ≤ (1867/2347) := by linarith
  apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_fourth (by linarith) (by linarith) _hε)
  have hd1 : 0 < (-1065 + (3936 * σ)) := by linarith
  have hd2 : (0:ℝ) < (-8 + (16 * σ)) := by linarith
  have hA : (3782:ℝ)/(-1065 + (3936 * σ)) ≤ 9/(-8 + (16 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (20671 + (-25088 * σ)) := by
      calc
        0 ≤ (900949931/6058)*((1867/2347)-σ)+(748966827/6058)*(σ-(353/447)) := by positivity
        _ = (20671 + (-25088 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact published-source density conclusion, supplied by native project domination and strict actual zero-freeness. No new mathematics or claim to reprove the original published route. -/
theorem source_extra_baseline_tty_9 {σ ε : ℝ} (_hlo : (1867/2347) ≤ σ)
    (_hhi : σ < (7/8)) (_hε : 0 < ε) :
    DensityBound σ ((3 + (-3 * σ)) / (2 * σ)) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  by_cases hc0 : σ ≤ (467/586)
  ·
    have hl : (1867/2347) ≤ σ := by linarith
    have hh : σ ≤ (467/586) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_fourth (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1065 + (3936 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 * σ) := by linarith
    have hA : (3782:ℝ)/(-1065 + (3936 * σ)) ≤ 3/(2 * σ) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-3195 + (4244 * σ)) := by
        calc
          0 ≤ (248981438/1987)*((467/586)-σ)+(257414266/1987)*(σ-(1867/2347)) := by positivity
          _ = (-3195 + (4244 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc1 : σ ≤ (4/5)
  ·
    have hl : (467/586) ≤ σ := by linarith
    have hh : σ ≤ (4/5) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_fifth (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-631 + (2282 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 * σ) := by linarith
    have hA : (2168:ℝ)/(-631 + (2282 * σ)) ≤ 3/(2 * σ) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-1893 + (2510 * σ)) := by
        calc
          0 ≤ (314360/9)*((4/5)-σ)+(336950/9)*(σ-(467/586)) := by positivity
          _ = (-1893 + (2510 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc2 : σ ≤ (289/358)
  ·
    have hl : (4/5) ≤ σ := by linarith
    have hh : σ ≤ (289/358) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_dashed_first (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-631 + (2282 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 * σ) := by linarith
    have hA : (2168:ℝ)/(-631 + (2282 * σ)) ≤ 3/(2 * σ) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-1893 + (2510 * σ)) := by
        calc
          0 ≤ (205850/13)*((289/358)-σ)+(238480/13)*(σ-(4/5)) := by positivity
          _ = (-1893 + (2510 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc3 : σ ≤ (163/198)
  ·
    have hl : (289/358) ≤ σ := by linarith
    have hh : σ ≤ (163/198) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_dashed_second (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-173 + (606 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 * σ) := by linarith
    have hA : (566:ℝ)/(-173 + (606 * σ)) ≤ 3/(2 * σ) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-519 + (686 * σ)) := by
        calc
          0 ≤ 2178*((163/198)-σ)+2864*(σ-(289/358)) := by positivity
          _ = (-519 + (686 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc4 : σ ≤ (7873/9370)
  ·
    have hl : (163/198) ≤ σ := by linarith
    have hh : σ ≤ (7873/9370) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_cube_row3 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-11203 + (35670 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 * σ) := by linarith
    have hA : (31544:ℝ)/(-11203 + (35670 * σ)) ≤ 3/(2 * σ) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-33609 + (43922 * σ)) := by
        calc
          0 ≤ 149920*((7873/9370)-σ)+193842*(σ-(163/198)) := by positivity
          _ = (-33609 + (43922 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc5 : σ ≤ (2018/2375)
  ·
    have hl : (7873/9370) ≤ σ := by linarith
    have hh : σ ≤ (2018/2375) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_universal_row4 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-465509 + (1447460 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 * σ) := by linarith
    have hA : (1261710:ℝ)/(-465509 + (1447460 * σ)) ≤ 3/(2 * σ) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-1396527 + (1818960 * σ)) := by
        calc
          0 ≤ 13950750*((2018/2375)-σ)+15769710*(σ-(7873/9370)) := by positivity
          _ = (-1396527 + (1818960 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc6 : σ ≤ (1959705/2298302)
  ·
    have hl : (2018/2375) ≤ σ := by linarith
    have hh : σ ≤ (1959705/2298302) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_universal_row5 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1215 + (3616 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 * σ) := by linarith
    have hA : (3066:ℝ)/(-1215 + (3616 * σ)) ≤ 3/(2 * σ) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-3645 + (4716 * σ)) := by
        calc
          0 ≤ (3868042266/31949)*((1959705/2298302)-σ)+(4018713750/31949)*(σ-(2018/2375)) := by positivity
          _ = (-3645 + (4716 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc7 : σ ≤ (6482825/7570038)
  ·
    have hl : (1959705/2298302) ≤ σ := by linarith
    have hh : σ ≤ (6482825/7570038) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row6 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-257415 + (729216 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 * σ) := by linarith
    have hA : (597962:ℝ)/(-257415 + (729216 * σ)) ≤ 3/(2 * σ) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-772245 + (991724 * σ)) := by
        calc
          0 ≤ (213486426657/10778)*((6482825/7570038)-σ)+(224175227929/10778)*(σ-(1959705/2298302)) := by positivity
          _ = (-772245 + (991724 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc8 : σ ≤ (2905/3354)
  ·
    have hl : (6482825/7570038) ≤ σ := by linarith
    have hh : σ ≤ (2905/3354) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row7 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-7623595 + (20732766 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 * σ) := by linarith
    have hA : (16504356:ℝ)/(-7623595 + (20732766 * σ)) ≤ 3/(2 * σ) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-22870785 + (29189586 * σ)) := by
        calc
          0 ≤ 218098322*((2905/3354)-σ)+247287908*(σ-(6482825/7570038)) := by positivity
          _ = (-22870785 + (29189586 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  have hl : (2905/3354) ≤ σ := by linarith
  have hh : σ ≤ (7/8) := by linarith
  apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row8 (by linarith) (by linarith) _hε)
  have hd1 : 0 < (-1015 + (2742 * σ)) := by linarith
  have hd2 : (0:ℝ) < (2 * σ) := by linarith
  have hA : (2172:ℝ)/(-1015 + (2742 * σ)) ≤ 3/(2 * σ) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (-3045 + (3882 * σ)) := by
      calc
        0 ≤ (608160/17)*((7/8)-σ)+(674154/17)*(σ-(2905/3354)) := by positivity
        _ = (-3045 + (3882 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact published-source density conclusion, supplied by native project domination and strict actual zero-freeness. No new mathematics or claim to reprove the original published route. -/
theorem source_extra_baseline_kerr6 {σ ε : ℝ} (_hlo : (23/29) ≤ σ)
    (_hhi : σ ≤ 1) (_hε : 0 < ε) :
    DensityBound σ ((3 + (-3 * σ)) / (2 * σ)) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  by_cases hc0 : σ ≤ (467/586)
  ·
    have hl : (23/29) ≤ σ := by linarith
    have hh : σ ≤ (467/586) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_fourth (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1065 + (3936 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 * σ) := by linarith
    have hA : (3782:ℝ)/(-1065 + (3936 * σ)) ≤ 3/(2 * σ) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-3195 + (4244 * σ)) := by
        calc
          0 ≤ (2904802/65)*((467/586)-σ)+(3180662/65)*(σ-(23/29)) := by positivity
          _ = (-3195 + (4244 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc1 : σ ≤ (4/5)
  ·
    have hl : (467/586) ≤ σ := by linarith
    have hh : σ ≤ (4/5) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_fifth (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-631 + (2282 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 * σ) := by linarith
    have hA : (2168:ℝ)/(-631 + (2282 * σ)) ≤ 3/(2 * σ) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-1893 + (2510 * σ)) := by
        calc
          0 ≤ (314360/9)*((4/5)-σ)+(336950/9)*(σ-(467/586)) := by positivity
          _ = (-1893 + (2510 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc2 : σ ≤ (289/358)
  ·
    have hl : (4/5) ≤ σ := by linarith
    have hh : σ ≤ (289/358) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_dashed_first (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-631 + (2282 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 * σ) := by linarith
    have hA : (2168:ℝ)/(-631 + (2282 * σ)) ≤ 3/(2 * σ) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-1893 + (2510 * σ)) := by
        calc
          0 ≤ (205850/13)*((289/358)-σ)+(238480/13)*(σ-(4/5)) := by positivity
          _ = (-1893 + (2510 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc3 : σ ≤ (163/198)
  ·
    have hl : (289/358) ≤ σ := by linarith
    have hh : σ ≤ (163/198) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_dashed_second (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-173 + (606 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 * σ) := by linarith
    have hA : (566:ℝ)/(-173 + (606 * σ)) ≤ 3/(2 * σ) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-519 + (686 * σ)) := by
        calc
          0 ≤ 2178*((163/198)-σ)+2864*(σ-(289/358)) := by positivity
          _ = (-519 + (686 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc4 : σ ≤ (7873/9370)
  ·
    have hl : (163/198) ≤ σ := by linarith
    have hh : σ ≤ (7873/9370) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_cube_row3 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-11203 + (35670 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 * σ) := by linarith
    have hA : (31544:ℝ)/(-11203 + (35670 * σ)) ≤ 3/(2 * σ) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-33609 + (43922 * σ)) := by
        calc
          0 ≤ 149920*((7873/9370)-σ)+193842*(σ-(163/198)) := by positivity
          _ = (-33609 + (43922 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc5 : σ ≤ (2018/2375)
  ·
    have hl : (7873/9370) ≤ σ := by linarith
    have hh : σ ≤ (2018/2375) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_universal_row4 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-465509 + (1447460 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 * σ) := by linarith
    have hA : (1261710:ℝ)/(-465509 + (1447460 * σ)) ≤ 3/(2 * σ) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-1396527 + (1818960 * σ)) := by
        calc
          0 ≤ 13950750*((2018/2375)-σ)+15769710*(σ-(7873/9370)) := by positivity
          _ = (-1396527 + (1818960 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc6 : σ ≤ (1959705/2298302)
  ·
    have hl : (2018/2375) ≤ σ := by linarith
    have hh : σ ≤ (1959705/2298302) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_universal_row5 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1215 + (3616 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 * σ) := by linarith
    have hA : (3066:ℝ)/(-1215 + (3616 * σ)) ≤ 3/(2 * σ) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-3645 + (4716 * σ)) := by
        calc
          0 ≤ (3868042266/31949)*((1959705/2298302)-σ)+(4018713750/31949)*(σ-(2018/2375)) := by positivity
          _ = (-3645 + (4716 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc7 : σ ≤ (6482825/7570038)
  ·
    have hl : (1959705/2298302) ≤ σ := by linarith
    have hh : σ ≤ (6482825/7570038) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row6 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-257415 + (729216 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 * σ) := by linarith
    have hA : (597962:ℝ)/(-257415 + (729216 * σ)) ≤ 3/(2 * σ) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-772245 + (991724 * σ)) := by
        calc
          0 ≤ (213486426657/10778)*((6482825/7570038)-σ)+(224175227929/10778)*(σ-(1959705/2298302)) := by positivity
          _ = (-772245 + (991724 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc8 : σ ≤ (2905/3354)
  ·
    have hl : (6482825/7570038) ≤ σ := by linarith
    have hh : σ ≤ (2905/3354) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row7 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-7623595 + (20732766 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 * σ) := by linarith
    have hA : (16504356:ℝ)/(-7623595 + (20732766 * σ)) ≤ 3/(2 * σ) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-22870785 + (29189586 * σ)) := by
        calc
          0 ≤ 218098322*((2905/3354)-σ)+247287908*(σ-(6482825/7570038)) := by positivity
          _ = (-22870785 + (29189586 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  have hl : (2905/3354) ≤ σ := by linarith
  have hh : σ ≤ (7/8) := by linarith
  apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row8 (by linarith) (by linarith) _hε)
  have hd1 : 0 < (-1015 + (2742 * σ)) := by linarith
  have hd2 : (0:ℝ) < (2 * σ) := by linarith
  have hA : (2172:ℝ)/(-1015 + (2742 * σ)) ≤ 3/(2 * σ) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (-3045 + (3882 * σ)) := by
      calc
        0 ≤ (608160/17)*((7/8)-σ)+(674154/17)*(σ-(2905/3354)) := by positivity
        _ = (-3045 + (3882 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact published-source density conclusion, supplied by native project domination and strict actual zero-freeness. No new mathematics or claim to reprove the original published route. -/
theorem source_extra_baseline_kerr7_first {σ ε : ℝ} (_hlo : (127/168) ≤ σ)
    (_hhi : σ ≤ (23/30)) (_hε : 0 < ε) :
    DensityBound σ ((36 + (-36 * σ)) / (-89 + (138 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  have hl : (127/168) ≤ σ := by linarith
  have hh : σ ≤ (23/30) := by linarith
  apply density_weaken (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) _hε)
  have hd1 : 0 < (2 * σ) := by linarith
  have hd2 : (0:ℝ) < (-89 + (138 * σ)) := by linarith
  have hA : (3:ℝ)/(2 * σ) ≤ 36/(-89 + (138 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (267 + (-342 * σ)) := by
      calc
        0 ≤ 790*((23/30)-σ)+448*(σ-(127/168)) := by positivity
        _ = (267 + (-342 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact published-source density conclusion, supplied by native project domination and strict actual zero-freeness. No new mathematics or claim to reprove the original published route. -/
theorem source_extra_baseline_kerr7_second {σ ε : ℝ} (_hlo : (23/30) ≤ σ)
    (_hhi : σ ≤ (107/138)) (_hε : 0 < ε) :
    DensityBound σ ((-79 + (114 * σ)) / (-89 + (138 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  have hl : (23/30) ≤ σ := by linarith
  have hh : σ ≤ (107/138) := by linarith
  apply density_weaken (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) _hε)
  have hd1 : 0 < (2 * σ) := by linarith
  have hden : 0 ≤ ((-89000001/1000000) + (-138 * (σ)^2) + (227 * σ)) := by
    calc
      0 ≤ (2073679471/40000)*((107/138)-σ)^2+(2109099471/20000)*(σ-(23/30))*((107/138)-σ)+(2138999471/40000)*(σ-(23/30))^2 := by positivity
      _ = ((-89000001/1000000) + (-138 * (σ)^2) + (227 * σ)) := by ring
  have hd2 : (0:ℝ) < (-89 + (-138 * (σ)^2) + (227 * σ)) := by linarith
  have hA : (3:ℝ)/(2 * σ) ≤ (-79 + (114 * σ))/(-89 + (-138 * (σ)^2) + (227 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (267 + (-839 * σ) + (642 * (σ)^2)) := by
      calc
        0 ≤ 14812*((107/138)-σ)^2+46345*(σ-(23/30))*((107/138)-σ)+32175*(σ-(23/30))^2 := by positivity
        _ = (267 + (-839 * σ) + (642 * (σ)^2)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  have hpd : ((-89 + (138 * σ)):ℝ) ≠ 0 := by linarith
  calc
    _ = (3:ℝ)/(2 * σ)*(1-σ) := by ring
    _ ≤ (-79 + (114 * σ))/(-89 + (-138 * (σ)^2) + (227 * σ))*(1-σ) := hp
    _ = ((-79 + (114 * σ)) / (-89 + (138 * σ))) := by
      rw [div_mul_eq_mul_div]
      apply (div_eq_div_iff (ne_of_gt hd2) hpd).2
      ring
/-- Exact published-source density conclusion, supplied by native project domination and strict actual zero-freeness. No new mathematics or claim to reprove the original published route. -/
theorem source_extra_baseline_full_hb {σ ε : ℝ} (_hlo : (7/10) < σ)
    (_hhi : σ ≤ 1) (_hε : 0 < ε) :
    DensityBound σ ((3 + (-3 * σ)) / (-7 + (10 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  by_cases hc0 : σ ≤ (12/17)
  ·
    have hl : (7/10) ≤ σ := by linarith
    have hh : σ ≤ (12/17) := by linarith
    apply density_weaken (Montgomery.Refined.refined_density_middle (by linarith) (by linarith) _hε)
    have hd1 : 0 < (3 + (7 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (18:ℝ)/(3 + (7 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (135 + (-159 * σ)) := by
        calc
          0 ≤ 4029*((12/17)-σ)+3870*(σ-(7/10)) := by positivity
          _ = (135 + (-159 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc1 : σ ≤ (5/7)
  ·
    have hl : (12/17) ≤ σ := by linarith
    have hh : σ ≤ (5/7) := by linarith
    apply density_weaken (Montgomery.RationalMoment.two_term_density_first (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-3 + (8 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (6:ℝ)/(-3 + (8 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (33 + (-36 * σ)) := by
        calc
          0 ≤ 903*((5/7)-σ)+867*(σ-(12/17)) := by positivity
          _ = (33 + (-36 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc2 : σ ≤ (113/153)
  ·
    have hl : (5/7) ≤ σ := by linarith
    have hh : σ ≤ (113/153) := by linarith
    apply density_weaken (Montgomery.RationalMoment.adjacent_density_second (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1 + (9 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (12:ℝ)/(-1 + (9 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (81 + (-93 * σ)) := by
        calc
          0 ≤ (7803/13)*((113/153)-σ)+(6594/13)*(σ-(5/7)) := by positivity
          _ = (81 + (-93 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc3 : σ ≤ (3/4)
  ·
    have hl : (113/153) ≤ σ := by linarith
    have hh : σ ≤ (3/4) := by linarith
    apply density_weaken (Montgomery.RationalMoment.third_density_segment (by linarith) (by linarith) _hε)
    have hd1 : 0 < (7 + (153 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (255:ℝ)/(7 + (153 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (1806 + (-2091 * σ)) := by
        calc
          0 ≤ (160140/7)*((3/4)-σ)+(145503/7)*(σ-(113/153)) := by positivity
          _ = (1806 + (-2091 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc4 : σ ≤ (7/9)
  ·
    have hl : (3/4) ≤ σ := by linarith
    have hh : σ ≤ (7/9) := by linarith
    apply density_weaken (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) _hε)
    have hd1 : 0 < (2 * σ) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (3:ℝ)/(2 * σ) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (21 + (-24 * σ)) := by
        calc
          0 ≤ 108*((7/9)-σ)+84*(σ-(3/4)) := by positivity
          _ = (21 + (-24 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc5 : σ ≤ (29359/37574)
  ·
    have hl : (7/9) ≤ σ := by linarith
    have hh : σ ≤ (29359/37574) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_first (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-7 + (11 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (3:ℝ)/(-7 + (11 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (3 * σ) := by
        calc
          0 ≤ (789054/1213)*((29359/37574)-σ)+(792693/1213)*(σ-(7/9)) := by positivity
          _ = (3 * σ) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc6 : σ ≤ (1015/1294)
  ·
    have hl : (29359/37574) ≤ σ := by linarith
    have hh : σ ≤ (1015/1294) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_second (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1283 + (4870 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (4744:ℝ)/(-1283 + (4870 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (29359 + (-32830 * σ)) := by
        calc
          0 ≤ (37990546/31)*((1015/1294)-σ)+(36972816/31)*(σ-(29359/37574)) := by positivity
          _ = (29359 + (-32830 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc7 : σ ≤ (353/447)
  ·
    have hl : (1015/1294) ≤ σ := by linarith
    have hh : σ ≤ (353/447) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_third (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1693 + (6354 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (6154:ℝ)/(-1693 + (6354 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (37999 + (-42478 * σ)) := by
        calc
          0 ≤ 879696*((353/447)-σ)+837218*(σ-(1015/1294)) := by positivity
          _ = (37999 + (-42478 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc8 : σ ≤ (467/586)
  ·
    have hl : (353/447) ≤ σ := by linarith
    have hh : σ ≤ (467/586) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_fourth (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1065 + (3936 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (3782:ℝ)/(-1065 + (3936 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (23279 + (-26012 * σ)) := by
        calc
          0 ≤ 379142*((467/586)-σ)+353130*(σ-(353/447)) := by positivity
          _ = (23279 + (-26012 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc9 : σ ≤ (4/5)
  ·
    have hl : (467/586) ≤ σ := by linarith
    have hh : σ ≤ (4/5) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_fifth (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-631 + (2282 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (2168:ℝ)/(-631 + (2282 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (13283 + (-14834 * σ)) := by
        calc
          0 ≤ (4281800/9)*((4/5)-σ)+(4148294/9)*(σ-(467/586)) := by positivity
          _ = (13283 + (-14834 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc10 : σ ≤ (289/358)
  ·
    have hl : (4/5) ≤ σ := by linarith
    have hh : σ ≤ (289/358) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_dashed_first (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-631 + (2282 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (2168:ℝ)/(-631 + (2282 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (13283 + (-14834 * σ)) := by
        calc
          0 ≤ (2534282/13)*((289/358)-σ)+(2341440/13)*(σ-(4/5)) := by positivity
          _ = (13283 + (-14834 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc11 : σ ≤ (163/198)
  ·
    have hl : (289/358) ≤ σ := by linarith
    have hh : σ ≤ (163/198) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_dashed_second (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-173 + (606 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (566:ℝ)/(-173 + (606 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (3443 + (-3842 * σ)) := by
        calc
          0 ≤ 21384*((163/198)-σ)+17542*(σ-(289/358)) := by positivity
          _ = (3443 + (-3842 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc12 : σ ≤ (7873/9370)
  ·
    have hl : (163/198) ≤ σ := by linarith
    have hh : σ ≤ (7873/9370) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_cube_row3 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-11203 + (35670 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (31544:ℝ)/(-11203 + (35670 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (187199 + (-208430 * σ)) := by
        calc
          0 ≤ 918260*((7873/9370)-σ)+709830*(σ-(163/198)) := by positivity
          _ = (187199 + (-208430 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc13 : σ ≤ (2018/2375)
  ·
    have hl : (7873/9370) ≤ σ := by linarith
    have hh : σ ≤ (2018/2375) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_universal_row4 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-465509 + (1447460 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (1261710:ℝ)/(-465509 + (1447460 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (7435443 + (-8274720 * σ)) := by
        calc
          0 ≤ 51086250*((2018/2375)-σ)+42811530*(σ-(7873/9370)) := by positivity
          _ = (7435443 + (-8274720 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc14 : σ ≤ (1959705/2298302)
  ·
    have hl : (2018/2375) ≤ σ := by linarith
    have hh : σ ≤ (1959705/2298302) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_universal_row5 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1215 + (3616 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (3066:ℝ)/(-1215 + (3616 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (17817 + (-19812 * σ)) := by
        calc
          0 ≤ (10500941838/31949)*((1959705/2298302)-σ)+(9867968250/31949)*(σ-(2018/2375)) := by positivity
          _ = (17817 + (-19812 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc15 : σ ≤ (6482825/7570038)
  ·
    have hl : (1959705/2298302) ≤ σ := by linarith
    have hh : σ ≤ (6482825/7570038) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row6 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-257415 + (729216 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (597962:ℝ)/(-257415 + (729216 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (3413489 + (-3791972 * σ)) := by
        calc
          0 ≤ (2621084022291/53890)*((6482825/7570038)-σ)+(2416734651211/53890)*(σ-(1959705/2298302)) := by positivity
          _ = (3413489 + (-3791972 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc16 : σ ≤ (2905/3354)
  ·
    have hl : (6482825/7570038) ≤ σ := by linarith
    have hh : σ ≤ (2905/3354) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row7 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-7623595 + (20732766 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (16504356:ℝ)/(-7623595 + (20732766 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (92659707 + (-102845262 * σ)) := by
        calc
          0 ≤ (2351222198/5)*((2905/3354)-σ)+(1836995888/5)*(σ-(6482825/7570038)) := by positivity
          _ = (92659707 + (-102845262 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  have hl : (2905/3354) ≤ σ := by linarith
  have hh : σ ≤ (7/8) := by linarith
  apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row8 (by linarith) (by linarith) _hε)
  have hd1 : 0 < (-1015 + (2742 * σ)) := by linarith
  have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
  have hA : (2172:ℝ)/(-1015 + (2742 * σ)) ≤ 3/(-7 + (10 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (12159 + (-13494 * σ)) := by
      calc
        0 ≤ (903552/17)*((7/8)-σ)+(674154/17)*(σ-(2905/3354)) := by positivity
        _ = (12159 + (-13494 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact published-source density conclusion, supplied by native project domination and strict actual zero-freeness. No new mathematics or claim to reprove the original published route. -/
theorem source_tty47_full {σ ε : ℝ} (_hlo : (1/2) ≤ σ)
    (_hhi : σ ≤ 1) (_hε : 0 < ε) :
    DensityBound σ ((-3 + (3 * σ)) / (-2 + σ)) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  by_cases hc0 : σ ≤ (9/13)
  ·
    have hl : (1/2) ≤ σ := by linarith
    have hh : σ ≤ (9/13) := by linarith
    apply density_weaken (GuthMaynard.Improvement.ingham_lower_density σ (by linarith) (by linarith) ε _hε)
    have hd1 : 0 < (2 + (-1 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 + (-1 * σ)) := by linarith
    have hA : (3:ℝ)/(2 + (-1 * σ)) ≤ 3/(2 + (-1 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ 0 := by
        calc
          0 ≤ 0 := by positivity
          _ = 0 := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    have hpd : ((-2 + σ):ℝ) ≠ 0 := by linarith
    calc
      _ = (3:ℝ)/(2 + (-1 * σ))*(1-σ) := by ring
      _ ≤ 3/(2 + (-1 * σ))*(1-σ) := hp
      _ = ((-3 + (3 * σ)) / (-2 + σ)) := by
        rw [div_mul_eq_mul_div]
        apply (div_eq_div_iff (ne_of_gt hd2) hpd).2
        ring
  by_cases hc1 : σ ≤ (12/17)
  ·
    have hl : (9/13) ≤ σ := by linarith
    have hh : σ ≤ (12/17) := by linarith
    apply density_weaken (Montgomery.Refined.refined_density_middle (by linarith) (by linarith) _hε)
    have hd1 : 0 < (3 + (7 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 + (-1 * σ)) := by linarith
    have hA : (18:ℝ)/(3 + (7 * σ)) ≤ 3/(2 + (-1 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-27 + (39 * σ)) := by
        calc
          0 ≤ 39*(σ-(9/13)) := by positivity
          _ = (-27 + (39 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    have hpd : ((-2 + σ):ℝ) ≠ 0 := by linarith
    calc
      _ = (18:ℝ)/(3 + (7 * σ))*(1-σ) := by ring
      _ ≤ 3/(2 + (-1 * σ))*(1-σ) := hp
      _ = ((-3 + (3 * σ)) / (-2 + σ)) := by
        rw [div_mul_eq_mul_div]
        apply (div_eq_div_iff (ne_of_gt hd2) hpd).2
        ring
  by_cases hc2 : σ ≤ (5/7)
  ·
    have hl : (12/17) ≤ σ := by linarith
    have hh : σ ≤ (5/7) := by linarith
    apply density_weaken (Montgomery.RationalMoment.two_term_density_first (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-3 + (8 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 + (-1 * σ)) := by linarith
    have hA : (6:ℝ)/(-3 + (8 * σ)) ≤ 3/(2 + (-1 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-21 + (30 * σ)) := by
        calc
          0 ≤ 21*((5/7)-σ)+51*(σ-(12/17)) := by positivity
          _ = (-21 + (30 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    have hpd : ((-2 + σ):ℝ) ≠ 0 := by linarith
    calc
      _ = (6:ℝ)/(-3 + (8 * σ))*(1-σ) := by ring
      _ ≤ 3/(2 + (-1 * σ))*(1-σ) := hp
      _ = ((-3 + (3 * σ)) / (-2 + σ)) := by
        rw [div_mul_eq_mul_div]
        apply (div_eq_div_iff (ne_of_gt hd2) hpd).2
        ring
  by_cases hc3 : σ ≤ (113/153)
  ·
    have hl : (5/7) ≤ σ := by linarith
    have hh : σ ≤ (113/153) := by linarith
    apply density_weaken (Montgomery.RationalMoment.adjacent_density_second (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1 + (9 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 + (-1 * σ)) := by linarith
    have hA : (12:ℝ)/(-1 + (9 * σ)) ≤ 3/(2 + (-1 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-27 + (39 * σ)) := by
        calc
          0 ≤ (459/13)*((113/153)-σ)+(966/13)*(σ-(5/7)) := by positivity
          _ = (-27 + (39 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    have hpd : ((-2 + σ):ℝ) ≠ 0 := by linarith
    calc
      _ = (12:ℝ)/(-1 + (9 * σ))*(1-σ) := by ring
      _ ≤ 3/(2 + (-1 * σ))*(1-σ) := hp
      _ = ((-3 + (3 * σ)) / (-2 + σ)) := by
        rw [div_mul_eq_mul_div]
        apply (div_eq_div_iff (ne_of_gt hd2) hpd).2
        ring
  by_cases hc4 : σ ≤ (3/4)
  ·
    have hl : (113/153) ≤ σ := by linarith
    have hh : σ ≤ (3/4) := by linarith
    apply density_weaken (Montgomery.RationalMoment.third_density_segment (by linarith) (by linarith) _hε)
    have hd1 : 0 < (7 + (153 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 + (-1 * σ)) := by linarith
    have hA : (255:ℝ)/(7 + (153 * σ)) ≤ 3/(2 + (-1 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-489 + (714 * σ)) := by
        calc
          0 ≤ (23460/7)*((3/4)-σ)+(28458/7)*(σ-(113/153)) := by positivity
          _ = (-489 + (714 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    have hpd : ((-2 + σ):ℝ) ≠ 0 := by linarith
    calc
      _ = (255:ℝ)/(7 + (153 * σ))*(1-σ) := by ring
      _ ≤ 3/(2 + (-1 * σ))*(1-σ) := hp
      _ = ((-3 + (3 * σ)) / (-2 + σ)) := by
        rw [div_mul_eq_mul_div]
        apply (div_eq_div_iff (ne_of_gt hd2) hpd).2
        ring
  by_cases hc5 : σ ≤ (7/9)
  ·
    have hl : (3/4) ≤ σ := by linarith
    have hh : σ ≤ (7/9) := by linarith
    apply density_weaken (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) _hε)
    have hd1 : 0 < (2 * σ) := by linarith
    have hd2 : (0:ℝ) < (2 + (-1 * σ)) := by linarith
    have hA : (3:ℝ)/(2 * σ) ≤ 3/(2 + (-1 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-6 + (9 * σ)) := by
        calc
          0 ≤ 27*((7/9)-σ)+36*(σ-(3/4)) := by positivity
          _ = (-6 + (9 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    have hpd : ((-2 + σ):ℝ) ≠ 0 := by linarith
    calc
      _ = (3:ℝ)/(2 * σ)*(1-σ) := by ring
      _ ≤ 3/(2 + (-1 * σ))*(1-σ) := hp
      _ = ((-3 + (3 * σ)) / (-2 + σ)) := by
        rw [div_mul_eq_mul_div]
        apply (div_eq_div_iff (ne_of_gt hd2) hpd).2
        ring
  by_cases hc6 : σ ≤ (29359/37574)
  ·
    have hl : (7/9) ≤ σ := by linarith
    have hh : σ ≤ (29359/37574) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_first (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-7 + (11 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 + (-1 * σ)) := by linarith
    have hA : (3:ℝ)/(-7 + (11 * σ)) ≤ 3/(2 + (-1 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-27 + (36 * σ)) := by
        calc
          0 ≤ (338166/1213)*((29359/37574)-σ)+(381834/1213)*(σ-(7/9)) := by positivity
          _ = (-27 + (36 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    have hpd : ((-2 + σ):ℝ) ≠ 0 := by linarith
    calc
      _ = (3:ℝ)/(-7 + (11 * σ))*(1-σ) := by ring
      _ ≤ 3/(2 + (-1 * σ))*(1-σ) := hp
      _ = ((-3 + (3 * σ)) / (-2 + σ)) := by
        rw [div_mul_eq_mul_div]
        apply (div_eq_div_iff (ne_of_gt hd2) hpd).2
        ring
  by_cases hc7 : σ ≤ (1015/1294)
  ·
    have hl : (29359/37574) ≤ σ := by linarith
    have hh : σ ≤ (1015/1294) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_second (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1283 + (4870 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 + (-1 * σ)) := by linarith
    have hA : (4744:ℝ)/(-1283 + (4870 * σ)) ≤ 3/(2 + (-1 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-13337 + (19354 * σ)) := by
        calc
          0 ≤ (18299748/31)*((1015/1294)-σ)+(18899722/31)*(σ-(29359/37574)) := by positivity
          _ = (-13337 + (19354 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    have hpd : ((-2 + σ):ℝ) ≠ 0 := by linarith
    calc
      _ = (4744:ℝ)/(-1283 + (4870 * σ))*(1-σ) := by ring
      _ ≤ 3/(2 + (-1 * σ))*(1-σ) := hp
      _ = ((-3 + (3 * σ)) / (-2 + σ)) := by
        rw [div_mul_eq_mul_div]
        apply (div_eq_div_iff (ne_of_gt hd2) hpd).2
        ring
  by_cases hc8 : σ ≤ (353/447)
  ·
    have hl : (1015/1294) ≤ σ := by linarith
    have hh : σ ≤ (353/447) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_third (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1693 + (6354 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 + (-1 * σ)) := by linarith
    have hA : (6154:ℝ)/(-1693 + (6354 * σ)) ≤ 3/(2 + (-1 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-17387 + (25216 * σ)) := by
        calc
          0 ≤ 449682*((353/447)-σ)+474898*(σ-(1015/1294)) := by positivity
          _ = (-17387 + (25216 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    have hpd : ((-2 + σ):ℝ) ≠ 0 := by linarith
    calc
      _ = (6154:ℝ)/(-1693 + (6354 * σ))*(1-σ) := by ring
      _ ≤ 3/(2 + (-1 * σ))*(1-σ) := hp
      _ = ((-3 + (3 * σ)) / (-2 + σ)) := by
        rw [div_mul_eq_mul_div]
        apply (div_eq_div_iff (ne_of_gt hd2) hpd).2
        ring
  by_cases hc9 : σ ≤ (467/586)
  ·
    have hl : (353/447) ≤ σ := by linarith
    have hh : σ ≤ (467/586) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_fourth (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1065 + (3936 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 + (-1 * σ)) := by linarith
    have hA : (3782:ℝ)/(-1065 + (3936 * σ)) ≤ 3/(2 + (-1 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-10759 + (15590 * σ)) := by
        calc
          0 ≤ 215062*((467/586)-σ)+230652*(σ-(353/447)) := by positivity
          _ = (-10759 + (15590 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    have hpd : ((-2 + σ):ℝ) ≠ 0 := by linarith
    calc
      _ = (3782:ℝ)/(-1065 + (3936 * σ))*(1-σ) := by ring
      _ ≤ 3/(2 + (-1 * σ))*(1-σ) := hp
      _ = ((-3 + (3 * σ)) / (-2 + σ)) := by
        rw [div_mul_eq_mul_div]
        apply (div_eq_div_iff (ne_of_gt hd2) hpd).2
        ring
  by_cases hc10 : σ ≤ (4/5)
  ·
    have hl : (467/586) ≤ σ := by linarith
    have hh : σ ≤ (4/5) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_fifth (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-631 + (2282 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 + (-1 * σ)) := by linarith
    have hA : (2168:ℝ)/(-631 + (2282 * σ)) ≤ 3/(2 + (-1 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-6229 + (9014 * σ)) := by
        calc
          0 ≤ (932240/3)*((4/5)-σ)+(959282/3)*(σ-(467/586)) := by positivity
          _ = (-6229 + (9014 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    have hpd : ((-2 + σ):ℝ) ≠ 0 := by linarith
    calc
      _ = (2168:ℝ)/(-631 + (2282 * σ))*(1-σ) := by ring
      _ ≤ 3/(2 + (-1 * σ))*(1-σ) := hp
      _ = ((-3 + (3 * σ)) / (-2 + σ)) := by
        rw [div_mul_eq_mul_div]
        apply (div_eq_div_iff (ne_of_gt hd2) hpd).2
        ring
  by_cases hc11 : σ ≤ (289/358)
  ·
    have hl : (4/5) ≤ σ := by linarith
    have hh : σ ≤ (289/358) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_dashed_first (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-631 + (2282 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 + (-1 * σ)) := by linarith
    have hA : (2168:ℝ)/(-631 + (2282 * σ)) ≤ 3/(2 + (-1 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-6229 + (9014 * σ)) := by
        calc
          0 ≤ (1758138/13)*((289/358)-σ)+(1875320/13)*(σ-(4/5)) := by positivity
          _ = (-6229 + (9014 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    have hpd : ((-2 + σ):ℝ) ≠ 0 := by linarith
    calc
      _ = (2168:ℝ)/(-631 + (2282 * σ))*(1-σ) := by ring
      _ ≤ 3/(2 + (-1 * σ))*(1-σ) := hp
      _ = ((-3 + (3 * σ)) / (-2 + σ)) := by
        rw [div_mul_eq_mul_div]
        apply (div_eq_div_iff (ne_of_gt hd2) hpd).2
        ring
  by_cases hc12 : σ ≤ (163/198)
  ·
    have hl : (289/358) ≤ σ := by linarith
    have hh : σ ≤ (163/198) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_dashed_second (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-173 + (606 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 + (-1 * σ)) := by linarith
    have hA : (566:ℝ)/(-173 + (606 * σ)) ≤ 3/(2 + (-1 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-1651 + (2384 * σ)) := by
        calc
          0 ≤ 17127*((163/198)-σ)+19511*(σ-(289/358)) := by positivity
          _ = (-1651 + (2384 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    have hpd : ((-2 + σ):ℝ) ≠ 0 := by linarith
    calc
      _ = (566:ℝ)/(-173 + (606 * σ))*(1-σ) := by ring
      _ ≤ 3/(2 + (-1 * σ))*(1-σ) := hp
      _ = ((-3 + (3 * σ)) / (-2 + σ)) := by
        rw [div_mul_eq_mul_div]
        apply (div_eq_div_iff (ne_of_gt hd2) hpd).2
        ring
  by_cases hc13 : σ ≤ (7873/9370)
  ·
    have hl : (163/198) ≤ σ := by linarith
    have hh : σ ≤ (7873/9370) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_cube_row3 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-11203 + (35670 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 + (-1 * σ)) := by linarith
    have hA : (31544:ℝ)/(-11203 + (35670 * σ)) ≤ 3/(2 + (-1 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-96697 + (138554 * σ)) := by
        calc
          0 ≤ 1021330*((7873/9370)-σ)+1159884*(σ-(163/198)) := by positivity
          _ = (-96697 + (138554 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    have hpd : ((-2 + σ):ℝ) ≠ 0 := by linarith
    calc
      _ = (31544:ℝ)/(-11203 + (35670 * σ))*(1-σ) := by ring
      _ ≤ 3/(2 + (-1 * σ))*(1-σ) := hp
      _ = ((-3 + (3 * σ)) / (-2 + σ)) := by
        rw [div_mul_eq_mul_div]
        apply (div_eq_div_iff (ne_of_gt hd2) hpd).2
        ring
  by_cases hc14 : σ ≤ (2018/2375)
  ·
    have hl : (7873/9370) ≤ σ := by linarith
    have hh : σ ≤ (2018/2375) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_universal_row4 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-465509 + (1447460 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 + (-1 * σ)) := by linarith
    have hA : (1261710:ℝ)/(-465509 + (1447460 * σ)) ≤ 3/(2 + (-1 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-3919947 + (5604090 * σ)) := by
        calc
          0 ≤ 83476500*((2018/2375)-σ)+89080590*(σ-(7873/9370)) := by positivity
          _ = (-3919947 + (5604090 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    have hpd : ((-2 + σ):ℝ) ≠ 0 := by linarith
    calc
      _ = (1261710:ℝ)/(-465509 + (1447460 * σ))*(1-σ) := by ring
      _ ≤ 3/(2 + (-1 * σ))*(1-σ) := hp
      _ = ((-3 + (3 * σ)) / (-2 + σ)) := by
        rw [div_mul_eq_mul_div]
        apply (div_eq_div_iff (ne_of_gt hd2) hpd).2
        ring
  by_cases hc15 : σ ≤ (1959705/2298302)
  ·
    have hl : (2018/2375) ≤ σ := by linarith
    have hh : σ ≤ (1959705/2298302) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_universal_row5 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1215 + (3616 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 + (-1 * σ)) := by linarith
    have hA : (3066:ℝ)/(-1215 + (3616 * σ)) ≤ 3/(2 + (-1 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-9777 + (13914 * σ)) := by
        calc
          0 ≤ (21849957114/31949)*((1959705/2298302)-σ)+(22294495500/31949)*(σ-(2018/2375)) := by positivity
          _ = (-9777 + (13914 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    have hpd : ((-2 + σ):ℝ) ≠ 0 := by linarith
    calc
      _ = (3066:ℝ)/(-1215 + (3616 * σ))*(1-σ) := by ring
      _ ≤ 3/(2 + (-1 * σ))*(1-σ) := hp
      _ = ((-3 + (3 * σ)) / (-2 + σ)) := by
        rw [div_mul_eq_mul_div]
        apply (div_eq_div_iff (ne_of_gt hd2) hpd).2
        ring
  by_cases hc16 : σ ≤ (6482825/7570038)
  ·
    have hl : (1959705/2298302) ≤ σ := by linarith
    have hh : σ ≤ (6482825/7570038) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row6 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-257415 + (729216 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 + (-1 * σ)) := by linarith
    have hA : (597962:ℝ)/(-257415 + (729216 * σ)) ≤ 3/(2 + (-1 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-1968169 + (2785610 * σ)) := by
        calc
          0 ≤ (2960880317997/26945)*((6482825/7570038)-σ)+(3035938579447/26945)*(σ-(1959705/2298302)) := by positivity
          _ = (-1968169 + (2785610 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    have hpd : ((-2 + σ):ℝ) ≠ 0 := by linarith
    calc
      _ = (597962:ℝ)/(-257415 + (729216 * σ))*(1-σ) := by ring
      _ ≤ 3/(2 + (-1 * σ))*(1-σ) := hp
      _ = ((-3 + (3 * σ)) / (-2 + σ)) := by
        rw [div_mul_eq_mul_div]
        apply (div_eq_div_iff (ne_of_gt hd2) hpd).2
        ring
  by_cases hc17 : σ ≤ (2905/3354)
  ·
    have hl : (6482825/7570038) ≤ σ := by linarith
    have hh : σ ≤ (2905/3354) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row7 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-7623595 + (20732766 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 + (-1 * σ)) := by linarith
    have hA : (16504356:ℝ)/(-7623595 + (20732766 * σ)) ≤ 3/(2 + (-1 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-55879497 + (78702654 * σ)) := by
        calc
          0 ≤ (5907281692/5)*((2905/3354)-σ)+(6300794962/5)*(σ-(6482825/7570038)) := by positivity
          _ = (-55879497 + (78702654 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    have hpd : ((-2 + σ):ℝ) ≠ 0 := by linarith
    calc
      _ = (16504356:ℝ)/(-7623595 + (20732766 * σ))*(1-σ) := by ring
      _ ≤ 3/(2 + (-1 * σ))*(1-σ) := hp
      _ = ((-3 + (3 * σ)) / (-2 + σ)) := by
        rw [div_mul_eq_mul_div]
        apply (div_eq_div_iff (ne_of_gt hd2) hpd).2
        ring
  have hl : (2905/3354) ≤ σ := by linarith
  have hh : σ ≤ (7/8) := by linarith
  apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row8 (by linarith) (by linarith) _hε)
  have hd1 : 0 < (-1015 + (2742 * σ)) := by linarith
  have hd2 : (0:ℝ) < (2 + (-1 * σ)) := by linarith
  have hA : (2172:ℝ)/(-1015 + (2742 * σ)) ≤ 3/(2 + (-1 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (-7389 + (10398 * σ)) := by
      calc
        0 ≤ (21693936/119)*((7/8)-σ)+(22931298/119)*(σ-(2905/3354)) := by positivity
        _ = (-7389 + (10398 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  have hpd : ((-2 + σ):ℝ) ≠ 0 := by linarith
  calc
    _ = (2172:ℝ)/(-1015 + (2742 * σ))*(1-σ) := by ring
    _ ≤ 3/(2 + (-1 * σ))*(1-σ) := hp
    _ = ((-3 + (3 * σ)) / (-2 + σ)) := by
      rw [div_mul_eq_mul_div]
      apply (div_eq_div_iff (ne_of_gt hd2) hpd).2
      ring
/-- Exact published-source density conclusion, supplied by native project domination and strict actual zero-freeness. No new mathematics or claim to reprove the original published route. -/
theorem source_tty48_full {σ ε : ℝ} (_hlo : (1/2) ≤ σ)
    (_hhi : σ ≤ 1) (_hε : 0 < ε) :
    DensityBound σ ((3 + (-3 * σ)) / (-1 + (3 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  by_cases hc0 : σ ≤ (9/13)
  ·
    have hl : (1/2) ≤ σ := by linarith
    have hh : σ ≤ (9/13) := by linarith
    apply density_weaken (GuthMaynard.Improvement.ingham_lower_density σ (by linarith) (by linarith) ε _hε)
    have hd1 : 0 < (2 + (-1 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (3 * σ)) := by linarith
    have hA : (3:ℝ)/(2 + (-1 * σ)) ≤ 3/(-1 + (3 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (9 + (-12 * σ)) := by
        calc
          0 ≤ (78/5)*((9/13)-σ)+(18/5)*(σ-(1/2)) := by positivity
          _ = (9 + (-12 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc1 : σ ≤ (12/17)
  ·
    have hl : (9/13) ≤ σ := by linarith
    have hh : σ ≤ (12/17) := by linarith
    apply density_weaken (Montgomery.Refined.refined_density_middle (by linarith) (by linarith) _hε)
    have hd1 : 0 < (3 + (7 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (3 * σ)) := by linarith
    have hA : (18:ℝ)/(3 + (7 * σ)) ≤ 3/(-1 + (3 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (27 + (-33 * σ)) := by
        calc
          0 ≤ 306*((12/17)-σ)+273*(σ-(9/13)) := by positivity
          _ = (27 + (-33 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc2 : σ ≤ (5/7)
  ·
    have hl : (12/17) ≤ σ := by linarith
    have hh : σ ≤ (5/7) := by linarith
    apply density_weaken (Montgomery.RationalMoment.two_term_density_first (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-3 + (8 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (3 * σ)) := by linarith
    have hA : (6:ℝ)/(-3 + (8 * σ)) ≤ 3/(-1 + (3 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-3 + (6 * σ)) := by
        calc
          0 ≤ 147*((5/7)-σ)+153*(σ-(12/17)) := by positivity
          _ = (-3 + (6 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc3 : σ ≤ (113/153)
  ·
    have hl : (5/7) ≤ σ := by linarith
    have hh : σ ≤ (113/153) := by linarith
    apply density_weaken (Montgomery.RationalMoment.adjacent_density_second (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1 + (9 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (3 * σ)) := by linarith
    have hA : (12:ℝ)/(-1 + (9 * σ)) ≤ 3/(-1 + (3 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (9 + (-9 * σ)) := by
        calc
          0 ≤ (1377/13)*((113/153)-σ)+(1260/13)*(σ-(5/7)) := by positivity
          _ = (9 + (-9 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc4 : σ ≤ (3/4)
  ·
    have hl : (113/153) ≤ σ := by linarith
    have hh : σ ≤ (3/4) := by linarith
    apply density_weaken (Montgomery.RationalMoment.third_density_segment (by linarith) (by linarith) _hε)
    have hd1 : 0 < (7 + (153 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (3 * σ)) := by linarith
    have hA : (255:ℝ)/(7 + (153 * σ)) ≤ 3/(-1 + (3 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (276 + (-306 * σ)) := by
        calc
          0 ≤ (30600/7)*((3/4)-σ)+(28458/7)*(σ-(113/153)) := by positivity
          _ = (276 + (-306 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc5 : σ ≤ (7/9)
  ·
    have hl : (3/4) ≤ σ := by linarith
    have hh : σ ≤ (7/9) := by linarith
    apply density_weaken (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) _hε)
    have hd1 : 0 < (2 * σ) := by linarith
    have hd2 : (0:ℝ) < (-1 + (3 * σ)) := by linarith
    have hA : (3:ℝ)/(2 * σ) ≤ 3/(-1 + (3 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (3 + (-3 * σ)) := by
        calc
          0 ≤ 27*((7/9)-σ)+24*(σ-(3/4)) := by positivity
          _ = (3 + (-3 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc6 : σ ≤ (29359/37574)
  ·
    have hl : (7/9) ≤ σ := by linarith
    have hh : σ ≤ (29359/37574) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_first (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-7 + (11 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (3 * σ)) := by linarith
    have hA : (3:ℝ)/(-7 + (11 * σ)) ≤ 3/(-1 + (3 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-18 + (24 * σ)) := by
        calc
          0 ≤ (225444/1213)*((29359/37574)-σ)+(254556/1213)*(σ-(7/9)) := by positivity
          _ = (-18 + (24 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc7 : σ ≤ (1015/1294)
  ·
    have hl : (29359/37574) ≤ σ := by linarith
    have hh : σ ≤ (1015/1294) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_second (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1283 + (4870 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (3 * σ)) := by linarith
    have hA : (4744:ℝ)/(-1283 + (4870 * σ)) ≤ 3/(-1 + (3 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (895 + (378 * σ)) := by
        calc
          0 ≤ (12199832/31)*((1015/1294)-σ)+(12211550/31)*(σ-(29359/37574)) := by positivity
          _ = (895 + (378 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc8 : σ ≤ (353/447)
  ·
    have hl : (1015/1294) ≤ σ := by linarith
    have hh : σ ≤ (353/447) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_third (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1693 + (6354 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (3 * σ)) := by linarith
    have hA : (6154:ℝ)/(-1693 + (6354 * σ)) ≤ 3/(-1 + (3 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (1075 + (600 * σ)) := by
        calc
          0 ≤ 290550*((353/447)-σ)+291150*(σ-(1015/1294)) := by positivity
          _ = (1075 + (600 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc9 : σ ≤ (467/586)
  ·
    have hl : (353/447) ≤ σ := by linarith
    have hh : σ ≤ (467/586) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_fourth (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1065 + (3936 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (3 * σ)) := by linarith
    have hA : (3782:ℝ)/(-1065 + (3936 * σ)) ≤ 3/(-1 + (3 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (587 + (462 * σ)) := by
        calc
          0 ≤ 131850*((467/586)-σ)+132312*(σ-(353/447)) := by positivity
          _ = (587 + (462 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc10 : σ ≤ (4/5)
  ·
    have hl : (467/586) ≤ σ := by linarith
    have hh : σ ≤ (4/5) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_fifth (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-631 + (2282 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (3 * σ)) := by linarith
    have hA : (2168:ℝ)/(-631 + (2282 * σ)) ≤ 3/(-1 + (3 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (275 + (342 * σ)) := by
        calc
          0 ≤ (1604320/9)*((4/5)-σ)+(1607398/9)*(σ-(467/586)) := by positivity
          _ = (275 + (342 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc11 : σ ≤ (289/358)
  ·
    have hl : (4/5) ≤ σ := by linarith
    have hh : σ ≤ (289/358) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_dashed_first (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-631 + (2282 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (3 * σ)) := by linarith
    have hA : (2168:ℝ)/(-631 + (2282 * σ)) ≤ 3/(-1 + (3 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (275 + (342 * σ)) := by
        calc
          0 ≤ 75538*((289/358)-σ)+75880*(σ-(4/5)) := by positivity
          _ = (275 + (342 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc12 : σ ≤ (163/198)
  ·
    have hl : (289/358) ≤ σ := by linarith
    have hh : σ ≤ (163/198) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_dashed_second (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-173 + (606 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (3 * σ)) := by linarith
    have hA : (566:ℝ)/(-173 + (606 * σ)) ≤ 3/(-1 + (3 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (47 + (120 * σ)) := by
        calc
          0 ≤ 9009*((163/198)-σ)+9129*(σ-(289/358)) := by positivity
          _ = (47 + (120 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc13 : σ ≤ (7873/9370)
  ·
    have hl : (163/198) ≤ σ := by linarith
    have hh : σ ≤ (7873/9370) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_cube_row3 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-11203 + (35670 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (3 * σ)) := by linarith
    have hA : (31544:ℝ)/(-11203 + (35670 * σ)) ≤ 3/(-1 + (3 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-2065 + (12378 * σ)) := by
        calc
          0 ≤ 477870*((7873/9370)-σ)+490248*(σ-(163/198)) := by positivity
          _ = (-2065 + (12378 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc14 : σ ≤ (2018/2375)
  ·
    have hl : (7873/9370) ≤ σ := by linarith
    have hh : σ ≤ (2018/2375) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_universal_row4 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-465509 + (1447460 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (3 * σ)) := by linarith
    have hA : (1261710:ℝ)/(-465509 + (1447460 * σ)) ≤ 3/(-1 + (3 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-134817 + (557250 * σ)) := by
        calc
          0 ≤ 35283000*((2018/2375)-σ)+35840250*(σ-(7873/9370)) := by positivity
          _ = (-134817 + (557250 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc15 : σ ≤ (1959705/2298302)
  ·
    have hl : (2018/2375) ≤ σ := by linarith
    have hh : σ ≤ (1959705/2298302) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_universal_row5 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1215 + (3616 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (3 * σ)) := by linarith
    have hA : (3066:ℝ)/(-1215 + (3616 * σ)) ≤ 3/(-1 + (3 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-579 + (1650 * σ)) := by
        calc
          0 ≤ (8791005150/31949)*((1959705/2298302)-σ)+(8843721000/31949)*(σ-(2018/2375)) := by positivity
          _ = (-579 + (1650 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc16 : σ ≤ (6482825/7570038)
  ·
    have hl : (1959705/2298302) ≤ σ := by linarith
    have hh : σ ≤ (6482825/7570038) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row6 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-257415 + (729216 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (3 * σ)) := by linarith
    have hA : (597962:ℝ)/(-257415 + (729216 * σ)) ≤ 3/(-1 + (3 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-174283 + (393762 * σ)) := by
        calc
          0 ≤ (1174514105814/26945)*((6482825/7570038)-σ)+(1185124022904/26945)*(σ-(1959705/2298302)) := by positivity
          _ = (-174283 + (393762 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc17 : σ ≤ (2905/3354)
  ·
    have hl : (6482825/7570038) ≤ σ := by linarith
    have hh : σ ≤ (2905/3354) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row7 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-7623595 + (20732766 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (3 * σ)) := by linarith
    have hA : (16504356:ℝ)/(-7623595 + (20732766 * σ)) ≤ 3/(-1 + (3 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-6366429 + (12685230 * σ)) := by
        calc
          0 ≤ (2305995744/5)*((2905/3354)-σ)+(2369421894/5)*(σ-(6482825/7570038)) := by positivity
          _ = (-6366429 + (12685230 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  have hl : (2905/3354) ≤ σ := by linarith
  have hh : σ ≤ (7/8) := by linarith
  apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row8 (by linarith) (by linarith) _hε)
  have hd1 : 0 < (-1015 + (2742 * σ)) := by linarith
  have hd2 : (0:ℝ) < (-1 + (3 * σ)) := by linarith
  have hA : (2172:ℝ)/(-1015 + (2742 * σ)) ≤ 3/(-1 + (3 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (-873 + (1710 * σ)) := by
      calc
        0 ≤ (8158032/119)*((7/8)-σ)+(8361522/119)*(σ-(2905/3354)) := by positivity
        _ = (-873 + (1710 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact published-source density conclusion, supplied by native project domination and strict actual zero-freeness. No new mathematics or claim to reprove the original published route. -/
theorem source_tty49_full {σ ε : ℝ} (_hlo : (1/2) ≤ σ)
    (_hhi : σ ≤ 1) (_hε : 0 < ε) :
    DensityBound σ ((15 + (-15 * σ)) / (3 + (5 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  by_cases hc0 : σ ≤ (9/13)
  ·
    have hl : (1/2) ≤ σ := by linarith
    have hh : σ ≤ (9/13) := by linarith
    apply density_weaken (GuthMaynard.Improvement.ingham_lower_density σ (by linarith) (by linarith) ε _hε)
    have hd1 : 0 < (2 + (-1 * σ)) := by linarith
    have hd2 : (0:ℝ) < (3 + (5 * σ)) := by linarith
    have hA : (3:ℝ)/(2 + (-1 * σ)) ≤ 15/(3 + (5 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (21 + (-30 * σ)) := by
        calc
          0 ≤ (156/5)*((9/13)-σ)+(6/5)*(σ-(1/2)) := by positivity
          _ = (21 + (-30 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc1 : σ ≤ (12/17)
  ·
    have hl : (9/13) ≤ σ := by linarith
    have hh : σ ≤ (12/17) := by linarith
    apply density_weaken (Montgomery.Refined.refined_density_middle (by linarith) (by linarith) _hε)
    have hd1 : 0 < (3 + (7 * σ)) := by linarith
    have hd2 : (0:ℝ) < (3 + (5 * σ)) := by linarith
    have hA : (18:ℝ)/(3 + (7 * σ)) ≤ 15/(3 + (5 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-9 + (15 * σ)) := by
        calc
          0 ≤ 102*((12/17)-σ)+117*(σ-(9/13)) := by positivity
          _ = (-9 + (15 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc2 : σ ≤ (5/7)
  ·
    have hl : (12/17) ≤ σ := by linarith
    have hh : σ ≤ (5/7) := by linarith
    apply density_weaken (Montgomery.RationalMoment.two_term_density_first (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-3 + (8 * σ)) := by linarith
    have hd2 : (0:ℝ) < (3 + (5 * σ)) := by linarith
    have hA : (6:ℝ)/(-3 + (8 * σ)) ≤ 15/(3 + (5 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-63 + (90 * σ)) := by
        calc
          0 ≤ 63*((5/7)-σ)+153*(σ-(12/17)) := by positivity
          _ = (-63 + (90 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc3 : σ ≤ (113/153)
  ·
    have hl : (5/7) ≤ σ := by linarith
    have hh : σ ≤ (113/153) := by linarith
    apply density_weaken (Montgomery.RationalMoment.adjacent_density_second (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1 + (9 * σ)) := by linarith
    have hd2 : (0:ℝ) < (3 + (5 * σ)) := by linarith
    have hA : (12:ℝ)/(-1 + (9 * σ)) ≤ 15/(3 + (5 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-51 + (75 * σ)) := by
        calc
          0 ≤ (1377/13)*((113/153)-σ)+(2352/13)*(σ-(5/7)) := by positivity
          _ = (-51 + (75 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc4 : σ ≤ (3/4)
  ·
    have hl : (113/153) ≤ σ := by linarith
    have hh : σ ≤ (3/4) := by linarith
    apply density_weaken (Montgomery.RationalMoment.third_density_segment (by linarith) (by linarith) _hε)
    have hd1 : 0 < (7 + (153 * σ)) := by linarith
    have hd2 : (0:ℝ) < (3 + (5 * σ)) := by linarith
    have hA : (255:ℝ)/(7 + (153 * σ)) ≤ 15/(3 + (5 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-660 + (1020 * σ)) := by
        calc
          0 ≤ 8160*((3/4)-σ)+9180*(σ-(113/153)) := by positivity
          _ = (-660 + (1020 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc5 : σ ≤ (7/9)
  ·
    have hl : (3/4) ≤ σ := by linarith
    have hh : σ ≤ (7/9) := by linarith
    apply density_weaken (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) _hε)
    have hd1 : 0 < (2 * σ) := by linarith
    have hd2 : (0:ℝ) < (3 + (5 * σ)) := by linarith
    have hA : (3:ℝ)/(2 * σ) ≤ 15/(3 + (5 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-9 + (15 * σ)) := by
        calc
          0 ≤ 81*((7/9)-σ)+96*(σ-(3/4)) := by positivity
          _ = (-9 + (15 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc6 : σ ≤ (29359/37574)
  ·
    have hl : (7/9) ≤ σ := by linarith
    have hh : σ ≤ (29359/37574) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_first (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-7 + (11 * σ)) := by linarith
    have hd2 : (0:ℝ) < (3 + (5 * σ)) := by linarith
    have hA : (3:ℝ)/(-7 + (11 * σ)) ≤ 15/(3 + (5 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-114 + (150 * σ)) := by
        calc
          0 ≤ (901776/1213)*((29359/37574)-σ)+(1083726/1213)*(σ-(7/9)) := by positivity
          _ = (-114 + (150 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc7 : σ ≤ (1015/1294)
  ·
    have hl : (29359/37574) ≤ σ := by linarith
    have hh : σ ≤ (1015/1294) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_second (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1283 + (4870 * σ)) := by linarith
    have hd2 : (0:ℝ) < (3 + (5 * σ)) := by linarith
    have hA : (4744:ℝ)/(-1283 + (4870 * σ)) ≤ 15/(3 + (5 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-33477 + (49330 * σ)) := by
        calc
          0 ≤ (51938572/31)*((1015/1294)-σ)+(53467802/31)*(σ-(29359/37574)) := by positivity
          _ = (-33477 + (49330 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc8 : σ ≤ (353/447)
  ·
    have hl : (1015/1294) ≤ σ := by linarith
    have hh : σ ≤ (353/447) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_third (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1693 + (6354 * σ)) := by linarith
    have hd2 : (0:ℝ) < (3 + (5 * σ)) := by linarith
    have hA : (6154:ℝ)/(-1693 + (6354 * σ)) ≤ 15/(3 + (5 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-43857 + (64540 * σ)) := by
        calc
          0 ≤ 1272162*((353/447)-σ)+1336702*(σ-(1015/1294)) := by positivity
          _ = (-43857 + (64540 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc9 : σ ≤ (467/586)
  ·
    have hl : (353/447) ≤ σ := by linarith
    have hh : σ ≤ (467/586) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_fourth (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1065 + (3936 * σ)) := by linarith
    have hd2 : (0:ℝ) < (3 + (5 * σ)) := by linarith
    have hA : (3782:ℝ)/(-1065 + (3936 * σ)) ≤ 15/(3 + (5 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-27321 + (40130 * σ)) := by
        calc
          0 ≤ 605338*((467/586)-σ)+645468*(σ-(353/447)) := by positivity
          _ = (-27321 + (40130 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc10 : σ ≤ (4/5)
  ·
    have hl : (467/586) ≤ σ := by linarith
    have hh : σ ≤ (4/5) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_fifth (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-631 + (2282 * σ)) := by linarith
    have hd2 : (0:ℝ) < (3 + (5 * σ)) := by linarith
    have hA : (2168:ℝ)/(-631 + (2282 * σ)) ≤ 15/(3 + (5 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-15969 + (23390 * σ)) := by
        calc
          0 ≤ (7826480/9)*((4/5)-σ)+(8036990/9)*(σ-(467/586)) := by positivity
          _ = (-15969 + (23390 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc11 : σ ≤ (289/358)
  ·
    have hl : (4/5) ≤ σ := by linarith
    have hh : σ ≤ (289/358) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_dashed_first (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-631 + (2282 * σ)) := by linarith
    have hd2 : (0:ℝ) < (3 + (5 * σ)) := by linarith
    have hA : (2168:ℝ)/(-631 + (2282 * σ)) ≤ 15/(3 + (5 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-15969 + (23390 * σ)) := by
        calc
          0 ≤ 377690*((289/358)-σ)+401080*(σ-(4/5)) := by positivity
          _ = (-15969 + (23390 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc12 : σ ≤ (163/198)
  ·
    have hl : (289/358) ≤ σ := by linarith
    have hh : σ ≤ (163/198) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_dashed_second (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-173 + (606 * σ)) := by linarith
    have hd2 : (0:ℝ) < (3 + (5 * σ)) := by linarith
    have hA : (566:ℝ)/(-173 + (606 * σ)) ≤ 15/(3 + (5 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-4293 + (6260 * σ)) := by
        calc
          0 ≤ 47619*((163/198)-σ)+53879*(σ-(289/358)) := by positivity
          _ = (-4293 + (6260 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc13 : σ ≤ (7873/9370)
  ·
    have hl : (163/198) ≤ σ := by linarith
    have hh : σ ≤ (7873/9370) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_cube_row3 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-11203 + (35670 * σ)) := by linarith
    have hd2 : (0:ℝ) < (3 + (5 * σ)) := by linarith
    have hA : (31544:ℝ)/(-11203 + (35670 * σ)) ≤ 15/(3 + (5 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-262677 + (377330 * σ)) := by
        calc
          0 ≤ 2820370*((7873/9370)-σ)+3197700*(σ-(163/198)) := by positivity
          _ = (-262677 + (377330 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc14 : σ ≤ (2018/2375)
  ·
    have hl : (7873/9370) ≤ σ := by linarith
    have hh : σ ≤ (2018/2375) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_universal_row4 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-465509 + (1447460 * σ)) := by linarith
    have hd2 : (0:ℝ) < (3 + (5 * σ)) := by linarith
    have hA : (1261710:ℝ)/(-465509 + (1447460 * σ)) ≤ 15/(3 + (5 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-10767765 + (15403350 * σ)) := by
        calc
          0 ≤ 230137500*((2018/2375)-σ)+245540850*(σ-(7873/9370)) := by positivity
          _ = (-10767765 + (15403350 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc15 : σ ≤ (1959705/2298302)
  ·
    have hl : (2018/2375) ≤ σ := by linarith
    have hh : σ ≤ (1959705/2298302) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_universal_row5 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1215 + (3616 * σ)) := by linarith
    have hd2 : (0:ℝ) < (3 + (5 * σ)) := by linarith
    have hA : (3066:ℝ)/(-1215 + (3616 * σ)) ≤ 15/(3 + (5 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-27423 + (38910 * σ)) := by
        calc
          0 ≤ (60227003910/31949)*((1959705/2298302)-σ)+(61470139500/31949)*(σ-(2018/2375)) := by positivity
          _ = (-27423 + (38910 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc16 : σ ≤ (6482825/7570038)
  ·
    have hl : (1959705/2298302) ≤ σ := by linarith
    have hh : σ ≤ (6482825/7570038) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row6 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-257415 + (729216 * σ)) := by linarith
    have hd2 : (0:ℝ) < (3 + (5 * σ)) := by linarith
    have hA : (597962:ℝ)/(-257415 + (729216 * σ)) ≤ 15/(3 + (5 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-5655111 + (7948430 * σ)) := by
        calc
          0 ≤ (8163706875093/26945)*((6482825/7570038)-σ)+(8377877321443/26945)*(σ-(1959705/2298302)) := by positivity
          _ = (-5655111 + (7948430 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc17 : σ ≤ (2905/3354)
  ·
    have hl : (6482825/7570038) ≤ σ := by linarith
    have hh : σ ≤ (2905/3354) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row7 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-7623595 + (20732766 * σ)) := by linarith
    have hd2 : (0:ℝ) < (3 + (5 * σ)) := by linarith
    have hA : (16504356:ℝ)/(-7623595 + (20732766 * σ)) ≤ 15/(3 + (5 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-163866993 + (228469710 * σ)) := by
        calc
          0 ≤ (16301542348/5)*((2905/3354)-σ)+(17443890898/5)*(σ-(6482825/7570038)) := by positivity
          _ = (-163866993 + (228469710 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  have hl : (2905/3354) ≤ σ := by linarith
  have hh : σ ≤ (7/8) := by linarith
  apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row8 (by linarith) (by linarith) _hε)
  have hd1 : 0 < (-1015 + (2742 * σ)) := by linarith
  have hd2 : (0:ℝ) < (3 + (5 * σ)) := by linarith
  have hA : (2172:ℝ)/(-1015 + (2742 * σ)) ≤ 15/(3 + (5 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (-21741 + (30270 * σ)) := by
      calc
        0 ≤ (60060144/119)*((7/8)-σ)+(63662274/119)*(σ-(2905/3354)) := by positivity
        _ = (-21741 + (30270 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
end Montgomery.LiteratureDensity
