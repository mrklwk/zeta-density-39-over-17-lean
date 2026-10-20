module
public import WrittenDensity.Common

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.WrittenDensity
open MathCollab.Density
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_v7_A_1 {σ ε : ℝ} (_hlo : (7/10) ≤ σ)
    (_hhi : σ ≤ (12/17)) (_hε : 0 < ε) :
    DensityBound σ ((6 + (-6 * σ)) / (-3 + (8 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  have hl : (7/10) ≤ σ := by linarith
  have hh : σ ≤ (12/17) := by linarith
  apply density_weaken (Montgomery.Refined.refined_density_middle (by linarith) (by linarith) _hε)
  have hd1 : 0 < (3 + (7 * σ)) := by linarith
  have hd2 : (0:ℝ) < (-3 + (8 * σ)) := by linarith
  have hA : (18:ℝ)/(3 + (7 * σ)) ≤ 6/(-3 + (8 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (72 + (-102 * σ)) := by
      calc
        0 ≤ 102*((12/17)-σ) := by positivity
        _ = (72 + (-102 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_v7_A_2 {σ ε : ℝ} (_hlo : (12/17) ≤ σ)
    (_hhi : σ ≤ (81/113)) (_hε : 0 < ε) :
    DensityBound σ ((54 + (-54 * σ)) / (-15 + (55 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  by_cases hc0 : σ ≤ (5/7)
  ·
    have hl : (12/17) ≤ σ := by linarith
    have hh : σ ≤ (5/7) := by linarith
    apply density_weaken (Montgomery.RationalMoment.two_term_density_first (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-3 + (8 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-15 + (55 * σ)) := by linarith
    have hA : (6:ℝ)/(-3 + (8 * σ)) ≤ 54/(-15 + (55 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-72 + (102 * σ)) := by
        calc
          0 ≤ 102*(σ-(12/17)) := by positivity
          _ = (-72 + (102 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  have hl : (5/7) ≤ σ := by linarith
  have hh : σ ≤ (81/113) := by linarith
  apply density_weaken (Montgomery.RationalMoment.adjacent_density_second (by linarith) (by linarith) _hε)
  have hd1 : 0 < (-1 + (9 * σ)) := by linarith
  have hd2 : (0:ℝ) < (-15 + (55 * σ)) := by linarith
  have hA : (12:ℝ)/(-1 + (9 * σ)) ≤ 54/(-15 + (55 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (126 + (-174 * σ)) := by
      calc
        0 ≤ 678*((81/113)-σ)+504*(σ-(5/7)) := by positivity
        _ = (126 + (-174 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_v7_A_3 {σ ε : ℝ} (_hlo : (81/113) ≤ σ)
    (_hhi : σ ≤ (47/65)) (_hε : 0 < ε) :
    DensityBound σ ((414 + (-414 * σ)) / (-7 + (271 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  have hl : (81/113) ≤ σ := by linarith
  have hh : σ ≤ (47/65) := by linarith
  apply density_weaken (Montgomery.RationalMoment.adjacent_density_second (by linarith) (by linarith) _hε)
  have hd1 : 0 < (-1 + (9 * σ)) := by linarith
  have hd2 : (0:ℝ) < (-7 + (271 * σ)) := by linarith
  have hA : (12:ℝ)/(-1 + (9 * σ)) ≤ 414/(-7 + (271 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (-330 + (474 * σ)) := by
      calc
        0 ≤ 1560*((47/65)-σ)+2034*(σ-(81/113)) := by positivity
        _ = (-330 + (474 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_v7_A_4 {σ ε : ℝ} (_hlo : (47/65) ≤ σ)
    (_hhi : σ ≤ (69/91)) (_hε : 0 < ε) :
    DensityBound σ ((39 + (-39 * σ)) / (-1 + (26 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  by_cases hc0 : σ ≤ (113/153)
  ·
    have hl : (47/65) ≤ σ := by linarith
    have hh : σ ≤ (113/153) := by linarith
    apply density_weaken (Montgomery.RationalMoment.adjacent_density_second (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1 + (9 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (26 * σ)) := by linarith
    have hA : (12:ℝ)/(-1 + (9 * σ)) ≤ 39/(-1 + (26 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-27 + (39 * σ)) := by
        calc
          0 ≤ (5967/77)*((113/153)-σ)+(8970/77)*(σ-(47/65)) := by positivity
          _ = (-27 + (39 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc1 : σ ≤ (3/4)
  ·
    have hl : (113/153) ≤ σ := by linarith
    have hh : σ ≤ (3/4) := by linarith
    apply density_weaken (Montgomery.RationalMoment.third_density_segment (by linarith) (by linarith) _hε)
    have hd1 : 0 < (7 + (153 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (26 * σ)) := by linarith
    have hA : (255:ℝ)/(7 + (153 * σ)) ≤ 39/(-1 + (26 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (528 + (-663 * σ)) := by
        calc
          0 ≤ (23460/7)*((3/4)-σ)+(18819/7)*(σ-(113/153)) := by positivity
          _ = (528 + (-663 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  have hl : (3/4) ≤ σ := by linarith
  have hh : σ ≤ (69/91) := by linarith
  apply density_weaken (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) _hε)
  have hd1 : 0 < (2 * σ) := by linarith
  have hd2 : (0:ℝ) < (-1 + (26 * σ)) := by linarith
  have hA : (3:ℝ)/(2 * σ) ≤ 39/(-1 + (26 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ 3 := by
      calc
        0 ≤ 3 := by positivity
        _ = 3 := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_v7_A_5 {σ ε : ℝ} (_hlo : (69/91) ≤ σ)
    (_hhi : σ ≤ (7/9)) (_hε : 0 < ε) :
    DensityBound σ ((12 + (-12 * σ)) / (5 + σ)) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  have hl : (69/91) ≤ σ := by linarith
  have hh : σ ≤ (7/9) := by linarith
  apply density_weaken (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) _hε)
  have hd1 : 0 < (2 * σ) := by linarith
  have hd2 : (0:ℝ) < (5 + σ) := by linarith
  have hA : (3:ℝ)/(2 * σ) ≤ 12/(5 + σ) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (-15 + (21 * σ)) := by
      calc
        0 ≤ (189/4)*((7/9)-σ)+(273/4)*(σ-(69/91)) := by positivity
        _ = (-15 + (21 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_v7_B_1 {σ ε : ℝ} (_hlo : (69/91) ≤ σ)
    (_hhi : σ ≤ (63/83)) (_hε : 0 < ε) :
    DensityBound σ ((3 + (-3 * σ)) / (-16 + (23 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  have hl : (69/91) ≤ σ := by linarith
  have hh : σ ≤ (63/83) := by linarith
  apply density_weaken (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) _hε)
  have hd1 : 0 < (2 * σ) := by linarith
  have hd2 : (0:ℝ) < (-16 + (23 * σ)) := by linarith
  have hA : (3:ℝ)/(2 * σ) ≤ 3/(-16 + (23 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (48 + (-63 * σ)) := by
      calc
        0 ≤ (581/2)*((63/83)-σ)+(455/2)*(σ-(69/91)) := by positivity
        _ = (48 + (-63 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_v7_B_2 {σ ε : ℝ} (_hlo : (63/83) ≤ σ)
    (_hhi : σ ≤ (45/59)) (_hε : 0 < ε) :
    DensityBound σ ((12 + (-12 * σ)) / (-1 + (9 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  have hl : (63/83) ≤ σ := by linarith
  have hh : σ ≤ (45/59) := by linarith
  apply density_weaken (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) _hε)
  have hd1 : 0 < (2 * σ) := by linarith
  have hd2 : (0:ℝ) < (-1 + (9 * σ)) := by linarith
  have hA : (3:ℝ)/(2 * σ) ≤ 12/(-1 + (9 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (3 + (-3 * σ)) := by
      calc
        0 ≤ (590/3)*((45/59)-σ)+(581/3)*(σ-(63/83)) := by positivity
        _ = (3 + (-3 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_v7_B_3 {σ ε : ℝ} (_hlo : (45/59) ≤ σ)
    (_hhi : σ ≤ (13/17)) (_hε : 0 < ε) :
    DensityBound σ ((6 + (-6 * σ)) / (-23 + (34 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  have hl : (45/59) ≤ σ := by linarith
  have hh : σ ≤ (13/17) := by linarith
  apply density_weaken (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) _hε)
  have hd1 : 0 < (2 * σ) := by linarith
  have hd2 : (0:ℝ) < (-23 + (34 * σ)) := by linarith
  have hA : (3:ℝ)/(2 * σ) ≤ 6/(-23 + (34 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (69 + (-90 * σ)) := by
      calc
        0 ≤ (357/2)*((13/17)-σ)+(177/2)*(σ-(45/59)) := by positivity
        _ = (69 + (-90 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_v7_B_4 {σ ε : ℝ} (_hlo : (13/17) ≤ σ)
    (_hhi : σ ≤ 1) (_hε : 0 < ε) :
    DensityBound σ (2 + (-2 * σ)) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  by_cases hc0 : σ ≤ (7/9)
  ·
    have hl : (13/17) ≤ σ := by linarith
    have hh : σ ≤ (7/9) := by linarith
    apply density_weaken (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) _hε)
    have hd1 : 0 < (2 * σ) := by linarith
    have hd2 : (0:ℝ) < 1 := by linarith
    have hA : (3:ℝ)/(2 * σ) ≤ 2/1 := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-3 + (4 * σ)) := by
        calc
          0 ≤ (9/2)*((7/9)-σ)+(17/2)*(σ-(13/17)) := by positivity
          _ = (-3 + (4 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc1 : σ ≤ (29359/37574)
  ·
    have hl : (7/9) ≤ σ := by linarith
    have hh : σ ≤ (29359/37574) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_first (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-7 + (11 * σ)) := by linarith
    have hd2 : (0:ℝ) < 1 := by linarith
    have hA : (3:ℝ)/(-7 + (11 * σ)) ≤ 2/1 := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-17 + (22 * σ)) := by
        calc
          0 ≤ (37574/1213)*((29359/37574)-σ)+(64260/1213)*(σ-(7/9)) := by positivity
          _ = (-17 + (22 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc2 : σ ≤ (1015/1294)
  ·
    have hl : (29359/37574) ≤ σ := by linarith
    have hh : σ ≤ (1015/1294) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_second (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1283 + (4870 * σ)) := by linarith
    have hd2 : (0:ℝ) < 1 := by linarith
    have hA : (4744:ℝ)/(-1283 + (4870 * σ)) ≤ 2/1 := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-7310 + (9740 * σ)) := by
        calc
          0 ≤ (3079720/31)*((1015/1294)-σ)+(3381660/31)*(σ-(29359/37574)) := by positivity
          _ = (-7310 + (9740 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc3 : σ ≤ (353/447)
  ·
    have hl : (1015/1294) ≤ σ := by linarith
    have hh : σ ≤ (353/447) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_third (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1693 + (6354 * σ)) := by linarith
    have hd2 : (0:ℝ) < 1 := by linarith
    have hA : (6154:ℝ)/(-1693 + (6354 * σ)) ≤ 2/1 := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-9540 + (12708 * σ)) := by
        calc
          0 ≤ 80460*((353/447)-σ)+93168*(σ-(1015/1294)) := by positivity
          _ = (-9540 + (12708 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc4 : σ ≤ (467/586)
  ·
    have hl : (353/447) ≤ σ := by linarith
    have hh : σ ≤ (467/586) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_fourth (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1065 + (3936 * σ)) := by linarith
    have hd2 : (0:ℝ) < 1 := by linarith
    have hA : (3782:ℝ)/(-1065 + (3936 * σ)) ≤ 2/1 := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-5912 + (7872 * σ)) := by
        calc
          0 ≤ 42192*((467/586)-σ)+50064*(σ-(353/447)) := by positivity
          _ = (-5912 + (7872 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc5 : σ ≤ (4/5)
  ·
    have hl : (467/586) ≤ σ := by linarith
    have hh : σ ≤ (4/5) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_fifth (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-631 + (2282 * σ)) := by linarith
    have hd2 : (0:ℝ) < 1 := by linarith
    have hA : (2168:ℝ)/(-631 + (2282 * σ)) ≤ 2/1 := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-3430 + (4564 * σ)) := by
        calc
          0 ≤ (607040/9)*((4/5)-σ)+(648116/9)*(σ-(467/586)) := by positivity
          _ = (-3430 + (4564 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc6 : σ ≤ (289/358)
  ·
    have hl : (4/5) ≤ σ := by linarith
    have hh : σ ≤ (289/358) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_dashed_first (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-631 + (2282 * σ)) := by linarith
    have hd2 : (0:ℝ) < 1 := by linarith
    have hA : (2168:ℝ)/(-631 + (2282 * σ)) ≤ 2/1 := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-3430 + (4564 * σ)) := by
        calc
          0 ≤ (395948/13)*((289/358)-σ)+(455280/13)*(σ-(4/5)) := by positivity
          _ = (-3430 + (4564 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc7 : σ ≤ (163/198)
  ·
    have hl : (289/358) ≤ σ := by linarith
    have hh : σ ≤ (163/198) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_dashed_second (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-173 + (606 * σ)) := by linarith
    have hd2 : (0:ℝ) < 1 := by linarith
    have hA : (566:ℝ)/(-173 + (606 * σ)) ≤ 2/1 := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-912 + (1212 * σ)) := by
        calc
          0 ≤ 4158*((163/198)-σ)+5370*(σ-(289/358)) := by positivity
          _ = (-912 + (1212 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc8 : σ ≤ (7873/9370)
  ·
    have hl : (163/198) ≤ σ := by linarith
    have hh : σ ≤ (7873/9370) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_cube_row3 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-11203 + (35670 * σ)) := by linarith
    have hd2 : (0:ℝ) < 1 := by linarith
    have hA : (31544:ℝ)/(-11203 + (35670 * σ)) ≤ 2/1 := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-53950 + (71340 * σ)) := by
        calc
          0 ≤ 281100*((7873/9370)-σ)+352440*(σ-(163/198)) := by positivity
          _ = (-53950 + (71340 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc9 : σ ≤ (2018/2375)
  ·
    have hl : (7873/9370) ≤ σ := by linarith
    have hh : σ ≤ (2018/2375) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_universal_row4 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-465509 + (1447460 * σ)) := by linarith
    have hd2 : (0:ℝ) < 1 := by linarith
    have hA : (1261710:ℝ)/(-465509 + (1447460 * σ)) ≤ 2/1 := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-2192728 + (2894920 * σ)) := by
        calc
          0 ≤ 25365000*((2018/2375)-σ)+28259920*(σ-(7873/9370)) := by positivity
          _ = (-2192728 + (2894920 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc10 : σ ≤ (1959705/2298302)
  ·
    have hl : (2018/2375) ≤ σ := by linarith
    have hh : σ ≤ (1959705/2298302) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_universal_row5 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1215 + (3616 * σ)) := by linarith
    have hd2 : (0:ℝ) < 1 := by linarith
    have hA : (3066:ℝ)/(-1215 + (3616 * σ)) ≤ 2/1 := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-5496 + (7232 * σ)) := by
        calc
          0 ≤ (6931678832/31949)*((1959705/2298302)-σ)+(7162734000/31949)*(σ-(2018/2375)) := by positivity
          _ = (-5496 + (7232 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc11 : σ ≤ (6482825/7570038)
  ·
    have hl : (1959705/2298302) ≤ σ := by linarith
    have hh : σ ≤ (6482825/7570038) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row6 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-257415 + (729216 * σ)) := by linarith
    have hd2 : (0:ℝ) < 1 := by linarith
    have hA : (597962:ℝ)/(-257415 + (729216 * σ)) ≤ 2/1 := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-1112792 + (1458432 * σ)) := by
        calc
          0 ≤ (951266115156/26945)*((6482825/7570038)-σ)+(990563565396/26945)*(σ-(1959705/2298302)) := by positivity
          _ = (-1112792 + (1458432 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc12 : σ ≤ (2905/3354)
  ·
    have hl : (6482825/7570038) ≤ σ := by linarith
    have hh : σ ≤ (2905/3354) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row7 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-7623595 + (20732766 * σ)) := by linarith
    have hd2 : (0:ℝ) < 1 := by linarith
    have hA : (16504356:ℝ)/(-7623595 + (20732766 * σ)) ≤ 2/1 := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-31751546 + (41465532 * σ)) := by
        calc
          0 ≤ (1927423056/5)*((2905/3354)-σ)+(2134750716/5)*(σ-(6482825/7570038)) := by positivity
          _ = (-31751546 + (41465532 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  have hl : (2905/3354) ≤ σ := by linarith
  have hh : σ ≤ (7/8) := by linarith
  apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row8 (by linarith) (by linarith) _hε)
  have hd1 : 0 < (-1015 + (2742 * σ)) := by linarith
  have hd2 : (0:ℝ) < 1 := by linarith
  have hA : (2172:ℝ)/(-1015 + (2742 * σ)) ≤ 2/1 := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (-4202 + (5484 * σ)) := by
      calc
        0 ≤ (7350048/119)*((7/8)-σ)+(8002644/119)*(σ-(2905/3354)) := by positivity
        _ = (-4202 + (5484 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_v7_C_1 {σ ε : ℝ} (_hlo : (43/56) ≤ σ)
    (_hhi : σ < (11/14)) (_hε : 0 < ε) :
    DensityBound σ ((3 + (-3 * σ)) / (2 * σ)) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  by_cases hc0 : σ ≤ (7/9)
  ·
    have hl : (43/56) ≤ σ := by linarith
    have hh : σ ≤ (7/9) := by linarith
    apply density_weaken (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) _hε)
    have hd1 : 0 < (2 * σ) := by linarith
    have hd2 : (0:ℝ) < (2 * σ) := by linarith
    have hA : (3:ℝ)/(2 * σ) ≤ 3/(2 * σ) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ 0 := by
        calc
          0 ≤ 0 := by positivity
          _ = 0 := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc1 : σ ≤ (29359/37574)
  ·
    have hl : (7/9) ≤ σ := by linarith
    have hh : σ ≤ (29359/37574) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_first (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-7 + (11 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 * σ) := by linarith
    have hA : (3:ℝ)/(-7 + (11 * σ)) ≤ 3/(2 * σ) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-21 + (27 * σ)) := by
        calc
          0 ≤ 27*(σ-(7/9)) := by positivity
          _ = (-21 + (27 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc2 : σ ≤ (1015/1294)
  ·
    have hl : (29359/37574) ≤ σ := by linarith
    have hh : σ ≤ (1015/1294) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_second (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1283 + (4870 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 * σ) := by linarith
    have hA : (4744:ℝ)/(-1283 + (4870 * σ)) ≤ 3/(2 * σ) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-3849 + (5122 * σ)) := by
        calc
          0 ≤ (1569622/31)*((1015/1294)-σ)+(1728404/31)*(σ-(29359/37574)) := by positivity
          _ = (-3849 + (5122 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  have hl : (1015/1294) ≤ σ := by linarith
  have hh : σ ≤ (11/14) := by linarith
  apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_third (by linarith) (by linarith) _hε)
  have hd1 : 0 < (-1693 + (6354 * σ)) := by linarith
  have hd2 : (0:ℝ) < (2 * σ) := by linarith
  have hA : (6154:ℝ)/(-1693 + (6354 * σ)) ≤ 3/(2 * σ) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (-5079 + (6754 * σ)) := by
      calc
        0 ≤ (495397/3)*((11/14)-σ)+(515659/3)*(σ-(1015/1294)) := by positivity
        _ = (-5079 + (6754 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_v7_C_2 {σ ε : ℝ} (_hlo : (11/14) ≤ σ)
    (_hhi : σ ≤ (5/6)) (_hε : 0 < ε) :
    DensityBound σ ((4 + (-4 * σ)) / (-1 + (4 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  by_cases hc0 : σ ≤ (353/447)
  ·
    have hl : (11/14) ≤ σ := by linarith
    have hh : σ ≤ (353/447) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_third (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1693 + (6354 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (4 * σ)) := by linarith
    have hA : (6154:ℝ)/(-1693 + (6354 * σ)) ≤ 4/(-1 + (4 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-618 + (800 * σ)) := by
        calc
          0 ≤ (66156/25)*((353/447)-σ)+(86156/25)*(σ-(11/14)) := by positivity
          _ = (-618 + (800 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc1 : σ ≤ (467/586)
  ·
    have hl : (353/447) ≤ σ := by linarith
    have hh : σ ≤ (467/586) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_fourth (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1065 + (3936 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (4 * σ)) := by linarith
    have hA : (3782:ℝ)/(-1065 + (3936 * σ)) ≤ 4/(-1 + (4 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-478 + (616 * σ)) := by
        calc
          0 ≤ 1172*((467/586)-σ)+1788*(σ-(353/447)) := by positivity
          _ = (-478 + (616 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc2 : σ ≤ (4/5)
  ·
    have hl : (467/586) ≤ σ := by linarith
    have hh : σ ≤ (4/5) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_fifth (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-631 + (2282 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (4 * σ)) := by linarith
    have hA : (2168:ℝ)/(-631 + (2282 * σ)) ≤ 4/(-1 + (4 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-356 + (456 * σ)) := by
        calc
          0 ≤ (21680/9)*((4/5)-σ)+(25784/9)*(σ-(467/586)) := by positivity
          _ = (-356 + (456 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc3 : σ ≤ (289/358)
  ·
    have hl : (4/5) ≤ σ := by linarith
    have hh : σ ≤ (289/358) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_dashed_first (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-631 + (2282 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (4 * σ)) := by linarith
    have hA : (2168:ℝ)/(-631 + (2282 * σ)) ≤ 4/(-1 + (4 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-356 + (456 * σ)) := by
        calc
          0 ≤ (15752/13)*((289/358)-σ)+(21680/13)*(σ-(4/5)) := by positivity
          _ = (-356 + (456 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc4 : σ ≤ (163/198)
  ·
    have hl : (289/358) ≤ σ := by linarith
    have hh : σ ≤ (163/198) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_dashed_second (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-173 + (606 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (4 * σ)) := by linarith
    have hA : (566:ℝ)/(-173 + (606 * σ)) ≤ 4/(-1 + (4 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-126 + (160 * σ)) := by
        calc
          0 ≤ 198*((163/198)-σ)+358*(σ-(289/358)) := by positivity
          _ = (-126 + (160 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  have hl : (163/198) ≤ σ := by linarith
  have hh : σ ≤ (5/6) := by linarith
  apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_cube_row3 (by linarith) (by linarith) _hε)
  have hd1 : 0 < (-11203 + (35670 * σ)) := by linarith
  have hd2 : (0:ℝ) < (-1 + (4 * σ)) := by linarith
  have hA : (31544:ℝ)/(-11203 + (35670 * σ)) ≤ 4/(-1 + (4 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (-13268 + (16504 * σ)) := by
      calc
        0 ≤ 31544*((5/6)-σ)+48048*(σ-(163/198)) := by positivity
        _ = (-13268 + (16504 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_v7_C_3 {σ ε : ℝ} (_hlo : (5/6) ≤ σ)
    (_hhi : σ < 1) (_hε : 0 < ε) :
    DensityBound σ ((6 + (-6 * σ)) / (1 + (3 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  by_cases hc0 : σ ≤ (7873/9370)
  ·
    have hl : (5/6) ≤ σ := by linarith
    have hh : σ ≤ (7873/9370) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_cube_row3 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-11203 + (35670 * σ)) := by linarith
    have hd2 : (0:ℝ) < (1 + (3 * σ)) := by linarith
    have hA : (31544:ℝ)/(-11203 + (35670 * σ)) ≤ 6/(1 + (3 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-98762 + (119388 * σ)) := by
        calc
          0 ≤ (10232040/97)*((7873/9370)-σ)+(21812676/97)*(σ-(5/6)) := by positivity
          _ = (-98762 + (119388 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc1 : σ ≤ (2018/2375)
  ·
    have hl : (7873/9370) ≤ σ := by linarith
    have hh : σ ≤ (2018/2375) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_universal_row4 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-465509 + (1447460 * σ)) := by linarith
    have hd2 : (0:ℝ) < (1 + (3 * σ)) := by linarith
    have hA : (1261710:ℝ)/(-465509 + (1447460 * σ)) ≤ 6/(1 + (3 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-4054764 + (4899630 * σ)) := by
        calc
          0 ≤ 6569250*((2018/2375)-σ)+11468880*(σ-(7873/9370)) := by positivity
          _ = (-4054764 + (4899630 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc2 : σ ≤ (1959705/2298302)
  ·
    have hl : (2018/2375) ≤ σ := by linarith
    have hh : σ ≤ (1959705/2298302) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_universal_row5 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1215 + (3616 * σ)) := by linarith
    have hd2 : (0:ℝ) < (1 + (3 * σ)) := by linarith
    have hA : (3066:ℝ)/(-1215 + (3616 * σ)) ≤ 6/(1 + (3 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-10356 + (12498 * σ)) := by
        calc
          0 ≤ (2813121648/31949)*((1959705/2298302)-σ)+(3212420250/31949)*(σ-(2018/2375)) := by positivity
          _ = (-10356 + (12498 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc3 : σ ≤ (6482825/7570038)
  ·
    have hl : (1959705/2298302) ≤ σ := by linarith
    have hh : σ ≤ (6482825/7570038) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row6 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-257415 + (729216 * σ)) := by linarith
    have hd2 : (0:ℝ) < (1 + (3 * σ)) := by linarith
    have hA : (597962:ℝ)/(-257415 + (729216 * σ)) ≤ 6/(1 + (3 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-2142452 + (2581410 * σ)) := by
        calc
          0 ≤ (853268188227/53890)*((6482825/7570038)-σ)+(992380373127/53890)*(σ-(1959705/2298302)) := by positivity
          _ = (-2142452 + (2581410 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc4 : σ ≤ (2905/3354)
  ·
    have hl : (6482825/7570038) ≤ σ := by linarith
    have hh : σ ≤ (2905/3354) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row7 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-7623595 + (20732766 * σ)) := by linarith
    have hd2 : (0:ℝ) < (1 + (3 * σ)) := by linarith
    have hA : (16504356:ℝ)/(-7623595 + (20732766 * σ)) ≤ 6/(1 + (3 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-62245926 + (74883528 * σ)) := by
        calc
          0 ≤ (965479086/5)*((2905/3354)-σ)+(1339896726/5)*(σ-(6482825/7570038)) := by positivity
          _ = (-62245926 + (74883528 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  have hl : (2905/3354) ≤ σ := by linarith
  have hh : σ ≤ (7/8) := by linarith
  apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row8 (by linarith) (by linarith) _hε)
  have hd1 : 0 < (-1015 + (2742 * σ)) := by linarith
  have hd2 : (0:ℝ) < (1 + (3 * σ)) := by linarith
  have hA : (2172:ℝ)/(-1015 + (2742 * σ)) ≤ 6/(1 + (3 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (-8262 + (9936 * σ)) := by
      calc
        0 ≤ (4613328/119)*((7/8)-σ)+(5795712/119)*(σ-(2905/3354)) := by positivity
        _ = (-8262 + (9936 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_v7_D1_1 {σ ε : ℝ} (_hlo : (5/6) ≤ σ)
    (_hhi : σ ≤ (67/80)) (_hε : 0 < ε) :
    DensityBound σ ((4 + (-4 * σ)) / (-1 + (4 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  have hl : (5/6) ≤ σ := by linarith
  have hh : σ ≤ (67/80) := by linarith
  apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_cube_row3 (by linarith) (by linarith) _hε)
  have hd1 : 0 < (-11203 + (35670 * σ)) := by linarith
  have hd2 : (0:ℝ) < (-1 + (4 * σ)) := by linarith
  have hA : (31544:ℝ)/(-11203 + (35670 * σ)) ≤ 4/(-1 + (4 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (-13268 + (16504 * σ)) := by
      calc
        0 ≤ 116480*((67/80)-σ)+132984*(σ-(5/6)) := by positivity
        _ = (-13268 + (16504 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_v7_D1_2 {σ ε : ℝ} (_hlo : (67/80) ≤ σ)
    (_hhi : σ < 1) (_hε : 0 < ε) :
    DensityBound σ ((39 + (-39 * σ)) / (7 + (19 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  by_cases hc0 : σ ≤ (7873/9370)
  ·
    have hl : (67/80) ≤ σ := by linarith
    have hh : σ ≤ (7873/9370) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_cube_row3 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-11203 + (35670 * σ)) := by linarith
    have hd2 : (0:ℝ) < (7 + (19 * σ)) := by linarith
    have hA : (31544:ℝ)/(-11203 + (35670 * σ)) ≤ 39/(7 + (19 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-657725 + (791794 * σ)) := by
        calc
          0 ≤ (404969526/205)*((7873/9370)-σ)+(567287296/205)*(σ-(67/80)) := by positivity
          _ = (-657725 + (791794 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc1 : σ ≤ (2018/2375)
  ·
    have hl : (7873/9370) ≤ σ := by linarith
    have hh : σ ≤ (2018/2375) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_universal_row4 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-465509 + (1447460 * σ)) := by linarith
    have hd2 : (0:ℝ) < (7 + (19 * σ)) := by linarith
    have hA : (1261710:ℝ)/(-465509 + (1447460 * σ)) ≤ 39/(7 + (19 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-26986821 + (32478450 * σ)) := by
        calc
          0 ≤ 32034000*((2018/2375)-σ)+64512450*(σ-(7873/9370)) := by positivity
          _ = (-26986821 + (32478450 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc2 : σ ≤ (1959705/2298302)
  ·
    have hl : (2018/2375) ≤ σ := by linarith
    have hh : σ ≤ (1959705/2298302) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_universal_row5 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1215 + (3616 * σ)) := by linarith
    have hd2 : (0:ℝ) < (7 + (19 * σ)) := by linarith
    have hA : (3066:ℝ)/(-1215 + (3616 * σ)) ≤ 39/(7 + (19 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-68847 + (82770 * σ)) := by
        calc
          0 ≤ (15823809270/31949)*((1959705/2298302)-σ)+(18468228000/31949)*(σ-(2018/2375)) := by positivity
          _ = (-68847 + (82770 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc3 : σ ≤ (6482825/7570038)
  ·
    have hl : (1959705/2298302) ≤ σ := by linarith
    have hh : σ ≤ (6482825/7570038) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row6 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-257415 + (729216 * σ)) := by linarith
    have hd2 : (0:ℝ) < (7 + (19 * σ)) := by linarith
    have hA : (597962:ℝ)/(-257415 + (729216 * σ)) ≤ 39/(7 + (19 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-14224919 + (17078146 * σ)) := by
        calc
          0 ≤ (2452722592152/26945)*((6482825/7570038)-σ)+(2912893236122/26945)*(σ-(1959705/2298302)) := by positivity
          _ = (-14224919 + (17078146 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc4 : σ ≤ (2905/3354)
  ·
    have hl : (6482825/7570038) ≤ σ := by linarith
    have hh : σ ≤ (2905/3354) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row7 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-7623595 + (20732766 * σ)) := by linarith
    have hd2 : (0:ℝ) < (7 + (19 * σ)) := by linarith
    have hA : (16504356:ℝ)/(-7623595 + (20732766 * σ)) ≤ 39/(7 + (19 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-412850697 + (494995110 * σ)) := by
        calc
          0 ≤ (5667861992/5)*((2905/3354)-σ)+(8142837542/5)*(σ-(6482825/7570038)) := by positivity
          _ = (-412850697 + (494995110 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  have hl : (2905/3354) ≤ σ := by linarith
  have hh : σ ≤ (7/8) := by linarith
  apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row8 (by linarith) (by linarith) _hε)
  have hd1 : 0 < (-1015 + (2742 * σ)) := by linarith
  have hd2 : (0:ℝ) < (7 + (19 * σ)) := by linarith
  have hA : (2172:ℝ)/(-1015 + (2742 * σ)) ≤ 39/(7 + (19 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (-54789 + (65670 * σ)) := by
      calc
        0 ≤ (4005168/17)*((7/8)-σ)+(5121558/17)*(σ-(2905/3354)) := by positivity
        _ = (-54789 + (65670 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_v7_D2_1 {σ ε : ℝ} (_hlo : (6/7) ≤ σ)
    (_hhi : σ ≤ (69/80)) (_hε : 0 < ε) :
    DensityBound σ ((39 + (-39 * σ)) / (-27 + (59 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  have hl : (6/7) ≤ σ := by linarith
  have hh : σ ≤ (69/80) := by linarith
  apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row7 (by linarith) (by linarith) _hε)
  have hd1 : 0 < (-7623595 + (20732766 * σ)) := by linarith
  have hd2 : (0:ℝ) < (-27 + (59 * σ)) := by linarith
  have hA : (16504356:ℝ)/(-7623595 + (20732766 * σ)) ≤ 39/(-27 + (59 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (148297407 + (-165179130 * σ)) := by
      calc
        0 ≤ 1253521840*((69/80)-σ)+1088342710*(σ-(6/7)) := by positivity
        _ = (148297407 + (-165179130 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_v7_D2_2 {σ ε : ℝ} (_hlo : (69/80) ≤ σ)
    (_hhi : σ ≤ (51/58)) (_hε : 0 < ε) :
    DensityBound σ ((4 + (-4 * σ)) / (-1 + (4 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  by_cases hc0 : σ ≤ (2905/3354)
  ·
    have hl : (69/80) ≤ σ := by linarith
    have hh : σ ≤ (2905/3354) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row7 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-7623595 + (20732766 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (4 * σ)) := by linarith
    have hA : (16504356:ℝ)/(-7623595 + (20732766 * σ)) ≤ 4/(-1 + (4 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-13990024 + (16913640 * σ)) := by
        calc
          0 ≤ (80226405480/487)*((2905/3354)-σ)+(88463348160/487)*(σ-(69/80)) := by positivity
          _ = (-13990024 + (16913640 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  have hl : (2905/3354) ≤ σ := by linarith
  have hh : σ ≤ (7/8) := by linarith
  apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row8 (by linarith) (by linarith) _hε)
  have hd1 : 0 < (-1015 + (2742 * σ)) := by linarith
  have hd2 : (0:ℝ) < (-1 + (4 * σ)) := by linarith
  have hA : (2172:ℝ)/(-1015 + (2742 * σ)) ≤ 4/(-1 + (4 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (-1888 + (2280 * σ)) := by
      calc
        0 ≤ (1164192/119)*((7/8)-σ)+(1435512/119)*(σ-(2905/3354)) := by positivity
        _ = (-1888 + (2280 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_v7_D2_3 {σ ε : ℝ} (_hlo : (51/58) ≤ σ)
    (_hhi : σ < 1) (_hε : 0 < ε) :
    DensityBound σ ((42 + (-42 * σ)) / (15 + (13 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  linarith
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_v7_coprime_cubic {σ ε : ℝ} (_hlo : (37/50) ≤ σ)
    (_hhi : σ ≤ (315/418)) (_hε : 0 < ε) :
    DensityBound σ ((333 + (-333 * σ)) / (-12 + (227 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  by_cases hc0 : σ ≤ (3/4)
  ·
    have hl : (37/50) ≤ σ := by linarith
    have hh : σ ≤ (3/4) := by linarith
    apply density_weaken (Montgomery.RationalMoment.third_density_segment (by linarith) (by linarith) _hε)
    have hd1 : 0 < (7 + (153 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-12 + (227 * σ)) := by linarith
    have hA : (255:ℝ)/(7 + (153 * σ)) ≤ 333/(-12 + (227 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (5391 + (-6936 * σ)) := by
        calc
          0 ≤ 25836*((3/4)-σ)+18900*(σ-(37/50)) := by positivity
          _ = (5391 + (-6936 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  have hl : (3/4) ≤ σ := by linarith
  have hh : σ ≤ (315/418) := by linarith
  apply density_weaken (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) _hε)
  have hd1 : 0 < (2 * σ) := by linarith
  have hd2 : (0:ℝ) < (-12 + (227 * σ)) := by linarith
  have hA : (3:ℝ)/(2 * σ) ≤ 333/(-12 + (227 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (36 + (-15 * σ)) := by
      calc
        0 ≤ 6897*((315/418)-σ)+6882*(σ-(3/4)) := by positivity
        _ = (36 + (-15 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_v7_coprime_quadratic {σ ε : ℝ} (_hlo : (201+Real.sqrt 145)/272 ≤ σ)
    (_hhi : σ ≤ (9/10)) (_hε : 0 < ε) :
    DensityBound σ ((4 + (-4 * σ)) / (-1 + (4 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  have _hloR : (3132/4000 : ℝ) ≤ σ := source_transition_endpoint_bounds.1.trans _hlo
  by_cases hc0 : σ ≤ (1015/1294)
  ·
    have hl : (783/1000) ≤ σ := by linarith
    have hh : σ ≤ (1015/1294) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_second (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1283 + (4870 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (4 * σ)) := by linarith
    have hA : (4744:ℝ)/(-1283 + (4870 * σ)) ≤ 4/(-1 + (4 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-388 + (504 * σ)) := by
        calc
          0 ≤ (4290904/899)*((1015/1294)-σ)+(4744000/899)*(σ-(783/1000)) := by positivity
          _ = (-388 + (504 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc1 : σ ≤ (353/447)
  ·
    have hl : (1015/1294) ≤ σ := by linarith
    have hh : σ ≤ (353/447) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_third (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1693 + (6354 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (4 * σ)) := by linarith
    have hA : (6154:ℝ)/(-1693 + (6354 * σ)) ≤ 4/(-1 + (4 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-618 + (800 * σ)) := by
        calc
          0 ≤ 1788*((353/447)-σ)+2588*(σ-(1015/1294)) := by positivity
          _ = (-618 + (800 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc2 : σ ≤ (467/586)
  ·
    have hl : (353/447) ≤ σ := by linarith
    have hh : σ ≤ (467/586) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_fourth (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1065 + (3936 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (4 * σ)) := by linarith
    have hA : (3782:ℝ)/(-1065 + (3936 * σ)) ≤ 4/(-1 + (4 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-478 + (616 * σ)) := by
        calc
          0 ≤ 1172*((467/586)-σ)+1788*(σ-(353/447)) := by positivity
          _ = (-478 + (616 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc3 : σ ≤ (4/5)
  ·
    have hl : (467/586) ≤ σ := by linarith
    have hh : σ ≤ (4/5) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_fifth (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-631 + (2282 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (4 * σ)) := by linarith
    have hA : (2168:ℝ)/(-631 + (2282 * σ)) ≤ 4/(-1 + (4 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-356 + (456 * σ)) := by
        calc
          0 ≤ (21680/9)*((4/5)-σ)+(25784/9)*(σ-(467/586)) := by positivity
          _ = (-356 + (456 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc4 : σ ≤ (289/358)
  ·
    have hl : (4/5) ≤ σ := by linarith
    have hh : σ ≤ (289/358) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_dashed_first (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-631 + (2282 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (4 * σ)) := by linarith
    have hA : (2168:ℝ)/(-631 + (2282 * σ)) ≤ 4/(-1 + (4 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-356 + (456 * σ)) := by
        calc
          0 ≤ (15752/13)*((289/358)-σ)+(21680/13)*(σ-(4/5)) := by positivity
          _ = (-356 + (456 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc5 : σ ≤ (163/198)
  ·
    have hl : (289/358) ≤ σ := by linarith
    have hh : σ ≤ (163/198) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_dashed_second (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-173 + (606 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (4 * σ)) := by linarith
    have hA : (566:ℝ)/(-173 + (606 * σ)) ≤ 4/(-1 + (4 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-126 + (160 * σ)) := by
        calc
          0 ≤ 198*((163/198)-σ)+358*(σ-(289/358)) := by positivity
          _ = (-126 + (160 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc6 : σ ≤ (7873/9370)
  ·
    have hl : (163/198) ≤ σ := by linarith
    have hh : σ ≤ (7873/9370) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_cube_row3 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-11203 + (35670 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (4 * σ)) := by linarith
    have hA : (31544:ℝ)/(-11203 + (35670 * σ)) ≤ 4/(-1 + (4 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-13268 + (16504 * σ)) := by
        calc
          0 ≤ 18740*((7873/9370)-σ)+35244*(σ-(163/198)) := by positivity
          _ = (-13268 + (16504 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc7 : σ ≤ (2018/2375)
  ·
    have hl : (7873/9370) ≤ σ := by linarith
    have hh : σ ≤ (2018/2375) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_universal_row4 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-465509 + (1447460 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (4 * σ)) := by linarith
    have hA : (1261710:ℝ)/(-465509 + (1447460 * σ)) ≤ 4/(-1 + (4 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-600326 + (743000 * σ)) := by
        calc
          0 ≤ 2536500*((2018/2375)-σ)+3279500*(σ-(7873/9370)) := by positivity
          _ = (-600326 + (743000 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc8 : σ ≤ (1959705/2298302)
  ·
    have hl : (2018/2375) ≤ σ := by linarith
    have hh : σ ≤ (1959705/2298302) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_universal_row5 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1215 + (3616 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (4 * σ)) := by linarith
    have hA : (3066:ℝ)/(-1215 + (3616 * σ)) ≤ 4/(-1 + (4 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-1794 + (2200 * σ)) := by
        calc
          0 ≤ (804405700/31949)*((1959705/2298302)-σ)+(874693500/31949)*(σ-(2018/2375)) := by positivity
          _ = (-1794 + (2200 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc9 : σ ≤ (6482825/7570038)
  ·
    have hl : (1959705/2298302) ≤ σ := by linarith
    have hh : σ ≤ (6482825/7570038) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row6 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-257415 + (729216 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (4 * σ)) := by linarith
    have hA : (597962:ℝ)/(-257415 + (729216 * σ)) ≤ 4/(-1 + (4 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-431698 + (525016 * σ)) := by
        calc
          0 ≤ (116166018129/26945)*((6482825/7570038)-σ)+(130312574249/26945)*(σ-(1959705/2298302)) := by positivity
          _ = (-431698 + (525016 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc10 : σ ≤ (2905/3354)
  ·
    have hl : (6482825/7570038) ≤ σ := by linarith
    have hh : σ ≤ (2905/3354) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row7 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-7623595 + (20732766 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-1 + (4 * σ)) := by linarith
    have hA : (16504356:ℝ)/(-7623595 + (20732766 * σ)) ≤ 4/(-1 + (4 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-13990024 + (16913640 * σ)) := by
        calc
          0 ≤ (253560164/5)*((2905/3354)-σ)+(338128364/5)*(σ-(6482825/7570038)) := by positivity
          _ = (-13990024 + (16913640 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  have hl : (2905/3354) ≤ σ := by linarith
  have hh : σ ≤ (7/8) := by linarith
  apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row8 (by linarith) (by linarith) _hε)
  have hd1 : 0 < (-1015 + (2742 * σ)) := by linarith
  have hd2 : (0:ℝ) < (-1 + (4 * σ)) := by linarith
  have hA : (2172:ℝ)/(-1015 + (2742 * σ)) ≤ 4/(-1 + (4 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (-1888 + (2280 * σ)) := by
      calc
        0 ≤ (1164192/119)*((7/8)-σ)+(1435512/119)*(σ-(2905/3354)) := by positivity
        _ = (-1888 + (2280 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_v7_transition_first {σ ε : ℝ} (_hlo : (13/17) ≤ σ)
    (_hhi : σ ≤ (23/30)) (_hε : 0 < ε) :
    DensityBound σ ((-36 + (44 * σ)) / (-31 + (34 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  have hl : (13/17) ≤ σ := by linarith
  have hh : σ ≤ (23/30) := by linarith
  apply density_weaken (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) _hε)
  have hd1 : 0 < (2 * σ) := by linarith
  have hden : 0 ≤ ((30999999/1000000) + (-65 * σ) + (34 * (σ)^2)) := by
    calc
      0 ≤ (3059997399/10000)*((23/30)-σ)^2+(3026847399/5000)*(σ-(13/17))*((23/30)-σ)+(2994037399/10000)*(σ-(13/17))^2 := by positivity
      _ = ((30999999/1000000) + (-65 * σ) + (34 * (σ)^2)) := by ring
  have hd2 : (0:ℝ) < (31 + (-65 * σ) + (34 * (σ)^2)) := by linarith
  have hA : (3:ℝ)/(2 * σ) ≤ (36 + (-44 * σ))/(31 + (-65 * σ) + (34 * (σ)^2)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (-93 + (-190 * (σ)^2) + (267 * σ)) := by
      calc
        0 ≤ 18000*((23/30)-σ)^2+23970*(σ-(13/17))*((23/30)-σ)+5780*(σ-(13/17))^2 := by positivity
        _ = (-93 + (-190 * (σ)^2) + (267 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  have hpd : ((-31 + (34 * σ)):ℝ) ≠ 0 := by linarith
  calc
    _ = (3:ℝ)/(2 * σ)*(1-σ) := by ring
    _ ≤ (36 + (-44 * σ))/(31 + (-65 * σ) + (34 * (σ)^2))*(1-σ) := hp
    _ = ((-36 + (44 * σ)) / (-31 + (34 * σ))) := by
      rw [div_mul_eq_mul_div]
      apply (div_eq_div_iff (ne_of_gt hd2) hpd).2
      ring
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_v7_transition_second {σ ε : ℝ} (_hlo : (7/9) ≤ σ)
    (_hhi : σ ≤ (201+Real.sqrt 145)/272) (_hε : 0 < ε) :
    DensityBound σ ((-18 + (21 * σ)) / (-14 + (13 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  have _hhiR : σ ≤ (3133/4000 : ℝ) := _hhi.trans source_transition_endpoint_bounds.2
  by_cases hc0 : σ ≤ (29359/37574)
  ·
    have hl : (7/9) ≤ σ := by linarith
    have hh : σ ≤ (29359/37574) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_first (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-7 + (11 * σ)) := by linarith
    have hden : 0 ≤ ((13999999/1000000) + (-27 * σ) + (13 * (σ)^2)) := by
      calc
        0 ≤ (24706567240939111/367842250000)*((29359/37574)-σ)^2+(24359040618189111/183921125000)*(σ-(7/9))*((29359/37574)-σ)+(24016295944689111/367842250000)*(σ-(7/9))^2 := by positivity
        _ = ((13999999/1000000) + (-27 * σ) + (13 * (σ)^2)) := by ring
    have hd2 : (0:ℝ) < (14 + (-27 * σ) + (13 * (σ)^2)) := by linarith
    have hA : (3:ℝ)/(-7 + (11 * σ)) ≤ (18 + (-21 * σ))/(14 + (-27 * σ) + (13 * (σ)^2)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-168 + (-270 * (σ)^2) + (426 * σ)) := by
        calc
          0 ≤ (2028996/1213)*(σ-(7/9))*((29359/37574)-σ)+(1701486/1213)*(σ-(7/9))^2 := by positivity
          _ = (-168 + (-270 * (σ)^2) + (426 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    have hpd : ((-14 + (13 * σ)):ℝ) ≠ 0 := by linarith
    calc
      _ = (3:ℝ)/(-7 + (11 * σ))*(1-σ) := by ring
      _ ≤ (18 + (-21 * σ))/(14 + (-27 * σ) + (13 * (σ)^2))*(1-σ) := hp
      _ = ((-18 + (21 * σ)) / (-14 + (13 * σ))) := by
        rw [div_mul_eq_mul_div]
        apply (div_eq_div_iff (ne_of_gt hd2) hpd).2
        ring
  have hl : (29359/37574) ≤ σ := by linarith
  have hh : σ ≤ (3133/4000) := by linarith
  apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_second (by linarith) (by linarith) _hε)
  have hd1 : 0 < (-1283 + (4870 * σ)) := by linarith
  have hden : 0 ≤ ((13999999/1000000) + (-27 * σ) + (13 * (σ)^2)) := by
    calc
      0 ≤ (4743959692778096/20070672241)*((3133/4000)-σ)^2+(9416754075468192/20070672241)*(σ-(29359/37574))*((3133/4000)-σ)+(4673055301429229/20070672241)*(σ-(29359/37574))^2 := by positivity
      _ = ((13999999/1000000) + (-27 * σ) + (13 * (σ)^2)) := by ring
  have hd2 : (0:ℝ) < (14 + (-27 * σ) + (13 * (σ)^2)) := by linarith
  have hA : (4744:ℝ)/(-1283 + (4870 * σ)) ≤ (18 + (-21 * σ))/(14 + (-27 * σ) + (13 * (σ)^2)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (-89510 + (-163942 * (σ)^2) + (242691 * σ)) := by
      calc
        0 ≤ (161171251776000000/20070672241)*((3133/4000)-σ)^2+(178553600871076000/20070672241)*(σ-(29359/37574))*((3133/4000)-σ)+(14091922946541978/20070672241)*(σ-(29359/37574))^2 := by positivity
        _ = (-89510 + (-163942 * (σ)^2) + (242691 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  have hpd : ((-14 + (13 * σ)):ℝ) ≠ 0 := by linarith
  calc
    _ = (4744:ℝ)/(-1283 + (4870 * σ))*(1-σ) := by ring
    _ ≤ (18 + (-21 * σ))/(14 + (-27 * σ) + (13 * (σ)^2))*(1-σ) := hp
    _ = ((-18 + (21 * σ)) / (-14 + (13 * σ))) := by
      rw [div_mul_eq_mul_div]
      apply (div_eq_div_iff (ne_of_gt hd2) hpd).2
      ring
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_v7_power_first {σ ε : ℝ} (_hlo : (57/80) ≤ σ)
    (_hhi : σ ≤ (5/7)) (_hε : 0 < ε) :
    DensityBound σ ((651 + (-651 * σ)) / (-25 + (446 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  have hl : (57/80) ≤ σ := by linarith
  have hh : σ ≤ (5/7) := by linarith
  apply density_weaken (Montgomery.RationalMoment.two_term_density_first (by linarith) (by linarith) _hε)
  have hd1 : 0 < (-3 + (8 * σ)) := by linarith
  have hd2 : (0:ℝ) < (-25 + (446 * σ)) := by linarith
  have hA : (6:ℝ)/(-3 + (8 * σ)) ≤ 651/(-25 + (446 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (-1803 + (2532 * σ)) := by
      calc
        0 ≤ 588*((5/7)-σ)+3120*(σ-(57/80)) := by positivity
        _ = (-1803 + (2532 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_v7_power_second {σ ε : ℝ} (_hlo : (37/50) ≤ σ)
    (_hhi : σ ≤ (3/4)) (_hε : 0 < ε) :
    DensityBound σ ((192 + (-192 * σ)) / (-7 + (131 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  have hl : (37/50) ≤ σ := by linarith
  have hh : σ ≤ (3/4) := by linarith
  apply density_weaken (Montgomery.RationalMoment.third_density_segment (by linarith) (by linarith) _hε)
  have hd1 : 0 < (7 + (153 * σ)) := by linarith
  have hd2 : (0:ℝ) < (-7 + (131 * σ)) := by linarith
  have hA : (255:ℝ)/(7 + (153 * σ)) ≤ 192/(-7 + (131 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (3129 + (-4029 * σ)) := by
      calc
        0 ≤ 14754*((3/4)-σ)+10725*(σ-(37/50)) := by positivity
        _ = (3129 + (-4029 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_oct2_mixed_1 {σ ε : ℝ} (_hlo : (4/5) ≤ σ)
    (_hhi : σ ≤ (417/514)) (_hε : 0 < ε) :
    DensityBound σ ((121 + (-121 * σ)) / (-35 + (127 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  by_cases hc0 : σ ≤ (289/358)
  ·
    have hl : (4/5) ≤ σ := by linarith
    have hh : σ ≤ (289/358) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_dashed_first (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-631 + (2282 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-35 + (127 * σ)) := by linarith
    have hA : (2168:ℝ)/(-631 + (2282 * σ)) ≤ 121/(-35 + (127 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-471 + (786 * σ)) := by
        calc
          0 ≤ (282462/13)*((289/358)-σ)+(292680/13)*(σ-(4/5)) := by positivity
          _ = (-471 + (786 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  have hl : (289/358) ≤ σ := by linarith
  have hh : σ ≤ (417/514) := by linarith
  apply density_weaken (Montgomery.RationalMoment.RightDetector.density_dashed_second (by linarith) (by linarith) _hε)
  have hd1 : 0 < (-173 + (606 * σ)) := by linarith
  have hd2 : (0:ℝ) < (-35 + (127 * σ)) := by linarith
  have hA : (566:ℝ)/(-173 + (606 * σ)) ≤ 121/(-35 + (127 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (-1123 + (1444 * σ)) := by
      calc
        0 ≤ (1963737/185)*((417/514)-σ)+(2230877/185)*(σ-(289/358)) := by positivity
        _ = (-1123 + (1444 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_oct2_mixed_2 {σ ε : ℝ} (_hlo : (417/514) ≤ σ)
    (_hhi : σ ≤ (161/194)) (_hε : 0 < ε) :
    DensityBound σ ((116 + (-116 * σ)) / (-37 + (126 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  by_cases hc0 : σ ≤ (163/198)
  ·
    have hl : (417/514) ≤ σ := by linarith
    have hh : σ ≤ (163/198) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_dashed_second (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-173 + (606 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-37 + (126 * σ)) := by linarith
    have hA : (566:ℝ)/(-173 + (606 * σ)) ≤ 116/(-37 + (126 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (874 + (-1020 * σ)) := by
        calc
          0 ≤ (295713/76)*((163/198)-σ)+(218193/76)*(σ-(417/514)) := by positivity
          _ = (874 + (-1020 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  have hl : (163/198) ≤ σ := by linarith
  have hh : σ ≤ (161/194) := by linarith
  apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_cube_row3 (by linarith) (by linarith) _hε)
  have hd1 : 0 < (-11203 + (35670 * σ)) := by linarith
  have hd2 : (0:ℝ) < (-37 + (126 * σ)) := by linarith
  have hA : (31544:ℝ)/(-11203 + (35670 * σ)) ≤ 116/(-37 + (126 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (-132420 + (163176 * σ)) := by
      calc
        0 ≤ (1147413/4)*((161/194)-σ)+(1800117/4)*(σ-(163/198)) := by positivity
        _ = (-132420 + (163176 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_oct2_mixed_3 {σ ε : ℝ} (_hlo : (161/194) ≤ σ)
    (_hhi : σ ≤ (19/22)) (_hε : 0 < ε) :
    DensityBound σ ((27 + (-27 * σ)) / (-10 + (31 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  by_cases hc0 : σ ≤ (7873/9370)
  ·
    have hl : (161/194) ≤ σ := by linarith
    have hh : σ ≤ (7873/9370) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_cube_row3 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-11203 + (35670 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-10 + (31 * σ)) := by linarith
    have hA : (31544:ℝ)/(-11203 + (35670 * σ)) ≤ 27/(-10 + (31 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (12959 + (-14774 * σ)) := by
        calc
          0 ≤ (1958330/29)*((7873/9370)-σ)+(1529884/29)*(σ-(161/194)) := by positivity
          _ = (12959 + (-14774 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc1 : σ ≤ (2018/2375)
  ·
    have hl : (7873/9370) ≤ σ := by linarith
    have hh : σ ≤ (2018/2375) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_universal_row4 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-465509 + (1447460 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-10 + (31 * σ)) := by linarith
    have hA : (1261710:ℝ)/(-465509 + (1447460 * σ)) ≤ 27/(-10 + (31 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (48357 + (-31590 * σ)) := by
        calc
          0 ≤ 2308500*((2018/2375)-σ)+2276910*(σ-(7873/9370)) := by positivity
          _ = (48357 + (-31590 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc2 : σ ≤ (1959705/2298302)
  ·
    have hl : (2018/2375) ≤ σ := by linarith
    have hh : σ ≤ (1959705/2298302) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_universal_row5 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1215 + (3616 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-10 + (31 * σ)) := by linarith
    have hA : (3066:ℝ)/(-1215 + (3616 * σ)) ≤ 27/(-10 + (31 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-2145 + (2586 * σ)) := by
        calc
          0 ≤ (558487386/31949)*((1959705/2298302)-σ)+(641107500/31949)*(σ-(2018/2375)) := by positivity
          _ = (-2145 + (2586 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc3 : σ ≤ (6482825/7570038)
  ·
    have hl : (1959705/2298302) ≤ σ := by linarith
    have hh : σ ≤ (6482825/7570038) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row6 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-257415 + (729216 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-10 + (31 * σ)) := by linarith
    have hA : (597962:ℝ)/(-257415 + (729216 * σ)) ≤ 27/(-10 + (31 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-970585 + (1152010 * σ)) := by
        calc
          0 ≤ (17028800481/5389)*((6482825/7570038)-σ)+(23236982371/5389)*(σ-(1959705/2298302)) := by positivity
          _ = (-970585 + (1152010 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  have hl : (6482825/7570038) ≤ σ := by linarith
  have hh : σ ≤ (19/22) := by linarith
  apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row7 (by linarith) (by linarith) _hε)
  have hd1 : 0 < (-7623595 + (20732766 * σ)) := by linarith
  have hd2 : (0:ℝ) < (-10 + (31 * σ)) := by linarith
  have hA : (16504356:ℝ)/(-7623595 + (20732766 * σ)) ≤ 27/(-10 + (31 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (-40793505 + (48149646 * σ)) := by
      calc
        0 ≤ (18355402047180/302143)*((19/22)-σ)+(32903480538558/302143)*(σ-(6482825/7570038)) := by positivity
        _ = (-40793505 + (48149646 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_oct2_mixed_4 {σ ε : ℝ} (_hlo : (19/22) ≤ σ)
    (_hhi : σ ≤ (23/26)) (_hε : 0 < ε) :
    DensityBound σ ((24 + (-24 * σ)) / (-11 + (30 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  by_cases hc0 : σ ≤ (2905/3354)
  ·
    have hl : (19/22) ≤ σ := by linarith
    have hh : σ ≤ (2905/3354) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row7 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-7623595 + (20732766 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-11 + (30 * σ)) := by linarith
    have hA : (16504356:ℝ)/(-7623595 + (20732766 * σ)) ≤ 24/(-11 + (30 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-1418364 + (2455704 * σ)) := by
        calc
          0 ≤ (6479243784/23)*((2905/3354)-σ)+(6535724976/23)*(σ-(19/22)) := by positivity
          _ = (-1418364 + (2455704 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  have hl : (2905/3354) ≤ σ := by linarith
  have hh : σ ≤ (7/8) := by linarith
  apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row8 (by linarith) (by linarith) _hε)
  have hd1 : 0 < (-1015 + (2742 * σ)) := by linarith
  have hd2 : (0:ℝ) < (-11 + (30 * σ)) := by linarith
  have hA : (2172:ℝ)/(-1015 + (2742 * σ)) ≤ 24/(-11 + (30 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (-468 + (648 * σ)) := by
      calc
        0 ≤ (1251072/119)*((7/8)-σ)+(1328184/119)*(σ-(2905/3354)) := by positivity
        _ = (-468 + (648 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_oct2_mixed_5 {σ ε : ℝ} (_hlo : (23/26) ≤ σ)
    (_hhi : σ < 1) (_hε : 0 < ε) :
    DensityBound σ ((6 + (-6 * σ)) / (3 + σ)) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  linarith
end Montgomery.WrittenDensity
