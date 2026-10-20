module
public import LaterPairs.PhysicalDetectorParameters

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector

/-- The full closed row3 satisfies the physical contour-detector conditions. -/
theorem physicalDetectorWindow_row3 {σ : ℝ} (hlo : 163/198 ≤ σ) (hhi : σ ≤ 7873/9370) :
    PhysicalDetectorWindow σ (31544/(107010*σ-33609)) := by
  have hd : 0 < 107010*σ-33609 := by linarith
  refine ⟨by linarith,by linarith,?_,?_,?_⟩
  · apply (le_div_iff₀ hd).mpr
    linarith
  · apply (div_lt_iff₀ hd).mpr
    linarith
  · have he : (3*(31544/(107010*σ-33609))/4)*(σ-1/2) =
        (3*31544*(σ-1/2))/(4*(107010*σ-33609)) := by field_simp
    rw [he]
    apply (lt_div_iff₀ (by positivity : 0 < 4*(107010*σ-33609))).mpr
    linarith

/-- The full closed row4 satisfies the physical contour-detector conditions. -/
theorem physicalDetectorWindow_row4 {σ : ℝ} (hlo : 7873/9370 ≤ σ) (hhi : σ ≤ 2018/2375) :
    PhysicalDetectorWindow σ (1261710/(4342380*σ-1396527)) := by
  have hd : 0 < 4342380*σ-1396527 := by linarith
  refine ⟨by linarith,by linarith,?_,?_,?_⟩
  · apply (le_div_iff₀ hd).mpr
    linarith
  · apply (div_lt_iff₀ hd).mpr
    linarith
  · have he : (3*(1261710/(4342380*σ-1396527))/4)*(σ-1/2) =
        (3*1261710*(σ-1/2))/(4*(4342380*σ-1396527)) := by field_simp
    rw [he]
    apply (lt_div_iff₀ (by positivity : 0 < 4*(4342380*σ-1396527))).mpr
    linarith

/-- The full closed row5 satisfies the physical contour-detector conditions. -/
theorem physicalDetectorWindow_row5 {σ : ℝ} (hlo : 2018/2375 ≤ σ) (hhi : σ ≤ 1959705/2298302) :
    PhysicalDetectorWindow σ (3066/(10848*σ-3645)) := by
  have hd : 0 < 10848*σ-3645 := by linarith
  refine ⟨by linarith,by linarith,?_,?_,?_⟩
  · apply (le_div_iff₀ hd).mpr
    linarith
  · apply (div_lt_iff₀ hd).mpr
    linarith
  · have he : (3*(3066/(10848*σ-3645))/4)*(σ-1/2) =
        (3*3066*(σ-1/2))/(4*(10848*σ-3645)) := by field_simp
    rw [he]
    apply (lt_div_iff₀ (by positivity : 0 < 4*(10848*σ-3645))).mpr
    linarith

/-- The full closed row6 satisfies the physical contour-detector conditions. -/
theorem physicalDetectorWindow_row6 {σ : ℝ} (hlo : 1959705/2298302 ≤ σ) (hhi : σ ≤ 6482825/7570038) :
    PhysicalDetectorWindow σ (597962/(2187648*σ-772245)) := by
  have hd : 0 < 2187648*σ-772245 := by linarith
  refine ⟨by linarith,by linarith,?_,?_,?_⟩
  · apply (le_div_iff₀ hd).mpr
    linarith
  · apply (div_lt_iff₀ hd).mpr
    linarith
  · have he : (3*(597962/(2187648*σ-772245))/4)*(σ-1/2) =
        (3*597962*(σ-1/2))/(4*(2187648*σ-772245)) := by field_simp
    rw [he]
    apply (lt_div_iff₀ (by positivity : 0 < 4*(2187648*σ-772245))).mpr
    linarith

/-- The full closed row7 satisfies the physical contour-detector conditions. -/
theorem physicalDetectorWindow_row7 {σ : ℝ} (hlo : 6482825/7570038 ≤ σ) (hhi : σ ≤ 2905/3354) :
    PhysicalDetectorWindow σ (16504356/(62198298*σ-22870785)) := by
  have hd : 0 < 62198298*σ-22870785 := by linarith
  refine ⟨by linarith,by linarith,?_,?_,?_⟩
  · apply (le_div_iff₀ hd).mpr
    linarith
  · apply (div_lt_iff₀ hd).mpr
    linarith
  · have he : (3*(16504356/(62198298*σ-22870785))/4)*(σ-1/2) =
        (3*16504356*(σ-1/2))/(4*(62198298*σ-22870785)) := by field_simp
    rw [he]
    apply (lt_div_iff₀ (by positivity : 0 < 4*(62198298*σ-22870785))).mpr
    linarith

/-- The full closed row8 satisfies the physical contour-detector conditions. -/
theorem physicalDetectorWindow_row8 {σ : ℝ} (hlo : 2905/3354 ≤ σ) (hhi : σ ≤ 7/8) :
    PhysicalDetectorWindow σ (2172/(8226*σ-3045)) := by
  have hd : 0 < 8226*σ-3045 := by linarith
  refine ⟨by linarith,by linarith,?_,?_,?_⟩
  · apply (le_div_iff₀ hd).mpr
    linarith
  · apply (div_lt_iff₀ hd).mpr
    linarith
  · have he : (3*(2172/(8226*σ-3045))/4)*(σ-1/2) =
        (3*2172*(σ-1/2))/(4*(8226*σ-3045)) := by field_simp
    rw [he]
    apply (lt_div_iff₀ (by positivity : 0 < 4*(8226*σ-3045))).mpr
    linarith

end Montgomery.RationalMoment.RightDetector
