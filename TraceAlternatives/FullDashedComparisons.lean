module
public import TraceAlternatives.FullDashedDensity
public import PeakTailCombinedDensity

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector.Physical

private theorem rational_density_lt {P Q C σ A B D : ℝ}
    (hg : 0<1-σ) (hd : 0<Q*σ-C) (hd' : 0<B*σ+D)
    (hm : P*(B*σ+D)<A*(Q*σ-C)) :
    P*(1-σ)/(Q*σ-C)<A*(1-σ)/(B*σ+D) := by
  apply (div_lt_div_iff₀ hd hd').mpr
  have hh := mul_lt_mul_of_pos_left hm hg
  nlinarith only [hh]

/-- Exact comparison with the recorded Palomar baseline on the entire
original eight-piece span. All denominators and endpoint signs are checked. -/
theorem fullDashedExponent_lt_palomar {σ : ℝ}
    (hlo : 4/5≤σ) (hhi : σ≤7/8) :
    fullDashedExponent σ<3*(1-σ)/(2*σ) := by
  have hg : 0<1-σ := by linarith
  have hd : 0<2*σ+0 := by linarith
  by_cases h1 : σ≤289/358
  · rw [fullDashedExponent,ite_eq_left h1]
    simpa only [add_zero] using rational_density_lt (P:=2168) (Q:=2282) (C:=631) (A:=3) (B:=2) (D:=0) hg (by linarith) hd (by linarith)
  by_cases h2 : σ≤163/198
  · rw [fullDashedExponent,ite_eq_right h1,ite_eq_left h2]
    simpa only [add_zero] using rational_density_lt (P:=566) (Q:=606) (C:=173) (A:=3) (B:=2) (D:=0) hg (by linarith) hd (by linarith)
  by_cases h3 : σ≤7873/9370
  · rw [fullDashedExponent,ite_eq_right h1,ite_eq_right h2,ite_eq_left h3]
    simpa only [add_zero] using rational_density_lt (P:=31544) (Q:=35670) (C:=11203) (A:=3) (B:=2) (D:=0) hg (by linarith) hd (by linarith)
  by_cases h4 : σ≤2018/2375
  · rw [fullDashedExponent,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_left h4]
    simpa only [add_zero] using rational_density_lt (P:=1261710) (Q:=1447460) (C:=465509) (A:=3) (B:=2) (D:=0) hg (by linarith) hd (by linarith)
  rw [fullDashedExponent,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4]
  by_cases h5 : σ≤1959705/2298302
  · rw [sharpLaterExponent,ite_eq_left h5]
    simpa only [add_zero] using rational_density_lt (P:=3066) (Q:=3616) (C:=1215) (A:=3) (B:=2) (D:=0) hg (by linarith) hd (by linarith)
  exact sharpLaterExponent_lt_palomar (by linarith) hhi

theorem row3_lt_preserved {σ : ℝ} (hlo : 163/198<σ) (hhi : σ≤7873/9370) :
    31544*(1-σ)/(35670*σ-11203)<Montgomery.PeakTailDensity.exponent σ := by
  have hg : 0<1-σ := by linarith
  have hd : 0<35670*σ-11203 := by linarith
  unfold Montgomery.PeakTailDensity.exponent
  rw [ite_eq_right (by linarith : ¬σ≤7/9),ite_eq_right (by linarith : ¬σ≤4/5),
    ite_eq_right (by linarith : ¬σ≤289/358),ite_eq_right (by linarith : ¬σ≤163/198)]
  by_cases h0 : σ≤491/596
  · rw [ite_eq_left h0]
    apply (div_lt_iff₀ hd).mpr
    linarith
  rw [ite_eq_right h0]
  by_cases h1 : σ≤5/6
  · rw [ite_eq_left h1]
    exact rational_density_lt hg hd (by linarith) (by linarith)
  · rw [ite_eq_right h1]
    exact rational_density_lt hg hd (by linarith) (by linarith)

theorem row4_lt_preserved {σ : ℝ} (hlo : 7873/9370≤σ) (hhi : σ≤2018/2375) :
    1261710*(1-σ)/(1447460*σ-465509)<Montgomery.PeakTailDensity.exponent σ := by
  rw [preserved_peak_tail_exponent_on_sharp_rows (by linarith)]
  exact rational_density_lt (by linarith) (by linarith) (by linarith) (by linarith)

theorem row5_lt_preserved {σ : ℝ} (hlo : 2018/2375≤σ) (hhi : σ≤1959705/2298302) :
    3066*(1-σ)/(3616*σ-1215)<Montgomery.PeakTailDensity.exponent σ := by
  rw [preserved_peak_tail_exponent_on_sharp_rows (by linarith)]
  exact rational_density_lt (by linarith) (by linarith) (by linarith) (by linarith)

theorem fullDashedExponent_lt_preserved {σ : ℝ}
    (hlo : 163/198<σ) (hhi : σ≤7/8) :
    fullDashedExponent σ<Montgomery.PeakTailDensity.exponent σ := by
  have h1 : ¬σ≤289/358 := by linarith
  have h2 : ¬σ≤163/198 := by linarith
  rw [fullDashedExponent,ite_eq_right h1,ite_eq_right h2]
  by_cases h3 : σ≤7873/9370
  · rw [ite_eq_left h3]
    exact row3_lt_preserved hlo h3
  rw [ite_eq_right h3]
  by_cases h4 : σ≤2018/2375
  · rw [ite_eq_left h4]
    exact row4_lt_preserved (le_of_not_ge h3) h4
  rw [ite_eq_right h4]
  by_cases h5 : σ≤1959705/2298302
  · rw [sharpLaterExponent,ite_eq_left h5]
    exact row5_lt_preserved (le_of_not_ge h4) h5
  exact sharpLaterExponent_lt_preserved (by linarith) hhi

theorem fullDashedExponent_preserved_join :
    fullDashedExponent (163/198)=Montgomery.PeakTailDensity.exponent (163/198) := by
  norm_num [fullDashedExponent,Montgomery.PeakTailDensity.exponent]

end Montgomery.RationalMoment.RightDetector.Physical
