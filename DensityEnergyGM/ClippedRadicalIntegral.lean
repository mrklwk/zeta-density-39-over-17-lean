module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory Set
namespace Montgomery.RationalMoment

def clippedRadicalTail (R K A B s : ℝ) : ℝ :=
  min (R ^ 2) (Real.sqrt (K * (A ^ 2 / s ^ 2 + B / s ^ 4)))

theorem clippedRadicalTail_nonneg (R K A B s : ℝ) :
    0 ≤ clippedRadicalTail R K A B s :=
  le_min (sq_nonneg _) (Real.sqrt_nonneg _)

theorem clippedRadicalTail_mono {R K K' A B s : ℝ}
    (hK : K ≤ K') (hB : 0 ≤ B) :
    clippedRadicalTail R K A B s ≤ clippedRadicalTail R K' A B s := by
  apply min_le_min_left
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_right hK (by positivity)

theorem clippedRadicalTail_integrable (R K A B Y : ℝ) :
    IntegrableOn (clippedRadicalTail R K A B) (Ioc 0 Y) := by
  have hfinite : volume (Ioc (0 : ℝ) Y) < ⊤ := by simp
  let : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) Y)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfinite⟩
  have hmeas : Measurable (clippedRadicalTail R K A B) := by
    unfold clippedRadicalTail
    fun_prop
  apply (integrable_const (R ^ 2)).mono' hmeas.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro s
  rw [Real.norm_eq_abs, abs_of_nonneg (clippedRadicalTail_nonneg _ _ _ _ _)]
  exact min_le_left _ _

theorem radical_tail_le_rational {K A B s : ℝ}
    (hK : 0 ≤ K) (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : 0 < s) :
    Real.sqrt (K * (A ^ 2 / s ^ 2 + B / s ^ 4)) ≤
      Real.sqrt K * (A * s⁻¹ + Real.sqrt B * (s⁻¹) ^ 2) := by
  have hKs := Real.sq_sqrt hK
  have hBs := Real.sq_sqrt hB
  have hK0 := Real.sqrt_nonneg K
  have hB0 := Real.sqrt_nonneg B
  have hsInv : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have hRight : 0 ≤ Real.sqrt K * (A * s⁻¹ + Real.sqrt B * (s⁻¹) ^ 2) := by positivity
  have hInside : 0 ≤ K * (A ^ 2 / s ^ 2 + B / s ^ 4) := by positivity
  have hLeft := Real.sq_sqrt hInside
  have hLeft0 := Real.sqrt_nonneg (K * (A ^ 2 / s ^ 2 + B / s ^ 4))
  have hCross : 0 ≤ 2 * K * A * Real.sqrt B * s⁻¹ ^ 3 := by positivity
  have hSq : (Real.sqrt K * (A * s⁻¹ + Real.sqrt B * s⁻¹ ^ 2)) ^ 2 =
      K * (A ^ 2 / s ^ 2 + B / s ^ 4) +
        2 * K * A * Real.sqrt B * s⁻¹ ^ 3 := by
    rw [mul_pow]
    rw [hKs]
    calc
      K * (A * s⁻¹ + Real.sqrt B * s⁻¹ ^ 2) ^ 2 =
          K * (A ^ 2 * s⁻¹ ^ 2 + Real.sqrt B ^ 2 * s⁻¹ ^ 4) +
            2 * K * A * Real.sqrt B * s⁻¹ ^ 3 := by ring
      _ = _ := by rw [hBs]; simp only [div_eq_mul_inv, inv_pow]
  nlinarith

theorem integral_inv_sq_of_pos {x Y : ℝ} (hx : 0 < x) (hY : 0 < Y) :
    (∫ s in x..Y, (s⁻¹) ^ 2) = x⁻¹ - Y⁻¹ := by
  have h := integral_zpow (a := x) (b := Y) (n := (-2 : ℤ))
    (Or.inr ⟨by norm_num, notMem_uIcc_of_lt hx hY⟩)
  norm_num [zpow_neg, one_div] at h ⊢
  linarith

/-- Explicit scalar cutoff bound before optimization. -/
theorem clipped_radical_integral_cutoff {R K A B x Y : ℝ}
    (hK : 0 ≤ K) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hx : 0 < x) (hxY : x ≤ Y) :
    (∫ s in Ioc 0 Y, clippedRadicalTail R K A B s) ≤
      R ^ 2 * x + Real.sqrt K *
        (A * Real.log (Y / x) + Real.sqrt B / x) := by
  have hY : 0 < Y := hx.trans_le hxY
  have hWhole : IntervalIntegrable (clippedRadicalTail R K A B) volume 0 Y :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hY.le).mpr
      (clippedRadicalTail_integrable R K A B Y)
  have hLow : IntervalIntegrable (clippedRadicalTail R K A B) volume 0 x := by
    apply hWhole.mono_set
    rw [uIcc_of_le hx.le, uIcc_of_le hY.le]
    exact Icc_subset_Icc le_rfl hxY
  have hHigh : IntervalIntegrable (clippedRadicalTail R K A B) volume x Y := by
    apply hWhole.mono_set
    rw [uIcc_of_le hxY, uIcc_of_le hY.le]
    exact Icc_subset_Icc hx.le le_rfl
  have hInvCont : ContinuousOn (fun s : ℝ => s⁻¹) (Icc x Y) := by
    apply continuousOn_inv₀.mono
    intro s hs
    exact ne_of_gt (hx.trans_le hs.1)
  have hInv : IntervalIntegrable (fun s : ℝ => s⁻¹) volume x Y :=
    hInvCont.intervalIntegrable_of_Icc hxY
  have hInvSq : IntervalIntegrable (fun s : ℝ => (s⁻¹) ^ 2) volume x Y :=
    (hInvCont.pow 2).intervalIntegrable_of_Icc hxY
  have hMajor : IntervalIntegrable (fun s : ℝ =>
      Real.sqrt K * (A * s⁻¹ + Real.sqrt B * (s⁻¹) ^ 2)) volume x Y :=
    ((hInv.const_mul A).add (hInvSq.const_mul (Real.sqrt B))).const_mul (Real.sqrt K)
  have hLowBound : (∫ s in 0..x, clippedRadicalTail R K A B s) ≤ R ^ 2 * x := by
    have h := intervalIntegral.integral_mono_on hx.le hLow intervalIntegrable_const
      (fun s hs => min_le_left (R ^ 2) _)
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm x] using h
  have hHighBound : (∫ s in x..Y, clippedRadicalTail R K A B s) ≤
      Real.sqrt K * (A * Real.log (Y / x) + Real.sqrt B * (x⁻¹ - Y⁻¹)) := by
    have h := intervalIntegral.integral_mono_on hxY hHigh hMajor (fun s hs =>
      (min_le_right _ _).trans (radical_tail_le_rational hK hA hB (hx.trans_le hs.1)))
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hInv.const_mul A) (hInvSq.const_mul (Real.sqrt B)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_inv_of_pos hx hY, integral_inv_sq_of_pos hx hY] at h
    exact h
  rw [← intervalIntegral.integral_of_le hY.le,
    ← intervalIntegral.integral_add_adjacent_intervals hLow hHigh]
  have hDiscard : 0 ≤ Real.sqrt K * Real.sqrt B * Y⁻¹ := by positivity
  simp only [div_eq_mul_inv] at hHighBound ⊢
  nlinarith

theorem clipped_radical_integral_cap {R K A B Y : ℝ} (hY : 0 ≤ Y) :
    (∫ s in Ioc 0 Y, clippedRadicalTail R K A B s) ≤ R ^ 2 * Y := by
  have hInt : IntervalIntegrable (clippedRadicalTail R K A B) volume 0 Y :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hY).mpr
      (clippedRadicalTail_integrable R K A B Y)
  rw [← intervalIntegral.integral_of_le hY]
  have h := intervalIntegral.integral_mono_on hY hInt intervalIntegrable_const
    (fun s hs => min_le_left (R ^ 2) _)
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm Y] using h

/-- Optimize the cutoff without hiding the logarithmic endpoint cost. -/
theorem clipped_radical_integral_optimized {R K A B Y : ℝ}
    (hR : 0 < R) (hK : 0 < K) (hA : 0 ≤ A) (hB : 0 < B) (hY : 0 ≤ Y) :
    let Q := Real.sqrt (Real.sqrt K * Real.sqrt B)
    (∫ s in Ioc 0 Y, clippedRadicalTail R K A B s) ≤
      2 * R * Q + Real.sqrt K * A * max 0 (Real.log (Y * R / Q)) := by
  let Q := Real.sqrt (Real.sqrt K * Real.sqrt B)
  change (∫ s in Ioc 0 Y, clippedRadicalTail R K A B s) ≤
    2 * R * Q + Real.sqrt K * A * max 0 (Real.log (Y * R / Q))
  have hQ : 0 < Q := Real.sqrt_pos.mpr
    (mul_pos (Real.sqrt_pos.mpr hK) (Real.sqrt_pos.mpr hB))
  have hQsq : Q ^ 2 = Real.sqrt K * Real.sqrt B :=
    Real.sq_sqrt (by positivity)
  let x := Q / R
  have hx : 0 < x := div_pos hQ hR
  have hScale : R ^ 2 * x = R * Q := by dsimp only [x]; field_simp
  have hLog : 0 ≤ Real.sqrt K * A * max 0 (Real.log (Y * R / Q)) := by positivity
  by_cases hxY : x ≤ Y
  · have h := clipped_radical_integral_cutoff (R := R) hK.le hA hB.le hx hxY
    have hTail : Real.sqrt K * (Real.sqrt B / x) = R * Q := by
      dsimp only [x]
      calc
        Real.sqrt K * (Real.sqrt B / (Q / R)) =
            (Real.sqrt K * Real.sqrt B) * R / Q := by field_simp
        _ = R * Q := by rw [← hQsq]; field_simp
    have hArg : Y / x = Y * R / Q := by dsimp only [x]; field_simp
    rw [mul_add, hScale, hTail, hArg] at h
    have hLogMono := mul_le_mul_of_nonneg_left
      (le_max_right 0 (Real.log (Y * R / Q)))
      (mul_nonneg (Real.sqrt_nonneg K) hA)
    nlinarith
  · have hcap := clipped_radical_integral_cap (R := R) (K := K) (A := A) (B := B) hY
    have hLow : R ^ 2 * Y ≤ R * Q := by
      rw [← hScale]
      exact mul_le_mul_of_nonneg_left (le_of_not_ge hxY) (sq_nonneg R)
    have hRQ : 0 ≤ R * Q := mul_nonneg hR.le hQ.le
    linarith

theorem clipped_radical_integral_log_bound {R K A B Y T : ℝ}
    (hR : 0 < R) (hK : 1 ≤ K) (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hY : 0 < Y) (hYT : Y ≤ T) (hRT : R ≤ 2 * T) (hT : 2 ≤ T) :
    (∫ s in Ioc 0 Y, clippedRadicalTail R K A B s) ≤
      2 * R * Real.sqrt (Real.sqrt K * Real.sqrt B) +
        3 * Real.sqrt K * A * Real.log T := by
  let Q := Real.sqrt (Real.sqrt K * Real.sqrt B)
  have hKpos : 0 < K := by linarith
  have hBpos : 0 < B := by linarith
  have hKroot : 1 ≤ Real.sqrt K := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hK
  have hBroot : 1 ≤ Real.sqrt B := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hB
  have hQ : 1 ≤ Q := by
    have hprod : 1 ≤ Real.sqrt K * Real.sqrt B := by nlinarith
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hprod
  have hQpos : 0 < Q := by linarith
  have hArgPos : 0 < Y * R / Q := div_pos (mul_pos hY hR) hQpos
  have hArg : Y * R / Q ≤ T ^ 3 := by
    apply (div_le_iff₀ hQpos).mpr
    have hprod : Y * R ≤ T * (2 * T) :=
      mul_le_mul hYT hRT hR.le (by linarith)
    have hTcube : T * (2 * T) ≤ T ^ 3 := by nlinarith [sq_nonneg T]
    have hQmul : T ^ 3 ≤ T ^ 3 * Q := by nlinarith [show 0 ≤ T ^ 3 by positivity]
    exact hprod.trans (hTcube.trans hQmul)
  have hLog : Real.log (Y * R / Q) ≤ 3 * Real.log T := by
    have h := Real.log_le_log hArgPos hArg
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hLogMax : max 0 (Real.log (Y * R / Q)) ≤ 3 * Real.log T := by
    exact max_le (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))) hLog
  have h := clipped_radical_integral_optimized hR hKpos hA hBpos hY.le
  change (∫ s in Ioc 0 Y, clippedRadicalTail R K A B s) ≤
    2 * R * Q + Real.sqrt K * A * max 0 (Real.log (Y * R / Q)) at h
  calc
    _ ≤ 2 * R * Q + Real.sqrt K * A * max 0 (Real.log (Y * R / Q)) := h
    _ ≤ 2 * R * Q + Real.sqrt K * A * (3 * Real.log T) := by gcongr
    _ = _ := by ring

end Montgomery.RationalMoment
