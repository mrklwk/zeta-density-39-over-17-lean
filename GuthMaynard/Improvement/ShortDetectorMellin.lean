module
/-
Right-contour extension reusing the audited DetectorMellin proof, whose termwise
Mellin argument is adapted from McColm TypeIICoverage, commit
2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be, MIT. Original sources unchanged.
-/
public import MathCollab.Density.DetectorMellin

@[expose] public section
open Complex MeasureTheory Set Filter MathCollab.Density
open scoped ArithmeticFunction.Moebius BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

def short_detectorPSeries : ℝ :=
  ∑' n : ℕ, (n : ℝ) ^ (-(9 / 8 : ℝ))

theorem short_summable_detectorPSeries :
    Summable (fun n : ℕ => (n : ℝ) ^ (-(9 / 8 : ℝ))) := by
  exact Real.summable_nat_rpow.mpr (by norm_num)

theorem short_detectorPSeries_nonneg : 0 ≤ short_detectorPSeries := by
  exact tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem short_norm_mollifier_LSeries_le_cutoff_pSeries {z : ℂ} {X : ℝ}
    (hz : 9 / 8 ≤ z.re) :
    ‖LSeries (mollifierDirichletCoeff X) z‖ ≤
      (⌊X⌋₊ : ℝ) * short_detectorPSeries := by
  let f : ℕ → ℂ := mollifierDirichletCoeff X
  have hAbs : 1 < z.re := by linarith
  have hLS : LSeriesSummable f z :=
    mollifierDirichletCoeff_LSeriesSummable X hAbs
  have hNorm : Summable (fun n : ℕ => ‖LSeries.term f z n‖) :=
    summable_norm_iff.mpr hLS
  have hTerm (n : ℕ) : ‖LSeries.term f z n‖ ≤
      (⌊X⌋₊ : ℝ) * (n : ℝ) ^ (-(9 / 8 : ℝ)) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hnPos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hDen : (n : ℝ) ^ (9 / 8 : ℝ) ≤ (n : ℝ) ^ z.re :=
        Real.rpow_le_rpow_of_exponent_le hnOne hz
      rw [LSeries.norm_term_eq, ite_eq_right hn]
      rw [Real.rpow_neg hnPos.le]
      have hCoeff := norm_mollifierDirichletCoeff_le_cutoff X n
      have hLeft : ‖f n‖ / (n : ℝ) ^ z.re ≤
          (⌊X⌋₊ : ℝ) / (n : ℝ) ^ z.re := by
        exact div_le_div_of_nonneg_right hCoeff (Real.rpow_nonneg hnPos.le _)
      have hRight : (⌊X⌋₊ : ℝ) / (n : ℝ) ^ z.re ≤
          (⌊X⌋₊ : ℝ) / (n : ℝ) ^ (9 / 8 : ℝ) := by
        exact div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hnPos _)
          hDen
      exact hLeft.trans hRight
  calc
    ‖LSeries f z‖ ≤ ∑' n : ℕ, ‖LSeries.term f z n‖ :=
      norm_tsum_le_tsum_norm hNorm
    _ ≤ ∑' n : ℕ, (⌊X⌋₊ : ℝ) *
        (n : ℝ) ^ (-(9 / 8 : ℝ)) := by
      exact hNorm.tsum_le_tsum hTerm
        (short_summable_detectorPSeries.mul_left (⌊X⌋₊ : ℝ))
    _ = (⌊X⌋₊ : ℝ) * short_detectorPSeries := by
      rw [short_detectorPSeries, tsum_mul_left]

set_option maxHeartbeats 800000 in
/-- The Mellin transform of the smoothed detector is genuinely integrable on
the right line `Re s = 1/2`, uniformly for the zero-density range `Re ρ ≥ 9/13`. -/
theorem short_verticalIntegrable_mellin_smoothedDetector {ρ : ℂ} {X : ℝ}
    (hρ : 9 / 13 ≤ ρ.re) :
    VerticalIntegrable (mellin (smoothedDetector ρ X)) (1 / 2 : ℝ) := by
  let line : ℝ → ℂ := fun u => ((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I
  let g : ℝ → ℂ := fun u => Complex.Gamma (line u) *
    (riemannZeta (ρ + line u) *
      zetaMollifier X (ρ + line u))
  have hGammaCont : Continuous (fun u : ℝ => Complex.Gamma (line u)) := by
    apply continuous_iff_continuousAt.2
    intro u
    have hNoPole : ∀ m : ℕ, line u ≠ -m := by
      intro m hm
      have hRe := congrArg Complex.re hm
      have hmNonneg : (0 : ℝ) ≤ m := by positivity
      simp [line] at hRe
      linarith
    exact ContinuousAt.comp' (Complex.differentiableAt_Gamma _ hNoPole).continuousAt
      (by dsimp [line]; fun_prop)
  have hZetaCont : Continuous (fun u : ℝ => riemannZeta (ρ + line u)) := by
    apply continuous_iff_continuousAt.2
    intro u
    have hzRe : 1 < (ρ + line u).re := by simp [line]; linarith
    have hzNe : ρ + line u ≠ 1 := by
      intro hz
      have hRe := congrArg Complex.re hz
      simp [line] at hRe
      linarith
    exact ContinuousAt.comp' (differentiableAt_riemannZeta hzNe).continuousAt
      (by dsimp [line]; fun_prop)
  have hMollCont : Continuous (fun u : ℝ => zetaMollifier X (ρ + line u)) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    exact ContinuousAt.comp' (differentiableAt_zetaMollifier X (ρ + line u)).continuousAt (by
      dsimp [line]; fun_prop)
  have hgCont : Continuous g := by
    exact hGammaCont.mul (hZetaCont.mul hMollCont)
  let C : ℝ := (⌊X⌋₊ : ℝ) * short_detectorPSeries
  have hDom : MeasureTheory.Integrable (fun u : ℝ =>
      C * ‖Complex.Gamma (line u)‖) := by
    have hGammaInt : MeasureTheory.Integrable
        (fun u : ℝ => Complex.Gamma (line u)) := by
      simpa [line, VerticalIntegrable] using GammaMellin.verticalIntegrable_Gamma (sigma := 1/2) (by norm_num)
    exact hGammaInt.norm.const_mul C
  have hg : MeasureTheory.Integrable g := by
    refine MeasureTheory.Integrable.mono' hDom hgCont.aestronglyMeasurable ?_
    filter_upwards with u
    have hzRe : 9 / 8 ≤ (ρ + line u).re := by simp [line]; linarith
    have hAbs : 1 < (ρ + line u).re := by linarith
    have hLSeries := short_norm_mollifier_LSeries_le_cutoff_pSeries (X := X) hzRe
    have hProduct := riemannZeta_mul_zetaMollifier_eq_LSeries
      X hAbs
    dsimp [g]
    rw [norm_mul, hProduct]
    dsimp [C]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hLSeries
      (norm_nonneg (Complex.Gamma (line u)))
  apply hg.congr
  filter_upwards with u
  have hsRe : 0 < (line u).re := by simp [line]
  have hρNonneg : 0 ≤ ρ.re := by linarith
  have hAbs : 1 < (ρ + line u).re := by simp [line]; linarith
  rw [mellin_smoothedDetector_eq (X := X) hρNonneg hsRe hAbs]
  dsimp [g]
  rw [riemannZeta_mul_zetaMollifier_eq_LSeries
    X hAbs]

set_option maxHeartbeats 800000 in
/-- Absolute convergence in the Mellin variable on `Re s = 1/2`.  The key
summability exponent is `Re ρ + 1/2 > 1`; this is exactly why the detector
works uniformly in the repaired zero-density range `Re ρ ≥ 9/13`. -/
theorem short_mellinConvergent_smoothedDetector {ρ : ℂ} {X : ℝ}
    (hρ : 9 / 13 ≤ ρ.re) :
    MellinConvergent (smoothedDetector ρ X) ((1 / 2 : ℝ) : ℂ) := by
  let f : ℕ → ℂ := mollifierDirichletCoeff X
  let s : ℂ := ((1 / 2 : ℝ) : ℂ)
  let a : ℕ → ℂ := fun n => LSeries.term f ρ n
  let term : ℕ → ℝ → ℂ := fun n t =>
    a n * ((t : ℂ) ^ (s - 1) * Real.exp (-(n : ℝ) * t))
  have hs : 0 < s.re := by simp [s]
  have hAbs : 1 < (ρ + s).re := by simp [s]; linarith
  have hLS : LSeriesSummable f (ρ + s) :=
    mollifierDirichletCoeff_LSeriesSummable X hAbs
  have hSumNorm : Summable (fun n => ‖a n‖ / (n : ℝ) ^ s.re) := by
    have hNorm : Summable (fun n => ‖LSeries.term f (ρ + s) n‖) :=
      summable_norm_iff.mpr hLS
    exact hNorm.congr fun n => by
      simpa [a] using (norm_LSeries_term_div_rpow_eq_add f ρ s n).symm
  have hTermInt (n : ℕ) : MeasureTheory.IntegrableOn (term n) (Set.Ioi 0) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [term, a, LSeries.term]
    · have hnPos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hGamma := Complex.GammaIntegral_convergent hs
      rw [← mul_zero (n : ℝ),
        ← integrableOn_Ioi_comp_mul_left_iff _ _ hnPos] at hGamma
      refine (MeasureTheory.IntegrableOn.congr_fun
        (hGamma.const_mul (1 / (((n : ℝ) : ℂ) ^ (s - 1)))) ?_ measurableSet_Ioi).const_mul (a n)
      intro t ht
      change 1 / (((n : ℝ) : ℂ) ^ (s - 1)) *
          ((Real.exp (-((n : ℝ) * t)) : ℂ) *
            ((((n : ℝ) * t : ℝ) : ℂ) ^ (s - 1))) =
        (t : ℂ) ^ (s - 1) * (Real.exp (-(n : ℝ) * t) : ℂ)
      rw [mul_comm (Real.exp _ : ℂ), ← mul_assoc, neg_mul, Complex.ofReal_mul]
      rw [Complex.mul_cpow_ofReal_nonneg hnPos.le ht.le, ← mul_assoc, one_div,
        inv_mul_cancel₀, one_mul]
      rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
      exact Or.inl (Complex.ofReal_ne_zero.mpr hnPos.ne')
  have hTermSum : Summable (fun n => ∫ t in Set.Ioi 0, ‖term n t‖) := by
    apply Summable.of_norm
    convert! hSumNorm.mul_left (Real.Gamma s.re) using 2 with n
    simp_rw [term, norm_mul (a n), integral_const_mul]
    rw [← mul_div_assoc, mul_comm (Real.Gamma _), mul_div_assoc,
      norm_mul ‖a n‖, norm_norm]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [a, LSeries.term]
    congr 1
    have hnPos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hReal := Real.integral_rpow_mul_exp_neg_mul_Ioi hs hnPos
    simp_rw [← neg_mul (n : ℝ), one_div, Real.inv_rpow hnPos.le,
      ← div_eq_inv_mul] at hReal
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), ← hReal]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp,
      norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re]
  have hSeriesInt : MeasureTheory.IntegrableOn (fun t => ∑' n, term n t) (Set.Ioi 0) :=
    integrable_tsum_of_summable_integral_norm hTermInt hTermSum
  rw [MellinConvergent]
  apply hSeriesInt.congr_fun
  · intro t ht
    have htPos : 0 < t := ht
    have hSeries := hasSum_smoothedDetector (X := X) htPos (by linarith : 0 ≤ ρ.re)
    have hMul := hSeries.mul_left ((t : ℂ) ^ (s - 1))
    calc
      ∑' n, term n t = ∑' n,
          (t : ℂ) ^ (s - 1) *
            (LSeries.term (mollifierDirichletCoeff X) ρ n *
              Complex.exp (-((n : ℝ) * t))) := by
        apply tsum_congr
        intro n
        dsimp [term, a, f]
        rw [Complex.ofReal_exp]
        push_cast
        ring_nf
      _ = (t : ℂ) ^ (s - 1) * smoothedDetector ρ X t := by
        simpa [Complex.ofReal_exp] using hMul.tsum_eq
  · exact measurableSet_Ioi


/-- Exact inversion for an arbitrary positive smoothing variable. -/
theorem short_smoothedDetector_eq_mellinInv {ρ : ℂ} {X x : ℝ}
    (hx : 0 < x) (hρ : 9/13 ≤ ρ.re) :
    smoothedDetector ρ X x = mellinInv (1/2 : ℝ)
      (fun s => Complex.Gamma s * LSeries (mollifierDirichletCoeff X) (ρ+s)) x := by
  have hInv := mellinInv_mellin_eq (1/2 : ℝ) (smoothedDetector ρ X) hx
    (short_mellinConvergent_smoothedDetector hρ)
    (short_verticalIntegrable_mellin_smoothedDetector hρ)
    (continuousAt_smoothedDetector hx (by linarith : 0 ≤ ρ.re))
  rw [← hInv, mellinInv, mellinInv]
  congr 1
  apply integral_congr_ae
  filter_upwards with u
  rw [mellin_smoothedDetector_eq (by linarith : 0 ≤ ρ.re) (by norm_num)
    (by simp; linarith)]

theorem short_smoothedDetector_eq_rightContour {ρ : ℂ} {X Y : ℝ}
    (hY : 0 < Y) (hρ : 9/13 ≤ ρ.re) :
    smoothedDetector ρ X (1/Y) =
      (((1/(2*Real.pi) : ℝ) : ℂ) * ∫ u : ℝ,
        detectorKernel ρ X Y (((1/2 : ℝ) : ℂ)+(u : ℂ)*I)) := by
  rw [short_smoothedDetector_eq_mellinInv (one_div_pos.mpr hY) hρ,
    mellinInv, Complex.real_smul]
  congr 1
  apply integral_congr_ae
  filter_upwards with u
  let s : ℂ := ((1/2 : ℝ) : ℂ)+(u : ℂ)*I
  have hAbs : 1 < (ρ+s).re := by simp [s]; linarith
  have hPow : ((1/Y : ℝ) : ℂ)^(-s) = (Y : ℂ)^s := by
    simpa using GammaMellin.cpow_neg_div_eq_reverse_cpow (x := 1) (by norm_num) hY s
  change ((1/Y : ℝ) : ℂ)^(-s) *
    (Complex.Gamma s * LSeries (mollifierDirichletCoeff X) (ρ+s)) = detectorKernel ρ X Y s
  rw [hPow, ← riemannZeta_mul_zetaMollifier_eq_LSeries X hAbs]
  unfold detectorKernel
  ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.short_summable_detectorPSeries
#print axioms GuthMaynard.Improvement.short_detectorPSeries_nonneg
#print axioms GuthMaynard.Improvement.short_norm_mollifier_LSeries_le_cutoff_pSeries
#print axioms GuthMaynard.Improvement.short_verticalIntegrable_mellin_smoothedDetector
#print axioms GuthMaynard.Improvement.short_mellinConvergent_smoothedDetector
#print axioms GuthMaynard.Improvement.short_smoothedDetector_eq_mellinInv
#print axioms GuthMaynard.Improvement.short_smoothedDetector_eq_rightContour
