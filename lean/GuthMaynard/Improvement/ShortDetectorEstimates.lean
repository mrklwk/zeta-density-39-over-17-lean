module
/-
Adapted from the verified MathCollab.Density.DetectorEstimates and DetectorGamma.
The literal kernel and horizontal majorant are reused unchanged. The left-line
Gamma domination uses ShortDetectorGamma, and right-line Mellin integrability
uses ShortDetectorMellin, to cover beta >= 9/13. No original source is modified.
-/
public import GuthMaynard.Improvement.ShortDetectorGamma
public import GuthMaynard.Improvement.ShortDetectorMellin
public import MathCollab.Density.DetectorEstimates

@[expose] public section
set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Set Filter MathCollab.Density
open scoped Topology
namespace GuthMaynard.Improvement

/-- Continuity on every fixed negative line between -1/2 and zero. The strict
upper bound excludes the Gamma pole; no imaginary-part restriction is needed. -/
theorem short_continuous_Gamma_detector_strip {a : ℝ} (ha : -(1/2 : ℝ) ≤ a)
    (ha' : a < 0) :
    Continuous (fun t : ℝ => Complex.Gamma ((a : ℂ)+(t : ℂ)*Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply (Complex.continuousAt_Gamma _ ?_).comp (by fun_prop)
  intro m he
  have hre := congrArg Complex.re he
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero,
    Complex.neg_re, Complex.natCast_re] at hre
  by_cases hm : m = 0
  · subst m
    norm_num at hre
    linarith
  · have hm' : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
    linarith

/-- Uniform Gamma mass down to beta=9/13. The majorant is exactly twice the
already audited integrable majorant; the new negative-strip estimate supplies
its pointwise domination, including ordinate zero. -/
theorem short_uniform_detector_gamma_mass :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 9/13 ≤ β → β ≤ 1 →
      Integrable (fun t : ℝ => Complex.Gamma (((1/2-β : ℝ) : ℂ)+(t : ℂ)*Complex.I)) ∧
      Integrable (fun t : ℝ => (1+|t|)*
        ‖Complex.Gamma (((1/2-β : ℝ) : ℂ)+(t : ℂ)*Complex.I)‖) ∧
      (∫ t : ℝ, (1+|t|)*
        ‖Complex.Gamma (((1/2-β : ℝ) : ℂ)+(t : ℂ)*Complex.I)‖) ≤ C := by
  have hmajor : Integrable (fun t => 2*detectorGammaMajorant t) :=
    integrable_detectorGammaMajorant.const_mul 2
  have hnonneg : 0 ≤ ∫ t : ℝ, 2*detectorGammaMajorant t :=
    integral_nonneg (fun t => by dsimp [detectorGammaMajorant]; positivity)
  refine ⟨(∫ t : ℝ, 2*detectorGammaMajorant t)+1, by linarith, ?_⟩
  intro β hβ hβ'
  let g := fun t : ℝ => Complex.Gamma (((1/2-β : ℝ) : ℂ)+(t : ℂ)*Complex.I)
  have hg : Continuous g := short_continuous_Gamma_detector_strip (by linarith) (by linarith)
  have hbound : ∀ t : ℝ, (1+|t|)*‖g t‖ ≤ 2*detectorGammaMajorant t := by
    intro t
    have ha : 0 < β-1/2 := by linarith
    have h := short_detector_gamma_bound ha (show β-1/2 ≤ 1/2 by linarith) t
    rw [show -(β-1/2)=1/2-β by ring] at h
    have hc : 12/(β-1/2) ≤ 96 := (div_le_iff₀ ha).mpr (by linarith)
    have hh : ‖g t‖ ≤ 96*(1+|t|)*Real.exp (-|t|) :=
      h.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity))
    have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 1+|t| by positivity)
    dsimp [detectorGammaMajorant]
    convert hm using 1; ring
  have hwcont : Continuous (fun t : ℝ => (1+|t|)*‖g t‖) := by fun_prop
  have hw : Integrable (fun t : ℝ => (1+|t|)*‖g t‖) :=
    hmajor.mono' hwcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hbound t)
  have hgint : Integrable g := hw.mono' hg.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => by nlinarith [abs_nonneg t, norm_nonneg (g t)])
  refine ⟨hgint, hw, ?_⟩
  exact (integral_mono hw hmajor hbound).trans (by linarith)

/-- The right contour is absolutely integrable for independent X and Y. -/
theorem short_integrable_detectorKernel_right {ρ : ℂ} {X Y : ℝ}
    (hY : 0 < Y) (hρ : 9/13 ≤ ρ.re) :
    Integrable (fun t : ℝ => detectorKernel ρ X Y (((1/2 : ℝ) : ℂ)+(t : ℂ)*I)) := by
  let line := fun t : ℝ => ((1/2 : ℝ) : ℂ)+(t : ℂ)*I
  have hg : Integrable (fun t : ℝ => Complex.Gamma (line t) *
      LSeries (mollifierDirichletCoeff X) (ρ+line t)) := by
    have h := short_verticalIntegrable_mellin_smoothedDetector (X := X) hρ
    apply h.congr
    filter_upwards with t
    exact mellin_smoothedDetector_eq (by linarith : 0 ≤ ρ.re)
      (by simp) (by simp; linarith)
  have hp : Continuous (fun t : ℝ => (Y : ℂ)^(line t)) := by
    apply Continuous.cpow continuous_const (by dsimp [line]; fun_prop)
    intro t
    left; simpa using hY
  have hb : ∀ t : ℝ, ‖(Y : ℂ)^(line t)‖ ≤ Y^(1/2 : ℝ) := by
    intro t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
    simp [line]
  have hi := hg.bdd_mul hp.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  apply hi.congr
  filter_upwards with t
  dsimp [detectorKernel]
  rw [← riemannZeta_mul_zetaMollifier_eq_LSeries X (by simp [line]; linarith)]
  dsimp [line]
  ring

/-- The shifted contour is absolutely integrable using only linear zeta growth. -/
theorem short_integrable_detectorKernel_left {ρ : ℂ} {X Y : ℝ}
    (hY : 0 < Y) (hβ : 9/13 ≤ ρ.re) (hβ' : ρ.re ≤ 1) :
    Integrable (fun t : ℝ => detectorKernel ρ X Y (((1/2-ρ.re : ℝ) : ℂ)+(t : ℂ)*I)) := by
  let a : ℝ := 1/2-ρ.re
  let line := fun t : ℝ => (a : ℂ)+(t : ℂ)*I
  have he : ∀ t : ℝ, ρ+line t = (1/2 : ℂ)+((ρ.im+t : ℝ) : ℂ)*I := by
    intro t
    apply Complex.ext <;> simp [line, a]
  have hg := (short_uniform_detector_gamma_mass.choose_spec.2 ρ.re hβ hβ').2.1
  have hc : Continuous (fun t : ℝ => detectorKernel ρ X Y (line t)) := by
    unfold detectorKernel
    apply Continuous.mul
    · apply Continuous.mul
      · apply Continuous.mul
        · apply Continuous.cpow continuous_const (by dsimp [line]; fun_prop)
          intro t
          left; simpa using hY
        · exact short_continuous_Gamma_detector_strip (by dsimp [a]; linarith) (by dsimp [a]; linarith)
      · apply continuous_iff_continuousAt.mpr
        intro t
        exact ContinuousAt.comp' (differentiableAt_zetaMollifier X (ρ+line t)).continuousAt
          (by dsimp [line]; fun_prop)
    · apply continuous_iff_continuousAt.mpr
      intro t
      apply ContinuousAt.comp' (differentiableAt_riemannZeta ?_).continuousAt
        (by dsimp [line]; fun_prop)
      rw [he]
      intro h
      have hr := congrArg Complex.re h
      norm_num at hr
  let C : ℝ := Y^a*(⌊X⌋₊ : ℝ)*4*(1+|ρ.im|)
  have hbound : ∀ t : ℝ, ‖detectorKernel ρ X Y (line t)‖ ≤
      C*((1+|t|)*‖Complex.Gamma (line t)‖) := by
    intro t
    have hm := norm_zetaMollifier_le_cutoff X (s := ρ+line t) (by rw [he]; norm_num)
    have hz := norm_riemannZeta_critical_le_linear (ρ.im+t)
    rw [← he] at hz
    have hab := abs_add_le ρ.im t
    have hzt : ‖riemannZeta (ρ+line t)‖ ≤ 4*(1+|ρ.im|)*(1+|t|) := by
      nlinarith [mul_nonneg (abs_nonneg ρ.im) (abs_nonneg t)]
    dsimp [detectorKernel]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY]
    have hre : (line t).re = a := by simp [line]
    rw [hre]
    calc
      _ ≤ (Y^a*‖Complex.Gamma (line t)‖)*(⌊X⌋₊ : ℝ)*(4*(1+|ρ.im|)*(1+|t|)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hm (by positivity)) hzt (norm_nonneg _) (by positivity)
      _ = _ := by dsimp [C]; ring
  exact (hg.const_mul C).mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

/-- Both horizontal integrals vanish as the independent rectangle height grows. -/
theorem short_tendsto_detector_horizontal_integral {ρ : ℂ} {X Y ε : ℝ}
    (hY : 1 ≤ Y) (hβ : 9/13 ≤ ρ.re) (hβ' : ρ.re ≤ 1) (hε : |ε| = 1) :
    Tendsto (fun R : ℝ => ∫ u in (1/2-ρ.re)..(1/2 : ℝ),
      detectorKernel ρ X Y ((u : ℂ)+((ε*R : ℝ) : ℂ)*I)) atTop (𝓝 0) := by
  let C : ℝ := 60*Y^(1/2 : ℝ)*(⌊X⌋₊ : ℝ)*(2+|ρ.im|)
  apply squeeze_zero_norm' _ (tendsto_detector_horizontal_majorant C)
  filter_upwards [eventually_ge_atTop (|ρ.im|+1)] with R hR
  have hRpos : 0 < R := by linarith [abs_nonneg ρ.im]
  have he : |ε*R| = R := by rw [abs_mul, hε, one_mul, abs_of_pos hRpos]
  have hlength : |(1/2 : ℝ)-(1/2-ρ.re)| ≤ 1 := by
    rw [show (1/2 : ℝ)-(1/2-ρ.re) = ρ.re by ring,
      abs_of_nonneg (show 0 ≤ ρ.re by linarith)]
    exact hβ'
  have hpoint : ∀ u ∈ Set.uIoc (1/2-ρ.re) (1/2 : ℝ),
      ‖detectorKernel ρ X Y ((u : ℂ)+((ε*R : ℝ) : ℂ)*I)‖ ≤
        C*(1+R)^3*Real.exp (-R) := by
    intro u hu
    rw [Set.uIoc_of_le (by linarith : 1/2-ρ.re ≤ (1/2 : ℝ))] at hu
    have h := norm_detectorKernel_horizontal (ρ := ρ) (X := X) (Y := Y)
      (u := u) (t := ε*R) hY hβ' hu.1.le hu.2 (by rw [he]; exact hR)
    rw [he] at h
    exact h
  have hnonneg : 0 ≤ C*(1+R)^3*Real.exp (-R) := by dsimp [C]; positivity
  have hmul := mul_le_mul_of_nonneg_left hlength hnonneg
  exact (intervalIntegral.norm_integral_le_of_norm_le_const hpoint).trans (by simpa using hmul)

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.short_continuous_Gamma_detector_strip
#print axioms GuthMaynard.Improvement.short_uniform_detector_gamma_mass
#print axioms GuthMaynard.Improvement.short_integrable_detectorKernel_right
#print axioms GuthMaynard.Improvement.short_integrable_detectorKernel_left
#print axioms GuthMaynard.Improvement.short_tendsto_detector_horizontal_integral
