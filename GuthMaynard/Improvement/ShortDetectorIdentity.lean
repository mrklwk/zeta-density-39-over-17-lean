module
/- Adapted from the audited MathCollab.Density.DetectorIdentity at
 eff263d7b957f99e73fd226f84b83dd826941151. Only the independently proved
 lower-real-part components are substituted; the literal detector is preserved. -/
public import GuthMaynard.Improvement.ShortDetectorContour
public import GuthMaynard.Improvement.ShortDetectorEstimates
public import MathCollab.Density.DetectorIdentity

@[expose] public section

open Complex MeasureTheory Set Filter
open MathCollab.Density MathCollab.Density.Contour
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- The exact infinite contour identity, with no Weyl premise or fixed relation
between the independent mollifier and smoothing parameters. -/
theorem short_smoothedDetector_contour_identity {ρ : ℂ} {X Y : ℝ}
    (hY : 1 ≤ Y) (hβ : 9/13 ≤ ρ.re) (hβ' : ρ.re < 1)
    (hZero : riemannZeta ρ = 0) :
    smoothedDetector ρ X (1/Y) = detectorResidue ρ X Y +
      (((1/(2*Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
        detectorKernel ρ X Y (((1/2-ρ.re : ℝ) : ℂ)+(t : ℂ)*I)) := by
  let a : ℝ := 1/2-ρ.re
  let F := detectorKernel ρ X Y
  let Jl : ℂ := ∫ t : ℝ, F ((a : ℂ)+(t : ℂ)*I)
  let Jr : ℂ := ∫ t : ℝ, F (((1/2 : ℝ) : ℂ)+(t : ℂ)*I)
  let c : ℂ := 1/(2*Real.pi*I)
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hl := intervalIntegral_tendsto_integral
    (short_integrable_detectorKernel_left (X := X) hYpos hβ hβ'.le)
    tendsto_neg_atTop_atBot (tendsto_id : Tendsto (fun R : ℝ => R) atTop atTop)
  have hr := intervalIntegral_tendsto_integral
    (short_integrable_detectorKernel_right (X := X) hYpos hβ)
    tendsto_neg_atTop_atBot (tendsto_id : Tendsto (fun R : ℝ => R) atTop atTop)
  have hb := short_tendsto_detector_horizontal_integral (X := X) hY hβ hβ'.le
    (show |(-1 : ℝ)| = 1 by norm_num)
  have ht := short_tendsto_detector_horizontal_integral (X := X) hY hβ hβ'.le
    (show |(1 : ℝ)| = 1 by norm_num)
  have hlim : Tendsto (fun R : ℝ => RectangleIntegral' F
      ((a : ℂ)-(R : ℂ)*I) (((1/2 : ℝ) : ℂ)+(R : ℂ)*I)) atTop
      (𝓝 (c*(I*Jr-I*Jl))) := by
    have h := (((hb.sub ht).add (hr.const_smul I)).sub (hl.const_smul I)).const_smul c
    simpa [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral,
      F, a, Jl, Jr, c, smul_eq_mul] using h
  have heq : ∀ᶠ R : ℝ in atTop, RectangleIntegral' F
      ((a : ℂ)-(R : ℂ)*I) (((1/2 : ℝ) : ℂ)+(R : ℂ)*I) = detectorResidue ρ X Y := by
    filter_upwards [eventually_gt_atTop |ρ.im|] with R hR
    exact short_detector_finite_rectangle_kernel_nine_thirteenths hYpos hβ hβ' hR hZero
  have he : c*(I*Jr-I*Jl) = detectorResidue ρ X Y :=
    tendsto_nhds_unique hlim ((tendsto_congr' heq).mpr tendsto_const_nhds)
  rw [short_smoothedDetector_eq_rightContour hYpos hβ]
  change (((1/(2*Real.pi) : ℝ) : ℂ)*Jr) = detectorResidue ρ X Y +
    (((1/(2*Real.pi) : ℝ) : ℂ)*Jl)
  rw [← he]
  dsimp [c]
  push_cast
  field_simp
  ring

/-- The generic actual-zeta detector, valid for every independent X and Y>=1.
The n=0 term vanishes; this is the positive-integer series with its exact residue. -/
theorem short_zeta_detector_identity {ρ : ℂ} (X : ℝ) {Y : ℝ}
    (hY : 1 ≤ Y) (hβ : 9/13 ≤ ρ.re) (hβ' : ρ.re < 1)
    (hZero : riemannZeta ρ = 0) :
    (∑' n : ℕ, (mollifierCoefficient X n : ℂ)*(n : ℂ)^(-ρ)*
      (Real.exp (-(n : ℝ)/Y) : ℂ)) =
      zetaMollifier X 1*(Y : ℂ)^(1-ρ)*Complex.Gamma (1-ρ) +
      (((1/(2*Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
        Complex.Gamma (((1/2-ρ.re : ℝ) : ℂ)+(t : ℂ)*I) *
        riemannZeta ((1/2 : ℂ)+((ρ.im+t : ℝ) : ℂ)*I) *
        zetaMollifier X ((1/2 : ℂ)+((ρ.im+t : ℝ) : ℂ)*I) *
        (Y : ℂ)^(((1/2-ρ.re : ℝ) : ℂ)+(t : ℂ)*I)) := by
  have he : (∑' n : ℕ, (mollifierCoefficient X n : ℂ)*(n : ℂ)^(-ρ)*
      (Real.exp (-(n : ℝ)/Y) : ℂ)) = smoothedDetector ρ X (1/Y) := by
    apply tsum_congr
    intro n
    exact (smoothedDetector_term_eq ρ X Y n).symm
  rw [he, short_smoothedDetector_contour_identity hY hβ hβ' hZero]
  congr 1
  · dsimp [detectorResidue]
    ring
  · congr 1
    apply integral_congr_ae
    filter_upwards with t
    have harg : ρ+(((1/2-ρ.re : ℝ) : ℂ)+(t : ℂ)*I) =
        (1/2 : ℂ)+((ρ.im+t : ℝ) : ℂ)*I := by
      apply Complex.ext <;> simp
    dsimp [detectorKernel]
    rw [harg]
    ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.short_smoothedDetector_contour_identity
#print axioms GuthMaynard.Improvement.short_zeta_detector_identity
