module
/-
Finite contour proof generalized from audited Density.DetectorContour.
The inherited analytic residue argument is adapted there from McColm's MIT
TypeIICoverage (pin2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be).
No original density sources are changed. Numerator, kernel and residue are the
same literal definitions; only the unnecessarily strong lower bound is relaxed.
-/
public import MathCollab.Density.DetectorContour

@[expose] public section
open Complex MeasureTheory Set Filter
open MathCollab.Density MathCollab.Density.ZetaGrowth MathCollab.Density.Contour
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

set_option maxHeartbeats 800000 in
/-- Finite-height rectangle shift.  The apparent pole at zero has already
been removed, so the rectangle crosses exactly the zeta pole `1 - ρ`. -/
theorem short_detector_finite_rectangle_residue {ρ : ℂ} {X Y R : ℝ}
    (hY : 0 < Y) (hβLower : 1/2 < ρ.re) (hβUpper : ρ.re < 1)
    (hR : |ρ.im| < R) (hZero : riemannZeta ρ = 0) :
    let a : ℝ := 1/2 - ρ.re
    RectangleIntegral'
      (fun s => detectorContourNumerator ρ X Y s / (s - (1 - ρ)))
      ((a : ℂ) - (R : ℂ)*I) (((1/2 : ℝ) : ℂ) + (R : ℂ)*I) =
        detectorResidue ρ X Y := by
  let a : ℝ := 1/2 - ρ.re
  let z : ℂ := (a : ℂ) - (R : ℂ) * I
  let w : ℂ := ((1 / 2 : ℝ) : ℂ) + (R : ℂ) * I
  let p : ℂ := 1 - ρ
  let N : ℂ → ℂ := detectorContourNumerator ρ X Y
  let f : ℂ → ℂ := fun s => N s / (s - p)
  let g : ℂ → ℂ := dslope N p
  have hRpos : 0 < R := lt_of_le_of_lt (abs_nonneg _) hR
  have hγLower := (abs_lt.mp hR).1
  have hγUpper := (abs_lt.mp hR).2
  have hρOne : ρ ≠ 1 := by
    intro h
    have hRe := congrArg Complex.re h
    simp at hRe
    linarith
  have hzRe : z.re ≤ w.re := by simp [z, w, a]; linarith
  have hzIm : z.im ≤ w.im := by simp [z, w]; linarith
  have hpInterior : Rectangle z w ∈ nhds p := by
    rw [rectangle_mem_nhds_iff, Set.uIoo_of_le hzRe, Set.uIoo_of_le hzIm,
      mem_reProdIm, Set.mem_Ioo, Set.mem_Ioo]
    constructor
    · simp [p, z, w, a]
      constructor <;> linarith
    · simp [p, z, w]
      constructor <;> linarith
  have hRectSubset : Rectangle z w ⊆ {s : ℂ | -(1 : ℝ) < s.re} := by
    intro s hs
    have hsBounds := (mem_Rect hzRe hzIm s).mp hs
    change -(1 : ℝ) < s.re
    have haLower : -(1 / 2 : ℝ) ≤ a := by dsimp [a]; linarith
    have hzReal : z.re = a := by simp [z]
    linarith [hsBounds.1]
  have hNdiff : DifferentiableOn ℂ N (Rectangle z w) := by
    exact (differentiableOn_detectorContourNumerator hY).mono hRectSubset
  have hgHolo : HolomorphicOn g (Rectangle z w) := by
    exact (Complex.differentiableOn_dslope hpInterior).2 hNdiff
  have hNp : N p = detectorResidue ρ X Y := by
    simpa [N, p] using detectorContourNumerator_at_pole
      (X := X) (Y := Y) hρOne hZero
  have hPrincipal : Set.EqOn
      (f - fun s => detectorResidue ρ X Y / (s - p)) g
      (Rectangle z w \ {p}) := by
    intro s hs
    have hsp : s ≠ p := by simpa using hs.2
    have hSlope := sub_smul_dslope N p s
    change f s - detectorResidue ρ X Y / (s - p) = g s
    rw [← hNp]
    dsimp [f, g]
    rw [← sub_div]
    rw [← hSlope]
    rw [smul_eq_mul, mul_div_cancel_left₀ _ (sub_ne_zero.mpr hsp)]
  have hResidue := ResidueTheoremOnRectangleWithSimplePole
    hzRe hzIm hpInterior hgHolo hPrincipal
  simpa [a, z, w, p, N, f, g] using hResidue


/-- Exact finite shift for the literal kernel; both exceptional points are
strictly interior for every independently chosen R>|Im(rho)|. -/
theorem short_detector_finite_rectangle_kernel {ρ : ℂ} {X Y R : ℝ}
    (hY : 0 < Y) (hβLower : 1/2 < ρ.re) (hβUpper : ρ.re < 1)
    (hR : |ρ.im| < R) (hZero : riemannZeta ρ = 0) :
    let a : ℝ := 1/2 - ρ.re
    RectangleIntegral' (detectorKernel ρ X Y)
      ((a : ℂ)-(R : ℂ)*I) (((1/2 : ℝ) : ℂ)+(R : ℂ)*I) =
        detectorResidue ρ X Y := by
  let a : ℝ := 1 / 2 - ρ.re
  let z : ℂ := (a : ℂ) - (R : ℂ) * I
  let w : ℂ := ((1 / 2 : ℝ) : ℂ) + (R : ℂ) * I
  have hρOne : ρ ≠ 1 := by
    intro h
    have hRe := congrArg Complex.re h
    simp at hRe
    linarith
  have hRpos : 0 < R := lt_of_le_of_lt (abs_nonneg _) hR
  have hγLower := (abs_lt.mp hR).1
  have hγUpper := (abs_lt.mp hR).2
  have hFinite := short_detector_finite_rectangle_residue (X := X) hY hβLower hβUpper hR hZero
  change RectangleIntegral' (detectorKernel ρ X Y) z w =
    detectorResidue ρ X Y
  rw [← hFinite]
  apply RectangleIntegral'_congr
  intro s hs
  have hsZero : s ≠ 0 := by
    intro hs0
    rw [hs0] at hs
    simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm,
      Set.mem_singleton_iff] at hs
    rcases hs with ((hBottom | hLeft) | hTop) | hRight
    · have : (0 : ℝ) = -R := by simpa [z, w] using hBottom.2
      linarith
    · have : (0 : ℝ) = a := by simpa [z, w] using hLeft.1
      dsimp [a] at this
      linarith
    · have : (0 : ℝ) = R := by simpa [z, w] using hTop.2
      linarith
    · have : (0 : ℝ) = 1 / 2 := by simpa [z, w] using hRight.1
      norm_num at this
  have hsPole : s ≠ 1 - ρ := by
    intro hsp
    rw [hsp] at hs
    simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm,
      Set.mem_singleton_iff] at hs
    rcases hs with ((hBottom | hLeft) | hTop) | hRight
    · have : -ρ.im = -R := by simpa [z, w] using hBottom.2
      linarith
    · have : 1 - ρ.re = a := by simpa [z, w] using hLeft.1
      dsimp [a] at this
      linarith
    · have : -ρ.im = R := by simpa [z, w] using hTop.2
      linarith
    · have : 1 - ρ.re = 1 / 2 := by simpa [z, w] using hRight.1
      linarith
  exact (detectorContourNumerator_div_eq_integrand hρOne hZero hsZero hsPole).symm


/-- The finite residue shift in the lower sigma range needed by the candidate
zero-detection port. This remains a finite contour identity, not a decay estimate. -/
theorem short_detector_finite_rectangle_residue_nine_thirteenths
    {ρ : ℂ} {X Y R : ℝ} (hY : 0 < Y) (hβLower : 9/13 ≤ ρ.re)
    (hβUpper : ρ.re < 1) (hR : |ρ.im| < R) (hZero : riemannZeta ρ = 0) :
    let a : ℝ := 1/2 - ρ.re
    RectangleIntegral'
      (fun s => detectorContourNumerator ρ X Y s / (s - (1 - ρ)))
      ((a : ℂ) - (R : ℂ)*I) (((1/2 : ℝ) : ℂ) + (R : ℂ)*I) =
        detectorResidue ρ X Y :=
  short_detector_finite_rectangle_residue hY (by linarith) hβUpper hR hZero

/-- The actual detector kernel, including its exact mollifier and residue,
satisfies the same finite shift for beta>=9/13. -/
theorem short_detector_finite_rectangle_kernel_nine_thirteenths
    {ρ : ℂ} {X Y R : ℝ} (hY : 0 < Y) (hβLower : 9/13 ≤ ρ.re)
    (hβUpper : ρ.re < 1) (hR : |ρ.im| < R) (hZero : riemannZeta ρ = 0) :
    let a : ℝ := 1/2 - ρ.re
    RectangleIntegral' (detectorKernel ρ X Y)
      ((a : ℂ)-(R : ℂ)*I) (((1/2 : ℝ) : ℂ)+(R : ℂ)*I) =
        detectorResidue ρ X Y :=
  short_detector_finite_rectangle_kernel hY (by linarith) hβUpper hR hZero

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.short_detector_finite_rectangle_residue
#print axioms GuthMaynard.Improvement.short_detector_finite_rectangle_kernel
#print axioms GuthMaynard.Improvement.short_detector_finite_rectangle_residue_nine_thirteenths
#print axioms GuthMaynard.Improvement.short_detector_finite_rectangle_kernel_nine_thirteenths
