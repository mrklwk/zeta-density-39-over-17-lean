import GuthMaynard.Improvement.Smoothing

/-! Exact restricted-mass and L2 bounds for every positive smoothing width.
Smoothness/Fourier decay and the published affine theorem are not asserted.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace GuthMaynard.Improvement

def scaledKernel (φ : ℝ → ℝ) (δ x : ℝ) : ℝ := δ⁻¹ * φ (x / δ)

theorem scaledKernel_measurable {φ : ℝ → ℝ} (hφ : Measurable φ) (δ : ℝ) :
    Measurable (scaledKernel φ δ) :=
  measurable_const.mul (hφ.comp (measurable_id.div_const δ))

theorem scaledKernel_integrable {φ : ℝ → ℝ} {δ : ℝ} (hφ : Integrable φ) (hδ : 0 < δ) :
    Integrable (scaledKernel φ δ) := (hφ.comp_div hδ.ne').const_mul δ⁻¹

theorem scaledKernel_nonneg {φ : ℝ → ℝ} {δ : ℝ}
    (hφ : ∀ x, 0 ≤ φ x) (hδ : 0 < δ) (x : ℝ) : 0 ≤ scaledKernel φ δ x :=
  mul_nonneg (inv_nonneg.mpr hδ.le) (hφ _)

theorem scaledKernel_mass {φ : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hmass : ∫ x, φ x = 1) : (∫ x, scaledKernel φ δ x) = 1 := by
  simp only [scaledKernel, integral_const_mul, Measure.integral_comp_div,
    abs_of_pos hδ, smul_eq_mul, hmass, mul_one, inv_mul_cancel₀ hδ.ne']

theorem scaledKernel_bound {φ : ℝ → ℝ} {δ B : ℝ}
    (hδ : 0 < δ) (hB : ∀ x, ‖φ x‖ ≤ B) (x : ℝ) :
    ‖scaledKernel φ δ x‖ ≤ δ⁻¹ * B := by
  simp only [scaledKernel, norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hδ)]
  exact mul_le_mul_of_nonneg_left (hB (x / δ)) (inv_nonneg.mpr hδ.le)

/-- The complete mask norm interface, with no loss in the restricted mass.
Integrability of the smoothed square is included in the conclusion. -/
theorem masked_smoothing_bounds {κ r : ℝ → ℝ} {A : Set ℝ} {B : ℝ}
    (hA : MeasurableSet A) (hκm : Measurable κ) (hκi : Integrable κ)
    (hκ0 : ∀ x, 0 ≤ κ x) (hκB : ∀ x, ‖κ x‖ ≤ B) (hmass : ∫ x, κ x = 1)
    (hr : Measurable r) (hr2 : Integrable (fun y => r y ^ 2))
    (hr4 : Integrable (fun y => r y ^ 4)) :
    Integrable (squareSmoothing κ (A.indicator r)) ∧
    Integrable (fun x => squareSmoothing κ (A.indicator r) x ^ 2) ∧
    (∫ x, squareSmoothing κ (A.indicator r) x) = ∫ y in A, r y ^ 2 ∧
    (∫ x, squareSmoothing κ (A.indicator r) x ^ 2) ≤ ∫ y in A, r y ^ 4 := by
  let g : ℝ → ℝ := A.indicator (fun y => r y ^ 2)
  have hgm : Measurable g := (hr.pow_const 2).indicator hA
  have hgi : Integrable g := hr2.indicator hA
  have hg0 : ∀ y, 0 ≤ g y := by
    intro y
    by_cases hy : y ∈ A <;> simp [g, hy, sq_nonneg]
  have hg2eq : (fun y => g y ^ 2) = A.indicator (fun y => r y ^ 4) := by
    funext y
    by_cases hy : y ∈ A
    · simp only [g, Set.indicator_of_mem hy]
      ring
    · simp [g, hy]
  have hg2 : Integrable (fun y => g y ^ 2) := by
    rw [hg2eq]
    exact hr4.indicator hA
  have heq : squareSmoothing κ (A.indicator r) = smooth κ g := by
    funext x
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ A <;> simp [g, hy]
  rw [heq]
  refine ⟨smooth_integrable hκi hgi,
    smooth_square_integrable hκm hκi hκ0 hκB hmass hgm hgi hg2 hg0, ?_, ?_⟩
  · rw [smooth_mass hκi hgi hmass]
    exact integral_indicator hA
  · have h := smooth_l2_contraction hκm hκi hκ0 hκB hmass hgm hgi hg2 hg0
    rw [hg2eq, integral_indicator hA] at h
    exact h

/-- For a fixed positive mass-one kernel, every delta>0 and every measurable
mask share contraction constant one. No constant depends on the mask or its
mass, and there is no lower bound on delta or on restricted mass. -/
theorem scaled_mask_smoothing_bounds {φ r : ℝ → ℝ} {A : Set ℝ} {B δ : ℝ}
    (hφm : Measurable φ) (hφi : Integrable φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hφB : ∀ x, ‖φ x‖ ≤ B) (hmass : ∫ x, φ x = 1)
    (hδ : 0 < δ) (hA : MeasurableSet A)
    (hr : Measurable r) (hr2 : Integrable (fun y => r y ^ 2))
    (hr4 : Integrable (fun y => r y ^ 4)) :
    Integrable (squareSmoothing (scaledKernel φ δ) (A.indicator r)) ∧
    Integrable (fun x => squareSmoothing (scaledKernel φ δ) (A.indicator r) x ^ 2) ∧
    (∫ x, squareSmoothing (scaledKernel φ δ) (A.indicator r) x) = ∫ y in A, r y ^ 2 ∧
    (∫ x, squareSmoothing (scaledKernel φ δ) (A.indicator r) x ^ 2) ≤ ∫ y in A, r y ^ 4 :=
  masked_smoothing_bounds hA (scaledKernel_measurable hφm δ)
    (scaledKernel_integrable hφi hδ) (scaledKernel_nonneg hφ0 hδ)
    (scaledKernel_bound hδ hφB) (scaledKernel_mass hδ hmass) hr hr2 hr4

end GuthMaynard.Improvement

#print axioms GuthMaynard.Improvement.scaledKernel_measurable
#print axioms GuthMaynard.Improvement.scaledKernel_integrable
#print axioms GuthMaynard.Improvement.scaledKernel_nonneg
#print axioms GuthMaynard.Improvement.scaledKernel_mass
#print axioms GuthMaynard.Improvement.scaledKernel_bound
#print axioms GuthMaynard.Improvement.masked_smoothing_bounds
#print axioms GuthMaynard.Improvement.scaled_mask_smoothing_bounds
#check @GuthMaynard.Improvement.scaled_mask_smoothing_bounds
