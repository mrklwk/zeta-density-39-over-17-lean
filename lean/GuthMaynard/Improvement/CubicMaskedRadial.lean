import GuthMaynard.Improvement.CubicMaskPermutation
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace GuthMaynard.Improvement

def ratioMaskProduct (A B C : Set ℝ) (p : ℝ × ℝ) : ℂ :=
  A.indicator (fun _ : ℝ => (1:ℂ)) (-mellinFrequency p.1) *
    B.indicator (fun _ : ℝ => (1:ℂ)) (mellinFrequency p.1-mellinFrequency p.2) *
    C.indicator (fun _ : ℝ => (1:ℂ)) (mellinFrequency p.2)

theorem ratioMaskProduct_measurable {A B C : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    Measurable (ratioMaskProduct A B C) := by
  have hAi : Measurable (A.indicator (fun _ : ℝ => (1:ℂ))) := measurable_const.indicator hA
  have hBi : Measurable (B.indicator (fun _ : ℝ => (1:ℂ))) := measurable_const.indicator hB
  have hCi : Measurable (C.indicator (fun _ : ℝ => (1:ℂ))) := measurable_const.indicator hC
  unfold ratioMaskProduct mellinFrequency
  fun_prop

theorem ratioMaskProduct_norm_le_one (A B C : Set ℝ) (p : ℝ × ℝ) :
    ‖ratioMaskProduct A B C p‖ ≤ 1 := by
  unfold ratioMaskProduct
  by_cases hA : -mellinFrequency p.1 ∈ A <;>
    by_cases hB : mellinFrequency p.1-mellinFrequency p.2 ∈ B <;>
    by_cases hC : mellinFrequency p.2 ∈ C <;> simp [hA,hB,hC]

/-- Exact Jacobian identity with the three original masks evaluated at
(-freq(v), freq(v)-freq(y), freq(y)); no reflection or mask enlargement. -/
theorem maskedSpatialCubicMode_radial {a : ℝ → ℂ}
    (ha : ∀ x, x ≤ 0 → a x = 0) (μ : ℝ → ℝ) (L : ℝ)
    (m : ℤ × (ℤ × ℤ)) (A B C : Set ℝ) (r v y : ℝ) :
    (r:ℂ)^2*maskedSpatialCubicMode a μ L m A B C (r*v,r*y,r) =
      radialIntegrand a μ L m r (v,y)*ratioMaskProduct A B C (v,y) := by
  by_cases hr : a r = 0
  · simp [maskedSpatialCubicMode,spatialCubicMode,radialIntegrand,radialAmplitude,hr]
  by_cases hv : a (r*v) = 0
  · simp [maskedSpatialCubicMode,spatialCubicMode,radialIntegrand,radialAmplitude,mul_comm v r,hv]
  by_cases hy : a (r*y) = 0
  · simp [maskedSpatialCubicMode,spatialCubicMode,radialIntegrand,radialAmplitude,mul_comm y r,hy]
  have hrp : 0 < r := lt_of_not_ge (fun h => hr (ha r h))
  have hvp : 0 < v := by
    by_contra hn
    exact hv (ha _ (mul_nonpos_of_nonneg_of_nonpos hrp.le (le_of_not_gt hn)))
  have hyp : 0 < y := by
    by_contra hn
    exact hy (ha _ (mul_nonpos_of_nonneg_of_nonpos hrp.le (le_of_not_gt hn)))
  have h₁ : mellinFrequency r-mellinFrequency (r*v) = -mellinFrequency v := by
    rw [mellinFrequency_mul hrp.ne' hvp.ne']; ring
  have h₂ : mellinFrequency (r*v)-mellinFrequency (r*y) = mellinFrequency v-mellinFrequency y := by
    rw [mellinFrequency_mul hrp.ne' hvp.ne',mellinFrequency_mul hrp.ne' hyp.ne']; ring
  have h₃ : mellinFrequency (r*y)-mellinFrequency r = mellinFrequency y := by
    rw [mellinFrequency_mul hrp.ne' hyp.ne']; ring
  unfold maskedSpatialCubicMode
  dsimp only
  rw [h₁,h₂,h₃]
  calc
    _ = ((r:ℂ)^2*spatialCubicMode a μ L m (r*v) (r*y) r)*ratioMaskProduct A B C (v,y) := by
      unfold ratioMaskProduct; dsimp only; ring
    _ = _ := by rw [spatialCubicMode_radial ha]; rfl

/-- Actual absolute integrability of the masked radial integrand, derived
from compact radial support and the norm-one mask product. -/
theorem maskedRadialIntegrand_integrable {a : ℝ → ℂ} {μ : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hs : ∀ x, x ∉ Icc l u → a x = 0)
    (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t) (hi : Integrable μ)
    (L : ℝ) (m : ℤ × (ℤ × ℤ)) {A B C : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    Integrable (fun z : Triple => radialIntegrand a μ L m z.1 z.2*ratioMaskProduct A B C z.2) := by
  have hmeas := (radialIntegrand_measurable ha.continuous.measurable hi L m).mul
    ((ratioMaskProduct_measurable hA hB hC).comp measurable_snd)
  apply (radialIntegrand_integrable ha hl hlu hs hm h0 hi L m).norm.mono' hmeas.aestronglyMeasurable
  filter_upwards with z
  dsimp only [Pi.mul_apply,Function.comp_apply]
  rw [norm_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (ratioMaskProduct_norm_le_one A B C z.2) (norm_nonneg _)

/-- The exact masked ratio integrand itself is integrable on the full
ratio plane; restriction to the compact ratio box is therefore justified. -/
theorem maskedRadialRatio_integrable {a : ℝ → ℂ} {μ : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hs : ∀ x, x ∉ Icc l u → a x = 0)
    (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t) (hi : Integrable μ)
    (L : ℝ) (m : ℤ × (ℤ × ℤ)) {A B C : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    Integrable (fun p : ℝ × ℝ => radialKernel a L m p*ratioFourierProduct μ p*ratioMaskProduct A B C p) := by
  have hint := maskedRadialIntegrand_integrable ha hl hlu hs hm h0 hi L m hA hB hC
  have hint' : Integrable (fun z : Triple => radialIntegrand a μ L m z.1 z.2*ratioMaskProduct A B C z.2)
      (volume.prod volume) := hint
  apply hint'.integral_prod_right.congr
  filter_upwards with p
  rw [integral_mul_const]
  congr 1
  exact integral_mul_const _ _

/-- Full masked spatial integral equals the compact-ratio radial integral,
with all three complex Fourier factors and all independent masks retained. -/
theorem maskedSpatialCubicMode_radial_fubini {a : ℝ → ℂ} {μ : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hs : ∀ x, x ∉ Icc l u → a x = 0)
    (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t) (hi : Integrable μ)
    (L : ℝ) (m : ℤ × (ℤ × ℤ)) {A B C : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    (∫ x : Triple, maskedSpatialCubicMode a μ L m A B C x) =
      ∫ p in Icc (l/u) (u/l) ×ˢ Icc (l/u) (u/l),
        radialKernel a L m p*ratioFourierProduct μ p*ratioMaskProduct A B C p := by
  have ha0 : ∀ x, x ≤ 0 → a x = 0 := by
    intro x hx
    exact hs x (fun h => (not_lt_of_ge hx) (lt_of_lt_of_le hl h.1))
  have hf := maskedSpatialCubicMode_integrable ha.continuous hs hm h0 hi L m hA hB hC
  have hperm := cycleSpatial_preserving.integrable_comp_of_integrable hf
  rw [← cycleSpatial_preserving.integral_comp' (maskedSpatialCubicMode a μ L m A B C)]
  change (∫ z : Triple, maskedSpatialCubicMode a μ L m A B C (z.2.1,z.2.2,z.1) ∂volume.prod volume) = _
  change Integrable (fun z : Triple => maskedSpatialCubicMode a μ L m A B C (z.2.1,z.2.2,z.1)) (volume.prod volume) at hperm
  rw [integral_prod _ hperm]
  have hsplit : (∫ r, ∫ p : ℝ × ℝ, maskedSpatialCubicMode a μ L m A B C (p.1,p.2,r)) =
      ∫ r, ∫ x₁, ∫ x₂, maskedSpatialCubicMode a μ L m A B C (x₁,x₂,r) := by
    apply integral_congr_ae
    filter_upwards [hperm.prod_right_ae] with r hr
    exact integral_prod _ hr
  rw [hsplit]
  have hscale : (∫ r, ∫ x₁, ∫ x₂, maskedSpatialCubicMode a μ L m A B C (x₁,x₂,r)) =
      ∫ r, ∫ v, ∫ y, radialIntegrand a μ L m r (v,y)*ratioMaskProduct A B C (v,y) := by
    apply integral_congr_ae
    filter_upwards with r
    by_cases hr : r = 0
    · subst r
      simp [maskedSpatialCubicMode,spatialCubicMode,radialIntegrand,radialAmplitude,ha0 0 le_rfl]
    · rw [← two_coordinate_scaling (fun x₁ x₂ => maskedSpatialCubicMode a μ L m A B C (x₁,x₂,r)) hr]
      simp_rw [maskedSpatialCubicMode_radial ha0]
  rw [hscale]
  have hint := maskedRadialIntegrand_integrable ha hl hlu hs hm h0 hi L m hA hB hC
  have hint' : Integrable (fun z : Triple => radialIntegrand a μ L m z.1 z.2*ratioMaskProduct A B C z.2)
      (volume.prod volume) := hint
  have hmerge : (∫ r, ∫ v, ∫ y, radialIntegrand a μ L m r (v,y)*ratioMaskProduct A B C (v,y)) =
      ∫ r, ∫ p : ℝ × ℝ, radialIntegrand a μ L m r p*ratioMaskProduct A B C p := by
    apply integral_congr_ae
    filter_upwards [hint'.prod_right_ae] with r hr
    exact (integral_prod _ hr).symm
  rw [hmerge,integral_integral_swap hint']
  have hrint : ∀ p, (∫ r, radialIntegrand a μ L m r p*ratioMaskProduct A B C p) =
      radialKernel a L m p*ratioFourierProduct μ p*ratioMaskProduct A B C p := by
    intro p
    rw [integral_mul_const]
    congr 1
    exact integral_mul_const _ _
  simp_rw [hrint]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  have hz : ∀ r, radialAmplitude a p.1 p.2 r = 0 := by
    intro r
    by_contra hn
    exact hp (radialAmplitude_support hl hlu hs hn).2
  simp [radialKernel,hz]

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.ratioMaskProduct_measurable
#print axioms GuthMaynard.Improvement.ratioMaskProduct_norm_le_one
#print axioms GuthMaynard.Improvement.maskedSpatialCubicMode_radial
#print axioms GuthMaynard.Improvement.maskedRadialIntegrand_integrable
#print axioms GuthMaynard.Improvement.maskedSpatialCubicMode_radial_fubini

#print axioms GuthMaynard.Improvement.maskedRadialRatio_integrable
