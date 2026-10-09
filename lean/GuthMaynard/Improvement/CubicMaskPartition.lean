import GuthMaynard.Improvement.CubicMaskPermutation
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- Exact disjoint threshold partition of the original complex spatial
integrand. The exceptional mask is still literal; no norm has been taken. -/
theorem spatialCubicMode_mask_partition (a : ℝ → ℂ) (μ : ℝ → ℝ) (L : ℝ)
    (m : ℤ × (ℤ × ℤ)) (A : Set ℝ) (x : Triple) :
    spatialCubicMode a μ L m x.1 x.2.1 x.2.2 =
      maskedSpatialCubicMode a μ L m Aᶜ Aᶜ Aᶜ x +
      maskedSpatialCubicMode a μ L m A univ univ x +
      maskedSpatialCubicMode a μ L m Aᶜ A univ x +
      maskedSpatialCubicMode a μ L m Aᶜ Aᶜ A x := by
  by_cases h₁ : mellinFrequency x.2.2-mellinFrequency x.1 ∈ A <;>
    by_cases h₂ : mellinFrequency x.1-mellinFrequency x.2.1 ∈ A <;>
    by_cases h₃ : mellinFrequency x.2.1-mellinFrequency x.2.2 ∈ A <;>
    simp [maskedSpatialCubicMode,h₁,h₂,h₃]

/-- Actual integral partition with all four integrals proved to exist from
ordinary input data. It is independent of mask boundary regularity. -/
theorem spatialCubicMode_integral_mask_partition {a : ℝ → ℂ} {μ : ℝ → ℝ}
    (ha : Continuous a) {l u : ℝ} (hs : ∀ x, x ∉ Icc l u → a x = 0)
    (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t) (hi : Integrable μ)
    (L : ℝ) (m : ℤ × (ℤ × ℤ)) {A : Set ℝ} (hA : MeasurableSet A) :
    (∫ x : Triple, spatialCubicMode a μ L m x.1 x.2.1 x.2.2) =
      (∫ x : Triple, maskedSpatialCubicMode a μ L m Aᶜ Aᶜ Aᶜ x) +
      (∫ x : Triple, maskedSpatialCubicMode a μ L m A univ univ x) +
      (∫ x : Triple, maskedSpatialCubicMode a μ L m Aᶜ A univ x) +
      (∫ x : Triple, maskedSpatialCubicMode a μ L m Aᶜ Aᶜ A x) := by
  have h₀ := maskedSpatialCubicMode_integrable ha hs hm h0 hi L m hA.compl hA.compl hA.compl
  have h₁ := maskedSpatialCubicMode_integrable ha hs hm h0 hi L m hA MeasurableSet.univ MeasurableSet.univ
  have h₂ := maskedSpatialCubicMode_integrable ha hs hm h0 hi L m hA.compl hA MeasurableSet.univ
  have h₃ := maskedSpatialCubicMode_integrable ha hs hm h0 hi L m hA.compl hA.compl hA
  simp_rw [spatialCubicMode_mask_partition a μ L m A]
  have e₁ := integral_add ((h₀.add h₁).add h₂) h₃
  have e₂ := integral_add (h₀.add h₁) h₂
  have e₃ := integral_add h₀ h₁
  simp only [Pi.add_apply] at e₁ e₂ e₃
  rw [e₁,e₂,e₃]

/-- Cyclically put the exceptional mask first in each of the three terms.
The all-low term retains all three low masks. Exact complex equality comes
before any triangle inequality or radial estimate. -/
theorem spatialCubicMode_integral_designated_partition {a : ℝ → ℂ} {μ : ℝ → ℝ}
    (ha : Continuous a) {l u : ℝ} (hs : ∀ x, x ∉ Icc l u → a x = 0)
    (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t) (hi : Integrable μ)
    (L : ℝ) (m : ℤ × (ℤ × ℤ)) {A : Set ℝ} (hA : MeasurableSet A) :
    (∫ x : Triple, spatialCubicMode a μ L m x.1 x.2.1 x.2.2) =
      (∫ x : Triple, maskedSpatialCubicMode a μ L m Aᶜ Aᶜ Aᶜ x) +
      (∫ x : Triple, maskedSpatialCubicMode a μ L m A univ univ x) +
      (∫ x : Triple, maskedSpatialCubicMode a μ L (cycleCubicMode m) A univ Aᶜ x) +
      (∫ x : Triple, maskedSpatialCubicMode a μ L (cycleCubicMode (cycleCubicMode m)) A Aᶜ Aᶜ x) := by
  rw [spatialCubicMode_integral_mask_partition ha hs hm h0 hi L m hA]
  rw [maskedSpatialCubicMode_integral_cycle a μ L m Aᶜ A univ]
  rw [maskedSpatialCubicMode_integral_cycle a μ L m Aᶜ Aᶜ A]
  rw [maskedSpatialCubicMode_integral_cycle a μ L (cycleCubicMode m) Aᶜ A Aᶜ]

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.spatialCubicMode_mask_partition
#print axioms GuthMaynard.Improvement.spatialCubicMode_integral_mask_partition
#print axioms GuthMaynard.Improvement.spatialCubicMode_integral_designated_partition
