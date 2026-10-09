import GuthMaynard.Improvement.CubicMaskPartition
import GuthMaynard.Improvement.CenteredTruncation
import GuthMaynard.Improvement.CubicModeCount
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace GuthMaynard.Improvement

def retainedCubicModes (U : ℝ) : Finset (ℤ × (ℤ × ℤ)) :=
  poissonModes U ×ˢ (poissonModes U ×ˢ poissonModes U)

def maskedRetainedCubic (a : ℝ → ℂ) (μ : ℝ → ℝ) (L U : ℝ) (A B C : Set ℝ) : ℂ :=
  (L:ℂ)^3 * ∑ m ∈ retainedCubicModes U,
    ∫ x : Triple, maskedSpatialCubicMode a μ L m A B C x

theorem retainedCubicModes_mem (U : ℝ) (m : ℤ × (ℤ × ℤ)) :
    m ∈ retainedCubicModes U ↔
      m.1 ∈ poissonModes U ∧ m.2.1 ∈ poissonModes U ∧ m.2.2 ∈ poissonModes U := by
  simp only [retainedCubicModes,Finset.mem_product]

theorem retainedCubicModes_subset (U : ℝ) : retainedCubicModes U ⊆ cubicModes U := by
  intro m hm
  obtain ⟨h₁,h₂,h₃⟩ := (retainedCubicModes_mem U m).mp hm
  exact (mem_cubicModes U m).mpr ⟨((mem_poissonModes U m.1).mp h₁).2,
    ((mem_poissonModes U m.2.1).mp h₂).2,((mem_poissonModes U m.2.2).mp h₃).2⟩

/-- The actual full retained nonzero cube is invariant under cyclic
reindexing, with no duplication or missing modes. -/
theorem retainedCubicModes_cycle (U : ℝ) :
    (retainedCubicModes U).image cycleCubicMode = retainedCubicModes U := by
  ext m
  constructor
  · intro hm
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨h₁,h₂,h₃⟩ := (retainedCubicModes_mem U n).mp hn
    exact (retainedCubicModes_mem U _).mpr ⟨h₂,h₃,h₁⟩
  · intro hm
    obtain ⟨h₁,h₂,h₃⟩ := (retainedCubicModes_mem U m).mp hm
    refine Finset.mem_image.mpr ⟨(m.2.2,m.1,m.2.1),?_,?_⟩
    · exact (retainedCubicModes_mem U _).mpr ⟨h₃,h₁,h₂⟩
    · rfl

theorem maskedRetainedCubic_cycle (a : ℝ → ℂ) (μ : ℝ → ℝ) (L U : ℝ) (A B C : Set ℝ) :
    maskedRetainedCubic a μ L U A B C = maskedRetainedCubic a μ L U B C A := by
  unfold maskedRetainedCubic
  rw [maskedSpatialCubicMode_sum_cycle,retainedCubicModes_cycle]

/-- Genuine retained time kernel cubic equals the finite sum of full
complex spatial integrals. The identity precedes threshold partition. -/
theorem retained_cubic_spatial_assembly {a : ℝ → ℂ} {μ : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hs : ∀ x, x ∉ Icc l u → a x = 0)
    (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t) (hi : Integrable μ) (L U : ℝ) :
    kernelCubic (timeMeasure μ) (retainedPoissonKernel (volume.restrict (Icc l u)) a L (poissonModes U)) =
      (L:ℂ)^3 * ∑ m ∈ retainedCubicModes U,
        ∫ x : Triple, spatialCubicMode a μ L m x.1 x.2.1 x.2.2 := by
  rw [retained_cubic_radial_assembly ha hl hlu hs hm h0 hi]
  simp only [retainedCubicModes,Finset.sum_product]
  congr 1
  apply Finset.sum_congr rfl
  intro m₁ _
  apply Finset.sum_congr rfl
  intro m₂ _
  apply Finset.sum_congr rfl
  intro m₃ _
  exact (spatialCubicMode_integral_radial ha hl hlu hs hm h0 hi L (m₁,m₂,m₃)).symm

/-- Exact threshold decomposition of the actual retained kernel cubic,
with every exceptional mask moved to the first Fourier factor. -/
theorem retained_cubic_designated_partition {a : ℝ → ℂ} {μ : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hs : ∀ x, x ∉ Icc l u → a x = 0)
    (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t) (hi : Integrable μ)
    (L U : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    kernelCubic (timeMeasure μ) (retainedPoissonKernel (volume.restrict (Icc l u)) a L (poissonModes U)) =
      maskedRetainedCubic a μ L U Aᶜ Aᶜ Aᶜ +
      maskedRetainedCubic a μ L U A univ univ +
      maskedRetainedCubic a μ L U A univ Aᶜ +
      maskedRetainedCubic a μ L U A Aᶜ Aᶜ := by
  rw [retained_cubic_spatial_assembly ha hl hlu hs hm h0 hi]
  simp_rw [spatialCubicMode_integral_mask_partition ha.continuous hs hm h0 hi L _ hA]
  simp only [Finset.sum_add_distrib,mul_add]
  change maskedRetainedCubic a μ L U Aᶜ Aᶜ Aᶜ +
      maskedRetainedCubic a μ L U A univ univ +
      maskedRetainedCubic a μ L U Aᶜ A univ +
      maskedRetainedCubic a μ L U Aᶜ Aᶜ A = _
  rw [maskedRetainedCubic_cycle a μ L U Aᶜ A univ]
  rw [maskedRetainedCubic_cycle a μ L U Aᶜ Aᶜ A]
  rw [maskedRetainedCubic_cycle a μ L U Aᶜ A Aᶜ]

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.retainedCubicModes_mem
#print axioms GuthMaynard.Improvement.retainedCubicModes_subset
#print axioms GuthMaynard.Improvement.retainedCubicModes_cycle
#print axioms GuthMaynard.Improvement.maskedRetainedCubic_cycle
#print axioms GuthMaynard.Improvement.retained_cubic_spatial_assembly
#print axioms GuthMaynard.Improvement.retained_cubic_designated_partition
