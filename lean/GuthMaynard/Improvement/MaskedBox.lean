import GuthMaynard.Improvement.MeasureGate
import GuthMaynard.Improvement.Gate
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace GuthMaynard.Improvement

theorem sqrt_product_memLp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    MemLp (fun x => Real.sqrt (f x)*Real.sqrt (g x)) 2 μ := by
  have hm := hf.aestronglyMeasurable.aemeasurable.sqrt.aestronglyMeasurable.mul
    hg.aestronglyMeasurable.aemeasurable.sqrt.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).2
  change Integrable (fun x => (Real.sqrt (f x)*Real.sqrt (g x))^2) μ
  simp_rw [mul_pow,Real.sq_sqrt (hf0 _),Real.sq_sqrt (hg0 _)]
  exact hf.integrable_mul hg

/-- Actual Lebesgue integral of the finite sum, with the designated first
mask unchanged. All integrability follows from L2 premises. -/
theorem masked_box_cauchy_schwarz {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} (s : Finset ι) {A : Set α} (hA : MeasurableSet A)
    {r : α → ℝ} {f g : ι → α → ℝ}
    (hr : MemLp r 2 μ) (hf : ∀ i ∈ s, MemLp (f i) 2 μ)
    (hg : ∀ i ∈ s, MemLp (g i) 2 μ)
    (hr0 : ∀ x, 0 ≤ r x) (hf0 : ∀ i x, 0 ≤ f i x) (hg0 : ∀ i x, 0 ≤ g i x) :
    (∫ x, A.indicator r x * (∑ i ∈ s, Real.sqrt (f i x)*Real.sqrt (g i x)) ∂μ) ≤
      Real.sqrt (∫ x in A, r x^2 ∂μ) *
        Real.sqrt (Real.sqrt (∫ x, (∑ i ∈ s, f i x)^2 ∂μ) *
          Real.sqrt (∫ x, (∑ i ∈ s, g i x)^2 ∂μ)) := by
  have hX := memLp_finsetSum s hf
  have hY := memLp_finsetSum s hg
  have hX0 : ∀ x, 0 ≤ ∑ i ∈ s, f i x := fun x => Finset.sum_nonneg (fun i _ => hf0 i x)
  have hY0 : ∀ x, 0 ≤ ∑ i ∈ s, g i x := fun x => Finset.sum_nonneg (fun i _ => hg0 i x)
  have hterms := memLp_finsetSum s (fun i hi => sqrt_product_memLp (hf i hi) (hg i hi) (hf0 i) (hg0 i))
  have hprod := sqrt_product_memLp hX hY hX0 hY0
  have hleft := (hr.indicator hA).integrable_mul hterms
  have hright := (hr.indicator hA).integrable_mul hprod
  calc
    _ ≤ ∫ x, A.indicator r x *
        (Real.sqrt (∑ i ∈ s, f i x)*Real.sqrt (∑ i ∈ s, g i x)) ∂μ := by
      apply integral_mono hleft hright
      intro x
      apply mul_le_mul_of_nonneg_left (inner_sum_bound s (fun i => f i x) (fun i => g i x)
        (fun i => hf0 i x) (fun i => hg0 i x))
      by_cases hx : x ∈ A <;> simp [hx,hr0]
    _ ≤ _ := masked_outer_integral_bound hA hr hX hY hr0 hX0 hY0

/-- Equal affine energy majorants collapse the two fourth roots without
altering the restricted first-factor mass. -/
theorem masked_box_of_energy_bounds {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} (s : Finset ι) {A : Set α} (hA : MeasurableSet A)
    {r : α → ℝ} {f g : ι → α → ℝ} {B : ℝ}
    (hr : MemLp r 2 μ) (hf : ∀ i ∈ s, MemLp (f i) 2 μ)
    (hg : ∀ i ∈ s, MemLp (g i) 2 μ)
    (hr0 : ∀ x, 0 ≤ r x) (hf0 : ∀ i x, 0 ≤ f i x) (hg0 : ∀ i x, 0 ≤ g i x)
    (hB : 0 ≤ B) (hX : (∫ x, (∑ i ∈ s, f i x)^2 ∂μ) ≤ B)
    (hY : (∫ x, (∑ i ∈ s, g i x)^2 ∂μ) ≤ B) :
    (∫ x, A.indicator r x * (∑ i ∈ s, Real.sqrt (f i x)*Real.sqrt (g i x)) ∂μ) ≤
      Real.sqrt (∫ x in A, r x^2 ∂μ)*Real.sqrt B := by
  apply (masked_box_cauchy_schwarz s hA hr hf hg hr0 hf0 hg0).trans
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Real.sqrt_le_sqrt
  calc
    _ ≤ Real.sqrt B*Real.sqrt B := mul_le_mul (Real.sqrt_le_sqrt hX)
      (Real.sqrt_le_sqrt hY) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = B := Real.mul_self_sqrt hB

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.sqrt_product_memLp
#print axioms GuthMaynard.Improvement.masked_box_cauchy_schwarz
#print axioms GuthMaynard.Improvement.masked_box_of_energy_bounds
