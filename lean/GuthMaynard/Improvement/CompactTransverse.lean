import GuthMaynard.Improvement.CompactKernel
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- Exact positive plateau of the constructed mass-one kernel. -/
theorem compactKernel_plateau {x : ℝ} (hx : |x| ≤ 1) :
    compactKernel x = (∫ y, kernelBump y)⁻¹ := by
  have hh : x ∈ Metric.closedBall (0 : ℝ) kernelBump.rIn := by
    simpa [kernelBump, Metric.mem_closedBall, Real.dist_eq] using hx
  change kernelBump x / (∫ y, kernelBump y) = _
  rw [kernelBump.one_of_mem_closedBall hh, one_div]

/-- A wider kernel covers both transverse windows uniformly for v in [a,b].
The width is max(1,1/a)*delta, chosen independently of the mask. -/
theorem compact_masked_transverse (a b : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ v z : ℝ) (A : Set ℝ) (r : ℝ → ℝ),
      0 < δ → a ≤ v → v ≤ b → MeasurableSet A → Measurable r →
      Integrable (fun y => r y^2) → (∀ y, 0 ≤ r y) →
      (∫ y in {y | |y-z| ≤ δ}, A.indicator r y * A.indicator r (y/v)) ≤
        C*δ*Real.sqrt b * Real.sqrt
          (squareSmoothing (scaledKernel compactKernel (max 1 (1/a)*δ)) (A.indicator r) z *
           squareSmoothing (scaledKernel compactKernel (max 1 (1/a)*δ)) (A.indicator r) (z/v)) := by
  let q := max 1 (1/a)
  have hq : 0 < q := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hi : 0 < ∫ y, kernelBump y := kernelBump.integral_pos
  refine ⟨q*(∫ y, kernelBump y),mul_pos hq hi,?_⟩
  intro δ v z A r hδ hav hvb hA hr hr2 hr0
  obtain ⟨B,hB,hbound⟩ := compactKernel_bound
  have hlower : ∀ t, |t| ≤ max 1 (1/a)*δ →
      1 ≤ ((q*(∫ y, kernelBump y))*δ) * scaledKernel compactKernel (q*δ) t := by
    intro t ht
    have ht' : |t/(q*δ)| ≤ 1 := by
      rw [abs_div, abs_of_pos (mul_pos hq hδ)]
      exact (div_le_one (mul_pos hq hδ)).mpr ht
    rw [scaledKernel,compactKernel_plateau ht']
    have hqn := hq.ne'
    have hdn := hδ.ne'
    have hin := hi.ne'
    field_simp
    nlinarith
  exact masked_transverse_smoothing hA
    (scaledKernel_measurable compactKernel_smooth.continuous.measurable _)
    (scaledKernel_bound (mul_pos hq hδ) hbound)
    (scaledKernel_nonneg compactKernel_nonneg (mul_pos hq hδ))
    (mul_pos hq hi).le hδ.le ha hav hvb hlower hr hr2 hr0

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.compactKernel_plateau
#print axioms GuthMaynard.Improvement.compact_masked_transverse
