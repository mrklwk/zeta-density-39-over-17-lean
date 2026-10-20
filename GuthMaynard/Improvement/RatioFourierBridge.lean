module
public import GuthMaynard.Improvement.RadialRemainder
public import GuthMaynard.Improvement.LogMask

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped FourierTransform ComplexConjugate
namespace GuthMaynard.Improvement

/-- Reflection symmetry for the literal Fourier integral of a real density. -/
theorem realDensity_fourier_conj (μ : ℝ → ℝ) (ξ : ℝ) :
    𝓕 (fun t => (μ t:ℂ)) (-ξ) = conj (𝓕 (fun t => (μ t:ℂ)) ξ) := by
  have hp : ∀ s : ℝ, conj (phase s) = phase (-s) := by
    intro s
    unfold phase
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]
    push_cast
    ring
  rw [fourier_eq_phase_integral,fourier_eq_phase_integral,← integral_conj]
  apply integral_congr_ae
  filter_upwards with t
  simp only [map_mul,Complex.conj_ofReal,hp]
  congr 2
  ring

theorem realDensity_fourier_norm_neg (μ : ℝ → ℝ) (ξ : ℝ) :
    ‖𝓕 (fun t => (μ t:ℂ)) (-ξ)‖ = ‖𝓕 (fun t => (μ t:ℂ)) ξ‖ := by
  rw [realDensity_fourier_conj,RCLike.norm_conj]

/-- Exact normalization of the three magnitudes used in the transverse
argument. Neither the first Fourier factor nor its mask is enlarged. -/
theorem ratioFourierProduct_norm (μ : ℝ → ℝ) {v y : ℝ} (hv : 0 < v) (hy : 0 < y) :
    ‖ratioFourierProduct μ (v,y)‖ =
      ‖𝓕 (fun t => (μ t:ℂ)) (mellinFrequency v)‖ *
      ‖𝓕 (fun t => (μ t:ℂ)) (mellinFrequency (y/v))‖ *
      ‖𝓕 (fun t => (μ t:ℂ)) (mellinFrequency y)‖ := by
  have he : mellinFrequency v-mellinFrequency y = -mellinFrequency (y/v) := by
    unfold mellinFrequency
    rw [Real.log_div hy.ne' hv.ne']
    ring
  simp only [ratioFourierProduct,norm_mul,he,realDensity_fourier_norm_neg]

/-- The exceptional Fourier set is symmetric without assumptions on its
boundary or positive measure. -/
theorem realDensity_level_symmetry (μ : ℝ → ℝ) (Λ ξ : ℝ) :
    (Λ < ‖𝓕 (fun t => (μ t:ℂ)) (-ξ)‖) ↔
      (Λ < ‖𝓕 (fun t => (μ t:ℂ)) ξ‖) := by
  rw [realDensity_fourier_norm_neg]

/-- Logarithmic mask transfer in the exact mathlib Fourier normalization.
The original measurable Fourier mask A is retained on the right. -/
theorem mellin_compact_mask_integral {w h : ℝ → ℝ} {a b W : ℝ} {A : Set ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hW : 0 ≤ W)
    (hw : Measurable w) (hw0 : ∀ v, 0 ≤ w v) (hwW : ∀ v, w v ≤ W)
    (hs : ∀ v, v ∉ Icc a b → w v = 0) (hA : MeasurableSet A)
    (hh : Integrable h) (hh0 : ∀ u, 0 ≤ h u) :
    Integrable (fun v => w v*A.indicator h (mellinFrequency v)) ∧
      (∫ v, w v*A.indicator h (mellinFrequency v)) ≤
        (b*W*(2*Real.pi))*(∫ ξ in A, h ξ) := by
  have hpi : (2*Real.pi) ≠ 0 := by positivity
  have hi : Integrable (fun u : ℝ => A.indicator h (u/(2*Real.pi))) :=
    (hh.indicator hA).comp_div hpi
  have h0 : ∀ u : ℝ, 0 ≤ A.indicator h (u/(2*Real.pi)) := by
    intro u
    by_cases hu : u/(2*Real.pi) ∈ A <;> simp [hu,hh0]
  have hp := log_compact_mask_integral ha hab hW hw hw0 hwW hs MeasurableSet.univ hi h0
  simp only [indicator_univ,setIntegral_univ] at hp
  refine ⟨hp.1,?_⟩
  have he : (∫ u : ℝ, A.indicator h (u/(2*Real.pi))) =
      (2*Real.pi)*(∫ ξ in A, h ξ) := by
    rw [Measure.integral_comp_div,abs_of_pos (by positivity : 0 < 2*Real.pi),
      smul_eq_mul,integral_indicator hA]
  rw [he] at hp
  simpa only [mellinFrequency,mul_assoc] using hp.2

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.realDensity_fourier_conj
#print axioms GuthMaynard.Improvement.realDensity_fourier_norm_neg
#print axioms GuthMaynard.Improvement.ratioFourierProduct_norm
#print axioms GuthMaynard.Improvement.realDensity_level_symmetry

#print axioms GuthMaynard.Improvement.mellin_compact_mask_integral
