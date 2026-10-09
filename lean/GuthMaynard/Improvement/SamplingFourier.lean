import GuthMaynard.Improvement.SourceFourierDerivative
import GuthMaynard.Improvement.SamplingVariation
set_option autoImplicit false
noncomputable section
open MeasureTheory Set InnerProductSpace
open scoped FourierTransform
namespace GuthMaynard.Improvement

/-- The derivative of squared norm has an ordinary L1 bound from two L2 norms. -/
theorem sampling_square_variation {F G : ℝ → ℂ} (hF : MemLp F 2) (hG : MemLp G 2) :
    Integrable (fun t => 2*inner ℝ (F t) (G t)) ∧
    (∫ t, ‖2*inner ℝ (F t) (G t)‖) ≤
      2*Real.sqrt (∫ t, ‖F t‖^2)*Real.sqrt (∫ t, ‖G t‖^2) := by
  have hip := hF.norm.integrable_mul hG.norm
  have hp : ∀ t, ‖2*inner ℝ (F t) (G t)‖ ≤ 2*(‖F t‖*‖G t‖) := by
    intro t
    rw [norm_mul]
    rw [show ‖(2:ℝ)‖ = 2 by norm_num]
    exact mul_le_mul_of_nonneg_left (norm_inner_le_norm (F t) (G t)) (by norm_num)
  have hi : Integrable (fun t => 2*inner ℝ (F t) (G t)) := by
    apply (hip.const_mul 2).mono'
      ((hF.aestronglyMeasurable.inner hG.aestronglyMeasurable).const_mul 2)
    exact Filter.Eventually.of_forall hp
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ t, 2*(‖F t‖*‖G t‖) := integral_mono hi.norm (hip.const_mul 2) hp
    _ = 2*(∫ t, ‖F t‖*‖G t‖) := integral_const_mul _ _
    _ ≤ 2*(Real.sqrt (∫ t, ‖F t‖^2)*Real.sqrt (∫ t, ‖G t‖^2)) :=
      mul_le_mul_of_nonneg_left (integral_cauchy_schwarz_nonneg hF.norm hG.norm
        (fun t => norm_nonneg (F t)) (fun t => norm_nonneg (G t))) (by norm_num)
    _ = _ := by ring

/-- Separated sampling of the literal Fourier transform squared. No L1
hypothesis on the Fourier transform is used. The spacing δ is in mathlib's
actual Fourier frequency, with no hidden normalization change. -/
theorem sampling_fourier_square {ι : Type*} [Fintype ι]
    {f : ℝ → ℂ} (h1 : Integrable f) (h2 : MemLp f 2)
    {R : ℝ} (hR : 0 ≤ R) (hs : Function.support f ⊆ Icc (-R) R)
    (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : Pairwise (fun i j => δ ≤ |x i-x j|)) :
    (∑ i, ‖𝓕 f (x i)‖^2) ≤ (δ⁻¹+4*Real.pi*R)*(∫ t, ‖f t‖^2) := by
  have hF := ordinary_fourier_memLp h1 h2
  obtain ⟨hd,hG,hGb⟩ := source_fourier_derivative_l2 h1 h2 hR hs
  obtain ⟨hi,hb⟩ := sampling_square_variation hF hG
  have hqi := (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have hqd : ∀ t, HasDerivAt (fun ξ => ‖𝓕 f ξ‖^2)
      (2*inner ℝ (𝓕 f t) (deriv (𝓕 f) t)) t := fun t => (hd t).hasDerivAt.norm_sq
  have hh := sampling_separated_norm x hδ hqd hsep
    (A := univ) (fun _ => subset_univ _) (by simpa using hqi) (by simpa using hi)
  simp only [Real.norm_eq_abs,abs_pow,abs_norm,setIntegral_univ] at hh
  rw [ordinary_fourier_integral_sq h1 h2] at hh hb
  have hM : 0 ≤ ∫ t, ‖f t‖^2 := integral_nonneg (fun t => sq_nonneg _)
  have hroot : Real.sqrt (∫ t, ‖deriv (𝓕 f) t‖^2) ≤
      (2*Real.pi*R)*Real.sqrt (∫ t, ‖f t‖^2) := by
    calc
      _ ≤ Real.sqrt ((2*Real.pi*R)^2*(∫ t, ‖f t‖^2)) := Real.sqrt_le_sqrt hGb
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity : 0 ≤ 2*Real.pi*R)]
  have hv : (∫ t, ‖2*inner ℝ (𝓕 f t) (deriv (𝓕 f) t)‖) ≤
      4*Real.pi*R*(∫ t, ‖f t‖^2) := by
    calc
      _ ≤ _ := hb
      _ ≤ 2*Real.sqrt (∫ t, ‖f t‖^2)*((2*Real.pi*R)*Real.sqrt (∫ t, ‖f t‖^2)) := by
        gcongr
      _ = 4*Real.pi*R*(Real.sqrt (∫ t, ‖f t‖^2))^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hM]
  calc
    _ ≤ _ := hh
    _ ≤ δ⁻¹*(∫ t, ‖f t‖^2)+4*Real.pi*R*(∫ t, ‖f t‖^2) := by
      simpa only [Real.norm_eq_abs] using add_le_add le_rfl hv
    _ = _ := by ring

/-- High-height first-variation sampling retains the actual Fourier L1 mass
on [-2,2]. Only the sampling intervals must lie inside that fixed band. -/
theorem sampling_fourier_first_variation {ι : Type*} [Fintype ι]
    {f : ℝ → ℂ} (h1 : Integrable f) (h2 : MemLp f 2)
    {R : ℝ} (hR : 0 ≤ R) (hs : Function.support f ⊆ Icc (-R) R)
    (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : Pairwise (fun i j => δ ≤ |x i-x j|))
    (hband : ∀ i, Ioc (x i) (x i+δ) ⊆ Icc (-2:ℝ) 2) :
    (∑ i, ‖𝓕 f (x i)‖) ≤ δ⁻¹*(∫ ξ in Icc (-2:ℝ) 2, ‖𝓕 f ξ‖)+
      4*Real.pi*R*Real.sqrt (∫ t, ‖f t‖^2) := by
  have hd := (source_fourier_derivative_l2 h1 h2 hR hs).1
  have hFi := (source_l2_interval_l1 (ordinary_fourier_memLp h1 h2)).1
  obtain ⟨hGi,hGb⟩ := source_fourier_derivative_interval_l1 h1 h2 hR hs
  have hh := sampling_separated_norm x hδ (fun ξ => (hd ξ).hasDerivAt) hsep hband hFi hGi
  have hb : (∫ ξ in Icc (-2:ℝ) 2, ‖deriv (𝓕 f) ξ‖) ≤
      4*Real.pi*R*Real.sqrt (∫ t, ‖f t‖^2) := by convert hGb using 1; ring
  exact hh.trans (add_le_add le_rfl hb)

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.sampling_square_variation
#print axioms GuthMaynard.Improvement.sampling_fourier_square
#print axioms GuthMaynard.Improvement.sampling_fourier_first_variation
