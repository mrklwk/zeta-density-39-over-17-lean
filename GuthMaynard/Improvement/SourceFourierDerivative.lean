module
public import GuthMaynard.Improvement.OrdinaryFourierL2
public import GuthMaynard.Improvement.MeasureGate
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped FourierTransform
namespace GuthMaynard.Improvement

/-- Compact time support makes the actual time-weighted signal L1 and L2. -/
theorem source_time_weight_bounds {f : ℝ → ℂ} (h1 : Integrable f) (h2 : MemLp f 2)
    {R : ℝ} (_hR : 0 ≤ R) (hs : Function.support f ⊆ Icc (-R) R) :
    Integrable (fun t => t • f t) ∧ MemLp (fun t => t • f t) 2 ∧
      (∫ t, ‖t • f t‖^2) ≤ R^2*(∫ t, ‖f t‖^2) := by
  have hm : AEStronglyMeasurable (fun t : ℝ => t • f t) :=
    measurable_id.aestronglyMeasurable.smul h1.aestronglyMeasurable
  have hp : ∀ t : ℝ, ‖t • f t‖ ≤ R*‖f t‖ := by
    intro t
    by_cases ht : t ∈ Function.support f
    · have hb : |t| ≤ R := abs_le.mpr (hs ht)
      simpa only [norm_smul,Real.norm_eq_abs] using mul_le_mul_of_nonneg_right hb (norm_nonneg (f t))
    · have hz : f t=0 := by simpa [Function.mem_support] using ht
      simp [hz]
  have hi1 : Integrable (fun t : ℝ => t • f t) :=
    (h1.norm.const_mul R).mono' hm (Filter.Eventually.of_forall hp)
  have hfi := (memLp_two_iff_integrable_sq_norm h2.aestronglyMeasurable).mp h2
  have hp2 : ∀ t : ℝ, ‖t • f t‖^2 ≤ R^2*‖f t‖^2 := by
    intro t
    simpa [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hp t) 2
  have hi2 : Integrable (fun t : ℝ => ‖t • f t‖^2) := by
    apply (hfi.const_mul (R^2)).mono' (hm.norm.pow 2)
    filter_upwards [] with t
    simpa only [Pi.pow_apply,Real.norm_eq_abs,abs_pow,abs_norm] using hp2 t
  refine ⟨hi1,(memLp_two_iff_integrable_sq_norm hm).mpr hi2,?_⟩
  calc
    _ ≤ ∫ t, R^2*‖f t‖^2 := integral_mono hi2 (hfi.const_mul _) hp2
    _ = _ := integral_const_mul _ _

/-- Actual literal Fourier derivative, with exact 2π normalization. -/
theorem source_fourier_hasDerivAt {f : ℝ → ℂ} (h1 : Integrable f) (h2 : MemLp f 2)
    {R : ℝ} (hR : 0 ≤ R) (hs : Function.support f ⊆ Icc (-R) R) (ξ : ℝ) :
    HasDerivAt (𝓕 f) (𝓕 (fun t : ℝ => (-2*Real.pi*Complex.I*t)*f t) ξ) ξ := by
  simpa only [smul_eq_mul] using
    Real.hasDerivAt_fourier h1 (source_time_weight_bounds h1 h2 hR hs).1 ξ

/-- Ordinary compactly supported L1/L2 data have a differentiable literal
Fourier transform and an L2 derivative, with exact support-radius loss. -/
theorem source_fourier_derivative_l2 {f : ℝ → ℂ} (h1 : Integrable f) (h2 : MemLp f 2)
    {R : ℝ} (hR : 0 ≤ R) (hs : Function.support f ⊆ Icc (-R) R) :
    Differentiable ℝ (𝓕 f) ∧ MemLp (deriv (𝓕 f)) 2 ∧
      (∫ ξ, ‖deriv (𝓕 f) ξ‖^2) ≤ (2*Real.pi*R)^2*(∫ t, ‖f t‖^2) := by
  obtain ⟨hwi,hw2,hwb⟩ := source_time_weight_bounds h1 h2 hR hs
  let c : ℂ := -2*Real.pi*Complex.I
  let w : ℝ → ℂ := fun t => c • (t • f t)
  have hwi' : Integrable w := hwi.smul c
  have hw2' : MemLp w 2 := hw2.const_smul c
  have he : deriv (𝓕 f) = 𝓕 w := by
    rw [Real.deriv_fourier h1 hwi]
    congr 1
    funext t
    simp [w,c,smul_eq_mul,Complex.real_smul,mul_assoc]
  have hn : ‖c‖ = 2*Real.pi := by
    simp [c,Complex.norm_real,abs_of_pos Real.pi_pos]
  refine ⟨fun ξ => (source_fourier_hasDerivAt h1 h2 hR hs ξ).differentiableAt,?_,?_⟩
  · rw [he]
    exact ordinary_fourier_memLp hwi' hw2'
  · rw [he,ordinary_fourier_integral_sq hwi' hw2']
    have hi : (∫ t, ‖w t‖^2) = (2*Real.pi)^2*(∫ t, ‖t • f t‖^2) := by
      simp only [w,norm_smul,hn,mul_pow]
      exact integral_const_mul _ _
    rw [hi]
    calc
      _ ≤ (2*Real.pi)^2*(R^2*(∫ t, ‖f t‖^2)) :=
        mul_le_mul_of_nonneg_left hwb (sq_nonneg _)
      _ = _ := by ring

/-- The derivative is continuous as the Fourier transform of an actual L1
weighted signal; this supplies ordinary FTC regularity for sampling. -/
theorem source_fourier_derivative_continuous {f : ℝ → ℂ}
    (h1 : Integrable f) (h2 : MemLp f 2) {R : ℝ} (hR : 0 ≤ R)
    (hs : Function.support f ⊆ Icc (-R) R) : Continuous (deriv (𝓕 f)) := by
  have hwi := (source_time_weight_bounds h1 h2 hR hs).1
  have hi : Integrable (fun t : ℝ => (-2*Real.pi*Complex.I*t)*f t) := by
    convert hwi.smul (-2*Real.pi*Complex.I) using 1
    funext t
    simp [smul_eq_mul,Complex.real_smul,mul_assoc]
  have he : deriv (𝓕 f) = 𝓕 (fun t : ℝ => (-2*Real.pi*Complex.I*t)*f t) := by
    funext ξ
    exact (source_fourier_hasDerivAt h1 h2 hR hs ξ).deriv
  rw [he]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hi

/-- Exact Cauchy--Schwarz constant on the fixed frequency interval [-2,2]. -/
theorem source_l2_interval_l1 {f : ℝ → ℂ} (h2 : MemLp f 2) :
    IntegrableOn f (Icc (-2:ℝ) 2) ∧
    (∫ ξ in Icc (-2:ℝ) 2, ‖f ξ‖) ≤ 2*Real.sqrt (∫ ξ, ‖f ξ‖^2) := by
  have hs : MemLp f 2 (volume.restrict (Icc (-2:ℝ) 2)) := h2.restrict _
  have hi : IntegrableOn f (Icc (-2:ℝ) 2) := hs.integrable (by norm_num)
  refine ⟨hi,?_⟩
  have hcs := integral_cauchy_schwarz_nonneg
    (μ := volume.restrict (Icc (-2:ℝ) 2))
    (memLp_const (1:ℝ)) hs.norm (fun _ => zero_le_one) (fun ξ => norm_nonneg (f ξ))
  have hc : (∫ ξ in Icc (-2:ℝ) 2, (1:ℝ)^2) = 4 := by
    norm_num [Measure.real,Real.volume_Icc]
  simp only [one_mul] at hcs
  rw [hc] at hcs
  have hsqrt : Real.sqrt 4 = 2 := by norm_num
  rw [hsqrt] at hcs
  apply hcs.trans
  apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt _) (by norm_num : (0:ℝ)≤2)
  exact setIntegral_le_integral
    ((memLp_two_iff_integrable_sq_norm h2.aestronglyMeasurable).mp h2)
    (Filter.Eventually.of_forall (fun ξ => sq_nonneg ‖f ξ‖))

/-- The actual Fourier derivative has the local L1 budget used in sampling. -/
theorem source_fourier_derivative_interval_l1 {f : ℝ → ℂ}
    (h1 : Integrable f) (h2 : MemLp f 2) {R : ℝ} (hR : 0 ≤ R)
    (hs : Function.support f ⊆ Icc (-R) R) :
    IntegrableOn (deriv (𝓕 f)) (Icc (-2:ℝ) 2) ∧
    (∫ ξ in Icc (-2:ℝ) 2, ‖deriv (𝓕 f) ξ‖) ≤
      2*(2*Real.pi*R)*Real.sqrt (∫ t, ‖f t‖^2) := by
  obtain ⟨_,hd2,hdb⟩ := source_fourier_derivative_l2 h1 h2 hR hs
  obtain ⟨hi,hb⟩ := source_l2_interval_l1 hd2
  refine ⟨hi,?_⟩
  calc
    _ ≤ 2*Real.sqrt (∫ ξ, ‖deriv (𝓕 f) ξ‖^2) := hb
    _ ≤ 2*Real.sqrt ((2*Real.pi*R)^2*(∫ t, ‖f t‖^2)) := by gcongr
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity : 0 ≤ 2*Real.pi*R)]; ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.source_time_weight_bounds
#print axioms GuthMaynard.Improvement.source_fourier_hasDerivAt
#print axioms GuthMaynard.Improvement.source_fourier_derivative_l2
#print axioms GuthMaynard.Improvement.source_l2_interval_l1
#print axioms GuthMaynard.Improvement.source_fourier_derivative_interval_l1

#print axioms GuthMaynard.Improvement.source_fourier_derivative_continuous
