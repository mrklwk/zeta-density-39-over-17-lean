module
public import GuthMaynard.Improvement.RetainedCubicKernel
public import GuthMaynard.Improvement.CubicKernelError
public import GuthMaynard.Improvement.MeasureGate

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped FourierTransform
namespace GuthMaynard.Improvement

def timeMeasure (μ : ℝ → ℝ) : Measure ℝ := volume.withDensity (fun t => ENNReal.ofReal (μ t))

theorem timeMeasure_finite {μ : ℝ → ℝ} (hi : Integrable μ) : IsFiniteMeasure (timeMeasure μ) :=
  isFiniteMeasure_withDensity_ofReal hi.hasFiniteIntegral

theorem timeMeasure_mass {μ : ℝ → ℝ} (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t) :
    (timeMeasure μ).real univ = ∫ t, μ t := by
  have hh := integral_withDensity_eq_integral_toReal_smul (μ := volume) hm.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) (fun _ : ℝ => (1:ℝ))
  simpa only [ENNReal.toReal_ofReal (h0 _),smul_eq_mul,mul_one,integral_const,
    smul_eq_mul,mul_one,timeMeasure] using hh

theorem measureFourier_timeMeasure {μ : ℝ → ℝ} (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t) (u : ℝ) :
    measureFourier (timeMeasure μ) u = 𝓕 (fun t => (μ t:ℂ)) u := by
  unfold measureFourier timeMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),fourier_eq_phase_integral]
  apply integral_congr_ae
  filter_upwards with t
  simp only [ENNReal.toReal_ofReal (h0 t),Complex.real_smul]
  ring

/-- Uniform Fourier bound with the exact original L1 mass, for use in
spatial discarded-region estimates. -/
theorem time_fourier_norm_le_mass {μ : ℝ → ℝ} (hm : Measurable μ)
    (h0 : ∀ t, 0 ≤ μ t) (hi : Integrable μ) (u : ℝ) :
    ‖𝓕 (fun t => (μ t:ℂ)) u‖ ≤ ∫ t, μ t := by
  let := timeMeasure_finite hi
  rw [← measureFourier_timeMeasure hm h0]
  have hh := norm_integral_le_of_norm_le_const (μ := timeMeasure μ)
    (f := fun t => phase (-u*t)) (C := 1)
    (Filter.Eventually.of_forall (fun t => (phase_norm (-u*t)).le))
  simpa only [measureFourier,one_mul,timeMeasure_mass hm h0] using hh

/-- Actual retained cubic identity for an ordinary nonnegative integrable
time density and the project's literal Fourier transform. -/
theorem retained_cubic_time_density (ν : Measure ℝ) [IsFiniteMeasure ν]
    {μ : ℝ → ℝ} (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t) (hi : Integrable μ)
    {a : ℝ → ℂ} {B : ℝ} (ha : Measurable a) (hB : 0 ≤ B) (hb : ∀ x, ‖a x‖ ≤ B)
    (L : ℝ) (S : Finset ℤ) :
    kernelCubic (timeMeasure μ) (retainedPoissonKernel ν a L S) =
      ∫ x : Triple, (retainedAmplitude a L S x.1*retainedAmplitude a L S x.2.1*
        retainedAmplitude a L S x.2.2)*
        (𝓕 (fun t => (μ t:ℂ)) (mellinFrequency x.2.2-mellinFrequency x.1)*
          𝓕 (fun t => (μ t:ℂ)) (mellinFrequency x.1-mellinFrequency x.2.1)*
          𝓕 (fun t => (μ t:ℂ)) (mellinFrequency x.2.1-mellinFrequency x.2.2)) ∂tripleMeasure ν := by
  let := timeMeasure_finite hi
  simpa only [measureFourier_timeMeasure hm h0] using retainedPoissonKernel_cubic (timeMeasure μ) ν ha hB hb L S

/-- The genuine compact-support L1/L2 comparison used to turn mass-cubed
remainders into homogeneous M^(3/2) errors. No inverse mass is introduced. -/
theorem compact_time_mass_bound {μ : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t)
    (h2 : Integrable (fun t => μ t^2)) (hs : ∀ t, t ∉ Icc a b → μ t = 0) :
    (∫ t, μ t) ≤ Real.sqrt (b-a)*Real.sqrt (∫ t, μ t^2) := by
  have hmem := (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr h2
  have hone : MemLp (fun _ : ℝ => (1:ℝ)) 2 (volume.restrict (Icc a b)) := memLp_const 1
  have hh := integral_cauchy_schwarz_nonneg (hmem.restrict (Icc a b)) hone h0 (fun _ => zero_le_one)
  have hs2 : ∀ t, t ∉ Icc a b → μ t^2 = 0 := by intro t ht; rw [hs t ht]; norm_num
  simp only [mul_one,one_pow,integral_const,smul_eq_mul,mul_one] at hh
  have hvol : (volume.restrict (Icc a b)).real univ = b-a := by
    rw [Measure.real,Measure.restrict_apply_univ,← Measure.real,Real.volume_real_Icc_of_le hab]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hs,
    setIntegral_eq_integral_of_forall_compl_eq_zero hs2,hvol] at hh
  simpa only [mul_comm] using hh

/-- Actual cubic perturbation for an ordinary compactly supported density,
with exact support-length and L2 homogeneity. The uniform kernel error e
is explicit; its Poisson/nonstationary-phase estimate is separate. -/
theorem cubic_time_density_perturbation {μ : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t) (hi : Integrable μ)
    (h2 : Integrable (fun t => μ t^2)) (hs : ∀ t, t ∉ Icc a b → μ t = 0)
    {K J : ℝ → ℂ} {B e : ℝ} (hK : Measurable K) (hJ : Measurable J)
    (hB : 0 ≤ B) (he : 0 ≤ e) (hbK : ∀ s, ‖K s‖ ≤ B) (hbJ : ∀ s, ‖J s‖ ≤ B)
    (herr : ∀ s, ‖K s-J s‖ ≤ e) :
    ‖kernelCubic (timeMeasure μ) K-kernelCubic (timeMeasure μ) J‖ ≤
      3*e*B^2*(Real.sqrt (b-a))^3*(Real.sqrt (∫ t, μ t^2))^3 := by
  let := timeMeasure_finite hi
  have hh := kernelCubic_perturbation (timeMeasure μ) hK hJ hB he hbK hbJ herr
  rw [timeMeasure_mass hm h0] at hh
  have hmass := compact_time_mass_bound hab hm h0 h2 hs
  have hmass0 : 0 ≤ ∫ t, μ t := integral_nonneg h0
  calc
    _ ≤ 3*e*B^2*(∫ t, μ t)^3 := hh
    _ ≤ 3*e*B^2*(Real.sqrt (b-a)*Real.sqrt (∫ t, μ t^2))^3 := by gcongr
    _ = _ := by ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.timeMeasure_finite
#print axioms GuthMaynard.Improvement.timeMeasure_mass
#print axioms GuthMaynard.Improvement.measureFourier_timeMeasure
#print axioms GuthMaynard.Improvement.retained_cubic_time_density
#print axioms GuthMaynard.Improvement.compact_time_mass_bound
#print axioms GuthMaynard.Improvement.cubic_time_density_perturbation

#print axioms GuthMaynard.Improvement.time_fourier_norm_le_mass
