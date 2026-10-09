import GuthMaynard.Improvement.RadialDecay
import GuthMaynard.Improvement.CubicTimeMeasure
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped FourierTransform ContDiff
namespace GuthMaynard.Improvement

def radialKernel (a : ℝ → ℂ) (L : ℝ) (m : ℤ × (ℤ × ℤ)) (p : ℝ × ℝ) : ℂ :=
  ∫ r, radialAmplitude a p.1 p.2 r*phase (-L*((m.1:ℝ)*p.1+(m.2.1:ℝ)*p.2+(m.2.2:ℝ))*r)
def ratioFourierProduct (μ : ℝ → ℝ) (p : ℝ × ℝ) : ℂ :=
  𝓕 (fun t => (μ t:ℂ)) (-mellinFrequency p.1)*
  𝓕 (fun t => (μ t:ℂ)) (mellinFrequency p.1-mellinFrequency p.2)*
  𝓕 (fun t => (μ t:ℂ)) (mellinFrequency p.2)
def radialDiscard (a : ℝ → ℂ) (μ : ℝ → ℝ) (L H : ℝ) (m : ℤ × (ℤ × ℤ)) (p : ℝ × ℝ) : ℂ :=
  if H < |L*((m.1:ℝ)*p.1+(m.2.1:ℝ)*p.2+(m.2.2:ℝ))| then radialKernel a L m p*ratioFourierProduct μ p else 0

theorem radialKernel_measurable {a : ℝ → ℂ} (ha : Measurable a) (L : ℝ) (m : ℤ × (ℤ × ℤ)) :
    Measurable (radialKernel a L m) := by
  have hp := phase_measurable
  have hh : Measurable (fun z : (ℝ × ℝ) × ℝ =>
      radialAmplitude a z.1.1 z.1.2 z.2*phase (-L*((m.1:ℝ)*z.1.1+(m.2.1:ℝ)*z.1.2+(m.2.2:ℝ))*z.2)) := by
    unfold radialAmplitude
    fun_prop
  exact hh.stronglyMeasurable.integral_prod_right'.measurable

theorem ratioFourierProduct_measurable {μ : ℝ → ℝ} (hi : Integrable μ) : Measurable (ratioFourierProduct μ) := by
  have hc : Continuous (𝓕 (fun t => (μ t:ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂
      (Complex.ofRealCLM.integrable_comp hi)
  unfold ratioFourierProduct mellinFrequency
  fun_prop

theorem ratioFourierProduct_bound {μ : ℝ → ℝ} (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t)
    (hi : Integrable μ) (p : ℝ × ℝ) : ‖ratioFourierProduct μ p‖ ≤ (∫ t, μ t)^3 := by
  have hmass : 0 ≤ ∫ t, μ t := integral_nonneg h0
  unfold ratioFourierProduct
  simp only [norm_mul]
  calc
    _ ≤ (∫ t, μ t)*(∫ t, μ t)*(∫ t, μ t) := by gcongr <;> exact time_fourier_norm_le_mass hm h0 hi _
    _ = _ := by ring

/-- Actual discarded radial double integral, with one uniform constant
before every mode, L, H, and time density. All integral existence is proved.
The right side retains original mass cubed and the exact ratio-box area. -/
theorem radial_discard_integral_bound {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {l u : ℝ} (hlu : l ≤ u) (hs : ∀ r, r ∉ Icc l u → a r = 0)
    (v₀ v₁ y₀ y₁ : ℝ) (hv : v₀ ≤ v₁) (hy : y₀ ≤ y₁) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L H : ℝ) (m : ℤ × (ℤ × ℤ)) (μ : ℝ → ℝ),
      0 < H → Measurable μ → (∀ t, 0 ≤ μ t) → Integrable μ →
      IntegrableOn (radialDiscard a μ L H m) (Icc v₀ v₁ ×ˢ Icc y₀ y₁) ∧
      ‖∫ p in Icc v₀ v₁ ×ˢ Icc y₀ y₁, radialDiscard a μ L H m p‖ ≤
        C/H^n*(∫ t, μ t)^3*((v₁-v₀)*(y₁-y₀)) := by
  obtain ⟨C,hC,hb⟩ := radial_uniform_power_decay ha hlu hs v₀ v₁ y₀ y₁ n
  refine ⟨C,hC,?_⟩
  intro L H m μ hH hm h0 hi
  have hmass : 0 ≤ ∫ t, μ t := integral_nonneg h0
  have hmeas : Measurable (radialDiscard a μ L H m) := by
    unfold radialDiscard
    apply Measurable.ite (measurableSet_lt measurable_const (by fun_prop))
      ((radialKernel_measurable ha.continuous.measurable L m).mul (ratioFourierProduct_measurable hi)) measurable_const
  have hpoint : ∀ p ∈ Icc v₀ v₁ ×ˢ Icc y₀ y₁,
      ‖radialDiscard a μ L H m p‖ ≤ C/H^n*(∫ t, μ t)^3 := by
    intro p hp
    unfold radialDiscard
    split_ifs with hx
    · have hh := hb p.1 hp.1 p.2 hp.2 (L*((m.1:ℝ)*p.1+(m.2.1:ℝ)*p.2+(m.2.2:ℝ)))
      have hpow := pow_le_pow_left₀ hH.le hx.le n
      have hr : ‖radialKernel a L m p‖ ≤ C/H^n := by
        rw [radialKernel,radial_integral_fourier]
        apply (le_div_iff₀ (pow_pos hH n)).mpr
        nlinarith [mul_le_mul_of_nonneg_right hpow (norm_nonneg (𝓕 (radialAmplitude a p.1 p.2) (L*((m.1:ℝ)*p.1+(m.2.1:ℝ)*p.2+(m.2.2:ℝ)))))]
      rw [norm_mul]
      exact mul_le_mul hr (ratioFourierProduct_bound hm h0 hi p) (norm_nonneg _) (by positivity)
    · simp only [norm_zero]
      positivity
  have hfinite : volume (Icc v₀ v₁ ×ˢ Icc y₀ y₁) < ⊤ := (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  have hInt : IntegrableOn (radialDiscard a μ L H m) (Icc v₀ v₁ ×ˢ Icc y₀ y₁) :=
    (integrableOn_const hfinite.ne).mono' hmeas.aestronglyMeasurable
      (ae_restrict_of_forall_mem (measurableSet_Icc.prod measurableSet_Icc) hpoint)
  refine ⟨hInt,?_⟩
  have hh := norm_setIntegral_le_of_norm_le_const hfinite hpoint
  have hvol : volume.real (Icc v₀ v₁ ×ˢ Icc y₀ y₁) = (v₁-v₀)*(y₁-y₀) := by
    rw [Measure.real,Measure.volume_eq_prod,Measure.prod_prod]
    rw [ENNReal.toReal_mul]
    change volume.real (Icc v₀ v₁)*volume.real (Icc y₀ y₁) = _
    rw [Real.volume_real_Icc_of_le hv,Real.volume_real_Icc_of_le hy]
  rw [hvol] at hh
  exact hh

/-- Sum of the actual discarded radial integrals, retaining L^3, every
mode, the exact mode count and the original mass cubed. -/
theorem radial_total_discard_bound {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {l u : ℝ} (hlu : l ≤ u) (hs : ∀ r, r ∉ Icc l u → a r = 0)
    (v₀ v₁ y₀ y₁ : ℝ) (hv : v₀ ≤ v₁) (hy : y₀ ≤ y₁) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L H : ℝ) (S : Finset (ℤ × (ℤ × ℤ))) (μ : ℝ → ℝ),
      0 < H → Measurable μ → (∀ t, 0 ≤ μ t) → Integrable μ →
      ‖(L:ℂ)^3*(∑ m ∈ S, ∫ p in Icc v₀ v₁ ×ˢ Icc y₀ y₁, radialDiscard a μ L H m p)‖ ≤
        |L| ^3*S.card*C/H^n*(∫ t, μ t)^3*((v₁-v₀)*(y₁-y₀)) := by
  obtain ⟨C,hC,h⟩ := radial_discard_integral_bound ha hlu hs v₀ v₁ y₀ y₁ hv hy n
  refine ⟨C,hC,?_⟩
  intro L H S μ hH hm h0 hi
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ |L| ^3*(∑ m ∈ S, ‖∫ p in Icc v₀ v₁ ×ˢ Icc y₀ y₁, radialDiscard a μ L H m p‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ |L| ^3*(∑ _m ∈ S, C/H^n*(∫ t, μ t)^3*((v₁-v₀)*(y₁-y₀))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun m _ => (h L H m μ hH hm h0 hi).2)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.radialKernel_measurable
#print axioms GuthMaynard.Improvement.ratioFourierProduct_measurable
#print axioms GuthMaynard.Improvement.ratioFourierProduct_bound
#print axioms GuthMaynard.Improvement.radial_discard_integral_bound

#print axioms GuthMaynard.Improvement.radial_total_discard_bound
