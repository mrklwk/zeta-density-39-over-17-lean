module
public import GuthMaynard.Improvement.RadialFubini

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped FourierTransform ContDiff
namespace GuthMaynard.Improvement

theorem assembly_cutoff_bound {a : ℝ → ℂ} (ha : Continuous a) {l u : ℝ}
    (hs : ∀ x, x ∉ Icc l u → a x = 0) :
    ∃ B : ℝ, 0 < B ∧ ∀ x, ‖a x‖ ≤ B := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn ha.continuousOn
  refine ⟨max 1 C,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro x
  by_cases hx : x ∈ Icc l u
  · exact (hC x hx).trans (le_max_right _ _)
  · rw [hs x hx,norm_zero]; positivity

theorem spatialCubicMode_measurable {a : ℝ → ℂ} {μ : ℝ → ℝ}
    (ha : Measurable a) (hi : Integrable μ) (L : ℝ) (m : ℤ × (ℤ × ℤ)) :
    Measurable (fun x : Triple => spatialCubicMode a μ L m x.1 x.2.1 x.2.2) := by
  have hp := phase_measurable
  have hc : Continuous (𝓕 (fun t => (μ t:ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂
      (Complex.ofRealCLM.integrable_comp hi)
  have hf := hc.measurable
  have hm : Measurable mellinFrequency := by unfold mellinFrequency; fun_prop
  unfold spatialCubicMode
  fun_prop

theorem spatialCubicMode_support {a : ℝ → ℂ} {l u : ℝ}
    (hs : ∀ x, x ∉ Icc l u → a x = 0) (μ : ℝ → ℝ) (L : ℝ) (m : ℤ × (ℤ × ℤ)) :
    Function.support (fun x : Triple => spatialCubicMode a μ L m x.1 x.2.1 x.2.2) ⊆
      Icc l u ×ˢ (Icc l u ×ˢ Icc l u) := by
  intro x hx
  by_contra hn
  have h : x.1 ∉ Icc l u ∨ x.2.1 ∉ Icc l u ∨ x.2.2 ∉ Icc l u := by simpa only [Set.mem_prod,not_and_or] using hn
  rcases h with h | h | h <;> exact hx (by simp [spatialCubicMode,hs _ h])

theorem spatialCubicMode_integrable {a : ℝ → ℂ} {μ : ℝ → ℝ}
    (ha : Continuous a) {l u : ℝ} (hs : ∀ x, x ∉ Icc l u → a x = 0)
    (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t) (hi : Integrable μ)
    (L : ℝ) (m : ℤ × (ℤ × ℤ)) :
    Integrable (fun x : Triple => spatialCubicMode a μ L m x.1 x.2.1 x.2.2) := by
  have hmass : 0 ≤ ∫ t, μ t := integral_nonneg h0
  have hE : IsCompact (Icc l u ×ˢ (Icc l u ×ˢ Icc l u)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  apply (integrableOn_iff_integrable_of_support_subset (spatialCubicMode_support hs μ L m)).mp
  obtain ⟨B,hB,hb⟩ := assembly_cutoff_bound ha hs
  apply (integrableOn_const hE.measure_lt_top.ne (C := B^3*(∫ t, μ t)^3)).mono'
    (spatialCubicMode_measurable ha.measurable hi L m).aestronglyMeasurable
  filter_upwards with x
  simp only [spatialCubicMode,norm_mul,phase_norm,mul_one]
  calc
    _ ≤ (B*B*B)*((∫ t, μ t)*(∫ t, μ t)*(∫ t, μ t)) := by
      gcongr <;> first | exact hb _ | exact time_fourier_norm_le_mass hm h0 hi _
    _ = _ := by ring

/-- Actual coordinate reordering followed by the proved radial Fubini identity. -/
theorem spatialCubicMode_integral_radial {a : ℝ → ℂ} {μ : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hs : ∀ x, x ∉ Icc l u → a x = 0)
    (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t) (hi : Integrable μ)
    (L : ℝ) (m : ℤ × (ℤ × ℤ)) :
    (∫ x : Triple, spatialCubicMode a μ L m x.1 x.2.1 x.2.2) =
      ∫ p in Icc (l/u) (u/l) ×ˢ Icc (l/u) (u/l),
        radialKernel a L m p * ratioFourierProduct μ p := by
  let e : Triple ≃ᵐ Triple := MeasurableEquiv.prodComm.trans MeasurableEquiv.prodAssoc
  have he : MeasurePreserving e volume volume :=
    (measurePreserving_prodAssoc volume volume volume).comp Measure.measurePreserving_swap
  have hf := spatialCubicMode_integrable ha.continuous hs hm h0 hi L m
  have hp := he.integrable_comp_of_integrable hf
  rw [← he.integral_comp' (fun x : Triple => spatialCubicMode a μ L m x.1 x.2.1 x.2.2)]
  change (∫ x : Triple, spatialCubicMode a μ L m x.2.1 x.2.2 x.1) = _
  change Integrable (fun x : Triple => spatialCubicMode a μ L m x.2.1 x.2.2 x.1) (volume.prod volume) at hp
  change (∫ x : Triple, spatialCubicMode a μ L m x.2.1 x.2.2 x.1 ∂volume.prod volume) = _
  rw [integral_prod _ hp]
  have hh : (∫ r, ∫ p : ℝ × ℝ, spatialCubicMode a μ L m p.1 p.2 r) =
      ∫ r, ∫ x₁, ∫ x₂, spatialCubicMode a μ L m x₁ x₂ r := by
    apply integral_congr_ae
    filter_upwards [hp.prod_right_ae] with r hr
    exact integral_prod _ hr
  rw [hh]
  exact spatialCubicMode_radial_fubini ha hl hlu hs hm h0 hi L m

/-- Complete retained finite cubic kernel, with all three actual Fourier
factors, equals its finite sum of compact-ratio radial integrals. -/
theorem retained_cubic_radial_assembly {a : ℝ → ℂ} {μ : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hs : ∀ x, x ∉ Icc l u → a x = 0)
    (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t) (hi : Integrable μ)
    (L : ℝ) (S : Finset ℤ) :
    kernelCubic (timeMeasure μ) (retainedPoissonKernel (volume.restrict (Icc l u)) a L S) =
      (L:ℂ)^3 * ∑ m₁ ∈ S, ∑ m₂ ∈ S, ∑ m₃ ∈ S,
        ∫ p in Icc (l/u) (u/l) ×ˢ Icc (l/u) (u/l),
          radialKernel a L (m₁,m₂,m₃) p * ratioFourierProduct μ p := by
  obtain ⟨B,hB,hb⟩ := assembly_cutoff_bound ha.continuous hs
  rw [retained_cubic_time_density _ hm h0 hi ha.continuous.measurable hB.le hb]
  simp_rw [retainedAmplitude_product, mul_assoc ((L:ℂ)^3)]
  have heq : ∀ x : Triple,
      (∑ m₁ ∈ S, ∑ m₂ ∈ S, ∑ m₃ ∈ S,
        (a x.1*a x.2.1*a x.2.2)*phase (-L*((m₁:ℝ)*x.1+(m₂:ℝ)*x.2.1+(m₃:ℝ)*x.2.2))) *
        (𝓕 (fun t => (μ t:ℂ)) (mellinFrequency x.2.2-mellinFrequency x.1)*
          𝓕 (fun t => (μ t:ℂ)) (mellinFrequency x.1-mellinFrequency x.2.1)*
          𝓕 (fun t => (μ t:ℂ)) (mellinFrequency x.2.1-mellinFrequency x.2.2)) =
      ∑ m₁ ∈ S, ∑ m₂ ∈ S, ∑ m₃ ∈ S, spatialCubicMode a μ L (m₁,m₂,m₃) x.1 x.2.1 x.2.2 := by
    intro x
    simp only [Finset.sum_mul,spatialCubicMode,mul_assoc]
  simp_rw [heq]
  rw [integral_const_mul]
  congr 1
  have hsint : ∀ m, Integrable (fun x : Triple => spatialCubicMode a μ L m x.1 x.2.1 x.2.2)
      (tripleMeasure (volume.restrict (Icc l u))) := by
    intro m
    have h := (spatialCubicMode_integrable ha.continuous hs hm h0 hi L m).integrableOn
      (s := Icc l u ×ˢ (Icc l u ×ˢ Icc l u))
    simpa only [tripleMeasure,Measure.prod_restrict,Measure.volume_eq_prod,IntegrableOn] using h
  change (∫ x : Triple, ∑ m₁ ∈ S, ∑ m₂ ∈ S, ∑ m₃ ∈ S,
    spatialCubicMode a μ L (m₁,m₂,m₃) x.1 x.2.1 x.2.2 ∂tripleMeasure (volume.restrict (Icc l u))) = _
  rw [integral_finsetSum S (fun m₁ _ => integrable_finsetSum S (fun m₂ _ => integrable_finsetSum S (fun m₃ _ => hsint (m₁,m₂,m₃))))]
  apply Finset.sum_congr rfl
  intro m₁ _
  rw [integral_finsetSum S (fun m₂ _ => integrable_finsetSum S (fun m₃ _ => hsint (m₁,m₂,m₃)))]
  apply Finset.sum_congr rfl
  intro m₂ _
  rw [integral_finsetSum S (fun m₃ _ => hsint (m₁,m₂,m₃))]
  apply Finset.sum_congr rfl
  intro m₃ _
  rw [tripleMeasure,Measure.prod_restrict,Measure.prod_restrict]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => Function.notMem_support.mp
    (fun hn => hx (spatialCubicMode_support hs μ L (m₁,m₂,m₃) hn)))]
  exact spatialCubicMode_integral_radial ha hl hlu hs hm h0 hi L (m₁,m₂,m₃)

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.assembly_cutoff_bound
#print axioms GuthMaynard.Improvement.spatialCubicMode_measurable
#print axioms GuthMaynard.Improvement.spatialCubicMode_support
#print axioms GuthMaynard.Improvement.spatialCubicMode_integrable
#print axioms GuthMaynard.Improvement.spatialCubicMode_integral_radial
#print axioms GuthMaynard.Improvement.retained_cubic_radial_assembly
