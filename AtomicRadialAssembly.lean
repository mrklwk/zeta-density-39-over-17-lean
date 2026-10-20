module
public import AtomicRadialFubini

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped FourierTransform ContDiff
namespace GuthMaynard.Improvement.AtomicCubic

theorem spatialCubicMode_measurable {a : ℝ → ℂ} {F : ℝ → ℂ}
    (ha : Measurable a) (hF : Continuous F) (L : ℝ) (m : ℤ × (ℤ × ℤ)) :
    Measurable (fun x : Triple => spatialCubicMode a F L m x.1 x.2.1 x.2.2) := by
  have hp := phase_measurable
  have hf := hF.measurable
  have hm : Measurable mellinFrequency := by unfold mellinFrequency; fun_prop
  unfold spatialCubicMode
  fun_prop

theorem spatialCubicMode_support {a : ℝ → ℂ} {l u : ℝ}
    (hs : ∀ x, x ∉ Icc l u → a x = 0) (F : ℝ → ℂ) (L : ℝ) (m : ℤ × (ℤ × ℤ)) :
    Function.support (fun x : Triple => spatialCubicMode a F L m x.1 x.2.1 x.2.2) ⊆
      Icc l u ×ˢ (Icc l u ×ˢ Icc l u) := by
  intro x hx
  by_contra hn
  have h : x.1 ∉ Icc l u ∨ x.2.1 ∉ Icc l u ∨ x.2.2 ∉ Icc l u := by simpa only [Set.mem_prod,not_and_or] using hn
  rcases h with h | h | h <;> exact hx (by simp [spatialCubicMode,hs _ h])

theorem spatialCubicMode_integrable {a : ℝ → ℂ} {F : ℝ → ℂ}
    (ha : Continuous a) {l u : ℝ} (hs : ∀ x, x ∉ Icc l u → a x = 0)
    (hF : Continuous F) {M : ℝ} (hM : 0 ≤ M) (hbF : ∀ ξ, ‖F ξ‖ ≤ M)
    (L : ℝ) (m : ℤ × (ℤ × ℤ)) :
    Integrable (fun x : Triple => spatialCubicMode a F L m x.1 x.2.1 x.2.2) := by
  have hE : IsCompact (Icc l u ×ˢ (Icc l u ×ˢ Icc l u)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  apply (integrableOn_iff_integrable_of_support_subset (spatialCubicMode_support hs F L m)).mp
  obtain ⟨B,hB,hb⟩ := assembly_cutoff_bound ha hs
  apply (integrableOn_const hE.measure_lt_top.ne (C := B^3*M^3)).mono'
    (spatialCubicMode_measurable ha.measurable hF L m).aestronglyMeasurable
  filter_upwards with x
  simp only [spatialCubicMode,norm_mul,phase_norm,mul_one]
  calc
    _ ≤ (B*B*B)*(M*M*M) := by
      gcongr <;> first | exact hb _ | exact hbF _
    _ = _ := by ring

/-- Actual coordinate reordering followed by the proved radial Fubini identity. -/
theorem spatialCubicMode_integral_radial {a : ℝ → ℂ} {F : ℝ → ℂ}
    (ha : ContDiff ℝ ∞ a) {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hs : ∀ x, x ∉ Icc l u → a x = 0)
    (hF : Continuous F) {M : ℝ} (hM : 0 ≤ M) (hbF : ∀ ξ, ‖F ξ‖ ≤ M)
    (L : ℝ) (m : ℤ × (ℤ × ℤ)) :
    (∫ x : Triple, spatialCubicMode a F L m x.1 x.2.1 x.2.2) =
      ∫ p in Icc (l/u) (u/l) ×ˢ Icc (l/u) (u/l),
        radialKernel a L m p * ratioFourierProduct F p := by
  let e : Triple ≃ᵐ Triple := MeasurableEquiv.prodComm.trans MeasurableEquiv.prodAssoc
  have he : MeasurePreserving e volume volume :=
    (measurePreserving_prodAssoc volume volume volume).comp Measure.measurePreserving_swap
  have hf := spatialCubicMode_integrable ha.continuous hs hF hM hbF L m
  have hp := he.integrable_comp_of_integrable hf
  rw [← he.integral_comp' (fun x : Triple => spatialCubicMode a F L m x.1 x.2.1 x.2.2)]
  change (∫ x : Triple, spatialCubicMode a F L m x.2.1 x.2.2 x.1) = _
  change Integrable (fun x : Triple => spatialCubicMode a F L m x.2.1 x.2.2 x.1) (volume.prod volume) at hp
  change (∫ x : Triple, spatialCubicMode a F L m x.2.1 x.2.2 x.1 ∂volume.prod volume) = _
  rw [integral_prod _ hp]
  have hh : (∫ r, ∫ p : ℝ × ℝ, spatialCubicMode a F L m p.1 p.2 r) =
      ∫ r, ∫ x₁, ∫ x₂, spatialCubicMode a F L m x₁ x₂ r := by
    apply integral_congr_ae
    filter_upwards [hp.prod_right_ae] with r hr
    exact integral_prod _ hr
  rw [hh]
  exact spatialCubicMode_radial_fubini ha hl hlu hs hF hM hbF L m

/-- Complete retained finite cubic kernel, with all three actual Fourier
factors, equals its finite sum of compact-ratio radial integrals. -/
theorem retained_cubic_radial_assembly (ν : Measure ℝ) [IsFiniteMeasure ν] {a : ℝ → ℂ}
    (ha : ContDiff ℝ ∞ a) {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hs : ∀ x, x ∉ Icc l u → a x = 0)
    (L : ℝ) (S : Finset ℤ) :
    kernelCubic ν (retainedPoissonKernel (volume.restrict (Icc l u)) a L S) =
      (L:ℂ)^3 * ∑ m₁ ∈ S, ∑ m₂ ∈ S, ∑ m₃ ∈ S,
        ∫ p in Icc (l/u) (u/l) ×ˢ Icc (l/u) (u/l),
          radialKernel a L (m₁,m₂,m₃) p * ratioFourierProduct (measureFourier ν) p := by
  obtain ⟨B,hB,hb⟩ := assembly_cutoff_bound ha.continuous hs
  have hF := operator_measureFourier_continuous ν
  have hM : 0 ≤ ν.real univ := ENNReal.toReal_nonneg
  have hbF (ξ : ℝ) : ‖measureFourier ν ξ‖ ≤ ν.real univ := by
    simpa only [measureFourier,one_mul] using norm_integral_le_of_norm_le_const
      (μ := ν) (f := fun t => phase (-ξ*t)) (C := 1)
      (Filter.Eventually.of_forall (fun t => (phase_norm _).le))
  rw [retainedPoissonKernel_cubic ν _ ha.continuous.measurable hB.le hb]
  simp_rw [retainedAmplitude_product, mul_assoc ((L:ℂ)^3)]
  have heq : ∀ x : Triple,
      (∑ m₁ ∈ S, ∑ m₂ ∈ S, ∑ m₃ ∈ S,
        (a x.1*a x.2.1*a x.2.2)*phase (-L*((m₁:ℝ)*x.1+(m₂:ℝ)*x.2.1+(m₃:ℝ)*x.2.2))) *
        (measureFourier ν (mellinFrequency x.2.2-mellinFrequency x.1)*
          measureFourier ν (mellinFrequency x.1-mellinFrequency x.2.1)*
          measureFourier ν (mellinFrequency x.2.1-mellinFrequency x.2.2)) =
      ∑ m₁ ∈ S, ∑ m₂ ∈ S, ∑ m₃ ∈ S, spatialCubicMode a (measureFourier ν) L (m₁,m₂,m₃) x.1 x.2.1 x.2.2 := by
    intro x
    simp only [Finset.sum_mul,spatialCubicMode,mul_assoc]
  simp_rw [heq]
  rw [integral_const_mul]
  congr 1
  have hsint : ∀ m, Integrable (fun x : Triple => spatialCubicMode a (measureFourier ν) L m x.1 x.2.1 x.2.2)
      (tripleMeasure (volume.restrict (Icc l u))) := by
    intro m
    have h := (spatialCubicMode_integrable ha.continuous hs hF hM hbF L m).integrableOn
      (s := Icc l u ×ˢ (Icc l u ×ˢ Icc l u))
    simpa only [tripleMeasure,Measure.prod_restrict,Measure.volume_eq_prod,IntegrableOn] using h
  change (∫ x : Triple, ∑ m₁ ∈ S, ∑ m₂ ∈ S, ∑ m₃ ∈ S,
    spatialCubicMode a (measureFourier ν) L (m₁,m₂,m₃) x.1 x.2.1 x.2.2 ∂tripleMeasure (volume.restrict (Icc l u))) = _
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
    (fun hn => hx (spatialCubicMode_support hs (measureFourier ν) L (m₁,m₂,m₃) hn)))]
  exact spatialCubicMode_integral_radial ha hl hlu hs hF hM hbF L (m₁,m₂,m₃)

end GuthMaynard.Improvement.AtomicCubic
