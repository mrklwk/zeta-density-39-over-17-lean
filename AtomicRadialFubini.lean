module
public import AtomicRadialCoordinates

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace GuthMaynard.Improvement.AtomicCubic

def radialIntegrand (a : ℝ → ℂ) (F : ℝ → ℂ) (L : ℝ)
    (m : ℤ × (ℤ × ℤ)) (r : ℝ) (p : ℝ × ℝ) : ℂ :=
  radialAmplitude a p.1 p.2 r *
    phase (-L*((m.1:ℝ)*p.1+(m.2.1:ℝ)*p.2+(m.2.2:ℝ))*r) * ratioFourierProduct F p

theorem radialIntegrand_measurable {a : ℝ → ℂ} {F : ℝ → ℂ}
    (ha : Measurable a) (hF : Continuous F) (L : ℝ) (m : ℤ × (ℤ × ℤ)) :
    Measurable (fun z : ℝ × (ℝ × ℝ) => radialIntegrand a F L m z.1 z.2) := by
  have hp := phase_measurable
  have hf := ratio_fourier_measurable hF
  unfold radialIntegrand radialAmplitude
  fun_prop

/-- Absolute integrability on the full radial/ratio space is proved from
actual compact support and Fourier mass bounds, with no Fubini premise. -/
theorem radialIntegrand_integrable {a : ℝ → ℂ} {F : ℝ → ℂ}
    (ha : ContDiff ℝ ∞ a) {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hs : ∀ x, x ∉ Icc l u → a x = 0)
    (hF : Continuous F) {M : ℝ} (hM : 0 ≤ M) (hbF : ∀ ξ, ‖F ξ‖ ≤ M)
    (L : ℝ) (m : ℤ × (ℤ × ℤ)) :
    Integrable (fun z : ℝ × (ℝ × ℝ) => radialIntegrand a F L m z.1 z.2) := by
  let Q := Icc (l/u) (u/l) ×ˢ Icc (l/u) (u/l)
  let E := Icc l u ×ˢ Q
  have hE : IsCompact E := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hsup : Function.support (fun z : ℝ × (ℝ × ℝ) => radialIntegrand a F L m z.1 z.2) ⊆ E := by
    intro z hz
    apply radialAmplitude_support hl hlu hs
    intro h
    exact hz (by simp [radialIntegrand,h])
  apply (integrableOn_iff_integrable_of_support_subset hsup).mp
  obtain ⟨C,hC,hb⟩ := radialAmplitude_uniform_deriv ha hs (l/u) (u/l) (l/u) (u/l) 0
  apply (integrableOn_const hE.measure_lt_top.ne (C := C*M^3)).mono'
    (radialIntegrand_measurable ha.continuous.measurable hF L m).aestronglyMeasurable
  apply ae_restrict_of_forall_mem hE.measurableSet
  intro z hz
  have hb' : ‖radialAmplitude a z.2.1 z.2.2 z.1‖ ≤ C := by
    simpa using hb z.2.1 hz.2.1 z.2.2 hz.2.2 z.1
  simp only [radialIntegrand,norm_mul,phase_norm,mul_one]
  exact mul_le_mul hb' (ratio_fourier_bound hM hbF z.2) (norm_nonneg _) hC.le

/-- Fubini moves the actual radial integral inside the ratio integral.
The original three Fourier factors and the exact Jacobian are preserved. -/
theorem spatialCubicMode_radial_fubini {a : ℝ → ℂ} {F : ℝ → ℂ}
    (ha : ContDiff ℝ ∞ a) {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hs : ∀ x, x ∉ Icc l u → a x = 0)
    (hF : Continuous F) {M : ℝ} (hM : 0 ≤ M) (hbF : ∀ ξ, ‖F ξ‖ ≤ M)
    (L : ℝ) (m : ℤ × (ℤ × ℤ)) :
    (∫ r, ∫ x₁, ∫ x₂, spatialCubicMode a F L m x₁ x₂ r) =
      ∫ p in Icc (l/u) (u/l) ×ˢ Icc (l/u) (u/l),
        radialKernel a L m p * ratioFourierProduct F p := by
  have ha0 : ∀ x, x ≤ 0 → a x = 0 := by
    intro x hx
    exact hs x (fun h => (not_lt_of_ge hx) (lt_of_lt_of_le hl h.1))
  rw [spatialCubicMode_radial_integrals ha0]
  have hInt := radialIntegrand_integrable ha hl hlu hs hF hM hbF L m
  have hip : Integrable (fun z : ℝ × (ℝ × ℝ) => radialIntegrand a F L m z.1 z.2)
      (volume.prod volume) := hInt
  have hsplit : (∫ r, ∫ v, ∫ y, radialIntegrand a F L m r (v,y)) =
      ∫ r, ∫ p : ℝ × ℝ, radialIntegrand a F L m r p := by
    apply integral_congr_ae
    filter_upwards [hip.prod_right_ae] with r hr
    exact (integral_prod _ hr).symm
  change (∫ r, ∫ v, ∫ y, radialIntegrand a F L m r (v,y)) = _
  rw [hsplit,integral_integral_swap hip]
  have hp : ∀ p, (∫ r, radialIntegrand a F L m r p) =
      radialKernel a L m p * ratioFourierProduct F p := by
    intro p
    exact integral_mul_const _ _
  simp_rw [hp]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  have hz : ∀ r, radialAmplitude a p.1 p.2 r = 0 := by
    intro r
    by_contra hn
    exact hp (radialAmplitude_support hl hlu hs hn).2
  simp [radialKernel,hz]

end GuthMaynard.Improvement.AtomicCubic
