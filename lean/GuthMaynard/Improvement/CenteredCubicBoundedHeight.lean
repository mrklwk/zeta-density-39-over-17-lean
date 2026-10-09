import GuthMaynard.Improvement.CenteredKernelBridge
import GuthMaynard.Improvement.CubicTimeMeasure
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace GuthMaynard.Improvement

/-- Actual centered cubic, with its full homogeneous mass cubed and
L cubed. The kernel bound is derived from the fixed smooth cutoff. -/
theorem centered_cubic_mass_bound {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hs : ∀ x, x ∉ Icc l u → a x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) (μ : ℝ → ℝ),
      1 ≤ L → Measurable μ → (∀ t, 0 ≤ μ t) → Integrable μ →
      Integrable (fun t : Triple => centeredKernel a l u L (t.1-t.2.1)*
        centeredKernel a l u L (t.2.1-t.2.2)*centeredKernel a l u L (t.2.2-t.1))
          (tripleMeasure (timeMeasure μ)) ∧
      ‖kernelCubic (timeMeasure μ) (centeredKernel a l u L)‖ ≤
        C*L^3*(∫ t, μ t)^3 := by
  obtain ⟨D,hD,hbound⟩ := centeredKernel_uniform_bound ha hl hlu hs
  refine ⟨D^3,by positivity,?_⟩
  intro L μ hL hm h0 hi
  let := timeMeasure_finite hi
  let : IsFiniteMeasure (tripleMeasure (timeMeasure μ)) := by unfold tripleMeasure; infer_instance
  have hLp : 0 < L := by linarith
  have hDL : 0 ≤ D*L := mul_nonneg hD hLp.le
  refine ⟨kernelCubic_integrable (timeMeasure μ)
    (centeredKernel_measurable ha.continuous.measurable l u L) hDL
    (fun s => hbound L s hL),?_⟩
  have hp (t : Triple) :
      ‖centeredKernel a l u L (t.1-t.2.1)*centeredKernel a l u L (t.2.1-t.2.2)*
        centeredKernel a l u L (t.2.2-t.1)‖ ≤ (D*L)^3 := by
    simp only [norm_mul]
    calc
      _ ≤ (D*L)*(D*L)*(D*L) := by gcongr <;> exact hbound L _ hL
      _ = _ := by ring
  have hh := norm_integral_le_of_norm_le_const
    (μ := tripleMeasure (timeMeasure μ)) (Filter.Eventually.of_forall hp)
  rw [tripleMeasure_mass,timeMeasure_mass hm h0] at hh
  simpa only [kernelCubic,mul_pow] using hh

/-- Uniform bounded-height absorption. The constant is chosen after the
fixed height cutoff T0 and before T,L,the interval and the ordinary density.
There is no assumed pointwise kernel bound and no positive-mass division. -/
theorem centered_cubic_bounded_height {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hs : ∀ x, x ∉ Icc l u → a x = 0)
    (T₀ : ℝ) (_hT₀ : 1 ≤ T₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T L t₀ t₁ : ℝ) (μ : ℝ → ℝ),
      1 ≤ T → T ≤ T₀ → 1 ≤ L → L ≤ T → t₀ ≤ t₁ → t₁-t₀ ≤ T →
      Measurable μ → (∀ t, 0 ≤ μ t) → Integrable μ → Integrable (fun t => μ t^2) →
      (∀ t, t ∉ Icc t₀ t₁ → μ t = 0) →
      ‖kernelCubic (timeMeasure μ) (centeredKernel a l u L)‖ ≤
        C*T^2*Real.sqrt (∫ t, μ t^2)^3 := by
  obtain ⟨D,hD,hbound⟩ := centered_cubic_mass_bound ha hl hlu hs
  refine ⟨D*T₀^4,by positivity,?_⟩
  intro T L t₀ t₁ μ hT hTT₀ hL hLT ht hlen hm h0 hi h2 hsup
  have hTp : 0 < T := by linarith
  have hLp : 0 < L := by linarith
  have hsqrt : Real.sqrt (t₁-t₀) ≤ T := (Real.sqrt_le_iff).mpr ⟨hTp.le,by nlinarith⟩
  have hmass : (∫ t, μ t) ≤ T*Real.sqrt (∫ t, μ t^2) :=
    (compact_time_mass_bound ht hm h0 h2 hsup).trans (by gcongr)
  have hm0 : 0 ≤ ∫ t, μ t := integral_nonneg h0
  have hscale : L^3*T^3 ≤ T₀^4*T^2 := by
    calc
      _ ≤ T^3*T^3 := by gcongr
      _ = T^4*T^2 := by ring
      _ ≤ _ := by gcongr
  calc
    _ ≤ D*L^3*(∫ t, μ t)^3 := (hbound L μ hL hm h0 hi).2
    _ ≤ D*L^3*(T*Real.sqrt (∫ t, μ t^2))^3 := by gcongr
    _ = D*(L^3*T^3)*Real.sqrt (∫ t, μ t^2)^3 := by ring
    _ ≤ D*(T₀^4*T^2)*Real.sqrt (∫ t, μ t^2)^3 := by gcongr
    _ = _ := by ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.centered_cubic_mass_bound
#print axioms GuthMaynard.Improvement.centered_cubic_bounded_height
