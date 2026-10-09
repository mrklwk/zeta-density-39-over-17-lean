import GuthMaynard.Improvement.CenteredKernelBridge
import GuthMaynard.Improvement.CubicLocalError
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff FourierTransform
namespace GuthMaynard.Improvement

theorem retainedPoissonKernel_measurable (ν : Measure ℝ) [SFinite ν]
    {a : ℝ → ℂ} (ha : Measurable a) (L : ℝ) (S : Finset ℤ) :
    Measurable (retainedPoissonKernel ν a L S) := by
  have hA := retainedAmplitude_measurable ha L S
  have hp := phase_measurable
  have hf : Measurable mellinFrequency := by unfold mellinFrequency; fun_prop
  have hh : Measurable (fun z : ℝ × ℝ => retainedAmplitude a L S z.2*phase (z.1*mellinFrequency z.2)) := by fun_prop
  exact hh.stronglyMeasurable.integral_prod_right'.measurable

/-- The actual centered cubic kernel integral differs from the actual
retained Poisson kernel cubic by a uniform homogeneous negligible error.
No operator trace, Poisson identity, or kernel bound is an input premise. -/
theorem centered_cubic_approximation {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hs : ∀ x, x ∉ Icc l u → a x = 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T L t₀ t₁ : ℝ) (μ : ℝ → ℝ),
      1 ≤ T → 1 ≤ L → L ≤ T^2 → t₀ ≤ t₁ → t₁-t₀ ≤ T →
      Measurable μ → (∀ t, 0 ≤ μ t) → Integrable μ → Integrable (fun t => μ t^2) →
      (∀ t, t ∉ Icc t₀ t₁ → μ t = 0) →
      ‖kernelCubic (timeMeasure μ) (centeredKernel a l u L) -
        kernelCubic (timeMeasure μ)
          (retainedPoissonKernel (volume.restrict (Icc l u)) a L (poissonModes (T^(1+η)/L)))‖ ≤
        C*T^(-100:ℝ)*Real.sqrt (∫ t, μ t^2)^3 := by
  obtain ⟨E,hE,herr⟩ := centeredKernel_truncation_negligible ha hl hlu hs hη (show (0:ℝ) ≤ 1 by norm_num)
  obtain ⟨D,hD,hbound⟩ := centeredKernel_uniform_bound ha hl hlu hs
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn ha.continuous.continuousOn
  have hb : ∀ x, ‖a x‖ ≤ max 0 B := by
    intro x
    by_cases hx : x ∈ Icc l u
    · exact (hB x hx).trans (le_max_right _ _)
    · simp [hs x hx]
  refine ⟨3*E*(D+E)^2,by positivity,?_⟩
  intro T L t₀ t₁ μ hT hL hLT ht hlen hm h0 hi h2 hsup
  let J := retainedPoissonKernel (volume.restrict (Icc l u)) a L (poissonModes (T^(1+η)/L))
  have hLp : 0 < L := by linarith
  have hTp : 0 < T := by linarith
  have hpow : T^(-200:ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hT (by norm_num)
  have he : ∀ s, |s| ≤ t₁-t₀ → ‖centeredKernel a l u L s-J s‖ ≤ E*T^(-200:ℝ) := by
    intro s hst
    dsimp only [J]
    rw [retainedPoissonKernel_fourier ha.continuous.measurable hb hs]
    exact herr T L s hT hL hLT (by simpa using hst.trans hlen)
  have hk : ∀ s, |s| ≤ t₁-t₀ → ‖centeredKernel a l u L s‖ ≤ (D+E)*L := by
    intro s _
    exact (hbound L s hL).trans (by nlinarith)
  have hj : ∀ s, |s| ≤ t₁-t₀ → ‖J s‖ ≤ (D+E)*L := by
    intro s hst
    calc
      _ = ‖centeredKernel a l u L s-(centeredKernel a l u L s-J s)‖ := by congr 1; ring
      _ ≤ ‖centeredKernel a l u L s‖ + ‖centeredKernel a l u L s-J s‖ := norm_sub_le _ _
      _ ≤ D*L+E*T^(-200:ℝ) := add_le_add (hbound L s hL) (he s hst)
      _ ≤ (D+E)*L := by nlinarith
  have hp := cubic_local_time_perturbation ht hm h0 hi h2 hsup
    (centeredKernel_measurable ha.continuous.measurable l u L)
    (retainedPoissonKernel_measurable _ ha.continuous.measurable L _)
    (show 0 ≤ (D+E)*L by positivity) (show 0 ≤ E*T^(-200:ℝ) by positivity) hk hj he
  exact hp.trans (poisson_cubic_error_budget hT hLp.le hLT hE (by positivity) hlen)

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.retainedPoissonKernel_measurable
#print axioms GuthMaynard.Improvement.centered_cubic_approximation
