module
public import GuthMaynard.Improvement.CubicClosure
public import GuthMaynard.Improvement.OrdinaryFourierMoments

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped FourierTransform
namespace GuthMaynard.Improvement

/-- Exact ordinary Fourier threshold budgets, in the normalized Fourier
coordinate with Plancherel constant one. No moment bound is assumed. -/
theorem ordinary_fourier_threshold_budgets {μ : ℝ → ℝ}
    (h0 : ∀ t, 0 ≤ μ t) (h1 : Integrable μ) (h2 : Integrable (fun t => μ t^2))
    {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    let F := 𝓕 (fun t => (μ t:ℂ))
    let A := {ξ | Λ < ‖F ξ‖}
    (∫ ξ in A, ‖F ξ‖^2) ≤ ∫ t, μ t^2 ∧
    (∫ ξ in Aᶜ, ‖F ξ‖^4) ≤ Λ^2*(∫ t, μ t^2) ∧
    (∫ ξ, ‖F ξ‖^4) ≤ Λ^2*(∫ t, μ t^2)+(∫ t, μ t)^2*(∫ ξ in A, ‖F ξ‖^2) := by
  let F := 𝓕 (fun t => (μ t:ℂ))
  let A := {ξ | Λ < ‖F ξ‖}
  have hc : Continuous F := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ (Complex.ofRealCLM.integrable_comp h1)
  have hs := ordinary_real_fourier_square_integrable h1 h2
  have hf := ordinary_real_fourier_fourth_integrable h0 h1 h2
  have hp := ordinary_real_fourier_integral_square h1 h2
  have hsplit := fourth_moment_level_split hc.measurable.norm (fun _ => norm_nonneg _)
    (fourier_nonneg_mass h0) hΛ hs hf
  rw [hp] at hsplit
  refine ⟨?_,?_,hsplit.2⟩
  · exact (setIntegral_le_integral hs (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).trans_eq hp
  · simpa only [A,mem_ofPred_eq,compl_ofPred,not_lt] using hsplit.1

/-- Closing helper for an arbitrary complex quantity H. The only remaining
analytic premise is the displayed masked majorant; all ordinary Fourier
threshold estimates are derived. This does not assert a trace theorem. -/
theorem ordinary_restricted_cubic_of_masked {μ : ℝ → ℝ}
    (h0 : ∀ t, 0 ≤ μ t) (h1 : Integrable μ) (h2 : Integrable (fun t => μ t^2))
    {Λ Q T L : ℝ} (hΛ : 0 ≤ Λ) (hQ : 0 ≤ Q) (hT : 0 ≤ T) (hL : 0 ≤ L)
    (H : ℂ) :
    let F := 𝓕 (fun t => (μ t:ℂ))
    let M := ∫ t, μ t^2
    let M₁ := ∫ t, μ t
    let A := {ξ | Λ < ‖F ξ‖}
    let A₂ := ∫ ξ in A, ‖F ξ‖^2
    let E := ∫ ξ, ‖F ξ‖^4
    let E₀ := ∫ ξ in Aᶜ, ‖F ξ‖^4
    ‖H‖ ≤ Q*(T^2*M*Real.sqrt M+T*L*Real.sqrt M*Real.sqrt E₀+
      Real.sqrt A₂*(T^2*M+T*L*Real.sqrt E)) →
    ‖H‖ ≤ 3*Q*(T^2*M*Real.sqrt M+T*L*Λ*M+T*L*M₁*A₂) := by
  dsimp only
  intro hmasked
  obtain ⟨hA,hE₀,hE⟩ := ordinary_fourier_threshold_budgets h0 h1 h2 hΛ
  have hm : 0 ≤ ∫ t, μ t^2 := integral_nonneg (fun _ => sq_nonneg _)
  have hm1 : 0 ≤ ∫ t, μ t := integral_nonneg h0
  have ha : 0 ≤ ∫ ξ in {ξ | Λ < ‖𝓕 (fun t => (μ t:ℂ)) ξ‖}, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hh := restricted_cubic_of_masked (H := ‖H‖) (c := 1) hQ hT hL hm hm1 ha hΛ
    (by norm_num) (by simpa using hA) (by simpa using hE₀) (by simpa using hE)
    (by simpa only [abs_of_nonneg (norm_nonneg H)] using hmasked)
  simpa only [abs_of_nonneg (norm_nonneg H),mul_one,one_mul,
    show (1:ℝ)+2=3 by norm_num,mul_comm Q 3] using hh

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.ordinary_fourier_threshold_budgets
#print axioms GuthMaynard.Improvement.ordinary_restricted_cubic_of_masked
