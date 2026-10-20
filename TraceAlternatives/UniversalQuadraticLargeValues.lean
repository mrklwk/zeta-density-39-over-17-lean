module
public import QuadraticAmplifiedMoment
public import TraceAlternatives.UniversalCenteredTrace

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement

/-- The actual quadratic amplifier with the sharp reflected trace.
Every analytic input is supplied, with the original closed ordered energy. -/
theorem finite_quadratic_large_value_universal (w : MathCollab.Density.ComparisonCutoff)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ N L : ℝ,
      2 ≤ T → 1 ≤ N → N ≤ L → Real.sqrt T ≤ L → L ≤ T →
      ∀ a : ℕ → ℂ, (∀ n ∈ amplifierSource N, ‖a n‖ ≤ 1) →
      ∀ (W : Finset ℝ) (V : ℝ), 0 ≤ V →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, V ≤ ‖boundedPolynomial N a t‖) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (W.card:ℝ)^2*V^4 ≤ C*T^η*((N*L)^2+
        (N^3/L)*universalCenteredBudget T L W.card (discreteAdditiveEnergy W)) := by
  have hδ : 0 < η/2 := by positivity
  obtain ⟨A,hA,hamp⟩ := finite_quadratic_amplified_moment w hδ
  obtain ⟨B,hB,htrace⟩ := centered_trace_universal w.toReflectionCutoff hδ
  refine ⟨A*(1+B),by positivity,?_⟩
  intro T t₀ N L hT hN hNL hLs hLT a ha W V hV hW hlarge hsep
  have hTp : 0 < T := by linarith
  have hNp : 0 < N := by linarith
  have hLp : 0 < L := hNp.trans_le hNL
  have hb := universalCenteredBudget_nonneg hTp.le hLp.le (Nat.cast_nonneg W.card) (Nat.cast_nonneg (discreteAdditiveEnergy W))
  have hamp' := hamp T N L (by linarith) hN hNL hLT a ha W V hV hlarge hsep
  have ht := htrace T t₀ L hT hLs W hW hsep
  have ht' : (Matrix.trace (cutoffCenteredMatrix w.toReflectionCutoff L W^2)).re ≤
      B*T^(η/2)*universalCenteredBudget T L W.card (discreteAdditiveEnergy W) := by
    exact (Complex.re_le_norm _).trans (by simpa only [pow_two] using ht)
  have hp : 1 ≤ T^(η/2) := Real.one_le_rpow (by linarith) hδ.le
  have he : T^(η/2)*T^(η/2)=T^η := by rw [← Real.rpow_add hTp]; congr 1; ring
  let X := (N*L)^2+(N^3/L)*universalCenteredBudget T L W.card (discreteAdditiveEnergy W)
  have hbudget : (N*L)^2+(N^3/L)*
      (Matrix.trace (cutoffCenteredMatrix w.toReflectionCutoff L W^2)).re ≤
      (1+B)*T^(η/2)*X := by
    calc
      _ ≤ (N*L)^2+(N^3/L)*(B*T^(η/2)*universalCenteredBudget T L W.card (discreteAdditiveEnergy W)) := by gcongr
      _ ≤ T^(η/2)*(N*L)^2+(N^3/L)*(B*T^(η/2)*universalCenteredBudget T L W.card (discreteAdditiveEnergy W)) := by
        gcongr
        exact le_mul_of_one_le_left (sq_nonneg (N*L)) hp
      _ ≤ _ := by
        have h1 : 0 ≤ (N*L)^2 := sq_nonneg _
        have h2 : 0 ≤ (N^3/L)*universalCenteredBudget T L W.card (discreteAdditiveEnergy W) := by positivity
        have hh1 := mul_nonneg hB.le h1
        have hh2 := mul_nonneg (show 0 ≤ 1+B by positivity) h2
        have hi : (N*L)^2+B*((N^3/L)*universalCenteredBudget T L W.card (discreteAdditiveEnergy W)) ≤ (1+B)*X := by
          dsimp [X]
          nlinarith only [hh1,h2]
        have hh := mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg hTp.le (η/2))
        nlinarith only [hh]
  calc
    _ ≤ _ := hamp'
    _ ≤ A*T^(η/2)*((1+B)*T^(η/2)*X) := mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = _ := by rw [← he]; ring


end Montgomery.RationalMoment
