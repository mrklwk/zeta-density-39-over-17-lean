module
public import QuadraticAmplifiedMoment
public import GeneralCenteredTrace

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement

/-- Actual quadratic amplifier and unrestricted adjacent reflected trace.
No cardinality threshold, assumed energy or thinning occurs. -/
theorem finite_quadratic_large_value_general (w : MathCollab.Density.ComparisonCutoff)
    {K : ℕ} (hK : 1 ≤ K) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ N L : ℝ,
      1 < T → 1 ≤ N → N ≤ L → L ≤ T →
      ∀ a : ℕ → ℂ, (∀ n ∈ amplifierSource N, ‖a n‖ ≤ 1) →
      ∀ (W : Finset ℝ) (V : ℝ), 0 ≤ V →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, V ≤ ‖boundedPolynomial N a t‖) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (W.card:ℝ)^2*V^4 ≤ C*T^η*((N*L)^2+
        (N^3/L)*adjacentCenteredBudget K T L W.card) := by
  have hδ : 0 < η/2 := by positivity
  obtain ⟨A,hA,hamp⟩ := finite_quadratic_amplified_moment w hδ
  obtain ⟨B,hB,htrace⟩ := centered_trace_general w.toReflectionCutoff hK hδ
  refine ⟨A*(1+B),by positivity,?_⟩
  intro T t₀ N L hT hN hNL hLT a ha W V hV hW hlarge hsep
  have hTp : 0 < T := by linarith
  have hNp : 0 < N := by linarith
  have hLp : 0 < L := hNp.trans_le hNL
  have hL1 : 1 ≤ L := hN.trans hNL
  have hb := adjacentCenteredBudget_nonneg K hTp.le hLp.le (Nat.cast_nonneg W.card)
  have hamp' := hamp T N L hT hN hNL hLT a ha W V hV hlarge hsep
  have ht := htrace T t₀ L hT hL1 W hW hsep
  have ht' : (Matrix.trace (cutoffCenteredMatrix w.toReflectionCutoff L W^2)).re ≤
      B*T^(η/2)*adjacentCenteredBudget K T L W.card := by
    exact (Complex.re_le_norm _).trans (by simpa only [pow_two] using ht)
  have hp : 1 ≤ T^(η/2) := Real.one_le_rpow hT.le hδ.le
  have he : T^(η/2)*T^(η/2)=T^η := by rw [← Real.rpow_add hTp]; congr 1; ring
  let X := (N*L)^2+(N^3/L)*adjacentCenteredBudget K T L W.card
  have hbudget : (N*L)^2+(N^3/L)*
      (Matrix.trace (cutoffCenteredMatrix w.toReflectionCutoff L W^2)).re ≤
      (1+B)*T^(η/2)*X := by
    calc
      _ ≤ (N*L)^2+(N^3/L)*(B*T^(η/2)*adjacentCenteredBudget K T L W.card) := by gcongr
      _ ≤ T^(η/2)*(N*L)^2+(N^3/L)*(B*T^(η/2)*adjacentCenteredBudget K T L W.card) := by
        gcongr
        exact le_mul_of_one_le_left (sq_nonneg (N*L)) hp
      _ ≤ _ := by
        have h1 : 0 ≤ (N*L)^2 := sq_nonneg _
        have h2 : 0 ≤ (N^3/L)*adjacentCenteredBudget K T L W.card := by positivity
        have hh1 := mul_nonneg hB.le h1
        have hh2 := mul_nonneg (show 0 ≤ 1+B by positivity) h2
        have hi : (N*L)^2+B*((N^3/L)*adjacentCenteredBudget K T L W.card) ≤ (1+B)*X := by
          dsimp [X]
          nlinarith only [hh1,h2]
        have hh := mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg hTp.le (η/2))
        nlinarith only [hh]
  calc
    _ ≤ _ := hamp'
    _ ≤ A*T^(η/2)*((1+B)*T^(η/2)*X) := mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = _ := by rw [← he]; ring

/-- The exact four-term classical quadratic bound used by the five solid
right-hand branches, now for the literal finite bounded polynomial. -/
theorem finite_quadratic_large_value_second (w : MathCollab.Density.ComparisonCutoff)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ N L : ℝ,
      1 < T → 1 ≤ N → N ≤ L → L ≤ T →
      ∀ a : ℕ → ℂ, (∀ n ∈ amplifierSource N, ‖a n‖ ≤ 1) →
      ∀ (W : Finset ℝ) (V : ℝ), 0 ≤ V →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, V ≤ ‖boundedPolynomial N a t‖) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (W.card:ℝ)^2*V^4 ≤ C*T^η*((N*L)^2+N^3*(W.card:ℝ)^2+
        (N^3*T/L)*(W.card:ℝ)^((3:ℝ)/2)+
        N^3*T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12)) := by
  obtain ⟨C,hC,hb⟩ := finite_quadratic_large_value_general w (K:=2) (by norm_num) hη
  refine ⟨C,hC,?_⟩
  intro T t₀ N L hT hN hNL hLT a ha W V hV hW hlarge hsep
  have hLp : 0 < L := (show 0 < N by linarith).trans_le hNL
  have hh := hb T t₀ N L hT hN hNL hLT a ha W V hV hW hlarge hsep
  norm_num [adjacentCenteredBudget] at hh
  convert hh using 1; field_simp; ring

end Montgomery.RationalMoment
