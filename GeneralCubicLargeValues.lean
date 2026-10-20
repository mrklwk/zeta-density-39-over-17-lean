module
public import FiniteCenteredCubic
public import GeneralCenteredMixedTrace

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement

/-- The full cubic large-value inequality with the actual finite signed
amplifier, discrete cubic and improved mixed trace all proved. E is the
literal closed-boundary quadruple count, not an assumed energy bound. -/
theorem finite_cubic_large_value_general (w : MathCollab.Density.ComparisonCutoff)
    {K : ℕ} (hK : 1 ≤ K) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ N L : ℝ,
      2 ≤ T → 1 ≤ N → N ≤ L → T^((4:ℝ)/5) ≤ L → L ≤ T →
      ∀ a : ℕ → ℂ, (∀ n ∈ amplifierSource N, ‖a n‖ ≤ 1) →
      ∀ (W : Finset ℝ) (V : ℝ), 0 ≤ V →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, V ≤ ‖boundedPolynomial N a t‖) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (W.card:ℝ)^3*V^6 ≤ C*T^η*((N*L)^3+
        (N^4*T^2/L)*(W.card:ℝ)*Real.sqrt (W.card:ℝ)+
        N^4*T*Real.sqrt (W.card:ℝ)*Real.sqrt (discreteAdditiveEnergy W:ℝ)+
        N^4*adjacentCenteredBudget K T L W.card) := by
  have hδ : 0 < η/2 := by positivity
  obtain ⟨A,hA,hamp⟩ := finite_signed_amplified_moment w hδ
  obtain ⟨B,hB,hcubic⟩ := centered_matrix_cubic_bound w.toReflectionCutoff hδ
  obtain ⟨D,hD,hmix⟩ := centered_mixed_trace_general w.toReflectionCutoff hK hδ
  refine ⟨A*(1+B+D),by positivity,?_⟩
  intro T t₀ N L hT hN hNL hLl hLu a ha W V hV hW hlarge hsep
  have hT1 : 1 ≤ T := by linarith
  have hTp : 0 < T := by linarith
  have hNp : 0 < N := by linarith
  have hLp : 0 < L := hNp.trans_le hNL
  have hL1 : 1 ≤ L := hN.trans hNL
  have hamp' := hamp T N L (by linarith) hN hNL hLu a ha W V hV hlarge hsep
  have hc := hcubic T L t₀ hT hLl hLu W hW hsep
  have hm := hmix T t₀ L (by linarith) hL1 W hW hsep
  have hm' : ‖Matrix.trace (cutoffContinuousMatrix w.toReflectionCutoff L W*
      cutoffCenteredMatrix w.toReflectionCutoff L W^2)‖ ≤ D*T^(η/2)*L*adjacentCenteredBudget K T L W.card := by
    simpa only [pow_two,mul_assoc] using hm
  let R : ℝ := W.card
  let E : ℝ := discreteAdditiveEnergy W
  let X := (N*L)^3+(N^4*T^2/L)*R*Real.sqrt R+
    N^4*T*Real.sqrt R*Real.sqrt E+N^4*adjacentCenteredBudget K T L R
  have hR0 : 0 ≤ R := Nat.cast_nonneg _
  have hE0 : 0 ≤ E := Nat.cast_nonneg _
  have hbudget : 0 ≤ adjacentCenteredBudget K T L R :=
    adjacentCenteredBudget_nonneg K hTp.le hLp.le hR0
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hTe : 1 ≤ T^(η/2) := Real.one_le_rpow hT1 hδ.le
  have hp : T^(η/2)*T^(η/2)=T^η := by rw [← Real.rpow_add hTp]; congr 1; ring
  have hsum : (N*L)^3+(N^4/L)*
      ((Matrix.trace (cutoffCenteredMatrix w.toReflectionCutoff L W^3)).re+
        (Matrix.trace (cutoffContinuousMatrix w.toReflectionCutoff L W*
          cutoffCenteredMatrix w.toReflectionCutoff L W^2)).re) ≤
      (1+B+D)*T^(η/2)*X := by
    calc
      _ ≤ (N*L)^3+(N^4/L)*(B*T^(η/2)*(T^2*R*Real.sqrt R+T*L*Real.sqrt R*Real.sqrt E)+
          D*T^(η/2)*L*adjacentCenteredBudget K T L R) := by
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add ((Complex.re_le_norm _).trans hc) ((Complex.re_le_norm _).trans hm')
      _ ≤ T^(η/2)*(N*L)^3+(N^4/L)*(B*T^(η/2)*(T^2*R*Real.sqrt R+T*L*Real.sqrt R*Real.sqrt E)+
          D*T^(η/2)*L*adjacentCenteredBudget K T L R) := by
        exact add_le_add (by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hTe (show 0 ≤ (N*L)^3 by positivity)) le_rfl
      _ = T^(η/2)*((N*L)^3+B*((N^4*T^2/L)*R*Real.sqrt R+
          N^4*T*Real.sqrt R*Real.sqrt E)+D*(N^4*adjacentCenteredBudget K T L R)) := by field_simp; ring
      _ ≤ (1+B+D)*T^(η/2)*X := by
        have h₁ : 0 ≤ (N*L)^3 := by positivity
        have h₂ : 0 ≤ (N^4*T^2/L)*R*Real.sqrt R+N^4*T*Real.sqrt R*Real.sqrt E := by positivity
        have h₃ : 0 ≤ N^4*adjacentCenteredBudget K T L R := by positivity
        have hcoef₁ : 1 ≤ 1+B+D := by linarith
        have hcoef₂ : B ≤ 1+B+D := by linarith
        have hcoef₃ : D ≤ 1+B+D := by linarith
        have hb := add_le_add (add_le_add (mul_le_mul_of_nonneg_right hcoef₁ h₁)
          (mul_le_mul_of_nonneg_right hcoef₂ h₂)) (mul_le_mul_of_nonneg_right hcoef₃ h₃)
        have hh := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hTp.le (η/2))
        dsimp [X]
        nlinarith only [hh]
  calc
    _ ≤ _ := hamp'
    _ ≤ A*T^(η/2)*((1+B+D)*T^(η/2)*X) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (A*(1+B+D))*T^η*X := by rw [← hp]; ring


end Montgomery.RationalMoment
