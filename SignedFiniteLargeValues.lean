module
public import FiniteCutoffOperators

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset InnerProductSpace
open scoped InnerProductSpace
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement

/-- The literal finite large-value spectral inequality. The divisor witness,
both Gram positivities, continuous Schur norm, and signed traces are discharged.
This uses the established comparison cutoff with plateau [1,4]. -/
theorem finite_signed_large_value_comparison (w : MathCollab.Density.ComparisonCutoff)
    {η : ℝ} (hη : 0 < η) :
    ∃ A D : ℝ, 0 < A ∧ 0 < D ∧ ∀ N L : ℝ, 0 < N → N ≤ L →
      ∀ a : ℕ → ℂ, (∀ n ∈ amplifierSource N, ‖a n‖ ≤ 1) →
      ∀ (W : Finset ℝ) (V : ℝ), 0 ≤ V →
      (∀ t ∈ W, V ≤ ‖boundedPolynomial N a t‖) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (L/(2*N))*(max (((W.card:ℝ)*V^2)/(A*(1+L)^η*(N+1))-D*L) 0)^3 ≤
        (Matrix.trace (cutoffCenteredMatrix w.toReflectionCutoff L W^3)).re+
        (Matrix.trace (cutoffContinuousMatrix w.toReflectionCutoff L W*
          cutoffCenteredMatrix w.toReflectionCutoff L W^2)).re := by
  obtain ⟨A,hA,hamp⟩ := finite_amplifier_quantitative_witness hη
  obtain ⟨B,hB,hnorm⟩ := cutoff_continuous_operator_norm w.toReflectionCutoff
  refine ⟨A,B+1,hA,by positivity,?_⟩
  intro N L hN hNL a ha W V hV hlarge hsep
  have hL : 0 < L := hN.trans_le hNL
  have hP : 0 < A*(1+L)^η*(N+1) := by positivity
  obtain ⟨r,hr,v,hv,hwit⟩ := hamp N L (1/2) 5 hN hNL (by norm_num) (by norm_num)
    a w ha w.one_on W
  have hmass : (W.card:ℝ)*V^2 ≤ ∑ t ∈ W, ‖boundedPolynomial N a t‖^2 := by
    calc
      _ = ∑ _t ∈ W, V^2 := by simp
      _ ≤ _ := sum_le_sum (fun t ht => (sq_le_sq₀ hV (norm_nonneg _)).mpr (hlarge t ht))
  have hlevel : ((amplifierColumns N L).card:ℝ)*
      (((W.card:ℝ)*V^2)/(A*(1+L)^η*(N+1))) ≤
      ∑ j, (inner ℂ (v j) (finiteMatrixOperator (cutoffGramMatrix w.toReflectionCutoff L W) (v j))).re := by
    rw [finite_cutoff_gram_eq w.toReflectionCutoff hL W]
    exact (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hmass hP.le) (Nat.cast_nonneg _)).trans hwit
  obtain ⟨hG,hC⟩ := cutoff_matrix_operators_positive w.toReflectionCutoff hL W
  have hnorm' : ‖finiteMatrixOperator (cutoffContinuousMatrix w.toReflectionCutoff L W)‖ ≤ (B+1)*L :=
    (hnorm L hL W hsep).trans (by nlinarith)
  have hspec := operator_finite_signed_spectral_comparison (EuclideanSpace.basisFun W ℂ)
    _ _ hG hC v hv (by simpa using (show (r:ℝ) ≤ (amplifierColumns N L).card by exact_mod_cast hr)) hnorm' hlevel
  have heH : finiteMatrixOperator (cutoffGramMatrix w.toReflectionCutoff L W)-
      finiteMatrixOperator (cutoffContinuousMatrix w.toReflectionCutoff L W) =
      finiteMatrixOperator (cutoffCenteredMatrix w.toReflectionCutoff L W) :=
    (finite_matrix_operator_sub _ _).symm
  rw [heH,← finite_matrix_operator_pow,← finite_matrix_operator_pow,
    ← finite_matrix_operator_mul,finite_matrix_operator_trace,finite_matrix_operator_trace] at hspec
  have hk : L/(2*N) ≤ ((amplifierColumns N L).card:ℝ) := by
    convert (amplifier_columns_card hN hNL).1 using 1
    ring
  exact (mul_le_mul_of_nonneg_right hk (pow_nonneg (le_max_right _ _) 3)).trans hspec

/-- Full finite signed amplifier comparison with the improved mixed trace
inserted in its exact short-polynomial range. The remaining cubic is literal,
not an assumed analytic bound or a conditional density conclusion. -/
theorem finite_signed_large_value_short_range (w : MathCollab.Density.ComparisonCutoff)
    {K : ℕ} (hK : 1 ≤ K) {η : ℝ} (hη : 0 < η) :
    ∃ A D C : ℝ, 0 < A ∧ 0 < D ∧ 0 < C ∧ ∀ T t₀ N L : ℝ,
      1 < T → 0 < N → N ≤ L → 1 ≤ L →
      ∀ a : ℕ → ℂ, (∀ n ∈ amplifierSource N, ‖a n‖ ≤ 1) →
      ∀ (W : Finset ℝ) (V : ℝ), 0 ≤ V →
      T^(((K:ℝ)+1)/(2*K+1)) ≤ W.card → (T/L)^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, V ≤ ‖boundedPolynomial N a t‖) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (L/(2*N))*(max (((W.card:ℝ)*V^2)/(A*(1+L)^η*(N+1))-D*L) 0)^3 ≤
        (Matrix.trace (cutoffCenteredMatrix w.toReflectionCutoff L W^3)).re+
        C*T^η*L^2*(W.card:ℝ)^2 := by
  obtain ⟨A,D,hA,hD,h⟩ := finite_signed_large_value_comparison w hη
  obtain ⟨C,hC,hmix⟩ := centered_mixed_trace_short_range w.toReflectionCutoff hK hη
  refine ⟨A,D,C,hA,hD,hC,?_⟩
  intro T t₀ N L hT hN hNL hL a ha W V hV hR hlen hW hlarge hsep
  have hs := h N L hN hNL a ha W V hV hlarge hsep
  have hq := hmix T t₀ L hT hL W hR hlen hW hsep
  have hq' : ‖Matrix.trace (cutoffContinuousMatrix w.toReflectionCutoff L W*
      cutoffCenteredMatrix w.toReflectionCutoff L W^2)‖ ≤ C*T^η*L^2*(W.card:ℝ)^2 := by
    simpa only [pow_two,mul_assoc] using hq
  exact hs.trans (add_le_add le_rfl ((Complex.re_le_norm _).trans hq'))

end Montgomery.RationalMoment
