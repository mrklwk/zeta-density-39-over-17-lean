module
public import QuadraticSpectralComparison

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset InnerProductSpace
open scoped InnerProductSpace
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement

/-- The literal finite quadratic large-value spectral inequality. The divisor witness,
both Gram positivities, continuous Schur norm, and the quadratic trace are discharged.
This uses the established comparison cutoff with plateau [1,4]. -/
theorem finite_quadratic_large_value_comparison (w : MathCollab.Density.ComparisonCutoff)
    {η : ℝ} (hη : 0 < η) :
    ∃ A D : ℝ, 0 < A ∧ 0 < D ∧ ∀ N L : ℝ, 0 < N → N ≤ L →
      ∀ a : ℕ → ℂ, (∀ n ∈ amplifierSource N, ‖a n‖ ≤ 1) →
      ∀ (W : Finset ℝ) (V : ℝ), 0 ≤ V →
      (∀ t ∈ W, V ≤ ‖boundedPolynomial N a t‖) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (L/(2*N))*(max (((W.card:ℝ)*V^2)/(A*(1+L)^η*(N+1))-D*L) 0)^2 ≤
        (Matrix.trace (cutoffCenteredMatrix w.toReflectionCutoff L W^2)).re := by
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
  have hspec := operator_finite_quadratic_comparison (EuclideanSpace.basisFun W ℂ)
    _ _ hG hC v hv (by simpa using (show (r:ℝ) ≤ (amplifierColumns N L).card by exact_mod_cast hr)) hnorm' hlevel
  have heH : finiteMatrixOperator (cutoffGramMatrix w.toReflectionCutoff L W)-
      finiteMatrixOperator (cutoffContinuousMatrix w.toReflectionCutoff L W) =
      finiteMatrixOperator (cutoffCenteredMatrix w.toReflectionCutoff L W) :=
    (finite_matrix_operator_sub _ _).symm
  rw [heH,← finite_matrix_operator_pow,finite_matrix_operator_trace] at hspec
  have hk : L/(2*N) ≤ ((amplifierColumns N L).card:ℝ) := by
    convert (amplifier_columns_card hN hNL).1 using 1
    ring
  exact (mul_le_mul_of_nonneg_right hk (pow_nonneg (le_max_right _ _) 2)).trans hspec


end Montgomery.RationalMoment
