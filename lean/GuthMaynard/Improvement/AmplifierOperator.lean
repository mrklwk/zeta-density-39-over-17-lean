import GuthMaynard.Improvement.AmplifierNorm
import GuthMaynard.Improvement.OperatorKernel
set_option autoImplicit false
noncomputable section
open Finset InnerProductSpace
open scoped InnerProductSpace
namespace GuthMaynard.Improvement

/-- The actual divisor matrix as a bounded operator between finite Hilbert
spaces, with the prescribed signed integer row set. -/
def amplifierOperator (N L : ℝ) (a : ℕ → ℂ) (M : Finset ℤ) :
    EuclideanSpace ℂ (amplifierColumns N L) →L[ℂ] EuclideanSpace ℂ M :=
  (Matrix.toEuclideanLin (fun (m : M) (q : amplifierColumns N L) =>
    amplifierMatrix N a m q)).toContinuousLinearMap

theorem amplifier_operator_apply (N L : ℝ) (a : ℕ → ℂ) (M : Finset ℤ)
    (z : EuclideanSpace ℂ (amplifierColumns N L)) (m : M) :
    amplifierOperator N L a M z m = ∑ q : amplifierColumns N L,
      amplifierMatrix N a m q*z q := rfl

/-- Operator norm squared from the actual divisor estimate. C depends on
eta alone; M may be any finite signed-integer row set. -/
theorem amplifier_operator_norm {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ N L : ℝ, 0 < N → N ≤ L →
      ∀ (a : ℕ → ℂ) (M : Finset ℤ),
      (∀ n ∈ amplifierSource N, ‖a n‖ ≤ 1) →
      ‖amplifierOperator N L a M‖^2 ≤ C*(1+L)^η*(N+1) := by
  classical
  obtain ⟨C,hC,henergy⟩ := amplifier_matrix_energy hη
  refine ⟨C,hC,?_⟩
  intro N L hN hNL a M ha
  have hL : 0 < L := hN.trans_le hNL
  let D := C*(1+L)^η*(N+1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hvec (z : EuclideanSpace ℂ (amplifierColumns N L)) :
      ‖amplifierOperator N L a M z‖^2 ≤ D*‖z‖^2 := by
    let z' : ℕ → ℂ := fun q => if h : q ∈ amplifierColumns N L then z ⟨q,h⟩ else 0
    have hz (q : amplifierColumns N L) : z' q=z q := by simp [z']
    have he := henergy N L hN hNL a z' M ha
    have hq (m : ℤ) : (∑ q ∈ amplifierColumns N L, amplifierMatrix N a m q*z' q) =
        ∑ q : amplifierColumns N L, amplifierMatrix N a m q*z q := by
      rw [← sum_attach]
      exact sum_congr rfl (fun q _ => by rw [hz])
    have hzsum : (∑ q ∈ amplifierColumns N L, ‖z' q‖^2)=‖z‖^2 := by
      rw [← sum_attach,PiLp.norm_sq_eq_of_L2]
      exact sum_congr rfl (fun q _ => by rw [hz])
    simp_rw [hq] at he
    rw [hzsum,← sum_attach] at he
    simpa only [PiLp.norm_sq_eq_of_L2,amplifier_operator_apply,D,Finset.attach_eq_univ] using he
  have hop : ‖amplifierOperator N L a M‖ ≤ Real.sqrt D := by
    apply (amplifierOperator N L a M).opNorm_le_bound (Real.sqrt_nonneg D)
    intro z
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg D) (norm_nonneg z))).mp
    rw [mul_pow,Real.sq_sqrt hD]
    exact hvec z
  exact ((sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg D)).mpr hop).trans_eq (Real.sq_sqrt hD)

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.amplifier_operator_apply
#print axioms GuthMaynard.Improvement.amplifier_operator_norm
