module
public import DensityEnergyGM.PoweredLargeValues
public import GuthMaynard.Improvement.RealIntegerSource

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset Complex GuthMaynard.NativeMoment GuthMaynard.Improvement
namespace Montgomery.RationalMoment

/-- The real normalized source at an integer scale has exactly the native
open dyadic support. -/
theorem sourceRatioIndices_nat (M : ℕ) : sourceRatioIndices (M:ℝ)=Ioc M (2*M) := by
  simp only [sourceRatioIndices,Nat.floor_natCast]
  have hf : ⌊2*(M:ℝ)⌋₊=2*M := by
    norm_cast
    exact Nat.floor_natCast _
  rw [hf]

/-- Conjugation and a common unit phase identify the actual normalized
positive-phase polynomial with the native negative-phase polynomial in norm. -/
theorem norm_boundedPolynomial_native_conjugate {M : ℕ} (hM : 0<M)
    (a : ℕ → ℂ) (t : ℝ) :
    ‖boundedPolynomial (M:ℝ) (conjugateCoeffs a) t‖ = ‖dirichletPoly M a t‖ := by
  rw [boundedPolynomial_norm_integer_sum (by exact_mod_cast hM),sourceRatioIndices_nat]
  have hSum : (∑ n ∈ Ioc M (2*M), conjugateCoeffs a n*dirichletPhase n t) =
      sourceDirichletPoly M (conjugateCoeffs a) t := by
    unfold sourceDirichletPoly dyadicInterval
    apply sum_congr rfl
    intro n hn
    simp only [dirichletPhase]
    congr 2
    rw [Complex.cpow_def_of_ne_zero (by
      have hh : 0<n := lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp hn).1
      exact_mod_cast hh.ne')]
    rw [← Complex.natCast_log]
    congr 1
    push_cast
    ring
  rw [hSum,norm_sourceDirichletPoly_conjugateCoeffs]

end Montgomery.RationalMoment
