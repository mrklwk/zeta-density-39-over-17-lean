module
public import GuthMaynard.Improvement.AmplifierWitness
public import GuthMaynard.Improvement.OperatorDensityVector

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory InnerProductSpace Finset
open scoped InnerProductSpace
namespace GuthMaynard.Improvement

/-- The literal finite feature map B, on the same signed frequency rows as G. -/
def amplifierSynthesis (ν : Measure ℝ) [IsFiniteMeasure ν] (w : ℝ → ℝ)
    (L : ℝ) (M : Finset ℤ) : EuclideanSpace ℂ M →L[ℂ] Lp ℂ 2 ν :=
  ∑ m : M, rankOne ℂ
    ((w ((m:ℝ)/L):ℂ) • operatorPhase ν (mellinFrequency ((m:ℝ)/L)))
    (EuclideanSpace.basisFun M ℂ m)

theorem amplifier_synthesis_apply (ν : Measure ℝ) [IsFiniteMeasure ν]
    (w : ℝ → ℝ) (L : ℝ) (M : Finset ℤ) (z : EuclideanSpace ℂ M) :
    amplifierSynthesis ν w L M z = ∑ m : M,
      (z m*(w ((m:ℝ)/L):ℂ)) • operatorPhase ν (mellinFrequency ((m:ℝ)/L)) := by
  simp only [amplifierSynthesis,_root_.sum_apply,rankOne_apply,EuclideanSpace.basisFun_inner,smul_smul]

theorem amplifier_synthesis_basis (ν : Measure ℝ) [IsFiniteMeasure ν]
    (w : ℝ → ℝ) (L : ℝ) (M : Finset ℤ) (m : M) :
    amplifierSynthesis ν w L M (EuclideanSpace.basisFun M ℂ m) =
      (w ((m:ℝ)/L):ℂ) • operatorPhase ν (mellinFrequency ((m:ℝ)/L)) := by
  classical
  rw [amplifier_synthesis_apply]
  simp [EuclideanSpace.basisFun_apply]

theorem amplifier_synthesis_adjoint (ν : Measure ℝ) [IsFiniteMeasure ν]
    (w : ℝ → ℝ) (L : ℝ) (M : Finset ℤ) (v : Lp ℂ 2 ν) (m : M) :
    (amplifierSynthesis ν w L M).adjoint v m =
      inner ℂ ((w ((m:ℝ)/L):ℂ) • operatorPhase ν (mellinFrequency ((m:ℝ)/L))) v := by
  rw [← EuclideanSpace.basisFun_inner,
    ContinuousLinearMap.adjoint_inner_right,amplifier_synthesis_basis]

/-- Exact BB* factorization of the actual discrete operator with cutoff w². -/
theorem amplifier_synthesis_factorization (ν : Measure ℝ) [IsFiniteMeasure ν]
    (w : ℝ → ℝ) (L l u : ℝ) :
    (amplifierSynthesis ν w L (Icc ⌈l*L⌉ ⌊u*L⌋)).comp
      (amplifierSynthesis ν w L (Icc ⌈l*L⌉ ⌊u*L⌋)).adjoint =
        operatorDiscrete ν (fun x => w x^2) L l u := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply,amplifier_synthesis_apply]
  simp_rw [amplifier_synthesis_adjoint,inner_smul_left,Complex.conj_ofReal]
  unfold operatorDiscrete
  simp only [_root_.sum_apply,smul_apply,rankOne_apply,smul_smul]
  conv_rhs => rw [← sum_attach,attach_eq_univ]
  apply sum_congr rfl
  intro m _
  congr 1
  push_cast
  ring

/-- The actual matrix acts on each standard column by its literal entries. -/
theorem amplifier_operator_basis (N L : ℝ) (a : ℕ → ℂ) (M : Finset ℤ)
    (q : amplifierColumns N L) (m : M) :
    amplifierOperator N L a M (EuclideanSpace.basisFun (amplifierColumns N L) ℂ q) m =
      amplifierMatrix N a m q := by
  classical
  rw [amplifier_operator_apply]
  simp [EuclideanSpace.basisFun_apply]

/-- Literal Lp column representative. Equality holds almost everywhere for
any finite time measure, before any assumption on the time density. -/
theorem amplifier_synthesis_column (ν : Measure ℝ) [IsFiniteMeasure ν]
    {N L l u : ℝ} (hN : 0 < N) (hNL : N ≤ L) (hl : l ≤ 1) (hu : 4 ≤ u)
    (a : ℕ → ℂ) (w : ℝ → ℝ) (hw : ∀ x ∈ Set.Icc (1:ℝ) 4, w x=1)
    (q : amplifierColumns N L) :
    (amplifierSynthesis ν w L (Icc ⌈l*L⌉ ⌊u*L⌋)
      (amplifierOperator N L a (Icc ⌈l*L⌉ ⌊u*L⌋)
        (EuclideanSpace.basisFun (amplifierColumns N L) ℂ q)) : ℝ → ℂ) =ᵐ[ν]
      fun t => phase (t*mellinFrequency ((q:ℝ)*N/L))*boundedPolynomial N a t := by
  rw [amplifier_synthesis_apply]
  simp_rw [amplifier_operator_basis]
  refine (Lp.coeFn_finsetSum _ _).trans ?_
  have hterm (m : Icc ⌈l*L⌉ ⌊u*L⌋) :
      (((amplifierMatrix N a m q*(w ((m:ℝ)/L):ℂ)) •
        operatorPhase ν (mellinFrequency ((m:ℝ)/L)) : Lp ℂ 2 ν) : ℝ → ℂ) =ᵐ[ν]
      fun t => amplifierMatrix N a m q*(w ((m:ℝ)/L):ℂ)*
        phase (t*mellinFrequency ((m:ℝ)/L)) :=
    (Lp.coeFn_smul _ _).trans ((operator_phase_coe ν _).const_smul _)
  have he := eventuallyEq_sum (s := Finset.univ) (fun m _ => hterm m)
  refine he.trans ?_
  filter_upwards with t
  have hh := amplifier_column_identity hN hNL hl hu a w hw q.property t
  rw [← sum_attach,attach_eq_univ] at hh
  simpa only [mul_assoc,Finset.sum_apply] using hh

/-- Every constructed column has exactly the original polynomial L2 mass;
the extra q-dependent phase has norm one. -/
theorem amplifier_synthesis_column_norm (ν : Measure ℝ) [IsFiniteMeasure ν]
    {N L l u : ℝ} (hN : 0 < N) (hNL : N ≤ L) (hl : l ≤ 1) (hu : 4 ≤ u)
    (a : ℕ → ℂ) (w : ℝ → ℝ) (hw : ∀ x ∈ Set.Icc (1:ℝ) 4, w x=1)
    (q : amplifierColumns N L) :
    ‖amplifierSynthesis ν w L (Icc ⌈l*L⌉ ⌊u*L⌋)
      (amplifierOperator N L a (Icc ⌈l*L⌉ ⌊u*L⌋)
        (EuclideanSpace.basisFun (amplifierColumns N L) ℂ q))‖^2 =
      ∫ t, ‖boundedPolynomial N a t‖^2 ∂ν := by
  rw [← operator_L2_integral_sq]
  apply integral_congr_ae
  filter_upwards [amplifier_synthesis_column ν hN hNL hl hu a w hw q] with t ht
  rw [ht,norm_mul,phase_norm,one_mul]

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.amplifier_synthesis_apply
#print axioms GuthMaynard.Improvement.amplifier_synthesis_basis
#print axioms GuthMaynard.Improvement.amplifier_synthesis_adjoint
#print axioms GuthMaynard.Improvement.amplifier_synthesis_factorization
#print axioms GuthMaynard.Improvement.amplifier_operator_basis
#print axioms GuthMaynard.Improvement.amplifier_synthesis_column
#print axioms GuthMaynard.Improvement.amplifier_synthesis_column_norm
