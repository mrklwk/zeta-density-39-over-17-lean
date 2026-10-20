module
public import SignedOperatorAmplifier
public import GuthMaynard.Improvement.AmplifierQuantitative
public import CenteredShortTrace

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory InnerProductSpace
open scoped InnerProductSpace
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement

/-- The divisor amplifier evaluated at the literal finite time set. -/
def finiteAmplifierSynthesis (w : ℝ → ℝ) (L : ℝ) (W : Finset ℝ) (M : Finset ℤ) :
    EuclideanSpace ℂ M →L[ℂ] EuclideanSpace ℂ W :=
  (Matrix.toEuclideanLin (fun (t : W) (m : M) =>
    (w ((m:ℝ)/L):ℂ)*GuthMaynard.Improvement.phase ((t:ℝ)*mellinFrequency ((m:ℝ)/L)))).toContinuousLinearMap

theorem finite_amplifier_synthesis_apply (w : ℝ → ℝ) (L : ℝ) (W : Finset ℝ)
    (M : Finset ℤ) (z : EuclideanSpace ℂ M) (t : W) :
    finiteAmplifierSynthesis w L W M z t =
      ∑ m : M, (w ((m:ℝ)/L):ℂ)*GuthMaynard.Improvement.phase ((t:ℝ)*mellinFrequency ((m:ℝ)/L))*z m := rfl

/-- Every divisor column has the exact discrete polynomial mass. -/
theorem finite_amplifier_column_norm {N L l u : ℝ} (hN : 0 < N) (hNL : N ≤ L)
    (hl : l ≤ 1) (hu : 4 ≤ u) (a : ℕ → ℂ) (w : ℝ → ℝ)
    (hw : ∀ x ∈ Set.Icc (1:ℝ) 4, w x=1) (W : Finset ℝ)
    (q : amplifierColumns N L) :
    ‖finiteAmplifierSynthesis w L W (Icc ⌈l*L⌉ ⌊u*L⌋)
      (amplifierOperator N L a (Icc ⌈l*L⌉ ⌊u*L⌋)
        (EuclideanSpace.basisFun (amplifierColumns N L) ℂ q))‖^2 =
      ∑ t ∈ W, ‖boundedPolynomial N a t‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2, ← sum_coe_sort W (fun t => ‖boundedPolynomial N a t‖^2)]
  apply sum_congr rfl
  intro t _
  rw [finite_amplifier_synthesis_apply]
  simp_rw [amplifier_operator_basis]
  have he := amplifier_column_identity hN hNL hl hu a w hw q.property (t:ℝ)
  rw [← sum_coe_sort] at he
  have he' : (∑ m : Icc ⌈l*L⌉ ⌊u*L⌋,
      (w ((m:ℝ)/L):ℂ)*GuthMaynard.Improvement.phase ((t:ℝ)*mellinFrequency ((m:ℝ)/L))*amplifierMatrix N a m q) =
      GuthMaynard.Improvement.phase ((t:ℝ)*mellinFrequency ((q:ℝ)*N/L))*boundedPolynomial N a t := by
    convert he using 1
    apply sum_congr rfl
    intro m _
    ring
  rw [he',norm_mul,phase_norm,one_mul]

theorem finite_amplifier_synthesis_basis (w : ℝ → ℝ) (L : ℝ) (W : Finset ℝ)
    (M : Finset ℤ) (m : M) (t : W) :
    finiteAmplifierSynthesis w L W M (EuclideanSpace.basisFun M ℂ m) t =
      (w ((m:ℝ)/L):ℂ)*GuthMaynard.Improvement.phase ((t:ℝ)*mellinFrequency ((m:ℝ)/L)) := by
  classical
  rw [finite_amplifier_synthesis_apply]
  simp [EuclideanSpace.basisFun_apply]

theorem finite_amplifier_synthesis_adjoint (w : ℝ → ℝ) (L : ℝ) (W : Finset ℝ)
    (M : Finset ℤ) (z : EuclideanSpace ℂ W) (m : M) :
    (finiteAmplifierSynthesis w L W M).adjoint z m =
      ∑ t : W, star ((w ((m:ℝ)/L):ℂ)*
        GuthMaynard.Improvement.phase ((t:ℝ)*mellinFrequency ((m:ℝ)/L)))*z t := by
  rw [← EuclideanSpace.basisFun_inner,ContinuousLinearMap.adjoint_inner_right]
  simp only [PiLp.inner_apply,finite_amplifier_synthesis_basis,RCLike.inner_apply,starRingEnd_apply]
  apply sum_congr rfl
  intro t _
  ring

/-- Literal finite Gram operator, before any use of the continuous correction. -/
def finiteCutoffGram (w : ℝ → ℝ) (L l u : ℝ) (W : Finset ℝ) :
    EuclideanSpace ℂ W →L[ℂ] EuclideanSpace ℂ W :=
  let B := finiteAmplifierSynthesis w L W (Icc ⌈l*L⌉ ⌊u*L⌋)
  B.comp B.adjoint

/-- Every entry of BB* is the literal signed-integer cutoff Gram sum. -/
theorem finite_cutoff_gram_entry (w : ℝ → ℝ) (L l u : ℝ) (W : Finset ℝ)
    (t u' : W) :
    finiteCutoffGram w L l u W (EuclideanSpace.basisFun W ℂ u') t =
      ∑ m ∈ Icc ⌈l*L⌉ ⌊u*L⌋, ((w ((m:ℝ)/L))^2:ℂ)*
        GuthMaynard.Improvement.phase (((t:ℝ)-u')*mellinFrequency ((m:ℝ)/L)) := by
  classical
  simp only [finiteCutoffGram,ContinuousLinearMap.comp_apply,finite_amplifier_synthesis_apply,
    finite_amplifier_synthesis_adjoint]
  simp [EuclideanSpace.basisFun_apply,PiLp.single_apply]
  conv_rhs => rw [← sum_attach,attach_eq_univ]
  apply sum_congr rfl
  intro m _
  have hc (v : ℝ) : star (GuthMaynard.Improvement.phase v) = GuthMaynard.Improvement.phase (-v) :=
    operator_phase_conj v
  simp only [starRingEnd_apply,hc]
  rw [show (((t:ℝ)-u')*mellinFrequency ((m:ℝ)/L)) =
    (t:ℝ)*mellinFrequency ((m:ℝ)/L)+(-((u':ℝ)*mellinFrequency ((m:ℝ)/L))) by ring,phase_add]
  ring

/-- Actual orthonormal divisor witness for the finite time set; no density,
rank hypothesis, spectral premise, or large-value estimate is assumed. -/
theorem finite_amplifier_quantitative_witness {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ N L l u : ℝ, 0 < N → N ≤ L → l ≤ 1 → 4 ≤ u →
      ∀ (a : ℕ → ℂ) (w : ℝ → ℝ),
      (∀ n ∈ amplifierSource N, ‖a n‖ ≤ 1) →
      (∀ x ∈ Set.Icc (1:ℝ) 4, w x=1) → ∀ W : Finset ℝ,
      ∃ r : ℕ, r ≤ (amplifierColumns N L).card ∧
        ∃ v : Fin r → EuclideanSpace ℂ W, Orthonormal ℂ v ∧
          ((amplifierColumns N L).card:ℝ)*
            ((∑ t ∈ W, ‖boundedPolynomial N a t‖^2)/(C*(1+L)^η*(N+1))) ≤
          ∑ j, (inner ℂ (v j) (finiteCutoffGram w L l u W (v j))).re := by
  obtain ⟨C,hC,hnorm⟩ := amplifier_operator_norm hη
  refine ⟨C,hC,?_⟩
  intro N L l u hN hNL hl hu a w ha hw W
  let M := Icc ⌈l*L⌉ ⌊u*L⌋
  let A := amplifierOperator N L a M
  let B := finiteAmplifierSynthesis w L W M
  obtain ⟨r,hr,v,hv,henergy⟩ := amplifier_range_witness A B
  refine ⟨r,by simpa using hr,v,hv,?_⟩
  have hmass : (∑ q : amplifierColumns N L,
      ‖B (A (EuclideanSpace.basisFun (amplifierColumns N L) ℂ q))‖^2) =
      ((amplifierColumns N L).card:ℝ)*(∑ t ∈ W, ‖boundedPolynomial N a t‖^2) := by
    simp_rw [show ∀ q : amplifierColumns N L,
      ‖B (A (EuclideanSpace.basisFun (amplifierColumns N L) ℂ q))‖^2 =
        ∑ t ∈ W, ‖boundedPolynomial N a t‖^2 from
          fun q => finite_amplifier_column_norm hN hNL hl hu a w hw W q]
    simp
  have hnonneg : 0 ≤ ∑ j, (inner ℂ (v j) (B (B.adjoint (v j)))).re := by
    apply sum_nonneg
    intro j _
    rw [← B.adjoint_inner_left,inner_self_eq_norm_sq_to_K]
    exact_mod_cast sq_nonneg ‖B.adjoint (v j)‖
  have hn : ‖A‖^2 ≤ C*(1+L)^η*(N+1) := hnorm N L hN hNL a M ha
  rw [hmass] at henergy
  have hb := henergy.trans (mul_le_mul_of_nonneg_right hn hnonneg)
  have hL : 0 < L := hN.trans_le hNL
  have hD : 0 < C*(1+L)^η*(N+1) := by positivity
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hD).mpr
  simpa only [finiteCutoffGram,ContinuousLinearMap.comp_apply,mul_comm,B,M] using hb

end Montgomery.RationalMoment
