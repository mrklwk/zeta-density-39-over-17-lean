module
public import GuthMaynard.Improvement.AmplifierSynthesis

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory InnerProductSpace Finset
open scoped InnerProductSpace
namespace GuthMaynard.Improvement

/-- The actual quantitative amplifier witness, derived from the literal
matrix and feature map. The constant precedes all scales, coefficients,
cutoffs and finite time measures. -/
theorem amplifier_quantitative_witness {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N L l u : ℝ), 0 < N → N ≤ L → l ≤ 1 → 4 ≤ u →
      ∀ (a : ℕ → ℂ) (w : ℝ → ℝ),
      (∀ n ∈ amplifierSource N, ‖a n‖ ≤ 1) →
      (∀ x ∈ Set.Icc (1:ℝ) 4, w x=1) →
      ∀ (ν : Measure ℝ) [IsFiniteMeasure ν],
      ∃ r : ℕ, r ≤ (amplifierColumns N L).card ∧
        ∃ v : Fin r → Lp ℂ 2 ν, Orthonormal ℂ v ∧
          ((amplifierColumns N L).card:ℝ)*
            ((∫ t, ‖boundedPolynomial N a t‖^2 ∂ν)/(C*(1+L)^η*(N+1))) ≤
          ∑ j, (inner ℂ (v j) (operatorDiscrete ν (fun x => w x^2) L l u (v j))).re := by
  obtain ⟨C,hC,hnorm⟩ := amplifier_operator_norm hη
  refine ⟨C,hC,?_⟩
  intro N L l u hN hNL hl hu a w ha hw ν _
  let M := Icc ⌈l*L⌉ ⌊u*L⌋
  let A := amplifierOperator N L a M
  let B := amplifierSynthesis ν w L M
  obtain ⟨r,hr,v,hv,henergy⟩ := amplifier_range_witness A B
  refine ⟨r,by simpa using hr,v,hv,?_⟩
  have hmass : (∑ q : amplifierColumns N L,
      ‖B (A (EuclideanSpace.basisFun (amplifierColumns N L) ℂ q))‖^2) =
      ((amplifierColumns N L).card:ℝ)*(∫ t, ‖boundedPolynomial N a t‖^2 ∂ν) := by
    simp_rw [show ∀ q : amplifierColumns N L,
      ‖B (A (EuclideanSpace.basisFun (amplifierColumns N L) ℂ q))‖^2 =
        ∫ t, ‖boundedPolynomial N a t‖^2 ∂ν from
          fun q => amplifier_synthesis_column_norm ν hN hNL hl hu a w hw q]
    simp
  have hfactor (x : Lp ℂ 2 ν) : B (B.adjoint x)=operatorDiscrete ν (fun x => w x^2) L l u x := by
    exact congrArg (fun T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν => T x)
      (amplifier_synthesis_factorization ν w L l u)
  have hnonneg : 0 ≤ ∑ j, (inner ℂ (v j) (B (B.adjoint (v j)))).re := by
    apply sum_nonneg
    intro j _
    rw [← B.adjoint_inner_left,inner_self_eq_norm_sq_to_K]
    exact_mod_cast sq_nonneg ‖B.adjoint (v j)‖
  have hn : ‖A‖^2 ≤ C*(1+L)^η*(N+1) := hnorm N L hN hNL a M ha
  rw [hmass] at henergy
  have hb := henergy.trans (mul_le_mul_of_nonneg_right hn hnonneg)
  simp_rw [hfactor] at hb
  have hL : 0 < L := hN.trans_le hNL
  have hD : 0 < C*(1+L)^η*(N+1) := by positivity
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hD).mpr
  simpa only [mul_comm] using hb

set_option maxHeartbeats 800000 in
/-- Ordinary nonnegative integrable time densities require no separate finite
measure premise; the mass in the level is the literal weighted polynomial mass. -/
theorem amplifier_time_density_witness {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N L l u : ℝ), 0 < N → N ≤ L → l ≤ 1 → 4 ≤ u →
      ∀ (a : ℕ → ℂ) (w : ℝ → ℝ),
      (∀ n ∈ amplifierSource N, ‖a n‖ ≤ 1) →
      (∀ x ∈ Set.Icc (1:ℝ) 4, w x=1) →
      ∀ (μ : ℝ → ℝ), Measurable μ → (hiμ : Integrable μ) → (∀ t, 0 ≤ μ t) →
      let := timeMeasure_finite hiμ
      ∃ r : ℕ, r ≤ (amplifierColumns N L).card ∧
        ∃ v : Fin r → Lp ℂ 2 (timeMeasure μ), Orthonormal ℂ v ∧
          ((amplifierColumns N L).card:ℝ)*
            ((∫ t, μ t*‖boundedPolynomial N a t‖^2)/(C*(1+L)^η*(N+1))) ≤
          ∑ j, (inner ℂ (v j)
            (operatorDiscrete (timeMeasure μ) (fun x => w x^2) L l u (v j))).re := by
  obtain ⟨C,hC,h⟩ := amplifier_quantitative_witness hη
  refine ⟨C,hC,?_⟩
  intro N L l u hN hNL hl hu a w ha hw μ hm hiμ h0
  let := timeMeasure_finite hiμ
  have he : (∫ t, ‖boundedPolynomial N a t‖^2 ∂timeMeasure μ) =
      ∫ t, μ t*‖boundedPolynomial N a t‖^2 := by
    unfold timeMeasure
    rw [integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (h0 _),smul_eq_mul]
  simpa only [he] using h N L l u hN hNL hl hu a w ha hw (timeMeasure μ)

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.amplifier_quantitative_witness

#print axioms GuthMaynard.Improvement.amplifier_time_density_witness
