module
public import GuthMaynard.Improvement.SourceTailConditional

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- Finite dyadic layer bound; the last endpoint and strict threshold are exact. -/
theorem removed_square_dyadic {x U : ℝ} (hx : 0 ≤ x)
    (J : ℕ) (hb : x ≤ 2^J*U) :
    (if U < x then x^2 else 0) ≤
      ∑ j ∈ Finset.range J, (if 2^j*U < x then 4*(2^j*U)^2 else 0) := by
  induction J with
  | zero => simp only [pow_zero, one_mul] at hb; simp [not_lt.mpr hb]
  | succ J ih =>
    rw [Finset.sum_range_succ]
    by_cases hj : x ≤ 2^J*U
    · exact (ih hj).trans (le_add_of_nonneg_right (by split_ifs <;> positivity))
    · have ht : 2^J*U < x := lt_of_not_ge hj
      have hp : x^2 ≤ 4*(2^J*U)^2 := by
        have hh := pow_le_pow_left₀ hx hb 2
        rw [pow_succ (2:ℝ) J] at hh
        nlinarith
      have hn : 0 ≤ ∑ j ∈ Finset.range J,
          (if 2^j*U < x then 4*(2^j*U)^2 else 0) := by
        apply Finset.sum_nonneg
        intro j _
        split_ifs <;> positivity
      simp only [ht, reduceIte]
      split_ifs <;> nlinarith

/-- Integrate actual removed density against a finite collection of its strict
superlevels. No continuity or boundary-null assumption is needed. -/
theorem source_removed_mass_dyadic {β : ℝ → ℝ} (hβm : Measurable β)
    (hβi : Integrable β) (hβ0 : ∀ t, 0 ≤ β t) (hβ1 : ∀ t, β t ≤ 1)
    {D : ℝ → ℂ} (hDm : Measurable D) {U : ℝ}
    (J : ℕ) (hb : ∀ t, ‖D t‖ ≤ 2^J*U) :
    (∫ t, sourceRemovedDensity β D U t) ≤
      ∑ j ∈ Finset.range J, 4*(2^j*U)^2*
        (∫ t, {t | 2^j*U < ‖D t‖}.indicator β t) := by
  have hi j : Integrable (fun t => 4*(2^j*U)^2*
      {t | 2^j*U < ‖D t‖}.indicator β t) :=
    (hβi.indicator (measurableSet_lt measurable_const hDm.norm)).const_mul _
  have hr := (source_density_regular hβm hβi hβ0 hβ1 hDm hb U).2.2.2.2.1
  calc
    _ ≤ ∫ t, ∑ j ∈ Finset.range J, 4*(2^j*U)^2*
        {t | 2^j*U < ‖D t‖}.indicator β t := by
      apply integral_mono hr (integrable_finsetSum _ (fun j _ => hi j))
      intro t
      have hh := mul_le_mul_of_nonneg_left
        (removed_square_dyadic (norm_nonneg (D t)) J (hb t)) (hβ0 t)
      convert hh using 1
      · by_cases ht : U < ‖D t‖ <;> simp [sourceRemovedDensity,ht,not_le]
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        by_cases ht : 2^j*U < ‖D t‖ <;> simp only [Set.indicator_apply, Set.mem_ofPred_eq, ht, reduceIte, mul_zero]
        ring
    _ = _ := by
      rw [integral_finsetSum _ (fun j _ => hi j)]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul]

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.removed_square_dyadic
#print axioms GuthMaynard.Improvement.source_removed_mass_dyadic
