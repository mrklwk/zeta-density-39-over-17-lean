module
public import GuthMaynard.Improvement.SourceRatioAssembly
public import GuthMaynard.Improvement.SourceRatioHeightBudget

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Finset
namespace GuthMaynard.Improvement

/-- Reuse the exact finite height partition at a singleton to partition a
real integral. Endpoints belong to precisely one half-open shell. -/
theorem reflection_dyadic_indicator (F : ℝ → ℝ) (u t : ℝ)
    {Y : ℝ} (hY : 0 ≤ Y) (J : ℕ) :
    (if |t-u| ≤ (2:ℝ)^J*Y then F t else 0) =
      (if |t-u| ≤ Y then F t else 0) +
        ∑ j ∈ range J, if (2:ℝ)^j*Y < |t-u| ∧ |t-u| ≤ (2:ℝ)^(j+1)*Y then F t else 0 := by
  classical
  simpa only [sum_filter,sum_singleton] using
    source_height_dyadic_prefix {()} (fun _ => |t-u|) (fun _ => F t) hY J

/-- Exact ordinary integral decomposition, with no shell-count loss. -/
theorem reflection_dyadic_integral {F : ℝ → ℝ} (hi : Integrable F) (u : ℝ)
    {Y : ℝ} (hY : 0 ≤ Y) (J : ℕ) :
    (∫ t in {t | |t-u| ≤ (2:ℝ)^J*Y}, F t) =
      (∫ t in {t | |t-u| ≤ Y}, F t) +
        ∑ j ∈ range J, ∫ t in {t | (2:ℝ)^j*Y < |t-u| ∧ |t-u| ≤ (2:ℝ)^(j+1)*Y}, F t := by
  have hm : Measurable (fun t : ℝ => |t-u|) := by fun_prop
  have hlow (R : ℝ) : MeasurableSet {t : ℝ | |t-u| ≤ R} := measurableSet_le hm measurable_const
  have hshell (j : ℕ) : MeasurableSet
      {t : ℝ | (2:ℝ)^j*Y < |t-u| ∧ |t-u| ≤ (2:ℝ)^(j+1)*Y} := by
    exact (measurableSet_lt measurable_const hm).inter (hlow _)
  rw [← integral_indicator (hlow _),← integral_indicator (hlow _)]
  have he : {t : ℝ | |t-u| ≤ (2:ℝ)^J*Y}.indicator F =
      fun t => {t : ℝ | |t-u| ≤ Y}.indicator F t +
        ∑ j ∈ range J, {t : ℝ | (2:ℝ)^j*Y < |t-u| ∧ |t-u| ≤ (2:ℝ)^(j+1)*Y}.indicator F t := by
    funext t
    rw [show {t : ℝ | |t-u| ≤ (2:ℝ)^J*Y}.indicator F t =
      (if |t-u| ≤ (2:ℝ)^J*Y then F t else 0) by rfl,
      reflection_dyadic_indicator F u t hY J]
    congr 1
    apply sum_congr rfl
    intro j _
    by_cases hh : (2:ℝ)^j*Y < |t-u| ∧ |t-u| ≤ (2:ℝ)^(j+1)*Y <;> simp [hh]
  rw [he,integral_add (hi.indicator (hlow _))
    (integrable_finsetSum _ (fun j _ => hi.indicator (hshell j))),
    integral_finsetSum _ (fun j _ => hi.indicator (hshell j))]
  simp_rw [integral_indicator (hshell _)]

/-- Uniform geometric shell assembly. Analytic near/shell budgets are
explicit helper premises; their sum costs no logarithmic factor. -/
theorem reflection_dyadic_integral_bound {F : ℝ → ℝ} (hi : Integrable F)
    (u : ℝ) {Y T E B : ℝ} (hY : 0 < Y) (hYT : Y ≤ T) (hB : 0 ≤ B)
    (hs : ∀ t, T < |t-u| → F t = 0)
    (hnear : (∫ t in {t | |t-u| ≤ Y}, F t) ≤ E)
    (hband : ∀ H : ℝ, Y ≤ H → H < T →
      (∫ t in {t | H < |t-u| ∧ |t-u| ≤ 2*H}, F t) ≤ B*H) :
    (∫ t, F t) ≤ E+2*B*T := by
  obtain ⟨J,hcover,hmin,hover,_⟩ := source_least_height_cover hY hYT
  have he : (∫ t in {t | |t-u| ≤ (2:ℝ)^J*Y}, F t) = ∫ t, F t :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => hs t
      (hcover.trans_lt (lt_of_not_ge ht)))
  rw [← he,reflection_dyadic_integral hi u hY.le J]
  apply add_le_add hnear
  have hsum : (∑ j ∈ range J, ∫ t in
      {t | (2:ℝ)^j*Y < |t-u| ∧ |t-u| ≤ (2:ℝ)^(j+1)*Y}, F t) ≤
      B*(∑ j ∈ range J, (2:ℝ)^j*Y) := by
    rw [mul_sum]
    apply sum_le_sum
    intro j hj
    have hjY : Y ≤ (2:ℝ)^j*Y := by
      nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := j)]
    simpa only [pow_succ,mul_assoc,mul_left_comm,mul_comm] using
      hband ((2:ℝ)^j*Y) hjY (hmin j (mem_range.mp hj))
  refine hsum.trans ?_
  rw [source_height_geometric_sum]
  nlinarith

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.reflection_dyadic_indicator
#print axioms GuthMaynard.Improvement.reflection_dyadic_integral
#print axioms GuthMaynard.Improvement.reflection_dyadic_integral_bound
