import GuthMaynard.Improvement.ReflectionShellBudget
import GuthMaynard.Improvement.ReflectionNearRow
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- Literal restricted density integral, valid without extra regularity of F. -/
theorem reflection_restrict_density_integral {μ : ℝ → ℝ} (hm : Measurable μ)
    (h0 : ∀ t, 0 ≤ μ t) (S : Set ℝ) (hS : MeasurableSet S) (F : ℝ → ℝ) :
    (∫ t, F t ∂(timeMeasure μ).restrict S) = ∫ t in S, μ t*F t := by
  rw [timeMeasure,restrict_withDensity hS,
    integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (h0 _),smul_eq_mul]

/-- The order-two discarded-mode error is absorbed at the correct scale. -/
theorem reflection_shell_error_absorb {N L H ε : ℝ} (hN : 2 ≤ N) (hNL : N ≤ L)
    (hH : 0 ≤ H) (hε : 0 ≤ ε) (K : ℝ) :
    2*(K*L/L^2)^2*(4*N^2*H) ≤ (8*K^2)*N^ε*L*N*H := by
  have hL : 0 < L := by linarith
  have hn : 1 ≤ N^ε := Real.one_le_rpow (by linarith) hε
  have hratio : N^2/L^2 ≤ 1 := (div_le_one (sq_pos_of_pos hL)).mpr (by nlinarith)
  have he : 2*(K*L/L^2)^2*(4*N^2*H) = 8*K^2*H*(N^2/L^2) := by field_simp; ring
  have hbig : 1 ≤ N^ε*L*N := by nlinarith [mul_le_mul_of_nonneg_right hn hL.le]
  rw [he]
  calc
    _ ≤ 8*K^2*H := by simpa using mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 8*K^2*H)
    _ ≤ (8*K^2*H)*(N^ε*L*N) := by simpa using mul_le_mul_of_nonneg_left hbig (by positivity : 0 ≤ 8*K^2*H)
    _ = _ := by ring

/-- Actual absolute-distance shell bound. No row or error estimate is a
premise: both signed shells and the rapid error are discharged. -/
theorem reflection_absolute_shell_bound (w : MathCollab.Density.ReflectionCutoff)
    {ε A p : ℝ} (hε : 0 < ε) (hA : 1 ≤ A) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ N L H u : ℝ,
      2 ≤ N → N ≤ L → 0 < H → H ≤ A*N^p → ∀ (a : ℕ → ℂ) (μ : ℝ → ℝ),
      (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) → Measurable μ → Integrable μ → (∀ t, 0 ≤ μ t) →
      (∀ t, μ t ≤ ‖boundedPolynomial N a t‖^2) →
      (∫ t in {t : ℝ | H < |t-u| ∧ |t-u| ≤ 2*H},
        μ t*‖centeredKernel (fun x => (w x:ℂ)) (1/2) 5 L (t-u)‖^2) ≤ C*N^ε*L*N*H := by
  obtain ⟨K,C,hK,hC,h⟩ := reflection_signed_shell_budget w (q := 2) (by norm_num) hε hA hp
  refine ⟨2*(C+8*K^2),by positivity,?_⟩
  intro N L H u hN hNL hH hupper a μ ha hm hi h0 hμ
  let := timeMeasure_finite hi
  let F := fun t => μ t*‖centeredKernel (fun x => (w x:ℂ)) (1/2) 5 L (t-u)‖^2
  have hiF : Integrable F := centered_row_integrable w (by linarith) u hi
  have hF0 (t : ℝ) : 0 ≤ F t := mul_nonneg (h0 t) (sq_nonneg _)
  have hsingle (S : Set ℝ) (hS : S ∈ ({Icc (u+H) (u+2*H),Icc (u-2*H) (u-H)} : Set (Set ℝ))) :
      (∫ t in S, F t) ≤ (C+8*K^2)*N^ε*L*N*H := by
    have hSm : MeasurableSet S := by
      rcases hS with rfl | hS
      · exact measurableSet_Icc
      · have heS : S = Icc (u-2*H) (u-H) := hS
        subst S
        exact measurableSet_Icc
    have hmass : ((timeMeasure μ).restrict S).real univ ≤ 4*N^2*H := by
      have he := reflection_restrict_density_integral hm h0 S hSm (fun _ => 1)
      simp only [integral_const,smul_eq_mul,mul_one] at he
      rw [he]
      rcases hS with rfl | hS
      · have hh := source_density_interval_mass hN a ha μ hi hμ (show u+H ≤ u+2*H by linarith)
        convert hh using 1; ring
      · have heS : S = Icc (u-2*H) (u-H) := hS
        subst S
        have hh := source_density_interval_mass hN a ha μ hi hμ (show u-2*H ≤ u-H by linarith)
        convert hh using 1; ring
    have hh := h N L H u hN hNL hH hupper a ha μ hm hi h0 hμ S hS
    rw [reflection_restrict_density_integral hm h0 S hSm] at hh
    have herr := (mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ 2*(K*L/L^2)^2)).trans
      (reflection_shell_error_absorb hN hNL hH.le hε.le K)
    calc
      _ ≤ C*N^ε*L*N*H+(8*K^2)*N^ε*L*N*H := hh.trans (add_le_add le_rfl herr)
      _ = _ := by ring
  have hdis : Disjoint (Icc (u+H) (u+2*H)) (Icc (u-2*H) (u-H)) := by
    apply Set.disjoint_left.mpr
    intro t ht ht'
    linarith [ht.1,ht'.2]
  have hsub : {t : ℝ | H < |t-u| ∧ |t-u| ≤ 2*H} ⊆
      Icc (u+H) (u+2*H) ∪ Icc (u-2*H) (u-H) := by
    intro t ht
    change H < |t-u| ∧ |t-u| ≤ 2*H at ht
    rcases lt_or_ge (t-u) 0 with hn | hn
    · right
      rw [abs_of_neg hn] at ht
      constructor <;> linarith [ht.1,ht.2]
    · left
      rw [abs_of_nonneg hn] at ht
      constructor <;> linarith [ht.1,ht.2]
  calc
    _ ≤ ∫ t in Icc (u+H) (u+2*H) ∪ Icc (u-2*H) (u-H), F t :=
      setIntegral_mono_set hiF.integrableOn (Filter.Eventually.of_forall hF0)
        (Filter.Eventually.of_forall (fun t ht => hsub ht))
    _ = (∫ t in Icc (u+H) (u+2*H), F t)+(∫ t in Icc (u-2*H) (u-H), F t) :=
      setIntegral_union hdis measurableSet_Icc hiF.integrableOn hiF.integrableOn
    _ ≤ (C+8*K^2)*N^ε*L*N*H+(C+8*K^2)*N^ε*L*N*H :=
      add_le_add (hsingle _ (by simp)) (hsingle _ (by simp))
    _ = _ := by ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.reflection_restrict_density_integral
#print axioms GuthMaynard.Improvement.reflection_shell_error_absorb
#print axioms GuthMaynard.Improvement.reflection_absolute_shell_bound
