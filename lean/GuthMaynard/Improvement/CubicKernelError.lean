module
public import GuthMaynard.Improvement.CubicKernel

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace GuthMaynard.Improvement

/-- Actual triple measure mass, including the zero measure. -/
theorem tripleMeasure_mass (μ : Measure ℝ) [SFinite μ] :
    (tripleMeasure μ).real Set.univ = (μ.real Set.univ)^3 := by
  simp only [tripleMeasure,Measure.real]
  rw [← Set.univ_prod_univ,Measure.prod_prod,← Set.univ_prod_univ,Measure.prod_prod]
  rw [ENNReal.toReal_mul,ENNReal.toReal_mul]
  ring

theorem kernelCubic_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    {K : ℝ → ℂ} {B : ℝ} (hK : Measurable K) (hB : 0 ≤ B) (hb : ∀ s, ‖K s‖ ≤ B) :
    Integrable (fun t : Triple => K (t.1-t.2.1)*K (t.2.1-t.2.2)*K (t.2.2-t.1))
      (tripleMeasure μ) := by
  let : IsFiniteMeasure (tripleMeasure μ) := by unfold tripleMeasure; infer_instance
  apply (integrable_const (B^3)).mono' (by fun_prop)
  filter_upwards with t
  simp only [norm_mul]
  calc
    _ ≤ B*B*B := mul_le_mul (mul_le_mul (hb _) (hb _) (norm_nonneg _) hB) (hb _) (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Perturbation of the actual cubic kernel integral. The full mass cubed
is retained; no normalized absolute error or positive-mass division occurs. -/
theorem kernelCubic_perturbation (μ : Measure ℝ) [IsFiniteMeasure μ]
    {K J : ℝ → ℂ} {B e : ℝ} (hK : Measurable K) (hJ : Measurable J)
    (hB : 0 ≤ B) (he : 0 ≤ e) (hbK : ∀ s, ‖K s‖ ≤ B) (hbJ : ∀ s, ‖J s‖ ≤ B)
    (herr : ∀ s, ‖K s-J s‖ ≤ e) :
    ‖kernelCubic μ K-kernelCubic μ J‖ ≤ 3*e*B^2*(μ.real Set.univ)^3 := by
  let : IsFiniteMeasure (tripleMeasure μ) := by unfold tripleMeasure; infer_instance
  have hki := kernelCubic_integrable μ hK hB hbK
  have hji := kernelCubic_integrable μ hJ hB hbJ
  unfold kernelCubic
  rw [← integral_sub hki hji]
  have hp : ∀ t : Triple,
      ‖K (t.1-t.2.1)*K (t.2.1-t.2.2)*K (t.2.2-t.1)-
        J (t.1-t.2.1)*J (t.2.1-t.2.2)*J (t.2.2-t.1)‖ ≤ 3*e*B^2 := by
    intro t
    let a := t.1-t.2.1
    let b := t.2.1-t.2.2
    let c := t.2.2-t.1
    change ‖K a*K b*K c-J a*J b*J c‖ ≤ _
    have hid : K a*K b*K c-J a*J b*J c =
        (K a-J a)*K b*K c+J a*(K b-J b)*K c+J a*J b*(K c-J c) := by ring
    rw [hid]
    calc
      _ ≤ ‖(K a-J a)*K b*K c‖+‖J a*(K b-J b)*K c‖+‖J a*J b*(K c-J c)‖ := norm_add₃_le
      _ ≤ e*B*B+B*e*B+B*B*e := by
        simp only [norm_mul]
        gcongr
        · exact herr a
        · exact hbK b
        · exact hbK c
        · exact hbJ a
        · exact herr b
        · exact hbK c
        · exact hbJ a
        · exact hbJ b
        · exact herr c
      _ = _ := by ring
  have hh := norm_integral_le_of_norm_le_const (μ := tripleMeasure μ) (Filter.Eventually.of_forall hp)
  rw [tripleMeasure_mass] at hh
  exact hh

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.tripleMeasure_mass
#print axioms GuthMaynard.Improvement.kernelCubic_integrable
#print axioms GuthMaynard.Improvement.kernelCubic_perturbation
