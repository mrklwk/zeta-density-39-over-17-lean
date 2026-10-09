module
public import Mathlib

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- Log-coordinate transfer for any nonnegative integrable density. The
constant is the exact bound on the weighted Jacobian v*w(v). -/
theorem log_weight_integral {w h : ℝ → ℝ} {B : ℝ}
    (hw : Measurable w) (hw0 : ∀ v, 0 ≤ w v)
    (_hB : 0 ≤ B) (hbound : ∀ v, 0 < v → v*w v ≤ B)
    (hz : ∀ v, v ≤ 0 → w v = 0) (hh : Integrable h) (hh0 : ∀ u, 0 ≤ h u) :
    Integrable (fun v => w v*h (Real.log v)) ∧
      (∫ v, w v*h (Real.log v)) ≤ B*(∫ u, h u) := by
  have hm : Measurable (fun u => Real.exp u*w (Real.exp u)) :=
    Real.measurable_exp.mul (hw.comp Real.measurable_exp)
  have hb : ∀ u, ‖Real.exp u*w (Real.exp u)‖ ≤ B := by
    intro u
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.exp_pos u).le (hw0 _))]
    exact hbound _ (Real.exp_pos u)
  have hi := hh.bdd_mul hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  have hi' : Integrable (fun u => Real.exp u • (w (Real.exp u)*h (Real.log (Real.exp u)))) := by
    simpa only [Real.log_exp,smul_eq_mul,mul_assoc] using hi
  have hio := (integrable_comp_exp (fun v => w v*h (Real.log v))).mp hi'
  have heq : (Ioi (0:ℝ)).indicator (fun v => w v*h (Real.log v)) =
      (fun v => w v*h (Real.log v)) := by
    funext v
    by_cases hv : 0 < v
    · simp [hv]
    · simp [hv,hz v (le_of_not_gt hv)]
  have hfull : Integrable (fun v => w v*h (Real.log v)) := by
    have := hio.integrable_indicator measurableSet_Ioi
    rwa [heq] at this
  refine ⟨hfull,?_⟩
  have hid := integral_comp_exp (fun v => w v*h (Real.log v))
  rw [← integral_indicator measurableSet_Ioi,heq] at hid
  rw [← hid]
  simp only [Real.log_exp,smul_eq_mul] at hi' ⊢
  calc
    _ ≤ ∫ u, B*h u := integral_mono hi' (hh.const_mul B) (fun u => by
      simp only [Real.log_exp, smul_eq_mul] at *
      nlinarith [mul_le_mul_of_nonneg_right (hbound _ (Real.exp_pos u)) (hh0 u)])
    _ = _ := integral_const_mul _ _

/-- Every measurable mask retains its own mass under log coordinates.
No boundary assumption, positive-mass assumption, or division by mass. -/
theorem log_mask_integral {w h : ℝ → ℝ} {B : ℝ} {A : Set ℝ}
    (hw : Measurable w) (hw0 : ∀ v, 0 ≤ w v)
    (hB : 0 ≤ B) (hbound : ∀ v, 0 < v → v*w v ≤ B)
    (hz : ∀ v, v ≤ 0 → w v = 0) (hA : MeasurableSet A)
    (hh : Integrable h) (hh0 : ∀ u, 0 ≤ h u) :
    Integrable (fun v => w v*A.indicator h (Real.log v)) ∧
      (∫ v, w v*A.indicator h (Real.log v)) ≤ B*(∫ u in A, h u) := by
  have hn : ∀ u, 0 ≤ A.indicator h u := by
    intro u
    by_cases hu : u ∈ A <;> simp [hu,hh0]
  simpa only [integral_indicator hA] using
    log_weight_integral hw hw0 hB hbound hz (hh.indicator hA) hn

/-- Explicit fixed-cutoff Jacobian constant for the ratio
masks. Apply to h=|F|²,w=omega and h=|F|⁴,w=omega². -/
theorem log_compact_mask_integral {w h : ℝ → ℝ} {a b W : ℝ} {A : Set ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hW : 0 ≤ W)
    (hw : Measurable w) (hw0 : ∀ v, 0 ≤ w v) (hwW : ∀ v, w v ≤ W)
    (hs : ∀ v, v ∉ Icc a b → w v = 0) (hA : MeasurableSet A)
    (hh : Integrable h) (hh0 : ∀ u, 0 ≤ h u) :
    Integrable (fun v => w v*A.indicator h (Real.log v)) ∧
      (∫ v, w v*A.indicator h (Real.log v)) ≤ b*W*(∫ u in A, h u) := by
  have hb : 0 ≤ b := ha.le.trans hab
  apply log_mask_integral hw hw0 (mul_nonneg hb hW) _ _ hA hh hh0
  · intro v hv
    by_cases hx : v ∈ Icc a b
    · exact mul_le_mul hx.2 (hwW v) (hw0 v) hb
    · rw [hs v hx,mul_zero]
      exact mul_nonneg hb hW
  · intro v hv
    exact hs v (fun hx => by linarith [hx.1])

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.log_weight_integral
#print axioms GuthMaynard.Improvement.log_mask_integral

#print axioms GuthMaynard.Improvement.log_compact_mask_integral
