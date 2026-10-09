module
public import GuthMaynard.Improvement.CubicStripGeometry

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- Restricted inversion change of variables with its actual Jacobian.
No global integrability of q composed with inversion is assumed. -/
theorem inverse_ratio_integral {q : ℝ → ℝ} (hq : Integrable q)
    (hq0 : ∀ x, 0 ≤ q x) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (fun v => q (1/v)) (Icc a b) ∧
      (∫ v in Icc a b, q (1/v)) ≤ b^2*(∫ u, q u) := by
  have hb : 0 < b := ha.trans_le hab
  have hd : ∀ x ∈ Icc a b, HasDerivWithinAt (fun v : ℝ => v⁻¹)
      (-(x^2)⁻¹) (Icc a b) x := by
    intro x hx
    exact (hasDerivAt_inv (ne_of_gt (ha.trans_le hx.1))).hasDerivWithinAt
  have hinj : InjOn (fun v : ℝ => v⁻¹) (Icc a b) := inv_injective.injOn
  have hweight : IntegrableOn (fun v : ℝ => |-(v^2)⁻¹| *q v⁻¹) (Icc a b) := by
    simpa only [smul_eq_mul] using
      (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Icc hd hinj q).mp hq.integrableOn
  have hnorm : ∀ᵐ v ∂volume.restrict (Icc a b), ‖v^2‖ ≤ b^2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg v)]
    exact pow_le_pow_left₀ (ha.trans_le hv.1).le hv.2 2
  have heq (v : ℝ) (hv : v ∈ Icc a b) :
      v^2*(|-(v^2)⁻¹| *q v⁻¹) = q (1/v) := by
    have hv0 : v ≠ 0 := ne_of_gt (ha.trans_le hv.1)
    rw [abs_neg,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg v)),← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ hv0),one_mul,one_div]
  have hi : IntegrableOn (fun v => q (1/v)) (Icc a b) :=
    (hweight.bdd_mul (by fun_prop) hnorm).congr (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
      exact heq v hv)
  refine ⟨hi,?_⟩
  have hchange := integral_image_eq_integral_abs_deriv_smul measurableSet_Icc hd hinj q
  simp only [smul_eq_mul] at hchange
  calc
    _ ≤ ∫ v in Icc a b, b^2*(|-(v^2)⁻¹| *q v⁻¹) := by
      apply integral_mono_ae hi (hweight.const_mul (b^2))
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
      rw [← heq v hv]
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (abs_nonneg _) (hq0 _))
      exact pow_le_pow_left₀ (ha.trans_le hv.1).le hv.2 2
    _ = b^2*(∫ u in (fun v : ℝ => v⁻¹) '' Icc a b, q u) := by
      rw [integral_const_mul,← hchange]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (integral_mono_measure Measure.restrict_le_self (Filter.Eventually.of_forall hq0) hq)
      (sq_nonneg b)

/-- Squared genuine finite affine sum after inversion. The integrability
premise concerns the ordinary affine sum on the whole line, which is the
input provided by an affine L2 theorem; the inverse-composed sum is proved
integrable only on the required compact positive ratio interval. -/
theorem inverse_ratio_affine_square (S : Finset (ℝ × (ℝ × ℝ))) (F : ℝ → ℝ)
    (hm : ∀ m ∈ S, m.2.1 ≠ 0)
    (hi : Integrable (fun u => (∑ m ∈ S, F (-(m.2.2*u+m.1)/m.2.1))^2))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (fun v => (∑ m ∈ S, F ((-(m.1*v+m.2.2)/m.2.1)/v))^2) (Icc a b) ∧
    (∫ v in Icc a b, (∑ m ∈ S, F ((-(m.1*v+m.2.2)/m.2.1)/v))^2) ≤
      b^2*(∫ u, (∑ m ∈ S, F (-(m.2.2*u+m.1)/m.2.1))^2) := by
  obtain ⟨hint,hbound⟩ := inverse_ratio_integral hi (fun u => sq_nonneg _) ha hab
  have heq : ∀ᵐ v ∂volume.restrict (Icc a b),
      (∑ m ∈ S, F (-(m.2.2*(1/v)+m.1)/m.2.1))^2 =
      (∑ m ∈ S, F ((-(m.1*v+m.2.2)/m.2.1)/v))^2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    congr 1
    apply Finset.sum_congr rfl
    intro m hmS
    rw [cubic_affine_inversion (hm m hmS) (ne_of_gt (ha.trans_le hv.1))]
  exact ⟨hint.congr heq,(integral_congr_ae heq).symm.le.trans hbound⟩

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.inverse_ratio_integral

#print axioms GuthMaynard.Improvement.inverse_ratio_affine_square
