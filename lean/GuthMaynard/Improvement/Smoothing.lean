module
public import GuthMaynard.Improvement.MeasureGate

@[expose] public section

/-! Mass-preserving positive smoothing and its L2 contraction. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Convolution

namespace GuthMaynard.Improvement

def smooth (κ g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y, κ (x - y) * g y

theorem smooth_eq_convolution (κ g : ℝ → ℝ) :
    smooth κ g = g ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] κ := by
  funext x
  simp only [smooth, convolution_mul, mul_comm]

theorem smooth_integrable {κ g : ℝ → ℝ} (hκ : Integrable κ) (hg : Integrable g) :
    Integrable (smooth κ g) := by
  rw [smooth_eq_convolution]
  exact hg.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hκ

theorem smooth_mass {κ g : ℝ → ℝ} (hκ : Integrable κ) (hg : Integrable g)
    (hmass : ∫ x, κ x = 1) : (∫ x, smooth κ g x) = ∫ x, g x := by
  rw [smooth_eq_convolution, integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hg hκ]
  simp [hmass]

theorem smooth_nonneg {κ g : ℝ → ℝ} (hκ : ∀ x, 0 ≤ κ x) (hg : ∀ x, 0 ≤ g x)
    (x : ℝ) : 0 ≤ smooth κ g x := integral_nonneg (fun y => mul_nonneg (hκ _) (hg y))

/-- Jensen/Cauchy–Schwarz for the actual positive mass-one convolution.
Both product integrals are proved to exist from the bounded kernel and
the L1 and L2 hypotheses on g. -/
theorem smooth_square_le {κ g : ℝ → ℝ} {B : ℝ}
    (hκm : Measurable κ) (hκi : Integrable κ) (hκ0 : ∀ x, 0 ≤ κ x)
    (hκB : ∀ x, ‖κ x‖ ≤ B) (hmass : ∫ x, κ x = 1)
    (hgm : Measurable g) (hg2 : Integrable (fun x => g x ^ 2))
    (hg0 : ∀ x, 0 ≤ g x) (x : ℝ) :
    smooth κ g x ^ 2 ≤ smooth κ (fun y => g y ^ 2) x := by
  have hkxm : Measurable (fun y : ℝ => κ (x - y)) :=
    hκm.comp (measurable_const.sub measurable_id)
  have hkxi : Integrable (fun y : ℝ => κ (x - y)) := hκi.comp_sub_left x
  have hprod2 : Integrable (fun y => κ (x - y) * g y ^ 2) :=
    hg2.bdd_mul hkxm.aestronglyMeasurable (Eventually.of_forall (fun y => hκB (x-y)))
  have hs1 : MemLp (fun y => Real.sqrt (κ (x - y))) 2 volume := by
    apply (memLp_two_iff_integrable_sq hkxm.sqrt.aestronglyMeasurable).2
    simpa only [Real.sq_sqrt (hκ0 _)] using hkxi
  have hs2 : MemLp (fun y => Real.sqrt (κ (x - y)) * g y) 2 volume := by
    apply (memLp_two_iff_integrable_sq (hkxm.sqrt.mul hgm).aestronglyMeasurable).2
    simpa only [Pi.mul_apply, mul_pow, Real.sq_sqrt (hκ0 _)] using hprod2
  have hcs := integral_cauchy_schwarz_nonneg hs1 hs2
    (fun y => Real.sqrt_nonneg _) (fun y => mul_nonneg (Real.sqrt_nonneg _) (hg0 y))
  have hmul : (fun y => Real.sqrt (κ (x - y)) * (Real.sqrt (κ (x - y)) * g y)) =
      (fun y => κ (x - y) * g y) := by
    funext y
    rw [← mul_assoc, Real.mul_self_sqrt (hκ0 _)]
  have htotal : (∫ y, κ (x - y)) = 1 := by
    rw [integral_sub_left_eq_self, hmass]
  simp only [hmul, mul_pow, Real.sq_sqrt (hκ0 _), htotal, Real.sqrt_one, one_mul] at hcs
  change smooth κ g x ≤ Real.sqrt (smooth κ (fun y => g y ^ 2) x) at hcs
  have h0 := smooth_nonneg hκ0 hg0 x
  have h02 := smooth_nonneg hκ0 (fun y => sq_nonneg (g y)) x
  have hsq := Real.sq_sqrt h02
  nlinarith [Real.sqrt_nonneg (smooth κ (fun y => g y ^ 2) x)]

theorem smooth_square_integrable {κ g : ℝ → ℝ} {B : ℝ}
    (hκm : Measurable κ) (hκi : Integrable κ) (hκ0 : ∀ x, 0 ≤ κ x)
    (hκB : ∀ x, ‖κ x‖ ≤ B) (hmass : ∫ x, κ x = 1)
    (hgm : Measurable g) (hgi : Integrable g) (hg2 : Integrable (fun x => g x ^ 2))
    (hg0 : ∀ x, 0 ≤ g x) : Integrable (fun x => smooth κ g x ^ 2) := by
  apply (smooth_integrable hκi hg2).mono'
    ((smooth_integrable hκi hgi).aestronglyMeasurable.pow 2)
  exact Eventually.of_forall (fun x => by
    simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (smooth κ g x))] using
      smooth_square_le hκm hκi hκ0 hκB hmass hgm hg2 hg0 x)

/-- L2 squared contraction with constant exactly one. The constant is uniform
in all kernel scales and measurable masks satisfying the stated hypotheses. -/
theorem smooth_l2_contraction {κ g : ℝ → ℝ} {B : ℝ}
    (hκm : Measurable κ) (hκi : Integrable κ) (hκ0 : ∀ x, 0 ≤ κ x)
    (hκB : ∀ x, ‖κ x‖ ≤ B) (hmass : ∫ x, κ x = 1)
    (hgm : Measurable g) (hgi : Integrable g) (hg2 : Integrable (fun x => g x ^ 2))
    (hg0 : ∀ x, 0 ≤ g x) : (∫ x, smooth κ g x ^ 2) ≤ ∫ x, g x ^ 2 := by
  calc
    (∫ x, smooth κ g x ^ 2) ≤ ∫ x, smooth κ (fun y => g y ^ 2) x :=
      integral_mono (smooth_square_integrable hκm hκi hκ0 hκB hmass hgm hgi hg2 hg0)
        (smooth_integrable hκi hg2)
        (smooth_square_le hκm hκi hκ0 hκB hmass hgm hg2 hg0)
    _ = ∫ x, g x ^ 2 := smooth_mass hκi hg2 hmass

end GuthMaynard.Improvement

#print axioms GuthMaynard.Improvement.smooth_eq_convolution
#print axioms GuthMaynard.Improvement.smooth_integrable
#print axioms GuthMaynard.Improvement.smooth_mass
#print axioms GuthMaynard.Improvement.smooth_nonneg
#print axioms GuthMaynard.Improvement.smooth_square_le
#print axioms GuthMaynard.Improvement.smooth_square_integrable
#print axioms GuthMaynard.Improvement.smooth_l2_contraction
