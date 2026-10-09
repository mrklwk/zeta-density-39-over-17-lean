import Mathlib

/-! Measure-theoretic parts of the candidate gate. No affine or trace estimate
is assumed in these inequalities. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace GuthMaynard.Improvement

theorem integral_cauchy_schwarz_nonneg {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    (∫ x, f x * g x ∂μ) ≤
      Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0)
    (by simpa using hf) (by simpa using hg)
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  simpa only [Real.rpow_two] using h

/-- The integral analogue of the two outer Cauchy–Schwarz steps.
The first factor r is unchanged, and the measure may itself be restricted. -/
theorem outer_integral_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {r X Y : α → ℝ}
    (hr : MemLp r 2 μ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hr0 : ∀ x, 0 ≤ r x) (hX0 : ∀ x, 0 ≤ X x) (hY0 : ∀ x, 0 ≤ Y x) :
    (∫ x, r x * (Real.sqrt (X x) * Real.sqrt (Y x)) ∂μ) ≤
      Real.sqrt (∫ x, r x ^ 2 ∂μ) *
        Real.sqrt (Real.sqrt (∫ x, X x ^ 2 ∂μ) *
          Real.sqrt (∫ x, Y x ^ 2 ∂μ)) := by
  have hm : AEStronglyMeasurable (fun x => Real.sqrt (X x) * Real.sqrt (Y x)) μ :=
    hX.aestronglyMeasurable.aemeasurable.sqrt.aestronglyMeasurable.mul
      hY.aestronglyMeasurable.aemeasurable.sqrt.aestronglyMeasurable
  have hid : (fun x => (Real.sqrt (X x) * Real.sqrt (Y x)) ^ 2) =
      (fun x => X x * Y x) := by
    funext x
    simp [mul_pow, Real.sq_sqrt (hX0 x), Real.sq_sqrt (hY0 x)]
  have hmem : MemLp (fun x => Real.sqrt (X x) * Real.sqrt (Y x)) 2 μ := by
    apply (memLp_two_iff_integrable_sq hm).2
    rw [hid]
    exact hX.integrable_mul hY
  have hfirst := integral_cauchy_schwarz_nonneg hr hmem hr0
    (fun x => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  change (∫ x, r x * (Real.sqrt (X x) * Real.sqrt (Y x)) ∂μ) ≤
    Real.sqrt (∫ x, r x ^ 2 ∂μ) *
      Real.sqrt (∫ x, (fun x => (Real.sqrt (X x) * Real.sqrt (Y x)) ^ 2) x ∂μ)
    at hfirst
  rw [hid] at hfirst
  exact hfirst.trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (integral_cauchy_schwarz_nonneg hX hY hX0 hY0))
    (Real.sqrt_nonneg _))

/-- The mask mass is the exact restricted integral, not an unrestricted norm. -/
theorem masked_outer_integral_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {r X Y : α → ℝ} {A : Set α} (hA : MeasurableSet A)
    (hr : MemLp r 2 μ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hr0 : ∀ x, 0 ≤ r x) (hX0 : ∀ x, 0 ≤ X x) (hY0 : ∀ x, 0 ≤ Y x) :
    (∫ x, A.indicator r x * (Real.sqrt (X x) * Real.sqrt (Y x)) ∂μ) ≤
      Real.sqrt (∫ x in A, r x ^ 2 ∂μ) *
        Real.sqrt (Real.sqrt (∫ x, X x ^ 2 ∂μ) *
          Real.sqrt (∫ x, Y x ^ 2 ∂μ)) := by
  have h := outer_integral_bound (hr.indicator hA) hX hY
    (fun x => by by_cases hx : x ∈ A <;> simp [hx, hr0]) hX0 hY0
  have hid : (fun x => (A.indicator r x) ^ 2) = A.indicator (fun x => r x ^ 2) := by
    funext x
    by_cases hx : x ∈ A <;> simp [hx]
  rw [hid, integral_indicator hA] at h
  exact h

def squareSmoothing (κ r : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ y, κ (z - y) * r y ^ 2

/-- A positive kernel lower bound controls local square mass. Integrability
is explicit; the integral cannot become a vacuous default zero. -/
theorem local_square_mass_le {r k : ℝ → ℝ} {s : Set ℝ} {D : ℝ}
    (hs : MeasurableSet s) (hr : Integrable (fun y => r y ^ 2))
    (hk : Integrable (fun y => k y * r y ^ 2))
    (hD : 0 ≤ D) (hk0 : ∀ y, 0 ≤ k y)
    (hlower : ∀ y ∈ s, 1 ≤ D * k y) :
    (∫ y in s, r y ^ 2) ≤ D * ∫ y, k y * r y ^ 2 := by
  calc
    (∫ y in s, r y ^ 2) ≤ ∫ y in s, D * (k y * r y ^ 2) := by
      apply setIntegral_mono_on hr.integrableOn (hk.const_mul D).integrableOn hs
      intro y hy
      have := mul_le_mul_of_nonneg_right (hlower y hy) (sq_nonneg (r y))
      nlinarith
    _ ≤ ∫ y, D * (k y * r y ^ 2) :=
      setIntegral_le_integral (hk.const_mul D)
        (Filter.Eventually.of_forall (fun y =>
          mul_nonneg hD (mul_nonneg (hk0 y) (sq_nonneg _))))
    _ = D * ∫ y, k y * r y ^ 2 := integral_const_mul _ _

theorem squareSmoothing_nonneg {κ r : ℝ → ℝ} (hκ : ∀ y, 0 ≤ κ y) (z : ℝ) :
    0 ≤ squareSmoothing κ r z :=
  integral_nonneg (fun _ => mul_nonneg (hκ _) (sq_nonneg _))

/-- Measurability and a uniform boundedness bound on κ suffice for existence
of every smoothing integral. Smoothness and mask-boundary regularity are not
needed by this theorem. -/
theorem squareSmoothing_integrable {κ r : ℝ → ℝ} {B : ℝ}
    (hκ : Measurable κ) (hb : ∀ y, ‖κ y‖ ≤ B)
    (hr : Integrable (fun y => r y ^ 2)) (z : ℝ) :
    Integrable (fun y => κ (z - y) * r y ^ 2) := by
  exact hr.bdd_mul (hκ.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y => hb (z - y)))

/-- A change of variables contributes exactly v in the second square mass.
The same measurable r is used in both factors; it may already contain a mask.
The two kernel lower bounds are local on s, not assumptions of the conclusion. -/
theorem transverse_of_kernel_bounds {κ r : ℝ → ℝ} {s : Set ℝ} {B D v z : ℝ}
    (hs : MeasurableSet s) (hκ : Measurable κ) (hb : ∀ y, ‖κ y‖ ≤ B)
    (hκ0 : ∀ y, 0 ≤ κ y) (hr : Measurable r)
    (hr2 : Integrable (fun y => r y ^ 2)) (hr0 : ∀ y, 0 ≤ r y)
    (hD : 0 ≤ D) (hv : 0 < v)
    (hlower : ∀ y ∈ s, 1 ≤ D * κ (z - y))
    (hlower' : ∀ y ∈ s, 1 ≤ D * κ (z / v - y / v)) :
    (∫ y in s, r y * r (y / v)) ≤
      D * Real.sqrt v * Real.sqrt (squareSmoothing κ r z * squareSmoothing κ r (z / v)) := by
  have hmem : MemLp r 2 volume :=
    (memLp_two_iff_integrable_sq hr.aestronglyMeasurable).2 hr2
  have hdiv2 : Integrable (fun y => r (y / v) ^ 2) := hr2.comp_div hv.ne'
  have hdivmem : MemLp (fun y => r (y / v)) 2 volume :=
    (memLp_two_iff_integrable_sq
      (hr.comp (measurable_id.div_const v)).aestronglyMeasurable).2 hdiv2
  have hkz := squareSmoothing_integrable hκ hb hr2 z
  have hkzv := squareSmoothing_integrable hκ hb hr2 (z / v)
  have hkdiv : Integrable (fun y => κ (z / v - y / v) * r (y / v) ^ 2) :=
    hkzv.comp_div hv.ne'
  have hchange : (∫ y, κ (z / v - y / v) * r (y / v) ^ 2) =
      v * squareSmoothing κ r (z / v) := by
    simpa only [abs_of_pos hv, smul_eq_mul, squareSmoothing] using
      Measure.integral_comp_div (fun y => κ (z / v - y) * r y ^ 2) v
  have h1 := local_square_mass_le hs hr2 hkz hD (fun y => hκ0 (z - y)) hlower
  have h2 := local_square_mass_le hs hdiv2 hkdiv hD
    (fun y => hκ0 (z / v - y / v)) hlower'
  rw [hchange] at h2
  have hcs := integral_cauchy_schwarz_nonneg (hmem.restrict s) (hdivmem.restrict s)
    hr0 (fun y => hr0 (y / v))
  have hmass1 := squareSmoothing_nonneg (r := r) hκ0 z
  calc
    (∫ y in s, r y * r (y / v)) ≤
        Real.sqrt (D * squareSmoothing κ r z) *
          Real.sqrt (D * (v * squareSmoothing κ r (z / v))) :=
      hcs.trans (mul_le_mul (Real.sqrt_le_sqrt h1) (Real.sqrt_le_sqrt h2)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = D * Real.sqrt v *
        Real.sqrt (squareSmoothing κ r z * squareSmoothing κ r (z / v)) := by
      rw [← Real.sqrt_mul (mul_nonneg hD hmass1)]
      rw [show D * squareSmoothing κ r z * (D * (v * squareSmoothing κ r (z / v))) =
        D ^ 2 * (v * (squareSmoothing κ r z * squareSmoothing κ r (z / v))) by ring]
      rw [Real.sqrt_mul (sq_nonneg D), Real.sqrt_sq hD, Real.sqrt_mul hv.le]
      ring

/-- Uniform transverse smoothing on v in [a,b]. The kernel can be any bounded
measurable nonnegative kernel with the displayed lower bound. In particular
this theorem imposes no regularity on the boundary of a mask included in r.
The constant C*sqrt(b) precedes r,z,v; the radius multiplier depends only on a. -/
theorem transverse_smoothing_uniform {κ r : ℝ → ℝ} {B C δ a b v z : ℝ}
    (hκ : Measurable κ) (hb : ∀ y, ‖κ y‖ ≤ B) (hκ0 : ∀ y, 0 ≤ κ y)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (ha : 0 < a) (hav : a ≤ v) (hvb : v ≤ b)
    (hlower : ∀ t, |t| ≤ max 1 (1 / a) * δ → 1 ≤ (C * δ) * κ t)
    (hr : Measurable r) (hr2 : Integrable (fun y => r y ^ 2))
    (hr0 : ∀ y, 0 ≤ r y) :
    (∫ y in {y | |y - z| ≤ δ}, r y * r (y / v)) ≤
      (C * δ) * Real.sqrt b *
        Real.sqrt (squareSmoothing κ r z * squareSmoothing κ r (z / v)) := by
  have hv : 0 < v := ha.trans_le hav
  have hs : MeasurableSet {y : ℝ | |y - z| ≤ δ} :=
    measurableSet_le (measurable_id.sub_const z).abs measurable_const
  have hfirst : ∀ y ∈ {y : ℝ | |y - z| ≤ δ}, 1 ≤ (C * δ) * κ (z - y) := by
    intro y hy
    apply hlower
    change |y - z| ≤ δ at hy
    have hdist : |z - y| ≤ δ := by rw [abs_sub_comm]; exact hy
    have hδbound : δ ≤ max 1 (1 / a) * δ := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) (1 / a)) hδ
    exact hdist.trans hδbound
  have hsecond : ∀ y ∈ {y : ℝ | |y - z| ≤ δ},
      1 ≤ (C * δ) * κ (z / v - y / v) := by
    intro y hy
    apply hlower
    change |y - z| ≤ δ at hy
    have hdist : |z - y| ≤ δ := by rw [abs_sub_comm]; exact hy
    calc
      |z / v - y / v| = |z - y| / v := by rw [← sub_div, abs_div, abs_of_pos hv]
      _ ≤ δ / v := div_le_div_of_nonneg_right hdist hv.le
      _ ≤ δ / a := div_le_div_of_nonneg_left hδ ha hav
      _ = (1 / a) * δ := by ring
      _ ≤ max 1 (1 / a) * δ := mul_le_mul_of_nonneg_right (le_max_right _ _) hδ
  have h := transverse_of_kernel_bounds hs hκ hb hκ0 hr hr2 hr0
    (mul_nonneg hC hδ) hv hfirst hsecond
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hvb) (mul_nonneg hC hδ))
    (Real.sqrt_nonneg _))

/-- Applying the transverse theorem to an arbitrary measurable mask needs
no assumptions about the geometry or regularity of its boundary. -/
theorem masked_transverse_smoothing {κ r : ℝ → ℝ} {A : Set ℝ}
    {B C δ a b v z : ℝ} (hA : MeasurableSet A)
    (hκ : Measurable κ) (hb : ∀ y, ‖κ y‖ ≤ B) (hκ0 : ∀ y, 0 ≤ κ y)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (ha : 0 < a) (hav : a ≤ v) (hvb : v ≤ b)
    (hlower : ∀ t, |t| ≤ max 1 (1 / a) * δ → 1 ≤ (C * δ) * κ t)
    (hr : Measurable r) (hr2 : Integrable (fun y => r y ^ 2))
    (hr0 : ∀ y, 0 ≤ r y) :
    (∫ y in {y | |y - z| ≤ δ}, A.indicator r y * A.indicator r (y / v)) ≤
      (C * δ) * Real.sqrt b * Real.sqrt
        (squareSmoothing κ (A.indicator r) z * squareSmoothing κ (A.indicator r) (z / v)) := by
  have hid : (fun y => (A.indicator r y) ^ 2) = A.indicator (fun y => r y ^ 2) := by
    funext y
    by_cases hy : y ∈ A <;> simp [hy]
  have hmasked : Integrable (fun y => (A.indicator r y) ^ 2) := by
    rw [hid]
    exact hr2.indicator hA
  exact transverse_smoothing_uniform hκ hb hκ0 hC hδ ha hav hvb hlower
    (hr.indicator hA) hmasked (fun y => by by_cases hy : y ∈ A <;> simp [hy, hr0])

end GuthMaynard.Improvement

#print axioms GuthMaynard.Improvement.integral_cauchy_schwarz_nonneg
#print axioms GuthMaynard.Improvement.outer_integral_bound
#print axioms GuthMaynard.Improvement.masked_outer_integral_bound
#print axioms GuthMaynard.Improvement.local_square_mass_le
#print axioms GuthMaynard.Improvement.squareSmoothing_nonneg
#print axioms GuthMaynard.Improvement.squareSmoothing_integrable
#print axioms GuthMaynard.Improvement.transverse_of_kernel_bounds
#print axioms GuthMaynard.Improvement.transverse_smoothing_uniform
#print axioms GuthMaynard.Improvement.masked_transverse_smoothing
