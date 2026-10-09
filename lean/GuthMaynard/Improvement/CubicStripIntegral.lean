module
public import GuthMaynard.Improvement.CompactTransverse
public import GuthMaynard.Improvement.CubicStripGeometry

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

def stripCenter (m : ℤ × (ℤ × ℤ)) (v : ℝ) : ℝ :=
  -((m.1:ℝ)*v+(m.2.2:ℝ))/(m.2.1:ℝ)
def cubicStripMass (r : ℝ → ℝ) (L H : ℝ) (m : ℤ × (ℤ × ℤ)) (v : ℝ) : ℝ :=
  ∫ y in {y | |L*((m.1:ℝ)*v+(m.2.1:ℝ)*y+(m.2.2:ℝ))| ≤ H}, r y*r (y/v)
def smoothedStripPair (r : ℝ → ℝ) (a δ : ℝ) (m : ℤ × (ℤ × ℤ)) (v : ℝ) : ℝ :=
  Real.sqrt (squareSmoothing (scaledKernel compactKernel (max 1 (1/a)*δ)) r (stripCenter m v)) *
    Real.sqrt (squareSmoothing (scaledKernel compactKernel (max 1 (1/a)*δ)) r (stripCenter m v/v))

theorem cubicStripMass_measurable {r : ℝ → ℝ} (hr : Measurable r)
    (L H : ℝ) (m : ℤ × (ℤ × ℤ)) : Measurable (cubicStripMass r L H m) := by
  have hs : MeasurableSet {p : ℝ × ℝ | |L*((m.1:ℝ)*p.1+(m.2.1:ℝ)*p.2+(m.2.2:ℝ))| ≤ H} := by
    apply measurableSet_le <;> fun_prop
  have hmeas : Measurable (fun p : ℝ × ℝ =>
      ({p : ℝ × ℝ | |L*((m.1:ℝ)*p.1+(m.2.1:ℝ)*p.2+(m.2.2:ℝ))| ≤ H}).indicator
        (fun p => r p.2*r (p.2/p.1)) p) := by
    apply Measurable.indicator _ hs
    fun_prop
  have hi := (hmeas.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  convert hi using 1
  funext v
  rw [cubicStripMass,← integral_indicator (show MeasurableSet {y : ℝ | |L*((m.1:ℝ)*v+(m.2.1:ℝ)*y+(m.2.2:ℝ))| ≤ H} by apply measurableSet_le <;> fun_prop)]
  rfl

theorem squareSmoothing_bounded_measurable {κ r : ℝ → ℝ} {B : ℝ}
    (hκ : Measurable κ) (hκ0 : ∀ x, 0 ≤ κ x) (_hB : 0 ≤ B)
    (hb : ∀ x, ‖κ x‖ ≤ B) (hr : Measurable r) (hr2 : Integrable (fun x => r x^2)) :
    Measurable (squareSmoothing κ r) ∧ ∀ z, 0 ≤ squareSmoothing κ r z ∧
      squareSmoothing κ r z ≤ B*(∫ x, r x^2) := by
  constructor
  · have h : Measurable (fun p : ℝ × ℝ => κ (p.1-p.2)*r p.2^2) := by fun_prop
    exact h.stronglyMeasurable.integral_prod_right'.measurable
  · intro z
    refine ⟨squareSmoothing_nonneg hκ0 z,?_⟩
    calc
      _ ≤ ∫ y, B*r y^2 := integral_mono (squareSmoothing_integrable hκ hb hr2 z)
        (hr2.const_mul B) (fun y => mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hb _)) (sq_nonneg _))
      _ = _ := integral_const_mul _ _

theorem smoothedStripPair_bounded_measurable {r : ℝ → ℝ} (hr : Measurable r)
    (hr2 : Integrable (fun x => r x^2)) (a : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ m : ℤ × (ℤ × ℤ), Measurable (smoothedStripPair r a δ m) ∧
      ∀ v, 0 ≤ smoothedStripPair r a δ m v ∧ smoothedStripPair r a δ m v ≤ W := by
  have hq : 0 < max 1 (1/a) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hw : 0 < max 1 (1/a)*δ := mul_pos hq hδ
  obtain ⟨B,hB,hb⟩ := compactKernel_bound
  obtain ⟨hFm,hFb⟩ := squareSmoothing_bounded_measurable
    (scaledKernel_measurable compactKernel_smooth.continuous.measurable _)
    (scaledKernel_nonneg compactKernel_nonneg hw) (by positivity)
    (scaledKernel_bound hw hb) hr hr2
  let W := (max 1 (1/a)*δ)⁻¹*B*(∫ x, r x^2)
  have hW : 0 ≤ W := mul_nonneg (by positivity) (integral_nonneg (fun _ => sq_nonneg _))
  refine ⟨W,hW,?_⟩
  intro m
  constructor
  · unfold smoothedStripPair stripCenter
    fun_prop
  · intro v
    refine ⟨mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),?_⟩
    unfold smoothedStripPair
    calc
      _ ≤ Real.sqrt W*Real.sqrt W := mul_le_mul
        (Real.sqrt_le_sqrt (hFb _).2) (Real.sqrt_le_sqrt (hFb _).2)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt hW

/-- Pointwise transverse bound on the literal strip. The fixed constant
precedes every density, scale, mode and positive ratio. -/
theorem cubic_strip_transverse (a b : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L H K v : ℝ) (m : ℤ × (ℤ × ℤ)) (r : ℝ → ℝ),
      0 < L → 0 < H → 0 < K → K ≤ (m.2.1:ℝ) → a ≤ v → v ≤ b →
      Measurable r → Integrable (fun y => r y^2) → (∀ y, 0 ≤ r y) →
      IntegrableOn (fun y => r y*r (y/v))
        {y | |L*((m.1:ℝ)*v+(m.2.1:ℝ)*y+(m.2.2:ℝ))| ≤ H} ∧
      cubicStripMass r L H m v ≤ C*(H/(L*K))*Real.sqrt b*
        smoothedStripPair r a (H/(L*K)) m v := by
  obtain ⟨C,hC,h⟩ := compact_masked_transverse a b ha
  refine ⟨C,hC,?_⟩
  intro L H K v m r hL hH hK hKm hav hvb hr hr2 hr0
  have hv : 0 < v := ha.trans_le hav
  have hm : 0 < (m.2.1:ℝ) := hK.trans_le hKm
  have hδ : 0 < H/(L*K) := div_pos hH (mul_pos hL hK)
  have hp := (memLp_two_iff_integrable_sq hr.aestronglyMeasurable).mpr hr2
  have hpv := (memLp_two_iff_integrable_sq (hr.comp (measurable_id.div_const v)).aestronglyMeasurable).mpr
    (hr2.comp_div hv.ne')
  have hint := hp.integrable_mul hpv
  refine ⟨hint.integrableOn,?_⟩
  have hsub : {y : ℝ | |L*((m.1:ℝ)*v+(m.2.1:ℝ)*y+(m.2.2:ℝ))| ≤ H} ⊆
      {y | |y-stripCenter m v| ≤ H/(L*K)} := by
    intro y hy
    have hlin : |(m.1:ℝ)*v+(m.2.1:ℝ)*y+(m.2.2:ℝ)| ≤ H/L := by
      apply (le_div_iff₀ hL).mpr
      simpa only [Set.mem_ofPred_eq,abs_mul,abs_of_pos hL,mul_comm] using hy
    have hh := (cubic_strip_window hm.ne').mp hlin
    change |y-stripCenter m v| ≤ _
    apply hh.trans
    rw [abs_of_pos hm]
    calc
      _ ≤ (H/L)/K := div_le_div_of_nonneg_left (div_nonneg hH.le hL.le) hK hKm
      _ = _ := by field_simp
  have hwindow := h (H/(L*K)) v (stripCenter m v) univ r hδ hav hvb MeasurableSet.univ hr hr2 hr0
  simp only [indicator_univ] at hwindow
  rw [Real.sqrt_mul (squareSmoothing_nonneg (scaledKernel_nonneg compactKernel_nonneg
    (mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hδ)) _)] at hwindow
  exact (setIntegral_mono_set hint.integrableOn (Filter.Eventually.of_forall (fun y => mul_nonneg (hr0 y) (hr0 _)))
    (Filter.Eventually.of_forall hsub)).trans hwindow

/-- The actual finite strip integral exists and satisfies its smoothed box
majorant. The designated first mask is retained literally on both sides. -/
theorem cubic_strip_integral (a b : ℝ) (ha : 0 < a) (_hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L H K : ℝ) (S : Finset (ℤ × (ℤ × ℤ)))
      (A₀ : Set ℝ) (r₀ r : ℝ → ℝ),
      0 < L → 0 < H → 0 < K → (∀ m ∈ S, K ≤ (m.2.1:ℝ)) →
      MeasurableSet A₀ → Measurable r₀ → MemLp r₀ 2 → (∀ v, 0 ≤ r₀ v) →
      Measurable r → Integrable (fun y => r y^2) → (∀ y, 0 ≤ r y) →
      IntegrableOn (fun v => A₀.indicator r₀ v * ∑ m ∈ S, cubicStripMass r L H m v) (Icc a b) ∧
      IntegrableOn (fun v => A₀.indicator r₀ v * ∑ m ∈ S, smoothedStripPair r a (H/(L*K)) m v) (Icc a b) ∧
      (∫ v in Icc a b, A₀.indicator r₀ v * ∑ m ∈ S, cubicStripMass r L H m v) ≤
        C*(H/(L*K))*Real.sqrt b *
          (∫ v in Icc a b, A₀.indicator r₀ v * ∑ m ∈ S, smoothedStripPair r a (H/(L*K)) m v) := by
  obtain ⟨C,hC,h⟩ := cubic_strip_transverse a b ha
  refine ⟨C,hC,?_⟩
  intro L H K S A₀ r₀ r hL hH hK hKm hA₀ hr₀ hmem₀ hr₀0 hr hr2 hr0
  have hδ : 0 < H/(L*K) := div_pos hH (mul_pos hL hK)
  have hρ : IntegrableOn (A₀.indicator r₀) (Icc a b) :=
    MemLp.integrable (by norm_num) ((hmem₀.indicator hA₀).restrict _)
  have hρ0 : ∀ v, 0 ≤ A₀.indicator r₀ v := by
    intro v; by_cases hv : v ∈ A₀ <;> simp [hv,hr₀0]
  obtain ⟨W,hW,hpair⟩ := smoothedStripPair_bounded_measurable hr hr2 a hδ
  have hright : IntegrableOn (fun v => A₀.indicator r₀ v * ∑ m ∈ S, smoothedStripPair r a (H/(L*K)) m v) (Icc a b) := by
    have hm : Measurable (fun v => ∑ m ∈ S, smoothedStripPair r a (H/(L*K)) m v) :=
      Finset.measurable_sum S (fun m _ => (hpair m).1)
    have hh := hρ.bdd_mul hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun v => show
      ‖∑ m ∈ S, smoothedStripPair r a (H/(L*K)) m v‖ ≤ S.card*W from by
        rw [Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun m _ => (hpair m).2 v |>.1))]
        exact (Finset.sum_le_sum (fun m _ => (hpair m).2 v |>.2)).trans_eq (by simp)))
    simpa only [mul_comm,IntegrableOn] using hh
  have hpoint : ∀ v ∈ Icc a b,
      A₀.indicator r₀ v * ∑ m ∈ S, cubicStripMass r L H m v ≤
        (C*(H/(L*K))*Real.sqrt b)*(A₀.indicator r₀ v * ∑ m ∈ S, smoothedStripPair r a (H/(L*K)) m v) := by
    intro v hv
    have hh := Finset.sum_le_sum (fun m hmS => (h L H K v m r hL hH hK (hKm m hmS) hv.1 hv.2 hr hr2 hr0).2)
    have hh' := mul_le_mul_of_nonneg_left hh (hρ0 v)
    simpa only [← Finset.mul_sum,mul_left_comm] using hh'
  have hleftm : Measurable (fun v => A₀.indicator r₀ v * ∑ m ∈ S, cubicStripMass r L H m v) :=
    (hr₀.indicator hA₀).mul (Finset.measurable_sum S (fun m _ => cubicStripMass_measurable hr L H m))
  have hleft0 : ∀ v, 0 ≤ A₀.indicator r₀ v * ∑ m ∈ S, cubicStripMass r L H m v := by
    intro v
    apply mul_nonneg (hρ0 v) (Finset.sum_nonneg _)
    intro m _
    exact integral_nonneg (fun y => mul_nonneg (hr0 y) (hr0 _))
  have hleft : IntegrableOn (fun v => A₀.indicator r₀ v * ∑ m ∈ S, cubicStripMass r L H m v) (Icc a b) :=
    (hright.const_mul (C*(H/(L*K))*Real.sqrt b)).mono' hleftm.aestronglyMeasurable (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
      rw [Real.norm_eq_abs,abs_of_nonneg (hleft0 v)]
      exact hpoint v hv)
  refine ⟨hleft,hright,?_⟩
  calc
    _ ≤ ∫ v in Icc a b, (C*(H/(L*K))*Real.sqrt b)*(A₀.indicator r₀ v * ∑ m ∈ S, smoothedStripPair r a (H/(L*K)) m v) :=
      integral_mono_ae hleft (hright.const_mul _) (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
        exact hpoint v hv)
    _ = _ := integral_const_mul _ _

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.cubicStripMass_measurable
#print axioms GuthMaynard.Improvement.squareSmoothing_bounded_measurable
#print axioms GuthMaynard.Improvement.smoothedStripPair_bounded_measurable
#print axioms GuthMaynard.Improvement.cubic_strip_transverse
#print axioms GuthMaynard.Improvement.cubic_strip_integral
