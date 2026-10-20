module
public import GuthMaynard.Improvement.CubicMaskedStrip
public import GuthMaynard.Improvement.CubicStripIntegral
public import GuthMaynard.Improvement.RatioFourierInput

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped FourierTransform
namespace GuthMaynard.Improvement

theorem ratio_box_input_coordinates {a b v y : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hb1 : 1 ≤ b)
    (hv : v ∈ Icc a b) (hy : y ∈ Icc a b) :
    v ∈ Icc (a/b) (b/a) ∧ y ∈ Icc (a/b) (b/a) ∧ y/v ∈ Icc (a/b) (b/a) := by
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hvp : 0 < v := ha.trans_le hv.1
  have hyp : 0 < y := ha.trans_le hy.1
  have hcover : ∀ z ∈ Icc a b, z ∈ Icc (a/b) (b/a) := by
    intro z hz
    constructor
    · exact (div_le_self ha.le hb1).trans hz.1
    · exact hz.2.trans ((le_div_iff₀ ha).mpr (by nlinarith))
  refine ⟨hcover v hv,hcover y hy,?_,?_⟩
  · apply (div_le_div_iff₀ hb hvp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hv.2 ha.le,mul_le_mul_of_nonneg_right hy.1 hb.le]
  · apply (div_le_div_iff₀ hvp ha).mpr
    nlinarith [mul_le_mul_of_nonneg_left hv.1 hb.le,mul_le_mul_of_nonneg_right hy.2 ha.le]

/-- Literal Fourier magnitude and independent masks, retaining A in the
first factor and enlarging only the two transverse masks to D. -/
theorem ratioFourier_mask_domination (μ : ℝ → ℝ) {a b v y : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hb1 : 1 ≤ b) (hv : v ∈ Icc a b) (hy : y ∈ Icc a b)
    (A B C D : Set ℝ) (hAsym : ∀ ξ, -ξ ∈ A ↔ ξ ∈ A)
    (hDsym : ∀ ξ, -ξ ∈ D ↔ ξ ∈ D) (hBD : B ⊆ D) (hCD : C ⊆ D) :
    ‖ratioFourierProduct μ (v,y)‖*‖ratioMaskProduct A B C (v,y)‖ ≤
      (mellinFrequency ⁻¹' A).indicator (ratioFourierInput μ (a/b) (b/a)) v *
      (mellinFrequency ⁻¹' D).indicator (ratioFourierInput μ (a/b) (b/a)) y *
      (mellinFrequency ⁻¹' D).indicator (ratioFourierInput μ (a/b) (b/a)) (y/v) := by
  have hvp : 0 < v := ha.trans_le hv.1
  have hyp : 0 < y := ha.trans_le hy.1
  obtain ⟨hvi,hyi,hyvi⟩ := ratio_box_input_coordinates ha ha1 hb1 hv hy
  have hfreq : mellinFrequency v-mellinFrequency y = -mellinFrequency (y/v) := by
    unfold mellinFrequency
    rw [Real.log_div hyp.ne' hvp.ne']
    ring
  have hn (E : Set ℝ) (z : ℝ) : 0 ≤ (mellinFrequency ⁻¹' E).indicator (ratioFourierInput μ (a/b) (b/a)) z :=
    indicator_nonneg (fun _ _ => ratioFourierInput_nonneg _ _ _ _) _
  by_cases hA : -mellinFrequency v ∈ A
  · by_cases hB : mellinFrequency v-mellinFrequency y ∈ B
    · by_cases hC : mellinFrequency y ∈ C
      · have hAv : mellinFrequency v ∈ A := (hAsym _).mp hA
        have hDy : mellinFrequency y ∈ D := hCD hC
        have hDyv : mellinFrequency (y/v) ∈ D := (hDsym _).mp (by rw [← hfreq]; exact hBD hB)
        simp only [ratioMaskProduct,Set.indicator_of_mem hA,Set.indicator_of_mem hB,Set.indicator_of_mem hC,
          norm_one,mul_one,Set.indicator_of_mem (show v ∈ mellinFrequency ⁻¹' A from hAv),
          Set.indicator_of_mem (show y ∈ mellinFrequency ⁻¹' D from hDy),
          Set.indicator_of_mem (show y/v ∈ mellinFrequency ⁻¹' D from hDyv)]
        rw [ratioFourierProduct_norm μ hvp hyp,ratioFourierInput_on hvi,ratioFourierInput_on hyi,ratioFourierInput_on hyvi]
        exact le_of_eq (by ring)
      · simp only [ratioMaskProduct,Set.indicator_of_notMem hC,mul_zero,norm_zero,mul_zero]
        exact mul_nonneg (mul_nonneg (hn A v) (hn D y)) (hn D (y/v))
    · simp only [ratioMaskProduct,Set.indicator_of_notMem hB,mul_zero,zero_mul,norm_zero,mul_zero]
      exact mul_nonneg (mul_nonneg (hn A v) (hn D y)) (hn D (y/v))
  · simp only [ratioMaskProduct,Set.indicator_of_notMem hA,zero_mul,norm_zero,mul_zero]
    exact mul_nonneg (mul_nonneg (hn A v) (hn D y)) (hn D (y/v))

/-- Uniform scalar control of the genuine strip integral, used solely to
justify integration in the positive compact ratio variable. -/
theorem cubicStripMass_le_square {r : ℝ → ℝ} (hr : Measurable r)
    (hr2 : Integrable (fun x => r x^2)) (hr0 : ∀ x, 0 ≤ r x)
    (L H : ℝ) (m : ℤ × (ℤ × ℤ)) {v : ℝ} (hv : 0 < v) :
    cubicStripMass r L H m v ≤ Real.sqrt v*(∫ y, r y^2) := by
  have hp := (memLp_two_iff_integrable_sq hr.aestronglyMeasurable).mpr hr2
  have hpv := (memLp_two_iff_integrable_sq (hr.comp (measurable_id.div_const v)).aestronglyMeasurable).mpr (hr2.comp_div hv.ne')
  have hint := hp.integrable_mul hpv
  have hcs := integral_cauchy_schwarz_nonneg hp hpv hr0 (fun _ => hr0 _)
  have hmass : 0 ≤ ∫ y, r y^2 := integral_nonneg (fun _ => sq_nonneg _)
  have hchange : (∫ y, r (y/v)^2) = v*(∫ y, r y^2) := by
    simpa only [abs_of_pos hv,smul_eq_mul] using Measure.integral_comp_div (fun y => r y^2) v
  dsimp only [Function.comp_apply,id_eq] at hcs
  rw [hchange,Real.sqrt_mul hv.le] at hcs
  have heq : Real.sqrt (∫ y, r y^2)*(Real.sqrt v*Real.sqrt (∫ y, r y^2)) = Real.sqrt v*(∫ y, r y^2) := by
    calc
      _ = Real.sqrt v * (Real.sqrt (∫ y, r y^2))^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hmass]
  rw [heq] at hcs
  exact (setIntegral_le_integral hint (Filter.Eventually.of_forall (fun y => mul_nonneg (hr0 y) (hr0 _)))).trans hcs

/-- Actual near-strip Fourier mass is bounded by the actual transverse
strip integral, with all existence facts derived from the ordinary density. -/
theorem fourier_near_strip_integral {μ : ℝ → ℝ} (hm : Measurable μ)
    (h0 : ∀ t, 0 ≤ μ t) (h1 : Integrable μ) (h2 : Integrable (fun t => μ t^2))
    {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hb1 : 1 ≤ b)
    {A B C D : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hAsym : ∀ ξ, -ξ ∈ A ↔ ξ ∈ A) (hDsym : ∀ ξ, -ξ ∈ D ↔ ξ ∈ D)
    (hBD : B ⊆ D) (hCD : C ⊆ D) (L H : ℝ) (m : ℤ × (ℤ × ℤ)) :
    let r₀ := ratioFourierInput μ (a/b) (b/a)
    let r := (mellinFrequency ⁻¹' D).indicator r₀
    let first := (mellinFrequency ⁻¹' A).indicator r₀
    IntegrableOn (maskedRadialNearMass μ A B C L H m) (Icc a b ×ˢ Icc a b) ∧
    IntegrableOn (fun v => first v*cubicStripMass r L H m v) (Icc a b) ∧
    (∫ p in Icc a b ×ˢ Icc a b, maskedRadialNearMass μ A B C L H m p) ≤
      ∫ v in Icc a b, first v*cubicStripMass r L H m v := by
  let r₀ := ratioFourierInput μ (a/b) (b/a)
  let r := (mellinFrequency ⁻¹' D).indicator r₀
  let first := (mellinFrequency ⁻¹' A).indicator r₀
  dsimp only
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hab : a ≤ b := ha1.trans hb1
  have hc : 0 < a/b := div_pos ha hb
  have hcd : a/b ≤ b/a := by apply (div_le_div_iff₀ hb ha).mpr; nlinarith
  have hfreq : Measurable mellinFrequency := by unfold mellinFrequency; fun_prop
  have hAP : MeasurableSet (mellinFrequency ⁻¹' A) := hA.preimage hfreq
  have hDP : MeasurableSet (mellinFrequency ⁻¹' D) := hD.preimage hfreq
  have hr₀ : Measurable r₀ := ratioFourierInput_measurable h1 _ _
  have hr : Measurable r := hr₀.indicator hDP
  have hfirst : Measurable first := hr₀.indicator hAP
  have hr₀2 : Integrable (fun v => r₀ v^2) := ratioFourierInput_square_integrable hc hcd h1 h2
  have hr2 : Integrable (fun v => r v^2) := by
    have heq : (fun v => r v^2) = (mellinFrequency ⁻¹' D).indicator (fun v => r₀ v^2) := by
      funext v; by_cases hv : v ∈ mellinFrequency ⁻¹' D <;> simp [r,hv]
    rw [heq]; exact hr₀2.indicator hDP
  have hr0 : ∀ v, 0 ≤ r v := fun _ => indicator_nonneg (fun _ _ => ratioFourierInput_nonneg _ _ _ _) _
  have hf0 : ∀ v, 0 ≤ first v := fun _ => indicator_nonneg (fun _ _ => ratioFourierInput_nonneg _ _ _ _) _
  have hmass : 0 ≤ ∫ t, μ t := integral_nonneg h0
  have hfirstbound : ∀ v, first v ≤ ∫ t, μ t := by
    intro v; by_cases hv : v ∈ mellinFrequency ⁻¹' A
    · rw [show first v = r₀ v from indicator_of_mem hv _]; exact ratioFourierInput_le_mass h0 _ _ _
    · rw [show first v = 0 from indicator_of_notMem hv _]; exact hmass
  have hnearMeas : Measurable (maskedRadialNearMass μ A B C L H m) := by
    apply Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
      ((ratioFourierProduct_measurable h1).norm.mul (ratioMaskProduct_measurable hA hB hC).norm) measurable_const
  have hnear0 : ∀ p, 0 ≤ maskedRadialNearMass μ A B C L H m p := by
    intro p; unfold maskedRadialNearMass; split_ifs <;> positivity
  have hnearB : ∀ p, ‖maskedRadialNearMass μ A B C L H m p‖ ≤ (∫ t, μ t)^3 := by
    intro p
    rw [Real.norm_eq_abs,abs_of_nonneg (hnear0 p)]
    unfold maskedRadialNearMass
    split_ifs
    · exact (mul_le_of_le_one_right (norm_nonneg _) (ratioMaskProduct_norm_le_one A B C p)).trans (ratioFourierProduct_bound hm h0 h1 p)
    · positivity
  have hnearI : IntegrableOn (maskedRadialNearMass μ A B C L H m) (Icc a b ×ˢ Icc a b) :=
    (integrableOn_const (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne (C := (∫ t, μ t)^3)).mono'
      hnearMeas.aestronglyMeasurable (Filter.Eventually.of_forall hnearB)
  have hstrip0 : ∀ v, 0 ≤ cubicStripMass r L H m v := fun v => integral_nonneg (fun y => mul_nonneg (hr0 y) (hr0 _))
  have hrightI : IntegrableOn (fun v => first v*cubicStripMass r L H m v) (Icc a b) := by
    apply (integrableOn_const isCompact_Icc.measure_lt_top.ne
      (C := (∫ t, μ t)*Real.sqrt b*(∫ y, r y^2))).mono'
      (hfirst.mul (cubicStripMass_measurable hr L H m)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    dsimp only [Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hf0 v) (hstrip0 v))]
    calc
      _ ≤ (∫ t, μ t)*(Real.sqrt v*(∫ y, r y^2)) := mul_le_mul (hfirstbound v)
        (cubicStripMass_le_square hr hr2 hr0 L H m (ha.trans_le hv.1)) (hstrip0 v) hmass
      _ = (∫ t, μ t)*Real.sqrt v*(∫ y, r y^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hv.2) hmass)
        (integral_nonneg (fun y => sq_nonneg (r y)))
  have hslice : ∀ v ∈ Icc a b,
      (∫ y in Icc a b, maskedRadialNearMass μ A B C L H m (v,y)) ≤ first v*cubicStripMass r L H m v := by
    intro v hv
    have hvp : 0 < v := ha.trans_le hv.1
    let Z := {y : ℝ | |L*((m.1:ℝ)*v+(m.2.1:ℝ)*y+(m.2.2:ℝ))| ≤ H}
    have hZ : MeasurableSet Z := by apply measurableSet_le <;> fun_prop
    have hp := (memLp_two_iff_integrable_sq hr.aestronglyMeasurable).mpr hr2
    have hpv := (memLp_two_iff_integrable_sq (hr.comp (measurable_id.div_const v)).aestronglyMeasurable).mpr (hr2.comp_div hvp.ne')
    have hprod := hp.integrable_mul hpv
    have hiUpper := (hprod.indicator hZ).const_mul (first v)
    have hiNear : IntegrableOn (fun y => maskedRadialNearMass μ A B C L H m (v,y)) (Icc a b) :=
      (integrableOn_const isCompact_Icc.measure_lt_top.ne (C := (∫ t, μ t)^3)).mono'
        (hnearMeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun y => hnearB (v,y)))
    calc
      _ ≤ ∫ y in Icc a b, first v*Z.indicator (fun y => r y*r (y/v)) y := by
        apply setIntegral_mono_on hiNear hiUpper.integrableOn measurableSet_Icc
        intro y hy
        by_cases hz : y ∈ Z
        · rw [indicator_of_mem hz]
          unfold maskedRadialNearMass
          change |L*((m.1:ℝ)*v+(m.2.1:ℝ)*y+(m.2.2:ℝ))| ≤ H at hz
          dsimp only
          rw [ite_eq_left hz]
          exact ratioFourier_mask_domination μ ha ha1 hb1 hv hy A B C D hAsym hDsym hBD hCD |>.trans_eq (by dsimp only [first, r, r₀, Pi.mul_apply, Function.comp_apply, id_eq]; ring)
        · rw [indicator_of_notMem hz]
          unfold maskedRadialNearMass
          change ¬ |L*((m.1:ℝ)*v+(m.2.1:ℝ)*y+(m.2.2:ℝ))| ≤ H at hz
          dsimp only
          rw [ite_eq_right hz]
          simp
      _ ≤ ∫ y, first v*Z.indicator (fun y => r y*r (y/v)) y :=
        setIntegral_le_integral hiUpper (Filter.Eventually.of_forall (fun y =>
          mul_nonneg (hf0 v) (indicator_nonneg (fun _ _ => mul_nonneg (hr0 _) (hr0 _)) _)))
      _ = _ := by rw [integral_const_mul,integral_indicator hZ]; rfl
  refine ⟨hnearI,hrightI,?_⟩
  have hprodI : Integrable (fun p => maskedRadialNearMass μ A B C L H m p)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))) := by
    simpa only [Measure.prod_restrict,Measure.volume_eq_prod,IntegrableOn] using hnearI
  rw [show volume.restrict (Icc a b ×ˢ Icc a b) =
    (volume.restrict (Icc a b)).prod (volume.restrict (Icc a b)) by rw [Measure.prod_restrict,Measure.volume_eq_prod]]
  rw [integral_prod _ hprodI]
  apply integral_mono_ae hprodI.integral_prod_left hrightI
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  exact hslice v hv

/-- Finite actual near-mode mass transfers to the outer first-mask strip
sum. No shell, sign, nonzero-mode, or width restriction is needed here. -/
theorem fourier_near_strip_sum {μ : ℝ → ℝ} (hm : Measurable μ)
    (h0 : ∀ t, 0 ≤ μ t) (h1 : Integrable μ) (h2 : Integrable (fun t => μ t^2))
    {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hb1 : 1 ≤ b)
    {A B C D : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hAsym : ∀ ξ, -ξ ∈ A ↔ ξ ∈ A) (hDsym : ∀ ξ, -ξ ∈ D ↔ ξ ∈ D)
    (hBD : B ⊆ D) (hCD : C ⊆ D) (L H : ℝ) (S : Finset (ℤ × (ℤ × ℤ))) :
    let r₀ := ratioFourierInput μ (a/b) (b/a)
    let r := (mellinFrequency ⁻¹' D).indicator r₀
    let first := (mellinFrequency ⁻¹' A).indicator r₀
    IntegrableOn (fun v => first v * ∑ m ∈ S, cubicStripMass r L H m v) (Icc a b) ∧
    (∑ m ∈ S, ∫ p in Icc a b ×ˢ Icc a b, maskedRadialNearMass μ A B C L H m p) ≤
      ∫ v in Icc a b, first v * ∑ m ∈ S, cubicStripMass r L H m v := by
  let r₀ := ratioFourierInput μ (a/b) (b/a)
  let r := (mellinFrequency ⁻¹' D).indicator r₀
  let first := (mellinFrequency ⁻¹' A).indicator r₀
  have hmode := fun m => fourier_near_strip_integral hm h0 h1 h2 ha ha1 hb1
    hA hB hC hD hAsym hDsym hBD hCD L H m
  have hi : ∀ m ∈ S, IntegrableOn (fun v => first v*cubicStripMass r L H m v) (Icc a b) :=
    fun m _ => (hmode m).2.1
  constructor
  · simpa only [Finset.mul_sum, first, r, r₀, IntegrableOn] using integrable_finsetSum S hi
  · calc
      _ ≤ ∑ m ∈ S, ∫ v in Icc a b, first v*cubicStripMass r L H m v :=
        Finset.sum_le_sum (fun m _ => (hmode m).2.2)
      _ = _ := by rw [← integral_finsetSum S hi]; simp only [Finset.mul_sum, first, r, r₀]

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.ratio_box_input_coordinates
#print axioms GuthMaynard.Improvement.ratioFourier_mask_domination
#print axioms GuthMaynard.Improvement.cubicStripMass_le_square
#print axioms GuthMaynard.Improvement.fourier_near_strip_integral

#print axioms GuthMaynard.Improvement.fourier_near_strip_sum
