import GuthMaynard.Improvement.CubicMaskedRadial
import GuthMaynard.Improvement.CubicModeCount
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped FourierTransform ContDiff
namespace GuthMaynard.Improvement

def maskedRadialNearMass (μ : ℝ → ℝ) (A B C : Set ℝ) (L H : ℝ)
    (m : ℤ × (ℤ × ℤ)) (p : ℝ × ℝ) : ℝ :=
  if |L*((m.1:ℝ)*p.1+(m.2.1:ℝ)*p.2+(m.2.2:ℝ))| ≤ H
  then ‖ratioFourierProduct μ p‖*‖ratioMaskProduct A B C p‖ else 0

theorem masked_radial_discard_integral_bound {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {l u : ℝ} (hlu : l ≤ u) (hs : ∀ r, r ∉ Icc l u → a r = 0)
    (v₀ v₁ y₀ y₁ : ℝ) (hv : v₀ ≤ v₁) (hy : y₀ ≤ y₁) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L H : ℝ) (m : ℤ × (ℤ × ℤ)) (μ : ℝ → ℝ) (A B Cmask : Set ℝ),
      0 < H → MeasurableSet A → MeasurableSet B → MeasurableSet Cmask → Measurable μ → (∀ t, 0 ≤ μ t) → Integrable μ →
      IntegrableOn (fun p => radialDiscard a μ L H m p*ratioMaskProduct A B Cmask p) (Icc v₀ v₁ ×ˢ Icc y₀ y₁) ∧
      ‖∫ p in Icc v₀ v₁ ×ˢ Icc y₀ y₁, radialDiscard a μ L H m p*ratioMaskProduct A B Cmask p‖ ≤
        C/H^n*(∫ t, μ t)^3*((v₁-v₀)*(y₁-y₀)) := by
  obtain ⟨C,hC,hb⟩ := radial_uniform_power_decay ha hlu hs v₀ v₁ y₀ y₁ n
  refine ⟨C,hC,?_⟩
  intro L H m μ A B Cmask hH hA hB hCmask hm h0 hi
  have hmass : 0 ≤ ∫ t, μ t := integral_nonneg h0
  have hmeas : Measurable (radialDiscard a μ L H m) := by
    unfold radialDiscard
    apply Measurable.ite (measurableSet_lt measurable_const (by fun_prop))
      ((radialKernel_measurable ha.continuous.measurable L m).mul (ratioFourierProduct_measurable hi)) measurable_const
  have hpoint : ∀ p ∈ Icc v₀ v₁ ×ˢ Icc y₀ y₁,
      ‖radialDiscard a μ L H m p‖ ≤ C/H^n*(∫ t, μ t)^3 := by
    intro p hp
    unfold radialDiscard
    split_ifs with hx
    · have hh := hb p.1 hp.1 p.2 hp.2 (L*((m.1:ℝ)*p.1+(m.2.1:ℝ)*p.2+(m.2.2:ℝ)))
      have hpow := pow_le_pow_left₀ hH.le hx.le n
      have hr : ‖radialKernel a L m p‖ ≤ C/H^n := by
        rw [radialKernel,radial_integral_fourier]
        apply (le_div_iff₀ (pow_pos hH n)).mpr
        nlinarith [mul_le_mul_of_nonneg_right hpow (norm_nonneg (𝓕 (radialAmplitude a p.1 p.2) (L*((m.1:ℝ)*p.1+(m.2.1:ℝ)*p.2+(m.2.2:ℝ)))))]
      rw [norm_mul]
      exact mul_le_mul hr (ratioFourierProduct_bound hm h0 hi p) (norm_nonneg _) (by positivity)
    · simp only [norm_zero]
      positivity
  have hmasked : Measurable (fun p => radialDiscard a μ L H m p*ratioMaskProduct A B Cmask p) :=
    hmeas.mul (ratioMaskProduct_measurable hA hB hCmask)
  have hmaskedpoint : ∀ p ∈ Icc v₀ v₁ ×ˢ Icc y₀ y₁,
      ‖radialDiscard a μ L H m p*ratioMaskProduct A B Cmask p‖ ≤ C/H^n*(∫ t, μ t)^3 := by
    intro p hp
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (ratioMaskProduct_norm_le_one A B Cmask p)).trans (hpoint p hp)
  have hfinite : volume (Icc v₀ v₁ ×ˢ Icc y₀ y₁) < ⊤ := (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  have hInt : IntegrableOn (fun p => radialDiscard a μ L H m p*ratioMaskProduct A B Cmask p) (Icc v₀ v₁ ×ˢ Icc y₀ y₁) :=
    (integrableOn_const hfinite.ne).mono' hmasked.aestronglyMeasurable
      (ae_restrict_of_forall_mem (measurableSet_Icc.prod measurableSet_Icc) hmaskedpoint)
  refine ⟨hInt,?_⟩
  have hh := norm_setIntegral_le_of_norm_le_const hfinite hmaskedpoint
  have hvol : volume.real (Icc v₀ v₁ ×ˢ Icc y₀ y₁) = (v₁-v₀)*(y₁-y₀) := by
    rw [Measure.real,Measure.volume_eq_prod,Measure.prod_prod]
    rw [ENNReal.toReal_mul]
    change volume.real (Icc v₀ v₁)*volume.real (Icc y₀ y₁) = _
    rw [Real.volume_real_Icc_of_le hv,Real.volume_real_Icc_of_le hy]
  rw [hvol] at hh
  exact hh


def maskedRadialNear (a : ℝ → ℂ) (μ : ℝ → ℝ) (A B C : Set ℝ) (L H : ℝ)
    (m : ℤ × (ℤ × ℤ)) (p : ℝ × ℝ) : ℂ :=
  if |L*((m.1:ℝ)*p.1+(m.2.1:ℝ)*p.2+(m.2.2:ℝ))| ≤ H
  then radialKernel a L m p*ratioFourierProduct μ p*ratioMaskProduct A B C p else 0

/-- The exact near-strip term keeps every mask. Radial cancellation has
already taken place inside radialKernel before this norm bound is applied. -/
theorem masked_radial_near_bound {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {l u : ℝ} (hlu : l ≤ u) (hs : ∀ r, r ∉ Icc l u → a r = 0)
    (v₀ v₁ y₀ y₁ : ℝ) :
    ∃ Cnear : ℝ, 0 < Cnear ∧ ∀ (L H : ℝ) (m : ℤ × (ℤ × ℤ))
      (μ : ℝ → ℝ) (A B C : Set ℝ),
      MeasurableSet A → MeasurableSet B → MeasurableSet C →
      Measurable μ → (∀ t, 0 ≤ μ t) → Integrable μ →
      IntegrableOn (maskedRadialNearMass μ A B C L H m) (Icc v₀ v₁ ×ˢ Icc y₀ y₁) ∧
      IntegrableOn (maskedRadialNear a μ A B C L H m) (Icc v₀ v₁ ×ˢ Icc y₀ y₁) ∧
      ‖∫ p in Icc v₀ v₁ ×ˢ Icc y₀ y₁, maskedRadialNear a μ A B C L H m p‖ ≤
        Cnear*(∫ p in Icc v₀ v₁ ×ˢ Icc y₀ y₁, maskedRadialNearMass μ A B C L H m p) := by
  obtain ⟨Cnear,hCnear,hb⟩ := radial_uniform_power_decay ha hlu hs v₀ v₁ y₀ y₁ 0
  refine ⟨Cnear,hCnear,?_⟩
  intro L H m μ A B C hA hB hC hm h0 hi
  have hmass : 0 ≤ ∫ t, μ t := integral_nonneg h0
  have hQ : volume (Icc v₀ v₁ ×ˢ Icc y₀ y₁) < ⊤ := (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  have hset : MeasurableSet {p : ℝ × ℝ | |L*((m.1:ℝ)*p.1+(m.2.1:ℝ)*p.2+(m.2.2:ℝ))| ≤ H} := by
    apply measurableSet_le <;> fun_prop
  have hrm := ratioFourierProduct_measurable hi
  have hmaskm := ratioMaskProduct_measurable hA hB hC
  have hnm : Measurable (maskedRadialNearMass μ A B C L H m) :=
    Measurable.ite hset (hrm.norm.mul hmaskm.norm) measurable_const
  have hnear0 : ∀ p, 0 ≤ maskedRadialNearMass μ A B C L H m p := by
    intro p; unfold maskedRadialNearMass; split_ifs <;> positivity
  have hnearBound : ∀ p, maskedRadialNearMass μ A B C L H m p ≤ (∫ t, μ t)^3 := by
    intro p
    unfold maskedRadialNearMass
    split_ifs
    · exact (mul_le_of_le_one_right (norm_nonneg _) (ratioMaskProduct_norm_le_one A B C p)).trans (ratioFourierProduct_bound hm h0 hi p)
    · positivity
  have hni : IntegrableOn (maskedRadialNearMass μ A B C L H m) (Icc v₀ v₁ ×ˢ Icc y₀ y₁) :=
    (integrableOn_const hQ.ne (C := (∫ t, μ t)^3)).mono' hnm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => by rw [Real.norm_eq_abs,abs_of_nonneg (hnear0 p)]; exact hnearBound p))
  have hcm : Measurable (maskedRadialNear a μ A B C L H m) :=
    Measurable.ite hset (((radialKernel_measurable ha.continuous.measurable L m).mul hrm).mul hmaskm) measurable_const
  have hpoint : ∀ p ∈ Icc v₀ v₁ ×ˢ Icc y₀ y₁,
      ‖maskedRadialNear a μ A B C L H m p‖ ≤ Cnear*maskedRadialNearMass μ A B C L H m p := by
    intro p hp
    have hk : ‖radialKernel a L m p‖ ≤ Cnear := by
      have hh := hb p.1 hp.1 p.2 hp.2 (L*((m.1:ℝ)*p.1+(m.2.1:ℝ)*p.2+(m.2.2:ℝ)))
      rw [radialKernel,radial_integral_fourier]
      simpa only [pow_zero,one_mul] using hh
    unfold maskedRadialNear maskedRadialNearMass
    split_ifs
    · simp only [norm_mul]
      nlinarith [mul_le_mul_of_nonneg_right hk (mul_nonneg (norm_nonneg (ratioFourierProduct μ p)) (norm_nonneg (ratioMaskProduct A B C p)))]
    · simp
  have hci : IntegrableOn (maskedRadialNear a μ A B C L H m) (Icc v₀ v₁ ×ˢ Icc y₀ y₁) :=
    (hni.const_mul Cnear).mono' hcm.aestronglyMeasurable
      (ae_restrict_of_forall_mem (measurableSet_Icc.prod measurableSet_Icc) hpoint)
  refine ⟨hni,hci,?_⟩
  calc
    _ ≤ ∫ p in Icc v₀ v₁ ×ˢ Icc y₀ y₁, ‖maskedRadialNear a μ A B C L H m p‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ p in Icc v₀ v₁ ×ˢ Icc y₀ y₁, Cnear*maskedRadialNearMass μ A B C L H m p :=
      integral_mono_ae hci.norm (hni.const_mul _) (ae_restrict_of_forall_mem (measurableSet_Icc.prod measurableSet_Icc) hpoint)
    _ = _ := integral_const_mul _ _

theorem masked_radial_near_discard (a : ℝ → ℂ) (μ : ℝ → ℝ) (A B C : Set ℝ)
    (L H : ℝ) (m : ℤ × (ℤ × ℤ)) (p : ℝ × ℝ) :
    radialKernel a L m p*ratioFourierProduct μ p*ratioMaskProduct A B C p =
      maskedRadialNear a μ A B C L H m p + radialDiscard a μ L H m p*ratioMaskProduct A B C p := by
  unfold maskedRadialNear radialDiscard
  by_cases h : |L*((m.1:ℝ)*p.1+(m.2.1:ℝ)*p.2+(m.2.2:ℝ))| ≤ H
  · simp only [ite_eq_left h,ite_eq_right (not_lt_of_ge h),zero_mul,add_zero]
  · simp only [ite_eq_right h,ite_eq_left (lt_of_not_ge h),zero_add]

/-- Actual finite masked radial sum, with uniform near and tail constants,
exact L^3, mode count and original time mass. No first-factor mask is lost. -/
theorem masked_radial_sum_strip_bound {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {l u : ℝ} (hlu : l ≤ u) (hs : ∀ r, r ∉ Icc l u → a r = 0)
    (v₀ v₁ y₀ y₁ : ℝ) (hv : v₀ ≤ v₁) (hy : y₀ ≤ y₁) (n : ℕ) :
    ∃ Cnear Ctail : ℝ, 0 < Cnear ∧ 0 < Ctail ∧
      ∀ (L H : ℝ) (S : Finset (ℤ × (ℤ × ℤ))) (μ : ℝ → ℝ) (A B C : Set ℝ),
      0 < H → MeasurableSet A → MeasurableSet B → MeasurableSet C →
      Measurable μ → (∀ t, 0 ≤ μ t) → Integrable μ →
      (∀ m, IntegrableOn (fun p => radialKernel a L m p*ratioFourierProduct μ p*ratioMaskProduct A B C p)
        (Icc v₀ v₁ ×ˢ Icc y₀ y₁)) ∧
      (∀ m, IntegrableOn (maskedRadialNearMass μ A B C L H m) (Icc v₀ v₁ ×ˢ Icc y₀ y₁)) ∧
      ‖(L:ℂ)^3*(∑ m ∈ S, ∫ p in Icc v₀ v₁ ×ˢ Icc y₀ y₁,
        radialKernel a L m p*ratioFourierProduct μ p*ratioMaskProduct A B C p)‖ ≤
        |L|^3*Cnear*(∑ m ∈ S, ∫ p in Icc v₀ v₁ ×ˢ Icc y₀ y₁, maskedRadialNearMass μ A B C L H m p) +
        |L|^3*S.card*Ctail/H^n*(∫ t, μ t)^3*((v₁-v₀)*(y₁-y₀)) := by
  obtain ⟨Cnear,hCnear,hn⟩ := masked_radial_near_bound ha hlu hs v₀ v₁ y₀ y₁
  obtain ⟨Ctail,hCtail,hd⟩ := masked_radial_discard_integral_bound ha hlu hs v₀ v₁ y₀ y₁ hv hy n
  refine ⟨Cnear,Ctail,hCnear,hCtail,?_⟩
  intro L H S μ A B C hH hA hB hC hm h0 hi
  have hni := fun m => hn L H m μ A B C hA hB hC hm h0 hi
  have hdi := fun m => hd L H m μ A B C hH hA hB hC hm h0 hi
  have heq : ∀ m, (fun p => radialKernel a L m p*ratioFourierProduct μ p*ratioMaskProduct A B C p) =
      (fun p => maskedRadialNear a μ A B C L H m p) +
      (fun p => radialDiscard a μ L H m p*ratioMaskProduct A B C p) := by
    intro m; funext p; exact masked_radial_near_discard a μ A B C L H m p
  refine ⟨?_,fun m => (hni m).1,?_⟩
  · intro m; rw [heq]; exact (hni m).2.1.add (hdi m).1
  · have hmode : ∀ m ∈ S,
        ‖∫ p in Icc v₀ v₁ ×ˢ Icc y₀ y₁, radialKernel a L m p*ratioFourierProduct μ p*ratioMaskProduct A B C p‖ ≤
          Cnear*(∫ p in Icc v₀ v₁ ×ˢ Icc y₀ y₁, maskedRadialNearMass μ A B C L H m p) +
          Ctail/H^n*(∫ t, μ t)^3*((v₁-v₀)*(y₁-y₀)) := by
      intro m _
      rw [heq]
      simp only [Pi.add_def]
      rw [integral_add (hni m).2.1 (hdi m).1]
      exact (norm_add_le _ _).trans (add_le_add (hni m).2.2 (hdi m).2)
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    calc
      _ ≤ |L|^3*(∑ m ∈ S, ‖∫ p in Icc v₀ v₁ ×ˢ Icc y₀ y₁, radialKernel a L m p*ratioFourierProduct μ p*ratioMaskProduct A B C p‖) :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ |L|^3*(∑ m ∈ S, (Cnear*(∫ p in Icc v₀ v₁ ×ˢ Icc y₀ y₁, maskedRadialNearMass μ A B C L H m p) +
          Ctail/H^n*(∫ t, μ t)^3*((v₁-v₀)*(y₁-y₀)))) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hmode) (by positivity)
      _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum]; simp only [Finset.sum_const,nsmul_eq_mul]; ring

/-- The actual summed discarded complex integral has the same mask-uniform tail. -/
theorem masked_radial_total_discard_bound {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {l u : ℝ} (hlu : l ≤ u) (hs : ∀ r, r ∉ Icc l u → a r = 0)
    (v₀ v₁ y₀ y₁ : ℝ) (hv : v₀ ≤ v₁) (hy : y₀ ≤ y₁) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L H : ℝ) (S : Finset (ℤ × (ℤ × ℤ))) (μ : ℝ → ℝ) (A B Cmask : Set ℝ),
      0 < H → MeasurableSet A → MeasurableSet B → MeasurableSet Cmask → Measurable μ → (∀ t, 0 ≤ μ t) → Integrable μ →
      ‖(L:ℂ)^3*(∑ m ∈ S, ∫ p in Icc v₀ v₁ ×ˢ Icc y₀ y₁, radialDiscard a μ L H m p*ratioMaskProduct A B Cmask p)‖ ≤
        |L| ^3*S.card*C/H^n*(∫ t, μ t)^3*((v₁-v₀)*(y₁-y₀)) := by
  obtain ⟨C,hC,h⟩ := masked_radial_discard_integral_bound ha hlu hs v₀ v₁ y₀ y₁ hv hy n
  refine ⟨C,hC,?_⟩
  intro L H S μ A B Cmask hH hA hB hCmask hm h0 hi
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ |L| ^3*(∑ m ∈ S, ‖∫ p in Icc v₀ v₁ ×ˢ Icc y₀ y₁, radialDiscard a μ L H m p*ratioMaskProduct A B Cmask p‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ |L| ^3*(∑ _m ∈ S, C/H^n*(∫ t, μ t)^3*((v₁-v₀)*(y₁-y₀))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun m _ => (h L H m μ A B Cmask hH hA hB hCmask hm h0 hi).2)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.masked_radial_discard_integral_bound
#print axioms GuthMaynard.Improvement.masked_radial_near_bound
#print axioms GuthMaynard.Improvement.masked_radial_near_discard
#print axioms GuthMaynard.Improvement.masked_radial_sum_strip_bound

#print axioms GuthMaynard.Improvement.masked_radial_total_discard_bound
