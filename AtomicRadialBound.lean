module
public import AtomicRadialAssembly
public import BoxTimeDensity

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Finset
open scoped ContDiff FourierTransform
namespace GuthMaynard.Improvement.AtomicCubic

def ratioBox : Set (ℝ × ℝ) := Icc (1/10:ℝ) 10 ×ˢ Icc (1/10:ℝ) 10

theorem ratio_box_volume : volume.real ratioBox = (99/10:ℝ)^2 := by
  rw [ratioBox,Measure.real,Measure.volume_eq_prod,Measure.prod_prod,ENNReal.toReal_mul]
  change volume.real (Icc (1/10:ℝ) 10)*volume.real (Icc (1/10:ℝ) 10) = _
  rw [Real.volume_real_Icc_of_le (by norm_num)]
  norm_num

/-- Radial cancellation is preserved before comparison of Fourier magnitudes.
This is the direct finite-profile replacement for a density approximation. -/
theorem radial_profile_sum_bound (w : MathCollab.Density.ReflectionCutoff) (n : ℕ) :
    ∃ Cnear Ctail : ℝ, 0 < Cnear ∧ 0 < Ctail ∧
    ∀ (L H : ℝ) (S : Finset (ℤ × (ℤ × ℤ))) (F : ℝ → ℂ) (M D : ℝ) (μ : ℝ → ℝ),
      0 < H → Continuous F → 0 ≤ M → (∀ ξ, ‖F ξ‖ ≤ M) → 0 ≤ D →
      Measurable μ → (∀ t, 0 ≤ μ t) → Integrable μ →
      (∀ p ∈ ratioBox, ‖ratioFourierProduct F p‖ ≤ D*‖GuthMaynard.Improvement.ratioFourierProduct μ p‖) →
      ‖(L:ℂ)^3*(∑ m ∈ S, ∫ p in ratioBox,
        radialKernel (fun x => (w x:ℂ)) L m p*ratioFourierProduct F p)‖ ≤
      |L|^3*Cnear*D*(∑ m ∈ S, ∫ p in ratioBox, maskedRadialNearMass μ univ univ univ L H m p)+
        |L|^3*S.card*Ctail/H^n*M^3*(99/10:ℝ)^2 := by
  have hs : ∀ x, x ∉ Icc (1/2:ℝ) 5 → (w x:ℂ)=0 := by
    intro x hx
    have hz : w x=0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (w.support hh))
    simp only [hz,Complex.ofReal_zero]
  obtain ⟨Cn,hCn,hnear⟩ := radial_uniform_power_decay w.complex_smooth (by norm_num : (1/2:ℝ) ≤ 5)
    hs (1/10) 10 (1/10) 10 0
  obtain ⟨Ct,hCt,htail⟩ := radial_uniform_power_decay w.complex_smooth (by norm_num : (1/2:ℝ) ≤ 5)
    hs (1/10) 10 (1/10) 10 n
  obtain ⟨B,hB,hiNear⟩ := masked_radial_near_bound w.complex_smooth (by norm_num : (1/2:ℝ) ≤ 5)
    hs (1/10) 10 (1/10) 10
  refine ⟨Cn,Ct,hCn,hCt,?_⟩
  intro L H S F M D μ hH hF hM hbF hD hm h0 hi hdom
  have hQ : volume ratioBox < ⊤ := (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  have hQm : MeasurableSet ratioBox := measurableSet_Icc.prod measurableSet_Icc
  have hni (m : ℤ × (ℤ × ℤ)) : IntegrableOn
      (maskedRadialNearMass μ univ univ univ L H m) ratioBox :=
    (hiNear L H m μ univ univ univ MeasurableSet.univ MeasurableSet.univ MeasurableSet.univ hm h0 hi).1
  have hk (m : ℤ × (ℤ × ℤ)) (p : ℝ × ℝ) (hp : p ∈ ratioBox) :
      ‖radialKernel (fun x => (w x:ℂ)) L m p‖ ≤ Cn := by
    rw [radialKernel,radial_integral_fourier]
    simpa only [pow_zero,one_mul] using hnear p.1 hp.1 p.2 hp.2 _
  have hInt (m : ℤ × (ℤ × ℤ)) : IntegrableOn (fun p =>
      radialKernel (fun x => (w x:ℂ)) L m p*ratioFourierProduct F p) ratioBox := by
    apply (integrableOn_const hQ.ne (C := Cn*M^3)).mono'
      ((radialKernel_measurable w.complex_smooth.continuous.measurable L m).mul
        (ratio_fourier_measurable hF)).aestronglyMeasurable
    apply ae_restrict_of_forall_mem hQm
    intro p hp
    dsimp only [Pi.mul_apply]
    rw [norm_mul]
    exact mul_le_mul (hk m p hp) (ratio_fourier_bound hM hbF p) (norm_nonneg _) hCn.le
  have hpoint (m : ℤ × (ℤ × ℤ)) (p : ℝ × ℝ) (hp : p ∈ ratioBox) :
      ‖radialKernel (fun x => (w x:ℂ)) L m p*ratioFourierProduct F p‖ ≤
      Cn*D*maskedRadialNearMass μ univ univ univ L H m p+Ct/H^n*M^3 := by
    have hmask : ratioMaskProduct univ univ univ p=1 := by simp [ratioMaskProduct]
    by_cases hh : |L*((m.1:ℝ)*p.1+(m.2.1:ℝ)*p.2+(m.2.2:ℝ))| ≤ H
    · have hnearMass : maskedRadialNearMass μ univ univ univ L H m p =
          ‖GuthMaynard.Improvement.ratioFourierProduct μ p‖ := by
        simp only [maskedRadialNearMass,ite_eq_left hh,hmask,norm_one,mul_one]
      rw [hnearMass,norm_mul]
      have hx := mul_le_mul (hk m p hp) (hdom p hp) (norm_nonneg _) hCn.le
      nlinarith [show 0 ≤ Ct/H^n*M^3 by positivity]
    · have ht : ‖radialKernel (fun x => (w x:ℂ)) L m p‖ ≤ Ct/H^n := by
        have hb := htail p.1 hp.1 p.2 hp.2 (L*((m.1:ℝ)*p.1+(m.2.1:ℝ)*p.2+(m.2.2:ℝ)))
        have hpw := pow_le_pow_left₀ hH.le (le_of_lt (lt_of_not_ge hh)) n
        rw [radialKernel,radial_integral_fourier]
        apply (le_div_iff₀ (pow_pos hH n)).mpr
        nlinarith [mul_le_mul_of_nonneg_right hpw (norm_nonneg (𝓕 (radialAmplitude (fun x => (w x:ℂ)) p.1 p.2)
          (L*((m.1:ℝ)*p.1+(m.2.1:ℝ)*p.2+(m.2.2:ℝ)))))]
      rw [show maskedRadialNearMass μ univ univ univ L H m p=0 from ite_eq_right hh,
        mul_zero,zero_add,norm_mul]
      exact mul_le_mul ht (ratio_fourier_bound hM hbF p) (norm_nonneg _) (by positivity)
  have hmode (m : ℤ × (ℤ × ℤ)) :
      ‖∫ p in ratioBox, radialKernel (fun x => (w x:ℂ)) L m p*ratioFourierProduct F p‖ ≤
      Cn*D*(∫ p in ratioBox, maskedRadialNearMass μ univ univ univ L H m p)+
        Ct/H^n*M^3*(99/10:ℝ)^2 := by
    calc
      _ ≤ ∫ p in ratioBox, ‖radialKernel (fun x => (w x:ℂ)) L m p*ratioFourierProduct F p‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ p in ratioBox, Cn*D*maskedRadialNearMass μ univ univ univ L H m p+Ct/H^n*M^3 :=
        integral_mono_ae (hInt m).norm ((hni m).const_mul _ |>.add (integrableOn_const hQ.ne))
          (ae_restrict_of_forall_mem hQm (hpoint m))
      _ = _ := by
        rw [integral_add ((hni m).const_mul _) (integrableOn_const hQ.ne),integral_const_mul,setIntegral_const]
        simp only [smul_eq_mul]
        rw [ratio_box_volume]
        ring
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ |L|^3*(∑ m ∈ S, ‖∫ p in ratioBox, radialKernel (fun x => (w x:ℂ)) L m p*ratioFourierProduct F p‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ |L|^3*(∑ m ∈ S, (Cn*D*(∫ p in ratioBox, maskedRadialNearMass μ univ univ univ L H m p)+
        Ct/H^n*M^3*(99/10:ℝ)^2)) := mul_le_mul_of_nonneg_left (sum_le_sum (fun m _ => hmode m)) (by positivity)
    _ = _ := by rw [sum_add_distrib,← mul_sum]; simp only [sum_const,nsmul_eq_mul]; ring

end GuthMaynard.Improvement.AtomicCubic
