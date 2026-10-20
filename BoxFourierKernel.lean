module
public import CompactSmoothingEnergy

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Set
open scoped FourierTransform Convolution
namespace Montgomery.RationalMoment

def energyBox : ℝ → ℂ := (Icc (-(1/64:ℝ)) (1/64)).indicator (fun _ => (32:ℂ))

theorem energy_box_integrable : Integrable energyBox := by
  apply (integrable_indicator_iff measurableSet_Icc).mpr
  exact integrableOn_const isCompact_Icc.measure_lt_top.ne

theorem energy_box_bound (t : ℝ) : ‖energyBox t‖ ≤ 32 := by
  unfold energyBox
  by_cases h : t ∈ Icc (-(1/64:ℝ)) (1/64)
  · rw [indicator_of_mem h]; norm_num
  · rw [indicator_of_notMem h]; norm_num

theorem energy_box_support (t : ℝ) (ht : (1/64:ℝ) < |t|) : energyBox t=0 := by
  have hn : t ∉ Icc (-(1/64:ℝ)) (1/64) := by
    intro h
    exact not_le.mpr ht (abs_le.mpr h)
  exact indicator_of_notMem hn _

theorem energy_box_mass : (∫ t, energyBox t)=1 ∧ (∫ t, ‖energyBox t‖)=1 := by
  constructor
  · rw [energyBox,integral_indicator measurableSet_Icc,setIntegral_const,
      Real.volume_real_Icc_of_le (by norm_num : -(1/64:ℝ) ≤ 1/64)]
    norm_num
  · have he : (fun t => ‖energyBox t‖) = (Icc (-(1/64:ℝ)) (1/64)).indicator (fun _ => (32:ℝ)) := by
      funext t
      by_cases h : t ∈ Icc (-(1/64:ℝ)) (1/64)
      · simp only [energyBox,indicator_of_mem h]; norm_num
      · simp only [energyBox,indicator_of_notMem h]; norm_num
    rw [he,integral_indicator measurableSet_Icc,setIntegral_const,
      Real.volume_real_Icc_of_le (by norm_num : -(1/64:ℝ) ≤ 1/64)]
    norm_num

/-- This elementary lower bound uses only the small support of the box,
not an unproved positivity formula for its Fourier transform. -/
theorem energy_box_fourier_lower {ξ : ℝ} (hξ : |ξ| ≤ 1) :
    (1/2:ℝ) ≤ ‖𝓕 energyBox ξ‖ := by
  let J := Icc (-(1/64:ℝ)) (1/64)
  have he : 𝓕 energyBox ξ - 1 =
      ∫ t in J, (32:ℂ)*(GuthMaynard.Improvement.phase (-ξ*t)-1) := by
    rw [GuthMaynard.Improvement.fourier_eq_phase_integral]
    have hp : (fun t => GuthMaynard.Improvement.phase (-ξ*t)*energyBox t) =
        J.indicator (fun t => (32:ℂ)*GuthMaynard.Improvement.phase (-ξ*t)) := by
      funext t
      by_cases ht : t ∈ J
      · rw [show energyBox t=32 from indicator_of_mem ht _,indicator_of_mem ht]
        ring
      · rw [show energyBox t=0 from indicator_of_notMem ht _,indicator_of_notMem ht,mul_zero]
    rw [hp,integral_indicator measurableSet_Icc]
    have hi : IntegrableOn (fun t => (32:ℂ)*GuthMaynard.Improvement.phase (-ξ*t)) J :=
      ContinuousOn.integrableOn_Icc (by unfold GuthMaynard.Improvement.phase; fun_prop)
    have hconst : IntegrableOn (fun _ : ℝ => (32:ℂ)) J :=
      integrableOn_const isCompact_Icc.measure_lt_top.ne
    have hm : (∫ _t in J, (32:ℂ))=1 := by
      rw [setIntegral_const]
      norm_num [J,Real.volume_real_Icc_of_le]
    simp_rw [mul_sub,mul_one]
    rw [integral_sub hi hconst,hm]
  have hb (t : ℝ) (ht : t ∈ J) : ‖(32:ℂ)*(GuthMaynard.Improvement.phase (-ξ*t)-1)‖ ≤ 16 := by
    have ht0 : |t| ≤ 1/64 := abs_le.mpr ht
    have hp : |2*Real.pi*(-ξ*t)| ≤ 1/2 := by
      simp only [abs_mul,abs_neg,abs_of_pos Real.pi_pos,abs_of_pos (by norm_num : (0:ℝ)<2)]
      have hprod : |ξ| * |t| ≤ 1/64 := by
        nlinarith [mul_le_mul hξ ht0 (abs_nonneg t) (by norm_num : (0:ℝ) ≤ 1)]
      calc
        _ ≤ 2*Real.pi*(1/64) := mul_le_mul_of_nonneg_left hprod (by positivity)
        _ ≤ _ := by nlinarith [Real.pi_lt_four]
    have hh : ‖GuthMaynard.Improvement.phase (-ξ*t)-1‖ ≤ 1/2 := by
      have hn := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi*(-ξ*t))
      have heq : Complex.exp (Complex.I*((2*Real.pi*(-ξ*t):ℝ):ℂ)) =
          GuthMaynard.Improvement.phase (-ξ*t) := by
        unfold GuthMaynard.Improvement.phase
        congr 1
        push_cast
        ring
      rw [heq,Real.norm_eq_abs] at hn
      exact hn.trans hp
    rw [norm_mul]
    rw [show ‖(32:ℂ)‖=(32:ℝ) by norm_num]
    linarith
  have hn : ‖𝓕 energyBox ξ-1‖ ≤ 1/2 := by
    rw [he]
    have hh := norm_setIntegral_le_of_norm_le_const (μ := volume)
      isCompact_Icc.measure_lt_top hb
    exact hh.trans (by norm_num [J,Real.volume_real_Icc_of_le])
  have ht := norm_sub_le (𝓕 energyBox ξ) (𝓕 energyBox ξ-1)
  rw [sub_sub_cancel] at ht
  norm_num at ht
  linarith

/-- Its convolution is supported twice as far out and retains a fixed L∞ bound. -/
def energyPairBox : ℝ → ℂ := energyBox ⋆[ContinuousLinearMap.mul ℂ ℂ] energyBox

theorem energy_pair_box_integrable : Integrable energyPairBox :=
  energy_box_integrable.integrable_convolution _ energy_box_integrable

theorem energy_pair_box_bound (t : ℝ) : ‖energyPairBox t‖ ≤ 32 := by
  unfold energyPairBox
  rw [convolution_def]
  calc
    _ ≤ ∫ x, ‖energyBox x*energyBox (t-x)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖energyBox x‖*32 := by
      apply integral_mono_ae
      · exact (energy_box_integrable.mul_bdd
          (energy_box_integrable.comp_sub_left t).aestronglyMeasurable
          (c := 32) (Filter.Eventually.of_forall (fun x => energy_box_bound (t-x)))).norm
      · exact energy_box_integrable.norm.mul_const 32
      · filter_upwards with x
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (energy_box_bound _) (norm_nonneg _)
    _ = 32 := by rw [integral_mul_const,energy_box_mass.2]; norm_num

theorem energy_pair_box_support (t : ℝ) (ht : (1/32:ℝ) < |t|) : energyPairBox t=0 := by
  unfold energyPairBox
  rw [convolution_def]
  have he : (fun x => energyBox x*energyBox (t-x)) = 0 := by
    funext x
    by_cases hx : (1/64:ℝ) < |x|
    · simp [energy_box_support x hx]
    · have hh : (1/64:ℝ) < |t-x| := by
        have hab := abs_add_le x (t-x)
        have hn : |x| ≤ 1/64 := le_of_not_gt hx
        rw [add_sub_cancel] at hab
        linarith
      simp [energy_box_support (t-x) hh]
  change (∫ x, energyBox x*energyBox (t-x))=0
  rw [he]
  exact integral_zero ℝ ℂ

theorem energy_pair_box_fourier (ξ : ℝ) :
    𝓕 energyPairBox ξ=(𝓕 energyBox ξ)^2 := by
  rw [energyPairBox,Real.fourier_mul_convolution_eq energy_box_integrable energy_box_integrable,pow_two]

end Montgomery.RationalMoment
