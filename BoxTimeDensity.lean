module
public import SampledAdditiveMoments
public import FiniteCubicBasics
public import GuthMaynard.Improvement.CubicMaskedEstimate

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Set
open scoped FourierTransform
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement

def realEnergyBox : ℝ → ℝ := (Icc (-(1/64:ℝ)) (1/64)).indicator (fun _ => 32)
def boxTimeDensity (W : Finset ℝ) (t : ℝ) : ℝ := ∑ w ∈ W, realEnergyBox (t-w)

theorem real_energy_box_cast (t : ℝ) : (realEnergyBox t:ℂ) = energyBox t := by
  unfold realEnergyBox energyBox
  by_cases ht : t ∈ Icc (-(1/64:ℝ)) (1/64)
  · rw [indicator_of_mem ht,indicator_of_mem ht]; norm_num
  · rw [indicator_of_notMem ht,indicator_of_notMem ht]; norm_num

theorem box_time_cast (W : Finset ℝ) (t : ℝ) :
    (boxTimeDensity W t:ℂ) = finiteSmooth W (fun w => w) energyBox t := by
  simp only [boxTimeDensity,Complex.ofReal_sum,real_energy_box_cast,finiteSmooth]

theorem box_time_measurable (W : Finset ℝ) : Measurable (boxTimeDensity W) := by
  have hb : Measurable realEnergyBox := measurable_const.indicator measurableSet_Icc
  unfold boxTimeDensity
  fun_prop

theorem box_time_nonneg (W : Finset ℝ) (t : ℝ) : 0 ≤ boxTimeDensity W t := by
  apply sum_nonneg
  intro w _
  exact indicator_nonneg (by intros; norm_num) _

theorem box_time_integrable (W : Finset ℝ) : Integrable (boxTimeDensity W) := by
  have hb : Integrable realEnergyBox := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact integrableOn_const isCompact_Icc.measure_lt_top.ne
  exact integrable_finsetSum _ (fun w _ => hb.comp_sub_right w)

theorem box_time_square_integrable (W : Finset ℝ) : Integrable (fun t => boxTimeDensity W t^2) := by
  have hh := (memLp_two_iff_integrable_sq_norm
    (finite_smooth_integrable W (fun w => w) energy_box_integrable).aestronglyMeasurable).mp
      (finite_smooth_memLp_two W (fun w => w) energy_box_integrable energy_box_bound)
  simpa only [← box_time_cast,Complex.norm_real,Real.norm_eq_abs,sq_abs] using hh

theorem box_time_square_bound (W : Finset ℝ)
    (hsep : ∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) :
    (∫ t, boxTimeDensity W t^2) ≤ 32*(W.card:ℝ) := by
  have hh := point_smoothing_energy W 0 hsep
  simpa only [sub_zero,← box_time_cast,Complex.norm_real,Real.norm_eq_abs,sq_abs] using hh

theorem box_time_fourier (W : Finset ℝ) (ξ : ℝ) :
    𝓕 (fun t => (boxTimeDensity W t:ℂ)) ξ =
      (measureFourier (finiteTimeMeasure W) ξ)*𝓕 energyBox ξ := by
  simp only [box_time_cast,finite_smooth_fourier W (fun w => w) energy_box_integrable,
    finite_time_fourier]

/-- Fixed-width positive smoothing dominates every atomic Fourier value
on the actual compact band. No limit or unbounded L2 mass is involved. -/
theorem box_time_fourier_domination (W : Finset ℝ) {ξ : ℝ} (hξ : |ξ| ≤ 1) :
    ‖measureFourier (finiteTimeMeasure W) ξ‖ ≤
      2*‖𝓕 (fun t => (boxTimeDensity W t:ℂ)) ξ‖ := by
  rw [box_time_fourier,norm_mul]
  nlinarith [mul_le_mul_of_nonneg_left (energy_box_fourier_lower hξ)
    (norm_nonneg (measureFourier (finiteTimeMeasure W) ξ))]

theorem box_pair_fourier (W : Finset ℝ) (ξ : ℝ) :
    𝓕 (finiteSmooth (W ×ˢ W) (fun p => p.1+p.2) energyPairBox) ξ =
      (𝓕 (fun t => (boxTimeDensity W t:ℂ)) ξ)^2 := by
  rw [finite_smooth_fourier _ _ energy_pair_box_integrable,
    box_time_fourier,energy_pair_box_fourier,mul_pow]
  congr 1
  have hh := centered_pair_character W 0 ξ
  simpa only [mul_zero,sub_zero,centeredCharacter,finite_time_fourier] using hh

/-- The ordinary Fourier fourth moment of the fixed smoothing is bounded
by the literal closed-boundary discrete additive energy. -/
theorem box_time_fourth_bound (W : Finset ℝ) :
    (∫ ξ, ‖𝓕 (fun t => (boxTimeDensity W t:ℂ)) ξ‖^4) ≤
      64*(discreteAdditiveEnergy W:ℝ) := by
  have h1 := finite_smooth_integrable (W ×ˢ W) (fun p => p.1+p.2) energy_pair_box_integrable
  have h2 := finite_smooth_memLp_two (W ×ˢ W) (fun p => p.1+p.2)
    energy_pair_box_integrable energy_pair_box_bound
  have he : (fun ξ => ‖𝓕 (fun t => (boxTimeDensity W t:ℂ)) ξ‖^4) =
      (fun ξ => ‖𝓕 (finiteSmooth (W ×ˢ W) (fun p => p.1+p.2) energyPairBox) ξ‖^2) := by
    funext ξ
    rw [box_pair_fourier,norm_pow]
    ring
  rw [he,ordinary_fourier_integral_sq h1 h2]
  simpa only [mul_zero,sub_zero] using pair_smoothing_energy W 0

end Montgomery.RationalMoment
