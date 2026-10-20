module
public import BoxFourierKernel

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Set
open scoped FourierTransform Convolution
namespace Montgomery.RationalMoment

def centeredCharacter (W : Finset ℝ) (t₀ ξ : ℝ) : ℂ :=
  ∑ w ∈ W, GuthMaynard.Improvement.phase (-ξ*(w-t₀))

/-- The time translate is a unit phase; the actual logarithmic rational sum
has exactly the same norm. -/
theorem centered_character_norm (W : Finset ℝ) (t₀ r : ℝ) :
    ‖centeredCharacter W t₀ (Real.log r/(2*Real.pi))‖ = ‖∑ t ∈ W, phase r t‖ := by
  have he : centeredCharacter W t₀ (Real.log r/(2*Real.pi)) =
      GuthMaynard.Improvement.phase ((Real.log r/(2*Real.pi))*t₀)*star (∑ t ∈ W, phase r t) := by
    rw [centeredCharacter,star_sum,mul_sum]
    apply sum_congr rfl
    intro t _
    have hp : GuthMaynard.Improvement.phase (-(Real.log r/(2*Real.pi))*t) = star (phase r t) := by
      rw [show -(Real.log r/(2*Real.pi))*t=(-t)*GuthMaynard.Improvement.mellinFrequency r by
        unfold GuthMaynard.Improvement.mellinFrequency; ring,
        GuthMaynard.Improvement.mellinFrequency_phase]
      change Complex.exp _ = (starRingEnd ℂ) (Complex.exp _)
      rw [← Complex.exp_conj]
      congr 1
      simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]
      push_cast
      ring
    rw [← hp,← GuthMaynard.Improvement.phase_add]
    congr 1
    ring
  rw [he,norm_mul,GuthMaynard.Improvement.phase_norm,norm_star,one_mul]

/-- The convolution smoothing has the square of the original character
sum, without coefficient collisions or a change of energy definition. -/
theorem centered_pair_character (W : Finset ℝ) (t₀ ξ : ℝ) :
    (∑ p ∈ W ×ˢ W, GuthMaynard.Improvement.phase (-ξ*(p.1+p.2-2*t₀))) =
      (centeredCharacter W t₀ ξ)^2 := by
  rw [pow_two,centeredCharacter,sum_mul]
  simp only [sum_product,mul_sum]
  apply sum_congr rfl
  intro t _
  apply sum_congr rfl
  intro u _
  rw [← GuthMaynard.Improvement.phase_add]
  congr 1
  ring

/-- Narrow single-point smoothing has no overlap on a one-separated set. -/
theorem point_smoothing_energy (W : Finset ℝ) (t₀ : ℝ)
    (hsep : ∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) :
    (∫ t, ‖finiteSmooth W (fun w => w-t₀) energyBox t‖^2) ≤ 32*(W.card:ℝ) := by
  have hh := finite_smooth_l2_energy W (fun w => w-t₀) energy_box_integrable
    (by norm_num : (0:ℝ) ≤ 1/64) (by norm_num : (0:ℝ) ≤ 32)
    energy_box_bound energy_box_support
  have he : (∑ t ∈ W, ∑ u ∈ W, if |(t-t₀)-(u-t₀)| ≤ 2*(1/64:ℝ) then (1:ℝ) else 0) = W.card := by
    calc
      _ = ∑ _t ∈ W, (1:ℝ) := by
        apply sum_congr rfl
        intro t ht
        rw [sum_eq_single t]
        · simp
        · intro u hu hne
          have hdist := hsep t ht u hu hne.symm
          have hn : ¬ |(t-t₀)-(u-t₀)| ≤ 2*(1/64:ℝ) := by
            rw [sub_sub_sub_cancel_right]
            linarith
          exact ite_eq_right hn
        · exact fun hn => False.elim (hn ht)
      _ = _ := by simp
  rw [he,show (2:ℝ)*(1/64)*32^2=32 by norm_num] at hh
  exact hh

/-- Pair-sum smoothing is bounded by the literal quadruple count. -/
theorem pair_smoothing_energy (W : Finset ℝ) (t₀ : ℝ) :
    (∫ t, ‖finiteSmooth (W ×ˢ W) (fun p => p.1+p.2-2*t₀) energyPairBox t‖^2) ≤
      64*(discreteAdditiveEnergy W:ℝ) := by
  have hh := finite_smooth_l2_energy (W ×ˢ W) (fun p => p.1+p.2-2*t₀)
    energy_pair_box_integrable (by norm_num : (0:ℝ) ≤ 1/32) (by norm_num : (0:ℝ) ≤ 32)
    energy_pair_box_bound energy_pair_box_support
  have hc : (∑ p ∈ W ×ˢ W, ∑ q ∈ W ×ˢ W,
      if |(p.1+p.2-2*t₀)-(q.1+q.2-2*t₀)| ≤ 2*(1/32:ℝ) then (1:ℝ) else 0) ≤
      (discreteAdditiveEnergy W:ℝ) := by
    have he : (discreteAdditiveEnergy W:ℝ) = ∑ t ∈ W, ∑ u ∈ W, ∑ v ∈ W, ∑ w ∈ W,
        if |t+u-v-w| ≤ 1 then (1:ℝ) else 0 := by
      unfold discreteAdditiveEnergy
      simp only [card_eq_sum_ones,Nat.cast_sum,sum_filter,sum_product,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    rw [he]
    simp only [sum_product]
    apply sum_le_sum
    intro t _
    apply sum_le_sum
    intro u _
    apply sum_le_sum
    intro v _
    apply sum_le_sum
    intro w _
    by_cases h : |(t+u-2*t₀)-(v+w-2*t₀)| ≤ 2*(1/32:ℝ)
    · have heq : (t+u-2*t₀)-(v+w-2*t₀)=t+u-v-w := by ring
      rw [heq] at h
      have h1 : |t+u-v-w| ≤ 1 := by linarith
      rw [heq,ite_eq_left h,ite_eq_left h1]
    · simp only [ite_eq_right h]
      split_ifs <;> norm_num
  rw [show (2:ℝ)*(1/32)*32^2=64 by norm_num] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hc (by norm_num))

/-- Sampled second moment from the existing Fourier-square sampling theorem. -/
theorem sampled_character_second {ι : Type*} [Fintype ι]
    {T t₀ δ : ℝ} (hT : 1 < T) (hδ : 0 < δ)
    (W : Finset ℝ) (hW : ∀ t ∈ W, t ∈ Icc t₀ (t₀+T))
    (hsep : ∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|)
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ 1)
    (hxs : Pairwise (fun i j => δ ≤ |x i-x j|)) :
    (∑ i, ‖centeredCharacter W t₀ (x i)‖^2) ≤
      128*(δ⁻¹+8*Real.pi*T)*(W.card:ℝ) := by
  let f := finiteSmooth W (fun w => w-t₀) energyBox
  have hf := finite_smooth_integrable W (fun w => w-t₀) energy_box_integrable
  have hlp := finite_smooth_memLp_two W (fun w => w-t₀) energy_box_integrable energy_box_bound
  have hsupport : Function.support f ⊆ Icc (-(2*T)) (2*T) := by
    apply finite_smooth_support _ _ energy_box_support
    intro w hw
    have hh := hW w hw
    have hab : |w-t₀| ≤ T := abs_le.mpr ⟨by linarith [hh.1],by linarith [hh.2]⟩
    linarith
  have hb := GuthMaynard.Improvement.sampling_fourier_square hf hlp (by linarith : 0 ≤ 2*T)
    hsupport x hδ hxs
  have hnorm (i : ι) : ‖centeredCharacter W t₀ (x i)‖^2 ≤ 4*‖𝓕 f (x i)‖^2 := by
    rw [finite_smooth_fourier _ _ energy_box_integrable,norm_mul]
    change ‖centeredCharacter W t₀ (x i)‖^2 ≤
      4*(‖centeredCharacter W t₀ (x i)‖*‖𝓕 energyBox (x i)‖)^2
    have hh := energy_box_fourier_lower (hx i)
    nlinarith [mul_nonneg (sq_nonneg ‖centeredCharacter W t₀ (x i)‖)
      (show 0 ≤ 4*‖𝓕 energyBox (x i)‖^2-1 by nlinarith)]
  calc
    _ ≤ ∑ i, 4*‖𝓕 f (x i)‖^2 := sum_le_sum (fun i _ => hnorm i)
    _ = 4*∑ i, ‖𝓕 f (x i)‖^2 := (mul_sum _ _ _).symm
    _ ≤ 4*((δ⁻¹+4*Real.pi*(2*T))*(∫ t, ‖f t‖^2)) := by gcongr
    _ ≤ 4*((δ⁻¹+4*Real.pi*(2*T))*(32*(W.card:ℝ))) := by
      gcongr
      exact point_smoothing_energy W t₀ hsep
    _ = _ := by ring

/-- Sampled fourth moment has the actual additive energy on the right. -/
theorem sampled_character_fourth {ι : Type*} [Fintype ι]
    {T t₀ δ : ℝ} (hT : 1 < T) (hδ : 0 < δ)
    (W : Finset ℝ) (hW : ∀ t ∈ W, t ∈ Icc t₀ (t₀+T))
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ 1)
    (hxs : Pairwise (fun i j => δ ≤ |x i-x j|)) :
    (∑ i, ‖centeredCharacter W t₀ (x i)‖^4) ≤
      1024*(δ⁻¹+12*Real.pi*T)*(discreteAdditiveEnergy W:ℝ) := by
  let f := finiteSmooth (W ×ˢ W) (fun p => p.1+p.2-2*t₀) energyPairBox
  have hf := finite_smooth_integrable (W ×ˢ W) (fun p => p.1+p.2-2*t₀) energy_pair_box_integrable
  have hlp := finite_smooth_memLp_two (W ×ˢ W) (fun p => p.1+p.2-2*t₀)
    energy_pair_box_integrable energy_pair_box_bound
  have hsupport : Function.support f ⊆ Icc (-(3*T)) (3*T) := by
    apply finite_smooth_support _ _ energy_pair_box_support
    intro p hp
    obtain ⟨hp1,hp2⟩ := mem_product.mp hp
    have hh1 := hW p.1 hp1
    have hh2 := hW p.2 hp2
    have hab : |p.1+p.2-2*t₀| ≤ 2*T :=
      abs_le.mpr ⟨by linarith [hh1.1,hh2.1],by linarith [hh1.2,hh2.2]⟩
    linarith
  have hb := GuthMaynard.Improvement.sampling_fourier_square hf hlp (by linarith : 0 ≤ 3*T)
    hsupport x hδ hxs
  have hnorm (i : ι) : ‖centeredCharacter W t₀ (x i)‖^4 ≤ 16*‖𝓕 f (x i)‖^2 := by
    rw [finite_smooth_fourier _ _ energy_pair_box_integrable,centered_pair_character,
      energy_pair_box_fourier,norm_mul,norm_pow,norm_pow]
    have hh := energy_box_fourier_lower (hx i)
    have hp : (1/16:ℝ) ≤ ‖𝓕 energyBox (x i)‖^4 := by
      nlinarith [sq_nonneg (‖𝓕 energyBox (x i)‖^2-1/4)]
    nlinarith [mul_nonneg (pow_nonneg (norm_nonneg (centeredCharacter W t₀ (x i))) 4)
      (show 0 ≤ 16*‖𝓕 energyBox (x i)‖^4-1 by linarith)]
  calc
    _ ≤ ∑ i, 16*‖𝓕 f (x i)‖^2 := sum_le_sum (fun i _ => hnorm i)
    _ = 16*∑ i, ‖𝓕 f (x i)‖^2 := (mul_sum _ _ _).symm
    _ ≤ 16*((δ⁻¹+4*Real.pi*(3*T))*(∫ t, ‖f t‖^2)) := by gcongr
    _ ≤ 16*((δ⁻¹+4*Real.pi*(3*T))*(64*(discreteAdditiveEnergy W:ℝ))) := by
      gcongr
      exact pair_smoothing_energy W t₀
    _ = _ := by ring

/-- The separated cubic estimate needed for the small-gcd argument follows
from the two proved sampled moments. No general L3 sampling theorem is assumed. -/
theorem sampled_character_cubic {ι : Type*} [Fintype ι]
    {T t₀ δ : ℝ} (hT : 1 < T) (hδ : 0 < δ)
    (W : Finset ℝ) (hW : ∀ t ∈ W, t ∈ Icc t₀ (t₀+T))
    (hsep : ∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|)
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ 1)
    (hxs : Pairwise (fun i j => δ ≤ |x i-x j|)) :
    (∑ i, ‖centeredCharacter W t₀ (x i)‖^3) ≤
      (512*(1+12*Real.pi))*(T+δ⁻¹)*Real.sqrt (W.card:ℝ)*
        Real.sqrt (discreteAdditiveEnergy W:ℝ) := by
  let D := (1+12*Real.pi)*(T+δ⁻¹)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hsecond := sampled_character_second hT hδ W hW hsep x hx hxs
  have hfourth := sampled_character_fourth hT hδ W hW x hx hxs
  have hd2 : δ⁻¹+8*Real.pi*T ≤ D := by
    dsimp [D]
    nlinarith [mul_nonneg Real.pi_pos.le (inv_nonneg.mpr hδ.le)]
  have hd4 : δ⁻¹+12*Real.pi*T ≤ D := by
    dsimp [D]
    nlinarith [mul_nonneg Real.pi_pos.le (inv_nonneg.mpr hδ.le)]
  have h2 : (∑ i, ‖centeredCharacter W t₀ (x i)‖^2) ≤ 128*D*(W.card:ℝ) :=
    hsecond.trans (by gcongr)
  have h4 : (∑ i, ‖centeredCharacter W t₀ (x i)‖^4) ≤ 1024*D*(discreteAdditiveEnergy W:ℝ) :=
    hfourth.trans (by gcongr)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset ι)
    (fun i => ‖centeredCharacter W t₀ (x i)‖)
    (fun i => ‖centeredCharacter W t₀ (x i)‖^2)
  have hp (i : ι) : ‖centeredCharacter W t₀ (x i)‖*‖centeredCharacter W t₀ (x i)‖^2 =
      ‖centeredCharacter W t₀ (x i)‖^3 := by ring
  simp only [hp,← pow_mul,show (2:ℕ)*2=4 by norm_num] at hcs
  have hmul := mul_le_mul h2 h4 (sum_nonneg (fun _ _ => by positivity)) (by positivity : 0 ≤ 128*D*(W.card:ℝ))
  have hsq := Real.sq_sqrt (Nat.cast_nonneg W.card : (0:ℝ) ≤ W.card)
  have hsqE := Real.sq_sqrt (Nat.cast_nonneg (discreteAdditiveEnergy W) : (0:ℝ) ≤ discreteAdditiveEnergy W)
  have hbound : (∑ i, ‖centeredCharacter W t₀ (x i)‖^3)^2 ≤
      (512*D*Real.sqrt (W.card:ℝ)*Real.sqrt (discreteAdditiveEnergy W:ℝ))^2 := by
    calc
      _ ≤ (128*D*(W.card:ℝ))*(1024*D*(discreteAdditiveEnergy W:ℝ)) := hcs.trans hmul
      _ ≤ _ := by
        rw [mul_pow,mul_pow,mul_pow,hsq,hsqE]
        nlinarith [mul_nonneg (sq_nonneg D) (mul_nonneg (Nat.cast_nonneg W.card)
          (Nat.cast_nonneg (discreteAdditiveEnergy W)))]
  have hr : (∑ i, ‖centeredCharacter W t₀ (x i)‖^3) ≤
      512*D*Real.sqrt (W.card:ℝ)*Real.sqrt (discreteAdditiveEnergy W:ℝ) := by
    have hpos : 0 ≤ 512*D*Real.sqrt (W.card:ℝ)*Real.sqrt (discreteAdditiveEnergy W:ℝ) := by positivity
    nlinarith
  convert hr using 1
  dsimp [D]
  ring

end Montgomery.RationalMoment
