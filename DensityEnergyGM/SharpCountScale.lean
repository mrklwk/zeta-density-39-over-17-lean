module
public import DensityEnergyGM.SharpCountTraceExpansion

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Montgomery.RationalMoment

theorem gm_amplitude_log_identity {T : ℝ} (hT : 0 < T) (σ x δ : ℝ) :
    (T^x)^σ*T^(-2*δ)=T^(σ*x-2*δ) := by
  rw [← Real.rpow_mul hT.le,← Real.rpow_add hT]
  congr 1
  ring

/-- An admissible actual amplifier length for the entire perturbed
physical detector range; the baseline costs exactly at most10delta. -/
theorem gm_detecting_scale {σ a δ T N : ℝ}
    (hσ : 4/5 ≤ σ) (hσ1 : σ < 1) (ha : 1/2 ≤ a) (ha1 : a < 2/3)
    (hδ : 0 ≤ δ) (hδa : δ ≤ (1-3*a/2)/2) (hT : 1 < T)
    (hlo : T^a ≤ N) (hhi : N ≤ T^(3*a/2+δ)) :
    ∃ x ell : ℝ, T^x=N ∧ a ≤ x ∧ N ≤ T^ell ∧ T^ell ≤ T ∧
      Real.sqrt T ≤ T^ell ∧ 3*a*(1-σ)+(2*σ-1)*x ≤ ell ∧
      (N*T^ell)^2 ≤ T^(10*δ)*(T^(3*a*(1-σ)))^2*(N^σ*T^(-2*δ))^4 := by
  have hTp : 0 < T := by linarith
  have hNp : 0 < N := (Real.rpow_pos_of_pos hTp a).trans_le hlo
  have ht : 0 < Real.log T := Real.log_pos hT
  let x := Real.logb T N
  have hNx : T^x=N := Real.rpow_logb hTp (by linarith) hNp
  have hxa : a ≤ x := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hTp a) hlo
    rw [Real.log_rpow hTp] at hh
    exact (le_div_iff₀ ht).mpr hh
  have hxhi : x ≤ 3*a/2+δ := by
    have hh := Real.log_le_log hNp hhi
    rw [Real.log_rpow hTp] at hh
    exact (div_le_iff₀ ht).mpr hh
  let p := 3*a*(1-σ)
  let ell := max x (p+(2*σ-1)*x)
  have hlx : x ≤ ell := le_max_left _ _
  have hlower : p+(2*σ-1)*x ≤ ell := le_max_right _ _
  have hupper : ell ≤ p+(2*σ-1)*x+δ := by
    apply max_le ?_ (by linarith only [hδ])
    have hm := mul_le_mul_of_nonneg_left hxhi (show 0 ≤ 2*(1-σ) by linarith)
    have hd := mul_nonneg hδ (show 0 ≤ 2*σ-1 by linarith)
    dsimp [p]
    nlinarith only [hm,hd]
  have hell1 : ell ≤ 1 := by
    have hxu : x ≤ 1 := by linarith
    apply max_le hxu
    have hm := mul_le_mul_of_nonneg_left hxhi (show 0 ≤ 2*σ-1 by linarith)
    have hd := mul_nonneg hδ (show 0 ≤ 2-2*σ by linarith)
    dsimp [p]
    nlinarith only [hm,hd,hδa,ha1]
  have hellhalf : (1/2:ℝ) ≤ ell := by
    have hm := mul_le_mul_of_nonneg_left hxa (show 0 ≤ 2*σ-1 by linarith)
    have hh := mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ 1-σ by linarith)
    dsimp [p] at hlower
    nlinarith only [hm,hh,ha,hlower]
  refine ⟨x,ell,hNx,hxa,?_,?_,?_,hlower,?_⟩
  · rw [← hNx]
    exact Real.rpow_le_rpow_of_exponent_le hT.le hlx
  · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT.le hell1
  · rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hT.le hellhalf
  · rw [← hNx,gm_amplitude_log_identity hTp]
    rw [mul_pow]
    repeat rw [← Real.rpow_mul_natCast hTp.le]
    repeat rw [← Real.rpow_add hTp]
    apply Real.rpow_le_rpow_of_exponent_le hT.le
    dsimp [p] at hupper
    norm_num
    linarith only [hupper]

end Montgomery.RationalMoment
