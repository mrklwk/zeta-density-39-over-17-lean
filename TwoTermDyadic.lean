module
public import MathCollab.Density.Stronger.DyadicMoment

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped Interval
namespace Montgomery.CriticalPeak
open MathCollab.Density.Stronger

/-- Two dyadic powers, with a vanishing initial integral, retain uniform constants. -/
theorem integral_zero_le_of_two_dyadic_powers (f : ℝ → ℝ) (hf : Continuous f)
    (hf0 : ∀ t, 0 ≤ f t) {p r B T A D : ℝ}
    (hp : 1 ≤ p) (hr : 1 ≤ r) (hB : 1 ≤ B) (hT : B ≤ T)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hprefix : (∫ t in 0..B,f t)=0)
    (hdyad : ∀ H : ℝ, B ≤ H → H ≤ T →
      (∫ t in H..2*H,f t) ≤ A*H^p+D*H^r) :
    (∫ t in 0..T,f t) ≤ A*(2:ℝ)^p*T^p+D*(2:ℝ)^r*T^r := by
  have hBp : 0 < B := by linarith
  have hTp : 0 < T := hBp.trans_le hT
  have htwoP : (2:ℝ) ≤ (2:ℝ)^p := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hp
  have htwoR : (2:ℝ) ≤ (2:ℝ)^r := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hr
  have hstep : ∀ m : ℕ, (2:ℝ)^m*B ≤ 2*T →
      (∫ t in 0..(2:ℝ)^m*B,f t) ≤ A*((2:ℝ)^m*B)^p+D*((2:ℝ)^m*B)^r := by
    intro m
    induction m with
    | zero =>
      intro _
      simp only [pow_zero,one_mul,hprefix]
      positivity
    | succ m ih =>
      intro hupper
      have hm : B ≤ (2:ℝ)^m*B := by
        have hh : 1 ≤ (2:ℝ)^m := one_le_pow₀ (by norm_num)
        nlinarith
      have hX : 0 ≤ (2:ℝ)^m*B := by positivity
      have heq : (2:ℝ)^(m+1)*B=2*((2:ℝ)^m*B) := by rw [pow_succ']; ring
      rw [heq] at hupper ⊢
      have hXT : (2:ℝ)^m*B ≤ T := by linarith
      have hih := ih (by linarith)
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable 0 ((2:ℝ)^m*B))
        (hf.intervalIntegrable ((2:ℝ)^m*B) (2*((2:ℝ)^m*B)))]
      calc
        _ ≤ (A*((2:ℝ)^m*B)^p+D*((2:ℝ)^m*B)^r)+
            (A*((2:ℝ)^m*B)^p+D*((2:ℝ)^m*B)^r) :=
          add_le_add hih (hdyad _ hm hXT)
        _ = A*2*((2:ℝ)^m*B)^p+D*2*((2:ℝ)^m*B)^r := by ring
        _ ≤ A*(2:ℝ)^p*((2:ℝ)^m*B)^p+D*(2:ℝ)^r*((2:ℝ)^m*B)^r := by
          gcongr
        _ = _ := by
          rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hX,
            Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hX]
          ring
  obtain ⟨m,hlo,hhi⟩ := exists_dyadic_cutoff ((le_div_iff₀ hBp).mpr (by simpa using hT))
  have hlo' : T ≤ (2:ℝ)^m*B := (div_le_iff₀ hBp).mp hlo
  have hhi' : (2:ℝ)^m*B ≤ 2*T := by
    have hh := (mul_le_mul_iff_left₀ hBp).mpr hhi
    field_simp at hh
    nlinarith
  calc
    _ ≤ ∫ t in 0..(2:ℝ)^m*B,f t := by
      apply intervalIntegral.integral_mono_interval le_rfl hTp.le hlo'
      · exact Filter.Eventually.of_forall hf0
      · exact hf.intervalIntegrable _ _
    _ ≤ A*((2:ℝ)^m*B)^p+D*((2:ℝ)^m*B)^r := hstep m hhi'
    _ ≤ A*(2*T)^p+D*(2*T)^r := by gcongr
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hTp.le,
        Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hTp.le]
      ring
end Montgomery.CriticalPeak
