module
public import GuthMaynard.Improvement.ShortDetectorPoweredHeight

@[expose] public section

open Real Set Filter MathCollab.Density
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- Least-successful powering, allowing all short bases rather than just four powers. -/
theorem short_detector_power_exists {T a : ℝ} {N : ℕ}
    (hT : 1 < T) (ha : 0 < a) (ha' : a ≤ 1)
    (hN : T^((100:ℝ)⁻¹) < N)
    (hN' : (N : ℝ) ≤ T^(1/2:ℝ)*(Real.log T)^2)
    (hbuffer : T*(Real.log T)^4 ≤ T^(3*a/2)) :
    ∃ k : ℕ, 0 < k ∧ k ≤ 100 ∧ T^a ≤ (N : ℝ)^k ∧
      (N : ℝ)^k ≤ T^(3*a/2) := by
  have hTpos : 0 < T := by linarith
  have hNreal : 1 < (N : ℝ) :=
    (Real.one_le_rpow hT.le (by positivity)).trans_lt hN
  have h100 : T^a ≤ (N : ℝ)^100 := by
    have hp := pow_le_pow_left₀ (Real.rpow_nonneg hTpos.le _) hN.le 100
    rw [← Real.rpow_mul_natCast hTpos.le] at hp
    norm_num at hp
    exact (show T^a ≤ T by simpa using Real.rpow_le_rpow_of_exponent_le hT.le ha').trans hp
  have hex : ∃ k : ℕ, T^a ≤ (N : ℝ)^k := ⟨100,h100⟩
  let k := Nat.find hex
  have hk : T^a ≤ (N : ℝ)^k := Nat.find_spec hex
  have hk100 : k ≤ 100 := Nat.find_min' hex h100
  have hkpos : 0 < k := by
    by_contra hh
    have hz : k = 0 := by omega
    rw [hz, pow_zero] at hk
    exact (not_le_of_gt (Real.one_lt_rpow hT ha)) hk
  refine ⟨k,hkpos,hk100,hk,?_⟩
  by_cases hksmall : k ≤ 2
  · have hp : (N : ℝ)^k ≤ (N : ℝ)^2 := pow_le_pow_right₀ hNreal.le hksmall
    have hsq := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ N) hN' 2
    have he : (T^(1/2:ℝ)*(Real.log T)^2)^2 = T*(Real.log T)^4 := by
      rw [mul_pow, ← Real.rpow_mul_natCast hTpos.le]
      norm_num only [Nat.cast_ofNat, show (1/2:ℝ)*2=1 by norm_num, Real.rpow_one]
      ring
    rw [he] at hsq
    exact hp.trans (hsq.trans hbuffer)
  · have hprev : (N : ℝ)^(k-1) < T^a :=
      lt_of_not_ge (Nat.find_min hex (show k-1 < k by omega))
    have hlog := Real.log_lt_log (by positivity : (0:ℝ) < (N:ℝ)^(k-1)) hprev
    rw [Real.log_pow, Real.log_rpow hTpos] at hlog
    have hcast : ((k-1:ℕ):ℝ) = (k:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
    rw [hcast] at hlog
    have hkn : (3:ℝ) ≤ k := by exact_mod_cast (show 3 ≤ k by omega)
    have hln : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg hNreal.le
    have hmul : (k:ℝ)*Real.log (N:ℝ) ≤ 3/2*((k:ℝ)-1)*Real.log (N:ℝ) := by nlinarith
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_pow, Real.log_rpow hTpos]
    nlinarith

/-- Uniform logarithmic buffer for the entire compact target exponent range. -/
theorem short_detector_power_buffer_eventually :
    ∀ᶠ T : ℝ in atTop, ∀ a : ℝ, 3/4 ≤ a → a ≤ 4/5 →
      T*(Real.log T)^4 ≤ T^(3*a/2) ∧
      (2:ℝ)^100*T^(3*a/2) ≤ T^2 := by
  have hl := (isLittleO_log_rpow_rpow_atTop (4:ℝ) (show (0:ℝ)<1/8 by norm_num)).tendsto_div_nhds_zero
  norm_num at hl
  filter_upwards [eventually_ge_atTop (1:ℝ),
    hl.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),
    (tendsto_rpow_atTop (show (0:ℝ)<4/5 by norm_num)).eventually_ge_atTop ((2:ℝ)^100)]
    with T hT hlog hconst
  intro a ha ha'
  have ht : 0 < T := by linarith
  constructor
  · have hb : (Real.log T)^4 ≤ T^(1/8:ℝ) :=
      ((div_lt_one (by positivity)).mp hlog).le
    calc
      _ ≤ T*T^(1/8:ℝ) := mul_le_mul_of_nonneg_left hb ht.le
      _ = T^(9/8:ℝ) := by
        nth_rw 1 [← Real.rpow_one T]
        rw [← Real.rpow_add ht]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  · calc
      _ ≤ T^(4/5:ℝ)*T^(3*a/2) := mul_le_mul_of_nonneg_right hconst (by positivity)
      _ = T^((4/5:ℝ)+3*a/2) := by rw [← Real.rpow_add ht]
      _ ≤ T^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
      _ = T^2 := Real.rpow_two T

/-- Every actual dyadic piece lies in the target window with its explicit fixed margin. -/
theorem short_detector_power_piece_bounds {T a : ℝ} {N k ℓ : ℕ}
    (hk : k ≤ 100) (hℓ : ℓ < k)
    (hlo : T^a ≤ (N:ℝ)^k) (hhi : (N:ℝ)^k ≤ T^(3*a/2))
    (hbuffer : (2:ℝ)^100*T^(3*a/2) ≤ T^2) :
    T^a ≤ ((2^ℓ*N^k:ℕ):ℝ) ∧
      ((2^ℓ*N^k:ℕ):ℝ) ≤ (2:ℝ)^99*T^(3*a/2) ∧
      2*((2^ℓ*N^k:ℕ):ℝ) ≤ T^2 := by
  have htwo : (1:ℝ) ≤ 2^ℓ := one_le_pow₀ (by norm_num)
  have htwo99 : (2:ℝ)^ℓ ≤ 2^99 := pow_le_pow_right₀ (by norm_num) (by omega)
  have htwo100 : (2:ℝ)^(ℓ+1) ≤ 2^100 := pow_le_pow_right₀ (by norm_num) (by omega)
  push_cast
  refine ⟨hlo.trans ?_, ?_, ?_⟩
  · nlinarith [pow_nonneg (Nat.cast_nonneg N : (0:ℝ) ≤ N) k]
  · exact mul_le_mul htwo99 hhi (by positivity) (by positivity)
  · calc
      _ = (2:ℝ)^(ℓ+1)*(N:ℝ)^k := by rw [pow_succ]; ring
      _ ≤ (2:ℝ)^100*T^(3*a/2) := mul_le_mul htwo100 hhi (by positivity) (by positivity)
      _ ≤ _ := hbuffer

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.short_detector_power_exists
#print axioms GuthMaynard.Improvement.short_detector_power_buffer_eventually

#print axioms GuthMaynard.Improvement.short_detector_power_piece_bounds
