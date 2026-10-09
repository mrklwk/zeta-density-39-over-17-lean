import GuthMaynard.Improvement.ShortDetectorNormalization

open Real Complex Set Filter MathCollab.Density
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

def shortDetectorHeightConstant : ℝ := 2^100*100*60^100

/-- Explicit height after powering and splitting; all losses are absolute or
logarithmic, and no dependence on beta or the zero enters the coefficients. -/
theorem exists_shortPoweredDetector_height {T σ t : ℝ} {N j k : ℕ}
    (hlog : 1 ≤ Real.log T) (hN : 0 < N) (_hσ : 0 ≤ σ) (hσ' : σ ≤ 1)
    (hk : 0 < k) (hk' : k ≤ 100)
    (hD : (N : ℝ)^σ/(60*Real.log T) ≤ ‖shortDetectorTaylorPolynomial T N j t‖) :
    ∃ ℓ ∈ Finset.range k,
      (((2^ℓ*N^k : ℕ) : ℝ)^σ)/(shortDetectorHeightConstant*(Real.log T)^100) ≤
        ‖detectingPolynomial (2^ℓ*N^k) (shortPoweredDetectorCoefficient T N j k) t‖ := by
  obtain ⟨ℓ, hℓ, hh⟩ := exists_shortPoweredDetector_piece hN hk T t j
  refine ⟨ℓ, hℓ, ?_⟩
  have hlogpos : 0 < Real.log T := by linarith
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hkfour : (k : ℝ) ≤ 100 := by exact_mod_cast hk'
  have hℓthree : ℓ ≤ 100 := by have := Finset.mem_range.mp hℓ; omega
  have htwo : (2 : ℝ)^ℓ ≤ 2^100 := by
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hℓthree
    norm_num at hh ⊢
    exact hh
  have hscale : (((2^ℓ*N^k : ℕ) : ℝ)^σ) ≤ 2^100*((N : ℝ)^σ)^k := by
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast_mul (Nat.cast_nonneg N),
      mul_comm (k : ℝ) σ, Real.rpow_mul_natCast (Nat.cast_nonneg N)]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact (Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) hσ').trans
      (by simpa only [Real.rpow_one] using htwo)
  have hden : (k : ℝ)*(60*Real.log T)^k ≤ 100*60^100*(Real.log T)^100 := by
    have hp := pow_le_pow_right₀ (show (1 : ℝ) ≤ 60*Real.log T by linarith) hk'
    have hm := mul_le_mul hkfour hp (by positivity) (by norm_num)
    simpa only [mul_pow, mul_assoc] using hm
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (N : ℝ)^σ/(60*Real.log T)) hD k
  calc
    _ ≤ (2^100*((N : ℝ)^σ)^k)/(shortDetectorHeightConstant*(Real.log T)^100) :=
      div_le_div_of_nonneg_right hscale (by unfold shortDetectorHeightConstant; positivity)
    _ = ((N : ℝ)^σ)^k/(100*60^100*(Real.log T)^100) := by unfold shortDetectorHeightConstant; ring
    _ ≤ ((N : ℝ)^σ)^k/((k : ℝ)*(60*Real.log T)^k) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = ((N : ℝ)^σ/(60*Real.log T))^k/(k : ℝ) := by rw [div_pow]; ring
    _ ≤ ‖shortDetectorTaylorPolynomial T N j t‖^k/(k : ℝ) :=
      div_le_div_of_nonneg_right hpow hkpos.le
    _ ≤ _ := hh

/-- The fixed logarithmic loss costs any positive power of T. -/
theorem shortDetectorHeightConstant_eventually {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, shortDetectorHeightConstant*(Real.log T)^100 ≤ T^η := by
  have hl := (isLittleO_log_rpow_rpow_atTop (100 : ℝ) hη).tendsto_div_nhds_zero
  norm_num at hl
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    hl.eventually (gt_mem_nhds (show (0 : ℝ) < 1/shortDetectorHeightConstant by unfold shortDetectorHeightConstant; positivity))]
    with T hT hh
  have hb := (div_lt_iff₀ (by positivity : 0 < T^η)).mp hh
  have hc : 0 < shortDetectorHeightConstant := by unfold shortDetectorHeightConstant; positivity
  have hm := mul_le_mul_of_nonneg_left hb.le hc.le
  calc
    _ ≤ shortDetectorHeightConstant*((1/shortDetectorHeightConstant)*T^η) := hm
    _ = _ := by field_simp

/-- Normalizing by T^eta and absorbing the actual logarithmic loss gives
precisely L^sigma*T^(-2eta), as required by the epsilon budget. -/
theorem exists_shortNormalizedPowered_height {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, ∀ (σ t : ℝ) (N j k : ℕ),
      0 < N → 0 ≤ σ → σ ≤ 1 → 0 < k → k ≤ 100 →
      (N : ℝ)^σ/(60*Real.log T) ≤ ‖shortDetectorTaylorPolynomial T N j t‖ →
      ∃ ℓ ∈ Finset.range k,
        (((2^ℓ*N^k : ℕ) : ℝ)^σ)*T^(-2*η) ≤
          ‖detectingPolynomial (2^ℓ*N^k) (shortNormalizedPoweredCoefficient η T N j k) t‖ := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1,
    shortDetectorHeightConstant_eventually hη] with T hT hlog hc
  intro σ t N j k hN hσ hσ' hk hk' hD
  obtain ⟨ℓ, hℓ, hh⟩ := exists_shortPoweredDetector_height hlog hN hσ hσ' hk hk' hD
  refine ⟨ℓ, hℓ, ?_⟩
  have hTpos : 0 < T := by linarith
  have hden : 0 < shortDetectorHeightConstant*(Real.log T)^100 := by
    unfold shortDetectorHeightConstant
    positivity
  rw [detectingPolynomial_shortNormalizedPowered, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hTpos η)]
  calc
    _ = (((2^ℓ*N^k : ℕ) : ℝ)^σ)/T^η/T^η := by
      rw [div_div, ← Real.rpow_add hTpos, div_eq_mul_inv, ← Real.rpow_neg hTpos.le]
      congr 1
      congr 1
      ring
    _ ≤ ((((2^ℓ*N^k : ℕ) : ℝ)^σ)/(shortDetectorHeightConstant*(Real.log T)^100))/T^η := by
      exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_left (by positivity) hden hc) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_right hh (by positivity)

end GuthMaynard.Improvement

#print axioms GuthMaynard.Improvement.exists_shortPoweredDetector_height
#print axioms GuthMaynard.Improvement.shortDetectorHeightConstant_eventually
#print axioms GuthMaynard.Improvement.exists_shortNormalizedPowered_height
