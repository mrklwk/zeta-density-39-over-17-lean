module
public import DensityWindowBudgets

@[expose] public section

open Real Complex Set Filter Finset MathCollab.Density GuthMaynard.Improvement
open scoped BigOperators Topology
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 1200000
noncomputable section
namespace Montgomery.RationalMoment

/-- Uniform logarithmic buffer for the entire compact target exponent range. -/
theorem two_term_power_buffer_eventually :
    ∀ᶠ T : ℝ in atTop, ∀ a : ℝ, 7/10 ≤ a → a ≤ 4/5 →
      T*(Real.log T)^4 ≤ T^(3*a/2) ∧
      (2:ℝ)^100*T^(3*a/2) ≤ T^2 := by
  have hl := (isLittleO_log_rpow_rpow_atTop (4:ℝ) (show (0:ℝ)<1/20 by norm_num)).tendsto_div_nhds_zero
  norm_num at hl
  filter_upwards [eventually_ge_atTop (1:ℝ),
    hl.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),
    (tendsto_rpow_atTop (show (0:ℝ)<4/5 by norm_num)).eventually_ge_atTop ((2:ℝ)^100)]
    with T hT hlog hconst
  intro a ha ha'
  have ht : 0 < T := by linarith
  constructor
  · have hb : (Real.log T)^4 ≤ T^(1/20:ℝ) :=
      ((div_lt_one (by positivity)).mp hlog).le
    calc
      _ ≤ T*T^(1/20:ℝ) := mul_le_mul_of_nonneg_left hb ht.le
      _ = T^(21/20:ℝ) := by
        nth_rw 1 [← Real.rpow_one T]
        rw [← Real.rpow_add ht]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  · calc
      _ ≤ T^(4/5:ℝ)*T^(3*a/2) := mul_le_mul_of_nonneg_right hconst (by positivity)
      _ = T^((4/5:ℝ)+3*a/2) := by rw [← Real.rpow_add ht]
      _ ≤ T^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
      _ = T^2 := Real.rpow_two T

/-- Actual short detection yields a bounded-coefficient powered family in the
full target window, without moving the ordinate. No counting estimate is assumed. -/
theorem two_term_powered_cover {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop,
      ((shortPoweredDetectorIndices T).card:ℝ) ≤ 600000*(Real.log T)^2 ∧
      ∀ (a σ : ℝ) (ρ : ℂ), 7/10 ≤ a → a ≤ 4/5 →
        0 ≤ σ → σ ≤ ρ.re → ρ.re ≤ 1 → 1/3 ≤ ‖shortFiniteDetector ρ T‖ →
        ∃ p ∈ shortPoweredDetectorIndices T,
          T^a ≤ (shortPoweredDetectorScale p:ℝ) ∧
          (shortPoweredDetectorScale p:ℝ) ≤ (2:ℝ)^99*T^(3*a/2) ∧
          2*(shortPoweredDetectorScale p:ℝ) ≤ T^2 ∧
          (shortPoweredDetectorScale p:ℝ)^σ*T^(-2*η) ≤
            ‖detectingPolynomial (shortPoweredDetectorScale p)
              (shortPoweredDetectorFamilyCoeff η T p) ρ.im‖ := by
  filter_upwards [eventually_gt_atTop (1:ℝ), shortFiniteDetector_fixed_family_eventually,
    two_term_power_buffer_eventually, exists_shortNormalizedPowered_height hη]
    with T hT hf hb hh
  refine ⟨shortPoweredDetectorIndices_card_le hf.1, ?_⟩
  intro a σ ρ ha ha' hσ hσβ hβ hlarge
  obtain ⟨q,hq,hlo,hhi,hd⟩ := hf.2 σ ρ hσ hσβ hβ hlarge
  obtain ⟨k,hk,hk100,hklo,hkhi⟩ := short_detector_power_exists hT
    (by linarith) (by linarith) hlo hhi.le (hb a ha ha').1
  obtain ⟨ℓ,hℓ,hheight⟩ := hh σ ρ.im (2^q.1) q.2 k (by positivity)
    hσ (hσβ.trans hβ) hk hk100 hd
  have hs := short_detector_power_piece_bounds hk100 (Finset.mem_range.mp hℓ)
    hklo hkhi (hb a ha ha').2
  refine ⟨(q,(k,ℓ)), Finset.mem_product.mpr ⟨hq, Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨hk,hk100⟩, Finset.mem_range.mpr (by change ℓ < 100; have := Finset.mem_range.mp hℓ; omega)⟩⟩,
    hs.1, hs.2.1, hs.2.2, hheight⟩



end Montgomery.RationalMoment
