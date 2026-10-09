import GuthMaynard.Improvement.ShortDetectorBlockExpansion
import GuthMaynard.Improvement.ShortDetectorFamilyScales

open Complex Set Filter MathCollab.Density
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- This finite set depends on T alone, before any zero is selected. -/
def fixedShortDetectorIndices (T : ℝ) : Finset (ℕ × ℕ) :=
  (Finset.range (shortDetectorDyadicCount T)).product (Finset.range (detectorTaylorCutoff T+1))

theorem fixedShortDetectorIndices_card_le {T : ℝ}
    (hlog : 0 ≤ Real.log T)
    (hD : (shortDetectorDyadicCount T : ℝ) ≤ 5*Real.log T)
    (hJ : (detectorTaylorCutoff T+1 : ℝ) ≤ 12*Real.log T) :
    ((fixedShortDetectorIndices T).card : ℝ) ≤ 60*(Real.log T)^2 := by
  have h := mul_le_mul hD hJ (by positivity) (by positivity)
  calc
    _ = (shortDetectorDyadicCount T : ℝ)*((detectorTaylorCutoff T : ℝ)+1) := by simp [fixedShortDetectorIndices]
    _ ≤ (5*Real.log T)*(12*Real.log T) := h
    _ = _ := by ring

/-- Quantitative tail control at the actual family cutoff. -/
theorem norm_fixedShortDetector_tail_le {T : ℝ} {N : ℕ} {ρ : ℂ}
    (hT : 1 ≤ T) (hN : 0 < N) (hN' : (N : ℝ) ≤ T^2)
    (hβ : 0 ≤ ρ.re) (hβ' : ρ.re ≤ 1) :
    ‖∑' j : ℕ, (detectorTaylorWeight ρ.re (j+(detectorTaylorCutoff T+1)) : ℂ)*
      shortDetectorTaylorPolynomial T N (j+(detectorTaylorCutoff T+1)) ρ.im‖ ≤ 3*T^(-1 : ℝ) := by
  have hTpos : 0 < T := by linarith
  have hp : (1/3 : ℝ)^(detectorTaylorCutoff T+1) ≤ T^(-5 : ℝ) := by
    have hh : (1/3 : ℝ)^(detectorTaylorCutoff T+1) ≤ (1/3 : ℝ)^(detectorTaylorCutoff T) := by
      rw [pow_succ]
      nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1/3 by norm_num) (detectorTaylorCutoff T)]
    exact hh.trans (detectorTaylorCutoff_geometric_le hT)
  calc
    _ ≤ 3*(N : ℝ)^2*(1/3 : ℝ)^(detectorTaylorCutoff T+1) :=
      norm_shortDetectorTaylor_tail_le hTpos hN hβ hβ' _ _
    _ ≤ 3*(T^2)^2*T^(-5 : ℝ) := by gcongr
    _ = 3*T^(-1 : ℝ) := by
      rw [show (T^2)^2 = T^4 by ring, ← Real.rpow_natCast T 4, mul_assoc, ← Real.rpow_add hTpos]
      norm_num

/-- The fixed family has the full block height, up to an absolute constant. -/
theorem exists_fixedShortDetector_component {T : ℝ} {N : ℕ} {ρ : ℂ}
    (hT : 1 ≤ T) (hN : 0 < N) (hN' : (N : ℝ) ≤ T^2)
    (hβ : 0 ≤ ρ.re) (hβ' : ρ.re ≤ 1)
    (hsmall : 3*T^(-1 : ℝ) ≤ 1/(6*(shortDetectorDyadicCount T : ℝ)))
    (hblock : 1/(3*(shortDetectorDyadicCount T : ℝ)) ≤ ‖shortDetectorBlock ρ T N‖) :
    ∃ j ∈ Finset.range (detectorTaylorCutoff T+1),
      (N : ℝ)^ρ.re/(12*(shortDetectorDyadicCount T : ℝ)) ≤ ‖shortDetectorTaylorPolynomial T N j ρ.im‖ := by
  let D : ℝ := shortDetectorDyadicCount T
  let J := detectorTaylorCutoff T
  let W := fun j : ℕ => (detectorTaylorWeight ρ.re j : ℂ)*shortDetectorTaylorPolynomial T N j ρ.im
  have hD : 0 < D := by dsimp [D, shortDetectorDyadicCount]; positivity
  have hp : 1 ≤ (N : ℝ)^ρ.re := Real.one_le_rpow (by exact_mod_cast hN) hβ
  have hfull := norm_shortDetectorTaylor_tsum_ge hN hβ T
  have ht := (norm_fixedShortDetector_tail_le hT hN hN' hβ hβ').trans hsmall
  have hs := (hasSum_shortDetectorTaylorPolynomial hN ρ T).summable.sum_add_tsum_nat_add (J+1)
  have hnorm : ‖∑' j, W j‖ ≤ ‖∑ j ∈ Finset.range (J+1), W j‖ + ‖∑' j, W (j+(J+1))‖ := by
    change (∑ j ∈ Finset.range (J+1), W j)+(∑' j, W (j+(J+1))) = (∑' j, W j) at hs
    rw [← hs]
    exact norm_add_le _ _
  have hpartial : (N : ℝ)^ρ.re/(6*D) ≤ ‖∑ j ∈ Finset.range (J+1), W j‖ := by
    have hb := mul_le_mul_of_nonneg_left hblock (Real.rpow_nonneg (Nat.cast_nonneg N) ρ.re)
    have ht' : ‖∑' j, W (j+(J+1))‖ ≤ (N : ℝ)^ρ.re/(6*D) := by
      exact ht.trans ((div_le_div_iff_of_pos_right (by positivity)).mpr hp)
    change (N : ℝ)^ρ.re*‖shortDetectorBlock ρ T N‖ ≤ ‖∑' j, W j‖ at hfull
    change (N : ℝ)^ρ.re*(1/(3*D)) ≤ _ at hb
    have halg : (N : ℝ)^ρ.re*(1/(3*D)) = 2*((N : ℝ)^ρ.re/(6*D)) := by ring
    rw [halg] at hb
    linarith
  obtain ⟨j, hj, hlarge⟩ := exists_large_taylor_component hβ hβ' J (shortDetectorTaylorPolynomial T N · ρ.im)
  refine ⟨j, hj, ?_⟩
  have hh := div_le_div_of_nonneg_right hpartial (by norm_num : (0 : ℝ) ≤ 2)
  change ‖∑ j ∈ Finset.range (J+1), W j‖/2 ≤ _ at hlarge
  exact (show (N : ℝ)^ρ.re/(12*D) = ((N : ℝ)^ρ.re/(6*D))/2 by ring).trans_le (hh.trans hlarge)

/-- Actual short finite detection gives a member of a fixed coefficient family.
The family and its logarithmic size are chosen before beta or gamma. -/
theorem shortFiniteDetector_fixed_family_eventually :
    ∀ᶠ T : ℝ in atTop,
      ((fixedShortDetectorIndices T).card : ℝ) ≤ 60*(Real.log T)^2 ∧
      ∀ (σ : ℝ) (ρ : ℂ), 0 ≤ σ → σ ≤ ρ.re → ρ.re ≤ 1 →
        1/3 ≤ ‖shortFiniteDetector ρ T‖ →
        ∃ p ∈ fixedShortDetectorIndices T,
          T^((100:ℝ)⁻¹) < ((2^p.1 : ℕ) : ℝ) ∧
          ((2^p.1 : ℕ) : ℝ) < T^(1/2:ℝ)*(Real.log T)^2 ∧
          ((2^p.1 : ℕ) : ℝ)^σ/(60*Real.log T) ≤
            ‖shortDetectorTaylorPolynomial T (2^p.1) p.2 ρ.im‖ := by
  filter_upwards [short_detector_family_scales_eventually] with T hsc
  obtain ⟨hT, hlog, hK, hD, hJ, hsmall⟩ := hsc
  refine ⟨fixedShortDetectorIndices_card_le (by linarith) hD hJ, ?_⟩
  intro σ ρ hσ hσβ hβ' hlarge
  obtain ⟨r, hr, hblock⟩ := exists_short_detector_dyadic_block (by linarith : 1 ≤ T)
    (by norm_num : (0 : ℝ) < 1/3) hlarge
  let N : ℕ := 2^r
  have hN : 0 < N := by dsimp [N]; positivity
  have hDpos : (0 : ℝ) < shortDetectorDyadicCount T := by unfold shortDetectorDyadicCount; positivity
  have hb : 1/(3*(shortDetectorDyadicCount T : ℝ)) ≤ ‖shortDetectorBlock ρ T N‖ := by
    convert hblock using 1; ring
  have hbn : shortDetectorBlock ρ T N ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hb)
  obtain ⟨hlo, hhi⟩ := shortDetectorBlock_scale_bounds (by linarith : 0 < T) hbn
  have hN' : (N : ℝ) ≤ T^2 := hhi.le.trans ((Nat.le_ceil _).trans hK)
  obtain ⟨j, hj, hdetect⟩ := exists_fixedShortDetector_component (by linarith : 1 ≤ T) hN hN'
    (hσ.trans hσβ) hβ' hsmall hb
  refine ⟨(r,j), Finset.mem_product.mpr ⟨hr, hj⟩, hlo, hhi, ?_⟩
  have hp : (N : ℝ)^σ ≤ (N : ℝ)^ρ.re := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hσβ
  have hden : 12*(shortDetectorDyadicCount T : ℝ) ≤ 60*Real.log T := by linarith
  change (N : ℝ)^σ/(60*Real.log T) ≤ _
  exact (div_le_div_of_nonneg_left (by positivity) (by positivity) hden).trans
    ((div_le_div_of_nonneg_right hp (by positivity)).trans hdetect)

end GuthMaynard.Improvement

#print axioms GuthMaynard.Improvement.fixedShortDetectorIndices_card_le
#print axioms GuthMaynard.Improvement.norm_fixedShortDetector_tail_le
#print axioms GuthMaynard.Improvement.exists_fixedShortDetector_component
#print axioms GuthMaynard.Improvement.shortFiniteDetector_fixed_family_eventually
