module
public import GuthMaynard.Improvement.ShortDetectorIdentity
public import GuthMaynard.Improvement.ShortDetectorResidue
public import GuthMaynard.Improvement.ShortFiniteDetector

@[expose] public section

open Complex MeasureTheory Set Filter MathCollab.Density
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- Actual zero detection below three quarters. A single eventual height
threshold works for all zeros in the slab, with fixed finite coefficients.
This alternative does not assert a count for either branch. -/
theorem short_detector_eventually_alternative :
    ∀ᶠ H : ℝ in atTop, ∀ ρ : ℂ,
      9/13 ≤ ρ.re → ρ.re < 1 → H ≤ |ρ.im| → |ρ.im| ≤ 2*H →
      riemannZeta ρ = 0 →
      (1/3 : ℝ) ≤ ‖shortFiniteDetector ρ H‖ ∨
      (1/3 : ℝ) ≤ ‖detectorIntegral ρ (2*H^((100:ℝ)⁻¹)) (H^(1/2:ℝ))‖ := by
  have hYlim := (tendsto_rpow_atTop (show (0:ℝ) < 1/2 by norm_num)).eventually
    (eventually_ge_atTop (4:ℝ))
  filter_upwards [eventually_ge_atTop (1:ℝ), hYlim,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4:ℝ)),
    short_detector_tail_eventually_small (show (0:ℝ) < 1/24 by norm_num),
    short_detector_residue_eventually_small (show (0:ℝ) < 1/24 by norm_num)]
    with H hH hY hlog htail hres
  intro ρ hβ hβ' hγ hγ' hzero
  have hYpos : 0 < H^(1/2:ℝ) := by linarith
  have hK : 1 < shortDetectorCutoff H := by
    have hk : H^(1/2:ℝ)*(Real.log H)^2 ≤ (shortDetectorCutoff H:ℝ) := Nat.le_ceil _
    have hs : 16 ≤ (Real.log H)^2 := by nlinarith
    have hr : (1:ℝ) < shortDetectorCutoff H := by nlinarith
    exact_mod_cast hr
  have hd := shortFiniteDetector_decomposition hH hK (show 0 ≤ ρ.re by linarith)
  have hi := short_smoothedDetector_contour_identity
    (X := 2*H^((100:ℝ)⁻¹)) (by linarith : 1 ≤ H^(1/2:ℝ)) hβ hβ' hzero
  change smoothedDetector ρ (2*H^((100:ℝ)⁻¹)) (1/(H^(1/2:ℝ))) =
    detectorResidue ρ (2*H^((100:ℝ)⁻¹)) (H^(1/2:ℝ)) +
    detectorIntegral ρ (2*H^((100:ℝ)⁻¹)) (H^(1/2:ℝ)) at hi
  have hfirst : (3/4:ℝ) ≤ Real.exp (-1/(H^(1/2:ℝ))) := by
    have he := Real.add_one_le_exp (-1/(H^(1/2:ℝ)))
    have hq : 1/(H^(1/2:ℝ)) ≤ (1/4:ℝ) := (div_le_iff₀ hYpos).2 (by linarith)
    rw [neg_div] at he ⊢
    linarith
  have hnorm : ‖(Real.exp (-1/(H^(1/2:ℝ))) : ℂ)‖ ≤
      ‖smoothedDetector ρ (2*H^((100:ℝ)⁻¹)) (1/(H^(1/2:ℝ)))‖ +
      ‖shortFiniteDetector ρ H‖ +
      ‖∑' n : ℕ, detectorTerm ρ (2*H^((100:ℝ)⁻¹)) (H^(1/2:ℝ))
        (n+shortDetectorCutoff H)‖ := by
    have he : (Real.exp (-1/(H^(1/2:ℝ))) : ℂ) =
        smoothedDetector ρ (2*H^((100:ℝ)⁻¹)) (1/(H^(1/2:ℝ))) -
        shortFiniteDetector ρ H -
        (∑' n : ℕ, detectorTerm ρ (2*H^((100:ℝ)⁻¹)) (H^(1/2:ℝ))
          (n+shortDetectorCutoff H)) := by rw [← hd]; ring
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hnorm
  have ht := htail ρ (by linarith)
  have hr := hres ρ hβ hβ'.le hγ hγ'
  have hm : ‖smoothedDetector ρ (2*H^((100:ℝ)⁻¹)) (1/(H^(1/2:ℝ)))‖ ≤
      ‖detectorResidue ρ (2*H^((100:ℝ)⁻¹)) (H^(1/2:ℝ))‖ +
      ‖detectorIntegral ρ (2*H^((100:ℝ)⁻¹)) (H^(1/2:ℝ))‖ := by
    rw [hi]
    exact norm_add_le _ _
  by_contra hn
  push Not at hn
  simp only [one_div] at ht hr hm hnorm hn
  linarith [hn.1, hn.2]

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.short_detector_eventually_alternative
