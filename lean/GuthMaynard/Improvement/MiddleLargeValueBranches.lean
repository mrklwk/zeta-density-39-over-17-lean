import GuthMaynard.Improvement.MiddleRangeIdentities
import GuthMaynard.Improvement.ClassicalLargeValues
set_option autoImplicit false
noncomputable section
open Set
namespace GuthMaynard.Improvement

/-- The fixed truncation threshold lies below the source length throughout
the full middle range; it is not changed by the operator's factor-five rescaling. -/
theorem middle_threshold_le_length {N T : ℝ} (hN : 2 ≤ N)
    (hlo : N^((6:ℝ)/5) ≤ T) (hhi : T ≤ N^((5:ℝ)/3)) :
    middleThreshold N T ≤ N := by
  obtain ⟨hNT,hTN⟩ := middle_time_bounds hN hlo hhi
  have hn : 0 < N := by linarith
  have ht : 0 ≤ T := by linarith
  unfold middleThreshold
  have hh := Real.rpow_le_rpow ht hTN (by norm_num : (0:ℝ) ≤ 1/14)
  rw [← Real.rpow_natCast N 2, ← Real.rpow_mul hn.le] at hh
  norm_num at hh
  calc
    _ ≤ N^((5:ℝ)/7)*N^((1:ℝ)/7) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = N^((6:ℝ)/7) := by rw [← Real.rpow_add hn]; norm_num
    _ ≤ N^((1:ℝ)) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    _ = N := Real.rpow_one _

/-- Above the fixed threshold, the classical sixth-power contribution is
bounded by the desired middle-range fourth-power contribution. -/
theorem middle_high_threshold_budget {N T V : ℝ} (hn : 0 < N) (ht : 0 < T)
    (hV : middleThreshold N T ≤ V) :
    T*N^4/V^6 ≤ middleMoment N T/V^4 := by
  have hu : 0 < middleThreshold N T := by unfold middleThreshold; positivity
  have hv : 0 < V := hu.trans_le hV
  have hs : (middleThreshold N T)^2 ≤ V^2 := pow_le_pow_left₀ hu.le hV 2
  have hh : T*N^4/V^2 ≤ T*N^4/(middleThreshold N T)^2 := by gcongr
  rw [middle_threshold_square_quotient hn ht] at hh
  calc
    _ = (T*N^4/V^2)/V^4 := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hh (by positivity)

/-- Actual high-threshold branch on every translated interval, with no
classical large-values estimate left as a premise. -/
theorem middle_large_values_high {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N T V t₀ : ℝ,
      2 ≤ N → N^((6:ℝ)/5) ≤ T → T ≤ N^((5:ℝ)/3) →
      middleThreshold N T ≤ V → ∀ (a : ℕ → ℂ) (W : Finset ℝ),
      (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
      (∀ t ∈ W, t ∈ Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, V ≤ ‖boundedPolynomial N a t‖) →
      (W.card:ℝ) ≤ C*N^ε*(N^2/V^2+middleMoment N T/V^4) := by
  obtain ⟨C,hC,h⟩ := classical_large_values hε
  refine ⟨C,hC,?_⟩
  intro N T V t₀ hN hlo hhi hV a W ha hloc hsep hlarge
  obtain ⟨hNT,hTN⟩ := middle_time_bounds hN hlo hhi
  have hn : 0 < N := by linarith
  have ht : 0 < T := by linarith
  have hu : 0 < middleThreshold N T := by unfold middleThreshold; positivity
  have hv : 0 < V := hu.trans_le hV
  exact (h N T V t₀ hN hNT hTN hv a W ha hloc hsep hlarge).trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl (middle_high_threshold_budget hn ht hV))
      (by positivity))

/-- Small thresholds require only packing. This stronger branch does not
assume any polynomial or large-value property. -/
theorem middle_large_values_small {N T V t₀ : ℝ} (hN : 2 ≤ N)
    (hT : 0 ≤ T) (hTN : T ≤ N^2) (hV : 0 < V) (hV1 : V < 1)
    (W : Finset ℝ) (hloc : ∀ t ∈ W, t ∈ Icc t₀ (t₀+T))
    (hsep : ∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) :
    (W.card:ℝ) ≤ 2*N^2/V^2 := by
  have hspan := MathCollab.Density.intervalSpan_le_of_forall hT (U := W) (by
    intro t ht u hu
    have ht' := hloc t ht
    have hu' := hloc u hu
    exact abs_le.mpr ⟨by linarith [ht'.1,hu'.2],by linarith [hu'.1,ht'.2]⟩)
  have hc := MathCollab.Density.separated_card_le_localDiameter hsep
  have hpack : (W.card:ℝ) ≤ T+1 := by
    dsimp [MathCollab.Density.localDiameter] at hc
    linarith
  have hN2 : 1 ≤ N^2 := by nlinarith
  have hVs : V^2 ≤ 1 := by nlinarith
  calc
    _ ≤ T+1 := hpack
    _ ≤ 2*N^2 := by linarith
    _ ≤ _ := by
      apply (le_div_iff₀ (show 0 < V^2 by positivity)).mpr
      have hh := mul_le_mul_of_nonneg_left hVs (show 0 ≤ 2*N^2 by positivity)
      simpa only [mul_one] using hh

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.middle_threshold_le_length
#print axioms GuthMaynard.Improvement.middle_high_threshold_budget
#print axioms GuthMaynard.Improvement.middle_large_values_high
#print axioms GuthMaynard.Improvement.middle_large_values_small
