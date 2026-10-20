module
public import GuthMaynard.Improvement.QuarticRadiusExtraction
public import GuthMaynard.Improvement.MiddleFourthMoment
public import GuthMaynard.Improvement.MiddleLargeValueBranches

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- The two classical bad-cell terms fit the chosen fourth-moment budget
below the fixed truncation threshold. This is exact scalar scale algebra. -/
theorem middle_low_threshold_budget {N T V : ℝ} (hN : 2 ≤ N)
    (hlo : N^((6:ℝ)/5) ≤ T) (hhi : T ≤ N^((5:ℝ)/3))
    (hV : 0 < V) (hVU : V ≤ middleThreshold N T) :
    N^2/(middleThreshold N T)^2+T*N^4/(middleThreshold N T)^6 ≤
      2*middleMoment N T/V^4 := by
  have hn : 0 < N := by linarith
  have ht : 0 < T := hn.trans_le (middle_time_bounds hN hlo hhi).1
  have hu : 0 < middleThreshold N T := by unfold middleThreshold; positivity
  have hp : 0 < middleMoment N T := by unfold middleMoment; positivity
  have hnl := (middle_length_bounds hN hlo hhi).1
  have hfirst : N^2/(middleThreshold N T)^2 ≤ middleMoment N T/(middleThreshold N T)^4 := by
    calc
      _ ≤ (N*middleLength N T)/(middleThreshold N T)^2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith
      _ = _ := by rw [← middle_length_threshold_identity hn ht]; field_simp
  have hsecond : T*N^4/(middleThreshold N T)^6 = middleMoment N T/(middleThreshold N T)^4 := by
    rw [← middle_threshold_square_quotient hn ht]
    field_simp
  calc
    _ ≤ 2*middleMoment N T/(middleThreshold N T)^4 := by
      convert add_le_add hfirst hsecond.le using 1; ring
    _ ≤ _ := by gcongr

/-- Actual separated large values below the fixed truncation threshold in the
full middle range. All moment, tail, packing and scale estimates are discharged;
there are no analytic estimate premises. -/
theorem middle_large_values_low {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N T V : ℝ,
      2 ≤ N → N^((6:ℝ)/5) ≤ T → T ≤ N^((5:ℝ)/3) →
      1 ≤ V → V ≤ middleThreshold N T →
      ∀ (a : ℕ → ℂ) (W : Finset ℝ),
      (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
      (∀ w ∈ W, w ∈ Icc (0:ℝ) T) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ w ∈ W, V ≤ ‖boundedPolynomial N a w‖) →
      (W.card:ℝ) ≤ C*N^ε*middleMoment N T/V^4 := by
  have hhalf : 0 < ε/2 := by positivity
  obtain ⟨E,hE,he⟩ := quartic_extraction_of_moment hhalf
  obtain ⟨D,hD,hd⟩ := middle_fourth_moment hhalf
  refine ⟨E*(2+D),by positivity,?_⟩
  intro N T V hN hlo hhi hV hVU a W ha hw hsep hv
  obtain ⟨hnt,htn⟩ := middle_time_bounds hN hlo hhi
  have hn : 0 < N := by linarith
  have ht : 0 < T := by linarith
  have hv0 : 0 < V := by linarith
  have hp : 0 ≤ middleMoment N T := by unfold middleMoment; positivity
  have hU : middleThreshold N T ≤ 2*N :=
    (middle_threshold_le_length hN hlo hhi).trans (by linarith)
  have hm := hd N T hN hlo hhi a ha
  have hx := he N T (middleThreshold N T) V (D*N^(ε/2)*middleMoment N T)
    hN hnt htn hV hVU hU a W ha hsep hw hv hm
  have hbudget := middle_low_threshold_budget hN hlo hhi hv0 hVU
  have hpow : 1 ≤ N^(ε/2) := Real.one_le_rpow (by linarith) hhalf.le
  have hid : N^(ε/2)*N^(ε/2)=N^ε := by rw [← Real.rpow_add hn]; congr 1; ring
  calc
    _ ≤ E*N^(ε/2)*(2*middleMoment N T/V^4+D*N^(ε/2)*middleMoment N T/V^4) :=
      hx.trans (mul_le_mul_of_nonneg_left (add_le_add hbudget le_rfl) (by positivity))
    _ ≤ E*N^(ε/2)*(2*N^(ε/2)*middleMoment N T/V^4+D*N^(ε/2)*middleMoment N T/V^4) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add _ le_rfl
      gcongr
      linarith
    _ = E*(2+D)*(N^(ε/2)*N^(ε/2))*middleMoment N T/V^4 := by ring
    _ = _ := by rw [hid]

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.middle_low_threshold_budget
#print axioms GuthMaynard.Improvement.middle_large_values_low
