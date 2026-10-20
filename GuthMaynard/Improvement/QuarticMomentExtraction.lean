module
public import GuthMaynard.Improvement.SourceQuarticTail
public import GuthMaynard.Improvement.QuarticCellGeometry
public import GuthMaynard.Improvement.TruncatedSourceAttachment

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- Multiplying the actual truncated square by a translated fixed weight is L1. -/
theorem quartic_truncated_weight_integrable {N T : ℝ} (hN : 2 ≤ N) (hT : 0 < T)
    (a : ℕ → ℂ) (ha : ∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) (U w : ℝ) :
    let μ := sourceTruncatedDensity (fun t => fixedTimeCutoff (t/T)) (boundedPolynomial N a) U
    Integrable (fun t => sourceQuarticWeight (t-w)*μ t^2) := by
  obtain ⟨_,_,hi,_,_,_⟩ := fixed_truncated_source_regular hN hT a ha U
  obtain ⟨C,_,hC⟩ := source_quartic_weight_decay 0
  have hh := hi.mul_bdd (g := fun t => ‖sourceReproducingKernel (t-w)‖) (sourceReproducingKernel.continuous.comp
    (continuous_id.sub continuous_const)).norm.aestronglyMeasurable (c := C) ?_
  · simpa only [mul_comm,sourceQuarticWeight] using hh
  · filter_upwards with t
    simpa [sourceQuarticWeight] using hC (t-w)

/-- The exact good-cell geometry attaches the actual truncated density to the
quartic reproducing integral. The tail remains a literal integral. -/
theorem quartic_good_integral {N T R U w : ℝ} (hN : 2 ≤ N) (hT : 0 < T)
    (hRT : R ≤ T) (a : ℕ → ℂ) (ha : ∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1)
    (W : Finset ℝ) (hw : w ∈ Icc (0:ℝ) T) (hwW : w ∈ W)
    (hg : w ∉ quarticDeleted W (occupiedRealCells
      ({x | U < ‖boundedPolynomial N a x‖} ∩ Icc (-T) (2*T)) (-T) (2*T)) R) :
    let μ := sourceTruncatedDensity (fun t => fixedTimeCutoff (t/T)) (boundedPolynomial N a) U
    (∫ t, sourceQuarticWeight (t-w)*‖boundedPolynomial N a t‖^4) ≤
      (∫ t, sourceQuarticWeight (t-w)*μ t^2) +
      ∫ t in {t : ℝ | R < |t-w|}, sourceQuarticWeight (t-w)*‖boundedPolynomial N a t‖^4 := by
  dsimp only
  have hmeas : MeasurableSet {t : ℝ | R < |t-w|} := by measurability
  rw [← integral_indicator hmeas,← integral_add
    (quartic_truncated_weight_integrable hN hT a ha U w)
    ((source_quartic_weighted_integrable N a w 4).indicator hmeas)]
  apply integral_mono (source_quartic_weighted_integrable N a w 4)
    ((quartic_truncated_weight_integrable hN hT a ha U w).add
      ((source_quartic_weighted_integrable N a w 4).indicator hmeas))
  intro t
  simp only [Pi.add_apply]
  by_cases ht : R < |t-w|
  · simp only [indicator_of_mem (show t ∈ {t : ℝ | R < |t-w|} from ht)]
    have h0 : 0 ≤ sourceQuarticWeight (t-w)*
      (sourceTruncatedDensity (fun t => fixedTimeCutoff (t/T)) (boundedPolynomial N a) U t)^2 :=
      mul_nonneg (norm_nonneg _) (sq_nonneg _)
    linarith
  · obtain ⟨hlo,hcut⟩ := quartic_good_neighborhood hT hRT hw a W hwW hg (le_of_not_gt ht)
    simp [ht,sourceTruncatedDensity,hlo,hcut,← pow_mul]

/-- Conditional extraction at the actual moment level. The only analytic input
is the displayed truncated fourth moment; radius smallness is an explicit scalar
condition. Deletion is charged by the actual occupied-cell cardinality. -/
theorem quartic_moment_extraction (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N T R U V M : ℝ,
      2 ≤ N → 0 < T → 0 < R → R ≤ T → 0 < V →
      C*N^4/R^q ≤ V^4/2 →
      ∀ (a : ℕ → ℂ) (W : Finset ℝ),
      (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
      MathCollab.Density.oneSeparated W → (∀ w ∈ W, w ∈ Icc (0:ℝ) T) →
      (∀ w ∈ W, V ≤ ‖boundedPolynomial N a w‖) →
      (∫ t, (sourceTruncatedDensity (fun t => fixedTimeCutoff (t/T))
        (boundedPolynomial N a) U t)^2) ≤ M →
      (W.card:ℝ) ≤ (2*R+3)*((occupiedRealCells
        ({x | U < ‖boundedPolynomial N a x‖} ∩ Icc (-T) (2*T)) (-T) (2*T)).card:ℝ)
        +C*M/V^4 := by
  obtain ⟨B,hB,hb⟩ := source_quartic_weight_overlap
  obtain ⟨D,hD,hd⟩ := source_quartic_polynomial_tail q
  let A := (∫ t, sourceQuarticWeight t)^3
  have hA : 0 ≤ A := pow_nonneg (integral_nonneg (fun _ => norm_nonneg _)) _
  let C := 2*A*B+A*D+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro N T R U V M hN hT hR hRT hV hsmall a W ha hsep hw hv hM
  classical
  let μ := sourceTruncatedDensity (fun t => fixedTimeCutoff (t/T)) (boundedPolynomial N a) U
  let K := occupiedRealCells ({x | U < ‖boundedPolynomial N a x‖} ∩ Icc (-T) (2*T)) (-T) (2*T)
  let Z := quarticDeleted W K R
  let G := W \ Z
  have hGW : G ⊆ W := Finset.sdiff_subset
  have hGsep : MathCollab.Density.oneSeparated G := fun x hx y hy => hsep x (hGW hx) y (hGW hy)
  have hμi : Integrable (fun t => μ t^2) := (fixed_truncated_source_regular hN hT a ha U).2.2.1
  have hM0 : 0 ≤ M := (integral_nonneg (fun t => sq_nonneg (μ t))).trans hM
  have hiw (w : ℝ) : Integrable (fun t => sourceQuarticWeight (t-w)*μ t^2) :=
    quartic_truncated_weight_integrable hN hT a ha U w
  have hsum : (∑ w ∈ G, ∫ t, sourceQuarticWeight (t-w)*μ t^2) ≤ B*M := by
    rw [← integral_finsetSum G (fun w _ => hiw w)]
    calc
      _ ≤ ∫ t, B*μ t^2 := by
        apply integral_mono (integrable_finsetSum G (fun w _ => hiw w)) (hμi.const_mul B)
        intro t
        dsimp only
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (hb G hGsep t) (sq_nonneg _)
      _ = B*(∫ t, μ t^2) := integral_const_mul _ _
      _ ≤ B*M := mul_le_mul_of_nonneg_left hM hB.le
  have hone (w : ℝ) (hg : w ∈ G) :
      V^4 ≤ A*(∫ t, sourceQuarticWeight (t-w)*μ t^2)+A*D*N^4/R^q := by
    have hrep := boundedPolynomial_quartic_reproduce (show 0 < N by linarith) a w
    have hnear := quartic_good_integral hN hT hRT a ha W (hw w (hGW hg)) (hGW hg)
      (Finset.mem_sdiff.mp hg).2
    have htail := hd N R w hN hR a ha
    have hv4 := pow_le_pow_left₀ hV.le (hv w (hGW hg)) 4
    have hh := mul_le_mul_of_nonneg_left (hnear.trans (add_le_add_right htail _)) hA
    dsimp only [A,μ] at hh ⊢
    convert (hv4.trans hrep).trans hh using 1; ring
  have hall := Finset.sum_le_sum hone
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum] at hall
  have hs := mul_le_mul_of_nonneg_left hsum hA
  have hsmall' : A*D*N^4/R^q ≤ V^4/2 := by
    apply le_trans _ hsmall
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    dsimp [C]
    nlinarith
  have hcount : (G.card:ℝ)*V^4 ≤ 2*A*B*M := by
    have ht := mul_le_mul_of_nonneg_left hsmall' (show 0 ≤ (G.card:ℝ) by positivity)
    nlinarith
  have hcount' : (G.card:ℝ) ≤ C*M/V^4 := by
    apply (le_div_iff₀ (pow_pos hV 4)).mpr
    have hc : 2*A*B ≤ C := by dsimp [C]; nlinarith
    exact hcount.trans (mul_le_mul_of_nonneg_right hc hM0)
  have hz := quarticDeleted_card hsep K hR.le
  have he : (G.card:ℝ)+(Z.card:ℝ)=(W.card:ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card (quarticDeleted_subset W K R)
  dsimp only [K] at hz
  linarith

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.quartic_truncated_weight_integrable
#print axioms GuthMaynard.Improvement.quartic_good_integral
#print axioms GuthMaynard.Improvement.quartic_moment_extraction
