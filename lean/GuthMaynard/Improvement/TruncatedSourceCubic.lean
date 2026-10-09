import GuthMaynard.Improvement.TruncatedSourceMeanValue
import GuthMaynard.Improvement.CenteredRestrictedCubic
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- Actual restricted cubic attached to the literal truncated source.
The threshold uses its actual removed mass; no Fourier-tail or moment estimate
is assumed. The support length is 5T, not T. -/
theorem fixed_truncated_source_cubic {ε : ℝ} (hε : 0 < ε) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ N T L : ℝ,
      2 ≤ N → N ≤ T → (5*T)^((4:ℝ)/5) ≤ L → L ≤ 5*T →
      ∀ (a : ℕ → ℂ) (U : ℝ),
      (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
      let μ := sourceTruncatedDensity (fun t => fixedTimeCutoff (t/T))
        (boundedPolynomial N a) U
      let H := ∫ t, sourceRemovedDensity (fun t => fixedTimeCutoff (t/T))
        (boundedPolynomial N a) U t
      let M := ∫ t, μ t^2
      ‖kernelCubic (timeMeasure μ) (centeredKernel
        (fun x => ((MathCollab.Density.comparisonCutoff x^2:ℝ):ℂ)) (1/2) 5 L)‖ ≤
        C*(5*T)^ε*(25*T^2*M*Real.sqrt M+5*T*L*(D*(N^2+H))*M+
          3060*D*N^3*L*T^3*(Real.log (2*N))^2) := by
  have hs : ∀ t, t ∉ Icc (-2:ℝ) 3 → fixedTimeCutoff t=0 := by
    intro t ht
    by_contra hn
    exact ht (fixedTimeCutoff_support (subset_closure hn))
  obtain ⟨D,hD,htail⟩ := boundedPolynomial_source_tail fixedTimeCutoff_smooth
    (fun t => (fixedTimeCutoff_bounds t).1) (fun t => (fixedTimeCutoff_bounds t).2) hs
  have hspace : ∀ x, x ∉ Icc (1/2:ℝ) 5 → (fixedSquaredCutoff x:ℂ)=0 := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (f := fun x => (fixedSquaredCutoff x:ℂ))
      (fun hh => hx (fixedSquaredCutoff.complex_support hh))
  obtain ⟨C,hC,hcubic⟩ := centered_restricted_cubic fixedSquaredCutoff.complex_smooth
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)≤5) hspace hε
  refine ⟨C,D,hC,hD,?_⟩
  intro N T L hN hNT hLl hLu a U ha
  dsimp only
  let μ := sourceTruncatedDensity (fun t => fixedTimeCutoff (t/T)) (boundedPolynomial N a) U
  let H := ∫ t, sourceRemovedDensity (fun t => fixedTimeCutoff (t/T)) (boundedPolynomial N a) U t
  let M := ∫ t, μ t^2
  have hT : 0 < T := by linarith
  have hlog : 0 ≤ Real.log (2*N) := Real.log_nonneg (by linarith)
  have hL : 0 < L := (Real.rpow_pos_of_pos (by positivity : 0 < 5*T) _).trans_le hLl
  obtain ⟨hm,hi,h2,h0,hμs,_⟩ := fixed_truncated_source_regular hN hT a ha U
  have hH : 0 ≤ H := by
    apply integral_nonneg
    intro t
    exact indicator_nonneg (fun x _ => mul_nonneg (fixedTimeCutoff_bounds (x/T)).1 (sq_nonneg _)) t
  have hΛ : 0 ≤ D*(N^2+H) := by positivity
  have hc := hcubic (5*T) L (-2*T) (3*T) (D*(N^2+H)) μ
    (by linarith) hLl hLu (by linarith) (by linarith) hΛ hm h0 hi h2
    (fun t ht => Function.notMem_support.mp (fun hh => ht (hμs hh)))
  have ht := htail N T hN (by linarith) a U (D*(N^2+H)) ha (by rfl)
  have hp := fixed_truncated_source_mass hN hNT a ha U
  have hA : 0 ≤ sourceFourierMass μ (D*(N^2+H)) :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hprod : (∫ t, μ t)*sourceFourierMass μ (D*(N^2+H)) ≤
      (612*T*N*Real.log (2*N))*(D*N^2*T*Real.log (2*N)) :=
    mul_le_mul hp ht hA (by positivity)
  change ‖kernelCubic (timeMeasure μ) (centeredKernel
    (fun x => ((MathCollab.Density.comparisonCutoff x^2:ℝ):ℂ)) (1/2) 5 L)‖ ≤ _
  change _ ≤ C*(5*T)^ε*((5*T)^2*M*Real.sqrt M+(5*T)*L*(D*(N^2+H))*M+
    (5*T)*L*(∫ t, μ t)*sourceFourierMass μ (D*(N^2+H))) at hc
  apply hc.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ C*(5*T)^ε)
  have hh := mul_le_mul_of_nonneg_left hprod (show 0 ≤ (5*T)*L by positivity)
  dsimp only [M,μ,H] at *
  nlinarith only [hh]

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.fixed_truncated_source_cubic
