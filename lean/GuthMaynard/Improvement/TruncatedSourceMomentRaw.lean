import GuthMaynard.Improvement.TruncatedSourceCubic
import GuthMaynard.Improvement.SpectralScaleBudget
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- The actual spectral and restricted cubic inequalities combined.
All remaining quantities are literal source moments; no analytic estimate
is assumed. The removed mass is retained for the subsequent scale budget. -/
theorem fixed_truncated_source_moment_raw {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ S C D : ℝ, 0 < S ∧ 0 < C ∧ 0 < D ∧ ∀ N T L : ℝ,
      2 ≤ N → N ≤ T → T ≤ N^2 → N ≤ L →
      (5*T)^((4:ℝ)/5) ≤ L → L ≤ 5*T →
      ∀ (a : ℕ → ℂ) (U : ℝ),
      (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
      let μ := sourceTruncatedDensity (fun t => fixedTimeCutoff (t/T)) (boundedPolynomial N a) U
      let H := ∫ t, sourceRemovedDensity (fun t => fixedTimeCutoff (t/T)) (boundedPolynomial N a) U t
      let M := ∫ t, μ t^2
      M^3 ≤ S*N^δ*((N*L*U^2)^3+
        (N^4/L)*(C*(5*T)^ε*(25*T^2*M*Real.sqrt M+
          5*T*L*(D*(N^2+H))*M+3060*D*N^3*L*T^3*(Real.log (2*N))^2))+
        5*N^5*L*T*M) := by
  obtain ⟨C,D,hC,hD,hc⟩ := fixed_truncated_source_cubic hε
  obtain ⟨S,hS,hs⟩ := source_spectral_scale MathCollab.Density.comparisonCutoff hδ
    (by norm_num : (1:ℝ)≤5) (by norm_num : (0:ℝ)<2)
  refine ⟨S,C,D,hS,hC,hD,?_⟩
  intro N T L hN hNT hTN hNL hLl hLu a U ha
  dsimp only
  let μ := sourceTruncatedDensity (fun t => fixedTimeCutoff (t/T)) (boundedPolynomial N a) U
  let H := ∫ t, sourceRemovedDensity (fun t => fixedTimeCutoff (t/T)) (boundedPolynomial N a) U t
  let M := ∫ t, μ t^2
  have hT : 0 < T := by linarith
  have hL : 0 < L := by linarith
  obtain ⟨hm,hi,h2,h0,hμs,hdom⟩ := fixed_truncated_source_regular hN hT a ha U
  have hsupport : Function.support μ ⊆ Icc (-2*T) (-2*T+5*T) := by
    have he : -2*T+5*T=3*T := by ring
    simpa only [he] using hμs
  have hLa : L ≤ 5*N^(2:ℝ) := by rw [Real.rpow_ofNat]; linarith
  have hTa : 5*T ≤ 5*N^(2:ℝ) := by rw [Real.rpow_ofNat]; linarith
  have hh := hs N L (5*T) (-2*T) hN hNL hLa (by positivity) hTa a μ ha
    hm hi h2 h0 hsupport (U^2) (sq_nonneg U) hdom
  have hb := hc N T L hN hNT hLl hLu a U ha
  have hx := mul_le_mul_of_nonneg_left hb (show 0 ≤ N^4/L by positivity)
  have hsum := add_le_add_left (add_le_add_right hx (N^5*L*(5*T)*M)) ((N*L*U^2)^3)
  have hout := mul_le_mul_of_nonneg_left hsum (show 0 ≤ S*N^δ by positivity)
  change M^3 ≤ _ at hh ⊢
  apply hh.trans
  convert hout using 1 <;> ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.fixed_truncated_source_moment_raw
