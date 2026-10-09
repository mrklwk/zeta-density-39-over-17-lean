import GuthMaynard.Improvement.TruncatedSourceMomentRaw
import GuthMaynard.Improvement.MiddleRangeIdentities
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- Actual raw moment at the middle-range scales, with the actual removed
mass still explicit. Constants are chosen before every source and scale. -/
theorem middle_source_moment_raw {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ S C D : ℝ, 0 < S ∧ 0 < C ∧ 0 < D ∧ ∀ N T : ℝ,
      2 ≤ N → N^((6:ℝ)/5) ≤ T → T ≤ N^((5:ℝ)/3) →
      ∀ a : ℕ → ℂ, (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
      let U := middleThreshold N T
      let P := middleMoment N T
      let μ := sourceTruncatedDensity (fun t => fixedTimeCutoff (t/T)) (boundedPolynomial N a) U
      let H := ∫ t, sourceRemovedDensity (fun t => fixedTimeCutoff (t/T)) (boundedPolynomial N a) U t
      let M := ∫ t, μ t^2
      M^3 ≤ S*N^δ*(125*P^3+C*(5*T)^ε*
        (5*P*Real.sqrt P*M*Real.sqrt M+5*D*N^4*T*(N^2+H)*M+
          3060*D*N^7*T^3*(Real.log (2*N))^2)+25*P^2*M) := by
  obtain ⟨S,C,D,hS,hC,hD,hr⟩ := fixed_truncated_source_moment_raw hδ hε
  refine ⟨S,C,D,hS,hC,hD,?_⟩
  intro N T hN hlo hhi a ha
  dsimp only
  let L := middleLength N T
  let U := middleThreshold N T
  let P := middleMoment N T
  let μ := sourceTruncatedDensity (fun t => fixedTimeCutoff (t/T)) (boundedPolynomial N a) U
  let H := ∫ t, sourceRemovedDensity (fun t => fixedTimeCutoff (t/T)) (boundedPolynomial N a) U t
  let M := ∫ t, μ t^2
  obtain ⟨hNT,hTN⟩ := middle_time_bounds hN hlo hhi
  obtain ⟨hNL,hLl,hLu,_⟩ := middle_rescaled_length_bounds hN hlo hhi
  have hn : 0 < N := by linarith
  have ht : 0 < T := by linarith
  have hl : 0 < L := by dsimp [L,middleLength]; positivity
  have h1 : N*L*U^2=P := middle_length_threshold_identity hn ht
  have h2 : N^4*T^2/L=P*Real.sqrt P :=
    (middle_moment_three_halves hn ht).1.trans (middle_moment_three_halves hn ht).2
  have h3 : N^5*L*T=P^2 := middle_length_moment_square hn ht
  have hraw := hr N T (5*L) hN hNT hTN hNL hLl hLu a U ha
  have he1 : (N*(5*L)*U^2)^3=125*P^3 := by
    calc
      _ = 125*(N*L*U^2)^3 := by ring
      _ = _ := by rw [h1]
  have he2 : (N^4/(5*L))*(C*(5*T)^ε*(25*T^2*M*Real.sqrt M+
      5*T*(5*L)*(D*(N^2+H))*M+3060*D*N^3*(5*L)*T^3*(Real.log (2*N))^2)) =
      C*(5*T)^ε*(5*P*Real.sqrt P*M*Real.sqrt M+5*D*N^4*T*(N^2+H)*M+
        3060*D*N^7*T^3*(Real.log (2*N))^2) := by
    calc
      _ = C*(5*T)^ε*(5*(N^4*T^2/L)*M*Real.sqrt M+
          5*D*N^4*T*(N^2+H)*M+3060*D*N^7*T^3*(Real.log (2*N))^2) := by
        field_simp
        ring
      _ = _ := by rw [h2]; ring
  have he3 : 5*N^5*(5*L)*T*M=25*P^2*M := by
    calc
      _ = 25*(N^5*L*T)*M := by ring
      _ = _ := by rw [h3]
  change M^3 ≤ _ at hraw ⊢
  dsimp only [M,μ,H] at he2 he3
  simpa only [he1,he2,he3] using hraw

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.middle_source_moment_raw
