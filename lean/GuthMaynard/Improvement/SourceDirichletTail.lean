import GuthMaynard.Improvement.SourceDirichletPairing
import GuthMaynard.Improvement.SourceRatioBound
import GuthMaynard.Improvement.SourceTailConditional
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped FourierTransform ContDiff
namespace GuthMaynard.Improvement

/-- The actual bounded polynomial satisfies the universal source test bound.
The constant precedes N,T,coefficients and every test function. -/
theorem boundedPolynomial_source_sampling {χ : ℝ → ℝ}
    (hs : ∀ t, t ∉ Icc (-2:ℝ) 3 → χ t = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ N T : ℝ, 2 ≤ N → 2 ≤ T →
      ∀ a : ℕ → ℂ, (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
      SourceSamplingBound (boundedPolynomial N a) (fun t => χ (t/T))
        (C*N^2) (C*N*Real.sqrt (T*Real.log (2*N))) := by
  obtain ⟨C,hC,h⟩ := source_ratio_sampling_global 3 (by norm_num)
  refine ⟨C,hC,?_⟩
  intro N T hN hT a ha f h1 h2 hF hf
  have hTp : 0 < T := by linarith
  have hfs : Function.support f ⊆ Icc (-(3*T)) (3*T) := by
    intro t ht
    have hχ : χ (t/T) ≠ 0 := hf ht
    have hmem : t/T ∈ Icc (-2:ℝ) 3 := by
      by_contra hn
      exact hχ (hs _ hn)
    constructor
    · have hh := (le_div_iff₀ hTp).mp hmem.1
      linarith
    · exact (div_le_iff₀ hTp).mp hmem.2
  have hh := (boundedPolynomial_pairing_ratio_bound (by linarith : 0 < N) a ha h1).trans
    (h N T hN hT f h1 h2 hF hfs)
  convert hh using 1
  ring

/-- Actual source restricted Fourier tail for bounded coefficients, with no
sampling or Fourier-estimate premise. The constant is fixed before all scales,
coefficients, cutoff levels and exceptional thresholds. -/
theorem boundedPolynomial_source_tail {χ : ℝ → ℝ} (hχd : ContDiff ℝ ∞ χ)
    (hχ0 : ∀ t, 0 ≤ χ t) (hχ1 : ∀ t, χ t ≤ 1)
    (hs : ∀ t, t ∉ Icc (-2:ℝ) 3 → χ t = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ N T : ℝ, 2 ≤ N → 2 ≤ T →
      ∀ (a : ℕ → ℂ) (U Λ : ℝ), (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
      C*(N^2+(∫ t, sourceRemovedDensity (fun t => χ (t/T)) (boundedPolynomial N a) U t)) ≤ Λ →
      sourceFourierMass (sourceTruncatedDensity (fun t => χ (t/T)) (boundedPolynomial N a) U) Λ ≤
        C*N^2*T*Real.log (2*N) := by
  obtain ⟨D,hD,hbound⟩ := boundedPolynomial_source_sampling hs
  let J := ∫ ξ, ‖𝓕 (fun t => (χ t:ℂ)) ξ‖
  have hJ : 0 ≤ J := integral_nonneg (fun _ => norm_nonneg _)
  let C := 4*D^2+2*(D*J+1)+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro N T hN hT a U Λ ha hΛ
  let H := ∫ t, sourceRemovedDensity (fun t => χ (t/T)) (boundedPolynomial N a) U t
  have hH : 0 ≤ H := by
    apply integral_nonneg
    intro t
    exact indicator_nonneg (fun x _ => mul_nonneg (hχ0 (x/T)) (sq_nonneg _)) t
  have hNp : 0 < N := by linarith
  have hTp : 0 < T := by linarith
  have hlog : 0 ≤ Real.log (2*N) := Real.log_nonneg (by linarith)
  have hΛp : 0 < Λ := (mul_pos hC (by positivity : 0 < N^2+H)).trans_le hΛ
  have hc1 : 2*(D*J) ≤ C := by dsimp [C]; nlinarith [sq_nonneg D]
  have hc2 : 2 ≤ C := by dsimp [C]; nlinarith [sq_nonneg D,mul_nonneg hD.le hJ]
  have hth : 2*((D*N^2)*J+H) ≤ Λ := by
    have hp := mul_le_mul_of_nonneg_right hc1 (sq_nonneg N)
    have hq := mul_le_mul_of_nonneg_right hc2 hH
    dsimp [H] at *
    nlinarith
  obtain ⟨hcont,hreg⟩ := boundedPolynomial_regular N a
  have hh := source_tail_of_sampling hχd (HasCompactSupport.intro isCompact_Icc hs)
    hχ0 hχ1 hTp hcont.measurable hreg U
    (by positivity : 0 ≤ D*N^2) (by positivity : 0 ≤ D*N*Real.sqrt (T*Real.log (2*N)))
    hΛp (hbound N T hN hT a ha) hth
  have hsqrt := Real.sq_sqrt (mul_nonneg hTp.le hlog)
  have hc4 : 4*D^2 ≤ C := by dsimp [C]; nlinarith [mul_nonneg hD.le hJ]
  calc
    _ ≤ 4*(D*N*Real.sqrt (T*Real.log (2*N)))^2 := hh
    _ = (4*D^2)*N^2*T*Real.log (2*N) := by rw [mul_pow,mul_pow,hsqrt]; ring
    _ ≤ _ := by gcongr

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.boundedPolynomial_source_sampling
#print axioms GuthMaynard.Improvement.boundedPolynomial_source_tail
