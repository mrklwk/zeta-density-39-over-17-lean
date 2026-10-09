module
public import GuthMaynard.Improvement.SourceRatioImage
public import GuthMaynard.Improvement.SourceRatioHeightBudget

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Finset
open scoped FourierTransform
namespace GuthMaynard.Improvement

/-- Uniform actual double-ratio sampling for all ordinary compactly supported
L1/L2 signals. The Fourier L1 term is the literal restricted band integral;
no global Fourier L1 premise is needed. -/
theorem source_ratio_sampling_band (c : ℝ) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ N T : ℝ, 2 ≤ N → 2 ≤ T →
      ∀ f : ℝ → ℂ, Integrable f → MemLp f 2 →
      Function.support f ⊆ Icc (-(c*T)) (c*T) →
      (∑ n ∈ sourceRatioIndices N, ∑ m ∈ sourceRatioIndices N,
        ‖𝓕 f (Real.log ((n:ℝ)/m)/(2*Real.pi))‖) ≤
      C*(N^2*(∫ ξ in Icc (-2:ℝ) 2, ‖𝓕 f ξ‖)+
        N*Real.sqrt (T*Real.log (2*N))*Real.sqrt (∫ t, ‖f t‖^2)) := by
  obtain ⟨C,hC,hbudget⟩ := source_sampling_scalar_budget c hc
  refine ⟨C,hC,?_⟩
  intro N T hN hT f h1 h2 hs
  have hN0 : 0 ≤ N := by linarith
  have hR : 0 ≤ c*T := mul_nonneg hc (by linarith)
  let Y := sourceHeight N T
  let M := ∫ t, ‖f t‖^2
  let I := ∫ ξ in Icc (-2:ℝ) 2, ‖𝓕 f ξ‖
  have hM : 0 ≤ M := integral_nonneg (fun _ => sq_nonneg _)
  have hI : 0 ≤ I := integral_nonneg (fun _ => norm_nonneg _)
  obtain ⟨hY,hYN,_⟩ := sourceHeight_bounds hN hT
  have hY0 : 0 < Y := by dsimp [Y]; linarith
  obtain ⟨J,hcover,hmin,hzero,hgeom,hinv⟩ := source_height_shell_budgets hN hT
  let L := ∑ q ∈ (sourceRatioImage N).filter (fun q => (max q.1 q.2:ℕ) ≤ Y),
    sourceRatioWeight N q*‖𝓕 f (sourceRatioFrequency q)‖
  let shell := fun j : ℕ => ∑ q ∈ (sourceRatioImage N).filter
    (fun q => (2:ℝ)^j*Y < (max q.1 q.2:ℕ) ∧ (max q.1 q.2:ℕ) ≤ (2:ℝ)^(j+1)*Y),
      sourceRatioWeight N q*‖𝓕 f (sourceRatioFrequency q)‖
  have hdecomp : (∑ p ∈ sourceRatioPairSet N, ‖𝓕 f (sourceRatioFrequency p)‖) =
      L+∑ j ∈ range J, shell j := by
    exact source_ratio_sum_dyadic (sourceRatioPairSet N)
      (fun p hp => ⟨(source_ratio_pair_box hN0 p hp).1,(source_ratio_pair_box hN0 p hp).2.1⟩)
      (fun s => ‖𝓕 f (s/(2*Real.pi))‖) hY0.le J
      (fun q hq => (source_ratio_image_data hN0 hq).2.2.2.2.1.trans hcover)
  have hlow : L ≤ Real.sqrt (16*N^2*Real.log (2*N))*
      Real.sqrt ((2*Real.pi*Y^2+4*Real.pi*c*T)*M) := by
    simpa only [L,Y,M,mul_assoc] using source_actual_ratio_low hN hY0 h1 h2 hR hs
  have hshell (j : ℕ) : shell j ≤
      16*Real.pi*N*((2:ℝ)^j*Y)*I+8*Real.pi*N*(c*T)/((2:ℝ)^j*Y)*Real.sqrt M := by
    have hp : 1 ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
    have hQ : 1 ≤ (2:ℝ)^j*Y := by dsimp [Y]; nlinarith
    have hh := source_actual_ratio_shell hN hQ h1 h2 hR hs
    simpa only [shell,I,M,pow_succ,mul_assoc,mul_left_comm,mul_comm] using hh
  have hhigh : (∑ j ∈ range J, shell j) ≤ 64*Real.pi*N^2*I+
      (if Y=2*N then 0 else 16*Real.pi*c*(N*T/Y)*Real.sqrt M) := by
    by_cases he : Y=2*N
    · have hJ : J=0 := hzero.mpr he
      rw [hJ,ite_eq_left he]
      simp only [Finset.range_zero,sum_empty,add_zero]
      positivity
    · rw [ite_eq_right he]
      calc
        _ ≤ ∑ j ∈ range J, (16*Real.pi*N*((2:ℝ)^j*Y)*I+
            8*Real.pi*N*(c*T)/((2:ℝ)^j*Y)*Real.sqrt M) := sum_le_sum (fun j _ => hshell j)
        _ = 16*Real.pi*N*(∑ j ∈ range J, (2:ℝ)^j*Y)*I+
            8*Real.pi*N*(c*T)*(∑ j ∈ range J, ((2:ℝ)^j*Y)⁻¹)*Real.sqrt M := by
          simp only [div_eq_mul_inv,sum_add_distrib,sum_mul,mul_sum]
        _ ≤ 16*Real.pi*N*(4*N)*I+8*Real.pi*N*(c*T)*(2/Y)*Real.sqrt M := by
          gcongr
        _ = _ := by field_simp; ring
  have htotal : (∑ p ∈ sourceRatioPairSet N, ‖𝓕 f (sourceRatioFrequency p)‖) ≤
      C*(N^2*I+N*Real.sqrt (T*Real.log (2*N))*Real.sqrt M) := by
    rw [hdecomp]
    exact (add_le_add hlow hhigh).trans (by
      simpa only [Y,add_assoc] using hbudget N T M I hN hT hM hI)
  simpa only [sourceRatioPairSet,sum_product,sourceRatioFrequency,I,M] using htotal

/-- Global Fourier-L1 form for signals whose literal Fourier transform is
integrable. This premise is supplied by the checked spatial-cutoff theorem. -/
theorem source_ratio_sampling_global (c : ℝ) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ N T : ℝ, 2 ≤ N → 2 ≤ T →
      ∀ f : ℝ → ℂ, Integrable f → MemLp f 2 → Integrable (𝓕 f) →
      Function.support f ⊆ Icc (-(c*T)) (c*T) →
      (∑ n ∈ sourceRatioIndices N, ∑ m ∈ sourceRatioIndices N,
        ‖𝓕 f (Real.log ((n:ℝ)/m)/(2*Real.pi))‖) ≤
      C*(N^2*(∫ ξ, ‖𝓕 f ξ‖)+
        N*Real.sqrt (T*Real.log (2*N))*Real.sqrt (∫ t, ‖f t‖^2)) := by
  obtain ⟨C,hC,hb⟩ := source_ratio_sampling_band c hc
  refine ⟨C,hC,?_⟩
  intro N T hN hT f h1 h2 hF hs
  apply (hb N T hN hT f h1 h2 hs).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply add_le_add _ le_rfl
  exact mul_le_mul_of_nonneg_left
    (setIntegral_le_integral hF.norm (Filter.Eventually.of_forall (fun ξ => norm_nonneg (𝓕 f ξ))))
    (sq_nonneg N)

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.source_ratio_sampling_band
#print axioms GuthMaynard.Improvement.source_ratio_sampling_global
