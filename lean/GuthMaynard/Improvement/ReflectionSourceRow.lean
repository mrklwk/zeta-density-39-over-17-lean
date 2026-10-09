import GuthMaynard.Improvement.ReflectionAbsoluteShell
import GuthMaynard.Improvement.ReflectionDyadicIntegral
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- The actual source-specific row estimate. All reflection, mean-value,
Mellin, error and dyadic budgets are discharged. Constants precede every
variable scale, density, coefficient family and support translate. -/
theorem centered_source_row (w : MathCollab.Density.ReflectionCutoff)
    {ε A p : ℝ} (hε : 0 < ε) (hA : 1 ≤ A) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ N L T t₀ u : ℝ,
      2 ≤ N → N ≤ L → 0 ≤ T → T ≤ A*N^p → u ∈ Icc t₀ (t₀+T) →
      ∀ (a : ℕ → ℂ) (μ : ℝ → ℝ),
      (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) → Measurable μ → Integrable μ →
      (∀ t, 0 ≤ μ t) → Function.support μ ⊆ Icc t₀ (t₀+T) →
      (∀ t, μ t ≤ ‖boundedPolynomial N a t‖^2) →
      (∫ t, μ t*‖centeredKernel (fun x => (w x:ℂ)) (1/2) 5 L (u-t)‖^2) ≤
        C*N^ε*L*N*T := by
  obtain ⟨C₀,hC₀,hnear⟩ := centered_near_row_bound w
  obtain ⟨C₁,hC₁,hband⟩ := reflection_absolute_shell_bound w hε hA hp
  refine ⟨1+C₀+2*C₁,by positivity,?_⟩
  intro N L T t₀ u hN hNL hT hupper hu a μ ha hm hi h0 hs hμ
  have hN0 : 0 < N := by linarith
  have hL : 0 < L := hN0.trans_le hNL
  have hpow : 1 ≤ N^ε := Real.one_le_rpow (by linarith) hε.le
  let Y := Real.pi*L/8
  have hY : 0 < Y := by dsimp [Y]; positivity
  let F := fun t => μ t*‖centeredKernel (fun x => (w x:ℂ)) (1/2) 5 L (t-u)‖^2
  have hiF : Integrable F := centered_row_integrable w (by linarith) u hi
  have hz : ∀ t, T < |t-u| → F t=0 := by
    intro t ht
    have hn : μ t=0 := by
      by_contra hh
      have hmem := hs hh
      have hb : |t-u| ≤ T := abs_le.mpr ⟨by linarith [hmem.1,hu.2],by linarith [hmem.2,hu.1]⟩
      linarith
    simp only [F,hn,zero_mul]
  have hnear' : (∫ t in {t | |t-u| ≤ Y}, F t) ≤ C₀*N^ε*L*N*T := by
    have hh := hnear N L T t₀ u hN hNL hT a μ ha hi h0 hs hμ
    have hmono := mul_le_mul_of_nonneg_left hpow (show 0 ≤ C₀*L*N*T by positivity)
    change (∫ t in {t | |t-u| ≤ Y}, F t) ≤ _
    exact hh.trans (by nlinarith)
  have hfull : (∫ t, F t) ≤ (C₀+2*C₁)*N^ε*L*N*T := by
    by_cases hYT : Y ≤ T
    · have hh := reflection_dyadic_integral_bound hiF u hY hYT
        (show 0 ≤ C₁*N^ε*L*N by positivity) hz hnear'
        (fun H hYH hHT => by
          have hb := hband N L H u hN hNL (hY.trans_le hYH) (hHT.le.trans hupper)
            a μ ha hm hi h0 hμ
          exact hb)
      convert hh using 1
      ring
    · have he : (∫ t in {t | |t-u| ≤ Y}, F t) = ∫ t, F t :=
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht =>
          hz t ((lt_of_not_ge hYT).trans (lt_of_not_ge ht)))
      rw [← he]
      exact hnear'.trans (by nlinarith [show 0 ≤ C₁*N^ε*L*N*T by positivity])
  have horient : (∫ t, μ t*‖centeredKernel (fun x => (w x:ℂ)) (1/2) 5 L (u-t)‖^2) =
      ∫ t, F t := by
    apply integral_congr_ae
    filter_upwards with t
    rw [show u-t=-(t-u) by ring,centeredKernel_norm_neg w hL]
  rw [horient]
  exact hfull.trans (by nlinarith [show 0 ≤ N^ε*L*N*T by positivity])

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.centered_source_row
