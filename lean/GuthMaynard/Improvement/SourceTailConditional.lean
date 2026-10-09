import GuthMaynard.Improvement.SourceCutoffConvolution
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped FourierTransform ContDiff
namespace GuthMaynard.Improvement

def sourceTruncatedDensity (β : ℝ → ℝ) (D : ℝ → ℂ) (U : ℝ) : ℝ → ℝ :=
  {t | ‖D t‖ ≤ U}.indicator (fun t => β t * ‖D t‖^2)
def sourceRemovedDensity (β : ℝ → ℝ) (D : ℝ → ℂ) (U : ℝ) : ℝ → ℝ :=
  ({t | ‖D t‖ ≤ U}ᶜ).indicator (fun t => β t * ‖D t‖^2)

/-- The actual truncated and removed densities have all ordinary measure
hypotheses, for any bounded measurable D. -/
theorem source_density_regular {β : ℝ → ℝ} (hβm : Measurable β)
    (hβi : Integrable β) (hβ0 : ∀ t, 0 ≤ β t) (hβ1 : ∀ t, β t ≤ 1)
    {D : ℝ → ℂ} (hDm : Measurable D) {B : ℝ} (hDb : ∀ t, ‖D t‖ ≤ B) (U : ℝ) :
    Measurable (sourceTruncatedDensity β D U) ∧
    (∀ t, 0 ≤ sourceTruncatedDensity β D U t) ∧
    Integrable (sourceTruncatedDensity β D U) ∧
    Integrable (fun t => sourceTruncatedDensity β D U t ^2) ∧
    Integrable (sourceRemovedDensity β D U) ∧
    (∀ t, 0 ≤ sourceRemovedDensity β D U t) ∧
    (∀ t, sourceTruncatedDensity β D U t + sourceRemovedDensity β D U t = β t*‖D t‖^2) := by
  have hA : MeasurableSet {t | ‖D t‖ ≤ U} := measurableSet_le hDm.norm measurable_const
  have hfm : Measurable (fun t => β t*‖D t‖^2) := hβm.mul (hDm.norm.pow_const 2)
  have hfull0 : ∀ t, 0 ≤ β t*‖D t‖^2 := fun t => mul_nonneg (hβ0 t) (sq_nonneg _)
  have hb0 : 0 ≤ B := (norm_nonneg (D 0)).trans (hDb 0)
  have hp : ∀ t, β t*‖D t‖^2 ≤ β t*B^2 := by
    intro t
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hDb t) 2) (hβ0 t)
  have hfi : Integrable (fun t => β t*‖D t‖^2) := by
    apply (hβi.mul_const (B^2)).mono' hfm.aestronglyMeasurable
    filter_upwards [] with t
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hfull0 t)] using hp t
  have hm : Measurable (sourceTruncatedDensity β D U) := hfm.indicator hA
  have h0 : ∀ t, 0 ≤ sourceTruncatedDensity β D U t := by
    intro t
    exact indicator_nonneg (fun x _ => hfull0 x) t
  have hμb : ∀ t, sourceTruncatedDensity β D U t ≤ β t*B^2 := by
    intro t
    by_cases ht : t ∈ {t | ‖D t‖ ≤ U}
    · simpa [sourceTruncatedDensity,ht] using hp t
    · simp only [sourceTruncatedDensity,indicator_of_notMem ht]
      exact mul_nonneg (hβ0 t) (sq_nonneg B)
  have hμ2 : Integrable (fun t => sourceTruncatedDensity β D U t^2) := by
    apply (hβi.mul_const (B^4)).mono' (hm.pow_const 2).aestronglyMeasurable
    filter_upwards [] with t
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ (β t*B^2)^2 := pow_le_pow_left₀ (h0 t) (hμb t) 2
      _ = (β t)^2*B^4 := by ring
      _ ≤ β t*B^4 := mul_le_mul_of_nonneg_right (by nlinarith [hβ0 t,hβ1 t]) (by positivity)
  refine ⟨hm,h0,hfi.indicator hA,hμ2,hfi.indicator hA.compl,?_,?_⟩
  · intro t
    exact indicator_nonneg (fun x _ => hfull0 x) t
  · intro t
    by_cases ht : t ∈ {t | ‖D t‖ ≤ U} <;> simp [sourceTruncatedDensity,sourceRemovedDensity,ht]

/-- Sole open analytic contract: a sampling bound for the actual D-pairing
against every Fourier-integrable L1/L2 test supported on the cutoff. -/
def SourceSamplingBound (D : ℝ → ℂ) (β : ℝ → ℝ) (P Q : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, Integrable f → MemLp f 2 → Integrable (𝓕 f) →
    Function.support f ⊆ Function.support β →
    ‖∫ t, (‖D t‖^2:ℂ)*f t‖ ≤ P*(∫ ξ, ‖𝓕 f ξ‖) + Q*Real.sqrt (∫ t, ‖f t‖^2)

/-- Scalar absorption preserves the zero-mass case and requires a positive threshold. -/
theorem source_tail_scalar_absorption {A K Q Λ : ℝ}
    (hA : 0 ≤ A) (hQ : 0 ≤ Q) (hΛ : 0 < Λ) (hthreshold : 2*K ≤ Λ)
    (hbudget : A ≤ K*(A/Λ)+Q*Real.sqrt A) : A ≤ 4*Q^2 := by
  have hk : K*(A/Λ) ≤ A/2 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    have hh := mul_le_mul_of_nonneg_right hthreshold (div_nonneg hA hΛ.le)
    have hc : Λ*(A/Λ)=A := by field_simp
    rw [hc] at hh
    nlinarith
  have hs := Real.sq_sqrt hA
  have hroot := Real.sqrt_nonneg A
  have hh : Real.sqrt A ≤ 2*Q := by nlinarith
  nlinarith

/-- Conditional source tail for the actual low-value density. All inverse-Fourier,
cutoff and removal estimates are proved; only SourceSamplingBound remains open. -/
theorem source_tail_of_sampling {χ : ℝ → ℝ} (hχd : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχ0 : ∀ t, 0 ≤ χ t) (hχ1 : ∀ t, χ t ≤ 1)
    {T : ℝ} (hT : 0 < T) {D : ℝ → ℂ} (hDm : Measurable D)
    {B : ℝ} (hDb : ∀ t, ‖D t‖ ≤ B) (U : ℝ)
    {P Q Λ : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hΛ : 0 < Λ)
    (hsampling : SourceSamplingBound D (fun t => χ (t/T)) P Q)
    (hthreshold : 2*(P*(∫ ξ, ‖𝓕 (fun t => (χ t:ℂ)) ξ‖) +
      ∫ t, sourceRemovedDensity (fun t => χ (t/T)) D U t) ≤ Λ) :
    sourceFourierMass (sourceTruncatedDensity (fun t => χ (t/T)) D U) Λ ≤ 4*Q^2 := by
  let β : ℝ → ℝ := fun t => χ (t/T)
  let μ := sourceTruncatedDensity β D U
  let ρ := sourceRemovedDensity β D U
  let g := sourceFourierSignal μ Λ
  let A := sourceFourierMass μ Λ
  have hβm : Measurable β := (hχd.continuous.comp (continuous_id.div_const T)).measurable
  have hβi : Integrable β := by
    simpa [β,div_eq_mul_inv,mul_comm] using
      (hχd.continuous.integrable_of_hasCompactSupport hχc).comp_mul_left' (inv_ne_zero (ne_of_gt hT))
  obtain ⟨hμm,hμ0,hμi,hμ2,hρi,hρ0,hdecomp⟩ :=
    source_density_regular hβm hβi (fun t => hχ0 (t/T)) (fun t => hχ1 (t/T)) hDm hDb U
  have hA : 0 ≤ A := integral_nonneg (fun ξ => sq_nonneg _)
  obtain ⟨hfi,hf2,hfbound,hFfi,hFbound⟩ :=
    source_smooth_scaled_cutoff_bounds hμi hμ2 hΛ hχd hχc hχ0 hχ1 hT
  have hsupport : Function.support (fun t => (β t:ℂ)*g t) ⊆ Function.support β := by
    intro t ht
    by_contra hn
    have hz : β t=0 := by simpa [Function.mem_support] using hn
    exact ht (by simp [hz])
  have hsample := hsampling (fun t => (β t:ℂ)*g t) hfi hf2 hFfi hsupport
  have hmain : ‖∫ t, (‖D t‖^2:ℂ)*((β t:ℂ)*g t)‖ ≤
      P*(∫ ξ, ‖𝓕 (fun t => (χ t:ℂ)) ξ‖)*(A/Λ)+Q*Real.sqrt A := by
    calc
      _ ≤ _ := hsample
      _ ≤ _ := by
        apply add_le_add
        · calc
            _ ≤ P*((∫ ξ, ‖𝓕 (fun t => (χ t:ℂ)) ξ‖)*(A/Λ)) :=
              mul_le_mul_of_nonneg_left hFbound hP
            _ = _ := by ring
        · exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hfbound) hQ
  have hρ0' : ∀ t, 0 ≤ ρ t := hρ0
  have hgm := (sourceFourierSignal_l2 hμi hμ2 hΛ).1.aestronglyMeasurable
  have hρgi : Integrable (fun t => (ρ t:ℂ)*g t) := by
    apply (hρi.mul_const (A/Λ)).mono' ((Complex.ofRealCLM.integrable_comp hρi).aestronglyMeasurable.mul hgm)
    filter_upwards [] with t
    change ‖(ρ t:ℂ)*g t‖ ≤ ρ t*(A/Λ)
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hρ0' t)]
    exact mul_le_mul_of_nonneg_left (sourceFourierSignal_bound hμi hμ2 hΛ t) (hρ0 t)
  have hρbound : ‖∫ t, (ρ t:ℂ)*g t‖ ≤ (∫ t, ρ t)*(A/Λ) := by
    calc
      _ ≤ ∫ t, ‖(ρ t:ℂ)*g t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t, ρ t*(A/Λ) := by
        apply integral_mono hρgi.norm (hρi.mul_const _)
        intro t
        simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hρ0' t)]
        exact mul_le_mul_of_nonneg_left (sourceFourierSignal_bound hμi hμ2 hΛ t) (hρ0 t)
      _ = _ := integral_mul_const _ _
  have hsplit : (∫ t, (‖D t‖^2:ℂ)*((β t:ℂ)*g t)) =
      (A:ℂ)+(∫ t, (ρ t:ℂ)*g t) := by
    rw [← sourceFourierSignal_pairing hμi hμ2 hΛ,← integral_add (sourceFourierSignal_pair_integrable hμi hμ2 hΛ) hρgi]
    apply integral_congr_ae
    filter_upwards [] with t
    have hd := congrArg (fun x : ℝ => (x:ℂ)) (hdecomp t)
    push_cast at hd
    dsimp [μ,ρ,g] at hd ⊢
    rw [← add_mul,hd]
    ring
  have hbudget : A ≤ (P*(∫ ξ, ‖𝓕 (fun t => (χ t:ℂ)) ξ‖)+(∫ t,ρ t))*(A/Λ)+Q*Real.sqrt A := by
    have ht := norm_sub_le (∫ t, (‖D t‖^2:ℂ)*((β t:ℂ)*g t)) (∫ t, (ρ t:ℂ)*g t)
    have hdiff : (∫ t, (‖D t‖^2:ℂ)*((β t:ℂ)*g t)) - (∫ t, (ρ t:ℂ)*g t) = (A:ℂ) := by
      rw [hsplit,add_sub_cancel_right]
    rw [hdiff,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hA] at ht
    nlinarith
  exact source_tail_scalar_absorption hA hQ hΛ hthreshold hbudget

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.source_density_regular
#print axioms GuthMaynard.Improvement.source_tail_scalar_absorption
#print axioms GuthMaynard.Improvement.source_tail_of_sampling
