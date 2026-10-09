import GuthMaynard.Improvement.CubicRetainedMasked
import GuthMaynard.Improvement.CenteredCubicApprox
import GuthMaynard.Improvement.CenteredCubicBoundedHeight
import GuthMaynard.Improvement.CubicOrdinaryClosure
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped FourierTransform ContDiff
namespace GuthMaynard.Improvement

/-- Actual centered kernel masked cubic for every height T>=2. The
bounded-height argument is included; no retained-kernel approximation or
masked-majorant premise remains. -/
theorem centered_masked_cubic_estimate {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hs : ∀ x, x ∉ Icc l u → a x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T L t₀ t₁ : ℝ) (μ : ℝ → ℝ) (A : Set ℝ),
      2 ≤ T → T^((4:ℝ)/5) ≤ L → L ≤ T → t₀ ≤ t₁ → t₁-t₀ ≤ T →
      Measurable μ → (∀ t, 0 ≤ μ t) → Integrable μ → Integrable (fun t => μ t^2) →
      (∀ t, t ∉ Icc t₀ t₁ → μ t = 0) → MeasurableSet A →
      (∀ ξ, -ξ ∈ A ↔ ξ ∈ A) →
      let M := ∫ t, μ t^2
      let E := ∫ ξ, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^4
      let E₀ := ∫ ξ in Aᶜ, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^4
      let A₂ := ∫ ξ in A, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^2
      ‖kernelCubic (timeMeasure μ) (centeredKernel a l u L)‖ ≤
        C*T^ε*(T^2*M*Real.sqrt M+T*L*Real.sqrt M*Real.sqrt E₀+
          Real.sqrt A₂*(T^2*M+T*L*Real.sqrt E)) := by
  obtain ⟨η,C,T₀,hη,_hη1,hC,hT₀,hret⟩ := retained_masked_cubic_estimate ha hl hlu hs hε
  obtain ⟨E,hE,herr⟩ := centered_cubic_approximation ha hl hlu hs hη
  obtain ⟨B,hB,hsmall⟩ := centered_cubic_bounded_height ha hl hlu hs T₀ (by linarith)
  refine ⟨C+E+B+1,by positivity,?_⟩
  intro T L t₀ t₁ μ A hT hLl hLu ht hlen hm h0 hi h2 hsup hA hAsym
  dsimp only
  let M := ∫ t, μ t^2
  let Z := T^2*M*Real.sqrt M+T*L*Real.sqrt M*Real.sqrt (∫ ξ in Aᶜ, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^4)+
    Real.sqrt (∫ ξ in A, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^2)*(T^2*M+T*L*Real.sqrt (∫ ξ, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^4))
  have hM : 0 ≤ M := integral_nonneg (fun _ => sq_nonneg _)
  have hT1 : 1 ≤ T := by linarith
  have hTp : 0 < T := by linarith
  have hL1 : 1 ≤ L := (Real.one_le_rpow hT1 (by norm_num : (0:ℝ) ≤ 4/5)).trans hLl
  have hLp : 0 < L := by linarith
  have hLT2 : L ≤ T^2 := hLu.trans (by nlinarith)
  have hTe : 1 ≤ T^ε := Real.one_le_rpow hT1 hε.le
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hbase : T^2*M*Real.sqrt M ≤ Z := by
    dsimp [Z]
    have hp : 0 ≤ T*L*Real.sqrt M*Real.sqrt (∫ ξ in Aᶜ, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^4) := by positivity
    have hq : 0 ≤ Real.sqrt (∫ ξ in A, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^2)*(T^2*M+T*L*Real.sqrt (∫ ξ, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^4)) := by positivity
    linarith
  have hZT : Z ≤ T^ε*Z := by nlinarith
  have hsqrt : Real.sqrt M^3 = M*Real.sqrt M := by
    rw [pow_succ,Real.sq_sqrt hM]
  by_cases hbig : T₀ ≤ T
  · let K := kernelCubic (timeMeasure μ) (centeredKernel a l u L)
    let J := kernelCubic (timeMeasure μ)
      (retainedPoissonKernel (volume.restrict (Icc l u)) a L (poissonModes (T^(1+η)/L)))
    have hJ : ‖J‖ ≤ C*T^ε*Z := hret T L t₀ t₁ μ A hbig hLl hLu ht hlen hm h0 hi h2 hsup hA hAsym
    have hd : ‖K-J‖ ≤ E*T^(-100:ℝ)*Real.sqrt M^3 :=
      herr T L t₀ t₁ μ hT1 hL1 hLT2 ht hlen hm h0 hi h2 hsup
    have hpow : T^(-100:ℝ) ≤ T^2 := by
      rw [← Real.rpow_natCast T 2]
      exact Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
    have hy : T^(-100:ℝ)*Real.sqrt M^3 ≤ T^ε*Z := by
      rw [hsqrt]
      calc
        _ ≤ T^2*(M*Real.sqrt M) := mul_le_mul_of_nonneg_right hpow (by positivity)
        _ = T^2*M*Real.sqrt M := by ring
        _ ≤ Z := hbase
        _ ≤ _ := hZT
    have hd' : ‖K-J‖ ≤ E*(T^ε*Z) := hd.trans (by nlinarith [mul_le_mul_of_nonneg_left hy hE])
    change ‖K‖ ≤ (C+E+B+1)*T^ε*Z
    calc
      _ = ‖J+(K-J)‖ := by congr 1; ring
      _ ≤ ‖J‖+‖K-J‖ := norm_add_le _ _
      _ ≤ C*T^ε*Z+E*(T^ε*Z) := add_le_add hJ hd'
      _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ B+1 by positivity) (mul_nonneg (by positivity : 0 ≤ T^ε) hZ)]
  · have hb := hsmall T L t₀ t₁ μ hT1 (le_of_not_ge hbig) hL1 hLu ht hlen hm h0 hi h2 hsup
    change _ ≤ B*T^2*Real.sqrt M^3 at hb
    rw [hsqrt] at hb
    calc
      _ ≤ B*T^2*(M*Real.sqrt M) := hb
      _ = B*(T^2*M*Real.sqrt M) := by ring
      _ ≤ B*(T^ε*Z) := mul_le_mul_of_nonneg_left (hbase.trans hZT) hB
      _ ≤ (C+E+B+1)*T^ε*Z := by
        have hh : B ≤ C+E+B+1 := by linarith
        nlinarith [mul_le_mul_of_nonneg_right hh (mul_nonneg (by positivity : 0 ≤ T^ε) hZ)]

/-- Restricted cubic bound for the actual centered kernel. Exact scales
T^(4/5)<=L<=T and time support length<=T; cutoff fixed before epsilon and
all varying data. This theorem has no open analytic estimate premise. -/
theorem centered_restricted_cubic {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hs : ∀ x, x ∉ Icc l u → a x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T L t₀ t₁ Λ : ℝ) (μ : ℝ → ℝ),
      2 ≤ T → T^((4:ℝ)/5) ≤ L → L ≤ T → t₀ ≤ t₁ → t₁-t₀ ≤ T → 0 ≤ Λ →
      Measurable μ → (∀ t, 0 ≤ μ t) → Integrable μ → Integrable (fun t => μ t^2) →
      (∀ t, t ∉ Icc t₀ t₁ → μ t = 0) →
      ‖kernelCubic (timeMeasure μ) (centeredKernel a l u L)‖ ≤
        C*T^ε*(T^2*(∫ t, μ t^2)*Real.sqrt (∫ t, μ t^2)+T*L*Λ*(∫ t, μ t^2)+
          T*L*(∫ t, μ t)*(∫ ξ in {ξ | Λ < ‖𝓕 (fun t => (μ t:ℂ)) ξ‖}, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^2)) := by
  obtain ⟨C,hC,h⟩ := centered_masked_cubic_estimate ha hl hlu hs hε
  refine ⟨3*C,by positivity,?_⟩
  intro T L t₀ t₁ Λ μ hT hLl hLu ht hlen hΛ hm h0 hi h2 hsup
  have hTp : 0 < T := by linarith
  have hLp : 0 < L := (Real.rpow_pos_of_pos hTp _).trans_le hLl
  let A := {ξ | Λ < ‖𝓕 (fun t => (μ t:ℂ)) ξ‖}
  have hf : Continuous (𝓕 (fun t => (μ t:ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂
      (Complex.ofRealCLM.integrable_comp hi)
  have hA : MeasurableSet A := measurableSet_lt measurable_const hf.measurable.norm
  have hsym : ∀ ξ, -ξ ∈ A ↔ ξ ∈ A := realDensity_level_symmetry μ Λ
  have hh := ordinary_restricted_cubic_of_masked h0 hi h2 hΛ
    (show 0 ≤ C*T^ε by positivity) hTp.le hLp.le
    (kernelCubic (timeMeasure μ) (centeredKernel a l u L))
    (h T L t₀ t₁ μ A hT hLl hLu ht hlen hm h0 hi h2 hsup hA hsym)
  convert hh using 1
  ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.centered_masked_cubic_estimate
#print axioms GuthMaynard.Improvement.centered_restricted_cubic
