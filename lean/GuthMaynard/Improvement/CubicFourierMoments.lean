import GuthMaynard.Improvement.CubicScaledStrip
import GuthMaynard.Improvement.RatioFourierInput
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped FourierTransform
namespace GuthMaynard.Improvement

/-- The actual finite strip theorem for ordinary Fourier input, with two
independent measurable frequency masks. No symmetry or boundary regularity
of either mask is assumed. Constants precede the density and both masks. -/
theorem cubic_fourier_moments (a b c d : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c) (hcd : c ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ η C T₀ : ℝ, 0 < η ∧ η < (4:ℝ)/5 ∧ 0 < C ∧ 2 ≤ T₀ ∧
    ∀ (T L : ℝ) (μ : ℝ → ℝ) (A D : Set ℝ) (S : Finset (ℤ × (ℤ × ℤ))),
      T₀ ≤ T → T^((4:ℝ)/5) ≤ L → L ≤ T →
      (∀ t, 0 ≤ μ t) → Integrable μ → Integrable (fun t => μ t^2) →
      MeasurableSet A → MeasurableSet D →
      (∀ m ∈ S, m.1 ∈ poissonModes (T^(1+η)/L) ∧
        m.2.1 ∈ poissonModes (T^(1+η)/L) ∧ m.2.2 ∈ poissonModes (T^(1+η)/L)) →
      let r₀ := ratioFourierInput μ c d
      let r := (mellinFrequency ⁻¹' D).indicator r₀
      IntegrableOn (fun v => (mellinFrequency ⁻¹' A).indicator r₀ v *
        ∑ m ∈ S, cubicStripMass r L (T^η) m v) (Icc a b) ∧
      L^3*(∫ v in Icc a b, (mellinFrequency ⁻¹' A).indicator r₀ v *
        ∑ m ∈ S, cubicStripMass r L (T^η) m v) ≤
      C*T^ε*Real.sqrt (∫ ξ in A, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^2)*
        (T^2*(∫ ξ in D, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^2)+
          T*L*Real.sqrt (∫ ξ in D, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^4)) := by
  obtain ⟨η,C,T₀,hη,hη1,hC,hT₀,h⟩ := cubic_scaled_strip a b c d ha hab hc hcd hε
  let K := 2*Real.pi*d
  let J := 1+K
  have hd : 0 < d := hc.trans_le hcd
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hJ : 0 < J := by dsimp [J]; positivity
  have hKJ : K ≤ J := by dsimp [J]; linarith
  have hrootK : Real.sqrt K ≤ J := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hJ.le,by dsimp [J]; nlinarith [sq_nonneg K]⟩
  refine ⟨η,C*J^2,T₀,hη,hη1,by positivity,hT₀,?_⟩
  intro T L μ A D S hT hLl hLu h0 h1 h2 hA hD hS
  dsimp only
  let r₀ := ratioFourierInput μ c d
  let A₀ := mellinFrequency ⁻¹' A
  let D₀ := mellinFrequency ⁻¹' D
  let r := D₀.indicator r₀
  have hmf : Measurable mellinFrequency := by unfold mellinFrequency; fun_prop
  have hA₀ : MeasurableSet A₀ := hA.preimage hmf
  have hD₀ : MeasurableSet D₀ := hD.preimage hmf
  have hm₀ : Measurable r₀ := ratioFourierInput_measurable h1 c d
  have hsq₀ : Integrable (fun v => r₀ v^2) := ratioFourierInput_square_integrable hc hcd h1 h2
  have hfour₀ : Integrable (fun v => r₀ v^4) := ratioFourierInput_fourth_integrable hc hcd h0 h1 h2
  have hmem₀ : MemLp r₀ 2 := (memLp_two_iff_integrable_sq hm₀.aestronglyMeasurable).mpr hsq₀
  have hnon₀ : ∀ v, 0 ≤ r₀ v := ratioFourierInput_nonneg μ c d
  have hmr : Measurable r := hm₀.indicator hD₀
  have hnonr : ∀ v, 0 ≤ r v := by intro v; exact indicator_nonneg (fun x _ => hnon₀ x) v
  have hpow (n : ℕ) (hn : n ≠ 0) : (fun v => r v^n) = D₀.indicator (fun v => r₀ v^n) := by
    funext v
    by_cases hv : v ∈ D₀ <;> simp [r,hv,hn]
  have hsqr : Integrable (fun v => r v^2) := by rw [hpow 2 (by norm_num)]; exact hsq₀.indicator hD₀
  have hfourr : Integrable (fun v => r v^4) := by rw [hpow 4 (by norm_num)]; exact hfour₀.indicator hD₀
  have hs : ∀ v, v ∉ Icc c d → r v = 0 := by
    intro v hv
    by_cases hD : v ∈ D₀ <;> simp [r,hD,r₀,ratioFourierInput_off hv]
  obtain ⟨hint,hbound⟩ := h T L r₀ r A₀ S hT hLl hLu hA₀ hm₀ hmem₀ hnon₀
    hmr hsqr hfourr hnonr hs hS
  refine ⟨hint,hbound.trans ?_⟩
  let FA := ∫ ξ in A, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^2
  let FD := ∫ ξ in D, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^2
  let ED := ∫ ξ in D, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^4
  have hFA : 0 ≤ FA := integral_nonneg (fun _ => sq_nonneg _)
  have hFD : 0 ≤ FD := integral_nonneg (fun _ => sq_nonneg _)
  have hED : 0 ≤ ED := integral_nonneg (fun _ => by positivity)
  have hmA : (∫ v in A₀, r₀ v^2 ∂volume.restrict (Icc a b)) ≤ K*FA := by
    calc
      _ = ∫ v in Icc a b, A₀.indicator (fun v => r₀ v^2) v := (integral_indicator hA₀).symm
      _ ≤ ∫ v, A₀.indicator (fun v => r₀ v^2) v :=
        setIntegral_le_integral (hsq₀.indicator hA₀)
          (Filter.Eventually.of_forall (fun v => indicator_nonneg (fun x _ => sq_nonneg (r₀ x)) v))
      _ = ∫ v in A₀, r₀ v^2 := integral_indicator hA₀
      _ ≤ _ := ratioFourierInput_masked_square hc hcd hA h1 h2
  have hmD : (∫ v, r v^2) ≤ K*FD := by
    rw [hpow 2 (by norm_num),integral_indicator hD₀]
    exact ratioFourierInput_masked_square hc hcd hD h1 h2
  have heD : (∫ v, r v^4) ≤ K*ED := by
    rw [hpow 4 (by norm_num),integral_indicator hD₀]
    exact ratioFourierInput_masked_fourth hc hcd hD h0 h1 h2
  have hrootA : Real.sqrt (∫ v in A₀, r₀ v^2 ∂volume.restrict (Icc a b)) ≤ J*Real.sqrt FA := by
    calc
      _ ≤ Real.sqrt (K*FA) := Real.sqrt_le_sqrt hmA
      _ = Real.sqrt K*Real.sqrt FA := Real.sqrt_mul hK _
      _ ≤ _ := mul_le_mul_of_nonneg_right hrootK (Real.sqrt_nonneg _)
  have hrootD : Real.sqrt (∫ v, r v^4) ≤ J*Real.sqrt ED := by
    calc
      _ ≤ Real.sqrt (K*ED) := Real.sqrt_le_sqrt heD
      _ = Real.sqrt K*Real.sqrt ED := Real.sqrt_mul hK _
      _ ≤ _ := mul_le_mul_of_nonneg_right hrootK (Real.sqrt_nonneg _)
  have hmD' : (∫ v, r v^2) ≤ J*FD := hmD.trans (mul_le_mul_of_nonneg_right hKJ hFD)
  have hTp : 0 < T := by linarith
  have hLp : 0 < L := (Real.rpow_pos_of_pos hTp _).trans_le hLl
  calc
    _ ≤ C*T^ε*(J*Real.sqrt FA)*(T^2*(J*FD)+T*L*(J*Real.sqrt ED)) := by gcongr
    _ = _ := by dsimp only [FA,FD,ED]; ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.cubic_fourier_moments
