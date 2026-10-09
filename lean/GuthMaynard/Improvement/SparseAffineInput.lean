module
public import GuthMaynard.AffineSource.LargeValuesAffineHeight
public import GuthMaynard.Improvement.CompactNormalization

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped SchwartzMap FourierTransform Convolution ContDiff
namespace GuthMaynard.Improvement
open RiemannZeta.GuthMaynard

/-- The verified height-family endpoint extended to all T>=2 using its actual
finite affine baseline on the bounded initial height interval. -/
theorem sparse_affine_all_heights (D : ℝ → ℕ → ℝ) (hD : ∀ β n, 0 ≤ D β n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ) (f : 𝓢(ℝ, ℝ)) (M : ℕ),
      2 ≤ T → (∀ x, 0 ≤ f x) → GMAffineSupportedOn (1/4:ℝ) (9/4) f →
      GMAffineHeightFourierMassFamilyAtDepth T D 0 f → 0 < M → (M:ℝ) ≤ T^4 →
      gmAffineJ f M ≤ C*T^ε*((M:ℝ)^6*(∫ x, f x)^2+(M:ℝ)^4*(∫ x, f x^2)) := by
  obtain ⟨C,T₀,hC,hT₀,h⟩ := gmAffine_proposition9_1_height_family_native D hD hε
  refine ⟨C+36992*T₀^8,by positivity,?_⟩
  intro T f M hT hf hs hp hM hMT
  have hL2 : 0 ≤ ∫ x, f x^2 := integral_nonneg (fun _ => sq_nonneg _)
  have hW : 0 ≤ (M:ℝ)^6*(∫ x, f x)^2+(M:ℝ)^4*(∫ x, f x^2) := by positivity
  have hTp : 0 < T := by linarith
  have hTe : 1 ≤ T^ε := Real.one_le_rpow (by linarith) hε.le
  by_cases hlarge : T₀ ≤ T
  · exact (h hlarge f hf hs hp hM hMT).trans (by gcongr; exact le_add_of_nonneg_right (by positivity))
  · have hsmall : T ≤ T₀ := le_of_lt (lt_of_not_ge hlarge)
    have hf2 : Integrable (fun x => f x^2) :=
      (memLp_two_iff_integrable_sq f.continuous.aestronglyMeasurable).1 (f.memLp 2)
    have hm2 : (M:ℝ)^2 ≤ T₀^8 := by
      calc
        _ ≤ (T₀^4)^2 := by gcongr; exact hMT.trans (by gcongr)
        _ = _ := by ring
    calc
      _ ≤ 36992*(M:ℝ)^6*(∫ x, f x^2) := gmAffineJ_le_crude hf2 hM
      _ = (36992*(M:ℝ)^2)*((M:ℝ)^4*(∫ x, f x^2)) := by ring
      _ ≤ (36992*T₀^8)*((M:ℝ)^4*(∫ x, f x^2)) := by gcongr
      _ ≤ (36992*T₀^8)*((M:ℝ)^6*(∫ x, f x)^2+(M:ℝ)^4*(∫ x, f x^2)) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity)
      _ ≤ (C+36992*T₀^8)*T^ε*((M:ℝ)^6*(∫ x, f x)^2+(M:ℝ)^4*(∫ x, f x^2)) := by
        apply mul_le_mul_of_nonneg_right _ hW
        have hbase : 0 ≤ 36992*T₀^8 := by positivity
        nlinarith

/-- Arbitrary integrable input on [1/2,2], smoothed by our constructed
compact kernel, has an actual real Schwartz representative. -/
theorem compact_smoothed_schwartz {g : ℝ → ℝ} (hg : Integrable g) {δ : ℝ}
    (hδ : 0 < δ) (hs : ∀ x, x ∉ Icc (1/2:ℝ) 2 → g x = 0) :
    ∃ f : 𝓢(ℝ, ℝ), (f:ℝ→ℝ) = smooth (scaledKernel compactKernel δ) g := by
  have hκc : HasCompactSupport (scaledKernel compactKernel δ) := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-2*δ) (2*δ)))
    intro x hx
    apply scaled_compactKernel_zero hδ
    by_contra hn
    have ha := abs_le.mp (le_of_not_gt hn)
    exact hx ⟨by linarith [ha.1],ha.2⟩
  have hκd : ContDiff ℝ ∞ (scaledKernel compactKernel δ) :=
    contDiff_const.mul (compactKernel_smooth.comp (contDiff_id.div_const δ))
  have hd : ContDiff ℝ ∞ (smooth (scaledKernel compactKernel δ) g) := by
    rw [smooth_eq_convolution]
    exact hκc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hg.locallyIntegrable hκd
  have hc : HasCompactSupport (smooth (scaledKernel compactKernel δ) g) := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (1/2-2*δ) (2+2*δ)))
    intro x hx
    exact smooth_support_interval (fun t ht => scaled_compactKernel_zero hδ ht) hs hx
  exact ⟨hc.toSchwartzMap hd,rfl⟩

/-- A single Fourier coefficient profile works for every input and height.
There is no division by mass, and no height-dependent seminorm hidden in D. -/
theorem compact_smoothed_uniform_profile :
    ∃ D : ℝ → ℕ → ℝ, (∀ β n, 0 ≤ D β n) ∧
      ∀ (g : ℝ → ℝ) (f : 𝓢(ℝ, ℝ)) (δ T : ℝ),
      Integrable g → (∀ x, 0 ≤ g x) → 0 < δ → 2 ≤ T → δ⁻¹ ≤ T →
      (f:ℝ→ℝ) = smooth (scaledKernel compactKernel δ) g →
      GMAffineHeightFourierMassFamilyAtDepth T D 0 f := by
  obtain ⟨κ,hκ⟩ := compactKernel_schwartz
  choose C hC h using (fun n => scaled_smooth_power_bound compactKernel κ hκ compactKernel_integrable n)
  refine ⟨fun _ n => C n,fun _ n => (hC n).le,?_⟩
  intro g f δ T hg hg0 hδ hT hδT hf β hβ n
  have hm : (∫ x, f x) = ∫ x, g x := by
    rw [hf]
    exact smooth_mass (scaledKernel_integrable compactKernel_integrable hδ) hg (scaledKernel_mass hδ compactKernel_mass)
  have hmass : 0 ≤ ∫ x, g x := integral_nonneg hg0
  have hpoint := h n δ hδ g hg hg0
  have hCn := hC n
  have hfC : (gmAffineComplexify f : ℝ → ℂ) = fun x => (smooth (scaledKernel compactKernel δ) g x : ℂ) := by
    funext x
    rw [gmAffineComplexify_apply]
    exact congrArg Complex.ofReal (congrFun hf x)
  have hsn : SchwartzMap.seminorm ℝ n 0 (𝓕 (gmAffineComplexify f)) ≤ δ⁻¹^n*C n*(∫ x, g x) := by
    apply SchwartzMap.seminorm_le_bound' ℝ n 0 _ (by positivity)
    intro ξ
    simpa only [iteratedDeriv_zero, SchwartzMap.fourier_coe, hfC] using hpoint ξ
  have hTp : 0 < T := by linarith
  have hTe : 1 ≤ T^β := Real.one_le_rpow (by linarith) hβ.le
  have hpow : δ⁻¹^n ≤ T^(n+2) := (pow_le_pow_left₀ (inv_nonneg.mpr hδ.le) hδT n).trans
    (pow_le_pow_right₀ (by linarith : 1 ≤ T) (by omega))
  change SchwartzMap.seminorm ℝ n 0 (𝓕 (gmAffineComplexify f)) ≤
    ((2:ℝ)^0*C n)*T^β*T^(n+2)*(∫ x, f x)
  rw [hm, pow_zero, one_mul]
  calc
    _ ≤ δ⁻¹^n*C n*(∫ x, g x) := hsn
    _ ≤ T^(n+2)*C n*(∫ x, g x) := by gcongr
    _ ≤ C n*T^β*T^(n+2)*(∫ x, g x) := by nlinarith [mul_nonneg (mul_nonneg (hC n).le (pow_nonneg hTp.le (n+2))) hmass]

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.sparse_affine_all_heights
#print axioms GuthMaynard.Improvement.compact_smoothed_schwartz
#print axioms GuthMaynard.Improvement.compact_smoothed_uniform_profile
