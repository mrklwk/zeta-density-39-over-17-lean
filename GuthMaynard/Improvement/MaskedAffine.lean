module
public import GuthMaynard.Improvement.StrengthenedAffine
public import GuthMaynard.Improvement.SparseAffineInput

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped SchwartzMap FourierTransform ContDiff
namespace GuthMaynard.Improvement
open RiemannZeta.GuthMaynard

/-- Smoothness and compact support for arbitrary integrable compact inputs;
no regularity of a measurable mask boundary is required. -/
theorem compact_smoothed_general_schwartz {g : ℝ → ℝ} {a b δ : ℝ}
    (hg : Integrable g) (hδ : 0 < δ)
    (hs : ∀ x, x ∉ Icc a b → g x = 0) :
    ∃ f : 𝓢(ℝ, ℝ), (f : ℝ → ℝ) = smooth (scaledKernel compactKernel δ) g := by
  have hc : HasCompactSupport (scaledKernel compactKernel δ) := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-2*δ) (2*δ)))
    intro x hx
    apply scaled_compactKernel_zero hδ
    by_contra hn
    have hh := abs_le.mp (le_of_not_gt hn)
    exact hx ⟨by linarith [hh.1],hh.2⟩
  have hd : ContDiff ℝ ∞ (scaledKernel compactKernel δ) :=
    contDiff_const.mul (compactKernel_smooth.comp (contDiff_id.div_const δ))
  have hsd : ContDiff ℝ ∞ (smooth (scaledKernel compactKernel δ) g) := by
    rw [smooth_eq_convolution]
    exact hc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hg.locallyIntegrable hd
  have hsc : HasCompactSupport (smooth (scaledKernel compactKernel δ) g) := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (a-2*δ) (b+2*δ)))
    intro x hx
    exact smooth_support_interval (fun t ht => scaled_compactKernel_zero hδ ht) hs hx
  exact ⟨hsc.toSchwartzMap hsd,rfl⟩

/-- Fixed Fourier constants precede every height, width, and measurable input.
The normalization uses the actual output supremum, never inverse mask mass. -/
theorem compact_smoothed_full_input (a b : ℝ) (hab : a ≤ b) :
    ∃ D : ℝ → ℕ → ℝ, (∀ β n, 0 ≤ D β n) ∧
      ∀ (T δ : ℝ) (g : ℝ → ℝ), 2 ≤ T → 0 < δ → δ ≤ 1 → δ⁻¹ ≤ T →
      Integrable g → (∀ x, 0 ≤ g x) → (∀ x, x ∉ Icc a b → g x = 0) →
      FourierSupInput D T (smooth (scaledKernel compactKernel δ) g) := by
  choose C hC h using compact_smoothing_normalized_fourier hab
  refine ⟨fun _ n => C n,fun _ n => (hC n).le,?_⟩
  intro T δ g hT hδ hδ1 hδT hg hg0 hs
  obtain ⟨f,hf⟩ := compact_smoothed_general_schwartz hg hδ hs
  have hsup : ∀ x, smooth (scaledKernel compactKernel δ) g x ≤ sourceSup f := by
    intro x
    rw [← hf, sourceSup_eq_seminorm]
    exact (le_abs_self _).trans (by
      simpa only [gmAffineComplexify_apply, Complex.norm_real, Real.norm_eq_abs] using
        SchwartzMap.norm_le_seminorm (𝕜 := ℝ) (gmAffineComplexify f) x)
  have hU : 0 ≤ sourceSup f := (smooth_nonneg
    (scaledKernel_nonneg compactKernel_nonneg hδ) hg0 0).trans (hsup 0)
  intro β hβ n ξ hξ
  have hh := h n δ hδ hδ1 g hg hg0 hs (sourceSup f) hsup ξ
  have ht : 1 ≤ T^β := Real.one_le_rpow (by linarith) hβ.le
  have hpow : δ⁻¹^n ≤ T^n := pow_le_pow_left₀ (by positivity) hδT n
  have hξp : 0 < |ξ|^n := pow_pos (abs_pos.mpr hξ) n
  have hnum : |ξ|^n * ‖𝓕 (fun x => (smooth (scaledKernel compactKernel δ) g x : ℂ)) ξ‖ ≤
      C n*T^β*T^n*sourceSup f := hh.trans (by
    calc
      _ ≤ T^n*C n*sourceSup f := by gcongr; exact (hC n).le
      _ ≤ C n*T^β*T^n*sourceSup f := by nlinarith [mul_nonneg (mul_nonneg (hC n).le (pow_nonneg (by linarith : 0 ≤ T) n)) hU])
  change _ ≤ C n*T^β*(T/|ξ|)^n*sourceSup (smooth (scaledKernel compactKernel δ) g)
  rw [← hf] at hnum ⊢
  calc
    _ ≤ (C n*T^β*T^n*sourceSup f) / |ξ|^n :=
      (le_div_iff₀ hξp).mpr (by simpa only [mul_comm] using hnum)
    _ = _ := by rw [div_pow]; ring

/-- Actual strengthened affine bound for arbitrary nonnegative measurable
compact inputs. Both original norms are retained, including zero mass. -/
theorem compact_smoothed_unequal_affine (a b C₀ : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hC₀ : 0 ≤ C₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T R K δ : ℝ) (g : ℝ → ℝ),
      2 ≤ T → 1 ≤ K → K ≤ R → R ≤ T^4 →
      0 < δ → δ ≤ 1 → δ ≤ a/4 → δ⁻¹ ≤ T →
      Measurable g → Integrable g → Integrable (fun x => g x^2) →
      (∀ x, 0 ≤ g x) → (∀ x, x ∉ Icc a b → g x = 0) →
      affineAverage R K C₀ (smooth (scaledKernel compactKernel δ) g) ≤
        C*T^ε*(R^2*K^4*(∫ x, g x)^2+R*K^3*(∫ x, g x^2)) := by
  obtain ⟨D,hD,hprofile⟩ := compact_smoothed_full_input a b hab
  obtain ⟨C,hC,h⟩ := strengthened_unequal_affine (a/2) (b+2) C₀
    (by positivity) (by linarith) hC₀ D hD hε
  refine ⟨C,hC,?_⟩
  intro T R K δ g hT hK hKR hRT hδ hδ1 hδa hδT hgm hgi hg2 hg0 hs
  obtain ⟨f,hf⟩ := compact_smoothed_general_schwartz hgi hδ hs
  have hκi := scaledKernel_integrable compactKernel_integrable hδ
  have hκm := scaledKernel_measurable compactKernel_smooth.continuous.measurable δ
  have hκ0 := scaledKernel_nonneg compactKernel_nonneg hδ
  have hmass := scaledKernel_mass hδ compactKernel_mass
  have hfs : ∀ x, x ∉ Icc (a/2) (b+2) → smooth (scaledKernel compactKernel δ) g x = 0 := by
    intro x hx
    apply smooth_support_interval (fun t ht => scaled_compactKernel_zero hδ ht) hs
    intro hh
    exact hx ⟨by linarith [hh.1],by linarith [hh.2]⟩
  have hd : ContDiff ℝ ∞ (smooth (scaledKernel compactKernel δ) g) := by rw [← hf]; exact f.smooth ⊤
  have hm := smooth_mass hκi hgi hmass
  obtain ⟨B,hB,hb⟩ := compactKernel_bound
  have hl2 := smooth_l2_contraction hκm hκi hκ0 (scaledKernel_bound hδ hb) hmass hgm hgi hg2 hg0
  have hh := h T R K _ hT hK hKR hRT hd (smooth_nonneg hκ0 hg0) hfs
    (hprofile T δ g hT hδ hδ1 hδT hgi hg0 hs)
  rw [hm] at hh
  have hK0 : 0 ≤ K := by linarith
  have hR0 : 0 ≤ R := hK0.trans hKR
  exact hh.trans (by gcongr)

/-- The masked affine consumer retains the literal restricted square mass
and restricted fourth moment. The constant precedes the measurable set. -/
theorem masked_unequal_affine (a b C₀ : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hC₀ : 0 ≤ C₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T R K δ : ℝ) (A : Set ℝ) (r : ℝ → ℝ),
      2 ≤ T → 1 ≤ K → K ≤ R → R ≤ T^4 →
      0 < δ → δ ≤ 1 → δ ≤ a/4 → δ⁻¹ ≤ T →
      MeasurableSet A → Measurable r → Integrable (fun x => r x^2) →
      Integrable (fun x => r x^4) → (∀ x, x ∉ Icc a b → r x = 0) →
      affineAverage R K C₀ (squareSmoothing (scaledKernel compactKernel δ) (A.indicator r)) ≤
        C*T^ε*(R^2*K^4*(∫ x in A, r x^2)^2+R*K^3*(∫ x in A, r x^4)) := by
  obtain ⟨C,hC,h⟩ := compact_smoothed_unequal_affine a b C₀ ha hab hC₀ hε
  refine ⟨C,hC,?_⟩
  intro T R K δ A r hT hK hKR hRT hδ hδ1 hδa hδT hA hr hr2 hr4 hs
  let g := A.indicator (fun x => r x^2)
  have hg2 : (fun x => g x^2) = A.indicator (fun x => r x^4) := by
    funext x
    by_cases hx : x ∈ A
    · simp only [g,indicator_of_mem hx]; ring
    · simp [g,hx]
  have hgs : ∀ x, x ∉ Icc a b → g x = 0 := by
    intro x hx
    by_cases hxA : x ∈ A <;> simp [g,hxA,hs x hx]
  have hg0 : ∀ x, 0 ≤ g x := by
    intro x
    by_cases hx : x ∈ A <;> simp [g,hx,sq_nonneg]
  have hgi2 : Integrable (fun x => g x^2) := by rw [hg2]; exact hr4.indicator hA
  have heq : squareSmoothing (scaledKernel compactKernel δ) (A.indicator r) =
      smooth (scaledKernel compactKernel δ) g := by
    funext x
    apply integral_congr_ae
    filter_upwards with y
    by_cases hy : y ∈ A <;> simp [g,hy]
  have hh := h T R K δ g hT hK hKR hRT hδ hδ1 hδa hδT
    ((hr.pow_const 2).indicator hA) (hr2.indicator hA) hgi2 hg0 hgs
  rw [heq]
  simpa only [hg2, g, integral_indicator hA] using hh

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.compact_smoothed_general_schwartz
#print axioms GuthMaynard.Improvement.compact_smoothed_full_input
#print axioms GuthMaynard.Improvement.compact_smoothed_unequal_affine

#print axioms GuthMaynard.Improvement.masked_unequal_affine
