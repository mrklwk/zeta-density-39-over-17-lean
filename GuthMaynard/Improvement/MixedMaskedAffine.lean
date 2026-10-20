module
public import GuthMaynard.Improvement.MixedMaskedInput

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped SchwartzMap FourierTransform ContDiff
namespace GuthMaynard.Improvement
open RiemannZeta.GuthMaynard

/-- Ordinary smooth compact inputs with independent affine shells. -/
theorem mixed_compact_affine
    (a b C₀ : ℝ) (ha : 0 < a) (hab : a ≤ b) (hC₀ : 0 ≤ C₀)
    (D : ℝ → ℕ → ℝ) (hD : ∀ β n, 0 ≤ D β n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T R K B Q : ℝ) (f : ℝ → ℝ) (S : Finset (ℤ × (ℤ × ℤ))),
      2 ≤ T → 1 ≤ K → K ≤ R → 1 ≤ B → B ≤ R → 1 ≤ Q → Q ≤ K → R ≤ T^4 →
      ContDiff ℝ ∞ f → (∀ x, 0 ≤ f x) →
      (∀ x, x ∉ Icc a b → f x = 0) → FourierSupInput D T f → (∀ p ∈ S, InMixedAffineBox B Q R C₀ p) →
      affineIndexIntegral f S ≤ C*T^ε*
        (R^2*K^4*(∫ x, f x)^2+R*K^3*(∫ x, f x^2)) := by
  let L := ⌈b⌉₊
  have hL : 0 < L := Nat.ceil_pos.mpr (ha.trans_le hab)
  have hbL : b ≤ (L:ℝ) := Nat.le_ceil _
  obtain ⟨C,hC,h⟩ := mixed_affine_full_finite D hD L hL C₀ hC₀ hε
  refine ⟨C,hC,?_⟩
  intro T R K B Q f S hT hK hKR hB hBR hQ hQK hRT hfd hf hs hp hbox
  have hc : HasCompactSupport f := HasCompactSupport.intro isCompact_Icc hs
  let fs : 𝓢(ℝ, ℝ) := hc.toSchwartzMap hfd
  have hfs : GMAffineSupportedOn 0 L fs := by
    intro x hx
    apply hs
    intro habx
    exact hx ⟨ha.le.trans habx.1,habx.2.trans hbL⟩
  have hfp : FourierSupFamily D T fs := by
    intro β hβ n ξ hξ
    have hh := hp β hβ n ξ hξ
    rw [show sourceSup f = SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify fs) from sourceSup_eq_seminorm fs] at hh
    exact hh
  exact h T R K B Q fs S hT hK hKR hB hBR hQ hQK hRT hf hfs hfp hbox

theorem compact_smoothed_mixed_affine (a b C₀ : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hC₀ : 0 ≤ C₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T R K B Q δ : ℝ) (g : ℝ → ℝ) (S : Finset (ℤ × (ℤ × ℤ))),
      2 ≤ T → 1 ≤ K → K ≤ R → 1 ≤ B → B ≤ R → 1 ≤ Q → Q ≤ K → R ≤ T^4 →
      0 < δ → δ ≤ 1 → δ ≤ a/4 → δ⁻¹ ≤ T →
      Measurable g → Integrable g → Integrable (fun x => g x^2) →
      (∀ x, 0 ≤ g x) → (∀ x, x ∉ Icc a b → g x = 0) → (∀ p ∈ S, InMixedAffineBox B Q R C₀ p) →
      affineIndexIntegral (smooth (scaledKernel compactKernel δ) g) S ≤
        C*T^ε*(R^2*K^4*(∫ x, g x)^2+R*K^3*(∫ x, g x^2)) := by
  obtain ⟨D,hD,hprofile⟩ := compact_smoothed_full_input a b hab
  obtain ⟨C,hC,h⟩ := mixed_compact_affine (a/2) (b+2) C₀
    (by positivity) (by linarith) hC₀ D hD hε
  refine ⟨C,hC,?_⟩
  intro T R K B Q δ g S hT hK hKR hB hBR hQ hQK hRT hδ hδ1 hδa hδT hgm hgi hg2 hg0 hs hbox
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
  obtain ⟨W,hW,hb⟩ := compactKernel_bound
  have hl2 := smooth_l2_contraction hκm hκi hκ0 (scaledKernel_bound hδ hb) hmass hgm hgi hg2 hg0
  have hh := h T R K B Q _ S hT hK hKR hB hBR hQ hQK hRT hd (smooth_nonneg hκ0 hg0) hfs
    (hprofile T δ g hT hδ hδ1 hδT hgi hg0 hs) hbox
  rw [hm] at hh
  have hK0 : 0 ≤ K := by linarith
  have hR0 : 0 ≤ R := hK0.trans hKR
  exact hh.trans (by gcongr)

/-- The masked affine consumer retains the literal restricted square mass
and restricted fourth moment. The constant precedes the measurable set. -/
theorem masked_mixed_affine (a b C₀ : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hC₀ : 0 ≤ C₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T R K B Q δ : ℝ) (A : Set ℝ) (r : ℝ → ℝ) (S : Finset (ℤ × (ℤ × ℤ))),
      2 ≤ T → 1 ≤ K → K ≤ R → 1 ≤ B → B ≤ R → 1 ≤ Q → Q ≤ K → R ≤ T^4 →
      0 < δ → δ ≤ 1 → δ ≤ a/4 → δ⁻¹ ≤ T →
      MeasurableSet A → Measurable r → Integrable (fun x => r x^2) →
      Integrable (fun x => r x^4) → (∀ x, x ∉ Icc a b → r x = 0) → (∀ p ∈ S, InMixedAffineBox B Q R C₀ p) →
      affineIndexIntegral (squareSmoothing (scaledKernel compactKernel δ) (A.indicator r)) S ≤
        C*T^ε*(R^2*K^4*(∫ x in A, r x^2)^2+R*K^3*(∫ x in A, r x^4)) := by
  obtain ⟨C,hC,h⟩ := compact_smoothed_mixed_affine a b C₀ ha hab hC₀ hε
  refine ⟨C,hC,?_⟩
  intro T R K B Q δ A r S hT hK hKR hB hBR hQ hQK hRT hδ hδ1 hδa hδT hA hr hr2 hr4 hs hbox
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
  have hh := h T R K B Q δ g S hT hK hKR hB hBR hQ hQK hRT hδ hδ1 hδa hδT
    ((hr.pow_const 2).indicator hA) (hr2.indicator hA) hgi2 hg0 hgs hbox
  rw [heq]
  simpa only [hg2, g, integral_indicator hA] using hh

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.mixed_compact_affine
#print axioms GuthMaynard.Improvement.compact_smoothed_mixed_affine
#print axioms GuthMaynard.Improvement.masked_mixed_affine
