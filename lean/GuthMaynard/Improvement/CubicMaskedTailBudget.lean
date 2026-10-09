module
public import GuthMaynard.Improvement.CubicMaskedStrip
public import GuthMaynard.Improvement.RadialScaleBudget

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace GuthMaynard.Improvement

/-- Actual complex masked far sum; all three measurable masks vary after
the constant. The full L cubed and exact integer mode count are retained. -/
theorem masked_radial_truncated_discard_bound {a : ℝ → ℂ}
    (ha : ContDiff ℝ ∞ a) {l u : ℝ} (hlu : l ≤ u)
    (hs : ∀ r, r ∉ Icc l u → a r = 0)
    (v₀ v₁ y₀ y₁ : ℝ) (hv : v₀ ≤ v₁) (hy : y₀ ≤ y₁) (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (L H U : ℝ) (S : Finset (ℤ × (ℤ × ℤ)))
      (μ : ℝ → ℝ) (A B C : Set ℝ),
      0 < H → 1 ≤ U → S ⊆ cubicModes U →
      MeasurableSet A → MeasurableSet B → MeasurableSet C →
      Measurable μ → (∀ t, 0 ≤ μ t) → Integrable μ →
      ‖(L:ℂ)^3*(∑ m ∈ S, ∫ p in Icc v₀ v₁ ×ˢ Icc y₀ y₁,
        radialDiscard a μ L H m p*ratioMaskProduct A B C p)‖ ≤
      D*|L|^3*U^3/H^n*(∫ t, μ t)^3*((v₁-v₀)*(y₁-y₀)) := by
  obtain ⟨D,hD,h⟩ := masked_radial_total_discard_bound ha hlu hs v₀ v₁ y₀ y₁ hv hy n
  refine ⟨27*D,by positivity,?_⟩
  intro L H U S μ A B C hH hU hS hA hB hC hm h0 hi
  have hcard : (S.card:ℝ) ≤ 27*U^3 := by
    have hh : (S.card:ℝ) ≤ (cubicModes U).card := by exact_mod_cast Finset.card_le_card hS
    exact hh.trans (cubicModes_card hU)
  have hmass : 0 ≤ ∫ t, μ t := integral_nonneg h0
  calc
    _ ≤ |L|^3*S.card*D/H^n*(∫ t, μ t)^3*((v₁-v₀)*(y₁-y₀)) :=
      h L H S μ A B C hH hA hB hC hm h0 hi
    _ ≤ |L|^3*(27*U^3)*D/H^n*(∫ t, μ t)^3*((v₁-v₀)*(y₁-y₀)) := by gcongr
    _ = _ := by ring

/-- The actual masked discarded complex sum is uniformly negligible.
The decay order is fixed from eta before the constant and before every
scale, mode set, measurable mask, support interval, and time density. -/
theorem masked_radial_discard_negligible {a : ℝ → ℂ}
    (ha : ContDiff ℝ ∞ a) {l u : ℝ} (hlu : l ≤ u)
    (hs : ∀ r, r ∉ Icc l u → a r = 0)
    (v₀ v₁ y₀ y₁ : ℝ) (hv : v₀ ≤ v₁) (hy : y₀ ≤ y₁)
    {η : ℝ} (hη : 0 < η) :
    ∃ D : ℝ, 0 < D ∧ ∀ (T L t₀ t₁ : ℝ) (S : Finset (ℤ × (ℤ × ℤ)))
      (μ : ℝ → ℝ) (A B C : Set ℝ),
      1 ≤ T → 0 < L → L ≤ T^(1+η) → t₀ ≤ t₁ → t₁-t₀ ≤ T →
      S ⊆ cubicModes (T^(1+η)/L) →
      MeasurableSet A → MeasurableSet B → MeasurableSet C →
      Measurable μ → (∀ t, 0 ≤ μ t) → Integrable μ → Integrable (fun t => μ t^2) →
      (∀ t, t ∉ Icc t₀ t₁ → μ t = 0) →
      ‖(L:ℂ)^3*(∑ m ∈ S, ∫ p in Icc v₀ v₁ ×ˢ Icc y₀ y₁,
        radialDiscard a μ L (T^η) m p*ratioMaskProduct A B C p)‖ ≤
      D*T^(-100:ℝ)*((v₁-v₀)*(y₁-y₀))*Real.sqrt (∫ t, μ t^2)^3 := by
  obtain ⟨n,hn⟩ := choose_radial_discard_order hη
  obtain ⟨D,hD,h⟩ := masked_radial_truncated_discard_bound ha hlu hs v₀ v₁ y₀ y₁ hv hy n
  refine ⟨D,hD,?_⟩
  intro T L t₀ t₁ S μ A B C hT hL hLT ht hlen hS hA hB hC hm h0 hi h2 hsup
  have hTp : 0 < T := by linarith
  have hH : 0 < T^η := Real.rpow_pos_of_pos hTp _
  have hU : 1 ≤ T^(1+η)/L := (le_div_iff₀ hL).mpr (by simpa using hLT)
  have hsqrt : Real.sqrt (t₁-t₀) ≤ T := (Real.sqrt_le_iff).mpr ⟨hTp.le,by nlinarith⟩
  have hmass : (∫ t, μ t) ≤ T*Real.sqrt (∫ t, μ t^2) :=
    (compact_time_mass_bound ht hm h0 h2 hsup).trans (by gcongr)
  have hm0 : 0 ≤ ∫ t, μ t := integral_nonneg h0
  have he : |L|^3*(T^(1+η)/L)^3*T^3 = T^(6+3*η) := by
    rw [abs_of_pos hL,div_pow]
    have hh : L^3*((T^(1+η))^(3:ℕ)/L^3)*T^3 = (T^(1+η))^(3:ℕ)*T^3 := by field_simp
    rw [hh,← Real.rpow_natCast (T^(1+η)) 3,← Real.rpow_mul hTp.le,
      ← Real.rpow_natCast T 3,← Real.rpow_add hTp]
    congr 1
    norm_num
    ring
  calc
    _ ≤ D*|L|^3*(T^(1+η)/L)^3/(T^η)^n*(∫ t, μ t)^3*((v₁-v₀)*(y₁-y₀)) :=
      h L (T^η) (T^(1+η)/L) S μ A B C hH hU hS hA hB hC hm h0 hi
    _ ≤ D*|L|^3*(T^(1+η)/L)^3/(T^η)^n*
        (T*Real.sqrt (∫ t, μ t^2))^3*((v₁-v₀)*(y₁-y₀)) := by gcongr
    _ = D*(T^(6+3*η)/(T^η)^n)*((v₁-v₀)*(y₁-y₀))*Real.sqrt (∫ t, μ t^2)^3 := by
      rw [← he]
      ring
    _ ≤ _ := by gcongr; exact hn T hT

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.masked_radial_truncated_discard_bound
#print axioms GuthMaynard.Improvement.masked_radial_discard_negligible
