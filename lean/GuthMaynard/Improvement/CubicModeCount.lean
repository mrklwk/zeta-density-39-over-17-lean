module
public import GuthMaynard.Improvement.RadialRemainder

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace GuthMaynard.Improvement

def cubicModes (U : ℝ) : Finset (ℤ × (ℤ × ℤ)) :=
  (Finset.Icc (-⌊U⌋) ⌊U⌋) ×ˢ ((Finset.Icc (-⌊U⌋) ⌊U⌋) ×ˢ (Finset.Icc (-⌊U⌋) ⌊U⌋))

theorem cubicModes_card {U : ℝ} (hU : 1 ≤ U) : ((cubicModes U).card:ℝ) ≤ 27*U^3 := by
  have hf : 0 ≤ ⌊U⌋ := Int.floor_nonneg.mpr (by linarith)
  have hcZ : ((Finset.Icc (-⌊U⌋) ⌊U⌋).card:ℤ) = 2*⌊U⌋+1 := by
    rw [Int.card_Icc,Int.toNat_of_nonneg (by omega)]
    ring
  have hcR : ((Finset.Icc (-⌊U⌋) ⌊U⌋).card:ℝ) = 2*(⌊U⌋:ℝ)+1 := by exact_mod_cast hcZ
  have hb : ((Finset.Icc (-⌊U⌋) ⌊U⌋).card:ℝ) ≤ 3*U := by
    rw [hcR]
    linarith [Int.floor_le U]
  unfold cubicModes
  rw [Finset.card_product,Finset.card_product]
  push_cast
  calc
    _ ≤ (3*U)*((3*U)*(3*U)) := by gcongr
    _ = _ := by ring

/-- Exact membership in the full symmetric real-frequency truncation. -/
theorem mem_cubicModes (U : ℝ) (m : ℤ × (ℤ × ℤ)) :
    m ∈ cubicModes U ↔ |(m.1:ℝ)| ≤ U ∧ |(m.2.1:ℝ)| ≤ U ∧ |(m.2.2:ℝ)| ≤ U := by
  have hm : ∀ k : ℤ, k ∈ Finset.Icc (-⌊U⌋) ⌊U⌋ ↔ |(k:ℝ)| ≤ U := by
    intro k
    rw [Finset.mem_Icc,abs_le]
    constructor
    · intro hk
      have h₁ : -(k:ℝ) ≤ U := by
        have hz : -k ≤ ⌊U⌋ := by omega
        simpa only [Int.cast_neg] using Int.le_floor.mp hz
      exact ⟨by linarith,Int.le_floor.mp hk.2⟩
    · intro hk
      have h₁ : -k ≤ ⌊U⌋ := Int.le_floor.mpr (by push_cast; linarith)
      exact ⟨by omega,Int.le_floor.mpr hk.2⟩
  simp only [cubicModes,Finset.mem_product,hm]

/-- The actual radial discarded sum for ANY retained subset, with no
unproved cardinality premise. Zero modes may be omitted by taking a subset. -/
theorem radial_truncated_discard_bound {a : ℝ → ℂ}
    (ha : ContDiff ℝ ∞ a) {l u : ℝ} (hlu : l ≤ u) (hs : ∀ r, r ∉ Icc l u → a r = 0)
    (v₀ v₁ y₀ y₁ : ℝ) (hv : v₀ ≤ v₁) (hy : y₀ ≤ y₁) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L H U : ℝ) (S : Finset (ℤ × (ℤ × ℤ))) (μ : ℝ → ℝ),
      0 < H → 1 ≤ U → S ⊆ cubicModes U →
      Measurable μ → (∀ t, 0 ≤ μ t) → Integrable μ →
      ‖(L:ℂ)^3*(∑ m ∈ S, ∫ p in Icc v₀ v₁ ×ˢ Icc y₀ y₁, radialDiscard a μ L H m p)‖ ≤
        C*|L|^3*U^3/H^n*(∫ t, μ t)^3*((v₁-v₀)*(y₁-y₀)) := by
  obtain ⟨C,hC,h⟩ := radial_total_discard_bound ha hlu hs v₀ v₁ y₀ y₁ hv hy n
  refine ⟨27*C,by positivity,?_⟩
  intro L H U S μ hH hU hS hm h0 hi
  have hcle : (S.card:ℝ) ≤ (cubicModes U).card := by exact_mod_cast Finset.card_le_card hS
  have hcard : (S.card:ℝ) ≤ 27*U^3 := hcle.trans (cubicModes_card hU)
  have hmass : 0 ≤ ∫ t, μ t := integral_nonneg h0
  calc
    _ ≤ |L|^3*S.card*C/H^n*(∫ t, μ t)^3*((v₁-v₀)*(y₁-y₀)) := h L H S μ hH hm h0 hi
    _ ≤ |L|^3*(27*U^3)*C/H^n*(∫ t, μ t)^3*((v₁-v₀)*(y₁-y₀)) := by gcongr
    _ = _ := by ring

/-- Homogeneous L2 version of the actual discarded radial mode sum. The
time interval and density vary after the uniform radial constant. -/
theorem radial_truncated_discard_L2 {a : ℝ → ℂ}
    (ha : ContDiff ℝ ∞ a) {l u : ℝ} (hlu : l ≤ u) (hs : ∀ r, r ∉ Icc l u → a r = 0)
    (v₀ v₁ y₀ y₁ : ℝ) (hv : v₀ ≤ v₁) (hy : y₀ ≤ y₁) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L H U t₀ t₁ : ℝ) (S : Finset (ℤ × (ℤ × ℤ))) (μ : ℝ → ℝ),
      0 < H → 1 ≤ U → t₀ ≤ t₁ → S ⊆ cubicModes U →
      Measurable μ → (∀ t, 0 ≤ μ t) → Integrable μ → Integrable (fun t => μ t^2) →
      (∀ t, t ∉ Icc t₀ t₁ → μ t = 0) →
      ‖(L:ℂ)^3*(∑ m ∈ S, ∫ p in Icc v₀ v₁ ×ˢ Icc y₀ y₁, radialDiscard a μ L H m p)‖ ≤
        C*|L|^3*U^3/H^n*((v₁-v₀)*(y₁-y₀))*Real.sqrt (t₁-t₀)^3*Real.sqrt (∫ t, μ t^2)^3 := by
  obtain ⟨C,hC,h⟩ := radial_truncated_discard_bound ha hlu hs v₀ v₁ y₀ y₁ hv hy n
  refine ⟨C,hC,?_⟩
  intro L H U t₀ t₁ S μ hH hU ht hS hm h0 hi h2 hsup
  have hmass := compact_time_mass_bound ht hm h0 h2 hsup
  have hm0 : 0 ≤ ∫ t, μ t := integral_nonneg h0
  calc
    _ ≤ C*|L|^3*U^3/H^n*(∫ t, μ t)^3*((v₁-v₀)*(y₁-y₀)) := h L H U S μ hH hU hS hm h0 hi
    _ ≤ C*|L|^3*U^3/H^n*(Real.sqrt (t₁-t₀)*Real.sqrt (∫ t, μ t^2))^3*((v₁-v₀)*(y₁-y₀)) := by gcongr
    _ = _ := by ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.cubicModes_card
#print axioms GuthMaynard.Improvement.mem_cubicModes
#print axioms GuthMaynard.Improvement.radial_truncated_discard_bound

#print axioms GuthMaynard.Improvement.radial_truncated_discard_L2
