module
public import MathCollab.Density.ZeroSeparation
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace GuthMaynard.Improvement

/-- A bounded measurable or nonmeasurable level set has volume at most twice
any uniform bound for the cardinalities of its one-separated finite subsets. -/
theorem level_volume_of_separated_bound {S : Set ℝ} {a b B : ℝ}
    (hS : S ⊆ Icc a b)
    (hcard : ∀ W : Finset ℝ, (∀ x ∈ W, x ∈ S) →
      (∀ x ∈ W, ∀ y ∈ W, x ≠ y → 1 ≤ |x-y|) → (W.card:ℝ) ≤ B) :
    volume.real S ≤ 2*B := by
  classical
  let K := (Finset.Icc ⌊a⌋ ⌊b⌋).filter (fun k => ∃ x ∈ S, ⌊x⌋ = k)
  have hK (x : ℝ) (hx : x ∈ S) : ⌊x⌋ ∈ K := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_,?_⟩,x,hx,rfl⟩
    · exact Int.floor_mono (hS hx).1
    · exact Int.floor_mono (hS hx).2
  have hex : ∀ k : ℤ, ∃ x : ℝ, k ∈ K → x ∈ S ∧ ⌊x⌋ = k := by
    intro k
    by_cases hk : k ∈ K
    · obtain ⟨x,hx,he⟩ := (Finset.mem_filter.mp hk).2
      exact ⟨x,fun _ => ⟨hx,he⟩⟩
    · exact ⟨0,fun h => (hk h).elim⟩
  choose f hf using hex
  obtain ⟨J,hJK,hcount,hpar⟩ := MathCollab.Density.occupied_bins_parity K
  have hfJ : ∀ k ∈ J, f k ∈ S ∧ ⌊f k⌋ = k := fun k hk => hf k (hJK hk)
  have hinj : Set.InjOn f (J : Set ℤ) := by
    intro k hk l hl he
    rw [← (hfJ k hk).2, ← (hfJ l hl).2,he]
  have hb := hcard (J.image f) (by
    intro x hx
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
    exact (hfJ k hk).1) (by
    intro x hx y hy hxy
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hy
    apply MathCollab.Density.same_parity_bins_separated
    · rw [(hfJ k hk).2,(hfJ l hl).2]
      intro he
      exact hxy (congrArg f he)
    · rw [(hfJ k hk).2,(hfJ l hl).2]
      exact hpar k hk l hl)
  rw [Finset.card_image_of_injOn hinj] at hb
  have hcover : S ⊆ ⋃ k ∈ K, Ico (k:ℝ) ((k:ℝ)+1) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⌊x⌋,mem_iUnion.mpr ⟨hK x hx,
      ⟨Int.floor_le x,Int.lt_floor_add_one x⟩⟩⟩
  have hm : volume S ≤ (K.card : ℝ≥0∞) := by
    calc
      _ ≤ volume (⋃ k ∈ K, Ico (k:ℝ) ((k:ℝ)+1)) := measure_mono hcover
      _ ≤ ∑ k ∈ K, volume (Ico (k:ℝ) ((k:ℝ)+1)) := measure_biUnion_finset_le _ _
      _ = _ := by simp
  have hmreal : volume.real S ≤ (K.card:ℝ) := by
    simpa [Measure.real] using ENNReal.toReal_mono (by simp : (K.card:ℝ≥0∞) ≠ ⊤) hm
  have hcounts : (K.card:ℝ) ≤ 2*(J.card:ℝ) := by exact_mod_cast hcount
  linarith

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.level_volume_of_separated_bound
