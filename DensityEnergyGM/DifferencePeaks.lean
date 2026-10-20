module
public import DensityEnergyGM.DifferenceFloorEnergy

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment

/-- Choose an actual maximizing ordered pair in each occupied difference
cell. No supremum over a continuous interval is introduced. -/
theorem exists_difference_peak_representatives (W : Finset ℝ) (f : ℝ → ℝ) :
    ∃ p : ℤ → ℝ × ℝ, ∀ j ∈ differenceFloorSupport W,
      p j ∈ differenceOrdinatePairs W ∧ differenceFloor (p j) = j ∧
        ∀ q ∈ differenceOrdinatePairs W, differenceFloor q = j →
          f (q.1 - q.2) ≤ f ((p j).1 - (p j).2) := by
  classical
  have hnonempty : ∀ j ∈ differenceFloorSupport W,
      ((differenceOrdinatePairs W).filter fun q => differenceFloor q = j).Nonempty := by
    intro j hj
    obtain ⟨q, hq, hfloor⟩ := Finset.mem_image.mp hj
    exact ⟨q, Finset.mem_filter.mpr ⟨hq, hfloor⟩⟩
  have hmax : ∀ j ∈ differenceFloorSupport W,
      ∃ p ∈ (differenceOrdinatePairs W).filter (fun q => differenceFloor q = j),
        ∀ q ∈ (differenceOrdinatePairs W).filter (fun q => differenceFloor q = j),
          f (q.1 - q.2) ≤ f (p.1 - p.2) := by
    intro j hj
    exact Finset.exists_max_image _ (fun q => f (q.1 - q.2)) (hnonempty j hj)
  let p : ℤ → ℝ × ℝ := fun j => if hj : j ∈ differenceFloorSupport W then
    Classical.choose (hmax j hj) else (0, 0)
  refine ⟨p, ?_⟩
  intro j hj
  dsimp only [p]
  rw [dite_eq_left hj]
  have h := Classical.choose_spec (hmax j hj)
  exact ⟨(Finset.mem_filter.mp h.1).1, (Finset.mem_filter.mp h.1).2,
    fun q hq hfloor => h.2 q (Finset.mem_filter.mpr ⟨hq, hfloor⟩)⟩

/-- Representatives of distinct cells in one residue class modulo three
are one-separated, including closed cell-endpoint cases. -/
theorem difference_floor_residue_separated {x y : ℝ} {i j : ℤ}
    (hx : ⌊x⌋ = i) (hy : ⌊y⌋ = j) (hmod : i % 3 = j % 3) (hne : i ≠ j) :
    1 ≤ |x - y| := by
  have hiL := Int.floor_le x
  have hiU := Int.lt_floor_add_one x
  have hjL := Int.floor_le y
  have hjU := Int.lt_floor_add_one y
  rw [hx] at hiL hiU
  rw [hy] at hjL hjU
  have hgap : i + 3 ≤ j ∨ j + 3 ≤ i := by omega
  rcases hgap with hgap | hgap
  · have hgapReal : (i : ℝ) + 3 ≤ j := by exact_mod_cast hgap
    have h := neg_le_abs (x - y)
    linarith
  · have hgapReal : (j : ℝ) + 3 ≤ i := by exact_mod_cast hgap
    have h := le_abs_self (x - y)
    linarith

end Montgomery.RationalMoment
