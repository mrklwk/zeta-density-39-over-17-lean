module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

 
                             

                                                                              
                                                                          
                                                                


namespace TaoTrudgianYang2025

private theorem sortedList_length_le_interval
    (W : Finset ℝ)
    (hsep : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → 1 ≤ |x - y|) :
    ∀ (L : List ℝ), L.Pairwise (· < ·) →
      (∀ x ∈ L, x ∈ W) →
      ∀ a b : ℝ, (∀ x ∈ L, a ≤ x ∧ x ≤ b) →
        0 ≤ b - a → (L.length : ℝ) ≤ b - a + 1 := by
  intro L hsorted hsub
  induction L with
  | nil =>
      intro a b _ hab
      simp
      linarith
  | cons x xs ih =>
      cases xs with
      | nil =>
          intro a b hmem _
          have hx := hmem x (by simp)
          simp
          linarith
      | cons y ys =>
          intro a b hmem hab
          have hxmem : x ∈ W := hsub x (by simp)
          have hymem : y ∈ W := hsub y (by simp)
          have hxy : x < y :=
            (List.pairwise_cons_cons_iff_of_trans.mp hsorted).1
          have hgap := hsep y hymem x hxmem (ne_of_gt hxy)
          rw [abs_of_nonneg (sub_nonneg.mpr hxy.le)] at hgap
          have htailSub : ∀ z ∈ y :: ys, z ∈ W := by
            intro z hz
            exact hsub z (by simp [hz])
          have htailMem : ∀ z ∈ y :: ys, y ≤ z ∧ z ≤ b := by
            intro z hz
            have hyz : y ≤ z := by
              rcases List.mem_cons.mp hz with hzy | hzys
              · subst z
                exact le_rfl
              · have hyz' := hsorted.tail.rel_head_tail (by simpa using hzys)
                simpa using hyz'.le
            exact ⟨hyz, (hmem z (by simp [hz])).2⟩
          have htail := ih hsorted.tail htailSub y b htailMem (by
            have hyb := (hmem y (by simp)).2
            linarith)
          have hax := (hmem x (by simp)).1
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          norm_num at htail ⊢
          linarith

theorem oneSeparated_card_cast_le_interval_length_add_one
    (W : Finset ℝ)
    (hsep : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → 1 ≤ |x - y|)
    {a b : ℝ} (hab : 0 ≤ b - a)
    (hmem : ∀ x ∈ W, a ≤ x ∧ x ≤ b) :
    (W.card : ℝ) ≤ b - a + 1 := by
  let L : List ℝ := W.sort
  have hsorted : L.Pairwise (· < ·) := by
    exact List.sortedLT_iff_pairwise.mp (by
      simpa [L] using Finset.sortedLT_sort W)
  have hsub : ∀ x ∈ L, x ∈ W := by
    intro x hx
    change x ∈ W.sort at hx
    exact (Finset.mem_sort (· ≤ ·)).mp hx
  have hmemL : ∀ x ∈ L, a ≤ x ∧ x ≤ b := by
    intro x hx
    exact hmem x (hsub x hx)
  simpa [L] using
    sortedList_length_le_interval W hsep L hsorted hsub a b hmemL hab

                                                          
end TaoTrudgianYang2025
