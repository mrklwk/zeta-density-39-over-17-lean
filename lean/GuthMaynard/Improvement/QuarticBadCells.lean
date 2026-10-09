import GuthMaynard.Improvement.QuarticCellGeometry
import GuthMaynard.Improvement.ClassicalLargeValues
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- A three-interval count uses the same length T on each interval; the
classical range T≤N² is therefore preserved. Endpoints may overlap harmlessly. -/
theorem separated_three_intervals {T B : ℝ} (W : Finset ℝ)
    (hsep : MathCollab.Density.oneSeparated W) (hw : ∀ t ∈ W, t ∈ Icc (-T) (2*T))
    (hb : ∀ (Z : Finset ℝ) (s : ℝ), Z ⊆ W → (∀ t ∈ Z, t ∈ Icc s (s+T)) →
      MathCollab.Density.oneSeparated Z → (Z.card:ℝ) ≤ B) : (W.card:ℝ) ≤ 3*B := by
  classical
  let Z₁ := W.filter (fun t => t ∈ Icc (-T) 0)
  let Z₂ := W.filter (fun t => t ∈ Icc (0:ℝ) T)
  let Z₃ := W.filter (fun t => t ∈ Icc T (2*T))
  have hsub₁ : Z₁ ⊆ W := Finset.filter_subset _ _
  have hsub₂ : Z₂ ⊆ W := Finset.filter_subset _ _
  have hsub₃ : Z₃ ⊆ W := Finset.filter_subset _ _
  have h₁ : (Z₁.card:ℝ) ≤ B := hb Z₁ (-T) hsub₁ (by
    intro t ht; simpa using (Finset.mem_filter.mp ht).2)
    (MathCollab.Density.oneSeparated_subset hsep hsub₁)
  have h₂ : (Z₂.card:ℝ) ≤ B := hb Z₂ 0 hsub₂ (by
    intro t ht; simpa using (Finset.mem_filter.mp ht).2)
    (MathCollab.Density.oneSeparated_subset hsep hsub₂)
  have h₃ : (Z₃.card:ℝ) ≤ B := hb Z₃ T hsub₃ (by
    intro t ht; simpa only [two_mul] using (Finset.mem_filter.mp ht).2)
    (MathCollab.Density.oneSeparated_subset hsep hsub₃)
  have hcover : W ⊆ Z₁ ∪ Z₂ ∪ Z₃ := by
    intro t ht
    obtain ⟨hlo,hhi⟩ := hw t ht
    by_cases h0 : t ≤ 0
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ht,hlo,h0⟩))
    · by_cases hT : t ≤ T
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ht,by linarith,hT⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ht,by linarith,hhi⟩)
  have hcard : W.card ≤ Z₁.card+Z₂.card+Z₃.card :=
    (Finset.card_le_card hcover).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hc : (W.card:ℝ) ≤ (Z₁.card:ℝ)+Z₂.card+Z₃.card := by exact_mod_cast hcard
  linarith

/-- Actual bad-cell count from the audited classical large-values theorem,
with no analytic premise. -/
theorem quartic_bad_cells_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N T U : ℝ, 2 ≤ N → N ≤ T → T ≤ N^2 → 0 < U →
      ∀ a : ℕ → ℂ, (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
      ((occupiedRealCells ({x | U < ‖boundedPolynomial N a x‖} ∩ Icc (-T) (2*T))
        (-T) (2*T)).card:ℝ) ≤ C*N^ε*(N^2/U^2+T*N^4/U^6) := by
  obtain ⟨C,hC,hclass⟩ := classical_large_values hε
  refine ⟨6*C,by positivity,?_⟩
  intro N T U hN hNT hTN hU a ha
  have hh := occupiedRealCells_card (S := {x | U < ‖boundedPolynomial N a x‖} ∩ Icc (-T) (2*T))
    (a := -T) (b := 2*T) (B := 3*(C*N^ε*(N^2/U^2+T*N^4/U^6))) (by
      intro W hw hsep
      apply separated_three_intervals W hsep (fun t ht => (hw t ht).2)
      intro Z s hZW hs hZsep
      exact hclass N T U s hN hNT hTN hU a Z ha hs hZsep
        (fun t ht => (hw t (hZW ht)).1.le))
  convert hh using 1; ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.separated_three_intervals
#print axioms GuthMaynard.Improvement.quartic_bad_cells_bound
