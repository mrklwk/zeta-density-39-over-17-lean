import GuthMaynard.Improvement.SeparatedLevelVolume
import GuthMaynard.Improvement.ClassicalLargeValues
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- Extending a uniform interval level-volume bound to integer multiples of
that interval uses only subadditivity, so no enlarged-height premise is needed. -/
theorem level_volume_interval_multiple {E : Set ℝ} {T B : ℝ} (hT : 0 ≤ T)
    (h : ∀ s : ℝ, volume.real (E ∩ Icc s (s+T)) ≤ B) (s : ℝ) (k : ℕ) :
    volume.real (E ∩ Icc s (s+k*T)) ≤ k*B := by
  induction k with
  | zero =>
    have hh : volume (E ∩ Icc s s) = 0 := by
      apply measure_mono_null (inter_subset_right) (by simp)
    simp only [Nat.cast_zero, zero_mul, add_zero]
    change (volume (E ∩ Icc s s)).toReal ≤ 0
    rw [hh]
    simp
  | succ k ih =>
    have he : E ∩ Icc s (s+(k+1:ℕ)*T) =
        (E ∩ Icc s (s+k*T)) ∪ (E ∩ Icc (s+k*T) (s+k*T+T)) := by
      ext x
      simp only [mem_inter_iff,mem_Icc,mem_union]
      push_cast
      constructor
      · intro hx
        by_cases hh : x ≤ s+k*T
        · exact Or.inl ⟨hx.1,hx.2.1,hh⟩
        · exact Or.inr ⟨hx.1,by linarith,by nlinarith [hx.2.2]⟩
      · rintro (hx|hx)
        · exact ⟨hx.1,hx.2.1,by nlinarith [hx.2.2]⟩
        · exact ⟨hx.1,by nlinarith [hx.2.1,mul_nonneg (Nat.cast_nonneg k : (0:ℝ)≤k) hT],by nlinarith [hx.2.2]⟩
    rw [he]
    have hh := measureReal_union_le (μ := volume)
      (E ∩ Icc s (s+k*T)) (E ∩ Icc (s+k*T) (s+k*T+T))
    have ht := h (s+k*T)
    push_cast
    linarith

/-- Continuous level volume for the actual source polynomial. Constants precede
all scales, coefficients, thresholds, translated intervals and integer lengths. -/
theorem boundedPolynomial_classical_level_volume {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N T V s : ℝ,
      2 ≤ N → N ≤ T → T ≤ N^2 → 0 < V →
      ∀ a : ℕ → ℂ, (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) → ∀ k : ℕ,
      volume.real ({t | V < ‖boundedPolynomial N a t‖} ∩ Icc s (s+k*T)) ≤
        k*C*N^ε*(N^2/V^2+T*N^4/V^6) := by
  obtain ⟨C,hC,h⟩ := classical_large_values hε
  refine ⟨2*C,by positivity,?_⟩
  intro N T V s hN hNT hTN hV a ha k
  have hT : 0 ≤ T := by linarith
  have hs (u : ℝ) : volume.real
      ({t | V < ‖boundedPolynomial N a t‖} ∩ Icc u (u+T)) ≤
      2*(C*N^ε*(N^2/V^2+T*N^4/V^6)) := by
    apply level_volume_of_separated_bound inter_subset_right
    intro W hW hsep
    exact h N T V u hN hNT hTN hV a W ha
      (fun t ht => (hW t ht).2) hsep (fun t ht => (hW t ht).1.le)
  convert level_volume_interval_multiple hT hs s k using 1
  ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.level_volume_interval_multiple
#print axioms GuthMaynard.Improvement.boundedPolynomial_classical_level_volume
