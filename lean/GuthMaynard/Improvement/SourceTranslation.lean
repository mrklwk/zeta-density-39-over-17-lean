import GuthMaynard.Improvement.Target
set_option autoImplicit false
noncomputable section
open Finset
namespace GuthMaynard.Improvement

/-- Time translation changes only the unit phases of the source coefficients. -/
def translatedSourceCoefficient (N t₀ : ℝ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a n * Complex.exp (((t₀*Real.log ((n:ℝ)/N):ℝ):ℂ)*Complex.I)

theorem translatedSourceCoefficient_norm (N t₀ : ℝ) (a : ℕ → ℂ) (n : ℕ) :
    ‖translatedSourceCoefficient N t₀ a n‖=‖a n‖ := by
  simp [translatedSourceCoefficient,Complex.norm_exp]

theorem boundedPolynomial_translate (N t₀ t : ℝ) (a : ℕ → ℂ) :
    boundedPolynomial N (translatedSourceCoefficient N t₀ a) t =
      boundedPolynomial N a (t+t₀) := by
  unfold boundedPolynomial
  apply sum_congr rfl
  intro n _
  unfold translatedSourceCoefficient
  rw [mul_assoc,← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Any bound uniform in coefficients and sets on [0,T] transfers to [t₀,t₀+T]
with exactly the same right-hand side. This helper assumes the origin bound
explicitly and asserts no particular large-values estimate. -/
theorem source_large_values_translation {N T V B : ℝ}
    (horigin : ∀ (a : ℕ → ℂ) (W : Finset ℝ),
      (∀ n ∈ Ioc ⌊N⌋₊ ⌊2*N⌋₊, ‖a n‖ ≤ 1) →
      (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, V ≤ ‖boundedPolynomial N a t‖) → (W.card:ℝ) ≤ B)
    (t₀ : ℝ) (a : ℕ → ℂ) (W : Finset ℝ)
    (ha : ∀ n ∈ Ioc ⌊N⌋₊ ⌊2*N⌋₊, ‖a n‖ ≤ 1)
    (hW : ∀ t ∈ W, t₀ ≤ t ∧ t ≤ t₀+T)
    (hsep : ∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|)
    (hlarge : ∀ t ∈ W, V ≤ ‖boundedPolynomial N a t‖) : (W.card:ℝ) ≤ B := by
  classical
  let W₀ := W.image (fun t => t-t₀)
  have hinj : Function.Injective (fun t : ℝ => t-t₀) := by
    intro t u h
    linarith
  have hcard : W₀.card=W.card := Finset.card_image_of_injective W hinj
  have hh := horigin (translatedSourceCoefficient N t₀ a) W₀
    (fun n hn => by rw [translatedSourceCoefficient_norm]; exact ha n hn)
    (by
      intro t ht
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨hlo,hhi⟩ := hW s hs
      exact ⟨by linarith,by linarith⟩)
    (by
      intro t ht u hu hne
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hu
      have hsr : s ≠ r := by intro he; subst r; exact hne rfl
      simpa only [sub_sub_sub_cancel_right] using hsep s hs r hr hsr)
    (by
      intro t ht
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp ht
      rw [boundedPolynomial_translate,sub_add_cancel]
      exact hlarge s hs)
  simpa only [hcard] using hh

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.translatedSourceCoefficient_norm
#print axioms GuthMaynard.Improvement.boundedPolynomial_translate
#print axioms GuthMaynard.Improvement.source_large_values_translation
