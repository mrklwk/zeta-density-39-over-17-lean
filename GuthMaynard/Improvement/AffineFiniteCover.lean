module
public import GuthMaynard.Improvement.AffineScaleTransfer

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped SchwartzMap
namespace GuthMaynard.Improvement
open RiemannZeta.GuthMaynard

/-- Positivity allows overlapping finite covers without a disjointness premise. -/
theorem sum_le_cover {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (S : Finset α) (A : Finset ι) (boxes : ι → Finset α) (g : α → ℝ)
    (hg : ∀ x, 0 ≤ g x) (hcover : ∀ x ∈ S, ∃ i ∈ A, x ∈ boxes i) :
    ∑ x ∈ S, g x ≤ ∑ i ∈ A, ∑ x ∈ boxes i, g x := by
  have hpoint : ∀ x ∈ S, g x ≤ ∑ i ∈ A, if x ∈ boxes i then g x else 0 := by
    intro x hx
    obtain ⟨i,hi,hxi⟩ := hcover x hx
    have h := Finset.single_le_sum (fun j _ => show 0 ≤ (if x ∈ boxes j then g x else 0) by split_ifs; exact hg x; exact le_rfl) hi
    simpa only [ite_eq_left hxi] using h
  calc
    _ ≤ ∑ x ∈ S, ∑ i ∈ A, if x ∈ boxes i then g x else 0 := Finset.sum_le_sum hpoint
    _ = ∑ i ∈ A, ∑ x ∈ S, if x ∈ boxes i then g x else 0 := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← Finset.sum_filter]
      exact Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => (Finset.mem_filter.mp hx).2)
        (fun x _ _ => hg x)

/-- Integrability of the sharp native affine square sum. -/
theorem integrable_affine_square (f : 𝓢(ℝ, ℝ)) {M₁ M₂ M₃ : ℕ}
    (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    Integrable (fun u => gmAffineTransformSum f M₁ M₂ M₃ u^2) := by
  have hf2 : Integrable (fun x => f x^2) :=
    (memLp_two_iff_integrable_sq f.continuous.aestronglyMeasurable).1 (f.memLp 2)
  have hi : Integrable (fun u => ((gmAffineIndexSet M₁ M₂ M₃).card:ℝ)*
      ∑ p ∈ gmAffineIndexSet M₁ M₂ M₃, gmAffineTerm f p.1 p.2.1 p.2.2 u^2) := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro p hp
    exact integrable_gmAffineTerm_sq hf2
      (gmAffineSignedShell_ne_zero h₁ (mem_gmAffineIndexSet.mp hp).1)
      (gmAffinePositiveShell_ne_zero h₂ (mem_gmAffineIndexSet.mp hp).2.1)
  apply hi.mono' ((continuous_gmAffineTransformSum f.continuous M₁ M₂ M₃).pow 2).aestronglyMeasurable
  filter_upwards with u
  simp only [Pi.pow_apply]
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact gmAffineTransformSum_sq_le f M₁ M₂ M₃ u

/-- Arbitrary finite affine index sums, so shell conversion remains visible. -/
def affineIndexIntegral (f : ℝ → ℝ) (S : Finset (ℤ × (ℤ × ℤ))) : ℝ :=
  ∫ u, (∑ p ∈ S, gmAffineTerm f p.1 p.2.1 p.2.2 u)^2

/-- Integrated finite-cover inequality, with the exact number of boxes. -/
theorem affine_integral_le_cover {ι : Type*} [DecidableEq ι]
    (f : 𝓢(ℝ, ℝ)) (hf : ∀ x, 0 ≤ f x) (S : Finset (ℤ × (ℤ × ℤ)))
    (A : Finset ι) (M₁ M₂ M₃ : ι → ℕ)
    (h₁ : ∀ i ∈ A, 0 < M₁ i) (h₂ : ∀ i ∈ A, 0 < M₂ i)
    (hcover : ∀ p ∈ S, ∃ i ∈ A, p ∈ gmAffineIndexSet (M₁ i) (M₂ i) (M₃ i)) :
    affineIndexIntegral f S ≤ (A.card:ℝ)*∑ i ∈ A, gmAffineTransformIntegral f (M₁ i) (M₂ i) (M₃ i) := by
  have hint : Integrable (fun u => (A.card:ℝ)*∑ i ∈ A, gmAffineTransformSum f (M₁ i) (M₂ i) (M₃ i) u^2) := by
    apply Integrable.const_mul
    exact integrable_finsetSum A (fun i hi => integrable_affine_square f (h₁ i hi) (h₂ i hi))
  unfold affineIndexIntegral
  calc
    _ ≤ ∫ u, (A.card:ℝ)*∑ i ∈ A, gmAffineTransformSum f (M₁ i) (M₂ i) (M₃ i) u^2 := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) hint
      filter_upwards with u
      have hp := sum_le_cover S A (fun i => gmAffineIndexSet (M₁ i) (M₂ i) (M₃ i))
        (fun p => gmAffineTerm f p.1 p.2.1 p.2.2 u) (fun p => hf _) hcover
      simp_rw [← gmAffineTransformSum_eq_indexSum] at hp
      have hn : 0 ≤ ∑ p ∈ S, gmAffineTerm f p.1 p.2.1 p.2.2 u := Finset.sum_nonneg (fun p _ => hf _)
      exact (sq_le_sq₀ hn (hn.trans hp)).mpr hp |>.trans (sq_sum_le_card_mul_sum_sq)
    _ = _ := by
      rw [integral_const_mul,integral_finsetSum]
      · rfl
      · exact fun i hi => integrable_affine_square f (h₁ i hi) (h₂ i hi)

/-- A real dyadic interval is covered by two native natural dyadic intervals. -/
theorem real_dyadic_two_shells {R : ℝ} (hR : 1 ≤ R) {m : ℤ}
    (hlo : R ≤ (m:ℝ)) (hhi : (m:ℝ) ≤ 2*R) :
    m ∈ gmAffinePositiveShell ⌊R⌋₊ ∨ m ∈ gmAffinePositiveShell (2*⌊R⌋₊) := by
  have hp : 0 < ⌊R⌋₊ := Nat.floor_pos.mpr hR
  have hpr : (1:ℝ) ≤ ⌊R⌋₊ := by exact_mod_cast hp
  have hfloor := Nat.floor_le (show 0 ≤ R by linarith)
  have hupper := Nat.lt_floor_add_one R
  have h₁ : (⌊R⌋₊:ℤ) ≤ m := by exact_mod_cast hfloor.trans hlo
  have h₂ : m ≤ 4*(⌊R⌋₊:ℤ) := by
    have hh : (m:ℝ) ≤ 4*(⌊R⌋₊:ℝ) := by linarith only [hhi,hupper,hpr]
    exact_mod_cast hh
  by_cases hm : m ≤ 2*(⌊R⌋₊:ℤ)
  · exact Or.inl (mem_gmAffinePositiveShell.mpr ⟨h₁,hm⟩)
  · apply Or.inr
    apply mem_gmAffinePositiveShell.mpr
    push_cast
    constructor <;> omega

/-- The same two-shell cover retains both slope signs. -/
theorem real_signed_two_shells {R : ℝ} (hR : 1 ≤ R) {m : ℤ}
    (hlo : R ≤ |(m:ℝ)|) (hhi : |(m:ℝ)| ≤ 2*R) :
    m ∈ gmAffineSignedShell ⌊R⌋₊ ∨ m ∈ gmAffineSignedShell (2*⌊R⌋₊) := by
  have h := real_dyadic_two_shells hR (m := |m|) (by simpa using hlo) (by simpa using hhi)
  have hc : ∀ {N : ℕ}, |m| ∈ gmAffinePositiveShell N → m ∈ gmAffineSignedShell N := by
    intro N hp
    rcases mem_gmAffinePositiveShell.mp hp with ⟨hl,hu⟩
    apply mem_gmAffineSignedShell.mpr
    by_cases hz : 0 ≤ m
    · right
      simpa only [abs_of_nonneg hz] using And.intro hl hu
    · left
      have hz' : m < 0 := lt_of_not_ge hz
      rw [abs_of_neg hz'] at hl hu
      push_cast
      constructor <;> omega
  exact h.elim (fun hp => Or.inl (hc hp)) (fun hp => Or.inr (hc hp))

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.sum_le_cover
#print axioms GuthMaynard.Improvement.integrable_affine_square
#print axioms GuthMaynard.Improvement.affine_integral_le_cover
#print axioms GuthMaynard.Improvement.real_dyadic_two_shells
#print axioms GuthMaynard.Improvement.real_signed_two_shells
