module
public import WeightedFourthMoment

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment

theorem sum_vectors_succ {α M : Type*} [Fintype α] [AddCommMonoid M]
    {n : ℕ} (f : (Fin (n+1) → α) → M) :
    (∑ v, f v) = ∑ a, ∑ v, f (Fin.cons a v) := by
  classical
  calc
    _ = ∑ p : α × (Fin n → α), f (Fin.cons p.1 p.2) :=
      (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => α))
        _ _ (fun _ => rfl)).symm
    _ = _ := Fintype.sum_prod_type _

/-- The fourth-moment contraction iterates over any number of coordinates,
with no dimension-dependent constant. -/
theorem product_fourth_bound {ι τ : Type*} [Fintype ι] [Fintype τ]
    (n : ℕ) (w : Fin n → τ → ℝ) (u : Fin n → ι → ℝ)
    (χ : Fin n → ι → τ → ℂ)
    (hw : ∀ j x, 0 ≤ w j x) (hu : ∀ j i, 0 ≤ u j i)
    (hχ : ∀ j (a : ι → ℂ),
      (∑ x, w j x * ‖∑ i, a i * χ j i x‖^4) ≤
        (∑ i, u j i * ‖a i‖^2)^2)
    (c : (Fin n → ι) → ℂ) :
    (∑ x : Fin n → τ, (∏ j, w j (x j)) *
      ‖∑ i : Fin n → ι, c i * ∏ j, χ j (i j) (x j)‖^4) ≤
      (∑ i : Fin n → ι, (∏ j, u j (i j)) * ‖c i‖^2)^2 := by
  classical
  induction n with
  | zero => simp [← pow_mul]
  | succ n ih =>
    have htail := ih (fun j => w j.succ) (fun j => u j.succ)
      (fun j => χ j.succ) (fun j => hw j.succ) (fun j => hu j.succ)
      (fun j => hχ j.succ)
    have hh := tensorize_fourth_bound univ univ univ univ
      (w 0) (fun y : Fin n → τ => ∏ j, w j.succ (y j))
      (u 0) (fun i : Fin n → ι => ∏ j, u j.succ (i j))
      (χ 0) (fun i y => ∏ j, χ j.succ (i j) (y j))
      (fun y _ => prod_nonneg (fun j _ => hw j.succ (y j)))
      (fun i _ => hu 0 i)
      (fun i _ => prod_nonneg (fun j _ => hu j.succ (i j)))
      (hχ 0) htail (fun i v => c (Fin.cons i v))
    rw [sum_vectors_succ, sum_comm]
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [sum_vectors_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    convert hh using 1
    apply sum_congr rfl
    intro y _
    apply sum_congr rfl
    intro x _
    congr 1
    · ring
    congr 1
    rw [sum_vectors_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, sum_mul]
    congr 1
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring

/-- Extending coefficients by zero along an injection preserves a finite sum. -/
theorem sum_extend_zero {ι κ M : Type*} [Fintype ι] [Fintype κ]
    [AddCommMonoid M] (v : ι → κ) (hv : Function.Injective v)
    (c : ι → ℂ) (F : κ → ℂ → M) (hF : ∀ j, F j 0 = 0) :
    (∑ j, F j (Function.extend v c (fun _ => 0) j)) = ∑ i, F (v i) (c i) := by
  classical
  have hs : (univ.image v : Finset κ) ⊆ univ := subset_univ _
  calc
    _ = ∑ j ∈ univ.image v, F j (Function.extend v c (fun _ => 0) j) := by
      symm
      apply sum_subset hs
      intro j _ hj
      rw [Function.extend_apply' c (fun _ => 0) j (by simpa using hj), hF]
    _ = _ := by
      rw [sum_image (fun i _ j _ h => hv h)]
      apply sum_congr rfl
      intro i _
      rw [hv.extend_apply]

/-- Restriction to any finite subset of frequencies preserves the contraction. -/
theorem restrict_fourth_bound {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
    (v : ι → κ) (hv : Function.Injective v) (w : τ → ℝ) (u : κ → ℝ)
    (χ : κ → τ → ℂ)
    (hχ : ∀ b : κ → ℂ, (∑ x, w x * ‖∑ j, b j*χ j x‖^4) ≤
      (∑ j, u j*‖b j‖^2)^2) (c : ι → ℂ) :
    (∑ x, w x * ‖∑ i, c i*χ (v i) x‖^4) ≤
      (∑ i, u (v i)*‖c i‖^2)^2 := by
  have hh := hχ (Function.extend v c (fun _ => 0))
  have hpoly (x : τ) := sum_extend_zero v hv c (fun j z => z*χ j x) (by simp)
  have henergy := sum_extend_zero v hv c (fun j z => u j*‖z‖^2) (by simp)
  simp_rw [hpoly] at hh
  rwa [henergy] at hh

end Montgomery.RationalMoment
