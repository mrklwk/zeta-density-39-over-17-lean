module
public import IntegerFourthMoment
public import ProductFourthMoment
public import RationalDifferenceEnergy

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment

theorem cyclic_fourth_moment_subtype {N : ℕ} [NeZero N] (A : Finset ℤ)
    (hzero : 0 ∈ A) (hN : ∀ n ∈ A, n.natAbs < N) (c : A → ℂ) :
    (∑ x : ZMod N, (N : ℝ)⁻¹ * ‖∑ n : A, c n*cyclicPhase n.val x‖^4) ≤
      (∑ n : A, integerFourthWeight n.val * ‖c n‖^2)^2 := by
  let b := Function.extend (Subtype.val : A → ℤ) c (fun _ => 0)
  have hh := cyclic_fourth_moment A hzero hN b
  simp_rw [← sum_coe_sort A] at hh
  simpa only [b, Function.Injective.extend_apply Subtype.val_injective] using hh

def productCyclicPhase {N : ℕ} [NeZero N] {d : ℕ}
    (v : Fin d → ℤ) (x : Fin d → ZMod N) : ℂ := ∏ j, cyclicPhase (v j) (x j)

/-- Weighted fourth moment for any finite, injectively indexed collection of
integer frequency vectors. The finite cyclic modulus is chosen above their size. -/
theorem sparse_cyclic_fourth_moment {ι : Type*} [Fintype ι]
    {N : ℕ} [NeZero N] (d : ℕ) (v : ι → Fin d → ℤ)
    (hv : Function.Injective v) (hN : ∀ i j, (v i j).natAbs < N) (c : ι → ℂ) :
    (∑ x : Fin d → ZMod N, (∏ _j : Fin d, (N : ℝ)⁻¹) *
      ‖∑ i, c i*productCyclicPhase (v i) x‖^4) ≤
      (∑ i, (∏ j, integerFourthWeight (v i j))*‖c i‖^2)^2 := by
  classical
  let A : Finset ℤ := insert 0 (univ.biUnion (fun i : ι => univ.image (v i)))
  have hmem (i : ι) (j : Fin d) : v i j ∈ A :=
    mem_insert_of_mem (mem_biUnion.mpr ⟨i, mem_univ _, mem_image.mpr ⟨j, mem_univ _, rfl⟩⟩)
  have hAN : ∀ n ∈ A, n.natAbs < N := by
    intro n hn
    rcases mem_insert.mp hn with rfl | hn
    · simpa using Nat.pos_of_ne_zero (NeZero.ne N)
    · obtain ⟨i, _, hn⟩ := mem_biUnion.mp hn
      obtain ⟨j, _, rfl⟩ := mem_image.mp hn
      exact hN i j
  let e : ι → Fin d → A := fun i j => ⟨v i j, hmem i j⟩
  have he : Function.Injective e := by
    intro i j hij
    apply hv
    funext k
    exact congrArg Subtype.val (congrFun hij k)
  have hprod := product_fourth_bound d
    (fun (_ : Fin d) (_ : ZMod N) => (N : ℝ)⁻¹)
    (fun (_ : Fin d) (n : A) => integerFourthWeight n.val)
    (fun (_ : Fin d) (n : A) => cyclicPhase n.val)
    (fun _ _ => by positivity) (fun _ n => integerFourthWeight_nonneg n.val)
    (fun _ b => cyclic_fourth_moment_subtype A (mem_insert_self _ _) hAN b)
  exact restrict_fourth_bound e he
    (fun _ : Fin d → ZMod N => ∏ _j : Fin d, (N : ℝ)⁻¹)
    (fun i : Fin d → A => ∏ j, integerFourthWeight (i j).val)
    (fun i x => ∏ j, cyclicPhase (i j).val (x j)) hprod c

theorem cyclicPhase_add {N : ℕ} [NeZero N] (m n : ℤ) (x : ZMod N) :
    cyclicPhase (m+n) x = cyclicPhase m x*cyclicPhase n x := by
  simp only [cyclicPhase, Int.cast_add, add_mul, AddChar.map_add_eq_mul]

theorem cyclicPhase_star {N : ℕ} [NeZero N] (n : ℤ) (x : ZMod N) :
    star (cyclicPhase n x) = cyclicPhase (-n) x := by
  rw [cyclicPhase, cyclicPhase, Int.cast_neg, neg_mul, AddChar.map_neg_eq_inv]
  simp only [ZMod.stdAddChar_apply, ← Circle.coe_inv, Circle.coe_inv_eq_conj]
  rfl

theorem cyclicPhase_orthogonal {N : ℕ} [NeZero N] (m n : ℤ)
    (hN : (m-n).natAbs < N) :
    (∑ x : ZMod N, (((N : ℝ)⁻¹ : ℝ) : ℂ)*cyclicPhase m x*star (cyclicPhase n x)) =
      if m = n then 1 else 0 := by
  simp_rw [cyclicPhase_star, mul_assoc, ← cyclicPhase_add, ← sub_eq_add_neg]
  rw [← mul_sum]
  by_cases h : m = n
  · subst n
    simp [cyclicPhase, ZMod.card, NeZero.ne N]
  · rw [cyclicPhase_mean_zero (sub_ne_zero.mpr h) hN, mul_zero, ite_eq_right h]

theorem productCyclicPhase_orthogonal {N : ℕ} [NeZero N] {d : ℕ}
    (v w : Fin d → ℤ) (hN : ∀ j, (v j-w j).natAbs < N) :
    (∑ x : Fin d → ZMod N, ((∏ _j : Fin d, (N : ℝ)⁻¹ : ℝ) : ℂ)*
      productCyclicPhase v x*star (productCyclicPhase w x)) =
      if v = w then 1 else 0 := by
  classical
  simp only [productCyclicPhase, star_prod, Complex.ofReal_prod]
  simp_rw [← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (j : Fin d) (x : ZMod N) =>
    (((N : ℝ)⁻¹ : ℝ) : ℂ)*cyclicPhase (v j) x*star (cyclicPhase (w j) x))]
  simp_rw [cyclicPhase_orthogonal _ _ (hN _)]
  by_cases h : v = w
  · subst w
    simp
  · rw [ite_eq_right h]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    exact prod_eq_zero (mem_univ j) (ite_eq_right hj)

/-- Exact Parseval identity for a finite orthonormal character family. -/
theorem finite_character_parseval {ι τ : Type*} [DecidableEq ι]
    (A : Finset ι) (X : Finset τ) (w : τ → ℝ) (χ : ι → τ → ℂ)
    (horth : ∀ i ∈ A, ∀ j ∈ A,
      (∑ x ∈ X, (w x : ℂ)*χ i x*star (χ j x)) = if i = j then 1 else 0)
    (c : ι → ℂ) :
    (∑ x ∈ X, w x*‖∑ i ∈ A, c i*χ i x‖^2) = ∑ i ∈ A, ‖c i‖^2 := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, square_sum_expansion, mul_sum]
  rw [sum_comm]
  calc
    _ = ∑ i ∈ A, ∑ j ∈ A, (c i*star (c j)) *
        (∑ x ∈ X, (w x : ℂ)*χ i x*star (χ j x)) := by
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      rw [mul_sum]
      apply sum_congr rfl
      intro x _
      simp only [star_mul]
      ring
    _ = ∑ i ∈ A, ((‖c i‖^2 : ℝ) : ℂ) := by
      apply sum_congr rfl
      intro i hi
      have he : (∑ j ∈ A, (c i*star (c j)) *
          (∑ x ∈ X, (w x : ℂ)*χ i x*star (χ j x))) =
          ∑ j ∈ A, (c i*star (c j))*(if i = j then 1 else 0) :=
        sum_congr rfl (fun j hj => by rw [horth i hi j hj])
      rw [he]
      simp only [mul_ite, mul_one, mul_zero, sum_ite_eq, hi, ite_true,
        ← starRingEnd_apply, Complex.mul_conj', Complex.ofReal_pow]

end Montgomery.RationalMoment
