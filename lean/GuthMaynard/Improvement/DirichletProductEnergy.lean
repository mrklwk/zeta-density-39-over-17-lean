import GuthMaynard.Improvement.DirichletMeanValue
import GuthMaynard.Improvement.SourceRatioAssembly
import GuthMaynard.Improvement.DivisorMultiplicity
import MathCollab.Density.DivisorGrowth
set_option autoImplicit false
noncomputable section
open Finset
namespace GuthMaynard.Improvement

/-- Exact pairs for real source length and positive reflected modes. -/
def dirichletProductPairs (N : ℝ) (X : ℕ) : Finset (ℕ × ℕ) :=
  sourceRatioIndices N ×ˢ Finset.Icc 1 X

def dirichletProductFiber (N : ℝ) (X k : ℕ) : Finset (ℕ × ℕ) :=
  (dirichletProductPairs N X).filter (fun p => p.1*p.2=k)

def dirichletProductCoefficient (N : ℝ) (X : ℕ) (a b : ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑ p ∈ dirichletProductFiber N X k, a p.1*b p.2

theorem dirichlet_product_pair_bounds {N : ℝ} (hN : 0 ≤ N) {X : ℕ}
    {p : ℕ × ℕ} (hp : p ∈ dirichletProductPairs N X) :
    0 < p.1*p.2 ∧ p.1*p.2 ≤ ⌊2*N⌋₊*X ∧ ((p.1*p.2:ℕ):ℝ) ≤ 2*N*X := by
  obtain ⟨hn,hm⟩ := Finset.mem_product.mp hp
  have hn' := (sourceRatioIndices_mem hN p.1).mp hn
  have hm' := Finset.mem_Icc.mp hm
  have hn0 : 0 < p.1 := by exact_mod_cast hN.trans_lt hn'.1
  refine ⟨Nat.mul_pos hn0 hm'.1,Nat.mul_le_mul (Nat.le_floor hn'.2) hm'.2,?_⟩
  push_cast
  exact mul_le_mul hn'.2 (by exact_mod_cast hm'.2) (Nat.cast_nonneg _) (by positivity)

/-- Raw fiber Cauchy--Schwarz; no divisor estimate is a premise. -/
theorem dirichlet_product_coefficient_square (N : ℝ) (X k : ℕ) (a b : ℕ → ℂ) :
    ‖dirichletProductCoefficient N X a b k‖^2 ≤
      ((dirichletProductFiber N X k).card:ℝ)*
        ∑ p ∈ dirichletProductFiber N X k, ‖a p.1*b p.2‖^2 := by
  calc
    _ ≤ (∑ p ∈ dirichletProductFiber N X k, ‖a p.1*b p.2‖)^2 :=
      (sq_le_sq₀ (norm_nonneg _) (sum_nonneg (fun _ _ => norm_nonneg _))).mpr (norm_sum_le _ _)
    _ ≤ _ := by
      simpa using sum_mul_sq_le_sq_mul_sq (dirichletProductFiber N X k)
        (fun _ => (1:ℝ)) (fun p => ‖a p.1*b p.2‖)

/-- Actual finite coefficient energy with the exact maximum divisor count. -/
theorem dirichlet_product_energy_raw {N : ℝ} (hN : 0 ≤ N) (X : ℕ)
    (a b : ℕ → ℂ) (K : Finset ℕ) :
    (∑ k ∈ K, ‖dirichletProductCoefficient N X a b k‖^2) ≤
      ((((dirichletProductPairs N X).image (fun p => p.1*p.2)).sup (fun k => k.divisors.card):ℕ):ℝ)*
        ∑ p ∈ dirichletProductPairs N X, ‖a p.1*b p.2‖^2 := by
  let D := ((dirichletProductPairs N X).image (fun p => p.1*p.2)).sup (fun k => k.divisors.card)
  have hcard (k : ℕ) : (dirichletProductFiber N X k).card ≤ D := by
    by_cases hh : (dirichletProductFiber N X k).Nonempty
    · obtain ⟨p,hp⟩ := hh
      obtain ⟨hp,hprod⟩ := mem_filter.mp hp
      have hk : 0 < k := hprod ▸ (dirichlet_product_pair_bounds hN hp).1
      exact (product_fiber_card_le_divisors _ hk.ne' (fun q hq => (mem_filter.mp hq).2)).trans
        (Finset.le_sup (f := fun k : ℕ => k.divisors.card) (mem_image.mpr ⟨p,hp,hprod⟩))
    · rw [Finset.not_nonempty_iff_eq_empty.mp hh]
      simp
  have hf : (∑ k ∈ K, ∑ p ∈ dirichletProductFiber N X k, ‖a p.1*b p.2‖^2) ≤
      ∑ p ∈ dirichletProductPairs N X, ‖a p.1*b p.2‖^2 :=
    sum_fiberwise_le_sum_of_sum_fiber_nonneg (fun _ _ => sum_nonneg (fun _ _ => sq_nonneg _))
  calc
    _ ≤ ∑ k ∈ K, (D:ℝ)*(∑ p ∈ dirichletProductFiber N X k, ‖a p.1*b p.2‖^2) := by
      apply sum_le_sum
      intro k _
      exact (dirichlet_product_coefficient_square N X k a b).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard k) (sum_nonneg (fun _ _ => sq_nonneg _)))
    _ = (D:ℝ)*(∑ k ∈ K, ∑ p ∈ dirichletProductFiber N X k, ‖a p.1*b p.2‖^2) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg D)

/-- Uniform subpower budget before lengths, coefficients or coefficient cutoff. -/
theorem dirichlet_product_energy_subpower {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 0 ≤ N → ∀ (X : ℕ) (a b : ℕ → ℂ) (K : Finset ℕ),
      (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
      (∀ m ∈ Finset.Icc 1 X, ‖b m‖ ≤ 1) →
      (∑ k ∈ K, ‖dirichletProductCoefficient N X a b k‖^2) ≤
        C*(1+2*N*X)^η*(N+1)*X := by
  obtain ⟨C,hC,hd⟩ := MathCollab.Density.divisor_card_subpower hη
  refine ⟨C,by linarith,?_⟩
  intro N hN X a b K ha hb
  let D := ((dirichletProductPairs N X).image (fun p => p.1*p.2)).sup (fun k => k.divisors.card)
  have hD : (D:ℝ) ≤ C*(1+2*N*X)^η := by
    by_cases he : ((dirichletProductPairs N X).image (fun p => p.1*p.2)).Nonempty
    · obtain ⟨k,hk,hke⟩ := Finset.exists_mem_eq_sup _ he (fun k => k.divisors.card)
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hk
      have hsize := dirichlet_product_pair_bounds hN hp
      change (D:ℝ) ≤ _
      rw [show D=(p.1*p.2).divisors.card from hke]
      exact (hd _ hsize.1).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by linarith [hsize.2.2]) hη.le) (by linarith))
    · have hempty := Finset.not_nonempty_iff_eq_empty.mp he
      simp only [D,hempty,Finset.sup_empty,bot_eq_zero,Nat.cast_zero]
      positivity
  have hpair : (∑ p ∈ dirichletProductPairs N X, ‖a p.1*b p.2‖^2) ≤
      ((sourceRatioIndices N).card:ℝ)*X := by
    calc
      _ ≤ ∑ _p ∈ dirichletProductPairs N X, (1:ℝ) := by
        apply sum_le_sum
        intro p hp
        obtain ⟨hn,hm⟩ := mem_product.mp hp
        rw [norm_mul]
        have hh : ‖a p.1‖*‖b p.2‖ ≤ 1 := by nlinarith [ha p.1 hn,hb p.2 hm,norm_nonneg (a p.1),norm_nonneg (b p.2)]
        nlinarith [mul_nonneg (norm_nonneg (a p.1)) (norm_nonneg (b p.2))]
      _ = _ := by simp [dirichletProductPairs]
  have hsource : ((sourceRatioIndices N).card:ℝ) ≤ N+1 := by
    have hf : ⌊N⌋₊ ≤ ⌊2*N⌋₊ := Nat.floor_mono (by linarith)
    rw [sourceRatioIndices,Nat.card_Ioc,Nat.cast_sub hf]
    linarith [Nat.floor_le (by positivity : 0 ≤ 2*N),Nat.lt_floor_add_one N]
  calc
    _ ≤ (D:ℝ)*(∑ p ∈ dirichletProductPairs N X, ‖a p.1*b p.2‖^2) := dirichlet_product_energy_raw hN X a b K
    _ ≤ (C*(1+2*N*X)^η)*(((sourceRatioIndices N).card:ℝ)*X) :=
      mul_le_mul hD hpair (sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsource (by positivity)) (Nat.cast_nonneg X)


/-- Exact phase multiplication for positive integer frequencies. -/
theorem dirichlet_phase_product {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (t : ℝ) :
    dirichletPhase n t*dirichletPhase m t=dirichletPhase (n*m) t := by
  unfold dirichletPhase
  rw [← Complex.exp_add,Nat.cast_mul,Real.log_mul (by positivity) (by positivity)]
  congr 1
  push_cast
  ring

/-- The actual product polynomial equals the polynomial with the literal product-fiber coefficients.
No coefficient or grouping identity is assumed. -/
theorem dirichlet_product_polynomial {N : ℝ} (hN : 0 ≤ N) (X : ℕ)
    (a b : ℕ → ℂ) (t : ℝ) :
    (∑ n ∈ sourceRatioIndices N, a n*dirichletPhase n t)*finiteDirichletPolynomial X b t =
      finiteDirichletPolynomial (⌊2*N⌋₊*X) (dirichletProductCoefficient N X a b) t := by
  let P := dirichletProductPairs N X
  let Y := Finset.Icc 1 (⌊2*N⌋₊*X)
  have hmaps : ∀ p ∈ P, p.1*p.2 ∈ Y := by
    intro p hp
    have hh := dirichlet_product_pair_bounds hN hp
    exact mem_Icc.mpr ⟨hh.1,hh.2.1⟩
  have hgroup := Finset.sum_fiberwise_of_maps_to hmaps
    (fun p : ℕ × ℕ => (a p.1*b p.2)*dirichletPhase (p.1*p.2) t)
  have he : finiteDirichletPolynomial (⌊2*N⌋₊*X) (dirichletProductCoefficient N X a b) t =
      ∑ p ∈ P, (a p.1*b p.2)*dirichletPhase (p.1*p.2) t := by
    rw [← hgroup]
    unfold finiteDirichletPolynomial dirichletProductCoefficient
    apply sum_congr rfl
    intro k _
    rw [sum_mul]
    apply sum_congr rfl
    intro p hp
    rw [(mem_filter.mp hp).2]
  rw [he]
  unfold finiteDirichletPolynomial
  rw [sum_mul]
  simp only [dirichletProductPairs,P,sum_product,mul_sum]
  apply sum_congr rfl
  intro n hn
  apply sum_congr rfl
  intro m hm
  have hn0 : 0 < n := by exact_mod_cast hN.trans_lt ((sourceRatioIndices_mem hN n).mp hn).1
  have hm0 : 0 < m := (mem_Icc.mp hm).1
  rw [← dirichlet_phase_product hn0 hm0]
  ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.dirichlet_product_pair_bounds
#print axioms GuthMaynard.Improvement.dirichlet_product_coefficient_square
#print axioms GuthMaynard.Improvement.dirichlet_product_energy_raw
#print axioms GuthMaynard.Improvement.dirichlet_product_energy_subpower

#print axioms GuthMaynard.Improvement.dirichlet_phase_product
#print axioms GuthMaynard.Improvement.dirichlet_product_polynomial
