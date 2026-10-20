module
public import WeightedFourthMoment
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.PSeries

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment

theorem nat_reciprocal_square_budget (A : Finset ℕ)
    (hA : ∀ n ∈ A, n ≠ 0) :
    (∑ n ∈ A, ((n : ℝ)^2)⁻¹) ≤ 2 := by
  have hs : A ⊆ Ioo 0 (A.sup id + 1) := by
    intro n hn
    exact mem_Ioo.mpr ⟨Nat.pos_of_ne_zero (hA n hn),
      Nat.lt_succ_of_le (le_sup (f := id) hn)⟩
  exact (sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)).trans
    (by simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (A.sup id + 1)))

theorem int_reciprocal_square_budget (A : Finset ℤ)
    (hA : ∀ n ∈ A, n ≠ 0) :
    (∑ n ∈ A, (n : ℝ)⁻¹ ^ 2) ≤ 4 := by
  let B := A.image Int.natAbs
  have hB : ∀ n ∈ B, n ≠ 0 := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
    exact Int.natAbs_ne_zero.mpr (hA m hm)
  have hb := nat_reciprocal_square_budget B hB
  let P := B.image (fun n : ℕ => (n : ℤ))
  let Q := B.image (fun n : ℕ => -(n : ℤ))
  have hs : A ⊆ P ∪ Q := by
    intro n hn
    have hnB : n.natAbs ∈ B := mem_image.mpr ⟨n, hn, rfl⟩
    rcases le_total 0 n with hn0 | hn0
    · exact mem_union_left Q (mem_image.mpr ⟨n.natAbs, hnB, by
        rw [Int.natCast_natAbs, abs_of_nonneg hn0]⟩)
    · exact mem_union_right P (mem_image.mpr ⟨n.natAbs, hnB, by
        rw [Int.natCast_natAbs, abs_of_nonpos hn0, neg_neg]⟩)
  have hp : (∑ n ∈ P, (n : ℝ)⁻¹ ^ 2) = ∑ n ∈ B, ((n : ℝ)^2)⁻¹ := by
    rw [show P = B.image (fun n : ℕ => (n : ℤ)) from rfl, sum_image]
    · simp only [Int.cast_natCast, inv_pow]
    · intro a _ b _ hab
      change (a : ℤ) = (b : ℤ) at hab
      exact_mod_cast hab
  have hq : (∑ n ∈ Q, (n : ℝ)⁻¹ ^ 2) = ∑ n ∈ B, ((n : ℝ)^2)⁻¹ := by
    rw [show Q = B.image (fun n : ℕ => -(n : ℤ)) from rfl, sum_image]
    · simp only [Int.cast_neg, Int.cast_natCast, inv_neg, neg_sq, inv_pow]
    · intro a _ b _ hab
      exact_mod_cast neg_injective hab
  calc
    _ ≤ ∑ n ∈ P ∪ Q, (n : ℝ)⁻¹ ^ 2 :=
      sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => sq_nonneg _)
    _ ≤ (∑ n ∈ P, (n : ℝ)⁻¹ ^ 2) + ∑ n ∈ Q, (n : ℝ)⁻¹ ^ 2 :=
      by
        have he : (∑ n ∈ P ∪ Q, (n : ℝ)⁻¹ ^ 2) +
            (∑ n ∈ P ∩ Q, (n : ℝ)⁻¹ ^ 2) =
            (∑ n ∈ P, (n : ℝ)⁻¹ ^ 2) + ∑ n ∈ Q, (n : ℝ)⁻¹ ^ 2 := sum_union_inter
        have hn : 0 ≤ ∑ n ∈ P ∩ Q, (n : ℝ)⁻¹ ^ 2 :=
          sum_nonneg (fun _ _ => sq_nonneg _)
        linarith
    _ ≤ 4 := by rw [hp, hq]; linarith

def integerFourthWeight (n : ℤ) : ℝ := if n = 0 then 1 else 16*(n : ℝ)^2

theorem integerFourthWeight_nonneg (n : ℤ) : 0 ≤ integerFourthWeight n := by
  unfold integerFourthWeight
  split_ifs <;> positivity

def cyclicPhase {N : ℕ} [NeZero N] (n : ℤ) (x : ZMod N) : ℂ :=
  ZMod.stdAddChar ((n : ZMod N)*x)

theorem cyclicPhase_norm {N : ℕ} [NeZero N] (n : ℤ) (x : ZMod N) : ‖cyclicPhase n x‖ = 1 := by
  simp only [cyclicPhase, ZMod.stdAddChar_apply, Circle.norm_coe]

theorem cyclicPhase_mean_zero {N : ℕ} [NeZero N] {n : ℤ}
    (hn : n ≠ 0) (hN : n.natAbs < N) :
    (∑ x : ZMod N, cyclicPhase n x) = 0 := by
  have hcast : (n : ZMod N) ≠ 0 := by
    intro he
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd n N).mp he
    have hd' : N ∣ n.natAbs := by exact_mod_cast Int.natAbs_dvd_natAbs.mpr hd
    exact (Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr hn) hN) hd'
  simpa only [cyclicPhase, AddChar.mulShift_apply, mul_comm] using
    AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N hcast)

/-- A genuine finite cyclic Laurent-polynomial estimate, with mean zero
and the reciprocal-square budget proved internally. -/
theorem cyclic_fourth_moment {N : ℕ} [NeZero N] (A : Finset ℤ)
    (hzero : 0 ∈ A) (hN : ∀ n ∈ A, n.natAbs < N) (c : ℤ → ℂ) :
    (∑ x : ZMod N, (N : ℝ)⁻¹ * ‖∑ n ∈ A, c n*cyclicPhase n x‖^4) ≤
      (∑ n ∈ A, integerFourthWeight n * ‖c n‖^2)^2 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hmean (n : ℤ) (hn : n ∈ A.erase 0) :
      (∑ x : ZMod N, (((N : ℝ)⁻¹ : ℝ) : ℂ)*cyclicPhase n x) = 0 := by
    rw [← mul_sum, cyclicPhase_mean_zero (ne_of_mem_erase hn) (hN n (mem_of_mem_erase hn)), mul_zero]
  have hh := weighted_character_fourth_moment (A.erase 0) univ
    (fun _ : ZMod N => (N : ℝ)⁻¹) cyclicPhase c (c 0) (fun n => (n : ℝ))
    (fun _ _ => by positivity)
    (by simp [ZMod.card, hNp.ne']) hmean
    (fun n hn => by exact_mod_cast ne_of_mem_erase hn)
    (fun n _ x _ => (cyclicPhase_norm n x).le)
    (int_reciprocal_square_budget (A.erase 0) (fun _ hn => ne_of_mem_erase hn))
  have he (x : ZMod N) :
      (∑ n ∈ A, c n*cyclicPhase n x) = c 0 + ∑ n ∈ A.erase 0, c n*cyclicPhase n x := by
    rw [← sum_erase_add _ _ hzero]
    simp [cyclicPhase, add_comm]
  have hw : (∑ n ∈ A, integerFourthWeight n * ‖c n‖^2) =
      ‖c 0‖^2 + 16*(∑ n ∈ A.erase 0, (n : ℝ)^2*‖c n‖^2) := by
    rw [← sum_erase_add _ _ hzero, mul_sum]
    simp only [integerFourthWeight, ite_true, Int.cast_zero, one_mul]
    rw [add_comm]
    congr 1
    apply sum_congr rfl
    intro n hn
    rw [ite_eq_right (ne_of_mem_erase hn)]
    ring
  simp_rw [he]
  rw [hw]
  convert hh using 1
  norm_num

end Montgomery.RationalMoment
