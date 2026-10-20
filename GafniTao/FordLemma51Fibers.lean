module
public import Mathlib
public import GafniTao.FordVinogradovIntegral

@[expose] public section
open MeasureTheory Finset
open scoped BigOperators
namespace GafniTao
noncomputable section
def fordAdditiveCharacter (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

theorem ford_sum_Icc_one_eq_fin
    {R : Type*} [AddCommMonoid R] (M : ℕ) (f : ℕ → R) :
    (∑ a ∈ Finset.Icc 1 M, f a) = ∑ a : Fin M, f ((a : ℕ) + 1) := by
  have hset : Finset.Icc 1 M = Finset.Ico 1 (M + 1) := by
    ext a
    simp
  rw [hset, Finset.sum_Ico_eq_sum_range]
  rw [Fin.sum_univ_eq_sum_range (fun n => f (n + 1)) M]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  omega

theorem fordAdditiveCharacter_add (x y : ℝ) :
    fordAdditiveCharacter (x + y) =
      fordAdditiveCharacter x * fordAdditiveCharacter y := by
  unfold fordAdditiveCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem fordAdditiveCharacter_sum
    {ι : Type*} (S : Finset ι) (f : ι → ℝ) :
    fordAdditiveCharacter (∑ i ∈ S, f i) =
      ∏ i ∈ S, fordAdditiveCharacter (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [fordAdditiveCharacter]
  | @insert a S ha ih =>
      simp only [sum_insert ha, prod_insert ha]
      rw [fordAdditiveCharacter_add, ih]


end
end GafniTao
