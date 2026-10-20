module
public import Mathlib
public import GafniTao.FordVinogradovIntegral

@[expose] public section
open MeasureTheory Finset
open scoped BigOperators
namespace GafniTao
noncomputable section
def fordLambda34 (s k : ℕ) (delta : ℝ) : ℝ :=
  2*(s:ℝ)-((k:ℝ)*(k+1))/2+delta

def FordVinogradovMomentBound (s k : ℕ) (C delta : ℝ) : Prop :=
  ∀ Q : ℕ,1 ≤ Q → (fordVinogradovMomentNat s k Q:ℝ) ≤ C*(Q:ℝ)^fordLambda34 s k delta
abbrev FordPowerSolution (s k Q : ℕ) :=
  {xy : FordVinogradovTuple s Q × FordVinogradovTuple s Q //
    fordVinogradovPowerVector s k Q xy.1 = fordVinogradovPowerVector s k Q xy.2}

theorem card_fordPowerSolution (s k Q : ℕ) :
    Nat.card (FordPowerSolution s k Q) = fordVinogradovMomentNat s k Q := by
  classical
  rw [Nat.card_eq_fintype_card]
  unfold FordPowerSolution fordVinogradovMomentNat
    fordVinogradovShiftedCountNat fordRepresentationCount
  rw [Fintype.card_subtype]
  congr 1
  ext xy
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
    true_and, sub_eq_zero]

end
end GafniTao
