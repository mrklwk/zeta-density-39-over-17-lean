module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.SargosPlanarWindow

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                       

noncomputable section

open GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargos_character_finset_prod {ι : Type*} (S : Finset ι) (f : ι → ℝ) :
    (∏ i ∈ S, fordAdditiveCharacter (f i)) =
      fordAdditiveCharacter (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [fordAdditiveCharacter]
  | @insert a S ha ih =>
      rw [Finset.prod_insert ha,Finset.sum_insert ha,ih,fordAdditiveCharacter_add]

end TaoTrudgianYang2025
