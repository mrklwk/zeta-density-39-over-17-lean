module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.SargosDualTentWindow
public import LaterPairs.Native.SargosInitialInterval
public import LaterPairs.Native.SargosSymmetricAveraging

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                       

noncomputable section

open scoped BigOperators ComplexConjugate

namespace TaoTrudgianYang2025

theorem sargos_sum_Ico_add_one {A : Type*} [AddCommMonoid A]
    (f : ℤ → A) (M : ℕ) :
    (∑ m ∈ Finset.Ico (0:ℤ) M, f (m+1)) = ∑ m ∈ Finset.Ioc (0:ℤ) M, f m := by
  apply Finset.sum_bij (fun m _ => m+1)
  · intro m hm
    have h := Finset.mem_Ico.mp hm
    apply Finset.mem_Ioc.mpr
    constructor <;> omega
  · intro m hm n hn he
    omega
  · intro n hn
    have h := Finset.mem_Ioc.mp hn
    refine ⟨n-1,Finset.mem_Ico.mpr ⟨by omega,by omega⟩,by omega⟩
  · intro m hm
    rfl

end TaoTrudgianYang2025
