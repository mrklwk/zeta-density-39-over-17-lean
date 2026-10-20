module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.SargosDualTentWindow
public import LaterPairs.Native.SargosIntegerPrefix
public import LaterPairs.Native.SargosMomentTuples
public import LaterPairs.Native.SargosPositiveQuadraticRemainder
public import LaterPairs.Native.SargosPrefixFourthMajorant
public import LaterPairs.Native.SargosQuarticKernelJets
public import LaterPairs.Native.SargosQuarticPhase
public import LaterPairs.Native.SargosQuarticPoisson
public import LaterPairs.Native.SargosSlowAbel
public import LaterPairs.Native.SargosSlowCharacter

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                                

noncomputable section

open GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargos_integer_Ioc_sum_split {A : Type*} [AddCommMonoid A]
    (f : ℤ → A) {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    (∑ n ∈ Finset.Ioc a c, f n) =
      (∑ n ∈ Finset.Ioc a b, f n)+(∑ n ∈ Finset.Ioc b c, f n) := by
  classical
  have hu : Finset.Ioc a c = Finset.Ioc a b ∪ Finset.Ioc b c := by
    ext n
    simp only [Finset.mem_Ioc,Finset.mem_union]
    omega
  have hd : Disjoint (Finset.Ioc a b) (Finset.Ioc b c) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    simp only [Finset.mem_Ioc] at hn hm
    omega
  rw [hu,Finset.sum_union hd]

end TaoTrudgianYang2025
