module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.IntegerTripleNormalization
public import LaterPairs.Native.RobertSargosReducedSystem

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                                 

namespace TaoTrudgianYang2025

def robertSargosCoefficientGcd (p : RobertSargosPoint) : ℕ :=
  integerTripleGcd p.r p.h₁ p.h₂

def robertSargosFrequencyGcd (p : RobertSargosPoint) : ℕ :=
  integerTripleGcd p.d p.q₁ p.q₂

def robertSargosNormalize (j k : ℕ) (p : RobertSargosPoint) : RobertSargosPoint :=
  ⟨p.r/(j:ℤ),p.q₁/(k:ℤ),p.q₂/(k:ℤ),p.h₁/(j:ℤ),p.h₂/(j:ℤ),p.d/(k:ℤ)⟩

def robertSargosRestore (j k : ℕ) (p : RobertSargosPoint) : RobertSargosPoint :=
  ⟨(j:ℤ)*p.r,(k:ℤ)*p.q₁,(k:ℤ)*p.q₂,(j:ℤ)*p.h₁,(j:ℤ)*p.h₂,(k:ℤ)*p.d⟩

theorem robertSargos_restore_normalize (p : RobertSargosPoint) {j k : ℕ}
    (hj : j = robertSargosCoefficientGcd p) (hk : k = robertSargosFrequencyGcd p) :
    robertSargosRestore j k (robertSargosNormalize j k p) = p := by
  have hdj : (j:ℤ) ∣ p.r ∧ (j:ℤ) ∣ p.h₁ ∧ (j:ℤ) ∣ p.h₂ := by
    rw [hj]
    exact integerTripleGcd_dvd _ _ _
  have hdk : (k:ℤ) ∣ p.d ∧ (k:ℤ) ∣ p.q₁ ∧ (k:ℤ) ∣ p.q₂ := by
    rw [hk]
    exact integerTripleGcd_dvd _ _ _
  cases p
  dsimp [robertSargosRestore,robertSargosNormalize]
  congr 1
  · exact Int.mul_ediv_cancel_of_dvd hdj.1
  · exact Int.mul_ediv_cancel_of_dvd hdk.2.1
  · exact Int.mul_ediv_cancel_of_dvd hdk.2.2
  · exact Int.mul_ediv_cancel_of_dvd hdj.2.1
  · exact Int.mul_ediv_cancel_of_dvd hdj.2.2
  · exact Int.mul_ediv_cancel_of_dvd hdk.1

theorem robertSargos_normalize_injective_on_gcd_fiber
    (S : Finset RobertSargosPoint) {j k : ℕ}
    (hj : ∀ p ∈ S, j = robertSargosCoefficientGcd p)
    (hk : ∀ p ∈ S, k = robertSargosFrequencyGcd p) :
    Set.InjOn (robertSargosNormalize j k) S := by
  intro p hp q hq he
  have hr := congrArg (robertSargosRestore j k) he
  rwa [robertSargos_restore_normalize p (hj p hp) (hk p hp),
    robertSargos_restore_normalize q (hj q hq) (hk q hq)] at hr

theorem robertSargos_normalized_gcds (p : RobertSargosPoint) {j k : ℕ}
    (hr : p.r ≠ 0) (hd : p.d ≠ 0)
    (hj : j = robertSargosCoefficientGcd p) (hk : k = robertSargosFrequencyGcd p) :
    robertSargosCoefficientGcd (robertSargosNormalize j k p) = 1 ∧
      robertSargosFrequencyGcd (robertSargosNormalize j k p) = 1 := by
  subst j
  subst k
  exact ⟨integerTripleGcd_quotient_primitive hr,integerTripleGcd_quotient_primitive hd⟩

theorem RobertSargosReducedSystem.coefficient_gcd_pos {R H Q δ : ℝ}
    {p : RobertSargosPoint} (h : RobertSargosReducedSystem R H Q δ p) :
    0 < robertSargosCoefficientGcd p :=
  integerTripleGcd_pos h.r_ne_zero

theorem RobertSargosReducedSystem.frequency_gcd_pos {R H Q δ : ℝ}
    {p : RobertSargosPoint} (h : RobertSargosReducedSystem R H Q δ p) :
    0 < robertSargosFrequencyGcd p :=
  integerTripleGcd_pos h.d_ne_zero

theorem RobertSargosReducedSystem.coefficient_gcd_le {R H Q δ : ℝ}
    {p : RobertSargosPoint} (h : RobertSargosReducedSystem R H Q δ p) :
    (robertSargosCoefficientGcd p:ℝ) ≤ R := by
  have hc : (robertSargosCoefficientGcd p:ℝ) ≤ p.r.natAbs := by
    exact_mod_cast integerTripleGcd_le_natAbs h.r_ne_zero
  have he : (p.r.natAbs:ℝ) = |(p.r:ℝ)| := by
    simpa only [Int.cast_natCast,Int.cast_abs] using
      congrArg (fun z : ℤ => (z:ℝ)) (Int.natCast_natAbs p.r)
  exact hc.trans (he.trans_le h.r_bound)

end TaoTrudgianYang2025
