import GuthMaynard.Improvement.GlobalDensityConditional
import Mathlib.Analysis.Asymptotics.Basic

open Complex Filter MathCollab.Density
open scoped Topology
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- A literal native closed rectangle zero set has exactly the audited count.
The membership premise describes a finite set, not an analytic estimate. -/
theorem native_rectangle_sum_eq_zetaSlabCount {σ a b : ℝ} (hσ : 0 < σ)
    (S : Finset ℂ)
    (hS : ∀ ρ : ℂ, ρ ∈ S ↔ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ a ≤ ρ.im ∧
      ρ.im ≤ b ∧ riemannZeta ρ = 0) :
    (∑ ρ ∈ S, analyticOrderNatAt riemannZeta ρ) = zetaSlabCount σ a b := by
  have he : S = zetaZeroFinset σ a b := by
    ext ρ
    rw [hS, mem_zetaZeroFinset]
    constructor
    · rintro ⟨hlo,hhi,ha,hb,hzero⟩
      have hstrict : ρ.re < 1 := by
        by_contra hh
        exact (riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hh)) hzero
      exact ⟨⟨hzero,lt_of_lt_of_le hσ hlo,hstrict⟩,hlo,ha,hb⟩
    · rintro ⟨hz,hlo,ha,hb⟩
      exact ⟨hlo,hz.2.2.le,ha,hb,hz.1⟩
  rw [he]
  rfl

/-- The native both-sign closed rectangle convention preserves analytic multiplicity. -/
theorem native_rectangle_sum_eq_zetaDensityCount {σ T : ℝ} (hσ : 0 < σ)
    (S : Finset ℂ)
    (hS : ∀ ρ : ℂ, ρ ∈ S ↔ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ -T ≤ ρ.im ∧
      ρ.im ≤ T ∧ riemannZeta ρ = 0) :
    (∑ ρ ∈ S, analyticOrderNatAt riemannZeta ρ) = zetaDensityCount σ T :=
  native_rectangle_sum_eq_zetaSlabCount hσ S hS

/-- An eventual power estimate for the actual count extends to all T≥2.
This handles the bounded-height difference in the native asymptotic convention. -/
theorem zetaDensityCount_all_height_of_eventual {σ p C : ℝ}
    (hp : 0 ≤ p) (hC : 0 < C)
    (hb : ∀ᶠ T : ℝ in atTop, (zetaDensityCount σ T:ℝ) ≤ C*T^p) :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ A*T^p := by
  obtain ⟨D,hD⟩ := eventually_atTop.mp hb
  let R : ℝ := max 2 D
  let Q : ℝ := zetaDensityCount σ R
  have hQ : 0 ≤ Q := Nat.cast_nonneg _
  refine ⟨C+Q,by positivity,?_⟩
  intro T hT
  by_cases hRT : R ≤ T
  · exact (hD T ((le_max_right _ _).trans hRT)).trans
      (mul_le_mul_of_nonneg_right (by linarith : C ≤ C+Q) (by positivity))
  · have hsmall : (zetaDensityCount σ T:ℝ) ≤ Q := by
      dsimp [Q]
      exact_mod_cast zetaDensityCount_mono (le_refl σ) (le_of_not_ge hRT)
    have hpow := Real.one_le_rpow (show 1 ≤ T by linarith) hp
    exact hsmall.trans (by nlinarith)

/-- Exact translation of the native EpsilonPowerBound body. No asymptotic
estimate is invented: its actual Big-O hypothesis is displayed. -/
theorem zetaDensityCount_bound_of_native_bigO {σ p ε : ℝ}
    (hp : 0 ≤ p) (hε : 0 < ε)
    (hb : (fun T : ℝ => |(zetaDensityCount σ T:ℝ)|) =O[atTop]
      (fun T : ℝ => T^ε*|T^p|)) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(p+ε) := by
  obtain ⟨C,hC,hbound⟩ := hb.exists_pos
  apply zetaDensityCount_all_height_of_eventual (by linarith : 0 ≤ p+ε) hC
  filter_upwards [eventually_ge_atTop (2:ℝ),hbound.bound] with T hT hh
  have ht : 0 < T := by linarith
  have hn : 0 ≤ (zetaDensityCount σ T:ℝ) := Nat.cast_nonneg _
  simpa only [Real.norm_eq_abs,abs_of_nonneg hn,abs_of_nonneg (Real.rpow_nonneg ht.le p),
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le ε) (Real.rpow_nonneg ht.le p)),
    ← Real.rpow_add ht,add_comm ε p,abs_of_nonneg (Real.rpow_nonneg ht.le (p+ε))] using hh

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.native_rectangle_sum_eq_zetaSlabCount
#print axioms GuthMaynard.Improvement.native_rectangle_sum_eq_zetaDensityCount
#print axioms GuthMaynard.Improvement.zetaDensityCount_all_height_of_eventual
#print axioms GuthMaynard.Improvement.zetaDensityCount_bound_of_native_bigO
