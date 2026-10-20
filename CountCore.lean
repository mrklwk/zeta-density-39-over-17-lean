module

public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal

@[expose] public section

namespace LewkoDensityPalomar

/-- Analytic multiplicity of an actual global zeta zero in the closed height window.
The critical strip is open; the density and height cutoffs are closed. -/
noncomputable def zeroWeight (σ T : ℝ) (ρ : ℂ) : ℝ≥0∞ := by
  classical
  exact if riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T
    then (analyticOrderNatAt riemannZeta ρ : ℝ≥0∞) else 0

/-- The full count of actual zeta zeros with analytic multiplicity and both signs
of the ordinate. This is a genuine nonnegative extended-real sum. -/
noncomputable def zeroCount (σ T : ℝ) : ℝ≥0∞ := ∑' ρ : ℂ, zeroWeight σ T ρ

/-- An exact enumeration gives exactly the same multiplicity count. -/
theorem zeroCount_eq_finset (σ T : ℝ) (F : Finset ℂ)
    (hF : ∀ ρ : ℂ, ρ ∈ F ↔ riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      σ ≤ ρ.re ∧ |ρ.im| ≤ T) :
    zeroCount σ T = ((∑ ρ ∈ F, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ≥0∞) := by
  classical
  calc
    zeroCount σ T = ∑ ρ ∈ F, zeroWeight σ T ρ := by
      apply tsum_eq_sum
      intro ρ hρ
      simp only [zeroWeight, ite_eq_right (mt (hF ρ).mpr hρ)]
    _ = ∑ ρ ∈ F, (analyticOrderNatAt riemannZeta ρ : ℝ≥0∞) := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      simp only [zeroWeight, ite_eq_left ((hF ρ).mp hρ)]
    _ = ((∑ ρ ∈ F, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ≥0∞) := by simp

/-- Comparison with a nonnegative real number is exactly the usual real count
comparison. In particular, using `ofReal` on the right does not weaken a bound. -/
theorem zeroCount_le_iff (σ T B : ℝ) (F : Finset ℂ) (hB : 0 ≤ B)
    (hF : ∀ ρ : ℂ, ρ ∈ F ↔ riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      σ ≤ ρ.re ∧ |ρ.im| ≤ T) :
    zeroCount σ T ≤ ENNReal.ofReal B ↔
      ((∑ ρ ∈ F, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤ B := by
  rw [zeroCount_eq_finset σ T F hF, ← ENNReal.ofReal_natCast,
    ENNReal.ofReal_le_ofReal_iff hB]

/-- Such an enumeration exists without any analytic or finiteness hypothesis. -/
theorem exact_zero_set_exists (σ T : ℝ) : ∃ F : Finset ℂ,
    ∀ ρ : ℂ, ρ ∈ F ↔ riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      σ ≤ ρ.re ∧ |ρ.im| ≤ T := by
  classical
  have hfin : {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      σ ≤ ρ.re ∧ |ρ.im| ≤ T}.Finite := by
    apply ((isCompact_closedBall (0 : ℂ) (1 + |T|)).inter_riemannZetaZeros_finite).subset
    intro ρ hρ
    refine ⟨?_, hρ.1⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
      _ ≤ 1 + |T| := by
        rw [abs_of_pos hρ.2.1]
        linarith [hρ.2.2.1, hρ.2.2.2.2, le_abs_self T]
  exact ⟨hfin.toFinset, fun ρ => Set.Finite.mem_toFinset hfin⟩

/-- The extended-real count is finite for every real cutoff and height. -/
theorem zeroCount_ne_top (σ T : ℝ) : zeroCount σ T ≠ ⊤ := by
  obtain ⟨F, hF⟩ := exact_zero_set_exists σ T
  rw [zeroCount_eq_finset σ T F hF]
  exact ENNReal.natCast_ne_top _

/-- No zero inside the critical strip has infinite analytic order, so the
natural analytic order used in the count is a positive, genuine multiplicity. -/
theorem positive_finite_multiplicity {ρ : ℂ}
    (hz : riemannZeta ρ = 0) (_hlo : 0 < ρ.re) (hhi : ρ.re < 1) :
    0 < analyticOrderNatAt riemannZeta ρ ∧ analyticOrderAt riemannZeta ρ ≠ ⊤ := by
  have hne : ρ ≠ 1 := by
    intro he
    simp [he] at hhi
  have horder : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    intro h
    have he := analyticOn_riemannZeta.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
      (show ρ ∈ ({1}ᶜ : Set ℂ) from hne) (analyticOrderAt_eq_top.mp h)
    exact (riemannZeta_ne_zero_of_one_le_re (s := 2) (by norm_num)) (he (by simp))
  exact ⟨ENat.toNat_pos
    (analyticOrderAt_ne_zero.mpr ⟨analyticOn_riemannZeta ρ hne, hz⟩) horder, horder⟩

/-- Transfer a real-valued full enumeration bound without changing any
quantifier or discarding any possible infinite count. -/
theorem bound_of_literal {σ p ε : ℝ}
    (h : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤ C * T ^ (p + ε)) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (p + ε)) := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, ?_⟩
  intro T hT
  obtain ⟨F, hF⟩ := exact_zero_set_exists σ T
  rw [zeroCount_eq_finset σ T F hF, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (hb T hT F hF)

/-- The same exact transfer keeps a constant uniform over a whole sigma range. -/
theorem uniform_bound_of_literal {D : ℝ → Prop} {p : ℝ → ℝ} {ε : ℝ}
    (h : ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, D σ → 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤ C * T ^ (p σ + ε)) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, D σ → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (p σ + ε)) := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, ?_⟩
  intro σ T hσ hT
  obtain ⟨F, hF⟩ := exact_zero_set_exists σ T
  rw [zeroCount_eq_finset σ T F hF, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (hb σ T hσ hT F hF)

end LewkoDensityPalomar
