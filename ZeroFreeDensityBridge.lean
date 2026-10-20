module
public import MathCollab.Density.ZetaCounting
public import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Montgomery.ZeroFreeHatching
open MathCollab.Density

/-- The recovered source theorem, required at global Mathlib's exact zeta
type. This file must only be certified after the complete source check. -/
theorem actual_zeta_nonzero (s : ℂ) (hs : (7/8:ℝ)<s.re) :
    _root_.riemannZeta s ≠ 0 :=
  OAI.SevenEighths.ProbeFinalAssemblyUnconditional.zeta_nonzero s hs

theorem actual_zero_region_empty {σ a b : ℝ} (hσ : (7/8:ℝ)<σ) :
    zetaZeroFinset σ a b = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro ρ hρ
  obtain ⟨hz, hreal, _⟩ := mem_zetaZeroFinset.mp hρ
  exact actual_zeta_nonzero ρ (hσ.trans_le hreal) hz.1

theorem actual_slab_count_zero {σ a b : ℝ} (hσ : (7/8:ℝ)<σ) :
    zetaSlabCount σ a b = 0 := by
  simp only [zetaSlabCount, actual_zero_region_empty hσ, Finset.sum_empty]

/-- Every real height and closed cutoff, with the existing actual analytic
multiplicity count. The line sigma=7/8 is not included. -/
theorem actual_density_count_zero {σ T : ℝ} (hσ : (7/8:ℝ)<σ) :
    zetaDensityCount σ T = 0 :=
  actual_slab_count_zero hσ

/-- Literal finite zero set and analytic vanishing orders. No count alias
or assumption of a simple zero occurs in this statement. -/
theorem literal_density_count_zero (σ T : ℝ) (hσ : (7/8:ℝ)<σ)
    (F : Finset ℂ)
    (hF : ∀ ρ : ℂ, ρ∈F ↔ _root_.riemannZeta ρ=0 ∧
      0<ρ.re ∧ ρ.re<1 ∧ σ≤ρ.re ∧ |ρ.im|≤T) :
    (∑ ρ∈F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ)=0 := by
  have he : F=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro ρ hρ
    have hh := (hF ρ).mp hρ
    exact actual_zeta_nonzero ρ (hσ.trans_le hh.2.2.2.1) hh.1
  simp only [he, Finset.sum_empty]

end Montgomery.ZeroFreeHatching
