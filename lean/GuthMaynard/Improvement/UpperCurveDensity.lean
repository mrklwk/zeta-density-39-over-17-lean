import GuthMaynard.Improvement.UpperCurveTypeICount
import GuthMaynard.Improvement.WeakShortDensity

open Complex Filter Set MathCollab.Density
open scoped Topology
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- Uniform actual slab density, using the proved weaker moment.
Both separated branch estimates, contour detection and analytic multiplicity
restoration are proved dependencies. -/
theorem upper_curve_slab_density
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ σ : ℝ,
      5/7 ≤ σ → σ ≤ 3/4 →
      (zetaSlabCount σ H (2*H):ℝ) ≤ C*H^(((9/4)*(1-σ))+ε) := by
  have hη : 0 < ε/2 := by positivity
  obtain ⟨CI,hCI,hI⟩ := upper_curve_typeI_zero_slab_count hη
  obtain ⟨CII,hCII,hII⟩ := weak_short_typeII_zero_slab_count hη
  obtain ⟨C₀,hC₀,hrestore⟩ := short_slab_count_of_separated_branch_bounds
  let D : ℝ := Real.log 2+1/(ε/2)
  have hD : 0 < D := by
    dsimp [D]
    exact add_pos_of_nonneg_of_pos (Real.log_nonneg (by norm_num)) (one_div_pos.mpr hη)
  refine ⟨C₀*(CI+CII)*D,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (2:ℝ),hI,hII,hrestore] with H hH hi hii hr
  intro σ hσ hσ'
  have hσ₀ : 9/13 ≤ σ := by linarith
  have hIIexp : 2-2*σ+1/25 ≤ (9/4)*(1-σ) := by nlinarith
  have hH1 : 1 ≤ H := by linarith
  have hH0 : 0 < H := by linarith
  have hb := hr σ (CI*H^(((9/4)*(1-σ))+ε/2))
    (CII*H^(((9/4)*(1-σ))+ε/2)) hσ₀ (fun R hR hc hs hl => hi σ R hσ hσ' hR hc hs hl) (by
      intro R hR hc hs hl
      exact (hii σ R hσ₀ hR hc hs hl).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hH1
          (by linarith)) hCII.le))
  have hlog : Real.log (2*H) ≤ D*H^(ε/2) := classical_log_budget hH1 hη
  calc
    _ ≤ C₀*Real.log (2*H)*(CI*H^(((9/4)*(1-σ))+ε/2)+CII*H^(((9/4)*(1-σ))+ε/2)) := hb
    _ ≤ C₀*(D*H^(ε/2))*(CI*H^(((9/4)*(1-σ))+ε/2)+CII*H^(((9/4)*(1-σ))+ε/2)) := by gcongr
    _ = (C₀*(CI+CII)*D)*(H^(ε/2)*H^(((9/4)*(1-σ))+ε/2)) := by ring
    _ = _ := by rw [← Real.rpow_add hH0]; congr 2; ring

/-- All actual zeros with analytic multiplicity and both signs. The audited
fixed-sigma dyadic summation is reused, so this constant may depend on sigma. -/
theorem upper_curve_density
    {σ ε : ℝ} (hσ : 5/7 ≤ σ) (hσ' : σ ≤ 3/4) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^((9/4)*(1-σ)+ε) := by
  obtain ⟨C,hC,hslab⟩ := upper_curve_slab_density hε
  have hp : 0 < ((9/4)*(1-σ))+ε := by
    nlinarith
  apply zetaDensity_bound_of_eventual_slabs hp hC
  filter_upwards [hslab] with H hh
  exact hh σ hσ hσ'

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.upper_curve_slab_density
#print axioms GuthMaynard.Improvement.upper_curve_density
