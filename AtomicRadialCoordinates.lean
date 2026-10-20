module
public import FiniteCubicBasics
public import GuthMaynard.Improvement.RetainedRadialAssembly

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped FourierTransform ContDiff
namespace GuthMaynard.Improvement.AtomicCubic

/-- A general compact-frequency profile; no ordinary time density is assumed. -/
def ratioFourierProduct (F : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  F (-mellinFrequency p.1)*F (mellinFrequency p.1-mellinFrequency p.2)*F (mellinFrequency p.2)

theorem ratio_fourier_measurable {F : ℝ → ℂ} (hF : Continuous F) : Measurable (ratioFourierProduct F) := by
  unfold ratioFourierProduct mellinFrequency
  fun_prop

theorem ratio_fourier_bound {F : ℝ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ ξ, ‖F ξ‖ ≤ M) (p : ℝ × ℝ) : ‖ratioFourierProduct F p‖ ≤ M^3 := by
  unfold ratioFourierProduct
  simp only [norm_mul]
  calc
    _ ≤ M*M*M := by gcongr <;> exact hb _
    _ = _ := by ring

def spatialCubicMode (a : ℝ → ℂ) (F : ℝ → ℂ) (L : ℝ) (m : ℤ × (ℤ × ℤ))
    (x₁ x₂ r : ℝ) : ℂ :=
  (a x₁*a x₂*a r)*phase (-L*((m.1:ℝ)*x₁+(m.2.1:ℝ)*x₂+(m.2.2:ℝ)*r))*
    (F (mellinFrequency r-mellinFrequency x₁)*
      F (mellinFrequency x₁-mellinFrequency x₂)*
      F (mellinFrequency x₂-mellinFrequency r))
/-- Exact radial integrand identity on positive cutoff support. The full
Fourier triple product is retained, not replaced by a mass majorant. -/
theorem spatialCubicMode_radial {a : ℝ → ℂ} (ha : ∀ x, x ≤ 0 → a x = 0)
    (F : ℝ → ℂ) (L : ℝ) (m : ℤ × (ℤ × ℤ)) (r v y : ℝ) :
    (r:ℂ)^2*spatialCubicMode a F L m (r*v) (r*y) r =
      radialAmplitude a v y r*phase (-L*((m.1:ℝ)*v+(m.2.1:ℝ)*y+(m.2.2:ℝ))*r)*ratioFourierProduct F (v,y) := by
  by_cases hr : a r = 0
  · simp [spatialCubicMode,radialAmplitude,hr]
  by_cases hv : a (r*v) = 0
  · simp [spatialCubicMode,radialAmplitude,mul_comm v r,hv]
  by_cases hy : a (r*y) = 0
  · simp [spatialCubicMode,radialAmplitude,mul_comm y r,hy]
  have hrp : 0 < r := lt_of_not_ge (fun h => hr (ha r h))
  have hvp : 0 < v := by
    by_contra hn
    exact hv (ha _ (mul_nonpos_of_nonneg_of_nonpos hrp.le (le_of_not_gt hn)))
  have hyp : 0 < y := by
    by_contra hn
    exact hy (ha _ (mul_nonpos_of_nonneg_of_nonpos hrp.le (le_of_not_gt hn)))
  have h₁ : mellinFrequency r-mellinFrequency (r*v) = -mellinFrequency v := by
    rw [mellinFrequency_mul hrp.ne' hvp.ne']; ring
  have h₂ : mellinFrequency (r*v)-mellinFrequency (r*y) = mellinFrequency v-mellinFrequency y := by
    rw [mellinFrequency_mul hrp.ne' hvp.ne',mellinFrequency_mul hrp.ne' hyp.ne']; ring
  have h₃ : mellinFrequency (r*y)-mellinFrequency r = mellinFrequency y := by
    rw [mellinFrequency_mul hrp.ne' hyp.ne']; ring
  unfold spatialCubicMode
  rw [h₁,h₂,h₃]
  have hp : -L*((m.1:ℝ)*(r*v)+(m.2.1:ℝ)*(r*y)+(m.2.2:ℝ)*r) =
      -L*((m.1:ℝ)*v+(m.2.1:ℝ)*y+(m.2.2:ℝ))*r := by ring
  rw [hp]
  unfold radialAmplitude ratioFourierProduct
  rw [mul_comm v r,mul_comm y r]
  ring

/-- Exact iterated radial-coordinate reduction for each actual retained
spatial mode. This does not silently interchange the r and ratio integrals;
that Fubini step still requires its integrability argument. -/
theorem spatialCubicMode_radial_integrals {a : ℝ → ℂ} (ha : ∀ x, x ≤ 0 → a x = 0)
    (F : ℝ → ℂ) (L : ℝ) (m : ℤ × (ℤ × ℤ)) :
    (∫ r, ∫ x₁, ∫ x₂, spatialCubicMode a F L m x₁ x₂ r) =
      ∫ r, ∫ v, ∫ y, radialAmplitude a v y r*
        phase (-L*((m.1:ℝ)*v+(m.2.1:ℝ)*y+(m.2.2:ℝ))*r)*ratioFourierProduct F (v,y) := by
  apply integral_congr_ae
  filter_upwards with r
  by_cases hr : r = 0
  · subst r
    simp [spatialCubicMode,radialAmplitude,ha 0 le_rfl]
  · rw [← two_coordinate_scaling (fun x₁ x₂ => spatialCubicMode a F L m x₁ x₂ r) hr]
    simp_rw [spatialCubicMode_radial ha]

end GuthMaynard.Improvement.AtomicCubic
