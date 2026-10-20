module
public import TraceAlternatives.CubeCenteredReflection
public import DensityEnergyGM.SharpShellBudget

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

def cubeCenteredBudget (T L R E : ℝ) : ℝ :=
  (T+L*T^(1/3:ℝ))*R^(2/3:ℝ)*E^(1/3:ℝ)

theorem cubeCenteredBudget_nonneg {T L R E : ℝ}
    (hT : 0≤T) (hL : 0≤L) (hR : 0≤R) (hE : 0≤E) :
    0 ≤ cubeCenteredBudget T L R E := by
  unfold cubeCenteredBudget
  positivity

/-- The exact physical scale conversion for the cube source profile. -/
theorem cube_shell_budget_le {T L H R E : ℝ}
    (hT : 0<T) (hL : 0<L) (hH : 0<H) (hHT : H≤2*T)
    (hR : 0≤R) (hE : 0≤E) :
    L^2/H*cubeLocalReflectionBudget T L H R E ≤
      2*cubeCenteredBudget T L R E := by
  have hId : L^2/H*cubeLocalReflectionBudget T L H R E =
      (H+L*T^(1/3:ℝ))*R^(2/3:ℝ)*E^(1/3:ℝ) := by
    unfold cubeLocalReflectionBudget
    field_simp
  rw [hId]
  have hLin : H+L*T^(1/3:ℝ) ≤ 2*(T+L*T^(1/3:ℝ)) := by
    nlinarith [mul_nonneg hL.le (Real.rpow_nonneg hT.le (1/3:ℝ))]
  calc
    _ ≤ (2*(T+L*T^(1/3:ℝ)))*R^(2/3:ℝ)*E^(1/3:ℝ) := by gcongr
    _ = _ := by unfold cubeCenteredBudget; ring

end Montgomery.RationalMoment
