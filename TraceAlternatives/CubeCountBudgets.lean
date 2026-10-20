module
public import DensityEnergyGM.SharpCountEnergyExpansion

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

def cubeTraceA : Fin 2 → ℝ := ![1,1/3]
def cubeTraceB : Fin 2 → ℝ := ![-1,0]
def cubeTraceG : Fin 2 → ℝ := ![2/3,2/3]
def cubeTraceD : Fin 2 → ℝ := ![1/3,1/3]

def cubeTraceEnergyMargin (σ a x : ℝ) (j : Fin 2) (i : Fin 5) : ℝ :=
  (2-cubeTraceB j-cubeTraceG j-cubeTraceD j*gmEnergyR i)*(3*a*(1-σ))-
    cubeTraceA j-cubeTraceD j*gmEnergyV i+
    ((4-2*cubeTraceB j-cubeTraceD j*gmEnergyW i)*σ-3+cubeTraceB j-
      cubeTraceD j*gmEnergyU i)*x

theorem cubeTraceEnergy_sublinearity (j : Fin 2) (i : Fin 5) :
    cubeTraceG j+cubeTraceD j*gmEnergyR i ≤ 7/4 := by
  fin_cases j <;> fin_cases i <;>
    norm_num [cubeTraceG,cubeTraceD,gmEnergyR]

theorem cubeTraceEnergyMargin_of_endpoints {σ a x : ℝ} (j : Fin 2) (i : Fin 5)
    (hx : a ≤ x) (hx' : x ≤ 3*a/2)
    (hlo : 0 ≤ cubeTraceEnergyMargin σ a a j i)
    (hhi : 0 ≤ cubeTraceEnergyMargin σ a (3*a/2) j i) :
    0 ≤ cubeTraceEnergyMargin σ a x j i := by
  let c := (4-2*cubeTraceB j-cubeTraceD j*gmEnergyW i)*σ-3+cubeTraceB j-
    cubeTraceD j*gmEnergyU i
  by_cases hc : 0 ≤ c
  · have h := mul_le_mul_of_nonneg_left hx hc
    dsimp only [c] at h
    unfold cubeTraceEnergyMargin at *
    linarith only [hlo,h]
  · have h := mul_le_mul_of_nonpos_left hx' (le_of_not_ge hc)
    dsimp only [c] at h
    unfold cubeTraceEnergyMargin at *
    linarith only [hhi,h]

theorem cubeTraceEnergy_length_slope_nonneg {σ : ℝ} (hσ : 13/16 ≤ σ)
    (j : Fin 2) (i : Fin 5) :
    0 ≤ (4-2*cubeTraceB j-cubeTraceD j*gmEnergyW i)*σ-3+cubeTraceB j-
      cubeTraceD j*gmEnergyU i := by
  fin_cases j <;> fin_cases i <;>
    norm_num [cubeTraceA,cubeTraceB,cubeTraceG,cubeTraceD,gmEnergyU,gmEnergyV,gmEnergyW,gmEnergyR] <;>
    linarith

theorem cubeTraceEnergyMargin_mono_length {σ a x y : ℝ} (hσ : 13/16 ≤ σ)
    (hxy : x ≤ y) (j : Fin 2) (i : Fin 5) :
    cubeTraceEnergyMargin σ a x j i ≤ cubeTraceEnergyMargin σ a y j i := by
  have h := mul_le_mul_of_nonneg_left hxy (cubeTraceEnergy_length_slope_nonneg hσ j i)
  unfold cubeTraceEnergyMargin
  linarith only [h]

end Montgomery.RationalMoment
