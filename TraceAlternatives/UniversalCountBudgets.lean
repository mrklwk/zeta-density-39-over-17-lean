module
public import DensityEnergyGM.SharpCountEnergyExpansion

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

def universalTraceA : Fin 3 → ℝ := ![1,1/2,9/16]
def universalTraceB : Fin 3 → ℝ := ![-1,-1/3,-1/2]
def universalTraceG : Fin 3 → ℝ := ![0,1,19/12]
def universalTraceD : Fin 3 → ℝ := ![1/2,1/4,5/48]

def universalTraceEnergyMargin (σ a x : ℝ) (j : Fin 3) (i : Fin 5) : ℝ :=
  (2-universalTraceB j-universalTraceG j-universalTraceD j*gmEnergyR i)*(3*a*(1-σ))-
    universalTraceA j-universalTraceD j*gmEnergyV i+
    ((4-2*universalTraceB j-universalTraceD j*gmEnergyW i)*σ-3+universalTraceB j-
      universalTraceD j*gmEnergyU i)*x

theorem universalTraceEnergy_sublinearity (j : Fin 3) (i : Fin 5) :
    universalTraceG j+universalTraceD j*gmEnergyR i ≤ 15/8 := by
  fin_cases j <;> fin_cases i <;>
    norm_num [universalTraceG,universalTraceD,gmEnergyR]

theorem universalTraceEnergyMargin_of_endpoints {σ a x : ℝ} (j : Fin 3) (i : Fin 5)
    (hx : a ≤ x) (hx' : x ≤ 3*a/2)
    (hlo : 0 ≤ universalTraceEnergyMargin σ a a j i)
    (hhi : 0 ≤ universalTraceEnergyMargin σ a (3*a/2) j i) :
    0 ≤ universalTraceEnergyMargin σ a x j i := by
  let c := (4-2*universalTraceB j-universalTraceD j*gmEnergyW i)*σ-3+universalTraceB j-
    universalTraceD j*gmEnergyU i
  by_cases hc : 0 ≤ c
  · have h := mul_le_mul_of_nonneg_left hx hc
    dsimp only [c] at h
    unfold universalTraceEnergyMargin at *
    linarith only [hlo,h]
  · have h := mul_le_mul_of_nonpos_left hx' (le_of_not_ge hc)
    dsimp only [c] at h
    unfold universalTraceEnergyMargin at *
    linarith only [hhi,h]

theorem universalTraceEnergy_length_slope_nonneg {σ : ℝ} (hσ : 7873/9370 ≤ σ)
    (j : Fin 3) (i : Fin 5) :
    0 ≤ (4-2*universalTraceB j-universalTraceD j*gmEnergyW i)*σ-3+universalTraceB j-
      universalTraceD j*gmEnergyU i := by
  fin_cases j <;> fin_cases i <;>
    norm_num [universalTraceA,universalTraceB,universalTraceG,universalTraceD,gmEnergyU,gmEnergyV,gmEnergyW,gmEnergyR] <;>
    linarith

theorem universalTraceEnergyMargin_mono_length {σ a x y : ℝ} (hσ : 7873/9370 ≤ σ)
    (hxy : x ≤ y) (j : Fin 3) (i : Fin 5) :
    universalTraceEnergyMargin σ a x j i ≤ universalTraceEnergyMargin σ a y j i := by
  have h := mul_le_mul_of_nonneg_left hxy (universalTraceEnergy_length_slope_nonneg hσ j i)
  unfold universalTraceEnergyMargin
  linarith only [h]

end Montgomery.RationalMoment
