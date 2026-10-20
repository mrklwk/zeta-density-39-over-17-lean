module
public import LaterPairs.PhysicalTargetWindows
public import RightSolidTailBudgets

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

/-- Exact genuine-pair tail budgets over the full closed target row6. -/
theorem sharp_row6_tail_budgets {σ : ℝ}
    (hl : 1959705/2298302 ≤ σ) (_hr : σ ≤ 6482825/7570038) :
    let a : ℝ := 597962/(2187648*σ-772245)
    1-6*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ) ∧
    1+(47947/86410:ℝ)/(107193/345640)-(4+(2+4*(47947/86410))/(107193/345640))*((3*a/4)*(σ-1/2)) ≤
      3*a*(1-σ) := by
  dsimp only
  have hd : 0 < 2187648*σ-772245 := by linarith
  rw [show (1:ℝ)+(47947/86410)/(107193/345640)=298981/107193 by norm_num,
    show (4:ℝ)+(2+4*(47947/86410))/(107193/345640)=629068/35731 by norm_num]
  apply tail_budgets_of_fraction hd
  · linarith
  · nlinarith

/-- Exact genuine-pair tail budgets over the full closed target row7. -/
theorem sharp_row7_tail_budgets {σ : ℝ}
    (hl : 6482825/7570038 ≤ σ) (_hr : σ ≤ 2905/3354) :
    let a : ℝ := 16504356/(62198298*σ-22870785)
    1-6*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ) ∧
    1+(2754695/4856993:ℝ)/(1371394/4856993)-(4+(2+4*(2754695/4856993))/(1371394/4856993))*((3*a/4)*(σ-1/2)) ≤
      3*a*(1-σ) := by
  dsimp only
  have hd : 0 < 62198298*σ-22870785 := by linarith
  rw [show (1:ℝ)+(2754695/4856993)/(1371394/4856993)=4126089/1371394 by norm_num,
    show (4:ℝ)+(2+4*(2754695/4856993))/(1371394/4856993)=13109171/685697 by norm_num]
  apply tail_budgets_of_fraction hd
  · linarith
  · nlinarith

/-- Exact genuine-pair tail budgets over the full closed target row8. -/
theorem sharp_row8_tail_budgets {σ : ℝ}
    (hl : 2905/3354 ≤ σ) (_hr : σ ≤ 7/8) :
    let a : ℝ := 2172/(8226*σ-3045)
    1-6*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ) ∧
    1+(365/641:ℝ)/(178/641)-(4+(2+4*(365/641))/(178/641))*((3*a/4)*(σ-1/2)) ≤
      3*a*(1-σ) := by
  dsimp only
  have hd : 0 < 8226*σ-3045 := by linarith
  rw [show (1:ℝ)+(365/641)/(178/641)=543/178 by norm_num,
    show (4:ℝ)+(2+4*(365/641))/(178/641)=1727/89 by norm_num]
  apply tail_budgets_of_fraction hd
  · linarith
  · nlinarith

/-- Identification with the requested row6 density exponent. -/
theorem sharp_row6_density_exponent {σ : ℝ} :
    3*(597962/(2187648*σ-772245))*(1-σ) =
      597962*(1-σ)/(729216*σ-257415) := by
  have hd : 2187648*σ-772245 = 3*(729216*σ-257415) := by ring
  calc
    _ = (3*597962/(3*(729216*σ-257415)))*(1-σ) := by rw [hd]; ring
    _ = (597962/(729216*σ-257415))*(1-σ) := by
      rw [mul_div_mul_left _ _ (by norm_num : (3:ℝ) ≠ 0)]
    _ = _ := div_mul_eq_mul_div _ _ _

/-- Identification with the requested row7 density exponent. -/
theorem sharp_row7_density_exponent {σ : ℝ} :
    3*(16504356/(62198298*σ-22870785))*(1-σ) =
      16504356*(1-σ)/(20732766*σ-7623595) := by
  have hd : 62198298*σ-22870785 = 3*(20732766*σ-7623595) := by ring
  calc
    _ = (3*16504356/(3*(20732766*σ-7623595)))*(1-σ) := by rw [hd]; ring
    _ = (16504356/(20732766*σ-7623595))*(1-σ) := by
      rw [mul_div_mul_left _ _ (by norm_num : (3:ℝ) ≠ 0)]
    _ = _ := div_mul_eq_mul_div _ _ _

/-- Identification with the requested row8 density exponent. -/
theorem sharp_row8_density_exponent {σ : ℝ} :
    3*(2172/(8226*σ-3045))*(1-σ) =
      2172*(1-σ)/(2742*σ-1015) := by
  have hd : 8226*σ-3045 = 3*(2742*σ-1015) := by ring
  calc
    _ = (3*2172/(3*(2742*σ-1015)))*(1-σ) := by rw [hd]; ring
    _ = (2172/(2742*σ-1015))*(1-σ) := by
      rw [mul_div_mul_left _ _ (by norm_num : (3:ℝ) ≠ 0)]
    _ = _ := div_mul_eq_mul_div _ _ _

end Montgomery.RationalMoment
