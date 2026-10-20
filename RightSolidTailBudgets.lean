module
public import DetectorPowerRange

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

def rightSolidTailK (σ : ℝ) : ℝ :=
  if σ ≤ 1015/1294 then 64/135
  else if σ ≤ 353/447 then 371/792
  else if σ ≤ 467/586 then 129/280
  else 85/189

def rightSolidTailL (σ : ℝ) : ℝ :=
  if σ ≤ 1015/1294 then 122/243
  else if σ ≤ 353/447 then 177/352
  else if σ ≤ 467/586 then 247/490
  else 41/81

theorem first_tail_budget_of_length {σ a : ℝ} (ha : 4 ≤ a*(6*σ+3)) :
    1-6*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ) := by nlinarith

theorem second_tail_budget_of_length {σ a φ b : ℝ}
    (ha : φ ≤ a*(3*(1-σ)+(3*b/4)*(σ-1/2))) :
    φ-b*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ) := by nlinarith

theorem tail_budgets_of_fraction {σ n d φ b : ℝ} (hd : 0 < d)
    (hfirst : 4*d ≤ n*(6*σ+3))
    (hsecond : φ*d ≤ n*(3*(1-σ)+(3*b/4)*(σ-1/2))) :
    1-6*((3*(n/d)/4)*(σ-1/2)) ≤ 3*(n/d)*(1-σ) ∧
    φ-b*((3*(n/d)/4)*(σ-1/2)) ≤ 3*(n/d)*(1-σ) := by
  constructor
  · apply first_tail_budget_of_length
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hd).mpr hfirst
  · apply second_tail_budget_of_length
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hd).mpr hsecond

/-- Both exact tail exponents meet all five closed solid branches. -/
theorem rightSolid_tail_budgets {σ : ℝ} (hl : 7/9 ≤ σ) (hr : σ ≤ 4/5) :
    let a := rightSolidLengthExponent σ
    let k := rightSolidTailK σ
    let l := rightSolidTailL σ
    1-6*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ) ∧
    1+l/k-(4+(2+4*l)/k)*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ) := by
  dsimp only
  by_cases h1 : σ ≤ 29359/37574
  · have h2 : σ ≤ (1015:ℝ)/1294 := by linarith
    simp only [rightSolidLengthExponent,rightSolidTailK,rightSolidTailL,ite_eq_left h1,ite_eq_left h2]
    rw [show (1:ℝ)+(122/243)/(64/135)=593/288 by norm_num,
      show (4:ℝ)+(2+4*(122/243))/(64/135)=3587/288 by norm_num]
    apply tail_budgets_of_fraction
    · linarith
    · nlinarith
    · nlinarith
  by_cases h2 : σ ≤ 1015/1294
  · simp only [rightSolidLengthExponent,rightSolidTailK,rightSolidTailL,ite_eq_right h1,ite_eq_left h2]
    rw [show (1:ℝ)+(122/243)/(64/135)=593/288 by norm_num,
      show (4:ℝ)+(2+4*(122/243))/(64/135)=3587/288 by norm_num]
    apply tail_budgets_of_fraction
    · linarith
    · nlinarith
    · nlinarith
  by_cases h3 : σ ≤ 353/447
  · simp only [rightSolidLengthExponent,rightSolidTailK,rightSolidTailL,ite_eq_right h1,ite_eq_right h2,ite_eq_left h3]
    rw [show (1:ℝ)+(177/352)/(371/792)=3077/1484 by norm_num,
      show (4:ℝ)+(2+4*(177/352))/(371/792)=4661/371 by norm_num]
    apply tail_budgets_of_fraction
    · linarith
    · nlinarith
    · nlinarith
  by_cases h4 : σ ≤ 467/586
  · simp only [rightSolidLengthExponent,rightSolidTailK,rightSolidTailL,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_left h4]
    rw [show (1:ℝ)+(247/490)/(129/280)=1891/903 by norm_num,
      show (4:ℝ)+(2+4*(247/490))/(129/280)=3828/301 by norm_num]
    apply tail_budgets_of_fraction
    · linarith
    · nlinarith
    · nlinarith
  simp only [rightSolidLengthExponent,rightSolidTailK,rightSolidTailL,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4]
  rw [show (1:ℝ)+(41/81)/(85/189)=542/255 by norm_num,
    show (4:ℝ)+(2+4*(41/81))/(85/189)=3302/255 by norm_num]
  apply tail_budgets_of_fraction
  · linarith
  · nlinarith
  · nlinarith
end Montgomery.RationalMoment
