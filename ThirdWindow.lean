module
public import GeneralAdditiveEnergy
public import GeneralCubicLargeValues
public import GeneralDetectorCover

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

/-- Explicit amplifier exponent for the third orange branch. -/
def thirdAmplifierExponent (σ p x : ℝ) : ℝ :=
  max x (max (5/6:ℝ) (2+(4-6*σ)*x-3*p/2))

/-- Only arithmetic inequalities appear in this window. Its analytic
consequences are proved separately and its pictured parameters are discharged. -/
structure ThirdWindow (σ a p α : ℝ) : Prop where
  sigma_low : 9/13 ≤ σ
  sigma_high : σ ≤ 3/4
  a_low : 69/100 ≤ a
  a_high : a ≤ 4/5
  p_low : 1/2 ≤ p
  alpha_low : a ≤ α
  alpha_high : α ≤ 1
  p_identity : p=3*a*(1-σ)
  mean_identity : 1+α*(1-2*σ)=p
  typeII : 2-2*σ+1/50 ≤ p
  budgets : ∀ x : ℝ, a ≤ x → x ≤ α →
    let l := thirdAmplifierExponent σ p x
    l ≤ 1 ∧ l ≤ p+(2*σ-1)*x ∧ l ≤ p+(6*σ-4)*x ∧
    l ≤ (49/40)*p+(6*σ-4)*x-1/8 ∧
    2 ≤ 4*p+(16*σ-12)*x ∧
    2 ≤ 2*p+(14*σ-9)*x ∧
    3 ≤ (5/2)*p+(14*σ-8)*x ∧
    9/4 ≤ (29/12)*p+(14*σ-9)*x ∧
    1 ≤ (5/4)*p+(6*σ-4)*x

lemma affine_nonneg_between {a b x q r : ℝ} (ha : a ≤ x) (hb : x ≤ b)
    (h₁ : 0 ≤ q*a+r) (h₂ : 0 ≤ q*b+r) : 0 ≤ q*x+r := by
  by_cases hq : 0 ≤ q
  · have := mul_le_mul_of_nonneg_left ha hq
    linarith
  · have := mul_le_mul_of_nonpos_left hb (le_of_not_ge hq)
    linarith

end Montgomery.RationalMoment
