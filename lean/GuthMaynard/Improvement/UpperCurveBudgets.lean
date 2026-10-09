import GuthMaynard.Improvement.UpperWindowBudgets

set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- Choose one of two fixed length splits, with overlap at sigma=18/25. -/
def upperCurveSplit (σ : ℝ) : ℝ := if σ ≤ 18/25 then 6/7 else 7/8

/-- Exact comparisons retain the first-term exponent throughout the upper interval. -/
theorem upper_curve_exponents {σ : ℝ} (hσ : 5/7 ≤ σ) (hσ' : σ ≤ 3/4) :
    (9/4)*(1-σ) ≤ (9/4)*(1-σ) ∧
    39/14-3*σ ≤ (9/4)*(1-σ) ∧
    upperCurveSplit σ*(18/5-4*σ) ≤ (9/4)*(1-σ) ∧
    1+upperCurveSplit σ*(1-2*σ) ≤ (9/4)*(1-σ) := by
  constructor
  · exact le_rfl
  constructor
  · linarith
  unfold upperCurveSplit
  split_ifs with h <;> constructor <;> linarith

/-- Length losses and the first large-value term in the fixed powered window. -/
theorem upper_curve_length_budgets {σ H N δ : ℝ}
    (hσ : 5/7 ≤ σ) (hσ' : σ ≤ 3/4) (hH : 1 ≤ H) (hN : 0 ≤ N)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/100) (hhi : N ≤ H^(9/8+δ)) :
    N^δ ≤ H^(2*δ) ∧
    N^(2-2*σ) ≤ H^((9/4)*(1-σ)+2*δ) := by
  have hH0 : 0 < H := by linarith
  constructor
  · calc
      _ ≤ (H^(9/8+δ))^δ := Real.rpow_le_rpow hN hhi hδ
      _ = H^((9/8+δ)*δ) := (Real.rpow_mul hH0.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hH
        (mul_le_mul_of_nonneg_right (by linarith : 9/8+δ ≤ 2) hδ)
  · calc
      _ ≤ (H^(9/8+δ))^(2-2*σ) := Real.rpow_le_rpow hN hhi (by linarith)
      _ = H^((9/8+δ)*(2-2*σ)) := (Real.rpow_mul hH0.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hH (by
        have he := (upper_curve_exponents hσ hσ').1
        nlinarith [mul_nonneg hδ (show 0 ≤ σ by linarith)])

/-- Padding the time interval preserves the exact middle-range hypotheses and
bounds the second term up to the sigma-dependent split. No sampling assumption is added. -/
theorem upper_curve_padded_time {σ H N : ℝ}
    (hσ : 5/7 ≤ σ) (hσ' : σ ≤ 3/4) (hH : 1 ≤ H) (hN : 2 ≤ N)
    (hlo : H^(3/4:ℝ) ≤ N) (hhi : N ≤ H^(upperCurveSplit σ)) :
    ∃ S : ℝ, N^(6/5:ℝ) ≤ S ∧ S ≤ N^(5/3:ℝ) ∧ H ≤ S ∧
      N^(18/7-4*σ)*S^(6/7:ℝ) ≤ H^((9/4)*(1-σ)) := by
  have hH0 : 0 < H := by linarith
  have hN0 : 0 < N := by linarith
  have he := upper_curve_exponents hσ hσ'
  by_cases hm : N ≤ H^(5/6:ℝ)
  · refine ⟨H,?_,?_,le_rfl,?_⟩
    · calc
        _ ≤ (H^(5/6:ℝ))^(6/5:ℝ) := Real.rpow_le_rpow hN0.le hm (by norm_num)
        _ = H := by rw [← Real.rpow_mul hH0.le]; norm_num
    · calc
        H = H^(1:ℝ) := (Real.rpow_one H).symm
        _ ≤ H^((3/4:ℝ)*(5/3)) := Real.rpow_le_rpow_of_exponent_le hH (by norm_num)
        _ = (H^(3/4:ℝ))^(5/3:ℝ) := Real.rpow_mul hH0.le _ _
        _ ≤ _ := Real.rpow_le_rpow (by positivity) hlo (by norm_num)
    · calc
        _ ≤ (H^(3/4:ℝ))^(18/7-4*σ)*H^(6/7:ℝ) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos
            (by positivity) hlo (by linarith)) (by positivity)
        _ = H^(39/14-3*σ) := by
          rw [← Real.rpow_mul hH0.le,← Real.rpow_add hH0]; congr 1; ring
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hH he.2.1
  · refine ⟨N^(6/5:ℝ),le_rfl,?_,?_,?_⟩
    · exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    · calc
        H = (H^(5/6:ℝ))^(6/5:ℝ) := by rw [← Real.rpow_mul hH0.le]; norm_num
        _ ≤ _ := Real.rpow_le_rpow (by positivity) (le_of_not_ge hm) (by norm_num)
    · calc
        _ = N^(18/5-4*σ) := by
          rw [← Real.rpow_mul hN0.le,← Real.rpow_add hN0]; congr 1; ring
        _ ≤ (H^(upperCurveSplit σ))^(18/5-4*σ) :=
          Real.rpow_le_rpow hN0.le hhi (by linarith)
        _ = H^(upperCurveSplit σ*(18/5-4*σ)) := by rw [← Real.rpow_mul hH0.le]
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hH he.2.2.1

/-- Ordinary mean value closes lengths above the second split. -/
theorem upper_curve_mean_budget {σ H N : ℝ}
    (hσ : 5/7 ≤ σ) (hσ' : σ ≤ 3/4) (hH : 1 ≤ H)
    (hlo : H^(upperCurveSplit σ) ≤ N) :
    H*N^(1-2*σ) ≤ H^((9/4)*(1-σ)) := by
  have hH0 : 0 < H := by linarith
  calc
    _ ≤ H*(H^(upperCurveSplit σ))^(1-2*σ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by positivity) hlo (by linarith)) hH0.le
    _ = H^(1+upperCurveSplit σ*(1-2*σ)) := by
      rw [← Real.rpow_mul hH0.le]
      nth_rw 1 [← Real.rpow_one H]
      rw [← Real.rpow_add hH0]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hH (upper_curve_exponents hσ hσ').2.2.2

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.upper_curve_exponents
#print axioms GuthMaynard.Improvement.upper_curve_length_budgets
#print axioms GuthMaynard.Improvement.upper_curve_padded_time
#print axioms GuthMaynard.Improvement.upper_curve_mean_budget
