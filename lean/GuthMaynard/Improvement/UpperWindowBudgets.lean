module
public import GuthMaynard.Improvement.ShortDensityHeight

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- Four exact exponent comparisons for the padded upper window. -/
theorem upper_window_exponents {σ : ℝ} (hσ : 5/7 ≤ σ) (hσ' : σ ≤ 3/4) :
    (9/4)*(1-σ) ≤ (39/17)*(1-σ) ∧
    39/14-3*σ ≤ (39/17)*(1-σ) ∧
    63/20-7*σ/2 ≤ (39/17)*(1-σ) ∧
    15/8-7*σ/4 ≤ (39/17)*(1-σ) := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Length losses and the first large-value term in the fixed powered window. -/
theorem upper_window_length_budgets {σ H N δ : ℝ}
    (hσ : 5/7 ≤ σ) (hσ' : σ ≤ 3/4) (hH : 1 ≤ H) (hN : 0 ≤ N)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/100) (hhi : N ≤ H^(9/8+δ)) :
    N^δ ≤ H^(2*δ) ∧
    N^(2-2*σ) ≤ H^((39/17)*(1-σ)+2*δ) := by
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
        have he := (upper_window_exponents hσ hσ').1
        nlinarith [mul_nonneg hδ (show 0 ≤ σ by linarith)])

/-- Padding the time interval preserves the exact middle-range hypotheses and
bounds the second term up to length H^(7/8). No sampling assumption is added. -/
theorem upper_window_padded_time {σ H N : ℝ}
    (hσ : 5/7 ≤ σ) (hσ' : σ ≤ 3/4) (hH : 1 ≤ H) (hN : 2 ≤ N)
    (hlo : H^(3/4:ℝ) ≤ N) (hhi : N ≤ H^(7/8:ℝ)) :
    ∃ S : ℝ, N^(6/5:ℝ) ≤ S ∧ S ≤ N^(5/3:ℝ) ∧ H ≤ S ∧
      N^(18/7-4*σ)*S^(6/7:ℝ) ≤ H^((39/17)*(1-σ)) := by
  have hH0 : 0 < H := by linarith
  have hN0 : 0 < N := by linarith
  have he := upper_window_exponents hσ hσ'
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
        _ ≤ (H^(7/8:ℝ))^(18/5-4*σ) :=
          Real.rpow_le_rpow hN0.le hhi (by linarith)
        _ = H^(63/20-7*σ/2) := by rw [← Real.rpow_mul hH0.le]; congr 1; ring
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hH he.2.2.1

/-- Ordinary mean value closes lengths above the second split. -/
theorem upper_window_mean_budget {σ H N : ℝ}
    (hσ : 5/7 ≤ σ) (hσ' : σ ≤ 3/4) (hH : 1 ≤ H)
    (hlo : H^(7/8:ℝ) ≤ N) :
    H*N^(1-2*σ) ≤ H^((39/17)*(1-σ)) := by
  have hH0 : 0 < H := by linarith
  calc
    _ ≤ H*(H^(7/8:ℝ))^(1-2*σ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by positivity) hlo (by linarith)) hH0.le
    _ = H^(15/8-7*σ/4) := by
      rw [← Real.rpow_mul hH0.le]
      nth_rw 1 [← Real.rpow_one H]
      rw [← Real.rpow_add hH0]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hH (upper_window_exponents hσ hσ').2.2.2

/-- Threshold algebra retains the original H even when the time is padded. -/
theorem upper_window_padded_denominator {H N : ℝ} (hH : 0 < H) (hN : 0 < N)
    (S σ δ : ℝ) :
    N^(18/7:ℝ)*S^(6/7:ℝ)/(N^σ*H^(-2*δ))^4 =
      (N^(18/7-4*σ)*S^(6/7:ℝ))*H^(8*δ) := by
  have hV := (short_density_height_eq hH hN σ δ).1
  have hnσ : N^σ ≠ 0 := (Real.rpow_pos_of_pos hN _).ne'
  have hhδ : H^δ ≠ 0 := (Real.rpow_pos_of_pos hH _).ne'
  have hn4 : N^(18/7-4*σ) = N^(18/7:ℝ)/(N^σ)^4 := by
    rw [Real.rpow_sub hN,show 4*σ = σ*4 by ring,
      Real.rpow_mul hN.le σ 4,Real.rpow_ofNat]
  have hh8 : H^(8*δ) = (H^δ)^8 := by
    rw [show 8*δ = δ*8 by ring,Real.rpow_mul hH.le δ 8,Real.rpow_ofNat]
  rw [hV,hn4,hh8]
  field_simp

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.upper_window_exponents
#print axioms GuthMaynard.Improvement.upper_window_length_budgets
#print axioms GuthMaynard.Improvement.upper_window_padded_time
#print axioms GuthMaynard.Improvement.upper_window_mean_budget
#print axioms GuthMaynard.Improvement.upper_window_padded_denominator
