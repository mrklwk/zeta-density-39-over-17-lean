module
public import GuthMaynard.Improvement.MiddleLargeValues
public import GuthMaynard.Improvement.SeparatedSecondMoment

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

def shortDensityA (σ : ℝ) : ℝ := 6/(7*σ+3)
def shortDensityB (σ : ℝ) : ℝ := 3*shortDensityA σ/2
def shortDensityExponent (σ : ℝ) : ℝ := 18*(1-σ)/(7*σ+3)

/-- Exact scale margins and the mean-value comparison throughout the compact
sigma range. The final inequality is sharp at sigma=5/7. -/
theorem short_density_scale_bounds {σ : ℝ} (hσ : 9/13 ≤ σ) (hσ' : σ ≤ 5/7) :
    3/4 ≤ shortDensityA σ ∧ shortDensityA σ ≤ 4/5 ∧
    0 ≤ shortDensityB σ ∧ shortDensityB σ ≤ 6/5 ∧
    0 < shortDensityExponent σ ∧
    11/6-5*σ/3 ≤ shortDensityExponent σ := by
  have hd : 0 < 7*σ+3 := by linarith
  have ha : 3/4 ≤ shortDensityA σ := by
    unfold shortDensityA
    apply (le_div_iff₀ hd).mpr
    linarith
  have ha' : shortDensityA σ ≤ 4/5 := by
    unfold shortDensityA
    apply (div_le_iff₀ hd).mpr
    linarith
  refine ⟨ha,ha',?_,?_,?_,?_⟩
  · unfold shortDensityB; linarith
  · unfold shortDensityB; linarith
  · unfold shortDensityExponent
    exact div_pos (by linarith) hd
  · unfold shortDensityExponent
    apply (le_div_iff₀ hd).mpr
    nlinarith [mul_nonneg (show 0 ≤ 5/7-σ by linarith)
      (show 0 ≤ 3/2-σ by linarith)]

/-- The two large-value budgets meet at the intended density exponent. -/
theorem short_density_scale_identities {σ : ℝ} (hσ : 9/13 ≤ σ) :
    2*shortDensityB σ*(1-σ) = shortDensityExponent σ ∧
    shortDensityA σ*(18/7-4*σ)+6/7 = shortDensityExponent σ := by
  have hd : 7*σ+3 ≠ 0 := by linarith
  simp only [shortDensityB, shortDensityA, shortDensityExponent]
  constructor <;> field_simp [hd] <;> ring

/-- The length split at H^(5/6) respects both exact middle-range endpoints. -/
theorem short_density_middle_time {σ H N : ℝ} (hσ : 9/13 ≤ σ)
    (hσ' : σ ≤ 5/7) (hH : 1 ≤ H) (hN : 0 < N)
    (hlo : H^(shortDensityA σ) ≤ N) (hhi : N ≤ H^(5/6:ℝ)) :
    N^(6/5:ℝ) ≤ H ∧ H ≤ N^(5/3:ℝ) := by
  have hH0 : 0 < H := by linarith
  have ha := (short_density_scale_bounds hσ hσ').1
  constructor
  · have hh := Real.rpow_le_rpow hN.le hhi (by norm_num : (0:ℝ) ≤ 6/5)
    rw [← Real.rpow_mul hH0.le] at hh
    norm_num at hh
    exact hh
  · have hl : H^(3/5:ℝ) ≤ N :=
      (Real.rpow_le_rpow_of_exponent_le hH (by linarith : (3/5:ℝ) ≤ shortDensityA σ)).trans hlo
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hH0.le _) hl
      (by norm_num : (0:ℝ) ≤ 5/3)
    rw [← Real.rpow_mul hH0.le] at hh
    norm_num at hh
    exact hh

/-- The common positive-power term across both length ranges. A small upper
length buffer is charged explicitly, not hidden in the scale convention. -/
theorem short_density_positive_budget {σ H N δ : ℝ} (hσ : 9/13 ≤ σ)
    (hσ' : σ ≤ 5/7) (hH : 1 ≤ H) (hN : 0 ≤ N) (hδ : 0 ≤ δ)
    (hhi : N ≤ H^(shortDensityB σ+δ)) :
    N^(2-2*σ) ≤ H^(shortDensityExponent σ+2*δ) := by
  have hH0 : 0 < H := by linarith
  have hid := (short_density_scale_identities hσ).1
  calc
    _ ≤ (H^(shortDensityB σ+δ))^(2-2*σ) :=
      Real.rpow_le_rpow hN hhi (by linarith)
    _ = H^((shortDensityB σ+δ)*(2-2*σ)) := (Real.rpow_mul hH0.le _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hH (by
      nlinarith [mul_nonneg hδ (show 0 ≤ σ by linarith)])

/-- The decreasing middle-range term uses the lower length endpoint. -/
theorem short_density_middle_budget {σ H N : ℝ} (hσ : 9/13 ≤ σ)
    (hH : 0 < H) (hlo : H^(shortDensityA σ) ≤ N) :
    N^(18/7-4*σ)*H^(6/7:ℝ) ≤ H^(shortDensityExponent σ) := by
  have hm := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hH _) hlo
    (show 18/7-4*σ ≤ 0 by linarith)
  have hid := (short_density_scale_identities hσ).2
  calc
    _ ≤ (H^(shortDensityA σ))^(18/7-4*σ)*H^(6/7:ℝ) :=
      mul_le_mul_of_nonneg_right hm (by positivity)
    _ = _ := by rw [← Real.rpow_mul hH.le, ← Real.rpow_add hH, hid]

/-- Above H^(5/6), the first mean-value term is no larger than the target. -/
theorem short_density_mean_budget {σ H N : ℝ} (hσ : 9/13 ≤ σ)
    (hσ' : σ ≤ 5/7) (hH : 1 ≤ H) (hlo : H^(5/6:ℝ) ≤ N) :
    H*N^(1-2*σ) ≤ H^(shortDensityExponent σ) := by
  have hH0 : 0 < H := by linarith
  have hm := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hH0 _) hlo
    (show 1-2*σ ≤ 0 by linarith)
  have he := (short_density_scale_bounds hσ hσ').2.2.2.2.2
  calc
    _ ≤ H*(H^(5/6:ℝ))^(1-2*σ) := mul_le_mul_of_nonneg_left hm hH0.le
    _ = H^(11/6-5*σ/3) := by
      rw [← Real.rpow_mul hH0.le]
      nth_rw 1 [← Real.rpow_one H]
      rw [← Real.rpow_add hH0]
      congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hH he

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.short_density_scale_bounds
#print axioms GuthMaynard.Improvement.short_density_scale_identities
#print axioms GuthMaynard.Improvement.short_density_middle_time
#print axioms GuthMaynard.Improvement.short_density_positive_budget
#print axioms GuthMaynard.Improvement.short_density_middle_budget
#print axioms GuthMaynard.Improvement.short_density_mean_budget
