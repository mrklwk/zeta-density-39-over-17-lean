import Mathlib
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

def middleLength (N T : ℝ) : ℝ := N^((1:ℝ)/7)*T^((5:ℝ)/7)
def middleThreshold (N T : ℝ) : ℝ := N^((5:ℝ)/7)*T^((1:ℝ)/14)
def middleMoment (N T : ℝ) : ℝ := N^((18:ℝ)/7)*T^((6:ℝ)/7)

theorem middle_time_bounds {N T : ℝ} (hN : 2 ≤ N)
    (hlo : N^((6:ℝ)/5) ≤ T) (hhi : T ≤ N^((5:ℝ)/3)) :
    N ≤ T ∧ T ≤ N^2 := by
  have hn : 1 ≤ N := by linarith
  constructor
  · have hh := Real.rpow_le_rpow_of_exponent_le hn (by norm_num : (1:ℝ)≤6/5)
    rw [Real.rpow_one] at hh
    exact hh.trans hlo
  · have hh := Real.rpow_le_rpow_of_exponent_le hn (by norm_num : (5:ℝ)/3≤2)
    rw [Real.rpow_ofNat] at hh
    exact hhi.trans hh

theorem middle_length_bounds {N T : ℝ} (hN : 2 ≤ N)
    (hlo : N^((6:ℝ)/5) ≤ T) (hhi : T ≤ N^((5:ℝ)/3)) :
    N ≤ middleLength N T ∧ T^((4:ℝ)/5) ≤ middleLength N T ∧
      middleLength N T ≤ T := by
  have hnt := (middle_time_bounds hN hlo hhi).1
  have hn : 0 < N := by linarith
  have ht : 0 < T := by linarith
  have ht1 : 1 ≤ T := by linarith
  unfold middleLength
  constructor
  · have hh := Real.rpow_le_rpow (Real.rpow_nonneg hn.le _) hlo
      (by norm_num : (0:ℝ)≤5/7)
    rw [← Real.rpow_mul hn.le] at hh
    norm_num at hh
    calc
      N = N^((1:ℝ)/7)*N^((6:ℝ)/7) := by rw [← Real.rpow_add hn]; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hn.le _)
  constructor
  · have hh := Real.rpow_le_rpow ht.le hhi (by norm_num : (0:ℝ)≤3/35)
    rw [← Real.rpow_mul hn.le] at hh
    norm_num at hh
    calc
      T^((4:ℝ)/5) = T^((3:ℝ)/35)*T^((5:ℝ)/7) := by rw [← Real.rpow_add ht]; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg ht.le _)
  · calc
      _ ≤ T^((1:ℝ)/7)*T^((5:ℝ)/7) := by gcongr
      _ = T^((6:ℝ)/7) := by rw [← Real.rpow_add ht]; norm_num
      _ ≤ T^((1:ℝ)) := Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
      _ = T := Real.rpow_one _

/-- The factor-five rescaling matches the actual time support of the source. -/
theorem middle_rescaled_length_bounds {N T : ℝ} (hN : 2 ≤ N)
    (hlo : N^((6:ℝ)/5) ≤ T) (hhi : T ≤ N^((5:ℝ)/3)) :
    N ≤ 5*middleLength N T ∧ (5*T)^((4:ℝ)/5) ≤ 5*middleLength N T ∧
      5*middleLength N T ≤ 5*T ∧ 5*middleLength N T ≤ 5*N^2 := by
  obtain ⟨hnl,htl,hlt⟩ := middle_length_bounds hN hlo hhi
  obtain ⟨hnt,htn⟩ := middle_time_bounds hN hlo hhi
  have ht : 0 ≤ T := by linarith
  have hfive : (5:ℝ)^((4:ℝ)/5) ≤ 5 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤5)
      (by norm_num : (4:ℝ)/5≤1)
    simpa only [Real.rpow_one] using hh
  refine ⟨by linarith,?_,by linarith,by linarith⟩
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤5) ht]
  exact (mul_le_mul_of_nonneg_right hfive (Real.rpow_nonneg ht _)).trans
    (mul_le_mul_of_nonneg_left htl (by norm_num))

theorem middle_threshold_ge_one {N T : ℝ} (hN : 1 ≤ N) (hT : 1 ≤ T) :
    1 ≤ middleThreshold N T := by
  exact one_le_mul_of_one_le_of_one_le
    (Real.one_le_rpow hN (by norm_num)) (Real.one_le_rpow hT (by norm_num))

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.middle_time_bounds
#print axioms GuthMaynard.Improvement.middle_length_bounds
#print axioms GuthMaynard.Improvement.middle_rescaled_length_bounds
#print axioms GuthMaynard.Improvement.middle_threshold_ge_one
