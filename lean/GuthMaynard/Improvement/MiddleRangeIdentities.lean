import GuthMaynard.Improvement.MiddleRangeScales
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

private theorem middle_logs {N T : ℝ} (hn : 0 < N) (ht : 0 < T) :
    Real.log (middleLength N T) = (1/7:ℝ)*Real.log N+(5/7:ℝ)*Real.log T ∧
    Real.log (middleThreshold N T) = (5/7:ℝ)*Real.log N+(1/14:ℝ)*Real.log T ∧
    Real.log (middleMoment N T) = (18/7:ℝ)*Real.log N+(6/7:ℝ)*Real.log T := by
  unfold middleLength middleThreshold middleMoment
  constructor
  · rw [Real.log_mul (by positivity) (by positivity),Real.log_rpow hn,Real.log_rpow ht]
  constructor
  · rw [Real.log_mul (by positivity) (by positivity),Real.log_rpow hn,Real.log_rpow ht]
  · rw [Real.log_mul (by positivity) (by positivity),Real.log_rpow hn,Real.log_rpow ht]

theorem middle_length_threshold_identity {N T : ℝ} (hn : 0 < N) (ht : 0 < T) :
    N*middleLength N T*(middleThreshold N T)^2 = middleMoment N T := by
  have hl : 0 < middleLength N T := by unfold middleLength; positivity
  have hu : 0 < middleThreshold N T := by unfold middleThreshold; positivity
  have hp : 0 < middleMoment N T := by unfold middleMoment; positivity
  obtain ⟨hll,hlu,hlp⟩ := middle_logs hn ht
  apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity) hp
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul hn.ne' hl.ne',Real.log_pow,hll,hlu,hlp]
  ring

theorem middle_moment_three_halves {N T : ℝ} (hn : 0 < N) (ht : 0 < T) :
    N^4*T^2/middleLength N T = (middleMoment N T)^((3:ℝ)/2) ∧
      (middleMoment N T)^((3:ℝ)/2) = middleMoment N T*Real.sqrt (middleMoment N T) := by
  have hl : 0 < middleLength N T := by unfold middleLength; positivity
  have hp : 0 < middleMoment N T := by unfold middleMoment; positivity
  obtain ⟨hll,_,hlp⟩ := middle_logs hn ht
  constructor
  · apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity) (by simp only [Set.mem_Ioi]; positivity)
    rw [Real.log_div (by positivity) hl.ne',Real.log_mul (by positivity) (by positivity),
      Real.log_pow,Real.log_pow,Real.log_rpow hp,hll,hlp]
    ring
  · apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity) (by simp only [Set.mem_Ioi]; positivity)
    rw [Real.log_rpow hp,Real.log_mul hp.ne' (by positivity),Real.log_sqrt hp.le]
    ring

theorem middle_length_moment_square {N T : ℝ} (hn : 0 < N) (ht : 0 < T) :
    N^5*middleLength N T*T = (middleMoment N T)^2 := by
  have hl : 0 < middleLength N T := by unfold middleLength; positivity
  have hp : 0 < middleMoment N T := by unfold middleMoment; positivity
  obtain ⟨hll,_,hlp⟩ := middle_logs hn ht
  apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity) (by simp only [Set.mem_Ioi]; positivity)
  rw [Real.log_mul (by positivity) ht.ne',Real.log_mul (by positivity) hl.ne',
    Real.log_pow,Real.log_pow,hll,hlp]
  ring

theorem middle_threshold_square_quotient {N T : ℝ} (hn : 0 < N) (ht : 0 < T) :
    T*N^4/(middleThreshold N T)^2 = middleMoment N T := by
  have hu : 0 < middleThreshold N T := by unfold middleThreshold; positivity
  have hp : 0 < middleMoment N T := by unfold middleMoment; positivity
  obtain ⟨_,hlu,hlp⟩ := middle_logs hn ht
  apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity) hp
  rw [Real.log_div (by positivity) (by positivity),Real.log_mul ht.ne' (by positivity),
    Real.log_pow,Real.log_pow,hlu,hlp]
  ring

theorem middle_threshold_fourth_quotient {N T : ℝ} (hn : 0 < N) (ht : 0 < T) :
    T*N^4/(middleThreshold N T)^4 = N*middleLength N T := by
  have hl : 0 < middleLength N T := by unfold middleLength; positivity
  have hu : 0 < middleThreshold N T := by unfold middleThreshold; positivity
  obtain ⟨hll,hlu,_⟩ := middle_logs hn ht
  apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity) (by simp only [Set.mem_Ioi]; positivity)
  rw [Real.log_div (by positivity) (by positivity),Real.log_mul ht.ne' (by positivity),
    Real.log_mul hn.ne' hl.ne',Real.log_pow,Real.log_pow,hlu,hll]
  ring

theorem middle_cubic_budget {N T : ℝ} (hn : 0 < N) (ht : 0 < T)
    (hhi : T ≤ N^((5:ℝ)/3)) : N^7*T^3 ≤ (middleMoment N T)^3 := by
  have hp : 0 < middleMoment N T := by unfold middleMoment; positivity
  have hh := Real.log_le_log ht hhi
  rw [Real.log_rpow hn] at hh
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  rw [Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow,
    Real.log_pow,(middle_logs hn ht).2.2]
  linarith

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.middle_length_threshold_identity
#print axioms GuthMaynard.Improvement.middle_moment_three_halves
#print axioms GuthMaynard.Improvement.middle_length_moment_square
#print axioms GuthMaynard.Improvement.middle_threshold_square_quotient
#print axioms GuthMaynard.Improvement.middle_threshold_fourth_quotient
#print axioms GuthMaynard.Improvement.middle_cubic_budget
