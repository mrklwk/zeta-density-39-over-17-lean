import GuthMaynard.Improvement.ReflectionKernelBridge
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

theorem centeredKernel_norm_neg (w : MathCollab.Density.ReflectionCutoff)
    {L : ℝ} (hL : 0 < L) (v : ℝ) :
    ‖centeredKernel (fun x => (w x:ℂ)) (1/2) 5 L (-v)‖ =
      ‖centeredKernel (fun x => (w x:ℂ)) (1/2) 5 L v‖ := by
  simp only [centeredKernel_eq_density_hKernel w hL,
    MathCollab.Density.norm_hKernel_neg]

theorem reflectionBand_empty_near {L H : ℝ} (hL : 0 < L)
    (hH : H ≤ Real.pi*L/8) : MathCollab.Density.reflectionBand L H = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro m hm
  have hh := (MathCollab.Density.mem_reflectionBand L H m).mp hm
  have hmpos := hh.1
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast (show (1:ℤ) ≤ m by omega)
  have hu := (le_div_iff₀ (mul_pos Real.pi_pos hL)).mp hh.2.2
  have hlo := mul_le_mul_of_nonneg_right hm1 (mul_pos Real.pi_pos hL).le
  nlinarith [mul_pos Real.pi_pos hL]

/-- The exact centered kernel has a rapidly decreasing error in the whole
near region, including the diagonal; the constant precedes every scale. -/
theorem centeredKernel_near (w : MathCollab.Density.ReflectionCutoff)
    {A : ℕ} (hA : 1 < A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L v : ℝ, 0 < L → |v| ≤ Real.pi*L/8 →
      ‖centeredKernel (fun x => (w x:ℂ)) (1/2) 5 L v‖ ≤ K*L/L^A := by
  obtain ⟨K,hK,h⟩ := MathCollab.Density.uniform_fixedBand_and_diagonal_error w hA
  refine ⟨K,hK,?_⟩
  intro L v hL hv
  rw [centeredKernel_eq_density_hKernel w hL]
  have hp (s : ℝ) (hs : 0 < s) (hsL : s ≤ Real.pi*L/8) :
      ‖MathCollab.Density.hKernel w L s‖ ≤ K*L/L^A := by
    have he := (h L s s hL hs le_rfl (by linarith)).1
    have hz : MathCollab.Density.bandContribution w L s s = 0 := by
      rw [MathCollab.Density.bandContribution,
        MathCollab.Density.tsum_retainedMode_eq_finite,
        reflectionBand_empty_near hL hsL]
      simp
    simpa only [hz,sub_zero] using he
  rcases lt_trichotomy v 0 with hn | hz | hpv
  · have he := hp (-v) (by linarith) (by simpa only [abs_of_neg hn] using hv)
    rwa [MathCollab.Density.norm_hKernel_neg] at he
  · subst v
    exact (h L 1 1 hL (by norm_num) le_rfl (by norm_num)).2
  · exact hp v hpv (by simpa only [abs_of_pos hpv] using hv)

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.centeredKernel_norm_neg
#print axioms GuthMaynard.Improvement.reflectionBand_empty_near
#print axioms GuthMaynard.Improvement.centeredKernel_near
