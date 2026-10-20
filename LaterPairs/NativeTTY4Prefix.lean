module
public import LaterPairs.NativeTTY4
public import LaterPairs.TTY4TargetParameters
public import LaterPairs.PairActualDensity

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger MathCollab.Density

theorem tty4_prefix_density_exponent {σ : ℝ} :
    3*(31544/(107010*σ-33609))*(1-σ) =
      31544*(1-σ)/(35670*σ-11203) := by
  have hd : 107010*σ-33609 = 3*(35670*σ-11203) := by ring
  calc
    _ = (3*31544/(3*(35670*σ-11203)))*(1-σ) := by rw [hd]; ring
    _ = (31544/(35670*σ-11203))*(1-σ) := by
      rw [mul_div_mul_left _ _ (by norm_num : (3:ℝ) ≠ 0)]
    _ = _ := div_mul_eq_mul_div _ _ _

/-- The exact intended row3 exponent on the maximal closed prefix supported
by the preserved quadratic short-piece window. The rest of row3 is separate. -/
theorem density_native_tty4_prefix {σ ε : ℝ}
    (hlo : 163/198 ≤ σ) (hhi : σ ≤ 49381/59694) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : ℝ,2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤
        C*T^(31544*(1-σ)/(35670*σ-11203)+ε) := by
  obtain ⟨hthreshold,hfirst,hsecond⟩ := tty4_full_target_tail_budgets hlo
    (show σ ≤ 7873/9370 by linarith)
  simpa only [tty4_prefix_density_exponent] using
    density_of_pair_tail_window_general TaoTrudgianYang2025.exponentPair_BTTY4
      (by norm_num) (tty4_old_quadratic_window_prefix hlo hhi) (by linarith)
      hthreshold hfirst hsecond hε
end Montgomery.RationalMoment.RightDetector
