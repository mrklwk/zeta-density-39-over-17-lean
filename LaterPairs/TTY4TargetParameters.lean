module
public import DashedInitialParameters

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

/-- Exact original TTY4 target tail budgets on its full requested interval. -/
theorem tty4_full_target_tail_budgets {σ : ℝ}
    (hl : 163/198 ≤ σ) (_hr : σ ≤ 7873/9370) :
    let a : ℝ := 31544/(107010*σ-33609)
    1/8 < (3*a/4)*(σ-1/2) ∧
    1-6*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ) ∧
    1+(914/1739:ℝ)/(3316/8695)-(4+(2+4*(914/1739))/(3316/8695))*((3*a/4)*(σ-1/2)) ≤
      3*a*(1-σ) := by
  dsimp only
  have hd : 0 < 107010*σ-33609 := by linarith
  refine ⟨fraction_detector_threshold hd (by linarith),?_⟩
  rw [show (1:ℝ)+(914/1739)/(3316/8695)=3943/1658 by norm_num,
    show (4:ℝ)+(2+4*(914/1739))/(3316/8695)=24467/1658 by norm_num]
  apply tail_budgets_of_fraction hd
  · linarith
  · nlinarith

/-- Only this prefix fits the older short-polynomial consumer. The full
requested interval remains the target of the stronger short-piece proof. -/
theorem tty4_old_quadratic_window_prefix {σ : ℝ}
    (hl : 163/198 ≤ σ) (hr : σ ≤ 49381/59694) :
    QuadraticWindow σ (31544/(107010*σ-33609)) := by
  have hd : 0 < 107010*σ-33609 := by linarith
  constructor
  · linarith
  · linarith
  · apply (le_div_iff₀ hd).mpr
    linarith
  · apply (div_lt_iff₀ hd).mpr
    linarith
  · rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hd).mpr
    linarith
  · rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hd).mpr
    linarith
/-- The old fixed log cap fails for the exact required B(TTY4) pair. -/
theorem tty4_native_log_cap_gap :
    (2+4*((914:ℝ)/1739)/((3316:ℝ)/8695)) = 7+425/829 ∧
    (2+4*((914:ℝ)/1739)/((3316:ℝ)/8695)) < 8 := by norm_num

/-- Exact range of the first old quadratic-window condition for the next target.
This is an obstruction to that consumer, not to the proposed density estimate. -/
theorem tty4_native_old_quadratic_first_iff {σ : ℝ} (hσ : (163:ℝ)/198 ≤ σ) :
    2 ≤ (31544/(107010*σ-33609))*(3*σ+1) ↔ σ ≤ 49381/59694 := by
  have hd : 0 < 107010*σ-33609 := by linarith
  rw [div_mul_eq_mul_div]
  constructor
  · intro h
    have hh := (le_div_iff₀ hd).mp h
    linarith
  · intro h
    apply (le_div_iff₀ hd).mpr
    linarith

/-- The requested upper endpoint is outside the old short-piece window. -/
theorem tty4_native_upper_endpoint_old_window_fails :
    (31544/(107010*((7873:ℝ)/9370)-33609)) = 1874/3345 ∧
    ((1874:ℝ)/3345)*(3*((7873:ℝ)/9370)+1)-2 = -461/16725 ∧
    ¬ QuadraticWindow ((7873:ℝ)/9370) ((1874:ℝ)/3345) := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro hw
  have h := hw.first
  norm_num at h
end Montgomery.RationalMoment
