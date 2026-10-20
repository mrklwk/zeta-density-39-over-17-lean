module
public import GuthMaynard.Improvement.LogPoissonTail

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff FourierTransform
namespace GuthMaynard.Improvement

theorem choose_log_poisson_order {η : ℝ} (hη : 0 < η) :
    ∃ j : ℕ, ∀ T : ℝ, 1 ≤ T →
      T^2*T^(j+2)/(T^(1+η))^j ≤ T^(-200:ℝ) := by
  let j := ⌈204/η⌉₊
  have hj : (204:ℝ) ≤ (j:ℝ)*η := (div_le_iff₀ hη).mp (Nat.le_ceil _)
  refine ⟨j,?_⟩
  intro T hT
  have hTp : 0 < T := by linarith
  rw [← Real.rpow_natCast (T^(1+η)) j,← Real.rpow_mul hTp.le,
    ← Real.rpow_natCast T 2,← Real.rpow_natCast T (j+2),
    ← Real.rpow_add hTp,← Real.rpow_sub hTp]
  apply Real.rpow_le_rpow_of_exponent_le hT
  push_cast
  nlinarith

/-- The actual log-modulated Poisson tail, including the outer L.
The decay order and constant precede time, length, and shift. -/
theorem log_poisson_negligible {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hs : ∀ x, x ∉ Icc l u → a x = 0)
    {η c : ℝ} (hη : 0 < η) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T L s α : ℝ,
      1 ≤ T → 1 ≤ L → L ≤ T^2 → |s| ≤ c*T →
      Summable (fun m : ℤ => ‖poissonRemainder (logModulated a s) L α (T^(1+η)) m‖) ∧
      ‖(L:ℂ)*(∑' m : ℤ, poissonRemainder (logModulated a s) L α (T^(1+η)) m)‖ ≤
        C*T^(-200:ℝ) := by
  obtain ⟨j,hj⟩ := choose_log_poisson_order hη
  obtain ⟨C,hC,h⟩ := logModulated_poisson_tail ha hl hlu hs j
  refine ⟨4*C*(1+c)^(j+2),by positivity,?_⟩
  intro T L s α hT hL hLT hst
  have hTp : 0 < T := by linarith
  have hLp : 0 < L := by linarith
  have hHp : 0 < T^(1+η) := Real.rpow_pos_of_pos hTp _
  obtain ⟨hi,hb⟩ := h s L α (T^(1+η)) hLp hHp.le
  refine ⟨hi,?_⟩
  have htime : 1+|s| ≤ (1+c)*T := by nlinarith
  have hspace : (1+L⁻¹)^2 ≤ 4 := by
    have hh : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL
    have hh0 : 0 ≤ L⁻¹ := inv_nonneg.mpr hLp.le
    nlinarith
  calc
    _ = L*‖∑' m : ℤ, poissonRemainder (logModulated a s) L α (T^(1+η)) m‖ := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hLp]
    _ ≤ L*(C*(1+|s|)^(j+2)*(1+L⁻¹)^2/(1+T^(1+η))^j) := by gcongr
    _ ≤ T^2*(C*((1+c)*T)^(j+2)*4/(T^(1+η))^j) := by gcongr; linarith
    _ = (4*C*(1+c)^(j+2))*(T^2*T^(j+2)/(T^(1+η))^j) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hj T hT) (by positivity)

/-- Scalar budget for the already-proved local cubic perturbation bound.
This retains two kernel-size factors and the full compact-support L2 cost;
it does not assert a kernel identification or a kernel bound. -/
theorem poisson_cubic_error_budget {T L C D d M : ℝ}
    (hT : 1 ≤ T) (hL : 0 ≤ L) (hLT : L ≤ T^2)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hd : d ≤ T) :
    3*(C*T^(-200:ℝ))*(D*L)^2*Real.sqrt d^3*Real.sqrt M^3 ≤
      (3*C*D^2)*T^(-100:ℝ)*Real.sqrt M^3 := by
  have hTp : 0 < T := by linarith
  have hsqrt : Real.sqrt d ≤ T := (Real.sqrt_le_iff).mpr ⟨hTp.le,by nlinarith⟩
  have he : T^(-200:ℝ)*(T^2)^2*T^3 = T^(-193:ℝ) := by
    rw [← pow_mul,← Real.rpow_natCast T (2*2),← Real.rpow_add hTp,
      ← Real.rpow_natCast T 3,← Real.rpow_add hTp]
    norm_num
  calc
    _ ≤ 3*(C*T^(-200:ℝ))*(D*T^2)^2*T^3*Real.sqrt M^3 := by gcongr
    _ = (3*C*D^2)*T^(-193:ℝ)*Real.sqrt M^3 := by rw [← he]; ring
    _ ≤ _ := by
      have hp : T^(-193:ℝ) ≤ T^(-100:ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
      gcongr

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.choose_log_poisson_order
#print axioms GuthMaynard.Improvement.log_poisson_negligible

#print axioms GuthMaynard.Improvement.poisson_cubic_error_budget
