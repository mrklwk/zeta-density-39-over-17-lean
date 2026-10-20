module
public import DensityEnergyGM.SharpQuadraticLargeValues
public import DensityEnergyGM.EnergyPowerMean

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment

theorem finite_sum_rpow_le_sum_rpow {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i) {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    (∑ i ∈ S, f i)^q ≤ ∑ i ∈ S, (f i)^q := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [sum_empty,Real.zero_rpow hq.ne',le_refl]
  | @insert i S hi ih =>
      rw [sum_insert hi,sum_insert hi]
      exact (Real.rpow_add_le_add_rpow (hf i (mem_insert_self _ _))
        (sum_nonneg (fun j hj => hf j (mem_insert_of_mem hj))) hq.le hq1).trans
        (add_le_add le_rfl (ih (fun j hj => hf j (mem_insert_of_mem hj))))

/-- Normalize every sublinear monomial to one common positive count gap. -/
theorem sublinear_monomial_domination {S R r c : ℝ}
    (hS : 0 < S) (hSR : S ≤ R) (hr : r ≤ 2-c) :
    S^(2-r)*R^r ≤ S^c*R^(2-c) := by
  have hR : 0 < R := hS.trans_le hSR
  have he : S^(2-r)=S^c*S^(2-c-r) := by
    rw [← Real.rpow_add hS]
    congr 1
    ring
  rw [he]
  calc
    _ = S^c*(S^(2-c-r)*R^r) := by ring
    _ ≤ S^c*(R^(2-c-r)*R^r) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hS.le hSR (by linarith)) (by positivity)
    _ = _ := by rw [← Real.rpow_add hR]; congr 2; ring

/-- Exact fourth-power count absorption for the common gap1/4. -/
theorem quarter_gap_count_absorption {R S C : ℝ}
    (hS : 0 < S) (hSR : S ≤ R)
    (hbound : R^2 ≤ C*S^(1/4:ℝ)*R^(7/4:ℝ)) : R ≤ C^4*S := by
  have hR : 0 < R := hS.trans_le hSR
  have he : R^2=R^(1/4:ℝ)*R^(7/4:ℝ) := by
    rw [← Real.rpow_add hR]
    norm_num
  rw [he] at hbound
  have hh : R^(1/4:ℝ) ≤ C*S^(1/4:ℝ) :=
    (mul_le_mul_iff_left₀ (by positivity : 0 < R^(7/4:ℝ))).mp (by
      simpa only [mul_comm,mul_left_comm] using hbound)
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ R^(1/4:ℝ)) hh 4
  have hleft : (R^(1/4:ℝ))^4=R := by
    rw [← Real.rpow_mul_natCast hR.le]
    norm_num
  have hright : (S^(1/4:ℝ))^4=S := by
    rw [← Real.rpow_mul_natCast hS.le]
    norm_num
  simpa only [hleft,mul_pow,hright] using hp

end Montgomery.RationalMoment
