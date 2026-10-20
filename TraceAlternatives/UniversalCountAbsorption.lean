module
public import DensityEnergyGM.SharpCountAlgebra

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

theorem eighth_gap_count_absorption {R S C : ℝ}
    (hS : 0 < S) (hSR : S ≤ R)
    (hbound : R^2 ≤ C*S^(1/8:ℝ)*R^(15/8:ℝ)) : R ≤ C^8*S := by
  have hR : 0 < R := hS.trans_le hSR
  have he : R^2=R^(1/8:ℝ)*R^(15/8:ℝ) := by
    rw [← Real.rpow_add hR]
    norm_num
  rw [he] at hbound
  have hh : R^(1/8:ℝ) ≤ C*S^(1/8:ℝ) :=
    (mul_le_mul_iff_left₀ (by positivity : 0 < R^(15/8:ℝ))).mp (by
      simpa only [mul_comm,mul_left_comm] using hbound)
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ R^(1/8:ℝ)) hh 8
  have hleft : (R^(1/8:ℝ))^8=R := by
    rw [← Real.rpow_mul_natCast hR.le]
    norm_num
  have hright : (S^(1/8:ℝ))^8=S := by
    rw [← Real.rpow_mul_natCast hS.le]
    norm_num
  simpa only [hleft,mul_pow,hright] using hp

end Montgomery.RationalMoment
