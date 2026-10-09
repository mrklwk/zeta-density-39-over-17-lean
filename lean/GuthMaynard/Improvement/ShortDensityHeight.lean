module
public import GuthMaynard.Improvement.ShortDensityScale

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

theorem short_density_height_eq {H N : ℝ} (hH : 0 < H) (hN : 0 < N)
    (σ δ : ℝ) :
    N^σ*H^(-2*δ) = N^σ/(H^δ)^2 ∧ 0 < N^σ*H^(-2*δ) := by
  constructor
  · rw [show -2*δ = -(δ*2) by ring, Real.rpow_neg hH.le,
      Real.rpow_mul hH.le δ 2, Real.rpow_ofNat]
    rfl
  · positivity

/-- Exact denominator algebra for the normalized powered detector height. -/
theorem short_density_height_budgets {H N : ℝ} (hH : 0 < H) (hN : 0 < N)
    (σ δ : ℝ) :
    N^2/(N^σ*H^(-2*δ))^2 = N^(2-2*σ)*H^(4*δ) ∧
    N^(18/7:ℝ)*H^(6/7:ℝ)/(N^σ*H^(-2*δ))^4 =
      (N^(18/7-4*σ)*H^(6/7:ℝ))*H^(8*δ) ∧
    N*(H+N*Real.log (2*N))/(N^σ*H^(-2*δ))^2 =
      (H*N^(1-2*σ)+N^(2-2*σ)*Real.log (2*N))*H^(4*δ) := by
  have hV := (short_density_height_eq hH hN σ δ).1
  have hnσ : N^σ ≠ 0 := (Real.rpow_pos_of_pos hN _).ne'
  have hhδ : H^δ ≠ 0 := (Real.rpow_pos_of_pos hH _).ne'
  have hn2 : N^(2-2*σ) = N^2/(N^σ)^2 := by
    rw [Real.rpow_sub hN, show 2*σ = σ*2 by ring,
      Real.rpow_mul hN.le σ 2, Real.rpow_ofNat, Real.rpow_ofNat]
  have hn1 : N^(1-2*σ) = N/(N^σ)^2 := by
    rw [Real.rpow_sub hN, show 2*σ = σ*2 by ring,
      Real.rpow_mul hN.le σ 2, Real.rpow_ofNat, Real.rpow_one]
  have hn4 : N^(18/7-4*σ) = N^(18/7:ℝ)/(N^σ)^4 := by
    rw [Real.rpow_sub hN, show 4*σ = σ*4 by ring,
      Real.rpow_mul hN.le σ 4, Real.rpow_ofNat]
  have hh4 : H^(4*δ) = (H^δ)^4 := by
    rw [show 4*δ = δ*4 by ring, Real.rpow_mul hH.le δ 4, Real.rpow_ofNat]
  have hh8 : H^(8*δ) = (H^δ)^8 := by
    rw [show 8*δ = δ*8 by ring, Real.rpow_mul hH.le δ 8, Real.rpow_ofNat]
  rw [hV,hn2,hn1,hn4,hh4,hh8]
  constructor
  · field_simp
  constructor <;> field_simp

/-- Uniform conversion of the length epsilon factor into a height factor. -/
theorem short_density_small_power {σ H N δ : ℝ} (hσ : 9/13 ≤ σ)
    (hσ' : σ ≤ 5/7) (hH : 1 ≤ H) (hN : 0 ≤ N) (hδ : 0 ≤ δ)
    (hδ' : δ ≤ 1/100) (hhi : N ≤ H^(shortDensityB σ+δ)) :
    N^δ ≤ H^(2*δ) := by
  have hH0 : 0 < H := by linarith
  have hb := (short_density_scale_bounds hσ hσ').2.2.2.1
  calc
    _ ≤ (H^(shortDensityB σ+δ))^δ := Real.rpow_le_rpow hN hhi hδ
    _ = H^((shortDensityB σ+δ)*δ) := (Real.rpow_mul hH0.le _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hH
      (mul_le_mul_of_nonneg_right (by linarith : shortDensityB σ+δ ≤ 2) hδ)

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.short_density_height_eq
#print axioms GuthMaynard.Improvement.short_density_height_budgets
#print axioms GuthMaynard.Improvement.short_density_small_power
