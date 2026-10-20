module
public import DensityEnergyGM.DifferenceFloorEnergy

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

theorem card_differenceFloorSupport_le_height {T : ℝ} {W : Finset ℝ}
    (hT : 2 ≤ T) (hBase : InBaseInterval T W) :
    ((differenceFloorSupport W).card : ℝ) ≤ 4 * T := by
  let K : ℕ := ⌈T⌉₊
  have hKT : T ≤ (K : ℝ) := Nat.le_ceil T
  have hKupper : (K : ℝ) < T + 1 := Nat.ceil_lt_add_one (by linarith)
  have hSub : differenceFloorSupport W ⊆ Icc (-(K : ℤ)) (K : ℤ) := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨ht0, htT⟩ := hBase p.1 hp1
    obtain ⟨hu0, huT⟩ := hBase p.2 hp2
    rw [Finset.mem_Icc]
    constructor
    · apply Int.le_floor.mpr
      push_cast
      linarith
    · have hfloor := Int.floor_le (p.1 - p.2)
      have hbound : (⌊p.1 - p.2⌋ : ℝ) ≤ (K : ℝ) := by linarith
      exact_mod_cast hbound
  have hCard : (Icc (-(K : ℤ)) (K : ℤ)).card = 2 * K + 1 := by
    rw [Int.card_Icc]
    omega
  have h := Finset.card_le_card hSub
  rw [hCard] at h
  have hc : ((differenceFloorSupport W).card : ℝ) ≤ 2 * (K : ℝ) + 1 := by
    exact_mod_cast h
  linarith

/-- A bounded height interval forces additive energy even without separation.
This supplies the genuine endpoint correction when changing dyadic scales. -/
theorem card_four_le_four_height_energy {T : ℝ} {W : Finset ℝ}
    (hT : 2 ≤ T) (hBase : InBaseInterval T W) :
    (W.card : ℝ) ^ 4 ≤ 4 * T * (discreteAdditiveEnergy W : ℝ) := by
  have h := differenceFloor_subset_mass_sq W (differenceFloorSupport W) (by rfl)
  have hSum : (∑ j ∈ differenceFloorSupport W, (differenceFloorCount W j : ℝ)) =
      (W.card : ℝ) ^ 2 := by exact_mod_cast sum_differenceFloorCount W
  rw [hSum] at h
  have hCard := card_differenceFloorSupport_le_height hT hBase
  have hm := mul_le_mul_of_nonneg_right hCard
    (Nat.cast_nonneg (discreteAdditiveEnergy W) : (0 : ℝ) ≤ discreteAdditiveEnergy W)
  nlinarith

theorem card_sq_le_four_quarter_height_energy {T : ℝ} {W : Finset ℝ}
    (hT : 2 ≤ T) (hBase : InBaseInterval T W) :
    (W.card : ℝ) ^ 2 ≤ 4 * (W.card : ℝ) *
      T ^ (1 / 4 : ℝ) * (discreteAdditiveEnergy W : ℝ) ^ (1 / 4 : ℝ) := by
  have hE := card_four_le_four_height_energy hT hBase
  have hQuarter := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (W.card : ℝ) ^ 4)
    hE (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hId : ((W.card : ℝ) ^ 4) ^ (1 / 4 : ℝ) = (W.card : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg W.card)]
    norm_num
  rw [hId, Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4 * T) (by positivity),
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by linarith)] at hQuarter
  have hFour : (4 : ℝ) ^ (1 / 4 : ℝ) ≤ 4 :=
    Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have hBound : (W.card : ℝ) ≤ 4 * T ^ (1 / 4 : ℝ) *
      (discreteAdditiveEnergy W : ℝ) ^ (1 / 4 : ℝ) := by
    exact hQuarter.trans (by gcongr)
  have h := mul_le_mul_of_nonneg_left hBound (Nat.cast_nonneg W.card : (0 : ℝ) ≤ W.card)
  nlinarith

end Montgomery.RationalMoment
