module
public import DensityEnergyGM.DifferencePeaks
public import DensityEnergyGM.SquaredLevelCount

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

/-- The level count for actual maximizing difference-cell representatives.
The representatives are fixed before the varying level U. Three residue
classes provide genuinely separated ordinates for the native theorem. -/
theorem difference_cell_level_count_native (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (M : ℕ) (T : ℝ) (a : ℕ → ℂ) (W : Finset ℝ),
        0 < M → T₀ ≤ T → (M : ℝ) ^ 2 ≤ T →
        (∀ n ∈ Ioc M (2 * M), ‖a n‖ ≤ 1) → InBaseInterval T W →
        ∃ p : ℤ → ℝ × ℝ,
          (∀ j ∈ differenceFloorSupport W,
            p j ∈ differenceOrdinatePairs W ∧ differenceFloor (p j) = j ∧
              ∀ q ∈ differenceOrdinatePairs W, differenceFloor q = j →
                ‖dirichletPoly M a (q.1 - q.2)‖ ≤
                  ‖dirichletPoly M a ((p j).1 - (p j).2)‖) ∧
          ∀ U : ℝ, 0 < U →
            (((differenceFloorSupport W).filter fun j =>
                U ≤ ‖dirichletPoly M a ((p j).1 - (p j).2)‖).card : ℝ) ≤
              C * (2 * T) ^ ε *
                ((M : ℝ) ^ 4 * U ^ (-4 : ℝ) +
                  (M : ℝ) ^ (36 / 5 : ℝ) * U ^ (-8 : ℝ) +
                  (2 * T) * (M : ℝ) ^ (24 / 5 : ℝ) * U ^ (-8 : ℝ)) := by
  classical
  obtain ⟨C₀, T₀, hC₀, hT₀, hJ⟩ := squared_polynomial_level_count_native ε hε
  refine ⟨3 * C₀, T₀, by positivity, hT₀, ?_⟩
  intro M T a W hM hT hMT ha hBase
  have hTone : 1 ≤ T := hT₀.trans hT
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hTone
  obtain ⟨p, hrep⟩ := exists_difference_peak_representatives W
    (fun t => ‖dirichletPoly M a t‖)
  refine ⟨p, hrep, ?_⟩
  intro U hU
  let S := (differenceFloorSupport W).filter fun j =>
    U ≤ ‖dirichletPoly M a ((p j).1 - (p j).2)‖
  let color : ℤ → ℕ := fun j => (j % 3).toNat
  let y : ℤ → ℝ := fun j => (p j).1 - (p j).2 + T
  have hsupport : ∀ j ∈ S, j ∈ differenceFloorSupport W :=
    fun j hj => (Finset.mem_filter.mp hj).1
  have hcolor : ∀ j ∈ S, color j ∈ Finset.range 3 := by
    intro j hj
    have hnonneg := Int.emod_nonneg j (by norm_num : (3 : ℤ) ≠ 0)
    have hlt := Int.emod_lt_of_pos j (by norm_num : (0 : ℤ) < 3)
    rw [Finset.mem_range]
    change (j % 3).toNat < 3
    omega
  have hcounts : S.card = ∑ r ∈ Finset.range 3,
      ((S.filter fun j => color j = r).card) :=
    Finset.card_eq_sum_card_fiberwise hcolor
  have hEach : ∀ r ∈ Finset.range 3,
      (((S.filter fun j => color j = r).card) : ℝ) ≤
        C₀ * (2 * T) ^ ε *
          ((M : ℝ) ^ 4 * U ^ (-4 : ℝ) +
            (M : ℝ) ^ (36 / 5 : ℝ) * U ^ (-8 : ℝ) +
            (2 * T) * (M : ℝ) ^ (24 / 5 : ℝ) * U ^ (-8 : ℝ)) := by
    intro r hr
    let A := S.filter fun j => color j = r
    let Y := A.image y
    have hA : ∀ j ∈ A, j ∈ S := fun j hj => (Finset.mem_filter.mp hj).1
    have hfloor : ∀ j ∈ A, ⌊y j - T⌋ = j := by
      intro j hj
      have h := (hrep j (hsupport j (hA j hj))).2.1
      simpa only [y, add_sub_cancel_right, differenceFloor] using h
    have hyinj : Set.InjOn y A := by
      intro i hi j hj heq
      have h := congrArg (fun x : ℝ => ⌊x - T⌋) heq
      rwa [hfloor i hi, hfloor j hj] at h
    have hcardY : Y.card = A.card := Finset.card_image_of_injOn hyinj
    have hSepY : IsSeparated 1 Y := by
      intro x hx z hz hne
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
      have hneij : i ≠ j := by intro h; subst j; exact hne rfl
      have hci := (Finset.mem_filter.mp hi).2
      have hcj := (Finset.mem_filter.mp hj).2
      have hmod : i % 3 = j % 3 := by
        have hinonneg := Int.emod_nonneg i (by norm_num : (3 : ℤ) ≠ 0)
        have hjnonneg := Int.emod_nonneg j (by norm_num : (3 : ℤ) ≠ 0)
        dsimp only [color] at hci hcj
        omega
      have h := difference_floor_residue_separated (hfloor i hi) (hfloor j hj) hmod hneij
      simpa only [Real.dist_eq, sub_sub_sub_cancel_right] using h
    have hBaseY : InBaseInterval (2 * T) Y := by
      intro z hz
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
      have hp := (hrep j (hsupport j (hA j hj))).1
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      have ht := hBase (p j).1 hp1
      have hu := hBase (p j).2 hp2
      dsimp only [y]
      exact ⟨by linarith [ht.1, hu.2], by linarith [ht.2, hu.1]⟩
    have hLargeY : ∀ z ∈ Y,
        U ≤ ‖dirichletPoly M (phaseShiftCoeffs (-T) a) z‖ := by
      intro z hz
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
      have h := (Finset.mem_filter.mp (hA j hj)).2
      dsimp only [y]
      rw [← dirichletPoly_difference_eq_translated]
      exact h
    have hcount := hJ M (2 * T) U (phaseShiftCoeffs (-T) a) Y hM
      (by linarith) (by linarith) hU
      (by intro n hn; rw [norm_phaseShiftCoeffs]; exact ha n hn)
      hSepY hBaseY hLargeY
    rw [hcardY] at hcount
    exact hcount
  calc
    (S.card : ℝ) = ∑ r ∈ Finset.range 3,
        (((S.filter fun j => color j = r).card) : ℝ) := by exact_mod_cast hcounts
    _ ≤ ∑ _r ∈ Finset.range 3, C₀ * (2 * T) ^ ε *
        ((M : ℝ) ^ 4 * U ^ (-4 : ℝ) +
          (M : ℝ) ^ (36 / 5 : ℝ) * U ^ (-8 : ℝ) +
          (2 * T) * (M : ℝ) ^ (24 / 5 : ℝ) * U ^ (-8 : ℝ)) :=
      Finset.sum_le_sum hEach
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- The weighted weak level estimate used in the sharper second moment.
Every weight is the literal number of original pairs in a unit difference
cell; the same representatives work for every positive threshold. -/
theorem difference_cell_weighted_level_native (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (M : ℕ) (T : ℝ) (a : ℕ → ℂ) (W : Finset ℝ),
        0 < M → T₀ ≤ T → (M : ℝ) ^ 2 ≤ T →
        (∀ n ∈ Ioc M (2 * M), ‖a n‖ ≤ 1) → InBaseInterval T W →
        ∃ p : ℤ → ℝ × ℝ,
          (∀ j ∈ differenceFloorSupport W,
            p j ∈ differenceOrdinatePairs W ∧ differenceFloor (p j) = j ∧
              ∀ q ∈ differenceOrdinatePairs W, differenceFloor q = j →
                ‖dirichletPoly M a (q.1 - q.2)‖ ≤
                  ‖dirichletPoly M a ((p j).1 - (p j).2)‖) ∧
          ∀ U : ℝ, 0 < U →
            (∑ j ∈ (differenceFloorSupport W).filter (fun j =>
                U ≤ ‖dirichletPoly M a ((p j).1 - (p j).2)‖),
                (differenceFloorCount W j : ℝ)) ≤
              min ((W.card : ℝ) ^ 2)
                (Real.sqrt ((discreteAdditiveEnergy W : ℝ) *
                  (C * (2 * T) ^ ε *
                    ((M : ℝ) ^ 4 * U ^ (-4 : ℝ) +
                      (M : ℝ) ^ (36 / 5 : ℝ) * U ^ (-8 : ℝ) +
                      (2 * T) * (M : ℝ) ^ (24 / 5 : ℝ) * U ^ (-8 : ℝ))))) := by
  obtain ⟨C, T₀, hC, hT₀, hLevels⟩ := difference_cell_level_count_native ε hε
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro M T a W hM hT hMT ha hBase
  obtain ⟨p, hrep, hcounts⟩ := hLevels M T a W hM hT hMT ha hBase
  refine ⟨p, hrep, ?_⟩
  intro U hU
  let J := (differenceFloorSupport W).filter fun j =>
    U ≤ ‖dirichletPoly M a ((p j).1 - (p j).2)‖
  let B : ℝ := C * (2 * T) ^ ε *
    ((M : ℝ) ^ 4 * U ^ (-4 : ℝ) +
      (M : ℝ) ^ (36 / 5 : ℝ) * U ^ (-8 : ℝ) +
      (2 * T) * (M : ℝ) ^ (24 / 5 : ℝ) * U ^ (-8 : ℝ))
  let mass : ℝ := ∑ j ∈ J, (differenceFloorCount W j : ℝ)
  have hsub : J ⊆ differenceFloorSupport W := Finset.filter_subset _ _
  have hmass0 : 0 ≤ mass := Finset.sum_nonneg fun j hj => Nat.cast_nonneg _
  have hE0 : 0 ≤ (discreteAdditiveEnergy W : ℝ) := Nat.cast_nonneg _
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one (hT₀.trans hT)
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hcard : (J.card : ℝ) ≤ B := hcounts U hU
  have hmassSq : mass ^ 2 ≤ (discreteAdditiveEnergy W : ℝ) * B := by
    have h := differenceFloor_subset_mass_sq W J hsub
    have hc := mul_le_mul_of_nonneg_right hcard hE0
    dsimp only [mass]
    nlinarith
  have hRoot : mass ≤ Real.sqrt ((discreteAdditiveEnergy W : ℝ) * B) := by
    have hs := Real.sq_sqrt (mul_nonneg hE0 hB0)
    have hsn := Real.sqrt_nonneg ((discreteAdditiveEnergy W : ℝ) * B)
    nlinarith
  have htotal : (∑ j ∈ differenceFloorSupport W,
      (differenceFloorCount W j : ℝ)) = (W.card : ℝ) ^ 2 := by
    exact_mod_cast sum_differenceFloorCount W
  have hTrivial : mass ≤ (W.card : ℝ) ^ 2 := by
    rw [← htotal]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun j hj hnot => Nat.cast_nonneg _)
  exact le_min hTrivial hRoot

end Montgomery.RationalMoment
