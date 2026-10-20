module
public import DiscreteEnergyReproduction
public import DensityEnergyGM.LargeValuesS3

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset
namespace Montgomery.RationalMoment

/-- Ordered pairs of source ordinates. -/
noncomputable def differenceOrdinatePairs (W : Finset ℝ) : Finset (ℝ × ℝ) :=
  W ×ˢ W

/-- The unit-bin label of an ordered difference. -/
noncomputable def differenceFloor (p : ℝ × ℝ) : ℤ :=
  ⌊p.1 - p.2⌋

/-- The finite support of the difference floor multiplicity function. -/
noncomputable def differenceFloorSupport (W : Finset ℝ) : Finset ℤ :=
  (differenceOrdinatePairs W).image differenceFloor

/-- Number of ordered pairs whose difference lies in one unit floor bin. -/
noncomputable def differenceFloorCount (W : Finset ℝ) (j : ℤ) : ℕ :=
  ((differenceOrdinatePairs W).filter fun p => differenceFloor p = j).card

/-- Pair-pairs lying in the same unit floor bin. -/
noncomputable def floorMatchedDifferences (W : Finset ℝ) :
    Finset ((ℝ × ℝ) × (ℝ × ℝ)) :=
  ((differenceOrdinatePairs W) ×ˢ (differenceOrdinatePairs W)).filter fun q =>
    differenceFloor q.1 = differenceFloor q.2

/-- The exact floor-bin square sum is the cardinality of the matched
pair-pair set. -/
theorem sum_differenceFloorCount_sq (W : Finset ℝ) :
    ∑ j ∈ differenceFloorSupport W, differenceFloorCount W j ^ 2 =
      (floorMatchedDifferences W).card := by
  classical
  unfold differenceFloorSupport differenceFloorCount floorMatchedDifferences
  simp_rw [pow_two, ← Finset.card_product]
  rw [← Finset.card_biUnion]
  · congr 1
    ext q
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_product,
      Finset.mem_filter]
    constructor
    · rintro ⟨j, ⟨p, hp, rfl⟩, hq⟩
      exact ⟨⟨hq.1.1, hq.2.1⟩, hq.1.2.trans hq.2.2.symm⟩
    · intro hq
      refine ⟨differenceFloor q.1, ⟨q.1, hq.1.1, rfl⟩, ?_⟩
      exact ⟨⟨hq.1.1, rfl⟩, ⟨hq.1.2, hq.2.symm⟩⟩
  · intro i hi j hj hij
    change Disjoint
      (((differenceOrdinatePairs W).filter fun p => differenceFloor p = i) ×ˢ
        ((differenceOrdinatePairs W).filter fun p => differenceFloor p = i))
      (((differenceOrdinatePairs W).filter fun p => differenceFloor p = j) ×ˢ
        ((differenceOrdinatePairs W).filter fun p => differenceFloor p = j))
    rw [Finset.disjoint_left]
    intro q hqi hqj
    have hiq := Finset.mem_filter.mp (Finset.mem_product.mp hqi).1 |>.2
    have hjq := Finset.mem_filter.mp (Finset.mem_product.mp hqj).1 |>.2
    exact hij (hiq.symm.trans hjq)


/-- Equal difference floors force the corresponding additive defect below
one, with the two second coordinates exchanged. -/
theorem abs_difference_defect_lt_one_of_floor_eq {p q : ℝ × ℝ}
    (h : differenceFloor p = differenceFloor q) :
    |p.1 + q.2 - q.1 - p.2| < 1 := by
  unfold differenceFloor at h
  have hpLower := Int.floor_le (p.1 - p.2)
  have hpUpper := Int.lt_floor_add_one (p.1 - p.2)
  have hqLower := Int.floor_le (q.1 - q.2)
  have hqUpper := Int.lt_floor_add_one (q.1 - q.2)
  rw [h] at hpLower hpUpper
  rw [abs_lt]
  constructor <;> linarith

/-- The literal unit-difference occupancies have square sum bounded by the
same tolerance-one ordered additive energy used in the zero-density proof. -/
theorem differenceFloor_energy_le (W : Finset ℝ) :
    ∑ j ∈ differenceFloorSupport W, differenceFloorCount W j ^ 2 ≤
      discreteAdditiveEnergy W := by
  rw [sum_differenceFloorCount_sq]
  let swap : ((ℝ × ℝ) × (ℝ × ℝ)) → ((ℝ × ℝ) × (ℝ × ℝ)) :=
    fun q => ((q.1.1, q.2.2), (q.2.1, q.1.2))
  have hmaps : Set.MapsTo swap (floorMatchedDifferences W)
      (((W ×ˢ W) ×ˢ (W ×ˢ W)).filter
        (fun p => |p.1.1 + p.1.2 - p.2.1 - p.2.2| ≤ 1)) := by
    intro q hq
    have hmem := Finset.mem_filter.mp hq
    have hpairs := Finset.mem_product.mp hmem.1
    have hp := Finset.mem_product.mp hpairs.1
    have hq' := Finset.mem_product.mp hpairs.2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨hp.1, hq'.2⟩,
        Finset.mem_product.mpr ⟨hq'.1, hp.2⟩⟩,
      (abs_difference_defect_lt_one_of_floor_eq hmem.2).le⟩
  have hinj : Set.InjOn swap (floorMatchedDifferences W) := by
    intro q hq p hp heq
    have h := congrArg swap heq
    exact h
  exact Finset.card_le_card_of_injOn swap hmaps hinj

/-- Mass of any finite family of occupied difference cells. The count of
cells and the original energy enter through ordinary finite Cauchy--Schwarz. -/
theorem differenceFloor_subset_mass_sq (W : Finset ℝ) (J : Finset ℤ)
    (hJ : J ⊆ differenceFloorSupport W) :
    (∑ j ∈ J, (differenceFloorCount W j : ℝ)) ^ 2 ≤
      (J.card : ℝ) * (discreteAdditiveEnergy W : ℝ) := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq J
    (fun j => (differenceFloorCount W j : ℝ)) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hCS
  have hEnergy : (∑ j ∈ J, (differenceFloorCount W j : ℝ) ^ 2) ≤
      (discreteAdditiveEnergy W : ℝ) := by
    have hsub := Finset.sum_le_sum_of_subset_of_nonneg hJ
      (fun j hj hnot => Nat.zero_le (differenceFloorCount W j ^ 2))
    have hNat := hsub.trans (differenceFloor_energy_le W)
    exact_mod_cast hNat
  have hcard : 0 ≤ (J.card : ℝ) := Nat.cast_nonneg _
  have h := mul_le_mul_of_nonneg_left hEnergy hcard
  exact hCS.trans (by nlinarith)

/-- Unit difference cells retain exactly all ordered pairs. -/
theorem sum_differenceFloorCount (W : Finset ℝ) :
    ∑ j ∈ differenceFloorSupport W, differenceFloorCount W j = W.card ^ 2 := by
  have hmaps : ∀ p ∈ differenceOrdinatePairs W,
      differenceFloor p ∈ differenceFloorSupport W := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have h := Finset.card_eq_sum_card_fiberwise hmaps
  change (differenceOrdinatePairs W).card =
    ∑ j ∈ differenceFloorSupport W, differenceFloorCount W j at h
  rw [← h]
  simp only [differenceOrdinatePairs, Finset.card_product, pow_two]

end Montgomery.RationalMoment
