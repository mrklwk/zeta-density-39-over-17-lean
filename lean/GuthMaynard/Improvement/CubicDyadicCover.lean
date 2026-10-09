import GuthMaynard.Improvement.CenteredTruncation
import MathCollab.Density.DyadicBlocks
set_option autoImplicit false
noncomputable section
open Set
namespace GuthMaynard.Improvement

def integerDyadicIndex (m : ℤ) : ℕ := m.natAbs.log2

def cubicDyadicClass (m : ℤ × (ℤ × ℤ)) : ℕ × (ℕ × ℕ) :=
  (integerDyadicIndex m.1,integerDyadicIndex m.2.1,integerDyadicIndex m.2.2)

def cubicDyadicClasses (U : ℝ) : Finset (ℕ × (ℕ × ℕ)) :=
  let I := Finset.range (⌊U⌋₊.log2+1)
  I ×ˢ (I ×ˢ I)

theorem integer_dyadic_bounds {m : ℤ} (hm : m ≠ 0) :
    (2:ℝ)^(integerDyadicIndex m) ≤ |(m:ℝ)| ∧
      |(m:ℝ)| < 2*(2:ℝ)^(integerDyadicIndex m) := by
  have hp : 0 < m.natAbs := Int.natAbs_pos.mpr hm
  have hh := MathCollab.Density.log2_block_bounds hp
  have he : (m.natAbs:ℝ) = |(m:ℝ)| := by rw [Nat.cast_natAbs,Int.cast_abs]
  rw [← he]
  constructor
  · exact_mod_cast hh.1
  · exact_mod_cast hh.2

/-- Every actual retained nonzero mode triple is assigned a fixed dyadic
class, independent of integration variables and Fourier masks. -/
theorem cubicDyadicClass_mem {U : ℝ} (hU : 1 ≤ U) {m : ℤ × (ℤ × ℤ)}
    (hm : m.1 ∈ poissonModes U ∧ m.2.1 ∈ poissonModes U ∧ m.2.2 ∈ poissonModes U) :
    cubicDyadicClass m ∈ cubicDyadicClasses U := by
  have hp : 0 < ⌊U⌋₊ := (Nat.one_le_floor_iff U).mpr hU
  have hb : ∀ k ∈ poissonModes U, integerDyadicIndex k < ⌊U⌋₊.log2+1 := by
    intro k hk
    obtain ⟨hk0,hkU⟩ := (mem_poissonModes U k).mp hk
    have hkn : k.natAbs ≤ ⌊U⌋₊ := by
      apply Nat.le_floor
      simpa only [Nat.cast_natAbs,Int.cast_abs] using hkU
    have hpow := (MathCollab.Density.log2_block_bounds (Int.natAbs_pos.mpr hk0)).1
    have hi := (Nat.le_log2 hp.ne').mpr (hpow.trans hkn)
    exact Nat.lt_succ_of_le hi
  simpa only [cubicDyadicClasses,cubicDyadicClass,Finset.mem_product,Finset.mem_range] using
    And.intro (hb _ hm.1) (And.intro (hb _ hm.2.1) (hb _ hm.2.2))

/-- The finite dyadic class list has its exact logarithmic count. -/
theorem cubicDyadicClasses_card {U : ℝ} (hU : 1 ≤ U) :
    ((cubicDyadicClasses U).card:ℝ) ≤ (Real.log (2*U)/Real.log 2)^3 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : 0 < ⌊U⌋₊ := (Nat.one_le_floor_iff U).mpr hU
  have hpow : (2:ℝ)^⌊U⌋₊.log2 ≤ U := by
    have hh : (2:ℝ)^⌊U⌋₊.log2 ≤ (⌊U⌋₊:ℝ) := by exact_mod_cast (MathCollab.Density.log2_block_bounds hp).1
    exact hh.trans (Nat.floor_le (by linarith))
  have he : (2:ℝ)^(⌊U⌋₊.log2+1) ≤ 2*U := by rw [pow_succ]; nlinarith
  have hh := Real.log_le_log (by positivity : (0:ℝ) < (2:ℝ)^(⌊U⌋₊.log2+1)) he
  rw [Real.log_pow] at hh
  have hb : ((⌊U⌋₊.log2+1:ℕ):ℝ) ≤ Real.log (2*U)/Real.log 2 :=
    (le_div_iff₀ hlog).mpr hh
  unfold cubicDyadicClasses
  simp only [Finset.card_product,Finset.card_range,Nat.cast_mul]
  calc
    _ = (((⌊U⌋₊.log2+1:ℕ):ℝ))^3 := by ring
    _ ≤ _ := by gcongr

/-- Exact finite partition, so no modes or mask-dependent multiplicities
are hidden in the dyadic decomposition. -/
theorem cubic_dyadic_sum_partition {M : Type*} [AddCommMonoid M]
    {U : ℝ} (hU : 1 ≤ U) (S : Finset (ℤ × (ℤ × ℤ))) (f : (ℤ × (ℤ × ℤ)) → M)
    (hS : ∀ m ∈ S, m.1 ∈ poissonModes U ∧ m.2.1 ∈ poissonModes U ∧ m.2.2 ∈ poissonModes U) :
    (∑ k ∈ cubicDyadicClasses U, ∑ m ∈ S with cubicDyadicClass m = k, f m) = ∑ m ∈ S, f m := by
  exact Finset.sum_fiberwise_of_maps_to (fun m hm => cubicDyadicClass_mem hU (hS m hm)) f

/-- All dyadic triples cost an arbitrarily small power, with the constant
fixed before the real truncation scale. -/
theorem cubicDyadicClasses_subpower {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 1 ≤ U →
      ((cubicDyadicClasses U).card:ℝ) ≤ C*U^ε := by
  have he : 0 < ε/3 := by positivity
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let D := (Real.log 2+1/(ε/3))/Real.log 2
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D^3,by positivity,?_⟩
  intro U hU
  have hUp : 0 < U := by linarith
  have hp : 1 ≤ U^(ε/3) := Real.one_le_rpow hU he.le
  have hb : Real.log (2*U)/Real.log 2 ≤ D*U^(ε/3) := by
    apply (div_le_iff₀ hlog).mpr
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hUp.ne']
    have hh := Real.log_le_rpow_div hUp.le he
    have hDmul : D*Real.log 2 = Real.log 2+1/(ε/3) := by dsimp [D]; field_simp
    calc
      _ ≤ Real.log 2*U^(ε/3)+U^(ε/3)/(ε/3) := by nlinarith
      _ = (D*Real.log 2)*U^(ε/3) := by rw [hDmul]; ring
      _ = _ := by ring
  calc
    _ ≤ (Real.log (2*U)/Real.log 2)^3 := cubicDyadicClasses_card hU
    _ ≤ (D*U^(ε/3))^3 := pow_le_pow_left₀
      (div_nonneg (Real.log_nonneg (by linarith)) hlog.le) hb 3
    _ = D^3*U^ε := by
      rw [mul_pow,← Real.rpow_natCast (U^(ε/3)) 3,← Real.rpow_mul hUp.le]
      congr 2
      norm_num

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.integer_dyadic_bounds
#print axioms GuthMaynard.Improvement.cubicDyadicClass_mem
#print axioms GuthMaynard.Improvement.cubicDyadicClasses_card

#print axioms GuthMaynard.Improvement.cubic_dyadic_sum_partition
#print axioms GuthMaynard.Improvement.cubicDyadicClasses_subpower
