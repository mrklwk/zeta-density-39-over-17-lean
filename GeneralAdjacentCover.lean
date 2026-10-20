module
public import AdjacentRationalEnergy

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Montgomery.RationalMoment

/-- Adjacent moments are chosen from a finite set before the height varies.
No cardinality exponent restriction is needed in this cover. -/
theorem adjacent_finite_height_cover {K : ℕ} (hK : 1 ≤ K)
    {m δ : ℝ} (hδ : 0 < δ) (hδm : δ ≤ m)
    (hm : m ≤ 1/(2*(K:ℝ))) :
    ∃ j : ℕ, K ≤ j ∧ j ≤ ⌈1/δ⌉₊ ∧
      2*(j:ℝ)*m ≤ 1 ∧ 1 ≤ 2*((j:ℝ)+1)*m := by
  have hkp : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hmp : 0 < m := hδ.trans_le hδm
  let j := ⌊1/(2*m)⌋₊
  have hKj : K ≤ j := Nat.le_floor ((le_div_iff₀ (by positivity : 0 < 2*m)).mpr (by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*(K:ℝ))).mp hm
    nlinarith))
  have hjr : (0:ℝ) ≤ j := Nat.cast_nonneg _
  have hlo : 2*(j:ℝ)*m ≤ 1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*m)).mp
      (Nat.floor_le (by positivity : 0 ≤ 1/(2*m)))
    nlinarith only [hh]
  have hhi : 1 ≤ 2*((j:ℝ)+1)*m := by
    have hh := (div_lt_iff₀ (by positivity : 0 < 2*m)).mp (Nat.lt_floor_add_one (1/(2*m)))
    nlinarith only [hh]
  have hbound : j ≤ ⌈1/δ⌉₊ := by
    have hh := mul_le_mul_of_nonneg_left hδm hjr
    have hjδ : (j:ℝ)*δ ≤ 1 := by nlinarith
    have hh' : (j:ℝ) ≤ (⌈1/δ⌉₊:ℝ) :=
      ((le_div_iff₀ hδ).mpr hjδ).trans (Nat.le_ceil _)
    exact_mod_cast hh'
  exact ⟨j,hKj,hbound,hlo,hhi⟩

/-- The exact logarithmic remainder comparison for adjacent moment orders.
Both logarithmic heights and cardinalities may vary freely in their ranges. -/
theorem adjacent_log_remainder {k j r t : ℝ}
    (hk : 0 < k) (hkj : k ≤ j) (hr : 0 ≤ r) :
    let ck := (2*k+1)/(2*k*(k+1))
    let cj := (2*j+1)/(2*j*(j+1))
    t/(2*j)-cj*r ≤ max 0 (t/(2*k)-ck*r) := by
  have hj : 0 < j := hk.trans_le hkj
  have hk1 : 0 < k+1 := by linarith
  have hj1 : 0 < j+1 := by linarith
  dsimp only
  have hid : (t/(2*j)-(2*j+1)/(2*j*(j+1))*r)-
      (k/j)*(t/(2*k)-(2*k+1)/(2*k*(k+1))*r) =
      r*(k-j)/(2*j*(j+1)*(k+1)) := by
    field_simp
    ring
  have he : t/(2*j)-(2*j+1)/(2*j*(j+1))*r ≤
      (k/j)*(t/(2*k)-(2*k+1)/(2*k*(k+1))*r) := by
    have hh : r*(k-j)/(2*j*(j+1)*(k+1)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hr (by linarith)) (by positivity)
    linarith only [hid,hh]
  have hθ : 0 ≤ k/j := by positivity
  have hθ1 : k/j ≤ 1 := (div_le_one hj).mpr hkj
  have hd : t/(2*k)-(2*k+1)/(2*k*(k+1))*r ≤
      max 0 (t/(2*k)-(2*k+1)/(2*k*(k+1))*r) := le_max_right _ _
  have hd0 : 0 ≤ max 0 (t/(2*k)-(2*k+1)/(2*k*(k+1))*r) := le_max_left _ _
  calc
    _ ≤ (k/j)*(t/(2*k)-(2*k+1)/(2*k*(k+1))*r) := he
    _ ≤ (k/j)*max 0 (t/(2*k)-(2*k+1)/(2*k*(k+1))*r) := mul_le_mul_of_nonneg_left hd hθ
    _ ≤ _ := mul_le_of_le_one_left hd0 hθ1

end Montgomery.RationalMoment
