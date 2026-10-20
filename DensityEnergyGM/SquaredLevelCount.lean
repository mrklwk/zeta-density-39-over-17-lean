module
public import DensityEnergyGM.PoweredLargeValues
public import DensityEnergyGM.SquareLevelBounds

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
open Complex Finset
namespace GuthMaynard.NativeMoment

/-- Native square-level count, with the full uniform epsilon loss and
the exact fourth/eighth amplitude powers.  The coefficient-one instance is
obtained by taking `a = 1`. -/
theorem squared_polynomial_level_count_native (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (M : ℕ) (T U : ℝ) (a : ℕ → ℂ) (W : Finset ℝ),
        0 < M → T₀ ≤ T → (M : ℝ) ^ 2 ≤ T → 0 < U →
        (∀ n ∈ Ioc M (2 * M), ‖a n‖ ≤ 1) →
        IsSeparated 1 W → InBaseInterval T W →
        (∀ t ∈ W, U ≤ ‖dirichletPoly M a t‖) →
        (W.card : ℝ) ≤ C * T ^ ε *
          ((M : ℝ) ^ 4 * U ^ (-4 : ℝ) +
            (M : ℝ) ^ (36 / 5 : ℝ) * U ^ (-8 : ℝ) +
            T * (M : ℝ) ^ (24 / 5 : ℝ) * U ^ (-8 : ℝ)) := by
  let η : ℝ := ε / 8
  let δ : ℝ := ε / 2
  have hη : 0 < η := by dsimp only [η]; positivity
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨A, C₀, T₀, hA, hC₀, hT₀, hPowered⟩ :=
    powered_unit_block_gm_large_values_native 2 η δ hη hδ
  let B : ℝ := max 1 (2 * A * (4 : ℝ) ^ η)
  let C : ℝ := 32 * C₀ * B ^ 4
  have hBone : 1 ≤ B := le_max_left _ _
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hBone
  refine ⟨C, T₀, by dsimp only [C]; positivity, hT₀, ?_⟩
  intro M T U a W hM hT hMT hU ha hSep hBase hLarge
  have hTone : 1 ≤ T := hT₀.trans hT
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hTone
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨r, hr, W', hsub, hcard, hbound⟩ :=
    hPowered M a T U W hM (by norm_num) hT hU ha hSep hBase hLarge
  let q : ℝ := (2 ^ r * M ^ 2 : ℕ)
  let D : ℝ := 2 * (A * ((2 ^ 2 * M ^ 2 : ℕ) : ℝ) ^ η)
  have hDpos : 0 < D := by dsimp only [D]; positivity
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hqx : q ≤ 2 * (M : ℝ) ^ 2 := by
    have hrle : r ≤ 1 := by have := Finset.mem_range.mp hr; omega
    have hp : 2 ^ r ≤ 2 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ 2) hrle
    dsimp only [q]
    exact_mod_cast Nat.mul_le_mul_right (M ^ 2) hp
  have hDform : D = (2 * A * (4 : ℝ) ^ η) * ((M : ℝ) ^ 2) ^ η := by
    dsimp only [D]
    have hcast : ((2 ^ 2 * M ^ 2 : ℕ) : ℝ) = 4 * (M : ℝ) ^ 2 := by
      push_cast
      norm_num
    rw [hcast, Real.mul_rpow (by norm_num) (sq_nonneg _)]
    ring_nf
  have hDle : D ≤ B * T ^ η := by
    rw [hDform]
    exact mul_le_mul
      (le_max_right _ _) (Real.rpow_le_rpow (sq_nonneg _) hMT hη.le)
      (Real.rpow_nonneg (sq_nonneg _) _) hBpos.le
  have hPone : 1 ≤ B * T ^ η :=
    one_le_mul_of_one_le_of_one_le hBone (Real.one_le_rpow hTone hη.le)
  have hPpow : (B * T ^ η) ^ 4 = B ^ 4 * T ^ (4 * η) := by
    rw [mul_pow, ← Real.rpow_natCast (T ^ η) 4,
      ← Real.rpow_mul hTpos.le]
    congr 1
    ring_nf
  have hD4 : D ^ 4 ≤ B ^ 4 * T ^ (4 * η) := by
    rw [← hPpow]
    exact pow_le_pow_left₀ hDpos.le hDle 4
  have hD2 : D ^ 2 ≤ B ^ 4 * T ^ (4 * η) := by
    rw [← hPpow]
    exact (pow_le_pow_left₀ hDpos.le hDle 2).trans
      (pow_le_pow_right₀ hPone (by norm_num : 2 ≤ 4))
  have hVeq : (U ^ 2 / (A * ((2 ^ 2 * M ^ 2 : ℕ) : ℝ) ^ η)) / 2 =
      U ^ 2 / D := by
    dsimp only [D]
    rw [div_div]
    congr 1
    ring_nf
  have hbound' : (W'.card : ℝ) ≤ C₀ * T ^ δ *
      (q ^ 2 * (U ^ 2 / D) ^ (-2 : ℝ) +
        q ^ (18 / 5 : ℝ) * (U ^ 2 / D) ^ (-4 : ℝ) +
        T * q ^ (12 / 5 : ℝ) * (U ^ 2 / D) ^ (-4 : ℝ)) := by
    simpa only [q, Nat.cast_ofNat, hVeq] using hbound
  have hshape := square_level_shape_bound hq hMpos.le hqx hU hDpos hTpos.le
    (mul_nonneg (pow_nonneg hBpos.le 4) (Real.rpow_nonneg hTpos.le _)) hD2 hD4
  have hbudget : T ^ δ * T ^ (4 * η) = T ^ ε := by
    rw [← Real.rpow_add hTpos]
    congr 1
    dsimp only [δ, η]
    ring_nf
  calc
    (W.card : ℝ) ≤ 2 * (W'.card : ℝ) := by simpa only [Nat.cast_ofNat] using hcard
    _ ≤ 2 * (C₀ * T ^ δ *
        (q ^ 2 * (U ^ 2 / D) ^ (-2 : ℝ) +
          q ^ (18 / 5 : ℝ) * (U ^ 2 / D) ^ (-4 : ℝ) +
          T * q ^ (12 / 5 : ℝ) * (U ^ 2 / D) ^ (-4 : ℝ))) := by gcongr
    _ ≤ 2 * (C₀ * T ^ δ * (16 * (B ^ 4 * T ^ (4 * η)) *
        ((M : ℝ) ^ 4 * U ^ (-4 : ℝ) +
          (M : ℝ) ^ (36 / 5 : ℝ) * U ^ (-8 : ℝ) +
          T * (M : ℝ) ^ (24 / 5 : ℝ) * U ^ (-8 : ℝ)))) := by gcongr
    _ = C * T ^ ε *
        ((M : ℝ) ^ 4 * U ^ (-4 : ℝ) +
          (M : ℝ) ^ (36 / 5 : ℝ) * U ^ (-8 : ℝ) +
          T * (M : ℝ) ^ (24 / 5 : ℝ) * U ^ (-8 : ℝ)) := by
      dsimp only [C]
      rw [show 2 * (C₀ * T ^ δ * (16 * (B ^ 4 * T ^ (4 * η)) *
          ((M : ℝ) ^ 4 * U ^ (-4 : ℝ) + (M : ℝ) ^ (36 / 5 : ℝ) * U ^ (-8 : ℝ) +
            T * (M : ℝ) ^ (24 / 5 : ℝ) * U ^ (-8 : ℝ)))) =
          32 * C₀ * B ^ 4 * (T ^ δ * T ^ (4 * η)) *
            ((M : ℝ) ^ 4 * U ^ (-4 : ℝ) + (M : ℝ) ^ (36 / 5 : ℝ) * U ^ (-8 : ℝ) +
              T * (M : ℝ) ^ (24 / 5 : ℝ) * U ^ (-8 : ℝ)) by ring_nf, hbudget]

/-- The literal coefficient-one positive-phase level count. -/
theorem coefficient_one_squared_level_count_native (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (M : ℕ) (T U : ℝ) (W : Finset ℝ),
        0 < M → T₀ ≤ T → (M : ℝ) ^ 2 ≤ T → 0 < U →
        IsSeparated 1 W → InBaseInterval T W →
        (∀ t ∈ W, U ≤ ‖∑ n ∈ Ioc M (2 * M),
          (n : ℂ) ^ ((t : ℂ) * I)‖) →
        (W.card : ℝ) ≤ C * T ^ ε *
          ((M : ℝ) ^ 4 * U ^ (-4 : ℝ) +
            (M : ℝ) ^ (36 / 5 : ℝ) * U ^ (-8 : ℝ) +
            T * (M : ℝ) ^ (24 / 5 : ℝ) * U ^ (-8 : ℝ)) := by
  obtain ⟨C, T₀, hC, hT₀, hLevel⟩ := squared_polynomial_level_count_native ε hε
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro M T U W hM hT hMT hU hSep hBase hLarge
  apply hLevel M T U (fun _ => 1) W hM hT hMT hU
    (by intro n hn; norm_num) hSep hBase
  intro t ht
  have hNorm := norm_sourceDirichletPoly_conjugateCoeffs M (fun _ => 1) t
  have hOne : conjugateCoeffs (fun _ => (1 : ℂ)) = (fun _ => 1) := by
    funext n
    simp [conjugateCoeffs]
  rw [hOne] at hNorm
  rw [← hNorm]
  simpa only [sourceDirichletPoly, dyadicInterval, one_mul] using hLarge t ht

end GuthMaynard.NativeMoment
