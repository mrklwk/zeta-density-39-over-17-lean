module
public import DensityEnergyGM.PoweredLargeValues
public import RationalMomentDuality
public import GuthMaynard.NativeSource.GuthMaynard.MeanValueProof

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Complex Finset
namespace Montgomery.RationalMoment
open GuthMaynard.NativeMoment

/-- An actual integer cube, followed by the proved separated mean square.
No fractional polynomial power or assumed analytic estimate is used. -/
theorem short_polynomial_sixth_moment_native (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ℕ) (T : ℝ) (a : ℕ → ℂ) (W : Finset ℝ),
        0 < M → 2 ≤ T → (M : ℝ) ^ 2 ≤ T →
        (∀ n ∈ Ioc M (2 * M), ‖a n‖ ≤ 1) →
        IsSeparated 1 W → InBaseInterval T W →
        (∑ t ∈ W, ‖dirichletPoly M a t‖ ^ 6) ≤
          C * T ^ ε * ((M : ℝ) ^ 6 + T * (M : ℝ) ^ 3) := by
  let η : ℝ := ε / 3
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨A, hA, hCoeff⟩ := finitePowCoeff_bound_uniform 3 η hη
  let K : ℝ := 3 * (2 + 2 * (5 * Real.pi + 1))
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨144 * K * A ^ 2 * (8 : ℝ) ^ (2 * η), by positivity, ?_⟩
  intro M T a W hM hT hMT ha hSep hBase
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hTp : 0 < T := by linarith
  let c := finitePoweredLineCoeffs M 3 a 0
  let D : ℝ := A * (8 * (M : ℝ) ^ 3) ^ η
  have hD : 0 < D := by dsimp only [D]; positivity
  have hWide (t : ℝ) : wideDirichletPoly (M ^ 3) 3 c t =
      (dirichletPoly M a t) ^ 3 := by
    have hh := wideDirichletPoly_finitePoweredLineCoeffs M 3 a 0 t hM (by norm_num)
    simpa only [c, ofReal_zero, cpow_zero, one_mul, zero_add,
      finitePowPoly, dirichletPoly, dyadicInterval, mul_comm I (t : ℂ),
      neg_mul, ofReal_neg, ofReal_mul] using hh
  have hNorm : ∀ m ∈ Ioc (M ^ 3) (2 ^ 3 * M ^ 3), ‖c m‖ ≤ D := by
    intro m hm
    have hmp : 0 < m := lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp hm).1
    have hmU : (m : ℝ) ≤ 8 * (M : ℝ) ^ 3 := by
      exact_mod_cast (mem_Ioc.mp hm).2
    exact (norm_finitePoweredLineCoeffs_le M 3 m a 0 hM le_rfl hm).trans
      ((hCoeff M a ha m hmp).trans (by
        dsimp only [D]
        gcongr))
  have hEach : ∀ r ∈ range 3,
      (∑ t ∈ W, ‖dirichletPoly (2 ^ r * M ^ 3) c t‖ ^ 2) ≤
        16 * K * D ^ 2 * ((M : ℝ) ^ 6 + T * (M : ℝ) ^ 3) := by
    intro r hr
    let Q := 2 ^ r * M ^ 3
    have hQ : 0 < Q := by dsimp only [Q]; positivity
    have hr2 : r ≤ 2 := by have := mem_range.mp hr; omega
    have h2r : 2 ^ r ≤ 4 := by
      have hh := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hr2
      norm_num at hh ⊢
      exact hh
    have hQr : (Q : ℝ) ≤ 4 * (M : ℝ) ^ 3 := by
      dsimp only [Q]
      exact_mod_cast Nat.mul_le_mul_right (M ^ 3) h2r
    have hsub : Ioc Q (2 * Q) ⊆ Ioc (M ^ 3) (2 ^ 3 * M ^ 3) := by
      intro m hm
      obtain ⟨hmL, hmU⟩ := mem_Ioc.mp hm
      apply mem_Ioc.mpr
      constructor
      · exact lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by positivity)) hmL
      · have hQu : Q ≤ 4 * M ^ 3 := Nat.mul_le_mul_right (M ^ 3) h2r
        omega
    have hEnergy : (∑ m ∈ Ioc Q (2 * Q), ‖c m‖ ^ 2) ≤ (Q : ℝ) * D ^ 2 := by
      calc
        _ ≤ ∑ _m ∈ Ioc Q (2 * Q), D ^ 2 := by
          exact sum_le_sum (fun m hm => pow_le_pow_left₀ (norm_nonneg _) (hNorm m (hsub hm)) 2)
        _ = _ := by simp [Nat.card_Ioc, show 2 * Q - Q = Q by omega]
    have hh := montgomery_mean_value_estimate Q T W c hQ (by linarith) hSep hBase
    have hId : (∑ t ∈ W, ‖dirichletPoly Q c t‖ ^ 2) ≤
        K * (T + (Q : ℝ)) * ((Q : ℝ) * D ^ 2) := by
      apply (show (∑ t ∈ W, ‖dirichletPoly Q c t‖ ^ 2) ≤
        K * (T + (Q : ℝ)) * ∑ m ∈ Ioc Q (2 * Q), ‖c m‖ ^ 2 from ?_).trans
        (mul_le_mul_of_nonneg_left hEnergy (by positivity))
      simpa only [K, dirichletPoly, dyadicInterval, ofReal_neg, ofReal_mul] using hh
    apply hId.trans
    calc
      _ ≤ K * (T + 4 * (M : ℝ) ^ 3) * (4 * (M : ℝ) ^ 3 * D ^ 2) := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg (by positivity : 0 ≤ K * D ^ 2) (by positivity : 0 ≤ T * (M : ℝ) ^ 3)]
  have hPoint (t : ℝ) : ‖dirichletPoly M a t‖ ^ 6 ≤
      3 * ∑ r ∈ range 3, ‖dirichletPoly (2 ^ r * M ^ 3) c t‖ ^ 2 := by
    have hh := norm_sum_pow_le (range 3)
      (fun r => dirichletPoly (2 ^ r * M ^ 3) c t) (p := 2) (by norm_num)
    rw [← wideDirichletPoly_eq_sum_blocks, hWide] at hh
    simpa only [norm_pow, ← pow_mul, card_range, Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, pow_one] using hh
  have hTotal : (∑ t ∈ W, ‖dirichletPoly M a t‖ ^ 6) ≤
      144 * K * D ^ 2 * ((M : ℝ) ^ 6 + T * (M : ℝ) ^ 3) := by
    calc
      _ ≤ ∑ t ∈ W, 3 * ∑ r ∈ range 3, ‖dirichletPoly (2 ^ r * M ^ 3) c t‖ ^ 2 :=
        sum_le_sum (fun t _ => hPoint t)
      _ = 3 * ∑ r ∈ range 3, ∑ t ∈ W, ‖dirichletPoly (2 ^ r * M ^ 3) c t‖ ^ 2 := by
        rw [← mul_sum, sum_comm]
      _ ≤ 3 * ∑ _r ∈ range 3,
          16 * K * D ^ 2 * ((M : ℝ) ^ 6 + T * (M : ℝ) ^ 3) := by gcongr; exact hEach _ ‹_›
      _ = _ := by simp; ring
  have hD2 : D ^ 2 ≤ A ^ 2 * (8 : ℝ) ^ (2 * η) * T ^ ε := by
    have hPow : (M : ℝ) ^ (6 * η) ≤ T ^ ε := by
      have hh := Real.rpow_le_rpow (sq_nonneg (M : ℝ)) hMT
        (show 0 ≤ 3 * η by positivity)
      rw [← Real.rpow_natCast_mul hMp.le] at hh
      convert hh using 1 <;> congr 1 <;> dsimp only [η] <;> ring
    calc
      D ^ 2 = A ^ 2 * (8 : ℝ) ^ (2 * η) * (M : ℝ) ^ (6 * η) := by
        dsimp only [D]
        rw [mul_pow, ← Real.rpow_mul_natCast (by positivity : 0 ≤ 8 * (M : ℝ) ^ 3),
          Real.mul_rpow (by norm_num) (by positivity),
          ← Real.rpow_natCast_mul hMp.le]
        ring_nf
      _ ≤ _ := by gcongr
  apply hTotal.trans
  calc
    _ ≤ 144 * K * (A ^ 2 * (8 : ℝ) ^ (2 * η) * T ^ ε) *
        ((M : ℝ) ^ 6 + T * (M : ℝ) ^ 3) := by gcongr
    _ = _ := by ring

end Montgomery.RationalMoment
