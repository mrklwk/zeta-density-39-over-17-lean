module
public import DensityEnergyGM.LargeValuesFinal
public import GuthMaynard.NativeSource.GuthMaynard.ClassicalPowering

@[expose] public section

open Complex Finset
open scoped BigOperators

namespace GuthMaynard.NativeMoment

/-- The actual native large-value theorem with only the coefficients on its
literal open dyadic support bounded.  Clipping outside the support preserves
the polynomial exactly. -/
theorem guthMaynardLargeValues_support_native
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (N : ℕ) (V T : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
        0 < N → T₀ ≤ T → 0 < V →
        (∀ n ∈ dyadicInterval N, ‖b n‖ ≤ 1) →
        IsSeparated 1 W → InBaseInterval T W →
        (∀ t ∈ W, V ≤ ‖dirichletPoly N b t‖) →
        (W.card : ℝ) ≤ C * T ^ ε *
          ((N : ℝ) ^ 2 * V ^ (-2 : ℝ) +
            (N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℝ) +
            T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ)) := by
  classical
  obtain ⟨C, T₀, hC, hT₀, hGM⟩ :=
    guthMaynardLargeValues_neg guthMaynardLargeValues_native ε hε
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro N V T b W hN hT hV hb hSep hBase hLarge
  let c : ℕ → ℂ := fun n => if n ∈ dyadicInterval N then b n else 0
  have hc : ∀ n, ‖c n‖ ≤ 1 := by
    intro n
    by_cases hn : n ∈ dyadicInterval N
    · simpa only [c, ite_eq_left hn] using hb n hn
    · simp only [c, ite_eq_right hn, norm_zero, zero_le_one]
  have heq : ∀ t, dirichletPoly N c t = dirichletPoly N b t := by
    intro t
    unfold dirichletPoly
    apply Finset.sum_congr rfl
    intro n hn
    simp only [c, ite_eq_left hn]
  apply hGM N V T c W hN hT hV hc hSep hBase
  intro t ht
  rw [heq]
  exact hLarge t ht

/-- Uniform native powered large values.  The factorization and analytic
constants are chosen before the polynomial, amplitude, height and ordinate
set.  This is the literal powered-block step used for the square level count;
it has no assumed large-value theorem. -/
theorem powered_unit_block_gm_large_values_native
    (k : ℕ) (η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ A C T₀ : ℝ, 0 < A ∧ 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (N : ℕ) (a : ℕ → ℂ) (T L : ℝ) (W : Finset ℝ),
        0 < N → 0 < k → T₀ ≤ T → 0 < L →
        (∀ n ∈ Ioc N (2 * N), ‖a n‖ ≤ 1) →
        IsSeparated 1 W → InBaseInterval T W →
        (∀ t ∈ W, L ≤ ‖dirichletPoly N a t‖) →
        ∃ r ∈ Finset.range k, ∃ W' ⊆ W,
          let Q := 2 ^ r * N ^ k
          let V := (L ^ k / (A * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η)) / k
          (W.card : ℝ) ≤ k * (W'.card : ℝ) ∧
          (W'.card : ℝ) ≤ C * T ^ ε *
            ((Q : ℝ) ^ 2 * V ^ (-2 : ℝ) +
              (Q : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℝ) +
              T * (Q : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℝ)) := by
  obtain ⟨A, hA, hCoeff⟩ := finitePowCoeff_bound_uniform k η hη
  obtain ⟨C, T₀, hC, hT₀, hGM⟩ := guthMaynardLargeValues_support_native ε hε
  refine ⟨A, C, T₀, hA, hC, hT₀, ?_⟩
  intro N a T L W hN hk hT hL ha hSep hBase hLarge
  have hDenom : 0 < A * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η := by
    have hUpper : 0 < 2 ^ k * N ^ k := by positivity
    exact mul_pos hA (Real.rpow_pos_of_pos (by exact_mod_cast hUpper) _)
  obtain ⟨r, hr, W', hsub, hcard, hlarge⟩ :=
    extract_normalized_finite_powered_block N k a 0 A η L W hN hk hL.le hDenom
      (by
        intro t ht
        simpa [dirichletPoly, dyadicInterval, mul_comm] using hLarge t ht)
  let Q := 2 ^ r * N ^ k
  let V := (L ^ k / (A * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η)) / k
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hV : 0 < V := by dsimp only [V]; positivity
  have hWide : ∀ m ∈ dyadicInterval Q,
      m ∈ Ioc (N ^ k) (2 ^ k * N ^ k) := by
    intro m hm
    change m ∈ Ioc Q (2 * Q) at hm
    rw [Finset.mem_Ioc] at hm ⊢
    constructor
    · exact lt_of_le_of_lt (Nat.le_mul_of_pos_left (N ^ k)
        (pow_pos (by omega) r)) hm.1
    · have hrk : r + 1 ≤ k := by have := Finset.mem_range.mp hr; omega
      have hpow := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hrk
      have htwice : 2 * Q = 2 ^ (r + 1) * N ^ k := by
        dsimp only [Q]
        rw [pow_succ]
        ring
      rw [htwice] at hm
      exact hm.2.trans (Nat.mul_le_mul_right (N ^ k) hpow)
  have hNorm : ∀ m ∈ dyadicInterval Q,
      ‖normalizedFinitePoweredCoeffs N k a 0 A η m‖ ≤ 1 := by
    intro m hm
    have hmem := hWide m hm
    exact norm_normalizedFinitePoweredCoeffs_le_one N k m a 0 A η
      hN le_rfl hA hη hmem (hCoeff N a ha m (by
        have := (Finset.mem_Ioc.mp hmem).1
        omega))
  have hSep' : IsSeparated 1 W' := fun x hx y hy hxy =>
    hSep x (hsub hx) y (hsub hy) hxy
  have hBase' : InBaseInterval T W' := fun x hx => hBase x (hsub hx)
  have hbound := hGM Q V T (normalizedFinitePoweredCoeffs N k a 0 A η) W'
    hQ hT hV hNorm hSep' hBase' (by
      intro t ht
      simpa only [Q, V, Real.rpow_zero, one_mul] using hlarge t ht)
  exact ⟨r, hr, W', hsub, hcard, hbound⟩

end GuthMaynard.NativeMoment
