module
public import DensityEnergyGM.SharpEnergyExpansion
public import DensityEnergyGM.SublinearEnergyAbsorption
public import DensityEnergyGM.EnergyMonomialPowers

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 3200000
noncomputable section
open Finset GuthMaynard.NativeMoment GuthMaynard.Improvement
namespace Montgomery.RationalMoment

/-- The requested five-term energy bound for the actual detecting
polynomial, at eventual height in the base interval. Every analytic input
is supplied by a proved native theorem inside the proof. -/
theorem discrete_energy_five_term_base_eventual (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T N : ℝ) (a : ℕ → ℂ) (W : Finset ℝ) (V : ℝ),
        T₀ ≤ T → 0 < N → T ≤ N ^ 2 → N ≤ T →
        (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
        0 < V → (∀ t ∈ W, V ≤ ‖boundedPolynomial N a t‖) →
        IsSeparated 1 W → InBaseInterval T W →
        (discreteAdditiveEnergy W : ℝ) ≤ C * T ^ ε *
          (N ^ 4 * (W.card : ℝ) * V ^ (-4 : ℝ) +
            N ^ 4 * T ^ 2 * V ^ (-8 : ℝ) +
            N ^ (5 / 2 : ℝ) * T ^ (9 / 8 : ℝ) * V ^ (-5 : ℝ) * (W.card : ℝ) ^ (3 / 2 : ℝ) +
            N ^ (40 / 31 : ℝ) * T ^ (9 / 31 : ℝ) * V ^ (-80 / 31 : ℝ) * (W.card : ℝ) ^ (84 / 31 : ℝ) +
            N ^ (40 / 19 : ℝ) * T ^ (17 / 19 : ℝ) * V ^ (-80 / 19 : ℝ) * (W.card : ℝ) ^ (36 / 19 : ℝ)) := by
  let δ : ℝ := ε / 4
  obtain ⟨C₀, T₀, hC₀, hT₀, hNative⟩ := discrete_energy_sublinear_native δ (by dsimp only [δ]; positivity)
  let B : ℝ := 2 * C₀ + 1
  let K : ℝ := 5 * B
  have hB : 0 < B := by dsimp only [B]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  have hKone : 1 ≤ K := by dsimp only [K, B]; linarith
  refine ⟨K ^ 4, T₀, by positivity, hT₀, ?_⟩
  intro T N a W V hT hN hTN hNT ha hV hValues hSep hBase
  have hTtwo : 2 ≤ T := hT₀.trans hT
  have hTone : 1 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  let E : ℝ := discreteAdditiveEnergy W
  let R : ℝ := W.card
  have hE0 : 0 ≤ E := Nat.cast_nonneg _
  have hR0 : 0 ≤ R := Nat.cast_nonneg _
  let A : ℝ → ℝ → ℝ → ℝ := fun α β γ => B * T ^ δ * N ^ α * T ^ β * R ^ γ
  have hA0 : ∀ α β γ, 0 ≤ A α β γ := by
    intro α β γ
    dsimp only [A]
    positivity
  have hFront : E * V ^ 2 ≤
      A 2 0 (1 / 2) * E ^ (1 / 2 : ℝ) +
      A 1 (1 / 2) 0 * E ^ (3 / 4 : ℝ) +
      A 1 (9 / 20) (3 / 5) * E ^ (3 / 5 : ℝ) +
      A 1 (9 / 40) (21 / 10) * E ^ (9 / 40 : ℝ) +
      A 1 (17 / 40) (9 / 10) * E ^ (21 / 40 : ℝ) := by
    have hActual := hNative T N a W V hT hN hTN hNT ha hV hValues hSep hBase
    change E * V ^ 2 ≤ C₀ * T ^ δ *
      (N ^ 2 * R ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) +
        N * T ^ (1 / 2 : ℝ) * E ^ (3 / 4 : ℝ) +
        N * T ^ (9 / 20 : ℝ) * R ^ (3 / 5 : ℝ) * E ^ (3 / 5 : ℝ) +
        N * T ^ (9 / 40 : ℝ) * R ^ (21 / 10 : ℝ) * E ^ (9 / 40 : ℝ) +
        2 * N * T ^ (17 / 40 : ℝ) * R ^ (9 / 10 : ℝ) * E ^ (21 / 40 : ℝ)) at hActual
    have hDiff : 0 ≤ (B - C₀) * T ^ δ *
      (N ^ 2 * R ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) +
        N * T ^ (1 / 2 : ℝ) * E ^ (3 / 4 : ℝ) +
        N * T ^ (9 / 20 : ℝ) * R ^ (3 / 5 : ℝ) * E ^ (3 / 5 : ℝ) +
        N * T ^ (9 / 40 : ℝ) * R ^ (21 / 10 : ℝ) * E ^ (9 / 40 : ℝ)) := by
      have hb : 0 ≤ B - C₀ := by dsimp only [B]; linarith
      positivity
    have hLast : 0 ≤ (B - 2 * C₀) * T ^ δ *
      (N * T ^ (17 / 40 : ℝ) * R ^ (9 / 10 : ℝ) * E ^ (21 / 40 : ℝ)) := by
      have hb : 0 ≤ B - 2 * C₀ := by dsimp only [B]; linarith
      positivity
    dsimp only [A]
    simp only [Real.rpow_two, Real.rpow_one, Real.rpow_zero, mul_one]
    nlinarith
  have hSolved := five_sublinear_energy_absorption hE0 hV
    (hA0 2 0 (1 / 2)) (hA0 1 (1 / 2) 0) (hA0 1 (9 / 20) (3 / 5))
    (hA0 1 (9 / 40) (21 / 10)) (hA0 1 (17 / 40) (9 / 10))
    (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num : (3 / 4 : ℝ) < 1)
    (by norm_num : (3 / 5 : ℝ) < 1) (by norm_num : (9 / 40 : ℝ) < 1)
    (by norm_num : (21 / 40 : ℝ) < 1) hFront
  have hRoot (α β γ q : ℝ) :
      (5 * A α β γ / V ^ 2) ^ q = K ^ q * T ^ (δ * q) *
        (N ^ (α * q) * T ^ (β * q) * V ^ (-2 * q) * R ^ (γ * q)) := by
    have hNumerator : 5 * A α β γ = K * T ^ δ * N ^ α * T ^ β * R ^ γ := by
      dsimp only [A, K]
      ring
    rw [hNumerator]
    exact energy_monomial_rpow δ α β γ q hK.le hN.le hTpos.le hR0 hV.le
  have hRootBound (α β γ q : ℝ) (hq : q ≤ 4) :
      (5 * A α β γ / V ^ 2) ^ q ≤ K ^ 4 * T ^ ε *
        (N ^ (α * q) * T ^ (β * q) * V ^ (-2 * q) * R ^ (γ * q)) := by
    rw [hRoot]
    have hKpow : K ^ q ≤ K ^ (4 : ℕ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hKone hq
    have hδq : δ * q ≤ ε := by dsimp only [δ]; nlinarith
    have hTpow : T ^ (δ * q) ≤ T ^ ε :=
      Real.rpow_le_rpow_of_exponent_le hTone hδq
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hKpow hTpow (by positivity) (by positivity)) (by positivity)
  have h1 := hRootBound 2 0 (1 / 2) 2 (by norm_num)
  have h2 := hRootBound 1 (1 / 2) 0 4 (by norm_num)
  have h3 := hRootBound 1 (9 / 20) (3 / 5) (5 / 2) (by norm_num)
  have h4 := hRootBound 1 (9 / 40) (21 / 10) (40 / 31) (by norm_num)
  have h5 := hRootBound 1 (17 / 40) (9 / 10) (40 / 19) (by norm_num)
  norm_num at hSolved h1 h2 h3 h4 h5
  change E ≤ _
  calc
    _ ≤ _ := hSolved
    _ ≤ _ := add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) h5
    _ = _ := by dsimp only [R]; norm_num; ring

end Montgomery.RationalMoment
