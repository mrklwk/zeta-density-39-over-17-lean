module
public import DensityEnergyGM.EnergySensitiveDifference
public import CenteredMixedTrace

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Finset MeasureTheory
namespace Montgomery.RationalMoment

def energyCenteredBudget (k : ℕ) (T L R E : ℝ) : ℝ :=
  T * R ^ (2 - 1 / (k : ℝ)) +
    L * (T * E) ^ (1 / (2 * (k : ℝ))) * R ^ (2 - 2 / (k : ℝ))

theorem energyCenteredBudget_nonneg (k : ℕ) {T L R E : ℝ}
    (hT : 0 ≤ T) (hL : 0 ≤ L) (hR : 0 ≤ R) (hE : 0 ≤ E) :
    0 ≤ energyCenteredBudget k T L R E := by
  unfold energyCenteredBudget
  positivity

theorem reflection_complete_pair_energy {k : ℕ} (hk : 0 < k)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ : ℝ, 2 ≤ T → ∀ M : ℕ, 0 < M → (M : ℝ) ≤ 4 * T →
      ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀ + T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t - u|) →
      MathCollab.Density.completePairEnergy M W ≤ C * T ^ η *
        ((M : ℝ) ^ 2 * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
          (M : ℝ) * (T * (discreteAdditiveEnergy W : ℝ)) ^ (1 / (2 * (k : ℝ))) *
            (W.card : ℝ) ^ (2 - 2 / (k : ℝ))) := by
  obtain ⟨C, hC, hBound⟩ := energy_sensitive_dirichlet_difference k 3 η hk (by norm_num) hη
  refine ⟨C, hC, ?_⟩
  intro T t₀ hT M hM hMT W hW hSep
  have hTp : 0 < T := by linarith
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hA : ∀ n ∈ Ico M (2 * M), 0 < n ∧ (M : ℝ) - 1 / 2 < n ∧
      (n : ℝ) ≤ 2 * ((M : ℝ) - 1 / 2) := by
    intro n hn
    obtain ⟨hl, hu⟩ := mem_Ico.mp hn
    have hLo : (M : ℝ) ≤ n := by exact_mod_cast hl
    have hHi : (n : ℝ) + 1 ≤ 2 * (M : ℝ) := by exact_mod_cast hu
    exact ⟨hM.trans_le hl, by linarith, by linarith⟩
  have hX : 0 < (M : ℝ) - 1 / 2 := by linarith
  have h4 : 4 * T ≤ T ^ (3 : ℝ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hT 2) hTp.le
    nlinarith
  have hHeight : (M : ℝ) - 1 / 2 ≤ T ^ (3 : ℝ) := by linarith
  have h := hBound T t₀ ((M : ℝ) - 1 / 2) hT hX hHeight (Ico M (2 * M)) hA W
    hW hSep (fun _ => 1) (by simp)
  have hNorm (v : ℝ) : ‖MathCollab.Density.dyadicPolynomial M v‖ =
      ‖∑ n ∈ Ico M (2 * M), phase n v‖ := by
    have hEq : MathCollab.Density.dyadicPolynomial M v =
        (∑ n ∈ Ico M (2 * M), phase n v) * star (phase M v) := by
      unfold MathCollab.Density.dyadicPolynomial
      rw [sum_mul]
      apply sum_congr rfl
      intro n hn
      rw [density_phase_eq, phase_frequency_ratio
        (by exact_mod_cast (hA n hn).1) (by linarith)]
    rw [hEq, norm_mul, norm_star]
    have hPhase : ‖phase M v‖ = 1 := by rw [← exponentialPhase_log, exponentialPhase_norm]
    rw [hPhase, mul_one]
  unfold MathCollab.Density.completePairEnergy
  simp_rw [hNorm]
  simp only [one_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hX.le (by linarith : (M : ℝ) - 1 / 2 ≤ M) 2)
      (by positivity))
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : (M : ℝ) - 1 / 2 ≤ M) (by positivity))
      (by positivity))) (by positivity))

theorem reflection_local_energy_sensitive {k : ℕ} (hk : 0 < k)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ L H : ℝ, 2 ≤ T → 1 ≤ L → 0 < H → H ≤ 2 * T →
      ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀ + T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t - u|) →
      MathCollab.Density.localReflectionEnergy L H W ≤ C * T ^ η *
        ((H / L) ^ 2 * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
          (H / L) * (T * (discreteAdditiveEnergy W : ℝ)) ^ (1 / (2 * (k : ℝ))) *
            (W.card : ℝ) ^ (2 - 2 / (k : ℝ))) := by
  obtain ⟨C, hC, hBound⟩ := reflection_complete_pair_energy hk hη
  refine ⟨120 * C, by positivity, ?_⟩
  intro T t₀ L H hT hL hH hHT W hW hSep
  have hLp : 0 < L := by linarith
  open MathCollab.Density in
  have hBlock (M : ℕ) (hM : M ∈ reflectionBlocks L H) :
      (∑' j : ℤ, completePairEnergy M (localSet W H j)) ≤
        12 * (C * T ^ η *
          ((H / L) ^ 2 * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
            (H / L) * (T * (discreteAdditiveEnergy W : ℝ)) ^ (1 / (2 * (k : ℝ))) *
              (W.card : ℝ) ^ (2 - 2 / (k : ℝ)))) := by
    obtain ⟨hM0, _, hMhi⟩ := reflectionBlock_scale_bounds hLp hH hM
    have hMU : (M : ℝ) ≤ 2 * (H / L) := by
      apply hMhi.trans
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ (by positivity : 0 < Real.pi * L) hLp).mpr
      nlinarith [Real.pi_gt_three, mul_pos hH hLp]
    have hMT : (M : ℝ) ≤ 4 * T := by
      have h := div_le_self hH.le hL
      linarith
    have h := hBound T t₀ hT M hM0 hMT W hW hSep
    have hSq : (M : ℝ) ^ 2 ≤ 4 * (H / L) ^ 2 := by
      have h := pow_le_pow_left₀ (Nat.cast_nonneg M : (0 : ℝ) ≤ M) hMU 2
      nlinarith
    have hMono : C * T ^ η *
        ((M : ℝ) ^ 2 * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
          (M : ℝ) * (T * (discreteAdditiveEnergy W : ℝ)) ^ (1 / (2 * (k : ℝ))) *
            (W.card : ℝ) ^ (2 - 2 / (k : ℝ))) ≤
        4 * (C * T ^ η *
          ((H / L) ^ 2 * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
            (H / L) * (T * (discreteAdditiveEnergy W : ℝ)) ^ (1 / (2 * (k : ℝ))) *
              (W.card : ℝ) ^ (2 - 2 / (k : ℝ)))) := by
      have hLin : (M : ℝ) ≤ 4 * (H / L) := by
        have hp : 0 ≤ H / L := by positivity
        linarith
      calc
        _ ≤ C * T ^ η *
            ((4 * (H / L) ^ 2) * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
              (4 * (H / L)) * (T * (discreteAdditiveEnergy W : ℝ)) ^ (1 / (2 * (k : ℝ))) *
                (W.card : ℝ) ^ (2 - 2 / (k : ℝ))) := by
          exact mul_le_mul_of_nonneg_left (add_le_add
            (mul_le_mul_of_nonneg_right hSq (by positivity))
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLin (by positivity))
              (by positivity))) (by positivity)
        _ = _ := by ring
    exact (reflection_local_pair_le_three hH M W).trans
      ((mul_le_mul_of_nonneg_left (h.trans hMono) (by norm_num : (0 : ℝ) ≤ 3)).trans_eq (by ring))
  open MathCollab.Density in
  calc
    localReflectionEnergy L H W ≤ ∑ _M ∈ reflectionBlocks L H,
        12 * (C * T ^ η *
          ((H / L) ^ 2 * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
            (H / L) * (T * (discreteAdditiveEnergy W : ℝ)) ^ (1 / (2 * (k : ℝ))) *
              (W.card : ℝ) ^ (2 - 2 / (k : ℝ)))) := sum_le_sum hBlock
    _ = ((reflectionBlocks L H).card : ℝ) *
        (12 * (C * T ^ η *
          ((H / L) ^ 2 * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
            (H / L) * (T * (discreteAdditiveEnergy W : ℝ)) ^ (1 / (2 * (k : ℝ))) *
              (W.card : ℝ) ^ (2 - 2 / (k : ℝ))))) := by simp
    _ ≤ 10 * (12 * (C * T ^ η *
          ((H / L) ^ 2 * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
            (H / L) * (T * (discreteAdditiveEnergy W : ℝ)) ^ (1 / (2 * (k : ℝ))) *
              (W.card : ℝ) ^ (2 - 2 / (k : ℝ))))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast reflectionBlocks_card_le hLp hH
    _ = _ := by ring

end Montgomery.RationalMoment
