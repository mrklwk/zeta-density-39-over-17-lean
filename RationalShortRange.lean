module
public import RationalMomentTheorem

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment

/-- In the overlap range of the k-th moment, the rational-frequency energy
is linear in the reduced denominator height. All analytic inputs are proved. -/
theorem rational_energy_linear_height {k : ℕ} (hk : 1 ≤ k) {η : ℝ} (hη : 0 < η) :
    ∃ D : ℝ, 0 < D ∧ ∀ (H : ℕ), 1 ≤ H → ∀ (T t₀ : ℝ), 0 ≤ T →
      ∀ (A : Finset ℚ),
      (∀ r ∈ A, 0 < r ∧ r.den ≤ H ∧ |Real.log (r : ℝ)| ≤ 1) →
      ∀ (W : Finset ℝ), (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (H : ℝ)^k ≤ W.card → T ≤ (H : ℝ)^k*W.card →
      rationalEnergy A W ≤ D*(H : ℝ)^η*(H : ℝ)*(W.card : ℝ)^2 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  obtain ⟨C, hC, hdual⟩ := rational_dual_moment hk (show 0 < η*(k : ℝ) by positivity)
  let D := max 1 (2*C)
  have hD : 1 ≤ D := le_max_left _ _
  have hCpow : 2*C ≤ D^k := by
    apply (le_max_right 1 (2*C)).trans
    simpa only [pow_one] using (pow_le_pow_right₀ hD hk)
  refine ⟨D, by linarith, ?_⟩
  intro H hH T t₀ hT A hA W hW hsep hHR hTR
  have hm := hdual H hH T t₀ hT A hA W hW hsep
  let R : ℝ := W.card
  have hR : 0 ≤ R := Nat.cast_nonneg _
  have hH0 : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hE : 0 ≤ rationalEnergy A W := sum_nonneg (fun _ _ => sq_nonneg _)
  have hHpow : (H : ℝ)^(2*k) = ((H : ℝ)^k)^2 := by rw [← pow_mul, Nat.mul_comm]
  have htotal : T+(H : ℝ)^(2*k) ≤ 2*(H : ℝ)^k*R := by
    rw [hHpow]
    have hh := mul_le_mul_of_nonneg_left hHR (pow_nonneg hH0.le k)
    change T ≤ (H : ℝ)^k*R at hTR
    change (H : ℝ)^k*(H : ℝ)^k ≤ (H : ℝ)^k*R at hh
    nlinarith
  have hRmul : R^(2*k-1)*R = R^(2*k) := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ 2*k)]
  have hsplit : (H : ℝ)^(η*(k : ℝ)) = ((H : ℝ)^η)^k := by
    rw [Real.rpow_mul hH0.le, Real.rpow_natCast]
  apply (pow_le_pow_iff_left₀ hE (by positivity) (by omega : k ≠ 0)).mp
  calc
    _ ≤ R^(2*k-1)*(C*(T+(H : ℝ)^(2*k))*(H : ℝ)^(η*(k : ℝ))) := hm
    _ ≤ R^(2*k-1)*(C*(2*(H : ℝ)^k*R)*(H : ℝ)^(η*(k : ℝ))) := by
      gcongr
    _ = (2*C)*((H : ℝ)^η)^k*(H : ℝ)^k*R^(2*k) := by
      rw [hsplit]
      calc
        _ = (2*C)*((H : ℝ)^η)^k*(H : ℝ)^k*(R^(2*k-1)*R) := by ring
        _ = _ := by rw [hRmul]
    _ ≤ D^k*((H : ℝ)^η)^k*(H : ℝ)^k*R^(2*k) := by gcongr
    _ = _ := by
      simp only [mul_pow, ← pow_mul]
      ring

/-- Coprime pairs retain the same estimate, with no multiplicity loss. -/
theorem coprime_energy_linear_height {k : ℕ} (hk : 1 ≤ k) {η : ℝ} (hη : 0 < η) :
    ∃ D : ℝ, 0 < D ∧ ∀ (H : ℕ), 1 ≤ H → ∀ (T t₀ : ℝ), 0 ≤ T →
      ∀ Q : Finset (ℕ × ℕ),
      (∀ q ∈ Q, 0 < q.2 ∧ Nat.Coprime q.1 q.2) →
      (∀ q ∈ Q, 0 < pairRatio q ∧ (pairRatio q).den ≤ H ∧
        |Real.log (pairRatio q : ℝ)| ≤ 1) →
      ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (H : ℝ)^k ≤ W.card → T ≤ (H : ℝ)^k*W.card →
      (∑ q ∈ Q, ‖∑ t ∈ W, phase (pairRatio q) t‖^2) ≤
        D*(H : ℝ)^η*(H : ℝ)*(W.card : ℝ)^2 := by
  obtain ⟨D, hD, hbound⟩ := rational_energy_linear_height hk hη
  refine ⟨D, hD, ?_⟩
  intro H hH T t₀ hT Q hQ hrat W hW hsep hHR hTR
  rw [reduced_energy_eq_rational_energy Q hQ W]
  apply hbound H hH T t₀ hT (Q.image pairRatio) _ W hW hsep hHR hTR
  intro r hr
  obtain ⟨q, hq, rfl⟩ := mem_image.mp hr
  exact hrat q hq

end Montgomery.RationalMoment
