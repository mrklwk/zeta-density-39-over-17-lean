module
public import SmallGcdCubicEnergy

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset
namespace Montgomery.RationalMoment

/-- Distinct reduced fractions retain the actual fourth energy in the
sampling estimate. No lower bound on the ordinate cardinality is required. -/
theorem coprime_dyadic_fourth_energy {T t₀ M : ℝ} (hT : 1 < T) (hM : 0 < M)
    (Q : Finset (ℕ × ℕ))
    (hQ : ∀ q ∈ Q, 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2 ∧
      M < q.1 ∧ (q.1:ℝ) ≤ 2*M ∧ M < q.2 ∧ (q.2:ℝ) ≤ 2*M)
    (W : Finset ℝ) (hW : ∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T))
    :
    (∑ q ∈ Q, ‖∑ t ∈ W, phase (pairRatio q) t‖^4) ≤
      1024*(16*Real.pi*M^2+12*Real.pi*T)*(discreteAdditiveEnergy W:ℝ) := by
  let x : Q → ℝ := fun q => Real.log ((q.1.1:ℝ)/q.1.2)/(2*Real.pi)
  let δ : ℝ := 1/(16*Real.pi*M^2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hx (q : Q) : |x q| ≤ 1 := by
    obtain ⟨h1,h2,_,hl1,hu1,hl2,hu2⟩ := hQ q q.2
    have hh := dyadic_pair_log h1 h2 hl1 hu1 hl2 hu2
    simp only [pairRatio,Rat.cast_div,Rat.cast_natCast] at hh
    dsimp [x]
    rw [abs_div,abs_of_pos (by positivity : 0 < 2*Real.pi)]
    apply (div_le_one (by positivity : 0 < 2*Real.pi)).mpr
    linarith [Real.pi_gt_three]
  have hs : Pairwise (fun p q : Q => δ ≤ |x p-x q|) := by
    intro p q hpq
    have hp := hQ p p.2
    have hq := hQ q q.2
    have hgap := rational_log_separation ⟨hp.1,hp.2.1,hp.2.2.1⟩
      ⟨hq.1,hq.2.1,hq.2.2.1⟩ (by exact fun he => hpq (Subtype.ext he))
      hp.2.2.2.2.2.2 hq.2.2.2.2.2.2
      (U := 2) ((div_le_iff₀ (by exact_mod_cast hp.2.1)).mpr (by linarith [hp.2.2.2.1,hp.2.2.2.2.2.1]))
      ((div_le_iff₀ (by exact_mod_cast hq.2.1)).mpr (by linarith [hq.2.2.2.1,hq.2.2.2.2.2.1]))
    dsimp [x,δ]
    rw [← sub_div,abs_div,abs_of_pos (by positivity : 0 < 2*Real.pi)]
    apply (le_div_iff₀ (by positivity : 0 < 2*Real.pi)).mpr
    convert hgap using 1; field_simp; ring
  have hh := sampled_character_fourth hT hδ W hW x hx hs
  have he (q : Q) : ‖centeredCharacter W t₀ (x q)‖=‖∑ t ∈ W, phase (pairRatio q) t‖ := by
    dsimp only [x]
    rw [centered_character_norm]
    simp only [pairRatio,Rat.cast_div,Rat.cast_natCast]
  simp only [he] at hh
  rw [Finset.sum_coe_sort Q (fun q => ‖∑ t ∈ W, phase (pairRatio q) t‖^4)] at hh
  have hd : δ⁻¹=16*Real.pi*M^2 := by dsimp [δ]; rw [inv_div,div_one]
  simpa only [hd] using hh


/-- The reduced fourth moment at every short real scale, including small
scales and the exact tolerance-one energy. -/
theorem coprime_short_fourth_energy {T t₀ M : ℝ} (hT : 1 < T) (hM : 0 < M)
    (hMT : M ^ 2 ≤ T) (Q : Finset (ℕ × ℕ))
    (hQ : ∀ q ∈ Q, 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2 ∧
      M < q.1 ∧ (q.1 : ℝ) ≤ 2 * M ∧ M < q.2 ∧ (q.2 : ℝ) ≤ 2 * M)
    (W : Finset ℝ) (hW : ∀ t ∈ W, t ∈ Set.Icc t₀ (t₀ + T)) :
    (∑ q ∈ Q, ‖∑ t ∈ W, phase (pairRatio q) t‖ ^ 4) ≤
      (28672 * Real.pi) * T * (discreteAdditiveEnergy W : ℝ) := by
  have h := coprime_dyadic_fourth_energy hT hM Q hQ W hW
  have he : 0 ≤ (discreteAdditiveEnergy W : ℝ) := Nat.cast_nonneg _
  have hscale : 16 * Real.pi * M ^ 2 + 12 * Real.pi * T ≤ 28 * Real.pi * T := by
    nlinarith [Real.pi_pos]
  exact h.trans (by nlinarith [mul_le_mul_of_nonneg_right hscale he])

end Montgomery.RationalMoment
