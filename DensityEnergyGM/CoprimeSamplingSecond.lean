module
public import DensityEnergyGM.CoprimeFourthEnergy

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset
namespace Montgomery.RationalMoment

/-- Actual reduced second moment from separated Fourier sampling. -/
theorem coprime_dyadic_second_energy {T t₀ M : ℝ} (hT : 1 < T) (hM : 0 < M)
    (Q : Finset (ℕ × ℕ))
    (hQ : ∀ q ∈ Q, 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2 ∧
      M < q.1 ∧ (q.1:ℝ) ≤ 2*M ∧ M < q.2 ∧ (q.2:ℝ) ≤ 2*M)
    (W : Finset ℝ) (hW : ∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T))
    (hsep : ∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) :
    (∑ q ∈ Q, ‖∑ t ∈ W, phase (pairRatio q) t‖^2) ≤
      128*(16*Real.pi*M^2+8*Real.pi*T)*(W.card:ℝ) := by
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
  have hh := sampled_character_second hT hδ W hW hsep x hx hs
  have he (q : Q) : ‖centeredCharacter W t₀ (x q)‖=‖∑ t ∈ W, phase (pairRatio q) t‖ := by
    dsimp only [x]
    rw [centered_character_norm]
    simp only [pairRatio,Rat.cast_div,Rat.cast_natCast]
  simp only [he] at hh
  rw [Finset.sum_coe_sort Q (fun q => ‖∑ t ∈ W, phase (pairRatio q) t‖^2)] at hh
  have hd : δ⁻¹=16*Real.pi*M^2 := by dsimp [δ]; rw [inv_div,div_one]
  simpa only [hd] using hh


theorem dyadic_pair_card_le_four_sq {M : ℝ} (hM : 0 ≤ M)
    (Q : Finset (ℕ × ℕ))
    (hQ : ∀ q ∈ Q, 0 < q.1 ∧ 0 < q.2 ∧ (q.1 : ℝ) ≤ 2 * M ∧ (q.2 : ℝ) ≤ 2 * M) :
    (Q.card : ℝ) ≤ 4 * M ^ 2 := by
  have hSub : Q ⊆ (Icc 1 ⌊2 * M⌋₊) ×ˢ (Icc 1 ⌊2 * M⌋₊) := by
    intro q hq
    obtain ⟨h1, h2, hu1, hu2⟩ := hQ q hq
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨h1, (Nat.le_floor_iff (by positivity : 0 ≤ 2 * M)).mpr hu1⟩,
        Finset.mem_Icc.mpr ⟨h2, (Nat.le_floor_iff (by positivity : 0 ≤ 2 * M)).mpr hu2⟩⟩
  have hCard : Q.card ≤ ⌊2 * M⌋₊ ^ 2 := by
    simpa only [Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel, pow_two] using
      Finset.card_le_card hSub
  have hReal : (Q.card : ℝ) ≤ (⌊2 * M⌋₊ : ℝ) ^ 2 := by exact_mod_cast hCard
  have hFloor := Nat.floor_le (show 0 ≤ 2 * M by positivity)
  have hSq := pow_le_pow_left₀ (Nat.cast_nonneg ⌊2 * M⌋₊) hFloor 2
  nlinarith

/-- Short reduced second moment obtained from the actual fourth energy
and finite Cauchy, without separation of the original ordinate set. -/
theorem coprime_short_second_energy {T t₀ M : ℝ} (hT : 1 < T) (hM : 0 < M)
    (hMT : M ^ 2 ≤ T) (Q : Finset (ℕ × ℕ))
    (hQ : ∀ q ∈ Q, 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2 ∧
      M < q.1 ∧ (q.1 : ℝ) ≤ 2 * M ∧ M < q.2 ∧ (q.2 : ℝ) ≤ 2 * M)
    (W : Finset ℝ) (hW : ∀ t ∈ W, t ∈ Set.Icc t₀ (t₀ + T)) :
    (∑ q ∈ Q, ‖∑ t ∈ W, phase (pairRatio q) t‖ ^ 2) ≤
      (2 * Real.sqrt (28672 * Real.pi)) * M *
        Real.sqrt (T * (discreteAdditiveEnergy W : ℝ)) := by
  let f : ℕ × ℕ → ℝ := fun q => ‖∑ t ∈ W, phase (pairRatio q) t‖
  have hCard := dyadic_pair_card_le_four_sq hM.le Q (by
    intro q hq
    obtain ⟨h1, h2, hcop, hl1, hu1, hl2, hu2⟩ := hQ q hq
    exact ⟨h1, h2, hu1, hu2⟩)
  have hFourth := coprime_short_fourth_energy hT hM hMT Q hQ W hW
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Q (fun q => f q ^ 2) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hCS
  have hFour : (∑ q ∈ Q, (f q ^ 2) ^ 2) = ∑ q ∈ Q, f q ^ 4 := by
    apply Finset.sum_congr rfl
    intro q hq
    ring
  rw [hFour] at hCS
  have hProduct : (∑ q ∈ Q, f q ^ 4) * (Q.card : ℝ) ≤
      ((28672 * Real.pi) * T * (discreteAdditiveEnergy W : ℝ)) * (4 * M ^ 2) := by
    exact mul_le_mul hFourth hCard (Nat.cast_nonneg Q.card) (by positivity)
  have hSq : ((2 * Real.sqrt (28672 * Real.pi)) * M *
      Real.sqrt (T * (discreteAdditiveEnergy W : ℝ))) ^ 2 =
        ((28672 * Real.pi) * T * (discreteAdditiveEnergy W : ℝ)) * (4 * M ^ 2) := by
    simp only [mul_pow]
    rw [Real.sq_sqrt (by positivity : 0 ≤ 28672 * Real.pi),
      Real.sq_sqrt (by positivity : 0 ≤ T * (discreteAdditiveEnergy W : ℝ))]
    ring
  have hBound := hCS.trans (hProduct.trans_eq hSq.symm)
  have hLeft : 0 ≤ ∑ q ∈ Q, f q ^ 2 := Finset.sum_nonneg fun q hq => sq_nonneg _
  have hRight : 0 ≤ (2 * Real.sqrt (28672 * Real.pi)) * M *
      Real.sqrt (T * (discreteAdditiveEnergy W : ℝ)) := by positivity
  change (∑ q ∈ Q, f q ^ 2) ≤ _
  nlinarith

end Montgomery.RationalMoment
