module
public import RationalDilatedHeight
public import MathCollab.Density.Packing

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment

theorem separated_interval_card {T t₀ : ℝ} (hT : 0 ≤ T)
    (W : Finset ℝ) (hloc : ∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T))
    (hsep : ∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) :
    (W.card : ℝ) ≤ T+1 := by
  have hspan := MathCollab.Density.intervalSpan_le_of_forall hT (U := W) (by
    intro t ht u hu
    have ht' := hloc t ht
    have hu' := hloc u hu
    exact abs_le.mpr ⟨by linarith [ht'.1, hu'.2], by linarith [hu'.1, ht'.2]⟩)
  have hc := MathCollab.Density.separated_card_le_localDiameter hsep
  dsimp [MathCollab.Density.localDiameter] at hc
  linarith

/-- Short-range rational energy for any one-separated set in a length-T
interval. In particular, no artificial cardinality restriction R<=T is needed. -/
theorem rational_energy_interval_short_range {K : ℕ} (hK : 1 ≤ K)
    {η B : ℝ} (hη : 0 < η) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t₀ M : ℝ), 1 < T → 0 ≤ M →
      ∀ (A : Finset ℚ),
      (∀ q ∈ A, 0 < q ∧ (q.den : ℝ) ≤ B*M ∧ |Real.log (q : ℝ)| ≤ 1) →
      ∀ (W : Finset ℝ), T^(((K : ℝ)+1)/(2*K+1)) ≤ W.card →
      M^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      rationalEnergy A W ≤ C*T^η*M*(W.card : ℝ)^2 := by
  obtain ⟨C, hC, hbound⟩ := rational_energy_dilated_short_range hK hη hB
  refine ⟨C*2^η, by positivity, ?_⟩
  intro T t₀ M hT hM A hA W hR hMR hW hsep
  let U := max T (W.card : ℝ)
  have hTU : T ≤ U := le_max_left _ _
  have hRU : (W.card : ℝ) ≤ U := le_max_right _ _
  have hU : 1 < U := hT.trans_le hTU
  have hUT : U ≤ 2*T := by
    have hp := separated_interval_card (by linarith : 0 ≤ T) W hW hsep
    exact max_le (by linarith) (by linarith)
  have hα : ((K : ℝ)+1)/(2*K+1) ≤ 1 := by
    have hk0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    apply (div_le_one (by positivity)).mpr
    linarith
  have hR' : U^(((K : ℝ)+1)/(2*K+1)) ≤ W.card := by
    by_cases hRT : (W.card : ℝ) ≤ T
    · simpa only [U, max_eq_left hRT] using hR
    · have hTR : T ≤ (W.card : ℝ) := le_of_lt (lt_of_not_ge hRT)
      rw [show U = (W.card : ℝ) from max_eq_right hTR]
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (hT.le.trans hTR) hα
  have hW' : ∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+U) := by
    intro t ht
    exact ⟨(hW t ht).1, (hW t ht).2.trans (by linarith)⟩
  have hh := hbound U t₀ M hU hM A hA W hRU hR' hMR hW' hsep
  have hp : U^η ≤ 2^η*T^η := by
    calc
      _ ≤ (2*T)^η := Real.rpow_le_rpow (by linarith) hUT hη.le
      _ = _ := Real.mul_rpow (by norm_num) (by linarith)
  calc
    _ ≤ C*U^η*M*(W.card : ℝ)^2 := hh
    _ ≤ C*(2^η*T^η)*M*(W.card : ℝ)^2 := by gcongr
    _ = _ := by ring

/-- Complete coprime dyadic second-moment estimate, with real lengths,
the intended M^K<=R range, and only the actual interval/separation assumptions. -/
theorem coprime_dyadic_short_range {K : ℕ} (hK : 1 ≤ K)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t₀ M : ℝ), 1 < T → 0 ≤ M →
      ∀ (Q : Finset (ℕ × ℕ)),
      (∀ q ∈ Q, 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2 ∧
        M < q.1 ∧ (q.1 : ℝ) ≤ 2*M ∧ M < q.2 ∧ (q.2 : ℝ) ≤ 2*M) →
      ∀ (W : Finset ℝ), T^(((K : ℝ)+1)/(2*K+1)) ≤ W.card →
      M^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∑ q ∈ Q, ‖∑ t ∈ W, phase (pairRatio q) t‖^2) ≤
        C*T^η*M*(W.card : ℝ)^2 := by
  obtain ⟨C, hC, hbound⟩ := rational_energy_interval_short_range hK hη (B := 2) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro T t₀ M hT hM Q hQ W hR hMR hW hsep
  rw [reduced_energy_eq_rational_energy Q (fun q hq => ⟨(hQ q hq).2.1, (hQ q hq).2.2.1⟩) W]
  apply hbound T t₀ M hT hM (Q.image pairRatio) _ W hR hMR hW hsep
  intro r hr
  obtain ⟨q, hq, rfl⟩ := mem_image.mp hr
  obtain ⟨h1, h2, hc, hl1, hu1, hl2, hu2⟩ := hQ q hq
  refine ⟨div_pos (by exact_mod_cast h1) (by exact_mod_cast h2), ?_,
    dyadic_pair_log h1 h2 hl1 hu1 hl2 hu2⟩
  rw [coprime_pair_den h2 hc]
  exact hu2

end Montgomery.RationalMoment
