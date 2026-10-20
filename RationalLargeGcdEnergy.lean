module
public import RationalDyadicDifference

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment

theorem rational_phase_sum_norm_le_card (r : ℚ) (W : Finset ℝ) :
    ‖∑ t ∈ W, phase r t‖ ≤ W.card := by
  have hp (t : ℝ) : ‖phase r t‖ = 1 := by
    rw [← exponentialPhase_log, exponentialPhase_norm]
  exact (norm_sum_le _ _).trans_eq (by simp only [hp, sum_const, nsmul_eq_mul, mul_one])

/-- The second-moment estimate for only the large-gcd part of a longer
dyadic interval. The short-range condition is imposed on X/D, not X. -/
theorem large_gcd_pair_energy {K : ℕ} (hK : 1 ≤ K)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t₀ X D : ℝ), 1 < T → 0 ≤ X → X ≤ T → 0 < D →
      ∀ (P : Finset (ℕ × ℕ)),
      (∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
        X < p.1 ∧ (p.1 : ℝ) ≤ 2*X ∧ X < p.2 ∧ (p.2 : ℝ) ≤ 2*X ∧
        D ≤ pairGcd p) →
      ∀ (W : Finset ℝ),
      T^(((K : ℝ)+1)/(2*K+1)) ≤ W.card → (X/D)^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∑ p ∈ P, ‖∑ t ∈ W, phase (pairRatio p) t‖^2) ≤
        C*T^η*X*(W.card : ℝ)^2 := by
  obtain ⟨C, hC, hbound⟩ := coprime_dyadic_short_range hK (show 0 < η/2 by positivity)
  let L : ℝ := 1+4^(η/2)/(η/2)
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨C*L, by positivity, ?_⟩
  intro T t₀ X D hT hX hXT hD P hP W hR hXR hW hsep
  have hgeom : ∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
      X < p.1 ∧ (p.1 : ℝ) ≤ 2*X ∧ X < p.2 ∧ (p.2 : ℝ) ≤ 2*X := by
    intro p hp
    obtain ⟨h1,h2,hl1,hu1,hl2,hu2,_⟩ := hP p hp
    exact ⟨h1,h2,hl1,hu1,hl2,hu2⟩
  have hblock : ∀ d ∈ gcdValues P,
      (∑ q ∈ reducedFiber P d, ‖∑ t ∈ W, phase (pairRatio q) t‖^2) ≤
        (C*T^(η/2)*(W.card : ℝ)^2)*(X/d) := by
    intro d hd
    obtain ⟨p, hp, he⟩ := mem_image.mp hd
    have hdD : D ≤ (d : ℝ) := he ▸ (hP p hp).2.2.2.2.2.2
    have hdiv : X/(d : ℝ) ≤ X/D := div_le_div_of_nonneg_left hX hD hdD
    have hQ : ∀ q ∈ reducedFiber P d,
        0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2 ∧
        X/d < q.1 ∧ (q.1 : ℝ) ≤ 2*(X/d) ∧
        X/d < q.2 ∧ (q.2 : ℝ) ≤ 2*(X/d) := by
      intro q hq
      exact (reduced_fiber_bounds hgeom hq).2
    have hh := hbound T t₀ (X/d) hT (by positivity) (reducedFiber P d) hQ W hR
      ((pow_le_pow_left₀ (by positivity) hdiv K).trans hXR) hW hsep
    convert hh using 1
    ring
  have h2X : 0 ≤ 2*X := by positivity
  have hpN : ∀ p ∈ P, 0 < p.1 ∧ p.1 ≤ ⌊2*X⌋₊ := by
    intro p hp
    exact ⟨(hP p hp).1, (Nat.le_floor_iff h2X).mpr (hP p hp).2.2.2.1⟩
  have hh := pair_energy_le_log P hpN W
    (show 0 ≤ C*T^(η/2)*(W.card : ℝ)^2 by positivity) hX hblock
  have hN : (⌊2*X⌋₊ : ℝ) ≤ 4*T := (Nat.floor_le h2X).trans (by linarith)
  have hl := logarithmic_height_loss hT.le (show 0 < η/2 by positivity) ⌊2*X⌋₊ hN
  change 1+Real.log ⌊2*X⌋₊ ≤ L*T^(η/2) at hl
  have hp : T^(η/2)*T^(η/2) = T^η := by
    rw [← Real.rpow_add (by linarith : 0 < T)]
    congr 1
    ring
  calc
    _ ≤ (C*T^(η/2)*(W.card : ℝ)^2)*X*(1+Real.log ⌊2*X⌋₊) := hh
    _ ≤ (C*T^(η/2)*(W.card : ℝ)^2)*X*(L*T^(η/2)) := by gcongr
    _ = C*L*(T^(η/2)*T^(η/2))*X*(W.card : ℝ)^2 := by ring
    _ = _ := by rw [hp]

/-- The large-gcd cubic contribution used in the proposed two-term additive
energy argument is bounded without any unproved analytic input. -/
theorem large_gcd_cubic_energy {K : ℕ} (hK : 1 ≤ K)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t₀ X D : ℝ), 1 < T → 0 ≤ X → X ≤ T → 0 < D →
      ∀ (P : Finset (ℕ × ℕ)),
      (∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
        X < p.1 ∧ (p.1 : ℝ) ≤ 2*X ∧ X < p.2 ∧ (p.2 : ℝ) ≤ 2*X ∧
        D ≤ pairGcd p) →
      ∀ (W : Finset ℝ),
      T^(((K : ℝ)+1)/(2*K+1)) ≤ W.card → (X/D)^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∑ p ∈ P, ‖∑ t ∈ W, phase (pairRatio p) t‖^3) ≤
        C*T^η*X*(W.card : ℝ)^3 := by
  obtain ⟨C, hC, hbound⟩ := large_gcd_pair_energy hK hη
  refine ⟨C, hC, ?_⟩
  intro T t₀ X D hT hX hXT hD P hP W hR hXR hW hsep
  have hh := hbound T t₀ X D hT hX hXT hD P hP W hR hXR hW hsep
  calc
    _ ≤ ∑ p ∈ P, (W.card : ℝ)*‖∑ t ∈ W, phase (pairRatio p) t‖^2 := by
      apply sum_le_sum
      intro p _
      have hn := rational_phase_sum_norm_le_card (pairRatio p) W
      nlinarith [mul_le_mul_of_nonneg_right hn (sq_nonneg ‖∑ t ∈ W, phase (pairRatio p) t‖)]
    _ = (W.card : ℝ)*(∑ p ∈ P, ‖∑ t ∈ W, phase (pairRatio p) t‖^2) := by rw [mul_sum]
    _ ≤ (W.card : ℝ)*(C*T^η*X*(W.card : ℝ)^2) := by gcongr
    _ = _ := by ring

/-- The large-gcd half of the proposed additive-energy split, at the
actual cutoff D=X^2/T. This does not assert the still-open low-gcd or
reproducing-kernel bounds for the discrete additive energy. -/
theorem large_gcd_cubic_at_transition {K : ℕ} (hK : 1 ≤ K)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t₀ X : ℝ), 1 < T → 0 < X → X ≤ T →
      ∀ (P : Finset (ℕ × ℕ)),
      (∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
        X < p.1 ∧ (p.1 : ℝ) ≤ 2*X ∧ X < p.2 ∧ (p.2 : ℝ) ≤ 2*X) →
      ∀ (W : Finset ℝ),
      T^(((K : ℝ)+1)/(2*K+1)) ≤ W.card → (T/X)^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∑ p ∈ P.filter (fun p => X^2/T ≤ (pairGcd p : ℝ)),
        ‖∑ t ∈ W, phase (pairRatio p) t‖^3) ≤ C*T^η*X*(W.card : ℝ)^3 := by
  obtain ⟨C, hC, hbound⟩ := large_gcd_cubic_energy hK hη
  refine ⟨C, hC, ?_⟩
  intro T t₀ X hT hX hXT P hP W hR hXR hW hsep
  have hTp : 0 < T := by linarith
  have he : X/(X^2/T) = T/X := by field_simp
  apply hbound T t₀ X (X^2/T) hT hX.le hXT (by positivity) _ _ W hR
    (by rw [he]; exact hXR) hW hsep
  intro p hp
  obtain ⟨hp, hd⟩ := mem_filter.mp hp
  obtain ⟨h1,h2,hl1,hu1,hl2,hu2⟩ := hP p hp
  exact ⟨h1,h2,hl1,hu1,hl2,hu2,hd⟩

end Montgomery.RationalMoment
