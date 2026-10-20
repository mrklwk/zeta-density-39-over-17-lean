module
public import RationalDyadicShortRange
public import RationalDifferenceEnergy

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment

/-- The gcd-class hypothesis in the previous assembly is now discharged
by the proved rational moment theorem, with the full logarithmic loss. -/
theorem dyadic_pair_energy_log {K : ℕ} (hK : 1 ≤ K)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t₀ M : ℝ), 1 < T → 0 ≤ M →
      ∀ (N : ℕ) (P : Finset (ℕ × ℕ)),
      (∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧ p.1 ≤ N ∧
        M < p.1 ∧ (p.1 : ℝ) ≤ 2*M ∧ M < p.2 ∧ (p.2 : ℝ) ≤ 2*M) →
      ∀ (W : Finset ℝ),
      T^(((K : ℝ)+1)/(2*K+1)) ≤ W.card → M^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∑ p ∈ P, ‖∑ t ∈ W, phase (pairRatio p) t‖^2) ≤
        C*T^η*M*(W.card : ℝ)^2*(1+Real.log N) := by
  obtain ⟨C, hC, hbound⟩ := coprime_dyadic_short_range hK hη
  refine ⟨C, hC, ?_⟩
  intro T t₀ M hT hM N P hP W hR hMR hW hsep
  have hgeom : ∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
      M < p.1 ∧ (p.1 : ℝ) ≤ 2*M ∧ M < p.2 ∧ (p.2 : ℝ) ≤ 2*M := by
    intro p hp
    exact ⟨(hP p hp).1, (hP p hp).2.1, (hP p hp).2.2.2⟩
  have hblock : ∀ d ∈ gcdValues P,
      (∑ q ∈ reducedFiber P d, ‖∑ t ∈ W, phase (pairRatio q) t‖^2) ≤
        (C*T^η*(W.card : ℝ)^2)*(M/d) := by
    intro d hd
    obtain ⟨p, hp, he⟩ := mem_image.mp hd
    have hdpos : 0 < d := he ▸ Nat.gcd_pos_of_pos_left p.2 (hP p hp).1
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
    have hdiv : M/(d : ℝ) ≤ M := div_le_self hM hd1
    have hQ : ∀ q ∈ reducedFiber P d,
        0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2 ∧
        M/d < q.1 ∧ (q.1 : ℝ) ≤ 2*(M/d) ∧
        M/d < q.2 ∧ (q.2 : ℝ) ≤ 2*(M/d) := by
      intro q hq
      exact (reduced_fiber_bounds hgeom hq).2
    have hh := hbound T t₀ (M/d) hT (by positivity) (reducedFiber P d) hQ W hR
      ((pow_le_pow_left₀ (by positivity) hdiv K).trans hMR)
      hW hsep
    convert hh using 1
    ring
  have hh := pair_energy_le_log P
    (fun p hp => ⟨(hP p hp).1, (hP p hp).2.2.1⟩) W
    (show 0 ≤ C*T^η*(W.card : ℝ)^2 by positivity) hM hblock
  convert hh using 1
  ring

/-- An unconditional estimate for the actual Dirichlet difference sum,
for arbitrary coefficients of modulus at most one in a real dyadic interval. -/
theorem dyadic_dirichlet_difference_log {K : ℕ} (hK : 1 ≤ K)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t₀ M : ℝ), 1 < T → 0 ≤ M →
      ∀ (N : ℕ) (A : Finset ℕ),
      (∀ n ∈ A, 0 < n ∧ n ≤ N ∧ M < n ∧ (n : ℝ) ≤ 2*M) →
      ∀ (W : Finset ℝ),
      T^(((K : ℝ)+1)/(2*K+1)) ≤ W.card → M^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      ∀ (a : ℕ → ℂ), (∀ n ∈ A, ‖a n‖ ≤ 1) →
      (∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ A, a n * phase n (t-u)‖^2) ≤
        C*T^η*M*(W.card : ℝ)^2*(1+Real.log N) := by
  obtain ⟨C, hC, hbound⟩ := dyadic_pair_energy_log hK hη
  refine ⟨C, hC, ?_⟩
  intro T t₀ M hT hM N A hA W hR hMR hW hsep a ha
  have hP : ∀ p ∈ A ×ˢ A, 0 < p.1 ∧ 0 < p.2 ∧ p.1 ≤ N ∧
      M < p.1 ∧ (p.1 : ℝ) ≤ 2*M ∧ M < p.2 ∧ (p.2 : ℝ) ≤ 2*M := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := mem_product.mp hp
    exact ⟨(hA p.1 hp1).1, (hA p.2 hp2).1, (hA p.1 hp1).2.1,
      (hA p.1 hp1).2.2.1, (hA p.1 hp1).2.2.2, (hA p.2 hp2).2.2⟩
  have hh := hbound T t₀ M hT hM N (A ×ˢ A) hP W hR hMR hW hsep
  simp only [sum_product, pairRatio, Rat.cast_div, Rat.cast_natCast] at hh
  exact (dirichlet_difference_energy_le A (fun n hn => (hA n hn).1) W a ha).trans hh

theorem short_length_le_twice_time {K : ℕ} (hK : 1 ≤ K)
    {T t₀ M : ℝ} (hT : 1 < T) (W : Finset ℝ)
    (hMR : M^K ≤ W.card)
    (hW : ∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T))
    (hsep : ∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) : M ≤ 2*T := by
  by_cases hm : M ≤ 1
  · linarith
  · have hpow : M ≤ M^K := by
      simpa only [pow_one] using pow_le_pow_right₀ (le_of_lt (lt_of_not_ge hm)) hK
    have hp := separated_interval_card (by linarith : 0 ≤ T) W hW hsep
    linarith

theorem logarithmic_height_loss {T δ : ℝ} (hT : 1 ≤ T) (hδ : 0 < δ)
    (N : ℕ) (hN : (N : ℝ) ≤ 4*T) :
    1+Real.log N ≤ (1+4^δ/δ)*T^δ := by
  have hTp : 0 < T := by linarith
  have hpow : 1 ≤ T^δ := Real.one_le_rpow hT hδ.le
  have hlog : Real.log N ≤ (4^δ*T^δ)/δ := by
    calc
      _ ≤ (N : ℝ)^δ/δ := Real.log_natCast_le_rpow_div N hδ
      _ ≤ (4*T)^δ/δ := by
        apply div_le_div_of_nonneg_right _ hδ.le
        exact Real.rpow_le_rpow (Nat.cast_nonneg _) hN hδ.le
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hTp.le]
  calc
    _ ≤ T^δ+(4^δ*T^δ)/δ := add_le_add hpow hlog
    _ = _ := by ring

/-- Full all-pairs short-range rational estimate. Gcd multiplicities,
real lengths, fixed height factors and the logarithmic loss are all discharged. -/
theorem dyadic_pair_energy {K : ℕ} (hK : 1 ≤ K)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t₀ M : ℝ), 1 < T → 0 ≤ M →
      ∀ (P : Finset (ℕ × ℕ)),
      (∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
        M < p.1 ∧ (p.1 : ℝ) ≤ 2*M ∧ M < p.2 ∧ (p.2 : ℝ) ≤ 2*M) →
      ∀ (W : Finset ℝ),
      T^(((K : ℝ)+1)/(2*K+1)) ≤ W.card → M^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∑ p ∈ P, ‖∑ t ∈ W, phase (pairRatio p) t‖^2) ≤
        C*T^η*M*(W.card : ℝ)^2 := by
  obtain ⟨C, hC, hbound⟩ := dyadic_pair_energy_log hK (show 0 < η/2 by positivity)
  let L : ℝ := 1+4^(η/2)/(η/2)
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨C*L, by positivity, ?_⟩
  intro T t₀ M hT hM P hP W hR hMR hW hsep
  have h2M : 0 ≤ 2*M := by positivity
  have hP' : ∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧ p.1 ≤ ⌊2*M⌋₊ ∧
      M < p.1 ∧ (p.1 : ℝ) ≤ 2*M ∧ M < p.2 ∧ (p.2 : ℝ) ≤ 2*M := by
    intro p hp
    exact ⟨(hP p hp).1, (hP p hp).2.1,
      (Nat.le_floor_iff h2M).mpr (hP p hp).2.2.2.1, (hP p hp).2.2⟩
  have hMT := short_length_le_twice_time hK hT W hMR hW hsep
  have hN : (⌊2*M⌋₊ : ℝ) ≤ 4*T := (Nat.floor_le h2M).trans (by linarith)
  have hl := logarithmic_height_loss hT.le (show 0 < η/2 by positivity) ⌊2*M⌋₊ hN
  change 1+Real.log ⌊2*M⌋₊ ≤ L*T^(η/2) at hl
  have hh := hbound T t₀ M hT hM ⌊2*M⌋₊ P hP' W hR hMR hW hsep
  have hp : T^(η/2)*T^(η/2) = T^η := by
    rw [← Real.rpow_add (by linarith : 0 < T)]
    congr 1
    ring
  calc
    _ ≤ C*T^(η/2)*M*(W.card : ℝ)^2*(1+Real.log ⌊2*M⌋₊) := hh
    _ ≤ C*T^(η/2)*M*(W.card : ℝ)^2*(L*T^(η/2)) := by gcongr
    _ = C*L*(T^(η/2)*T^(η/2))*M*(W.card : ℝ)^2 := by ring
    _ = _ := by rw [hp]

/-- The completed short-range Dirichlet difference estimate, with no
unproved moment or reduced-class bound among its hypotheses. -/
theorem dyadic_dirichlet_difference {K : ℕ} (hK : 1 ≤ K)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t₀ M : ℝ), 1 < T → 0 ≤ M →
      ∀ (A : Finset ℕ),
      (∀ n ∈ A, 0 < n ∧ M < n ∧ (n : ℝ) ≤ 2*M) →
      ∀ (W : Finset ℝ),
      T^(((K : ℝ)+1)/(2*K+1)) ≤ W.card → M^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      ∀ (a : ℕ → ℂ), (∀ n ∈ A, ‖a n‖ ≤ 1) →
      (∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ A, a n * phase n (t-u)‖^2) ≤
        C*T^η*M*(W.card : ℝ)^2 := by
  obtain ⟨C, hC, hbound⟩ := dyadic_pair_energy hK hη
  refine ⟨C, hC, ?_⟩
  intro T t₀ M hT hM A hA W hR hMR hW hsep a ha
  have hP : ∀ p ∈ A ×ˢ A, 0 < p.1 ∧ 0 < p.2 ∧
      M < p.1 ∧ (p.1 : ℝ) ≤ 2*M ∧ M < p.2 ∧ (p.2 : ℝ) ≤ 2*M := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := mem_product.mp hp
    exact ⟨(hA p.1 hp1).1, (hA p.2 hp2).1, (hA p.1 hp1).2.1,
      (hA p.1 hp1).2.2, (hA p.2 hp2).2⟩
  have hh := hbound T t₀ M hT hM (A ×ˢ A) hP W hR hMR hW hsep
  simp only [sum_product, pairRatio, Rat.cast_div, Rat.cast_natCast] at hh
  exact (dirichlet_difference_energy_le A (fun n hn => (hA n hn).1) W a ha).trans hh

end Montgomery.RationalMoment
