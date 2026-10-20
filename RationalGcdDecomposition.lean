module
public import RationalMomentDuality
public import Mathlib

@[expose] public section

/-! Exact gcd decomposition, including multiplicities. No analytic estimate is
assumed in the identities. The final bound states its reduced-pair input explicitly. -/
set_option autoImplicit false
noncomputable section
open Finset

namespace Montgomery.RationalMoment

def pairGcd (p : ℕ × ℕ) : ℕ := p.1.gcd p.2
def reducePair (p : ℕ × ℕ) : ℕ × ℕ := (p.1 / pairGcd p, p.2 / pairGcd p)
def pairRatio (p : ℕ × ℕ) : ℚ := (p.1 : ℚ) / p.2
def gcdValues (P : Finset (ℕ × ℕ)) : Finset ℕ := P.image pairGcd
def gcdFiber (P : Finset (ℕ × ℕ)) (d : ℕ) : Finset (ℕ × ℕ) :=
  P.filter (fun p => pairGcd p = d)
def reducedFiber (P : Finset (ℕ × ℕ)) (d : ℕ) : Finset (ℕ × ℕ) :=
  (gcdFiber P d).image reducePair

theorem reduce_reconstruct (p : ℕ × ℕ) :
    (reducePair p).1 * pairGcd p = p.1 ∧
    (reducePair p).2 * pairGcd p = p.2 :=
  ⟨Nat.div_mul_cancel (Nat.gcd_dvd_left _ _),
    Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)⟩

theorem reduce_positive_coprime {p : ℕ × ℕ} (hp : 0 < p.1 ∧ 0 < p.2) :
    0 < (reducePair p).1 ∧ 0 < (reducePair p).2 ∧
      Nat.Coprime (reducePair p).1 (reducePair p).2 := by
  refine ⟨Nat.div_gcd_pos_of_pos_left _ hp.1, ?_, ?_⟩
  · simpa [reducePair, pairGcd, Nat.gcd_comm] using Nat.div_gcd_pos_of_pos_left p.1 hp.2
  · exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left _ hp.1)

theorem reduce_ratio {p : ℕ × ℕ} (hp : 0 < p.1) :
    pairRatio (reducePair p) = pairRatio p := by
  have hd : (pairGcd p : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_left p.2 hp).ne'
  obtain ⟨ha, hb⟩ := reduce_reconstruct p
  have ha' : ((reducePair p).1 : ℚ) * pairGcd p = p.1 := by exact_mod_cast ha
  have hb' : ((reducePair p).2 : ℚ) * pairGcd p = p.2 := by exact_mod_cast hb
  unfold pairRatio
  rw [← ha', ← hb', mul_div_mul_right _ _ hd]

/-- Positive reduced pairs give distinct rational frequencies. -/
theorem pair_ratio_injective {p q : ℕ × ℕ}
    (hp : 0 < p.2) (hq : 0 < q.2)
    (hcp : Nat.Coprime p.1 p.2) (hcq : Nat.Coprime q.1 q.2)
    (he : pairRatio p = pairRatio q) : p = q := by
  have hh := Rat.div_int_inj (a := (p.1 : ℤ)) (b := (p.2 : ℤ))
    (c := (q.1 : ℤ)) (d := (q.2 : ℤ)) (by exact_mod_cast hp)
    (by exact_mod_cast hq) (by simpa using hcp) (by simpa using hcq)
    (by simpa [pairRatio] using he)
  exact Prod.ext (by exact_mod_cast hh.1) (by exact_mod_cast hh.2)

theorem reduced_energy_eq_rational_energy (Q : Finset (ℕ × ℕ))
    (hQ : ∀ p ∈ Q, 0 < p.2 ∧ Nat.Coprime p.1 p.2) (W : Finset ℝ) :
    (∑ p ∈ Q, ‖∑ t ∈ W, phase (pairRatio p) t‖ ^ 2) =
      rationalEnergy (Q.image pairRatio) W := by
  unfold rationalEnergy
  rw [sum_image]
  intro p hp q hq he
  exact pair_ratio_injective (hQ p hp).1 (hQ q hq).1 (hQ p hp).2 (hQ q hq).2 he

/-- The rational-frequency moment premise applies to a coprime pair set
without losing multiplicity, because the preceding injectivity is proved. -/
theorem coprime_pair_energy_pow_le (Q : Finset (ℕ × ℕ))
    (hQ : ∀ p ∈ Q, 0 < p.2 ∧ Nat.Coprime p.1 p.2) (W : Finset ℝ)
    {k : ℕ} (hk : 1 ≤ k) {B : ℝ} (hB : 0 ≤ B)
    (hmoment : ∀ c : ℚ → ℂ,
      (∑ t ∈ W, ‖∑ r ∈ Q.image pairRatio, c r * phase r t‖ ^ (2 * k)) ≤
        B * (∑ r ∈ Q.image pairRatio, ‖c r‖ ^ 2) ^ k) :
    (∑ p ∈ Q, ‖∑ t ∈ W, phase (pairRatio p) t‖ ^ 2) ^ k ≤
      (W.card : ℝ) ^ (2 * k - 1) * B := by
  rw [reduced_energy_eq_rational_energy Q hQ W]
  exact rational_energy_pow_le _ W hk hB hmoment

/-- Reduction is injective within a fixed gcd class, not on all pairs. -/
theorem reduce_injective_on_fiber (P : Finset (ℕ × ℕ)) (d : ℕ) :
    Set.InjOn reducePair (gcdFiber P d) := by
  intro p hp q hq he
  have hp' := (mem_filter.mp hp).2
  have hq' := (mem_filter.mp hq).2
  obtain ⟨ha, hb⟩ := reduce_reconstruct p
  obtain ⟨hc, hd⟩ := reduce_reconstruct q
  rw [hp'] at ha hb
  rw [hq'] at hc hd
  rw [he] at ha hb
  exact Prod.ext (ha.symm.trans hc) (hb.symm.trans hd)

/-- Exact regrouping of an arbitrary function of the rational number.
Repeated fractions in different gcd classes retain their multiplicity. -/
theorem sum_by_gcd (P : Finset (ℕ × ℕ))
    (hP : ∀ p ∈ P, 0 < p.1) (f : ℚ → ℝ) :
    (∑ p ∈ P, f (pairRatio p)) =
      ∑ d ∈ gcdValues P, ∑ q ∈ reducedFiber P d, f (pairRatio q) := by
  have hf := Finset.sum_fiberwise_of_maps_to
    (show ∀ p ∈ P, pairGcd p ∈ gcdValues P from
      fun p hp => mem_image.mpr ⟨p, hp, rfl⟩) (fun p => f (pairRatio p))
  rw [← hf]
  apply sum_congr rfl
  intro d _
  rw [reducedFiber, sum_image (reduce_injective_on_fiber P d)]
  apply sum_congr rfl
  intro p hp
  rw [reduce_ratio (hP p (mem_filter.mp hp).1)]

theorem reduced_fiber_bounds {P : Finset (ℕ × ℕ)} {M : ℝ}
    (hP : ∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
      M < p.1 ∧ (p.1 : ℝ) ≤ 2 * M ∧ M < p.2 ∧ (p.2 : ℝ) ≤ 2 * M)
    {d : ℕ} {q : ℕ × ℕ} (hq : q ∈ reducedFiber P d) :
    0 < d ∧ 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2 ∧
      M / d < q.1 ∧ (q.1 : ℝ) ≤ 2 * (M / d) ∧
      M / d < q.2 ∧ (q.2 : ℝ) ≤ 2 * (M / d) := by
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
  obtain ⟨hp, hd⟩ := mem_filter.mp hp
  obtain ⟨ha, hb, hma, ham, hmb, hbm⟩ := hP p hp
  have hdpos : 0 < d := hd ▸ Nat.gcd_pos_of_pos_left p.2 ha
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hdpos
  obtain ⟨hqa, hqb, hc⟩ := reduce_positive_coprime ⟨ha, hb⟩
  obtain ⟨he, hf⟩ := reduce_reconstruct p
  rw [hd] at he hf
  have he' : ((reducePair p).1 : ℝ) * d = p.1 := by exact_mod_cast he
  have hf' : ((reducePair p).2 : ℝ) * d = p.2 := by exact_mod_cast hf
  refine ⟨hdpos, hqa, hqb, hc, ?_, ?_, ?_, ?_⟩
  · exact (div_lt_iff₀ hdreal).mpr (by linarith)
  · rw [← mul_div_assoc]
    exact (le_div_iff₀ hdreal).mpr (by linarith)
  · exact (div_lt_iff₀ hdreal).mpr (by linarith)
  · rw [← mul_div_assoc]
    exact (le_div_iff₀ hdreal).mpr (by linarith)

/-- Actual sums of squared rational phase sums, with exact gcd multiplicities. -/
theorem pair_energy_by_gcd (P : Finset (ℕ × ℕ))
    (hP : ∀ p ∈ P, 0 < p.1) (W : Finset ℝ) :
    (∑ p ∈ P, ‖∑ t ∈ W, phase (pairRatio p) t‖ ^ 2) =
      ∑ d ∈ gcdValues P,
        ∑ q ∈ reducedFiber P d, ‖∑ t ∈ W, phase (pairRatio q) t‖ ^ 2 :=
  sum_by_gcd P hP (fun r => ‖∑ t ∈ W, phase r t‖ ^ 2)

/-- A height-linear estimate for each reduced class gives the exact harmonic
gcd loss. The premise is a reduced-pair estimate, explicitly left open here. -/
theorem pair_energy_le_harmonic (P : Finset (ℕ × ℕ))
    (hP : ∀ p ∈ P, 0 < p.1) (W : Finset ℝ) {B M : ℝ}
    (hblock : ∀ d ∈ gcdValues P,
      (∑ q ∈ reducedFiber P d, ‖∑ t ∈ W, phase (pairRatio q) t‖ ^ 2) ≤ B * (M / d)) :
    (∑ p ∈ P, ‖∑ t ∈ W, phase (pairRatio p) t‖ ^ 2) ≤
      B * M * ∑ d ∈ gcdValues P, (d : ℝ)⁻¹ := by
  rw [pair_energy_by_gcd P hP W, mul_sum]
  apply sum_le_sum
  intro d hd
  simpa [div_eq_mul_inv, mul_assoc] using hblock d hd

/-- The full gcd sum has a logarithmic cost, including the fraction one.
This is conditional only on the displayed bound for each reduced class. -/
theorem pair_energy_le_log (P : Finset (ℕ × ℕ)) {N : ℕ}
    (hP : ∀ p ∈ P, 0 < p.1 ∧ p.1 ≤ N) (W : Finset ℝ)
    {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hblock : ∀ d ∈ gcdValues P,
      (∑ q ∈ reducedFiber P d, ‖∑ t ∈ W, phase (pairRatio q) t‖ ^ 2) ≤ B * (M / d)) :
    (∑ p ∈ P, ‖∑ t ∈ W, phase (pairRatio p) t‖ ^ 2) ≤
      B * M * (1 + Real.log N) := by
  have hsub : gcdValues P ⊆ Finset.Icc 1 N := by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hd
    exact mem_Icc.mpr ⟨Nat.gcd_pos_of_pos_left _ (hP p hp).1,
      (Nat.gcd_le_left _ (hP p hp).1).trans (hP p hp).2⟩
  have hsum : (∑ d ∈ gcdValues P, (d : ℝ)⁻¹) ≤ 1 + Real.log N := by
    calc
      _ ≤ ∑ d ∈ Finset.Icc 1 N, (d : ℝ)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => by positivity)
      _ ≤ _ := by
        simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
          using harmonic_le_one_add_log N
  exact (pair_energy_le_harmonic P (fun p hp => (hP p hp).1) W hblock).trans
    (mul_le_mul_of_nonneg_left hsum (mul_nonneg hB hM))

end Montgomery.RationalMoment

#print axioms Montgomery.RationalMoment.sum_by_gcd
#print axioms Montgomery.RationalMoment.reduced_fiber_bounds
#print axioms Montgomery.RationalMoment.pair_energy_le_harmonic
#print axioms Montgomery.RationalMoment.coprime_pair_energy_pow_le
#print axioms Montgomery.RationalMoment.pair_energy_le_log
