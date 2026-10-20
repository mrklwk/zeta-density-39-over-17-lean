module
public import SeparatedFrequencyMeanValue
public import RationalFrequencySeparation

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment

def positiveRatPair (r : ℚ) : ℕ × ℕ := (r.num.natAbs, r.den)

theorem positiveRatPair_ratio {r : ℚ} (hr : 0 < r) : pairRatio (positiveRatPair r) = r := by
  have hn : (r.num.natAbs : ℤ) = r.num := by
    rw [Int.natCast_natAbs, abs_of_nonneg (Rat.num_nonneg.mpr hr.le)]
  have hn' : (r.num.natAbs : ℚ) = (r.num : ℚ) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) hn
  simp only [pairRatio, positiveRatPair, hn', Rat.num_div_den]

theorem positiveRatPair_properties {r : ℚ} (hr : 0 < r) :
    0 < (positiveRatPair r).1 ∧ 0 < (positiveRatPair r).2 ∧
      Nat.Coprime (positiveRatPair r).1 (positiveRatPair r).2 := by
  exact ⟨Int.natAbs_pos.mpr (Rat.num_pos.mpr hr).ne', r.pos, r.reduced⟩

theorem positive_rational_log_gap {r s : ℚ} (hr : 0 < r) (hs : 0 < s) (hne : r ≠ s)
    {H L : ℝ} (hrH : (r.den : ℝ) ≤ H) (hsH : (s.den : ℝ) ≤ H)
    (hrL : Real.log (r : ℝ) ≤ L) (hsL : Real.log (s : ℝ) ≤ L) :
    1 / (Real.exp L * H ^ 2) ≤ |Real.log (r : ℝ) - Real.log (s : ℝ)| := by
  have hpr := positiveRatPair_properties hr
  have hps := positiveRatPair_properties hs
  have hrepr (q : ℚ) (hq : 0 < q) :
      ((positiveRatPair q).1 : ℝ) / (positiveRatPair q).2 = q := by
    have hh := congrArg (fun x : ℚ => (x : ℝ)) (positiveRatPair_ratio hq)
    simpa [pairRatio] using hh
  have hu (q : ℚ) (hq : 0 < q) (hl : Real.log (q : ℝ) ≤ L) : (q : ℝ) ≤ Real.exp L := by
    simpa only [Real.exp_log (by exact_mod_cast hq : (0 : ℝ) < q)] using Real.exp_le_exp.mpr hl
  have hpq : positiveRatPair r ≠ positiveRatPair s := by
    intro he
    apply hne
    rw [← positiveRatPair_ratio hr, he, positiveRatPair_ratio hs]
  have hh := rational_log_separation (U := Real.exp L) hpr hps hpq hrH hsH
    (by rw [hrepr r hr]; exact hu r hr hrL)
    (by rw [hrepr s hs]; exact hu s hs hsL)
  simpa only [hrepr r hr, hrepr s hs] using hh

theorem exponentialPhase_log (r t : ℝ) : exponentialPhase (Real.log r) t = phase r t := by
  unfold exponentialPhase phase
  congr 1
  push_cast
  ring

/-- Actual finite-height second moment for positive rational frequencies of
bounded denominator. All frequency separation and mean-value input is proved. -/
theorem rational_finite_height_mean_value (A : Finset ℚ) (c : ℚ → ℂ)
    {H L T t₀ : ℝ} (hH : 0 < H) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hA : ∀ r ∈ A, 0 < r ∧ (r.den : ℝ) ≤ H ∧ |Real.log (r : ℝ)| ≤ L)
    (W : Finset ℝ) (hW : ∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T))
    (hsep : ∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) :
    let δ := 1 / (Real.exp L * H ^ 2)
    (∑ t ∈ W, ‖∑ r ∈ A, c r * phase r t‖ ^ 2) ≤
      (2+L^2) * (T+1+4*δ⁻¹*(1+Real.log ⌊2*L/δ⌋₊)) * ∑ r ∈ A, ‖c r‖ ^ 2 := by
  dsimp only
  have hδ : 0 < 1 / (Real.exp L * H ^ 2) := by positivity
  have hf : ∀ r ∈ A, ∀ s ∈ A, r ≠ s →
      1 / (Real.exp L * H ^ 2) ≤ |Real.log (r : ℝ) - Real.log (s : ℝ)| := by
    intro r hr s hs hne
    exact positive_rational_log_gap (hA r hr).1 (hA s hs).1 hne
      (hA r hr).2.1 (hA s hs).2.1
      ((le_abs_self _).trans (hA r hr).2.2) ((le_abs_self _).trans (hA s hs).2.2)
  have hh := separated_frequency_discrete_mean_value A (fun r => Real.log (r : ℝ)) c
    hδ hL hT (fun r hr => (hA r hr).2.2) hf W hW hsep
  simpa only [exponentialPolynomial, exponentialPhase_log] using hh

def rationalTuples (A : Finset ℚ) (k : ℕ) : Finset (Fin k → ℚ) :=
  Fintype.piFinset (fun _ => A)
def rationalProducts (A : Finset ℚ) (k : ℕ) : Finset ℚ :=
  (rationalTuples A k).image (fun x => ∏ j, x j)
def rationalPowerCoefficient (A : Finset ℚ) (k : ℕ) (c : ℚ → ℂ) (q : ℚ) : ℂ :=
  ∑ x ∈ (rationalTuples A k).filter (fun x => ∏ j, x j = q), ∏ j, c (x j)
def rationalCoefficientEnergy (A : Finset ℚ) (k : ℕ) (c : ℚ → ℂ) : ℝ :=
  ∑ q ∈ rationalProducts A k, ‖rationalPowerCoefficient A k c q‖ ^ 2

theorem phase_product {κ : Type*} (S : Finset κ) (r : κ → ℝ)
    (hr : ∀ j ∈ S, 0 < r j) (t : ℝ) :
    (∏ j ∈ S, phase (r j) t) = phase (∏ j ∈ S, r j) t := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [phase]
  | @insert i S hi ih =>
    rw [prod_insert hi, prod_insert hi, ih (fun j hj => hr j (mem_insert_of_mem hj))]
    unfold phase
    rw [← Complex.exp_add, Real.log_mul (hr i (mem_insert_self i S)).ne'
      (Finset.prod_pos (fun j hj => hr j (mem_insert_of_mem hj))).ne']
    congr 1
    push_cast
    ring

/-- Literal expansion of B(t)^k, with all equal products grouped together. -/
theorem rational_power_expansion (A : Finset ℚ) (c : ℚ → ℂ) (k : ℕ)
    (hA : ∀ r ∈ A, 0 < r) (t : ℝ) :
    (∑ r ∈ A, c r * phase r t) ^ k =
      ∑ q ∈ rationalProducts A k, rationalPowerCoefficient A k c q * phase q t := by
  rw [sum_pow']
  have he (x : Fin k → ℚ) (hx : x ∈ rationalTuples A k) :
      (∏ j, c (x j) * phase (x j) t) = (∏ j, c (x j)) * phase (∏ j, x j : ℚ) t := by
    rw [prod_mul_distrib]
    have hp : ∀ j ∈ (univ : Finset (Fin k)), (0 : ℝ) < (x j : ℝ) := by
      intro j _
      exact_mod_cast hA (x j) (Fintype.mem_piFinset.mp hx j)
    rw [phase_product univ (fun j => (x j : ℝ)) hp]
    simp only [Rat.cast_prod]
  have hgroup := Finset.sum_fiberwise_of_maps_to
    (show ∀ x ∈ rationalTuples A k, (∏ j, x j) ∈ rationalProducts A k from
      fun x hx => mem_image.mpr ⟨x, hx, rfl⟩)
    (fun x : Fin k → ℚ => (∏ j, c (x j)) * phase (∏ j, x j : ℚ) t)
  change (∑ x ∈ rationalTuples A k, ∏ j, c (x j) * phase (x j) t) = _
  rw [sum_congr rfl he, ← hgroup]
  apply sum_congr rfl
  intro q _
  rw [rationalPowerCoefficient, sum_mul]
  apply sum_congr rfl
  intro x hx
  rw [(mem_filter.mp hx).2]

theorem rational_product_denominator {κ : Type*} (S : Finset κ) (r : κ → ℚ) :
    (∏ j ∈ S, r j).den ≤ ∏ j ∈ S, (r j).den := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [prod_insert hi, prod_insert hi]
    exact (Nat.le_of_dvd (Nat.mul_pos (r i).pos (∏ j ∈ S, r j).pos)
      (Rat.mul_den_dvd _ _)).trans (Nat.mul_le_mul_left _ ih)

theorem rational_product_bounds (A : Finset ℚ) (k H : ℕ) {L : ℝ}
    (hA : ∀ r ∈ A, 0 < r ∧ r.den ≤ H ∧ |Real.log (r : ℝ)| ≤ L)
    {q : ℚ} (hq : q ∈ rationalProducts A k) :
    0 < q ∧ q.den ≤ H ^ k ∧ |Real.log (q : ℝ)| ≤ (k : ℝ) * L := by
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hq
  have hxA (j : Fin k) : x j ∈ A := Fintype.mem_piFinset.mp hx j
  have hpos (j : Fin k) : (0 : ℝ) < (x j : ℝ) := by exact_mod_cast (hA (x j) (hxA j)).1
  refine ⟨Finset.prod_pos (fun j _ => (hA (x j) (hxA j)).1), ?_, ?_⟩
  · calc
      _ ≤ ∏ j, (x j).den := rational_product_denominator univ x
      _ ≤ ∏ _j : Fin k, H := prod_le_prod (fun j _ => (hA (x j) (hxA j)).2.1)
      _ = H ^ k := by simp
  · rw [Rat.cast_prod, Real.log_prod (fun j _ => (hpos j).ne')]
    calc
      _ ≤ ∑ j, |Real.log (x j : ℝ)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin k, L := sum_le_sum (fun j _ => (hA (x j) (hxA j)).2.2)
      _ = (k : ℝ) * L := by simp

/-- Full finite-height transfer for every integer moment order. The right side
contains the exact grouped-product coefficient energy, not an assumed torus
moment. The small-power bound for that arithmetic energy is a separate task. -/
theorem rational_finite_height_moment (A : Finset ℚ) (c : ℚ → ℂ) (k H : ℕ)
    (hH : 1 ≤ H) {L T t₀ : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hA : ∀ r ∈ A, 0 < r ∧ r.den ≤ H ∧ |Real.log (r : ℝ)| ≤ L)
    (W : Finset ℝ) (hW : ∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T))
    (hsep : ∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) :
    let Lk := (k : ℝ) * L
    let δ := 1 / (Real.exp Lk * ((H : ℝ) ^ k) ^ 2)
    (∑ t ∈ W, ‖∑ r ∈ A, c r * phase r t‖ ^ (2*k)) ≤
      (2+Lk^2) * (T+1+4*δ⁻¹*(1+Real.log ⌊2*Lk/δ⌋₊)) *
        rationalCoefficientEnergy A k c := by
  dsimp only
  have hHr : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hproducts : ∀ q ∈ rationalProducts A k,
      0 < q ∧ (q.den : ℝ) ≤ (H : ℝ) ^ k ∧ |Real.log (q : ℝ)| ≤ (k : ℝ) * L := by
    intro q hq
    have hb := rational_product_bounds A k H hA hq
    exact ⟨hb.1, by exact_mod_cast hb.2.1, hb.2.2⟩
  have hh := rational_finite_height_mean_value (rationalProducts A k)
    (rationalPowerCoefficient A k c) (pow_pos hHr k) (by positivity : 0 ≤ (k : ℝ) * L)
    hT hproducts W hW hsep
  dsimp only at hh
  change _ ≤ _ * rationalCoefficientEnergy A k c at hh
  convert hh using 1
  apply sum_congr rfl
  intro t _
  rw [← rational_power_expansion A c k (fun r hr => (hA r hr).1), norm_pow, ← pow_mul]
  congr 1
  omega

end Montgomery.RationalMoment

#print axioms Montgomery.RationalMoment.rational_finite_height_mean_value
#print axioms Montgomery.RationalMoment.rational_power_expansion
#print axioms Montgomery.RationalMoment.rational_product_bounds
#print axioms Montgomery.RationalMoment.rational_finite_height_moment
