module
public import RationalFiniteHeight
public import GuthMaynard.NativeSource.GuthMaynard.ArithmeticCoefficients

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Finset GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

def finiteSupportTuples (A : Finset ℕ) (k : ℕ) : Finset (Fin k → ℕ) :=
  Fintype.piFinset (fun _ => A)

def finiteSupportProducts (A : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (finiteSupportTuples A k).image (fun p => ∏ i, p i)

def finiteSupportPowerCoeff (A : Finset ℕ) (k : ℕ) (a : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ p ∈ (finiteSupportTuples A k).filter (fun p => ∏ i, p i = m), ∏ i, a (p i)

/-- Exact powering on arbitrary finite positive support. Products equal to
an endpoint are retained literally; no rounded base dyadic interval occurs. -/
theorem finite_support_power_expansion (A : Finset ℕ) (a : ℕ → ℂ) (k : ℕ)
    (hA : ∀ n ∈ A, 0 < n) (t : ℝ) :
    (∑ n ∈ A, a n * phase n t) ^ k =
      ∑ m ∈ finiteSupportProducts A k, finiteSupportPowerCoeff A k a m * phase m t := by
  classical
  rw [sum_pow']
  have he (p : Fin k → ℕ) (hp : p ∈ finiteSupportTuples A k) :
      (∏ i, a (p i) * phase (p i) t) =
        (∏ i, a (p i)) * phase (∏ i, p i : ℕ) t := by
    rw [prod_mul_distrib]
    have hPos : ∀ i ∈ (univ : Finset (Fin k)), (0 : ℝ) < p i := by
      intro i _
      exact_mod_cast hA (p i) (Fintype.mem_piFinset.mp hp i)
    rw [phase_product univ (fun i => (p i : ℝ)) hPos]
    simp only [Nat.cast_prod]
  have hGroup := Finset.sum_fiberwise_of_maps_to
    (show ∀ p ∈ finiteSupportTuples A k, (∏ i, p i) ∈ finiteSupportProducts A k from
      fun p hp => mem_image.mpr ⟨p, hp, rfl⟩)
    (fun p : Fin k → ℕ => (∏ i, a (p i)) * phase (∏ i, p i : ℕ) t)
  change (∑ p ∈ finiteSupportTuples A k, ∏ i, a (p i) * phase (p i) t) = _
  rw [sum_congr rfl he, ← hGroup]
  apply sum_congr rfl
  intro m _
  rw [finiteSupportPowerCoeff, sum_mul]
  apply sum_congr rfl
  intro p hp
  rw [(mem_filter.mp hp).2]

/-- Uniform coefficient growth, including tuples containing the factor1.
Every coordinate divides the positive target, so the proved divisor bound
controls all ordered factorizations without an artificial lower cutoff2. -/
theorem finite_support_power_coeff_bound_uniform (k : ℕ) (ν : ℝ) (hν : 0 < ν) :
    ∃ D : ℝ, 0 < D ∧ ∀ (A : Finset ℕ) (a : ℕ → ℂ),
      (∀ n ∈ A, ‖a n‖ ≤ 1) → ∀ m : ℕ, 0 < m →
      ‖finiteSupportPowerCoeff A k a m‖ ≤ D * (m : ℝ) ^ ν := by
  classical
  let δ : ℝ := ν / (k + 1 : ℕ)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨C, hC, hDiv⟩ := divisorCountBound_native δ hδ
  refine ⟨C ^ k, by positivity, ?_⟩
  intro A a ha m hm
  let S := (finiteSupportTuples A k).filter (fun p => ∏ i, p i = m)
  have hSub : S ⊆ Fintype.piFinset (fun (_ : Fin k) => m.divisors) := by
    intro p hp
    have hProd := (mem_filter.mp hp).2
    rw [Fintype.mem_piFinset]
    intro i
    rw [Nat.mem_divisors]
    refine ⟨?_, hm.ne'⟩
    have h := dvd_prod_of_mem (fun j => p j) (mem_univ i)
    simpa only [hProd] using h
  have hTerms : ∀ p ∈ S, ‖∏ i, a (p i)‖ ≤ 1 := by
    intro p hp
    rw [norm_prod]
    apply prod_le_one₀ (fun i _ => norm_nonneg _)
    intro i _
    exact ha (p i) (Fintype.mem_piFinset.mp (mem_filter.mp hp).1 i)
  have hCard : (S.card : ℝ) ≤ (m.divisors.card : ℝ) ^ k := by
    have h := card_le_card hSub
    rw [Fintype.card_piFinset_const] at h
    exact_mod_cast h
  have hδk : δ * (k : ℝ) ≤ ν := by
    have hk : (k : ℝ) ≤ (k + 1 : ℕ) := by norm_num
    have h := (div_le_one (by positivity : (0 : ℝ) < (k + 1 : ℕ))).mpr hk
    calc
      δ * (k : ℝ) = ν * ((k : ℝ) / (k + 1 : ℕ)) := by dsimp only [δ]; ring
      _ ≤ ν * 1 := mul_le_mul_of_nonneg_left h hν.le
      _ = ν := mul_one _
  calc
    ‖finiteSupportPowerCoeff A k a m‖ ≤ ∑ p ∈ S, ‖∏ i, a (p i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _p ∈ S, (1 : ℝ) := sum_le_sum hTerms
    _ = (S.card : ℝ) := by simp
    _ ≤ (m.divisors.card : ℝ) ^ k := hCard
    _ ≤ (C * (m : ℝ) ^ δ) ^ k := by gcongr; exact hDiv m hm
    _ = C ^ k * (m : ℝ) ^ (δ * (k : ℝ)) := by
      rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg m)]
    _ ≤ C ^ k * (m : ℝ) ^ ν := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm) hδk

theorem finite_support_products_bounds {X : ℝ} (hX : 0 < X)
    {A : Finset ℕ} (hA : ∀ n ∈ A, X < n ∧ (n : ℝ) ≤ 2 * X)
    {k : ℕ} (hk : 0 < k) {m : ℕ} (hm : m ∈ finiteSupportProducts A k) :
    X ^ k < (m : ℝ) ∧ (m : ℝ) ≤ (2 * X) ^ k := by
  classical
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hm
  have hpA := Fintype.mem_piFinset.mp hp
  have hNonempty : (univ : Finset (Fin k)).Nonempty :=
    ⟨⟨0, hk⟩, mem_univ _⟩
  constructor
  · have h := prod_lt_prod_of_nonempty₀ (fun (_ : Fin k) _ => hX)
      (fun i _ => (hA (p i) (hpA i)).1) hNonempty
    simpa only [prod_const, card_univ, Fintype.card_fin, Nat.cast_prod] using h
  · have h := prod_le_prod₀ (fun i (_ : i ∈ (univ : Finset (Fin k))) => Nat.cast_nonneg (p i))
      (fun i _ => (hA (p i) (hpA i)).2)
    simpa only [prod_const, card_univ, Fintype.card_fin, Nat.cast_prod] using h

end Montgomery.RationalMoment
