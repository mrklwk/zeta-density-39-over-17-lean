module
public import GuthMaynard.Improvement.Target
public import GuthMaynard.Improvement.CenteredKernelBridge
public import GuthMaynard.Improvement.DivisorMultiplicity
public import MathCollab.Density.DivisorGrowth

@[expose] public section
set_option autoImplicit false
noncomputable section
open Finset
namespace GuthMaynard.Improvement

/-- The real source length is retained literally, including nonintegral N. -/
def amplifierSource (N : ℝ) : Finset ℕ := Ioc ⌊N⌋₊ ⌊2*N⌋₊

/-- The complete integer amplifier interval, with both endpoints included. -/
def amplifierColumns (N L : ℝ) : Finset ℕ := Icc ⌈L/N⌉₊ ⌊2*L/N⌋₊

/-- Finite fiber definition of the literal divisor matrix, embedded into
signed frequency rows. Coefficients outside the original source vanish. -/
def amplifierMatrix (N : ℝ) (a : ℕ → ℂ) (m : ℤ) (q : ℕ) : ℂ :=
  ∑ n ∈ amplifierSource N, if m=(q*n:ℕ) then a n else 0

theorem amplifier_source_bounds {N : ℝ} (hN : 0 < N) {n : ℕ}
    (hn : n ∈ amplifierSource N) : N < (n:ℝ) ∧ (n:ℝ) ≤ 2*N := by
  obtain ⟨h₁,h₂⟩ := mem_Ioc.mp hn
  exact ⟨(Nat.floor_lt hN.le).mp h₁,(Nat.le_floor_iff (by positivity)).mp h₂⟩

theorem amplifier_column_bounds {N L : ℝ} (hN : 0 < N) (hNL : N ≤ L) {q : ℕ}
    (hq : q ∈ amplifierColumns N L) :
    0 < q ∧ L/N ≤ (q:ℝ) ∧ (q:ℝ) ≤ 2*L/N := by
  obtain ⟨h₁,h₂⟩ := mem_Icc.mp hq
  have hL : 0 < L := hN.trans_le hNL
  have hlo : L/N ≤ (q:ℝ) := Nat.ceil_le.mp h₁
  have hhi : (q:ℝ) ≤ 2*L/N := (Nat.le_floor_iff (by positivity)).mp h₂
  exact ⟨by exact_mod_cast (lt_of_lt_of_le (div_pos hL hN) hlo),hlo,hhi⟩

theorem amplifier_product_plateau {N L : ℝ} (hN : 0 < N) (hNL : N ≤ L)
    {q n : ℕ} (hq : q ∈ amplifierColumns N L) (hn : n ∈ amplifierSource N) :
    1 ≤ ((q*n:ℕ):ℝ)/L ∧ ((q*n:ℕ):ℝ)/L ≤ 4 := by
  obtain ⟨hq0,hqlo,hqhi⟩ := amplifier_column_bounds hN hNL hq
  obtain ⟨hnlo,hnhi⟩ := amplifier_source_bounds hN hn
  have hL : 0 < L := hN.trans_le hNL
  have hqN : L ≤ (q:ℝ)*N := (div_le_iff₀ hN).mp hqlo
  have hqN' : (q:ℝ)*N ≤ 2*L := (le_div_iff₀ hN).mp hqhi
  constructor
  · apply (le_div_iff₀ hL).mpr
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hnlo.le (Nat.cast_nonneg q)]
  · apply (div_le_iff₀ hL).mpr
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hnhi (Nat.cast_nonneg q)]

theorem amplifier_product_row {N L l u : ℝ} (hN : 0 < N) (hNL : N ≤ L)
    (hl : l ≤ 1) (hu : 4 ≤ u) {q n : ℕ}
    (hq : q ∈ amplifierColumns N L) (hn : n ∈ amplifierSource N) :
    ((q*n:ℕ):ℤ) ∈ Icc ⌈l*L⌉ ⌊u*L⌋ := by
  have hL : 0 < L := hN.trans_le hNL
  obtain ⟨hlo,hhi⟩ := amplifier_product_plateau hN hNL hq hn
  push_cast at hlo hhi
  rw [mem_Icc,Int.ceil_le,Int.le_floor]
  push_cast
  exact ⟨(mul_le_mul_of_nonneg_right hl hL.le).trans ((le_div_iff₀ hL).mp hlo),
    ((div_le_iff₀ hL).mp hhi).trans (mul_le_mul_of_nonneg_right hu hL.le)⟩

/-- Actual amplifier cardinality is comparable to L/N, even when that
ratio is between one and two and the endpoints are nonintegral. -/
theorem amplifier_columns_card {N L : ℝ} (hN : 0 < N) (hNL : N ≤ L) :
    L/N/2 ≤ ((amplifierColumns N L).card:ℝ) ∧
      ((amplifierColumns N L).card:ℝ) ≤ 2*L/N := by
  let x := L/N
  have hx : 1 ≤ x := (le_div_iff₀ hN).mpr (by simpa using hNL)
  have hxc : x ≤ (⌈x⌉₊:ℝ) := Nat.le_ceil x
  have hxc' : (⌈x⌉₊:ℝ) ≤ x+1 := by
    have hh : (⌈x⌉₊:ℝ) ≤ (⌊x⌋₊:ℝ)+1 := by exact_mod_cast Nat.ceil_le_floor_add_one x
    have hf := Nat.floor_le (by linarith : 0 ≤ x)
    linarith
  have hcf : ⌈x⌉₊ ≤ ⌊2*x⌋₊ := Nat.le_floor (by linarith)
  have hcard : ((amplifierColumns N L).card:ℝ) = (⌊2*x⌋₊:ℝ)+1-(⌈x⌉₊:ℝ) := by
    have he : 2*L/N=2*x := by dsimp [x]; ring
    unfold amplifierColumns
    change ((Icc ⌈x⌉₊ ⌊2*L/N⌋₊).card:ℝ) = _
    rw [he,Nat.card_Icc,Nat.cast_sub (by omega)]
    push_cast
    rfl
  have hf : (⌊2*x⌋₊:ℝ) ≤ 2*x := Nat.floor_le (by linarith)
  have hf' : 2*x < (⌊2*x⌋₊:ℝ)+1 := Nat.lt_floor_add_one (2*x)
  have hone : 1 ≤ ((amplifierColumns N L).card:ℝ) := by
    have hp : 0 < (amplifierColumns N L).card := Finset.card_pos.mpr ⟨⌈x⌉₊,by
      unfold amplifierColumns
      rw [show 2*L/N=2*x by dsimp [x]; ring]
      exact mem_Icc.mpr ⟨le_rfl,hcf⟩⟩
    exact_mod_cast hp
  constructor
  · change x/2 ≤ _
    by_cases hh : x ≤ 2
    · linarith
    · rw [hcard]
      linarith
  · rw [hcard,show 2*L/N=2*x by dsimp [x]; ring]
    linarith

/-- The source has at most N+1 terms, uniformly for real N. -/
theorem amplifier_source_card {N : ℝ} (hN : 0 ≤ N) :
    ((amplifierSource N).card:ℝ) ≤ N+1 := by
  have hfl : ⌊N⌋₊ ≤ ⌊2*N⌋₊ := Nat.floor_mono (by linarith)
  rw [amplifierSource,Nat.card_Ioc,Nat.cast_sub hfl]
  have h₁ := Nat.floor_le (by linarith : 0 ≤ 2*N)
  have h₂ := Nat.lt_floor_add_one N
  linarith

/-- Exact finite reindexing, not an analytic or operator identity premise. -/
theorem amplifier_matrix_column (N : ℝ) (a : ℕ → ℂ) (q : ℕ)
    (M : Finset ℤ) (F : ℤ → ℂ)
    (hm : ∀ n ∈ amplifierSource N, ((q*n:ℕ):ℤ) ∈ M) :
    (∑ m ∈ M, amplifierMatrix N a m q * F m) =
      ∑ n ∈ amplifierSource N, a n * F ((q*n:ℕ):ℤ) := by
  classical
  simp only [amplifierMatrix,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_eq_single ((q*n:ℕ):ℤ)]
  · simp
  · intro m _ hne
    rw [ite_eq_right hne,zero_mul]
  · intro habs
    exact False.elim (habs (hm n hn))

/-- Multiplicative normalization of the actual source n/N and row qn/L. -/
theorem amplifier_product_phase {N L : ℝ} (hN : 0 < N) (hL : 0 < L)
    {q n : ℕ} (hq : 0 < q) (hn : 0 < n) (t : ℝ) :
    phase (t*mellinFrequency (((q*n:ℕ):ℝ)/L)) =
      phase (t*mellinFrequency ((q:ℝ)*N/L)) *
        Complex.exp (((t*Real.log ((n:ℝ)/N):ℝ):ℂ)*Complex.I) := by
  rw [← mellinFrequency_phase]
  rw [← phase_add]
  congr 1
  unfold mellinFrequency
  have he : ((q*n:ℕ):ℝ)/L = ((q:ℝ)*N/L)*((n:ℝ)/N) := by
    push_cast
    field_simp
  rw [he,Real.log_mul (by positivity) (by positivity)]
  ring

/-- The literal finite matrix column, with the actual cutoff plateau, is
exactly a unit phase times the original boundedPolynomial. -/
theorem amplifier_column_identity {N L l u : ℝ} (hN : 0 < N) (hNL : N ≤ L)
    (hl : l ≤ 1) (hu : 4 ≤ u) (a : ℕ → ℂ) (w : ℝ → ℝ)
    (hw : ∀ x ∈ Set.Icc (1:ℝ) 4, w x=1) {q : ℕ}
    (hq : q ∈ amplifierColumns N L) (t : ℝ) :
    (∑ m ∈ Icc ⌈l*L⌉ ⌊u*L⌋,
      amplifierMatrix N a m q *
        ((w ((m:ℝ)/L):ℂ)*phase (t*mellinFrequency ((m:ℝ)/L)))) =
      phase (t*mellinFrequency ((q:ℝ)*N/L))*boundedPolynomial N a t := by
  rw [amplifier_matrix_column N a q _ _
    (fun n hn => amplifier_product_row hN hNL hl hu hq hn)]
  unfold boundedPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn' : n ∈ amplifierSource N := hn
  have hp := amplifier_product_plateau hN hNL hq hn'
  have hq0 := (amplifier_column_bounds hN hNL hq).1
  have hn0 : 0 < n := by
    exact_mod_cast (hN.trans (amplifier_source_bounds hN hn').1)
  have hww := hw (((q*n:ℕ):ℝ)/L) hp
  push_cast
  push_cast at hww
  rw [hww,Complex.ofReal_one,one_mul]
  have hh := amplifier_product_phase hN (hN.trans_le hNL) hq0 hn0 t
  push_cast at hh
  rw [hh]
  ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.amplifier_source_bounds
#print axioms GuthMaynard.Improvement.amplifier_column_bounds
#print axioms GuthMaynard.Improvement.amplifier_product_plateau
#print axioms GuthMaynard.Improvement.amplifier_product_row
#print axioms GuthMaynard.Improvement.amplifier_matrix_column
#print axioms GuthMaynard.Improvement.amplifier_product_phase
#print axioms GuthMaynard.Improvement.amplifier_column_identity

#print axioms GuthMaynard.Improvement.amplifier_columns_card
#print axioms GuthMaynard.Improvement.amplifier_source_card
