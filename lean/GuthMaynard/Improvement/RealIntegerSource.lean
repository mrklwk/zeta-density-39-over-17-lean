import GuthMaynard.Improvement.ReflectedBandMeanValue
import MathCollab.Density.LargeValueDefinitions
set_option autoImplicit false
noncomputable section
open Finset
namespace GuthMaynard.Improvement

/-- The integer length loses at most a factor two from a real source length. -/
theorem source_floor_bounds {N : ℝ} (hN : 2 ≤ N) :
    2 ≤ ⌊N⌋₊ ∧ N/2 ≤ (⌊N⌋₊:ℝ) ∧ (⌊N⌋₊:ℝ) ≤ N := by
  have hM : 2 ≤ ⌊N⌋₊ := Nat.le_floor hN
  have hlo := Nat.floor_le (by linarith : 0 ≤ N)
  have hhi := Nat.lt_floor_add_one N
  have hm : (2:ℝ) ≤ ⌊N⌋₊ := by exact_mod_cast hM
  exact ⟨hM,by linarith,hlo⟩

/-- Exactly zero or one endpoint lies beyond the integer dyadic source. -/
theorem source_double_floor {N : ℝ} (hN : 0 ≤ N) :
    ⌊2*N⌋₊ = 2*⌊N⌋₊ ∨ ⌊2*N⌋₊ = 2*⌊N⌋₊+1 := by
  have hlo := Nat.floor_le hN
  have hhi := Nat.lt_floor_add_one N
  have hlo2 := Nat.floor_le (by positivity : 0 ≤ 2*N)
  have hl : 2*⌊N⌋₊ ≤ ⌊2*N⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hu : ⌊2*N⌋₊ < 2*⌊N⌋₊+2 := by
    have hh : (⌊2*N⌋₊:ℝ) < (2*⌊N⌋₊+2:ℕ) := by push_cast; linarith
    exact_mod_cast hh
  omega

/-- The audited integer source is literally the present integer-length
polynomial, including normalization and endpoint convention. -/
theorem detectingPolynomial_eq_boundedPolynomial (M : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    MathCollab.Density.detectingPolynomial M a t = boundedPolynomial (M:ℝ) a t := by
  have hf : ⌊2*(M:ℝ)⌋₊ = 2*M := by
    norm_cast
    exact Nat.floor_natCast _
  unfold MathCollab.Density.detectingPolynomial boundedPolynomial
  rw [Nat.floor_natCast,hf]
  apply sum_congr rfl
  intro n _
  unfold MathCollab.Density.dirichletPhase
  congr 2
  ring

/-- Remove only a unit phase; the integer-frequency coefficient sum is literal. -/
theorem boundedPolynomial_norm_integer_sum {N : ℝ} (hN : 0 < N)
    (a : ℕ → ℂ) (t : ℝ) :
    ‖boundedPolynomial N a t‖ = ‖∑ n ∈ sourceRatioIndices N, a n*dirichletPhase n t‖ := by
  rw [boundedPolynomial_integer_phase hN,norm_mul,MathCollab.Density.norm_dirichletPhase,one_mul]

/-- Bounded coefficients on the original real source remain bounded on
its integer source; no coefficient extension estimate is assumed. -/
theorem source_floor_coefficients {N : ℝ} (hN : 0 ≤ N) (a : ℕ → ℂ)
    (ha : ∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) :
    ∀ n ∈ Ioc ⌊N⌋₊ (2*⌊N⌋₊), ‖a n‖ ≤ 1 := by
  intro n hn
  apply ha n
  obtain ⟨hn0,hn1⟩ := mem_Ioc.mp hn
  have hl : 2*⌊N⌋₊ ≤ ⌊2*N⌋₊ := Nat.le_floor (by
    push_cast
    exact mul_le_mul_of_nonneg_left (Nat.floor_le hN) (by norm_num))
  exact mem_Ioc.mpr ⟨hn0,hn1.trans hl⟩

/-- The real source differs, after a unit normalization, by at most one
bounded endpoint term. This is an actual polynomial estimate. -/
theorem boundedPolynomial_le_detecting_floor_add_one {N : ℝ} (hN : 2 ≤ N)
    (a : ℕ → ℂ) (ha : ∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) (t : ℝ) :
    ‖boundedPolynomial N a t‖ ≤ ‖MathCollab.Density.detectingPolynomial ⌊N⌋₊ a t‖+1 := by
  have hN0 : 0 < N := by linarith
  have hM0 : (0:ℝ) < ⌊N⌋₊ := by
    have hh := (source_floor_bounds hN).1
    exact_mod_cast (by omega : 0 < ⌊N⌋₊)
  rw [detectingPolynomial_eq_boundedPolynomial,
    boundedPolynomial_norm_integer_sum hN0,boundedPolynomial_norm_integer_sum hM0]
  have hf : ⌊2*(⌊N⌋₊:ℝ)⌋₊ = 2*⌊N⌋₊ := by
    norm_cast
    exact Nat.floor_natCast _
  simp only [sourceRatioIndices,Nat.floor_natCast,hf]
  rcases source_double_floor hN0.le with he | he
  · rw [he]
    linarith
  · rw [he,sum_Ioc_succ_top (by omega : ⌊N⌋₊ ≤ 2*⌊N⌋₊)]
    have ha' : ‖a (2*⌊N⌋₊+1)‖ ≤ 1 := ha _ (by
      unfold sourceRatioIndices
      rw [he]
      exact mem_Ioc.mpr ⟨by omega,le_rfl⟩)
    have ht : ‖a (2*⌊N⌋₊+1)*dirichletPhase (2*⌊N⌋₊+1) t‖ ≤ 1 := by
      simpa only [norm_mul,dirichletPhase_norm,mul_one] using ha'
    exact (norm_add_le _ _).trans (add_le_add le_rfl ht)

/-- Large values at real length pass to the audited integer source at
half the threshold, for V≥2. -/
theorem detecting_floor_large_value {N V : ℝ} (hN : 2 ≤ N) (hV : 2 ≤ V)
    (a : ℕ → ℂ) (ha : ∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) {t : ℝ}
    (ht : V ≤ ‖boundedPolynomial N a t‖) :
    V/2 ≤ ‖MathCollab.Density.detectingPolynomial ⌊N⌋₊ a t‖ := by
  have hh := boundedPolynomial_le_detecting_floor_add_one hN a ha t
  linarith

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.source_floor_bounds
#print axioms GuthMaynard.Improvement.source_double_floor
#print axioms GuthMaynard.Improvement.detectingPolynomial_eq_boundedPolynomial
#print axioms GuthMaynard.Improvement.boundedPolynomial_norm_integer_sum
#print axioms GuthMaynard.Improvement.source_floor_coefficients
#print axioms GuthMaynard.Improvement.boundedPolynomial_le_detecting_floor_add_one
#print axioms GuthMaynard.Improvement.detecting_floor_large_value
