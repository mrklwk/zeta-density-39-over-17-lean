import GuthMaynard.Improvement.DirichletProductEnergy
import GuthMaynard.Improvement.Target
import MathCollab.Density.Reflection
set_option autoImplicit false
noncomputable section
open MeasureTheory Finset
open scoped ComplexConjugate
namespace GuthMaynard.Improvement

/-- The exact positive reflected band fits inside this natural initial interval. -/
def reflectedBandLength (L H : ℝ) : ℕ := ⌊4*H/(Real.pi*L)⌋₊

def reflectedBandCoefficient (L H r u : ℝ) (m : ℕ) : ℂ :=
  if m ∈ MathCollab.Density.reflectionNatBand L H then
    MathCollab.Density.dirichletPhase m (-(r+u)) else 0

theorem reflected_band_subset (L H : ℝ) :
    MathCollab.Density.reflectionNatBand L H ⊆ Finset.Icc 1 (reflectedBandLength L H) := by
  intro m hm
  have hh := (MathCollab.Density.mem_reflectionNatBand L H m).mp hm
  exact mem_Icc.mpr ⟨by exact_mod_cast hh.1,Nat.le_floor (by exact_mod_cast hh.2.2)⟩

theorem reflected_band_coefficient_norm (L H r u : ℝ) (m : ℕ) :
    ‖reflectedBandCoefficient L H r u m‖ ≤ 1 := by
  unfold reflectedBandCoefficient
  split_ifs <;> simp [MathCollab.Density.norm_dirichletPhase]

theorem density_dirichletPhase_nat (m : ℕ) (t : ℝ) :
    MathCollab.Density.dirichletPhase m t = dirichletPhase m t := by
  unfold MathCollab.Density.dirichletPhase dirichletPhase
  congr 1
  push_cast
  ring

/-- Exact reflected polynomial orientation. Conjugating the negative-frequency band
produces positive integer frequencies, with all r,u dependence in unit coefficients. -/
theorem reflected_band_polynomial {L : ℝ} (hL : 0 < L) (H r u t : ℝ) :
    conj (MathCollab.Density.bandPhaseSum L H (t-u) r) =
      MathCollab.Density.dirichletPhase L (t-r-u)*
        finiteDirichletPolynomial (reflectedBandLength L H) (reflectedBandCoefficient L H r u) t := by
  have hsum : finiteDirichletPolynomial (reflectedBandLength L H) (reflectedBandCoefficient L H r u) t =
      ∑ m ∈ MathCollab.Density.reflectionNatBand L H,
        MathCollab.Density.dirichletPhase m (-(r+u))*dirichletPhase m t := by
    unfold finiteDirichletPolynomial
    rw [← sum_subset (reflected_band_subset L H) (by
      intro m _ hm
      simp only [reflectedBandCoefficient,ite_eq_right hm,zero_mul])]
    apply sum_congr rfl
    intro m hm
    simp only [reflectedBandCoefficient,ite_eq_left hm]
  rw [hsum,mul_sum,MathCollab.Density.bandPhaseSum,MathCollab.Density.sum_reflectionBand_eq_nat,map_sum]
  apply sum_congr rfl
  intro m hm
  have hm0 : 0 < (m:ℝ) := by
    have hh := (MathCollab.Density.mem_reflectionNatBand L H m).mp hm
    exact_mod_cast hh.1
  rw [← MathCollab.Density.dirichletPhase_neg]
  push_cast
  rw [show -(r-(t-u))=t-r-u by ring,
    MathCollab.Density.dirichletPhase_mul hm0 hL]
  rw [show t-r-u=-(r+u)+t by ring,MathCollab.Density.dirichletPhase_add]
  simp only [density_dirichletPhase_nat]
  ring

/-- Source normalization removes only a unit phase, preserving the literal source indices. -/
theorem boundedPolynomial_integer_phase {N : ℝ} (hN : 0 < N) (a : ℕ → ℂ) (t : ℝ) :
    boundedPolynomial N a t = MathCollab.Density.dirichletPhase N (-t)*
      (∑ n ∈ sourceRatioIndices N, a n*dirichletPhase n t) := by
  unfold boundedPolynomial sourceRatioIndices
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  have hn0 : (0:ℝ) < n := hN.trans ((sourceRatioIndices_mem hN.le n).mp hn).1
  unfold MathCollab.Density.dirichletPhase dirichletPhase
  rw [Real.log_div hn0.ne' hN.ne']
  calc
    _ = a n*(Complex.exp (Complex.I*((-t*Real.log N:ℝ):ℂ))*
        Complex.exp (Complex.I*(Real.log n:ℂ)*t)) := by
      rw [← Complex.exp_add]
      congr 2
      push_cast
      ring
    _ = _ := by ring

/-- Actual norm product, with no oscillatory factor discarded except unit global phases. -/
theorem reflected_band_product_norm {N L : ℝ} (hN : 0 < N) (hL : 0 < L)
    (H r u t : ℝ) (a : ℕ → ℂ) :
    ‖boundedPolynomial N a t‖^2*‖MathCollab.Density.bandPhaseSum L H (t-u) r‖^2 =
      ‖finiteDirichletPolynomial (⌊2*N⌋₊*reflectedBandLength L H)
        (dirichletProductCoefficient N (reflectedBandLength L H) a (reflectedBandCoefficient L H r u)) t‖^2 := by
  have hs : ‖boundedPolynomial N a t‖ = ‖∑ n ∈ sourceRatioIndices N, a n*dirichletPhase n t‖ := by
    rw [boundedPolynomial_integer_phase hN,norm_mul,MathCollab.Density.norm_dirichletPhase,one_mul]
  have hb : ‖MathCollab.Density.bandPhaseSum L H (t-u) r‖ =
      ‖finiteDirichletPolynomial (reflectedBandLength L H) (reflectedBandCoefficient L H r u) t‖ := by
    rw [← RCLike.norm_conj,reflected_band_polynomial hL,norm_mul,
      MathCollab.Density.norm_dirichletPhase,one_mul]
  rw [hs,hb,← mul_pow,← norm_mul,dirichlet_product_polynomial hN.le]

/-- The actual shell integrand is integrable, for every Mellin parameter and translate. -/
theorem reflected_band_product_integrable {N L : ℝ} (hN : 0 < N) (hL : 0 < L)
    (H r u : ℝ) (a : ℕ → ℂ) :
    IntegrableOn (fun t => ‖boundedPolynomial N a t‖^2*
      ‖MathCollab.Density.bandPhaseSum L H (t-u) r‖^2) (Set.Icc (u+H) (u+2*H)) := by
  have he := funext (fun t => reflected_band_product_norm hN hL H r u t a)
  rw [he]
  exact finiteDirichletPolynomial_integrable _ _ _ _

/-- Actual reflected mean value. The constant depends on eta alone, before
all scales, Mellin parameters, translates and bounded source coefficients. -/
theorem reflected_band_mean_value {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ N L H r u : ℝ, 0 < N → 0 < L → 0 ≤ H →
      ∀ a : ℕ → ℂ, (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
      let X := reflectedBandLength L H
      let Y := ⌊2*N⌋₊*X
      (∫ t in Set.Icc (u+H) (u+2*H), ‖boundedPolynomial N a t‖^2*
        ‖MathCollab.Density.bandPhaseSum L H (t-u) r‖^2) ≤
        C*(H+4*(Y:ℝ)*(1+Real.log Y))*(1+2*N*X)^η*(N+1)*X := by
  obtain ⟨C,hC,henergy⟩ := dirichlet_product_energy_subpower hη
  refine ⟨C,hC,?_⟩
  intro N L H r u hN hL hH a ha
  dsimp only
  let X := reflectedBandLength L H
  let Y := ⌊2*N⌋₊*X
  let c := dirichletProductCoefficient N X a (reflectedBandCoefficient L H r u)
  have hmv := dirichlet_mean_value Y c (show u+H ≤ u+2*H by linarith)
  have he := henergy N hN.le X a (reflectedBandCoefficient L H r u) (Finset.Icc 1 Y) ha
    (fun m _ => reflected_band_coefficient_norm L H r u m)
  have hfactor : 0 ≤ H+4*(Y:ℝ)*(1+Real.log Y) := by
    by_cases hy : Y=0
    · simp only [hy,Nat.cast_zero,mul_zero,zero_mul,add_zero]
      exact hH
    · have hy1 : (1:ℝ) ≤ Y := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hy
      have hl : 0 ≤ Real.log Y := Real.log_nonneg hy1
      positivity
  calc
    _ = ∫ t in Set.Icc (u+H) (u+2*H), ‖finiteDirichletPolynomial Y c t‖^2 := by
      apply integral_congr_ae
      filter_upwards with t
      exact reflected_band_product_norm hN hL H r u t a
    _ ≤ (H+4*(Y:ℝ)*(1+Real.log Y))*(∑ k ∈ Finset.Icc 1 Y, ‖c k‖^2) := by
      convert hmv using 1
      ring
    _ ≤ (H+4*(Y:ℝ)*(1+Real.log Y))*(C*(1+2*N*X)^η*(N+1)*X) :=
      mul_le_mul_of_nonneg_left he hfactor
    _ = _ := by ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.reflected_band_subset
#print axioms GuthMaynard.Improvement.reflected_band_coefficient_norm
#print axioms GuthMaynard.Improvement.density_dirichletPhase_nat
#print axioms GuthMaynard.Improvement.reflected_band_polynomial
#print axioms GuthMaynard.Improvement.boundedPolynomial_integer_phase
#print axioms GuthMaynard.Improvement.reflected_band_product_norm
#print axioms GuthMaynard.Improvement.reflected_band_product_integrable
#print axioms GuthMaynard.Improvement.reflected_band_mean_value
