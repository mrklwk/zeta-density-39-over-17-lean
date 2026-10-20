module
public import RationalDyadicDifference
public import GuthMaynard.Improvement.ReflectionKernelBridge
public import GuthMaynard.Improvement.ReflectionNear

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
namespace Montgomery.RationalMoment

/-- The density-library phase uses exactly the same real logarithm. -/
theorem density_phase_eq (x v : ℝ) :
    MathCollab.Density.dirichletPhase x v = phase x v := by
  unfold MathCollab.Density.dirichletPhase phase
  congr 1
  push_cast
  ring

/-- The published reflection blocks use [M,2M). The half-unit shift
allows the proved real-length difference estimate to apply to this exact set. -/
theorem reflection_complete_pair_short_range {K : ℕ} (hK : 1 ≤ K)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t₀ : ℝ), 1 < T → ∀ M : ℕ, 0 < M →
      ∀ W : Finset ℝ,
      T^(((K : ℝ)+1)/(2*K+1)) ≤ W.card → (M : ℝ)^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      MathCollab.Density.completePairEnergy M W ≤ C*T^η*M*(W.card : ℝ)^2 := by
  obtain ⟨C,hC,hbound⟩ := dyadic_dirichlet_difference hK hη
  refine ⟨C,hC,?_⟩
  intro T t₀ hT M hM W hR hMR hW hsep
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hA : ∀ n ∈ Ico M (2*M), 0 < n ∧ (M:ℝ)-1/2 < n ∧
      (n:ℝ) ≤ 2*((M:ℝ)-1/2) := by
    intro n hn
    obtain ⟨hn1,hn2⟩ := mem_Ico.mp hn
    have hlo : (M:ℝ) ≤ n := by exact_mod_cast hn1
    have hhi : (n:ℝ) ≤ 2*(M:ℝ)-1 := by
      have hh : n+1 ≤ 2*M := hn2
      have hr : (n:ℝ)+1 ≤ 2*(M:ℝ) := by exact_mod_cast hh
      linarith
    exact ⟨lt_of_lt_of_le hM hn1,by linarith,by linarith⟩
  have hm : 0 ≤ (M:ℝ)-1/2 := by linarith
  have hh := hbound T t₀ ((M:ℝ)-1/2) hT hm (Ico M (2*M)) hA W hR
    ((pow_le_pow_left₀ hm (by linarith : (M:ℝ)-1/2 ≤ M) K).trans hMR)
    hW hsep (fun _ => 1) (by simp)
  have hnorm (v : ℝ) : ‖MathCollab.Density.dyadicPolynomial M v‖ =
      ‖∑ n ∈ Ico M (2*M), phase n v‖ := by
    have he : MathCollab.Density.dyadicPolynomial M v =
        (∑ n ∈ Ico M (2*M), phase n v) * star (phase M v) := by
      unfold MathCollab.Density.dyadicPolynomial
      rw [sum_mul]
      apply sum_congr rfl
      intro n hn
      rw [density_phase_eq,phase_frequency_ratio
        (by exact_mod_cast (hA n hn).1) (by linarith)]
    rw [he,norm_mul,norm_star]
    have hp : ‖phase M v‖ = 1 := by rw [← exponentialPhase_log,exponentialPhase_norm]
    rw [hp,mul_one]
  unfold MathCollab.Density.completePairEnergy
  simp_rw [hnorm]
  simp only [one_mul] at hh
  exact hh.trans (by gcongr; linarith)

/-- Every pair occurs in at most three of the actual local reflection sets.
This permits the global short-range theorem to be used without imposing a
cardinality threshold on each local subset. -/
theorem reflection_local_pair_le_three {H : ℝ} (hH : 0 < H)
    (M : ℕ) (W : Finset ℝ) :
    (∑' j : ℤ, MathCollab.Density.completePairEnergy M
      (MathCollab.Density.localSet W H j)) ≤
      3*MathCollab.Density.completePairEnergy M W := by
  classical
  open MathCollab.Density in
  rw [tsum_completePairEnergy_localSet hH]
  have he (j : ℤ) : completePairEnergy M (localSet W H j) =
      ∑ t ∈ W, ∑ u ∈ W, if t ∈ localSet W H j ∧ u ∈ localSet W H j then
        ‖dyadicPolynomial M (t-u)‖^2 else 0 :=
    (sum_pairs_indicator (filter_subset _ _) _).symm
  simp_rw [he]
  simp_rw [sum_comm (s := localIndices W H) (t := W)]
  unfold completePairEnergy
  rw [mul_sum]
  apply sum_le_sum
  intro t ht
  rw [mul_sum]
  apply sum_le_sum
  intro u _
  calc
    _ ≤ ∑ j ∈ localIndices W H, if t ∈ localSet W H j then
        ‖dyadicPolynomial M (t-u)‖^2 else 0 := by
      apply sum_le_sum
      intro j _
      by_cases htj : t ∈ localSet W H j
      · simp only [htj,true_and,ite_true]
        split_ifs <;> first | exact le_rfl | exact sq_nonneg _
      · simp only [htj,false_and,ite_false,le_refl]
    _ = 3*‖dyadicPolynomial M (t-u)‖^2 := by
      rw [← sum_filter,localIndices_filter_point hH ht]
      simp

/-- All actual reflected blocks satisfy the short-range estimate at once;
the bound uses the explicit largest reflected length 4H/(pi L). -/
theorem reflection_local_energy_short_range {K : ℕ} (hK : 1 ≤ K)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ L H : ℝ, 1 < T → 0 < L → 0 < H →
      ∀ W : Finset ℝ,
      T^(((K : ℝ)+1)/(2*K+1)) ≤ W.card →
      (4*H/(Real.pi*L))^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      MathCollab.Density.localReflectionEnergy L H W ≤
        C*T^η*(H/L)*(W.card : ℝ)^2 := by
  obtain ⟨C,hC,hbound⟩ := reflection_complete_pair_short_range hK hη
  refine ⟨120*C/Real.pi,by positivity,?_⟩
  intro T t₀ L H hT hL hH W hR hlen hW hsep
  open MathCollab.Density in
  have hb (M : ℕ) (hM : M ∈ reflectionBlocks L H) :
      (∑' j : ℤ, completePairEnergy M (localSet W H j)) ≤
        3*(C*T^η*(4*H/(Real.pi*L))*(W.card : ℝ)^2) := by
    obtain ⟨hM0,_,hMhi⟩ := reflectionBlock_scale_bounds hL hH hM
    refine (reflection_local_pair_le_three hH M W).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 3)
    exact (hbound T t₀ hT M hM0 W hR
      ((pow_le_pow_left₀ (by positivity) hMhi K).trans hlen) hW hsep).trans (by gcongr)
  open MathCollab.Density in
  calc
    localReflectionEnergy L H W ≤ ∑ _M ∈ reflectionBlocks L H,
        3*(C*T^η*(4*H/(Real.pi*L))*(W.card : ℝ)^2) := sum_le_sum hb
    _ = ((reflectionBlocks L H).card:ℝ)*
        (3*(C*T^η*(4*H/(Real.pi*L))*(W.card : ℝ)^2)) := by simp
    _ ≤ 10*(3*(C*T^η*(4*H/(Real.pi*L))*(W.card : ℝ)^2)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast reflectionBlocks_card_le hL hH
    _ = _ := by field_simp; ring

/-- Short-range reflection for the actual centered kernel, with both
ordinate signs and the exact Poisson error retained. No reflection estimate
or moment bound is supplied as a hypothesis. -/
theorem centered_shell_short_range (w : MathCollab.Density.ReflectionCutoff)
    {K A : ℕ} (hK : 1 ≤ K) (hA : 1 < A) {η : ℝ} (hη : 0 < η) :
    ∃ C B : ℝ, 0 < C ∧ 0 ≤ B ∧ ∀ T t₀ L H : ℝ,
      1 < T → 0 < L → 0 < H → ∀ W : Finset ℝ,
      T^(((K : ℝ)+1)/(2*K+1)) ≤ W.card →
      (4*H/(Real.pi*L))^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      MathCollab.Density.shellEnergy w L H W ≤
        C*T^η*L*(W.card : ℝ)^2 + B*(W.card : ℝ)^2*L^(2-2*(A:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := reflection_local_energy_short_range hK hη
  obtain ⟨B,hB,href⟩ := MathCollab.Density.uniform_reflection w hA
  let F : ℝ := (20000/Real.pi^2)*(MathCollab.Density.mellinMass w)^2
  have hF : 0 ≤ F := by dsimp [F]; positivity
  refine ⟨1+F*C,4*B^2,by positivity,by positivity,?_⟩
  intro T t₀ L H hT hL hH W hR hlen hW hsep
  have he := (href L H W hL hH).1
  have hb := hbound T t₀ L H hT hL hH W hR hlen hW hsep
  have hm : F*(L^2/H)*MathCollab.Density.localReflectionEnergy L H W ≤
      (F*C)*T^η*L*(W.card : ℝ)^2 := by
    calc
      _ ≤ F*(L^2/H)*(C*T^η*(H/L)*(W.card : ℝ)^2) := by gcongr
      _ = _ := by field_simp
  exact he.trans (add_le_add (hm.trans (by gcongr; linarith)) le_rfl)

end Montgomery.RationalMoment
