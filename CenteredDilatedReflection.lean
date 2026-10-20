module
public import CenteredShortReflection
public import RationalDilatedDifference

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
namespace Montgomery.RationalMoment

theorem reflection_complete_pair_dilated_short_range {K : ℕ} (hK : 1 ≤ K)
    {η B : ℝ} (hη : 0 < η) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t₀ : ℝ), 1 < T → ∀ M : ℕ, 0 < M → ∀ U : ℝ, 0 ≤ U → (M:ℝ) ≤ B*U →
      ∀ W : Finset ℝ,
      T^(((K : ℝ)+1)/(2*K+1)) ≤ W.card → U^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      MathCollab.Density.completePairEnergy M W ≤ C*T^η*U*(W.card : ℝ)^2 := by
  obtain ⟨C,hC,hbound⟩ := dilated_dyadic_dirichlet_difference hK hη hB
  refine ⟨C,hC,?_⟩
  intro T t₀ hT M hM U hU hMU W hR hUR hW hsep
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
  have hh := hbound T t₀ ((M:ℝ)-1/2) U hT hm hU (by linarith) (Ico M (2*M)) hA W hR hUR
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
  exact hh

/-- Fixed dilations in the reflected band are absorbed in the constant,
not imposed on the cardinality threshold. -/
theorem reflection_local_energy_dilated_short_range {K : ℕ} (hK : 1 ≤ K)
    {η B : ℝ} (hη : 0 < η) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ L H : ℝ, 1 < T → 0 < L → 0 < H →
      ∀ W : Finset ℝ,
      T^(((K:ℝ)+1)/(2*K+1)) ≤ W.card → (H/(B*L))^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      MathCollab.Density.localReflectionEnergy L H W ≤
        C*T^η*(H/L)*(W.card:ℝ)^2 := by
  obtain ⟨C,hC,hbound⟩ := reflection_complete_pair_dilated_short_range hK hη
    (B := 2*B) (by linarith)
  have hBp : 0 < B := by linarith
  refine ⟨30*C,by positivity,?_⟩
  intro T t₀ L H hT hL hH W hR hlen hW hsep
  let U : ℝ := H/(B*L)
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hUL : U ≤ H/L := by
    dsimp [U]
    exact div_le_div_of_nonneg_left hH.le hL (by nlinarith)
  open MathCollab.Density in
  have hb (M : ℕ) (hM : M ∈ reflectionBlocks L H) :
      (∑' j : ℤ, completePairEnergy M (localSet W H j)) ≤
        3*(C*T^η*(H/L)*(W.card:ℝ)^2) := by
    obtain ⟨hM0,_,hMhi⟩ := reflectionBlock_scale_bounds hL hH hM
    have hMU : (M:ℝ) ≤ (2*B)*U := by
      have hpi : 4*H/(Real.pi*L) ≤ 2*H/L := by
        apply (div_le_div_iff₀ (by positivity : 0 < Real.pi*L) hL).mpr
        nlinarith [Real.pi_gt_three,mul_pos hH hL]
      have he : (2*B)*U=2*H/L := by dsimp [U]; field_simp
      rw [he]
      exact hMhi.trans hpi
    refine (reflection_local_pair_le_three hH M W).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 3)
    exact (hbound T t₀ hT M hM0 U hU hMU W hR hlen hW hsep).trans (by gcongr)
  open MathCollab.Density in
  calc
    localReflectionEnergy L H W ≤ ∑ _M ∈ reflectionBlocks L H,
        3*(C*T^η*(H/L)*(W.card:ℝ)^2) := sum_le_sum hb
    _ = ((reflectionBlocks L H).card:ℝ)*(3*(C*T^η*(H/L)*(W.card:ℝ)^2)) := by simp
    _ ≤ 10*(3*(C*T^η*(H/L)*(W.card:ℝ)^2)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast reflectionBlocks_card_le hL hH
    _ = _ := by ring

theorem centered_shell_dilated_short_range (w : MathCollab.Density.ReflectionCutoff)
    {K A : ℕ} (hK : 1 ≤ K) (hA : 1 < A) {η D : ℝ} (hη : 0 < η) (hD : 1 ≤ D) :
    ∃ C B : ℝ, 0 < C ∧ 0 ≤ B ∧ ∀ T t₀ L H : ℝ,
      1 < T → 0 < L → 0 < H → ∀ W : Finset ℝ,
      T^(((K : ℝ)+1)/(2*K+1)) ≤ W.card →
      (H/(D*L))^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      MathCollab.Density.shellEnergy w L H W ≤
        C*T^η*L*(W.card : ℝ)^2 + B*(W.card : ℝ)^2*L^(2-2*(A:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := reflection_local_energy_dilated_short_range hK hη hD
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
