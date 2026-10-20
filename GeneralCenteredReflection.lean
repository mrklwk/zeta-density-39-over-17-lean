module
public import GeneralDirichletDifference
public import CenteredMixedTrace

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset MeasureTheory
namespace Montgomery.RationalMoment

/-- The three adjacent-moment terms in the reflected centered matrix. -/
def adjacentCenteredBudget (K : ℕ) (T L R : ℝ) : ℝ :=
  L*R^2+T*R^(2-1/(K:ℝ))+L*T^(1/(2*(K:ℝ)))*R^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))

lemma adjacentCenteredBudget_nonneg (K : ℕ) {T L R : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) (hR : 0 ≤ R) :
    0 ≤ adjacentCenteredBudget K T L R := by
  unfold adjacentCenteredBudget
  positivity

lemma adjacentCenteredBudget_first (K : ℕ) {T L R : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) (hR : 0 ≤ R) :
    L*R^2 ≤ adjacentCenteredBudget K T L R := by
  unfold adjacentCenteredBudget
  have : 0 ≤ T*R^(2-1/(K:ℝ)) := by positivity
  have : 0 ≤ L*T^(1/(2*(K:ℝ)))*R^(2-(2*(K:ℝ)+1)/(2*K*(K+1))) := by positivity
  linarith

theorem reflection_complete_pair_general {K : ℕ} (hK : 1 ≤ K)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ : ℝ, 1 < T → ∀ M : ℕ, 0 < M → (M:ℝ) ≤ 4*T →
      ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      MathCollab.Density.completePairEnergy M W ≤ C*T^η*
        ((M:ℝ)*(W.card:ℝ)^2+(M:ℝ)^2*(W.card:ℝ)^(2-1/(K:ℝ))+
        (M:ℝ)*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))) := by
  obtain ⟨C,hC,hbound⟩ := general_dirichlet_difference hK hη (B:=4) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro T t₀ hT M hM hMT W hW hsep
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
  have hh := hbound T t₀ ((M:ℝ)-1/2) hT hm (by linarith) (Ico M (2*M)) hA W
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
  calc
    _ ≤ C*T^η*((M:ℝ)-1/2)*((W.card:ℝ)^2+((M:ℝ)-1/2)*(W.card:ℝ)^(2-1/(K:ℝ))+
        T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))) := hh
    _ ≤ C*T^η*(M:ℝ)*((W.card:ℝ)^2+(M:ℝ)*(W.card:ℝ)^(2-1/(K:ℝ))+
        T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))) := by gcongr <;> linarith
    _ = _ := by ring

theorem reflection_local_energy_general {K : ℕ} (hK : 1 ≤ K)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ L H : ℝ, 1 < T → 1 ≤ L → 0 < H → H ≤ 2*T →
      ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      MathCollab.Density.localReflectionEnergy L H W ≤ C*T^η*
        ((H/L)*(W.card:ℝ)^2+(H/L)^2*(W.card:ℝ)^(2-1/(K:ℝ))+
        (H/L)*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))) := by
  obtain ⟨C,hC,hbound⟩ := reflection_complete_pair_general hK hη
  refine ⟨120*C,by positivity,?_⟩
  intro T t₀ L H hT hL hH hHT W hW hsep
  have hLp : 0 < L := by linarith
  open MathCollab.Density in
  have hb (M : ℕ) (hM : M ∈ reflectionBlocks L H) :
      (∑' j : ℤ, completePairEnergy M (localSet W H j)) ≤
        12*(C*T^η*((H/L)*(W.card:ℝ)^2+(H/L)^2*(W.card:ℝ)^(2-1/(K:ℝ))+
        (H/L)*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1))))) := by
    obtain ⟨hM0,_,hMhi⟩ := reflectionBlock_scale_bounds hLp hH hM
    have hMU : (M:ℝ) ≤ 2*(H/L) := by
      apply hMhi.trans
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ (by positivity : 0 < Real.pi*L) hLp).mpr
      nlinarith [Real.pi_gt_three,mul_pos hH hLp]
    have hMT : (M:ℝ) ≤ 4*T := by
      have hh : H/L ≤ H := div_le_self hH.le hL
      linarith
    have hh := hbound T t₀ hT M hM0 hMT W hW hsep
    have hm : (M:ℝ)^2 ≤ 4*(H/L)^2 := by nlinarith [sq_nonneg ((M:ℝ)-2*(H/L))]
    have hp : C*T^η*((M:ℝ)*(W.card:ℝ)^2+(M:ℝ)^2*(W.card:ℝ)^(2-1/(K:ℝ))+
        (M:ℝ)*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))) ≤
        4*(C*T^η*((H/L)*(W.card:ℝ)^2+(H/L)^2*(W.card:ℝ)^(2-1/(K:ℝ))+
        (H/L)*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1))))) := by
      calc
        _ ≤ C*T^η*((2*(H/L))*(W.card:ℝ)^2+(4*(H/L)^2)*(W.card:ℝ)^(2-1/(K:ℝ))+
          (2*(H/L))*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))) := by gcongr
        _ ≤ _ := by
          have h1 : 0 ≤ (H/L)*(W.card:ℝ)^2 := by positivity
          have h3 : 0 ≤ (H/L)*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1))) := by positivity
          have hi : (2*(H/L))*(W.card:ℝ)^2+(4*(H/L)^2)*(W.card:ℝ)^(2-1/(K:ℝ))+
              (2*(H/L))*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1))) ≤
              4*((H/L)*(W.card:ℝ)^2+(H/L)^2*(W.card:ℝ)^(2-1/(K:ℝ))+
              (H/L)*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))) := by nlinarith
          exact (mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ C*T^η)).trans_eq (by ring)
    exact (reflection_local_pair_le_three hH M W).trans
      ((mul_le_mul_of_nonneg_left (hh.trans hp) (by norm_num : (0:ℝ) ≤ 3)).trans_eq (by ring))
  open MathCollab.Density in
  calc
    localReflectionEnergy L H W ≤ ∑ _M ∈ reflectionBlocks L H,
        12*(C*T^η*((H/L)*(W.card:ℝ)^2+(H/L)^2*(W.card:ℝ)^(2-1/(K:ℝ))+
        (H/L)*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1))))) := sum_le_sum hb
    _ = ((reflectionBlocks L H).card:ℝ)*(12*(C*T^η*((H/L)*(W.card:ℝ)^2+(H/L)^2*(W.card:ℝ)^(2-1/(K:ℝ))+
        (H/L)*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))))) := by simp
    _ ≤ 10*(12*(C*T^η*((H/L)*(W.card:ℝ)^2+(H/L)^2*(W.card:ℝ)^(2-1/(K:ℝ))+
        (H/L)*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast reflectionBlocks_card_le hLp hH
    _ = _ := by ring

theorem centered_shell_general (w : MathCollab.Density.ReflectionCutoff)
    {K A : ℕ} (hK : 1 ≤ K) (hA : 1 < A) {η : ℝ} (hη : 0 < η) :
    ∃ C B : ℝ, 0 < C ∧ 0 ≤ B ∧ ∀ T t₀ L H : ℝ,
      1 < T → 1 ≤ L → 0 < H → H ≤ 2*T → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      MathCollab.Density.shellEnergy w L H W ≤
        C*T^η*adjacentCenteredBudget K T L W.card + B*(W.card:ℝ)^2*L^(2-2*(A:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := reflection_local_energy_general hK hη
  obtain ⟨B,hB,href⟩ := MathCollab.Density.uniform_reflection w hA
  let F : ℝ := (20000/Real.pi^2)*(MathCollab.Density.mellinMass w)^2
  have hF : 0 ≤ F := by dsimp [F]; positivity
  refine ⟨1+2*F*C,4*B^2,by positivity,by positivity,?_⟩
  intro T t₀ L H hT hL hH hHT W hW hsep
  have hLp : 0 < L := by linarith
  have he := (href L H W hLp hH).1
  have hb := hbound T t₀ L H hT hL hH hHT W hW hsep
  have hm : F*(L^2/H)*MathCollab.Density.localReflectionEnergy L H W ≤
      (2*F*C)*T^η*adjacentCenteredBudget K T L W.card := by
    calc
      _ ≤ F*(L^2/H)*(C*T^η*((H/L)*(W.card:ℝ)^2+(H/L)^2*(W.card:ℝ)^(2-1/(K:ℝ))+
          (H/L)*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1))))) := by gcongr
      _ = (F*C)*T^η*(L*(W.card:ℝ)^2+H*(W.card:ℝ)^(2-1/(K:ℝ))+
          L*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))) := by field_simp
      _ ≤ (F*C)*T^η*(L*(W.card:ℝ)^2+(2*T)*(W.card:ℝ)^(2-1/(K:ℝ))+
          L*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))) := by gcongr
      _ ≤ _ := by
        unfold adjacentCenteredBudget
        have h1 : 0 ≤ L*(W.card:ℝ)^2 := by positivity
        have h3 : 0 ≤ L*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1))) := by positivity
        have hi : L*(W.card:ℝ)^2+(2*T)*(W.card:ℝ)^(2-1/(K:ℝ))+
            L*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1))) ≤
            2*(L*(W.card:ℝ)^2+T*(W.card:ℝ)^(2-1/(K:ℝ))+
            L*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))) := by nlinarith
        exact (mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ F*C*T^η)).trans_eq (by ring)
  exact he.trans (add_le_add (hm.trans (by
    apply mul_le_mul_of_nonneg_right _ (adjacentCenteredBudget_nonneg K (by linarith) (by linarith) (Nat.cast_nonneg _))
    gcongr
    linarith)) le_rfl)

end Montgomery.RationalMoment
