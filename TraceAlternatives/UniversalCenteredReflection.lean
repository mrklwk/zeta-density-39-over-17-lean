module
public import TraceAlternatives.UniversalReflectionSecond

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
namespace Montgomery.RationalMoment

def universalLocalReflectionBudget (T L H R E : ℝ) : ℝ :=
  universalShortProfile T (H/L) R E

theorem reflection_local_energy_universal {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ,0<C ∧ ∀ T t₀ L H : ℝ,2≤T → Real.sqrt T≤L → 0<H → H≤2*T →
      ∀ W : Finset ℝ,(∀ t∈W,t∈Set.Icc t₀ (t₀+T)) →
        (∀ t∈W,∀ u∈W,t≠u → 1≤|t-u|) →
        MathCollab.Density.localReflectionEnergy L H W ≤
          C*T^η*universalLocalReflectionBudget T L H W.card (discreteAdditiveEnergy W) := by
  obtain ⟨C,hC,hBound⟩ := reflection_complete_pair_energy_universal hη
  refine ⟨240*C,by positivity,?_⟩
  intro T t₀ L H hT hL hH hHT W hW _hSep
  have hTp : 0<T := by linarith
  have hRoot : 0<Real.sqrt T := Real.sqrt_pos.mpr hTp
  have hLp : 0<L := hRoot.trans_le hL
  let X : ℝ := H/L
  have hX : 0<X := div_pos hH hLp
  have hXbound : X≤2*Real.sqrt T := by
    apply (div_le_iff₀ hLp).mpr
    nlinarith [Real.sq_sqrt hTp.le,
      mul_nonneg (sub_nonneg.mpr hL) (Real.sqrt_nonneg T)]
  let S := universalLocalReflectionBudget T L H W.card (discreteAdditiveEnergy W)
  have hS : 0≤S := by dsimp [S,universalLocalReflectionBudget,universalShortProfile,universalShortSublinearProfile]; positivity
  open MathCollab.Density in
  have hBlock (M : ℕ) (hM : M∈reflectionBlocks L H) :
      (∑' j : ℤ,completePairEnergy M (localSet W H j)) ≤ 24*(C*T^η*S) := by
    obtain ⟨hM0,_,hMhi⟩ := reflectionBlock_scale_bounds hLp hH hM
    have hMU : (M:ℝ)≤2*X := by
      apply hMhi.trans
      dsimp [X]
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ (by positivity : 0<Real.pi*L) hLp).mpr
      nlinarith [Real.pi_gt_three,mul_pos hH hLp]
    have hMT : (M:ℝ)≤4*Real.sqrt T := by linarith
    have h := hBound T t₀ hT M hM0 hMT W hW
    have hMono : universalShortProfile T M W.card (discreteAdditiveEnergy W) ≤ 8*S := by
      have hh := universalShortProfile_mono hTp.le (by linarith : T≤2*T)
        (Nat.cast_nonneg M) hMU (Nat.cast_nonneg W.card) (Nat.cast_nonneg (discreteAdditiveEnergy W))
      have hs := universalShortProfile_scale (by norm_num : (1:ℝ)≤2) hTp.le hX.le
        (Nat.cast_nonneg W.card) (Nat.cast_nonneg (discreteAdditiveEnergy W))
      norm_num only [pow_succ,pow_zero,mul_one] at hs
      exact hh.trans hs
    have hGrouped : completePairEnergy M W ≤ C*T^η*
        universalShortProfile T M W.card (discreteAdditiveEnergy W) := h
    exact (reflection_local_pair_le_three hH M W).trans
      ((mul_le_mul_of_nonneg_left
        (hGrouped.trans (mul_le_mul_of_nonneg_left hMono (by positivity)))
        (by norm_num : (0:ℝ)≤3)).trans_eq (by ring))
  open MathCollab.Density in
  calc
    localReflectionEnergy L H W ≤ ∑ _M∈reflectionBlocks L H,24*(C*T^η*S) := sum_le_sum hBlock
    _ = ((reflectionBlocks L H).card:ℝ)*(24*(C*T^η*S)) := by simp
    _ ≤ 10*(24*(C*T^η*S)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast reflectionBlocks_card_le hLp hH
    _ = _ := by ring

end Montgomery.RationalMoment
