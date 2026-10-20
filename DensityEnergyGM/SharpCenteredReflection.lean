module
public import DensityEnergyGM.SharpReflectionSecond

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
namespace Montgomery.RationalMoment

def sharpLocalReflectionBudget (T L H R E : ℝ) : ℝ :=
  (H/L)^2*E^(1/2:ℝ)+R*E^(1/4:ℝ)*
    ((H/L)^(9/5:ℝ)+T^(1/4:ℝ)*(H/L)^(6/5:ℝ))

theorem reflection_local_energy_sharp {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ,0<C ∧ ∀ T t₀ L H : ℝ,2≤T → Real.sqrt T≤L → 0<H → H≤2*T →
      ∀ W : Finset ℝ,(∀ t∈W,t∈Set.Icc t₀ (t₀+T)) →
        (∀ t∈W,∀ u∈W,t≠u → 1≤|t-u|) →
        MathCollab.Density.localReflectionEnergy L H W ≤
          C*T^η*sharpLocalReflectionBudget T L H W.card (discreteAdditiveEnergy W) := by
  obtain ⟨C,hC,hBound⟩ := reflection_complete_pair_energy_sharp hη
  refine ⟨120*C,by positivity,?_⟩
  intro T t₀ L H hT hL hH hHT W hW hSep
  have hTp : 0<T := by linarith
  have hRoot : 0<Real.sqrt T := Real.sqrt_pos.mpr hTp
  have hLp : 0<L := hRoot.trans_le hL
  let X : ℝ := H/L
  have hX : 0<X := div_pos hH hLp
  have hXbound : X≤2*Real.sqrt T := by
    apply (div_le_iff₀ hLp).mpr
    nlinarith [Real.sq_sqrt hTp.le,
      mul_nonneg (sub_nonneg.mpr hL) (Real.sqrt_nonneg T)]
  let S := sharpLocalReflectionBudget T L H W.card (discreteAdditiveEnergy W)
  have hS : 0≤S := by dsimp [S,sharpLocalReflectionBudget]; positivity
  open MathCollab.Density in
  have hBlock (M : ℕ) (hM : M∈reflectionBlocks L H) :
      (∑' j : ℤ,completePairEnergy M (localSet W H j)) ≤ 12*(C*T^η*S) := by
    obtain ⟨hM0,_,hMhi⟩ := reflectionBlock_scale_bounds hLp hH hM
    have hMU : (M:ℝ)≤2*X := by
      apply hMhi.trans
      dsimp [X]
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ (by positivity : 0<Real.pi*L) hLp).mpr
      nlinarith [Real.pi_gt_three,mul_pos hH hLp]
    have hMT : (M:ℝ)≤4*Real.sqrt T := by linarith
    have h := hBound T t₀ hT M hM0 hMT W hW hSep
    have hSq : (M:ℝ)^2≤4*X^2 := by
      have hh := pow_le_pow_left₀ (Nat.cast_nonneg M : (0:ℝ)≤M) hMU 2
      nlinarith
    have hPow (q : ℝ) (hq : 0≤q) (hq2 : q≤2) : (M:ℝ)^q≤4*X^q := by
      calc
        _ ≤ (2*X)^q := Real.rpow_le_rpow (Nat.cast_nonneg M) hMU hq
        _ = (2:ℝ)^q*X^q := Real.mul_rpow (by norm_num) hX.le
        _ ≤ 4*X^q := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hq2
          norm_num at hh
          exact hh
    have hMono : (M:ℝ)^2*(discreteAdditiveEnergy W:ℝ)^(1/2:ℝ)+
        (W.card:ℝ)*(discreteAdditiveEnergy W:ℝ)^(1/4:ℝ)*
          ((M:ℝ)^(9/5:ℝ)+T^(1/4:ℝ)*(M:ℝ)^(6/5:ℝ)) ≤ 4*S := by
      calc
        _ ≤ (4*X^2)*(discreteAdditiveEnergy W:ℝ)^(1/2:ℝ)+
            (W.card:ℝ)*(discreteAdditiveEnergy W:ℝ)^(1/4:ℝ)*
              ((4*X^(9/5:ℝ))+T^(1/4:ℝ)*(4*X^(6/5:ℝ))) := by
          gcongr
          · exact hPow _ (by norm_num) (by norm_num)
          · exact hPow _ (by norm_num) (by norm_num)
        _ = _ := by dsimp [S,sharpLocalReflectionBudget,X]; ring
    exact (reflection_local_pair_le_three hH M W).trans
      ((mul_le_mul_of_nonneg_left
        (h.trans (mul_le_mul_of_nonneg_left hMono (by positivity)))
        (by norm_num : (0:ℝ)≤3)).trans_eq (by ring))
  open MathCollab.Density in
  calc
    localReflectionEnergy L H W ≤ ∑ _M∈reflectionBlocks L H,12*(C*T^η*S) := sum_le_sum hBlock
    _ = ((reflectionBlocks L H).card:ℝ)*(12*(C*T^η*S)) := by simp
    _ ≤ 10*(12*(C*T^η*S)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast reflectionBlocks_card_le hLp hH
    _ = _ := by ring

end Montgomery.RationalMoment
