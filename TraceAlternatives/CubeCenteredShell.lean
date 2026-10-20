module
public import TraceAlternatives.CubeShellBudget
public import DensityEnergyGM.DifferenceEnergyGeometry

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

/-- The original ordered energy absorbs quadratic near and shell errors. -/
theorem card_sq_le_twice_cubeCenteredBudget {T t₀ L : ℝ}
    (hT : 2 ≤ T) (hL : 0 ≤ L) (W : Finset ℝ)
    (hW : ∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) :
    (W.card : ℝ)^2 ≤ 2*cubeCenteredBudget T L W.card (discreteAdditiveEnergy W) := by
  have hBase : InBaseInterval T (translateSet t₀ W) := by
    intro t ht
    obtain ⟨u,hu,rfl⟩ := mem_image.mp ht
    obtain ⟨hl,hh⟩ := hW u hu
    exact ⟨by linarith,by linarith⟩
  have hE := card_four_le_four_height_energy hT hBase
  rw [translateSet_card,discrete_energy_translateSet] at hE
  have hEn : (0:ℝ) ≤ discreteAdditiveEnergy W := Nat.cast_nonneg _
  have hTp : 0 < T := by linarith
  have hEsq := Real.sq_sqrt hEn
  have hProd : 0 ≤ (T-1)*(T*(discreteAdditiveEnergy W:ℝ)) :=
    mul_nonneg (by linarith) (mul_nonneg hTp.le hEn)
  have hSq : (2*T*Real.sqrt (discreteAdditiveEnergy W:ℝ))^2 =
      4*T^2*(discreteAdditiveEnergy W:ℝ) := by nlinarith [hEsq]
  have hR : (W.card:ℝ)^2 ≤ 2*T*Real.sqrt (discreteAdditiveEnergy W:ℝ) := by
    have hNon : 0 ≤ 2*T*Real.sqrt (discreteAdditiveEnergy W:ℝ) := by positivity
    have hSquares : ((W.card:ℝ)^2)^2 ≤ (2*T*Real.sqrt (discreteAdditiveEnergy W:ℝ))^2 := by
      nlinarith only [hE,hProd,hSq]
    exact (sq_le_sq₀ (sq_nonneg _) hNon).mp hSquares
  rw [Real.sqrt_eq_rpow] at hR
  have hEupper : (discreteAdditiveEnergy W:ℝ) ≤ (W.card:ℝ)^4 := by
    have hh := approxAddEnergy_le_card_pow_four 1 W
    rw [native_approx_energy_eq] at hh
    exact_mod_cast hh
  have hSixth : (discreteAdditiveEnergy W:ℝ)^(1/6:ℝ) ≤ (W.card:ℝ)^(2/3:ℝ) := by
    have hh := Real.rpow_le_rpow hEn hEupper (by norm_num : (0:ℝ)≤1/6)
    rw [← Real.rpow_natCast_mul (Nat.cast_nonneg W.card)] at hh
    norm_num at hh
    exact hh
  have hRoot : (discreteAdditiveEnergy W:ℝ)^(1/2:ℝ) ≤
      (W.card:ℝ)^(2/3:ℝ)*(discreteAdditiveEnergy W:ℝ)^(1/3:ℝ) := by
    by_cases hz : (discreteAdditiveEnergy W:ℝ)=0
    · simp [hz]
    have hp : 0 < (discreteAdditiveEnergy W:ℝ) := lt_of_le_of_ne hEn (Ne.symm hz)
    have hh := mul_le_mul_of_nonneg_right hSixth
      (Real.rpow_nonneg hEn (1/3:ℝ))
    rw [← Real.rpow_add hp] at hh
    norm_num at hh
    exact hh
  have hh := mul_le_mul_of_nonneg_left hRoot (show 0≤2*T by positivity)
  have hOther : 0 ≤ L*T^(1/3:ℝ)*(W.card:ℝ)^(2/3:ℝ)*
      (discreteAdditiveEnergy W:ℝ)^(1/3:ℝ) := by positivity
  unfold cubeCenteredBudget
  nlinarith only [hR,hh,hOther]


theorem centered_shell_cube (w : MathCollab.Density.ReflectionCutoff)
    {A : ℕ} (hA : 1 < A) {η : ℝ} (hη : 0 < η) :
    ∃ C B : ℝ, 0 < C ∧ 0 ≤ B ∧ ∀ T t₀ L H : ℝ,
      2 ≤ T → Real.sqrt T ≤ L → 0 < H → H ≤ 2*T → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      MathCollab.Density.shellEnergy w L H W ≤
        C*T^η*cubeCenteredBudget T L W.card (discreteAdditiveEnergy W)+
          B*(W.card:ℝ)^2*L^(2-2*(A:ℝ)) := by
  obtain ⟨C,hC,hBound⟩ := reflection_local_energy_cube hη
  obtain ⟨B,hB,hRef⟩ := MathCollab.Density.uniform_reflection w hA
  let F : ℝ := (20000/Real.pi^2)*(MathCollab.Density.mellinMass w)^2
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  refine ⟨1+2*F*C,4*B^2,by positivity,by positivity,?_⟩
  intro T t₀ L H hT hL hH hHT W hW hSep
  have hTp : 0 < T := by linarith
  have hLp : 0 < L := (Real.sqrt_pos.mpr hTp).trans_le hL
  have hReflected := (hRef L H W hLp hH).1
  have hLocal := hBound T t₀ L H hT hL hH hHT W hW hSep
  have hScale := cube_shell_budget_le hTp hLp hH hHT
    (Nat.cast_nonneg W.card) (Nat.cast_nonneg (discreteAdditiveEnergy W))
  have hMain : F*(L^2/H)*MathCollab.Density.localReflectionEnergy L H W ≤
      (2*F*C)*T^η*cubeCenteredBudget T L W.card (discreteAdditiveEnergy W) := by
    calc
      _ ≤ F*(L^2/H)*(C*T^η*cubeLocalReflectionBudget T L H W.card (discreteAdditiveEnergy W)) :=
        mul_le_mul_of_nonneg_left hLocal (by positivity)
      _ = (F*C*T^η)*(L^2/H*cubeLocalReflectionBudget T L H W.card (discreteAdditiveEnergy W)) := by ring
      _ ≤ (F*C*T^η)*(2*cubeCenteredBudget T L W.card (discreteAdditiveEnergy W)) :=
        mul_le_mul_of_nonneg_left hScale (by positivity)
      _ = _ := by ring
  have hBudget := cubeCenteredBudget_nonneg hTp.le hLp.le
    (Nat.cast_nonneg W.card) (Nat.cast_nonneg (discreteAdditiveEnergy W))
  have hCoeff : (2*F*C)*T^η*cubeCenteredBudget T L W.card (discreteAdditiveEnergy W) ≤
      (1+2*F*C)*T^η*cubeCenteredBudget T L W.card (discreteAdditiveEnergy W) := by
    gcongr
    linarith
  exact hReflected.trans (add_le_add (hMain.trans hCoeff) le_rfl)

end Montgomery.RationalMoment
