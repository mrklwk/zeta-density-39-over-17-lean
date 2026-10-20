module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.SargosQuarticPhase

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                         
                                                                          
                                                                          

noncomputable section

open Set Filter MeasureTheory Expdb GafniTao
open scoped ContDiff Topology FourierTransform BigOperators

namespace TaoTrudgianYang2025

theorem sargos_ford_character_eq_fourier (x : ℝ) :
    fordAdditiveCharacter x = (𝐞 x : ℂ) := by
  rw [fordAdditiveCharacter,Real.fourierChar_apply]
  congr 1
  push_cast
  ring

def sargosQuarticWeightedKernel (χ : ℝ → ℝ) (N α γ x : ℝ) : ℂ :=
  (χ (x/N) : ℂ)*(𝐞 (sargosQuarticPhase α γ x) : ℂ)

theorem sargosQuarticWeightedKernel_contDiff {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (N α γ : ℝ) :
    ContDiff ℝ ∞ (sargosQuarticWeightedKernel χ N α γ) := by
  unfold sargosQuarticWeightedKernel sargosQuarticPhase
  simp only [Real.fourierChar_apply]
  have hw : ContDiff ℝ ∞ (fun x : ℝ => χ (x/N)) := hχ.comp (contDiff_id.div_const N)
  have hp : ContDiff ℝ ∞ (fun x : ℝ => 2*Real.pi*(α*x^2+γ*x^4)) := by fun_prop
  exact (Complex.ofRealCLM.contDiff.comp hw).mul
    (((Complex.ofRealCLM.contDiff.comp hp).mul contDiff_const).cexp)

theorem sargosQuarticWeightedKernel_zero_of_not_mem {χ : ℝ → ℝ} {N x : ℝ}
    (hs : tsupport χ ⊆ Ioo 1 2) (hN : 0 < N) (hx : x ∉ Icc N (2*N)) (α γ : ℝ) :
    sargosQuarticWeightedKernel χ N α γ x = 0 := by
  have hnot : x/N ∉ tsupport χ := by
    intro h
    have hu := hs h
    apply hx
    exact ⟨by simpa only [one_mul] using ((lt_div_iff₀ hN).mp hu.1).le,
      ((div_lt_iff₀ hN).mp hu.2).le⟩
  simp only [sargosQuarticWeightedKernel,image_eq_zero_of_notMem_tsupport hnot,
    Complex.ofReal_zero,zero_mul]

theorem sargosQuarticWeightedKernel_hasCompactSupport {χ : ℝ → ℝ} {N : ℝ}
    (hs : tsupport χ ⊆ Ioo 1 2) (hN : 0 < N) (α γ : ℝ) :
    HasCompactSupport (sargosQuarticWeightedKernel χ N α γ) :=
  HasCompactSupport.intro isCompact_Icc
    (fun _ hx => sargosQuarticWeightedKernel_zero_of_not_mem hs hN hx α γ)

end TaoTrudgianYang2025
