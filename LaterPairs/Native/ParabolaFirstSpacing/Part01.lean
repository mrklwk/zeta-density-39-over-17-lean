module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import MathCollab.Density.Stronger.Atkinson.FiniteWeightedGram
public import TaoTrudgianYang2025.FourierDecayCore
public import MathCollab.Density.Stronger.Atkinson.SeparatedReciprocal
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.ContinuousPhaseAbel
public import LaterPairs.Native.ContinuousSecondDerivativeRange
public import LaterPairs.Native.ExponentPairShiftJets
public import LaterPairs.Native.FiniteSmoothThirdDerivative
public import LaterPairs.Native.IntegerIntervalCount
public import LaterPairs.Native.RobertSargosCubicJets
public import LaterPairs.Native.RobertSargosDisplacementSums
public import LaterPairs.Native.RobertSargosExponentPair
public import LaterPairs.Native.SargosDoubleLargeSieve
public import LaterPairs.Native.SargosLocalAffineJets
public import LaterPairs.Native.SargosPlanarIntegral
public import LaterPairs.Native.SargosPlanarRegularity
public import LaterPairs.Native.SargosPrefixFourthMajorant
public import LaterPairs.Native.SargosQuarticKernelJets

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxErrors 1000
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

 
                                        

                                                                           
                                                                              
                                                                              
                                                                         
                                                    

                                                                         
                                                                               
                                                                              
                                                                           
                                                                               
                                                                               
                                                                               
                                                                                
                                                                             
                                                                             
                                                                       
                                                                      
                                                                          
                                                                     
                                                                          
                                                                     
                                                                        
                                                                          
                                                                      
                                                                     
                                                                           
                                                                  
                                                                       
                                                                            
                                                                         
                                                                         
                                                                               
                                                                         
                                                                            
                                                                      
                                                                       
                                                                        
                                                                        
                                                                         
                                                                      
                                                                           
                                                                        
                                                                              
                                                                             
                                                                      
                                                                            
                                                  


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ComplexConjugate
namespace TaoTrudgianYang2025

theorem parabola_sixth_frequency_gap
    {x x' y₁ y₂ y₃ y₄ w ρ b : ℝ}
    (hw : 0 ≤ w) (hρ : 0 < ρ)
    (h₁ : y₁ ∈ Icc 0 w) (h₂ : y₂ ∈ Icc 0 w)
    (h₃ : y₃ ∈ Icc 0 w) (h₄ : y₄ ∈ Icc 0 w)
    (hsep : ρ ≤ |x+x'|)
    (hgap : (b+2*w^2)/ρ < |x-x'|) :
    b < |x^2+y₁^2+y₂^2-(x'^2+y₃^2+y₄^2)| := by
  have hs₁ : y₁^2 ≤ w^2 := by nlinarith [h₁.1,h₁.2]
  have hs₂ : y₂^2 ≤ w^2 := by nlinarith [h₂.1,h₂.2]
  have hs₃ : y₃^2 ≤ w^2 := by nlinarith [h₃.1,h₃.2]
  have hs₄ : y₄^2 ≤ w^2 := by nlinarith [h₄.1,h₄.2]
  by_contra hn
  have hf := abs_le.mp (le_of_not_gt hn)
  have hd : |x^2-x'^2| ≤ b+2*w^2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg y₁,sq_nonneg y₂,sq_nonneg y₃,sq_nonneg y₄]
  have he : |x-x'| * |x+x'| = |x^2-x'^2| := by
    rw [← abs_mul]
    congr 1
    ring
  have hg := (div_lt_iff₀ hρ).mp hgap
  have hm := mul_le_mul_of_nonneg_left hsep (abs_nonneg (x-x'))
  nlinarith only [hd,he,hg,hm]

theorem parabola_same_interval_separation
    {x x' d u ν : ℝ} (hν : 0 ≤ ν)
    (hu : u ≤ ν) (hd : 3*ν ≤ |d|)
    (hx : x ∈ Icc d (d+u)) (hx' : x' ∈ Icc d (d+u)) :
    4*ν ≤ |x+x'| := by
  rcases le_total 0 d with h | h
  · rw [abs_of_nonneg h] at hd
    have hp : 0 ≤ x+x' := by linarith [hx.1,hx'.1]
    rw [abs_of_nonneg hp]
    linarith [hx.1,hx'.1]
  · rw [abs_of_nonpos h] at hd
    have hp : x+x' ≤ 0 := by linarith [hx.2,hx'.2]
    rw [abs_of_nonpos hp]
    linarith [hx.2,hx'.2]

theorem planarSum_mul {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (z : ι → ℂ) (w : κ → ℂ)
    (u v : ι → ℝ) (p q : κ → ℝ) (α γ : ℝ) :
    sargosPlanarSum S z u v α γ * sargosPlanarSum T w p q α γ =
      sargosPlanarSum (S ×ˢ T) (fun i => z i.1*w i.2)
        (fun i => u i.1+p i.2) (fun i => v i.1+q i.2) α γ := by
  unfold sargosPlanarSum
  rw [Finset.sum_mul_sum,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  calc
    _ = (z i*w j)*(fordAdditiveCharacter (u i*α+v i*γ)*
        fordAdditiveCharacter (p j*α+q j*γ)) := by ring
    _ = _ := by
      rw [← fordAdditiveCharacter_add]
      congr 2
      ring

private theorem banded_real_sum_le (J : Finset ℤ) (G : ℤ → ℤ → ℝ)
    (E : ℤ → ℝ) (m : ℕ)
    (hE : ∀ i ∈ J, 0 ≤ E i)
    (hG : ∀ i ∈ J, ∀ j ∈ J, 2*G i j ≤ E i+E j)
    (hzero : ∀ i ∈ J, ∀ j ∈ J, (m : ℤ) < |i-j| → G i j = 0) :
    ∑ i ∈ J, ∑ j ∈ J, G i j ≤ (2*(m : ℝ)+1)*∑ i ∈ J, E i := by
  classical
  have hcard (i : ℤ) : ((J.filter (fun j => |i-j| ≤ (m : ℤ))).card : ℝ) ≤
      2*(m : ℝ)+1 := by
    have hs : J.filter (fun j => |i-j| ≤ (m : ℤ)) ⊆
        Finset.Icc (i-(m : ℤ)) (i+(m : ℤ)) := by
      intro j hj
      have hj' := abs_le.mp (Finset.mem_filter.mp hj).2
      apply Finset.mem_Icc.mpr
      constructor <;> omega
    have hn : (J.filter (fun j => |i-j| ≤ (m : ℤ))).card ≤ 2*m+1 := by
      calc
        _ ≤ (Finset.Icc (i-(m : ℤ)) (i+(m : ℤ))).card := Finset.card_le_card hs
        _ = 2*m+1 := by rw [Int.card_Icc]; omega
    exact_mod_cast hn
  let A : ℤ → ℤ → ℝ := fun i j => if |i-j| ≤ (m : ℤ) then E i else 0
  have ha : (∑ i ∈ J, ∑ j ∈ J, A i j) ≤
      (2*(m : ℝ)+1)*∑ i ∈ J, E i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    calc
      _ = ((J.filter (fun j => |i-j| ≤ (m : ℤ))).card : ℝ)*E i := by
        dsimp [A]
        rw [← Finset.sum_filter]
        simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (hcard i) (hE i hi)
  have hab : 2*(∑ i ∈ J, ∑ j ∈ J, G i j) ≤
      (∑ i ∈ J, ∑ j ∈ J, A i j)+(∑ i ∈ J, ∑ j ∈ J, A j i) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    dsimp [A]
    rw [abs_sub_comm j i]
    by_cases h : |i-j| ≤ (m : ℤ)
    · simp only [ite_eq_left h]
      exact hG i hi j hj
    · simp only [ite_eq_right h,hzero i hi j hj (lt_of_not_ge h),mul_zero,add_zero,le_refl]
  have hswap : (∑ i ∈ J, ∑ j ∈ J, A j i) = ∑ i ∈ J, ∑ j ∈ J, A i j :=
    Finset.sum_comm
  rw [hswap] at hab
  linarith


private theorem parabola_product_sum {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) (α γ : ℝ) :
    sargosPlanarSum ((S ×ˢ V) ×ˢ V)
      (fun ij => z ij.1.1*c ij.1.2*c ij.2)
      (fun ij => x ij.1.1+y ij.1.2+y ij.2)
      (fun ij => (x ij.1.1)^2+(y ij.1.2)^2+(y ij.2)^2) α γ =
    sargosPlanarSum S z x (fun i => (x i)^2) α γ *
      (sargosPlanarSum V c y (fun k => (y k)^2) α γ)^2 := by
  rw [← planarSum_mul (S ×ˢ V) V (fun ij => z ij.1*c ij.2) c
    (fun ij => x ij.1+y ij.2) (fun ij => (x ij.1)^2+(y ij.2)^2) y
    (fun k => (y k)^2) α γ,
    ← planarSum_mul S V z c x (fun i => (x i)^2) y (fun k => (y k)^2) α γ]
  ring

private theorem parabola_family_product_sum {ι τ : Type*}
    (J : Finset ℤ) (S : ℤ → Finset ι) (V : Finset τ)
    (z : ℤ → ι → ℂ) (c : τ → ℂ)
    (x : ℤ → ι → ℝ) (y : τ → ℝ) (α γ : ℝ) :
    sargosPlanarSum (J.sigma (fun i => (S i ×ˢ V) ×ˢ V))
      (fun ij => z ij.1 ij.2.1.1*c ij.2.1.2*c ij.2.2)
      (fun ij => x ij.1 ij.2.1.1+y ij.2.1.2+y ij.2.2)
      (fun ij => (x ij.1 ij.2.1.1)^2+(y ij.2.1.2)^2+(y ij.2.2)^2) α γ =
    sargosPlanarSum (J.sigma S) (fun ij => z ij.1 ij.2)
      (fun ij => x ij.1 ij.2) (fun ij => (x ij.1 ij.2)^2) α γ *
      (sargosPlanarSum V c y (fun k => (y k)^2) α γ)^2 := by
  change (∑ ij ∈ J.sigma (fun i => (S i ×ˢ V) ×ˢ V), _) = _
  rw [Finset.sum_sigma]
  change (∑ i ∈ J, sargosPlanarSum ((S i ×ˢ V) ×ˢ V)
    (fun ij => z i ij.1.1*c ij.1.2*c ij.2)
    (fun ij => x i ij.1.1+y ij.1.2+y ij.2)
    (fun ij => (x i ij.1.1)^2+(y ij.1.2)^2+(y ij.2)^2) α γ) = _
  simp_rw [parabola_product_sum]
  rw [← Finset.sum_mul]
  congr 1
  simp only [sargosPlanarSum,Finset.sum_sigma]

private theorem parabola_block_gap_closed {i j : ℤ} {m : ℕ} {x x' d w ν : ℝ}
    (hm : 2/ν ≤ (m : ℝ))
    (hx : x ∈ Icc (d+w^2*(i : ℝ)) (d+w^2*((i : ℝ)+1)))
    (hx' : x' ∈ Icc (d+w^2*(j : ℝ)) (d+w^2*((j : ℝ)+1)))
    (hij : (m : ℤ) < |i-j|) :
    2*w^2/ν ≤ |x-x'| := by
  have hm' : 2*w^2/ν ≤ w^2*(m : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hm (sq_nonneg w)
    convert h using 1
    ring
  rcases le_total i j with h | h
  · have hji : (m : ℤ)+1 ≤ j-i := by
      rw [abs_of_nonpos (sub_nonpos.mpr h)] at hij
      omega
    have hji' : (m : ℝ)+1 ≤ (j : ℝ)-(i : ℝ) := by exact_mod_cast hji
    have hp := mul_le_mul_of_nonneg_left hji' (sq_nonneg w)
    have hd : w^2*(m : ℝ) ≤ x'-x := by nlinarith [hx.2,hx'.1]
    exact (hm'.trans hd).trans (by rw [abs_sub_comm]; exact le_abs_self _)
  · have hij' : (m : ℤ)+1 ≤ i-j := by
      rw [abs_of_nonneg (sub_nonneg.mpr h)] at hij
      omega
    have hij'' : (m : ℝ)+1 ≤ (i : ℝ)-(j : ℝ) := by exact_mod_cast hij'
    have hp := mul_le_mul_of_nonneg_left hij'' (sq_nonneg w)
    have hd : w^2*(m : ℝ) ≤ x-x' := by nlinarith [hx.1,hx'.2]
    exact (hm'.trans hd).trans (le_abs_self _)

end TaoTrudgianYang2025
noncomputable section
open MeasureTheory FourierTransform SchwartzMap Set GafniTao
open scoped ComplexConjugate Convolution ContDiff
namespace TaoTrudgianYang2025
private def cutoffConjReflect (g : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (LinearIsometryEquiv.neg ℝ (E := ℝ)).toContinuousLinearEquiv g)

private theorem cutoffConjReflect_apply (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    cutoffConjReflect g x = conj (g (-x)) := rfl

private theorem fourier_cutoffConjReflect (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    𝓕 (cutoffConjReflect g) x = conj (𝓕 g x) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe,
    Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul, ← integral_conj]
  rw [← integral_neg_eq_self (fun y : ℝ =>
    Complex.exp (↑(-2 * Real.pi * y * x) * Complex.I) •
      cutoffConjReflect g y) volume]
  apply integral_congr_ae
  filter_upwards with y
  simp only [cutoffConjReflect_apply, neg_neg, smul_eq_mul, map_mul,
    ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I]
  congr 2
  push_cast
  ring

private theorem fourier_fourier_cutoff (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    𝓕 (𝓕 g) x = g (-x) := by
  have h := congrFun (g.continuous.fourierInv_fourier_eq
    g.integrable (𝓕 g).integrable) (-x)
  rw [Real.fourierInv_eq_fourier_neg, neg_neg] at h
  exact h

private def cutoffSquare (g : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ)
    (𝓕 g) (𝓕 (cutoffConjReflect g))

private theorem cutoffSquare_apply (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    cutoffSquare g x = (‖𝓕 g x‖^2 : ℝ) := by
  simp only [cutoffSquare, SchwartzMap.pairing_apply_apply,
    ContinuousLinearMap.mul_apply', fourier_cutoffConjReflect,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]

private theorem fourier_cutoffSquare (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    𝓕 (cutoffSquare g) x =
      (g ⋆[ContinuousLinearMap.mul ℂ ℂ] cutoffConjReflect g) (-x) := by
  have h : cutoffSquare g =
      𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
        g (cutoffConjReflect g)) :=
    (SchwartzMap.fourier_convolution _ _ _).symm
  rw [h, fourier_fourier_cutoff, SchwartzMap.convolution_apply]

private theorem fourier_cutoffSquare_eq_zero
    (g : 𝓢(ℝ, ℂ)) {R x : ℝ}
    (hs : ∀ y, R < |y| → g y = 0) (hx : 2*R < |x|) :
    𝓕 (cutoffSquare g) x = 0 := by
  rw [fourier_cutoffSquare]
  apply Function.notMem_support.mp
  intro h
  obtain ⟨u,hu,v,hv,huv⟩ :=
    support_convolution_subset (ContinuousLinearMap.mul ℂ ℂ) h
  have hu' : |u| ≤ R := le_of_not_gt (fun hn => hu (hs u hn))
  have hv' : |v| ≤ R := by
    apply le_of_not_gt
    intro hn
    apply hv
    rw [cutoffConjReflect_apply, hs (-v) (by simpa only [abs_neg] using hn), map_zero]
  have hsum := abs_add_le u v
  change u+v = -x at huv
  rw [huv, abs_neg] at hsum
  linarith

private def parabolaFrequencyBumpReal : ℝ → ℝ :=
  modelPhaseBufferedCutoff (-1) 1 (1/4)

private theorem parabolaFrequencyBumpReal_smooth :
    ContDiff ℝ ∞ parabolaFrequencyBumpReal :=
  modelPhaseBufferedCutoff_contDiff _ _ _

private theorem parabolaFrequencyBumpReal_compact :
    HasCompactSupport parabolaFrequencyBumpReal :=
  modelPhaseBufferedCutoff_hasCompactSupport (by norm_num)

private def parabolaFrequencyBump : 𝓢(ℝ, ℂ) :=
  SchwartzMap.postcompCLM Complex.ofRealCLM
    (parabolaFrequencyBumpReal_compact.toSchwartzMap
      parabolaFrequencyBumpReal_smooth)

private theorem parabolaFrequencyBump_apply (x : ℝ) :
    parabolaFrequencyBump x = (parabolaFrequencyBumpReal x : ℂ) := rfl

private theorem parabolaFrequencyBump_zero {x : ℝ} (hx : 1 < |x|) :
    parabolaFrequencyBump x = 0 := by
  rw [parabolaFrequencyBump_apply]
  apply Complex.ofReal_eq_zero.mpr
  rcases lt_abs.mp hx with h | h
  · exact modelPhaseBufferedCutoff_zero_right (by norm_num) (by linarith)
  · exact modelPhaseBufferedCutoff_zero_left (by norm_num) (by linarith)

private theorem parabolaFrequencyBump_fourier_zero_pos :
    0 < (𝓕 parabolaFrequencyBump 0).re := by
  have hi : Integrable parabolaFrequencyBumpReal :=
    parabolaFrequencyBumpReal_smooth.continuous.integrable_of_hasCompactSupport
      parabolaFrequencyBumpReal_compact
  have hz : parabolaFrequencyBumpReal 0 = 1 :=
    modelPhaseBufferedCutoff_one (by norm_num) (by norm_num) (by norm_num)
  have hp := integral_pos_of_integrable_nonneg_nonzero
    parabolaFrequencyBumpReal_smooth.continuous hi
    (fun x => modelPhaseBufferedCutoff_nonneg _ _ _ x)
    (show parabolaFrequencyBumpReal 0 ≠ 0 by rw [hz]; norm_num)
  have he : (𝓕 parabolaFrequencyBump 0).re = ∫ x, parabolaFrequencyBumpReal x := by
    rw [SchwartzMap.fourier_coe, Real.fourier_eq']
    simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, one_smul, parabolaFrequencyBump_apply]
    exact (integral_re (show Integrable (fun x => (parabolaFrequencyBumpReal x : ℂ))
      from parabolaFrequencyBump.integrable)).symm
  rwa [he]

private def cutoffRescale (f : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : a ≠ 0) :
    𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℝ)
      (Units.mk0 a ha)) f

private theorem cutoffRescale_apply
    (f : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : a ≠ 0) (x : ℝ) :
    cutoffRescale f a ha x = f (a*x) := rfl

private theorem fourier_cutoffRescale
    (f : 𝓢(ℝ, ℂ)) {a : ℝ} (ha : a ≠ 0) (ξ : ℝ) :
    𝓕 (cutoffRescale f a ha) ξ = |a⁻¹| • 𝓕 f (ξ/a) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe,
    Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  calc
    _ = ∫ x : ℝ, (fun y : ℝ =>
      Complex.exp (↑(-2*Real.pi*y*(ξ/a))*Complex.I) • f y) (a*x) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [cutoffRescale_apply]
      congr 3
      field_simp
    _ = _ := by
      simpa using Measure.integral_comp_mul_left
        (fun y : ℝ => Complex.exp (↑(-2*Real.pi*y*(ξ/a))*Complex.I) • f y) a

private theorem cutoff_polynomial_decay (f : 𝓢(ℝ, ℂ)) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, (1+|x|)^n*‖f x‖ ≤ C := by
  let B : ℝ := 2^n * (Finset.Iic (n,0)).sup
    (fun p => SchwartzMap.seminorm ℝ p.1 p.2) f
  refine ⟨max B 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro x
  have h := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℝ) (m := (n,0)) (k := n) (n := 0) le_rfl le_rfl f x
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  exact h.trans (le_max_left _ _)

theorem exists_parabola_rapid_cutoff :
    ∃ η : 𝓢(ℝ, ℂ),
      (∀ x : ℝ, 0 ≤ (η x).re ∧ (η x).im = 0) ∧
      (∀ x : ℝ, |x| ≤ 1 → 1 ≤ (η x).re) ∧
      (∀ ξ : ℝ, 1/100 ≤ |ξ| → 𝓕 η ξ = 0) ∧
      (∀ n : ℕ, ∃ C : ℝ, 0 < C ∧
        ∀ x : ℝ, (1+|x|)^n*‖η x‖ ≤ C) := by
  let f := cutoffSquare parabolaFrequencyBump
  have hf (x : ℝ) : f x = (‖𝓕 parabolaFrequencyBump x‖^2 : ℝ) :=
    cutoffSquare_apply _ _
  have hfn (x : ℝ) : 0 ≤ (f x).re := by rw [hf]; exact sq_nonneg _
  have hfi (x : ℝ) : (f x).im = 0 := by rw [hf]; rfl
  have hf₀ : 0 < (f 0).re := by
    rw [hf,Complex.ofReal_re]
    apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    intro hz
    have h := parabolaFrequencyBump_fourier_zero_pos
    rw [hz] at h
    simp at h
  let m : ℝ := (f 0).re/2
  have hm : 0 < m := by dsimp [m]; positivity
  have hn : {x : ℝ | m < (f x).re} ∈ nhds 0 :=
    ((Complex.continuous_re.comp f.continuous).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds (by dsimp [m]; linarith))
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hn
  let a : ℝ := min (δ/2) (1/400)
  have ha : 0 < a := lt_min (by positivity) (by norm_num)
  let η : 𝓢(ℝ, ℂ) := (m⁻¹ : ℂ) • cutoffRescale f a ha.ne'
  have he (x : ℝ) : η x = (m⁻¹ : ℂ)*f (a*x) := rfl
  have her (x : ℝ) : (η x).re = m⁻¹*(f (a*x)).re := by
    rw [he,Complex.mul_re]
    simp
  have hei (x : ℝ) : (η x).im = 0 := by
    rw [he,Complex.mul_im,hfi]
    simp
  refine ⟨η,fun x => ⟨?_,hei x⟩,?_,?_,cutoff_polynomial_decay η⟩
  · rw [her]
    exact mul_nonneg (inv_nonneg.mpr hm.le) (hfn _)
  · intro x hx
    have hxδ : a*|x| < δ := by
      have hax := mul_le_mul_of_nonneg_left hx ha.le
      have haδ : a ≤ δ/2 := min_le_left _ _
      nlinarith
    have hmx := hball (show a*x ∈ Metric.ball 0 δ by
      simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_mul,abs_of_pos ha]
        using hxδ)
    rw [her]
    apply (le_inv_mul_iff₀ hm).mpr
    simpa only [mul_one] using le_of_lt hmx
  · intro ξ hξ
    change 𝓕 ((m⁻¹ : ℂ) • cutoffRescale f a ha.ne') ξ = 0
    rw [fourier_smul]
    change (m⁻¹ : ℂ) • 𝓕 (cutoffRescale f a ha.ne') ξ = 0
    rw [fourier_cutoffRescale,
      fourier_cutoffSquare_eq_zero parabolaFrequencyBump
        (fun y hy => parabolaFrequencyBump_zero hy)]
    · simp
    · rw [abs_div,abs_of_pos ha]
      apply (lt_div_iff₀ ha).mpr
      have hab : a ≤ 1/400 := min_le_right _ _
      linarith

def parabolaRapidProfile : 𝓢(ℝ, ℂ) :=
  Classical.choose exists_parabola_rapid_cutoff

private theorem parabolaRapidProfile_nonneg (x : ℝ) :
    0 ≤ (parabolaRapidProfile x).re :=
  (Classical.choose_spec exists_parabola_rapid_cutoff).1 x |>.1

private theorem parabolaRapidProfile_real (x : ℝ) :
    (parabolaRapidProfile x).im = 0 :=
  (Classical.choose_spec exists_parabola_rapid_cutoff).1 x |>.2

private theorem parabolaRapidProfile_one_le (x : ℝ) (hx : |x| ≤ 1) :
    1 ≤ (parabolaRapidProfile x).re :=
  (Classical.choose_spec exists_parabola_rapid_cutoff).2.1 x hx

private theorem parabolaRapidProfile_fourier_zero (ξ : ℝ) (hξ : 1/100 ≤ |ξ|) :
    𝓕 parabolaRapidProfile ξ = 0 :=
  (Classical.choose_spec exists_parabola_rapid_cutoff).2.2.1 ξ hξ

private theorem parabolaRapidProfile_coe_re (x : ℝ) :
    ((parabolaRapidProfile x).re : ℂ) = parabolaRapidProfile x := by
  apply Complex.ext
  · rfl
  · simpa using (parabolaRapidProfile_real x).symm

def parabolaRapidKernel (R c x : ℝ) : ℝ :=
  (parabolaRapidProfile ((x-c)/R)).re

theorem parabolaRapidKernel_nonneg (R c x : ℝ) :
    0 ≤ parabolaRapidKernel R c x := parabolaRapidProfile_nonneg _

theorem parabolaRapidKernel_one_le {R c x : ℝ}
    (hR : 0 < R) (hx : |x-c| ≤ R) :
    1 ≤ parabolaRapidKernel R c x := by
  apply parabolaRapidProfile_one_le
  rw [abs_div,abs_of_pos hR]
  exact (div_le_one hR).mpr hx

theorem integrable_parabolaRapidKernel {R : ℝ} (hR : 0 < R) (c : ℝ) :
    Integrable (parabolaRapidKernel R c) := by
  have h₀ : Integrable (cutoffRescale parabolaRapidProfile R⁻¹
    (inv_ne_zero hR.ne')) := (cutoffRescale parabolaRapidProfile R⁻¹
      (inv_ne_zero hR.ne')).integrable
  have h := h₀.re.comp_add_right (-c)
  convert h using 1
  ext x
  simp only [parabolaRapidKernel,cutoffRescale_apply,sub_eq_add_neg,div_eq_mul_inv,mul_comm]
  rfl

theorem parabolaRapidKernel_decay (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R c x : ℝ,
      (1+|(x-c)/R|)^n*parabolaRapidKernel R c x ≤ C := by
  obtain ⟨C,hC,h⟩ := cutoff_polynomial_decay parabolaRapidProfile n
  refine ⟨C,hC,fun R c x => ?_⟩
  have he : ‖parabolaRapidProfile ((x-c)/R)‖ = parabolaRapidKernel R c x := by
    rw [← parabolaRapidProfile_coe_re,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (parabolaRapidProfile_nonneg _)]
    rfl
  simpa only [he] using h ((x-c)/R)

private theorem integral_parabolaRapidKernel_character_zero_origin
    {R ξ : ℝ} (hR : 0 < R) (hξ : 1/(100*R) ≤ |ξ|) :
    (∫ x : ℝ, (parabolaRapidKernel R 0 x : ℂ)*fordAdditiveCharacter (ξ*x)) = 0 := by
  have he : (∫ x : ℝ, (parabolaRapidKernel R 0 x : ℂ)*fordAdditiveCharacter (ξ*x)) =
      𝓕 (cutoffRescale parabolaRapidProfile R⁻¹ (inv_ne_zero hR.ne')) (-ξ) := by
    rw [SchwartzMap.fourier_coe,Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with x
    simp only [parabolaRapidKernel,sub_zero,parabolaRapidProfile_coe_re,
      cutoffRescale_apply,fordAdditiveCharacter,smul_eq_mul]
    rw [show R⁻¹*x = x/R by ring]
    rw [mul_comm (parabolaRapidProfile (x/R))]
    congr 2
    push_cast
    ring
  rw [he,fourier_cutoffRescale,parabolaRapidProfile_fourier_zero]
  · simp
  · rw [div_inv_eq_mul,abs_mul,abs_neg,abs_of_pos hR]
    have h := (div_le_iff₀ (by positivity : 0 < 100*R)).mp hξ
    nlinarith

theorem integral_parabolaRapidKernel_character_zero
    {R ξ : ℝ} (hR : 0 < R) (hξ : 1/(100*R) ≤ |ξ|) (c : ℝ) :
    (∫ x : ℝ, (parabolaRapidKernel R c x : ℂ)*fordAdditiveCharacter (ξ*x)) = 0 := by
  let f : ℝ → ℂ := fun x =>
    (parabolaRapidKernel R c x : ℂ)*fordAdditiveCharacter (ξ*x)
  have ht := integral_add_right_eq_self (μ := volume) f c
  calc
    _ = ∫ x : ℝ, f (x+c) := ht.symm
    _ = ∫ x : ℝ, fordAdditiveCharacter (ξ*c)*
      ((parabolaRapidKernel R 0 x : ℂ)*fordAdditiveCharacter (ξ*x)) := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [f,parabolaRapidKernel]
      rw [add_sub_cancel_right,sub_zero,
        show ξ*(x+c) = ξ*c+ξ*x by ring,fordAdditiveCharacter_add]
      ring
    _ = fordAdditiveCharacter (ξ*c)*
      ∫ x : ℝ, (parabolaRapidKernel R 0 x : ℂ)*fordAdditiveCharacter (ξ*x) :=
        integral_const_mul _ _
    _ = 0 := by rw [integral_parabolaRapidKernel_character_zero_origin hR hξ,mul_zero]

def parabolaRapidWeight (R r t α γ : ℝ) : ℝ :=
  parabolaRapidKernel R r α * parabolaRapidKernel R t γ

theorem parabolaRapidWeight_nonneg (R r t α γ : ℝ) :
    0 ≤ parabolaRapidWeight R r t α γ :=
  mul_nonneg (parabolaRapidKernel_nonneg _ _ _) (parabolaRapidKernel_nonneg _ _ _)

theorem parabolaRapidWeight_one_le {R r t α γ : ℝ}
    (hR : 0 < R) (hα : |α-r| ≤ R) (hγ : |γ-t| ≤ R) :
    1 ≤ parabolaRapidWeight R r t α γ := by
  exact one_le_mul_of_one_le_of_one_le
    (parabolaRapidKernel_one_le hR hα) (parabolaRapidKernel_one_le hR hγ)

theorem parabolaRapidWeight_decay (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R r t α γ : ℝ,
      (1+|(α-r)/R|+|(γ-t)/R|)^n*parabolaRapidWeight R r t α γ ≤ C := by
  obtain ⟨C,hC,h⟩ := parabolaRapidKernel_decay n
  refine ⟨C^2,sq_pos_of_pos hC,fun R r t α γ => ?_⟩
  have hp : 1+|(α-r)/R|+|(γ-t)/R| ≤
      (1+|(α-r)/R|)*(1+|(γ-t)/R|) := by
    nlinarith [mul_nonneg (abs_nonneg ((α-r)/R)) (abs_nonneg ((γ-t)/R))]
  have hpn := pow_le_pow_left₀ (by positivity : 0 ≤ 1+|(α-r)/R|+|(γ-t)/R|) hp n
  have hprod := mul_le_mul (h R r α) (h R t γ)
    (mul_nonneg (by positivity) (parabolaRapidKernel_nonneg _ _ _)) hC.le
  have hm := mul_le_mul_of_nonneg_right hpn (parabolaRapidWeight_nonneg R r t α γ)
  rw [mul_pow] at hm
  unfold parabolaRapidWeight at hm ⊢
  nlinarith only [hm,hprod]

theorem integral_parabolaRapidWeight_character_zero
    {R u v : ℝ} (hR : 0 < R)
    (hgap : 1/(100*R) ≤ |u| ∨ 1/(100*R) ≤ |v|) (r t : ℝ) :
    (∫ α : ℝ, ∫ γ : ℝ, (parabolaRapidWeight R r t α γ : ℂ)*
      fordAdditiveCharacter (u*α+v*γ)) = 0 := by
  have he (α γ : ℝ) :
      (parabolaRapidWeight R r t α γ : ℂ)*fordAdditiveCharacter (u*α+v*γ) =
      ((parabolaRapidKernel R r α : ℂ)*fordAdditiveCharacter (u*α))*
      ((parabolaRapidKernel R t γ : ℂ)*fordAdditiveCharacter (v*γ)) := by
    rw [fordAdditiveCharacter_add]
    unfold parabolaRapidWeight
    push_cast
    ring
  simp_rw [he,integral_const_mul]
  rw [integral_mul_const]
  rcases hgap with h | h
  · rw [integral_parabolaRapidKernel_character_zero hR h,zero_mul]
  · rw [integral_parabolaRapidKernel_character_zero hR h,mul_zero]

private theorem continuous_rapidWeight (R r t : ℝ) :
    Continuous (fun p : ℝ × ℝ => parabolaRapidWeight R r t p.1 p.2) := by
  unfold parabolaRapidWeight parabolaRapidKernel
  exact (Complex.continuous_re.comp
    (parabolaRapidProfile.continuous.comp (by fun_prop))).mul
    (Complex.continuous_re.comp
      (parabolaRapidProfile.continuous.comp (by fun_prop)))

private theorem rapid_weighted_integrable {f : ℝ × ℝ → ℂ}
    (hf : Continuous f) {M R : ℝ} (hR : 0 < R)
    (hM : ∀ p, ‖f p‖ ≤ M) (r t : ℝ) :
    Integrable (fun p : ℝ × ℝ =>
      (parabolaRapidWeight R r t p.1 p.2 : ℂ)*f p) := by
  have hw : Integrable (fun p : ℝ × ℝ => parabolaRapidWeight R r t p.1 p.2) :=
    (integrable_parabolaRapidKernel hR r).mul_prod (integrable_parabolaRapidKernel hR t)
  have hc := (Complex.continuous_ofReal.comp (continuous_rapidWeight R r t)).mul hf
  apply (hw.mul_const M).mono' hc.aestronglyMeasurable
  filter_upwards with p
  change ‖(parabolaRapidWeight R r t p.1 p.2 : ℂ)*f p‖ ≤ _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (parabolaRapidWeight_nonneg R r t p.1 p.2)]
  exact mul_le_mul_of_nonneg_left (hM p) (parabolaRapidWeight_nonneg R r t p.1 p.2)

private theorem weighted_family_banded (J : Finset ℤ)
    (F : ℤ → (ℝ × ℝ) → ℂ) (W : (ℝ × ℝ) → ℝ) (m : ℕ)
    (hW : ∀ p, 0 ≤ W p)
    (hi : ∀ i ∈ J, ∀ j ∈ J, Integrable (fun p => (W p : ℂ)*F i p*conj (F j p)))
    (hz : ∀ i ∈ J, ∀ j ∈ J, (m : ℤ) < |i-j| →
      (∫ p, (W p : ℂ)*F i p*conj (F j p)) = 0) :
    (∫ p, W p*‖∑ i ∈ J, F i p‖^2) ≤
      (2*(m : ℝ)+1)*∑ i ∈ J, ∫ p, W p*‖F i p‖^2 := by
  classical
  have hself (i : ℤ) (p : ℝ × ℝ) :
      (W p : ℂ)*F i p*conj (F i p) = (W p*‖F i p‖^2 : ℝ) := by
    rw [mul_assoc,Complex.mul_conj']
    push_cast
    ring
  have hdiag (i : ℤ) (hiJ : i ∈ J) : Integrable (fun p => W p*‖F i p‖^2) := by
    apply (Integrable.iff_ofReal (𝕜:=ℂ)).mpr
    convert (hi i hiJ i hiJ) using 1
    funext p
    exact (hself i p).symm
  have hexpand (p : ℝ × ℝ) :
      (W p*‖∑ i ∈ J, F i p‖^2 : ℝ) =
        ∑ i ∈ J, ∑ j ∈ J, (W p : ℂ)*F i p*conj (F j p) := by
    rw [Complex.ofReal_mul,Complex.ofReal_pow,← Complex.mul_conj']
    rw [map_sum,Finset.sum_mul_sum]
    simp only [Finset.mul_sum,mul_assoc]
  have he : ((∫ p, W p*‖∑ i ∈ J, F i p‖^2 : ℝ) : ℂ) =
      ∑ i ∈ J, ∑ j ∈ J, ∫ p, (W p : ℂ)*F i p*conj (F j p) := by
    rw [← integral_complex_ofReal]
    simp_rw [hexpand]
    rw [integral_finsetSum J (fun i hiJ =>
      integrable_finsetSum J (fun j hj => hi i hiJ j hj))]
    apply Finset.sum_congr rfl
    intro i hiJ
    exact integral_finsetSum J (hi i hiJ)
  have hre := congrArg Complex.re he
  simp only [Complex.ofReal_re,Complex.re_sum] at hre
  rw [hre]
  apply banded_real_sum_le
  · intro i hiJ
    exact integral_nonneg (fun p => mul_nonneg (hW p) (sq_nonneg _))
  · intro i hiJ j hj
    have hpoint (p : ℝ × ℝ) :
        2*((W p : ℂ)*F i p*conj (F j p)).re ≤
          W p*‖F i p‖^2+W p*‖F j p‖^2 := by
      have hn : (F i p*conj (F j p)).re ≤ ‖F i p‖*‖F j p‖ := by
        simpa only [norm_mul,Complex.norm_conj] using
          Complex.re_le_norm (F i p*conj (F j p))
      have hc : 2*(F i p*conj (F j p)).re ≤ ‖F i p‖^2+‖F j p‖^2 := by
        nlinarith [sq_nonneg (‖F i p‖-‖F j p‖)]
      have hm := mul_le_mul_of_nonneg_left hc (hW p)
      rw [mul_assoc,Complex.re_ofReal_mul]
      nlinarith only [hm]
    have hre' : (∫ p, (W p : ℂ)*F i p*conj (F j p)).re =
        ∫ p, ((W p : ℂ)*F i p*conj (F j p)).re :=
      (integral_re (hi i hiJ j hj)).symm
    rw [hre',← integral_const_mul,← integral_add (hdiag i hiJ) (hdiag j hj)]
    exact integral_mono ((hi i hiJ j hj).re.const_mul 2)
      ((hdiag i hiJ).add (hdiag j hj)) hpoint
  · intro i hiJ j hj hij
    rw [hz i hiJ j hj hij]
    rfl

private theorem rapidCharacter_integrable {R : ℝ} (hR : 0 < R) (r t u v : ℝ) :
    Integrable (fun p : ℝ × ℝ => (parabolaRapidWeight R r t p.1 p.2 : ℂ)*
      fordAdditiveCharacter (u*p.1+v*p.2)) :=
  rapid_weighted_integrable (by unfold fordAdditiveCharacter; fun_prop) hR
    (fun p => (sargos_character_norm _).le) r t

private theorem rapidCross_expand {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (z : ι → ℂ) (z' : κ → ℂ)
    (u v : ι → ℝ) (u' v' : κ → ℝ) (W α γ : ℝ) :
    (W : ℂ)*sargosPlanarSum S z u v α γ*
      conj (sargosPlanarSum T z' u' v' α γ) =
      ∑ ij ∈ S ×ˢ T, (z ij.1*conj (z' ij.2))*
        ((W : ℂ)*fordAdditiveCharacter
          ((u ij.1-u' ij.2)*α+(v ij.1-v' ij.2)*γ)) := by
  unfold sargosPlanarSum
  rw [map_sum,mul_assoc,Finset.sum_mul_sum,Finset.sum_product]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul,conj_fordAdditiveCharacter]
  calc
    _ = (z i*conj (z' j))*((W : ℂ)*
      (fordAdditiveCharacter (u i*α+v i*γ)*fordAdditiveCharacter (-(u' j*α+v' j*γ)))) := by ring
    _ = _ := by
      rw [← fordAdditiveCharacter_add]
      congr 3
      ring

def parabolaRapidBilinearMoment {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) (R r t : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, parabolaRapidWeight R r t p.1 p.2*
    ‖sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2‖^2 *
    ‖sargosPlanarSum V c y (fun j => (y j)^2) p.1 p.2‖^4

def parabolaSourceWeight (R r t α γ : ℝ) : ℝ :=
  1/(1+‖(((α-r)/R : ℝ) : ℂ)+((γ-t)/R : ℝ)*Complex.I‖)^100

theorem parabolaSourceWeight_nonneg (R r t α γ : ℝ) :
    0 ≤ parabolaSourceWeight R r t α γ := by
  unfold parabolaSourceWeight
  positivity

private theorem continuous_sourceWeight (R r t : ℝ) :
    Continuous (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2) := by
  unfold parabolaSourceWeight
  exact continuous_const.div (by fun_prop) (fun p => by positivity)

theorem integrable_parabolaSourceWeight {R : ℝ} (hR : 0 < R) (r t : ℝ) :
    Integrable (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2) := by
  have hb := integrable_one_add_norm (E := ℝ × ℝ) (μ := volume) (r := 100)
    (by norm_num)
  have hi := (hb.comp_smul (inv_ne_zero hR.ne')).comp_add_right (-(r,t))
  apply hi.mono' (continuous_sourceWeight R r t).aestronglyMeasurable
  filter_upwards with p
  rw [Real.norm_eq_abs,abs_of_nonneg (parabolaSourceWeight_nonneg _ _ _ _ _)]
  have hnorm : ‖R⁻¹ • (p + -(r,t))‖ ≤
      ‖(((p.1-r)/R : ℝ) : ℂ)+((p.2-t)/R : ℝ)*Complex.I‖ := by
    rw [Prod.norm_def]
    apply max_le
    · have h := Complex.abs_re_le_norm
        ((((p.1-r)/R : ℝ) : ℂ)+((p.2-t)/R : ℝ)*Complex.I)
      simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,
        Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero] at h
      change |R⁻¹*(p.1 + -r)| ≤ _
      simpa only [sub_eq_add_neg,div_eq_mul_inv,mul_comm] using h
    · have h := Complex.abs_im_le_norm
        ((((p.1-r)/R : ℝ) : ℂ)+((p.2-t)/R : ℝ)*Complex.I)
      simp only [Complex.add_im,Complex.ofReal_re,Complex.mul_im,
        Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_add,add_zero] at h
      change |R⁻¹*(p.2 + -t)| ≤ _
      simpa only [sub_eq_add_neg,div_eq_mul_inv,mul_comm] using h
  rw [Real.rpow_neg (by positivity),Real.rpow_ofNat]
  change 1/(1+‖(((p.1-r)/R : ℝ) : ℂ)+((p.2-t)/R : ℝ)*Complex.I‖)^100 ≤ _
  rw [← one_div]
  apply one_div_le_one_div_of_le (by positivity)
  gcongr

theorem parabolaRapidWeight_le_sourceWeight :
    ∃ C : ℝ, 0 < C ∧ ∀ R r t α γ : ℝ,
      parabolaRapidWeight R r t α γ ≤ C*parabolaSourceWeight R r t α γ := by
  obtain ⟨C,hC,h⟩ := parabolaRapidWeight_decay 100
  refine ⟨C,hC,fun R r t α γ => ?_⟩
  have hn : ‖(((α-r)/R : ℝ) : ℂ)+((γ-t)/R : ℝ)*Complex.I‖ ≤
      |(α-r)/R|+|(γ-t)/R| := by
    simpa using Complex.norm_le_abs_re_add_abs_im
      ((((α-r)/R : ℝ) : ℂ)+((γ-t)/R : ℝ)*Complex.I)
  have hp : (1+‖(((α-r)/R : ℝ) : ℂ)+((γ-t)/R : ℝ)*Complex.I‖)^100 ≤
      (1+|(α-r)/R|+|(γ-t)/R|)^100 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hm := mul_le_mul_of_nonneg_right hp (parabolaRapidWeight_nonneg R r t α γ)
  unfold parabolaSourceWeight
  rw [mul_one_div,le_div_iff₀ (by positivity)]
  rw [mul_comm]
  exact hm.trans (h R r t α γ)

private def parabolaMomentFunction {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ‖sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2‖^2 *
  ‖sargosPlanarSum V c y (fun j => (y j)^2) p.1 p.2‖^4

private theorem parabolaMomentFunction_nonneg {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) (p : ℝ × ℝ) :
    0 ≤ parabolaMomentFunction S V z c x y p := by
  unfold parabolaMomentFunction
  positivity

private theorem parabolaMomentFunction_continuous {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) :
    Continuous (parabolaMomentFunction S V z c x y) := by
  unfold parabolaMomentFunction sargosPlanarSum fordAdditiveCharacter
  fun_prop

private theorem parabolaMomentFunction_integrable {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) {W : ℝ × ℝ → ℝ} (hW : Integrable W) :
    Integrable (fun p => W p*parabolaMomentFunction S V z c x y p) := by
  apply hW.mul_bdd (parabolaMomentFunction_continuous S V z c x y).aestronglyMeasurable
    (c := (∑ i ∈ S, ‖z i‖)^2*(∑ j ∈ V, ‖c j‖)^4)
  filter_upwards with p
  rw [Real.norm_eq_abs,abs_of_nonneg (parabolaMomentFunction_nonneg _ _ _ _ _ _ _)]
  unfold parabolaMomentFunction
  have hS := norm_sargosPlanarSum_le_sum_norm S z x (fun i => (x i)^2) p.1 p.2
  have hV := norm_sargosPlanarSum_le_sum_norm V c y (fun j => (y j)^2) p.1 p.2
  gcongr

def parabolaSourceBilinearMoment {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) (R r t : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, parabolaSourceWeight R r t p.1 p.2*
    ‖sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2‖^2 *
    ‖sargosPlanarSum V c y (fun j => (y j)^2) p.1 p.2‖^4

def parabolaBoxBilinearMoment {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) (R r t : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ in Icc (r-R) (r+R) ×ˢ Icc (t-R) (t+R),
    ‖sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2‖^2 *
    ‖sargosPlanarSum V c y (fun j => (y j)^2) p.1 p.2‖^4

private theorem parabolaBox_le_rapid {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) {R : ℝ} (hR : 0 < R) (r t : ℝ) :
    parabolaBoxBilinearMoment S V z c x y R r t ≤
      parabolaRapidBilinearMoment S V z c x y R r t := by
  let F := parabolaMomentFunction S V z c x y
  let W := fun p : ℝ × ℝ => parabolaRapidWeight R r t p.1 p.2
  let B := Icc (r-R) (r+R) ×ˢ Icc (t-R) (t+R)
  have hiF : IntegrableOn F B := ContinuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)
    (parabolaMomentFunction_continuous S V z c x y).continuousOn
  have hiW : Integrable W :=
    (integrable_parabolaRapidKernel hR r).mul_prod (integrable_parabolaRapidKernel hR t)
  have hi := parabolaMomentFunction_integrable S V z c x y hiW
  have hpoint (p : ℝ × ℝ) (hp : p ∈ B) : F p ≤ W p*F p := by
    have hα : |p.1-r| ≤ R := abs_le.mpr ⟨by linarith [hp.1.1],by linarith [hp.1.2]⟩
    have hγ : |p.2-t| ≤ R := abs_le.mpr ⟨by linarith [hp.2.1],by linarith [hp.2.2]⟩
    have hW := parabolaRapidWeight_one_le hR hα hγ
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hW
      (parabolaMomentFunction_nonneg S V z c x y p)
  have hlocal := setIntegral_mono_on hiF hi.integrableOn
    (measurableSet_Icc.prod measurableSet_Icc) hpoint
  have hwhole := setIntegral_le_integral (s := B) hi
    (Filter.Eventually.of_forall (fun p =>
      mul_nonneg (parabolaRapidWeight_nonneg _ _ _ _ _)
        (parabolaMomentFunction_nonneg _ _ _ _ _ _ _)))
  simpa only [parabolaBoxBilinearMoment,parabolaRapidBilinearMoment,F,W,B,
    parabolaMomentFunction,mul_assoc] using hlocal.trans hwhole

private theorem parabolaRapid_le_source {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) {C R : ℝ} (hR : 0 < R)
    (hC : ∀ R r t α γ : ℝ,
      parabolaRapidWeight R r t α γ ≤ C*parabolaSourceWeight R r t α γ)
    (r t : ℝ) :
    parabolaRapidBilinearMoment S V z c x y R r t ≤
      C*parabolaSourceBilinearMoment S V z c x y R r t := by
  have hiR := parabolaMomentFunction_integrable S V z c x y
    ((integrable_parabolaRapidKernel hR r).mul_prod (integrable_parabolaRapidKernel hR t))
  have hiS := parabolaMomentFunction_integrable S V z c x y
    (integrable_parabolaSourceWeight hR r t)
  have hb := integral_mono hiR (hiS.const_mul C)
    (fun p => by
      have h := mul_le_mul_of_nonneg_right (hC R r t p.1 p.2)
        (parabolaMomentFunction_nonneg S V z c x y p)
      simpa only [parabolaRapidWeight,mul_assoc] using h)
  rw [integral_const_mul] at hb
  simpa only [parabolaRapidBilinearMoment,parabolaSourceBilinearMoment,
    parabolaMomentFunction,parabolaRapidWeight,mul_assoc] using hb

end TaoTrudgianYang2025
noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ComplexConjugate
namespace TaoTrudgianYang2025
theorem parabola_sum_shift {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (x : ι → ℝ) (β α γ : ℝ) :
    sargosPlanarSum S z x (fun i => (x i)^2) α γ =
      fordAdditiveCharacter (β*α+β^2*γ)*
      sargosPlanarSum S z (fun i => x i-β)
        (fun i => (x i-β)^2) (α+2*β*γ) γ := by
  unfold sargosPlanarSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_left_comm (fordAdditiveCharacter _),← fordAdditiveCharacter_add]
  congr 2
  ring

end TaoTrudgianYang2025
noncomputable section
namespace TaoTrudgianYang2025
open MeasureTheory Set
open scoped BigOperators
private theorem sourceWeight_triangle (R r t α γ β δ : ℝ) :
    ‖(((β-r)/R : ℝ) : ℂ)+((δ-t)/R : ℝ)*Complex.I‖ ≤
      ‖(((α-r)/R : ℝ) : ℂ)+((γ-t)/R : ℝ)*Complex.I‖+
      ‖(((β-α)/R : ℝ) : ℂ)+((δ-γ)/R : ℝ)*Complex.I‖ := by
  have heq :
      (((β-r)/R : ℝ) : ℂ)+((δ-t)/R : ℝ)*Complex.I =
        ((((α-r)/R : ℝ) : ℂ)+((γ-t)/R : ℝ)*Complex.I)+
        ((((β-α)/R : ℝ) : ℂ)+((δ-γ)/R : ℝ)*Complex.I) := by
    push_cast
    ring
  rw [heq]
  exact norm_add_le _ _

private theorem parabolaSourceWeight_triangle_lower (R r t α γ β δ : ℝ) :
    parabolaSourceWeight R r t α γ * parabolaSourceWeight R α γ β δ ≤
      parabolaSourceWeight R r t β δ := by
  have h := sourceWeight_triangle R r t α γ β δ
  have hm := mul_nonneg
    (norm_nonneg ((((α-r)/R : ℝ) : ℂ)+((γ-t)/R : ℝ)*Complex.I))
    (norm_nonneg ((((β-α)/R : ℝ) : ℂ)+((δ-γ)/R : ℝ)*Complex.I))
  unfold parabolaSourceWeight
  rw [div_mul_div_comm,one_mul,← mul_pow]
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_left₀ (by positivity) (by nlinarith only [h,hm]) _

end TaoTrudgianYang2025
noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators NNReal ENNReal
namespace TaoTrudgianYang2025
def parabolaBandGauge (ξ κ : ℝ) : ℝ := max |κ| |κ-2*ξ|

theorem parabolaBandGauge_nonneg (ξ κ : ℝ) : 0 ≤ parabolaBandGauge ξ κ :=
  le_trans (abs_nonneg _) (le_max_left _ _)

theorem parabolaBandGauge_slope_le {a : ℝ} (ha : a ∈ Icc 0 1) (ξ κ : ℝ) :
    |κ-2*a*ξ| ≤ parabolaBandGauge ξ κ := by
  have heq : κ-2*a*ξ = (1-a)*κ+a*(κ-2*ξ) := by ring
  rw [heq]
  calc
    _ ≤ |(1-a)*κ|+|a*(κ-2*ξ)| := abs_add_le _ _
    _ = (1-a)*|κ|+a*|κ-2*ξ| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (by linarith [ha.2] : 0 ≤ 1-a),abs_of_nonneg ha.1]
    _ ≤ (1-a)*parabolaBandGauge ξ κ+a*parabolaBandGauge ξ κ :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith [ha.2]))
        (mul_le_mul_of_nonneg_left (le_max_right _ _) ha.1)
    _ = _ := by ring

                                                                           
theorem parabolaBandGauge_rescale_le {a σ : ℝ}
    (hσ : 0 ≤ σ) (ha : 0 ≤ a) (haσ : a+σ ≤ 1) (ξ κ : ℝ) :
    σ^2*parabolaBandGauge ξ κ ≤
      parabolaBandGauge (σ*ξ) (2*a*σ*ξ+σ^2*κ) := by
  have h1 := parabolaBandGauge_slope_le
    (show a ∈ Icc 0 1 from ⟨ha,by linarith⟩) (σ*ξ) (2*a*σ*ξ+σ^2*κ)
  have h2 := parabolaBandGauge_slope_le
    (show a+σ ∈ Icc 0 1 from ⟨by linarith,haσ⟩) (σ*ξ) (2*a*σ*ξ+σ^2*κ)
  have he1 : 2*a*σ*ξ+σ^2*κ-2*a*(σ*ξ) = σ^2*κ := by ring
  have he2 : 2*a*σ*ξ+σ^2*κ-2*(a+σ)*(σ*ξ) = σ^2*(κ-2*ξ) := by ring
  rw [he1,abs_mul,abs_of_nonneg (sq_nonneg σ)] at h1
  rw [he2,abs_mul,abs_of_nonneg (sq_nonneg σ)] at h2
  unfold parabolaBandGauge
  rw [mul_max_of_nonneg _ _ (sq_nonneg σ)]
  exact max_le h1 h2

theorem parabolaBandGauge_rescale_gap {a σ δ ξ κ : ℝ}
    (hσ : 0 < σ) (ha : 0 ≤ a) (haσ : a+σ ≤ 1)
    (hgap : (δ/σ)^2 ≤ parabolaBandGauge ξ κ) :
    δ^2 ≤ parabolaBandGauge (σ*ξ) (2*a*σ*ξ+σ^2*κ) := by
  have h := (mul_le_mul_of_nonneg_left hgap (sq_nonneg σ)).trans
    (parabolaBandGauge_rescale_le hσ.le ha haσ ξ κ)
  have he : σ^2*(δ/σ)^2 = δ^2 := by field_simp
  simpa only [he] using h


private def parabolaRescaling (a σ : ℝ) (hσ : σ ≠ 0) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) where
  toFun p := (σ*p.1+2*a*σ*p.2,σ^2*p.2)
  invFun p := (p.1/σ-2*a*p.2/σ^2,p.2/σ^2)
  left_inv p := by
    ext <;> dsimp <;> field_simp
    ring
  right_inv p := by
    ext <;> dsimp <;> field_simp
    ring
  map_add' p q := by
    ext <;> dsimp <;> ring
  map_smul' c p := by
    ext <;> dsimp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem parabolaRescaling_haar_factor (e : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) :
    ∃ c : ℝ≥0, 0 < c ∧
      Measure.map e (volume : Measure (ℝ × ℝ)) = (c : ℝ≥0∞) • volume := by
  have : (Measure.map e (volume : Measure (ℝ × ℝ))).IsAddHaarMeasure :=
    e.isAddHaarMeasure_map volume
  refine ⟨Measure.addHaarScalarFactor (Measure.map e volume) volume,
    Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _,?_⟩
  exact Measure.isAddLeftInvariant_eq_smul _ _

private theorem parabolaRescaling_integrable
    (e : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) {W : ℝ × ℝ → ℝ} (hW : Integrable W) :
    Integrable (fun p => W (e p)) := by
  obtain ⟨c,hc,he⟩ := parabolaRescaling_haar_factor e
  apply (integrable_map_equiv e.toHomeomorph.toMeasurableEquiv W).mp
  change Integrable W (Measure.map e volume)
  rw [he]
  exact hW.smul_measure ENNReal.coe_ne_top

private theorem parabolaRescaling_integral
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : ℝ × ℝ → F,
      (∫ p : ℝ × ℝ, f (e p)) = c • ∫ p : ℝ × ℝ, f p := by
  obtain ⟨c,hc,he⟩ := parabolaRescaling_haar_factor e
  refine ⟨c,hc,fun f => ?_⟩
  calc
    (∫ p : ℝ × ℝ, f (e p)) = ∫ p, f p ∂Measure.map e volume :=
      (integral_map_equiv (μ := volume) e.toHomeomorph.toMeasurableEquiv f).symm
    _ = _ := by rw [he,integral_smul_measure,ENNReal.coe_toReal]

                                                                           
                                                                                
def ParabolaWeightBand (δ : ℝ) (W : ℝ × ℝ → ℝ) : Prop :=
  (∀ p, 0 ≤ W p) ∧ Integrable W ∧
    ∀ ξ κ : ℝ, δ^2 ≤ parabolaBandGauge ξ κ →
      (∫ p : ℝ × ℝ, (W p : ℂ)*fordAdditiveCharacter (ξ*p.1+κ*p.2)) = 0

theorem ParabolaWeightBand.rescale {δ a σ : ℝ} {W : ℝ × ℝ → ℝ}
    (hW : ParabolaWeightBand δ W) (hσ : 0 < σ) (ha : 0 ≤ a) (haσ : a+σ ≤ 1) :
    ParabolaWeightBand (δ/σ)
      (fun p : ℝ × ℝ => W (p.1/σ-2*a*p.2/σ^2,p.2/σ^2)) := by
  let e := parabolaRescaling a σ hσ.ne'
  refine ⟨fun p => hW.1 _,parabolaRescaling_integrable e.symm hW.2.1,?_⟩
  intro ξ κ hgap
  obtain ⟨c,hc,hint⟩ := parabolaRescaling_integral (F := ℂ) e.symm
  let f := fun p : ℝ × ℝ => (W p : ℂ)*
    fordAdditiveCharacter (ξ*(e p).1+κ*(e p).2)
  have heq : (∫ p : ℝ × ℝ,
      ((W (p.1/σ-2*a*p.2/σ^2,p.2/σ^2)) : ℂ)*fordAdditiveCharacter (ξ*p.1+κ*p.2)) =
      ∫ p : ℝ × ℝ, f (e.symm p) := by
    apply integral_congr_ae
    filter_upwards with p
    dsimp only [f]
    rw [e.apply_symm_apply]
    rfl
  rw [heq,hint f]
  have hchar := hW.2.2 (σ*ξ) (2*a*σ*ξ+σ^2*κ)
    (parabolaBandGauge_rescale_gap hσ ha haσ hgap)
  have he (p : ℝ × ℝ) :
      ξ*(e p).1+κ*(e p).2 = (σ*ξ)*p.1+(2*a*σ*ξ+σ^2*κ)*p.2 := by
    dsimp [e,parabolaRescaling]
    ring
  dsimp only [f]
  simp_rw [he]
  rw [hchar,smul_zero]

                                                                         
theorem parabolaRapidWeight_band {δ R : ℝ} (hR : 0 < R)
    (hwidth : 3/(100*R) ≤ δ^2) (r t : ℝ) :
    ParabolaWeightBand δ (fun p : ℝ × ℝ => parabolaRapidWeight R r t p.1 p.2) := by
  refine ⟨fun p => parabolaRapidWeight_nonneg _ _ _ _ _,
    (integrable_parabolaRapidKernel hR r).mul_prod (integrable_parabolaRapidKernel hR t),?_⟩
  intro ξ κ hgap
  have hgap' : 1/(100*R) ≤ |ξ| ∨ 1/(100*R) ≤ |κ| := by
    by_contra h
    push Not at h
    have hh : 3*(1/(100*R)) ≤ δ^2 := by
      simpa only [div_eq_mul_inv,one_mul] using hwidth
    have ht : |κ-2*ξ| ≤ |κ|+2*|ξ| := by
      simpa only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] using abs_sub κ (2*ξ)
    have hm : parabolaBandGauge ξ κ < δ^2 :=
      max_lt (by linarith [h.2,show 0 < 1/(100*R) by positivity])
        (by linarith [h.1,h.2])
    exact (not_lt_of_ge hgap) hm
  have hi := rapidCharacter_integrable hR r t ξ κ
  have he := integral_prod
    (fun p : ℝ × ℝ => (parabolaRapidWeight R r t p.1 p.2 : ℂ)*
      fordAdditiveCharacter (ξ*p.1+κ*p.2)) hi
  exact he.trans (integral_parabolaRapidWeight_character_zero hR hgap' r t)

theorem parabola_sum_rescale {ι : Type*} (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ)
    (a σ α γ : ℝ) (hσ : σ ≠ 0) :
    sargosPlanarSum S z x (fun i => (x i)^2) α γ =
      fordAdditiveCharacter (a*α+a^2*γ)*
        sargosPlanarSum S z (fun i => (x i-a)/σ)
          (fun i => ((x i-a)/σ)^2) (σ*α+2*a*σ*γ) (σ^2*γ) := by
  rw [parabola_sum_shift S z x a α γ]
  congr 1
  unfold sargosPlanarSum
  apply Finset.sum_congr rfl
  intro i hi
  congr 2
  field_simp

def parabolaWeightedBilinearMoment {ι τ : Type*}
    (W : ℝ × ℝ → ℝ) (S : Finset ι) (V : Finset τ)
    (z : ι → ℂ) (c : τ → ℂ) (x : ι → ℝ) (y : τ → ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, W p*
    ‖sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2‖^2 *
    ‖sargosPlanarSum V c y (fun j => (y j)^2) p.1 p.2‖^4

private theorem parabola_norm_rescale {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (x : ι → ℝ) (a σ α γ : ℝ) (hσ : σ ≠ 0) :
    ‖sargosPlanarSum S z x (fun i => (x i)^2) α γ‖ =
      ‖sargosPlanarSum S z (fun i => (x i-a)/σ)
        (fun i => ((x i-a)/σ)^2) (σ*α+2*a*σ*γ) (σ^2*γ)‖ := by
  rw [parabola_sum_rescale S z x a σ α γ hσ,norm_mul,sargos_character_norm,one_mul]

                                                                    
                                                                                    
private theorem band_weighted_integrable {f : ℝ × ℝ → ℂ} {W : ℝ × ℝ → ℝ}
    (hf : Continuous f) (hW : Integrable W) {M : ℝ} (hM : ∀ p, ‖f p‖ ≤ M) :
    Integrable (fun p : ℝ × ℝ => (W p : ℂ)*f p) := by
  have hw : Integrable (fun p : ℝ × ℝ => (W p : ℂ)) := hW.ofReal
  exact hw.mul_bdd hf.aestronglyMeasurable (Filter.Eventually.of_forall hM)

private theorem bandCross_integrable {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (z : ι → ℂ) (z' : κ → ℂ)
    (u v : ι → ℝ) (u' v' : κ → ℝ) {W : ℝ × ℝ → ℝ} (hW : Integrable W) :
    Integrable (fun p : ℝ × ℝ => (W p : ℂ)*
      sargosPlanarSum S z u v p.1 p.2*conj (sargosPlanarSum T z' u' v' p.1 p.2)) := by
  have hf : Continuous (fun p : ℝ × ℝ =>
      sargosPlanarSum S z u v p.1 p.2*conj (sargosPlanarSum T z' u' v' p.1 p.2)) := by
    unfold sargosPlanarSum fordAdditiveCharacter
    fun_prop
  have hn (p : ℝ × ℝ) :
      ‖sargosPlanarSum S z u v p.1 p.2*conj (sargosPlanarSum T z' u' v' p.1 p.2)‖ ≤
        (∑ i ∈ S, ‖z i‖)*(∑ j ∈ T, ‖z' j‖) := by
    rw [norm_mul,Complex.norm_conj]
    exact mul_le_mul (norm_sargosPlanarSum_le_sum_norm S z u v p.1 p.2)
      (norm_sargosPlanarSum_le_sum_norm T z' u' v' p.1 p.2)
      (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  simpa only [mul_assoc] using band_weighted_integrable hf hW hn

private theorem bandCharacter_integrable {W : ℝ × ℝ → ℝ} (hW : Integrable W)
    (u v : ℝ) :
    Integrable (fun p : ℝ × ℝ => (W p : ℂ)*fordAdditiveCharacter (u*p.1+v*p.2)) :=
  band_weighted_integrable (by unfold fordAdditiveCharacter; fun_prop) hW
    (fun p => (sargos_character_norm _).le)

                                                                        
                                                                           
                                                                 
theorem sargosWeightedPlanarFamily_banded_bound {ι : Type*}
    (J : Finset ℤ) (S : ℤ → Finset ι)
    (z : ℤ → ι → ℂ) (u v : ℤ → ι → ℝ)
    (W : ℝ × ℝ → ℝ) (hW₀ : ∀ p, 0≤W p) (hW : Integrable W) (m : ℕ)
    (hzero : ∀ i∈J, ∀ j∈J, (m : ℤ) < |i-j| → ∀ s∈S i, ∀ t∈S j,
      (∫ p : ℝ × ℝ, (W p : ℂ)*fordAdditiveCharacter
        ((u i s-u j t)*p.1+(v i s-v j t)*p.2))=0) :
    (∫ p : ℝ × ℝ, W p*‖sargosPlanarSum (J.sigma S)
      (fun ij => z ij.1 ij.2) (fun ij => u ij.1 ij.2) (fun ij => v ij.1 ij.2) p.1 p.2‖^2)≤
      (2*(m : ℝ)+1)*∑ i∈J, ∫ p : ℝ × ℝ,
        W p*‖sargosPlanarSum (S i) (z i) (u i) (v i) p.1 p.2‖^2 := by
  have hz : ∀ i∈J, ∀ j∈J, (m : ℤ) < |i-j| →
      (∫ p : ℝ × ℝ, (W p : ℂ)*sargosPlanarSum (S i) (z i) (u i) (v i) p.1 p.2*
        conj (sargosPlanarSum (S j) (z j) (u j) (v j) p.1 p.2))=0 := by
    intro i hi j hj hij
    simp_rw [rapidCross_expand]
    rw [integral_finsetSum (S i ×ˢ S j) (fun st _ =>
      (bandCharacter_integrable hW (u i st.1-u j st.2) (v i st.1-v j st.2)).const_mul _)]
    apply Finset.sum_eq_zero
    intro st hst
    have hs := Finset.mem_product.mp hst
    rw [integral_const_mul,hzero i hi j hj hij st.1 hs.1 st.2 hs.2,mul_zero]
  have h := weighted_family_banded J
    (fun i p => sargosPlanarSum (S i) (z i) (u i) (v i) p.1 p.2) W m hW₀
    (fun i _ j _ => bandCross_integrable (S i) (S j) (z i) (z j)
      (u i) (v i) (u j) (v j) hW) hz
  simpa only [sargosPlanarSum,Finset.sum_sigma] using h

private theorem integral_bandCross_zero {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (z : ι → ℂ) (z' : κ → ℂ)
    (u v : ι → ℝ) (u' v' : κ → ℝ) {δ : ℝ} {W : ℝ × ℝ → ℝ}
    (hW : ParabolaWeightBand δ W)
    (hgap : ∀ i ∈ S, ∀ j ∈ T, δ^2 ≤ parabolaBandGauge (u i-u' j) (v i-v' j)) :
    (∫ p : ℝ × ℝ, (W p : ℂ)*sargosPlanarSum S z u v p.1 p.2*
      conj (sargosPlanarSum T z' u' v' p.1 p.2)) = 0 := by
  simp_rw [rapidCross_expand]
  rw [integral_finsetSum (S ×ˢ T) (fun ij _ =>
    (bandCharacter_integrable hW.2.1 (u ij.1-u' ij.2) (v ij.1-v' ij.2)).const_mul _)]
  apply Finset.sum_eq_zero
  intro ij hij
  rw [integral_const_mul,hW.2.2 _ _
    (hgap ij.1 (Finset.mem_product.mp hij).1 ij.2 (Finset.mem_product.mp hij).2),mul_zero]

private theorem parabola_band_sixth_gap
    {x x' y₁ y₂ y₃ y₄ w a β u ν δ : ℝ}
    (hw : 0 < w) (hν : 0 < ν) (hβ : β ∈ Icc 0 1)
    (hwidth : δ^2 ≤ w^2) (hu : u ≤ ν) (hd : 3*ν ≤ |a-β|)
    (hx : x ∈ Icc a (a+u)) (hx' : x' ∈ Icc a (a+u))
    (h₁ : y₁ ∈ Icc β (β+w)) (h₂ : y₂ ∈ Icc β (β+w))
    (h₃ : y₃ ∈ Icc β (β+w)) (h₄ : y₄ ∈ Icc β (β+w))
    (hgap : 2*w^2/ν ≤ |x-x'|) :
    δ^2 ≤ parabolaBandGauge (x+y₁+y₂-(x'+y₃+y₄))
      (x^2+y₁^2+y₂^2-(x'^2+y₃^2+y₄^2)) := by
  have hmem {v : ℝ} (hv : v ∈ Icc β (β+w)) : v-β ∈ Icc 0 w :=
    ⟨by linarith [hv.1],by linarith [hv.2]⟩
  have hxp : x-β ∈ Icc (a-β) (a-β+u) :=
    ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hxp' : x'-β ∈ Icc (a-β) (a-β+u) :=
    ⟨by linarith [hx'.1],by linarith [hx'.2]⟩
  have hsep := parabola_same_interval_separation hν.le hu hd hxp hxp'
  have hgap' : (δ^2+2*w^2)/(4*ν) < |(x-β)-(x'-β)| := by
    rw [show (x-β)-(x'-β) = x-x' by ring]
    have hg := (div_le_iff₀ hν).mp hgap
    apply (div_lt_iff₀ (by positivity : 0 < 4*ν)).mpr
    nlinarith [sq_pos_of_pos hw]
  have hs := parabola_sixth_frequency_gap hw.le (by positivity : 0 < 4*ν)
    (hmem h₁) (hmem h₂) (hmem h₃) (hmem h₄) hsep hgap'
  have he : (x-β)^2+(y₁-β)^2+(y₂-β)^2-
      ((x'-β)^2+(y₃-β)^2+(y₄-β)^2) =
      (x^2+y₁^2+y₂^2-(x'^2+y₃^2+y₄^2))-2*β*(x+y₁+y₂-(x'+y₃+y₄)) := by ring
  rw [he] at hs
  exact hs.le.trans (parabolaBandGauge_slope_le hβ _ _)

                                                                          
                                                                          
                                                      
theorem parabolaWeightedBilinearMoment_localization_closed {ι τ : Type*}
    (J : Finset ℤ) (S : ℤ → Finset ι) (V : Finset τ)
    (z : ℤ → ι → ℂ) (c : τ → ℂ)
    (x : ℤ → ι → ℝ) (y : τ → ℝ)
    {w a β u ν δ : ℝ} {W : ℝ × ℝ → ℝ}
    (hW : ParabolaWeightBand δ W)
    (hw : 0 < w) (hν : 0 < ν) (hν₁ : ν ≤ 1) (hβ : β ∈ Icc 0 1)
    (hwidth : δ^2 ≤ w^2) (hu : u ≤ ν) (hd : 3*ν ≤ |a-β|)
    (hx : ∀ i ∈ J, ∀ k ∈ S i, x i k ∈ Icc a (a+u))
    (hy : ∀ k ∈ V, y k ∈ Icc β (β+w))
    (hblock : ∀ i ∈ J, ∀ k ∈ S i,
      x i k ∈ Icc (a+w^2*(i : ℝ)) (a+w^2*((i : ℝ)+1))) :
    parabolaWeightedBilinearMoment W (J.sigma S) V
      (fun ij => z ij.1 ij.2) c (fun ij => x ij.1 ij.2) y ≤
      (7/ν)*∑ i ∈ J, parabolaWeightedBilinearMoment W (S i) V (z i) c (x i) y := by
  classical
  let m := ⌈2/ν⌉₊
  have hm : 2/ν ≤ (m : ℝ) := Nat.le_ceil _
  have hceil : (m : ℝ) < 2/ν+1 := Nat.ceil_lt_add_one (by positivity)
  have hfac : 2*(m : ℝ)+1 ≤ 7/ν := by
    have hn := (lt_div_iff₀ hν).mp (show (m : ℝ)-1 < 2/ν by linarith)
    apply (le_div_iff₀ hν).mpr
    nlinarith
  let A := fun i : ℤ => (S i ×ˢ V) ×ˢ V
  let Z := fun i : ℤ => fun ij : (ι × τ) × τ => z i ij.1.1*c ij.1.2*c ij.2
  let X := fun i : ℤ => fun ij : (ι × τ) × τ => x i ij.1.1+y ij.1.2+y ij.2
  let Y := fun i : ℤ => fun ij : (ι × τ) × τ =>
    (x i ij.1.1)^2+(y ij.1.2)^2+(y ij.2)^2
  let F := fun i : ℤ => fun p : ℝ × ℝ => sargosPlanarSum (A i) (Z i) (X i) (Y i) p.1 p.2
  have hz : ∀ i ∈ J, ∀ j ∈ J, (m : ℤ) < |i-j| →
      (∫ p, (W p : ℂ)*F i p*conj (F j p)) = 0 := by
    intro i hi j hj hij
    apply integral_bandCross_zero _ _ _ _ _ _ _ _ hW
    intro a ha b hb
    have hal := Finset.mem_product.mp (Finset.mem_product.mp ha).1
    have har := (Finset.mem_product.mp ha).2
    have hbl := Finset.mem_product.mp (Finset.mem_product.mp hb).1
    have hbr := (Finset.mem_product.mp hb).2
    exact parabola_band_sixth_gap hw hν hβ hwidth hu hd
      (hx i hi _ hal.1) (hx j hj _ hbl.1)
      (hy _ hal.2) (hy _ har) (hy _ hbl.2) (hy _ hbr)
      (parabola_block_gap_closed hm (hblock i hi _ hal.1) (hblock j hj _ hbl.1) hij)
  have hmain := weighted_family_banded J F W m
    hW.1
    (fun i _ j _ => bandCross_integrable (A i) (A j) (Z i) (Z j)
      (X i) (Y i) (X j) (Y j) hW.2.1) hz
  have hsingle (i : ℤ) :
      (∫ p, W p*‖F i p‖^2) =
        parabolaWeightedBilinearMoment W (S i) V (z i) c (x i) y := by
    unfold parabolaWeightedBilinearMoment
    apply integral_congr_ae
    filter_upwards with p
    dsimp [F,A,Z,X,Y]
    rw [parabola_product_sum,norm_mul,norm_pow]
    ring
  have htotal :
      (∫ p, W p*‖∑ i ∈ J, F i p‖^2) =
        parabolaWeightedBilinearMoment W (J.sigma S) V
          (fun ij => z ij.1 ij.2) c (fun ij => x ij.1 ij.2) y := by
    unfold parabolaWeightedBilinearMoment
    apply integral_congr_ae
    filter_upwards with p
    have hs : (∑ i ∈ J, F i p) =
      sargosPlanarSum (J.sigma (fun i => (S i ×ˢ V) ×ˢ V))
        (fun ij => z ij.1 ij.2.1.1*c ij.2.1.2*c ij.2.2)
        (fun ij => x ij.1 ij.2.1.1+y ij.2.1.2+y ij.2.2)
        (fun ij => (x ij.1 ij.2.1.1)^2+(y ij.2.1.2)^2+(y ij.2.2)^2) p.1 p.2 := by
      simp only [F,A,Z,X,Y,sargosPlanarSum,Finset.sum_sigma]
    rw [hs,parabola_family_product_sum,norm_mul,norm_pow]
    ring
  simp_rw [hsingle] at hmain
  rw [htotal] at hmain
  refine hmain.trans (mul_le_mul_of_nonneg_right hfac ?_)
  apply Finset.sum_nonneg
  intro i hi
  rw [← hsingle]
  exact integral_nonneg (fun p => mul_nonneg (hW.1 p) (sq_nonneg _))

end TaoTrudgianYang2025
noncomputable section
namespace TaoTrudgianYang2025
open MeasureTheory Set
open scoped BigOperators
private theorem weighted_integral_cauchy_square
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {W P Q : α → ℝ}
    (hW : ∀ x, 0 ≤ W x)
    (hPP : Integrable (fun x => W x*(P x)^2) μ)
    (hPQ : Integrable (fun x => W x*P x*Q x) μ)
    (hQQ : Integrable (fun x => W x*(Q x)^2) μ) :
    (∫ x, W x*P x*Q x ∂μ)^2 ≤
      (∫ x, W x*(P x)^2 ∂μ)*(∫ x, W x*(Q x)^2 ∂μ) := by
  have hquad (a : ℝ) :
      0 ≤ (∫ x, W x*(P x)^2 ∂μ)*(a*a) +
        (-2*(∫ x, W x*P x*Q x ∂μ))*a +
        (∫ x, W x*(Q x)^2 ∂μ) := by
    have heq (x : α) : W x*(a*P x-Q x)^2 =
        a^2*(W x*(P x)^2) - (2*a)*(W x*P x*Q x) + W x*(Q x)^2 := by ring
    have hp : 0 ≤ ∫ x, W x*(a*P x-Q x)^2 ∂μ :=
      integral_nonneg (fun x => mul_nonneg (hW x) (sq_nonneg _))
    simp_rw [heq] at hp
    have hA : Integrable (fun x => a^2*(W x*(P x)^2)) μ := hPP.const_mul _
    have hB : Integrable (fun x => (2*a)*(W x*P x*Q x)) μ := hPQ.const_mul _
    have hAB : Integrable (fun x => a^2*(W x*(P x)^2)-(2*a)*(W x*P x*Q x)) μ := hA.sub hB
    rw [integral_add hAB hQQ,
      integral_sub hA hB,
      integral_const_mul,integral_const_mul] at hp
    nlinarith only [hp]
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith only [hd]

                                                                 
                                                                       
theorem parabolaWeightedBilinearMoment_holder_swap {ι τ : Type*}
    (W : ℝ × ℝ → ℝ) (hW₀ : ∀ p, 0 ≤ W p) (hW : Integrable W)
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) :
    (parabolaWeightedBilinearMoment W S V z c x y)^2 ≤
      parabolaWeightedBilinearMoment W V S c z y x *
        parabolaWeightedBilinearMoment W V V c c y y := by
  let P := fun p : ℝ × ℝ => ‖sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2‖^2*
    ‖sargosPlanarSum V c y (fun j => (y j)^2) p.1 p.2‖
  let Q := fun p : ℝ × ℝ => ‖sargosPlanarSum V c y (fun j => (y j)^2) p.1 p.2‖^3
  have hePP (p : ℝ × ℝ) :
      W p*(P p)^2 = W p*parabolaMomentFunction V S c z y x p := by
    dsimp [P,parabolaMomentFunction]
    ring
  have hePQ (p : ℝ × ℝ) :
      W p*P p*Q p = W p*parabolaMomentFunction S V z c x y p := by
    dsimp [P,Q,parabolaMomentFunction]
    ring
  have heQQ (p : ℝ × ℝ) :
      W p*(Q p)^2 = W p*parabolaMomentFunction V V c c y y p := by
    dsimp [Q,parabolaMomentFunction]
    ring
  have hPP : Integrable (fun p => W p*(P p)^2) := by
    exact (parabolaMomentFunction_integrable V S c z y x hW).congr
      (Filter.Eventually.of_forall (fun p => (hePP p).symm))
  have hPQ : Integrable (fun p => W p*P p*Q p) := by
    exact (parabolaMomentFunction_integrable S V z c x y hW).congr
      (Filter.Eventually.of_forall (fun p => (hePQ p).symm))
  have hQQ : Integrable (fun p => W p*(Q p)^2) := by
    exact (parabolaMomentFunction_integrable V V c c y y hW).congr
      (Filter.Eventually.of_forall (fun p => (heQQ p).symm))
  have h := weighted_integral_cauchy_square (W := W) (P := P) (Q := Q)
    hW₀ hPP hPQ hQQ
  simp_rw [hePP,hePQ,heQQ] at h
  simpa only [parabolaMomentFunction,parabolaWeightedBilinearMoment,mul_assoc] using h


def parabolaWeightedSixNorm {ι : Type*} (W : ℝ × ℝ → ℝ)
    (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ) : ℝ :=
  lpNorm (fun p : ℝ × ℝ => sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2)
    6 (volume.withDensity (fun p => ENNReal.ofReal (W p)))

private theorem parabolaWeighted_memLp {ι : Type*} {W : ℝ × ℝ → ℝ}
    (hW : Integrable W) (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ) :
    MemLp (fun p : ℝ × ℝ => sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2)
      6 (volume.withDensity (fun p => ENNReal.ofReal (W p))) := by
  let := isFiniteMeasure_withDensity_ofReal hW.2
  have hc : Continuous (fun p : ℝ × ℝ =>
      sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2) := by
    unfold sargosPlanarSum fordAdditiveCharacter
    fun_prop
  exact MemLp.of_bound hc.aestronglyMeasurable (∑ i ∈ S, ‖z i‖)
    (Filter.Eventually.of_forall fun p =>
      norm_sargosPlanarSum_le_sum_norm S z x (fun i => (x i)^2) p.1 p.2)

theorem parabolaWeightedSixNorm_nonneg {ι : Type*} (W : ℝ × ℝ → ℝ)
    (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ) :
    0 ≤ parabolaWeightedSixNorm W S z x := lpNorm_nonneg

theorem parabolaWeightedSixNorm_pow_six {ι : Type*} (W : ℝ × ℝ → ℝ)
    (hW₀ : ∀ p, 0 ≤ W p) (hW : Integrable W)
    (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ) :
    (parabolaWeightedSixNorm W S z x)^6 =
      parabolaWeightedBilinearMoment W S S z z x x := by
  unfold parabolaWeightedSixNorm
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    (parabolaWeighted_memLp hW S z x).aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat, show (6:ℝ) = ((6:ℕ):ℝ) from rfl,
    Real.rpow_natCast]
  simp only [one_div]
  have hroot (m : ℝ) (hm : 0 ≤ m) : (m^((6:ℝ)⁻¹))^6 = m := by
    simpa only [Nat.cast_ofNat] using Real.rpow_inv_natCast_pow hm (by norm_num : (6:ℕ) ≠ 0)
  rw [hroot _ (integral_nonneg fun _ => by positivity)]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    hW.1.aemeasurable.ennreal_ofReal (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  unfold parabolaWeightedBilinearMoment
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    dsimp only
    rw [ENNReal.toReal_ofReal (hW₀ p)]
    dsimp only [smul_eq_mul]
    norm_num only [Real.rpow_ofNat]
    ring

theorem parabolaWeightedSixNorm_sum_le {κ ι : Type*} (J : Finset κ)
    (S : κ → Finset ι) (z : κ → ι → ℂ) (x : κ → ι → ℝ)
    (W : ℝ × ℝ → ℝ) (hW : Integrable W) :
    parabolaWeightedSixNorm W (J.sigma S) (fun ij => z ij.1 ij.2)
      (fun ij => x ij.1 ij.2) ≤
        ∑ i ∈ J, parabolaWeightedSixNorm W (S i) (z i) (x i) := by
  unfold parabolaWeightedSixNorm
  have he : (fun p : ℝ × ℝ =>
      sargosPlanarSum (J.sigma S) (fun ij => z ij.1 ij.2)
        (fun ij => x ij.1 ij.2) (fun ij => (x ij.1 ij.2)^2) p.1 p.2) =
      ∑ i ∈ J, fun p : ℝ × ℝ =>
        sargosPlanarSum (S i) (z i) (x i) (fun k => (x i k)^2) p.1 p.2 := by
    ext p
    simp only [sargosPlanarSum,Finset.sum_sigma,Finset.sum_apply]
  rw [he]
  exact lpNorm_sum_le (fun i _ => parabolaWeighted_memLp hW (S i) (z i) (x i))
    (by norm_num)

theorem parabolaWeightedSixNorm_sq_le_card {κ ι : Type*} (J : Finset κ)
    (S : κ → Finset ι) (z : κ → ι → ℂ) (x : κ → ι → ℝ)
    (W : ℝ × ℝ → ℝ) (hW : Integrable W) :
    (parabolaWeightedSixNorm W (J.sigma S) (fun ij => z ij.1 ij.2)
      (fun ij => x ij.1 ij.2))^2 ≤
        (J.card:ℝ)*∑ i ∈ J, (parabolaWeightedSixNorm W (S i) (z i) (x i))^2 := by
  calc
    _ ≤ (∑ i ∈ J, parabolaWeightedSixNorm W (S i) (z i) (x i))^2 := by
      exact pow_le_pow_left₀ (parabolaWeightedSixNorm_nonneg _ _ _ _)
        (parabolaWeightedSixNorm_sum_le J S z x W hW) 2
    _ ≤ _ := sq_sum_le_card_mul_sum_sq

theorem parabolaWeightedBilinearMoment_le_sixNorm {ι τ : Type*}
    (W : ℝ × ℝ → ℝ) (hW₀ : ∀ p, 0 ≤ W p) (hW : Integrable W)
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) :
    parabolaWeightedBilinearMoment W S V z c x y ≤
      (parabolaWeightedSixNorm W S z x)^2*(parabolaWeightedSixNorm W V c y)^4 := by
  let M := parabolaWeightedBilinearMoment W S V z c x y
  let N := parabolaWeightedBilinearMoment W V S c z y x
  let A := parabolaWeightedSixNorm W S z x
  let B := parabolaWeightedSixNorm W V c y
  have hM : 0 ≤ M := integral_nonneg fun p => by
    exact mul_nonneg (mul_nonneg (hW₀ p) (sq_nonneg _)) (pow_nonneg (norm_nonneg _) 4)
  have hA : 0 ≤ A := parabolaWeightedSixNorm_nonneg _ _ _ _
  have hB : 0 ≤ B := parabolaWeightedSixNorm_nonneg _ _ _ _
  have hMN : M^2 ≤ N*B^6 := by
    simpa only [M,N,A,B,parabolaWeightedSixNorm_pow_six W hW₀ hW] using
      parabolaWeightedBilinearMoment_holder_swap W hW₀ hW S V z c x y
  have hNM : N^2 ≤ M*A^6 := by
    simpa only [M,N,A,B,parabolaWeightedSixNorm_pow_six W hW₀ hW] using
      parabolaWeightedBilinearMoment_holder_swap W hW₀ hW V S c z y x
  have hfour : M^4 ≤ M*A^6*B^12 := by
    calc
      M^4 = (M^2)^2 := by ring
      _ ≤ (N*B^6)^2 := pow_le_pow_left₀ (sq_nonneg M) hMN 2
      _ = N^2*B^12 := by ring
      _ ≤ M*A^6*B^12 := mul_le_mul_of_nonneg_right hNM (pow_nonneg hB 12)
  change M ≤ A^2*B^4
  by_cases hz : M = 0
  · rw [hz]
    positivity
  have hMp := lt_of_le_of_ne hM (Ne.symm hz)
  have hcube : M^3 ≤ (A^2*B^4)^3 := by
    apply (mul_le_mul_iff_right₀ hMp).mp
    nlinarith only [hfour]
  exact (pow_le_pow_iff_left₀ hM (by positivity) (by norm_num : (3:ℕ) ≠ 0)).mp hcube

universe u

                                                                                         
theorem exists_parabolaWeightedSixNorm_rescale (a σ : ℝ) (hσ : σ ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type u) (W : ℝ × ℝ → ℝ),
      (∀ p, 0 ≤ W p) → Integrable W →
      ∀ (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ),
      parabolaWeightedSixNorm
        (fun p => W (p.1/σ-2*a*p.2/σ^2,p.2/σ^2)) S z (fun i => (x i-a)/σ) =
        C*parabolaWeightedSixNorm W S z x := by
  let e := parabolaRescaling a σ hσ
  obtain ⟨d,hd,hint⟩ := parabolaRescaling_integral (F:=ℝ) e.symm
  let C := d^((6:ℝ)⁻¹)
  have hC : 0 < C := Real.rpow_pos_of_pos hd _
  have hCpow : C^6 = d := by
    simpa only [C,Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow hd.le (by norm_num : (6:ℕ) ≠ 0)
  refine ⟨C,hC,fun ι W hW₀ hW S z x => ?_⟩
  let W' : ℝ × ℝ → ℝ := fun p => W (e.symm p)
  have hW' : Integrable W' := parabolaRescaling_integrable e.symm hW
  have hW'₀ : ∀ p, 0 ≤ W' p := fun p => hW₀ (e.symm p)
  change parabolaWeightedSixNorm W' S z (fun i => (x i-a)/σ) =
    C*parabolaWeightedSixNorm W S z x
  apply (pow_left_inj₀ (parabolaWeightedSixNorm_nonneg _ _ _ _)
    (mul_nonneg hC.le (parabolaWeightedSixNorm_nonneg _ _ _ _))
    (by norm_num : (6:ℕ) ≠ 0)).mp
  rw [parabolaWeightedSixNorm_pow_six W' hW'₀ hW',mul_pow,hCpow,
    parabolaWeightedSixNorm_pow_six W hW₀ hW]
  let f := fun p : ℝ × ℝ => W p*
    ‖sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2‖^2*
    ‖sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2‖^4
  have hn (p : ℝ × ℝ) :
      ‖sargosPlanarSum S z x (fun i => (x i)^2) (e.symm p).1 (e.symm p).2‖ =
        ‖sargosPlanarSum S z (fun i => (x i-a)/σ)
          (fun i => ((x i-a)/σ)^2) p.1 p.2‖ := by
    have h := parabola_norm_rescale S z x a σ (e.symm p).1 (e.symm p).2 hσ
    change _ = ‖sargosPlanarSum S z (fun i => (x i-a)/σ)
      (fun i => ((x i-a)/σ)^2) (e (e.symm p)).1 (e (e.symm p)).2‖ at h
    simpa only [e.apply_symm_apply] using h
  calc
    _ = ∫ p : ℝ × ℝ, f (e.symm p) := by
      apply integral_congr_ae
      filter_upwards with p
      dsimp only [f,parabolaWeightedBilinearMoment]
      rw [hn]
    _ = _ := by
      simpa only [f,parabolaWeightedBilinearMoment,smul_eq_mul] using hint f

                                                                             
                                                                        
def ParabolaDecouplingBound (n : ℕ) (D : ℝ) : Prop :=
  0 ≤ D ∧ ∀ (ι : Type u) (W : ℝ × ℝ → ℝ), ParabolaWeightBand (1/(n:ℝ)) W →
    ∀ (S : Fin n → Finset ι) (z : Fin n → ι → ℂ) (x : Fin n → ι → ℝ),
      (∀ j, ∀ k ∈ S j, x j k ∈ Icc ((j:ℕ)/(n:ℝ)) (((j:ℕ)+1)/(n:ℝ))) →
      (parabolaWeightedSixNorm W (Finset.univ.sigma S)
        (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2))^2 ≤
        D^2*∑ j, (parabolaWeightedSixNorm W (S j) (z j) (x j))^2

theorem parabolaDecouplingBound_trivial (n : ℕ) :
    ParabolaDecouplingBound.{u} n (Real.sqrt n) := by
  refine ⟨Real.sqrt_nonneg _,fun ι W hW S z x _ => ?_⟩
  rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  simpa only [Finset.card_univ,Fintype.card_fin] using
    parabolaWeightedSixNorm_sq_le_card Finset.univ S z x W hW.2.1

                                                                       
                                                                                   
theorem ParabolaDecouplingBound.rescale {n : ℕ} {D a σ : ℝ}
    (hD : ParabolaDecouplingBound.{u} n D) (hσ : 0 < σ)
    (ha : 0 ≤ a) (haσ : a+σ ≤ 1)
    (ι : Type u) (W : ℝ × ℝ → ℝ) (hW : ParabolaWeightBand (σ/(n:ℝ)) W)
    (S : Fin n → Finset ι) (z : Fin n → ι → ℂ) (x : Fin n → ι → ℝ)
    (hx : ∀ j, ∀ k ∈ S j,
      x j k ∈ Icc (a+σ*((j:ℕ)/(n:ℝ))) (a+σ*(((j:ℕ)+1)/(n:ℝ)))) :
    (parabolaWeightedSixNorm W (Finset.univ.sigma S)
      (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2))^2 ≤
      D^2*∑ j, (parabolaWeightedSixNorm W (S j) (z j) (x j))^2 := by
  let W' : ℝ × ℝ → ℝ := fun p => W (p.1/σ-2*a*p.2/σ^2,p.2/σ^2)
  have hW' : ParabolaWeightBand (1/(n:ℝ)) W' := by
    have he : (σ/(n:ℝ))/σ = 1/(n:ℝ) := by
      rw [div_right_comm,div_self hσ.ne']
    simpa only [he,W'] using hW.rescale hσ ha haσ
  have hx' (j : Fin n) (k : ι) (hk : k ∈ S j) :
      (x j k-a)/σ ∈ Icc ((j:ℕ)/(n:ℝ)) (((j:ℕ)+1)/(n:ℝ)) := by
    constructor
    · apply (le_div_iff₀ hσ).mpr
      nlinarith [(hx j k hk).1]
    · apply (div_le_iff₀ hσ).mpr
      nlinarith [(hx j k hk).2]
  have h := hD.2 ι W' hW' S z (fun j k => (x j k-a)/σ) hx'
  obtain ⟨C,hC,hscale⟩ := exists_parabolaWeightedSixNorm_rescale.{u} a σ hσ.ne'
  have ht := hscale (Sigma fun _ : Fin n => ι) W hW.1 hW.2.1
    (Finset.univ.sigma S) (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2)
  have hi (j : Fin n) := hscale ι W hW.1 hW.2.1 (S j) (z j) (x j)
  change parabolaWeightedSixNorm W' _ _ _ = _ at ht
  change ∀ j, parabolaWeightedSixNorm W' _ _ _ = _ at hi
  rw [ht] at h
  simp_rw [hi,mul_pow] at h
  rw [← Finset.mul_sum] at h
  have hC₂ : 0 < C^2 := sq_pos_of_pos hC
  apply (mul_le_mul_iff_right₀ hC₂).mp
  nlinarith only [h]


end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem add_sixth_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a+b)^6 ≤ 64*(a^6+b^6) := by
  rcases le_total a b with h | h
  · have hs := pow_le_pow_left₀ (by positivity : 0 ≤ a+b)
      (show a+b ≤ 2*b by linarith) 6
    nlinarith only [hs,pow_nonneg ha 6]
  · have hs := pow_le_pow_left₀ (by positivity : 0 ≤ a+b)
      (show a+b ≤ 2*a by linarith) 6
    nlinarith only [hs,pow_nonneg hb 6]

public  theorem parabola_near_card (J : Finset ℤ) (i : ℤ) :
    ((J.filter (fun j => |i-j| ≤ 3)).card : ℝ) ≤ 7 := by
  have hs : J.filter (fun j => |i-j| ≤ 3) ⊆ Finset.Icc (i-3) (i+3) := by
    intro j hj
    have hh := abs_le.mp (Finset.mem_filter.mp hj).2
    apply Finset.mem_Icc.mpr
    constructor <;> omega
  have hc : (J.filter (fun j => |i-j| ≤ 3)).card ≤ 7 := by
    calc
      _ ≤ (Finset.Icc (i-3) (i+3)).card := Finset.card_le_card hs
      _ = 7 := by rw [Int.card_Icc]; omega
  exact_mod_cast hc

theorem parabola_bilinear_reduction_pointwise (J : Finset ℤ) (f : ℤ → ℂ) :
    ‖∑ i ∈ J, f i‖^6 ≤
      (64*7^6:ℝ)*∑ i ∈ J, ‖f i‖^6 +
      64*(J.card:ℝ)^5*
        ∑ i ∈ J, ∑ j ∈ J.filter (fun j => 3 < |i-j|), ‖f j‖^2*‖f i‖^4 := by
  classical
  rcases J.eq_empty_or_nonempty with rfl | hJ
  · simp
  obtain ⟨i,hi,hmax⟩ := J.exists_max_image (fun j => ‖f j‖) hJ
  let K := J.filter (fun j => |i-j| ≤ 3)
  let L := J.filter (fun j => 3 < |i-j|)
  let A := ∑ j ∈ K, ‖f j‖
  let B := ∑ j ∈ L, ‖f j‖
  let M := ‖f i‖
  let n := (J.card:ℝ)
  have hM : 0 ≤ M := norm_nonneg _
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hK : (K.card:ℝ) ≤ 7 := parabola_near_card J i
  have hL : (L.card:ℝ) ≤ n := by
    dsimp only [L,n]
    exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun j => 3 < |i-j|) J)
  have hnear : A ≤ 7*M := by
    calc
      A ≤ ∑ _j ∈ K, M := Finset.sum_le_sum fun j hj => hmax j (Finset.mem_filter.mp hj).1
      _ = (K.card:ℝ)*M := by simp
      _ ≤ 7*M := mul_le_mul_of_nonneg_right hK hM
  have hfar : B ≤ n*M := by
    calc
      B ≤ ∑ _j ∈ L, M := Finset.sum_le_sum fun j hj => hmax j (Finset.mem_filter.mp hj).1
      _ = (L.card:ℝ)*M := by simp
      _ ≤ n*M := mul_le_mul_of_nonneg_right hL hM
  have hfar₂ : B^2 ≤ n*∑ j ∈ L, ‖f j‖^2 :=
    (sq_sum_le_card_mul_sum_sq (s:=L) (f:=fun j => ‖f j‖)).trans
      (mul_le_mul_of_nonneg_right hL (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hfar₆ : B^6 ≤ n^5*∑ j ∈ L, ‖f j‖^2*M^4 := by
    calc
      B^6 = B^4*B^2 := by ring
      _ ≤ (n*M)^4*(n*∑ j ∈ L, ‖f j‖^2) :=
        mul_le_mul (pow_le_pow_left₀ hB hfar 4) hfar₂ (sq_nonneg B) (by positivity)
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hdiag : M^6 ≤ ∑ j ∈ J, ‖f j‖^6 :=
    Finset.single_le_sum (fun j _ => pow_nonneg (norm_nonneg _) 6) hi
  have hcross : (∑ j ∈ L, ‖f j‖^2*M^4) ≤
      ∑ k ∈ J, ∑ j ∈ J.filter (fun j => 3 < |k-j|), ‖f j‖^2*‖f k‖^4 :=
by
    dsimp only [L,M]
    exact Finset.single_le_sum (f := fun k =>
      ∑ j ∈ J.filter (fun j => 3 < |k-j|), ‖f j‖^2*‖f k‖^4)
      (fun k _ => Finset.sum_nonneg fun j _ => by positivity) hi
  have hsplit : (∑ j ∈ J, ‖f j‖) = A+B := by
    dsimp [A,B,K,L]
    simpa only [not_le] using
      (Finset.sum_filter_add_sum_filter_not J (fun j => |i-j| ≤ 3) (fun j => ‖f j‖)).symm
  have hsum : ‖∑ j ∈ J, f j‖ ≤ A+B := by
    rw [← hsplit]
    exact norm_sum_le _ _
  have hnear₆ : A^6 ≤ 7^6*M^6 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hA hnear 6
  calc
    _ ≤ (A+B)^6 := pow_le_pow_left₀ (norm_nonneg _) hsum 6
    _ ≤ 64*(A^6+B^6) := add_sixth_le A B hA hB
    _ ≤ 64*(7^6*M^6+n^5*∑ j ∈ L, ‖f j‖^2*M^4) := by
      gcongr
    _ ≤ _ := by
      dsimp only [n]
      have hd := mul_le_mul_of_nonneg_left hdiag (by positivity : (0:ℝ) ≤ 64*7^6)
      have hc := mul_le_mul_of_nonneg_left hcross (by positivity : (0:ℝ) ≤ 64*(J.card:ℝ)^5)
      nlinarith only [hd,hc]

theorem parabolaWeightedSixNorm_bilinear_reduction {ι : Type*}
    (J : Finset ℤ) (S : ℤ → Finset ι) (z : ℤ → ι → ℂ) (x : ℤ → ι → ℝ)
    (W : ℝ × ℝ → ℝ) (hW₀ : ∀ p, 0 ≤ W p) (hW : Integrable W) :
    (parabolaWeightedSixNorm W (J.sigma S) (fun ij => z ij.1 ij.2)
      (fun ij => x ij.1 ij.2))^6 ≤
      (64*7^6:ℝ)*∑ i ∈ J, (parabolaWeightedSixNorm W (S i) (z i) (x i))^6 +
      64*(J.card:ℝ)^5*∑ i ∈ J, ∑ j ∈ J.filter (fun j => 3 < |i-j|),
        parabolaWeightedBilinearMoment W (S j) (S i) (z j) (z i) (x j) (x i) := by
  classical
  let F := fun i => fun p : ℝ × ℝ =>
    sargosPlanarSum (S i) (z i) (x i) (fun k => (x i k)^2) p.1 p.2
  let G := fun i j => fun p : ℝ × ℝ => W p*‖F i p‖^2*‖F j p‖^4
  let T := J.sigma S
  let Z := fun ij : (i : ℤ) × ι => z ij.1 ij.2
  let X := fun ij : (i : ℤ) × ι => x ij.1 ij.2
  let H := fun p : ℝ × ℝ => W p*
    ‖sargosPlanarSum T Z X (fun ij => (X ij)^2) p.1 p.2‖^2*
    ‖sargosPlanarSum T Z X (fun ij => (X ij)^2) p.1 p.2‖^4
  have hG (i j : ℤ) : Integrable (G i j) := by
    simpa only [G,F,parabolaMomentFunction,mul_assoc] using
      parabolaMomentFunction_integrable (S i) (S j) (z i) (z j) (x i) (x j) hW
  have hH : Integrable H := by
    simpa only [H,parabolaMomentFunction,mul_assoc] using
      parabolaMomentFunction_integrable T T Z Z X X hW
  have hs (p : ℝ × ℝ) :
      sargosPlanarSum T Z X (fun ij => (X ij)^2) p.1 p.2 = ∑ i ∈ J, F i p := by
    simp only [T,Z,X,F,sargosPlanarSum,Finset.sum_sigma]
  have hpoint (p : ℝ × ℝ) :
      H p ≤ (64*7^6:ℝ)*(∑ i ∈ J, G i i p) +
        64*(J.card:ℝ)^5*(∑ i ∈ J, ∑ j ∈ J.filter (fun j => 3 < |i-j|), G j i p) := by
    have hp := mul_le_mul_of_nonneg_left
      (parabola_bilinear_reduction_pointwise J (fun i => F i p)) (hW₀ p)
    have he (v : ℂ) : ‖v‖^6 = ‖v‖^2*‖v‖^4 := by ring
    dsimp only [H]
    rw [hs]
    simp_rw [he] at hp
    have hd : W p*((64*7^6:ℝ)*∑ i ∈ J, ‖F i p‖^2*‖F i p‖^4) =
        (64*7^6:ℝ)*∑ i ∈ J, G i i p := by
      rw [← mul_assoc,mul_comm (W p),mul_assoc,Finset.mul_sum]
      simp only [G,mul_assoc]
    have hc : W p*(64*(J.card:ℝ)^5*
        ∑ i ∈ J, ∑ j ∈ J.filter (fun j => 3 < |i-j|), ‖F j p‖^2*‖F i p‖^4) =
        64*(J.card:ℝ)^5*
          ∑ i ∈ J, ∑ j ∈ J.filter (fun j => 3 < |i-j|), G j i p := by
      rw [← mul_assoc,mul_comm (W p),mul_assoc]
      simp only [Finset.mul_sum,G,mul_assoc]
    rw [mul_add,hd,hc] at hp
    simpa only [mul_assoc] using hp
  have hdiag : Integrable (fun p => ∑ i ∈ J, G i i p) :=
    integrable_finsetSum J (fun i _ => hG i i)
  have hcross : Integrable (fun p => ∑ i ∈ J,
      ∑ j ∈ J.filter (fun j => 3 < |i-j|), G j i p) :=
    integrable_finsetSum J (fun i _ =>
      integrable_finsetSum _ (fun j _ => hG j i))
  have h := integral_mono hH
    ((hdiag.const_mul (64*7^6:ℝ)).add (hcross.const_mul (64*(J.card:ℝ)^5))) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add (hdiag.const_mul _) (hcross.const_mul _),
    integral_const_mul,integral_const_mul,
    integral_finsetSum J (fun i _ => hG i i),
    integral_finsetSum J (fun i _ => integrable_finsetSum _ (fun j _ => hG j i))] at h
  simp_rw [integral_finsetSum _ (fun j _ => hG j _)] at h
  simpa only [parabolaWeightedSixNorm_pow_six W hW₀ hW,
    parabolaWeightedBilinearMoment,H,T,Z,X,G,F] using h


end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private theorem parabolaWeightBand_mono {δ η : ℝ} {W : ℝ × ℝ → ℝ}
    (hW : ParabolaWeightBand δ W) (h : δ^2 ≤ η^2) : ParabolaWeightBand η W :=
  ⟨hW.1,hW.2.1,fun ξ κ hg => hW.2.2 ξ κ (h.trans hg)⟩

public  theorem finGrid_sum {k l : ℕ} {A : Type*} [AddCommMonoid A]
    (f : Fin (k*l) → A) :
    ∑ r, f r = ∑ i : Fin k, ∑ j : Fin l, f (finProdFinEquiv (i,j)) := by
  simpa only [Fintype.sum_prod_type] using (Equiv.sum_comp finProdFinEquiv f).symm

public  theorem finGrid_cell {k l : ℕ} (hk : 0 < k) (hl : 0 < l)
    (i : Fin k) (j : Fin l) :
    ((finProdFinEquiv (i,j) : Fin (k*l)):ℕ)/(k*l:ℝ) =
      (i:ℕ)/(k:ℝ)+(1/(k:ℝ))*((j:ℕ)/(l:ℝ)) ∧
    (((finProdFinEquiv (i,j) : Fin (k*l)):ℕ)+1)/(k*l:ℝ) =
      (i:ℕ)/(k:ℝ)+(1/(k:ℝ))*(((j:ℕ)+1)/(l:ℝ)) := by
  have hk' : (k:ℝ) ≠ 0 := by positivity
  have hl' : (l:ℝ) ≠ 0 := by positivity
  simp only [finProdFinEquiv,Equiv.coe_fn_mk,Nat.cast_add,Nat.cast_mul]
  constructor <;> field_simp <;> ring

                                                                                  
theorem ParabolaDecouplingBound.mul {k l : ℕ} {A B : ℝ}
    (hk : 0 < k) (hl : 0 < l)
    (hA : ParabolaDecouplingBound.{u} k A) (hB : ParabolaDecouplingBound.{u} l B) :
    ParabolaDecouplingBound.{u} (k*l) (A*B) := by
  refine ⟨mul_nonneg hA.1 hB.1,fun ι W hW S z x hx => ?_⟩
  let e : Fin k × Fin l ≃ Fin (k*l) := finProdFinEquiv
  let T := fun i : Fin k => Finset.univ.sigma (fun j : Fin l => S (e (i,j)))
  let Z := fun i : Fin k => fun jk : (j : Fin l) × ι => z (e (i,jk.1)) jk.2
  let X := fun i : Fin k => fun jk : (j : Fin l) × ι => x (e (i,jk.1)) jk.2
  have hk' : (0:ℝ) < k := by positivity
  have hl' : (0:ℝ) < l := by positivity
  have hwidth : 1/((k*l:ℕ):ℝ) = (1/(k:ℝ))/(l:ℝ) := by
    rw [Nat.cast_mul,div_div]
  have hsmall : 1/((k*l:ℕ):ℝ) ≤ 1/(k:ℝ) := by
    apply one_div_le_one_div_of_le hk'
    have hl₁ : (1:ℝ) ≤ l := by exact_mod_cast hl
    rw [Nat.cast_mul]
    nlinarith
  have hWk : ParabolaWeightBand (1/(k:ℝ)) W :=
    parabolaWeightBand_mono hW (pow_le_pow_left₀ (by positivity) hsmall 2)
  have hfine (i : Fin k) (j : Fin l) (v : ι) (hv : v ∈ S (e (i,j))) :
      x (e (i,j)) v ∈ Icc
        ((i:ℕ)/(k:ℝ)+(1/(k:ℝ))*((j:ℕ)/(l:ℝ)))
        ((i:ℕ)/(k:ℝ)+(1/(k:ℝ))*(((j:ℕ)+1)/(l:ℝ))) := by
    have h := hx (e (i,j)) v hv
    simpa only [Nat.cast_mul,(finGrid_cell hk hl i j).1,
      (finGrid_cell hk hl i j).2,e] using h
  have hcoarse (i : Fin k) (v : (j : Fin l) × ι) (hv : v ∈ T i) :
      X i v ∈ Icc ((i:ℕ)/(k:ℝ)) (((i:ℕ)+1)/(k:ℝ)) := by
    have hf := hfine i v.1 v.2 (Finset.mem_sigma.mp hv).2
    have hj : ((v.1:ℕ)+1)/(l:ℝ) ≤ 1 := by
      apply (div_le_iff₀ hl').mpr
      simpa only [one_mul] using (show ((v.1:ℕ):ℝ)+1 ≤ l by exact_mod_cast v.1.isLt)
    have hz : 0 ≤ (v.1:ℕ)/(l:ℝ) := by positivity
    have hp : 0 ≤ 1/(k:ℝ) := by positivity
    change x (e (i,v.1)) v.2 ∈ _
    constructor
    · nlinarith [hf.1,mul_nonneg hp hz]
    · have hu := mul_le_mul_of_nonneg_left hj hp
      have he : (((i:ℕ):ℝ)+1)/(k:ℝ) = (i:ℕ)/(k:ℝ)+1/(k:ℝ) := by ring
      rw [he]
      nlinarith [hf.2]
  have h := hA.2 ((j : Fin l) × ι) W hWk T Z X hcoarse
  have hpart (i : Fin k) :
      (parabolaWeightedSixNorm W (T i) (Z i) (X i))^2 ≤
        B^2*∑ j : Fin l,
          (parabolaWeightedSixNorm W (S (e (i,j))) (z (e (i,j))) (x (e (i,j))))^2 := by
    apply hB.rescale (a := (i:ℕ)/(k:ℝ)) (σ := 1/(k:ℝ))
      (by positivity) (by positivity) ?_ ι W
      (by simpa only [hwidth] using hW)
      (fun j => S (e (i,j))) (fun j => z (e (i,j))) (fun j => x (e (i,j)))
      (hfine i)
    rw [← add_div]
    apply (div_le_iff₀ hk').mpr
    have hi : ((i:ℕ):ℝ)+1 ≤ k := by exact_mod_cast i.isLt
    simpa only [one_mul,← add_div] using hi
  have htotal :
      parabolaWeightedSixNorm W (Finset.univ.sigma S)
        (fun rv => z rv.1 rv.2) (fun rv => x rv.1 rv.2) =
      parabolaWeightedSixNorm W (Finset.univ.sigma T)
        (fun iv => Z iv.1 iv.2) (fun iv => X iv.1 iv.2) := by
    unfold parabolaWeightedSixNorm
    congr 1
    funext p
    simp only [sargosPlanarSum,Finset.sum_sigma,T,Z,X]
    exact finGrid_sum _
  rw [htotal]
  refine h.trans ?_
  have hp := Finset.sum_le_sum (fun i (_hi : i ∈ Finset.univ) => hpart i)
  have hm := mul_le_mul_of_nonneg_left hp (sq_nonneg A)
  rw [← Finset.mul_sum] at hm
  have he := finGrid_sum (fun r =>
    (parabolaWeightedSixNorm W (S r) (z r) (x r))^2)
  rw [he]
  nlinarith only [hm]

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

                                                                     
                                                                                     
def ParabolaBilinearSixBound (δ : ℝ) (p q : ℕ) (ν K : ℝ) : Prop :=
  0 ≤ K ∧ ∀ (ι τ : Type u) (W : ℝ × ℝ → ℝ), ParabolaWeightBand δ W →
    ∀ (a b : ℝ), 0 ≤ a → a+δ*p ≤ 1 → 0 ≤ b → b+δ*q ≤ 1 →
      (a+δ*p+3*ν ≤ b ∨ b+δ*q+3*ν ≤ a) →
      ∀ (S : Fin p → Finset ι) (V : Fin q → Finset τ)
        (z : Fin p → ι → ℂ) (c : Fin q → τ → ℂ)
        (x : Fin p → ι → ℝ) (y : Fin q → τ → ℝ),
      (∀ j, ∀ k ∈ S j, x j k ∈ Icc (a+δ*(j:ℕ)) (a+δ*((j:ℕ)+1))) →
      (∀ j, ∀ k ∈ V j, y j k ∈ Icc (b+δ*(j:ℕ)) (b+δ*((j:ℕ)+1))) →
      parabolaWeightedBilinearMoment W (Finset.univ.sigma S) (Finset.univ.sigma V)
        (fun jk => z jk.1 jk.2) (fun jk => c jk.1 jk.2)
        (fun jk => x jk.1 jk.2) (fun jk => y jk.1 jk.2) ≤
          K*(∑ j, (parabolaWeightedSixNorm W (S j) (z j) (x j))^2)*
            (∑ j, (parabolaWeightedSixNorm W (V j) (c j) (y j))^2)^2

private theorem parabola_grid_rescale_bound {n : ℕ} {D δ a : ℝ}
    (hn : 0 < n) (hδ : 0 < δ) (hD : ParabolaDecouplingBound.{u} n D)
    (ha : 0 ≤ a) (haδ : a+δ*n ≤ 1)
    (ι : Type u) (W : ℝ × ℝ → ℝ) (hW : ParabolaWeightBand δ W)
    (S : Fin n → Finset ι) (z : Fin n → ι → ℂ) (x : Fin n → ι → ℝ)
    (hx : ∀ j, ∀ k ∈ S j, x j k ∈ Icc (a+δ*(j:ℕ)) (a+δ*((j:ℕ)+1))) :
    (parabolaWeightedSixNorm W (Finset.univ.sigma S)
      (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2))^2 ≤
      D^2*∑ j, (parabolaWeightedSixNorm W (S j) (z j) (x j))^2 := by
  have hn' : (n:ℝ) ≠ 0 := by positivity
  apply hD.rescale (a:=a) (σ:=δ*n) (by positivity) ha haδ ι W
    (by simpa only [mul_div_cancel_right₀ _ hn'] using hW) S z x
  intro j k hk
  have h := hx j k hk
  have hleft : δ*n*((j:ℕ)/(n:ℝ)) = δ*(j:ℕ) := by field_simp
  have hright : δ*n*(((j:ℕ)+1)/(n:ℝ)) = δ*((j:ℕ)+1) := by field_simp
  simpa only [hleft,hright] using h

                                                                       
theorem parabolaBilinearSixBound_of_linear {p q : ℕ} {δ ν A B : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hδ : 0 < δ)
    (hA : ParabolaDecouplingBound.{u} p A) (hB : ParabolaDecouplingBound.{u} q B) :
    ParabolaBilinearSixBound.{u} δ p q ν (A^2*B^4) := by
  refine ⟨by positivity,fun ι τ W hW a b ha haδ hb hbδ _ S V z c x y hx hy => ?_⟩
  have hS := parabola_grid_rescale_bound hp hδ hA ha haδ ι W hW S z x hx
  have hV := parabola_grid_rescale_bound hq hδ hB hb hbδ τ W hW V c y hy
  have hm := parabolaWeightedBilinearMoment_le_sixNorm W hW.1 hW.2.1
    (Finset.univ.sigma S) (Finset.univ.sigma V)
    (fun jk => z jk.1 jk.2) (fun jk => c jk.1 jk.2)
    (fun jk => x jk.1 jk.2) (fun jk => y jk.1 jk.2)
  refine hm.trans ?_
  have hV₂ := pow_le_pow_left₀ (sq_nonneg _) hV 2
  have hs := mul_le_mul hS hV₂ (sq_nonneg _) (by positivity)
  convert hs using 1 <;> ring

theorem ParabolaBilinearSixBound.holder_swap {p q : ℕ} {δ ν K B : ℝ}
    (hq : 0 < q) (hδ : 0 < δ)
    (hK : ParabolaBilinearSixBound.{u} δ q p ν K)
    (hB : ParabolaDecouplingBound.{u} q B) :
    ParabolaBilinearSixBound.{u} δ p q ν (Real.sqrt K*B^3) := by
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hB.1 3),
    fun ι τ W hW a b ha haδ hb hbδ hsep S V z c x y hx hy => ?_⟩
  let ES := ∑ j, (parabolaWeightedSixNorm W (S j) (z j) (x j))^2
  let EV := ∑ j, (parabolaWeightedSixNorm W (V j) (c j) (y j))^2
  let M := parabolaWeightedBilinearMoment W (Finset.univ.sigma S) (Finset.univ.sigma V)
    (fun jk => z jk.1 jk.2) (fun jk => c jk.1 jk.2)
    (fun jk => x jk.1 jk.2) (fun jk => y jk.1 jk.2)
  let N := parabolaWeightedBilinearMoment W (Finset.univ.sigma V) (Finset.univ.sigma S)
    (fun jk => c jk.1 jk.2) (fun jk => z jk.1 jk.2)
    (fun jk => y jk.1 jk.2) (fun jk => x jk.1 jk.2)
  let Q := parabolaWeightedSixNorm W (Finset.univ.sigma V)
    (fun jk => c jk.1 jk.2) (fun jk => y jk.1 jk.2)
  have hES : 0 ≤ ES := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hEV : 0 ≤ EV := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hM : 0 ≤ M := integral_nonneg fun r =>
    mul_nonneg (mul_nonneg (hW.1 r) (sq_nonneg _)) (pow_nonneg (norm_nonneg _) 4)
  have hN : N ≤ K*EV*ES^2 :=
    hK.2 τ ι W hW b a hb hbδ ha haδ hsep.symm V S c z y x hy hx
  have hQ : Q^2 ≤ B^2*EV :=
    parabola_grid_rescale_bound hq hδ hB hb hbδ τ W hW V c y hy
  have hMN : M^2 ≤ N*Q^6 := by
    simpa only [M,N,Q,parabolaWeightedSixNorm_pow_six W hW.1 hW.2.1] using
      parabolaWeightedBilinearMoment_holder_swap W hW.1 hW.2.1
        (Finset.univ.sigma S) (Finset.univ.sigma V)
        (fun jk => z jk.1 jk.2) (fun jk => c jk.1 jk.2)
        (fun jk => x jk.1 jk.2) (fun jk => y jk.1 jk.2)
  have hQ₆ : Q^6 ≤ B^6*EV^3 := by
    convert pow_le_pow_left₀ (sq_nonneg Q) hQ 3 using 1 <;> ring
  have hprod := mul_le_mul hN hQ₆ (by positivity : 0 ≤ Q^6)
    (mul_nonneg (mul_nonneg hK.1 hEV) (sq_nonneg ES))
  have he : (Real.sqrt K*B^3*ES*EV^2)^2 = (K*EV*ES^2)*(B^6*EV^3) := by
    rw [show (Real.sqrt K*B^3*ES*EV^2)^2 =
      (Real.sqrt K)^2*B^6*ES^2*EV^4 by ring,Real.sq_sqrt hK.1]
    ring
  have hB₀ := hB.1
  change M ≤ Real.sqrt K*B^3*ES*EV^2
  apply (pow_le_pow_iff_left₀ hM (by positivity) (by norm_num : (2:ℕ) ≠ 0)).mp
  rw [he]
  exact hMN.trans hprod


end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private def parabolaIntGridIndex (k : ℕ) (hk : 0 < k) (i : ℤ) : Fin k :=
  ⟨i.toNat % k,Nat.mod_lt _ hk⟩

private theorem parabolaIntGridIndex_cast {k : ℕ} (hk : 0 < k) (i : Fin k) :
    parabolaIntGridIndex k hk (i:ℕ) = i := by
  apply Fin.ext
  simp [parabolaIntGridIndex,Nat.mod_eq_of_lt i.isLt]

private theorem parabolaIntGridIndex_val {k : ℕ} (hk : 0 < k) {i : ℤ}
    (hi : i ∈ Finset.Ico 0 (k:ℤ)) :
    ((parabolaIntGridIndex k hk i : Fin k):ℕ) = i.toNat := by
  have hh := Finset.mem_Ico.mp hi
  simp only [parabolaIntGridIndex]
  exact Nat.mod_eq_of_lt (by omega)

private theorem parabola_intGrid_sum {k : ℕ} (hk : 0 < k)
    {A : Type*} [AddCommMonoid A] (f : Fin k → A) :
    ∑ i ∈ Finset.Ico 0 (k:ℤ), f (parabolaIntGridIndex k hk i) = ∑ j, f j := by
  classical
  symm
  refine Finset.sum_bij (fun j _ => (j:ℤ)) ?_ ?_ ?_ ?_
  · intro j _
    apply Finset.mem_Ico.mpr
    constructor
    · exact_mod_cast (Nat.zero_le (j:ℕ))
    · exact_mod_cast j.isLt
  · intro i _ j _ h
    apply Fin.ext
    exact_mod_cast h
  · intro i hi
    have hh := Finset.mem_Ico.mp hi
    refine ⟨⟨i.toNat,by omega⟩,Finset.mem_univ _,?_⟩
    dsimp
    omega
  · intro i _
    rw [parabolaIntGridIndex_cast]

private theorem parabolaWeightedBilinearMoment_fin_localization {k : ℕ}
    (hk : 0 < k) {ι τ : Type*}
    (S : Fin k → Finset ι) (V : Finset τ)
    (z : Fin k → ι → ℂ) (c : τ → ℂ) (x : Fin k → ι → ℝ) (y : τ → ℝ)
    {w a β u ν δ : ℝ} {W : ℝ × ℝ → ℝ}
    (hW : ParabolaWeightBand δ W)
    (hw : 0 < w) (hν : 0 < ν) (hν₁ : ν ≤ 1) (hβ : β ∈ Icc 0 1)
    (hwidth : δ^2 ≤ w^2) (hu : u ≤ ν) (hd : 3*ν ≤ |a-β|)
    (hx : ∀ i, ∀ v ∈ S i, x i v ∈ Icc a (a+u))
    (hy : ∀ v ∈ V, y v ∈ Icc β (β+w))
    (hblock : ∀ i, ∀ v ∈ S i,
      x i v ∈ Icc (a+w^2*(i:ℕ)) (a+w^2*((i:ℕ)+1))) :
    parabolaWeightedBilinearMoment W (Finset.univ.sigma S) V
      (fun iv => z iv.1 iv.2) c (fun iv => x iv.1 iv.2) y ≤
      (7/ν)*∑ i, parabolaWeightedBilinearMoment W (S i) V (z i) c (x i) y := by
  let R := parabolaIntGridIndex k hk
  let J := Finset.Ico 0 (k:ℤ)
  have hR (i : ℤ) (hi : i ∈ J) : ((R i:Fin k):ℝ) = (i:ℝ) := by
    have hv := parabolaIntGridIndex_val hk hi
    have hn : 0 ≤ i := (Finset.mem_Ico.mp hi).1
    change (((R i:Fin k):ℕ):ℝ) = _
    rw [hv]
    exact_mod_cast Int.toNat_of_nonneg hn
  have h := parabolaWeightedBilinearMoment_localization_closed J
    (fun i => S (R i)) V (fun i => z (R i)) c (fun i => x (R i)) y
    hW hw hν hν₁ hβ hwidth hu hd
    (fun i _ => hx (R i)) hy (fun i hi v hv => by
      simpa only [hR i hi] using hblock (R i) v hv)
  have he (α γ : ℝ) :
      sargosPlanarSum (J.sigma (fun i => S (R i)))
        (fun iv => z (R iv.1) iv.2) (fun iv => x (R iv.1) iv.2)
        (fun iv => (x (R iv.1) iv.2)^2) α γ =
      sargosPlanarSum (Finset.univ.sigma S) (fun iv => z iv.1 iv.2)
        (fun iv => x iv.1 iv.2) (fun iv => (x iv.1 iv.2)^2) α γ := by
    simp only [sargosPlanarSum,Finset.sum_sigma]
    exact parabola_intGrid_sum hk (fun i => ∑ v ∈ S i,
      z i v*fordAdditiveCharacter (x i v*α+(x i v)^2*γ))
  have hm : parabolaWeightedBilinearMoment W (J.sigma (fun i => S (R i))) V
      (fun iv => z (R iv.1) iv.2) c (fun iv => x (R iv.1) iv.2) y =
      parabolaWeightedBilinearMoment W (Finset.univ.sigma S) V
        (fun iv => z iv.1 iv.2) c (fun iv => x iv.1 iv.2) y := by
    unfold parabolaWeightedBilinearMoment
    simp_rw [he]
  rw [hm] at h
  have hsum := parabola_intGrid_sum hk (fun i =>
    parabolaWeightedBilinearMoment W (S i) V (z i) c (x i) y)
  change (∑ i ∈ J, parabolaWeightedBilinearMoment W (S (R i)) V (z (R i)) c (x (R i)) y) = _ at hsum
  rw [hsum] at h
  exact h

universe u

                                                                           
                                                                                 
theorem ParabolaBilinearSixBound.localization {k m q : ℕ} {δ ν K : ℝ}
    (hk : 0 < k) (hq : 0 < q) (hδ : 0 < δ)
    (hν : 0 < ν) (hν₁ : ν ≤ 1)
    (hsmall : δ*(k*m) ≤ ν) (hscale : δ*m = (δ*q)^2)
    (hK : ParabolaBilinearSixBound.{u} δ m q ν K) :
    ParabolaBilinearSixBound.{u} δ (k*m) q ν ((7/ν)*K) := by
  refine ⟨mul_nonneg (by positivity) hK.1,
    fun ι τ W hW a b ha haδ hb hbδ hsep S V z c x y hx hy => ?_⟩
  simp only [Nat.cast_mul] at haδ hsep
  let e : Fin k × Fin m ≃ Fin (k*m) := finProdFinEquiv
  let T := fun i : Fin k => Finset.univ.sigma (fun j : Fin m => S (e (i,j)))
  let Z := fun i : Fin k => fun jv : (j : Fin m) × ι => z (e (i,jv.1)) jv.2
  let X := fun i : Fin k => fun jv : (j : Fin m) × ι => x (e (i,jv.1)) jv.2
  let U := Finset.univ.sigma V
  let C := fun jv : (j : Fin q) × τ => c jv.1 jv.2
  let Y := fun jv : (j : Fin q) × τ => y jv.1 jv.2
  let ai := fun i : Fin k => a+δ*m*(i:ℕ)
  have heval (i : Fin k) (j : Fin m) :
      ((e (i,j):Fin (k*m)):ℝ) = (j:ℕ)+(m:ℝ)*(i:ℕ) := by
    simp [e,finProdFinEquiv,Nat.cast_add,Nat.cast_mul]
  have hai (i : Fin k) : a ≤ ai i ∧ ai i+δ*m ≤ a+δ*(k*m) := by
    have hi : ((i:ℕ):ℝ)+1 ≤ k := by exact_mod_cast i.isLt
    have hp := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ δ*m)
    have hzero : 0 ≤ δ*m*(i:ℕ) := by positivity
    dsimp only [ai]
    constructor
    · linarith
    · nlinarith only [hp]
  have hfine (i : Fin k) (j : Fin m) (v : ι) (hv : v ∈ S (e (i,j))) :
      x (e (i,j)) v ∈ Icc (ai i+δ*(j:ℕ)) (ai i+δ*((j:ℕ)+1)) := by
    have hf := hx (e (i,j)) v hv
    change x (e (i,j)) v ∈ Icc (a+δ*((e (i,j):Fin (k*m)):ℝ))
      (a+δ*(((e (i,j):Fin (k*m)):ℝ)+1)) at hf
    rw [heval] at hf
    dsimp only [ai]
    constructor <;> nlinarith [hf.1,hf.2]
  have hblock (i : Fin k) (v : (j : Fin m) × ι) (hv : v ∈ T i) :
      X i v ∈ Icc (ai i) (ai i+δ*m) := by
    have hf := hfine i v.1 v.2 (Finset.mem_sigma.mp hv).2
    have hj : ((v.1:ℕ):ℝ)+1 ≤ m := by exact_mod_cast v.1.isLt
    have hp := mul_le_mul_of_nonneg_left hj hδ.le
    have hn : 0 ≤ δ*(v.1:ℕ) := by positivity
    constructor <;> dsimp only [X] <;> nlinarith [hf.1,hf.2]
  have hglobal (i : Fin k) (v : (j : Fin m) × ι) (hv : v ∈ T i) :
      X i v ∈ Icc a (a+δ*(k*m)) :=
    ⟨(hai i).1.trans (hblock i v hv).1,(hblock i v hv).2.trans (hai i).2⟩
  have hsecondary (v : (j : Fin q) × τ) (hv : v ∈ U) :
      Y v ∈ Icc b (b+δ*q) := by
    have hf := hy v.1 v.2 (Finset.mem_sigma.mp hv).2
    have hj : ((v.1:ℕ):ℝ)+1 ≤ q := by exact_mod_cast v.1.isLt
    have hp := mul_le_mul_of_nonneg_left hj hδ.le
    have hn : 0 ≤ δ*(v.1:ℕ) := by positivity
    constructor <;> dsimp only [Y] <;> nlinarith [hf.1,hf.2]
  have hd : 3*ν ≤ |a-b| := by
    rcases hsep with hs | hs
    · have hz : 0 ≤ δ*(k*m) := by positivity
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hz : 0 ≤ δ*q := by positivity
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hq₁ : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hwidth : δ^2 ≤ (δ*q)^2 :=
    pow_le_pow_left₀ hδ.le (by nlinarith) 2
  have hloc := parabolaWeightedBilinearMoment_fin_localization hk T U Z C X Y
    hW (by positivity : 0 < δ*q) hν hν₁
    (show b ∈ Icc 0 1 from ⟨hb,by nlinarith [mul_nonneg hδ.le (Nat.cast_nonneg q)]⟩)
    hwidth hsmall hd hglobal hsecondary (fun i v hv => by
      have h := hblock i v hv
      dsimp only [ai] at h
      simpa only [← hscale,mul_add,mul_one,mul_assoc,add_assoc] using h)

  let EV := ∑ j, (parabolaWeightedSixNorm W (V j) (c j) (y j))^2
  have hpiece (i : Fin k) :
      parabolaWeightedBilinearMoment W (T i) U (Z i) C (X i) Y ≤
        K*(∑ j : Fin m,
          (parabolaWeightedSixNorm W (S (e (i,j))) (z (e (i,j))) (x (e (i,j))))^2)*EV^2 := by
    have hsep' : ai i+δ*m+3*ν ≤ b ∨ b+δ*q+3*ν ≤ ai i := by
      rcases hsep with hs | hs
      · exact Or.inl (by linarith [(hai i).2])
      · exact Or.inr (by linarith [(hai i).1])
    exact hK.2 ι τ W hW (ai i) b (ha.trans (hai i).1) ((hai i).2.trans haδ)
      hb hbδ hsep' (fun j => S (e (i,j))) V (fun j => z (e (i,j))) c
      (fun j => x (e (i,j))) y (hfine i) hy
  have ht :
      parabolaWeightedBilinearMoment W (Finset.univ.sigma S) U
        (fun rv => z rv.1 rv.2) C (fun rv => x rv.1 rv.2) Y =
      parabolaWeightedBilinearMoment W (Finset.univ.sigma T) U
        (fun iv => Z iv.1 iv.2) C (fun iv => X iv.1 iv.2) Y := by
    unfold parabolaWeightedBilinearMoment
    apply integral_congr_ae
    filter_upwards with r
    have he :
        sargosPlanarSum (Finset.univ.sigma S) (fun rv => z rv.1 rv.2)
          (fun rv => x rv.1 rv.2) (fun rv => (x rv.1 rv.2)^2) r.1 r.2 =
        sargosPlanarSum (Finset.univ.sigma T) (fun iv => Z iv.1 iv.2)
          (fun iv => X iv.1 iv.2) (fun iv => (X iv.1 iv.2)^2) r.1 r.2 := by
      simp only [sargosPlanarSum,Finset.sum_sigma,T,Z,X]
      exact finGrid_sum _
    rw [he]
  change parabolaWeightedBilinearMoment W (Finset.univ.sigma S) U
    (fun rv => z rv.1 rv.2) C (fun rv => x rv.1 rv.2) Y ≤ _
  rw [ht]
  refine hloc.trans ?_
  have hp := Finset.sum_le_sum (fun i (_hi : i ∈ Finset.univ) => hpiece i)
  have hp' := mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ) ≤ 7/ν)
  have he : (∑ i : Fin k, K*(∑ j : Fin m,
      (parabolaWeightedSixNorm W (S (e (i,j))) (z (e (i,j))) (x (e (i,j))))^2)*EV^2) =
      K*(∑ r, (parabolaWeightedSixNorm W (S r) (z r) (x r))^2)*EV^2 := by
    rw [← Finset.sum_mul,← Finset.mul_sum,finGrid_sum]
  rw [he] at hp'
  simpa only [EV,mul_assoc] using hp'

                                                                    
                                                                  
theorem ParabolaBilinearSixBound.localization_holder {k m q : ℕ} {δ ν K B : ℝ}
    (hk : 0 < k) (hq : 0 < q) (hδ : 0 < δ) (hν : 0 < ν) (hν₁ : ν ≤ 1)
    (hsmall : δ*(k*m) ≤ ν) (hscale : δ*m = (δ*q)^2)
    (hK : ParabolaBilinearSixBound.{u} δ q m ν K)
    (hB : ParabolaDecouplingBound.{u} q B) :
    ParabolaBilinearSixBound.{u} δ (k*m) q ν ((7/ν)*(Real.sqrt K*B^3)) :=
  (hK.holder_swap hq hδ hB).localization hk hq hδ hν hν₁ hsmall hscale


end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem sum_nonneg_powers_le {ι : Type*} (J : Finset ι) (E : ι → ℝ)
    (hE : ∀ i ∈ J, 0 ≤ E i) {n : ℕ} (hn : n ≠ 0) :
    ∑ i ∈ J, (E i)^n ≤ (∑ i ∈ J, E i)^n := by
  classical
  induction J using Finset.induction_on with
  | empty => simp [zero_pow hn]
  | @insert a J ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    have hJ : ∀ i ∈ J, 0 ≤ E i := fun i hi => hE i (Finset.mem_insert_of_mem hi)
    calc
      E a^n+(∑ i ∈ J, (E i)^n) ≤ E a^n+(∑ i ∈ J, E i)^n :=
        add_le_add le_rfl (ih hJ)
      _ ≤ _ := pow_add_pow_le (hE a (Finset.mem_insert_self a J))
        (Finset.sum_nonneg hJ) hn

private theorem parabolaWeightedSixNorm_bilinear_budget {ι : Type*}
    (J : Finset ℤ) (S : ℤ → Finset ι) (z : ℤ → ι → ℂ) (x : ℤ → ι → ℝ)
    (W : ℝ × ℝ → ℝ) (hW₀ : ∀ p, 0 ≤ W p) (hW : Integrable W)
    (E : ℤ → ℝ) (A K : ℝ) (hE : ∀ i ∈ J, 0 ≤ E i) (hK : 0 ≤ K)
    (hdiag : ∀ i ∈ J, (parabolaWeightedSixNorm W (S i) (z i) (x i))^2 ≤ A^2*E i)
    (hfar : ∀ i ∈ J, ∀ j ∈ J, 3 < |i-j| →
      parabolaWeightedBilinearMoment W (S j) (S i) (z j) (z i) (x j) (x i) ≤ K*E j*(E i)^2) :
    (parabolaWeightedSixNorm W (J.sigma S)
      (fun iv => z iv.1 iv.2) (fun iv => x iv.1 iv.2))^6 ≤
      ((64*7^6:ℝ)*A^6+64*(J.card:ℝ)^5*K)*(∑ i ∈ J, E i)^3 := by
  have hmain := parabolaWeightedSixNorm_bilinear_reduction J S z x W hW₀ hW
  have hds : (∑ i ∈ J, (parabolaWeightedSixNorm W (S i) (z i) (x i))^6) ≤
      A^6*(∑ i ∈ J, E i)^3 := by
    calc
      _ ≤ ∑ i ∈ J, A^6*(E i)^3 := by
        apply Finset.sum_le_sum
        intro i hi
        convert pow_le_pow_left₀ (sq_nonneg _) (hdiag i hi) 3 using 1 <;> ring
      _ = A^6*∑ i ∈ J, (E i)^3 := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sum_nonneg_powers_le J E hE (by norm_num : (3:ℕ) ≠ 0)) (by positivity)
  have hc (i : ℤ) (hi : i ∈ J) :
      (∑ j ∈ J.filter (fun j => 3 < |i-j|),
        parabolaWeightedBilinearMoment W (S j) (S i) (z j) (z i) (x j) (x i)) ≤
      K*(∑ j ∈ J, E j)*(E i)^2 := by
    calc
      _ ≤ ∑ j ∈ J.filter (fun j => 3 < |i-j|), K*E j*(E i)^2 := by
        apply Finset.sum_le_sum
        intro j hj
        exact hfar i hi j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
      _ ≤ ∑ j ∈ J, K*E j*(E i)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun j hj _ => mul_nonneg (mul_nonneg hK (hE j hj)) (sq_nonneg _))
      _ = _ := by rw [← Finset.sum_mul,← Finset.mul_sum]
  have hcs : (∑ i ∈ J, ∑ j ∈ J.filter (fun j => 3 < |i-j|),
      parabolaWeightedBilinearMoment W (S j) (S i) (z j) (z i) (x j) (x i)) ≤
      K*(∑ i ∈ J, E i)^3 := by
    calc
      _ ≤ ∑ i ∈ J, K*(∑ j ∈ J, E j)*(E i)^2 := Finset.sum_le_sum hc
      _ = (K*(∑ j ∈ J, E j))*∑ i ∈ J, (E i)^2 := (Finset.mul_sum ..).symm
      _ ≤ (K*(∑ j ∈ J, E j))*(∑ i ∈ J, E i)^2 :=
        mul_le_mul_of_nonneg_left
          (sum_nonneg_powers_le J E hE (by norm_num : (2:ℕ) ≠ 0))
          (mul_nonneg hK (Finset.sum_nonneg hE))
      _ = _ := by ring
  have hd := mul_le_mul_of_nonneg_left hds (by positivity : (0:ℝ) ≤ 64*7^6)
  have hf := mul_le_mul_of_nonneg_left hcs (by positivity : (0:ℝ) ≤ 64*(J.card:ℝ)^5)
  nlinarith only [hmain,hd,hf]

private theorem parabola_sixth_budget_to_square {L E A K k : ℝ}
    (hE : 0 ≤ E) (hA : 0 ≤ A) (hK : 0 ≤ K) (hk : 1 ≤ k)
    (h : L^6 ≤ ((64*7^6:ℝ)*A^6+64*k^5*K)*E^3) :
    L^2 ≤ (14*A+2*k*K^((6:ℝ)⁻¹))^2*E := by
  let R := K^((6:ℝ)⁻¹)
  have hR : 0 ≤ R := Real.rpow_nonneg hK _
  have hR₆ : R^6 = K := by
    simpa only [R,Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow hK (by norm_num : (6:ℕ) ≠ 0)
  have hk₀ : 0 ≤ k := by linarith
  have hkp : k^5 ≤ k^6 := by
    have hp := mul_le_mul_of_nonneg_left hk (pow_nonneg hk₀ 5)
    simpa only [mul_one,← pow_succ] using hp
  have hab := pow_add_pow_le (by positivity : 0 ≤ 14*A)
    (by positivity : 0 ≤ 2*k*R) (by norm_num : (6:ℕ) ≠ 0)
  have hb : (64*7^6:ℝ)*A^6+64*k^5*K ≤ (14*A+2*k*R)^6 := by
    have he : (14*A)^6+(2*k*R)^6 = (64*7^6:ℝ)*A^6+64*k^6*K := by
      rw [mul_pow, mul_pow, mul_pow,hR₆]
      ring
    rw [he] at hab
    have hp := mul_le_mul_of_nonneg_right hkp (mul_nonneg (by norm_num : (0:ℝ) ≤ 64) hK)
    nlinarith only [hab,hp]
  have hc := h.trans (mul_le_mul_of_nonneg_right hb (pow_nonneg hE 3))
  apply (pow_le_pow_iff_left₀ (sq_nonneg L) (by positivity)
    (by norm_num : (3:ℕ) ≠ 0)).mp
  change (L^2)^3 ≤ ((14*A+2*k*R)^2*E)^3
  convert hc using 1 <;> ring

universe u

set_option maxHeartbeats 1000000 in
                                                                          
                                                                           
theorem ParabolaDecouplingBound.of_bilinear {k l : ℕ} {A K : ℝ}
    (hk : 0 < k) (hl : 0 < l) (hA : ParabolaDecouplingBound.{u} l A)
    (hK : ParabolaBilinearSixBound.{u} (1/((k*l:ℕ):ℝ)) l l (1/(k:ℝ)) K) :
    ParabolaDecouplingBound.{u} (k*l) (14*A+2*k*K^((6:ℝ)⁻¹)) := by
  have hA₀ := hA.1
  have hK₀ := hK.1
  refine ⟨by positivity,fun ι W hW S z x hx => ?_⟩
  let δ : ℝ := 1/((k*l:ℕ):ℝ)
  let e : Fin k × Fin l ≃ Fin (k*l) := finProdFinEquiv
  let T := fun i : Fin k => Finset.univ.sigma (fun j : Fin l => S (e (i,j)))
  let Z := fun i : Fin k => fun jv : (j : Fin l) × ι => z (e (i,jv.1)) jv.2
  let X := fun i : Fin k => fun jv : (j : Fin l) × ι => x (e (i,jv.1)) jv.2
  let E := fun i : Fin k => ∑ j : Fin l,
    (parabolaWeightedSixNorm W (S (e (i,j))) (z (e (i,j))) (x (e (i,j))))^2
  let ai := fun i : Fin k => (i:ℕ)/(k:ℝ)
  let R := parabolaIntGridIndex k hk
  let J := Finset.Ico 0 (k:ℤ)
  have hk' : (0:ℝ) < k := by positivity
  have hl' : (0:ℝ) < l := by positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδl : δ*l = 1/(k:ℝ) := by
    dsimp [δ]
    push_cast
    field_simp
  have hfine (i : Fin k) (j : Fin l) (v : ι) (hv : v ∈ S (e (i,j))) :
      x (e (i,j)) v ∈ Icc (ai i+δ*(j:ℕ)) (ai i+δ*((j:ℕ)+1)) := by
    have h := hx (e (i,j)) v hv
    simp only [Nat.cast_mul] at h
    have hcell := finGrid_cell hk hl i j
    change x (e (i,j)) v ∈ Icc
      (((e (i,j):Fin (k*l)):ℝ)/(k*l:ℝ))
      ((((e (i,j):Fin (k*l)):ℝ)+1)/(k*l:ℝ)) at h
    rw [hcell.1,hcell.2] at h
    convert h using 1
    dsimp [ai,δ]
    push_cast
    field_simp
  have hai (i : Fin k) : 0 ≤ ai i := by dsimp [ai]; positivity
  have htop (i : Fin k) : ai i+δ*l ≤ 1 := by
    rw [hδl]
    dsimp only [ai]
    rw [← add_div]
    apply (div_le_iff₀ hk').mpr
    simpa only [one_mul] using
      (show ((i:ℕ):ℝ)+1 ≤ k by exact_mod_cast i.isLt)
  have hlin (i : Fin k) :
      (parabolaWeightedSixNorm W (T i) (Z i) (X i))^2 ≤ A^2*E i :=
    parabola_grid_rescale_bound hl hδ hA (hai i) (htop i) ι W hW
      (fun j => S (e (i,j))) (fun j => z (e (i,j))) (fun j => x (e (i,j))) (hfine i)
  have hR (i : ℤ) (hi : i ∈ J) : ((R i:Fin k):ℝ) = (i:ℝ) := by
    have hv := parabolaIntGridIndex_val hk hi
    have hn : 0 ≤ i := (Finset.mem_Ico.mp hi).1
    change (((R i:Fin k):ℕ):ℝ) = _
    rw [hv]
    exact_mod_cast Int.toNat_of_nonneg hn
  have hfar (i : ℤ) (hi : i ∈ J) (j : ℤ) (hj : j ∈ J) (hij : 3 < |i-j|) :
      parabolaWeightedBilinearMoment W (T (R j)) (T (R i))
        (Z (R j)) (Z (R i)) (X (R j)) (X (R i)) ≤ K*E (R j)*(E (R i))^2 := by
    have hsep : ai (R j)+δ*l+3*(1/(k:ℝ)) ≤ ai (R i) ∨
        ai (R i)+δ*l+3*(1/(k:ℝ)) ≤ ai (R j) := by
      dsimp only [ai]
      rw [hδl,hR i hi,hR j hj]
      rcases le_total i j with h | h
      · right
        have hh : i+4 ≤ j := by
          rw [abs_of_nonpos (sub_nonpos.mpr h)] at hij
          omega
        have hh' : (i:ℝ)+4 ≤ j := by exact_mod_cast hh
        convert div_le_div_of_nonneg_right hh' hk'.le using 1
        ring
      · left
        have hh : j+4 ≤ i := by
          rw [abs_of_nonneg (sub_nonneg.mpr h)] at hij
          omega
        have hh' : (j:ℝ)+4 ≤ i := by exact_mod_cast hh
        convert div_le_div_of_nonneg_right hh' hk'.le using 1
        ring
    exact hK.2 ι ι W hW (ai (R j)) (ai (R i)) (hai _) (htop _) (hai _) (htop _) hsep
      (fun v => S (e (R j,v))) (fun v => S (e (R i,v)))
      (fun v => z (e (R j,v))) (fun v => z (e (R i,v)))
      (fun v => x (e (R j,v))) (fun v => x (e (R i,v))) (hfine (R j)) (hfine (R i))

  have hE : ∀ i ∈ J, 0 ≤ E (R i) := fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbudget := parabolaWeightedSixNorm_bilinear_budget J
    (fun i => T (R i)) (fun i => Z (R i)) (fun i => X (R i)) W hW.1 hW.2.1
    (fun i => E (R i)) A K hE hK.1 (fun i _ => hlin (R i)) hfar
  have hcard : (J.card:ℝ) = k := by simp [J,Int.card_Ico]
  rw [hcard] at hbudget
  have hsq := parabola_sixth_budget_to_square (Finset.sum_nonneg hE) hA.1 hK.1
    (show (1:ℝ) ≤ k by exact_mod_cast hk) hbudget
  have hsum : (∑ i ∈ J, E (R i)) =
      ∑ r, (parabolaWeightedSixNorm W (S r) (z r) (x r))^2 := by
    calc
      _ = ∑ i : Fin k, E i := parabola_intGrid_sum hk E
      _ = _ := by
        dsimp only [E,e]
        exact (finGrid_sum (fun r => (parabolaWeightedSixNorm W (S r) (z r) (x r))^2)).symm
  rw [hsum] at hsq
  have htotal :
      parabolaWeightedSixNorm W (Finset.univ.sigma S)
        (fun rv => z rv.1 rv.2) (fun rv => x rv.1 rv.2) =
      parabolaWeightedSixNorm W (J.sigma (fun i => T (R i)))
        (fun iv => Z (R iv.1) iv.2) (fun iv => X (R iv.1) iv.2) := by
    unfold parabolaWeightedSixNorm
    congr 1
    funext r
    simp only [sargosPlanarSum,Finset.sum_sigma]
    have hs := parabola_intGrid_sum hk (fun i => ∑ v ∈ T i,
      Z i v*fordAdditiveCharacter (X i v*r.1+(X i v)^2*r.2))
    rw [hs]
    simp only [T,Z,X,Finset.sum_sigma]
    exact finGrid_sum _
  rw [htotal]
  exact hsq

                                                                         
theorem ParabolaDecouplingBound.of_bilinear_dyadic {n r : ℕ} {A K : ℝ}
    (hr : r ≤ n) (hA : ParabolaDecouplingBound.{u} (2^(n-r)) A)
    (hK : ParabolaBilinearSixBound.{u} (1/(2:ℝ)^n)
      (2^(n-r)) (2^(n-r)) (1/(2:ℝ)^r) K) :
    ParabolaDecouplingBound.{u} (2^n) (14*A+2*(2:ℝ)^r*K^((6:ℝ)⁻¹)) := by
  have hcount : (2:ℕ)^r*2^(n-r) = 2^n := by
    rw [← pow_add]
    congr 1
    omega
  have hK' : ParabolaBilinearSixBound.{u} (1/(((2:ℕ)^r*2^(n-r):ℕ):ℝ))
      (2^(n-r)) (2^(n-r)) (1/((2^r:ℕ):ℝ)) K := by
    simpa only [hcount,Nat.cast_pow,Nat.cast_ofNat] using hK
  have h := ParabolaDecouplingBound.of_bilinear
    (by positivity : 0 < (2:ℕ)^r) (by positivity : 0 < (2:ℕ)^(n-r)) hA hK'
  simpa only [hcount,Nat.cast_pow,Nat.cast_ofNat] using h


end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private theorem dyadic_width_mul_cells {a n : ℕ} (ha : a ≤ n) :
    (1/(2:ℝ)^n)*(2:ℝ)^(n-a) = 1/(2:ℝ)^a := by
  rw [pow_sub₀ (2:ℝ) (by norm_num) ha]
  field_simp

private theorem dyadic_width_sq (b : ℕ) :
    (1/(2:ℝ)^b)^2 = 1/(2:ℝ)^(2*b) := by
  rw [div_pow,one_pow,← pow_mul]
  congr 2
  omega

                                                            
theorem ParabolaBilinearSixBound.dyadic_step {n a b r : ℕ} {K B : ℝ}
    (ha : a ≤ 2*b) (hb : 2*b ≤ n) (hr : r ≤ a)
    (hK : ParabolaBilinearSixBound.{u} (1/(2:ℝ)^n)
      (2^(n-b)) (2^(n-2*b)) (1/(2:ℝ)^r) K)
    (hB : ParabolaDecouplingBound.{u} (2^(n-b)) B) :
    ParabolaBilinearSixBound.{u} (1/(2:ℝ)^n)
      (2^(n-a)) (2^(n-b)) (1/(2:ℝ)^r)
      ((7/(1/(2:ℝ)^r))*(Real.sqrt K*B^3)) := by
  have hcount : (2:ℕ)^(2*b-a)*2^(n-2*b) = 2^(n-a) := by
    rw [← pow_add]
    congr 1
    omega
  have hsmall : (1/(2:ℝ)^n)*((2:ℕ)^(2*b-a)*(2:ℕ)^(n-2*b)) ≤ 1/(2:ℝ)^r := by
    push_cast
    rw [← pow_add,show (2*b-a)+(n-2*b) = n-a by omega,
      dyadic_width_mul_cells (ha.trans hb)]
    exact one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hr)
  have hscale : (1/(2:ℝ)^n)*(((2:ℕ)^(n-2*b):ℕ):ℝ) =
      ((1/(2:ℝ)^n)*(((2:ℕ)^(n-b):ℕ):ℝ))^2 := by
    push_cast
    rw [dyadic_width_mul_cells hb,dyadic_width_mul_cells (by omega : b ≤ n),
      dyadic_width_sq]
  have hν₁ : 1/(2:ℝ)^r ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2^r)).mpr
    simpa only [one_mul] using one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n:=r)
  have h := hK.localization_holder (k:=2^(2*b-a)) (by positivity) (by positivity)
    (by positivity) (by positivity) hν₁ (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hsmall) hscale hB
  simpa only [hcount] using h

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

                                                                                    
def parabolaDyadicBilinearBudget (D : ℕ → ℝ) (n r : ℕ) : ℕ → ℕ → ℕ → ℝ
  | 0,a,b => (D (n-a))^2*(D (n-b))^4
  | t+1,_,b => (7/(1/(2:ℝ)^r))*
      (Real.sqrt (parabolaDyadicBilinearBudget D n r t b (2*b))*(D (n-b))^3)

                                                                           
theorem parabolaBilinearSixBound_dyadic_iterate (D : ℕ → ℝ)
    {n r a b t : ℕ} (hr : 0 < r) (hra : r ≤ a) (hab : a ≤ b)
    (hb : b*2^t ≤ n)
    (hD : ∀ j < n, ParabolaDecouplingBound.{u} (2^j) (D j)) :
    ParabolaBilinearSixBound.{u} (1/(2:ℝ)^n) (2^(n-a)) (2^(n-b))
      (1/(2:ℝ)^r) (parabolaDyadicBilinearBudget D n r t a b) := by
  induction t generalizing a b with
  | zero =>
    simp only [pow_zero,mul_one] at hb
    exact parabolaBilinearSixBound_of_linear (by positivity) (by positivity)
      (by positivity) (hD (n-a) (by omega)) (hD (n-b) (by omega))
  | succ t ih =>
    have hpow : (1:ℕ) ≤ 2^t := Nat.succ_le_iff.mpr (by positivity)
    have he : (2*b)*2^t = b*2^(t+1) := by rw [pow_succ]; ring
    have hnext : (2*b)*2^t ≤ n := by rw [he]; exact hb
    have hb₂ : 2*b ≤ n :=
      (show 2*b ≤ (2*b)*2^t by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hpow (Nat.zero_le (2*b))).trans hnext
    have hprev := ih (hra.trans hab) (by omega : b ≤ 2*b) hnext
    have h := hprev.dyadic_step (a:=a) (by omega) hb₂ hra (hD (n-b) (by omega))
    simpa only [parabolaDyadicBilinearBudget] using h

                                                                              
                                                                 
theorem parabolaDecouplingBound_dyadic_iterate (D : ℕ → ℝ)
    {n r t : ℕ} (hr : 0 < r) (hn : r*2^t ≤ n)
    (hD : ∀ j < n, ParabolaDecouplingBound.{u} (2^j) (D j)) :
    ParabolaDecouplingBound.{u} (2^n)
      (14*D (n-r)+2*(2:ℝ)^r*
        (parabolaDyadicBilinearBudget D n r t r r)^((6:ℝ)⁻¹)) := by
  have hpow : (1:ℕ) ≤ 2^t := Nat.succ_le_iff.mpr (by positivity)
  have hrn : r ≤ n :=
    (show r ≤ r*2^t by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hpow (Nat.zero_le r)).trans hn
  exact ParabolaDecouplingBound.of_bilinear_dyadic hrn (hD (n-r) (by omega))
    (parabolaBilinearSixBound_dyadic_iterate D hr le_rfl le_rfl hn hD)

end TaoTrudgianYang2025

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem two_rpow_product (C x y : ℝ) (m k : ℕ) :
    (C*(2:ℝ)^x)^m*(C*(2:ℝ)^y)^k =
      C^(m+k)*(2:ℝ)^(x*m+y*k) := by
  rw [Real.rpow_add (by norm_num), Real.rpow_mul_natCast (by norm_num),
    Real.rpow_mul_natCast (by norm_num), pow_add]
  ring

                                                                         
theorem parabolaDyadicBilinearBudget_exponential {C ε : ℝ} (hC : 0 ≤ C)
    {n r a b t : ℕ} (ht : 1 ≤ t) (hb : b*2^t ≤ n) :
    parabolaDyadicBilinearBudget (fun j => C*(2:ℝ)^(ε*j)) n r t a b ≤
      49*C^6*(2:ℝ)^(6*ε*n-(3*(t:ℝ)+5)*ε*b+2*r) := by
  obtain ⟨s,rfl⟩ := Nat.exists_eq_add_of_le ht
  induction s generalizing a b with
  | zero =>
    have hb₂ : 2*b ≤ n := by simpa [mul_comm] using hb
    have hb₁ : b ≤ n := by omega
    have hx : 0 ≤ C*(2:ℝ)^(ε*((n-b:ℕ):ℝ)) := by positivity
    have hy : 0 ≤ C*(2:ℝ)^(ε*((n-2*b:ℕ):ℝ)) := by positivity
    simp only [Nat.add_zero,parabolaDyadicBilinearBudget]
    rw [show (C*(2:ℝ)^(ε*((n-b:ℕ):ℝ)))^2*
        (C*(2:ℝ)^(ε*((n-2*b:ℕ):ℝ)))^4 =
        ((C*(2:ℝ)^(ε*((n-b:ℕ):ℝ)))*
          (C*(2:ℝ)^(ε*((n-2*b:ℕ):ℝ)))^2)^2 by ring,
      Real.sqrt_sq (by positivity)]
    have hp := two_rpow_product C (ε*((n-b:ℕ):ℝ))
      (ε*((n-2*b:ℕ):ℝ)) 4 2
    simp only [Nat.cast_sub hb₁,Nat.cast_sub hb₂,Nat.cast_mul,Nat.cast_ofNat] at hp ⊢
    have he : (ε*((n:ℝ)-b))*4+(ε*((n:ℝ)-2*b))*2 =
        6*ε*n-8*ε*b := by ring
    norm_num only [show (4+2:ℕ)=6 by omega] at hp
    rw [he] at hp
    have hmain :
        7/(1/(2:ℝ)^r)*
          (C*(2:ℝ)^(ε*((n:ℝ)-b))*
            (C*(2:ℝ)^(ε*((n:ℝ)-2*b)))^2*
              (C*(2:ℝ)^(ε*((n:ℝ)-b)))^3) =
        7*(2:ℝ)^r*(C^6*(2:ℝ)^(6*ε*n-8*ε*b)) := by
      rw [div_div_eq_mul_div,div_one]
      calc
        _ = 7*(2:ℝ)^r*((C*(2:ℝ)^(ε*((n:ℝ)-b)))^4*
          (C*(2:ℝ)^(ε*((n:ℝ)-2*b)))^2) := by ring
        _ = _ := by rw [hp]
    rw [hmain]
    have hrpow : (2:ℝ)^r ≤ (2:ℝ)^(2*(r:ℝ)) := by
      rw [←Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r; linarith)
    have he' : 6*ε*n-(3*(1:ℝ)+5)*ε*b+2*r =
        (6*ε*n-8*ε*b)+2*r := by ring
    simp only [Nat.cast_one]
    rw [he',Real.rpow_add (by norm_num)]
    have hmul := mul_le_mul_of_nonneg_right hrpow
      (show 0 ≤ C^6*(2:ℝ)^(6*ε*n-8*ε*b) by positivity)
    nlinarith [mul_nonneg (show 0 ≤ C^6*(2:ℝ)^(6*ε*n-8*ε*b) by positivity)
      (show 0 ≤ (2:ℝ)^(2*(r:ℝ)) by positivity)]
  | succ s ih =>
    have hp : (1:ℕ) ≤ 2^(1+s) := Nat.succ_le_iff.mpr (by positivity)
    have he : (2*b)*2^(1+s)=b*2^(1+(s+1)) := by
      rw [show 1+(s+1)=(1+s)+1 by omega,pow_succ]; ring
    have hbnext : (2*b)*2^(1+s) ≤ n := by rw [he]; exact hb
    have hb₂ : 2*b ≤ n :=
      (show 2*b ≤ (2*b)*2^(1+s) by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (Nat.zero_le (2*b))).trans hbnext
    have hb₁ : b ≤ n := by omega
    have hprev := ih (a:=b) (by omega) hbnext
    have hsquare :
        (7*C^3*(2:ℝ)^(3*ε*n-(3*((1+s:ℕ):ℝ)+5)*ε*b+r))^2 =
        49*C^6*(2:ℝ)^(6*ε*n-(3*((1+s:ℕ):ℝ)+5)*ε*(2*b)+2*r) := by
      rw [mul_pow,mul_pow,←pow_mul,←Real.rpow_mul_natCast (by norm_num)]
      norm_num only [show (3*2:ℕ)=6 by omega,show (7:ℝ)^2=49 by norm_num,Nat.cast_ofNat]
      congr 1
      congr 1
      ring
    have hsqrt : Real.sqrt
        (parabolaDyadicBilinearBudget (fun j => C*(2:ℝ)^(ε*j)) n r (1+s) b (2*b)) ≤
        7*C^3*(2:ℝ)^(3*ε*n-(3*((1+s:ℕ):ℝ)+5)*ε*b+r) := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity,?_⟩
      rw [hsquare]
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using hprev
    rw [show 1+(s+1)=(1+s)+1 by omega,parabolaDyadicBilinearBudget]
    calc
      _ ≤ (7/(1/(2:ℝ)^r))*
          ((7*C^3*(2:ℝ)^(3*ε*n-(3*((1+s:ℕ):ℝ)+5)*ε*b+r))*
            (C*(2:ℝ)^(ε*((n-b:ℕ):ℝ)))^3) := by
        gcongr
      _ = _ := by
        rw [div_div_eq_mul_div,div_one,mul_pow,←Real.rpow_mul_natCast (by norm_num)]
        rw [←Real.rpow_natCast (2:ℝ) r]
        simp only [Nat.cast_sub hb₁,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
        have he' : 6*ε*n-(3*(1+(s:ℝ)+1)+5)*ε*b+2*r =
            (r:ℝ)+(3*ε*n-(3*(1+s:ℝ)+5)*ε*b+r)+(ε*((n:ℝ)-b))*3 := by ring
        rw [he']
        conv_rhs =>
          rw [Real.rpow_add (by norm_num),Real.rpow_add (by norm_num)]
        ring
end TaoTrudgianYang2025

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

                                                                         
theorem ParabolaDecouplingBound.mono {n : ℕ} {A B : ℝ}
    (hA : ParabolaDecouplingBound.{u} n A) (hAB : A ≤ B) :
    ParabolaDecouplingBound.{u} n B := by
  refine ⟨hA.1.trans hAB,fun ι W hW S z x hx => ?_⟩
  exact (hA.2 ι W hW S z x hx).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA.1 hAB 2)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

private theorem parabola_dyadic_exponential_root {C ε : ℝ} (hC : 0 ≤ C)
    {n r t : ℕ} (ht : 1 ≤ t) (hn : r*2^t ≤ n) :
    (parabolaDyadicBilinearBudget (fun j => C*(2:ℝ)^(ε*j)) n r t r r)^((6:ℝ)⁻¹) ≤
      2*C*(2:ℝ)^(ε*n-((3*(t:ℝ)+5)/6)*ε*r+(r:ℝ)/3) := by
  have hbudget : 0 ≤
      parabolaDyadicBilinearBudget (fun j => C*(2:ℝ)^(ε*j)) n r t r r := by
    cases t <;> simp only [parabolaDyadicBilinearBudget] <;> positivity
  have hmajor := parabolaDyadicBilinearBudget_exponential (ε:=ε) (r:=r) hC (a:=r) ht hn
  have hpower :
      (2*C*(2:ℝ)^(ε*n-((3*(t:ℝ)+5)/6)*ε*r+(r:ℝ)/3))^6 =
        64*C^6*(2:ℝ)^(6*ε*n-(3*(t:ℝ)+5)*ε*r+2*r) := by
    rw [mul_pow,mul_pow,←Real.rpow_mul_natCast (by norm_num)]
    norm_num only [show (2:ℝ)^6=64 by norm_num,Nat.cast_ofNat]
    congr 1
    congr 1
    ring
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity)
    (by norm_num : (6:ℕ) ≠ 0)).mp
  have hroot := Real.rpow_inv_natCast_pow hbudget (by norm_num : (6:ℕ) ≠ 0)
  simp only [Nat.cast_ofNat] at hroot
  rw [hroot,hpower]
  exact hmajor.trans (by gcongr; norm_num)

private theorem parabola_dyadic_exponential_iteration {C ε : ℝ} (hC : 0 ≤ C)
    {n r t : ℕ} (ht : 1 ≤ t) (hn : r*2^t ≤ n)
    (hεt : 8 ≤ (3*(t:ℝ)-1)*ε) :
    14*(C*(2:ℝ)^(ε*((n-r:ℕ):ℝ)))+2*(2:ℝ)^r*
      (parabolaDyadicBilinearBudget (fun j => C*(2:ℝ)^(ε*j)) n r t r r)^((6:ℝ)⁻¹) ≤
        18*C*(2:ℝ)^(ε*((n-r:ℕ):ℝ)) := by
  have hpow : (1:ℕ) ≤ 2^t := Nat.succ_le_iff.mpr (by positivity)
  have hrn : r ≤ n :=
    (show r ≤ r*2^t by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hpow (Nat.zero_le r)).trans hn
  have hroot := parabola_dyadic_exponential_root (ε:=ε) hC ht hn
  have hexp : ε*n-((3*(t:ℝ)+5)/6)*ε*r+(r:ℝ)/3+r ≤ ε*((n:ℝ)-r) := by
    have hmul := mul_le_mul_of_nonneg_right hεt (Nat.cast_nonneg r : (0:ℝ) ≤ r)
    nlinarith
  have hterm : 2*(2:ℝ)^r*
      (2*C*(2:ℝ)^(ε*n-((3*(t:ℝ)+5)/6)*ε*r+(r:ℝ)/3)) ≤
        4*C*(2:ℝ)^(ε*((n-r:ℕ):ℝ)) := by
    rw [Nat.cast_sub hrn]
    calc
      _ = 4*C*(2:ℝ)^(ε*n-((3*(t:ℝ)+5)/6)*ε*r+(r:ℝ)/3+r) := by
        rw [Real.rpow_add (by norm_num)
          (ε*n-((3*(t:ℝ)+5)/6)*ε*r+(r:ℝ)/3) (r:ℝ),
          Real.rpow_natCast]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) (by positivity)
  have h := mul_le_mul_of_nonneg_left hroot (show 0 ≤ 2*(2:ℝ)^r by positivity)
  linarith

end TaoTrudgianYang2025

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

                                                                            
                                                                            
                                               
theorem exists_parabolaDecouplingBound_dyadic {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ n : ℕ,
      ParabolaDecouplingBound.{u} (2^n) (C*(2:ℝ)^(ε*n)) := by
  obtain ⟨s,hs⟩ := exists_nat_gt ((8:ℝ)/ε)
  let t := s+1
  have ht : 1 ≤ t := by omega
  have hεt : 8 ≤ (3*(t:ℝ)-1)*ε := by
    have h := (div_lt_iff₀ hε).mp hs
    dsimp only [t]
    push_cast
    nlinarith
  obtain ⟨r,hr'⟩ := exists_nat_gt ((5:ℝ)/ε)
  have hr0 : (0:ℝ) < r := (div_pos (by norm_num) hε).trans hr'
  have hr : 0 < r := by exact_mod_cast hr0
  have hεr : 5 ≤ ε*r := by
    have h := (div_lt_iff₀ hε).mp hr'
    nlinarith
  have hcontract : (18:ℝ) ≤ (2:ℝ)^(ε*r) := by
    calc
      18 ≤ (2:ℝ)^(5:ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hεr
  let N := r*2^t
  let C : ℝ := (2:ℝ)^N
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : N ≤ n
    · have hactual := parabolaDecouplingBound_dyadic_iterate
        (fun j => C*(2:ℝ)^(ε*j)) hr hn ih
      apply hactual.mono
      have hnum := parabola_dyadic_exponential_iteration hC.le ht hn hεt
      have hpow : (1:ℕ) ≤ 2^t := Nat.succ_le_iff.mpr (by positivity)
      have hrn : r ≤ n :=
        (show r ≤ r*2^t by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hpow (Nat.zero_le r)).trans hn
      have he : ε*(n:ℝ)=ε*((n-r:ℕ):ℝ)+ε*r := by
        rw [Nat.cast_sub hrn]; ring
      calc
        _ ≤ 18*C*(2:ℝ)^(ε*((n-r:ℕ):ℝ)) := hnum
        _ ≤ (2:ℝ)^(ε*r)*C*(2:ℝ)^(ε*((n-r:ℕ):ℝ)) := by
          gcongr
        _ = C*(2:ℝ)^(ε*n) := by
          rw [he,Real.rpow_add (by norm_num) (ε*((n-r:ℕ):ℝ)) (ε*r)]
          ring
    · have hnN : n ≤ N := by omega
      have htrivial : ParabolaDecouplingBound.{u} (2^n) (Real.sqrt ((2:ℝ)^n)) := by
        simpa only [Nat.cast_pow,Nat.cast_ofNat] using parabolaDecouplingBound_trivial.{u} (2^n)
      apply htrivial.mono
      have hpow : (1:ℝ) ≤ (2:ℝ)^n := one_le_pow₀ (by norm_num)
      calc
        Real.sqrt ((2:ℝ)^n) ≤ (2:ℝ)^n := by
          apply Real.sqrt_le_iff.mpr
          exact ⟨by positivity,by nlinarith⟩
        _ ≤ C := pow_le_pow_right₀ (by norm_num) hnN
        _ ≤ C*(2:ℝ)^(ε*n) := by
          have h := Real.one_le_rpow (by norm_num : (1:ℝ) ≤ 2)
            (show 0 ≤ ε*(n:ℝ) by positivity)
          nlinarith
end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

                                                                          
                                                                     
                                                                         
theorem exists_parabolaBox_dyadic_decoupling {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ (n : ℕ) (R r t : ℝ), 0 < R →
      3/(100*R) ≤ (1/(2:ℝ)^n)^2 →
      ∀ (ι : Type u) (S : Fin (2^n) → Finset ι)
        (z : Fin (2^n) → ι → ℂ) (x : Fin (2^n) → ι → ℝ),
        (∀ j, ∀ k ∈ S j, x j k ∈ Icc
          ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) →
        parabolaBoxBilinearMoment (Finset.univ.sigma S) (Finset.univ.sigma S)
          (fun jk => z jk.1 jk.2) (fun jk => z jk.1 jk.2)
          (fun jk => x jk.1 jk.2) (fun jk => x jk.1 jk.2) R r t ≤
          C*(2:ℝ)^(ε*n)*
            (∑ j, (parabolaWeightedSixNorm
              (fun p : ℝ × ℝ => parabolaRapidWeight R r t p.1 p.2)
              (S j) (z j) (x j))^2)^3 := by
  obtain ⟨D,hDpos,hD⟩ := exists_parabolaDecouplingBound_dyadic.{u}
    (ε:=ε/6) (by positivity)
  refine ⟨D^6,by positivity,?_⟩
  intro n R r t hR hwidth ι S z x hx
  let W := fun p : ℝ × ℝ => parabolaRapidWeight R r t p.1 p.2
  have hW : ParabolaWeightBand (1/((2^n:ℕ):ℝ)) W := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using parabolaRapidWeight_band hR hwidth r t
  have hnorm := (hD n).2 ι W hW S z x hx
  have hcube := pow_le_pow_left₀ (sq_nonneg _) hnorm 3
  simp only [mul_pow,←pow_mul] at hcube
  have hcoef : (D*(2:ℝ)^((ε/6)*n))^6 = D^6*(2:ℝ)^(ε*n) := by
    rw [mul_pow,←Real.rpow_mul_natCast (by norm_num)]
    congr 1
    congr 1
    push_cast
    ring
  norm_num only [show (2*3:ℕ)=6 by omega] at hcube
  rw [←mul_pow,hcoef] at hcube
  have hbox := parabolaBox_le_rapid (Finset.univ.sigma S) (Finset.univ.sigma S)
    (fun jk => z jk.1 jk.2) (fun jk => z jk.1 jk.2)
    (fun jk => x jk.1 jk.2) (fun jk => x jk.1 jk.2) hR r t
  have hid := parabolaWeightedSixNorm_pow_six W hW.1 hW.2.1
    (Finset.univ.sigma S) (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2)
  have he : parabolaRapidBilinearMoment
      (Finset.univ.sigma S) (Finset.univ.sigma S)
      (fun jk => z jk.1 jk.2) (fun jk => z jk.1 jk.2)
      (fun jk => x jk.1 jk.2) (fun jk => x jk.1 jk.2) R r t =
      (parabolaWeightedSixNorm W (Finset.univ.sigma S)
        (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2))^6 := by
    simpa only [parabolaRapidBilinearMoment,parabolaWeightedBilinearMoment,W] using hid.symm
  exact hbox.trans (he.le.trans hcube)
end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private theorem parabola_sixNorm_weight_comparison {ι : Type*}
    {V W : ℝ × ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hV₀ : ∀ p, 0 ≤ V p) (hW₀ : ∀ p, 0 ≤ W p)
    (hV : Integrable V) (hW : Integrable W) (hVW : ∀ p, V p ≤ C*W p)
    (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ) :
    (parabolaWeightedSixNorm V S z x)^2 ≤
      C^((3:ℝ)⁻¹)*(parabolaWeightedSixNorm W S z x)^2 := by
  have hm : parabolaWeightedBilinearMoment V S S z z x x ≤
      C*parabolaWeightedBilinearMoment W S S z z x x := by
    have h := integral_mono
      (parabolaMomentFunction_integrable S S z z x x hV)
      ((parabolaMomentFunction_integrable S S z z x x hW).const_mul C)
      (fun p => (mul_le_mul_of_nonneg_right (hVW p)
        (parabolaMomentFunction_nonneg S S z z x x p)).trans_eq (by ring))
    rw [integral_const_mul] at h
    simpa only [parabolaWeightedBilinearMoment,parabolaMomentFunction,mul_assoc] using h
  apply (pow_le_pow_iff_left₀ (sq_nonneg _) (by positivity)
    (by norm_num : (3:ℕ) ≠ 0)).mp
  rw [mul_pow,←pow_mul,←pow_mul]
  have hroot := Real.rpow_inv_natCast_pow hC (by norm_num : (3:ℕ) ≠ 0)
  simp only [Nat.cast_ofNat] at hroot
  rw [hroot]
  norm_num only [show (2*3:ℕ)=6 by omega]
  rw [parabolaWeightedSixNorm_pow_six V hV₀ hV,
    parabolaWeightedSixNorm_pow_six W hW₀ hW]
  exact hm

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

                                                                             
theorem exists_parabolaBox_sourceWeight_decoupling {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ (n : ℕ) (R r t : ℝ), 0 < R →
      3/(100*R) ≤ (1/(2:ℝ)^n)^2 →
      ∀ (ι : Type u) (S : Fin (2^n) → Finset ι)
        (z : Fin (2^n) → ι → ℂ) (x : Fin (2^n) → ι → ℝ),
        (∀ j, ∀ k ∈ S j, x j k ∈ Icc
          ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) →
        parabolaBoxBilinearMoment (Finset.univ.sigma S) (Finset.univ.sigma S)
          (fun jk => z jk.1 jk.2) (fun jk => z jk.1 jk.2)
          (fun jk => x jk.1 jk.2) (fun jk => x jk.1 jk.2) R r t ≤
          C*(2:ℝ)^(ε*n)*
            (∑ j, (parabolaWeightedSixNorm
              (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2)
              (S j) (z j) (x j))^2)^3 := by
  obtain ⟨C,hC,hbox⟩ := exists_parabolaBox_dyadic_decoupling.{u} hε
  obtain ⟨K,hK,hcomp⟩ := parabolaRapidWeight_le_sourceWeight
  refine ⟨C*K,by positivity,?_⟩
  intro n R r t hR hwidth ι S z x hx
  have hm := hbox n R r t hR hwidth ι S z x hx
  have hnorm (j : Fin (2^n)) :=
    parabola_sixNorm_weight_comparison hK.le
      (fun p : ℝ × ℝ => parabolaRapidWeight_nonneg R r t p.1 p.2)
      (fun p : ℝ × ℝ => parabolaSourceWeight_nonneg R r t p.1 p.2)
      (parabolaRapidWeight_band hR hwidth r t).2.1
      (integrable_parabolaSourceWeight hR r t)
      (fun p => hcomp R r t p.1 p.2) (S j) (z j) (x j)
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hnorm j)
  rw [←Finset.mul_sum] at hs
  have hcube := pow_le_pow_left₀
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hs 3
  rw [mul_pow] at hcube
  have hroot := Real.rpow_inv_natCast_pow hK.le (by norm_num : (3:ℕ) ≠ 0)
  simp only [Nat.cast_ofNat] at hroot
  rw [hroot] at hcube
  calc
    _ ≤ _ := hm
    _ ≤ C*(2:ℝ)^(ε*n)*(K*
        (∑ j, (parabolaWeightedSixNorm
          (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2)
          (S j) (z j) (x j))^2)^3) :=
      mul_le_mul_of_nonneg_left hcube (by positivity)
    _ = _ := by ring
end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem parabola_sourceWeight_horizontal_translate {R : ℝ} (hR : 0 < R)
    (r t α γ u : ℝ) :
    parabolaSourceWeight R r t (α-u) γ ≤
      (1+|u|/R)^100*parabolaSourceWeight R r t α γ := by
  have h := parabolaSourceWeight_triangle_lower R r t (α-u) γ α γ
  have he : parabolaSourceWeight R (α-u) γ α γ = 1/(1+|u|/R)^100 := by
    unfold parabolaSourceWeight
    have hx : (α-(α-u))/R=u/R := by ring
    rw [hx,sub_self,zero_div,Complex.ofReal_zero,zero_mul,add_zero,
      Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_pos hR]
  rw [he,mul_one_div] at h
  rw [div_le_iff₀ (by positivity)] at h
  simpa only [mul_comm] using h

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ContDiff
namespace TaoTrudgianYang2025

private def bourgainCubicQuarticCutoff (a b s : ℝ) : ℂ :=
  (modelPhaseBufferedCutoff (-2) 2 (1/2) s : ℂ)*
    fordAdditiveCharacter (a*s^3+b*s^4)

private def bourgainCubicQuarticJoint (p : (ℝ × ℝ) × ℝ) : ℂ :=
  bourgainCubicQuarticCutoff p.1.1 p.1.2 p.2

private theorem bourgainCubicQuarticJoint_smooth :
    ContDiff ℝ ∞ bourgainCubicQuarticJoint := by
  have hc : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ =>
      (modelPhaseBufferedCutoff (-2) 2 (1/2) p.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      ((modelPhaseBufferedCutoff_contDiff (-2) 2 (1/2)).comp contDiff_snd)
  unfold bourgainCubicQuarticJoint bourgainCubicQuarticCutoff fordAdditiveCharacter
  apply hc.mul
  have hp : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => p.1.1*p.2^3+p.1.2*p.2^4) :=
    ((contDiff_fst.fst).mul (contDiff_snd.pow 3)).add
      ((contDiff_fst.snd).mul (contDiff_snd.pow 4))
  exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hp)).cexp

private theorem bourgainCubicQuarticCutoff_smooth (a b : ℝ) :
    ContDiff ℝ ∞ (bourgainCubicQuarticCutoff a b) := by
  have hmap : ContDiff ℝ ∞ (fun s : ℝ => ((a,b),s)) :=
    contDiff_const.prodMk contDiff_id
  simpa only [Function.comp_def,bourgainCubicQuarticJoint] using
    bourgainCubicQuarticJoint_smooth.comp hmap

private theorem bourgainCubicQuarticCutoff_support (a b : ℝ) :
    tsupport (bourgainCubicQuarticCutoff a b) ⊆ Icc (-2:ℝ) 2 := by
  apply closure_minimal _ isClosed_Icc
  intro s hs
  have hk : s ∈ tsupport (modelPhaseBufferedCutoff (-2) 2 (1/2)) := by
    apply subset_closure
    intro hz
    exact hs (by rw [bourgainCubicQuarticCutoff,hz,Complex.ofReal_zero,zero_mul])
  have hb := modelPhaseBufferedCutoff_tsupport (by norm_num : (0:ℝ)<1/2) hk
  constructor <;> linarith [hb.1,hb.2]


private theorem norm_vertical_slice_iteratedFDeriv
    (F : (ℝ × ℝ) × ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (p : ℝ × ℝ) (s : ℝ) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun x => F (p,x)) s‖ ≤
      ‖iteratedFDeriv ℝ j F (p,s)‖ := by
  let L : ℝ →L[ℝ] (ℝ × ℝ) × ℝ := ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ
  have hL : ‖L‖=1 := ContinuousLinearMap.norm_inr ℝ (ℝ × ℝ) ℝ
  have hshift : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => (p,0)+q) :=
    contDiff_const.add contDiff_id
  have hf : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => F ((p,0)+q)) :=
    hF.comp hshift
  have he : (fun x => F (p,x)) = (fun q => F ((p,0)+q)) ∘ L := by
    ext x; simp [L]
  rw [he,L.iteratedFDeriv_comp_right hf s (i:=j)
    (by exact_mod_cast (le_top : (j:ℕ∞)≤⊤)),iteratedFDeriv_comp_add_left]
  have hp : (p,0)+L s = (p,s) := by simp [L]
  rw [hp]
  have h := (iteratedFDeriv ℝ j F (p,s)).norm_compContinuousLinearMap_le
    (fun _ : Fin j => L)
  simpa only [hL,Finset.prod_const_one,mul_one] using h

private theorem bourgainCubicQuarticCutoff_derivative_bound (Q : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a ∈ Icc (-1:ℝ) 1, ∀ b ∈ Icc (-1:ℝ) 1,
      ∀ s : ℝ, ∀ j ≤ Q,
        ‖iteratedFDeriv ℝ j (bourgainCubicQuarticCutoff a b) s‖ ≤ C := by
  let F := bourgainCubicQuarticJoint
  let B := fun p : (ℝ × ℝ) × ℝ =>
    ∑ j ∈ Finset.range (Q+1), ‖iteratedFDeriv ℝ j F p‖
  have hB : Continuous B := continuous_finsetSum _ fun j _ =>
    (bourgainCubicQuarticJoint_smooth.continuous_iteratedFDeriv (m:=j) (by exact_mod_cast (le_top : (j:ℕ∞)≤⊤))).norm
  obtain ⟨M,hM⟩ := ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).exists_bound_of_continuousOn
    (s := (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1) ×ˢ Icc (-2:ℝ) 2) hB.continuousOn
  refine ⟨max M 1,le_max_right _ _,?_⟩
  intro a ha b hb s j hj
  by_cases hs : s ∈ Icc (-2:ℝ) 2
  · have hnorm : ‖iteratedFDeriv ℝ j (bourgainCubicQuarticCutoff a b) s‖ ≤
        ‖iteratedFDeriv ℝ j F ((a,b),s)‖ := by
      simpa only [F,bourgainCubicQuarticJoint] using
        norm_vertical_slice_iteratedFDeriv F bourgainCubicQuarticJoint_smooth (a,b) s j
    have hsum : ‖iteratedFDeriv ℝ j F ((a,b),s)‖ ≤ B ((a,b),s) := by
      dsimp only [B]
      exact Finset.single_le_sum (fun k _ => norm_nonneg (iteratedFDeriv ℝ k F ((a,b),s)))
        (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
    exact hnorm.trans (hsum.trans ((le_abs_self _).trans
      ((hM _ ⟨⟨ha,hb⟩,hs⟩).trans (le_max_left _ _))))
  · have hz : iteratedFDeriv ℝ j (bourgainCubicQuarticCutoff a b) s = 0 := by
      apply Function.notMem_support.mp
      intro h
      exact hs (bourgainCubicQuarticCutoff_support a b
        ((tsupport_iteratedFDeriv_subset j) (subset_closure h)))
    rw [hz,norm_zero]
    exact zero_le_one.trans (le_max_right _ _)

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ContDiff FourierTransform
namespace TaoTrudgianYang2025

private theorem bourgainCubicQuarticCutoff_derivative_integrable (a b : ℝ) (j : ℕ) :
    Integrable (fun s : ℝ => ‖iteratedFDeriv ℝ j (bourgainCubicQuarticCutoff a b) s‖) := by
  have hc : HasCompactSupport (bourgainCubicQuarticCutoff a b) :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (bourgainCubicQuarticCutoff_support a b)
  exact ((bourgainCubicQuarticCutoff_smooth a b).continuous_iteratedFDeriv
    (m:=j) (by exact_mod_cast (le_top : (j:ℕ∞)≤⊤))).norm.integrable_of_hasCompactSupport
      (hc.iteratedFDeriv j).norm

private theorem bourgainCubicQuarticCutoff_derivative_integrals (Q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a ∈ Icc (-1:ℝ) 1, ∀ b ∈ Icc (-1:ℝ) 1,
      ∀ j ≤ Q, (∫ s : ℝ, ‖iteratedFDeriv ℝ j (bourgainCubicQuarticCutoff a b) s‖) ≤ C := by
  obtain ⟨C,hC,h⟩ := bourgainCubicQuarticCutoff_derivative_bound Q
  refine ⟨4*C,by positivity,?_⟩
  intro a ha b hb j hj
  have hz (s : ℝ) (hs : s ∉ Icc (-2:ℝ) 2) :
      ‖iteratedFDeriv ℝ j (bourgainCubicQuarticCutoff a b) s‖ = 0 := by
    have hd : iteratedFDeriv ℝ j (bourgainCubicQuarticCutoff a b) s = 0 :=
      Function.notMem_support.mp (fun hh => hs
        (bourgainCubicQuarticCutoff_support a b ((support_iteratedFDeriv_subset j) hh)))
    rw [hd,norm_zero]
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  have hmain := norm_setIntegral_le_of_norm_le_const
    (μ:=volume) (s:=Icc (-2:ℝ) 2)
    (f:=fun s : ℝ => ‖iteratedFDeriv ℝ j (bourgainCubicQuarticCutoff a b) s‖)
    (by simp)
    (fun s _ => by simpa only [norm_norm] using h a ha b hb s j hj)
  have hnorm := le_abs_self
    (∫ s : ℝ in Icc (-2:ℝ) 2, ‖iteratedFDeriv ℝ j (bourgainCubicQuarticCutoff a b) s‖)
  have hmeasure : volume.real (Icc (-2:ℝ) 2) = 4 := by
    norm_num [Measure.real,Real.volume_Icc]
  rw [hmeasure] at hmain
  simpa only [mul_comm] using hnorm.trans hmain

private theorem bourgainCubicQuarticCutoff_fourier_moment (a b ξ : ℝ) (m : ℕ) :
    |ξ|^m*‖𝓕 (bourgainCubicQuarticCutoff a b) ξ‖ ≤
      (2:ℝ)^m*∑ j ∈ Finset.range (m+1),
        ∫ s : ℝ, ‖iteratedFDeriv ℝ j (bourgainCubicQuarticCutoff a b) s‖ := by
  have hI (k n : ℕ) (hk : (k:ℕ∞) ≤ 0) (_hn : (n:ℕ∞) ≤ ⊤) :
      Integrable (fun s : ℝ => ‖s‖^k*
        ‖iteratedFDeriv ℝ n (bourgainCubicQuarticCutoff a b) s‖) := by
    have hk0 : k=0 := by
      have hk' : k ≤ 0 := by exact_mod_cast hk
      omega
    subst k
    simpa using bourgainCubicQuarticCutoff_derivative_integrable a b n
  have h := Real.pow_mul_norm_iteratedFDeriv_fourier_le
    (K:=0) (N:=(⊤:ℕ∞)) (bourgainCubicQuarticCutoff_smooth a b) hI
    (k:=0) (n:=m) (by simp) (by simp) ξ
  simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, Nat.cast_zero, mul_zero, zero_add,
    pow_zero, one_mul, Finset.range_one, Finset.sum_product, Finset.sum_singleton] using h

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ContDiff FourierTransform
namespace TaoTrudgianYang2025

private theorem bourgainCubicQuarticCutoff_fourier_decay (Q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a ∈ Icc (-1:ℝ) 1, ∀ b ∈ Icc (-1:ℝ) 1,
      ∀ ξ : ℝ, (1+|ξ|)^Q*‖𝓕 (bourgainCubicQuarticCutoff a b) ξ‖ ≤ C := by
  obtain ⟨D,hD,hjet⟩ := bourgainCubicQuarticCutoff_derivative_integrals Q
  let E := (2:ℝ)^Q*((Q+1:ℕ):ℝ)*D
  refine ⟨(2:ℝ)^Q*(D+E),by dsimp [E]; positivity,?_⟩
  intro a ha b hb ξ
  have hz : ‖𝓕 (bourgainCubicQuarticCutoff a b) ξ‖ ≤ D := by
    have h := bourgainCubicQuarticCutoff_fourier_moment a b ξ 0
    simpa using h.trans (by simpa using hjet a ha b hb 0 (Nat.zero_le Q))
  have hp : |ξ|^Q*‖𝓕 (bourgainCubicQuarticCutoff a b) ξ‖ ≤ E := by
    apply (bourgainCubicQuarticCutoff_fourier_moment a b ξ Q).trans
    calc
      _ ≤ (2:ℝ)^Q*∑ _j ∈ Finset.range (Q+1), D := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum (fun j hj => hjet a ha b hb j
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
      _ = E := by simp [E,mul_assoc]
  have hscale : (1+|ξ|)^Q ≤ (2:ℝ)^Q*(1+|ξ|^Q) := by
    by_cases hξ : |ξ| ≤ 1
    · have h := pow_le_pow_left₀ (by positivity : (0:ℝ)≤1+|ξ|)
        (by linarith : 1+|ξ| ≤ 2) Q
      have hnonneg : 0 ≤ (2:ℝ)^Q*|ξ|^Q := by positivity
      nlinarith
    · have hξ' : 1 ≤ |ξ| := le_of_lt (lt_of_not_ge hξ)
      calc
        _ ≤ (2*|ξ|)^Q := pow_le_pow_left₀ (by positivity) (by linarith) Q
        _ = (2:ℝ)^Q*|ξ|^Q := mul_pow _ _ _
        _ ≤ _ := by nlinarith [show (0:ℝ)≤(2:ℝ)^Q by positivity]
  calc
    _ ≤ (2:ℝ)^Q*(1+|ξ|^Q)*‖𝓕 (bourgainCubicQuarticCutoff a b) ξ‖ :=
      mul_le_mul_of_nonneg_right hscale (norm_nonneg _)
    _ = (2:ℝ)^Q*(‖𝓕 (bourgainCubicQuarticCutoff a b) ξ‖+
        |ξ|^Q*‖𝓕 (bourgainCubicQuarticCutoff a b) ξ‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hz hp) (by positivity)

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ContDiff FourierTransform
namespace TaoTrudgianYang2025

private theorem bourgainCubicQuarticCutoff_uniform_fourierL1 :
    ∃ C : ℝ, 0 < C ∧ ∀ a ∈ Icc (-1:ℝ) 1, ∀ b ∈ Icc (-1:ℝ) 1,
      Integrable (fun ξ : ℝ => (1+|ξ|)^100*‖𝓕 (bourgainCubicQuarticCutoff a b) ξ‖) ∧
      (∫ ξ : ℝ, (1+|ξ|)^100*‖𝓕 (bourgainCubicQuarticCutoff a b) ξ‖) ≤ C := by
  obtain ⟨C,hC,hdec⟩ := bourgainCubicQuarticCutoff_fourier_decay 102
  refine ⟨C*Real.pi,by positivity,?_⟩
  intro a ha b hb
  let f := bourgainCubicQuarticCutoff a b
  have hdom (ξ : ℝ) :
      (1+|ξ|)^100*‖𝓕 f ξ‖ ≤ C*(1+ξ^2)⁻¹ := by
    have hs : 1+ξ^2 ≤ (1+|ξ|)^2 := by
      nlinarith [sq_abs ξ,abs_nonneg ξ]
    have hp : (1+ξ^2)*((1+|ξ|)^100*‖𝓕 f ξ‖) ≤ C := by
      calc
        _ ≤ (1+|ξ|)^2*((1+|ξ|)^100*‖𝓕 f ξ‖) :=
          mul_le_mul_of_nonneg_right hs (by positivity)
        _ = (1+|ξ|)^102*‖𝓕 f ξ‖ := by
          rw [show (102:ℕ)=2+100 by omega,pow_add]
          exact (mul_assoc _ _ _).symm
        _ ≤ C := hdec a ha b hb ξ
    rw [←div_eq_mul_inv,le_div_iff₀ (by positivity)]
    simpa only [mul_comm] using hp
  have hc : HasCompactSupport f :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (bourgainCubicQuarticCutoff_support a b)
  have hi : Integrable f :=
    (bourgainCubicQuarticCutoff_smooth a b).continuous.integrable_of_hasCompactSupport hc
  have hhat : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hi
  have hcont : Continuous (fun ξ : ℝ => (1+|ξ|)^100*‖𝓕 f ξ‖) :=
    ((continuous_const.add continuous_abs).pow 100).mul hhat.norm
  have hint : Integrable (fun ξ : ℝ => (1+|ξ|)^100*‖𝓕 f ξ‖) :=
    (integrable_inv_one_add_sq.const_mul C).mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤
          (1+|ξ|)^100*‖𝓕 f ξ‖ by positivity)] using hdom ξ))
  refine ⟨hint,?_⟩
  have hmain := integral_mono hint (integrable_inv_one_add_sq.const_mul C) hdom
  rw [integral_const_mul,integral_univ_inv_one_add_sq] at hmain
  exact hmain

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ContDiff FourierTransform
namespace TaoTrudgianYang2025

                                                                       
                                                                                
theorem exists_bourgainCubicQuartic_multiplier_kernel :
    ∃ C : ℝ, 0 < C ∧ ∀ a ∈ Icc (-1:ℝ) 1, ∀ b ∈ Icc (-1:ℝ) 1,
      ∃ K : ℝ → ℂ,
        Continuous K ∧ Integrable (fun ξ => (1+|ξ|)^100*‖K ξ‖) ∧
        (∫ ξ : ℝ, (1+|ξ|)^100*‖K ξ‖) ≤ C ∧
        (∀ ξ : ℝ, ‖K ξ‖ ≤ C/(1+|ξ|)^102) ∧
        ∀ s ∈ Icc (-1:ℝ) 1,
          fordAdditiveCharacter (a*s^3+b*s^4) =
            ∫ ξ : ℝ, K ξ*fordAdditiveCharacter (ξ*s) := by
  obtain ⟨C,hC,h⟩ := bourgainCubicQuarticCutoff_uniform_fourierL1
  obtain ⟨D,hD,hdec⟩ := bourgainCubicQuarticCutoff_fourier_decay 102
  refine ⟨max C D,hC.trans_le (le_max_left _ _),?_⟩
  intro a ha b hb
  let f := bourgainCubicQuarticCutoff a b
  let K : ℝ → ℂ := 𝓕 f
  have hkernel := h a ha b hb
  have hc : HasCompactSupport f :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (bourgainCubicQuarticCutoff_support a b)
  have hi : Integrable f :=
    (bourgainCubicQuarticCutoff_smooth a b).continuous.integrable_of_hasCompactSupport hc
  have hhat : Continuous K :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hi
  have hKi : Integrable K :=
    hkernel.1.mono' hhat.aestronglyMeasurable (Filter.Eventually.of_forall (fun ξ => by
      have hp : (1:ℝ) ≤ (1+|ξ|)^100 := one_le_pow₀ (by linarith [abs_nonneg ξ])
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (norm_nonneg (K ξ))))
  refine ⟨K,hhat,hkernel.1,hkernel.2.trans (le_max_left _ _),?_,?_⟩
  · intro ξ
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using (hdec a ha b hb ξ).trans (le_max_right C D)
  intro s hs
  have hcut : f s = fordAdditiveCharacter (a*s^3+b*s^4) := by
    dsimp only [f,bourgainCubicQuarticCutoff]
    rw [modelPhaseBufferedCutoff_one (by norm_num)
      (by linarith [hs.1]) (by linarith [hs.2]),Complex.ofReal_one,one_mul]
  have hinv := congrFun
    ((bourgainCubicQuarticCutoff_smooth a b).continuous.fourierInv_fourier_eq hi hKi) s
  rw [Real.fourierInv_eq_fourier_neg,Real.fourier_real_eq_integral_exp_smul] at hinv
  calc
    _ = f s := hcut.symm
    _ = _ := hinv.symm
    _ = ∫ ξ : ℝ, K ξ*fordAdditiveCharacter (ξ*s) := by
      apply integral_congr_ae
      filter_upwards with ξ
      simp only [smul_eq_mul,fordAdditiveCharacter]
      have he : (↑(-2*Real.pi*ξ*(-s)) : ℂ)*Complex.I =
          2*(Real.pi:ℂ)*Complex.I*↑(ξ*s) := by push_cast; ring
      rw [he]
      exact mul_comm _ _
end TaoTrudgianYang2025


noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace TaoTrudgianYang2025

public  theorem weighted_integral_sixth_power
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {W f : α → ℝ}
    (hW : ∀ x, 0 ≤ W x)
    (hI : ∀ j ≤ 6, Integrable (fun x => W x*(f x)^j) μ) :
    (∫ x, W x*f x ∂μ)^6 ≤
      (∫ x, W x ∂μ)^5*(∫ x, W x*(f x)^6 ∂μ) := by
  let I := fun j : ℕ => ∫ x, W x*(f x)^j ∂μ
  have h0 : 0 ≤ I 0 := integral_nonneg (fun x => by simp [hW x])
  have h2 : 0 ≤ I 2 := integral_nonneg (fun x => mul_nonneg (hW x) (by positivity))
  have h6 : 0 ≤ I 6 := integral_nonneg (fun x => mul_nonneg (hW x) (by positivity))
  have h01 : (I 1)^2 ≤ I 0*I 2 := by
    simpa only [I,pow_zero,pow_one,one_pow,mul_one,one_mul] using
      (weighted_integral_cauchy_square (W:=W) (P:=fun _ => 1) (Q:=f) hW
        (by simpa using hI 0 (by omega))
        (by simpa using hI 1 (by omega))
        (hI 2 (by omega)))
  have h02 : (I 2)^2 ≤ I 0*I 4 := by
    have h := weighted_integral_cauchy_square (W:=W) (P:=fun _ => 1)
      (Q:=fun x => (f x)^2) hW
      (by simpa using hI 0 (by omega))
      (by simpa using hI 2 (by omega))
      (by simpa only [←pow_mul] using hI 4 (by omega))
    simpa only [I,pow_zero,one_pow,mul_one,one_mul,←pow_mul] using h
  have h24 : (I 4)^2 ≤ I 2*I 6 := by
    have hcross : Integrable (fun x => W x*f x*(f x)^3) μ := by
      convert hI 4 (by omega) using 1
      ext x
      ring
    have h := weighted_integral_cauchy_square (W:=W) (P:=f)
      (Q:=fun x => (f x)^3) hW (hI 2 (by omega)) hcross
      (by simpa only [←pow_mul] using hI 6 (by omega))
    have he (x : α) : W x*f x*(f x)^3 = W x*(f x)^4 := by ring
    simpa only [I,he,←pow_mul] using h
  have hcube : (I 2)^3 ≤ (I 0)^2*I 6 := by
    by_cases hz : I 2=0
    · simpa only [hz,zero_pow (by norm_num : (3:ℕ) ≠ 0)] using
        mul_nonneg (sq_nonneg (I 0)) h6
    have hpos : 0 < I 2 := lt_of_le_of_ne h2 (Ne.symm hz)
    have hs := pow_le_pow_left₀ (sq_nonneg (I 2)) h02 2
    have hs' : (I 2)^4 ≤ (I 0)^2*(I 4)^2 := by
      convert hs using 1 <;> ring
    have hprod := hs'.trans
      (mul_le_mul_of_nonneg_left h24 (sq_nonneg (I 0)))
    by_contra! hbad
    have hp := mul_pos hpos (sub_pos.mpr hbad)
    nlinarith only [hprod,hp]
  have hmain : (I 1)^6 ≤ (I 0)^5*I 6 := by
    calc
      _ = ((I 1)^2)^3 := by ring
      _ ≤ (I 0*I 2)^3 := pow_le_pow_left₀ (sq_nonneg (I 1)) h01 3
      _ = (I 0)^3*(I 2)^3 := mul_pow _ _ _
      _ ≤ (I 0)^3*((I 0)^2*I 6) :=
        mul_le_mul_of_nonneg_left hcube (pow_nonneg h0 3)
      _ = _ := by ring
  simpa only [I,pow_zero,pow_one,mul_one] using hmain

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

public  theorem bourgainRemainderEnvelope_integrable :
    Integrable (fun ξ : ℝ => ((1+|ξ|)^102)⁻¹) := by
  have hc : Continuous (fun ξ : ℝ => ((1+|ξ|)^102)⁻¹) :=
    (show Continuous (fun ξ : ℝ => (1+|ξ|)^102) from
      (continuous_const.add continuous_abs).pow 102).inv₀
      (fun ξ => ne_of_gt (by positivity : (0:ℝ) < (1+|ξ|)^102))
  apply integrable_inv_one_add_sq.mono' hc.aestronglyMeasurable
  filter_upwards with ξ
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hs : 1+ξ^2 ≤ (1+|ξ|)^2 := by nlinarith [sq_abs ξ,abs_nonneg ξ]
  exact inv_anti₀ (by positivity) (hs.trans
    (pow_le_pow_right₀ (by linarith [abs_nonneg ξ]) (by omega : (2:ℕ) ≤ 102)))

                                                                   
                                                                            
                                                  
theorem bourgain_finite_multiplier_moment {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ)
    {K : ℝ → ℂ} (hKc : Continuous K)
    (hKi : Integrable (fun ξ => (1+|ξ|)^100*‖K ξ‖))
    {C : ℝ} (hC : 0 < C)
    (hmass : (∫ ξ : ℝ, (1+|ξ|)^100*‖K ξ‖) ≤ C)
    (henv : ∀ ξ : ℝ, ‖K ξ‖ ≤ C/(1+|ξ|)^102) :
    ‖∫ ξ : ℝ, K ξ*(∑ i ∈ S, z i*fordAdditiveCharacter (ξ*s i))‖^6 ≤
      C^6*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
        ‖∑ i ∈ S, z i*fordAdditiveCharacter (ξ*s i)‖^6) := by
  let F := fun ξ : ℝ => ∑ i ∈ S, z i*fordAdditiveCharacter (ξ*s i)
  let M := ∑ i ∈ S, ‖z i‖
  have hM : 0 ≤ M := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hFc : Continuous F := by
    unfold F fordAdditiveCharacter
    fun_prop
  have hFb (ξ : ℝ) : ‖F ξ‖ ≤ M := by
    calc
      _ ≤ ∑ i ∈ S, ‖z i*fordAdditiveCharacter (ξ*s i)‖ := norm_sum_le _ _
      _ = M := by simp only [M,norm_mul,sargos_character_norm,mul_one]
  have hweight (ξ : ℝ) : ‖K ξ‖ ≤ (1+|ξ|)^100*‖K ξ‖ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (one_le_pow₀ (by linarith [abs_nonneg ξ]) : (1:ℝ) ≤ (1+|ξ|)^100)
      (norm_nonneg (K ξ))
  have hK : Integrable K :=
    hKi.mono' hKc.aestronglyMeasurable (Filter.Eventually.of_forall hweight)
  have hJ (j : ℕ) : Integrable (fun ξ => ‖K ξ‖*‖F ξ‖^j) :=
    hK.norm.mul_bdd (hFc.norm.pow j).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => by
        rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hFb ξ) j))
  have hV : Integrable (fun ξ => ((1+|ξ|)^102)⁻¹*‖F ξ‖^6) :=
    bourgainRemainderEnvelope_integrable.mul_bdd (hFc.norm.pow 6).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => by
        rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hFb ξ) 6))
  have hmass' : (∫ ξ : ℝ, ‖K ξ‖) ≤ C :=
    (integral_mono hK.norm hKi hweight).trans hmass
  have hm0 : 0 ≤ ∫ ξ : ℝ, ‖K ξ‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hJ0 : 0 ≤ ∫ ξ : ℝ, ‖K ξ‖*‖F ξ‖^6 :=
    integral_nonneg (fun _ => mul_nonneg (norm_nonneg _) (by positivity))
  have hpow := weighted_integral_sixth_power (W:=fun ξ => ‖K ξ‖)
    (f:=fun ξ => ‖F ξ‖) (fun _ => norm_nonneg _) (fun j _ => hJ j)
  have hmajor : (∫ ξ : ℝ, ‖K ξ‖*‖F ξ‖^6) ≤
      C*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*‖F ξ‖^6) := by
    rw [←integral_const_mul]
    apply integral_mono (hJ 6) (hV.const_mul C)
    intro ξ
    simpa only [div_eq_mul_inv,mul_assoc] using
      mul_le_mul_of_nonneg_right (henv ξ) (pow_nonneg (norm_nonneg _) 6)
  calc
    _ ≤ (∫ ξ : ℝ, ‖K ξ‖*‖F ξ‖)^6 := by
      apply pow_le_pow_left₀ (norm_nonneg _) _ 6
      simpa only [norm_mul] using norm_integral_le_integral_norm (fun ξ => K ξ*F ξ)
    _ ≤ (∫ ξ : ℝ, ‖K ξ‖)^5*(∫ ξ : ℝ, ‖K ξ‖*‖F ξ‖^6) := hpow
    _ ≤ C^5*(∫ ξ : ℝ, ‖K ξ‖*‖F ξ‖^6) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hm0 hmass' 5) hJ0
    _ ≤ C^5*(C*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*‖F ξ‖^6)) :=
      mul_le_mul_of_nonneg_left hmajor (pow_nonneg hC.le 5)
    _ = _ := by ring

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

                                                                       
                                                                                   
theorem exists_bourgainCubicQuartic_finite_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ a ∈ Icc (-1:ℝ) 1, ∀ b ∈ Icc (-1:ℝ) 1,
      ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ),
        (∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1) →
        ‖∑ i ∈ S, z i*fordAdditiveCharacter (a*(s i)^3+b*(s i)^4)‖^6 ≤
          C*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
            ‖∑ i ∈ S, z i*fordAdditiveCharacter (ξ*s i)‖^6) := by
  obtain ⟨C,hC,hkern⟩ := exists_bourgainCubicQuartic_multiplier_kernel
  refine ⟨C^6,by positivity,?_⟩
  intro a ha b hb ι S z s hs
  obtain ⟨K,hKc,hKi,hmass,henv,hrep⟩ := hkern a ha b hb
  have hK : Integrable K :=
    hKi.mono' hKc.aestronglyMeasurable (Filter.Eventually.of_forall (fun ξ => by
      have hp : (1:ℝ) ≤ (1+|ξ|)^100 := one_le_pow₀ (by linarith [abs_nonneg ξ])
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (norm_nonneg (K ξ))))
  have hterm (i : ι) :
      Integrable (fun ξ : ℝ => z i*(K ξ*fordAdditiveCharacter (ξ*s i))) := by
    have hc : Continuous (fun ξ : ℝ => fordAdditiveCharacter (ξ*s i)) := by
      unfold fordAdditiveCharacter
      fun_prop
    exact (hK.mul_bdd hc.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => (sargos_character_norm (ξ*s i)).le))).const_mul _
  have he : (∑ i ∈ S, z i*fordAdditiveCharacter (a*(s i)^3+b*(s i)^4)) =
      ∫ ξ : ℝ, K ξ*(∑ i ∈ S, z i*fordAdditiveCharacter (ξ*s i)) := by
    calc
      _ = ∑ i ∈ S, z i*(∫ ξ : ℝ, K ξ*fordAdditiveCharacter (ξ*s i)) :=
        Finset.sum_congr rfl (fun i hi => congrArg (fun v => z i*v) (hrep (s i) (hs i hi)))
      _ = ∑ i ∈ S, ∫ ξ : ℝ, z i*(K ξ*fordAdditiveCharacter (ξ*s i)) := by
        simp only [integral_const_mul]
      _ = ∫ ξ : ℝ, ∑ i ∈ S, z i*(K ξ*fordAdditiveCharacter (ξ*s i)) :=
        (integral_finsetSum S (fun i _ => hterm i)).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with ξ
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  rw [he]
  exact bourgain_finite_multiplier_moment S z s hKc hKi hC hmass henv

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025


private theorem parabola_sum_modulation {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ) (ξ α γ : ℝ) :
    sargosPlanarSum S (fun i => z i*fordAdditiveCharacter (ξ*x i))
      x (fun i => (x i)^2) α γ =
    sargosPlanarSum S z x (fun i => (x i)^2) (α+ξ) γ := by
  unfold sargosPlanarSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc,←fordAdditiveCharacter_add]
  congr 2
  ring

private theorem parabola_sourceWeight_modulation {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ)
    {R : ℝ} (hR : 0 < R) (r t ξ : ℝ) :
    (parabolaWeightedSixNorm
      (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2)
      S (fun i => z i*fordAdditiveCharacter (ξ*x i)) x)^2 ≤
      ((1+|ξ|/R)^100)^((3:ℝ)⁻¹)*
        (parabolaWeightedSixNorm
          (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2) S z x)^2 := by
  let W := fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2
  let V := fun p : ℝ × ℝ => parabolaSourceWeight R r t (p.1-ξ) p.2
  have hW : Integrable W := integrable_parabolaSourceWeight hR r t
  have hV : Integrable V := by
    simpa only [V,W,Prod.fst_add,Prod.snd_add,add_zero,sub_eq_add_neg] using
      hW.comp_add_right (-ξ,0)
  have he := parabola_sum_modulation S z x ξ
  have hm :
      parabolaWeightedBilinearMoment W S S
        (fun i => z i*fordAdditiveCharacter (ξ*x i))
        (fun i => z i*fordAdditiveCharacter (ξ*x i)) x x =
      parabolaWeightedBilinearMoment V S S z z x x := by
    let F := fun p : ℝ × ℝ => V p*
      ‖sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2‖^2*
      ‖sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2‖^4
    calc
      _ = ∫ p : ℝ × ℝ, F (p+(ξ,0)) := by
        unfold parabolaWeightedBilinearMoment
        apply integral_congr_ae
        filter_upwards with p
        simp only [F,V,W,Prod.fst_add,Prod.snd_add,add_zero,add_sub_cancel_right,he]
      _ = ∫ p : ℝ × ℝ, F p := integral_add_right_eq_self F (ξ,0)
      _ = _ := rfl
  have hn :
      parabolaWeightedSixNorm W S (fun i => z i*fordAdditiveCharacter (ξ*x i)) x =
      parabolaWeightedSixNorm V S z x := by
    apply (pow_left_inj₀ (parabolaWeightedSixNorm_nonneg _ _ _ _)
      (parabolaWeightedSixNorm_nonneg _ _ _ _) (by norm_num : (6:ℕ) ≠ 0)).mp
    rw [parabolaWeightedSixNorm_pow_six W
      (fun p => parabolaSourceWeight_nonneg _ _ _ _ _) hW,
      parabolaWeightedSixNorm_pow_six V
      (fun p => parabolaSourceWeight_nonneg _ _ _ _ _) hV]
    exact hm
  change (parabolaWeightedSixNorm W S _ x)^2 ≤ _
  rw [hn]
  exact parabola_sixNorm_weight_comparison (by positivity)
    (fun p => parabolaSourceWeight_nonneg _ _ _ _ _)
    (fun p => parabolaSourceWeight_nonneg _ _ _ _ _) hV hW
    (fun p => parabola_sourceWeight_horizontal_translate hR r t p.1 p.2 ξ) S z x

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

end TaoTrudgianYang2025
noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u
private theorem bourgain_modulation_envelope {R : ℝ} (hR : 1 ≤ R) (ξ : ℝ) :
    ((1+|ξ|)^102)⁻¹*(1+|ξ|/R)^100 ≤ (1+ξ^2)⁻¹ := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hdiv : |ξ|/R ≤ |ξ| := (div_le_self (abs_nonneg ξ) hR)
  have hloss : (1+|ξ|/R)^100 ≤ (1+|ξ|)^100 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 100
  have he : ((1+|ξ|)^102)⁻¹*(1+|ξ|)^100 = ((1+|ξ|)^2)⁻¹ := by
    rw [show (102:ℕ)=2+100 by omega,pow_add,mul_inv_rev]
    calc
      _ = ((1+|ξ|)^2)⁻¹*(((1+|ξ|)^100)⁻¹*(1+|ξ|)^100) := by ring
      _ = _ := by rw [inv_mul_cancel₀ (by positivity),mul_one]
  calc
    _ ≤ ((1+|ξ|)^102)⁻¹*(1+|ξ|)^100 :=
      mul_le_mul_of_nonneg_left hloss (by positivity)
    _ = ((1+|ξ|)^2)⁻¹ := he
    _ ≤ (1+ξ^2)⁻¹ := inv_anti₀ (by positivity)
      (by nlinarith [sq_abs ξ,abs_nonneg ξ])

                                                                         
                                                                        
end TaoTrudgianYang2025
noncomputable section
open MeasureTheory
open scoped Matrix
namespace TaoTrudgianYang2025
private def bourgainQuadraticFrame (a b : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,2*a,3*a^2,4*a^3;
     0,1,3*a,6*a^2;
     1,2*b,3*b^2,4*b^3;
     0,1,3*b,6*b^2]

private theorem bourgainQuadraticFrame_det (a b : ℝ) : (bourgainQuadraticFrame a b).det = 6*(b-a)^4 := by
  unfold bourgainQuadraticFrame
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ,Matrix.det_fin_three,Matrix.submatrix,
    show (1:Fin 4).succAbove (2:Fin 3)=3 by decide,
    show (2:Fin 4).succAbove (2:Fin 3)=3 by decide,
    show (3:Fin 4).succAbove (2:Fin 3)=2 by decide]
  ring

private theorem bourgainQuadraticFrame_map_volume {a b : ℝ} (hab : a ≠ b) :
    Measure.map ((bourgainQuadraticFrame a b).mulVec)
      (volume : Measure (Fin 4 → ℝ)) =
      ENNReal.ofReal ((6*(b-a)^4)⁻¹) • volume := by
  have hn : b-a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hp : 0 < 6*(b-a)^4 := by
    have h := sq_pos_of_ne_zero (pow_ne_zero 2 hn)
    nlinarith
  have hdet : (bourgainQuadraticFrame a b).det ≠ 0 := by
    rw [bourgainQuadraticFrame_det]
    exact hp.ne'
  have hm := Real.map_matrix_volume_pi_eq_smul_volume_pi hdet
  change Measure.map (bourgainQuadraticFrame a b).mulVec volume = _ at hm
  simpa only [bourgainQuadraticFrame_det,
    abs_of_pos (inv_pos.mpr hp)] using hm

private theorem bourgainQuadraticFrame_integral {a b : ℝ} (hab : a ≠ b)
    (f : (Fin 4 → ℝ) → ℝ) (hf : StronglyMeasurable f) :
    (∫ x : Fin 4 → ℝ, f ((bourgainQuadraticFrame a b).mulVec x)) =
      (6*(b-a)^4)⁻¹*(∫ y : Fin 4 → ℝ, f y) := by
  have hc : Continuous ((bourgainQuadraticFrame a b).mulVec) := by
    change Continuous (Matrix.toLin' (bourgainQuadraticFrame a b))
    exact LinearMap.continuous_on_pi _
  have hi := integral_map (μ:=volume) hc.aemeasurable hf.aestronglyMeasurable
  rw [bourgainQuadraticFrame_map_volume hab,integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity),smul_eq_mul] at hi
  exact hi.symm

end TaoTrudgianYang2025



noncomputable section
open MeasureTheory Set
namespace TaoTrudgianYang2025

private def bourgainFourCoordinates :
    (Fin 4 → ℝ) ≃ᵐ (ℝ × ℝ) × (ℝ × ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => ℝ)
    (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)).symm.trans
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => ℝ)).trans
        (MeasurableEquiv.prodCongr MeasurableEquiv.finTwoArrow MeasurableEquiv.finTwoArrow))

private theorem bourgainFourCoordinates_apply (x : Fin 4 → ℝ) :
    bourgainFourCoordinates x = ((x 0,x 1),(x 2,x 3)) := rfl

private theorem bourgainFourCoordinates_measurePreserving :
    MeasurePreserving bourgainFourCoordinates volume volume := by
  exact ((volume_preserving_finTwoArrow ℝ).prod (volume_preserving_finTwoArrow ℝ)).comp
    ((volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => ℝ)).comp
      (volume_measurePreserving_piCongrLeft (fun _ : Fin 4 => ℝ)
        (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)).symm)

private theorem bourgainFourCoordinates_integral_product
    (f g : ℝ × ℝ → ℝ) :
    (∫ y : Fin 4 → ℝ, f (y 0,y 1)*g (y 2,y 3)) =
      (∫ p : ℝ × ℝ, f p)*(∫ q : ℝ × ℝ, g q) := by
  have h := bourgainFourCoordinates_measurePreserving.integral_comp
    bourgainFourCoordinates.measurableEmbedding
    (fun p : (ℝ × ℝ) × (ℝ × ℝ) => f p.1*g p.2)
  calc
    _ = ∫ p : (ℝ × ℝ) × (ℝ × ℝ), f p.1*g p.2 := by
      simpa only [bourgainFourCoordinates_apply] using h
    _ = _ := integral_prod_mul f g

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025

private theorem bourgainQuadraticFrame_cube_bound {a b R : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hR : 0 ≤ R)
    (x : Fin 4 → ℝ) (hx : ∀ j, |x j| ≤ R) :
    ∀ i, |(bourgainQuadraticFrame a b).mulVec x i| ≤ 10*R := by
  have ha2 : |a|^2 ≤ 1 := pow_le_one₀ (abs_nonneg _) ha
  have ha3 : |a|^3 ≤ 1 := pow_le_one₀ (abs_nonneg _) ha
  have hb2 : |b|^2 ≤ 1 := pow_le_one₀ (abs_nonneg _) hb
  have hb3 : |b|^3 ≤ 1 := pow_le_one₀ (abs_nonneg _) hb
  have hrow (i : Fin 4) : (∑ j, |bourgainQuadraticFrame a b i j|) ≤ 10 := by
    fin_cases i <;>
      norm_num [bourgainQuadraticFrame,Fin.sum_univ_succ,abs_mul,abs_pow] <;>
      nlinarith [sq_abs a,sq_abs b]
  intro i
  calc
    _ ≤ ∑ j, |bourgainQuadraticFrame a b i j*x j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |bourgainQuadraticFrame a b i j| *|x j| := by simp only [abs_mul]
    _ ≤ ∑ j, |bourgainQuadraticFrame a b i j| *R :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hx j) (abs_nonneg _))
    _ = (∑ j, |bourgainQuadraticFrame a b i j|)*R := (Finset.sum_mul _ _ _).symm
    _ ≤ 10*R := mul_le_mul_of_nonneg_right (hrow i) hR

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025

private theorem bourgainQuadraticFrame_box_product
    {a b R : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hab : a ≠ b) (hR : 0 ≤ R)
    (f g : ℝ × ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ p, 0 ≤ f p) (hg0 : ∀ p, 0 ≤ g p) :
    (∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
      f ((bourgainQuadraticFrame a b).mulVec x 0,
        (bourgainQuadraticFrame a b).mulVec x 1)*
      g ((bourgainQuadraticFrame a b).mulVec x 2,
        (bourgainQuadraticFrame a b).mulVec x 3)) ≤
      (6*(b-a)^4)⁻¹*
        (∫ p : ℝ × ℝ in Icc (-10*R) (10*R) ×ˢ Icc (-10*R) (10*R), f p)*
        (∫ q : ℝ × ℝ in Icc (-10*R) (10*R) ×ˢ Icc (-10*R) (10*R), g q) := by
  let B := Icc (-10*R) (10*R) ×ˢ Icc (-10*R) (10*R)
  let C := Icc (fun _ : Fin 4 => -R) (fun _ : Fin 4 => R)
  let F := (bourgainQuadraticFrame a b).mulVec
  let G := fun y : Fin 4 → ℝ => B.indicator f (y 0,y 1)*B.indicator g (y 2,y 3)
  have hB : MeasurableSet B := measurableSet_Icc.prod measurableSet_Icc
  have hBcompact : IsCompact B := isCompact_Icc.prod isCompact_Icc
  have hi1 : Integrable (B.indicator f) :=
    (hf.continuousOn.integrableOn_compact hBcompact).integrable_indicator hB
  have hi2 : Integrable (B.indicator g) :=
    (hg.continuousOn.integrableOn_compact hBcompact).integrable_indicator hB
  have hGm : StronglyMeasurable G := by
    apply Measurable.stronglyMeasurable
    exact ((hf.measurable.indicator hB).comp (by fun_prop)).mul
      ((hg.measurable.indicator hB).comp (by fun_prop))
  have hiG : Integrable G := by
    have h := bourgainFourCoordinates_measurePreserving.integrable_comp_of_integrable
      (hi1.mul_prod hi2)
    simpa only [G,Function.comp_def,bourgainFourCoordinates_apply] using h
  have hFc : Continuous F := by
    change Continuous (Matrix.toLin' (bourgainQuadraticFrame a b))
    exact LinearMap.continuous_on_pi _
  have hiGF : Integrable (fun x : Fin 4 → ℝ => G (F x)) := by
    have h : Integrable G (Measure.map F volume) := by
      rw [bourgainQuadraticFrame_map_volume hab]
      exact hiG.smul_measure ENNReal.ofReal_ne_top
    exact h.comp_measurable hFc.measurable
  have hG0 (y : Fin 4 → ℝ) : 0 ≤ G y := by
    apply mul_nonneg
    · exact Set.indicator_nonneg (fun p _ => hf0 p) _
    · exact Set.indicator_nonneg (fun p _ => hg0 p) _
  have he (x : Fin 4 → ℝ) (hx : x ∈ C) :
      f (F x 0,F x 1)*g (F x 2,F x 3) = G (F x) := by
    have hbound := bourgainQuadraticFrame_cube_bound ha hb hR x
      (fun j => abs_le.mpr ⟨hx.1 j,hx.2 j⟩)
    have hmem (i j : Fin 4) : (F x i,F x j) ∈ B := by
      exact ⟨⟨by linarith [(abs_le.mp (hbound i)).1],
        (abs_le.mp (hbound i)).2⟩,
        ⟨by linarith [(abs_le.mp (hbound j)).1],
        (abs_le.mp (hbound j)).2⟩⟩
    simp only [G,Set.indicator_of_mem (hmem 0 1),Set.indicator_of_mem (hmem 2 3)]
  calc
    _ = ∫ x : Fin 4 → ℝ in C, G (F x) :=
      setIntegral_congr_fun measurableSet_Icc he
    _ ≤ ∫ x : Fin 4 → ℝ, G (F x) :=
      setIntegral_le_integral hiGF (Filter.Eventually.of_forall (fun x => hG0 (F x)))
    _ = (6*(b-a)^4)⁻¹*(∫ y : Fin 4 → ℝ, G y) :=
      bourgainQuadraticFrame_integral hab G hGm
    _ = (6*(b-a)^4)⁻¹*((∫ p : ℝ × ℝ, B.indicator f p)*
        (∫ q : ℝ × ℝ, B.indicator g q)) := by
      rw [show (∫ y : Fin 4 → ℝ, G y) =
        (∫ p : ℝ × ℝ, B.indicator f p)*(∫ q : ℝ × ℝ, B.indicator g q) from
        bourgainFourCoordinates_integral_product (B.indicator f) (B.indicator g)]
    _ = _ := by rw [integral_indicator hB,integral_indicator hB]; ring

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025

private theorem bourgainQuartic_remainder_bounds
    {c σ R : ℝ} (hc : |c| ≤ 1) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hR : 0 ≤ R) (hsmall : 5*R*σ^3 ≤ 1)
    (x : Fin 4 → ℝ) (hx : ∀ j, |x j| ≤ R) :
    |(x 2+4*c*x 3)*σ^3| ≤ 1 ∧ |x 3*σ^4| ≤ 1 := by
  have hcprod : |c| *|x 3| ≤ R :=
    (mul_le_mul hc (hx 3) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hs : |x 2+4*c*x 3| ≤ 5*R := by
    have h := abs_add_le (x 2) (4*c*x 3)
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4)] at h
    nlinarith [hx 2]
  constructor
  · rw [abs_mul,abs_of_nonneg (pow_nonneg hσ 3)]
    exact (mul_le_mul_of_nonneg_right hs (pow_nonneg hσ 3)).trans hsmall
  · rw [abs_mul,abs_of_nonneg (pow_nonneg hσ 4)]
    have hpow : σ^4 ≤ σ^3 := by
      have h := mul_le_mul_of_nonneg_left hσ1 (pow_nonneg hσ 3)
      nlinarith only [h]
    calc
      _ ≤ R*σ^4 := mul_le_mul_of_nonneg_right (hx 3) (pow_nonneg hσ 4)
      _ ≤ R*σ^3 := mul_le_mul_of_nonneg_left hpow hR
      _ ≤ 1 := by nlinarith [mul_nonneg hR (pow_nonneg hσ 3)]

universe u
                                                                         
                                                                               
theorem exists_bourgainQuartic_scaled_moment :
    ∃ C > (0:ℝ), ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ),
      (∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1) →
      ∀ (c σ R : ℝ), |c| ≤ 1 → 0 ≤ σ → σ ≤ 1 → 0 ≤ R → 5*R*σ^3 ≤ 1 →
      ∀ x : Fin 4 → ℝ, (∀ j, |x j| ≤ R) →
      ‖∑ i ∈ S, z i*fordAdditiveCharacter
        (x 0*(c+σ*s i)+x 1*(c+σ*s i)^2+
          x 2*(c+σ*s i)^3+x 3*(c+σ*s i)^4)‖^6 ≤
        C*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
          ‖∑ i ∈ S, z i*fordAdditiveCharacter
            ((σ*s i)*(x 0+2*c*x 1+3*c^2*x 2+4*c^3*x 3)+
              (σ*s i)^2*(x 1+3*c*x 2+6*c^2*x 3)+ξ*s i)‖^6) := by
  obtain ⟨C,hC,h⟩ := exists_bourgainCubicQuartic_finite_moment.{u}
  refine ⟨C,hC,?_⟩
  intro ι S z s hs c σ R hc hσ hσ1 hR hsmall x hx
  have hb := bourgainQuartic_remainder_bounds hc hσ hσ1 hR hsmall x hx
  let L := x 0+2*c*x 1+3*c^2*x 2+4*c^3*x 3
  let Q := x 1+3*c*x 2+6*c^2*x 3
  let A := (x 2+4*c*x 3)*σ^3
  let B := x 3*σ^4
  let Z := fun i => z i*fordAdditiveCharacter ((σ*s i)*L+(σ*s i)^2*Q)
  have hmain := h A (abs_le.mp hb.1) B (abs_le.mp hb.2) S Z s hs
  have he :
      (∑ i ∈ S, z i*fordAdditiveCharacter
        (x 0*(c+σ*s i)+x 1*(c+σ*s i)^2+
          x 2*(c+σ*s i)^3+x 3*(c+σ*s i)^4)) =
      fordAdditiveCharacter (x 0*c+x 1*c^2+x 2*c^3+x 3*c^4)*
        ∑ i ∈ S, Z i*fordAdditiveCharacter (A*(s i)^3+B*(s i)^4) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [Z]
    rw [show fordAdditiveCharacter (x 0*c+x 1*c^2+x 2*c^3+x 3*c^4)*
        ((z i*fordAdditiveCharacter ((σ*s i)*L+(σ*s i)^2*Q))*
          fordAdditiveCharacter (A*(s i)^3+B*(s i)^4)) =
        z i*(fordAdditiveCharacter (x 0*c+x 1*c^2+x 2*c^3+x 3*c^4)*
          (fordAdditiveCharacter ((σ*s i)*L+(σ*s i)^2*Q)*
            fordAdditiveCharacter (A*(s i)^3+B*(s i)^4))) by ring]
    rw [←fordAdditiveCharacter_add,←fordAdditiveCharacter_add]
    congr 2
    dsimp [L,Q,A,B]
    ring
  rw [he,norm_mul,sargos_character_norm,one_mul]
  have hr (ξ : ℝ) :
      (∑ i ∈ S, Z i*fordAdditiveCharacter (ξ*s i)) =
      ∑ i ∈ S, z i*fordAdditiveCharacter
        ((σ*s i)*L+(σ*s i)^2*Q+ξ*s i) := by
    simp only [Z,mul_assoc,←fordAdditiveCharacter_add]
  simpa only [hr,L,Q] using hmain

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025

                                                                        
                                                                                 
private theorem bourgainQuadraticFrame_finite_product {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (u : ι → ℝ) (v : τ → ℝ) {a b R : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hab : a ≠ b) (hR : 0 ≤ R) :
    (∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
      ‖sargosPlanarSum S z u (fun i => (u i)^2)
        ((bourgainQuadraticFrame a b).mulVec x 0)
        ((bourgainQuadraticFrame a b).mulVec x 1)‖^6*
      ‖sargosPlanarSum V c v (fun j => (v j)^2)
        ((bourgainQuadraticFrame a b).mulVec x 2)
        ((bourgainQuadraticFrame a b).mulVec x 3)‖^6) ≤
      (6*(b-a)^4)⁻¹*
        parabolaBoxBilinearMoment S S z z u u (10*R) 0 0*
        parabolaBoxBilinearMoment V V c c v v (10*R) 0 0 := by
  have hf : Continuous (fun p : ℝ × ℝ =>
      ‖sargosPlanarSum S z u (fun i => (u i)^2) p.1 p.2‖^6) := by
    unfold sargosPlanarSum fordAdditiveCharacter
    fun_prop
  have hg : Continuous (fun p : ℝ × ℝ =>
      ‖sargosPlanarSum V c v (fun j => (v j)^2) p.1 p.2‖^6) := by
    unfold sargosPlanarSum fordAdditiveCharacter
    fun_prop
  have h := bourgainQuadraticFrame_box_product ha hb hab hR
    (fun p => ‖sargosPlanarSum S z u (fun i => (u i)^2) p.1 p.2‖^6)
    (fun p => ‖sargosPlanarSum V c v (fun j => (v j)^2) p.1 p.2‖^6)
    hf hg (fun _ => by positivity) (fun _ => by positivity)
  have he (w : ℝ) : w^2*w^4=w^6 := by ring
  simpa only [parabolaBoxBilinearMoment,he,zero_sub,zero_add,neg_mul] using h

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem integrable_bourgain_modulated_box {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (s u : ι → ℝ) (R r t : ℝ) :
    Integrable (fun ξ : ℝ => ((1+|ξ|)^102)⁻¹*
      parabolaBoxBilinearMoment S S
        (fun i => z i*fordAdditiveCharacter (ξ*s i))
        (fun i => z i*fordAdditiveCharacter (ξ*s i)) u u R r t) := by
  let B := Icc (r-R) (r+R) ×ˢ Icc (t-R) (t+R)
  let F := fun (ξ : ℝ) (p : ℝ × ℝ) =>
    ‖sargosPlanarSum S (fun i => z i*fordAdditiveCharacter (ξ*s i))
      u (fun i => (u i)^2) p.1 p.2‖^6
  let V := fun ξ : ℝ => ((1+|ξ|)^102)⁻¹
  have hFc : Continuous (fun q : ℝ × (ℝ × ℝ) => F q.1 q.2) := by
    unfold F sargosPlanarSum fordAdditiveCharacter
    fun_prop
  have hFb (ξ : ℝ) (p : ℝ × ℝ) :
      ‖F ξ p‖ ≤ (∑ i ∈ S, ‖z i‖)^6 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (by dsimp [F]; positivity)]
    apply pow_le_pow_left₀ (norm_nonneg _) _ 6
    have h := norm_sargosPlanarSum_le_sum_norm S
      (fun i => z i*fordAdditiveCharacter (ξ*s i))
      u (fun i => (u i)^2) p.1 p.2
    simpa only [norm_mul,sargos_character_norm,mul_one] using h
  have hiV : Integrable V := bourgainRemainderEnvelope_integrable
  have hiF : Integrable (fun q : ℝ × (ℝ × ℝ) => V q.1*F q.1 q.2)
      (volume.prod (volume.restrict B)) := by
    have hiConst : IntegrableOn (fun _p : ℝ × ℝ => (1:ℝ)) B :=
      integrableOn_const (isCompact_Icc.prod isCompact_Icc).measure_ne_top
    have hprod := hiV.mul_prod hiConst
    have h := hprod.mul_bdd hFc.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun q => hFb q.1 q.2))
    simpa only [mul_one] using h
  have he (w : ℝ) : w^2*w^4=w^6 := by ring
  simpa only [integral_const_mul,F,V,B,parabolaBoxBilinearMoment,he] using
    hiF.integral_prod_left

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025

public  theorem bourgain_character_six_bound {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (θ : ι → ℝ) :
    ‖(‖∑ i ∈ S, z i*fordAdditiveCharacter (θ i)‖^6:ℝ)‖ ≤
      (∑ i ∈ S, ‖z i‖)^6 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 6
  calc
    _ ≤ ∑ i ∈ S, ‖z i*fordAdditiveCharacter (θ i)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul,sargos_character_norm,mul_one]

private theorem bourgain_frame_modulation {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ) (σ ξ α γ : ℝ) :
    sargosPlanarSum S (fun i => z i*fordAdditiveCharacter (ξ*s i))
      (fun i => σ*s i) (fun i => (σ*s i)^2) α γ =
    ∑ i ∈ S, z i*fordAdditiveCharacter
      ((σ*s i)*α+(σ*s i)^2*γ+ξ*s i) := by
  unfold sargosPlanarSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc,←fordAdditiveCharacter_add]
  congr 2
  ring

private theorem bourgainQuadraticFrame_apply (a b : ℝ) (x : Fin 4 → ℝ) :
    (bourgainQuadraticFrame a b).mulVec x =
      ![x 0+2*a*x 1+3*a^2*x 2+4*a^3*x 3,
        x 1+3*a*x 2+6*a^2*x 3,
        x 0+2*b*x 1+3*b^2*x 2+4*b^3*x 3,
        x 1+3*b*x 2+6*b^2*x 3] := by
  funext i
  fin_cases i <;>
    simp [bourgainQuadraticFrame,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring


public  theorem bourgain_kernel_setIntegral_bound
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {B : Set α} {f : α → ℝ} {H : β → α → ℝ} {C : ℝ}
    (hB : MeasurableSet B) (hf : IntegrableOn f B μ)
    (hH : Integrable (Function.uncurry H) (ν.prod (μ.restrict B)))
    (hp : ∀ x ∈ B, f x ≤ C*(∫ y, H y x ∂ν)) :
    (∫ x in B, f x ∂μ) ≤ C*(∫ y, ∫ x in B, H y x ∂μ ∂ν) := by
  have h := setIntegral_mono_on hf (hH.integral_prod_right.const_mul C) hB hp
  rw [integral_const_mul] at h
  dsimp only [Function.uncurry] at h
  have hswap := integral_integral_swap (μ:=ν) (ν:=μ.restrict B) hH
  rw [←hswap] at h
  exact h

universe u
set_option maxHeartbeats 400000 in
                                                                     
                                                                                     
theorem exists_bourgainQuartic_bilinear_reduction :
    ∃ C > (0:ℝ), ∀ (ι τ : Type u) (S : Finset ι) (V : Finset τ)
      (z : ι → ℂ) (c : τ → ℂ) (s : ι → ℝ) (v : τ → ℝ),
      (∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1) →
      (∀ j ∈ V, v j ∈ Icc (-1:ℝ) 1) →
      ∀ (a b σ R : ℝ), |a| ≤ 1 → |b| ≤ 1 → a ≠ b →
      0 ≤ σ → σ ≤ 1 → 0 ≤ R → 5*R*σ^3 ≤ 1 →
      (∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
        ‖∑ i ∈ S, z i*fordAdditiveCharacter
          (x 0*(a+σ*s i)+x 1*(a+σ*s i)^2+
            x 2*(a+σ*s i)^3+x 3*(a+σ*s i)^4)‖^6*
        ‖∑ j ∈ V, c j*fordAdditiveCharacter
          (x 0*(b+σ*v j)+x 1*(b+σ*v j)^2+
            x 2*(b+σ*v j)^3+x 3*(b+σ*v j)^4)‖^6) ≤
        C*(6*(b-a)^4)⁻¹*
          (∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
            parabolaBoxBilinearMoment S S
              (fun i => z i*fordAdditiveCharacter (ξ*s i))
              (fun i => z i*fordAdditiveCharacter (ξ*s i))
              (fun i => σ*s i) (fun i => σ*s i) (10*R) 0 0)*
          (∫ η : ℝ, ((1+|η|)^102)⁻¹*
            parabolaBoxBilinearMoment V V
              (fun j => c j*fordAdditiveCharacter (η*v j))
              (fun j => c j*fordAdditiveCharacter (η*v j))
              (fun j => σ*v j) (fun j => σ*v j) (10*R) 0 0) := by
  obtain ⟨C,hC,hbound⟩ := exists_bourgainQuartic_scaled_moment.{u}
  refine ⟨C^2,by positivity,?_⟩
  intro ι τ S V z c s v hs hv a b σ R ha hb hab hσ hσ1 hR hsmall
  let B := Icc (fun _ : Fin 4 => -R) (fun _ : Fin 4 => R)
  let W := fun ξ : ℝ => ((1+|ξ|)^102)⁻¹
  let A := fun x : Fin 4 → ℝ => ‖∑ i ∈ S, z i*fordAdditiveCharacter
    (x 0*(a+σ*s i)+x 1*(a+σ*s i)^2+x 2*(a+σ*s i)^3+x 3*(a+σ*s i)^4)‖^6
  let D := fun x : Fin 4 → ℝ => ‖∑ j ∈ V, c j*fordAdditiveCharacter
    (x 0*(b+σ*v j)+x 1*(b+σ*v j)^2+x 2*(b+σ*v j)^3+x 3*(b+σ*v j)^4)‖^6
  let F := fun (ξ : ℝ) (x : Fin 4 → ℝ) =>
    ‖∑ i ∈ S, z i*fordAdditiveCharacter
      ((σ*s i)*(x 0+2*a*x 1+3*a^2*x 2+4*a^3*x 3)+
        (σ*s i)^2*(x 1+3*a*x 2+6*a^2*x 3)+ξ*s i)‖^6
  let G := fun (η : ℝ) (x : Fin 4 → ℝ) =>
    ‖∑ j ∈ V, c j*fordAdditiveCharacter
      ((σ*v j)*(x 0+2*b*x 1+3*b^2*x 2+4*b^3*x 3)+
        (σ*v j)^2*(x 1+3*b*x 2+6*b^2*x 3)+η*v j)‖^6
  let J := fun ξ : ℝ => parabolaBoxBilinearMoment S S
    (fun i => z i*fordAdditiveCharacter (ξ*s i))
    (fun i => z i*fordAdditiveCharacter (ξ*s i))
    (fun i => σ*s i) (fun i => σ*s i) (10*R) 0 0
  let K := fun η : ℝ => parabolaBoxBilinearMoment V V
    (fun j => c j*fordAdditiveCharacter (η*v j))
    (fun j => c j*fordAdditiveCharacter (η*v j))
    (fun j => σ*v j) (fun j => σ*v j) (10*R) 0 0
  have hF0 (ξ : ℝ) (x : Fin 4 → ℝ) : 0 ≤ F ξ x := by dsimp [F]; positivity
  have hG0 (η : ℝ) (x : Fin 4 → ℝ) : 0 ≤ G η x := by dsimp [G]; positivity
  have hcont : Continuous (fun qx : (ℝ × ℝ) × (Fin 4 → ℝ) =>
      F qx.1.1 qx.2*G qx.1.2 qx.2) := by
    unfold F G fordAdditiveCharacter
    fun_prop
  have hfinite (qx : (ℝ × ℝ) × (Fin 4 → ℝ)) :
      ‖F qx.1.1 qx.2*G qx.1.2 qx.2‖ ≤
        (∑ i ∈ S, ‖z i‖)^6*(∑ j ∈ V, ‖c j‖)^6 := by
    rw [norm_mul]
    exact mul_le_mul (bourgain_character_six_bound S z _)
      (bourgain_character_six_bound V c _) (norm_nonneg _) (by positivity)
  have hW : Integrable W := bourgainRemainderEnvelope_integrable
  have hiH : Integrable (fun qx : (ℝ × ℝ) × (Fin 4 → ℝ) =>
      W qx.1.1*W qx.1.2*(F qx.1.1 qx.2*G qx.1.2 qx.2))
      (volume.prod (volume.restrict B)) := by
    have hconst : IntegrableOn (fun _x : Fin 4 → ℝ => (1:ℝ)) B :=
      integrableOn_const isCompact_Icc.measure_ne_top
    have hprod := (hW.mul_prod hW).mul_prod hconst
    have h := hprod.mul_bdd hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hfinite)
    convert h using 1
    funext qx
    simp only [mul_one]
  have hAD : IntegrableOn (fun x => A x*D x) B := by
    have hc : Continuous (fun x => A x*D x) := by
      unfold A D fordAdditiveCharacter
      fun_prop
    exact hc.continuousOn.integrableOn_compact isCompact_Icc
  have hpoint (x : Fin 4 → ℝ) (hx : x ∈ B) :
      A x*D x ≤ C^2*(∫ q : ℝ × ℝ, W q.1*W q.2*(F q.1 x*G q.2 x)) := by
    have hxc : ∀ j, |x j| ≤ R := fun j => abs_le.mpr ⟨hx.1 j,hx.2 j⟩
    have hA := hbound S z s hs a σ R ha hσ hσ1 hR hsmall x hxc
    have hD := hbound V c v hv b σ R hb hσ hσ1 hR hsmall x hxc
    have hpos : 0 ≤ C*(∫ ξ : ℝ, W ξ*F ξ x) :=
      mul_nonneg hC.le (integral_nonneg (fun ξ => mul_nonneg (by dsimp [W]; positivity) (hF0 ξ x)))
    have hprod := mul_le_mul hA hD (by positivity) hpos
    have he : (∫ q : ℝ × ℝ, W q.1*W q.2*(F q.1 x*G q.2 x)) =
        (∫ ξ : ℝ, W ξ*F ξ x)*(∫ η : ℝ, W η*G η x) := by
      calc
        _ = ∫ q : ℝ × ℝ, (W q.1*F q.1 x)*(W q.2*G q.2 x) := by
          apply integral_congr_ae
          filter_upwards with q
          ring
        _ = _ := integral_prod_mul (μ:=volume) (ν:=volume)
          (fun ξ : ℝ => W ξ*F ξ x) (fun η : ℝ => W η*G η x)
    rw [he]
    calc
      _ ≤ (C*(∫ ξ : ℝ, W ξ*F ξ x))*(C*(∫ η : ℝ, W η*G η x)) := hprod
      _ = _ := by ring
  have hm := bourgain_kernel_setIntegral_bound (α:=Fin 4 → ℝ) (β:=ℝ × ℝ)
    (μ:=volume) (ν:=volume) (B:=B) (C:=C^2)
    (f:=fun x => A x*D x)
    (H:=fun q x => W q.1*W q.2*(F q.1 x*G q.2 x))
    measurableSet_Icc hAD hiH hpoint
  have hFframe (ξ : ℝ) (x : Fin 4 → ℝ) :
      F ξ x = ‖sargosPlanarSum S (fun i => z i*fordAdditiveCharacter (ξ*s i))
        (fun i => σ*s i) (fun i => (σ*s i)^2)
        ((bourgainQuadraticFrame a b).mulVec x 0)
        ((bourgainQuadraticFrame a b).mulVec x 1)‖^6 := by
    rw [bourgain_frame_modulation,bourgainQuadraticFrame_apply]
    rfl
  have hGframe (η : ℝ) (x : Fin 4 → ℝ) :
      G η x = ‖sargosPlanarSum V (fun j => c j*fordAdditiveCharacter (η*v j))
        (fun j => σ*v j) (fun j => (σ*v j)^2)
        ((bourgainQuadraticFrame a b).mulVec x 2)
        ((bourgainQuadraticFrame a b).mulVec x 3)‖^6 := by
    rw [bourgain_frame_modulation,bourgainQuadraticFrame_apply]
    rfl
  have hinner (q : ℝ × ℝ) :
      (∫ x : Fin 4 → ℝ in B, F q.1 x*G q.2 x) ≤
        (6*(b-a)^4)⁻¹*J q.1*K q.2 := by
    simpa only [hFframe,hGframe,J,K,B] using
      bourgainQuadraticFrame_finite_product S V
        (fun i => z i*fordAdditiveCharacter (q.1*s i))
        (fun j => c j*fordAdditiveCharacter (q.2*v j))
        (fun i => σ*s i) (fun j => σ*v j) ha hb hab hR
  have hJ : Integrable (fun ξ => W ξ*J ξ) :=
    integrable_bourgain_modulated_box S z s (fun i => σ*s i) (10*R) 0 0
  have hK : Integrable (fun η => W η*K η) :=
    integrable_bourgain_modulated_box V c v (fun j => σ*v j) (10*R) 0 0
  have hmajor := integral_mono hiH.integral_prod_left
    ((hJ.mul_prod hK).const_mul ((6*(b-a)^4)⁻¹)) (fun q => by
      dsimp only [Prod.fst,Prod.snd]
      rw [integral_const_mul]
      calc
        _ ≤ (W q.1*W q.2)*((6*(b-a)^4)⁻¹*J q.1*K q.2) :=
          mul_le_mul_of_nonneg_left (hinner q) (by dsimp [W]; positivity)
        _ = _ := by ring)
  rw [integral_const_mul] at hmajor
  have heProduct : (∫ q : ℝ × ℝ, (W q.1*J q.1)*(W q.2*K q.2)) =
      (∫ ξ : ℝ, W ξ*J ξ)*(∫ η : ℝ, W η*K η) :=
    integral_prod_mul (μ:=volume) (ν:=volume)
      (fun ξ : ℝ => W ξ*J ξ) (fun η : ℝ => W η*K η)
  rw [heProduct] at hmajor
  calc
    _ ≤ C^2*(∫ q : ℝ × ℝ, ∫ x : Fin 4 → ℝ in B,
        W q.1*W q.2*(F q.1 x*G q.2 x)) := hm
    _ ≤ C^2*((6*(b-a)^4)⁻¹*
        ((∫ ξ : ℝ, W ξ*J ξ)*(∫ η : ℝ, W η*K η))) :=
      mul_le_mul_of_nonneg_left hmajor (sq_nonneg C)
    _ = _ := by dsimp [W,J,K]; ring

end TaoTrudgianYang2025


noncomputable section
namespace TaoTrudgianYang2025

                                                                          
                                                          
public  theorem bourgain_source_quartic_phase {t : ℝ} (ht : 0 ≤ t) (x : Fin 4 → ℝ) :
    x 0*t+x 1*t^2+x 2*t^((3:ℝ)/2)+x 3*Real.sqrt t =
      x 3*Real.sqrt t+x 0*(Real.sqrt t)^2+
        x 2*(Real.sqrt t)^3+x 1*(Real.sqrt t)^4 := by
  have h3 : (Real.sqrt t)^3 = t^((3:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_natCast,←Real.rpow_mul ht]
    congr 1
    norm_num
  have h4 : (Real.sqrt t)^4 = t^2 := by
    calc
      _ = ((Real.sqrt t)^2)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt ht]
  rw [Real.sq_sqrt ht,h3,h4]
  ring

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory Set
namespace TaoTrudgianYang2025

public  def bourgainSourcePermutation : (Fin 4 → ℝ) ≃ᵐ (Fin 4 → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => ℝ)
    ((Equiv.swap (0:Fin 4) 3).trans (Equiv.swap 1 3))

private theorem bourgainSourcePermutation_apply (x : Fin 4 → ℝ) :
    bourgainSourcePermutation x = ![x 3,x 0,x 2,x 1] := by
  funext i
  fin_cases i <;> rfl

public  theorem bourgainSourcePermutation_measurePreserving :
    MeasurePreserving bourgainSourcePermutation volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ : Fin 4 => ℝ)
    ((Equiv.swap (0:Fin 4) 3).trans (Equiv.swap 1 3))

private theorem bourgainSourcePermutation_preimage_cube (R : ℝ) :
    bourgainSourcePermutation ⁻¹' Icc (fun _ => -R) (fun _ => R) =
      Icc (fun _ => -R) (fun _ => R) := by
  ext x
  change ((∀ i, -R ≤ bourgainSourcePermutation x i) ∧
    ∀ i, bourgainSourcePermutation x i ≤ R) ↔
    ((∀ i, -R ≤ x i) ∧ ∀ i, x i ≤ R)
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> intro i <;> fin_cases i <;>
    first | exact h1 0 | exact h1 1 | exact h1 2 | exact h1 3 |
      exact h2 0 | exact h2 1 | exact h2 2 | exact h2 3

private theorem bourgainSourcePermutation_cube_integral (R : ℝ)
    (f : (Fin 4 → ℝ) → ℝ) :
    (∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
      f (bourgainSourcePermutation x)) =
    ∫ y : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R), f y := by
  let B := Icc (fun _ : Fin 4 => -R) (fun _ : Fin 4 => R)
  have h := bourgainSourcePermutation_measurePreserving.integral_comp
    bourgainSourcePermutation.measurableEmbedding (B.indicator f)
  rw [integral_indicator measurableSet_Icc] at h
  have he (x : Fin 4 → ℝ) :
      B.indicator f (bourgainSourcePermutation x) =
        B.indicator (fun y => f (bourgainSourcePermutation y)) x := by
    have hx : bourgainSourcePermutation x ∈ B ↔ x ∈ B := by
      change x ∈ bourgainSourcePermutation ⁻¹' B ↔ x ∈ B
      rw [bourgainSourcePermutation_preimage_cube]
    by_cases hmem : x ∈ B
    · rw [indicator_of_mem hmem,indicator_of_mem (hx.mpr hmem)]
    · rw [indicator_of_notMem hmem,indicator_of_notMem (mt hx.mp hmem)]
  simp_rw [he] at h
  rw [integral_indicator measurableSet_Icc] at h
  exact h

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

                                                                   
                                                                               
                                                 
theorem exists_bourgainSourceCurve_bilinear_reduction :
    ∃ C > (0:ℝ), ∀ (ι τ : Type u) (S : Finset ι) (V : Finset τ)
      (z : ι → ℂ) (c : τ → ℂ) (w : ι → ℝ) (v : τ → ℝ),
      (∀ i ∈ S, 0 ≤ w i) → (∀ j ∈ V, 0 ≤ v j) →
      ∀ (a b σ R : ℝ), |a| ≤ 1 → |b| ≤ 1 → a ≠ b →
      0 < σ → σ ≤ 1 → 0 ≤ R → 5*R*σ^3 ≤ 1 →
      (∀ i ∈ S, |Real.sqrt (w i)-a| ≤ σ) →
      (∀ j ∈ V, |Real.sqrt (v j)-b| ≤ σ) →
      (∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
        ‖∑ i ∈ S, z i*fordAdditiveCharacter
          (x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))‖^6*
        ‖∑ j ∈ V, c j*fordAdditiveCharacter
          (x 0*v j+x 1*(v j)^2+x 2*(v j)^((3:ℝ)/2)+x 3*Real.sqrt (v j))‖^6) ≤
        C*(6*(b-a)^4)⁻¹*
          (∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
            parabolaBoxBilinearMoment S S
              (fun i => z i*fordAdditiveCharacter (ξ*((Real.sqrt (w i)-a)/σ)))
              (fun i => z i*fordAdditiveCharacter (ξ*((Real.sqrt (w i)-a)/σ)))
              (fun i => Real.sqrt (w i)-a) (fun i => Real.sqrt (w i)-a) (10*R) 0 0)*
          (∫ η : ℝ, ((1+|η|)^102)⁻¹*
            parabolaBoxBilinearMoment V V
              (fun j => c j*fordAdditiveCharacter (η*((Real.sqrt (v j)-b)/σ)))
              (fun j => c j*fordAdditiveCharacter (η*((Real.sqrt (v j)-b)/σ)))
              (fun j => Real.sqrt (v j)-b) (fun j => Real.sqrt (v j)-b) (10*R) 0 0) := by
  obtain ⟨C,hC,hbound⟩ := exists_bourgainQuartic_bilinear_reduction.{u}
  refine ⟨C,hC,?_⟩
  intro ι τ S V z c w v hw hv a b σ R ha hb hab hσ hσ1 hR hsmall hwc hvc
  let s := fun i => (Real.sqrt (w i)-a)/σ
  let t := fun j => (Real.sqrt (v j)-b)/σ
  have hs : ∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1 := by
    intro i hi
    apply abs_le.mp
    dsimp [s]
    rw [abs_div,abs_of_pos hσ]
    exact (div_le_one hσ).mpr (hwc i hi)
  have ht : ∀ j ∈ V, t j ∈ Icc (-1:ℝ) 1 := by
    intro j hj
    apply abs_le.mp
    dsimp [t]
    rw [abs_div,abs_of_pos hσ]
    exact (div_le_one hσ).mpr (hvc j hj)
  have hsbase (i : ι) : σ*s i = Real.sqrt (w i)-a := by
    dsimp [s]
    field_simp
  have htbase (j : τ) : σ*t j = Real.sqrt (v j)-b := by
    dsimp [t]
    field_simp
  have hscenter (i : ι) : a+σ*s i = Real.sqrt (w i) := by rw [hsbase]; ring
  have htcenter (j : τ) : b+σ*t j = Real.sqrt (v j) := by rw [htbase]; ring
  let QS := fun y : Fin 4 → ℝ => ‖∑ i ∈ S, z i*fordAdditiveCharacter
    (y 0*(a+σ*s i)+y 1*(a+σ*s i)^2+y 2*(a+σ*s i)^3+y 3*(a+σ*s i)^4)‖^6
  let QV := fun y : Fin 4 → ℝ => ‖∑ j ∈ V, c j*fordAdditiveCharacter
    (y 0*(b+σ*t j)+y 1*(b+σ*t j)^2+y 2*(b+σ*t j)^3+y 3*(b+σ*t j)^4)‖^6
  have heS (x : Fin 4 → ℝ) :
      (∑ i ∈ S, z i*fordAdditiveCharacter
        (x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))) =
      ∑ i ∈ S, z i*fordAdditiveCharacter
        ((bourgainSourcePermutation x) 0*(a+σ*s i)+
          (bourgainSourcePermutation x) 1*(a+σ*s i)^2+
          (bourgainSourcePermutation x) 2*(a+σ*s i)^3+
          (bourgainSourcePermutation x) 3*(a+σ*s i)^4) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hscenter,bourgainSourcePermutation_apply]
    exact congrArg (fun q => z i*fordAdditiveCharacter q)
      (bourgain_source_quartic_phase (hw i hi) x)
  have heV (x : Fin 4 → ℝ) :
      (∑ j ∈ V, c j*fordAdditiveCharacter
        (x 0*v j+x 1*(v j)^2+x 2*(v j)^((3:ℝ)/2)+x 3*Real.sqrt (v j))) =
      ∑ j ∈ V, c j*fordAdditiveCharacter
        ((bourgainSourcePermutation x) 0*(b+σ*t j)+
          (bourgainSourcePermutation x) 1*(b+σ*t j)^2+
          (bourgainSourcePermutation x) 2*(b+σ*t j)^3+
          (bourgainSourcePermutation x) 3*(b+σ*t j)^4) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [htcenter,bourgainSourcePermutation_apply]
    exact congrArg (fun q => c j*fordAdditiveCharacter q)
      (bourgain_source_quartic_phase (hv j hj) x)
  have hmain := hbound ι τ S V z c s t hs ht a b σ R ha hb hab hσ.le hσ1 hR hsmall
  calc
    _ = ∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
        QS (bourgainSourcePermutation x)*QV (bourgainSourcePermutation x) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [heS,heV]
    _ = ∫ y : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R), QS y*QV y :=
      bourgainSourcePermutation_cube_integral R (fun y => QS y*QV y)
    _ ≤ _ := by
      simpa only [QS,QV,hsbase,htbase,s,t] using hmain

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private theorem exists_parabolaBox_scaled_rapid_decoupling {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ (n : ℕ) (σ R r t : ℝ), 0 < σ → σ ≤ 1 → 0 < R →
      3/(100*R) ≤ (σ/(2:ℝ)^n)^2 →
      ∀ (ι : Type u) (S : Fin (2^n) → Finset ι)
        (z : Fin (2^n) → ι → ℂ) (x : Fin (2^n) → ι → ℝ),
        (∀ j, ∀ k ∈ S j, x j k ∈ Icc
          (σ*((j:ℕ)/((2^n:ℕ):ℝ))) (σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ)))) →
        parabolaBoxBilinearMoment (Finset.univ.sigma S) (Finset.univ.sigma S)
          (fun jk => z jk.1 jk.2) (fun jk => z jk.1 jk.2)
          (fun jk => x jk.1 jk.2) (fun jk => x jk.1 jk.2) R r t ≤
          C*(2:ℝ)^(ε*n)*
            (∑ j, (parabolaWeightedSixNorm
              (fun p : ℝ × ℝ => parabolaRapidWeight R r t p.1 p.2)
              (S j) (z j) (x j))^2)^3 := by
  obtain ⟨D,hDpos,hD⟩ := exists_parabolaDecouplingBound_dyadic.{u}
    (ε:=ε/6) (by positivity)
  refine ⟨D^6,by positivity,?_⟩
  intro n σ R r t hσ hσ₁ hR hwidth ι S z x hx
  let W := fun p : ℝ × ℝ => parabolaRapidWeight R r t p.1 p.2
  have hW : ParabolaWeightBand (σ/((2^n:ℕ):ℝ)) W := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using parabolaRapidWeight_band hR hwidth r t
  have hnorm := (hD n).rescale hσ (a:=0) (by norm_num)
    (by simpa using hσ₁) ι W hW S z x (by simpa only [zero_add] using hx)
  have hcube := pow_le_pow_left₀ (sq_nonneg _) hnorm 3
  simp only [mul_pow,←pow_mul] at hcube
  have hcoef : (D*(2:ℝ)^((ε/6)*n))^6 = D^6*(2:ℝ)^(ε*n) := by
    rw [mul_pow,←Real.rpow_mul_natCast (by norm_num)]
    congr 1
    congr 1
    push_cast
    ring
  norm_num only [show (2*3:ℕ)=6 by omega] at hcube
  rw [←mul_pow,hcoef] at hcube
  have hbox := parabolaBox_le_rapid (Finset.univ.sigma S) (Finset.univ.sigma S)
    (fun jk => z jk.1 jk.2) (fun jk => z jk.1 jk.2)
    (fun jk => x jk.1 jk.2) (fun jk => x jk.1 jk.2) hR r t
  have hid := parabolaWeightedSixNorm_pow_six W hW.1 hW.2.1
    (Finset.univ.sigma S) (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2)
  have he : parabolaRapidBilinearMoment
      (Finset.univ.sigma S) (Finset.univ.sigma S)
      (fun jk => z jk.1 jk.2) (fun jk => z jk.1 jk.2)
      (fun jk => x jk.1 jk.2) (fun jk => x jk.1 jk.2) R r t =
      (parabolaWeightedSixNorm W (Finset.univ.sigma S)
        (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2))^6 := by
    simpa only [parabolaRapidBilinearMoment,parabolaWeightedBilinearMoment,W] using hid.symm
  exact hbox.trans (he.le.trans hcube)

private theorem exists_parabolaBox_scaled_source_decoupling {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ (n : ℕ) (σ R r t : ℝ), 0 < σ → σ ≤ 1 → 0 < R →
      3/(100*R) ≤ (σ/(2:ℝ)^n)^2 →
      ∀ (ι : Type u) (S : Fin (2^n) → Finset ι)
        (z : Fin (2^n) → ι → ℂ) (x : Fin (2^n) → ι → ℝ),
        (∀ j, ∀ k ∈ S j, x j k ∈ Icc
          (σ*((j:ℕ)/((2^n:ℕ):ℝ))) (σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ)))) →
        parabolaBoxBilinearMoment (Finset.univ.sigma S) (Finset.univ.sigma S)
          (fun jk => z jk.1 jk.2) (fun jk => z jk.1 jk.2)
          (fun jk => x jk.1 jk.2) (fun jk => x jk.1 jk.2) R r t ≤
          C*(2:ℝ)^(ε*n)*
            (∑ j, (parabolaWeightedSixNorm
              (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2)
              (S j) (z j) (x j))^2)^3 := by
  obtain ⟨C,hC,hbox⟩ := exists_parabolaBox_scaled_rapid_decoupling.{u} hε
  obtain ⟨K,hK,hcomp⟩ := parabolaRapidWeight_le_sourceWeight
  refine ⟨C*K,by positivity,?_⟩
  intro n σ R r t hσ hσ₁ hR hwidth ι S z x hx
  have hm := hbox n σ R r t hσ hσ₁ hR hwidth ι S z x hx
  have hnorm (j : Fin (2^n)) :=
    parabola_sixNorm_weight_comparison hK.le
      (fun p : ℝ × ℝ => parabolaRapidWeight_nonneg R r t p.1 p.2)
      (fun p : ℝ × ℝ => parabolaSourceWeight_nonneg R r t p.1 p.2)
      (parabolaRapidWeight_band hR hwidth r t).2.1
      (integrable_parabolaSourceWeight hR r t)
      (fun p => hcomp R r t p.1 p.2) (S j) (z j) (x j)
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hnorm j)
  rw [←Finset.mul_sum] at hs
  have hcube := pow_le_pow_left₀
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hs 3
  rw [mul_pow] at hcube
  have hroot := Real.rpow_inv_natCast_pow hK.le (by norm_num : (3:ℕ) ≠ 0)
  simp only [Nat.cast_ofNat] at hroot
  rw [hroot] at hcube
  calc
    _ ≤ _ := hm
    _ ≤ C*(2:ℝ)^(ε*n)*(K*
        (∑ j, (parabolaWeightedSixNorm
          (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2)
          (S j) (z j) (x j))^2)^3) :=
      mul_le_mul_of_nonneg_left hcube (by positivity)
    _ = _ := by ring
end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

                                                                         
                                                                            
                                                             
theorem exists_parabolaBox_scaled_modulation_decoupling {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ (n : ℕ) (σ R r t : ℝ), 0 < σ → σ ≤ 1 → 1 ≤ σ*R →
      3/(100*R) ≤ (σ/(2:ℝ)^n)^2 →
      ∀ (ι : Type u) (S : Fin (2^n) → Finset ι)
        (z : Fin (2^n) → ι → ℂ) (s : Fin (2^n) → ι → ℝ),
        (∀ j, ∀ k ∈ S j, s j k ∈ Icc
          ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) →
        (∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
          parabolaBoxBilinearMoment (Finset.univ.sigma S) (Finset.univ.sigma S)
            (fun jk => z jk.1 jk.2*fordAdditiveCharacter (ξ*s jk.1 jk.2))
            (fun jk => z jk.1 jk.2*fordAdditiveCharacter (ξ*s jk.1 jk.2))
            (fun jk => σ*s jk.1 jk.2) (fun jk => σ*s jk.1 jk.2) R r t) ≤
          C*(2:ℝ)^(ε*n)*
            (∑ j, (parabolaWeightedSixNorm
              (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2)
              (S j) (z j) (fun i => σ*s j i))^2)^3 := by
  obtain ⟨D,hD,hdec⟩ := exists_parabolaBox_scaled_source_decoupling.{u} hε
  refine ⟨D*Real.pi,by positivity,?_⟩
  intro n σ R r t hσ hσ₁ hσR hwidth ι S z s hs
  have hR : 0 < R := (mul_pos_iff_of_pos_left hσ).mp (lt_of_lt_of_le zero_lt_one hσR)
  let Q := ∑ j, (parabolaWeightedSixNorm
    (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2)
    (S j) (z j) (fun i => σ*s j i))^2
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hx : ∀ j, ∀ k ∈ S j, σ*s j k ∈ Icc
      (σ*((j:ℕ)/((2^n:ℕ):ℝ))) (σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ))) := by
    intro j k hk
    exact ⟨mul_le_mul_of_nonneg_left (hs j k hk).1 hσ.le,
      mul_le_mul_of_nonneg_left (hs j k hk).2 hσ.le⟩
  have hpoint (ξ : ℝ) :
      parabolaBoxBilinearMoment (Finset.univ.sigma S) (Finset.univ.sigma S)
        (fun jk => z jk.1 jk.2*fordAdditiveCharacter (ξ*s jk.1 jk.2))
        (fun jk => z jk.1 jk.2*fordAdditiveCharacter (ξ*s jk.1 jk.2))
        (fun jk => σ*s jk.1 jk.2) (fun jk => σ*s jk.1 jk.2) R r t ≤
        D*(2:ℝ)^(ε*n)*(1+|ξ|/(σ*R))^100*Q^3 := by
    have hd := hdec n σ R r t hσ hσ₁ hR hwidth ι S
      (fun j i => z j i*fordAdditiveCharacter (ξ*s j i)) (fun j i => σ*s j i) hx
    have hmod (v : ℝ) : (ξ/σ)*(σ*v) = ξ*v := by field_simp
    have hratio : |ξ/σ|/R = |ξ|/(σ*R) := by rw [abs_div,abs_of_pos hσ,div_div]
    have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun j _ =>
      parabola_sourceWeight_modulation (S j) (z j) (fun i => σ*s j i) hR r t (ξ/σ))
    simp_rw [hmod,hratio] at hsum
    rw [←Finset.mul_sum] at hsum
    have hc := pow_le_pow_left₀
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hsum 3
    rw [mul_pow] at hc
    have hroot := Real.rpow_inv_natCast_pow
      (by positivity : (0:ℝ) ≤ (1+|ξ|/(σ*R))^100) (by norm_num : (3:ℕ) ≠ 0)
    simp only [Nat.cast_ofNat] at hroot
    rw [hroot] at hc
    calc
      _ ≤ _ := hd
      _ ≤ D*(2:ℝ)^(ε*n)*((1+|ξ|/(σ*R))^100*Q^3) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by ring
  have hi := integrable_bourgain_modulated_box (Finset.univ.sigma S)
    (fun jk => z jk.1 jk.2) (fun jk => s jk.1 jk.2) (fun jk => σ*s jk.1 jk.2) R r t
  have hj := integrable_inv_one_add_sq.const_mul (D*(2:ℝ)^(ε*n)*Q^3)
  have hm := integral_mono hi hj (fun ξ => by
    calc
      _ ≤ ((1+|ξ|)^102)⁻¹*(D*(2:ℝ)^(ε*n)*(1+|ξ|/(σ*R))^100*Q^3) :=
        mul_le_mul_of_nonneg_left (hpoint ξ) (by positivity)
      _ = D*(2:ℝ)^(ε*n)*Q^3*(((1+|ξ|)^102)⁻¹*(1+|ξ|/(σ*R))^100) := by ring
      _ ≤ D*(2:ℝ)^(ε*n)*Q^3*(1+ξ^2)⁻¹ :=
        mul_le_mul_of_nonneg_left (bourgain_modulation_envelope hσR ξ) (by positivity))
  rw [integral_const_mul,integral_univ_inv_one_add_sq] at hm
  calc
    _ ≤ _ := hm
    _ = _ := by dsimp [Q]; ring

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

                                                                      
                                                                           
                                                                                 
theorem exists_bourgainSourceCurve_parabolic_cell_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ (n : ℕ) (a b σ R : ℝ),
      |a| ≤ 1 → |b| ≤ 1 → a ≠ b → 0 < σ → σ ≤ 1 → 0 ≤ R →
      5*R*σ^3 ≤ 1 → 1 ≤ σ*(10*R) →
      3/(100*(10*R)) ≤ (σ/(2:ℝ)^n)^2 →
      ∀ (ι τ : Type u) (S : Fin (2^n) → Finset ι) (V : Fin (2^n) → Finset τ)
        (z : Fin (2^n) → ι → ℂ) (c : Fin (2^n) → τ → ℂ)
        (w : Fin (2^n) → ι → ℝ) (v : Fin (2^n) → τ → ℝ),
        (∀ j, ∀ i ∈ S j, 0 ≤ w j i) → (∀ j, ∀ k ∈ V j, 0 ≤ v j k) →
        (∀ j, ∀ i ∈ S j, Real.sqrt (w j i) ∈ Icc
          (a+σ*((j:ℕ)/((2^n:ℕ):ℝ))) (a+σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ)))) →
        (∀ j, ∀ k ∈ V j, Real.sqrt (v j k) ∈ Icc
          (b+σ*((j:ℕ)/((2^n:ℕ):ℝ))) (b+σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ)))) →
        (∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
          ‖∑ ji ∈ Finset.univ.sigma S, z ji.1 ji.2*fordAdditiveCharacter
            (x 0*w ji.1 ji.2+x 1*(w ji.1 ji.2)^2+
              x 2*(w ji.1 ji.2)^((3:ℝ)/2)+x 3*Real.sqrt (w ji.1 ji.2))‖^6*
          ‖∑ jk ∈ Finset.univ.sigma V, c jk.1 jk.2*fordAdditiveCharacter
            (x 0*v jk.1 jk.2+x 1*(v jk.1 jk.2)^2+
              x 2*(v jk.1 jk.2)^((3:ℝ)/2)+x 3*Real.sqrt (v jk.1 jk.2))‖^6) ≤
          C*(2:ℝ)^(ε*n)*(6*(b-a)^4)⁻¹*
            (∑ j, (parabolaWeightedSixNorm
              (fun p : ℝ × ℝ => parabolaSourceWeight (10*R) 0 0 p.1 p.2)
              (S j) (z j) (fun i => Real.sqrt (w j i)-a))^2)^3*
            (∑ j, (parabolaWeightedSixNorm
              (fun p : ℝ × ℝ => parabolaSourceWeight (10*R) 0 0 p.1 p.2)
              (V j) (c j) (fun k => Real.sqrt (v j k)-b))^2)^3 := by
  obtain ⟨E,hE,hsource⟩ := exists_bourgainSourceCurve_bilinear_reduction.{u}
  obtain ⟨D,hD,hdec⟩ := exists_parabolaBox_scaled_modulation_decoupling.{u}
    (ε:=ε/2) (by positivity)
  refine ⟨E*D^2,by positivity,?_⟩
  intro n a b σ R ha hb hab hσ hσ₁ hR hrem hσR hwidth ι τ S V z c w v hw hv hwgrid hvgrid
  let s := fun j i => (Real.sqrt (w j i)-a)/σ
  let t := fun j k => (Real.sqrt (v j k)-b)/σ
  have hsbase (j : Fin (2^n)) (i : ι) : σ*s j i = Real.sqrt (w j i)-a := by
    dsimp [s]
    field_simp
  have htbase (j : Fin (2^n)) (k : τ) : σ*t j k = Real.sqrt (v j k)-b := by
    dsimp [t]
    field_simp
  have hsgrid : ∀ j, ∀ i ∈ S j, s j i ∈ Icc
      ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ)) := by
    intro j i hi
    constructor
    · apply (le_div_iff₀ hσ).mpr
      nlinarith [(hwgrid j i hi).1]
    · apply (div_le_iff₀ hσ).mpr
      nlinarith [(hwgrid j i hi).2]
  have htgrid : ∀ j, ∀ k ∈ V j, t j k ∈ Icc
      ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ)) := by
    intro j k hk
    constructor
    · apply (le_div_iff₀ hσ).mpr
      nlinarith [(hvgrid j k hk).1]
    · apply (div_le_iff₀ hσ).mpr
      nlinarith [(hvgrid j k hk).2]
  have hunit (j : Fin (2^n)) {y : ℝ}
      (hy : y ∈ Icc ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) :
      y ∈ Icc (0:ℝ) 1 := by
    have hl : (0:ℝ) ≤ (j:ℕ)/((2^n:ℕ):ℝ) := by positivity
    have hh : ((j:ℕ)+1:ℝ)/((2^n:ℕ):ℝ) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      exact_mod_cast (show (j:ℕ)+1 ≤ 2^n from j.isLt)
    exact ⟨hl.trans hy.1,hy.2.trans hh⟩
  have hwindowS : ∀ ji ∈ Finset.univ.sigma S, |Real.sqrt (w ji.1 ji.2)-a| ≤ σ := by
    intro ji hji
    have hh := hunit ji.1 (hsgrid ji.1 ji.2 (Finset.mem_sigma.mp hji).2)
    rw [←hsbase,abs_of_nonneg (mul_nonneg hσ.le hh.1)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh.2 hσ.le
  have hwindowV : ∀ jk ∈ Finset.univ.sigma V, |Real.sqrt (v jk.1 jk.2)-b| ≤ σ := by
    intro jk hjk
    have hh := hunit jk.1 (htgrid jk.1 jk.2 (Finset.mem_sigma.mp hjk).2)
    rw [←htbase,abs_of_nonneg (mul_nonneg hσ.le hh.1)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh.2 hσ.le
  have hmain := hsource ((j : Fin (2^n)) × ι) ((j : Fin (2^n)) × τ)
    (Finset.univ.sigma S) (Finset.univ.sigma V)
    (fun ji => z ji.1 ji.2) (fun jk => c jk.1 jk.2)
    (fun ji => w ji.1 ji.2) (fun jk => v jk.1 jk.2)
    (fun ji hji => hw ji.1 ji.2 (Finset.mem_sigma.mp hji).2)
    (fun jk hjk => hv jk.1 jk.2 (Finset.mem_sigma.mp hjk).2)
    a b σ R ha hb hab hσ hσ₁ hR hrem hwindowS hwindowV
  have hS := hdec n σ (10*R) 0 0 hσ hσ₁ hσR hwidth ι S z s hsgrid
  have hV := hdec n σ (10*R) 0 0 hσ hσ₁ hσR hwidth τ V c t htgrid
  simp_rw [hsbase] at hS
  simp_rw [htbase] at hV
  have hnonnegV : 0 ≤ ∫ η : ℝ, ((1+|η|)^102)⁻¹*
      parabolaBoxBilinearMoment (Finset.univ.sigma V) (Finset.univ.sigma V)
        (fun jk => c jk.1 jk.2*fordAdditiveCharacter (η*t jk.1 jk.2))
        (fun jk => c jk.1 jk.2*fordAdditiveCharacter (η*t jk.1 jk.2))
        (fun jk => Real.sqrt (v jk.1 jk.2)-b)
        (fun jk => Real.sqrt (v jk.1 jk.2)-b) (10*R) 0 0 := by
    apply integral_nonneg
    intro η
    apply mul_nonneg (by positivity)
    unfold parabolaBoxBilinearMoment
    exact integral_nonneg (fun p => mul_nonneg (sq_nonneg _)
      (pow_nonneg (norm_nonneg _) 4))
  have hprod := mul_le_mul hS hV hnonnegV (by positivity)
  have hm := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ E*(6*(b-a)^4)⁻¹ by positivity)
  have he : ((2:ℝ)^((ε/2)*n))^2 = (2:ℝ)^(ε*n) := by
    rw [←Real.rpow_mul_natCast (by norm_num)]
    congr 1
    push_cast
    ring
  calc
    _ ≤ _ := hmain
    _ ≤ _ := by simpa only [s,t,mul_assoc] using hm
    _ = _ := by
      have he' : (2:ℝ)^((ε/2)*n)*(2:ℝ)^((ε/2)*n) = (2:ℝ)^(ε*n) := by
        rw [←pow_two,he]
      calc
        _ = E*D^2*((2:ℝ)^((ε/2)*n)*(2:ℝ)^((ε/2)*n))*(6*(b-a)^4)⁻¹*
            (∑ j, (parabolaWeightedSixNorm
              (fun p : ℝ × ℝ => parabolaSourceWeight (10*R) 0 0 p.1 p.2)
              (S j) (z j) (fun i => Real.sqrt (w j i)-a))^2)^3*
            (∑ j, (parabolaWeightedSixNorm
              (fun p : ℝ × ℝ => parabolaSourceWeight (10*R) 0 0 p.1 p.2)
              (V j) (c j) (fun k => Real.sqrt (v j k)-b))^2)^3 := by ring
        _ = _ := by rw [he']

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025
universe u

private theorem exists_bourgainCubicQuartic_inverse_moment :
    ∃ C > (0:ℝ), ∀ a ∈ Icc (-1:ℝ) 1, ∀ b ∈ Icc (-1:ℝ) 1,
      ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ) (s θ : ι → ℝ),
        (∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1) →
        ‖∑ i ∈ S, z i*fordAdditiveCharacter (θ i)‖^6 ≤
          C*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
            ‖∑ i ∈ S, z i*fordAdditiveCharacter
              (θ i+a*(s i)^3+b*(s i)^4+ξ*s i)‖^6) := by
  obtain ⟨C,hC,h⟩ := exists_bourgainCubicQuartic_finite_moment.{u}
  refine ⟨C,hC,?_⟩
  intro a ha b hb ι S z s θ hs
  have hna : -a ∈ Icc (-1:ℝ) 1 := ⟨by linarith [ha.2],by linarith [ha.1]⟩
  have hnb : -b ∈ Icc (-1:ℝ) 1 := ⟨by linarith [hb.2],by linarith [hb.1]⟩
  have hm := h (-a) hna (-b) hnb S
    (fun i => z i*fordAdditiveCharacter (θ i+a*(s i)^3+b*(s i)^4)) s hs
  have hleft :
      (∑ i ∈ S, (z i*fordAdditiveCharacter (θ i+a*(s i)^3+b*(s i)^4))*
        fordAdditiveCharacter (-a*(s i)^3+-b*(s i)^4)) =
      ∑ i ∈ S, z i*fordAdditiveCharacter (θ i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_assoc,←fordAdditiveCharacter_add]
    congr 2
    ring
  have hright (ξ : ℝ) :
      (∑ i ∈ S, (z i*fordAdditiveCharacter (θ i+a*(s i)^3+b*(s i)^4))*
        fordAdditiveCharacter (ξ*s i)) =
      ∑ i ∈ S, z i*fordAdditiveCharacter
        (θ i+a*(s i)^3+b*(s i)^4+ξ*s i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_assoc,←fordAdditiveCharacter_add]
  simpa only [hleft,hright] using hm

private def bourgainCurveCellFrame (a c : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,-2*a,3*c^2,8*c^3;
     0,1,-3*c,-6*c^2;
     0,0,1,0;
     0,0,0,1]

private theorem bourgainCurveCellFrame_apply (a c : ℝ) (y : Fin 4 → ℝ) :
    (bourgainCurveCellFrame a c).mulVec y =
      ![y 0-2*a*y 1+3*c^2*y 2+8*c^3*y 3,
        y 1-3*c*y 2-6*c^2*y 3,y 2,y 3] := by
  funext i
  fin_cases i <;>
    simp [bourgainCurveCellFrame,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

private theorem bourgainCurveCellFrame_det (a c : ℝ) :
    (bourgainCurveCellFrame a c).det = 1 := by
  unfold bourgainCurveCellFrame
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ,Matrix.det_fin_three,Matrix.submatrix]

private theorem bourgainCurveCellFrame_measurePreserving (a c : ℝ) :
    MeasurePreserving ((bourgainCurveCellFrame a c).mulVec)
      (volume : Measure (Fin 4 → ℝ)) volume := by
  have hc : Continuous ((bourgainCurveCellFrame a c).mulVec) := by
    change Continuous (Matrix.toLin' (bourgainCurveCellFrame a c))
    exact LinearMap.continuous_on_pi _
  refine ⟨hc.measurable,?_⟩
  have hm := Real.map_matrix_volume_pi_eq_smul_volume_pi
    (show (bourgainCurveCellFrame a c).det ≠ 0 by rw [bourgainCurveCellFrame_det]; norm_num)
  change Measure.map (bourgainCurveCellFrame a c).mulVec volume = _ at hm
  simpa only [bourgainCurveCellFrame_det,inv_one,abs_one,
    ENNReal.ofReal_one,one_smul] using hm

private theorem bourgainCurveCellFrame_phase (a c δ s : ℝ) (y : Fin 4 → ℝ) :
    let x := (bourgainCurveCellFrame a c).mulVec y
    x 0*(c+δ*s)+x 1*(c+δ*s)^2+x 2*(c+δ*s)^3+x 3*(c+δ*s)^4 =
      (c+δ*s-a)*y 0+(c+δ*s-a)^2*y 1+
        ((y 2+4*c*y 3)*δ^3)*s^3+(y 3*δ^4)*s^4+
        (a*y 0-a^2*y 1+c^3*y 2+3*c^4*y 3) := by
  rw [bourgainCurveCellFrame_apply]
  dsimp
  ring

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025
universe u

public  theorem norm_bourgain_character_sum_add {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (θ : ι → ℝ) (k : ℝ) :
    ‖∑ i ∈ S, z i*fordAdditiveCharacter (θ i+k)‖ =
      ‖∑ i ∈ S, z i*fordAdditiveCharacter (θ i)‖ := by
  have he :
      (∑ i ∈ S, z i*fordAdditiveCharacter (θ i+k)) =
        (∑ i ∈ S, z i*fordAdditiveCharacter (θ i))*fordAdditiveCharacter k := by
    rw [Finset.sum_mul]
    simp only [fordAdditiveCharacter_add,mul_assoc]
  rw [he,norm_mul,sargos_character_norm,mul_one]

private theorem exists_bourgainCurveCell_inverse_pointwise :
    ∃ C > (0:ℝ), ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ),
      (∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1) →
      ∀ (a c δ R : ℝ), |c| ≤ 1 → 0 ≤ δ → δ ≤ 1 → 0 ≤ R → 5*R*δ^3 ≤ 1 →
      ∀ y : Fin 4 → ℝ, |y 2| ≤ R → |y 3| ≤ R →
        ‖∑ i ∈ S, z i*fordAdditiveCharacter
          ((c+δ*s i-a)*y 0+(c+δ*s i-a)^2*y 1)‖^6 ≤
          C*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
            ‖∑ i ∈ S, z i*fordAdditiveCharacter
              ((bourgainCurveCellFrame a c).mulVec y 0*(c+δ*s i)+
                (bourgainCurveCellFrame a c).mulVec y 1*(c+δ*s i)^2+
                (bourgainCurveCellFrame a c).mulVec y 2*(c+δ*s i)^3+
                (bourgainCurveCellFrame a c).mulVec y 3*(c+δ*s i)^4+ξ*s i)‖^6) := by
  obtain ⟨C,hC,h⟩ := exists_bourgainCubicQuartic_inverse_moment.{u}
  refine ⟨C,hC,?_⟩
  intro ι S z s hs a c δ R hc hδ hδ₁ hR hrem y hy₂ hy₃
  have hcoeff := bourgainQuartic_remainder_bounds hc hδ hδ₁ hR hrem
    ![0,0,y 2,y 3] (by
      intro j
      fin_cases j
      · simpa using hR
      · simpa using hR
      · exact hy₂
      · exact hy₃)
  change |(y 2+4*c*y 3)*δ^3| ≤ 1 ∧ |y 3*δ^4| ≤ 1 at hcoeff
  let P := fun i => (c+δ*s i-a)*y 0+(c+δ*s i-a)^2*y 1
  let A := (y 2+4*c*y 3)*δ^3
  let B := y 3*δ^4
  let K := a*y 0-a^2*y 1+c^3*y 2+3*c^4*y 3
  have hm := h A (abs_le.mp hcoeff.1) B (abs_le.mp hcoeff.2) S z s P hs
  have he (ξ : ℝ) :
      ‖∑ i ∈ S, z i*fordAdditiveCharacter
        ((bourgainCurveCellFrame a c).mulVec y 0*(c+δ*s i)+
          (bourgainCurveCellFrame a c).mulVec y 1*(c+δ*s i)^2+
          (bourgainCurveCellFrame a c).mulVec y 2*(c+δ*s i)^3+
          (bourgainCurveCellFrame a c).mulVec y 3*(c+δ*s i)^4+ξ*s i)‖ =
        ‖∑ i ∈ S, z i*fordAdditiveCharacter (P i+A*(s i)^3+B*(s i)^4+ξ*s i)‖ := by
    calc
      _ = ‖∑ i ∈ S, z i*fordAdditiveCharacter
          ((P i+A*(s i)^3+B*(s i)^4+ξ*s i)+K)‖ := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        congr 2
        have hp := bourgainCurveCellFrame_phase a c δ (s i) y
        dsimp only at hp
        rw [hp]
        dsimp [P,A,B,K]
        ring
      _ = _ := norm_bourgain_character_sum_add S z _ K
  simpa only [he,P] using hm

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025

private theorem bourgainCurveCellFrame_norm_bound {a c R : ℝ}
    (ha : |a| ≤ 1) (hc : |c| ≤ 1) (hR : 0 ≤ R)
    (y : Fin 4 → ℝ) (hy₂ : |y 2| ≤ R) (hy₃ : |y 3| ≤ R) :
    ‖(bourgainCurveCellFrame a c).mulVec y‖ ≤ 14*(|y 0|+|y 1|+R) := by
  have hc2 : |c|^2 ≤ 1 := pow_le_one₀ (abs_nonneg _) hc
  have hc3 : |c|^3 ≤ 1 := pow_le_one₀ (abs_nonneg _) hc
  have hrow (i : Fin 4) : (∑ j, |bourgainCurveCellFrame a c i j|) ≤ 14 := by
    fin_cases i <;>
      norm_num [bourgainCurveCellFrame,Fin.sum_univ_succ,abs_mul,abs_pow] <;>
      nlinarith [sq_abs c]
  have hy (j : Fin 4) : |y j| ≤ |y 0|+|y 1|+R := by
    fin_cases j
    · change |y 0| ≤ _
      linarith [abs_nonneg (y 1)]
    · change |y 1| ≤ _
      linarith [abs_nonneg (y 0)]
    · change |y 2| ≤ _
      linarith [abs_nonneg (y 0),abs_nonneg (y 1)]
    · change |y 3| ≤ _
      linarith [abs_nonneg (y 0),abs_nonneg (y 1)]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [Real.norm_eq_abs]
  calc
    _ ≤ ∑ j, |bourgainCurveCellFrame a c i j*y j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |bourgainCurveCellFrame a c i j| * |y j| := by simp only [abs_mul]
    _ ≤ ∑ j, |bourgainCurveCellFrame a c i j| * (|y 0|+|y 1|+R) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hy j) (abs_nonneg _))
    _ = (∑ j, |bourgainCurveCellFrame a c i j|)*(|y 0|+|y 1|+R) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (hrow i) (by positivity)

private theorem bourgainCurveCellFrame_weight_bound {a c R δ : ℝ}
    (ha : |a| ≤ 1) (hc : |c| ≤ 1) (hR : 0 < R) (hδ : 0 < δ)
    (y : Fin 4 → ℝ) (hy₂ : |y 2| ≤ R) (hy₃ : |y 3| ≤ R) (ξ : ℝ) :
    parabolaSourceWeight R 0 0 (y 0) (y 1) ≤
      (32:ℝ)^100*(1+|ξ|/(δ*R))^100*
        ((1+‖R⁻¹ • ((bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0])‖)^100)⁻¹ := by
  let q := ‖(((y 0/R:ℝ):ℂ)+(y 1/R:ℝ)*Complex.I)‖
  let L := |ξ|/(δ*R)
  have hq : 0 ≤ q := norm_nonneg _
  have hL : 0 ≤ L := by positivity
  have hy₀ : |y 0| ≤ R*q := by
    have h := Complex.abs_re_le_norm (((y 0/R:ℝ):ℂ)+(y 1/R:ℝ)*Complex.I)
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero,
      abs_div,abs_of_pos hR] at h
    exact (div_le_iff₀ hR).mp h |>.trans_eq (mul_comm _ _)
  have hy₁ : |y 1| ≤ R*q := by
    have h := Complex.abs_im_le_norm (((y 0/R:ℝ):ℂ)+(y 1/R:ℝ)*Complex.I)
    simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,
      Complex.ofReal_re,Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_add,add_zero,
      abs_div,abs_of_pos hR] at h
    exact (div_le_iff₀ hR).mp h |>.trans_eq (mul_comm _ _)
  have hshift : ‖(![ξ/δ,0,0,0] : Fin 4 → ℝ)‖ ≤ |ξ|/δ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    fin_cases i <;> simp [Real.norm_eq_abs,abs_of_pos hδ] <;> positivity
  have hf := bourgainCurveCellFrame_norm_bound ha hc hR.le y hy₂ hy₃
  have hn : ‖R⁻¹ • ((bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0])‖ ≤
      28*q+14+L := by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hR]
    have hadd := norm_add_le ((bourgainCurveCellFrame a c).mulVec y) ![ξ/δ,0,0,0]
    have hb : ‖(bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0]‖ ≤
        R*(28*q+14+L) := by
      have hRL : R*L = |ξ|/δ := by dsimp [L]; field_simp
      nlinarith only [hadd,hf,hshift,hy₀,hy₁,hRL]
    have h := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hR.le)
    simpa only [←mul_assoc,inv_mul_cancel₀ hR.ne',one_mul] using h
  have hb : 1+‖R⁻¹ • ((bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0])‖ ≤
      32*(1+q)*(1+L) := by nlinarith [mul_nonneg hq hL]
  have hp := pow_le_pow_left₀ (by positivity) hb 100
  rw [mul_pow,mul_pow] at hp
  simp only [parabolaSourceWeight,sub_zero]
  change 1/(1+q)^100 ≤ (32:ℝ)^100*(1+L)^100*
    ((1+‖R⁻¹ • ((bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0])‖)^100)⁻¹
  rw [←div_eq_mul_inv,le_div_iff₀ (by positivity),one_div_mul_eq_div]
  apply (div_le_iff₀ (by positivity : (0:ℝ) < (1+q)^100)).mpr
  calc
    _ ≤ _ := hp
    _ = _ := by ac_rfl

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025

private def bourgainCurveCellMoment {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (u : ι → ℝ) (x : Fin 4 → ℝ) : ℝ :=
  ‖∑ i ∈ S, z i*fordAdditiveCharacter
    (x 0*u i+x 1*(u i)^2+x 2*(u i)^3+x 3*(u i)^4)‖^6

private theorem continuous_bourgainCurveCellMoment {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (u : ι → ℝ) :
    Continuous (bourgainCurveCellMoment S z u) := by
  unfold bourgainCurveCellMoment fordAdditiveCharacter
  fun_prop

public  theorem integrable_bourgainCurveCellWeight {R : ℝ} (hR : 0 < R) :
    Integrable (fun x : Fin 4 → ℝ => ((1+‖R⁻¹ • x‖)^100)⁻¹) := by
  have h := integrable_one_add_norm (E:=Fin 4 → ℝ) (μ:=volume) (r:=100) (by norm_num)
  have hi := h.comp_smul (inv_ne_zero hR.ne')
  have he (x : Fin 4 → ℝ) : (1+‖R⁻¹ • x‖)^(-(100:ℝ)) =
      ((1+‖R⁻¹ • x‖)^100)⁻¹ := by
    rw [Real.rpow_neg (by positivity),Real.rpow_ofNat]
  simpa only [he] using hi

private theorem integrable_bourgainCurveCellMoment {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (u : ι → ℝ) {R : ℝ} (hR : 0 < R) :
    Integrable (fun x : Fin 4 → ℝ =>
      ((1+‖R⁻¹ • x‖)^100)⁻¹*bourgainCurveCellMoment S z u x) := by
  exact (integrable_bourgainCurveCellWeight hR).mul_bdd
    (continuous_bourgainCurveCellMoment S z u).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => bourgain_character_six_bound S z
      (fun i => x 0*u i+x 1*(u i)^2+x 2*(u i)^3+x 3*(u i)^4)))

private theorem bourgainCurveCellFrame_shift_measurePreserving (a c δ ξ : ℝ) :
    MeasurePreserving
      (fun y : Fin 4 → ℝ => (bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0])
      volume volume :=
  (measurePreserving_add_right volume ![ξ/δ,0,0,0]).comp
    (bourgainCurveCellFrame_measurePreserving a c)

private theorem bourgainCurveCellFrame_shift_integral (a c δ ξ : ℝ)
    (f : (Fin 4 → ℝ) → ℝ) (hf : StronglyMeasurable f) :
    (∫ y : Fin 4 → ℝ, f ((bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0])) =
      ∫ x : Fin 4 → ℝ, f x := by
  have hT := bourgainCurveCellFrame_shift_measurePreserving a c δ ξ
  have h := integral_map (μ:=volume) hT.measurable.aemeasurable hf.aestronglyMeasurable
  rw [hT.map_eq] at h
  exact h.symm

private theorem bourgainCurveCellMoment_shift {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ) (c ξ : ℝ) {δ : ℝ} (hδ : δ ≠ 0)
    (x : Fin 4 → ℝ) :
    bourgainCurveCellMoment S z (fun i => c+δ*s i) (x+![ξ/δ,0,0,0]) =
      ‖∑ i ∈ S, z i*fordAdditiveCharacter
        (x 0*(c+δ*s i)+x 1*(c+δ*s i)^2+x 2*(c+δ*s i)^3+
          x 3*(c+δ*s i)^4+ξ*s i)‖^6 := by
  unfold bourgainCurveCellMoment
  have he :
      ‖∑ i ∈ S, z i*fordAdditiveCharacter
        ((x+![ξ/δ,0,0,0]) 0*(c+δ*s i)+(x+![ξ/δ,0,0,0]) 1*(c+δ*s i)^2+
          (x+![ξ/δ,0,0,0]) 2*(c+δ*s i)^3+(x+![ξ/δ,0,0,0]) 3*(c+δ*s i)^4)‖ =
      ‖∑ i ∈ S, z i*fordAdditiveCharacter
        ((x 0*(c+δ*s i)+x 1*(c+δ*s i)^2+x 2*(c+δ*s i)^3+
          x 3*(c+δ*s i)^4+ξ*s i)+ξ*c/δ)‖ := by
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    simp only [Pi.add_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      add_zero]
    field_simp
    ring
  rw [he,norm_bourgain_character_sum_add]

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025

private def bourgainCurveCellBaseWeight (R : ℝ) (y : Fin 4 → ℝ) : ℝ :=
  parabolaSourceWeight R 0 0 (y 0) (y 1)*
    (Icc (-R) R ×ˢ Icc (-R) R).indicator (fun _ : ℝ × ℝ => (1:ℝ)) (y 2,y 3)

private theorem bourgainCurveCellBaseWeight_nonneg (R : ℝ) (y : Fin 4 → ℝ) :
    0 ≤ bourgainCurveCellBaseWeight R y :=
  mul_nonneg (parabolaSourceWeight_nonneg _ _ _ _ _)
    (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

private theorem integrable_bourgainCurveCellBaseWeight {R : ℝ} (hR : 0 < R) :
    Integrable (bourgainCurveCellBaseWeight R) := by
  let B := Icc (-R) R ×ˢ Icc (-R) R
  have hi : Integrable (B.indicator (fun _ : ℝ × ℝ => (1:ℝ))) :=
    (integrableOn_const (isCompact_Icc.prod isCompact_Icc).measure_ne_top).integrable_indicator
      (measurableSet_Icc.prod measurableSet_Icc)
  have h := bourgainFourCoordinates_measurePreserving.integrable_comp_of_integrable
    ((integrable_parabolaSourceWeight hR 0 0).mul_prod hi)
  convert h using 1
  rfl

private theorem bourgainCurveCell_transverse_mass {R : ℝ} (hR : 0 ≤ R) :
    (∫ q : ℝ × ℝ, (Icc (-R) R ×ˢ Icc (-R) R).indicator
      (fun _ : ℝ × ℝ => (1:ℝ)) q) = 4*R^2 := by
  rw [integral_indicator (measurableSet_Icc.prod measurableSet_Icc),integral_const,
    smul_eq_mul,mul_one,measureReal_restrict_apply_univ]
  change (volume.prod volume).real (Icc (-R) R ×ˢ Icc (-R) R) = _
  rw [measureReal_prod_prod,Real.volume_real_Icc_of_le (by linarith),
    sub_neg_eq_add]
  ring

private theorem bourgainCurveCell_inner_bound {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (u : ι → ℝ) {a c R δ : ℝ}
    (ha : |a| ≤ 1) (hc : |c| ≤ 1) (hR : 0 < R) (hδ : 0 < δ) (ξ : ℝ) :
    (∫ y : Fin 4 → ℝ, bourgainCurveCellBaseWeight R y*
      bourgainCurveCellMoment S z u
        ((bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0])) ≤
      (32:ℝ)^100*(1+|ξ|/(δ*R))^100*
        (∫ x : Fin 4 → ℝ, ((1+‖R⁻¹ • x‖)^100)⁻¹*bourgainCurveCellMoment S z u x) := by
  let T := fun y : Fin 4 → ℝ => (bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0]
  let K := (32:ℝ)^100*(1+|ξ|/(δ*R))^100
  have hcF : Continuous ((bourgainCurveCellFrame a c).mulVec) := by
    change Continuous (Matrix.toLin' (bourgainCurveCellFrame a c))
    exact LinearMap.continuous_on_pi _
  have hcT : Continuous T := hcF.add continuous_const
  have hi₁ : Integrable (fun y => bourgainCurveCellBaseWeight R y*
      bourgainCurveCellMoment S z u (T y)) :=
    (integrable_bourgainCurveCellBaseWeight hR).mul_bdd
      ((continuous_bourgainCurveCellMoment S z u).comp hcT).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => bourgain_character_six_bound S z
        (fun i => T y 0*u i+T y 1*(u i)^2+T y 2*(u i)^3+T y 3*(u i)^4)))
  have hi₂ : Integrable (fun y => ((1+‖R⁻¹ • T y‖)^100)⁻¹*
      bourgainCurveCellMoment S z u (T y)) :=
    (bourgainCurveCellFrame_shift_measurePreserving a c δ ξ).integrable_comp_of_integrable
      (integrable_bourgainCurveCellMoment S z u hR)
  have hp (y : Fin 4 → ℝ) :
      bourgainCurveCellBaseWeight R y ≤ K*((1+‖R⁻¹ • T y‖)^100)⁻¹ := by
    by_cases hy : (y 2,y 3) ∈ Icc (-R) R ×ˢ Icc (-R) R
    · simp only [bourgainCurveCellBaseWeight,Set.indicator_of_mem hy,mul_one]
      exact bourgainCurveCellFrame_weight_bound ha hc hR hδ y
        (abs_le.mpr hy.1) (abs_le.mpr hy.2) ξ
    · simp only [bourgainCurveCellBaseWeight,Set.indicator_of_notMem hy,mul_zero]
      dsimp [K]
      positivity
  have hm := integral_mono hi₁ (hi₂.const_mul K) (fun y => by
    have h := mul_le_mul_of_nonneg_right (hp y)
      (show 0 ≤ bourgainCurveCellMoment S z u (T y) by unfold bourgainCurveCellMoment; positivity)
    simpa only [mul_assoc] using h)
  rw [integral_const_mul] at hm
  have hf : StronglyMeasurable (fun x : Fin 4 → ℝ =>
      ((1+‖R⁻¹ • x‖)^100)⁻¹*bourgainCurveCellMoment S z u x) := by
    have hwc : Continuous (fun x : Fin 4 → ℝ => ((1+‖R⁻¹ • x‖)^100)⁻¹) := by
      apply Continuous.inv₀
      · fun_prop
      · intro x
        positivity
    exact (hwc.mul (continuous_bourgainCurveCellMoment S z u)).stronglyMeasurable
  have he := bourgainCurveCellFrame_shift_integral a c δ ξ _ hf
  change (∫ y : Fin 4 → ℝ, ((1+‖R⁻¹ • T y‖)^100)⁻¹*
    bourgainCurveCellMoment S z u (T y)) = _ at he
  rw [he] at hm
  exact hm

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025
universe u

set_option maxHeartbeats 400000 in
private theorem exists_bourgainQuartic_cell_return :
    ∃ C > (0:ℝ), ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ),
      (∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1) →
      ∀ (a c δ R : ℝ), |a| ≤ 1 → |c| ≤ 1 → 0 < δ → δ ≤ 1 →
      0 < R → 5*R*δ^3 ≤ 1 → 1 ≤ δ*R →
      (∫ p : ℝ × ℝ, parabolaSourceWeight R 0 0 p.1 p.2*
        ‖∑ i ∈ S, z i*fordAdditiveCharacter
          ((c+δ*s i-a)*p.1+(c+δ*s i-a)^2*p.2)‖^6) ≤
        C/R^2*(∫ x : Fin 4 → ℝ, ((1+‖R⁻¹ • x‖)^100)⁻¹*
          bourgainCurveCellMoment S z (fun i => c+δ*s i) x) := by
  obtain ⟨E,hE,hInv⟩ := exists_bourgainCurveCell_inverse_pointwise.{u}
  refine ⟨E*(32:ℝ)^100*Real.pi/4,by positivity,?_⟩
  intro ι S z s hs a c δ R ha hc hδ hδ₁ hR hrem hδR
  let u := fun i => c+δ*s i
  let T := fun (ξ : ℝ) (y : Fin 4 → ℝ) =>
    (bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0]
  let W := fun ξ : ℝ => ((1+|ξ|)^102)⁻¹
  let P := fun p : ℝ × ℝ => ‖∑ i ∈ S, z i*fordAdditiveCharacter
    ((u i-a)*p.1+(u i-a)^2*p.2)‖^6
  let F := fun y : Fin 4 → ℝ => bourgainCurveCellBaseWeight R y*P (y 0,y 1)
  let H := fun (ξ : ℝ) (y : Fin 4 → ℝ) =>
    W ξ*bourgainCurveCellBaseWeight R y*bourgainCurveCellMoment S z u (T ξ y)
  let J := ∫ x : Fin 4 → ℝ, ((1+‖R⁻¹ • x‖)^100)⁻¹*bourgainCurveCellMoment S z u x
  have hJ : 0 ≤ J := integral_nonneg (fun x => by
    apply mul_nonneg (by positivity)
    unfold bourgainCurveCellMoment
    positivity)
  have hPc : Continuous P := by
    unfold P fordAdditiveCharacter
    fun_prop
  have hPb (p : ℝ × ℝ) : ‖P p‖ ≤ (∑ i ∈ S, ‖z i‖)^6 :=
    bourgain_character_six_bound S z (fun i => (u i-a)*p.1+(u i-a)^2*p.2)
  have hiF : Integrable F :=
    (integrable_bourgainCurveCellBaseWeight hR).mul_bdd
      (hPc.comp (by fun_prop)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => hPb (y 0,y 1)))
  have hcFrame : Continuous ((bourgainCurveCellFrame a c).mulVec) := by
    change Continuous (Matrix.toLin' (bourgainCurveCellFrame a c))
    exact LinearMap.continuous_on_pi _
  have hcT : Continuous (fun q : ℝ × (Fin 4 → ℝ) => T q.1 q.2) := by
    exact (hcFrame.comp continuous_snd).add (by dsimp [T]; fun_prop)
  have hcM : Continuous (fun q : ℝ × (Fin 4 → ℝ) =>
      bourgainCurveCellMoment S z u (T q.1 q.2)) :=
    (continuous_bourgainCurveCellMoment S z u).comp hcT
  have hiH : Integrable (Function.uncurry H) (volume.prod volume) := by
    have hp := bourgainRemainderEnvelope_integrable.mul_prod
      (integrable_bourgainCurveCellBaseWeight hR)
    exact hp.mul_bdd hcM.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun q => bourgain_character_six_bound S z
        (fun i => T q.1 q.2 0*u i+T q.1 q.2 1*(u i)^2+
          T q.1 q.2 2*(u i)^3+T q.1 q.2 3*(u i)^4)))
  have hp (y : Fin 4 → ℝ) : F y ≤ E*(∫ ξ : ℝ, H ξ y) := by
    by_cases hy : (y 2,y 3) ∈ Icc (-R) R ×ˢ Icc (-R) R
    · have hm := hInv S z s hs a c δ R hc hδ.le hδ₁ hR.le hrem y
        (abs_le.mpr hy.1) (abs_le.mpr hy.2)
      have he (ξ : ℝ) := bourgainCurveCellMoment_shift S z s c ξ hδ.ne'
        ((bourgainCurveCellFrame a c).mulVec y)
      have hmi : P (y 0,y 1) ≤ E*(∫ ξ : ℝ, W ξ*bourgainCurveCellMoment S z u (T ξ y)) := by
        simpa only [P,W,u,T,he] using hm
      have hm' := mul_le_mul_of_nonneg_left hmi (bourgainCurveCellBaseWeight_nonneg R y)
      have heH : (∫ ξ : ℝ, H ξ y) = bourgainCurveCellBaseWeight R y*
          (∫ ξ : ℝ, W ξ*bourgainCurveCellMoment S z u (T ξ y)) := by
        rw [←integral_const_mul]
        apply integral_congr_ae
        filter_upwards with ξ
        dsimp [H]
        ring
      rw [heH]
      simpa only [F,mul_left_comm] using hm'
    · simp only [F,H,bourgainCurveCellBaseWeight,Set.indicator_of_notMem hy,
        mul_zero,zero_mul,integral_zero,le_refl]
  have hmain := bourgain_kernel_setIntegral_bound
    (α:=Fin 4 → ℝ) (β:=ℝ) (μ:=volume) (ν:=volume)
    (B:=Set.univ) (C:=E) (f:=F) (H:=H)
    MeasurableSet.univ hiF.integrableOn
    (by simpa only [Measure.restrict_univ] using hiH) (fun y _ => hp y)
  simp only [setIntegral_univ] at hmain

  have hinner (ξ : ℝ) : (∫ y : Fin 4 → ℝ, H ξ y) ≤
      (32:ℝ)^100*J*(1+ξ^2)⁻¹ := by
    have hb := bourgainCurveCell_inner_bound S z u ha hc hR hδ ξ
    have heH : (∫ y : Fin 4 → ℝ, H ξ y) =
        W ξ*(∫ y : Fin 4 → ℝ, bourgainCurveCellBaseWeight R y*
          bourgainCurveCellMoment S z u (T ξ y)) := by
      simp only [H,mul_assoc,integral_const_mul]
    rw [heH]
    calc
      _ ≤ W ξ*((32:ℝ)^100*(1+|ξ|/(δ*R))^100*J) :=
        mul_le_mul_of_nonneg_left hb (by dsimp [W]; positivity)
      _ = (32:ℝ)^100*J*(W ξ*(1+|ξ|/(δ*R))^100) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (bourgain_modulation_envelope hδR ξ)
        (mul_nonneg (by positivity) hJ)
  have hiOuter : Integrable (fun ξ : ℝ => ∫ y : Fin 4 → ℝ, H ξ y) :=
    hiH.integral_prod_left
  have hout := integral_mono hiOuter
    (integrable_inv_one_add_sq.const_mul ((32:ℝ)^100*J)) hinner
  rw [integral_const_mul,integral_univ_inv_one_add_sq] at hout
  have hleft : (∫ y : Fin 4 → ℝ, F y) =
      4*R^2*(∫ p : ℝ × ℝ, parabolaSourceWeight R 0 0 p.1 p.2*P p) := by
    calc
      _ = ∫ y : Fin 4 → ℝ,
          (parabolaSourceWeight R 0 0 (y 0) (y 1)*P (y 0,y 1))*
            (Icc (-R) R ×ˢ Icc (-R) R).indicator (fun _ : ℝ × ℝ => (1:ℝ)) (y 2,y 3) := by
        apply integral_congr_ae
        filter_upwards with y
        dsimp [F,bourgainCurveCellBaseWeight]
        ring
      _ = (∫ p : ℝ × ℝ, parabolaSourceWeight R 0 0 p.1 p.2*P p)*
          (∫ q : ℝ × ℝ, (Icc (-R) R ×ˢ Icc (-R) R).indicator
            (fun _ : ℝ × ℝ => (1:ℝ)) q) :=
        bourgainFourCoordinates_integral_product
          (fun p : ℝ × ℝ => parabolaSourceWeight R 0 0 p.1 p.2*P p)
          ((Icc (-R) R ×ˢ Icc (-R) R).indicator (fun _ : ℝ × ℝ => (1:ℝ)))
      _ = _ := by rw [bourgainCurveCell_transverse_mass hR.le]; ring
  rw [hleft] at hmain
  have hfinal := hmain.trans (mul_le_mul_of_nonneg_left hout hE.le)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
  change (∫ p : ℝ × ℝ, parabolaSourceWeight R 0 0 p.1 p.2*P p)*R^2 ≤ _
  nlinarith only [hfinal]

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

public  theorem bourgainSourcePermutation_norm (x : Fin 4 → ℝ) :
    ‖bourgainSourcePermutation x‖ = ‖x‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
    intro i
    fin_cases i <;>
      first | exact norm_le_pi_norm x 3 | exact norm_le_pi_norm x 0 |
        exact norm_le_pi_norm x 2 | exact norm_le_pi_norm x 1
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (bourgainSourcePermutation x))).mpr
    intro i
    fin_cases i <;>
      first | exact norm_le_pi_norm (bourgainSourcePermutation x) 1 |
        exact norm_le_pi_norm (bourgainSourcePermutation x) 3 |
        exact norm_le_pi_norm (bourgainSourcePermutation x) 2 |
        exact norm_le_pi_norm (bourgainSourcePermutation x) 0

                                                                          
                                                                    
                                                                            
theorem exists_bourgainSourceCurve_cell_return :
    ∃ C > (0:ℝ), ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ),
      (∀ i ∈ S, 0 ≤ w i) →
      ∀ (a c δ R : ℝ), |a| ≤ 1 → |c| ≤ 1 → 0 < δ → δ ≤ 1 →
      0 < R → 5*R*δ^3 ≤ 1 → 1 ≤ δ*R →
      (∀ i ∈ S, |Real.sqrt (w i)-c| ≤ δ) →
      (∫ p : ℝ × ℝ, parabolaSourceWeight R 0 0 p.1 p.2*
        ‖∑ i ∈ S, z i*fordAdditiveCharacter
          ((Real.sqrt (w i)-a)*p.1+(Real.sqrt (w i)-a)^2*p.2)‖^6) ≤
        C/R^2*(∫ x : Fin 4 → ℝ, ((1+‖R⁻¹ • x‖)^100)⁻¹*
          ‖∑ i ∈ S, z i*fordAdditiveCharacter
            (x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))‖^6) := by
  obtain ⟨C,hC,h⟩ := exists_bourgainQuartic_cell_return.{u}
  refine ⟨C,hC,?_⟩
  intro ι S z w hw a c δ R ha hc hδ hδ₁ hR hrem hδR hwindow
  let s := fun i => (Real.sqrt (w i)-c)/δ
  have hs : ∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1 := by
    intro i hi
    have hh := abs_le.mp (hwindow i hi)
    constructor
    · apply (le_div_iff₀ hδ).mpr
      linarith [hh.1]
    · apply (div_le_iff₀ hδ).mpr
      linarith [hh.2]
  have hbase (i : ι) : c+δ*s i = Real.sqrt (w i) := by
    dsimp [s]
    field_simp
    ring
  have hmain := h S z s hs a c δ R ha hc hδ hδ₁ hR hrem hδR
  simp_rw [hbase] at hmain
  let f := fun x : Fin 4 → ℝ => ((1+‖R⁻¹ • x‖)^100)⁻¹*
    bourgainCurveCellMoment S z (fun i => Real.sqrt (w i)) x
  have he : (∫ x : Fin 4 → ℝ, f x) =
      ∫ x : Fin 4 → ℝ, ((1+‖R⁻¹ • x‖)^100)⁻¹*
        ‖∑ i ∈ S, z i*fordAdditiveCharacter
          (x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))‖^6 := by
    calc
      _ = ∫ x : Fin 4 → ℝ, f (bourgainSourcePermutation x) :=
        (bourgainSourcePermutation_measurePreserving.integral_comp
          bourgainSourcePermutation.measurableEmbedding f).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp only [f]
        rw [norm_smul,bourgainSourcePermutation_norm,←norm_smul]
        apply congrArg (fun v : ℝ => ((1+‖R⁻¹ • x‖)^100)⁻¹*v)
        unfold bourgainCurveCellMoment
        apply congrArg (fun v : ℂ => ‖v‖^6)
        apply Finset.sum_congr rfl
        intro i hi
        apply congrArg (fun v : ℝ => z i*fordAdditiveCharacter v)
        simpa only [bourgainSourcePermutation_apply,Matrix.cons_val_zero,
          Matrix.cons_val_one,Matrix.cons_val] using
          (bourgain_source_quartic_phase (hw i hi) x).symm
  change _ ≤ C/R^2*(∫ x : Fin 4 → ℝ, f x) at hmain
  rw [he] at hmain
  exact hmain

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

set_option maxHeartbeats 400000 in
                                                                     
                                                                            
                                                                      
theorem exists_bourgainSourceCurve_local_cell_decoupling {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ (n : ℕ) (a b σ R : ℝ),
      0 ≤ a → a+σ ≤ 1 → 0 ≤ b → b+σ ≤ 1 → a ≠ b →
      0 < σ → σ ≤ 1 → 0 < R → 5*R*σ^3 ≤ 1 →
      5*(10*R)*(σ/(2:ℝ)^n)^3 ≤ 1 → 1 ≤ (σ/(2:ℝ)^n)*(10*R) →
      3/(100*(10*R)) ≤ (σ/(2:ℝ)^n)^2 →
      ∀ (ι τ : Type u) (S : Fin (2^n) → Finset ι) (V : Fin (2^n) → Finset τ)
        (z : Fin (2^n) → ι → ℂ) (c : Fin (2^n) → τ → ℂ)
        (w : Fin (2^n) → ι → ℝ) (v : Fin (2^n) → τ → ℝ),
        (∀ j, ∀ i ∈ S j, 0 ≤ w j i) → (∀ j, ∀ k ∈ V j, 0 ≤ v j k) →
        (∀ j, ∀ i ∈ S j, Real.sqrt (w j i) ∈ Icc
          (a+σ*((j:ℕ)/((2^n:ℕ):ℝ))) (a+σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ)))) →
        (∀ j, ∀ k ∈ V j, Real.sqrt (v j k) ∈ Icc
          (b+σ*((j:ℕ)/((2^n:ℕ):ℝ))) (b+σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ)))) →
        (∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
          ‖∑ ji ∈ Finset.univ.sigma S, z ji.1 ji.2*fordAdditiveCharacter
            (x 0*w ji.1 ji.2+x 1*(w ji.1 ji.2)^2+
              x 2*(w ji.1 ji.2)^((3:ℝ)/2)+x 3*Real.sqrt (w ji.1 ji.2))‖^6*
          ‖∑ jk ∈ Finset.univ.sigma V, c jk.1 jk.2*fordAdditiveCharacter
            (x 0*v jk.1 jk.2+x 1*(v jk.1 jk.2)^2+
              x 2*(v jk.1 jk.2)^((3:ℝ)/2)+x 3*Real.sqrt (v jk.1 jk.2))‖^6) ≤
          C*(2:ℝ)^((ε+4)*n)/(10*R)^4*(6*(b-a)^4)⁻¹*
            (∑ j, ∫ x : Fin 4 → ℝ, ((1+‖(10*R)⁻¹ • x‖)^100)⁻¹*
              ‖∑ i ∈ S j, z j i*fordAdditiveCharacter
                (x 0*w j i+x 1*(w j i)^2+x 2*(w j i)^((3:ℝ)/2)+
                  x 3*Real.sqrt (w j i))‖^6)*
            (∑ j, ∫ x : Fin 4 → ℝ, ((1+‖(10*R)⁻¹ • x‖)^100)⁻¹*
              ‖∑ k ∈ V j, c j k*fordAdditiveCharacter
                (x 0*v j k+x 1*(v j k)^2+x 2*(v j k)^((3:ℝ)/2)+
                  x 3*Real.sqrt (v j k))‖^6) := by
  obtain ⟨D,hD,hSource⟩ := exists_bourgainSourceCurve_parabolic_cell_bound.{u} hε
  obtain ⟨E,hE,hReturn⟩ := exists_bourgainSourceCurve_cell_return.{u}
  refine ⟨D*E^2,by positivity,?_⟩
  intro n a b σ R ha haσ hb hbσ hab hσ hσ₁ hR hrem hfine hδR hwidth
    ι τ S V z c w v hw hv hwgrid hvgrid
  let δ := σ/(2:ℝ)^n
  let W := fun p : ℝ × ℝ => parabolaSourceWeight (10*R) 0 0 p.1 p.2
  let J {κ : Type u} (K : Finset κ) (q : κ → ℂ) (f : κ → ℝ) :=
    ∫ x : Fin 4 → ℝ, ((1+‖(10*R)⁻¹ • x‖)^100)⁻¹*
      ‖∑ i ∈ K, q i*fordAdditiveCharacter
        (x 0*f i+x 1*(f i)^2+x 2*(f i)^((3:ℝ)/2)+x 3*Real.sqrt (f i))‖^6
  have hδ : 0 < δ := div_pos hσ (by positivity)
  have hδσ : δ ≤ σ := div_le_self hσ.le (one_le_pow₀ (by norm_num))
  have hδ₁ : δ ≤ 1 := hδσ.trans hσ₁
  have hσR : 1 ≤ σ*(10*R) :=
    hδR.trans (mul_le_mul_of_nonneg_right hδσ (by positivity))
  have haabs : |a| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hbabs : |b| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hmain := hSource n a b σ R haabs hbabs hab hσ hσ₁ hR.le hrem hσR hwidth
    ι τ S V z c w v hw hv hwgrid hvgrid
  have hQ (κ : Type u) (K : Fin (2^n) → Finset κ)
      (q : Fin (2^n) → κ → ℂ) (f : Fin (2^n) → κ → ℝ)
      (d : ℝ) (hd : 0 ≤ d) (hdσ : d+σ ≤ 1)
      (hf : ∀ j, ∀ i ∈ K j, 0 ≤ f j i)
      (hgrid : ∀ j, ∀ i ∈ K j, Real.sqrt (f j i) ∈ Icc
        (d+σ*((j:ℕ)/((2^n:ℕ):ℝ))) (d+σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ)))) :
      (∑ j, (parabolaWeightedSixNorm W (K j) (q j)
        (fun i => Real.sqrt (f j i)-d))^2)^3 ≤
        ((2:ℝ)^n)^2*(E/(10*R)^2)*(∑ j, J (K j) (q j) (f j)) := by
    have hdabs : |d| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
    have hcell (j : Fin (2^n)) :
        (parabolaWeightedSixNorm W (K j) (q j)
          (fun i => Real.sqrt (f j i)-d))^6 ≤ E/(10*R)^2*J (K j) (q j) (f j) := by
      let e := d+σ*((j:ℕ)/((2^n:ℕ):ℝ))
      have hj : (0:ℝ) ≤ (j:ℕ)/((2^n:ℕ):ℝ) := by positivity
      have hj₁ : ((j:ℕ):ℝ)/((2^n:ℕ):ℝ) ≤ 1 := by
        apply (div_le_one (by positivity)).mpr
        exact_mod_cast Nat.le_of_lt j.isLt
      have he₀ : 0 ≤ e := add_nonneg hd (mul_nonneg hσ.le hj)
      have he₁ : e ≤ 1 := by
        have hh := mul_le_mul_of_nonneg_left hj₁ hσ.le
        dsimp [e]
        linarith
      have heabs : |e| ≤ 1 := abs_le.mpr ⟨by linarith,he₁⟩
      have heupper : d+σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ)) = e+δ := by
        dsimp [e,δ]
        push_cast
        ring
      have hwindow : ∀ i ∈ K j, |Real.sqrt (f j i)-e| ≤ δ := by
        intro i hi
        have hl := (hgrid j i hi).1
        have hh := (hgrid j i hi).2
        rw [heupper] at hh
        change e ≤ Real.sqrt (f j i) at hl
        rw [abs_of_nonneg (sub_nonneg.mpr hl)]
        linarith
      have hr := hReturn (K j) (q j) (f j) (hf j) d e δ (10*R) hdabs heabs
        hδ hδ₁ (by positivity) hfine hδR hwindow
      have hn := parabolaWeightedSixNorm_pow_six W
        (fun p => parabolaSourceWeight_nonneg _ _ _ _ _)
        (integrable_parabolaSourceWeight (by positivity : 0 < 10*R) 0 0)
        (K j) (q j) (fun i => Real.sqrt (f j i)-d)
      have hepow (x : ℝ) : x^2*x^4=x^6 := by ring
      rw [hn]
      simpa only [parabolaWeightedBilinearMoment,sargosPlanarSum,mul_assoc,hepow,W,J] using hr
    have hh := pow_sum_le_card_mul_sum_pow (s:=Finset.univ)
      (f:=fun j => (parabolaWeightedSixNorm W (K j) (q j)
        (fun i => Real.sqrt (f j i)-d))^2) (fun _ _ => sq_nonneg _) 2
    norm_num only [show (2+1:ℕ)=3 by omega,←pow_mul,
      show (2*3:ℕ)=6 by omega,Finset.card_univ,Fintype.card_fin,
      Nat.cast_pow,Nat.cast_ofNat] at hh
    have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hcell j)
    rw [←Finset.mul_sum] at hsum
    calc
      _ ≤ ((2:ℝ)^n)^2*∑ j, (parabolaWeightedSixNorm W (K j) (q j)
          (fun i => Real.sqrt (f j i)-d))^6 := by
        simpa only [pow_mul] using hh
      _ ≤ ((2:ℝ)^n)^2*(E/(10*R)^2*(∑ j, J (K j) (q j) (f j))) :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg ((2:ℝ)^n))
      _ = _ := by ring

  have hS := hQ ι S z w a ha haσ hw hwgrid
  have hV := hQ τ V c v b hb hbσ hv hvgrid
  have hJV : 0 ≤ ∑ j, J (V j) (c j) (v j) := by
    apply Finset.sum_nonneg
    intro j hj
    apply integral_nonneg
    intro x
    positivity
  have hprod := mul_le_mul hS hV (by positivity) (by positivity)
  have hm := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ D*(2:ℝ)^(ε*n)*(6*(b-a)^4)⁻¹ by positivity)
  have hpow : (2:ℝ)^(ε*n)*((2:ℝ)^n)^4 = (2:ℝ)^((ε+4)*n) := by
    have he : ((2:ℝ)^n)^4 = (2:ℝ)^((4:ℝ)*n) := by
      rw [←Real.rpow_natCast (2:ℝ) n,←Real.rpow_mul_natCast (by norm_num)]
      congr 1
      push_cast
      ring
    rw [he,←Real.rpow_add (by norm_num)]
    congr 1
    ring
  have halg (A B : ℝ) :
      (D*(2:ℝ)^(ε*n)*(6*(b-a)^4)⁻¹)*
        ((((2:ℝ)^n)^2*(E/(10*R)^2)*A)*(((2:ℝ)^n)^2*(E/(10*R)^2)*B)) =
      (D*E^2)*(2:ℝ)^((ε+4)*n)/(10*R)^4*(6*(b-a)^4)⁻¹*A*B := by
    rw [←hpow]
    ring
  calc
    _ ≤ _ := hmain
    _ ≤ _ := by simpa only [W,mul_assoc] using hm
    _ = _ := halg _ _

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

public  def bourgainRadialWeight (R : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  ((1+‖R⁻¹ • x‖)^100)⁻¹

public  theorem bourgainRadialWeight_nonneg (R : ℝ) (x : Fin 4 → ℝ) :
    0 ≤ bourgainRadialWeight R x := by
  unfold bourgainRadialWeight
  positivity

private theorem bourgainRadialWeight_le_one (R : ℝ) (x : Fin 4 → ℝ) :
    bourgainRadialWeight R x ≤ 1 := by
  unfold bourgainRadialWeight
  apply inv_le_one_of_one_le₀
  exact one_le_pow₀ (by linarith [norm_nonneg (R⁻¹ • x)])

public  theorem continuous_bourgainRadialWeight (R : ℝ) :
    Continuous (bourgainRadialWeight R) := by
  unfold bourgainRadialWeight
  apply Continuous.inv₀
  · fun_prop
  · intro x
    positivity

public  theorem bourgainRadialWeight_distance {R : ℝ} (hR : 0 < R) (x : Fin 4 → ℝ) :
    bourgainRadialWeight R x = ((1+‖x‖/R)^100)⁻¹ := by
  unfold bourgainRadialWeight
  rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hR]
  congr 2
  rw [div_eq_mul_inv,mul_comm]

private theorem integral_bourgainRadialWeight {R : ℝ} (hR : 0 ≤ R) :
    (∫ x : Fin 4 → ℝ, bourgainRadialWeight R x) =
      R^4*(∫ x : Fin 4 → ℝ, bourgainRadialWeight 1 x) := by
  have h := Measure.integral_comp_inv_smul_of_nonneg
    (volume : Measure (Fin 4 → ℝ)) (fun x : Fin 4 → ℝ => ((1+‖x‖)^100)⁻¹) hR
  simpa only [Module.finrank_pi_fintype,Module.finrank_self,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul,Nat.cast_ofNat,mul_one,
    bourgainRadialWeight,inv_one,one_smul] using h

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

public  theorem bourgain_inverse_power_ratio {p q L : ℝ}
    (hp : 0 < p) (hq : 0 < q) (h : q ≤ L*p) :
    (p^100)⁻¹ ≤ L^100*(q^100)⁻¹ := by
  rw [←div_eq_mul_inv,le_div_iff₀ (pow_pos hq 100),inv_mul_eq_div,
    div_le_iff₀ (pow_pos hp 100)]
  simpa only [mul_pow] using pow_le_pow_left₀ hq.le h 100

private theorem bourgain_scalar_weight_product {K R X A B : ℝ}
    (hK : 0 < K) (hKR : K ≤ R) (hX : 0 ≤ X) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (htriangle : X ≤ A+B) :
    ((1+A/K)^100)⁻¹*((1+B/R)^100)⁻¹ ≤
      (4:ℝ)^100*((1+X/R)^100)⁻¹*
        (((1+A/K)^100)⁻¹+(K/R)^4*((1+B/R)^100)⁻¹) := by
  have hR : 0 < R := hK.trans_le hKR
  have hp : 0 < 1+A/K := by positivity
  have hq : 0 < 1+B/R := by positivity
  have hr : 0 < 1+X/R := by positivity
  have hratio₀ : 0 ≤ K/R := by positivity
  have hratio₁ : K/R ≤ 1 := (div_le_one hR).mpr hKR
  have hW : ((1+B/R)^100)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [div_nonneg hB hR.le]))
  have hfirst (hh : ((1+B/R)^100)⁻¹ ≤ (4:ℝ)^100*((1+X/R)^100)⁻¹) :
      ((1+A/K)^100)⁻¹*((1+B/R)^100)⁻¹ ≤
        (4:ℝ)^100*((1+X/R)^100)⁻¹*
          (((1+A/K)^100)⁻¹+(K/R)^4*((1+B/R)^100)⁻¹) := by
    calc
      _ ≤ ((1+A/K)^100)⁻¹*((4:ℝ)^100*((1+X/R)^100)⁻¹) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = (4:ℝ)^100*((1+X/R)^100)⁻¹*((1+A/K)^100)⁻¹ := by ac_rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity)
  by_cases hXB : X ≤ 2*B
  · have hdiv : X/R ≤ 2*(B/R) := by
      calc
        _ ≤ (2*B)/R := div_le_div_of_nonneg_right hXB hR.le
        _ = _ := by ring
    apply hfirst
    have hh := bourgain_inverse_power_ratio hq hr
      (show 1+X/R ≤ 4*(1+B/R) by nlinarith [div_nonneg hB hR.le])
    exact hh
  by_cases hXR : X ≤ R
  · have hxdiv : X/R ≤ 1 := (div_le_one hR).mpr hXR
    have hh := bourgain_inverse_power_ratio (by norm_num : (0:ℝ)<1) hr
      (show 1+X/R ≤ (4:ℝ)*1 by linarith)
    simp only [one_pow,inv_one] at hh
    exact hfirst (hW.trans hh)
  have hXA : X ≤ 2*A := by linarith
  have hden : 1+X/R ≤ (4*K/R)*(1+A/K) := by
    have he : (4*K/R)*(1+A/K) = (4*K+4*A)/R := by field_simp
    rw [he]
    apply (le_div_iff₀ hR).mpr
    rw [add_mul,one_mul,div_mul_cancel₀ _ hR.ne']
    linarith
  have hh := bourgain_inverse_power_ratio hp hr hden
  have hpow : (K/R)^100 ≤ (K/R)^4 := by
    rw [show (100:ℕ)=4+96 by omega,pow_add]
    have h := pow_le_one₀ hratio₀ hratio₁ (n:=96)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left h (pow_nonneg hratio₀ 4)
  have hlast : ((1+A/K)^100)⁻¹ ≤ (4:ℝ)^100*(K/R)^4*((1+X/R)^100)⁻¹ := by
    calc
      _ ≤ _ := hh
      _ = (4:ℝ)^100*(K/R)^100*((1+X/R)^100)⁻¹ := by
        rw [show 4*K/R=4*(K/R) by ring,mul_pow]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
  calc
    _ ≤ ((4:ℝ)^100*(K/R)^4*((1+X/R)^100)⁻¹)*((1+B/R)^100)⁻¹ :=
      mul_le_mul_of_nonneg_right hlast (by positivity)
    _ = (4:ℝ)^100*((1+X/R)^100)⁻¹*((K/R)^4*((1+B/R)^100)⁻¹) := by ac_rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity)

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem bourgainRadialWeight_product {K R : ℝ}
    (hK : 0 < K) (hKR : K ≤ R) (x y : Fin 4 → ℝ) :
    bourgainRadialWeight K y*bourgainRadialWeight R (x-y) ≤
      (4:ℝ)^100*bourgainRadialWeight R x*
        (bourgainRadialWeight K y+(K/R)^4*bourgainRadialWeight R (x-y)) := by
  have hR : 0 < R := hK.trans_le hKR
  have ht : ‖x‖ ≤ ‖y‖+‖x-y‖ := by
    calc
      _ = ‖y+(x-y)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  simpa only [bourgainRadialWeight_distance hK,bourgainRadialWeight_distance hR] using
    bourgain_scalar_weight_product hK hKR (norm_nonneg x) (norm_nonneg y)
      (norm_nonneg (x-y)) ht

private theorem exists_bourgainRadialWeight_convolution :
    ∃ C > (0:ℝ), ∀ K R : ℝ, 0 < K → K ≤ R → ∀ x : Fin 4 → ℝ,
      (∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*bourgainRadialWeight R (x-y)) ≤
        C*K^4*bourgainRadialWeight R x := by
  let M := ∫ y : Fin 4 → ℝ, bourgainRadialWeight 1 y
  have hM : 0 ≤ M := integral_nonneg (bourgainRadialWeight_nonneg 1)
  refine ⟨2*(4:ℝ)^100*(M+1),by positivity,?_⟩
  intro K R hK hKR x
  have hR : 0 < R := hK.trans_le hKR
  have hiK : Integrable (bourgainRadialWeight K) := integrable_bourgainCurveCellWeight hK
  have hiR : Integrable (bourgainRadialWeight R) := integrable_bourgainCurveCellWeight hR
  have hiShift := hiR.comp_sub_left x
  have hiProd : Integrable (fun y : Fin 4 → ℝ =>
      bourgainRadialWeight K y*bourgainRadialWeight R (x-y)) :=
    hiK.mul_bdd ((continuous_bourgainRadialWeight R).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_eq_abs,abs_of_nonneg (bourgainRadialWeight_nonneg _ _)]
        exact bourgainRadialWeight_le_one _ _))
  have hm := integral_mono hiProd
    ((hiK.add (hiShift.const_mul ((K/R)^4))).const_mul
      ((4:ℝ)^100*bourgainRadialWeight R x))
    (bourgainRadialWeight_product hK hKR x)
  simp only [Pi.add_apply] at hm
  rw [integral_const_mul,integral_add hiK (hiShift.const_mul ((K/R)^4)),
    integral_const_mul,integral_sub_left_eq_self _ volume x,
    integral_bourgainRadialWeight hK.le,integral_bourgainRadialWeight hR.le] at hm
  have he : (K/R)^4*R^4 = K^4 := by
    rw [←mul_pow,div_mul_cancel₀ _ hR.ne']
  calc
    _ ≤ _ := hm
    _ = 2*(4:ℝ)^100*M*K^4*bourgainRadialWeight R x := by
      rw [←mul_assoc ((K/R)^4) (R^4) M,he]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (bourgainRadialWeight_nonneg _ _)
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hK.le 4)
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (by positivity)

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem exists_bourgainRadialWeight_shift_average :
    ∃ C > (0:ℝ), ∀ K R : ℝ, 0 < K → K ≤ R →
      ∀ (f : (Fin 4 → ℝ) → ℝ) (M : ℝ), Continuous f →
      (∀ x, 0 ≤ f x) → (∀ x, ‖f x‖ ≤ M) →
      (∫ z : Fin 4 → ℝ, bourgainRadialWeight K z*
        (∫ x : Fin 4 → ℝ, bourgainRadialWeight R x*f (x+z))) ≤
        C*K^4*(∫ x : Fin 4 → ℝ, bourgainRadialWeight R x*f x) := by
  obtain ⟨C,hC,hconv⟩ := exists_bourgainRadialWeight_convolution
  refine ⟨C,hC,?_⟩
  intro K R hK hKR f M hf hf₀ hfM
  have hR : 0 < R := hK.trans_le hKR
  have hiK : Integrable (bourgainRadialWeight K) := integrable_bourgainCurveCellWeight hK
  have hiR : Integrable (bourgainRadialWeight R) := integrable_bourgainCurveCellWeight hR
  have hiBase : Integrable (fun q : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      bourgainRadialWeight K q.1*bourgainRadialWeight R (q.2-q.1)) (volume.prod volume) := by
    have h := (measurePreserving_prod_neg_add
      (volume : Measure (Fin 4 → ℝ)) (volume : Measure (Fin 4 → ℝ))).integrable_comp_of_integrable
        (hiK.mul_prod hiR)
    simpa only [Function.comp_def,sub_eq_add_neg,add_comm] using h
  have hiH : Integrable (fun q : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      bourgainRadialWeight K q.1*bourgainRadialWeight R (q.2-q.1)*f q.2)
      (volume.prod volume) :=
    hiBase.mul_bdd (hf.comp continuous_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun q => hfM q.2))
  have he (z : Fin 4 → ℝ) :
      (∫ x : Fin 4 → ℝ, bourgainRadialWeight R x*f (x+z)) =
        ∫ y : Fin 4 → ℝ, bourgainRadialWeight R (y-z)*f y := by
    calc
      _ = ∫ x : Fin 4 → ℝ, bourgainRadialWeight R ((x+z)-z)*f (x+z) := by
        simp only [add_sub_cancel_right]
      _ = _ := integral_add_right_eq_self
        (fun y : Fin 4 → ℝ => bourgainRadialWeight R (y-z)*f y) z
  have hiLeft : Integrable (fun y : Fin 4 → ℝ =>
      (∫ z : Fin 4 → ℝ, bourgainRadialWeight K z*bourgainRadialWeight R (y-z))*f y) := by
    simpa only [integral_mul_const] using hiH.integral_prod_right
  have hiRight := (hiR.mul_bdd hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hfM)).const_mul (C*K^4)
  have hm := integral_mono hiLeft hiRight (fun y => by
    have h := mul_le_mul_of_nonneg_right (hconv K R hK hKR y) (hf₀ y)
    simpa only [mul_assoc] using h)
  rw [integral_const_mul] at hm
  calc
    _ = ∫ z : Fin 4 → ℝ, ∫ y : Fin 4 → ℝ,
        bourgainRadialWeight K z*bourgainRadialWeight R (y-z)*f y := by
      apply integral_congr_ae
      filter_upwards with z
      rw [he,←integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      ring
    _ = ∫ y : Fin 4 → ℝ, ∫ z : Fin 4 → ℝ,
        bourgainRadialWeight K z*bourgainRadialWeight R (y-z)*f y :=
      integral_integral_swap hiH
    _ = ∫ y : Fin 4 → ℝ,
        (∫ z : Fin 4 → ℝ, bourgainRadialWeight K z*bourgainRadialWeight R (y-z))*f y := by
      simp only [integral_mul_const]
    _ ≤ _ := hm

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

                                                                        
                                                                 
end TaoTrudgianYang2025
noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
private theorem bourgain_modulation_envelope_general {L : ℝ} (hL : 0 < L) (ξ : ℝ) :
    ((1+|ξ|)^102)⁻¹*(1+|ξ|/L)^100 ≤
      (1+L⁻¹)^100*(1+ξ^2)⁻¹ := by
  have hbase : 1+|ξ|/L ≤ (1+L⁻¹)*(1+|ξ|) := by
    rw [div_eq_mul_inv]
    nlinarith [inv_pos.mpr hL,abs_nonneg ξ]
  have hp := pow_le_pow_left₀ (by positivity) hbase 100
  rw [mul_pow] at hp
  have henv := bourgain_modulation_envelope (R:=1) (by norm_num) ξ
  simp only [div_one] at henv
  calc
    _ ≤ ((1+|ξ|)^102)⁻¹*((1+L⁻¹)^100*(1+|ξ|)^100) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (1+L⁻¹)^100*(((1+|ξ|)^102)⁻¹*(1+|ξ|)^100) := by ac_rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left henv (by positivity)

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025
universe u

set_option maxHeartbeats 400000 in
private theorem exists_bourgainQuartic_cell_return_quantitative :
    ∃ C > (0:ℝ), ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ),
      (∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1) →
      ∀ (a c δ R : ℝ), |a| ≤ 1 → |c| ≤ 1 → 0 < δ → δ ≤ 1 →
      0 < R → 5*R*δ^3 ≤ 1 →
      (∫ p : ℝ × ℝ, parabolaSourceWeight R 0 0 p.1 p.2*
        ‖∑ i ∈ S, z i*fordAdditiveCharacter
          ((c+δ*s i-a)*p.1+(c+δ*s i-a)^2*p.2)‖^6) ≤
        C*(1+(δ*R)⁻¹)^100/R^2*(∫ x : Fin 4 → ℝ, ((1+‖R⁻¹ • x‖)^100)⁻¹*
          bourgainCurveCellMoment S z (fun i => c+δ*s i) x) := by
  obtain ⟨E,hE,hInv⟩ := exists_bourgainCurveCell_inverse_pointwise.{u}
  refine ⟨E*(32:ℝ)^100*Real.pi/4,by positivity,?_⟩
  intro ι S z s hs a c δ R ha hc hδ hδ₁ hR hrem
  let u := fun i => c+δ*s i
  let T := fun (ξ : ℝ) (y : Fin 4 → ℝ) =>
    (bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0]
  let W := fun ξ : ℝ => ((1+|ξ|)^102)⁻¹
  let P := fun p : ℝ × ℝ => ‖∑ i ∈ S, z i*fordAdditiveCharacter
    ((u i-a)*p.1+(u i-a)^2*p.2)‖^6
  let F := fun y : Fin 4 → ℝ => bourgainCurveCellBaseWeight R y*P (y 0,y 1)
  let H := fun (ξ : ℝ) (y : Fin 4 → ℝ) =>
    W ξ*bourgainCurveCellBaseWeight R y*bourgainCurveCellMoment S z u (T ξ y)
  let J := ∫ x : Fin 4 → ℝ, ((1+‖R⁻¹ • x‖)^100)⁻¹*bourgainCurveCellMoment S z u x
  let L := (1+(δ*R)⁻¹)^100
  have hJ : 0 ≤ J := integral_nonneg (fun x => by
    apply mul_nonneg (by positivity)
    unfold bourgainCurveCellMoment
    positivity)
  have hPc : Continuous P := by
    unfold P fordAdditiveCharacter
    fun_prop
  have hPb (p : ℝ × ℝ) : ‖P p‖ ≤ (∑ i ∈ S, ‖z i‖)^6 :=
    bourgain_character_six_bound S z (fun i => (u i-a)*p.1+(u i-a)^2*p.2)
  have hiF : Integrable F :=
    (integrable_bourgainCurveCellBaseWeight hR).mul_bdd
      (hPc.comp (by fun_prop)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => hPb (y 0,y 1)))
  have hcFrame : Continuous ((bourgainCurveCellFrame a c).mulVec) := by
    change Continuous (Matrix.toLin' (bourgainCurveCellFrame a c))
    exact LinearMap.continuous_on_pi _
  have hcT : Continuous (fun q : ℝ × (Fin 4 → ℝ) => T q.1 q.2) := by
    exact (hcFrame.comp continuous_snd).add (by dsimp [T]; fun_prop)
  have hcM : Continuous (fun q : ℝ × (Fin 4 → ℝ) =>
      bourgainCurveCellMoment S z u (T q.1 q.2)) :=
    (continuous_bourgainCurveCellMoment S z u).comp hcT
  have hiH : Integrable (Function.uncurry H) (volume.prod volume) := by
    have hp := bourgainRemainderEnvelope_integrable.mul_prod
      (integrable_bourgainCurveCellBaseWeight hR)
    exact hp.mul_bdd hcM.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun q => bourgain_character_six_bound S z
        (fun i => T q.1 q.2 0*u i+T q.1 q.2 1*(u i)^2+
          T q.1 q.2 2*(u i)^3+T q.1 q.2 3*(u i)^4)))
  have hp (y : Fin 4 → ℝ) : F y ≤ E*(∫ ξ : ℝ, H ξ y) := by
    by_cases hy : (y 2,y 3) ∈ Icc (-R) R ×ˢ Icc (-R) R
    · have hm := hInv S z s hs a c δ R hc hδ.le hδ₁ hR.le hrem y
        (abs_le.mpr hy.1) (abs_le.mpr hy.2)
      have he (ξ : ℝ) := bourgainCurveCellMoment_shift S z s c ξ hδ.ne'
        ((bourgainCurveCellFrame a c).mulVec y)
      have hmi : P (y 0,y 1) ≤ E*(∫ ξ : ℝ, W ξ*bourgainCurveCellMoment S z u (T ξ y)) := by
        simpa only [P,W,u,T,he] using hm
      have hm' := mul_le_mul_of_nonneg_left hmi (bourgainCurveCellBaseWeight_nonneg R y)
      have heH : (∫ ξ : ℝ, H ξ y) = bourgainCurveCellBaseWeight R y*
          (∫ ξ : ℝ, W ξ*bourgainCurveCellMoment S z u (T ξ y)) := by
        rw [←integral_const_mul]
        apply integral_congr_ae
        filter_upwards with ξ
        dsimp [H]
        ring
      rw [heH]
      simpa only [F,mul_left_comm] using hm'
    · simp only [F,H,bourgainCurveCellBaseWeight,Set.indicator_of_notMem hy,
        mul_zero,zero_mul,integral_zero,le_refl]
  have hmain := bourgain_kernel_setIntegral_bound
    (α:=Fin 4 → ℝ) (β:=ℝ) (μ:=volume) (ν:=volume)
    (B:=Set.univ) (C:=E) (f:=F) (H:=H)
    MeasurableSet.univ hiF.integrableOn
    (by simpa only [Measure.restrict_univ] using hiH) (fun y _ => hp y)
  simp only [setIntegral_univ] at hmain

  have hinner (ξ : ℝ) : (∫ y : Fin 4 → ℝ, H ξ y) ≤
      (32:ℝ)^100*J*L*(1+ξ^2)⁻¹ := by
    have hb := bourgainCurveCell_inner_bound S z u ha hc hR hδ ξ
    have heH : (∫ y : Fin 4 → ℝ, H ξ y) =
        W ξ*(∫ y : Fin 4 → ℝ, bourgainCurveCellBaseWeight R y*
          bourgainCurveCellMoment S z u (T ξ y)) := by
      simp only [H,mul_assoc,integral_const_mul]
    rw [heH]
    calc
      _ ≤ W ξ*((32:ℝ)^100*(1+|ξ|/(δ*R))^100*J) :=
        mul_le_mul_of_nonneg_left hb (by dsimp [W]; positivity)
      _ = (32:ℝ)^100*J*(W ξ*(1+|ξ|/(δ*R))^100) := by ring
      _ ≤ (32:ℝ)^100*J*(L*(1+ξ^2)⁻¹) :=
        mul_le_mul_of_nonneg_left (bourgain_modulation_envelope_general (mul_pos hδ hR) ξ)
          (mul_nonneg (by positivity) hJ)
      _ = _ := by ring
  have hiOuter : Integrable (fun ξ : ℝ => ∫ y : Fin 4 → ℝ, H ξ y) :=
    hiH.integral_prod_left
  have hout := integral_mono hiOuter
    (integrable_inv_one_add_sq.const_mul ((32:ℝ)^100*J*L)) hinner
  rw [integral_const_mul,integral_univ_inv_one_add_sq] at hout
  have hleft : (∫ y : Fin 4 → ℝ, F y) =
      4*R^2*(∫ p : ℝ × ℝ, parabolaSourceWeight R 0 0 p.1 p.2*P p) := by
    calc
      _ = ∫ y : Fin 4 → ℝ,
          (parabolaSourceWeight R 0 0 (y 0) (y 1)*P (y 0,y 1))*
            (Icc (-R) R ×ˢ Icc (-R) R).indicator (fun _ : ℝ × ℝ => (1:ℝ)) (y 2,y 3) := by
        apply integral_congr_ae
        filter_upwards with y
        dsimp [F,bourgainCurveCellBaseWeight]
        ring
      _ = (∫ p : ℝ × ℝ, parabolaSourceWeight R 0 0 p.1 p.2*P p)*
          (∫ q : ℝ × ℝ, (Icc (-R) R ×ˢ Icc (-R) R).indicator
            (fun _ : ℝ × ℝ => (1:ℝ)) q) :=
        bourgainFourCoordinates_integral_product
          (fun p : ℝ × ℝ => parabolaSourceWeight R 0 0 p.1 p.2*P p)
          ((Icc (-R) R ×ˢ Icc (-R) R).indicator (fun _ : ℝ × ℝ => (1:ℝ)))
      _ = _ := by rw [bourgainCurveCell_transverse_mass hR.le]; ring
  rw [hleft] at hmain
  have hfinal := hmain.trans (mul_le_mul_of_nonneg_left hout hE.le)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
  change (∫ p : ℝ × ℝ, parabolaSourceWeight R 0 0 p.1 p.2*P p)*R^2 ≤
    (E*(32:ℝ)^100*Real.pi/4)*L*J
  nlinarith only [hfinal]

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private theorem exists_bourgainSourceCurve_cell_return_quantitative :
    ∃ C > (0:ℝ), ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ),
      (∀ i ∈ S, 0 ≤ w i) →
      ∀ (a c δ R : ℝ), |a| ≤ 1 → |c| ≤ 1 → 0 < δ → δ ≤ 1 →
      0 < R → 5*R*δ^3 ≤ 1 →
      (∀ i ∈ S, |Real.sqrt (w i)-c| ≤ δ) →
      (∫ p : ℝ × ℝ, parabolaSourceWeight R 0 0 p.1 p.2*
        ‖∑ i ∈ S, z i*fordAdditiveCharacter
          ((Real.sqrt (w i)-a)*p.1+(Real.sqrt (w i)-a)^2*p.2)‖^6) ≤
        C*(1+(δ*R)⁻¹)^100/R^2*(∫ x : Fin 4 → ℝ, ((1+‖R⁻¹ • x‖)^100)⁻¹*
          ‖∑ i ∈ S, z i*fordAdditiveCharacter
            (x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))‖^6) := by
  obtain ⟨C,hC,h⟩ := exists_bourgainQuartic_cell_return_quantitative.{u}
  refine ⟨C,hC,?_⟩
  intro ι S z w hw a c δ R ha hc hδ hδ₁ hR hrem hwindow
  let s := fun i => (Real.sqrt (w i)-c)/δ
  have hs : ∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1 := by
    intro i hi
    have hh := abs_le.mp (hwindow i hi)
    constructor
    · apply (le_div_iff₀ hδ).mpr
      linarith [hh.1]
    · apply (div_le_iff₀ hδ).mpr
      linarith [hh.2]
  have hbase (i : ι) : c+δ*s i = Real.sqrt (w i) := by
    dsimp [s]
    field_simp
    ring
  have hmain := h S z s hs a c δ R ha hc hδ hδ₁ hR hrem
  simp_rw [hbase] at hmain
  let f := fun x : Fin 4 → ℝ => ((1+‖R⁻¹ • x‖)^100)⁻¹*
    bourgainCurveCellMoment S z (fun i => Real.sqrt (w i)) x
  have he : (∫ x : Fin 4 → ℝ, f x) =
      ∫ x : Fin 4 → ℝ, ((1+‖R⁻¹ • x‖)^100)⁻¹*
        ‖∑ i ∈ S, z i*fordAdditiveCharacter
          (x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))‖^6 := by
    calc
      _ = ∫ x : Fin 4 → ℝ, f (bourgainSourcePermutation x) :=
        (bourgainSourcePermutation_measurePreserving.integral_comp
          bourgainSourcePermutation.measurableEmbedding f).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp only [f]
        rw [norm_smul,bourgainSourcePermutation_norm,←norm_smul]
        apply congrArg (fun v : ℝ => ((1+‖R⁻¹ • x‖)^100)⁻¹*v)
        unfold bourgainCurveCellMoment
        apply congrArg (fun v : ℂ => ‖v‖^6)
        apply Finset.sum_congr rfl
        intro i hi
        apply congrArg (fun v : ℝ => z i*fordAdditiveCharacter v)
        simpa only [bourgainSourcePermutation_apply,Matrix.cons_val_zero,
          Matrix.cons_val_one,Matrix.cons_val] using
          (bourgain_source_quartic_phase (hw i hi) x).symm
  change _ ≤ C*(1+(δ*R)⁻¹)^100/R^2*(∫ x : Fin 4 → ℝ, f x) at hmain
  rw [he] at hmain
  exact hmain

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private theorem exists_bourgainParabola_unit_average :
    ∃ C > (0:ℝ), ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ),
      (∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
        parabolaBoxBilinearMoment S S
          (fun i => z i*fordAdditiveCharacter (ξ*x i))
          (fun i => z i*fordAdditiveCharacter (ξ*x i)) x x 1 0 0) ≤
        C*(∫ p : ℝ × ℝ, parabolaSourceWeight 1 0 0 p.1 p.2*
          ‖∑ i ∈ S, z i*fordAdditiveCharacter (x i*p.1+(x i)^2*p.2)‖^6) := by
  obtain ⟨K,hK,hcomp⟩ := parabolaRapidWeight_le_sourceWeight
  refine ⟨K*Real.pi,by positivity,?_⟩
  intro ι S z x
  let W := fun p : ℝ × ℝ => parabolaSourceWeight 1 0 0 p.1 p.2
  let J := parabolaSourceBilinearMoment S S z z x x 1 0 0
  have hW₀ : ∀ p, 0 ≤ W p := fun p => parabolaSourceWeight_nonneg _ _ _ _ _
  have hW : Integrable W := integrable_parabolaSourceWeight (by norm_num) 0 0
  have hJ : 0 ≤ J := integral_nonneg (fun p => by
    apply mul_nonneg
    · exact mul_nonneg (hW₀ p) (by positivity)
    · positivity)
  have hm (ξ : ℝ) :
      parabolaSourceBilinearMoment S S
        (fun i => z i*fordAdditiveCharacter (ξ*x i))
        (fun i => z i*fordAdditiveCharacter (ξ*x i)) x x 1 0 0 ≤
          (1+|ξ|)^100*J := by
    have hn := pow_le_pow_left₀ (sq_nonneg _)
      (parabola_sourceWeight_modulation S z x (by norm_num : (0:ℝ)<1) 0 0 ξ) 3
    rw [mul_pow,←pow_mul,←pow_mul] at hn
    have hr := Real.rpow_inv_natCast_pow
      (by positivity : (0:ℝ) ≤ (1+|ξ|/1)^100) (by norm_num : (3:ℕ) ≠ 0)
    simp only [Nat.cast_ofNat] at hr
    rw [hr] at hn
    norm_num only [show (2*3:ℕ)=6 by omega,div_one] at hn
    rw [parabolaWeightedSixNorm_pow_six W hW₀ hW,
      parabolaWeightedSixNorm_pow_six W hW₀ hW] at hn
    exact hn
  have hp (ξ : ℝ) :
      ((1+|ξ|)^102)⁻¹*parabolaBoxBilinearMoment S S
        (fun i => z i*fordAdditiveCharacter (ξ*x i))
        (fun i => z i*fordAdditiveCharacter (ξ*x i)) x x 1 0 0 ≤
          K*J*(1+ξ^2)⁻¹ := by
    have hb := (parabolaBox_le_rapid S S
      (fun i => z i*fordAdditiveCharacter (ξ*x i))
      (fun i => z i*fordAdditiveCharacter (ξ*x i)) x x (by norm_num : (0:ℝ)<1) 0 0).trans
      (parabolaRapid_le_source S S
        (fun i => z i*fordAdditiveCharacter (ξ*x i))
        (fun i => z i*fordAdditiveCharacter (ξ*x i)) x x (by norm_num : (0:ℝ)<1) hcomp 0 0)
    have he := bourgain_modulation_envelope (R:=1) (by norm_num) ξ
    simp only [div_one] at he
    calc
      _ ≤ ((1+|ξ|)^102)⁻¹*(K*((1+|ξ|)^100*J)) :=
        mul_le_mul_of_nonneg_left
          (hb.trans (mul_le_mul_of_nonneg_left (hm ξ) hK.le)) (by positivity)
      _ = K*J*(((1+|ξ|)^102)⁻¹*(1+|ξ|)^100) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left he (mul_nonneg hK.le hJ)
  have hi := integrable_bourgain_modulated_box S z x x 1 0 0
  have hh := integral_mono hi (integrable_inv_one_add_sq.const_mul (K*J)) hp
  rw [integral_const_mul,integral_univ_inv_one_add_sq] at hh
  have he (r : ℝ) : r^2*r^4=r^6 := by ring
  have hJe : J = ∫ p : ℝ × ℝ, parabolaSourceWeight 1 0 0 p.1 p.2*
      ‖∑ i ∈ S, z i*fordAdditiveCharacter (x i*p.1+(x i)^2*p.2)‖^6 := by
    simp only [J,parabolaSourceBilinearMoment,mul_assoc,he,sargosPlanarSum]
  rw [←hJe]
  exact hh.trans_eq (by ring)

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory Set
namespace TaoTrudgianYang2025

public  theorem bourgain_cube_mass {R : ℝ} (hR : 0 ≤ R) :
    volume.real (Icc (fun _ : Fin 4 => -R) (fun _ => R)) = (2*R)^4 := by
  change (volume (Icc (fun _ : Fin 4 => -R) (fun _ => R))).toReal = _
  rw [Real.volume_Icc_pi_toReal (fun _ => by linarith)]
  simp only [sub_neg_eq_add,←two_mul,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

public  theorem bourgain_finite_box_average {K R : ℝ}
    (hK : 0 ≤ K) (hKR : K ≤ R) (f : (Fin 4 → ℝ) → ℝ)
    (hfc : Continuous f) (hf₀ : ∀ x, 0 ≤ f x) :
    (2*K)^4*(∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R), f x) ≤
      ∫ q : Fin 4 → ℝ in Icc (fun _ => -(2*R)) (fun _ => 2*R),
        ∫ y : Fin 4 → ℝ in Icc (fun _ => -K) (fun _ => K), f (q+y) := by
  let B := fun r : ℝ => Icc (fun _ : Fin 4 => -r) (fun _ => r)
  have hpoint (y : Fin 4 → ℝ) (hy : y ∈ B K) :
      (∫ x in B R, f x) ≤ ∫ q in B (2*R), f (q+y) := by
    have hsub : (fun q => q+y) ⁻¹' B R ⊆ B (2*R) := by
      intro q hq
      constructor
      · intro i
        have hl := hq.1 i
        have hu := hy.2 i
        change -R ≤ q i+y i at hl
        change y i ≤ K at hu
        linarith
      · intro i
        have hu := hq.2 i
        have hl := hy.1 i
        change q i+y i ≤ R at hu
        change -K ≤ y i at hl
        linarith
    have hi : IntegrableOn (fun q => f (q+y)) (B (2*R)) :=
      ContinuousOn.integrableOn_compact isCompact_Icc
        (hfc.comp (continuous_id.add continuous_const)).continuousOn
    calc
      _ = ∫ q in (fun q => q+y) ⁻¹' B R, f (q+y) :=
        ((measurePreserving_add_right volume y).setIntegral_preimage_emb
          (Homeomorph.addRight y).measurableEmbedding f (B R)).symm
      _ ≤ _ := setIntegral_mono_set hi
        (Filter.Eventually.of_forall (fun q => hf₀ (q+y)))
        (Filter.Eventually.of_forall hsub)
  have hc : Continuous (fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) => f (p.1+p.2)) :=
    hfc.comp (continuous_fst.add continuous_snd)
  have hi : Integrable (fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) => f (p.1+p.2))
      ((volume.restrict (B (2*R))).prod (volume.restrict (B K))) := by
    rw [Measure.prod_restrict]
    exact ContinuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc) hc.continuousOn
  have hconst : IntegrableOn (fun _y : Fin 4 → ℝ => ∫ x in B R, f x) (B K) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hh := setIntegral_mono_on hconst hi.integral_prod_right measurableSet_Icc hpoint
  rw [integral_const,measureReal_restrict_apply_univ] at hh
  change volume.real (B K)*(∫ x in B R, f x) ≤ _ at hh
  rw [bourgain_cube_mass hK] at hh
  have hswap := integral_integral_swap (f:=fun q y => f (q+y)) hi
  exact hh.trans_eq hswap.symm

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

public  def bourgainSourceSixMoment {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (w : ι → ℝ) (x : Fin 4 → ℝ) : ℝ :=
  ‖∑ i ∈ S, z i*fordAdditiveCharacter
    (x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))‖^6

private theorem exists_bourgainSourceCurve_small_box :
    ∃ C > (0:ℝ), ∀ {ι τ : Type u} (S : Finset ι) (V : Finset τ)
      (z : ι → ℂ) (c : τ → ℂ) (w : ι → ℝ) (v : τ → ℝ),
      (∀ i ∈ S, 0 ≤ w i) → (∀ j ∈ V, 0 ≤ v j) →
      (∀ i ∈ S, Real.sqrt (w i) ∈ Icc 0 1) →
      (∀ j ∈ V, Real.sqrt (v j) ∈ Icc 0 1) →
      (∫ x : Fin 4 → ℝ in Icc (fun _ => -(1/10:ℝ)) (fun _ => (1/10:ℝ)),
        bourgainSourceSixMoment S z w x*bourgainSourceSixMoment V c v x) ≤
        C*(∫ x : Fin 4 → ℝ, bourgainRadialWeight 1 x*bourgainSourceSixMoment S z w x)*
          (∫ x : Fin 4 → ℝ, bourgainRadialWeight 1 x*bourgainSourceSixMoment V c v x) := by
  obtain ⟨D,hD,hframe⟩ := exists_bourgainSourceCurve_bilinear_reduction.{u}
  obtain ⟨P,hP,hpar⟩ := exists_bourgainParabola_unit_average.{u}
  obtain ⟨Q,hQ,hret⟩ := exists_bourgainSourceCurve_cell_return_quantitative.{u}
  let A := P*Q*(3:ℝ)^100
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨D*(6:ℝ)⁻¹*A^2,by positivity,?_⟩
  intro ι τ S V z c w v hw hv hs ht
  have hsingle {κ : Type u} (U : Finset κ) (d : κ → ℂ) (u : κ → ℝ)
      (hu : ∀ i ∈ U, 0 ≤ u i) (hr : ∀ i ∈ U, Real.sqrt (u i) ∈ Icc 0 1)
      (a : ℝ) (ha : |a| ≤ 1) :
      (∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
        parabolaBoxBilinearMoment U U
          (fun i => d i*fordAdditiveCharacter (ξ*(Real.sqrt (u i)-a)))
          (fun i => d i*fordAdditiveCharacter (ξ*(Real.sqrt (u i)-a)))
          (fun i => Real.sqrt (u i)-a) (fun i => Real.sqrt (u i)-a) 1 0 0) ≤
        A*(∫ x : Fin 4 → ℝ, bourgainRadialWeight 1 x*bourgainSourceSixMoment U d u x) := by
    have hb := hpar U d (fun i => Real.sqrt (u i)-a)
    have hc := hret U d u hu a (1/2) (1/2) 1 ha
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun i hi => abs_le.mpr ⟨by linarith [(hr i hi).1],by linarith [(hr i hi).2]⟩)
    rw [show (1+((1/2:ℝ)*1)⁻¹)=3 by norm_num] at hc
    simp only [one_pow,div_one] at hc
    have hh := hb.trans (mul_le_mul_of_nonneg_left hc hP.le)
    change _ ≤ A*_
    exact hh.trans_eq (by dsimp [A,bourgainRadialWeight,bourgainSourceSixMoment]; ring)
  have hS := hsingle S z w hw hs 0 (by norm_num)
  have hV := hsingle V c v hv ht 1 (by norm_num)
  have hframe' := hframe ι τ S V z c w v hw hv 0 1 1 (1/10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (fun i hi => abs_le.mpr ⟨by linarith [(hs i hi).1],by linarith [(hs i hi).2]⟩)
    (fun j hj => abs_le.mpr ⟨by linarith [(ht j hj).1],by linarith [(ht j hj).2]⟩)
  simp only [div_one,show (10:ℝ)*(1/10)=1 by norm_num,
    sub_zero,one_pow,mul_one] at hframe' hS
  have hV₀ : 0 ≤ ∫ η : ℝ, ((1+|η|)^102)⁻¹*
      parabolaBoxBilinearMoment V V
        (fun j => c j*fordAdditiveCharacter (η*(Real.sqrt (v j)-1)))
        (fun j => c j*fordAdditiveCharacter (η*(Real.sqrt (v j)-1)))
        (fun j => Real.sqrt (v j)-1) (fun j => Real.sqrt (v j)-1) 1 0 0 :=
    integral_nonneg (fun η => mul_nonneg (by positivity)
      (integral_nonneg (fun p => by positivity)))
  have hSJ₀ : 0 ≤ A*(∫ x : Fin 4 → ℝ,
      bourgainRadialWeight 1 x*bourgainSourceSixMoment S z w x) :=
    mul_nonneg hA.le (integral_nonneg (fun x =>
      mul_nonneg (bourgainRadialWeight_nonneg 1 x) (by
        unfold bourgainSourceSixMoment
        positivity)))
  have hprod := mul_le_mul hS hV hV₀ hSJ₀
  have hmain := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ D*(6:ℝ)⁻¹)
  change _ ≤ _ at hframe'
  calc
    _ ≤ _ := hframe'
    _ = D*(6:ℝ)⁻¹*(_*_) := by ring
    _ ≤ _ := hmain
    _ = _ := by ring

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory Set
namespace TaoTrudgianYang2025

private theorem bourgainRadialWeight_translate_large {R : ℝ}
    (hR : 1 ≤ R) {q : Fin 4 → ℝ} (hq : ‖q‖ ≤ 2*R) (x : Fin 4 → ℝ) :
    bourgainRadialWeight 1 (x-q) ≤ (2:ℝ)^100*bourgainRadialWeight (20*R) x := by
  have hR₀ : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have h20 : 0 < 20*R := by positivity
  rw [bourgainRadialWeight_distance (by norm_num : (0:ℝ)<1),
    bourgainRadialWeight_distance h20,div_one]
  apply bourgain_inverse_power_ratio (by positivity) (by positivity)
  have hn : ‖x‖ ≤ ‖x-q‖+2*R := by
    calc
      _ = ‖(x-q)+q‖ := by rw [sub_add_cancel]
      _ ≤ ‖x-q‖+‖q‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hd : ‖x‖/(20*R) ≤ 1+‖x-q‖ := by
    apply (div_le_iff₀ h20).mpr
    nlinarith [norm_nonneg (x-q),mul_nonneg (sub_nonneg.mpr hR) (norm_nonneg (x-q))]
  linarith [norm_nonneg (x-q)]

private theorem bourgainRadialWeight_translated_integral {R : ℝ}
    (hR : 1 ≤ R) {q : Fin 4 → ℝ} (hq : ‖q‖ ≤ 2*R)
    (f : (Fin 4 → ℝ) → ℝ) (M : ℝ) (hc : Continuous f)
    (h₀ : ∀ x, 0 ≤ f x) (hb : ∀ x, ‖f x‖ ≤ M) :
    (∫ x : Fin 4 → ℝ, bourgainRadialWeight 1 x*f (x+q)) ≤
      (2:ℝ)^100*(∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*f x) := by
  have hR₀ : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hw1 : Integrable (bourgainRadialWeight 1) :=
    integrable_bourgainCurveCellWeight (by norm_num)
  have hwR : Integrable (bourgainRadialWeight (20*R)) :=
    integrable_bourgainCurveCellWeight (by positivity)
  have hi1 := (hw1.comp_sub_right q).mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)
  have hiR := hwR.mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)
  have hh := integral_mono hi1 (hiR.const_mul ((2:ℝ)^100))
    (fun x => (mul_le_mul_of_nonneg_right
      (bourgainRadialWeight_translate_large hR hq x) (h₀ x)).trans_eq (by ring))
  rw [integral_const_mul] at hh
  calc
    _ = ∫ x : Fin 4 → ℝ, bourgainRadialWeight 1 (x-q)*f x := by
      have he := integral_add_right_eq_self (μ:=volume)
        (fun x : Fin 4 → ℝ => bourgainRadialWeight 1 (x-q)*f x) q
      simpa only [add_sub_cancel_right] using he
    _ ≤ _ := hh

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

public  theorem bourgainSourceSixMoment_nonneg {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ) (x : Fin 4 → ℝ) :
    0 ≤ bourgainSourceSixMoment S z w x := by
  unfold bourgainSourceSixMoment
  positivity

public  theorem continuous_bourgainSourceSixMoment {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ) :
    Continuous (bourgainSourceSixMoment S z w) := by
  unfold bourgainSourceSixMoment fordAdditiveCharacter
  fun_prop

public  theorem bourgainSourceSixMoment_translate {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ) (q x : Fin 4 → ℝ) :
    bourgainSourceSixMoment S (fun i => z i*fordAdditiveCharacter
      (q 0*w i+q 1*(w i)^2+q 2*(w i)^((3:ℝ)/2)+q 3*Real.sqrt (w i))) w x =
        bourgainSourceSixMoment S z w (x+q) := by
  unfold bourgainSourceSixMoment
  apply congrArg (fun v : ℂ => ‖v‖^6)
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc,←fordAdditiveCharacter_add]
  apply congrArg (fun v : ℝ => z i*fordAdditiveCharacter v)
  simp only [Pi.add_apply]
  ring

private theorem exists_bourgainSourceCurve_box_base :
    ∃ C > (0:ℝ), ∀ R : ℝ, 1 ≤ R →
      ∀ {ι τ : Type u} (S : Finset ι) (V : Finset τ)
        (z : ι → ℂ) (c : τ → ℂ) (w : ι → ℝ) (v : τ → ℝ),
        (∀ i ∈ S, 0 ≤ w i) → (∀ j ∈ V, 0 ≤ v j) →
        (∀ i ∈ S, Real.sqrt (w i) ∈ Icc 0 1) →
        (∀ j ∈ V, Real.sqrt (v j) ∈ Icc 0 1) →
        (∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
          bourgainSourceSixMoment S z w x*bourgainSourceSixMoment V c v x) ≤
          C*R^4*(∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*
            bourgainSourceSixMoment S z w x)*
            (∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*
              bourgainSourceSixMoment V c v x) := by
  obtain ⟨D,hD,hsmall⟩ := exists_bourgainSourceCurve_small_box.{u}
  refine ⟨D*(2:ℝ)^200*20^4,by positivity,?_⟩
  intro R hR ι τ S V z c w v hw hv hs ht
  let B := fun r : ℝ => Icc (fun _ : Fin 4 => -r) (fun _ => r)
  let F := fun x : Fin 4 → ℝ => bourgainSourceSixMoment S z w x*bourgainSourceSixMoment V c v x
  let JS := ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*bourgainSourceSixMoment S z w x
  let JV := ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*bourgainSourceSixMoment V c v x
  have hJS : 0 ≤ JS := integral_nonneg (fun x =>
    mul_nonneg (bourgainRadialWeight_nonneg _ _) (bourgainSourceSixMoment_nonneg _ _ _ _))
  have hJV : 0 ≤ JV := integral_nonneg (fun x =>
    mul_nonneg (bourgainRadialWeight_nonneg _ _) (bourgainSourceSixMoment_nonneg _ _ _ _))
  have hFc : Continuous F :=
    (continuous_bourgainSourceSixMoment S z w).mul (continuous_bourgainSourceSixMoment V c v)
  have hF₀ (x : Fin 4 → ℝ) : 0 ≤ F x :=
    mul_nonneg (bourgainSourceSixMoment_nonneg _ _ _ _) (bourgainSourceSixMoment_nonneg _ _ _ _)
  have havg := bourgain_finite_box_average (K:=1/10) (R:=R)
    (by norm_num) (by linarith) F hFc hF₀
  have hpoint (q : Fin 4 → ℝ) (hq : q ∈ B (2*R)) :
      (∫ y in B (1/10), F (q+y)) ≤ D*(2:ℝ)^200*JS*JV := by
    have hqnorm : ‖q‖ ≤ 2*R := (pi_norm_le_iff_of_nonneg (by linarith)).mpr
      (fun i => by rw [Real.norm_eq_abs]; exact abs_le.mpr ⟨hq.1 i,hq.2 i⟩)
    have hmoment {κ : Type u} (U : Finset κ) (d : κ → ℂ) (u : κ → ℝ) :
        (∫ x : Fin 4 → ℝ, bourgainRadialWeight 1 x*
          bourgainSourceSixMoment U (fun i => d i*fordAdditiveCharacter
            (q 0*u i+q 1*(u i)^2+q 2*(u i)^((3:ℝ)/2)+q 3*Real.sqrt (u i))) u x) ≤
          (2:ℝ)^100*(∫ x : Fin 4 → ℝ,
            bourgainRadialWeight (20*R) x*bourgainSourceSixMoment U d u x) := by
      simp_rw [bourgainSourceSixMoment_translate]
      exact bourgainRadialWeight_translated_integral hR hqnorm
        (bourgainSourceSixMoment U d u) ((∑ i ∈ U, ‖d i‖)^6)
        (continuous_bourgainSourceSixMoment U d u)
        (bourgainSourceSixMoment_nonneg U d u)
        (fun x => bourgain_character_six_bound U d
          (fun i => x 0*u i+x 1*(u i)^2+x 2*(u i)^((3:ℝ)/2)+x 3*Real.sqrt (u i)))
    have hlocal := hsmall S V
      (fun i => z i*fordAdditiveCharacter
        (q 0*w i+q 1*(w i)^2+q 2*(w i)^((3:ℝ)/2)+q 3*Real.sqrt (w i)))
      (fun j => c j*fordAdditiveCharacter
        (q 0*v j+q 1*(v j)^2+q 2*(v j)^((3:ℝ)/2)+q 3*Real.sqrt (v j)))
      w v hw hv hs ht
    have hmS := hmoment S z w
    have hmV := hmoment V c v
    have hleft : (∫ y in B (1/10), F (q+y)) =
        ∫ y in B (1/10),
          bourgainSourceSixMoment S (fun i => z i*fordAdditiveCharacter
            (q 0*w i+q 1*(w i)^2+q 2*(w i)^((3:ℝ)/2)+q 3*Real.sqrt (w i))) w y*
          bourgainSourceSixMoment V (fun j => c j*fordAdditiveCharacter
            (q 0*v j+q 1*(v j)^2+q 2*(v j)^((3:ℝ)/2)+q 3*Real.sqrt (v j))) v y := by
      simp only [bourgainSourceSixMoment_translate,F,add_comm]
    rw [hleft]
    refine hlocal.trans ?_
    have hh := mul_le_mul hmS hmV
      (integral_nonneg (fun x => mul_nonneg (bourgainRadialWeight_nonneg _ _)
        (bourgainSourceSixMoment_nonneg _ _ _ _)))
      (mul_nonneg (by positivity) hJS)
    have hh' := mul_le_mul_of_nonneg_left hh hD.le
    change D*_ * _ ≤ D*(2:ℝ)^200*JS*JV
    calc
      _ = D*(_*_) := by ring
      _ ≤ D*(((2:ℝ)^100*JS)*((2:ℝ)^100*JV)) := hh'
      _ = _ := by ring
  have hi : Integrable (fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) => F (p.1+p.2))
      ((volume.restrict (B (2*R))).prod (volume.restrict (B (1/10)))) := by
    rw [Measure.prod_restrict]
    exact ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      (hFc.comp (continuous_fst.add continuous_snd)).continuousOn
  have hconst : IntegrableOn (fun _q : Fin 4 → ℝ => D*(2:ℝ)^200*JS*JV) (B (2*R)) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hh := setIntegral_mono_on hi.integral_prod_left hconst measurableSet_Icc hpoint
  rw [integral_const,measureReal_restrict_apply_univ] at hh
  change _ ≤ volume.real (B (2*R))*(D*(2:ℝ)^200*JS*JV) at hh
  rw [bourgain_cube_mass (by linarith : 0 ≤ 2*R)] at hh
  have hfinal := havg.trans hh
  apply (mul_le_mul_iff_right₀ (by norm_num : (0:ℝ)<(2*(1/10:ℝ))^4)).mp
  change (2*(1/10:ℝ))^4*(∫ x in B R, F x) ≤
    (2*(1/10:ℝ))^4*((D*(2:ℝ)^200*20^4)*R^4*JS*JV)
  exact hfinal.trans_eq (by ring)

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

public  theorem integrable_bourgainSource_weighted {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ) {R : ℝ} (hR : 0 < R) :
    Integrable (fun x : Fin 4 → ℝ => bourgainRadialWeight R x*bourgainSourceSixMoment S z w x) :=
  (integrable_bourgainCurveCellWeight hR).mul_bdd
    (continuous_bourgainSourceSixMoment S z w).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => bourgain_character_six_bound S z
      (fun i => x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))))

private theorem bourgainSourceSixMoment_finite_sum {N : ℕ} {ι : Type*}
    (S : Fin N → Finset ι) (z : Fin N → ι → ℂ) (w : Fin N → ι → ℝ)
    (x : Fin 4 → ℝ) :
    bourgainSourceSixMoment (Finset.univ.sigma S) (fun ji => z ji.1 ji.2)
      (fun ji => w ji.1 ji.2) x ≤
        (N:ℝ)^5*∑ j, bourgainSourceSixMoment (S j) (z j) (w j) x := by
  let A := fun j : Fin N => ∑ i ∈ S j, z j i*fordAdditiveCharacter
    (x 0*w j i+x 1*(w j i)^2+x 2*(w j i)^((3:ℝ)/2)+x 3*Real.sqrt (w j i))
  have hn := pow_le_pow_left₀ (norm_nonneg (∑ j, A j)) (norm_sum_le Finset.univ A) 6
  have hh := pow_sum_le_card_mul_sum_pow (s:=Finset.univ)
    (f:=fun j => ‖A j‖) (fun _ _ => norm_nonneg _) 5
  simp only [show (5+1:ℕ)=6 by omega,Finset.card_univ,Fintype.card_fin] at hh
  simpa only [bourgainSourceSixMoment,Finset.sum_sigma,A] using hn.trans hh

private theorem bourgainSource_weighted_finite_sum {N : ℕ} {ι : Type*}
    (S : Fin N → Finset ι) (z : Fin N → ι → ℂ) (w : Fin N → ι → ℝ)
    {R : ℝ} (hR : 0 < R) :
    (∫ x : Fin 4 → ℝ, bourgainRadialWeight R x*
      bourgainSourceSixMoment (Finset.univ.sigma S) (fun ji => z ji.1 ji.2)
        (fun ji => w ji.1 ji.2) x) ≤
      (N:ℝ)^5*∑ j, ∫ x : Fin 4 → ℝ,
        bourgainRadialWeight R x*bourgainSourceSixMoment (S j) (z j) (w j) x := by
  have hi (j : Fin N) := integrable_bourgainSource_weighted (S j) (z j) (w j) hR
  have hsum : Integrable (fun x : Fin 4 → ℝ =>
      ∑ j, bourgainRadialWeight R x*bourgainSourceSixMoment (S j) (z j) (w j) x) :=
    integrable_finsetSum Finset.univ (fun j _ => hi j)
  have hh := integral_mono
    (integrable_bourgainSource_weighted (Finset.univ.sigma S)
      (fun ji => z ji.1 ji.2) (fun ji => w ji.1 ji.2) hR)
    (hsum.const_mul ((N:ℝ)^5))
    (fun x => by
      have hp := mul_le_mul_of_nonneg_left (bourgainSourceSixMoment_finite_sum S z w x)
        (bourgainRadialWeight_nonneg R x)
      simpa only [Finset.mul_sum,mul_left_comm] using hp)
  rw [integral_const_mul,integral_finsetSum Finset.univ (fun j _ => hi j)] at hh
  exact hh

                                                                     
                                                                           
                                                                           
                                                                        
                                             
theorem exists_bourgainSourceCurve_polynomial_base :
    ∃ C > (0:ℝ), ∀ (n : ℕ) (ι τ : Type u)
      (S : Fin (2^n) → Finset ι) (V : Fin (2^n) → Finset τ)
      (z : Fin (2^n) → ι → ℂ) (c : Fin (2^n) → τ → ℂ)
      (w : Fin (2^n) → ι → ℝ) (v : Fin (2^n) → τ → ℝ),
      (∀ j, ∀ i ∈ S j, 0 ≤ w j i) → (∀ j, ∀ k ∈ V j, 0 ≤ v j k) →
      (∀ j, ∀ i ∈ S j, Real.sqrt (w j i) ∈ Icc 0 1) →
      (∀ j, ∀ k ∈ V j, Real.sqrt (v j k) ∈ Icc 0 1) →
      (∫ x : Fin 4 → ℝ in Icc (fun _ => -((2:ℝ)^n)^2) (fun _ => ((2:ℝ)^n)^2),
        ‖∑ ji ∈ Finset.univ.sigma S, z ji.1 ji.2*fordAdditiveCharacter
          (x 0*w ji.1 ji.2+x 1*(w ji.1 ji.2)^2+
            x 2*(w ji.1 ji.2)^((3:ℝ)/2)+x 3*Real.sqrt (w ji.1 ji.2))‖^6*
        ‖∑ jk ∈ Finset.univ.sigma V, c jk.1 jk.2*fordAdditiveCharacter
          (x 0*v jk.1 jk.2+x 1*(v jk.1 jk.2)^2+
            x 2*(v jk.1 jk.2)^((3:ℝ)/2)+x 3*Real.sqrt (v jk.1 jk.2))‖^6) ≤
        C*((2:ℝ)^n)^22/(((2:ℝ)^n)^2)^2*
          (∑ j, ∫ x : Fin 4 → ℝ, ((1+‖(20*((2:ℝ)^n)^2)⁻¹ • x‖)^100)⁻¹*
            ‖∑ i ∈ S j, z j i*fordAdditiveCharacter
              (x 0*w j i+x 1*(w j i)^2+x 2*(w j i)^((3:ℝ)/2)+x 3*Real.sqrt (w j i))‖^6)*
          (∑ j, ∫ x : Fin 4 → ℝ, ((1+‖(20*((2:ℝ)^n)^2)⁻¹ • x‖)^100)⁻¹*
            ‖∑ k ∈ V j, c j k*fordAdditiveCharacter
              (x 0*v j k+x 1*(v j k)^2+x 2*(v j k)^((3:ℝ)/2)+x 3*Real.sqrt (v j k))‖^6) := by
  obtain ⟨C,hC,hbase⟩ := exists_bourgainSourceCurve_box_base.{u}
  refine ⟨C,hC,?_⟩
  intro n ι τ S V z c w v hw hv hs ht
  let N := (2:ℝ)^n
  let R := N^2
  let JS := ∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*
    bourgainSourceSixMoment (S j) (z j) (w j) x
  let JV := ∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*
    bourgainSourceSixMoment (V j) (c j) (v j) x
  have hN : 1 ≤ N := one_le_pow₀ (by norm_num)
  have hR : 1 ≤ R := one_le_pow₀ hN
  have hR₀ : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have h20 : 0 < 20*R := by positivity
  have hm := hbase R hR (Finset.univ.sigma S) (Finset.univ.sigma V)
    (fun ji => z ji.1 ji.2) (fun jk => c jk.1 jk.2)
    (fun ji => w ji.1 ji.2) (fun jk => v jk.1 jk.2)
    (fun ji hji => hw ji.1 ji.2 (Finset.mem_sigma.mp hji).2)
    (fun jk hjk => hv jk.1 jk.2 (Finset.mem_sigma.mp hjk).2)
    (fun ji hji => hs ji.1 ji.2 (Finset.mem_sigma.mp hji).2)
    (fun jk hjk => ht jk.1 jk.2 (Finset.mem_sigma.mp hjk).2)
  have hS := bourgainSource_weighted_finite_sum S z w h20
  have hV := bourgainSource_weighted_finite_sum V c v h20
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hS hV
  have hJS : 0 ≤ JS := Finset.sum_nonneg (fun j _ => integral_nonneg (fun x =>
    mul_nonneg (bourgainRadialWeight_nonneg _ _) (bourgainSourceSixMoment_nonneg _ _ _ _)))
  have hprod := mul_le_mul hS hV
    (integral_nonneg (fun x => mul_nonneg (bourgainRadialWeight_nonneg _ _)
      (bourgainSourceSixMoment_nonneg _ _ _ _)))
    (mul_nonneg (by positivity) hJS)
  have hprod' := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ C*R^4)
  change _ ≤ C*N^22/R^2*JS*JV
  calc
    _ ≤ _ := hm
    _ = C*R^4*(_*_) := by ring
    _ ≤ C*R^4*((N^5*JS)*(N^5*JV)) := hprod'
    _ = C*N^22/R^2*JS*JV := by
      dsimp [R]
      field_simp

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory Set
namespace TaoTrudgianYang2025

public  theorem bourgain_radial_bilinear_fubini
    {K R : ℝ} (hK : 0 < K) (f g : (Fin 4 → ℝ) → ℝ) (Mf Mg : ℝ)
    (hfc : Continuous f) (hgc : Continuous g)
    (hfb : ∀ x, ‖f x‖ ≤ Mf) (hgb : ∀ x, ‖g x‖ ≤ Mg) :
    Integrable (fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      bourgainRadialWeight K p.1*bourgainRadialWeight K p.2*
        (∫ q : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R), f (q+p.1)*g (q+p.2))) ∧
    ((∫ q : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
      (∫ x : Fin 4 → ℝ, bourgainRadialWeight K x*f (q+x))*
        (∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*g (q+y))) =
      ∫ p : (Fin 4 → ℝ) × (Fin 4 → ℝ),
        bourgainRadialWeight K p.1*bourgainRadialWeight K p.2*
          (∫ q : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R), f (q+p.1)*g (q+p.2))) ∧
    IntegrableOn (fun q : Fin 4 → ℝ =>
      (∫ x : Fin 4 → ℝ, bourgainRadialWeight K x*f (q+x))*
        (∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*g (q+y)))
      (Icc (fun _ => -R) (fun _ => R)) := by
  let B := Icc (fun _ : Fin 4 => -R) (fun _ => R)
  let H := fun (p : (Fin 4 → ℝ) × (Fin 4 → ℝ)) (q : Fin 4 → ℝ) =>
    bourgainRadialWeight K p.1*bourgainRadialWeight K p.2*(f (q+p.1)*g (q+p.2))
  have hMf : 0 ≤ Mf := (norm_nonneg (f 0)).trans (hfb 0)
  have hw : Integrable (bourgainRadialWeight K) := integrable_bourgainCurveCellWeight hK
  have hconst : IntegrableOn (fun _q : Fin 4 → ℝ => (1:ℝ)) B :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hc : Continuous (fun p : ((Fin 4 → ℝ) × (Fin 4 → ℝ)) × (Fin 4 → ℝ) =>
      f (p.2+p.1.1)*g (p.2+p.1.2)) :=
    (hfc.comp (continuous_snd.add continuous_fst.fst)).mul
      (hgc.comp (continuous_snd.add continuous_fst.snd))
  have hiH : Integrable (Function.uncurry H)
      ((volume.prod volume).prod (volume.restrict B)) := by
    have hwprod := (hw.mul_prod hw).mul_prod hconst
    have hi := hwprod.mul_bdd hc.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => by
        rw [norm_mul]
        exact mul_le_mul (hfb _) (hgb _) (norm_nonneg _) hMf))
    convert hi using 1
    funext p
    simp only [Function.uncurry,H,mul_one]
  have he (p : (Fin 4 → ℝ) × (Fin 4 → ℝ)) :
      (∫ q in B, H p q) =
        bourgainRadialWeight K p.1*bourgainRadialWeight K p.2*
          (∫ q in B, f (q+p.1)*g (q+p.2)) := by
    simp only [H,integral_const_mul]
  have heq (q : Fin 4 → ℝ) : (∫ p : (Fin 4 → ℝ) × (Fin 4 → ℝ), H p q) =
      (∫ x : Fin 4 → ℝ, bourgainRadialWeight K x*f (q+x))*
        (∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*g (q+y)) := by
    calc
      _ = ∫ p : (Fin 4 → ℝ) × (Fin 4 → ℝ),
          (bourgainRadialWeight K p.1*f (q+p.1))*
            (bourgainRadialWeight K p.2*g (q+p.2)) := by
        apply integral_congr_ae
        filter_upwards with p
        dsimp [H]
        ring
      _ = _ := integral_prod_mul (μ:=volume) (ν:=volume)
        (fun x : Fin 4 → ℝ => bourgainRadialWeight K x*f (q+x))
        (fun y : Fin 4 → ℝ => bourgainRadialWeight K y*g (q+y))
  refine ⟨?_,?_,?_⟩
  · convert hiH.integral_prod_left using 1
    simp only [Function.uncurry,he,B]
  · have hswap := integral_integral_swap (f:=H) hiH
    calc
      _ = ∫ q in B, ∫ p : (Fin 4 → ℝ) × (Fin 4 → ℝ), H p q := by
        simp only [heq,B]
      _ = ∫ p : (Fin 4 → ℝ) × (Fin 4 → ℝ), ∫ q in B, H p q := hswap.symm
      _ = _ := by simp only [he,B]

  · have hiR : Integrable (fun q : Fin 4 → ℝ =>
        ∫ p : (Fin 4 → ℝ) × (Fin 4 → ℝ), H p q) (volume.restrict B) :=
      hiH.integral_prod_right
    simpa only [heq,B,IntegrableOn] using hiR

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private theorem integrable_bourgainRadial_shift_average
    {K R : ℝ} (hK : 0 < K) (hR : 0 < R)
    (f : (Fin 4 → ℝ) → ℝ) (M : ℝ) (hc : Continuous f)
    (hb : ∀ x, ‖f x‖ ≤ M) :
    Integrable (fun y : Fin 4 → ℝ => bourgainRadialWeight K y*
      (∫ x : Fin 4 → ℝ, bourgainRadialWeight R x*f (x+y))) := by
  have hwK : Integrable (bourgainRadialWeight K) := integrable_bourgainCurveCellWeight hK
  have hwR : Integrable (bourgainRadialWeight R) := integrable_bourgainCurveCellWeight hR
  have hprod := hwK.mul_prod hwR
  have hi := hprod.mul_bdd
    (hc.comp (continuous_snd.add continuous_fst)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => hb (p.2+p.1)))
  convert hi.integral_prod_left using 1
  funext y
  simp only [mul_assoc,integral_const_mul,Function.comp_apply,Pi.add_apply]


private theorem integrable_bourgainSource_shift_sum
    {K R : ℝ} (hK : 0 < K) (hR : 0 < R) {N : ℕ} {ι : Type*}
    (S : Fin N → Finset ι) (z : Fin N → ι → ℂ) (w : Fin N → ι → ℝ) :
    Integrable (fun y : Fin 4 → ℝ => bourgainRadialWeight K y*
      (∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight R x*
        bourgainSourceSixMoment (S j) (z j) (w j) (x+y))) := by
  have hi (j : Fin N) := integrable_bourgainRadial_shift_average hK hR
    (bourgainSourceSixMoment (S j) (z j) (w j)) ((∑ i ∈ S j, ‖z j i‖)^6)
    (continuous_bourgainSourceSixMoment (S j) (z j) (w j))
    (fun x => bourgain_character_six_bound (S j) (z j)
      (fun i => x 0*w j i+x 1*(w j i)^2+x 2*(w j i)^((3:ℝ)/2)+x 3*Real.sqrt (w j i)))
  simpa only [Finset.mul_sum] using integrable_finsetSum Finset.univ (fun j _ => hi j)

private theorem exists_bourgainSource_shift_sum :
    ∃ C > (0:ℝ), ∀ K R : ℝ, 0 < K → K ≤ R →
      ∀ (N : ℕ) {ι : Type u} (S : Fin N → Finset ι)
        (z : Fin N → ι → ℂ) (w : Fin N → ι → ℝ),
        (∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*
          (∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight R x*
            bourgainSourceSixMoment (S j) (z j) (w j) (x+y))) ≤
          C*K^4*(∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight R x*
            bourgainSourceSixMoment (S j) (z j) (w j) x) := by
  obtain ⟨C,hC,h⟩ := exists_bourgainRadialWeight_shift_average
  refine ⟨C,hC,?_⟩
  intro K R hK hKR N ι S z w
  have hR : 0 < R := hK.trans_le hKR
  have hi (j : Fin N) := integrable_bourgainRadial_shift_average hK hR
    (bourgainSourceSixMoment (S j) (z j) (w j)) ((∑ i ∈ S j, ‖z j i‖)^6)
    (continuous_bourgainSourceSixMoment (S j) (z j) (w j))
    (fun x => bourgain_character_six_bound (S j) (z j)
      (fun i => x 0*w j i+x 1*(w j i)^2+x 2*(w j i)^((3:ℝ)/2)+x 3*Real.sqrt (w j i)))
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun j _ => hi j)]
  apply Finset.sum_le_sum
  intro j hj
  exact h K R hK hKR
    (bourgainSourceSixMoment (S j) (z j) (w j)) ((∑ i ∈ S j, ‖z j i‖)^6)
    (continuous_bourgainSourceSixMoment (S j) (z j) (w j))
    (bourgainSourceSixMoment_nonneg (S j) (z j) (w j))
    (fun x => bourgain_character_six_bound (S j) (z j)
      (fun i => x 0*w j i+x 1*(w j i)^2+x 2*(w j i)^((3:ℝ)/2)+x 3*Real.sqrt (w j i)))

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u


public  theorem bourgainSourceSixMoment_norm_bound {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ) (x : Fin 4 → ℝ) :
    ‖bourgainSourceSixMoment S z w x‖ ≤ (∑ i ∈ S, ‖z i‖)^6 :=
  bourgain_character_six_bound S z
    (fun i => x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))

set_option maxHeartbeats 400000 in
public  theorem exists_bourgainSourceCurve_averaged_local_decoupling {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (n : ℕ) (a b σ R K : ℝ),
      0 ≤ a → a+σ ≤ 1 → 0 ≤ b → b+σ ≤ 1 → a ≠ b →
      0 < σ → σ ≤ 1 → 0 < R → 5*R*σ^3 ≤ 1 →
      5*(10*R)*(σ/(2:ℝ)^n)^3 ≤ 1 → 1 ≤ (σ/(2:ℝ)^n)*(10*R) →
      3/(100*(10*R)) ≤ (σ/(2:ℝ)^n)^2 → 0 < K → K ≤ 10*R →
      ∀ (ι τ : Type u) (S : Fin (2^n) → Finset ι) (V : Fin (2^n) → Finset τ)
        (z : Fin (2^n) → ι → ℂ) (c : Fin (2^n) → τ → ℂ)
        (w : Fin (2^n) → ι → ℝ) (v : Fin (2^n) → τ → ℝ),
        (∀ j, ∀ i ∈ S j, 0 ≤ w j i) → (∀ j, ∀ k ∈ V j, 0 ≤ v j k) →
        (∀ j, ∀ i ∈ S j, Real.sqrt (w j i) ∈ Icc
          (a+σ*((j:ℕ)/((2^n:ℕ):ℝ))) (a+σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ)))) →
        (∀ j, ∀ k ∈ V j, Real.sqrt (v j k) ∈ Icc
          (b+σ*((j:ℕ)/((2^n:ℕ):ℝ))) (b+σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ)))) →
        (∫ q : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
          (∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*
            bourgainSourceSixMoment (Finset.univ.sigma S)
              (fun ji => z ji.1 ji.2) (fun ji => w ji.1 ji.2) (q+y))*
          (∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*
            bourgainSourceSixMoment (Finset.univ.sigma V)
              (fun ji => c ji.1 ji.2) (fun ji => v ji.1 ji.2) (q+y))) ≤
          C*K^8*(2:ℝ)^((ε+4)*n)/(10*R)^4*(6*(b-a)^4)⁻¹*
            (∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (10*R) x*
              bourgainSourceSixMoment (S j) (z j) (w j) x)*
            (∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (10*R) x*
              bourgainSourceSixMoment (V j) (c j) (v j) x) := by
  obtain ⟨D,hD,hlocal⟩ := exists_bourgainSourceCurve_local_cell_decoupling.{u} hε
  obtain ⟨E,hE,havg⟩ := exists_bourgainSource_shift_sum.{u}
  refine ⟨D*E^2,by positivity,?_⟩
  intro n a b σ R K ha haσ hb hbσ hab hσ hσ₁ hR hrem hfine hδR hwidth hK hKR
    ι τ S V z c w v hw hv hs ht
  let F := bourgainSourceSixMoment (Finset.univ.sigma S)
    (fun ji => z ji.1 ji.2) (fun ji => w ji.1 ji.2)
  let G := bourgainSourceSixMoment (Finset.univ.sigma V)
    (fun ji => c ji.1 ji.2) (fun ji => v ji.1 ji.2)
  let JS := fun y : Fin 4 → ℝ => ∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (10*R) x*
    bourgainSourceSixMoment (S j) (z j) (w j) (x+y)
  let JV := fun y : Fin 4 → ℝ => ∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (10*R) x*
    bourgainSourceSixMoment (V j) (c j) (v j) (x+y)
  let AS := ∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (10*R) x*
    bourgainSourceSixMoment (S j) (z j) (w j) x
  let AV := ∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (10*R) x*
    bourgainSourceSixMoment (V j) (c j) (v j) x
  let A := D*(2:ℝ)^((ε+4)*n)/(10*R)^4*(6*(b-a)^4)⁻¹
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have h10 : 0 < 10*R := by positivity
  have hFub := bourgain_radial_bilinear_fubini (R:=R) hK F G
    ((∑ ji ∈ Finset.univ.sigma S, ‖z ji.1 ji.2‖)^6)
    ((∑ ji ∈ Finset.univ.sigma V, ‖c ji.1 ji.2‖)^6)
    (continuous_bourgainSourceSixMoment (Finset.univ.sigma S)
      (fun ji => z ji.1 ji.2) (fun ji => w ji.1 ji.2))
    (continuous_bourgainSourceSixMoment (Finset.univ.sigma V)
      (fun ji => c ji.1 ji.2) (fun ji => v ji.1 ji.2))
    (bourgainSourceSixMoment_norm_bound (Finset.univ.sigma S)
      (fun ji => z ji.1 ji.2) (fun ji => w ji.1 ji.2))
    (bourgainSourceSixMoment_norm_bound (Finset.univ.sigma V)
      (fun ji => c ji.1 ji.2) (fun ji => v ji.1 ji.2))
  have hp (p : (Fin 4 → ℝ) × (Fin 4 → ℝ)) :
      (∫ q : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
        F (q+p.1)*G (q+p.2)) ≤ A*JS p.1*JV p.2 := by
    have hh := hlocal n a b σ R ha haσ hb hbσ hab hσ hσ₁ hR hrem hfine hδR hwidth
      ι τ S V
      (fun j i => z j i*fordAdditiveCharacter
        (p.1 0*w j i+p.1 1*(w j i)^2+p.1 2*(w j i)^((3:ℝ)/2)+p.1 3*Real.sqrt (w j i)))
      (fun j i => c j i*fordAdditiveCharacter
        (p.2 0*v j i+p.2 1*(v j i)^2+p.2 2*(v j i)^((3:ℝ)/2)+p.2 3*Real.sqrt (v j i)))
      w v hw hv hs ht
    change (∫ q : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
      bourgainSourceSixMoment (Finset.univ.sigma S)
        (fun ji => z ji.1 ji.2*fordAdditiveCharacter
          (p.1 0*w ji.1 ji.2+p.1 1*(w ji.1 ji.2)^2+
            p.1 2*(w ji.1 ji.2)^((3:ℝ)/2)+p.1 3*Real.sqrt (w ji.1 ji.2)))
        (fun ji => w ji.1 ji.2) q*
      bourgainSourceSixMoment (Finset.univ.sigma V)
        (fun ji => c ji.1 ji.2*fordAdditiveCharacter
          (p.2 0*v ji.1 ji.2+p.2 1*(v ji.1 ji.2)^2+
            p.2 2*(v ji.1 ji.2)^((3:ℝ)/2)+p.2 3*Real.sqrt (v ji.1 ji.2)))
        (fun ji => v ji.1 ji.2) q) ≤
      A*(∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (10*R) x*
        bourgainSourceSixMoment (S j)
          (fun i => z j i*fordAdditiveCharacter
            (p.1 0*w j i+p.1 1*(w j i)^2+p.1 2*(w j i)^((3:ℝ)/2)+p.1 3*Real.sqrt (w j i))) (w j) x)*
        (∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (10*R) x*
          bourgainSourceSixMoment (V j)
            (fun i => c j i*fordAdditiveCharacter
              (p.2 0*v j i+p.2 1*(v j i)^2+p.2 2*(v j i)^((3:ℝ)/2)+p.2 3*Real.sqrt (v j i))) (v j) x) at hh
    simpa only [bourgainSourceSixMoment_translate,F,G,JS,JV] using hh
  have hiS := integrable_bourgainSource_shift_sum hK h10 S z w
  have hiV := integrable_bourgainSource_shift_sum hK h10 V c v
  have hiRight : Integrable (fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      A*((bourgainRadialWeight K p.1*JS p.1)*(bourgainRadialWeight K p.2*JV p.2))) :=
    (hiS.mul_prod hiV).const_mul A
  have hout := integral_mono hFub.1 hiRight
    (fun p => by
      have hh := mul_le_mul_of_nonneg_left (hp p)
        (mul_nonneg (bourgainRadialWeight_nonneg K p.1) (bourgainRadialWeight_nonneg K p.2))
      exact hh.trans_eq (by ring))
  have hfactor : (∫ p : (Fin 4 → ℝ) × (Fin 4 → ℝ),
      (bourgainRadialWeight K p.1*JS p.1)*(bourgainRadialWeight K p.2*JV p.2)) =
      (∫ x : Fin 4 → ℝ, bourgainRadialWeight K x*JS x)*
        (∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*JV y) :=
    integral_prod_mul (μ:=volume) (ν:=volume)
      (fun x : Fin 4 → ℝ => bourgainRadialWeight K x*JS x)
      (fun y : Fin 4 → ℝ => bourgainRadialWeight K y*JV y)
  rw [integral_const_mul,hfactor] at hout
  have hmS := havg K (10*R) hK hKR (2^n) S z w
  have hmV := havg K (10*R) hK hKR (2^n) V c v
  have hAS : 0 ≤ AS := Finset.sum_nonneg (fun j _ => integral_nonneg (fun x =>
    mul_nonneg (bourgainRadialWeight_nonneg (10*R) x) (bourgainSourceSixMoment_nonneg (S j) (z j) (w j) x)))
  have hJV : 0 ≤ ∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*JV y :=
    integral_nonneg (fun y => mul_nonneg (bourgainRadialWeight_nonneg _ _)
      (Finset.sum_nonneg (fun j _ => integral_nonneg (fun x =>
        mul_nonneg (bourgainRadialWeight_nonneg (10*R) x) (bourgainSourceSixMoment_nonneg (V j) (c j) (v j) (x+y))))))
  have hprod := mul_le_mul hmS hmV hJV (mul_nonneg (by positivity) hAS)
  have hmain := hout.trans (mul_le_mul_of_nonneg_left hprod hA)
  rw [hFub.2.1]
  change _ ≤ (D*E^2)*K^8*(2:ℝ)^((ε+4)*n)/(10*R)^4*(6*(b-a)^4)⁻¹*AS*AV
  exact hmain.trans_eq (by dsimp [A]; ring)

end TaoTrudgianYang2025


noncomputable section
open Set
namespace TaoTrudgianYang2025

public  theorem bourgain_coarse_center_separation {a b σ ν u v : ℝ}
    (hν : 0 < ν) (hσ : σ ≤ ν/2)
    (hu : u ∈ Icc a (a+σ)) (hv : v ∈ Icc b (b+σ))
    (hsep : ν ≤ |u-v|) :
    ν/2 ≤ |b-a| ∧ a ≠ b ∧ (6*(b-a)^4)⁻¹ ≤ (6*(ν/2)^4)⁻¹ := by
  have hh : |u-v| ≤ |a-b|+σ := by
    apply abs_le.mpr
    constructor
    · linarith [hu.1,hv.2,neg_abs_le (a-b)]
    · linarith [hu.2,hv.1,le_abs_self (a-b)]
  have hd : ν/2 ≤ |b-a| := by
    rw [abs_sub_comm a b] at hh
    linarith
  have hab : a ≠ b := by
    intro he
    rw [he,sub_self,abs_zero] at hd
    linarith
  have hp : (ν/2)^4 ≤ (b-a)^4 := by
    have h := pow_le_pow_left₀ (by positivity) hd 4
    simpa only [show (4:ℕ)=2*2 by omega,pow_mul,sq_abs] using h
  exact ⟨hd,hab,inv_anti₀ (by positivity)
    (mul_le_mul_of_nonneg_left hp (by norm_num))⟩

end TaoTrudgianYang2025


noncomputable section
namespace TaoTrudgianYang2025

public  theorem bourgain_bootstrap_depth {n : ℕ} (hn : 9 ≤ n) :
    let m := (2*n+2)/3+2
    m < n ∧ 2*n+6 ≤ 3*m ∧ n ≤ 2*m := by
  dsimp
  omega

public  theorem bourgain_bootstrap_scale_conditions {n m : ℕ}
    (hm : m ≤ n) (hlarge : 2*n+6 ≤ 3*m) (hn : 7 ≤ n) :
    let N := (2:ℝ)^n
    let M := (2:ℝ)^m
    let σ := 1/M
    let δ := σ/(2:ℝ)^(n-m)
    0 < σ ∧ σ ≤ 1 ∧ δ=1/N ∧
      5*(2*N^2)*σ^3 ≤ 1 ∧
      5*(10*(2*N^2))*δ^3 ≤ 1 ∧
      1 ≤ δ*(10*(2*N^2)) ∧
      3/(100*(10*(2*N^2))) ≤ δ^2 ∧
      0 < 20*M^2 ∧ 20*M^2 ≤ 10*(2*N^2) := by
  let N := (2:ℝ)^n
  let M := (2:ℝ)^m
  have hN : 0 < N := by dsimp [N]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hN₁ : 1 ≤ N := one_le_pow₀ (by norm_num)
  have hM₁ : 1 ≤ M := one_le_pow₀ (by norm_num)
  have hMN : M ≤ N := pow_le_pow_right₀ (by norm_num) hm
  have hN128 : (128:ℝ) ≤ N := by
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn
    norm_num only [show (2:ℝ)^7=128 by norm_num] at h
    exact h
  have hpow : N^2*64 ≤ M^3 := by
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2)
      (by omega : n*2+6 ≤ m*3)
    rw [pow_add,pow_mul,pow_mul] at h
    norm_num only [show (2:ℝ)^6=64 by norm_num] at h
    exact h
  have hδ : (1/M)/(2:ℝ)^(n-m)=1/N := by
    dsimp [M,N]
    rw [pow_sub₀ (2:ℝ) (by norm_num) hm]
    field_simp
  change 0 < 1/M ∧ 1/M ≤ 1 ∧ (1/M)/(2:ℝ)^(n-m)=1/N ∧ _
  refine ⟨by positivity,(div_le_one hM).mpr hM₁,hδ,?_,?_,?_,?_,by positivity,?_⟩
  · have he : 5*(2*N^2)*(1/M)^3 = 10*N^2/M^3 := by ring
    rw [he]
    apply (div_le_one (pow_pos hM 3)).mpr
    nlinarith [sq_nonneg N]
  · rw [hδ]
    have he : 5*(10*(2*N^2))*(1/N)^3 = 100/N := by field_simp; ring
    rw [he]
    exact (div_le_one hN).mpr (by linarith)
  · rw [hδ]
    have he : (1/N)*(10*(2*N^2)) = 20*N := by field_simp; ring
    rw [he]
    linarith
  · rw [hδ,div_pow,one_pow]
    apply (div_le_div_iff₀ (by positivity) (sq_pos_of_pos hN)).mpr
    nlinarith [sq_nonneg N]
  · have hp := pow_le_pow_left₀ hM.le hMN 2
    nlinarith

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

                                                                         
                                                                           
                  
public  def BourgainSourceGridBound (N : ℕ) (ν D : ℝ) : Prop :=
  0 ≤ D ∧ ∀ (ι τ : Type u)
    (S : Fin N → Finset ι) (V : Fin N → Finset τ)
    (z : Fin N → ι → ℂ) (c : Fin N → τ → ℂ)
    (w : Fin N → ι → ℝ) (v : Fin N → τ → ℝ),
    (∀ j, ∀ i ∈ S j, 0 ≤ w j i) → (∀ j, ∀ k ∈ V j, 0 ≤ v j k) →
    (∀ j, ∀ i ∈ S j, Real.sqrt (w j i) ∈ Icc ((j:ℕ)/(N:ℝ)) (((j:ℕ)+1)/(N:ℝ))) →
    (∀ j, ∀ k ∈ V j, Real.sqrt (v j k) ∈ Icc ((j:ℕ)/(N:ℝ)) (((j:ℕ)+1)/(N:ℝ))) →
    (∀ j k, ∀ i ∈ S j, ∀ l ∈ V k, ν ≤ |Real.sqrt (w j i)-Real.sqrt (v k l)|) →
    (∫ x : Fin 4 → ℝ in Icc (fun _ => -(N:ℝ)^2) (fun _ => (N:ℝ)^2),
      bourgainSourceSixMoment (Finset.univ.sigma S) (fun ji => z ji.1 ji.2)
        (fun ji => w ji.1 ji.2) x*
      bourgainSourceSixMoment (Finset.univ.sigma V) (fun ji => c ji.1 ji.2)
        (fun ji => v ji.1 ji.2) x) ≤
      D/((N:ℝ)^2)^2*
        (∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*(N:ℝ)^2) x*
          bourgainSourceSixMoment (S j) (z j) (w j) x)*
        (∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*(N:ℝ)^2) x*
          bourgainSourceSixMoment (V j) (c j) (v j) x)

public  theorem bourgainSourceGridBound_mono {N : ℕ} {ν D E : ℝ}
    (hD : BourgainSourceGridBound.{u} N ν D) (hDE : D ≤ E) :
    BourgainSourceGridBound.{u} N ν E := by
  refine ⟨hD.1.trans hDE,?_⟩
  intro ι τ S V z c w v hw hv hs ht hsep
  have hm := hD.2 ι τ S V z c w v hw hv hs ht hsep
  have hS : 0 ≤ ∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*(N:ℝ)^2) x*
      bourgainSourceSixMoment (S j) (z j) (w j) x :=
    Finset.sum_nonneg (fun j _ => integral_nonneg (fun x =>
      mul_nonneg (bourgainRadialWeight_nonneg _ _) (bourgainSourceSixMoment_nonneg (S j) (z j) (w j) x)))
  have hV : 0 ≤ ∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*(N:ℝ)^2) x*
      bourgainSourceSixMoment (V j) (c j) (v j) x :=
    Finset.sum_nonneg (fun j _ => integral_nonneg (fun x =>
      mul_nonneg (bourgainRadialWeight_nonneg _ _) (bourgainSourceSixMoment_nonneg (V j) (c j) (v j) x)))
  exact hm.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hDE (by positivity)) hS) hV)

public  theorem exists_bourgainSourceGridBound_polynomial :
    ∃ C > (0:ℝ), ∀ (n : ℕ) (ν : ℝ),
      BourgainSourceGridBound.{u} (2^n) ν (C*((2:ℝ)^n)^22) := by
  obtain ⟨C,hC,hbase⟩ := exists_bourgainSourceCurve_polynomial_base.{u}
  refine ⟨C,hC,?_⟩
  intro n ν
  refine ⟨by positivity,?_⟩
  intro ι τ S V z c w v hw hv hs ht _hsep
  have hunit {κ : Type u} (U : Fin (2^n) → Finset κ) (u : Fin (2^n) → κ → ℝ)
      (hu : ∀ j, ∀ i ∈ U j, Real.sqrt (u j i) ∈ Icc
        ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) :
      ∀ j, ∀ i ∈ U j, Real.sqrt (u j i) ∈ Icc 0 1 := by
    intro j i hi
    refine ⟨(by positivity : (0:ℝ) ≤ (j:ℕ)/((2^n:ℕ):ℝ)).trans (hu j i hi).1,?_⟩
    apply (hu j i hi).2.trans
    apply (div_le_one (by positivity)).mpr
    exact_mod_cast Nat.succ_le_of_lt j.isLt
  have hm := hbase n ι τ S V z c w v hw hv (hunit S w hs) (hunit V v ht)
  simpa only [Nat.cast_pow,Nat.cast_ofNat,bourgainRadialWeight,bourgainSourceSixMoment] using hm

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

public  theorem bourgainSource_grid_coarse_interval {k l : ℕ}
  (hk : 0 < k) (hl : 0 < l) {κ : Type u} (A : Fin (k*l) → Finset κ) (f : Fin (k*l) → κ → ℝ)
    (hgrid : ∀ j, ∀ i ∈ A j, Real.sqrt (f j i) ∈ Icc
      ((j:ℕ)/((k*l:ℕ):ℝ)) (((j:ℕ)+1)/((k*l:ℕ):ℝ))) :
    ∀ i : Fin k, ∀ ji ∈ Finset.univ.sigma (fun j : Fin l => A (finProdFinEquiv (i,j))),
      Real.sqrt (f (finProdFinEquiv (i,ji.1)) ji.2) ∈ Icc ((i:ℕ)/(k:ℝ)) (((i:ℕ)+1)/(k:ℝ)) := by
  intro i ji hji
  have hf := hgrid (finProdFinEquiv (i,ji.1)) ji.2 (Finset.mem_sigma.mp hji).2
  have hcell := finGrid_cell hk hl i ji.1
  simp only [Nat.cast_mul] at hf
  change Real.sqrt (f (finProdFinEquiv (i,ji.1)) ji.2) ∈ Icc
    (((finProdFinEquiv (i,ji.1) : Fin (k*l)):ℕ)/(k*l:ℝ))
    ((((finProdFinEquiv (i,ji.1) : Fin (k*l)):ℕ)+1)/(k*l:ℝ)) at hf
  rw [hcell.1,hcell.2] at hf
  have hj₀ : (0:ℝ) ≤ (ji.1:ℕ)/(l:ℝ) := by positivity
  have hj₁ : ((ji.1:ℕ)+1)/(l:ℝ) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    exact_mod_cast Nat.succ_le_of_lt ji.1.isLt
  refine ⟨(le_add_of_nonneg_right (mul_nonneg (by positivity) hj₀)).trans hf.1,?_⟩
  calc
    _ ≤ (i:ℕ)/(k:ℝ)+(1/(k:ℝ))*(((ji.1:ℕ)+1)/(l:ℝ)) := hf.2
    _ ≤ (i:ℕ)/(k:ℝ)+(1/(k:ℝ))*1 := add_le_add_right
      (mul_le_mul_of_nonneg_left hj₁ (by positivity)) _
    _ = ((i:ℕ)+1)/(k:ℝ) := by ring

public  theorem bourgainSourceSixMoment_grid_reindex {k l : ℕ} {ι : Type*}
    (S : Fin (k*l) → Finset ι) (z : Fin (k*l) → ι → ℂ) (w : Fin (k*l) → ι → ℝ)
    (x : Fin 4 → ℝ) :
    bourgainSourceSixMoment (Finset.univ.sigma S) (fun ri => z ri.1 ri.2)
      (fun ri => w ri.1 ri.2) x =
    bourgainSourceSixMoment
      (Finset.univ.sigma (fun i : Fin k => Finset.univ.sigma
        (fun j : Fin l => S (finProdFinEquiv (i,j)))))
      (fun ijv => z (finProdFinEquiv (ijv.1,ijv.2.1)) ijv.2.2)
      (fun ijv => w (finProdFinEquiv (ijv.1,ijv.2.1)) ijv.2.2) x := by
  unfold bourgainSourceSixMoment
  apply congrArg (fun q : ℂ => ‖q‖^6)
  simp only [Finset.sum_sigma]
  exact finGrid_sum (fun r => ∑ i ∈ S r, z r i*fordAdditiveCharacter
    (x 0*w r i+x 1*(w r i)^2+x 2*(w r i)^((3:ℝ)/2)+x 3*Real.sqrt (w r i)))

-- Generated closures: source context is replayed in the next part.
end TaoTrudgianYang2025
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
