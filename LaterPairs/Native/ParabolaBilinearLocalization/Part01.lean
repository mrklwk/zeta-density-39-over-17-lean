module
public import LaterPairs.Native.ParabolaFirstSpacing
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

open GafniTao Set
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth
open MeasureTheory
open MeasureTheory FourierTransform SchwartzMap Set GafniTao
open MeasureTheory GafniTao
open MeasureTheory GafniTao Set
open MeasureTheory Set
open Set
open scoped BigOperators
open scoped BigOperators ComplexConjugate
open scoped BigOperators ContDiff
open scoped BigOperators ContDiff FourierTransform
open scoped BigOperators Matrix
open scoped BigOperators Matrix ContDiff
open scoped BigOperators NNReal ENNReal
open scoped ComplexConjugate Convolution ContDiff
open scoped ContDiff
open scoped ContDiff BigOperators
open scoped ContDiff FourierTransform
open scoped ContDiff Topology
open scoped Matrix
noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology FourierTransform BigOperators

namespace TaoTrudgianYang2025


private theorem bourgain_schwartz_integer_summable (f : SchwartzMap ℝ ℂ) :
    Summable (fun n : ℤ => f n) := by
  exact summable_of_isBigO
    (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
    (by simpa only [Function.comp_def, Real.norm_eq_abs] using
      (f.isBigO_cocompact_rpow (-(2 : ℝ))).comp_tendsto Int.tendsto_coe_cofinite)

private theorem bourgain_smooth_residue_poisson {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    {q : ℝ} (hq : 0 < q) (d : ℝ) :
    Summable (fun h : ℤ => 𝓕 f ((h : ℝ)/q)) ∧
      (∑' k : ℤ, f ((k : ℝ)*q+d)) =
        (q : ℂ)⁻¹ * ∑' h : ℤ,
          (𝐞 ((h : ℝ)*d/q) : ℂ)*𝓕 f ((h : ℝ)/q) := by
  let g : SchwartzMap ℝ ℂ :=
    (hs.comp_homeomorph (Homeomorph.smulOfNeZero q hq.ne')).toSchwartzMap
      (hf.comp (contDiff_const.mul contDiff_id))
  have hg (x : ℝ) : g x = f (q*x) := rfl
  have hgF (y : ℝ) : 𝓕 g y = (q : ℂ)⁻¹ * 𝓕 f (y/q) := by
    rw [SchwartzMap.fourier_coe,Real.fourier_real_eq,Real.fourier_real_eq]
    simp only [Circle.smul_def,smul_eq_mul,hg]
    have hphase (x : ℝ) : -(q*x*(y/q)) = -(x*y) := by field_simp
    have h := Measure.integral_comp_mul_left
      (fun x : ℝ => (𝐞 (-(x*(y/q))) : ℂ)*f x) q
    simp only [hphase,abs_of_pos (inv_pos.mpr hq),Complex.real_smul,Complex.ofReal_inv] at h
    exact h
  have hsum : Summable (fun h : ℤ => 𝓕 f ((h : ℝ)/q)) := by
    have h := (bourgain_schwartz_integer_summable (𝓕 g)).mul_left (q : ℂ)
    simpa only [hgF,← mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hq.ne'),
      one_mul] using h
  refine ⟨hsum,?_⟩
  have h := SchwartzMap.tsum_eq_tsum_fourier g (d/q)
  have he (h : ℤ) : fourier h (d/q : UnitAddCircle) =
      (𝐞 ((h : ℝ)*d/q) : ℂ) := by
    rw [fourier_coe_apply,Real.fourierChar_apply]
    push_cast
    congr 1
    ring
  have harg (k : ℤ) : q*(d/q+(k : ℝ)) = (k : ℝ)*q+d := by field_simp; ring
  simp only [hg,harg,hgF,he] at h
  rw [h,← tsum_mul_left]
  apply tsum_congr
  intro k
  ring

set_option maxHeartbeats 400000 in
private theorem bourgain_periodic_weighted_poisson {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (q : ℕ) [NeZero q] (w : ZMod q → ℂ) :
    (∑' n : ℤ, w (n : ZMod q)*f n) =
      (q : ℂ)⁻¹ * ∑' h : ℤ,
        (∑ d : Fin q, w (d.val : ZMod q)*
          (𝐞 ((h : ℝ)*(d.val : ℝ)/(q : ℝ)) : ℂ))*
            𝓕 f ((h : ℝ)/(q : ℝ)) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hfs : Summable (fun n : ℤ => f n) :=
    bourgain_schwartz_integer_summable (hs.toSchwartzMap hf)
  have hw : Summable (fun n : ℤ => w (n : ZMod q)*f n) :=
    (hfs.norm.mul_left ‖w‖).of_norm_bounded (fun n => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_le_pi_norm w (n : ZMod q)) (norm_nonneg _))
  let e := (Int.divModEquiv q).symm
  have hp : Summable (fun p : ℤ × Fin q => w ((e p : ℤ) : ZMod q)*f (e p)) :=
    e.summable_iff.mpr hw
  have hsplit : (∑' n : ℤ, w (n : ZMod q)*f n) =
      ∑ d : Fin q, w (d.val : ZMod q)*
        ∑' k : ℤ, f ((k : ℝ)*(q : ℝ)+(d.val : ℝ)) := by
    have hcomm := Summable.tsum_comm
      (f := fun (k : ℤ) (d : Fin q) => w ((e (k,d) : ℤ) : ZMod q)*f (e (k,d))) hp
    rw [← e.tsum_eq (fun n : ℤ => w (n : ZMod q)*f n),hp.tsum_prod,
      ← hcomm,tsum_fintype]
    apply Finset.sum_congr rfl
    intro d hd
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    simp only [e,Int.divModEquiv_symm_apply,Int.cast_add,Int.cast_mul,
      Int.cast_natCast,ZMod.natCast_self,mul_zero,zero_add]
  have hF := (bourgain_smooth_residue_poisson hf hs hq 0).1
  have hsum (d : Fin q) : Summable (fun h : ℤ =>
      w (d.val : ZMod q)*(q : ℂ)⁻¹*
        ((𝐞 ((h : ℝ)*(d.val : ℝ)/(q : ℝ)) : ℂ)*𝓕 f ((h : ℝ)/(q : ℝ)))) := by
    apply ((hF.norm.mul_left ‖w (d.val : ZMod q)*(q : ℂ)⁻¹‖)).of_norm_bounded
    intro h
    simp only [norm_mul,Circle.norm_coe,one_mul]
    exact le_rfl
  rw [hsplit]
  conv_lhs =>
    arg 2
    ext d
    rw [(bourgain_smooth_residue_poisson hf hs hq (d.val : ℝ)).2]
  calc
    _ = ∑ d : Fin q, ∑' h : ℤ,
        w (d.val : ZMod q)*(q : ℂ)⁻¹*
          ((𝐞 ((h : ℝ)*(d.val : ℝ)/(q : ℝ)) : ℂ)*𝓕 f ((h : ℝ)/(q : ℝ))) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [tsum_mul_left]
      push_cast
      ring
    _ = ∑' h : ℤ, ∑ d : Fin q,
        w (d.val : ZMod q)*(q : ℂ)⁻¹*
          ((𝐞 ((h : ℝ)*(d.val : ℝ)/(q : ℝ)) : ℂ)*𝓕 f ((h : ℝ)/(q : ℝ))) :=
      (Summable.tsum_finsetSum (fun d _ => hsum d)).symm
    _ = _ := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro h
      simp only [Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring


def bourgainQuadraticGauss (q : ℕ) (a b : ℤ) : ℂ :=
  ∑ d : Fin q, (𝐞 (((a : ℝ)*(d.val : ℝ)^2+(b : ℝ)*(d.val : ℝ))/(q : ℝ)) : ℂ)

def bourgainCubicFourierMode (χ : ℝ → ℂ) (μ y : ℝ) : ℂ :=
  ∫ x : ℝ, χ x*(𝐞 (μ*x^3-y*x) : ℂ)

private theorem bourgain_modular_character (q : ℕ) [NeZero q] (n : ℤ) :
    ZMod.stdAddChar (n : ZMod q) = (𝐞 ((n : ℝ)/(q : ℝ)) : ℂ) := by
  rw [ZMod.stdAddChar_coe,Real.fourierChar_apply]
  push_cast
  congr 1
  ring

                                                                      
                                                                            
theorem bourgain_cubic_rational_weighted_poisson {χ : ℝ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hs : HasCompactSupport χ)
    (μ : ℝ) (q : ℕ) [NeZero q] (a b : ℤ) :
    Summable (fun h : ℤ =>
      ‖bourgainQuadraticGauss q a (b+h)*
        bourgainCubicFourierMode χ μ ((h : ℝ)/(q : ℝ))‖) ∧
    (∑' n : ℤ, χ n*(𝐞 (μ*(n : ℝ)^3+
        ((a : ℝ)*(n : ℝ)^2+(b : ℝ)*(n : ℝ))/(q : ℝ)) : ℂ)) =
      (q : ℂ)⁻¹ * ∑' h : ℤ,
        bourgainQuadraticGauss q a (b+h)*
          bourgainCubicFourierMode χ μ ((h : ℝ)/(q : ℝ)) := by
  let f : ℝ → ℂ := fun x => χ x*(𝐞 (μ*x^3) : ℂ)
  let w : ZMod q → ℂ := fun d => ZMod.stdAddChar ((a : ZMod q)*d^2+(b : ZMod q)*d)
  have hf : ContDiff ℝ ∞ f := by
    dsimp only [f]
    simp only [Real.fourierChar_apply]
    have hp : ContDiff ℝ ∞ (fun x : ℝ => 2*Real.pi*(μ*x^3)) := by fun_prop
    exact hχ.mul (((Complex.ofRealCLM.contDiff.comp hp).mul contDiff_const).cexp)
  have hfs : HasCompactSupport f := hs.mul_right
  have hw (n : ℤ) : w (n : ZMod q) =
      (𝐞 (((a : ℝ)*(n : ℝ)^2+(b : ℝ)*(n : ℝ))/(q : ℝ)) : ℂ) := by
    dsimp only [w]
    rw [← Int.cast_pow,← Int.cast_mul,← Int.cast_mul,← Int.cast_add,
      bourgain_modular_character]
    push_cast
    rfl
  have hF (y : ℝ) : 𝓕 f y = bourgainCubicFourierMode χ μ y := by
    rw [Real.fourier_real_eq]
    unfold bourgainCubicFourierMode
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [Circle.smul_def,smul_eq_mul,f]
    rw [show μ*x^3-y*x = -(x*y)+μ*x^3 by ring,
      AddChar.map_add_eq_mul,Circle.coe_mul]
    ring
  have hG (h : ℤ) :
      (∑ d : Fin q, w (d.val : ZMod q)*
        (𝐞 ((h : ℝ)*(d.val : ℝ)/(q : ℝ)) : ℂ)) =
          bourgainQuadraticGauss q a (b+h) := by
    unfold bourgainQuadraticGauss
    apply Finset.sum_congr rfl
    intro d hd
    have hwd := hw (d.val : ℤ)
    simp only [Int.cast_natCast] at hwd
    rw [hwd,← Circle.coe_mul,← AddChar.map_add_eq_mul]
    congr 2
    push_cast
    ring
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hFourier := (bourgain_smooth_residue_poisson hf hfs hq 0).1
  have hsum (d : Fin q) : Summable (fun h : ℤ =>
      w (d.val : ZMod q)*(𝐞 ((h : ℝ)*(d.val : ℝ)/(q : ℝ)) : ℂ)*
        𝓕 f ((h : ℝ)/(q : ℝ))) := by
    apply (hFourier.norm.mul_left ‖w (d.val : ZMod q)‖).of_norm_bounded
    intro h
    simp only [norm_mul,Circle.norm_coe,mul_one]
    exact le_rfl
  have htotal := (summable_sum (s := Finset.univ) (fun d _ => hsum d)).norm
  simp only [← Finset.sum_mul,hG,hF] at htotal
  refine ⟨htotal,?_⟩
  have hp := bourgain_periodic_weighted_poisson hf hfs q w
  simp only [hG,hF] at hp
  rw [← hp]
  apply tsum_congr
  intro n
  rw [hw]
  dsimp only [f]
  rw [AddChar.map_add_eq_mul,Circle.coe_mul]
  ring


set_option maxHeartbeats 400000 in
private theorem bourgain_two_torsion_card (q : ℕ) [NeZero q] :
    (Finset.univ.filter (fun t : ZMod q => 2*t = 0)).card ≤ 2 := by
  classical
  let S := Finset.univ.filter (fun t : ZMod q => 2*t = 0)
  have hval (t : ZMod q) (ht : t ∈ S) : t.val = 0 ∨ t.val = q/2 := by
    have ht0 : 2*t = 0 := (Finset.mem_filter.mp ht).2
    have htneg : -t = t := by
      rw [neg_eq_iff_add_eq_zero]
      simpa only [two_mul] using ht0
    rcases (ZMod.neg_eq_self_iff t).mp htneg with hz | hz
    · left
      simp only [hz,ZMod.val_zero]
    · right
      omega
  have hi : S.image ZMod.val ⊆ {0,q/2} := by
    intro n hn
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hn
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hval t ht
  calc
    S.card = (S.image ZMod.val).card := (Finset.card_image_of_injective S (ZMod.val_injective q)).symm
    _ ≤ ({0,q/2} : Finset ℕ).card := Finset.card_le_card hi
    _ ≤ 2 := Finset.card_le_two


open scoped ComplexConjugate

private theorem bourgain_gauss_norm_sq (q : ℕ) [NeZero q] (a b : ZMod q) :
    ((‖∑ x : ZMod q, ZMod.stdAddChar (a*x^2+b*x)‖^2 : ℝ) : ℂ) =
      ∑ t : ZMod q, ZMod.stdAddChar (a*t^2+b*t)*
        (if 2*a*t = 0 then (q : ℂ) else 0) := by
  have hc (u : ZMod q) : conj (ZMod.stdAddChar u) = ZMod.stdAddChar (-u) := by
    rw [ZMod.stdAddChar_apply,ZMod.stdAddChar_apply,
      AddChar.map_neg_eq_inv,Circle.coe_inv_eq_conj]
  rw [← Complex.normSq_eq_norm_sq,← Complex.mul_conj,map_sum]
  simp only [Finset.sum_mul,Finset.mul_sum,hc,← AddChar.map_add_eq_mul]
  have hshift (y : ZMod q) :
      (∑ x : ZMod q, ZMod.stdAddChar (a*x^2+b*x+ -(a*y^2+b*y))) =
        ∑ t : ZMod q, ZMod.stdAddChar (a*t^2+b*t+(2*a*t)*y) := by
    symm
    apply Fintype.sum_equiv (Equiv.addRight y)
    intro t
    congr 1
    change a*t^2+b*t+(2*a*t)*y = a*(t+y)^2+b*(t+y)+ -(a*y^2+b*y)
    ring
  simp only [hshift]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [← GafniTao.wooley_sum_stdAddChar_mul q (2*a*t),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  exact AddChar.map_add_eq_mul _ _ _

private theorem bourgain_gauss_norm_le (q : ℕ) [NeZero q] (a b : ZMod q)
    (ha : IsUnit a) :
    ‖∑ x : ZMod q, ZMod.stdAddChar (a*x^2+b*x)‖ ≤ Real.sqrt (2*(q : ℝ)) := by
  classical
  have hker (t : ZMod q) : 2*a*t = 0 ↔ 2*t = 0 := by
    rw [show 2*a*t = a*(2*t) by ring]
    exact ha.mul_right_eq_zero
  have hsq := bourgain_gauss_norm_sq q a b
  simp only [hker] at hsq
  have hn := congrArg norm hsq
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)] at hn
  have hsum :
      ‖∑ t : ZMod q, ZMod.stdAddChar (a*t^2+b*t)*
        (if 2*t = 0 then (q : ℂ) else 0)‖ ≤ 2*(q : ℝ) := by
    calc
      _ ≤ ∑ t : ZMod q,
          ‖ZMod.stdAddChar (a*t^2+b*t)*(if 2*t = 0 then (q : ℂ) else 0)‖ :=
        norm_sum_le _ _
      _ = ((Finset.univ.filter (fun t : ZMod q => 2*t = 0)).card : ℝ)*(q : ℝ) := by
        simp only [norm_mul,sargos_stdAddChar_norm,one_mul]
        simp only [apply_ite norm,Complex.norm_natCast,norm_zero,← Finset.sum_filter,
          Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2*(q : ℝ) := mul_le_mul_of_nonneg_right
        (by exact_mod_cast bourgain_two_torsion_card q) (Nat.cast_nonneg _)
  have hbound : ‖∑ x : ZMod q, ZMod.stdAddChar (a*x^2+b*x)‖^2 ≤ 2*(q : ℝ) := by
    rw [hn]
    exact hsum
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr hbound


private theorem bourgain_gauss_fin_sum (q : ℕ) [NeZero q] (a b : ℤ) :
    bourgainQuadraticGauss q a b =
      ∑ x : ZMod q, ZMod.stdAddChar ((a : ZMod q)*x^2+(b : ZMod q)*x) := by
  have he (d : Fin q) : (ZMod.finEquiv q) d = (d.val : ZMod q) := by
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q =>
      apply Fin.ext
      exact (Nat.mod_eq_of_lt d.isLt).symm
  unfold bourgainQuadraticGauss
  apply Fintype.sum_equiv (ZMod.finEquiv q).toEquiv
  intro d
  rw [show (ZMod.finEquiv q).toEquiv d = (d.val : ZMod q) from he d]
  have h := bourgain_modular_character q (a*(d.val : ℤ)^2+b*(d.val : ℤ))
  push_cast at h
  exact h.symm

                                                                       
                                                                        
theorem bourgainQuadraticGauss_norm_le (q : ℕ) [NeZero q] (a b : ℤ)
    (ha : IsCoprime a (q : ℤ)) :
    ‖bourgainQuadraticGauss q a b‖ ≤ Real.sqrt (2*(q : ℝ)) := by
  rw [bourgain_gauss_fin_sum]
  apply bourgain_gauss_norm_le
  have h := ha.map (Int.castRingHom (ZMod q))
  exact isCoprime_zero_right.mp (by simpa using h)


private theorem bourgain_modular_gauss_shift (q : ℕ) [NeZero q] (a b t : ZMod q) :
    (∑ x : ZMod q, ZMod.stdAddChar (a*x^2+(b+2*a*t)*x)) =
      ZMod.stdAddChar (-(a*t^2+b*t))*
        ∑ x : ZMod q, ZMod.stdAddChar (a*x^2+b*x) := by
  have he :
      (∑ x : ZMod q, ZMod.stdAddChar (a*(x+t)^2+b*(x+t))) =
        ∑ x : ZMod q, ZMod.stdAddChar (a*x^2+b*x) :=
    Fintype.sum_equiv (Equiv.addRight t) _ _ (fun _ => rfl)
  rw [← he,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

                                                                    
                                                                    
theorem bourgainQuadraticGauss_inverse_shift (q : ℕ) [NeZero q]
    (a r b t : ℤ) (har : (q : ℤ) ∣ a*r-1) :
    bourgainQuadraticGauss q a (b+2*t) =
      (𝐞 (-((r : ℝ)*(t : ℝ)^2+(r : ℝ)*(b : ℝ)*(t : ℝ))/(q : ℝ)) : ℂ)*
        bourgainQuadraticGauss q a b := by
  have har' : (a : ZMod q)*(r : ZMod q) = 1 := by
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (a*r-1) q).mpr har
    simpa only [Int.cast_sub,Int.cast_mul,Int.cast_one,sub_eq_zero] using hz
  have hs := bourgain_modular_gauss_shift q (a : ZMod q) (b : ZMod q)
    ((r : ZMod q)*(t : ZMod q))
  have hc : (b : ZMod q)+2*(a : ZMod q)*((r : ZMod q)*(t : ZMod q)) =
      ((b+2*t : ℤ) : ZMod q) := by
    push_cast
    calc
      _ = (b : ZMod q)+2*((a : ZMod q)*(r : ZMod q))*(t : ZMod q) := by ring
      _ = _ := by rw [har']; ring
  have hp :
      -((a : ZMod q)*((r : ZMod q)*(t : ZMod q))^2+
        (b : ZMod q)*((r : ZMod q)*(t : ZMod q))) =
          ((-(r*t^2+r*b*t) : ℤ) : ZMod q) := by
    push_cast
    calc
      _ = -(((a : ZMod q)*(r : ZMod q))*(r : ZMod q)*(t : ZMod q)^2+
        (r : ZMod q)*(b : ZMod q)*(t : ZMod q)) := by ring
      _ = _ := by rw [har']; ring
  rw [hc,hp,bourgain_modular_character] at hs
  push_cast at hs
  simpa only [bourgain_gauss_fin_sum,Int.cast_add,Int.cast_mul,Int.cast_ofNat] using hs



private def bourgainCubicMorseCoordinate (u : ℝ) : ℝ := (u-1)*Real.sqrt (u+2)

private def bourgainCubicMorseRange : Set ℝ := bourgainCubicMorseCoordinate '' Ioo 0 3

private def bourgainCubicMorseInverse : ℝ → ℝ :=
  Function.invFunOn bourgainCubicMorseCoordinate (Icc 0 3)

private theorem bourgainCubicMorseCoordinate_contDiffAt {u : ℝ} (hu : -2 < u) :
    ContDiffAt ℝ ∞ bourgainCubicMorseCoordinate u := by
  exact (contDiffAt_id.sub contDiffAt_const).mul
    ((contDiffAt_id.add contDiffAt_const).sqrt (by linarith : u+2 ≠ 0))

private theorem bourgainCubicMorseCoordinate_hasDerivAt {u : ℝ} (hu : -2 < u) :
    HasDerivAt bourgainCubicMorseCoordinate (3*(u+1)/(2*Real.sqrt (u+2))) u := by
  have hs : Real.sqrt (u+2) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  have hsq := Real.sq_sqrt (show 0 ≤ u+2 by linarith)
  convert ((hasDerivAt_id u).sub_const 1).mul
    (((hasDerivAt_id u).add_const 2).sqrt (by linarith : u+2 ≠ 0)) using 1
  · rfl
  · dsimp only [id_eq]
    field_simp [hs]
    nlinarith only [hsq]

private theorem bourgainCubicMorseCoordinate_deriv_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < deriv bourgainCubicMorseCoordinate u := by
  rw [(bourgainCubicMorseCoordinate_hasDerivAt (by linarith : -2 < u)).deriv]
  positivity

private theorem bourgainCubicMorseCoordinate_strictMonoOn :
    StrictMonoOn bourgainCubicMorseCoordinate (Icc 0 3) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 3)
  · intro u hu
    exact (bourgainCubicMorseCoordinate_contDiffAt (by linarith [hu.1])).continuousAt.continuousWithinAt
  · intro u hu
    exact bourgainCubicMorseCoordinate_deriv_pos (interior_subset hu).1

private theorem bourgainCubicMorseCoordinate_normalForm {u : ℝ} (hu : 0 ≤ u) :
    u^3-3*u = bourgainCubicMorseCoordinate u ^2-2 := by
  unfold bourgainCubicMorseCoordinate
  rw [mul_pow,Real.sq_sqrt (by linarith : 0 ≤ u+2)]
  ring

private theorem bourgainCubicMorseInverse_coordinate {u : ℝ} (hu : u ∈ Icc 0 3) :
    bourgainCubicMorseInverse (bourgainCubicMorseCoordinate u) = u :=
  bourgainCubicMorseCoordinate_strictMonoOn.injOn.leftInvOn_invFunOn hu

private theorem bourgainCubicMorseInverse_mem {z : ℝ} (hz : z ∈ bourgainCubicMorseRange) :
    bourgainCubicMorseInverse z ∈ Ioo 0 3 := by
  obtain ⟨u,hu,rfl⟩ := hz
  rw [bourgainCubicMorseInverse_coordinate ⟨hu.1.le,hu.2.le⟩]
  exact hu

private theorem bourgainCubicMorseCoordinate_inverse {z : ℝ} (hz : z ∈ bourgainCubicMorseRange) :
    bourgainCubicMorseCoordinate (bourgainCubicMorseInverse z) = z := by
  apply Function.invFunOn_eq
  obtain ⟨u,hu,rfl⟩ := hz
  exact ⟨u,⟨hu.1.le,hu.2.le⟩,rfl⟩

private theorem bourgainCubicMorseCoordinate_hasStrictDerivAt {u : ℝ} (hu : 0 ≤ u) :
    HasStrictDerivAt bourgainCubicMorseCoordinate (deriv bourgainCubicMorseCoordinate u) u :=
  (bourgainCubicMorseCoordinate_contDiffAt (by linarith : -2 < u)).hasStrictDerivAt (by simp)

private theorem bourgainCubicMorseInverse_hasStrictDerivAt {z : ℝ}
    (hz : z ∈ bourgainCubicMorseRange) :
    HasStrictDerivAt bourgainCubicMorseInverse
      (deriv bourgainCubicMorseCoordinate (bourgainCubicMorseInverse z))⁻¹ z := by
  obtain ⟨u,hu,rfl⟩ := hz
  rw [bourgainCubicMorseInverse_coordinate ⟨hu.1.le,hu.2.le⟩]
  apply (bourgainCubicMorseCoordinate_hasStrictDerivAt hu.1.le).to_local_left_inverse
    (bourgainCubicMorseCoordinate_deriv_pos hu.1.le).ne'
  filter_upwards [isOpen_Ioo.mem_nhds hu] with x hx
  exact bourgainCubicMorseInverse_coordinate ⟨hx.1.le,hx.2.le⟩

private theorem bourgainCubicMorseRange_isOpen : IsOpen bourgainCubicMorseRange := by
  apply isOpen_iff_mem_nhds.mpr
  rintro z ⟨u,hu,rfl⟩
  have hd := bourgainCubicMorseCoordinate_hasStrictDerivAt hu.1.le
  have hi := Filter.image_mem_map (m := bourgainCubicMorseCoordinate) (isOpen_Ioo.mem_nhds hu)
  rwa [hd.map_nhds_eq (bourgainCubicMorseCoordinate_deriv_pos hu.1.le).ne'] at hi

private theorem bourgainCubicMorseInverse_contDiffAt {z : ℝ}
    (hz : z ∈ bourgainCubicMorseRange) :
    ContDiffAt ℝ ∞ bourgainCubicMorseInverse z := by
  obtain ⟨u,hu,rfl⟩ := hz
  have hc := bourgainCubicMorseCoordinate_contDiffAt (by linarith [hu.1] : -2 < u)
  have hd := bourgainCubicMorseCoordinate_hasStrictDerivAt hu.1.le
  have he := hd.hasStrictFDerivAt_equiv (bourgainCubicMorseCoordinate_deriv_pos hu.1.le).ne'
  have hg : ∀ᶠ x in 𝓝 u,
      bourgainCubicMorseInverse (bourgainCubicMorseCoordinate x) = x := by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with x hx
    exact bourgainCubicMorseInverse_coordinate ⟨hx.1.le,hx.2.le⟩
  exact (hc.to_localInverse he.hasFDerivAt (by simp)).congr_of_eventuallyEq
    (he.localInverse_unique hg)

private theorem bourgainCubicMorseInverse_deriv_pos {z : ℝ} (hz : z ∈ bourgainCubicMorseRange) :
    0 < deriv bourgainCubicMorseInverse z := by
  rw [(bourgainCubicMorseInverse_hasStrictDerivAt hz).hasDerivAt.deriv]
  exact inv_pos.mpr (bourgainCubicMorseCoordinate_deriv_pos (bourgainCubicMorseInverse_mem hz).1.le)

private theorem bourgainCubicMorseRange_zero : (0 : ℝ) ∈ bourgainCubicMorseRange := by
  refine ⟨1,by constructor <;> norm_num,?_⟩
  norm_num [bourgainCubicMorseCoordinate]

private theorem bourgainCubicMorseInverse_zero : bourgainCubicMorseInverse 0 = 1 := by
  have h := bourgainCubicMorseInverse_coordinate (show (1 : ℝ) ∈ Icc 0 3 by constructor <;> norm_num)
  simpa only [bourgainCubicMorseCoordinate,sub_self,zero_mul] using h

private theorem bourgainCubicMorseInverse_deriv_zero :
    deriv bourgainCubicMorseInverse 0 = (Real.sqrt 3)⁻¹ := by
  rw [(bourgainCubicMorseInverse_hasStrictDerivAt bourgainCubicMorseRange_zero).hasDerivAt.deriv,
    bourgainCubicMorseInverse_zero,
    (bourgainCubicMorseCoordinate_hasDerivAt (show (-2 : ℝ) < 1 by norm_num)).deriv]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hn : Real.sqrt 3 ≠ 0 := by positivity
  norm_num
  field_simp
  nlinarith only [hs]


private def bourgainCubicMorseWeight (χ : ℝ → ℝ) : ℝ → ℝ :=
  bourgainCubicMorseRange.indicator
    (fun z => χ (bourgainCubicMorseInverse z)*deriv bourgainCubicMorseInverse z)

private theorem bourgainCubicMorseWeight_tsupport {χ : ℝ → ℝ}
    (hs : tsupport χ ⊆ Ioo (0 : ℝ) 3) :
    tsupport (bourgainCubicMorseWeight χ) ⊆ bourgainCubicMorseCoordinate '' tsupport χ := by
  have hc : IsCompact (bourgainCubicMorseCoordinate '' tsupport χ) := by
    have hcχ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport χ) (hs.trans Ioo_subset_Icc_self)
    exact hcχ.image (by unfold bourgainCubicMorseCoordinate; fun_prop)
  apply closure_minimal _ hc.isClosed
  intro z hz
  have hr : z ∈ bourgainCubicMorseRange := by
    by_contra hn
    exact hz (Set.indicator_of_notMem hn _)
  refine ⟨bourgainCubicMorseInverse z,?_,bourgainCubicMorseCoordinate_inverse hr⟩
  apply subset_tsupport χ
  intro hzero
  apply hz
  simp only [bourgainCubicMorseWeight,Set.indicator_of_mem hr,hzero,zero_mul]

private theorem bourgainCubicMorseWeight_contDiff {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (0 : ℝ) 3) :
    ContDiff ℝ ∞ (bourgainCubicMorseWeight χ) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ bourgainCubicMorseRange
  · have hi := bourgainCubicMorseInverse_contDiffAt hz
    apply ((hχ.contDiffAt.comp z hi).mul (hi.derivWithin (by simp))).congr_of_eventuallyEq
    filter_upwards [bourgainCubicMorseRange_isOpen.mem_nhds hz] with w hw
    exact Set.indicator_of_mem hw _
  · have hn : z ∉ tsupport (bourgainCubicMorseWeight χ) :=
      fun h => hz (image_mono hs (bourgainCubicMorseWeight_tsupport hs h))
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hn)

private theorem bourgainCubicMorseWeight_hasCompactSupport {χ : ℝ → ℝ}
    (hs : tsupport χ ⊆ Ioo (0 : ℝ) 3) :
    HasCompactSupport (bourgainCubicMorseWeight χ) := by
  have hcχ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport χ) (hs.trans Ioo_subset_Icc_self)
  have hc := hcχ.image (show Continuous bourgainCubicMorseCoordinate by
    unfold bourgainCubicMorseCoordinate; fun_prop)
  exact hc.of_isClosed_subset (isClosed_tsupport _) (bourgainCubicMorseWeight_tsupport hs)

private theorem bourgainCubicMorseWeight_zero (χ : ℝ → ℝ) :
    bourgainCubicMorseWeight χ 0 = χ 1*(Real.sqrt 3)⁻¹ := by
  rw [bourgainCubicMorseWeight,Set.indicator_of_mem bourgainCubicMorseRange_zero,
    bourgainCubicMorseInverse_zero,bourgainCubicMorseInverse_deriv_zero]

private theorem bourgainCubicMorse_integral {χ : ℝ → ℝ}
    (hs : tsupport χ ⊆ Ioo (0 : ℝ) 3) (g : ℝ → ℂ) :
    (∫ u : ℝ, (χ u : ℂ)*g u) =
      ∫ z : ℝ, (bourgainCubicMorseWeight χ z : ℂ)*g (bourgainCubicMorseInverse z) := by
  have hi : InjOn bourgainCubicMorseInverse bourgainCubicMorseRange := by
    intro z hz w hw he
    have h := congrArg bourgainCubicMorseCoordinate he
    simpa only [bourgainCubicMorseCoordinate_inverse hz,
      bourgainCubicMorseCoordinate_inverse hw] using h
  have himage : bourgainCubicMorseInverse '' bourgainCubicMorseRange = Ioo 0 3 := by
    apply Subset.antisymm
    · rintro u ⟨z,hz,rfl⟩
      exact bourgainCubicMorseInverse_mem hz
    · intro u hu
      exact ⟨bourgainCubicMorseCoordinate u,⟨u,hu,rfl⟩,
        bourgainCubicMorseInverse_coordinate ⟨hu.1.le,hu.2.le⟩⟩
  have hd : ∀ z ∈ bourgainCubicMorseRange, HasDerivWithinAt bourgainCubicMorseInverse
      (deriv bourgainCubicMorseInverse z) bourgainCubicMorseRange z :=
    fun _ hz => (bourgainCubicMorseInverse_hasStrictDerivAt hz).hasDerivAt
      |>.differentiableAt.hasDerivAt.hasDerivWithinAt
  have hr := bourgainCubicMorseRange_isOpen.measurableSet
  have hsource : (∫ u in Ioo (0 : ℝ) 3, (χ u : ℂ)*g u) =
      ∫ u : ℝ, (χ u : ℂ)*g u := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    have hz := image_eq_zero_of_notMem_tsupport (fun h => hu (hs h))
    simp only [hz,Complex.ofReal_zero,zero_mul]
  have h := integral_image_eq_integral_abs_deriv_smul hr hd hi (fun u => (χ u : ℂ)*g u)
  rw [himage,hsource] at h
  rw [h,← integral_indicator hr]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ bourgainCubicMorseRange
  · rw [Set.indicator_of_mem hz,bourgainCubicMorseWeight,Set.indicator_of_mem hz,
      abs_of_pos (bourgainCubicMorseInverse_deriv_pos hz),Complex.real_smul,Complex.ofReal_mul]
    ring
  · rw [Set.indicator_of_notMem hz,bourgainCubicMorseWeight,Set.indicator_of_notMem hz,
      Complex.ofReal_zero,zero_mul]

private theorem bourgainCubicMorse_character_integral {χ : ℝ → ℝ}
    (hs : tsupport χ ⊆ Ioo (0 : ℝ) 3) (Λ : ℝ) :
    (∫ u : ℝ, (χ u : ℂ)*(𝐞 (Λ*(u^3-3*u)) : ℂ)) =
      (𝐞 (-2*Λ) : ℂ)*
        ∫ z : ℝ, (bourgainCubicMorseWeight χ z : ℂ)*(𝐞 (Λ*z^2) : ℂ) := by
  rw [bourgainCubicMorse_integral hs,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ bourgainCubicMorseRange
  · have hu := bourgainCubicMorseInverse_mem hz
    rw [bourgainCubicMorseCoordinate_normalForm hu.1.le,bourgainCubicMorseCoordinate_inverse hz,
      show Λ*(z^2-2) = -2*Λ+Λ*z^2 by ring,AddChar.map_add_eq_mul,Circle.coe_mul]
    ring
  · simp only [bourgainCubicMorseWeight,Set.indicator_of_notMem hz,Complex.ofReal_zero,
      zero_mul,mul_zero]


                                                                      
                                                                    
private theorem exists_bourgain_cubic_window_stationary {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (0 : ℝ) 3) :
    ∃ C > (0 : ℝ), ∀ Λ : ℝ, 0 < Λ →
      ‖(∫ u : ℝ, (χ u : ℂ)*(𝐞 (Λ*(u^3-3*u)) : ℂ))-
        (χ 1 : ℂ)*(𝐞 ((1 : ℝ)/8-2*Λ) : ℂ)/(Real.sqrt (6*Λ) : ℂ)‖ ≤ C/Λ := by
  let W := bourgainCubicMorseWeight χ
  have hW : ContDiff ℝ ∞ W := bourgainCubicMorseWeight_contDiff hχ hs
  have hcompact : HasCompactSupport W := bourgainCubicMorseWeight_hasCompactSupport hs
  have hsW : Function.support W ⊆ Ioc (-7 : ℝ) 7 := by
    intro z hz
    obtain ⟨u,hu,rfl⟩ := bourgainCubicMorseWeight_tsupport hs (subset_tsupport W hz)
    have hu' := hs hu
    have ha : |u-1| ≤ 2 := by rw [abs_le]; constructor <;> linarith [hu'.1,hu'.2]
    have hb : Real.sqrt (u+2) ≤ 3 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by nlinarith [hu'.2]⟩
    have hab : |bourgainCubicMorseCoordinate u| ≤ 6 := by
      rw [bourgainCubicMorseCoordinate,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
      nlinarith [mul_le_mul ha hb (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
    rw [abs_le] at hab
    constructor <;> linarith [hab.1,hab.2]
  have hc2 : HasCompactSupport (iteratedDeriv 2 W) := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hcompact.deriv.deriv
  have hc3 : HasCompactSupport (iteratedDeriv 3 W) := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hcompact.deriv.deriv.deriv
  obtain ⟨M2,hM2⟩ := hc2.exists_bound_of_continuous (hW.continuous_iteratedDeriv 2 (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  obtain ⟨M3,hM3⟩ := hc3.exists_bound_of_continuous (hW.continuous_iteratedDeriv 3 (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3))
  let Q := quadraticRemainderConstant 7 |W 0| M2 M3
  refine ⟨1+|Q|,by positivity,?_⟩
  intro Λ hΛ
  have hg := sargos_positive_quadratic_global_remainder hW
    (show 0 < 2*Λ by positivity) (show (0 : ℝ) < 7 by norm_num) hsW le_rfl
    (fun z => by simpa only [Real.norm_eq_abs] using hM2 z)
    (fun z => by simpa only [Real.norm_eq_abs] using hM3 z)
  have hmain :
      (𝐞 (-2*Λ) : ℂ)*((W 0 : ℂ)*
        ((𝐞 ((1 : ℝ)/8) : ℂ)/(Real.sqrt (2*Λ) : ℂ))) =
      (χ 1 : ℂ)*(𝐞 ((1 : ℝ)/8-2*Λ) : ℂ)/(Real.sqrt (6*Λ) : ℂ) := by
    have hsqrt : Real.sqrt (6*Λ) = Real.sqrt 3*Real.sqrt (2*Λ) := by
      rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring
    rw [show (1 : ℝ)/8-2*Λ = -2*Λ+1/8 by ring,
      AddChar.map_add_eq_mul,Circle.coe_mul,hsqrt]
    dsimp only [W]
    rw [bourgainCubicMorseWeight_zero]
    push_cast
    ring
  rw [bourgainCubicMorse_character_integral hs,← hmain,← mul_sub,norm_mul,Circle.norm_coe,one_mul]
  have heq : (2*Λ)/2 = Λ := by ring
  simp only [heq] at hg
  apply hg.trans
  change Q/(2*Λ) ≤ (1+|Q|)/Λ
  rw [show Q/(2*Λ) = (Q/2)/Λ by ring]
  apply div_le_div_of_nonneg_right _ hΛ.le
  linarith [le_abs_self Q,abs_nonneg Q]


private theorem bourgain_cubic_nonstationary {f : ℝ → ℝ} {a b M Λ : ℝ}
    (hf : MathCollab.Density.Stronger.Atkinson.IntervalC1Bound (fun u => (f u : ℂ)) a b M)
    (hab : a ≤ b) (ha : 0 ≤ a) (hΛ : 0 < Λ)
    (hgap : b ≤ 1/2 ∨ 3/2 ≤ a) :
    ‖∫ u in a..b, (f u : ℂ)*(𝐞 (Λ*(u^3-3*u)) : ℂ)‖ ≤ 2*M/(Λ*Real.pi) := by
  let φ : ℝ → ℝ := fun u => -(Λ*(u^3-3*u))
  have hd (u : ℝ) : deriv φ u = 3*Λ*(1-u^2) := by
    have h := (((hasDerivAt_id u).pow 3).sub ((hasDerivAt_id u).const_mul 3)).const_mul Λ
    have hh : HasDerivAt φ (3*Λ*(1-u^2)) u := by
      convert h.neg using 1
      · rfl
      · norm_num
        ring
    exact hh.deriv
  have hm : AntitoneOn (deriv φ) (Icc a b) := by
    intro u hu v hv huv
    rw [hd,hd]
    have hsq := mul_self_le_mul_self (ha.trans hu.1) huv
    nlinarith [mul_le_mul_of_nonneg_left hsq hΛ.le]
  have hg : (∀ u ∈ Icc a b, Λ ≤ deriv φ u) ∨
      (∀ u ∈ Icc a b, deriv φ u ≤ -Λ) := by
    rcases hgap with hl | hr
    · left
      intro u hu
      rw [hd]
      have hsq := mul_self_le_mul_self (ha.trans hu.1) (hu.2.trans hl)
      nlinarith [mul_le_mul_of_nonneg_left hsq hΛ.le]
    · right
      intro u hu
      rw [hd]
      have hsq := mul_self_le_mul_self (show (0 : ℝ) ≤ 3/2 by norm_num) (hr.trans hu.1)
      nlinarith [mul_le_mul_of_nonneg_left hsq hΛ.le]
  have hc : ContDiff ℝ 2 φ := by dsimp only [φ]; fun_prop
  have h := IntervalC1Bound.fourierChar_of_closed_slope_gap (φ:=φ) (J:=Set.univ) hf hab hΛ isOpen_univ (subset_univ _)
    (fun u _ => hc.contDiffAt) hm hg
  have he :
      (∫ u in a..b, (f u : ℂ)*(𝐞 (Λ*(u^3-3*u)) : ℂ)) =
        starRingEnd ℂ (∫ u in a..b, (f u : ℂ)*(𝐞 (φ u) : ℂ)) := by
    simp only [intervalIntegral.integral_of_le hab]
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [] with u
    dsimp only [φ]
    rw [map_mul (starRingEnd ℂ),Complex.conj_ofReal,sargos_fourier_conj]
  rw [he,Complex.norm_conj]
  exact h


private theorem exists_bourgain_cubic_stationary_truncation :
    ∃ C > (0 : ℝ), ∀ Λ : ℝ, 0 < Λ → ∀ R : ℝ, 2 ≤ R →
      ‖(∫ u in (0 : ℝ)..R, (𝐞 (Λ*(u^3-3*u)) : ℂ))-
        (𝐞 ((1 : ℝ)/8-2*Λ) : ℂ)/(Real.sqrt (6*Λ) : ℂ)‖ ≤ C/Λ := by
  let χ := modelPhaseBufferedCutoff 0 2 (1/4)
  have hχ : ContDiff ℝ ∞ χ := modelPhaseBufferedCutoff_contDiff _ _ _
  have hχsupp : tsupport χ ⊆ Icc (1/4 : ℝ) (7/4) := by
    simpa only [zero_add,show (2 : ℝ)-1/4 = 7/4 by ring] using
      (modelPhaseBufferedCutoff_tsupport (l := 0) (r := 2) (by norm_num : (0 : ℝ) < 1/4))
  have hs : tsupport χ ⊆ Ioo (0 : ℝ) 3 := by
    intro u hu
    have h := hχsupp hu
    constructor <;> linarith [h.1,h.2]
  have hχone {u : ℝ} (hu : u ∈ Icc (1/2 : ℝ) (3/2)) : χ u = 1 := by
    exact modelPhaseBufferedCutoff_one (by norm_num) (by linarith [hu.1]) (by linarith [hu.2])
  obtain ⟨C,hC,hmain⟩ := exists_bourgain_cubic_window_stationary hχ hs
  refine ⟨C+12/Real.pi,by positivity,?_⟩
  intro Λ hΛ R hR
  let k : ℝ → ℂ := fun u => (𝐞 (Λ*(u^3-3*u)) : ℂ)
  let F : ℝ → ℂ := fun u => (1-(χ u : ℂ))*k u
  have hk : Continuous k := by
    dsimp only [k]
    simp only [Real.fourierChar_apply]
    fun_prop
  have hχk : Continuous (fun u => (χ u : ℂ)*k u) :=
    (Complex.continuous_ofReal.comp hχ.continuous).mul hk
  have hFc : Continuous F := (continuous_const.sub
    (Complex.continuous_ofReal.comp hχ.continuous)).mul hk
  have hsource :
      (∫ u : ℝ, (χ u : ℂ)*k u) = ∫ u in (0 : ℝ)..R, (χ u : ℂ)*k u := by
    symm
    apply intervalIntegral.integral_eq_integral_of_support_subset
    intro u hu
    have hχu : u ∈ tsupport χ := by
      apply subset_tsupport χ
      intro hz
      exact hu (by simp only [hz,Complex.ofReal_zero,zero_mul])
    have hb := hχsupp hχu
    constructor <;> linarith [hb.1,hb.2]
  have hzero : (∫ u in (1/2 : ℝ)..(3/2 : ℝ), F u) = 0 := by
    rw [← intervalIntegral.integral_zero]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 3/2)] at hu
    simp only [F,hχone hu,Complex.ofReal_one,sub_self,zero_mul]
  have hsplit : (∫ u in (0 : ℝ)..R, F u) =
      (∫ u in (0 : ℝ)..(1/2 : ℝ), F u)+(∫ u in (3/2 : ℝ)..R, F u) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hFc.intervalIntegrable 0 (1/2)) (hFc.intervalIntegrable (1/2) R)]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hFc.intervalIntegrable (1/2) (3/2)) (hFc.intervalIntegrable (3/2) R),hzero,zero_add]
  have htail {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a)
      (hgap : b ≤ 1/2 ∨ 3/2 ≤ a) :
      ‖∫ u in a..b, F u‖ ≤ 6/(Λ*Real.pi) := by
    have hf1 : MathCollab.Density.Stronger.Atkinson.IntervalC1Bound (fun _ : ℝ => ((1 : ℝ) : ℂ)) a b 1 := by
      simpa only [Complex.ofReal_one,norm_one] using MathCollab.Density.Stronger.Atkinson.intervalC1Bound_const (1 : ℂ) a b
    have hplain := bourgain_cubic_nonstationary hf1 hab ha hΛ hgap
    have hcut := bourgain_cubic_nonstationary
      (intervalC1Bound_modelPhaseBufferedCutoff
        (l := 0) (r := 2) (by norm_num : (0 : ℝ) < 1/4) hab) hab ha hΛ hgap
    have he : (∫ u in a..b, F u) =
        (∫ u in a..b, k u)-(∫ u in a..b, (χ u : ℂ)*k u) := by
      rw [← intervalIntegral.integral_sub (hk.intervalIntegrable a b) (hχk.intervalIntegrable a b)]
      apply intervalIntegral.integral_congr
      intro u hu
      dsimp only [F]
      ring
    rw [he]
    apply (norm_sub_le _ _).trans
    have hp : ‖∫ u in a..b, k u‖ ≤ 2/(Λ*Real.pi) := by
      simpa only [Complex.ofReal_one,one_mul,mul_one] using hplain
    exact (add_le_add hp hcut).trans_eq (by ring)
  have herror : ‖(∫ u in (0 : ℝ)..R, k u)-(∫ u : ℝ, (χ u : ℂ)*k u)‖ ≤ 12/(Λ*Real.pi) := by
    rw [hsource,← intervalIntegral.integral_sub (hk.intervalIntegrable 0 R)
      (hχk.intervalIntegrable 0 R)]
    have he : (fun u => k u-(χ u : ℂ)*k u) = F := by funext u; dsimp only [F]; ring
    rw [he,hsplit]
    exact (norm_add_le _ _).trans
      ((add_le_add (htail (by norm_num) (by norm_num) (Or.inl le_rfl))
        (htail (by linarith) (by norm_num) (Or.inr le_rfl))).trans_eq (by ring))
  have hm := hmain Λ hΛ
  rw [hχone (show (1 : ℝ) ∈ Icc (1/2) (3/2) by constructor <;> norm_num),
    Complex.ofReal_one,one_mul] at hm
  have he :
      (∫ u in (0 : ℝ)..R, k u)-(𝐞 ((1 : ℝ)/8-2*Λ) : ℂ)/(Real.sqrt (6*Λ) : ℂ) =
      ((∫ u in (0 : ℝ)..R, k u)-(∫ u : ℝ, (χ u : ℂ)*k u))+
        ((∫ u : ℝ, (χ u : ℂ)*k u)-
          (𝐞 ((1 : ℝ)/8-2*Λ) : ℂ)/(Real.sqrt (6*Λ) : ℂ)) := by ring
  change ‖(∫ u in (0 : ℝ)..R, k u)-
    (𝐞 ((1 : ℝ)/8-2*Λ) : ℂ)/(Real.sqrt (6*Λ) : ℂ)‖ ≤ _
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add herror hm).trans_eq (by ring))


                                                                        
                                                                        
                                                                            
theorem exists_bourgain_cubic_stationary_prefix :
    ∃ C > (0 : ℝ), ∀ μ : ℝ, 0 < μ → ∀ β : ℝ, 0 < β →
      let r := Real.sqrt (β/(3*μ))
      ∀ R : ℝ, 2*r ≤ R →
        ‖(∫ x in (0 : ℝ)..R, (𝐞 (μ*x^3-β*x) : ℂ))-
          (𝐞 ((1 : ℝ)/8-2*μ*r^3) : ℂ)/(Real.sqrt (6*μ*r) : ℂ)‖ ≤ C/β := by
  obtain ⟨C,hC,h⟩ := exists_bourgain_cubic_stationary_truncation
  refine ⟨3*C,by positivity,?_⟩
  intro μ hμ β hβ r R hR
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr2 : r^2 = β/(3*μ) := Real.sq_sqrt (by positivity)
  have hβr : β = 3*μ*r^2 := by
    rw [hr2]
    field_simp
  let Λ := μ*r^3
  have hΛ : 0 < Λ := by dsimp only [Λ]; positivity
  have hphase (u : ℝ) : μ*(r*u)^3-β*(r*u) = Λ*(u^3-3*u) := by
    rw [hβr]
    dsimp only [Λ]
    ring
  have hscale :
      (∫ x in (0 : ℝ)..R, (𝐞 (μ*x^3-β*x) : ℂ)) =
        (r : ℂ)*(∫ u in (0 : ℝ)..(R/r), (𝐞 (Λ*(u^3-3*u)) : ℂ)) := by
    have hs := intervalIntegral.smul_integral_comp_mul_left
      (fun x : ℝ => (𝐞 (μ*x^3-β*x) : ℂ)) (a := 0) (b := R/r) r
    simp only [mul_zero,mul_div_cancel₀ _ hr.ne',Complex.real_smul,hphase] at hs
    exact hs.symm
  have hroot : Real.sqrt (6*Λ) = r*Real.sqrt (6*μ*r) := by
    rw [show 6*Λ = r^2*(6*μ*r) by dsimp only [Λ]; ring,
      Real.sqrt_mul (sq_nonneg r),Real.sqrt_sq hr.le]
  have hmain :
      (𝐞 ((1 : ℝ)/8-2*μ*r^3) : ℂ)/(Real.sqrt (6*μ*r) : ℂ) =
        (r : ℂ)*((𝐞 ((1 : ℝ)/8-2*Λ) : ℂ)/(Real.sqrt (6*Λ) : ℂ)) := by
    rw [hroot]
    have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    have harg : (1 : ℝ)/8-2*μ*r^3 = 1/8-2*Λ := by dsimp only [Λ]; ring
    rw [harg,Complex.ofReal_mul]
    field_simp
  rw [hscale,hmain,← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  apply (mul_le_mul_of_nonneg_left
    (h Λ hΛ (R/r) ((le_div_iff₀ hr).mpr hR)) hr.le).trans_eq
  rw [hβr]
  dsimp only [Λ]
  field_simp


private theorem bourgain_cubic_endpoint_gap {a b Λ L : ℝ}
    (hab : a ≤ b) (ha : 0 ≤ a) (hΛ : 0 < Λ) (hL : 0 < L)
    (hgap : L ≤ 3*Λ*(1-b^2) ∨ L ≤ 3*Λ*(a^2-1)) :
    ‖∫ u in a..b, (𝐞 (Λ*(u^3-3*u)) : ℂ)‖ ≤ 1/(L*Real.pi) := by
  let φ : ℝ → ℝ := fun u => -(Λ*(u^3-3*u))
  have hd (u : ℝ) : deriv φ u = 3*Λ*(1-u^2) := by
    have h := (((hasDerivAt_id u).pow 3).sub ((hasDerivAt_id u).const_mul 3)).const_mul Λ
    have hh : HasDerivAt φ (3*Λ*(1-u^2)) u := by
      convert h.neg using 1
      · rfl
      · norm_num
        ring
    exact hh.deriv
  have hm : AntitoneOn (deriv φ) (Icc a b) := by
    intro u hu v hv huv
    rw [hd,hd]
    have hsq := mul_self_le_mul_self (ha.trans hu.1) huv
    nlinarith [mul_le_mul_of_nonneg_left hsq hΛ.le]
  have hg : (∀ u ∈ Icc a b, L ≤ deriv φ u) ∨
      (∀ u ∈ Icc a b, deriv φ u ≤ -L) := by
    rcases hgap with hl | hr
    · left
      intro u hu
      rw [hd]
      have hsq := mul_self_le_mul_self (ha.trans hu.1) hu.2
      nlinarith [mul_le_mul_of_nonneg_left hsq hΛ.le]
    · right
      intro u hu
      rw [hd]
      have hsq := mul_self_le_mul_self ha hu.1
      nlinarith [mul_le_mul_of_nonneg_left hsq hΛ.le]
  have hc : ContDiff ℝ 2 φ := by dsimp only [φ]; fun_prop
  have h := norm_fourierCharIntegral_le_of_slope_gap hab hL (fun u _ => hc.contDiffAt) hm hg
  have he :
      (∫ u in a..b, (𝐞 (Λ*(u^3-3*u)) : ℂ)) =
        starRingEnd ℂ (∫ u in a..b, (𝐞 (φ u) : ℂ)) := by
    simp only [intervalIntegral.integral_of_le hab]
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [] with u
    exact (sargos_fourier_conj _).symm
  rw [he,Complex.norm_conj]
  exact h



private def bourgainCubicPrefix (Λ u : ℝ) : ℂ :=
  ∫ x in (0 : ℝ)..u, (𝐞 (Λ*(x^3-3*x)) : ℂ)

private def bourgainCubicStationaryMain (Λ : ℝ) : ℂ :=
  (𝐞 ((1 : ℝ)/8-2*Λ) : ℂ)/(Real.sqrt (6*Λ) : ℂ)

private theorem bourgainCubicPrefix_continuous (Λ : ℝ) :
    Continuous (fun x : ℝ => (𝐞 (Λ*(x^3-3*x)) : ℂ)) := by
  simp only [Real.fourierChar_apply]
  fun_prop

private theorem bourgainCubicPrefix_sub (Λ a b : ℝ) :
    bourgainCubicPrefix Λ b-bourgainCubicPrefix Λ a =
      ∫ x in a..b, (𝐞 (Λ*(x^3-3*x)) : ℂ) := by
  unfold bourgainCubicPrefix
  exact intervalIntegral.integral_interval_sub_left
    ((bourgainCubicPrefix_continuous Λ).intervalIntegrable 0 b)
    ((bourgainCubicPrefix_continuous Λ).intervalIntegrable 0 a)

private theorem bourgainCubicPrefix_norm_sub (Λ : ℝ) {a b : ℝ} (hab : a ≤ b) :
    ‖bourgainCubicPrefix Λ b-bourgainCubicPrefix Λ a‖ ≤ b-a := by
  rw [bourgainCubicPrefix_sub]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := 1)
    (f := fun x : ℝ => (𝐞 (Λ*(x^3-3*x)) : ℂ))
    (fun x _ => (Circle.norm_coe _).le)
  simpa only [one_mul,abs_of_nonneg (sub_nonneg.mpr hab)] using h

private theorem bourgainCubicStationaryMain_norm {Λ : ℝ} (hΛ : 0 < Λ) :
    ‖bourgainCubicStationaryMain Λ‖ ≤ 1/Real.sqrt Λ := by
  simp only [bourgainCubicStationaryMain,norm_div,Circle.norm_coe,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hΛ)
    (Real.sqrt_le_sqrt (by linarith))

private theorem exists_bourgainCubicPrefix_far :
    ∃ C > (0 : ℝ), ∀ Λ > (0 : ℝ), ∀ u ≥ (2 : ℝ),
      ‖bourgainCubicPrefix Λ u-bourgainCubicStationaryMain Λ‖ ≤ C/Λ := by
  obtain ⟨C,hC,h⟩ := exists_bourgain_cubic_stationary_prefix
  refine ⟨C/3,by positivity,?_⟩
  intro Λ hΛ u hu
  have hr : Real.sqrt ((3*Λ)/(3*Λ)) = 1 := by
    rw [div_self (by positivity : 3*Λ ≠ 0),Real.sqrt_one]
  have hp := h Λ hΛ (3*Λ) (by positivity)
  dsimp only at hp
  rw [hr] at hp
  have hh := hp u (by simpa using hu)
  have he (x : ℝ) : Λ*x^3-3*Λ*x = Λ*(x^3-3*x) := by ring
  simpa only [he,one_pow,mul_one,bourgainCubicPrefix,bourgainCubicStationaryMain,
    div_div] using hh

private theorem bourgainCubicPrefix_left {Λ u : ℝ}
    (hΛ : 0 < Λ) (hu : 0 ≤ u) (hu1 : u < 1) :
    ‖bourgainCubicPrefix Λ u‖ ≤ 1/(Λ*(1-u^2)) := by
  have hg : 0 < 1-u^2 := by nlinarith
  have h := bourgain_cubic_endpoint_gap hu (by norm_num) hΛ
    (by positivity : 0 < 3*Λ*(1-u^2)) (Or.inl le_rfl)
  apply h.trans
  apply one_div_le_one_div_of_le (by positivity : 0 < Λ*(1-u^2))
  nlinarith [mul_pos (mul_pos hΛ hg) (show 0 < 3*Real.pi-1 by linarith [Real.pi_gt_three])]

private theorem bourgainCubicPrefix_right {Λ a b : ℝ}
    (hΛ : 0 < Λ) (ha : 1 < a) (hab : a ≤ b) :
    ‖bourgainCubicPrefix Λ b-bourgainCubicPrefix Λ a‖ ≤ 1/(Λ*(a^2-1)) := by
  have hg : 0 < a^2-1 := by nlinarith
  rw [bourgainCubicPrefix_sub]
  have h := bourgain_cubic_endpoint_gap hab (by linarith) hΛ
    (by positivity : 0 < 3*Λ*(a^2-1)) (Or.inr le_rfl)
  apply h.trans
  apply one_div_le_one_div_of_le (by positivity : 0 < Λ*(a^2-1))
  nlinarith [mul_pos (mul_pos hΛ hg) (show 0 < 3*Real.pi-1 by linarith [Real.pi_gt_three])]

private theorem exists_bourgainCubicPrefix_reciprocal :
    ∃ C > (0 : ℝ), ∀ Λ > (0 : ℝ), ∀ u ≥ (0 : ℝ), u ≠ 1 →
      ‖bourgainCubicPrefix Λ u-
        (if 1 ≤ u then bourgainCubicStationaryMain Λ else 0)‖ ≤
          C/Λ+1/(Λ*|u^2-1|) := by
  obtain ⟨C,hC,hfar⟩ := exists_bourgainCubicPrefix_far
  refine ⟨C,hC,?_⟩
  intro Λ hΛ u hu hne
  by_cases h : u < 1
  · rw [ite_eq_right (not_le.mpr h),sub_zero,abs_of_neg (by nlinarith : u^2-1 < 0)]
    have hh := bourgainCubicPrefix_left hΛ hu h
    have he : -(u^2-1) = 1-u^2 := by ring
    rw [he]
    exact hh.trans (le_add_of_nonneg_left (by positivity))
  · have hu1 : 1 < u := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hne)
    rw [ite_eq_left hu1.le,abs_of_pos (by nlinarith : 0 < u^2-1)]
    have htail := bourgainCubicPrefix_right hΛ hu1 (le_max_right 2 u)
    have hf := hfar Λ hΛ (max 2 u) (le_max_left 2 u)
    have he : bourgainCubicPrefix Λ u-bourgainCubicStationaryMain Λ =
        (bourgainCubicPrefix Λ (max 2 u)-bourgainCubicStationaryMain Λ)-
          (bourgainCubicPrefix Λ (max 2 u)-bourgainCubicPrefix Λ u) := by ring
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add hf htail)



private theorem exists_bourgainCubicPrefix_cap :
    ∃ C > (0 : ℝ), ∀ Λ > (0 : ℝ), ∀ u ≥ (0 : ℝ),
      ‖bourgainCubicPrefix Λ u-
        (if 1 ≤ u then bourgainCubicStationaryMain Λ else 0)‖ ≤
          C/Λ+4/Real.sqrt Λ := by
  obtain ⟨C,hC,hfar⟩ := exists_bourgainCubicPrefix_far
  refine ⟨C+2,by positivity,?_⟩
  intro Λ hΛ u hu
  have hM : ‖if 1 ≤ u then bourgainCubicStationaryMain Λ else 0‖ ≤ 1/Real.sqrt Λ := by
    split_ifs
    · exact bourgainCubicStationaryMain_norm hΛ
    · simp only [norm_zero]; positivity
  have hzero : bourgainCubicPrefix Λ 0 = 0 := by simp [bourgainCubicPrefix]
  have hCP : 0 < C/Λ := by positivity
  by_cases h2 : 2 ≤ u
  · rw [ite_eq_left (by linarith : 1 ≤ u)]
    exact (hfar Λ hΛ u h2).trans (by
      have hh : C/Λ ≤ (C+2)/Λ := div_le_div_of_nonneg_right (by linarith) hΛ.le
      exact hh.trans (le_add_of_nonneg_right (by positivity)))
  have hu2 : u < 2 := lt_of_not_ge h2
  by_cases hΛ1 : Λ ≤ 1
  · have hJ := bourgainCubicPrefix_norm_sub Λ hu
    rw [hzero,sub_zero,sub_zero] at hJ
    have htwo : 2 ≤ 2/Λ := (le_div_iff₀ hΛ).mpr (by nlinarith)
    have hnorm := (norm_sub_le _ _).trans (add_le_add hJ hM)
    have hs : 0 ≤ 1/Real.sqrt Λ := by positivity
    have he : (C+2)/Λ = C/Λ+2/Λ := by ring
    rw [he,show (4 : ℝ)/Real.sqrt Λ = 4*(1/Real.sqrt Λ) by ring]
    nlinarith
  have hΛlarge : 1 < Λ := lt_of_not_ge hΛ1
  let h : ℝ := 1/Real.sqrt Λ
  have hh : 0 < h := by dsimp only [h]; positivity
  have hh1 : h ≤ 1 := by
    dsimp only [h]
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hΛ)).mpr
    nlinarith [Real.sq_sqrt hΛ.le,Real.sqrt_nonneg Λ]
  have hidentity : 1/(Λ*h) = h := by
    have hs := Real.sq_sqrt hΛ.le
    dsimp only [h]
    field_simp
    nlinarith
  have hleft {v : ℝ} (hv : 0 ≤ v) (hvl : v ≤ 1-h) :
      ‖bourgainCubicPrefix Λ v‖ ≤ h := by
    have hv1 : v < 1 := by linarith
    apply (bourgainCubicPrefix_left hΛ hv hv1).trans
    rw [← hidentity]
    apply one_div_le_one_div_of_le (by positivity : 0 < Λ*h)
    apply mul_le_mul_of_nonneg_left _ hΛ.le
    nlinarith [mul_nonneg hv (show 0 ≤ 1-v by linarith)]
  have hright {v : ℝ} (hvr : 1+h ≤ v) :
      ‖bourgainCubicPrefix Λ v-bourgainCubicStationaryMain Λ‖ ≤ C/Λ+h := by
    have hv1 : 1 < v := by linarith
    have ht := bourgainCubicPrefix_right hΛ hv1 (le_max_right 2 v)
    have ht' : ‖bourgainCubicPrefix Λ (max 2 v)-bourgainCubicPrefix Λ v‖ ≤ h := by
      apply ht.trans
      rw [← hidentity]
      apply one_div_le_one_div_of_le (by positivity : 0 < Λ*h)
      apply mul_le_mul_of_nonneg_left _ hΛ.le
      nlinarith [sq_nonneg (v-1)]
    have hf := hfar Λ hΛ (max 2 v) (le_max_left 2 v)
    have he : bourgainCubicPrefix Λ v-bourgainCubicStationaryMain Λ =
        (bourgainCubicPrefix Λ (max 2 v)-bourgainCubicStationaryMain Λ)-
          (bourgainCubicPrefix Λ (max 2 v)-bourgainCubicPrefix Λ v) := by ring
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add hf ht')
  rw [show (4 : ℝ)/Real.sqrt Λ = 4*h by dsimp only [h]; ring]
  by_cases hur : 1+h ≤ u
  · rw [ite_eq_left (by linarith : 1 ≤ u)]
    apply (hright hur).trans
    have hc : C/Λ ≤ (C+2)/Λ := div_le_div_of_nonneg_right (by linarith) hΛ.le
    linarith
  have hJ : ‖bourgainCubicPrefix Λ u‖ ≤ 3*h := by
    by_cases hul : u ≤ 1-h
    · exact (hleft hu hul).trans (by linarith)
    · have hdist := bourgainCubicPrefix_norm_sub Λ (le_of_not_ge hul)
      have hl := hleft (show 0 ≤ 1-h by linarith) le_rfl
      have he : bourgainCubicPrefix Λ u =
          (bourgainCubicPrefix Λ u-bourgainCubicPrefix Λ (1-h))+
            bourgainCubicPrefix Λ (1-h) := by ring
      rw [he]
      exact (norm_add_le _ _).trans ((add_le_add hdist hl).trans (by linarith))
  exact ((norm_sub_le _ _).trans (add_le_add hJ hM)).trans (by
    change 3*h+h ≤ (C+2)/Λ+4*h
    have hc : 0 ≤ (C+2)/Λ := by positivity
    linarith)



private def bourgainCubicEndpointError (Λ u : ℝ) : ℝ :=
  if u = 1 then 1/Real.sqrt Λ
  else min (1/Real.sqrt Λ) (1/(Λ*|u^2-1|))

private theorem bourgainCubicEndpointError_nonneg {Λ u : ℝ} (hΛ : 0 < Λ) :
    0 ≤ bourgainCubicEndpointError Λ u := by
  unfold bourgainCubicEndpointError
  split_ifs
  · positivity
  · exact le_min (by positivity) (by positivity)

private theorem exists_bourgainCubicPrefix_minimum :
    ∃ C > (0 : ℝ), ∀ Λ > (0 : ℝ), ∀ u ≥ (0 : ℝ),
      ‖bourgainCubicPrefix Λ u-
        (if 1 ≤ u then bourgainCubicStationaryMain Λ else 0)‖ ≤
          C/Λ+4*bourgainCubicEndpointError Λ u := by
  obtain ⟨C,hC,hcap⟩ := exists_bourgainCubicPrefix_cap
  obtain ⟨D,hD,hrec⟩ := exists_bourgainCubicPrefix_reciprocal
  refine ⟨C+D,by positivity,?_⟩
  intro Λ hΛ u hu
  have hc : C/Λ ≤ (C+D)/Λ := div_le_div_of_nonneg_right (by linarith) hΛ.le
  have hd : D/Λ ≤ (C+D)/Λ := div_le_div_of_nonneg_right (by linarith) hΛ.le
  have hp := hcap Λ hΛ u hu
  rw [show (4 : ℝ)/Real.sqrt Λ = 4*(1/Real.sqrt Λ) by ring] at hp
  by_cases he : u = 1
  · simp only [bourgainCubicEndpointError,ite_eq_left he]
    exact hp.trans (add_le_add hc le_rfl)
  · simp only [bourgainCubicEndpointError,ite_eq_right he]
    rcases le_total (1/Real.sqrt Λ) (1/(Λ*|u^2-1|)) with h | h
    · rw [min_eq_left h]
      exact hp.trans (add_le_add hc le_rfl)
    · rw [min_eq_right h]
      have hr := hrec Λ hΛ u hu he
      have hn : 0 ≤ 1/(Λ*|u^2-1|) := by positivity
      linarith



private theorem exists_bourgainCubic_finite_stationary :
    ∃ C > (0 : ℝ), ∀ Λ > (0 : ℝ), ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      ‖(∫ u in a..b, (𝐞 (Λ*(u^3-3*u)) : ℂ))-
        (if a ≤ 1 ∧ 1 ≤ b then bourgainCubicStationaryMain Λ else 0)‖ ≤
          C/Λ+5*(bourgainCubicEndpointError Λ a+bourgainCubicEndpointError Λ b) := by
  obtain ⟨C,hC,hprefix⟩ := exists_bourgainCubicPrefix_minimum
  refine ⟨2*C,by positivity,?_⟩
  intro Λ hΛ a b ha hab
  have hpa := hprefix Λ hΛ a ha
  have hpb := hprefix Λ hΛ b (ha.trans hab)
  have hea := bourgainCubicEndpointError_nonneg (u := a) hΛ
  have heb := bourgainCubicEndpointError_nonneg (u := b) hΛ
  rw [← bourgainCubicPrefix_sub]
  let Ma : ℂ := if 1 ≤ a then bourgainCubicStationaryMain Λ else 0
  let Mb : ℂ := if 1 ≤ b then bourgainCubicStationaryMain Λ else 0
  have he : bourgainCubicPrefix Λ b-bourgainCubicPrefix Λ a-(Mb-Ma) =
      (bourgainCubicPrefix Λ b-Mb)-(bourgainCubicPrefix Λ a-Ma) := by ring
  have hbase :
      ‖bourgainCubicPrefix Λ b-bourgainCubicPrefix Λ a-(Mb-Ma)‖ ≤
        2*C/Λ+4*(bourgainCubicEndpointError Λ a+bourgainCubicEndpointError Λ b) := by
    rw [he]
    exact (norm_sub_le _ _).trans ((add_le_add hpb hpa).trans_eq (by ring))
  by_cases ha1 : a = 1
  · have hb1 : 1 ≤ b := by simpa only [ha1] using hab
    have hdiff : Mb-Ma = 0 := by simp [Ma,Mb,ha1,hb1]
    rw [hdiff,sub_zero] at hbase
    rw [ite_eq_left ⟨ha1.le,hb1⟩]
    have hM := bourgainCubicStationaryMain_norm hΛ
    have hEa : bourgainCubicEndpointError Λ a = 1/Real.sqrt Λ := by
      simp [bourgainCubicEndpointError,ha1]
    have hnorm := (norm_sub_le _ _).trans (add_le_add hbase hM)
    rw [← hEa] at hnorm
    linarith
  · have hid : Mb-Ma =
        if a ≤ 1 ∧ 1 ≤ b then bourgainCubicStationaryMain Λ else 0 := by
      dsimp only [Ma,Mb]
      by_cases hal : a < 1
      · have han : ¬1 ≤ a := not_le.mpr hal
        by_cases hb : 1 ≤ b <;> simp [han,hb,hal.le]
      · have hag : 1 < a := lt_of_le_of_ne (le_of_not_gt hal) (Ne.symm ha1)
        have hb : 1 ≤ b := hag.le.trans hab
        simp [hag.le,not_le.mpr hag,hb]
    rw [hid] at hbase
    linarith



private def bourgainCubicSourceEndpointError (Λ a u : ℝ) : ℝ :=
  if u = 1 then 1/Real.sqrt (Λ*a)
  else min (1/Real.sqrt (Λ*a)) (1/(Λ*|u^2-1|))

private theorem bourgainCubicSourceEndpointError_nonneg {Λ a u : ℝ}
    (hΛ : 0 < Λ) (ha : 0 < a) :
    0 ≤ bourgainCubicSourceEndpointError Λ a u := by
  unfold bourgainCubicSourceEndpointError
  split_ifs
  · positivity
  · exact le_min (by positivity) (by positivity)

private theorem bourgainCubicEndpointError_source {Λ a u : ℝ}
    (hΛ : 0 < Λ) (ha : 0 < a) (ha2 : a ≤ 2) :
    bourgainCubicEndpointError Λ u ≤ 2*bourgainCubicSourceEndpointError Λ a u := by
  have hs : 1/Real.sqrt Λ ≤ 2/Real.sqrt (Λ*a) := by
    apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hΛ) (Real.sqrt_pos.mpr (by positivity))).mpr
    have h1 := Real.sq_sqrt hΛ.le
    have h2 := Real.sq_sqrt (show 0 ≤ Λ*a by positivity)
    have h3 := Real.sqrt_nonneg Λ
    have h4 := Real.sqrt_nonneg (Λ*a)
    have h5 := mul_le_mul_of_nonneg_left ha2 hΛ.le
    nlinarith
  rw [show (2 : ℝ)/Real.sqrt (Λ*a) = 2*(1/Real.sqrt (Λ*a)) by ring] at hs
  by_cases hu : u = 1
  · simpa only [bourgainCubicEndpointError,bourgainCubicSourceEndpointError,ite_eq_left hu] using hs
  · simp only [bourgainCubicEndpointError,bourgainCubicSourceEndpointError,ite_eq_right hu]
    rcases le_total (1/Real.sqrt (Λ*a)) (1/(Λ*|u^2-1|)) with h | h
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans hs
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans (by
        have hn : 0 ≤ 1/(Λ*|u^2-1|) := by positivity
        linarith)

private theorem exists_bourgainCubic_source_stationary :
    ∃ C > (0 : ℝ), ∀ Λ > (0 : ℝ), ∀ a b : ℝ, 0 < a → a ≤ b →
      ‖(∫ u in a..b, (𝐞 (Λ*(u^3-3*u)) : ℂ))-
        (if a ≤ 1 ∧ 1 ≤ b then bourgainCubicStationaryMain Λ else 0)‖ ≤
          C/Λ+10*(bourgainCubicSourceEndpointError Λ a a+
            bourgainCubicSourceEndpointError Λ a b) := by
  obtain ⟨C,hC,hfinite⟩ := exists_bourgainCubic_finite_stationary
  refine ⟨C+1,by positivity,?_⟩
  intro Λ hΛ a b ha hab
  have hEa := bourgainCubicSourceEndpointError_nonneg (u := a) hΛ ha
  have hEb := bourgainCubicSourceEndpointError_nonneg (u := b) hΛ ha
  by_cases ha2 : a ≤ 2
  · have h := hfinite Λ hΛ a b ha.le hab
    have hca := bourgainCubicEndpointError_source (u := a) hΛ ha ha2
    have hcb := bourgainCubicEndpointError_source (u := b) hΛ ha ha2
    have hc : C/Λ ≤ (C+1)/Λ := div_le_div_of_nonneg_right (by linarith) hΛ.le
    linarith
  · have ha2' : 2 < a := lt_of_not_ge ha2
    rw [ite_eq_right (by intro h; linarith [h.1]),sub_zero,← bourgainCubicPrefix_sub]
    have h := bourgainCubicPrefix_right hΛ (by linarith : 1 < a) hab
    have hrec : 1/(Λ*(a^2-1)) ≤ 1/Λ := by
      apply one_div_le_one_div_of_le hΛ
      nlinarith [mul_pos hΛ (show 0 < a^2-2 by nlinarith)]
    have hc : 1/Λ ≤ (C+1)/Λ := div_le_div_of_nonneg_right (by linarith) hΛ.le
    exact (h.trans hrec).trans (hc.trans (le_add_of_nonneg_right (by positivity)))

                                                                    
                                                                      
def bourgainCubicEndpointBudget (μ N β x : ℝ) : ℝ :=
  if 3*μ*x^2 = β then 1/Real.sqrt (μ*N)
  else min (1/Real.sqrt (μ*N)) (1/|3*μ*x^2-β|)

private theorem bourgainCubicEndpointBudget_nonneg {μ N β x : ℝ}
    (hμ : 0 < μ) (hN : 0 < N) :
    0 ≤ bourgainCubicEndpointBudget μ N β x := by
  unfold bourgainCubicEndpointBudget
  split_ifs
  · positivity
  · exact le_min (by positivity) (by positivity)

private theorem bourgainCubicEndpointBudget_scale {μ N β r x : ℝ}
    (hμ : 0 < μ) (hN : 0 < N) (hr : 0 < r) (hx : 0 ≤ x)
    (hβ : β = 3*μ*r^2) :
    r*bourgainCubicSourceEndpointError (μ*r^3) (N/r) (x/r) ≤
      3*bourgainCubicEndpointBudget μ N β x := by
  have hz : x/r = 1 ↔ 3*μ*x^2 = β := by
    rw [div_eq_one_iff_eq hr.ne']
    constructor
    · intro h; rw [h,hβ]
    · intro h
      have hs : x^2 = r^2 :=
        mul_left_cancel₀ (by positivity : 3*μ ≠ 0) (by simpa only [hβ] using h)
      nlinarith
  have hroot : Real.sqrt ((μ*r^3)*(N/r)) = r*Real.sqrt (μ*N) := by
    have he : (μ*r^3)*(N/r) = r^2*(μ*N) := by field_simp
    rw [he,Real.sqrt_mul (sq_nonneg r),Real.sqrt_sq hr.le]
  have hcap : r*(1/Real.sqrt ((μ*r^3)*(N/r))) = 1/Real.sqrt (μ*N) := by
    rw [hroot]
    field_simp
  have hgap : (μ*r^3)*|(x/r)^2-1| = (r/3)*|3*μ*x^2-β| := by
    have he : (μ*r^3)*((x/r)^2-1) = (r/3)*(3*μ*x^2-β) := by
      rw [hβ]
      field_simp
    have habs := congrArg abs he
    simpa only [abs_mul,abs_of_pos (show 0 < μ*r^3 by positivity),
      abs_of_pos (show 0 < r/3 by positivity)] using habs
  have hrec : r*(1/((μ*r^3)*|(x/r)^2-1|)) = 3*(1/|3*μ*x^2-β|) := by
    rw [hgap]
    field_simp
  have hc : 0 ≤ 1/Real.sqrt (μ*N) := by positivity
  by_cases he : 3*μ*x^2 = β
  · rw [bourgainCubicSourceEndpointError,ite_eq_left (hz.mpr he),
      bourgainCubicEndpointBudget,ite_eq_left he,hcap]
    linarith
  · rw [bourgainCubicSourceEndpointError,ite_eq_right (fun h => he (hz.mp h)),
      bourgainCubicEndpointBudget,ite_eq_right he]
    rcases le_total (1/Real.sqrt (μ*N)) (1/|3*μ*x^2-β|) with h | h
    · rw [min_eq_left h]
      apply (mul_le_mul_of_nonneg_left (min_le_left _ _) hr.le).trans
      rw [hcap]
      linarith
    · rw [min_eq_right h]
      exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hr.le).trans_eq hrec

private theorem exists_bourgain_cubic_finite_positive :
    ∃ C > (0 : ℝ), ∀ μ > (0 : ℝ), ∀ β > (0 : ℝ),
      let r := Real.sqrt (β/(3*μ))
      ∀ N N₁ : ℝ, 0 < N → N ≤ N₁ →
        ‖(∫ x in N..N₁, (𝐞 (μ*x^3-β*x) : ℂ))-
          (if 3*μ*N^2 ≤ β ∧ β ≤ 3*μ*N₁^2 then
            (𝐞 ((1 : ℝ)/8-2*μ*r^3) : ℂ)/(Real.sqrt (6*μ*r) : ℂ) else 0)‖ ≤
          C/β+30*(bourgainCubicEndpointBudget μ N β N+
            bourgainCubicEndpointBudget μ N β N₁) := by
  obtain ⟨C,hC,h⟩ := exists_bourgainCubic_source_stationary
  refine ⟨3*C,by positivity,?_⟩
  intro μ hμ β hβ r N N₁ hN hNN
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr2 : r^2 = β/(3*μ) := Real.sq_sqrt (by positivity)
  have hβr : β = 3*μ*r^2 := by rw [hr2]; field_simp
  have hN₁ : 0 < N₁ := hN.trans_le hNN
  let Λ := μ*r^3
  have hΛ : 0 < Λ := by dsimp only [Λ]; positivity
  have hphase (u : ℝ) : μ*(r*u)^3-β*(r*u) = Λ*(u^3-3*u) := by
    rw [hβr]
    dsimp only [Λ]
    ring
  have hscale :
      (∫ x in N..N₁, (𝐞 (μ*x^3-β*x) : ℂ)) =
        (r : ℂ)*(∫ u in (N/r)..(N₁/r), (𝐞 (Λ*(u^3-3*u)) : ℂ)) := by
    have hs := intervalIntegral.smul_integral_comp_mul_left
      (fun x : ℝ => (𝐞 (μ*x^3-β*x) : ℂ)) (a := N/r) (b := N₁/r) r
    simp only [mul_div_cancel₀ _ hr.ne',Complex.real_smul,hphase] at hs
    exact hs.symm
  have hroot : Real.sqrt (6*Λ) = r*Real.sqrt (6*μ*r) := by
    rw [show 6*Λ = r^2*(6*μ*r) by dsimp only [Λ]; ring,
      Real.sqrt_mul (sq_nonneg r),Real.sqrt_sq hr.le]
  have hmain :
      (𝐞 ((1 : ℝ)/8-2*μ*r^3) : ℂ)/(Real.sqrt (6*μ*r) : ℂ) =
        (r : ℂ)*bourgainCubicStationaryMain Λ := by
    unfold bourgainCubicStationaryMain
    rw [hroot]
    have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    have harg : (1 : ℝ)/8-2*μ*r^3 = 1/8-2*Λ := by dsimp only [Λ]; ring
    rw [harg,Complex.ofReal_mul]
    field_simp
  have hδ : (N/r ≤ 1 ∧ 1 ≤ N₁/r) ↔ (3*μ*N^2 ≤ β ∧ β ≤ 3*μ*N₁^2) := by
    simp only [div_le_one hr,le_div_iff₀ hr,one_mul,hβr,
      mul_le_mul_iff_right₀ (show 0 < 3*μ by positivity),
      sq_le_sq₀ hN.le hr.le,sq_le_sq₀ hr.le hN₁.le]
  have hind :
      (if 3*μ*N^2 ≤ β ∧ β ≤ 3*μ*N₁^2 then
          (𝐞 ((1 : ℝ)/8-2*μ*r^3) : ℂ)/(Real.sqrt (6*μ*r) : ℂ) else 0) =
        (r : ℂ)*(if N/r ≤ 1 ∧ 1 ≤ N₁/r then bourgainCubicStationaryMain Λ else 0) := by
    by_cases hd : N/r ≤ 1 ∧ 1 ≤ N₁/r
    · rw [ite_eq_left hd,ite_eq_left (hδ.mp hd),hmain]
    · rw [ite_eq_right hd,ite_eq_right (fun h => hd (hδ.mpr h)),mul_zero]
  rw [hscale,hind,← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  apply (mul_le_mul_of_nonneg_left
    (h Λ hΛ (N/r) (N₁/r) (by positivity) (div_le_div_of_nonneg_right hNN hr.le)) hr.le).trans
  have hEa := bourgainCubicEndpointBudget_scale hμ hN hr hN.le hβr
  have hEb := bourgainCubicEndpointBudget_scale hμ hN hr hN₁.le hβr
  have hcoef : r*(C/Λ) = 3*C/β := by
    rw [hβr]
    dsimp only [Λ]
    field_simp
  change r*(C/Λ+10*(bourgainCubicSourceEndpointError (μ*r^3) (N/r) (N/r)+
    bourgainCubicSourceEndpointError (μ*r^3) (N/r) (N₁/r))) ≤ _
  nlinarith

private theorem bourgain_cubic_negative_linear {μ β N N₁ : ℝ}
    (hμ : 0 < μ) (hβ : β < 0) (hN : 0 ≤ N) (hNN : N ≤ N₁) :
    ‖∫ x in N..N₁, (𝐞 (μ*x^3-β*x) : ℂ)‖ ≤ 1/|β| := by
  let φ : ℝ → ℝ := fun x => -(μ*x^3-β*x)
  have hd (x : ℝ) : deriv φ x = β-3*μ*x^2 := by
    have h := (((hasDerivAt_id x).pow 3).const_mul μ).sub
      ((hasDerivAt_id x).const_mul β)
    have hh : HasDerivAt φ (β-3*μ*x^2) x := by
      convert h.neg using 1
      · rfl
      · norm_num
        ring
    exact hh.deriv
  have hm : AntitoneOn (deriv φ) (Icc N N₁) := by
    intro x hx y hy hxy
    rw [hd,hd]
    have hsq := mul_self_le_mul_self (hN.trans hx.1) hxy
    nlinarith [mul_le_mul_of_nonneg_left hsq hμ.le]
  have hg : (∀ x ∈ Icc N N₁, -β ≤ deriv φ x) ∨
      (∀ x ∈ Icc N N₁, deriv φ x ≤ -(-β)) := by
    right
    intro x hx
    rw [hd]
    nlinarith [mul_nonneg hμ.le (sq_nonneg x)]
  have hc : ContDiff ℝ 2 φ := by dsimp only [φ]; fun_prop
  have hb := norm_fourierCharIntegral_le_of_slope_gap hNN (neg_pos.mpr hβ)
    (fun x _ => hc.contDiffAt) hm hg
  have he :
      (∫ x in N..N₁, (𝐞 (μ*x^3-β*x) : ℂ)) =
        starRingEnd ℂ (∫ x in N..N₁, (𝐞 (φ x) : ℂ)) := by
    simp only [intervalIntegral.integral_of_le hNN]
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [] with x
    exact (sargos_fourier_conj _).symm
  rw [he,Complex.norm_conj,abs_of_neg hβ]
  apply hb.trans
  apply one_div_le_one_div_of_le (neg_pos.mpr hβ)
  nlinarith [mul_pos (neg_pos.mpr hβ) (show 0 < Real.pi-1 by linarith [Real.pi_gt_three])]

                                                                         
                                                                     
                                                                       
                                                          
theorem exists_bourgain_cubic_finite_stationary :
    ∃ C > (0 : ℝ), ∀ μ > (0 : ℝ), ∀ β : ℝ, β ≠ 0 →
      let r := Real.sqrt (β/(3*μ))
      ∀ N N₁ : ℝ, 0 < N → N ≤ N₁ →
        ‖(∫ x in N..N₁, (𝐞 (μ*x^3-β*x) : ℂ))-
          (if 3*μ*N^2 ≤ β ∧ β ≤ 3*μ*N₁^2 then
            (𝐞 ((1 : ℝ)/8-2*μ*r^3) : ℂ)/(Real.sqrt (6*μ*r) : ℂ) else 0)‖ ≤
          C*(1/|β|+bourgainCubicEndpointBudget μ N β N+
            bourgainCubicEndpointBudget μ N β N₁) := by
  obtain ⟨C,hC,hpositive⟩ := exists_bourgain_cubic_finite_positive
  refine ⟨C+31,by positivity,?_⟩
  intro μ hμ β hβ r N N₁ hN hNN
  have hEa := bourgainCubicEndpointBudget_nonneg (β := β) (x := N) hμ hN
  have hEb := bourgainCubicEndpointBudget_nonneg (β := β) (x := N₁) hμ hN
  rcases lt_or_gt_of_ne hβ with hneg | hpos
  · have hδ : ¬(3*μ*N^2 ≤ β ∧ β ≤ 3*μ*N₁^2) := by
      intro h
      have hp : 0 < 3*μ*N^2 := by positivity
      linarith [h.1]
    rw [ite_eq_right hδ,sub_zero]
    apply (bourgain_cubic_negative_linear hμ hneg hN.le hNN).trans
    have hb : 0 ≤ 1/|β| := by positivity
    have hc : 1/|β| ≤ (C+31)*(1/|β|) := by nlinarith
    exact hc.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  · have h := hpositive μ hμ β hpos N N₁ hN hNN
    rw [abs_of_pos hpos]
    apply h.trans
    have hc : C/β ≤ (C+31)/β := div_le_div_of_nonneg_right (by linarith) hpos.le
    have he : 30*(bourgainCubicEndpointBudget μ N β N+
        bourgainCubicEndpointBudget μ N β N₁) ≤
        (C+31)*(bourgainCubicEndpointBudget μ N β N+
          bourgainCubicEndpointBudget μ N β N₁) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    exact (add_le_add hc he).trans_eq (by ring)


private def bourgainCubicSharpCutoff (N N₁ : ℝ) : ℝ → ℝ :=
  modelPhaseBufferedCutoff (N-1) (N₁+1) (1/2)

private theorem bourgainCubicSharpCutoff_tsupport (N N₁ : ℝ) :
    tsupport (bourgainCubicSharpCutoff N N₁) ⊆ Icc (N-1/2) (N₁+1/2) := by
  have h := modelPhaseBufferedCutoff_tsupport
    (l := N-1) (r := N₁+1) (by norm_num : (0 : ℝ) < 1/2)
  simpa only [bourgainCubicSharpCutoff,
    show N-1+(1/2:ℝ)=N-1/2 by ring,
    show N₁+1-(1/2:ℝ)=N₁+1/2 by ring] using h

private theorem exists_bourgain_cubic_cutoff_fourier_decay :
    ∃ C ≥ (1 : ℝ), ∀ μ N N₁ : ℝ, 0 < μ → 1 ≤ N → N ≤ N₁ → N₁ ≤ 2*N →
      μ*N^2 ≤ 1 → ∀ y : ℝ,
        (1+|y|)^2*‖bourgainCubicFourierMode
          (fun x => (bourgainCubicSharpCutoff N N₁ x : ℂ)) μ y‖ ≤ C*N := by
  obtain ⟨M,hM,hcut⟩ := modelPhaseBufferedCutoff_uniform_c2
  let D : ℝ := (2*Real.pi)^2*32^2+2*Real.pi*32+1
  have hD : 1 ≤ D := by
    have hn : 0 ≤ (2*Real.pi)^2*32^2+2*Real.pi*32 := by positivity
    dsimp only [D]
    linarith
  have hM0 : 0 ≤ M := by linarith
  have hD0 : 0 ≤ D := by linarith
  let K : ℝ := 16*M*D
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨8*(1+K),by linarith,?_⟩
  intro μ N N₁ hμ hN hNN hN₁ hμN y
  let χ := bourgainCubicSharpCutoff N N₁
  let F : ℝ → ℝ := fun x => μ*x^3
  let f : ℝ → ℂ := fun x => (χ x : ℂ)*(𝐞 (μ*x^3) : ℂ)
  have hχ : ContDiff ℝ ∞ χ := modelPhaseBufferedCutoff_contDiff _ _ _
  have hχs := bourgainCubicSharpCutoff_tsupport N N₁
  have hf : ContDiff ℝ ∞ f := by
    dsimp only [f]
    simp only [Real.fourierChar_apply]
    have hp : ContDiff ℝ ∞ (fun x : ℝ => 2*Real.pi*(μ*x^3)) := by fun_prop
    exact (Complex.ofRealCLM.contDiff.comp hχ).mul
      (((Complex.ofRealCLM.contDiff.comp hp).mul contDiff_const).cexp)
  have hd (x : ℝ) : deriv F x = 3*μ*x^2 := by
    have hh : HasDerivAt F (3*μ*x^2) x := by
      convert (((hasDerivAt_id x).pow 3).const_mul μ) using 1
      · rfl
      · norm_num
        ring
    exact hh.deriv
  have hdd (x : ℝ) : iteratedDeriv 2 F x = 6*μ*x := by
    rw [iteratedDeriv_succ,iteratedDeriv_one,show deriv F = fun x => 3*μ*x^2 from funext hd]
    have hh : HasDerivAt (fun y : ℝ => 3*μ*y^2) (6*μ*x) x := by
      convert (((hasDerivAt_id x).pow 2).const_mul (3*μ)) using 1
      · rfl
      · norm_num
        ring
    exact hh.deriv
  have hxbound {x : ℝ} (hx : x ∈ Icc (N-1/2) (N₁+1/2)) :
      0 ≤ x ∧ x ≤ (5/2)*N := by constructor <;> linarith [hx.1,hx.2]
  have hphase : IntervalC2Bound (fun x => (𝐞 (μ*x^3) : ℂ))
      (N-1/2) (N₁+1/2) D 2 := by
    have h := intervalC2Bound_fourierChar_of_derivative_bounds (F := F)
      (a := N-1/2) (b := N₁+1/2) (by norm_num : (1 : ℝ) ≤ 32)
      (by intro x hx; dsimp only [F]; fun_prop)
      (by
        intro x hx
        rw [hd,abs_of_nonneg (by positivity : 0 ≤ 3*μ*x^2)]
        have hb := hxbound hx
        have hs := mul_self_le_mul_self hb.1 hb.2
        have hm := mul_le_mul_of_nonneg_left hs hμ.le
        nlinarith)
      (by
        intro x hx
        have hb := hxbound hx
        have hx0 : 0 ≤ x := hb.1
        rw [hdd,abs_of_nonneg (by positivity : 0 ≤ 6*μ*x)]
        have hN2 : N ≤ N^2 := by nlinarith
        have hmN : μ*N ≤ 1 := (mul_le_mul_of_nonneg_left hN2 hμ.le).trans hμN
        have hm := mul_le_mul_of_nonneg_left hb.2 hμ.le
        nlinarith) 1
    simpa only [F,one_mul,abs_one,show (1 : ℝ)+1 = 2 by norm_num] using h
  have hχ2 : IntervalC2Bound (fun x => (χ x : ℂ)) (N-1/2) (N₁+1/2) M 2 := by
    have h := hcut (N-1) (N₁+1) (1/2) (N-1/2) (N₁+1/2) (by norm_num)
    norm_num only [one_div,inv_inv] at h
    exact h
  have hp := hχ2.mul hphase
  have hs : Function.support f ⊆ Icc (N-1/2) (N₁+1/2) := by
    intro x hx
    apply hχs
    apply subset_tsupport χ
    intro hz
    exact hx (by simp only [f,hz,Complex.ofReal_zero,zero_mul])
  have h0 (x : ℝ) : ‖iteratedDeriv 0 f x‖ ≤ 1 := by
    simp only [iteratedDeriv_zero,f,norm_mul,Circle.norm_coe,mul_one,
      Complex.norm_real,Real.norm_eq_abs]
    dsimp only [χ,bourgainCubicSharpCutoff]
    rw [abs_of_nonneg (modelPhaseBufferedCutoff_nonneg _ _ _ _)]
    exact modelPhaseBufferedCutoff_le_one _ _ _ _
  have h2 (x : ℝ) : ‖iteratedDeriv 2 f x‖ ≤ K := by
    by_cases hx : x ∈ tsupport χ
    · have h := hp.second_le x (hχs hx)
      change ‖iteratedDeriv 2 f x‖ ≤ _
      exact h.trans_eq (by dsimp only [K]; ring)
    · have hz : f =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with u hu
        simp only [f,hu,Pi.zero_apply,Complex.ofReal_zero,zero_mul]
      rw [hz.iteratedDeriv_eq 2]
      simpa only [iteratedDeriv_const,show (2 : ℕ) ≠ 0 by norm_num,ite_false,norm_zero] using hK
  have hFourier := RiemannZeta.GuthMaynard.one_add_abs_fourier_decay_of_support_of_bounds_order
    2 hf (by linarith : N-1/2 ≤ N₁+1/2) hs (by norm_num) hK h0 h2 y
  have hmode : 𝓕 f y =
      bourgainCubicFourierMode (fun x => (χ x : ℂ)) μ y := by
    rw [Real.fourier_real_eq]
    unfold bourgainCubicFourierMode
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [Circle.smul_def,smul_eq_mul,f]
    rw [show μ*x^3-y*x = -(x*y)+μ*x^3 by ring,
      AddChar.map_add_eq_mul,Circle.coe_mul]
    ring
  rw [hmode] at hFourier
  apply hFourier.trans
  norm_num only [Nat.reducePow]
  have hlen : N₁+1/2-(N-1/2) ≤ 2*N := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hlen (show 0 ≤ 1+K by positivity)]



private theorem bourgain_cubic_weighted_gap {f : ℝ → ℝ} {a b M μ β L : ℝ}
    (hf : MathCollab.Density.Stronger.Atkinson.IntervalC1Bound (fun x => (f x : ℂ)) a b M)
    (hab : a ≤ b) (ha : 0 ≤ a) (hμ : 0 < μ) (hL : 0 < L)
    (hgap : L ≤ β-3*μ*b^2 ∨ L ≤ 3*μ*a^2-β) :
    ‖∫ x in a..b, (f x : ℂ)*(𝐞 (μ*x^3-β*x) : ℂ)‖ ≤ 2*M/(L*Real.pi) := by
  let φ : ℝ → ℝ := fun x => -(μ*x^3-β*x)
  have hd (x : ℝ) : deriv φ x = β-3*μ*x^2 := by
    have h := (((hasDerivAt_id x).pow 3).const_mul μ).sub
      ((hasDerivAt_id x).const_mul β)
    have hh : HasDerivAt φ (β-3*μ*x^2) x := by
      convert h.neg using 1
      · rfl
      · norm_num
        ring
    exact hh.deriv
  have hm : AntitoneOn (deriv φ) (Icc a b) := by
    intro x hx y hy hxy
    rw [hd,hd]
    have hs := mul_self_le_mul_self (ha.trans hx.1) hxy
    nlinarith [mul_le_mul_of_nonneg_left hs hμ.le]
  have hg : (∀ x ∈ Icc a b, L ≤ deriv φ x) ∨
      (∀ x ∈ Icc a b, deriv φ x ≤ -L) := by
    rcases hgap with hl | hr
    · left
      intro x hx
      rw [hd]
      have hs := mul_self_le_mul_self (ha.trans hx.1) hx.2
      nlinarith [mul_le_mul_of_nonneg_left hs hμ.le]
    · right
      intro x hx
      rw [hd]
      have hs := mul_self_le_mul_self ha hx.1
      nlinarith [mul_le_mul_of_nonneg_left hs hμ.le]
  have hc : ContDiff ℝ 2 φ := by dsimp only [φ]; fun_prop
  have hb := IntervalC1Bound.fourierChar_of_closed_slope_gap (φ:=φ) (J:=Set.univ) hf hab hL isOpen_univ
    (subset_univ _) (fun x _ => hc.contDiffAt) hm hg
  have he :
      (∫ x in a..b, (f x : ℂ)*(𝐞 (μ*x^3-β*x) : ℂ)) =
        starRingEnd ℂ (∫ x in a..b, (f x : ℂ)*(𝐞 (φ x) : ℂ)) := by
    simp only [intervalIntegral.integral_of_le hab]
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [map_mul,Complex.conj_ofReal]
    congr 1
    exact (sargos_fourier_conj _).symm
  rw [he,Complex.norm_conj]
  exact hb



private theorem bourgain_cubic_cutoff_difference {μ N N₁ y : ℝ}
    (hμ : 0 < μ) (hN : 1 ≤ N) (hNN : N ≤ N₁) (hN₁ : N₁ ≤ 2*N)
    (hμN : μ*N^2 ≤ 1) :
    ‖bourgainCubicFourierMode (fun x => (bourgainCubicSharpCutoff N N₁ x : ℂ)) μ y-
      (∫ x in N..N₁, (𝐞 (μ*x^3-y*x) : ℂ))‖ ≤ 130/(1+|y|) := by
  let χ := bourgainCubicSharpCutoff N N₁
  let k : ℝ → ℂ := fun x => (𝐞 (μ*x^3-y*x) : ℂ)
  let f : ℝ → ℂ := fun x => (χ x : ℂ)*k x
  have hχ : ContDiff ℝ ∞ χ := modelPhaseBufferedCutoff_contDiff _ _ _
  have hk : Continuous k := by
    simp only [k,Real.fourierChar_apply]
    fun_prop
  have hf : Continuous f := (Complex.continuous_ofReal.comp hχ.continuous).mul hk
  have hχs := bourgainCubicSharpCutoff_tsupport N N₁
  have hwhole :
      bourgainCubicFourierMode (fun x => (χ x : ℂ)) μ y =
        ∫ x in (N-1)..(N₁+1), f x := by
    unfold bourgainCubicFourierMode
    symm
    apply intervalIntegral.integral_eq_integral_of_support_subset
    intro x hx
    have hxs : x ∈ tsupport χ := by
      apply subset_tsupport χ
      intro hz
      exact hx (by simp only [f,hz,Complex.ofReal_zero,zero_mul])
    have hb := hχs hxs
    constructor <;> linarith [hb.1,hb.2]
  have hmiddle : (∫ x in N..N₁, f x) = ∫ x in N..N₁, k x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hNN] at hx
    have hone : χ x = 1 :=
      modelPhaseBufferedCutoff_one (by norm_num : (0 : ℝ) < 1/2)
        (by linarith [hx.1]) (by linarith [hx.2])
    simp only [f,hone,Complex.ofReal_one,one_mul]
  have hsplit :
      bourgainCubicFourierMode (fun x => (χ x : ℂ)) μ y-
        (∫ x in N..N₁, k x) =
          (∫ x in (N-1)..N, f x)+(∫ x in N₁..(N₁+1), f x) := by
    rw [hwhole,← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (N-1) N) (hf.intervalIntegrable N (N₁+1))]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable N N₁) (hf.intervalIntegrable N₁ (N₁+1)),hmiddle]
    ring
  change ‖bourgainCubicFourierMode (fun x => (χ x : ℂ)) μ y-
    (∫ x in N..N₁, k x)‖ ≤ _
  rw [hsplit]
  have htriv {a b : ℝ} (hab : a ≤ b) : ‖∫ x in a..b, f x‖ ≤ b-a := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := 1) (f := f) (by
        intro x hx
        simp only [f,k,norm_mul,Circle.norm_coe,mul_one,Complex.norm_real,Real.norm_eq_abs]
        dsimp only [χ,bourgainCubicSharpCutoff]
        rw [abs_of_nonneg (modelPhaseBufferedCutoff_nonneg _ _ _ _)]
        exact modelPhaseBufferedCutoff_le_one _ _ _ _)
    simpa only [one_mul,abs_of_nonneg (sub_nonneg.mpr hab)] using h
  have hden : 0 < 1+|y| := by positivity
  by_cases hy : |y| ≤ 64
  · apply (norm_add_le _ _).trans
    apply (add_le_add (htriv (show N-1 ≤ N by linarith))
      (htriv (show N₁ ≤ N₁+1 by linarith))).trans
    apply (le_div_iff₀ hden).mpr
    nlinarith
  have hy64 : 64 < |y| := lt_of_not_ge hy
  have htail {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ N₁+1) :
      ‖∫ x in a..b, f x‖ ≤ 8/(|y| *Real.pi) := by
    have hb0 : 0 ≤ b := ha.trans hab
    have hbN : b ≤ 3*N := by linarith
    have hsq := mul_self_le_mul_self hb0 hbN
    have hmb : 3*μ*b^2 ≤ 27 := by
      have hm := mul_le_mul_of_nonneg_left hsq hμ.le
      nlinarith
    have hgap : |y|/2 ≤ y-3*μ*b^2 ∨ |y|/2 ≤ 3*μ*a^2-y := by
      by_cases hy0 : 0 ≤ y
      · left
        rw [abs_of_nonneg hy0] at hy64 ⊢
        linarith
      · right
        have hn : y < 0 := lt_of_not_ge hy0
        rw [abs_of_neg hn]
        nlinarith [mul_nonneg hμ.le (sq_nonneg a)]
    have h := bourgain_cubic_weighted_gap
      (intervalC1Bound_modelPhaseBufferedCutoff (l := N-1) (r := N₁+1)
        (by norm_num : (0 : ℝ) < 1/2) hab)
      hab ha hμ (by linarith : 0 < |y|/2) hgap
    exact h.trans_eq (by ring)
  apply (norm_add_le _ _).trans
  apply (add_le_add (htail (show N-1 ≤ N by linarith) (by linarith) (by linarith))
    (htail (show N₁ ≤ N₁+1 by linarith) (by linarith) le_rfl)).trans
  have hy0 : 0 < |y| := by linarith
  have hp : 3*|y| ≤ |y| *Real.pi := by nlinarith [mul_pos hy0 (show 0 < Real.pi-3 from sub_pos.mpr Real.pi_gt_three)]
  apply (le_div_iff₀ hden).mpr
  have he : (8/(|y| *Real.pi)+8/(|y| *Real.pi))*(1+|y|) =
      16*(1+|y|)/(|y| *Real.pi) := by ring
  rw [he]
  apply (div_le_iff₀ (by positivity : 0 < |y| *Real.pi)).mpr
  nlinarith



private theorem bourgain_capped_reciprocal_sum
    (W : Finset ℝ) (w : ℝ) (L : ℕ) {A q : ℝ} (g : ℝ → ℝ)
    (hSep : MathCollab.Density.Stronger.Atkinson.IsSeparated 1 W)
    (hRange : ∀ t ∈ W, |t-w| ≤ L) (hA : 0 ≤ A) (hq : 0 ≤ q)
    (hcap : ∀ t ∈ W, g t ≤ A)
    (hrec : ∀ t ∈ W, t ≠ w → g t ≤ q/|t-w|) :
    (∑ t ∈ W, g t) ≤ 3*A+2*q*(3+2*Real.log (L+1)) := by
  classical
  let S := W.filter (fun t => |t-w| < 1)
  let T := W.filter (fun t => t ≠ w ∧ (0 : ℝ) ≤ |t-w| ∧ |t-w| < 1)
  have hT : T.card ≤ 2 := by
    simpa only [T,Nat.cast_zero,zero_add] using
      MathCollab.Density.Stronger.Atkinson.separated_annulus_card_le_two W w 0 hSep
  have hS : S.card ≤ 3 := by
    have hsub : S ⊆ insert w T := by
      intro t ht
      by_cases he : t = w
      · simp only [he,Finset.mem_insert_self]
      · apply Finset.mem_insert.mpr
        right
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp ht).1,he,abs_nonneg _,(Finset.mem_filter.mp ht).2⟩
    exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le w T).trans (by omega))
  have hp {t : ℝ} (ht : t ∈ W) :
      g t ≤ (if |t-w| < 1 then A else 0)+2*q*zetaMomentKernel t w := by
    by_cases hn : |t-w| < 1
    · rw [ite_eq_left hn]
      exact (hcap t ht).trans (le_add_of_nonneg_right
        (mul_nonneg (by positivity) (zetaMomentKernel_pos t w).le))
    · rw [ite_eq_right hn,zero_add]
      have hd : 1 ≤ |t-w| := le_of_not_gt hn
      have hd0 : 0 < |t-w| := by linarith
      have hne : t ≠ w := by intro he; simp only [he,sub_self,abs_zero] at hd; linarith
      apply (hrec t ht hne).trans
      unfold zetaMomentKernel
      rw [abs_sub_comm w t]
      have he : 2*q*(1/(1+|t-w|)) = 2*q/(1+|t-w|) := by ring
      rw [he]
      apply (div_le_div_iff₀ hd0 (by positivity : 0 < 1+|t-w|)).mpr
      nlinarith [mul_nonneg hq (sub_nonneg.mpr hd)]
  have hnear : (∑ t ∈ W, if |t-w| < 1 then A else 0) ≤ 3*A := by
    rw [← Finset.sum_filter]
    change (∑ _t ∈ S, A) ≤ _
    simp only [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hS) hA
  have hk := sum_zetaMomentKernel_le_log W w L hSep hRange
  calc
    _ ≤ ∑ t ∈ W, ((if |t-w| < 1 then A else 0)+2*q*zetaMomentKernel t w) :=
      Finset.sum_le_sum (fun t ht => hp ht)
    _ = (∑ t ∈ W, if |t-w| < 1 then A else 0)+2*q*∑ t ∈ W, zetaMomentKernel t w := by
      rw [Finset.sum_add_distrib,Finset.mul_sum]
    _ ≤ _ := add_le_add hnear (mul_le_mul_of_nonneg_left hk (by positivity))



private theorem bourgain_integer_abs_ge_one {h : ℤ} (hh : h ≠ 0) :
    1 ≤ |(h : ℝ)| := by
  rcases lt_or_gt_of_ne hh with hn | hp
  · have hz : h ≤ -1 := by omega
    have hc : (h : ℝ) ≤ -1 := by exact_mod_cast hz
    rw [abs_of_neg (by linarith : (h : ℝ) < 0)]
    linarith
  · have hz : 1 ≤ h := by omega
    have hc : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hz
    rw [abs_of_nonneg (by linarith : 0 ≤ (h : ℝ))]
    exact hc

private theorem bourgain_integer_image_separated (S : Finset ℤ) :
    MathCollab.Density.Stronger.Atkinson.IsSeparated 1 (S.image (fun h : ℤ => (h : ℝ))) := by
  classical
  intro x hx y hy hxy
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hy
  have hne : m-n ≠ 0 := by
    intro h
    exact hxy (by exact_mod_cast (sub_eq_zero.mp h))
  have h := bourgain_integer_abs_ge_one hne
  simpa only [Int.cast_sub,Real.dist_eq] using h

private theorem bourgain_integer_kernel_sum (S : Finset ℤ) (H : ℕ)
    (hRange : ∀ h ∈ S, |(h : ℝ)| ≤ H) :
    (∑ h ∈ S, 1/(1+|(h : ℝ)|)) ≤ 3+2*Real.log ((H : ℝ)+1) := by
  classical
  have hr : ∀ t ∈ S.image (fun h : ℤ => (h : ℝ)), |t-(0 : ℝ)| ≤ H := by
    intro t ht
    obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp ht
    simpa only [sub_zero] using hRange h hh
  have hk := sum_zetaMomentKernel_le_log (S.image (fun h : ℤ => (h : ℝ))) 0 H
    (bourgain_integer_image_separated S) hr
  rw [Finset.sum_image (fun _ _ _ _ h => Int.cast_injective h)] at hk
  simpa only [zetaMomentKernel,zero_sub,abs_neg] using hk

theorem bourgain_integer_reciprocal_sum (H : ℕ) :
    (∑ h ∈ (Finset.Icc (-(H : ℤ)) (H : ℤ)).erase 0, 1/|(h : ℝ)|) ≤
      2*(3+2*Real.log ((H : ℝ)+1)) := by
  let S := (Finset.Icc (-(H : ℤ)) (H : ℤ)).erase 0
  have hRange : ∀ h ∈ S, |(h : ℝ)| ≤ H := by
    intro h hh
    have hi := Finset.mem_Icc.mp (Finset.mem_of_mem_erase hh)
    apply abs_le.mpr
    constructor
    · exact_mod_cast hi.1
    · exact_mod_cast hi.2
  have hp {h : ℤ} (hh : h ∈ S) :
      1/|(h : ℝ)| ≤ 2*(1/(1+|(h : ℝ)|)) := by
    have hi := bourgain_integer_abs_ge_one (Finset.mem_erase.mp hh).1
    have he : 2*(1/(1+|(h : ℝ)|)) = 2/(1+|(h : ℝ)|) := by ring
    rw [he]
    apply (div_le_div_iff₀ (by linarith : 0 < |(h : ℝ)|) (by positivity)).mpr
    linarith
  calc
    _ ≤ ∑ h ∈ S, 2*(1/(1+|(h : ℝ)|)) := Finset.sum_le_sum (fun h hh => hp hh)
    _ = 2*∑ h ∈ S, 1/(1+|(h : ℝ)|) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (bourgain_integer_kernel_sum S H hRange) (by norm_num)

def bourgainCubicStationaryTerm (μ N N₁ β : ℝ) : ℂ :=
  let r := Real.sqrt (β/(3*μ))
  if 3*μ*N^2 ≤ β ∧ β ≤ 3*μ*N₁^2 then
    (𝐞 ((1 : ℝ)/8-2*μ*r^3) : ℂ)/(Real.sqrt (6*μ*r) : ℂ) else 0

private theorem exists_bourgain_cubic_stationary_mode :
    ∃ C ≥ (1 : ℝ), ∀ μ N N₁ : ℝ, 0 < μ → 1 ≤ N → N ≤ N₁ → N₁ ≤ 2*N →
      μ*N^2 ≤ 1 → ∀ β : ℝ, β ≠ 0 →
        ‖bourgainCubicFourierMode (fun x => (bourgainCubicSharpCutoff N N₁ x : ℂ)) μ β-
          bourgainCubicStationaryTerm μ N N₁ β‖ ≤
            C*(1/(1+|β|)+1/|β|+bourgainCubicEndpointBudget μ N β N+
              bourgainCubicEndpointBudget μ N β N₁) := by
  obtain ⟨C,hC,hfinite⟩ := exists_bourgain_cubic_finite_stationary
  refine ⟨C+130,by linarith,?_⟩
  intro μ N N₁ hμ hN hNN hN₁ hμN β hβ
  have hN0 : 0 < N := by linarith
  have hcut := bourgain_cubic_cutoff_difference (y := β) hμ hN hNN hN₁ hμN
  have hfin := hfinite μ hμ β hβ N N₁ hN0 hNN
  change ‖(∫ x in N..N₁, (𝐞 (μ*x^3-β*x) : ℂ))-
    bourgainCubicStationaryTerm μ N N₁ β‖ ≤
    C*(1/|β|+bourgainCubicEndpointBudget μ N β N+
      bourgainCubicEndpointBudget μ N β N₁) at hfin
  have hEa : 0 ≤ bourgainCubicEndpointBudget μ N β N := by
    unfold bourgainCubicEndpointBudget
    split_ifs <;> positivity
  have hEb : 0 ≤ bourgainCubicEndpointBudget μ N β N₁ := by
    unfold bourgainCubicEndpointBudget
    split_ifs <;> positivity
  have he :
      bourgainCubicFourierMode (fun x => (bourgainCubicSharpCutoff N N₁ x : ℂ)) μ β-
        bourgainCubicStationaryTerm μ N N₁ β =
      (bourgainCubicFourierMode (fun x => (bourgainCubicSharpCutoff N N₁ x : ℂ)) μ β-
        (∫ x in N..N₁, (𝐞 (μ*x^3-β*x) : ℂ)))+
      ((∫ x in N..N₁, (𝐞 (μ*x^3-β*x) : ℂ))-bourgainCubicStationaryTerm μ N N₁ β) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  apply (add_le_add hcut hfin).trans
  calc
    _ ≤ (C+130)*(1/(1+|β|))+
        (C+130)*(1/|β|+bourgainCubicEndpointBudget μ N β N+
          bourgainCubicEndpointBudget μ N β N₁) := by
      apply add_le_add
      · rw [div_eq_mul_inv,one_div]
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      · exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring



private theorem bourgainCubicSharpCutoff_integer (A B n : ℤ) :
    bourgainCubicSharpCutoff A B n = if n ∈ Finset.Icc A B then 1 else 0 := by
  classical
  by_cases hn : n ∈ Finset.Icc A B
  · rw [ite_eq_left hn]
    have ha : (A : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hb : (n : ℝ) ≤ B := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    exact modelPhaseBufferedCutoff_one (by norm_num) (by linarith) (by linarith)
  · rw [ite_eq_right hn]
    have hn' : n < A ∨ B < n := by simpa only [Finset.mem_Icc,not_and_or,not_le] using hn
    rcases hn' with ha | hb
    · have ha' : (n : ℝ) ≤ (A : ℝ)-1 := by exact_mod_cast (show n ≤ A-1 by omega)
      exact modelPhaseBufferedCutoff_zero_left (by norm_num) (by linarith)
    · have hb' : (B : ℝ)+1 ≤ (n : ℝ) := by exact_mod_cast (show B+1 ≤ n by omega)
      exact modelPhaseBufferedCutoff_zero_right (by norm_num) (by linarith)

set_option maxHeartbeats 400000 in
private theorem bourgain_cubic_truncation_log {q N : ℝ} {H : ℕ}
    (hN : 1 ≤ N) (hqN : q ≤ N) (hH : (H : ℝ) = 64*q*N) :
    1 ≤ 2*Real.log (2*N) ∧ 1+Real.log (2*(H : ℝ)+1) ≤ 258*Real.log (2*N) := by
  have hN0 : 0 < N := by linarith
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hN
  have hl2 : (1 : ℝ)/2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlog : Real.log (2*N) = Real.log 2+Real.log N :=
    Real.log_mul (by norm_num) hN0.ne'
  have hupper : 2*(H : ℝ)+1 ≤ 129*N^2 := by
    rw [hH]
    have h := mul_le_mul_of_nonneg_right hqN hN0.le
    nlinarith
  have hl129 : Real.log 129 ≤ 128 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 129)
    norm_num at h
    exact h
  have hlogH : Real.log (2*(H : ℝ)+1) ≤ 128+2*Real.log N := by
    apply (Real.log_le_log (by positivity) hupper).trans
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ hN0.ne'),Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  rw [hlog]
  constructor <;> linarith


set_option maxHeartbeats 400000 in
private theorem bourgain_cubic_modulated_mode (χ : ℝ → ℂ) (μ θ y : ℝ) :
    bourgainCubicFourierMode (fun x => χ x*(𝐞 (θ*x) : ℂ)) μ y =
      bourgainCubicFourierMode χ μ (y-θ) := by
  unfold bourgainCubicFourierMode
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    dsimp only
    rw [mul_assoc,← Circle.coe_mul,← AddChar.map_add_eq_mul]
    rw [show θ*x+(μ*x^3-y*x) = μ*x^3-(y-θ)*x by ring])

private theorem bourgain_cubic_shifted_weighted_poisson {χ : ℝ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hs : HasCompactSupport χ)
    (μ θ : ℝ) (q : ℕ) [NeZero q] (a b : ℤ) :
    Summable (fun h : ℤ =>
      ‖bourgainQuadraticGauss q a (b+h)*
        bourgainCubicFourierMode χ μ ((h : ℝ)/(q : ℝ)-θ)‖) ∧
    (∑' n : ℤ, χ n*(𝐞 (μ*(n : ℝ)^3+θ*n+
        ((a : ℝ)*(n : ℝ)^2+(b : ℝ)*(n : ℝ))/(q : ℝ)) : ℂ)) =
      (q : ℂ)⁻¹ * ∑' h : ℤ,
        bourgainQuadraticGauss q a (b+h)*
          bourgainCubicFourierMode χ μ ((h : ℝ)/(q : ℝ)-θ) := by
  have hc : ContDiff ℝ ∞ (fun x : ℝ => χ x*(𝐞 (θ*x) : ℂ)) := by
    simp only [Real.fourierChar_apply]
    have hp : ContDiff ℝ ∞ (fun x : ℝ => 2*Real.pi*(θ*x)) := by fun_prop
    exact hχ.mul (((Complex.ofRealCLM.contDiff.comp hp).mul contDiff_const).cexp)
  obtain ⟨habs,he⟩ := bourgain_cubic_rational_weighted_poisson hc hs.mul_right μ q a b
  simp only [bourgain_cubic_modulated_mode] at habs he
  refine ⟨habs,?_⟩
  rw [← he]
  apply tsum_congr
  intro n
  rw [mul_assoc,← Circle.coe_mul,← AddChar.map_add_eq_mul]
  rw [show θ*(n : ℝ)+(μ*(n : ℝ)^3+
      ((a : ℝ)*(n : ℝ)^2+(b : ℝ)*(n : ℝ))/(q : ℝ)) =
    μ*(n : ℝ)^3+θ*n+((a : ℝ)*(n : ℝ)^2+(b : ℝ)*(n : ℝ))/(q : ℝ) by ring]

private theorem bourgain_cubic_endpoint_le_cap (μ N β X : ℝ) :
    bourgainCubicEndpointBudget μ N β X ≤ 1/Real.sqrt (μ*N) := by
  unfold bourgainCubicEndpointBudget
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

private theorem bourgain_cubic_cutoff_low_mode {μ N N₁ β : ℝ}
    (hμ : 0 < μ) (hN : 1 ≤ N) (hNN : N ≤ N₁) (hβ : β ≤ μ*N^2/16) :
    ‖bourgainCubicFourierMode (fun x => (bourgainCubicSharpCutoff N N₁ x : ℂ)) μ β‖ ≤
      32/(μ*N^2) := by
  let χ := bourgainCubicSharpCutoff N N₁
  have hN0 : 0 < N := by linarith
  have hab : N/4 ≤ N₁+1 := by linarith
  have hwhole :
      bourgainCubicFourierMode (fun x => (χ x : ℂ)) μ β =
        ∫ x in (N/4)..(N₁+1), (χ x : ℂ)*(𝐞 (μ*x^3-β*x) : ℂ) := by
    unfold bourgainCubicFourierMode
    symm
    apply intervalIntegral.integral_eq_integral_of_support_subset
    intro x hx
    have hxs : x ∈ tsupport χ := by
      apply subset_tsupport χ
      intro hz
      exact hx (by simp only [hz,Complex.ofReal_zero,zero_mul])
    have hb := bourgainCubicSharpCutoff_tsupport N N₁ hxs
    constructor <;> linarith [hb.1,hb.2]
  rw [hwhole]
  have h := bourgain_cubic_weighted_gap (β := β)
    (intervalC1Bound_modelPhaseBufferedCutoff (l := N-1) (r := N₁+1)
      (by norm_num : (0 : ℝ) < 1/2) hab) hab (by positivity) hμ
    (by positivity : 0 < μ*N^2/8) (Or.inr (by nlinarith))
  apply h.trans
  have he : 2*2/(μ*N^2/8*Real.pi) = 32/(μ*N^2*Real.pi) := by ring
  rw [he]
  apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 32)
    (by positivity : 0 < μ*N^2)
  nlinarith [mul_nonneg (show 0 ≤ μ*N^2 by positivity)
    (show 0 ≤ Real.pi-1 by linarith [Real.pi_gt_three])]

private theorem exists_bourgain_cubic_uniform_mode_error :
    ∃ C ≥ (1 : ℝ), ∀ μ N N₁ : ℝ, 0 < μ → 1 ≤ N → N ≤ N₁ → N₁ ≤ 2*N →
      μ*N^2 ≤ 1 → ∀ β : ℝ,
        ‖bourgainCubicFourierMode (fun x => (bourgainCubicSharpCutoff N N₁ x : ℂ)) μ β-
          bourgainCubicStationaryTerm μ N N₁ β‖ ≤
            C*(1/(μ*N^2)+1/Real.sqrt (μ*N)) := by
  obtain ⟨C,hC,hm⟩ := exists_bourgain_cubic_stationary_mode
  refine ⟨32+17*C,by linarith,?_⟩
  intro μ N N₁ hμ hN hNN hN₁ hμN β
  have hN0 : 0 < N := by linarith
  have hA : 0 < μ*N^2 := by positivity
  have hcap : 0 ≤ 1/Real.sqrt (μ*N) := by positivity
  by_cases hβ : β ≤ μ*N^2/16
  · have hmain : bourgainCubicStationaryTerm μ N N₁ β = 0 := by
      unfold bourgainCubicStationaryTerm
      rw [ite_eq_right (by intro h; nlinarith [h.1])]
    rw [hmain,sub_zero]
    apply (bourgain_cubic_cutoff_low_mode hμ hN hNN hβ).trans
    have hp : 0 ≤ 17*C*(1/(μ*N^2)+1/Real.sqrt (μ*N)) := by positivity
    simp only [div_eq_mul_inv,one_mul] at hp hcap ⊢
    nlinarith
  · have hβ0 : 0 < β := by nlinarith
    have h := hm μ N N₁ hμ hN hNN hN₁ hμN β hβ0.ne'
    have ha : 1/(1+|β|) ≤ 1/(μ*N^2) :=
      div_le_div_of_nonneg_left (by norm_num) hA (by linarith [abs_nonneg β])
    have hb : 1/|β| ≤ 16/(μ*N^2) := by
      rw [abs_of_pos hβ0]
      apply (div_le_div_iff₀ hβ0 hA).mpr
      linarith
    have he := add_le_add (add_le_add (add_le_add ha hb)
      (bourgain_cubic_endpoint_le_cap μ N β N))
      (bourgain_cubic_endpoint_le_cap μ N β N₁)
    apply h.trans ((mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ C)).trans ?_)
    have hp : 0 ≤ C*(1/Real.sqrt (μ*N)) := mul_nonneg (by linarith) hcap
    have hp' : 0 ≤ 1/(μ*N^2) := by positivity
    simp only [div_eq_mul_inv,one_mul] at hp hp' hcap ⊢
    nlinarith

private theorem bourgain_cubic_shifted_endpoint_sum {μ N q X θ : ℝ} {H : ℕ}
    (hμ : 0 < μ) (hN : 1 ≤ N) (hq : 1 ≤ q)
    (hX : N ≤ X) (hX2 : X ≤ 2*N) (hμN : μ*N^2 ≤ 1)
    (hθ : |q*θ| ≤ 1/2) (hH : 13*q ≤ H) :
    (∑ h ∈ (Finset.Icc (-(H : ℤ)) (H : ℤ)).erase 0,
      bourgainCubicEndpointBudget μ N ((h : ℝ)/q-θ) X) ≤
        3/Real.sqrt (μ*N)+2*q*(3+2*Real.log (2*(H : ℝ)+1)) := by
  classical
  let S := (Finset.Icc (-(H : ℤ)) (H : ℤ)).erase 0
  let W := S.image (fun h : ℤ => (h : ℝ))
  let w := q*(3*μ*X^2+θ)
  let g : ℝ → ℝ := fun t => bourgainCubicEndpointBudget μ N (t/q-θ) X
  have hq0 : 0 < q := by linarith
  have hN0 : 0 < N := by linarith
  have hw : |w| ≤ H := by
    have hX0 : 0 ≤ X := by linarith
    have hs := mul_self_le_mul_self hX0 hX2
    have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 3*μ*q by positivity)
    have hμq := mul_le_mul_of_nonneg_left hμN hq0.le
    have ht := abs_le.mp hθ
    dsimp only [w]
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg X,mul_nonneg hμ.le (sq_nonneg X)]
  have hRange : ∀ t ∈ W, |t-w| ≤ (2*H : ℕ) := by
    intro t ht
    obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp ht
    have hi := Finset.mem_Icc.mp (Finset.mem_of_mem_erase hh)
    have hl : -(H : ℝ) ≤ (h : ℝ) := by exact_mod_cast hi.1
    have hr : (h : ℝ) ≤ (H : ℝ) := by exact_mod_cast hi.2
    have hh := abs_le.mp hw
    rw [abs_le]
    push_cast
    constructor <;> linarith
  have hcap : ∀ t ∈ W, g t ≤ 1/Real.sqrt (μ*N) := by
    intro t _
    exact bourgain_cubic_endpoint_le_cap μ N (t/q-θ) X
  have hrec : ∀ t ∈ W, t ≠ w → g t ≤ q/|t-w| := by
    intro t _ hne
    have he : 3*μ*X^2-(t/q-θ) = (w-t)/q := by
      dsimp only [w]
      field_simp
      ring
    have hz : 3*μ*X^2 ≠ t/q-θ := by
      intro h
      have hh : w-t = 0 := (div_eq_zero_iff).mp
        (by rw [← he,h,sub_self]) |>.resolve_right hq0.ne'
      exact hne (sub_eq_zero.mp hh).symm
    change bourgainCubicEndpointBudget μ N (t/q-θ) X ≤ _
    rw [bourgainCubicEndpointBudget,ite_eq_right hz]
    apply (min_le_right _ _).trans_eq
    rw [he,abs_div,abs_of_pos hq0,abs_sub_comm w t]
    field_simp
  have hb := bourgain_capped_reciprocal_sum W w (2*H) g
    (bourgain_integer_image_separated S) hRange (by positivity) hq0.le hcap hrec
  dsimp only [W] at hb
  rw [Finset.sum_image (fun _ _ _ _ h => Int.cast_injective h)] at hb
  convert hb using 1
  push_cast
  ring

private theorem bourgain_shifted_nonzero_frequency {q θ : ℝ} {h : ℤ}
    (hq : 0 < q) (hθ : |q*θ| ≤ 1/2) (hh : h ≠ 0) :
    0 < |(h : ℝ)/q-θ| ∧
      1/|(h : ℝ)/q-θ| ≤ 2*q*(1/|(h : ℝ)|) := by
  have hi := bourgain_integer_abs_ge_one hh
  have ht : |(h : ℝ)| ≤ |(h : ℝ)-q*θ|+|q*θ| := by
    simpa only [sub_add_cancel] using abs_add_le ((h : ℝ)-q*θ) (q*θ)
  have hgap : |(h : ℝ)|/2 ≤ |(h : ℝ)-q*θ| := by linarith
  have he : (h : ℝ)/q-θ = ((h : ℝ)-q*θ)/q := by field_simp
  rw [he,abs_div,abs_of_pos hq]
  have hg : 0 < |(h : ℝ)-q*θ| := by linarith
  refine ⟨div_pos hg hq,?_⟩
  rw [one_div_div]
  have hr : 2*q*(1/|(h : ℝ)|) = 2*q/|(h : ℝ)| := by ring
  rw [hr]
  apply (div_le_div_iff₀ hg (by linarith : 0 < |(h : ℝ)|)).mpr
  nlinarith


private theorem exists_bourgain_cubic_shifted_gauss_far_tail :
    ∃ C ≥ (1 : ℝ), ∀ μ N N₁ : ℝ, 0 < μ → 1 ≤ N → N ≤ N₁ → N₁ ≤ 2*N →
      μ*N^2 ≤ 1 → ∀ q : ℕ, 0 < q → ∀ a b : ℤ, IsCoprime a (q : ℤ) →
      ∀ θ : ℝ, |(q : ℝ)*θ| ≤ 1/2 → ∀ R : ℕ, 0 < R →
        ‖(q : ℂ)⁻¹*∑' h : ℤ, if R < h.natAbs then
          bourgainQuadraticGauss q a (b+h)*
            bourgainCubicFourierMode (fun x => (bourgainCubicSharpCutoff N N₁ x : ℂ))
              μ ((h : ℝ)/(q : ℝ)-θ) else 0‖ ≤
          C*N*(q : ℝ)*Real.sqrt q/(R : ℝ) := by
  obtain ⟨C,hC,hdecay⟩ := exists_bourgain_cubic_cutoff_fourier_decay
  refine ⟨16*C,by linarith,?_⟩
  intro μ N N₁ hμ hN hNN hN₁ hμN q hq a b ha θ hθ R hR
  let : NeZero q := ⟨hq.ne'⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hN0 : 0 < N := by linarith
  have hC0 : 0 ≤ C := by linarith
  let χ := bourgainCubicSharpCutoff N N₁
  let f : ℤ → ℂ := fun h => bourgainQuadraticGauss q a (b+h)*
    bourgainCubicFourierMode (fun x => (χ x : ℂ)) μ ((h : ℝ)/(q : ℝ)-θ)
  have hχ : ContDiff ℝ ∞ (fun x => (χ x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (modelPhaseBufferedCutoff_contDiff _ _ _)
  have hs : HasCompactSupport (fun x => (χ x : ℂ)) :=
    (modelPhaseBufferedCutoff_hasCompactSupport
      (l := N-1) (r := N₁+1) (by norm_num : (0 : ℝ) < 1/2)).comp_left
        (g := fun x : ℝ => (x : ℂ)) rfl
  have hsum : Summable (fun h => ‖f h‖) :=
    (bourgain_cubic_shifted_weighted_poisson hχ hs μ θ q a b).1
  have hmode (h : ℤ) (hh : h ≠ 0) :
      ‖bourgainCubicFourierMode (fun x => (χ x : ℂ)) μ ((h : ℝ)/(q : ℝ)-θ)‖ ≤
        4*C*N*(q : ℝ)^2/(h : ℝ)^2 := by
    have hh0 : (h : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hh
    let β := (h : ℝ)/(q : ℝ)-θ
    have hd := hdecay μ N N₁ hμ hN hNN hN₁ hμN β
    have hi := bourgain_integer_abs_ge_one hh
    have he : (h : ℝ) = (q : ℝ)*β+(q : ℝ)*θ := by dsimp only [β]; field_simp; ring
    have ht : |(h : ℝ)| ≤ (q : ℝ)*|β|+|(q : ℝ)*θ| := by
      calc
        _ = |(q : ℝ)*β+(q : ℝ)*θ| := congrArg abs he
        _ ≤ |(q : ℝ)*β|+|(q : ℝ)*θ| := abs_add_le _ _
        _ = _ := by rw [abs_mul,abs_of_pos hq0]
    have hg : |(h : ℝ)| ≤ 2*(q : ℝ)*|β| := by linarith
    have hs : (h : ℝ)^2 ≤ 4*(q : ℝ)^2*(1+|β|)^2 := by
      have hp := pow_le_pow_left₀ (abs_nonneg (h : ℝ)) hg 2
      have ht := sq_nonneg (q : ℝ)
      have hb := abs_nonneg β
      nlinarith [sq_abs (h : ℝ),mul_nonneg ht hb]
    have hb := mul_le_mul_of_nonneg_right hs
      (norm_nonneg (bourgainCubicFourierMode (fun x => (χ x : ℂ)) μ β))
    have hm := mul_le_mul_of_nonneg_left hd
      (show 0 ≤ 4*(q : ℝ)^2 by positivity)
    apply (le_div_iff₀ (sq_pos_of_ne_zero hh0)).mpr
    change ‖bourgainCubicFourierMode (fun x => (χ x : ℂ)) μ β‖*(h : ℝ)^2 ≤ _
    nlinarith only [hb,hm]
  let K : ℝ := Real.sqrt (2*(q : ℝ))*(4*C)*N*(q : ℝ)^2
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hb (h : ℤ) (hh : h ≠ 0) : ‖f h‖ ≤ K/(h : ℝ)^2 := by
    dsimp only [f]
    rw [norm_mul]
    exact (mul_le_mul (bourgainQuadraticGauss_norm_le q a (b+h) ha) (hmode h hh)
      (norm_nonneg _) (Real.sqrt_nonneg _)).trans_eq (by dsimp only [K]; ring)
  have ht := norm_integer_far_tail_le_of_inverse_square hK hsum hb hR
  have hroot : Real.sqrt (2*(q : ℝ)) ≤ 2*Real.sqrt (q : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    norm_num [Real.sqrt_le_iff]
  simp only [norm_mul,norm_inv,Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr hq0.le)).trans
  dsimp only [K]
  have he : (q : ℝ)⁻¹*(2*(Real.sqrt (2*(q : ℝ))*(4*C)*N*(q : ℝ)^2)/(R : ℝ)) =
      (8*C*N*(q : ℝ)/(R : ℝ))*Real.sqrt (2*(q : ℝ)) := by field_simp; norm_num
  rw [he]
  exact (mul_le_mul_of_nonneg_left hroot (by positivity)).trans_eq (by ring)
set_option maxHeartbeats 400000 in
private theorem bourgain_cubic_shifted_exact_cutoff_poisson (A B : ℤ) (μ θ : ℝ)
    (q : ℕ) [NeZero q] (a b : ℤ) :
    Summable (fun h : ℤ => ‖bourgainQuadraticGauss q a (b+h)*
      bourgainCubicFourierMode (fun x => (bourgainCubicSharpCutoff A B x : ℂ))
        μ ((h : ℝ)/(q : ℝ)-θ)‖) ∧
    (∑ n ∈ Finset.Icc A B, (𝐞 (μ*(n : ℝ)^3+θ*n+
      ((a : ℝ)*(n : ℝ)^2+(b : ℝ)*(n : ℝ))/(q : ℝ)) : ℂ)) =
      (q : ℂ)⁻¹*∑' h : ℤ, bourgainQuadraticGauss q a (b+h)*
        bourgainCubicFourierMode (fun x => (bourgainCubicSharpCutoff A B x : ℂ))
          μ ((h : ℝ)/(q : ℝ)-θ) := by
  classical
  have hχ : ContDiff ℝ ∞ (fun x => (bourgainCubicSharpCutoff A B x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (modelPhaseBufferedCutoff_contDiff _ _ _)
  have hs : HasCompactSupport (fun x => (bourgainCubicSharpCutoff A B x : ℂ)) :=
    (modelPhaseBufferedCutoff_hasCompactSupport
      (l := (A : ℝ)-1) (r := (B : ℝ)+1) (by norm_num : (0 : ℝ) < 1/2)).comp_left
        (g := fun x : ℝ => (x : ℂ)) rfl
  obtain ⟨habs,hp⟩ := bourgain_cubic_shifted_weighted_poisson hχ hs μ θ q a b
  refine ⟨habs,?_⟩
  rw [← hp,tsum_eq_sum (s := Finset.Icc A B) (fun n hn => by
    simp only [bourgainCubicSharpCutoff_integer A B n,ite_eq_right hn,Complex.ofReal_zero,zero_mul])]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [bourgainCubicSharpCutoff_integer A B n,ite_eq_left hn,Complex.ofReal_one,one_mul]

set_option maxHeartbeats 400000 in
private theorem exists_bourgain_cubic_shifted_central_error :
    ∃ C ≥ (1 : ℝ), ∀ μ N N₁ : ℝ, 0 < μ → 1 ≤ N → N ≤ N₁ → N₁ ≤ 2*N →
      μ*N^2 ≤ 1 → ∀ q : ℕ, 0 < q → ∀ a b : ℤ, IsCoprime a (q : ℤ) →
      ∀ θ : ℝ, |(q : ℝ)*θ| ≤ 1/2 → ∀ H : ℕ, 13*(q : ℝ) ≤ H →
        ‖(q : ℂ)⁻¹*∑ h ∈ (Finset.Icc (-(H : ℤ)) (H : ℤ)).erase 0,
          bourgainQuadraticGauss q a (b+h)*
            (bourgainCubicFourierMode (fun x => (bourgainCubicSharpCutoff N N₁ x : ℂ))
              μ ((h : ℝ)/(q : ℝ)-θ)-
                bourgainCubicStationaryTerm μ N N₁ ((h : ℝ)/(q : ℝ)-θ))‖ ≤
          C*(1/(Real.sqrt (μ*N)*Real.sqrt q)+
            Real.sqrt q*(1+Real.log (2*(H : ℝ)+1))) := by
  obtain ⟨C,hC,hmode⟩ := exists_bourgain_cubic_stationary_mode
  refine ⟨72*C,by linarith,?_⟩
  intro μ N N₁ hμ hN hNN hN₁ hμN q hq a b ha θ hθ H hH
  let : NeZero q := ⟨hq.ne'⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hN0 : 0 < N := by linarith
  have hC0 : 0 ≤ C := by linarith
  let S := (Finset.Icc (-(H : ℤ)) (H : ℤ)).erase 0
  let β := fun h : ℤ => (h : ℝ)/(q : ℝ)-θ
  let err : ℤ → ℂ := fun h =>
    bourgainCubicFourierMode (fun x => (bourgainCubicSharpCutoff N N₁ x : ℂ)) μ (β h)-
      bourgainCubicStationaryTerm μ N N₁ (β h)
  let L := Real.log (2*(H : ℝ)+1)
  let A := 1/Real.sqrt (μ*N)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hL : 0 ≤ L := Real.log_nonneg (by have hn : (0 : ℝ) ≤ H := Nat.cast_nonneg H; linarith)
  have hlog : Real.log ((H : ℝ)+1) ≤ L :=
    Real.log_le_log (by positivity) (by have hn := Nat.cast_nonneg (α := ℝ) H; linarith)
  have hβ (h : ℤ) (hh : h ∈ S) :
      0 < |β h| ∧ 1/|β h| ≤ 2*(q : ℝ)*(1/|(h : ℝ)|) :=
    bourgain_shifted_nonzero_frequency hq0 hθ (Finset.mem_erase.mp hh).1
  have hrecip : (∑ h ∈ S, 1/|β h|) ≤ 4*(q : ℝ)*(3+2*L) := by
    calc
      _ ≤ ∑ h ∈ S, 2*(q : ℝ)*(1/|(h : ℝ)|) :=
        Finset.sum_le_sum (fun h hh => (hβ h hh).2)
      _ = 2*(q : ℝ)*∑ h ∈ S, 1/|(h : ℝ)| := (Finset.mul_sum _ _ _).symm
      _ ≤ 2*(q : ℝ)*(2*(3+2*Real.log ((H : ℝ)+1))) :=
        mul_le_mul_of_nonneg_left (bourgain_integer_reciprocal_sum H) (by positivity)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hlog hq0.le
        nlinarith
  have hscaled : (∑ h ∈ S, 1/(1+|β h|)) ≤ 4*(q : ℝ)*(3+2*L) := by
    apply (Finset.sum_le_sum (fun h hh =>
      div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (hβ h hh).1
        (by linarith : |β h| ≤ 1+|β h|))).trans hrecip
  have hEa := bourgain_cubic_shifted_endpoint_sum hμ hN hq1 (le_refl N)
    (show N ≤ 2*N by linarith) hμN hθ hH
  have hEb := bourgain_cubic_shifted_endpoint_sum hμ hN hq1 hNN hN₁ hμN hθ hH
  have hsum : (∑ h ∈ S, ‖err h‖) ≤ 36*C*(A+(q : ℝ)*(1+L)) := by
    calc
      _ ≤ ∑ h ∈ S, C*(1/(1+|β h|)+1/|β h|+
          bourgainCubicEndpointBudget μ N (β h) N+
          bourgainCubicEndpointBudget μ N (β h) N₁) := by
        apply Finset.sum_le_sum
        intro h hh
        exact hmode μ N N₁ hμ hN hNN hN₁ hμN (β h)
          (abs_pos.mp (hβ h hh).1)
      _ = C*((∑ h ∈ S, 1/(1+|β h|))+(∑ h ∈ S, 1/|β h|)+
          (∑ h ∈ S, bourgainCubicEndpointBudget μ N (β h) N)+
          (∑ h ∈ S, bourgainCubicEndpointBudget μ N (β h) N₁)) := by
        rw [← Finset.mul_sum]
        simp only [Finset.sum_add_distrib]
      _ ≤ C*(6*A+36*(q : ℝ)+24*(q : ℝ)*L) := by
        apply mul_le_mul_of_nonneg_left _ hC0
        change (∑ h ∈ S, bourgainCubicEndpointBudget μ N (β h) N) ≤
          3/Real.sqrt (μ*N)+2*(q : ℝ)*(3+2*L) at hEa
        change (∑ h ∈ S, bourgainCubicEndpointBudget μ N (β h) N₁) ≤
          3/Real.sqrt (μ*N)+2*(q : ℝ)*(3+2*L) at hEb
        have he : 3/Real.sqrt (μ*N) = 3*A := by dsimp only [A]; ring
        rw [he] at hEa hEb
        linarith
      _ ≤ _ := by
        nlinarith [mul_nonneg hC0 hA,
          mul_nonneg hC0 (mul_nonneg hq0.le hL)]
  have hGS : ‖∑ h ∈ S, bourgainQuadraticGauss q a (b+h)*err h‖ ≤
      Real.sqrt (2*(q : ℝ))*(∑ h ∈ S, ‖err h‖) := by
    apply (norm_sum_le _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (bourgainQuadraticGauss_norm_le q a (b+h) ha)
      (norm_nonneg _)
  have hroot : Real.sqrt (2*(q : ℝ)) ≤ 2*Real.sqrt (q : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    norm_num [Real.sqrt_le_iff]
  change ‖(q : ℂ)⁻¹*∑ h ∈ S, bourgainQuadraticGauss q a (b+h)*err h‖ ≤ _
  simp only [norm_mul,norm_inv,Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left hGS (inv_nonneg.mpr hq0.le)).trans
  apply (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)) (inv_nonneg.mpr hq0.le)).trans
  apply (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hroot (by positivity))
    (inv_nonneg.mpr hq0.le)).trans_eq
  have hsq : (Real.sqrt (q : ℝ))^2 = (q : ℝ) := Real.sq_sqrt hq0.le
  have hr : Real.sqrt (q : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hq0).ne'
  have hm : Real.sqrt (μ*N) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hcancel : (q : ℝ)⁻¹*Real.sqrt (q : ℝ) = (Real.sqrt (q : ℝ))⁻¹ := by
    field_simp
    nlinarith [hsq]
  change (q : ℝ)⁻¹*(2*Real.sqrt (q : ℝ)*(36*C*(A+(q : ℝ)*(1+L)))) =
    72*C*(1/(Real.sqrt (μ*N)*Real.sqrt (q : ℝ))+Real.sqrt (q : ℝ)*(1+L))
  calc
    _ = 72*C*((q : ℝ)⁻¹*Real.sqrt (q : ℝ))*(A+(q : ℝ)*(1+L)) := by ring
    _ = 72*C*(Real.sqrt (q : ℝ))⁻¹*(A+(q : ℝ)*(1+L)) := by rw [hcancel]
    _ = _ := by
      dsimp only [A]
      field_simp
      linear_combination -(Real.sqrt (μ*N)*(1+L))*hsq

private theorem bourgain_cubic_shifted_stationary_window {μ N N₁ θ : ℝ}
    (hμ : 0 < μ) (hN : 1 ≤ N) (hNN : N ≤ N₁) (hN₁ : N₁ ≤ 2*N)
    (hμN : μ*N^2 ≤ 1) (q : ℕ) [NeZero q] (a b : ℤ)
    (hθ : |(q : ℝ)*θ| ≤ 1/2) {H : ℕ} (hH : 13*(q : ℝ) ≤ H) :
    (∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
      bourgainQuadraticGauss q a (b+h)*
        bourgainCubicStationaryTerm μ N N₁ ((h : ℝ)/(q : ℝ)-θ)) =
    ∑ h ∈ Finset.Icc ⌈(q : ℝ)*(3*μ*N^2+θ)⌉ ⌊(q : ℝ)*(3*μ*N₁^2+θ)⌋,
      let r := Real.sqrt (((h : ℝ)/(q : ℝ)-θ)/(3*μ))
      bourgainQuadraticGauss q a (b+h)*
        ((𝐞 ((1 : ℝ)/8-2*μ*r^3) : ℂ)/(Real.sqrt (6*μ*r) : ℂ)) := by
  classical
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q))
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have hN0 : 0 < N := by linarith
  have hN₁0 : 0 ≤ N₁ := by linarith
  have hθ' := abs_le.mp hθ
  let S := Finset.Icc ⌈(q : ℝ)*(3*μ*N^2+θ)⌉ ⌊(q : ℝ)*(3*μ*N₁^2+θ)⌋
  let T := Finset.Icc (-(H : ℤ)) (H : ℤ)
  have hwindow (h : ℤ) :
      h ∈ S ↔ (3*μ*N^2 ≤ (h : ℝ)/(q : ℝ)-θ ∧
        (h : ℝ)/(q : ℝ)-θ ≤ 3*μ*N₁^2) := by
    simp only [S,Finset.mem_Icc,Int.ceil_le,Int.le_floor,
      le_sub_iff_add_le,sub_le_iff_le_add,le_div_iff₀ hq0,div_le_iff₀ hq0,mul_comm]
  have hupper : (q : ℝ)*(3*μ*N₁^2+θ) ≤ 13*(q : ℝ) := by
    have hs := mul_self_le_mul_self hN₁0 hN₁
    have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 3*μ*(q : ℝ) by positivity)
    have hμq := mul_le_mul_of_nonneg_left hμN hq0.le
    nlinarith [hθ'.2]
  have hsub : S ⊆ T := by
    intro h hh
    have hb : (q : ℝ)*(3*μ*N^2+θ) ≤ (h : ℝ) ∧
        (h : ℝ) ≤ (q : ℝ)*(3*μ*N₁^2+θ) := by
      simpa only [S,Finset.mem_Icc,Int.ceil_le,Int.le_floor] using hh
    have hl : -(H : ℝ) ≤ (h : ℝ) := by
      have hp : 0 ≤ 3*μ*(q : ℝ)*N^2 := by positivity
      nlinarith [hb.1,hθ'.1]
    have hr : (h : ℝ) ≤ H := hb.2.trans (hupper.trans hH)
    apply Finset.mem_Icc.mpr
    constructor
    · exact_mod_cast hl
    · exact_mod_cast hr
  calc
    _ = ∑ h ∈ S, bourgainQuadraticGauss q a (b+h)*
        bourgainCubicStationaryTerm μ N N₁ ((h : ℝ)/(q : ℝ)-θ) := by
      symm
      apply Finset.sum_subset hsub
      intro h _ hn
      simp only [bourgainCubicStationaryTerm,ite_eq_right (fun hd => hn ((hwindow h).mpr hd)),mul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h hh
      simp only [bourgainCubicStationaryTerm,ite_eq_left ((hwindow h).mp hh)]

private theorem exists_bourgain_cubic_shifted_zero_error :
    ∃ C ≥ (1 : ℝ), ∀ μ N N₁ : ℝ, 0 < μ → 1 ≤ N → N ≤ N₁ → N₁ ≤ 2*N →
      μ*N^2 ≤ 1 → ∀ q : ℕ, 0 < q → ∀ a b : ℤ, IsCoprime a (q : ℤ) →
      ∀ θ : ℝ,
        ‖(q : ℂ)⁻¹*(bourgainQuadraticGauss q a b*
          (bourgainCubicFourierMode (fun x => (bourgainCubicSharpCutoff N N₁ x : ℂ))
            μ (-θ)-bourgainCubicStationaryTerm μ N N₁ (-θ)))‖ ≤
          C*(1/(μ*N^2)+1/(Real.sqrt (μ*N)*Real.sqrt q)) := by
  obtain ⟨C,hC,hm⟩ := exists_bourgain_cubic_uniform_mode_error
  refine ⟨2*C,by linarith,?_⟩
  intro μ N N₁ hμ hN hNN hN₁ hμN q hq a b ha θ
  let : NeZero q := ⟨hq.ne'⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hN0 : 0 < N := by linarith
  have hC0 : 0 ≤ C := by linarith
  have h := hm μ N N₁ hμ hN hNN hN₁ hμN (-θ)
  have hg := bourgainQuadraticGauss_norm_le q a b ha
  have hr : 1 ≤ Real.sqrt (q : ℝ) := by
    nlinarith [Real.sq_sqrt hq0.le,Real.sqrt_nonneg (q : ℝ)]
  have hroot : Real.sqrt (2*(q : ℝ)) ≤ 2*Real.sqrt (q : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    norm_num [Real.sqrt_le_iff]
  simp only [norm_mul,norm_inv,Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left (mul_le_mul hg h (norm_nonneg _)
    (Real.sqrt_nonneg _)) (inv_nonneg.mpr hq0.le)).trans
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hroot (by positivity))
    (inv_nonneg.mpr hq0.le)).trans
  have hsr : Real.sqrt (q : ℝ) ≠ 0 := by linarith
  have he : (q : ℝ)⁻¹*(2*Real.sqrt (q : ℝ)*
      (C*(1/(μ*N^2)+1/Real.sqrt (μ*N)))) =
        2*C*((1/(μ*N^2))/Real.sqrt (q : ℝ)+
          1/(Real.sqrt (μ*N)*Real.sqrt (q : ℝ))) := by
    have hcancel : (q : ℝ)⁻¹*Real.sqrt (q : ℝ) = (Real.sqrt (q : ℝ))⁻¹ := by
      field_simp
      nlinarith [Real.sq_sqrt hq0.le]
    calc
      _ = 2*C*((q : ℝ)⁻¹*Real.sqrt (q : ℝ))*
          (1/(μ*N^2)+1/Real.sqrt (μ*N)) := by ring
      _ = _ := by rw [hcancel]; ring
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2*C)
  exact add_le_add (div_le_self (by positivity) hr) le_rfl
set_option maxHeartbeats 400000 in

                                                                     
                                                                         
                                                                          
theorem exists_bourgain_cubic_shifted_gauss_denominator_error :
    ∃ C ≥ (1 : ℝ), ∀ N N₁ q : ℕ, 1 ≤ N → N ≤ N₁ → N₁ ≤ 2*N →
      0 < q → q ≤ N → ∀ μ : ℝ, 0 < μ → μ*(N : ℝ)^2 ≤ 1 →
      ∀ a b : ℤ, IsCoprime a (q : ℤ) →
      ∀ θ : ℝ, |(q : ℝ)*θ| ≤ 1/2 →
        ‖(∑ n ∈ Finset.Icc (N : ℤ) (N₁ : ℤ),
          (𝐞 (μ*(n : ℝ)^3+θ*n+((a : ℝ)*(n : ℝ)^2+(b : ℝ)*(n : ℝ))/(q : ℝ)) : ℂ))-
          (q : ℂ)⁻¹*∑ h ∈ Finset.Icc ⌈(q : ℝ)*(3*μ*(N : ℝ)^2+θ)⌉ ⌊(q : ℝ)*(3*μ*(N₁ : ℝ)^2+θ)⌋,
            let r := Real.sqrt (((h : ℝ)/(q : ℝ)-θ)/(3*μ))
            bourgainQuadraticGauss q a (b+h)*
              ((𝐞 ((1 : ℝ)/8-2*μ*r^3) : ℂ)/(Real.sqrt (6*μ*r) : ℂ))‖ ≤
          C*(Real.sqrt q*Real.log (2*(N : ℝ))+1/(μ*(N : ℝ)^2)+
            1/(Real.sqrt (μ*(N : ℝ))*Real.sqrt q)) := by
  classical
  obtain ⟨Cc,hCc,hcentral⟩ := exists_bourgain_cubic_shifted_central_error
  obtain ⟨Cf,hCf,hfar⟩ := exists_bourgain_cubic_shifted_gauss_far_tail
  obtain ⟨Cz,hCz,hzero⟩ := exists_bourgain_cubic_shifted_zero_error
  let D := 260*Cc+2*Cf+2*Cz
  have hCc0 : 0 ≤ Cc := by linarith
  have hCf0 : 0 ≤ Cf := by linarith
  have hCz0 : 0 ≤ Cz := by linarith
  refine ⟨D,by dsimp only [D]; linarith,?_⟩
  intro N N₁ q hN hNN hN₁ hq hqN μ hμ hμN a b ha θ hθ
  let : NeZero q := ⟨hq.ne'⟩
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNr0 : (0 : ℝ) < N := by linarith
  have hNNr : (N : ℝ) ≤ N₁ := by exact_mod_cast hNN
  have hN₁r : (N₁ : ℝ) ≤ 2*(N : ℝ) := by exact_mod_cast hN₁
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hqNr : (q : ℝ) ≤ N := by exact_mod_cast hqN
  have hNnat0 : 0 < N := by omega
  let H : ℕ := 64*q*N
  have hH0 : 0 < H := by dsimp only [H]; positivity
  have hHcast : (H : ℝ) = 64*(q : ℝ)*(N : ℝ) := by
    dsimp only [H]
    push_cast
    ring
  have hH : 13*(q : ℝ) ≤ H := by
    rw [hHcast]
    nlinarith [mul_le_mul_of_nonneg_left hNr hqr.le]
  have hlogs := bourgain_cubic_truncation_log hNr hqNr hHcast
  have hlog0 : 0 ≤ Real.log (2*(N : ℝ)) := by linarith [hlogs.1]
  let χ := bourgainCubicSharpCutoff (N : ℝ) (N₁ : ℝ)
  let F : ℤ → ℂ := fun h => bourgainQuadraticGauss q a (b+h)*
    bourgainCubicFourierMode (fun x => (χ x : ℂ)) μ ((h : ℝ)/(q : ℝ)-θ)
  let M : ℤ → ℂ := fun h => bourgainQuadraticGauss q a (b+h)*
    bourgainCubicStationaryTerm μ N N₁ ((h : ℝ)/(q : ℝ)-θ)
  let T := Finset.Icc (-(H : ℤ)) (H : ℤ)
  let S := T.erase 0
  let E : ℂ := ∑ h ∈ S, bourgainQuadraticGauss q a (b+h)*
    (bourgainCubicFourierMode (fun x => (χ x : ℂ)) μ ((h : ℝ)/(q : ℝ)-θ)-
      bourgainCubicStationaryTerm μ N N₁ ((h : ℝ)/(q : ℝ)-θ))
  let tail : ℂ := ∑' h : ℤ, if H < h.natAbs then F h else 0
  have h0 : (0 : ℤ) ∈ T := by simp [T]
  have hE : E = (∑ h ∈ S, F h)-(∑ h ∈ S, M h) := by
    simp only [E,F,M,mul_sub,Finset.sum_sub_distrib]
  obtain ⟨hs,hsource⟩ := bourgain_cubic_shifted_exact_cutoff_poisson (N : ℤ) (N₁ : ℤ) μ θ q a b
  simp only [Int.cast_natCast] at hs hsource
  change Summable (fun h => ‖F h‖) at hs
  have hsplit := tsum_int_eq_sum_Icc_add_far hs.of_norm H
  change (∑' h : ℤ, F h) = (∑ h ∈ T, F h)+tail at hsplit
  have hFs : (∑ h ∈ T, F h) = (∑ h ∈ S, F h)+F 0 :=
    (Finset.sum_erase_add T F h0).symm
  have hMs : (∑ h ∈ T, M h) = (∑ h ∈ S, M h)+M 0 :=
    (Finset.sum_erase_add T M h0).symm
  rw [← bourgain_cubic_shifted_stationary_window hμ hNr hNNr hN₁r hμN q a b hθ hH]
  have he :
      (∑ n ∈ Finset.Icc (N : ℤ) (N₁ : ℤ),
        (𝐞 (μ*(n : ℝ)^3+θ*n+((a : ℝ)*(n : ℝ)^2+(b : ℝ)*(n : ℝ))/(q : ℝ)) : ℂ))-
        (q : ℂ)⁻¹*(∑ h ∈ T, M h) =
          (q : ℂ)⁻¹*(F 0-M 0)+(q : ℂ)⁻¹*E+(q : ℂ)⁻¹*tail := by
    rw [hsource]
    change (q : ℂ)⁻¹*(∑' h : ℤ, F h)-(q : ℂ)⁻¹*(∑ h ∈ T, M h) = _
    rw [hsplit,hFs,hMs,hE]
    ring
  change ‖(∑ n ∈ Finset.Icc (N : ℤ) (N₁ : ℤ),
    (𝐞 (μ*(n : ℝ)^3+θ*n+((a : ℝ)*(n : ℝ)^2+(b : ℝ)*(n : ℝ))/(q : ℝ)) : ℂ))-
    (q : ℂ)⁻¹*(∑ h ∈ T, M h)‖ ≤ _
  rw [he]

  have hz : ‖(q : ℂ)⁻¹*(F 0-M 0)‖ ≤
      Cz*(1/(μ*(N : ℝ)^2)+1/(Real.sqrt (μ*(N : ℝ))*Real.sqrt q)) := by
    have h := hzero μ N N₁ hμ hNr hNNr hN₁r hμN q hq a b ha θ
    simpa only [F,M,χ,Int.cast_zero,zero_div,zero_sub,add_zero,mul_sub] using h
  have hc := hcentral μ N N₁ hμ hNr hNNr hN₁r hμN q hq a b ha θ hθ H hH
  change ‖(q : ℂ)⁻¹*E‖ ≤
    Cc*(1/(Real.sqrt (μ*(N : ℝ))*Real.sqrt q)+
      Real.sqrt q*(1+Real.log (2*(H : ℝ)+1))) at hc
  have hunit : Real.sqrt (q : ℝ) ≤ 2*(Real.sqrt (q : ℝ)*Real.log (2*(N : ℝ))) := by
    have h := mul_le_mul_of_nonneg_left hlogs.1 (Real.sqrt_nonneg (q : ℝ))
    nlinarith
  have hc' : ‖(q : ℂ)⁻¹*E‖ ≤
      Cc*(1/(Real.sqrt (μ*(N : ℝ))*Real.sqrt q))+
        258*Cc*(Real.sqrt q*Real.log (2*(N : ℝ))) := by
    apply hc.trans
    have hm : Real.sqrt (q : ℝ)*(1+Real.log (2*(H : ℝ)+1)) ≤
        Real.sqrt (q : ℝ)*(258*Real.log (2*(N : ℝ))) :=
      mul_le_mul_of_nonneg_left hlogs.2 (Real.sqrt_nonneg _)
    have hmc := mul_le_mul_of_nonneg_left hm hCc0
    nlinarith
  have hf := hfar μ N N₁ hμ hNr hNNr hN₁r hμN q hq a b ha θ hθ H hH0
  change ‖(q : ℂ)⁻¹*tail‖ ≤ Cf*(N : ℝ)*(q : ℝ)*Real.sqrt q/(H : ℝ) at hf
  have hf' : ‖(q : ℂ)⁻¹*tail‖ ≤ 2*Cf*(Real.sqrt q*Real.log (2*(N : ℝ))) := by
    apply hf.trans
    rw [hHcast]
    have he' : Cf*(N : ℝ)*(q : ℝ)*Real.sqrt q/(64*(q : ℝ)*(N : ℝ)) =
        (Cf/64)*Real.sqrt q := by field_simp
    rw [he']
    calc
      _ ≤ Cf*Real.sqrt (q : ℝ) := mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left hunit hCf0
        nlinarith
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  apply (add_le_add (add_le_add hz hc') hf').trans
  have hmain0 : 0 ≤ Real.sqrt (q : ℝ)*Real.log (2*(N : ℝ)) := by positivity
  have hinv0 : 0 ≤ 1/(μ*(N : ℝ)^2) := by positivity
  have hcap0 : 0 ≤ 1/(Real.sqrt (μ*(N : ℝ))*Real.sqrt q) := by positivity
  have hbcoef : 258*Cc+2*Cf ≤ D := by dsimp only [D]; linarith
  have hucoef : Cz ≤ D := by dsimp only [D]; linarith
  have hvcoef : Cc+Cz ≤ D := by dsimp only [D]; linarith
  calc
    _ = (258*Cc+2*Cf)*(Real.sqrt q*Real.log (2*(N : ℝ)))+
        Cz*(1/(μ*(N : ℝ)^2))+
        (Cc+Cz)*(1/(Real.sqrt (μ*(N : ℝ))*Real.sqrt q)) := by ring
    _ ≤ D*(Real.sqrt q*Real.log (2*(N : ℝ)))+
        D*(1/(μ*(N : ℝ)^2))+
        D*(1/(Real.sqrt (μ*(N : ℝ))*Real.sqrt q)) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_right hbcoef hmain0)
        (mul_le_mul_of_nonneg_right hucoef hinv0)) (mul_le_mul_of_nonneg_right hvcoef hcap0)
    _ = _ := by ring

                                                             
private theorem exists_bourgain_cubic_shifted_gauss_closed :
    ∃ C ≥ (1 : ℝ), ∀ N N₁ q : ℕ, 1 ≤ N → N ≤ N₁ → N₁ ≤ 2*N →
      0 < q → q ≤ N → ∀ μ : ℝ, 0 < μ → μ*(N : ℝ)^2 ≤ 1 →
      ∀ a b : ℤ, IsCoprime a (q : ℤ) →
      ∀ θ : ℝ, |(q : ℝ)*θ| ≤ 1/2 →
        ‖(∑ n ∈ Finset.Icc (N : ℤ) (N₁ : ℤ),
          (𝐞 (μ*(n : ℝ)^3+θ*n+((a : ℝ)*(n : ℝ)^2+(b : ℝ)*(n : ℝ))/(q : ℝ)) : ℂ))-
          (q : ℂ)⁻¹*∑ h ∈ Finset.Icc ⌈(q : ℝ)*(3*μ*(N : ℝ)^2+θ)⌉ ⌊(q : ℝ)*(3*μ*(N₁ : ℝ)^2+θ)⌋,
            let r := Real.sqrt (((h : ℝ)/(q : ℝ)-θ)/(3*μ))
            bourgainQuadraticGauss q a (b+h)*
              ((𝐞 ((1 : ℝ)/8-2*μ*r^3) : ℂ)/(Real.sqrt (6*μ*r) : ℂ))‖ ≤
          C*(Real.sqrt N*Real.log (2*(N : ℝ))+1/(μ*(N : ℝ)^2)+
            1/(Real.sqrt (μ*(N : ℝ))*Real.sqrt q)) := by
  obtain ⟨C,hC,hbound⟩ := exists_bourgain_cubic_shifted_gauss_denominator_error
  refine ⟨C,hC,?_⟩
  intro N N₁ q hN hNN hN₁ hq hqN μ hμ hμN a b ha θ hθ
  apply (hbound N N₁ q hN hNN hN₁ hq hqN μ hμ hμN a b ha θ hθ).trans
  have hlog : 0 ≤ Real.log (2*(N : ℝ)) := by
    apply Real.log_nonneg
    have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
    linarith only [hn]
  have hsq : Real.sqrt (q : ℝ) ≤ Real.sqrt (N : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hqN)
  gcongr


private theorem bourgain_cubic_real_linear_reindex (q : ℕ) (hq : 0 < q)
    (a b : ℤ) (μ N N₁ ℓ : ℝ) :
    (∑ h ∈ Finset.Icc
        ⌈(q : ℝ)*(3*μ*N^2+(ℓ-(b : ℝ)/(q : ℝ)))⌉
        ⌊(q : ℝ)*(3*μ*N₁^2+(ℓ-(b : ℝ)/(q : ℝ)))⌋,
      let r := Real.sqrt (((h : ℝ)/(q : ℝ)-(ℓ-(b : ℝ)/(q : ℝ)))/(3*μ))
      bourgainQuadraticGauss q a (b+h)*
        ((𝐞 ((1 : ℝ)/8-2*μ*r^3) : ℂ)/(Real.sqrt (6*μ*r) : ℂ))) =
    ∑ k ∈ Finset.Icc ⌈(q : ℝ)*(3*μ*N^2+ℓ)⌉ ⌊(q : ℝ)*(3*μ*N₁^2+ℓ)⌋,
      let r := Real.sqrt (((k : ℝ)/(q : ℝ)-ℓ)/(3*μ))
      bourgainQuadraticGauss q a k*
        ((𝐞 ((1 : ℝ)/8-2*μ*r^3) : ℂ)/(Real.sqrt (6*μ*r) : ℂ)) := by
  classical
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  let S := Finset.Icc
    ⌈(q : ℝ)*(3*μ*N^2+(ℓ-(b : ℝ)/(q : ℝ)))⌉
    ⌊(q : ℝ)*(3*μ*N₁^2+(ℓ-(b : ℝ)/(q : ℝ)))⌋
  let T := Finset.Icc ⌈(q : ℝ)*(3*μ*N^2+ℓ)⌉ ⌊(q : ℝ)*(3*μ*N₁^2+ℓ)⌋
  have he (X : ℝ) : (q : ℝ)*(3*μ*X^2+(ℓ-(b : ℝ)/(q : ℝ))) =
      (q : ℝ)*(3*μ*X^2+ℓ)-(b : ℝ) := by field_simp; ring
  have hmem (h : ℤ) : h ∈ S ↔ b+h ∈ T := by
    simp only [S,T,Finset.mem_Icc,Int.ceil_le,Int.le_floor,Int.cast_add,he]
    constructor <;> intro hh <;> constructor <;> linarith [hh.1,hh.2]
  refine Finset.sum_bij (fun h _ => b+h) ?_ ?_ ?_ ?_
  · intro h hh
    exact (hmem h).mp hh
  · intro h _ k _ hk
    exact add_left_cancel hk
  · intro k hk
    refine ⟨k-b,?_,?_⟩
    · exact (hmem (k-b)).mpr (by simpa only [show b+(k-b) = k by omega] using hk)
    ·
      omega
  · intro h _
    have hfreq : (h : ℝ)/(q : ℝ)-(ℓ-(b : ℝ)/(q : ℝ)) =
        ((b+h : ℤ) : ℝ)/(q : ℝ)-ℓ := by push_cast; ring
    dsimp only
    rw [hfreq]

private theorem bourgain_cubic_real_linear_center (q : ℕ) (hq : 0 < q) (ℓ : ℝ) :
    |(q : ℝ)*(ℓ-(⌊(q : ℝ)*ℓ+1/2⌋ : ℝ)/(q : ℝ))| ≤ 1/2 := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have he : (q : ℝ)*(ℓ-(⌊(q : ℝ)*ℓ+1/2⌋ : ℝ)/(q : ℝ)) =
      (q : ℝ)*ℓ-(⌊(q : ℝ)*ℓ+1/2⌋ : ℝ) := by field_simp
  rw [he]
  have hl := Int.floor_le ((q : ℝ)*ℓ+1/2)
  have hr := Int.lt_floor_add_one ((q : ℝ)*ℓ+1/2)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

private theorem exists_bourgain_cubic_real_linear_closed :
    ∃ C ≥ (1 : ℝ), ∀ N N₁ q : ℕ, 1 ≤ N → N ≤ N₁ → N₁ ≤ 2*N →
      0 < q → q ≤ N → ∀ μ : ℝ, 0 < μ → μ*(N : ℝ)^2 ≤ 1 →
      ∀ a : ℤ, IsCoprime a (q : ℤ) → ∀ ℓ : ℝ,
        ‖(∑ n ∈ Finset.Icc (N : ℤ) (N₁ : ℤ),
          (𝐞 (μ*(n : ℝ)^3+(a : ℝ)*(n : ℝ)^2/(q : ℝ)+ℓ*n) : ℂ))-
          (q : ℂ)⁻¹*∑ k ∈ Finset.Icc
            ⌈(q : ℝ)*(3*μ*(N : ℝ)^2+ℓ)⌉ ⌊(q : ℝ)*(3*μ*(N₁ : ℝ)^2+ℓ)⌋,
            let r := Real.sqrt (((k : ℝ)/(q : ℝ)-ℓ)/(3*μ))
            bourgainQuadraticGauss q a k*
              ((𝐞 ((1 : ℝ)/8-2*μ*r^3) : ℂ)/(Real.sqrt (6*μ*r) : ℂ))‖ ≤
          C*(Real.sqrt N*Real.log (2*(N : ℝ))+1/(μ*(N : ℝ)^2)+
            1/(Real.sqrt (μ*(N : ℝ))*Real.sqrt q)) := by
  obtain ⟨C,hC,hshift⟩ := exists_bourgain_cubic_shifted_gauss_closed
  refine ⟨C,hC,?_⟩
  intro N N₁ q hN hNN hN₁ hq hqN μ hμ hμN a ha ℓ
  let b : ℤ := ⌊(q : ℝ)*ℓ+1/2⌋
  have h := hshift N N₁ q hN hNN hN₁ hq hqN μ hμ hμN a b ha
    (ℓ-(b : ℝ)/(q : ℝ)) (bourgain_cubic_real_linear_center q hq ℓ)
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have he (n : ℤ) :
      μ*(n : ℝ)^3+(ℓ-(b : ℝ)/(q : ℝ))*n+
          ((a : ℝ)*(n : ℝ)^2+(b : ℝ)*(n : ℝ))/(q : ℝ) =
        μ*(n : ℝ)^3+(a : ℝ)*(n : ℝ)^2/(q : ℝ)+ℓ*n := by field_simp; ring
  simp only [he] at h
  rw [bourgain_cubic_real_linear_reindex q hq a b μ N N₁ ℓ] at h
  exact h

                                                                     
                                                                          
                                                                   
theorem exists_bourgain_cubic_real_linear_stationary :
    ∃ C ≥ (1 : ℝ), ∀ N N₁ q : ℕ, 1 ≤ N → N ≤ N₁ → N₁ ≤ 2*N →
      0 < q → q ≤ N → ∀ μ : ℝ, 0 < μ → μ*(N : ℝ)^2 ≤ 1 →
      ∀ a : ℤ, IsCoprime a (q : ℤ) → ∀ ℓ : ℝ,
        ‖(∑ n ∈ Finset.Ioc (N : ℤ) (N₁ : ℤ),
          (𝐞 (μ*(n : ℝ)^3+(a : ℝ)*(n : ℝ)^2/(q : ℝ)+ℓ*n) : ℂ))-
          (q : ℂ)⁻¹*∑ k ∈ Finset.Icc
            ⌈(q : ℝ)*(3*μ*(N : ℝ)^2+ℓ)⌉ ⌊(q : ℝ)*(3*μ*(N₁ : ℝ)^2+ℓ)⌋,
            let r := Real.sqrt (((k : ℝ)/(q : ℝ)-ℓ)/(3*μ))
            bourgainQuadraticGauss q a k*
              ((𝐞 ((1 : ℝ)/8-2*μ*r^3) : ℂ)/(Real.sqrt (6*μ*r) : ℂ))‖ ≤
          C*(Real.sqrt N*Real.log (2*(N : ℝ))+1/(μ*(N : ℝ)^2)+
            1/(Real.sqrt (μ*(N : ℝ))*Real.sqrt q)) := by
  classical
  obtain ⟨C,hC,hclosed⟩ := exists_bourgain_cubic_real_linear_closed
  refine ⟨3*C,by linarith,?_⟩
  intro N N₁ q hN hNN hN₁ hq hqN μ hμ hμN a ha ℓ
  have h := hclosed N N₁ q hN hNN hN₁ hq hqN μ hμ hμN a ha ℓ
  let P : ℤ → ℂ := fun n => (𝐞 (μ*(n : ℝ)^3+(a : ℝ)*(n : ℝ)^2/(q : ℝ)+ℓ*n) : ℂ)
  let main : ℂ := (q : ℂ)⁻¹*
    ∑ h ∈ Finset.Icc ⌈(q : ℝ)*(3*μ*(N : ℝ)^2+ℓ)⌉ ⌊(q : ℝ)*(3*μ*(N₁ : ℝ)^2+ℓ)⌋,
      let r := Real.sqrt (((h : ℝ)/(q : ℝ)-ℓ)/(3*μ))
      bourgainQuadraticGauss q a h*
        ((𝐞 ((1 : ℝ)/8-2*μ*r^3) : ℂ)/(Real.sqrt (6*μ*r) : ℂ))
  have hmem : (N : ℤ) ∈ Finset.Icc (N : ℤ) (N₁ : ℤ) := by
    exact Finset.mem_Icc.mpr ⟨le_rfl,by exact_mod_cast hNN⟩
  have hsum :
      (∑ n ∈ Finset.Icc (N : ℤ) (N₁ : ℤ), P n) =
        (∑ n ∈ Finset.Ioc (N : ℤ) (N₁ : ℤ), P n)+P N := by
    have hs := Finset.sum_erase_add (Finset.Icc (N : ℤ) (N₁ : ℤ)) P hmem
    simpa only [Finset.Icc_erase_left] using hs.symm
  have he :
      (∑ n ∈ Finset.Ioc (N : ℤ) (N₁ : ℤ), P n)-main =
        ((∑ n ∈ Finset.Icc (N : ℤ) (N₁ : ℤ), P n)-main)-P N := by
    rw [hsum]
    ring
  change ‖(∑ n ∈ Finset.Ioc (N : ℤ) (N₁ : ℤ), P n)-main‖ ≤ _
  rw [he]
  apply (norm_sub_le _ _).trans
  have hP : ‖P N‖ = 1 := Circle.norm_coe _
  rw [hP]
  apply (add_le_add h le_rfl).trans
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNr0 : (0 : ℝ) < N := by linarith
  have hsqrt : 1 ≤ Real.sqrt (N : ℝ) := by
    nlinarith [Real.sq_sqrt hNr0.le,Real.sqrt_nonneg (N : ℝ)]
  have hl2 : (1 : ℝ)/2 ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (show 2 ≤ 2*(N : ℝ) by linarith)
  have htwolog : 1 ≤ 2*Real.log (2*(N : ℝ)) := by linarith
  have hunit : 1 ≤ 2*(Real.sqrt N*Real.log (2*(N : ℝ))) := by
    have hh := one_le_mul_of_one_le_of_one_le hsqrt htwolog
    nlinarith
  have hinv : 0 ≤ 1/(μ*(N : ℝ)^2) := by positivity
  have hC0 : 0 ≤ C := by linarith
  have hm := mul_le_mul_of_nonneg_right hC
    (show 0 ≤ 2*(Real.sqrt N*Real.log (2*(N : ℝ))) by linarith)
  have hcap : 0 ≤ 1/(Real.sqrt (μ*(N : ℝ))*Real.sqrt q) := by positivity
  nlinarith [mul_nonneg hC0 hinv,mul_nonneg hC0 hcap]

                                                                 
                                                                   
                                                            
theorem exists_bourgain_cubic_minor_arc_stationary :
    ∃ C ≥ (1 : ℝ), ∀ N N₁ q : ℕ, 1 ≤ N → N ≤ N₁ → N₁ ≤ 2*N →
      0 < q → q ≤ N → ∀ μ : ℝ, 0 < μ → μ*(N : ℝ)^2 ≤ 1 → 1 ≤ μ*(q : ℝ)^2*N →
      ∀ a : ℤ, IsCoprime a (q : ℤ) → ∀ ℓ : ℝ,
        ‖(∑ n ∈ Finset.Ioc (N : ℤ) (N₁ : ℤ),
          (𝐞 (μ*(n : ℝ)^3+(a : ℝ)*(n : ℝ)^2/(q : ℝ)+ℓ*n) : ℂ))-
          (q : ℂ)⁻¹*∑ k ∈ Finset.Icc
            ⌈(q : ℝ)*(3*μ*(N : ℝ)^2+ℓ)⌉ ⌊(q : ℝ)*(3*μ*(N₁ : ℝ)^2+ℓ)⌋,
            let r := Real.sqrt (((k : ℝ)/(q : ℝ)-ℓ)/(3*μ))
            bourgainQuadraticGauss q a k*
              ((𝐞 ((1 : ℝ)/8-2*μ*r^3) : ℂ)/(Real.sqrt (6*μ*r) : ℂ))‖ ≤
          C*(Real.sqrt N*Real.log (2*(N : ℝ))+1/(μ*(N : ℝ)^2)) := by
  obtain ⟨C,hC,hreal⟩ := exists_bourgain_cubic_real_linear_stationary
  refine ⟨3*C,by linarith,?_⟩
  intro N N₁ q hN hNN hN₁ hq hqN μ hμ hμN hscale a ha ℓ
  have h := hreal N N₁ q hN hNN hN₁ hq hqN μ hμ hμN a ha ℓ
  apply h.trans
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNr0 : (0 : ℝ) < N := by linarith
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hqNr : (q : ℝ) ≤ N := by exact_mod_cast hqN
  have hroot : 1 ≤ Real.sqrt (μ*(N : ℝ))*(q : ℝ) := by
    have hs := Real.sq_sqrt (show 0 ≤ μ*(N : ℝ) by positivity)
    have hs' : (Real.sqrt (μ*(N : ℝ))*(q : ℝ))^2 = μ*(q : ℝ)^2*N := by
      rw [mul_pow,hs]
      ring
    have hp : 0 ≤ Real.sqrt (μ*(N : ℝ))*(q : ℝ) := by positivity
    nlinarith
  have hcap : 1/(Real.sqrt (μ*(N : ℝ))*Real.sqrt q) ≤ Real.sqrt (q : ℝ) := by
    apply (div_le_iff₀ (show 0 < Real.sqrt (μ*(N : ℝ))*Real.sqrt q by positivity)).mpr
    calc
      (1 : ℝ) ≤ Real.sqrt (μ*(N : ℝ))*(q : ℝ) := hroot
      _ = Real.sqrt (q : ℝ)*(Real.sqrt (μ*(N : ℝ))*Real.sqrt q) := by
        rw [show Real.sqrt (q : ℝ)*(Real.sqrt (μ*(N : ℝ))*Real.sqrt q) =
          Real.sqrt (μ*(N : ℝ))*(Real.sqrt (q : ℝ))^2 by ring,
          Real.sq_sqrt hqr.le]
  have hlog2 : (1 : ℝ)/2 ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (show 2 ≤ 2*(N : ℝ) by linarith)
  have hunit : Real.sqrt (N : ℝ) ≤ 2*(Real.sqrt N*Real.log (2*(N : ℝ))) := by
    have hh := mul_le_mul_of_nonneg_left
      (show 1 ≤ 2*Real.log (2*(N : ℝ)) by linarith) (Real.sqrt_nonneg (N : ℝ))
    nlinarith
  have hcap' := hcap.trans ((Real.sqrt_le_sqrt hqNr).trans hunit)
  have hC0 : 0 ≤ C := by linarith
  have hc := mul_le_mul_of_nonneg_left hcap' hC0
  have hi : 0 ≤ C*(1/(μ*(N : ℝ)^2)) := by positivity
  nlinarith


private theorem bourgain_common_weighted_prefix {ι : Type*}
    (S : Finset ι) (w z : ι → ℕ → ℂ) (H : ℕ) {K : ℝ}
    (hK : 0 ≤ K) (hw : ∀ m ∈ S, ‖w m (H-1)‖ ≤ 1)
    (hd : ∀ m ∈ S, ∀ j ∈ Finset.range (H-1), ‖w m (j+1)-w m j‖ ≤ K) :
    ∃ L ≤ H, (∑ m ∈ S, ‖∑ j ∈ Finset.range H, w m j*z m j‖) ≤
      (1+K*H)*∑ m ∈ S, ‖∑ j ∈ Finset.range L, z m j‖ := by
  classical
  let Z : ℕ → ℝ := fun n => ∑ m ∈ S, ‖∑ j ∈ Finset.range n, z m j‖
  have hZ (n : ℕ) : 0 ≤ Z n := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  obtain ⟨L,hL,hmax⟩ := (Finset.range (H+1)).exists_max_image Z
    (Finset.nonempty_range_iff.mpr (by omega))
  have hL' : L ≤ H := by have hh := Finset.mem_range.mp hL; omega
  have hmax' (n : ℕ) (hn : n ≤ H) : Z n ≤ Z L :=
    hmax n (Finset.mem_range.mpr (by omega))
  refine ⟨L,hL',?_⟩
  calc
    _ ≤ ∑ m ∈ S, (‖∑ j ∈ Finset.range H, z m j‖+
        ∑ j ∈ Finset.range (H-1), K*‖∑ k ∈ Finset.range (j+1), z m k‖) := by
      apply Finset.sum_le_sum
      intro m hm
      apply (norm_sum_mul_le_discrete_parts (w m) (z m) H).trans
      apply add_le_add
      · simpa only [one_mul] using mul_le_mul_of_nonneg_right (hw m hm) (norm_nonneg _)
      · apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_right (hd m hm j hj) (norm_nonneg _)
    _ = Z H+K*∑ j ∈ Finset.range (H-1), Z (j+1) := by
      rw [Finset.sum_add_distrib,Finset.sum_comm]
      simp only [Z,Finset.mul_sum]
    _ ≤ Z L+K*∑ _j ∈ Finset.range (H-1), Z L := by
      apply add_le_add (hmax' H le_rfl)
      apply mul_le_mul_of_nonneg_left _ hK
      apply Finset.sum_le_sum
      intro j hj
      exact hmax' (j+1) (by have hh := Finset.mem_range.mp hj; omega)
    _ = (1+K*((H-1 : ℕ) : ℝ))*Z L := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      ring
    _ ≤ (1+K*(H : ℝ))*Z L := by
      apply mul_le_mul_of_nonneg_right _ (hZ L)
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (by exact_mod_cast Nat.sub_le H 1) hK)

private theorem bourgain_cubic_taylor_error_jet
    {f : ℝ → ℝ} {m L B α D x : ℝ}
    (hL : 0 ≤ L) (hD : 0 ≤ D) (hx : |x| ≤ L)
    (hf : ∀ y ∈ Icc (m-L) (m+L), ContDiffAt ℝ 4 f y)
    (hfour : ∀ y ∈ Icc (m-L) (m+L), |iteratedDeriv 4 f y| ≤ B)
    (hα : |iteratedDeriv 2 f m/2-α| ≤ D) :
    let u : ℝ → ℝ := fun y => f (m+y)-f m-deriv f m*y-α*y^2-
      (iteratedDeriv 3 f m/6)*y^3
    HasDerivAt u (deriv u x) x ∧ |deriv u x| ≤ B*L^3+2*D*L := by
  let u : ℝ → ℝ := fun y => f (m+y)-f m-deriv f m*y-α*y^2-
    (iteratedDeriv 3 f m/6)*y^3
  let δ := iteratedDeriv 2 f m/2-α
  have hxe := abs_le.mp hx
  have hm : m ∈ Icc (m-L) (m+L) := ⟨by linarith,by linarith⟩
  have hmx : m+x ∈ Icc (m-L) (m+L) := ⟨by linarith [hxe.1],by linarith [hxe.2]⟩
  have hseg : uIcc m (m+x) ⊆ Icc (m-L) (m+L) := uIcc_subset_Icc hm hmx
  have hp : ContDiffAt ℝ 4 (finiteTaylorPolynomial f 3 m) (m+x) :=
    (finiteTaylorPolynomial_contDiff f 3 m).contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)
  have hc : ContDiffAt ℝ 4 (robertSargosCubicRemainder f m) x :=
    ((hf _ hmx).sub hp).comp x (contDiffAt_const.add contDiffAt_id)
  have hr : HasDerivAt (robertSargosCubicRemainder f m)
      (deriv (robertSargosCubicRemainder f m) x) x :=
    (hc.differentiableAt (by norm_num)).hasDerivAt
  have he : u = fun y => robertSargosCubicRemainder f m y+δ*y^2 := by
    funext y
    dsimp only [u,δ]
    rw [robertSargosCubicRemainder,robertSargos_cubic_polynomial]
    ring
  have hd : HasDerivAt u (deriv (robertSargosCubicRemainder f m) x+2*δ*x) x := by
    rw [he]
    convert hr.add (((hasDerivAt_id x).pow 2).const_mul δ) using 1
    · rfl
    · norm_num
      ring
  have hb := robertSargos_cubic_remainder_radius_jets (j := 1) (by omega) hx
    (fun y hy => hf y (hseg hy)) (fun y hy => hfour y (hseg hy))
  simp only [iteratedDeriv_one,show 4-1 = 3 from rfl] at hb
  refine ⟨hd.differentiableAt.hasDerivAt,?_⟩
  change |deriv u x| ≤ _
  rw [hd.deriv]
  apply (abs_add_le _ _).trans
  apply add_le_add hb
  rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hδ : |δ| ≤ D := hα
  nlinarith [mul_le_mul hδ hx (abs_nonneg x) hD]

                                                                    
                                                                       
                                                                          
theorem bourgain_cubic_taylor_common_prefix {ι : Type*}
    (S : Finset ι) (f : ι → ℝ → ℝ) (m α : ι → ℝ) (A : ℝ) (H : ℕ)
    {L B D : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hRange : ∀ x ∈ Icc A (A+H), |x| ≤ L)
    (hf : ∀ i ∈ S, ∀ y ∈ Icc (m i-L) (m i+L), ContDiffAt ℝ 4 (f i) y)
    (hfour : ∀ i ∈ S, ∀ y ∈ Icc (m i-L) (m i+L), |iteratedDeriv 4 (f i) y| ≤ B)
    (hα : ∀ i ∈ S, |iteratedDeriv 2 (f i) (m i)/2-α i| ≤ D) :
    ∃ J ≤ H,
      (∑ i ∈ S, ‖∑ j ∈ Finset.range H, (𝐞 (f i (m i+(A+j))) : ℂ)‖) ≤
        (1+2*Real.pi*H*(B*L^3+2*D*L))*
          ∑ i ∈ S, ‖∑ j ∈ Finset.range J,
            (𝐞 ((iteratedDeriv 3 (f i) (m i)/6)*(A+j)^3+
              α i*(A+j)^2+deriv (f i) (m i)*(A+j)) : ℂ)‖ := by
  classical
  let K := B*L^3+2*D*L
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  let u : ι → ℝ → ℝ := fun i x => f i (m i+x)-f i (m i)-
    deriv (f i) (m i)*x-α i*x^2-(iteratedDeriv 3 (f i) (m i)/6)*x^3
  let g : ι → ℝ → ℝ := fun i x =>
    (iteratedDeriv 3 (f i) (m i)/6)*x^3+α i*x^2+deriv (f i) (m i)*x
  let w : ι → ℕ → ℂ := fun i j => fordAdditiveCharacter (u i (A+j))
  let z : ι → ℕ → ℂ := fun i j => fordAdditiveCharacter (g i (A+j))
  have hu (i : ι) (hi : i ∈ S) (x : ℝ) (hx : x ∈ Icc A (A+H)) :
      HasDerivAt (u i) (deriv (u i) x) x ∧ |deriv (u i) x| ≤ K :=
    bourgain_cubic_taylor_error_jet hL hD (hRange x hx) (hf i hi) (hfour i hi) (hα i hi)
  have hd : ∀ i ∈ S, ∀ j ∈ Finset.range (H-1),
      ‖w i (j+1)-w i j‖ ≤ 2*Real.pi*K := by
    intro i hi j hj
    have hjH : (j : ℝ)+1 ≤ H := by
      exact_mod_cast (show j+1 ≤ H by have hh := Finset.mem_range.mp hj; omega)
    have hx : A+j ∈ Icc A (A+H) := by
      constructor <;> linarith [Nat.cast_nonneg (α := ℝ) j]
    have hy : A+(j+1) ∈ Icc A (A+H) := by
      constructor <;> linarith [Nat.cast_nonneg (α := ℝ) j]
    have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (hu i hi x hx).1.hasDerivWithinAt)
      (fun x hx => by simpa only [Real.norm_eq_abs] using (hu i hi x hx).2)
      (convex_Icc A (A+H)) hx hy
    have he : A+(j+1)-(A+j) = 1 := by ring
    simp only [Real.norm_eq_abs,he,abs_one,mul_one] at hb
    dsimp only [w]
    push_cast
    exact (sargos_character_sub_norm_le _ _).trans
      (mul_le_mul_of_nonneg_left hb (by positivity))
  obtain ⟨J,hJ,hbound⟩ := bourgain_common_weighted_prefix S w z H
    (show 0 ≤ 2*Real.pi*K by positivity)
    (fun i _ => le_of_eq (sargos_character_norm _)) hd
  have hsource (i : ι) :
      ‖∑ j ∈ Finset.range H, (𝐞 (f i (m i+(A+j))) : ℂ)‖ =
        ‖∑ j ∈ Finset.range H, w i j*z i j‖ := by
    have he (j : ℕ) : f i (m i+(A+j)) = f i (m i)+u i (A+j)+g i (A+j) := by
      dsimp only [u,g]
      ring
    simp only [← sargos_ford_character_eq_fourier,he,fordAdditiveCharacter_add]
    have hsum :
        (∑ j ∈ Finset.range H,
          fordAdditiveCharacter (f i (m i))*fordAdditiveCharacter (u i (A+j))*
            fordAdditiveCharacter (g i (A+j))) =
        fordAdditiveCharacter (f i (m i))*∑ j ∈ Finset.range H, w i j*z i j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [w,z]
      ring
    rw [hsum,norm_mul,sargos_character_norm,one_mul]
  refine ⟨J,hJ,?_⟩
  calc
    _ = ∑ i ∈ S, ‖∑ j ∈ Finset.range H, w i j*z i j‖ :=
      Finset.sum_congr rfl (fun i _ => hsource i)
    _ ≤ (1+(2*Real.pi*K)*(H : ℝ))*∑ i ∈ S, ‖∑ j ∈ Finset.range J, z i j‖ := hbound
    _ = _ := by
      simp only [z,g,sargos_ford_character_eq_fourier]
      congr 1
      dsimp only [K]
      ring

public  theorem bourgain_cubic_taylor_short_cost {N H : ℕ} {B D : ℝ}
    (hH : H ≤ N) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hfour : B*(2*(N : ℝ)+1)^4 ≤ 1)
    (hquad : D*(2*(N : ℝ)+1)^2 ≤ 1) :
    1+2*Real.pi*H*(B*(2*(N : ℝ)+1)^3+2*D*(2*(N : ℝ)+1)) ≤ 1+6*Real.pi := by
  let L := 2*(N : ℝ)+1
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hHL : (H : ℝ) ≤ L := by
    have hh : (H : ℝ) ≤ N := by exact_mod_cast hH
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    dsimp only [L]
    linarith
  have hb := mul_le_mul_of_nonneg_left hHL (show 0 ≤ B*L^3 by positivity)
  have hd := mul_le_mul_of_nonneg_left hHL (show 0 ≤ D*L by positivity)
  have hcost : (H : ℝ)*(B*L^3+2*D*L) ≤ 3 := by
    change B*L^4 ≤ 1 at hfour
    change D*L^2 ≤ 1 at hquad
    nlinarith
  have hp := mul_le_mul_of_nonneg_left hcost (show 0 ≤ 2*Real.pi by positivity)
  change 1+2*Real.pi*(H : ℝ)*(B*L^3+2*D*L) ≤ _
  nlinarith

public  theorem bourgain_cubic_Ioc_range (N H : ℕ) (μ α ℓ : ℝ) :
    (∑ n ∈ Finset.Ioc (N : ℤ) ((N : ℤ)+H),
      (𝐞 (μ*(n : ℝ)^3+α*(n : ℝ)^2+ℓ*n) : ℂ)) =
      ∑ j ∈ Finset.range H,
        (𝐞 (μ*((N : ℝ)+1+j)^3+α*((N : ℝ)+1+j)^2+ℓ*((N : ℝ)+1+j)) : ℂ) := by
  rw [sargos_sum_Ioc_eq_range]
  apply Finset.sum_congr rfl
  intro j _
  have he : (((N : ℤ)+j+1 : ℤ) : ℝ) = (N : ℝ)+1+j := by push_cast; ring
  simp only [he]

public  theorem bourgain_source_Ioc_range (f : ℝ → ℝ) (m : ℝ) (N H : ℕ) :
    (∑ n ∈ Finset.Ioc (N : ℤ) ((N : ℤ)+H), (𝐞 (f (m+n)) : ℂ)) =
      ∑ j ∈ Finset.range H, (𝐞 (f (m+((N : ℝ)+1+j))) : ℂ) := by
  rw [sargos_sum_Ioc_eq_range]
  apply Finset.sum_congr rfl
  intro j _
  have he : (((N : ℤ)+j+1 : ℤ) : ℝ) = (N : ℝ)+1+j := by push_cast; ring
  simp only [he]

                                                                         
                                                                       
                                                              
theorem exists_bourgain_cubic_C4_source_entry :
    ∃ C ≥ (1 : ℝ), ∀ (ι : Type*) (S : Finset ι) (f : ι → ℝ → ℝ)
      (m : ι → ℝ) (a : ι → ℤ) (q : ι → ℕ) (N H : ℕ),
      1 ≤ N → H ≤ N → ∀ B D : ℝ, 0 ≤ B → 0 ≤ D →
      B*(2*(N : ℝ)+1)^4 ≤ 1 → D*(2*(N : ℝ)+1)^2 ≤ 1 →
      (∀ i ∈ S, ∀ y ∈ Icc (m i-(2*(N : ℝ)+1)) (m i+(2*(N : ℝ)+1)),
        ContDiffAt ℝ 4 (f i) y) →
      (∀ i ∈ S, ∀ y ∈ Icc (m i-(2*(N : ℝ)+1)) (m i+(2*(N : ℝ)+1)),
        |iteratedDeriv 4 (f i) y| ≤ B) →
      (∀ i ∈ S, |iteratedDeriv 2 (f i) (m i)/2-(a i : ℝ)/(q i : ℝ)| ≤ D) →
      let μ := fun i => iteratedDeriv 3 (f i) (m i)/6
      let ℓ := fun i => deriv (f i) (m i)
      (∀ i ∈ S, 0 < q i ∧ q i ≤ N ∧ IsCoprime (a i) (q i : ℤ) ∧
        0 < μ i ∧ μ i*(N : ℝ)^2 ≤ 1 ∧ 1 ≤ μ i*(q i : ℝ)^2*N) →
      ∃ J ≤ H,
        (∑ i ∈ S, ‖∑ n ∈ Finset.Ioc (N : ℤ) ((N : ℤ)+H),
          (𝐞 (f i (m i+n)) : ℂ)‖) ≤
        C*((∑ i ∈ S,
          ‖(q i : ℂ)⁻¹*∑ k ∈ Finset.Icc
            ⌈(q i : ℝ)*(3*μ i*(N : ℝ)^2+ℓ i)⌉
            ⌊(q i : ℝ)*(3*μ i*((N : ℝ)+J)^2+ℓ i)⌋,
            let r := Real.sqrt (((k : ℝ)/(q i : ℝ)-ℓ i)/(3*μ i))
            bourgainQuadraticGauss (q i) (a i) k*
              ((𝐞 ((1 : ℝ)/8-2*μ i*r^3) : ℂ)/(Real.sqrt (6*μ i*r) : ℂ))‖)+
          ∑ i ∈ S, (Real.sqrt N*Real.log (2*(N : ℝ))+1/(μ i*(N : ℝ)^2))) := by
  classical
  obtain ⟨C,hC,htransform⟩ := exists_bourgain_cubic_minor_arc_stationary
  let P := 1+6*Real.pi
  have hP : 1 ≤ P := by dsimp only [P]; linarith [Real.pi_pos]
  have hP0 : 0 ≤ P := by linarith
  refine ⟨P*C,one_le_mul_of_one_le_of_one_le hP hC,?_⟩
  intro ι S f m a q N H hN hH B D hB hD hfourSmall hquadSmall hf hfour hα μ ℓ hscale
  let L := 2*(N : ℝ)+1
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hRange : ∀ x ∈ Icc ((N : ℝ)+1) ((N : ℝ)+1+H), |x| ≤ L := by
    intro x hx
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hh : (H : ℝ) ≤ N := by exact_mod_cast hH
    rw [abs_of_nonneg (by linarith [hx.1] : 0 ≤ x)]
    dsimp only [L]
    linarith [hx.2]
  obtain ⟨J,hJ,hprefix⟩ := bourgain_cubic_taylor_common_prefix S f m
    (fun i => (a i : ℝ)/(q i : ℝ)) ((N : ℝ)+1) H hL hB hD hRange hf hfour hα
  let Z : ι → ℂ := fun i => ∑ n ∈ Finset.Ioc (N : ℤ) ((N : ℤ)+J),
    (𝐞 (μ i*(n : ℝ)^3+((a i : ℝ)/(q i : ℝ))*(n : ℝ)^2+ℓ i*n) : ℂ)
  let M : ι → ℂ := fun i => (q i : ℂ)⁻¹*∑ k ∈ Finset.Icc
    ⌈(q i : ℝ)*(3*μ i*(N : ℝ)^2+ℓ i)⌉ ⌊(q i : ℝ)*(3*μ i*((N : ℝ)+J)^2+ℓ i)⌋,
    let r := Real.sqrt (((k : ℝ)/(q i : ℝ)-ℓ i)/(3*μ i))
    bourgainQuadraticGauss (q i) (a i) k*
      ((𝐞 ((1 : ℝ)/8-2*μ i*r^3) : ℂ)/(Real.sqrt (6*μ i*r) : ℂ))
  let E : ι → ℝ := fun i => Real.sqrt N*Real.log (2*(N : ℝ))+1/(μ i*(N : ℝ)^2)
  have hsource :
      (∑ i ∈ S, ‖∑ n ∈ Finset.Ioc (N : ℤ) ((N : ℤ)+H),
        (𝐞 (f i (m i+n)) : ℂ)‖) ≤ P*∑ i ∈ S, ‖Z i‖ := by
    have hp := bourgain_cubic_taylor_short_cost hH hB hD hfourSmall hquadSmall
    simp only [bourgain_source_Ioc_range]
    apply hprefix.trans
    have hn : 0 ≤ ∑ i ∈ S, ‖Z i‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have hz : (∑ i ∈ S, ‖Z i‖) =
        ∑ i ∈ S, ‖∑ j ∈ Finset.range J,
          (𝐞 ((iteratedDeriv 3 (f i) (m i)/6)*((N : ℝ)+1+j)^3+
            ((a i : ℝ)/(q i : ℝ))*((N : ℝ)+1+j)^2+
            deriv (f i) (m i)*((N : ℝ)+1+j)) : ℂ)‖ := by
      simp only [Z,bourgain_cubic_Ioc_range,μ,ℓ]
    rw [← hz]
    exact mul_le_mul_of_nonneg_right hp hn
  have hZ (i : ι) (hi : i ∈ S) : ‖Z i‖ ≤ ‖M i‖+C*E i := by
    obtain ⟨hqi,hqiN,hai,hμi,hμiN,hμiq⟩ := hscale i hi
    have ht := htransform N (N+J) (q i) hN (by omega) (by omega) hqi hqiN
      (μ i) hμi hμiN hμiq (a i) hai (ℓ i)
    have hc (n : ℤ) : ((a i : ℝ)/(q i : ℝ))*(n : ℝ)^2 =
        (a i : ℝ)*(n : ℝ)^2/(q i : ℝ) := by ring
    have ht' : ‖Z i-M i‖ ≤ C*E i := by
      simpa only [Z,M,E,Nat.cast_add,hc] using ht
    calc
      _ = ‖(Z i-M i)+M i‖ := by congr 1; ring
      _ ≤ ‖Z i-M i‖+‖M i‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  refine ⟨J,hJ,?_⟩
  apply hsource.trans
  apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hZ) hP0).trans
  change P*(∑ i ∈ S, (‖M i‖+C*E i)) ≤ P*C*((∑ i ∈ S, ‖M i‖)+∑ i ∈ S, E i)
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  have hm : 0 ≤ ∑ i ∈ S, ‖M i‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hb : (∑ i ∈ S, ‖M i‖)+C*(∑ i ∈ S, E i) ≤
      C*((∑ i ∈ S, ‖M i‖)+(∑ i ∈ S, E i)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) hm]
  exact (mul_le_mul_of_nonneg_left hb hP0).trans_eq (by ring)


open scoped ComplexConjugate

private def bourgainFourSum {ι : Type*} (S : Finset ι) (z : ι → ℂ)
    (u : ι → Fin 4 → ℝ) (p : Fin 4 → ℝ) : ℂ :=
  ∑ i ∈ S, z i*fordAdditiveCharacter (∑ d, u i d*p d)

private def bourgainFourSinc (a c p : Fin 4 → ℝ) : ℝ :=
  ∏ d, sargosSincKernel (a d) (p d-c d)

private def bourgainFourKernel (a c ξ p : Fin 4 → ℝ) : ℂ :=
  ∏ d, (sargosSincKernel (a d) (p d-c d):ℂ)*fordAdditiveCharacter (ξ d*p d)

private def bourgainFourPairs {ι : Type*} (S : Finset ι)
    (u : ι → Fin 4 → ℝ) (a : Fin 4 → ℝ) : Finset (ι × ι) := by
  classical
  exact (S ×ˢ S).filter (fun ij => ∀ d, |u ij.1 d-u ij.2 d| ≤ a d)

private theorem bourgainFourKernel_integrable {a : Fin 4 → ℝ}
    (ha : ∀ d, 0 < a d) (c ξ : Fin 4 → ℝ) :
    Integrable (bourgainFourKernel a c ξ) := by
  exact Integrable.fintype_prod (fun d =>
    integrable_sargosSincKernel_shift_character_positive (ha d) (c d) (ξ d))

private theorem bourgainFourKernel_integral {a : Fin 4 → ℝ}
    (ha : ∀ d, 0 < a d) (c ξ : Fin 4 → ℝ) :
    (∫ p : Fin 4 → ℝ, bourgainFourKernel a c ξ p) =
      ∏ d, fordAdditiveCharacter (ξ d*c d)*(sargosRealTent (a d) (ξ d):ℂ) := by
  unfold bourgainFourKernel
  rw [integral_fintype_prod_volume_eq_prod (fun d t =>
    (sargosSincKernel (a d) (t-c d):ℂ)*fordAdditiveCharacter (ξ d*t))]
  simp_rw [integral_sargosSincKernel_shift_character_positive (ha _)]

private theorem bourgainFourSum_gram {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (u : ι → Fin 4 → ℝ) (p : Fin 4 → ℝ) :
    ((‖bourgainFourSum S z u p‖^2:ℝ):ℂ) =
      ∑ ij ∈ S ×ˢ S, z ij.1*conj (z ij.2)*
        fordAdditiveCharacter (∑ d, (u ij.1 d-u ij.2 d)*p d) := by
  calc
    _ = bourgainFourSum S z u p*conj (bourgainFourSum S z u p) := by
      rw [Complex.mul_conj']
      norm_num
    _ = _ := by
      unfold bourgainFourSum
      rw [map_sum,Finset.sum_mul_sum,Finset.sum_product]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_mul,conj_fordAdditiveCharacter]
      calc
        _ = (z i*conj (z j))*
            (fordAdditiveCharacter (∑ d, u i d*p d)*
              fordAdditiveCharacter (-(∑ d, u j d*p d))) := by ring
        _ = _ := by
          rw [← fordAdditiveCharacter_add]
          congr 2
          simp only [sub_mul,Finset.sum_sub_distrib]
          ring

private theorem bourgainFour_weighted_gram {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (u : ι → Fin 4 → ℝ) (a c p : Fin 4 → ℝ) :
    ((bourgainFourSinc a c p*‖bourgainFourSum S z u p‖^2:ℝ):ℂ) =
      ∑ ij ∈ S ×ˢ S, (z ij.1*conj (z ij.2))*
        bourgainFourKernel a c (fun d => u ij.1 d-u ij.2 d) p := by
  rw [Complex.ofReal_mul,bourgainFourSum_gram,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij _
  unfold bourgainFourSinc bourgainFourKernel
  rw [Complex.ofReal_prod,Finset.prod_mul_distrib,← fordAdditiveCharacter_sum Finset.univ]
  ring

private theorem bourgainFour_weighted_integrable {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (u : ι → Fin 4 → ℝ) {a : Fin 4 → ℝ}
    (ha : ∀ d, 0 < a d) (c : Fin 4 → ℝ) :
    Integrable (fun p => bourgainFourSinc a c p*‖bourgainFourSum S z u p‖^2) := by
  have hi : Integrable (fun p => ∑ ij ∈ S ×ˢ S, (z ij.1*conj (z ij.2))*
      bourgainFourKernel a c (fun d => u ij.1 d-u ij.2 d) p) :=
    integrable_finsetSum _ (fun ij _ =>
      (bourgainFourKernel_integrable ha c _).const_mul _)
  have he := funext (bourgainFour_weighted_gram S z u a c)
  rw [← he] at hi
  exact hi.re

private theorem bourgainFour_weighted_integral {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (u : ι → Fin 4 → ℝ) {a : Fin 4 → ℝ}
    (ha : ∀ d, 0 < a d) (c : Fin 4 → ℝ) :
    ((∫ p, bourgainFourSinc a c p*‖bourgainFourSum S z u p‖^2:ℝ):ℂ) =
      ∑ ij ∈ S ×ˢ S, (z ij.1*conj (z ij.2))*
        ∏ d, fordAdditiveCharacter ((u ij.1 d-u ij.2 d)*c d)*
          (sargosRealTent (a d) (u ij.1 d-u ij.2 d):ℂ) := by
  rw [← integral_complex_ofReal]
  simp_rw [bourgainFour_weighted_gram]
  rw [integral_finsetSum _ (fun ij _ =>
    (bourgainFourKernel_integrable ha c _).const_mul _)]
  simp_rw [integral_const_mul,bourgainFourKernel_integral ha]

private theorem bourgainFour_weighted_le_pairs {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (u : ι → Fin 4 → ℝ) (hz : ∀ i ∈ S, ‖z i‖ ≤ 1)
    {a : Fin 4 → ℝ} (ha : ∀ d, 0 < a d) (c : Fin 4 → ℝ) :
    (∫ p, bourgainFourSinc a c p*‖bourgainFourSum S z u p‖^2) ≤
      ((bourgainFourPairs S u a).card:ℝ) := by
  classical
  have hnon p : 0 ≤ bourgainFourSinc a c p := Finset.prod_nonneg
    (fun d _ => sargosSincKernel_nonneg (ha d).le _)
  have hn : 0 ≤ ∫ p, bourgainFourSinc a c p*‖bourgainFourSum S z u p‖^2 :=
    integral_nonneg (fun p => mul_nonneg (hnon p) (sq_nonneg _))
  calc
    _ = ‖((∫ p, bourgainFourSinc a c p*‖bourgainFourSum S z u p‖^2:ℝ):ℂ)‖ :=
      (Complex.norm_of_nonneg hn).symm
    _ = ‖∑ ij ∈ S ×ˢ S, (z ij.1*conj (z ij.2))*
        ∏ d, fordAdditiveCharacter ((u ij.1 d-u ij.2 d)*c d)*
          (sargosRealTent (a d) (u ij.1 d-u ij.2 d):ℂ)‖ := by
      rw [bourgainFour_weighted_integral S z u ha c]
    _ ≤ ∑ ij ∈ S ×ˢ S, ‖(z ij.1*conj (z ij.2))*
        ∏ d, fordAdditiveCharacter ((u ij.1 d-u ij.2 d)*c d)*
          (sargosRealTent (a d) (u ij.1 d-u ij.2 d):ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ ij ∈ S ×ˢ S,
        if ∀ d, |u ij.1 d-u ij.2 d| ≤ a d then (1:ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro ij hij
      obtain ⟨hi,hj⟩ := Finset.mem_product.mp hij
      by_cases hnear : ∀ d, |u ij.1 d-u ij.2 d| ≤ a d
      · rw [ite_eq_left hnear,norm_mul,norm_mul,Complex.norm_conj,norm_prod]
        have hp : (∏ d, ‖fordAdditiveCharacter ((u ij.1 d-u ij.2 d)*c d)*
            (sargosRealTent (a d) (u ij.1 d-u ij.2 d):ℂ)‖) ≤ 1 := by
          apply Finset.prod_le_one₀
          · intro d _; exact norm_nonneg _
          · intro d _
            rw [norm_mul,sargos_character_norm,one_mul,Complex.norm_real,
              Real.norm_eq_abs,abs_of_nonneg (sargosRealTent_nonneg _ _)]
            exact sargosRealTent_le_one (ha d) _
        have hzprod : ‖z ij.1‖*‖z ij.2‖ ≤ 1 := by
          nlinarith [hz ij.1 hi,hz ij.2 hj,norm_nonneg (z ij.1),norm_nonneg (z ij.2)]
        nlinarith [Finset.prod_nonneg (fun d (_:d ∈ Finset.univ) =>
          norm_nonneg (fordAdditiveCharacter ((u ij.1 d-u ij.2 d)*c d)*
            (sargosRealTent (a d) (u ij.1 d-u ij.2 d):ℂ)))]
      · obtain ⟨d,hd⟩ := not_forall.mp hnear
        have he : (∏ k, fordAdditiveCharacter ((u ij.1 k-u ij.2 k)*c k)*
            (sargosRealTent (a k) (u ij.1 k-u ij.2 k):ℂ)) = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ d)
          rw [sargosRealTent_zero_of_le_abs (ha d) (le_of_lt (lt_of_not_ge hd))]
          simp
        rw [he,mul_zero,norm_zero,ite_eq_right hnear]
    _ = _ := by
      simp only [bourgainFourPairs,Finset.card_eq_sum_ones,Nat.cast_sum,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro ij _
      split_ifs <;> norm_num

private theorem bourgainFourSum_continuous {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (u : ι → Fin 4 → ℝ) :
    Continuous (bourgainFourSum S z u) := by
  unfold bourgainFourSum fordAdditiveCharacter
  fun_prop

private theorem bourgainFour_window_le_pairs {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (u : ι → Fin 4 → ℝ) (hz : ∀ i ∈ S, ‖z i‖ ≤ 1)
    {δ : Fin 4 → ℝ} (hδ : ∀ d, 0 < δ d) (c : Fin 4 → ℝ) :
    (∫ p in Icc c (fun d => c d+δ d), ‖bourgainFourSum S z u p‖^2) ≤
      (256*∏ d, δ d)*((bourgainFourPairs S u (fun d => 1/δ d)).card:ℝ) := by
  let a := fun d => 1/δ d
  let b := fun d => c d+δ d/2
  let C := 256*∏ d, δ d
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (Finset.prod_nonneg (fun d _ => (hδ d).le))
  have ha d : 0 < a d := one_div_pos.mpr (hδ d)
  have hnon p : 0 ≤ bourgainFourSinc a b p := Finset.prod_nonneg
    (fun d _ => sargosSincKernel_nonneg (ha d).le _)
  have hi := bourgainFour_weighted_integrable S z u ha b
  have hj : IntegrableOn (fun p => ‖bourgainFourSum S z u p‖^2)
      (Icc c (fun d => c d+δ d)) :=
    ((bourgainFourSum_continuous S z u).norm.pow 2).continuousOn.integrableOn_compact
      isCompact_Icc
  have hpt p (hp : p ∈ Icc c (fun d => c d+δ d)) :
      ‖bourgainFourSum S z u p‖^2 ≤
        C*(bourgainFourSinc a b p*‖bourgainFourSum S z u p‖^2) := by
    have hk d : 1 ≤ (4*δ d)*sargosSincKernel (a d) (p d-b d) := by
      have hl := sargosSincKernel_lower (ha d)
        (sargos_window_scale_control (hδ d) ⟨hp.1 d,hp.2 d⟩)
      have he : (4*δ d)*(a d/4) = 1 := by dsimp [a]; field_simp [(hδ d).ne']
      have hm := mul_le_mul_of_nonneg_left hl
        (show 0 ≤ 4*δ d from mul_nonneg (by norm_num) (hδ d).le)
      rwa [he] at hm
    have hh : 1 ≤ C*bourgainFourSinc a b p := by
      have hm := Finset.prod_le_prod₀
        (fun d (_:d ∈ (Finset.univ:Finset (Fin 4))) => (by norm_num : (0:ℝ) ≤ 1))
        (fun d _ => hk d)
      norm_num [C,bourgainFourSinc,Finset.prod_mul_distrib] at hm ⊢
      exact hm
    have hm := mul_le_mul_of_nonneg_right hh (sq_nonneg ‖bourgainFourSum S z u p‖)
    simpa only [one_mul,mul_assoc] using hm
  calc
    _ ≤ ∫ p in Icc c (fun d => c d+δ d),
        C*(bourgainFourSinc a b p*‖bourgainFourSum S z u p‖^2) :=
      setIntegral_mono_on hj (hi.const_mul C).integrableOn measurableSet_Icc hpt
    _ ≤ ∫ p, C*(bourgainFourSinc a b p*‖bourgainFourSum S z u p‖^2) :=
      setIntegral_le_integral (hi.const_mul C)
        (Eventually.of_forall (fun p => mul_nonneg hC (mul_nonneg (hnon p) (sq_nonneg _))))
    _ = C*(∫ p, bourgainFourSinc a b p*‖bourgainFourSum S z u p‖^2) :=
      integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (bourgainFour_weighted_le_pairs S z u hz ha b) hC

private def bourgainFourTent (a c p : Fin 4 → ℝ) : ℝ :=
  ∏ d, sargosRealTent (a d) (p d-c d)

private def bourgainFourCloud {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (x : ι → Fin 4 → ℝ) (a p : Fin 4 → ℝ) : ℂ :=
  ∑ i ∈ S, z i*(bourgainFourTent a (x i) p:ℂ)

private theorem bourgainFourTent_nonneg (a c p : Fin 4 → ℝ) :
    0 ≤ bourgainFourTent a c p :=
  Finset.prod_nonneg (fun _ _ => sargosRealTent_nonneg _ _)

private theorem bourgainFourTent_le_one {a : Fin 4 → ℝ}
    (ha : ∀ d, 0 < a d) (c p : Fin 4 → ℝ) :
    bourgainFourTent a c p ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => sargosRealTent_nonneg _ _)
    (fun d _ => sargosRealTent_le_one (ha d) _)

private theorem bourgainFourTent_integrable {a : Fin 4 → ℝ}
    (ha : ∀ d, 0 < a d) (c : Fin 4 → ℝ) :
    Integrable (bourgainFourTent a c) :=
  Integrable.fintype_prod (fun d => integrable_sargosRealTent_shift (ha d) (c d))

private theorem bourgainFourTent_integral {a : Fin 4 → ℝ}
    (ha : ∀ d, 0 < a d) (c : Fin 4 → ℝ) :
    (∫ p, bourgainFourTent a c p) = ∏ d, a d := by
  unfold bourgainFourTent
  rw [integral_fintype_prod_volume_eq_prod (fun d t => sargosRealTent (a d) (t-c d))]
  simp_rw [integral_sargosRealTent_shift (ha _)]

private theorem bourgainFourTent_mul_zero {a c c' : Fin 4 → ℝ}
    (ha : ∀ d, 0 < a d) (p : Fin 4 → ℝ)
    (hfar : ¬ ∀ d, |c d-c' d| ≤ 2*a d) :
    bourgainFourTent a c p*bourgainFourTent a c' p = 0 := by
  classical
  obtain ⟨d,hd⟩ := not_forall.mp hfar
  unfold bourgainFourTent
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_zero (Finset.mem_univ d)
  by_cases h₁ : a d ≤ |p d-c d|
  · rw [sargosRealTent_zero_of_le_abs (ha d) h₁,zero_mul]
  · have h₂ : a d ≤ |p d-c' d| := by
      have ht : |c d-c' d| ≤ |p d-c d|+|p d-c' d| := by
        calc
          _ = |-(p d-c d)+(p d-c' d)| := by congr 1; ring
          _ ≤ |-(p d-c d)|+|p d-c' d| := abs_add_le _ _
          _ = _ := by rw [abs_neg]
      linarith [lt_of_not_ge hd,lt_of_not_ge h₁]
    rw [sargosRealTent_zero_of_le_abs (ha d) h₂,mul_zero]

private theorem bourgainFourCloud_continuous {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (x : ι → Fin 4 → ℝ) (a : Fin 4 → ℝ) :
    Continuous (bourgainFourCloud S z x a) := by
  have hc : ∀ d, Continuous (sargosRealTent (a d)) := fun d => continuous_sargosRealTent (a d)
  unfold bourgainFourCloud bourgainFourTent
  fun_prop

private theorem bourgainFourCloud_sq_pointwise {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (x : ι → Fin 4 → ℝ) {a : Fin 4 → ℝ}
    (ha : ∀ d, 0 < a d) (hz : ∀ i ∈ S, ‖z i‖ ≤ 1) (p : Fin 4 → ℝ) :
    ‖bourgainFourCloud S z x a p‖^2 ≤
      ∑ ij ∈ bourgainFourPairs S x (fun d => 2*a d), bourgainFourTent a (x ij.1) p := by
  classical
  let w := fun i => bourgainFourTent a (x i) p
  have hw i : 0 ≤ w i := bourgainFourTent_nonneg _ _ _
  have hw1 i : w i ≤ 1 := bourgainFourTent_le_one ha _ _
  have hn : ‖bourgainFourCloud S z x a p‖ ≤ ∑ i ∈ S, w i := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hw i)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hz i hi) (hw i)
  calc
    _ ≤ (∑ i ∈ S, w i)^2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = ∑ ij ∈ S ×ˢ S, w ij.1*w ij.2 := by
      rw [pow_two,Finset.sum_mul_sum,Finset.sum_product]
    _ ≤ ∑ ij ∈ S ×ˢ S,
        if ∀ d, |x ij.1 d-x ij.2 d| ≤ 2*a d then w ij.1 else 0 := by
      apply Finset.sum_le_sum
      intro ij _
      split_ifs with h
      · simpa only [mul_one] using mul_le_mul_of_nonneg_left (hw1 ij.2) (hw ij.1)
      · exact le_of_eq (bourgainFourTent_mul_zero ha p h)
    _ = _ := by simp only [bourgainFourPairs,Finset.sum_filter,w]

private theorem bourgainFourCloud_energy {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (x : ι → Fin 4 → ℝ) {a : Fin 4 → ℝ}
    (ha : ∀ d, 0 < a d) (hz : ∀ i ∈ S, ‖z i‖ ≤ 1) :
    Integrable (fun p => ‖bourgainFourCloud S z x a p‖^2) ∧
      (∫ p, ‖bourgainFourCloud S z x a p‖^2) ≤
        (∏ d, a d)*((bourgainFourPairs S x (fun d => 2*a d)).card:ℝ) := by
  let P := bourgainFourPairs S x (fun d => 2*a d)
  let W := fun p => ∑ ij ∈ P, bourgainFourTent a (x ij.1) p
  have hW : Integrable W :=
    integrable_finsetSum _ (fun ij _ => bourgainFourTent_integrable ha _)
  have he : (∫ p, W p) = (∏ d, a d)*(P.card:ℝ) := by
    dsimp only [W]
    rw [integral_finsetSum _ (fun ij _ => bourgainFourTent_integrable ha _)]
    simp only [bourgainFourTent_integral ha,Finset.sum_const,nsmul_eq_mul]
    ring
  have hpt p := bourgainFourCloud_sq_pointwise S z x ha hz p
  have hi : Integrable (fun p => ‖bourgainFourCloud S z x a p‖^2) := by
    apply hW.mono' ((bourgainFourCloud_continuous S z x a).norm.pow 2).aestronglyMeasurable
    exact Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact hpt p)
  refine ⟨hi,?_⟩
  exact (integral_mono_ae hi hW (Eventually.of_forall hpt)).trans_eq he

private theorem bourgainFourTent_character {a : Fin 4 → ℝ}
    (ha : ∀ d, 0 < a d) (c u : Fin 4 → ℝ) :
    Integrable (fun p : Fin 4 → ℝ => (bourgainFourTent a c p:ℂ)*
      fordAdditiveCharacter (∑ d, u d*p d)) ∧
    (∫ p : Fin 4 → ℝ, (bourgainFourTent a c p:ℂ)*
      fordAdditiveCharacter (∑ d, u d*p d)) =
      fordAdditiveCharacter (∑ d, u d*c d)*(∏ d, sargosSincKernel (a d) (u d):ℝ) := by
  have he (p : Fin 4 → ℝ) :
      (bourgainFourTent a c p:ℂ)*fordAdditiveCharacter (∑ d, u d*p d) =
        ∏ d, (sargosRealTent (a d) (p d-c d):ℂ)*fordAdditiveCharacter (u d*p d) := by
    simp only [bourgainFourTent,Complex.ofReal_prod,Finset.prod_mul_distrib,
      fordAdditiveCharacter_sum Finset.univ]
  simp_rw [he]
  constructor
  · exact Integrable.fintype_prod
      (fun d => integrable_sargosRealTent_shift_character (ha d) (c d) (u d))
  · rw [integral_fintype_prod_volume_eq_prod (fun d t =>
      (sargosRealTent (a d) (t-c d):ℂ)*fordAdditiveCharacter (u d*t))]
    simp_rw [integral_sargosRealTent_shift_character (ha _)]
    rw [Finset.prod_mul_distrib,← fordAdditiveCharacter_sum Finset.univ,Complex.ofReal_prod]

private theorem bourgainFourCloud_pairing {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (z : ι → ℂ) (w : κ → ℂ)
    (x : ι → Fin 4 → ℝ) (u : κ → Fin 4 → ℝ) {a : Fin 4 → ℝ}
    (ha : ∀ d, 0 < a d) :
    (∫ p, bourgainFourCloud S z x a p*bourgainFourSum T w u p) =
      ∑ i ∈ S, ∑ j ∈ T, z i*w j*fordAdditiveCharacter (∑ d, u j d*x i d)*
        (∏ d, sargosSincKernel (a d) (u j d):ℝ) := by
  have he p : bourgainFourCloud S z x a p*bourgainFourSum T w u p =
      ∑ i ∈ S, ∑ j ∈ T, (z i*w j)*((bourgainFourTent a (x i) p:ℂ)*
        fordAdditiveCharacter (∑ d, u j d*p d)) := by
    unfold bourgainFourCloud bourgainFourSum
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => ((bourgainFourTent_character ha (x i) (u j)).1).const_mul (z i*w j)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ =>
    ((bourgainFourTent_character ha (x i) (u j)).1).const_mul (z i*w j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul,(bourgainFourTent_character ha (x i) (u j)).2]
  ring

private theorem bourgainFour_cauchy {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {F G : α → ℂ}
    (hF : AEStronglyMeasurable F μ) (hG : AEStronglyMeasurable G μ)
    (hiF : Integrable (fun p => ‖F p‖^2) μ)
    (hiG : Integrable (fun p => ‖G p‖^2) μ) :
    ‖∫ p, F p*G p ∂μ‖^2 ≤
      (∫ p, ‖F p‖^2 ∂μ)*(∫ p, ‖G p‖^2 ∂μ) := by
  have hF2 := (memLp_two_iff_integrable_sq_norm hF).mpr hiF
  have hG2 := (memLp_two_iff_integrable_sq_norm hG).mpr hiG
  have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hF2) (by simpa using hG2)
  have hn := norm_integral_le_integral_norm (μ := μ) (fun p => F p*G p)
  simp only [norm_mul] at hn
  have hs : ‖∫ p, F p*G p ∂μ‖ ≤
      Real.sqrt (∫ p, ‖F p‖^2 ∂μ)*Real.sqrt (∫ p, ‖G p‖^2 ∂μ) := by
    apply hn.trans
    simpa only [Real.rpow_two,← Real.sqrt_eq_rpow] using hh
  calc
    _ ≤ (Real.sqrt (∫ p, ‖F p‖^2 ∂μ)*Real.sqrt (∫ p, ‖G p‖^2 ∂μ))^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hs 2
    _ = _ := by
      rw [mul_pow,Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _)),
        Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))]

private theorem bourgainFourCloud_zero_outside {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (x : ι → Fin 4 → ℝ) {a c δ : Fin 4 → ℝ}
    (ha : ∀ d, 0 < a d) (hx : ∀ i ∈ S, ∀ d, x i d ∈ Icc (c d) (c d+δ d))
    (p : Fin 4 → ℝ)
    (hp : p ∉ Icc (fun d => c d-a d) (fun d => c d+δ d+a d)) :
    bourgainFourCloud S z x a p = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i hi
  suffices he : bourgainFourTent a (x i) p = 0 by rw [he]; simp
  by_cases hfar : ∃ d, a d ≤ |p d-x i d|
  · obtain ⟨d,hd⟩ := hfar
    unfold bourgainFourTent
    exact Finset.prod_eq_zero (Finset.mem_univ d) (sargosRealTent_zero_of_le_abs (ha d) hd)
  · exfalso
    apply hp
    have hnear d : |p d-x i d| < a d := lt_of_not_ge (fun hd => hfar ⟨d,hd⟩)
    constructor <;> intro d
    · have ht := (abs_lt.mp (hnear d)).1
      have hl := (hx i hi d).1
      linarith
    · have ht := (abs_lt.mp (hnear d)).2
      have hl := (hx i hi d).2
      linarith

private theorem bourgainFour_tent_bilinear {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (z : ι → ℂ) (w : κ → ℂ)
    (x : ι → Fin 4 → ℝ) (u : κ → Fin 4 → ℝ) {a c δ : Fin 4 → ℝ}
    (ha : ∀ d, 0 < a d) (hδ : ∀ d, 0 < δ d)
    (hz : ∀ i ∈ S, ‖z i‖ ≤ 1) (hw : ∀ j ∈ T, ‖w j‖ ≤ 1)
    (hx : ∀ i ∈ S, ∀ d, x i d ∈ Icc (c d) (c d+δ d)) :
    ‖∑ i ∈ S, ∑ j ∈ T, z i*w j*fordAdditiveCharacter (∑ d, u j d*x i d)*
        (∏ d, sargosSincKernel (a d) (u j d):ℝ)‖^2 ≤
      256*(∏ d, a d)*(∏ d, (δ d+2*a d))*
        ((bourgainFourPairs S x (fun d => 2*a d)).card:ℝ)*
        ((bourgainFourPairs T u (fun d => 1/(δ d+2*a d))).card:ℝ) := by
  let F := bourgainFourCloud S z x a
  let G := bourgainFourSum T w u
  let D := fun d => δ d+2*a d
  let b := fun d => c d-a d
  let U := Icc b (fun d => b d+D d)
  let ν := volume.restrict U
  have hD d : 0 < D d := by dsimp [D]; linarith [hδ d,ha d]
  have he : (∫ p, F p*G p) = ∫ p, F p*G p ∂ν := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    have heU : U = Icc (fun d => c d-a d) (fun d => c d+δ d+a d) := by
      dsimp only [U,b,D]
      congr 1
      funext d
      ring
    rw [heU] at hp
    change F p*G p = 0
    rw [show F p=0 from bourgainFourCloud_zero_outside S z x ha hx p hp,zero_mul]
  obtain ⟨hiF,hFB⟩ := bourgainFourCloud_energy S z x ha hz
  have hiG : Integrable (fun p => ‖G p‖^2) ν :=
    ((bourgainFourSum_continuous T w u).norm.pow 2).continuousOn.integrableOn_compact
      isCompact_Icc
  have hcs := bourgainFour_cauchy
    (bourgainFourCloud_continuous S z x a).aestronglyMeasurable
    (bourgainFourSum_continuous T w u).aestronglyMeasurable hiF.integrableOn hiG
  have hFbound : (∫ p, ‖F p‖^2 ∂ν) ≤
      (∏ d, a d)*((bourgainFourPairs S x (fun d => 2*a d)).card:ℝ) :=
    (setIntegral_le_integral hiF
      (Eventually.of_forall (fun _ => sq_nonneg _))).trans hFB
  have hGbound : (∫ p, ‖G p‖^2 ∂ν) ≤
      (256*∏ d, D d)*((bourgainFourPairs T u (fun d => 1/D d)).card:ℝ) :=
    bourgainFour_window_le_pairs T w u hw hD b
  rw [← bourgainFourCloud_pairing S T z w x u ha,he]
  apply hcs.trans
  have hp : 0 ≤ (∏ d, a d)*((bourgainFourPairs S x (fun d => 2*a d)).card:ℝ) :=
    mul_nonneg (Finset.prod_nonneg (fun d _ => (ha d).le)) (Nat.cast_nonneg _)
  have hbnd := mul_le_mul hFbound hGbound
    (integral_nonneg (fun _ => sq_nonneg _)) hp
  convert hbnd using 1
  dsimp [D]
  ring

                                                                         
                                                                            
theorem bourgain_four_dimensional_double_large_sieve {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (z : ι → ℂ) (w : κ → ℂ)
    (x : ι → Fin 4 → ℝ) (u : κ → Fin 4 → ℝ) {a c δ : Fin 4 → ℝ}
    (ha : ∀ d, 0 < a d) (hδ : ∀ d, 0 < δ d)
    (hz : ∀ i ∈ S, ‖z i‖ ≤ 1) (hw : ∀ j ∈ T, ‖w j‖ ≤ 1)
    (hx : ∀ i ∈ S, ∀ d, x i d ∈ Icc (c d) (c d+δ d))
    (hu : ∀ j ∈ T, ∀ d, a d*|u j d| ≤ 1/2) :
    ‖∑ i ∈ S, ∑ j ∈ T, z i*w j*fordAdditiveCharacter (∑ d, u j d*x i d)‖^2 ≤
      (16777216*(∏ d, (δ d+2*a d))/(∏ d, a d))*
        (((S ×ˢ S).filter (fun ij => ∀ d, |x ij.1 d-x ij.2 d| ≤ 2*a d)).card:ℝ)*
        (((T ×ˢ T).filter (fun ij => ∀ d, |u ij.1 d-u ij.2 d| ≤ 1/(δ d+2*a d))).card:ℝ) := by
  classical
  let t := (∏ d, a d)/256
  let K := fun j => ∏ d, sargosSincKernel (a d) (u j d)
  let w' := fun j => (t:ℂ)*w j/(K j:ℂ)
  have hA : 0 < ∏ d, a d := Finset.prod_pos (fun d _ => ha d)
  have ht : 0 < t := div_pos hA (by norm_num)
  have hK j (hj : j ∈ T) : t ≤ K j := by
    have hh := Finset.prod_le_prod₀
      (fun d (_:d ∈ (Finset.univ:Finset (Fin 4))) =>
        (div_nonneg (ha d).le (by norm_num) : 0 ≤ a d/4))
      (fun d _ => sargosSincKernel_lower (ha d) (hu j hj d))
    norm_num [Finset.prod_div_distrib,t,K] at hh ⊢
    exact hh
  have hw' : ∀ j ∈ T, ‖w' j‖ ≤ 1 := by
    intro j hj
    have hk : 0 < K j := ht.trans_le (hK j hj)
    dsimp only [w']
    rw [norm_div,norm_mul,Complex.norm_real,Complex.norm_real,
      Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos ht,abs_of_pos hk]
    apply (div_le_one hk).mpr
    exact (mul_le_mul_of_nonneg_left (hw j hj) ht.le).trans
      (by simpa only [mul_one] using hK j hj)
  have hbound := bourgainFour_tent_bilinear S T z w' x u ha hδ hz hw' hx
  have he :
      (∑ i ∈ S, ∑ j ∈ T, z i*w' j*fordAdditiveCharacter (∑ d, u j d*x i d)*
        (∏ d, sargosSincKernel (a d) (u j d):ℝ)) =
      (t:ℂ)*(∑ i ∈ S, ∑ j ∈ T, z i*w j*fordAdditiveCharacter (∑ d, u j d*x i d)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j hj
    have hk : (K j:ℂ) ≠ 0 := by exact_mod_cast (ht.trans_le (hK j hj)).ne'
    change z i*((t:ℂ)*w j/(K j:ℂ))*fordAdditiveCharacter (∑ d, u j d*x i d)*(K j:ℂ) =
      (t:ℂ)*(z i*w j*fordAdditiveCharacter (∑ d, u j d*x i d))
    field_simp
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht,mul_pow] at hbound
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos ht)).mp
  apply hbound.trans_eq
  change 256*(∏ d, a d)*(∏ d, (δ d+2*a d))*
      ((bourgainFourPairs S x (fun d => 2*a d)).card:ℝ)*
      ((bourgainFourPairs T u (fun d => 1/(δ d+2*a d))).card:ℝ) =
    t^2*((16777216*(∏ d, (δ d+2*a d))/(∏ d, a d))*
      ((bourgainFourPairs S x (fun d => 2*a d)).card:ℝ)*
      ((bourgainFourPairs T u (fun d => 1/(δ d+2*a d))).card:ℝ))
  dsimp only [t]
  field_simp
  ring

                                                                     
                                                        
theorem bourgain_four_dimensional_double_large_sieve_sum_norm {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (w : κ → ℂ)
    (x : ι → Fin 4 → ℝ) (u : κ → Fin 4 → ℝ) {a c δ : Fin 4 → ℝ}
    (ha : ∀ d, 0 < a d) (hδ : ∀ d, 0 < δ d)
    (hw : ∀ j ∈ T, ‖w j‖ ≤ 1)
    (hx : ∀ i ∈ S, ∀ d, x i d ∈ Icc (c d) (c d+δ d))
    (hu : ∀ j ∈ T, ∀ d, a d*|u j d| ≤ 1/2) :
    (∑ i ∈ S, ‖∑ j ∈ T, w j*fordAdditiveCharacter (∑ d, u j d*x i d)‖)^2 ≤
      (16777216*(∏ d, (δ d+2*a d))/(∏ d, a d))*
        (((S ×ˢ S).filter (fun ij => ∀ d, |x ij.1 d-x ij.2 d| ≤ 2*a d)).card:ℝ)*
        (((T ×ˢ T).filter (fun ij => ∀ d, |u ij.1 d-u ij.2 d| ≤ 1/(δ d+2*a d))).card:ℝ) := by
  let A := fun i => ∑ j ∈ T, w j*fordAdditiveCharacter (∑ d, u j d*x i d)
  let z := fun i => MathCollab.Density.Stronger.Atkinson.phaseAlign (A i)
  have hz : ∀ i ∈ S, ‖z i‖ ≤ 1 := fun i _ =>
    MathCollab.Density.Stronger.Atkinson.norm_phaseAlign_le_one (A i)
  have h := bourgain_four_dimensional_double_large_sieve S T z w x u ha hδ hz hw hx hu
  have he : (∑ i ∈ S, ∑ j ∈ T, z i*w j*fordAdditiveCharacter (∑ d, u j d*x i d)) =
      ((∑ i ∈ S, ‖A i‖:ℝ):ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = z i*A i := by
        dsimp only [A]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := MathCollab.Density.Stronger.Atkinson.phaseAlign_mul (A i)
  rw [he,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))] at h
  exact h

                                                                         
                                                                                
theorem bourgain_four_dimensional_sixth_power_sieve {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (w : κ → ℂ)
    (x : ι → Fin 4 → ℝ) (u : κ → Fin 4 → ℝ) {a c δ : Fin 4 → ℝ}
    (ha : ∀ d, 0 < a d) (hδ : ∀ d, 0 < δ d)
    (hw : ∀ j ∈ T, ‖w j‖ ≤ 1)
    (hx : ∀ i ∈ S, ∀ d, x i d ∈ Icc (c d) (c d+δ d))
    (hu : ∀ j ∈ T, ∀ d, a d*|u j d| ≤ 1/12) :
    let V := Fintype.piFinset (fun _ : Fin 6 => T)
    let v := fun (j : Fin 6 → κ) d => ∑ k, u (j k) d
    (∑ i ∈ S, ‖∑ j ∈ T, w j*fordAdditiveCharacter (∑ d, u j d*x i d)‖)^12 ≤
      (S.card:ℝ)^10*(16777216*(∏ d, (δ d+2*a d))/(∏ d, a d))*
        (((S ×ˢ S).filter (fun ij => ∀ d, |x ij.1 d-x ij.2 d| ≤ 2*a d)).card:ℝ)*
        (((V ×ˢ V).filter (fun ij => ∀ d, |v ij.1 d-v ij.2 d| ≤ 1/(δ d+2*a d))).card:ℝ) := by
  classical
  dsimp only
  let V := Fintype.piFinset (fun _ : Fin 6 => T)
  let v := fun (j : Fin 6 → κ) d => ∑ k, u (j k) d
  let W := fun j : Fin 6 → κ => ∏ k, w (j k)
  let A := fun i => ∑ j ∈ T, w j*fordAdditiveCharacter (∑ d, u j d*x i d)
  have hW : ∀ j ∈ V, ‖W j‖ ≤ 1 := by
    intro j hj
    rw [show W j = ∏ k, w (j k) from rfl,norm_prod]
    apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
    intro k _
    exact hw (j k) ((Fintype.mem_piFinset.mp hj) k)
  have hv : ∀ j ∈ V, ∀ d, a d*|v j d| ≤ 1/2 := by
    intro j hj d
    have hh := Finset.abs_sum_le_sum_abs (s := (Finset.univ:Finset (Fin 6))) (f := fun k => u (j k) d)
    have hm := mul_le_mul_of_nonneg_left hh (ha d).le
    have hn : (∑ k : Fin 6, a d*|u (j k) d|) ≤ ∑ _k : Fin 6, (1/12:ℝ) :=
      Finset.sum_le_sum (fun k _ => hu (j k) ((Fintype.mem_piFinset.mp hj) k) d)
    rw [Finset.mul_sum] at hm
    exact hm.trans (by norm_num at hn ⊢; exact hn)
  have he i : A i^6 =
      ∑ j ∈ V, W j*fordAdditiveCharacter (∑ d, v j d*x i d) := by
    dsimp only [A]
    rw [Finset.sum_pow']
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.prod_mul_distrib,← fordAdditiveCharacter_sum Finset.univ]
    change (∏ k, w (j k))*fordAdditiveCharacter (∑ k, ∑ d, u (j k) d*x i d) =
      (∏ k, w (j k))*fordAdditiveCharacter (∑ d, (∑ k, u (j k) d)*x i d)
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_mul]
  have hs := bourgain_four_dimensional_double_large_sieve_sum_norm S V W x v ha hδ hW hx hv
  have heNorm i : ‖∑ j ∈ V, W j*fordAdditiveCharacter (∑ d, v j d*x i d)‖ = ‖A i‖^6 := by
    rw [← he,norm_pow]
  simp_rw [heNorm] at hs
  have hj := pow_sum_le_card_mul_sum_pow (s := S)
    (f := fun i => ‖A i‖) (fun _ _ => norm_nonneg _) 5
  have hsq := pow_le_pow_left₀
    (pow_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) 6) hj 2
  have hm := mul_le_mul_of_nonneg_left hs (pow_nonneg (Nat.cast_nonneg S.card) 10)
  calc
    _ = ((∑ i ∈ S, ‖A i‖)^6)^2 := by ring
    _ ≤ ((S.card:ℝ)^5*(∑ i ∈ S, ‖A i‖^6))^2 := hsq
    _ = (S.card:ℝ)^10*(∑ i ∈ S, ‖A i‖^6)^2 := by ring
    _ ≤ _ := hm.trans_eq (by ring)


private theorem bourgainFour_tent_moment_gram {ι : Type*}
    (S : Finset ι) (u : ι → Fin 4 → ℝ) {a : Fin 4 → ℝ}
    (ha : ∀ d, 0 < a d) :
    Integrable (fun p => bourgainFourTent a (fun _ => 0) p*
      ‖bourgainFourSum S (fun _ => 1) u p‖^2) ∧
    (∫ p, bourgainFourTent a (fun _ => 0) p*‖bourgainFourSum S (fun _ => 1) u p‖^2) =
      ∑ ij ∈ S ×ˢ S, ∏ d, sargosSincKernel (a d) (u ij.1 d-u ij.2 d) := by
  have he p : ((bourgainFourTent a (fun _ => 0) p*
      ‖bourgainFourSum S (fun _ => 1) u p‖^2:ℝ):ℂ) =
      ∑ ij ∈ S ×ˢ S, (bourgainFourTent a (fun _ => 0) p:ℂ)*
        fordAdditiveCharacter (∑ d, (u ij.1 d-u ij.2 d)*p d) := by
    rw [Complex.ofReal_mul,bourgainFourSum_gram,Finset.mul_sum]
    simp only [map_one,one_mul]
  have hc := integrable_finsetSum (S ×ˢ S) (fun ij _ =>
    (bourgainFourTent_character ha (fun _ => 0) (fun d => u ij.1 d-u ij.2 d)).1)
  have hr : Integrable (fun p => bourgainFourTent a (fun _ => 0) p*
      ‖bourgainFourSum S (fun _ => 1) u p‖^2) := by
    have hh := hc.congr (Eventually.of_forall (fun p => (he p).symm))
    exact hh.re
  refine ⟨hr,?_⟩
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [he]
  rw [integral_finsetSum _ (fun ij _ =>
    (bourgainFourTent_character ha (fun _ => 0) (fun d => u ij.1 d-u ij.2 d)).1)]
  simp_rw [(bourgainFourTent_character ha (fun _ => 0) _).2]
  simp only [mul_zero,Finset.sum_const_zero,fordAdditiveCharacter,
    Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_mul,Complex.ofReal_sum]

private theorem bourgainFour_pairs_le_box_moment {ι : Type*}
    (S : Finset ι) (u : ι → Fin 4 → ℝ) {a : Fin 4 → ℝ}
    (ha : ∀ d, 0 < a d) :
    ((bourgainFourPairs S u (fun d => 1/(2*a d))).card:ℝ) ≤
      (256/(∏ d, a d))*
        ∫ p in Icc (fun d => -a d) a, ‖bourgainFourSum S (fun _ => 1) u p‖^2 := by
  classical
  let t := (∏ d, a d)/256
  let W := fun p => bourgainFourTent a (fun _ => 0) p
  let F := fun p => ‖bourgainFourSum S (fun _ => 1) u p‖^2
  let K := fun ij : ι × ι => ∏ d, sargosSincKernel (a d) (u ij.1 d-u ij.2 d)
  have hA : 0 < ∏ d, a d := Finset.prod_pos (fun d _ => ha d)
  have ht : 0 < t := div_pos hA (by norm_num)
  have hK ij : 0 ≤ K ij :=
    Finset.prod_nonneg (fun d _ => sargosSincKernel_nonneg (ha d).le _)
  have hnear ij (h : ∀ d, |u ij.1 d-u ij.2 d| ≤ 1/(2*a d)) : t ≤ K ij := by
    have hh d : a d*|u ij.1 d-u ij.2 d| ≤ 1/2 := by
      calc
        _ ≤ a d*(1/(2*a d)) := mul_le_mul_of_nonneg_left (h d) (ha d).le
        _ = _ := by field_simp [(ha d).ne']
    have hb := Finset.prod_le_prod₀
      (fun d (_:d ∈ (Finset.univ:Finset (Fin 4))) =>
        (div_nonneg (ha d).le (by norm_num) : 0 ≤ a d/4))
      (fun d _ => sargosSincKernel_lower (ha d) (hh d))
    norm_num [Finset.prod_div_distrib,t,K] at hb ⊢
    exact hb
  have hc : t*((bourgainFourPairs S u (fun d => 1/(2*a d))).card:ℝ) ≤
      ∑ ij ∈ S ×ˢ S, K ij := by
    calc
      _ = ∑ ij ∈ S ×ˢ S,
          if ∀ d, |u ij.1 d-u ij.2 d| ≤ 1/(2*a d) then t else 0 := by
        simp only [bourgainFourPairs,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
        ring
      _ ≤ _ := Finset.sum_le_sum (fun ij _ => by
        split_ifs with h
        · exact hnear ij h
        · exact hK ij)
  obtain ⟨hi,he⟩ := bourgainFour_tent_moment_gram S u ha
  have hzero p (hp : p ∉ Icc (fun d => -a d) a) : W p = 0 := by
    have hfar : ∃ d, a d ≤ |p d| := by
      by_contra hn
      apply hp
      push Not at hn
      exact ⟨fun d => (abs_lt.mp (hn d)).1.le,fun d => (abs_lt.mp (hn d)).2.le⟩
    obtain ⟨d,hd⟩ := hfar
    dsimp only [W,bourgainFourTent]
    apply Finset.prod_eq_zero (Finset.mem_univ d)
    rw [sub_zero,sargosRealTent_zero_of_le_abs (ha d) hd]
  have hbox : (∫ p, W p*F p) ≤
      ∫ p in Icc (fun d => -a d) a, F p := by
    have heq : (∫ p, W p*F p) = ∫ p in Icc (fun d => -a d) a, W p*F p := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      rw [hzero p hp,zero_mul]
    rw [heq]
    apply setIntegral_mono_on hi.integrableOn
      (((bourgainFourSum_continuous S (fun _ => 1) u).norm.pow 2).continuousOn.integrableOn_compact
        isCompact_Icc) measurableSet_Icc
    intro p _
    exact mul_le_of_le_one_left (sq_nonneg _) (bourgainFourTent_le_one ha _ _)
  have hb : t*((bourgainFourPairs S u (fun d => 1/(2*a d))).card:ℝ) ≤
      ∫ p in Icc (fun d => -a d) a, F p := hc.trans (he.symm.le.trans hbox)
  have hd : ((bourgainFourPairs S u (fun d => 1/(2*a d))).card:ℝ) ≤
      (∫ p in Icc (fun d => -a d) a, F p)/t :=
    (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using hb)
  convert hd using 1
  dsimp only [t,F]
  field_simp

private theorem bourgainFour_half_box_shift {ι : Type*} (S : Finset ι)
    (u : ι → Fin 4 → ℝ) :
    (∫ p : Fin 4 → ℝ in Icc (-![1/2,1/2,1,1]) ![1/2,1/2,1,1],
      ‖bourgainFourSum S (fun _ => 1) u p‖^12) =
    ∫ p : Fin 4 → ℝ in Icc ![0,0,-1,-1] (fun _ => 1),
      ‖bourgainFourSum S
        (fun i => fordAdditiveCharacter (-(∑ d, u i d*(![1/2,1/2,0,0] : Fin 4 → ℝ) d)))
        u p‖^12 := by
  let q : Fin 4 → ℝ := ![1/2,1/2,0,0]
  let z := fun i => fordAdditiveCharacter (-(∑ d, u i d*q d))
  let B := Icc ![0,0,-1,-1] (fun _ : Fin 4 => (1:ℝ))
  let F := fun p => ‖bourgainFourSum S z u p‖^12
  have hpre : (fun p : Fin 4 → ℝ => p+q) ⁻¹' B =
      Icc (-![1/2,1/2,1,1]) ![1/2,1/2,1,1] := by
    ext p
    change (∀ d, (![0,0,-1,-1] : Fin 4 → ℝ) d ≤ p d+q d) ∧
        (∀ d, p d+q d ≤ 1) ↔
      (∀ d, (-![1/2,1/2,1,1] : Fin 4 → ℝ) d ≤ p d) ∧
        (∀ d, p d ≤ (![1/2,1/2,1,1] : Fin 4 → ℝ) d)
    constructor
    · rintro ⟨hl,hu⟩
      constructor
      · intro d
        have hd := hl d
        fin_cases d <;> norm_num [q] at hd ⊢ <;> linarith
      · intro d
        have hd := hu d
        fin_cases d <;> norm_num [q] at hd ⊢ <;> linarith
    · rintro ⟨hl,hu⟩
      constructor
      · intro d
        have hd := hl d
        fin_cases d <;> norm_num [q] at hd ⊢ <;> linarith
      · intro d
        have hd := hu d
        fin_cases d <;> norm_num [q] at hd ⊢ <;> linarith
  have he p : F (p+q) = ‖bourgainFourSum S (fun _ => 1) u p‖^12 := by
    dsimp only [F]
    congr 2
    unfold bourgainFourSum
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [z]
    rw [← fordAdditiveCharacter_add,one_mul]
    congr 1
    simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
    ring
  have ht := (measurePreserving_add_right (volume : Measure (Fin 4 → ℝ)) q).setIntegral_preimage_emb
    (Homeomorph.addRight q).measurableEmbedding F B
  rw [hpre] at ht
  simp_rw [he] at ht
  exact ht

private theorem bourgainFour_six_tuple_count_to_moment {ι : Type*}
    (S : Finset ι) (u : ι → Fin 4 → ℝ) :
    let V := Fintype.piFinset (fun _ : Fin 6 => S)
    let v := fun (j : Fin 6 → ι) d => ∑ k, u (j k) d
    ((bourgainFourPairs V v ![1,1,1/2,1/2]).card:ℝ) ≤
      1024*∫ p : Fin 4 → ℝ in Icc ![0,0,-1,-1] (fun _ => 1),
        ‖bourgainFourSum S
          (fun i => fordAdditiveCharacter (-(∑ d, u i d*(![1/2,1/2,0,0] : Fin 4 → ℝ) d)))
          u p‖^12 := by
  classical
  dsimp only
  let V := Fintype.piFinset (fun _ : Fin 6 => S)
  let v := fun (j : Fin 6 → ι) d => ∑ k, u (j k) d
  let a : Fin 4 → ℝ := ![1/2,1/2,1,1]
  have ha d : 0 < a d := by fin_cases d <;> norm_num [a]
  have hnear : (fun d => 1/(2*a d)) = ![1,1,1/2,1/2] := by
    funext d
    fin_cases d <;> norm_num [a]
  have he p : bourgainFourSum S (fun _ => 1) u p^6 =
      bourgainFourSum V (fun _ => 1) v p := by
    unfold bourgainFourSum
    rw [Finset.sum_pow']
    apply Finset.sum_congr rfl
    intro j _
    simp only [one_mul]
    rw [← fordAdditiveCharacter_sum Finset.univ]
    congr 1
    change (∑ k, ∑ d, u (j k) d*p d) = ∑ d, (∑ k, u (j k) d)*p d
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_mul]
  have hnorm p : ‖bourgainFourSum V (fun _ => 1) v p‖^2 =
      ‖bourgainFourSum S (fun _ => 1) u p‖^12 := by
    rw [← he,norm_pow,← pow_mul]
  have hb := bourgainFour_pairs_le_box_moment V v ha
  rw [hnear] at hb
  simp_rw [hnorm] at hb
  have hc : (256/(∏ d, a d):ℝ)=1024 := by norm_num [a,Fin.prod_univ_succ]
  rw [hc] at hb
  change ((bourgainFourPairs V v ![1,1,1/2,1/2]).card:ℝ) ≤ _ at hb ⊢
  rw [show (fun d => -a d) = -![1/2,1/2,1,1] from rfl] at hb
  change ((bourgainFourPairs V v ![1,1,1/2,1/2]).card:ℝ) ≤
    1024*(∫ p : Fin 4 → ℝ in Icc (-![1/2,1/2,1,1]) ![1/2,1/2,1,1],
      ‖bourgainFourSum S (fun _ => 1) u p‖^12) at hb
  rw [bourgainFour_half_box_shift S u] at hb
  exact hb

universe v

                                                                 
                                                                        
                                                                     
theorem exists_bourgainSourceCurve_six_tuple_first_spacing {ε : ℝ} (hε : 0<ε) :
    ∃ C>(0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (δ Δ : ℝ),
      δ∈Icc (1/(N:ℝ)^2) 1 → Δ∈Icc (1/(N:ℝ)) 1 →
      ∀ (ι : Type v) (S : Finset ι) (m : ι → ℤ) (B : ℝ),
        0 ≤ B → (∀ i∈S,1 ≤ m i ∧ m i ≤ N) →
        (∀ q : ℤ,((S.filter (fun i => m i=q)).card:ℝ) ≤ B) →
        let U := fun i => ![(m i:ℝ),(m i:ℝ)^2,
          (1/δ)*((m i:ℝ)/N)^((3:ℝ)/2),(1/Δ)*Real.sqrt ((m i:ℝ)/N)]
        let V := Fintype.piFinset (fun _ : Fin 6 => S)
        let y := fun (j : Fin 6 → ι) d => ∑ k, U (j k) d
        (((V ×ˢ V).filter (fun ij => ∀ d,
          |y ij.1 d-y ij.2 d| ≤ (![1,1,1/2,1/2] : Fin 4 → ℝ) d)).card:ℝ) ≤
          C*δ*Δ*(N:ℝ)^((9:ℝ)+ε)*B^12 := by
  classical
  obtain ⟨C,hC,h⟩ := exists_bourgainSourceCurve_anisotropic_first_spacing.{v} hε
  refine ⟨1024*C,by positivity,?_⟩
  intro N hN δ Δ hδ hΔ ι S m B hB hm hmass
  dsimp only
  let U := fun i => ![(m i:ℝ),(m i:ℝ)^2,
    (1/δ)*((m i:ℝ)/N)^((3:ℝ)/2),(1/Δ)*Real.sqrt ((m i:ℝ)/N)]
  let V := Fintype.piFinset (fun _ : Fin 6 => S)
  let y := fun (j : Fin 6 → ι) d => ∑ k, U (j k) d
  let z := fun i => fordAdditiveCharacter (-(∑ d, U i d*(![1/2,1/2,0,0] : Fin 4 → ℝ) d))
  have hz q : (∑ i ∈ S.filter (fun i => m i=q), ‖z i‖) ≤ B := by
    simpa only [z,sargos_character_norm,Finset.sum_const,nsmul_eq_mul,mul_one] using hmass q
  have hs := h N hN δ Δ hδ hΔ ι S z m B hB hm hz
  have hphase p : bourgainFourSum S z U p =
      ∑ i∈S,z i*fordAdditiveCharacter
        (p 0*(m i:ℝ)+p 1*(m i:ℝ)^2+
          (1/δ)*((m i:ℝ)/N)^((3:ℝ)/2)*p 2+
          (1/Δ)*Real.sqrt ((m i:ℝ)/N)*p 3) := by
    unfold bourgainFourSum
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    simp [U,Fin.sum_univ_succ]
    ring
  have hc := bourgainFour_six_tuple_count_to_moment S U
  change ((bourgainFourPairs V y ![1,1,1/2,1/2]).card:ℝ) ≤
    1024*(∫ p : Fin 4 → ℝ in Icc ![0,0,-1,-1] (fun _ => 1),
      ‖bourgainFourSum S z U p‖^12) at hc
  simp_rw [hphase] at hc
  change ((bourgainFourPairs V y ![1,1,1/2,1/2]).card:ℝ) ≤ _
  exact hc.trans ((mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 1024)).trans_eq (by ring))



public  theorem bourgain_source_sieve_frequency_scale {N t η ζ : ℝ}
    (hN : 1≤N) (ht : t∈Icc 1 N) (hη : 0<η) (hζ : 0<ζ) :
    let a : Fin 4 → ℝ := ![1/(12*N),1/(12*N^2),η/12,ζ/12]
    let U : Fin 4 → ℝ := ![t,t^2,(1/η)*(t/N)^((3:ℝ)/2),(1/ζ)*Real.sqrt (t/N)]
    ∀ d, a d*|U d| ≤ 1/12 := by
  have hNp : 0<N := by linarith
  have ht0 : 0≤t := by linarith [ht.1]
  have hv0 : 0≤t/N := div_nonneg ht0 hNp.le
  have hv1 : t/N≤1 := (div_le_one hNp).mpr ht.2
  have hp : (t/N)^((3:ℝ)/2) ≤ 1 := Real.rpow_le_one hv0 hv1 (by norm_num)
  have hroot : Real.sqrt (t/N) ≤ 1 := Real.sqrt_le_one.mpr hv1
  dsimp only
  intro d
  fin_cases d
  · change (1/(12*N))*|t|≤1/12
    rw [abs_of_nonneg ht0]
    have hh := mul_le_mul_of_nonneg_left ht.2 (by positivity : 0≤1/(12*N))
    exact hh.trans_eq (by field_simp)
  · change (1/(12*N^2))*|t^2|≤1/12
    rw [abs_of_nonneg (sq_nonneg _)]
    have hsq : t^2≤N^2 := pow_le_pow_left₀ ht0 ht.2 2
    have hh := mul_le_mul_of_nonneg_left hsq (by positivity : 0≤1/(12*N^2))
    exact hh.trans_eq (by field_simp)
  · change (η/12)*|(1/η)*(t/N)^((3:ℝ)/2)|≤1/12
    rw [abs_of_nonneg (by positivity)]
    calc
      _ = (1/12)*(t/N)^((3:ℝ)/2) := by field_simp
      _ ≤ _ := by nlinarith
  · change (ζ/12)*|(1/ζ)*Real.sqrt (t/N)|≤1/12
    rw [abs_of_nonneg (by positivity)]
    calc
      _ = (1/12)*Real.sqrt (t/N) := by field_simp
      _ ≤ _ := by nlinarith

private theorem bourgain_source_sieve_box_scale {N η ζ : ℝ}
    (hN : 1≤N) (hη : η∈Ioc 0 1) (hζ : ζ∈Ioc 0 1) :
    let a : Fin 4 → ℝ := ![1/(12*N),1/(12*N^2),η/12,ζ/12]
    let δ : Fin 4 → ℝ := ![1,1,2,2]
    (∀ d, 0<a d) ∧
    (∀ d, 1/(δ d+2*a d) ≤ (![1,1,1/2,1/2] : Fin 4 → ℝ) d) ∧
    16777216*(∏ d, (δ d+2*a d))/(∏ d, a d) ≤
      (16777216*36*12^4)*N^3/(η*ζ) := by
  dsimp only
  let a : Fin 4 → ℝ := ![1/(12*N),1/(12*N^2),η/12,ζ/12]
  let δ : Fin 4 → ℝ := ![1,1,2,2]
  have hNp : 0<N := by linarith
  have hηp := hη.1
  have hζp := hζ.1
  have ha d : 0<a d := by
    fin_cases d <;> norm_num [a,Matrix.cons_val_succ] <;> positivity
  refine ⟨ha,?_,?_⟩
  · intro d
    have hb : 0 < δ d := by fin_cases d <;> norm_num [δ,Matrix.cons_val_succ]
    have hh : 1/(δ d+2*a d) ≤ 1/(δ d) :=
      one_div_le_one_div_of_le hb (by linarith [ha d])
    convert hh using 1
    fin_cases d <;> norm_num [δ,Matrix.cons_val_succ]
  · have ha1 d : a d≤1/12 := by
      fin_cases d
      · change 1/(12*N)≤1/12
        exact one_div_le_one_div_of_le (by norm_num) (by linarith)
      · change 1/(12*N^2)≤1/12
        exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
      · change η/12≤1/12
        exact div_le_div_of_nonneg_right hη.2 (by norm_num)
      · change ζ/12≤1/12
        exact div_le_div_of_nonneg_right hζ.2 (by norm_num)
    have hD : (∏ d, (δ d+2*a d)) ≤ 36 := by
      have hb := Finset.prod_le_prod₀
        (fun d (_:d∈(Finset.univ:Finset (Fin 4))) => (by
          have hd : 0≤δ d := by fin_cases d <;> norm_num [δ,Matrix.cons_val_succ]
          linarith [ha d] : 0≤δ d+2*a d))
        (g := (![2,2,3,3] : Fin 4 → ℝ))
        (fun d _ => by
          have hh := ha1 d
          calc
            δ d+2*a d ≤ δ d+1 := by linarith
            _ ≤ _ := by fin_cases d <;> norm_num [δ,Matrix.cons_val_succ])
      norm_num [Fin.prod_univ_succ] at hb ⊢
      exact hb
    have hprod : (∏ d, a d) = η*ζ/(12^4*N^3) := by
      norm_num [a,Fin.prod_univ_succ]
      field_simp
      ring
    have hp : 0<∏ d, a d := Finset.prod_pos (fun d _ => ha d)
    calc
      _ ≤ 16777216*36/(∏ d, a d) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hD (by norm_num)) hp.le
      _ = _ := by rw [hprod]; field_simp


set_option maxHeartbeats 400000 in
                                                                  
                                                                    
                                                                
theorem exists_bourgainSourceCurve_double_sieve {ε : ℝ} (hε : 0<ε) :
    ∃ C>(0:ℝ), ∀ (N : ℕ), 1≤N → ∀ (η ζ : ℝ),
      η∈Icc (1/(N:ℝ)^2) 1 → ζ∈Icc (1/(N:ℝ)) 1 →
      ∀ (ι κ : Type v) (S : Finset ι) (T : Finset κ) (w : κ → ℂ)
        (m : κ → ℤ) (x : ι → Fin 4 → ℝ) (B : ℝ),
        0≤B → (∀ j∈T,1 ≤ m j ∧ m j≤N) →
        (∀ j∈T,‖w j‖≤1) →
        (∀ q : ℤ,((T.filter (fun j => m j=q)).card:ℝ)≤B) →
        (∀ i∈S,x i∈Icc ![0,0,-1,-1] (fun _ => 1)) →
        let U := fun j => ![(m j:ℝ),(m j:ℝ)^2,
          (1/η)*((m j:ℝ)/N)^((3:ℝ)/2),(1/ζ)*Real.sqrt ((m j:ℝ)/N)]
        let a : Fin 4 → ℝ := ![1/(12*(N:ℝ)),1/(12*(N:ℝ)^2),η/12,ζ/12]
        (∑ i∈S,‖∑ j∈T,w j*fordAdditiveCharacter (∑ d,U j d*x i d)‖)^12 ≤
          C*(N:ℝ)^((12:ℝ)+ε)*(S.card:ℝ)^10*B^12*
            (((S ×ˢ S).filter (fun ij => ∀ d, |x ij.1 d-x ij.2 d|≤2*a d)).card:ℝ) := by
  classical
  obtain ⟨C,hC,hcount⟩ := exists_bourgainSourceCurve_six_tuple_first_spacing.{v} hε
  let L : ℝ := 16777216*36*12^4
  refine ⟨L*C,by dsimp [L]; positivity,?_⟩
  intro N hN η ζ hη hζ ι κ S T w m x B hB hm hw hmass hx
  dsimp only
  have hNr : (1:ℝ)≤N := by exact_mod_cast hN
  have hNp : (0:ℝ)<N := by linarith
  have hηp : 0<η := lt_of_lt_of_le (by positivity) hη.1
  have hζp : 0<ζ := lt_of_lt_of_le (by positivity) hζ.1
  let a : Fin 4 → ℝ := ![1/(12*(N:ℝ)),1/(12*(N:ℝ)^2),η/12,ζ/12]
  let D : Fin 4 → ℝ := ![1,1,2,2]
  let c : Fin 4 → ℝ := ![0,0,-1,-1]
  let U := fun j => ![(m j:ℝ),(m j:ℝ)^2,
    (1/η)*((m j:ℝ)/N)^((3:ℝ)/2),(1/ζ)*Real.sqrt ((m j:ℝ)/N)]
  let V := Fintype.piFinset (fun _ : Fin 6 => T)
  let y := fun (j : Fin 6 → κ) d => ∑ k, U (j k) d
  let P := (S ×ˢ S).filter (fun ij => ∀ d, |x ij.1 d-x ij.2 d|≤2*a d)
  let Q := (V ×ˢ V).filter (fun ij => ∀ d, |y ij.1 d-y ij.2 d|≤1/(D d+2*a d))
  let K := 16777216*(∏ d,(D d+2*a d))/(∏ d,a d)
  obtain ⟨ha,hthreshold,hscale⟩ :=
    bourgain_source_sieve_box_scale hNr ⟨hηp,hη.2⟩ ⟨hζp,hζ.2⟩
  have hD d : 0<D d := by fin_cases d <;> norm_num [D,Matrix.cons_val_succ]
  have hU j (hj : j∈T) : ∀ d,a d*|U j d|≤1/12 :=
    bourgain_source_sieve_frequency_scale hNr
      (by exact ⟨by exact_mod_cast (hm j hj).1,by exact_mod_cast (hm j hj).2⟩) hηp hζp
  have hx' i (hi : i∈S) d : x i d∈Icc (c d) (c d+D d) := by
    refine ⟨(hx i hi).1 d,?_⟩
    have hh := (hx i hi).2 d
    fin_cases d <;> norm_num [c,D,Matrix.cons_val_succ] <;> exact hh
  have hs := bourgain_four_dimensional_sixth_power_sieve S T w x U ha hD hw hx' hU
  change (∑ i∈S,‖∑ j∈T,w j*fordAdditiveCharacter (∑ d,U j d*x i d)‖)^12 ≤
    (S.card:ℝ)^10*K*(P.card:ℝ)*(Q.card:ℝ) at hs
  have hfirst := hcount N hN η ζ hη hζ κ T m B hB hm hmass
  change (((V ×ˢ V).filter (fun ij => ∀ d,
      |y ij.1 d-y ij.2 d|≤(![1,1,1/2,1/2] : Fin 4 → ℝ) d)).card:ℝ) ≤
    C*η*ζ*(N:ℝ)^((9:ℝ)+ε)*B^12 at hfirst
  have hsub : Q ⊆ (V ×ˢ V).filter (fun ij => ∀ d,
      |y ij.1 d-y ij.2 d|≤(![1,1,1/2,1/2] : Fin 4 → ℝ) d) := by
    intro ij hij
    obtain ⟨hij,hnear⟩ := Finset.mem_filter.mp hij
    exact Finset.mem_filter.mpr ⟨hij,fun d => (hnear d).trans (hthreshold d)⟩
  have hQ : (Q.card:ℝ) ≤ C*η*ζ*(N:ℝ)^((9:ℝ)+ε)*B^12 :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hfirst
  have hK : 0≤K := by
    dsimp only [K]
    exact div_nonneg (mul_nonneg (by norm_num)
      (Finset.prod_nonneg (fun d _ => by linarith [hD d,ha d])))
      (Finset.prod_nonneg (fun d _ => (ha d).le))
  have hR : 0≤C*η*ζ*(N:ℝ)^((9:ℝ)+ε)*B^12 := by positivity
  have hCouter : 0≤(S.card:ℝ)^10*(P.card:ℝ) := by positivity
  have hpow : (N:ℝ)^3*(N:ℝ)^((9:ℝ)+ε)=(N:ℝ)^((12:ℝ)+ε) := by
    rw [←Real.rpow_ofNat,←Real.rpow_add hNp]
    congr 1
    ring
  have hbound := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hscale hR) hCouter
  calc
    _ ≤ (S.card:ℝ)^10*K*(P.card:ℝ)*(C*η*ζ*(N:ℝ)^((9:ℝ)+ε)*B^12) :=
      hs.trans (mul_le_mul_of_nonneg_left hQ (by positivity))
    _ = ((S.card:ℝ)^10*(P.card:ℝ))*(K*(C*η*ζ*(N:ℝ)^((9:ℝ)+ε)*B^12)) := by ring
    _ ≤ ((S.card:ℝ)^10*(P.card:ℝ))*
        ((L*(N:ℝ)^3/(η*ζ))*(C*η*ζ*(N:ℝ)^((9:ℝ)+ε)*B^12)) := hbound
    _ = _ := by
      change _ = (L*C)*(N:ℝ)^((12:ℝ)+ε)*(S.card:ℝ)^10*B^12*(P.card:ℝ)
      rw [←hpow]
      field_simp


public  theorem bourgain_dual_three_halves_remainder_derivative
    {x τ : ℝ} (hx : 0<x) (ht : 0<x+τ) :
    HasDerivAt (fun y : ℝ =>
      (Real.sqrt (y+τ))^3-(Real.sqrt y)^3-(3*τ/2)*Real.sqrt y)
      (-(3*τ^2)/(4*Real.sqrt x*(Real.sqrt (x+τ)+Real.sqrt x)^2)) x := by
  have hs : 0<Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsτ : 0<Real.sqrt (x+τ) := Real.sqrt_pos.mpr ht
  have hsum : Real.sqrt (x+τ)+Real.sqrt x ≠ 0 := by positivity
  have h₁ : HasDerivAt (fun y : ℝ => (Real.sqrt (y+τ))^3)
      ((3/2)*Real.sqrt (x+τ)) x := by
    convert (((hasDerivAt_id x).add_const τ).sqrt ht.ne').pow 3 using 1
    · rfl
    · norm_num only [Nat.reduceSub,Nat.cast_ofNat,id_eq]
      field_simp
  have h₂ : HasDerivAt (fun y : ℝ => (Real.sqrt y)^3) ((3/2)*Real.sqrt x) x := by
    convert (Real.hasDerivAt_sqrt hx.ne').pow 3 using 1
    norm_num only [Nat.reduceSub,Nat.cast_ofNat]
    field_simp
  have h₃ := (Real.hasDerivAt_sqrt hx.ne').const_mul (3*τ/2)
  have hr := nativeParabola_sqrt_linear_remainder (Real.sqrt x) (Real.sqrt (x+τ)) hs.ne' hsum
  rw [Real.sq_sqrt ht.le,Real.sq_sqrt hx.le,add_sub_cancel_left] at hr
  convert (h₁.sub h₂).sub h₃ using 1
  symm
  calc
    _ = (3/2)*(Real.sqrt (x+τ)-Real.sqrt x-τ/(2*Real.sqrt x)) := by ring
    _ = (3/2)*(-τ^2/(2*Real.sqrt x*(Real.sqrt (x+τ)+Real.sqrt x)^2)) := by
      congr 1
      linear_combination hr
    _ = _ := by
      field_simp
      ring

private theorem bourgain_dual_three_halves_remainder_bound
    {H x τ : ℝ} (hH : 1≤H) (hx : H≤x) (hτ : |τ|≤1/2) :
    |-(3*τ^2)/(4*Real.sqrt x*(Real.sqrt (x+τ)+Real.sqrt x)^2)| ≤
      1/(H*Real.sqrt H) := by
  have hHpos : 0<H := by linarith
  have hxpos : 0<x := hHpos.trans_le hx
  have hτs := abs_le.mp hτ
  have ht : 0<x+τ := by linarith
  have hs : 0<Real.sqrt x := Real.sqrt_pos.mpr hxpos
  have hHsqrt : 0<Real.sqrt H := Real.sqrt_pos.mpr hHpos
  have hsτ : 0<Real.sqrt (x+τ) := Real.sqrt_pos.mpr ht
  have hm : Real.sqrt H ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
  have hsq : τ^2 ≤ 1/4 := by nlinarith [sq_nonneg (τ-1/2),sq_nonneg (τ+1/2)]
  have hroot : H ≤ (Real.sqrt (x+τ)+Real.sqrt x)^2 := by
    nlinarith [Real.sq_sqrt hxpos.le,mul_nonneg hsτ.le hs.le]
  have hd : 0<4*Real.sqrt x*(Real.sqrt (x+τ)+Real.sqrt x)^2 := by positivity
  rw [abs_div,abs_neg,abs_of_nonneg (by positivity : 0≤3*τ^2),abs_of_pos hd]
  apply (div_le_div_iff₀ hd (mul_pos hHpos hHsqrt)).mpr
  have hp := mul_le_mul hm hroot hHpos.le hs.le
  nlinarith [mul_nonneg hHpos.le hHsqrt.le]

private theorem bourgain_dual_physical_scale {μ q N : ℝ}
    (hμ : 0<μ) (hq : 0<q) (hN : 0<N) (hqN : q≤N)
    (hscale : 1≤μ*q^2*N) :
    1≤μ*q*N^2 ∧
    |-2*μ*(Real.sqrt (2/(3*μ*q)))^3|/Real.sqrt (μ*q*N^2) ≤ 2 := by
  have hA : 1≤μ*q*N^2 := by
    have hh := mul_le_mul_of_nonneg_left hqN (by positivity : 0≤μ*q*N)
    nlinarith
  refine ⟨hA,?_⟩
  have hs := Real.sq_sqrt (by positivity : 0≤2/(3*μ*q))
  have ht := Real.sq_sqrt (by positivity : 0≤μ*q*N^2)
  have hs0 := Real.sqrt_nonneg (2/(3*μ*q))
  have ht0 := Real.sqrt_pos.mpr (by positivity : 0<μ*q*N^2)
  have hden : 0<3*μ*q := by positivity
  have hs' : (Real.sqrt (2/(3*μ*q)))^2*(3*μ*q)=2 :=
    (eq_div_iff hden.ne').mp hs
  rw [abs_mul,abs_mul,abs_of_nonpos (by norm_num : (-2:ℝ)≤0),
    abs_of_pos hμ,abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ ht0).mpr
  have hh : (μ*q^2*N)^2≥1 := by nlinarith
  have he : (μ*(Real.sqrt (2/(3*μ*q)))^3)^2*(27*μ*q^3)=8 := by
    nlinarith [show ((Real.sqrt (2/(3*μ*q)))^2*(3*μ*q))^3=8 by rw [hs']; norm_num]
  have hcomp : (μ*(Real.sqrt (2/(3*μ*q)))^3)^2 ≤ μ*q*N^2 := by
    apply (mul_le_mul_iff_left₀ (show 0<27*μ*q^3 by positivity)).mp
    rw [he]
    nlinarith
  nlinarith [show 0≤μ*(Real.sqrt (2/(3*μ*q)))^3 by positivity]

private theorem bourgain_dual_stationary_window {q N N₁ : ℕ}
    (hq : 0<q) (hN : 1≤N) (hN₁ : N₁≤2*N) (hqN : q≤N)
    {μ ℓ : ℝ} (hμ : 0<μ) (hscale : 1≤μ*(q:ℝ)^2*N)
    {b h : ℤ} (hτ : |((b:ℝ)-(q:ℝ)*ℓ)/2|≤1/2)
    (hh : b+2*h∈Finset.Icc
      ⌈(q:ℝ)*(3*μ*(N:ℝ)^2+ℓ)⌉ ⌊(q:ℝ)*(3*μ*(N₁:ℝ)^2+ℓ)⌋) :
    (h:ℝ)∈Icc (μ*(q:ℝ)*(N:ℝ)^2) (7*(μ*(q:ℝ)*(N:ℝ)^2)) := by
  have hqr : (0:ℝ)<q := by exact_mod_cast hq
  have hNr : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hqNr : (q:ℝ)≤N := by exact_mod_cast hqN
  have hN₁r : (N₁:ℝ)≤2*N := by exact_mod_cast hN₁
  have hN₁0 : (0:ℝ)≤N₁ := Nat.cast_nonneg _
  have hA := (bourgain_dual_physical_scale hμ hqr hNr hqNr hscale).1
  have ht := abs_le.mp hτ
  simp only [Finset.mem_Icc,Int.ceil_le,Int.le_floor] at hh
  push_cast at hh
  have hsq : (N₁:ℝ)^2≤4*(N:ℝ)^2 := by nlinarith
  have hh' := mul_le_mul_of_nonneg_left hsq (by positivity : 0≤3*μ*(q:ℝ))
  constructor <;> nlinarith [hh.1,hh.2,ht.1,ht.2]

                                                                    
                                                                      
                                                                  
theorem bourgain_cubic_dual_phase_coordinates (q : ℕ) [NeZero q]
    (a r : ℤ) (har : (q : ℤ) ∣ a*r-1) {μ : ℝ} (hμ : 0<μ)
    (ℓ : ℝ) (p : Fin 2) :
    let b : ℤ := ⌊(q:ℝ)*ℓ⌋+(p:ℕ)
    let τ : ℝ := ((b:ℝ)-(q:ℝ)*ℓ)/2
    let s := Real.sqrt (2/(3*μ*(q:ℝ)))
    let K := -2*μ*s^3
    let x : Fin 4 → ℝ := ![-(r:ℝ)*b/q,-(r:ℝ)/q,K,3*K*τ/2]
    let R : ℝ → ℝ := fun y =>
      K*((Real.sqrt (y+τ))^3-(Real.sqrt y)^3-(3*τ/2)*Real.sqrt y)
    |τ|≤1/2 ∧
    (∀ h : ℤ, 1 ≤ h →
      let u := Real.sqrt ((((b+2*h:ℤ):ℝ)/(q:ℝ)-ℓ)/(3*μ))
      bourgainQuadraticGauss q a (b+2*h)*
          ((𝐞 ((1:ℝ)/8-2*μ*u^3) : ℂ)/(Real.sqrt (6*μ*u):ℂ)) =
        (bourgainQuadraticGauss q a b*(𝐞 ((1:ℝ)/8):ℂ))*
          (fordAdditiveCharacter (∑ d, x d*
            (![ (h:ℝ),(h:ℝ)^2,(h:ℝ)^((3:ℝ)/2),Real.sqrt (h:ℝ)] : Fin 4 → ℝ) d))*
          (fordAdditiveCharacter (R h)/(Real.sqrt (6*μ*s*Real.sqrt ((h:ℝ)+τ)):ℂ))) ∧
    (∀ H : ℝ, 1≤H → ∀ y : ℝ, H≤y →
      HasDerivAt R (deriv R y) y ∧ |deriv R y|≤|K|/(H*Real.sqrt H)) ∧
    (∀ N N₁ : ℕ, 1≤N → N₁≤2*N → q≤N → 1≤μ*(q:ℝ)^2*N →
      let A := μ*(q:ℝ)*(N:ℝ)^2
      1≤A ∧
      (∀ y : ℝ, A≤y → HasDerivAt R (deriv R y) y ∧ |deriv R y|≤2/A) ∧
      (∀ h : ℤ, b+2*h∈Finset.Icc
        ⌈(q:ℝ)*(3*μ*(N:ℝ)^2+ℓ)⌉ ⌊(q:ℝ)*(3*μ*(N₁:ℝ)^2+ℓ)⌋ →
        (h:ℝ)∈Icc A (7*A))) := by
  dsimp only
  let b : ℤ := ⌊(q:ℝ)*ℓ⌋+(p:ℕ)
  let τ : ℝ := ((b:ℝ)-(q:ℝ)*ℓ)/2
  let s := Real.sqrt (2/(3*μ*(q:ℝ)))
  let K := -2*μ*s^3
  let x : Fin 4 → ℝ := ![-(r:ℝ)*b/q,-(r:ℝ)/q,K,3*K*τ/2]
  let R : ℝ → ℝ := fun y =>
    K*((Real.sqrt (y+τ))^3-(Real.sqrt y)^3-(3*τ/2)*Real.sqrt y)
  have hq : (0:ℝ)<q := by exact_mod_cast NeZero.pos q
  have hτ : |τ|≤1/2 := by
    have hl := Int.floor_le ((q:ℝ)*ℓ)
    have hu := Int.lt_floor_add_one ((q:ℝ)*ℓ)
    have hp0 : (0:ℝ)≤(p:ℕ) := Nat.cast_nonneg _
    have hp1 : ((p:ℕ):ℝ)≤1 := by exact_mod_cast (show (p:ℕ)≤1 by omega)
    dsimp only [τ,b]
    push_cast
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hderiv : ∀ H : ℝ, 1≤H → ∀ y : ℝ, H≤y →
      HasDerivAt R (deriv R y) y ∧ |deriv R y|≤|K|/(H*Real.sqrt H) := by
    intro H hH y hy
    have hy0 : 0<y := by linarith
    have hyt : 0<y+τ := by have ht := abs_le.mp hτ; linarith
    have hd := (bourgain_dual_three_halves_remainder_derivative hy0 hyt).const_mul K
    have hd' : HasDerivAt R
        (K*(-(3*τ^2)/(4*Real.sqrt y*(Real.sqrt (y+τ)+Real.sqrt y)^2))) y := hd
    refine ⟨hd'.differentiableAt.hasDerivAt,?_⟩

    rw [hd'.deriv,abs_mul]
    calc
      _ ≤ |K| *(1/(H*Real.sqrt H)) := mul_le_mul_of_nonneg_left
        (bourgain_dual_three_halves_remainder_bound hH hy hτ) (abs_nonneg _)
      _ = _ := by ring
  refine ⟨hτ,?_,hderiv,?_⟩
  · intro h hh
    have hh0 : (0:ℝ)≤h := by exact_mod_cast (by omega : 0≤h)
    have hroot :
        Real.sqrt ((((b+2*h:ℤ):ℝ)/(q:ℝ)-ℓ)/(3*μ)) =
          s*Real.sqrt ((h:ℝ)+τ) := by
      rw [show ((((b+2*h:ℤ):ℝ)/(q:ℝ)-ℓ)/(3*μ)) =
          (2/(3*μ*(q:ℝ)))*((h:ℝ)+τ) by
            dsimp only [τ]
            push_cast
            field_simp
            ring]
      exact Real.sqrt_mul (by positivity) _
    have hcube : (Real.sqrt (h:ℝ))^3 = (h:ℝ)^((3:ℝ)/2) := by
      rw [Real.sqrt_eq_rpow,←Real.rpow_natCast,←Real.rpow_mul hh0]
      norm_num
    have he : -((r:ℝ)*(h:ℝ)^2+(r:ℝ)*(b:ℝ)*(h:ℝ))/(q:ℝ)+
        ((1:ℝ)/8-2*μ*(s*Real.sqrt ((h:ℝ)+τ))^3) =
        (1:ℝ)/8+(∑ d,x d*
          (![ (h:ℝ),(h:ℝ)^2,(h:ℝ)^((3:ℝ)/2),Real.sqrt (h:ℝ)] : Fin 4 → ℝ) d)+R h := by
      dsimp only [R]
      rw [hcube]
      simp only [x,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
        Fin.sum_univ_zero,add_zero]
      dsimp only [K]
      ring
    rw [bourgainQuadraticGauss_inverse_shift q a r b h har,hroot]
    have hc := congrArg (fun t : ℝ => (𝐞 t : ℂ)) he
    simp only [sargos_ford_character_eq_fourier]
    simp only [AddChar.map_add_eq_mul, Circle.coe_mul] at hc
    rw [show 6*μ*(s*Real.sqrt ((h:ℝ)+τ))=6*μ*s*Real.sqrt ((h:ℝ)+τ) by ring]
    calc
      _ = bourgainQuadraticGauss q a b*
          ((𝐞 (-((r:ℝ)*(h:ℝ)^2+(r:ℝ)*(b:ℝ)*(h:ℝ))/(q:ℝ)):ℂ)*
            (𝐞 ((1:ℝ)/8-2*μ*(s*Real.sqrt ((h:ℝ)+τ))^3):ℂ))/
            (Real.sqrt (6*μ*s*Real.sqrt ((h:ℝ)+τ)):ℂ) := by ring
      _ = _ := by rw [hc]; ring
  · intro N N₁ hN hN₁ hqN hscale
    have hNr : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
    have hqNr : (q:ℝ)≤N := by exact_mod_cast hqN
    obtain ⟨hA,hK⟩ := bourgain_dual_physical_scale hμ hq hNr hqNr hscale
    refine ⟨hA,?_,?_⟩
    · intro y hy
      have hd := hderiv _ hA y hy
      refine ⟨hd.1,hd.2.trans ?_⟩
      calc
        _ = (|K|/Real.sqrt (μ*(q:ℝ)*(N:ℝ)^2))/(μ*(q:ℝ)*(N:ℝ)^2) := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hK (by positivity)
    · intro h hh
      exact bourgain_dual_stationary_window (NeZero.pos q) hN hN₁ hqN hμ hscale hτ hh


public  theorem bourgain_weighted_interval_common_fourier
    {N : ℕ} [NeZero N] {ι : Type*} (S : Finset ι)
    (f : ι → ZMod N → ℂ) (w : ι → ℕ → ℂ) (A H : ι → ℕ)
    {V : ℝ} (hV : 0≤V) (hH : ∀ i∈S, A i+H i≤N)
    (hw : ∀ i∈S, ‖w i (H i-1)‖≤1)
    (hv : ∀ i∈S, (∑ j∈Finset.range (H i-1), ‖w i (j+1)-w i j‖)≤V) :
    ∃ k : ZMod N,
      (∑ i∈S, ‖∑ j∈Finset.range (H i), w i j*f i ((A i+j:ℕ):ZMod N)‖) ≤
        (6*(1+V)*(1+Real.log N))*∑ i∈S, ‖ZMod.dft (f i) k‖ := by
  classical
  let F := fun i => ∑ k : ZMod N, sargosPrefixMajorant k*‖ZMod.dft (f i) k‖
  have hF i : 0≤F i := Finset.sum_nonneg
    (fun k _ => mul_nonneg (sargosPrefixMajorant_nonneg k) (norm_nonneg _))
  have hp i (hi : i∈S) n (hn : n≤H i) :
      ‖∑ j∈Finset.range n, f i ((A i+j:ℕ):ZMod N)‖ ≤ 2*F i := by
    have he : (∑ j∈Finset.range n, f i ((A i+j:ℕ):ZMod N)) =
        sargosFinitePrefix (f i) (A i+n)-sargosFinitePrefix (f i) (A i) := by
      unfold sargosFinitePrefix
      rw [Finset.sum_range_add]
      abel
    rw [he]
    have h₁ := norm_sargosFinitePrefix_le_fourierMajorant (f i)
      (show A i+n≤N by linarith [hH i hi])
    have h₂ := norm_sargosFinitePrefix_le_fourierMajorant (f i)
      (show A i≤N by linarith [hH i hi])
    exact (norm_sub_le _ _).trans ((add_le_add h₁ h₂).trans_eq (by ring))
  have hi i (hi : i∈S) :
      ‖∑ j∈Finset.range (H i), w i j*f i ((A i+j:ℕ):ZMod N)‖ ≤ (1+V)*(2*F i) :=
    norm_weighted_range_of_prefix_bound _ _ (H i) (mul_nonneg (by norm_num) (hF i))
      (hp i hi) (hw i hi) (hv i hi)
  let Z := fun k : ZMod N => ∑ i∈S, ‖ZMod.dft (f i) k‖
  obtain ⟨k,hk,hmax⟩ := Finset.univ.exists_max_image Z Finset.univ_nonempty
  have hZ : 0≤Z k := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  refine ⟨k,?_⟩
  calc
    _ ≤ ∑ i∈S, (1+V)*(2*F i) := Finset.sum_le_sum hi
    _ = (2*(1+V))*∑ l : ZMod N, sargosPrefixMajorant l*Z l := by
      simp only [F,Z,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ (2*(1+V))*∑ l : ZMod N, sargosPrefixMajorant l*Z k := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun l hl => mul_le_mul_of_nonneg_left
        (hmax l hl) (sargosPrefixMajorant_nonneg l))
    _ = (2*(1+V))*(∑ l : ZMod N, sargosPrefixMajorant l)*Z k := by
      rw [←Finset.sum_mul]
      ring
    _ ≤ (2*(1+V))*(3*(1+Real.log N))*Z k :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left sum_sargosPrefixMajorant_le_log (by positivity)) hZ
    _ = _ := by ring

public  theorem bourgain_dual_amplitude_bound {μ q N y τ : ℝ}
    (hμ : 0<μ) (hq : 0<q) (hN : 0<N)
    (hA : 1≤μ*q*N^2) (hy : μ*q*N^2≤y) (hτ : |τ|≤1/2) :
    0 ≤ Real.sqrt (μ*N)/Real.sqrt (6*μ*Real.sqrt (2/(3*μ*q))*Real.sqrt (y+τ)) ∧
    Real.sqrt (μ*N)/Real.sqrt (6*μ*Real.sqrt (2/(3*μ*q))*Real.sqrt (y+τ)) ≤ 1 := by
  have ht := abs_le.mp hτ
  have hyτ : 0<y+τ := by linarith
  have hs : 0<Real.sqrt (2/(3*μ*q)) := by positivity
  have hr : 0<Real.sqrt (y+τ) := Real.sqrt_pos.mpr hyτ
  have hsq := Real.sq_sqrt (by positivity : 0≤2/(3*μ*q))
  have hsq' : (Real.sqrt (2/(3*μ*q)))^2*(3*μ*q)=2 :=
    (eq_div_iff (by positivity : 3*μ*q≠0)).mp hsq
  have hroot : N/6 ≤ Real.sqrt (2/(3*μ*q))*Real.sqrt (y+τ) := by
    have hy' : μ*q*N^2/2 ≤ y+τ := by linarith
    have hb := mul_le_mul_of_nonneg_left hy' (sq_nonneg (Real.sqrt (2/(3*μ*q))))
    have he : (Real.sqrt (2/(3*μ*q)))^2*(μ*q*N^2/2)=N^2/3 := by
      nlinarith [congrArg (fun t : ℝ => t*N^2) hsq']
    rw [he,←Real.sq_sqrt hyτ.le,←mul_pow] at hb
    nlinarith [mul_nonneg hs.le hr.le]
  have hden : 0<Real.sqrt (6*μ*Real.sqrt (2/(3*μ*q))*Real.sqrt (y+τ)) := by positivity
  refine ⟨by positivity,(div_le_one hden).mpr ?_⟩
  apply Real.sqrt_le_sqrt
  nlinarith

private theorem bourgain_dual_stationary_weight_variation
    {μ q N L τ : ℝ} (hμ : 0<μ) (hq : 0<q) (hN : 0<N)
    (hA : 1≤μ*q*N^2) (hL : μ*q*N^2≤L) (hτ : |τ|≤1/2)
    (H : ℕ) (hH : (H:ℝ)≤7*(μ*q*N^2)) (R : ℝ → ℝ)
    (hR : ∀ y : ℝ, μ*q*N^2≤y →
      HasDerivAt R (deriv R y) y ∧ |deriv R y|≤2/(μ*q*N^2)) :
    let w := fun j : ℕ =>
      ((Real.sqrt (μ*N)/Real.sqrt
        (6*μ*Real.sqrt (2/(3*μ*q))*Real.sqrt (L+j+τ))):ℂ)*
        fordAdditiveCharacter (R (L+j))
    ‖w (H-1)‖≤1 ∧
      (∑ j∈Finset.range (H-1), ‖w (j+1)-w j‖)≤2*(1+28*Real.pi) := by
  dsimp only
  let g := fun j : ℕ => Real.sqrt (μ*N)/Real.sqrt
    (6*μ*Real.sqrt (2/(3*μ*q))*Real.sqrt (L+j+τ))
  have hg j : 0≤g j ∧ g j≤1 := bourgain_dual_amplitude_bound hμ hq hN hA
    (by linarith [Nat.cast_nonneg (α:=ℝ) j]) hτ
  have hy (j : ℕ) : 0<L+(j:ℝ)+τ := by
    have ht := abs_le.mp hτ
    linarith [Nat.cast_nonneg (α:=ℝ) j]
  have hmono : AntitoneOn g (Iic (H-1)) := by
    intro i hi j hj hij
    have hijr : (i:ℝ)≤j := by exact_mod_cast hij
    dsimp only [g]
    exact div_le_div_of_nonneg_left (by positivity)
      (by have hp := hy i; positivity)
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (by linarith)) (by positivity)))
  have hgv := finiteVariationBound_of_antitone (by norm_num : (0:ℝ)≤1)
    hmono (fun j _ => hg j)
  have hv := continuous_character_range_variation R (deriv R) L H
    (by positivity : 0≤2/(μ*q*N^2))
    (fun y hy => (hR y (hL.trans hy.1)).1)
    (fun y hy => (hR y (hL.trans hy.1)).2)
  have hvar :
      (∑ j∈Finset.range (H-1),
        ‖fordAdditiveCharacter (R (L+(j+1)))-fordAdditiveCharacter (R (L+j))‖)≤
        1+28*Real.pi := by
    apply hv.trans
    have hHp : (H:ℝ)/(μ*q*N^2)≤7 :=
      (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    have ht := mul_le_mul_of_nonneg_left hHp (by positivity : 0≤4*Real.pi)
    calc
      _ = 4*Real.pi*((H:ℝ)/(μ*q*N^2)) := by ring
      _ ≤ 4*Real.pi*7 := ht
      _ ≤ _ := by linarith
  have hev : FiniteVariationBound (fun j => fordAdditiveCharacter (R (L+j)))
      (H-1) (1+28*Real.pi) := by
    refine ⟨by positivity,?_,?_⟩
    · intro j hj
      rw [sargos_character_norm]
      linarith [Real.pi_pos]
    · simpa only [Nat.cast_add,Nat.cast_one] using hvar
  have hprod := hgv.mul hev
  constructor
  · rw [norm_mul,sargos_character_norm,mul_one,←Complex.ofReal_div]
    change ‖(g (H-1):ℂ)‖≤1
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hg (H-1)).1]
    exact (hg (H-1)).2
  · simpa only [g,Complex.ofReal_div,mul_one] using hprod.variation_le

public  theorem bourgain_dual_branch_normalized
    (q : ℕ) [NeZero q] (a r : ℤ) (har : (q:ℤ)∣a*r-1)
    {μ N : ℝ} (hμ : 0<μ) (hN : 0<N) (ℓ : ℝ) (p : Fin 2)
    (h : ℤ) (hh : 1≤h) :
    let b : ℤ := ⌊(q:ℝ)*ℓ⌋+(p:ℕ)
    let τ := ((b:ℝ)-(q:ℝ)*ℓ)/2
    let s := Real.sqrt (2/(3*μ*(q:ℝ)))
    let K := -2*μ*s^3
    let x : Fin 4 → ℝ := ![-(r:ℝ)*b/q,-(r:ℝ)/q,K,3*K*τ/2]
    let R := fun y : ℝ => K*((Real.sqrt (y+τ))^3-(Real.sqrt y)^3-(3*τ/2)*Real.sqrt y)
    let u := Real.sqrt ((((b+2*h:ℤ):ℝ)/(q:ℝ)-ℓ)/(3*μ))
    let W := ((Real.sqrt (μ*N)/Real.sqrt (6*μ*s*Real.sqrt ((h:ℝ)+τ))):ℂ)*
      fordAdditiveCharacter (R h)
    let C := (q:ℂ)⁻¹*bourgainQuadraticGauss q a b*(𝐞 ((1:ℝ)/8):ℂ)/(Real.sqrt (μ*N):ℂ)
    (q:ℂ)⁻¹*bourgainQuadraticGauss q a (b+2*h)*
      ((𝐞 ((1:ℝ)/8-2*μ*u^3):ℂ)/(Real.sqrt (6*μ*u):ℂ)) =
      W*(C*fordAdditiveCharacter (∑ d,x d*
        (![ (h:ℝ),(h:ℝ)^2,(h:ℝ)^((3:ℝ)/2),Real.sqrt (h:ℝ)] : Fin 4 → ℝ) d)) := by
  have he := (bourgain_cubic_dual_phase_coordinates q a r har hμ ℓ p).2.1 h hh
  dsimp only at he ⊢
  rw [mul_assoc (q:ℂ)⁻¹,he]
  have hs : (Real.sqrt (μ*N):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  push_cast
  field_simp

public  theorem bourgain_dual_coefficient_norm
    (q : ℕ) [NeZero q] (a r b : ℤ) (har : (q:ℤ)∣a*r-1)
    {μ N : ℝ} (hμ : 0<μ) (hN : 0<N) :
    ‖(q:ℂ)⁻¹*bourgainQuadraticGauss q a b*
      (𝐞 ((1:ℝ)/8):ℂ)/(Real.sqrt (μ*N):ℂ)‖ ≤
      Real.sqrt (2*(q:ℝ))/((q:ℝ)*Real.sqrt (μ*N)) := by
  obtain ⟨t,ht⟩ := har
  have ha : IsCoprime a (q:ℤ) := by
    refine ⟨r,-t,?_⟩
    nlinarith
  have hG := bourgainQuadraticGauss_norm_le q a b ha
  rw [norm_div,norm_mul,norm_mul,norm_inv,Complex.norm_natCast,
    Circle.norm_coe,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ ((q:ℝ)⁻¹*Real.sqrt (2*(q:ℝ)))/Real.sqrt (μ*N) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hG (by positivity)) (by positivity)
    _ = _ := by ring

set_option maxHeartbeats 400000 in
                                                                   
                                                                      
                                                       
private theorem bourgain_cubic_dual_branch_common_fourier
    {M : ℕ} [NeZero M] {ι : Type*} (S : Finset ι)
    (q N L H : ι → ℕ) (a r : ι → ℤ) (μ ℓ : ι → ℝ) (p : ι → Fin 2)
    (hq : ∀ i∈S, 0<q i) (hN : ∀ i∈S, 1≤N i) (hqN : ∀ i∈S, q i≤N i)
    (hμ : ∀ i∈S, 0<μ i) (hscale : ∀ i∈S, 1≤μ i*(q i:ℝ)^2*N i)
    (har : ∀ i∈S, (q i:ℤ)∣a i*r i-1)
    (hL : ∀ i∈S, μ i*(q i:ℝ)*(N i:ℝ)^2≤L i)
    (hH : ∀ i∈S, (H i:ℝ)≤7*(μ i*(q i:ℝ)*(N i:ℝ)^2))
    (hwindow : ∀ i∈S, L i+H i≤M+1) :
    let b := fun i => (⌊(q i:ℝ)*ℓ i⌋+(p i:ℕ) : ℤ)
    let τ := fun i => ((b i:ℝ)-(q i:ℝ)*ℓ i)/2
    let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
    let K := fun i => -2*μ i*(s i)^3
    let x := fun i => (![-(r i:ℝ)*b i/q i,-(r i:ℝ)/q i,K i,3*K i*τ i/2] : Fin 4 → ℝ)
    ∃ k : ZMod M,
      (∑ i∈S, ‖(q i:ℂ)⁻¹*∑ j∈Finset.range (H i),
        let h : ℤ := L i+j
        let u := Real.sqrt ((((b i+2*h:ℤ):ℝ)/(q i:ℝ)-ℓ i)/(3*μ i))
        bourgainQuadraticGauss (q i) (a i) (b i+2*h)*
          ((𝐞 ((1:ℝ)/8-2*μ i*u^3):ℂ)/(Real.sqrt (6*μ i*u):ℂ))‖) ≤
        (6*(3+56*Real.pi)*(1+Real.log M))*
          ∑ i∈S, (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*N i)))*
            ‖∑ j : ZMod M,
            ZMod.stdAddChar (-(j*k))*
              fordAdditiveCharacter (∑ d,x i d*
                (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                  Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖ := by
  classical
  dsimp only
  let b := fun i => (⌊(q i:ℝ)*ℓ i⌋+(p i:ℕ) : ℤ)
  let τ := fun i => ((b i:ℝ)-(q i:ℝ)*ℓ i)/2
  let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
  let K := fun i => -2*μ i*(s i)^3
  let x := fun i => (![-(r i:ℝ)*b i/q i,-(r i:ℝ)/q i,K i,3*K i*τ i/2] : Fin 4 → ℝ)
  let R := fun i y => K i*((Real.sqrt (y+τ i))^3-(Real.sqrt y)^3-(3*τ i/2)*Real.sqrt y)
  let C := fun i => (q i:ℂ)⁻¹*bourgainQuadraticGauss (q i) (a i) (b i)*
    (𝐞 ((1:ℝ)/8):ℂ)/(Real.sqrt (μ i*N i):ℂ)
  let U := fun y : ℝ => (![y,y^2,y^((3:ℝ)/2),Real.sqrt y] : Fin 4 → ℝ)
  let f := fun i (j : ZMod M) => C i*fordAdditiveCharacter (∑ d,x i d*U (j.val+1) d)
  let w := fun i (j : ℕ) =>
    ((Real.sqrt (μ i*N i)/Real.sqrt
      (6*μ i*s i*Real.sqrt ((L i:ℝ)+j+τ i))):ℂ)*
      fordAdditiveCharacter (R i ((L i:ℝ)+j))
  have hdata i (hi : i∈S) :
      1≤L i ∧ ‖w i (H i-1)‖≤1 ∧
      (∑ j∈Finset.range (H i-1),‖w i (j+1)-w i j‖)≤2*(1+28*Real.pi) := by
    let : NeZero (q i) := ⟨(hq i hi).ne'⟩
    have hp := bourgain_cubic_dual_phase_coordinates (q i) (a i) (r i) (har i hi)
      (hμ i hi) (ℓ i) (p i)
    have hd := hp.2.2.2 (N i) (N i) (hN i hi) (by omega) (hqN i hi) (hscale i hi)
    have hL' : (1:ℝ)≤L i := hd.1.trans (hL i hi)
    refine ⟨by exact_mod_cast hL',?_⟩
    exact bourgain_dual_stationary_weight_variation (hμ i hi)
      (by exact_mod_cast hq i hi) (by exact_mod_cast (by have := hN i hi; omega : 0<N i))
      hd.1 (hL i hi) hp.1 (H i) (hH i hi) (R i) hd.2.1
  have hf i (hi : i∈S) j (hj : j∈Finset.range (H i)) :
      w i j*f i (((L i-1)+j:ℕ):ZMod M) =
        (q i:ℂ)⁻¹*bourgainQuadraticGauss (q i) (a i) (b i+2*((L i+j:ℕ):ℤ))*
          ((𝐞 ((1:ℝ)/8-2*μ i*
            (Real.sqrt ((((b i+2*((L i+j:ℕ):ℤ):ℤ):ℝ)/(q i:ℝ)-ℓ i)/(3*μ i)))^3):ℂ)/
            (Real.sqrt (6*μ i*Real.sqrt
              ((((b i+2*((L i+j:ℕ):ℤ):ℤ):ℝ)/(q i:ℝ)-ℓ i)/(3*μ i))):ℂ)) := by
    let : NeZero (q i) := ⟨(hq i hi).ne'⟩
    have hLj := (hdata i hi).1
    have hbound : L i-1+j<M := by
      have := hwindow i hi
      have := Finset.mem_range.mp hj
      omega
    have he := bourgain_dual_branch_normalized (q i) (a i) (r i) (har i hi)
      (hμ i hi) (show (0:ℝ)<N i by exact_mod_cast (by have := hN i hi; omega : 0<N i))
      (ℓ i) (p i) (L i+j) (by exact_mod_cast (show 1≤L i+j by omega))
    dsimp only at he
    dsimp only [f]
    rw [ZMod.val_cast_of_lt hbound]
    have hcast : ((L i-1+j:ℕ):ℝ)+1=(L i:ℝ)+j := by
      exact_mod_cast (show L i-1+j+1=L i+j by omega)
    rw [hcast]
    simpa only [w,C,x,U,K,s,τ,b,R,Nat.cast_add,Int.cast_natCast,Int.cast_add] using he.symm
  obtain ⟨k,hk⟩ := bourgain_weighted_interval_common_fourier S f w (fun i => L i-1) H
    (by positivity : 0≤2*(1+28*Real.pi))
    (fun i hi => by

      have := (hdata i hi).1
      have := hwindow i hi
      omega)
    (fun i hi => (hdata i hi).2.1) (fun i hi => (hdata i hi).2.2)
  refine ⟨k,?_⟩
  have he i (hi : i∈S) :
      (∑ j∈Finset.range (H i),w i j*f i (((L i-1)+j:ℕ):ZMod M)) =
      (q i:ℂ)⁻¹*∑ j∈Finset.range (H i),
        let h : ℤ := L i+j
        let u := Real.sqrt ((((b i+2*h:ℤ):ℝ)/(q i:ℝ)-ℓ i)/(3*μ i))
        bourgainQuadraticGauss (q i) (a i) (b i+2*h)*
          ((𝐞 ((1:ℝ)/8-2*μ i*u^3):ℂ)/(Real.sqrt (6*μ i*u):ℂ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simpa only [Nat.cast_add,mul_assoc] using hf i hi j hj
  have heDFT i :
      ZMod.dft (f i) k = C i*∑ j : ZMod M,
        ZMod.stdAddChar (-(j*k))*fordAdditiveCharacter (∑ d,x i d*U (j.val+1) d) := by
    rw [ZMod.dft_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [f,smul_eq_mul]
    ring
  simp_rw [heDFT] at hk
  have heSum := Finset.sum_congr rfl (fun i hi => congrArg norm (he i hi))
  rw [heSum] at hk
  rw [show 6*(1+2*(1+28*Real.pi))=6*(3+56*Real.pi) by ring] at hk
  apply hk.trans
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro i hi
    let : NeZero (q i) := ⟨(hq i hi).ne'⟩
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact bourgain_dual_coefficient_norm (q i) (a i) (r i) (b i) (har i hi) (hμ i hi)
      (by exact_mod_cast (by have := hN i hi; omega : 0<N i))
  · have hM : (1:ℝ)≤M := by exact_mod_cast NeZero.pos M
    have hlog := Real.log_nonneg hM
    positivity

public  theorem bourgain_integer_interval_parity_split
    (K₀ K₁ b : ℤ) (F : ℤ → ℂ) :
    (∑ k∈Finset.Icc K₀ K₁,F k) =
      ∑ p : Fin 2, ∑ h∈Finset.Icc
        ((K₀-b-(p:ℕ)+1)/2) ((K₁-b-(p:ℕ))/2),
        F (b+(p:ℕ)+2*h) := by
  classical
  let T := Finset.univ.sigma (fun p : Fin 2 =>
    Finset.Icc ((K₀-b-(p:ℕ)+1)/2) ((K₁-b-(p:ℕ))/2))
  symm
  rw [Finset.sum_sigma']
  change (∑ t∈T,F (b+(t.1:ℕ)+2*t.2))=_
  refine Finset.sum_bij (fun t _ => b+(t.1:ℕ)+2*t.2) ?_ ?_ ?_ ?_
  · intro t ht
    have hh := (Finset.mem_sigma.mp ht).2
    have hp := t.1.2
    simp only [Finset.mem_Icc] at hh ⊢
    omega
  · intro t ht u hu he

    have hp := t.1.2
    have hp' := u.1.2
    have hpEq : t.1=u.1 := Fin.ext (by omega)
    cases t with
    | mk p h =>
      cases u with
      | mk p' h' =>
        dsimp only at hpEq he
        subst p'
        congr 1
        omega
  · intro k hk
    have hrem : 0≤(k-b)%2 ∧ (k-b)%2<2 := ⟨Int.emod_nonneg _ (by omega),Int.emod_lt_of_pos _ (by omega)⟩
    let p : Fin 2 := ⟨((k-b)%2).toNat,by omega⟩
    let h := (k-b)/2
    have hp : ((p:ℕ):ℤ)=(k-b)%2 := by
      dsimp only [p]
      exact Int.toNat_of_nonneg hrem.1
    have he : b+(p:ℕ)+2*h=k := by
      dsimp only [h]
      rw [hp]
      omega
    refine ⟨⟨p,h⟩,?_,he⟩
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    simp only [Finset.mem_Icc] at hk ⊢
    dsimp only [h]
    rw [hp]
    omega
  · intro t ht
    rfl

private theorem bourgain_cubic_parity_interval_scales
    {q N N₁ M : ℕ} (hq : 0<q) (hN : 1≤N) (hN₁ : N₁≤2*N) (hqN : q≤N)
    {μ ℓ : ℝ} (hμ : 0<μ) (hscale : 1≤μ*(q:ℝ)^2*N)
    (hM : 7*(μ*(q:ℝ)*(N:ℝ)^2)≤M) (p : Fin 2) :
    let b : ℤ := ⌊(q:ℝ)*ℓ⌋+(p:ℕ)
    let l : ℤ := (⌈(q:ℝ)*(3*μ*(N:ℝ)^2+ℓ)⌉-b+1)/2
    let u : ℤ := (⌊(q:ℝ)*(3*μ*(N₁:ℝ)^2+ℓ)⌋-b)/2
    0≤l ∧ μ*(q:ℝ)*(N:ℝ)^2≤(l.toNat:ℝ) ∧
      (((u-l+1).toNat:ℕ):ℝ)≤7*(μ*(q:ℝ)*(N:ℝ)^2) ∧
      l.toNat+(u-l+1).toNat≤M+1 := by
  dsimp only
  let b : ℤ := ⌊(q:ℝ)*ℓ⌋+(p:ℕ)
  let l : ℤ := (⌈(q:ℝ)*(3*μ*(N:ℝ)^2+ℓ)⌉-b+1)/2
  let u : ℤ := (⌊(q:ℝ)*(3*μ*(N₁:ℝ)^2+ℓ)⌋-b)/2
  let A := μ*(q:ℝ)*(N:ℝ)^2
  have hqr : (0:ℝ)<q := by exact_mod_cast hq
  have hNr : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hqNr : (q:ℝ)≤N := by exact_mod_cast hqN
  have hA : 1≤A := (bourgain_dual_physical_scale hμ hqr hNr hqNr hscale).1
  have hp0 : (0:ℝ)≤(p:ℕ) := Nat.cast_nonneg _
  have hp1 : ((p:ℕ):ℝ)≤1 := by exact_mod_cast (show (p:ℕ)≤1 by omega)
  have hbLo : (q:ℝ)*ℓ-1≤(b:ℝ) := by
    have hh := Int.lt_floor_add_one ((q:ℝ)*ℓ)
    dsimp only [b]
    push_cast
    linarith
  have hbHi : (b:ℝ)≤(q:ℝ)*ℓ+1 := by
    have hh := Int.floor_le ((q:ℝ)*ℓ)
    dsimp only [b]
    push_cast
    linarith
  have hlInt : ⌈(q:ℝ)*(3*μ*(N:ℝ)^2+ℓ)⌉≤b+2*l := by dsimp only [l]; omega
  have hlInt' : b+2*l≤⌈(q:ℝ)*(3*μ*(N:ℝ)^2+ℓ)⌉+1 := by dsimp only [l]; omega
  have hlLo : (q:ℝ)*(3*μ*(N:ℝ)^2+ℓ)≤(b:ℝ)+2*l := by
    have hh := (Int.le_ceil ((q:ℝ)*(3*μ*(N:ℝ)^2+ℓ))).trans
      (show (⌈(q:ℝ)*(3*μ*(N:ℝ)^2+ℓ)⌉:ℝ)≤((b+2*l:ℤ):ℝ) by exact_mod_cast hlInt)
    simpa only [Int.cast_add,Int.cast_mul,Int.cast_ofNat] using hh
  have hlHi : (b:ℝ)+2*l<(q:ℝ)*(3*μ*(N:ℝ)^2+ℓ)+2 := by
    have hc := Int.ceil_lt_add_one ((q:ℝ)*(3*μ*(N:ℝ)^2+ℓ))
    have hh : (b:ℝ)+2*l≤(⌈(q:ℝ)*(3*μ*(N:ℝ)^2+ℓ)⌉:ℝ)+1 := by exact_mod_cast hlInt'
    linarith
  have hlA : A≤(l:ℝ) := by dsimp only [A] at hA ⊢; nlinarith
  have hl3 : (l:ℝ)≤3*A := by dsimp only [A] at hA ⊢; nlinarith
  have hl1 : (1:ℤ)≤l := by exact_mod_cast hA.trans hlA
  have hl0 : 0≤l := by omega
  have hcast : ((l.toNat:ℕ):ℝ)=(l:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hl0
  have huInt : b+2*u≤⌊(q:ℝ)*(3*μ*(N₁:ℝ)^2+ℓ)⌋ := by dsimp only [u]; omega
  have huHi : (b:ℝ)+2*u≤(q:ℝ)*(3*μ*(N₁:ℝ)^2+ℓ) := by
    have hh : ((b+2*u:ℤ):ℝ)≤(⌊(q:ℝ)*(3*μ*(N₁:ℝ)^2+ℓ)⌋:ℝ) := by exact_mod_cast huInt
    have hh' := hh.trans (Int.floor_le _)
    simpa only [Int.cast_add,Int.cast_mul,Int.cast_ofNat] using hh'
  have hN₁r : (N₁:ℝ)≤2*N := by exact_mod_cast hN₁
  have hsq : (N₁:ℝ)^2≤4*(N:ℝ)^2 := by nlinarith [Nat.cast_nonneg (α:=ℝ) N₁]
  have hmsq := mul_le_mul_of_nonneg_left hsq (by positivity : 0≤3*μ*(q:ℝ))
  have huA : (u:ℝ)≤7*A := by dsimp only [A] at hA ⊢; nlinarith
  refine ⟨hl0,by change A≤(l.toNat:ℝ); rw [hcast]; exact hlA,?_,?_⟩
  · by_cases hh : 0≤u-l+1
    · have hc : (((u-l+1).toNat:ℕ):ℝ)=(u:ℝ)-l+1 := by
        exact_mod_cast Int.toNat_of_nonneg hh
      rw [hc]
      have hl1r : (1:ℝ)≤l := by exact_mod_cast hl1
      linarith
    · rw [Int.toNat_of_nonpos (by omega)]
      norm_num only [Nat.cast_zero]
      positivity
  · have hlM : l≤M := by
      have hh : (l:ℝ)≤M := hl3.trans ((by nlinarith : 3*A≤7*A).trans hM)
      exact_mod_cast hh
    have huM : u≤M := by exact_mod_cast huA.trans hM
    omega

public  theorem bourgain_sum_integer_Icc_range (l u : ℤ) (F : ℤ → ℂ) :
    (∑ h∈Finset.Icc l u,F h)=
      ∑ j∈Finset.range (u-l+1).toNat,F (l+j) := by
  classical
  symm
  refine Finset.sum_bij (fun j _ => l+(j:ℤ)) ?_ ?_ ?_ ?_
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    apply Finset.mem_Icc.mpr

    omega
  · intro j hj k hk he

    omega
  · intro h hh
    have hh' := Finset.mem_Icc.mp hh
    refine ⟨(h-l).toNat,?_,?_⟩
    · apply Finset.mem_range.mpr
      omega
    ·
      omega
  · intro j hj
    rfl

set_option maxHeartbeats 400000 in
                                                                    
                                                                           
                                                                         
                                                                  
theorem bourgain_cubic_gauss_main_common_fourier
    {M : ℕ} [NeZero M] {ι : Type*} (S : Finset ι)
    (q N N₁ : ι → ℕ) (a r : ι → ℤ) (μ ℓ : ι → ℝ)
    (hq : ∀ i∈S, 0<q i) (hN : ∀ i∈S, 1≤N i)
    (hN₁ : ∀ i∈S, N₁ i≤2*N i) (hqN : ∀ i∈S, q i≤N i)
    (hμ : ∀ i∈S, 0<μ i) (hscale : ∀ i∈S, 1≤μ i*(q i:ℝ)^2*N i)
    (har : ∀ i∈S, (q i:ℤ)∣a i*r i-1)
    (hM : ∀ i∈S, 7*(μ i*(q i:ℝ)*(N i:ℝ)^2)≤M) :
    let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
    let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
    let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
    let K := fun i => -2*μ i*(s i)^3
    let x := fun i p =>
      (![-(r i:ℝ)*b i p/q i,-(r i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
    ∃ k : ZMod M,
      (∑ i∈S, ‖(q i:ℂ)⁻¹*∑ v∈Finset.Icc
        ⌈(q i:ℝ)*(3*μ i*(N i:ℝ)^2+ℓ i)⌉
        ⌊(q i:ℝ)*(3*μ i*(N₁ i:ℝ)^2+ℓ i)⌋,
        let u := Real.sqrt (((v:ℝ)/(q i:ℝ)-ℓ i)/(3*μ i))
        bourgainQuadraticGauss (q i) (a i) v*
          ((𝐞 ((1:ℝ)/8-2*μ i*u^3):ℂ)/(Real.sqrt (6*μ i*u):ℂ))‖) ≤
        (6*(3+56*Real.pi)*(1+Real.log M))*
          ∑ i∈S, ∑ p : Fin 2,
            (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*N i)))*
            ‖∑ j : ZMod M,ZMod.stdAddChar (-(j*k))*
              fordAdditiveCharacter (∑ d,x i p d*
                (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                  Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖ := by
  classical
  dsimp only
  let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
  let K₀ := fun i => ⌈(q i:ℝ)*(3*μ i*(N i:ℝ)^2+ℓ i)⌉
  let K₁ := fun i => ⌊(q i:ℝ)*(3*μ i*(N₁ i:ℝ)^2+ℓ i)⌋
  let l := fun i p => (K₀ i-b i p+1)/2
  let u := fun i p => (K₁ i-b i p)/2
  let L := fun ip : ι × Fin 2 => (l ip.1 ip.2).toNat
  let H := fun ip : ι × Fin 2 => (u ip.1 ip.2-l ip.1 ip.2+1).toNat
  let T := S ×ˢ (Finset.univ : Finset (Fin 2))
  let F := fun i (v : ℤ) =>
    let t := Real.sqrt (((v:ℝ)/(q i:ℝ)-ℓ i)/(3*μ i))
    bourgainQuadraticGauss (q i) (a i) v*
      ((𝐞 ((1:ℝ)/8-2*μ i*t^3):ℂ)/(Real.sqrt (6*μ i*t):ℂ))
  have hdata i (hi : i∈S) (p : Fin 2) :
      0≤l i p ∧ μ i*(q i:ℝ)*(N i:ℝ)^2≤(L (i,p):ℝ) ∧
        (H (i,p):ℝ)≤7*(μ i*(q i:ℝ)*(N i:ℝ)^2) ∧ L (i,p)+H (i,p)≤M+1 :=
    bourgain_cubic_parity_interval_scales (hq i hi) (hN i hi) (hN₁ i hi) (hqN i hi)
      (hμ i hi) (hscale i hi) (hM i hi) p
  obtain ⟨k,hk⟩ := bourgain_cubic_dual_branch_common_fourier T
    (fun ip => q ip.1) (fun ip => N ip.1) L H
    (fun ip => a ip.1) (fun ip => r ip.1) (fun ip => μ ip.1) (fun ip => ℓ ip.1)
    (fun ip => ip.2)
    (fun ip hip => hq ip.1 (Finset.mem_product.mp hip).1)
    (fun ip hip => hN ip.1 (Finset.mem_product.mp hip).1)
    (fun ip hip => hqN ip.1 (Finset.mem_product.mp hip).1)
    (fun ip hip => hμ ip.1 (Finset.mem_product.mp hip).1)
    (fun ip hip => hscale ip.1 (Finset.mem_product.mp hip).1)
    (fun ip hip => har ip.1 (Finset.mem_product.mp hip).1)
    (fun ip hip => (hdata ip.1 (Finset.mem_product.mp hip).1 ip.2).2.1)
    (fun ip hip => (hdata ip.1 (Finset.mem_product.mp hip).1 ip.2).2.2.1)
    (fun ip hip => (hdata ip.1 (Finset.mem_product.mp hip).1 ip.2).2.2.2)
  have hsplit i (hi : i∈S) :
      (q i:ℂ)⁻¹*(∑ v∈Finset.Icc (K₀ i) (K₁ i),F i v) =
        ∑ p : Fin 2,(q i:ℂ)⁻¹*∑ j∈Finset.range (H (i,p)),
          F i (b i p+2*((L (i,p)+j:ℕ):ℤ)) := by
    rw [bourgain_integer_interval_parity_split (K₀ i) (K₁ i) ⌊(q i:ℝ)*ℓ i⌋,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    congr 1
    have he := bourgain_sum_integer_Icc_range (l i p) (u i p) (fun v => F i (b i p+2*v))
    convert he using 1
    · simp only [l,u,b,sub_add_eq_sub_sub]
    · apply Finset.sum_congr rfl
      intro j hj
      congr 2
      dsimp only [L]
      rw [Nat.cast_add,Int.toNat_of_nonneg (hdata i hi p).1]
  have hbound :
      (∑ i∈S,‖(q i:ℂ)⁻¹*∑ v∈Finset.Icc (K₀ i) (K₁ i),F i v‖) ≤
        ∑ ip∈T,‖(q ip.1:ℂ)⁻¹*∑ j∈Finset.range (H ip),
          F ip.1 (b ip.1 ip.2+2*((L ip+j:ℕ):ℤ))‖ := by
    rw [Finset.sum_product]
    apply Finset.sum_le_sum
    intro i hi
    rw [hsplit i hi]
    exact norm_sum_le _ _
  refine ⟨k,hbound.trans ?_⟩
  simpa only [T,Finset.sum_product,F,b,K₀,K₁,Nat.cast_add] using hk

set_option maxHeartbeats 400000 in
                                                                   
                                                                   
                                                                          
                                                                    
theorem bourgain_integer_source_translation
    (f : ℝ → ℝ) (m : ℤ) (N H : ℕ) :
    (∑ n∈Finset.Ioc (m+N) (m+N+H),(𝐞 (f n):ℂ))=
    ∑ n∈Finset.Ioc (N:ℤ) ((N:ℤ)+H),(𝐞 (f ((m:ℝ)+n)):ℂ) := by
  symm
  apply Finset.sum_bij (fun n _ => m+n)
  · intro n hn
    obtain ⟨hn1,hn2⟩ := Finset.mem_Ioc.mp hn
    exact Finset.mem_Ioc.mpr ⟨by omega,by omega⟩
  · intro n _ n' _ he
    omega
  · intro n hn
    refine ⟨n-m,?_,by omega⟩
    obtain ⟨hn1,hn2⟩ := Finset.mem_Ioc.mp hn
    exact Finset.mem_Ioc.mpr ⟨by omega,by omega⟩
  · intro n _
    simp only [Int.cast_add]


set_option maxHeartbeats 400000 in
                                                                        
                                                                            
                                                 
public  theorem bourgain_completed_phase_normalize
    {M : ℕ} (hM : 0 < M) (x : Fin 4 → ℝ) (n : ℤ) (hn : 0 ≤ n) :
    fordAdditiveCharacter (∑ d,x d*
      (![(n:ℝ),(n:ℝ)^2,(n:ℝ)^((3:ℝ)/2),Real.sqrt (n:ℝ)] : Fin 4 → ℝ) d)=
    fordAdditiveCharacter (∑ d,
      (![(n:ℝ),(n:ℝ)^2,(M:ℝ)^2*((n:ℝ)/M)^((3:ℝ)/2),
        (M:ℝ)*Real.sqrt ((n:ℝ)/M)] : Fin 4 → ℝ) d*
      (![Int.fract (x 0),Int.fract (x 1),x 2/Real.sqrt M,x 3/Real.sqrt M] : Fin 4 → ℝ) d) := by
  have hMr : (0:ℝ) < M := Nat.cast_pos.mpr hM
  have hnr : (0:ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMr
  have hsq := Real.sq_sqrt hMr.le
  have hp : (M:ℝ)^((3:ℝ)/2)=(M:ℝ)*Real.sqrt M := by
    rw [show (3:ℝ)/2=1+1/2 by norm_num,Real.rpow_add hMr]
    simp only [Real.rpow_one,Real.sqrt_eq_rpow]
  have hthird : (M:ℝ)^2*((n:ℝ)/M)^((3:ℝ)/2)*(x 2/Real.sqrt M)=
      x 2*(n:ℝ)^((3:ℝ)/2) := by
    rw [Real.div_rpow hnr hMr.le,hp]
    field_simp
    rw [hsq]
    ring
  have hfourth : (M:ℝ)*Real.sqrt ((n:ℝ)/M)*(x 3/Real.sqrt M)=
      x 3*Real.sqrt (n:ℝ) := by
    rw [Real.sqrt_div hnr]
    field_simp
    rw [hsq]
    ring
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,
    Matrix.cons_val_succ,add_zero]
  rw [hthird,hfourth]
  simp only [fordAdditiveCharacter_add]
  have he1 : fordAdditiveCharacter (x 0*(n:ℝ))=
      fordAdditiveCharacter ((n:ℝ)*Int.fract (x 0)) := by
    simpa only [mul_comm] using (sargos_character_integer_fract n (x 0)).symm
  have he2 : fordAdditiveCharacter (x 1*(n:ℝ)^2)=
      fordAdditiveCharacter ((n:ℝ)^2*Int.fract (x 1)) := by
    have hh := sargos_character_integer_fract (n^2) (x 1)
    push_cast at hh
    simpa only [mul_comm] using hh.symm
  change fordAdditiveCharacter (x 0*(n:ℝ))*
      (fordAdditiveCharacter (x 1*(n:ℝ)^2)*
        (fordAdditiveCharacter (x 2*(n:ℝ)^((3:ℝ)/2))*
          fordAdditiveCharacter (x 3*Real.sqrt (n:ℝ))))=
    fordAdditiveCharacter ((n:ℝ)*Int.fract (x 0))*
      (fordAdditiveCharacter ((n:ℝ)^2*Int.fract (x 1))*
        (fordAdditiveCharacter (x 2*(n:ℝ)^((3:ℝ)/2))*
          fordAdditiveCharacter (x 3*Real.sqrt (n:ℝ))))
  rw [he1,he2]


private theorem bourgain_completed_source_sieve {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (M : ℕ) [NeZero M] (ι : Type v) (S : Finset ι)
      (x : ι → Fin 4 → ℝ),
      (∀ i∈S, |x i 2| ≤ Real.sqrt M ∧ |x i 3| ≤ Real.sqrt M) →
      let y := fun i => (![Int.fract (x i 0),Int.fract (x i 1),
        x i 2/Real.sqrt M,x i 3/Real.sqrt M] : Fin 4 → ℝ)
      let a : Fin 4 → ℝ :=
        ![1/(12*(M:ℝ)),1/(12*(M:ℝ)^2),(1/(M:ℝ)^2)/12,(1/(M:ℝ))/12]
      ∀ k : ZMod M,
      (∑ i∈S, ‖∑ j : ZMod M,ZMod.stdAddChar (-(j*k))*
        fordAdditiveCharacter (∑ d,x i d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
        C*(M:ℝ)^((12:ℝ)+ε)*(S.card:ℝ)^10*
          (((S ×ˢ S).filter (fun ij => ∀ d,|y ij.1 d-y ij.2 d| ≤ 2*a d)).card:ℝ) := by
  classical
  obtain ⟨C,hC,hsource⟩ := exists_bourgainSourceCurve_double_sieve.{v} hε
  refine ⟨C,hC,?_⟩
  intro M inst ι S x hx y a k
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hMr : (0:ℝ) < M := Nat.cast_pos.mpr hM
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hsqrt : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMr
  let T : Finset (ULift.{v} (ZMod M)) := Finset.univ
  let m := fun j : ULift.{v} (ZMod M) => (j.down.val:ℤ)+1
  let w := fun j : ULift.{v} (ZMod M) => ZMod.stdAddChar (-(j.down*k))
  have hm j (_hj : j∈T) : 1 ≤ m j ∧ m j ≤ M := by
    dsimp only [m]
    have hj := j.down.val_lt
    constructor <;> omega
  have hmass (q : ℤ) : (((T.filter (fun j => m j=q)).card):ℝ) ≤ 1 := by
    have hh : (T.filter (fun j => m j=q)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro j hj j' hj'
      apply ULift.ext
      apply ZMod.val_injective M
      have hjm := (Finset.mem_filter.mp hj).2
      have hjm' := (Finset.mem_filter.mp hj').2
      dsimp only [m] at hjm hjm'
      omega
    exact_mod_cast hh
  have hy i (hi : i∈S) : y i∈Icc ![0,0,-1,-1] (fun _ => 1) := by
    have h2 : |x i 2/Real.sqrt M| ≤ 1 := by
      rw [abs_div,abs_of_pos hsqrt]
      exact (div_le_one hsqrt).mpr (hx i hi).1
    have h3 : |x i 3/Real.sqrt M| ≤ 1 := by
      rw [abs_div,abs_of_pos hsqrt]
      exact (div_le_one hsqrt).mpr (hx i hi).2
    refine ⟨?_,?_⟩
    · intro d
      fin_cases d
      · exact Int.fract_nonneg _
      · exact Int.fract_nonneg _
      · exact (abs_le.mp h2).1
      · exact (abs_le.mp h3).1
    · intro d
      fin_cases d
      · exact (Int.fract_lt_one _).le
      · exact (Int.fract_lt_one _).le
      · exact (abs_le.mp h2).2
      · exact (abs_le.mp h3).2
  have hη : 1/(M:ℝ)^2∈Icc (1/(M:ℝ)^2) 1 := by
    refine ⟨le_rfl,?_⟩
    exact (div_le_one (by positivity)).mpr (by nlinarith only [hM1])
  have hζ : 1/(M:ℝ)∈Icc (1/(M:ℝ)) 1 := by
    exact ⟨le_rfl,(div_le_one hMr).mpr hM1⟩
  have hh := hsource M (by omega) (1/(M:ℝ)^2) (1/(M:ℝ))
    hη hζ ι (ULift.{v} (ZMod M)) S T w m y 1 (by norm_num) hm
    (fun j _ => (sargos_stdAddChar_norm _).le) hmass hy
  simp only [one_div_one_div,one_pow,mul_one] at hh
  let U := fun j : ULift.{v} (ZMod M) =>
    (![(m j:ℝ),(m j:ℝ)^2,(M:ℝ)^2*((m j:ℝ)/M)^((3:ℝ)/2),
      (M:ℝ)*Real.sqrt ((m j:ℝ)/M)] : Fin 4 → ℝ)
  have he :
      (∑ i∈S, ‖∑ j : ZMod M,ZMod.stdAddChar (-(j*k))*
        fordAdditiveCharacter (∑ d,x i d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)=
      ∑ i∈S, ‖∑ j∈T,w j*fordAdditiveCharacter (∑ d,U j d*y i d)‖ := by
    apply Finset.sum_congr rfl
    intro i _hi
    congr 1
    calc
      _ = ∑ j : ULift.{v} (ZMod M),w j*
          fordAdditiveCharacter (∑ d,x i d*
            (![(m j:ℝ),(m j:ℝ)^2,(m j:ℝ)^((3:ℝ)/2),
              Real.sqrt (m j:ℝ)] : Fin 4 → ℝ) d) := by
        apply Fintype.sum_equiv Equiv.ulift.symm
        intro j
        simp [w,m,Equiv.ulift]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _hj
        congr 1
        exact bourgain_completed_phase_normalize hM (x i) (m j) (by dsimp only [m]; omega)
  rw [he]
  exact hh


private theorem bourgain_actual_dual_source_box
    {M q N : ℕ} [NeZero M] (hq : 0 < q) (hN : 1 ≤ N) (hqN : q ≤ N)
    {μ ℓ : ℝ} (hμ : 0 < μ) (hscale : 1 ≤ μ*(q:ℝ)^2*N)
    (hM : 7*(μ*(q:ℝ)*(N:ℝ)^2) ≤ M) (r : ℤ) (p : Fin 2) :
    let b : ℤ := ⌊(q:ℝ)*ℓ⌋+(p:ℕ)
    let τ := ((b:ℝ)-(q:ℝ)*ℓ)/2
    let K := -2*μ*(Real.sqrt (2/(3*μ*(q:ℝ))))^3
    let x : Fin 4 → ℝ := ![-(r:ℝ)*b/q,-(r:ℝ)/q,K,3*K*τ/2]
    |x 2| ≤ Real.sqrt M ∧ |x 3| ≤ Real.sqrt M := by
  intro b τ K x
  let A := μ*(q:ℝ)*(N:ℝ)^2
  have hqr : (0:ℝ) < q := Nat.cast_pos.mpr hq
  have hNr : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hqNr : (q:ℝ) ≤ N := by exact_mod_cast hqN
  obtain ⟨hA,hK⟩ := bourgain_dual_physical_scale hμ hqr hNr hqNr hscale
  change 1 ≤ A at hA
  change |K|/Real.sqrt A ≤ 2 at hK
  have hA0 : 0 < A := by linarith only [hA]
  have hKA : |K| ≤ 2*Real.sqrt A := (div_le_iff₀ (Real.sqrt_pos.mpr hA0)).mp hK
  have hKA2 : |K|^2 ≤ 4*A := by
    nlinarith [Real.sq_sqrt hA0.le,Real.sqrt_nonneg A,abs_nonneg K]
  have hMr : (0:ℝ) ≤ M := Nat.cast_nonneg M
  have hKM : |K| ≤ Real.sqrt M := by
    change 7*A ≤ M at hM
    nlinarith [Real.sq_sqrt hMr,Real.sqrt_nonneg (M:ℝ),abs_nonneg K]
  have hp0 : (0:ℝ) ≤ p.val := Nat.cast_nonneg _
  have hp1 : (p.val:ℝ) ≤ 1 := by exact_mod_cast (by omega : p.val ≤ 1)
  have ht : |τ| ≤ 1/2 := by
    have hlo := Int.floor_le ((q:ℝ)*ℓ)
    have hhi := Int.lt_floor_add_one ((q:ℝ)*ℓ)
    dsimp only [τ,b]
    rw [Int.cast_add,Int.cast_natCast]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  constructor
  · exact hKM
  · change |3*K*τ/2| ≤ Real.sqrt M
    rw [abs_div,abs_mul,abs_mul]
    norm_num
    have hh := mul_le_mul_of_nonneg_left ht (abs_nonneg K)
    nlinarith [Real.sqrt_nonneg (M:ℝ)]


                                                                      
                                                                         
                                                                          
theorem exists_bourgain_cubic_dual_source_sieve {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (M : ℕ) [NeZero M] (ι : Type v) (S : Finset ι)
      (q N : ι → ℕ) (r : ι → ℤ) (μ ℓ : ι → ℝ),
      (∀ i∈S, 0 < q i ∧ 1 ≤ N i ∧ q i ≤ N i ∧ 0 < μ i ∧
        1 ≤ μ i*(q i:ℝ)^2*N i) →
      (∀ i∈S, 7*(μ i*(q i:ℝ)*(N i:ℝ)^2) ≤ M) →
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let K := fun i => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
      let x := fun i p =>
        (![-(r i:ℝ)*b i p/q i,-(r i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      let V := S ×ˢ (Finset.univ : Finset (Fin 2))
      let y := fun ip : ι × Fin 2 =>
        (![Int.fract (x ip.1 ip.2 0),Int.fract (x ip.1 ip.2 1),
          x ip.1 ip.2 2/Real.sqrt M,x ip.1 ip.2 3/Real.sqrt M] : Fin 4 → ℝ)
      let a : Fin 4 → ℝ :=
        ![1/(12*(M:ℝ)),1/(12*(M:ℝ)^2),(1/(M:ℝ)^2)/12,(1/(M:ℝ))/12]
      ∀ k : ZMod M,
      (∑ i∈S, ∑ p : Fin 2, ‖∑ j : ZMod M,ZMod.stdAddChar (-(j*k))*
        fordAdditiveCharacter (∑ d,x i p d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
        C*(M:ℝ)^((12:ℝ)+ε)*(V.card:ℝ)^10*
          (((V ×ˢ V).filter (fun ij => ∀ d,|y ij.1 d-y ij.2 d| ≤ 2*a d)).card:ℝ) := by
  classical
  obtain ⟨C,hC,hsource⟩ := bourgain_completed_source_sieve.{v} hε
  refine ⟨C,hC,?_⟩
  intro M inst ι S q N r μ ℓ hscale hM b τ K x V y a k
  have hbox ip (hip : ip∈V) :
      |x ip.1 ip.2 2| ≤ Real.sqrt M ∧ |x ip.1 ip.2 3| ≤ Real.sqrt M := by
    have hi := (Finset.mem_product.mp hip).1
    have hd := hscale ip.1 hi
    exact bourgain_actual_dual_source_box hd.1 hd.2.1 hd.2.2.1
      hd.2.2.2.1 hd.2.2.2.2 (hM ip.1 hi) (r ip.1) ip.2
  have hh := hsource M (ι × Fin 2) V (fun ip => x ip.1 ip.2) hbox k
  simpa only [V,Finset.sum_product] using hh


public  theorem bourgain_dual_amplitude_coefficient_le
    {μ q N d : ℝ} (hμ : 0 < μ) (hq : 0 < q) (hN : 0 < N)
    (hd : 0 < d) (hscale : d ≤ μ*q*N) :
    Real.sqrt (2*q)/(q*Real.sqrt (μ*N)) ≤ Real.sqrt (2/d) := by
  have hden : 0 < q^2*(μ*N) := by positivity
  have he : (2*q)/(q^2*(μ*N))=2/(μ*q*N) := by field_simp
  have hroot : Real.sqrt (q^2*(μ*N))=q*Real.sqrt (μ*N) := by
    rw [Real.sqrt_mul (sq_nonneg q),Real.sqrt_sq hq.le]
  rw [←hroot,←Real.sqrt_div (by positivity : 0 ≤ 2*q),he]
  exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (by norm_num) hd hscale)


set_option maxHeartbeats 400000 in
                                                                              
                                                                         
                                                                            
set_option maxHeartbeats 400000 in
private theorem bourgain_canonical_inverse (a r : ℤ) (q : ℕ) (hq : 0 < q)
    (hinv : (q:ℤ) ∣ a*r-1) :
    ∃ R B : ℤ, a*R-B*q=1 ∧
      (R:ℝ)=-(q:ℝ)*Int.fract (-(r:ℝ)/q) := by
  obtain ⟨b,hb⟩ := hinv
  let t : ℤ := ⌊-(r:ℝ)/q⌋
  refine ⟨r+(q:ℤ)*t,b+a*t,?_,?_⟩
  · nlinarith only [hb]
  · have hqr : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    push_cast
    dsimp only [t,Int.fract]
    field_simp
    ring

                                                                     
                                                                      
                                  
theorem bourgain_inverse_coordinate_resonance
    (a a' r r' : ℤ) (q q' : ℕ) (hq : 0 < q) (hq' : 0 < q')
    (har : (q:ℤ) ∣ a*r-1) (har' : (q':ℤ) ∣ a'*r'-1)
    {eta : ℝ}
    (hnear : |Int.fract (-(r:ℝ)/q)-Int.fract (-(r':ℝ)/q')| ≤ eta) :
    ∃ alpha beta gamma delta : ℤ,
      alpha*delta-beta*gamma=1 ∧
      alpha*a+beta*q=a' ∧ gamma*a+delta*q=q' ∧
      |(gamma:ℝ)| ≤ eta*(q:ℝ)*q' ∧
      (eta*(q:ℝ)*q' < 1 → gamma=0 ∧ q=q' ∧ (q:ℤ) ∣ a'-a) := by
  obtain ⟨R,B,hB,hR⟩ := bourgain_canonical_inverse a r q hq har
  obtain ⟨R',B',hB',hR'⟩ := bourgain_canonical_inverse a' r' q' hq' har'
  let alpha := a'*R-B'*(q:ℤ)
  let beta := B'*a-a'*B
  let gamma := (q':ℤ)*R-R'*(q:ℤ)
  let delta := R'*a-(q':ℤ)*B
  have hdet : alpha*delta-beta*gamma=1 := by
    dsimp only [alpha,beta,gamma,delta]
    calc
      _ = (a*R-B*(q:ℤ))*(a'*R'-B'*(q':ℤ)) := by ring
      _ = 1 := by rw [hB,hB']; norm_num
  have ha : alpha*a+beta*q=a' := by
    dsimp only [alpha,beta]
    nlinarith only [congrArg (fun z : ℤ => a'*z) hB]
  have hqmap : gamma*a+delta*q=q' := by
    dsimp only [gamma,delta]
    nlinarith only [congrArg (fun z : ℤ => (q':ℤ)*z) hB]
  have hgamma : |(gamma:ℝ)| ≤ eta*(q:ℝ)*q' := by
    have hge : (gamma:ℝ)=
        -((q:ℝ)*q')*(Int.fract (-(r:ℝ)/q)-Int.fract (-(r':ℝ)/q')) := by
      dsimp only [gamma]
      push_cast
      rw [hR,hR']
      ring
    rw [hge,abs_mul,abs_neg,abs_of_nonneg (by positivity : 0 ≤ (q:ℝ)*q')]
    nlinarith only [mul_le_mul_of_nonneg_left hnear
      (by positivity : 0 ≤ (q:ℝ)*q')]
  refine ⟨alpha,beta,gamma,delta,hdet,ha,hqmap,hgamma,?_⟩
  intro hsmall
  have hg : gamma=0 := by
    have habs : |(gamma:ℝ)| < 1 := hgamma.trans_lt hsmall
    have hz : |gamma| < (1:ℤ) := by exact_mod_cast habs
    have hn := abs_nonneg gamma
    exact abs_eq_zero.mp (by omega : |gamma|=0)
  have hqi : (0:ℤ) < q := by exact_mod_cast hq
  have hqi' : (0:ℤ) < q' := by exact_mod_cast hq'
  rw [hg,zero_mul,zero_add] at hqmap
  rw [hg,mul_zero,sub_zero] at hdet
  have hd : 0 < delta := by nlinarith only [hqi,hqi',hqmap]
  have hal : 0 < alpha := by nlinarith only [hd,hdet]
  have hd1 : delta=1 := by nlinarith only [hd,hal,hdet]
  have hal1 : alpha=1 := by nlinarith only [hdet,hd1]
  refine ⟨hg,?_,?_⟩
  · have he : (q:ℤ)=q' := by simpa only [hd1,one_mul] using hqmap
    exact_mod_cast he
  · refine ⟨beta,?_⟩
    rw [hal1,one_mul] at ha
    nlinarith only [ha]

private theorem bourgain_dual_root_identity {mu q : ℝ} (hm : 0 < mu) (hq : 0 < q) :
    let K := -2*mu*(Real.sqrt (2/(3*mu*q)))^3
    K*Real.sqrt (mu*q^3)=-Real.sqrt (32/27) := by
  intro K
  have ht : 0 ≤ 2/(3*mu*q) := by positivity
  have hroot := Real.sq_sqrt ht
  have hP := Real.sq_sqrt (by positivity : 0 ≤ mu*q^3)
  have hc := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 32/27)
  have hK : K ≤ 0 := by
    dsimp only [K]
    nlinarith only [mul_nonneg hm.le (pow_nonneg (Real.sqrt_nonneg (2/(3*mu*q))) 3)]
  have hKsq : K^2*(mu*q^3)=32/27 := by
    dsimp only [K]
    calc
      _ = 4*mu^2*((Real.sqrt (2/(3*mu*q)))^2)^3*(mu*q^3) := by ring
      _ = 4*mu^2*(2/(3*mu*q))^3*(mu*q^3) := by rw [hroot]
      _ = _ := by field_simp; ring
  have hprod : (K*Real.sqrt (mu*q^3))^2=32/27 := by
    rw [mul_pow,hP]
    exact hKsq
  have hp : K*Real.sqrt (mu*q^3) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hK (Real.sqrt_nonneg _)
  have hc0 := Real.sqrt_nonneg ((32:ℝ)/27)
  nlinarith only [hprod,hc,hp,hc0]

private theorem bourgain_inverse_root_difference {A B c X Y V : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 1 ≤ c)
    (hAV : A ≤ V) (hBV : B ≤ V)
    (hX : X*A=-c) (hY : Y*B=-c) :
    |A^2-B^2| ≤ 2*V^3*|X-Y| := by
  have he : c*(A-B)=A*B*(X-Y) := by
    nlinarith only [congrArg (fun z : ℝ => B*z) hX,
      congrArg (fun z : ℝ => A*z) hY]
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hab : c*|A-B|=A*B*|X-Y| := by
    have hh := congrArg abs he
    simpa only [abs_mul,abs_of_nonneg hc0,abs_of_nonneg hA,abs_of_nonneg hB] using hh
  have hab' : |A-B| ≤ A*B*|X-Y| := by
    nlinarith only [hab,mul_le_mul_of_nonneg_right hc (abs_nonneg (A-B))]
  have hV : 0 ≤ V := hA.trans hAV
  calc
    _ = |A-B| *(A+B) := by
      rw [←abs_of_nonneg (add_nonneg hA hB),←abs_mul]
      congr 1
      ring
    _ ≤ (A*B*|X-Y|)*(A+B) :=
      mul_le_mul_of_nonneg_right hab' (add_nonneg hA hB)
    _ ≤ (V*V*|X-Y|)*(V+V) := by gcongr
    _ = _ := by ring

private theorem bourgain_dual_coefficient_difference
    {mu nu U q : ℝ} (hm : 0 < mu) (hn : 0 < nu) (hq : 0 < q)
    (hmU : mu ≤ U) (hnU : nu ≤ U) :
    let K := fun t => -2*t*(Real.sqrt (2/(3*t*q)))^3
    |mu-nu| ≤ 2*U*Real.sqrt (U*q^3)*|K mu-K nu| := by
  intro K
  have hU : 0 < U := hm.trans_le hmU
  have hc : (1:ℝ) ≤ Real.sqrt (32/27) := by
    have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 32/27)
    have hp := Real.sqrt_nonneg ((32:ℝ)/27)
    nlinarith only [h,hp]
  have hmu := Real.sq_sqrt (by positivity : 0 ≤ mu*q^3)
  have hnu := Real.sq_sqrt (by positivity : 0 ≤ nu*q^3)
  have hupper := Real.sq_sqrt (by positivity : 0 ≤ U*q^3)
  have hb := bourgain_inverse_root_difference
    (Real.sqrt_nonneg (mu*q^3)) (Real.sqrt_nonneg (nu*q^3)) hc
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hmU (by positivity)))
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hnU (by positivity)))
    (bourgain_dual_root_identity hm hq) (bourgain_dual_root_identity hn hq)
  rw [hmu,hnu] at hb
  have hleft : |mu*q^3-nu*q^3|=|mu-nu| *q^3 := by
    rw [←sub_mul,abs_mul,abs_of_pos (pow_pos hq 3)]
  rw [hleft] at hb
  have hright : (Real.sqrt (U*q^3))^3=(U*q^3)*Real.sqrt (U*q^3) := by
    nlinarith only [congrArg (fun z : ℝ => z*Real.sqrt (U*q^3)) hupper]
  rw [hright] at hb
  apply (mul_le_mul_iff_left₀ (pow_pos hq 3)).mp
  convert hb using 1; ring

private theorem bourgain_fourth_derivative_spacing
    (f : ℝ → ℝ) {a b m n lambda : ℝ} (hm : m∈Icc a b) (hn : n∈Icc a b)
    (hf : ∀ x∈Icc a b, ContDiffAt ℝ 4 f x)
    (hfour : ∀ x∈Icc a b, lambda ≤ |iteratedDeriv 4 f x|) :
    lambda*|m-n| ≤ |iteratedDeriv 3 f m-iteratedDeriv 3 f n| := by
  have hh {u v : ℝ} (hu : u∈Icc a b) (hv : v∈Icc a b) (huv : u < v) :
      lambda*|u-v| ≤ |iteratedDeriv 3 f u-iteratedDeriv 3 f v| := by
    have hsub : Icc u v ⊆ Icc a b := fun x hx => ⟨hu.1.trans hx.1,hx.2.trans hv.2⟩
    have hd x (hx : x∈Icc u v) :
        HasDerivAt (iteratedDeriv 3 f) (iteratedDeriv 4 f x) x := by
      have hc := contDiffAt_iteratedDeriv_finite (n:=1) (j:=3) (hf x (hsub hx))
      simpa only [iteratedDeriv_succ] using hc.differentiableAt_one.hasDerivAt
    obtain ⟨x,hx,he⟩ := exists_hasDerivAt_eq_slope
      (iteratedDeriv 3 f) (iteratedDeriv 4 f) huv
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => hd y ⟨hy.1.le,hy.2.le⟩)
    have hb := hfour x (hsub ⟨hx.1.le,hx.2.le⟩)
    rw [he,abs_div,abs_of_pos (sub_pos.mpr huv)] at hb
    have hb' := (le_div_iff₀ (sub_pos.mpr huv)).mp hb
    simpa only [abs_sub_comm u v,abs_of_pos (sub_pos.mpr huv),
      abs_sub_comm (iteratedDeriv 3 f u) (iteratedDeriv 3 f v)] using hb'
  rcases lt_trichotomy m n with h | h | h
  · exact hh hm hn h
  · subst n
    simp
  · simpa only [abs_sub_comm] using hh hn hm h

                                                                       
                                                                          
                                                            
theorem bourgain_upper_triangular_source_spacing
    (f : ℝ → ℝ) {A B lambda U eta zeta : ℝ}
    (hlambda : 0 < lambda) (m n : ℤ)
    (hm : (m:ℝ)∈Icc A B) (hn : (n:ℝ)∈Icc A B)
    (hf : ∀ x∈Icc A B, ContDiffAt ℝ 4 f x)
    (hfour : ∀ x∈Icc A B, lambda ≤ |iteratedDeriv 4 f x|)
    (a a' r r' : ℤ) (q q' : ℕ) (hq : 0 < q) (hq' : 0 < q')
    (har : (q:ℤ)∣a*r-1) (har' : (q':ℤ)∣a'*r'-1)
    (hnear : |Int.fract (-(r:ℝ)/q)-Int.fract (-(r':ℝ)/q')| ≤ eta)
    (hsmall : eta*(q:ℝ)*q' < 1) :
    let mu := iteratedDeriv 3 f m/6
    let nu := iteratedDeriv 3 f n/6
    let K := fun (t d : ℝ) => -2*t*(Real.sqrt (2/(3*t*d)))^3
    0 < mu → mu ≤ U → 0 < nu → nu ≤ U →
    |K mu q-K nu q'| ≤ zeta →
    q=q' ∧ (q:ℤ)∣a'-a ∧
      |(m:ℝ)-n| ≤ (12*U*Real.sqrt (U*(q:ℝ)^3)/lambda)*zeta := by
  intro mu nu K hmu hmuU hnu hnuU hdual
  obtain ⟨alpha,beta,gamma,delta,_hdet,_ha,_hqmap,_hg,hs⟩ :=
    bourgain_inverse_coordinate_resonance a a' r r' q q' hq hq' har har' hnear
  obtain ⟨_hgamma,hqq,hdiv⟩ := hs hsmall
  refine ⟨hqq,hdiv,?_⟩
  subst q'
  have hqr : (0:ℝ) < q := by exact_mod_cast hq
  have hU : 0 < U := hmu.trans_le hmuU
  have hd := bourgain_dual_coefficient_difference hmu hnu hqr hmuU hnuU
  have hdiff : |mu-nu| ≤ 2*U*Real.sqrt (U*(q:ℝ)^3)*zeta := by
    apply hd.trans
    exact mul_le_mul_of_nonneg_left hdual (by positivity)
  have hf3 := bourgain_fourth_derivative_spacing f hm hn hf hfour
  have he : iteratedDeriv 3 f m-iteratedDeriv 3 f n=6*(mu-nu) := by
    dsimp only [mu,nu]
    ring
  rw [he,abs_mul] at hf3
  norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 6)] at hf3
  calc
    _ ≤ (12*U*Real.sqrt (U*(q:ℝ)^3)*zeta)/lambda := by
      apply (le_div_iff₀ hlambda).mpr
      nlinarith only [hf3,hdiff]
    _ = _ := by ring

                                                                   
                                                                    
                                                                     
private theorem bourgain_resonance_derivative_lower {u c t g v w : ℝ}
    (hu : 0 < u) (hc : 1 ≤ |c|) (ht : (1:ℝ)/2 ≤ t)
    (ht' : t ≤ 2) (hg : u ≤ g)
    (hv : |v| ≤ u/8) (hw : |w| ≤ u/8) :
    |c| *u/4 ≤ |v*t+3*c*g*t^2-w| := by
  have hc0 : 0 ≤ |c| := abs_nonneg _
  have hg0 : 0 ≤ g := hu.le.trans hg
  have ht0 : 0 ≤ t := by linarith only [ht]
  have ht2 : (1:ℝ)/4 ≤ t^2 := by nlinarith only [ht]
  have hm : 3*|c| *u/4 ≤ |3*c*g*t^2| := by
    rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg hg0,abs_of_nonneg (sq_nonneg t)]
    rw [abs_of_pos (by norm_num : (0:ℝ) < 3)]
    have hgt : u/4 ≤ g*t^2 := by
      have hh := mul_le_mul hg ht2 (by norm_num : (0:ℝ) ≤ 1/4) hg0
      nlinarith only [hh]
    nlinarith only [mul_le_mul_of_nonneg_left hgt
      (by positivity : 0 ≤ 3*|c|)]
  have he : |v*t-w| ≤ 3*u/8 := by
    calc
      _ ≤ |v*t|+|w| := abs_sub _ _
      _ = |v| *t+|w| := by rw [abs_mul,abs_of_nonneg ht0]
      _ ≤ (u/8)*2+u/8 := by gcongr
      _ = _ := by ring
  have htri : |3*c*g*t^2| ≤ |v*t+3*c*g*t^2-w|+|v*t-w| := by
    calc
      _ = |(v*t+3*c*g*t^2-w)+(-(v*t-w))| := by congr 1; ring
      _ ≤ _ := by simpa only [abs_neg] using
        abs_add_le (v*t+3*c*g*t^2-w) (-(v*t-w))
  have hcu : u ≤ |c| *u := by nlinarith only [mul_le_mul_of_nonneg_right hc hu.le]
  nlinarith only [hm,he,htri,hcu,hu]

private theorem bourgain_resonance_hasDerivAt
    (g gp : ℝ → ℝ) {a b c d x : ℝ}
    (hdet : a*d-b*c=1) (ht : c*x+d ≠ 0)
    (hg : HasDerivAt g (gp x) x)
    (hgy : HasDerivAt g (gp ((a*x+b)/(c*x+d))) ((a*x+b)/(c*x+d))) :
    HasDerivAt (fun z => g ((a*z+b)/(c*z+d))*(c*z+d)^3-g z)
      (gp ((a*x+b)/(c*x+d))*(c*x+d)+
        3*c*g ((a*x+b)/(c*x+d))*(c*x+d)^2-gp x) x := by
  have htd := ((hasDerivAt_id x).const_mul c).add_const d
  have hyd := (((hasDerivAt_id x).const_mul a).add_const b).div htd ht
  have he : (a*(c*x+d)-(a*x+b)*c)/(c*x+d)^2=1/(c*x+d)^2 := by
    congr 1
    nlinarith only [hdet]
  simp only [mul_one,id_eq] at hyd
  rw [he] at hyd
  have hh := ((hgy.comp x hyd).mul (htd.pow 3)).sub hg
  dsimp at hh
  simp only [mul_one] at hh
  change HasDerivAt (fun z => g ((a*z+b)/(c*z+d))*(c*z+d)^3-g z)
    (gp ((a*x+b)/(c*x+d))*(1/(c*x+d)^2)*(c*x+d)^3+
      g ((a*x+b)/(c*x+d))*(3*(c*x+d)^2*c)-gp x) x at hh
  convert hh using 1
  field_simp

                                                                       
                                                                                  
private theorem bourgain_nontriangular_profile_compression
    (g gp : ℝ → ℝ) {a b c d l r u E : ℝ}
    (hlr : l ≤ r) (hu : 0 < u) (hdet : a*d-b*c=1)
    (hc : 1 ≤ |c|)
    (hg : ∀ x∈Icc l r, HasDerivAt g (gp x) x)
    (hgy : ∀ x∈Icc l r,
      HasDerivAt g (gp ((a*x+b)/(c*x+d))) ((a*x+b)/(c*x+d)))
    (ht : ∀ x∈Icc l r, (1:ℝ)/2 ≤ c*x+d ∧ c*x+d ≤ 2)
    (hpos : ∀ x∈Icc l r, u ≤ g ((a*x+b)/(c*x+d)))
    (hgp : ∀ x∈Icc l r, |gp x| ≤ u/8)
    (hgpy : ∀ x∈Icc l r, |gp ((a*x+b)/(c*x+d))| ≤ u/8)
    (hl : |g ((a*l+b)/(c*l+d))*(c*l+d)^3-g l| ≤ E)
    (hr : |g ((a*r+b)/(c*r+d))*(c*r+d)^3-g r| ≤ E) :
    r-l ≤ 8*E/(|c| *u) := by
  have hd : 0 < |c| *u := mul_pos (by linarith only [hc]) hu
  have hE : 0 ≤ E := (abs_nonneg _).trans hl
  rcases hlr.eq_or_lt with he | hlt
  · subst r
    simp only [sub_self]
    positivity
  let F := fun x => g ((a*x+b)/(c*x+d))*(c*x+d)^3-g x
  let F' := fun x => gp ((a*x+b)/(c*x+d))*(c*x+d)+
      3*c*g ((a*x+b)/(c*x+d))*(c*x+d)^2-gp x
  have hder x (hx : x∈Icc l r) : HasDerivAt F (F' x) x :=
    bourgain_resonance_hasDerivAt g gp hdet (by linarith only [(ht x hx).1])
      (hg x hx) (hgy x hx)
  obtain ⟨x,hx,he⟩ := exists_hasDerivAt_eq_slope F F' hlt
    (fun x hx => (hder x hx).continuousAt.continuousWithinAt)
    (fun x hx => hder x ⟨hx.1.le,hx.2.le⟩)
  have hxi : x∈Icc l r := ⟨hx.1.le,hx.2.le⟩
  have hb := bourgain_resonance_derivative_lower hu hc (ht x hxi).1 (ht x hxi).2
    (hpos x hxi) (hgpy x hxi) (hgp x hxi)
  change |c| *u/4 ≤ |F' x| at hb
  rw [he,abs_div,abs_of_pos (sub_pos.mpr hlt)] at hb
  have hdiff : |F r-F l| ≤ 2*E := by
    calc
      _ ≤ |F r|+|F l| := abs_sub _ _
      _ ≤ _ := by linarith only [hr,hl]
  have hs := (le_div_iff₀ (sub_pos.mpr hlt)).mp hb
  apply (le_div_iff₀ hd).mpr
  nlinarith only [hs,hdiff]

                                                                            
                                                                                   
private theorem bourgain_curvature_profile
    (f : ℝ → ℝ) {A B L : ℝ} (hL : 0 < L)
    (hf : ∀ x∈Ioo A B, ContDiffAt ℝ 4 f x)
    (hthree : ∀ x∈Ioo A B, L ≤ iteratedDeriv 3 f x)
    (hfour : ∀ x∈Ioo A B, |iteratedDeriv 4 f x| ≤ L^2/16) :
    let I := Ioo A B
    let h := fun x => iteratedDeriv 2 f x/2
    let c := Function.invFunOn h I
    let g := fun v => iteratedDeriv 3 f (c v)/6
    let gp := fun v => iteratedDeriv 4 f (c v)/(3*iteratedDeriv 3 f (c v))
    (∀ x∈I, c (h x)=x) ∧
    ∀ v∈h '' I, h (c v)=v ∧ c v∈I ∧ HasDerivAt g (gp v) v ∧
      L/6 ≤ g v ∧ |gp v| ≤ (L/6)/8 := by
  intro I h c g gp
  have hd x (hx : x∈I) : HasDerivAt h (iteratedDeriv 3 f x/2) x := by
    have hc := contDiffAt_iteratedDeriv_finite (n:=2) (j:=2) (hf x hx)
    simpa only [h,iteratedDeriv_succ] using
      (hc.differentiableAt (by norm_num)).hasDerivAt.div_const 2
  have hs : StrictMonoOn h I := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo A B)
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      have hxi : x∈I := by simpa only [I,interior_Ioo] using hx
      rw [(hd x hxi).deriv]
      have hh := hthree x hxi
      linarith only [hh,hL]
  have hleft x (hx : x∈I) : c (h x)=x :=
    hs.injOn.leftInvOn_invFunOn hx
  have hcder v (hv : v∈h '' I) :
      HasDerivAt c (iteratedDeriv 3 f (c v)/2)⁻¹ v := by
    obtain ⟨x,hx,rfl⟩ := hv
    rw [hleft x hx]
    have hc := (contDiffAt_iteratedDeriv_finite (n:=2) (j:=2) (hf x hx)).div_const 2
    have hsd := hc.hasStrictDerivAt (by norm_num)
    change HasStrictDerivAt h (deriv h x) x at hsd
    rw [(hd x hx).deriv] at hsd
    have hi : HasStrictDerivAt c (iteratedDeriv 3 f x/2)⁻¹ (h x) := by
      apply hsd.to_local_left_inverse (by have hh := hthree x hx; linarith only [hh,hL])
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      exact hleft y hy
    exact hi.hasDerivAt
  refine ⟨hleft,?_⟩
  intro v hv
  have hvI : c v∈I := Function.invFunOn_mem hv
  have he : h (c v)=v := Function.invFunOn_eq hv
  have hp : 0 < iteratedDeriv 3 f (c v) := hL.trans_le (hthree _ hvI)
  have hgder : HasDerivAt g (gp v) v := by
    have hc := contDiffAt_iteratedDeriv_finite (n:=1) (j:=3) (hf _ hvI)
    have hh := (hc.differentiableAt_one.hasDerivAt.div_const 6).comp v (hcder v hv)
    simp only [←iteratedDeriv_succ] at hh
    convert hh using 1
    · funext t
      dsimp only [g,Function.comp_apply]
    · dsimp only [gp]
      field_simp
      ring
  refine ⟨he,hvI,hgder,?_,?_⟩
  · dsimp only [g]
    linarith only [hthree _ hvI]
  · dsimp only [gp]
    rw [abs_div,abs_of_pos (by positivity : 0 < 3*iteratedDeriv 3 f (c v))]
    apply (div_le_iff₀ (by positivity : 0 < 3*iteratedDeriv 3 f (c v))).mpr
    have hh := mul_le_mul_of_nonneg_left (hthree _ hvI) hL.le
    nlinarith only [hh,hfour _ hvI]

private theorem bourgain_paired_resonance_hasDerivAt
    (g gp j jp : ℝ → ℝ) {a b c d x : ℝ}
    (hdet : a*d-b*c=1) (ht : c*x+d ≠ 0)
    (hg : HasDerivAt g (gp x) x)
    (hgy : HasDerivAt j (jp ((a*x+b)/(c*x+d))) ((a*x+b)/(c*x+d))) :
    HasDerivAt (fun z => j ((a*z+b)/(c*z+d))*(c*z+d)^3-g z)
      (jp ((a*x+b)/(c*x+d))*(c*x+d)+
        3*c*j ((a*x+b)/(c*x+d))*(c*x+d)^2-gp x) x := by
  have htd := ((hasDerivAt_id x).const_mul c).add_const d
  have hyd := (((hasDerivAt_id x).const_mul a).add_const b).div htd ht
  have he : (a*(c*x+d)-(a*x+b)*c)/(c*x+d)^2=1/(c*x+d)^2 := by
    congr 1
    nlinarith only [hdet]
  simp only [mul_one,id_eq] at hyd
  rw [he] at hyd
  have hh := ((hgy.comp x hyd).mul (htd.pow 3)).sub hg
  dsimp at hh
  simp only [mul_one] at hh
  change HasDerivAt (fun z => j ((a*z+b)/(c*z+d))*(c*z+d)^3-g z)
    (jp ((a*x+b)/(c*x+d))*(1/(c*x+d)^2)*(c*x+d)^3+
      j ((a*x+b)/(c*x+d))*(3*(c*x+d)^2*c)-gp x) x at hh
  convert hh using 1
  field_simp

                                                                       
                                                                                  
private theorem bourgain_paired_nontriangular_profile_compression
    (g gp j jp : ℝ → ℝ) {a b c d l r u E : ℝ}
    (hlr : l ≤ r) (hu : 0 < u) (hdet : a*d-b*c=1)
    (hc : 1 ≤ |c|)
    (hg : ∀ x∈Icc l r, HasDerivAt g (gp x) x)
    (hgy : ∀ x∈Icc l r,
      HasDerivAt j (jp ((a*x+b)/(c*x+d))) ((a*x+b)/(c*x+d)))
    (ht : ∀ x∈Icc l r, (1:ℝ)/2 ≤ c*x+d ∧ c*x+d ≤ 2)
    (hpos : ∀ x∈Icc l r, u ≤ j ((a*x+b)/(c*x+d)))
    (hgp : ∀ x∈Icc l r, |gp x| ≤ u/8)
    (hgpy : ∀ x∈Icc l r, |jp ((a*x+b)/(c*x+d))| ≤ u/8)
    (hl : |j ((a*l+b)/(c*l+d))*(c*l+d)^3-g l| ≤ E)
    (hr : |j ((a*r+b)/(c*r+d))*(c*r+d)^3-g r| ≤ E) :
    r-l ≤ 8*E/(|c| *u) := by
  have hd : 0 < |c| *u := mul_pos (by linarith only [hc]) hu
  have hE : 0 ≤ E := (abs_nonneg _).trans hl
  rcases hlr.eq_or_lt with he | hlt
  · subst r
    simp only [sub_self]
    positivity
  let F := fun x => j ((a*x+b)/(c*x+d))*(c*x+d)^3-g x
  let F' := fun x => jp ((a*x+b)/(c*x+d))*(c*x+d)+
      3*c*j ((a*x+b)/(c*x+d))*(c*x+d)^2-gp x
  have hder x (hx : x∈Icc l r) : HasDerivAt F (F' x) x :=
    bourgain_paired_resonance_hasDerivAt g gp j jp hdet (by linarith only [(ht x hx).1])
      (hg x hx) (hgy x hx)
  obtain ⟨x,hx,he⟩ := exists_hasDerivAt_eq_slope F F' hlt
    (fun x hx => (hder x hx).continuousAt.continuousWithinAt)
    (fun x hx => hder x ⟨hx.1.le,hx.2.le⟩)
  have hxi : x∈Icc l r := ⟨hx.1.le,hx.2.le⟩
  have hb := bourgain_resonance_derivative_lower hu hc (ht x hxi).1 (ht x hxi).2
    (hpos x hxi) (hgpy x hxi) (hgp x hxi)
  change |c| *u/4 ≤ |F' x| at hb
  rw [he,abs_div,abs_of_pos (sub_pos.mpr hlt)] at hb
  have hdiff : |F r-F l| ≤ 2*E := by
    calc
      _ ≤ |F r|+|F l| := abs_sub _ _
      _ ≤ _ := by linarith only [hr,hl]
  have hs := (le_div_iff₀ (sub_pos.mpr hlt)).mp hb
  apply (le_div_iff₀ hd).mpr
  nlinarith only [hs,hdiff]

                                                                                       
                                                                         
                                                                           
                                                     
theorem bourgain_paired_C4_nontriangular_resonance_compression
    (f f₁ : ℝ → ℝ) {A B A₁ B₁ L E xl xr yl yr : ℝ}
    (a b c d : ℤ) (hdet : a*d-b*c=1) (hc : c ≠ 0) (hL : 0 < L)
    (hf : ∀ x∈Ioo A B, ContDiffAt ℝ 4 f x)
    (hthree : ∀ x∈Ioo A B, L ≤ iteratedDeriv 3 f x)
    (hfour : ∀ x∈Ioo A B, |iteratedDeriv 4 f x| ≤ L^2/16)
    (hf₁ : ∀ x∈Ioo A₁ B₁, ContDiffAt ℝ 4 f₁ x)
    (hthree₁ : ∀ x∈Ioo A₁ B₁, L ≤ iteratedDeriv 3 f₁ x)
    (hfour₁ : ∀ x∈Ioo A₁ B₁, |iteratedDeriv 4 f₁ x| ≤ L^2/16)
    (hxl : xl∈Ioo A B) (hxr : xr∈Ioo A B)
    (hyl : yl∈Ioo A₁ B₁) (hyr : yr∈Ioo A₁ B₁) :
    let h := fun x => iteratedDeriv 2 f x/2
    let h₁ := fun x => iteratedDeriv 2 f₁ x/2
    let t := fun v => (c:ℝ)*v+d
    h xl ≤ h xr →
    ((a:ℝ)*h xl+b)/t (h xl)=h₁ yl →
    ((a:ℝ)*h xr+b)/t (h xr)=h₁ yr →
    ((1:ℝ)/2 ≤ t (h xl) ∧ t (h xl) ≤ 2) →
    ((1:ℝ)/2 ≤ t (h xr) ∧ t (h xr) ≤ 2) →
    |(iteratedDeriv 3 f₁ yl/6)*t (h xl)^3-iteratedDeriv 3 f xl/6| ≤ E →
    |(iteratedDeriv 3 f₁ yr/6)*t (h xr)^3-iteratedDeriv 3 f xr/6| ≤ E →
    h xr-h xl ≤ 48*E/(|(c:ℝ)| *L) := by
  intro h h₁ t hlr hmapl hmapr htl htr hel her
  let I := Ioo A B
  let inv := Function.invFunOn h I
  let g := fun v => iteratedDeriv 3 f (inv v)/6
  let gp := fun v => iteratedDeriv 4 f (inv v)/(3*iteratedDeriv 3 f (inv v))
  have hp := bourgain_curvature_profile f hL hf hthree hfour
  change (∀ x∈I, inv (h x)=x) ∧
    ∀ v∈h '' I, h (inv v)=v ∧ inv v∈I ∧ HasDerivAt g (gp v) v ∧
      L/6 ≤ g v ∧ |gp v| ≤ (L/6)/8 at hp
  let I₁ := Ioo A₁ B₁
  let inv₁ := Function.invFunOn h₁ I₁
  let g₁ := fun v => iteratedDeriv 3 f₁ (inv₁ v)/6
  let gp₁ := fun v => iteratedDeriv 4 f₁ (inv₁ v)/(3*iteratedDeriv 3 f₁ (inv₁ v))
  have hp₁ := bourgain_curvature_profile f₁ hL hf₁ hthree₁ hfour₁
  change (∀ x∈I₁, inv₁ (h₁ x)=x) ∧
    ∀ v∈h₁ '' I₁, h₁ (inv₁ v)=v ∧ inv₁ v∈I₁ ∧ HasDerivAt g₁ (gp₁ v) v ∧
      L/6 ≤ g₁ v ∧ |gp₁ v| ≤ (L/6)/8 at hp₁
  have hhcont₁ : ContinuousOn h₁ I₁ := by
    intro x hx
    exact ((contDiffAt_iteratedDeriv_finite (n:=2) (j:=2)
      (hf₁ x hx)).continuousAt.div_const 2).continuousWithinAt
  have himage₁ : (h₁ '' I₁).OrdConnected :=
    (isPreconnected_Ioo.image h₁ hhcont₁).ordConnected
  have hhcont : ContinuousOn h I := by
    intro x hx
    exact ((contDiffAt_iteratedDeriv_finite (n:=2) (j:=2)
      (hf x hx)).continuousAt.div_const 2).continuousWithinAt
  have himage : (h '' I).OrdConnected :=
    (isPreconnected_Ioo.image h hhcont).ordConnected
  have hxin : ∀ x∈Icc (h xl) (h xr), x∈h '' I :=
    fun x hx => himage.out ⟨xl,hxl,rfl⟩ ⟨xr,hxr,rfl⟩ hx
  have ht x (hx : x∈Icc (h xl) (h xr)) : (1:ℝ)/2 ≤ t x ∧ t x ≤ 2 := by
    rcases le_total 0 (c:ℝ) with hcpos | hcneg
    · have hlo := mul_le_mul_of_nonneg_left hx.1 hcpos
      have hhi := mul_le_mul_of_nonneg_left hx.2 hcpos
      dsimp only [t] at *
      constructor <;> linarith only [htl.1,htr.2,hlo,hhi]
    · have hlo := mul_le_mul_of_nonpos_left hx.1 hcneg
      have hhi := mul_le_mul_of_nonpos_left hx.2 hcneg
      dsimp only [t] at *
      constructor <;> linarith only [htl.2,htr.1,hlo,hhi]
  let y := fun x => ((a:ℝ)*x+b)/t x
  have hdetR : (a:ℝ)*d-(b:ℝ)*c=1 := by exact_mod_cast hdet
  have hyder x (hx : x∈Icc (h xl) (h xr)) : HasDerivAt y (1/(t x)^2) x := by
    have hd := (((hasDerivAt_id x).const_mul (a:ℝ)).add_const (b:ℝ)).div
      (((hasDerivAt_id x).const_mul (c:ℝ)).add_const (d:ℝ))
      (by change t x ≠ 0; linarith only [(ht x hx).1])
    simp only [mul_one,id_eq] at hd
    convert hd using 1
    congr 1
    nlinarith only [hdetR]
  have hymono : MonotoneOn y (Icc (h xl) (h xr)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun x hx => (hyder x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hyder x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hyder x (interior_subset hx)).deriv]
      positivity
  have hyin x (hx : x∈Icc (h xl) (h xr)) : y x∈h₁ '' I₁ := by
    apply himage₁.out ⟨yl,hyl,rfl⟩ ⟨yr,hyr,rfl⟩
    constructor
    · rw [←hmapl]
      exact hymono ⟨le_rfl,hlr⟩ hx hx.1
    · rw [←hmapr]
      exact hymono hx ⟨hlr,le_rfl⟩ hx.2
  have hcabs : (1:ℝ) ≤ |(c:ℝ)| := by exact_mod_cast Int.one_le_abs hc
  have hleft : |g₁ (y (h xl))*t (h xl)^3-g (h xl)| ≤ E := by
    dsimp only [g,g₁,y]
    rw [hmapl,hp₁.1 yl hyl,hp.1 xl hxl]
    exact hel
  have hright : |g₁ (y (h xr))*t (h xr)^3-g (h xr)| ≤ E := by
    dsimp only [g,g₁,y]
    rw [hmapr,hp₁.1 yr hyr,hp.1 xr hxr]
    exact her
  have hb := bourgain_paired_nontriangular_profile_compression g gp g₁ gp₁ hlr
    (by positivity : 0 < L/6) hdetR hcabs
    (fun x hx => (hp.2 x (hxin x hx)).2.2.1)
    (fun x hx => (hp₁.2 _ (hyin x hx)).2.2.1) ht
    (fun x hx => (hp₁.2 _ (hyin x hx)).2.2.2.1)
    (fun x hx => (hp.2 x (hxin x hx)).2.2.2.2)
    (fun x hx => (hp₁.2 _ (hyin x hx)).2.2.2.2) hleft hright
  convert hb using 1
  ring

                                                                        
                                                                         
                                                                           
                                                     
theorem bourgain_C4_nontriangular_resonance_compression
    (f : ℝ → ℝ) {A B L E xl xr yl yr : ℝ}
    (a b c d : ℤ) (hdet : a*d-b*c=1) (hc : c ≠ 0) (hL : 0 < L)
    (hf : ∀ x∈Ioo A B, ContDiffAt ℝ 4 f x)
    (hthree : ∀ x∈Ioo A B, L ≤ iteratedDeriv 3 f x)
    (hfour : ∀ x∈Ioo A B, |iteratedDeriv 4 f x| ≤ L^2/16)
    (hxl : xl∈Ioo A B) (hxr : xr∈Ioo A B)
    (hyl : yl∈Ioo A B) (hyr : yr∈Ioo A B) :
    let h := fun x => iteratedDeriv 2 f x/2
    let t := fun v => (c:ℝ)*v+d
    h xl ≤ h xr →
    ((a:ℝ)*h xl+b)/t (h xl)=h yl →
    ((a:ℝ)*h xr+b)/t (h xr)=h yr →
    ((1:ℝ)/2 ≤ t (h xl) ∧ t (h xl) ≤ 2) →
    ((1:ℝ)/2 ≤ t (h xr) ∧ t (h xr) ≤ 2) →
    |(iteratedDeriv 3 f yl/6)*t (h xl)^3-iteratedDeriv 3 f xl/6| ≤ E →
    |(iteratedDeriv 3 f yr/6)*t (h xr)^3-iteratedDeriv 3 f xr/6| ≤ E →
    h xr-h xl ≤ 48*E/(|(c:ℝ)| *L) := by
  intro h t hlr hmapl hmapr htl htr hel her
  let I := Ioo A B
  let inv := Function.invFunOn h I
  let g := fun v => iteratedDeriv 3 f (inv v)/6
  let gp := fun v => iteratedDeriv 4 f (inv v)/(3*iteratedDeriv 3 f (inv v))
  have hp := bourgain_curvature_profile f hL hf hthree hfour
  change (∀ x∈I, inv (h x)=x) ∧
    ∀ v∈h '' I, h (inv v)=v ∧ inv v∈I ∧ HasDerivAt g (gp v) v ∧
      L/6 ≤ g v ∧ |gp v| ≤ (L/6)/8 at hp
  have hhcont : ContinuousOn h I := by
    intro x hx
    exact ((contDiffAt_iteratedDeriv_finite (n:=2) (j:=2)
      (hf x hx)).continuousAt.div_const 2).continuousWithinAt
  have himage : (h '' I).OrdConnected :=
    (isPreconnected_Ioo.image h hhcont).ordConnected
  have hxin : ∀ x∈Icc (h xl) (h xr), x∈h '' I :=
    fun x hx => himage.out ⟨xl,hxl,rfl⟩ ⟨xr,hxr,rfl⟩ hx
  have ht x (hx : x∈Icc (h xl) (h xr)) : (1:ℝ)/2 ≤ t x ∧ t x ≤ 2 := by
    rcases le_total 0 (c:ℝ) with hcpos | hcneg
    · have hlo := mul_le_mul_of_nonneg_left hx.1 hcpos
      have hhi := mul_le_mul_of_nonneg_left hx.2 hcpos
      dsimp only [t] at *
      constructor <;> linarith only [htl.1,htr.2,hlo,hhi]
    · have hlo := mul_le_mul_of_nonpos_left hx.1 hcneg
      have hhi := mul_le_mul_of_nonpos_left hx.2 hcneg
      dsimp only [t] at *
      constructor <;> linarith only [htl.2,htr.1,hlo,hhi]
  let y := fun x => ((a:ℝ)*x+b)/t x
  have hdetR : (a:ℝ)*d-(b:ℝ)*c=1 := by exact_mod_cast hdet
  have hyder x (hx : x∈Icc (h xl) (h xr)) : HasDerivAt y (1/(t x)^2) x := by
    have hd := (((hasDerivAt_id x).const_mul (a:ℝ)).add_const (b:ℝ)).div
      (((hasDerivAt_id x).const_mul (c:ℝ)).add_const (d:ℝ))
      (by change t x ≠ 0; linarith only [(ht x hx).1])
    simp only [mul_one,id_eq] at hd
    convert hd using 1
    congr 1
    nlinarith only [hdetR]
  have hymono : MonotoneOn y (Icc (h xl) (h xr)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun x hx => (hyder x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hyder x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hyder x (interior_subset hx)).deriv]
      positivity
  have hyin x (hx : x∈Icc (h xl) (h xr)) : y x∈h '' I := by
    apply himage.out ⟨yl,hyl,rfl⟩ ⟨yr,hyr,rfl⟩
    constructor
    · rw [←hmapl]
      exact hymono ⟨le_rfl,hlr⟩ hx hx.1
    · rw [←hmapr]
      exact hymono hx ⟨hlr,le_rfl⟩ hx.2
  have hcabs : (1:ℝ) ≤ |(c:ℝ)| := by exact_mod_cast Int.one_le_abs hc
  have hleft : |g (y (h xl))*t (h xl)^3-g (h xl)| ≤ E := by
    dsimp only [g,y]
    rw [hmapl,hp.1 yl hyl,hp.1 xl hxl]
    exact hel
  have hright : |g (y (h xr))*t (h xr)^3-g (h xr)| ≤ E := by
    dsimp only [g,y]
    rw [hmapr,hp.1 yr hyr,hp.1 xr hxr]
    exact her
  have hb := bourgain_nontriangular_profile_compression g gp hlr
    (by positivity : 0 < L/6) hdetR hcabs
    (fun x hx => (hp.2 x (hxin x hx)).2.2.1)
    (fun x hx => (hp.2 _ (hyin x hx)).2.2.1) ht
    (fun x hx => (hp.2 _ (hyin x hx)).2.2.2.1)
    (fun x hx => (hp.2 x (hxin x hx)).2.2.2.2)
    (fun x hx => (hp.2 _ (hyin x hx)).2.2.2.2) hleft hright
  convert hb using 1
  ring

private theorem bourgain_bounded_denominator_separation
    {a b q r : ℤ} {Q : ℝ} (hq : 0 < q) (hr : 0 < r)
    (hqQ : (q:ℝ) ≤ Q) (hrQ : (r:ℝ) ≤ Q)
    (hne : (a:ℝ)/q ≠ (b:ℝ)/r) :
    1 ≤ |Q^2*((a:ℝ)/q-(b:ℝ)/r)| := by
  have hqr : 0 < (q:ℝ) := by exact_mod_cast hq
  have hrr : 0 < (r:ℝ) := by exact_mod_cast hr
  have hQ : 0 < Q := hqr.trans_le hqQ
  have hn : a*r-b*q ≠ 0 := by
    intro he
    apply hne
    apply (div_eq_div_iff hqr.ne' hrr.ne').mpr
    exact_mod_cast (sub_eq_zero.mp he)
  have hd : (1:ℝ) ≤ |(a:ℝ)*r-(b:ℝ)*q| := by exact_mod_cast Int.one_le_abs hn
  have he : (a:ℝ)/q-(b:ℝ)/r=((a:ℝ)*r-(b:ℝ)*q)/((q:ℝ)*r) := by
    field_simp
  rw [abs_mul,abs_of_nonneg (sq_nonneg Q),he,abs_div,
    abs_of_pos (mul_pos hqr hrr)]
  have hm : (q:ℝ)*r ≤ Q^2 := by
    nlinarith only [mul_le_mul hqQ hrQ hrr.le hQ.le]
  rw [←mul_div_assoc]
  apply (le_div_iff₀ (mul_pos hqr hrr)).mpr
  nlinarith only [hm,mul_le_mul_of_nonneg_left hd (sq_nonneg Q)]

                                                                        
                                                                       
                                                            
theorem bourgain_C4_fixed_matrix_resonance_count
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ℝ → ℝ) (x y : ι → ℝ) (p : ι → ℤ) (q : ι → ℕ)
    (Q Bmul : ℕ) {A B L E : ℝ}
    (a b c d : ℤ) (hdet : a*d-b*c=1) (hc : c ≠ 0)
    (hL : 0 < L) (hE : 0 ≤ E)
    (hf : ∀ z∈Ioo A B, ContDiffAt ℝ 4 f z)
    (hthree : ∀ z∈Ioo A B, L ≤ iteratedDeriv 3 f z)
    (hfour : ∀ z∈Ioo A B, |iteratedDeriv 4 f z| ≤ L^2/16)
    (hx : ∀ i∈S, x i∈Ioo A B) (hy : ∀ i∈S, y i∈Ioo A B)
    (hq : ∀ i∈S, 0 < q i ∧ q i ≤ Q) :
    let h := fun z => iteratedDeriv 2 f z/2
    let t := fun v => (c:ℝ)*v+d
    (∀ i∈S, h (x i)=(p i:ℝ)/q i) →
    (∀ i∈S, ((a:ℝ)*h (x i)+b)/t (h (x i))=h (y i)) →
    (∀ i∈S, (1:ℝ)/2 ≤ t (h (x i)) ∧ t (h (x i)) ≤ 2) →
    (∀ i∈S, |(iteratedDeriv 3 f (y i)/6)*t (h (x i))^3-
      iteratedDeriv 3 f (x i)/6| ≤ E) →
    (∀ v : ℝ, (S.filter (fun i => h (x i)=v)).card ≤ Bmul) →
    (S.card:ℝ) ≤ Bmul*(1+48*E*(Q:ℝ)^2/(|(c:ℝ)| *L)) := by
  classical
  intro h t hlevel hmap ht hres hmul
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp only [Finset.card_empty,Nat.cast_zero]
    positivity
  have hQ : (0:ℝ) < Q := by
    obtain ⟨i,hi⟩ := hS
    exact_mod_cast (hq i hi).1.trans_le (hq i hi).2
  let level := fun i => (Q:ℝ)^2*h (x i)
  let W := S.image level
  have hW : W.Nonempty := hS.image level
  obtain ⟨il,hil,hel⟩ := Finset.mem_image.mp (W.min'_mem hW)
  obtain ⟨ir,hir,her⟩ := Finset.mem_image.mp (W.max'_mem hW)
  have hlo i (hi : i∈S) : level il ≤ level i := by
    rw [hel]
    exact W.min'_le _ (Finset.mem_image_of_mem level hi)
  have hhi i (hi : i∈S) : level i ≤ level ir := by
    rw [her]
    exact W.le_max' _ (Finset.mem_image_of_mem level hi)
  have hlr : h (x il) ≤ h (x ir) :=
    (mul_le_mul_iff_right₀ (sq_pos_of_pos hQ)).mp (hlo ir hir)
  have hwidth := bourgain_C4_nontriangular_resonance_compression f a b c d
    hdet hc hL hf hthree hfour (hx il hil) (hx ir hir) (hy il hil) (hy ir hir)
    hlr (hmap il hil) (hmap ir hir) (ht il hil) (ht ir hir)
    (hres il hil) (hres ir hir)
  change h (x ir)-h (x il) ≤ 48*E/(|(c:ℝ)| *L) at hwidth
  have hsep : ∀ u∈W, ∀ v∈W, u ≠ v → 1 ≤ |u-v| := by
    intro u hu v hv huv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hv
    have hne : (p i:ℝ)/q i ≠ (p j:ℝ)/q j := by
      intro he
      apply huv
      dsimp only [level]
      rw [hlevel i hi,hlevel j hj,he]
    have hb := bourgain_bounded_denominator_separation
      (a:=p i) (b:=p j) (q:=(q i:ℤ)) (r:=(q j:ℤ)) (Q:=(Q:ℝ))
      (by exact_mod_cast (hq i hi).1) (by exact_mod_cast (hq j hj).1)
      (by exact_mod_cast (hq i hi).2) (by exact_mod_cast (hq j hj).2)
      (by simpa only [Int.cast_natCast] using hne)
    simp only [Int.cast_natCast] at hb
    dsimp only [level]
    rw [hlevel i hi,hlevel j hj,←mul_sub]
    exact hb
  have hWbound := oneSeparated_card_cast_le_interval_length_add_one W hsep
    (sub_nonneg.mpr (hlo ir hir)) (by
      intro v hv
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
      exact ⟨hlo i hi,hhi i hi⟩)
  have hWfinal : (W.card:ℝ) ≤ 1+48*E*(Q:ℝ)^2/(|(c:ℝ)| *L) := by
    have hh := mul_le_mul_of_nonneg_left hwidth (sq_nonneg (Q:ℝ))
    dsimp only [level] at hWbound
    calc
      _ ≤ (Q:ℝ)^2*(h (x ir)-h (x il))+1 := by nlinarith only [hWbound]
      _ ≤ (Q:ℝ)^2*(48*E/(|(c:ℝ)| *L))+1 := by linarith only [hh]
      _ = _ := by ring
  have hcard : (S.card:ℝ)=∑ v∈W,((S.filter (fun i => level i=v)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise
      (fun i hi => Finset.mem_image_of_mem level hi)
  have hfiber v : ((S.filter (fun i => level i=v)).card:ℝ) ≤ Bmul := by
    have he : S.filter (fun i => level i=v)=
        S.filter (fun i => h (x i)=v/(Q:ℝ)^2) := by
      ext i
      simp only [Finset.mem_filter]
      dsimp only [level]
      rw [eq_div_iff (sq_pos_of_pos hQ).ne',mul_comm]
    rw [he]
    exact Nat.cast_le.mpr (hmul (v/(Q:ℝ)^2))
  calc
    _ = _ := hcard
    _ ≤ ∑ v∈W,(Bmul:ℝ) := Finset.sum_le_sum (fun v _ => hfiber v)
    _ = (Bmul:ℝ)*W.card := by simp [mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hWfinal (Nat.cast_nonneg _)

theorem bourgain_dual_variable_denominator_difference
    {mu nu U q r Q zeta : ℝ}
    (hm : 0 < mu) (hn : 0 < nu) (hq : 0 < q) (hr : 0 < r)
    (hmU : mu ≤ U) (hnU : nu ≤ U) (hqQ : q ≤ Q) (hrQ : r ≤ Q)
    (hQq : Q ≤ 2*q)
    (hdual : |(-2*mu*(Real.sqrt (2/(3*mu*q)))^3)-
      (-2*nu*(Real.sqrt (2/(3*nu*r)))^3)| ≤ zeta) :
    |nu*(r/q)^3-mu| ≤ 16*U*Real.sqrt (U*Q^3)*zeta := by
  have hU : 0 < U := hm.trans_le hmU
  have hQ : 0 < Q := hq.trans_le hqQ
  have hzeta : 0 ≤ zeta := (abs_nonneg _).trans hdual
  have hc : (1:ℝ) ≤ Real.sqrt (32/27) := by
    have hh := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 32/27)
    have hp := Real.sqrt_nonneg ((32:ℝ)/27)
    nlinarith only [hh,hp]
  have hb := bourgain_inverse_root_difference (V:=Real.sqrt (U*Q^3))
    (Real.sqrt_nonneg (mu*q^3)) (Real.sqrt_nonneg (nu*r^3)) hc
    (Real.sqrt_le_sqrt (by gcongr))
    (Real.sqrt_le_sqrt (by gcongr))
    (bourgain_dual_root_identity hm hq) (bourgain_dual_root_identity hn hr)
  have hs := Real.sq_sqrt (by positivity : 0 ≤ U*Q^3)
  have hcube : (Real.sqrt (U*Q^3))^3=U*Q^3*Real.sqrt (U*Q^3) := by
    nlinarith only [congrArg (fun z : ℝ => z*Real.sqrt (U*Q^3)) hs]
  rw [Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity),hcube] at hb
  have he : |nu*(r/q)^3-mu| *q^3=|mu*q^3-nu*r^3| := by
    calc
      _ = |(nu*(r/q)^3-mu)*q^3| := by
        rw [abs_mul,abs_of_pos (pow_pos hq 3)]
      _ = _ := by
        rw [abs_sub_comm (mu*q^3)]
        congr 1
        field_simp
  have hQcube : Q^3 ≤ 8*q^3 := by
    calc
      _ ≤ (2*q)^3 := by gcongr
      _ = _ := by ring
  apply (mul_le_mul_iff_left₀ (pow_pos hq 3)).mp
  rw [he]
  calc
    _ ≤ 2*(U*Q^3*Real.sqrt (U*Q^3))*
      |(-2*mu*(Real.sqrt (2/(3*mu*q)))^3)-
        (-2*nu*(Real.sqrt (2/(3*nu*r)))^3)| := hb
    _ ≤ 2*(U*(8*q^3)*Real.sqrt (U*Q^3))*zeta := by gcongr
    _ = _ := by ring

private theorem bourgain_rounded_third_derivative_error
    (f : ℝ → ℝ) {A B F x m : ℝ}
    (hf : ∀ z∈Ioo A B, ContDiffAt ℝ 4 f z)
    (hfour : ∀ z∈Ioo A B, |iteratedDeriv 4 f z| ≤ F)
    (hx : x∈Ioo A B) (hm : m∈Ioo A B) (hdist : |x-m| ≤ 1/2) :
    |iteratedDeriv 3 f x/6-iteratedDeriv 3 f m/6| ≤ F/12 := by
  have hF : 0 ≤ F := (abs_nonneg _).trans (hfour x hx)
  have hd z (hz : z∈Ioo A B) :
      HasDerivWithinAt (iteratedDeriv 3 f) (iteratedDeriv 4 f z) (Ioo A B) z := by
    have hh := contDiffAt_iteratedDeriv_finite (n:=1) (j:=3) (hf z hz)
    simpa only [iteratedDeriv_succ] using hh.differentiableAt_one.hasDerivAt.hasDerivWithinAt
  have hb := (convex_Ioo A B).norm_image_sub_le_of_norm_hasDerivWithin_le hd
    (fun z hz => by simpa only [Real.norm_eq_abs] using hfour z hz) hx hm
  simp only [Real.norm_eq_abs] at hb
  rw [abs_sub_comm (iteratedDeriv 3 f m),abs_sub_comm m] at hb
  rw [←sub_div,abs_div]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 6)]
  have hm := mul_le_mul_of_nonneg_left hdist hF
  linarith only [hb,hm]

                                                                          
                                                                   
theorem bourgain_C4_rounded_cubic_resonance_residual
    (f : ℝ → ℝ) {A B F U Q zeta x y : ℝ} (m n : ℤ) (q r : ℕ)
    (hf : ∀ z∈Ioo A B, ContDiffAt ℝ 4 f z)
    (hfour : ∀ z∈Ioo A B, |iteratedDeriv 4 f z| ≤ F)
    (hx : x∈Ioo A B) (hy : y∈Ioo A B)
    (hm : (m:ℝ)∈Ioo A B) (hn : (n:ℝ)∈Ioo A B)
    (hdm : |x-m| ≤ 1/2) (hdn : |y-n| ≤ 1/2)
    (hq : 0 < q) (hr : 0 < r)
    (hqQ : (q:ℝ) ≤ Q) (hrQ : (r:ℝ) ≤ Q) (hQq : Q ≤ 2*q) :
    let mu := iteratedDeriv 3 f m/6
    let nu := iteratedDeriv 3 f n/6
    let K := fun (v d : ℝ) => -2*v*(Real.sqrt (2/(3*v*d)))^3
    0 < mu → mu ≤ U → 0 < nu → nu ≤ U →
    |K mu q-K nu r| ≤ zeta →
    |(iteratedDeriv 3 f y/6)*((r:ℝ)/q)^3-iteratedDeriv 3 f x/6| ≤
      16*U*Real.sqrt (U*Q^3)*zeta+3*F/4 := by
  intro mu nu K hmu hmuU hnu hnuU hdual
  have hqr : (0:ℝ) < q := by exact_mod_cast hq
  have hrr : (0:ℝ) < r := by exact_mod_cast hr
  have hxerr := bourgain_rounded_third_derivative_error f hf hfour hx hm hdm
  have hyerr := bourgain_rounded_third_derivative_error f hf hfour hy hn hdn
  have hd := bourgain_dual_variable_denominator_difference hmu hnu hqr hrr
    hmuU hnuU hqQ hrQ hQq hdual
  have hF : 0 ≤ F := (abs_nonneg _).trans (hfour x hx)
  have ht : (r:ℝ)/q ≤ 2 := (div_le_iff₀ hqr).mpr (hrQ.trans hQq)
  have htp : 0 ≤ ((r:ℝ)/q)^3 := by positivity
  have ht3 : ((r:ℝ)/q)^3 ≤ 8 := by
    calc
      _ ≤ (2:ℝ)^3 := by gcongr
      _ = _ := by norm_num
  calc
    _ = |(iteratedDeriv 3 f y/6-nu)*((r:ℝ)/q)^3+
      (nu*((r:ℝ)/q)^3-mu)+(mu-iteratedDeriv 3 f x/6)| := by
        congr 1
        ring
    _ ≤ |(iteratedDeriv 3 f y/6-nu)*((r:ℝ)/q)^3|+
      |nu*((r:ℝ)/q)^3-mu|+|mu-iteratedDeriv 3 f x/6| := abs_add_three _ _ _
    _ = |iteratedDeriv 3 f y/6-nu| *((r:ℝ)/q)^3+
      |nu*((r:ℝ)/q)^3-mu|+|iteratedDeriv 3 f x/6-mu| := by
        rw [abs_mul,abs_of_nonneg htp,abs_sub_comm mu]
    _ ≤ (F/12)*8+16*U*Real.sqrt (U*Q^3)*zeta+F/12 := by gcongr
    _ = _ := by ring

                                                                            
                                                                           
                                                                         
theorem bourgain_C4_rounded_fixed_matrix_count
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ℝ → ℝ) (x y : ι → ℝ) (m n p pp : ι → ℤ) (q qq : ι → ℕ)
    (Q Bmul : ℕ) {A B L F U zeta : ℝ}
    (a b c d : ℤ) (hdet : a*d-b*c=1) (hc : c ≠ 0)
    (hL : 0 < L) (hF : 0 ≤ F) (hU : 0 < U) (hzeta : 0 ≤ zeta)
    (hFL : F ≤ L^2/16)
    (hf : ∀ z∈Ioo A B, ContDiffAt ℝ 4 f z)
    (hthree : ∀ z∈Ioo A B, L ≤ iteratedDeriv 3 f z ∧ iteratedDeriv 3 f z ≤ 6*U)
    (hfour : ∀ z∈Ioo A B, |iteratedDeriv 4 f z| ≤ F)
    (hx : ∀ i∈S, x i∈Ioo A B) (hy : ∀ i∈S, y i∈Ioo A B)
    (hm : ∀ i∈S, (m i:ℝ)∈Ioo A B) (hn : ∀ i∈S, (n i:ℝ)∈Ioo A B)
    (hdm : ∀ i∈S, |x i-m i| ≤ 1/2)
    (hdn : ∀ i∈S, |y i-n i| ≤ 1/2)
    (hq : ∀ i∈S, 0 < q i ∧ q i ≤ Q ∧ Q ≤ 2*q i)
    (hqq : ∀ i∈S, 0 < qq i ∧ qq i ≤ Q ∧ Q ≤ 2*qq i)
    (hmatp : ∀ i∈S, a*p i+b*(q i:ℤ)=pp i)
    (hmatq : ∀ i∈S, c*p i+d*(q i:ℤ)=(qq i:ℤ)) :
    let h := fun z => iteratedDeriv 2 f z/2
    let mu := fun i => iteratedDeriv 3 f (m i)/6
    let nu := fun i => iteratedDeriv 3 f (n i)/6
    let K := fun (v s : ℝ) => -2*v*(Real.sqrt (2/(3*v*s)))^3
    (∀ i∈S, h (x i)=(p i:ℝ)/q i) →
    (∀ i∈S, h (y i)=(pp i:ℝ)/qq i) →
    (∀ i∈S, |K (mu i) (q i)-K (nu i) (qq i)| ≤ zeta) →
    (∀ v : ℝ, (S.filter (fun i => h (x i)=v)).card ≤ Bmul) →
    (S.card:ℝ) ≤ Bmul*(1+
      48*(16*U*Real.sqrt (U*(Q:ℝ)^3)*zeta+3*F/4)*(Q:ℝ)^2/(|(c:ℝ)| *L)) := by
  classical
  intro h mu nu K hlevel hlevely hdual hmul
  let E := 16*U*Real.sqrt (U*(Q:ℝ)^3)*zeta+3*F/4
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have ht i (hi : i∈S) :
      (c:ℝ)*h (x i)+d=(qq i:ℝ)/q i := by
    have hqi : (q i:ℝ) ≠ 0 := by exact_mod_cast (hq i hi).1.ne'
    rw [hlevel i hi]
    field_simp
    exact_mod_cast (show c*p i+(q i:ℤ)*d=(qq i:ℤ) from by
      nlinarith only [hmatq i hi])
  have hmapi i (hi : i∈S) :
      ((a:ℝ)*h (x i)+b)/((c:ℝ)*h (x i)+d)=h (y i) := by
    have hqi : (q i:ℝ) ≠ 0 := by exact_mod_cast (hq i hi).1.ne'
    have hqqi : (qq i:ℝ) ≠ 0 := by exact_mod_cast (hqq i hi).1.ne'
    rw [ht i hi,hlevel i hi,hlevely i hi]
    have he : ((a:ℝ)*((p i:ℝ)/q i)+b)/((qq i:ℝ)/q i)=
        ((a:ℝ)*p i+(b:ℝ)*q i)/qq i := by field_simp
    rw [he]
    congr 1
    exact_mod_cast hmatp i hi
  have hti i (hi : i∈S) :
      (1:ℝ)/2 ≤ (c:ℝ)*h (x i)+d ∧ (c:ℝ)*h (x i)+d ≤ 2 := by
    rw [ht i hi]
    have hqi : (0:ℝ) < q i := by exact_mod_cast (hq i hi).1
    have hqu : (q i:ℝ) ≤ Q := by exact_mod_cast (hq i hi).2.1
    have hqqu : (qq i:ℝ) ≤ Q := by exact_mod_cast (hqq i hi).2.1
    have hql : (Q:ℝ) ≤ 2*q i := by exact_mod_cast (hq i hi).2.2
    have hqql : (Q:ℝ) ≤ 2*qq i := by exact_mod_cast (hqq i hi).2.2
    constructor
    · apply (le_div_iff₀ hqi).mpr
      linarith only [hqu,hqql]
    · exact (div_le_iff₀ hqi).mpr (hqqu.trans hql)
  have hmui i (hi : i∈S) : 0 < mu i ∧ mu i ≤ U := by
    have hh := hthree _ (hm i hi)
    dsimp only [mu]
    constructor <;> linarith only [hh.1,hh.2,hL]
  have hnui i (hi : i∈S) : 0 < nu i ∧ nu i ≤ U := by
    have hh := hthree _ (hn i hi)
    dsimp only [nu]
    constructor <;> linarith only [hh.1,hh.2,hL]
  have hres i (hi : i∈S) :
      |(iteratedDeriv 3 f (y i)/6)*((c:ℝ)*h (x i)+d)^3-
        iteratedDeriv 3 f (x i)/6| ≤ E := by
    rw [ht i hi]
    exact bourgain_C4_rounded_cubic_resonance_residual f (m i) (n i) (q i) (qq i)
      hf hfour (hx i hi) (hy i hi) (hm i hi) (hn i hi) (hdm i hi) (hdn i hi)
      (hq i hi).1 (hqq i hi).1
      (by exact_mod_cast (hq i hi).2.1) (by exact_mod_cast (hqq i hi).2.1)
      (by exact_mod_cast (hq i hi).2.2)
      (hmui i hi).1 (hmui i hi).2 (hnui i hi).1 (hnui i hi).2 (hdual i hi)
  exact bourgain_C4_fixed_matrix_resonance_count S f x y p q Q Bmul a b c d
    hdet hc hL hE hf (fun z hz => (hthree z hz).1)
    (fun z hz => (hfour z hz).trans hFL) hx hy
    (fun i hi => ⟨(hq i hi).1,(hq i hi).2.1⟩)
    hlevel hmapi hti hres hmul

private theorem bourgain_fixed_first_column_delta_spacing {a b c d b' d' : ℤ}
    (hdet : a*d-b*c=1) (hdet' : a*d'-b'*c=1)
    (hne : d ≠ d') : |c| ≤ |d-d'| := by
  have hid : d-d'=c*(b*d'-b'*d) := by
    nlinarith only [congrArg (fun z : ℤ => d'*z) hdet,
      congrArg (fun z : ℤ => d*z) hdet']
  have hn : b*d'-b'*d ≠ 0 := by
    intro he
    rw [he,mul_zero] at hid
    exact hne (sub_eq_zero.mp hid)
  have hh := Int.one_le_abs hn
  rw [hid,abs_mul]
  nlinarith only [mul_le_mul_of_nonneg_left hh (abs_nonneg c)]
                                                                      
                                                                       
                                             
theorem bourgain_fixed_gamma_matrix_count
    (S : Finset (Fin 4 → ℤ)) {c : ℤ} {X : ℝ} (hc : c ≠ 0) (hX : 0 ≤ X)
    (hdet : ∀ M∈S, M 0*M 3-M 1*M 2=1)
    (hgamma : ∀ M∈S, M 2=c)
    (ha : ∀ M∈S, |(M 0:ℝ)| ≤ |(c:ℝ)| *X+2)
    (hd : ∀ M∈S, |(M 3:ℝ)| ≤ |(c:ℝ)| *X+2) :
    (S.card:ℝ) ≤ (2*|(c:ℝ)| *X+5)*(2*X+5) := by
  classical
  have hc1 : (1:ℝ) ≤ |(c:ℝ)| := by exact_mod_cast Int.one_le_abs hc
  have hcpos : 0 < |(c:ℝ)| := by linarith only [hc1]
  let W := S.image (fun M => M 0)
  have hW : (W.card:ℝ) ≤ 2*|(c:ℝ)| *X+5 := by
    have hb := integer_card_le_of_abs_sub_le (a:=0) W
      (by positivity : 0 ≤ |(c:ℝ)| *X+2) (by
        intro a haW
        obtain ⟨M,hM,rfl⟩ := Finset.mem_image.mp haW
        simpa only [sub_zero] using ha M hM)
    linarith only [hb]
  have hfiber a : ((S.filter (fun M => M 0=a)).card:ℝ) ≤ 2*X+5 := by
    let T := S.filter (fun M => M 0=a)
    let val := fun M : Fin 4 → ℤ => (M 3:ℝ)/|(c:ℝ)|
    let V := T.image val
    have hT M (hM : M∈T) : M∈S ∧ M 0=a := Finset.mem_filter.mp hM
    have hinj : Set.InjOn val (T: Set (Fin 4 → ℤ)) := by
      intro M hM N hN he
      have hMr := hT M hM
      have hNr := hT N hN
      have h03 : M 3=N 3 := by
        have hh : (M 3:ℝ)=(N 3:ℝ) := (div_left_inj' hcpos.ne').mp he
        exact_mod_cast hh
      have hMdet := hdet M hMr.1
      have hNdet := hdet N hNr.1
      rw [hgamma M hMr.1,hMr.2] at hMdet
      rw [hgamma N hNr.1,hNr.2,←h03] at hNdet
      have hb : M 1=N 1 := by
        apply (mul_left_inj' hc).mp
        nlinarith only [hMdet,hNdet,h03]
      funext i
      fin_cases i
      · exact hMr.2.trans hNr.2.symm
      · exact hb
      · exact (hgamma M hMr.1).trans (hgamma N hNr.1).symm
      · exact h03
    have hsep : ∀ u∈V, ∀ v∈V, u ≠ v → 1 ≤ |u-v| := by
      intro u hu v hv huv
      obtain ⟨M,hM,rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨N,hN,rfl⟩ := Finset.mem_image.mp hv
      have hMr := hT M hM
      have hNr := hT N hN
      have hMdet : a*M 3-M 1*c=1 := by
        simpa only [hMr.2,hgamma M hMr.1] using hdet M hMr.1
      have hNdet : a*N 3-N 1*c=1 := by
        simpa only [hNr.2,hgamma N hNr.1] using hdet N hNr.1
      have hne : M 3 ≠ N 3 := by
        intro he
        apply huv
        dsimp only [val]
        rw [he]
      have hb : |(c:ℝ)| ≤ |(M 3:ℝ)-N 3| := by
        exact_mod_cast bourgain_fixed_first_column_delta_spacing hMdet hNdet hne
      dsimp only [val]
      rw [←sub_div,abs_div,abs_abs]
      exact (le_div_iff₀ hcpos).mpr (by simpa only [one_mul] using hb)
    have hmem v (hv : v∈V) : -(X+2) ≤ v ∧ v ≤ X+2 := by
      obtain ⟨M,hM,rfl⟩ := Finset.mem_image.mp hv
      have hb := hd M (hT M hM).1
      have hvb : |val M| ≤ X+2 := by
        dsimp only [val]
        rw [abs_div,abs_abs]
        apply (div_le_iff₀ hcpos).mpr
        nlinarith only [hb,hc1]
      exact abs_le.mp hvb
    have hb := oneSeparated_card_cast_le_interval_length_add_one V hsep
      (by linarith : 0 ≤ (X+2)-(-(X+2))) hmem
    have hcard : V.card=T.card := Finset.card_image_of_injOn hinj
    rw [hcard] at hb
    linarith only [hb]
  have hcard : (S.card:ℝ)=∑ a∈W,((S.filter (fun M => M 0=a)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise
      (fun M hM => Finset.mem_image_of_mem (fun M : Fin 4 → ℤ => M 0) hM)
  calc
    _ = _ := hcard
    _ ≤ ∑ a∈W,(2*X+5) := Finset.sum_le_sum (fun a _ => hfiber a)
    _ = (W.card:ℝ)*(2*X+5) := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hW (by positivity)

                                                                        
                                                                           
theorem bourgain_resonance_matrix_weight_sum
    (S : Finset (Fin 4 → ℤ)) {X Gamma W : ℝ}
    (hX : 0 ≤ X) (hGamma : 0 ≤ Gamma) (hW : 0 ≤ W)
    (hdet : ∀ M∈S, M 0*M 3-M 1*M 2=1)
    (hc : ∀ M∈S, M 2 ≠ 0 ∧ |(M 2:ℝ)| ≤ Gamma)
    (ha : ∀ M∈S, |(M 0:ℝ)| ≤ |(M 2:ℝ)| *X+2)
    (hd : ∀ M∈S, |(M 3:ℝ)| ≤ |(M 2:ℝ)| *X+2) :
    ∑ M∈S,(1+W/|(M 2:ℝ)|) ≤ (2*Gamma+1)*(2*X+5)^2*(Gamma+W) := by
  classical
  let C := S.image (fun M => M 2)
  have hC : (C.card:ℝ) ≤ 2*Gamma+1 :=
    integer_card_le_of_abs_sub_le (a:=0) C hGamma (by
      intro c hcC
      obtain ⟨M,hM,rfl⟩ := Finset.mem_image.mp hcC
      simpa only [sub_zero] using (hc M hM).2)
  have hfiber c (hcC : c∈C) :
      ∑ M∈S.filter (fun M => M 2=c),(1+W/|(M 2:ℝ)|) ≤
        (2*X+5)^2*(Gamma+W) := by
    obtain ⟨M,hM,he⟩ := Finset.mem_image.mp hcC
    have hcz : c ≠ 0 := by rw [←he]; exact (hc M hM).1
    have hc1 : (1:ℝ) ≤ |(c:ℝ)| := by exact_mod_cast Int.one_le_abs hcz
    have hcpos : 0 < |(c:ℝ)| := by linarith only [hc1]
    have hcG : |(c:ℝ)| ≤ Gamma := by rw [←he]; exact (hc M hM).2
    let T := S.filter (fun M => M 2=c)
    have hT N (hN : N∈T) : N∈S ∧ N 2=c := Finset.mem_filter.mp hN
    have hb := bourgain_fixed_gamma_matrix_count T hcz hX
      (fun N hN => hdet N (hT N hN).1) (fun N hN => (hT N hN).2)
      (fun N hN => by simpa only [(hT N hN).2] using ha N (hT N hN).1)
      (fun N hN => by simpa only [(hT N hN).2] using hd N (hT N hN).1)
    have hcard : (T.card:ℝ) ≤ |(c:ℝ)| *(2*X+5)^2 := by
      calc
        _ ≤ (2*|(c:ℝ)| *X+5)*(2*X+5) := hb
        _ ≤ (|(c:ℝ)| *(2*X+5))*(2*X+5) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          nlinarith only [hc1]
        _ = _ := by ring
    calc
      _ = ∑ N∈T,(1+W/|(c:ℝ)|) := Finset.sum_congr rfl (fun N hN => by rw [(hT N hN).2])
      _ = (T.card:ℝ)*(1+W/|(c:ℝ)|) := by simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ (|(c:ℝ)| *(2*X+5)^2)*(1+W/|(c:ℝ)|) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (2*X+5)^2*(|(c:ℝ)|+W) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hcG] : |(c:ℝ)|+W ≤ Gamma+W) (sq_nonneg _)
  have hsum : (∑ M∈S,(1+W/|(M 2:ℝ)|)) =
      ∑ c∈C,∑ M∈S.filter (fun M => M 2=c),(1+W/|(M 2:ℝ)|) := by
    exact (Finset.sum_fiberwise_of_maps_to
      (fun M hM => Finset.mem_image_of_mem (fun M : Fin 4 → ℤ => M 2) hM) _).symm
  rw [hsum]
  calc
    _ ≤ ∑ c∈C,(2*X+5)^2*(Gamma+W) := Finset.sum_le_sum hfiber
    _ = (C.card:ℝ)*((2*X+5)^2*(Gamma+W)) := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (2*Gamma+1)*((2*X+5)^2*(Gamma+W)) :=
      mul_le_mul_of_nonneg_right hC (by positivity)
    _ = _ := by ring

theorem bourgain_mobius_entry_bounds {a b c d x y X : ℝ}
    (hdet : a*d-b*c=1) (htl : (1:ℝ)/2 ≤ c*x+d) (htu : c*x+d ≤ 2)
    (hmap : (a*x+b)/(c*x+d)=y) (hx : |x| ≤ X) (hy : |y| ≤ X) :
    |a| ≤ |c| *X+2 ∧ |d| ≤ |c| *X+2 := by
  have ht : 0 < c*x+d := by linarith only [htl]
  have hid : a=c*y+1/(c*x+d) := by
    have he := (div_eq_iff ht.ne').mp hmap
    have hid : (a-c*y)*(c*x+d)=1 := by
      nlinarith only [hdet,congrArg (fun z : ℝ => c*z) he]
    have hh : a-c*y=1/(c*x+d) := (eq_div_iff ht.ne').mpr hid
    linarith only [hh]
  have hinv : 1/(c*x+d) ≤ 2 := by
    apply (div_le_iff₀ ht).mpr
    linarith only [htl]
  constructor
  · rw [hid]
    calc
      _ ≤ |c*y|+|1/(c*x+d)| := abs_add_le _ _
      _ = |c| *|y|+1/(c*x+d) := by rw [abs_mul,abs_of_pos (one_div_pos.mpr ht)]
      _ ≤ _ := by gcongr
  · calc
      _ = |(c*x+d)-c*x| := by congr 1; ring
      _ ≤ |c*x+d|+|c*x| := abs_sub _ _
      _ = (c*x+d)+|c| *|x| := by rw [abs_of_pos ht,abs_mul]
      _ ≤ 2+|c| *X := by gcongr
      _ = _ := by ring


                                                                            
                                                                          
                                            
theorem bourgain_curvature_level_block_multiplicity
    {ι : Type*} (S : Finset ι) (f : ℝ → ℝ) (z : ι → ℝ)
    (m k : ι → ℤ) (N Bmul : ℕ) (s : ℤ) {A B L : ℝ}
    (hN : 0 < N) (hL : 0 < L)
    (hf : ∀ x∈Ioo A B, ContDiffAt ℝ 4 f x)
    (hthree : ∀ x∈Ioo A B, L ≤ iteratedDeriv 3 f x)
    (hz : ∀ i∈S, z i∈Ioo A B)
    (hround : ∀ i∈S, |z i-m i| ≤ 1/2)
    (hspan : ∀ i∈S, (N:ℤ) ≤ s+(N:ℤ)*k i-m i ∧
      s+(N:ℤ)*k i-m i ≤ 3*(N:ℤ))
    (hmul : ∀ j : ℤ, (S.filter (fun i => k i=j)).card ≤ Bmul) :
    ∀ v : ℝ, (S.filter (fun i => iteratedDeriv 2 f (z i)/2=v)).card ≤ 4*Bmul := by
  classical
  let h := fun x => iteratedDeriv 2 f x/2
  have hd x (hx : x∈Ioo A B) : HasDerivAt h (iteratedDeriv 3 f x/2) x := by
    have hh := contDiffAt_iteratedDeriv_finite (n:=2) (j:=2) (hf x hx)
    simpa only [h,iteratedDeriv_succ] using
      (hh.differentiableAt (by norm_num)).hasDerivAt.div_const 2
  have hs : StrictMonoOn h (Ioo A B) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo A B)
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      have hxi : x∈Ioo A B := by simpa only [interior_Ioo] using hx
      rw [(hd x hxi).deriv]
      linarith only [hthree x hxi,hL]
  intro v
  let T := S.filter (fun i => h (z i)=v)
  change T.card ≤ 4*Bmul
  rcases T.eq_empty_or_nonempty with hT | hT
  · rw [hT,Finset.card_empty]
    exact Nat.zero_le _
  obtain ⟨i,hi⟩ := hT
  have hi' := Finset.mem_filter.mp hi
  have hsame j (hj : j∈T) : z j=z i := by
    have hj' := Finset.mem_filter.mp hj
    exact hs.injOn (hz j hj'.1) (hz i hi'.1) (hj'.2.trans hi'.2.symm)
  let W := T.image k
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  let lo := (z i+N-1/2-s)/N
  let up := (z i+3*N+1/2-s)/N
  have hlen : up-lo=2+1/(N:ℝ) := by dsimp only [lo,up]; field_simp; ring
  have hW : (W.card:ℝ) ≤ 4 := by
    have hh := integer_card_le_interval_length_add_one W
      (by rw [←sub_nonneg,hlen]; positivity) (by
        intro j hj
        obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hj
        have hr' := Finset.mem_filter.mp hr
        have hdist := abs_le.mp (hround r hr'.1)
        rw [hsame r hr] at hdist
        have hl : (N:ℝ) ≤ (s:ℝ)+(N:ℝ)*k r-m r := by exact_mod_cast (hspan r hr'.1).1
        have hu : (s:ℝ)+(N:ℝ)*k r-m r ≤ 3*(N:ℝ) := by exact_mod_cast (hspan r hr'.1).2
        dsimp only [lo,up]
        constructor
        · apply (div_le_iff₀ hNr).mpr
          nlinarith only [hl,hdist.2]
        · apply (le_div_iff₀ hNr).mpr
          nlinarith only [hu,hdist.1])
    rw [hlen] at hh
    have hinv : 1/(N:ℝ) ≤ 1 := (div_le_iff₀ hNr).mpr (by simpa using hN1)
    linarith only [hh,hinv]
  have hcard : (T.card:ℝ)=∑ j∈W,((T.filter (fun i => k i=j)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise
      (fun i hi => Finset.mem_image_of_mem k hi)
  have hfiber j : ((T.filter (fun i => k i=j)).card:ℝ) ≤ Bmul := by
    have hsub : T.filter (fun i => k i=j) ⊆ S.filter (fun i => k i=j) := by
      intro r hr
      obtain ⟨hr,he⟩ := Finset.mem_filter.mp hr
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hr).1,he⟩
    exact_mod_cast (Finset.card_le_card hsub).trans (hmul j)
  have hb : (T.card:ℝ) ≤ 4*Bmul := by
    calc
      _ = _ := hcard
      _ ≤ ∑ j∈W,(Bmul:ℝ) := Finset.sum_le_sum (fun j _ => hfiber j)
      _ = (W.card:ℝ)*Bmul := by simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hW (Nat.cast_nonneg _)
  exact_mod_cast hb

private theorem bourgain_rational_matrix_map
    {a b c d p pp : ℤ} {q qq : ℕ} (hq : 0 < q) (hqq : 0 < qq)
    (hp : a*p+b*(q:ℤ)=pp) (hd : c*p+d*(q:ℤ)=(qq:ℤ)) :
    (c:ℝ)*((p:ℝ)/q)+d=(qq:ℝ)/q ∧
    ((a:ℝ)*((p:ℝ)/q)+b)/((c:ℝ)*((p:ℝ)/q)+d)=(pp:ℝ)/qq := by
  have hqr : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqqr : (qq:ℝ) ≠ 0 := by exact_mod_cast hqq.ne'
  have ht : (c:ℝ)*((p:ℝ)/q)+d=(qq:ℝ)/q := by
    field_simp
    exact_mod_cast (show c*p+(q:ℤ)*d=(qq:ℤ) from by nlinarith only [hd])
  refine ⟨ht,?_⟩
  rw [ht]
  have he : ((a:ℝ)*((p:ℝ)/q)+b)/((qq:ℝ)/q)=((a:ℝ)*p+(b:ℝ)*q)/qq := by
    field_simp
  rw [he]
  congr 1
  exact_mod_cast hp

                                                                       
                                                                        
                                                               
theorem bourgain_C4_assigned_nontriangular_pair_count
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (R : Finset (ι × ι))
    (f : ℝ → ℝ) (z : ι → ℝ) (m k p : ι → ℤ) (q : ι → ℕ)
    (M : ι × ι → Fin 4 → ℤ) (N Q Bmul : ℕ) (s : ℤ)
    {A B L F U X Gamma zeta : ℝ}
    (hN : 0 < N) (hL : 0 < L) (hF : 0 ≤ F) (hU : 0 < U)
    (hX : 0 ≤ X) (hGamma : 0 ≤ Gamma) (hzeta : 0 ≤ zeta)
    (hFL : F ≤ L^2/16)
    (hf : ∀ x∈Ioo A B, ContDiffAt ℝ 4 f x)
    (hthree : ∀ x∈Ioo A B, L ≤ iteratedDeriv 3 f x ∧ iteratedDeriv 3 f x ≤ 6*U)
    (hfour : ∀ x∈Ioo A B, |iteratedDeriv 4 f x| ≤ F)
    (hz : ∀ i∈S, z i∈Ioo A B) (hm : ∀ i∈S, (m i:ℝ)∈Ioo A B)
    (hround : ∀ i∈S, |z i-m i| ≤ 1/2)
    (hspan : ∀ i∈S, (N:ℤ) ≤ s+(N:ℤ)*k i-m i ∧
      s+(N:ℤ)*k i-m i ≤ 3*(N:ℤ))
    (hmul : ∀ j : ℤ, (S.filter (fun i => k i=j)).card ≤ Bmul)
    (hq : ∀ i∈S, 0 < q i ∧ q i ≤ Q ∧ Q ≤ 2*q i)
    (hR : R ⊆ S ×ˢ S)
    (hdet : ∀ ij∈R, M ij 0*M ij 3-M ij 1*M ij 2=1)
    (hc : ∀ ij∈R, M ij 2 ≠ 0 ∧ |(M ij 2:ℝ)| ≤ Gamma)
    (hmatp : ∀ ij∈R, M ij 0*p ij.1+M ij 1*(q ij.1:ℤ)=p ij.2)
    (hmatq : ∀ ij∈R, M ij 2*p ij.1+M ij 3*(q ij.1:ℤ)=(q ij.2:ℤ)) :
    let h := fun x => iteratedDeriv 2 f x/2
    let mu := fun i => iteratedDeriv 3 f (m i)/6
    let K := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let E := 16*U*Real.sqrt (U*(Q:ℝ)^3)*zeta+3*F/4
    (∀ i∈S, h (z i)=(p i:ℝ)/q i) →
    (∀ i∈S, |h (z i)| ≤ X) →
    (∀ ij∈R, |K ij.1-K ij.2| ≤ zeta) →
    (R.card:ℝ) ≤ 16*(Bmul:ℝ)^2*(2*Gamma+1)*(2*X+5)^2*
      (Gamma+48*E*(Q:ℝ)^2/L) := by
  classical
  intro h mu K E hlevel hlevelX hdual
  have hRmem ij (hij : ij∈R) : ij.1∈S ∧ ij.2∈S := Finset.mem_product.mp (hR hij)
  have hlevels : ∀ v : ℝ, (S.filter (fun i => h (z i)=v)).card ≤ 4*Bmul :=
    bourgain_curvature_level_block_multiplicity S f z m k N Bmul s hN hL hf
      (fun x hx => (hthree x hx).1) hz hround hspan hmul
  have hmap ij (hij : ij∈R) :
      (M ij 2:ℝ)*h (z ij.1)+M ij 3=(q ij.2:ℝ)/q ij.1 ∧
      ((M ij 0:ℝ)*h (z ij.1)+M ij 1)/((M ij 2:ℝ)*h (z ij.1)+M ij 3)=h (z ij.2) := by
    rw [hlevel ij.1 (hRmem ij hij).1,hlevel ij.2 (hRmem ij hij).2]
    exact bourgain_rational_matrix_map (hq ij.1 (hRmem ij hij).1).1
      (hq ij.2 (hRmem ij hij).2).1 (hmatp ij hij) (hmatq ij hij)
  have ht ij (hij : ij∈R) :
      (1:ℝ)/2 ≤ (M ij 2:ℝ)*h (z ij.1)+M ij 3 ∧
      (M ij 2:ℝ)*h (z ij.1)+M ij 3 ≤ 2 := by
    rw [(hmap ij hij).1]
    have hqi : (0:ℝ) < q ij.1 := by exact_mod_cast (hq ij.1 (hRmem ij hij).1).1
    have hqu : (q ij.1:ℝ) ≤ Q := by exact_mod_cast (hq ij.1 (hRmem ij hij).1).2.1
    have hqv : (q ij.2:ℝ) ≤ Q := by exact_mod_cast (hq ij.2 (hRmem ij hij).2).2.1
    have hql : (Q:ℝ) ≤ 2*q ij.1 := by exact_mod_cast (hq ij.1 (hRmem ij hij).1).2.2
    have hqr : (Q:ℝ) ≤ 2*q ij.2 := by exact_mod_cast (hq ij.2 (hRmem ij hij).2).2.2
    constructor
    · apply (le_div_iff₀ hqi).mpr
      linarith only [hqu,hqr]
    · exact (div_le_iff₀ hqi).mpr (hqv.trans hql)
  let T := R.image M
  let W := 48*E*(Q:ℝ)^2/L
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hmatrix t (htT : t∈T) :
      t 0*t 3-t 1*t 2=1 ∧ t 2 ≠ 0 ∧ |(t 2:ℝ)| ≤ Gamma ∧
      |(t 0:ℝ)| ≤ |(t 2:ℝ)| *X+2 ∧ |(t 3:ℝ)| ≤ |(t 2:ℝ)| *X+2 := by
    obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp htT
    have hb := bourgain_mobius_entry_bounds
      (by exact_mod_cast hdet ij hij) (ht ij hij).1 (ht ij hij).2 (hmap ij hij).2
      (hlevelX ij.1 (hRmem ij hij).1) (hlevelX ij.2 (hRmem ij hij).2)
    exact ⟨hdet ij hij,(hc ij hij).1,(hc ij hij).2,hb⟩
  have hsum := bourgain_resonance_matrix_weight_sum T hX hGamma hW
    (fun t htT => (hmatrix t htT).1)
    (fun t htT => ⟨(hmatrix t htT).2.1,(hmatrix t htT).2.2.1⟩)
    (fun t htT => (hmatrix t htT).2.2.2.1)
    (fun t htT => (hmatrix t htT).2.2.2.2)
  have hfiber t (htT : t∈T) :
      ((R.filter (fun ij => M ij=t)).card:ℝ) ≤ ((4*Bmul)^2:ℕ)*(1+W/|(t 2:ℝ)|) := by
    let V := R.filter (fun ij => M ij=t)
    have hV ij (hij : ij∈V) : ij∈R ∧ M ij=t := Finset.mem_filter.mp hij
    have hpairlevels v : (V.filter (fun ij => h (z ij.1)=v)).card ≤ (4*Bmul)^2 := by
      let w := ((t 0:ℝ)*v+t 1)/((t 2:ℝ)*v+t 3)
      have hsub : V.filter (fun ij => h (z ij.1)=v) ⊆
          (S.filter (fun i => h (z i)=v)) ×ˢ (S.filter (fun j => h (z j)=w)) := by
        intro ij hij
        obtain ⟨hij,hi⟩ := Finset.mem_filter.mp hij
        have hijR := (hV ij hij).1
        have hmapi := (hmap ij hijR).2
        rw [(hV ij hij).2,hi] at hmapi
        exact Finset.mem_product.mpr
          ⟨Finset.mem_filter.mpr ⟨(hRmem ij hijR).1,hi⟩,
           Finset.mem_filter.mpr ⟨(hRmem ij hijR).2,hmapi.symm⟩⟩
      calc
        _ ≤ _ := Finset.card_le_card hsub
        _ = _ := Finset.card_product _ _
        _ ≤ (4*Bmul)*(4*Bmul) := Nat.mul_le_mul (hlevels v) (hlevels w)
        _ = _ := by ring
    have hb := bourgain_C4_rounded_fixed_matrix_count V f
      (fun ij => z ij.1) (fun ij => z ij.2) (fun ij => m ij.1) (fun ij => m ij.2)
      (fun ij => p ij.1) (fun ij => p ij.2) (fun ij => q ij.1) (fun ij => q ij.2)
      Q ((4*Bmul)^2) (t 0) (t 1) (t 2) (t 3)
      (hmatrix t htT).1 (hmatrix t htT).2.1 hL hF hU hzeta hFL hf hthree hfour
      (fun ij hij => hz ij.1 (hRmem ij (hV ij hij).1).1)
      (fun ij hij => hz ij.2 (hRmem ij (hV ij hij).1).2)
      (fun ij hij => hm ij.1 (hRmem ij (hV ij hij).1).1)
      (fun ij hij => hm ij.2 (hRmem ij (hV ij hij).1).2)
      (fun ij hij => hround ij.1 (hRmem ij (hV ij hij).1).1)
      (fun ij hij => hround ij.2 (hRmem ij (hV ij hij).1).2)
      (fun ij hij => hq ij.1 (hRmem ij (hV ij hij).1).1)
      (fun ij hij => hq ij.2 (hRmem ij (hV ij hij).1).2)
      (fun ij hij => by simpa only [(hV ij hij).2] using hmatp ij (hV ij hij).1)
      (fun ij hij => by simpa only [(hV ij hij).2] using hmatq ij (hV ij hij).1)
      (fun ij hij => hlevel ij.1 (hRmem ij (hV ij hij).1).1)
      (fun ij hij => hlevel ij.2 (hRmem ij (hV ij hij).1).2)
      (fun ij hij => hdual ij (hV ij hij).1) hpairlevels
    convert hb using 1
    dsimp only [W,E]
    ring
  have hcard : (R.card:ℝ)=∑ t∈T,((R.filter (fun ij => M ij=t)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise (fun ij hij => Finset.mem_image_of_mem M hij)
  calc
    _ = _ := hcard
    _ ≤ ∑ t∈T,(((4*Bmul)^2:ℕ):ℝ)*(1+W/|(t 2:ℝ)|) := Finset.sum_le_sum hfiber
    _ = (((4*Bmul)^2:ℕ):ℝ)*(∑ t∈T,(1+W/|(t 2:ℝ)|)) := by rw [Finset.mul_sum]
    _ ≤ (((4*Bmul)^2:ℕ):ℝ)*((2*Gamma+1)*(2*X+5)^2*(Gamma+W)) :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ = _ := by dsimp only [W]; push_cast; ring

                                                                          
                                                                             
                                                                          
                                  
theorem exists_bourgain_C4_nontriangular_second_spacing
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ℝ → ℝ) (z : ι → ℝ) (m k p r : ι → ℤ) (q : ι → ℕ)
    (N Q Bmul : ℕ) (s : ℤ) {A B L F U X eta zeta : ℝ}
    (hN : 0 < N) (hL : 0 < L) (hF : 0 ≤ F) (hU : 0 < U)
    (hX : 0 ≤ X) (heta : 0 ≤ eta) (hzeta : 0 ≤ zeta)
    (hFL : F ≤ L^2/16)
    (hf : ∀ x∈Ioo A B, ContDiffAt ℝ 4 f x)
    (hthree : ∀ x∈Ioo A B, L ≤ iteratedDeriv 3 f x ∧ iteratedDeriv 3 f x ≤ 6*U)
    (hfour : ∀ x∈Ioo A B, |iteratedDeriv 4 f x| ≤ F)
    (hz : ∀ i∈S, z i∈Ioo A B) (hm : ∀ i∈S, (m i:ℝ)∈Ioo A B)
    (hround : ∀ i∈S, |z i-m i| ≤ 1/2)
    (hspan : ∀ i∈S, (N:ℤ) ≤ s+(N:ℤ)*k i-m i ∧
      s+(N:ℤ)*k i-m i ≤ 3*(N:ℤ))
    (hmul : ∀ j : ℤ, (S.filter (fun i => k i=j)).card ≤ Bmul)
    (hq : ∀ i∈S, 0 < q i ∧ q i ≤ Q ∧ Q ≤ 2*q i)
    (hinv : ∀ i∈S, (q i:ℤ) ∣ p i*r i-1) :
    let h := fun x => iteratedDeriv 2 f x/2
    let mu := fun i => iteratedDeriv 3 f (m i)/6
    let K := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let E := 16*U*Real.sqrt (U*(Q:ℝ)^3)*zeta+3*F/4
    let Gamma := eta*(Q:ℝ)^2
    let R := (S ×ˢ S).filter (fun ij =>
      |Int.fract (-(r ij.1:ℝ)/q ij.1)-Int.fract (-(r ij.2:ℝ)/q ij.2)| ≤ eta ∧
      |K ij.1-K ij.2| ≤ zeta)
    (∀ i∈S, h (z i)=(p i:ℝ)/q i) →
    (∀ i∈S, |h (z i)| ≤ X) →
    ∃ M : ι × ι → Fin 4 → ℤ,
      (∀ ij∈R, M ij 0*M ij 3-M ij 1*M ij 2=1 ∧
        M ij 0*p ij.1+M ij 1*(q ij.1:ℤ)=p ij.2 ∧
        M ij 2*p ij.1+M ij 3*(q ij.1:ℤ)=(q ij.2:ℤ) ∧
        |(M ij 2:ℝ)| ≤ eta*(q ij.1:ℝ)*q ij.2) ∧
      ((R.filter (fun ij => M ij 2 ≠ 0)).card:ℝ) ≤
        16*(Bmul:ℝ)^2*(2*Gamma+1)*(2*X+5)^2*
          (Gamma+48*E*(Q:ℝ)^2/L) := by
  classical
  intro h mu K E Gamma R hlevel hlevelX
  have hRmem ij (hij : ij∈R) : ij.1∈S ∧ ij.2∈S :=
    Finset.mem_product.mp (Finset.mem_filter.mp hij).1
  have hex : ∀ ij : ι × ι, ∃ M : Fin 4 → ℤ, ij∈R →
      M 0*M 3-M 1*M 2=1 ∧
      M 0*p ij.1+M 1*(q ij.1:ℤ)=p ij.2 ∧
      M 2*p ij.1+M 3*(q ij.1:ℤ)=(q ij.2:ℤ) ∧
      |(M 2:ℝ)| ≤ eta*(q ij.1:ℝ)*q ij.2 := by
    intro ij
    by_cases hij : ij∈R
    · obtain ⟨a,b,c,d,hdet,hp,hqmap,hc,_hsmall⟩ :=
        bourgain_inverse_coordinate_resonance (p ij.1) (p ij.2) (r ij.1) (r ij.2)
          (q ij.1) (q ij.2) (hq ij.1 (hRmem ij hij).1).1 (hq ij.2 (hRmem ij hij).2).1
          (hinv ij.1 (hRmem ij hij).1) (hinv ij.2 (hRmem ij hij).2)
          (Finset.mem_filter.mp hij).2.1
      exact ⟨![a,b,c,d],fun _ => by simpa using And.intro hdet ⟨hp,hqmap,hc⟩⟩
    · exact ⟨![1,0,0,1],fun h => False.elim (hij h)⟩
  choose M hM using hex
  refine ⟨M,hM,?_⟩
  let T := R.filter (fun ij => M ij 2 ≠ 0)
  have hT ij (hij : ij∈T) : ij∈R ∧ M ij 2 ≠ 0 := Finset.mem_filter.mp hij
  have hG : 0 ≤ Gamma := by dsimp only [Gamma]; positivity
  have hgamma ij (hij : ij∈T) : M ij 2 ≠ 0 ∧ |(M ij 2:ℝ)| ≤ Gamma := by
    refine ⟨(hT ij hij).2,(hM ij (hT ij hij).1).2.2.2.trans ?_⟩
    have hqi : (q ij.1:ℝ) ≤ Q := by exact_mod_cast (hq ij.1 (hRmem ij (hT ij hij).1).1).2.1
    have hqj : (q ij.2:ℝ) ≤ Q := by exact_mod_cast (hq ij.2 (hRmem ij (hT ij hij).1).2).2.1
    dsimp only [Gamma]
    calc
      _ ≤ eta*(Q:ℝ)*Q := by gcongr
      _ = _ := by ring
  exact bourgain_C4_assigned_nontriangular_pair_count S T f z m k p q M N Q Bmul s
    hN hL hF hU hX hG hzeta hFL hf hthree hfour hz hm hround hspan hmul hq
    (fun ij hij => (Finset.mem_filter.mp (hT ij hij).1).1)
    (fun ij hij => (hM ij (hT ij hij).1).1) hgamma
    (fun ij hij => (hM ij (hT ij hij).1).2.1)
    (fun ij hij => (hM ij (hT ij hij).1).2.2.1)
    hlevel hlevelX (fun ij hij => (Finset.mem_filter.mp (hT ij hij).1).2.2)

private theorem bourgain_triangular_inverse_coordinate_equality
    (alpha beta delta p pp r rr : ℤ) (q qq : ℕ)
    (hq : 0 < q) (hqq : 0 < qq)
    (hdet : alpha*delta=1)
    (hp : alpha*p+beta*(q:ℤ)=pp) (hd : delta*(q:ℤ)=(qq:ℤ))
    (hinv : (q:ℤ)∣p*r-1) (hinv' : (qq:ℤ)∣pp*rr-1) :
    q=qq ∧ Int.fract (-(r:ℝ)/q)=Int.fract (-(rr:ℝ)/qq) ∧
      (pp:ℝ)/qq-(p:ℝ)/q=(beta:ℝ) := by
  have hqi : (0:ℤ) < q := by exact_mod_cast hq
  have hqqi : (0:ℤ) < qq := by exact_mod_cast hqq
  have hdpos : 0 < delta := by nlinarith only [hd,hqi,hqqi]
  have hapos : 0 < alpha := by nlinarith only [hdet,hdpos]
  have hd1 : delta=1 := by nlinarith only [hdpos,hapos,hdet]
  have ha1 : alpha=1 := by nlinarith only [hdet,hd1]
  have hqeq : q=qq := by
    have hh : (q:ℤ)=(qq:ℤ) := by simpa only [hd1,one_mul] using hd
    exact_mod_cast hh
  subst qq
  rw [ha1,one_mul] at hp
  refine ⟨rfl,?_,?_⟩
  · obtain ⟨b,hb⟩ := hinv
    have hcop : IsCoprime (q:ℤ) p := by
      refine ⟨-b,r,?_⟩
      nlinarith only [hb]
    have hr' : (q:ℤ)∣p*rr-1 := by
      obtain ⟨b',hb'⟩ := hinv'
      refine ⟨b'-beta*rr,?_⟩
      nlinarith only [hb',congrArg (fun v : ℤ => v*rr) hp]
    have hdiff : (q:ℤ)∣p*(r-rr) := by
      convert dvd_sub (show (q:ℤ)∣p*r-1 from ⟨b,hb⟩) hr' using 1
      ring
    obtain ⟨j,hj⟩ := hcop.dvd_of_dvd_mul_left hdiff
    apply Int.fract_eq_fract.mpr
    refine ⟨-j,?_⟩
    have hqr : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have hrreal : (r:ℝ)-rr=(q:ℝ)*j := by exact_mod_cast hj
    push_cast
    field_simp
    nlinarith only [hrreal]
  · have hqr : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have hpR : (p:ℝ)+(beta:ℝ)*q=(pp:ℝ) := by exact_mod_cast hp
    field_simp
    nlinarith only [hpR]

                                                                       
theorem bourgain_curvature_level_difference
    (f : ℝ → ℝ) {A B U x y : ℝ}
    (hf : ∀ z∈Icc A B, ContDiffAt ℝ 4 f z)
    (hthree : ∀ z∈Icc A B, 0 ≤ iteratedDeriv 3 f z ∧ iteratedDeriv 3 f z ≤ 6*U)
    (hx : x∈Icc A B) (hy : y∈Icc A B) :
    |iteratedDeriv 2 f x/2-iteratedDeriv 2 f y/2| ≤ 3*U*|x-y| := by
  have hd z (hz : z∈Icc A B) :
      HasDerivWithinAt (fun z => iteratedDeriv 2 f z/2)
        (iteratedDeriv 3 f z/2) (Icc A B) z := by
    have hh := contDiffAt_iteratedDeriv_finite (n:=2) (j:=2) (hf z hz)
    simpa only [iteratedDeriv_succ] using
      ((hh.differentiableAt (by norm_num)).hasDerivAt.div_const 2).hasDerivWithinAt
  have hb := (convex_Icc A B).norm_image_sub_le_of_norm_hasDerivWithin_le (C:=3*U) hd
    (by
      intro z hz
      rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (hthree z hz).1 (by norm_num))]
      linarith only [(hthree z hz).2]) hx hy
  simpa only [Real.norm_eq_abs,abs_sub_comm y x,
    abs_sub_comm (iteratedDeriv 2 f y/2) (iteratedDeriv 2 f x/2)] using hb

                                                                         
                                                                          
                                                                     
theorem bourgain_C4_triangular_pair_count
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (R : Finset (ι × ι))
    (f : ℝ → ℝ) (z : ι → ℝ) (m k p r : ι → ℤ) (q : ι → ℕ)
    (M : ι × ι → Fin 4 → ℤ) (N Q Bmul : ℕ) (s : ℤ)
    {A B L U lambda zeta : ℝ}
    (hN : 0 < N) (hL : 0 < L) (hU : 0 < U)
    (hlambda : 0 < lambda) (hzeta : 0 ≤ zeta)
    (hf : ∀ x∈Icc A B, ContDiffAt ℝ 4 f x)
    (hthree : ∀ x∈Icc A B, L ≤ iteratedDeriv 3 f x ∧ iteratedDeriv 3 f x ≤ 6*U)
    (hfour : ∀ x∈Icc A B, lambda ≤ |iteratedDeriv 4 f x|)
    (hz : ∀ i∈S, z i∈Ioo A B) (hm : ∀ i∈S, (m i:ℝ)∈Ioo A B)
    (hround : ∀ i∈S, |z i-m i| ≤ 1/2)
    (hspan : ∀ i∈S, (N:ℤ) ≤ s+(N:ℤ)*k i-m i ∧
      s+(N:ℤ)*k i-m i ≤ 3*(N:ℤ))
    (hmul : ∀ j : ℤ, (S.filter (fun i => k i=j)).card ≤ Bmul)
    (hq : ∀ i∈S, 0 < q i ∧ q i ≤ Q)
    (hinv : ∀ i∈S, (q i:ℤ) ∣ p i*r i-1)
    (hR : R ⊆ S ×ˢ S)
    (hdet : ∀ ij∈R, M ij 0*M ij 3-M ij 1*M ij 2=1)
    (hzero : ∀ ij∈R, M ij 2=0)
    (hmatp : ∀ ij∈R, M ij 0*p ij.1+M ij 1*(q ij.1:ℤ)=p ij.2)
    (hmatq : ∀ ij∈R, M ij 2*p ij.1+M ij 3*(q ij.1:ℤ)=(q ij.2:ℤ)) :
    let h := fun x => iteratedDeriv 2 f x/2
    let mu := fun i => iteratedDeriv 3 f (m i)/6
    let K := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let rho := (12*U*Real.sqrt (U*(Q:ℝ)^3)/lambda)*zeta
    (∀ i∈S, h (z i)=(p i:ℝ)/q i) →
    (∀ ij∈R, |K ij.1-K ij.2| ≤ zeta) →
    (R.card:ℝ) ≤ 4*Bmul*S.card*(1+6*U*(rho+1)) := by
  classical
  intro h mu K rho hlevel hdual
  have hRmem ij (hij : ij∈R) : ij.1∈S ∧ ij.2∈S := Finset.mem_product.mp (hR hij)
  have hlevels := bourgain_curvature_level_block_multiplicity S f z m k N Bmul s
    hN hL (fun x hx => hf x ⟨hx.1.le,hx.2.le⟩)
    (fun x hx => (hthree x ⟨hx.1.le,hx.2.le⟩).1) hz hround hspan hmul
  have hmu i (hi : i∈S) : 0 < mu i ∧ mu i ≤ U := by
    have hh := hthree _ ⟨(hm i hi).1.le,(hm i hi).2.le⟩
    dsimp only [mu]
    constructor <;> linarith only [hh.1,hh.2,hL]
  have hrho : 0 ≤ rho := by dsimp only [rho]; positivity
  have hbeta ij (hij : ij∈R) :
      h (z ij.2)-h (z ij.1)=(M ij 1:ℝ) ∧ |(M ij 1:ℝ)| ≤ 3*U*(rho+1) := by
    have hi := (hRmem ij hij).1
    have hj := (hRmem ij hij).2
    have htri := bourgain_triangular_inverse_coordinate_equality
      (M ij 0) (M ij 1) (M ij 3) (p ij.1) (p ij.2) (r ij.1) (r ij.2)
      (q ij.1) (q ij.2) (hq ij.1 hi).1 (hq ij.2 hj).1
      (by simpa only [hzero ij hij,mul_zero,sub_zero] using hdet ij hij)
      (hmatp ij hij)
      (by simpa only [hzero ij hij,zero_mul,zero_add] using hmatq ij hij)
      (hinv ij.1 hi) (hinv ij.2 hj)
    have he : h (z ij.2)-h (z ij.1)=(M ij 1:ℝ) := by
      rw [hlevel ij.2 hj,hlevel ij.1 hi]
      exact htri.2.2
    refine ⟨he,?_⟩
    have hb := bourgain_upper_triangular_source_spacing f hlambda
      (m ij.1) (m ij.2) ⟨(hm ij.1 hi).1.le,(hm ij.1 hi).2.le⟩
      ⟨(hm ij.2 hj).1.le,(hm ij.2 hj).2.le⟩ hf hfour
      (p ij.1) (p ij.2) (r ij.1) (r ij.2) (q ij.1) (q ij.2)
      (hq ij.1 hi).1 (hq ij.2 hj).1 (hinv ij.1 hi) (hinv ij.2 hj)
      (eta:=0) (by rw [htri.2.1]; norm_num) (by simp)
      (hmu ij.1 hi).1 (hmu ij.1 hi).2 (hmu ij.2 hj).1 (hmu ij.2 hj).2 (hdual ij hij)
    have hdist : |(m ij.2:ℝ)-m ij.1| ≤ rho := by
      rw [abs_sub_comm]
      apply hb.2.2.trans
      have hqi : (q ij.1:ℝ) ≤ Q := by exact_mod_cast (hq ij.1 hi).2
      dsimp only [rho]
      gcongr
    have hzd : |z ij.2-z ij.1| ≤ rho+1 := by
      calc
        _ = |(z ij.2-m ij.2)+((m ij.2:ℝ)-m ij.1)+((m ij.1:ℝ)-z ij.1)| := by
          congr 1
          ring
        _ ≤ |z ij.2-m ij.2|+|(m ij.2:ℝ)-m ij.1|+|(m ij.1:ℝ)-z ij.1| :=
          abs_add_three _ _ _
        _ = |z ij.2-m ij.2|+|(m ij.2:ℝ)-m ij.1|+|z ij.1-m ij.1| := by
          rw [abs_sub_comm (m ij.1:ℝ)]
        _ ≤ 1/2+rho+1/2 := by gcongr; exact hround ij.2 hj; exact hround ij.1 hi
        _ = _ := by ring
    have hc := bourgain_curvature_level_difference f hf
      (fun x hx => ⟨hL.le.trans (hthree x hx).1,(hthree x hx).2⟩)
      ⟨(hz ij.2 hj).1.le,(hz ij.2 hj).2.le⟩ ⟨(hz ij.1 hi).1.le,(hz ij.1 hi).2.le⟩
    change |h (z ij.2)-h (z ij.1)| ≤ _ at hc
    rw [he] at hc
    exact hc.trans (mul_le_mul_of_nonneg_left hzd (by positivity))
  have hrow i (hi : i∈S) :
      ((S.filter (fun j => (i,j)∈R)).card:ℝ) ≤ (4*Bmul)*(1+6*U*(rho+1)) := by
    let T := S.filter (fun j => (i,j)∈R)
    let beta := fun j => M (i,j) 1
    let W := T.image beta
    have hW : (W.card:ℝ) ≤ 1+6*U*(rho+1) := by
      have hh := integer_card_le_of_abs_sub_le (a:=0) W
        (by positivity : 0 ≤ 3*U*(rho+1)) (by
          intro b hb
          obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hb
          simpa only [sub_zero] using (hbeta (i,j) (Finset.mem_filter.mp hj).2).2)
      linarith only [hh]
    have hfiber b : ((T.filter (fun j => beta j=b)).card:ℝ) ≤ 4*Bmul := by
      have hsub : T.filter (fun j => beta j=b) ⊆
          S.filter (fun j => h (z j)=(b:ℝ)+h (z i)) := by
        intro j hj
        obtain ⟨hj,hb⟩ := Finset.mem_filter.mp hj
        have hj' := Finset.mem_filter.mp hj
        have he := (hbeta (i,j) hj'.2).1
        change h (z j)-h (z i)=(beta j:ℝ) at he
        rw [hb] at he
        exact Finset.mem_filter.mpr ⟨hj'.1,by linarith only [he]⟩
      exact_mod_cast (Finset.card_le_card hsub).trans (hlevels ((b:ℝ)+h (z i)))
    have hcard : (T.card:ℝ)=∑ b∈W,((T.filter (fun j => beta j=b)).card:ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_fiberwise
        (fun j hj => Finset.mem_image_of_mem beta hj)
    calc
      _ = _ := hcard
      _ ≤ ∑ b∈W,(4*Bmul:ℝ) := Finset.sum_le_sum (fun b _ => hfiber b)
      _ = (4*Bmul:ℝ)*W.card := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hW (by positivity)
  have he : R=(S ×ˢ S).filter (fun ij => ij∈R) := by
    ext ij
    simp only [Finset.mem_filter]
    exact ⟨fun hij => ⟨hR hij,hij⟩,And.right⟩
  have hcard : (R.card:ℝ)=∑ i∈S,((S.filter (fun j => (i,j)∈R)).card:ℝ) := by
    conv_lhs => rw [he]
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter,Finset.sum_product,
      Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [hcard]
  calc
    _ ≤ ∑ i∈S,(4*Bmul:ℝ)*(1+6*U*(rho+1)) := Finset.sum_le_sum hrow
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

                                                                            
                                                                           
                                                                  
                                                                                
theorem bourgain_C4_two_coordinate_second_spacing
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ℝ → ℝ) (z : ι → ℝ) (m k p r : ι → ℤ) (q : ι → ℕ)
    (N Q Bmul : ℕ) (s : ℤ) {A B L F U X lambda eta zeta : ℝ}
    (hN : 0 < N) (hL : 0 < L) (hF : 0 ≤ F) (hU : 0 < U)
    (hX : 0 ≤ X) (hlambda : 0 < lambda) (heta : 0 ≤ eta) (hzeta : 0 ≤ zeta)
    (hFL : F ≤ L^2/16)
    (hf : ∀ x∈Icc A B, ContDiffAt ℝ 4 f x)
    (hthree : ∀ x∈Icc A B, L ≤ iteratedDeriv 3 f x ∧ iteratedDeriv 3 f x ≤ 6*U)
    (hfour : ∀ x∈Icc A B, lambda ≤ |iteratedDeriv 4 f x| ∧ |iteratedDeriv 4 f x| ≤ F)
    (hz : ∀ i∈S, z i∈Ioo A B) (hm : ∀ i∈S, (m i:ℝ)∈Ioo A B)
    (hround : ∀ i∈S, |z i-m i| ≤ 1/2)
    (hspan : ∀ i∈S, (N:ℤ) ≤ s+(N:ℤ)*k i-m i ∧
      s+(N:ℤ)*k i-m i ≤ 3*(N:ℤ))
    (hmul : ∀ j : ℤ, (S.filter (fun i => k i=j)).card ≤ Bmul)
    (hq : ∀ i∈S, 0 < q i ∧ q i ≤ Q ∧ Q ≤ 2*q i)
    (hinv : ∀ i∈S, (q i:ℤ) ∣ p i*r i-1) :
    let h := fun x => iteratedDeriv 2 f x/2
    let mu := fun i => iteratedDeriv 3 f (m i)/6
    let K := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let E := 16*U*Real.sqrt (U*(Q:ℝ)^3)*zeta+3*F/4
    let Gamma := eta*(Q:ℝ)^2
    let rho := (12*U*Real.sqrt (U*(Q:ℝ)^3)/lambda)*zeta
    (∀ i∈S, h (z i)=(p i:ℝ)/q i) →
    (∀ i∈S, |h (z i)| ≤ X) →
    (((S ×ˢ S).filter (fun ij =>
      |Int.fract (-(r ij.1:ℝ)/q ij.1)-Int.fract (-(r ij.2:ℝ)/q ij.2)| ≤ eta ∧
      |K ij.1-K ij.2| ≤ zeta)).card:ℝ) ≤
        4*Bmul*S.card*(1+6*U*(rho+1))+
        16*(Bmul:ℝ)^2*(2*Gamma+1)*(2*X+5)^2*
          (Gamma+48*E*(Q:ℝ)^2/L) := by
  classical
  intro h mu K E Gamma rho hlevel hlevelX
  let R := (S ×ˢ S).filter (fun ij =>
    |Int.fract (-(r ij.1:ℝ)/q ij.1)-Int.fract (-(r ij.2:ℝ)/q ij.2)| ≤ eta ∧
    |K ij.1-K ij.2| ≤ zeta)
  obtain ⟨M,hM,hcount⟩ := exists_bourgain_C4_nontriangular_second_spacing S f z m k p r q
    N Q Bmul s hN hL hF hU hX heta hzeta hFL
    (fun x hx => hf x ⟨hx.1.le,hx.2.le⟩)
    (fun x hx => hthree x ⟨hx.1.le,hx.2.le⟩)
    (fun x hx => (hfour x ⟨hx.1.le,hx.2.le⟩).2)
    hz hm hround hspan hmul hq hinv hlevel hlevelX
  let Z := R.filter (fun ij => M ij 2=0)
  let T := R.filter (fun ij => M ij 2 ≠ 0)
  have hZ ij (hij : ij∈Z) : ij∈R ∧ M ij 2=0 := Finset.mem_filter.mp hij
  have hzero := bourgain_C4_triangular_pair_count S Z f z m k p r q M N Q Bmul s
    hN hL hU hlambda hzeta hf hthree (fun x hx => (hfour x hx).1)
    hz hm hround hspan hmul (fun i hi => ⟨(hq i hi).1,(hq i hi).2.1⟩) hinv
    (fun ij hij => (Finset.mem_filter.mp (hZ ij hij).1).1)
    (fun ij hij => (hM ij (hZ ij hij).1).1)
    (fun ij hij => (hZ ij hij).2)
    (fun ij hij => (hM ij (hZ ij hij).1).2.1)
    (fun ij hij => (hM ij (hZ ij hij).1).2.2.1)
    hlevel (fun ij hij => (Finset.mem_filter.mp (hZ ij hij).1).2.2)
  have hcard : R.card=Z.card+T.card := by
    exact (Finset.card_filter_add_card_filter_not (s:=R) (p:=fun ij => M ij 2=0)).symm
  have hcardR : (R.card:ℝ)=(Z.card:ℝ)+(T.card:ℝ) := by exact_mod_cast hcard
  change (R.card:ℝ) ≤ _
  rw [hcardR]
  exact add_le_add hzero hcount

-- Generated closures: source context is replayed in the next part.
end TaoTrudgianYang2025
end
end
