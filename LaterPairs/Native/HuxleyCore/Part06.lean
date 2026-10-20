module
public import LaterPairs.Native.HuxleyCore.Part05

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxErrors 1000
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth
open Filter
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth
open Polynomial
open Set
open scoped Classical
open scoped ContDiff
open scoped FourierTransform BigOperators
open scoped Topology
open Filter
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth
open Polynomial
open Set
open scoped Classical
open scoped ContDiff
open scoped FourierTransform BigOperators
open scoped Topology
universe huxleyNarrowV
noncomputable section
namespace TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators FourierTransform Classical ContDiff NNReal
open Filter
open Set Expdb TaoTrudgianYang2025
open scoped BigOperators FourierTransform ContDiff Classical NNReal


public  theorem capped_short_nonAsymptotic_of_window_margins
    {α : ℝ≥0} {β h g₀ ν₀ ν₁ δw μ : ℝ}
    (hδw : 0<δw) (hμ : 0<μ)
    (hWindows : ∀ u : ℝ, u∈Icc (0:ℝ) 1 →
      let ℓ := (α:ℝ)-δw
      let v := (α:ℝ)+δw
      let g := fun u : ℝ => (1-u)*g₀+u*(3*h)
      let ν := fun u : ℝ => (1-u)*ν₀+u*ν₁
      μ≤ℓ ∧
        v+μ≤1 ∧
        μ≤h ∧
        μ≤(ν u) ∧
        μ≤g₀ ∧
        5*h+μ≤ℓ ∧
        g₀+μ≤3*h ∧
        (ν u)+μ≤ℓ ∧
        5*v-1-(g u)+μ≤3*(ν u) ∧
        1+(g u)+2*(ν u)+μ≤5*ℓ ∧
        4*(ν u)+1+(g u)+μ≤6*ℓ ∧
        (ν u)+3*v+μ≤1+(g u) ∧
        1+(g u)+μ≤4*ℓ ∧
        3*v+μ≤1+(g u) ∧
        7*v+μ≤2+2*(g u)+(ν u) ∧
        7+7*(g u)+27*(ν u)+μ≤41*ℓ ∧
        2*h+μ≤β ∧
        4*v+g₀-3*h+μ≤4*β ∧
        288*v-144*h+μ≤288*β ∧
        288*v-36*(ν u)+72*(g u)-216*h+μ≤288*β ∧
        648*v-72-216*h-216*(ν u)+μ≤288*β ∧
        24+96*(g u)-216*h+96*v+144*(ν u)+μ≤288*β ∧
        21+87*(g u)-216*h+177*v+33*(ν u)+μ≤288*β ∧
        15+87*(g u)-216*h+207*v+15*(ν u)+μ≤288*β ∧
        12+78*(g u)-216*h+216*v+24*(ν u)+μ≤288*β ∧
        6+78*(g u)-216*h+246*v+6*(ν u)+μ≤288*β ∧
        72*(g u)-216*h+284*v-24*(ν u)+μ≤288*β ∧
        504*v-72-216*h+72*(ν u)+μ≤288*β) :
    Expdb.IsExponentSumBoundNonAsymptotic α β := by
  let g := fun u : ℝ => (1-u)*g₀+u*(3*h)
  let ν := fun u : ℝ => (1-u)*ν₀+u*ν₁
  let ℓ := (α:ℝ)-δw
  let v := (α:ℝ)+δw
  let εs := μ/1000
  let ζ := μ/2
  let ξ := 288*β-μ
  have hεs : 0<εs := by dsimp only [εs]; positivity
  have hζ : 0<ζ := by dsimp only [ζ]; positivity
  have hMargins (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
      μ≤ℓ ∧
        v+μ≤1 ∧
        μ≤h ∧
        μ≤(ν u) ∧
        μ≤g₀ ∧
        5*h+μ≤ℓ ∧
        g₀+μ≤3*h ∧
        (ν u)+μ≤ℓ ∧
        5*v-1-(g u)+μ≤3*(ν u) ∧
        1+(g u)+2*(ν u)+μ≤5*ℓ ∧
        4*(ν u)+1+(g u)+μ≤6*ℓ ∧
        (ν u)+3*v+μ≤1+(g u) ∧
        1+(g u)+μ≤4*ℓ ∧
        3*v+μ≤1+(g u) ∧
        7*v+μ≤2+2*(g u)+(ν u) ∧
        7+7*(g u)+27*(ν u)+μ≤41*ℓ ∧
        2*h+μ≤β ∧
        4*v+g₀-3*h+μ≤4*β ∧
        288*v-144*h+μ≤288*β ∧
        288*v-36*(ν u)+72*(g u)-216*h+μ≤288*β ∧
        648*v-72-216*h-216*(ν u)+μ≤288*β ∧
        24+96*(g u)-216*h+96*v+144*(ν u)+μ≤288*β ∧
        21+87*(g u)-216*h+177*v+33*(ν u)+μ≤288*β ∧
        15+87*(g u)-216*h+207*v+15*(ν u)+μ≤288*β ∧
        12+78*(g u)-216*h+216*v+24*(ν u)+μ≤288*β ∧
        6+78*(g u)-216*h+246*v+6*(ν u)+μ≤288*β ∧
        72*(g u)-216*h+284*v-24*(ν u)+μ≤288*β ∧
        504*v-72-216*h+72*(ν u)+μ≤288*β := by
    exact hWindows u hu
  have hzero := hMargins 0 (by norm_num)
  simp only [g,ν,sub_zero,zero_mul,one_mul,add_zero] at hzero
  obtain ⟨hμℓ,hv,hμh,hμν₀,hμg₀,hWidth,hg₀h,hν₀M,hRN₀,hNR₀,hCubic₀,hCap₀,
    hHeight₀,hMT₀,hRT₀,hTen₀,hShort,hSmall,hDiag,hSqrt₀,hSecond₀,hFourth₀,
    hSecondMain₀,hFourthMain₀,hFirstMain₀,hThirdMain₀,hFifthMain₀,hThird₀⟩ := hzero
  have hℓv : ℓ≤v := by dsimp only [ℓ,v]; linarith only [hδw]
  have hhp := hμ.trans_le hμh
  have hℓp := hμ.trans_le hμℓ
  have hg₀p := hμ.trans_le hμg₀
  have hβ : 0<β := by linarith only [hShort,hhp,hμ]
  have hξ : 0≤ξ := by dsimp only [ξ]; linarith only [hShort,hhp,hμ]
  have hh3 : 3*h≤1 := by linarith only [hWidth,hℓv,hv,hhp,hμ]
  intro ε hε σ hσ
  obtain ⟨δsrc,w₀,B,Csrc,hδsrc,hw₀,hw₀cap,hB,hCsrc,hSource⟩ :=
    approximateModelPhase_enlarged_double_product_correlation_moment hσ hεs
  obtain ⟨A,hA,hWeylSource⟩ := source_product_twice_weyl_normalized_block hεs
  let Clarge := (2:ℝ)^364*A^72*Csrc^6*(11*2^432)
  let Csmall := (20*A)^72
  let D := 1+Clarge+Csmall
  let Ctotal := (2:ℝ)^287*((6:ℝ)^288+D)
  have hA0 := zero_le_one.trans hA
  have hCsrc0 := zero_le_one.trans hCsrc
  have hClarge : 0≤Clarge := by
    dsimp only [Clarge]
    clear * - hA0 hCsrc0
    positivity
  have hCsmall : 0≤Csmall := by
    dsimp only [Csmall]
    clear * - hA0
    positivity
  have hD : 1≤D := (le_add_of_nonneg_right hClarge).trans (le_add_of_nonneg_right hCsmall)
  have hLargeD : Clarge≤D :=
    (le_add_of_nonneg_left (by norm_num : (0:ℝ)≤1)).trans (le_add_of_nonneg_right hCsmall)
  have hSmallD : Csmall≤D := le_add_of_nonneg_left (add_nonneg zero_le_one hClarge)
  have hCtotal : 0≤Ctotal := by
    dsimp only [Ctotal]
    exact mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) 287)
      (add_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤6) 288) (zero_le_one.trans hD))
  have hPhys := eventually_double_difference_capped_physical_window
    hB hCsrc hw₀ hμ hμℓ hℓv hμh hWidth
  have hLog := middleOriginal_eventually_uniform_clog_power_loss_72 hCtotal hζ
  obtain ⟨X₀,hX₀⟩ := Filter.eventually_atTop.mp (hPhys.and hLog)
  let δ := min δsrc δw
  let C := max 1 X₀
  have hC : 1≤C := le_max_left _ _
  refine ⟨δ,lt_min hδsrc hδw,7,by norm_num,C,hC,?_⟩
  intro X M F a b setup
  have hTogether := hX₀ X ((le_max_right 1 X₀).trans setup.threshold_le_param)
  have hX2 := hTogether.1.1
  have hX : 1≤X := (by norm_num : (1:ℝ)≤2).trans hX2
  have hXp := zero_lt_one.trans_le hX
  have hMl : X^ℓ≤M :=
    (Real.rpow_le_rpow_of_exponent_le hX
      (sub_le_sub_left (min_le_right δsrc δw) _)).trans setup.rpow_sub_le_scale
  have hMu : M≤X^v := setup.scale_le_rpow_add.trans
    (Real.rpow_le_rpow_of_exponent_le hX (add_le_add le_rfl (min_le_right δsrc δw)))
  have hF := approximateModelPhase_mono setup.isApproximateModelPhase le_rfl (min_le_left δsrc δw)
  have hBasePhys := hTogether.1.2 M (X^g₀) g₀ ν₀ hMl hMu rfl hg₀p.le
    (by linarith only [hg₀h,hμ]) hμν₀ hν₀M hRN₀ hNR₀ hCubic₀ hCap₀ hHeight₀ hMT₀ hRT₀ hTen₀
  let H := ⌊X^h⌋₊
  obtain ⟨hM,hN₀2,hH2,hN₀l,hN₀u,hHl,hHu,hJ₀,hR₀,hscale₀,hThreshold₀,hW,
    hJ₀M,hWJ₀,hR₀B,hR₀N,hN₀R,hN₀M,hCubicBudget₀,hCapBudget₀,hHeightBudget₀,
    hMTBudget₀,hRTBudget₀,hTenBudget₀⟩ := hBasePhys
  have hMp := zero_lt_one.trans_le hM
  have hHp : (0:ℝ)<H := by exact_mod_cast (show 0<H by omega)
  have hH1 : (1:ℝ)≤H := by exact_mod_cast (show 1≤H by omega)
  have hHcube : (H:ℝ)^3≤X := by
    calc
      _ ≤ (X^h)^3 := pow_le_pow_left₀ hHp.le hHu 3
      _ = X^(3*h) := by
        simpa only [Nat.cast_ofNat,mul_comm] using (Real.rpow_mul_natCast hXp.le h 3).symm
      _ ≤ X := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX hh3
  suffices hResult : ‖Expdb.exponentialSumAt F X M a b‖≤X^β by
    calc
      _ ≤ X^β := hResult
      _ ≤ X^(β+ε) := Real.rpow_le_rpow_of_exponent_le hX (le_add_of_nonneg_right hε.le)
      _ ≤ C*X^(β+ε) := le_mul_of_one_le_left (Real.rpow_nonneg hXp.le _) hC
  by_cases hba : b<a
  · rw [Expdb.exponentialSumAt_of_lt hba,norm_zero]
    exact Real.rpow_nonneg hXp.le _
  have hab : a≤b := Nat.le_of_not_gt hba
  let L := b-a
  have hEnd : a+L=b := Nat.add_sub_of_le hab
  have ha := setup.scale_le_start
  have hb : ((a+L:ℕ):ℝ)≤2*M := by rw [hEnd]; exact setup.end_le_two_mul_scale
  by_cases hShortL : L+1<H^2
  · calc
      _ ≤ ((Finset.Icc a b).card:ℝ) := Expdb.norm_exponentialSumAt_le_card F X M a b
      _ = (L:ℝ)+1 := by
        have hc : (Finset.Icc a b).card=L+1 := by rw [Nat.card_Icc]; dsimp only [L]; omega
        exact_mod_cast hc
      _ ≤ (H:ℝ)^2 := by exact_mod_cast hShortL.le
      _ ≤ (X^h)^2 := pow_le_pow_left₀ hHp.le hHu 2
      _ = X^(2*h) := by
        simpa only [Nat.cast_ofNat,mul_comm] using (Real.rpow_mul_natCast hXp.le h 2).symm
      _ ≤ X^β := Real.rpow_le_rpow_of_exponent_le hX (by linarith only [hShort,hμ])
  have hLong : H^2≤L+1 := Nat.le_of_not_gt hShortL
  obtain ⟨Fext,hSharp,hFamily⟩ := hSource M F hM hF
  obtain ⟨pick,k,hk,hkH,hpick,hZcap,hWeyl⟩ :=
    hWeylSource Fext σ X M a L H hσ hX hM hH2 hLong hHcube (hW.trans hw₀cap) ha hb
  let J := (k:ℝ)
  let Pairs := (Finset.Icc 1 (H-1)) ×ˢ (Finset.Icc 1 (H^2-1))
  let Products := Pairs.image (fun p => p.1*p.2)
  let W := fun p : ℕ × ℕ => ∑ j∈Finset.range (L+1-p.1-p.2),
    (𝐞 (X*(Fext (((a:ℝ)+j)/M)-Fext (((a:ℝ)+j+p.1)/M)-
      Fext (((a:ℝ)+j+p.2)/M)+Fext (((a:ℝ)+j+p.1+p.2)/M))):ℂ)
  let Z := ∑ l∈(Finset.Ico k (2*k)).filter (fun l => l∈Products),‖W (pick l)‖
  let Log := 1+(Nat.clog 2 (H^3):ℝ)
  have hZ0 : 0≤Z := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hLog1 : 1≤Log := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hLog0 := zero_le_one.trans hLog1
  have hLog72 : 1≤Log^72 := one_le_pow₀ hLog1
  have hJp : 0<J := by change (0:ℝ)<k; exact_mod_cast hk
  have hJH : J≤(H:ℝ)^3 := by
    change (k:ℝ)≤(H:ℝ)^3
    exact_mod_cast (show k≤H^3 by omega)
  have hQ : 0≤A*X^εs*Log :=
    mul_nonneg (mul_nonneg hA0 (Real.rpow_nonneg hXp.le _)) hLog0
  have hξPower : 1≤X^ξ := Real.one_le_rpow hX hξ
  have hLossPower : 1≤X^(78*εs) := Real.one_le_rpow hX (by positivity)
  have hCommon :
      ‖Expdb.exponentialSumAt Fext X M a (a+L)‖^288 ≤ D*Log^72*X^(78*εs)*X^ξ := by
    by_cases hSmallJ : J≤X^g₀
    · have hdPower : M^4/(H:ℝ)^2≤4*X^(ξ/72) := by
        have hh := double_difference_monomial_power_window hX hMl hMu hN₀l hN₀u hHl
          (rfl : X^g₀=X^g₀) 0 0 4 0 0 2 0 0 0
        norm_num only [Nat.cast_zero,Nat.cast_ofNat,pow_zero,pow_one,zero_mul,one_mul,
          mul_one,zero_add,add_zero,sub_zero] at hh
        have hexp : 4*v-2*h≤ξ/72 := by
          apply (le_div_iff₀ (by norm_num : (0:ℝ)<72)).mpr
          calc
            (4*v-2*h)*72 = 288*v-144*h := by ring
            _ ≤ 288*β-μ := (le_sub_iff_add_le).mpr hDiag
        exact hh.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hX hexp)
          (by norm_num))
      have hSmallPower : M^4*J/(H:ℝ)^3≤8*X^(ξ/72) := by
        have hh := double_difference_monomial_power_window hX hMl hMu hN₀l hN₀u hHl
          (rfl : X^g₀=X^g₀) 0 1 4 0 0 3 0 0 0
        norm_num only [Nat.cast_zero,Nat.cast_ofNat,pow_zero,pow_one,zero_mul,one_mul,
          mul_one,zero_add,add_zero,sub_zero] at hh
        calc
          _ ≤ M^4*(X^g₀)/(H:ℝ)^3 := by gcongr
          _ = (X^g₀)*M^4/(H:ℝ)^3 := by rw [mul_comm (M^4)]
          _ ≤ 8*X^(g₀+4*v-3*h) := hh
          _ ≤ 8*X^(ξ/72) := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hX (by
              apply (le_div_iff₀ (by norm_num : (0:ℝ)<72)).mpr
              calc
                (g₀+4*v-3*h)*72 = (4*v+g₀-3*h)*72 := by ring
                _ ≤ (4*β-μ)*72 := mul_le_mul_of_nonneg_right
                  ((le_sub_iff_add_le).mpr hSmall) (by norm_num)
                _ ≤ 288*β-μ := by nlinarith only [hμ])) (by norm_num)
      have hCorr : (M^3/(H:ℝ)^3)*Z≤16*X^(ξ/72) := by
        calc
          _ ≤ (M^3/(H:ℝ)^3)*(2*M*J) := mul_le_mul_of_nonneg_left hZcap (by positivity)
          _ = 2*(M^4*J/(H:ℝ)^3) := by ring
          _ ≤ 2*(8*X^(ξ/72)) := mul_le_mul_of_nonneg_left hSmallPower (by norm_num)
          _ = _ := by ring
      have hFourth :
          ‖Expdb.exponentialSumAt Fext X M a (a+L)‖^4≤
            (20*A)*Log*X^εs*X^(ξ/72) := by
        calc
          _ ≤ A*X^εs*Log*(M^4/(H:ℝ)^2+(M^3/(H:ℝ)^3)*Z) := hWeyl
          _ ≤ A*X^εs*Log*(4*X^(ξ/72)+16*X^(ξ/72)) :=
            mul_le_mul_of_nonneg_left (add_le_add hdPower hCorr) hQ
          _ = _ := by ring
      have hpε : (X^εs)^72=X^(72*εs) := by
        simpa only [Nat.cast_ofNat,mul_comm] using (Real.rpow_mul_natCast hXp.le εs 72).symm
      have hpξ : (X^(ξ/72))^72=X^ξ := by
        have hh := (Real.rpow_mul_natCast hXp.le (ξ/72) 72).symm
        norm_num only [Nat.cast_ofNat,div_mul_cancel₀ _ (by norm_num : (72:ℝ)≠0)] at hh
        exact hh
      calc
        _ = (‖Expdb.exponentialSumAt Fext X M a (a+L)‖^4)^72 := by rw [←pow_mul]
        _ ≤ ((20*A)*Log*X^εs*X^(ξ/72))^72 :=
          pow_le_pow_left₀ (pow_nonneg (norm_nonneg _) 4) hFourth 72
        _ = Csmall*Log^72*X^(72*εs)*X^ξ := by
          simp only [mul_pow,hpε,hpξ,Csmall]
        _ ≤ D*Log^72*X^(78*εs)*X^ξ := by
          gcongr
          norm_num
    · let γ := Real.logb X J
      have hXgt : 1<X := by linarith only [hX2]
      have hJpow : J=X^γ := (Real.rpow_logb hXp hXgt.ne' hJp).symm
      have hγlo : g₀≤γ :=
        (Real.le_logb_iff_rpow_le hXgt hJp).mpr (le_of_not_ge hSmallJ)
      have hγhi : γ≤3*h := by
        apply (Real.logb_le_iff_le_rpow hXgt hJp).mpr
        calc
          J ≤ (H:ℝ)^3 := hJH
          _ ≤ (X^h)^3 := pow_le_pow_left₀ hHp.le hHu 3
          _ = X^(3*h) := by
            simpa only [Nat.cast_ofNat,mul_comm] using (Real.rpow_mul_natCast hXp.le h 3).symm
      have hDen : 0<3*h-g₀ := by linarith only [hg₀h,hμ]
      let u := (γ-g₀)/(3*h-g₀)
      have hu : u∈Icc (0:ℝ) 1 := by
        refine ⟨div_nonneg (sub_nonneg.mpr hγlo) hDen.le,?_⟩
        exact (div_le_one hDen).mpr (by linarith only [hγhi])
      have hgu : g u=γ := by
        dsimp only [g,u]
        field_simp
        ring
      have hm := hMargins u hu
      rw [hgu] at hm
      obtain ⟨_,_,_,hμν,_,_,_,hνM,hRN,hNR,hCubic,hCap,hHeight,hMT,hRT,hTen,
        _,_,hDiag',hSqrt,hSecond,hFourth,hSecondMain,hFourthMain,hFirstMain,hThirdMain,hFifthMain,hThird⟩ := hm
      let n := ⌊X^(ν u)/8⌋₊
      let N := 8*n
      let R := Real.sqrt (M^5/(X*J*(N:ℝ)))
      let T := X*J/M^2
      have hPhysical := hTogether.1.2 M J γ (ν u) hMl hMu hJpow
        (hg₀p.le.trans hγlo) hγhi hμν hνM hRN hNR hCubic hCap hHeight hMT hRT hTen
      obtain ⟨_,hN2,_,hNl,hNu,_,_,hJ1,hRp,hscale,hThreshold,hWidthJ,hJM,hWJ,
        hBR,hRNbudget,hNRbudget,hNMbudget,hCubicBudget,hCapBudget,hHeightBudget,
        hMTbudget,hRTbudget,hTenBudget⟩ := hPhysical
      have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
      have hTp : 0<T := by dsimp only [T]; positivity
      have hTX : T≤X := by
        apply (div_le_iff₀ (sq_pos_of_pos hMp)).mpr
        have hJM2 : J≤M^2 := hJM.trans (by nlinarith only [hM])
        nlinarith only [mul_le_mul_of_nonneg_left hJM2 hXp.le]
      let E := J*M/Real.sqrt (N:ℝ)+J*M*R^2/(N:ℝ)^2+J*(N:ℝ)^2*R^2/M+
        J*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
      let Main := J^11*M^10*(N:ℝ)^2/R^4+J^11*M^11*(N:ℝ)^2/R^7+
        J^11*J*M^10/R^2+J^11*J*M^11/R^5+
        J^12*M^10*R^2/(N:ℝ)^2*(R/(N:ℝ))^((2:ℝ)/3)*((X*J/M^2)/M^2)^((4:ℝ)/3)
      let V :=
        (J^72*M^288/((H:ℝ)^216*(N:ℝ)^36)+M^648/(X^72*(H:ℝ)^216*(N:ℝ)^216)+
          M^504*(N:ℝ)^72/(X^72*(H:ℝ)^216)+X^24*J^96*M^96*(N:ℝ)^144/(H:ℝ)^216)+
        (X^12*J^78*M^216*(N:ℝ)^24/(H:ℝ)^216+X^21*J^87*M^177*(N:ℝ)^33/(H:ℝ)^216+
          X^6*J^78*M^246*(N:ℝ)^6/(H:ℝ)^216+X^15*J^87*M^207*(N:ℝ)^15/(H:ℝ)^216+
          J^72*M^284/((H:ℝ)^216*(N:ℝ)^24))
      have hE0 : 0≤E := by
        dsimp only [E]
        clear * - hJp hMp hNp hRp
        positivity
      have hMain0 : 0≤Main := by
        dsimp only [Main]
        clear * - hJp hMp hNp hRp hXp
        positivity
      have hFamilyMoment : Z^12≤Csrc*T^εs*(Main+E^12) := by
        exact hFamily X n N a L H (H^2) k R hThreshold rfl hN2 hBR hk
          (by simpa only [Nat.cast_pow] using hWidthJ) hJM
          (by simpa only [Nat.cast_pow] using hWJ) ha hb hscale
          hRNbudget hNRbudget hNMbudget hCubicBudget hCapBudget hHeightBudget
          hMTbudget hRTbudget hTenBudget pick (fun l hl => ⟨(hpick l hl).1,(hpick l hl).2.1⟩)
      have hMoment : Z^12≤Csrc*X^εs*(Main+E^12) := hFamilyMoment.trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hTp.le hTX hεs.le) hCsrc0)
          (add_nonneg hMain0 (pow_nonneg hE0 12)))
      have hWeighted : (M^3/(H:ℝ)^3)^72*(E^72+Main^6)≤(2:ℝ)^288*V :=
        double_difference_weighted_capped_integer_moments hXp hMp hNp hJp hHp hRp hscale
      have hPower := double_difference_fourth_twelfth_moment_assembly
        (norm_nonneg _) hZ0 (div_nonneg (pow_nonneg hMp.le 4) (pow_nonneg hHp.le 2))
        (div_nonneg (pow_nonneg hMp.le 3) (pow_nonneg hHp.le 3)) hMain0 hE0 hCsrc hX hεs.le hQ
        hWeyl hMoment hWeighted
      have hPoly : 1+(M^288/(H:ℝ)^144+V)≤(11*(2:ℝ)^432)*X^ξ :=
        double_difference_ten_monomials_power_window hX hξ hMl hMu hNl hNu hHl hJpow
          (by dsimp only [ξ]; linarith only [hDiag'])
          (by dsimp only [ξ]; linarith only [hSqrt])
          (by dsimp only [ξ]; linarith only [hSecond])
          (by dsimp only [ξ]; linarith only [hThird])
          (by dsimp only [ξ]; linarith only [hFourth])
          (by dsimp only [ξ]; linarith only [hFirstMain])
          (by dsimp only [ξ]; linarith only [hSecondMain])
          (by dsimp only [ξ]; linarith only [hThirdMain])
          (by dsimp only [ξ]; linarith only [hFourthMain])
          (by dsimp only [ξ]; linarith only [hFifthMain])
      have hPoly' : M^288/(H:ℝ)^144+V≤(11*(2:ℝ)^432)*X^ξ :=
        (le_add_of_nonneg_left (by norm_num : (0:ℝ)≤1)).trans hPoly
      have hPowers :
          (2:ℝ)^364*(A*X^εs*Log)^72*Csrc^6*X^(6*εs)*
              ((M^4/(H:ℝ)^2)^72+V)=
            ((2:ℝ)^364*A^72*Csrc^6)*Log^72*X^(78*εs)*(M^288/(H:ℝ)^144+V) := by
        simp only [mul_pow,div_pow,←pow_mul]
        have hεpower : (X^εs)^72=X^(72*εs) := by
          simpa only [Nat.cast_ofNat,mul_comm] using (Real.rpow_mul_natCast hXp.le εs 72).symm
        rw [hεpower]
        have hcombine : X^(72*εs)*X^(6*εs)=X^(78*εs) := by
          rw [←Real.rpow_add hXp]
          congr 1
          ring
        have heq (a b c d e f z : ℝ) : a*(b*c*d)*e*f*z=(a*b*e)*d*(c*f)*z := by ring
        rw [heq,hcombine]
      calc
        _ ≤ ((2:ℝ)^364*A^72*Csrc^6)*Log^72*X^(78*εs)*(M^288/(H:ℝ)^144+V) :=
          hPower.trans_eq hPowers
        _ ≤ ((2:ℝ)^364*A^72*Csrc^6)*Log^72*X^(78*εs)*((11*(2:ℝ)^432)*X^ξ) :=
          mul_le_mul_of_nonneg_left hPoly' (by
            clear * - hA0 hCsrc0 hLog0 hXp
            positivity)
        _ = Clarge*Log^72*X^(78*εs)*X^ξ := by
          dsimp only [Clarge]
          have heq (a b c d e f z : ℝ) : (a*b*c)*d*e*(f*z)=(a*b*c*f)*d*e*z := by ring
          exact heq _ _ _ _ _ _ _
        _ ≤ D*Log^72*X^(78*εs)*X^ξ := by gcongr
  have hSharp' := hSharp X a (a+L) ha hb
  have hOriginal : ‖Expdb.exponentialSumAt F X M a (a+L)‖≤
      6+‖Expdb.exponentialSumAt Fext X M a (a+L)‖ :=
    (norm_le_norm_sub_add _ _).trans (add_le_add hSharp' le_rfl)
  have hY : 1≤Log^72*X^(78*εs)*X^ξ :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hLog72 hLossPower) hξPower
  have hSix : (6:ℝ)^288≤(6:ℝ)^288*(Log^72*X^(78*εs)*X^ξ) :=
    le_mul_of_one_le_right (pow_nonneg (by norm_num : (0:ℝ)≤6) 288) hY
  have hFinalPower : ‖Expdb.exponentialSumAt F X M a (a+L)‖^288≤X^(288*β) := by
    have hLogLoss : Ctotal*Log^72≤X^ζ :=
      hTogether.2 (H^3)
        ((by norm_num : (2:ℕ)≤2^3).trans (Nat.pow_le_pow_left (show 2≤H from hH2) 3))
        (by exact_mod_cast hHcube)
    calc
      _ ≤ (6+‖Expdb.exponentialSumAt Fext X M a (a+L)‖)^288 :=
        pow_le_pow_left₀ (norm_nonneg _) hOriginal 288
      _ ≤ (2:ℝ)^287*((6:ℝ)^288+‖Expdb.exponentialSumAt Fext X M a (a+L)‖^288) :=
        add_pow_le (by norm_num : (0:ℝ)≤6) (norm_nonneg _) 288
      _ ≤ (2:ℝ)^287*((6:ℝ)^288*(Log^72*X^(78*εs)*X^ξ)+
          D*Log^72*X^(78*εs)*X^ξ) :=
        mul_le_mul_of_nonneg_left (add_le_add hSix hCommon)
          (pow_nonneg (by norm_num : (0:ℝ)≤2) 287)
      _ = (Ctotal*Log^72)*X^(78*εs)*X^ξ := by
        dsimp only [Ctotal]
        have heq (a b c d e f : ℝ) : a*(b*(d*e*f)+c*d*e*f)=((a*(b+c))*d)*e*f := by ring
        exact heq _ _ _ _ _ _
      _ ≤ X^ζ*X^(78*εs)*X^ξ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hLogLoss (Real.rpow_nonneg hXp.le _))
          (Real.rpow_nonneg hXp.le _)
      _ = X^(ζ+78*εs+ξ) := by rw [←Real.rpow_add hXp,←Real.rpow_add hXp]
      _ ≤ X^(288*β) := Real.rpow_le_rpow_of_exponent_le hX (by
        dsimp only [ζ,εs,ξ]
        linarith only [hμ])
  have hRootPower : (X^β)^288=X^(288*β) := by
    simpa only [Nat.cast_ofNat,mul_comm] using (Real.rpow_mul_natCast hXp.le β 288).symm
  rw [←hEnd]
  exact le_of_pow_le_pow_left₀ (by norm_num : (288:ℕ)≠0)
    (Real.rpow_nonneg hXp.le _) (hFinalPower.trans_eq hRootPower.symm)


private theorem fourth_pair_capped_short_nonAsymptotic
    {α : ℝ≥0} {t : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (hα : (α:ℝ)=(1-t)*(890/3277)+t*(17604372/60424193)) :
    Expdb.IsExponentSumBoundNonAsymptotic α (89/3478+(7441/8695)*(α:ℝ)) := by
  let h := ((1-t)*2749411+t*3296917)/100000000
  let g₀ := ((1-t)*16756+t*1976824)/100000000
  let ν₀ := ((1-t)*11931645+t*14567321)/100000000
  let ν₁ := ((1-t)*11969967+t*14925729)/100000000
  let g := fun u : ℝ => (1-u)*g₀+u*(3*h)
  let ν := fun u : ℝ => (1-u)*ν₀+u*ν₁
  let β := 89/3478+(7441/8695)*(α:ℝ)
  let δw := (1:ℝ)/10000000000
  let ℓ := (α:ℝ)-δw
  let v := (α:ℝ)+δw
  let μ := (1:ℝ)/1000000
  have hμ : 0<μ := by norm_num [μ]
  have hδw : 0<δw := by norm_num [δw]
  have hMargins (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
      μ≤ℓ ∧
        v+μ≤1 ∧
        μ≤h ∧
        μ≤(ν u) ∧
        μ≤g₀ ∧
        5*h+μ≤ℓ ∧
        g₀+μ≤3*h ∧
        (ν u)+μ≤ℓ ∧
        5*v-1-(g u)+μ≤3*(ν u) ∧
        1+(g u)+2*(ν u)+μ≤5*ℓ ∧
        4*(ν u)+1+(g u)+μ≤6*ℓ ∧
        (ν u)+3*v+μ≤1+(g u) ∧
        1+(g u)+μ≤4*ℓ ∧
        3*v+μ≤1+(g u) ∧
        7*v+μ≤2+2*(g u)+(ν u) ∧
        7+7*(g u)+27*(ν u)+μ≤41*ℓ ∧
        2*h+μ≤β ∧
        4*v+g₀-3*h+μ≤4*β ∧
        288*v-144*h+μ≤288*β ∧
        288*v-36*(ν u)+72*(g u)-216*h+μ≤288*β ∧
        648*v-72-216*h-216*(ν u)+μ≤288*β ∧
        24+96*(g u)-216*h+96*v+144*(ν u)+μ≤288*β ∧
        21+87*(g u)-216*h+177*v+33*(ν u)+μ≤288*β ∧
        15+87*(g u)-216*h+207*v+15*(ν u)+μ≤288*β ∧
        12+78*(g u)-216*h+216*v+24*(ν u)+μ≤288*β ∧
        6+78*(g u)-216*h+246*v+6*(ν u)+μ≤288*β ∧
        72*(g u)-216*h+284*v-24*(ν u)+μ≤288*β ∧
        504*v-72-216*h+72*(ν u)+μ≤288*β := by
    have hh := fourth_pair_capped_full_window_margins ht hu
    dsimp only at hh
    rw [←hα] at hh
    exact hh
  exact capped_short_nonAsymptotic_of_window_margins hδw hμ hMargins

                                                                  
                                                                      
                                                              
theorem exponentSumGrowthExponent_le_huxley_fourthPair_shortRange
    {α : ℝ≥0} (hα : (890:ℝ)/3277≤(α:ℝ))
    (hα₁ : (α:ℝ)≤(17604372:ℝ)/60424193) :
    Expdb.exponentSumGrowthExponent α≤89/3478+(7441/8695)*(α:ℝ) := by
  let t := ((α:ℝ)-(890:ℝ)/3277)/((17604372:ℝ)/60424193-(890:ℝ)/3277)
  have hden : 0<(17604372:ℝ)/60424193-(890:ℝ)/3277 := by norm_num
  have ht : t∈Icc (0:ℝ) 1 := by
    refine ⟨div_nonneg (sub_nonneg.mpr hα) hden.le,?_⟩
    exact (div_le_one hden).mpr (by linarith only [hα₁])
  have hαeq : (α:ℝ)=(1-t)*(890/3277)+t*(17604372/60424193) := by
    dsimp only [t]
    ring
  exact Expdb.exponentSumGrowthExponent_le_iff_nonAsymptotic.mpr
    (fourth_pair_capped_short_nonAsymptotic ht hαeq)


                                                                                 

abbrev nativeHuxleyCore_capped_short_nonAsymptotic_of_window_margins := @capped_short_nonAsymptotic_of_window_margins

end TaoTrudgianYang2025.HuxleyRationalPhase

-- Generated closures: source context is replayed in the next part.
end
end
