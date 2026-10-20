module
public import LaterPairs.Native.HuxleyCore.Part04

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


private theorem eventually_double_difference_actual_family_physical_sieve
    {csrc Usrc E σ εloss : ℝ}
    (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hE : 0 < E) (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let L := max (32*Usrc^2/csrc^2)
      (64*(modelPhaseJetCoefficient σ 3+1)*Usrc*E/κ^2)
    let θ := 1/(8*(L+3))
    ∃ C Dtype : ℝ, 0 < C ∧ 0 < Dtype ∧
    ∀ {Jref : ℝ}, 0 ≤ Jref →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (S : Finset (ℝ × ℤ)) (Fsrc rshift sshift : ℝ → ℝ)
    (z : (ℝ × ℤ) → ℝ) (rat : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ) (Nlen : (ℝ × ℤ) → ℕ)
    (Q K₀ N : ℕ) [NeZero K₀] (R Jsep : ℝ) (Z : ℝ → ℤ)
    {d Wmax Tsrc M δ Bcut Bselect : ℝ}
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ))
    (A : ℝ → ℤ) (W : ℝ → ℝ) (gap : (ℝ × ℤ) → ℝ × ℝ)
    (anchor : (ℝ × ℤ) → ℚ) (e r vRef s : ℝ × ℝ → ℤ),
    let lambda := csrc*Tsrc/(2*M^2)
    let Uband := Usrc*Tsrc/M^2
    let Vscale := max 1 (Uband*(N:ℝ)/(Q:ℝ))
    (0 < d) → (0 ≤ Wmax) → (Wmax ≤ 1/4) → (2*Usrc*Wmax ≤ csrc/64) →
    (0 < Tsrc) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (Tsrc ≤ E*T) →
    (0 < Q) → (Uband ≤ 1) →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Icc M (2*M)) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, csrc ≤ iteratedDeriv 5 Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3,
      csrc ≤ |(iteratedDeriv 5 Fsrc w)^2-iteratedDeriv 4 Fsrc w*iteratedDeriv 6 Fsrc w|) →
    (∀ i∈S, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) →
    (∀ i∈S, ((rat i).den:ℤ) ∣ (rat i).num*v i-1) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (2 ≤ M) →
    (0 < N) →
    (0 < Jsep) → (Jsep ≤ M) → ((N:ℝ) ≤ M) → (Wmax*Jsep ≤ 1) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i∈S, N ≤ Nlen i ∧ Nlen i ≤ 3*N ∧
      round (z i)+(Nlen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    (∀ y∈S.image Prod.fst,
      0 ≤ rshift y ∧ 0 ≤ sshift y ∧ rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
    let Φ := fun y u =>
      (Fsrc u-Fsrc (u+rshift y)-Fsrc (u+sshift y)+Fsrc (u+rshift y+sshift y))/d
    let Fmodel := fun (i : ℝ × ℤ) u => (Tsrc/T)*Φ i.1 u
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 4 δ) →
    let f := fun p w => Tsrc*Φ p (w/M)
    (∀ i∈S, iteratedDeriv 2 (f (i.1)) (z i)/2=(rat i:ℝ)) →
    (∀ i∈S, 1 ≤ Nlen i ∧ (rat i).den ≤ Nlen i ∧
      1 ≤ (iteratedDeriv 3 (f (i.1)) (round (z i))/6)*((rat i).den:ℝ)^2*Nlen i) →
    (∀ i∈S, 7*((iteratedDeriv 3 (f (i.1)) (round (z i))/6)*
      ((rat i).den:ℝ)*(Nlen i:ℝ)^2) ≤ K₀) →

    (1 ≤ R) → (R ≤ M) → (T*(N:ℝ)*R^2=M^3) →
    (∀ i∈S, M ≤ A i.1) → (∀ i∈S, A i.1+W i.1 ≤ 2*M) →
    let xlocal := fun i : ℝ × ℤ => z i-(A i.1:ℝ)
    (∀ i∈S, xlocal i∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, gap i∈Gaps) →
    (∀ ab∈Gaps, (vRef ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) → (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((vRef ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ i∈S, xlocal i-(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (1 ≤ Uref) →
    (2+168/κ ≤ Bselect) → (7*Bcut ≤ κ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ i∈S, (rat i:ℝ)∈Icc (gap i).1 (gap i).2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((vRef ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ i∈S, xlocal i-H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    let ε := κ/(16*(Cphys+2)*R^2)
    (∀ i∈S, |(anchor i:ℝ)-(rat i:ℝ)| ≤ ε) →
    (∀ i∈S, 256*((anchor i).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ i∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor i).den) →
    let narrow := fun (i : ℝ × ℤ) =>
      (⌊((rat i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
       ⌊((rat i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    let qell := fun (i : ℝ × ℤ) => ((rat i).den:ℝ)*deriv (f (i.1)) (round (z i))
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let offset := fun ip : (ℝ × ℤ) × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : (ℝ × ℤ) × Fin 2 => (narrow ip.1,offset ip)
    let NarrowCap := (4/θ+3)*(8*Usrc/(csrc*θ)+3)
    let Cap := 3*NarrowCap

    let q := fun (i : ℝ × ℤ) => (rat i).den
    let μ := fun (i : ℝ × ℤ) => iteratedDeriv 3 (f (i.1)) (round (z i))/6
    let b := fun ip : (ℝ × ℤ) × Fin 2 => (⌊qell ip.1⌋+(ip.2:ℕ) : ℤ)
    let tau := fun ip : (ℝ × ℤ) × Fin 2 => ((b ip:ℝ)-qell ip.1)/2
    let dual := fun (i : ℝ × ℤ) => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![-(v ip.1:ℝ)*b ip/q ip.1,-(v ip.1:ℝ)/q ip.1,
        dual ip.1,3*dual ip.1*tau ip/2] : Fin 4 → ℝ)
    let Fiber := fun key => V.filter (fun ip => color ip=key)
    let μ₀ := csrc*Tsrc/(12*M^3)
    let U₀ := Usrc*Tsrc/(2*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Klarge := 60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain*((Q:ℝ)/(Uband*(N:ℝ)))^((2:ℝ)/3)+Ctail/(Uref:ℝ))
    let Y := S.image Prod.fst
    let Values := fun k : ZMod K₀ =>
      ∑ ip∈V, ‖∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x ip d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖
    let Wphys := (144*Usrc/(csrc*κ))*(R^2/(Q:ℝ))
    let WeightedValues := fun k : ZMod K₀ =>
      ∑ ip∈V, (Real.sqrt (2*(q ip.1:ℝ))/((q ip.1:ℝ)*Real.sqrt (μ ip.1*(Nlen ip.1:ℝ))))*
        ‖∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
          GafniTao.fordAdditiveCharacter (∑ d,x ip d*
            (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
              Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖
    let Mass := Vscale*Dtype*(2+θ*(Uband+1/lambda))*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
      (Y.card:ℝ)^2*Klarge*T^εloss
    ((V.image color).card:ℝ) ≤ Cap ∧
      (∀ k, (Values k)^12 ≤ C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
        ∑ key∈V.image color, ((Fiber key).card:ℝ)^10*Mass) ∧
      (V.card:ℝ) ≤ 10*(Y.card:ℝ)*(M/(N:ℝ)) ∧
      (∀ k, (Values k)^12 ≤ C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
        (10*(Y.card:ℝ)*(M/(N:ℝ)))^10*Mass) ∧
      ∀ k, ((WeightedValues k)^12 ≤ Wphys^6*
        (C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(V.card:ℝ)^10*Mass)) ∧
        (WeightedValues k)^12 ≤ Wphys^6*
          (C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(10*(Y.card:ℝ)*(M/(N:ℝ)))^10*Mass) := by
  classical
  intro κ L θ
  obtain ⟨C,Dtype,hC,hDtype,hsource⟩ :=
    eventually_double_difference_actual_family_source_sieve hcsrc hUsrc hE hσ hεloss
  refine ⟨C,Dtype,hC,hDtype,?_⟩
  intro Jref hJref
  filter_upwards [hsource hJref] with T hfamily
  intro S Fsrc rshift sshift z rat v Nlen Q K₀ N instK R Jsep Z
    d Wmax Tsrc M δ Bcut Bselect Uref Refs Gaps A W gap anchor e r vRef s
    lambda Uband Vscale hd hw hwcap hsmallShift hTsrc hT hM hδ hsourceScale hQ hUbandCap
    hy hz hreg hlower hjets htests hden hinv hnegative hMtwo hN
    hJsep hJM hNM hwJ hmesh hgeometry hseparation hshifts Φ Fmodel hmodel f hlevel hminor hcomplete
    hR hRM hscale hA hW xlocal hx hgapMem
    hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
    hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
    hselectedUpper hscaleTen hfamilyGap hgap hQN hNsqM hUR
    hrHeight hsHeight heHeight hvHeight Cphys c J B hsmall hNR hRN hNcube hminscale
    H hNtwo hLeft hRight ε hanchor hcut hcount
    narrow qell V offset color NarrowCap Cap q μ b tau dual x Fiber μ₀ U₀ Δtype
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird Cpack Cfirst Cgap Cmain Ctail Klarge Y Values Wphys WeightedValues Mass

  obtain ⟨hcard,hweighted⟩ := hfamily S Fsrc rshift sshift z rat v Nlen Q K₀ N R Jsep Z
    (d:=d) (Wmax:=Wmax) (Tsrc:=Tsrc) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
    Uref Refs Gaps A W gap anchor e r vRef s
    hd hw hwcap hsmallShift hTsrc hT hM hδ hsourceScale hQ hUbandCap
    hy hz hreg hlower hjets htests hden hinv hnegative hMtwo hN
    hJsep hJM hNM hwJ hmesh hgeometry hseparation hshifts hmodel hlevel hminor hcomplete
    hR hRM hscale hA hW hx hgapMem
    hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
    hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
    hselectedUpper hscaleTen hfamilyGap hgap hQN hNsqM hUR
    hrHeight hsHeight heHeight hvHeight hsmall hNR hRN hNcube hminscale
    hNtwo hLeft hRight hanchor hcut hcount hsize hD hΔ hBsize
  let Scale := C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11
  change ∀ k, (Values k)^12 ≤ Scale*
    (∑ key∈V.image color, ((Fiber key).card:ℝ)^10*Mass) at hweighted
  have hYimage : V.image (fun ip => ip.1.1)=Y := by
    ext y
    constructor
    · intro hym
      obtain ⟨ip,hip,rfl⟩ := Finset.mem_image.mp hym
      exact Finset.mem_image_of_mem Prod.fst (Finset.mem_product.mp hip).1
    · intro hym
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hym
      exact Finset.mem_image.mpr ⟨(i,0),Finset.mem_product.mpr ⟨hi,Finset.mem_univ _⟩,rfl⟩
  have hpoints := rounded_offset_family_point_count V (fun y n => z (y,n))
    (fun y n => Nlen (y,n)) N Z hM.le hN
    (fun ip hip => hz ip.1 (Finset.mem_product.mp hip).1)
    (fun ip hip => hgeometry ip.1 (Finset.mem_product.mp hip).1)
  rw [hYimage] at hpoints
  have hNpos : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hratio : 1 ≤ M/(N:ℝ) := (le_div_iff₀ hNpos).mpr (by simpa only [one_mul] using hNM)
  have hphysical : (V.card:ℝ) ≤ 10*(Y.card:ℝ)*(M/(N:ℝ)) := by
    calc
      _ ≤ 2*(4+M/(N:ℝ))*(Y.card:ℝ) := hpoints
      _ ≤ (10*(M/(N:ℝ)))*(Y.card:ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith only [hratio]) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hweightCard : (∑ key∈V.image color, ((Fiber key).card:ℝ))=(V.card:ℝ) := by
    exact_mod_cast (Finset.card_eq_sum_card_image color V).symm
  have hweights : (∑ key∈V.image color, ((Fiber key).card:ℝ)^10) ≤ (V.card:ℝ)^10 := by
    calc
      _ = ∑ key∈V.image color, ((Fiber key).card:ℝ)*((Fiber key).card:ℝ)^9 := by
        apply Finset.sum_congr rfl
        intro key _
        rw [pow_succ']
      _ ≤ ∑ key∈V.image color, ((Fiber key).card:ℝ)*(V.card:ℝ)^9 := by
        apply Finset.sum_le_sum
        intro key _
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply pow_le_pow_left₀ (Nat.cast_nonneg _)
        exact_mod_cast Finset.card_filter_le V (fun ip => color ip=key)
      _ = (V.card:ℝ)^10 := by
        rw [←Finset.sum_mul,hweightCard]
        ring
  have hplainCap (Bcard : ℝ) (hVcard : (V.card:ℝ) ≤ Bcard) (k : ZMod K₀) : (Values k)^12 ≤
      Scale*Bcard^10*Mass := by
    by_cases hV : V=∅
    · have hY : Y=∅ := by rw [←hYimage,hV,Finset.image_empty]
      have hh := hweighted k
      simpa only [Values,Mass,hV,hY,Finset.sum_empty,Finset.image_empty,Finset.card_empty,
        Nat.cast_zero,mul_zero,zero_mul,zero_pow (by decide : (10:ℕ)≠0),
        zero_pow (by decide : (2:ℕ)≠0),add_zero] using hh
    · obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr hV
      have hf : 0 < (Fiber (color i)).card :=
        Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,rfl⟩⟩
      have hweight : 0 < ∑ key∈V.image color, ((Fiber key).card:ℝ)^10 :=
        lt_of_lt_of_le (pow_pos (Nat.cast_pos.mpr hf) 10)
          (Finset.single_le_sum (f:=fun key => ((Fiber key).card:ℝ)^10)
            (fun key _ => pow_nonneg (Nat.cast_nonneg _) 10)
            (Finset.mem_image_of_mem color hi))
      have hb : (Values k)^12 ≤ (Scale*Mass)*
          (∑ key∈V.image color, ((Fiber key).card:ℝ)^10) := by
        calc
          _ ≤ _ := hweighted k
          _ = _ := by rw [←Finset.sum_mul]; ac_rfl
      have hSM : 0 ≤ Scale*Mass := nonneg_of_mul_nonneg_left
        ((pow_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) 12).trans hb) hweight
      calc
        (Values k)^12 ≤ (Scale*Mass)*(∑ key∈V.image color, ((Fiber key).card:ℝ)^10) := hb
        _ ≤ (Scale*Mass)*Bcard^10 :=
          mul_le_mul_of_nonneg_left
            (hweights.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hVcard 10)) hSM
        _ = _ := mul_right_comm Scale Mass _
  have hplain (k : ZMod K₀) : (Values k)^12 ≤
      Scale*(10*(Y.card:ℝ)*(M/(N:ℝ)))^10*Mass :=
    hplainCap _ hphysical k
  refine ⟨hcard,hweighted,hphysical,hplain,?_⟩
  intro k
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hWphys : 0 ≤ Wphys := by dsimp only [Wphys]; positivity
  let weight := fun ip : (ℝ × ℤ) × Fin 2 =>
    Real.sqrt (2*(q ip.1:ℝ))/((q ip.1:ℝ)*Real.sqrt (μ ip.1*(Nlen ip.1:ℝ)))
  let val := fun ip : (ℝ × ℤ) × Fin 2 =>
    ∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
      GafniTao.fordAdditiveCharacter (∑ d,x ip d*
        (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
          Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)
  have hweight ip (hip : ip∈V) : weight ip ≤ Real.sqrt Wphys := by
    have hi := (Finset.mem_product.mp hip).1
    have hsdata := hshifts ip.1.1 (Finset.mem_image_of_mem Prod.fst hi)
    have hh := double_difference_source_completion_weight Fsrc
      hsdata.1 hsdata.2.1 hd (hy ip.1 hi) hsdata.2.2.1 hsdata.2.2.2 hwcap hsmallShift
      hcsrc hUsrc hσ hTsrc hT hMtwo hNpos (zero_lt_one.trans_le hR)
      (Nat.cast_pos.mpr hQ)
      (show (Q:ℝ) ≤ 2*((rat ip.1).den:ℝ) by exact_mod_cast (hden ip.1 hi).2)
      (show (N:ℝ) ≤ (Nlen ip.1:ℝ) by exact_mod_cast (hgeometry ip.1 hi).1)
      (hz ip.1 hi) hscale hδ hreg hlower hjets
      (approximateModelPhase_mono (hmodel ip.1 hi) (by norm_num : 2 ≤ 4) le_rfl)
    exact hh.2.2
  have hweight0 ip : 0 ≤ weight ip :=
    div_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
  have hs0 : 0 ≤ ∑ ip∈V, weight ip*‖val ip‖ :=
    Finset.sum_nonneg (fun ip _ => mul_nonneg (hweight0 ip) (norm_nonneg _))
  have hsum : (∑ ip∈V, weight ip*‖val ip‖) ≤ Real.sqrt Wphys*(Values k) := by
    change (∑ ip∈V, weight ip*‖val ip‖) ≤ Real.sqrt Wphys*(∑ ip∈V, ‖val ip‖)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun ip hip =>
      mul_le_mul_of_nonneg_right (hweight ip hip) (norm_nonneg _))
  have hp := pow_le_pow_left₀ hs0 hsum 12
  have hsqrt : (Real.sqrt Wphys)^12=Wphys^6 := by
    rw [show (12:ℕ)=2*6 by norm_num,pow_mul,Real.sq_sqrt hWphys]
  rw [mul_pow,hsqrt] at hp
  constructor
  · exact hp.trans (mul_le_mul_of_nonneg_left (hplainCap _ le_rfl k) (pow_nonneg hWphys 6))
  · exact hp.trans (mul_le_mul_of_nonneg_left (hplain k) (pow_nonneg hWphys 6))

private theorem double_difference_physical_curvature_growth
    (F : ℝ → ℝ) {r s d y w c U T M x z : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hd : 0 < d)
    (hy : y∈Icc (1:ℝ) 2) (hprod : r*s=d*y)
    (hshift : r+s ≤ w) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hc : 0 < c) (hU : 0 < U) (hT : 0 < T) (hM : 0 < M)
    (hx : x∈Icc (3*M/4) (9*M/4)) (hz : z∈Icc (3*M/4) (9*M/4)) (hxz : x ≤ z)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hjets : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) :
    let Φ := fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/d
    let f := fun v => T*Φ (v/M)
    c*T/(4*M^3)*(z-x) ≤ iteratedDeriv 2 f z/2-iteratedDeriv 2 f x/2 := by
  intro Φ f
  let h := fun v => iteratedDeriv 2 f v/2
  have hjet u (hu : u∈Icc (3/4:ℝ) (9/4)) :=
    double_difference_cubic_jet_bounds F hu hy hr hs hd hU hc
      hprod hshift hw hsmall hf hlower hjets
  have hreg u (hu : 0 < u) : ContDiffAt ℝ ∞ Φ u :=
    (hjet 1 (by norm_num)).1 u hu
  have hnorm v (hv : v∈Icc (3*M/4) (9*M/4)) :
      v/M∈Icc (3/4:ℝ) (9/4) := by
    constructor
    · apply (le_div_iff₀ hM).mpr
      linarith only [hv.1]
    · apply (div_le_iff₀ hM).mpr
      linarith only [hv.2]
  have hvpos v (hv : v∈Icc (3*M/4) (9*M/4)) : 0 < v := by
    linarith only [hv.1,hM]
  have hdcurv v (hv : v∈Icc (3*M/4) (9*M/4)) :
      HasDerivAt h (iteratedDeriv 3 f v/2) v := by
    have hcf : ContDiffAt ℝ ∞ f v :=
      contDiffAt_const.mul ((hreg (v/M) (div_pos (hvpos v hv) hM)).comp v
        (contDiffAt_id.div_const M))
    have hh : HasDerivAt (iteratedDeriv 2 f) (iteratedDeriv 3 f v) v := by
      simpa only [iteratedDeriv_succ] using
        ((contDiffAt_iteratedDeriv_infty hcf 2).differentiableAt (by simp)).hasDerivAt
    exact hh.div_const 2
  have hb v (hv : v∈Icc (3*M/4) (9*M/4)) : c*T/(4*M^3) ≤ deriv h v := by
    have ha := sargos_iteratedDeriv_comp_affine_local (f:=Φ)
      (l:=0) (r:=v+1) (c:=M⁻¹) (d:=0)
      (fun u hu => hreg _ (by
        simpa only [add_zero] using mul_pos (inv_pos.mpr hM) hu.1))
      (show v∈Ioo (0:ℝ) (v+1) from ⟨hvpos v hv,by linarith⟩) 3
    have hphysical : iteratedDeriv 3 f v=T/M^3*iteratedDeriv 3 Φ (v/M) := by
      change iteratedDeriv 3 (fun u => T*Φ (u/M)) v=_
      rw [iteratedDeriv_const_mul_field]
      have he : (fun u => Φ (u/M))=(fun u => Φ (M⁻¹*u+0)) := by
        funext u
        congr 1
        ring
      rw [he,ha]
      simp only [add_zero,inv_pow]
      rw [show M⁻¹*v=v/M by ring]
      ring
    rw [(hdcurv v hv).deriv,hphysical]
    calc
      c*T/(4*M^3) = (T/M^3)*(c/2)/2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hjet _ (hnorm v hv)).2.1 (by positivity)) (by norm_num)
  exact (convex_Icc (3*M/4) (9*M/4)).mul_sub_le_image_sub_of_le_deriv
    (fun v hv => (hdcurv v hv).continuousAt.continuousWithinAt)
    (fun v hv => (hdcurv v (interior_subset hv)).differentiableAt.differentiableWithinAt)
    (fun v hv => hb v (interior_subset hv)) x hx z hz hxz

private theorem double_difference_constructed_reference_system_bounded
    (F rshift sshift : ℝ → ℝ) (Y : Finset ℝ) {c J d w T M N R U : ℝ}
    (hc : 0 < c) (hJ : 0 < J) (hd : 0 < d)
    (hw : w ≤ 1/4) (hsmallShift : 2*J*w ≤ c/64)
    (hy : ∀ y∈Y, y∈Icc (1:ℝ) 2)
    (hshifts : ∀ y∈Y, 0 ≤ rshift y ∧ 0 ≤ sshift y ∧
      rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ w)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hbound : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ J)
    (hnegative : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hU : 0 < U) (hUmax : U ≤ R^2) (hphase : T*N*R^2=M^3) :
    let Φ := fun y u => (F u-F (u+rshift y)-F (u+sshift y)+F (u+rshift y+sshift y))/d
    let f := fun y v => T*Φ y (v/M)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let curvatureScale := J*T/M^2
    ∃ H : ℤ, 2 ≤ H ∧ (H:ℝ)<4*R^2/U ∧ ∃ S : Finset ℝ,
      (∀ q : ℚ, (q.den:ℤ) ≤ H → |(q:ℝ)| ≤ curvatureScale → (q:ℝ) ∈ S) ∧
      (∀ a ∈ S, ∀ b ∈ S, ∀ q : ℚ, (q.den:ℤ) ≤ H →
        (q:ℝ) ∈ Icc a b → (q:ℝ) ∈ S) ∧
      (∃ l ∈ S, ∃ u ∈ S, l ≤ -curvatureScale ∧ curvatureScale ≤ u) ∧
      (∀ z ∈ S, |z| ≤ curvatureScale+1) ∧
      (∀ z∈S, ∃ a b : ℤ, z=(a:ℝ)/b ∧ IsCoprime a b ∧ 0 < b ∧
        (b:ℝ)<4*R^2/U ∧ |(a:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U)) ∧
      (∀ y∈Y, ∀ x ∈ Icc M (2*M), |h y x| ≤ curvatureScale) ∧
      (∀ z ∈ S,
        (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ H) ∨
        (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
          R^2 ≤ U*(n:ℝ)^2 ∧ 0 < v ∧ v ≤ H ∧ (u:ℝ)/v ∈ S ∧ |m*v-u*n|=1)) ∧
      (∀ x ∈ S, ∀ z ∈ S, x ≠ z → U/(4*R^2) < |x-z|) ∧
      (∀ y∈Y, ∀ x ∈ Icc M (2*M),
        ∃ q ∈ S, |h y x-q| ≤ 7*U/(4*R^2)) ∧
      (∀ y∈Y, ∀ q ∈ S,
        q ∈ Icc (h y M) (h y (2*M)) →
        ∃ x ∈ Icc M (2*M), h y x=q) ∧
      (∀ a ∈ S, ∀ b ∈ S, a < b →
        (∀ z ∈ S, ¬ (a < z ∧ z < b)) →
        U/(4*R^2) < b-a ∧ b-a ≤ 7*U/(2*R^2) ∧
        (∃ m n u v : ℤ, a=(m:ℝ)/n ∧ b=(u:ℝ)/v ∧
          IsCoprime m n ∧ IsCoprime u v ∧ 0 < n ∧ 0 < v ∧
          R^2 ≤ U*((max n v:ℤ):ℝ)^2) ∧
        (∀ y∈Y, ∀ x ∈ Icc M (2*M), ∀ z ∈ Icc M (2*M),
          h y x=a → h y z=b → |z-x| ≤ (14/c)*U*N)) := by
  intro Φ f h curvatureScale
  let δ := U/R^2
  have hδ : 0 < δ := div_pos hU (sq_pos_of_pos hR)
  have hδmax : δ ≤ 1 := (div_le_one (sq_pos_of_pos hR)).mpr hUmax
  have hcurvpos : 0 ≤ curvatureScale := by dsimp only [curvatureScale]; positivity
  let L : ℤ := Int.floor (-curvatureScale)
  let V : ℤ := Int.floor curvatureScale
  have hLV : L ≤ V := Int.floor_mono (by linarith only [hcurvpos])
  obtain ⟨H,hH,hHbound,hbuild⟩ := exists_source_interval_reference_system_bounded hδ hδmax
  obtain ⟨S,hseed,hpoints,hlabels,hsep,hcover,hgaps,hheight⟩ := hbuild L V hLV
  have hinside x (hx : |x| ≤ curvatureScale) : x ∈ Icc (L:ℝ) ((V:ℝ)+1) := by
    have hxI := abs_le.mp hx
    have hL := Int.floor_le (-curvatureScale)
    have hV := Int.lt_floor_add_one curvatureScale
    change ((L:ℝ) ≤ x ∧ x ≤ (V:ℝ)+1)
    dsimp only [L,V]
    constructor <;> linarith only [hxI.1,hxI.2,hL,hV]
  have houtside x (hx : x ∈ Icc (L:ℝ) ((V:ℝ)+1)) : |x| ≤ curvatureScale+1 := by
    have hL := Int.lt_floor_add_one (-curvatureScale)
    have hV := Int.floor_le curvatureScale
    apply abs_le.mpr
    dsimp only [L,V] at hx
    constructor <;> linarith only [hx.1,hx.2,hL,hV]
  have hheightScale : 4/δ=4*R^2/U := by
    dsimp only [δ]
    rw [div_div_eq_mul_div]
  have hHbound' : (H:ℝ)<4*R^2/U := by simpa only [hheightScale] using hHbound
  have hheight' z (hz : z∈S) :
      ∃ a b : ℤ, z=(a:ℝ)/b ∧ IsCoprime a b ∧ 0 < b ∧
        (b:ℝ)<4*R^2/U ∧ |(a:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U) := by
    obtain ⟨a,b,hval,hcop,hb,hbb,_hnum⟩ := hheight z hz
    have hbR : (0:ℝ) < b := by exact_mod_cast hb
    have hbb' : (b:ℝ)<4*R^2/U := by simpa only [hheightScale] using hbb
    refine ⟨a,b,hval,hcop,hb,hbb',?_⟩
    have hnum : (a:ℝ)=z*(b:ℝ) := (div_eq_iff hbR.ne').mp hval.symm
    rw [hnum,abs_mul,abs_of_pos hbR]
    exact mul_le_mul (houtside z (hpoints z hz)) hbb'.le hbR.le
      (add_nonneg hcurvpos zero_le_one)
  have hscaled (n : ℤ) (hn : 1 ≤ δ*(n:ℝ)^2) : R^2 ≤ U*(n:ℝ)^2 := by
    have hh : 1 ≤ U*(n:ℝ)^2/R^2 := by dsimp only [δ] at hn; convert hn using 1; ring
    simpa only [one_mul] using (le_div_iff₀ (sq_pos_of_pos hR)).mp hh
  have hregQ y (hyY : y∈Y) u (hu : 0 < u) : ContDiffAt ℝ ∞ (Φ y) u := by
    have hsdata := hshifts y hyY
    exact (double_difference_cubic_jet_bounds F
      (by norm_num : (1:ℝ)∈Icc (3/4:ℝ) (9/4)) (hy y hyY)
      hsdata.1 hsdata.2.1 hd hJ hc hsdata.2.2.1 hsdata.2.2.2 hw hsmallShift
      hf hlower hbound).1 u hu
  have hcurv y x (hyY : y∈Y) (hx : x∈Icc M (2*M)) : |h y x| ≤ curvatureScale := by
    have hsdata := hshifts y hyY
    have hpar := hy y hyY
    have hprodpos : 0 < rshift y*sshift y := by
      rw [hsdata.2.2.1]
      exact mul_pos hd (by linarith only [hpar.1])
    have hrp : 0 < rshift y := by nlinarith only [hsdata.1,hsdata.2.1,hprodpos]
    have hsp : 0 < sshift y := by nlinarith only [hsdata.1,hsdata.2.1,hprodpos]
    exact (double_difference_physical_curvature_band F hx hpar hrp hsp hd hc hJ hT hM
      hsdata.2.2.1 (hsdata.2.2.2.trans hw) hf hnegative
      (fun u hu => hbound u hu 4 (by norm_num) (by norm_num))).2
  have hgrow y (hyY : y∈Y) x z (hx : x∈Icc M (2*M)) (hz : z∈Icc M (2*M))
      (hxz : x ≤ z) : c*T/(4*M^3)*(z-x) ≤ h y z-h y x := by
    have hsdata := hshifts y hyY
    apply double_difference_physical_curvature_growth F
      hsdata.1 hsdata.2.1 hd (hy y hyY) hsdata.2.2.1 hsdata.2.2.2 hw hsmallShift
      hc hJ hT hM _ _ hxz hf hlower hbound
    · constructor <;> linarith only [hx.1,hx.2,hM]
    · constructor <;> linarith only [hz.1,hz.2,hM]
  have hLmem : (L:ℝ) ∈ S := by
    have hq := hseed (L:ℚ) (by norm_num; omega)
      (show ((L:ℚ):ℝ) ∈ Icc (L:ℝ) ((V:ℝ)+1) by
        simp only [Rat.cast_intCast]
        have hh : (L:ℝ) ≤ V := by exact_mod_cast hLV
        exact ⟨le_rfl,by linarith only [hh]⟩)
    simpa only [Rat.cast_intCast] using hq
  have hVmem : (V:ℝ)+1 ∈ S := by
    have hq := hseed ((V+1:ℤ):ℚ) (by norm_num; omega)
      (show (((V+1:ℤ):ℚ):ℝ) ∈ Icc (L:ℝ) ((V:ℝ)+1) by
        push_cast
        have hh : (L:ℝ) ≤ V := by exact_mod_cast hLV
        exact ⟨by linarith only [hh],le_rfl⟩)
    simpa using hq
  have hgapLower : δ/4=U/(4*R^2) := by dsimp only [δ]; ring
  have hgapCover : 7*δ/4=7*U/(4*R^2) := by dsimp only [δ]; ring
  have hgapUpper : 7*δ/2=7*U/(2*R^2) := by dsimp only [δ]; ring
  refine ⟨H,hH,hHbound',S,(fun q hqH hq => hseed q hqH (hinside q hq)),
    (fun a ha b hb q hqH hqI => hseed q hqH
      ⟨(hpoints a ha).1.trans hqI.1,hqI.2.trans (hpoints b hb).2⟩),
    ⟨L,hLmem,(V:ℝ)+1,hVmem,Int.floor_le (-curvatureScale),(Int.lt_floor_add_one curvatureScale).le⟩,
    (fun z hz => houtside z (hpoints z hz)),hheight',
    (fun y hy x hx => hcurv y x hy hx),?_,?_,?_,?_,?_⟩
  · intro z hz
    rcases hlabels z hz with hsmall | ⟨m,n,u,v,hval,hcop,hn,hnscale,hv,hvH,huI,hdet⟩
    · exact Or.inl hsmall
    · right
      have hneighbor : (u:ℝ)/v ∈ S := by
        have hq := hseed (Rat.divInt u v)
          ((Int.le_of_dvd hv (Rat.den_dvd u v)).trans hvH)
          (by simpa only [Rat.cast_divInt] using huI)
        simpa only [Rat.cast_divInt] using hq
      exact ⟨m,n,u,v,hval,hcop,hn,hscaled n hnscale,hv,hvH,hneighbor,hdet⟩
  · intro x hx z hz hne
    simpa only [hgapLower] using hsep x hx z hz hne
  · intro y hy x hx
    obtain ⟨q,hq,hnear⟩ := hcover (h y x) (hinside _ (hcurv y x hy hx))
    exact ⟨q,hq,by simpa only [hgapCover] using hnear⟩
  · intro y hy q _hq hqI
    have hcont : ContinuousOn (h y) (Icc M (2*M)) := by
      intro x hx
      have hx0 : 0 < x/M := div_pos (hM.trans_le hx.1) hM
      have hcf : ContDiffAt ℝ 3 (f y) x :=
        (contDiffAt_const.mul ((hregQ y hy (x/M) hx0).comp x
          (contDiffAt_id.div_const M))).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
      exact ((hasDerivAt_iteratedDeriv_finite (by norm_num : 2 < 3) hcf).div_const 2).continuousAt.continuousWithinAt
    exact intermediate_value_Icc (by linarith only [hM] : M ≤ 2*M) hcont hqI
  · intro a ha b hb hab hadj
    obtain ⟨hlow,hupp,m,n,u,v,haval,hbval,hcopn,hcopv,hn,hv,hmax⟩ :=
      hgaps a ha b hb hab hadj
    refine ⟨by simpa only [hgapLower] using hlow,by simpa only [hgapUpper] using hupp,
      ⟨m,n,u,v,haval,hbval,hcopn,hcopv,hn,hv,hscaled (max n v) hmax⟩,?_⟩
    intro y hy x hx z hz hxa hzb
    have hxz : x < z := by
      by_contra hn
      have hh := hgrow y hy z x hz hx (le_of_not_gt hn)
      rw [hxa,hzb] at hh
      have hnonneg : 0 ≤ c*T/(4*M^3)*(x-z) :=
        mul_nonneg (by positivity) (sub_nonneg.mpr (le_of_not_gt hn))
      linarith only [hh,hnonneg,hab]
    have hh := hgrow y hy x z hx hz hxz.le
    rw [hxa,hzb] at hh
    have hrate : c*T/(4*M^3)=c/(4*N*R^2) := by
      rw [←hphase]
      field_simp
    have hratepos : 0 < c/(4*N*R^2) := by positivity
    rw [hrate] at hh
    rw [abs_of_pos (sub_pos.mpr hxz)]
    calc
      z-x ≤ (b-a)/(c/(4*N*R^2)) :=
        (le_div_iff₀ hratepos).mpr (by simpa only [mul_comm] using hh)
      _ ≤ (7*U/(2*R^2))/(c/(4*N*R^2)) :=
        div_le_div_of_nonneg_right (by simpa only [hgapUpper] using hupp) hratepos.le
      _ = (14/c)*U*N := by field_simp; ring

private theorem double_difference_physical_source_jets
    (F : ℝ → ℝ) {r s d y w c U T M x : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hd : 0 < d)
    (hy : y∈Icc (1:ℝ) 2) (hprod : r*s=d*y)
    (hshift : r+s ≤ w) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hc : 0 < c) (hU : 0 < U) (hT : 0 < T) (hM : 0 < M)
    (hx : x∈Icc (3*M/4) (9*M/4))
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hjets : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) :
    let Φ := fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/d
    let f := fun v => T*Φ (v/M)
    (∀ v, 0 < v → ContDiffAt ℝ ∞ f v) ∧
      c*T/(2*M^3) ≤ iteratedDeriv 3 f x ∧
      |iteratedDeriv 3 f x| ≤ 3*U*T/M^3 ∧
      |iteratedDeriv 4 f x| ≤ 3*U*T/M^4 := by
  intro Φ f
  have hnorm : x/M∈Icc (3/4:ℝ) (9/4) := by
    constructor
    · apply (le_div_iff₀ hM).mpr
      linarith only [hx.1]
    · apply (div_le_iff₀ hM).mpr
      linarith only [hx.2]
  have hj := double_difference_cubic_jet_bounds F hnorm hy hr hs hd hU hc
    hprod hshift hw hsmall hf hlower hjets
  have hreg v (hv : 0 < v) : ContDiffAt ℝ ∞ f v :=
    contDiffAt_const.mul ((hj.1 (v/M) (div_pos hv hM)).comp v
      (contDiffAt_id.div_const M))
  have hxp : 0 < x := by linarith only [hx.1,hM]
  have hphysical n : iteratedDeriv n f x=T/M^n*iteratedDeriv n Φ (x/M) := by
    have ha := sargos_iteratedDeriv_comp_affine_local (f:=Φ)
      (l:=0) (r:=x+1) (c:=M⁻¹) (d:=0)
      (fun u hu => hj.1 _ (by
        simpa only [add_zero] using mul_pos (inv_pos.mpr hM) hu.1))
      (show x∈Ioo (0:ℝ) (x+1) from ⟨hxp,by linarith⟩) n
    change iteratedDeriv n (fun v => T*Φ (v/M)) x=_
    rw [iteratedDeriv_const_mul_field]
    have he : (fun v => Φ (v/M))=(fun v => Φ (M⁻¹*v+0)) := by
      funext v
      congr 1
      ring
    rw [he,ha]
    simp only [add_zero,inv_pow]
    rw [show M⁻¹*x=x/M by ring]
    ring
  refine ⟨hreg,?_,?_,?_⟩
  · rw [hphysical]
    have hh := mul_le_mul_of_nonneg_left hj.2.1 (show 0 ≤ T/M^3 by positivity)
    convert hh using 1
    ring
  · rw [hphysical,abs_mul,abs_of_pos (show 0 < T/M^3 by positivity)]
    have hh := mul_le_mul_of_nonneg_left hj.2.2.1 (show 0 ≤ T/M^3 by positivity)
    convert hh using 1
    ring
  · rw [hphysical,abs_mul,abs_of_pos (show 0 < T/M^4 by positivity)]
    have hh := mul_le_mul_of_nonneg_left hj.2.2.2 (show 0 ≤ T/M^4 by positivity)
    convert hh using 1
    ring

private theorem double_difference_chosen_arcs_band_fourier
    {c J : ℝ} (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (S : Finset ι) (F : ℝ → ℝ)
      (y rshift sshift : ι → ℝ) (L : ι → ℤ) (H : ι → ℕ) (r : ι → ℚ) (z : ι → ℝ)
      (N : ℕ) (d w T M R : ℝ),
      1 ≤ N → (∀ i∈S, H i ≤ N) →
      0 < d → w ≤ 1/4 → 2*J*w ≤ c/64 → 0 < T → 0 < M → 0 < R →
      (∀ i∈S, y i∈Icc (1:ℝ) 2) →
      (∀ i∈S, 0 ≤ rshift i ∧ 0 ≤ sshift i ∧
        rshift i*sshift i=d*y i ∧ rshift i+sshift i ≤ w) →
      (∀ i∈S, (L i:ℝ)-2*(N:ℝ)∈Icc M (2*M)) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ J) →
      (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
      T*(N:ℝ)*R^2=M^3 →
      7*(N:ℝ)+2 ≤ M/4 →
      (3*J)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/4)*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      let f := fun i v => T*((F (v/M)-F (v/M+rshift i)-F (v/M+sshift i)+
        F (v/M+rshift i+sshift i))/d)
      (∀ i∈S, z i∈Ioo ((L i:ℝ)-2*(N:ℝ)-(N:ℝ)/4)
        ((L i:ℝ)-2*(N:ℝ)+(N:ℝ)/4) ∧
        iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ)) →
      let m := fun i => round (z i)
      let A := fun i => (L i-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i) (m i)/6
      let ℓ := fun i => deriv (f i) (m i)
      let lambda := c/(12*(N:ℝ)*R^2)
      let U₃ := J/(2*(N:ℝ)*R^2)
      let G := S.filter (fun i => q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)
      (∀ i∈S, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i) ∧
      (∀ i∈G, 1 ≤ A i ∧ q i ≤ A i ∧ 1 ≤ μ i*(q i:ℝ)^2*A i) ∧
      ∀ Q₀ : ℕ, (∀ i∈G, q i ≤ Q₀) →
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q₀:ℝ)*(N:ℝ)^2 ≤ K₀ →
      (∀ i∈G, 7*(μ i*(q i:ℝ)*(A i:ℝ)^2) ≤ K₀) ∧
      ∃ v : ι → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈S, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f i n):ℂ)‖) ≤
          C*((∑ i∈S.filter (fun i => ¬ (q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)),(H i:ℝ))+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) := by
  classical
  obtain ⟨C,hC,hentry⟩ := TaoTrudgianYang2025.exists_bourgain_C4_variable_source_common_fourier
  refine ⟨C,hC,?_⟩
  intro ι S F y rshift sshift L H r z N d w T M R hN hH hd hw hsmall hT hM hR hy hshifts
    hbase hf hbound hlower hphase hbuffer hfourBudget hquadBudget f hroots m A q μ ℓ lambda U₃ G
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlambda : 0 < lambda := by dsimp only [lambda]; positivity
  have hU₃ : 0 < U₃ := by dsimp only [U₃]; positivity
  let beta := 3*J/(M*(N:ℝ)*R^2)
  have hbeta : 0 ≤ beta := by dsimp only [beta]; positivity
  have hdata i (hi : i∈S) v (hv : v∈Icc (3*M/4) (9*M/4)) :=
    double_difference_physical_source_jets F (hshifts i hi).1 (hshifts i hi).2.1 hd
      (hy i hi) (hshifts i hi).2.2.1 (hshifts i hi).2.2.2 hw hsmall
      hc hJ hT hM hv hf hlower hbound
  have hcf i (hi : i∈S) v (hv : v∈Icc (3*M/4) (9*M/4)) :
      ContDiffAt ℝ ∞ (f i) v :=
    (hdata i hi v hv).1 v (by linarith only [hv.1,hM])
  have hscale3 : T/M^3=1/((N:ℝ)*R^2) := by
    apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    nlinarith only [hphase]
  have hscale4 : T/M^4=1/(M*(N:ℝ)*R^2) := by
    apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    calc
      T*(M*(N:ℝ)*R^2)=M*(T*(N:ℝ)*R^2) := by ring
      _ = M*M^3 := by rw [hphase]
      _ = 1*M^4 := by ring
  have hthree i (hi : i∈S) v (hv : v∈Icc (3*M/4) (9*M/4)) :
      6*lambda ≤ iteratedDeriv 3 (f i) v ∧ iteratedDeriv 3 (f i) v ≤ 6*U₃ := by
    have hh := hdata i hi v hv
    constructor
    · calc
        6*lambda = (c/2)*(T/M^3) := by rw [hscale3]; dsimp only [lambda]; ring
        _ = c*T/(2*M^3) := by ring
        _ ≤ _ := hh.2.1
    · calc
        _ ≤ |iteratedDeriv 3 (f i) v| := le_abs_self _
        _ ≤ 3*J*T/M^3 := hh.2.2.1
        _ = 3*J*(T/M^3) := by ring
        _ = 6*U₃ := by rw [hscale3]; dsimp only [U₃]; ring
  have hfour i (hi : i∈S) v (hv : v∈Icc (3*M/4) (9*M/4)) :
      |iteratedDeriv 4 (f i) v| ≤ beta := by
    calc
      _ ≤ 3*J*T/M^4 := (hdata i hi v hv).2.2.2
      _ = 3*J*(T/M^4) := by ring
      _ = beta := by rw [hscale4]; dsimp only [beta]; ring
  have hgeo i (hi : i∈S) :
      z i∈Ioo (3*M/4) (9*M/4) ∧ |z i-(m i:ℝ)| ≤ 1/2 ∧
      ((N:ℤ) ≤ L i-m i ∧ L i-m i ≤ 3*(N:ℤ)) ∧
      Icc ((m i:ℝ)-(6*(N:ℝ)+1)) ((m i:ℝ)+(6*(N:ℝ)+1)) ⊆ Icc (3*M/4) (9*M/4) := by
    apply TaoTrudgianYang2025.bourgain_minimal_arc_rounded_source_geometry
      (show 0 < N by omega) (by ring) (hroots i hi).1
    intro w hw
    have hb := hbase i hi
    constructor <;> linarith only [hb.1,hb.2,hw.1,hw.2,hbuffer]
  have hA i (hi : i∈S) : N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i := by
    have hg := (hgeo i hi).2.2.1
    have hnonneg : 0 ≤ L i-m i := (Int.natCast_nonneg N).trans hg.1
    have he : (A i:ℤ)=L i-m i := Int.toNat_of_nonneg hnonneg
    refine ⟨?_,?_,?_⟩
    · exact_mod_cast (show (N:ℤ) ≤ (A i:ℤ) by rw [he]; exact hg.1)
    · exact_mod_cast (show (A i:ℤ) ≤ 3*(N:ℤ) by rw [he]; exact hg.2)
    · omega
  have hm i (hi : i∈S) : (m i:ℝ)∈Icc (3*M/4) (9*M/4) :=
    (hgeo i hi).2.2.2 ⟨by linarith only [hNp],by linarith only [hNp]⟩
  have hmu i (hi : i∈S) : 0 < μ i ∧ lambda ≤ μ i ∧ μ i ≤ U₃ := by
    have hh := hthree i hi (m i) (hm i hi)
    change 0 < iteratedDeriv 3 (f i) (m i)/6 ∧
      lambda ≤ iteratedDeriv 3 (f i) (m i)/6 ∧ iteratedDeriv 3 (f i) (m i)/6 ≤ U₃
    constructor
    · linarith only [hh.1,hlambda]
    · constructor <;> linarith only [hh.1,hh.2]
  have hsmall i (hi : i∈S) :
      beta*(2*(A i:ℝ)+1)^4 ≤ 1 ∧ (3*U₃/2)*(2*(A i:ℝ)+1)^2 ≤ 1 := by
    have hAr : (A i:ℝ) ≤ 3*(N:ℝ) := by exact_mod_cast (hA i hi).2.1
    have ha : 2*(A i:ℝ)+1 ≤ 6*(N:ℝ)+1 := by linarith only [hAr]
    have hb : beta*(6*(N:ℝ)+1)^4 ≤ 1 := by
      have hh := (div_le_one (show 0 < M*(N:ℝ)*R^2 by positivity)).mpr hfourBudget
      convert hh using 1
      dsimp only [beta]
      ring
    have hd : (3*U₃/2)*(6*(N:ℝ)+1)^2 ≤ 1 := by
      have hh := (div_le_one (show 0 < (N:ℝ)*R^2 by positivity)).mpr hquadBudget
      convert hh using 1
      dsimp only [U₃]
      ring
    exact ⟨(mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ha 4) hbeta).trans hb,
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ha 2) (by positivity)).trans hd⟩
  have hsub i (hi : i∈S) :
      Icc ((m i:ℝ)-(2*(A i:ℝ)+1)) ((m i:ℝ)+(2*(A i:ℝ)+1)) ⊆ Icc (3*M/4) (9*M/4) := by
    intro w hw
    apply (hgeo i hi).2.2.2
    have ha : (A i:ℝ) ≤ 3*(N:ℝ) := by exact_mod_cast (hA i hi).2.1
    constructor <;> linarith only [hw.1,hw.2,ha]
  have hcurv i (hi : i∈S) :
      |iteratedDeriv 2 (f i) (m i)/2-((r i).num:ℝ)/(q i:ℝ)| ≤ 3*U₃/2 := by
    have hh := TaoTrudgianYang2025.bourgain_curvature_level_difference (f i)
      (fun w hw => (hcf i hi w hw).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4))
      (fun w hw => ⟨(by linarith only [(hthree i hi w hw).1,hlambda]),(hthree i hi w hw).2⟩)
      (hm i hi) ⟨(hgeo i hi).1.1.le,(hgeo i hi).1.2.le⟩
    rw [(hroots i hi).2] at hh
    have hr := mul_le_mul_of_nonneg_left (hgeo i hi).2.1 (show 0 ≤ 3*U₃ by positivity)
    have he : (r i:ℝ)=((r i).num:ℝ)/(q i:ℝ) := by rw [Rat.cast_def]
    rw [he,abs_sub_comm (m i:ℝ) (z i)] at hh
    exact hh.trans (by linarith only [hr])
  have hGS : G ⊆ S := fun i hi => (Finset.mem_filter.mp hi).1
  have hscale i (hi : i∈G) :
      0 < q i ∧ q i ≤ A i ∧ IsCoprime (r i).num (q i:ℤ) ∧
      0 < μ i ∧ μ i*(A i:ℝ)^2 ≤ 1 ∧ 1 ≤ μ i*(q i:ℝ)^2*A i := by
    have hiS := hGS hi
    have hd := (Finset.mem_filter.mp hi).2
    have hmu' := hmu i hiS
    refine ⟨(r i).pos,hd.1.trans (hA i hiS).1,(r i).isCoprime_num_den,hmu'.1,?_,?_⟩
    · calc
        _ ≤ U₃*(2*(A i:ℝ)+1)^2 :=
          mul_le_mul hmu'.2.2
            (pow_le_pow_left₀ (show (0:ℝ) ≤ A i from Nat.cast_nonneg _)
              (show (A i:ℝ) ≤ 2*(A i:ℝ)+1 by linarith [show (0:ℝ) ≤ A i from Nat.cast_nonneg _]) 2)
            (sq_nonneg _) hU₃.le
        _ ≤ (3*U₃/2)*(2*(A i:ℝ)+1)^2 := by gcongr; linarith only [hU₃]
        _ ≤ _ := (hsmall i hiS).2
    · have hAr : (N:ℝ) ≤ A i := by exact_mod_cast (hA i hiS).1
      exact hd.2.trans (mul_le_mul
        (mul_le_mul_of_nonneg_right hmu'.2.1 (sq_nonneg (q i:ℝ))) hAr hNp.le
        (mul_nonneg hmu'.1.le (sq_nonneg _)))
  refine ⟨(fun i hi => ⟨(hgeo i hi).2.1,hA i hi⟩),
    (fun i hi => ⟨hN.trans (hA i (hGS hi)).1,(hscale i hi).2.1,
      (hscale i hi).2.2.2.2.2⟩),?_⟩
  intro Q₀ hQ₀ K₀ inst hK₀
  have hKG i (hi : i∈G) : 7*(μ i*(q i:ℝ)*(A i:ℝ)^2) ≤ K₀ := by
    have hiS := hGS hi
    have hAr : (A i:ℝ) ≤ 3*(N:ℝ) := by exact_mod_cast (hA i hiS).2.1
    have hqr : (q i:ℝ) ≤ Q₀ := by exact_mod_cast hQ₀ i hi
    calc
      _ ≤ 7*(U₃*(Q₀:ℝ)*(3*(N:ℝ))^2) := by gcongr; exact (hmu i hiS).2.2
      _ = 63*U₃*(Q₀:ℝ)*(N:ℝ)^2 := by ring
      _ ≤ _ := hK₀
  refine ⟨hKG,?_⟩
  obtain ⟨v,hv,hfourier⟩ := hentry ι G f (fun i => (m i:ℝ)) (fun i => (r i).num) q A H
    (fun i hi => hN.trans (hA i (hGS hi)).1)
    (fun i hi => (hH i (hGS hi)).trans (hA i (hGS hi)).1)
    beta (3*U₃/2) hbeta (by positivity)
    (fun i hi => (hsmall i (hGS hi)).1) (fun i hi => (hsmall i (hGS hi)).2)
    (fun i hi w hw => (hcf i (hGS hi) w (hsub i (hGS hi) hw)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4))
    (fun i hi v hv => hfour i (hGS hi) v (hsub i (hGS hi) hv))
    (fun i hi => hcurv i (hGS hi)) hscale K₀ hKG
  refine ⟨v,hv,?_⟩
  intro b τ s K x
  obtain ⟨k,hk⟩ := hfourier
  refine ⟨k,?_⟩
  let Src := fun i => ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f i n):ℂ)‖
  have hsrc :
      (∑ i∈G,Src i) =
        ∑ i∈G, ‖∑ n∈Finset.Ioc (A i:ℤ) ((A i:ℤ)+H i),(𝐞 (f i ((m i:ℝ)+n)):ℂ)‖ := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [Src]
    rw [←(hA i (hGS hi)).2.2,TaoTrudgianYang2025.bourgain_integer_source_translation]
  rw [←hsrc] at hk
  let Bad := S.filter (fun i => ¬ (q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N))
  have hbad : (∑ i∈Bad,Src i) ≤ ∑ i∈Bad,(H i:ℝ) := by
    apply Finset.sum_le_sum
    intro i _hi
    dsimp only [Src]
    apply (norm_sum_le _ _).trans_eq
    simp
  have hbad0 : 0 ≤ ∑ i∈Bad,(H i:ℝ) :=
    Finset.sum_nonneg (fun i _ => Nat.cast_nonneg (H i))
  have hbadC := mul_le_mul_of_nonneg_right hC hbad0
  simp only [one_mul] at hbadC
  have hsplit : (∑ i∈S,Src i)=(∑ i∈G,Src i)+(∑ i∈Bad,Src i) :=
    (Finset.sum_filter_add_sum_filter_not S
      (fun i => q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N) Src).symm
  change (∑ i∈S,Src i) ≤ _
  rw [hsplit]
  have hh := add_le_add hk (hbad.trans hbadC)
  convert hh using 1
  dsimp only [Bad]
  ring

private theorem double_difference_dyadic_anchor_center
    (F : ℝ → ℝ) {Q : ℕ} {a : ℚ} {r s d y w c U T M N R x : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hd : 0 < d)
    (hy : y∈Icc (1:ℝ) 2) (hprod : r*s=d*y)
    (hshift : r+s ≤ w) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hc : 0 < c) (hU : 0 < U) (hT : 0 < T) (hM : 0 < M)
    (hN : 0 < N) (hR : 0 < R) (hNM : N ≤ M)
    (hphase : T*N*R^2=M^3)
    (hx : x∈Icc (7*M/8) (17*M/8))
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hjets : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U)
    (hcut : 2*a.den ≤ Q) (hmajor : 128*R^2 ≤ c*(Q:ℝ)*a.den) :
    let Φ := fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/d
    let f := fun v => T*Φ (v/M)
    iteratedDeriv 2 f x/2=(a:ℝ) →
    ∃ b : ℚ, b.den ≤ Q ∧ Q ≤ 2*b.den ∧
      (a:ℝ) < b ∧ |(b:ℝ)-(a:ℝ)| ≤ c/(64*R^2) ∧
      ∃ z∈Icc x (x+N/16), iteratedDeriv 2 f z/2=(b:ℝ) := by
  intro Φ f hlevel
  let ε := c/(32*R^2)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hmajor' : 4 ≤ ε*(Q:ℝ)*a.den := by
    dsimp only [ε]
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0 < 32*R^2)).mpr
    nlinarith only [hmajor]
  obtain ⟨b,hb,hbhalf,hab,hclose,_⟩ := exists_dyadic_rational_near_anchor hcut hmajor'
  have hclose' : |(b:ℝ)-(a:ℝ)| ≤ c/(64*R^2) := by
    convert hclose using 1
    dsimp only [ε]
    ring
  let g := fun v => iteratedDeriv 2 f v/2
  have hxwide : x∈Icc (3*M/4) (9*M/4) := by
    constructor <;> linarith only [hx.1,hx.2,hM]
  have hUwide : x+N/16∈Icc (3*M/4) (9*M/4) := by
    constructor <;> linarith only [hx.1,hx.2,hM,hN,hNM]
  have hinc := double_difference_physical_curvature_growth F hr hs hd hy hprod
    hshift hw hsmall hc hU hT hM hxwide hUwide
    (show x ≤ x+N/16 by linarith only [hN]) hf hlower hjets
  have hrate : (c*T/(4*M^3))*(N/16)=c/(64*R^2) := by
    rw [←hphase]
    field_simp
    ring
  rw [add_sub_cancel_left,hrate] at hinc
  have hsub : Icc x (x+N/16) ⊆ Icc (3*M/4) (9*M/4) :=
    Icc_subset_Icc hxwide.1 hUwide.2
  have htarget : (b:ℝ)∈Icc (g x) (g (x+N/16)) := by
    change (b:ℝ)∈Icc (iteratedDeriv 2 f x/2) (g (x+N/16))
    rw [hlevel]
    refine ⟨hab.le,?_⟩
    change c/(64*R^2) ≤ g (x+N/16)-iteratedDeriv 2 f x/2 at hinc
    rw [hlevel] at hinc
    linarith only [hinc,(abs_le.mp hclose').2]
  have hreg := (double_difference_physical_source_jets F hr hs hd hy hprod
    hshift hw hsmall hc hU hT hM hxwide hf hlower hjets).1
  have hcont : ContinuousOn g (Icc x (x+N/16)) := by
    intro v hv
    have hv0 : 0 < v := by linarith only [(hsub hv).1,hM]
    exact ((contDiffAt_iteratedDeriv_infty (hreg v hv0) 2).continuousAt.div_const 2).continuousWithinAt
  obtain ⟨z,hz,hzlevel⟩ := intermediate_value_Icc
    (show x ≤ x+N/16 by linarith only [hN]) hcont htarget
  exact ⟨b,hb,hbhalf,hab,hclose',z,hz,hzlevel⟩

private theorem double_difference_dyadic_anchor_source_fourier
    {c J : ℝ} (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (S : Finset ι) (F : ℝ → ℝ)
      (y rshift sshift : ι → ℝ) (L : ι → ℤ) (H : ι → ℕ) (anchor : ι → ℚ) (za : ι → ℝ)
      (N Q : ℕ) (d w T M R : ℝ),
      1 ≤ N → (∀ i∈S, H i ≤ N) →
      0 < d → w ≤ 1/4 → 2*J*w ≤ c/64 → 0 < T → 0 < M → 0 < R →
      (∀ i∈S, y i∈Icc (1:ℝ) 2) →
      (∀ i∈S, 0 ≤ rshift i ∧ 0 ≤ sshift i ∧
        rshift i*sshift i=d*y i ∧ rshift i+sshift i ≤ w) →
      (∀ i∈S, (L i:ℝ)-2*(N:ℝ)∈Icc M (2*M)) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ J) →
      (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
      T*(N:ℝ)*R^2=M^3 →
      7*(N:ℝ)+2 ≤ M/4 →
      (3*J)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/4)*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      Q ≤ N → (∀ i∈S, 2*(anchor i).den ≤ Q) →
      (∀ i∈S, 128*R^2 ≤ c*(Q:ℝ)*(anchor i).den) →
      let f := fun i v => T*((F (v/M)-F (v/M+rshift i)-F (v/M+sshift i)+
        F (v/M+rshift i+sshift i))/d)
      (∀ i∈S, za i∈Ioo ((L i:ℝ)-2*(N:ℝ)-(N:ℝ)/8)
        ((L i:ℝ)-2*(N:ℝ)+(N:ℝ)/8) ∧
        iteratedDeriv 2 (f i) (za i)/2=(anchor i:ℝ)) →
      ∃ (r : ι → ℚ) (z : ι → ℝ),
      (∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i:ℝ) < r i ∧ |(r i:ℝ)-(anchor i:ℝ)| ≤ c/(64*R^2) ∧
        z i∈Icc (za i) (za i+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ)) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i) (m i)/6
      let ℓ := fun i => deriv (f i) (m i)
      let U₃ := J/(2*(N:ℝ)*R^2)
      (∀ i∈S, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i) ∧
      (∀ i∈S, 1 ≤ A i ∧ q i ≤ A i ∧ 1 ≤ μ i*(q i:ℝ)^2*A i) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      (∀ i∈S, 7*(μ i*(q i:ℝ)*(A i:ℝ)^2) ≤ K₀) ∧
      ∃ v : ι → ℤ, (∀ i∈S, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈S, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f i n):ℂ)‖) ≤
          C*((1+Real.log K₀)*
            (∑ i∈S, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈S, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) := by
  classical
  obtain ⟨C,hC,hentry⟩ := double_difference_chosen_arcs_band_fourier hc hJ
  refine ⟨C,hC,?_⟩
  intro ι S F y rshift sshift L H anchor za N Q d w T M R hN hH hd hw hsmall hT hM hR
    hy hshifts hbase hf hbound hlower hphase hbuffer hfourBudget hquadBudget
    hQN hcut hmajor f hanchors
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNM : (N:ℝ) ≤ M := by linarith only [hbuffer,hNp]
  have hex i : ∃ b : ℚ, ∃ z : ℝ, i∈S →
      b.den ≤ Q ∧ Q ≤ 2*b.den ∧ (anchor i:ℝ) < b ∧
      |(b:ℝ)-(anchor i:ℝ)| ≤ c/(64*R^2) ∧
      z∈Icc (za i) (za i+(N:ℝ)/16) ∧
      iteratedDeriv 2 (f i) z/2=(b:ℝ) := by
    by_cases hi : i∈S
    · have hx : za i∈Icc (7*M/8) (17*M/8) := by
        have hh := (hanchors i hi).1
        have hb := hbase i hi
        constructor <;> linarith only [hh.1,hh.2,hb.1,hb.2,hNM]
      obtain ⟨b,hb,hhalf,hab,hclose,z,hz,he⟩ :=
        double_difference_dyadic_anchor_center F (hshifts i hi).1 (hshifts i hi).2.1 hd
          (hy i hi) (hshifts i hi).2.2.1 (hshifts i hi).2.2.2 hw hsmall hc hJ
          hT hM hNp hR hNM hphase hx hf hlower hbound (hcut i hi) (hmajor i hi) (hanchors i hi).2
      exact ⟨b,z,fun _ => ⟨hb,hhalf,hab,hclose,hz,he⟩⟩
    · exact ⟨anchor i,za i,fun h => (hi h).elim⟩
  choose r z hr using hex
  refine ⟨r,z,hr,?_⟩
  intro m A q μ ℓ U₃
  have hroots i (hi : i∈S) :
      z i∈Ioo ((L i:ℝ)-2*(N:ℝ)-(N:ℝ)/4)
        ((L i:ℝ)-2*(N:ℝ)+(N:ℝ)/4) ∧
      iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ) := by
    have hz := (hr i hi).2.2.2.2.1
    have ha := (hanchors i hi).1
    exact ⟨⟨by linarith only [hz.1,ha.1,hNp],
      by linarith only [hz.2,ha.2,hNp]⟩,(hr i hi).2.2.2.2.2⟩
  obtain ⟨hgeo,hminor,hcomplete⟩ := hentry ι S F y rshift sshift L H r z N d w T M R
    hN hH hd hw hsmall hT hM hR hy hshifts hbase hf hbound hlower
    hphase hbuffer hfourBudget hquadBudget hroots
  let lambda := c/(12*(N:ℝ)*R^2)
  have hgood i (hi : i∈S) : q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N := by
    refine ⟨(hr i hi).1.trans hQN,?_⟩
    have hcutR : 2*((anchor i).den:ℝ) ≤ Q := by exact_mod_cast hcut i hi
    have hqR : (Q:ℝ) ≤ 2*(q i:ℝ) := by exact_mod_cast (hr i hi).2.1
    have haQ : ((anchor i).den:ℝ) ≤ (q i:ℝ) := by linarith only [hcutR,hqR]
    have hprod : c*(Q:ℝ)*(anchor i).den ≤ 2*c*(q i:ℝ)^2 := by
      calc
        _ ≤ c*(2*(q i:ℝ))*(q i:ℝ) := by gcongr
        _ = _ := by ring
    have hbudget : 12*R^2 ≤ c*(q i:ℝ)^2 := by
      have hpositive : 0 < R^2 := by positivity
      nlinarith only [hmajor i hi,hprod,hpositive]
    have heq : lambda*(q i:ℝ)^2*N=c*(q i:ℝ)^2/(12*R^2) := by
      dsimp only [lambda]
      field_simp
    rw [heq]
    exact (one_le_div (by positivity : 0 < 12*R^2)).mpr hbudget
  have hGS : S.filter (fun i => q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)=S :=
    Finset.filter_eq_self.mpr hgood
  have hBad : S.filter (fun i => ¬ (q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N))=∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i hi hn
    exact hn (hgood i hi)
  dsimp only [q,lambda] at hGS hBad
  have hminor' : ∀ i∈S, 1 ≤ A i ∧ q i ≤ A i ∧ 1 ≤ μ i*(q i:ℝ)^2*A i := by
    simpa only [hGS] using hminor
  refine ⟨hgeo,hminor',?_⟩
  intro K₀ inst hK₀
  have hqG i (hi : i∈S.filter (fun i => q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)) :
      q i ≤ Q := (hr i (Finset.mem_filter.mp hi).1).1
  obtain ⟨hmesh,v,hv,hout⟩ := hcomplete Q hqG K₀ hK₀
  refine ⟨?_,v,?_,?_⟩
  · simpa only [hGS] using hmesh
  · simpa only [hGS] using hv
  · intro b τ s K x
    simpa only [hGS,hBad,Finset.sum_empty,zero_add] using hout

private theorem double_difference_minimal_anchor_roots_sharp_tail
    (S : Finset ℤ) (F : ℝ → ℝ) (N : ℕ) (base : ℝ)
    {r s d y w c U T M R : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hd : 0 < d)
    (hy : y∈Icc (1:ℝ) 2) (hprod : r*s=d*y)
    (hshift : r+s ≤ w) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hc : 0 < c) (hU : 0 < U) (hT : 0 < T) (hM : 0 < M)
    (hN : 0 < N) (hR : 0 < R) (hNM : (N:ℝ) ≤ M)
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hjets : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U)
    (hnegative : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c)
    (hpoints : ∀ j∈S, base+(N:ℝ)*j∈Icc (M+(N:ℝ)/4) (2*M-(N:ℝ)/4)) :
    let Φ := fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/d
    let f := fun v => T*Φ (v/M)
    let h := fun v => iteratedDeriv 2 f v/2
    let t := fun j : ℤ => base+(N:ℝ)*j
    let delta := c/(64*R^2)
    let heightCap := U*M/((N:ℝ)*R^2)
    ∃ (anchor : ℤ → ℚ) (za : ℤ → ℝ),
      (∀ j∈S, (anchor j:ℝ)∈Ioo (h (t j)-delta) (h (t j)+delta) ∧
        ∀ q : ℚ, (q:ℝ)∈Ioo (h (t j)-delta) (h (t j)+delta) → (anchor j).den ≤ q.den) ∧
      (∀ j∈S, h (za j)=(anchor j:ℝ) ∧ |za j-t j| ≤ (N:ℝ)/16 ∧ za j∈Icc M (2*M)) ∧
      Set.InjOn anchor (S : Set ℤ) ∧
      (∀ j∈S, |(anchor j:ℝ)| ≤ heightCap+delta) ∧
      ∀ Q : ℕ, 2 ≤ Q →
        let D := 64*R^2/(c*(Q:ℝ))
        (((S.filter (fun j => Q ≤ (anchor j).den)).card:ℝ)) ≤
          4*heightCap*D^2+3*D*(2+Real.log (D+1)) := by
  classical
  intro Φ f h t delta heightCap
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hXp : 0 ≤ heightCap := by dsimp only [heightCap]; positivity
  have hplain j (hj : j∈S) : t j∈Icc M (2*M) := by
    have hh := hpoints j hj
    constructor <;> linarith only [hh.1,hh.2,hNp]
  have hdata x (hx : x∈Icc (3*M/4) (9*M/4)) :=
    double_difference_physical_source_jets F hr hs hd hy hprod hshift hw hsmall hc hU hT hM
      hx hf hlower hjets
  have hcf x (hx : x∈Icc (3*M/4) (9*M/4)) : ContDiffAt ℝ 3 f x :=
    ((hdata x hx).1 x (by linarith only [hx.1,hM])).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  let L := c*T/(8*M^3)
  have hL : 0 < L := by dsimp only [L]; positivity
  have hthree x (hx : x∈Icc (3*M/4) (9*M/4)) : L ≤ iteratedDeriv 3 f x := by
    have hh := (hdata x hx).2.1
    have he : c*T/(2*M^3)=4*L := by dsimp only [L]; ring
    rw [he] at hh
    linarith only [hh,hL]
  have hcurv j (hj : j∈S) : |h (t j)| ≤ heightCap := by
    have hprodpos : 0 < r*s := by rw [hprod]; exact mul_pos hd (by linarith only [hy.1])
    have hrp : 0 < r := by nlinarith only [hr,hs,hprodpos]
    have hsp : 0 < s := by nlinarith only [hr,hs,hprodpos]
    have hh := (double_difference_physical_curvature_band F (hplain j hj) hy hrp hsp hd
      hc hU hT hM hprod (hshift.trans hw) hf hnegative
      (fun u hu => hjets u hu 4 (by norm_num) (by norm_num))).2
    have he : U*T/M^2=heightCap := by
      dsimp only [heightCap]
      apply (div_eq_div_iff (by positivity) (by positivity)).mpr
      calc
        U*T*((N:ℝ)*R^2)=U*(T*(N:ℝ)*R^2) := by ring
        _ = U*M^3 := by rw [hphase]
        _ = U*M*M^2 := by ring
    exact hh.trans_eq he
  have hmul j : (S.filter (fun k => id k=j)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi k hk
    exact ((Finset.mem_filter.mp hi).2).trans ((Finset.mem_filter.mp hk).2).symm
  obtain ⟨anchor,za,hanchors,_hweak⟩ :=
    TaoTrudgianYang2025.exists_bourgain_C3_minimal_curvature_arc_count S f id N 1 base
      hN hL hXp hcf hthree hmul
      (by
        intro j hj v hv
        have hp := hplain j hj
        change t j-(N:ℝ)/4 ≤ v ∧ v ≤ t j+(N:ℝ)/4 at hv
        constructor <;> linarith only [hp.1,hp.2,hv.1,hv.2,hNM])
      hcurv
  have hdeltaEq : L*(N:ℝ)/8=delta := by
    dsimp only [L,delta]
    rw [←hphase]
    field_simp
    ring
  have hanchors' j (hj : j∈S) :
      za j∈Ioo (t j-(N:ℝ)/4) (t j+(N:ℝ)/4) ∧
      h (za j)=(anchor j:ℝ) ∧
      (anchor j:ℝ)∈Ioo (h (t j)-delta) (h (t j)+delta) ∧
      ∀ q : ℚ, (q:ℝ)∈Ioo (h (t j)-delta) (h (t j)+delta) → (anchor j).den ≤ q.den := by
    simpa only [hdeltaEq, id_eq] using hanchors j hj
  let eta := c/(4*R^2)
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hgrow x z (hx : x∈Icc M (2*M)) (hz : z∈Icc M (2*M)) (hxz : x ≤ z) :
      c*T/(4*M^3)*(z-x) ≤ h z-h x := by
    apply double_difference_physical_curvature_growth F hr hs hd hy hprod hshift hw hsmall
      hc hU hT hM _ _ hxz hf hlower hjets
    · constructor <;> linarith only [hx.1,hx.2,hM]
    · constructor <;> linarith only [hz.1,hz.2,hM]
  have hsepOrdered i (hi : i∈S) j (hj : j∈S) (hij : t i ≤ t j) :
      eta*|(i:ℝ)-j| ≤ |h (t i)-h (t j)| := by
    have hiR : (i:ℝ) ≤ j := by
      apply (mul_le_mul_iff_right₀ hNp).mp
      dsimp only [t] at hij
      linarith only [hij]
    calc
      _ = (c*T/(4*M^3))*(t j-t i) := by
        rw [abs_of_nonpos (sub_nonpos.mpr hiR)]
        dsimp only [eta,t]
        rw [←hphase]
        field_simp
        ring
      _ ≤ h (t j)-h (t i) := hgrow _ _ (hplain i hi) (hplain j hj) hij
      _ ≤ |h (t j)-h (t i)| := le_abs_self _
      _ = _ := abs_sub_comm _ _
  have hsep i (hi : i∈S) j (hj : j∈S) : eta*|(i:ℝ)-j| ≤ |h (t i)-h (t j)| := by
    rcases le_total (t i) (t j) with hij | hji
    · exact hsepOrdered i hi j hj hij
    · simpa only [abs_sub_comm] using hsepOrdered j hj i hi hji
  have hnear j (hj : j∈S) : |(anchor j:ℝ)-h (t j)| ≤ delta := by
    have hh := (hanchors' j hj).2.2.1
    exact abs_le.mpr ⟨by linarith only [hh.1],by linarith only [hh.2]⟩
  have hroots j (hj : j∈S) :
      h (za j)=(anchor j:ℝ) ∧ |za j-t j| ≤ (N:ℝ)/16 ∧ za j∈Icc M (2*M) := by
    have hh := hanchors' j hj
    have hp := hpoints j hj
    have hz : za j∈Icc M (2*M) := by
      constructor <;> linarith only [hh.1.1,hh.1.2,hp.1,hp.2]
    have hrate : c*T/(4*M^3)*((N:ℝ)/16)=delta := by
      dsimp only [delta]
      rw [←hphase]
      field_simp
      ring
    refine ⟨hh.2.1,?_,hz⟩
    have hn := hnear j hj
    rw [←hh.2.1] at hn
    rcases le_total (t j) (za j) with hle | hle
    · have hg := hgrow _ _ (hplain j hj) hz hle
      rw [abs_of_nonneg (sub_nonneg.mpr hle)]
      apply (mul_le_mul_iff_right₀ (show 0 < c*T/(4*M^3) by positivity)).mp
      rw [hrate]
      exact hg.trans ((le_abs_self _).trans hn)
    · have hg := hgrow _ _ hz (hplain j hj) hle
      rw [abs_of_nonpos (sub_nonpos.mpr hle),neg_sub]
      apply (mul_le_mul_iff_right₀ (show 0 < c*T/(4*M^3) by positivity)).mp
      rw [hrate]
      rw [abs_sub_comm] at hn
      exact hg.trans ((le_abs_self _).trans hn)
  have hinj : Set.InjOn anchor (S : Set ℤ) := by
    intro i hi j hj he
    have hh := hsep i hi j hj
    have hdiff : |h (t i)-h (t j)| ≤ 2*delta := by
      calc
        _ = |(h (t i)-(anchor i:ℝ))+((anchor j:ℝ)-h (t j))| := by rw [he]; congr 1; ring
        _ ≤ |h (t i)-(anchor i:ℝ)|+|(anchor j:ℝ)-h (t j)| := abs_add_le _ _
        _ ≤ delta+delta := by rw [abs_sub_comm (h (t i))]; exact add_le_add (hnear i hi) (hnear j hj)
        _ = _ := by ring
    have he : 2*delta=eta/8 := by dsimp only [delta,eta]; ring
    rw [he] at hdiff
    have hiR : |(i:ℝ)-j| < 1 := by nlinarith only [hh,hdiff,heta]
    have hiZ : |i-j| < 1 := by exact_mod_cast hiR
    exact sub_eq_zero.mp (Int.abs_lt_one_iff.mp hiZ)
  refine ⟨anchor,za,(fun j hj => (hanchors' j hj).2.2),hroots,hinj,?_,?_⟩
  · intro j hj
    calc
      |(anchor j:ℝ)| = |((anchor j:ℝ)-h (t j))+h (t j)| := by rw [sub_add_cancel]
      _ ≤ |(anchor j:ℝ)-h (t j)|+|h (t j)| := abs_add_le _ _
      _ ≤ delta+heightCap := add_le_add (hnear j hj) (hcurv j hj)
      _ = _ := by ring
  · intro Q hQ D
    have hwidth : 4*delta ≤ eta := by
      have he : 4*delta=eta/4 := by dsimp only [delta,eta]; ring
      rw [he]
      linarith only [heta]
    have hh := TaoTrudgianYang2025.bourgain_actual_minimal_arc_sharp_tail S id (fun j => h (t j))
      anchor 1 heta hdelta hXp hwidth hmul hsep hcurv
      (fun j hj => (hanchors' j hj).2.2.2) Q hQ
    have he : 1/(delta*(Q:ℝ))=D := by dsimp only [delta,D]; field_simp
    simpa only [he,Nat.cast_one,one_mul] using hh

private theorem double_difference_minimal_anchor_complement

    (S : Finset ℤ) (F : ℝ → ℝ) (N : ℕ) (base : ℝ)
    {r s d y w c U T M R : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hd : 0 < d)
    (hy : y∈Icc (1:ℝ) 2) (hprod : r*s=d*y)
    (hshift : r+s ≤ w) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hc : 0 < c) (hU : 0 < U) (hT : 0 < T) (hM : 0 < M)
    (hN : 0 < N) (hR : 0 < R) (hNM : (N:ℝ) ≤ M)
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hjets : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U)
    (hnegative : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c)
    (hpoints : ∀ j∈S, base+(N:ℝ)*j∈Icc (M+(N:ℝ)/4) (2*M-(N:ℝ)/4)) :
    let Φ := fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/d
    let f := fun v => T*Φ (v/M)
    let h := fun v => iteratedDeriv 2 f v/2
    let t := fun j : ℤ => base+(N:ℝ)*j
    let delta := c/(64*R^2)
    let heightCap := U*M/((N:ℝ)*R^2)
    ∃ (anchor : ℤ → ℚ) (za : ℤ → ℝ),
      (∀ j∈S, (anchor j:ℝ)∈Ioo (h (t j)-delta) (h (t j)+delta) ∧
        ∀ q : ℚ, (q:ℝ)∈Ioo (h (t j)-delta) (h (t j)+delta) → (anchor j).den ≤ q.den) ∧
      (∀ j∈S, h (za j)=(anchor j:ℝ) ∧ |za j-t j| ≤ (N:ℝ)/16 ∧ za j∈Icc M (2*M)) ∧
      ∀ (Q Acut : ℕ) (Bmajor : ℝ), 2 ≤ Acut → Acut ≤ Q → 0 ≤ Bmajor →
    let Bad := S.filter (fun i => ¬ (Acut*(anchor i).den ≤ Q ∧
      Bmajor*R^2 ≤ c*(Q:ℝ)*(anchor i).den))
    let Dlow := Bmajor*R^2/(c*(Q:ℝ))
    let Khigh := Q/Acut+1
    let Dhigh := 64*R^2/(c*(Khigh:ℝ))
    let Cost := 4*heightCap*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
      Dlow*(2*(heightCap+delta)*Dlow+1)
    (Bad.card:ℝ) ≤ Cost ∧
      ∀ H : ℤ → ℕ, (∀ i∈S, H i ≤ N) →
        (∑ i∈Bad,(H i:ℝ)) ≤ (N:ℝ)*Cost := by
  classical
  intro Φ f h t delta heightCap
  obtain ⟨anchor,za,hanchor,hroots,hinj,hvalues,hhighAll⟩ :=
    double_difference_minimal_anchor_roots_sharp_tail S F N base hr hs hd hy hprod
      hshift hw hsmall hc hU hT hM hN hR hNM hphase hf hlower hjets hnegative hpoints
  refine ⟨anchor,za,hanchor,hroots,?_⟩
  intro Q Acut Bmajor hAcut hAQ hBmajor Bad Dlow Khigh Dhigh Cost
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hQ : 0 < Q := by omega
  have hQr : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hApos : 0 < Acut := by omega
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hV : 0 ≤ heightCap := by dsimp only [heightCap]; positivity
  have hDlow : 0 ≤ Dlow := by dsimp only [Dlow]; positivity
  have hK : 2 ≤ Khigh := by
    have hh : 1 ≤ Q/Acut := (Nat.le_div_iff_mul_le hApos).mpr (by simpa only [one_mul] using hAQ)
    dsimp only [Khigh]
    omega
  let High := S.filter (fun i => Khigh ≤ (anchor i).den)
  have hhigh : (High.card:ℝ) ≤ 4*heightCap*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1)) :=
    hhighAll Khigh hK
  let Low := S.filter (fun i => c*(Q:ℝ)*(anchor i).den < Bmajor*R^2)
  have hlowden i (hi : i∈Low) : (anchor i).den ≤ ⌊Dlow⌋₊ := by
    apply Nat.le_floor
    apply (le_div_iff₀ (mul_pos hc hQr)).mpr
    have hh := (Finset.mem_filter.mp hi).2
    nlinarith only [hh]
  have hlow : (Low.card:ℝ) ≤ Dlow*(2*(heightCap+delta)*Dlow+1) := by
    have hcount := bourgain_bounded_denominator_count Low anchor ⌊Dlow⌋₊ 1
      (add_nonneg hV hdelta.le) (fun i hi => hvalues i (Finset.mem_filter.mp hi).1) hlowden
      (by
        intro a
        apply Finset.card_le_one.mpr
        intro i hi j hj
        obtain ⟨hiL,hia⟩ := Finset.mem_filter.mp hi
        obtain ⟨hjL,hja⟩ := Finset.mem_filter.mp hj
        exact hinj (Finset.mem_filter.mp hiL).1 (Finset.mem_filter.mp hjL).1 (hia.trans hja.symm))
    simp only [Nat.cast_one,one_mul] at hcount
    apply hcount.trans
    have hfloor : (⌊Dlow⌋₊:ℝ) ≤ Dlow := Nat.floor_le hDlow
    gcongr
  have hsub : Bad⊆High∪Low := by
    intro i hi
    obtain ⟨hiS,hbad⟩ := Finset.mem_filter.mp hi
    rcases not_and_or.mp hbad with hlarge | hsmall
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨hiS,?_⟩
      have hh : Q/Acut < (anchor i).den :=
        (Nat.div_lt_iff_lt_mul hApos).mpr (by simpa only [mul_comm] using lt_of_not_ge hlarge)
      exact Nat.succ_le_of_lt hh
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hiS,lt_of_not_ge hsmall⟩)
  have hcard : (Bad.card:ℝ) ≤ Cost := by
    have hh : (Bad.card:ℝ) ≤ (High.card:ℝ)+(Low.card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    exact hh.trans (add_le_add hhigh hlow)
  refine ⟨hcard,?_⟩
  intro H hH
  calc
    (∑ i∈Bad,(H i:ℝ)) ≤ ∑ _i∈Bad,(N:ℝ) := Finset.sum_le_sum (fun i hi =>
      Nat.cast_le.mpr (hH i (Finset.mem_filter.mp hi).1))
    _ = (N:ℝ)*(Bad.card:ℝ) := by simp only [Finset.sum_const,nsmul_eq_mul,mul_comm]
    _ ≤ (N:ℝ)*Cost := mul_le_mul_of_nonneg_left hcard hNp.le

private theorem double_difference_two_probe_dyadic_band_card
    (S : Finset ℤ) (F : ℝ → ℝ) (N Qbase kmax Acut : ℕ) (base : Fin 2 → ℝ) (Bmajor : ℝ)
    {r s d y w c U T M R : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hd : 0 < d)
    (hy : y∈Icc (1:ℝ) 2) (hprod : r*s=d*y)
    (hshift : r+s ≤ w) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hc : 0 < c) (hU : 0 < U) (hT : 0 < T) (hM : 0 < M)
    (hN : 0 < N) (hR : 0 < R) (hNM : (N:ℝ) ≤ M)
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hjets : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U)
    (hnegative : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c)
    (hAcut : 2 ≤ Acut) (hAQ : Acut ≤ Qbase) (hBmajor : 0 ≤ Bmajor)
    (hpoints : ∀ j∈S, ∀ i, base i+(N:ℝ)*j∈Icc (M+(N:ℝ)/4) (2*M-(N:ℝ)/4)) :
    let f := fun v => T*((F (v/M)-F (v/M+r)-F (v/M+s)+F (v/M+r+s))/d)
    let h := fun w => iteratedDeriv 2 f w/2
    let t := fun (j : ℤ) (i : Fin 2) => base i+(N:ℝ)*j
    let delta := c/(64*R^2)
    let Q := fun k : ℕ => Qbase*2^k
    let Vbound := U*M/((N:ℝ)*R^2)
    let Cost := fun q : ℕ =>
      let Dlow := Bmajor*R^2/(c*(q:ℝ))
      let Dhigh := 64*R^2/(c*((q/Acut+1:ℕ):ℝ))
      4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
        Dlow*(2*(Vbound+delta)*Dlow+1)
    ∃ (anchor : ℤ → Fin 2 → ℚ) (band : ℤ → Option ℕ) (za : ℤ → Fin 2 → ℝ),
      (∀ j∈S, ∀ i, (anchor j i:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) ∧
        ∀ q : ℚ, (q:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
          (anchor j i).den ≤ q.den) ∧
      (∀ j∈S, ∀ i, h (za j i)=(anchor j i:ℝ) ∧
        |za j i-t j i| ≤ (N:ℝ)/16 ∧ za j i∈Icc M (2*M)) ∧
      let Good := fun j k (i : Fin 2) =>
        Acut*(anchor j i).den ≤ Q k ∧
          Bmajor*R^2 ≤ c*(Q k:ℝ)*(anchor j i).den
      (∀ j, match band j with
        | none => ∃ i, ¬Good j kmax i
        | some k => k ≤ kmax ∧ (∀ i, Good j k i) ∧
            (k=0 ∨ ∃ i, ¬Good j (k-1) i)) ∧
      (∀ j∈S, ∀ k, band j=some k → ∀ i, ∀ q : ℚ,
        (q:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
        (∀ r : ℚ, (r:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
          q.den ≤ r.den) →
        Acut*q.den ≤ Q k ∧ Bmajor*R^2 ≤ c*(Q k:ℝ)*q.den) ∧
      (∀ k, ((S.filter (fun j => band j=some (k+1))).card:ℝ) ≤ 2*Cost (Q k)) ∧
      ((S.filter (fun j => band j=none)).card:ℝ) ≤ 2*Cost (Q kmax) := by
  classical
  intro f h t delta Q Vbound Cost
  choose a z ha hz hcomplement using
    fun i => double_difference_minimal_anchor_complement S F N (base i) hr hs hd hy hprod
      hshift hw hsmall hc hU hT hM hN hR hNM hphase hf hlower hjets hnegative
      (fun j hj => hpoints j hj i)
  let anchor := fun j i => a i j
  let za := fun j i => z i j
  have hanchor j (hj : j∈S) i :
      (anchor j i:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) ∧
        ∀ q : ℚ, (q:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
          (anchor j i).den ≤ q.den := ha i j hj
  have hroots j (hj : j∈S) i : h (za j i)=(anchor j i:ℝ) ∧
      |za j i-t j i| ≤ (N:ℝ)/16 ∧ za j i∈Icc M (2*M) := hz i j hj
  let Good := fun (j : ℤ) (k : ℕ) (i : Fin 2) =>
    Acut*(anchor j i).den ≤ Q k ∧
      Bmajor*R^2 ≤ c*(Q k:ℝ)*(anchor j i).den
  have hchoose j : ∃ label : Option ℕ, match label with
      | none => ∃ i, ¬Good j kmax i
      | some k => k ≤ kmax ∧ (∀ i, Good j k i) ∧
          (k=0 ∨ ∃ i, ¬Good j (k-1) i) := by
    by_cases hlast : ∀ i, Good j kmax i
    · have he : ∃ k : ℕ, k ≤ kmax ∧ ∀ i, Good j k i :=
        ⟨kmax,le_rfl,hlast⟩
      let k := Nat.find he
      have hk : k ≤ kmax ∧ ∀ i, Good j k i := Nat.find_spec he
      refine ⟨some k,hk.1,hk.2,?_⟩
      by_cases hz : k=0
      · exact Or.inl hz
      · right
        by_contra hno
        have hall : ∀ i, Good j (k-1) i := not_exists_not.mp hno
        exact Nat.find_min he (show k-1 < k by omega)
          ⟨(Nat.sub_le k 1).trans hk.1,hall⟩
    · exact ⟨none,not_forall.mp hlast⟩
  choose band hband using hchoose
  have hqA k : Acut ≤ Q k :=
    hAQ.trans (Nat.le_mul_of_pos_right Qbase (pow_pos (by decide : 0 < (2:ℕ)) k))
  have hbadcard k :
      ((S.filter (fun j => ∃ i, ¬Good j k i)).card:ℝ) ≤ 2*Cost (Q k) := by
    let Bad := fun i : Fin 2 => S.filter (fun j => ¬Good j k i)
    have hone (i : Fin 2) : ((Bad i).card:ℝ) ≤ Cost (Q k) :=
      (hcomplement i (Q k) Acut Bmajor hAcut (hqA k) hBmajor).1
    have hsub : S.filter (fun j => ∃ i, ¬Good j k i) ⊆ Bad 0 ∪ Bad 1 := by
      intro j hj
      obtain ⟨hjS,i,hi⟩ := Finset.mem_filter.mp hj
      fin_cases i
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hjS,hi⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hjS,hi⟩)
    have hh : ((S.filter (fun j => ∃ i, ¬Good j k i)).card:ℝ) ≤
        ((Bad 0).card:ℝ)+((Bad 1).card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hzero := hone 0
    have hone' := hone 1
    linarith only [hh,hzero,hone']
  refine ⟨anchor,band,za,hanchor,hroots,?_⟩
  change (∀ j, match band j with
    | none => ∃ i, ¬Good j kmax i
    | some k => k ≤ kmax ∧ (∀ i, Good j k i) ∧
      (k=0 ∨ ∃ i, ¬Good j (k-1) i)) ∧ _
  refine ⟨hband,?_,?_,?_⟩
  · intro j hjS k hj i q hq hmin
    have hd := hband j
    rw [hj] at hd
    have hsame : q.den=(anchor j i).den :=
      Nat.le_antisymm (hmin _ (hanchor j hjS i).1) ((hanchor j hjS i).2 q hq)
    rw [hsame]
    exact hd.2.1 i
  · intro k
    have hsub : S.filter (fun j => band j=some (k+1)) ⊆
        S.filter (fun j => ∃ i, ¬Good j k i) := by
      intro j hj
      obtain ⟨hjS,hjband⟩ := Finset.mem_filter.mp hj
      have hd := hband j
      rw [hjband] at hd
      refine Finset.mem_filter.mpr ⟨hjS,?_⟩
      rcases hd.2.2 with hz | hprev
      · omega
      · simpa only [Nat.add_sub_cancel] using hprev
    exact (show ((S.filter (fun j => band j=some (k+1))).card:ℝ) ≤
      ((S.filter (fun j => ∃ i, ¬Good j k i)).card:ℝ) by
        exact_mod_cast Finset.card_le_card hsub).trans (hbadcard k)
  · have hsub : S.filter (fun j => band j=none) ⊆
        S.filter (fun j => ∃ i, ¬Good j kmax i) := by
      intro j hj
      obtain ⟨hjS,hjband⟩ := Finset.mem_filter.mp hj
      have hd := hband j
      rw [hjband] at hd
      exact Finset.mem_filter.mpr ⟨hjS,hd⟩
    exact (show ((S.filter (fun j => band j=none)).card:ℝ) ≤
      ((S.filter (fun j => ∃ i, ¬Good j kmax i)).card:ℝ) by
        exact_mod_cast Finset.card_le_card hsub).trans (hbadcard kmax)

private theorem double_difference_two_probe_dyadic_quadratic_density
    (S : Finset ℤ) (F : ℝ → ℝ) (N Qbase kmax Acut : ℕ) (base : Fin 2 → ℝ) (Bmajor : ℝ)
    {r s d y w c U T M R : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hd : 0 < d)
    (hy : y∈Icc (1:ℝ) 2) (hprod : r*s=d*y)
    (hshift : r+s ≤ w) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hc : 0 < c) (hU : 0 < U) (hT : 0 < T) (hM : 0 < M)
    (hN : 0 < N) (hR : 0 < R)
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hjets : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U)
    (hnegative : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c)
    (hAcut : 2 ≤ Acut) (hAQ : Acut ≤ Qbase) (hBmajor : 0 ≤ Bmajor)
    (hpoints : ∀ j∈S, ∀ i, base i+(N:ℝ)*j∈Icc (M+(N:ℝ)/4) (2*M-(N:ℝ)/4))
    (hNQmax : (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M) :
    let f := fun v => T*((F (v/M)-F (v/M+r)-F (v/M+s)+F (v/M+r+s))/d)
    let h := fun w => iteratedDeriv 2 f w/2
    let t := fun (j : ℤ) (i : Fin 2) => base i+(N:ℝ)*j
    let delta := c/(64*R^2)
    let Q := fun k : ℕ => Qbase*2^k
    let Ctail := 4*U*(64/c)^2+192/c
    let Clow := (2*U+c/32)*(Bmajor/c)^2+Bmajor/c
    let Cerror := (Acut:ℝ)^2*Ctail+Clow
    let Density := fun k => 2*Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (64*R^2/(c*((Q k:ℝ)/Acut))+1))
    ∃ (anchor : ℤ → Fin 2 → ℚ) (band : ℤ → Option ℕ) (za : ℤ → Fin 2 → ℝ),
      (∀ j∈S, ∀ i, (anchor j i:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) ∧
        ∀ q : ℚ, (q:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
          (anchor j i).den ≤ q.den) ∧
      (∀ j∈S, ∀ i, h (za j i)=(anchor j i:ℝ) ∧
        |za j i-t j i| ≤ (N:ℝ)/16 ∧ za j i∈Icc M (2*M)) ∧
      let Good := fun j k (i : Fin 2) =>
        Acut*(anchor j i).den ≤ Q k ∧
          Bmajor*R^2 ≤ c*(Q k:ℝ)*(anchor j i).den
      (∀ j, match band j with
        | none => ∃ i, ¬Good j kmax i
        | some k => k ≤ kmax ∧ (∀ i, Good j k i) ∧
            (k=0 ∨ ∃ i, ¬Good j (k-1) i)) ∧
      (∀ j∈S, ∀ k, band j=some k → ∀ i, ∀ q : ℚ,
        (q:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
        (∀ r : ℚ, (r:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
          q.den ≤ r.den) →
        Acut*q.den ≤ Q k ∧ Bmajor*R^2 ≤ c*(Q k:ℝ)*q.den) ∧
      (∀ k ≤ kmax, ((S.filter (fun j => band j=some (k+1))).card:ℝ) ≤ Density k) ∧
      ((S.filter (fun j => band j=none)).card:ℝ) ≤ Density kmax := by
  classical
  intro f h t delta Q Ctail Clow Cerror Density
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hqbase : 1 ≤ Qbase := by omega
  have hqmax : 1 ≤ Qbase*2^kmax :=
    hqbase.trans (Nat.le_mul_of_pos_right Qbase (pow_pos (by decide) kmax))
  have hqmaxR : (1:ℝ) ≤ (Qbase*2^kmax:ℕ) := by exact_mod_cast hqmax
  have hNM : (N:ℝ) ≤ M := by nlinarith only [hNQmax,hqmaxR,hNp]
  obtain ⟨anchor,band,za,hanchor,hroots,hband,htransfer,hcounts,htail⟩ :=
    double_difference_two_probe_dyadic_band_card S F N Qbase kmax Acut base Bmajor
      hr hs hd hy hprod hshift hw hsmall hc hU hT hM hN hR hNM hphase hf hlower hjets
      hnegative hAcut hAQ hBmajor hpoints
  let Vbound := U*M/((N:ℝ)*R^2)
  let Cost := fun q : ℕ =>
    let Dlow := Bmajor*R^2/(c*(q:ℝ))
    let Dhigh := 64*R^2/(c*((q/Acut+1:ℕ):ℝ))
    4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
      Dlow*(2*(Vbound+delta)*Dlow+1)
  have hcost k (hk : k ≤ kmax) : 2*Cost (Q k) ≤ Density k := by
    have hqA : Acut ≤ Q k :=
      hAQ.trans (Nat.le_mul_of_pos_right Qbase (pow_pos (by decide : 0 < (2:ℕ)) k))
    have hqmax : Q k ≤ Q kmax :=
      Nat.mul_le_mul_left Qbase (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hk)
    have hNQ : (N:ℝ)*(Q k:ℝ) ≤ M :=
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hqmax) (Nat.cast_nonneg N)).trans hNQmax
    have hh := huxley_anchor_complement_quadratic_density_scale (Q k) Acut
      (σ:=1) (J:=2*U/3) (by norm_num) hc (by positivity) hM hNp hR hAcut hqA hBmajor hNQ
    have hthree : 3*(2*U/3)=2*U := by ring
    have hsix : 6*(2*U/3)=4*U := by ring
    have hV : 2*U*M/(2*(N:ℝ)*R^2)=Vbound := by dsimp only [Vbound]; ring
    have hbound : Cost (Q k) ≤ Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
        (2+Real.log (64*R^2/(c*((Q k:ℝ)/Acut))+1)) := by
      simpa only [mul_one,one_mul,div_one,hthree,hsix,hV] using hh
    calc
      _ ≤ 2*(Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
          (2+Real.log (64*R^2/(c*((Q k:ℝ)/Acut))+1))) :=
        mul_le_mul_of_nonneg_left hbound (by norm_num)
      _ = _ := by dsimp only [Density]; ring
  refine ⟨anchor,band,za,hanchor,hroots,?_⟩
  intro Good
  exact ⟨hband,htransfer,fun k hk => (hcounts k).trans (hcost k hk),
    htail.trans (hcost kmax le_rfl)⟩

private theorem double_difference_constructed_reference_system_charts
    (F rshift sshift : ℝ → ℝ) (Y : Finset ℝ) {c J d w T M N R U : ℝ}
    (hc : 0 < c) (hJ : 0 < J) (hd : 0 < d)
    (hw : w ≤ 1/4) (hsmallShift : 2*J*w ≤ c/64)
    (hy : ∀ y∈Y, y∈Icc (1:ℝ) 2)
    (hshifts : ∀ y∈Y, 0 ≤ rshift y ∧ 0 ≤ sshift y ∧
      rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ w)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hbound : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ J)
    (hnegative : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hU : 0 < U) (hUmax : U ≤ R^2) (hphase : T*N*R^2=M^3) :
    let Φ := fun y u => (F u-F (u+rshift y)-F (u+sshift y)+F (u+rshift y+sshift y))/d
    let f := fun y v => T*Φ y (v/M)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let curvatureScale := J*T/M^2
    ∃ H : ℤ, 2 ≤ H ∧ (H:ℝ)<4*R^2/U ∧ ∃ S : Finset ℝ,
      (∀ q : ℚ, (q.den:ℤ) ≤ H → |(q:ℝ)| ≤ curvatureScale → (q:ℝ) ∈ S) ∧
      (∀ a ∈ S, ∀ b ∈ S, ∀ q : ℚ, (q.den:ℤ) ≤ H →
        (q:ℝ) ∈ Icc a b → (q:ℝ) ∈ S) ∧
      (∃ l ∈ S, ∃ u ∈ S, l ≤ -curvatureScale ∧ curvatureScale ≤ u) ∧
      (∀ z ∈ S, |z| ≤ curvatureScale+1) ∧
      (∀ z∈S, ∃ a b : ℤ, z=(a:ℝ)/b ∧ IsCoprime a b ∧ 0 < b ∧
        (b:ℝ)<4*R^2/U ∧ |(a:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U)) ∧
      (∀ y∈Y, ∀ x ∈ Icc M (2*M), |h y x| ≤ curvatureScale) ∧
      (∀ z ∈ S,
        (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ H) ∨
        (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
          R^2 ≤ U*(n:ℝ)^2 ∧ 0 < v ∧ v ≤ H ∧ (u:ℝ)/v ∈ S ∧ |m*v-u*n|=1)) ∧
      (∀ x ∈ S, ∀ z ∈ S, x ≠ z → U/(4*R^2) < |x-z|) ∧
      (∀ y∈Y, ∀ x ∈ Icc M (2*M),
        ∃ q ∈ S, |h y x-q| ≤ 7*U/(4*R^2)) ∧
      (∀ y∈Y, ∀ q ∈ S,
        q ∈ Icc (h y M) (h y (2*M)) →
        ∃ x ∈ Icc M (2*M), h y x=q) ∧
      (∀ a ∈ S, ∀ b ∈ S, a < b →
        (∀ z ∈ S, ¬ (a < z ∧ z < b)) →
        U/(4*R^2) < b-a ∧ b-a ≤ 7*U/(2*R^2) ∧
        (∃ m n u v : ℤ, a=(m:ℝ)/n ∧ b=(u:ℝ)/v ∧
          IsCoprime m n ∧ IsCoprime u v ∧ 0 < n ∧ 0 < v ∧
          R^2 ≤ U*((max n v:ℤ):ℝ)^2) ∧
        (∀ y∈Y, ∀ x ∈ Icc M (2*M), ∀ z ∈ Icc M (2*M),
          h y x=a → h y z=b → |z-x| ≤ (14/c)*U*N)) ∧
      (∀ a∈S, ∀ b∈S, a < b → (∀ z∈S, ¬(a < z ∧ z < b)) →
        ∃ e r v s : ℤ, v*r-e*s=1 ∧
          ((0 < r ∧ (e:ℝ)/r=a) ∨ (r < 0 ∧ (e:ℝ)/r=b)) ∧
          s≠0 ∧ (e:ℝ)/r∈S ∧ (v:ℝ)/s∈S ∧ R^2 ≤ (r:ℝ)^2*U ∧
          |(r:ℝ)| < 4*R^2/U ∧ |(s:ℝ)| < 4*R^2/U ∧
          |(e:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U) ∧
          |(v:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U)) := by
  intro Φ f h curvatureScale
  obtain ⟨H,hH,hHeight,S,hseed,hhull,henclose,hpoints,hheights,hcurv,hlabels,hsep,hcover,hroots,hgaps⟩ :=
    double_difference_constructed_reference_system_bounded F rshift sshift Y hc hJ hd hw hsmallShift
      hy hshifts hf hlower hbound hnegative hT hM hN hR hU hUmax hphase
  refine ⟨H,hH,hHeight,S,hseed,hhull,henclose,hpoints,hheights,hcurv,hlabels,hsep,hcover,hroots,hgaps,?_⟩
  intro a ha b hb hab hadj
  apply actual_reference_gap_oriented_chart S hR hU
    (show 0 ≤ curvatureScale by dsimp only [curvatureScale]; positivity)
    hhull hpoints _ hsep ha hb hab hadj (hgaps a ha b hb hab hadj).2.2.1
  intro z hz
  rcases hlabels z hz with hsmall | ⟨m,n,u,v,hval,hcop,hn,_hlarge,hv,hvH,hparent,hdet⟩
  · exact Or.inl hsmall
  · exact Or.inr ⟨m,n,u,v,hval,hcop,hn,hv,hvH,hparent,hdet⟩

private theorem double_difference_constructed_reference_gap_factory
    (F rshift sshift : ℝ → ℝ) (Y : Finset ℝ) {c J d w T M R U : ℝ}
    (hc : 0 < c) (hJ : 0 < J) (hd : 0 < d)
    (hw : w ≤ 1/4) (hsmallShift : 2*J*w ≤ c/64)
    (hy : ∀ y∈Y, y∈Icc (1:ℝ) 2)
    (hshifts : ∀ y∈Y, 0 ≤ rshift y ∧ 0 ≤ sshift y ∧
      rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ w)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hbound : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ J)
    (hnegative : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hR : 0 < R)
    (hU : 0 < U) (hUmax : U ≤ R^2) :
    let Φ := fun y u => (F u-F (u+rshift y)-F (u+sshift y)+F (u+rshift y+sshift y))/d
    let f := fun y v => T*Φ y (v/M)
    let h := fun y z => iteratedDeriv 2 (f y) z/2
    let curvatureScale := J*T/M^2
    ∃ (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) (e r v s : ℝ × ℝ → ℤ),
      (∀ a∈Refs, ∀ b∈Refs, a≠b → U/(4*R^2) < |a-b|) ∧
      (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
        ∀ z∈Refs, ¬(ab.1 < z ∧ z < ab.2)) ∧
      (∀ ab∈Gaps, v ab*r ab-e ab*s ab=1) ∧
      (∀ ab∈Gaps, (((0:ℝ) < r ab ∧ (e ab:ℝ)/r ab=ab.1) ∨
        ((r ab:ℝ) < 0 ∧ (e ab:ℝ)/r ab=ab.2))) ∧
      (∀ ab∈Gaps, s ab≠0) ∧
      (∀ ab∈Gaps, (e ab:ℝ)/r ab∈Refs) ∧
      (∀ ab∈Gaps, (v ab:ℝ)/s ab∈Refs) ∧
      (∀ ab∈Gaps, R^2 ≤ (r ab:ℝ)^2*U) ∧
      (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*U/(2*R^2)) ∧
      (∀ ab∈Gaps, |(r ab:ℝ)| ≤ 4*R^2/U) ∧
      (∀ ab∈Gaps, |(s ab:ℝ)| ≤ 4*R^2/U) ∧
      (∀ ab∈Gaps, |(e ab:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U)) ∧
      (∀ ab∈Gaps, |(v ab:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U)) ∧
      ∀ y∈Y, ∀ z∈Icc M (2*M), ∃ ab∈Gaps, h y z∈Icc ab.1 ab.2 := by
  classical
  intro Φ f h curvatureScale
  let Nref := M^3/(T*R^2)
  have hNref : 0 < Nref := by dsimp only [Nref]; positivity
  have hphase : T*Nref*R^2=M^3 := by dsimp only [Nref]; field_simp
  obtain ⟨H,_hH,_hHeight,Refs,_hseed,_hhull,henclose,_hpoints,_hheights,hcurv,
      _hlabels,hsep,_hcover,_hroots,hgaps,hcharts⟩ :=
    double_difference_constructed_reference_system_charts F rshift sshift Y hc hJ hd hw hsmallShift
      hy hshifts hf hlower hbound hnegative hT hM hNref hR hU hUmax hphase
  let Gaps := (Refs ×ˢ Refs).filter (fun ab => ab.1 < ab.2 ∧ ∀ z∈Refs, ¬(ab.1 < z ∧ z < ab.2))
  have hgap ab (hab : ab∈Gaps) : ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ z∈Refs, ¬(ab.1 < z ∧ z < ab.2) := by
    obtain ⟨hp,hl,hadj⟩ := Finset.mem_filter.mp hab
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
    exact ⟨ha,hb,hl,hadj⟩
  have hex (ab : ℝ × ℝ) : ∃ e r v s : ℤ, ab∈Gaps →
      v*r-e*s=1 ∧ ((0 < r ∧ (e:ℝ)/r=ab.1) ∨ (r < 0 ∧ (e:ℝ)/r=ab.2)) ∧
      s≠0 ∧ (e:ℝ)/r∈Refs ∧ (v:ℝ)/s∈Refs ∧ R^2 ≤ (r:ℝ)^2*U ∧
      |(r:ℝ)| < 4*R^2/U ∧ |(s:ℝ)| < 4*R^2/U ∧
      |(e:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U) ∧
      |(v:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U) := by
    by_cases hab : ab∈Gaps
    · have hg := hgap ab hab
      obtain ⟨e,r,v,s,hout⟩ := hcharts ab.1 hg.1 ab.2 hg.2.1 hg.2.2.1 hg.2.2.2
      exact ⟨e,r,v,s,fun _ => hout⟩
    · exact ⟨0,0,0,0,fun hh => (hab hh).elim⟩
  choose e r v s hdata using hex
  refine ⟨Refs,Gaps,e,r,v,s,hsep,hgap,(fun ab hab => (hdata ab hab).1),?_,
    (fun ab hab => (hdata ab hab).2.2.1),
    (fun ab hab => (hdata ab hab).2.2.2.1),
    (fun ab hab => (hdata ab hab).2.2.2.2.1),
    (fun ab hab => (hdata ab hab).2.2.2.2.2.1),?_,
    (fun ab hab => (hdata ab hab).2.2.2.2.2.2.1.le),
    (fun ab hab => (hdata ab hab).2.2.2.2.2.2.2.1.le),
    (fun ab hab => (hdata ab hab).2.2.2.2.2.2.2.2.1),
    (fun ab hab => (hdata ab hab).2.2.2.2.2.2.2.2.2),?_⟩
  · intro ab hab
    rcases (hdata ab hab).2.1 with hleft | hright
    · exact Or.inl ⟨by exact_mod_cast hleft.1,hleft.2⟩
    · exact Or.inr ⟨by exact_mod_cast hright.1,hright.2⟩
  · intro ab hab
    have hg := hgap ab hab
    exact (hgaps ab.1 hg.1 ab.2 hg.2.1 hg.2.2.1 hg.2.2.2).2.1
  · intro y hyY z hz
    obtain ⟨l,hl,u,hu,hlo,hhi⟩ := henclose
    have hscale : 0 < curvatureScale := by dsimp only [curvatureScale]; positivity
    obtain ⟨a,ha,b,hb,hab,hax,hxb,hadj,_hal,_hub⟩ :=
      nativeHuxleyReference_finite_reference_closed_bracket Refs hl hu hlo hhi
        (show -curvatureScale < curvatureScale by linarith only [hscale])
        (abs_le.mp (hcurv y hyY z hz))
    exact ⟨(a,b),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha,hb⟩,hab,hadj⟩,hax,hxb⟩

private theorem eventually_double_difference_constructed_reference_weighted_sieve
    {csrc Usrc E σ εloss : ℝ}
    (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hE : 0 < E) (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let L := max (32*Usrc^2/csrc^2)
      (64*(modelPhaseJetCoefficient σ 3+1)*Usrc*E/κ^2)
    let θ := 1/(8*(L+3))
    ∃ C Dtype : ℝ, 0 < C ∧ 0 < Dtype ∧
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (S : Finset (ℝ × ℤ)) (Fsrc rshift sshift : ℝ → ℝ)
    (z : (ℝ × ℤ) → ℝ) (rat : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ) (Nlen : (ℝ × ℤ) → ℕ)
    (Q K₀ N : ℕ) [NeZero K₀] (R Jsep : ℝ) (Z : ℝ → ℤ)
    {d Wmax Tsrc M δ Bcut Bselect : ℝ}
    (Uref : ℕ) (anchor : (ℝ × ℤ) → ℚ),
    let lambda := csrc*Tsrc/(2*M^2)
    let Uband := Usrc*Tsrc/M^2
    let Vscale := max 1 (Uband*(N:ℝ)/(Q:ℝ))
    let Buffer := (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(σ*(σ+1)+3)+2
    (0 < d) → (0 ≤ Wmax) → (Wmax ≤ 1/4) → (2*Usrc*Wmax ≤ csrc/64) →
    (0 < Tsrc) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (Tsrc ≤ E*T) →
    (0 < Q) → (Uband ≤ 1) →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Ioo (M+Buffer) (2*M-Buffer)) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, csrc ≤ iteratedDeriv 5 Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3,
      csrc ≤ |(iteratedDeriv 5 Fsrc w)^2-iteratedDeriv 4 Fsrc w*iteratedDeriv 6 Fsrc w|) →
    (∀ i∈S, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) →
    (∀ i∈S, ((rat i).den:ℤ) ∣ (rat i).num*v i-1) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (2 ≤ M) →
    (0 < N) →
    (0 < Jsep) → (Jsep ≤ M) → ((N:ℝ) ≤ M) → (Wmax*Jsep ≤ 1) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i∈S, N ≤ Nlen i ∧ Nlen i ≤ 3*N ∧
      round (z i)+(Nlen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    (∀ y∈S.image Prod.fst,
      0 ≤ rshift y ∧ 0 ≤ sshift y ∧ rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
    let Φ := fun y u =>
      (Fsrc u-Fsrc (u+rshift y)-Fsrc (u+sshift y)+Fsrc (u+rshift y+sshift y))/d
    let Fmodel := fun (i : ℝ × ℤ) u => (Tsrc/T)*Φ i.1 u
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 4 δ) →
    let f := fun p w => Tsrc*Φ p (w/M)
    (∀ i∈S, iteratedDeriv 2 (f (i.1)) (z i)/2=(rat i:ℝ)) →
    (∀ i∈S, 1 ≤ Nlen i ∧ (rat i).den ≤ Nlen i ∧
      1 ≤ (iteratedDeriv 3 (f (i.1)) (round (z i))/6)*((rat i).den:ℝ)^2*Nlen i) →
    (∀ i∈S, 7*((iteratedDeriv 3 (f (i.1)) (round (z i))/6)*
      ((rat i).den:ℝ)*(Nlen i:ℝ)^2) ≤ K₀) →

    (1 ≤ R) → (R ≤ M) → (T*(N:ℝ)*R^2=M^3) →
    (0 < Bcut) →
    (1 ≤ Uref) →
    (2+168/κ ≤ Bselect) → (7*Bcut ≤ κ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (Q:ℝ) ≤ (N:ℝ) →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) → (Uref:ℝ) ≤ R^2 →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    2 ≤ (N:ℝ) →
    let ε := κ/(16*(Cphys+2)*R^2)
    (∀ i∈S, |(anchor i:ℝ)-(rat i:ℝ)| ≤ ε) →
    (∀ i∈S, 256*((anchor i).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ i∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor i).den) →
    let narrow := fun (i : ℝ × ℤ) =>
      (⌊((rat i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
       ⌊((rat i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    let qell := fun (i : ℝ × ℤ) => ((rat i).den:ℝ)*deriv (f (i.1)) (round (z i))
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let offset := fun ip : (ℝ × ℤ) × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : (ℝ × ℤ) × Fin 2 => (narrow ip.1,offset ip)
    let NarrowCap := (4/θ+3)*(8*Usrc/(csrc*θ)+3)
    let Cap := 3*NarrowCap

    let q := fun (i : ℝ × ℤ) => (rat i).den
    let μ := fun (i : ℝ × ℤ) => iteratedDeriv 3 (f (i.1)) (round (z i))/6
    let b := fun ip : (ℝ × ℤ) × Fin 2 => (⌊qell ip.1⌋+(ip.2:ℕ) : ℤ)
    let tau := fun ip : (ℝ × ℤ) × Fin 2 => ((b ip:ℝ)-qell ip.1)/2
    let dual := fun (i : ℝ × ℤ) => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![-(v ip.1:ℝ)*b ip/q ip.1,-(v ip.1:ℝ)/q ip.1,
        dual ip.1,3*dual ip.1*tau ip/2] : Fin 4 → ℝ)
    let Fiber := fun key => V.filter (fun ip => color ip=key)
    let μ₀ := csrc*Tsrc/(12*M^3)
    let U₀ := Usrc*Tsrc/(2*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Klarge := 60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain*((Q:ℝ)/(Uband*(N:ℝ)))^((2:ℝ)/3)+Ctail/(Uref:ℝ))
    let Y := S.image Prod.fst
    let Values := fun k : ZMod K₀ =>
      ∑ ip∈V, ‖∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x ip d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖
    let Wphys := (144*Usrc/(csrc*κ))*(R^2/(Q:ℝ))
    let WeightedValues := fun k : ZMod K₀ =>
      ∑ ip∈V, (Real.sqrt (2*(q ip.1:ℝ))/((q ip.1:ℝ)*Real.sqrt (μ ip.1*(Nlen ip.1:ℝ))))*
        ‖∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
          GafniTao.fordAdditiveCharacter (∑ d,x ip d*
            (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
              Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖
    let Mass := Vscale*Dtype*(2+θ*(Uband+1/lambda))*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
      (Y.card:ℝ)^2*Klarge*T^εloss
    ((V.image color).card:ℝ) ≤ Cap ∧
      (∀ k, (Values k)^12 ≤ C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
        ∑ key∈V.image color, ((Fiber key).card:ℝ)^10*Mass) ∧
      (V.card:ℝ) ≤ 10*(Y.card:ℝ)*(M/(N:ℝ)) ∧
      (∀ k, (Values k)^12 ≤ C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
        (10*(Y.card:ℝ)*(M/(N:ℝ)))^10*Mass) ∧
      ∀ k, ((WeightedValues k)^12 ≤ Wphys^6*
        (C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(V.card:ℝ)^10*Mass)) ∧
        (WeightedValues k)^12 ≤ Wphys^6*
          (C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(10*(Y.card:ℝ)*(M/(N:ℝ)))^10*Mass) := by
  classical
  intro κ L θ
  obtain ⟨C,Dtype,hC,hDtype,hsource⟩ :=
    eventually_double_difference_actual_family_physical_sieve hcsrc hUsrc hE hσ hεloss
  let Jref := 2*σ*Usrc*E/3
  have hJref : 0 ≤ Jref := by dsimp only [Jref]; positivity
  refine ⟨C,Dtype,hC,hDtype,?_⟩
  filter_upwards [hsource hJref] with T hfamily
  intro S Fsrc rshift sshift z rat v Nlen Q K₀ N instK R Jsep Z
    d Wmax Tsrc M δ Bcut Bselect Uref anchor
    lambda Uband Vscale Buffer hd hw hwcap hsmallShift hTsrc hT hM hδ hsourceScale hQ hUbandCap
    hy hz hreg hlower hjets htests hden hinv hnegative hMtwo hN
    hJsep hJM hNM hwJ hmesh hgeometry hseparation hshifts Φ Fmodel hmodel f hlevel hminor hcomplete
    hR hRM hscale hBcut hUref hBselectSize hcutMargin hselectedWrap hRQ
    hselectedUpper hscaleTen hQN hNsqM hUR
    Cphys c J B hsmall hNR hRN hNcube hminscale hNtwo ε hanchor hcut hcount
    narrow qell V offset color NarrowCap Cap q μ b tau dual x Fiber μ₀ U₀ Δtype
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird Cpack Cfirst Cgap Cmain Ctail Klarge Y Values Wphys WeightedValues Mass
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hUp : (0:ℝ) < Uref := by exact_mod_cast (show 0 < Uref by omega)
  have hdenom : 0 < σ*(σ+1)+3 := by positivity
  have hBuffer : 0 ≤ Buffer := by dsimp only [Buffer]; positivity
  have hzFull i (hi : i∈S) : z i∈Icc M (2*M) := by
    have hh := hz i hi
    constructor <;> linarith only [hh.1,hh.2,hBuffer]
  have hY y (hyY : y∈Y) : y∈Icc (1:ℝ) 2 := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hyY
    exact hy i hi
  obtain ⟨Refs,Gaps,e,r,vRef,s,hsep0,hgap,hchart,horientation,hs,hrefSet,hparentSet,
      hreferenceDen,hgapWidth,hrHeight,hsHeight,heHeight0,hvHeight0,hcover⟩ :=
    double_difference_constructed_reference_gap_factory Fsrc rshift sshift Y
      hcsrc hUsrc hd hwcap hsmallShift hY hshifts hreg hlower hjets hnegative
      hTsrc hM hRp hUp hUR
  have hex (i : ℝ × ℤ) : ∃ ab : ℝ × ℝ, i∈S → ab∈Gaps ∧ (rat i:ℝ)∈Icc ab.1 ab.2 := by
    by_cases hi : i∈S
    · obtain ⟨ab,hab,hval⟩ := hcover i.1 (Finset.mem_image_of_mem Prod.fst hi) (z i) (hzFull i hi)
      change iteratedDeriv 2 (f i.1) (z i)/2∈Icc ab.1 ab.2 at hval
      rw [hlevel i hi] at hval
      exact ⟨ab,fun _ => ⟨hab,hval⟩⟩
    · exact ⟨(0,0),fun hh => (hi hh).elim⟩
  choose gap hgapData using hex
  have hsep a (ha : a∈Refs) b (hb : b∈Refs) (hab : a≠b) :
      ((Uref:ℝ)/R^2)/4 < |a-b| := by
    convert hsep0 a ha b hb hab using 1
    ring
  have hcurvScale : Usrc*Tsrc/M^2 ≤ 3*Jref*T/(2*σ*M^2) := by
    calc
      _ ≤ Usrc*(E*T)/M^2 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsourceScale hUsrc.le) (sq_nonneg M)
      _ = _ := by dsimp only [Jref]; field_simp
  have hheight : (Usrc*Tsrc/M^2+1)*(4*R^2/(Uref:ℝ)) ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ)) :=
    mul_le_mul_of_nonneg_right (add_le_add hcurvScale le_rfl) (by positivity)
  have heHeight ab (hab : ab∈Gaps) :
      |(e ab:ℝ)| ≤ (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ)) :=
    (heHeight0 ab hab).trans hheight
  have hvHeight ab (hab : ab∈Gaps) :
      |(vRef ab:ℝ)| ≤ (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ)) :=
    (hvHeight0 ab hab).trans hheight
  let A := fun _ : ℝ => ⌈M⌉
  let W := fun _ : ℝ => 2*M-(⌈M⌉:ℝ)
  let Dpad := (56*(Uref:ℝ)/κ)*(N:ℝ)
  let Hphys := (N:ℝ)/(σ*(σ+1)+3)
  have hDpad : 0 ≤ Dpad := by dsimp only [Dpad]; positivity
  have hHphys : 0 ≤ Hphys := by dsimp only [Hphys]; positivity
  have hHeq : (N:ℝ)/(Cphys+2)=Hphys := by dsimp only [Cphys,Hphys]; ring
  have hBufferEq : Buffer=Dpad+Hphys+2 := rfl
  have hwindow i (hi : i∈S) t (ht : |t| ≤ Dpad+Hphys) :
      z i-(A i.1:ℝ)+t∈Ioo (1/2:ℝ) (W i.1-1/2) := by
    have hzz := hz i hi
    rw [hBufferEq] at hzz
    have hceil := Int.ceil_lt_add_one M
    have htb := abs_le.mp ht
    change (1/2:ℝ) < z i-(⌈M⌉:ℝ)+t ∧ z i-(⌈M⌉:ℝ)+t < 2*M-(⌈M⌉:ℝ)-1/2
    constructor <;> linarith only [hzz.1,hzz.2,hceil,htb.1,htb.2]
  have hx i (hi : i∈S) : z i-(A i.1:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2) := by
    simpa only [add_zero] using hwindow i hi 0 (by rw [abs_zero]; positivity)
  have hwideL i (hi : i∈S) : z i-(A i.1:ℝ)-Dpad∈Ioo (1/2:ℝ) (W i.1-1/2) := by
    simpa only [sub_eq_add_neg] using hwindow i hi (-Dpad)
      (by rw [abs_neg,abs_of_nonneg hDpad]; linarith only [hHphys])
  have hwideU i (hi : i∈S) : z i-(A i.1:ℝ)+Dpad∈Ioo (1/2:ℝ) (W i.1-1/2) :=
    hwindow i hi Dpad (by rw [abs_of_nonneg hDpad]; linarith only [hHphys])
  have hLeft i (hi : i∈S) : z i-(A i.1:ℝ)-(N:ℝ)/(Cphys+2)∈Ioo (1/2:ℝ) (W i.1-1/2) := by
    rw [hHeq]
    simpa only [sub_eq_add_neg] using hwindow i hi (-Hphys)
      (by rw [abs_neg,abs_of_nonneg hHphys]; linarith only [hDpad])
  have hRight i (hi : i∈S) : z i-(A i.1:ℝ)+(N:ℝ)/(Cphys+2)∈Ioo (1/2:ℝ) (W i.1-1/2) := by
    rw [hHeq]
    exact hwindow i hi Hphys (by rw [abs_of_nonneg hHphys]; linarith only [hDpad])
  exact hfamily S Fsrc rshift sshift z rat v Nlen Q K₀ N R Jsep Z
    (d:=d) (Wmax:=Wmax) (Tsrc:=Tsrc) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
    Uref Refs Gaps A W gap anchor e r vRef s
    hd hw hwcap hsmallShift hTsrc hT hM hδ hsourceScale hQ hUbandCap
    hy hzFull hreg hlower hjets htests hden hinv hnegative hMtwo hN
    hJsep hJM hNM hwJ hmesh hgeometry hseparation hshifts hmodel hlevel hminor hcomplete
    hR hRM hscale (fun _ _ => Int.le_ceil M)
    (fun _ _ => by dsimp only [A,W]; linarith) hx (fun i hi => (hgapData i hi).1)
    hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
    hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
    hselectedUpper hscaleTen (fun i hi => (hgapData i hi).2) hgap hQN hNsqM hUR
    hrHeight hsHeight heHeight hvHeight hsmall hNR hRN hNcube hminscale
    hNtwo hLeft hRight hanchor hcut hcount hsize hD hΔ hBsize

private theorem eventually_double_difference_original_selected_block_moment
    {csrc Usrc σ εloss : ℝ}
    (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let L := max (32*Usrc^2/csrc^2)
      (64*(modelPhaseJetCoefficient σ 3+1)*Usrc/κ^2)
    let θ := 1/(8*(L+3))
    ∃ CF C Dtype : ℝ, 1 ≤ CF ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (S : Finset (ℝ × ℤ)) (Fsrc rshift sshift : ℝ → ℝ)
    (H : (ℝ × ℤ) → ℕ) (za : (ℝ × ℤ) → ℝ)
    (Q K₀ N : ℕ) [NeZero K₀] (R Jsep : ℝ) (Z : ℝ → ℤ)
    {d Wmax M δ Bcut Bselect : ℝ}
    (Uref : ℕ) (anchor : (ℝ × ℤ) → ℚ),
    let lambda := csrc*T/(2*M^2)
    let Uband := Usrc*T/M^2
    let Vscale := max 1 (Uband*(N:ℝ)/(Q:ℝ))
    let Lsrc := fun i : ℝ × ℤ => Z i.1+(N:ℤ)*i.2+2*(N:ℤ)
    let Buffer := (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(σ*(σ+1)+3)+2
    (0 < d) → (0 ≤ Wmax) → (Wmax ≤ 1/4) → (2*Usrc*Wmax ≤ csrc/64) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (0 < Q) → (Uband ≤ 1) →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, (Lsrc i:ℝ)-2*(N:ℝ)∈Ioo (M+Buffer+(N:ℝ)) (2*M-Buffer-(N:ℝ))) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, csrc ≤ iteratedDeriv 5 Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3,
      csrc ≤ |(iteratedDeriv 5 Fsrc w)^2-iteratedDeriv 4 Fsrc w*iteratedDeriv 6 Fsrc w|) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (2 ≤ M) →
    (0 < N) →
    (0 < Jsep) → (Jsep ≤ M) → ((N:ℝ) ≤ M) → (Wmax*Jsep ≤ 1) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i∈S, H i ≤ N) →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/4)*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    63*(Usrc/(2*(N:ℝ)*R^2))*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
    (∀ i∈S, 2*(anchor i).den ≤ Q) →
    (∀ i∈S, 128*R^2 ≤ csrc*(Q:ℝ)*(anchor i).den) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    (∀ y∈S.image Prod.fst,
      0 ≤ rshift y ∧ 0 ≤ sshift y ∧ rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
    let Φ := fun y u =>
      (Fsrc u-Fsrc (u+rshift y)-Fsrc (u+sshift y)+Fsrc (u+rshift y+sshift y))/d
    let Fmodel := fun (i : ℝ × ℤ) u => Φ i.1 u
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 4 δ) →
    let f := fun p w => T*Φ p (w/M)
    (∀ i∈S, za i∈Ioo ((Lsrc i:ℝ)-2*(N:ℝ)-(N:ℝ)/8)
      ((Lsrc i:ℝ)-2*(N:ℝ)+(N:ℝ)/8) ∧
      iteratedDeriv 2 (f i.1) (za i)/2=(anchor i:ℝ)) →

    (1 ≤ R) → (R ≤ M) → (T*(N:ℝ)*R^2=M^3) →
    (0 < Bcut) →
    (1 ≤ Uref) →
    (2+168/κ ≤ Bselect) → (7*Bcut ≤ κ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (Q:ℝ) ≤ (N:ℝ) →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) → (Uref:ℝ) ≤ R^2 →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    2 ≤ (N:ℝ) →
    let ε := κ/(16*(Cphys+2)*R^2)
    csrc ≤ 4*κ/(Cphys+2) →
    (∀ i∈S, 256*((anchor i).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ i∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor i).den) →
    let NarrowCap := (4/θ+3)*(8*Usrc/(csrc*θ)+3)
    let Cap := 3*NarrowCap
    let μ₀ := csrc*T/(12*M^3)
    let U₀ := Usrc*T/(2*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Klarge := 60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain*((Q:ℝ)/(Uband*(N:ℝ)))^((2:ℝ)/3)+Ctail/(Uref:ℝ))
    let Y := S.image Prod.fst
    let Wphys := (144*Usrc/(csrc*κ))*(R^2/(Q:ℝ))
    let Mass := Vscale*Dtype*(2+θ*(Uband+1/lambda))*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
      (Y.card:ℝ)^2*Klarge*T^εloss
    let Error := (S.card:ℝ)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+36*Usrc*R^2/(csrc*κ*(N:ℝ)))
    (∑ i∈S, ‖∑ n∈Finset.Ioc (Lsrc i) (Lsrc i+H i),(𝐞 (f i.1 n):ℂ)‖)^12 ≤
      CF^12*2^11*((1+Real.log K₀)^12*Wphys^6*
        (C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(S.card:ℝ))^10*Mass)+Error^12) := by
  classical
  intro κ L θ
  obtain ⟨CF,hCF,hentry⟩ := double_difference_dyadic_anchor_source_fourier hcsrc hUsrc
  have hsource₀ := eventually_double_difference_constructed_reference_weighted_sieve
    hcsrc hUsrc (by norm_num : (0:ℝ) < 1) hσ hεloss
  simp only [mul_one] at hsource₀
  obtain ⟨C,Dtype,hC,hDtype,hsource⟩ := hsource₀
  refine ⟨CF,C,Dtype,hCF,hC,hDtype,?_⟩
  filter_upwards [hsource] with T hfamily
  intro S Fsrc rshift sshift H za Q K₀ N instK R Jsep Z
    d Wmax M δ Bcut Bselect Uref anchor
    lambda Uband Vscale Lsrc Buffer hd hw hwcap hsmallShift hT hM hδ hQ hUbandCap
    hy hbuffer hreg hlower hjets htests hnegative hMtwo hN
    hJsep hJM hNM hwJ hmesh hH hfourBuffer hfourBudget hquadBudget hfullmesh hsmallDen hmajor
    hseparation hshifts Φ Fmodel hmodel f hanchors
    hR hRM hscale hBcut hUref hBselectSize hcutMargin hselectedWrap hRQ
    hselectedUpper hscaleTen hQN hNsqM hUR
    Cphys c J B hsmall hNR hRN hNcube hminscale hNtwo ε hanchorBudget hcut hcount
    NarrowCap Cap μ₀ U₀ Δtype C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase
    hsize hD hΔ hBsize Lunit Gamma Cthird Cpack Cfirst Cgap Cmain Ctail Klarge Y Wphys Mass Error
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hBuffer : 0 ≤ Buffer := by dsimp only [Buffer]; positivity
  have hbase i (hi : i∈S) : (Lsrc i:ℝ)-2*(N:ℝ)∈Icc M (2*M) := by
    have hb := hbuffer i hi
    exact ⟨by linarith only [hb.1,hBuffer,hNp],
      by linarith only [hb.2,hBuffer,hNp]⟩
  have hshift i (hi : i∈S) :=
    hshifts i.1 (Finset.mem_image_of_mem Prod.fst hi)
  obtain ⟨rat,z,hrat,hgeo,hminor,hfour⟩ :=
    hentry (ℝ × ℤ) S Fsrc Prod.fst (fun i => rshift i.1) (fun i => sshift i.1)
      Lsrc H anchor za N Q d Wmax T M R
      (by omega) hH hd hwcap hsmallShift hT hM hRp hy hshift hbase
      hreg hjets hlower hscale hfourBuffer hfourBudget hquadBudget
      (by exact_mod_cast hQN) hsmallDen hmajor hanchors
  let Nlen := fun i : ℝ × ℤ => (Lsrc i-round (z i)).toNat
  let q := fun i : ℝ × ℤ => (rat i).den
  let μ := fun i : ℝ × ℤ => iteratedDeriv 3 (f i.1) (round (z i))/6
  obtain ⟨hcomplete,v,hinv,k,hfourier⟩ := hfour K₀ hfullmesh
  have hz i (hi : i∈S) : z i∈Ioo (M+Buffer) (2*M-Buffer) := by
    have hb := hbuffer i hi
    have ha := (hanchors i hi).1
    have hh := (hrat i hi).2.2.2.2.1
    exact ⟨by linarith only [hb.1,ha.1,hh.1,hNp],
      by linarith only [hb.2,ha.2,hh.2,hNp]⟩
  have hzFull i (hi : i∈S) : z i∈Icc M (2*M) := by
    have hh := hz i hi
    exact ⟨by linarith only [hh.1,hBuffer],by linarith only [hh.2,hBuffer]⟩
  have hden i (hi : i∈S) : (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den :=
    ⟨(hrat i hi).1,(hrat i hi).2.1⟩
  have hlevel i (hi : i∈S) : iteratedDeriv 2 (f i.1) (z i)/2=(rat i:ℝ) :=
    (hrat i hi).2.2.2.2.2
  have hgeometry i (hi : i∈S) : N ≤ Nlen i ∧ Nlen i ≤ 3*N ∧
      round (z i)+(Nlen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ) :=
    (hgeo i hi).2
  have htol : csrc/(64*R^2) ≤ ε := by
    calc
      _ ≤ (4*κ/(Cphys+2))/(64*R^2) :=
        div_le_div_of_nonneg_right hanchorBudget (by positivity)
      _ = ε := by dsimp only [ε]; field_simp; ring
  have hanchor i (hi : i∈S) : |(anchor i:ℝ)-(rat i:ℝ)| ≤ ε := by
    rw [abs_sub_comm]
    exact ((hrat i hi).2.2.2.1).trans htol
  have hmodel' i (hi : i∈S) : Expdb.IsApproximateModelPhaseFunction
      (fun u => (T/T)*Φ i.1 u) σ 4 δ := by
    simpa only [div_self hT.ne',one_mul] using hmodel i hi
  have hsieve := hfamily S Fsrc rshift sshift z rat v Nlen Q K₀ N R Jsep Z
    (d:=d) (Wmax:=Wmax) (Tsrc:=T) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
    Uref anchor hd hw hwcap hsmallShift hT hT hM hδ (by simp) hQ hUbandCap
    hy hz hreg hlower hjets htests hden hinv hnegative hMtwo hN
    hJsep hJM hNM hwJ hmesh hgeometry hseparation hshifts hmodel' hlevel hminor hcomplete
    hR hRM hscale hBcut hUref hBselectSize hcutMargin hselectedWrap hRQ
    hselectedUpper hscaleTen hQN hNsqM hUR hsmall hNR hRN hNcube hminscale
    hNtwo hanchor hcut hcount hsize hD hΔ hBsize
  let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*deriv (f i.1) (round (z i))⌋+(p:ℕ) : ℤ)
  let tau := fun i p => ((b i p:ℝ)-(q i:ℝ)*deriv (f i.1) (round (z i)))/2
  let dual := fun i => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
  let x := fun i p =>
    (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,dual i,3*dual i*tau i p/2] : Fin 4 → ℝ)
  let val := fun i p =>
    ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
      GafniTao.fordAdditiveCharacter (∑ d,x i p d*
        (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
          Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖
  let weight := fun i => Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*(Nlen i:ℝ)))
  let Wsum := ∑ i∈S, ∑ p : Fin 2,weight i*val i p
  let FamilyBound := Wphys^6*
    (C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(S.card:ℝ))^10*Mass)
  have hW12 : Wsum^12 ≤ FamilyBound := by
    have hh := (hsieve.2.2.2.2 k).1
    simpa only [Finset.sum_product,Finset.card_product,Finset.card_univ,Fintype.card_fin,
      Nat.cast_mul,Nat.cast_ofNat,mul_comm (S.card:ℝ) 2] using hh
  have hW0 : 0 ≤ Wsum := by
    apply Finset.sum_nonneg
    intro i _
    exact Finset.sum_nonneg (fun p _ =>
      mul_nonneg (div_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))) (norm_nonneg _))
  let PointError := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+
    36*Usrc*R^2/(csrc*κ*(N:ℝ))
  have hPointError : 0 ≤ PointError := by
    dsimp only [PointError]
    exact add_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (Real.log_nonneg (by linarith only [hNtwo]))) (by positivity)
  have hpoint i (hi : i∈S) :
      Real.sqrt (Nlen i)*Real.log (2*(Nlen i:ℝ))+1/(μ i*(Nlen i:ℝ)^2) ≤ PointError := by
    have hh := double_difference_source_completion_weight Fsrc (q:=(q i:ℝ)) (A:=(Nlen i:ℝ))
      (hshift i hi).1 (hshift i hi).2.1 hd (hy i hi)
      (hshift i hi).2.2.1 (hshift i hi).2.2.2 hwcap hsmallShift
      hcsrc hUsrc hσ hT hT hMtwo hNp hRp (Nat.cast_pos.mpr hQ)
      (by exact_mod_cast (hden i hi).2)
      (by exact_mod_cast (hgeometry i hi).1)
      (hzFull i hi) hscale hδ hreg hlower hjets
      (approximateModelPhase_mono (hmodel' i hi) (by norm_num : 2 ≤ 4) le_rfl)
    have hlo : csrc/(12*(3*Usrc/κ)*(N:ℝ)*R^2) ≤ μ i := by
      calc
        _ = csrc*κ/(36*Usrc*(N:ℝ)*R^2) := by field_simp; ring
        _ ≤ μ i := hh.2.1
    have herr := cubic_completion_point_error (σ:=3*Usrc/κ) (A:=(Nlen i:ℝ)) (by positivity)
      hcsrc (by linarith only [hNtwo] : (1:ℝ) ≤ N) hRp
      (by exact_mod_cast (hgeometry i hi).1)
      (by exact_mod_cast (hgeometry i hi).2.1) hlo
    convert herr using 1
    dsimp only [PointError]
    congr 1
    ring
  have herror : (∑ i∈S, (Real.sqrt (Nlen i)*Real.log (2*(Nlen i:ℝ))+
      1/(μ i*(Nlen i:ℝ)^2))) ≤ Error := by
    calc
      _ ≤ ∑ _i∈S,PointError := Finset.sum_le_sum hpoint
      _ = Error := by rw [Finset.sum_const,nsmul_eq_mul]
  have hError : 0 ≤ Error := mul_nonneg (Nat.cast_nonneg _) hPointError
  have hlog : 0 ≤ 1+Real.log K₀ := by
    have hkpos : 0 < K₀ := NeZero.pos K₀
    have hkone : (1:ℝ) ≤ K₀ := by exact_mod_cast (show 1 ≤ K₀ by omega)
    linarith only [Real.log_nonneg hkone]
  let Total := ∑ i∈S, ‖∑ n∈Finset.Ioc (Lsrc i) (Lsrc i+H i),(𝐞 (f i.1 n):ℂ)‖
  have hTotal : 0 ≤ Total := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hfourier' : Total ≤ CF*((1+Real.log K₀)*Wsum+Error) := by
    exact hfourier.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl herror)
      (zero_le_one.trans hCF))
  have hpow := pow_le_pow_left₀ hTotal hfourier' 12
  rw [mul_pow] at hpow
  have hsplit := add_pow_le (mul_nonneg hlog hW0) hError 12
  rw [mul_pow] at hsplit
  calc
    Total^12 ≤ CF^12*((1+Real.log K₀)*Wsum+Error)^12 := hpow
    _ ≤ CF^12*(2^11*((1+Real.log K₀)^12*Wsum^12+Error^12)) :=
      mul_le_mul_of_nonneg_left hsplit (pow_nonneg (zero_le_one.trans hCF) _)
    _ ≤ CF^12*(2^11*((1+Real.log K₀)^12*FamilyBound+Error^12)) := by
      gcongr
    _ = _ := by
      dsimp only [FamilyBound]
      simp only [mul_assoc]

private theorem double_difference_uniform_source_normalization
    (F : ℝ → ℝ) {c U lo hi : ℝ}
    (hc : 0 < c) (hU : 0 < U) (hlo : 0 < lo) (hhi : 0 < hi)
    (hreg : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hjets : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 →
      |iteratedDeriv n F u| ≤ U)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hdet : ∀ u∈Icc (1/2:ℝ) 3,
      c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|)
    (hnegative : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c) :
    let cnew := c*min lo (lo^2)
    let Unew := hi*U
    0 < cnew ∧ 0 < Unew ∧
    ∀ ampl : ℝ, lo ≤ ampl → ampl ≤ hi →
    let Fscaled := fun u => ampl*F u
    (∀ u, 0 < u → ContDiffAt ℝ ∞ Fscaled u) ∧
    (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 →
      |iteratedDeriv n Fscaled u| ≤ Unew) ∧
    (∀ u∈Icc (1/2:ℝ) 3, cnew ≤ iteratedDeriv 5 Fscaled u) ∧
    (∀ u∈Icc (1/2:ℝ) 3,
      cnew ≤ |(iteratedDeriv 5 Fscaled u)^2-
        iteratedDeriv 4 Fscaled u*iteratedDeriv 6 Fscaled u|) ∧
    (∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fscaled u ≤ -cnew) ∧
    ∀ Traw Tmodel d r s M v : ℝ, Tmodel*ampl=Traw →
      Tmodel*(Fscaled (v/M)-Fscaled (v/M+r)-Fscaled (v/M+s)+Fscaled (v/M+r+s))/d=
        Traw*(F (v/M)-F (v/M+r)-F (v/M+s)+F (v/M+r+s))/d := by
  intro cnew Unew
  refine ⟨mul_pos hc (lt_min hlo (pow_pos hlo 2)),mul_pos hhi hU,?_⟩
  intro ampl hampl hamplhi Fscaled
  have hamplpos := hlo.trans_le hampl
  have hderiv n u : iteratedDeriv n Fscaled u=ampl*iteratedDeriv n F u :=
    iteratedDeriv_const_mul_field ampl F
  have hlc : cnew ≤ ampl*c := by
    calc
      cnew ≤ c*lo := mul_le_mul_of_nonneg_left (min_le_left _ _) hc.le
      _ ≤ c*ampl := mul_le_mul_of_nonneg_left hampl hc.le
      _ = ampl*c := mul_comm _ _
  have hlc2 : cnew ≤ ampl^2*c := by
    calc
      cnew ≤ c*lo^2 := mul_le_mul_of_nonneg_left (min_le_right _ _) hc.le
      _ ≤ c*ampl^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlo.le hampl 2) hc.le
      _ = ampl^2*c := mul_comm _ _
  refine ⟨fun u hu => contDiffAt_const.mul (hreg u hu),?_,?_,?_,?_,?_⟩
  · intro u hu n hn hn'
    rw [hderiv,abs_mul,abs_of_pos hamplpos]
    exact mul_le_mul hamplhi (hjets u hu n hn hn') (abs_nonneg _) hhi.le
  · intro u hu
    rw [hderiv]
    exact hlc.trans (mul_le_mul_of_nonneg_left (hlower u hu) hamplpos.le)
  · intro u hu
    rw [hderiv,hderiv,hderiv]
    have he : (ampl*iteratedDeriv 5 F u)^2-
        (ampl*iteratedDeriv 4 F u)*(ampl*iteratedDeriv 6 F u)=
        ampl^2*((iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u) := by ring
    rw [he,abs_mul,abs_of_nonneg (sq_nonneg ampl)]
    exact hlc2.trans (mul_le_mul_of_nonneg_left (hdet u hu) (sq_nonneg ampl))
  · intro u hu
    rw [hderiv]
    have hh := mul_le_mul_of_nonneg_left (hnegative u hu) hamplpos.le
    linarith only [hh,hlc]
  · intro Traw Tmodel d r s M v hT
    change Tmodel*(ampl*F (v/M)-ampl*F (v/M+r)-ampl*F (v/M+s)+ampl*F (v/M+r+s))/d=_
    calc
      _ = (Tmodel*ampl)*(F (v/M)-F (v/M+r)-F (v/M+s)+F (v/M+r+s))/d := by ring
      _ = _ := by rw [hT]

private theorem double_difference_colored_common_scale_source
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ e : ℝ, 0 < e ∧
      ∀ {c U : ℝ}, 0 < c → 0 < U →
    ∃ w₀ a cnew Unew : ℝ,
      0 < w₀ ∧ w₀ ≤ 1/4 ∧ 0 < a ∧ 0 < cnew ∧ 0 < Unew ∧
      2*Unew*w₀ ≤ cnew/64 ∧
      cnew ≤ 4*modelPhaseThirdLower (σ+2)/((σ+2)*(σ+3)+3) ∧
      ∀ (F : ℝ → ℝ),
        (∀ u, 0 < u → ContDiffAt ℝ ∞ F u) →
        (∀ u∈Icc (1/2:ℝ) 3, ∀ p≤6,
          |iteratedDeriv (p+1) F u-iteratedDeriv p (Expdb.modelPhase σ) u| ≤ e) →
        (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
        (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
        (∀ u∈Icc (1/2:ℝ) 3,
          c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
        (∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c) →
        ∀ {ι : Type*} (S : Finset ι) (y r s : ι → ℝ) (d : ℝ),
          0 < d →
          (∀ i∈S, y i∈Icc (1:ℝ) 2) →
          (∀ i∈S, 0 < r i ∧ 0 < s i ∧ r i+s i ≤ w₀ ∧ r i*s i=d*y i) →
          let color := fun i => ⌊y i/a⌋
          let Cap := 4/a+3
          ((S.image color).card:ℝ) ≤ Cap ∧
          (∀ z : ι → ℂ, ‖∑ i∈S,z i‖^12 ≤
            Cap^11*∑ j∈S.image color, ‖∑ i∈S.filter (fun i => color i=j),z i‖^12) ∧
          ∀ j∈S.image color, ∃ i₀∈S, color i₀=j ∧
            let ampl := 1/(σ*(σ+1)*y i₀)
            let Fsrc := fun u => ampl*F u
            (∀ u, 0 < u → ContDiffAt ℝ ∞ Fsrc u) ∧
            (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 →
              |iteratedDeriv n Fsrc u| ≤ Unew) ∧
            (∀ u∈Icc (1/2:ℝ) 3, cnew ≤ iteratedDeriv 5 Fsrc u) ∧
            (∀ u∈Icc (1/2:ℝ) 3,
              cnew ≤ |(iteratedDeriv 5 Fsrc u)^2-
                iteratedDeriv 4 Fsrc u*iteratedDeriv 6 Fsrc u|) ∧
            (∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc u ≤ -cnew) ∧
            ∀ T N R M : ℝ, 0 < T → 0 < R → T*N*R^2=M^3 →
              let Tnew := T*σ*(σ+1)*y i₀
              let Rnew := R*Real.sqrt ampl
              0 < Tnew ∧ 0 < Rnew ∧
                Rnew^2=R^2*ampl ∧ Tnew*N*Rnew^2=M^3 ∧
              ∀ i∈S, color i=j →
                let G := fun u =>
                  (Fsrc u-Fsrc (u+r i)-Fsrc (u+s i)+Fsrc (u+r i+s i))/d
                Expdb.IsApproximateModelPhaseFunction G (σ+2) 4 ε ∧
                  ∀ v : ℝ, Tnew*G (v/M)=
                    T*(F (v/M)-F (v/M+r i)-F (v/M+s i)+F (v/M+r i+s i))/d := by
  classical
  obtain ⟨e,w,a,he,hw,hwcap,ha,hmodels⟩ := double_difference_colored_common_models hσ 4 hε
  refine ⟨e,he,?_⟩
  intro c U hc hU
  let lo := 1/(2*σ*(σ+1))
  let hi := 1/(σ*(σ+1))
  let cpre := c*min lo (lo^2)
  let Unew := hi*U
  let cnew := min cpre (4*modelPhaseThirdLower (σ+2)/((σ+2)*(σ+3)+3))
  let w₀ := min w (cnew/(128*Unew))
  have hlo : 0 < lo := by dsimp only [lo]; positivity
  have hhi : 0 < hi := by dsimp only [hi]; positivity
  have hcpre : 0 < cpre := mul_pos hc (lt_min hlo (pow_pos hlo 2))
  have hUnew : 0 < Unew := mul_pos hhi hU
  have hcnew : 0 < cnew := lt_min hcpre (div_pos
    (mul_pos (by norm_num) (modelPhaseThirdLower_pos (by positivity))) (by positivity))
  have hw₀ : 0 < w₀ := lt_min hw (div_pos hcnew (by positivity))
  have hsmall : 2*Unew*w₀ ≤ cnew/64 := by
    calc
      _ ≤ 2*Unew*(cnew/(128*Unew)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = cnew/64 := by field_simp; ring
  refine ⟨w₀,a,cnew,Unew,hw₀,(min_le_left _ _).trans hwcap,ha,hcnew,hUnew,
    hsmall,min_le_right _ _,?_⟩
  intro F hreg happrox hjets hlower hdet hnegative ι S y r s d hd hy hshifts color Cap
  have hshiftsOld i (hiS : i∈S) : 0 < r i ∧ 0 < s i ∧ r i+s i ≤ w ∧ r i*s i=d*y i :=
    ⟨(hshifts i hiS).1,(hshifts i hiS).2.1,
      (hshifts i hiS).2.2.1.trans (min_le_left _ _),(hshifts i hiS).2.2.2⟩
  obtain ⟨hcard,hmoment,hcolored⟩ := hmodels F hreg happrox S y r s d hd hy hshiftsOld
  refine ⟨hcard,hmoment,?_⟩
  intro j hj
  obtain ⟨i₀,hi₀,hcolor₀,hmodel⟩ := hcolored j hj
  refine ⟨i₀,hi₀,hcolor₀,?_⟩
  intro ampl Fsrc
  have hy₀ := hy i₀ hi₀
  have hypos : 0 < y i₀ := zero_lt_one.trans_le hy₀.1
  have hσ₁ : 0 < σ+1 := by positivity
  have hamp : 0 < ampl := by dsimp only [ampl]; positivity
  have hampLow : lo ≤ ampl := by
    apply one_div_le_one_div_of_le (by positivity : 0 < σ*(σ+1)*y i₀)
    nlinarith only [mul_le_mul_of_nonneg_left hy₀.2 (mul_pos hσ hσ₁).le]
  have hampHigh : ampl ≤ hi := by
    apply one_div_le_one_div_of_le (mul_pos hσ hσ₁)
    nlinarith only [mul_le_mul_of_nonneg_left hy₀.1 (mul_pos hσ hσ₁).le]
  obtain ⟨hsrcReg,hsrcJets,hsrcLower,hsrcDet,hsrcNegative,hphase⟩ :=
    (double_difference_uniform_source_normalization F hc hU hlo hhi
      hreg hjets hlower hdet hnegative).2.2 ampl hampLow hampHigh
  have hcc : cnew ≤ cpre := min_le_left _ _
  refine ⟨hsrcReg,hsrcJets,(fun u hu => hcc.trans (hsrcLower u hu)),
    (fun u hu => hcc.trans (hsrcDet u hu)),
    (fun u hu => (hsrcNegative u hu).trans (neg_le_neg hcc)),?_⟩
  intro T N R M hT hR hscale Tnew Rnew
  have hTnew : 0 < Tnew := by dsimp only [Tnew]; positivity
  have hRnew : 0 < Rnew := mul_pos hR (Real.sqrt_pos.mpr hamp)
  have hRsq : Rnew^2=R^2*ampl := by
    dsimp only [Rnew]
    rw [mul_pow,Real.sq_sqrt hamp.le]
  have hTamp : Tnew*ampl=T := by
    dsimp only [Tnew,ampl]
    field_simp
  have hscaleNew : Tnew*N*Rnew^2=M^3 := by
    calc
      _ = (Tnew*ampl)*N*R^2 := by rw [hRsq]; ring
      _ = M^3 := by rw [hTamp,hscale]
  refine ⟨hTnew,hRnew,hRsq,hscaleNew,?_⟩
  intro i hiS hcolor G
  let Graw := fun u => (F u-F (u+r i)-F (u+s i)+F (u+r i+s i))/(σ*(σ+1)*d*y i₀)
  have hGeq : G=Graw := by
    funext u
    dsimp only [G,Graw,Fsrc,ampl]
    field_simp
  refine ⟨?_,?_⟩
  · rw [hGeq]
    exact (hmodel i hiS hcolor).1
  · intro v
    change Tnew*((Fsrc (v/M)-Fsrc (v/M+r i)-Fsrc (v/M+s i)+Fsrc (v/M+r i+s i))/d)=_
    rw [←mul_div_assoc]
    exact hphase T Tnew d (r i) (s i) M v hTamp

private theorem approximateModelPhase_enlarged_double_common_scale_source
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ w₀ a c U : ℝ,
      0 < δ ∧ 0 < w₀ ∧ w₀ ≤ 1/4 ∧ 0 < a ∧ 0 < c ∧ 0 < U ∧
      2*U*w₀ ≤ c/64 ∧
      c ≤ 4*modelPhaseThirdLower (σ+2)/((σ+2)*(σ+3)+3) ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1 ≤ M →
        Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
      ∃ Fext : ℝ → ℝ,
        (∀ u, 0 < u → ContDiffAt ℝ ∞ Fext u) ∧
        (∀ (T : ℝ) (m n : ℕ), M ≤ (m:ℝ) → (n:ℝ) ≤ 2*M →
          ‖Expdb.exponentialSumAt F T M m n-Expdb.exponentialSumAt Fext T M m n‖ ≤ 6) ∧
        ∀ {ι : Type*} (S : Finset ι) (y r s : ι → ℝ) (d : ℝ),
          0 < d →
          (∀ i∈S, y i∈Icc (1:ℝ) 2) →
          (∀ i∈S, 0 < r i ∧ 0 < s i ∧ r i+s i ≤ w₀ ∧ r i*s i=d*y i) →
          let color := fun i => ⌊y i/a⌋
          let Cap := 4/a+3
          ((S.image color).card:ℝ) ≤ Cap ∧
          (∀ z : ι → ℂ, ‖∑ i∈S,z i‖^12 ≤
            Cap^11*∑ j∈S.image color, ‖∑ i∈S.filter (fun i => color i=j),z i‖^12) ∧
          ∀ j∈S.image color, ∃ i₀∈S, color i₀=j ∧
            let ampl := 1/(σ*(σ+1)*y i₀)
            let Fsrc := fun u => ampl*Fext u
            (∀ u, 0 < u → ContDiffAt ℝ ∞ Fsrc u) ∧
            (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 →
              |iteratedDeriv n Fsrc u| ≤ U) ∧
            (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 Fsrc u) ∧
            (∀ u∈Icc (1/2:ℝ) 3,
              c ≤ |(iteratedDeriv 5 Fsrc u)^2-
                iteratedDeriv 4 Fsrc u*iteratedDeriv 6 Fsrc u|) ∧
            (∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc u ≤ -c) ∧
            ∀ T N R M : ℝ, 0 < T → 0 < R → T*N*R^2=M^3 →
              let Tnew := T*σ*(σ+1)*y i₀
              let Rnew := R*Real.sqrt ampl
              0 < Tnew ∧ 0 < Rnew ∧
                Rnew^2=R^2*ampl ∧ Tnew*N*Rnew^2=M^3 ∧
              ∀ i∈S, color i=j →
                let G := fun u =>
                  (Fsrc u-Fsrc (u+r i)-Fsrc (u+s i)+Fsrc (u+r i+s i))/d
                Expdb.IsApproximateModelPhaseFunction G (σ+2) 4 ε ∧
                  ∀ v : ℝ, Tnew*G (v/M)=
                    T*(Fext (v/M)-Fext (v/M+r i)-Fext (v/M+s i)+Fext (v/M+r i+s i))/d := by
  obtain ⟨e,he,hcommon⟩ := double_difference_colored_common_scale_source hσ hε
  obtain ⟨δ,c₀,U₀,_K,_D,hδ,hc₀,hU₀,_hK,_hD,hbuild⟩ :=
    approximateModelPhase_enlarged_double_difference_count hσ he
  obtain ⟨w₀,a,c,U,hw₀,hwcap,ha,hc,hU,hsmall,hanchor,hcolors⟩ := hcommon hc₀ hU₀
  refine ⟨δ,w₀,a,c,U,hδ,hw₀,hwcap,ha,hc,hU,hsmall,hanchor,?_⟩
  intro M F hM hF
  obtain ⟨Fext,hreg,hjets,hbound,hlower,htests,hnegative,hsharp,_hcount⟩ := hbuild M F hM hF
  have hdet : ∀ u∈Icc (1/2:ℝ) 3,
      c₀ ≤ |(iteratedDeriv 5 Fext u)^2-iteratedDeriv 4 Fext u*iteratedDeriv 6 Fext u| := by
    intro u hu
    have hh := htests u hu (4:Fin 7)
    simpa [HuxleyModel.tests,abs_sub_comm] using hh
  exact ⟨Fext,hreg,hsharp,hcolors Fext hreg hjets hbound hlower hdet hnegative⟩

private theorem fourth_pair_capped_terminal_source_window_scales
    {t u : ℝ} (ht : t∈Icc (0:ℝ) 1) (hu : u∈Icc (0:ℝ) 1) :
    let α := (1-t)*(890/3277)+t*(17604372/60424193)
    let h := ((1-t)*2749411+t*3296917)/100000000
    let g₀ := ((1-t)*16756+t*1976824)/100000000
    let ν₀ := ((1-t)*11931645+t*14567321)/100000000
    let ν₁ := ((1-t)*11969967+t*14925729)/100000000
    let g := (1-u)*g₀+u*(3*h)
    let ν := (1-u)*ν₀+u*ν₁
    let β := 89/3478+(7441/8695)*α
    1/100000 ≤ g₀ ∧ g₀+1/100000 ≤ 3*h ∧ 1/100000 ≤ h ∧
      8*h+1/100000 ≤ α ∧
      2*α+1/2+(3/2)*g₀-3*h+1/100000 ≤ 4*β ∧
      5*α-1/2+g₀/2-3*h+1/100000 ≤ 4*β ∧
      1/100000 ≤ ν ∧ ν+1/100000 ≤ α ∧
      4*α-1-g+1/100000 ≤ ν ∧ ν+3*α+1/100000 ≤ 1+g ∧
      3*α+1/100000 ≤ 1+g ∧ 7*α+1/100000 ≤ 2+2*g+ν ∧
      5*α-1-g+1/100000 ≤ 3*ν ∧
      4*ν+1/100000 ≤ 6*α-1-g ∧
      1+g+1/100000 ≤ 4*α ∧
      1+g+2*ν+1/100000 ≤ 5*α ∧
      3+3*g+11*ν+1/100000 ≤ 17*α ∧
      7+7*g+27*ν+1/100000 ≤ 41*α ∧
      288*α-144*h+1/10000 ≤ 288*β ∧
      288*α-36*ν+72*g-216*h+1/10000 ≤ 288*β ∧
      648*α-72-216*h-216*ν+1/10000 ≤ 288*β ∧
      24+96*g-216*h+96*α+144*ν+1/10000 ≤ 288*β ∧
      21+87*g-216*h+177*α+33*ν+1/10000 ≤ 288*β ∧
      15+87*g-216*h+207*α+15*ν+1/10000 ≤ 288*β ∧
      12+78*g-216*h+216*α+24*ν+1/10000 ≤ 288*β ∧
      6+78*g-216*h+246*α+6*ν+1/10000 ≤ 288*β ∧
      4+76*g-216*h+268*α-24*ν+1/10000 ≤ 288*β ∧
      72*g-216*h+284*α-24*ν+1/10000 ≤ 288*β ∧
      504*α-72-216*h+72*ν+1/10000 ≤ 288*β := by
  intro α h g₀ ν₀ ν₁ g ν β
  have ht0 := ht.1
  have ht1 := ht.2
  have hu0 := hu.1
  have hu1 := hu.2
  have h00 := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hu1)
  have h01 := mul_nonneg (sub_nonneg.mpr ht1) hu0
  have h10 := mul_nonneg ht0 (sub_nonneg.mpr hu1)
  have h11 := mul_nonneg ht0 hu0
  dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β]
  repeat' constructor
  all_goals nlinarith only [ht0,ht1,hu0,hu1,h00,h01,h10,h11]

private theorem capped_terminal_physical_error
    {M N R Q qcap : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hcap : 0 < qcap)
    (hQ : qcap*min N (M/N) ≤ Q) :
    M*R^2/Q^2 ≤ (1/qcap^2)*(M*R^2/N^2+N^2*R^2/M) := by
  have hnum : 0 ≤ M*R^2 := mul_nonneg hM.le (sq_nonneg R)
  rcases le_total N (M/N) with hn | hn
  · rw [min_eq_left hn] at hQ
    calc
      _ ≤ M*R^2/(qcap*N)^2 := div_le_div_of_nonneg_left hnum
        (sq_pos_of_pos (mul_pos hcap hN)) (pow_le_pow_left₀ (mul_pos hcap hN).le hQ 2)
      _ = (1/qcap^2)*(M*R^2/N^2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (by positivity)) (by positivity)
  · rw [min_eq_right hn] at hQ
    calc
      _ ≤ M*R^2/(qcap*(M/N))^2 := div_le_div_of_nonneg_left hnum
        (sq_pos_of_pos (mul_pos hcap (div_pos hM hN)))
        (pow_le_pow_left₀ (mul_pos hcap (div_pos hM hN)).le hQ 2)
      _ = (1/qcap^2)*(N^2*R^2/M) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (by positivity)) (by positivity)

private theorem capped_dyadic_band_integer_physical_selection
    (N : ℕ) {σ J M R B L Cbase qcap Dcap : ℝ}
    (hσ : 0 < σ) (hM : 0 < M) (hR : 1 ≤ R) (hRN : R ≤ N) (hNR : (N:ℝ) ≤ R^2)
    (hB : 1 ≤ B) (hL : 1 ≤ L) (hCbase : 768 ≤ Cbase)
    (hcap : 0 < qcap) (hcapOne : qcap ≤ 1)
    (hlarge : qcap*(2*B*L)^((3:ℝ)/2) ≤ 1)
    (hDcap : 0 ≤ Dcap) (hsmall : 4*Dcap*qcap ≤ 1)
    (hroom : 2*Cbase*R ≤ qcap*min (N:ℝ) (M/(N:ℝ))) :
    ∃ (Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ),
      let Q := fun k : ℕ => Qbase*2^k
      Cbase*R ≤ Qbase ∧ (Qbase:ℝ) ≤ 2*Cbase*R ∧
      qcap*min (N:ℝ) (M/(N:ℝ))/2 ≤ Q kmax ∧
      (Q kmax:ℝ) ≤ qcap*min (N:ℝ) (M/(N:ℝ)) ∧
      (N:ℝ)*(Q kmax:ℝ) ≤ M ∧
      M*R^2/(Q kmax:ℝ)^2 ≤ (4/qcap^2)*
        (M*R^2/(N:ℝ)^2+(N:ℝ)^2*R^2/M) ∧
      (kmax:ℝ) ≤ Real.log N/Real.log 2 ∧
      (∀ k, 0 < Kmesh k) ∧
      (∀ k ≤ kmax,
        L ≤ (Usel k:ℝ) ∧
        63*(J/(2*σ*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
        (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
        (Kmesh k:ℝ) ≤ 2*(max 1 (63*J/(2*σ)))*(Q k:ℝ)*(N:ℝ)/R^2 ∧
        1 ≤ Usel k ∧
        B^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
        (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/B ∧
        ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*B) ≤ (Usel k:ℝ) ∧
        Q k ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
        768*R ≤ (Q k:ℝ) ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
        Dcap*(Q k:ℝ)/(N:ℝ) ≤ 1/4) ∧
      (∀ k, Usel k ≤ Usel 0) := by
  have hNp : (0:ℝ) < N := (zero_lt_one.trans_le hR).trans_le hRN
  let qcap' := qcap*min 1 (M/(N:ℝ)^2)
  have hp : 0 < qcap' := mul_pos hcap (lt_min (by norm_num) (div_pos hM (sq_pos_of_pos hNp)))
  have hle : qcap' ≤ qcap := by
    calc
      _ ≤ qcap*1 := mul_le_mul_of_nonneg_left (min_le_left _ _) hcap.le
      _ = qcap := mul_one _
  have hid : qcap'*(N:ℝ)=qcap*min (N:ℝ) (M/(N:ℝ)) := by
    dsimp only [qcap']
    rw [mul_assoc,min_mul_of_nonneg _ _ hNp.le,one_mul]
    have he : (M/(N:ℝ)^2)*(N:ℝ)=M/(N:ℝ) := by field_simp
    rw [he]
  have hlarge' : qcap'*(2*B*L)^((3:ℝ)/2) ≤ 1 :=
    (mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg (by positivity) _)).trans hlarge
  have hsmall' : 4*Dcap*qcap' ≤ 1 :=
    (mul_le_mul_of_nonneg_left hle (by positivity)).trans hsmall
  have hroom' : 2*Cbase*R ≤ qcap'*(N:ℝ) := by rw [hid]; exact hroom
  obtain ⟨Qbase,kmax,Kmesh,Usel,hlo,hhi,hqlo,hqhi,hlog,hK,hbudgets,hmono⟩ :=
    dyadic_band_integer_physical_selection N (J:=J) hσ hR hRN hNR hB hL hCbase hp
      (hle.trans hcapOne) hlarge' hDcap hsmall' hroom'
  let Q := fun k : ℕ => Qbase*2^k
  have hlow : qcap*min (N:ℝ) (M/(N:ℝ))/2 ≤ (Q kmax:ℝ) := by
    simpa only [hid] using hqlo
  have hupp : (Q kmax:ℝ) ≤ qcap*min (N:ℝ) (M/(N:ℝ)) := by
    simpa only [hid] using hqhi
  have hmax : (Q kmax:ℝ) ≤ M/(N:ℝ) := by
    calc
      _ ≤ qcap*min (N:ℝ) (M/(N:ℝ)) := hupp
      _ ≤ 1*min (N:ℝ) (M/(N:ℝ)) := mul_le_mul_of_nonneg_right hcapOne
        (le_min hNp.le (div_pos hM hNp).le)
      _ ≤ M/(N:ℝ) := by simpa only [one_mul] using min_le_right (N:ℝ) (M/(N:ℝ))
  have hNQ : (N:ℝ)*(Q kmax:ℝ) ≤ M := by
    have hh := (le_div_iff₀ hNp).mp hmax
    simpa only [mul_comm] using hh
  have herror : M*R^2/(Q kmax:ℝ)^2 ≤ (4/qcap^2)*
      (M*R^2/(N:ℝ)^2+(N:ℝ)^2*R^2/M) := by
    have hh := capped_terminal_physical_error (R:=R) hM hNp (show 0 < qcap/2 by positivity)
      (show (qcap/2)*min (N:ℝ) (M/(N:ℝ)) ≤ (Q kmax:ℝ) from
        (by simpa only [div_mul_eq_mul_div] using hlow))
    convert hh using 1
    congr 1
    field_simp
    norm_num
  exact ⟨Qbase,kmax,Kmesh,Usel,hlo,hhi,hlow,hupp,hNQ,herror,hlog,hK,hbudgets,hmono⟩

private theorem double_difference_chunk_grid_dyadic_bands
    (Chunks : Finset (ℝ × ℤ)) (Y : Finset ℝ) (F rshift sshift : ℝ → ℝ)
    (n N Qbase kmax : ℕ) (hNlink : N=8*n)
    {c U d w T M R : ℝ}
    (hc : 0 < c) (hU : 0 < U)
    (hn : 0 < n) (hd : 0 < d) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hshifts : ∀ y∈Y, 0 ≤ rshift y ∧ 0 ≤ sshift y ∧
      rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ w)
    (hy : ∀ y∈Y, y∈Icc (1:ℝ) 2) (hphase : ∀ p∈Chunks, p.1∈Y)
    (hT : 0 < T) (hM : 0 < M) (hR : 0 < R)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ u∈Icc (1/2:ℝ) 3, ∀ j, 1 ≤ j → j ≤ 7 → |iteratedDeriv j F u| ≤ U)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hscale : T*(N:ℝ)*R^2=M^3)
    (hQbase : 768 ≤ Qbase)
    (hQmax : (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M) :
    let f := fun y v => T*((F (v/M)-F (v/M+rshift y)-F (v/M+sshift y)+
      F (v/M+rshift y+sshift y))/d)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let probe := fun (p : ℝ × ℤ) (i : Fin 2) =>
      if i=0 then (n:ℝ)*p.2-2*(N:ℝ) else (n:ℝ)*p.2-11*(N:ℝ)/4
    (∀ p∈Chunks, ∀ i, probe p i∈Icc (M+(N:ℝ)/4) (2*M-(N:ℝ)/4)) →
    let Q := fun k : ℕ => Qbase*2^k
    let Ctail := 4*U*(64/c)^2+192/c
    let Clow := (2*U+c/32)*(3072/c)^2+3072/c
    let Cerror := (768:ℝ)^2*Ctail+Clow
    let Density := fun k => 128*Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (512*R^2/(c*((Q k:ℝ)/768))+1))
    ∃ (anchor : (ℝ × ℤ) → Fin 2 → ℚ)
      (band : (ℝ × ℤ) → Option ℕ) (za : (ℝ × ℤ) → Fin 2 → ℝ),
      (∀ p∈Chunks, ∀ i,
        h p.1 (za p i)=(anchor p i:ℝ) ∧
        |za p i-probe p i| ≤ (N:ℝ)/16 ∧ za p i∈Icc M (2*M)) ∧
      (∀ p∈Chunks, match band p with
        | none => ∃ i, ¬(768*(anchor p i).den ≤ Q kmax ∧
            24576*R^2 ≤ c*(Q kmax:ℝ)*(anchor p i).den)
        | some k => k ≤ kmax ∧
            (∀ i, 768*(anchor p i).den ≤ Q k ∧
              24576*R^2 ≤ c*(Q k:ℝ)*(anchor p i).den)) ∧
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        (Y.card:ℝ)*Density k) ∧
      ((Chunks.filter (fun p => band p=none)).card:ℝ) ≤
        (Y.card:ℝ)*Density kmax := by
  classical
  intro f h probe hpoints Q Ctail Clow Cerror Density
  have hnp : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hNreal : (N:ℝ)=8*(n:ℝ) := by exact_mod_cast hNlink
  have hnN : (n:ℝ) ≤ N := by rw [hNreal]; linarith only [hnp]
  let Rfine := Real.sqrt 8*R
  have hRfine : 0 < Rfine := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hR
  have hRsq : Rfine^2=8*R^2 := by
    dsimp only [Rfine]
    rw [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 8)]
  have hscaleFine : T*(n:ℝ)*Rfine^2=M^3 := by
    rw [hRsq]
    rw [hNreal] at hscale
    nlinarith only [hscale]
  have hQfine : (n:ℝ)*(Qbase*2^kmax:ℕ) ≤ M :=
    (mul_le_mul_of_nonneg_right hnN (Nat.cast_nonneg _)).trans hQmax
  let Sy := fun y => (Chunks.filter (fun p => p.1=y)).image Prod.snd
  have hSy y j : j∈Sy y ↔ (y,j)∈Chunks := by
    constructor
    · intro hj
      obtain ⟨p,hp,hpj⟩ := Finset.mem_image.mp hj
      have heq : p=(y,j) := Prod.ext (Finset.mem_filter.mp hp).2 hpj
      exact heq ▸ (Finset.mem_filter.mp hp).1
    · intro hj
      exact Finset.mem_image.mpr ⟨(y,j),Finset.mem_filter.mpr ⟨hj,rfl⟩,rfl⟩
  let base := fun i : Fin 2 => if i=0 then -2*(N:ℝ) else -11*(N:ℝ)/4
  have hprobe y j i : base i+(n:ℝ)*j=probe (y,j) i := by
    dsimp only [base,probe]
    split_ifs <;> ring
  let FineDensity := fun k => 2*Cerror*(M*Rfine^2/((n:ℝ)*(Q k:ℝ)^2))*
    (2+Real.log (64*Rfine^2/(c*((Q k:ℝ)/768))+1))
  have hDensity k : FineDensity k=Density k := by
    dsimp only [FineDensity,Density]
    rw [hRsq,hNreal]
    have he : 64*(8*R^2)=512*R^2 := by ring
    rw [he]
    ring
  have hex (y : ℝ) : ∃ (a : ℤ → Fin 2 → ℚ) (b : ℤ → Option ℕ)
      (z : ℤ → Fin 2 → ℝ), y∈Y →
      (∀ j∈Sy y, ∀ i, h y (z j i)=(a j i:ℝ) ∧
        |z j i-probe (y,j) i| ≤ (N:ℝ)/16 ∧ z j i∈Icc M (2*M)) ∧
      (∀ j∈Sy y, match b j with
        | none => ∃ i, ¬(768*(a j i).den ≤ Q kmax ∧
            24576*R^2 ≤ c*(Q kmax:ℝ)*(a j i).den)
        | some k => k ≤ kmax ∧
            (∀ i, 768*(a j i).den ≤ Q k ∧
              24576*R^2 ≤ c*(Q k:ℝ)*(a j i).den)) ∧
      (∀ k ≤ kmax, (((Sy y).filter (fun j => b j=some (k+1))).card:ℝ) ≤ Density k) ∧
      (((Sy y).filter (fun j => b j=none)).card:ℝ) ≤ Density kmax := by
    by_cases hyY : y∈Y
    · have hpointsFine j (hj : j∈Sy y) i :
          base i+(n:ℝ)*j∈Icc (M+(n:ℝ)/4) (2*M-(n:ℝ)/4) := by
        rw [hprobe y j i]
        have hh := hpoints (y,j) ((hSy y j).mp hj) i
        constructor <;> linarith only [hh.1,hh.2,hnN]
      obtain ⟨a,b,z,_hminimal,hroots,hband,_htransfer,hcounts,htail⟩ :=
        double_difference_two_probe_dyadic_quadratic_density (Sy y) F n Qbase kmax 768 base 3072
          (hshifts y hyY).1 (hshifts y hyY).2.1 hd (hy y hyY)
          (hshifts y hyY).2.2.1 (hshifts y hyY).2.2.2 hw hsmall
          hc hU hT hM hn hRfine hscaleFine hreg hlower hbound hnegative
          (by norm_num) hQbase (by norm_num) hpointsFine hQfine
      refine ⟨a,b,z,fun _ => ⟨?_,?_,?_,?_⟩⟩
      · intro j hj i
        have hh := hroots j hj i
        change h y (z j i)=(a j i:ℝ) ∧
          |z j i-(base i+(n:ℝ)*j)| ≤ (n:ℝ)/16 ∧ z j i∈Icc M (2*M) at hh
        rw [hprobe y j i] at hh
        exact ⟨hh.1,hh.2.1.trans (div_le_div_of_nonneg_right hnN (by norm_num)),hh.2.2⟩
      · intro j _hj
        have hh := hband j
        have hB : (3072:ℝ)*Rfine^2=24576*R^2 := by rw [hRsq]; ring
        dsimp only at hh
        rw [hB] at hh
        cases hb : b j with
        | none => simpa only [hb] using hh
        | some k =>
          rw [hb] at hh
          exact ⟨hh.1,hh.2.1⟩
      · intro k hk
        have hh := hcounts k hk
        change _ ≤ FineDensity k at hh
        exact hh.trans_eq (hDensity k)
      · change _ ≤ FineDensity kmax at htail
        exact htail.trans_eq (hDensity kmax)
    · exact ⟨fun _ _ => 0,fun _ => none,fun _ _ => 0,fun hh => (hyY hh).elim⟩
  choose a b z hdata using hex
  let anchor := fun p : ℝ × ℤ => a p.1 p.2
  let band := fun p : ℝ × ℤ => b p.1 p.2
  let za := fun p : ℝ × ℤ => z p.1 p.2
  have hcount (label : Option ℕ) (Bound : ℝ)
      (hlocal : ∀ y∈Y, (((Sy y).filter (fun j => b y j=label)).card:ℝ) ≤ Bound) :
      ((Chunks.filter (fun p => band p=label)).card:ℝ) ≤ (Y.card:ℝ)*Bound := by
    let E := Chunks.filter (fun p => band p=label)
    let Ey := fun y => (E.filter (fun p => p.1=y)).image Prod.snd
    have hEq y : Ey y=(Sy y).filter (fun j => b y j=label) := by
      ext j
      constructor
      · intro hj
        obtain ⟨p,hp,hpj⟩ := Finset.mem_image.mp hj
        obtain ⟨hpE,hpy⟩ := Finset.mem_filter.mp hp
        obtain ⟨hpC,hpb⟩ := Finset.mem_filter.mp hpE
        have heq : p=(y,j) := Prod.ext hpy hpj
        subst p
        exact Finset.mem_filter.mpr ⟨(hSy y j).mpr hpC,hpb⟩
      · intro hj
        obtain ⟨hjS,hjb⟩ := Finset.mem_filter.mp hj
        exact Finset.mem_image.mpr ⟨(y,j),
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨(hSy y j).mp hjS,hjb⟩,rfl⟩,rfl⟩
    have hcard y : (Ey y).card=(E.filter (fun p => p.1=y)).card := by
      apply Finset.card_image_of_injOn
      intro p hp q hq hpq
      exact Prod.ext ((Finset.mem_filter.mp hp).2.trans
        (Finset.mem_filter.mp hq).2.symm) hpq
    have hmaps : ∀ p∈E, p.1∈Y := fun p hp => hphase p (Finset.mem_filter.mp hp).1
    have hsum : (∑ y∈Y,((Ey y).card:ℝ))=E.card := by
      simp_rw [hcard]
      have hh := Finset.sum_fiberwise_of_maps_to hmaps (fun _ => (1:ℝ))
      simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using hh
    change (E.card:ℝ) ≤ _
    rw [←hsum]
    calc
      _ ≤ ∑ _y∈Y,Bound := Finset.sum_le_sum (fun y hyY => by rw [hEq]; exact hlocal y hyY)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
  refine ⟨anchor,band,za,?_,?_,?_,?_⟩
  · intro p hp i
    exact (hdata p.1 (hphase p hp)).1 p.2 ((hSy p.1 p.2).mpr hp) i
  · intro p hp
    exact (hdata p.1 (hphase p hp)).2.1 p.2 ((hSy p.1 p.2).mpr hp)
  · intro k hk
    exact hcount (some (k+1)) (Density k) (fun y hyY => (hdata y hyY).2.2.1 k hk)
  · exact hcount none (Density kmax) (fun y hyY => (hdata y hyY).2.2.2)

private theorem double_difference_phase_subinterval_dyadic_band_reduction
    (Y : Finset ℝ) (F rshift sshift : ℝ → ℝ) (n N Qbase kmax : ℕ) (hNlink : N=8*n)
    {c U d w T M R Buffer Width : ℝ}
    (hc : 0 < c) (hU : 0 < U)
    (hn : 0 < n) (hd : 0 < d) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hshifts : ∀ y∈Y, 0 ≤ rshift y ∧ 0 ≤ sshift y ∧
      rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ w)
    (hy : ∀ y∈Y, y∈Icc (1:ℝ) 2)
    (hT : 0 < T) (hM : 0 < M) (hR : 0 < R)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ u∈Icc (1/2:ℝ) 3, ∀ j, 1 ≤ j → j ≤ 7 → |iteratedDeriv j F u| ≤ U)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hscale : T*(N:ℝ)*R^2=M^3)
    (hQbase : 768 ≤ Qbase) (hQmax : (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M)
    (hBuffer : 0 ≤ Buffer) (hWidth : 0 ≤ Width)
    (hroom : 2*(Buffer+Width)+6*(N:ℝ) ≤ M)
    (A B : ℝ → ℤ) (hA : ∀ y∈Y, ⌈M⌉ ≤ A y)
    (hab : ∀ y∈Y, A y ≤ B y) (hB : ∀ y∈Y, B y ≤ ⌊2*M⌋) :
    let f := fun y v => T*((F (v/M)-F (v/M+rshift y)-F (v/M+sshift y)+
      F (v/M+rshift y+sshift y))/d)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let probe := fun (p : ℝ × ℤ) (i : Fin 2) =>
      if i=0 then (n:ℝ)*p.2-2*(N:ℝ) else (n:ℝ)*p.2-11*(N:ℝ)/4
    let Q := fun k : ℕ => Qbase*2^k
    let Ctail := 4*U*(64/c)^2+192/c
    let Clow := (2*U+c/32)*(3072/c)^2+3072/c
    let Cerror := (768:ℝ)^2*Ctail+Clow
    let Density := fun k => 128*Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (512*R^2/(c*((Q k:ℝ)/768))+1))
    let Endpoint := (Y.card:ℝ)*(2*Buffer+2*Width+6*(N:ℝ)+2*(n:ℝ))
    ∃ (Chunks : Finset (ℝ × ℤ)) (anchor : (ℝ × ℤ) → Fin 2 → ℚ)
      (band : (ℝ × ℤ) → Option ℕ) (za : (ℝ × ℤ) → Fin 2 → ℝ),
      (∀ p∈Chunks, p.1∈Y) ∧
      (∀ p∈Chunks, (n:ℝ)*p.2∈
        Icc (M+Buffer+Width+4*(N:ℝ)) (2*M-Buffer-Width-(N:ℝ))) ∧
      (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/(N:ℝ)) ∧
      (∀ p∈Chunks, ∀ i,
        h p.1 (za p i)=(anchor p i:ℝ) ∧
        |za p i-probe p i| ≤ (N:ℝ)/16 ∧ za p i∈Icc M (2*M)) ∧
      (∀ p∈Chunks, match band p with
        | none => ∃ i, ¬(768*(anchor p i).den ≤ Q kmax ∧
            24576*R^2 ≤ c*(Q kmax:ℝ)*(anchor p i).den)
        | some k => k ≤ kmax ∧
            (∀ i, 768*(anchor p i).den ≤ Q k ∧
              24576*R^2 ≤ c*(Q k:ℝ)*(anchor p i).den)) ∧
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        (Y.card:ℝ)*Density k) ∧
      ((Chunks.filter (fun p => band p=none)).card:ℝ) ≤ (Y.card:ℝ)*Density kmax ∧
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (B y),(𝐞 (f y j):ℂ)‖)^12 ≤
        2^11*(((kmax:ℝ)+2)^11*
          (((n:ℝ)*(Y.card:ℝ)*Density kmax)^12+
            ∑ k∈Finset.range (kmax+1),
              (∑ p∈Chunks.filter (fun p => band p=some k),
                ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),
                  (𝐞 (f p.1 j):ℂ)‖)^12)+Endpoint^12) := by
  classical
  intro f h probe Q Ctail Clow Cerror Density Endpoint
  have hnp : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hNreal : (N:ℝ)=8*(n:ℝ) := by exact_mod_cast hNlink
  have hNp : (0:ℝ) < N := by rw [hNreal]; positivity
  obtain ⟨a₀,b₀,ha₀,hab₀,hb₀,hdeep₀,hend₀⟩ :=
    eight_grid_endpoint_selection n hn hBuffer hWidth (by
      simpa only [←hNreal] using hroom)
  let v := fun y j : ℝ => (𝐞 (f y j):ℂ)
  obtain ⟨Chunks,hChunks,hwhole⟩ :=
    integer_phase_subinterval_trimmed_chunks Y (fun y j => v y j) n hn A B ha₀ hb₀ hA hB hab
      (fun _ _ _ _ => by simp [v])
  have hphase p (hp : p∈Chunks) : p.1∈Y := (Finset.mem_product.mp (hChunks hp)).1
  have hdeep p (hp : p∈Chunks) : (n:ℝ)*p.2∈
      Icc (M+Buffer+Width+4*(N:ℝ)) (2*M-Buffer-Width-(N:ℝ)) := by
    simpa only [←hNreal] using hdeep₀ p.2 (Finset.mem_product.mp (hChunks hp)).2
  have hpoints p (hp : p∈Chunks) i :
      probe p i∈Icc (M+(N:ℝ)/4) (2*M-(N:ℝ)/4) := by
    have hh := hdeep p hp
    dsimp only [probe]
    split_ifs <;> constructor <;> linarith only [hh.1,hh.2,hBuffer,hWidth,hNp]
  obtain ⟨anchor,band,za,hroots,hbands,hcounts,htail⟩ :=
    double_difference_chunk_grid_dyadic_bands Chunks Y F rshift sshift n N Qbase kmax hNlink
      hc hU hn hd hw hsmall hshifts hy hphase hT hM hR hreg hbound hlower hnegative
      hscale hQbase hQmax hpoints
  have hleft : M ≤ (n:ℝ)*a₀ :=
    (Int.le_ceil M).trans (by exact_mod_cast ha₀)
  have hright : (n:ℝ)*b₀ ≤ 2*M :=
    (by exact_mod_cast hb₀ : (n:ℝ)*b₀ ≤ (⌊2*M⌋:ℤ)).trans (Int.floor_le (2*M))
  have hcardI : ((Finset.Ico a₀ b₀).card:ℝ)=((b₀-a₀:ℤ):ℝ) := by
    exact_mod_cast (show ((Finset.Ico a₀ b₀).card:ℤ)=b₀-a₀ by
      rw [Int.card_Ico,Int.toNat_of_nonneg (sub_nonneg.mpr hab₀)])
  have hcardIle : ((Finset.Ico a₀ b₀).card:ℝ) ≤ 8*M/(N:ℝ) := by
    apply (le_div_iff₀ hNp).mpr
    rw [hcardI,hNreal]
    push_cast
    nlinarith only [hleft,hright]
  have hcardChunks : (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/(N:ℝ)) := by
    have hh : (Chunks.card:ℝ) ≤ (Y.card:ℝ)*((Finset.Ico a₀ b₀).card:ℝ) := by
      exact_mod_cast (show Chunks.card ≤ Y.card*(Finset.Ico a₀ b₀).card by
        simpa only [Finset.card_product] using Finset.card_le_card hChunks)
    exact hh.trans (mul_le_mul_of_nonneg_left hcardIle (Nat.cast_nonneg _))
  refine ⟨Chunks,anchor,band,za,hphase,hdeep,hcardChunks,hroots,hbands,hcounts,htail,?_⟩
  have hbudget :
      ((((n:ℤ)*a₀-⌈M⌉)+(⌊2*M⌋-(n:ℤ)*b₀)+2*(n:ℤ):ℤ):ℝ) ≤
        2*Buffer+2*Width+6*(N:ℝ)+2*(n:ℝ) := by
    have hh := hend₀
    rw [←hNreal] at hh
    push_cast at hh ⊢
    linarith only [hh]
  let Mass := ∑ p∈Chunks,
    ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),(𝐞 (f p.1 j):ℂ)‖
  have hmass : 0 ≤ Mass := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hEndpoint : 0 ≤ Endpoint := by dsimp only [Endpoint]; positivity
  have hwhole' : (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (B y),(𝐞 (f y j):ℂ)‖) ≤ Mass+Endpoint :=
    hwhole.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg _)))
  have hbandMax p (hp : p∈Chunks) k (hk : band p=some k) : k ≤ kmax := by
    have hh := hbands p hp
    rw [hk] at hh
    exact hh.1
  have hpower := integer_chunk_dyadic_band_power Chunks (fun y j => v y j) n kmax band
    (fun _ _ => by simp [v]) hbandMax
  have htailLe : (n:ℝ)*((Chunks.filter (fun p => band p=none)).card:ℝ) ≤
      (n:ℝ)*(Y.card:ℝ)*Density kmax := by
    have htail' : ((Chunks.filter (fun p => band p=none)).card:ℝ) ≤
        (Y.card:ℝ)*Density kmax := htail
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left htail' hnp.le
  have hpower' : Mass^12 ≤ ((kmax:ℝ)+2)^11*
      (((n:ℝ)*(Y.card:ℝ)*Density kmax)^12+
        ∑ k∈Finset.range (kmax+1),
          (∑ p∈Chunks.filter (fun p => band p=some k),
            ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),(𝐞 (f p.1 j):ℂ)‖)^12) :=
    hpower.trans (mul_le_mul_of_nonneg_left
      (add_le_add (pow_le_pow_left₀ (by positivity) htailLe 12) le_rfl) (by positivity))
  calc
    _ ≤ (Mass+Endpoint)^12 :=
      pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hwhole' 12
    _ ≤ 2^11*(Mass^12+Endpoint^12) := add_pow_le hmass hEndpoint 12
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hpower' le_rfl) (by norm_num)

private theorem eight_grid_exact_selected_transport
    (Chunks : Finset (ℝ × ℤ)) (Y : Finset ℝ) (n N Q : ℕ)
    (hNlink : N=8*n) (hN : 0 < N) (h : ℝ → ℝ → ℝ) (v : ℝ → ℤ → ℂ)
    {M Buffer c R : ℝ} (anchor : (ℝ × ℤ) → ℚ) (za : (ℝ × ℤ) → ℝ)
    (hphase : ∀ p∈Chunks, p.1∈Y)
    (hdeep : ∀ p∈Chunks, (n:ℝ)*p.2∈
      Icc (M+Buffer+4*(N:ℝ)) (2*M-Buffer-(N:ℝ)))
    (hanchors : ∀ p∈Chunks,
      |za p-((n:ℝ)*p.2-2*(N:ℝ))| ≤ (N:ℝ)/16 ∧
      h p.1 (za p)=(anchor p:ℝ) ∧
      768*(anchor p).den ≤ Q ∧
      24576*R^2 ≤ c*(Q:ℝ)*(anchor p).den) :
    let Grid := fun r : ℤ =>
      (Chunks.filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
    let Point := fun (r : ℤ) (p : ℝ × ℤ) => (p.1,r+8*p.2+16)
    let Lsrc := fun (r : ℤ) (p : ℝ × ℤ) =>
      r*(n:ℤ)+(N:ℤ)*p.2+2*(N:ℤ)
    (∀ r, (Grid r).card ≤ Chunks.card ∧ (Grid r).image Prod.fst ⊆ Y ∧
      ∀ p∈Grid r,
        Point r p∈Chunks ∧ Lsrc r p=(n:ℤ)*(Point r p).2 ∧
        (Lsrc r p:ℝ)-2*(N:ℝ)∈
          Ioo (M+Buffer+(N:ℝ)) (2*M-Buffer-(N:ℝ)) ∧
        za (Point r p)∈Ioo ((Lsrc r p:ℝ)-2*(N:ℝ)-(N:ℝ)/8)
          ((Lsrc r p:ℝ)-2*(N:ℝ)+(N:ℝ)/8) ∧
        h p.1 (za (Point r p))=(anchor (Point r p):ℝ) ∧
        768*(anchor (Point r p)).den ≤ Q ∧
        24576*R^2 ≤ c*(Q:ℝ)*(anchor (Point r p)).den) ∧
    (∑ p∈Chunks, ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖)=
      ∑ r∈Finset.Ico (0:ℤ) 8,
        ∑ p∈Grid r, ‖∑ j∈Finset.Ioc (Lsrc r p) (Lsrc r p+n),v p.1 j‖ := by
  classical
  intro Grid Point Lsrc
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hNz : (N:ℤ)=8*(n:ℤ) := by exact_mod_cast hNlink
  have hstart r p : Lsrc r p=(n:ℤ)*(Point r p).2 := by
    dsimp only [Lsrc,Point]
    rw [hNz]
    ring
  have hstartR r p : (Lsrc r p:ℝ)=(n:ℝ)*(Point r p).2 := by
    exact_mod_cast hstart r p
  have hpoint r p (hp : p∈Grid r) : Point r p∈Chunks := by
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hqC,hqmod⟩ := Finset.mem_filter.mp hq
    have heq : r+8*(q.2/8-2)+16=q.2 := by omega
    change (q.1,r+8*(q.2/8-2)+16)∈Chunks
    rw [heq]
    exact hqC
  refine ⟨?_,?_⟩
  · intro r
    refine ⟨Finset.card_image_le.trans (Finset.card_filter_le _ _),?_,?_⟩
    · intro y hy
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hy
      exact hphase (Point r p) (hpoint r p hp)
    · intro p hp
      have hq := hpoint r p hp
      have hd := hdeep (Point r p) hq
      have ha := hanchors (Point r p) hq
      rw [←hstartR r p] at hd ha
      refine ⟨hq,hstart r p,?_,?_,ha.2.1,ha.2.2.1,ha.2.2.2⟩
      · constructor <;> linarith only [hd.1,hd.2,hNp]
      · have hh := abs_le.mp ha.1
        constructor <;> linarith only [hh.1,hh.2,hNp]
  · rw [eight_grid_sum_reindex Chunks]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro p _
    have he : (n:ℤ)*((Point r p).2+1)=Lsrc r p+n := by rw [hstart]; ring
    change ‖∑ j∈Finset.Ioc ((n:ℤ)*(Point r p).2)
      ((n:ℤ)*((Point r p).2+1)),v p.1 j‖=_
    rw [he,←hstart]

private theorem eventually_double_difference_direct_residue_grid_moment
    {csrc Usrc σ εloss : ℝ}
    (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let L := max (32*Usrc^2/csrc^2)
      (64*(modelPhaseJetCoefficient σ 3+1)*Usrc/κ^2)
    let θ := 1/(8*(L+3))
    ∃ CF C Dtype : ℝ, 1 ≤ CF ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Chunks : Finset (ℝ × ℤ)) (Fsrc rshift sshift : ℝ → ℝ)
    (zaC : (ℝ × ℤ) → ℝ)
    (n Q K₀ N : ℕ) [NeZero K₀] (R Jsep : ℝ) (r : ℤ)
    {d Wmax M δ Bcut Bselect : ℝ}
    (Uref : ℕ) (anchorC : (ℝ × ℤ) → ℚ),
    N=8*n →
    let S := (Chunks.filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
    let Z := fun _ : ℝ => r*(n:ℤ)
    let H := fun _ : ℝ × ℤ => n
    let lambda := csrc*T/(2*M^2)
    let Uband := Usrc*T/M^2
    let Vscale := max 1 (Uband*(N:ℝ)/(Q:ℝ))
    let Lsrc := fun i : ℝ × ℤ => Z i.1+(N:ℤ)*i.2+2*(N:ℤ)
    let Buffer := (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(σ*(σ+1)+3)+2
    (0 < d) → (0 ≤ Wmax) → (Wmax ≤ 1/4) → (2*Usrc*Wmax ≤ csrc/64) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (0 < Q) → (Uband ≤ 1) →
    (∀ i∈Chunks, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈Chunks, (n:ℝ)*i.2∈Icc (M+Buffer+4*(N:ℝ)) (2*M-Buffer-(N:ℝ))) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, csrc ≤ iteratedDeriv 5 Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3,
      csrc ≤ |(iteratedDeriv 5 Fsrc w)^2-iteratedDeriv 4 Fsrc w*iteratedDeriv 6 Fsrc w|) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (2 ≤ M) →
    (0 < N) →
    (0 < Jsep) → (Jsep ≤ M) → ((N:ℝ) ≤ M) → (Wmax*Jsep ≤ 1) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/4)*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    63*(Usrc/(2*(N:ℝ)*R^2))*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
    (∀ i∈Chunks, ∀ j∈Chunks, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    (∀ y∈Chunks.image Prod.fst,
      0 ≤ rshift y ∧ 0 ≤ sshift y ∧ rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
    let Φ := fun y u =>
      (Fsrc u-Fsrc (u+rshift y)-Fsrc (u+sshift y)+Fsrc (u+rshift y+sshift y))/d
    (∀ i∈Chunks, Expdb.IsApproximateModelPhaseFunction (Φ i.1) σ 4 δ) →
    let f := fun p w => T*Φ p (w/M)
    (∀ i∈Chunks,
      |zaC i-((n:ℝ)*i.2-2*(N:ℝ))| ≤ (N:ℝ)/16 ∧
      iteratedDeriv 2 (f i.1) (zaC i)/2=(anchorC i:ℝ) ∧
      768*(anchorC i).den ≤ Q ∧
      24576*R^2 ≤ csrc*(Q:ℝ)*(anchorC i).den) →

    (1 ≤ R) → (R ≤ M) → (T*(N:ℝ)*R^2=M^3) →
    (0 < Bcut) →
    (1 ≤ Uref) →
    (2+168/κ ≤ Bselect) → (7*Bcut ≤ κ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (Q:ℝ) ≤ (N:ℝ) →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) → (Uref:ℝ) ≤ R^2 →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    2 ≤ (N:ℝ) →
    csrc ≤ 4*κ/(Cphys+2) →
    let NarrowCap := (4/θ+3)*(8*Usrc/(csrc*θ)+3)
    let Cap := 3*NarrowCap
    let μ₀ := csrc*T/(12*M^3)
    let U₀ := Usrc*T/(2*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Klarge := 60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain*((Q:ℝ)/(Uband*(N:ℝ)))^((2:ℝ)/3)+Ctail/(Uref:ℝ))
    let Y := S.image Prod.fst
    let Wphys := (144*Usrc/(csrc*κ))*(R^2/(Q:ℝ))
    let Mass := Vscale*Dtype*(2+θ*(Uband+1/lambda))*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
      (Y.card:ℝ)^2*Klarge*T^εloss
    let Error := (S.card:ℝ)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+36*Usrc*R^2/(csrc*κ*(N:ℝ)))
    (∑ i∈S, ‖∑ n∈Finset.Ioc (Lsrc i) (Lsrc i+H i),(𝐞 (f i.1 n):ℂ)‖)^12 ≤
      CF^12*2^11*((1+Real.log K₀)^12*Wphys^6*
        (C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(S.card:ℝ))^10*Mass)+Error^12) := by
  classical
  intro κ L θ
  obtain ⟨CF,C,Dtype,hCF,hC,hDtype,hsource⟩ :=
    eventually_double_difference_original_selected_block_moment hcsrc hUsrc hσ hεloss
  refine ⟨CF,C,Dtype,hCF,hC,hDtype,?_⟩
  filter_upwards [hsource] with T hfamily
  intro Chunks Fsrc rshift sshift zaC n Q K₀ N instK R Jsep r
    d Wmax M δ Bcut Bselect Uref anchorC hNlink S Z H
    lambda Uband Vscale Lsrc Buffer hd hw hwcap hsmallShift hT hM hδ hQ hUbandCap
    hy hdeep hreg hlower hjets htests hnegative hMtwo hN
    hJsep hJM hNM hwJ hmesh hfourBuffer hfourBudget hquadBudget hfullmesh
    hseparation hshifts Φ hmodel f hanchors
    hR hRM hscale hBcut hUref hBselectSize hcutMargin hselectedWrap hRQ
    hselectedUpper hscaleTen hQN hNsqM hUR
    Cphys c J B hsmall hNR hRN hNcube hminscale hNtwo hanchorBudget
    NarrowCap Cap μ₀ U₀ Δtype C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase
    hsize hD hΔ hBsize Lunit Gamma Cthird Cpack Cfirst Cgap Cmain Ctail Klarge Y Wphys Mass Error
  let Point := fun p : ℝ × ℤ => (p.1,r+8*p.2+16)
  let za := fun p => zaC (Point p)
  let anchor := fun p => anchorC (Point p)
  let Fmodel := fun (i : ℝ × ℤ) u => Φ i.1 u
  let ε := κ/(16*(Cphys+2)*R^2)
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCp : 0 < Cphys+2 := by dsimp only [Cphys]; positivity
  have hRp : 0 < R := zero_lt_one.trans_le hR
  obtain ⟨hgrids,_⟩ := eight_grid_exact_selected_transport Chunks
    (Chunks.image Prod.fst) n N Q hNlink hN
    (fun y w => iteratedDeriv 2 (f y) w/2) (fun y j => (𝐞 (f y j):ℂ))
    anchorC zaC (fun p hp => Finset.mem_image_of_mem Prod.fst hp) hdeep hanchors
  have hg := hgrids r
  have hmem i (hi : i∈S) : Point i∈Chunks := (hg.2.2 i hi).1
  have hbuffer i (hi : i∈S) :
      (Lsrc i:ℝ)-2*(N:ℝ)∈Ioo (M+Buffer+(N:ℝ)) (2*M-Buffer-(N:ℝ)) :=
    (hg.2.2 i hi).2.2.1
  have ha i (hi : i∈S) :
      za i∈Ioo ((Lsrc i:ℝ)-2*(N:ℝ)-(N:ℝ)/8)
        ((Lsrc i:ℝ)-2*(N:ℝ)+(N:ℝ)/8) ∧
      iteratedDeriv 2 (f i.1) (za i)/2=(anchor i:ℝ) ∧
      768*(anchor i).den ≤ Q ∧
      24576*R^2 ≤ csrc*(Q:ℝ)*(anchor i).den := (hg.2.2 i hi).2.2.2
  have hyS i (hi : i∈S) : i.1∈Icc (1:ℝ) 2 := hy (Point i) (hmem i hi)
  have hHS i (_hi : i∈S) : H i ≤ N := by dsimp only [H]; omega
  have hden i (hi : i∈S) : 2*(anchor i).den ≤ Q := by
    have hh := (ha i hi).2.2.1
    omega
  have hmajor i (hi : i∈S) : 128*R^2 ≤ csrc*(Q:ℝ)*(anchor i).den := by
    have hh := (ha i hi).2.2.2
    nlinarith only [hh,sq_nonneg R]
  have hsep i (hi : i∈S) j (hj : j∈S) (hne : i.1≠j.1) :
      1 ≤ Jsep*|i.1-j.1| := hseparation (Point i) (hmem i hi) (Point j) (hmem j hj) hne
  have hshift y (hyY : y∈S.image Prod.fst) :
      0 ≤ rshift y ∧ 0 ≤ sshift y ∧ rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax :=
    hshifts y (hg.2.1 hyY)
  have hmodels i (hi : i∈S) : Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 4 δ :=
    hmodel (Point i) (hmem i hi)
  have haroot i (hi : i∈S) :
      za i∈Ioo ((Lsrc i:ℝ)-2*(N:ℝ)-(N:ℝ)/8)
        ((Lsrc i:ℝ)-2*(N:ℝ)+(N:ℝ)/8) ∧
      iteratedDeriv 2 (f i.1) (za i)/2=(anchor i:ℝ) :=
    ⟨(ha i hi).1,(ha i hi).2.1⟩
  have hcut i (hi : i∈S) : 256*((anchor i).den:ℝ) ≤ (Q:ℝ)/3 := by
    have hh : (768:ℝ)*((anchor i).den:ℝ) ≤ Q := by exact_mod_cast (ha i hi).2.2.1
    linarith only [hh]
  have hcount i (hi : i∈S) : 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor i).den := by
    have hm := (ha i hi).2.2.2
    have hb : csrc*(Cphys+2) ≤ 4*κ := (le_div_iff₀ hCp).mp hanchorBudget
    have hh := mul_le_mul_of_nonneg_right hm hCp.le
    have hb' := mul_le_mul_of_nonneg_right hb
      (show 0 ≤ (Q:ℝ)*((anchor i).den:ℝ) by positivity)
    have he : (2*ε)*((Q:ℝ)/3)*(anchor i).den =
        κ*(Q:ℝ)*(anchor i).den/(24*(Cphys+2)*R^2) := by
      dsimp only [ε]
      field_simp
      ring
    rw [he]
    apply (le_div_iff₀ (show 0 < 24*(Cphys+2)*R^2 by positivity)).mpr
    nlinarith only [hh,hb']
  exact hfamily S Fsrc rshift sshift H za Q K₀ N R Jsep Z
    (d:=d) (Wmax:=Wmax) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
    Uref anchor hd hw hwcap hsmallShift hT hM hδ hQ hUbandCap
    hyS hbuffer hreg hlower hjets htests hnegative hMtwo hN
    hJsep hJM hNM hwJ hmesh hHS hfourBuffer hfourBudget hquadBudget hfullmesh hden hmajor
    hsep hshift hmodels haroot
    hR hRM hscale hBcut hUref hBselectSize hcutMargin hselectedWrap hRQ
    hselectedUpper hscaleTen hQN hNsqM hUR
    hsmall hNR hRN hNcube hminscale hNtwo hanchorBudget hcut hcount
    hsize hD hΔ hBsize

private theorem eventually_double_difference_all_band_subinterval_moment
    {csrc Usrc σ εloss : ℝ}
    (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let L := max (32*Usrc^2/csrc^2)
      (64*(modelPhaseJetCoefficient σ 3+1)*Usrc/κ^2)
    let θ := 1/(8*(L+3))
    ∃ CF C Dtype : ℝ, 1 ≤ CF ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc rshift sshift : ℝ → ℝ) (Y : Finset ℝ)
    (n N Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ) (R Jsep : ℝ)
    {d Wmax M δ Bcut Bselect : ℝ},
    (∀ k, 0 < Kmesh k) → N=8*n →
    0 < d → 0 ≤ Wmax → Wmax ≤ 1/4 → 2*Usrc*Wmax ≤ csrc/64 →
    0 < T → 2 ≤ M → 0 < N → δ ≤ min κ 1 →
    1 ≤ R → R ≤ M → 0 < Jsep → Jsep ≤ M → (N:ℝ) ≤ M → Wmax*Jsep ≤ 1 →
    (∀ y∈Y, y∈Icc (1:ℝ) 2) →
    (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
    (∀ y∈Y, 0 ≤ rshift y ∧ 0 ≤ sshift y ∧
      rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, csrc ≤ iteratedDeriv 5 Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j, 1 ≤ j → j ≤ 7 → |iteratedDeriv j Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3,
      csrc ≤ |(iteratedDeriv 5 Fsrc w)^2-iteratedDeriv 4 Fsrc w*iteratedDeriv 6 Fsrc w|) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    let Φ := fun y u =>
      (Fsrc u-Fsrc (u+rshift y)-Fsrc (u+sshift y)+Fsrc (u+rshift y+sshift y))/d
    (∀ y∈Y, Expdb.IsApproximateModelPhaseFunction (Φ y) σ 4 δ) →
    T*(N:ℝ)*R^2=M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/4)*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    0 < Bcut → 2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    (N:ℝ)^10 ≤ M^3*R^7 →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) →
    let Q := fun k : ℕ => Qbase*2^k
    768 ≤ Qbase → (N:ℝ)*(Q kmax:ℝ) ≤ M →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2 ≤ (N:ℝ) → csrc ≤ 4*κ/(Cphys+2) →
    let lambda := csrc*T/(2*M^2)
    let Uband := Usrc*T/M^2
    Uband ≤ 1 →
    let NarrowCap := (4/θ+3)*(8*Usrc/(csrc*θ)+3)
    let Cap := 3*NarrowCap
    let μ₀ := csrc*T/(12*M^3)
    let U₀ := Usrc*T/(2*M^3)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Δtype := fun k : ℕ =>
      (16*U₀/μ₀)*Real.sqrt (U₀*(Q k:ℝ)^3)*Real.sqrt (Kmesh k)/(6*(Kmesh k:ℝ)^2)
    let Δ := fun k : ℕ => (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q k:ℝ)/(N:ℝ)
    let D := fun k : ℕ => Δ k+quarticNonlinearResidualConstant σ δ*(2*(Q k:ℝ))/(N:ℝ)
    let Buffer := fun k : ℕ => (56*(Usel k:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    (∀ k ≤ kmax,
      63*(Usrc/(2*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      1 ≤ Usel k ∧ Bselect^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
      R ≤ (Q k:ℝ) ∧
      (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      (Q k:ℝ) ≤ (N:ℝ) ∧ (Usel k:ℝ) ≤ R^2 ∧
      2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧ D k ≤ 1/2 ∧ Δ k < 1/2) →
    (∀ k ≤ kmax, Usel k ≤ Usel 0) →
    2*Buffer 0+6*(N:ℝ) ≤ M →
    let f := fun y w => T*Φ y (w/M)
    let Vscale := fun k : ℕ => max 1 (Uband*(N:ℝ)/(Q k:ℝ))
    let Klarge := fun k : ℕ => 60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain*((Q k:ℝ)/(Uband*(N:ℝ)))^((2:ℝ)/3)+Ctail/(Usel k:ℝ))
    let Wphys := fun k : ℕ => (144*Usrc/(csrc*κ))*(R^2/(Q k:ℝ))
    let PointError := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+
      36*Usrc*R^2/(csrc*κ*(N:ℝ))
    let FamilyBound := fun (k : ℕ) (P : Finset (ℝ × ℤ)) =>
      let YP := P.image Prod.fst
      let Mass := Vscale k*Dtype*(2+θ*(Uband+1/lambda))*(YP.card:ℝ)*(M/(N:ℝ))*
        (1+Δtype k*Jsep)+(YP.card:ℝ)^2*Klarge k*T^εloss
      CF^12*2^11*((1+Real.log (Kmesh k))^12*Wphys k^6*
        (C*(Kmesh k:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*Mass)+
        ((P.card:ℝ)*PointError)^12)
    let CtailBand := 4*Usrc*(64/csrc)^2+192/csrc
    let ClowBand := (2*Usrc+csrc/32)*(3072/csrc)^2+3072/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    let Density := fun k => 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (512*R^2/(csrc*((Q k:ℝ)/768))+1))
    let Endpoint := (Y.card:ℝ)*(2*Buffer 0+6*(N:ℝ)+2*(n:ℝ))
    ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
    (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
    ∃ (Chunks : Finset (ℝ × ℤ)) (band : (ℝ × ℤ) → Option ℕ),
      (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/(N:ℝ)) ∧
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        (Y.card:ℝ)*Density k) ∧
      ((Chunks.filter (fun p => band p=none)).card:ℝ) ≤ (Y.card:ℝ)*Density kmax ∧
      let Selected := fun k => Chunks.filter (fun p => band p=some k)
      let Grid := fun (k : ℕ) (r : ℤ) =>
        ((Selected k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
      (∀ k r, (Grid k r).card ≤ (Selected k).card ∧ (Grid k r).image Prod.fst ⊆ Y) ∧
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),(𝐞 (f y j):ℂ)‖)^12 ≤
        2^11*(((kmax:ℝ)+2)^11*
          (((n:ℝ)*(Y.card:ℝ)*Density kmax)^12+
            (8:ℝ)^11*∑ k∈Finset.range (kmax+1),
              ∑ r∈Finset.Ico (0:ℤ) 8, FamilyBound k (Grid k r))+
            Endpoint^12)
 := by
  classical
  intro κ L θ
  obtain ⟨CF,C,Dtype,hCF,hC,hDtype,hcore⟩ :=
    eventually_double_difference_direct_residue_grid_moment hcsrc hUsrc hσ hεloss
  refine ⟨CF,C,Dtype,hCF,hC,hDtype,?_⟩
  filter_upwards [hcore] with T hcoreT
  intro Fsrc rshift sshift Y n N Qbase kmax Kmesh Usel R Jsep d Wmax M δ Bcut Bselect
    hK hNlink hd hw hwcap hsmallShift hT hMtwo hN hδ hR hRM hJsep hJM hNM hwJ
    hy hsepY hshifts hreg hlower hjets htests hnegative Φ hmodels
    hscale hfourBuffer hfourBudget hquadBudget hBcut hBselectSize hcutMargin hscaleTen hNsqM
    Q hQbase hQmax Cphys c J B hsmall hNR hRN hNcube hNtwo hanchorBudget
    lambda Uband hUbandCap NarrowCap Cap μ₀ U₀ C₂ C₃ Ct Cc Ccurv Kres Esize Dbase Tbase
    hsize hBsize Lunit Gamma Cthird Cpack Cfirst Cgap Cmain Ctail
    Δtype Δ D Buffer hvalid hUmax hroom f Vscale Klarge Wphys PointError FamilyBound
    CtailBand ClowBand CerrorBand Density Endpoint A Bint hA hab hB
  have hn : 0 < n := by omega
  have hM : 0 < M := by linarith only [hMtwo]
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hBuffer0 : 0 ≤ Buffer 0 := by dsimp only [Buffer]; positivity
  obtain ⟨Chunks,anchor,band,za,hphase,hdeep₀,hcardChunks,hroots,hbands,hcounts,htail,
      hReduction₀⟩ :=
    double_difference_phase_subinterval_dyadic_band_reduction Y Fsrc rshift sshift
      n N Qbase kmax hNlink hcsrc hUsrc hn hd hwcap hsmallShift hshifts hy hT hM hRp
      hreg hjets hlower hnegative hscale hQbase hQmax hBuffer0
      (show (0:ℝ) ≤ 0 by rfl) (by simpa only [add_zero] using hroom)
      A Bint hA hab hB
  have hdeep p (hp : p∈Chunks) :
      (n:ℝ)*p.2∈Icc (M+Buffer 0+4*(N:ℝ)) (2*M-Buffer 0-(N:ℝ)) := by
    simpa only [add_zero,sub_zero] using hdeep₀ p hp
  let Selected := fun k => Chunks.filter (fun p => band p=some k)
  let Grid := fun (k : ℕ) (r : ℤ) =>
    ((Selected k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
  let BandSum := fun k => ∑ p∈Selected k,
    ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),(𝐞 (f p.1 j):ℂ)‖
  have hBufferMono k (hk : k ≤ kmax) : Buffer k ≤ Buffer 0 := by
    have hu : (Usel k:ℝ) ≤ Usel 0 := by exact_mod_cast hUmax k hk
    exact add_le_add (add_le_add
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hu (by norm_num)) hκ.le)
        (Nat.cast_nonneg _)) le_rfl) le_rfl
  have hGridCard k r : (Grid k r).card ≤ (Selected k).card :=
    Finset.card_image_le.trans (Finset.card_filter_le _ _)
  have hGridPhase k r : (Grid k r).image Prod.fst ⊆ Y := by
    intro y hyGrid
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hyGrid
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact hphase q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
  have hBand k (hk : k ≤ kmax) :
      (BandSum k)^12 ≤ (8:ℝ)^11*∑ r∈Finset.Ico (0:ℤ) 8,FamilyBound k (Grid k r) := by
    obtain ⟨hfullmesh,hmesh,hUref,hselectedWrap,hRQ,hselectedUpper,hQN,hUR,
      hminscale,hD,hΔ⟩ := hvalid k hk
    have hQp : 0 < Q k := by
      dsimp only [Q]
      exact Nat.mul_pos (by omega) (by positivity)
    let : NeZero (Kmesh k) := ⟨Nat.ne_of_gt (hK k)⟩
    have hSelY p (hp : p∈Selected k) : p.1∈Y := hphase p (Finset.mem_filter.mp hp).1
    have hSelDeep p (hp : p∈Selected k) :
        (n:ℝ)*p.2∈Icc (M+Buffer k+4*(N:ℝ)) (2*M-Buffer k-(N:ℝ)) := by
      have hh := hdeep p (Finset.mem_filter.mp hp).1
      have hb := hBufferMono k hk
      constructor <;> linarith only [hh.1,hh.2,hb]
    have hSelAnchors p (hp : p∈Selected k) :
        |za p 0-((n:ℝ)*p.2-2*(N:ℝ))| ≤ (N:ℝ)/16 ∧
        iteratedDeriv 2 (f p.1) (za p 0)/2=(anchor p 0:ℝ) ∧
        768*(anchor p 0).den ≤ Q k ∧
        24576*R^2 ≤ csrc*(Q k:ℝ)*(anchor p 0).den := by
      obtain ⟨hpC,hpk⟩ := Finset.mem_filter.mp hp
      have hr := hroots p hpC 0
      have hb := hbands p hpC
      rw [hpk] at hb
      exact ⟨by simpa only [ite_true] using hr.2.1,hr.1,(hb.2 0).1,(hb.2 0).2⟩
    let Lsrc := fun (r : ℤ) (p : ℝ × ℤ) => r*(n:ℤ)+(N:ℤ)*p.2+2*(N:ℤ)
    let W := fun r : ℤ => ∑ p∈Grid k r,
      ‖∑ j∈Finset.Ioc (Lsrc r p) (Lsrc r p+n),(𝐞 (f p.1 j):ℂ)‖
    have hW r : 0 ≤ W r := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have hgridMoment r : (W r)^12 ≤ FamilyBound k (Grid k r) := by
      exact hcoreT (Selected k) Fsrc rshift sshift (fun p => za p 0)
        n (Q k) (Kmesh k) N R Jsep r
        (d:=d) (Wmax:=Wmax) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
        (Usel k) (fun p => anchor p 0) hNlink
        hd hw hwcap hsmallShift hT hM hδ hQp hUbandCap
        (fun p hp => hy p.1 (hSelY p hp))
        (by simpa only [Buffer,Cphys,show σ*(σ+1)+1+2=σ*(σ+1)+3 by ring] using hSelDeep)
        hreg hlower hjets htests hnegative hMtwo hN
        hJsep hJM hNM hwJ hmesh hfourBuffer hfourBudget hquadBudget hfullmesh
        (fun p hp q hq hne => hsepY p.1 (hSelY p hp) q.1 (hSelY q hq) hne)
        (by
          intro y hySel
          obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hySel
          exact hshifts p.1 (hSelY p hp))
        (fun p hp => hmodels p.1 (hSelY p hp)) hSelAnchors
        hR hRM hscale hBcut hUref hBselectSize hcutMargin hselectedWrap hRQ
        hselectedUpper hscaleTen hQN hNsqM hUR
        hsmall hNR hRN hNcube hminscale hNtwo hanchorBudget hsize hD hΔ hBsize
    have hsum := (eight_grid_exact_selected_transport (Selected k) Y n N (Q k) hNlink hN
      (fun y w => iteratedDeriv 2 (f y) w/2) (fun y j => (𝐞 (f y j):ℂ))
      (fun p => anchor p 0) (fun p => za p 0) hSelY hSelDeep hSelAnchors).2
    have hsum' : BandSum k=∑ r∈Finset.Ico (0:ℤ) 8,W r := hsum
    have hholder := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (Finset.Ico (0:ℤ) 8)
      (f:=W) (p:=(12:ℝ)) (by norm_num) (fun r _ => hW r)
    have hp : (BandSum k)^12 ≤ (8:ℝ)^11*∑ r∈Finset.Ico (0:ℤ) 8,(W r)^12 := by
      rw [hsum']
      norm_num only [Int.card_Ico,Int.reduceSub,Int.reduceToNat,Nat.cast_ofNat,
        show (12:ℝ)-1=11 by norm_num,Real.rpow_ofNat] at hholder
      simpa only [show (8:ℝ)^11=8589934592 by norm_num] using hholder
    exact hp.trans (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun r _ => hgridMoment r)) (by norm_num))
  refine ⟨Chunks,band,hcardChunks,hcounts,htail,?_⟩
  intro SelectedOut GridOut
  refine ⟨fun k r => ⟨hGridCard k r,hGridPhase k r⟩,?_⟩
  have hsum : (∑ k∈Finset.range (kmax+1),(BandSum k)^12) ≤
      (8:ℝ)^11*∑ k∈Finset.range (kmax+1),
        ∑ r∈Finset.Ico (0:ℤ) 8,FamilyBound k (Grid k r) := by
    calc
      _ ≤ ∑ k∈Finset.range (kmax+1),(8:ℝ)^11*
          ∑ r∈Finset.Ico (0:ℤ) 8,FamilyBound k (Grid k r) :=
        Finset.sum_le_sum (fun k hk => hBand k (by
          have hh := Finset.mem_range.mp hk
          omega))
      _ = _ := by rw [Finset.mul_sum]
  have hReduction :
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),(𝐞 (f y j):ℂ)‖)^12 ≤
        2^11*(((kmax:ℝ)+2)^11*
          (((n:ℝ)*(Y.card:ℝ)*Density kmax)^12+
            ∑ k∈Finset.range (kmax+1),(BandSum k)^12)+Endpoint^12) := by
    simpa only [mul_zero,add_zero] using hReduction₀
  exact hReduction.trans (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum) (by positivity))
      le_rfl) (by norm_num))

private theorem double_difference_clamped_triangular_monomials
    {Y M N R Q Jsep c U θ D Cdelta delta : ℝ}
    (hY : 0 ≤ Y) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q)
    (hJ : 0 ≤ Jsep) (hc : 0 < c) (hU : 0 < U) (hθ : 0 ≤ θ)
    (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta) (hd : 0 ≤ delta)
    (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hband : U*M/(N*R^2) ≤ 1) :
    let H := U*M/(N*R^2)
    let lambda := c*M/(2*N*R^2)
    let V := max 1 (H*N/Q)
    let Ctri := 2+θ*(1+2*U/c)
    (Y^10*M^10*N^2*R^8/Q^14)*
      (V*D*(2+θ*(H+1/lambda))*Y*(M/N)*(1+delta*Jsep)) ≤
      Ctri*D*(Y^11*M^10*N^2/(U*R^4)+Y^11*M^11*N^2/R^7+
        Cdelta*Y^11*Jsep*M^10/(U*R^2)+Cdelta*Y^11*Jsep*M^11/R^5) := by
  intro H lambda V Ctri
  have hQ : 0 < Q := hR.trans_le hRQ
  have hH : 0 < H := by dsimp only [H]; positivity
  have hLam : 0 < lambda := by dsimp only [lambda]; positivity
  have hCtri : 0 ≤ Ctri := by dsimp only [Ctri]; positivity
  have hV : 0 ≤ V := zero_le_one.trans (le_max_left _ _)
  have hprod : 0 ≤ H*N/Q := by positivity
  have hVupper : V ≤ 1+H*N/Q := max_le (by linarith only [hprod]) (by linarith)
  have hrecip : 1/lambda=(2*U/c)/H := by dsimp only [lambda,H]; field_simp
  have hInv : 1 ≤ 1/H := (le_div_iff₀ hH).mpr (by simpa only [one_mul] using hband)
  have hFactor : 2+θ*(H+1/lambda) ≤ Ctri/H := by
    rw [hrecip]
    calc
      _ ≤ 2/H+θ*(1/H+(2*U/c)/H) :=
        add_le_add ((le_div_iff₀ hH).mpr (by nlinarith only [show H ≤ 1 from hband]))
          (mul_le_mul_of_nonneg_left (add_le_add (hband.trans hInv) le_rfl) hθ)
      _ = _ := by dsimp only [Ctri]; ring
  have hCost : V*(2+θ*(H+1/lambda)) ≤ Ctri*(1/H+N/Q) := by
    calc
      _ ≤ (1+H*N/Q)*(Ctri/H) :=
        mul_le_mul hVupper hFactor (by positivity) (by positivity)
      _ = _ := by field_simp
  let Coeff := Ctri*D
  have hCoeff : 0 ≤ Coeff := mul_nonneg hCtri hD
  have hdecay (p : ℕ) : 1/Q^p ≤ 1/R^p :=
    one_div_le_one_div_of_le (pow_pos hR p) (pow_le_pow_left₀ hR.le hRQ p)
  have h0 : R^10/Q^14 ≤ 1/R^4 := by
    calc
      _ = R^10*(1/Q^14) := by ring
      _ ≤ R^10*(1/R^14) := mul_le_mul_of_nonneg_left (hdecay 14) (by positivity)
      _ = _ := by field_simp
  have h1 : R^8/Q^15 ≤ 1/R^7 := by
    calc
      _ = R^8*(1/Q^15) := by ring
      _ ≤ R^8*(1/R^15) := mul_le_mul_of_nonneg_left (hdecay 15) (by positivity)
      _ = _ := by field_simp
  have h2 : R^12/Q^14 ≤ 1/R^2 := by
    calc
      _ = R^12*(1/Q^14) := by ring
      _ ≤ R^12*(1/R^14) := mul_le_mul_of_nonneg_left (hdecay 14) (by positivity)
      _ = _ := by field_simp
  have h3 : R^10/Q^15 ≤ 1/R^5 := by
    calc
      _ = R^10*(1/Q^15) := by ring
      _ ≤ R^10*(1/R^15) := mul_le_mul_of_nonneg_left (hdecay 15) (by positivity)
      _ = _ := by field_simp

  let A₀ := Coeff*Y^11*M^10*N^2/U
  let A₁ := Coeff*Y^11*M^11*N^2
  let A₂ := Coeff*Cdelta*Y^11*Jsep*M^10/U
  let A₃ := Coeff*Cdelta*Y^11*Jsep*M^11
  have hA₀ : 0 ≤ A₀ := by dsimp only [A₀]; positivity
  have hA₁ : 0 ≤ A₁ := by dsimp only [A₁]; positivity
  have hA₂ : 0 ≤ A₂ := by dsimp only [A₂]; positivity
  have hA₃ : 0 ≤ A₃ := by dsimp only [A₃]; positivity
  calc
    _ = (Y^10*M^10*N^2*R^8/Q^14)*
        ((V*(2+θ*(H+1/lambda)))*D*Y*(M/N)*(1+delta*Jsep)) := by ring
    _ ≤ (Y^10*M^10*N^2*R^8/Q^14)*
        ((Ctri*(1/H+N/Q))*D*Y*(M/N)*(1+(Cdelta*R^2/N^2)*Jsep)) := by
      gcongr
    _ = A₀*(R^10/Q^14)+A₁*(R^8/Q^15)+A₂*(R^12/Q^14)+A₃*(R^10/Q^15) := by
      dsimp only [A₀,A₁,A₂,A₃,Coeff,H]
      field_simp
      ring
    _ ≤ A₀*(1/R^4)+A₁*(1/R^7)+A₂*(1/R^2)+A₃*(1/R^5) :=
      add_le_add (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left h0 hA₀)
        (mul_le_mul_of_nonneg_left h1 hA₁))
        (mul_le_mul_of_nonneg_left h2 hA₂))
        (mul_le_mul_of_nonneg_left h3 hA₃)
    _ = _ := by dsimp only [A₀,A₁,A₂,A₃,Coeff]; ring

private theorem double_difference_clamped_large_monomial
    {Y M N R Q H Uref C₀ Cmain Ctail B : ℝ}
    (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q)
    (hH : 0 < H) (hHcap : H ≤ 1) (hC : 0 ≤ C₀)
    (hmain : 0 ≤ Cmain) (htail : 0 ≤ Ctail) (hB : 0 < B)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ Uref) :
    (Y^10*M^10*N^2*R^8/Q^14)*
      (Y^2*(C₀*H^2*(R^8/N^4)*
        (Cmain*(Q/(H*N))^((2:ℝ)/3)+Ctail/Uref))) ≤
      C₀*(Cmain+2*B*Ctail)*(Y^12*M^10*R^2/N^2)*
        (R/N)^((2:ℝ)/3)*H^((4:ℝ)/3) := by
  have hQ : 0 < Q := hR.trans_le hRQ
  obtain ⟨hU,hUinv⟩ := physical_reference_reciprocal_bound hN hQ hB hUlower
  have hHpow : H^2 ≤ H^((4:ℝ)/3) := by
    simpa only [Real.rpow_ofNat] using
      Real.rpow_le_rpow_of_exponent_ge hH hHcap (by norm_num : (4:ℝ)/3 ≤ 2)
  have hcancel : H^2*(Q/(H*N))^((2:ℝ)/3)=
      H^((4:ℝ)/3)*(Q/N)^((2:ℝ)/3) := by
    have hsum : H^2=H^((4:ℝ)/3)*H^((2:ℝ)/3) := by
      rw [←Real.rpow_add hH]
      norm_num
    rw [show Q/(H*N)=(Q/N)/H by ring,Real.div_rpow (by positivity) hH.le,hsum]
    field_simp
  have hCost : H^2*(Cmain*(Q/(H*N))^((2:ℝ)/3)+Ctail/Uref) ≤
      (Cmain+2*B*Ctail)*H^((4:ℝ)/3)*(Q/N)^((2:ℝ)/3) := by
    have htailInv : Ctail/Uref ≤ Ctail*(2*B*(Q/N)^((2:ℝ)/3)) := by
      simpa only [div_eq_mul_inv,one_div,one_mul] using mul_le_mul_of_nonneg_left hUinv htail
    calc
      _ = Cmain*(H^2*(Q/(H*N))^((2:ℝ)/3))+H^2*(Ctail/Uref) := by ring
      _ ≤ Cmain*(H^((4:ℝ)/3)*(Q/N)^((2:ℝ)/3))+
          H^((4:ℝ)/3)*(Ctail*(2*B*(Q/N)^((2:ℝ)/3))) := by
        rw [hcancel]
        exact add_le_add le_rfl (mul_le_mul hHpow htailInv (by positivity) (by positivity))
      _ = _ := by ring
  have hdecay : R^16*(Q/N)^((2:ℝ)/3)/Q^14 ≤ R^2*(R/N)^((2:ℝ)/3) := by
    calc
      _ = R^16*((Q/N)^((2:ℝ)/3)/Q^14) := by ring
      _ ≤ R^16*((R/N)^((2:ℝ)/3)/R^14) :=
        mul_le_mul_of_nonneg_left
          (physical_denominator_rpow_decay 14 hR hRQ hN (by norm_num)) (by positivity)
      _ = _ := by field_simp

  let A := C₀*(Cmain+2*B*Ctail)*(Y^12*M^10/N^2)*H^((4:ℝ)/3)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  calc
    _ = (C₀*Y^12*M^10*R^16/(N^2*Q^14))*
        (H^2*(Cmain*(Q/(H*N))^((2:ℝ)/3)+Ctail/Uref)) := by
      field_simp
    _ ≤ (C₀*Y^12*M^10*R^16/(N^2*Q^14))*
        ((Cmain+2*B*Ctail)*H^((4:ℝ)/3)*(Q/N)^((2:ℝ)/3)) :=
      mul_le_mul_of_nonneg_left hCost (by positivity)
    _ = A*(R^16*(Q/N)^((2:ℝ)/3)/Q^14) := by dsimp only [A]; ring
    _ ≤ A*(R^2*(R/N)^((2:ℝ)/3)) := mul_le_mul_of_nonneg_left hdecay hA
    _ = _ := by dsimp only [A]; ring

private theorem double_difference_selected_grid_family_monomials
    {Y Z P M N R Q K Uref Jsep c U θ D Cdelta delta C₀ Cmain Ctail B Cmesh Ccard L T ε : ℝ}
    (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hZY : Z ≤ Y) (hP : 0 ≤ P)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q) (hK : 0 < K)
    (hJ : 0 ≤ Jsep) (hc : 0 < c) (hU : 0 < U) (hθ : 0 ≤ θ)
    (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta) (hd : 0 ≤ delta)
    (hC : 0 ≤ C₀) (hmain : 0 ≤ Cmain) (htail : 0 ≤ Ctail) (hB : 0 < B)
    (hCm : 0 < Cmesh) (hT : 1 ≤ T) (hε : 0 ≤ ε)
    (hQN : Q ≤ N) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hmesh : K ≤ Cmesh*Q*N/R^2)
    (hcard : P ≤ Ccard*Y*M*R^2/(N*Q^2)*L)
    (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hband : U*M/(N*R^2) ≤ 1)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ Uref) :
    let H := U*M/(N*R^2)
    let lambda := c*M/(2*N*R^2)
    let V := max 1 (H*N/Q)
    let Ctri := 2+θ*(1+2*U/c)
    (R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10*
      (V*D*(2+θ*(H+1/lambda))*Z*(M/N)*(1+delta*Jsep)+
        Z^2*(C₀*H^2*(R^8/N^4)*
          (Cmain*(Q/(H*N))^((2:ℝ)/3)+Ctail/Uref))*T^ε) ≤
      (Cmesh^12*Cmesh^ε*(2*Ccard)^10)*T^(2*ε)*L^10*
        (Ctri*D*(Y^11*M^10*N^2/(U*R^4)+Y^11*M^11*N^2/R^7+
          Cdelta*Y^11*Jsep*M^10/(U*R^2)+Cdelta*Y^11*Jsep*M^11/R^5)+
          C₀*(Cmain+2*B*Ctail)*(Y^12*M^10*R^2/N^2)*
            (R/N)^((2:ℝ)/3)*H^((4:ℝ)/3)) := by
  intro H lambda V Ctri
  have hQ := hR.trans_le hRQ
  have hH : 0 < H := by dsimp only [H]; positivity
  have hLam : 0 < lambda := by dsimp only [lambda]; positivity
  have hV : 0 ≤ V := zero_le_one.trans (le_max_left _ _)
  have hUref := (physical_reference_reciprocal_bound hN hQ hB hUlower).1
  have hTp := zero_lt_one.trans_le hT
  have hTpow : 1 ≤ T^ε := Real.one_le_rpow hT hε
  let Tri := V*D*(2+θ*(H+1/lambda))*Y*(M/N)*(1+delta*Jsep)
  let Pair := Y^2*(C₀*H^2*(R^8/N^4)*
    (Cmain*(Q/(H*N))^((2:ℝ)/3)+Ctail/Uref))
  let Cpref := Cmesh^12*Cmesh^ε*(2*Ccard)^10
  let Physical := Y^10*M^10*N^2*R^8/Q^14
  have hTri : 0 ≤ Tri := by dsimp only [Tri]; positivity
  have hPair : 0 ≤ Pair := by dsimp only [Pair]; positivity
  have hCpref : 0 ≤ Cpref := by dsimp only [Cpref]; positivity
  have hPhysical : 0 ≤ Physical := by dsimp only [Physical]; positivity
  have hmass :
      V*D*(2+θ*(H+1/lambda))*Z*(M/N)*(1+delta*Jsep)+
        Z^2*(C₀*H^2*(R^8/N^4)*
          (Cmain*(Q/(H*N))^((2:ℝ)/3)+Ctail/Uref))*T^ε ≤ (Tri+Pair)*T^ε := by
    calc
      _ ≤ Tri+Pair*T^ε := by dsimp only [Tri,Pair]; gcongr
      _ ≤ Tri*T^ε+Pair*T^ε :=
        add_le_add (le_mul_of_one_le_right hTri hTpow) le_rfl
      _ = _ := (add_mul _ _ _).symm
  have hpref := selected_band_mesh_cardinality_prefactor_bound
    hN hR hQ hK hP hCm hε hQN hNR hNT hmesh hcard
  have htri := double_difference_clamped_triangular_monomials
    hY hM hN hR hRQ hJ hc hU hθ hD hCd hd hdelta hband
  have hlarge := double_difference_clamped_large_monomial
    (Y:=Y) (M:=M) hN hR hRQ hH hband hC hmain htail hB hUlower
  have hmonomial :
      Physical*(Tri+Pair) ≤
        Ctri*D*(Y^11*M^10*N^2/(U*R^4)+Y^11*M^11*N^2/R^7+
          Cdelta*Y^11*Jsep*M^10/(U*R^2)+Cdelta*Y^11*Jsep*M^11/R^5)+
          C₀*(Cmain+2*B*Ctail)*(Y^12*M^10*R^2/N^2)*
            (R/N)^((2:ℝ)/3)*H^((4:ℝ)/3) := by
    rw [mul_add]
    exact add_le_add htri hlarge
  have hTproduct : T^ε*T^ε=T^(2*ε) := by
    rw [←Real.rpow_add hTp]
    apply congrArg (fun x : ℝ => T^x)
    ring
  calc
    _ ≤ (Cpref*T^ε*L^10*Physical)*((Tri+Pair)*T^ε) :=
      mul_le_mul hpref hmass (by positivity) (by positivity)
    _ = Cpref*T^(2*ε)*L^10*(Physical*(Tri+Pair)) := by
      calc
        _ = Cpref*(T^ε*T^ε)*L^10*(Physical*(Tri+Pair)) := by ring
        _ = _ := by rw [hTproduct]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmonomial (by positivity)

private theorem double_difference_actual_selected_grid_family_monomials
    (Chunks : Finset (ℝ × ℤ)) (Y : Finset ℝ)
    (band : (ℝ × ℤ) → Option ℕ) (Qbase kmax : ℕ)
    (Kmesh Usel : ℕ → ℕ) (delta : ℕ → ℝ)
    {M N R Jsep c U θ D Cdelta C₀ Cmain Ctail B Cmesh Cbase Cdensity L T ε : ℝ}
    (hQbase : 0 < Qbase) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hJ : 0 ≤ Jsep) (hc : 0 < c) (hU : 0 < U) (hθ : 0 ≤ θ)
    (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta) (hC : 0 ≤ C₀)
    (hmain : 0 ≤ Cmain) (htail : 0 ≤ Ctail) (hB : 0 < B)
    (hCm : 0 < Cmesh) (hDensity : 0 ≤ Cdensity) (hL : 1 ≤ L)
    (hT : 1 ≤ T) (hε : 0 ≤ ε) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hbase : (Qbase:ℝ) ≤ Cbase*R)
    (hchunks : (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/N))
    (hband : U*M/(N*R^2) ≤ 1) :
    let Q := fun k : ℕ => Qbase*2^k
    let Selected := fun k => Chunks.filter (fun p => band p=some k)
    let Grid := fun (k : ℕ) (r : ℤ) =>
      ((Selected k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
    (∀ j ≤ kmax, ((Chunks.filter (fun p => band p=some (j+1))).card:ℝ) ≤
      (Y.card:ℝ)*(Cdensity*M*R^2/(N*(Q j:ℝ)^2)*L)) →
    (∀ k r, (Grid k r).image Prod.fst ⊆ Y) →
    (∀ k ≤ kmax, 0 < Kmesh k ∧ R ≤ (Q k:ℝ) ∧ (Q k:ℝ) ≤ N ∧
      (Kmesh k:ℝ) ≤ Cmesh*(Q k:ℝ)*N/R^2 ∧
      0 ≤ delta k ∧ delta k ≤ Cdelta*R^2/N^2 ∧
      (N/(Q k:ℝ))^((2:ℝ)/3)/(2*B) ≤ (Usel k:ℝ)) →
    let H := U*M/(N*R^2)
    let lambda := c*M/(2*N*R^2)
    let Ctri := 2+θ*(1+2*U/c)
    let Ccard := 16*Cbase^2+8*Cdensity
    ∀ k ≤ kmax, ∀ r : ℤ,
      let Z := (((Grid k r).image Prod.fst).card:ℝ)
      let P := ((Grid k r).card:ℝ)
      let V := max 1 (H*N/(Q k:ℝ))
      (R^2/(Q k:ℝ))^6*(Kmesh k:ℝ)^((12:ℝ)+ε)*(2*P)^10*
        (V*D*(2+θ*(H+1/lambda))*Z*(M/N)*(1+delta k*Jsep)+
          Z^2*(C₀*H^2*(R^8/N^4)*
            (Cmain*((Q k:ℝ)/(H*N))^((2:ℝ)/3)+Ctail/(Usel k:ℝ)))*T^ε) ≤
        (Cmesh^12*Cmesh^ε*(2*Ccard)^10)*T^(2*ε)*L^10*
          (Ctri*D*((Y.card:ℝ)^11*M^10*N^2/(U*R^4)+(Y.card:ℝ)^11*M^11*N^2/R^7+
            Cdelta*(Y.card:ℝ)^11*Jsep*M^10/(U*R^2)+
              Cdelta*(Y.card:ℝ)^11*Jsep*M^11/R^5)+
            C₀*(Cmain+2*B*Ctail)*((Y.card:ℝ)^12*M^10*R^2/N^2)*
              (R/N)^((2:ℝ)/3)*H^((4:ℝ)/3))
 := by
  classical
  intro Q Selected Grid hbands hphase hvalid H lambda Ctri Ccard k hk r Z P V
  have hgrid j (_hj : j ≤ kmax) s :
      (Grid j s).card ≤ 2*(Chunks.filter (fun p => band p=some j)).card := by
    have hh : (Grid j s).card ≤ (Selected j).card :=
      Finset.card_image_le.trans (Finset.card_filter_le _ _)
    change (Grid j s).card ≤ 2*(Selected j).card
    omega
  have hcount := selected_band_grid_cardinality_bound Chunks band Grid Qbase kmax
    hQbase (Nat.cast_nonneg Y.card) hM.le hN hDensity hL hbase hchunks hbands hgrid k hk r
  have hZ : 0 ≤ Z := Nat.cast_nonneg _
  have hP : 0 ≤ P := Nat.cast_nonneg _
  have hZY : Z ≤ Y.card := by
    dsimp only [Z]
    exact_mod_cast Finset.card_le_card (hphase k r)
  obtain ⟨hK,hRQ,hQN,hmesh,hd,hdelta,hUlower⟩ := hvalid k hk
  exact double_difference_selected_grid_family_monomials
    (Nat.cast_nonneg Y.card) hZ hZY hP hM hN hR hRQ (by exact_mod_cast hK)
    hJ hc hU hθ hD hCd hd hC hmain htail hB hCm hT hε hQN hNR hNT
    hmesh hcount hdelta hband hUlower

private theorem double_difference_actual_source_grid_monomials
    (Chunks : Finset (ℝ × ℤ)) (Y : Finset ℝ)
    (band : (ℝ × ℤ) → Option ℕ) (Qbase kmax : ℕ)
    (Kmesh Usel : ℕ → ℕ)
    {M N R Jsep c U θ D Cmain Ctail B Cmesh Cbase Cdensity L T ε : ℝ}
    (hQbase : 0 < Qbase) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hJ : 0 ≤ Jsep) (hc : 0 < c) (hU : 0 < U) (hθ : 0 ≤ θ)
    (hD : 0 ≤ D)
    (hmain : 0 ≤ Cmain) (htail : 0 ≤ Ctail) (hB : 0 < B)
    (hCm : 0 < Cmesh) (hDensity : 0 ≤ Cdensity) (hL : 1 ≤ L)
    (hT : 1 ≤ T) (hε : 0 ≤ ε) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hbase : (Qbase:ℝ) ≤ Cbase*R)
    (hchunks : (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/N))
    (hscale : T*N*R^2=M^3) (hband : U*T/M^2 ≤ 1) :
    let Q := fun k : ℕ => Qbase*2^k
    let Selected := fun k => Chunks.filter (fun p => band p=some k)
    let Grid := fun (k : ℕ) (r : ℤ) =>
      ((Selected k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
    (∀ j ≤ kmax, ((Chunks.filter (fun p => band p=some (j+1))).card:ℝ) ≤
      (Y.card:ℝ)*(Cdensity*M*R^2/(N*(Q j:ℝ)^2)*L)) →
    (∀ k r, (Grid k r).image Prod.fst ⊆ Y) →
    (∀ k ≤ kmax, 0 < Kmesh k ∧ R ≤ (Q k:ℝ) ∧ (Q k:ℝ) ≤ N ∧
      (Q k:ℝ)*N ≤ (Kmesh k:ℝ)*R^2 ∧
      (Kmesh k:ℝ) ≤ Cmesh*(Q k:ℝ)*N/R^2 ∧
      (N/(Q k:ℝ))^((2:ℝ)/3)/(2*B) ≤ (Usel k:ℝ)) →
    let H := U*T/M^2
    let lambda := c*T/(2*M^2)
    let μ₀ := c*T/(12*M^3)
    let U₀ := U*T/(2*M^3)
    let delta := fun k : ℕ =>
      (16*U₀/μ₀)*Real.sqrt (U₀*(Q k:ℝ)^3)*Real.sqrt (Kmesh k)/(6*(Kmesh k:ℝ)^2)
    let Cdelta := (16*U/c)*Real.sqrt ((U/2)*Cmesh)
    let C₀ := 60*588*(2*U/c)^2
    let Ctri := 2+θ*(1+2*U/c)
    let Ccard := 16*Cbase^2+8*Cdensity
    ∀ k ≤ kmax, ∀ r : ℤ,
      let Z := (((Grid k r).image Prod.fst).card:ℝ)
      let P := ((Grid k r).card:ℝ)
      let V := max 1 (H*N/(Q k:ℝ))
      (R^2/(Q k:ℝ))^6*(Kmesh k:ℝ)^((12:ℝ)+ε)*(2*P)^10*
        (V*D*(2+θ*(H+1/lambda))*Z*(M/N)*(1+delta k*Jsep)+
          Z^2*(60*588*(H/lambda)^2*H^2*(R^8/N^4)*
            (Cmain*((Q k:ℝ)/(H*N))^((2:ℝ)/3)+Ctail/(Usel k:ℝ)))*T^ε) ≤
        (Cmesh^12*Cmesh^ε*(2*Ccard)^10)*T^(2*ε)*L^10*
          (Ctri*D*((Y.card:ℝ)^11*M^10*N^2/(U*R^4)+(Y.card:ℝ)^11*M^11*N^2/R^7+
            Cdelta*(Y.card:ℝ)^11*Jsep*M^10/(U*R^2)+
              Cdelta*(Y.card:ℝ)^11*Jsep*M^11/R^5)+
            C₀*(Cmain+2*B*Ctail)*((Y.card:ℝ)^12*M^10*R^2/N^2)*
              (R/N)^((2:ℝ)/3)*H^((4:ℝ)/3))
 := by
  classical
  intro Q Selected Grid hbands hphase hvalid H lambda μ₀ U₀ delta Cdelta C₀ Ctri Ccard k hk r Z P V
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hTidentity : T=M^3/(N*R^2) :=
    (eq_div_iff (show N*R^2 ≠ 0 by positivity)).mpr (by nlinarith only [hscale])
  have hH : H=U*M/(N*R^2) := by
    dsimp only [H]
    rw [hTidentity]
    field_simp
  have hLam : lambda=c*M/(2*N*R^2) := by
    dsimp only [lambda]
    rw [hTidentity]
    field_simp
  have hratio : H/lambda=2*U/c := by
    dsimp only [H,lambda]
    field_simp
  have hCd : 0 ≤ Cdelta := by dsimp only [Cdelta]; positivity
  have hC : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  have hvalid' j (hj : j ≤ kmax) :
      0 < Kmesh j ∧ R ≤ (Q j:ℝ) ∧ (Q j:ℝ) ≤ N ∧
      (Kmesh j:ℝ) ≤ Cmesh*(Q j:ℝ)*N/R^2 ∧
      0 ≤ delta j ∧ delta j ≤ Cdelta*R^2/N^2 ∧
      (N/(Q j:ℝ))^((2:ℝ)/3)/(2*B) ≤ (Usel j:ℝ) := by
    obtain ⟨hK,hRQ,hQN,hmesh,hupper,hUlower⟩ := hvalid j hj
    have hKp : (0:ℝ) < Kmesh j := by exact_mod_cast hK
    have hd : 0 ≤ delta j := by dsimp only [delta,μ₀,U₀]; positivity
    have hdelta := positive_difference_source_type_spacing_bound
      (σ:=(1:ℝ)) (c:=c) (J:=U)
      (by norm_num) hc hU.le hTp hM hN hR (hR.trans_le hRQ) hKp hCm.le
      hscale hmesh hupper
    refine ⟨hK,hRQ,hQN,hupper,hd,?_,hUlower⟩
    simpa only [mul_one,one_mul] using hdelta
  have hband' : U*M/(N*R^2) ≤ 1 := by rw [←hH]; exact hband
  have hh := double_difference_actual_selected_grid_family_monomials
    Chunks Y band Qbase kmax Kmesh Usel delta
    hQbase hM hN hR hJ hc hU hθ hD hCd hC hmain htail hB hCm hDensity hL
    hT hε hNR hNT hbase hchunks hband' hbands hphase hvalid' k hk r
  rw [hratio]
  simpa only [←hH,←hLam] using hh

private theorem model_source_large_entry_coefficients_nonneg
    {σ δ : ℝ} (hσ : 0 < σ) (hδ₀ : 0 ≤ δ) :
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    0 ≤ Cmain ∧ 0 ≤ Ctail
 := by
  intro κ Cphys c J B C₂ C₃ Ct Cc Kres Lunit Gamma Cthird Cpack Cfirst Cgap Cmain Ctail
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hC₂ : 0 ≤ C₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ₀
  have hC₃ : 0 ≤ C₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ₀
  have hC₄ : 0 ≤ modelPhaseJetCoefficient σ 4+δ :=
    add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ₀
  have hRes : 0 ≤ quarticNonlinearResidualConstant σ δ := by
    dsimp only [quarticNonlinearResidualConstant]
    positivity
  have hRecip : 0 ≤ quarticReciprocalConstant σ δ := by
    dsimp only [quarticReciprocalConstant]
    positivity
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hCt : 0 ≤ Ct := by dsimp only [Ct]; positivity
  have hCc : 0 ≤ Cc := by dsimp only [Cc]; positivity
  have hKres : 0 ≤ Kres := by dsimp only [Kres]; positivity
  have hLunit : 0 < Lunit := by dsimp only [Lunit]; positivity
  have hGamma : 0 ≤ Gamma := by dsimp only [Gamma]; positivity
  have hCthird : 0 ≤ Cthird := by dsimp only [Cthird]; positivity
  have hCpack : 0 ≤ Cpack := by dsimp only [Cpack]; positivity
  have hCgap : 0 ≤ Cgap := by dsimp only [Cgap]; positivity
  exact ⟨model_source_large_entry_main_coefficient_nonneg hσ hδ₀,
    by dsimp only [Ctail]; positivity⟩

private theorem completed_family_logarithmic_power_bound
    {CF C Cap W Cpref CK Ce Tp L Main E Perror Qpref Klog : ℝ}
    (hC : 0 ≤ C) (hCap : 0 ≤ Cap) (hPref : 0 ≤ Cpref)
    (hTp : 1 ≤ Tp) (hL : 1 ≤ L)
    (hMain : 0 ≤ Main) (hPerror : 0 ≤ Perror)
    (hKlog : 0 ≤ Klog) (hlog : Klog ≤ CK*L)
    (hnum : Qpref ≤ Cpref*Tp*L^10*Main)
    (herror : Perror ≤ Ce*E*L) :
    CF^12*2^11*(Klog^12*W^6*(C*Cap^11*Qpref)+Perror^12) ≤
      (CF^12*2^11*(C*Cap^11*W^6*CK^12*Cpref+Ce^12))*
        Tp*L^22*(Main+E^12)
 := by
  have hTnon : 0 ≤ Tp := zero_le_one.trans hTp
  have hLnon : 0 ≤ L := zero_le_one.trans hL
  have hlogPow : Klog^12 ≤ CK^12*L^12 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hKlog hlog 12
  let A := C*Cap^11*W^6*CK^12*Cpref
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hmainBound : Klog^12*W^6*(C*Cap^11*Qpref) ≤
      A*Tp*L^22*Main := by
    calc
      _ = (C*Cap^11*W^6)*Klog^12*Qpref := by ring
      _ ≤ (C*Cap^11*W^6)*Klog^12*(Cpref*Tp*L^10*Main) :=
        mul_le_mul_of_nonneg_left hnum (by positivity)
      _ ≤ (C*Cap^11*W^6)*(CK^12*L^12)*(Cpref*Tp*L^10*Main) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlogPow (by positivity)) (by positivity)
      _ = _ := by dsimp only [A]; ring
  have herrorBound : Perror^12 ≤ Ce^12*Tp*L^22*E^12 := by
    calc
      _ ≤ (Ce*E*L)^12 := pow_le_pow_left₀ hPerror herror 12
      _ = Ce^12*L^12*E^12 := by ring
      _ ≤ Ce^12*(Tp*L^22)*E^12 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (pow_le_pow_right₀ hL (show 12 ≤ 22 by omega)).trans
          (le_mul_of_one_le_left (by positivity) hTp)
      _ = _ := by ring
  calc
    _ ≤ CF^12*2^11*(A*Tp*L^22*Main+Ce^12*Tp*L^22*E^12) :=
      mul_le_mul_of_nonneg_left (add_le_add hmainBound herrorBound) (by positivity)
    _ ≤ CF^12*2^11*(A*Tp*L^22*(Main+E^12)+Ce^12*Tp*L^22*(Main+E^12)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity))
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hMain) (by positivity))
    _ = _ := by dsimp only [A]; ring

private theorem all_band_logarithmic_power_aggregation
    (kmax : ℕ) (Family : ℕ → ℤ → ℝ)
    {Cband Cfamily Cterminal Cendpoint Tp L Main E Term Endpoint X : ℝ}
    (hCband : 0 ≤ Cband) (hFamily : 0 ≤ Cfamily)
    (hMass : 0 ≤ Main) (hError : 0 ≤ E)
    (hLlog : 1 ≤ L) (hTpow : 1 ≤ Tp)
    (hTerm : 0 ≤ Term) (hEndpointNon : 0 ≤ Endpoint)
    (hbandCount : (kmax:ℝ)+2 ≤ Cband*L)
    (hfamily : ∀ k ≤ kmax, ∀ r : ℤ,
      Family k r ≤ Cfamily*Tp*L^22*(Main+E^12))
    (hterminal : Term ≤ Cterminal*E*L)
    (hendpoint : Endpoint ≤ Cendpoint*E) :
    X^12 ≤ 2^11*(((kmax:ℝ)+2)^11*
      (Term^12+(8:ℝ)^11*∑ k∈Finset.range (kmax+1),
        ∑ r∈Finset.Ico (0:ℤ) 8,Family k r)+Endpoint^12) →
    X^12 ≤ (2:ℝ)^11*
      (Cband^11*(Cterminal^12+(8:ℝ)^12*Cband*Cfamily)+Cendpoint^12)*
        Tp*L^36*(Main+E^12)
 := by
  classical
  have hTpowNon : 0 ≤ Tp := zero_le_one.trans hTpow
  have hLnon : 0 ≤ L := zero_le_one.trans hLlog
  let S := Main+E^12
  have hS : 0 ≤ S := add_nonneg hMass (pow_nonneg hError 12)
  have hES : E^12 ≤ S := le_add_of_nonneg_left hMass
  have hsum :
      (∑ k∈Finset.range (kmax+1),
        ∑ r∈Finset.Ico (0:ℤ) 8,Family k r) ≤
          (8*Cband*Cfamily)*Tp*L^23*S := by
    calc
      _ ≤ ∑ k∈Finset.range (kmax+1),∑ _r∈Finset.Ico (0:ℤ) 8,
          Cfamily*Tp*L^22*S :=
        Finset.sum_le_sum (fun k hk => Finset.sum_le_sum (fun r _ =>
          hfamily k (by have hh := Finset.mem_range.mp hk; omega) r))
      _ = ((kmax:ℝ)+1)*8*(Cfamily*Tp*L^22*S) := by
        simp only [Finset.sum_const,Finset.card_range,Int.card_Ico,Int.reduceSub,
          Int.reduceToNat,nsmul_eq_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
        ring
      _ ≤ (Cband*L)*8*(Cfamily*Tp*L^22*S) := by
        gcongr
        linarith only [hbandCount]
      _ = _ := by ring
  have hterminalPow :
      (Term)^12 ≤
        Cterminal^12*Tp*L^23*S := by
    calc
      _ ≤ (Cterminal*E*L)^12 :=
        pow_le_pow_left₀ (by positivity) hterminal 12
      _ = Cterminal^12*L^12*E^12 := by ring
      _ ≤ Cterminal^12*(Tp*L^23)*S := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact (pow_le_pow_right₀ hLlog (show 12 ≤ 23 by omega)).trans
            (le_mul_of_one_le_left (by positivity) hTpow)
        · exact hES
        · positivity
        · positivity
      _ = _ := by ring
  have hinside :
      (Term)^12+
        (8:ℝ)^11*∑ k∈Finset.range (kmax+1),
          ∑ r∈Finset.Ico (0:ℤ) 8,Family k r ≤
        (Cterminal^12+(8:ℝ)^12*Cband*Cfamily)*Tp*L^23*S := by
    calc
      _ ≤ Cterminal^12*Tp*L^23*S+
          (8:ℝ)^11*((8*Cband*Cfamily)*Tp*L^23*S) :=
        add_le_add hterminalPow (mul_le_mul_of_nonneg_left hsum (by norm_num))
      _ = _ := by ring
  have houter :
      ((kmax:ℝ)+2)^11*
        ((Term)^12+
          (8:ℝ)^11*∑ k∈Finset.range (kmax+1),
            ∑ r∈Finset.Ico (0:ℤ) 8,Family k r) ≤
        (Cband^11*(Cterminal^12+(8:ℝ)^12*Cband*Cfamily))*
          Tp*L^36*S := by
    calc
      _ ≤ (Cband*L)^11*
          ((Cterminal^12+(8:ℝ)^12*Cband*Cfamily)*Tp*L^23*S) := by
        exact (mul_le_mul_of_nonneg_left hinside (by positivity)).trans
          (mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (by positivity) hbandCount 11) (by positivity))
      _ = (Cband^11*(Cterminal^12+(8:ℝ)^12*Cband*Cfamily))*
          Tp*L^34*S := by ring
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hLlog (show 34 ≤ 36 by norm_num)) (by positivity)) hS
  have hendpointPow : Endpoint^12 ≤
      Cendpoint^12*Tp*L^36*S := by
    calc
      _ ≤ (Cendpoint*E)^12 :=
        pow_le_pow_left₀ hEndpointNon hendpoint 12
      _ = Cendpoint^12*E^12 := by ring
      _ ≤ (Cendpoint^12*(Tp*L^36))*S := by
        apply mul_le_mul
        · exact le_mul_of_one_le_right (by positivity)
            (one_le_mul_of_one_le_of_one_le hTpow (one_le_pow₀ hLlog))
        · exact hES
        · positivity
        · positivity
      _ = _ := by ring
  intro hwhole
  calc
    _ ≤ 2^11*(((kmax:ℝ)+2)^11*
        ((Term)^12+
          (8:ℝ)^11*∑ k∈Finset.range (kmax+1),
            ∑ r∈Finset.Ico (0:ℤ) 8,Family k r)+Endpoint^12) := hwhole
    _ ≤ 2^11*((Cband^11*(Cterminal^12+(8:ℝ)^12*Cband*Cfamily))*
        Tp*L^36*S+Cendpoint^12*Tp*L^36*S) :=
      mul_le_mul_of_nonneg_left (add_le_add houter hendpointPow) (by norm_num)
    _ = _ := by dsimp only [S]; ring

private theorem capped_terminal_density_error
    {M N R q Q n Y A L E Density : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hq : 0 < q)
    (hY : 0 ≤ Y) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hn : N=8*n) (hcap : (q/2)*min N (M/N) ≤ Q)
    (hDensity : Density ≤ A*M*R^2/(N*Q^2)*L)
    (hError : Y*M*R^2/N^2+Y*N^2*R^2/M ≤ E) :
    n*Y*Density ≤ (A/(2*q^2))*E*L := by
  have hnval : n=N/8 := by linarith only [hn]
  have hnnon : 0 ≤ n := by rw [hnval]; positivity
  have hQ : 0 < Q :=
    lt_of_lt_of_le (mul_pos (by positivity) (lt_min hN (div_pos hM hN))) hcap
  have hphysical := capped_terminal_physical_error (R:=R) hM hN
    (show 0 < q/2 by positivity) hcap
  calc
    _ ≤ n*Y*(A*M*R^2/(N*Q^2)*L) :=
      mul_le_mul_of_nonneg_left hDensity (mul_nonneg hnnon hY)
    _ = (A*Y/8)*(M*R^2/Q^2)*L := by rw [hnval]; field_simp
    _ ≤ (A*Y/8)*((1/(q/2)^2)*(M*R^2/N^2+N^2*R^2/M))*L :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hphysical (by positivity)) hL
    _ = (A/(2*q^2))*(Y*M*R^2/N^2+Y*N^2*R^2/M)*L := by
      field_simp
      ring
    _ ≤ (A/(2*q^2))*E*L :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hError (by positivity)) hL

private theorem double_difference_finite_source_power_bound
    {csrc Usrc κ θ Cphys εloss CF C Dtype Cmain Ctail Cap Bselect : ℝ}
    (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) (hκ : 0 < κ)
    (hθ : 0 ≤ θ) (hCphys : 0 ≤ Cphys) (hεloss : 0 ≤ εloss)
    (hC : 0 ≤ C) (hDtype : 0 ≤ Dtype) (hmain : 0 ≤ Cmain) (htail : 0 ≤ Ctail)
    (hCap : 0 ≤ Cap) (hBselect : 1 ≤ Bselect)
    (Chunks : Finset (ℝ × ℤ)) (Y : Finset ℝ) (band : (ℝ × ℤ) → Option ℕ)
    (n N Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ)
    {R Jsep M T Cbase Cmesh qcap X : ℝ}
    (hK : ∀ k, 0 < Kmesh k) (hNlink : N=8*n) (hNone : (1:ℝ) ≤ N)
    (hR : 1 ≤ R) (hJsep : 0 ≤ Jsep) (hNM : (N:ℝ) ≤ M)
    (hscale : T*(N:ℝ)*R^2=M^3) (hNR : (N:ℝ) ≤ R^2)
    (hUbandCap : Usrc*T/M^2 ≤ 1) (hTone : 1 ≤ T) (hMT : M ≤ T)
    (hQbase : 0 < Qbase) (hCm : 1 ≤ Cmesh) (hbase : (Qbase:ℝ) ≤ Cbase*R)
    (hklog : (kmax:ℝ) ≤ Real.log (N:ℝ)/Real.log 2) (hqcap : 0 < qcap) :
    let Q := fun k : ℕ => Qbase*2^k
    (qcap/2)*min (N:ℝ) (M/(N:ℝ)) ≤ (Q kmax:ℝ) →
    (∀ k ≤ kmax, R ≤ (Q k:ℝ) ∧ (Q k:ℝ) ≤ N ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      (Kmesh k:ℝ) ≤ Cmesh*(Q k:ℝ)*(N:ℝ)/R^2 ∧
      (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Usel k:ℝ)) →
    let Selected := fun k => Chunks.filter (fun p => band p=some k)
    let Grid := fun (k : ℕ) (r : ℤ) =>
      ((Selected k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
    let Uband := Usrc*T/M^2
    let CtailBand := 4*Usrc*(64/csrc)^2+192/csrc
    let ClowBand := (2*Usrc+csrc/32)*(3072/csrc)^2+3072/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    let Carg := 512*768/csrc
    let Cdensity := 128*CerrorBand*(3+Real.log (Carg+1))
    let Ccard := 16*Cbase^2+8*Cdensity
    let Cdelta := (16*Usrc/csrc)*Real.sqrt ((Usrc/2)*Cmesh)
    let Ctri := 2+θ*(1+2*Usrc/csrc)
    let C₀ := 60*588*(2*Usrc/csrc)^2
    let MassPower := Ctri*Dtype*
      ((Y.card:ℝ)^11*M^10*(N:ℝ)^2/(Usrc*R^4)+
        (Y.card:ℝ)^11*M^11*(N:ℝ)^2/R^7+
        Cdelta*(Y.card:ℝ)^11*Jsep*M^10/(Usrc*R^2)+
        Cdelta*(Y.card:ℝ)^11*Jsep*M^11/R^5)+
      C₀*(Cmain+2*Bselect*Ctail)*((Y.card:ℝ)^12*M^10*R^2/(N:ℝ)^2)*
        (R/(N:ℝ))^((2:ℝ)/3)*Uband^((4:ℝ)/3)
    let ErrorPower := (Y.card:ℝ)*M/Real.sqrt (N:ℝ)+
      (Y.card:ℝ)*M*R^2/(N:ℝ)^2+(Y.card:ℝ)*(N:ℝ)^2*R^2/M+
      (Y.card:ℝ)*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
    let Cpref := Cmesh^12*Cmesh^εloss*(2*Ccard)^10
    let Wconst := 144*Usrc/(csrc*κ)
    let CKlog := 3+Real.log (Cmesh+1)
    let Cerror := 8*(2*Real.sqrt 3*(1+Real.log 6)+72*Usrc/(csrc*κ))
    let Cfamily := CF^12*2^11*(C*Cap^11*Wconst^6*CKlog^12*Cpref+Cerror^12)
    let Cband := 2+1/Real.log 2
    let Cterminal := Cdensity/(2*qcap^2)
    let Cendpoint := 112/κ+2/(Cphys+2)+41/4
    let Ctotal := (2:ℝ)^11*
      (Cband^11*(Cterminal^12+(8:ℝ)^12*Cband*Cfamily)+Cendpoint^12)
    let lambda := csrc*T/(2*M^2)
    let μ₀ := csrc*T/(12*M^3)
    let U₀ := Usrc*T/(2*M^3)
    let Δtype := fun k : ℕ =>
      (16*U₀/μ₀)*Real.sqrt (U₀*(Q k:ℝ)^3)*Real.sqrt (Kmesh k)/(6*(Kmesh k:ℝ)^2)
    let Vscale := fun k : ℕ => max 1 (Uband*(N:ℝ)/(Q k:ℝ))
    let Klarge := fun k : ℕ => 60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain*((Q k:ℝ)/(Uband*(N:ℝ)))^((2:ℝ)/3)+Ctail/(Usel k:ℝ))
    let PointError := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+
      36*Usrc*R^2/(csrc*κ*(N:ℝ))
    let FamilyBound := fun (k : ℕ) (P : Finset (ℝ × ℤ)) =>
      let YP := P.image Prod.fst
      let Mass := Vscale k*Dtype*(2+θ*(Uband+1/lambda))*(YP.card:ℝ)*(M/(N:ℝ))*
        (1+Δtype k*Jsep)+(YP.card:ℝ)^2*Klarge k*T^εloss
      CF^12*2^11*((1+Real.log (Kmesh k))^12*(Wconst*(R^2/(Q k:ℝ)))^6*
        (C*(Kmesh k:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*Mass)+
        ((P.card:ℝ)*PointError)^12)
    let Density := fun k => 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (512*R^2/(csrc*((Q k:ℝ)/768))+1))
    let Buffer := fun k : ℕ => (56*(Usel k:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    let Endpoint := (Y.card:ℝ)*(2*Buffer 0+6*(N:ℝ)+2*(n:ℝ))
    (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/(N:ℝ)) →
    (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
      (Y.card:ℝ)*Density k) →
    (∀ k r, (Grid k r).image Prod.fst ⊆ Y) →
    X^12 ≤ 2^11*(((kmax:ℝ)+2)^11*(((n:ℝ)*(Y.card:ℝ)*Density kmax)^12+
      (8:ℝ)^11*∑ k∈Finset.range (kmax+1),
        ∑ r∈Finset.Ico (0:ℤ) 8,FamilyBound k (Grid k r))+Endpoint^12) →
    X^12 ≤ Ctotal*T^(2*εloss)*(1+Real.log T)^36*(MassPower+ErrorPower^12)
 := by
  classical
  intro Q hQcap hvalid Selected Grid Uband
    CtailBand ClowBand CerrorBand Carg Cdensity Ccard Cdelta Ctri C₀
    MassPower ErrorPower Cpref Wconst CKlog Cerror Cfamily Cband Cterminal Cendpoint Ctotal
    lambda μ₀ U₀ Δtype Vscale Klarge PointError FamilyBound Density Buffer Endpoint
    hchunks hbands hphase
  have hNp : (0:ℝ) < N := zero_lt_one.trans_le hNone
  have hM : 0 < M := hNp.trans_le hNM
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hT : 0 < T := zero_lt_one.trans_le hTone
  have hBp : 0 < Bselect := zero_lt_one.trans_le hBselect
  have hQp k : (0:ℝ) < Q k := by
    exact_mod_cast Nat.mul_pos hQbase (by positivity : 0 < 2^k)
  have hgrids k r : (Grid k r).card ≤ (Selected k).card ∧
      (Grid k r).image Prod.fst ⊆ Y :=
    ⟨Finset.card_image_le.trans (Finset.card_filter_le _ _),hphase k r⟩
  have hCarg : 0 ≤ Carg := by clear * - hcsrc; dsimp only [Carg]; positivity
  have hlogArg : 0 ≤ Real.log (Carg+1) := Real.log_nonneg (by linarith only [hCarg])
  have hDensity : 0 ≤ Cdensity := by
    clear * - hcsrc hUsrc hlogArg
    dsimp only [Cdensity,CerrorBand,CtailBand,ClowBand]
    positivity
  have hCKlog : 0 ≤ CKlog := by
    clear * - hCm
    have hh : 0 ≤ Real.log (Cmesh+1) := Real.log_nonneg (by linarith only [hCm])
    dsimp only [CKlog]
    positivity
  have hCband : 0 ≤ Cband := by
    clear * - hκ
    have hh : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp only [Cband]
    positivity
  have hCerror : 0 ≤ Cerror := by
    clear * - hUsrc hcsrc hκ
    have hh : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
    dsimp only [Cerror]
    positivity
  have hCterminal : 0 ≤ Cterminal := by clear * - hDensity hqcap; dsimp only [Cterminal]; positivity
  have hCendpoint : 0 ≤ Cendpoint := by clear * - hκ hCphys; dsimp only [Cendpoint]; positivity
  have hWconst : 0 ≤ Wconst := by clear * - hUsrc hcsrc hκ; dsimp only [Wconst]; positivity
  have hCpref : 0 ≤ Cpref := by clear * - hCm; dsimp only [Cpref]; positivity
  have hFamily : 0 ≤ Cfamily := by clear * - hC hCap hWconst hCpref; dsimp only [Cfamily]; positivity
  have hMass : 0 ≤ MassPower := by
    clear * - hDtype hθ hUsrc hcsrc hmain htail hBp hNp hRp hM hJsep hT
    dsimp only [MassPower,Ctri,Cdelta,C₀,Uband]
    positivity
  have hError : 0 ≤ ErrorPower := by clear * - hM hNp hRp; dsimp only [ErrorPower]; positivity
  let Llog := 1+Real.log T
  have hLlog : 1 ≤ Llog := by
    have hh := Real.log_nonneg hTone
    dsimp only [Llog]
    linarith only [hh]
  have hLnon : 0 ≤ Llog := zero_le_one.trans hLlog
  have hTpow : 1 ≤ T^(2*εloss) := Real.one_le_rpow hTone (by positivity)
  have hTpowNon : 0 ≤ T^(2*εloss) := zero_le_one.trans hTpow
  have hlogs k (hk : k ≤ kmax) :
      2+Real.log (Carg*R^2/(Q k:ℝ)+1) ≤
        (3+Real.log (Carg+1))*Llog ∧
      1+Real.log (Kmesh k) ≤ CKlog*Llog ∧
      (kmax:ℝ)+2 ≤ Cband*Llog := by
    obtain ⟨hRQ,hQN,_,hupper,_,_⟩ := hvalid k hk
    exact physical_band_logarithmic_bounds hCarg hCm hTone hR hRQ hQN hNR
      (hNM.trans hMT) (by exact_mod_cast hK k) hupper hklog
  have hDensityBound k (hk : k ≤ kmax) :
      Density k ≤ Cdensity*M*R^2/((N:ℝ)*(Q k:ℝ)^2)*Llog := by
    have harg : 512*R^2/(csrc*((Q k:ℝ)/768))=Carg*R^2/(Q k:ℝ) := by
      dsimp only [Carg]
      field_simp
    dsimp only [Density]
    rw [harg]
    calc
      _ ≤ 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
          ((3+Real.log (Carg+1))*Llog) :=
        mul_le_mul_of_nonneg_left (hlogs k hk).1 (by
          dsimp only [CerrorBand,CtailBand,ClowBand]
          positivity)
      _ = _ := by dsimp only [Cdensity]; ring
  have hcounts k (hk : k ≤ kmax) :
      ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        (Y.card:ℝ)*(Cdensity*M*R^2/((N:ℝ)*(Q k:ℝ)^2)*Llog) :=
    (hbands k hk).trans (mul_le_mul_of_nonneg_left
      (hDensityBound k hk) (Nat.cast_nonneg _))
  have hErrorSmall :
      (Y.card:ℝ)*M/Real.sqrt (N:ℝ)+(Y.card:ℝ)*M*R^2/(N:ℝ)^2 ≤ ErrorPower := by
    clear * - hM hNp hRp
    dsimp only [ErrorPower]
    exact (le_add_of_nonneg_right (by positivity)).trans
      (le_add_of_nonneg_right (by positivity))
  have hErrorTerminal :
      (Y.card:ℝ)*M*R^2/(N:ℝ)^2+(Y.card:ℝ)*(N:ℝ)^2*R^2/M ≤ ErrorPower := by
    clear * - hM hNp hRp
    dsimp only [ErrorPower]
    linarith only [show 0 ≤ (Y.card:ℝ)*M/Real.sqrt (N:ℝ) by positivity,
      show 0 ≤ (Y.card:ℝ)*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3) by positivity]
  have hErrorEndpoint :
      (Y.card:ℝ)*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3) ≤ ErrorPower := by
    clear * - hM hNp hRp
    dsimp only [ErrorPower]
    exact le_add_of_nonneg_left (by positivity)
  have hsumMass : 0 ≤ MassPower+ErrorPower^12 := add_nonneg hMass (pow_nonneg hError 12)
  have hfamily k (hk : k ≤ kmax) (r : ℤ) :
      FamilyBound k (Grid k r) ≤
        Cfamily*T^(2*εloss)*Llog^22*(MassPower+ErrorPower^12) := by
    let P := ((Grid k r).card:ℝ)
    let Z := (((Grid k r).image Prod.fst).card:ℝ)
    let Mass := Vscale k*Dtype*(2+θ*(Uband+1/lambda))*Z*(M/(N:ℝ))*
      (1+Δtype k*Jsep)+Z^2*Klarge k*T^εloss
    have hactual :=
      double_difference_actual_source_grid_monomials
        Chunks Y band Qbase kmax Kmesh Usel
        (by omega : 0 < Qbase) hM hNp hRp hJsep hcsrc hUsrc hθ hDtype
        hmain htail hBp (zero_lt_one.trans_le hCm) hDensity hLlog hTone
        hεloss hNR (hNM.trans hMT) hbase hchunks hscale hUbandCap
        hcounts (fun k r => (hgrids k r).2)
        (by
          intro j hj
          obtain ⟨hRQ,hQN,hmesh,hupper,_,hlower⟩ := hvalid j hj
          exact ⟨hK j,hRQ,hQN,hmesh,hupper,hlower⟩) k hk r
    have hnum :
        (R^2/(Q k:ℝ))^6*(Kmesh k:ℝ)^((12:ℝ)+εloss)*(2*P)^10*Mass ≤
          Cpref*T^(2*εloss)*Llog^10*MassPower := hactual
    clear hactual
    have hP : 0 ≤ P := Nat.cast_nonneg _
    have hPC : P ≤ (Chunks.card:ℝ) := by
      dsimp only [P]
      exact_mod_cast (hgrids k r).1.trans (Finset.card_filter_le _ _)
    have hpoint : 0 ≤ PointError := by
      have hh : 0 ≤ Real.log (6*(N:ℝ)) := Real.log_nonneg (by linarith only [hNone])
      dsimp only [PointError]
      positivity
    have hpe : P*PointError ≤ Cerror*ErrorPower*Llog := by
      have hh := positive_difference_completion_error_physical_bound
        (Y:=(Y.card:ℝ)) (R:=R) (C:=36*Usrc/(csrc*κ))
        (Nat.cast_nonneg _) hNone hNM hMT (by positivity)
      calc
        _ ≤ (8*((Y.card:ℝ)*(M/(N:ℝ)+1)))*PointError := by
          apply mul_le_mul_of_nonneg_right _ hpoint
          have hh := hPC.trans hchunks
          calc
            _ ≤ (Y.card:ℝ)*(8*M/(N:ℝ)) := hh
            _ = (8*(Y.card:ℝ))*(M/(N:ℝ)) := by ring
            _ ≤ (8*(Y.card:ℝ))*(M/(N:ℝ)+1) :=
              mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (by positivity)
            _ = _ := by ring
        _ = 8*((Y.card:ℝ)*(M/(N:ℝ)+1)*
            (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+
              (36*Usrc/(csrc*κ))*R^2/(N:ℝ))) := by
          dsimp only [PointError]
          ring
        _ ≤ 8*((2*Real.sqrt 3*(1+Real.log 6)+2*(36*Usrc/(csrc*κ)))*
            ((Y.card:ℝ)*M/Real.sqrt (N:ℝ)+(Y.card:ℝ)*M*R^2/(N:ℝ)^2)*Llog) :=
          mul_le_mul_of_nonneg_left hh (by norm_num)
        _ = Cerror*((Y.card:ℝ)*M/Real.sqrt (N:ℝ)+
            (Y.card:ℝ)*M*R^2/(N:ℝ)^2)*Llog := by dsimp only [Cerror]; ring
        _ ≤ Cerror*ErrorPower*Llog := by gcongr
    have hlogK : 0 ≤ 1+Real.log (Kmesh k) := by
      have hh : (1:ℝ) ≤ Kmesh k := by
        exact_mod_cast (show 1 ≤ Kmesh k by have hh := hK k; omega)
      have hl := Real.log_nonneg hh
      linarith only [hl]
    have hh := completed_family_logarithmic_power_bound
      (CF:=CF) (W:=Wconst) hC hCap hCpref hTpow hLlog hMass
      (mul_nonneg hP hpoint) hlogK (hlogs k hk).2.1 hnum hpe
    calc
      _ = CF^12*2^11*((1+Real.log (Kmesh k))^12*Wconst^6*
          (C*Cap^11*((R^2/(Q k:ℝ))^6*
            (Kmesh k:ℝ)^((12:ℝ)+εloss)*(2*P)^10*Mass))+(P*PointError)^12) := by
        change CF^12*2^11*((1+Real.log (Kmesh k))^12*(Wconst*(R^2/(Q k:ℝ)))^6*
          (C*(Kmesh k:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*P)^10*Mass)+(P*PointError)^12)=_
        ring
      _ ≤ _ := hh
  have hnReal : (N:ℝ)=8*(n:ℝ) := by exact_mod_cast hNlink
  have hterminal :
      (n:ℝ)*(Y.card:ℝ)*Density kmax ≤ Cterminal*ErrorPower*Llog :=
    capped_terminal_density_error hM hNp hqcap (Nat.cast_nonneg _) hDensity hLnon
      hnReal hQcap (hDensityBound kmax le_rfl) hErrorTerminal
  have hendpoint : Endpoint ≤ Cendpoint*ErrorPower := by
    obtain ⟨hRQ,hQN,_,_,hupper,_⟩ := hvalid 0 (Nat.zero_le _)
    have hh := positive_difference_endpoint_error_physical_bound
      (Y:=(Y.card:ℝ)) (σ:=0) (c:=1) (Nat.cast_nonneg _) hNone hRp hRQ hQN
      hκ (by rfl) (by norm_num) hCphys hBselect hnReal hupper
    have hh' : Endpoint ≤ Cendpoint*((Y.card:ℝ)*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)) := by
      simpa only [mul_zero,zero_mul,zero_div,add_zero,div_one] using hh
    exact hh'.trans (mul_le_mul_of_nonneg_left hErrorEndpoint hCendpoint)
  have hDensityNon : 0 ≤ Density kmax := by
    clear * - hcsrc hUsrc hM hNp hRp hQp
    have hh : 0 ≤ Real.log (512*R^2/(csrc*((Q kmax:ℝ)/768))+1) :=
      Real.log_nonneg (by
        have hh : 0 ≤ 512*R^2/(csrc*((Q kmax:ℝ)/768)) := by positivity
        linarith only [hh])
    dsimp only [Density,CerrorBand,CtailBand,ClowBand]
    positivity
  have hEndpointNon : 0 ≤ Endpoint := by
    clear * - hκ hCphys
    dsimp only [Endpoint,Buffer]
    positivity
  exact all_band_logarithmic_power_aggregation kmax (fun k r => FamilyBound k (Grid k r))
    hCband hFamily hMass hError hLlog hTpow
    (by positivity) hEndpointNon (hlogs 0 (Nat.zero_le _)).2.2 hfamily hterminal hendpoint

private theorem eventually_double_difference_all_source_physical_powers
    {csrc Usrc σ εloss : ℝ}
    (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let L := max (32*Usrc^2/csrc^2)
      (64*(modelPhaseJetCoefficient σ 3+1)*Usrc/κ^2)
    let θ := 1/(8*(L+3))
    ∃ CF C Dtype : ℝ, 1 ≤ CF ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc rshift sshift : ℝ → ℝ) (Y : Finset ℝ)
    (n N Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ) (R Jsep : ℝ)
    {d Wmax M δ Bcut Bselect Cbase Cmesh qcap : ℝ},
    (∀ k, 0 < Kmesh k) → N=8*n →
    0 < d → 0 ≤ Wmax → Wmax ≤ 1/4 → 2*Usrc*Wmax ≤ csrc/64 →
    0 < T → 2 ≤ M → 0 < N → δ ≤ min κ 1 →
    1 ≤ R → R ≤ M → 0 < Jsep → Jsep ≤ M → (N:ℝ) ≤ M → Wmax*Jsep ≤ 1 →
    (∀ y∈Y, y∈Icc (1:ℝ) 2) →
    (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
    (∀ y∈Y, 0 ≤ rshift y ∧ 0 ≤ sshift y ∧
      rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, csrc ≤ iteratedDeriv 5 Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j, 1 ≤ j → j ≤ 7 → |iteratedDeriv j Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3,
      csrc ≤ |(iteratedDeriv 5 Fsrc w)^2-iteratedDeriv 4 Fsrc w*iteratedDeriv 6 Fsrc w|) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    let Φ := fun y u =>
      (Fsrc u-Fsrc (u+rshift y)-Fsrc (u+sshift y)+Fsrc (u+rshift y+sshift y))/d
    (∀ y∈Y, Expdb.IsApproximateModelPhaseFunction (Φ y) σ 4 δ) →
    T*(N:ℝ)*R^2=M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/4)*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    0 < Bcut → 2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    (N:ℝ)^10 ≤ M^3*R^7 →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) →
    let Q := fun k : ℕ => Qbase*2^k
    768 ≤ Qbase → (N:ℝ)*(Q kmax:ℝ) ≤ M →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2 ≤ (N:ℝ) → csrc ≤ 4*κ/(Cphys+2) →
    let Uband := Usrc*T/M^2
    Uband ≤ 1 →
    let NarrowCap := (4/θ+3)*(8*Usrc/(csrc*θ)+3)
    let Cap := 3*NarrowCap
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Δ := fun k : ℕ => (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q k:ℝ)/(N:ℝ)
    let D := fun k : ℕ => Δ k+quarticNonlinearResidualConstant σ δ*(2*(Q k:ℝ))/(N:ℝ)
    let Buffer := fun k : ℕ => (56*(Usel k:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    (∀ k ≤ kmax,
      63*(Usrc/(2*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      1 ≤ Usel k ∧ Bselect^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
      R ≤ (Q k:ℝ) ∧
      (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      (Q k:ℝ) ≤ (N:ℝ) ∧ (Usel k:ℝ) ≤ R^2 ∧
      2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧ D k ≤ 1/2 ∧ Δ k < 1/2) →
    (∀ k ≤ kmax, Usel k ≤ Usel 0) →
    2*Buffer 0+6*(N:ℝ) ≤ M →
    1 ≤ T → M ≤ T → 0 ≤ δ → 1 ≤ Cmesh →
    (Qbase:ℝ) ≤ Cbase*R → (kmax:ℝ) ≤ Real.log (N:ℝ)/Real.log 2 →
    0 < qcap → (qcap/2)*min (N:ℝ) (M/(N:ℝ)) ≤ (Q kmax:ℝ) →
    (∀ k ≤ kmax, (Kmesh k:ℝ) ≤ Cmesh*(Q k:ℝ)*(N:ℝ)/R^2 ∧
      ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Usel k:ℝ)) →
    let f := fun y w => T*Φ y (w/M)
    let CtailBand := 4*Usrc*(64/csrc)^2+192/csrc
    let ClowBand := (2*Usrc+csrc/32)*(3072/csrc)^2+3072/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    let Carg := 512*768/csrc
    let Cdensity := 128*CerrorBand*(3+Real.log (Carg+1))
    let Ccard := 16*Cbase^2+8*Cdensity
    let Cdelta := (16*Usrc/csrc)*Real.sqrt ((Usrc/2)*Cmesh)
    let Ctri := 2+θ*(1+2*Usrc/csrc)
    let C₀ := 60*588*(2*Usrc/csrc)^2
    let MassPower := Ctri*Dtype*
      ((Y.card:ℝ)^11*M^10*(N:ℝ)^2/(Usrc*R^4)+
        (Y.card:ℝ)^11*M^11*(N:ℝ)^2/R^7+
        Cdelta*(Y.card:ℝ)^11*Jsep*M^10/(Usrc*R^2)+
        Cdelta*(Y.card:ℝ)^11*Jsep*M^11/R^5)+
      C₀*(Cmain+2*Bselect*Ctail)*((Y.card:ℝ)^12*M^10*R^2/(N:ℝ)^2)*
        (R/(N:ℝ))^((2:ℝ)/3)*Uband^((4:ℝ)/3)
    let ErrorPower := (Y.card:ℝ)*M/Real.sqrt (N:ℝ)+
      (Y.card:ℝ)*M*R^2/(N:ℝ)^2+(Y.card:ℝ)*(N:ℝ)^2*R^2/M+
      (Y.card:ℝ)*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
    let Cpref := Cmesh^12*Cmesh^εloss*(2*Ccard)^10
    let Wconst := 144*Usrc/(csrc*κ)
    let CKlog := 3+Real.log (Cmesh+1)
    let Cerror := 8*(2*Real.sqrt 3*(1+Real.log 6)+72*Usrc/(csrc*κ))
    let Cfamily := CF^12*2^11*(C*Cap^11*Wconst^6*CKlog^12*Cpref+Cerror^12)
    let Cband := 2+1/Real.log 2
    let Cterminal := Cdensity/(2*qcap^2)
    let Cendpoint := 112/κ+2/(Cphys+2)+41/4
    let Ctotal := (2:ℝ)^11*
      (Cband^11*(Cterminal^12+(8:ℝ)^12*Cband*Cfamily)+Cendpoint^12)
    ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
    (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),(𝐞 (f y j):ℂ)‖)^12 ≤
        Ctotal*T^(2*εloss)*(1+Real.log T)^36*(MassPower+ErrorPower^12)
 := by
  classical
  intro κ L θ
  obtain ⟨CF,C,Dtype,hCF,hC,hDtype,hcore⟩ :=
    eventually_double_difference_all_band_subinterval_moment hcsrc hUsrc hσ hεloss
  refine ⟨CF,C,Dtype,hCF,hC,hDtype,?_⟩
  filter_upwards [hcore] with T hcoreT
  clear hcore
  intro Fsrc rshift sshift Y n N Qbase kmax Kmesh Usel R Jsep
    d Wmax M δ Bcut Bselect Cbase Cmesh qcap
    hK hNlink hd hw hwcap hsmallShift hT hMtwo hN hδ hR hRM hJsep hJM hNM hwJ
    hy hsepY hshifts hreg hlower hjets htests hnegative Φ hmodels
    hscale hfourBuffer hfourBudget hquadBudget hBcut hBselectSize hcutMargin hscaleTen hNsqM
    Q hQbase hQmax Cphys c J B hsmall hNR hRN hNcube hNtwo hanchorBudget
    Uband hUbandCap NarrowCap Cap C₂ C₃ Ct Cc Ccurv Kres Esize Dbase Tbase
    hsize hBsize Lunit Gamma Cthird Cpack Cfirst Cgap Cmain Ctail
    Δ D Buffer hvalid hUmax hroom
    hTone hMT hδ₀ hCm hbase hklog hqcap hQcap hmore
    f CtailBand ClowBand CerrorBand Carg Cdensity Ccard Cdelta Ctri C₀
    MassPower ErrorPower Cpref Wconst CKlog Cerror Cfamily Cband Cterminal Cendpoint Ctotal
    A Bint hA hab hB
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hθ : 0 < θ := by
    clear * - hUsrc hcsrc hκ
    dsimp only [θ,L]
    positivity
  have hCphys : 0 ≤ Cphys := by
    clear * - hσ
    dsimp only [Cphys]
    positivity
  have hCap : 0 ≤ Cap := by
    clear * - hθ hcsrc hUsrc
    dsimp only [Cap,NarrowCap]
    positivity
  have hBselect : 1 ≤ Bselect := by
    have hh : 0 < 168/κ := by positivity
    linarith only [hBselectSize,hh]
  obtain ⟨hmain,htail⟩ : 0 ≤ Cmain ∧ 0 ≤ Ctail :=
    model_source_large_entry_coefficients_nonneg hσ hδ₀
  obtain ⟨Chunks,band,hchunks,hbands,_htail,hgrids,hwhole⟩ :=
    hcoreT Fsrc rshift sshift Y n N Qbase kmax Kmesh Usel R Jsep
      (d:=d) (Wmax:=Wmax) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
      hK hNlink hd hw hwcap hsmallShift hT hMtwo hN hδ hR hRM hJsep hJM hNM hwJ
      hy hsepY hshifts hreg hlower hjets htests hnegative hmodels
      hscale hfourBuffer hfourBudget hquadBudget hBcut hBselectSize hcutMargin
      hscaleTen hNsqM hQbase hQmax hsmall hNR hRN hNcube hNtwo hanchorBudget
      hUbandCap hsize hBsize hvalid hUmax hroom A Bint hA hab hB
  exact double_difference_finite_source_power_bound
    hcsrc hUsrc hκ hθ.le hCphys hεloss.le hC.le hDtype.le hmain htail hCap hBselect
    Chunks Y band n N Qbase kmax Kmesh Usel
    hK hNlink (by linarith only [hNtwo]) hR hJsep.le hNM
    hscale hNR hUbandCap hTone hMT (by omega) hCm hbase hklog hqcap hQcap
    (by
      intro k hk
      obtain ⟨_,hmesh,_,_,hRQ,hupper,hQN,_,_,_,_⟩ := hvalid k hk
      exact ⟨hRQ,hQN,hmesh,(hmore k hk).1,hupper,(hmore k hk).2⟩)
    hchunks hbands (fun k r => (hgrids k r).2) hwhole

private theorem exists_capped_source_physical_budget
    {Ccap A₄ A₂ B Cbuffer Clinear : ℝ}
    (hcap : 0 ≤ Ccap) (hA₄ : 0 ≤ A₄) (hA₂ : 0 ≤ A₂)
    (hB : 0 ≤ B) (hbuffer : 0 ≤ Cbuffer) (hlinear : 0 ≤ Clinear) :
    ∃ Cbudget : ℝ, 1 ≤ Cbudget ∧ Ccap ≤ Cbudget ∧
      ∀ (N R M U : ℝ), 1 ≤ N → 1 ≤ R →
      Cbudget*R ≤ N → Cbudget*N ≤ R^2 → Cbudget*N ≤ M →
      Cbudget*N^3 ≤ M*R^2 → Cbudget*N*R ≤ M →
      U ≤ (N/R)^((2:ℝ)/3) →
      0 < M ∧ R ≤ N ∧ N ≤ R^2 ∧ N ≤ M ∧ R ≤ M ∧
      N^3 ≤ M*R^2 ∧ Ccap*R ≤ N ∧ Ccap*N*R ≤ M ∧
      7*N+2 ≤ M/4 ∧
      A₄*(6*N+1)^4 ≤ M*N*R^2 ∧
      A₂*(6*N+1)^2 ≤ N*R^2 ∧
      B*R^2/N^2 ≤ 1/2 ∧
      2*(Cbuffer*U*N+Clinear*N+2)+6*N ≤ M
 := by
  let Cbudget := 37+Ccap+2401*A₄+49*A₂+2*B+2*Cbuffer+2*Clinear
  have hbounds : 1 ≤ Cbudget ∧ Ccap ≤ Cbudget ∧ 36 ≤ Cbudget ∧
      2401*A₄ ≤ Cbudget ∧ 49*A₂ ≤ Cbudget ∧ 2*B+1 ≤ Cbudget ∧
      2*Cbuffer+2*Clinear+10 ≤ Cbudget := by
    dsimp only [Cbudget]
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith only [hcap,hA₄,hA₂,hB,hbuffer,hlinear]
  obtain ⟨hC,hCap,h36,h4,h2,hBsize,hroomSize⟩ := hbounds
  have hCp : 0 < Cbudget := zero_lt_one.trans_le hC
  refine ⟨Cbudget,hC,hCap,?_⟩
  intro N R M U hN hR hsep hrad hlength hcubic hcapRoom hU
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hRN : R ≤ N := (le_mul_of_one_le_left hRp.le hC).trans hsep
  have hNR : N ≤ R^2 := (le_mul_of_one_le_left hNp.le hC).trans hrad
  have hNM : N ≤ M := (le_mul_of_one_le_left hNp.le hC).trans hlength
  have hMp : 0 < M := hNp.trans_le hNM
  have hNcube : N^3 ≤ M*R^2 :=
    (le_mul_of_one_le_left (by positivity) hC).trans hcubic
  have hN7 : 6*N+1 ≤ 7*N := by linarith only [hN]
  have hpad : 7*N+2 ≤ M/4 := by
    have hh := (mul_le_mul_of_nonneg_right h36 hNp.le).trans hlength
    linarith only [hh,hN]
  have hquartic : A₄*(6*N+1)^4 ≤ M*N*R^2 := by
    calc
      _ ≤ A₄*(7*N)^4 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hN7 4) hA₄
      _ = (2401*A₄)*N^4 := by ring
      _ ≤ Cbudget*N^4 := mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = (Cbudget*N^3)*N := by ring
      _ ≤ (M*R^2)*N := mul_le_mul_of_nonneg_right hcubic hNp.le
      _ = _ := by ring
  have hquadratic : A₂*(6*N+1)^2 ≤ N*R^2 := by
    calc
      _ ≤ A₂*(7*N)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hN7 2) hA₂
      _ = (49*A₂)*N^2 := by ring
      _ ≤ Cbudget*N^2 := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = N*(Cbudget*N) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hrad hNp.le
  have hsmall : B*R^2/N^2 ≤ 1/2 := by
    have hCsq : 2*B ≤ Cbudget^2 := by nlinarith only [hBsize,hC]
    have hh := pow_le_pow_left₀ (mul_pos hCp hRp).le hsep 2
    have hi := mul_le_mul_of_nonneg_right hCsq (sq_nonneg R)
    apply (div_le_iff₀ (sq_pos_of_pos hNp)).mpr
    nlinarith only [hh,hi]
  let heightCap := N*(N/R)^((2:ℝ)/3)
  have hXnon : 0 ≤ heightCap := by dsimp only [heightCap]; positivity
  have hXcube : heightCap^3=N^5/R^2 := by
    dsimp only [heightCap]
    have hh : ((N/R)^((2:ℝ)/3))^3=(N/R)^2 := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (div_pos hNp hRp).le]
      norm_num
    rw [mul_pow,hh]
    field_simp
  have hCcube : (Cbudget*heightCap)^3 ≤ M^3 := by
    rw [mul_pow,hXcube]
    calc
      _ = (Cbudget*N^3)*((Cbudget*N)^2)/R^2 := by ring
      _ ≤ (M*R^2)*(M^2)/R^2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg R)
        exact mul_le_mul hcubic (pow_le_pow_left₀ (mul_pos hCp hNp).le hlength 2)
          (by positivity) (by positivity)
      _ = M^3 := by field_simp
  have hCX : Cbudget*heightCap ≤ M :=
    (pow_le_pow_iff_left₀ (mul_nonneg hCp.le hXnon) hMp.le (by norm_num : (3:ℕ) ≠ 0)).mp hCcube
  have hNX : N ≤ heightCap := by
    have hh : 1 ≤ (N/R)^((2:ℝ)/3) := Real.one_le_rpow
      ((le_div_iff₀ hRp).mpr (by simpa only [one_mul] using hRN)) (by norm_num)
    exact le_mul_of_one_le_right hNp.le hh
  have hXone : 1 ≤ heightCap := hN.trans hNX
  have hUN : U*N ≤ heightCap := by
    simpa only [heightCap,mul_comm] using mul_le_mul_of_nonneg_right hU hNp.le
  have hroom : 2*(Cbuffer*U*N+Clinear*N+2)+6*N ≤ M := by
    calc
      _ ≤ (2*Cbuffer+2*Clinear+10)*heightCap := by
        nlinarith only [
          mul_le_mul_of_nonneg_left hUN hbuffer,
          mul_le_mul_of_nonneg_left hNX hlinear,hNX,hXone]
      _ ≤ Cbudget*heightCap := mul_le_mul_of_nonneg_right hroomSize hXnon
      _ ≤ M := hCX
  exact ⟨hMp,hRN,hNR,hNM,hRN.trans hNM,hNcube,
    (mul_le_mul_of_nonneg_right hCap hRp.le).trans hsep,
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCap hNp.le) hRp.le).trans hcapRoom,
    hpad,hquartic,hquadratic,hsmall,hroom⟩

private theorem exists_capped_source_discrete_budget
    {Usrc κ Cphys B Bselect Dbase Δbase : ℝ}
    (hUsrc : 0 < Usrc) (hκ : 0 < κ) (hCphys : 0 ≤ Cphys)
    (hB : 0 ≤ B) (hBselect : 1 ≤ Bselect) :
    ∃ Cbudget qcap : ℝ, 1 ≤ Cbudget ∧ Usrc ≤ Cbudget ∧ 0 < qcap ∧
    ∀ (N : ℕ) (M R : ℝ), (1:ℝ) ≤ N → 1 ≤ R →
      Cbudget*R ≤ N → Cbudget*(N:ℝ) ≤ R^2 → Cbudget*(N:ℝ) ≤ M →
      Cbudget*(N:ℝ)^3 ≤ M*R^2 → Cbudget*(N:ℝ)*R ≤ M →
    ∃ (Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ),
      let Q := fun k : ℕ => Qbase*2^k
      0 < M ∧ R ≤ (N:ℝ) ∧ (N:ℝ) ≤ R^2 ∧ (N:ℝ) ≤ M ∧ R ≤ M ∧
      (N:ℝ)^3 ≤ M*R^2 ∧
      7*(N:ℝ)+2 ≤ M/4 ∧
      (3*Usrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 ∧
      (3*Usrc/4)*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 ∧
      B*R^2/(N:ℝ)^2 ≤ 1/2 ∧
      768 ≤ Qbase ∧ (Qbase:ℝ) ≤ 1536*R ∧
      (N:ℝ)*(Q kmax:ℝ) ≤ M ∧
      (qcap/2)*min (N:ℝ) (M/(N:ℝ)) ≤ (Q kmax:ℝ) ∧
      (kmax:ℝ) ≤ Real.log (N:ℝ)/Real.log 2 ∧
      (∀ k, 0 < Kmesh k) ∧
      (∀ k ≤ kmax,
        63*(Usrc/(2*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
        (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
        1 ≤ Usel k ∧ Bselect^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
        R ≤ (Q k:ℝ) ∧
        (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
        (Q k:ℝ) ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
        2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
        Dbase*(Q k:ℝ)/(N:ℝ) ≤ 1/2 ∧ Δbase*(Q k:ℝ)/(N:ℝ) < 1/2) ∧
      (∀ k, Usel k ≤ Usel 0) ∧
      2*((56*(Usel 0:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2)+6*(N:ℝ) ≤ M ∧
      (∀ k ≤ kmax,
        (Kmesh k:ℝ) ≤ (2*max 1 (63*Usrc/2))*(Q k:ℝ)*(N:ℝ)/R^2 ∧
        ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Usel k:ℝ)) := by
  let Dcap := |Dbase|+|Δbase|+1
  have hDcap : 0 ≤ Dcap := by dsimp only [Dcap]; positivity
  have hDb : Dbase ≤ Dcap := by
    dsimp only [Dcap]
    linarith only [le_abs_self Dbase,abs_nonneg Δbase]
  have hΔb : Δbase ≤ Dcap := by
    dsimp only [Dcap]
    linarith only [le_abs_self Δbase,abs_nonneg Dbase]
  let H := (2*Bselect)^((3:ℝ)/2)
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  let qcap := 1/(1+H+4*Dcap)
  have hden : 0 < 1+H+4*Dcap := by positivity
  have hq : 0 < qcap := by dsimp only [qcap]; positivity
  have hqone : qcap ≤ 1 := by
    dsimp only [qcap]
    apply (div_le_iff₀ hden).mpr
    linarith only [hH,hDcap]
  have hqH : qcap*(2*Bselect*1)^((3:ℝ)/2) ≤ 1 := by
    simp only [mul_one]
    change (1/(1+H+4*Dcap))*H ≤ 1
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ hden).mpr
    linarith only [hDcap]
  have hqD : 4*Dcap*qcap ≤ 1 := by
    change 4*Dcap*(1/(1+H+4*Dcap)) ≤ 1
    rw [mul_one_div]
    apply (div_le_iff₀ hden).mpr
    linarith only [hH]
  obtain ⟨C₀,hC₀,hCcap,hbudget⟩ := exists_capped_source_physical_budget
    (Ccap:=1536/qcap) (A₄:=3*Usrc) (A₂:=3*Usrc/4)
    (Cbuffer:=56/κ) (Clinear:=1/(Cphys+2))
    (by positivity) (by positivity) (by positivity) hB (by positivity) (by positivity)
  let Cbudget := max C₀ Usrc
  have hC : C₀ ≤ Cbudget := le_max_left _ _
  refine ⟨Cbudget,qcap,hC₀.trans hC,le_max_right _ _,hq,?_⟩
  intro N M R hN hR hsep hrad hlength hcubic hcapRoom
  have hNp : (0:ℝ) < N := zero_lt_one.trans_le hN
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hsep₀ : C₀*R ≤ N := (mul_le_mul_of_nonneg_right hC hRp.le).trans hsep
  have hrad₀ : C₀*(N:ℝ) ≤ R^2 := (mul_le_mul_of_nonneg_right hC hNp.le).trans hrad
  have hlength₀ : C₀*(N:ℝ) ≤ M := (mul_le_mul_of_nonneg_right hC hNp.le).trans hlength
  have hcubic₀ : C₀*(N:ℝ)^3 ≤ M*R^2 :=
    (mul_le_mul_of_nonneg_right hC (by positivity)).trans hcubic
  have hcap₀ : C₀*(N:ℝ)*R ≤ M :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hNp.le) hRp.le).trans hcapRoom
  obtain ⟨hM,hRN,hNR,hNM,hRM,hNcube,hcapN,hcapM,hpad,hquartic,hquadratic,hsmall,_⟩ :=
    hbudget (N:ℝ) R M 0 hN hR hsep₀ hrad₀ hlength₀ hcubic₀ hcap₀ (by positivity)
  have hroom : 2*768*R ≤ qcap*min (N:ℝ) (M/(N:ℝ)) := by
    rw [mul_min_of_nonneg _ _ hq.le]
    apply le_min
    · have hh := mul_le_mul_of_nonneg_left hcapN hq.le
      calc
        _ = qcap*((1536/qcap)*R) := by field_simp; norm_num
        _ ≤ _ := hh
    · rw [←mul_div_assoc]
      apply (le_div_iff₀ hNp).mpr
      have hh := mul_le_mul_of_nonneg_left hcapM hq.le
      calc
        (2*768*R)*(N:ℝ) = qcap*((1536/qcap)*(N:ℝ)*R) := by field_simp; ring
        _ ≤ _ := hh
  obtain ⟨Qbase,kmax,Kmesh,Usel,hBaseLo,hBaseHi,hEndLo,_hEndHi,hNQ,_hError,
    hkmax,hK,hvalid,hmono⟩ :=
    capped_dyadic_band_integer_physical_selection N (σ:=1) (J:=Usrc) (L:=1)
      (Cbase:=768) (Dcap:=Dcap) (by norm_num) hM hR hRN hNR hBselect (by norm_num)
      (by norm_num) hq hqone hqH hDcap hqD hroom
  let Q := fun k : ℕ => Qbase*2^k
  have hUzero : (Usel 0:ℝ) ≤ ((N:ℝ)/R)^((2:ℝ)/3) := by
    obtain ⟨_,_,_,_,_,_,hupper,_,_,_,hstrong,_,_⟩ := hvalid 0 (Nat.zero_le _)
    have hRQ : R ≤ (Q 0:ℝ) := by linarith only [hstrong,hRp]
    calc
      _ ≤ ((N:ℝ)/(Q 0:ℝ))^((2:ℝ)/3)/Bselect := hupper
      _ ≤ ((N:ℝ)/(Q 0:ℝ))^((2:ℝ)/3) := div_le_self (by positivity) hBselect
      _ ≤ _ := Real.rpow_le_rpow (by positivity)
        (div_le_div_of_nonneg_left hNp.le hRp hRQ) (by norm_num)
  have hbuffer := (hbudget (N:ℝ) R M (Usel 0:ℝ) hN hR
    hsep₀ hrad₀ hlength₀ hcubic₀ hcap₀ hUzero).2.2.2.2.2.2.2.2.2.2.2.2
  have hbase : 768 ≤ Qbase := by
    have hh : (768:ℝ) ≤ Qbase :=
      (le_mul_of_one_le_right (by norm_num) hR).trans hBaseLo
    exact_mod_cast hh
  refine ⟨Qbase,kmax,Kmesh,Usel,hM,hRN,hNR,hNM,hRM,hNcube,hpad,hquartic,
    hquadratic,hsmall,hbase,?_,hNQ,?_,hkmax,hK,?_,hmono,?_,?_⟩
  · simpa only [show (2:ℝ)*768=1536 by norm_num] using hBaseHi
  · simpa only [div_mul_eq_mul_div] using hEndLo
  · intro k hk
    obtain ⟨_,hsource,hmesh,_,hU,hwrap,hupper,_,hQN,hUR,hstrong,hmin,hD⟩ := hvalid k hk
    have hD' : Dbase*(Q k:ℝ)/(N:ℝ) ≤ 1/4 :=
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hDb (Nat.cast_nonneg _)) hNp.le).trans hD
    have hΔ' : Δbase*(Q k:ℝ)/(N:ℝ) ≤ 1/4 :=
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hΔb (Nat.cast_nonneg _)) hNp.le).trans hD
    refine ⟨?_,hmesh,hU,hwrap,?_,hupper,?_,hUR,hmin,?_,?_⟩
    · simpa only [mul_one] using hsource
    · linarith only [hstrong,hRp]
    · exact_mod_cast hQN
    · exact hD'.trans (by norm_num)
    · exact hΔ'.trans_lt (by norm_num)
  · convert hbuffer using 1
    ring
  · intro k hk
    obtain ⟨_,_,_,hupper,_,_,_,hlower,_⟩ := hvalid k hk
    exact ⟨by simpa only [mul_one] using hupper,hlower⟩

private theorem double_difference_five_monomial_absorption
    {Usrc Ctri Dtype Cdelta C₀ Cmain Bselect Ctail Ctotal ε Y M N R Jsep T X : ℝ}
    (hUsrc : 0 < Usrc) (hY : 0 ≤ Y) (hM : 0 < M) (hNp : 0 < N) (hRp : 0 < R)
    (hJsep : 0 ≤ Jsep) (hT : 0 < T) (hTotal : 0 ≤ Ctotal) :
    let a₁ := Ctri*Dtype/Usrc
    let a₂ := Ctri*Dtype
    let a₃ := Ctri*Dtype*Cdelta/Usrc
    let a₄ := Ctri*Dtype*Cdelta
    let a₅ := C₀*(Cmain+2*Bselect*Ctail)*Usrc^((4:ℝ)/3)
    let Cmass := 1+|a₁|+|a₂|+|a₃|+|a₄|+|a₅|
    |Ctotal| *Cmass*T^(ε/2)*(1+Real.log T)^36 ≤ T^ε →
    let ErrorTotal := Y*M/Real.sqrt N+Y*M*R^2/N^2+
      Y*N^2*R^2/M+Y*N*(N/R)^((2:ℝ)/3)
    let Main := Y^11*M^10*N^2/R^4+Y^11*M^11*N^2/R^7+
      Y^11*Jsep*M^10/R^2+Y^11*Jsep*M^11/R^5+
      Y^12*M^10*R^2/N^2*(R/N)^((2:ℝ)/3)*(T/M^2)^((4:ℝ)/3)
    let MassPower := Ctri*Dtype*
      (Y^11*M^10*N^2/(Usrc*R^4)+Y^11*M^11*N^2/R^7+
        Cdelta*Y^11*Jsep*M^10/(Usrc*R^2)+Cdelta*Y^11*Jsep*M^11/R^5)+
      C₀*(Cmain+2*Bselect*Ctail)*(Y^12*M^10*R^2/N^2)*
        (R/N)^((2:ℝ)/3)*(Usrc*T/M^2)^((4:ℝ)/3)
    X ≤ Ctotal*T^(ε/2)*(1+Real.log T)^36*(MassPower+ErrorTotal^12) →
    X ≤ T^ε*(Main+ErrorTotal^12) := by
  intro a₁ a₂ a₃ a₄ a₅ Cmass habsorb ErrorTotal Main MassPower
  have hCmass : 1 ≤ Cmass := by
    dsimp only [Cmass]
    linarith only [abs_nonneg a₁,abs_nonneg a₂,abs_nonneg a₃,abs_nonneg a₄,abs_nonneg a₅]
  let P₁ := Y^11*M^10*N^2/R^4
  let P₂ := Y^11*M^11*N^2/R^7
  let P₃ := Y^11*Jsep*M^10/R^2
  let P₄ := Y^11*Jsep*M^11/R^5
  let P₅ := Y^12*M^10*R^2/N^2*
    (R/N)^((2:ℝ)/3)*(T/M^2)^((4:ℝ)/3)
  have hP₁ : 0 ≤ P₁ := by clear * - hY hM hNp hRp; dsimp only [P₁]; positivity
  have hP₂ : 0 ≤ P₂ := by clear * - hY hM hNp hRp; dsimp only [P₂]; positivity
  have hP₃ : 0 ≤ P₃ := by clear * - hY hM hNp hRp hJsep; dsimp only [P₃]; positivity
  have hP₄ : 0 ≤ P₄ := by clear * - hY hM hNp hRp hJsep; dsimp only [P₄]; positivity
  have hP₅ : 0 ≤ P₅ := by clear * - hY hM hNp hRp hT; dsimp only [P₅]; positivity
  have hMain : 0 ≤ Main := by change 0 ≤ P₁+P₂+P₃+P₄+P₅; positivity
  have hMassEq : MassPower=a₁*P₁+a₂*P₂+a₃*P₃+a₄*P₄+a₅*P₅ := by
    have hp : (Usrc*T/M^2)^((4:ℝ)/3)=
        Usrc^((4:ℝ)/3)*(T/M^2)^((4:ℝ)/3) := by
      rw [mul_div_assoc,Real.mul_rpow hUsrc.le (by positivity)]
    dsimp only [MassPower,P₁,P₂,P₃,P₄,P₅,a₁,a₂,a₃,a₄,a₅]
    rw [hp]
    ring
  have hweighted (a b c d e x y z u v : ℝ)
      (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hu : 0 ≤ u) (hv : 0 ≤ v) :
      a*x+b*y+c*z+d*u+e*v ≤
        (1+|a|+|b|+|c|+|d|+|e|)*(x+y+z+u+v) := by
    clear * - hx hy hz hu hv
    have ha := mul_le_mul (le_abs_self a)
      (show x ≤ x+y+z+u+v by linarith only [hy,hz,hu,hv]) hx (abs_nonneg a)
    have hb := mul_le_mul (le_abs_self b)
      (show y ≤ x+y+z+u+v by linarith only [hx,hz,hu,hv]) hy (abs_nonneg b)
    have hc := mul_le_mul (le_abs_self c)
      (show z ≤ x+y+z+u+v by linarith only [hx,hy,hu,hv]) hz (abs_nonneg c)
    have hd := mul_le_mul (le_abs_self d)
      (show u ≤ x+y+z+u+v by linarith only [hx,hy,hz,hv]) hu (abs_nonneg d)
    have he := mul_le_mul (le_abs_self e)
      (show v ≤ x+y+z+u+v by linarith only [hx,hy,hz,hu]) hv (abs_nonneg e)
    nlinarith only [ha,hb,hc,hd,he,hx,hy,hz,hu,hv]
  have hMass : MassPower ≤ Cmass*Main := by
    rw [hMassEq]
    exact hweighted a₁ a₂ a₃ a₄ a₅ P₁ P₂ P₃ P₄ P₅ hP₁ hP₂ hP₃ hP₄ hP₅
  have hEM : 0 ≤ Main+ErrorTotal^12 := add_nonneg hMain (by positivity)
  have hMassTotal : MassPower+ErrorTotal^12 ≤ Cmass*(Main+ErrorTotal^12) := by
    calc
      _ ≤ Cmass*Main+Cmass*ErrorTotal^12 :=
        add_le_add hMass (le_mul_of_one_le_left (by positivity) hCmass)
      _ = _ := (mul_add _ _ _).symm

  intro hraw
  calc
    _ ≤ Ctotal*T^(ε/2)*(1+Real.log T)^36*(MassPower+ErrorTotal^12) := hraw
    _ ≤ Ctotal*T^(ε/2)*(1+Real.log T)^36*(Cmass*(Main+ErrorTotal^12)) :=
      mul_le_mul_of_nonneg_left hMassTotal (by positivity)
    _ ≤ |Ctotal| *T^(ε/2)*(1+Real.log T)^36*(Cmass*(Main+ErrorTotal^12)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self Ctotal) (by positivity)) (by positivity))
        (mul_nonneg (zero_le_one.trans hCmass) hEM)
    _ = (|Ctotal| *Cmass*T^(ε/2)*(1+Real.log T)^36)*(Main+ErrorTotal^12) := by ac_rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right habsorb hEM

private theorem eventually_double_difference_uniform_capped_source_bound
    {csrc Usrc σ δ ε : ℝ}
    (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) (hσ : 0 < σ)
    (hδzero : 0 ≤ δ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hε : 0 < ε)
    (hanchor : csrc ≤ 4*modelPhaseThirdLower σ/(σ*(σ+1)+3)) :
    ∃ Cbudget w₀ : ℝ, 1 ≤ Cbudget ∧ 0 < w₀ ∧ w₀ ≤ 1/4 ∧
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc rshift sshift : ℝ → ℝ) (Y : Finset ℝ)
      (n N : ℕ) (R Jsep : ℝ) {d Wmax M : ℝ},
      N=8*n → 2 ≤ N → 1 ≤ R → 0 < d → 0 ≤ Wmax → Wmax ≤ w₀ →
      0 < Jsep → Jsep ≤ M → Wmax*Jsep ≤ 1 →
      (∀ y∈Y, y∈Icc (1:ℝ) 2) →
      (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
      (∀ y∈Y, 0 ≤ rshift y ∧ 0 ≤ sshift y ∧
        rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
      (∀ w∈Icc (1/2:ℝ) 3, csrc ≤ iteratedDeriv 5 Fsrc w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j, 1 ≤ j → j ≤ 7 → |iteratedDeriv j Fsrc w| ≤ Usrc) →
      (∀ w∈Icc (1/2:ℝ) 3,
        csrc ≤ |(iteratedDeriv 5 Fsrc w)^2-iteratedDeriv 4 Fsrc w*iteratedDeriv 6 Fsrc w|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
      let Φ := fun y u =>
        (Fsrc u-Fsrc (u+rshift y)-Fsrc (u+sshift y)+Fsrc (u+rshift y+sshift y))/d
      (∀ y∈Y, Expdb.IsApproximateModelPhaseFunction (Φ y) σ 4 δ) →
      T*(N:ℝ)*R^2=M^3 →
      Cbudget*R ≤ N → Cbudget*(N:ℝ) ≤ R^2 → Cbudget*(N:ℝ) ≤ M →
      Cbudget*(N:ℝ)^3 ≤ M*R^2 → Cbudget*(N:ℝ)*R ≤ M →
      Cbudget*M ≤ (N:ℝ)*R^2 → M ≤ T → R^2 ≤ T →
      (N:ℝ)^10 ≤ M^3*R^7 →
      ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
      (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
      let Yc := (Y.card:ℝ)
      let ErrorTotal := Yc*M/Real.sqrt (N:ℝ)+Yc*M*R^2/(N:ℝ)^2+
        Yc*(N:ℝ)^2*R^2/M+Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
      let Main := Yc^11*M^10*(N:ℝ)^2/R^4+Yc^11*M^11*(N:ℝ)^2/R^7+
        Yc^11*Jsep*M^10/R^2+Yc^11*Jsep*M^11/R^5+
        Yc^12*M^10*R^2/(N:ℝ)^2*(R/(N:ℝ))^((2:ℝ)/3)*(T/M^2)^((4:ℝ)/3)
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),(𝐞 (T*Φ y ((j:ℝ)/M)):ℂ)‖)^12 ≤
        T^ε*(Main+ErrorTotal^12) := by
  classical
  let εloss := ε/4
  have hεloss : 0 < εloss := by dsimp only [εloss]; linarith only [hε]
  let κ := modelPhaseThirdLower σ
  let L := max (32*Usrc^2/csrc^2)
    (64*(modelPhaseJetCoefficient σ 3+1)*Usrc/κ^2)
  let θ := 1/(8*(L+3))
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  obtain ⟨CF,C,Dtype,_hCF,hC,_hDtype,hfinite⟩ :=
    eventually_double_difference_all_source_physical_powers hcsrc hUsrc hσ hεloss
  let Cphys := σ*(σ+1)+1
  let c := κ/6
  let J := Cphys/6
  let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
  let NarrowCap := (4/θ+3)*(8*Usrc/(csrc*θ)+3)
  let Cap := 3*NarrowCap
  let C₂ := modelPhaseJetCoefficient σ 2+δ
  let C₃ := modelPhaseJetCoefficient σ 3+δ
  let Ct := C₂/2+5*C₃/12
  let Cc := C₂/κ+C₃/(2*κ)
  let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
  let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
    2*quarticNonlinearResidualConstant σ δ)/κ
  let Esize := κ/(16*(Cphys+2))
  let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
  let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
  let Lunit := 2*κ/Cphys
  let Gamma := Cphys/κ
  let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
  let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
  let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
  let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
  let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
  let Ctail := 4*Cpack/Lunit^2+Cgap
  have hCphys : 0 ≤ Cphys := by clear * - hσ; dsimp only [Cphys]; positivity
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hEsize : 0 < Esize := by clear * - hκ hCphys; dsimp only [Esize]; positivity
  let Δbase := 37*B/2+16*B*Cc+2*Ct+2*Cc
  let Sector := 2*3840*128^2*105*(Dbase+64*Tbase*Esize^2)
  obtain ⟨Bcut,Bselect,hBcut,hBs,hBsSize,hcutMargin,hsize,hcurvAbs⟩ :=
    exists_source_cutoff_margins (Sector:=Sector) hκ (abs_nonneg Ccurv) hCphys hEsize
  have hcurv : 61*Ccurv*Cphys ≤ Bcut :=
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_abs_self Ccurv) (by norm_num)) hCphys).trans hcurvAbs
  obtain ⟨Cbudget,qcap,hCbudget,hUbudget,hqcap,hselect⟩ :=
    exists_capped_source_discrete_budget (Dbase:=Dbase) (Δbase:=Δbase)
      hUsrc hκ hCphys hB hBs
  let w₀ := min (1/4:ℝ) (csrc/(128*Usrc))
  have hw₀ : 0 < w₀ := lt_min (by norm_num) (by positivity)
  have hwcap : w₀ ≤ 1/4 := min_le_left _ _
  have hwsmall : 2*Usrc*w₀ ≤ csrc/64 := by
    calc
      _ ≤ 2*Usrc*(csrc/(128*Usrc)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = _ := by field_simp; norm_num
  let Cbase := (1536:ℝ)
  let Cmesh := 2*max 1 (63*Usrc/2)
  have hCm : 1 ≤ Cmesh := by
    have hh := le_max_left (1:ℝ) (63*Usrc/2)
    dsimp only [Cmesh]
    linarith only [hh]
  let CtailBand := 4*Usrc*(64/csrc)^2+192/csrc
  let ClowBand := (2*Usrc+csrc/32)*(3072/csrc)^2+3072/csrc
  let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
  let Carg := 512*768/csrc
  let Cdensity := 128*CerrorBand*(3+Real.log (Carg+1))
  let Ccard := 16*Cbase^2+8*Cdensity
  let Cdelta := (16*Usrc/csrc)*Real.sqrt ((Usrc/2)*Cmesh)
  let Ctri := 2+θ*(1+2*Usrc/csrc)
  let C₀ := 60*588*(2*Usrc/csrc)^2
  let Cpref := Cmesh^12*Cmesh^εloss*(2*Ccard)^10
  let Wconst := 144*Usrc/(csrc*κ)
  let CKlog := 3+Real.log (Cmesh+1)
  let Cerror := 8*(2*Real.sqrt 3*(1+Real.log 6)+72*Usrc/(csrc*κ))
  let Cfamily := CF^12*2^11*(C*Cap^11*Wconst^6*CKlog^12*Cpref+Cerror^12)
  let Cband := 2+1/Real.log 2
  let Cterminal := Cdensity/(2*qcap^2)
  let Cendpoint := 112/κ+2/(Cphys+2)+41/4
  let Ctotal := (2:ℝ)^11*
    (Cband^11*(Cterminal^12+(8:ℝ)^12*Cband*Cfamily)+Cendpoint^12)
  have hθ : 0 < θ := by
    clear * - hUsrc hcsrc hκ
    dsimp only [θ,L]
    positivity
  have hCap : 0 ≤ Cap := by
    clear * - hθ hUsrc hcsrc
    dsimp only [Cap,NarrowCap]
    positivity
  have hTotal : 0 ≤ Ctotal := by
    clear * - hC hCap hCm
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp only [Ctotal,Cband,Cfamily,Cpref]
    positivity
  let a₁ := Ctri*Dtype/Usrc
  let a₂ := Ctri*Dtype
  let a₃ := Ctri*Dtype*Cdelta/Usrc
  let a₄ := Ctri*Dtype*Cdelta
  let a₅ := C₀*(Cmain+2*Bselect*Ctail)*Usrc^((4:ℝ)/3)
  let Cmass := 1+|a₁|+|a₂|+|a₃|+|a₄|+|a₅|
  have hCmass : 1 ≤ Cmass := by
    dsimp only [Cmass]
    linarith only [abs_nonneg a₁,abs_nonneg a₂,abs_nonneg a₃,abs_nonneg a₄,abs_nonneg a₅]
  have hAbsorb := eventually_selected_band_logarithmic_absorption
    (C:=|Ctotal| *Cmass) (mul_nonneg (abs_nonneg _) (zero_le_one.trans hCmass)) hε
  refine ⟨Cbudget,w₀,hCbudget,hw₀,hwcap,?_⟩
  filter_upwards [hfinite,hAbsorb,Filter.eventually_ge_atTop (1:ℝ)] with T hfiniteT habsorb hTone
  clear hfinite hAbsorb
  intro Fsrc rshift sshift Y n N R Jsep d Wmax M
    hNlink hNtwo hR hd hW hWsmall hJsep hJM hWJ hy hsepY hshifts
    hreg hlower hjets htests hnegative Φ hmodels hscale
    hsep hrad hlength hcubic hcapRoom hHeight hMT hRT hNten A Bint hA hab hBint
    Yc ErrorTotal Main
  have hT : 0 < T := zero_lt_one.trans_le hTone
  have hNreal : (2:ℝ) ≤ N := by exact_mod_cast hNtwo
  have hNp : (0:ℝ) < N := by linarith only [hNreal]
  have hNOne : (1:ℝ) ≤ N := by linarith only [hNreal]
  have hRp : 0 < R := zero_lt_one.trans_le hR
  obtain ⟨Qbase,kmax,Kmesh,Usel,hM,hRN,hNR,hNM,hRM,hNcube,hpad,hquartic,hquadratic,
    hsmall,hQbase,hBaseHi,hNQ,hQcap,hkmax,hK,hvalid,hmono,hbuffer,hmore⟩ :=
    hselect N M R hNOne hR hsep hrad hlength hcubic hcapRoom
  clear hselect
  let Q := fun k : ℕ => Qbase*2^k
  have hMtwo : 2 ≤ M := hNreal.trans hNM
  have hNpos : 0 < N := by omega
  have hUband : Usrc*T/M^2 ≤ 1 := by
    apply (div_le_iff₀ (sq_pos_of_pos hM)).mpr
    simp only [one_mul]
    apply (mul_le_mul_iff_left₀ hM).mp
    calc
      (Usrc*T)*M = (Usrc*M)*T := by ring
      _ ≤ (Cbudget*M)*T :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hUbudget hM.le) hT.le
      _ ≤ ((N:ℝ)*R^2)*T := mul_le_mul_of_nonneg_right hHeight hT.le
      _ = M^2*M := by nlinarith only [hscale]
  have hvalidSource : ∀ k ≤ kmax,
      63*(Usrc/(2*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      1 ≤ Usel k ∧ Bselect^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
      R ≤ (Q k:ℝ) ∧ (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      (Q k:ℝ) ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
      Δbase*(Q k:ℝ)/(N:ℝ)+
        quarticNonlinearResidualConstant σ δ*(2*(Q k:ℝ))/(N:ℝ) ≤ 1/2 ∧
      Δbase*(Q k:ℝ)/(N:ℝ) < 1/2 := by
    intro k hk
    obtain ⟨hsource,hmesh,hU,hwrap,hRQ,hupper,hQN,hUR,hmin,hD,hDelta⟩ := hvalid k hk
    refine ⟨hsource,hmesh,hU,hwrap,hRQ,hupper,hQN,hUR,hmin,?_,hDelta⟩
    convert hD using 1
    dsimp only [Dbase,Δbase]
    ring
  have hraw :=
    hfiniteT Fsrc rshift sshift Y n N Qbase kmax Kmesh Usel R Jsep
      (d:=d) (Wmax:=Wmax) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
      (Cbase:=Cbase) (Cmesh:=Cmesh) (qcap:=qcap)
      hK hNlink hd hW (hWsmall.trans hwcap)
      ((mul_le_mul_of_nonneg_left hWsmall (by positivity)).trans hwsmall)
      hT hMtwo hNpos hδ hR hRM hJsep hJM hNM hWJ
      hy hsepY hshifts hreg hlower hjets htests hnegative hmodels
      hscale hpad hquartic hquadratic hBcut hBsSize hcutMargin hNten
      (Or.inr ⟨by linarith only [hMtwo],hNM.trans hMT,hRT⟩)
      hQbase hNQ hsmall hNR hRN hNcube hNreal
      (by simpa only [Cphys,add_assoc,show (1:ℝ)+2=3 by norm_num] using hanchor)
      hUband hsize hcurv hvalidSource (fun k _ => hmono k) hbuffer
      hTone hMT hδzero hCm hBaseHi hkmax hqcap hQcap hmore A Bint hA hab hBint
  clear hfiniteT
  have heps : 2*εloss=ε/2 := by dsimp only [εloss]; ring
  exact double_difference_five_monomial_absorption
    (Ctri:=Ctri) (Dtype:=Dtype) (Cdelta:=Cdelta) (C₀:=C₀)
    (Cmain:=Cmain) (Bselect:=Bselect) (Ctail:=Ctail) (Ctotal:=Ctotal) (ε:=ε)
    hUsrc (Nat.cast_nonneg _) hM hNp hRp hJsep.le hT hTotal habsorb.2.2
    (by simpa only [heps] using hraw)

private theorem double_difference_capped_comparable_radius_budgets
    {M N R S T V D C : ℝ} (hM : 0 < M) (hN : 0 < N)
    (hR : 0 < R) (hD : 1 ≤ D) (hC : 1 ≤ C)
    (hSR : S ≤ D*R) (hRS : R ≤ D*S) (hTV : T ≤ D*V)
    (hRlow : C*D^7 ≤ R)
    (hRN : (C*D^7)*R ≤ N) (hNR : (C*D^7)*N ≤ R^2)
    (hNM : (C*D^7)*N ≤ M) (hCubic : (C*D^7)*N^3 ≤ M*R^2)
    (hCap : (C*D^7)*N*R ≤ M) (hHeight : (C*D^7)*M ≤ N*R^2)
    (hMT : (C*D^7)*M ≤ T) (hRT : (C*D^7)*R^2 ≤ T)
    (hTen : (C*D^7)*N^10 ≤ M^3*R^7) :
    1 ≤ S ∧ C*S ≤ N ∧ C*N ≤ S^2 ∧ C*N ≤ M ∧
      C*N^3 ≤ M*S^2 ∧ C*N*S ≤ M ∧ C*M ≤ N*S^2 ∧
      M ≤ V ∧ S^2 ≤ V ∧ N^10 ≤ M^3*S^7 := by
  have hDp := zero_lt_one.trans_le hD
  have hCp := zero_lt_one.trans_le hC
  have hpow (i : ℕ) (hi : i ≤ 7) : C*D^i ≤ C*D^7 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hi) hCp.le
  have hplain (i : ℕ) (hi : i ≤ 7) : D^i ≤ C*D^7 :=
    (le_mul_of_one_le_left (pow_nonneg hDp.le i) hC).trans (hpow i hi)
  have hB : C ≤ C*D^7 := by simpa only [pow_zero,mul_one] using hpow 0 (by omega)
  have hDb : D ≤ C*D^7 := by simpa only [pow_one] using hplain 1 (by omega)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hh := hDb.trans (hRlow.trans hRS)
    nlinarith only [hh,hDp]
  · calc
      _ ≤ C*(D*R) := mul_le_mul_of_nonneg_left hSR hCp.le
      _ = (C*D^1)*R := by ring
      _ ≤ (C*D^7)*R := mul_le_mul_of_nonneg_right (hpow 1 (by omega)) hR.le
      _ ≤ N := hRN
  · apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hDp)).mp
    calc
      _ = (C*D^2)*N := by ring
      _ ≤ (C*D^7)*N := mul_le_mul_of_nonneg_right (hpow 2 (by omega)) hN.le
      _ ≤ R^2 := hNR
      _ ≤ (D*S)^2 := pow_le_pow_left₀ hR.le hRS 2
      _ = _ := by ring
  · exact (mul_le_mul_of_nonneg_right hB hN.le).trans hNM
  · apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hDp)).mp
    calc
      _ = (C*D^2)*N^3 := by ring
      _ ≤ (C*D^7)*N^3 := mul_le_mul_of_nonneg_right (hpow 2 (by omega)) (by positivity)
      _ ≤ M*R^2 := hCubic
      _ ≤ M*(D*S)^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le hRS 2) hM.le
      _ = _ := by ring
  · calc
      _ ≤ C*N*(D*R) := mul_le_mul_of_nonneg_left hSR (by positivity)
      _ = (C*D^1)*N*R := by ring
      _ ≤ (C*D^7)*N*R :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hpow 1 (by omega)) hN.le) hR.le
      _ ≤ M := hCap
  · apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hDp)).mp
    calc
      _ = (C*D^2)*M := by ring
      _ ≤ (C*D^7)*M := mul_le_mul_of_nonneg_right (hpow 2 (by omega)) hM.le
      _ ≤ N*R^2 := hHeight
      _ ≤ N*(D*S)^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le hRS 2) hN.le
      _ = _ := by ring
  · apply (mul_le_mul_iff_right₀ hDp).mp
    exact ((mul_le_mul_of_nonneg_right hDb hM.le).trans hMT).trans hTV
  · apply (mul_le_mul_iff_right₀ hDp).mp
    have hSnon : 0 ≤ S := by
      have hh : 0 < D*S := hR.trans_le hRS
      exact (pos_of_mul_pos_right hh hDp.le).le
    calc
      _ ≤ D*(D*R)^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hSnon hSR 2) hDp.le
      _ = D^3*R^2 := by ring
      _ ≤ (C*D^7)*R^2 := mul_le_mul_of_nonneg_right (hplain 3 (by omega)) (sq_nonneg R)
      _ ≤ T := hRT
      _ ≤ D*V := hTV
  · apply (mul_le_mul_iff_right₀ (pow_pos hDp 7)).mp
    calc
      _ ≤ (C*D^7)*N^10 :=
        mul_le_mul_of_nonneg_right (hplain 7 le_rfl) (pow_nonneg hN.le 10)
      _ ≤ M^3*R^7 := hTen
      _ ≤ M^3*(D*S)^7 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le hRS 7) (pow_nonneg hM.le 3)
      _ = _ := by ring

private theorem double_difference_capped_radius_error_bound
    {Ysmall Y M N R S D : ℝ}
    (hYsmall : 0 ≤ Ysmall) (hY : Ysmall ≤ Y) (hM : 0 < M) (hN : 0 < N)
    (hR : 0 < R) (hS : 0 < S) (hD : 1 ≤ D) (hSR : S ≤ D*R) (hRS : R ≤ D*S) :
    Ysmall*M/Real.sqrt N+Ysmall*M*S^2/N^2+
      Ysmall*N^2*S^2/M+Ysmall*N*(N/S)^((2:ℝ)/3) ≤
    D^2*(Y*M/Real.sqrt N+Y*M*R^2/N^2+
      Y*N^2*R^2/M+Y*N*(N/R)^((2:ℝ)/3)) := by
  have hY0 := hYsmall.trans hY
  have hbase := upperOriginal_upper_radius_error_bound hYsmall hY hM hN hR hS hD hSR hRS
  have hSq := (upperOriginal_comparable_radius_powers hN hR hS hD hSR hRS).1
  have hnew : Ysmall*N^2*S^2/M ≤ D^2*(Y*N^2*R^2/M) := by
    calc
      _ ≤ Y*N^2*(D^2*R^2)/M := by gcongr
      _ = _ := by ring
  nlinarith only [hbase,hnew]

private theorem double_difference_capped_radius_main_bound
    {Ysmall Y M N R S D J T V : ℝ}
    (hYsmall : 0 ≤ Ysmall) (hY : Ysmall ≤ Y) (hM : 0 < M) (hN : 0 < N)
    (hR : 0 < R) (hS : 0 < S) (hD : 1 ≤ D) (hJ : 0 ≤ J)
    (hT : 0 < T) (hV : 0 < V)
    (hSR : S ≤ D*R) (hRS : R ≤ D*S) (hVT : V ≤ D*T) :
    Ysmall^11*M^10*N^2/S^4+Ysmall^11*M^11*N^2/S^7+
      Ysmall^11*J*M^10/S^2+Ysmall^11*J*M^11/S^5+
      Ysmall^12*M^10*S^2/N^2*(S/N)^((2:ℝ)/3)*(V/M^2)^((4:ℝ)/3) ≤
    D^8*(Y^11*M^10*N^2/R^4+Y^11*M^11*N^2/R^7+
      Y^11*J*M^10/R^2+Y^11*J*M^11/R^5+
      Y^12*M^10*R^2/N^2*(R/N)^((2:ℝ)/3)*(T/M^2)^((4:ℝ)/3)) := by
  have hY0 := hYsmall.trans hY
  have hD0 := zero_le_one.trans hD
  have hInv (j : ℕ) : 1/S^j ≤ D^j/R^j := by
    apply (div_le_div_iff₀ (pow_pos hS j) (pow_pos hR j)).mpr
    simpa only [one_mul,mul_pow] using pow_le_pow_left₀ hR.le hRS j
  have hi₄ := hInv 4
  have hi₇ := hInv 7
  have hi₂ := hInv 2
  have hi₅ := hInv 5
  obtain ⟨hSq,_,_,hFor⟩ := upperOriginal_comparable_radius_powers hN hR hS hD hSR hRS
  have hD48 : D^4 ≤ D^8 := pow_le_pow_right₀ hD (by norm_num)
  have hD78 : D^7 ≤ D^8 := pow_le_pow_right₀ hD (by norm_num)
  have hD28 : D^2 ≤ D^8 := pow_le_pow_right₀ hD (by norm_num)
  have hD58 : D^5 ≤ D^8 := pow_le_pow_right₀ hD (by norm_num)
  have hTr : (V/M^2)^((4:ℝ)/3) ≤ D^2*(T/M^2)^((4:ℝ)/3) := by
    have hDe : D^((4:ℝ)/3) ≤ D^2 := by
      rw [←Real.rpow_natCast D 2]
      exact Real.rpow_le_rpow_of_exponent_le hD (by norm_num)
    calc
      _ ≤ (D*(T/M^2))^((4:ℝ)/3) := by
        apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
        simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hVT (sq_nonneg M)
      _ = D^((4:ℝ)/3)*(T/M^2)^((4:ℝ)/3) := Real.mul_rpow hD0 (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hDe (by positivity)
  have h₁ : Ysmall^11*M^10*N^2/S^4 ≤ D^8*(Y^11*M^10*N^2/R^4) := by
    calc
      _ = (Ysmall^11*M^10*N^2)*(1/S^4) := by ring
      _ ≤ (Y^11*M^10*N^2)*(D^4/R^4) := by gcongr
      _ = D^4*(Y^11*M^10*N^2/R^4) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD48 (by positivity)
  have h₂ : Ysmall^11*M^11*N^2/S^7 ≤ D^8*(Y^11*M^11*N^2/R^7) := by
    calc
      _ = (Ysmall^11*M^11*N^2)*(1/S^7) := by ring
      _ ≤ (Y^11*M^11*N^2)*(D^7/R^7) := by gcongr
      _ = D^7*(Y^11*M^11*N^2/R^7) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD78 (by positivity)
  have h₃ : Ysmall^11*J*M^10/S^2 ≤ D^8*(Y^11*J*M^10/R^2) := by
    calc
      _ = (Ysmall^11*J*M^10)*(1/S^2) := by ring
      _ ≤ (Y^11*J*M^10)*(D^2/R^2) := by gcongr
      _ = D^2*(Y^11*J*M^10/R^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD28 (by positivity)
  have h₄ : Ysmall^11*J*M^11/S^5 ≤ D^8*(Y^11*J*M^11/R^5) := by
    calc
      _ = (Ysmall^11*J*M^11)*(1/S^5) := by ring
      _ ≤ (Y^11*J*M^11)*(D^5/R^5) := by gcongr
      _ = D^5*(Y^11*J*M^11/R^5) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD58 (by positivity)
  have h₅ :
      Ysmall^12*M^10*S^2/N^2*(S/N)^((2:ℝ)/3)*(V/M^2)^((4:ℝ)/3) ≤
      D^8*(Y^12*M^10*R^2/N^2*(R/N)^((2:ℝ)/3)*(T/M^2)^((4:ℝ)/3)) := by
    calc
      _ ≤ (Y^12*M^10*(D^2*R^2)/N^2)*
          (D*(R/N)^((2:ℝ)/3))*(D^2*(T/M^2)^((4:ℝ)/3)) := by gcongr
      _ = D^5*(Y^12*M^10*R^2/N^2*(R/N)^((2:ℝ)/3)*(T/M^2)^((4:ℝ)/3)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD58 (by positivity)
  calc
    _ ≤ D^8*(Y^11*M^10*N^2/R^4)+D^8*(Y^11*M^11*N^2/R^7)+
        D^8*(Y^11*J*M^10/R^2)+D^8*(Y^11*J*M^11/R^5)+
        D^8*(Y^12*M^10*R^2/N^2*(R/N)^((2:ℝ)/3)*(T/M^2)^((4:ℝ)/3)) :=
      add_le_add (add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄) h₅
    _ = _ := by ring

private theorem approximateModelPhase_enlarged_double_capped_quantitative
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ w₀ B C : ℝ, 0 < δ ∧ 0 < w₀ ∧ w₀ ≤ 1/4 ∧ 1 ≤ B ∧ 1 ≤ C ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1 ≤ M →
        Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
      ∃ Fext : ℝ → ℝ,
        (∀ (X : ℝ) (a b : ℕ), M ≤ (a:ℝ) → (b:ℝ) ≤ 2*M →
          ‖Expdb.exponentialSumAt F X M a b-
            Expdb.exponentialSumAt Fext X M a b‖ ≤ 6) ∧
        ∀ (T : ℝ) (Y : Finset ℝ) (rshift sshift : ℝ → ℝ) (n N : ℕ)
          (R Jsep d Wmax : ℝ),
          C ≤ T → N=8*n → 2 ≤ N → B ≤ R →
          0 < d → 0 ≤ Wmax → Wmax ≤ w₀ → 0 < Jsep → Jsep ≤ M → Wmax*Jsep ≤ 1 →
          (∀ y∈Y, y∈Icc (1:ℝ) 2) →
          (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
          (∀ y∈Y, 0 < rshift y ∧ 0 < sshift y ∧
            rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
          T*(N:ℝ)*R^2=M^3 →
          B*R ≤ N → B*(N:ℝ) ≤ R^2 → B*(N:ℝ) ≤ M →
          B*(N:ℝ)^3 ≤ M*R^2 → B*(N:ℝ)*R ≤ M →
          B*M ≤ (N:ℝ)*R^2 → B*M ≤ T → B*R^2 ≤ T →
          B*(N:ℝ)^10 ≤ M^3*R^7 →
          ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
          (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
          let Yc := (Y.card:ℝ)
          let ErrorTotal := Yc*M/Real.sqrt (N:ℝ)+Yc*M*R^2/(N:ℝ)^2+
            Yc*(N:ℝ)^2*R^2/M+Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
          let Main := Yc^11*M^10*(N:ℝ)^2/R^4+Yc^11*M^11*(N:ℝ)^2/R^7+
            Yc^11*Jsep*M^10/R^2+Yc^11*Jsep*M^11/R^5+
            Yc^12*M^10*R^2/(N:ℝ)^2*(R/(N:ℝ))^((2:ℝ)/3)*(T/M^2)^((4:ℝ)/3)
          (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),
            (𝐞 (T*(Fext ((j:ℝ)/M)-Fext ((j:ℝ)/M+rshift y)-
              Fext ((j:ℝ)/M+sshift y)+Fext ((j:ℝ)/M+rshift y+sshift y))/d):ℂ)‖)^12 ≤
            C*T^ε*(Main+ErrorTotal^12) := by
  classical
  have hσtwo : 0 < σ+2 := by linarith only [hσ]
  let δmodel := min (modelPhaseThirdLower (σ+2)) 1/2
  have hmin : 0 < min (modelPhaseThirdLower (σ+2)) 1 :=
    lt_min (modelPhaseThirdLower_pos hσtwo) zero_lt_one
  have hδmodel : 0 < δmodel := half_pos hmin
  have hδmodelCap : δmodel ≤ min (modelPhaseThirdLower (σ+2)) 1 := by
    dsimp only [δmodel]
    linarith only [hmin]
  obtain ⟨δ,wsrc,a,c,U,hδ,hwsrc,hwsrcCap,ha,hc,hU,_hsmall,hanchor,hsource⟩ :=
    approximateModelPhase_enlarged_double_common_scale_source hσ hδmodel
  have hanchor' : c ≤ 4*modelPhaseThirdLower (σ+2)/((σ+2)*((σ+2)+1)+3) := by
    simpa only [add_assoc,show (2:ℝ)+1=3 by norm_num] using hanchor
  obtain ⟨Cbudget,wquant,hCbudget,hwquant,_hwquantCap,hquant⟩ :=
    eventually_double_difference_uniform_capped_source_bound
      hc hU hσtwo hδmodel.le hδmodelCap hε hanchor'
  obtain ⟨Tcut,hTcut⟩ := Filter.eventually_atTop.mp hquant
  let G := σ*(σ+1)
  have hG : 0 < G := by dsimp only [G]; positivity
  let D := 2+2*G+1/G
  have hD : 1 ≤ D := by
    dsimp only [D]
    have hi : 0 < 1/G := by positivity
    linarith only [hG,hi]
  have hDp := zero_lt_one.trans_le hD
  have hDG : 1 ≤ D*G := by
    have hi : (1/G)*G=1 := div_mul_cancel₀ 1 hG.ne'
    dsimp only [D]
    nlinarith only [hi,hG,sq_nonneg G]
  have hGD : 2*G ≤ D := by
    dsimp only [D]
    have hi : 0 < 1/G := by positivity
    linarith only [hi]
  let B := Cbudget*D^7
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le hCbudget (one_le_pow₀ hD)
  let Cap := 4/a+3
  have hCap : 1 ≤ Cap := by
    dsimp only [Cap]
    have hh : 0 < 4/a := by positivity
    linarith only [hh]
  let K := (2*G)^ε*D^24
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  let C := max 1 (max (Tcut/G) (Cap^12*K))
  have hC : 1 ≤ C := le_max_left _ _
  have hCcut : Tcut/G ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCK : Cap^12*K ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨δ,min wsrc wquant,B,C,hδ,lt_min hwsrc hwquant,
    (min_le_left _ _).trans hwsrcCap,hB,hC,?_⟩
  intro M F hM hF
  obtain ⟨Fext,_hreg,hsharp,hcolors⟩ := hsource M F hM hF
  refine ⟨Fext,hsharp,?_⟩
  intro T Y rshift sshift n N R Jsep d Wmax
    hThreshold hN8 hN2 hRlow hd hW hWcap hJsep hJM hWJ hy hsep hshifts
    hphase hRN hNR hNM hCubic hCapRoom hHeight hMT hRT hTen
    A Bint hA hab hBint Yc ErrorTotal Main
  have hMp : 0 < M := zero_lt_one.trans_le hM
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRp : 0 < R := zero_lt_one.trans_le (hB.trans hRlow)
  have hTp : 0 < T := zero_lt_one.trans_le (hC.trans hThreshold)
  have hYc : 0 ≤ Yc := Nat.cast_nonneg _
  have hMain : 0 ≤ Main := by
    dsimp only [Main]
    clear * - hYc hMp hNp hRp hJsep hTp
    positivity
  have hError : 0 ≤ ErrorTotal := by
    dsimp only [ErrorTotal]
    clear * - hYc hMp hNp hRp
    positivity
  have hMass : 0 ≤ Main+ErrorTotal^12 := add_nonneg hMain (pow_nonneg hError 12)
  let color := fun y : ℝ => ⌊y/a⌋
  let z := fun y : ℝ => (‖∑ l∈Finset.Ioc (A y) (Bint y),
    (𝐞 (T*(Fext ((l:ℝ)/M)-Fext ((l:ℝ)/M+rshift y)-
      Fext ((l:ℝ)/M+sshift y)+Fext ((l:ℝ)/M+rshift y+sshift y))/d):ℂ)‖:ℂ)
  have hzNorm (V : Finset ℝ) :
      ‖∑ y∈V,z y‖ = ∑ y∈V,‖∑ l∈Finset.Ioc (A y) (Bint y),
        (𝐞 (T*(Fext ((l:ℝ)/M)-Fext ((l:ℝ)/M+rshift y)-
          Fext ((l:ℝ)/M+sshift y)+Fext ((l:ℝ)/M+rshift y+sshift y))/d):ℂ)‖ := by
    dsimp only [z]
    rw [←Complex.ofReal_sum]
    exact Complex.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  obtain ⟨hcard,hmoment,hclasses⟩ := hcolors Y id rshift sshift d hd hy (by
    intro y hy'
    obtain ⟨hr,hs,hproduct,hsum⟩ := hshifts y hy'
    exact ⟨hr,hs,hsum.trans (hWcap.trans (min_le_left _ _)),hproduct⟩)
  have hlocal (j : ℤ) (hj : j∈Y.image color) :
      ‖∑ y∈Y.filter (fun y => color y=j),z y‖^12 ≤
        K*T^ε*(Main+ErrorTotal^12) := by
    obtain ⟨y₀,hy₀,_hcolor,hreg,hjets,hlower,htests,hnegative,hscaled⟩ := hclasses j hj
    let γ := G*y₀
    have hy₀range := hy y₀ hy₀
    have hy₀p : 0 < y₀ := zero_lt_one.trans_le hy₀range.1
    have hγ : 0 < γ := mul_pos hG hy₀p
    have hγlo : G ≤ γ := le_mul_of_one_le_right hG.le hy₀range.1
    have hγhi : γ ≤ 2*G := by dsimp only [γ]; nlinarith only [hy₀range.2,hG]
    have hγD := hγhi.trans hGD
    have hDγ : 1 ≤ D*γ := hDG.trans (mul_le_mul_of_nonneg_left hγlo hDp.le)
    let Fsrc := fun w => (1/(σ*(σ+1)*y₀))*Fext w
    let Tnew := T*σ*(σ+1)*y₀
    let Rnew := R*Real.sqrt (1/(σ*(σ+1)*y₀))
    obtain ⟨hTnew,hRnew,hRsq,hnewphase,hmodels⟩ :=
      hscaled T (N:ℝ) R M hTp hRp hphase
    have hTnewEq : Tnew=T*γ := by dsimp only [Tnew,γ,G]; ring
    have hRnewSq : Rnew^2=R^2/γ := by
      simpa only [γ,G,mul_one_div,id_eq] using hRsq
    have hRg : γ*Rnew^2=R^2 := by rw [hRnewSq]; field_simp
    obtain ⟨hSle,hRle⟩ := upperOriginal_normalized_radius_comparable hRp hRnew hD hγD hDγ hRg
    have hTV : T ≤ D*Tnew := by
      rw [hTnewEq]
      calc
        _ ≤ (D*γ)*T := le_mul_of_one_le_left hTp.le hDγ
        _ = _ := by ring
    have hVT : Tnew ≤ D*T := by
      rw [hTnewEq]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hγD hTp.le
    obtain ⟨hRnew1,hnewRN,hnewNR,hnewNM,hnewCubic,hnewCap,hnewHeight,hnewMT,hnewRT,hnewTen⟩ :=
      double_difference_capped_comparable_radius_budgets
        hMp hNp hRp hD hCbudget hSle hRle hTV hRlow
        hRN hNR hNM hCubic hCapRoom hHeight hMT hRT hTen
    have hTnewCut : Tcut ≤ Tnew := by
      rw [hTnewEq]
      exact ((div_le_iff₀ hG).mp (hCcut.trans hThreshold)).trans
        (mul_le_mul_of_nonneg_left hγlo hTp.le)
    let Yj := Y.filter (fun y => color y=j)
    have hYj (y : ℝ) (hy' : y∈Yj) : y∈Y := (Finset.mem_filter.mp hy').1
    have hYjColor (y : ℝ) (hy' : y∈Yj) : color y=j := (Finset.mem_filter.mp hy').2
    let Φ := fun y u =>
      (Fsrc u-Fsrc (u+rshift y)-Fsrc (u+sshift y)+Fsrc (u+rshift y+sshift y))/d
    have hmod (y : ℝ) (hy' : y∈Yj) :
        Expdb.IsApproximateModelPhaseFunction (Φ y) (σ+2) 4 δmodel :=
      (hmodels y (hYj y hy') (hYjColor y hy')).1
    have hq := hTcut Tnew hTnewCut Fsrc rshift sshift Yj n N Rnew Jsep
      (d:=d) (Wmax:=Wmax) (M:=M) hN8 hN2 hRnew1 hd hW (hWcap.trans (min_le_right _ _)) hJsep hJM hWJ
      (fun y hy' => hy y (hYj y hy'))
      (fun y hy' v hv hne => hsep y (hYj y hy') v (hYj v hv) hne)
      (by
        intro y hy'
        obtain ⟨hr,hs,hprod,hsum⟩ := hshifts y (hYj y hy')
        exact ⟨hr.le,hs.le,hprod,hsum⟩)
      hreg hlower hjets htests hnegative hmod hnewphase hnewRN hnewNR hnewNM
      hnewCubic hnewCap hnewHeight hnewMT hnewRT hnewTen A Bint
      (fun y hy' => hA y (hYj y hy')) (fun y hy' => hab y (hYj y hy'))
      (fun y hy' => hBint y (hYj y hy'))
    have hYj0 : (0:ℝ) ≤ Yj.card := Nat.cast_nonneg _
    have hYjCard : (Yj.card:ℝ) ≤ Yc := by
      change ((Y.filter (fun y => color y=j)).card:ℝ) ≤ (Y.card:ℝ)
      exact_mod_cast (Finset.card_filter_le Y (fun y => color y=j))
    let Enew := (Yj.card:ℝ)*M/Real.sqrt (N:ℝ)+
      (Yj.card:ℝ)*M*Rnew^2/(N:ℝ)^2+
      (Yj.card:ℝ)*(N:ℝ)^2*Rnew^2/M+
      (Yj.card:ℝ)*(N:ℝ)*((N:ℝ)/Rnew)^((2:ℝ)/3)
    let MainNew := (Yj.card:ℝ)^11*M^10*(N:ℝ)^2/Rnew^4+
      (Yj.card:ℝ)^11*M^11*(N:ℝ)^2/Rnew^7+
      (Yj.card:ℝ)^11*Jsep*M^10/Rnew^2+(Yj.card:ℝ)^11*Jsep*M^11/Rnew^5+
      (Yj.card:ℝ)^12*M^10*Rnew^2/(N:ℝ)^2*
        (Rnew/(N:ℝ))^((2:ℝ)/3)*(Tnew/M^2)^((4:ℝ)/3)
    have hEnew : Enew ≤ D^2*ErrorTotal :=
      double_difference_capped_radius_error_bound hYj0 hYjCard hMp hNp hRp hRnew hD hSle hRle
    have hMainNew : MainNew ≤ D^8*Main :=
      double_difference_capped_radius_main_bound
        hYj0 hYjCard hMp hNp hRp hRnew hD hJsep.le hTp hTnew hSle hRle hVT
    have hEnew0 : 0 ≤ Enew := by
      dsimp only [Enew]
      clear * - hYj0 hMp hNp hRnew
      positivity
    have hMainNew0 : 0 ≤ MainNew := by
      dsimp only [MainNew]
      clear * - hYj0 hMp hNp hRnew hJsep hTnew
      positivity
    have hEpow : Enew^12 ≤ D^24*ErrorTotal^12 := by
      calc
        _ ≤ (D^2*ErrorTotal)^12 := pow_le_pow_left₀ hEnew0 hEnew 12
        _ = _ := by rw [mul_pow,←pow_mul]
    have hMainPow : MainNew ≤ D^24*Main :=
      hMainNew.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hD (by norm_num : 8 ≤ 24)) hMain)
    have hTotal : MainNew+Enew^12 ≤ D^24*(Main+ErrorTotal^12) := by
      calc
        _ ≤ D^24*Main+D^24*ErrorTotal^12 := add_le_add hMainPow hEpow
        _ = _ := (mul_add _ _ _).symm
    have hTpow : Tnew^ε ≤ (2*G)^ε*T^ε := by
      rw [hTnewEq,Real.mul_rpow hTp.le hγ.le]
      calc
        _ ≤ T^ε*(2*G)^ε :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hγ.le hγhi hε.le)
            (Real.rpow_nonneg hTp.le _)
        _ = _ := mul_comm _ _
    rw [hzNorm]
    calc
      _ = (∑ y∈Yj, ‖∑ l∈Finset.Ioc (A y) (Bint y),
          (𝐞 (Tnew*Φ y ((l:ℝ)/M)):ℂ)‖)^12 := by
        congr 1
        apply Finset.sum_congr rfl
        intro y hy'
        congr 1
        apply Finset.sum_congr rfl
        intro l _
        apply congrArg (fun x : ℝ => (𝐞 x:ℂ))
        exact ((hmodels y (hYj y hy') (hYjColor y hy')).2 (l:ℝ)).symm
      _ ≤ Tnew^ε*(MainNew+Enew^12) := hq
      _ ≤ ((2*G)^ε*T^ε)*(D^24*(Main+ErrorTotal^12)) :=
        mul_le_mul hTpow hTotal (add_nonneg hMainNew0 (pow_nonneg hEnew0 12))
          (mul_nonneg (Real.rpow_nonneg (by positivity) ε) (Real.rpow_nonneg hTp.le ε))
      _ = _ := by dsimp only [K]; ac_rfl
  have hKmass : 0 ≤ K*T^ε*(Main+ErrorTotal^12) :=
    mul_nonneg (mul_nonneg hK (Real.rpow_nonneg hTp.le ε)) hMass
  have hcolorSum :
      (∑ j∈Y.image color, ‖∑ y∈Y.filter (fun y => color y=j),z y‖^12) ≤
        Cap*(K*T^ε*(Main+ErrorTotal^12)) := by
    calc
      _ ≤ ∑ _j∈Y.image color,K*T^ε*(Main+ErrorTotal^12) := Finset.sum_le_sum hlocal
      _ = ((Y.image color).card:ℝ)*(K*T^ε*(Main+ErrorTotal^12)) := by
        rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard hKmass
  calc
    _ = ‖∑ y∈Y,z y‖^12 := congrArg (fun x : ℝ => x^12) (hzNorm Y).symm
    _ ≤ Cap^11*∑ j∈Y.image color,‖∑ y∈Y.filter (fun y => color y=j),z y‖^12 := hmoment z
    _ ≤ Cap^11*(Cap*(K*T^ε*(Main+ErrorTotal^12))) :=
      mul_le_mul_of_nonneg_left hcolorSum (pow_nonneg (zero_le_one.trans hCap) 11)
    _ = (Cap^12*K)*(T^ε*(Main+ErrorTotal^12)) := by
      rw [show Cap^12=Cap^11*Cap from pow_succ Cap 11]
      ac_rfl
    _ ≤ C*(T^ε*(Main+ErrorTotal^12)) :=
      mul_le_mul_of_nonneg_right hCK (mul_nonneg (Real.rpow_nonneg hTp.le ε) hMass)
    _ = _ := (mul_assoc _ _ _).symm

private theorem double_difference_actual_range_le_int_Ioc
    (F : ℝ → ℝ) (X : ℝ) {M : ℝ} (hM : M≠0)
    (a L r s k : ℕ) (hk : 0<k) (hrs : r+s≤L) :
    ‖∑ j∈Finset.range (L+1-r-s),
      (𝐞 (X*(F (((a:ℝ)+j)/M)-F (((a:ℝ)+j+r)/M)-
        F (((a:ℝ)+j+s)/M)+F (((a:ℝ)+j+r+s)/M))):ℂ)‖ ≤
      1+‖∑ j∈Finset.Ioc (a:ℤ) ((a+(L-r-s):ℕ):ℤ),
        (𝐞 ((X*k/M^2)*(F ((j:ℝ)/M)-F ((j:ℝ)/M+(r:ℝ)/M)-
          F ((j:ℝ)/M+(s:ℝ)/M)+F ((j:ℝ)/M+(r:ℝ)/M+(s:ℝ)/M))/
            ((k:ℝ)/M^2)):ℂ)‖ := by
  have hkR : (k:ℝ)≠0 := by exact_mod_cast hk.ne'
  have hd : (k:ℝ)/M^2≠0 := div_ne_zero hkR (pow_ne_zero 2 hM)
  have hcoeff (q : ℝ) : (X*k/M^2)*(q/((k:ℝ)/M^2))=X*q := by
    calc
      _ = X*((q/((k:ℝ)/M^2))*((k:ℝ)/M^2)) := by ring
      _ = _ := by rw [div_mul_cancel₀ q hd]
  let Φ := fun u => (F u-F (u+(r:ℝ)/M)-F (u+(s:ℝ)/M)+
    F (u+(r:ℝ)/M+(s:ℝ)/M))/((k:ℝ)/M^2)
  have heq :
      (∑ j∈Finset.range (L+1-r-s),
        (𝐞 (X*(F (((a:ℝ)+j)/M)-F (((a:ℝ)+j+r)/M)-
          F (((a:ℝ)+j+s)/M)+F (((a:ℝ)+j+r+s)/M))):ℂ)) =
        Expdb.exponentialSumAt Φ (X*k/M^2) M a (a+(L-r-s)) := by
    rw [exponentialSumAt_eq_range,show L-r-s+1=L+1-r-s by omega]
    apply Finset.sum_congr rfl
    intro j _
    apply congrArg (fun t : ℝ => (𝐞 t:ℂ))
    dsimp only [Φ]
    rw [hcoeff]
    simp only [add_div]
  rw [heq]
  calc
    _ ≤ 1+‖∑ j∈Finset.Ioc (a:ℤ) ((a+(L-r-s):ℕ):ℤ),
        Expdb.oscillatory Φ (X*k/M^2) M j‖ :=
      upperOriginal_norm_exponentialSumAt_le_int_Ioc Φ (X*k/M^2) M
        a (a+(L-r-s)) (Nat.le_add_right _ _)
    _ = _ := by
      apply congrArg (fun z : ℂ => 1+‖z‖)
      apply Finset.sum_congr rfl
      intro j _
      unfold Expdb.oscillatory
      apply congrArg (fun t : ℝ => (𝐞 t:ℂ))
      exact (mul_div_assoc _ _ _).symm

private theorem double_difference_product_dyadic_actual_family
    (F : ℝ → ℝ) (X : ℝ) {M : ℝ} (hM : 0<M)
    (a L H K k : ℕ) (hk : 0<k) (ha : M≤(a:ℝ)) (hb : ((a+L:ℕ):ℝ)≤2*M) :
    let Pairs := (Finset.Icc 1 (H-1)) ×ˢ (Finset.Icc 1 (K-1))
    let Products := Pairs.image (fun p => p.1*p.2)
    ∀ pick : ℕ → ℕ × ℕ,
      (∀ l∈Products, pick l∈Pairs ∧ (pick l).1*(pick l).2=l) →
    let Block := (Finset.Ico k (2*k)).filter (fun l => l∈Products)
    let Kept := Block.filter (fun l => (pick l).1+(pick l).2≤L)
    let Y := Kept.image (fun l : ℕ => (l:ℝ)/(k:ℝ))
    let rshift := fun y : ℝ => ((pick ⌊(k:ℝ)*y⌋₊).1:ℝ)/M
    let sshift := fun y : ℝ => ((pick ⌊(k:ℝ)*y⌋₊).2:ℝ)/M
    let Bint := fun y : ℝ =>
      ((a+(L-(pick ⌊(k:ℝ)*y⌋₊).1-(pick ⌊(k:ℝ)*y⌋₊).2):ℕ):ℤ)
    Y.card≤k ∧
      (∀ y∈Y, y∈Icc (1:ℝ) 2) ∧
      (∀ y∈Y, ∀ z∈Y, y≠z → 1≤(k:ℝ)*|y-z|) ∧
      (∀ y∈Y, 0<rshift y ∧ 0<sshift y ∧
        rshift y*sshift y=((k:ℝ)/M^2)*y ∧ rshift y+sshift y≤((H:ℝ)+K)/M) ∧
      ⌈M⌉≤(a:ℤ) ∧ (∀ y∈Y, (a:ℤ)≤Bint y) ∧
      (∀ y∈Y, Bint y≤⌊2*M⌋) ∧
      (∑ l∈Block,‖∑ j∈Finset.range (L+1-(pick l).1-(pick l).2),
        (𝐞 (X*(F (((a:ℝ)+j)/M)-F (((a:ℝ)+j+(pick l).1)/M)-
          F (((a:ℝ)+j+(pick l).2)/M)+
          F (((a:ℝ)+j+(pick l).1+(pick l).2)/M))):ℂ)‖) ≤
        (Y.card:ℝ)+∑ y∈Y,‖∑ j∈Finset.Ioc (a:ℤ) (Bint y),
          (𝐞 ((X*k/M^2)*(F ((j:ℝ)/M)-F ((j:ℝ)/M+rshift y)-
            F ((j:ℝ)/M+sshift y)+F ((j:ℝ)/M+rshift y+sshift y))/
              ((k:ℝ)/M^2)):ℂ)‖ := by
  classical
  intro Pairs Products pick hpick Block Kept Y rshift sshift Bint
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  have hinj : Function.Injective (fun l : ℕ => (l:ℝ)/(k:ℝ)) := by
    intro l m hlm
    exact_mod_cast (div_left_inj' hkR.ne').mp hlm
  have hcard : Y.card=Kept.card := Finset.card_image_of_injOn hinj.injOn
  have hcardK : Kept.card≤k := by
    calc
      _ ≤ Block.card := Finset.card_filter_le _ _
      _ ≤ (Finset.Ico k (2*k)).card := Finset.card_filter_le _ _
      _ = k := by rw [Nat.card_Ico]; omega
  have hfloor (l : ℕ) : ⌊(k:ℝ)*((l:ℝ)/(k:ℝ))⌋₊=l := by
    rw [show (k:ℝ)*((l:ℝ)/(k:ℝ))=(l:ℝ) by field_simp]
    exact Nat.floor_natCast l
  have hKept (l : ℕ) (hl : l∈Kept) :
      l∈Finset.Ico k (2*k) ∧ l∈Products ∧ (pick l).1+(pick l).2≤L := by
    have hh := Finset.mem_filter.mp hl
    have hh' := Finset.mem_filter.mp hh.1
    exact ⟨hh'.1,hh'.2,hh.2⟩
  have hgeom := HuxleyRationalPhase.difference_family_dyadic_parameter_geometry hkR
  refine ⟨hcard.trans_le hcardK,?_,?_,?_,?_,?_,?_,?_⟩
  · intro y hy
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hy
    have hl' := Finset.mem_Ico.mp (hKept l hl).1
    have hh := hgeom.1 l (by exact_mod_cast hl'.1) (by exact_mod_cast hl'.2.le)
    constructor <;> linarith only [hh.1,hh.2]
  · intro y hy z hz hyz
    obtain ⟨l,_hl,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨m,_hm,rfl⟩ := Finset.mem_image.mp hz
    have hlm : l≠m := fun he => hyz (congrArg (fun n : ℕ => (n:ℝ)/(k:ℝ)) he)
    have hh := hgeom.2 l m hlm
    rw [show (l:ℝ)/(k:ℝ)-1-((m:ℝ)/(k:ℝ)-1)=
      (l:ℝ)/(k:ℝ)-(m:ℝ)/(k:ℝ) by ring] at hh
    exact hh
  · intro y hy
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hpair,hprod⟩ := hpick l (hKept l hl).2.1
    obtain ⟨hr,hs⟩ := Finset.mem_product.mp hpair
    obtain ⟨hr1,hrH⟩ := Finset.mem_Icc.mp hr
    obtain ⟨hs1,hsK⟩ := Finset.mem_Icc.mp hs
    have hrp : (0:ℝ)<(pick l).1 := by exact_mod_cast (show 0<(pick l).1 by omega)
    have hsp : (0:ℝ)<(pick l).2 := by exact_mod_cast (show 0<(pick l).2 by omega)
    dsimp only [rshift,sshift]
    rw [hfloor]
    refine ⟨div_pos hrp hM,div_pos hsp hM,?_,?_⟩
    · have hh : ((pick l).1:ℝ)*(pick l).2=(l:ℝ) := by exact_mod_cast hprod
      field_simp
      nlinarith only [hh]
    · rw [←add_div]
      apply (div_le_div_iff_of_pos_right hM).mpr
      have hrr : ((pick l).1:ℝ)≤H := by exact_mod_cast (show (pick l).1≤H by omega)
      have hss : ((pick l).2:ℝ)≤K := by exact_mod_cast (show (pick l).2≤K by omega)
      exact add_le_add hrr hss
  · apply Int.ceil_le.mpr
    simpa only [Int.cast_natCast] using ha
  · intro y _
    dsimp only [Bint]
    exact_mod_cast (Nat.le_add_right a (L-(pick ⌊(k:ℝ)*y⌋₊).1-(pick ⌊(k:ℝ)*y⌋₊).2))
  · intro y _
    apply Int.le_floor.mpr
    have hh : ((a+(L-(pick ⌊(k:ℝ)*y⌋₊).1-(pick ⌊(k:ℝ)*y⌋₊).2):ℕ):ℝ)≤
        ((a+L:ℕ):ℝ) := by
      exact_mod_cast (show a+(L-(pick ⌊(k:ℝ)*y⌋₊).1-(pick ⌊(k:ℝ)*y⌋₊).2)≤a+L by omega)
    exact hh.trans hb
  · let f := fun l : ℕ => ‖∑ j∈Finset.range (L+1-(pick l).1-(pick l).2),
        (𝐞 (X*(F (((a:ℝ)+j)/M)-F (((a:ℝ)+j+(pick l).1)/M)-
          F (((a:ℝ)+j+(pick l).2)/M)+
          F (((a:ℝ)+j+(pick l).1+(pick l).2)/M))):ℂ)‖
    have hFilter : (∑ l∈Kept,f l)=∑ l∈Block,f l := by
      apply Finset.sum_filter_of_ne
      intro l _ hne
      by_contra hn
      exact hne (by
        dsimp only [f]
        rw [show L+1-(pick l).1-(pick l).2=0 by omega]
        simp only [Finset.range_zero,Finset.sum_empty,norm_zero])
    change (∑ l∈Block,f l)≤_
    rw [←hFilter,hcard,Finset.sum_image hinj.injOn]
    calc
      _ ≤ ∑ l∈Kept,(1+‖∑ j∈Finset.Ioc (a:ℤ) (Bint ((l:ℝ)/(k:ℝ))),
          (𝐞 ((X*k/M^2)*(F ((j:ℝ)/M)-F ((j:ℝ)/M+rshift ((l:ℝ)/(k:ℝ)))-
            F ((j:ℝ)/M+sshift ((l:ℝ)/(k:ℝ)))+
            F ((j:ℝ)/M+rshift ((l:ℝ)/(k:ℝ))+sshift ((l:ℝ)/(k:ℝ))))/
              ((k:ℝ)/M^2)):ℂ)‖) := by
        apply Finset.sum_le_sum
        intro l hl
        dsimp only [f,Bint,rshift,sshift]
        rw [hfloor]
        exact double_difference_actual_range_le_int_Ioc F X hM.ne'
          a L (pick l).1 (pick l).2 k hk (hKept l hl).2.2
      _ = _ := by rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one]

public  theorem approximateModelPhase_enlarged_double_product_correlation_moment
    {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∃ δ w₀ B C : ℝ, 0<δ ∧ 0<w₀ ∧ w₀≤1/4 ∧ 1≤B ∧ 1≤C ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1≤M →
        Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
      ∃ Fext : ℝ → ℝ,
        (∀ (X : ℝ) (a b : ℕ), M≤(a:ℝ) → (b:ℝ)≤2*M →
          ‖Expdb.exponentialSumAt F X M a b-
            Expdb.exponentialSumAt Fext X M a b‖≤6) ∧
        ∀ (X : ℝ) (n N a L H K k : ℕ) (R : ℝ),
          C≤X*k/M^2 → N=8*n → 2≤N → B≤R → 0<k →
          ((H:ℝ)+K)/M≤w₀ → (k:ℝ)≤M → (((H:ℝ)+K)/M)*(k:ℝ)≤1 →
          M≤(a:ℝ) → ((a+L:ℕ):ℝ)≤2*M →
          (X*k/M^2)*(N:ℝ)*R^2=M^3 →
          B*R≤N → B*(N:ℝ)≤R^2 → B*(N:ℝ)≤M →
          B*(N:ℝ)^3≤M*R^2 → B*(N:ℝ)*R≤M →
          B*M≤(N:ℝ)*R^2 → B*M≤X*k/M^2 → B*R^2≤X*k/M^2 →
          B*(N:ℝ)^10≤M^3*R^7 →
          let Pairs := (Finset.Icc 1 (H-1)) ×ˢ (Finset.Icc 1 (K-1))
          let Products := Pairs.image (fun p => p.1*p.2)
          ∀ pick : ℕ → ℕ × ℕ,
            (∀ l∈Products, pick l∈Pairs ∧ (pick l).1*(pick l).2=l) →
          let J := (k:ℝ)
          let E := J*M/Real.sqrt (N:ℝ)+J*M*R^2/(N:ℝ)^2+
            J*(N:ℝ)^2*R^2/M+J*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
          let Main := J^11*M^10*(N:ℝ)^2/R^4+J^11*M^11*(N:ℝ)^2/R^7+
            J^11*J*M^10/R^2+J^11*J*M^11/R^5+
            J^12*M^10*R^2/(N:ℝ)^2*(R/(N:ℝ))^((2:ℝ)/3)*
              ((X*k/M^2)/M^2)^((4:ℝ)/3)
          (∑ l∈(Finset.Ico k (2*k)).filter (fun l => l∈Products),
            ‖∑ j∈Finset.range (L+1-(pick l).1-(pick l).2),
              (𝐞 (X*(Fext (((a:ℝ)+j)/M)-Fext (((a:ℝ)+j+(pick l).1)/M)-
                Fext (((a:ℝ)+j+(pick l).2)/M)+
                Fext (((a:ℝ)+j+(pick l).1+(pick l).2)/M))):ℂ)‖)^12 ≤
            C*(X*k/M^2)^ε*(Main+E^12) := by
  classical
  obtain ⟨δ,w₀,B,C₀,hδ,hw₀,hwcap,hB,hC₀,hsource⟩ :=
    approximateModelPhase_enlarged_double_capped_quantitative hσ hε
  let C := (2:ℝ)^12*C₀
  have hCC₀ : C₀≤C := le_mul_of_one_le_left (zero_le_one.trans hC₀) (by norm_num)
  have hC : 1≤C := hC₀.trans hCC₀
  refine ⟨δ,w₀,B,C,hδ,hw₀,hwcap,hB,hC,?_⟩
  intro M F hM hF
  obtain ⟨Fext,hsharp,hupper⟩ := hsource M F hM hF
  refine ⟨Fext,hsharp,?_⟩
  intro X n N a L H K k R hT hN8 hN2 hR hk hWcap hJM hWJ ha hb hphase
    hRN hNR hNM hCubic hCap hHeight hMT hRT hTen Pairs Products pick hpick J E Main
  have hMp := zero_lt_one.trans_le hM
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hN1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hRp := zero_lt_one.trans_le (hB.trans hR)
  have hJp : 0<J := by
    change (0:ℝ)<k
    exact_mod_cast hk
  let T := X*k/M^2
  have hT1 : 1≤T := hC.trans hT
  have hTp := zero_lt_one.trans_le hT1
  let Block := (Finset.Ico k (2*k)).filter (fun l => l∈Products)
  let Kept := Block.filter (fun l => (pick l).1+(pick l).2≤L)
  let Y := Kept.image (fun l : ℕ => (l:ℝ)/(k:ℝ))
  let rshift := fun y : ℝ => ((pick ⌊(k:ℝ)*y⌋₊).1:ℝ)/M
  let sshift := fun y : ℝ => ((pick ⌊(k:ℝ)*y⌋₊).2:ℝ)/M
  let Bint := fun y : ℝ =>
    ((a+(L-(pick ⌊(k:ℝ)*y⌋₊).1-(pick ⌊(k:ℝ)*y⌋₊).2):ℕ):ℤ)
  obtain ⟨hcard,hY,hsep,hshifts,hA,hAB,hBint,hcorr⟩ :=
    double_difference_product_dyadic_actual_family Fext X hMp a L H K k hk ha hb pick hpick
  have hY0 : (0:ℝ)≤Y.card := Nat.cast_nonneg _
  have hYJ : (Y.card:ℝ)≤J := by
    change (Y.card:ℝ)≤(k:ℝ)
    exact_mod_cast hcard
  let EY := (Y.card:ℝ)*M/Real.sqrt (N:ℝ)+(Y.card:ℝ)*M*R^2/(N:ℝ)^2+
    (Y.card:ℝ)*(N:ℝ)^2*R^2/M+(Y.card:ℝ)*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
  let MainY := (Y.card:ℝ)^11*M^10*(N:ℝ)^2/R^4+
    (Y.card:ℝ)^11*M^11*(N:ℝ)^2/R^7+
    (Y.card:ℝ)^11*J*M^10/R^2+(Y.card:ℝ)^11*J*M^11/R^5+
    (Y.card:ℝ)^12*M^10*R^2/(N:ℝ)^2*(R/(N:ℝ))^((2:ℝ)/3)*(T/M^2)^((4:ℝ)/3)
  have hEY : EY≤E := by
    have hh := double_difference_capped_radius_error_bound hY0 hYJ hMp hNp hRp hRp
      (show (1:ℝ)≤1 from le_rfl) (by rw [one_mul]) (by rw [one_mul])
    simpa only [one_pow,one_mul] using hh
  have hMY : MainY≤Main := by
    have hh := double_difference_capped_radius_main_bound hY0 hYJ hMp hNp hRp hRp
      (show (1:ℝ)≤1 from le_rfl) hJp.le hTp hTp
      (by rw [one_mul]) (by rw [one_mul]) (by rw [one_mul])
    simpa only [one_pow,one_mul] using hh
  have hEY0 : 0≤EY := by
    dsimp only [EY]
    clear * - hY0 hMp hNp hRp
    positivity
  have hE0 : 0≤E := by
    dsimp only [E]
    clear * - hJp hMp hNp hRp
    positivity
  have hMain0 : 0≤Main := by
    dsimp only [Main]
    change 0≤J^11*M^10*(N:ℝ)^2/R^4+J^11*M^11*(N:ℝ)^2/R^7+
      J^11*J*M^10/R^2+J^11*J*M^11/R^5+
      J^12*M^10*R^2/(N:ℝ)^2*(R/(N:ℝ))^((2:ℝ)/3)*(T/M^2)^((4:ℝ)/3)
    clear * - hJp hMp hNp hRp hTp
    positivity
  have hMass0 : 0≤Main+E^12 := add_nonneg hMain0 (pow_nonneg hE0 12)
  have hMass : MainY+EY^12≤Main+E^12 :=
    add_le_add hMY (pow_le_pow_left₀ hEY0 hEY 12)
  let Z := ∑ y∈Y,‖∑ j∈Finset.Ioc (a:ℤ) (Bint y),
    (𝐞 (T*(Fext ((j:ℝ)/M)-Fext ((j:ℝ)/M+rshift y)-
      Fext ((j:ℝ)/M+sshift y)+Fext ((j:ℝ)/M+rshift y+sshift y))/
        ((k:ℝ)/M^2)):ℂ)‖
  have hZ0 : 0≤Z := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hZ : Z^12≤C₀*T^ε*(Main+E^12) := by
    have hW : 0≤((H:ℝ)+K)/M := div_nonneg (by positivity) hMp.le
    have hu := hupper T Y rshift sshift n N R J ((k:ℝ)/M^2) (((H:ℝ)+K)/M)
      (hCC₀.trans hT) hN8 hN2 hR (div_pos hJp (sq_pos_of_pos hMp)) hW hWcap hJp hJM hWJ
      hY hsep hshifts hphase hRN hNR hNM hCubic hCap hHeight hMT hRT hTen
      (fun _ => (a:ℤ)) Bint (fun _ _ => hA) hAB hBint
    exact hu.trans (mul_le_mul_of_nonneg_left hMass
      (mul_nonneg (zero_le_one.trans hC₀) (Real.rpow_nonneg hTp.le ε)))
  have hQ : 1≤C₀*T^ε := by
    calc
      _ = (1:ℝ)*1 := by norm_num
      _ ≤ _ := mul_le_mul hC₀ (Real.one_le_rpow hT1 hε.le)
        zero_le_one (zero_le_one.trans hC₀)
  have hRleN : R≤(N:ℝ) := (le_mul_of_one_le_left hRp.le hB).trans hRN
  have hJE : J≤E := by
    have hratio : 1≤(N:ℝ)/R := (one_le_div hRp).mpr hRleN
    have hp : 1≤((N:ℝ)/R)^((2:ℝ)/3) := Real.one_le_rpow hratio (by norm_num)
    have hu : 1≤(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3) := one_le_mul_of_one_le_of_one_le hN1 hp
    have hlast : J≤J*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3) := by
      simpa only [mul_assoc] using le_mul_of_one_le_right hJp.le hu
    have hother : 0≤J*M/Real.sqrt (N:ℝ)+J*M*R^2/(N:ℝ)^2+
        J*(N:ℝ)^2*R^2/M := by
      clear * - hJp hMp hNp hRp
      positivity
    exact hlast.trans (le_add_of_nonneg_left hother)
  have hJpow : J^12≤C₀*T^ε*(Main+E^12) :=
    ((pow_le_pow_left₀ hJp.le hJE 12).trans (le_add_of_nonneg_left hMain0)).trans
      (le_mul_of_one_le_left hMass0 hQ)
  have hCorr :
      (∑ l∈Block,‖∑ j∈Finset.range (L+1-(pick l).1-(pick l).2),
        (𝐞 (X*(Fext (((a:ℝ)+j)/M)-Fext (((a:ℝ)+j+(pick l).1)/M)-
          Fext (((a:ℝ)+j+(pick l).2)/M)+
          Fext (((a:ℝ)+j+(pick l).1+(pick l).2)/M))):ℂ)‖)≤J+Z :=
    hcorr.trans (add_le_add hYJ le_rfl)
  calc
    _ ≤ (J+Z)^12 :=
      pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hCorr 12
    _ ≤ (2:ℝ)^11*(J^12+Z^12) := add_pow_le hJp.le hZ0 12
    _ ≤ (2:ℝ)^11*(C₀*T^ε*(Main+E^12)+C₀*T^ε*(Main+E^12)) :=
      mul_le_mul_of_nonneg_left (add_le_add hJpow hZ) (by norm_num)
    _ = _ := by
      rw [←two_mul]
      dsimp only [C]
      rw [show (2:ℝ)^12=2^11*2 from pow_succ 2 11]
      ac_rfl

private theorem double_difference_capped_integer_moments
    {X M N J R : ℝ} (hX : 0<X) (hM : 0<M) (hN : 0<N)
    (hJ : 0<J) (hR : 0<R) (hscale : (X*J/M^2)*N*R^2=M^3) :
    (J*M/Real.sqrt N)^72=J^72*M^72/N^36 ∧
    (J*M*R^2/N^2)^72=M^432/(X^72*N^216) ∧
    (J*N^2*R^2/M)^72=M^288*N^72/X^72 ∧
    (J*N*(N/R)^((2:ℝ)/3))^72=X^24*J^96*N^144/M^120 ∧
    (J^11*M^10*N^2/R^4)^6=X^12*J^78*N^24 ∧
    (J^11*M^11*N^2/R^7)^6=X^21*J^87*N^33/M^39 ∧
    (J^11*J*M^10/R^2)^6=X^6*J^78*M^30*N^6 ∧
    (J^11*J*M^11/R^5)^6=X^15*J^87*N^15/M^9 ∧
    (J^12*M^10*R^2/N^2*(R/N)^((2:ℝ)/3)*
      ((X*J/M^2)/M^2)^((4:ℝ)/3))^6=J^72*M^68/N^24 := by
  have hR2 : R^2=M^5/(X*J*N) := by
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero hX.ne' hJ.ne') hN.ne')).mpr
    have hs := hscale
    field_simp at hs
    nlinarith only [hs]
  have hSecond : J*M*R^2/N^2=M^6/(X*N^3) := by
    rw [hR2]
    field_simp
  have hThird : J*N^2*R^2/M=M^4*N/X := by
    rw [hR2]
    field_simp
  have hFrac : ((R/N)^((2:ℝ)/3))^6=(R/N)^4 := by
    rw [←Real.rpow_mul_natCast (div_nonneg hR.le hN.le)]
    norm_num
  have hTime : (((X*J/M^2)/M^2)^((4:ℝ)/3))^6=((X*J/M^2)/M^2)^8 := by
    rw [←Real.rpow_mul_natCast (by positivity : 0≤(X*J/M^2)/M^2)]
    norm_num
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hsqrt : (Real.sqrt N)^72=N^36 := by
      calc
        _ = ((Real.sqrt N)^2)^36 := by rw [←pow_mul]
        _ = N^36 := by rw [Real.sq_sqrt hN.le]
    rw [div_pow,mul_pow,hsqrt]
  · rw [hSecond]
    simp only [div_pow,mul_pow,←pow_mul]
  · rw [hThird]
    simp only [div_pow,mul_pow,←pow_mul]
  · rw [mul_pow,mul_pow,←Real.rpow_mul_natCast (div_nonneg hN.le hR.le),
      show ((2:ℝ)/3)*((72:ℕ):ℝ)=((48:ℕ):ℝ) by norm_num,
      Real.rpow_natCast,div_pow]
    rw [show R^48=(R^2)^24 by rw [←pow_mul],hR2]
    field_simp
  · simp only [mul_pow,div_pow,←pow_mul]
    rw [show R^24=(R^2)^12 by rw [←pow_mul],hR2]
    field_simp
    ac_rfl
  · simp only [mul_pow,div_pow,←pow_mul]
    rw [show R^42=(R^2)^21 by rw [←pow_mul],hR2]
    field_simp
    ac_rfl
  · simp only [mul_pow,div_pow,←pow_mul]
    rw [show R^12=(R^2)^6 by rw [←pow_mul],hR2]
    field_simp
  · simp only [mul_pow,div_pow,←pow_mul]
    rw [show R^30=(R^2)^15 by rw [←pow_mul],hR2]
    field_simp
  · rw [mul_pow,mul_pow,hFrac,hTime]
    simp only [mul_pow,div_pow,←pow_mul]
    rw [show R^12=(R^2)^6 by rw [←pow_mul],
      show R^4=(R^2)^2 by rw [←pow_mul],hR2]
    field_simp
    ring

private theorem source_product_twice_weyl_doubled_block
    {ε : ℝ} (hε : 0<ε) :
    ∃ D : ℝ, 0<D ∧
      ∀ (F : ℝ → ℝ) (σ X M : ℝ) (a L H K : ℕ),
        0<σ → 2≤H → 2≤K → H+K≤a →
        H≤L+1 → K≤L+1 → (H:ℝ)+K<M →
        let Pairs := (Finset.Icc 1 (H-1)) ×ˢ (Finset.Icc 1 (K-1))
        let Products := Pairs.image (fun p => p.1*p.2)
        let W := fun p : ℕ × ℕ => ∑ j∈Finset.range (L+1-p.1-p.2),
          (𝐞 (X*(F (((a:ℝ)+j)/M)-F (((a:ℝ)+j+p.1)/M)-
            F (((a:ℝ)+j+p.2)/M)+F (((a:ℝ)+j+p.1+p.2)/M))):ℂ)
        ∃ (pick : ℕ → ℕ × ℕ) (k : ℕ), 0<k ∧ 2*k≤H*K ∧
          (∀ l∈Products, pick l∈Pairs ∧ (pick l).1*(pick l).2=l ∧
            ∀ p∈Pairs, p.1*p.2=l → ‖W p‖≤‖W (pick l)‖) ∧
          (H:ℝ)^2*K*‖Expdb.exponentialSumAt F X M a (a+L)‖^4 ≤
            8*K*((L:ℝ)+1)^4+64*(H:ℝ)^2*((L:ℝ)+1)^4+
              128*H*((L:ℝ)+1)^3*
                (D*((H:ℝ)*K)^ε*((Nat.clog 2 (H*K):ℝ)*
                  ((L:ℝ)+1+∑ l∈(Finset.Ico k (2*k)).filter (fun l => l∈Products),
                    ‖W (pick l)‖))) := by
  classical
  obtain ⟨D,hD,hsource⟩ := source_product_twice_weyl hε
  refine ⟨D,hD,?_⟩
  intro F σ X M a L H K hσ hH hK hHa hHL hKL hM Pairs Products W
  obtain ⟨pick,hpick,hweyl⟩ := hsource F σ X M a L H K hσ
    (by omega) (by omega) hHa hHL hKL hM
  have hbounds (p : ℕ × ℕ) (hp : p∈Pairs) :
      0<p.1 ∧ p.1<H ∧ 0<p.2 ∧ p.2<K := by
    obtain ⟨hr,hs⟩ := Finset.mem_product.mp hp
    obtain ⟨hr1,hrH⟩ := Finset.mem_Icc.mp hr
    obtain ⟨hs1,hsK⟩ := Finset.mem_Icc.mp hs
    omega
  have hproduct (l : ℕ) (hl : l∈Products) : 0<l ∧ l<H*K := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨hr,hrH,hs,hsK⟩ := hbounds p hp
    refine ⟨Nat.mul_pos hr hs,?_⟩
    exact (Nat.mul_lt_mul_of_pos_right hrH hs).trans_le (Nat.mul_le_mul_left H hsK.le)
  have hWcap (p : ℕ × ℕ) : ‖W p‖≤(L:ℝ)+1 := by
    calc
      _ ≤ ∑ j∈Finset.range (L+1-p.1-p.2),
          ‖(𝐞 (X*(F (((a:ℝ)+j)/M)-F (((a:ℝ)+j+p.1)/M)-
            F (((a:ℝ)+j+p.2)/M)+F (((a:ℝ)+j+p.1+p.2)/M))):ℂ)‖ := norm_sum_le _ _
      _ = (L+1-p.1-p.2:ℕ) := by simp
      _ ≤ (L:ℝ)+1 := by exact_mod_cast (show L+1-p.1-p.2≤L+1 by omega)
  let f := fun l => if l∈Products then ‖W (pick l)‖ else 0
  have hf0 : f 0=0 := ite_eq_right (by
    intro hh
    exact (Nat.lt_irrefl 0) (hproduct 0 hh).1)
  have hf (l : ℕ) : 0≤f l := by
    dsimp only [f]
    split_ifs
    · exact norm_nonneg _
    · exact le_rfl
  have hfCap (l : ℕ) : f l≤(L:ℝ)+1 := by
    dsimp only [f]
    split_ifs
    · exact hWcap _
    · positivity
  have hHK : 2≤H*K := by nlinarith only [hH,hK]
  obtain ⟨k,hk,hkHK,hselected⟩ :=
    upperOriginal_nonnegative_doubled_block_selection f (H*K) hHK hf0 hf
      (by positivity : 0≤(L:ℝ)+1) (fun l _ => hfCap l)
  have hFilter : (Finset.range (H*K)).filter (fun l => l∈Products)=Products := by
    ext l
    simp only [Finset.mem_filter,Finset.mem_range]
    exact ⟨fun hh => hh.2,fun hl => ⟨(hproduct l hl).2,hl⟩⟩
  have hAll : (∑ l∈Products,‖W (pick l)‖)=∑ l∈Finset.range (H*K),f l := by
    calc
      _ = ∑ l∈(Finset.range (H*K)).filter (fun l => l∈Products),‖W (pick l)‖ :=
        congrArg (fun S : Finset ℕ => ∑ l∈S,‖W (pick l)‖) hFilter.symm
      _ = _ := by rw [Finset.sum_filter]
  have hRange :
      (∑ j∈Finset.range k,f (k+j))=∑ l∈Finset.Ico k (2*k),f l := by
    apply Finset.sum_bij (fun (j:ℕ) _ => k+j)
    case hi =>
      intro j hj
      have hj' := Finset.mem_range.mp hj
      exact Finset.mem_Ico.mpr ⟨by omega,by omega⟩
    case i_inj =>
      intro j _ l _ hjl
      omega
    case i_surj =>
      intro l hl
      have hl' := Finset.mem_Ico.mp hl
      exact ⟨l-k,Finset.mem_range.mpr (by omega),by omega⟩
    case h =>
      intro j _
      rfl
  have hBlock :
      (∑ j∈Finset.range k,f (k+j))=
        ∑ l∈(Finset.Ico k (2*k)).filter (fun l => l∈Products),‖W (pick l)‖ := by
    rw [hRange,Finset.sum_filter]
  rw [←hAll,hBlock] at hselected
  refine ⟨pick,k,hk,hkHK,hpick,?_⟩
  exact hweyl.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hselected
        (mul_nonneg hD.le (Real.rpow_nonneg (by positivity) ε)))
      (by positivity)))

public  theorem double_difference_weighted_capped_integer_moments
    {X M N J H R : ℝ} (hX : 0<X) (hM : 0<M) (hN : 0<N)
    (hJ : 0<J) (hH : 0<H) (hR : 0<R) (hscale : (X*J/M^2)*N*R^2=M^3) :
    let E := J*M/Real.sqrt N+J*M*R^2/N^2+J*N^2*R^2/M+
      J*N*(N/R)^((2:ℝ)/3)
    let Main := J^11*M^10*N^2/R^4+J^11*M^11*N^2/R^7+
      J^11*J*M^10/R^2+J^11*J*M^11/R^5+
      J^12*M^10*R^2/N^2*(R/N)^((2:ℝ)/3)*((X*J/M^2)/M^2)^((4:ℝ)/3)
    (M^3/H^3)^72*(E^72+Main^6) ≤ (2:ℝ)^288*
      ((J^72*M^288/(H^216*N^36)+M^648/(X^72*H^216*N^216)+
        M^504*N^72/(X^72*H^216)+X^24*J^96*M^96*N^144/H^216)+
        (X^12*J^78*M^216*N^24/H^216+X^21*J^87*M^177*N^33/H^216+
          X^6*J^78*M^246*N^6/H^216+X^15*J^87*M^207*N^15/H^216+
          J^72*M^284/(H^216*N^24))) := by
  intro E Main
  let e₁ := J*M/Real.sqrt N
  let e₂ := J*M*R^2/N^2
  let e₃ := J*N^2*R^2/M
  let e₄ := J*N*(N/R)^((2:ℝ)/3)
  let a₁ := J^11*M^10*N^2/R^4
  let a₂ := J^11*M^11*N^2/R^7
  let a₃ := J^11*J*M^10/R^2
  let a₄ := J^11*J*M^11/R^5
  let a₅ := J^12*M^10*R^2/N^2*(R/N)^((2:ℝ)/3)*((X*J/M^2)/M^2)^((4:ℝ)/3)
  have he₁ : 0≤e₁ := by dsimp only [e₁]; positivity
  have he₂ : 0≤e₂ := by dsimp only [e₂]; positivity
  have he₃ : 0≤e₃ := by dsimp only [e₃]; positivity
  have he₄ : 0≤e₄ := by dsimp only [e₄]; positivity
  have ha₁ : 0≤a₁ := by dsimp only [a₁]; positivity
  have ha₂ : 0≤a₂ := by dsimp only [a₂]; positivity
  have ha₃ : 0≤a₃ := by dsimp only [a₃]; positivity
  have ha₄ : 0≤a₄ := by dsimp only [a₄]; positivity
  have ha₅ : 0≤a₅ := by dsimp only [a₅]; positivity
  have hE : E^72≤(2:ℝ)^288*(e₁^72+e₂^72+e₃^72+e₄^72) := by
    have hh := middleOriginal_five_term_power_bound he₁ he₂ he₃ he₄ (le_refl (0:ℝ)) 72
    rw [add_zero,show (0:ℝ)^72=0 by norm_num,add_zero] at hh
    exact hh
  have hMain : Main^6≤(2:ℝ)^288*(a₁^6+a₂^6+a₃^6+a₄^6+a₅^6) := by
    exact (middleOriginal_five_term_power_bound ha₁ ha₂ ha₃ ha₄ ha₅ 6).trans
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by norm_num : 4*6≤288))
        (by positivity))
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉⟩ :=
    double_difference_capped_integer_moments hX hM hN hJ hR hscale
  have hW : 0≤(M^3/H^3)^72 := pow_nonneg (div_nonneg (pow_nonneg hM.le 3) (pow_nonneg hH.le 3)) 72
  calc
    _ ≤ (M^3/H^3)^72*((2:ℝ)^288*(e₁^72+e₂^72+e₃^72+e₄^72)+
        (2:ℝ)^288*(a₁^6+a₂^6+a₃^6+a₄^6+a₅^6)) :=
      mul_le_mul_of_nonneg_left (add_le_add hE hMain) hW
    _ = (2:ℝ)^288*((M^3/H^3)^72*
        ((e₁^72+e₂^72+e₃^72+e₄^72)+(a₁^6+a₂^6+a₃^6+a₄^6+a₅^6))) := by
      rw [←mul_add]
      ac_rfl
    _ = _ := by
      apply congrArg (fun q : ℝ => (2:ℝ)^288*q)
      dsimp only [e₁,e₂,e₃,e₄,a₁,a₂,a₃,a₄,a₅]
      rw [h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉]
      simp only [div_pow,←pow_mul,mul_add]
      field_simp
      ring

public  theorem double_difference_monomial_power_window
    {X M N H J ℓ u ν h g : ℝ} (hX : 1≤X)
    (hMl : X^ℓ≤M) (hMu : M≤X^u)
    (hNl : X^ν/2≤N) (hNu : N≤X^ν)
    (hHl : X^h/2≤H) (hJ : J=X^g)
    (p q r s x t v w z : ℕ) :
    X^p*J^q*M^r*N^s/(X^x*H^t*N^v*M^w*J^z) ≤
      (2:ℝ)^(t+v)*X^((p:ℝ)+q*g+r*u+s*ν-x-t*h-v*ν-w*ℓ-z*g) := by
  have hXp := zero_lt_one.trans_le hX
  have hMp : 0<M := (Real.rpow_pos_of_pos hXp ℓ).trans_le hMl
  have hNp : 0<N := (div_pos (Real.rpow_pos_of_pos hXp ν) (by norm_num)).trans_le hNl
  have hHp : 0<H := (div_pos (Real.rpow_pos_of_pos hXp h) (by norm_num)).trans_le hHl
  rw [hJ]
  calc
    _ ≤ X^p*(X^g)^q*(X^u)^r*(X^ν)^s/
        (X^x*(X^h/2)^t*(X^ν/2)^v*(X^ℓ)^w*(X^g)^z) := by
      gcongr
    _ = (2:ℝ)^(t+v)*(X^p*(X^g)^q*(X^u)^r*(X^ν)^s/
        (X^x*(X^h)^t*(X^ν)^v*(X^ℓ)^w*(X^g)^z)) := by
      rw [div_pow,div_pow,pow_add]
      field_simp
    _ = _ := by
      rw [←Real.rpow_natCast X p,←Real.rpow_natCast X x]
      simp only [←Real.rpow_mul_natCast hXp.le,←Real.rpow_add hXp,←Real.rpow_sub hXp]
      apply congrArg (fun a : ℝ => (2:ℝ)^(t+v)*X^a)
      ring

public  theorem fourth_pair_capped_full_window_margins
    {t u : ℝ} (ht : t∈Icc (0:ℝ) 1) (hu : u∈Icc (0:ℝ) 1) :
    let α := (1-t)*(890/3277)+t*(17604372/60424193)
    let h := ((1-t)*2749411+t*3296917)/100000000
    let g₀ := ((1-t)*16756+t*1976824)/100000000
    let ν₀ := ((1-t)*11931645+t*14567321)/100000000
    let ν₁ := ((1-t)*11969967+t*14925729)/100000000
    let g := (1-u)*g₀+u*(3*h)
    let ν := (1-u)*ν₀+u*ν₁
    let β := 89/3478+(7441/8695)*α
    let ℓ := α-1/10000000000
    let v := α+1/10000000000
    let μ := (1:ℝ)/1000000
    μ≤ℓ ∧
      v+μ≤1 ∧
      μ≤h ∧
      μ≤ν ∧
      μ≤g₀ ∧
      5*h+μ≤ℓ ∧
      g₀+μ≤3*h ∧
      ν+μ≤ℓ ∧
      5*v-1-g+μ≤3*ν ∧
      1+g+2*ν+μ≤5*ℓ ∧
      4*ν+1+g+μ≤6*ℓ ∧
      ν+3*v+μ≤1+g ∧
      1+g+μ≤4*ℓ ∧
      3*v+μ≤1+g ∧
      7*v+μ≤2+2*g+ν ∧
      7+7*g+27*ν+μ≤41*ℓ ∧
      2*h+μ≤β ∧
      4*v+g₀-3*h+μ≤4*β ∧
      288*v-144*h+μ≤288*β ∧
      288*v-36*ν+72*g-216*h+μ≤288*β ∧
      648*v-72-216*h-216*ν+μ≤288*β ∧
      24+96*g-216*h+96*v+144*ν+μ≤288*β ∧
      21+87*g-216*h+177*v+33*ν+μ≤288*β ∧
      15+87*g-216*h+207*v+15*ν+μ≤288*β ∧
      12+78*g-216*h+216*v+24*ν+μ≤288*β ∧
      6+78*g-216*h+246*v+6*ν+μ≤288*β ∧
      72*g-216*h+284*v-24*ν+μ≤288*β ∧
      504*v-72-216*h+72*ν+μ≤288*β := by
  intro α h g₀ ν₀ ν₁ g ν β ℓ v μ
  have ht0 := ht.1
  have ht1 := ht.2
  have hraw := fourth_pair_capped_terminal_source_window_scales ht hu
  dsimp only at hraw
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29⟩ := hraw
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [ht0,ht1]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [ht0,ht1]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h3]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h7]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h1]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h4,h3]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h2]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h8]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h13]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h16]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h14]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h10]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h15]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h11]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h12]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h18]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [ht0,ht1]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [ht0,ht1]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h19]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h20]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h21]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h22]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h23]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h24]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h25]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h26]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h28]
  · dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
    nlinarith only [h29]

private theorem double_difference_capped_polynomial_source_budgets
    {X M N J R B : ℝ} (hX : 0<X) (hM : 0<M) (hN : 0<N)
    (hJ : 0<J) (hR : 0<R) (hB : 1≤B) (hBN : B≤N)
    (hscale : (X*J/M^2)*N*R^2=M^3)
    (hRN : B^2*M^5≤X*J*N^3) (hNR : B*X*J*N^2≤M^5)
    (hNM : B*N≤M) (hCubic : B*X*J*N^4≤M^6)
    (hCap : B^2*N*M^3≤X*J) (hHeight : B*X*J≤M^4)
    (hMT : B*M^3≤X*J) (hRT : B*M^7≤X^2*J^2*N)
    (hTen : B^2*X^7*J^7*N^27≤M^41) :
    B≤R ∧ B*R≤N ∧ B*N≤R^2 ∧ B*N≤M ∧
      B*N^3≤M*R^2 ∧ B*N*R≤M ∧ B*M≤N*R^2 ∧
      B*M≤X*J/M^2 ∧ B*R^2≤X*J/M^2 ∧ B*N^10≤M^3*R^7 := by
  have hBp := zero_lt_one.trans_le hB
  have hDen : 0<X*J*N := mul_pos (mul_pos hX hJ) hN
  have hR2 : R^2=M^5/(X*J*N) := by
    apply (eq_div_iff hDen.ne').mpr
    have hs := hscale
    field_simp at hs
    nlinarith only [hs]
  have hNR' : B*N≤R^2 := by
    rw [hR2]
    apply (le_div_iff₀ hDen).mpr
    convert hNR using 1
    ring
  refine ⟨?_,?_,hNR',hNM,?_,?_,?_,?_,?_,?_⟩
  · apply (sq_le_sq₀ hBp.le hR.le).mp
    calc
      B^2 = B*B := pow_two B
      _ ≤ B*N := mul_le_mul_of_nonneg_left hBN hBp.le
      _ ≤ R^2 := hNR'
  · apply (sq_le_sq₀ (mul_nonneg hBp.le hR.le) hN.le).mp
    rw [mul_pow,hR2,←mul_div_assoc]
    apply (div_le_iff₀ hDen).mpr
    convert hRN using 1
    ring
  · rw [hR2,←mul_div_assoc]
    apply (le_div_iff₀ hDen).mpr
    convert hCubic using 1 <;> ring
  · apply (sq_le_sq₀ (mul_nonneg (mul_nonneg hBp.le hN.le) hR.le) hM.le).mp
    simp only [mul_pow]
    rw [hR2,←mul_div_assoc]
    apply (div_le_iff₀ hDen).mpr
    have hh := mul_le_mul_of_nonneg_right hCap (mul_nonneg hN.le (sq_nonneg M))
    convert hh using 1 <;> ring
  · rw [hR2,←mul_div_assoc]
    apply (le_div_iff₀ hDen).mpr
    have hh := mul_le_mul_of_nonneg_right hHeight (mul_nonneg hM.le hN.le)
    convert hh using 1 <;> ring
  · apply (le_div_iff₀ (sq_pos_of_pos hM)).mpr
    convert hMT using 1
    ring
  · rw [hR2,←mul_div_assoc]
    apply (div_le_div_iff₀ hDen (sq_pos_of_pos hM)).mpr
    convert hRT using 1 <;> ring
  · apply (sq_le_sq₀ (mul_nonneg hBp.le (pow_nonneg hN.le 10))
      (mul_nonneg (pow_nonneg hM.le 3) (pow_nonneg hR.le 7))).mp
    simp only [mul_pow,←pow_mul]
    rw [show R^14=(R^2)^7 by rw [←pow_mul],hR2,div_pow,←mul_div_assoc]
    apply (le_div_iff₀ (pow_pos hDen 7)).mpr
    convert hTen using 1 <;> ring

public  theorem double_difference_ten_monomials_power_window
    {X M N H J ℓ u ν h g ξ : ℝ} (hX : 1≤X) (hξ : 0≤ξ)
    (hMl : X^ℓ≤M) (hMu : M≤X^u)
    (hNl : X^ν/2≤N) (hNu : N≤X^ν) (hHl : X^h/2≤H) (hJ : J=X^g)
    (hDiag : 288*u-144*h≤ξ)
    (hSqrt : 288*u-36*ν+72*g-216*h≤ξ)
    (hSecond : 648*u-72-216*h-216*ν≤ξ)
    (hThird : 504*u-72-216*h+72*ν≤ξ)
    (hFourth : 24+96*g-216*h+96*u+144*ν≤ξ)
    (hFirstMain : 12+78*g-216*h+216*u+24*ν≤ξ)
    (hSecondMain : 21+87*g-216*h+177*u+33*ν≤ξ)
    (hThirdMain : 6+78*g-216*h+246*u+6*ν≤ξ)
    (hFourthMain : 15+87*g-216*h+207*u+15*ν≤ξ)
    (hFifthMain : 72*g-216*h+284*u-24*ν≤ξ) :
    1+(M^288/H^144+
        ((J^72*M^288/(H^216*N^36)+M^648/(X^72*H^216*N^216)+
          M^504*N^72/(X^72*H^216)+X^24*J^96*M^96*N^144/H^216)+
          (X^12*J^78*M^216*N^24/H^216+X^21*J^87*M^177*N^33/H^216+
            X^6*J^78*M^246*N^6/H^216+X^15*J^87*M^207*N^15/H^216+
            J^72*M^284/(H^216*N^24)))) ≤ (11*(2:ℝ)^432)*X^ξ := by
  have hXp := zero_lt_one.trans_le hX
  have hbound (k : ℕ) (e : ℝ) (hk : k≤432) (he : e≤ξ) :
      (2:ℝ)^k*X^e≤(2:ℝ)^432*X^ξ :=
    mul_le_mul (pow_le_pow_right₀ (by norm_num) hk)
      (Real.rpow_le_rpow_of_exponent_le hX he)
      (Real.rpow_nonneg hXp.le _) (by norm_num)
  have h₀ : 1≤(2:ℝ)^432*X^ξ :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (Real.one_le_rpow hX hξ)
  have hb1 : M^288/H^144≤(2:ℝ)^432*X^ξ := by
    have hh := double_difference_monomial_power_window hX hMl hMu hNl hNu hHl hJ
      0 0 288 0 0 144 0 0 0
    have heq : (0:ℝ)+0*g+288*u+0*ν-0-144*h-0*ν-0*ℓ-0*g =
        288*u-144*h := by ring
    simp only [Nat.cast_zero,Nat.cast_ofNat,pow_zero,one_mul,mul_one,
      heq] at hh
    exact hh.trans (hbound 144 _ (by norm_num) hDiag)
  have hb2 : J^72*M^288/(H^216*N^36)≤(2:ℝ)^432*X^ξ := by
    have hh := double_difference_monomial_power_window hX hMl hMu hNl hNu hHl hJ
      0 72 288 0 0 216 36 0 0
    have heq : (0:ℝ)+72*g+288*u+0*ν-0-216*h-36*ν-0*ℓ-0*g =
        288*u-36*ν+72*g-216*h := by ring
    simp only [Nat.cast_zero,Nat.cast_ofNat,pow_zero,one_mul,mul_one,
      heq] at hh
    exact hh.trans (hbound 252 _ (by norm_num) hSqrt)
  have hb3 : M^648/(X^72*H^216*N^216)≤(2:ℝ)^432*X^ξ := by
    have hh := double_difference_monomial_power_window hX hMl hMu hNl hNu hHl hJ
      0 0 648 0 72 216 216 0 0
    have heq : (0:ℝ)+0*g+648*u+0*ν-72-216*h-216*ν-0*ℓ-0*g =
        648*u-72-216*h-216*ν := by ring
    simp only [Nat.cast_zero,Nat.cast_ofNat,pow_zero,one_mul,mul_one,
      heq] at hh
    exact hh.trans (hbound 432 _ (by norm_num) hSecond)
  have hb4 : M^504*N^72/(X^72*H^216)≤(2:ℝ)^432*X^ξ := by
    have hh := double_difference_monomial_power_window hX hMl hMu hNl hNu hHl hJ
      0 0 504 72 72 216 0 0 0
    have heq : (0:ℝ)+0*g+504*u+72*ν-72-216*h-0*ν-0*ℓ-0*g =
        504*u-72-216*h+72*ν := by ring
    simp only [Nat.cast_zero,Nat.cast_ofNat,pow_zero,one_mul,mul_one,
      heq] at hh
    exact hh.trans (hbound 216 _ (by norm_num) hThird)
  have hb5 : X^24*J^96*M^96*N^144/H^216≤(2:ℝ)^432*X^ξ := by
    have hh := double_difference_monomial_power_window hX hMl hMu hNl hNu hHl hJ
      24 96 96 144 0 216 0 0 0
    have heq : (24:ℝ)+96*g+96*u+144*ν-0-216*h-0*ν-0*ℓ-0*g =
        24+96*g-216*h+96*u+144*ν := by ring
    simp only [Nat.cast_zero,Nat.cast_ofNat,pow_zero,one_mul,mul_one,
      heq] at hh
    exact hh.trans (hbound 216 _ (by norm_num) hFourth)
  have hb6 : X^12*J^78*M^216*N^24/H^216≤(2:ℝ)^432*X^ξ := by
    have hh := double_difference_monomial_power_window hX hMl hMu hNl hNu hHl hJ
      12 78 216 24 0 216 0 0 0
    have heq : (12:ℝ)+78*g+216*u+24*ν-0-216*h-0*ν-0*ℓ-0*g =
        12+78*g-216*h+216*u+24*ν := by ring
    simp only [Nat.cast_zero,Nat.cast_ofNat,pow_zero,one_mul,mul_one,
      heq] at hh
    exact hh.trans (hbound 216 _ (by norm_num) hFirstMain)
  have hb7 : X^21*J^87*M^177*N^33/H^216≤(2:ℝ)^432*X^ξ := by
    have hh := double_difference_monomial_power_window hX hMl hMu hNl hNu hHl hJ
      21 87 177 33 0 216 0 0 0
    have heq : (21:ℝ)+87*g+177*u+33*ν-0-216*h-0*ν-0*ℓ-0*g =
        21+87*g-216*h+177*u+33*ν := by ring
    simp only [Nat.cast_zero,Nat.cast_ofNat,pow_zero,one_mul,mul_one,
      heq] at hh
    exact hh.trans (hbound 216 _ (by norm_num) hSecondMain)
  have hb8 : X^6*J^78*M^246*N^6/H^216≤(2:ℝ)^432*X^ξ := by
    have hh := double_difference_monomial_power_window hX hMl hMu hNl hNu hHl hJ
      6 78 246 6 0 216 0 0 0
    have heq : (6:ℝ)+78*g+246*u+6*ν-0-216*h-0*ν-0*ℓ-0*g =
        6+78*g-216*h+246*u+6*ν := by ring
    simp only [Nat.cast_zero,Nat.cast_ofNat,pow_zero,one_mul,mul_one,
      heq] at hh
    exact hh.trans (hbound 216 _ (by norm_num) hThirdMain)
  have hb9 : X^15*J^87*M^207*N^15/H^216≤(2:ℝ)^432*X^ξ := by
    have hh := double_difference_monomial_power_window hX hMl hMu hNl hNu hHl hJ
      15 87 207 15 0 216 0 0 0
    have heq : (15:ℝ)+87*g+207*u+15*ν-0-216*h-0*ν-0*ℓ-0*g =
        15+87*g-216*h+207*u+15*ν := by ring
    simp only [Nat.cast_zero,Nat.cast_ofNat,pow_zero,one_mul,mul_one,
      heq] at hh
    exact hh.trans (hbound 216 _ (by norm_num) hFourthMain)
  have hb10 : J^72*M^284/(H^216*N^24)≤(2:ℝ)^432*X^ξ := by
    have hh := double_difference_monomial_power_window hX hMl hMu hNl hNu hHl hJ
      0 72 284 0 0 216 24 0 0
    have heq : (0:ℝ)+72*g+284*u+0*ν-0-216*h-24*ν-0*ℓ-0*g =
        72*g-216*h+284*u-24*ν := by ring
    simp only [Nat.cast_zero,Nat.cast_ofNat,pow_zero,one_mul,mul_one,
      heq] at hh
    exact hh.trans (hbound 240 _ (by norm_num) hFifthMain)
  have hSum (d : ℝ) : d+(d+((d+d+d+d)+(d+d+d+d+d)))=11*d := by ring
  calc
    _ ≤ (2:ℝ)^432*X^ξ+((2:ℝ)^432*X^ξ+
        (((2:ℝ)^432*X^ξ+(2:ℝ)^432*X^ξ+(2:ℝ)^432*X^ξ+(2:ℝ)^432*X^ξ)+
          ((2:ℝ)^432*X^ξ+(2:ℝ)^432*X^ξ+(2:ℝ)^432*X^ξ+
            (2:ℝ)^432*X^ξ+(2:ℝ)^432*X^ξ))) :=
      add_le_add h₀ (add_le_add hb1
        (add_le_add (add_le_add (add_le_add (add_le_add hb2 hb3) hb4) hb5)
          (add_le_add (add_le_add (add_le_add (add_le_add hb6 hb7) hb8) hb9) hb10)))
    _ = 11*((2:ℝ)^432*X^ξ) := hSum _
    _ = _ := (mul_assoc _ _ _).symm

public  theorem eventually_double_difference_capped_physical_window
    {B C w₀ μ ℓ v h : ℝ} (hB : 1≤B) (hC : 1≤C) (hw₀ : 0<w₀)
    (hμ : 0<μ) (hμℓ : μ≤ℓ) (hℓv : ℓ≤v) (hμh : μ≤h)
    (hWidth : 5*h+μ≤ℓ) :
    ∀ᶠ X : ℝ in Filter.atTop, 2≤X ∧
      ∀ M J g ν : ℝ, X^ℓ≤M → M≤X^v → J=X^g →
        0≤g → g≤3*h → μ≤ν → ν+μ≤ℓ →
        5*v-1-g+μ≤3*ν → 1+g+2*ν+μ≤5*ℓ →
        4*ν+1+g+μ≤6*ℓ → ν+3*v+μ≤1+g →
        1+g+μ≤4*ℓ → 3*v+μ≤1+g →
        7*v+μ≤2+2*g+ν → 7+7*g+27*ν+μ≤41*ℓ →
        let n := ⌊X^ν/8⌋₊
        let N := 8*n
        let H := ⌊X^h⌋₊
        let R := Real.sqrt (M^5/(X*J*(N:ℝ)))
        let T := X*J/M^2
        let W := ((H:ℝ)+(H:ℝ)^2)/M
        1≤M ∧ 2≤N ∧ 2≤H ∧
          X^ν/2≤(N:ℝ) ∧ (N:ℝ)≤X^ν ∧ X^h/2≤(H:ℝ) ∧ (H:ℝ)≤X^h ∧
          1≤J ∧ 0<R ∧ T*(N:ℝ)*R^2=M^3 ∧ C≤T ∧
          W≤w₀ ∧ J≤M ∧ W*J≤1 ∧
          B≤R ∧ B*R≤N ∧ B*(N:ℝ)≤R^2 ∧ B*(N:ℝ)≤M ∧
          B*(N:ℝ)^3≤M*R^2 ∧ B*(N:ℝ)*R≤M ∧ B*M≤(N:ℝ)*R^2 ∧
          B*M≤T ∧ B*R^2≤T ∧ B*(N:ℝ)^10≤M^3*R^7 := by
  have hB0 := zero_le_one.trans hB
  have hC0 := zero_le_one.trans hC
  have hℓp := hμ.trans_le hμℓ
  have hv0 := (hℓp.trans_le hℓv).le
  have hhp := hμ.trans_le hμh
  let D := 32+8*B^2+2*B+C+2/w₀
  have hInv : 0<2/w₀ := div_pos (by norm_num) hw₀
  have hD32 : 32≤D := by dsimp only [D]; nlinarith only [sq_nonneg B,hB0,hC0,hInv]
  have hDB : 2*B≤D := by dsimp only [D]; nlinarith only [sq_nonneg B,hC0,hInv]
  have hDBsq : 8*B^2≤D := by dsimp only [D]; linarith only [hB0,hC0,hInv]
  have hDC : C≤D := by dsimp only [D]; nlinarith only [sq_nonneg B,hB0,hInv]
  have hDW : 2/w₀≤D := by dsimp only [D]; nlinarith only [sq_nonneg B,hB0,hC0]
  have hD1 : 1≤D := (by norm_num : (1:ℝ)≤32).trans hD32
  have hDB1 : B≤D := (by linarith only [hB0] : B≤2*B).trans hDB
  have hDBsq1 : B^2≤D := (by nlinarith only [sq_nonneg B] : B^2≤8*B^2).trans hDBsq
  have hD2 : 2≤D := (by norm_num : (2:ℝ)≤32).trans hD32
  filter_upwards [(tendsto_rpow_atTop hμ).eventually_ge_atTop D,
    Filter.eventually_ge_atTop (2:ℝ)] with X hXD hX2
  have hX : 1≤X := (by norm_num : (1:ℝ)≤2).trans hX2
  have hXp := zero_lt_one.trans_le hX
  have hdom (A e : ℝ) (hAD : A≤D) (he : e+μ≤0) : A*X^e≤1 := by
    calc
      _ ≤ X^μ*X^e := mul_le_mul_of_nonneg_right (hAD.trans hXD) (Real.rpow_nonneg hXp.le _)
      _ = X^(μ+e) := (Real.rpow_add hXp _ _).symm
      _ ≤ X^(0:ℝ) := Real.rpow_le_rpow_of_exponent_le hX (by linarith only [he])
      _ = 1 := Real.rpow_zero X
  refine ⟨hX2,?_⟩
  intro M J g ν hMl hMu hJ hg0 hgh hμν hνM hRN hNR hCubic hCap hHeight hMT hRT hTen
    n N H R T W
  have hM1 : 1≤M := (Real.one_le_rpow hX hℓp.le).trans hMl
  have hMp := zero_lt_one.trans_le hM1
  have hJ1 : 1≤J := by rw [hJ]; exact Real.one_le_rpow hX hg0
  have hJp := zero_lt_one.trans_le hJ1
  have hNU : 32≤X^ν := hD32.trans (hXD.trans (Real.rpow_le_rpow_of_exponent_le hX hμν))
  have hHU : 4≤X^h :=
    (by norm_num : (4:ℝ)≤32).trans (hD32.trans (hXD.trans (Real.rpow_le_rpow_of_exponent_le hX hμh)))
  obtain ⟨hN2,hH2,hNl,hNu,hHl,hHu⟩ := upperOriginal_floor_power_scales hNU hHU
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hH1 : (1:ℝ)≤H := by exact_mod_cast (show 1≤H by omega)
  have hBN : B≤(N:ℝ) := by
    have hh := hDB.trans (hXD.trans (Real.rpow_le_rpow_of_exponent_le hX hμν))
    linarith only [hh,hNl]
  have hratio (A : ℝ) (p q r s x t vN w z : ℕ)
      (hA : 0≤A) (hAD : A*(2:ℝ)^(t+vN)≤D)
      (he : (p:ℝ)+q*g+r*v+s*ν-x-t*h-vN*ν-w*ℓ-z*g+μ≤0) :
      A*(X^p*J^q*M^r*(N:ℝ)^s/(X^x*(H:ℝ)^t*(N:ℝ)^vN*M^w*J^z))≤1 := by
    calc
      _ ≤ A*((2:ℝ)^(t+vN)*X^((p:ℝ)+q*g+r*v+s*ν-x-t*h-vN*ν-w*ℓ-z*g)) :=
        mul_le_mul_of_nonneg_left
          (double_difference_monomial_power_window hX hMl hMu hNl hNu hHl hJ p q r s x t vN w z) hA
      _ = (A*(2:ℝ)^(t+vN))*X^((p:ℝ)+q*g+r*v+s*ν-x-t*h-vN*ν-w*ℓ-z*g) :=
        (mul_assoc _ _ _).symm
      _ ≤ 1 := hdom _ _ hAD he

  have hpoly {a b c : ℝ} (hb : 0<b) (hh : c*(a/b)≤1) : c*a≤b := by
    rw [←mul_div_assoc] at hh
    simpa only [one_mul] using (div_le_iff₀ hb).mp hh
  have pRN : B^2*M^5≤X*J*(N:ℝ)^3 := by
    have hh := hratio (B^2) 0 0 5 0 1 0 3 0 1 (sq_nonneg B)
      (by norm_num; nlinarith only [hDBsq])
      (by norm_num; linarith only [hRN])
    simp only [pow_zero,pow_one,one_mul,mul_one] at hh
    have hh' := hpoly (by positivity) hh
    convert hh' using 1
    ring
  have pNR : B*X*J*(N:ℝ)^2≤M^5 := by
    have hh := hratio (B) 1 1 0 2 0 0 0 5 0 (hB0)
      (by norm_num; nlinarith only [hDB1])
      (by norm_num; linarith only [hNR])
    simp only [pow_zero,pow_one,one_mul,mul_one] at hh
    have hh' := hpoly (by positivity) hh
    convert hh' using 1
    ring
  have pNM : B*(N:ℝ)≤M := by
    have hh := hratio (B) 0 0 0 1 0 0 0 1 0 (hB0)
      (by norm_num; nlinarith only [hDB1])
      (by norm_num; linarith only [hνM])
    simp only [pow_zero,pow_one,one_mul,mul_one] at hh
    have hh' := hpoly (by positivity) hh
    exact hh'
  have pCubic : B*X*J*(N:ℝ)^4≤M^6 := by
    have hh := hratio (B) 1 1 0 4 0 0 0 6 0 (hB0)
      (by norm_num; nlinarith only [hDB1])
      (by norm_num; linarith only [hCubic])
    simp only [pow_zero,pow_one,one_mul,mul_one] at hh
    have hh' := hpoly (by positivity) hh
    convert hh' using 1
    ring
  have pCap : B^2*(N:ℝ)*M^3≤X*J := by
    have hh := hratio (B^2) 0 0 3 1 1 0 0 0 1 (sq_nonneg B)
      (by norm_num; nlinarith only [hDBsq1])
      (by norm_num; linarith only [hCap])
    simp only [pow_zero,pow_one,one_mul,mul_one] at hh
    have hh' := hpoly (by positivity) hh
    convert hh' using 1
    ring
  have pHeight : B*X*J≤M^4 := by
    have hh := hratio (B) 1 1 0 0 0 0 0 4 0 (hB0)
      (by norm_num; nlinarith only [hDB1])
      (by norm_num; linarith only [hHeight])
    simp only [pow_zero,pow_one,one_mul,mul_one] at hh
    have hh' := hpoly (by positivity) hh
    convert hh' using 1
    ring
  have pMT : B*M^3≤X*J := by
    have hh := hratio (B) 0 0 3 0 1 0 0 0 1 (hB0)
      (by norm_num; nlinarith only [hDB1])
      (by norm_num; linarith only [hMT])
    simp only [pow_zero,pow_one,one_mul,mul_one] at hh
    have hh' := hpoly (by positivity) hh
    exact hh'
  have pRT : B*M^7≤X^2*J^2*(N:ℝ) := by
    have hh := hratio (B) 0 0 7 0 2 0 1 0 2 (hB0)
      (by norm_num; nlinarith only [hDB])
      (by norm_num; linarith only [hRT])
    simp only [pow_zero,pow_one,one_mul,mul_one] at hh
    have hh' := hpoly (by positivity) hh
    convert hh' using 1
    ring
  have pTen : B^2*X^7*J^7*(N:ℝ)^27≤M^41 := by
    have hh := hratio (B^2) 7 7 0 27 0 0 0 41 0 (sq_nonneg B)
      (by norm_num; nlinarith only [hDBsq1])
      (by norm_num; linarith only [hTen])
    simp only [pow_zero,one_mul,mul_one] at hh
    have hh' := hpoly (by positivity) hh
    convert hh' using 1
    ring
  have pThreshold : C*M^2≤X*J := by
    have hh := hratio (C) 0 0 2 0 1 0 0 0 1 (hC0)
      (by norm_num; nlinarith only [hDC])
      (by norm_num; linarith only [hMT,hv0])
    simp only [pow_zero,pow_one,one_mul,mul_one] at hh
    have hh' := hpoly (by positivity) hh
    exact hh'
  have pJ : J≤M := by
    have hh := hratio (1) 0 1 0 0 0 0 0 1 0 (zero_le_one)
      (by norm_num; nlinarith only [hD1])
      (by norm_num; linarith only [hgh,hWidth,hhp])
    simp only [pow_zero,pow_one,one_mul,mul_one] at hh
    exact (div_le_one hMp).mp hh

  have hThreshold : C≤T := (le_div_iff₀ (sq_pos_of_pos hMp)).mpr pThreshold
  have hWbound : W≤2*X^(2*h-ℓ) := by
    have hHsq : (H:ℝ)^2≤(X^h)^2 := by gcongr
    have hnumer : (H:ℝ)+(H:ℝ)^2≤2*(X^h)^2 := by
      nlinarith only [hH1,hHsq]
    calc
      W ≤ 2*(X^h)^2/X^ℓ :=
        div_le_div₀ (by positivity) hnumer (Real.rpow_pos_of_pos hXp _) hMl
      _ = 2*X^(2*h-ℓ) := by
        have hp : X^(h*2)=(X^h)^2 := by
          simpa only [Nat.cast_ofNat] using Real.rpow_mul_natCast hXp.le h 2
        rw [Real.rpow_sub hXp,show 2*h=h*2 by ring,hp]
        ring
  have hW : W≤w₀ := by
    have hh := hdom (2/w₀) (2*h-ℓ) hDW (by linarith only [hWidth,hhp])
    have hh' := mul_le_mul_of_nonneg_right hh hw₀.le
    have heq : (2/w₀*X^(2*h-ℓ))*w₀=2*X^(2*h-ℓ) := by
      field_simp
    rw [heq,one_mul] at hh'
    exact hWbound.trans hh'
  have hWJ : W*J≤1 := by
    calc
      W*J ≤ (2*X^(2*h-ℓ))*J := mul_le_mul_of_nonneg_right hWbound hJp.le
      _ = 2*X^(2*h-ℓ+g) := by rw [hJ,mul_assoc,←Real.rpow_add hXp]
      _ ≤ 1 := hdom 2 _ hD2 (by linarith only [hgh,hWidth])
  have hRad : 0<M^5/(X*J*(N:ℝ)) := by positivity
  have hRp : 0<R := Real.sqrt_pos.2 hRad
  have hR2 : R^2=M^5/(X*J*(N:ℝ)) := Real.sq_sqrt hRad.le
  have hscale : T*(N:ℝ)*R^2=M^3 := by
    rw [hR2]
    dsimp only [T]
    field_simp
  have hbudgets := double_difference_capped_polynomial_source_budgets hXp hMp hNp hJp hRp
    hB hBN hscale pRN pNR pNM pCubic pCap pHeight pMT pRT pTen
  exact ⟨hM1,hN2,hH2,hNl,hNu,hHl,hHu,hJ1,hRp,hscale,hThreshold,hW,pJ,hWJ,hbudgets⟩

public  theorem source_product_twice_weyl_normalized_block
    {ε : ℝ} (hε : 0<ε) :
    ∃ A : ℝ, 1≤A ∧
      ∀ (F : ℝ → ℝ) (σ X M : ℝ) (a L H : ℕ),
        0<σ → 1≤X → 1≤M → 2≤H → H^2≤L+1 →
        (H:ℝ)^3≤X → ((H:ℝ)+(H:ℝ)^2)/M≤1/4 →
        M≤(a:ℝ) → ((a+L:ℕ):ℝ)≤2*M →
        let Pairs := (Finset.Icc 1 (H-1)) ×ˢ (Finset.Icc 1 (H^2-1))
        let Products := Pairs.image (fun p => p.1*p.2)
        let W := fun p : ℕ × ℕ => ∑ j∈Finset.range (L+1-p.1-p.2),
          (𝐞 (X*(F (((a:ℝ)+j)/M)-F (((a:ℝ)+j+p.1)/M)-
            F (((a:ℝ)+j+p.2)/M)+F (((a:ℝ)+j+p.1+p.2)/M))):ℂ)
        ∃ (pick : ℕ → ℕ × ℕ) (k : ℕ), 0<k ∧ 2*k≤H^3 ∧
          (∀ l∈Products, pick l∈Pairs ∧ (pick l).1*(pick l).2=l ∧
            ∀ p∈Pairs, p.1*p.2=l → ‖W p‖≤‖W (pick l)‖) ∧
          (∑ l∈(Finset.Ico k (2*k)).filter (fun l => l∈Products),‖W (pick l)‖)≤2*M*k ∧
          ‖Expdb.exponentialSumAt F X M a (a+L)‖^4 ≤
            A*X^ε*(1+(Nat.clog 2 (H^3):ℝ))*
              (M^4/(H:ℝ)^2+(M^3/(H:ℝ)^3)*
                (∑ l∈(Finset.Ico k (2*k)).filter (fun l => l∈Products),‖W (pick l)‖)) := by
  classical
  obtain ⟨D,hD,hsource⟩ := source_product_twice_weyl_doubled_block hε
  let A := 4096*max 1 D
  have hA : 1≤A := by
    dsimp only [A]
    linarith only [le_max_left (1:ℝ) D]
  refine ⟨A,hA,?_⟩
  intro F σ X M a L H hσ hX hM hH hHL hHX hWidth ha hb Pairs Products W
  have hMp := zero_lt_one.trans_le hM
  have hH1 : (1:ℝ)≤H := by exact_mod_cast (show 1≤H by omega)
  have hHp := zero_lt_one.trans_le hH1
  have hK2 : 2≤H^2 := by nlinarith only [hH]
  have hHK : (H:ℝ)+(H:ℝ)^2<M := by
    have hh := (div_le_iff₀ hMp).mp hWidth
    linarith only [hh,hMp]
  have hHKnat : H+H^2≤a := by
    exact_mod_cast (show (H:ℝ)+(H:ℝ)^2≤(a:ℝ) from hHK.le.trans ha)
  have hHshort : H≤L+1 := (by nlinarith only [hH] : H≤H^2).trans hHL
  have hCube : H*H^2=H^3 := by ring
  obtain ⟨pick,k,hk,hkH,hpick,hweyl⟩ :=
    hsource F σ X M a L H (H^2) hσ hH hK2 hHKnat hHshort hHL
      (by exact_mod_cast hHK)
  rw [hCube] at hkH hweyl
  simp only [Nat.cast_pow] at hweyl
  rw [show (H:ℝ)^2*(H:ℝ)^2=(H:ℝ)^4 by ring,
    show (H:ℝ)*(H:ℝ)^2=(H:ℝ)^3 by ring] at hweyl
  let Z := ∑ l∈(Finset.Ico k (2*k)).filter (fun l => l∈Products),‖W (pick l)‖
  have hZ : 0≤Z := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  let Log := 1+(Nat.clog 2 (H^3):ℝ)
  let U := max 1 D*X^ε*Log
  have hLog : 1≤Log := by dsimp only [Log]; exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hXpow : 1≤X^ε := Real.one_le_rpow hX hε.le
  have hU : 1≤U := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (le_max_left _ _) hXpow) hLog
  have hLcap : (L:ℝ)+1≤2*M := by
    have hb' : (a:ℝ)+(L:ℝ)≤2*M := by simpa only [Nat.cast_add] using hb
    linarith only [ha,hb',hM]
  have hZcap : Z≤2*M*k := by
    have hWcap (p : ℕ × ℕ) : ‖W p‖≤2*M := by
      calc
        _ ≤ ∑ j∈Finset.range (L+1-p.1-p.2),
            ‖(𝐞 (X*(F (((a:ℝ)+j)/M)-F (((a:ℝ)+j+p.1)/M)-
              F (((a:ℝ)+j+p.2)/M)+F (((a:ℝ)+j+p.1+p.2)/M))):ℂ)‖ := norm_sum_le _ _
        _ = (L+1-p.1-p.2:ℕ) := by simp
        _ ≤ (L:ℝ)+1 := by exact_mod_cast (show L+1-p.1-p.2≤L+1 by omega)
        _ ≤ 2*M := hLcap
    have hCard : ((Finset.Ico k (2*k)).filter (fun l => l∈Products)).card≤k := by
      calc
        _ ≤ (Finset.Ico k (2*k)).card := Finset.card_filter_le _ _
        _ = k := by rw [Nat.card_Ico]; omega
    calc
      _ ≤ ∑ l∈(Finset.Ico k (2*k)).filter (fun l => l∈Products), (2*M) :=
        Finset.sum_le_sum (fun l _ => hWcap (pick l))
      _ = (((Finset.Ico k (2*k)).filter (fun l => l∈Products)).card:ℝ)*(2*M) := by simp
      _ ≤ (k:ℝ)*(2*M) := mul_le_mul_of_nonneg_right (by exact_mod_cast hCard) (by positivity)
      _ = _ := by ring
  have hweight : D*((H:ℝ)^3)^ε*(Nat.clog 2 (H^3):ℝ)≤U := by
    dsimp only [U,Log]
    gcongr
    · exact le_max_right _ _
    · linarith
  have hraw :
      (H:ℝ)^4*‖Expdb.exponentialSumAt F X M a (a+L)‖^4 ≤
        1152*(H:ℝ)^2*M^4+1024*H*M^3*U*(2*M+Z) := by
    calc
      _ ≤ 8*(H:ℝ)^2*((L:ℝ)+1)^4+64*(H:ℝ)^2*((L:ℝ)+1)^4+
          128*H*((L:ℝ)+1)^3*(D*((H:ℝ)^3)^ε*((Nat.clog 2 (H^3):ℝ)*((L:ℝ)+1+Z))) :=
        hweyl
      _ = 72*(H:ℝ)^2*((L:ℝ)+1)^4+
          128*H*((L:ℝ)+1)^3*(D*((H:ℝ)^3)^ε*(Nat.clog 2 (H^3):ℝ))*((L:ℝ)+1+Z) := by ring
      _ ≤ 72*(H:ℝ)^2*(2*M)^4+128*H*(2*M)^3*U*(2*M+Z) := by gcongr
      _ = _ := by ring
  have hDen : (H:ℝ)^2≤(H:ℝ)^3 := by
    calc
      _ = 1*(H:ℝ)^2 := (one_mul _).symm
      _ ≤ (H:ℝ)*(H:ℝ)^2 := mul_le_mul_of_nonneg_right hH1 (sq_nonneg _)
      _ = _ := by ring
  have hRatio : M^4/(H:ℝ)^3≤M^4/(H:ℝ)^2 :=
    div_le_div_of_nonneg_left (pow_nonneg hMp.le 4) (sq_pos_of_pos hHp) hDen
  have hDiag0 : 0≤M^4/(H:ℝ)^2 := by positivity
  have hCorr0 : 0≤(M^3/(H:ℝ)^3)*Z := mul_nonneg (by positivity) hZ
  refine ⟨pick,k,hk,hkH,hpick,hZcap,?_⟩
  calc
    _ ≤ (1152*(H:ℝ)^2*M^4+1024*H*M^3*U*(2*M+Z))/(H:ℝ)^4 :=
      (le_div_iff₀ (pow_pos hHp 4)).mpr ((mul_comm _ _).trans_le hraw)
    _ = 1152*(M^4/(H:ℝ)^2)+2048*U*(M^4/(H:ℝ)^3)+
        1024*U*((M^3/(H:ℝ)^3)*Z) := by field_simp; ring
    _ ≤ 1152*(M^4/(H:ℝ)^2)+2048*U*(M^4/(H:ℝ)^2)+
        1024*U*((M^3/(H:ℝ)^3)*Z) := by gcongr
    _ ≤ 4096*U*(M^4/(H:ℝ)^2+(M^3/(H:ℝ)^3)*Z) := by
      nlinarith only [hDiag0,hCorr0,
        mul_le_mul_of_nonneg_right hU hDiag0,mul_nonneg (zero_le_one.trans hU) hCorr0]
    _ = _ := by
      dsimp only [A,U]
      ring

public  theorem double_difference_fourth_twelfth_moment_assembly
    {S Z d w Main E V C X ε Q : ℝ}
    (hS : 0≤S) (hZ : 0≤Z) (hd : 0≤d) (hw : 0≤w)
    (hMain : 0≤Main) (hE : 0≤E) (hC : 1≤C) (hX : 1≤X)
    (hε : 0≤ε) (hQ : 0≤Q)
    (hWeyl : S^4≤Q*(d+w*Z))
    (hMoment : Z^12≤C*X^ε*(Main+E^12))
    (hWeighted : w^72*(E^72+Main^6)≤(2:ℝ)^288*V) :
    S^288≤(2:ℝ)^364*Q^72*C^6*X^(6*ε)*(d^72+V) := by
  have hXp := zero_lt_one.trans_le hX
  have hC0 := zero_le_one.trans hC
  have hPower : 1≤X^(6*ε) := Real.one_le_rpow hX (by positivity)
  have hCoeff : 1≤(2:ℝ)^293*C^6*X^(6*ε) :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
        (one_le_pow₀ hC)) hPower
  have hZ72 : Z^72≤32*C^6*X^(6*ε)*(Main^6+E^72) := by
    calc
      _ = (Z^12)^6 := by rw [←pow_mul]
      _ ≤ (C*X^ε*(Main+E^12))^6 :=
        pow_le_pow_left₀ (pow_nonneg hZ 12) hMoment 6
      _ = C^6*X^(6*ε)*(Main+E^12)^6 := by
        rw [mul_pow,mul_pow]
        have hp : (X^ε)^6=X^(6*ε) := by
          simpa only [Nat.cast_ofNat,mul_comm] using (Real.rpow_mul_natCast hXp.le ε 6).symm
        rw [hp]
      _ ≤ C^6*X^(6*ε)*((2:ℝ)^5*(Main^6+(E^12)^6)) :=
        mul_le_mul_of_nonneg_left (add_pow_le hMain (pow_nonneg hE 12) 6) (by positivity)
      _ = _ := by rw [←pow_mul]; norm_num; ring
  have hZweighted : w^72*Z^72≤(2:ℝ)^293*C^6*X^(6*ε)*V := by
    calc
      _ ≤ w^72*(32*C^6*X^(6*ε)*(Main^6+E^72)) :=
        mul_le_mul_of_nonneg_left hZ72 (pow_nonneg hw 72)
      _ = 32*C^6*X^(6*ε)*(w^72*(E^72+Main^6)) := by ring
      _ ≤ 32*C^6*X^(6*ε)*((2:ℝ)^288*V) :=
        mul_le_mul_of_nonneg_left hWeighted (by positivity)
      _ = _ := by
        rw [show (2:ℝ)^293=32*2^288 by
          rw [show (293:ℕ)=5+288 by rfl,pow_add,show (2:ℝ)^5=32 by norm_num]]
        have heq (a b c d : ℝ) : 32*a*b*(c*d)=(32*c)*a*b*d := by ring
        exact heq _ _ _ _
  have hDiag : d^72≤(2:ℝ)^293*C^6*X^(6*ε)*d^72 :=
    le_mul_of_one_le_left (pow_nonneg hd 72) hCoeff
  calc
    _ = (S^4)^72 := by rw [←pow_mul]
    _ ≤ (Q*(d+w*Z))^72 := pow_le_pow_left₀ (pow_nonneg hS 4) hWeyl 72
    _ = Q^72*(d+w*Z)^72 := mul_pow _ _ _
    _ ≤ Q^72*((2:ℝ)^71*(d^72+(w*Z)^72)) :=
      mul_le_mul_of_nonneg_left (add_pow_le hd (mul_nonneg hw hZ) 72) (pow_nonneg hQ 72)
    _ = (2:ℝ)^71*Q^72*(d^72+w^72*Z^72) := by
      rw [mul_pow]
      exact (mul_left_comm _ _ _).trans (mul_assoc _ _ _).symm
    _ ≤ (2:ℝ)^71*Q^72*((2:ℝ)^293*C^6*X^(6*ε)*d^72+
        (2:ℝ)^293*C^6*X^(6*ε)*V) :=
      mul_le_mul_of_nonneg_left (add_le_add hDiag hZweighted)
        (mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) 71) (pow_nonneg hQ 72))
    _ = _ := by
      rw [show (2:ℝ)^364=2^71*2^293 by rw [←pow_add]]
      have heq (a b c d e f g : ℝ) :
          a*b*(c*d*e*f+c*d*e*g)=(a*c)*b*d*e*(f+g) := by ring
      exact heq _ _ _ _ _ _ _

-- Generated closures: source context is replayed in the next part.
end TaoTrudgianYang2025.HuxleyRationalPhase
end
end
