module
public import LaterPairs.Native.HuxleyCore.Part02

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


private theorem eventually_positive_difference_selected_eight_grid_chunk_physical_sieve
    {σsrc csrc Usrc σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
    ∃ Csrc η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      1 ≤ Csrc ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {θ : ℝ}, 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (Q K₀ N Uref : ℕ) [NeZero K₀] (R Jsep : ℝ) {η M δ Bcut Bselect : ℝ},
    0 < η → η ≤ η₀ → 0 < T → 2 ≤ N →
    1 ≤ R → R ≤ M → 0 ≤ δ → δ ≤ min κ 1 →
    0 < Jsep → Jsep ≤ M →
    (∀ y ∈ Y, y ∈ Icc (1:ℝ) 2) →
    (∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → 1 ≤ Jsep*|y-z|) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (∀ y ∈ Y, Expdb.IsApproximateModelPhaseFunction
      (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
    T*(N:ℝ)*R^2 = M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc/σsrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/(4*σsrc))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    12*Usrc ≤ σsrc*(Uref:ℝ) →
    63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
    (Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2 →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    1 ≤ Uref → 0 < Bcut →
    2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2 →
    (Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect →
    ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Uref:ℝ) →
    (N:ℝ)^10 ≤ M^3*R^7 →
    Q ≤ N → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    768*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let Vscale := (Uref:ℝ)^((3:ℝ)/2)
    let lambda := csrc*κ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*T/(2*M^2)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    let μ₀ := csrc*T/(12*σsrc*M^3)
    let U₀ := Usrc*T/(2*σsrc*M^3)
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
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := R^4/((N:ℝ)^2*(Uref:ℝ))
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Kupper := 240*CostUpper*
      (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := 240*CostLower*
      (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    let Klarge := 2*Bselect*60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain+Ctail)*((Q:ℝ)/(N:ℝ))^((2:ℝ)/3)

    let Buffer := (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    let Error := (Y.card:ℝ)*(M/(N:ℝ)+1)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
    let FamilyBound := fun (P : Finset (ℝ × ℤ)) =>
      (48*σsrc/csrc)^6*(R^2/(Q:ℝ))^6*
        C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*
          (Vscale*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
            ((P.image Prod.fst).card:ℝ)^2*(Vscale*(Kupper+Klower)+Klarge)*T^εloss)
    let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    ∀ n : ℕ, N=8*n →
    ∀ (Chunks : Finset (ℝ × ℤ))
      (anchor : (ℝ × ℤ) → Fin 2 → ℚ) (za : (ℝ × ℤ) → Fin 2 → ℝ),
    (∀ p∈Chunks, p.1∈Y) →
    (∀ p∈Chunks, (n:ℝ)*p.2∈
      Icc (M+Buffer+(14*σsrc/csrc)*(Uref:ℝ)*(N:ℝ)+4*(N:ℝ))
        (2*M-Buffer-(14*σsrc/csrc)*(Uref:ℝ)*(N:ℝ)-(N:ℝ))) →
    (∀ p∈Chunks, ∀ i : Fin 2,
      |za p i-(if i=0 then (n:ℝ)*p.2-2*(N:ℝ)
        else (n:ℝ)*p.2-11*(N:ℝ)/4)| ≤ (N:ℝ)/16 ∧
      h p.1 (za p i)=(anchor p i:ℝ) ∧
      768*(anchor p i).den ≤ Q ∧
      (24576*σsrc)*R^2 ≤ csrc*(Q:ℝ)*(anchor p i).den) →
    ∃ Dcover : Finset (ℝ × ℤ),
      Dcover ⊆ Chunks ∪ Chunks.image (fun p => (p.1,p.2-6)) ∧
      Dcover.card ≤ 2*Chunks.card ∧
      let Grid := fun r : ℤ =>
        (Dcover.filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
      (∀ r, (Grid r).card ≤ 2*Chunks.card) ∧
      (∀ r, (Grid r).image Prod.fst ⊆ Chunks.image Prod.fst) ∧
      (∑ p∈Chunks, ‖∑ k∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),
        (𝐞 (f p.1 k):ℂ)‖)^12 ≤
        (4:ℝ)^12*(8:ℝ)^11*∑ r∈Finset.Ico (0:ℤ) 8,
          (2^11*((Csrc*Error)^12+
            (Csrc*(1+Real.log K₀))^12*FamilyBound (Grid r))) := by

  classical
  intro κ Ratio L
  obtain ⟨Csrc,η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,hcore⟩ :=
    TaoTrudgianYang2025.HuxleyRationalPhase.eventually_positive_difference_selected_reference_core_physical_sieve
      hσsrc hcsrc hUsrc hσ hεloss hanchorBudget
  refine ⟨Csrc,η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,?_⟩
  intro θ hθ hθmax hθaction
  filter_upwards [hcore hθ hθmax hθaction] with T hcoreT
  intro Fsrc Y Q K₀ N Uref instK R Jsep η M δ Bcut Bselect
    hη hηsmall hT hNtwo hR hRM hδzero hδ hJsep hJM hy hsepY
    hreg hjets htests hnegative hmodels hscale hpad hquartic hquad hUlarge
    hsourceMesh hmesh hregime hUref hBcut hBselectSize hcutMargin hselectedWrap
    hselectedUpper hUlo hscaleTen hQN hNsqM hUR hstrongRQ hNRM
    Cphys c J B hsmall hNR hRN hNcube hminscale
    Vscale lambda Uband ChartCap NarrowCap Cap μ₀ U₀ Δtype
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird AupperConst BupperConst AlowerConst BlowerConst
    DupperConst DlowerConst CostUpper CostLower Cpack Cfirst Cgap Cmain Ctail
    Kupper Klower Klarge Buffer Error FamilyBound f h
    n hNlink Chunks anchor za hChunks hDeep hAnchors
  have hUlarge₃ : 3*Usrc ≤ σsrc*(Uref:ℝ) := by linarith only [hUlarge,hUsrc]
  obtain ⟨Refs,hRefSep,hRefGap,henclose,hroots,hgrid⟩ :=
    hcoreT Fsrc Y Q K₀ N Uref R Jsep  (η:=η) (M:=M) (δ:=δ)
      (Bcut:=Bcut) (Bselect:=Bselect)
      hη hηsmall hT hNtwo hR hRM  hδzero hδ hJsep hJM hy hsepY
      hreg hjets htests hnegative hmodels hscale hpad hquartic hquad hUlarge₃
      hsourceMesh hmesh hregime hUref hBcut hBselectSize hcutMargin hselectedWrap
      hselectedUpper hUlo hscaleTen hQN hNsqM hUR hstrongRQ hNRM
      hsmall hNR hRN hNcube hminscale hsize hD hΔ hBsize
  have hn : 0 < n := by omega
  have hNreal : (N:ℝ)=8*(n:ℝ) := by exact_mod_cast hNlink
  have hNint : (N:ℤ)=8*(n:ℤ) := by exact_mod_cast hNlink
  have hNpos : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hM : 0 < M := by nlinarith only [hNpos,hNsqM]
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hBuffer : 0 ≤ Buffer := by dsimp only [Buffer]; positivity
  have hscale' : T*(8*(n:ℝ))*R^2=M^3 := by rw [←hNreal]; exact hscale
  obtain ⟨H,hH,hcover⟩ := positive_difference_eight_grid_chunk_cover Fsrc Y Refs n
    hn hσsrc hcsrc hUsrc hη (hηsmall.trans hηcap) hy hreg hjets hnegative
    hT hM hRpos hscale' hRefSep hRefGap hUlarge hBuffer henclose hroots
  obtain ⟨Dcover,hDsub,hDgood,hChunksBound⟩ :=
    hcover Chunks hChunks (by simpa only [←hNreal] using hDeep)
  obtain ⟨aGrid,zGrid,hDcard,hGridCardBound,hGridPhase,hGridAnchors⟩ :=
    eight_grid_selected_anchor_transport Chunks Dcover n N Q hNlink h σsrc csrc R
      anchor za hDsub hAnchors
  refine ⟨Dcover,hDsub,hDcard,?_⟩
  intro Grid
  refine ⟨hGridCardBound,hGridPhase,?_⟩
  let X := fun r : ℤ => ∑ p∈Grid r,
    ‖∑ k∈Finset.Ioc ((n:ℤ)*(r+8*p.2+16))
      ((n:ℤ)*(r+8*p.2+16)+(H p.1 ((n:ℤ)*(r+8*p.2+16)):ℤ)),
        (𝐞 (f p.1 k):ℂ)‖
  let CoreBound := fun r : ℤ => 2^11*((Csrc*Error)^12+
    (Csrc*(1+Real.log K₀))^12*FamilyBound (Grid r))
  have hDphase q (hq : q∈Dcover) : q.1∈Y := by
    rcases Finset.mem_union.mp (hDsub hq) with hh | hh
    · exact hChunks q hh
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hh
      exact hChunks p hp
  have hLgrid (r k : ℤ) :
      r*(n:ℤ)+(N:ℤ)*k+2*(N:ℤ)=(n:ℤ)*(r+8*k+16) := by
    rw [hNint]
    ring
  have hXbound (r : ℤ) : (X r)^12 ≤ CoreBound r := by
    let Hgrid := fun y k => H y (r*(n:ℤ)+(N:ℤ)*k+2*(N:ℤ))
    have hHgrid y (_hy : y∈Y) k : Hgrid y k ≤ N := by
      rw [hNlink]
      exact hH y _
    have hGoodGrid : ∀ p∈Grid r, p.1∈Y ∧
        ∃ a∈Refs, ∃ b∈Refs, a < b ∧ (∀ q∈Refs,¬(a < q ∧ q < b)) ∧
          ∃ z₁ z₂ : ℝ, z₁∈Icc M (2*M) ∧ z₂∈Icc M (2*M) ∧
            iteratedDeriv 2 (f p.1) z₁/2=a ∧ iteratedDeriv 2 (f p.1) z₂/2=b ∧
            M+Buffer ≤ z₁ ∧ z₂ ≤ 2*M-Buffer ∧
            z₁+(N:ℝ)/4 ≤ (r*(n:ℤ):ℤ)+(N:ℝ)*p.2 ∧
              (r*(n:ℤ):ℤ)+(N:ℝ)*p.2 ≤ z₂-(N:ℝ)/4 := by
      intro p hp
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hqD,hqmod⟩ := Finset.mem_filter.mp hq
      refine ⟨hDphase q hqD,?_⟩
      have hdecomp : (q.2:ℝ)=(r:ℝ)+8*((q.2/8-2:ℤ):ℝ)+16 := by
        exact_mod_cast (show q.2=r+8*(q.2/8-2)+16 by omega)
      have htEq : ((r*(n:ℤ):ℤ):ℝ)+(N:ℝ)*((q.2/8-2:ℤ):ℝ)=
          (n:ℝ)*q.2-2*(N:ℝ) := by
        rw [hNreal,hdecomp]
        push_cast
        ring
      dsimp only
      rw [htEq,hNreal]
      exact hDgood q hqD
    have hh := hgrid (r*(n:ℤ)) Hgrid hHgrid (Grid r) (aGrid r) (zGrid r)
      hGoodGrid
      (fun p hp => ⟨(hGridAnchors r p hp).1,(hGridAnchors r p hp).2.1⟩)
      (fun p hp => (hGridAnchors r p hp).2.2.1)
      (fun p hp => (hGridAnchors r p hp).2.2.2)
    change (∑ p∈Grid r,
      ‖∑ k∈Finset.Ioc (r*(n:ℤ)+(N:ℤ)*p.2+2*(N:ℤ))
        (r*(n:ℤ)+(N:ℤ)*p.2+2*(N:ℤ)+(Hgrid p.1 p.2:ℤ)),
        (𝐞 (f p.1 k):ℂ)‖)^12 ≤ CoreBound r at hh
    simpa only [X,Hgrid,hLgrid] using hh
  let Grids := Finset.Ico (0:ℤ) 8
  have hXnonneg r : 0 ≤ X r := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hGridCard : Grids.card=8 := by decide
  have hholder := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Grids
    (f:=X) (p:=(12:ℝ)) (by norm_num) (fun r _ => hXnonneg r)
  have hh : (∑ r∈Grids,X r)^12 ≤ (8:ℝ)^11*∑ r∈Grids,(X r)^12 := by
    simpa only [hGridCard,Nat.cast_ofNat,
      show (12:ℝ)-1=11 by norm_num,Real.rpow_ofNat] using hholder
  have hs : (∑ r∈Grids,(X r)^12) ≤ ∑ r∈Grids,CoreBound r :=
    Finset.sum_le_sum (fun r _ => hXbound r)
  calc
    _ ≤ (4*∑ r∈Grids,X r)^12 :=
      pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hChunksBound 12
    _ = (4:ℝ)^12*(∑ r∈Grids,X r)^12 := mul_pow _ _ _
    _ ≤ (4:ℝ)^12*((8:ℝ)^11*∑ r∈Grids,CoreBound r) :=
      mul_le_mul_of_nonneg_left
        (hh.trans (mul_le_mul_of_nonneg_left hs (by norm_num))) (by norm_num)
    _ = _ := by rw [mul_assoc]

private theorem eventually_positive_difference_triangular_selected_eight_grid_chunk_physical_sieve
    {σsrc csrc Usrc σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
    ∃ Csrc η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      1 ≤ Csrc ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {θ : ℝ}, 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (Q K₀ N Uref : ℕ) [NeZero K₀] (R Jsep Vscale : ℝ) {η M δ Bcut Bselect : ℝ},
    0 < η → η ≤ η₀ → 0 < T → 2 ≤ N →
    1 ≤ R → R ≤ M → 1 ≤ Vscale → 0 ≤ δ → δ ≤ min κ 1 →
    0 < Jsep → Jsep ≤ M →
    (∀ y ∈ Y, y ∈ Icc (1:ℝ) 2) →
    (∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → 1 ≤ Jsep*|y-z|) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (∀ y ∈ Y, Expdb.IsApproximateModelPhaseFunction
      (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
    T*(N:ℝ)*R^2 = M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc/σsrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/(4*σsrc))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    12*Usrc ≤ σsrc*(Uref:ℝ) →
    63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
    (Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2 →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    1 ≤ Uref → 0 < Bcut →
    2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2 →
    (Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect →
    (N:ℝ)^10 ≤ M^3*R^7 →
    Q ≤ N → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    768*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let Uband := (3*Usrc/σsrc)*T/(2*M^2)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    let μ₀ := csrc*T/(12*σsrc*M^3)
    let U₀ := Usrc*T/(2*σsrc*M^3)
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
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := R^4/((N:ℝ)^2*(Uref:ℝ))
    let Kupper := 240*CostUpper*
      (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := 240*CostLower*
      (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    ∀ isUpper : Bool,
    (if isUpper then Vscale=1+R^4/(6*(N:ℝ)^2)
      else Uband ≤ 1/16 ∧ Vscale=1+R^4*Uband^2/(N:ℝ)^2) →
    let Buffer := (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    let Error := (Y.card:ℝ)*(M/(N:ℝ)+1)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
    let FamilyBound := fun (P : Finset (ℝ × ℤ)) =>
      (48*σsrc/csrc)^6*(R^2/(Q:ℝ))^6*
        C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*
          (Vscale*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
            ((P.image Prod.fst).card:ℝ)^2*Vscale*(if isUpper then Kupper else Klower)*T^εloss)
    let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    ∀ n : ℕ, N=8*n →
    ∀ (Chunks : Finset (ℝ × ℤ))
      (anchor : (ℝ × ℤ) → Fin 2 → ℚ) (za : (ℝ × ℤ) → Fin 2 → ℝ),
    (∀ p∈Chunks, p.1∈Y) →
    (∀ p∈Chunks, (n:ℝ)*p.2∈
      Icc (M+Buffer+(14*σsrc/csrc)*(Uref:ℝ)*(N:ℝ)+4*(N:ℝ))
        (2*M-Buffer-(14*σsrc/csrc)*(Uref:ℝ)*(N:ℝ)-(N:ℝ))) →
    (∀ p∈Chunks, ∀ i : Fin 2,
      |za p i-(if i=0 then (n:ℝ)*p.2-2*(N:ℝ)
        else (n:ℝ)*p.2-11*(N:ℝ)/4)| ≤ (N:ℝ)/16 ∧
      h p.1 (za p i)=(anchor p i:ℝ) ∧
      768*(anchor p i).den ≤ Q ∧
      (24576*σsrc)*R^2 ≤ csrc*(Q:ℝ)*(anchor p i).den) →
    ∃ Dcover : Finset (ℝ × ℤ),
      Dcover ⊆ Chunks ∪ Chunks.image (fun p => (p.1,p.2-6)) ∧
      Dcover.card ≤ 2*Chunks.card ∧
      let Grid := fun r : ℤ =>
        (Dcover.filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
      (∀ r, (Grid r).card ≤ 2*Chunks.card) ∧
      (∀ r, (Grid r).image Prod.fst ⊆ Chunks.image Prod.fst) ∧
      (∑ p∈Chunks, ‖∑ k∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),
        (𝐞 (f p.1 k):ℂ)‖)^12 ≤
        (4:ℝ)^12*(8:ℝ)^11*∑ r∈Finset.Ico (0:ℤ) 8,
          (2^11*((Csrc*Error)^12+
            (Csrc*(1+Real.log K₀))^12*FamilyBound (Grid r))) := by

  classical
  intro κ Ratio L
  obtain ⟨Csrc,η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,hcore⟩ :=
    TaoTrudgianYang2025.HuxleyRationalPhase.eventually_positive_difference_triangular_selected_reference_core_physical_sieve
      hσsrc hcsrc hUsrc hσ hεloss hanchorBudget
  refine ⟨Csrc,η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,?_⟩
  intro θ hθ hθmax hθaction
  filter_upwards [hcore hθ hθmax hθaction] with T hcoreT
  intro Fsrc Y Q K₀ N Uref instK R Jsep Vscale η M δ Bcut Bselect
    hη hηsmall hT hNtwo hR hRM hVscale hδzero hδ hJsep hJM hy hsepY
    hreg hjets htests hnegative hmodels hscale hpad hquartic hquad hUlarge
    hsourceMesh hmesh hregime hUref hBcut hBselectSize hcutMargin hselectedWrap
    hselectedUpper hscaleTen hQN hNsqM hUR hstrongRQ hNRM
    Cphys c J B hsmall hNR hRN hNcube hminscale
    Uband ChartCap NarrowCap Cap μ₀ U₀ Δtype
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird AupperConst BupperConst AlowerConst BlowerConst
    DupperConst DlowerConst CostUpper CostLower
    Kupper Klower isUpper hchoice Buffer Error FamilyBound f h
    n hNlink Chunks anchor za hChunks hDeep hAnchors
  have hUlarge₃ : 3*Usrc ≤ σsrc*(Uref:ℝ) := by linarith only [hUlarge,hUsrc]
  obtain ⟨Refs,hRefSep,hRefGap,henclose,hroots,hgrid⟩ :=
    hcoreT Fsrc Y Q K₀ N Uref R Jsep Vscale (η:=η) (M:=M) (δ:=δ)
      (Bcut:=Bcut) (Bselect:=Bselect)
      hη hηsmall hT hNtwo hR hRM hVscale hδzero hδ hJsep hJM hy hsepY
      hreg hjets htests hnegative hmodels hscale hpad hquartic hquad hUlarge₃
      hsourceMesh hmesh hregime hUref hBcut hBselectSize hcutMargin hselectedWrap
      hselectedUpper  hscaleTen hQN hNsqM hUR hstrongRQ hNRM
      hsmall hNR hRN hNcube hminscale hsize hD hΔ hBsize isUpper hchoice
  have hn : 0 < n := by omega
  have hNreal : (N:ℝ)=8*(n:ℝ) := by exact_mod_cast hNlink
  have hNint : (N:ℤ)=8*(n:ℤ) := by exact_mod_cast hNlink
  have hNpos : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hM : 0 < M := by nlinarith only [hNpos,hNsqM]
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hBuffer : 0 ≤ Buffer := by dsimp only [Buffer]; positivity
  have hscale' : T*(8*(n:ℝ))*R^2=M^3 := by rw [←hNreal]; exact hscale
  obtain ⟨H,hH,hcover⟩ := positive_difference_eight_grid_chunk_cover Fsrc Y Refs n
    hn hσsrc hcsrc hUsrc hη (hηsmall.trans hηcap) hy hreg hjets hnegative
    hT hM hRpos hscale' hRefSep hRefGap hUlarge hBuffer henclose hroots
  obtain ⟨Dcover,hDsub,hDgood,hChunksBound⟩ :=
    hcover Chunks hChunks (by simpa only [←hNreal] using hDeep)
  obtain ⟨aGrid,zGrid,hDcard,hGridCardBound,hGridPhase,hGridAnchors⟩ :=
    eight_grid_selected_anchor_transport Chunks Dcover n N Q hNlink h σsrc csrc R
      anchor za hDsub hAnchors
  refine ⟨Dcover,hDsub,hDcard,?_⟩
  intro Grid
  refine ⟨hGridCardBound,hGridPhase,?_⟩
  let X := fun r : ℤ => ∑ p∈Grid r,
    ‖∑ k∈Finset.Ioc ((n:ℤ)*(r+8*p.2+16))
      ((n:ℤ)*(r+8*p.2+16)+(H p.1 ((n:ℤ)*(r+8*p.2+16)):ℤ)),
        (𝐞 (f p.1 k):ℂ)‖
  let CoreBound := fun r : ℤ => 2^11*((Csrc*Error)^12+
    (Csrc*(1+Real.log K₀))^12*FamilyBound (Grid r))
  have hDphase q (hq : q∈Dcover) : q.1∈Y := by
    rcases Finset.mem_union.mp (hDsub hq) with hh | hh
    · exact hChunks q hh
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hh
      exact hChunks p hp
  have hLgrid (r k : ℤ) :
      r*(n:ℤ)+(N:ℤ)*k+2*(N:ℤ)=(n:ℤ)*(r+8*k+16) := by
    rw [hNint]
    ring
  have hXbound (r : ℤ) : (X r)^12 ≤ CoreBound r := by
    let Hgrid := fun y k => H y (r*(n:ℤ)+(N:ℤ)*k+2*(N:ℤ))
    have hHgrid y (_hy : y∈Y) k : Hgrid y k ≤ N := by
      rw [hNlink]
      exact hH y _
    have hGoodGrid : ∀ p∈Grid r, p.1∈Y ∧
        ∃ a∈Refs, ∃ b∈Refs, a < b ∧ (∀ q∈Refs,¬(a < q ∧ q < b)) ∧
          ∃ z₁ z₂ : ℝ, z₁∈Icc M (2*M) ∧ z₂∈Icc M (2*M) ∧
            iteratedDeriv 2 (f p.1) z₁/2=a ∧ iteratedDeriv 2 (f p.1) z₂/2=b ∧
            M+Buffer ≤ z₁ ∧ z₂ ≤ 2*M-Buffer ∧
            z₁+(N:ℝ)/4 ≤ (r*(n:ℤ):ℤ)+(N:ℝ)*p.2 ∧
              (r*(n:ℤ):ℤ)+(N:ℝ)*p.2 ≤ z₂-(N:ℝ)/4 := by
      intro p hp
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hqD,hqmod⟩ := Finset.mem_filter.mp hq
      refine ⟨hDphase q hqD,?_⟩
      have hdecomp : (q.2:ℝ)=(r:ℝ)+8*((q.2/8-2:ℤ):ℝ)+16 := by
        exact_mod_cast (show q.2=r+8*(q.2/8-2)+16 by omega)
      have htEq : ((r*(n:ℤ):ℤ):ℝ)+(N:ℝ)*((q.2/8-2:ℤ):ℝ)=
          (n:ℝ)*q.2-2*(N:ℝ) := by
        rw [hNreal,hdecomp]
        push_cast
        ring
      dsimp only
      rw [htEq,hNreal]
      exact hDgood q hqD
    have hh := hgrid (r*(n:ℤ)) Hgrid hHgrid (Grid r) (aGrid r) (zGrid r)
      hGoodGrid
      (fun p hp => ⟨(hGridAnchors r p hp).1,(hGridAnchors r p hp).2.1⟩)
      (fun p hp => (hGridAnchors r p hp).2.2.1)
      (fun p hp => (hGridAnchors r p hp).2.2.2)
    change (∑ p∈Grid r,
      ‖∑ k∈Finset.Ioc (r*(n:ℤ)+(N:ℤ)*p.2+2*(N:ℤ))
        (r*(n:ℤ)+(N:ℤ)*p.2+2*(N:ℤ)+(Hgrid p.1 p.2:ℤ)),
        (𝐞 (f p.1 k):ℂ)‖)^12 ≤ CoreBound r at hh
    simpa only [X,Hgrid,hLgrid] using hh
  let Grids := Finset.Ico (0:ℤ) 8
  have hXnonneg r : 0 ≤ X r := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hGridCard : Grids.card=8 := by decide
  have hholder := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Grids
    (f:=X) (p:=(12:ℝ)) (by norm_num) (fun r _ => hXnonneg r)
  have hh : (∑ r∈Grids,X r)^12 ≤ (8:ℝ)^11*∑ r∈Grids,(X r)^12 := by
    simpa only [hGridCard,Nat.cast_ofNat,
      show (12:ℝ)-1=11 by norm_num,Real.rpow_ofNat] using hholder
  have hs : (∑ r∈Grids,(X r)^12) ≤ ∑ r∈Grids,CoreBound r :=
    Finset.sum_le_sum (fun r _ => hXbound r)
  calc
    _ ≤ (4*∑ r∈Grids,X r)^12 :=
      pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hChunksBound 12
    _ = (4:ℝ)^12*(∑ r∈Grids,X r)^12 := mul_pow _ _ _
    _ ≤ (4:ℝ)^12*((8:ℝ)^11*∑ r∈Grids,CoreBound r) :=
      mul_le_mul_of_nonneg_left
        (hh.trans (mul_le_mul_of_nonneg_left hs (by norm_num))) (by norm_num)
    _ = _ := by rw [mul_assoc]

private theorem positive_difference_chunk_grid_dyadic_bands
    (Chunks : Finset (ℝ × ℤ)) (Y : Finset ℝ) (F : ℝ → ℝ)
    (n N Qbase kmax : ℕ) (hNlink : N=8*n)
    {σ c J η T M R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hn : 0 < n) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hy : ∀ y∈Y, y∈Icc (1:ℝ) 2) (hphase : ∀ p∈Chunks, p.1∈Y)
    (hT : 0 < T) (hM : 0 < M) (hR : 0 < R)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ j ≤ 6, |iteratedDeriv (j+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hscale : T*(N:ℝ)*R^2=M^3)
    (hQbase : 768 ≤ Qbase)
    (hQmax : (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let probe := fun (p : ℝ × ℤ) (i : Fin 2) =>
      if i=0 then (n:ℝ)*p.2-2*(N:ℝ) else (n:ℝ)*p.2-11*(N:ℝ)/4
    (∀ p∈Chunks, ∀ i, probe p i∈Icc (M+(N:ℝ)/4) (2*M-(N:ℝ)/4)) →
    let Q := fun k : ℕ => Qbase*2^k
    let Ctail := (6*J/σ)*(64*σ/c)^2+192*σ/c
    let Clow := (3*J/σ+c/(32*σ))*((3072*σ)/c)^2+(3072*σ)/c
    let Cerror := (768:ℝ)^2*Ctail+Clow
    let Density := fun k => 128*Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (512*σ*R^2/(c*((Q k:ℝ)/768))+1))
    ∃ (anchor : (ℝ × ℤ) → Fin 2 → ℚ)
      (band : (ℝ × ℤ) → Option ℕ) (za : (ℝ × ℤ) → Fin 2 → ℝ),
      (∀ p∈Chunks, ∀ i,
        h p.1 (za p i)=(anchor p i:ℝ) ∧
        |za p i-probe p i| ≤ (N:ℝ)/16 ∧ za p i∈Icc M (2*M)) ∧
      (∀ p∈Chunks, match band p with
        | none => ∃ i, ¬(768*(anchor p i).den ≤ Q kmax ∧
            (24576*σ)*R^2 ≤ c*(Q kmax:ℝ)*(anchor p i).den)
        | some k => k ≤ kmax ∧
            (∀ i, 768*(anchor p i).den ≤ Q k ∧
              (24576*σ)*R^2 ≤ c*(Q k:ℝ)*(anchor p i).den)) ∧
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
    (2+Real.log (64*σ*Rfine^2/(c*((Q k:ℝ)/768))+1))
  have hDensity k : FineDensity k=Density k := by
    dsimp only [FineDensity,Density]
    rw [hRsq,hNreal]
    have he : 64*σ*(8*R^2)=512*σ*R^2 := by ring
    rw [he]
    ring
  have hex (y : ℝ) : ∃ (a : ℤ → Fin 2 → ℚ) (b : ℤ → Option ℕ)
      (z : ℤ → Fin 2 → ℝ), y∈Y →
      (∀ j∈Sy y, ∀ i, h y (z j i)=(a j i:ℝ) ∧
        |z j i-probe (y,j) i| ≤ (N:ℝ)/16 ∧ z j i∈Icc M (2*M)) ∧
      (∀ j∈Sy y, match b j with
        | none => ∃ i, ¬(768*(a j i).den ≤ Q kmax ∧
            (24576*σ)*R^2 ≤ c*(Q kmax:ℝ)*(a j i).den)
        | some k => k ≤ kmax ∧
            (∀ i, 768*(a j i).den ≤ Q k ∧
              (24576*σ)*R^2 ≤ c*(Q k:ℝ)*(a j i).den)) ∧
      (∀ k ≤ kmax, (((Sy y).filter (fun j => b j=some (k+1))).card:ℝ) ≤ Density k) ∧
      (((Sy y).filter (fun j => b j=none)).card:ℝ) ≤ Density kmax := by
    by_cases hyY : y∈Y
    · have hpointsFine j (hj : j∈Sy y) i :
          base i+(n:ℝ)*j∈Icc (M+(n:ℝ)/4) (2*M-(n:ℝ)/4) := by
        rw [hprobe y j i]
        have hh := hpoints (y,j) ((hSy y j).mp hj) i
        constructor <;> linarith only [hh.1,hh.2,hnN]
      obtain ⟨a,b,z,_hminimal,hroots,hband,_htransfer,hcounts,htail⟩ :=
        positive_difference_two_probe_dyadic_root_family (Sy y) F n Qbase kmax 768
          base (3072*σ) hσ hc hJ hη hηmax (hy y hyY)
          hreg hbound htests hnegative hT hM hn hRfine hscaleFine
          (by norm_num) hQbase (by positivity) hpointsFine hQfine
      refine ⟨a,b,z,fun _ => ⟨?_,?_,?_,?_⟩⟩
      · intro j hj i
        have hh := hroots j hj i
        change h y (z j i)=(a j i:ℝ) ∧
          |z j i-(base i+(n:ℝ)*j)| ≤ (n:ℝ)/16 ∧ z j i∈Icc M (2*M) at hh
        rw [hprobe y j i] at hh
        exact ⟨hh.1,hh.2.1.trans (div_le_div_of_nonneg_right hnN (by norm_num)),hh.2.2⟩
      · intro j hj
        have hh := hband j hj
        have hB : (3072*σ)*Rfine^2=(24576*σ)*R^2 := by rw [hRsq]; ring
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

public  theorem integer_chunk_dyadic_band_power
    {α : Type*} (Chunks : Finset (α × ℤ)) (v : α → ℤ → ℂ)
    (n kmax : ℕ) (band : (α × ℤ) → Option ℕ)
    (hv : ∀ y k, ‖v y k‖ ≤ 1)
    (hband : ∀ p∈Chunks, ∀ k, band p=some k → k ≤ kmax) :
    (∑ p∈Chunks, ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖)^12 ≤
      ((kmax:ℝ)+2)^11*
        (((n:ℝ)*((Chunks.filter (fun p => band p=none)).card:ℝ))^12+
          ∑ k∈Finset.range (kmax+1),
            (∑ p∈Chunks.filter (fun p => band p=some k),
              ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖)^12) := by
  classical
  let Labels := insert none ((Finset.range (kmax+1)).image some)
  let Chunk := fun p : α × ℤ =>
    ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖
  let W := fun label => ∑ p∈Chunks.filter (fun p => band p=label),Chunk p
  have hW label : 0 ≤ W label := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hmaps : ∀ p∈Chunks, band p∈Labels := by
    intro p hp
    cases hb : band p with
    | none => exact Finset.mem_insert_self _ _
    | some k =>
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr (by
        have hh := hband p hp k hb
        omega),rfl⟩
  have hsum : (∑ label∈Labels,W label)=∑ p∈Chunks,Chunk p :=
    Finset.sum_fiberwise_of_maps_to hmaps Chunk
  have hcardLabels : Labels.card=kmax+2 := by
    have hnone : (none : Option ℕ)∉(Finset.range (kmax+1)).image some := by simp
    change (insert none ((Finset.range (kmax+1)).image some)).card=kmax+2
    rw [Finset.card_insert_of_notMem hnone,
      Finset.card_image_of_injective _ (Option.some_injective _),Finset.card_range]
  have hholder := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Labels
    (f:=W) (p:=(12:ℝ)) (by norm_num) (fun label _ => hW label)
  have hpower : (∑ p∈Chunks,Chunk p)^12 ≤
      ((kmax:ℝ)+2)^11*∑ label∈Labels,(W label)^12 := by
    simpa only [hsum,hcardLabels,Nat.cast_add,Nat.cast_ofNat,
      show (12:ℝ)-1=11 by norm_num,Real.rpow_ofNat] using hholder
  have hchunk p : Chunk p ≤ (n:ℝ) := by
    have hcard : (Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1))).card=n := by
      rw [Int.card_Ioc,show (n:ℤ)*(p.2+1)-(n:ℤ)*p.2=(n:ℤ) by ring]
      simp only [Int.toNat_natCast]
    calc
      Chunk p ≤ ∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),‖v p.1 j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),(1:ℝ) :=
        Finset.sum_le_sum (fun j _ => hv p.1 j)
      _ = _ := by simp only [Finset.sum_const,hcard,nsmul_eq_mul,mul_one]
  have hterminal : W none ≤ (n:ℝ)*((Chunks.filter (fun p => band p=none)).card:ℝ) := by
    calc
      W none ≤ ∑ _p∈Chunks.filter (fun p => band p=none),(n:ℝ) :=
        Finset.sum_le_sum (fun p _ => hchunk p)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
  have hlabelSum : (∑ label∈Labels,(W label)^12)=
      (W none)^12+∑ k∈Finset.range (kmax+1),(W (some k))^12 := by
    rw [Finset.sum_insert (by simp)]
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact Option.some_injective _ hab
  calc
    _ ≤ ((kmax:ℝ)+2)^11*∑ label∈Labels,(W label)^12 := hpower
    _ = ((kmax:ℝ)+2)^11*((W none)^12+
        ∑ k∈Finset.range (kmax+1),(W (some k))^12) := by rw [hlabelSum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (pow_le_pow_left₀ (hW none) hterminal 12) le_rfl) (by positivity)

private theorem integer_subinterval_trimmed_chunk_selection
    (n : ℕ) (hn : 0 < n) {A₀ B₀ a₀ b₀ A B : ℤ}
    (ha₀ : A₀ ≤ (n:ℤ)*a₀) (hb₀ : (n:ℤ)*b₀ ≤ B₀)
    (hA : A₀ ≤ A) (hB : B ≤ B₀) :
    let Budget : ℤ := ((n:ℤ)*a₀-A₀)+(B₀-(n:ℤ)*b₀)+2*(n:ℤ)
    B-A ≤ Budget ∨
      ∃ a b : ℤ, a₀ ≤ a ∧ b ≤ b₀ ∧ A ≤ (n:ℤ)*a ∧ a ≤ b ∧
        (n:ℤ)*b ≤ B ∧ ((n:ℤ)*a-A)+(B-(n:ℤ)*b) ≤ Budget := by
  intro Budget
  have hnz : (0:ℤ) < n := by exact_mod_cast hn
  have hceil : A < (n:ℤ)*(A/(n:ℤ)+1) ∧ (n:ℤ)*(A/(n:ℤ)+1) ≤ A+n := by
    have hzero := Int.emod_nonneg A hnz.ne'
    have hupper := Int.emod_lt_of_pos A hnz
    have heq := Int.mul_ediv_add_emod A (n:ℤ)
    constructor <;> nlinarith only [hzero,hupper,heq]
  have hfloor : (n:ℤ)*(B/(n:ℤ)) ≤ B ∧ B ≤ (n:ℤ)*(B/(n:ℤ))+n := by
    have hzero := Int.emod_nonneg B hnz.ne'
    have hupper := Int.emod_lt_of_pos B hnz
    have heq := Int.mul_ediv_add_emod B (n:ℤ)
    constructor <;> linarith only [hzero,hupper,heq]
  let a := max a₀ (A/(n:ℤ)+1)
  let b := min b₀ (B/(n:ℤ))
  have ha : A ≤ (n:ℤ)*a :=
    hceil.1.le.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hnz.le)
  have hb : (n:ℤ)*b ≤ B :=
    (mul_le_mul_of_nonneg_left (min_le_right _ _) hnz.le).trans hfloor.1
  have hleft : (n:ℤ)*a-A ≤ (n:ℤ)*a₀-A₀+n := by
    rcases le_total a₀ (A/(n:ℤ)+1) with hh | hh
    · rw [show a=A/(n:ℤ)+1 from max_eq_right hh]
      linarith only [hceil.2,ha₀]
    · rw [show a=a₀ from max_eq_left hh]
      linarith only [hA,hnz]
  have hright : B-(n:ℤ)*b ≤ B₀-(n:ℤ)*b₀+n := by
    rcases le_total b₀ (B/(n:ℤ)) with hh | hh
    · rw [show b=b₀ from min_eq_left hh]
      linarith only [hB,hnz]
    · rw [show b=B/(n:ℤ) from min_eq_right hh]
      linarith only [hfloor.2,hb₀]
  have hbudget : ((n:ℤ)*a-A)+(B-(n:ℤ)*b) ≤ Budget := by
    dsimp only [Budget]
    linarith only [hleft,hright]
  by_cases hab : a ≤ b
  · exact Or.inr ⟨a,b,le_max_left _ _,min_le_left _ _,ha,hab,hb,hbudget⟩
  · left
    have horder : (n:ℤ)*b ≤ (n:ℤ)*a :=
      mul_le_mul_of_nonneg_left (le_of_not_ge hab) hnz.le
    linarith only [hbudget,horder]

private theorem integer_subinterval_trimmed_chunks {α : Type*}
    (Y : Finset α) (v : α → ℤ → ℂ) (n : ℕ) (hn : 0 < n)
    {A₀ B₀ a₀ b₀ A B : ℤ}
    (ha₀ : A₀ ≤ (n:ℤ)*a₀) (hb₀ : (n:ℤ)*b₀ ≤ B₀)
    (hA : A₀ ≤ A) (hB : B ≤ B₀) (hab : A ≤ B)
    (hv : ∀ y∈Y, ∀ j∈Finset.Ioc A B, ‖v y j‖ ≤ 1) :
    let Budget : ℤ := ((n:ℤ)*a₀-A₀)+(B₀-(n:ℤ)*b₀)+2*(n:ℤ)
    ∃ Chunks : Finset (α × ℤ), Chunks ⊆ Y ×ˢ Finset.Ico a₀ b₀ ∧
      (∑ y∈Y, ‖∑ j∈Finset.Ioc A B,v y j‖) ≤
        (∑ p∈Chunks, ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖)+
          (Y.card:ℝ)*(Budget:ℝ) := by
  classical
  intro Budget
  rcases integer_subinterval_trimmed_chunk_selection n hn ha₀ hb₀ hA hB with
    hshort | ⟨a,b,haa,hbb,ha,hab',hb,hcost⟩
  · refine ⟨∅,Finset.empty_subset _,?_⟩
    have hcard : ((Finset.Ioc A B).card:ℝ)=((B-A:ℤ):ℝ) := by
      exact_mod_cast (show ((Finset.Ioc A B).card:ℤ)=B-A by
        rw [Int.card_Ioc,Int.toNat_of_nonneg (sub_nonneg.mpr hab)])
    have hone y (hyY : y∈Y) : ‖∑ j∈Finset.Ioc A B,v y j‖ ≤ (Budget:ℝ) := by
      calc
        _ ≤ ∑ j∈Finset.Ioc A B,‖v y j‖ := norm_sum_le _ _
        _ ≤ ∑ _j∈Finset.Ioc A B,(1:ℝ) := Finset.sum_le_sum (fun j hj => hv y hyY j hj)
        _ = ((B-A:ℤ):ℝ) := by simp only [Finset.sum_const,nsmul_eq_mul,mul_one,hcard]
        _ ≤ (Budget:ℝ) := by exact_mod_cast hshort
    have hh := Finset.sum_le_sum hone
    simpa only [Finset.sum_empty,zero_add,Finset.sum_const,nsmul_eq_mul] using hh
  · let Chunks := Y ×ˢ Finset.Ico a b
    refine ⟨Chunks,?_,?_⟩
    · intro p hp
      obtain ⟨hpY,hpI⟩ := Finset.mem_product.mp hp
      obtain ⟨hpa,hpb⟩ := Finset.mem_Ico.mp hpI
      exact Finset.mem_product.mpr ⟨hpY,Finset.mem_Ico.mpr
        ⟨haa.trans hpa,hpb.trans_le hbb⟩⟩
    · have hh := Finset.sum_le_sum (fun y hyY =>
        integer_whole_sum_le_chunks_and_endpoints (v y) n ha hab' hb (hv y hyY))
      have hmid : (∑ y∈Y, ‖∑ j∈Finset.Ioc A B,v y j‖) ≤
          (∑ p∈Chunks, ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖)+
            (Y.card:ℝ)*((((n:ℤ)*a-A)+(B-(n:ℤ)*b):ℤ):ℝ) := by
        convert hh using 1
        simp only [Chunks,Finset.sum_product,Finset.sum_add_distrib,Finset.sum_const,
          nsmul_eq_mul,Int.cast_add]
        ring
      exact hmid.trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hcost) (Nat.cast_nonneg _)))

public  theorem integer_phase_subinterval_trimmed_chunks {α : Type*}
    (Y : Finset α) (v : α → ℤ → ℂ) (n : ℕ) (hn : 0 < n)
    {A₀ B₀ a₀ b₀ : ℤ} (A B : α → ℤ)
    (ha₀ : A₀ ≤ (n:ℤ)*a₀) (hb₀ : (n:ℤ)*b₀ ≤ B₀)
    (hA : ∀ y∈Y, A₀ ≤ A y) (hB : ∀ y∈Y, B y ≤ B₀)
    (hab : ∀ y∈Y, A y ≤ B y)
    (hv : ∀ y∈Y, ∀ j∈Finset.Ioc (A y) (B y), ‖v y j‖ ≤ 1) :
    let Budget : ℤ := ((n:ℤ)*a₀-A₀)+(B₀-(n:ℤ)*b₀)+2*(n:ℤ)
    ∃ Chunks : Finset (α × ℤ), Chunks ⊆ Y ×ˢ Finset.Ico a₀ b₀ ∧
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (B y),v y j‖) ≤
        (∑ p∈Chunks, ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖)+
          (Y.card:ℝ)*(Budget:ℝ) := by
  classical
  intro Budget
  let Chunk := fun p : α × ℤ =>
    ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖
  have hex (y : α) : ∃ Cy : Finset (α × ℤ), y∈Y →
      Cy ⊆ {y} ×ˢ Finset.Ico a₀ b₀ ∧
      ‖∑ j∈Finset.Ioc (A y) (B y),v y j‖ ≤ (∑ p∈Cy,Chunk p)+(Budget:ℝ) := by
    by_cases hy : y∈Y
    · obtain ⟨Cy,hCy,hbound⟩ :=
        integer_subinterval_trimmed_chunks {y} v n hn ha₀ hb₀
          (hA y hy) (hB y hy) (hab y hy) (by
            intro z hz j hj
            have heq : z=y := Finset.mem_singleton.mp hz
            subst z
            exact hv y hy j hj)
      exact ⟨Cy,fun _ => ⟨hCy,by
        simpa only [Finset.sum_singleton,Finset.card_singleton,Nat.cast_one,one_mul]
          using hbound⟩⟩
    · exact ⟨∅,fun hh => (hy hh).elim⟩
  choose Cy hCy using hex
  have hphase y (hy : y∈Y) p (hp : p∈Cy y) : p.1=y :=
    Finset.mem_singleton.mp (Finset.mem_product.mp ((hCy y hy).1 hp)).1
  have hdisj : ∀ y∈Y, ∀ z∈Y, y≠z → Disjoint (Cy y) (Cy z) := by
    intro y hy z hz hyz
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact hyz ((hphase y hy p hp).symm.trans (hphase z hz p hq))
  refine ⟨Y.biUnion Cy,?_,?_⟩
  · intro p hp
    obtain ⟨y,hy,hpy⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hfirst,hsecond⟩ := Finset.mem_product.mp ((hCy y hy).1 hpy)
    exact Finset.mem_product.mpr
      ⟨(Finset.mem_singleton.mp hfirst).symm ▸ hy,hsecond⟩
  · have hh := Finset.sum_le_sum (fun y hy => (hCy y hy).2)
    rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at hh
    rw [Finset.sum_biUnion hdisj]
    exact hh

private theorem positive_difference_phase_subinterval_dyadic_band_reduction
    (Y : Finset ℝ) (F : ℝ → ℝ) (n N Qbase kmax : ℕ) (hNlink : N=8*n)
    {σ c J η T M R Buffer Width : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hn : 0 < n) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hy : ∀ y∈Y, y∈Icc (1:ℝ) 2)
    (hT : 0 < T) (hM : 0 < M) (hR : 0 < R)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ j ≤ 6, |iteratedDeriv (j+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hscale : T*(N:ℝ)*R^2=M^3)
    (hQbase : 768 ≤ Qbase) (hQmax : (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M)
    (hBuffer : 0 ≤ Buffer) (hWidth : 0 ≤ Width)
    (hroom : 2*(Buffer+Width)+6*(N:ℝ) ≤ M)
    (A B : ℝ → ℤ) (hA : ∀ y∈Y, ⌈M⌉ ≤ A y)
    (hab : ∀ y∈Y, A y ≤ B y) (hB : ∀ y∈Y, B y ≤ ⌊2*M⌋) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let probe := fun (p : ℝ × ℤ) (i : Fin 2) =>
      if i=0 then (n:ℝ)*p.2-2*(N:ℝ) else (n:ℝ)*p.2-11*(N:ℝ)/4
    let Q := fun k : ℕ => Qbase*2^k
    let Ctail := (6*J/σ)*(64*σ/c)^2+192*σ/c
    let Clow := (3*J/σ+c/(32*σ))*((3072*σ)/c)^2+(3072*σ)/c
    let Cerror := (768:ℝ)^2*Ctail+Clow
    let Density := fun k => 128*Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (512*σ*R^2/(c*((Q k:ℝ)/768))+1))
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
            (24576*σ)*R^2 ≤ c*(Q kmax:ℝ)*(anchor p i).den)
        | some k => k ≤ kmax ∧
            (∀ i, 768*(anchor p i).den ≤ Q k ∧
              (24576*σ)*R^2 ≤ c*(Q k:ℝ)*(anchor p i).den)) ∧
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
    positive_difference_chunk_grid_dyadic_bands Chunks Y F n N Qbase kmax hNlink
      hσ hc hJ hn hη hηmax hy hphase hT hM hR hreg hbound htests hnegative
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

                                                                                  
                                                                                          
                                         
theorem eventually_positive_difference_selected_band_phase_subinterval_physical_sieve
    {σsrc csrc Usrc σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
    ∃ Csrc η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      1 ≤ Csrc ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {θ : ℝ}, 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (n N Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ)
      (R Jsep : ℝ) {η M δ Bcut Bselect : ℝ},
    (∀ k, 0 < Kmesh k) → N=8*n →
    0 < η → η ≤ η₀ → 0 < T → 2 ≤ N →
    1 ≤ R → R ≤ M → 0 ≤ δ → δ ≤ min κ 1 →
    0 < Jsep → Jsep ≤ M →
    (∀ y∈Y, y∈Icc (1:ℝ) 2) →
    (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j ≤ 6, |iteratedDeriv (j+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (∀ y∈Y, Expdb.IsApproximateModelPhaseFunction
      (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
    T*(N:ℝ)*R^2=M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc/σsrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/(4*σsrc))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    0 < Bcut → 2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    (N:ℝ)^10 ≤ M^3*R^7 → (N:ℝ)^2 ≤ M → (N:ℝ)*R ≤ M →
    let Q := fun k : ℕ => Qbase*2^k
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let lambda := csrc*κ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*T/(2*M^2)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    let μ₀ := csrc*T/(12*σsrc*M^3)
    let U₀ := Usrc*T/(2*σsrc*M^3)
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
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Error := (Y.card:ℝ)*(M/(N:ℝ)+1)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
    let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
    let Vscale := fun k : ℕ =>
      let Uref := Usel k
      (Uref:ℝ)^((3:ℝ)/2)
    let Δtype := fun k : ℕ =>
      let Q := Q k
      let K₀ := Kmesh k
      (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let Δ := fun k : ℕ =>
      let Q := Q k
      (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let D := fun k : ℕ =>
      let Q := Q k
      (Δ k)+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let CostUpper := fun k : ℕ =>
      let Uref := Usel k
      M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := fun k : ℕ =>
      let Uref := Usel k
      R^4/((N:ℝ)^2*(Uref:ℝ))
    let Kupper := fun k : ℕ =>
      240*(CostUpper k)*
        (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := fun k : ℕ =>
      240*(CostLower k)*
        (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    let Klarge := fun k : ℕ =>
      let Q := Q k
      2*Bselect*60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
        (Cmain+Ctail)*((Q:ℝ)/(N:ℝ))^((2:ℝ)/3)
    let Buffer := fun k : ℕ =>
      let Uref := Usel k
      (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    let Width := fun k : ℕ => (14*σsrc/csrc)*(Usel k:ℝ)*(N:ℝ)
    let FamilyBound := fun k : ℕ =>
      let Q := Q k
      let K₀ := Kmesh k
      fun (P : Finset (ℝ × ℤ)) =>
        (48*σsrc/csrc)^6*(R^2/(Q:ℝ))^6*
          C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*
            ((Vscale k)*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+(Δtype k)*Jsep)+
              ((P.image Prod.fst).card:ℝ)^2*((Vscale k)*((Kupper k)+(Klower k))+(Klarge k))*T^εloss)
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    61*Ccurv*Cphys ≤ Bcut →
    (∀ k ≤ kmax,
      12*Usrc ≤ σsrc*(Usel k:ℝ) ∧
      63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      1 ≤ Usel k ∧
      Bselect^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
      (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Usel k:ℝ) ∧
      Q k ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
      768*R ≤ (Q k:ℝ) ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
      D k ≤ 1/2 ∧ Δ k < 1/2) →
    (∀ k ≤ kmax, Usel k ≤ Usel 0) →
    2*(Buffer 0+Width 0)+6*(N:ℝ) ≤ M →
    let CtailBand := (6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc
    let ClowBand := (3*Usrc/σsrc+csrc/(32*σsrc))*((3072*σsrc)/csrc)^2+(3072*σsrc)/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    let Density := fun k => 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (512*σsrc*R^2/(csrc*((Q k:ℝ)/768))+1))
    let Endpoint := (Y.card:ℝ)*(2*Buffer 0+2*Width 0+6*(N:ℝ)+2*(n:ℝ))
    ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
    (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
    ∃ (Chunks : Finset (ℝ × ℤ)) (band : (ℝ × ℤ) → Option ℕ)
      (Dcover : ℕ → Finset (ℝ × ℤ)),
      (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/(N:ℝ)) ∧
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        (Y.card:ℝ)*Density k) ∧
      ((Chunks.filter (fun p => band p=none)).card:ℝ) ≤ (Y.card:ℝ)*Density kmax ∧
      let Selected := fun k => Chunks.filter (fun p => band p=some k)
      let Grid := fun (k : ℕ) (r : ℤ) =>
        ((Dcover k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
      (∀ k ≤ kmax,
        Dcover k ⊆ Selected k ∪ (Selected k).image (fun p => (p.1,p.2-6)) ∧
        (Dcover k).card ≤ 2*(Selected k).card ∧
        (∀ r, (Grid k r).card ≤ 2*(Selected k).card) ∧
        (∀ r, (Grid k r).image Prod.fst ⊆ Y)) ∧
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),(𝐞 (f y j):ℂ)‖)^12 ≤
        2^11*(((kmax:ℝ)+2)^11*
          (((n:ℝ)*(Y.card:ℝ)*Density kmax)^12+
            (4:ℝ)^12*(8:ℝ)^11*∑ k∈Finset.range (kmax+1),
              ∑ r∈Finset.Ico (0:ℤ) 8,
                (2^11*((Csrc*Error)^12+
                  (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (Grid k r))))+
            Endpoint^12) := by

  classical
  intro κ Ratio L
  obtain ⟨Csrc,η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,hcore⟩ :=
    eventually_positive_difference_selected_eight_grid_chunk_physical_sieve
      hσsrc hcsrc hUsrc hσ hεloss hanchorBudget
  refine ⟨Csrc,η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,?_⟩
  intro θ hθ hθmax hθaction
  filter_upwards [hcore hθ hθmax hθaction] with T hcoreT
  intro Fsrc Y n N Qbase kmax Kmesh Usel R Jsep η M δ Bcut Bselect
    hK hNlink hη hηsmall hT hNtwo hR hRM hδzero hδ hJsep hJM hy hsepY
    hreg hjets htests hnegative hmodels hscale hpad hquartic hquad hregime
    hBcut hBselectSize hcutMargin hscaleTen hNsqM hNRM Q
    Cphys c J B lambda Uband ChartCap NarrowCap Cap μ₀ U₀ C₂ C₃ Ct Cc
    Ccurv Kres Esize Dbase Tbase Lunit Gamma Cthird
    AupperConst BupperConst AlowerConst BlowerConst DupperConst DlowerConst
    Cpack Cfirst Cgap Cmain Ctail Error f
    Vscale Δtype Δ D CostUpper CostLower Kupper Klower Klarge Buffer Width FamilyBound
    hsmall hNR hRN hNcube hsize hBsize hvalid hUmax hroom
    CtailBand ClowBand CerrorBand Density Endpoint A Bint hA hab hB
  have hn : 0 < n := by omega
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hM : 0 < M := by nlinarith only [hNp,hNsqM]
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hBuffer0 : 0 ≤ Buffer 0 := by dsimp only [Buffer]; positivity
  have hWidth0 : 0 ≤ Width 0 := by dsimp only [Width]; positivity
  have hQbase : 768 ≤ Qbase := by
    obtain ⟨_,_,_,_,_,_,_,_,_,hstrong,_,_,_⟩ := hvalid 0 (Nat.zero_le _)
    have hh : (768:ℝ) ≤ Q 0 := by nlinarith only [hstrong,hR]
    have hz : 768 ≤ Q 0 := by exact_mod_cast hh
    simpa only [Q,pow_zero,mul_one] using hz
  have hQmax : (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M := by
    obtain ⟨_,_,_,_,_,_,_,hQN,_,_,_,_,_⟩ := hvalid kmax le_rfl
    have hh : (Q kmax:ℝ) ≤ N := by exact_mod_cast hQN
    calc
      (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ (N:ℝ)*(N:ℝ) :=
        mul_le_mul_of_nonneg_left hh hNp.le
      _ = (N:ℝ)^2 := by ring
      _ ≤ M := hNsqM
  obtain ⟨Chunks,anchor,band,za,hphase,hdeep,hcardChunks,hroots,hbands,hcounts,htail,
      hReduction⟩ :=
    positive_difference_phase_subinterval_dyadic_band_reduction Y Fsrc n N Qbase kmax hNlink
      hσsrc hcsrc hUsrc hn hη (hηsmall.trans hηcap) hy hT hM hRp
      hreg hjets htests hnegative hscale hQbase hQmax hBuffer0 hWidth0 hroom
      A Bint hA hab hB
  let Selected := fun k => Chunks.filter (fun p => band p=some k)
  let GridOf := fun (Dp : Finset (ℝ × ℤ)) (r : ℤ) =>
    (Dp.filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
  let BandSum := fun k => ∑ p∈Selected k,
    ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),(𝐞 (f p.1 j):ℂ)‖
  let CoreSum := fun k Dp => ∑ r∈Finset.Ico (0:ℤ) 8,
    (2^11*((Csrc*Error)^12+
      (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (GridOf Dp r)))
  have hBufferMono k (hk : k ≤ kmax) : Buffer k ≤ Buffer 0 := by
    have hu : (Usel k:ℝ) ≤ Usel 0 := by exact_mod_cast hUmax k hk
    exact add_le_add (add_le_add
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hu (by norm_num)) hκ.le)
        (Nat.cast_nonneg _)) le_rfl) le_rfl
  have hWidthMono k (hk : k ≤ kmax) : Width k ≤ Width 0 := by
    have hu : (Usel k:ℝ) ≤ Usel 0 := by exact_mod_cast hUmax k hk
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ 14*σsrc/csrc)) (Nat.cast_nonneg _)
  have hchoose (k : ℕ) : ∃ Dp : Finset (ℝ × ℤ), k ≤ kmax →
      Dp ⊆ Selected k ∪ (Selected k).image (fun p => (p.1,p.2-6)) ∧
      Dp.card ≤ 2*(Selected k).card ∧
      (∀ r, (GridOf Dp r).card ≤ 2*(Selected k).card) ∧
      (∀ r, (GridOf Dp r).image Prod.fst ⊆ Y) ∧
      (BandSum k)^12 ≤ (4:ℝ)^12*(8:ℝ)^11*CoreSum k Dp := by
    by_cases hk : k ≤ kmax
    · obtain ⟨hUlarge,hsourceMesh,hmesh,hUref,hselectedWrap,hUupper,hUlower,
        hQN,hUR,hstrongRQ,hminscale,hD,hΔ⟩ := hvalid k hk
      let : NeZero (Kmesh k) := ⟨Nat.ne_of_gt (hK k)⟩
      have hSelY p (hp : p∈Selected k) : p.1∈Y := hphase p (Finset.mem_filter.mp hp).1
      have hSelDeep p (hp : p∈Selected k) :
          (n:ℝ)*p.2∈Icc (M+Buffer k+Width k+4*(N:ℝ))
            (2*M-Buffer k-Width k-(N:ℝ)) := by
        have hh := hdeep p (Finset.mem_filter.mp hp).1
        have hbuf := hBufferMono k hk
        have hwid := hWidthMono k hk
        constructor <;> linarith only [hh.1,hh.2,hbuf,hwid]
      have hSelAnchors p (hp : p∈Selected k) (i : Fin 2) :
          |za p i-(if i=0 then (n:ℝ)*p.2-2*(N:ℝ)
            else (n:ℝ)*p.2-11*(N:ℝ)/4)| ≤ (N:ℝ)/16 ∧
          iteratedDeriv 2 (f p.1) (za p i)/2=(anchor p i:ℝ) ∧
          768*(anchor p i).den ≤ Q k ∧
          (24576*σsrc)*R^2 ≤ csrc*(Q k:ℝ)*(anchor p i).den := by
        obtain ⟨hpC,hpk⟩ := Finset.mem_filter.mp hp
        have hr := hroots p hpC i
        have hb := hbands p hpC
        rw [hpk] at hb
        exact ⟨hr.2.1,hr.1,(hb.2 i).1,(hb.2 i).2⟩
      obtain ⟨Dp,hDsub,hDcard,hGcard,hGphase,hBandBound⟩ :=
        hcoreT Fsrc Y (Q k) (Kmesh k) N (Usel k) R Jsep
          (η:=η) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
          hη hηsmall hT hNtwo hR hRM hδzero hδ hJsep hJM hy hsepY
          hreg hjets htests hnegative hmodels hscale hpad hquartic hquad hUlarge
          hsourceMesh hmesh hregime hUref hBcut hBselectSize hcutMargin hselectedWrap
          hUupper hUlower hscaleTen hQN hNsqM hUR hstrongRQ hNRM
          hsmall hNR hRN hNcube hminscale hsize hD hΔ hBsize
          n hNlink (Selected k) anchor za hSelY hSelDeep hSelAnchors
      have hPhaseY r : (GridOf Dp r).image Prod.fst ⊆ Y := by
        intro y hyGrid
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp (hGphase r hyGrid)
        exact hSelY p hp
      exact ⟨Dp,fun _ => ⟨hDsub,hDcard,hGcard,hPhaseY,hBandBound⟩⟩
    · exact ⟨∅,fun hh => (hk hh).elim⟩
  choose Dcover hDcover using hchoose
  refine ⟨Chunks,band,Dcover,hcardChunks,hcounts,htail,?_⟩
  intro SelectedOut Grid
  refine ⟨fun k hk => ⟨(hDcover k hk).1,(hDcover k hk).2.1,
    (hDcover k hk).2.2.1,(hDcover k hk).2.2.2.1⟩,?_⟩
  have hsum : (∑ k∈Finset.range (kmax+1),(BandSum k)^12) ≤
      (4:ℝ)^12*(8:ℝ)^11*∑ k∈Finset.range (kmax+1),CoreSum k (Dcover k) := by
    calc
      _ ≤ ∑ k∈Finset.range (kmax+1), (4:ℝ)^12*(8:ℝ)^11*CoreSum k (Dcover k) :=
        Finset.sum_le_sum (fun k hk => (hDcover k (by
          have hh := Finset.mem_range.mp hk
          omega)).2.2.2.2)
      _ = _ := by rw [Finset.mul_sum]
  exact hReduction.trans (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum) (by positivity))
      le_rfl) (by norm_num))

                                                                               
                                                                                            
theorem eventually_positive_difference_triangular_selected_band_phase_subinterval_physical_sieve
    {σsrc csrc Usrc σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
    ∃ Csrc η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      1 ≤ Csrc ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {θ : ℝ}, 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (n N Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ)
      (R Jsep Vscale : ℝ) (isUpper : Bool) {η M δ Bcut Bselect : ℝ},
    (∀ k, 0 < Kmesh k) → N=8*n →
    0 < η → η ≤ η₀ → 0 < T → 2 ≤ N →
    1 ≤ R → R ≤ M → 1 ≤ Vscale → 0 ≤ δ → δ ≤ min κ 1 →
    0 < Jsep → Jsep ≤ M →
    (∀ y∈Y, y∈Icc (1:ℝ) 2) →
    (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j ≤ 6, |iteratedDeriv (j+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (∀ y∈Y, Expdb.IsApproximateModelPhaseFunction
      (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
    T*(N:ℝ)*R^2=M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc/σsrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/(4*σsrc))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    0 < Bcut → 2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    (N:ℝ)^10 ≤ M^3*R^7 → (N:ℝ)^2 ≤ M → (N:ℝ)*R ≤ M →
    let Q := fun k : ℕ => Qbase*2^k
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let Uband := (3*Usrc/σsrc)*T/(2*M^2)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    let μ₀ := csrc*T/(12*σsrc*M^3)
    let U₀ := Usrc*T/(2*σsrc*M^3)
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
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let Error := (Y.card:ℝ)*(M/(N:ℝ)+1)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
    let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
    let Δtype := fun k : ℕ =>
      let Q := Q k
      let K₀ := Kmesh k
      (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let Δ := fun k : ℕ =>
      let Q := Q k
      (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let D := fun k : ℕ =>
      let Q := Q k
      (Δ k)+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let CostUpper := fun k : ℕ =>
      let Uref := Usel k
      M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := fun k : ℕ =>
      let Uref := Usel k
      R^4/((N:ℝ)^2*(Uref:ℝ))
    let Kupper := fun k : ℕ =>
      240*(CostUpper k)*
        (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := fun k : ℕ =>
      240*(CostLower k)*
        (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    let Buffer := fun k : ℕ =>
      let Uref := Usel k
      (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    let Width := fun k : ℕ => (14*σsrc/csrc)*(Usel k:ℝ)*(N:ℝ)
    let FamilyBound := fun k : ℕ =>
      let Q := Q k
      let K₀ := Kmesh k
      fun (P : Finset (ℝ × ℤ)) =>
        (48*σsrc/csrc)^6*(R^2/(Q:ℝ))^6*
          C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*
            (Vscale*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+(Δtype k)*Jsep)+
              ((P.image Prod.fst).card:ℝ)^2*Vscale*(if isUpper then (Kupper k) else (Klower k))*T^εloss)
    (if isUpper then Vscale=1+R^4/(6*(N:ℝ)^2)
      else Uband ≤ 1/16 ∧ Vscale=1+R^4*Uband^2/(N:ℝ)^2) →
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    61*Ccurv*Cphys ≤ Bcut →
    (∀ k ≤ kmax,
      12*Usrc ≤ σsrc*(Usel k:ℝ) ∧
      63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      1 ≤ Usel k ∧
      Bselect^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
      (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      Q k ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
      768*R ≤ (Q k:ℝ) ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
      D k ≤ 1/2 ∧ Δ k < 1/2) →
    (∀ k ≤ kmax, Usel k ≤ Usel 0) →
    2*(Buffer 0+Width 0)+6*(N:ℝ) ≤ M →
    let CtailBand := (6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc
    let ClowBand := (3*Usrc/σsrc+csrc/(32*σsrc))*((3072*σsrc)/csrc)^2+(3072*σsrc)/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    let Density := fun k => 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (512*σsrc*R^2/(csrc*((Q k:ℝ)/768))+1))
    let Endpoint := (Y.card:ℝ)*(2*Buffer 0+2*Width 0+6*(N:ℝ)+2*(n:ℝ))
    ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
    (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
    ∃ (Chunks : Finset (ℝ × ℤ)) (band : (ℝ × ℤ) → Option ℕ)
      (Dcover : ℕ → Finset (ℝ × ℤ)),
      (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/(N:ℝ)) ∧
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        (Y.card:ℝ)*Density k) ∧
      ((Chunks.filter (fun p => band p=none)).card:ℝ) ≤ (Y.card:ℝ)*Density kmax ∧
      let Selected := fun k => Chunks.filter (fun p => band p=some k)
      let Grid := fun (k : ℕ) (r : ℤ) =>
        ((Dcover k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
      (∀ k ≤ kmax,
        Dcover k ⊆ Selected k ∪ (Selected k).image (fun p => (p.1,p.2-6)) ∧
        (Dcover k).card ≤ 2*(Selected k).card ∧
        (∀ r, (Grid k r).card ≤ 2*(Selected k).card) ∧
        (∀ r, (Grid k r).image Prod.fst ⊆ Y)) ∧
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),(𝐞 (f y j):ℂ)‖)^12 ≤
        2^11*(((kmax:ℝ)+2)^11*
          (((n:ℝ)*(Y.card:ℝ)*Density kmax)^12+
            (4:ℝ)^12*(8:ℝ)^11*∑ k∈Finset.range (kmax+1),
              ∑ r∈Finset.Ico (0:ℤ) 8,
                (2^11*((Csrc*Error)^12+
                  (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (Grid k r))))+
            Endpoint^12) := by

  classical
  intro κ Ratio L
  obtain ⟨Csrc,η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,hcore⟩ :=
    eventually_positive_difference_triangular_selected_eight_grid_chunk_physical_sieve
      hσsrc hcsrc hUsrc hσ hεloss hanchorBudget
  refine ⟨Csrc,η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,?_⟩
  intro θ hθ hθmax hθaction
  filter_upwards [hcore hθ hθmax hθaction] with T hcoreT
  intro Fsrc Y n N Qbase kmax Kmesh Usel R Jsep Vscale isUpper η M δ Bcut Bselect
    hK hNlink hη hηsmall hT hNtwo hR hRM hVscale hδzero hδ hJsep hJM hy hsepY
    hreg hjets htests hnegative hmodels hscale hpad hquartic hquad hregime
    hBcut hBselectSize hcutMargin hscaleTen hNsqM hNRM Q
    Cphys c J B Uband ChartCap NarrowCap Cap μ₀ U₀ C₂ C₃ Ct Cc
    Ccurv Kres Esize Dbase Tbase Lunit Gamma Cthird
    AupperConst BupperConst AlowerConst BlowerConst DupperConst DlowerConst
    Error f
    Δtype Δ D CostUpper CostLower Kupper Klower Buffer Width FamilyBound
    hchoice hsmall hNR hRN hNcube hsize hBsize hvalid hUmax hroom
    CtailBand ClowBand CerrorBand Density Endpoint A Bint hA hab hB
  have hn : 0 < n := by omega
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hM : 0 < M := by nlinarith only [hNp,hNsqM]
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hBuffer0 : 0 ≤ Buffer 0 := by dsimp only [Buffer]; positivity
  have hWidth0 : 0 ≤ Width 0 := by dsimp only [Width]; positivity
  have hQbase : 768 ≤ Qbase := by
    obtain ⟨_,_,_,_,_,_,_,_,hstrong,_,_,_⟩ := hvalid 0 (Nat.zero_le _)
    have hh : (768:ℝ) ≤ Q 0 := by nlinarith only [hstrong,hR]
    have hz : 768 ≤ Q 0 := by exact_mod_cast hh
    simpa only [Q,pow_zero,mul_one] using hz
  have hQmax : (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M := by
    obtain ⟨_,_,_,_,_,_,hQN,_,_,_,_,_⟩ := hvalid kmax le_rfl
    have hh : (Q kmax:ℝ) ≤ N := by exact_mod_cast hQN
    calc
      (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ (N:ℝ)*(N:ℝ) :=
        mul_le_mul_of_nonneg_left hh hNp.le
      _ = (N:ℝ)^2 := by ring
      _ ≤ M := hNsqM
  obtain ⟨Chunks,anchor,band,za,hphase,hdeep,hcardChunks,hroots,hbands,hcounts,htail,
      hReduction⟩ :=
    positive_difference_phase_subinterval_dyadic_band_reduction Y Fsrc n N Qbase kmax hNlink
      hσsrc hcsrc hUsrc hn hη (hηsmall.trans hηcap) hy hT hM hRp
      hreg hjets htests hnegative hscale hQbase hQmax hBuffer0 hWidth0 hroom
      A Bint hA hab hB
  let Selected := fun k => Chunks.filter (fun p => band p=some k)
  let GridOf := fun (Dp : Finset (ℝ × ℤ)) (r : ℤ) =>
    (Dp.filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
  let BandSum := fun k => ∑ p∈Selected k,
    ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),(𝐞 (f p.1 j):ℂ)‖
  let CoreSum := fun k Dp => ∑ r∈Finset.Ico (0:ℤ) 8,
    (2^11*((Csrc*Error)^12+
      (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (GridOf Dp r)))
  have hBufferMono k (hk : k ≤ kmax) : Buffer k ≤ Buffer 0 := by
    have hu : (Usel k:ℝ) ≤ Usel 0 := by exact_mod_cast hUmax k hk
    exact add_le_add (add_le_add
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hu (by norm_num)) hκ.le)
        (Nat.cast_nonneg _)) le_rfl) le_rfl
  have hWidthMono k (hk : k ≤ kmax) : Width k ≤ Width 0 := by
    have hu : (Usel k:ℝ) ≤ Usel 0 := by exact_mod_cast hUmax k hk
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ 14*σsrc/csrc)) (Nat.cast_nonneg _)
  have hchoose (k : ℕ) : ∃ Dp : Finset (ℝ × ℤ), k ≤ kmax →
      Dp ⊆ Selected k ∪ (Selected k).image (fun p => (p.1,p.2-6)) ∧
      Dp.card ≤ 2*(Selected k).card ∧
      (∀ r, (GridOf Dp r).card ≤ 2*(Selected k).card) ∧
      (∀ r, (GridOf Dp r).image Prod.fst ⊆ Y) ∧
      (BandSum k)^12 ≤ (4:ℝ)^12*(8:ℝ)^11*CoreSum k Dp := by
    by_cases hk : k ≤ kmax
    · obtain ⟨hUlarge,hsourceMesh,hmesh,hUref,hselectedWrap,hUupper,
        hQN,hUR,hstrongRQ,hminscale,hD,hΔ⟩ := hvalid k hk
      let : NeZero (Kmesh k) := ⟨Nat.ne_of_gt (hK k)⟩
      have hSelY p (hp : p∈Selected k) : p.1∈Y := hphase p (Finset.mem_filter.mp hp).1
      have hSelDeep p (hp : p∈Selected k) :
          (n:ℝ)*p.2∈Icc (M+Buffer k+Width k+4*(N:ℝ))
            (2*M-Buffer k-Width k-(N:ℝ)) := by
        have hh := hdeep p (Finset.mem_filter.mp hp).1
        have hbuf := hBufferMono k hk
        have hwid := hWidthMono k hk
        constructor <;> linarith only [hh.1,hh.2,hbuf,hwid]
      have hSelAnchors p (hp : p∈Selected k) (i : Fin 2) :
          |za p i-(if i=0 then (n:ℝ)*p.2-2*(N:ℝ)
            else (n:ℝ)*p.2-11*(N:ℝ)/4)| ≤ (N:ℝ)/16 ∧
          iteratedDeriv 2 (f p.1) (za p i)/2=(anchor p i:ℝ) ∧
          768*(anchor p i).den ≤ Q k ∧
          (24576*σsrc)*R^2 ≤ csrc*(Q k:ℝ)*(anchor p i).den := by
        obtain ⟨hpC,hpk⟩ := Finset.mem_filter.mp hp
        have hr := hroots p hpC i
        have hb := hbands p hpC
        rw [hpk] at hb
        exact ⟨hr.2.1,hr.1,(hb.2 i).1,(hb.2 i).2⟩
      obtain ⟨Dp,hDsub,hDcard,hGcard,hGphase,hBandBound⟩ :=
        hcoreT Fsrc Y (Q k) (Kmesh k) N (Usel k) R Jsep Vscale
          (η:=η) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
          hη hηsmall hT hNtwo hR hRM hVscale hδzero hδ hJsep hJM hy hsepY
          hreg hjets htests hnegative hmodels hscale hpad hquartic hquad hUlarge
          hsourceMesh hmesh hregime hUref hBcut hBselectSize hcutMargin hselectedWrap
          hUupper hscaleTen hQN hNsqM hUR hstrongRQ hNRM
          hsmall hNR hRN hNcube hminscale hsize hD hΔ hBsize isUpper hchoice
          n hNlink (Selected k) anchor za hSelY hSelDeep hSelAnchors
      have hPhaseY r : (GridOf Dp r).image Prod.fst ⊆ Y := by
        intro y hyGrid
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp (hGphase r hyGrid)
        exact hSelY p hp
      exact ⟨Dp,fun _ => ⟨hDsub,hDcard,hGcard,hPhaseY,hBandBound⟩⟩
    · exact ⟨∅,fun hh => (hk hh).elim⟩
  choose Dcover hDcover using hchoose
  refine ⟨Chunks,band,Dcover,hcardChunks,hcounts,htail,?_⟩
  intro SelectedOut Grid
  refine ⟨fun k hk => ⟨(hDcover k hk).1,(hDcover k hk).2.1,
    (hDcover k hk).2.2.1,(hDcover k hk).2.2.2.1⟩,?_⟩
  have hsum : (∑ k∈Finset.range (kmax+1),(BandSum k)^12) ≤
      (4:ℝ)^12*(8:ℝ)^11*∑ k∈Finset.range (kmax+1),CoreSum k (Dcover k) := by
    calc
      _ ≤ ∑ k∈Finset.range (kmax+1), (4:ℝ)^12*(8:ℝ)^11*CoreSum k (Dcover k) :=
        Finset.sum_le_sum (fun k hk => (hDcover k (by
          have hh := Finset.mem_range.mp hk
          omega)).2.2.2.2)
      _ = _ := by rw [Finset.mul_sum]
  exact hReduction.trans (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum) (by positivity))
      le_rfl) (by norm_num))

                                                                                      
                                                      
private theorem reference_floor_physical_budgets
    {N R Q B L : ℝ} (hR : 1 ≤ R) (hRQ : R ≤ Q) (hQN : Q ≤ N)
    (hNR : N ≤ R^2) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hlarge : 2*B*L ≤ (N/Q)^((2:ℝ)/3)) :
    let U : ℕ := ⌊(N/Q)^((2:ℝ)/3)/B⌋₊
    1 ≤ U ∧ L ≤ (U:ℝ) ∧
      (N/Q)^((2:ℝ)/3)/(2*B) ≤ (U:ℝ) ∧
      (U:ℝ) ≤ (N/Q)^((2:ℝ)/3)/B ∧
      B^2*(U:ℝ)^3*R^2 ≤ N^2 ∧
      (U:ℝ) ≤ R^2 := by
  intro U
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hQ : 0 < Q := hRp.trans_le hRQ
  have hN : 0 < N := hQ.trans_le hQN
  have hBp : 0 < B := zero_lt_one.trans_le hB
  let scale := (N/Q)^((2:ℝ)/3)/B
  have hX2L : 2*L ≤ scale := (le_div_iff₀ hBp).mpr (by nlinarith only [hlarge])
  have hX2 : 2 ≤ scale := by linarith only [hX2L,hL]
  have hU : 1 ≤ U := (Nat.one_le_floor_iff scale).mpr (by linarith only [hX2])
  have hUle : (U:ℝ) ≤ scale := Nat.floor_le (by linarith only [hX2])
  have hUlower : scale/2 ≤ (U:ℝ) := by
    have hh := Nat.lt_floor_add_one scale
    change scale < (U:ℝ)+1 at hh
    linarith only [hh,hX2]
  have hUL : L ≤ (U:ℝ) := by linarith only [hX2L,hUlower]
  have hpow : ((N/Q)^((2:ℝ)/3))^3=(N/Q)^2 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (div_pos hN hQ).le]
    norm_num
  have hcube : B^3*(U:ℝ)^3*Q^2 ≤ N^2 := by
    have hh := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg U) hUle 3)
      (show 0 ≤ B^3*Q^2 by positivity)
    have he : (B^3*Q^2)*scale^3=N^2 := by
      dsimp only [scale]
      rw [div_pow,hpow,div_pow]
      field_simp
    rw [he] at hh
    nlinarith only [hh]
  have hlinear : B*(U:ℝ)*Q ≤ N := by
    have hratio : 1 ≤ N/Q := (one_le_div hQ).mpr hQN
    have hp := Real.rpow_le_self_of_one_le hratio (by norm_num : (2:ℝ)/3 ≤ 1)
    have hh := mul_le_mul_of_nonneg_left hUle hBp.le
    have he : B*scale=(N/Q)^((2:ℝ)/3) := by dsimp only [scale]; field_simp
    rw [he] at hh
    exact (le_div_iff₀ hQ).mp (hh.trans hp)
  have hnowrap : B^2*(U:ℝ)^3*R^2 ≤ N^2 := by
    have hBpow : B^2 ≤ B^3 := by
      have hh := mul_le_mul_of_nonneg_left hB (sq_nonneg B)
      nlinarith only [hh]
    calc
      _ ≤ B^3*(U:ℝ)^3*Q^2 := by gcongr
      _ ≤ _ := hcube
  have hUN : (U:ℝ) ≤ N := by
    calc
      (U:ℝ) = 1*(U:ℝ)*1 := by ring
      _ ≤ B*(U:ℝ)*Q := by gcongr; exact hR.trans hRQ
      _ ≤ N := hlinear
  refine ⟨hU,hUL,?_,hUle,hnowrap,hUN.trans hNR⟩
  convert hUlower using 1
  dsimp only [scale]
  ring

public  theorem dyadic_band_integer_physical_selection
    (N : ℕ) {σ J R B L Cbase qcap Dcap : ℝ}
    (hσ : 0 < σ) (hR : 1 ≤ R) (hRN : R ≤ N) (hNR : (N:ℝ) ≤ R^2)
    (hB : 1 ≤ B) (hL : 1 ≤ L) (hCbase : 768 ≤ Cbase)
    (hcap : 0 < qcap) (hcapOne : qcap ≤ 1)
    (hlarge : qcap*(2*B*L)^((3:ℝ)/2) ≤ 1)
    (hDcap : 0 ≤ Dcap) (hsmall : 4*Dcap*qcap ≤ 1)
    (hroom : 2*Cbase*R ≤ qcap*(N:ℝ)) :
    ∃ (Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ),
      let Q := fun k : ℕ => Qbase*2^k
      Cbase*R ≤ Qbase ∧ (Qbase:ℝ) ≤ 2*Cbase*R ∧
      qcap*(N:ℝ)/2 ≤ Q kmax ∧ (Q kmax:ℝ) ≤ qcap*(N:ℝ) ∧
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
  classical
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hNp : (0:ℝ) < N := hRp.trans_le hRN
  have hCp : 0 < Cbase := by linarith only [hCbase]
  have hCR : 1 ≤ Cbase*R := by nlinarith only [hCbase,hR]
  let Qbase : ℕ := ⌈Cbase*R⌉₊
  have hQlo : Cbase*R ≤ (Qbase:ℝ) := Nat.le_ceil _
  have hQhi : (Qbase:ℝ) ≤ 2*Cbase*R := by
    have hh := Nat.ceil_lt_add_one (mul_pos hCp hRp).le
    change (Qbase:ℝ) < Cbase*R+1 at hh
    linarith only [hh,hCR]
  have hQp : (0:ℝ) < Qbase := (mul_pos hCp hRp).trans_le hQlo
  have hratio : 1 ≤ qcap*(N:ℝ)/(Qbase:ℝ) :=
    (le_div_iff₀ hQp).mpr (by simpa only [one_mul] using hQhi.trans hroom)
  obtain ⟨kmax,hklo,hkhi⟩ := exists_nat_pow_near hratio (by norm_num : (1:ℝ) < 2)
  let Q := fun k : ℕ => Qbase*2^k
  have hQcast k : (Q k:ℝ)=(Qbase:ℝ)*(2:ℝ)^k := by simp only [Q,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  have hQbase k : (Qbase:ℝ) ≤ Q k := by
    rw [hQcast]
    exact le_mul_of_one_le_right hQp.le (one_le_pow₀ (by norm_num))
  have hQpos k : (0:ℝ) < Q k := hQp.trans_le (hQbase k)
  have hQupper : (Q kmax:ℝ) ≤ qcap*(N:ℝ) := by
    rw [hQcast]
    have hh := (le_div_iff₀ hQp).mp hklo
    simpa only [mul_comm] using hh
  have hQlower : qcap*(N:ℝ)/2 ≤ Q kmax := by
    have hh := (div_lt_iff₀ hQp).mp hkhi
    rw [pow_succ] at hh
    rw [hQcast]
    nlinarith only [hh]
  have hQmono k (hk : k ≤ kmax) : Q k ≤ Q kmax := by
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hk)
  have hQN k (hk : k ≤ kmax) : Q k ≤ N := by
    have hh : (Q k:ℝ) ≤ N :=
      (by exact_mod_cast hQmono k hk : (Q k:ℝ) ≤ Q kmax).trans (hQupper.trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hcapOne hNp.le))
    exact_mod_cast hh
  have hstrong k : 768*R ≤ (Q k:ℝ) :=
    (mul_le_mul_of_nonneg_right hCbase hRp.le).trans (hQlo.trans (hQbase k))
  have hRQ k : R ≤ (Q k:ℝ) := by
    have hh := hstrong k
    linarith only [hh,hRp]
  have hminscale k : 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) := by
    have hh := mul_le_mul (hstrong k) hRN hRp.le (hQpos k).le
    nlinarith only [hh,sq_nonneg R]
  have hmesh k := exists_positive_difference_source_fourier_mesh
    (J:=J) hσ hNp hRp (hQpos k) (by
      have hh := hminscale k
      linarith only [hh,sq_nonneg R])
  choose Kmesh hK hSource hMesh hMeshUpper using hmesh
  let Usel := fun k => ⌊((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/B⌋₊
  have hUdata k (hk : k ≤ kmax) :=
    reference_floor_physical_budgets (N:=(N:ℝ)) (B:=B) (L:=L)
      hR (hRQ k) (by exact_mod_cast hQN k hk) hNR hB hL (by
        have hqcap : (Q k:ℝ) ≤ qcap*(N:ℝ) :=
          (by exact_mod_cast hQmono k hk : (Q k:ℝ) ≤ Q kmax).trans hQupper
        have hratioLower : 1/qcap ≤ (N:ℝ)/(Q k:ℝ) := by
          apply (div_le_div_iff₀ hcap (hQpos k)).mpr
          nlinarith only [hqcap]
        have hpowle : (2*B*L)^((3:ℝ)/2) ≤ (N:ℝ)/(Q k:ℝ) :=
          ((le_div_iff₀ hcap).mpr (by nlinarith only [hlarge])).trans hratioLower
        have hh := (Real.le_rpow_inv_iff_of_pos
          (by positivity : (0:ℝ) ≤ 2*B*L)
          (div_pos hNp (hQpos k)).le (by norm_num : (0:ℝ) < 3/2)).mpr hpowle
        norm_num only [show ((3:ℝ)/2)⁻¹=2/3 by norm_num] at hh
        exact hh)
  have hUmono k : Usel k ≤ Usel 0 := by
    apply Nat.floor_mono
    apply div_le_div_of_nonneg_right _ (zero_le_one.trans hB)
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    apply div_le_div_of_nonneg_left hNp.le (hQpos 0)
    simpa only [Q,pow_zero,mul_one] using hQbase k
  have hklog : (kmax:ℝ) ≤ Real.log N/Real.log 2 := by
    have hQone : (1:ℝ) ≤ Qbase := hCR.trans hQlo
    have hpowN : (2:ℝ)^kmax ≤ N := by
      have hh : (2:ℝ)^kmax ≤ (Q kmax:ℝ) := by
        rw [hQcast]
        exact le_mul_of_one_le_left (by positivity) hQone
      exact hh.trans (by exact_mod_cast hQN kmax le_rfl)
    have hh := Real.log_le_log (by positivity : (0:ℝ) < (2:ℝ)^kmax) hpowN
    rw [Real.log_pow] at hh
    exact (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mpr hh
  refine ⟨Qbase,kmax,Kmesh,Usel,hQlo,hQhi,hQlower,hQupper,hklog,hK,?_,hUmono⟩
  intro k hk
  obtain ⟨hU,hUL,hUlower,hUupper,hwrap,hUR⟩ := hUdata k hk
  refine ⟨hUL,hSource k,hMesh k,hMeshUpper k,hU,hwrap,hUupper,hUlower,
    hQN k hk,hUR,hstrong k,hminscale k,?_⟩
  have hqcap : (Q k:ℝ) ≤ qcap*(N:ℝ) :=
    (by exact_mod_cast hQmono k hk : (Q k:ℝ) ≤ Q kmax).trans hQupper
  apply (div_le_iff₀ hNp).mpr
  have hh := mul_le_mul_of_nonneg_left hqcap hDcap
  have hs := mul_le_mul_of_nonneg_right hsmall hNp.le
  nlinarith only [hh,hs]

public  theorem exists_uniform_dyadic_band_integer_scales
    {σ J B D₀ D₁ : ℝ} (hσ : 0 < σ)
    (hB : 1 ≤ B) (hD₀ : 0 ≤ D₀) (hD₁ : 0 ≤ D₁) :
    ∃ Csep : ℝ, 1 ≤ Csep ∧
      ∀ (N : ℕ) (R : ℝ), 1 ≤ R → (N:ℝ) ≤ R^2 → Csep*R ≤ N →
      ∃ (Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ),
        let Q := fun k : ℕ => Qbase*2^k
        (768:ℝ)*R ≤ Qbase ∧ (Qbase:ℝ) ≤ 1536*R ∧
        (N:ℝ)/Csep ≤ Q kmax ∧ (Q kmax:ℝ) ≤ N ∧
        (kmax:ℝ) ≤ Real.log N/Real.log 2 ∧
        (∀ k, 0 < Kmesh k) ∧
        (∀ k ≤ kmax,
          12*J ≤ σ*(Usel k:ℝ) ∧
          63*(J/(2*σ*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
          (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
          (Kmesh k:ℝ) ≤ 2*(max 1 (63*J/(2*σ)))*(Q k:ℝ)*(N:ℝ)/R^2 ∧
          1 ≤ Usel k ∧
          B^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
          (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/B ∧
          ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*B) ≤ (Usel k:ℝ) ∧
          Q k ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
          768*R ≤ (Q k:ℝ) ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
          D₀*(Q k:ℝ)/(N:ℝ)+D₁*(2*(Q k:ℝ))/(N:ℝ) ≤ 1/2 ∧
          D₀*(Q k:ℝ)/(N:ℝ) < 1/2) ∧
        (∀ k, Usel k ≤ Usel 0) := by
  let L := max 1 (12*J/σ)
  let Dcap := D₀+2*D₁
  let qcap := 1/(4*Dcap+(2*B*L)^((3:ℝ)/2)+1)
  let Csep := 1536/qcap
  have hL : 1 ≤ L := le_max_left _ _
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hDc : 0 ≤ Dcap := by dsimp only [Dcap]; positivity
  have hpow : 0 < (2*B*L)^((3:ℝ)/2) := by positivity
  have hden : 0 < 4*Dcap+(2*B*L)^((3:ℝ)/2)+1 := by positivity
  have hcap : 0 < qcap := by dsimp only [qcap]; positivity
  have hcapOne : qcap ≤ 1 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hDc,hpow]
  have hlarge : qcap*(2*B*L)^((3:ℝ)/2) ≤ 1 := by
    dsimp only [qcap]
    rw [one_div,mul_comm,←div_eq_mul_inv]
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hDc]
  have hsmall : 4*Dcap*qcap ≤ 1 := by
    dsimp only [qcap]
    rw [one_div,←div_eq_mul_inv]
    apply (div_le_iff₀ hden).mpr
    linarith only [hpow]
  have hCsep : 1 ≤ Csep := by
    apply (le_div_iff₀ hcap).mpr
    linarith only [hcapOne]
  refine ⟨Csep,hCsep,?_⟩
  intro N R hR hNR hroom
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hRN : R ≤ N :=
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hCsep hRp.le : R ≤ Csep*R).trans hroom
  have hNp : (0:ℝ) < N := hRp.trans_le hRN
  have hroom' : 2*(768:ℝ)*R ≤ qcap*(N:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hroom hcap.le
    have he : qcap*(Csep*R)=1536*R := by dsimp only [Csep]; field_simp
    rw [he] at hh
    nlinarith only [hh]
  obtain ⟨Qbase,kmax,Kmesh,Usel,hQlo,hQhi,hQlast,hQlastHi,hlog,hK,hvalid,hmono⟩ :=
    dyadic_band_integer_physical_selection N (J:=J) hσ hR hRN hNR hB hL
      (by norm_num : (768:ℝ) ≤ 768) hcap hcapOne hlarge hDc hsmall hroom'
  refine ⟨Qbase,kmax,Kmesh,Usel,hQlo,by simpa only [show (2:ℝ)*768=1536 by norm_num] using hQhi,
    ?_,?_,hlog,hK,?_,hmono⟩
  · have hh : (N:ℝ)/Csep ≤ qcap*(N:ℝ)/2 := by
      have he : (N:ℝ)/Csep=qcap*(N:ℝ)/1536 := by
        dsimp only [Csep]
        field_simp
      rw [he]
      exact div_le_div_of_nonneg_left (mul_pos hcap hNp).le
        (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≤ 1536)
    exact hh.trans hQlast
  · exact hQlastHi.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hcapOne hNp.le)
  · intro k hk
    obtain ⟨hUL,hSource,hMesh,hMeshUpper,hU,hwrap,hUupper,hUlower,hQN,hUR,hStrong,hMin,hD⟩ :=
      hvalid k hk
    have hULarge : 12*J ≤ σ*(Usel k:ℝ) := by
      have hh := (le_max_right (1:ℝ) (12*J/σ)).trans hUL
      have hh' := (div_le_iff₀ hσ).mp hh
      simpa only [mul_comm] using hh'
    have hDsum : D₀*(Qbase*2^k:ℕ)/(N:ℝ)+
        D₁*(2*(Qbase*2^k:ℕ))/(N:ℝ) ≤ 1/4 := by
      convert hD using 1
      dsimp only [Dcap]
      ring
    have hDlow : 0 ≤ D₁*(2*(Qbase*2^k:ℕ))/(N:ℝ) := by positivity
    refine ⟨hULarge,hSource,hMesh,hMeshUpper,hU,hwrap,hUupper,hUlower,
      hQN,hUR,hStrong,hMin,?_,?_⟩ <;> linarith only [hDsum,hDlow]

private theorem selected_band_prefactor_identity
    {R Q N M Cmesh Ccard Y : ℝ}
    (hR : R ≠ 0) (hQ : Q ≠ 0) (hN : N ≠ 0) :
    (R^2/Q)^6*(Cmesh*Q*N/R^2)^12*(Ccard*Y*M*R^2/(N*Q^2))^10 =
      Cmesh^12*Ccard^10*Y^10*M^10*N^2*R^8/Q^14 := by
  field_simp

private theorem physical_mesh_type_spacing_bound
    {α Cmesh N R Q K : ℝ}
    (hα : 0 ≤ α) (hC : 0 ≤ Cmesh) (hN : 0 < N)
    (hR : 0 < R) (hQ : 0 < Q) (hK : 0 < K)
    (hmesh : Q*N ≤ K*R^2)
    (hupper : K ≤ Cmesh*Q*N/R^2) :
    Real.sqrt ((α/(N*R^2))*Q^3)*Real.sqrt K/K^2 ≤
      Real.sqrt (α*Cmesh)*R^2/N^2 := by
  have hprod : (α/(N*R^2))*Q^3*K ≤ α*Cmesh*(Q^2/R^2)^2 := by
    calc
      _ ≤ (α/(N*R^2))*Q^3*(Cmesh*Q*N/R^2) :=
        mul_le_mul_of_nonneg_left hupper (by positivity)
      _ = _ := by field_simp
  have hroot :
      Real.sqrt ((α/(N*R^2))*Q^3)*Real.sqrt K ≤
        Real.sqrt (α*Cmesh)*(Q^2/R^2) := by
    rw [←Real.sqrt_mul (by positivity : 0 ≤ (α/(N*R^2))*Q^3)]
    calc
      _ ≤ Real.sqrt (α*Cmesh*(Q^2/R^2)^2) := Real.sqrt_le_sqrt hprod
      _ = _ := by
        rw [Real.sqrt_mul (mul_nonneg hα hC),
          Real.sqrt_sq (by positivity : 0 ≤ Q^2/R^2)]
  have hsq := pow_le_pow_left₀ (mul_pos hQ hN).le hmesh 2
  have hquot : Q^2/R^2/K^2 ≤ R^2/N^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hK) (sq_pos_of_pos hN)).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (sq_pos_of_pos hR)).mpr
    convert hsq using 1 <;> ring
  calc
    _ ≤ (Real.sqrt (α*Cmesh)*(Q^2/R^2))/K^2 :=
      div_le_div_of_nonneg_right hroot (sq_nonneg K)
    _ = Real.sqrt (α*Cmesh)*(Q^2/R^2/K^2) := by ring
    _ ≤ Real.sqrt (α*Cmesh)*(R^2/N^2) :=
      mul_le_mul_of_nonneg_left hquot (Real.sqrt_nonneg _)
    _ = _ := by ring

public  theorem physical_band_logarithmic_bounds
    {Carg Cmesh T N R Q K kmax : ℝ}
    (hCarg : 0 ≤ Carg) (hCmesh : 1 ≤ Cmesh)
    (hT : 1 ≤ T) (hR : 1 ≤ R) (hRQ : R ≤ Q)
    (hQN : Q ≤ N) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hK : 0 < K) (hKupper : K ≤ Cmesh*Q*N/R^2)
    (hkmax : kmax ≤ Real.log N/Real.log 2) :
    2+Real.log (Carg*R^2/Q+1) ≤ (3+Real.log (Carg+1))*(1+Real.log T) ∧
    1+Real.log K ≤ (3+Real.log (Cmesh+1))*(1+Real.log T) ∧
    kmax+2 ≤ (2+1/Real.log 2)*(1+Real.log T) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hQ : 0 < Q := hRp.trans_le hRQ
  have hN : 0 < N := hQ.trans_le hQN
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hlinear (C z : ℝ) (hC : 0 ≤ C) (hz : 0 ≤ z) (hzT : z ≤ C*T) :
      2+Real.log (z+1) ≤ (3+Real.log (C+1))*(1+Real.log T) := by
    have hCp : 0 < C+1 := by linarith only [hC]
    have hbound : z+1 ≤ (C+1)*T := by nlinarith only [hzT,hT]
    have hh := Real.log_le_log (by linarith only [hz] : 0 < z+1) hbound
    rw [Real.log_mul hCp.ne' hTp.ne'] at hh
    have hlogC : 0 ≤ Real.log (C+1) := Real.log_nonneg (by linarith only [hC])
    nlinarith only [hh,hlogC,hlogT,mul_nonneg hlogC hlogT]
  have hRT : R ≤ T := hRQ.trans (hQN.trans hNT)
  have hRquot : R^2/Q ≤ R := (div_le_iff₀ hQ).mpr (by
    nlinarith only [mul_le_mul_of_nonneg_left hRQ hRp.le])
  have harg : Carg*R^2/Q ≤ Carg*T := by
    calc
      _ = Carg*(R^2/Q) := by ring
      _ ≤ Carg*T := mul_le_mul_of_nonneg_left (hRquot.trans hRT) hCarg
  have hKT : K ≤ Cmesh*T := by
    calc
      _ ≤ Cmesh*Q*N/R^2 := hKupper
      _ ≤ Cmesh*Q := (div_le_iff₀ (sq_pos_of_pos hRp)).mpr
        (mul_le_mul_of_nonneg_left hNR (by positivity))
      _ ≤ Cmesh*T := mul_le_mul_of_nonneg_left (hQN.trans hNT) (by positivity)
  refine ⟨hlinear Carg _ hCarg (by positivity) harg,?_,?_⟩
  · have hh := hlinear Cmesh K (by positivity) hK.le hKT
    have hlogK := Real.log_le_log hK (by linarith : K ≤ K+1)
    linarith only [hh,hlogK]
  · have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogN := Real.log_le_log hN hNT
    have hq := div_le_div_of_nonneg_right hlogN hlog2.le
    have hh := hkmax.trans hq
    have he : (2+1/Real.log 2)*(1+Real.log T) =
        2+Real.log T/Real.log 2+2*Real.log T+1/Real.log 2 := by ring
    rw [he]
    nlinarith only [hh,hlogT,one_div_pos.mpr hlog2]

public  theorem positive_difference_source_type_spacing_bound
    {σ c J T M N R Q K Cmesh : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 ≤ J)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N)
    (hR : 0 < R) (hQ : 0 < Q) (hK : 0 < K) (hC : 0 ≤ Cmesh)
    (hscale : T*N*R^2=M^3)
    (hmesh : Q*N ≤ K*R^2) (hupper : K ≤ Cmesh*Q*N/R^2) :
    let μ₀ := c*T/(12*σ*M^3)
    let U₀ := J*T/(2*σ*M^3)
    (16*U₀/μ₀)*Real.sqrt (U₀*Q^3)*Real.sqrt K/(6*K^2) ≤
      (16*J/c)*Real.sqrt ((J/(2*σ))*Cmesh)*R^2/N^2 := by
  intro μ₀ U₀
  have hU : U₀=(J/(2*σ))/(N*R^2) := by
    dsimp only [U₀]
    rw [←hscale]
    field_simp
  have hratio : 16*U₀/μ₀=96*J/c := by
    dsimp only [U₀,μ₀]
    field_simp
    ring
  have hh := physical_mesh_type_spacing_bound
    (show 0 ≤ J/(2*σ) by positivity) hC hN hR hQ hK hmesh hupper
  calc
    _ = (16*J/c)*(Real.sqrt (((J/(2*σ))/(N*R^2))*Q^3)*Real.sqrt K/K^2) := by
      rw [hratio,hU]
      ring
    _ ≤ (16*J/c)*(Real.sqrt ((J/(2*σ))*Cmesh)*R^2/N^2) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

public  theorem physical_denominator_rpow_decay
    {R Q N s : ℝ} (p : ℕ)
    (hR : 0 < R) (hRQ : R ≤ Q) (hN : 0 < N) (hs : s ≤ p) :
    (Q/N)^s/Q^p ≤ (R/N)^s/R^p := by
  have hQ : 0 < Q := hR.trans_le hRQ
  have hh := Real.rpow_le_rpow_of_nonpos hR hRQ (sub_nonpos.mpr hs)
  rw [Real.rpow_sub_natCast hQ.ne',Real.rpow_sub_natCast hR.ne'] at hh
  calc
    _ = (Q^s/Q^p)/N^s := by
      rw [Real.div_rpow hQ.le hN.le]
      ring
    _ ≤ (R^s/R^p)/N^s :=
      div_le_div_of_nonneg_right hh (Real.rpow_nonneg hN.le _)
    _ = _ := by
      rw [Real.div_rpow hR.le hN.le]
      ring

public  theorem physical_reference_reciprocal_bound
    {N Q B U : ℝ} (hN : 0 < N) (hQ : 0 < Q) (hB : 0 < B)
    (hU : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    0 < U ∧ 1/U ≤ 2*B*(Q/N)^((2:ℝ)/3) := by
  have hlow : 0 < (N/Q)^((2:ℝ)/3)/(2*B) := by positivity
  refine ⟨hlow.trans_le hU,?_⟩
  calc
    _ ≤ 1/((N/Q)^((2:ℝ)/3)/(2*B)) :=
      one_div_le_one_div_of_le hlow hU
    _ = _ := by
      rw [Real.div_rpow hN.le hQ.le,Real.div_rpow hQ.le hN.le]
      field_simp

private theorem upper_physical_family_monomial_bound
    {Y M N R Q U V Jsep D Cdelta Cupper Cv B delta : ℝ}
    (hY : 0 ≤ Y) (hM : 0 ≤ M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q)
    (hJ : 0 ≤ Jsep) (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta)
    (hCu : 0 ≤ Cupper) (hCv : 0 ≤ Cv) (hB : 0 < B) (hd : 0 ≤ delta)
    (hVupper : V ≤ Cv*R^4/N^2) (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    (Y^10*M^10*N^2*R^8/Q^14)*
        (V*D*Y*(M/N)*(1+delta*Jsep)+Y^2*V*(Cupper*M^2/(N^4*U))) ≤
      Cv*(D*(Y^11*M^11/(N*R^2))+
        D*Cdelta*(Y^11*Jsep*M^11/N^3)+
        2*B*Cupper*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))) := by
  have hQ : 0 < Q := hR.trans_le hRQ
  obtain ⟨hU,hUinv⟩ := physical_reference_reciprocal_bound hN hQ hB hUlower
  have hcost : Cupper*M^2/(N^4*U) ≤
      (Cupper*M^2/N^4)*(2*B*(Q/N)^((2:ℝ)/3)) := by
    calc
      _ = (Cupper*M^2/N^4)*(1/U) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hUinv (by positivity)
  have hQpow := pow_le_pow_left₀ hR.le hRQ 14
  have hI0 : R^12/Q^14 ≤ 1/R^2 := by
    calc
      _ ≤ R^12/R^14 := div_le_div_of_nonneg_left (by positivity) (by positivity) hQpow
      _ = _ := by field_simp
  have hI1 : R^14/Q^14 ≤ 1 := (div_le_one (by positivity)).mpr hQpow
  have hII : R^12*(Q/N)^((2:ℝ)/3)/Q^14 ≤ (R/N)^((2:ℝ)/3)/R^2 := by
    calc
      _ = R^12*((Q/N)^((2:ℝ)/3)/Q^14) := by ring
      _ ≤ R^12*((R/N)^((2:ℝ)/3)/R^14) :=
        mul_le_mul_of_nonneg_left
          (physical_denominator_rpow_decay 14 hR hRQ hN (by norm_num)) (by positivity)
      _ = _ := by field_simp
  let A₀ := Cv*D*Y^11*M^11/N
  let A₁ := Cv*D*Cdelta*Y^11*Jsep*M^11/N^3
  let A₂ := Cv*2*B*Cupper*Y^12*M^12/N^4
  have hA₀ : 0 ≤ A₀ := by dsimp only [A₀]; positivity
  have hA₁ : 0 ≤ A₁ := by dsimp only [A₁]; positivity
  have hA₂ : 0 ≤ A₂ := by dsimp only [A₂]; positivity
  calc
    _ ≤ (Y^10*M^10*N^2*R^8/Q^14)*
        ((Cv*R^4/N^2)*D*Y*(M/N)*(1+(Cdelta*R^2/N^2)*Jsep)+
          Y^2*(Cv*R^4/N^2)*((Cupper*M^2/N^4)*(2*B*(Q/N)^((2:ℝ)/3)))) := by
      gcongr
    _ = A₀*(R^12/Q^14)+A₁*(R^14/Q^14)+A₂*(R^12*(Q/N)^((2:ℝ)/3)/Q^14) := by
      dsimp only [A₀,A₁,A₂]
      field_simp
    _ ≤ A₀*(1/R^2)+A₁*1+A₂*((R/N)^((2:ℝ)/3)/R^2) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hI0 hA₀)
        (mul_le_mul_of_nonneg_left hI1 hA₁)) (mul_le_mul_of_nonneg_left hII hA₂)
    _ = _ := by
      dsimp only [A₀,A₁,A₂]
      ring

public  theorem selected_band_grid_cardinality_bound
    (Chunks : Finset (ℝ × ℤ)) (band : (ℝ × ℤ) → Option ℕ)
    (Grid : ℕ → ℤ → Finset (ℝ × ℤ)) (Qbase kmax : ℕ)
    {Y M N R Cbase Cdensity L : ℝ}
    (hQbase : 0 < Qbase) (hY : 0 ≤ Y) (hM : 0 ≤ M) (hN : 0 < N)
    (hCd : 0 ≤ Cdensity) (hL : 1 ≤ L)
    (hbase : (Qbase:ℝ) ≤ Cbase*R)
    (hchunks : (Chunks.card:ℝ) ≤ Y*(8*M/N)) :
    let Q := fun k : ℕ => Qbase*2^k
    (∀ j ≤ kmax, ((Chunks.filter (fun p => band p=some (j+1))).card:ℝ) ≤
      Y*(Cdensity*M*R^2/(N*(Q j:ℝ)^2)*L)) →
    (∀ k ≤ kmax, ∀ r : ℤ,
      (Grid k r).card ≤ 2*(Chunks.filter (fun p => band p=some k)).card) →
    ∀ k ≤ kmax, ∀ r : ℤ,
      ((Grid k r).card:ℝ) ≤
        (16*Cbase^2+8*Cdensity)*Y*M*R^2/(N*(Q k:ℝ)^2)*L := by
  classical
  intro Q hbands hgrids k hk r
  have hQpos (j : ℕ) : (0:ℝ) < Q j := by
    exact_mod_cast Nat.mul_pos hQbase (by positivity : 0 < 2^j)
  have hLp : 0 ≤ L := zero_le_one.trans hL
  have hgrid : ((Grid k r).card:ℝ) ≤
      2*((Chunks.filter (fun p => band p=some k)).card:ℝ) := by
    exact_mod_cast hgrids k hk r
  cases k with
  | zero =>
    have hsub : ((Chunks.filter (fun p => band p=some 0)).card:ℝ) ≤ Chunks.card := by
      exact_mod_cast Finset.card_filter_le (s:=Chunks) (p:=fun p => band p=some 0)
    have hQsq : (Q 0:ℝ)^2 ≤ Cbase^2*R^2 := by
      simpa only [Q,pow_zero,Nat.mul_one,mul_pow] using
        pow_le_pow_left₀ (Nat.cast_nonneg Qbase) hbase 2
    have hcoef : 16*Cbase^2 ≤ (16*Cbase^2+8*Cdensity)*L := by
      calc
        _ ≤ 16*Cbase^2+8*Cdensity := by linarith only [hCd]
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hL
    calc
      _ ≤ 2*((Chunks.filter (fun p => band p=some 0)).card:ℝ) := hgrid
      _ ≤ 2*(Y*(8*M/N)) :=
        mul_le_mul_of_nonneg_left (hsub.trans hchunks) (by norm_num)
      _ = (16*Y*M/(N*(Q 0:ℝ)^2))*(Q 0:ℝ)^2 := by
        field_simp [(hQpos 0).ne']
        ring
      _ ≤ (16*Y*M/(N*(Q 0:ℝ)^2))*(Cbase^2*R^2) :=
        mul_le_mul_of_nonneg_left hQsq (by positivity)
      _ = (16*Cbase^2)*(Y*M*R^2/(N*(Q 0:ℝ)^2)) := by ring
      _ ≤ ((16*Cbase^2+8*Cdensity)*L)*(Y*M*R^2/(N*(Q 0:ℝ)^2)) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = _ := by ring
  | succ j =>
    have hj : j ≤ kmax := (Nat.le_succ j).trans hk
    have hstep : (Q (j+1):ℝ)=2*(Q j:ℝ) := by
      simp only [Q,pow_succ,Nat.cast_mul,Nat.cast_ofNat]
      ring
    have hcoef : 8*Cdensity ≤ 16*Cbase^2+8*Cdensity := by
      nlinarith only [sq_nonneg Cbase]
    calc
      _ ≤ 2*((Chunks.filter (fun p => band p=some (j+1))).card:ℝ) := hgrid
      _ ≤ 2*(Y*(Cdensity*M*R^2/(N*(Q j:ℝ)^2)*L)) :=
        mul_le_mul_of_nonneg_left (hbands j hj) (by norm_num)
      _ = (8*Cdensity)*(Y*M*R^2/(N*(Q (j+1):ℝ)^2))*L := by
        rw [hstep]
        field_simp
        ring
      _ ≤ (16*Cbase^2+8*Cdensity)*(Y*M*R^2/(N*(Q (j+1):ℝ)^2))*L :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef (by positivity)) hLp
      _ = _ := by ring

public  theorem selected_terminal_density_bound
    {n N M R Q Y Cdensity Csep L : ℝ}
    (hN : 0 < N) (hM : 0 ≤ M) (hY : 0 ≤ Y)
    (hCd : 0 ≤ Cdensity) (hC : 0 < Csep) (hL : 0 ≤ L)
    (hscale : N=8*n) (hQlower : N/Csep ≤ Q) :
    n*Y*(Cdensity*M*R^2/(N*Q^2)*L) ≤
      (Cdensity*Csep^2/8)*(Y*M*R^2/N^2)*L := by
  have hQ : 0 < Q := (div_pos hN hC).trans_le hQlower
  have hn : n=N/8 := by linarith only [hscale]
  calc
    _ = (Cdensity*Y*M*R^2/8)/Q^2*L := by rw [hn]; field_simp
    _ ≤ (Cdensity*Y*M*R^2/8)/(N/Csep)^2*L := by
      apply mul_le_mul_of_nonneg_right _ hL
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ (div_pos hN hC).le hQlower 2)
    _ = _ := by field_simp

public  theorem selected_band_mesh_cardinality_prefactor_bound
    {Y M N R Q K P Cmesh Ccard L T ε : ℝ}
    (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hK : 0 < K) (hP : 0 ≤ P)
    (hCm : 0 < Cmesh) (hε : 0 ≤ ε)
    (hQN : Q ≤ N) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hmesh : K ≤ Cmesh*Q*N/R^2)
    (hcard : P ≤ Ccard*Y*M*R^2/(N*Q^2)*L) :
    (R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10 ≤
      (Cmesh^12*Cmesh^ε*(2*Ccard)^10)*T^ε*L^10*
        (Y^10*M^10*N^2*R^8/Q^14) := by
  have hT : 0 < T := hN.trans_le hNT
  have hKT : K ≤ Cmesh*T := by
    calc
      _ ≤ Cmesh*Q*N/R^2 := hmesh
      _ ≤ Cmesh*Q := (div_le_iff₀ (sq_pos_of_pos hR)).mpr
        (mul_le_mul_of_nonneg_left hNR (by positivity))
      _ ≤ Cmesh*T := mul_le_mul_of_nonneg_left (hQN.trans hNT) hCm.le
  have hKpow : K^((12:ℝ)+ε) ≤
      (Cmesh*Q*N/R^2)^12*Cmesh^ε*T^ε := by
    calc
      _ = K^12*K^ε := by norm_num [Real.rpow_add hK]
      _ ≤ (Cmesh*Q*N/R^2)^12*(Cmesh*T)^ε := by gcongr
      _ = _ := by rw [Real.mul_rpow hCm.le hT.le]; ring
  have hPbound : 2*P ≤ (2*Ccard)*Y*M*R^2/(N*Q^2)*L := by
    calc
      _ ≤ 2*(Ccard*Y*M*R^2/(N*Q^2)*L) :=
        mul_le_mul_of_nonneg_left hcard (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ (R^2/Q)^6*((Cmesh*Q*N/R^2)^12*Cmesh^ε*T^ε)*
        ((2*Ccard)*Y*M*R^2/(N*Q^2)*L)^10 := by gcongr
    _ = (Cmesh^ε*T^ε*L^10)*
        ((R^2/Q)^6*(Cmesh*Q*N/R^2)^12*((2*Ccard)*Y*M*R^2/(N*Q^2))^10) := by
      rw [mul_pow]
      ring
    _ = _ := by
      rw [selected_band_prefactor_identity hR.ne' hQ.ne' hN.ne']
      ring

public  theorem positive_difference_completion_error_physical_bound
    {Y M N R T C : ℝ} (hY : 0 ≤ Y) (hN : 1 ≤ N)
    (hNM : N ≤ M) (hMT : M ≤ T) (hC : 0 ≤ C) :
    Y*(M/N+1)*(Real.sqrt (3*N)*Real.log (6*N)+C*R^2/N) ≤
      (2*Real.sqrt 3*(1+Real.log 6)+2*C)*
        (Y*M/Real.sqrt N+Y*M*R^2/N^2)*(1+Real.log T) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hMp : 0 < M := hNp.trans_le hNM
  have hT : 1 ≤ T := hN.trans (hNM.trans hMT)
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hlog6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hlogN := Real.log_le_log hNp (hNM.trans hMT)
  have hlog : Real.log (6*N) ≤ (1+Real.log 6)*(1+Real.log T) := by
    rw [Real.log_mul (by norm_num : (6:ℝ) ≠ 0) hNp.ne']
    nlinarith only [hlogN,hlog6,hlogT,mul_nonneg hlog6 hlogT]
  have hlogPos : 0 ≤ Real.log (6*N) := Real.log_nonneg (by linarith only [hN])
  have hL : 1 ≤ 1+Real.log T := by linarith only [hlogT]
  have hratio : 1 ≤ M/N := (le_div_iff₀ hNp).mpr (by simpa only [one_mul] using hNM)
  have hfront : M/N+1 ≤ 2*M/N := by
    calc
      _ ≤ M/N+M/N := add_le_add le_rfl hratio
      _ = _ := by ring
  have hsum : Real.sqrt (3*N)*Real.log (6*N)+C*R^2/N ≤
      (Real.sqrt 3*Real.sqrt N*(1+Real.log 6)+C*R^2/N)*(1+Real.log T) := by
    have hc := le_mul_of_one_le_right (by positivity : 0 ≤ C*R^2/N) hL
    calc
      _ = Real.sqrt 3*Real.sqrt N*Real.log (6*N)+C*R^2/N := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
      _ ≤ Real.sqrt 3*Real.sqrt N*((1+Real.log 6)*(1+Real.log T))+
          (C*R^2/N)*(1+Real.log T) :=
        add_le_add (mul_le_mul_of_nonneg_left hlog (by positivity)) hc
      _ = _ := by ring
  have hcancel : M/N*Real.sqrt N=M/Real.sqrt N := by
    calc
      _ = M*(Real.sqrt N/N) := by ring
      _ = _ := by rw [Real.sqrt_div_self']; ring
  let A := 2*Real.sqrt 3*(1+Real.log 6)
  let E₁ := Y*M/Real.sqrt N
  let E₂ := Y*M*R^2/N^2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hE₁ : 0 ≤ E₁ := by dsimp only [E₁]; positivity
  have hE₂ : 0 ≤ E₂ := by dsimp only [E₂]; positivity
  calc
    _ ≤ Y*(2*M/N)*
        ((Real.sqrt 3*Real.sqrt N*(1+Real.log 6)+C*R^2/N)*(1+Real.log T)) := by
      gcongr
    _ = (A*(Y*(M/N*Real.sqrt N))+2*C*E₂)*(1+Real.log T) := by
      dsimp only [A,E₂]
      ring
    _ = (A*E₁+2*C*E₂)*(1+Real.log T) := by
      rw [hcancel]
      dsimp only [E₁]
      ring
    _ ≤ ((A+2*C)*(E₁+E₂))*(1+Real.log T) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith only [hlogT])
      nlinarith only [mul_nonneg hA hE₂,mul_nonneg hC hE₁]
    _ = _ := rfl

public  theorem positive_difference_endpoint_error_physical_bound
    {Y N n R Q U κ σ c Cphys B : ℝ}
    (hY : 0 ≤ Y) (hN : 1 ≤ N) (hR : 0 < R) (hRQ : R ≤ Q) (hQN : Q ≤ N)
    (hκ : 0 < κ) (hσ : 0 ≤ σ) (hc : 0 < c) (hCphys : 0 ≤ Cphys)
    (hB : 1 ≤ B) (hscale : N=8*n)
    (hUupper : U ≤ (N/Q)^((2:ℝ)/3)/B) :
    Y*(2*((56*U/κ)*N+N/(Cphys+2)+2)+
        2*((14*σ/c)*U*N)+6*N+2*n) ≤
      (112/κ+28*σ/c+2/(Cphys+2)+41/4)*
        (Y*N*(N/R)^((2:ℝ)/3)) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hQ : 0 < Q := hR.trans_le hRQ
  let X := (N/R)^((2:ℝ)/3)
  let A := 112/κ+28*σ/c
  let E := 2/(Cphys+2)+25/4
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hn : n=N/8 := by linarith only [hscale]
  have hUX : U ≤ X := by
    calc
      _ ≤ (N/Q)^((2:ℝ)/3)/B := hUupper
      _ ≤ (N/Q)^((2:ℝ)/3) := div_le_self (by positivity) hB
      _ ≤ (N/R)^((2:ℝ)/3) := Real.rpow_le_rpow (by positivity)
        (div_le_div_of_nonneg_left hNp.le hR hRQ) (by norm_num)
  have hX : 1 ≤ X := Real.one_le_rpow
    ((le_div_iff₀ hR).mpr (by simpa only [one_mul] using hRQ.trans hQN)) (by norm_num)
  have hNX : N ≤ X*N := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hX hNp.le
  have hXN : 1 ≤ X*N := hN.trans hNX
  calc
    _ = Y*(A*(U*N)+E*N+4) := by
      dsimp only [A,E]
      rw [hn]
      ring
    _ ≤ Y*(A*(X*N)+E*(X*N)+4*(X*N)) := by
      apply mul_le_mul_of_nonneg_left _ hY
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hUX hNp.le) hA)
          (mul_le_mul_of_nonneg_left hNX hE))
        (by nlinarith only [hXN])
    _ = _ := by
      dsimp only [A,E,X]
      ring

public  theorem eventually_selected_band_logarithmic_absorption
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in Filter.atTop, 0 < T ∧ 1 ≤ Real.log T ∧
      C*T^(ε/2)*(1+Real.log T)^36 ≤ T^ε := by
  filter_upwards [
    TaoTrudgianYang2025.eventually_const_log_pow_le_rpow (C*2^36) (by positivity) 36
      (show 0 < ε/2 by linarith only [hε]),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Filter.eventually_ge_atTop (1:ℝ)] with T hsmall hlog hT
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hpoly : C*(1+Real.log T)^36 ≤ T^(ε/2) := by
    calc
      _ ≤ C*(2*Real.log T)^36 := by gcongr; linarith only [hlog]
      _ = (C*2^36)*(Real.log T)^36 := by rw [mul_pow]; ring
      _ ≤ _ := hsmall
  refine ⟨hTp,hlog,?_⟩
  calc
    _ = (C*(1+Real.log T)^36)*T^(ε/2) := by ring
    _ ≤ T^(ε/2)*T^(ε/2) := mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ = _ := by rw [←Real.rpow_add hTp]; congr 1; ring

public  theorem exists_uniform_source_physical_budget
    {Csep A₄ A₂ B Cbuffer Clinear Cwidth : ℝ}
    (hSep : 0 ≤ Csep) (hA₄ : 0 ≤ A₄) (hA₂ : 0 ≤ A₂)
    (hB : 0 ≤ B) (hBuffer : 0 ≤ Cbuffer) (hLinear : 0 ≤ Clinear)
    (hWidth : 0 ≤ Cwidth) :
    ∃ Cbudget : ℝ, 1 ≤ Cbudget ∧ Csep ≤ Cbudget ∧
      ∀ (N R M U : ℝ), 2 ≤ N → 1 ≤ R →
      Cbudget*R ≤ N → Cbudget*N ≤ R^2 → Cbudget*N^2 ≤ M → U ≤ N →
      0 < M ∧ R ≤ N ∧ N ≤ R^2 ∧ N^2 ≤ M ∧ N*R ≤ M ∧ N^3 ≤ M*R^2 ∧ R ≤ M ∧
      7*N+2 ≤ M/4 ∧
      A₄*(6*N+1)^4 ≤ M*N*R^2 ∧
      A₂*(6*N+1)^2 ≤ N*R^2 ∧
      B*R^2/N^2 ≤ 1/2 ∧
      2*((Cbuffer*U)*N+Clinear*N+2+(Cwidth*U)*N)+6*N ≤ M ∧
      (∀ T : ℝ, 0 < T → T*N*R^2=M^3 → M ≤ T) := by
  let Cbudget := 43+Csep+2401*A₄+49*A₂+2*B+2*Cbuffer+2*Cwidth+2*Clinear
  have hbounds : 1 ≤ Cbudget ∧ Csep ≤ Cbudget ∧ 32 ≤ Cbudget ∧
      2401*A₄ ≤ Cbudget ∧ 49*A₂ ≤ Cbudget ∧ 2*B ≤ Cbudget ∧
      2*(Cbuffer+Cwidth)+2*Clinear+10 ≤ Cbudget := by
    dsimp only [Cbudget]
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;>
      linarith only [hSep,hA₄,hA₂,hB,hBuffer,hLinear,hWidth]
  obtain ⟨hC,hSepC,h32,hC₄,hC₂,hCB,hCend⟩ := hbounds
  refine ⟨Cbudget,hC,hSepC,?_⟩
  intro N R M U hN hR hRNbudget hNRbudget hMbudget hUN
  have hNp : 0 < N := by linarith only [hN]
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hRN : R ≤ N :=
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hRp.le : R ≤ Cbudget*R).trans hRNbudget
  have hNR : N ≤ R^2 :=
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hNp.le : N ≤ Cbudget*N).trans hNRbudget
  have hNM₂ : N^2 ≤ M :=
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC (sq_nonneg N) : N^2 ≤ Cbudget*N^2).trans hMbudget
  have hNsq : N ≤ N^2 := by nlinarith only [hN]
  have hNsqOne : 1 ≤ N^2 := by nlinarith only [hN]
  have hNM : N ≤ M := hNsq.trans hNM₂
  have hMp : 0 < M := hNp.trans_le hNM
  have hNRM : N*R ≤ M := by
    calc
      _ ≤ N*N := mul_le_mul_of_nonneg_left hRN hNp.le
      _ = N^2 := (pow_two N).symm
      _ ≤ M := hNM₂
  have hN₃ : N^3 ≤ M*R^2 := by
    calc
      _ = N^2*N := by ring
      _ ≤ _ := mul_le_mul hNM₂ hNR hNp.le hMp.le
  have hpad : 7*N+2 ≤ M/4 := by
    have hh := (mul_le_mul_of_nonneg_right h32 (sq_nonneg N)).trans hMbudget
    have hn := mul_le_mul_of_nonneg_left hNsq (by norm_num : (0:ℝ) ≤ 32)
    nlinarith only [hh,hn,hN]
  have hshort : 6*N+1 ≤ 7*N := by linarith only [hN]
  have hquartic : A₄*(6*N+1)^4 ≤ M*N*R^2 := by
    calc
      _ ≤ A₄*(7*N)^4 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hshort 4) hA₄
      _ = (2401*A₄)*N^4 := by ring
      _ ≤ Cbudget*N^4 := mul_le_mul_of_nonneg_right hC₄ (by positivity)
      _ = (Cbudget*N^2)*N^2 := by ring
      _ ≤ M*N^2 := mul_le_mul_of_nonneg_right hMbudget (sq_nonneg N)
      _ = M*N*N := by ring
      _ ≤ M*N*R^2 := mul_le_mul_of_nonneg_left hNR (by positivity)
  have hquadratic : A₂*(6*N+1)^2 ≤ N*R^2 := by
    calc
      _ ≤ A₂*(7*N)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hshort 2) hA₂
      _ = (49*A₂)*N^2 := by ring
      _ ≤ Cbudget*N^2 := mul_le_mul_of_nonneg_right hC₂ (sq_nonneg N)
      _ = (Cbudget*N)*N := by ring
      _ ≤ R^2*N := mul_le_mul_of_nonneg_right hNRbudget hNp.le
      _ = _ := by ring
  have hsmall : B*R^2/N^2 ≤ 1/2 := by
    have hCsq : Cbudget ≤ Cbudget^2 := by nlinarith only [hC]
    have hmul := mul_le_mul_of_nonneg_right (hCB.trans hCsq) (sq_nonneg R)
    have hsq : Cbudget^2*R^2 ≤ N^2 := by
      simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hRNbudget 2
    apply (div_le_iff₀ (sq_pos_of_pos hNp)).mpr
    nlinarith only [hmul,hsq]
  have hroom : 2*((Cbuffer*U)*N+Clinear*N+2+(Cwidth*U)*N)+6*N ≤ M := by
    have hUN' : U*N ≤ N^2 := by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right hUN hNp.le
    have hb := mul_le_mul_of_nonneg_left hUN' hBuffer
    have hw := mul_le_mul_of_nonneg_left hUN' hWidth
    have hl := mul_le_mul_of_nonneg_left hNsq hLinear
    calc
      _ ≤ (2*(Cbuffer+Cwidth)+2*Clinear+10)*N^2 := by
        nlinarith only [hb,hw,hl,hNsq,hNsqOne]
      _ ≤ Cbudget*N^2 := mul_le_mul_of_nonneg_right hCend (sq_nonneg N)
      _ ≤ M := hMbudget
  refine ⟨hMp,hRN,hNR,hNM₂,hNRM,hN₃,hRN.trans hNM,hpad,hquartic,hquadratic,hsmall,hroom,?_⟩
  intro T hT hscale
  have hRM₂ : R^2 ≤ M :=
    (pow_le_pow_left₀ hRp.le hRN 2).trans hNM₂
  have hprod : N*R^2 ≤ M^2 := by
    calc
      _ ≤ M*M := mul_le_mul hNM hRM₂ (sq_nonneg R) hMp.le
      _ = _ := (pow_two M).symm
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hMp)).mp
  calc
    M^2*M = M^3 := by ring
    _ = T*(N*R^2) := by nlinarith only [hscale]
    _ ≤ T*M^2 := mul_le_mul_of_nonneg_left hprod hT.le
    _ = M^2*T := by ring

public  theorem selected_band_finite_power_cleanup
    (kmax : ℕ) (G : ℕ → ℤ → ℝ)
    {S Terminal Endpoint E Main L Tpow Cband Cerror Cgrid : ℝ}
    (hTerminal : 0 ≤ Terminal) (hEndpoint : 0 ≤ Endpoint)
    (hMain : 0 ≤ Main) (hL : 1 ≤ L) (hTpow : 1 ≤ Tpow)
    (hCb : 0 ≤ Cband) (hCg : 0 ≤ Cgrid)
    (hband : (kmax:ℝ)+2 ≤ Cband*L)
    (hterminal : Terminal ≤ Cerror*E*L) (hendpoint : Endpoint ≤ Cerror*E*L)
    (hgrid : ∀ k∈Finset.range (kmax+1), ∀ r∈Finset.Ico (0:ℤ) 8,
      G k r ≤ Cgrid*Tpow*L^22*(E^12+Main))
    (hsource : S ≤ 2^11*(((kmax:ℝ)+2)^11*
      (Terminal^12+(4:ℝ)^12*(8:ℝ)^11*
        ∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,G k r)+Endpoint^12)) :
    S ≤ (2:ℝ)^11*(Cband^11*Cerror^12+
      (4:ℝ)^12*(8:ℝ)^12*Cband^12*Cgrid+Cerror^12)*
        Tpow*L^36*(E^12+Main) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hT0 : 0 ≤ Tpow := zero_le_one.trans hTpow
  have hTotal : 0 ≤ E^12+Main := by positivity
  have hEtotal : E^12 ≤ E^12+Main := by linarith only [hMain]
  have hLpow (m : ℕ) (hm : m ≤ 36) : L^m ≤ L^36 :=
    pow_le_pow_right₀ hL hm
  have herror (m : ℕ) (hm : m ≤ 36) :
      E^12*L^m ≤ Tpow*L^36*(E^12+Main) := by
    calc
      _ ≤ (E^12+Main)*L^36 := mul_le_mul hEtotal (hLpow m hm) (by positivity) hTotal
      _ ≤ Tpow*((E^12+Main)*L^36) :=
        le_mul_of_one_le_left (by positivity) hTpow
      _ = _ := by ring
  have hsum : (∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,G k r) ≤
      ((kmax:ℝ)+1)*8*(Cgrid*Tpow*L^22*(E^12+Main)) := by
    calc
      _ ≤ ∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,
          Cgrid*Tpow*L^22*(E^12+Main) := by
        apply Finset.sum_le_sum
        intro k hk
        exact Finset.sum_le_sum (hgrid k hk)
      _ = _ := by
        have hcard8 : (Finset.Ico (0:ℤ) 8).card=8 := by decide
        simp only [Finset.sum_const,hcard8,Finset.card_range,nsmul_eq_mul,
          Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
        ring
  have hk : (kmax:ℝ)+1 ≤ Cband*L := by linarith only [hband]
  have hsumMajor : (∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,G k r) ≤
      (Cband*L)*8*(Cgrid*Tpow*L^22*(E^12+Main)) := by
    apply hsum.trans
    gcongr
  have hterm :
      ((kmax:ℝ)+2)^11*Terminal^12 ≤
        (Cband^11*Cerror^12)*Tpow*L^36*(E^12+Main) := by
    calc
      _ ≤ (Cband*L)^11*(Cerror*E*L)^12 := by gcongr
      _ = (Cband^11*Cerror^12)*(E^12*L^23) := by ring
      _ ≤ (Cband^11*Cerror^12)*(Tpow*L^36*(E^12+Main)) :=
        mul_le_mul_of_nonneg_left (herror 23 (by norm_num)) (by positivity)
      _ = _ := by ring
  have hgridCost :
      ((kmax:ℝ)+2)^11*((4:ℝ)^12*(8:ℝ)^11*
        ∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,G k r) ≤
      ((4:ℝ)^12*(8:ℝ)^12*Cband^12*Cgrid)*Tpow*L^36*(E^12+Main) := by
    have hkpow : ((kmax:ℝ)+2)^11 ≤ (Cband*L)^11 :=
      pow_le_pow_left₀ (by positivity) hband 11
    have hL34 : L^34 ≤ L^36 := hLpow 34 (by norm_num)
    calc
      _ ≤ ((kmax:ℝ)+2)^11*((4:ℝ)^12*(8:ℝ)^11*
          ((Cband*L)*8*(Cgrid*Tpow*L^22*(E^12+Main)))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsumMajor (by positivity)) (by positivity)
      _ ≤ (Cband*L)^11*((4:ℝ)^12*(8:ℝ)^11*
          ((Cband*L)*8*(Cgrid*Tpow*L^22*(E^12+Main)))) :=
        mul_le_mul_of_nonneg_right hkpow (by positivity)
      _ = ((4:ℝ)^12*(8:ℝ)^12*Cband^12*Cgrid)*Tpow*L^34*(E^12+Main) := by ring
      _ ≤ _ := by gcongr
  have hend : Endpoint^12 ≤ Cerror^12*Tpow*L^36*(E^12+Main) := by
    calc
      _ ≤ (Cerror*E*L)^12 := pow_le_pow_left₀ hEndpoint hendpoint 12
      _ = Cerror^12*(E^12*L^12) := by ring
      _ ≤ Cerror^12*(Tpow*L^36*(E^12+Main)) :=
        mul_le_mul_of_nonneg_left (herror 12 (by norm_num)) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ 2^11*(((kmax:ℝ)+2)^11*
        (Terminal^12+(4:ℝ)^12*(8:ℝ)^11*
          ∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,G k r)+Endpoint^12) := hsource
    _ = 2^11*(((kmax:ℝ)+2)^11*Terminal^12+
        ((kmax:ℝ)+2)^11*((4:ℝ)^12*(8:ℝ)^11*
          ∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,G k r)+Endpoint^12) := by ring
    _ ≤ 2^11*((Cband^11*Cerror^12)*Tpow*L^36*(E^12+Main)+
        ((4:ℝ)^12*(8:ℝ)^12*Cband^12*Cgrid)*Tpow*L^36*(E^12+Main)+
        Cerror^12*Tpow*L^36*(E^12+Main)) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add hterm hgridCost) hend) (by positivity)
    _ = _ := by ring

public  theorem positive_difference_source_physical_regime_coefficients
    {σ c J κ T M N R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) (hκ : 0 < κ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) (hNR : N ≤ R^2) (hNM : N^2 ≤ M) :
    let lambda := c*κ*T/(12*J*M^2)
    let Uband := (3*J/σ)*T/(2*M^2)
    Uband/lambda=18*J^2/(σ*c*κ) ∧
      Uband^2*(R^8/N^4)=(3*J/(2*σ))^2*M^2*R^4/N^6 ∧
      1+R^4/(6*N^2) ≤ (7/6:ℝ)*R^4/N^2 ∧
      1+R^4*Uband^2/N^2 ≤ (1+(3*J/(2*σ))^2)*M^2/N^4 := by
  intro lambda Uband
  have hTscale : T=M^3/(N*R^2) := (eq_div_iff (by positivity)).mpr (by
    nlinarith only [hscale])
  have hUscale : Uband=(3*J/(2*σ))*M/(N*R^2) := by
    dsimp only [Uband]
    rw [hTscale]
    field_simp
  have hratio : Uband/lambda=18*J^2/(σ*c*κ) := by
    dsimp only [Uband,lambda]
    field_simp
    ring
  have hupper : 1 ≤ R^4/N^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hN)).mpr
    have hh := pow_le_pow_left₀ hN.le hNR 2
    nlinarith only [hh]
  have hlower : 1 ≤ M^2/N^4 := by
    apply (le_div_iff₀ (pow_pos hN 4)).mpr
    have hh := pow_le_pow_left₀ (sq_nonneg N) hNM 2
    nlinarith only [hh]
  refine ⟨hratio,?_,?_,?_⟩
  · rw [hUscale]
    field_simp
  · have he : R^4/(6*N^2)=(R^4/N^2)/6 := by ring
    rw [he]
    calc
      _ ≤ R^4/N^2+(R^4/N^2)/6 := add_le_add hupper le_rfl
      _ = _ := by ring
  · have he : R^4*Uband^2/N^2=(3*J/(2*σ))^2*(M^2/N^4) := by
      rw [hUscale]
      field_simp
    rw [he]
    calc
      _ ≤ M^2/N^4+(3*J/(2*σ))^2*(M^2/N^4) := add_le_add hlower le_rfl
      _ = _ := by ring

private theorem upper_selected_grid_family_bound
    {Y Z P M N R Q U K V Jsep D Cdelta Cupper Cv B delta Cmesh Ccard L T ε : ℝ}
    (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hZY : Z ≤ Y) (hP : 0 ≤ P)
    (hM : 0 ≤ M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q) (hK : 0 < K)
    (hV : 0 ≤ V) (hJ : 0 ≤ Jsep) (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta)
    (hCu : 0 ≤ Cupper) (hCv : 0 ≤ Cv) (hB : 0 < B) (hd : 0 ≤ delta)
    (hCm : 0 < Cmesh) (hT : 1 ≤ T) (hε : 0 ≤ ε)
    (hQN : Q ≤ N) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hmesh : K ≤ Cmesh*Q*N/R^2)
    (hcard : P ≤ Ccard*Y*M*R^2/(N*Q^2)*L)
    (hVupper : V ≤ Cv*R^4/N^2) (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    (R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10*
      (V*D*Z*(M/N)*(1+delta*Jsep)+Z^2*V*(Cupper*M^2/(N^4*U))*T^ε) ≤
      (Cmesh^12*Cmesh^ε*(2*Ccard)^10)*T^(2*ε)*L^10*Cv*
        (D*(Y^11*M^11/(N*R^2))+
          D*Cdelta*(Y^11*Jsep*M^11/N^3)+
          2*B*Cupper*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))) := by
  have hQ : 0 < Q := hR.trans_le hRQ
  have hU := (physical_reference_reciprocal_bound hN hQ hB hUlower).1
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hTpow : 1 ≤ T^ε := Real.one_le_rpow hT hε
  let TypeI := V*D*Y*(M/N)*(1+delta*Jsep)
  let Pair := Y^2*V*(Cupper*M^2/(N^4*U))
  let Cpref := Cmesh^12*Cmesh^ε*(2*Ccard)^10
  let Physical := Y^10*M^10*N^2*R^8/Q^14
  have hTypeI : 0 ≤ TypeI := by dsimp only [TypeI]; positivity
  have hPair : 0 ≤ Pair := by dsimp only [Pair]; positivity
  have hCpref : 0 ≤ Cpref := by dsimp only [Cpref]; positivity
  have hPhysical : 0 ≤ Physical := by dsimp only [Physical]; positivity
  have hmass : V*D*Z*(M/N)*(1+delta*Jsep)+
      Z^2*V*(Cupper*M^2/(N^4*U))*T^ε ≤ (TypeI+Pair)*T^ε := by
    calc
      _ ≤ TypeI+Pair*T^ε := by dsimp only [TypeI,Pair]; gcongr
      _ ≤ TypeI*T^ε+Pair*T^ε :=
        add_le_add (le_mul_of_one_le_right hTypeI hTpow) le_rfl
      _ = _ := by ring
  have hpref := selected_band_mesh_cardinality_prefactor_bound
    hN hR hQ hK hP hCm hε hQN hNR hNT hmesh hcard
  have hmonomial := upper_physical_family_monomial_bound
    hY hM hN hR hRQ hJ hD hCd hCu hCv hB hd hVupper hdelta hUlower
  have hTproduct : T^ε*T^ε=T^(2*ε) := by
    rw [←Real.rpow_add hTp]
    congr 1
    ring
  calc
    _ ≤ (Cpref*T^ε*L^10*Physical)*((TypeI+Pair)*T^ε) := by
      exact mul_le_mul hpref hmass (by positivity) (by positivity)
    _ = Cpref*T^(2*ε)*L^10*(Physical*(TypeI+Pair)) := by
      calc
        _ = Cpref*(T^ε*T^ε)*L^10*(Physical*(TypeI+Pair)) := by ring
        _ = _ := by rw [hTproduct]
    _ ≤ Cpref*T^(2*ε)*L^10*
        (Cv*(D*(Y^11*M^11/(N*R^2))+
          D*Cdelta*(Y^11*Jsep*M^11/N^3)+
          2*B*Cupper*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)))) :=
      mul_le_mul_of_nonneg_left hmonomial (by positivity)
    _ = _ := by dsimp only [Cpref]; ring

public  theorem exists_source_cutoff_margins
    {κ Ccurv Cphys Sector Esize : ℝ}
    (hκ : 0 < κ) (hCcurv : 0 ≤ Ccurv) (hCphys : 0 ≤ Cphys)
    (hEsize : 0 < Esize) :
    ∃ Bcut Bselect : ℝ, 0 < Bcut ∧ 1 ≤ Bselect ∧
      2+168/κ ≤ Bselect ∧ 7*Bcut ≤ κ*Bselect ∧
      Sector ≤ Bselect*Esize ∧ 61*Ccurv*Cphys ≤ Bcut := by
  let Bcut := 1+61*Ccurv*Cphys
  let Bselect := max 1 (max (2+168/κ) (max (7*Bcut/κ) (Sector/Esize)))
  have hBcut : 0 < Bcut := by dsimp only [Bcut]; positivity
  have hBs : 1 ≤ Bselect := le_max_left _ _
  have hSize : 2+168/κ ≤ Bselect := (le_max_left _ _).trans (le_max_right _ _)
  have hCut : 7*Bcut/κ ≤ Bselect :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hSec : Sector/Esize ≤ Bselect :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨Bcut,Bselect,hBcut,hBs,hSize,?_,(div_le_iff₀ hEsize).mp hSec,?_⟩
  · calc
      7*Bcut ≤ Bselect*κ := (div_le_iff₀ hκ).mp hCut
      _ = κ*Bselect := mul_comm _ _
  · dsimp only [Bcut]
    linarith

public  theorem upper_numerical_constants_nonnegative
    {σsrc csrc Usrc κ Cphys Csrc Couter CUP Dtype Bselect Csep ε : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) (hκ : 0 < κ)
    (hCphys : 0 ≤ Cphys) (hCsrcZero : 0 ≤ Csrc) (hCouter : 0 ≤ Couter)
    (hCUP : 0 ≤ CUP) (hDtype : 0 ≤ Dtype) (hBsOne : 1 ≤ Bselect)
    (hCsep : 1 ≤ Csep) :
    let εloss := ε/4
    let Cmesh := 2*max 1 (63*Usrc/(2*σsrc))
    let CtailBand := (6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc
    let ClowBand := (3*Usrc/σsrc+csrc/(32*σsrc))*((3072*σsrc)/csrc)^2+(3072*σsrc)/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    let Carg := 512*768*σsrc/csrc
    let DensityLog := 3+Real.log (Carg+1)
    let Cdensity := 128*CerrorBand*DensityLog
    let Ccard := 16*(1536:ℝ)^2+8*Cdensity
    let CKlog := 3+Real.log (Cmesh+1)
    let Cband := 2+1/Real.log 2
    let Cdelta := (16*Usrc/csrc)*Real.sqrt ((Usrc/(2*σsrc))*Cmesh)
    let Cmass := Dtype+Dtype*Cdelta+2*Bselect*CUP
    let Cfamily := Couter*
      (Cmesh^12*Cmesh^εloss*(2*Ccard)^10)*(7/6:ℝ)*Cmass
    let CE₀ := 2*Real.sqrt 3*(1+Real.log 6)+24*σsrc/csrc
    let Cterminal := Cdensity*Csep^2/8
    let Cendpoint := 112/κ+28*σsrc/csrc+2/(Cphys+2)+41/4
    let Cerror := 1+Csrc*CE₀+Cterminal+Cendpoint
    let Cgrid := (2:ℝ)^11*(Cerror^12+(Csrc*CKlog)^12*Cfamily)
    let Ctotal := (2:ℝ)^11*(Cband^11*Cerror^12+
      (4:ℝ)^12*(8:ℝ)^12*Cband^12*Cgrid+Cerror^12)
    0 ≤ CtailBand ∧
    0 ≤ ClowBand ∧
    0 ≤ CerrorBand ∧
    1 ≤ Cmesh ∧
    0 ≤ Carg ∧
    0 ≤ DensityLog ∧
    0 ≤ Cdensity ∧
    0 ≤ Ccard ∧
    0 ≤ CKlog ∧
    0 ≤ Cband ∧
    0 ≤ Cdelta ∧
    0 ≤ Cmass ∧
    0 ≤ Cfamily ∧
    0 ≤ CE₀ ∧
    0 ≤ Cterminal ∧
    0 ≤ Cendpoint ∧
    0 ≤ Cerror ∧
    Csrc*CE₀ ≤ Cerror ∧
    Cterminal ≤ Cerror ∧
    Cendpoint ≤ Cerror ∧
    0 ≤ Cgrid ∧
    0 ≤ Ctotal := by
  classical
  intro εloss Cmesh CtailBand ClowBand CerrorBand Carg DensityLog Cdensity Ccard CKlog Cband Cdelta Cmass Cfamily CE₀ Cterminal Cendpoint Cerror Cgrid Ctotal
  have hBs : 0 < Bselect := zero_lt_one.trans_le hBsOne
  have hCtailBand : 0 ≤ CtailBand := by dsimp only [CtailBand]; positivity
  have hClowBand : 0 ≤ ClowBand := by dsimp only [ClowBand]; positivity
  have hCerrorBand : 0 ≤ CerrorBand := by dsimp only [CerrorBand]; positivity
  have hCmeshOne : 1 ≤ Cmesh := by
    have hh := le_max_left (1:ℝ) (63*Usrc/(2*σsrc))
    dsimp only [Cmesh]
    linarith only [hh]
  have hCmesh : 0 < Cmesh := zero_lt_one.trans_le hCmeshOne
  have hCarg : 0 ≤ Carg := by dsimp only [Carg]; positivity
  have hDensityLog : 0 ≤ DensityLog := by
    have hh := Real.log_nonneg (show (1:ℝ) ≤ Carg+1 by linarith only [hCarg])
    dsimp only [DensityLog]
    linarith only [hh]
  have hCdensity : 0 ≤ Cdensity := by dsimp only [Cdensity]; positivity
  have hCcard : 0 ≤ Ccard := by dsimp only [Ccard]; positivity
  have hCKlog : 0 ≤ CKlog := by
    have hh := Real.log_nonneg (show (1:ℝ) ≤ Cmesh+1 by linarith only [hCmeshOne])
    dsimp only [CKlog]
    linarith only [hh]
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCband : 0 ≤ Cband := by dsimp only [Cband]; positivity
  have hCdelta : 0 ≤ Cdelta := by dsimp only [Cdelta]; positivity
  have hCmass : 0 ≤ Cmass := by dsimp only [Cmass]; positivity
  have hCfamily : 0 ≤ Cfamily := by dsimp only [Cfamily]; positivity
  have hlogSix : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hCE₀ : 0 ≤ CE₀ := by dsimp only [CE₀]; positivity
  have hCterminal : 0 ≤ Cterminal := by dsimp only [Cterminal]; positivity
  have hCendpoint : 0 ≤ Cendpoint := by dsimp only [Cendpoint]; positivity
  have hCerror : 0 ≤ Cerror := by dsimp only [Cerror]; positivity
  have hErrorCompletion : Csrc*CE₀ ≤ Cerror := by
    dsimp only [Cerror]
    linarith only [hCterminal,hCendpoint]
  have hErrorTerminal : Cterminal ≤ Cerror := by
    dsimp only [Cerror]
    nlinarith only [mul_nonneg hCsrcZero hCE₀,hCendpoint]
  have hErrorEndpoint : Cendpoint ≤ Cerror := by
    dsimp only [Cerror]
    nlinarith only [mul_nonneg hCsrcZero hCE₀,hCterminal]
  have hCgrid : 0 ≤ Cgrid := by dsimp only [Cgrid]; positivity
  have hCtotal : 0 ≤ Ctotal := by dsimp only [Ctotal]; positivity

  exact ⟨hCtailBand,hClowBand,hCerrorBand,hCmeshOne,hCarg,hDensityLog,hCdensity,hCcard,hCKlog,hCband,hCdelta,hCmass,hCfamily,hCE₀,hCterminal,hCendpoint,hCerror,hErrorCompletion,hErrorTerminal,hErrorEndpoint,hCgrid,hCtotal⟩

public  theorem selected_grid_completion_bound
    {a b F E Main L W Cerror Clog Cfamily : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hMain : 0 ≤ Main) (hCf : 0 ≤ Cfamily)
    (hL : 1 ≤ L) (hW : 1 ≤ W)
    (haBound : a ≤ Cerror*E*L) (hbBound : b ≤ Clog*L)
    (hFBound : F ≤ Cfamily*W*L^10*Main) :
    (2:ℝ)^11*(a^12+b^12*F) ≤
      (2:ℝ)^11*(Cerror^12+Clog^12*Cfamily)*W*L^22*(E^12+Main) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hL12 : L^12 ≤ L^22 := pow_le_pow_right₀ hL (by norm_num)
  have hFirst : a^12 ≤ Cerror^12*W*L^22*E^12 := by
    calc
      _ ≤ (Cerror*E*L)^12 := pow_le_pow_left₀ ha haBound 12
      _ = Cerror^12*E^12*L^12 := by ring
      _ ≤ Cerror^12*E^12*L^22 := mul_le_mul_of_nonneg_left hL12 (by positivity)
      _ ≤ (Cerror^12*E^12*L^22)*W := le_mul_of_one_le_right (by positivity) hW
      _ = _ := by ring
  have hSecond : b^12*F ≤ (Clog^12*Cfamily)*W*L^22*Main := by
    calc
      _ ≤ b^12*(Cfamily*W*L^10*Main) :=
        mul_le_mul_of_nonneg_left hFBound (by positivity)
      _ ≤ (Clog*L)^12*(Cfamily*W*L^10*Main) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb hbBound 12) (by positivity)
      _ = _ := by ring
  have hCross : Cerror^12*E^12+(Clog^12*Cfamily)*Main ≤
      (Cerror^12+Clog^12*Cfamily)*(E^12+Main) := by
    nlinarith only [
      mul_nonneg (show 0 ≤ Cerror^12 by positivity) hMain,
      mul_nonneg (show 0 ≤ Clog^12*Cfamily by positivity) (show 0 ≤ E^12 by positivity)]
  calc
    _ ≤ (2:ℝ)^11*(Cerror^12*W*L^22*E^12+(Clog^12*Cfamily)*W*L^22*Main) :=
      mul_le_mul_of_nonneg_left (add_le_add hFirst hSecond) (by positivity)
    _ = ((2:ℝ)^11*W*L^22)*(Cerror^12*E^12+(Clog^12*Cfamily)*Main) := by ring
    _ ≤ ((2:ℝ)^11*W*L^22)*((Cerror^12+Clog^12*Cfamily)*(E^12+Main)) :=
      mul_le_mul_of_nonneg_left hCross (by positivity)
    _ = _ := by ring

private theorem upper_selected_grid_family_total_bound
    {Y Z P M N R Q U K V Jsep D Cdelta Cupper Cv B delta Cmesh Ccard L T ε Couter : ℝ}
    (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hZY : Z ≤ Y) (hP : 0 ≤ P)
    (hM : 0 ≤ M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q) (hK : 0 < K)
    (hV : 0 ≤ V) (hJ : 0 ≤ Jsep) (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta)
    (hCu : 0 ≤ Cupper) (hCv : 0 ≤ Cv) (hB : 0 < B) (hd : 0 ≤ delta)
    (hCm : 0 < Cmesh) (hT : 1 ≤ T) (hε : 0 ≤ ε) (hCo : 0 ≤ Couter)
    (hQN : Q ≤ N) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hmesh : K ≤ Cmesh*Q*N/R^2)
    (hcard : P ≤ Ccard*Y*M*R^2/(N*Q^2)*L)
    (hVupper : V ≤ Cv*R^4/N^2) (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    Couter*(R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10*
      (V*D*Z*(M/N)*(1+delta*Jsep)+Z^2*V*(Cupper*M^2/(N^4*U))*T^ε) ≤
      (Couter*(Cmesh^12*Cmesh^ε*(2*Ccard)^10)*Cv*(D+D*Cdelta+2*B*Cupper))*
        T^(2*ε)*L^10*
        (Y^11*M^11/(N*R^2)+Y^11*Jsep*M^11/N^3+
          Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) := by
  let m₁ := Y^11*M^11/(N*R^2)
  let m₂ := Y^11*Jsep*M^11/N^3
  let m₃ := Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)
  let Cmass := D+D*Cdelta+2*B*Cupper
  let Cpref := Cmesh^12*Cmesh^ε*(2*Ccard)^10
  have hm₁ : 0 ≤ m₁ := by dsimp only [m₁]; positivity
  have hm₂ : 0 ≤ m₂ := by dsimp only [m₂]; positivity
  have hm₃ : 0 ≤ m₃ := by dsimp only [m₃]; positivity
  have hDc := mul_nonneg hD hCd
  have hUc : 0 ≤ 2*B*Cupper := by positivity
  have hDmass : D ≤ Cmass :=
    (le_add_of_nonneg_right hDc).trans (le_add_of_nonneg_right hUc)
  have hDcmass : D*Cdelta ≤ Cmass :=
    (le_add_of_nonneg_left hD).trans (le_add_of_nonneg_right hUc)
  have hUcmass : 2*B*Cupper ≤ Cmass := le_add_of_nonneg_left (add_nonneg hD hDc)
  have hWeighted : D*m₁+D*Cdelta*m₂+2*B*Cupper*m₃ ≤ Cmass*(m₁+m₂+m₃) := by
    calc
      _ ≤ Cmass*m₁+Cmass*m₂+Cmass*m₃ :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_right hDmass hm₁)
          (mul_le_mul_of_nonneg_right hDcmass hm₂)) (mul_le_mul_of_nonneg_right hUcmass hm₃)
      _ = _ := by rw [mul_add, mul_add]
  have hCpref : 0 ≤ Cpref := by dsimp only [Cpref]; positivity
  have hraw := upper_selected_grid_family_bound
    hY hZ hZY hP hM hN hR hRQ hK hV hJ hD hCd hCu hCv hB hd hCm hT hε
    hQN hNR hNT hmesh hcard hVupper hdelta hUlower
  have hpref : 0 ≤ Cpref*T^(2*ε)*L^10*Cv :=
    mul_nonneg (mul_nonneg (mul_nonneg hCpref (Real.rpow_nonneg (zero_le_one.trans hT) _))
      (by positivity)) hCv
  calc
    _ = Couter*((R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10*
        (V*D*Z*(M/N)*(1+delta*Jsep)+Z^2*V*(Cupper*M^2/(N^4*U))*T^ε)) := by
      simp only [mul_assoc]
    _ ≤ Couter*(Cpref*T^(2*ε)*L^10*Cv*(D*m₁+D*Cdelta*m₂+2*B*Cupper*m₃)) :=
      mul_le_mul_of_nonneg_left hraw hCo
    _ ≤ Couter*(Cpref*T^(2*ε)*L^10*Cv*(Cmass*(m₁+m₂+m₃))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hWeighted hpref) hCo
    _ = _ := by
      change Couter*(Cpref*T^(2*ε)*L^10*Cv*(Cmass*(m₁+m₂+m₃))) =
        (Couter*Cpref*Cv*Cmass)*T^(2*ε)*L^10*(m₁+m₂+m₃)
      ac_rfl

private theorem eventually_upper_finite_numerical_consequence
    {σsrc csrc Usrc κ Cphys Csrc Couter CUP Dtype Bselect Csep ε : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) (hκ : 0 < κ)
    (hCphys : 0 ≤ Cphys) (hCsrcZero : 0 ≤ Csrc) (hCouter : 0 ≤ Couter)
    (hCUP : 0 ≤ CUP) (hDtype : 0 ≤ Dtype) (hBsOne : 1 ≤ Bselect)
    (hCsep : 1 ≤ Csep) (hε : 0 < ε) :
    let εloss := ε/4
    let Cmesh := 2*max 1 (63*Usrc/(2*σsrc))
    let CtailBand := (6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc
    let ClowBand := (3*Usrc/σsrc+csrc/(32*σsrc))*((3072*σsrc)/csrc)^2+(3072*σsrc)/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Y : Finset ℝ)
      (n N Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ) (R M Jsep : ℝ)
      (Chunks : Finset (ℝ × ℤ)) (band : (ℝ × ℤ) → Option ℕ)
      (Dcover : ℕ → Finset (ℝ × ℤ)) {S : ℝ},
      N=8*n → 2 ≤ N → 1 ≤ R → (N:ℝ) ≤ R^2 → (N:ℝ)^2 ≤ M →
      M ≤ T → 0 ≤ Jsep → T*(N:ℝ)*R^2=M^3 →
      0 < Qbase → (Qbase:ℝ) ≤ 1536*R → (N:ℝ)/Csep ≤ (Qbase*2^kmax:ℕ) →
      (kmax:ℝ) ≤ Real.log N/Real.log 2 → (∀ k, 0 < Kmesh k) →
      let Q := fun k : ℕ => Qbase*2^k
      (∀ k ≤ kmax,
        R ≤ (Q k:ℝ) ∧ Q k ≤ N ∧
        (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
        (Kmesh k:ℝ) ≤ Cmesh*(Q k:ℝ)*(N:ℝ)/R^2 ∧
        (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
        ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Usel k:ℝ)) →
      let Yc := (Y.card:ℝ)
      let μ₀ := csrc*T/(12*σsrc*M^3)
      let U₀ := Usrc*T/(2*σsrc*M^3)
      let Vscale := 1+R^4/(6*(N:ℝ)^2)
      let Error := Yc*(M/(N:ℝ)+1)*
        (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
      let Δtype := fun k : ℕ =>
        (16*U₀/μ₀)*Real.sqrt (U₀*(Q k:ℝ)^3)*Real.sqrt (Kmesh k)/(6*(Kmesh k:ℝ)^2)
      let Buffer := fun k : ℕ =>
        (56*(Usel k:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
      let Width := fun k : ℕ => (14*σsrc/csrc)*(Usel k:ℝ)*(N:ℝ)
      let FamilyBound := fun (k : ℕ) (P : Finset (ℝ × ℤ)) =>
        Couter*(R^2/(Q k:ℝ))^6*(Kmesh k:ℝ)^((12:ℝ)+εloss)*(2*(P.card:ℝ))^10*
          (Vscale*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+(Δtype k)*Jsep)+
            ((P.image Prod.fst).card:ℝ)^2*Vscale*
              (CUP*M^2/((N:ℝ)^4*(Usel k:ℝ)))*T^εloss)
      let Density := fun k => 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
        (2+Real.log (512*σsrc*R^2/(csrc*((Q k:ℝ)/768))+1))
      let Endpoint := Yc*(2*Buffer 0+2*Width 0+6*(N:ℝ)+2*(n:ℝ))
      let Selected := fun k => Chunks.filter (fun p => band p=some k)
      let Grid := fun (k : ℕ) (r : ℤ) =>
        ((Dcover k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
      (Chunks.card:ℝ) ≤ Yc*(8*M/(N:ℝ)) →
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤ Yc*Density k) →
      (∀ k ≤ kmax, ∀ r : ℤ, (Grid k r).card ≤ 2*(Selected k).card) →
      (∀ k ≤ kmax, ∀ r : ℤ, (Grid k r).image Prod.fst ⊆ Y) →
      S ≤ 2^11*(((kmax:ℝ)+2)^11*
        (((n:ℝ)*Yc*Density kmax)^12+
          (4:ℝ)^12*(8:ℝ)^11*∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,
            (2^11*((Csrc*Error)^12+
              (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (Grid k r))))+Endpoint^12) →
      let ErrorTotal := Yc*M/Real.sqrt (N:ℝ)+Yc*M*R^2/(N:ℝ)^2+
        Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
      let Main := Yc^11*M^11/((N:ℝ)*R^2)+Yc^11*Jsep*M^11/(N:ℝ)^3+
        Yc^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
      S ≤ T^ε*(ErrorTotal^12+Main) := by

  classical
  intro εloss Cmesh CtailBand ClowBand CerrorBand
  have hεloss : 0 < εloss := by dsimp only [εloss]; linarith only [hε]
  have hBs : 0 < Bselect := zero_lt_one.trans_le hBsOne
  let Carg := 512*768*σsrc/csrc
  let DensityLog := 3+Real.log (Carg+1)
  let Cdensity := 128*CerrorBand*DensityLog
  let Ccard := 16*(1536:ℝ)^2+8*Cdensity
  let CKlog := 3+Real.log (Cmesh+1)
  let Cband := 2+1/Real.log 2
  let Cdelta := (16*Usrc/csrc)*Real.sqrt ((Usrc/(2*σsrc))*Cmesh)
  let Cmass := Dtype+Dtype*Cdelta+2*Bselect*CUP
  let Cfamily := Couter*
    (Cmesh^12*Cmesh^εloss*(2*Ccard)^10)*(7/6:ℝ)*Cmass
  let CE₀ := 2*Real.sqrt 3*(1+Real.log 6)+24*σsrc/csrc
  let Cterminal := Cdensity*Csep^2/8
  let Cendpoint := 112/κ+28*σsrc/csrc+2/(Cphys+2)+41/4
  let Cerror := 1+Csrc*CE₀+Cterminal+Cendpoint
  let Cgrid := (2:ℝ)^11*(Cerror^12+(Csrc*CKlog)^12*Cfamily)
  let Ctotal := (2:ℝ)^11*(Cband^11*Cerror^12+
    (4:ℝ)^12*(8:ℝ)^12*Cband^12*Cgrid+Cerror^12)
  have hConstants :
      0 ≤ CtailBand ∧ 0 ≤ ClowBand ∧ 0 ≤ CerrorBand ∧ 1 ≤ Cmesh ∧
      0 ≤ Carg ∧ 0 ≤ DensityLog ∧ 0 ≤ Cdensity ∧ 0 ≤ Ccard ∧
      0 ≤ CKlog ∧ 0 ≤ Cband ∧ 0 ≤ Cdelta ∧ 0 ≤ Cmass ∧
      0 ≤ Cfamily ∧ 0 ≤ CE₀ ∧ 0 ≤ Cterminal ∧ 0 ≤ Cendpoint ∧
      0 ≤ Cerror ∧ Csrc*CE₀ ≤ Cerror ∧ Cterminal ≤ Cerror ∧
      Cendpoint ≤ Cerror ∧ 0 ≤ Cgrid ∧ 0 ≤ Ctotal :=
    upper_numerical_constants_nonnegative (ε:=ε) hσsrc hcsrc hUsrc hκ hCphys hCsrcZero
      hCouter hCUP hDtype hBsOne hCsep
  obtain ⟨hCtailBand,hClowBand,hCerrorBand,hCmeshOne,hCarg,hDensityLog,hCdensity,hCcard,hCKlog,hCband,hCdelta,hCmass,hCfamily,hCE₀,hCterminal,hCendpoint,hCerror,hErrorCompletion,hErrorTerminal,hErrorEndpoint,hCgrid,hCtotal⟩ :=
    hConstants
  have hCmesh : 0 < Cmesh := zero_lt_one.trans_le hCmeshOne
  filter_upwards [eventually_selected_band_logarithmic_absorption hCtotal hε,
    Filter.eventually_ge_atTop (1:ℝ)] with T hAbs hTone
  intro Y n N Qbase kmax Kmesh Usel R M Jsep Chunks band Dcover S
    hNlink hNtwo hR hNR' hNsqM hMT hJsep hscale hQbase hBaseHi hEndLo hkmax hKpos
    Q hvalid Yc μ₀ U₀ Vscale Error Δtype Buffer Width FamilyBound Density Endpoint Selected Grid
    hChunks hBands hGridCount hGridImage hNorm ErrorTotal Main
  have hT : 0 < T := hAbs.1
  have hLogOne : 1 ≤ Real.log T := hAbs.2.1
  have hNreal : (2:ℝ) ≤ N := by exact_mod_cast hNtwo
  have hNp : (0:ℝ) < N := by linarith only [hNreal]
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hNOne : (1:ℝ) ≤ N := by linarith only [hNreal]
  have hM : 0 < M := (sq_pos_of_pos hNp).trans_le hNsqM
  have hNM : (N:ℝ) ≤ M :=
    (by nlinarith only [hNreal] : (N:ℝ) ≤ (N:ℝ)^2).trans hNsqM
  have hNT : (N:ℝ) ≤ T := hNM.trans hMT
  have hVscale : 1 ≤ Vscale := by
    have hh : 0 ≤ R^4/(6*(N:ℝ)^2) := by positivity
    dsimp only [Vscale]
    linarith only [hh]
  let L := 1+Real.log T
  have hL : 1 ≤ L := by dsimp only [L]; linarith only [hLogOne]
  have hLzero : 0 ≤ L := zero_le_one.trans hL
  have hYc : 0 ≤ Yc := Nat.cast_nonneg _
  have hMain : 0 ≤ Main :=
    add_nonneg
      (add_nonneg
        (div_nonneg (mul_nonneg (pow_nonneg hYc 11) (pow_nonneg hM.le 11))
          (mul_nonneg hNp.le (sq_nonneg R)))
        (div_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hYc 11) hJsep)
          (pow_nonneg hM.le 11)) (pow_nonneg hNp.le 3)))
      (mul_nonneg
        (div_nonneg (mul_nonneg (pow_nonneg hYc 12) (pow_nonneg hM.le 12))
          (mul_nonneg (pow_nonneg hNp.le 4) (sq_nonneg R)))
        (Real.rpow_pos_of_pos (div_pos hRp hNp) _).le)
  have hErrorTotal : 0 ≤ ErrorTotal :=
    add_nonneg
      (add_nonneg (div_nonneg (mul_nonneg hYc hM.le) (Real.sqrt_nonneg _))
        (div_nonneg (mul_nonneg (mul_nonneg hYc hM.le) (sq_nonneg R))
          (sq_nonneg (N:ℝ))))
      (mul_nonneg (mul_nonneg hYc hNp.le)
        (Real.rpow_pos_of_pos (div_pos hNp hRp) _).le)
  have hQpos (k : ℕ) : (0:ℝ) < Q k := by
    exact_mod_cast Nat.mul_pos hQbase (by positivity : 0 < 2^k)
  have hKreal (k : ℕ) : (0:ℝ) < Kmesh k := by exact_mod_cast hKpos k
  have hlogs (k : ℕ) (hk : k ≤ kmax) :
      2+Real.log (Carg*R^2/(Q k:ℝ)+1) ≤ DensityLog*L ∧
      1+Real.log (Kmesh k) ≤ CKlog*L ∧
      (kmax:ℝ)+2 ≤ Cband*L := by
    obtain ⟨hRQ,hQN,_,hKU,_,_⟩ := hvalid k hk
    have hQNreal : (Q k:ℝ) ≤ N := by exact_mod_cast hQN
    exact physical_band_logarithmic_bounds hCarg hCmeshOne hTone hR hRQ
      hQNreal hNR' hNT (hKreal k) hKU hkmax
  have hDensity (k : ℕ) (hk : k ≤ kmax) :
      Density k ≤ Cdensity*M*R^2/((N:ℝ)*(Q k:ℝ)^2)*L := by
    have harg : 512*σsrc*R^2/(csrc*((Q k:ℝ)/768))=Carg*R^2/(Q k:ℝ) := by
      dsimp only [Carg]
      field_simp [(hQpos k).ne']
    calc
      _ = 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
          (2+Real.log (Carg*R^2/(Q k:ℝ)+1)) := by
        dsimp only [Density]
        rw [harg]
      _ ≤ 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*(DensityLog*L) :=
        mul_le_mul_of_nonneg_left (hlogs k hk).1 (by positivity)
      _ = _ := by dsimp only [Cdensity]; ring
  have hBandCounts (k : ℕ) (hk : k ≤ kmax) :
      ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        Yc*(Cdensity*M*R^2/((N:ℝ)*(Q k:ℝ)^2)*L) :=
    (hBands k hk).trans (mul_le_mul_of_nonneg_left (hDensity k hk) hYc)
  have hGridCard (k : ℕ) (hk : k ≤ kmax) (r : ℤ) :
      ((Grid k r).card:ℝ) ≤ Ccard*Yc*M*R^2/((N:ℝ)*(Q k:ℝ)^2)*L := by
    exact selected_band_grid_cardinality_bound Chunks band Grid Qbase kmax hQbase
      hYc hM.le hNp hCdensity hL hBaseHi hChunks hBandCounts
      hGridCount k hk r
  have hGridPhase (k : ℕ) (hk : k ≤ kmax) (r : ℤ) :
      (((Grid k r).image Prod.fst).card:ℝ) ≤ Yc := by
    change (((Grid k r).image Prod.fst).card:ℝ) ≤ (Y.card:ℝ)
    exact_mod_cast Finset.card_le_card (hGridImage k hk r)
  have hDeltaType (k : ℕ) (hk : k ≤ kmax) :
      Δtype k ≤ Cdelta*R^2/(N:ℝ)^2 := by
    obtain ⟨_,_,hMesh,hKU,_,_⟩ := hvalid k hk
    exact positive_difference_source_type_spacing_bound hσsrc hcsrc hUsrc.le
      hT hM hNp hRp (hQpos k) (hKreal k) hCmesh.le hscale hMesh hKU
  have hVupper : Vscale ≤ (7/6:ℝ)*R^4/(N:ℝ)^2 := by
    obtain ⟨_,_,hv,_⟩ := positive_difference_source_physical_regime_coefficients
      hσsrc hcsrc hUsrc hκ hT hM hNp hRp hscale hNR' hNsqM
    exact hv

  have hFamily (k : ℕ) (hk : k ≤ kmax) (r : ℤ) :
      FamilyBound k (Grid k r) ≤ Cfamily*T^(2*εloss)*L^10*Main := by
    obtain ⟨hRQ,hQN,_,hKU,_,hUlower⟩ := hvalid k hk
    have hQNreal : (Q k:ℝ) ≤ N := by exact_mod_cast hQN
    have hdeltazero : 0 ≤ Δtype k := by dsimp only [Δtype,U₀,μ₀]; positivity
    exact upper_selected_grid_family_total_bound
      hYc (Nat.cast_nonneg ((Grid k r).image Prod.fst).card) (hGridPhase k hk r)
      (Nat.cast_nonneg (Grid k r).card) hM.le hNp hRp hRQ (hKreal k)
      (zero_le_one.trans hVscale) hJsep hDtype hCdelta hCUP
      (show (0:ℝ) ≤ 7/6 by norm_num) hBs hdeltazero hCmesh hTone hεloss.le hCouter
      hQNreal hNR' hNT hKU (hGridCard k hk r) hVupper (hDeltaType k hk) hUlower
  let E₁ := Yc*M/Real.sqrt (N:ℝ)
  let E₂ := Yc*M*R^2/(N:ℝ)^2
  let E₃ := Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
  have hE₁ : 0 ≤ E₁ := div_nonneg (mul_nonneg hYc hM.le) (Real.sqrt_nonneg _)
  have hE₂ : 0 ≤ E₂ := div_nonneg (mul_nonneg (mul_nonneg hYc hM.le) (sq_nonneg R))
    (sq_nonneg (N:ℝ))
  have hE₃ : 0 ≤ E₃ := mul_nonneg (mul_nonneg hYc hNp.le)
    (Real.rpow_pos_of_pos (div_pos hNp hRp) _).le
  have hE₁₂Total : E₁+E₂ ≤ ErrorTotal := le_add_of_nonneg_right hE₃
  have hE₂Total : E₂ ≤ ErrorTotal := (le_add_of_nonneg_left hE₁).trans hE₁₂Total
  have hE₃Total : E₃ ≤ ErrorTotal := le_add_of_nonneg_left (add_nonneg hE₁ hE₂)
  have hCompletion : Csrc*Error ≤ Cerror*ErrorTotal*L := by
    have hraw := positive_difference_completion_error_physical_bound
      (R:=R) hYc hNOne hNM hMT (show 0 ≤ 12*σsrc/csrc by positivity)
    have he : Error ≤ CE₀*(E₁+E₂)*L := by
      convert hraw using 1
      · dsimp only [Error]
        ring
      · dsimp only [CE₀,E₁,E₂,L]
        ring
    calc
      _ ≤ Csrc*(CE₀*(E₁+E₂)*L) := mul_le_mul_of_nonneg_left he hCsrcZero
      _ = (Csrc*CE₀)*(E₁+E₂)*L := by simp only [mul_assoc]
      _ ≤ Cerror*ErrorTotal*L :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hErrorCompletion hE₁₂Total (add_nonneg hE₁ hE₂) hCerror) hLzero
  have hNlinkReal : (N:ℝ)=8*(n:ℝ) := by exact_mod_cast hNlink
  have hTerminalBound : (n:ℝ)*Yc*Density kmax ≤ Cerror*ErrorTotal*L := by
    have hnzero : 0 ≤ (n:ℝ)*Yc := mul_nonneg (Nat.cast_nonneg n) hYc
    have hcore := selected_terminal_density_bound (R:=R) hNp hM.le hYc hCdensity
      (zero_lt_one.trans_le hCsep) hLzero hNlinkReal hEndLo
    calc
      _ ≤ (n:ℝ)*Yc*(Cdensity*M*R^2/((N:ℝ)*(Q kmax:ℝ)^2)*L) :=
        mul_le_mul_of_nonneg_left (hDensity kmax le_rfl) hnzero
      _ ≤ Cterminal*E₂*L := hcore
      _ ≤ Cerror*ErrorTotal*L :=
        mul_le_mul_of_nonneg_right (mul_le_mul hErrorTerminal hE₂Total hE₂ hCerror) hLzero
  have hEndpointBound : Endpoint ≤ Cerror*ErrorTotal*L := by
    obtain ⟨hRQ,hQN,_,_,hUupper,_⟩ := hvalid 0 (Nat.zero_le _)
    have hQNreal : (Q 0:ℝ) ≤ N := by exact_mod_cast hQN
    have hraw := positive_difference_endpoint_error_physical_bound
      hYc hNOne hRp hRQ hQNreal hκ hσsrc.le hcsrc hCphys hBsOne hNlinkReal hUupper
    have he : Endpoint ≤ Cendpoint*E₃ := by
      exact hraw
    calc
      _ ≤ Cendpoint*E₃ := he
      _ ≤ Cerror*ErrorTotal := mul_le_mul hErrorEndpoint hE₃Total hE₃ hCerror
      _ ≤ Cerror*ErrorTotal*L := le_mul_of_one_le_right (mul_nonneg hCerror hErrorTotal) hL

  have hLogN : 0 ≤ Real.log (6*(N:ℝ)) :=
    Real.log_nonneg (by linarith only [hNreal])
  have hCompletionZero : 0 ≤ Csrc*Error := by dsimp only [Error]; positivity
  have hDensityZero (k : ℕ) : 0 ≤ Density k := by
    have harg : 1 ≤ 512*σsrc*R^2/(csrc*((Q k:ℝ)/768))+1 := by
      have hh : 0 ≤ 512*σsrc*R^2/(csrc*((Q k:ℝ)/768)) := by positivity
      linarith only [hh]
    have hh := Real.log_nonneg harg
    dsimp only [Density]
    positivity
  have hTerminalZero : 0 ≤ (n:ℝ)*Yc*Density kmax :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hYc) (hDensityZero kmax)
  have hEndpointZero : 0 ≤ Endpoint := by dsimp only [Endpoint,Buffer,Width]; positivity
  have hTpowOne : 1 ≤ T^(2*εloss) :=
    Real.one_le_rpow hTone (mul_nonneg (by norm_num) hεloss.le)
  let G := fun k r => 2^11*((Csrc*Error)^12+
    (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (Grid k r))
  have hG (k : ℕ) (hk : k ≤ kmax) (r : ℤ) :
      G k r ≤ Cgrid*T^(2*εloss)*L^22*(ErrorTotal^12+Main) := by
    have hKone : (1:ℝ) ≤ Kmesh k := by
      have hh : 1 ≤ Kmesh k := Nat.succ_le_iff.mpr (hKpos k)
      exact_mod_cast hh
    have hlogK := Real.log_nonneg hKone
    have hLogZero : 0 ≤ Csrc*(1+Real.log (Kmesh k)) :=
      mul_nonneg hCsrcZero (add_nonneg zero_le_one hlogK)
    have hLogBound : Csrc*(1+Real.log (Kmesh k)) ≤ (Csrc*CKlog)*L := by
      calc
        _ ≤ Csrc*(CKlog*L) := mul_le_mul_of_nonneg_left (hlogs k hk).2.1 hCsrcZero
        _ = _ := by simp only [mul_assoc]
    exact selected_grid_completion_bound hCompletionZero hLogZero hMain hCfamily hL hTpowOne
      hCompletion hLogBound (hFamily k hk r)
  have hClean := selected_band_finite_power_cleanup kmax G
    hTerminalZero hEndpointZero hMain hL hTpowOne hCband hCgrid
    (hlogs 0 (Nat.zero_le _)).2.2 hTerminalBound hEndpointBound
    (fun k hk r _ => hG k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) r) hNorm
  have hExp : 2*εloss=ε/2 := by dsimp only [εloss]; ring
  have hFactor : Ctotal*T^(2*εloss)*L^36 ≤ T^ε := by
    simpa only [hExp,L] using hAbs.2.2
  exact hClean.trans (mul_le_mul_of_nonneg_right hFactor
    (add_nonneg (pow_nonneg hErrorTotal 12) hMain))

                                                                                    
                                                                                   
                                                                                
theorem eventually_upper_quantitative_phase_subinterval_bound
    {σsrc csrc Usrc σ δ ε : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hδzero : 0 ≤ δ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hε : 0 < ε)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    ∃ Cbudget η₀ : ℝ, 1 ≤ Cbudget ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (n N : ℕ) (R Jsep : ℝ) {η M : ℝ},
      N=8*n → 2 ≤ N → 1 ≤ R → 0 < η → η ≤ η₀ →
      0 < Jsep → Jsep ≤ M →
      (∀ y∈Y, y∈Icc (1:ℝ) 2) →
      (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j ≤ 6, |iteratedDeriv (j+1) Fsrc w| ≤ Usrc) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
      (∀ y∈Y, Expdb.IsApproximateModelPhaseFunction
        (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
      T*(N:ℝ)*R^2=M^3 →
      Cbudget*R ≤ N → Cbudget*(N:ℝ) ≤ R^2 → Cbudget*(N:ℝ)^2 ≤ M →
      (N:ℝ)^4 ≤ M*R^3 → (N:ℝ)^10 ≤ M^3*R^7 →
      ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
      (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
      let Yc := (Y.card:ℝ)
      let ErrorTotal := Yc*M/Real.sqrt (N:ℝ)+Yc*M*R^2/(N:ℝ)^2+
        Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
      let Main := Yc^11*M^11/((N:ℝ)*R^2)+
        Yc^11*Jsep*M^11/(N:ℝ)^3+
        Yc^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),
        (𝐞 (T*(Fsrc ((j:ℝ)/M)-Fsrc ((j:ℝ)/M+η*y))/(σsrc*η)):ℂ)‖)^12 ≤
        T^ε*(ErrorTotal^12+Main) := by

  classical
  let εloss := ε/4
  have hεloss : 0 < εloss := by dsimp only [εloss]; linarith only [hε]
  let κ := modelPhaseThirdLower σ
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
  let Lsource := max (8*Ratio^2)
    (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
  have hLsource : 0 ≤ Lsource :=
    (by positivity : (0:ℝ) ≤ 8*Ratio^2).trans (le_max_left _ _)
  let θ := min (1/48:ℝ) (1/(16*(Lsource+3)))
  have hθ : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθmax : θ ≤ 1/24 := (min_le_left _ _).trans (by norm_num)
  have hθaction : θ ≤ 1/(8*(Lsource+3)) := by
    apply (min_le_right _ _).trans
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (by nlinarith only [hLsource])
  obtain ⟨Csrc,η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,hfinite⟩ :=
    eventually_positive_difference_triangular_selected_band_phase_subinterval_physical_sieve
      hσsrc hcsrc hUsrc hσ hεloss hanchorBudget
  let Cphys := σ*(σ+1)+1
  let c := κ/6
  let J := Cphys/6
  let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hc : 0 < c := by dsimp only [c]; positivity
  have hJ : 0 < J := by dsimp only [J]; positivity
  have hB : 1 ≤ B := le_max_left _ _
  have hBzero : 0 ≤ B := zero_le_one.trans hB
  let C₂ := modelPhaseJetCoefficient σ 2+δ
  let C₃ := modelPhaseJetCoefficient σ 3+δ
  let Ct := C₂/2+5*C₃/12
  let Cc := C₂/κ+C₃/(2*κ)
  have hC₂ : 0 ≤ C₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδzero
  have hC₃ : 0 ≤ C₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδzero
  have hC₄ : 0 ≤ modelPhaseJetCoefficient σ 4+δ :=
    add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδzero
  have hCR : 0 ≤ quarticReciprocalConstant σ δ := by
    dsimp only [quarticReciprocalConstant]
    positivity
  have hCN : 0 ≤ quarticNonlinearResidualConstant σ δ := by
    dsimp only [quarticNonlinearResidualConstant]
    positivity
  have hCt : 0 ≤ Ct := by dsimp only [Ct]; positivity
  have hCc : 0 ≤ Cc := by dsimp only [Cc]; positivity
  let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
  let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
    2*quarticNonlinearResidualConstant σ δ)/κ
  let Esize := κ/(16*(Cphys+2))
  let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
  let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
  let Lunit := 2*κ/Cphys
  let Gamma := Cphys/κ
  let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
  have hCcurv : 0 ≤ Ccurv := by dsimp only [Ccurv]; positivity
  have hKres : 0 ≤ Kres := by dsimp only [Kres]; positivity
  have hEsize : 0 < Esize := by dsimp only [Esize]; positivity
  have hDbase : 0 ≤ Dbase := by dsimp only [Dbase]; positivity
  have hTbase : 0 ≤ Tbase := by dsimp only [Tbase]; positivity
  have hLunit : 0 < Lunit := by dsimp only [Lunit]; positivity
  have hGamma : 0 < Gamma := by dsimp only [Gamma]; positivity
  have hCthird : 0 ≤ Cthird := by dsimp only [Cthird]; positivity
  let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
  let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
  let DupperConst := θ*(3*Usrc/σsrc)*1/2
  have hAupper : 0 ≤ AupperConst := by dsimp only [AupperConst]; positivity
  have hBupper : 0 ≤ BupperConst := by dsimp only [BupperConst]; positivity
  have hDupper : 0 ≤ DupperConst := by dsimp only [DupperConst]; positivity
  let Sector := 2*3840*128^2*105*(Dbase+64*Tbase*Esize^2)
  obtain ⟨Bcut,Bselect,hBcut,hBsOne,hBsSize,hcutMargin,hsize,hBsize⟩ :=
    exists_source_cutoff_margins (Sector:=Sector) hκ hCcurv hCphys.le hEsize
  have hBs : 0 < Bselect := zero_lt_one.trans_le hBsOne
  let D₀ := 37*B/2+16*B*Cc+2*Ct+2*Cc
  have hD₀ : 0 ≤ D₀ := by dsimp only [D₀]; positivity
  obtain ⟨Csep,hCsep,hselect⟩ :=
    exists_uniform_dyadic_band_integer_scales (J:=Usrc) hσsrc hBsOne hD₀ hCN
  obtain ⟨Cbudget,hCbudget,hCsepBudget,hbudget⟩ :=
    exists_uniform_source_physical_budget (zero_le_one.trans hCsep)
      (show 0 ≤ 3*Usrc/σsrc by positivity)
      (show 0 ≤ 3*Usrc/(4*σsrc) by positivity) hBzero
      (show 0 ≤ 56/κ by positivity)
      (show 0 ≤ 1/(Cphys+2) by positivity)
      (show 0 ≤ 14*σsrc/csrc by positivity)

  let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
  let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
  let Cap := 3*ChartCap*NarrowCap
  have hChartCap : 0 ≤ ChartCap := by dsimp only [ChartCap]; positivity
  have hNarrowCap : 0 ≤ NarrowCap := by dsimp only [NarrowCap]; positivity
  have hCap : 0 ≤ Cap := by dsimp only [Cap]; positivity
  let CUP := 240*(9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+
    2*BupperConst+(3/2:ℝ)*DupperConst)
  have hCUP : 0 ≤ CUP := by dsimp only [CUP]; positivity
  let Couter := (48*σsrc/csrc)^6*C*Cap^11
  have hCouter : 0 ≤ Couter := by dsimp only [Couter]; positivity
  let CtailBand := (6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc
  let ClowBand := (3*Usrc/σsrc+csrc/(32*σsrc))*((3072*σsrc)/csrc)^2+(3072*σsrc)/csrc
  let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
  have hNumeric := eventually_upper_finite_numerical_consequence
    hσsrc hcsrc hUsrc hκ hCphys.le (zero_le_one.trans hCsrc)
    hCouter hCUP hDtype.le hBsOne hCsep hε
  have hLog : ∀ᶠ T : ℝ in Filter.atTop, 1 ≤ Real.log T :=
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop 1)
  refine ⟨Cbudget,η₀,hCbudget,hη₀,hηcap,?_⟩
  filter_upwards [hfinite hθ hθmax hθaction,hNumeric,
    Filter.eventually_ge_atTop (1:ℝ),hLog] with T hfiniteT hNumericT hTone hLogOne
  intro Fsrc Y n N R Jsep η M hNlink hNtwo hR hη hηsmall hJsep hJM
    hy hsepY hreg hjets htests hnegative hmodels hscale
    hSepBudget hRadiusBudget hSquareBudget hNfour hNten A Bint hA hAB hBint
    Yc ErrorTotal Main
  have hT : 0 < T := zero_lt_one.trans_le hTone
  have hNreal : (2:ℝ) ≤ N := by exact_mod_cast hNtwo
  have hNp : (0:ℝ) < N := by linarith only [hNreal]
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hNOne : (1:ℝ) ≤ N := by linarith only [hNreal]
  have hNR : (N:ℝ) ≤ R^2 :=
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hCbudget hNp.le :
      (N:ℝ) ≤ Cbudget*N).trans hRadiusBudget
  have hCsepRoom : Csep*R ≤ N :=
    (mul_le_mul_of_nonneg_right hCsepBudget hRp.le).trans hSepBudget
  obtain ⟨Qbase,kmax,Kmesh,Usel,hBaseLo,hBaseHi,hEndLo,hEndHi,hkmax,hKpos,hvalid,hUmono⟩ :=
    hselect N R hR hNR hCsepRoom
  let Q := fun k : ℕ => Qbase*2^k
  have hUzero : (Usel 0:ℝ) ≤ N := by
    obtain ⟨_,_,_,_,_,_,hUupper,_,_,_,hQstrong,_,_,_⟩ := hvalid 0 (Nat.zero_le _)
    have hQone : (1:ℝ) ≤ Q 0 := by nlinarith only [hQstrong,hR]
    have hQzero : (0:ℝ) < Q 0 := zero_lt_one.trans_le hQone
    calc
      _ ≤ ((N:ℝ)/(Q 0:ℝ))^((2:ℝ)/3)/Bselect := hUupper
      _ ≤ ((N:ℝ)/(Q 0:ℝ))^((2:ℝ)/3) := div_le_self (by positivity) hBsOne
      _ ≤ (N:ℝ)^((2:ℝ)/3) := Real.rpow_le_rpow (by positivity)
        (div_le_self hNp.le hQone) (by norm_num)
      _ ≤ N := Real.rpow_le_self_of_one_le hNOne (by norm_num)
  obtain ⟨hM,hRN,hNR',hNsqM,hNRM,hNcube,hRM,hpad,hquartic,hquadratic,hsmall,hroom,hMTall⟩ :=
    hbudget (N:ℝ) R M (Usel 0:ℝ) hNreal hR hSepBudget hRadiusBudget hSquareBudget hUzero
  have hMT : M ≤ T := hMTall T hT hscale
  have hNM : (N:ℝ) ≤ M :=
    (by nlinarith only [hNreal] : (N:ℝ) ≤ (N:ℝ)^2).trans hNsqM
  have hNT : (N:ℝ) ≤ T := hNM.trans hMT
  have hRegimeLog : (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) :=
    hNfour.trans (le_mul_of_one_le_right (by positivity)
      (Real.one_le_rpow hLogOne (by norm_num)))
  let Vscale := 1+R^4/(6*(N:ℝ)^2)
  have hVscale : 1 ≤ Vscale := by
    have hh : 0 ≤ R^4/(6*(N:ℝ)^2) := by positivity
    dsimp only [Vscale]
    linarith only [hh]

  let μ₀ := csrc*T/(12*σsrc*M^3)
  let U₀ := Usrc*T/(2*σsrc*M^3)
  let Error := Yc*(M/(N:ℝ)+1)*
    (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
  let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
  let Δtype := fun k : ℕ =>
    (16*U₀/μ₀)*Real.sqrt (U₀*(Q k:ℝ)^3)*Real.sqrt (Kmesh k)/(6*(Kmesh k:ℝ)^2)
  let Δ := fun k : ℕ => D₀*(Q k:ℝ)/(N:ℝ)
  let D := fun k : ℕ =>
    Δ k+quarticNonlinearResidualConstant σ δ*(2*(Q k:ℝ))/(N:ℝ)
  let Kupper := fun k : ℕ =>
    240*(M^2/((N:ℝ)^4*(Usel k:ℝ)))*
      (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
  let Buffer := fun k : ℕ =>
    (56*(Usel k:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
  let Width := fun k : ℕ => (14*σsrc/csrc)*(Usel k:ℝ)*(N:ℝ)
  let FamilyBound := fun (k : ℕ) (P : Finset (ℝ × ℤ)) =>
    (48*σsrc/csrc)^6*(R^2/(Q k:ℝ))^6*
      C*(Kmesh k:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*
        (Vscale*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+(Δtype k)*Jsep)+
          ((P.image Prod.fst).card:ℝ)^2*Vscale*(Kupper k)*T^εloss)
  let Density := fun k => 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
    (2+Real.log (512*σsrc*R^2/(csrc*((Q k:ℝ)/768))+1))
  let Endpoint := Yc*(2*Buffer 0+2*Width 0+6*(N:ℝ)+2*(n:ℝ))
  have hvalidTri : ∀ k ≤ kmax,
      12*Usrc ≤ σsrc*(Usel k:ℝ) ∧
      63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      1 ≤ Usel k ∧ Bselect^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
      (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      Q k ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
      768*R ≤ (Q k:ℝ) ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
      D k ≤ 1/2 ∧ Δ k < 1/2 := by
    intro k hk
    obtain ⟨hUL,hSource,hMesh,_,hU,hWrap,hUpper,_,hQN,hUR,hStrong,hMin,hD,hDelta⟩ :=
      hvalid k hk
    exact ⟨hUL,hSource,hMesh,hU,hWrap,hUpper,hQN,hUR,hStrong,hMin,hD,hDelta⟩
  have hRoom : 2*(Buffer 0+Width 0)+6*(N:ℝ) ≤ M := by
    convert hroom using 1
    dsimp only [Buffer,Width]
    ring
  obtain ⟨Chunks,band,Dcover,hChunks,hBands,hTerminal,hGrids,hNorm⟩ :=
    hfiniteT Fsrc Y n N Qbase kmax Kmesh Usel R Jsep Vscale true
      (η:=η) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
      hKpos hNlink hη hηsmall hT hNtwo hR hRM hVscale hδzero hδ hJsep hJM
      hy hsepY hreg hjets htests hnegative hmodels hscale hpad hquartic hquadratic
      hRegimeLog hBcut hBsSize hcutMargin hNten hNsqM hNRM
      (by rfl) hsmall hNR' hRN hNcube hsize hBsize hvalidTri
      (fun k _ => hUmono k) hRoom A Bint hA hAB hBint
  let Selected := fun k => Chunks.filter (fun p => band p=some k)
  let Grid := fun (k : ℕ) (r : ℤ) =>
    ((Dcover k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
  let NumericFamily := fun (k : ℕ) (P : Finset (ℝ × ℤ)) =>
    Couter*(R^2/(Q k:ℝ))^6*(Kmesh k:ℝ)^((12:ℝ)+εloss)*(2*(P.card:ℝ))^10*
      (Vscale*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+(Δtype k)*Jsep)+
        ((P.image Prod.fst).card:ℝ)^2*Vscale*
          (CUP*M^2/((N:ℝ)^4*(Usel k:ℝ)))*T^εloss)
  have hQbaseReal : (0:ℝ) < Qbase := by nlinarith only [hBaseLo,hRp]
  have hQbase : 0 < Qbase := by exact_mod_cast hQbaseReal
  have hvalidNumeric : ∀ k ≤ kmax,
      R ≤ (Q k:ℝ) ∧ Q k ≤ N ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      (Kmesh k:ℝ) ≤ (2*max 1 (63*Usrc/(2*σsrc)))*(Q k:ℝ)*(N:ℝ)/R^2 ∧
      (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Usel k:ℝ) := by
    intro k hk
    obtain ⟨_,_,hMesh,hKU,_,_,hUpper,hLower,hQN,_,hStrong,_,_,_⟩ := hvalid k hk
    exact ⟨by nlinarith only [hStrong,hRp],hQN,hMesh,hKU,hUpper,hLower⟩
  have hKupper (k : ℕ) : Kupper k=CUP*M^2/((N:ℝ)^4*(Usel k:ℝ)) := by
    dsimp only [Kupper,CUP]
    simp only [div_eq_mul_inv]
    ac_rfl
  have hFamilyEq (k : ℕ) (P : Finset (ℝ × ℤ)) :
      FamilyBound k P=NumericFamily k P := by
    dsimp only [FamilyBound,NumericFamily]
    rw [hKupper]
    dsimp only [Couter]
    ac_rfl
  let S := (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y), (𝐞 (f y j):ℂ)‖)^12
  change S ≤ 2^11*(((kmax:ℝ)+2)^11*
    (((n:ℝ)*Yc*Density kmax)^12+
      (4:ℝ)^12*(8:ℝ)^11*∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,
        (2^11*((Csrc*Error)^12+
          (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (Grid k r))))+Endpoint^12) at hNorm
  simp only [hFamilyEq] at hNorm
  exact hNumericT Y n N Qbase kmax Kmesh Usel R M Jsep Chunks band Dcover
    hNlink hNtwo hR hNR' hNsqM hMT hJsep.le hscale hQbase hBaseHi hEndLo hkmax hKpos
    hvalidNumeric hChunks hBands
    (fun k hk r => (hGrids k hk).2.2.1 r)
    (fun k hk r => (hGrids k hk).2.2.2 r) hNorm


                                                         

                                                                           
                                                                          
                                                                   


open scoped BigOperators FourierTransform Classical ContDiff NNReal
open Filter

public  theorem upperOriginal_nonnegative_doubled_block_selection
    (f : ℕ → ℝ) (H : ℕ) (hH : 2 ≤ H) (hf₀ : f 0=0)
    (hf : ∀ n, 0 ≤ f n) {A : ℝ} (hA : 0 ≤ A)
    (hcap : ∀ n < H, f n ≤ A) :
    ∃ k : ℕ, 0 < k ∧ 2*k ≤ H ∧
      (∑ n∈Finset.range H,f n) ≤
        (Nat.clog 2 H:ℝ)*(A+∑ j∈Finset.range k,f (k+j)) := by
  classical
  obtain ⟨k,hk,hmax⟩ := (Finset.Icc 1 (H/2)).exists_max_image
    (fun k => ∑ j∈Finset.range k,f (k+j))
    (by exact ⟨1,Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩⟩)
  have hk' := Finset.mem_Icc.mp hk
  have hnorm (s : Finset ℕ) (g : ℕ → ℕ) :
      ‖∑ j∈s,(f (g j):ℂ)‖=∑ j∈s,f (g j) := by
    rw [←Complex.ofReal_sum]
    exact Complex.norm_of_nonneg (Finset.sum_nonneg (fun j _ => hf (g j)))
  have hbound := norm_prefix_le_doubled_blocks
    (fun n => (f n:ℂ)) H (Nat.clog 2 H) H
    (congrArg (fun x : ℝ => (x:ℂ)) hf₀) le_rfl (Nat.le_pow_clog (by norm_num) H)
    A (∑ j∈Finset.range k,f (k+j)) hA
    (Finset.sum_nonneg (fun j _ => hf (k+j)))
    (fun n hn => (Complex.norm_of_nonneg (hf n)).le.trans (hcap n hn))
    (fun l hl hlH => by
      rw [hnorm (Finset.range l) (fun j => l+j)]
      exact hmax l (Finset.mem_Icc.mpr ⟨by omega,by omega⟩))
  have he : ‖∑ n∈Finset.range H,(f n:ℂ)‖ = ∑ n∈Finset.range H,f n :=
    hnorm (Finset.range H) id
  rw [he] at hbound
  exact ⟨k,by omega,by omega,hbound⟩

private theorem upperOriginal_norm_sourceShiftCorrelation_le_length
    (F : ℝ → ℝ) (X M : ℝ) (a L r : ℕ) :
    ‖sourceShiftCorrelation F X M a L r‖ ≤ (L:ℝ)+1 := by
  unfold sourceShiftCorrelation
  calc
    _ ≤ ∑ j∈Finset.range (L+1-r),
        ‖star (Expdb.oscillatory F X M ((a:ℝ)+j))*
          Expdb.oscillatory F X M ((a:ℝ)+j+r)‖ := norm_sum_le _ _
    _ = (L+1-r:ℕ) := by simp
    _ ≤ (L:ℝ)+1 := by exact_mod_cast (Nat.sub_le (L+1) r)

private theorem upperOriginal_weyl_prefix_twenty_fourth_power
    {S All B M H L C : ℝ} (hM : 0 < M) (hH : 0 < H)
    (hAll : 0 ≤ All) (hB : 0 ≤ B) (hL : 0 ≤ L) (hC : 1 ≤ C)
    (hLM : L ≤ 2*M) (hHM : H ≤ M)
    (hWeyl : H^2*S^2 ≤ (L+H)*(H*L+2*H*All))
    (hPrefix : All ≤ C*(L+B)) :
    S^24 ≤ (18:ℝ)^12*(2:ℝ)^11*C^12*
      ((M^2/H)^12+(M/H)^12*B^12) := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hRight : 0 ≤ H*L+2*H*All := by positivity
  have hAllBound : All ≤ C*(2*M+B) :=
    hPrefix.trans (mul_le_mul_of_nonneg_left (add_le_add hLM le_rfl) hC0)
  have hraw : H^2*S^2 ≤ 18*H*C*(M^2+M*B) := by
    calc
      _ ≤ (L+H)*(H*L+2*H*All) := hWeyl
      _ ≤ (3*M)*(H*L+2*H*All) :=
        mul_le_mul_of_nonneg_right (by linarith only [hLM,hHM]) hRight
      _ ≤ (3*M)*(2*H*M+2*H*C*(2*M+B)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc
          _ ≤ H*(2*M)+2*H*(C*(2*M+B)) :=
            add_le_add (mul_le_mul_of_nonneg_left hLM hH.le)
              (mul_le_mul_of_nonneg_left hAllBound (by positivity))
          _ = _ := by ring
      _ ≤ _ := by
        nlinarith only [
          mul_nonneg (show 0 ≤ H*M^2 by positivity) (sub_nonneg.mpr hC),
          mul_nonneg (show 0 ≤ H*C*M by positivity) hB]
  have hSquare : S^2 ≤ 18*C*(M^2/H+(M/H)*B) := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hH)).mp
    calc
      _ ≤ 18*H*C*(M^2+M*B) := hraw
      _ = _ := by field_simp
  calc
    _ = (S^2)^12 := by ring
    _ ≤ (18*C*(M^2/H+(M/H)*B))^12 := pow_le_pow_left₀ (sq_nonneg S) hSquare 12
    _ = (18:ℝ)^12*C^12*(M^2/H+(M/H)*B)^12 := by ring
    _ ≤ (18:ℝ)^12*C^12*(2^11*((M^2/H)^12+((M/H)*B)^12)) :=
      mul_le_mul_of_nonneg_left (add_pow_le (by positivity) (by positivity) 12) (by positivity)
    _ = _ := by ring

private theorem upperOriginal_source_correlation_doubled_block
    (F : ℝ → ℝ) (X M : ℝ) (a L H : ℕ) (hH : 2 ≤ H) :
    ∃ k : ℕ, 0 < k ∧ 2*k ≤ H ∧
      (∑ r∈Finset.Icc 1 (H-1),‖sourceShiftCorrelation F X M a L r‖) ≤
        (Nat.clog 2 H:ℝ)*((L:ℝ)+1+
          ∑ j∈Finset.range k,‖sourceShiftCorrelation F X M a L (k+j)‖) := by
  classical
  let f := fun r : ℕ => if r=0 then 0 else ‖sourceShiftCorrelation F X M a L r‖
  have hf₀ : f 0=0 := by simp only [f,ite_eq_left rfl]
  have hf (r : ℕ) : 0 ≤ f r := by
    dsimp only [f]
    split_ifs
    · exact le_rfl
    · exact norm_nonneg _
  have hcap (r : ℕ) : f r ≤ (L:ℝ)+1 := by
    dsimp only [f]
    split_ifs
    · positivity
    · exact upperOriginal_norm_sourceShiftCorrelation_le_length F X M a L r
  obtain ⟨k,hk,hkH,hs⟩ := upperOriginal_nonnegative_doubled_block_selection f H hH hf₀ hf
    (show 0 ≤ (L:ℝ)+1 by positivity) (fun r _ => hcap r)
  have hfilt : (∑ r∈(Finset.range H).filter (fun r => 0<r),f r) =
      ∑ r∈Finset.range H,f r := by
    apply Finset.sum_filter_of_ne
    intro r _ hne
    by_contra hn
    have hr : r=0 := by omega
    subst r
    exact hne hf₀
  have hset : (Finset.range H).filter (fun r => 0<r) = Finset.Icc 1 (H-1) := by
    ext r
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Icc]
    omega
  have hall : (∑ r∈Finset.range H,f r) =
      ∑ r∈Finset.Icc 1 (H-1),‖sourceShiftCorrelation F X M a L r‖ := by
    rw [←hfilt,hset]
    apply Finset.sum_congr rfl
    intro r hr
    exact ite_eq_right (by have := (Finset.mem_Icc.mp hr).1; omega)
  have hblock : (∑ j∈Finset.range k,f (k+j)) =
      ∑ j∈Finset.range k,‖sourceShiftCorrelation F X M a L (k+j)‖ := by
    apply Finset.sum_congr rfl
    intro j _
    exact ite_eq_right (by omega)
  rw [hall,hblock] at hs
  exact ⟨k,hk,hkH,hs⟩

public  theorem upperOriginal_exists_source_dyadic_twenty_fourth_power
    (F : ℝ → ℝ) (X M : ℝ) (a L H : ℕ) (hM : 0 < M)
    (hH : 2 ≤ H) (hHM : (H:ℝ) ≤ M) (hLM : (L:ℝ)+1 ≤ 2*M) :
    ∃ k : ℕ, 0 < k ∧ 2*k ≤ H ∧
      ‖Expdb.exponentialSumAt F X M a (a+L)‖^24 ≤
        (18:ℝ)^12*(2:ℝ)^11*(Nat.clog 2 H:ℝ)^12*
          ((M^2/(H:ℝ))^12+(M/(H:ℝ))^12*
            (∑ j∈Finset.range k,‖sourceShiftCorrelation F X M a L (k+j)‖)^12) := by
  obtain ⟨k,hk,hkH,hs⟩ := upperOriginal_source_correlation_doubled_block F X M a L H hH
  have hHpos : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hclog : 1 ≤ Nat.clog 2 H := by
    have hh := Nat.le_pow_clog (by norm_num : 1<2) H
    by_contra hn
    have hz : Nat.clog 2 H=0 := by omega
    rw [hz,pow_zero] at hh
    omega
  have hC : (1:ℝ) ≤ Nat.clog 2 H := by exact_mod_cast hclog
  have hw := source_exponentialSum_weyl F X M a L H
  simp only [Nat.cast_add,Nat.cast_one] at hw
  exact ⟨k,hk,hkH,upperOriginal_weyl_prefix_twenty_fourth_power hM hHpos
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (by positivity) hC hLM hHM hw hs⟩

private theorem upperOriginal_exponentialSumAt_eq_int_Icc
    (F : ℝ → ℝ) (X M : ℝ) (a b : ℕ) :
    Expdb.exponentialSumAt F X M a b =
      ∑ j∈Finset.Icc (a:ℤ) (b:ℤ),Expdb.oscillatory F X M j := by
  unfold Expdb.exponentialSumAt
  apply Finset.sum_bij (fun (n:ℕ) _ => (n:ℤ))
  case hi =>
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hn'.1,by exact_mod_cast hn'.2⟩
  case i_inj =>
    intro n _ m _ hnm
    exact_mod_cast hnm
  case i_surj =>
    intro z hz
    have hz' := Finset.mem_Icc.mp hz
    have hz0 : 0≤z := (Int.natCast_nonneg a).trans hz'.1
    refine ⟨z.toNat,Finset.mem_Icc.mpr ⟨?_,?_⟩,Int.toNat_of_nonneg hz0⟩
    · omega
    · omega
  case h =>
    intro n _
    simp only [Int.cast_natCast]

public  theorem upperOriginal_norm_exponentialSumAt_le_int_Ioc
    (F : ℝ → ℝ) (X M : ℝ) (a b : ℕ) (hab : a≤b) :
    ‖Expdb.exponentialSumAt F X M a b‖ ≤
      1+‖∑ j∈Finset.Ioc (a:ℤ) (b:ℤ),Expdb.oscillatory F X M j‖ := by
  rw [upperOriginal_exponentialSumAt_eq_int_Icc,
    Finset.Icc_eq_cons_Ioc (by exact_mod_cast hab : (a:ℤ)≤b),Finset.sum_cons]
  simpa only [Expdb.norm_oscillatory] using
    norm_add_le (Expdb.oscillatory F X M (a:ℤ))
      (∑ j∈Finset.Ioc (a:ℤ) (b:ℤ),Expdb.oscillatory F X M j)

private theorem upperOriginal_norm_sourceShiftCorrelation_le_difference_Ioc
    (F : ℝ → ℝ) (X : ℝ) {M : ℝ} (hM : M≠0)
    (a L r k : ℕ) (hk : 0<k) (hrL : r≤L) :
    ‖sourceShiftCorrelation F X M a L r‖ ≤
      1+‖∑ j∈Finset.Ioc (a:ℤ) ((a+(L-r):ℕ):ℤ),
        Expdb.oscillatory
          (fun u => (F u-F (u+((k:ℝ)/M)*((r:ℝ)/k)))/((k:ℝ)/M))
          (X*k/M) M j‖ := by
  have hkR : (k:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hc := HuxleyRationalPhase.sourceShiftCorrelation_difference_family_sum
    F (σ:=1) (T:=X) (N:=M) (H:=(k:ℝ)) (by norm_num) hM hkR a L r hrL
  dsimp only at hc
  rw [hc]
  simpa only [one_mul,sub_add_cancel,Complex.norm_conj] using
    upperOriginal_norm_exponentialSumAt_le_int_Ioc
      (fun u => (F u-F (u+((k:ℝ)/M)*((r:ℝ)/k-1+1)))/(1*((k:ℝ)/M)))
      (1*X*k/M) M a (a+(L-r)) (Nat.le_add_right _ _)

public  theorem upperOriginal_comparable_radius_powers
    {N R S D : ℝ} (hN : 0<N) (hR : 0<R) (hS : 0<S) (hD : 1≤D)
    (hSR : S≤D*R) (hRS : R≤D*S) :
    S^2≤D^2*R^2 ∧ 1/S^2≤D^2/R^2 ∧
      (N/S)^((2:ℝ)/3)≤D*(N/R)^((2:ℝ)/3) ∧
      (S/N)^((2:ℝ)/3)≤D*(R/N)^((2:ℝ)/3) := by
  have hD0 : 0≤D := zero_le_one.trans hD
  have hDs : D^((2:ℝ)/3)≤D := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hD (by norm_num : (2:ℝ)/3≤1)
  have hpow {x y : ℝ} (hx : 0≤x) (hy : 0≤y) (hxy : x≤D*y) :
      x^((2:ℝ)/3)≤D*y^((2:ℝ)/3) := by
    calc
      _ ≤ (D*y)^((2:ℝ)/3) := Real.rpow_le_rpow hx hxy (by norm_num)
      _ = D^((2:ℝ)/3)*y^((2:ℝ)/3) := Real.mul_rpow hD0 hy
      _ ≤ _ := mul_le_mul_of_nonneg_right hDs (Real.rpow_nonneg hy _)
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [mul_pow] using pow_le_pow_left₀ hS.le hSR 2
  · apply (div_le_div_iff₀ (sq_pos_of_pos hS) (sq_pos_of_pos hR)).mpr
    simpa only [one_mul,mul_pow] using pow_le_pow_left₀ hR.le hRS 2
  · apply hpow (div_nonneg hN.le hS.le) (div_nonneg hN.le hR.le)
    calc
      _ ≤ (D*N)/R := (div_le_div_iff₀ hS hR).mpr (by
        nlinarith only [mul_le_mul_of_nonneg_left hRS hN.le])
      _ = _ := by ring
  · apply hpow (div_nonneg hS.le hN.le) (div_nonneg hR.le hN.le)
    calc
      _ ≤ (D*R)/N := div_le_div_of_nonneg_right hSR hN.le
      _ = _ := by ring

public  theorem upperOriginal_upper_radius_error_bound
    {Ysmall Y M N R S D : ℝ}
    (hYsmall : 0≤Ysmall) (hY : Ysmall≤Y) (hM : 0<M) (hN : 0<N)
    (hR : 0<R) (hS : 0<S) (hD : 1≤D) (hSR : S≤D*R) (hRS : R≤D*S) :
    Ysmall*M/Real.sqrt N+Ysmall*M*S^2/N^2+Ysmall*N*(N/S)^((2:ℝ)/3) ≤
      D^2*(Y*M/Real.sqrt N+Y*M*R^2/N^2+Y*N*(N/R)^((2:ℝ)/3)) := by
  have hY0 := hYsmall.trans hY
  have hD0 := zero_le_one.trans hD
  have hD2 : 1≤D^2 := by nlinarith only [hD,sq_nonneg (D-1)]
  have hDD2 : D≤D^2 := by nlinarith only [hD,sq_nonneg (D-1)]
  obtain ⟨hSq,_,hInv,_⟩ := upperOriginal_comparable_radius_powers hN hR hS hD hSR hRS
  have h₁ : Ysmall*M/Real.sqrt N≤D^2*(Y*M/Real.sqrt N) := by
    calc
      _ ≤ Y*M/Real.sqrt N := by gcongr
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hD2
  have h₂ : Ysmall*M*S^2/N^2≤D^2*(Y*M*R^2/N^2) := by
    calc
      _ ≤ Y*M*(D^2*R^2)/N^2 := by gcongr
      _ = _ := by ring
  have h₃ : Ysmall*N*(N/S)^((2:ℝ)/3)≤D^2*(Y*N*(N/R)^((2:ℝ)/3)) := by
    calc
      _ ≤ Y*N*(D*(N/R)^((2:ℝ)/3)) := by gcongr
      _ = D*(Y*N*(N/R)^((2:ℝ)/3)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hDD2 (by positivity)
  calc
    _ ≤ D^2*(Y*M/Real.sqrt N)+D^2*(Y*M*R^2/N^2)+
        D^2*(Y*N*(N/R)^((2:ℝ)/3)) := add_le_add (add_le_add h₁ h₂) h₃
    _ = _ := by ring

private theorem upperOriginal_upper_radius_main_bound
    {Ysmall Y M N R S D J : ℝ}
    (hYsmall : 0≤Ysmall) (hY : Ysmall≤Y) (hM : 0<M) (hN : 0<N)
    (hR : 0<R) (hS : 0<S) (hD : 1≤D) (hJ : 0≤J)
    (hSR : S≤D*R) (hRS : R≤D*S) :
    Ysmall^11*M^11/(N*S^2)+Ysmall^11*J*M^11/N^3+
      Ysmall^12*M^12/(N^4*S^2)*(S/N)^((2:ℝ)/3) ≤
    D^4*(Y^11*M^11/(N*R^2)+Y^11*J*M^11/N^3+
      Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) := by
  have hY0 := hYsmall.trans hY
  have hD0 := zero_le_one.trans hD
  have hD4 : 1≤D^4 := one_le_pow₀ hD
  have hD24 : D^2≤D^4 := pow_le_pow_right₀ hD (by norm_num)
  have hD34 : D^3≤D^4 := pow_le_pow_right₀ hD (by norm_num)
  obtain ⟨_,hInv,_,hFor⟩ := upperOriginal_comparable_radius_powers hN hR hS hD hSR hRS
  have h₁ : Ysmall^11*M^11/(N*S^2)≤D^4*(Y^11*M^11/(N*R^2)) := by
    calc
      _ = (Ysmall^11*M^11/N)*(1/S^2) := by ring
      _ ≤ (Y^11*M^11/N)*(D^2/R^2) := by gcongr
      _ = D^2*(Y^11*M^11/(N*R^2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD24 (by positivity)
  have h₂ : Ysmall^11*J*M^11/N^3≤D^4*(Y^11*J*M^11/N^3) := by
    calc
      _ ≤ Y^11*J*M^11/N^3 := by gcongr
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hD4
  have h₃ : Ysmall^12*M^12/(N^4*S^2)*(S/N)^((2:ℝ)/3)≤
      D^4*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) := by
    calc
      _ = (Ysmall^12*M^12/N^4)*(1/S^2)*(S/N)^((2:ℝ)/3) := by ring
      _ ≤ (Y^12*M^12/N^4)*(D^2/R^2)*(D*(R/N)^((2:ℝ)/3)) := by gcongr
      _ = D^3*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD34 (by positivity)
  calc
    _ ≤ D^4*(Y^11*M^11/(N*R^2))+D^4*(Y^11*J*M^11/N^3)+
        D^4*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) :=
          add_le_add (add_le_add h₁ h₂) h₃
    _ = _ := by ring

public  theorem upperOriginal_normalized_radius_comparable
    {γ R S D : ℝ} (hR : 0<R) (hS : 0<S) (hD : 1≤D)
    (hγD : γ≤D) (hDγ : 1≤D*γ) (hlink : γ*S^2=R^2) :
    S≤D*R ∧ R≤D*S := by
  have hD0 := zero_le_one.trans hD
  have hDD2 : D≤D^2 := by nlinarith only [hD,sq_nonneg (D-1)]
  constructor
  · apply (sq_le_sq₀ hS.le (mul_nonneg hD0 hR.le)).mp
    calc
      _ ≤ (D*γ)*S^2 := le_mul_of_one_le_left (sq_nonneg S) hDγ
      _ = D*R^2 := by rw [mul_assoc,hlink]
      _ ≤ D^2*R^2 := mul_le_mul_of_nonneg_right hDD2 (sq_nonneg R)
      _ = _ := (mul_pow D R 2).symm
  · apply (sq_le_sq₀ hR.le (mul_nonneg hD0 hS.le)).mp
    calc
      _ = γ*S^2 := hlink.symm
      _ ≤ D*S^2 := mul_le_mul_of_nonneg_right hγD (sq_nonneg S)
      _ ≤ D^2*S^2 := mul_le_mul_of_nonneg_right hDD2 (sq_nonneg S)
      _ = _ := (mul_pow D S 2).symm

public  theorem upperOriginal_comparable_radius_source_budgets
    {M N R S D C : ℝ} (hM : 0<M) (hN : 0<N)
    (hR : 0<R) (hD : 1≤D) (hC : 1≤C)
    (hSR : S≤D*R) (hRS : R≤D*S)
    (hRlow : C*D^7≤R) (hRN : (C*D^7)*R≤N)
    (hNR : (C*D^7)*N≤R^2) (hNM : (C*D^7)*N^2≤M)
    (hFour : (C*D^7)*N^4≤M*R^3)
    (hTen : (C*D^7)*N^10≤M^3*R^7) :
    1≤S ∧ C*S≤N ∧ C*N≤S^2 ∧ C*N^2≤M ∧
      N^4≤M*S^3 ∧ N^10≤M^3*S^7 := by
  have hDpos := zero_lt_one.trans_le hD
  have hCpos := zero_lt_one.trans_le hC
  have hpow (i : ℕ) (hi : i≤7) : C*D^i≤C*D^7 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hi) hCpos.le
  have hplain (i : ℕ) (hi : i≤7) : D^i≤C*D^7 :=
    (le_mul_of_one_le_left (pow_nonneg hDpos.le i) hC).trans (hpow i hi)
  have hB : C≤C*D^7 := by simpa only [pow_zero,mul_one] using hpow 0 (by omega)
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · have hDb : D≤C*D^7 := by simpa only [pow_one] using hplain 1 (by omega)
    have hh := hDb.trans (hRlow.trans hRS)
    nlinarith only [hh,hDpos]
  · calc
      _ ≤ C*(D*R) := mul_le_mul_of_nonneg_left hSR hCpos.le
      _ = (C*D^1)*R := by ring
      _ ≤ (C*D^7)*R := mul_le_mul_of_nonneg_right (hpow 1 (by omega)) hR.le
      _ ≤ N := hRN
  · apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hDpos)).mp
    calc
      _ = (C*D^2)*N := by ring
      _ ≤ (C*D^7)*N := mul_le_mul_of_nonneg_right (hpow 2 (by omega)) hN.le
      _ ≤ R^2 := hNR
      _ ≤ (D*S)^2 := pow_le_pow_left₀ hR.le hRS 2
      _ = _ := by ring
  · exact (mul_le_mul_of_nonneg_right hB (sq_nonneg N)).trans hNM
  · apply (mul_le_mul_iff_right₀ (pow_pos hDpos 3)).mp
    calc
      _ ≤ (C*D^7)*N^4 :=
        mul_le_mul_of_nonneg_right (hplain 3 (by omega)) (pow_nonneg hN.le 4)
      _ ≤ M*R^3 := hFour
      _ ≤ M*(D*S)^3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le hRS 3) hM.le
      _ = _ := by ring
  · apply (mul_le_mul_iff_right₀ (pow_pos hDpos 7)).mp
    calc
      _ ≤ (C*D^7)*N^10 :=
        mul_le_mul_of_nonneg_right (hplain 7 le_rfl) (pow_nonneg hN.le 10)
      _ ≤ M^3*R^7 := hTen
      _ ≤ M^3*(D*S)^7 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le hRS 7) (pow_nonneg hM.le 3)
      _ = _ := by ring

private theorem upperOriginal_upper_expression_nonnegative
    {Y M N R J : ℝ} (hY : 0≤Y) (hM : 0≤M) (hN : 0≤N)
    (hR : 0≤R) (hJ : 0≤J) :
    0≤Y*M/Real.sqrt N+Y*M*R^2/N^2+Y*N*(N/R)^((2:ℝ)/3) ∧
    0≤Y^11*M^11/(N*R^2)+Y^11*J*M^11/N^3+
      Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3) := by
  constructor <;> positivity

private theorem upperOriginal_approximateModelPhase_enlarged_quantitative_upper
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ η₀ B C : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 1 ≤ B ∧ 1 ≤ C ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1 ≤ M →
        Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
        ∃ Fext : ℝ → ℝ,
          (∀ (X : ℝ) (a b : ℕ), M ≤ (a:ℝ) → (b:ℝ) ≤ 2*M →
            ‖Expdb.exponentialSumAt F X M a b-
              Expdb.exponentialSumAt Fext X M a b‖ ≤ 6) ∧
          ∀ (T : ℝ) (Y : Finset ℝ) (n N : ℕ) (R Jsep η : ℝ),
            C ≤ T → N=8*n → 2 ≤ N → B ≤ R →
            0 < η → η ≤ η₀ → 0 < Jsep → Jsep ≤ M →
            (∀ y∈Y, y∈Icc (1:ℝ) 2) →
            (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
            T*(N:ℝ)*R^2=M^3 →
            B*R ≤ N → B*(N:ℝ) ≤ R^2 → B*(N:ℝ)^2 ≤ M →
            B*(N:ℝ)^4 ≤ M*R^3 → B*(N:ℝ)^10 ≤ M^3*R^7 →
            ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
              (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
              let Yc := (Y.card:ℝ)
              let ErrorTotal := Yc*M/Real.sqrt (N:ℝ)+Yc*M*R^2/(N:ℝ)^2+
                Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
              let Main := Yc^11*M^11/((N:ℝ)*R^2)+
                Yc^11*Jsep*M^11/(N:ℝ)^3+
                Yc^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
              (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),
                (𝐞 (T*(Fext ((j:ℝ)/M)-Fext ((j:ℝ)/M+η*y))/η):ℂ)‖)^12 ≤
                  C*T^ε*(ErrorTotal^12+Main) := by
  classical
  have hσone : 0<σ+1 := by linarith only [hσ]
  let δmodel := min (modelPhaseThirdLower (σ+1)) 1/2
  have hmin : 0 < min (modelPhaseThirdLower (σ+1)) 1 :=
    lt_min (modelPhaseThirdLower_pos hσone) zero_lt_one
  have hδmodel : 0<δmodel := half_pos hmin
  have hδmodelCap : δmodel ≤ min (modelPhaseThirdLower (σ+1)) 1 := by
    dsimp only [δmodel]
    linarith only [hmin]
  obtain ⟨δ,ηsrc,a,c,J,hδ,hηsrc,hηsrcCap,ha,hc,hJ,hanchor,hsource⟩ :=
    HuxleyRationalPhase.approximateModelPhase_enlarged_colored_common_scale_source
      hσ hδmodel (by norm_num : (0:ℝ)<1) 5 le_rfl
  have hanchor' : c≤4*modelPhaseThirdLower (σ+1)*1/((σ+1)*((σ+1)+1)+3) := by
    simpa only [add_assoc,show (1:ℝ)+1=2 by norm_num] using hanchor
  obtain ⟨Cbudget,ηquant,hCbudget,hηquant,_,hquant⟩ :=
    HuxleyRationalPhase.eventually_upper_quantitative_phase_subinterval_bound
      (by norm_num : (0:ℝ)<1) hc hJ hσone hδmodel.le hδmodelCap hε hanchor'
  obtain ⟨Tcut,hTcut⟩ := Filter.eventually_atTop.mp hquant
  let D := 2+2*σ+1/σ
  have hD : 1≤D := by
    dsimp only [D]
    have hi : 0<1/σ := div_pos zero_lt_one hσ
    linarith only [hσ,hi]
  have hDpos := zero_lt_one.trans_le hD
  have hDσ : 1≤D*σ := by
    have hi : (1/σ)*σ=1 := div_mul_cancel₀ 1 hσ.ne'
    dsimp only [D]
    nlinarith only [hi,hσ,sq_nonneg σ]
  have hσD : 2*σ≤D := by
    dsimp only [D]
    have hi : 0<1/σ := by positivity
    linarith only [hi]
  let B := Cbudget*D^7
  have hB : 1≤B := by
    calc
      _ = (1:ℝ)*1 := by norm_num
      _ ≤ Cbudget*D^7 := mul_le_mul hCbudget (one_le_pow₀ hD)
        zero_le_one (zero_le_one.trans hCbudget)
  let Cap := 4/a+3
  have hCap : 1≤Cap := by
    dsimp only [Cap]
    have hh : 0<4/a := by positivity
    linarith only [hh]
  let K := (2*σ)^ε*D^24
  have hK : 0≤K := mul_nonneg
    (Real.rpow_nonneg (mul_nonneg (by norm_num) hσ.le) ε) (pow_nonneg hDpos.le 24)
  let C := max 1 (max (Tcut/σ) (Cap^12*K))
  have hC : 1≤C := le_max_left _ _
  have hCcut : Tcut/σ≤C := (le_max_left _ _).trans (le_max_right _ _)
  have hCK : Cap^12*K≤C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨δ,min ηsrc ηquant,B,C,hδ,lt_min hηsrc hηquant,
    (min_le_left _ _).trans hηsrcCap,hB,hC,?_⟩
  intro M F hM hF
  obtain ⟨Fext,_,_,hsharp,hcolors⟩ := hsource M F hM hF
  refine ⟨Fext,hsharp,?_⟩
  intro T Y n N R Jsep η hT hN8 hN2 hRlow hη hηcap hJsep hJsepM
    hY hsep hphase hRN hNR hNM hFour hTen A Bint hA hAB hBint Yc ErrorTotal Main
  have hMp : 0<M := zero_lt_one.trans_le hM
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hRp : 0<R := zero_lt_one.trans_le (hB.trans hRlow)
  have hTp : 0<T := zero_lt_one.trans_le (hC.trans hT)
  have hYc : 0≤Yc := Nat.cast_nonneg _
  have hSigns := upperOriginal_upper_expression_nonnegative hYc hMp.le hNp.le hRp.le hJsep.le
  have hError : 0≤ErrorTotal := hSigns.1
  have hMain : 0≤Main := hSigns.2
  have hMass : 0≤ErrorTotal^12+Main := add_nonneg (pow_nonneg hError 12) hMain
  let color := fun y : ℝ => ⌊y/a⌋
  let z := fun y : ℝ => (‖∑ j∈Finset.Ioc (A y) (Bint y),
    (𝐞 (T*(Fext ((j:ℝ)/M)-Fext ((j:ℝ)/M+η*y))/η):ℂ)‖:ℂ)
  have hzNorm (U : Finset ℝ) :
      ‖∑ y∈U,z y‖ = ∑ y∈U,‖∑ j∈Finset.Ioc (A y) (Bint y),
        (𝐞 (T*(Fext ((j:ℝ)/M)-Fext ((j:ℝ)/M+η*y))/η):ℂ)‖ := by
    dsimp only [z]
    rw [←Complex.ofReal_sum]
    exact Complex.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  obtain ⟨hcard,hmoment,hclasses⟩ :=
    hcolors Y id η hY hη (hηcap.trans (min_le_left _ _))
  have hlocal (j : ℤ) (hj : j∈Y.image color) :
      ‖∑ y∈Y.filter (fun y => color y=j),z y‖^12 ≤
        K*T^ε*(ErrorTotal^12+Main) := by
    obtain ⟨y₀,hy₀,_,hreg,hjets,htests,hnegative,hscaled⟩ := hclasses j hj
    let γ := σ*y₀
    have hy₀range := hY y₀ hy₀
    have hy₀p : 0<y₀ := zero_lt_one.trans_le hy₀range.1
    have hγ : 0<γ := mul_pos hσ hy₀p
    have hγlo : σ≤γ := le_mul_of_one_le_right hσ.le hy₀range.1
    have hγhi : γ≤2*σ := by dsimp only [γ]; nlinarith only [hy₀range.2,hσ]
    have hγD := hγhi.trans hσD
    have hDγ : 1≤D*γ := hDσ.trans (mul_le_mul_of_nonneg_left hγlo hDpos.le)
    let Fsrc := fun w => (1/(σ*y₀))*Fext w
    let Tnew := T*σ*y₀/1
    let Rnew := R*Real.sqrt (1/(σ*y₀))
    obtain ⟨hTnew,hRnew,hRsq,hnewphase,hmodels⟩ :=
      hscaled T (N:ℝ) R hTp hRp hphase
    have hTnewEq : Tnew=T*γ := by dsimp only [Tnew,γ]; rw [div_one,mul_assoc]
    have hRnewSq : Rnew^2=R^2/γ := by
      simpa only [id_eq, mul_one] using hRsq
    have hRg : γ*Rnew^2=R^2 := by rw [hRnewSq]; field_simp
    obtain ⟨hSle,hRle⟩ := upperOriginal_normalized_radius_comparable hRp hRnew hD hγD hDγ hRg
    obtain ⟨hRnew1,hnewRN,hnewNR,hnewNM,hnewFour,hnewTen⟩ :=
      upperOriginal_comparable_radius_source_budgets hMp hNp hRp hD hCbudget hSle hRle
        hRlow hRN hNR hNM hFour hTen
    have hTnewCut : Tcut≤Tnew := by
      rw [hTnewEq]
      exact ((div_le_iff₀ hσ).mp (hCcut.trans hT)).trans
        (mul_le_mul_of_nonneg_left hγlo hTp.le)
    let Yj := Y.filter (fun y => color y=j)
    have hYj (y : ℝ) (hy : y∈Yj) : y∈Y :=
      (Finset.mem_filter.mp hy).1
    have hYjColor (y : ℝ) (hy : y∈Yj) : color y=j :=
      (Finset.mem_filter.mp hy).2
    have hmod (y : ℝ) (hy : y∈Yj) :
        Expdb.IsApproximateModelPhaseFunction
          (fun u => (Fsrc u-Fsrc (u+η*y))/(1*η)) (σ+1) 4 δmodel :=
      approximateModelPhase_mono (hmodels y (hYj y hy) (hYjColor y hy)).1
        (by norm_num) le_rfl
    have hq := hTcut Tnew hTnewCut Fsrc Yj n N Rnew Jsep hN8 hN2 hRnew1
      hη (hηcap.trans (min_le_right _ _)) hJsep hJsepM
      (fun y hy => hY y (hYj y hy))
      (fun y hy v hv hne => hsep y (hYj y hy) v (hYj v hv) hne)
      hreg hjets htests hnegative hmod hnewphase hnewRN hnewNR hnewNM
      hnewFour hnewTen A Bint (fun y hy => hA y (hYj y hy))
      (fun y hy => hAB y (hYj y hy)) (fun y hy => hBint y (hYj y hy))
    have hYj0 : (0:ℝ)≤Yj.card := Nat.cast_nonneg _
    have hYjCard : (Yj.card:ℝ)≤Yc := by
      change ((Y.filter (fun y => color y=j)).card:ℝ)≤(Y.card:ℝ)
      exact_mod_cast (Finset.card_filter_le Y (fun y => color y=j))
    let Enew := (Yj.card:ℝ)*M/Real.sqrt (N:ℝ)+
      (Yj.card:ℝ)*M*Rnew^2/(N:ℝ)^2+
      (Yj.card:ℝ)*(N:ℝ)*((N:ℝ)/Rnew)^((2:ℝ)/3)
    let MainNew := (Yj.card:ℝ)^11*M^11/((N:ℝ)*Rnew^2)+
      (Yj.card:ℝ)^11*Jsep*M^11/(N:ℝ)^3+
      (Yj.card:ℝ)^12*M^12/((N:ℝ)^4*Rnew^2)*(Rnew/(N:ℝ))^((2:ℝ)/3)
    have hEnew : Enew≤D^2*ErrorTotal :=
      upperOriginal_upper_radius_error_bound hYj0 hYjCard hMp hNp hRp hRnew hD hSle hRle
    have hMainNew : MainNew≤D^4*Main :=
      upperOriginal_upper_radius_main_bound hYj0 hYjCard hMp hNp hRp hRnew hD hJsep.le hSle hRle
    have hNewSigns := upperOriginal_upper_expression_nonnegative hYj0 hMp.le hNp.le hRnew.le hJsep.le
    have hEnew0 : 0≤Enew := hNewSigns.1
    have hMainNew0 : 0≤MainNew := hNewSigns.2
    have hEpow : Enew^12≤D^24*ErrorTotal^12 := by
      calc
        _ ≤ (D^2*ErrorTotal)^12 := pow_le_pow_left₀ hEnew0 hEnew 12
        _ = _ := by rw [mul_pow,←pow_mul]
    have hMainPow : MainNew≤D^24*Main :=
      hMainNew.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hD (by norm_num : 4≤24)) hMain)
    have hTotal : Enew^12+MainNew≤D^24*(ErrorTotal^12+Main) := by
      calc
        _ ≤ D^24*ErrorTotal^12+D^24*Main := add_le_add hEpow hMainPow
        _ = _ := (mul_add _ _ _).symm
    have hTpow : Tnew^ε≤(2*σ)^ε*T^ε := by
      rw [hTnewEq,Real.mul_rpow hTp.le hγ.le]
      calc
        _ ≤ T^ε*(2*σ)^ε :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hγ.le hγhi hε.le)
            (Real.rpow_nonneg hTp.le _)
        _ = _ := mul_comm _ _
    rw [hzNorm]
    calc
      _ = (∑ y∈Yj,‖∑ l∈Finset.Ioc (A y) (Bint y),
          (𝐞 (Tnew*(Fsrc ((l:ℝ)/M)-Fsrc ((l:ℝ)/M+η*y))/(1*η)):ℂ)‖)^12 := by
        congr 1
        apply Finset.sum_congr rfl
        intro y hy
        congr 1
        apply Finset.sum_congr rfl
        intro l _
        apply congrArg (fun x : ℝ => (𝐞 x:ℂ))
        simpa only [id_eq, one_mul] using ((hmodels y (hYj y hy) (hYjColor y hy)).2.1 (l:ℝ)).symm
      _ ≤ Tnew^ε*(Enew^12+MainNew) := hq
      _ ≤ ((2*σ)^ε*T^ε)*(D^24*(ErrorTotal^12+Main)) :=
        mul_le_mul hTpow hTotal (add_nonneg (pow_nonneg hEnew0 12) hMainNew0)
          (mul_nonneg (Real.rpow_nonneg (mul_nonneg (by norm_num) hσ.le) ε)
            (Real.rpow_nonneg hTp.le ε))
      _ = _ := by dsimp only [K]; ac_rfl
  have hKmass : 0≤K*T^ε*(ErrorTotal^12+Main) :=
    mul_nonneg (mul_nonneg hK (Real.rpow_nonneg hTp.le ε)) hMass
  have hcolorSum :
      (∑ j∈Y.image color,‖∑ y∈Y.filter (fun y => color y=j),z y‖^12) ≤
        Cap*(K*T^ε*(ErrorTotal^12+Main)) := by
    calc
      _ ≤ ∑ _j∈Y.image color,K*T^ε*(ErrorTotal^12+Main) :=
        Finset.sum_le_sum hlocal
      _ = ((Y.image color).card:ℝ)*(K*T^ε*(ErrorTotal^12+Main)) := by
        rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard hKmass
  calc
    _ = ‖∑ y∈Y,z y‖^12 := congrArg (fun x : ℝ => x^12) (hzNorm Y).symm
    _ ≤ Cap^11*∑ j∈Y.image color,‖∑ y∈Y.filter (fun y => color y=j),z y‖^12 :=
      hmoment z
    _ ≤ Cap^11*(Cap*(K*T^ε*(ErrorTotal^12+Main))) :=
      mul_le_mul_of_nonneg_left hcolorSum (pow_nonneg (zero_le_one.trans hCap) 11)
    _ = (Cap^12*K)*(T^ε*(ErrorTotal^12+Main)) := by
      rw [show Cap^12=Cap^11*Cap from pow_succ Cap 11]
      ac_rfl
    _ ≤ C*(T^ε*(ErrorTotal^12+Main)) :=
      mul_le_mul_of_nonneg_right hCK (mul_nonneg (Real.rpow_nonneg hTp.le ε) hMass)
    _ = _ := (mul_assoc _ _ _).symm

public  theorem upperOriginal_dyadic_shift_actual_family
    (F : ℝ → ℝ) (X : ℝ) {M : ℝ} (hM : 0<M)
    (a L k : ℕ) (hk : 0<k) (ha : M≤(a:ℝ)) (hb : ((a+L:ℕ):ℝ)≤2*M) :
    let S := (Finset.Ico k (2*k)).filter (fun r => r≤L)
    let Y := S.image (fun (r:ℕ) => (r:ℝ)/(k:ℝ))
    let Bint := fun y : ℝ => ((a+(L-⌊(k:ℝ)*y⌋₊):ℕ):ℤ)
    Y.card≤k ∧
      (∀ y∈Y, y∈Icc (1:ℝ) 2) ∧
      (∀ y∈Y, ∀ z∈Y, y≠z → 1≤(k:ℝ)*|y-z|) ∧
      ⌈M⌉≤(a:ℤ) ∧ (∀ y∈Y, (a:ℤ)≤Bint y) ∧
      (∀ y∈Y, Bint y≤⌊2*M⌋) ∧
      (∑ j∈Finset.range k,‖sourceShiftCorrelation F X M a L (k+j)‖) ≤
        (Y.card:ℝ)+∑ y∈Y,‖∑ l∈Finset.Ioc (a:ℤ) (Bint y),
          (𝐞 ((X*k/M)*(F ((l:ℝ)/M)-F ((l:ℝ)/M+((k:ℝ)/M)*y))/
            ((k:ℝ)/M)):ℂ)‖ := by
  classical
  intro S Y Bint
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  have hinj : Function.Injective (fun r : ℕ => (r:ℝ)/(k:ℝ)) := by
    intro r s hrs
    have hh := (div_left_inj' hkR.ne').mp hrs
    exact_mod_cast hh
  have hcard : Y.card=S.card := Finset.card_image_of_injOn hinj.injOn
  have hSk : S.card≤k := by
    calc
      _ ≤ (Finset.Ico k (2*k)).card := Finset.card_filter_le _ _
      _ = k := by rw [Nat.card_Ico]; omega
  have hfloor (r : ℕ) : ⌊(k:ℝ)*((r:ℝ)/(k:ℝ))⌋₊=r := by
    rw [show (k:ℝ)*((r:ℝ)/(k:ℝ))=(r:ℝ) by field_simp]
    exact Nat.floor_natCast r
  have hgeom := HuxleyRationalPhase.difference_family_dyadic_parameter_geometry hkR
  refine ⟨hcard.trans_le hSk,?_,?_,?_,?_,?_,?_⟩
  · intro y hy
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hy
    have hr' := Finset.mem_Ico.mp (Finset.mem_filter.mp hr).1
    have hh := hgeom.1 r (by exact_mod_cast hr'.1)
      (by exact_mod_cast hr'.2.le)
    constructor <;> linarith only [hh.1,hh.2]
  · intro y hy z hz hyz
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hz
    have hrs : r≠s := fun he => hyz (congrArg (fun n : ℕ => (n:ℝ)/(k:ℝ)) he)
    have hh := hgeom.2 r s hrs
    rw [show (r:ℝ)/(k:ℝ)-1-((s:ℝ)/(k:ℝ)-1)=
      (r:ℝ)/(k:ℝ)-(s:ℝ)/(k:ℝ) by ring] at hh
    exact hh
  · apply Int.ceil_le.mpr
    simpa only [Int.cast_natCast] using ha
  · intro y _
    dsimp only [Bint]
    exact_mod_cast (Nat.le_add_right a (L-⌊(k:ℝ)*y⌋₊))
  · intro y _
    apply Int.le_floor.mpr
    have hh : ((a+(L-⌊(k:ℝ)*y⌋₊):ℕ):ℝ)≤((a+L:ℕ):ℝ) := by
      exact_mod_cast (show a+(L-⌊(k:ℝ)*y⌋₊)≤a+L by omega)
    exact hh.trans hb
  · let f := fun r => ‖sourceShiftCorrelation F X M a L r‖
    have hRange : (∑ j∈Finset.range k,f (k+j))=∑ r∈Finset.Ico k (2*k),f r := by
      apply Finset.sum_bij (fun (j:ℕ) _ => k+j)
      case hi =>
        intro j hj
        have hj' := Finset.mem_range.mp hj
        exact Finset.mem_Ico.mpr ⟨by omega,by omega⟩
      case i_inj =>
        intro j _ l _ hjl
        omega
      case i_surj =>
        intro r hr
        have hr' := Finset.mem_Ico.mp hr
        exact ⟨r-k,Finset.mem_range.mpr (by omega),by omega⟩
      case h =>
        intro j _
        rfl
    have hFilter : (∑ r∈S,f r)=∑ r∈Finset.Ico k (2*k),f r := by
      apply Finset.sum_filter_of_ne
      intro r _ hne
      by_contra hn
      exact hne (by
        dsimp only [f]
        rw [sourceShiftCorrelation_empty F X M a L r (by omega),norm_zero])
    rw [hRange,←hFilter,hcard]
    rw [Finset.sum_image hinj.injOn]
    calc
      _ ≤ ∑ r∈S,(1+‖∑ l∈Finset.Ioc (a:ℤ) (Bint ((r:ℝ)/(k:ℝ))),
          (𝐞 ((X*k/M)*(F ((l:ℝ)/M)-F ((l:ℝ)/M+((k:ℝ)/M)*((r:ℝ)/(k:ℝ))))/
            ((k:ℝ)/M)):ℂ)‖) := by
        apply Finset.sum_le_sum
        intro r hr
        have hh := upperOriginal_norm_sourceShiftCorrelation_le_difference_Ioc
          F X hM.ne' a L r k hk (Finset.mem_filter.mp hr).2
        dsimp only [Bint]
        rw [hfloor]
        simpa only [Expdb.oscillatory,←mul_div_assoc] using hh
      _ = _ := by rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one]

public  theorem upperOriginal_upper_endpoint_error_absorption
    {Y M N R : ℝ} (hY : 0≤Y) (hM : 0≤M) (hN : 1≤N)
    (hR : 0<R) (hRN : R≤N) :
    Y≤Y*M/Real.sqrt N+Y*M*R^2/N^2+Y*N*(N/R)^((2:ℝ)/3) := by
  have hNp := zero_lt_one.trans_le hN
  have hratio : 1≤N/R := (one_le_div hR).mpr hRN
  have hpow : 1≤(N/R)^((2:ℝ)/3) := Real.one_le_rpow hratio (by norm_num)
  have hunit : 1≤N*(N/R)^((2:ℝ)/3) := by
    calc
      _ = (1:ℝ)*1 := by norm_num
      _ ≤ _ := mul_le_mul hN hpow zero_le_one hNp.le
  have hh : Y≤Y*N*(N/R)^((2:ℝ)/3) := by
    calc
      _ ≤ Y*(N*(N/R)^((2:ℝ)/3)) := le_mul_of_one_le_right hY hunit
      _ = _ := (mul_assoc _ _ _).symm
  have hfirst : 0≤Y*M/Real.sqrt N+Y*M*R^2/N^2 := by positivity
  exact hh.trans (le_add_of_nonneg_left hfirst)

private theorem upperOriginal_approximateModelPhase_enlarged_upper_correlation_moment
    {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∃ δ η₀ B C : ℝ, 0<δ ∧ 0<η₀ ∧ η₀≤1/8 ∧ 1≤B ∧ 1≤C ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1≤M →
        Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
        ∃ Fext : ℝ → ℝ,
          (∀ (X : ℝ) (a b : ℕ), M≤(a:ℝ) → (b:ℝ)≤2*M →
            ‖Expdb.exponentialSumAt F X M a b-
              Expdb.exponentialSumAt Fext X M a b‖≤6) ∧
          ∀ (X : ℝ) (n N a L k : ℕ) (R : ℝ),
            C≤X*k/M → N=8*n → 2≤N → B≤R →
            0<k → (k:ℝ)/M≤η₀ → (k:ℝ)≤M →
            M≤(a:ℝ) → ((a+L:ℕ):ℝ)≤2*M →
            (X*k/M)*(N:ℝ)*R^2=M^3 →
            B*R≤N → B*(N:ℝ)≤R^2 → B*(N:ℝ)^2≤M →
            B*(N:ℝ)^4≤M*R^3 → B*(N:ℝ)^10≤M^3*R^7 →
            let K := (k:ℝ)
            let E := K*M/Real.sqrt (N:ℝ)+K*M*R^2/(N:ℝ)^2+
              K*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
            let Main := K^11*M^11/((N:ℝ)*R^2)+
              K^11*K*M^11/(N:ℝ)^3+
              K^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
            (∑ j∈Finset.range k,‖sourceShiftCorrelation Fext X M a L (k+j)‖)^12 ≤
              C*(X*k/M)^ε*(E^12+Main) := by
  classical
  obtain ⟨δ,η₀,B,C₀,hδ,hη₀,hηcap,hB,hC₀,hsource⟩ :=
    upperOriginal_approximateModelPhase_enlarged_quantitative_upper hσ hε
  let C := (2:ℝ)^12*C₀
  have hCC₀ : C₀≤C := le_mul_of_one_le_left (zero_le_one.trans hC₀) (by norm_num)
  have hC : 1≤C := hC₀.trans hCC₀
  refine ⟨δ,η₀,B,C,hδ,hη₀,hηcap,hB,hC,?_⟩
  intro M F hM hF
  obtain ⟨Fext,hsharp,hupper⟩ := hsource M F hM hF
  refine ⟨Fext,hsharp,?_⟩
  intro X n N a L k R hT hN8 hN2 hR hk hη hKM ha hb hphase hRN hNR hNM
    hFour hTen K E Main
  have hMp := zero_lt_one.trans_le hM
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hN1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hRp := zero_lt_one.trans_le (hB.trans hR)
  have hKp : 0<K := by
    change (0:ℝ)<k
    exact_mod_cast hk
  have hT1 : 1≤X*k/M := hC.trans hT
  have hTp := zero_lt_one.trans_le hT1
  let S := (Finset.Ico k (2*k)).filter (fun r => r≤L)
  let Y := S.image (fun (r:ℕ) => (r:ℝ)/(k:ℝ))
  let Bint := fun y : ℝ => ((a+(L-⌊(k:ℝ)*y⌋₊):ℕ):ℤ)
  obtain ⟨hcard,hY,hsep,hA,hAB,hBint,hcorr⟩ :=
    upperOriginal_dyadic_shift_actual_family Fext X hMp a L k hk ha hb
  have hY0 : (0:ℝ)≤Y.card := Nat.cast_nonneg _
  have hYK : (Y.card:ℝ)≤K := by
    change (Y.card:ℝ)≤(k:ℝ)
    exact_mod_cast hcard
  let EY := (Y.card:ℝ)*M/Real.sqrt (N:ℝ)+(Y.card:ℝ)*M*R^2/(N:ℝ)^2+
    (Y.card:ℝ)*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
  let MainY := (Y.card:ℝ)^11*M^11/((N:ℝ)*R^2)+
    (Y.card:ℝ)^11*(k:ℝ)*M^11/(N:ℝ)^3+
    (Y.card:ℝ)^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
  have hEY : EY≤E := by
    have hh := upperOriginal_upper_radius_error_bound hY0 hYK hMp hNp hRp hRp
      (show (1:ℝ)≤1 from le_rfl) (by rw [one_mul]) (by rw [one_mul])
    simpa only [one_pow,one_mul] using hh
  have hMY : MainY≤Main := by
    have hh := upperOriginal_upper_radius_main_bound hY0 hYK hMp hNp hRp hRp
      (show (1:ℝ)≤1 from le_rfl) hKp.le (by rw [one_mul]) (by rw [one_mul])
    simpa only [one_pow,one_mul] using hh
  have hYSigns := upperOriginal_upper_expression_nonnegative hY0 hMp.le hNp.le hRp.le hKp.le
  have hSigns := upperOriginal_upper_expression_nonnegative hKp.le hMp.le hNp.le hRp.le hKp.le
  have hEY0 : 0≤EY := hYSigns.1
  have hE0 : 0≤E := hSigns.1
  have hMain0 : 0≤Main := hSigns.2
  have hMass0 : 0≤E^12+Main := add_nonneg (pow_nonneg hE0 12) hMain0
  have hMass : EY^12+MainY≤E^12+Main :=
    add_le_add (pow_le_pow_left₀ hEY0 hEY 12) hMY
  let Z := ∑ y∈Y,‖∑ l∈Finset.Ioc (a:ℤ) (Bint y),
    (𝐞 ((X*k/M)*(Fext ((l:ℝ)/M)-Fext ((l:ℝ)/M+((k:ℝ)/M)*y))/
      ((k:ℝ)/M)):ℂ)‖
  have hZ0 : 0≤Z := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hZ : Z^12≤C₀*(X*k/M)^ε*(E^12+Main) := by
    have hu := hupper (X*k/M) Y n N R k ((k:ℝ)/M)
      (hCC₀.trans hT) hN8 hN2 hR (div_pos hKp hMp) hη hKp hKM hY hsep hphase
      hRN hNR hNM hFour hTen (fun _ => (a:ℤ)) Bint (fun _ _ => hA) hAB hBint
    exact hu.trans (mul_le_mul_of_nonneg_left hMass
      (mul_nonneg (zero_le_one.trans hC₀) (Real.rpow_nonneg hTp.le ε)))
  have hQ : 1≤C₀*(X*k/M)^ε := by
    calc
      _ = (1:ℝ)*1 := by norm_num
      _ ≤ _ := mul_le_mul hC₀ (Real.one_le_rpow hT1 hε.le)
        zero_le_one (zero_le_one.trans hC₀)
  have hRleN : R≤(N:ℝ) :=
    (le_mul_of_one_le_left hRp.le hB).trans hRN
  have hKE : K≤E := upperOriginal_upper_endpoint_error_absorption hKp.le hMp.le hN1 hRp hRleN
  have hKpow : K^12≤C₀*(X*k/M)^ε*(E^12+Main) :=
    ((pow_le_pow_left₀ hKp.le hKE 12).trans (le_add_of_nonneg_right hMain0)).trans
      (le_mul_of_one_le_left hMass0 hQ)
  have hCorr : (∑ j∈Finset.range k,‖sourceShiftCorrelation Fext X M a L (k+j)‖)≤K+Z :=
    hcorr.trans (add_le_add hYK le_rfl)
  calc
    _ ≤ (K+Z)^12 :=
      pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hCorr 12
    _ ≤ (2:ℝ)^11*(K^12+Z^12) := add_pow_le hKp.le hZ0 12
    _ ≤ (2:ℝ)^11*(C₀*(X*k/M)^ε*(E^12+Main)+C₀*(X*k/M)^ε*(E^12+Main)) :=
      mul_le_mul_of_nonneg_left (add_le_add hKpow hZ) (by norm_num)
    _ = _ := by
      rw [←two_mul]
      dsimp only [C]
      rw [show (2:ℝ)^12=2^11*2 from pow_succ 2 11]
      ac_rfl

private theorem upperOriginal_upper_correlation_integer_moments
    {X M N K R : ℝ} (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hR : 0<R)
    (hscale : (X*K/M)*N*R^2=M^3) :
    (K*M/Real.sqrt N)^36=K^36*M^36/N^18 ∧
    (K*M*R^2/N^2)^36=M^180/(X^36*N^108) ∧
    (K*N*(N/R)^((2:ℝ)/3))^36=X^12*K^48*N^72/M^48 ∧
    (K^11*M^11/(N*R^2))^3=X^3*K^36*M^21 ∧
    (K^11*K*M^11/N^3)^3=K^36*M^33/N^9 ∧
    (K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))^3=
      X^2*K^38*M^28/N^12 := by
  have hR2 : R^2=M^4/(X*K*N) := by
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero hX.ne' hK.ne') hN.ne')).mpr
    have hs := hscale
    field_simp at hs
    nlinarith only [hs]
  have hCubic : K*M*R^2/N^2=M^5/(X*N^3) := by
    rw [hR2]
    field_simp
  have hTypeOne : K^11*M^11/(N*R^2)=X*K^12*M^7 := by
    rw [hR2]
    field_simp
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · have hsqrt : (Real.sqrt N)^36=N^18 := by
      calc
        _ = ((Real.sqrt N)^2)^18 := by rw [←pow_mul]
        _ = N^18 := by rw [Real.sq_sqrt hN.le]
    rw [div_pow,mul_pow,hsqrt]
  · rw [hCubic]
    simp only [div_pow,mul_pow,←pow_mul]
  · rw [mul_pow,mul_pow,←Real.rpow_mul_natCast (div_nonneg hN.le hR.le),
      show ((2:ℝ)/3)*((36:ℕ):ℝ)=((24:ℕ):ℝ) by norm_num,
      Real.rpow_natCast,div_pow]
    rw [show R^24=(R^2)^12 by rw [←pow_mul],hR2]
    field_simp
  · rw [hTypeOne]
    simp only [mul_pow,←pow_mul]
  · simp only [mul_pow,div_pow,←pow_mul]
    ring
  · rw [mul_pow,←Real.rpow_mul_natCast (div_nonneg hR.le hN.le),
      show ((2:ℝ)/3)*((3:ℕ):ℝ)=((2:ℕ):ℝ) by norm_num,
      Real.rpow_natCast,div_pow,
      hR2]
    field_simp
    nlinarith only [(eq_div_iff (mul_ne_zero (mul_ne_zero hX.ne' hK.ne') hN.ne')).mp hR2]

public  theorem upperOriginal_upper_integer_moments_all_shifts
    {X M N K H R : ℝ}
    (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hH : 0<H) (hR : 0<R)
    (hKH : K≤H) (hscale : (X*K/M)*N*R^2=M^3) :
    (M/H)^36*(K*M/Real.sqrt N)^36≤M^72/N^18 ∧
    (M/H)^36*(K*M*R^2/N^2)^36≤M^216/(H^36*X^36*N^108) ∧
    (M/H)^36*(K*N*(N/R)^((2:ℝ)/3))^36≤X^12*H^12*N^72/M^12 ∧
    (M/H)^36*(K^11*M^11/(N*R^2))^3≤X^3*M^57 ∧
    (M/H)^36*(K^11*K*M^11/N^3)^3≤M^69/N^9 ∧
    (M/H)^36*(K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))^3≤
      X^2*H^2*M^64/N^12 := by
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ :=
    upperOriginal_upper_correlation_integer_moments hX hM hN hK hR hscale
  rw [h₁,h₂,h₃,h₄,h₅,h₆]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · calc
      _ ≤ (M/H)^36*(H^36*M^36/N^18) := by gcongr
      _ = _ := by field_simp
  · exact le_of_eq (by field_simp)
  · calc
      _ ≤ (M/H)^36*(X^12*H^48*N^72/M^48) := by gcongr
      _ = _ := by field_simp
  · calc
      _ ≤ (M/H)^36*(X^3*H^36*M^21) := by gcongr
      _ = _ := by field_simp
  · calc
      _ ≤ (M/H)^36*(H^36*M^33/N^9) := by gcongr
      _ = _ := by field_simp
  · calc
      _ ≤ (M/H)^36*(X^2*H^38*M^28/N^12) := by gcongr
      _ = _ := by field_simp

public  theorem upperOriginal_three_term_power_bound
    {a b c : ℝ} (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (n : ℕ) :
    (a+b+c)^n≤(2:ℝ)^(2*n)*(a^n+b^n+c^n) := by
  let D := (2:ℝ)^(n-1)
  have hD : 1≤D := one_le_pow₀ (by norm_num)
  have hD0 := zero_le_one.trans hD
  have hDpow : D^2≤(2:ℝ)^(2*n) := by
    dsimp only [D]
    rw [←pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    _ ≤ D*((a+b)^n+c^n) := add_pow_le (add_nonneg ha hb) hc n
    _ ≤ D*(D*(a^n+b^n)+D*c^n) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (add_pow_le ha hb n)
          (le_mul_of_one_le_left (pow_nonneg hc n) hD)) hD0
    _ = D^2*(a^n+b^n+c^n) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hDpow
      (add_nonneg (add_nonneg (pow_nonneg ha n) (pow_nonneg hb n)) (pow_nonneg hc n))

private theorem upperOriginal_weighted_upper_integer_moment_bound
    {X M N K H R : ℝ}
    (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hH : 0<H) (hR : 0<R)
    (hKH : K≤H) (hscale : (X*K/M)*N*R^2=M^3) :
    let E := K*M/Real.sqrt N+K*M*R^2/N^2+K*N*(N/R)^((2:ℝ)/3)
    let Main := K^11*M^11/(N*R^2)+K^11*K*M^11/N^3+
      K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)
    (M/H)^36*(E^36+Main^3)≤(2:ℝ)^72*
      ((M^72/N^18+M^216/(H^36*X^36*N^108)+X^12*H^12*N^72/M^12)+
        (X^3*M^57+M^69/N^9+X^2*H^2*M^64/N^12)) := by
  intro E Main
  let e₁ := K*M/Real.sqrt N
  let e₂ := K*M*R^2/N^2
  let e₃ := K*N*(N/R)^((2:ℝ)/3)
  let a₁ := K^11*M^11/(N*R^2)
  let a₂ := K^11*K*M^11/N^3
  let a₃ := K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)
  have he₁ : 0≤e₁ := by dsimp only [e₁]; positivity
  have he₂ : 0≤e₂ := by dsimp only [e₂]; positivity
  have he₃ : 0≤e₃ := by dsimp only [e₃]; positivity
  have ha₁ : 0≤a₁ := by dsimp only [a₁]; positivity
  have ha₂ : 0≤a₂ := by dsimp only [a₂]; positivity
  have ha₃ : 0≤a₃ := by dsimp only [a₃]; positivity
  have hE : E^36≤(2:ℝ)^72*(e₁^36+e₂^36+e₃^36) :=
    upperOriginal_three_term_power_bound he₁ he₂ he₃ 36
  have hMain : Main^3≤(2:ℝ)^72*(a₁^3+a₂^3+a₃^3) :=
    (upperOriginal_three_term_power_bound ha₁ ha₂ ha₃ 3).trans
      (mul_le_mul_of_nonneg_right (by norm_num)
        (add_nonneg (add_nonneg (pow_nonneg ha₁ 3) (pow_nonneg ha₂ 3)) (pow_nonneg ha₃ 3)))
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ :=
    upperOriginal_upper_integer_moments_all_shifts hX hM hN hK hH hR hKH hscale
  have hW : 0≤(M/H)^36 := pow_nonneg (div_nonneg hM.le hH.le) 36
  calc
    _ ≤ (M/H)^36*((2:ℝ)^72*(e₁^36+e₂^36+e₃^36)+
        (2:ℝ)^72*(a₁^3+a₂^3+a₃^3)) :=
      mul_le_mul_of_nonneg_left (add_le_add hE hMain) hW
    _ = (2:ℝ)^72*(((M/H)^36*e₁^36+(M/H)^36*e₂^36+(M/H)^36*e₃^36)+
        ((M/H)^36*a₁^3+(M/H)^36*a₂^3+(M/H)^36*a₃^3)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (add_le_add h₁ h₂) h₃)
        (add_le_add (add_le_add h₄ h₅) h₆)) (by norm_num)

private theorem upperOriginal_upper_weyl_seventy_second_bound
    {S Z A C L X M N K H R ε : ℝ}
    (hS : 0≤S) (hZ : 0≤Z) (hA : 0≤A) (hC : 1≤C) (hL : 0≤L)
    (hX : 1≤X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hH : 0<H) (hR : 0<R)
    (hε : 0≤ε) (hKH : K≤H) (hscale : (X*K/M)*N*R^2=M^3) :
    let E := K*M/Real.sqrt N+K*M*R^2/N^2+K*N*(N/R)^((2:ℝ)/3)
    let Main := K^11*M^11/(N*R^2)+K^11*K*M^11/N^3+
      K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)
    Z^12≤C*X^ε*(E^12+Main) →
    S^24≤A*L^12*((M^2/H)^12+(M/H)^12*Z^12) →
    S^72≤(2:ℝ)^76*A^3*C^3*L^36*X^(3*ε)*
      (M^72/H^36+
        ((M^72/N^18+M^216/(H^36*X^36*N^108)+X^12*H^12*N^72/M^12)+
          (X^3*M^57+M^69/N^9+X^2*H^2*M^64/N^12))) := by
  intro E Main hCorr hWeyl
  have hXp := zero_lt_one.trans_le hX
  have hC0 := zero_le_one.trans hC
  have hSigns := upperOriginal_upper_expression_nonnegative hK.le hM.le hN.le hR.le hK.le
  have hE0 : 0≤E := hSigns.1
  have hMain0 : 0≤Main := hSigns.2
  let V := (M^72/N^18+M^216/(H^36*X^36*N^108)+X^12*H^12*N^72/M^12)+
    (X^3*M^57+M^69/N^9+X^2*H^2*M^64/N^12)
  have hV0 : 0≤V := by dsimp only [V]; positivity
  have hW0 : 0≤(M/H)^36 := pow_nonneg (div_nonneg hM.le hH.le) 36
  have hTpow : 0≤X^(3*ε) := Real.rpow_nonneg hXp.le _
  have hTpowOne : 1≤X^(3*ε) := Real.one_le_rpow hX (mul_nonneg (by norm_num) hε)
  have hXpCube : (X^ε)^3=X^(3*ε) := by
    rw [←Real.rpow_mul_natCast hXp.le]
    congr 1
    norm_num [mul_comm]
  have hCube : S^72≤A^3*L^36*((M^2/H)^12+(M/H)^12*Z^12)^3 := by
    simpa only [mul_pow,←pow_mul] using
      pow_le_pow_left₀ (pow_nonneg hS 24) hWeyl 3
  have hAdd : ((M^2/H)^12+(M/H)^12*Z^12)^3≤
      4*(M^72/H^36+(M/H)^36*Z^36) := by
    simpa only [div_pow,mul_pow,←pow_mul,show (2:ℝ)^(3-1)=4 by norm_num] using
      add_pow_le (by positivity : 0≤(M^2/H)^12)
        (by positivity : 0≤(M/H)^12*Z^12) 3
  have hSmain : S^72≤4*A^3*L^36*(M^72/H^36+(M/H)^36*Z^36) := by
    calc
      _ ≤ A^3*L^36*((M^2/H)^12+(M/H)^12*Z^12)^3 := hCube
      _ ≤ A^3*L^36*(4*(M^72/H^36+(M/H)^36*Z^36)) :=
        mul_le_mul_of_nonneg_left hAdd (mul_nonneg (pow_nonneg hA 3) (pow_nonneg hL 36))
      _ = _ := by ac_rfl
  have hZCube : Z^36≤C^3*X^(3*ε)*(E^12+Main)^3 := by
    have hh := pow_le_pow_left₀ (pow_nonneg hZ 12) hCorr 3
    simpa only [mul_pow,←pow_mul,hXpCube] using hh
  have hEM : (E^12+Main)^3≤4*(E^36+Main^3) := by
    simpa only [←pow_mul,show (2:ℝ)^(3-1)=4 by norm_num] using
      add_pow_le (pow_nonneg hE0 12) hMain0 3
  have hZMoment : Z^36≤4*C^3*X^(3*ε)*(E^36+Main^3) := by
    calc
      _ ≤ C^3*X^(3*ε)*(E^12+Main)^3 := hZCube
      _ ≤ C^3*X^(3*ε)*(4*(E^36+Main^3)) :=
        mul_le_mul_of_nonneg_left hEM (mul_nonneg (pow_nonneg hC0 3) hTpow)
      _ = _ := by ac_rfl
  have hWeighted : (M/H)^36*(E^36+Main^3)≤(2:ℝ)^72*V :=
    upperOriginal_weighted_upper_integer_moment_bound hXp hM hN hK hH hR hKH hscale
  let Q := (2:ℝ)^74*C^3*X^(3*ε)
  have hQ : 1≤Q := by
    calc
      _ ≤ C^3 := one_le_pow₀ hC
      _ ≤ C^3*X^(3*ε) := le_mul_of_one_le_right (pow_nonneg hC0 3) hTpowOne
      _ ≤ (2:ℝ)^74*(C^3*X^(3*ε)) :=
        le_mul_of_one_le_left (mul_nonneg (pow_nonneg hC0 3) hTpow) (by norm_num)
      _ = Q := (mul_assoc _ _ _).symm
  have hScaledZ : (M/H)^36*Z^36≤Q*V := by
    calc
      _ ≤ (M/H)^36*(4*C^3*X^(3*ε)*(E^36+Main^3)) :=
        mul_le_mul_of_nonneg_left hZMoment hW0
      _ = (4*C^3*X^(3*ε))*((M/H)^36*(E^36+Main^3)) := by ac_rfl
      _ ≤ (4*C^3*X^(3*ε))*((2:ℝ)^72*V) :=
        mul_le_mul_of_nonneg_left hWeighted
          (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hC0 3)) hTpow)
      _ = Q*V := by
        dsimp only [Q]
        rw [show (2:ℝ)^74=4*2^72 by norm_num]
        ac_rfl
  have hDiag : M^72/H^36≤Q*(M^72/H^36) :=
    le_mul_of_one_le_left (by positivity) hQ
  calc
    _ ≤ 4*A^3*L^36*(M^72/H^36+(M/H)^36*Z^36) := hSmain
    _ ≤ 4*A^3*L^36*(Q*(M^72/H^36)+Q*V) :=
      mul_le_mul_of_nonneg_left (add_le_add hDiag hScaledZ)
        (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hA 3)) (pow_nonneg hL 36))
    _ = _ := by
      rw [←mul_add]
      dsimp only [Q,V]
      rw [show (2:ℝ)^76=4*2^74 by norm_num]
      ring

public  theorem upperOriginal_upper_all_shift_polynomial_budgets
    {X M N K H R B : ℝ}
    (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 1≤K) (hR : 0<R)
    (hB : 1≤B) (hKH : K≤H) (hBN : B≤N)
    (hscale : (X*K/M)*N*R^2=M^3)
    (hRN : B^2*M^4≤X*N^3) (hNR : B*X*H*N^2≤M^4)
    (hNM : B*N^2≤M)
    (hFour : B^2*X^3*H^3*N^11≤M^14)
    (hTen : B^2*X^7*H^7*N^27≤M^34) :
    B≤R ∧ B*R≤N ∧ B*N≤R^2 ∧ B*N^2≤M ∧
      B*N^4≤M*R^3 ∧ B*N^10≤M^3*R^7 := by
  have hKp := zero_lt_one.trans_le hK
  have hHp := hKp.trans_le hKH
  have hBp := zero_lt_one.trans_le hB
  have hDen : 0<X*K*N := mul_pos (mul_pos hX hKp) hN
  have hR2 : R^2=M^4/(X*K*N) := by
    apply (eq_div_iff hDen.ne').mpr
    have hs := hscale
    field_simp at hs
    nlinarith only [hs]
  have hNR' : B*N≤R^2 := by
    rw [hR2]
    apply (le_div_iff₀ hDen).mpr
    calc
      _ = B*X*K*N^2 := by ring
      _ ≤ B*X*H*N^2 := by gcongr
      _ ≤ M^4 := hNR
  refine ⟨?_,?_,hNR',hNM,?_,?_⟩
  · apply (sq_le_sq₀ hBp.le hR.le).mp
    calc
      B^2 = B*B := pow_two B
      _ ≤ B*N := mul_le_mul_of_nonneg_left hBN hBp.le
      _ ≤ R^2 := hNR'
  · apply (sq_le_sq₀ (mul_nonneg hBp.le hR.le) hN.le).mp
    rw [mul_pow,hR2,←mul_div_assoc]
    apply (div_le_iff₀ hDen).mpr
    calc
      _ ≤ X*N^3 := hRN
      _ ≤ K*(X*N^3) := le_mul_of_one_le_left (by positivity) hK
      _ = _ := by ring
  · apply (sq_le_sq₀ (mul_nonneg hBp.le (pow_nonneg hN.le 4))
      (mul_nonneg hM.le (pow_nonneg hR.le 3))).mp
    simp only [mul_pow,←pow_mul]
    rw [show R^6=(R^2)^3 by rw [←pow_mul],hR2,div_pow,←mul_div_assoc]
    apply (le_div_iff₀ (pow_pos hDen 3)).mpr
    calc
      _ = B^2*X^3*K^3*N^11 := by ring
      _ ≤ B^2*X^3*H^3*N^11 := by gcongr
      _ ≤ M^14 := hFour
      _ = _ := by ring
  · apply (sq_le_sq₀ (mul_nonneg hBp.le (pow_nonneg hN.le 10))
      (mul_nonneg (pow_nonneg hM.le 3) (pow_nonneg hR.le 7))).mp
    simp only [mul_pow,←pow_mul]
    rw [show R^14=(R^2)^7 by rw [←pow_mul],hR2,div_pow,←mul_div_assoc]
    apply (le_div_iff₀ (pow_pos hDen 7)).mpr
    calc
      _ = B^2*X^7*K^7*N^27 := by ring
      _ ≤ B^2*X^7*H^7*N^27 := by gcongr
      _ ≤ M^34 := hTen
      _ = _ := by ring

public  theorem upperOriginal_sharp_extension_power_bound
    {u v : ℂ} {D W P E : ℝ} (hD : 0≤D) (hW : 1≤W) (hP : 0≤P) (hE : 0≤E)
    (hsharp : ‖u-v‖≤E) (hv : ‖v‖^72≤D*W*P) :
    ‖u‖^72≤(2:ℝ)^71*(D+E^72)*W*(1+P) := by
  have hW0 := zero_le_one.trans hW
  have hu : ‖u‖≤‖v‖+E := by
    calc
      _ = ‖v+(u-v)‖ := by congr 1; abel
      _ ≤ ‖v‖+‖u-v‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl hsharp
  have hErr : E^72≤E^72*W :=
    le_mul_of_one_le_right (pow_nonneg hE 72) hW
  have hFold : D*W*P+E^72*W≤(D+E^72)*W*(1+P) := by
    nlinarith only [mul_nonneg hD hW0,
      mul_nonneg (mul_nonneg (pow_nonneg hE 72) hW0) hP]
  calc
    _ ≤ (‖v‖+E)^72 := pow_le_pow_left₀ (norm_nonneg _) hu 72
    _ ≤ (2:ℝ)^71*(‖v‖^72+E^72) := add_pow_le (norm_nonneg _) hE 72
    _ ≤ (2:ℝ)^71*(D*W*P+E^72*W) :=
      mul_le_mul_of_nonneg_left (add_le_add hv hErr) (by norm_num)
    _ ≤ (2:ℝ)^71*((D+E^72)*W*(1+P)) :=
      mul_le_mul_of_nonneg_left hFold (by norm_num)
    _ = _ := by ac_rfl

private theorem upperOriginal_approximateModelPhase_upper_original_seventy_second
    {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∃ δ η₀ B C : ℝ, 0<δ ∧ 0<η₀ ∧ η₀≤1/8 ∧ 1≤B ∧ 1≤C ∧
      ∀ (X M : ℝ) (F : ℝ → ℝ) (n N H a L : ℕ),
        1≤X → 1≤M → Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
        N=8*n → 2≤N → 2≤H → (H:ℝ)≤η₀*M → C≤X/M →
        B≤N → B^2*M^4≤X*(N:ℝ)^3 → B*X*(H:ℝ)*(N:ℝ)^2≤M^4 →
        B*(N:ℝ)^2≤M → B^2*X^3*(H:ℝ)^3*(N:ℝ)^11≤M^14 →
        B^2*X^7*(H:ℝ)^7*(N:ℝ)^27≤M^34 →
        M≤(a:ℝ) → ((a+L:ℕ):ℝ)≤2*M →
        ‖Expdb.exponentialSumAt F X M a (a+L)‖^72 ≤
          C*(1+(Nat.clog 2 H:ℝ))^36*X^(3*ε)*
            (1+(M^72/(H:ℝ)^36+
              ((M^72/(N:ℝ)^18+M^216/((H:ℝ)^36*X^36*(N:ℝ)^108)+
                  X^12*(H:ℝ)^12*(N:ℝ)^72/M^12)+
                (X^3*M^57+M^69/(N:ℝ)^9+X^2*(H:ℝ)^2*M^64/(N:ℝ)^12)))) := by
  classical
  obtain ⟨δ,η₀,B,C₀,hδ,hη₀,hηcap,hB,hC₀,hsource⟩ :=
    upperOriginal_approximateModelPhase_enlarged_upper_correlation_moment hσ hε
  let A₀ := (18:ℝ)^12*(2:ℝ)^11
  have hA₀ : 0≤A₀ := by dsimp only [A₀]; norm_num
  let D := (2:ℝ)^76*A₀^3*C₀^3
  have hD : 0≤D := mul_nonneg
    (mul_nonneg (by norm_num) (pow_nonneg hA₀ 3)) (pow_nonneg (zero_le_one.trans hC₀) 3)
  let C := max C₀ ((2:ℝ)^71*(D+6^72))
  have hCC₀ : C₀≤C := le_max_left _ _
  have hCoeff : (2:ℝ)^71*(D+6^72)≤C := le_max_right _ _
  have hC : 1≤C := hC₀.trans hCC₀
  refine ⟨δ,η₀,B,C,hδ,hη₀,hηcap,hB,hC,?_⟩
  intro X M F n N H a L hX hM hF hN8 hN2 hH2 hHeta hThreshold
    hBN hRN hNR hNM hFour hTen ha hb
  have hXp := zero_lt_one.trans_le hX
  have hMp := zero_lt_one.trans_le hM
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hHp : (0:ℝ)<H := by exact_mod_cast (show 0<H by omega)
  have hHM : (H:ℝ)≤M := by
    calc
      _ ≤ η₀*M := hHeta
      _ ≤ (1:ℝ)*M := mul_le_mul_of_nonneg_right
        (hηcap.trans (by norm_num : (1:ℝ)/8≤1)) hMp.le
      _ = M := one_mul M
  have hLM : (L:ℝ)+1≤2*M := by
    have hb' : (a:ℝ)+(L:ℝ)≤2*M := by simpa only [Nat.cast_add] using hb
    linarith only [hb',ha,hM]
  obtain ⟨Fext,hsharp,hcorr⟩ := hsource M F hM hF
  obtain ⟨k,hk,hkH,hweyl⟩ := upperOriginal_exists_source_dyadic_twenty_fourth_power
    Fext X M a L H hMp hH2 hHM hLM
  have hKp : (0:ℝ)<k := by exact_mod_cast hk
  have hK1 : (1:ℝ)≤k := by exact_mod_cast (show 1≤k by omega)
  have hKH : (k:ℝ)≤H := by exact_mod_cast (show k≤H by omega)
  have hKM : (k:ℝ)≤M := hKH.trans hHM
  let R := Real.sqrt (M^4/(X*(k:ℝ)*(N:ℝ)))
  have hRadicand : 0<M^4/(X*(k:ℝ)*(N:ℝ)) :=
    div_pos (pow_pos hMp 4) (mul_pos (mul_pos hXp hKp) hNp)
  have hRp : 0<R := Real.sqrt_pos.mpr hRadicand
  have hR2 : R^2=M^4/(X*(k:ℝ)*(N:ℝ)) := Real.sq_sqrt hRadicand.le
  have hphase : (X*k/M)*(N:ℝ)*R^2=M^3 := by
    rw [hR2]
    field_simp
  obtain ⟨hBR,hRNN,hNRR,hNMM,hFourR,hTenR⟩ :=
    upperOriginal_upper_all_shift_polynomial_budgets hXp hMp hNp hK1 hRp hB hKH hBN
      hphase hRN hNR hNM hFour hTen
  have hTbase : C₀≤X*k/M := by
    calc
      _ ≤ X/M := hCC₀.trans hThreshold
      _ ≤ (X/M)*(k:ℝ) := le_mul_of_one_le_right (div_nonneg hXp.le hMp.le) hK1
      _ = _ := by ring
  have hTbasePos := zero_lt_one.trans_le (hC₀.trans hTbase)
  have hTbaseUpper : X*k/M≤X :=
    (div_le_iff₀ hMp).mpr (mul_le_mul_of_nonneg_left hKM hXp.le)
  have hEtaK : (k:ℝ)/M≤η₀ := (div_le_iff₀ hMp).mpr (hKH.trans hHeta)
  let E := (k:ℝ)*M/Real.sqrt (N:ℝ)+(k:ℝ)*M*R^2/(N:ℝ)^2+
    (k:ℝ)*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
  let Main := (k:ℝ)^11*M^11/((N:ℝ)*R^2)+(k:ℝ)^11*(k:ℝ)*M^11/(N:ℝ)^3+
    (k:ℝ)^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
  let Z := ∑ j∈Finset.range k,‖sourceShiftCorrelation Fext X M a L (k+j)‖
  have hZ0 : 0≤Z := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hZbase : Z^12≤C₀*(X*k/M)^ε*(E^12+Main) :=
    hcorr X n N a L k R hTbase hN8 hN2 hBR hk hEtaK hKM ha hb hphase
      hRNN hNRR hNMM hFourR hTenR
  have hSigns := upperOriginal_upper_expression_nonnegative hKp.le hMp.le hNp.le hRp.le hKp.le
  have hE0 : 0≤E := hSigns.1
  have hMain0 : 0≤Main := hSigns.2
  have hZ : Z^12≤C₀*X^ε*(E^12+Main) :=
    hZbase.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hTbasePos.le hTbaseUpper hε.le)
        (zero_le_one.trans hC₀)) (add_nonneg (pow_nonneg hE0 12) hMain0))
  let Poly := M^72/(H:ℝ)^36+
    ((M^72/(N:ℝ)^18+M^216/((H:ℝ)^36*X^36*(N:ℝ)^108)+
        X^12*(H:ℝ)^12*(N:ℝ)^72/M^12)+
      (X^3*M^57+M^69/(N:ℝ)^9+X^2*(H:ℝ)^2*M^64/(N:ℝ)^12))
  have hPoly : 0≤Poly := by dsimp only [Poly]; positivity
  have hClog : (0:ℝ)≤Nat.clog 2 H := Nat.cast_nonneg _
  have hClogPlus : (1:ℝ)≤1+(Nat.clog 2 H:ℝ) := le_add_of_nonneg_right hClog
  have hClogPlus0 := zero_le_one.trans hClogPlus
  have hXpow0 : 0≤X^(3*ε) := Real.rpow_nonneg hXp.le _
  have hSext : ‖Expdb.exponentialSumAt Fext X M a (a+L)‖^72≤
      D*(Nat.clog 2 H:ℝ)^36*X^(3*ε)*Poly :=
    upperOriginal_upper_weyl_seventy_second_bound (norm_nonneg _) hZ0 hA₀ hC₀ hClog hX hMp hNp
      hKp hHp hRp hε.le hKH hphase hZ hweyl
  let W := (1+(Nat.clog 2 H:ℝ))^36*X^(3*ε)
  have hW : 1≤W := by
    calc
      _ ≤ (1+(Nat.clog 2 H:ℝ))^36 := one_le_pow₀ hClogPlus
      _ ≤ _ := le_mul_of_one_le_right (pow_nonneg hClogPlus0 36)
        (Real.one_le_rpow hX (mul_nonneg (by norm_num) hε.le))
  have hLog : (Nat.clog 2 H:ℝ)^36≤(1+(Nat.clog 2 H:ℝ))^36 :=
    pow_le_pow_left₀ hClog (by linarith only) 36
  have hSext' : ‖Expdb.exponentialSumAt Fext X M a (a+L)‖^72≤D*W*Poly := by
    calc
      _ ≤ D*(Nat.clog 2 H:ℝ)^36*X^(3*ε)*Poly := hSext
      _ ≤ D*(1+(Nat.clog 2 H:ℝ))^36*X^(3*ε)*Poly :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLog hD) hXpow0) hPoly
      _ = _ := by dsimp only [W]; simp only [mul_assoc]
  have hOriginal := upperOriginal_sharp_extension_power_bound hD hW hPoly (by norm_num : (0:ℝ)≤6)
    (hsharp X a (a+L) ha hb) hSext'
  calc
    _ ≤ (2:ℝ)^71*(D+6^72)*W*(1+Poly) := hOriginal
    _ ≤ C*W*(1+Poly) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCoeff (zero_le_one.trans hW))
        (add_nonneg zero_le_one hPoly)
    _ = _ := by dsimp only [W,Poly]; simp only [mul_assoc]

public  theorem upperOriginal_floor_power_scales
    {U V : ℝ} (hU : 32≤U) (hV : 4≤V) :
    let n := ⌊U/8⌋₊
    let N := 8*n
    let H := ⌊V⌋₊
    2≤N ∧ 2≤H ∧ U/2≤(N:ℝ) ∧ (N:ℝ)≤U ∧
      V/2≤(H:ℝ) ∧ (H:ℝ)≤V := by
  intro n N H
  have hn4 : 4≤n := Nat.le_floor (by linarith only [hU] : (4:ℝ)≤U/8)
  have hH4 : 4≤H := Nat.le_floor hV
  have hNcast : (N:ℝ)=8*(n:ℝ) := by simp only [N,Nat.cast_mul,Nat.cast_ofNat]
  have hnlo : U/8<(n:ℝ)+1 := Nat.lt_floor_add_one (U/8)
  have hnhi : (n:ℝ)≤U/8 := Nat.floor_le (by linarith only [hU])
  have hHlo : V<(H:ℝ)+1 := Nat.lt_floor_add_one V
  have hHhi : (H:ℝ)≤V := Nat.floor_le (by linarith only [hV])
  refine ⟨by dsimp only [N]; omega,by omega,?_,?_,?_,hHhi⟩
  · rw [hNcast]
    linarith only [hnlo,hU]
  · rw [hNcast]
    linarith only [hnhi]
  · linarith only [hHlo,hV]

public  theorem upperOriginal_eventually_uniform_clog_power_loss
    {C ζ : ℝ} (hC : 0≤C) (hζ : 0<ζ) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ H : ℕ, 2≤H → (H:ℝ)≤X →
      C*(1+(Nat.clog 2 H:ℝ))^36≤X^ζ := by
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  let D := 1+2/Real.log 2
  have hD : 0≤D := by dsimp only [D]; positivity
  have hLoss := eventually_const_log_pow_le_rpow
    (C*D^36) (mul_nonneg hC (pow_nonneg hD 36)) 36 hζ
  filter_upwards [hLoss,Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Filter.eventually_ge_atTop (1:ℝ)] with X hLossX hlogX hX
  intro H hH hHX
  have hHp : (0:ℝ)<H := by exact_mod_cast (show 0<H by omega)
  have hlogHX := Real.log_le_log hHp hHX
  have hc : (Nat.clog 2 H:ℝ)≤(2/Real.log 2)*Real.log X := by
    calc
      _ ≤ 2*(Real.log H/Real.log 2) := nat_clog_two_le_twice_log H hH
      _ ≤ 2*(Real.log X/Real.log 2) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hlogHX hlog2.le) (by norm_num)
      _ = _ := by ring
  have hplus : 1+(Nat.clog 2 H:ℝ)≤D*Real.log X := by
    dsimp only [D]
    nlinarith only [hc,hlogX]
  calc
    _ ≤ C*(D*Real.log X)^36 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hplus 36) hC
    _ = (C*D^36)*(Real.log X)^36 := by rw [mul_pow,mul_assoc]
    _ ≤ X^ζ := hLossX

private theorem upperOriginal_upper_seven_monomials_power_window
    {X M N H ℓ u ν h ξ : ℝ}
    (hX : 1≤X) (hξ : 0≤ξ)
    (hMl : X^ℓ≤M) (hMu : M≤X^u)
    (hNl : X^ν/2≤N) (hNu : N≤X^ν)
    (hHl : X^h/2≤H) (hHu : H≤X^h)
    (hDiag : 72*u-36*h≤ξ) (hSqrt : 72*u-18*ν≤ξ)
    (hCubic : 216*u-36*h-36-108*ν≤ξ)
    (hEndpoint : 12+12*h+72*ν-12*ℓ≤ξ)
    (hType1 : 3+57*u≤ξ) (hType2 : 69*u-9*ν≤ξ)
    (hPair : 2+2*h+64*u-12*ν≤ξ) :
    1+(M^72/H^36+
      ((M^72/N^18+M^216/(H^36*X^36*N^108)+X^12*H^12*N^72/M^12)+
        (X^3*M^57+M^69/N^9+X^2*H^2*M^64/N^12))) ≤
      (8*(2:ℝ)^144)*X^ξ := by
  have hXp := zero_lt_one.trans_le hX
  have hMp : 0<M := (Real.rpow_pos_of_pos hXp ℓ).trans_le hMl
  have hNp : 0<N := (div_pos (Real.rpow_pos_of_pos hXp ν) (by norm_num)).trans_le hNl
  have hHp : 0<H := (div_pos (Real.rpow_pos_of_pos hXp h) (by norm_num)).trans_le hHl
  have hconst {b : ℝ} {j : ℕ} (hj : j≤144) (hb : b≤ξ) :
      (2:ℝ)^j*X^b≤(2:ℝ)^144*X^ξ :=
    mul_le_mul (pow_le_pow_right₀ (by norm_num) hj)
      (Real.rpow_le_rpow_of_exponent_le hX hb) (Real.rpow_nonneg hXp.le _) (by positivity)
  have h₀ : 1≤(2:ℝ)^144*X^ξ :=
    (Real.one_le_rpow hX hξ).trans
      (le_mul_of_one_le_left (Real.rpow_nonneg hXp.le _) (by norm_num))
  have h₁ : M^72/H^36≤(2:ℝ)^144*X^ξ := by
    calc
      _ ≤ (X^u)^72/(X^h/2)^36 := by gcongr
      _ = (2:ℝ)^36*((X^u)^72/(X^h)^36) := by field_simp
      _ = (2:ℝ)^36*X^(72*u-36*h) := by
        rw [←Real.rpow_mul_natCast hXp.le,←Real.rpow_mul_natCast hXp.le,
          ←Real.rpow_sub hXp]
        apply congrArg (fun y : ℝ => (2:ℝ)^36*X^y)
        push_cast
        ring
      _ ≤ _ := hconst (by norm_num) hDiag
  have h₂ : M^72/N^18≤(2:ℝ)^144*X^ξ := by
    calc
      _ ≤ (X^u)^72/(X^ν/2)^18 := by gcongr
      _ = (2:ℝ)^18*((X^u)^72/(X^ν)^18) := by field_simp
      _ = (2:ℝ)^18*X^(72*u-18*ν) := by
        rw [←Real.rpow_mul_natCast hXp.le,←Real.rpow_mul_natCast hXp.le,
          ←Real.rpow_sub hXp]
        apply congrArg (fun y : ℝ => (2:ℝ)^18*X^y)
        push_cast
        ring
      _ ≤ _ := hconst (by norm_num) hSqrt
  have h₃ : M^216/(H^36*X^36*N^108)≤(2:ℝ)^144*X^ξ := by
    calc
      _ ≤ (X^u)^216/((X^h/2)^36*X^36*(X^ν/2)^108) := by gcongr
      _ = (2:ℝ)^144*((X^u)^216/((X^h)^36*X^36*(X^ν)^108)) := by field_simp
      _ = (2:ℝ)^144*X^(216*u-36*h-36-108*ν) := by
        simp only [←Real.rpow_mul_natCast hXp.le]
        rw [←Real.rpow_natCast X 36]
        simp only [←Real.rpow_add hXp,←Real.rpow_sub hXp]
        apply congrArg (fun y : ℝ => (2:ℝ)^144*X^y)
        push_cast
        ring
      _ ≤ _ := hconst le_rfl hCubic
  have h₄ : X^12*H^12*N^72/M^12≤(2:ℝ)^144*X^ξ := by
    calc
      _ ≤ X^12*(X^h)^12*(X^ν)^72/(X^ℓ)^12 := by gcongr
      _ = X^(12+12*h+72*ν-12*ℓ) := by
        simp only [←Real.rpow_mul_natCast hXp.le]
        rw [←Real.rpow_natCast X 12]
        simp only [←Real.rpow_add hXp,←Real.rpow_sub hXp]
        apply congrArg (fun y : ℝ => X^y)
        push_cast
        ring
      _ ≤ _ := by simpa only [pow_zero,one_mul] using hconst (j:=0) (by omega) hEndpoint
  have h₅ : X^3*M^57≤(2:ℝ)^144*X^ξ := by
    calc
      _ ≤ X^3*(X^u)^57 := by gcongr
      _ = X^(3+57*u) := by
        rw [←Real.rpow_mul_natCast hXp.le,←Real.rpow_natCast X 3,←Real.rpow_add hXp]
        apply congrArg (fun y : ℝ => X^y)
        push_cast
        ring
      _ ≤ _ := by simpa only [pow_zero,one_mul] using hconst (j:=0) (by omega) hType1
  have h₆ : M^69/N^9≤(2:ℝ)^144*X^ξ := by
    calc
      _ ≤ (X^u)^69/(X^ν/2)^9 := by gcongr
      _ = (2:ℝ)^9*((X^u)^69/(X^ν)^9) := by field_simp
      _ = (2:ℝ)^9*X^(69*u-9*ν) := by
        rw [←Real.rpow_mul_natCast hXp.le,←Real.rpow_mul_natCast hXp.le,
          ←Real.rpow_sub hXp]
        apply congrArg (fun y : ℝ => (2:ℝ)^9*X^y)
        push_cast
        ring
      _ ≤ _ := hconst (by norm_num) hType2
  have h₇ : X^2*H^2*M^64/N^12≤(2:ℝ)^144*X^ξ := by
    calc
      _ ≤ X^2*(X^h)^2*(X^u)^64/(X^ν/2)^12 := by gcongr
      _ = (2:ℝ)^12*(X^2*(X^h)^2*(X^u)^64/(X^ν)^12) := by field_simp
      _ = (2:ℝ)^12*X^(2+2*h+64*u-12*ν) := by
        simp only [←Real.rpow_mul_natCast hXp.le]
        rw [←Real.rpow_natCast X 2]
        simp only [←Real.rpow_add hXp,←Real.rpow_sub hXp]
        apply congrArg (fun y : ℝ => (2:ℝ)^12*X^y)
        push_cast
        ring
      _ ≤ _ := hconst (by norm_num) hPair
  linarith only [h₀,h₁,h₂,h₃,h₄,h₅,h₆,h₇]

public  theorem upperOriginal_eventually_upper_polynomial_power_window
    {B C η ℓ u ν h : ℝ}
    (hB : 1≤B) (hC : 1≤C) (hη : 0<η)
    (hℓ : 0<ℓ) (hν : 0<ν) (hh : 0<h)
    (hu : u<1) (hhℓ : h<ℓ) (hRN : 4*u<1+3*ν)
    (hNR : 1+h+2*ν<4*ℓ) (hNM : 2*ν<ℓ)
    (hFour : 3+3*h+11*ν<14*ℓ) (hTen : 7+7*h+27*ν<34*ℓ) :
    ∀ᶠ X : ℝ in Filter.atTop, 1≤X ∧
      ∀ M : ℝ, X^ℓ≤M → M≤X^u →
        let n := ⌊X^ν/8⌋₊
        let N := 8*n
        let H := ⌊X^h⌋₊
        1≤M ∧ 2≤N ∧ 2≤H ∧
        X^ν/2≤(N:ℝ) ∧ (N:ℝ)≤X^ν ∧ X^h/2≤(H:ℝ) ∧ (H:ℝ)≤X^h ∧
        (H:ℝ)≤η*M ∧ C≤X/M ∧ B≤N ∧
        B^2*M^4≤X*(N:ℝ)^3 ∧ B*X*(H:ℝ)*(N:ℝ)^2≤M^4 ∧
        B*(N:ℝ)^2≤M ∧ B^2*X^3*(H:ℝ)^3*(N:ℝ)^11≤M^14 ∧
        B^2*X^7*(H:ℝ)^7*(N:ℝ)^27≤M^34 := by
  have hB0 := zero_le_one.trans hB
  have hC0 := zero_le_one.trans hC
  have hNpow : ∀ᶠ X : ℝ in Filter.atTop, 32≤X^ν :=
    (tendsto_rpow_atTop hν).eventually_ge_atTop 32
  have hHpow : ∀ᶠ X : ℝ in Filter.atTop, 4≤X^h :=
    (tendsto_rpow_atTop hh).eventually_ge_atTop 4
  have hBNdom := eventually_const_mul_rpow_le_rpow (D:=2*B) (a:=0) hν
  have hRNdom := eventually_const_mul_rpow_le_rpow (D:=8*B^2) hRN
  have hNRdom := eventually_const_mul_rpow_le_rpow (D:=B) hNR
  have hNMdom := eventually_const_mul_rpow_le_rpow (D:=B) hNM
  have hFourdom := eventually_const_mul_rpow_le_rpow (D:=B^2) hFour
  have hTendom := eventually_const_mul_rpow_le_rpow (D:=B^2) hTen
  have hEtadom := eventually_const_mul_rpow_le_rpow (D:=1/η) hhℓ
  have hThreshold := eventually_const_mul_rpow_le_rpow (D:=C) hu
  filter_upwards [hNpow,hHpow,hBNdom,hRNdom,hNRdom,hNMdom,hFourdom,hTendom,
    hEtadom,hThreshold,Filter.eventually_ge_atTop (1:ℝ)] with
    X hNU hHU hBNX hRNX hNRX hNMX hFourX hTenX hEtaX hThresholdX hX
  refine ⟨hX,?_⟩
  intro M hMl hMu n N H
  have hXp := zero_lt_one.trans_le hX
  have hM1 : 1≤M := (Real.one_le_rpow hX hℓ.le).trans hMl
  have hMp := zero_lt_one.trans_le hM1
  obtain ⟨hN2,hH2,hNl,hNu,hHl,hHu⟩ := upperOriginal_floor_power_scales hNU hHU
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hHp : (0:ℝ)<H := by exact_mod_cast (show 0<H by omega)
  have hp (q : ℝ) (m : ℕ) : (X^q)^m=X^((m:ℝ)*q) := by
    simpa only [mul_comm] using (Real.rpow_mul_natCast hXp.le q m).symm
  refine ⟨hM1,hN2,hH2,hNl,hNu,hHl,hHu,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have he : X^h≤η*X^ℓ := by
      have hh' := mul_le_mul_of_nonneg_left hEtaX hη.le
      simpa [one_div,←mul_assoc,hη.ne'] using hh'
    exact hHu.trans (he.trans (mul_le_mul_of_nonneg_left hMl hη.le))
  · apply (le_div_iff₀ hMp).mpr
    calc
      _ ≤ C*X^u := mul_le_mul_of_nonneg_left hMu hC0
      _ ≤ X^1 := hThresholdX
      _ = X := Real.rpow_one X
  · have he : 2*B≤X^ν := by simpa only [Real.rpow_zero,mul_one] using hBNX
    change B≤(N:ℝ)
    linarith only [he,hNl]
  · have hlow : B^2*(X^u)^4≤X*(X^ν/2)^3 := by
      apply (mul_le_mul_iff_right₀ (by norm_num : (0:ℝ)<8)).mp
      calc
        _ = (8*B^2)*X^(4*u) := by rw [hp]; norm_num only [Nat.cast_ofNat]; ring
        _ ≤ X^(1+3*ν) := hRNX
        _ = _ := by
          rw [div_pow,hp,Real.rpow_add hXp,Real.rpow_one]
          norm_num only [Nat.cast_ofNat]
          field_simp
    calc
      _ ≤ B^2*(X^u)^4 := by gcongr
      _ ≤ X*(X^ν/2)^3 := hlow
      _ ≤ _ := by gcongr
  · calc
      _ ≤ B*X*(X^h)*(X^ν)^2 := by gcongr
      _ = B*(X^(1:ℝ)*(X^h)*(X^ν)^2) := by rw [Real.rpow_one]; ring
      _ = B*X^(1+h+2*ν) := by
        rw [hp]
        norm_num only [Nat.cast_ofNat]
        rw [←Real.rpow_add hXp,←Real.rpow_add hXp]
      _ ≤ X^(4*ℓ) := hNRX
      _ = (X^ℓ)^4 := by simpa only [Nat.cast_ofNat] using (hp ℓ 4).symm
      _ ≤ _ := by gcongr
  · calc
      _ ≤ B*(X^ν)^2 := by gcongr
      _ = B*X^(2*ν) := by rw [hp]; norm_num only [Nat.cast_ofNat]
      _ ≤ X^ℓ := hNMX
      _ ≤ M := hMl
  · calc
      _ ≤ B^2*X^3*(X^h)^3*(X^ν)^11 := by gcongr
      _ = B^2*X^(3+3*h+11*ν) := by
        rw [hp,hp,←Real.rpow_natCast X 3]
        norm_num only [Nat.cast_ofNat]
        simp only [mul_assoc,←Real.rpow_add hXp]
      _ ≤ X^(14*ℓ) := hFourX
      _ = (X^ℓ)^14 := by simpa only [Nat.cast_ofNat] using (hp ℓ 14).symm
      _ ≤ _ := by gcongr
  · calc
      _ ≤ B^2*X^7*(X^h)^7*(X^ν)^27 := by gcongr
      _ = B^2*X^(7+7*h+27*ν) := by
        rw [hp,hp,←Real.rpow_natCast X 7]
        norm_num only [Nat.cast_ofNat]
        simp only [mul_assoc,←Real.rpow_add hXp]
      _ ≤ X^(34*ℓ) := hTenX
      _ = (X^ℓ)^34 := by simpa only [Nat.cast_ofNat] using (hp ℓ 34).symm
      _ ≤ _ := by gcongr

private theorem upperOriginal_upper_beta_of_power_window
    {α : ℝ≥0} {β δw ν h εs ζ : ℝ}
    (hδw : 0<δw) (hν : 0<ν) (hh : 0<h) (hεs : 0<εs) (hζ : 0<ζ)
    (hℓ : 0<(α:ℝ)-δw) (hu : (α:ℝ)+δw<1)
    (hhℓ : h<(α:ℝ)-δw) (hRN : 4*((α:ℝ)+δw)<1+3*ν)
    (hNR : 1+h+2*ν<4*((α:ℝ)-δw)) (hNM : 2*ν<(α:ℝ)-δw)
    (hFour : 3+3*h+11*ν<14*((α:ℝ)-δw))
    (hTen : 7+7*h+27*ν<34*((α:ℝ)-δw))
    (hBase : 3*εs+ζ≤72*β)
    (hDiag : 72*((α:ℝ)+δw)-36*h+3*εs+ζ≤72*β)
    (hSqrt : 72*((α:ℝ)+δw)-18*ν+3*εs+ζ≤72*β)
    (hCubic : 216*((α:ℝ)+δw)-36*h-36-108*ν+3*εs+ζ≤72*β)
    (hEndpoint : 12+12*h+72*ν-12*((α:ℝ)-δw)+3*εs+ζ≤72*β)
    (hType1 : 3+57*((α:ℝ)+δw)+3*εs+ζ≤72*β)
    (hType2 : 69*((α:ℝ)+δw)-9*ν+3*εs+ζ≤72*β)
    (hPair : 2+2*h+64*((α:ℝ)+δw)-12*ν+3*εs+ζ≤72*β) :
    Expdb.IsExponentSumBoundNonAsymptotic α β := by
  intro ε hε σ hσ
  obtain ⟨δsrc,η,B,Csrc,hδsrc,hη,hηcap,hB,hCsrc,hSource⟩ :=
    upperOriginal_approximateModelPhase_upper_original_seventy_second hσ hεs
  have hPhys := upperOriginal_eventually_upper_polynomial_power_window
    hB hCsrc hη hℓ hν hh hu hhℓ hRN hNR hNM hFour hTen
  have hLog := upperOriginal_eventually_uniform_clog_power_loss
    (C:=Csrc*(8*(2:ℝ)^144))
    (mul_nonneg (zero_le_one.trans hCsrc) (by norm_num)) hζ
  obtain ⟨T₀,hT₀⟩ := Filter.eventually_atTop.mp (hPhys.and hLog)
  let δ := min δsrc δw
  let C := max 1 T₀
  have hC : 1≤C := le_max_left _ _
  refine ⟨δ,lt_min hδsrc hδw,7,by norm_num,C,hC,?_⟩
  intro T M F a b setup
  have hT : 1≤T := hC.trans setup.threshold_le_param
  have hTp := zero_lt_one.trans_le hT
  have hTogether := hT₀ T ((le_max_right 1 T₀).trans setup.threshold_le_param)
  by_cases hba : b<a
  · rw [Expdb.exponentialSumAt_of_lt hba,norm_zero]
    exact mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg hTp.le _)
  have hab : a≤b := Nat.le_of_not_gt hba
  let L := b-a
  have hEnd : a+L=b := Nat.add_sub_of_le hab
  have hδwle : δ≤δw := min_le_right _ _
  have hδsrcle : δ≤δsrc := min_le_left _ _
  have hMl : T^((α:ℝ)-δw)≤M :=
    (Real.rpow_le_rpow_of_exponent_le hT (sub_le_sub_left hδwle _)).trans
      setup.rpow_sub_le_scale
  have hMu : M≤T^((α:ℝ)+δw) := setup.scale_le_rpow_add.trans
    (Real.rpow_le_rpow_of_exponent_le hT (add_le_add le_rfl hδwle))
  have hF := approximateModelPhase_mono setup.isApproximateModelPhase le_rfl hδsrcle
  let n := ⌊T^ν/8⌋₊
  let N := 8*n
  let H := ⌊T^h⌋₊
  obtain ⟨hM,hN2,hH2,hNl,hNu,hHl,hHu,hHη,hThreshold,hBN,hRNM,hNRM,
      hNMM,hFourM,hTenM⟩ := hTogether.1.2 M hMl hMu
  have hStart := setup.scale_le_start
  have hStop : ((a+L:ℕ):ℝ)≤2*M := by rw [hEnd]; exact setup.end_le_two_mul_scale
  have hActual := hSource T M F n N H a L hT hM hF rfl hN2 hH2 hHη
    hThreshold hBN hRNM hNRM hNMM hFourM hTenM hStart hStop
  let ξ := 72*β-3*εs-ζ
  have hξ : 0≤ξ := by dsimp only [ξ]; linarith only [hBase]
  have hPoly := upperOriginal_upper_seven_monomials_power_window hT hξ hMl hMu hNl hNu hHl hHu
    (by dsimp only [ξ]; linarith only [hDiag])
    (by dsimp only [ξ]; linarith only [hSqrt])
    (by dsimp only [ξ]; linarith only [hCubic])
    (by dsimp only [ξ]; linarith only [hEndpoint])
    (by dsimp only [ξ]; linarith only [hType1])
    (by dsimp only [ξ]; linarith only [hType2])
    (by dsimp only [ξ]; linarith only [hPair])
  have hh1 : h≤1 := by linarith only [hhℓ,hu,hδw]
  have hHT : (H:ℝ)≤T := hHu.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT hh1)
  have hLoss := hTogether.2 H hH2 hHT
  have hCsrc0 := zero_le_one.trans hCsrc
  have hLog0 : 0≤(1+(Nat.clog 2 H:ℝ))^36 := pow_nonneg (by positivity) _
  have hXpow0 := Real.rpow_nonneg hTp.le (3*εs)
  have hPower : ‖Expdb.exponentialSumAt F T M a b‖^72≤T^(72*β) := by
    rw [←hEnd]
    calc
      _ ≤ Csrc*(1+(Nat.clog 2 H:ℝ))^36*T^(3*εs)*
          (1+ (M^72/(H:ℝ)^36+
            ((M^72/(N:ℝ)^18+M^216/((H:ℝ)^36*T^36*(N:ℝ)^108)+
                T^12*(H:ℝ)^12*(N:ℝ)^72/M^12)+
              (T^3*M^57+M^69/(N:ℝ)^9+T^2*(H:ℝ)^2*M^64/(N:ℝ)^12)))) := hActual
      _ ≤ Csrc*(1+(Nat.clog 2 H:ℝ))^36*T^(3*εs)*((8*(2:ℝ)^144)*T^ξ) :=
        mul_le_mul_of_nonneg_left hPoly (mul_nonneg (mul_nonneg hCsrc0 hLog0) hXpow0)
      _ = (Csrc*(8*(2:ℝ)^144)*(1+(Nat.clog 2 H:ℝ))^36)*T^(3*εs)*T^ξ := by ac_rfl
      _ ≤ T^ζ*T^(3*εs)*T^ξ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hLoss hXpow0) (Real.rpow_nonneg hTp.le _)
      _ = T^(72*β) := by
        rw [←Real.rpow_add hTp,←Real.rpow_add hTp]
        apply congrArg (fun x : ℝ => T^x)
        dsimp only [ξ]
        ring
  have hRootPower : (T^β)^72=T^(72*β) := by
    simpa only [Nat.cast_ofNat,mul_comm] using (Real.rpow_mul_natCast hTp.le β 72).symm
  have hRoot : ‖Expdb.exponentialSumAt F T M a b‖≤T^β :=
    le_of_pow_le_pow_left₀ (by norm_num : (72:ℕ)≠0)
      (Real.rpow_nonneg hTp.le _) (hPower.trans_eq hRootPower.symm)
  calc
    _ ≤ T^β := hRoot
    _ ≤ T^(β+ε) := Real.rpow_le_rpow_of_exponent_le hT (le_add_of_nonneg_right hε.le)
    _ ≤ C*T^(β+ε) := le_mul_of_one_le_left (Real.rpow_nonneg hTp.le _) hC

private theorem upperOriginal_upper_seventh_row_nonAsymptotic
    {α : ℝ≥0} (hα : 861996/2811205≤(α:ℝ)) (hα₁ : (α:ℝ)≤87/275) :
    Expdb.IsExponentSumBoundNonAsymptotic α ((13+94*(α:ℝ))/146) := by
  let t : ℝ := ((α:ℝ)-861996/2811205)/(87/275-861996/2811205)
  let ν : ℝ := (1-t)*(92661/1000000)+t*(108591/1000000)
  let h : ℝ := (1-t)*(41183/1000000)+t*(48263/1000000)
  apply upperOriginal_upper_beta_of_power_window
    (δw:=1/1000000000000) (ν:=ν) (h:=h) (εs:=1/100000000) (ζ:=1/100000000)
  all_goals norm_num [ν,h,t]
  all_goals linarith only [hα,hα₁]

                                                                              
                                                                            
                                                                        
theorem exponentSumGrowthExponent_le_huxley_seventhRow
    {α : ℝ≥0} (hα : 861996/2811205≤(α:ℝ)) (hα₁ : (α:ℝ)≤87/275) :
    Expdb.exponentSumGrowthExponent α ≤ (13+94*(α:ℝ))/146 := by
  exact Expdb.exponentSumGrowthExponent_le_iff_nonAsymptotic.mpr
    (upperOriginal_upper_seventh_row_nonAsymptotic hα hα₁)

private theorem upperOriginal_upper_eighth_row_nonAsymptotic
    {α : ℝ≥0} (hα : 87/275≤(α:ℝ)) (hα₁ : (α:ℝ)≤423/1295) :
    Expdb.IsExponentSumBoundNonAsymptotic α ((11+191*(α:ℝ))/244) := by
  let t : ℝ := ((α:ℝ)-87/275)/(423/1295-87/275)
  let ν : ℝ := (1-t)*(108591/1000000)+t*(116002/1000000)
  let h : ℝ := (1-t)*(48263/1000000)+t*(52767/1000000)
  apply upperOriginal_upper_beta_of_power_window
    (δw:=1/1000000000000) (ν:=ν) (h:=h) (εs:=1/100000000) (ζ:=1/100000000)
  all_goals norm_num [ν,h,t]
  all_goals linarith only [hα,hα₁]

                                                                             
                                                                            
                                                                        
theorem exponentSumGrowthExponent_le_huxley_eighthRow
    {α : ℝ≥0} (hα : 87/275≤(α:ℝ)) (hα₁ : (α:ℝ)≤423/1295) :
    Expdb.exponentSumGrowthExponent α ≤ (11+191*(α:ℝ))/244 := by
  exact Expdb.exponentSumGrowthExponent_le_iff_nonAsymptotic.mpr
    (upperOriginal_upper_eighth_row_nonAsymptotic hα hα₁)


public  theorem middleOriginal_lower_physical_family_monomial_bound
    {Y M N R Q U V Jsep D Cdelta Clower Cv B delta : ℝ}
    (hY : 0 ≤ Y) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q)
    (hJ : 0 ≤ Jsep) (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta)
    (hCl : 0 ≤ Clower) (hCv : 0 ≤ Cv) (hB : 0 < B) (hd : 0 ≤ delta)
    (hVlower : V ≤ Cv*M^2/N^4) (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    (Y^10*M^10*N^2*R^8/Q^14)*
        (V*D*Y*(M/N)*(1+delta*Jsep)+Y^2*V*(Clower*R^4/(N^2*U))) ≤
      Cv*(D*(Y^11*M^13/(N^3*R^6))+
        D*Cdelta*(Y^11*Jsep*M^13/(N^5*R^4))+
        2*B*Clower*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))) := by
  have hQ : 0 < Q := hR.trans_le hRQ
  have hU := (physical_reference_reciprocal_bound hN hQ hB hUlower).1
  let Cv' := Cv*M^2/(N^2*R^4)
  let Cu' := Clower*R^4*N^2/M^2
  have hCv' : 0 ≤ Cv' := by dsimp only [Cv']; positivity
  have hCu' : 0 ≤ Cu' := by dsimp only [Cu']; positivity
  have hVupper : V ≤ Cv'*R^4/N^2 := by
    convert hVlower using 1
    dsimp only [Cv']
    field_simp
  have hh := upper_physical_family_monomial_bound hY hM.le hN hR hRQ
    hJ hD hCd hCu' hCv' hB hd hVupper hdelta hUlower
  calc
    _ = (Y^10*M^10*N^2*R^8/Q^14)*
        (V*D*Y*(M/N)*(1+delta*Jsep)+Y^2*V*(Cu'*M^2/(N^4*U))) := by
      dsimp only [Cu']
      field_simp
    _ ≤ Cv'*(D*(Y^11*M^11/(N*R^2))+
        D*Cdelta*(Y^11*Jsep*M^11/N^3)+
        2*B*Cu'*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))) := hh
    _ = _ := by
      dsimp only [Cv',Cu']
      field_simp

private theorem middleOriginal_physical_large_pair_monomial_bound
    {Y M N R Q C : ℝ}
    (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q) (hC : 0 ≤ C) :
    (Y^10*M^10*N^2*R^8/Q^14)*
        (Y^2*(C*M^2*R^4/N^6*(Q/N)^((2:ℝ)/3))) ≤
      C*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) := by
  have hQ : 0 < Q := hR.trans_le hRQ
  have hmono := physical_denominator_rpow_decay 14 hR hRQ hN (by norm_num : (2:ℝ)/3 ≤ 14)
  calc
    _ = (C*Y^12*M^12*R^12/N^4)*((Q/N)^((2:ℝ)/3)/Q^14) := by field_simp
    _ ≤ (C*Y^12*M^12*R^12/N^4)*((R/N)^((2:ℝ)/3)/R^14) :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = _ := by field_simp

private theorem middleOriginal_general_physical_family_monomial_bound
    {Y M N R Q U Jsep D Cdelta Cupper Clower Clarge B delta : ℝ}
    (hY : 0 ≤ Y) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q)
    (hJ : 0 ≤ Jsep) (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta)
    (hCu : 0 ≤ Cupper) (hCl : 0 ≤ Clower) (hCb : 0 ≤ Clarge)
    (hB : 1 ≤ B) (hd : 0 ≤ delta)
    (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hUupper : U ≤ (N/Q)^((2:ℝ)/3)/B)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    let V := U^((3:ℝ)/2)
    (Y^10*M^10*N^2*R^8/Q^14)*
        (V*D*Y*(M/N)*(1+delta*Jsep)+
          Y^2*(V*(Cupper*M^2/(N^4*U)+Clower*R^4/(N^2*U))+
            Clarge*M^2*R^4/N^6*(Q/N)^((2:ℝ)/3))) ≤
      D*(Y^11*M^11*N^2/R^7)+
        D*Cdelta*(Y^11*Jsep*M^11/R^5)+
        2*B*Cupper*(Y^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3))+
        2*B*Clower*(Y^12*M^10*N/R^3*(R/N)^((2:ℝ)/3))+
        Clarge*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) := by
  intro V
  have hQ : 0 < Q := hR.trans_le hRQ
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hU := (physical_reference_reciprocal_bound hN hQ hBp hUlower).1
  have hUbound : U ≤ (N/R)^((2:ℝ)/3) := by
    calc
      _ ≤ (N/Q)^((2:ℝ)/3)/B := hUupper
      _ ≤ (N/Q)^((2:ℝ)/3) := div_le_self (by positivity) hB
      _ ≤ (N/R)^((2:ℝ)/3) :=
        Real.rpow_le_rpow (by positivity)
          (div_le_div_of_nonneg_left hN.le hR hRQ) (by norm_num)
  have hVbound : V ≤ N/R := by
    have hh := Real.rpow_le_rpow hU.le hUbound (by norm_num : (0:ℝ) ≤ 3/2)
    have he : ((N/R)^((2:ℝ)/3))^((3:ℝ)/2)=N/R := by
      rw [←Real.rpow_mul (div_pos hN hR).le]
      norm_num
    exact hh.trans_eq he
  let Cvu := N^3/R^5
  let Cvl := N^5/(M^2*R)
  have hCvu : 0 ≤ Cvu := by dsimp only [Cvu]; positivity
  have hCvl : 0 ≤ Cvl := by dsimp only [Cvl]; positivity
  have hVu : V ≤ Cvu*R^4/N^2 := by
    convert hVbound using 1
    dsimp only [Cvu]
    field_simp
  have hVl : V ≤ Cvl*M^2/N^4 := by
    convert hVbound using 1
    dsimp only [Cvl]
    field_simp
  have hu := upper_physical_family_monomial_bound hY hM.le hN hR hRQ
    hJ hD hCd hCu hCvu hBp hd hVu hdelta hUlower
  have hl := middleOriginal_lower_physical_family_monomial_bound hY hM hN hR hRQ
    hJ (show (0:ℝ) ≤ 0 by rfl) hCd hCl hCvl hBp hd hVl hdelta hUlower
  have hb := middleOriginal_physical_large_pair_monomial_bound (Y:=Y) (M:=M) hN hR hRQ hCb
  convert add_le_add (add_le_add hu hl) hb using 1
  · ring
  · dsimp only [Cvu,Cvl]
    field_simp
    ring

private theorem middleOriginal_general_selected_grid_family_bound
    {Y Z P M N R Q U K Jsep D Cdelta Cupper Clower Clarge B delta Cmesh Ccard L T ε : ℝ}
    (hY : 0≤Y) (hZ : 0≤Z) (hZY : Z≤Y) (hP : 0≤P)
    (hM : 0<M) (hN : 0<N) (hR : 0<R) (hRQ : R≤Q) (hK : 0<K)
    (hJ : 0≤Jsep) (hD : 0≤D) (hCd : 0≤Cdelta)
    (hCu : 0≤Cupper) (hCl : 0≤Clower) (hCb : 0≤Clarge)
    (hB : 1≤B) (hd : 0≤delta) (hCm : 0<Cmesh) (hT : 1≤T) (hε : 0≤ε)
    (hQN : Q≤N) (hNR : N≤R^2) (hNT : N≤T)
    (hmesh : K≤Cmesh*Q*N/R^2)
    (hcard : P≤Ccard*Y*M*R^2/(N*Q^2)*L)
    (hdelta : delta≤Cdelta*R^2/N^2)
    (hUupper : U≤(N/Q)^((2:ℝ)/3)/B)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B)≤U) :
    let V := U^((3:ℝ)/2)
    (R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10*
      (V*D*Z*(M/N)*(1+delta*Jsep)+
        Z^2*(V*(Cupper*M^2/(N^4*U)+Clower*R^4/(N^2*U))+
          Clarge*M^2*R^4/N^6*(Q/N)^((2:ℝ)/3))*T^ε) ≤
      (Cmesh^12*Cmesh^ε*(2*Ccard)^10)*T^(2*ε)*L^10*
        (D*(Y^11*M^11*N^2/R^7)+D*Cdelta*(Y^11*Jsep*M^11/R^5)+
          2*B*Cupper*(Y^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3))+
          2*B*Clower*(Y^12*M^10*N/R^3*(R/N)^((2:ℝ)/3))+
          Clarge*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))) := by
  intro V
  have hQ := hR.trans_le hRQ
  have hBp := zero_lt_one.trans_le hB
  have hU := (physical_reference_reciprocal_bound hN hQ hBp hUlower).1
  have hV : 0≤V := Real.rpow_nonneg hU.le _
  have hTp := zero_lt_one.trans_le hT
  have hTpow : 1≤T^ε := Real.one_le_rpow hT hε
  let TypeI := V*D*Y*(M/N)*(1+delta*Jsep)
  let Pair := Y^2*(V*(Cupper*M^2/(N^4*U)+Clower*R^4/(N^2*U))+
    Clarge*M^2*R^4/N^6*(Q/N)^((2:ℝ)/3))
  let Cpref := Cmesh^12*Cmesh^ε*(2*Ccard)^10
  let Physical := Y^10*M^10*N^2*R^8/Q^14
  have hTypeI : 0≤TypeI := by dsimp only [TypeI]; positivity
  have hPair : 0≤Pair := by dsimp only [Pair]; positivity
  have hCpref : 0≤Cpref := by dsimp only [Cpref]; positivity
  have hPhysical : 0≤Physical := by dsimp only [Physical]; positivity
  have hmass : V*D*Z*(M/N)*(1+delta*Jsep)+
      Z^2*(V*(Cupper*M^2/(N^4*U)+Clower*R^4/(N^2*U))+
        Clarge*M^2*R^4/N^6*(Q/N)^((2:ℝ)/3))*T^ε ≤ (TypeI+Pair)*T^ε := by
    calc
      _ ≤ TypeI+Pair*T^ε := by dsimp only [TypeI,Pair]; gcongr
      _ ≤ TypeI*T^ε+Pair*T^ε :=
        add_le_add (le_mul_of_one_le_right hTypeI hTpow) le_rfl
      _ = _ := (add_mul _ _ _).symm
  have hpref := selected_band_mesh_cardinality_prefactor_bound
    hN hR hQ hK hP hCm hε hQN hNR hNT hmesh hcard
  have hmonomial := middleOriginal_general_physical_family_monomial_bound
    hY hM hN hR hRQ hJ hD hCd hCu hCl hCb hB hd hdelta hUupper hUlower
  have hTproduct : T^ε*T^ε=T^(2*ε) := by
    rw [←Real.rpow_add hTp]
    apply congrArg (fun x : ℝ => T^x)
    ring
  calc
    _ ≤ (Cpref*T^ε*L^10*Physical)*((TypeI+Pair)*T^ε) :=
      mul_le_mul hpref hmass (by positivity) (by positivity)
    _ = Cpref*T^(2*ε)*L^10*(Physical*(TypeI+Pair)) := by
      calc
        _ = Cpref*(T^ε*T^ε)*L^10*(Physical*(TypeI+Pair)) := by ring
        _ = _ := by rw [hTproduct]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmonomial (by positivity)

private theorem middleOriginal_general_selected_grid_family_total_bound
    {Y Z P M N R Q U K Jsep D Cdelta Cupper Clower Clarge B delta Cmesh Ccard L T ε Couter : ℝ}
    (hY : 0≤Y) (hZ : 0≤Z) (hZY : Z≤Y) (hP : 0≤P)
    (hM : 0<M) (hN : 0<N) (hR : 0<R) (hRQ : R≤Q) (hK : 0<K)
    (hJ : 0≤Jsep) (hD : 0≤D) (hCd : 0≤Cdelta)
    (hCu : 0≤Cupper) (hCl : 0≤Clower) (hCb : 0≤Clarge)
    (hB : 1≤B) (hd : 0≤delta) (hCm : 0<Cmesh) (hT : 1≤T) (hε : 0≤ε)
    (hCo : 0≤Couter)
    (hQN : Q≤N) (hNR : N≤R^2) (hNT : N≤T)
    (hmesh : K≤Cmesh*Q*N/R^2)
    (hcard : P≤Ccard*Y*M*R^2/(N*Q^2)*L)
    (hdelta : delta≤Cdelta*R^2/N^2)
    (hUupper : U≤(N/Q)^((2:ℝ)/3)/B)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B)≤U) :
    let V := U^((3:ℝ)/2)
    Couter*(R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10*
      (V*D*Z*(M/N)*(1+delta*Jsep)+
        Z^2*(V*(Cupper*M^2/(N^4*U)+Clower*R^4/(N^2*U))+
          Clarge*M^2*R^4/N^6*(Q/N)^((2:ℝ)/3))*T^ε) ≤
      (Couter*(Cmesh^12*Cmesh^ε*(2*Ccard)^10)*(7/6:ℝ)*
        (D+D*Cdelta+2*B*(Cupper+Clower+Clarge)))*T^(2*ε)*L^10*
        (Y^11*M^11*N^2/R^7+Y^11*Jsep*M^11/R^5+
          Y^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3)+
          Y^12*M^10*N/R^3*(R/N)^((2:ℝ)/3)+
          Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) := by
  intro V
  let m₁ := Y^11*M^11*N^2/R^7
  let m₂ := Y^11*Jsep*M^11/R^5
  let m₃ := Y^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3)
  let m₄ := Y^12*M^10*N/R^3*(R/N)^((2:ℝ)/3)
  let m₅ := Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)
  let Cmass := D+D*Cdelta+2*B*(Cupper+Clower+Clarge)
  let Cpref := Cmesh^12*Cmesh^ε*(2*Ccard)^10
  have hBp := zero_lt_one.trans_le hB
  have hm₁ : 0 ≤ m₁ := by dsimp only [m₁]; positivity
  have hm₂ : 0 ≤ m₂ := by dsimp only [m₂]; positivity
  have hm₃ : 0 ≤ m₃ := by dsimp only [m₃]; positivity
  have hm₄ : 0 ≤ m₄ := by dsimp only [m₄]; positivity
  have hm₅ : 0 ≤ m₅ := by dsimp only [m₅]; positivity
  have hDc := mul_nonneg hD hCd
  have hUc : 0≤2*B*Cupper := by positivity
  have hLc : 0≤2*B*Clower := by positivity
  have hBc : 0≤2*B*Clarge := by positivity
  have hBig : Clarge≤2*B*Clarge :=
    le_mul_of_one_le_left hCb (by linarith only [hB])
  have hDmass : D≤Cmass := by dsimp only [Cmass]; nlinarith only [hDc,hUc,hLc,hBc]
  have hDcmass : D*Cdelta≤Cmass := by dsimp only [Cmass]; nlinarith only [hD,hUc,hLc,hBc]
  have hUcmass : 2*B*Cupper≤Cmass := by dsimp only [Cmass]; nlinarith only [hD,hDc,hLc,hBc]
  have hLcmass : 2*B*Clower≤Cmass := by dsimp only [Cmass]; nlinarith only [hD,hDc,hUc,hBc]
  have hBcmass : Clarge≤Cmass := by
    apply hBig.trans
    dsimp only [Cmass]
    nlinarith only [hD,hDc,hUc,hLc]
  have hWeighted : D*m₁+D*Cdelta*m₂+2*B*Cupper*m₃+2*B*Clower*m₄+Clarge*m₅ ≤
      Cmass*(m₁+m₂+m₃+m₄+m₅) := by
    calc
      _ ≤ Cmass*m₁+Cmass*m₂+Cmass*m₃+Cmass*m₄+Cmass*m₅ :=
        add_le_add (add_le_add (add_le_add
          (add_le_add (mul_le_mul_of_nonneg_right hDmass hm₁)
            (mul_le_mul_of_nonneg_right hDcmass hm₂))
          (mul_le_mul_of_nonneg_right hUcmass hm₃))
          (mul_le_mul_of_nonneg_right hLcmass hm₄))
          (mul_le_mul_of_nonneg_right hBcmass hm₅)
      _ = _ := by ring
  have hCpref : 0≤Cpref := by dsimp only [Cpref]; positivity
  have hCmass : 0≤Cmass := hD.trans hDmass
  have hCmassScale : Cmass≤(7/6:ℝ)*Cmass :=
    le_mul_of_one_le_left hCmass (by norm_num)
  have hSum : 0 ≤ m₁+m₂+m₃+m₄+m₅ :=
    add_nonneg (add_nonneg (add_nonneg (add_nonneg hm₁ hm₂) hm₃) hm₄) hm₅
  have hWeighted' := hWeighted.trans (mul_le_mul_of_nonneg_right hCmassScale hSum)
  have hraw := middleOriginal_general_selected_grid_family_bound
    hY hZ hZY hP hM hN hR hRQ hK hJ hD hCd hCu hCl hCb hB hd hCm hT hε
    hQN hNR hNT hmesh hcard hdelta hUupper hUlower
  have hpref : 0≤Cpref*T^(2*ε)*L^10 :=
    mul_nonneg (mul_nonneg hCpref (Real.rpow_nonneg (zero_le_one.trans hT) _)) (by positivity)
  calc
    _ = Couter*((R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10*
        (V*D*Z*(M/N)*(1+delta*Jsep)+
          Z^2*(V*(Cupper*M^2/(N^4*U)+Clower*R^4/(N^2*U))+
            Clarge*M^2*R^4/N^6*(Q/N)^((2:ℝ)/3))*T^ε)) := by simp only [mul_assoc]
    _ ≤ Couter*(Cpref*T^(2*ε)*L^10*
        (D*m₁+D*Cdelta*m₂+2*B*Cupper*m₃+2*B*Clower*m₄+Clarge*m₅)) :=
      mul_le_mul_of_nonneg_left hraw hCo
    _ ≤ Couter*(Cpref*T^(2*ε)*L^10*((7/6:ℝ)*Cmass*(m₁+m₂+m₃+m₄+m₅))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hWeighted' hpref) hCo
    _ = _ := by
      change Couter*(Cpref*T^(2*ε)*L^10*((7/6:ℝ)*Cmass*(m₁+m₂+m₃+m₄+m₅))) =
        (Couter*Cpref*(7/6:ℝ)*Cmass)*T^(2*ε)*L^10*(m₁+m₂+m₃+m₄+m₅)
      ac_rfl

private theorem middleOriginal_general_radius_main_bound
    {Ysmall Y M N R S D J : ℝ}
    (hYsmall : 0≤Ysmall) (hY : Ysmall≤Y) (hM : 0<M) (hN : 0<N)
    (hR : 0<R) (hS : 0<S) (hD : 1≤D) (hJ : 0≤J)
    (hSR : S≤D*R) (hRS : R≤D*S) :
    Ysmall^11*M^11*N^2/S^7+Ysmall^11*J*M^11/S^5+
      Ysmall^12*M^12/(N*S^7)*(S/N)^((2:ℝ)/3)+
      Ysmall^12*M^10*N/S^3*(S/N)^((2:ℝ)/3)+
      Ysmall^12*M^12/(N^4*S^2)*(S/N)^((2:ℝ)/3) ≤
    D^8*(Y^11*M^11*N^2/R^7+Y^11*J*M^11/R^5+
      Y^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3)+
      Y^12*M^10*N/R^3*(R/N)^((2:ℝ)/3)+
      Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) := by
  have hY0 := hYsmall.trans hY
  have hD0 := zero_le_one.trans hD
  have hInv (j : ℕ) : 1/S^j≤D^j/R^j := by
    apply (div_le_div_iff₀ (pow_pos hS j) (pow_pos hR j)).mpr
    simpa only [one_mul,mul_pow] using pow_le_pow_left₀ hR.le hRS j
  have hi₇ := hInv 7
  have hi₅ := hInv 5
  have hi₃ := hInv 3
  have hi₂ := hInv 2
  have hFor := (upperOriginal_comparable_radius_powers hN hR hS hD hSR hRS).2.2.2
  have hD78 : D^7≤D^8 := pow_le_pow_right₀ hD (by norm_num)
  have hD58 : D^5≤D^8 := pow_le_pow_right₀ hD (by norm_num)
  have hD48 : D^4≤D^8 := pow_le_pow_right₀ hD (by norm_num)
  have hD38 : D^3≤D^8 := pow_le_pow_right₀ hD (by norm_num)
  have h₁ : Ysmall^11*M^11*N^2/S^7≤D^8*(Y^11*M^11*N^2/R^7) := by
    calc
      _ = (Ysmall^11*M^11*N^2)*(1/S^7) := by ring
      _ ≤ (Y^11*M^11*N^2)*(D^7/R^7) := by gcongr
      _ = D^7*(Y^11*M^11*N^2/R^7) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD78 (by positivity)
  have h₂ : Ysmall^11*J*M^11/S^5≤D^8*(Y^11*J*M^11/R^5) := by
    calc
      _ = (Ysmall^11*J*M^11)*(1/S^5) := by ring
      _ ≤ (Y^11*J*M^11)*(D^5/R^5) := by gcongr
      _ = D^5*(Y^11*J*M^11/R^5) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD58 (by positivity)
  have h₃ : Ysmall^12*M^12/(N*S^7)*(S/N)^((2:ℝ)/3)≤
      D^8*(Y^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3)) := by
    calc
      _ = (Ysmall^12*M^12/N)*(1/S^7)*(S/N)^((2:ℝ)/3) := by ring
      _ ≤ (Y^12*M^12/N)*(D^7/R^7)*(D*(R/N)^((2:ℝ)/3)) := by gcongr
      _ = _ := by ring
  have h₄ : Ysmall^12*M^10*N/S^3*(S/N)^((2:ℝ)/3)≤
      D^8*(Y^12*M^10*N/R^3*(R/N)^((2:ℝ)/3)) := by
    calc
      _ = (Ysmall^12*M^10*N)*(1/S^3)*(S/N)^((2:ℝ)/3) := by ring
      _ ≤ (Y^12*M^10*N)*(D^3/R^3)*(D*(R/N)^((2:ℝ)/3)) := by gcongr
      _ = D^4*(Y^12*M^10*N/R^3*(R/N)^((2:ℝ)/3)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD48 (by positivity)
  have h₅ : Ysmall^12*M^12/(N^4*S^2)*(S/N)^((2:ℝ)/3)≤
      D^8*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) := by
    calc
      _ = (Ysmall^12*M^12/N^4)*(1/S^2)*(S/N)^((2:ℝ)/3) := by ring
      _ ≤ (Y^12*M^12/N^4)*(D^2/R^2)*(D*(R/N)^((2:ℝ)/3)) := by gcongr
      _ = D^3*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD38 (by positivity)
  calc
    _ ≤ D^8*(Y^11*M^11*N^2/R^7)+D^8*(Y^11*J*M^11/R^5)+
        D^8*(Y^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3))+
        D^8*(Y^12*M^10*N/R^3*(R/N)^((2:ℝ)/3))+
        D^8*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) :=
      add_le_add (add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄) h₅
    _ = _ := by ring

private theorem middleOriginal_general_expression_nonnegative
    {Y M N R J : ℝ} (hY : 0 ≤ Y) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hR : 0 < R) (hJ : 0 ≤ J) :
    0 ≤ Y^11*M^11*N^2/R^7+Y^11*J*M^11/R^5+
      Y^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3)+
      Y^12*M^10*N/R^3*(R/N)^((2:ℝ)/3)+
      Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3) := by
  positivity

private theorem middleOriginal_eventually_general_finite_numerical_consequence
    {σsrc csrc Usrc κ Cphys Csrc Couter CUP CLOW CLARGE Dtype Bselect Csep ε : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) (hκ : 0 < κ)
    (hCphys : 0 ≤ Cphys) (hCsrcZero : 0 ≤ Csrc) (hCouter : 0 ≤ Couter)
    (hCUP : 0 ≤ CUP) (hCLOW : 0 ≤ CLOW) (hCLARGE : 0 ≤ CLARGE)
    (hDtype : 0 ≤ Dtype) (hBsOne : 1 ≤ Bselect)
    (hCsep : 1 ≤ Csep) (hε : 0 < ε) :
    let εloss := ε/4
    let Cmesh := 2*max 1 (63*Usrc/(2*σsrc))
    let CtailBand := (6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc
    let ClowBand := (3*Usrc/σsrc+csrc/(32*σsrc))*((3072*σsrc)/csrc)^2+(3072*σsrc)/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Y : Finset ℝ)
      (n N Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ) (R M Jsep : ℝ)
      (Chunks : Finset (ℝ × ℤ)) (band : (ℝ × ℤ) → Option ℕ)
      (Dcover : ℕ → Finset (ℝ × ℤ)) {S : ℝ},
      N=8*n → 2 ≤ N → 1 ≤ R → (N:ℝ) ≤ R^2 → (N:ℝ)^2 ≤ M →
      M ≤ T → 0 ≤ Jsep → T*(N:ℝ)*R^2=M^3 →
      0 < Qbase → (Qbase:ℝ) ≤ 1536*R → (N:ℝ)/Csep ≤ (Qbase*2^kmax:ℕ) →
      (kmax:ℝ) ≤ Real.log N/Real.log 2 → (∀ k, 0 < Kmesh k) →
      let Q := fun k : ℕ => Qbase*2^k
      (∀ k ≤ kmax,
        R ≤ (Q k:ℝ) ∧ Q k ≤ N ∧
        (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
        (Kmesh k:ℝ) ≤ Cmesh*(Q k:ℝ)*(N:ℝ)/R^2 ∧
        (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
        ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Usel k:ℝ)) →
      let Yc := (Y.card:ℝ)
      let μ₀ := csrc*T/(12*σsrc*M^3)
      let U₀ := Usrc*T/(2*σsrc*M^3)
      let Vscale := fun k : ℕ => (Usel k:ℝ)^((3:ℝ)/2)
      let Error := Yc*(M/(N:ℝ)+1)*
        (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
      let Δtype := fun k : ℕ =>
        (16*U₀/μ₀)*Real.sqrt (U₀*(Q k:ℝ)^3)*Real.sqrt (Kmesh k)/(6*(Kmesh k:ℝ)^2)
      let Buffer := fun k : ℕ =>
        (56*(Usel k:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
      let Width := fun k : ℕ => (14*σsrc/csrc)*(Usel k:ℝ)*(N:ℝ)
      let FamilyBound := fun (k : ℕ) (P : Finset (ℝ × ℤ)) =>
        Couter*(R^2/(Q k:ℝ))^6*(Kmesh k:ℝ)^((12:ℝ)+εloss)*(2*(P.card:ℝ))^10*
          ((Vscale k)*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+(Δtype k)*Jsep)+
            ((P.image Prod.fst).card:ℝ)^2*
              ((Vscale k)*(CUP*M^2/((N:ℝ)^4*(Usel k:ℝ))+
                CLOW*R^4/((N:ℝ)^2*(Usel k:ℝ)))+
                CLARGE*M^2*R^4/(N:ℝ)^6*((Q k:ℝ)/(N:ℝ))^((2:ℝ)/3))*T^εloss)
      let Density := fun k => 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
        (2+Real.log (512*σsrc*R^2/(csrc*((Q k:ℝ)/768))+1))
      let Endpoint := Yc*(2*Buffer 0+2*Width 0+6*(N:ℝ)+2*(n:ℝ))
      let Selected := fun k => Chunks.filter (fun p => band p=some k)
      let Grid := fun (k : ℕ) (r : ℤ) =>
        ((Dcover k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
      (Chunks.card:ℝ) ≤ Yc*(8*M/(N:ℝ)) →
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤ Yc*Density k) →
      (∀ k ≤ kmax, ∀ r : ℤ, (Grid k r).card ≤ 2*(Selected k).card) →
      (∀ k ≤ kmax, ∀ r : ℤ, (Grid k r).image Prod.fst ⊆ Y) →
      S ≤ 2^11*(((kmax:ℝ)+2)^11*
        (((n:ℝ)*Yc*Density kmax)^12+
          (4:ℝ)^12*(8:ℝ)^11*∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,
            (2^11*((Csrc*Error)^12+
              (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (Grid k r))))+Endpoint^12) →
      let ErrorTotal := Yc*M/Real.sqrt (N:ℝ)+Yc*M*R^2/(N:ℝ)^2+
        Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
      let Main := Yc^11*M^11*(N:ℝ)^2/R^7+Yc^11*Jsep*M^11/R^5+
        Yc^12*M^12/((N:ℝ)*R^7)*(R/(N:ℝ))^((2:ℝ)/3)+
        Yc^12*M^10*(N:ℝ)/R^3*(R/(N:ℝ))^((2:ℝ)/3)+
        Yc^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
      S ≤ T^ε*(ErrorTotal^12+Main) := by

  classical
  intro εloss Cmesh CtailBand ClowBand CerrorBand
  have hεloss : 0 < εloss := by dsimp only [εloss]; linarith only [hε]
  let Carg := 512*768*σsrc/csrc
  let DensityLog := 3+Real.log (Carg+1)
  let Cdensity := 128*CerrorBand*DensityLog
  let Ccard := 16*(1536:ℝ)^2+8*Cdensity
  let CKlog := 3+Real.log (Cmesh+1)
  let Cband := 2+1/Real.log 2
  let Cdelta := (16*Usrc/csrc)*Real.sqrt ((Usrc/(2*σsrc))*Cmesh)
  let Cmass := Dtype+Dtype*Cdelta+2*Bselect*(CUP+CLOW+CLARGE)
  let Cfamily := Couter*
    (Cmesh^12*Cmesh^εloss*(2*Ccard)^10)*(7/6:ℝ)*Cmass
  let CE₀ := 2*Real.sqrt 3*(1+Real.log 6)+24*σsrc/csrc
  let Cterminal := Cdensity*Csep^2/8
  let Cendpoint := 112/κ+28*σsrc/csrc+2/(Cphys+2)+41/4
  let Cerror := 1+Csrc*CE₀+Cterminal+Cendpoint
  let Cgrid := (2:ℝ)^11*(Cerror^12+(Csrc*CKlog)^12*Cfamily)
  let Ctotal := (2:ℝ)^11*(Cband^11*Cerror^12+
    (4:ℝ)^12*(8:ℝ)^12*Cband^12*Cgrid+Cerror^12)
  have hConstants :
      0 ≤ CtailBand ∧ 0 ≤ ClowBand ∧ 0 ≤ CerrorBand ∧ 1 ≤ Cmesh ∧
      0 ≤ Carg ∧ 0 ≤ DensityLog ∧ 0 ≤ Cdensity ∧ 0 ≤ Ccard ∧
      0 ≤ CKlog ∧ 0 ≤ Cband ∧ 0 ≤ Cdelta ∧ 0 ≤ Cmass ∧
      0 ≤ Cfamily ∧ 0 ≤ CE₀ ∧ 0 ≤ Cterminal ∧ 0 ≤ Cendpoint ∧
      0 ≤ Cerror ∧ Csrc*CE₀ ≤ Cerror ∧ Cterminal ≤ Cerror ∧
      Cendpoint ≤ Cerror ∧ 0 ≤ Cgrid ∧ 0 ≤ Ctotal :=
    upper_numerical_constants_nonnegative (ε:=ε) hσsrc hcsrc hUsrc hκ hCphys hCsrcZero
      hCouter (add_nonneg (add_nonneg hCUP hCLOW) hCLARGE) hDtype hBsOne hCsep
  obtain ⟨hCtailBand,hClowBand,hCerrorBand,hCmeshOne,hCarg,hDensityLog,hCdensity,hCcard,hCKlog,hCband,hCdelta,hCmass,hCfamily,hCE₀,hCterminal,hCendpoint,hCerror,hErrorCompletion,hErrorTerminal,hErrorEndpoint,hCgrid,hCtotal⟩ :=
    hConstants
  have hCmesh : 0 < Cmesh := zero_lt_one.trans_le hCmeshOne
  filter_upwards [eventually_selected_band_logarithmic_absorption hCtotal hε,
    Filter.eventually_ge_atTop (1:ℝ)] with T hAbs hTone
  intro Y n N Qbase kmax Kmesh Usel R M Jsep Chunks band Dcover S
    hNlink hNtwo hR hNR' hNsqM hMT hJsep hscale hQbase hBaseHi hEndLo hkmax hKpos
    Q hvalid Yc μ₀ U₀ Vscale Error Δtype Buffer Width FamilyBound Density Endpoint Selected Grid
    hChunks hBands hGridCount hGridImage hNorm ErrorTotal Main
  have hT : 0 < T := hAbs.1
  have hLogOne : 1 ≤ Real.log T := hAbs.2.1
  have hNreal : (2:ℝ) ≤ N := by exact_mod_cast hNtwo
  have hNp : (0:ℝ) < N := by linarith only [hNreal]
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hNOne : (1:ℝ) ≤ N := by linarith only [hNreal]
  have hM : 0 < M := (sq_pos_of_pos hNp).trans_le hNsqM
  have hNM : (N:ℝ) ≤ M :=
    (by nlinarith only [hNreal] : (N:ℝ) ≤ (N:ℝ)^2).trans hNsqM
  have hNT : (N:ℝ) ≤ T := hNM.trans hMT
  let L := 1+Real.log T
  have hL : 1 ≤ L := by dsimp only [L]; linarith only [hLogOne]
  have hLzero : 0 ≤ L := zero_le_one.trans hL
  have hYc : 0 ≤ Yc := Nat.cast_nonneg _
  have hMain : 0 ≤ Main :=
    middleOriginal_general_expression_nonnegative hYc hM.le hNp.le hRp hJsep
  have hErrorTotal : 0 ≤ ErrorTotal :=
    add_nonneg
      (add_nonneg (div_nonneg (mul_nonneg hYc hM.le) (Real.sqrt_nonneg _))
        (div_nonneg (mul_nonneg (mul_nonneg hYc hM.le) (sq_nonneg R))
          (sq_nonneg (N:ℝ))))
      (mul_nonneg (mul_nonneg hYc hNp.le)
        (Real.rpow_pos_of_pos (div_pos hNp hRp) _).le)
  have hQpos (k : ℕ) : (0:ℝ) < Q k := by
    exact_mod_cast Nat.mul_pos hQbase (by positivity : 0 < 2^k)
  have hKreal (k : ℕ) : (0:ℝ) < Kmesh k := by exact_mod_cast hKpos k
  have hlogs (k : ℕ) (hk : k ≤ kmax) :
      2+Real.log (Carg*R^2/(Q k:ℝ)+1) ≤ DensityLog*L ∧
      1+Real.log (Kmesh k) ≤ CKlog*L ∧
      (kmax:ℝ)+2 ≤ Cband*L := by
    obtain ⟨hRQ,hQN,_,hKU,_,_⟩ := hvalid k hk
    have hQNreal : (Q k:ℝ) ≤ N := by exact_mod_cast hQN
    exact physical_band_logarithmic_bounds hCarg hCmeshOne hTone hR hRQ
      hQNreal hNR' hNT (hKreal k) hKU hkmax
  have hDensity (k : ℕ) (hk : k ≤ kmax) :
      Density k ≤ Cdensity*M*R^2/((N:ℝ)*(Q k:ℝ)^2)*L := by
    have harg : 512*σsrc*R^2/(csrc*((Q k:ℝ)/768))=Carg*R^2/(Q k:ℝ) := by
      dsimp only [Carg]
      field_simp [(hQpos k).ne']
    calc
      _ = 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
          (2+Real.log (Carg*R^2/(Q k:ℝ)+1)) := by
        dsimp only [Density]
        rw [harg]
      _ ≤ 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*(DensityLog*L) :=
        mul_le_mul_of_nonneg_left (hlogs k hk).1 (by positivity)
      _ = _ := by dsimp only [Cdensity]; ring
  have hBandCounts (k : ℕ) (hk : k ≤ kmax) :
      ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        Yc*(Cdensity*M*R^2/((N:ℝ)*(Q k:ℝ)^2)*L) :=
    (hBands k hk).trans (mul_le_mul_of_nonneg_left (hDensity k hk) hYc)
  have hGridCard (k : ℕ) (hk : k ≤ kmax) (r : ℤ) :
      ((Grid k r).card:ℝ) ≤ Ccard*Yc*M*R^2/((N:ℝ)*(Q k:ℝ)^2)*L := by
    exact selected_band_grid_cardinality_bound Chunks band Grid Qbase kmax hQbase
      hYc hM.le hNp hCdensity hL hBaseHi hChunks hBandCounts
      hGridCount k hk r
  have hGridPhase (k : ℕ) (hk : k ≤ kmax) (r : ℤ) :
      (((Grid k r).image Prod.fst).card:ℝ) ≤ Yc := by
    change (((Grid k r).image Prod.fst).card:ℝ) ≤ (Y.card:ℝ)
    exact_mod_cast Finset.card_le_card (hGridImage k hk r)
  have hDeltaType (k : ℕ) (hk : k ≤ kmax) :
      Δtype k ≤ Cdelta*R^2/(N:ℝ)^2 := by
    obtain ⟨_,_,hMesh,hKU,_,_⟩ := hvalid k hk
    exact positive_difference_source_type_spacing_bound hσsrc hcsrc hUsrc.le
      hT hM hNp hRp (hQpos k) (hKreal k) hCmesh.le hscale hMesh hKU
  have hFamily (k : ℕ) (hk : k ≤ kmax) (r : ℤ) :
      FamilyBound k (Grid k r) ≤ Cfamily*T^(2*εloss)*L^10*Main := by
    obtain ⟨hRQ,hQN,_,hKU,hUupper,hUlower⟩ := hvalid k hk
    have hQNreal : (Q k:ℝ) ≤ N := by exact_mod_cast hQN
    have hdeltazero : 0 ≤ Δtype k := by dsimp only [Δtype,U₀,μ₀]; positivity
    exact middleOriginal_general_selected_grid_family_total_bound
      hYc (Nat.cast_nonneg ((Grid k r).image Prod.fst).card) (hGridPhase k hk r)
      (Nat.cast_nonneg (Grid k r).card) hM hNp hRp hRQ (hKreal k)
      hJsep hDtype hCdelta hCUP hCLOW hCLARGE
      hBsOne hdeltazero hCmesh hTone hεloss.le hCouter
      hQNreal hNR' hNT hKU (hGridCard k hk r) (hDeltaType k hk) hUupper hUlower
  let E₁ := Yc*M/Real.sqrt (N:ℝ)
  let E₂ := Yc*M*R^2/(N:ℝ)^2
  let E₃ := Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
  have hE₁ : 0 ≤ E₁ := div_nonneg (mul_nonneg hYc hM.le) (Real.sqrt_nonneg _)
  have hE₂ : 0 ≤ E₂ := div_nonneg (mul_nonneg (mul_nonneg hYc hM.le) (sq_nonneg R))
    (sq_nonneg (N:ℝ))
  have hE₃ : 0 ≤ E₃ := mul_nonneg (mul_nonneg hYc hNp.le)
    (Real.rpow_pos_of_pos (div_pos hNp hRp) _).le
  have hE₁₂Total : E₁+E₂ ≤ ErrorTotal := le_add_of_nonneg_right hE₃
  have hE₂Total : E₂ ≤ ErrorTotal := (le_add_of_nonneg_left hE₁).trans hE₁₂Total
  have hE₃Total : E₃ ≤ ErrorTotal := le_add_of_nonneg_left (add_nonneg hE₁ hE₂)
  have hCompletion : Csrc*Error ≤ Cerror*ErrorTotal*L := by
    have hraw := positive_difference_completion_error_physical_bound
      (R:=R) hYc hNOne hNM hMT (show 0 ≤ 12*σsrc/csrc by positivity)
    have he : Error ≤ CE₀*(E₁+E₂)*L := by
      convert hraw using 1
      · dsimp only [Error]
        ring
      · dsimp only [CE₀,E₁,E₂,L]
        ring
    calc
      _ ≤ Csrc*(CE₀*(E₁+E₂)*L) := mul_le_mul_of_nonneg_left he hCsrcZero
      _ = (Csrc*CE₀)*(E₁+E₂)*L := by simp only [mul_assoc]
      _ ≤ Cerror*ErrorTotal*L :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hErrorCompletion hE₁₂Total (add_nonneg hE₁ hE₂) hCerror) hLzero
  have hNlinkReal : (N:ℝ)=8*(n:ℝ) := by exact_mod_cast hNlink
  have hTerminalBound : (n:ℝ)*Yc*Density kmax ≤ Cerror*ErrorTotal*L := by
    have hnzero : 0 ≤ (n:ℝ)*Yc := mul_nonneg (Nat.cast_nonneg n) hYc
    have hcore := selected_terminal_density_bound (R:=R) hNp hM.le hYc hCdensity
      (zero_lt_one.trans_le hCsep) hLzero hNlinkReal hEndLo
    calc
      _ ≤ (n:ℝ)*Yc*(Cdensity*M*R^2/((N:ℝ)*(Q kmax:ℝ)^2)*L) :=
        mul_le_mul_of_nonneg_left (hDensity kmax le_rfl) hnzero
      _ ≤ Cterminal*E₂*L := hcore
      _ ≤ Cerror*ErrorTotal*L :=
        mul_le_mul_of_nonneg_right (mul_le_mul hErrorTerminal hE₂Total hE₂ hCerror) hLzero
  have hEndpointBound : Endpoint ≤ Cerror*ErrorTotal*L := by
    obtain ⟨hRQ,hQN,_,_,hUupper,_⟩ := hvalid 0 (Nat.zero_le _)
    have hQNreal : (Q 0:ℝ) ≤ N := by exact_mod_cast hQN
    have hraw := positive_difference_endpoint_error_physical_bound
      hYc hNOne hRp hRQ hQNreal hκ hσsrc.le hcsrc hCphys hBsOne hNlinkReal hUupper
    have he : Endpoint ≤ Cendpoint*E₃ := by
      exact hraw
    calc
      _ ≤ Cendpoint*E₃ := he
      _ ≤ Cerror*ErrorTotal := mul_le_mul hErrorEndpoint hE₃Total hE₃ hCerror
      _ ≤ Cerror*ErrorTotal*L := le_mul_of_one_le_right (mul_nonneg hCerror hErrorTotal) hL

  have hLogN : 0 ≤ Real.log (6*(N:ℝ)) :=
    Real.log_nonneg (by linarith only [hNreal])
  have hCompletionZero : 0 ≤ Csrc*Error :=
    mul_nonneg hCsrcZero
      (mul_nonneg (mul_nonneg hYc (add_nonneg (div_nonneg hM.le hNp.le) zero_le_one))
        (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hLogN)
          (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hσsrc.le) (sq_nonneg R))
            (mul_nonneg hcsrc.le hNp.le))))
  have hDensityZero (k : ℕ) : 0 ≤ Density k := by
    have hh : 0 ≤ 512*σsrc*R^2/(csrc*((Q k:ℝ)/768)) :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hσsrc.le) (sq_nonneg R))
        (mul_nonneg hcsrc.le (div_nonneg (hQpos k).le (by norm_num)))
    have harg : 1 ≤ 512*σsrc*R^2/(csrc*((Q k:ℝ)/768))+1 := le_add_of_nonneg_left hh
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hCerrorBand)
        (div_nonneg (mul_nonneg hM.le (sq_nonneg R))
          (mul_nonneg hNp.le (sq_nonneg _))))
      (add_nonneg (by norm_num) (Real.log_nonneg harg))
  have hTerminalZero : 0 ≤ (n:ℝ)*Yc*Density kmax :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hYc) (hDensityZero kmax)
  have hBufferZero : 0 ≤ Buffer 0 :=
    add_nonneg
      (add_nonneg
        (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hκ.le) hNp.le)
        (div_nonneg hNp.le (add_nonneg hCphys (by norm_num)))) (by norm_num)
  have hWidthZero : 0 ≤ Width 0 :=
    mul_nonneg
      (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hσsrc.le) hcsrc.le)
        (Nat.cast_nonneg _)) hNp.le
  have hEndpointZero : 0 ≤ Endpoint :=
    mul_nonneg hYc
      (add_nonneg
        (add_nonneg
          (add_nonneg (mul_nonneg (by norm_num) hBufferZero)
            (mul_nonneg (by norm_num) hWidthZero))
          (mul_nonneg (by norm_num) hNp.le))
        (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
  have hTpowOne : 1 ≤ T^(2*εloss) :=
    Real.one_le_rpow hTone (mul_nonneg (by norm_num) hεloss.le)
  let G := fun k r => 2^11*((Csrc*Error)^12+
    (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (Grid k r))
  have hG (k : ℕ) (hk : k ≤ kmax) (r : ℤ) :
      G k r ≤ Cgrid*T^(2*εloss)*L^22*(ErrorTotal^12+Main) := by
    have hKone : (1:ℝ) ≤ Kmesh k := by
      have hh : 1 ≤ Kmesh k := Nat.succ_le_iff.mpr (hKpos k)
      exact_mod_cast hh
    have hlogK := Real.log_nonneg hKone
    have hLogZero : 0 ≤ Csrc*(1+Real.log (Kmesh k)) :=
      mul_nonneg hCsrcZero (add_nonneg zero_le_one hlogK)
    have hLogBound : Csrc*(1+Real.log (Kmesh k)) ≤ (Csrc*CKlog)*L := by
      calc
        _ ≤ Csrc*(CKlog*L) := mul_le_mul_of_nonneg_left (hlogs k hk).2.1 hCsrcZero
        _ = _ := by simp only [mul_assoc]
    exact selected_grid_completion_bound hCompletionZero hLogZero hMain hCfamily hL hTpowOne
      hCompletion hLogBound (hFamily k hk r)
  have hClean := selected_band_finite_power_cleanup kmax G
    hTerminalZero hEndpointZero hMain hL hTpowOne hCband hCgrid
    (hlogs 0 (Nat.zero_le _)).2.2 hTerminalBound hEndpointBound
    (fun k hk r _ => hG k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) r) hNorm
  have hExp : 2*εloss=ε/2 := by dsimp only [εloss]; ring
  have hFactor : Ctotal*T^(2*εloss)*L^36 ≤ T^ε := by
    simpa only [hExp,L] using hAbs.2.2
  exact hClean.trans (mul_le_mul_of_nonneg_right hFactor
    (add_nonneg (pow_nonneg hErrorTotal 12) hMain))

public  theorem middleOriginal_general_source_constants_nonnegative
    {σ δ κ Usrc σsrc csrc θ Cupper Clower Dupper Dlower : ℝ}
    (hσ : 0 < σ) (hδzero : 0 ≤ δ) (hκ : 0 < κ)
    (hUsrc : 0 < Usrc) (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc)
    (hθ : 0 < θ) (hCU : 0 < Cupper) (hCL : 0 < Clower)
    (hDU : 0 < Dupper) (hDL : 0 < Dlower) :
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
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
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*C₃/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*C₃/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*C₃/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    0 < Cphys ∧
    0 < c ∧
    0 < J ∧
    1 ≤ B ∧
    0 ≤ B ∧
    0 ≤ C₂ ∧
    0 ≤ C₃ ∧
    0 ≤ modelPhaseJetCoefficient σ 4+δ ∧
    0 ≤ quarticReciprocalConstant σ δ ∧
    0 ≤ quarticNonlinearResidualConstant σ δ ∧
    0 ≤ Ct ∧
    0 ≤ Cc ∧
    0 ≤ Ccurv ∧
    0 ≤ Kres ∧
    0 < Esize ∧
    0 ≤ Dbase ∧
    0 ≤ Tbase ∧
    0 < Lunit ∧
    0 < Gamma ∧
    0 ≤ Cthird ∧
    0 ≤ AupperConst ∧
    0 ≤ BupperConst ∧
    0 ≤ DupperConst ∧
    0 ≤ AlowerConst ∧
    0 ≤ BlowerConst ∧
    0 ≤ DlowerConst ∧
    0 ≤ Cpack ∧
    0 ≤ Cfirst ∧
    0 ≤ Cgap ∧
    0 ≤ Cmain ∧
    0 ≤ Ctail := by
  intro Cphys c J B C₂ C₃ Ct Cc Ccurv Kres Esize Dbase Tbase Lunit Gamma Cthird AupperConst BupperConst DupperConst AlowerConst BlowerConst DlowerConst Cpack Cfirst Cgap Cmain Ctail
  have hModelPhase : 0 < modelPhaseThirdLower σ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hc : 0 < c := by dsimp only [c]; positivity
  have hJ : 0 < J := by dsimp only [J]; positivity
  have hB : 1 ≤ B := le_max_left _ _
  have hBzero : 0 ≤ B := zero_le_one.trans hB
  have hC₂ : 0 ≤ C₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδzero
  have hC₃ : 0 ≤ C₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδzero
  have hC₄ : 0 ≤ modelPhaseJetCoefficient σ 4+δ :=
    add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδzero
  have hCR : 0 ≤ quarticReciprocalConstant σ δ := by
    dsimp only [quarticReciprocalConstant]
    positivity
  have hCN : 0 ≤ quarticNonlinearResidualConstant σ δ := by
    dsimp only [quarticNonlinearResidualConstant]
    positivity
  have hCt : 0 ≤ Ct := by dsimp only [Ct]; positivity
  have hCc : 0 ≤ Cc := by dsimp only [Cc]; positivity
  have hCcurv : 0 ≤ Ccurv := by dsimp only [Ccurv]; positivity
  have hKres : 0 ≤ Kres := by dsimp only [Kres]; positivity
  have hEsize : 0 < Esize := by dsimp only [Esize]; positivity
  have hDbase : 0 ≤ Dbase := by dsimp only [Dbase]; positivity
  have hTbase : 0 ≤ Tbase := by dsimp only [Tbase]; positivity
  have hLunit : 0 < Lunit := by dsimp only [Lunit]; positivity
  have hGamma : 0 < Gamma := by dsimp only [Gamma]; positivity
  have hCthird : 0 ≤ Cthird := by dsimp only [Cthird]; positivity
  have hAupper : 0 ≤ AupperConst := by dsimp only [AupperConst]; positivity
  have hBupper : 0 ≤ BupperConst := by dsimp only [BupperConst]; positivity
  have hDupper : 0 ≤ DupperConst := by dsimp only [DupperConst]; positivity
  have hAlower : 0 ≤ AlowerConst := by dsimp only [AlowerConst]; positivity
  have hBlower : 0 ≤ BlowerConst := by dsimp only [BlowerConst]; positivity
  have hDlower : 0 ≤ DlowerConst := by dsimp only [DlowerConst]; positivity
  have hCpack : 0 ≤ Cpack := by dsimp only [Cpack]; positivity
  have hCfirst : 0 ≤ Cfirst := by dsimp only [Cfirst]; positivity
  have hCgap : 0 ≤ Cgap := by dsimp only [Cgap]; positivity
  have hCmain : 0 ≤ Cmain :=
    add_nonneg
      (mul_nonneg (by norm_num) (Real.rpow_nonneg
        (div_nonneg (mul_nonneg (by norm_num) hCfirst) (pow_nonneg hLunit.le 3)) _))
      (by norm_num)
  have hCtail : 0 ≤ Ctail :=
    add_nonneg (div_nonneg (mul_nonneg (by norm_num) hCpack) (sq_nonneg Lunit)) hCgap
  exact ⟨hCphys,hc,hJ,hB,hBzero,hC₂,hC₃,hC₄,hCR,hCN,hCt,hCc,hCcurv,hKres,hEsize,hDbase,hTbase,hLunit,hGamma,hCthird,hAupper,hBupper,hDupper,hAlower,hBlower,hDlower,hCpack,hCfirst,hCgap,hCmain,hCtail⟩

private theorem middleOriginal_eventually_general_quantitative_phase_subinterval_bound
    {σsrc csrc Usrc σ δ ε : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hδzero : 0 ≤ δ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hε : 0 < ε)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    ∃ Cbudget η₀ : ℝ, 1 ≤ Cbudget ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (n N : ℕ) (R Jsep : ℝ) {η M : ℝ},
      N=8*n → 2 ≤ N → 1 ≤ R → 0 < η → η ≤ η₀ →
      0 < Jsep → Jsep ≤ M →
      (∀ y∈Y, y∈Icc (1:ℝ) 2) →
      (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j ≤ 6, |iteratedDeriv (j+1) Fsrc w| ≤ Usrc) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
      (∀ y∈Y, Expdb.IsApproximateModelPhaseFunction
        (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
      T*(N:ℝ)*R^2=M^3 →
      Cbudget*R ≤ N → Cbudget*(N:ℝ) ≤ R^2 → Cbudget*(N:ℝ)^2 ≤ M →
      (N:ℝ)^4 ≤ M*R^3 → (N:ℝ)^10 ≤ M^3*R^7 →
      ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
      (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
      let Yc := (Y.card:ℝ)
      let ErrorTotal := Yc*M/Real.sqrt (N:ℝ)+Yc*M*R^2/(N:ℝ)^2+
        Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
      let Main := Yc^11*M^11*(N:ℝ)^2/R^7+Yc^11*Jsep*M^11/R^5+
        Yc^12*M^12/((N:ℝ)*R^7)*(R/(N:ℝ))^((2:ℝ)/3)+
        Yc^12*M^10*(N:ℝ)/R^3*(R/(N:ℝ))^((2:ℝ)/3)+
        Yc^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),
        (𝐞 (T*(Fsrc ((j:ℝ)/M)-Fsrc ((j:ℝ)/M+η*y))/(σsrc*η)):ℂ)‖)^12 ≤
        T^ε*(ErrorTotal^12+Main) := by

  classical
  let εloss := ε/4
  have hεloss : 0 < εloss := by dsimp only [εloss]; linarith only [hε]
  let κ := modelPhaseThirdLower σ
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
  let Lsource := max (8*Ratio^2)
    (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
  have hLsource : 0 ≤ Lsource :=
    (by positivity : (0:ℝ) ≤ 8*Ratio^2).trans (le_max_left _ _)
  let θ := min (1/48:ℝ) (1/(16*(Lsource+3)))
  have hθ : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθmax : θ ≤ 1/24 := (min_le_left _ _).trans (by norm_num)
  have hθaction : θ ≤ 1/(8*(Lsource+3)) := by
    apply (min_le_right _ _).trans
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (by nlinarith only [hLsource])
  obtain ⟨Csrc,η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,hfinite⟩ :=
    HuxleyRationalPhase.eventually_positive_difference_selected_band_phase_subinterval_physical_sieve
      hσsrc hcsrc hUsrc hσ hεloss hanchorBudget
  let Cphys := σ*(σ+1)+1
  let c := κ/6
  let J := Cphys/6
  let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
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
  let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
  let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
  let DupperConst := θ*(3*Usrc/σsrc)*1/2
  let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
  let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
  let DlowerConst := 12*Usrc*θ/(csrc*κ)
  let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*C₃/κ)/κ
  let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*C₃/κ)/κ^2
  let Cgap := 64*Cphys*(Gamma^2*B+Gamma*C₃/κ)/κ
  let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
  let Ctail := 4*Cpack/Lunit^2+Cgap
  obtain ⟨hCphys,hc,hJ,hB,hBzero,hC₂,hC₃,hC₄,hCR,hCN,hCt,hCc,hCcurv,hKres,hEsize,hDbase,hTbase,hLunit,hGamma,hCthird,hAupper,hBupper,hDupper,hAlower,hBlower,hDlower,hCpack,hCfirst,hCgap,hCmain,hCtail⟩ :=
    middleOriginal_general_source_constants_nonnegative hσ hδzero hκ hUsrc hσsrc hcsrc hθ hCU hCL hDU hDL
  let Sector := 2*3840*128^2*105*(Dbase+64*Tbase*Esize^2)
  obtain ⟨Bcut,Bselect,hBcut,hBsOne,hBsSize,hcutMargin,hsize,hBsize⟩ :=
    exists_source_cutoff_margins (Sector:=Sector) hκ hCcurv hCphys.le hEsize
  have hBs : 0 < Bselect := zero_lt_one.trans_le hBsOne
  let D₀ := 37*B/2+16*B*Cc+2*Ct+2*Cc
  have hD₀ : 0 ≤ D₀ := by clear hfinite; dsimp only [D₀]; positivity
  obtain ⟨Csep,hCsep,hselect⟩ :=
    exists_uniform_dyadic_band_integer_scales (J:=Usrc) hσsrc hBsOne hD₀ hCN
  obtain ⟨Cbudget,hCbudget,hCsepBudget,hbudget⟩ :=
    exists_uniform_source_physical_budget (zero_le_one.trans hCsep)
      (show 0 ≤ 3*Usrc/σsrc by positivity)
      (show 0 ≤ 3*Usrc/(4*σsrc) by positivity) hBzero
      (show 0 ≤ 56/κ by positivity)
      (show 0 ≤ 1/(Cphys+2) by positivity)
      (show 0 ≤ 14*σsrc/csrc by positivity)

  let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
  let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
  let Cap := 3*ChartCap*NarrowCap
  have hChartCap : 0 ≤ ChartCap := by clear hfinite; dsimp only [ChartCap]; positivity
  have hNarrowCap : 0 ≤ NarrowCap := by clear hfinite; dsimp only [NarrowCap]; positivity
  have hCap : 0 ≤ Cap := by clear hfinite; dsimp only [Cap]; positivity
  let CUP := 240*(9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+
    2*BupperConst+(3/2:ℝ)*DupperConst)
  have hCUP : 0 ≤ CUP := by clear hfinite; dsimp only [CUP]; positivity
  let CLOW := 240*(9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+
    2*BlowerConst+(3/2:ℝ)*DlowerConst)
  let CLARGE := 2*Bselect*60*588*Ratio^2*(3*Usrc/(2*σsrc))^2*(Cmain+Ctail)
  have hCLOW : 0 ≤ CLOW :=
    mul_nonneg (by norm_num)
      (add_nonneg
        (add_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg
          (mul_nonneg hAlower (sq_nonneg DlowerConst)) _))
          (mul_nonneg (by norm_num) hBlower))
        (mul_nonneg (by norm_num) hDlower))
  have hCLARGE : 0 ≤ CLARGE :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hBs.le)
          (by norm_num)) (by norm_num)) (sq_nonneg Ratio))
        (sq_nonneg (3*Usrc/(2*σsrc))))
      (add_nonneg hCmain hCtail)
  let Couter := (48*σsrc/csrc)^6*C*Cap^11
  have hCouter : 0 ≤ Couter := by clear hfinite; dsimp only [Couter]; positivity
  let CtailBand := (6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc
  let ClowBand := (3*Usrc/σsrc+csrc/(32*σsrc))*((3072*σsrc)/csrc)^2+(3072*σsrc)/csrc
  let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
  have hNumeric := middleOriginal_eventually_general_finite_numerical_consequence
    hσsrc hcsrc hUsrc hκ hCphys.le (zero_le_one.trans hCsrc)
    hCouter hCUP hCLOW hCLARGE hDtype.le hBsOne hCsep hε
  have hLog : ∀ᶠ T : ℝ in Filter.atTop, 1 ≤ Real.log T :=
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop 1)
  refine ⟨Cbudget,η₀,hCbudget,hη₀,hηcap,?_⟩
  filter_upwards [hfinite hθ hθmax hθaction,hNumeric,
    Filter.eventually_ge_atTop (1:ℝ),hLog] with T hfiniteT hNumericT hTone hLogOne
  intro Fsrc Y n N R Jsep η M hNlink hNtwo hR hη hηsmall hJsep hJM
    hy hsepY hreg hjets htests hnegative hmodels hscale
    hSepBudget hRadiusBudget hSquareBudget hNfour hNten A Bint hA hAB hBint
    Yc ErrorTotal Main
  have hT : 0 < T := zero_lt_one.trans_le hTone
  have hNreal : (2:ℝ) ≤ N := by exact_mod_cast hNtwo
  have hNp : (0:ℝ) < N := by linarith only [hNreal]
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hNOne : (1:ℝ) ≤ N := by linarith only [hNreal]
  have hNR : (N:ℝ) ≤ R^2 :=
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hCbudget hNp.le :
      (N:ℝ) ≤ Cbudget*N).trans hRadiusBudget
  have hCsepRoom : Csep*R ≤ N :=
    (mul_le_mul_of_nonneg_right hCsepBudget hRp.le).trans hSepBudget
  obtain ⟨Qbase,kmax,Kmesh,Usel,hBaseLo,hBaseHi,hEndLo,hEndHi,hkmax,hKpos,hvalid,hUmono⟩ :=
    hselect N R hR hNR hCsepRoom
  let Q := fun k : ℕ => Qbase*2^k
  have hUzero : (Usel 0:ℝ) ≤ N := by
    obtain ⟨_,_,_,_,_,_,hUupper,_,_,_,hQstrong,_,_,_⟩ := hvalid 0 (Nat.zero_le _)
    have hQone : (1:ℝ) ≤ Q 0 := by nlinarith only [hQstrong,hR]
    have hQzero : (0:ℝ) < Q 0 := zero_lt_one.trans_le hQone
    calc
      _ ≤ ((N:ℝ)/(Q 0:ℝ))^((2:ℝ)/3)/Bselect := hUupper
      _ ≤ ((N:ℝ)/(Q 0:ℝ))^((2:ℝ)/3) := div_le_self (by positivity) hBsOne
      _ ≤ (N:ℝ)^((2:ℝ)/3) := Real.rpow_le_rpow (by positivity)
        (div_le_self hNp.le hQone) (by norm_num)
      _ ≤ N := Real.rpow_le_self_of_one_le hNOne (by norm_num)
  obtain ⟨hM,hRN,hNR',hNsqM,hNRM,hNcube,hRM,hpad,hquartic,hquadratic,hsmall,hroom,hMTall⟩ :=
    hbudget (N:ℝ) R M (Usel 0:ℝ) hNreal hR hSepBudget hRadiusBudget hSquareBudget hUzero
  have hMT : M ≤ T := hMTall T hT hscale
  have hNM : (N:ℝ) ≤ M :=
    (by nlinarith only [hNreal] : (N:ℝ) ≤ (N:ℝ)^2).trans hNsqM
  have hNT : (N:ℝ) ≤ T := hNM.trans hMT
  have hRegimeLog : (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) :=
    hNfour.trans (le_mul_of_one_le_right (by positivity)
      (Real.one_le_rpow hLogOne (by norm_num)))
  let Vscale := fun k : ℕ => (Usel k:ℝ)^((3:ℝ)/2)
  let lambda := csrc*κ*T/(12*Usrc*M^2)
  let Uband := (3*Usrc/σsrc)*T/(2*M^2)
  obtain ⟨hRatio,hBandScale,_,_⟩ := positive_difference_source_physical_regime_coefficients
    hσsrc hcsrc hUsrc hκ hT hM hNp hRp hscale hNR' hNsqM

  let μ₀ := csrc*T/(12*σsrc*M^3)
  let U₀ := Usrc*T/(2*σsrc*M^3)
  let Error := Yc*(M/(N:ℝ)+1)*
    (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
  let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
  let Δtype := fun k : ℕ =>
    (16*U₀/μ₀)*Real.sqrt (U₀*(Q k:ℝ)^3)*Real.sqrt (Kmesh k)/(6*(Kmesh k:ℝ)^2)
  let Δ := fun k : ℕ => D₀*(Q k:ℝ)/(N:ℝ)
  let D := fun k : ℕ =>
    Δ k+quarticNonlinearResidualConstant σ δ*(2*(Q k:ℝ))/(N:ℝ)
  let Kupper := fun k : ℕ =>
    240*(M^2/((N:ℝ)^4*(Usel k:ℝ)))*
      (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
  let Klower := fun k : ℕ =>
    240*(R^4/((N:ℝ)^2*(Usel k:ℝ)))*
      (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
  let Klarge := fun k : ℕ =>
    2*Bselect*60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain+Ctail)*((Q k:ℝ)/(N:ℝ))^((2:ℝ)/3)
  let Buffer := fun k : ℕ =>
    (56*(Usel k:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
  let Width := fun k : ℕ => (14*σsrc/csrc)*(Usel k:ℝ)*(N:ℝ)
  let FamilyBound := fun (k : ℕ) (P : Finset (ℝ × ℤ)) =>
    (48*σsrc/csrc)^6*(R^2/(Q k:ℝ))^6*
      C*(Kmesh k:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*
        ((Vscale k)*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+(Δtype k)*Jsep)+
          ((P.image Prod.fst).card:ℝ)^2*((Vscale k)*((Kupper k)+(Klower k))+(Klarge k))*T^εloss)
  let Density := fun k => 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
    (2+Real.log (512*σsrc*R^2/(csrc*((Q k:ℝ)/768))+1))
  let Endpoint := Yc*(2*Buffer 0+2*Width 0+6*(N:ℝ)+2*(n:ℝ))
  have hvalidGeneral : ∀ k ≤ kmax,
      12*Usrc ≤ σsrc*(Usel k:ℝ) ∧
      63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      1 ≤ Usel k ∧ Bselect^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
      (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Usel k:ℝ) ∧
      Q k ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
      768*R ≤ (Q k:ℝ) ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
      D k ≤ 1/2 ∧ Δ k < 1/2 := by
    intro k hk
    obtain ⟨hUL,hSource,hMesh,_,hU,hWrap,hUpper,hLower,hQN,hUR,hStrong,hMin,hD,hDelta⟩ :=
      hvalid k hk
    exact ⟨hUL,hSource,hMesh,hU,hWrap,hUpper,hLower,hQN,hUR,hStrong,hMin,hD,hDelta⟩
  have hRoom : 2*(Buffer 0+Width 0)+6*(N:ℝ) ≤ M := by
    convert hroom using 1
    dsimp only [Buffer,Width]
    ring
  obtain ⟨Chunks,band,Dcover,hChunks,hBands,hTerminal,hGrids,hNorm⟩ :=
    hfiniteT Fsrc Y n N Qbase kmax Kmesh Usel R Jsep
      (η:=η) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
      hKpos hNlink hη hηsmall hT hNtwo hR hRM hδzero hδ hJsep hJM
      hy hsepY hreg hjets htests hnegative hmodels hscale hpad hquartic hquadratic
      hRegimeLog hBcut hBsSize hcutMargin hNten hNsqM hNRM
      hsmall hNR' hRN hNcube hsize hBsize hvalidGeneral
      (fun k _ => hUmono k) hRoom A Bint hA hAB hBint
  let Selected := fun k => Chunks.filter (fun p => band p=some k)
  let Grid := fun (k : ℕ) (r : ℤ) =>
    ((Dcover k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
  let NumericFamily := fun (k : ℕ) (P : Finset (ℝ × ℤ)) =>
    Couter*(R^2/(Q k:ℝ))^6*(Kmesh k:ℝ)^((12:ℝ)+εloss)*(2*(P.card:ℝ))^10*
      ((Vscale k)*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+(Δtype k)*Jsep)+
        ((P.image Prod.fst).card:ℝ)^2*
          ((Vscale k)*(CUP*M^2/((N:ℝ)^4*(Usel k:ℝ))+
            CLOW*R^4/((N:ℝ)^2*(Usel k:ℝ)))+
            CLARGE*M^2*R^4/(N:ℝ)^6*((Q k:ℝ)/(N:ℝ))^((2:ℝ)/3))*T^εloss)
  have hQbaseReal : (0:ℝ) < Qbase := by nlinarith only [hBaseLo,hRp]
  have hQbase : 0 < Qbase := by exact_mod_cast hQbaseReal
  have hvalidNumeric : ∀ k ≤ kmax,
      R ≤ (Q k:ℝ) ∧ Q k ≤ N ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      (Kmesh k:ℝ) ≤ (2*max 1 (63*Usrc/(2*σsrc)))*(Q k:ℝ)*(N:ℝ)/R^2 ∧
      (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Usel k:ℝ) := by
    intro k hk
    obtain ⟨_,_,hMesh,hKU,_,_,hUpper,hLower,hQN,_,hStrong,_,_,_⟩ := hvalid k hk
    exact ⟨by nlinarith only [hStrong,hRp],hQN,hMesh,hKU,hUpper,hLower⟩
  have hKupper (k : ℕ) : Kupper k=CUP*M^2/((N:ℝ)^4*(Usel k:ℝ)) := by
    dsimp only [Kupper,CUP]
    simp only [div_eq_mul_inv]
    ac_rfl
  have hKlower (k : ℕ) : Klower k=CLOW*R^4/((N:ℝ)^2*(Usel k:ℝ)) := by
    dsimp only [Klower,CLOW]
    simp only [div_eq_mul_inv]
    ac_rfl
  have hKlarge (k : ℕ) :
      Klarge k=CLARGE*M^2*R^4/(N:ℝ)^6*((Q k:ℝ)/(N:ℝ))^((2:ℝ)/3) := by
    dsimp only [Klarge]
    rw [hRatio]
    calc
      _ = (2*Bselect*60*588*Ratio^2*(Cmain+Ctail))*
          (Uband^2*(R^8/(N:ℝ)^4))*((Q k:ℝ)/(N:ℝ))^((2:ℝ)/3) := by ring
      _ = _ := by rw [hBandScale]; dsimp only [CLARGE]; ring
  have hFamilyEq (k : ℕ) (P : Finset (ℝ × ℤ)) :
      FamilyBound k P=NumericFamily k P := by
    dsimp only [FamilyBound,NumericFamily]
    rw [hKupper,hKlower,hKlarge]
    dsimp only [Couter]
    ac_rfl
  let S := (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y), (𝐞 (f y j):ℂ)‖)^12
  change S ≤ 2^11*(((kmax:ℝ)+2)^11*
    (((n:ℝ)*Yc*Density kmax)^12+
      (4:ℝ)^12*(8:ℝ)^11*∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,
        (2^11*((Csrc*Error)^12+
          (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (Grid k r))))+Endpoint^12) at hNorm
  simp only [hFamilyEq] at hNorm
  exact hNumericT Y n N Qbase kmax Kmesh Usel R M Jsep Chunks band Dcover
    hNlink hNtwo hR hNR' hNsqM hMT hJsep.le hscale hQbase hBaseHi hEndLo hkmax hKpos
    hvalidNumeric hChunks hBands
    (fun k hk r => (hGrids k hk).2.2.1 r)
    (fun k hk r => (hGrids k hk).2.2.2 r) hNorm

public  theorem middleOriginal_general_expressions_nonnegative
    {Y M N R J : ℝ} (hY : 0 ≤ Y) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hR : 0 < R) (hJ : 0 ≤ J) :
    0 ≤ Y*M/Real.sqrt N+Y*M*R^2/N^2+Y*N*(N/R)^((2:ℝ)/3) ∧
    0 ≤ Y^11*M^11*N^2/R^7+Y^11*J*M^11/R^5+
      Y^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3)+
      Y^12*M^10*N/R^3*(R/N)^((2:ℝ)/3)+
      Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3) := by
  refine ⟨?_, middleOriginal_general_expression_nonnegative hY hM hN hR hJ⟩
  positivity

private theorem middleOriginal_approximateModelPhase_enlarged_quantitative_general
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ η₀ B C : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 1 ≤ B ∧ 1 ≤ C ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1 ≤ M →
        Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
        ∃ Fext : ℝ → ℝ,
          (∀ (X : ℝ) (a b : ℕ), M ≤ (a:ℝ) → (b:ℝ) ≤ 2*M →
            ‖Expdb.exponentialSumAt F X M a b-
              Expdb.exponentialSumAt Fext X M a b‖ ≤ 6) ∧
          ∀ (T : ℝ) (Y : Finset ℝ) (n N : ℕ) (R Jsep η : ℝ),
            C ≤ T → N=8*n → 2 ≤ N → B ≤ R →
            0 < η → η ≤ η₀ → 0 < Jsep → Jsep ≤ M →
            (∀ y∈Y, y∈Icc (1:ℝ) 2) →
            (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
            T*(N:ℝ)*R^2=M^3 →
            B*R ≤ N → B*(N:ℝ) ≤ R^2 → B*(N:ℝ)^2 ≤ M →
            B*(N:ℝ)^4 ≤ M*R^3 → B*(N:ℝ)^10 ≤ M^3*R^7 →
            ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
              (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
              let Yc := (Y.card:ℝ)
              let ErrorTotal := Yc*M/Real.sqrt (N:ℝ)+Yc*M*R^2/(N:ℝ)^2+
                Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
              let Main := Yc^11*M^11*(N:ℝ)^2/R^7+Yc^11*Jsep*M^11/R^5+
                Yc^12*M^12/((N:ℝ)*R^7)*(R/(N:ℝ))^((2:ℝ)/3)+
                Yc^12*M^10*(N:ℝ)/R^3*(R/(N:ℝ))^((2:ℝ)/3)+
                Yc^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
              (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),
                (𝐞 (T*(Fext ((j:ℝ)/M)-Fext ((j:ℝ)/M+η*y))/η):ℂ)‖)^12 ≤
                  C*T^ε*(ErrorTotal^12+Main) := by
  classical
  have hσone : 0<σ+1 := by linarith only [hσ]
  let δmodel := min (modelPhaseThirdLower (σ+1)) 1/2
  have hmin : 0 < min (modelPhaseThirdLower (σ+1)) 1 :=
    lt_min (modelPhaseThirdLower_pos hσone) zero_lt_one
  have hδmodel : 0<δmodel := half_pos hmin
  have hδmodelCap : δmodel ≤ min (modelPhaseThirdLower (σ+1)) 1 := by
    dsimp only [δmodel]
    linarith only [hmin]
  obtain ⟨δ,ηsrc,a,c,J,hδ,hηsrc,hηsrcCap,ha,hc,hJ,hanchor,hsource⟩ :=
    HuxleyRationalPhase.approximateModelPhase_enlarged_colored_common_scale_source
      hσ hδmodel (by norm_num : (0:ℝ)<1) 5 le_rfl
  have hanchor' : c≤4*modelPhaseThirdLower (σ+1)*1/((σ+1)*((σ+1)+1)+3) := by
    simpa only [add_assoc,show (1:ℝ)+1=2 by norm_num] using hanchor
  obtain ⟨Cbudget,ηquant,hCbudget,hηquant,_,hquant⟩ :=
    middleOriginal_eventually_general_quantitative_phase_subinterval_bound
      (by norm_num : (0:ℝ)<1) hc hJ hσone hδmodel.le hδmodelCap hε hanchor'
  obtain ⟨Tcut,hTcut⟩ := Filter.eventually_atTop.mp hquant
  let D := 2+2*σ+1/σ
  have hD : 1≤D := by
    dsimp only [D]
    have hi : 0<1/σ := div_pos zero_lt_one hσ
    linarith only [hσ,hi]
  have hDpos := zero_lt_one.trans_le hD
  have hDσ : 1≤D*σ := by
    have hi : (1/σ)*σ=1 := div_mul_cancel₀ 1 hσ.ne'
    dsimp only [D]
    nlinarith only [hi,hσ,sq_nonneg σ]
  have hσD : 2*σ≤D := by
    dsimp only [D]
    have hi : 0<1/σ := by positivity
    linarith only [hi]
  let B := Cbudget*D^7
  have hB : 1≤B := by
    calc
      _ = (1:ℝ)*1 := by norm_num
      _ ≤ Cbudget*D^7 := mul_le_mul hCbudget (one_le_pow₀ hD)
        zero_le_one (zero_le_one.trans hCbudget)
  let Cap := 4/a+3
  have hCap : 1≤Cap := by
    dsimp only [Cap]
    have hh : 0<4/a := by positivity
    linarith only [hh]
  let K := (2*σ)^ε*D^24
  have hK : 0≤K := mul_nonneg
    (Real.rpow_nonneg (mul_nonneg (by norm_num) hσ.le) ε) (pow_nonneg hDpos.le 24)
  let C := max 1 (max (Tcut/σ) (Cap^12*K))
  have hC : 1≤C := le_max_left _ _
  have hCcut : Tcut/σ≤C := (le_max_left _ _).trans (le_max_right _ _)
  have hCK : Cap^12*K≤C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨δ,min ηsrc ηquant,B,C,hδ,lt_min hηsrc hηquant,
    (min_le_left _ _).trans hηsrcCap,hB,hC,?_⟩
  intro M F hM hF
  obtain ⟨Fext,_,_,hsharp,hcolors⟩ := hsource M F hM hF
  refine ⟨Fext,hsharp,?_⟩
  intro T Y n N R Jsep η hT hN8 hN2 hRlow hη hηcap hJsep hJsepM
    hY hsep hphase hRN hNR hNM hFour hTen A Bint hA hAB hBint Yc ErrorTotal Main
  have hMp : 0<M := zero_lt_one.trans_le hM
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hRp : 0<R := zero_lt_one.trans_le (hB.trans hRlow)
  have hTp : 0<T := zero_lt_one.trans_le (hC.trans hT)
  have hYc : 0≤Yc := Nat.cast_nonneg _
  have hSigns := middleOriginal_general_expressions_nonnegative hYc hMp.le hNp.le hRp hJsep.le
  have hError : 0≤ErrorTotal := hSigns.1
  have hMain : 0≤Main := hSigns.2
  have hMass : 0≤ErrorTotal^12+Main := add_nonneg (pow_nonneg hError 12) hMain
  let color := fun y : ℝ => ⌊y/a⌋
  let z := fun y : ℝ => (‖∑ j∈Finset.Ioc (A y) (Bint y),
    (𝐞 (T*(Fext ((j:ℝ)/M)-Fext ((j:ℝ)/M+η*y))/η):ℂ)‖:ℂ)
  have hzNorm (U : Finset ℝ) :
      ‖∑ y∈U,z y‖ = ∑ y∈U,‖∑ j∈Finset.Ioc (A y) (Bint y),
        (𝐞 (T*(Fext ((j:ℝ)/M)-Fext ((j:ℝ)/M+η*y))/η):ℂ)‖ := by
    dsimp only [z]
    rw [←Complex.ofReal_sum]
    exact Complex.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  obtain ⟨hcard,hmoment,hclasses⟩ :=
    hcolors Y id η hY hη (hηcap.trans (min_le_left _ _))
  have hlocal (j : ℤ) (hj : j∈Y.image color) :
      ‖∑ y∈Y.filter (fun y => color y=j),z y‖^12 ≤
        K*T^ε*(ErrorTotal^12+Main) := by
    obtain ⟨y₀,hy₀,_,hreg,hjets,htests,hnegative,hscaled⟩ := hclasses j hj
    let γ := σ*y₀
    have hy₀range := hY y₀ hy₀
    have hy₀p : 0<y₀ := zero_lt_one.trans_le hy₀range.1
    have hγ : 0<γ := mul_pos hσ hy₀p
    have hγlo : σ≤γ := le_mul_of_one_le_right hσ.le hy₀range.1
    have hγhi : γ≤2*σ := by dsimp only [γ]; nlinarith only [hy₀range.2,hσ]
    have hγD := hγhi.trans hσD
    have hDγ : 1≤D*γ := hDσ.trans (mul_le_mul_of_nonneg_left hγlo hDpos.le)
    let Fsrc := fun w => (1/(σ*y₀))*Fext w
    let Tnew := T*σ*y₀/1
    let Rnew := R*Real.sqrt (1/(σ*y₀))
    obtain ⟨hTnew,hRnew,hRsq,hnewphase,hmodels⟩ :=
      hscaled T (N:ℝ) R hTp hRp hphase
    have hTnewEq : Tnew=T*γ := by dsimp only [Tnew,γ]; rw [div_one,mul_assoc]
    have hRnewSq : Rnew^2=R^2/γ := by
      simpa only [id_eq, mul_one] using hRsq
    have hRg : γ*Rnew^2=R^2 := by rw [hRnewSq]; field_simp
    obtain ⟨hSle,hRle⟩ := upperOriginal_normalized_radius_comparable hRp hRnew hD hγD hDγ hRg
    obtain ⟨hRnew1,hnewRN,hnewNR,hnewNM,hnewFour,hnewTen⟩ :=
      upperOriginal_comparable_radius_source_budgets hMp hNp hRp hD hCbudget hSle hRle
        hRlow hRN hNR hNM hFour hTen
    have hTnewCut : Tcut≤Tnew := by
      rw [hTnewEq]
      exact ((div_le_iff₀ hσ).mp (hCcut.trans hT)).trans
        (mul_le_mul_of_nonneg_left hγlo hTp.le)
    let Yj := Y.filter (fun y => color y=j)
    have hYj (y : ℝ) (hy : y∈Yj) : y∈Y :=
      (Finset.mem_filter.mp hy).1
    have hYjColor (y : ℝ) (hy : y∈Yj) : color y=j :=
      (Finset.mem_filter.mp hy).2
    have hmod (y : ℝ) (hy : y∈Yj) :
        Expdb.IsApproximateModelPhaseFunction
          (fun u => (Fsrc u-Fsrc (u+η*y))/(1*η)) (σ+1) 4 δmodel :=
      approximateModelPhase_mono (hmodels y (hYj y hy) (hYjColor y hy)).1
        (by norm_num) le_rfl
    have hq := hTcut Tnew hTnewCut Fsrc Yj n N Rnew Jsep hN8 hN2 hRnew1
      hη (hηcap.trans (min_le_right _ _)) hJsep hJsepM
      (fun y hy => hY y (hYj y hy))
      (fun y hy v hv hne => hsep y (hYj y hy) v (hYj v hv) hne)
      hreg hjets htests hnegative hmod hnewphase hnewRN hnewNR hnewNM
      hnewFour hnewTen A Bint (fun y hy => hA y (hYj y hy))
      (fun y hy => hAB y (hYj y hy)) (fun y hy => hBint y (hYj y hy))
    have hYj0 : (0:ℝ)≤Yj.card := Nat.cast_nonneg _
    have hYjCard : (Yj.card:ℝ)≤Yc := by
      change ((Y.filter (fun y => color y=j)).card:ℝ)≤(Y.card:ℝ)
      exact_mod_cast (Finset.card_filter_le Y (fun y => color y=j))
    let Enew := (Yj.card:ℝ)*M/Real.sqrt (N:ℝ)+
      (Yj.card:ℝ)*M*Rnew^2/(N:ℝ)^2+
      (Yj.card:ℝ)*(N:ℝ)*((N:ℝ)/Rnew)^((2:ℝ)/3)
    let MainNew := (Yj.card:ℝ)^11*M^11*(N:ℝ)^2/Rnew^7+
      (Yj.card:ℝ)^11*Jsep*M^11/Rnew^5+
      (Yj.card:ℝ)^12*M^12/((N:ℝ)*Rnew^7)*(Rnew/(N:ℝ))^((2:ℝ)/3)+
      (Yj.card:ℝ)^12*M^10*(N:ℝ)/Rnew^3*(Rnew/(N:ℝ))^((2:ℝ)/3)+
      (Yj.card:ℝ)^12*M^12/((N:ℝ)^4*Rnew^2)*(Rnew/(N:ℝ))^((2:ℝ)/3)
    have hEnew : Enew≤D^2*ErrorTotal :=
      upperOriginal_upper_radius_error_bound hYj0 hYjCard hMp hNp hRp hRnew hD hSle hRle
    have hMainNew : MainNew≤D^8*Main :=
      middleOriginal_general_radius_main_bound hYj0 hYjCard hMp hNp hRp hRnew hD hJsep.le hSle hRle
    have hNewSigns := middleOriginal_general_expressions_nonnegative hYj0 hMp.le hNp.le hRnew hJsep.le
    have hEnew0 : 0≤Enew := hNewSigns.1
    have hMainNew0 : 0≤MainNew := hNewSigns.2
    have hEpow : Enew^12≤D^24*ErrorTotal^12 := by
      calc
        _ ≤ (D^2*ErrorTotal)^12 := pow_le_pow_left₀ hEnew0 hEnew 12
        _ = _ := by rw [mul_pow,←pow_mul]
    have hMainPow : MainNew≤D^24*Main :=
      hMainNew.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hD (by norm_num : 8≤24)) hMain)
    have hTotal : Enew^12+MainNew≤D^24*(ErrorTotal^12+Main) := by
      calc
        _ ≤ D^24*ErrorTotal^12+D^24*Main := add_le_add hEpow hMainPow
        _ = _ := (mul_add _ _ _).symm
    have hTpow : Tnew^ε≤(2*σ)^ε*T^ε := by
      rw [hTnewEq,Real.mul_rpow hTp.le hγ.le]
      calc
        _ ≤ T^ε*(2*σ)^ε :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hγ.le hγhi hε.le)
            (Real.rpow_nonneg hTp.le _)
        _ = _ := mul_comm _ _
    rw [hzNorm]
    calc
      _ = (∑ y∈Yj,‖∑ l∈Finset.Ioc (A y) (Bint y),
          (𝐞 (Tnew*(Fsrc ((l:ℝ)/M)-Fsrc ((l:ℝ)/M+η*y))/(1*η)):ℂ)‖)^12 := by
        congr 1
        apply Finset.sum_congr rfl
        intro y hy
        congr 1
        apply Finset.sum_congr rfl
        intro l _
        apply congrArg (fun x : ℝ => (𝐞 x:ℂ))
        simpa only [id_eq, one_mul] using ((hmodels y (hYj y hy) (hYjColor y hy)).2.1 (l:ℝ)).symm
      _ ≤ Tnew^ε*(Enew^12+MainNew) := hq
      _ ≤ ((2*σ)^ε*T^ε)*(D^24*(ErrorTotal^12+Main)) :=
        mul_le_mul hTpow hTotal (add_nonneg (pow_nonneg hEnew0 12) hMainNew0)
          (mul_nonneg (Real.rpow_nonneg (mul_nonneg (by norm_num) hσ.le) ε)
            (Real.rpow_nonneg hTp.le ε))
      _ = _ := by dsimp only [K]; ac_rfl
  have hKmass : 0≤K*T^ε*(ErrorTotal^12+Main) :=
    mul_nonneg (mul_nonneg hK (Real.rpow_nonneg hTp.le ε)) hMass
  have hcolorSum :
      (∑ j∈Y.image color,‖∑ y∈Y.filter (fun y => color y=j),z y‖^12) ≤
        Cap*(K*T^ε*(ErrorTotal^12+Main)) := by
    calc
      _ ≤ ∑ _j∈Y.image color,K*T^ε*(ErrorTotal^12+Main) :=
        Finset.sum_le_sum hlocal
      _ = ((Y.image color).card:ℝ)*(K*T^ε*(ErrorTotal^12+Main)) := by
        rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard hKmass
  calc
    _ = ‖∑ y∈Y,z y‖^12 := congrArg (fun x : ℝ => x^12) (hzNorm Y).symm
    _ ≤ Cap^11*∑ j∈Y.image color,‖∑ y∈Y.filter (fun y => color y=j),z y‖^12 :=
      hmoment z
    _ ≤ Cap^11*(Cap*(K*T^ε*(ErrorTotal^12+Main))) :=
      mul_le_mul_of_nonneg_left hcolorSum (pow_nonneg (zero_le_one.trans hCap) 11)
    _ = (Cap^12*K)*(T^ε*(ErrorTotal^12+Main)) := by
      rw [show Cap^12=Cap^11*Cap from pow_succ Cap 11]
      ac_rfl
    _ ≤ C*(T^ε*(ErrorTotal^12+Main)) :=
      mul_le_mul_of_nonneg_right hCK (mul_nonneg (Real.rpow_nonneg hTp.le ε) hMass)
    _ = _ := (mul_assoc _ _ _).symm

public  theorem middleOriginal_approximateModelPhase_enlarged_general_correlation_moment
    {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∃ δ η₀ B C : ℝ, 0<δ ∧ 0<η₀ ∧ η₀≤1/8 ∧ 1≤B ∧ 1≤C ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1≤M →
        Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
        ∃ Fext : ℝ → ℝ,
          (∀ (X : ℝ) (a b : ℕ), M≤(a:ℝ) → (b:ℝ)≤2*M →
            ‖Expdb.exponentialSumAt F X M a b-
              Expdb.exponentialSumAt Fext X M a b‖≤6) ∧
          ∀ (X : ℝ) (n N a L k : ℕ) (R : ℝ),
            C≤X*k/M → N=8*n → 2≤N → B≤R →
            0<k → (k:ℝ)/M≤η₀ → (k:ℝ)≤M →
            M≤(a:ℝ) → ((a+L:ℕ):ℝ)≤2*M →
            (X*k/M)*(N:ℝ)*R^2=M^3 →
            B*R≤N → B*(N:ℝ)≤R^2 → B*(N:ℝ)^2≤M →
            B*(N:ℝ)^4≤M*R^3 → B*(N:ℝ)^10≤M^3*R^7 →
            let K := (k:ℝ)
            let E := K*M/Real.sqrt (N:ℝ)+K*M*R^2/(N:ℝ)^2+
              K*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
            let Main := K^11*M^11*(N:ℝ)^2/R^7+K^11*K*M^11/R^5+
              K^12*M^12/((N:ℝ)*R^7)*(R/(N:ℝ))^((2:ℝ)/3)+
              K^12*M^10*(N:ℝ)/R^3*(R/(N:ℝ))^((2:ℝ)/3)+
              K^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
            (∑ j∈Finset.range k,‖sourceShiftCorrelation Fext X M a L (k+j)‖)^12 ≤
              C*(X*k/M)^ε*(E^12+Main) := by
  classical
  obtain ⟨δ,η₀,B,C₀,hδ,hη₀,hηcap,hB,hC₀,hsource⟩ :=
    middleOriginal_approximateModelPhase_enlarged_quantitative_general hσ hε
  let C := (2:ℝ)^12*C₀
  have hCC₀ : C₀≤C := le_mul_of_one_le_left (zero_le_one.trans hC₀) (by norm_num)
  have hC : 1≤C := hC₀.trans hCC₀
  refine ⟨δ,η₀,B,C,hδ,hη₀,hηcap,hB,hC,?_⟩
  intro M F hM hF
  obtain ⟨Fext,hsharp,hupper⟩ := hsource M F hM hF
  refine ⟨Fext,hsharp,?_⟩
  intro X n N a L k R hT hN8 hN2 hR hk hη hKM ha hb hphase hRN hNR hNM
    hFour hTen K E Main
  have hMp := zero_lt_one.trans_le hM
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hN1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hRp := zero_lt_one.trans_le (hB.trans hR)
  have hKp : 0<K := by
    change (0:ℝ)<k
    exact_mod_cast hk
  have hT1 : 1≤X*k/M := hC.trans hT
  have hTp := zero_lt_one.trans_le hT1
  let S := (Finset.Ico k (2*k)).filter (fun r => r≤L)
  let Y := S.image (fun (r:ℕ) => (r:ℝ)/(k:ℝ))
  let Bint := fun y : ℝ => ((a+(L-⌊(k:ℝ)*y⌋₊):ℕ):ℤ)
  obtain ⟨hcard,hY,hsep,hA,hAB,hBint,hcorr⟩ :=
    upperOriginal_dyadic_shift_actual_family Fext X hMp a L k hk ha hb
  have hY0 : (0:ℝ)≤Y.card := Nat.cast_nonneg _
  have hYK : (Y.card:ℝ)≤K := by
    change (Y.card:ℝ)≤(k:ℝ)
    exact_mod_cast hcard
  let EY := (Y.card:ℝ)*M/Real.sqrt (N:ℝ)+(Y.card:ℝ)*M*R^2/(N:ℝ)^2+
    (Y.card:ℝ)*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
  let MainY := (Y.card:ℝ)^11*M^11*(N:ℝ)^2/R^7+
    (Y.card:ℝ)^11*(k:ℝ)*M^11/R^5+
    (Y.card:ℝ)^12*M^12/((N:ℝ)*R^7)*(R/(N:ℝ))^((2:ℝ)/3)+
    (Y.card:ℝ)^12*M^10*(N:ℝ)/R^3*(R/(N:ℝ))^((2:ℝ)/3)+
    (Y.card:ℝ)^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
  have hEY : EY≤E := by
    have hh := upperOriginal_upper_radius_error_bound hY0 hYK hMp hNp hRp hRp
      (show (1:ℝ)≤1 from le_rfl) (by rw [one_mul]) (by rw [one_mul])
    simpa only [one_pow,one_mul] using hh
  have hMY : MainY≤Main := by
    have hh := middleOriginal_general_radius_main_bound hY0 hYK hMp hNp hRp hRp
      (show (1:ℝ)≤1 from le_rfl) hKp.le (by rw [one_mul]) (by rw [one_mul])
    simpa only [one_pow,one_mul] using hh
  have hYSigns := middleOriginal_general_expressions_nonnegative hY0 hMp.le hNp.le hRp hKp.le
  have hSigns := middleOriginal_general_expressions_nonnegative hKp.le hMp.le hNp.le hRp hKp.le
  have hEY0 : 0≤EY := hYSigns.1
  have hE0 : 0≤E := hSigns.1
  have hMain0 : 0≤Main := hSigns.2
  have hMass0 : 0≤E^12+Main := add_nonneg (pow_nonneg hE0 12) hMain0
  have hMass : EY^12+MainY≤E^12+Main :=
    add_le_add (pow_le_pow_left₀ hEY0 hEY 12) hMY
  let Z := ∑ y∈Y,‖∑ l∈Finset.Ioc (a:ℤ) (Bint y),
    (𝐞 ((X*k/M)*(Fext ((l:ℝ)/M)-Fext ((l:ℝ)/M+((k:ℝ)/M)*y))/
      ((k:ℝ)/M)):ℂ)‖
  have hZ0 : 0≤Z := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hZ : Z^12≤C₀*(X*k/M)^ε*(E^12+Main) := by
    have hu := hupper (X*k/M) Y n N R k ((k:ℝ)/M)
      (hCC₀.trans hT) hN8 hN2 hR (div_pos hKp hMp) hη hKp hKM hY hsep hphase
      hRN hNR hNM hFour hTen (fun _ => (a:ℤ)) Bint (fun _ _ => hA) hAB hBint
    exact hu.trans (mul_le_mul_of_nonneg_left hMass
      (mul_nonneg (zero_le_one.trans hC₀) (Real.rpow_nonneg hTp.le ε)))
  have hQ : 1≤C₀*(X*k/M)^ε := by
    calc
      _ = (1:ℝ)*1 := by norm_num
      _ ≤ _ := mul_le_mul hC₀ (Real.one_le_rpow hT1 hε.le)
        zero_le_one (zero_le_one.trans hC₀)
  have hRleN : R≤(N:ℝ) :=
    (le_mul_of_one_le_left hRp.le hB).trans hRN
  have hKE : K≤E := upperOriginal_upper_endpoint_error_absorption hKp.le hMp.le hN1 hRp hRleN
  have hKpow : K^12≤C₀*(X*k/M)^ε*(E^12+Main) :=
    ((pow_le_pow_left₀ hKp.le hKE 12).trans (le_add_of_nonneg_right hMain0)).trans
      (le_mul_of_one_le_left hMass0 hQ)
  have hCorr : (∑ j∈Finset.range k,‖sourceShiftCorrelation Fext X M a L (k+j)‖)≤K+Z :=
    hcorr.trans (add_le_add hYK le_rfl)
  calc
    _ ≤ (K+Z)^12 :=
      pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hCorr 12
    _ ≤ (2:ℝ)^11*(K^12+Z^12) := add_pow_le hKp.le hZ0 12
    _ ≤ (2:ℝ)^11*(C₀*(X*k/M)^ε*(E^12+Main)+C₀*(X*k/M)^ε*(E^12+Main)) :=
      mul_le_mul_of_nonneg_left (add_le_add hKpow hZ) (by norm_num)
    _ = _ := by
      rw [←two_mul]
      dsimp only [C]
      rw [show (2:ℝ)^12=2^11*2 from pow_succ 2 11]
      ac_rfl

private theorem middleOriginal_general_correlation_integer_moments
    {X M N K R : ℝ} (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hR : 0<R)
    (hscale : (X*K/M)*N*R^2=M^3) :
    (K^11*M^11*N^2/R^7)^6=X^21*K^87*N^33/M^18 ∧
    (K^11*K*M^11/R^5)^6=X^15*K^87*M^6*N^15 ∧
    (K^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3))^6=X^19*K^91*N^9/M^4 ∧
    (K^12*M^10*N/R^3*(R/N)^((2:ℝ)/3))^6=X^7*K^79*M^32*N^9 ∧
    (K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))^6=X^4*K^76*M^56/N^24 := by
  have hR2 : R^2=M^4/(X*K*N) := by
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero hX.ne' hK.ne') hN.ne')).mpr
    have hs := hscale
    field_simp at hs
    nlinarith only [hs]
  have hR42 : R^42=(R^2)^21 := by rw [←pow_mul]
  have hR30 : R^30=(R^2)^15 := by rw [←pow_mul]
  have hR18 : R^18=(R^2)^9 := by rw [←pow_mul]
  have hR12 : R^12=(R^2)^6 := by rw [←pow_mul]
  have hR4 : R^4=(R^2)^2 := by rw [←pow_mul]
  have hFrac : ((R/N)^((2:ℝ)/3))^6=(R/N)^4 := by
    rw [←Real.rpow_mul_natCast (div_nonneg hR.le hN.le)]
    norm_num
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp only [mul_pow,div_pow,←pow_mul]
    rw [hR42,hR2]
    field_simp
    ac_rfl
  · simp only [mul_pow,div_pow,←pow_mul]
    rw [hR30,hR2]
    field_simp
  · rw [mul_pow,hFrac]
    simp only [mul_pow,div_pow,←pow_mul]
    rw [hR42,hR4,hR2]
    field_simp
    ac_rfl
  · rw [mul_pow,hFrac]
    simp only [mul_pow,div_pow,←pow_mul]
    rw [hR18,hR4,hR2]
    field_simp
    ac_rfl
  · rw [mul_pow,hFrac]
    simp only [mul_pow,div_pow,←pow_mul]
    rw [hR12,hR4,hR2]
    field_simp
    ring

private theorem middleOriginal_general_integer_moments_all_shifts
    {X M N K H R : ℝ}
    (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hH : 0<H) (hR : 0<R)
    (hKH : K≤H) (hscale : (X*K/M)*N*R^2=M^3) :
    (M/H)^72*(K*M/Real.sqrt N)^72≤M^144/N^36 ∧
    (M/H)^72*(K*M*R^2/N^2)^72≤M^432/(H^72*X^72*N^216) ∧
    (M/H)^72*(K*N*(N/R)^((2:ℝ)/3))^72≤X^24*H^24*N^144/M^24 ∧
    (M/H)^72*(K^11*M^11*N^2/R^7)^6≤X^21*H^15*M^54*N^33 ∧
    (M/H)^72*(K^11*K*M^11/R^5)^6≤X^15*H^15*M^78*N^15 ∧
    (M/H)^72*(K^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3))^6≤X^19*H^19*M^68*N^9 ∧
    (M/H)^72*(K^12*M^10*N/R^3*(R/N)^((2:ℝ)/3))^6≤X^7*H^7*M^104*N^9 ∧
    (M/H)^72*(K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))^6≤X^4*H^4*M^128/N^24 := by
  obtain ⟨he₁,he₂,he₃,_,_,_⟩ :=
    upperOriginal_upper_integer_moments_all_shifts hX hM hN hK hH hR hKH hscale
  obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := middleOriginal_general_correlation_integer_moments hX hM hN hK hR hscale
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [mul_pow,div_pow,←pow_mul] using
      pow_le_pow_left₀ (by positivity) he₁ 2
  · simpa only [mul_pow,div_pow,←pow_mul] using
      pow_le_pow_left₀ (by positivity) he₂ 2
  · simpa only [mul_pow,div_pow,←pow_mul] using
      pow_le_pow_left₀ (by positivity) he₃ 2
  · rw [h₁]
    calc
      _ ≤ (M/H)^72*(X^21*H^87*N^33/M^18) := by gcongr
      _ = _ := by field_simp
  · rw [h₂]
    calc
      _ ≤ (M/H)^72*(X^15*H^87*M^6*N^15) := by gcongr
      _ = _ := by field_simp
  · rw [h₃]
    calc
      _ ≤ (M/H)^72*(X^19*H^91*N^9/M^4) := by gcongr
      _ = _ := by field_simp
  · rw [h₄]
    calc
      _ ≤ (M/H)^72*(X^7*H^79*M^32*N^9) := by gcongr
      _ = _ := by field_simp
  · rw [h₅]
    calc
      _ ≤ (M/H)^72*(X^4*H^76*M^56/N^24) := by gcongr
      _ = _ := by field_simp

public  theorem middleOriginal_five_term_power_bound
    {a b c d e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (n : ℕ) :
    (a+b+c+d+e)^n ≤ (2:ℝ)^(4*n)*(a^n+b^n+c^n+d^n+e^n) := by
  let D := (2:ℝ)^(2*n)
  have hD : 1 ≤ D := one_le_pow₀ (by norm_num)
  have hD0 := zero_le_one.trans hD
  have habc := upperOriginal_three_term_power_bound ha hb hc n
  have habc0 : 0 ≤ a+b+c := add_nonneg (add_nonneg ha hb) hc
  calc
    _ ≤ D*((a+b+c)^n+d^n+e^n) := upperOriginal_three_term_power_bound habc0 hd he n
    _ ≤ D*(D*(a^n+b^n+c^n)+D*d^n+D*e^n) :=
      mul_le_mul_of_nonneg_left
        (add_le_add
          (add_le_add habc (le_mul_of_one_le_left (pow_nonneg hd n) hD))
          (le_mul_of_one_le_left (pow_nonneg he n) hD)) hD0
    _ = (D*D)*(a^n+b^n+c^n+d^n+e^n) := by ring
    _ = _ := by
      dsimp only [D]
      rw [←pow_add]
      congr 2
      omega

private theorem middleOriginal_weighted_general_integer_moment_bound
    {X M N K H R : ℝ}
    (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hH : 0<H) (hR : 0<R)
    (hKH : K≤H) (hscale : (X*K/M)*N*R^2=M^3) :
    let E := K*M/Real.sqrt N+K*M*R^2/N^2+K*N*(N/R)^((2:ℝ)/3)
    let Main := K^11*M^11*N^2/R^7+K^11*K*M^11/R^5+
      K^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3)+
      K^12*M^10*N/R^3*(R/N)^((2:ℝ)/3)+
      K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)
    (M/H)^72*(E^72+Main^6)≤(2:ℝ)^144*
      ((M^144/N^36+M^432/(H^72*X^72*N^216)+X^24*H^24*N^144/M^24)+
        (X^21*H^15*M^54*N^33+X^15*H^15*M^78*N^15+
          X^19*H^19*M^68*N^9+X^7*H^7*M^104*N^9+X^4*H^4*M^128/N^24)) := by
  intro E Main
  let e₁ := K*M/Real.sqrt N
  let e₂ := K*M*R^2/N^2
  let e₃ := K*N*(N/R)^((2:ℝ)/3)
  let a₁ := K^11*M^11*N^2/R^7
  let a₂ := K^11*K*M^11/R^5
  let a₃ := K^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3)
  let a₄ := K^12*M^10*N/R^3*(R/N)^((2:ℝ)/3)
  let a₅ := K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)
  have he₁ : 0 ≤ e₁ := by dsimp only [e₁]; positivity
  have he₂ : 0 ≤ e₂ := by dsimp only [e₂]; positivity
  have he₃ : 0 ≤ e₃ := by dsimp only [e₃]; positivity
  have ha₁ : 0 ≤ a₁ := by dsimp only [a₁]; positivity
  have ha₂ : 0 ≤ a₂ := by dsimp only [a₂]; positivity
  have ha₃ : 0 ≤ a₃ := by dsimp only [a₃]; positivity
  have ha₄ : 0 ≤ a₄ := by dsimp only [a₄]; positivity
  have ha₅ : 0 ≤ a₅ := by dsimp only [a₅]; positivity
  have hE : E^72≤(2:ℝ)^144*(e₁^72+e₂^72+e₃^72) :=
    upperOriginal_three_term_power_bound he₁ he₂ he₃ 72
  have hMain : Main^6≤(2:ℝ)^144*(a₁^6+a₂^6+a₃^6+a₄^6+a₅^6) :=
    (middleOriginal_five_term_power_bound ha₁ ha₂ ha₃ ha₄ ha₅ 6).trans
      (mul_le_mul_of_nonneg_right (by norm_num)
        (add_nonneg (add_nonneg (add_nonneg (add_nonneg
          (pow_nonneg ha₁ 6) (pow_nonneg ha₂ 6)) (pow_nonneg ha₃ 6))
          (pow_nonneg ha₄ 6)) (pow_nonneg ha₅ 6)))
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈⟩ :=
    middleOriginal_general_integer_moments_all_shifts hX hM hN hK hH hR hKH hscale
  have hW : 0≤(M/H)^72 := pow_nonneg (div_nonneg hM.le hH.le) 72
  calc
    _ ≤ (M/H)^72*((2:ℝ)^144*(e₁^72+e₂^72+e₃^72)+
        (2:ℝ)^144*(a₁^6+a₂^6+a₃^6+a₄^6+a₅^6)) :=
      mul_le_mul_of_nonneg_left (add_le_add hE hMain) hW
    _ = (2:ℝ)^144*(((M/H)^72*e₁^72+(M/H)^72*e₂^72+(M/H)^72*e₃^72)+
        ((M/H)^72*a₁^6+(M/H)^72*a₂^6+(M/H)^72*a₃^6+(M/H)^72*a₄^6+
          (M/H)^72*a₅^6)) := by
      simp only [mul_add]
      ac_rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (add_le_add h₁ h₂) h₃)
        (add_le_add (add_le_add (add_le_add (add_le_add h₄ h₅) h₆) h₇) h₈))
      (by norm_num)

public  theorem middleOriginal_general_weyl_one_hundred_forty_fourth_bound
    {S Z A C L X M N K H R ε : ℝ}
    (hS : 0≤S) (hZ : 0≤Z) (hA : 0≤A) (hC : 1≤C) (hL : 0≤L)
    (hX : 1≤X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hH : 0<H) (hR : 0<R)
    (hε : 0≤ε) (hKH : K≤H) (hscale : (X*K/M)*N*R^2=M^3) :
    let E := K*M/Real.sqrt N+K*M*R^2/N^2+K*N*(N/R)^((2:ℝ)/3)
    let Main := K^11*M^11*N^2/R^7+K^11*K*M^11/R^5+
      K^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3)+
      K^12*M^10*N/R^3*(R/N)^((2:ℝ)/3)+
      K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)
    Z^12≤C*X^ε*(E^12+Main) →
    S^24≤A*L^12*((M^2/H)^12+(M/H)^12*Z^12) →
    S^144≤(2:ℝ)^154*A^6*C^6*L^72*X^(6*ε)*
      (M^144/H^72+
        ((M^144/N^36+M^432/(H^72*X^72*N^216)+X^24*H^24*N^144/M^24)+
          (X^21*H^15*M^54*N^33+X^15*H^15*M^78*N^15+
            X^19*H^19*M^68*N^9+X^7*H^7*M^104*N^9+X^4*H^4*M^128/N^24))) := by
  intro E Main hCorr hWeyl
  have hXp := zero_lt_one.trans_le hX
  have hC0 := zero_le_one.trans hC
  have hSigns := middleOriginal_general_expressions_nonnegative hK.le hM.le hN.le hR hK.le
  have hE0 : 0≤E := hSigns.1
  have hMain0 : 0≤Main := hSigns.2
  let V := (M^144/N^36+M^432/(H^72*X^72*N^216)+X^24*H^24*N^144/M^24)+
    (X^21*H^15*M^54*N^33+X^15*H^15*M^78*N^15+
      X^19*H^19*M^68*N^9+X^7*H^7*M^104*N^9+X^4*H^4*M^128/N^24)
  have hV0 : 0≤V := by dsimp only [V]; positivity
  have hW0 : 0≤(M/H)^72 := pow_nonneg (div_nonneg hM.le hH.le) 72
  have hTpow : 0≤X^(6*ε) := Real.rpow_nonneg hXp.le _
  have hTpowOne : 1≤X^(6*ε) := Real.one_le_rpow hX (mul_nonneg (by norm_num) hε)
  have hXpSix : (X^ε)^6=X^(6*ε) := by
    rw [←Real.rpow_mul_natCast hXp.le]
    congr 1
    norm_num [mul_comm]
  have hSix : S^144≤A^6*L^72*((M^2/H)^12+(M/H)^12*Z^12)^6 := by
    simpa only [mul_pow,←pow_mul] using
      pow_le_pow_left₀ (pow_nonneg hS 24) hWeyl 6
  have hAdd : ((M^2/H)^12+(M/H)^12*Z^12)^6≤
      32*(M^144/H^72+(M/H)^72*Z^72) := by
    simpa only [div_pow,mul_pow,←pow_mul,show (2:ℝ)^(6-1)=32 by norm_num] using
      add_pow_le (by positivity : 0≤(M^2/H)^12)
        (by positivity : 0≤(M/H)^12*Z^12) 6
  have hSmain : S^144≤32*A^6*L^72*(M^144/H^72+(M/H)^72*Z^72) := by
    calc
      _ ≤ A^6*L^72*((M^2/H)^12+(M/H)^12*Z^12)^6 := hSix
      _ ≤ A^6*L^72*(32*(M^144/H^72+(M/H)^72*Z^72)) :=
        mul_le_mul_of_nonneg_left hAdd (mul_nonneg (pow_nonneg hA 6) (pow_nonneg hL 72))
      _ = _ := by ac_rfl
  have hZSix : Z^72≤C^6*X^(6*ε)*(E^12+Main)^6 := by
    have hh := pow_le_pow_left₀ (pow_nonneg hZ 12) hCorr 6
    simpa only [mul_pow,←pow_mul,hXpSix] using hh
  have hEM : (E^12+Main)^6≤32*(E^72+Main^6) := by
    simpa only [←pow_mul,show (2:ℝ)^(6-1)=32 by norm_num] using
      add_pow_le (pow_nonneg hE0 12) hMain0 6
  have hZMoment : Z^72≤32*C^6*X^(6*ε)*(E^72+Main^6) := by
    calc
      _ ≤ C^6*X^(6*ε)*(E^12+Main)^6 := hZSix
      _ ≤ C^6*X^(6*ε)*(32*(E^72+Main^6)) :=
        mul_le_mul_of_nonneg_left hEM (mul_nonneg (pow_nonneg hC0 6) hTpow)
      _ = _ := by ac_rfl
  have hWeighted : (M/H)^72*(E^72+Main^6)≤(2:ℝ)^144*V :=
    middleOriginal_weighted_general_integer_moment_bound hXp hM hN hK hH hR hKH hscale
  let Q := (2:ℝ)^149*C^6*X^(6*ε)
  have hQ : 1≤Q := by
    calc
      _ ≤ C^6 := one_le_pow₀ hC
      _ ≤ C^6*X^(6*ε) := le_mul_of_one_le_right (pow_nonneg hC0 6) hTpowOne
      _ ≤ (2:ℝ)^149*(C^6*X^(6*ε)) :=
        le_mul_of_one_le_left (mul_nonneg (pow_nonneg hC0 6) hTpow) (by norm_num)
      _ = Q := (mul_assoc _ _ _).symm
  have hScaledZ : (M/H)^72*Z^72≤Q*V := by
    calc
      _ ≤ (M/H)^72*(32*C^6*X^(6*ε)*(E^72+Main^6)) :=
        mul_le_mul_of_nonneg_left hZMoment hW0
      _ = (32*C^6*X^(6*ε))*((M/H)^72*(E^72+Main^6)) := by ac_rfl
      _ ≤ (32*C^6*X^(6*ε))*((2:ℝ)^144*V) :=
        mul_le_mul_of_nonneg_left hWeighted
          (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hC0 6)) hTpow)
      _ = Q*V := by
        dsimp only [Q]
        rw [show (2:ℝ)^149=32*2^144 by norm_num]
        ac_rfl
  have hDiag : M^144/H^72≤Q*(M^144/H^72) :=
    le_mul_of_one_le_left (by positivity) hQ
  calc
    _ ≤ 32*A^6*L^72*(M^144/H^72+(M/H)^72*Z^72) := hSmain
    _ ≤ 32*A^6*L^72*(Q*(M^144/H^72)+Q*V) :=
      mul_le_mul_of_nonneg_left (add_le_add hDiag hScaledZ)
        (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hA 6)) (pow_nonneg hL 72))
    _ = _ := by
      rw [←mul_add]
      dsimp only [Q,V]
      rw [show (2:ℝ)^154=32*2^149 by norm_num]
      ac_rfl

public  theorem middleOriginal_sharp_extension_power_bound_144
    {u v : ℂ} {D W P E : ℝ} (hD : 0≤D) (hW : 1≤W) (hP : 0≤P) (hE : 0≤E)
    (hsharp : ‖u-v‖≤E) (hv : ‖v‖^144≤D*W*P) :
    ‖u‖^144≤(2:ℝ)^143*(D+E^144)*W*(1+P) := by
  have hW0 := zero_le_one.trans hW
  have hu : ‖u‖≤‖v‖+E := by
    calc
      _ = ‖v+(u-v)‖ := by congr 1; abel
      _ ≤ ‖v‖+‖u-v‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl hsharp
  have hErr : E^144≤E^144*W :=
    le_mul_of_one_le_right (pow_nonneg hE 144) hW
  have hFold : D*W*P+E^144*W≤(D+E^144)*W*(1+P) := by
    nlinarith only [mul_nonneg hD hW0,
      mul_nonneg (mul_nonneg (pow_nonneg hE 144) hW0) hP]
  calc
    _ ≤ (‖v‖+E)^144 := pow_le_pow_left₀ (norm_nonneg _) hu 144
    _ ≤ (2:ℝ)^143*(‖v‖^144+E^144) := add_pow_le (norm_nonneg _) hE 144
    _ ≤ (2:ℝ)^143*(D*W*P+E^144*W) :=
      mul_le_mul_of_nonneg_left (add_le_add hv hErr) (by norm_num)
    _ ≤ (2:ℝ)^143*((D+E^144)*W*(1+P)) :=
      mul_le_mul_of_nonneg_left hFold (by norm_num)
    _ = _ := by ac_rfl

-- Generated closures: source context is replayed in the next part.
end TaoTrudgianYang2025.HuxleyRationalPhase
end
end
