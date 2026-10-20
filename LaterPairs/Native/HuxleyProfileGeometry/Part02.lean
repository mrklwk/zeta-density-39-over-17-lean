module
public import LaterPairs.Native.HuxleyProfileGeometry.Part01

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxErrors 1000
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth
noncomputable section
open Set
namespace TaoTrudgianYang2025.HuxleyLinearForm
end TaoTrudgianYang2025.HuxleyLinearForm
namespace TaoTrudgianYang2025.HuxleyRationalPhase
open Filter
open scoped Topology
open Set
open Polynomial
open Set
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open Filter
open scoped Topology
open scoped ContDiff
open scoped FourierTransform BigOperators


                                                                  
                                                        
                                                         
theorem sourceShiftCorrelation_difference_family_sum
    (F : ℝ → ℝ) {σ T N H : ℝ} (hσ : σ ≠ 0) (hN : N ≠ 0) (hH : H ≠ 0)
    (a L r : ℕ) (hrL : r ≤ L) :
    let P := fun p : ℝ × ℝ => (F p.2-F (p.2+(H/N)*(p.1+1)))/(σ*(H/N))
    sourceShiftCorrelation F T N a L r =
      starRingEnd ℂ (Expdb.exponentialSumAt (fun x => P ((r:ℝ)/H-1,x))
        (σ*T*H/N) N a (a+(L-r))) := by
  intro P
  rw [exponentialSumAt_eq_range,map_sum]
  unfold sourceShiftCorrelation
  rw [show L+1-r=(L-r)+1 by omega]
  apply Finset.sum_congr rfl
  intro j _
  have hphase : (σ*T*H/N)*P ((r:ℝ)/H-1,((a:ℝ)+j)/N) =
      T*(F (((a:ℝ)+j)/N)-F (((a:ℝ)+j+r)/N)) := by
    have hx : ((a:ℝ)+j)/N+(H/N)*((r:ℝ)/H-1+1)=((a:ℝ)+j+r)/N := by
      field_simp
      ring
    dsimp only [P]
    rw [hx]
    field_simp
  unfold Expdb.oscillatory
  rw [hphase,mul_sub,sub_eq_add_neg,AddChar.map_add_eq_mul,AddChar.map_neg_eq_inv,
    Circle.coe_mul,Circle.coe_inv_eq_conj,map_mul (starRingEnd ℂ),Complex.conj_conj]

                                                                        
                                                                   
theorem curvature_surface_hasFDerivAt
    (H : (ℝ × ℝ) → ℝ → ℝ) (ρ : (ℝ × ℝ) → ℝ)
    {z : ℝ × ℝ} {L : (ℝ × ℝ) →L[ℝ] ℝ} {hx : ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hbase : ρ z ∈ I) (hx0 : hx ≠ 0)
    (hH : HasStrictFDerivAt (fun p : (ℝ × ℝ) × ℝ => H p.1 p.2)
      (L.comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)+
        hx • ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ) (z,ρ z))
    (hroot : ∀ᶠ w in 𝓝 z, ρ w ∈ I ∧ H w (ρ w)=H z (ρ z))
    (huniq : ∀ᶠ w in 𝓝 z, Set.InjOn (H w) I) :
    HasFDerivAt ρ (-(hx⁻¹ • L)) z := by
  let M : ((ℝ × ℝ) × ℝ) →L[ℝ] ℝ :=
    L.comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)+
      hx • ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ
  have hleft : M.comp (ContinuousLinearMap.inl ℝ (ℝ × ℝ) ℝ)=L := by
    apply ContinuousLinearMap.ext
    intro v
    simp [M]
  have hright : M.comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ)=
      hx • ContinuousLinearMap.id ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro v
    simp [M]
  have hcomp₁ : (M.comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ)).comp
      (hx⁻¹ • ContinuousLinearMap.id ℝ ℝ)=ContinuousLinearMap.id ℝ ℝ := by
    rw [hright]
    ext
    simp [hx0]
  have hcomp₂ : (hx⁻¹ • ContinuousLinearMap.id ℝ ℝ).comp
      (M.comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ))=ContinuousLinearMap.id ℝ ℝ := by
    rw [hright]
    ext
    simp [hx0]
  have hinv : (M.comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ)).IsInvertible :=
    ContinuousLinearMap.IsInvertible.of_inverse hcomp₁ hcomp₂
  have hinveq : (M.comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ)).inverse=
      hx⁻¹ • ContinuousLinearMap.id ℝ ℝ :=
    ContinuousLinearMap.inverse_eq hcomp₁ hcomp₂
  change HasStrictFDerivAt (fun p : (ℝ × ℝ) × ℝ => H p.1 p.2) M (z,ρ z) at hH
  let ψ := hH.implicitFunctionOfProdDomain hinv
  have hψder : HasFDerivAt ψ (-(hx⁻¹ • L)) z := by
    have hh := (hH.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv).hasFDerivAt
    rw [hinveq,hleft] at hh
    convert hh using 1
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply,neg_apply,smul_apply,ContinuousLinearMap.id_apply]
  have hψin : ∀ᶠ w in 𝓝 z, ψ w ∈ I :=
    (hH.tendsto_implicitFunctionOfProdDomain hinv) (hI.mem_nhds hbase)
  have hψroot := hH.eventually_apply_implicitFunctionOfProdDomain hinv
  have heq : ρ =ᶠ[𝓝 z] ψ := by
    filter_upwards [hroot,huniq,hψin,hψroot] with w hw hu hi he
    exact hu hw.1 hi (hw.2.trans he.symm)
  exact hψder.congr_of_eventuallyEq heq


                                                                          
                                                            
theorem curvature_surface_root_hasFDerivAt
    (H : ℝ × ℝ → ℝ) (ρ : (ℝ × ℝ) → ℝ)
    {z : ℝ × ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hbase : ρ z ∈ I)
    (hH : ContDiffAt ℝ 1 H (z.1,ρ z))
    (hx0 : fderiv ℝ H (z.1,ρ z) (0,1) ≠ 0)
    (hroot : ∀ᶠ w in 𝓝 z, ρ w ∈ I ∧ H (w.1,ρ w)=w.2)
    (huniq : ∀ᶠ w in 𝓝 z, Set.InjOn (fun x => H (w.1,x)) I) :
    HasFDerivAt ρ
      ((-fderiv ℝ H (z.1,ρ z) (1,0)/fderiv ℝ H (z.1,ρ z) (0,1)) •
          ContinuousLinearMap.fst ℝ ℝ ℝ +
        (1/fderiv ℝ H (z.1,ρ z) (0,1)) • ContinuousLinearMap.snd ℝ ℝ ℝ) z := by
  let p : ℝ × ℝ := (z.1,ρ z)
  let B := fderiv ℝ H p (1,0)
  let G := fderiv ℝ H p (0,1)
  let A : ((ℝ × ℝ) × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)
  let C : ((ℝ × ℝ) × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)
  let E : ((ℝ × ℝ) × ℝ) →L[ℝ] (ℝ × ℝ) :=
    A.prod (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ)
  let L : (ℝ × ℝ) →L[ℝ] ℝ :=
    B • ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ
  have hsplit (v : ℝ × ℝ) : fderiv ℝ H p v=B*v.1+G*v.2 := by
    have hv : v=v.1 • (1,0)+v.2 • (0,1) := by ext <;> simp
    rw [hv,map_add,map_smul,map_smul]
    change v.1*B+v.2*G=B*(v.1*1+v.2*0)+G*(v.1*0+v.2*1)
    ring
  have hstrict := (hH.hasStrictFDerivAt (by norm_num : (1:WithTop ℕ∞) ≠ 0)).comp
    (z,ρ z) E.hasStrictFDerivAt
  have hsub := hstrict.sub C.hasStrictFDerivAt
  have hmap : (fderiv ℝ H p).comp E-C =
      L.comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)+
        G • ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [sub_apply,ContinuousLinearMap.comp_apply,
      add_apply,smul_apply,smul_eq_mul]
    rw [hsplit]
    simp [E,A,C,L]
    ring
  have hsub' : HasStrictFDerivAt (fun v : (ℝ × ℝ) × ℝ => H (v.1.1,v.2)-v.1.2)
      (L.comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)+
        G • ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ) (z,ρ z) := by
    change HasStrictFDerivAt (fun v : (ℝ × ℝ) × ℝ => H (v.1.1,v.2)-v.1.2)
      ((fderiv ℝ H p).comp E-C) (z,ρ z) at hsub
    rw [hmap] at hsub
    exact hsub
  have hroot' : ∀ᶠ w in 𝓝 z, ρ w ∈ I ∧
      H (w.1,ρ w)-w.2=H (z.1,ρ z)-z.2 := by
    have hz := (Filter.Eventually.self_of_nhds hroot).2
    filter_upwards [hroot] with w hw
    exact ⟨hw.1,by rw [hw.2,hz,sub_self,sub_self]⟩
  have huniq' : ∀ᶠ w in 𝓝 z, Set.InjOn (fun x => H (w.1,x)-w.2) I := by
    filter_upwards [huniq] with w hw
    intro a ha b hb hab
    exact hw ha hb (sub_left_inj.mp hab)
  have hρ := curvature_surface_hasFDerivAt
    (fun w x => H (w.1,x)-w.2) ρ hI hbase hx0 hsub' hroot' huniq'
  convert hρ using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [L,B,p,div_eq_mul_inv]
  ring


                                                                    
                                                                               
theorem curvature_surface_profile_hasFDerivAt
    (H : ℝ × ℝ → ℝ) (ρ : (ℝ × ℝ) → ℝ)
    {z : ℝ × ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hbase : ρ z ∈ I)
    (hH : ContDiffAt ℝ 2 H (z.1,ρ z))
    (hx0 : fderiv ℝ H (z.1,ρ z) (0,1) ≠ 0)
    (hroot : ∀ᶠ w in 𝓝 z, ρ w ∈ I ∧ H (w.1,ρ w)=w.2)
    (huniq : ∀ᶠ w in 𝓝 z, Set.InjOn (fun x => H (w.1,x)) I) :
    let p := (z.1,ρ z)
    let G := fun v => fderiv ℝ H v (0,1)
    let B := fderiv ℝ H p (1,0)
    let K := fderiv ℝ G p (0,1)
    let Z := fderiv ℝ G p (1,0)
    HasFDerivAt (fun w => G (w.1,ρ w))
      ((Z-K*B/G p) • ContinuousLinearMap.fst ℝ ℝ ℝ+
        (K/G p) • ContinuousLinearMap.snd ℝ ℝ ℝ) z := by
  intro p G B K Z
  have hρ := curvature_surface_root_hasFDerivAt H ρ hI hbase
    (hH.of_le (by norm_num)) hx0 hroot huniq
  have hchart := (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).prodMk hρ
  have hG : ContDiffAt ℝ 1 G p :=
    (hH.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1 ≤ 2)).clm_apply contDiffAt_const
  have hdG := hG.differentiableAt_one.hasFDerivAt
  have hcomp := hdG.comp z hchart
  convert hcomp using 1
  · rfl
  apply ContinuousLinearMap.ext
  intro v
  have hsplit (u : ℝ × ℝ) : fderiv ℝ G p u=Z*u.1+K*u.2 := by
    have hu : u=u.1 • (1,0)+u.2 • (0,1) := by ext <;> simp
    rw [hu,map_add,map_smul,map_smul]
    change u.1*Z+u.2*K=Z*(u.1*1+u.2*0)+K*(u.1*0+u.2*1)
    ring
  simp only [ContinuousLinearMap.comp_apply,add_apply,
    smul_apply,ContinuousLinearMap.prod_apply,smul_eq_mul]
  rw [hsplit]
  change (Z-K*B/G p)*v.1+K/G p*v.2 =
    Z*v.1+K*((-B/G p)*v.1+1/G p*v.2)
  ring


                                                                       
                                                                         
theorem curvature_surface_profile_jacobian
    (H : ℝ × ℝ → ℝ) (ρ : (ℝ × ℝ) → ℝ)
    {z : ℝ × ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hbase : ρ z ∈ I)
    (hH : ContDiffAt ℝ 3 H (z.1,ρ z))
    (hx0 : fderiv ℝ H (z.1,ρ z) (0,1) ≠ 0)
    (hxx0 : fderiv ℝ (fun v => fderiv ℝ H v (0,1)) (z.1,ρ z) (0,1) ≠ 0)
    (hroot : ∀ᶠ w in 𝓝 z, ρ w ∈ I ∧ H (w.1,ρ w)=w.2)
    (huniq : ∀ᶠ w in 𝓝 z, Set.InjOn (fun x => H (w.1,x)) I) :
    let p := (z.1,ρ z)
    let G := fun v => fderiv ℝ H v (0,1)
    let K := fun v => fderiv ℝ G v (0,1)
    let Z := fun v => fderiv ℝ G v (1,0)
    let g := fun w => G (w.1,ρ w)
    let q := fun w => fderiv ℝ g w (0,1)
    fderiv ℝ g z (0,1)*fderiv ℝ q z (1,0)-
        fderiv ℝ q z (0,1)*fderiv ℝ g z (1,0) =
      (K p/G p)^2*deriv (fun x => Z (z.1,x)/K (z.1,x)) (ρ z) := by
  intro p G K Z g q
  let B := fderiv ℝ H p (1,0)
  let L := fderiv ℝ K p (0,1)
  let T := fderiv ℝ K p (1,0)
  let R := (-B/G p) • ContinuousLinearMap.fst ℝ ℝ ℝ+
    (1/G p) • ContinuousLinearMap.snd ℝ ℝ ℝ
  let C := (ContinuousLinearMap.fst ℝ ℝ ℝ).prod R
  have hρ : HasFDerivAt ρ R z := curvature_surface_root_hasFDerivAt H ρ hI hbase
    (hH.of_le (by norm_num)) hx0 hroot huniq
  have hchart : HasFDerivAt (fun w : ℝ × ℝ => (w.1,ρ w)) C z :=
    hasFDerivAt_fst.prodMk hρ
  have hG : ContDiffAt ℝ 2 G p :=
    (hH.fderiv_right (by norm_num : (2:WithTop ℕ∞)+1 ≤ 3)).clm_apply contDiffAt_const
  have hK : ContDiffAt ℝ 1 K p :=
    (hG.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1 ≤ 2)).clm_apply contDiffAt_const
  have hZ : ContDiffAt ℝ 1 Z p :=
    (hG.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1 ≤ 2)).clm_apply contDiffAt_const
  have hdG := (hG.of_le (by norm_num : (1:WithTop ℕ∞) ≤ 2)).differentiableAt_one.hasFDerivAt
  have hdK := hK.differentiableAt_one.hasFDerivAt
  have hgd := curvature_surface_profile_hasFDerivAt H ρ hI hbase
    (hH.of_le (by norm_num)) hx0 hroot huniq
  have hgx : fderiv ℝ g z (0,1)=K p/G p := by
    rw [hgd.fderiv]
    simp [K,G,p]
  have hgy : fderiv ℝ g z (1,0)=Z p-K p*B/G p := by
    rw [hgd.fderiv]
    simp [B,Z,K,G,p]
  have hnearH : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 2 H (w.1,ρ w) :=
    hchart.continuousAt ((hH.of_le (by norm_num : (2:WithTop ℕ∞) ≤ 3)).eventually
      (by norm_num))
  have hnearG : ∀ᶠ w in 𝓝 z, G (w.1,ρ w) ≠ 0 :=
    hchart.continuousAt (hG.continuousAt.eventually_ne hx0)
  have heq : q =ᶠ[𝓝 z] (fun w => K (w.1,ρ w)/G (w.1,ρ w)) := by
    filter_upwards [hnearH,hnearG,hroot,hroot.eventually_nhds,huniq.eventually_nhds]
      with w hwH hwG hwroot hwr hwu
    have hd := curvature_surface_profile_hasFDerivAt H ρ hI hwroot.1 hwH hwG hwr hwu
    change fderiv ℝ g w (0,1)=_
    rw [hd.fderiv]
    simp [K,G]
  have hinv := (hasDerivAt_inv hx0).comp_hasFDerivAt p hdG
  have hquot : HasFDerivAt (fun v => K v/G v)
      ((G p)⁻¹ • fderiv ℝ K p+
        K p • (-(G p^2)⁻¹ • fderiv ℝ G p)) p := by
    convert hdK.mul hinv using 1
    · rfl
    · simp only [G,p,Function.comp_apply,add_comm]
  have hqd := (hquot.comp z hchart).congr_of_eventuallyEq heq
  have hKG (v : ℝ × ℝ) : fderiv ℝ K p v=T*v.1+L*v.2 := by
    have hv : v=v.1 • (1,0)+v.2 • (0,1) := by ext <;> simp
    rw [hv,map_add,map_smul,map_smul]
    change v.1*T+v.2*L=T*(v.1*1+v.2*0)+L*(v.1*0+v.2*1)
    ring
  have hGG (v : ℝ × ℝ) : fderiv ℝ G p v=Z p*v.1+K p*v.2 := by
    have hv : v=v.1 • (1,0)+v.2 • (0,1) := by ext <;> simp
    rw [hv,map_add,map_smul,map_smul]
    change v.1*Z p+v.2*K p=Z p*(v.1*1+v.2*0)+K p*(v.1*0+v.2*1)
    ring
  have hqx : fderiv ℝ q z (0,1)=(L*G p-K p^2)/G p^3 := by
    rw [hqd.fderiv]
    simp only [ContinuousLinearMap.comp_apply,add_apply,
      smul_apply,smul_eq_mul]
    rw [hKG,hGG]
    simp [C,R]
    field_simp [show G p ≠ 0 from hx0]
    ring
  have hqy : fderiv ℝ q z (1,0)=
      (T*G p-K p*Z p)/G p^2-B*(L*G p-K p^2)/G p^3 := by
    rw [hqd.fderiv]
    simp only [ContinuousLinearMap.comp_apply,add_apply,
      smul_apply,smul_eq_mul]
    rw [hKG,hGG]
    simp [C,R]
    field_simp [show G p ≠ 0 from hx0]
    ring
  have hD := (hG.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1 ≤ 2)).differentiableAt_one.hasFDerivAt
  have hKd := hD.clm_apply (hasFDerivAt_const ((0,1):ℝ × ℝ) p)
  have hZd := hD.clm_apply (hasFDerivAt_const ((1,0):ℝ × ℝ) p)
  have hsym : fderiv ℝ Z p (0,1)=T := by
    rw [hZd.fderiv]
    change _=fderiv ℝ K p (1,0)
    rw [hKd.fderiv]
    simpa using hG.isSymmSndFDerivAt (by norm_num) (0,1) (1,0)
  have hline : HasDerivAt (fun x : ℝ => (z.1,x)) (0,1) (ρ z) :=
    (hasDerivAt_const (ρ z) z.1).prodMk (hasDerivAt_id (ρ z))
  have hZline := hZ.differentiableAt_one.hasFDerivAt.comp_hasDerivAt (ρ z) hline
  have hKline := hdK.comp_hasDerivAt (ρ z) hline
  have hratio : deriv (fun x => Z (z.1,x)/K (z.1,x)) (ρ z)=
      (T*K p-Z p*L)/K p^2 := by
    have hh := (hZline.div hKline hxx0).deriv
    change deriv (fun x => Z (z.1,x)/K (z.1,x)) (ρ z)=
      (fderiv ℝ Z p (0,1)*K p-Z p*L)/K p^2 at hh
    rw [hsym] at hh
    exact hh
  rw [hgx,hgy,hqx,hqy,hratio]
  field_simp [show G p ≠ 0 from hx0,show K p ≠ 0 from hxx0]
  ring


                                                                      
                                                                          
                                                                             
theorem positive_difference_inverse_profile_jacobian_lower
    (F : ℝ → ℝ) (ρ : (ℝ × ℝ) → ℝ)
    {σ c U η : ℝ} {z : ℝ × ℝ} {I : Set ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hx : ρ z ∈ Icc (3/4:ℝ) (9/4)) (hy : z.1 ∈ Icc (1/2:ℝ) 3)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hI : IsOpen I) (hbase : ρ z ∈ I)
    (hroot : ∀ᶠ w in 𝓝 z, ρ w ∈ I ∧
      (iteratedDeriv 2 F (ρ w)-iteratedDeriv 2 F (ρ w+η*w.1))/(σ*η)=w.2)
    (huniq : ∀ᶠ w in 𝓝 z, Set.InjOn
      (fun x => (iteratedDeriv 2 F x-iteratedDeriv 2 F (x+η*w.1))/(σ*η)) I) :
    let H := fun v : ℝ × ℝ =>
      (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
    let G := fun v => fderiv ℝ H v (0,1)
    let g := fun w => G (w.1,ρ w)
    let q := fun w => fderiv ℝ g w (0,1)
    (c/(6*U))^2*(c^2*c/(6*U^4)) ≤
      |fderiv ℝ g z (0,1)*fderiv ℝ q z (1,0)-
        fderiv ℝ q z (0,1)*fderiv ℝ g z (1,0)| := by
  intro H G g q
  let p : ℝ × ℝ := (z.1,ρ z)
  let J := fun v : ℝ × ℝ =>
    (iteratedDeriv 3 F v.2-iteratedDeriv 3 F (v.2+η*v.1))/(σ*η)
  let K := fun v => fderiv ℝ G v (0,1)
  let Z := fun v => fderiv ℝ G v (1,0)
  have hx0 : 0 < ρ z := by linarith only [hx.1]
  have hy0 : 0 < z.1 := by linarith only [hy.1]
  have hz0 : 0 < ρ z+η*z.1 := add_pos hx0 (mul_pos hη hy0)
  have hGerm (v : ℝ × ℝ) (hv : 0 < v.2) (hv' : 0 < v.2+η*v.1) :
      G =ᶠ[𝓝 v] J := by
    have hcv : ContinuousAt (fun w : ℝ × ℝ => w.2+η*w.1) v := by fun_prop
    have hn₀ : ∀ᶠ w : ℝ × ℝ in 𝓝 v, 0 < w.2 := continuousAt_snd (Ioi_mem_nhds hv)
    have hn₁ : ∀ᶠ w : ℝ × ℝ in 𝓝 v, 0 < w.2+η*w.1 := hcv (Ioi_mem_nhds hv')
    filter_upwards [hn₀,hn₁] with w hw hw'
    exact (positive_difference_curvature_directions F (σ:=σ) hw hw' hf 2).2.1
  have hGp := hGerm p hx0 hz0
  have he₃ := positive_jets_difference_curvature_entry F hσ hc hU hη hηmax
    hx hy hf hbound htests 3 (by norm_num) (by norm_num)
  have he₄ := positive_jets_difference_curvature_entry F hσ hc hU hη hηmax
    hx hy hf hbound htests 4 (by norm_num) (by norm_num)
  have hGlow : c/(2*σ) ≤ |G p| := he₃.2.2.2.1
  have hKlow : c/(2*σ) ≤ |K p| := by
    change c/(2*σ) ≤ |fderiv ℝ G p (0,1)|
    rw [hGp.fderiv_eq]
    exact he₄.2.2.2.1
  have hG0 : G p ≠ 0 := abs_pos.mp (lt_of_lt_of_le (by positivity) hGlow)
  have hK0 : K p ≠ 0 := abs_pos.mp (lt_of_lt_of_le (by positivity) hKlow)
  have hGup : |G p| ≤ 3*U/σ := by
    rw [hGp.self_of_nhds]
    have hj : iteratedDeriv 3 (fun x => (F x-F (x+η*z.1))/(σ*η)) (ρ z)=J p := he₄.1
    rw [←hj]
    simpa only [iteratedDeriv_zero] using
      positive_jets_difference_mixed_upper F hσ hU hη hηmax hx hy hf hbound
        3 0 (by norm_num) (by norm_num)
  have hratio : c^2*c/(6*U^4) ≤
      |deriv (fun x => Z (z.1,x)/K (z.1,x)) (ρ z)| := by
    have heq : (fun x => Z (z.1,x)/K (z.1,x)) =ᶠ[𝓝 (ρ z)]
        (fun x => fderiv ℝ J (z.1,x) (1,0)/fderiv ℝ J (z.1,x) (0,1)) := by
      filter_upwards [Ioi_mem_nhds hx0] with x hxp
      change fderiv ℝ G (z.1,x) (1,0)/fderiv ℝ G (z.1,x) (0,1)=_
      rw [(hGerm (z.1,x) hxp (add_pos hxp (mul_pos hη hy0))).fderiv_eq]
    rw [heq.deriv_eq]
    exact he₄.2.2.2.2
  have hH : ContDiffAt ℝ 3 H p :=
    (positive_difference_curvature_directions F (σ:=σ) hx0 hz0 hf 2).1.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hid := curvature_surface_profile_jacobian H ρ hI hbase hH hG0 hK0 hroot huniq
  change _=(K p/G p)^2*deriv (fun x => Z (z.1,x)/K (z.1,x)) (ρ z) at hid
  rw [hid,abs_mul,abs_of_nonneg (sq_nonneg _)]
  have hfrac : c/(6*U) ≤ |K p/G p| := by
    rw [abs_div]
    calc
      _ = (c/(2*σ))/(3*U/σ) := by field_simp; ring
      _ ≤ _ := div_le_div₀ (abs_nonneg _) hKlow (abs_pos.mpr hG0) hGup
  have hsq : (c/(6*U))^2 ≤ (K p/G p)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (by positivity) (abs_nonneg _)).mpr hfrac
  exact mul_le_mul hsq hratio (by positivity) (sq_nonneg _)

                                                                    
                                                                               
                                                                          
theorem planar_profile_quantitative_separation
    (Φ : ℝ × ℝ → ℝ × ℝ) {S : Set (ℝ × ℝ)} {p q : ℝ × ℝ}
    {κ M ε : ℝ} (hM : 0 ≤ M)
    (hsmall : 4*M*ε ≤ κ)
    (hS : Convex ℝ S) (hp : p ∈ S) (hq : q ∈ S)
    (hΦ : ∀ w ∈ S, DifferentiableAt ℝ Φ w)
    (hvar : ∀ w ∈ S, ‖fderiv ℝ Φ w-fderiv ℝ Φ p‖ ≤ ε)
    (hcol₁ : ‖fderiv ℝ Φ p (1,0)‖ ≤ M)
    (hcol₂ : ‖fderiv ℝ Φ p (0,1)‖ ≤ M)
    (hdet : κ ≤ |(fderiv ℝ Φ p (1,0)).1*(fderiv ℝ Φ p (0,1)).2-
      (fderiv ℝ Φ p (0,1)).1*(fderiv ℝ Φ p (1,0)).2|) :
    κ*‖q-p‖ ≤ 4*M*‖Φ q-Φ p‖ := by
  let D := fderiv ℝ Φ p
  let a := (D (1,0)).1
  let b := (D (0,1)).1
  let c := (D (1,0)).2
  let d := (D (0,1)).2
  have ha : |a| ≤ M := (norm_fst_le (D (1,0))).trans hcol₁
  have hb : |b| ≤ M := (norm_fst_le (D (0,1))).trans hcol₂
  have hc : |c| ≤ M := (norm_snd_le (D (1,0))).trans hcol₁
  have hd : |d| ≤ M := (norm_snd_le (D (0,1))).trans hcol₂
  have hmat (v : ℝ × ℝ) : D v=(a*v.1+b*v.2,c*v.1+d*v.2) := by
    have hv : v=v.1 • (1,0)+v.2 • (0,1) := by ext <;> simp
    calc
      D v=D (v.1 • (1,0)+v.2 • (0,1)) := congrArg D hv
      _ = _ := by rw [map_add,map_smul,map_smul]; ext <;> simp [a,b,c,d,mul_comm]
  have hlin (v : ℝ × ℝ) : κ*‖v‖ ≤ 2*M*‖D v‖ := by
    have hi₁ : (a*d-b*c)*v.1=d*(D v).1-b*(D v).2 := by rw [hmat]; ring
    have hi₂ : (a*d-b*c)*v.2=a*(D v).2-c*(D v).1 := by rw [hmat]; ring
    have he₁ : κ*|v.1| ≤ 2*M*‖D v‖ := by
      calc
        _ ≤ |a*d-b*c| *|v.1| := mul_le_mul_of_nonneg_right hdet (abs_nonneg _)
        _ = |d*(D v).1-b*(D v).2| := by rw [←abs_mul,hi₁]
        _ ≤ |d| *|(D v).1|+|b| *|(D v).2| := by
          simpa only [Real.norm_eq_abs,abs_mul] using norm_sub_le (d*(D v).1) (b*(D v).2)
        _ ≤ M*‖D v‖+M*‖D v‖ :=
          add_le_add (mul_le_mul hd (norm_fst_le (D v)) (abs_nonneg _) hM)
            (mul_le_mul hb (norm_snd_le (D v)) (abs_nonneg _) hM)
        _ = _ := by ring
    have he₂ : κ*|v.2| ≤ 2*M*‖D v‖ := by
      calc
        _ ≤ |a*d-b*c| *|v.2| := mul_le_mul_of_nonneg_right hdet (abs_nonneg _)
        _ = |a*(D v).2-c*(D v).1| := by rw [←abs_mul,hi₂]
        _ ≤ |a| *|(D v).2|+|c| *|(D v).1| := by
          simpa only [Real.norm_eq_abs,abs_mul] using norm_sub_le (a*(D v).2) (c*(D v).1)
        _ ≤ M*‖D v‖+M*‖D v‖ :=
          add_le_add (mul_le_mul ha (norm_snd_le (D v)) (abs_nonneg _) hM)
            (mul_le_mul hc (norm_fst_le (D v)) (abs_nonneg _) hM)
        _ = _ := by ring
    rcases le_total |v.1| |v.2| with hh | hh
    · simpa only [Prod.norm_def,Real.norm_eq_abs,max_eq_right hh] using he₂
    · simpa only [Prod.norm_def,Real.norm_eq_abs,max_eq_left hh] using he₁
  have ht : ‖Φ q-Φ p-D (q-p)‖ ≤ ε*‖q-p‖ :=
    hS.norm_image_sub_le_of_norm_fderiv_le' hΦ hvar hp hq
  have hbD : ‖D (q-p)‖ ≤ ‖Φ q-Φ p‖+ε*‖q-p‖ := by
    calc
      _ ≤ ‖Φ q-Φ p‖+‖Φ q-Φ p-D (q-p)‖ := by
        convert norm_sub_le (Φ q-Φ p) (Φ q-Φ p-D (q-p)) using 1
        congr 1
        abel
      _ ≤ _ := add_le_add le_rfl ht
  have hm := mul_le_mul_of_nonneg_left hbD (show 0 ≤ 2*M by positivity)
  have hs := mul_le_mul_of_nonneg_right hsmall (norm_nonneg (q-p))
  have hl := hlin (q-p)
  nlinarith only [hm,hs,hl]


                                                                    
                                                                         
                                                                        
theorem scalar_surface_contDiffAt
    (F : (ℝ × ℝ) × ℝ → ℝ) (ρ : ℝ × ℝ → ℝ)
    {n : ℕ∞ω} {z : ℝ × ℝ} {I : Set ℝ}
    (hn : n ≠ 0) (hI : IsOpen I) (hbase : ρ z ∈ I)
    (hF : ContDiffAt ℝ n F (z,ρ z))
    (hx : fderiv ℝ F (z,ρ z) ((0,0),1) ≠ 0)
    (hroot : ∀ᶠ w in 𝓝 z, ρ w ∈ I ∧ F (w,ρ w)=F (z,ρ z))
    (huniq : ∀ᶠ w in 𝓝 z, Set.InjOn (fun x => F (w,x)) I) :
    ContDiffAt ℝ n ρ z := by
  let D := fderiv ℝ F (z,ρ z)
  let a := D ((0,0),1)
  have hright : D.comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ)=
      a • ContinuousLinearMap.id ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro v
    change D ((0,0),v)=a*v
    have he : (((0,0),v):(ℝ × ℝ) × ℝ)=v • ((0,0),1) := by ext <;> simp
    rw [he,map_smul]
    change v*a=a*v
    ring
  have hcomp₁ : (D.comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ)).comp
      (a⁻¹ • ContinuousLinearMap.id ℝ ℝ)=ContinuousLinearMap.id ℝ ℝ := by
    rw [hright]
    ext
    simp [show a ≠ 0 from hx]
  have hcomp₂ : (a⁻¹ • ContinuousLinearMap.id ℝ ℝ).comp
      (D.comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ))=ContinuousLinearMap.id ℝ ℝ := by
    rw [hright]
    ext
    simp [show a ≠ 0 from hx]
  have hinv : (D.comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ)).IsInvertible :=
    ContinuousLinearMap.IsInvertible.of_inverse hcomp₁ hcomp₂
  let ψ := hF.implicitFunction hn hinv
  have hψ : ContDiffAt ℝ n ψ z := hF.contDiffAt_implicitFunction hn hinv
  have hψbase : ψ z=ρ z := hF.implicitFunction_apply_self hn hinv
  have hψin : ∀ᶠ w in 𝓝 z, ψ w ∈ I :=
    hψ.continuousAt (hI.mem_nhds (hψbase.symm ▸ hbase))
  have hψroot := hF.eventually_apply_implicitFunction hn hinv
  have heq : ρ =ᶠ[𝓝 z] ψ := by
    filter_upwards [hroot,huniq,hψin,hψroot] with w hw hu hi he
    exact hu hw.1 hi (hw.2.trans he.symm)
  exact hψ.congr_of_eventuallyEq heq


                                                                         
                                                                                
theorem curvature_surface_root_contDiffAt
    (H : ℝ × ℝ → ℝ) (ρ : ℝ × ℝ → ℝ)
    {n : ℕ∞ω} {z : ℝ × ℝ} {I : Set ℝ}
    (hn : n ≠ 0) (hI : IsOpen I) (hbase : ρ z ∈ I)
    (hH : ContDiffAt ℝ n H (z.1,ρ z))
    (hx : fderiv ℝ H (z.1,ρ z) (0,1) ≠ 0)
    (hroot : ∀ᶠ w in 𝓝 z, ρ w ∈ I ∧ H (w.1,ρ w)=w.2)
    (huniq : ∀ᶠ w in 𝓝 z, Set.InjOn (fun x => H (w.1,x)) I) :
    ContDiffAt ℝ n ρ z := by
  let E : ((ℝ × ℝ) × ℝ) →L[ℝ] (ℝ × ℝ) :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)).prod
        (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ)
  let C : ((ℝ × ℝ) × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)
  let F := fun v : (ℝ × ℝ) × ℝ => H (v.1.1,v.2)-v.1.2
  have hF : ContDiffAt ℝ n F (z,ρ z) :=
    (hH.comp (z,ρ z) E.contDiff.contDiffAt).sub C.contDiff.contDiffAt
  have hd := ((hH.hasStrictFDerivAt hn).comp (z,ρ z) E.hasStrictFDerivAt).sub
    C.hasStrictFDerivAt
  have he : fderiv ℝ F (z,ρ z)=
      (fderiv ℝ H (z.1,ρ z)).comp E-C := hd.hasFDerivAt.fderiv
  have hx' : fderiv ℝ F (z,ρ z) ((0,0),1) ≠ 0 := by
    rw [he]
    simpa [E,C] using hx
  apply scalar_surface_contDiffAt F ρ hn hI hbase hF hx'
  · have hz := hroot.self_of_nhds
    filter_upwards [hroot] with w hw
    exact ⟨hw.1,by dsimp [F]; rw [hw.2,hz.2,sub_self,sub_self]⟩
  · filter_upwards [huniq] with w hw
    intro a ha b hb hab
    exact hw ha hb (sub_left_inj.mp hab)


                                                                      
                                                                         
                                                                    
theorem curvature_surface_profile_derivative_matrix
    (H : ℝ × ℝ → ℝ) (ρ : (ℝ × ℝ) → ℝ)
    {z : ℝ × ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hbase : ρ z ∈ I)
    (hH : ContDiffAt ℝ 3 H (z.1,ρ z))
    (hx0 : fderiv ℝ H (z.1,ρ z) (0,1) ≠ 0)
    (hroot : ∀ᶠ w in 𝓝 z, ρ w ∈ I ∧ H (w.1,ρ w)=w.2)
    (huniq : ∀ᶠ w in 𝓝 z, Set.InjOn (fun x => H (w.1,x)) I) :
    let p := (z.1,ρ z)
    let G := fun v => fderiv ℝ H v (0,1)
    let K := fun v => fderiv ℝ G v (0,1)
    let Z := fun v => fderiv ℝ G v (1,0)
    let g := fun w => G (w.1,ρ w)
    let q := fun w => fderiv ℝ g w (0,1)
    fderiv ℝ (fun w => (g w,q w)) z (1,0) =
      (Z p-K p*fderiv ℝ H p (1,0)/G p,
       (fderiv ℝ K p (1,0)*G p-K p*Z p)/G p^2-
        fderiv ℝ H p (1,0)*(fderiv ℝ K p (0,1)*G p-K p^2)/G p^3) ∧
    fderiv ℝ (fun w => (g w,q w)) z (0,1) =
      (K p/G p,(fderiv ℝ K p (0,1)*G p-K p^2)/G p^3) := by
  intro p G K Z g q
  let B := fderiv ℝ H p (1,0)
  let L := fderiv ℝ K p (0,1)
  let T := fderiv ℝ K p (1,0)
  let R := (-B/G p) • ContinuousLinearMap.fst ℝ ℝ ℝ+
    (1/G p) • ContinuousLinearMap.snd ℝ ℝ ℝ
  let C := (ContinuousLinearMap.fst ℝ ℝ ℝ).prod R
  have hρ : HasFDerivAt ρ R z := curvature_surface_root_hasFDerivAt H ρ hI hbase
    (hH.of_le (by norm_num)) hx0 hroot huniq
  have hchart : HasFDerivAt (fun w : ℝ × ℝ => (w.1,ρ w)) C z :=
    hasFDerivAt_fst.prodMk hρ
  have hG : ContDiffAt ℝ 2 G p :=
    (hH.fderiv_right (by norm_num : (2:WithTop ℕ∞)+1 ≤ 3)).clm_apply contDiffAt_const
  have hK : ContDiffAt ℝ 1 K p :=
    (hG.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1 ≤ 2)).clm_apply contDiffAt_const
  have hdG := (hG.of_le (by norm_num : (1:WithTop ℕ∞) ≤ 2)).differentiableAt_one.hasFDerivAt
  have hdK := hK.differentiableAt_one.hasFDerivAt
  have hgd := curvature_surface_profile_hasFDerivAt H ρ hI hbase
    (hH.of_le (by norm_num)) hx0 hroot huniq
  have hgx : fderiv ℝ g z (0,1)=K p/G p := by
    rw [hgd.fderiv]
    simp [K,G,p]
  have hgy : fderiv ℝ g z (1,0)=Z p-K p*B/G p := by
    rw [hgd.fderiv]
    simp [B,Z,K,G,p]
  have hnearH : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 2 H (w.1,ρ w) :=
    hchart.continuousAt ((hH.of_le (by norm_num : (2:WithTop ℕ∞) ≤ 3)).eventually
      (by norm_num))
  have hnearG : ∀ᶠ w in 𝓝 z, G (w.1,ρ w) ≠ 0 :=
    hchart.continuousAt (hG.continuousAt.eventually_ne hx0)
  have heq : q =ᶠ[𝓝 z] (fun w => K (w.1,ρ w)/G (w.1,ρ w)) := by
    filter_upwards [hnearH,hnearG,hroot,hroot.eventually_nhds,huniq.eventually_nhds]
      with w hwH hwG hwroot hwr hwu
    have hd := curvature_surface_profile_hasFDerivAt H ρ hI hwroot.1 hwH hwG hwr hwu
    change fderiv ℝ g w (0,1)=_
    rw [hd.fderiv]
    simp [K,G]
  have hinv := (hasDerivAt_inv hx0).comp_hasFDerivAt p hdG
  have hquot : HasFDerivAt (fun v => K v/G v)
      ((G p)⁻¹ • fderiv ℝ K p+
        K p • (-(G p^2)⁻¹ • fderiv ℝ G p)) p := by
    convert hdK.mul hinv using 1
    · rfl
    · simp only [G,p,Function.comp_apply,add_comm]
  have hqd := (hquot.comp z hchart).congr_of_eventuallyEq heq
  have hKG (v : ℝ × ℝ) : fderiv ℝ K p v=T*v.1+L*v.2 := by
    have hv : v=v.1 • (1,0)+v.2 • (0,1) := by ext <;> simp
    rw [hv,map_add,map_smul,map_smul]
    change v.1*T+v.2*L=T*(v.1*1+v.2*0)+L*(v.1*0+v.2*1)
    ring
  have hGG (v : ℝ × ℝ) : fderiv ℝ G p v=Z p*v.1+K p*v.2 := by
    have hv : v=v.1 • (1,0)+v.2 • (0,1) := by ext <;> simp
    rw [hv,map_add,map_smul,map_smul]
    change v.1*Z p+v.2*K p=Z p*(v.1*1+v.2*0)+K p*(v.1*0+v.2*1)
    ring
  have hqx : fderiv ℝ q z (0,1)=(L*G p-K p^2)/G p^3 := by
    rw [hqd.fderiv]
    simp only [ContinuousLinearMap.comp_apply,add_apply,
      smul_apply,smul_eq_mul]
    rw [hKG,hGG]
    simp [C,R]
    field_simp [show G p ≠ 0 from hx0]
    ring
  have hqy : fderiv ℝ q z (1,0)=
      (T*G p-K p*Z p)/G p^2-B*(L*G p-K p^2)/G p^3 := by
    rw [hqd.fderiv]
    simp only [ContinuousLinearMap.comp_apply,add_apply,
      smul_apply,smul_eq_mul]
    rw [hKG,hGG]
    simp [C,R]
    field_simp [show G p ≠ 0 from hx0]
    ring
  have hΦ : HasFDerivAt (fun w => (g w,q w))
      ((fderiv ℝ g z).prod (fderiv ℝ q z)) z :=
    hgd.differentiableAt.hasFDerivAt.prodMk hqd.differentiableAt.hasFDerivAt
  rw [hΦ.fderiv]
  exact ⟨Prod.ext hgy hqy,Prod.ext hgx hqx⟩


private theorem profile_matrix_entries_bound
    {B G K Z L T R : ℝ} (hR : 1 ≤ R)
    (hB : |B| ≤ R) (hG : |G| ≤ R) (hK : |K| ≤ R) (hZ : |Z| ≤ R)
    (hL : |L| ≤ R) (hT : |T| ≤ R) (hinv : |G⁻¹| ≤ R) :
    |Z-K*B/G| ≤ 4*R^6 ∧ |K/G| ≤ 4*R^6 ∧
    |(T*G-K*Z)/G^2-B*(L*G-K^2)/G^3| ≤ 4*R^6 ∧
    |(L*G-K^2)/G^3| ≤ 4*R^6 := by
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hab (a b : ℝ) : |a-b| ≤ |a|+|b| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le a b
  have hLG : |L*G-K^2| ≤ 2*R^2 := by
    calc
      _ ≤ |L| * |G|+|K|^2 := by
        simpa only [abs_mul,_root_.abs_pow] using hab (L*G) (K^(2:ℕ))
      _ ≤ R*R+R^2 := by gcongr
      _ = _ := by ring
  have hTG : |T*G-K*Z| ≤ 2*R^2 := by
    calc
      _ ≤ |T| * |G|+|K| * |Z| := by simpa only [abs_mul] using hab (T*G) (K*Z)
      _ ≤ R*R+R*R := by gcongr
      _ = _ := by ring
  have hp₁ : R ≤ R^6 := by simpa using pow_le_pow_right₀ hR (show 1 ≤ 6 by norm_num)
  have hp₂ : R^2 ≤ R^6 := pow_le_pow_right₀ hR (by norm_num)
  have hp₃ : R^3 ≤ R^6 := pow_le_pow_right₀ hR (by norm_num)
  have hp₄ : R^4 ≤ R^6 := pow_le_pow_right₀ hR (by norm_num)
  have hp₅ : R^5 ≤ R^6 := pow_le_pow_right₀ hR (by norm_num)
  have hgY : |Z-K*B/G| ≤ R+R^3 := by
    calc
      _ ≤ |Z|+|K| * |B| * |G⁻¹| := by simpa only [div_eq_mul_inv,abs_mul] using hab Z (K*B/G)
      _ ≤ R+R*R*R := by gcongr
      _ = _ := by ring
  have hgU : |K/G| ≤ R^2 := by
    rw [div_eq_mul_inv,abs_mul]
    calc
      _ ≤ R*R := mul_le_mul hK hinv (abs_nonneg _) hR0
      _ = _ := by ring
  have hqU : |(L*G-K^2)/G^3| ≤ 2*R^5 := by
    rw [div_eq_mul_inv,←inv_pow,abs_mul,_root_.abs_pow]
    calc
      _ ≤ (2*R^2)*R^3 := by gcongr
      _ = _ := by ring
  have hqY : |(T*G-K*Z)/G^2-B*(L*G-K^2)/G^3| ≤ 2*R^4+2*R^6 := by
    calc
      _ ≤ |T*G-K*Z| * |G⁻¹|^2+|B| * |L*G-K^2| * |G⁻¹|^3 := by
        simpa only [div_eq_mul_inv,←inv_pow,abs_mul,_root_.abs_pow] using
          hab ((T*G-K*Z)/G^(2:ℕ)) (B*(L*G-K^(2:ℕ))/G^(3:ℕ))
      _ ≤ (2*R^2)*R^2+R*(2*R^2)*R^3 := by gcongr
      _ = _ := by ring
  refine ⟨?_,?_,?_,?_⟩
  · nlinarith only [hgY,hp₁,hp₃,sq_nonneg (R^3)]
  · nlinarith only [hgU,hp₂,sq_nonneg (R^3)]
  · linarith only [hqY,hp₄]
  · nlinarith only [hqU,hp₅,sq_nonneg (R^3)]


                                                                        
                                                               
theorem curvature_surface_profile_columns_bound
    (H : ℝ × ℝ → ℝ) (ρ : ℝ × ℝ → ℝ)
    {z : ℝ × ℝ} {I : Set ℝ} {R : ℝ}
    (hR : 1 ≤ R) (hI : IsOpen I) (hbase : ρ z ∈ I)
    (hH : ContDiffAt ℝ 3 H (z.1,ρ z))
    (hx0 : fderiv ℝ H (z.1,ρ z) (0,1) ≠ 0)
    (hroot : ∀ᶠ w in 𝓝 z, ρ w ∈ I ∧ H (w.1,ρ w)=w.2)
    (huniq : ∀ᶠ w in 𝓝 z, Set.InjOn (fun x => H (w.1,x)) I) :
    let p := (z.1,ρ z)
    let G := fun v => fderiv ℝ H v (0,1)
    let K := fun v => fderiv ℝ G v (0,1)
    let Z := fun v => fderiv ℝ G v (1,0)
    let g := fun w => G (w.1,ρ w)
    let Φ := fun w => (g w,fderiv ℝ g w (0,1))
    |fderiv ℝ H p (1,0)| ≤ R →
    |G p| ≤ R → |K p| ≤ R → |Z p| ≤ R →
    |fderiv ℝ K p (0,1)| ≤ R → |fderiv ℝ K p (1,0)| ≤ R →
    |(G p)⁻¹| ≤ R →
    ‖fderiv ℝ Φ z (1,0)‖ ≤ 4*R^6 ∧ ‖fderiv ℝ Φ z (0,1)‖ ≤ 4*R^6 := by
  intro p G K Z g Φ hB hG hK hZ hL hT hinv
  have he := curvature_surface_profile_derivative_matrix H ρ hI hbase hH hx0 hroot huniq
  have hb := profile_matrix_entries_bound hR hB hG hK hZ hL hT hinv
  constructor
  · rw [he.1]
    exact max_le hb.1 hb.2.2.1
  · rw [he.2]
    exact max_le hb.2.1 hb.2.2.2


                                                                        
                                                                           
theorem positive_difference_inverse_profile_columns_bound
    (F : ℝ → ℝ) (ρ : ℝ × ℝ → ℝ)
    {σ c U η : ℝ} {z : ℝ × ℝ} {I : Set ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hx : ρ z ∈ Icc (3/4:ℝ) (9/4)) (hy : z.1 ∈ Icc (1/2:ℝ) 3)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hI : IsOpen I) (hbase : ρ z ∈ I)
    (hroot : ∀ᶠ w in 𝓝 z, ρ w ∈ I ∧
      (iteratedDeriv 2 F (ρ w)-iteratedDeriv 2 F (ρ w+η*w.1))/(σ*η)=w.2)
    (huniq : ∀ᶠ w in 𝓝 z, Set.InjOn
      (fun x => (iteratedDeriv 2 F x-iteratedDeriv 2 F (x+η*w.1))/(σ*η)) I) :
    let H := fun v : ℝ × ℝ =>
      (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
    let g := fun w => fderiv ℝ H (w.1,ρ w) (0,1)
    let Φ := fun w => (g w,fderiv ℝ g w (0,1))
    let R := max 1 (max (3*U/σ) (2*σ/c))
    ‖fderiv ℝ Φ z (1,0)‖ ≤ 4*R^6 ∧ ‖fderiv ℝ Φ z (0,1)‖ ≤ 4*R^6 := by
  intro H g Φ R
  let p : ℝ × ℝ := (z.1,ρ z)
  let J := fun (r : ℕ) (v : ℝ × ℝ) =>
    (iteratedDeriv r F v.2-iteratedDeriv r F (v.2+η*v.1))/(σ*η)
  let G := fun v => fderiv ℝ H v (0,1)
  let K := fun v => fderiv ℝ G v (0,1)
  have hx0 : 0 < ρ z := by linarith only [hx.1]
  have hy0 : 0 < z.1 := by linarith only [hy.1]
  have hz0 : 0 < ρ z+η*z.1 := add_pos hx0 (mul_pos hη hy0)
  have hzI : ρ z+η*z.1 ∈ Icc (1/2:ℝ) 3 := by
    have hb := mul_le_mul hηmax hy.2 hy0.le (by norm_num : (0:ℝ) ≤ 1/8)
    constructor <;> nlinarith only [hx.1,hx.2,hb,mul_pos hη hy0]
  have hGerm (r : ℕ) (v : ℝ × ℝ) (hv : 0 < v.2) (hv' : 0 < v.2+η*v.1) :
      (fun w => fderiv ℝ (J r) w (0,1)) =ᶠ[𝓝 v] J (r+1) := by
    have hcv : ContinuousAt (fun w : ℝ × ℝ => w.2+η*w.1) v := by fun_prop
    have hn₀ : ∀ᶠ w : ℝ × ℝ in 𝓝 v, 0 < w.2 := continuousAt_snd (Ioi_mem_nhds hv)
    have hn₁ : ∀ᶠ w : ℝ × ℝ in 𝓝 v, 0 < w.2+η*w.1 := hcv (Ioi_mem_nhds hv')
    filter_upwards [hn₀,hn₁] with w hw hw'
    exact (positive_difference_curvature_directions F (σ:=σ) hw hw' hf r).2.1
  have hGe : G =ᶠ[𝓝 p] J 3 := hGerm 2 p hx0 hz0
  have hKe : K =ᶠ[𝓝 p] J 4 := by
    filter_upwards [hGe.fderiv (𝕜:=ℝ),hGerm 3 p hx0 hz0] with w hw hj
    change fderiv ℝ G w (0,1)=J 4 w
    rw [hw]
    exact hj
  have hJbound (r : ℕ) (hr : r ≤ 5) : |J r p| ≤ 3*U/σ := by
    have hc₀ : ContDiffAt ℝ r F (ρ z) :=
      (hf _ hx0).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl r)
    have hc₁ : ContDiffAt ℝ r (fun x => F (x+η*z.1)) (ρ z) :=
      ((hf _ hz0).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl r)).comp
        (ρ z) (contDiffAt_id.add contDiffAt_const)
    have he : iteratedDeriv r (fun x => (F x-F (x+η*z.1))/(σ*η)) (ρ z)=J r p := by
      rw [iteratedDeriv_div_const,iteratedDeriv_fun_sub hc₀ hc₁,iteratedDeriv_comp_add_const]
    rw [←he]
    simpa only [iteratedDeriv_zero] using
      positive_jets_difference_mixed_upper F hσ hU hη hηmax hx hy hf hbound r 0
        (by norm_num) (by omega)
  have hYbound (r : ℕ) (hr : r ≤ 5) : |fderiv ℝ (J r) p (1,0)| ≤ 3*U/σ := by
    rw [(positive_difference_curvature_directions F (σ:=σ) hx0 hz0 hf r).2.2]
    have he : -η*iteratedDeriv (r+1) F (ρ z+η*z.1)/(σ*η)=
        -iteratedDeriv (r+1) F (ρ z+η*z.1)/σ := by field_simp
    rw [he,abs_div,abs_neg,abs_of_pos hσ]
    apply (div_le_div_iff_of_pos_right hσ).mpr
    exact (hbound _ hzI r (by omega)).trans (by linarith)
  have hGlow : c/(2*σ) ≤ |G p| :=
    (positive_jets_difference_curvature_entry F hσ hc hU hη hηmax
      hx hy hf hbound htests 3 (by norm_num) (by norm_num)).2.2.2.1
  have hG0 : G p ≠ 0 := abs_pos.mp (lt_of_lt_of_le (by positivity) hGlow)
  have hH : ContDiffAt ℝ 3 H p :=
    (positive_difference_curvature_directions F (σ:=σ) hx0 hz0 hf 2).1.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hAR : 3*U/σ ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hIR : 2*σ/c ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  apply curvature_surface_profile_columns_bound H ρ (le_max_left _ _) hI hbase hH hG0 hroot huniq
  · exact (hYbound 2 (by norm_num)).trans hAR
  · change |G p| ≤ R
    rw [hGe.self_of_nhds]
    exact (hJbound 3 (by norm_num)).trans hAR
  · change |K p| ≤ R
    rw [hKe.self_of_nhds]
    exact (hJbound 4 (by norm_num)).trans hAR
  · change |fderiv ℝ G p (1,0)| ≤ R
    rw [hGe.fderiv_eq]
    exact (hYbound 3 (by norm_num)).trans hAR
  · change |fderiv ℝ K p (0,1)| ≤ R
    have he : fderiv ℝ (J 4) p (0,1)=J 5 p := (hGerm 4 p hx0 hz0).self_of_nhds
    rw [hKe.fderiv_eq,he]
    exact (hJbound 5 (by norm_num)).trans hAR
  · change |fderiv ℝ K p (1,0)| ≤ R
    rw [hKe.fderiv_eq]
    exact (hYbound 4 (by norm_num)).trans hAR
  · change |(G p)⁻¹| ≤ R
    calc
      _ = 1/|G p| := by rw [abs_inv,one_div]
      _ ≤ 1/(c/(2*σ)) := one_div_le_one_div_of_le (by positivity) hGlow
      _ = 2*σ/c := by field_simp
      _ ≤ _ := hIR


                                                                         
                                                                          
                            
def profileDerivativeColumns (w : Fin 7 → ℝ) : (ℝ × ℝ) × (ℝ × ℝ) :=
  ((w 3-w 2*w 0*w 6,
    (w 5*w 1-w 2*w 3)*(w 6)^2-w 0*(w 4*w 1-(w 2)^2)*(w 6)^3),
   (w 2*w 6,(w 4*w 1-(w 2)^2)*(w 6)^3))

theorem contDiff_profileDerivativeColumns : ContDiff ℝ ∞ profileDerivativeColumns := by
  unfold profileDerivativeColumns
  fun_prop

theorem profileDerivativeColumns_uniform_derivative_bound (R : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ w : Fin 7 → ℝ, (∀ i, |w i| ≤ R) →
      ‖fderiv ℝ profileDerivativeColumns w‖ ≤ D := by
  have hd : ContinuousOn (fderiv ℝ profileDerivativeColumns)
      (Icc (fun _ : Fin 7 => -R) (fun _ => R)) :=
    (contDiff_profileDerivativeColumns.continuous_fderiv (by simp)).continuousOn
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hd
  refine ⟨max 1 D,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro w hw
  exact (hD w ⟨fun i => (abs_le.mp (hw i)).1,fun i => (abs_le.mp (hw i)).2⟩).trans
    (le_max_right _ _)


                                                                       
                                                                              
theorem curvature_surface_profile_columns_polynomial
    (H : ℝ × ℝ → ℝ) (ρ : ℝ × ℝ → ℝ)
    {z : ℝ × ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hbase : ρ z ∈ I)
    (hH : ContDiffAt ℝ 3 H (z.1,ρ z))
    (hx0 : fderiv ℝ H (z.1,ρ z) (0,1) ≠ 0)
    (hroot : ∀ᶠ w in 𝓝 z, ρ w ∈ I ∧ H (w.1,ρ w)=w.2)
    (huniq : ∀ᶠ w in 𝓝 z, Set.InjOn (fun x => H (w.1,x)) I) :
    let p := (z.1,ρ z)
    let G := fun v => fderiv ℝ H v (0,1)
    let K := fun v => fderiv ℝ G v (0,1)
    let Z := fun v => fderiv ℝ G v (1,0)
    let g := fun w => G (w.1,ρ w)
    let Φ := fun w => (g w,fderiv ℝ g w (0,1))
    (fderiv ℝ Φ z (1,0),fderiv ℝ Φ z (0,1)) =
      profileDerivativeColumns ![fderiv ℝ H p (1,0),G p,K p,Z p,
        fderiv ℝ K p (0,1),fderiv ℝ K p (1,0),(G p)⁻¹] := by
  intro p G K Z g Φ
  obtain ⟨hy,hu⟩ := curvature_surface_profile_derivative_matrix H ρ hI hbase hH hx0 hroot huniq
  rw [hy,hu]
  dsimp only [profileDerivativeColumns,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.head_cons,Matrix.tail_cons]
  simp only [div_eq_mul_inv,←inv_pow]
  congr 1


private theorem planar_linearMap_norm_le_columns
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : (ℝ × ℝ) →L[ℝ] E) :
    ‖L‖ ≤ ‖L (1,0)‖+‖L (0,1)‖ := by
  apply L.opNorm_le_bound (by positivity)
  intro v
  have hv : v=v.1 • (1,0)+v.2 • (0,1) := by ext <;> simp
  calc
    ‖L v‖ = ‖v.1 • L (1,0)+v.2 • L (0,1)‖ := by
      conv_lhs => rw [hv,map_add,map_smul,map_smul]
    _ ≤ ‖v.1 • L (1,0)‖+‖v.2 • L (0,1)‖ := norm_add_le _ _
    _ = |v.1| * ‖L (1,0)‖+|v.2| * ‖L (0,1)‖ := by rw [norm_smul,norm_smul]; rfl
    _ ≤ ‖v‖ * ‖L (1,0)‖+‖v‖ * ‖L (0,1)‖ :=
      add_le_add (mul_le_mul_of_nonneg_right (norm_fst_le v) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (norm_snd_le v) (norm_nonneg _))
    _ = (‖L (1,0)‖+‖L (0,1)‖)*‖v‖ := by ring


                                                                     
                                                                     
                                                                    
theorem profile_columns_uniform_variation (R : ℝ) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (Φ : ℝ × ℝ → ℝ × ℝ) (J : ℝ × ℝ → Fin 7 → ℝ)
        (S : Set (ℝ × ℝ)) (p q : ℝ × ℝ) (B : ℝ),
      Convex ℝ S → p ∈ S → q ∈ S →
      (∀ w ∈ S, ∀ i, |J w i| ≤ R) →
      (∀ w ∈ S, DifferentiableAt ℝ J w) →
      (∀ w ∈ S, ‖fderiv ℝ J w‖ ≤ B) →
      (∀ w ∈ S, (fderiv ℝ Φ w (1,0),fderiv ℝ Φ w (0,1))=
        profileDerivativeColumns (J w)) →
      ‖fderiv ℝ Φ q-fderiv ℝ Φ p‖ ≤ 2*D*B*‖q-p‖ := by
  obtain ⟨D,hD,hbound⟩ := profileDerivativeColumns_uniform_derivative_bound R
  refine ⟨D,hD,?_⟩
  intro Φ J S p q B hS hp hq hjet hJ hJB hfactor
  have hd w (hw : w ∈ S) :
      HasFDerivAt (fun v => profileDerivativeColumns (J v))
        ((fderiv ℝ profileDerivativeColumns (J w)).comp (fderiv ℝ J w)) w :=
    (contDiff_profileDerivativeColumns.differentiable (by simp)).differentiableAt.hasFDerivAt.comp
      w (hJ w hw).hasFDerivAt
  have hcol : ‖profileDerivativeColumns (J q)-profileDerivativeColumns (J p)‖ ≤
      D*B*‖q-p‖ := by
    apply hS.norm_image_sub_le_of_norm_fderiv_le (fun w hw => (hd w hw).differentiableAt)
      (fun w hw => ?_) hp hq
    rw [(hd w hw).fderiv]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hbound (J w) (hjet w hw)) (hJB w hw) (norm_nonneg _) hD.le)
  let L := fderiv ℝ Φ q-fderiv ℝ Φ p
  have he : (L (1,0),L (0,1))=
      profileDerivativeColumns (J q)-profileDerivativeColumns (J p) := by
    calc
      _ = (fderiv ℝ Φ q (1,0),fderiv ℝ Φ q (0,1))-
          (fderiv ℝ Φ p (1,0),fderiv ℝ Φ p (0,1)) := rfl
      _ = _ := by rw [hfactor q hq,hfactor p hp]
  have hb₁ : ‖L (1,0)‖ ≤ D*B*‖q-p‖ := by
    have hh := norm_fst_le (L (1,0),L (0,1))
    change ‖L (1,0)‖ ≤ ‖(L (1,0),L (0,1))‖ at hh
    rw [he] at hh
    exact hh.trans hcol
  have hb₂ : ‖L (0,1)‖ ≤ D*B*‖q-p‖ := by
    have hh := norm_snd_le (L (1,0),L (0,1))
    change ‖L (0,1)‖ ≤ ‖(L (1,0),L (0,1))‖ at hh
    rw [he] at hh
    exact hh.trans hcol
  exact (planar_linearMap_norm_le_columns L).trans (by linarith only [hb₁,hb₂])


                                                                    
                                                                          
noncomputable def differenceProfileJet (F : ℝ → ℝ) (σ η : ℝ) (p : ℝ × ℝ) : Fin 7 → ℝ :=
  let J := fun r => (iteratedDeriv r F p.2-iteratedDeriv r F (p.2+η*p.1))/(σ*η)
  let Y := fun r => -iteratedDeriv (r+1) F (p.2+η*p.1)/σ
  ![Y 2,J 3,J 4,Y 3,J 5,Y 4,(J 3)⁻¹]

                                                                    
                                                                         
theorem positive_difference_profile_jet_bound
    (F : ℝ → ℝ) {σ c U η x y : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hx : x ∈ Icc (3/4:ℝ) (9/4)) (hy : y ∈ Icc (1/2:ℝ) 3)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) :
    let R := max 1 (max (3*U/σ) (2*σ/c))
    DifferentiableAt ℝ (differenceProfileJet F σ η) (y,x) ∧
    (∀ i, |differenceProfileJet F σ η (y,x) i| ≤ R) ∧
    ‖fderiv ℝ (differenceProfileJet F σ η) (y,x)‖ ≤ 2*R^3 := by
  intro R
  let p : ℝ × ℝ := (y,x)
  let J := fun (r : ℕ) (v : ℝ × ℝ) =>
    (iteratedDeriv r F v.2-iteratedDeriv r F (v.2+η*v.1))/(σ*η)
  let Y := fun (r : ℕ) (v : ℝ × ℝ) =>
    -iteratedDeriv (r+1) F (v.2+η*v.1)/σ
  have hx0 : 0 < x := by linarith only [hx.1]
  have hy0 : 0 < y := by linarith only [hy.1]
  have hz0 : 0 < x+η*y := add_pos hx0 (mul_pos hη hy0)
  have hzI : x+η*y ∈ Icc (1/2:ℝ) 3 := by
    have hb := mul_le_mul hηmax hy.2 hy0.le (by norm_num : (0:ℝ) ≤ 1/8)
    constructor <;> nlinarith only [hx.1,hx.2,hb,mul_pos hη hy0]
  have hR : 1 ≤ R := le_max_left _ _
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hAR : 3*U/σ ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hIR : 2*σ/c ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  have hUR : U/σ ≤ R :=
    (div_le_div_of_nonneg_right (by linarith : U ≤ 3*U) hσ.le).trans hAR
  have hJbound (r : ℕ) (hr : r ≤ 6) : |J r p| ≤ R := by
    have hc₀ : ContDiffAt ℝ r F x :=
      (hf _ hx0).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl r)
    have hc₁ : ContDiffAt ℝ r (fun u => F (u+η*y)) x :=
      ((hf _ hz0).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl r)).comp
        x (contDiffAt_id.add contDiffAt_const)
    have he : iteratedDeriv r (fun u => (F u-F (u+η*y))/(σ*η)) x=J r p := by
      rw [iteratedDeriv_div_const,iteratedDeriv_fun_sub hc₀ hc₁,iteratedDeriv_comp_add_const]
    rw [←he]
    have hb : |iteratedDeriv r (fun u => (F u-F (u+η*y))/(σ*η)) x| ≤ 3*U/σ := by
      simpa only [iteratedDeriv_zero] using
        (positive_jets_difference_mixed_upper F hσ hU hη hηmax hx hy hf hbound r 0
          (by norm_num) (by omega))
    exact hb.trans hAR
  have hYbound (r : ℕ) (hr : r ≤ 6) : |Y r p| ≤ R := by
    change |-iteratedDeriv (r+1) F (x+η*y)/σ| ≤ R
    rw [abs_div,abs_neg,abs_of_pos hσ]
    exact (div_le_div_of_nonneg_right (hbound _ hzI r hr) hσ.le).trans hUR
  have hJdiff (r : ℕ) : DifferentiableAt ℝ (J r) p :=
    ((positive_difference_curvature_directions F (σ:=σ) hx0 hz0 hf r).1.differentiableAt
      (by simp))
  have hJder (r : ℕ) (hr : r ≤ 5) : ‖fderiv ℝ (J r) p‖ ≤ 2*R := by
    have he : fderiv ℝ (J r) p (1,0)=Y r p := by
      rw [(positive_difference_curvature_directions F (σ:=σ) hx0 hz0 hf r).2.2]
      dsimp only [Y,p]
      field_simp
    apply (planar_linearMap_norm_le_columns _).trans
    rw [he,(positive_difference_curvature_directions F (σ:=σ) hx0 hz0 hf r).2.1]
    change |Y r p|+|J (r+1) p| ≤ 2*R
    linarith only [hYbound r (by omega),hJbound (r+1) (by omega)]
  have hYder (r : ℕ) (hr : r ≤ 4) :
      DifferentiableAt ℝ (Y r) p ∧ ‖fderiv ℝ (Y r) p‖ ≤ 2*R := by
    have hd : HasDerivAt (iteratedDeriv (r+1) F)
        (iteratedDeriv (r+2) F (x+η*y)) (x+η*y) :=
      hasDerivAt_iteratedDeriv_finite (show r+1 < r+2 by omega)
      ((hf _ hz0).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl (r+2)))
    have hs : HasFDerivAt (fun v : ℝ × ℝ => v.2+η*v.1)
        (ContinuousLinearMap.snd ℝ ℝ ℝ+η • ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
      hasFDerivAt_snd.add (hasFDerivAt_fst.const_mul η)
    have hd₀ : HasFDerivAt (fun v : ℝ × ℝ => iteratedDeriv (r+1) F (v.2+η*v.1))
        (iteratedDeriv (r+2) F (x+η*y) •
          (ContinuousLinearMap.snd ℝ ℝ ℝ+η • ContinuousLinearMap.fst ℝ ℝ ℝ)) p :=
      hd.comp_hasFDerivAt (f:=fun v : ℝ × ℝ => v.2+η*v.1) p hs
    have hdY : HasFDerivAt (Y r)
        (σ⁻¹ • (-(iteratedDeriv (r+2) F (x+η*y) •
          (ContinuousLinearMap.snd ℝ ℝ ℝ+η • ContinuousLinearMap.fst ℝ ℝ ℝ)))) p :=
      by convert hd₀.neg.mul_const σ⁻¹ using 1; rfl
    refine ⟨hdY.differentiableAt,?_⟩
    rw [hdY.fderiv]
    apply (planar_linearMap_norm_le_columns _).trans
    change |σ⁻¹ * (-(iteratedDeriv (r+2) F (x+η*y)*(0+η*1)))|+
      |σ⁻¹ * (-(iteratedDeriv (r+2) F (x+η*y)*(1+η*0)))| ≤ 2*R
    have he : |σ⁻¹ * (-(iteratedDeriv (r+2) F (x+η*y)*(0+η*1)))|+
        |σ⁻¹ * (-(iteratedDeriv (r+2) F (x+η*y)*(1+η*0)))|=
        (η+1)*(|iteratedDeriv (r+2) F (x+η*y)|/σ) := by
      simp only [mul_one,zero_add,mul_zero,add_zero,abs_mul,abs_neg,
        abs_of_pos hη,abs_of_pos (inv_pos.mpr hσ),div_eq_mul_inv]
      ring
    rw [he]
    have hj : |iteratedDeriv (r+2) F (x+η*y)|/σ ≤ R :=
      (div_le_div_of_nonneg_right (hbound _ hzI (r+1) (by omega)) hσ.le).trans hUR
    have hn : 0 ≤ |iteratedDeriv (r+2) F (x+η*y)|/σ := by positivity
    calc
      _ ≤ 2*(|iteratedDeriv (r+2) F (x+η*y)|/σ) :=
        mul_le_mul_of_nonneg_right (by linarith only [hηmax]) hn
      _ ≤ _ := mul_le_mul_of_nonneg_left hj (by norm_num)
  have hGlow : c/(2*σ) ≤ |J 3 p| := by
    have hh := (positive_jets_difference_curvature_entry F hσ hc hU hη hηmax
      hx hy hf hbound htests 3 (by norm_num) (by norm_num)).2.2.2.1
    change c/(2*σ) ≤ |fderiv ℝ (J 2) p (0,1)| at hh
    have he : fderiv ℝ (J 2) p (0,1)=J 3 p :=
      (positive_difference_curvature_directions F (σ:=σ) hx0 hz0 hf 2).2.1
    rw [he] at hh
    exact hh
  have hG0 : J 3 p ≠ 0 := abs_pos.mp (lt_of_lt_of_le (by positivity) hGlow)
  have hInv : |(J 3 p)⁻¹| ≤ R := by
    calc
      _ = 1/|J 3 p| := by rw [abs_inv,one_div]
      _ ≤ 1/(c/(2*σ)) := one_div_le_one_div_of_le (by positivity) hGlow
      _ = 2*σ/c := by field_simp
      _ ≤ _ := hIR
  have hInvDer : DifferentiableAt ℝ (fun v => (J 3 v)⁻¹) p ∧
      ‖fderiv ℝ (fun v => (J 3 v)⁻¹) p‖ ≤ 2*R^3 := by
    have hd : HasFDerivAt (fun v => (J 3 v)⁻¹)
        (-(J 3 p ^ 2)⁻¹ • fderiv ℝ (J 3) p) p :=
      (hasDerivAt_inv hG0).comp_hasFDerivAt p (hJdiff 3).hasFDerivAt
    refine ⟨hd.differentiableAt,?_⟩
    rw [hd.fderiv,norm_smul,Real.norm_eq_abs,abs_neg,←inv_pow,abs_pow]
    calc
      _ ≤ R^2*(2*R) := mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hInv 2)
        (hJder 3 (by norm_num)) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hbaseDer : 2*R ≤ 2*R^3 := by nlinarith [sq_nonneg (R-1)]
  have hdiff : ∀ i, DifferentiableAt ℝ (fun v => differenceProfileJet F σ η v i) p := by
    intro i
    fin_cases i
    · exact (hYder 2 (by norm_num)).1
    · exact hJdiff 3
    · exact hJdiff 4
    · exact (hYder 3 (by norm_num)).1
    · exact hJdiff 5
    · exact (hYder 4 (by norm_num)).1
    · exact hInvDer.1
  refine ⟨differentiableAt_pi.mpr hdiff,?_,?_⟩
  · intro i
    fin_cases i
    · exact hYbound 2 (by norm_num)
    · exact hJbound 3 (by norm_num)
    · exact hJbound 4 (by norm_num)
    · exact hYbound 3 (by norm_num)
    · exact hJbound 5 (by norm_num)
    · exact hYbound 4 (by norm_num)
    · exact hInv
  · have hder : ∀ i, ‖fderiv ℝ (fun v => differenceProfileJet F σ η v i) p‖ ≤ 2*R^3 := by
      intro i
      fin_cases i
      · exact (hYder 2 (by norm_num)).2.trans hbaseDer
      · exact (hJder 3 (by norm_num)).trans hbaseDer
      · exact (hJder 4 (by norm_num)).trans hbaseDer
      · exact (hYder 3 (by norm_num)).2.trans hbaseDer
      · exact (hJder 5 (by norm_num)).trans hbaseDer
      · exact (hYder 4 (by norm_num)).2.trans hbaseDer
      · exact hInvDer.2
    rw [fderiv_pi hdiff]
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    exact (ContinuousLinearMap.le_opNorm _ v).trans
      (mul_le_mul_of_nonneg_right (hder i) (norm_nonneg _))


                                                                     
                                                                         
theorem positive_difference_profile_chart_bound
    (F : ℝ → ℝ) (ρ : ℝ × ℝ → ℝ)
    {σ c U η : ℝ} {z : ℝ × ℝ} {I : Set ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hx : ρ z ∈ Icc (3/4:ℝ) (9/4)) (hy : z.1 ∈ Icc (1/2:ℝ) 3)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hI : IsOpen I) (hbase : ρ z ∈ I)
    (hroot : ∀ᶠ w in 𝓝 z, ρ w ∈ I ∧
      (iteratedDeriv 2 F (ρ w)-iteratedDeriv 2 F (ρ w+η*w.1))/(σ*η)=w.2)
    (huniq : ∀ᶠ w in 𝓝 z, Set.InjOn
      (fun x => (iteratedDeriv 2 F x-iteratedDeriv 2 F (x+η*w.1))/(σ*η)) I) :
    let H := fun v : ℝ × ℝ =>
      (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
    let g := fun w => fderiv ℝ H (w.1,ρ w) (0,1)
    let Φ := fun w => (g w,fderiv ℝ g w (0,1))
    let W := fun w => differenceProfileJet F σ η (w.1,ρ w)
    let R := max 1 (max (3*U/σ) (2*σ/c))
    DifferentiableAt ℝ W z ∧ (∀ i, |W z i| ≤ R) ∧
    ‖fderiv ℝ W z‖ ≤ 6*R^5 ∧
    (fderiv ℝ Φ z (1,0),fderiv ℝ Φ z (0,1))=profileDerivativeColumns (W z) := by
  intro H g Φ W R
  let p : ℝ × ℝ := (z.1,ρ z)
  let J := fun (r : ℕ) (v : ℝ × ℝ) =>
    (iteratedDeriv r F v.2-iteratedDeriv r F (v.2+η*v.1))/(σ*η)
  let Y := fun (r : ℕ) (v : ℝ × ℝ) =>
    -iteratedDeriv (r+1) F (v.2+η*v.1)/σ
  let G := fun v => fderiv ℝ H v (0,1)
  let K := fun v => fderiv ℝ G v (0,1)
  have hx0 : 0 < ρ z := by linarith only [hx.1]
  have hy0 : 0 < z.1 := by linarith only [hy.1]
  have hz0 : 0 < ρ z+η*z.1 := add_pos hx0 (mul_pos hη hy0)
  have hGerm (r : ℕ) (v : ℝ × ℝ) (hv : 0 < v.2) (hv' : 0 < v.2+η*v.1) :
      (fun w => fderiv ℝ (J r) w (0,1)) =ᶠ[𝓝 v] J (r+1) := by
    have hcv : ContinuousAt (fun w : ℝ × ℝ => w.2+η*w.1) v := by fun_prop
    have hn₀ : ∀ᶠ w : ℝ × ℝ in 𝓝 v, 0 < w.2 := continuousAt_snd (Ioi_mem_nhds hv)
    have hn₁ : ∀ᶠ w : ℝ × ℝ in 𝓝 v, 0 < w.2+η*w.1 := hcv (Ioi_mem_nhds hv')
    filter_upwards [hn₀,hn₁] with w hw hw'
    exact (positive_difference_curvature_directions F (σ:=σ) hw hw' hf r).2.1
  have hGe : G =ᶠ[𝓝 p] J 3 := hGerm 2 p hx0 hz0
  have hKe : K =ᶠ[𝓝 p] J 4 := by
    filter_upwards [hGe.fderiv (𝕜:=ℝ),hGerm 3 p hx0 hz0] with w hw hj
    change fderiv ℝ G w (0,1)=J 4 w
    rw [hw]
    exact hj
  have hYe r : fderiv ℝ (J r) p (1,0)=Y r p := by
    rw [(positive_difference_curvature_directions F (σ:=σ) hx0 hz0 hf r).2.2]
    dsimp only [Y,p]
    field_simp
  have hH : ContDiffAt ℝ 3 H p :=
    (positive_difference_curvature_directions F (σ:=σ) hx0 hz0 hf 2).1.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hGlow : c/(2*σ) ≤ |G p| :=
    (positive_jets_difference_curvature_entry F hσ hc hU hη hηmax
      hx hy hf hbound htests 3 (by norm_num) (by norm_num)).2.2.2.1
  have hG0 : G p ≠ 0 := abs_pos.mp (lt_of_lt_of_le (by positivity) hGlow)
  obtain ⟨hW,hsize,hWder⟩ := positive_difference_profile_jet_bound F hσ hc hU hη hηmax
    hx hy hf hbound htests
  have hB : |fderiv ℝ H p (1,0)| ≤ R := by
    change |fderiv ℝ (J 2) p (1,0)| ≤ R
    rw [hYe]
    exact hsize 0
  have hInv : |(G p)⁻¹| ≤ R := by
    rw [hGe.self_of_nhds]
    exact hsize 6
  have hρ := curvature_surface_root_hasFDerivAt H ρ hI hbase
    (hH.of_le (by norm_num)) hG0 hroot huniq
  have hR : 1 ≤ R := le_max_left _ _
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hρnorm : ‖fderiv ℝ ρ z‖ ≤ 2*R^2 := by
    rw [hρ.fderiv]
    apply (planar_linearMap_norm_le_columns _).trans
    change |(-fderiv ℝ H p (1,0)/G p)*1+(1/G p)*0|+
      |(-fderiv ℝ H p (1,0)/G p)*0+(1/G p)*1| ≤ 2*R^2
    simp only [mul_one,mul_zero,add_zero,zero_add,div_eq_mul_inv,one_mul,
      abs_mul,abs_neg]
    have hm := mul_le_mul hB hInv (abs_nonneg _) hRp.le
    nlinarith only [hm,hInv,hR]
  have hchart := (hasFDerivAt_fst (𝕜:=ℝ) (p:=z)).prodMk hρ
  have hchartnorm : ‖fderiv ℝ (fun w => (w.1,ρ w)) z‖ ≤ 3*R^2 := by
    rw [hchart.fderiv,ContinuousLinearMap.opNorm_prod,Prod.norm_def]
    apply max_le
    · exact (ContinuousLinearMap.norm_fst_le ..).trans (by nlinarith only [hR])
    · rw [←hρ.fderiv]
      exact hρnorm.trans (by nlinarith only [sq_nonneg R])
  have hcomp := hW.hasFDerivAt.comp z hchart.differentiableAt.hasFDerivAt
  change HasFDerivAt W
      ((fderiv ℝ (differenceProfileJet F σ η) p).comp
        (fderiv ℝ (fun w => (w.1,ρ w)) z)) z at hcomp
  refine ⟨hcomp.differentiableAt,hsize,?_,?_⟩
  · rw [hcomp.fderiv]
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    have hh := mul_le_mul hWder hchartnorm (norm_nonneg _) (show 0 ≤ 2*R^3 by positivity)
    convert hh using 1
    ring
  · have hh := curvature_surface_profile_columns_polynomial H ρ hI hbase hH hG0 hroot huniq
    change (fderiv ℝ Φ z (1,0),fderiv ℝ Φ z (0,1))=
      profileDerivativeColumns ![fderiv ℝ H p (1,0),G p,K p,
        fderiv ℝ G p (1,0),fderiv ℝ K p (0,1),fderiv ℝ K p (1,0),(G p)⁻¹] at hh
    rw [hh]
    apply congrArg profileDerivativeColumns
    change ![fderiv ℝ (J 2) p (1,0),G p,K p,
        fderiv ℝ G p (1,0),fderiv ℝ K p (0,1),fderiv ℝ K p (1,0),(G p)⁻¹]=
      ![Y 2 p,J 3 p,J 4 p,Y 3 p,J 5 p,Y 4 p,(J 3 p)⁻¹]
    have hJ4 : fderiv ℝ (J 4) p (0,1)=J 5 p := (hGerm 4 p hx0 hz0).self_of_nhds
    rw [hYe,hGe.self_of_nhds,hKe.self_of_nhds,hGe.fderiv_eq,hKe.fderiv_eq,
      hYe,hYe,hJ4]


                                                                            
                                                                                
theorem positive_difference_profile_uniform_variation
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ L : ℝ, 0 < L ∧
      ∀ (F : ℝ → ℝ) (ρ : ℝ × ℝ → ℝ) (η : ℝ) (I : Set ℝ) (S : Set (ℝ × ℝ)),
      0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      IsOpen I → IsOpen S → Convex ℝ S →
      (∀ w ∈ S, ρ w ∈ Icc (3/4:ℝ) (9/4) ∧ w.1 ∈ Icc (1/2:ℝ) 3) →
      (∀ w ∈ S, ρ w ∈ I ∧
        (iteratedDeriv 2 F (ρ w)-iteratedDeriv 2 F (ρ w+η*w.1))/(σ*η)=w.2) →
      (∀ w ∈ S, Set.InjOn
        (fun x => (iteratedDeriv 2 F x-iteratedDeriv 2 F (x+η*w.1))/(σ*η)) I) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let g := fun w => fderiv ℝ H (w.1,ρ w) (0,1)
      let Φ := fun w => (g w,fderiv ℝ g w (0,1))
      ∀ p ∈ S, ∀ q ∈ S, ‖fderiv ℝ Φ q-fderiv ℝ Φ p‖ ≤ L*‖q-p‖ := by
  let R := max 1 (max (3*U/σ) (2*σ/c))
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨D,hD,hvar⟩ := profile_columns_uniform_variation R
  refine ⟨12*D*R^5,by positivity,?_⟩
  intro F ρ η I S hη hηmax hf hbound htests hI hS hconv hrange hroot huniq H g Φ
  let W := fun w => differenceProfileJet F σ η (w.1,ρ w)
  have hlocal w (hw : w ∈ S) :
      DifferentiableAt ℝ W w ∧ (∀ i, |W w i| ≤ R) ∧
      ‖fderiv ℝ W w‖ ≤ 6*R^5 ∧
      (fderiv ℝ Φ w (1,0),fderiv ℝ Φ w (0,1))=profileDerivativeColumns (W w) := by
    apply positive_difference_profile_chart_bound F ρ hσ hc hU hη hηmax
      (hrange w hw).1 (hrange w hw).2 hf hbound htests hI (hroot w hw).1
    · filter_upwards [hS.mem_nhds hw] with v hv
      exact hroot v hv
    · filter_upwards [hS.mem_nhds hw] with v hv
      exact huniq v hv
  intro p hp q hq
  have hh := hvar Φ W S p q (6*R^5) hconv hp hq
    (fun w hw => (hlocal w hw).2.1) (fun w hw => (hlocal w hw).1)
    (fun w hw => (hlocal w hw).2.2.1) (fun w hw => (hlocal w hw).2.2.2)
  convert hh using 1
  ring


                                                                     
                                                                           
                                                                
                                                                          
private theorem interval_root_coverage_of_abs_derivative
    (f f' : ℝ → ℝ) {a b x L : ℝ}
    (hL : 0 < L) (hx : x ∈ Ioo a b)
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hlower : ∀ t ∈ Icc a b, L ≤ |f' t|) :
    Set.InjOn f (Icc a b) ∧ ∀ u : ℝ,
      |u-f x| < L*min (x-a) (b-x) → ∃ v ∈ Ioo a b, f v=u := by
  have hab : a < b := hx.1.trans hx.2
  have hl s t (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
      L*(t-s) ≤ |f t-f s| := by
    rcases hst.eq_or_lt with he | hlt
    · subst t
      simp
    have hsub : Icc s t ⊆ Icc a b := fun v hv =>
      ⟨hs.1.trans hv.1,hv.2.trans ht.2⟩
    obtain ⟨v,hv,he⟩ := exists_hasDerivAt_eq_slope f f' hlt
      (fun w hw => (hd w (hsub hw)).continuousAt.continuousWithinAt)
      (fun w hw => hd w (hsub ⟨hw.1.le,hw.2.le⟩))
    have hb := hlower v (hsub ⟨hv.1.le,hv.2.le⟩)
    rw [he,abs_div,abs_of_pos (sub_pos.mpr hlt)] at hb
    exact (le_div_iff₀ (sub_pos.mpr hlt)).mp hb
  have hi : Set.InjOn f (Icc a b) := by
    intro s hs t ht he
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hb := hl s t hs ht hlt.le
      rw [he,sub_self,abs_zero] at hb
      exact (not_lt_of_ge hb) (mul_pos hL (sub_pos.mpr hlt))
    · have hb := hl t s ht hs hgt.le
      rw [he,sub_self,abs_zero] at hb
      exact (not_lt_of_ge hb) (mul_pos hL (sub_pos.mpr hgt))
  refine ⟨hi,?_⟩
  intro u hu
  have ha : a ∈ Icc a b := ⟨le_rfl,hab.le⟩
  have hb : b ∈ Icc a b := ⟨hab.le,le_rfl⟩
  have hx' : x ∈ Icc a b := ⟨hx.1.le,hx.2.le⟩
  have hla : L*min (x-a) (b-x) ≤ |f x-f a| :=
    (mul_le_mul_of_nonneg_left (min_le_left _ _) hL.le).trans (hl a x ha hx' hx.1.le)
  have hlb : L*min (x-a) (b-x) ≤ |f b-f x| :=
    (mul_le_mul_of_nonneg_left (min_le_right _ _) hL.le).trans (hl x b hx' hb hx.2.le)
  have hcont : ContinuousOn f (Icc a b) :=
    fun w hw => (hd w hw).continuousAt.continuousWithinAt
  rcases hcont.strictMonoOn_of_injOn_Icc' hab.le hi with hm | hm
  · rw [abs_of_pos (sub_pos.mpr (hm ha hx' hx.1))] at hla
    rw [abs_of_pos (sub_pos.mpr (hm hx' hb hx.2))] at hlb
    exact intermediate_value_Ioo hab.le hcont
      ⟨by linarith only [hla,(abs_lt.mp hu).1],
       by linarith only [hlb,(abs_lt.mp hu).2]⟩
  · rw [abs_of_neg (sub_neg.mpr (hm ha hx' hx.1))] at hla
    rw [abs_of_neg (sub_neg.mpr (hm hx' hb hx.2))] at hlb
    exact intermediate_value_Ioo' hab.le hcont
      ⟨by linarith only [hlb,(abs_lt.mp hu).1],
       by linarith only [hla,(abs_lt.mp hu).2]⟩


                                                                           
                                                                          
                                                                           
theorem positive_difference_uniform_root_chart
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ r : ℝ, 0 < r ∧
      ∀ (F : ℝ → ℝ) (η x₀ y₀ : ℝ),
      0 < η → η ≤ 1/8 → x₀ ∈ Icc (1:ℝ) 2 → y₀ ∈ Icc (1:ℝ) 2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let ρ := fun w : ℝ × ℝ =>
        Function.invFunOn (fun x => H (w.1,x)) (Ioo (3/4:ℝ) (9/4)) w.2
      ∀ w : ℝ × ℝ, ‖w-(y₀,H (y₀,x₀))‖ < r →
        ρ w ∈ Ioo (3/4:ℝ) (9/4) ∧ w.1 ∈ Icc (1/2:ℝ) 3 ∧
        H (w.1,ρ w)=w.2 ∧ Set.InjOn (fun x => H (w.1,x)) (Ioo (3/4:ℝ) (9/4)) := by
  let V := U/σ
  let r := min (1/4:ℝ) (c/(16*σ*(1+V)))
  have hV : 0 < V := div_pos hU hσ
  have hr : 0 < r := by dsimp only [r]; positivity
  refine ⟨r,hr,?_⟩
  intro F η x₀ y₀ hη hηmax hx₀ hy₀ hf hbound htests H ρ w hw
  have hr₁ : r ≤ 1/4 := min_le_left _ _
  have hr₂ : r ≤ c/(16*σ*(1+V)) := min_le_right _ _
  have hwy : |w.1-y₀| < r := (norm_fst_le (w-(y₀,H (y₀,x₀)))).trans_lt hw
  have hwu : |w.2-H (y₀,x₀)| < r := (norm_snd_le (w-(y₀,H (y₀,x₀)))).trans_lt hw
  have hy : w.1 ∈ Icc (1/2:ℝ) 3 := by
    obtain ⟨hl,hu⟩ := abs_lt.mp hwy
    constructor <;> linarith only [hl,hu,hr₁,hy₀.1,hy₀.2]
  have hx : x₀ ∈ Ioo (3/4:ℝ) (9/4) := by
    constructor <;> linarith only [hx₀.1,hx₀.2]
  have hgeom (x y : ℝ) (hx : x ∈ Icc (3/4:ℝ) (9/4))
      (hy : y ∈ Icc (1/2:ℝ) 3) :
      0 < x ∧ 0 < x+η*y ∧ x+η*y ∈ Icc (1/2:ℝ) 3 := by
    have hx0 : 0 < x := by linarith only [hx.1]
    have hy0 : 0 < y := by linarith only [hy.1]
    have hp := mul_pos hη hy0
    have hb := mul_le_mul hηmax hy.2 hy0.le (by norm_num : (0:ℝ) ≤ 1/8)
    refine ⟨hx0,add_pos hx0 hp,?_⟩
    constructor <;> nlinarith only [hx.1,hx.2,hp,hb]
  have hDx (x : ℝ) (hx : x ∈ Icc (3/4:ℝ) (9/4)) :
      HasDerivAt (fun t => H (w.1,t)) (fderiv ℝ H (w.1,x) (0,1)) x := by
    have hh := (positive_difference_curvature_directions F (σ:=σ)
      (hgeom x w.1 hx hy).1 (hgeom x w.1 hx hy).2.1 hf 2).1
    exact (hh.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt x
      ((hasDerivAt_const x w.1).prodMk (hasDerivAt_id x))
  have hGlow (x : ℝ) (hx : x ∈ Icc (3/4:ℝ) (9/4)) :
      c/(2*σ) ≤ |fderiv ℝ H (w.1,x) (0,1)| :=
    (positive_jets_difference_curvature_entry F hσ hc hU hη hηmax
      hx hy hf hbound htests 3 (by norm_num) (by norm_num)).2.2.2.1
  have hDy (y : ℝ) (hy : y ∈ Icc (1/2:ℝ) 3) :
      HasDerivAt (fun t => H (t,x₀)) (-iteratedDeriv 3 F (x₀+η*y)/σ) y := by
    have hg := hgeom x₀ y ⟨hx.1.le,hx.2.le⟩ hy
    have hh := positive_difference_curvature_directions F (σ:=σ) hg.1 hg.2.1 hf 2
    have hd :=
      (hh.1.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt y
        ((hasDerivAt_id y).prodMk (hasDerivAt_const y x₀))
    change HasDerivAt (fun t => H (t,x₀)) (fderiv ℝ H (y,x₀) (1,0)) y at hd
    have he : fderiv ℝ H (y,x₀) (1,0)=-iteratedDeriv 3 F (x₀+η*y)/σ := by
      rw [hh.2.2]
      field_simp
    rw [he] at hd
    exact hd
  have hDbound (y : ℝ) (hy : y ∈ Icc (1/2:ℝ) 3) :
      ‖deriv (fun t => H (t,x₀)) y‖ ≤ V := by
    rw [(hDy y hy).deriv,Real.norm_eq_abs,abs_div,abs_neg,abs_of_pos hσ]
    exact div_le_div_of_nonneg_right
      (hbound _ (hgeom x₀ y ⟨hx.1.le,hx.2.le⟩ hy).2.2 2 (by norm_num)) hσ.le
  have hy₀' : y₀ ∈ Icc (1/2:ℝ) 3 := by
    constructor <;> linarith only [hy₀.1,hy₀.2]
  have hshift : |H (w.1,x₀)-H (y₀,x₀)| ≤ V*|w.1-y₀| :=
    (convex_Icc (1/2:ℝ) 3).norm_image_sub_le_of_norm_deriv_le
      (fun y hy => (hDy y hy).differentiableAt) hDbound hy₀' hy
  have hnear : |w.2-H (w.1,x₀)| < c/(8*σ) := by
    calc
      _ ≤ |w.2-H (y₀,x₀)|+|H (y₀,x₀)-H (w.1,x₀)| :=
        abs_sub_le _ _ _
      _ ≤ |w.2-H (y₀,x₀)|+V*|w.1-y₀| := by
        rw [abs_sub_comm (H (y₀,x₀))]
        exact add_le_add le_rfl hshift
      _ < r+V*r := add_lt_add hwu (mul_lt_mul_of_pos_left hwy hV)
      _ = (1+V)*r := by ring
      _ ≤ (1+V)*(c/(16*σ*(1+V))) := mul_le_mul_of_nonneg_left hr₂ (by positivity)
      _ = c/(16*σ) := by field_simp
      _ < c/(8*σ) := by
        apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith only [mul_pos hc hσ]
  obtain ⟨hinj,hcover⟩ := interval_root_coverage_of_abs_derivative
    (fun x => H (w.1,x)) (fun x => fderiv ℝ H (w.1,x) (0,1))
    (show 0 < c/(2*σ) by positivity) hx hDx hGlow
  have hmargin : c/(8*σ) ≤ c/(2*σ)*min (x₀-3/4) (9/4-x₀) := by
    have hmin : (1/4:ℝ) ≤ min (x₀-3/4) (9/4-x₀) :=
      le_min (by linarith only [hx₀.1]) (by linarith only [hx₀.2])
    calc
      _ = c/(2*σ)*(1/4) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmin (by positivity)
  obtain ⟨x,hx,he⟩ := hcover w.2 (hnear.trans_le hmargin)
  have himage : w.2 ∈ (fun x => H (w.1,x)) '' Ioo (3/4:ℝ) (9/4) := ⟨x,hx,he⟩
  exact ⟨Function.invFunOn_mem himage,hy,Function.invFunOn_eq himage,
    hinj.mono Ioo_subset_Icc_self⟩


                                                                         
                                                                      
                                                                       
theorem triangular_profile_endpoint_compression
    (f : ℝ × ℝ → ℝ) {S : Set (ℝ × ℝ)}
    {ya yb b l r κ M ε δ : ℝ}
    (hκ : 0 < κ) (hM : 0 ≤ M) (hsmall : 8*M*ε ≤ κ)
    (hlr : l < r) (hlen : r-l ≤ 2)
    (hS : Convex ℝ S)
    (hF : ∀ w ∈ S, ContDiffAt ℝ 2 f w)
    (hpoints : ∀ t ∈ Icc l r, (ya,t) ∈ S ∧ (yb,t+b) ∈ S)
    (hleft : |f (yb,l+b)-f (ya,l)| ≤ δ)
    (hright : |f (yb,r+b)-f (ya,r)| ≤ δ) :
    let Φ := fun w => (f w,fderiv ℝ f w (0,1))
    (∀ p ∈ S, ∀ w ∈ S, ‖fderiv ℝ Φ w-fderiv ℝ Φ p‖ ≤ ε) →
    (∀ p ∈ S, ‖fderiv ℝ Φ p (1,0)‖ ≤ M ∧ ‖fderiv ℝ Φ p (0,1)‖ ≤ M) →
    (∀ p ∈ S, κ ≤ |(fderiv ℝ Φ p (1,0)).1*(fderiv ℝ Φ p (0,1)).2-
      (fderiv ℝ Φ p (0,1)).1*(fderiv ℝ Φ p (1,0)).2|) →
    κ*‖((yb-ya,b):ℝ × ℝ)‖*(r-l) ≤ 16*M*δ := by
  intro Φ hvar hcol hdet
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hleft
  have hder t (ht : t ∈ Icc l r) :
      HasDerivAt (fun s => f (yb,s+b)-f (ya,s))
        (fderiv ℝ f (yb,t+b) (0,1)-fderiv ℝ f (ya,t) (0,1)) t := by
    have h₁ := ((hF _ (hpoints t ht).2).of_le
      (by norm_num : (1:WithTop ℕ∞) ≤ 2)).differentiableAt_one.hasFDerivAt
    have h₂ := ((hF _ (hpoints t ht).1).of_le
      (by norm_num : (1:WithTop ℕ∞) ≤ 2)).differentiableAt_one.hasFDerivAt
    have hc₁ : HasDerivAt (fun s : ℝ => (yb,s+b)) (0,1) t :=
      (hasDerivAt_const t yb).prodMk ((hasDerivAt_id t).add_const b)
    have hc₂ : HasDerivAt (fun s : ℝ => (ya,s)) (0,1) t :=
      (hasDerivAt_const t ya).prodMk (hasDerivAt_id t)
    exact (h₁.comp_hasDerivAt t hc₁).sub (h₂.comp_hasDerivAt t hc₂)
  obtain ⟨t,ht,hdt⟩ := exists_small_deriv_of_two_values (sub_pos.mpr hlr) le_rfl
    hder hleft hright
  have ht' : t ∈ Icc l r := ⟨ht.1.le,ht.2.le⟩
  have hΦ w (hw : w ∈ S) : DifferentiableAt ℝ Φ w := by
    have hf₀ := ((hF w hw).of_le
      (by norm_num : (1:WithTop ℕ∞) ≤ 2)).differentiableAt_one
    have hf₁ : ContDiffAt ℝ 1 (fun v => fderiv ℝ f v (0,1)) w :=
      ((hF w hw).fderiv_right (by norm_num : (1:WithTop ℕ∞)+1 ≤ 2)).clm_apply contDiffAt_const
    exact hf₀.prodMk hf₁.differentiableAt_one
  let p₀ : ℝ × ℝ := (ya,l)
  let Δ : ℝ × ℝ := (yb-ya,b)
  let A := fderiv ℝ Φ p₀
  have hp₀ : p₀ ∈ S := (hpoints l ⟨le_rfl,hlr.le⟩).1
  have hAder w : fderiv ℝ (fun v => A v) w=A := A.hasFDerivAt.fderiv
  have hlin : κ*‖Δ‖ ≤ 4*M*‖A Δ‖ := by
    have hh := planar_profile_quantitative_separation (fun v => A v)
      (S:=Set.univ) (p:=0) (q:=Δ) (ε:=0) hM
      (by simpa using hκ.le) convex_univ (Set.mem_univ _) (Set.mem_univ _)
      (fun _ _ => A.differentiableAt)
      (by intro w _; rw [hAder,hAder,sub_self,norm_zero])
      (by rw [hAder]; exact (hcol p₀ hp₀).1)
      (by rw [hAder]; exact (hcol p₀ hp₀).2)
      (by rw [hAder]; exact hdet p₀ hp₀)
    simpa only [sub_zero,map_zero] using hh
  have hrem s (hs : s ∈ Icc l r) :
      ‖Φ (yb,s+b)-Φ (ya,s)-A Δ‖ ≤ ε*‖Δ‖ := by
    have hh := hS.norm_image_sub_le_of_norm_fderiv_le' hΦ (hvar p₀ hp₀)
      (hpoints s hs).1 (hpoints s hs).2
    have he : ((yb,s+b):ℝ × ℝ)-(ya,s)=Δ := by ext <;> simp [Δ]
    rw [he] at hh
    exact hh
  have hb₁ : |(A Δ).1| ≤ δ+ε*‖Δ‖ := by
    have hh := (norm_fst_le (Φ (yb,l+b)-Φ (ya,l)-A Δ)).trans
      (hrem l ⟨le_rfl,hlr.le⟩)
    change |f (yb,l+b)-f (ya,l)-(A Δ).1| ≤ ε*‖Δ‖ at hh
    exact abs_le.mpr ⟨by linarith only [(abs_le.mp hleft).1,(abs_le.mp hh).2],
      by linarith only [(abs_le.mp hleft).2,(abs_le.mp hh).1]⟩
  have hb₂ : |(A Δ).2| ≤ 2*δ/(r-l)+ε*‖Δ‖ := by
    have hh := (norm_snd_le (Φ (yb,t+b)-Φ (ya,t)-A Δ)).trans (hrem t ht')
    change |fderiv ℝ f (yb,t+b) (0,1)-fderiv ℝ f (ya,t) (0,1)-(A Δ).2| ≤ ε*‖Δ‖ at hh
    exact abs_le.mpr ⟨by linarith only [(abs_le.mp hdt).1,(abs_le.mp hh).2],
      by linarith only [(abs_le.mp hdt).2,(abs_le.mp hh).1]⟩
  have hδwidth : δ ≤ 2*δ/(r-l) := by
    apply (le_div_iff₀ (sub_pos.mpr hlr)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hlen hδ]
  have hbA : ‖A Δ‖ ≤ 2*δ/(r-l)+ε*‖Δ‖ := by
    change max |(A Δ).1| |(A Δ).2| ≤ _
    exact max_le (hb₁.trans (add_le_add hδwidth le_rfl)) hb₂
  have hm := mul_le_mul_of_nonneg_left hbA (show 0 ≤ 4*M by positivity)
  have hs := mul_le_mul_of_nonneg_right hsmall (norm_nonneg Δ)
  have hlow : κ*‖Δ‖ ≤ 8*M*(2*δ/(r-l)) := by nlinarith only [hlin,hm,hs]
  have he := mul_le_mul_of_nonneg_right hlow (sub_pos.mpr hlr).le
  calc
    _ ≤ (8*M*(2*δ/(r-l)))*(r-l) := he
    _ = _ := by field_simp [ne_of_gt (sub_pos.mpr hlr)]; ring


                                                                       
                                                                       
                                                                    
                                                                    
theorem positive_difference_constructed_endpoint_compression
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ a : ℝ, 0 < a ∧
      ∀ (F : ℝ → ℝ) (η x₀ y₀ ya yb b l r δ : ℝ),
      0 < η → η ≤ 1/8 → x₀ ∈ Icc (1:ℝ) 2 → y₀ ∈ Icc (1:ℝ) 2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let ρ := fun w : ℝ × ℝ =>
        Function.invFunOn (fun x => H (w.1,x)) (Ioo (3/4:ℝ) (9/4)) w.2
      let g := fun w => fderiv ℝ H (w.1,ρ w) (0,1)
      let z₀ := (y₀,H (y₀,x₀))
      let R := max 1 (max (3*U/σ) (2*σ/c))
      let κ := (c/(6*U))^2*(c^2*c/(6*U^4))
      l < r → r-l ≤ 2 →
      (∀ t ∈ Icc l r, ‖((ya,t):ℝ × ℝ)-z₀‖ < a ∧ ‖((yb,t+b):ℝ × ℝ)-z₀‖ < a) →
      |g (yb,l+b)-g (ya,l)| ≤ δ → |g (yb,r+b)-g (ya,r)| ≤ δ →
      κ*‖((yb-ya,b):ℝ × ℝ)‖*(r-l) ≤ 64*R^6*δ := by
  let R := max 1 (max (3*U/σ) (2*σ/c))
  let κ := (c/(6*U))^2*(c^2*c/(6*U^4))
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  obtain ⟨r₀,hr₀,hchart⟩ := positive_difference_uniform_root_chart hσ hc hU
  obtain ⟨L,hL,hvariation⟩ := positive_difference_profile_uniform_variation hσ hc hU
  let a := min r₀ (κ/(64*R^6*L))
  have ha : 0 < a := by dsimp only [a]; positivity
  refine ⟨a,ha,?_⟩
  intro F η x₀ y₀ ya yb b l r δ hη hηmax hx₀ hy₀ hf hbound htests H ρ g z₀ R' κ'
    hlr hlen hpoints hleft hright
  let I := Ioo (3/4:ℝ) (9/4)
  let S := Metric.ball z₀ a
  let Φ := fun w => (g w,fderiv ℝ g w (0,1))
  have hI : IsOpen I := isOpen_Ioo
  have hS : IsOpen S := Metric.isOpen_ball
  have hconv : Convex ℝ S := convex_ball _ _
  have hdata w (hw : w ∈ S) :
      ρ w ∈ I ∧ w.1 ∈ Icc (1/2:ℝ) 3 ∧
      H (w.1,ρ w)=w.2 ∧ Set.InjOn (fun x => H (w.1,x)) I := by
    have hh : ‖w-z₀‖ < a := by simpa only [S,Metric.mem_ball,dist_eq_norm] using hw
    exact hchart F η x₀ y₀ hη hηmax hx₀ hy₀ hf hbound htests w
      (hh.trans_le (min_le_left _ _))
  have hrange w (hw : w ∈ S) :
      ρ w ∈ Icc (3/4:ℝ) (9/4) ∧ w.1 ∈ Icc (1/2:ℝ) 3 :=
    ⟨⟨(hdata w hw).1.1.le,(hdata w hw).1.2.le⟩,(hdata w hw).2.1⟩
  have hroot w (hw : w ∈ S) : ρ w ∈ I ∧ H (w.1,ρ w)=w.2 :=
    ⟨(hdata w hw).1,(hdata w hw).2.2.1⟩
  have huniq w (hw : w ∈ S) : Set.InjOn (fun x => H (w.1,x)) I :=
    (hdata w hw).2.2.2
  have hlocal w (hw : w ∈ S) :
      (∀ᶠ v in 𝓝 w, ρ v ∈ I ∧ H (v.1,ρ v)=v.2) ∧
      (∀ᶠ v in 𝓝 w, Set.InjOn (fun x => H (v.1,x)) I) := by
    constructor
    · filter_upwards [hS.mem_nhds hw] with v hv
      exact hroot v hv
    · filter_upwards [hS.mem_nhds hw] with v hv
      exact huniq v hv
  have hg w (hw : w ∈ S) : ContDiffAt ℝ ∞ g w := by
    have hx : 0 < ρ w := by linarith only [(hrange w hw).1.1]
    have hy : 0 < w.1 := by linarith only [(hrange w hw).2.1]
    have hz : 0 < ρ w+η*w.1 := add_pos hx (mul_pos hη hy)
    have hH : ContDiffAt ℝ ∞ H (w.1,ρ w) :=
      (positive_difference_curvature_directions F (σ:=σ) hx hz hf 2).1
    have hGbound := (positive_jets_difference_curvature_entry F hσ hc hU hη hηmax
      (hrange w hw).1 (hrange w hw).2 hf hbound htests 3 (by norm_num) (by norm_num)).2.2.2.1
    have hG0 : fderiv ℝ H (w.1,ρ w) (0,1) ≠ 0 :=
      abs_pos.mp (lt_of_lt_of_le (by positivity : 0 < c/(2*σ)) hGbound)
    have hρ := curvature_surface_root_contDiffAt H ρ (by simp) hI
      (hroot w hw).1 hH hG0 (hlocal w hw).1 (hlocal w hw).2
    have hG : ContDiffAt ℝ ∞ (fun v => fderiv ℝ H v (0,1)) (w.1,ρ w) :=
      (hH.fderiv_right (by simp : (∞:ℕ∞ω)+1 ≤ ∞)).clm_apply contDiffAt_const
    exact hG.comp w (contDiffAt_fst.prodMk hρ)
  have hdet w (hw : w ∈ S) : κ ≤
      |(fderiv ℝ Φ w (1,0)).1*(fderiv ℝ Φ w (0,1)).2-
        (fderiv ℝ Φ w (0,1)).1*(fderiv ℝ Φ w (1,0)).2| := by
    have hj := positive_difference_inverse_profile_jacobian_lower F ρ hσ hc hU hη hηmax
      (hrange w hw).1 (hrange w hw).2 hf hbound htests hI
      (hroot w hw).1 (hlocal w hw).1 (hlocal w hw).2
    let q := fun v => fderiv ℝ g v (0,1)
    have hq : ContDiffAt ℝ ∞ q w :=
      ((hg w hw).fderiv_right (by simp : (∞:ℕ∞ω)+1 ≤ ∞)).clm_apply contDiffAt_const
    have hdg := ((hg w hw).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)).differentiableAt_one.hasFDerivAt
    have hdq := (hq.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)).differentiableAt_one.hasFDerivAt
    rw [(hdg.prodMk hdq).fderiv]
    change κ ≤ |fderiv ℝ g w (1,0)*fderiv ℝ q w (0,1)-
      fderiv ℝ g w (0,1)*fderiv ℝ q w (1,0)|
    rw [mul_comm (fderiv ℝ g w (1,0)),abs_sub_comm]
    exact hj
  have hcol w (hw : w ∈ S) :
      ‖fderiv ℝ Φ w (1,0)‖ ≤ 4*R^6 ∧ ‖fderiv ℝ Φ w (0,1)‖ ≤ 4*R^6 :=
    positive_difference_inverse_profile_columns_bound F ρ hσ hc hU hη hηmax
      (hrange w hw).1 (hrange w hw).2 hf hbound htests hI
      (hroot w hw).1 (hlocal w hw).1 (hlocal w hw).2
  have hvar p (hp : p ∈ S) q (hq : q ∈ S) :
      ‖fderiv ℝ Φ q-fderiv ℝ Φ p‖ ≤ κ/(32*R^6) := by
    have hp' : ‖p-z₀‖ < a := by simpa only [S,Metric.mem_ball,dist_eq_norm] using hp
    have hq' : ‖q-z₀‖ < a := by simpa only [S,Metric.mem_ball,dist_eq_norm] using hq
    have hdist : ‖q-p‖ ≤ 2*a := by
      have he : q-p=(q-z₀)-(p-z₀) := by abel
      rw [he]
      exact (norm_sub_le _ _).trans (by linarith only [hp',hq'])
    have hv := hvariation F ρ η I S hη hηmax hf hbound htests hI hS hconv
      hrange hroot huniq p hp q hq
    calc
      _ ≤ L*‖q-p‖ := hv
      _ ≤ L*(2*a) := mul_le_mul_of_nonneg_left hdist hL.le
      _ ≤ L*(2*(κ/(64*R^6*L))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (min_le_right _ _) (by norm_num)) hL.le
      _ = _ := by field_simp; ring
  have hsmall : 8*(4*R^6)*(κ/(32*R^6)) ≤ κ := by
    have he : 8*(4*R^6)*(κ/(32*R^6))=κ := by field_simp; ring
    exact he.le
  have hpts t (ht : t ∈ Icc l r) : (ya,t) ∈ S ∧ (yb,t+b) ∈ S := by
    simpa only [S,Metric.mem_ball,dist_eq_norm] using hpoints t ht
  have hh := triangular_profile_endpoint_compression g hκ (show 0 ≤ 4*R^6 by positivity)
    hsmall hlr hlen hconv
    (fun w hw => (hg w hw).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    hpts hleft hright hvar hcol hdet
  convert hh using 1
  ring


                                                                     
                                                                       
                                                                  
private theorem interval_abs_derivative_lower
    (f f' : ℝ → ℝ) {a b x y L : ℝ}
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hlower : ∀ t ∈ Icc a b, L ≤ |f' t|) :
    L*|y-x| ≤ |f y-f x| := by
  have hordered s t (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
      L*(t-s) ≤ |f t-f s| := by
    rcases hst.eq_or_lt with he | hlt
    · subst t
      simp
    have hsub : Icc s t ⊆ Icc a b := fun v hv => ⟨hs.1.trans hv.1,hv.2.trans ht.2⟩
    obtain ⟨v,hv,he⟩ := exists_hasDerivAt_eq_slope f f' hlt
      (fun w hw => (hd w (hsub hw)).continuousAt.continuousWithinAt)
      (fun w hw => hd w (hsub ⟨hw.1.le,hw.2.le⟩))
    have hb := hlower v (hsub ⟨hv.1.le,hv.2.le⟩)
    rw [he,abs_div,abs_of_pos (sub_pos.mpr hlt)] at hb
    exact (le_div_iff₀ (sub_pos.mpr hlt)).mp hb
  rcases le_total x y with hxy | hyx
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hxy)] using hordered x y hx hy hxy
  · rw [abs_sub_comm y x,abs_sub_comm (f y) (f x)]
    simpa only [abs_of_nonneg (sub_nonneg.mpr hyx)] using hordered y x hy hx hyx


                                                                        
                                                                           
theorem positive_difference_curvature_inverse_eq
    (F : ℝ → ℝ) {σ c U η x y u : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hx : x ∈ Ioo (3/4:ℝ) (9/4)) (hy : y ∈ Icc (1/2:ℝ) 3)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hroot : (iteratedDeriv 2 F x-iteratedDeriv 2 F (x+η*y))/(σ*η)=u) :
    Function.invFunOn
      (fun t => (iteratedDeriv 2 F t-iteratedDeriv 2 F (t+η*y))/(σ*η))
      (Ioo (3/4:ℝ) (9/4)) u=x := by
  let H := fun v : ℝ × ℝ =>
    (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
  let G := fun t => fderiv ℝ H (y,t) (0,1)
  have hy0 : 0 < y := by linarith only [hy.1]
  have hDx t (ht : t ∈ Icc (3/4:ℝ) (9/4)) :
      HasDerivAt (fun s => H (y,s)) (G t) t := by
    have ht0 : 0 < t := by linarith only [ht.1]
    have hh := (positive_difference_curvature_directions F (σ:=σ) ht0
      (add_pos ht0 (mul_pos hη hy0)) hf 2).1
    exact (hh.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t y).prodMk (hasDerivAt_id t))
  have hGl t (ht : t ∈ Icc (3/4:ℝ) (9/4)) : c/(2*σ) ≤ |G t| :=
    (positive_jets_difference_curvature_entry F hσ hc hU hη hηmax
      ht hy hf hbound htests 3 (by norm_num) (by norm_num)).2.2.2.1
  have hi : Set.InjOn (fun t => H (y,t)) (Ioo (3/4:ℝ) (9/4)) := by
    intro s hs t ht heq
    have hh := interval_abs_derivative_lower (fun t => H (y,t)) G
      ⟨hs.1.le,hs.2.le⟩ ⟨ht.1.le,ht.2.le⟩ hDx hGl
    change H (y,s)=H (y,t) at heq
    rw [heq,sub_self,abs_zero] at hh
    have hl : 0 < c/(2*σ) := by positivity
    have hz : |t-s|=0 := le_antisymm
      ((mul_le_mul_iff_of_pos_left hl).mp (by simpa only [mul_zero] using hh))
      (abs_nonneg _)
    exact (sub_eq_zero.mp (abs_eq_zero.mp hz)).symm
  have himage : u ∈ (fun t => H (y,t)) '' Ioo (3/4:ℝ) (9/4) := ⟨x,hx,hroot⟩
  exact hi (Function.invFunOn_mem himage) hx ((Function.invFunOn_eq himage).trans hroot.symm)


                                                                         
                                                                        
                                                               
theorem positive_difference_physical_iteratedDeriv
    (F : ℝ → ℝ) {σ η y T M x : ℝ} (hM : 0 < M) (hx : 0 < x)
    (hshift : 0 ≤ η*y) (hf : ∀ z, 0 < z → ContDiffAt ℝ ∞ F z) (n : ℕ) :
    iteratedDeriv n (fun z => T*(F (z/M)-F (z/M+η*y))/(σ*η)) x =
      T/M^n*((iteratedDeriv n F (x/M)-iteratedDeriv n F (x/M+η*y))/(σ*η)) := by
  induction n generalizing x with
  | zero => simp only [iteratedDeriv_zero,pow_zero,div_one]; ring
  | succ n ih =>
    have he : iteratedDeriv n (fun z => T*(F (z/M)-F (z/M+η*y))/(σ*η))
        =ᶠ[𝓝 x] fun z =>
          T/M^n*((iteratedDeriv n F (z/M)-iteratedDeriv n F (z/M+η*y))/(σ*η)) :=
      (eventually_gt_nhds hx).mono (fun z hz => ih hz)
    have hxM : 0 < x/M := div_pos hx hM
    have hxS : 0 < x/M+η*y := add_pos_of_pos_of_nonneg hxM hshift
    have hd₀ := hasDerivAt_iteratedDeriv_finite (show n < n+1 by omega)
      ((hf _ hxM).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl (n+1)))
    have hd₁ := hasDerivAt_iteratedDeriv_finite (show n < n+1 by omega)
      ((hf _ hxS).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl (n+1)))
    have hd := (((hd₀.comp x ((hasDerivAt_id x).div_const M)).sub
      (hd₁.comp x (((hasDerivAt_id x).div_const M).add_const (η*y)))).div_const
        (σ*η)).const_mul (T/M^n)
    rw [iteratedDeriv_succ,he.deriv_eq]
    calc
      _ = T/M^n*((iteratedDeriv (n+1) F (x/M)*(1/M)-
          iteratedDeriv (n+1) F (x/M+η*y)*(1/M))/(σ*η)) := hd.deriv
      _ = _ := by simp only [pow_succ,div_eq_mul_inv,mul_inv_rev]; ring


                                                                 
                                                                       
                                                     
theorem positive_difference_rounded_third_bound
    (F : ℝ → ℝ) {σ c U η M xa xb ya yb Δ : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hM : 2 ≤ M) (hxa : xa ∈ Icc (1:ℝ) 2) (hxb : xb ∈ Icc (1:ℝ) 2)
    (hya : ya ∈ Icc (1:ℝ) 2) (hyb : yb ∈ Icc (1:ℝ) 2)
    (hf : ∀ z, 0 < z → ContDiffAt ℝ ∞ F z)
    (hbound : ∀ z ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F z| ≤ U)
    (htests : ∀ z ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F z) j|)
    (hΔ : 0 ≤ Δ) :
    let G := fun v : ℝ × ℝ =>
      (iteratedDeriv 3 F v.2-iteratedDeriv 3 F (v.2+η*v.1))/(σ*η)
    let R := max 1 (max (3*U/σ) (2*σ/c))
    |G (yb,(round (M*xb):ℝ)/M)/G (ya,(round (M*xa):ℝ)/M)-1| ≤ Δ →
    |G (yb,xb)-G (ya,xa)| ≤ R*(Δ+1/M) := by
  intro G R hnear
  have hMpos : 0 < M := by linarith only [hM]
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let rd := fun x : ℝ => (round (M*x):ℝ)/M
  have hr x : |rd x-x| ≤ 1/(2*M) := by
    calc
      _ = |((round (M*x):ℝ)-M*x)/M| := by
        congr 1
        dsimp only [rd]
        field_simp
      _ = |(round (M*x):ℝ)-M*x|/M := by rw [abs_div,abs_of_pos hMpos]
      _ ≤ (1/2)/M := div_le_div_of_nonneg_right
        (by simpa only [abs_sub_comm] using abs_sub_round (M*x)) hMpos.le
      _ = _ := by ring
  have hquarter : 1/(2*M) ≤ (1/4:ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2*M)).mpr
    linarith only [hM]
  have hxext x (hx : x ∈ Icc (1:ℝ) 2) : x ∈ Icc (3/4:ℝ) (9/4) :=
    ⟨by linarith only [hx.1],by linarith only [hx.2]⟩
  have hrange x (hx : x ∈ Icc (1:ℝ) 2) : rd x ∈ Icc (3/4:ℝ) (9/4) := by
    have hb := abs_le.mp ((hr x).trans hquarter)
    constructor <;> linarith only [hb.1,hb.2,hx.1,hx.2]
  have hyext y (hy : y ∈ Icc (1:ℝ) 2) : y ∈ Icc (1/2:ℝ) 3 :=
    ⟨by linarith only [hy.1],by linarith only [hy.2]⟩
  have hjet x y (hx : x ∈ Icc (3/4:ℝ) (9/4)) (hy : y ∈ Icc (1:ℝ) 2) :
      ∀ i, |differenceProfileJet F σ η (y,x) i| ≤ R :=
    (positive_difference_profile_jet_bound F hσ hc hU hη hηmax hx (hyext y hy)
      hf hbound htests).2.1
  have hder x y (hx : x ∈ Icc (3/4:ℝ) (9/4)) (hy : y ∈ Icc (1:ℝ) 2) :
      HasDerivAt (fun z => G (y,z))
        ((iteratedDeriv 4 F x-iteratedDeriv 4 F (x+η*y))/(σ*η)) x := by
    have hx0 : 0 < x := by linarith only [hx.1]
    have hy0 : 0 < y := by linarith only [hy.1]
    have hj := positive_difference_curvature_directions F (σ:=σ) hx0
      (add_pos hx0 (mul_pos hη hy0)) hf 3
    have hd := (hj.1.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt x
      ((hasDerivAt_const x y).prodMk (hasDerivAt_id x))
    convert hd using 1
    · rfl
    simpa using hj.2.1.symm
  have herr x y (hx : x ∈ Icc (1:ℝ) 2) (hy : y ∈ Icc (1:ℝ) 2) :
      |G (y,x)-G (y,rd x)| ≤ R/(2*M) := by
    have hh : |G (y,x)-G (y,rd x)| ≤ R*|x-rd x| := by
      apply (convex_Icc (3/4:ℝ) (9/4)).norm_image_sub_le_of_norm_deriv_le
        (fun z hz => (hder z y hz hy).differentiableAt) (fun z hz => ?_)
        (hrange x hx) (hxext x hx)
      rw [(hder z y hz hy).deriv]
      exact hjet z y hz hy 2
    calc
      _ ≤ R*|x-rd x| := hh
      _ ≤ R*(1/(2*M)) := mul_le_mul_of_nonneg_left (by simpa only [abs_sub_comm] using hr x) hR.le
      _ = _ := by ring
  have hGa : G (ya,rd xa) ≠ 0 := by
    have hj := positive_jets_difference_curvature_entry F hσ hc hU hη hηmax
      (hrange xa hxa) (hyext ya hya) hf hbound htests 3 (by norm_num) (by norm_num)
    have hh := hj.2.2.2.1
    rw [hj.2.2.1] at hh
    exact abs_pos.mp (lt_of_lt_of_le (by positivity : 0 < c/(2*σ)) hh)
  have hcoinc : |G (yb,rd xb)-G (ya,rd xa)| ≤ R*Δ := by
    calc
      _ = |G (ya,rd xa)| * |G (yb,rd xb)/G (ya,rd xa)-1| := by
        rw [←abs_mul]
        congr 1
        field_simp
      _ ≤ |G (ya,rd xa)| * Δ := mul_le_mul_of_nonneg_left hnear (abs_nonneg _)
      _ ≤ R*Δ := mul_le_mul_of_nonneg_right (hjet (rd xa) ya (hrange xa hxa) hya 1) hΔ
  calc
    _ ≤ |G (yb,xb)-G (yb,rd xb)|+|G (yb,rd xb)-G (ya,rd xa)|+
        |G (ya,rd xa)-G (ya,xa)| := by
      calc
        _ ≤ |G (yb,xb)-G (yb,rd xb)|+|G (yb,rd xb)-G (ya,xa)| :=
          abs_sub_le _ _ _
        _ ≤ |G (yb,xb)-G (yb,rd xb)|+
            (|G (yb,rd xb)-G (ya,rd xa)|+|G (ya,rd xa)-G (ya,xa)|) :=
          add_le_add le_rfl (abs_sub_le _ _ _)
        _ = _ := by ring
    _ ≤ R/(2*M)+R*Δ+R/(2*M) := by
      rw [abs_sub_comm (G (ya,rd xa))]
      exact add_le_add (add_le_add (herr xb yb hxb hyb) hcoinc) (herr xa ya hxa hya)
    _ = _ := by ring



                                                                      
                                                                         
                                                                      
theorem reciprocal_profile_case_two_jacobian_identity
    (H G K L B Z T : ℝ) (hH : H ≠ 0) (hG : G ≠ 0) :
    let gy := Z-K*B/G
    let gt := K/G
    let gtt := (L*G-K^2)/G^3
    let gty := (T*G-K*Z)/G^2-B*(L*G-K^2)/G^3
    (gy/H^3)*(6*G/H-4*gt+H*gtt)-
      (3*G/H^2-gt/H)*(3*gy/H^2-gty/H) =
      TaoTrudgianYang2025.HuxleyModel.caseTwoTests ![H,G,K,L,B,Z,T] 1/(H^4*G^2) := by
  dsimp only
  dsimp [TaoTrudgianYang2025.HuxleyModel.caseTwoTests]
  erw [Matrix.det_fin_three]
  norm_num
  field_simp
  ring



                                                               
                                                                    
                                                       
theorem reciprocal_profile_derivative_matrix
    (g : ℝ × ℝ → ℝ) {z : ℝ × ℝ} (hz : z.2 ≠ 0)
    (hg : ContDiffAt ℝ 2 g (z.1,z.2⁻¹)) :
    let p := (z.1,z.2⁻¹)
    let q := fun w => fderiv ℝ g w (0,1)
    let k := fun w : ℝ × ℝ => w.2^3*g (w.1,w.2⁻¹)
    let Φ := fun w => (k w,fderiv ℝ k w (0,1))
    fderiv ℝ Φ z (1,0)=
      (z.2^3*fderiv ℝ g p (1,0),
        3*z.2^2*fderiv ℝ g p (1,0)-z.2*fderiv ℝ q p (1,0)) ∧
    fderiv ℝ Φ z (0,1)=
      (3*z.2^2*g p-z.2*q p,
        6*z.2*g p-4*q p+fderiv ℝ q p (0,1)/z.2) := by
  intro p q k Φ
  let ι := fun w : ℝ × ℝ => (w.1,w.2⁻¹)
  let Q := fun w : ℝ × ℝ => 3*w.2^2*g (ι w)-w.2*q (ι w)
  have hi w (hw : w.2 ≠ 0) :
      HasFDerivAt ι
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
          (-(w.2^2)⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ)) w := by
    exact hasFDerivAt_fst.prodMk ((hasDerivAt_inv hw).comp_hasFDerivAt w hasFDerivAt_snd)
  have hk w (hw : w.2 ≠ 0) (hgw : DifferentiableAt ℝ g (ι w)) :
      HasFDerivAt k
        ((w.2^3) • ((fderiv ℝ g (ι w)).comp
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
            (-(w.2^2)⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ)))+
          (3*w.2^2*g (ι w)) • ContinuousLinearMap.snd ℝ ℝ ℝ) w := by
    have hd := (hasFDerivAt_snd.pow 3).mul (hgw.hasFDerivAt.comp w (hi w hw))
    convert hd using 1
    · rfl
    apply ContinuousLinearMap.ext
    intro v
    simp [smul_eq_mul]
    ring
  have hq : ContDiffAt ℝ 1 q p :=
    (hg.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1 ≤ 2)).clm_apply contDiffAt_const
  have hgd : DifferentiableAt ℝ g p := (hg.of_le (by norm_num : (1:WithTop ℕ∞) ≤ 2)).differentiableAt_one
  have hnear : ∀ᶠ w in 𝓝 z, w.2 ≠ 0 ∧ DifferentiableAt ℝ g (ι w) := by
    have h₁ := (hasFDerivAt_snd (𝕜:=ℝ) (p:=z)).continuousAt.eventually_ne hz
    have h₂ := (hi z hz).continuousAt
      ((hg.of_le (by norm_num : (1:WithTop ℕ∞) ≤ 2)).eventually (by norm_num))
    filter_upwards [h₁,h₂] with w hw hg'
    exact ⟨hw,hg'.differentiableAt_one⟩
  have he : (fun w => fderiv ℝ k w (0,1)) =ᶠ[𝓝 z] Q := by
    filter_upwards [hnear] with w hw
    rw [(hk w hw.1 hw.2).fderiv]
    dsimp only [Q,q]
    simp only [add_apply,smul_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,smul_eq_mul]
    simp only [show (ContinuousLinearMap.fst ℝ ℝ ℝ) ((0,1):ℝ × ℝ)=0 from rfl,
      show (ContinuousLinearMap.snd ℝ ℝ ℝ) ((0,1):ℝ × ℝ)=1 from rfl,mul_one]
    have hv : ((0:ℝ),-(w.2^2)⁻¹)=(-(w.2^2)⁻¹) • ((0,1):ℝ × ℝ) := by ext <;> simp
    rw [hv,map_smul]
    dsimp only [smul_eq_mul]
    field_simp
    ring
  have hgcomp := hgd.hasFDerivAt.comp z (hi z hz)
  have hqcomp := hq.differentiableAt_one.hasFDerivAt.comp z (hi z hz)
  have hQ := (((hasFDerivAt_snd.pow 2).const_mul 3).mul hgcomp).sub
    (hasFDerivAt_snd.mul hqcomp)
  change HasFDerivAt Q _ z at hQ
  have hke := hk z hz hgd
  have hPhi : HasFDerivAt Φ ((fderiv ℝ k z).prod (fderiv ℝ Q z)) z := by
    have hkd : HasFDerivAt k (fderiv ℝ k z) z := hke.differentiableAt.hasFDerivAt
    exact hkd.prodMk (hQ.differentiableAt.hasFDerivAt.congr_of_eventuallyEq he)
  rw [hPhi.fderiv,hke.fderiv,hQ.fderiv]
  constructor
  · simp [ι,p,q]
  · simp only [ContinuousLinearMap.prod_apply,add_apply,
      sub_apply,smul_apply,
      ContinuousLinearMap.comp_apply,smul_eq_mul]
    simp only [show (ContinuousLinearMap.fst ℝ ℝ ℝ) ((0,1):ℝ × ℝ)=0 from rfl,
      show (ContinuousLinearMap.snd ℝ ℝ ℝ) ((0,1):ℝ × ℝ)=1 from rfl,mul_one]
    have hv : ((0:ℝ),-(z.2^2)⁻¹)=(-(z.2^2)⁻¹) • ((0,1):ℝ × ℝ) := by ext <;> simp
    rw [hv,map_smul,map_smul]
    dsimp only [smul_eq_mul,q,Function.comp_apply,ι,p]
    ext <;> field_simp <;> ring



                                                              
                                                                          
                                                                         
theorem curvature_surface_reciprocal_profile_jacobian
    (H : ℝ × ℝ → ℝ) (ρ : ℝ × ℝ → ℝ)
    {z : ℝ × ℝ} {I : Set ℝ} (hz : z.2 ≠ 0)
    (hI : IsOpen I) (hbase : ρ (z.1,z.2⁻¹) ∈ I)
    (hH : ContDiffAt ℝ 3 H (z.1,ρ (z.1,z.2⁻¹)))
    (hx0 : fderiv ℝ H (z.1,ρ (z.1,z.2⁻¹)) (0,1) ≠ 0)
    (hroot : ∀ᶠ w in 𝓝 (z.1,z.2⁻¹), ρ w ∈ I ∧ H (w.1,ρ w)=w.2)
    (huniq : ∀ᶠ w in 𝓝 (z.1,z.2⁻¹), Set.InjOn (fun x => H (w.1,x)) I) :
    let p := (z.1,ρ (z.1,z.2⁻¹))
    let G := fun v => fderiv ℝ H v (0,1)
    let K := fun v => fderiv ℝ G v (0,1)
    let Z := fun v => fderiv ℝ G v (1,0)
    let g := fun w => G (w.1,ρ w)
    let k := fun w : ℝ × ℝ => w.2^3*g (w.1,w.2⁻¹)
    let Φ := fun w => (k w,fderiv ℝ k w (0,1))
    (fderiv ℝ Φ z (1,0)).1*(fderiv ℝ Φ z (0,1)).2-
      (fderiv ℝ Φ z (0,1)).1*(fderiv ℝ Φ z (1,0)).2 =
      TaoTrudgianYang2025.HuxleyModel.caseTwoTests
        ![H p,G p,K p,fderiv ℝ K p (0,1),
          fderiv ℝ H p (1,0),Z p,fderiv ℝ K p (1,0)] 1/
        ((H p)^4*(G p)^2) := by
  intro p G K Z g k Φ
  let z₀ : ℝ × ℝ := (z.1,z.2⁻¹)
  let q := fun w => fderiv ℝ g w (0,1)
  have hρ : ContDiffAt ℝ 3 ρ z₀ := curvature_surface_root_contDiffAt H ρ
    (by norm_num) hI hbase hH hx0 hroot huniq
  have hG : ContDiffAt ℝ 2 G p :=
    (hH.fderiv_right (by norm_num : (2:WithTop ℕ∞)+1 ≤ 3)).clm_apply contDiffAt_const
  have hg : ContDiffAt ℝ 2 g z₀ :=
    hG.comp z₀ (contDiffAt_fst.prodMk (hρ.of_le (by norm_num)))
  have hq : ContDiffAt ℝ 1 q z₀ :=
    (hg.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1 ≤ 2)).clm_apply contDiffAt_const
  have hgd := (hg.of_le (by norm_num : (1:WithTop ℕ∞) ≤ 2)).differentiableAt_one.hasFDerivAt
  have hqd := hq.differentiableAt_one.hasFDerivAt
  have hΦ₀ : HasFDerivAt (fun w => (g w,q w))
      ((fderiv ℝ g z₀).prod (fderiv ℝ q z₀)) z₀ := hgd.prodMk hqd
  have hcols := curvature_surface_profile_derivative_matrix H ρ hI hbase hH hx0 hroot huniq
  change fderiv ℝ (fun w => (g w,q w)) z₀ (1,0)=_ ∧
    fderiv ℝ (fun w => (g w,q w)) z₀ (0,1)=_ at hcols
  rw [hΦ₀.fderiv] at hcols
  have hgy : fderiv ℝ g z₀ (1,0)=Z p-K p*fderiv ℝ H p (1,0)/G p :=
    congrArg Prod.fst hcols.1
  have hgt : q z₀=K p/G p := congrArg Prod.fst hcols.2
  have hqY : fderiv ℝ q z₀ (1,0)=
      (fderiv ℝ K p (1,0)*G p-K p*Z p)/G p^2-
        fderiv ℝ H p (1,0)*(fderiv ℝ K p (0,1)*G p-K p^2)/G p^3 :=
    congrArg Prod.snd hcols.1
  have hqU : fderiv ℝ q z₀ (0,1)=
      (fderiv ℝ K p (0,1)*G p-K p^2)/G p^3 := congrArg Prod.snd hcols.2
  have hn := reciprocal_profile_derivative_matrix g hz hg
  change fderiv ℝ Φ z (1,0)=_ ∧ fderiv ℝ Φ z (0,1)=_ at hn
  rw [hn.1,hn.2]
  change (z.2^3*fderiv ℝ g z₀ (1,0))*
      (6*z.2*G p-4*q z₀+fderiv ℝ q z₀ (0,1)/z.2)-
    (3*z.2^2*G p-z.2*q z₀)*
      (3*z.2^2*fderiv ℝ g z₀ (1,0)-z.2*fderiv ℝ q z₀ (1,0))=_
  rw [hgy,hgt,hqY,hqU]
  have hlevel : H p=z.2⁻¹ := hroot.self_of_nhds.2
  have hHne : H p ≠ 0 := by rw [hlevel]; exact inv_ne_zero hz
  have he := reciprocal_profile_case_two_jacobian_identity (H p) (G p) (K p)
    (fderiv ℝ K p (0,1)) (fderiv ℝ H p (1,0)) (Z p) (fderiv ℝ K p (1,0)) hHne hx0
  convert he using 1
  rw [hlevel]
  field_simp

                                                                       
                                                                             
theorem positive_difference_reciprocal_profile_jacobian_lower
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ η₀ κ : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < κ ∧
      ∀ (F : ℝ → ℝ) (ρ : ℝ × ℝ → ℝ) (η : ℝ)
        (z : ℝ × ℝ) (I : Set ℝ),
      0 < η → η ≤ η₀ → z.2 ≠ 0 →
      ρ (z.1,z.2⁻¹) ∈ Icc (3/4:ℝ) (9/4) → z.1 ∈ Icc (1:ℝ) 2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      IsOpen I → ρ (z.1,z.2⁻¹) ∈ I →
      (∀ᶠ w in 𝓝 (z.1,z.2⁻¹), ρ w ∈ I ∧
        (iteratedDeriv 2 F (ρ w)-iteratedDeriv 2 F (ρ w+η*w.1))/(σ*η)=w.2) →
      (∀ᶠ w in 𝓝 (z.1,z.2⁻¹), Set.InjOn
        (fun x => (iteratedDeriv 2 F x-iteratedDeriv 2 F (x+η*w.1))/(σ*η)) I) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let g := fun w => fderiv ℝ H (w.1,ρ w) (0,1)
      let k := fun w : ℝ × ℝ => w.2^3*g (w.1,w.2⁻¹)
      let Φ := fun w => (k w,fderiv ℝ k w (0,1))
      κ ≤ |(fderiv ℝ Φ z (1,0)).1*(fderiv ℝ Φ z (0,1)).2-
        (fderiv ℝ Φ z (0,1)).1*(fderiv ℝ Φ z (1,0)).2| := by
  obtain ⟨η₀,d,hη₀,hηcap,hd,hcase⟩ :=
    positive_jets_difference_case_two_tests hσ hc hU
  let R := max 1 (max (3*U/σ) (2*σ/c))
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨η₀,d/R^6,hη₀,hηcap,by positivity,?_⟩
  intro F ρ η z I hη hηsmall hz hx hy hf hbound htests hI hbase hroot huniq H g k Φ
  let z₀ : ℝ × ℝ := (z.1,z.2⁻¹)
  let p : ℝ × ℝ := (z.1,ρ z₀)
  let J := fun (r : ℕ) (v : ℝ × ℝ) =>
    (iteratedDeriv r F v.2-iteratedDeriv r F (v.2+η*v.1))/(σ*η)
  let Y := fun (r : ℕ) (v : ℝ × ℝ) =>
    -iteratedDeriv (r+1) F (v.2+η*v.1)/σ
  let G := fun v => fderiv ℝ H v (0,1)
  let K := fun v => fderiv ℝ G v (0,1)
  let D := fun r => iteratedDeriv r (fun u => (F u-F (u+η*z.1))/(σ*η)) (ρ z₀)
  let B := fun r => iteratedDeriv r
    (fun u => deriv (fun v => (F u-F (u+η*v))/(σ*η)) z.1) (ρ z₀)
  have hηmax : η ≤ 1/8 := hηsmall.trans hηcap
  have hy' : z.1 ∈ Icc (1/2:ℝ) 3 := ⟨by linarith only [hy.1],by linarith only [hy.2]⟩
  have hx0 : 0 < ρ z₀ := by change 0 < ρ (z.1,z.2⁻¹); linarith only [hx.1]
  have hy0 : 0 < z.1 := zero_lt_one.trans_le hy.1
  have hz0 : 0 < ρ z₀+η*z.1 := add_pos hx0 (mul_pos hη hy0)
  have hGerm (r : ℕ) (v : ℝ × ℝ) (hv : 0 < v.2) (hv' : 0 < v.2+η*v.1) :
      (fun w => fderiv ℝ (J r) w (0,1)) =ᶠ[𝓝 v] J (r+1) := by
    have hcv : ContinuousAt (fun w : ℝ × ℝ => w.2+η*w.1) v := by fun_prop
    have hn₀ : ∀ᶠ w : ℝ × ℝ in 𝓝 v, 0 < w.2 := continuousAt_snd (Ioi_mem_nhds hv)
    have hn₁ : ∀ᶠ w : ℝ × ℝ in 𝓝 v, 0 < w.2+η*w.1 := hcv (Ioi_mem_nhds hv')
    filter_upwards [hn₀,hn₁] with w hw hw'
    exact (positive_difference_curvature_directions F (σ:=σ) hw hw' hf r).2.1
  have hGe : G =ᶠ[𝓝 p] J 3 := hGerm 2 p hx0 hz0
  have hKe : K =ᶠ[𝓝 p] J 4 := by
    filter_upwards [hGe.fderiv (𝕜:=ℝ),hGerm 3 p hx0 hz0] with w hw hj
    change fderiv ℝ G w (0,1)=J 4 w
    rw [hw]
    exact hj
  have hYe (r : ℕ) : fderiv ℝ (J r) p (1,0)=Y r p := by
    rw [(positive_difference_curvature_directions F (σ:=σ) hx0 hz0 hf r).2.2]
    dsimp only [Y,p]
    field_simp
  have hD (r : ℕ) : D r=J r p := by
    have hc₀ : ContDiffAt ℝ r F (ρ z₀) :=
      (hf _ hx0).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl r)
    have hc₁ : ContDiffAt ℝ r (fun x => F (x+η*z.1)) (ρ z₀) :=
      ((hf _ hz0).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl r)).comp
        (ρ z₀) (contDiffAt_id.add contDiffAt_const)
    dsimp only [D]
    rw [iteratedDeriv_div_const,iteratedDeriv_fun_sub hc₀ hc₁,iteratedDeriv_comp_add_const]
  have hB (r : ℕ) : B r=Y r p := by
    have he := positive_difference_mixed_derivative F hσ.ne' hη hx0 hy0 hf r 1
      (by norm_num)
    simp only [iteratedDeriv_one,Nat.sub_self,pow_zero] at he
    change B r= -(1/σ)*iteratedDeriv (r+1) F (ρ z₀+η*z.1) at he
    rw [he]
    dsimp only [Y,p]
    ring
  have hG0 : G p ≠ 0 := by
    have hh := (positive_jets_difference_curvature_entry F hσ hc hU hη hηmax
      hx hy' hf hbound htests 3 (by norm_num) (by norm_num)).2.2.2.1
    exact abs_pos.mp (lt_of_lt_of_le (by positivity) hh)
  have hH : ContDiffAt ℝ 3 H p :=
    (positive_difference_curvature_directions F (σ:=σ) hx0 hz0 hf 2).1.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hjac := curvature_surface_reciprocal_profile_jacobian H ρ hz hI hbase hH hG0
    hroot huniq
  change (fderiv ℝ Φ z (1,0)).1*(fderiv ℝ Φ z (0,1)).2-
    (fderiv ℝ Φ z (0,1)).1*(fderiv ℝ Φ z (1,0)).2 =
    TaoTrudgianYang2025.HuxleyModel.caseTwoTests
      ![H p,G p,K p,fderiv ℝ K p (0,1),
        fderiv ℝ H p (1,0),fderiv ℝ G p (1,0),fderiv ℝ K p (1,0)] 1 /
      ((H p)^4*(G p)^2) at hjac
  have hnum : d ≤ |TaoTrudgianYang2025.HuxleyModel.caseTwoTests
      ![H p,G p,K p,fderiv ℝ K p (0,1),
        fderiv ℝ H p (1,0),fderiv ℝ G p (1,0),fderiv ℝ K p (1,0)] 1| := by
    have he := hcase F hf hbound htests η hη hηsmall (ρ z₀) hx z.1 hy 1
    change d ≤ |TaoTrudgianYang2025.HuxleyModel.caseTwoTests
      ![D 2,D 3,D 4,D 5,B 2,B 3,B 4] 1| at he
    have hL : fderiv ℝ (J 4) p (0,1)=J 5 p := (hGerm 4 p hx0 hz0).self_of_nhds
    rw [hGe.self_of_nhds,hKe.self_of_nhds,hKe.fderiv_eq,hGe.fderiv_eq,
      hL,hYe 4,hYe 3]
    change d ≤ |TaoTrudgianYang2025.HuxleyModel.caseTwoTests
      ![J 2 p,J 3 p,J 4 p,J 5 p,fderiv ℝ (J 2) p (1,0),Y 3 p,Y 4 p] 1|
    rw [hYe 2]
    simpa only [hD,hB] using he
  have hJbound (r : ℕ) (hr : r ≤ 5) : |J r p| ≤ R := by
    rw [←hD r]
    have hh := positive_jets_difference_mixed_upper F hσ hU hη hηmax hx hy'
      hf hbound r 0 (by norm_num) (by omega)
    have hAR : 3*U/σ ≤ R := (le_max_left _ _).trans (le_max_right _ _)
    exact (show |D r| ≤ 3*U/σ from by simpa only [iteratedDeriv_zero] using hh).trans hAR
  have hHbound : |H p| ≤ R := hJbound 2 (by norm_num)
  have hGbound : |G p| ≤ R := hGe.self_of_nhds ▸ hJbound 3 (by norm_num)
  have hlevel : H p=z.2⁻¹ := hroot.self_of_nhds.2
  have hH0 : H p ≠ 0 := by rw [hlevel]; exact inv_ne_zero hz
  have hden : 0 < |(H p)^4*(G p)^2| := abs_pos.mpr (mul_ne_zero (pow_ne_zero _ hH0) (pow_ne_zero _ hG0))
  have hdenbound : |(H p)^4*(G p)^2| ≤ R^6 := by
    rw [abs_mul,abs_pow,abs_pow]
    calc
      _ ≤ R^4*R^2 := mul_le_mul
        (pow_le_pow_left₀ (abs_nonneg _) hHbound 4)
        (pow_le_pow_left₀ (abs_nonneg _) hGbound 2)
        (by positivity) (by positivity)
      _ = _ := by ring
  rw [hjac,abs_div]
  exact (div_le_div_of_nonneg_left hd.le hden hdenbound).trans
    (div_le_div_of_nonneg_right hnum hden.le)


                                                                         
                                                                            
theorem reciprocal_coordinate_local_bound {A a u : ℝ}
    (hA : 0 < A) (ha : a ≠ 0) (haA : |a| ≤ A)
    (hu : |u-a⁻¹| < 1/(2*A)) :
    u ≠ 0 ∧ |u⁻¹-a| ≤ 2*A^2*|u-a⁻¹| := by
  have haabs : 0 < |a| := abs_pos.mpr ha
  have hinv : 1/A ≤ |a⁻¹| := by
    rw [abs_inv,←one_div]
    exact one_div_le_one_div_of_le haabs haA
  have htri : |a⁻¹| ≤ |u-a⁻¹|+|u| := by
    calc
      _ = |u-(u-a⁻¹)| := by ring_nf
      _ ≤ |u|+|u-a⁻¹| := abs_sub _ _
      _ = _ := add_comm _ _
  have huabs : 1/(2*A) < |u| := by
    have he : 1/A=2*(1/(2*A)) := by field_simp
    linarith only [hinv,htri,hu,he]
  have hu0 : u ≠ 0 := abs_pos.mp (lt_trans (by positivity) huabs)
  have huinv : |u⁻¹| ≤ 2*A := by
    rw [abs_inv,←one_div]
    calc
      _ ≤ 1/(1/(2*A)) := one_div_le_one_div_of_le (by positivity) huabs.le
      _ = _ := by field_simp
  refine ⟨hu0,?_⟩
  have he : u⁻¹-a= -a*u⁻¹*(u-a⁻¹) := by field_simp; ring
  rw [he,abs_mul,abs_mul,abs_neg]
  calc
    _ ≤ A*(2*A)*|u-a⁻¹| :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul haA huinv (abs_nonneg _) hA.le) (abs_nonneg _)
    _ = _ := by ring

                                                                         
                                                                           
                                                              
theorem positive_difference_uniform_reciprocal_root_chart
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ s : ℝ, 0 < s ∧
      ∀ (F : ℝ → ℝ) (η x₀ y₀ : ℝ),
      0 < η → η ≤ 1/8 → x₀ ∈ Icc (1:ℝ) 2 → y₀ ∈ Icc (1:ℝ) 2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let ρ := fun w : ℝ × ℝ =>
        Function.invFunOn (fun x => H (w.1,x)) (Ioo (3/4:ℝ) (9/4)) w.2
      ∀ w : ℝ × ℝ, ‖w-(y₀,(H (y₀,x₀))⁻¹)‖ < s →
        w.2 ≠ 0 ∧ ρ (w.1,w.2⁻¹) ∈ Ioo (3/4:ℝ) (9/4) ∧
        w.1 ∈ Icc (1/2:ℝ) 3 ∧ H (w.1,ρ (w.1,w.2⁻¹))=w.2⁻¹ ∧
        (∀ᶠ v in 𝓝 (w.1,w.2⁻¹), ρ v ∈ Ioo (3/4:ℝ) (9/4) ∧
          H (v.1,ρ v)=v.2) ∧
        (∀ᶠ v in 𝓝 (w.1,w.2⁻¹), Set.InjOn
          (fun x => H (v.1,x)) (Ioo (3/4:ℝ) (9/4))) := by
  obtain ⟨r,hr,hchart⟩ := positive_difference_uniform_root_chart hσ hc hU
  let A := 3*U/σ
  have hA : 0 < A := by dsimp only [A]; positivity
  let s := min r (min (1/(2*A)) (r/(2*A^2)))
  have hs : 0 < s := by dsimp only [s]; positivity
  refine ⟨s,hs,?_⟩
  intro F η x₀ y₀ hη hηmax hx₀ hy₀ hf hbound htests H ρ w hw
  have hx : x₀ ∈ Icc (3/4:ℝ) (9/4) :=
    ⟨by linarith only [hx₀.1],by linarith only [hx₀.2]⟩
  have hy : y₀ ∈ Icc (1/2:ℝ) 3 :=
    ⟨by linarith only [hy₀.1],by linarith only [hy₀.2]⟩
  have he : iteratedDeriv 2 (fun u => (F u-F (u+η*y₀))/(σ*η)) x₀=H (y₀,x₀) :=
    (positive_jets_difference_curvature_entry F hσ hc hU hη hηmax
      hx hy hf hbound htests 3 (by norm_num) (by norm_num)).1
  have hHA : |H (y₀,x₀)| ≤ A := by
    rw [←he]
    simpa only [iteratedDeriv_zero] using
      positive_jets_difference_mixed_upper F hσ hU hη hηmax hx hy hf hbound
        2 0 (by norm_num) (by norm_num)
  have hH0 : H (y₀,x₀) ≠ 0 := by
    have hh := positive_jets_difference_spatial_lower F hσ hc hη hηmax
      hx hy hf htests 2 (by norm_num) (by norm_num)
    rw [he] at hh
    exact abs_pos.mp (lt_of_lt_of_le (by positivity) hh)
  have hwy : |w.1-y₀| < s := (norm_fst_le (w-(y₀,(H (y₀,x₀))⁻¹))).trans_lt hw
  have hwu : |w.2-(H (y₀,x₀))⁻¹| < s :=
    (norm_snd_le (w-(y₀,(H (y₀,x₀))⁻¹))).trans_lt hw
  have hs₁ : s ≤ 1/(2*A) := (min_le_right _ _).trans (min_le_left _ _)
  have hs₂ : s ≤ r/(2*A^2) := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨hw0,hinv⟩ := reciprocal_coordinate_local_bound hA hH0 hHA (hwu.trans_le hs₁)
  have hnear : ‖(w.1,w.2⁻¹)-(y₀,H (y₀,x₀))‖ < r := by
    change max |w.1-y₀| |w.2⁻¹-H (y₀,x₀)| < r
    apply max_lt (hwy.trans_le (min_le_left _ _))
    calc
      _ ≤ 2*A^2*|w.2-(H (y₀,x₀))⁻¹| := hinv
      _ < 2*A^2*s := mul_lt_mul_of_pos_left hwu (by positivity)
      _ ≤ 2*A^2*(r/(2*A^2)) := mul_le_mul_of_nonneg_left hs₂ (by positivity)
      _ = r := by field_simp
  have hcov := hchart F η x₀ y₀ hη hηmax hx₀ hy₀ hf hbound htests
  have hb := hcov (w.1,w.2⁻¹) hnear
  refine ⟨hw0,hb.1,hb.2.1,hb.2.2.1,?_,?_⟩
  · have hn : Metric.ball (y₀,H (y₀,x₀)) r ∈ 𝓝 (w.1,w.2⁻¹) :=
      Metric.isOpen_ball.mem_nhds (by simpa only [Metric.mem_ball,dist_eq_norm] using hnear)
    filter_upwards [hn] with v hv
    have hv' : ‖v-(y₀,H (y₀,x₀))‖ < r := by
      simpa only [Metric.mem_ball,dist_eq_norm] using hv
    exact ⟨(hcov v hv').1,(hcov v hv').2.2.1⟩
  · have hn : Metric.ball (y₀,H (y₀,x₀)) r ∈ 𝓝 (w.1,w.2⁻¹) :=
      Metric.isOpen_ball.mem_nhds (by simpa only [Metric.mem_ball,dist_eq_norm] using hnear)
    filter_upwards [hn] with v hv
    exact (hcov v (by simpa only [Metric.mem_ball,dist_eq_norm] using hv)).2.2.2


                                                                           
                                                                      
                                                                        
theorem positive_difference_constructed_reciprocal_profile
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ η₀ κ s : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < κ ∧ 0 < s ∧
      ∀ (F : ℝ → ℝ) (η x₀ y₀ : ℝ),
      0 < η → η ≤ η₀ → x₀ ∈ Icc (1:ℝ) 2 → y₀ ∈ Icc (1:ℝ) 2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let ρ := fun w : ℝ × ℝ =>
        Function.invFunOn (fun x => H (w.1,x)) (Ioo (3/4:ℝ) (9/4)) w.2
      let g := fun w => fderiv ℝ H (w.1,ρ w) (0,1)
      let k := fun w : ℝ × ℝ => w.2^3*g (w.1,w.2⁻¹)
      let Φ := fun w => (k w,fderiv ℝ k w (0,1))
      ∀ z : ℝ × ℝ, ‖z-(y₀,(H (y₀,x₀))⁻¹)‖ < s →
        z.1 ∈ Icc (1:ℝ) 2 →
        ContDiffAt ℝ 2 k z ∧
        κ ≤ |(fderiv ℝ Φ z (1,0)).1*(fderiv ℝ Φ z (0,1)).2-
          (fderiv ℝ Φ z (0,1)).1*(fderiv ℝ Φ z (1,0)).2| := by
  obtain ⟨η₀,κ,hη₀,hηcap,hκ,hjac⟩ := positive_difference_reciprocal_profile_jacobian_lower hσ hc hU
  obtain ⟨s,hs,hchart⟩ := positive_difference_uniform_reciprocal_root_chart hσ hc hU
  refine ⟨η₀,κ,s,hη₀,hηcap,hκ,hs,?_⟩
  intro F η x₀ y₀ hη hηsmall hx₀ hy₀ hf hbound htests H ρ g k Φ z hz hy
  have hηmax := hηsmall.trans hηcap
  obtain ⟨hz0,hx,hy',hlevel,hroot,huniq⟩ :=
    hchart F η x₀ y₀ hη hηmax hx₀ hy₀ hf hbound htests z hz
  have hx' : ρ (z.1,z.2⁻¹) ∈ Icc (3/4:ℝ) (9/4) := ⟨hx.1.le,hx.2.le⟩
  refine ⟨?_,hjac F ρ η z (Ioo (3/4:ℝ) (9/4)) hη hηsmall hz0 hx' hy
    hf hbound htests isOpen_Ioo hx hroot huniq⟩
  let z₀ : ℝ × ℝ := (z.1,z.2⁻¹)
  let p : ℝ × ℝ := (z.1,ρ z₀)
  let G := fun v => fderiv ℝ H v (0,1)
  have hp : 0 < ρ z₀ := by change 0 < ρ (z.1,z.2⁻¹); linarith only [hx.1]
  have hyp : 0 < z.1 := zero_lt_one.trans_le hy.1
  have hH : ContDiffAt ℝ 3 H p :=
    (positive_difference_curvature_directions F (σ:=σ) hp (add_pos hp (mul_pos hη hyp)) hf 2).1.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hG0 : G p ≠ 0 := by
    have hh := (positive_jets_difference_curvature_entry F hσ hc hU hη hηmax
      hx' hy' hf hbound htests 3 (by norm_num) (by norm_num)).2.2.2.1
    exact abs_pos.mp (lt_of_lt_of_le (by positivity) hh)
  have hρ : ContDiffAt ℝ 3 ρ z₀ := curvature_surface_root_contDiffAt H ρ
    (by norm_num) isOpen_Ioo hx hH hG0 hroot huniq
  have hG : ContDiffAt ℝ 2 G p :=
    (hH.fderiv_right (by norm_num : (2:WithTop ℕ∞)+1 ≤ 3)).clm_apply contDiffAt_const
  have hg : ContDiffAt ℝ 2 g z₀ :=
    hG.comp z₀ (contDiffAt_fst.prodMk (hρ.of_le (by norm_num)))
  exact (contDiffAt_snd.pow 3).mul
    (hg.comp z (contDiffAt_fst.prodMk (contDiffAt_snd.inv hz0)))

                                                                      
                                                       
def reciprocalProfileColumns (v : (Fin 7 → ℝ) × ℝ × ℝ) :
    (ℝ × ℝ) × (ℝ × ℝ) :=
  let w := v.1
  let u := v.2.1
  let t := v.2.2
  let C := profileDerivativeColumns w
  ((u^3*C.1.1,3*u^2*C.1.1-u*C.1.2),
   (3*u^2*w 1-u*(w 2*w 6),6*u*w 1-4*(w 2*w 6)+t*C.2.2))

theorem contDiff_reciprocalProfileColumns : ContDiff ℝ ∞ reciprocalProfileColumns := by
  unfold reciprocalProfileColumns profileDerivativeColumns
  fun_prop

theorem reciprocalProfileColumns_uniform_bound (R : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ v : (Fin 7 → ℝ) × ℝ × ℝ, ‖v‖ ≤ R →
      ‖reciprocalProfileColumns v‖ ≤ D ∧
      ‖fderiv ℝ reciprocalProfileColumns v‖ ≤ D := by
  obtain ⟨D₀,h₀⟩ := (isCompact_closedBall (0 : (Fin 7 → ℝ) × ℝ × ℝ) R).exists_bound_of_continuousOn
    contDiff_reciprocalProfileColumns.continuous.continuousOn
  obtain ⟨D₁,h₁⟩ := (isCompact_closedBall (0 : (Fin 7 → ℝ) × ℝ × ℝ) R).exists_bound_of_continuousOn
    (contDiff_reciprocalProfileColumns.continuous_fderiv (by simp)).continuousOn
  refine ⟨max 1 (max D₀ D₁),lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro v hv
  have hm : v ∈ Metric.closedBall 0 R := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hv
  exact ⟨(h₀ v hm).trans ((le_max_left _ _).trans (le_max_right _ _)),
    (h₁ v hm).trans ((le_max_right _ _).trans (le_max_right _ _))⟩


                                                                    
                                                                         
theorem positive_difference_reciprocal_profile_chart_bound
    (F : ℝ → ℝ) (ρ : ℝ × ℝ → ℝ)
    {σ c U η : ℝ} {z : ℝ × ℝ} {I : Set ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hz : z.2 ≠ 0)
    (hx : ρ (z.1,z.2⁻¹) ∈ Icc (3/4:ℝ) (9/4)) (hy : z.1 ∈ Icc (1/2:ℝ) 3)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hI : IsOpen I) (hbase : ρ (z.1,z.2⁻¹) ∈ I)
    (hroot : ∀ᶠ w in 𝓝 (z.1,z.2⁻¹), ρ w ∈ I ∧
      (iteratedDeriv 2 F (ρ w)-iteratedDeriv 2 F (ρ w+η*w.1))/(σ*η)=w.2)
    (huniq : ∀ᶠ w in 𝓝 (z.1,z.2⁻¹), Set.InjOn
      (fun x => (iteratedDeriv 2 F x-iteratedDeriv 2 F (x+η*w.1))/(σ*η)) I) :
    let H := fun v : ℝ × ℝ =>
      (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
    let g := fun w => fderiv ℝ H (w.1,ρ w) (0,1)
    let k := fun w : ℝ × ℝ => w.2^3*g (w.1,w.2⁻¹)
    let Φ := fun w => (k w,fderiv ℝ k w (0,1))
    let W := fun w => differenceProfileJet F σ η (w.1,ρ w)
    let V := fun w : ℝ × ℝ => (W (w.1,w.2⁻¹),w.2,w.2⁻¹)
    let R := max 1 (max (3*U/σ) (2*σ/c))
    DifferentiableAt ℝ V z ∧ ‖V z‖ ≤ R ∧
    ‖fderiv ℝ V z‖ ≤ 6*R^7 ∧
    (fderiv ℝ Φ z (1,0),fderiv ℝ Φ z (0,1))=reciprocalProfileColumns (V z) := by
  intro H g k Φ W V R
  let z₀ : ℝ × ℝ := (z.1,z.2⁻¹)
  let p : ℝ × ℝ := (z.1,ρ z₀)
  let G := fun v => fderiv ℝ H v (0,1)
  let q := fun w => fderiv ℝ g w (0,1)
  let Φ₀ := fun w => (g w,q w)
  let ι := fun w : ℝ × ℝ => (w.1,w.2⁻¹)
  have hR : 1 ≤ R := le_max_left _ _
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hR2 : 1 ≤ R^2 := one_le_pow₀ hR
  have hR7 : R^2 ≤ 6*R^7 := by
    have he : R^2 ≤ R^7 := pow_le_pow_right₀ hR (by norm_num)
    nlinarith only [he,pow_nonneg hRp.le 7]
  have hAR : 3*U/σ ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hIR : 2*σ/c ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨hW,hWsize,hWder,hfactor⟩ := positive_difference_profile_chart_bound F ρ
    hσ hc hU hη hηmax hx hy hf hbound htests hI hbase hroot huniq
  change DifferentiableAt ℝ W z₀ at hW
  change ∀ i, |W z₀ i| ≤ R at hWsize
  change ‖fderiv ℝ W z₀‖ ≤ 6*R^5 at hWder
  change (fderiv ℝ Φ₀ z₀ (1,0),fderiv ℝ Φ₀ z₀ (0,1))=
    profileDerivativeColumns (W z₀) at hfactor
  have hentry := positive_jets_difference_curvature_entry F hσ hc hU hη hηmax
    hx hy hf hbound htests 3 (by norm_num) (by norm_num)
  have hlevel : H p=z.2⁻¹ := hroot.self_of_nhds.2
  have hHupper : |H p| ≤ R := by
    have he := hentry.1
    change iteratedDeriv 2 (fun u => (F u-F (u+η*z.1))/(σ*η)) (ρ z₀)=H p at he
    rw [←he]
    have hh := positive_jets_difference_mixed_upper F hσ hU hη hηmax hx hy hf hbound
      2 0 (by norm_num) (by norm_num)
    exact (show |iteratedDeriv 2 (fun u => (F u-F (u+η*z.1))/(σ*η)) (ρ z₀)| ≤
      3*U/σ from by simpa only [iteratedDeriv_zero] using hh).trans hAR
  have hHlower : c/(2*σ) ≤ |H p| := by
    have hh := positive_jets_difference_spatial_lower F hσ hc hη hηmax
      hx hy hf htests 2 (by norm_num) (by norm_num)
    have he := hentry.1
    change iteratedDeriv 2 (fun u => (F u-F (u+η*z.1))/(σ*η)) (ρ z₀)=H p at he
    rw [he] at hh
    exact hh
  have hZu : |z.2⁻¹| ≤ R := hlevel ▸ hHupper
  have hZ : |z.2| ≤ R := by
    calc
      _ = 1/|H p| := by rw [hlevel,abs_inv,one_div,inv_inv]
      _ ≤ 1/(c/(2*σ)) := one_div_le_one_div_of_le (by positivity) hHlower
      _ = 2*σ/c := by field_simp
      _ ≤ R := hIR
  have hi : HasFDerivAt ι
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (-(z.2^2)⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ)) z :=
    hasFDerivAt_fst.prodMk ((hasDerivAt_inv hz).comp_hasFDerivAt z hasFDerivAt_snd)
  have hinv := (hasDerivAt_inv hz).comp_hasFDerivAt z
    (hasFDerivAt_snd (𝕜:=ℝ) (p:=z))
  change HasFDerivAt (fun w : ℝ × ℝ => w.2⁻¹) _ z at hinv
  have hinvnorm : ‖fderiv ℝ (fun w : ℝ × ℝ => w.2⁻¹) z‖ ≤ R^2 := by
    rw [hinv.fderiv,norm_smul,Real.norm_eq_abs,abs_neg,abs_inv,abs_pow,←inv_pow]
    apply (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_snd_le ..) (by positivity)).trans
    simpa only [mul_one,←abs_inv] using pow_le_pow_left₀ (abs_nonneg _) hZu 2
  have hinorm : ‖fderiv ℝ ι z‖ ≤ R^2 := by
    rw [hi.fderiv,ContinuousLinearMap.opNorm_prod,Prod.norm_def]
    apply max_le ((ContinuousLinearMap.norm_fst_le ..).trans hR2)
    rw [←hinv.fderiv]
    exact hinvnorm
  have hcomp := hW.hasFDerivAt.comp z hi.differentiableAt.hasFDerivAt
  have hcompnorm : ‖(fderiv ℝ W z₀).comp (fderiv ℝ ι z)‖ ≤ 6*R^7 := by
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    have hh := mul_le_mul hWder hinorm (norm_nonneg _) (by positivity : 0 ≤ 6*R^5)
    convert hh using 1
    ring
  have hv := hcomp.prodMk (hasFDerivAt_snd.prodMk hinv.differentiableAt.hasFDerivAt)
  change HasFDerivAt V _ z at hv
  refine ⟨hv.differentiableAt,?_,?_,?_⟩
  · change max ‖W z₀‖ (max |z.2| |z.2⁻¹|) ≤ R
    exact max_le ((pi_norm_le_iff_of_nonneg hRp.le).mpr hWsize) (max_le hZ hZu)
  · rw [hv.fderiv,ContinuousLinearMap.opNorm_prod,Prod.norm_def]
    apply max_le hcompnorm
    rw [ContinuousLinearMap.opNorm_prod,Prod.norm_def]
    exact max_le ((ContinuousLinearMap.norm_snd_le ..).trans (hR2.trans hR7))
      (hinvnorm.trans hR7)
  · have hp : 0 < ρ z₀ := by change 0 < ρ (z.1,z.2⁻¹); linarith only [hx.1]
    have hyp : 0 < z.1 := by linarith only [hy.1]
    have hH : ContDiffAt ℝ 3 H p :=
      (positive_difference_curvature_directions F (σ:=σ) hp (add_pos hp (mul_pos hη hyp)) hf 2).1.of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
    have hG0 : G p ≠ 0 := abs_pos.mp (lt_of_lt_of_le (by positivity) hentry.2.2.2.1)
    have hρ : ContDiffAt ℝ 3 ρ z₀ := curvature_surface_root_contDiffAt H ρ
      (by norm_num) hI hbase hH hG0 hroot huniq
    have hG : ContDiffAt ℝ 2 G p :=
      (hH.fderiv_right (by norm_num : (2:WithTop ℕ∞)+1 ≤ 3)).clm_apply contDiffAt_const
    have hg : ContDiffAt ℝ 2 g z₀ :=
      hG.comp z₀ (contDiffAt_fst.prodMk (hρ.of_le (by norm_num)))
    have hq : ContDiffAt ℝ 1 q z₀ :=
      (hg.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1 ≤ 2)).clm_apply contDiffAt_const
    have hold : HasFDerivAt Φ₀ ((fderiv ℝ g z₀).prod (fderiv ℝ q z₀)) z₀ :=
      (hg.of_le (by norm_num : (1:WithTop ℕ∞) ≤ 2)).differentiableAt_one.hasFDerivAt.prodMk
        hq.differentiableAt_one.hasFDerivAt
    rw [hold.fderiv] at hfactor
    have hgy : fderiv ℝ g z₀ (1,0)=(profileDerivativeColumns (W z₀)).1.1 :=
      congrArg (fun v => v.1.1) hfactor
    have hgt : q z₀=W z₀ 2*W z₀ 6 :=
      congrArg (fun v => v.2.1) hfactor
    have hqY : fderiv ℝ q z₀ (1,0)=(profileDerivativeColumns (W z₀)).1.2 :=
      congrArg (fun v => v.1.2) hfactor
    have hqU : fderiv ℝ q z₀ (0,1)=(profileDerivativeColumns (W z₀)).2.2 :=
      congrArg (fun v => v.2.2) hfactor
    have hgval : g z₀=W z₀ 1 := hentry.2.2.1
    obtain ⟨h₁,h₂⟩ := reciprocal_profile_derivative_matrix g hz hg
    change fderiv ℝ Φ z (1,0)=_ at h₁
    change fderiv ℝ Φ z (0,1)=_ at h₂
    rw [h₁,h₂]
    change ((z.2^3*fderiv ℝ g z₀ (1,0),
        3*z.2^2*fderiv ℝ g z₀ (1,0)-z.2*fderiv ℝ q z₀ (1,0)),
      (3*z.2^2*g z₀-z.2*q z₀,6*z.2*g z₀-4*q z₀+fderiv ℝ q z₀ (0,1)/z.2))=_
    rw [hgy,hgt,hqY,hqU,hgval]
    change ((z.2^3*(profileDerivativeColumns (W z₀)).1.1,
        3*z.2^2*(profileDerivativeColumns (W z₀)).1.1-z.2*(profileDerivativeColumns (W z₀)).1.2),
      (3*z.2^2*W z₀ 1-z.2*(W z₀ 2*W z₀ 6),
        6*z.2*W z₀ 1-4*(W z₀ 2*W z₀ 6)+(profileDerivativeColumns (W z₀)).2.2/z.2))=
      ((z.2^3*(profileDerivativeColumns (W z₀)).1.1,
        3*z.2^2*(profileDerivativeColumns (W z₀)).1.1-z.2*(profileDerivativeColumns (W z₀)).1.2),
      (3*z.2^2*W z₀ 1-z.2*(W z₀ 2*W z₀ 6),
        6*z.2*W z₀ 1-4*(W z₀ 2*W z₀ 6)+z.2⁻¹*(profileDerivativeColumns (W z₀)).2.2))
    rw [div_eq_mul_inv,mul_comm (profileDerivativeColumns (W z₀)).2.2 z.2⁻¹]


                                                                       
                                                                         
                                                                   
theorem positive_difference_reciprocal_profile_uniform_variation
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ D L : ℝ, 0 < D ∧ 0 < L ∧
      ∀ (F : ℝ → ℝ) (ρ : ℝ × ℝ → ℝ) (η : ℝ)
        (I : Set ℝ) (S : Set (ℝ × ℝ)),
      0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      IsOpen I → Convex ℝ S →
      (∀ w ∈ S, w.2 ≠ 0 ∧ ρ (w.1,w.2⁻¹) ∈ Icc (3/4:ℝ) (9/4) ∧
        w.1 ∈ Icc (1/2:ℝ) 3) →
      (∀ z ∈ S, ∀ᶠ w in 𝓝 (z.1,z.2⁻¹), ρ w ∈ I ∧
        (iteratedDeriv 2 F (ρ w)-iteratedDeriv 2 F (ρ w+η*w.1))/(σ*η)=w.2) →
      (∀ z ∈ S, ∀ᶠ w in 𝓝 (z.1,z.2⁻¹), Set.InjOn
        (fun x => (iteratedDeriv 2 F x-iteratedDeriv 2 F (x+η*w.1))/(σ*η)) I) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let g := fun w => fderiv ℝ H (w.1,ρ w) (0,1)
      let k := fun w : ℝ × ℝ => w.2^3*g (w.1,w.2⁻¹)
      let Φ := fun w => (k w,fderiv ℝ k w (0,1))
      (∀ w ∈ S, ‖fderiv ℝ Φ w (1,0)‖ ≤ D ∧ ‖fderiv ℝ Φ w (0,1)‖ ≤ D) ∧
      ∀ p ∈ S, ∀ q ∈ S, ‖fderiv ℝ Φ q-fderiv ℝ Φ p‖ ≤ L*‖q-p‖ := by
  let R := max 1 (max (3*U/σ) (2*σ/c))
  have hR : 0 < R := zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨D,hD,hpoly⟩ := reciprocalProfileColumns_uniform_bound R
  refine ⟨D,12*D*R^7,hD,by positivity,?_⟩
  intro F ρ η I S hη hηmax hf hbound htests hI hS hrange hroot huniq H g k Φ
  let W := fun w => differenceProfileJet F σ η (w.1,ρ w)
  let V := fun w : ℝ × ℝ => (W (w.1,w.2⁻¹),w.2,w.2⁻¹)
  have hjet w (hw : w ∈ S) :
      DifferentiableAt ℝ V w ∧ ‖V w‖ ≤ R ∧ ‖fderiv ℝ V w‖ ≤ 6*R^7 ∧
      (fderiv ℝ Φ w (1,0),fderiv ℝ Φ w (0,1))=reciprocalProfileColumns (V w) :=
    positive_difference_reciprocal_profile_chart_bound F ρ hσ hc hU hη hηmax
      (hrange w hw).1 (hrange w hw).2.1 (hrange w hw).2.2 hf hbound htests hI
      (hroot w hw).self_of_nhds.1 (hroot w hw) (huniq w hw)
  constructor
  · intro w hw
    have hh := (hpoly (V w) (hjet w hw).2.1).1
    rw [←(hjet w hw).2.2.2] at hh
    exact ⟨(norm_fst_le _).trans hh,(norm_snd_le _).trans hh⟩
  · intro p hp q hq
    have hd w (hw : w ∈ S) : HasFDerivAt (fun v => reciprocalProfileColumns (V v))
        ((fderiv ℝ reciprocalProfileColumns (V w)).comp (fderiv ℝ V w)) w :=
      (contDiff_reciprocalProfileColumns.differentiable (by simp)).differentiableAt.hasFDerivAt.comp
        w (hjet w hw).1.hasFDerivAt
    have hcol : ‖reciprocalProfileColumns (V q)-reciprocalProfileColumns (V p)‖ ≤
        D*(6*R^7)*‖q-p‖ := by
      apply hS.norm_image_sub_le_of_norm_fderiv_le (fun w hw => (hd w hw).differentiableAt)
        (fun w hw => ?_) hp hq
      rw [(hd w hw).fderiv]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (hpoly (V w) (hjet w hw).2.1).2 (hjet w hw).2.2.1
          (norm_nonneg _) hD.le)
    let A := fderiv ℝ Φ q-fderiv ℝ Φ p
    have he : (A (1,0),A (0,1))=
        reciprocalProfileColumns (V q)-reciprocalProfileColumns (V p) := by
      change (fderiv ℝ Φ q (1,0),fderiv ℝ Φ q (0,1))-
        (fderiv ℝ Φ p (1,0),fderiv ℝ Φ p (0,1))=_
      rw [(hjet q hq).2.2.2,(hjet p hp).2.2.2]
    have hb₁ : ‖A (1,0)‖ ≤ D*(6*R^7)*‖q-p‖ := by
      have hh := norm_fst_le (A (1,0),A (0,1))
      change ‖A (1,0)‖ ≤ ‖(A (1,0),A (0,1))‖ at hh
      rw [he] at hh
      exact hh.trans hcol
    have hb₂ : ‖A (0,1)‖ ≤ D*(6*R^7)*‖q-p‖ := by
      have hh := norm_snd_le (A (1,0),A (0,1))
      change ‖A (0,1)‖ ≤ ‖(A (1,0),A (0,1))‖ at hh
      rw [he] at hh
      exact hh.trans hcol
    have hA : ‖A‖ ≤ ‖A (1,0)‖+‖A (0,1)‖ := by
      apply A.opNorm_le_bound (by positivity)
      intro v
      have hv : v=v.1 • (1,0)+v.2 • (0,1) := by ext <;> simp
      calc
        ‖A v‖ = ‖v.1 • A (1,0)+v.2 • A (0,1)‖ := by
          conv_lhs => rw [hv,map_add,map_smul,map_smul]
        _ ≤ ‖v.1 • A (1,0)‖+‖v.2 • A (0,1)‖ := norm_add_le _ _
        _ = |v.1| *‖A (1,0)‖+|v.2| *‖A (0,1)‖ := by rw [norm_smul,norm_smul]; rfl
        _ ≤ ‖v‖ *‖A (1,0)‖+‖v‖ *‖A (0,1)‖ :=
          add_le_add (mul_le_mul_of_nonneg_right (norm_fst_le v) (norm_nonneg _))
            (mul_le_mul_of_nonneg_right (norm_snd_le v) (norm_nonneg _))
        _ = (‖A (1,0)‖+‖A (0,1)‖)*‖v‖ := by ring
    change ‖A‖ ≤ _
    nlinarith only [hA,hb₁,hb₂]


                                                                    
                                                                        
                                                   
theorem positive_difference_constructed_reciprocal_endpoint_compression
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ η₀ a C : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (η x₀ y₀ ya yb b l r δ : ℝ),
      0 < η → η ≤ η₀ → x₀ ∈ Icc (1:ℝ) 2 → y₀ ∈ Icc (1:ℝ) 2 →
      ya ∈ Icc (1:ℝ) 2 → yb ∈ Icc (1:ℝ) 2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let ρ := fun w : ℝ × ℝ =>
        Function.invFunOn (fun x => H (w.1,x)) (Ioo (3/4:ℝ) (9/4)) w.2
      let g := fun w => fderiv ℝ H (w.1,ρ w) (0,1)
      let k := fun w : ℝ × ℝ => w.2^3*g (w.1,w.2⁻¹)
      let z₀ := (y₀,(H (y₀,x₀))⁻¹)
      l < r → r-l ≤ 2 →
      (∀ t ∈ Icc l r, ‖((ya,t):ℝ × ℝ)-z₀‖ < a ∧ ‖((yb,t+b):ℝ × ℝ)-z₀‖ < a) →
      |k (yb,l+b)-k (ya,l)| ≤ δ → |k (yb,r+b)-k (ya,r)| ≤ δ →
      ‖((yb-ya,b):ℝ × ℝ)‖*(r-l) ≤ C*δ := by
  obtain ⟨η₀,κ,s₁,hη₀,hηcap,hκ,hs₁,hregular⟩ :=
    positive_difference_constructed_reciprocal_profile hσ hc hU
  obtain ⟨s₂,hs₂,hchart⟩ := positive_difference_uniform_reciprocal_root_chart hσ hc hU
  obtain ⟨D,L,hD,hL,hvariation⟩ := positive_difference_reciprocal_profile_uniform_variation hσ hc hU
  let a := min (min s₁ s₂) (κ/(16*D*L))
  have ha : 0 < a := by dsimp only [a]; positivity
  refine ⟨η₀,a,16*D/κ,hη₀,hηcap,ha,by positivity,?_⟩
  intro F η x₀ y₀ ya yb b l r δ hη hηsmall hx₀ hy₀ hya hyb hf hbound htests H ρ g k z₀
    hlr hlen hpoints hleft hright
  let I := Ioo (3/4:ℝ) (9/4)
  let S := Metric.ball z₀ a ∩ (Icc (1:ℝ) 2 ×ˢ (Set.univ : Set ℝ))
  let Φ := fun w => (k w,fderiv ℝ k w (0,1))
  have hηmax : η ≤ 1/8 := hηsmall.trans hηcap
  have hconv : Convex ℝ S :=
    (convex_ball z₀ a).inter ((convex_Icc (1:ℝ) 2).prod convex_univ)
  have hnear w (hw : w ∈ S) : ‖w-z₀‖ < a := by
    simpa only [S,Metric.mem_ball,dist_eq_norm] using hw.1
  have hrootdata w (hw : w ∈ S) :=
    hchart F η x₀ y₀ hη hηmax hx₀ hy₀ hf hbound htests w
      ((hnear w hw).trans_le ((min_le_left _ _).trans (min_le_right _ _)))
  have hrange w (hw : w ∈ S) :
      w.2 ≠ 0 ∧ ρ (w.1,w.2⁻¹) ∈ Icc (3/4:ℝ) (9/4) ∧ w.1 ∈ Icc (1/2:ℝ) 3 :=
    ⟨(hrootdata w hw).1,
      ⟨(hrootdata w hw).2.1.1.le,(hrootdata w hw).2.1.2.le⟩,
      (hrootdata w hw).2.2.1⟩
  have hroot w (hw : w ∈ S) :
      ∀ᶠ v in 𝓝 (w.1,w.2⁻¹), ρ v ∈ I ∧ H (v.1,ρ v)=v.2 :=
    (hrootdata w hw).2.2.2.2.1
  have huniq w (hw : w ∈ S) :
      ∀ᶠ v in 𝓝 (w.1,w.2⁻¹), Set.InjOn (fun x => H (v.1,x)) I :=
    (hrootdata w hw).2.2.2.2.2
  have hanalytic w (hw : w ∈ S) :=
    hregular F η x₀ y₀ hη hηsmall hx₀ hy₀ hf hbound htests w
      ((hnear w hw).trans_le ((min_le_left _ _).trans (min_le_left _ _))) hw.2.1
  obtain ⟨hcol,hvar⟩ := hvariation F ρ η I S hη hηmax hf hbound htests
    isOpen_Ioo hconv hrange hroot huniq
  have hv p (hp : p ∈ S) q (hq : q ∈ S) :
      ‖fderiv ℝ Φ q-fderiv ℝ Φ p‖ ≤ κ/(8*D) := by
    have hdist : ‖q-p‖ ≤ 2*a := by
      have he : q-p=(q-z₀)-(p-z₀) := by abel
      rw [he]
      exact (norm_sub_le _ _).trans (by linarith only [hnear p hp,hnear q hq])
    calc
      _ ≤ L*‖q-p‖ := hvar p hp q hq
      _ ≤ L*(2*a) := mul_le_mul_of_nonneg_left hdist hL.le
      _ ≤ L*(2*(κ/(16*D*L))) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)) hL.le
      _ = _ := by field_simp; ring
  have hsmall : 8*D*(κ/(8*D)) ≤ κ := by
    have he : 8*D*(κ/(8*D))=κ := by field_simp
    exact he.le
  have hpts t (ht : t ∈ Icc l r) : (ya,t) ∈ S ∧ (yb,t+b) ∈ S := by
    exact ⟨⟨by simpa only [S,Metric.mem_ball,dist_eq_norm] using (hpoints t ht).1,
        hya,Set.mem_univ _⟩,
      ⟨by simpa only [S,Metric.mem_ball,dist_eq_norm] using (hpoints t ht).2,
        hyb,Set.mem_univ _⟩⟩
  have hh := triangular_profile_endpoint_compression k hκ hD.le hsmall hlr hlen hconv
    (fun w hw => (hanalytic w hw).1) hpts hleft hright hv hcol
    (fun w hw => (hanalytic w hw).2)
  calc
    _ ≤ 16*D*δ/κ := (le_div_iff₀ hκ).mpr (by nlinarith only [hh])
    _ = _ := by ring


                                                                           
                                                                  
theorem positive_difference_rounded_weighted_third_bound
    (F : ℝ → ℝ) {σ c U η M xa xb ya yb Δ q : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hM : 2 ≤ M) (hxa : xa ∈ Icc (1:ℝ) 2) (hxb : xb ∈ Icc (1:ℝ) 2)
    (hya : ya ∈ Icc (1:ℝ) 2) (hyb : yb ∈ Icc (1:ℝ) 2)
    (hf : ∀ z, 0 < z → ContDiffAt ℝ ∞ F z)
    (hbound : ∀ z ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F z| ≤ U)
    (htests : ∀ z ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F z) j|)
    (hΔ : 0 ≤ Δ) :
    let G := fun v : ℝ × ℝ =>
      (iteratedDeriv 3 F v.2-iteratedDeriv 3 F (v.2+η*v.1))/(σ*η)
    let R := max 1 (max (3*U/σ) (2*σ/c))
    |G (yb,(round (M*xb):ℝ)/M)/G (ya,(round (M*xa):ℝ)/M)*q-1| ≤ Δ →
    |G (yb,xb)*q-G (ya,xa)| ≤ R*(Δ+(|q|+1)/(2*M)) := by
  intro G R hnear
  have hMpos : 0 < M := by linarith only [hM]
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let rd := fun x : ℝ => (round (M*x):ℝ)/M
  have hr x : |rd x-x| ≤ 1/(2*M) := by
    calc
      _ = |((round (M*x):ℝ)-M*x)/M| := by
        congr 1
        dsimp only [rd]
        field_simp
      _ = |(round (M*x):ℝ)-M*x|/M := by rw [abs_div,abs_of_pos hMpos]
      _ ≤ (1/2)/M := div_le_div_of_nonneg_right
        (by simpa only [abs_sub_comm] using abs_sub_round (M*x)) hMpos.le
      _ = _ := by ring
  have hquarter : 1/(2*M) ≤ (1/4:ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2*M)).mpr
    linarith only [hM]
  have hxext x (hx : x ∈ Icc (1:ℝ) 2) : x ∈ Icc (3/4:ℝ) (9/4) :=
    ⟨by linarith only [hx.1],by linarith only [hx.2]⟩
  have hrange x (hx : x ∈ Icc (1:ℝ) 2) : rd x ∈ Icc (3/4:ℝ) (9/4) := by
    have hb := abs_le.mp ((hr x).trans hquarter)
    constructor <;> linarith only [hb.1,hb.2,hx.1,hx.2]
  have hyext y (hy : y ∈ Icc (1:ℝ) 2) : y ∈ Icc (1/2:ℝ) 3 :=
    ⟨by linarith only [hy.1],by linarith only [hy.2]⟩
  have hjet x y (hx : x ∈ Icc (3/4:ℝ) (9/4)) (hy : y ∈ Icc (1:ℝ) 2) :
      ∀ i, |differenceProfileJet F σ η (y,x) i| ≤ R :=
    (positive_difference_profile_jet_bound F hσ hc hU hη hηmax hx (hyext y hy)
      hf hbound htests).2.1
  have hder x y (hx : x ∈ Icc (3/4:ℝ) (9/4)) (hy : y ∈ Icc (1:ℝ) 2) :
      HasDerivAt (fun z => G (y,z))
        ((iteratedDeriv 4 F x-iteratedDeriv 4 F (x+η*y))/(σ*η)) x := by
    have hx0 : 0 < x := by linarith only [hx.1]
    have hy0 : 0 < y := by linarith only [hy.1]
    have hj := positive_difference_curvature_directions F (σ:=σ) hx0
      (add_pos hx0 (mul_pos hη hy0)) hf 3
    have hd := (hj.1.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt x
      ((hasDerivAt_const x y).prodMk (hasDerivAt_id x))
    convert hd using 1
    · rfl
    simpa using hj.2.1.symm
  have herr x y (hx : x ∈ Icc (1:ℝ) 2) (hy : y ∈ Icc (1:ℝ) 2) :
      |G (y,x)-G (y,rd x)| ≤ R/(2*M) := by
    have hh : |G (y,x)-G (y,rd x)| ≤ R*|x-rd x| := by
      apply (convex_Icc (3/4:ℝ) (9/4)).norm_image_sub_le_of_norm_deriv_le
        (fun z hz => (hder z y hz hy).differentiableAt) (fun z hz => ?_)
        (hrange x hx) (hxext x hx)
      rw [(hder z y hz hy).deriv]
      exact hjet z y hz hy 2
    calc
      _ ≤ R*|x-rd x| := hh
      _ ≤ R*(1/(2*M)) := mul_le_mul_of_nonneg_left (by simpa only [abs_sub_comm] using hr x) hR.le
      _ = _ := by ring
  have hGa : G (ya,rd xa) ≠ 0 := by
    have hj := positive_jets_difference_curvature_entry F hσ hc hU hη hηmax
      (hrange xa hxa) (hyext ya hya) hf hbound htests 3 (by norm_num) (by norm_num)
    have hh := hj.2.2.2.1
    rw [hj.2.2.1] at hh
    exact abs_pos.mp (lt_of_lt_of_le (by positivity : 0 < c/(2*σ)) hh)
  have hcoinc : |G (yb,rd xb)*q-G (ya,rd xa)| ≤ R*Δ := by
    calc
      _ = |G (ya,rd xa)| * |G (yb,rd xb)/G (ya,rd xa)*q-1| := by
        rw [←abs_mul]
        congr 1
        field_simp
      _ ≤ |G (ya,rd xa)| * Δ := mul_le_mul_of_nonneg_left hnear (abs_nonneg _)
      _ ≤ R*Δ := mul_le_mul_of_nonneg_right (hjet (rd xa) ya (hrange xa hxa) hya 1) hΔ
  have he : G (yb,xb)*q-G (ya,xa)=
      (G (yb,xb)-G (yb,rd xb))*q+(G (yb,rd xb)*q-G (ya,rd xa))+
        (G (ya,rd xa)-G (ya,xa)) := by ring
  rw [he]
  calc
    _ ≤ |(G (yb,xb)-G (yb,rd xb))*q|+|G (yb,rd xb)*q-G (ya,rd xa)|+
        |G (ya,rd xa)-G (ya,xa)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (R/(2*M))*|q|+R*Δ+R/(2*M) := by
      rw [abs_mul,abs_sub_comm (G (ya,rd xa))]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right (herr xb yb hxb hyb) (abs_nonneg q)) hcoinc)
        (herr xa ya hxa hya)
    _ = _ := by ring


                                                                  
                                                                          
                                                                   
theorem positive_difference_rounded_reciprocal_profile_bound
    (F : ℝ → ℝ) {σ c U η M xa xb ya yb Δ : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hM : 2 ≤ M) (hxa : xa ∈ Icc (1:ℝ) 2) (hxb : xb ∈ Icc (1:ℝ) 2)
    (hya : ya ∈ Icc (1:ℝ) 2) (hyb : yb ∈ Icc (1:ℝ) 2)
    (hf : ∀ z, 0 < z → ContDiffAt ℝ ∞ F z)
    (hbound : ∀ z ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F z| ≤ U)
    (htests : ∀ z ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F z) j|)
    (hΔ : 0 ≤ Δ) :
    let H := fun v : ℝ × ℝ =>
      (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
    let G := fun v : ℝ × ℝ =>
      (iteratedDeriv 3 F v.2-iteratedDeriv 3 F (v.2+η*v.1))/(σ*η)
    let P := fun v => G v*((H v)⁻¹)^3
    let R := max 1 (max (3*U/σ) (2*σ/c))
    let q := (H (ya,xa)/H (yb,xb))^3
    |G (yb,(round (M*xb):ℝ)/M)/G (ya,(round (M*xa):ℝ)/M)*q-1| ≤ Δ →
    |P (yb,xb)-P (ya,xa)| ≤ R^10*(Δ+1/M) := by
  intro H G P R q hnear
  have hMpos : 0 < M := by linarith only [hM]
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR : 0 < R := zero_lt_one.trans_le hR1
  have hdata x y (hx : x ∈ Icc (1:ℝ) 2) (hy : y ∈ Icc (1:ℝ) 2) :
      |H (y,x)| ≤ R ∧ |(H (y,x))⁻¹| ≤ R ∧ H (y,x) ≠ 0 := by
    have hx' : x ∈ Icc (3/4:ℝ) (9/4) := ⟨by linarith only [hx.1],by linarith only [hx.2]⟩
    have hy' : y ∈ Icc (1/2:ℝ) 3 := ⟨by linarith only [hy.1],by linarith only [hy.2]⟩
    have he := (positive_jets_difference_curvature_entry F hσ hc hU hη hηmax
      hx' hy' hf hbound htests 3 (by norm_num) (by norm_num)).1
    change iteratedDeriv 2 (fun u => (F u-F (u+η*y))/(σ*η)) x=H (y,x) at he
    have hlo := positive_jets_difference_spatial_lower F hσ hc hη hηmax
      hx' hy' hf htests 2 (by norm_num) (by norm_num)
    rw [he] at hlo
    have hup := positive_jets_difference_mixed_upper F hσ hU hη hηmax
      hx' hy' hf hbound 2 0 (by norm_num) (by norm_num)
    simp only [iteratedDeriv_zero] at hup
    rw [he] at hup
    refine ⟨hup.trans ((le_max_left _ _).trans (le_max_right _ _)),?_,
      abs_pos.mp (lt_of_lt_of_le (by positivity) hlo)⟩
    rw [abs_inv,←one_div]
    calc
      _ ≤ 1/(c/(2*σ)) := one_div_le_one_div_of_le (by positivity) hlo
      _ = 2*σ/c := by field_simp
      _ ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  have ha := hdata xa ya hxa hya
  have hb := hdata xb yb hxb hyb
  have hq : |q| ≤ R^6 := by
    have hqbase : |H (ya,xa)| *|(H (yb,xb))⁻¹| ≤ R^2 := by
      convert mul_le_mul ha.1 hb.2.1 (abs_nonneg _) hR.le using 1
      ring
    calc
      _ = (|H (ya,xa)| *|(H (yb,xb))⁻¹|)^3 := by
        dsimp only [q]
        rw [abs_pow,abs_div,div_eq_mul_inv,abs_inv]
      _ ≤ (R^2)^3 := pow_le_pow_left₀ (by positivity) hqbase 3
      _ = _ := by ring
  have hweight := positive_difference_rounded_weighted_third_bound F hσ hc hU hη hηmax
    hM hxa hxb hya hyb hf hbound htests hΔ hnear
  change |G (yb,xb)*q-G (ya,xa)| ≤ R*(Δ+(|q|+1)/(2*M)) at hweight
  have hR6 : 1 ≤ R^6 := one_le_pow₀ hR1
  have hfrac : (|q|+1)/(2*M) ≤ R^6/M := by
    calc
      _ ≤ (2*R^6)/(2*M) :=
        div_le_div_of_nonneg_right (by linarith only [hq,hR6]) (by positivity)
      _ = _ := by ring
  have hΔR : Δ ≤ R^6*Δ := by nlinarith only [mul_le_mul_of_nonneg_right hR6 hΔ]
  have hw : |G (yb,xb)*q-G (ya,xa)| ≤ R^7*(Δ+1/M) := by
    calc
      _ ≤ R*(Δ+(|q|+1)/(2*M)) := hweight
      _ ≤ R*(R^6*Δ+R^6/M) := mul_le_mul_of_nonneg_left (add_le_add hΔR hfrac) hR.le
      _ = _ := by ring
  have he : P (yb,xb)-P (ya,xa)=(G (yb,xb)*q-G (ya,xa))*((H (ya,xa))⁻¹)^3 := by
    dsimp only [P,q]
    field_simp [ha.2.2,hb.2.2]
  rw [he,abs_mul,abs_pow]
  have hh := mul_le_mul hw (pow_le_pow_left₀ (abs_nonneg _) ha.2.1 3)
    (by positivity) (by positivity)
  convert hh using 1
  ring


                                                                      
                                                                         
                                                                      
theorem positive_difference_third_signed_lower
    (F : ℝ → ℝ) {σ c η x y : ℝ}
    (hσ : 0 < σ) (hη : 0 < η) (hηmax : η ≤ 1/8) (hc : 0 < c)
    (hx : x ∈ Icc (3/4:ℝ) (9/4)) (hy : y ∈ Icc (1/2:ℝ) 3)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) :
    c/(2*σ) ≤ (iteratedDeriv 3 F x-iteratedDeriv 3 F (x+η*y))/(σ*η) := by
  have hy0 : 0 < y := by linarith only [hy.1]
  have hp : 0 < η*y := mul_pos hη hy0
  have hxz : x < x+η*y := by linarith only [hp]
  have hI w (hw : w ∈ Icc x (x+η*y)) : w ∈ Icc (1/2:ℝ) 3 := by
    have hu := mul_le_mul hηmax hy.2 hy0.le (by norm_num : (0:ℝ) ≤ 1/8)
    constructor <;> linarith only [hx.1,hx.2,hw.1,hw.2,hu]
  have hd w (hw : w ∈ Icc x (x+η*y)) :
      HasDerivAt (iteratedDeriv 3 F) (iteratedDeriv 4 F w) w := by
    exact hasDerivAt_iteratedDeriv_finite (by norm_num : 3 < 4)
      ((hf w (by have hh := (hI w hw).1; linarith only [hh])).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4))
  obtain ⟨u,hu,he⟩ := exists_hasDerivAt_eq_slope (iteratedDeriv 3 F)
    (iteratedDeriv 4 F) hxz
    (fun w hw => (hd w hw).continuousAt.continuousWithinAt)
    (fun w hw => hd w ⟨hw.1.le,hw.2.le⟩)
  have hn := hnegative u (hI u ⟨hu.1.le,hu.2.le⟩)
  rw [he] at hn
  have hn' := (div_le_iff₀ (sub_pos.mpr hxz)).mp hn
  apply (le_div_iff₀ (mul_pos hσ hη)).mpr
  have heq : c/(2*σ)*(σ*η)=c*η/2 := by field_simp
  rw [heq]
  nlinarith only [hn',mul_le_mul_of_nonneg_left hy.1 (mul_pos hc hη).le]


                                                                  
                                                                   
                                                  
theorem positive_difference_local_parameter_count
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1/4 ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (η x₀ y₀ E J g : ℝ) (S : Finset ℝ) (x : ℝ → ℝ),
      0 < η → η ≤ 1/8 → x₀ ∈ Icc (1:ℝ) 2 → y₀ ∈ Icc (1:ℝ) 2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      0 ≤ E → 0 < J →
      (∀ y ∈ S, y ∈ Icc (1:ℝ) 2 ∧ |y-y₀| < a ∧ x y ∈ Icc (1:ℝ) 2) →
      (∀ y ∈ S, ∀ z ∈ S, y ≠ z → 1 ≤ J*|y-z|) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let G := fun v : ℝ × ℝ =>
        (iteratedDeriv 3 F v.2-iteratedDeriv 3 F (v.2+η*v.1))/(σ*η)
      (∀ y ∈ S, H (y,x y)=H (y₀,x₀)) →
      (∀ y ∈ S, |G (y,x y)-g| ≤ E) →
      (S.card:ℝ) ≤ 1+C*E*J := by
  obtain ⟨r,hr,hchart⟩ := positive_difference_uniform_root_chart hσ hc hU
  let a := min r (1/4:ℝ)
  let L := c/(2*σ)
  let K := c^2*c/(6*U^4)
  have ha : 0 < a := lt_min hr (by norm_num)
  have hL : 0 < L := by dsimp only [L]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨a,2/(L*K),ha,min_le_right _ _,by positivity,?_⟩
  intro F η x₀ y₀ E J g S x hη hηmax hx₀ hy₀ hf hbound htests hE hJ hpoints hsep
    H G hroot hres
  let ρ := fun y => Function.invFunOn (fun z => H (y,z)) (Ioo (3/4:ℝ) (9/4)) (H (y₀,x₀))
  have hywide y (hy : y ∈ Ioo (y₀-a) (y₀+a)) : y ∈ Icc (1/2:ℝ) 3 := by
    have hh : a ≤ 1/4 := min_le_right _ _
    constructor <;> linarith only [hy.1,hy.2,hy₀.1,hy₀.2,hh]
  have hdata y (hy : y ∈ Ioo (y₀-a) (y₀+a)) z (hz : z ∈ Ioo (3/4:ℝ) (9/4)) :
      ContDiffAt ℝ 2 H (y,z) ∧
      fderiv ℝ H (y,z) (0,1)=G (y,z) ∧
      L ≤ |fderiv ℝ H (y,z) (0,1)| ∧
      K ≤ |deriv (fun u => fderiv ℝ H (y,u) (1,0)/fderiv ℝ H (y,u) (0,1)) z| := by
    have hh := positive_jets_difference_curvature_entry F hσ hc hU hη hηmax
      ⟨hz.1.le,hz.2.le⟩ (hywide y hy) hf hbound htests 3 (by norm_num) (by norm_num)
    exact hh.2
  have hroots y (hy : y ∈ Ioo (y₀-a) (y₀+a)) :
      ρ y ∈ Ioo (3/4:ℝ) (9/4) ∧ H (y,ρ y)=H (y₀,x₀) := by
    have hdist : ‖((y,H (y₀,x₀)):ℝ × ℝ)-(y₀,H (y₀,x₀))‖ < r := by
      change max |y-y₀| |H (y₀,x₀)-H (y₀,x₀)| < r
      rw [sub_self,abs_zero,max_eq_left (abs_nonneg _)]
      exact (abs_lt.mpr ⟨by linarith only [hy.1],by linarith only [hy.2]⟩).trans_le
        (min_le_left r (1/4:ℝ))
    have hh := hchart F η x₀ y₀ hη hηmax hx₀ hy₀ hf hbound htests
      (y,H (y₀,x₀)) hdist
    exact ⟨hh.1,hh.2.2.1⟩
  have hS y (hy : y ∈ S) : y ∈ Ioo (y₀-a) (y₀+a) := by
    have hh := abs_lt.mp (hpoints y hy).2.1
    constructor <;> linarith only [hh.1,hh.2]
  have heq y (hy : y ∈ S) : ρ y=x y :=
    positive_difference_curvature_inverse_eq F hσ hc hU hη hηmax
      ⟨by linarith only [(hpoints y hy).2.2.1],by linarith only [(hpoints y hy).2.2.2]⟩
      ⟨by linarith only [(hpoints y hy).1.1],by linarith only [(hpoints y hy).1.2]⟩
      hf hbound htests (hroot y hy)
  have hres' y (hy : y ∈ S) : |fderiv ℝ H (y,ρ y) (0,1)-g| ≤ E := by
    rw [(hdata y (hS y hy) (ρ y) (hroots y (hS y hy)).1).2.1,heq y hy]
    exact hres y hy
  have hh := curvature_fiber_parameter_count S H ρ hL hK hE hJ hS hsep
    (fun y hy z hz => (hdata y hy z hz).1) hroots
    (fun y hy z hz => (hdata y hy z hz).2.2.1)
    (fun y hy z hz => (hdata y hy z hz).2.2.2) hres'
  convert hh using 1
  ring

                                                                   
                                                                       
                                                              
theorem positive_difference_parameter_count
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (η E J q g : ℝ) (S : Finset ℝ) (x : ℝ → ℝ),
      0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      0 ≤ E → 0 < J →
      (∀ y ∈ S, y ∈ Icc (1:ℝ) 2 ∧ x y ∈ Icc (1:ℝ) 2) →
      (∀ y ∈ S, ∀ z ∈ S, y ≠ z → 1 ≤ J*|y-z|) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let G := fun v : ℝ × ℝ =>
        (iteratedDeriv 3 F v.2-iteratedDeriv 3 F (v.2+η*v.1))/(σ*η)
      (∀ y ∈ S, H (y,x y)=q) →
      (∀ y ∈ S, |G (y,x y)-g| ≤ E) →
      (S.card:ℝ) ≤ K*(1+C*E*J) := by
  classical
  obtain ⟨a,C,ha,hacap,hC,hlocal⟩ := positive_difference_local_parameter_count hσ hc hU
  refine ⟨2+1/a,C,by positivity,hC,?_⟩
  intro F η E J q g S x hη hηmax hf hbound htests hE hJ hpoints hsep H G hroot hres
  let bin := fun y : ℝ => ⌊y/a⌋
  let I := S.image bin
  let B := 1+C*E*J
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hI : (I.card:ℝ) ≤ 2+1/a := by
    have hrange n (hn : n ∈ I) : 1/a-1 ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2/a := by
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hn
      have hlo := Int.floor_le (y/a)
      have hhi := Int.lt_floor_add_one (y/a)
      have hyl := div_le_div_of_nonneg_right (hpoints y hy).1.1 ha.le
      have hyu := div_le_div_of_nonneg_right (hpoints y hy).1.2 ha.le
      change (bin y:ℝ) ≤ y/a at hlo
      change y/a < (bin y:ℝ)+1 at hhi
      constructor <;> linarith only [hlo,hhi,hyl,hyu]
    have hh := integer_card_le_interval_length_add_one I
      (show 1/a-1 ≤ 2/a from (sub_le_self _ zero_le_one).trans
        (div_le_div_of_nonneg_right (by norm_num : (1:ℝ) ≤ 2) ha.le)) hrange
    calc
      _ ≤ 2/a-(1/a-1)+1 := hh
      _ = _ := by ring
  have hfiber n : ((S.filter (fun y => bin y=n)).card:ℝ) ≤ B := by
    let V := S.filter (fun y => bin y=n)
    rcases V.eq_empty_or_nonempty with hv | hv
    · change (V.card:ℝ) ≤ B
      rw [hv,Finset.card_empty,Nat.cast_zero]
      exact hB
    obtain ⟨y₀,hy₀⟩ := hv
    have hy₀S : y₀ ∈ S := (Finset.mem_filter.mp hy₀).1
    have hclose y (hy : y ∈ V) : |y-y₀| < a := by
      have hbin : bin y=bin y₀ := (Finset.mem_filter.mp hy).2.trans
        (Finset.mem_filter.mp hy₀).2.symm
      have hylo := Int.floor_le (y/a)
      have hyhi := Int.lt_floor_add_one (y/a)
      have h₀lo := Int.floor_le (y₀/a)
      have h₀hi := Int.lt_floor_add_one (y₀/a)
      change (bin y:ℝ) ≤ y/a at hylo
      change y/a < (bin y:ℝ)+1 at hyhi
      change (bin y₀:ℝ) ≤ y₀/a at h₀lo
      change y₀/a < (bin y₀:ℝ)+1 at h₀hi
      rw [hbin] at hylo hyhi
      have hl₁ := (le_div_iff₀ ha).mp hylo
      have hu₁ := (div_lt_iff₀ ha).mp hyhi
      have hl₂ := (le_div_iff₀ ha).mp h₀lo
      have hu₂ := (div_lt_iff₀ ha).mp h₀hi
      exact abs_lt.mpr ⟨by nlinarith only [hl₁,hu₂],by nlinarith only [hu₁,hl₂]⟩
    exact hlocal F η (x y₀) y₀ E J g V x hη hηmax (hpoints y₀ hy₀S).2
      (hpoints y₀ hy₀S).1 hf hbound htests hE hJ
      (fun y hy => ⟨(hpoints y (Finset.mem_filter.mp hy).1).1,hclose y hy,
        (hpoints y (Finset.mem_filter.mp hy).1).2⟩)
      (fun y hy z hz hyz => hsep y (Finset.mem_filter.mp hy).1 z
        (Finset.mem_filter.mp hz).1 hyz)
      (fun y hy => (hroot y (Finset.mem_filter.mp hy).1).trans (hroot y₀ hy₀S).symm)
      (fun y hy => hres y (Finset.mem_filter.mp hy).1)
  have hcard : (S.card:ℝ)=∑ n ∈ I, ((S.filter (fun y => bin y=n)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise
      (fun y hy => Finset.mem_image_of_mem bin hy)
  calc
    (S.card:ℝ) = _ := hcard
    _ ≤ ∑ _n ∈ I, B := Finset.sum_le_sum (fun n _ => hfiber n)
    _ = (I.card:ℝ)*B := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (2+1/a)*B := mul_le_mul_of_nonneg_right hI hB

                                                                      
                                                                     
                                                                           
theorem positive_difference_physical_parameter_count
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (η ya xa Δ J q t T M : ℝ) (S : Finset ℝ) (x : ℝ → ℝ),
      0 < η → η ≤ 1/8 → ya ∈ Icc (1:ℝ) 2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      0 < T → 2 ≤ M → 0 ≤ Δ → 0 < J → t ∈ Icc (1/2:ℝ) 2 →
      xa ∈ Icc M (2*M) →
      (∀ y ∈ S, y ∈ Icc (1:ℝ) 2 ∧ x y ∈ Icc M (2*M)) →
      (∀ y ∈ S, ∀ z ∈ S, y ≠ z → 1 ≤ J*|y-z|) →
      let f := fun y z => T*(F (z/M)-F (z/M+η*y))/(σ*η)
      let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
      (∀ y ∈ S, iteratedDeriv 2 (f y) (x y)/2=q) →
      (∀ y ∈ S, |μ y (x y)/μ ya xa*t^3-1| ≤ Δ) →
      let B := max 1 (max (3*U/σ) (2*σ/c))
      (S.card:ℝ) ≤ K*(1+8*C*B*(Δ+5/M)*J) := by
  obtain ⟨K,C,hK,hC,hcount⟩ := positive_difference_parameter_count hσ hc hU
  refine ⟨K,C,hK,hC,?_⟩
  intro F η ya xa Δ J q t T M S x hη hηmax hya hf hbound htests hT hM hΔ hJ ht
    hxa hpoints hsep f μ hmap hthird B
  have hMpos : 0 < M := by linarith only [hM]
  have htpos : 0 < t := by linarith only [ht.1]
  let H := fun v : ℝ × ℝ =>
    (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
  let G := fun v : ℝ × ℝ =>
    (iteratedDeriv 3 F v.2-iteratedDeriv 3 F (v.2+η*v.1))/(σ*η)
  let g := G (ya,xa/M)/t^3
  have hnorm z (hz : z ∈ Icc M (2*M)) : z/M ∈ Icc (1:ℝ) 2 :=
    ⟨(le_div_iff₀ hMpos).mpr (by simpa using hz.1),(div_le_iff₀ hMpos).mpr hz.2⟩
  have hd n z y (hz : 0 < z) (hy : y ∈ Icc (1:ℝ) 2) :
      iteratedDeriv n (f y) z =
        T/M^n*((iteratedDeriv n F (z/M)-iteratedDeriv n F (z/M+η*y))/(σ*η)) :=
    positive_difference_physical_iteratedDeriv F hMpos hz
      (mul_nonneg hη.le (by linarith only [hy.1])) hf n
  have hroots y (hy : y ∈ S) : H (y,x y/M)=2*M^2*q/T := by
    calc
      _ = (2*M^2/T)*(iteratedDeriv 2 (f y) (x y)/2) := by
        rw [hd 2 _ _ (hMpos.trans_le (hpoints y hy).2.1) (hpoints y hy).1]
        dsimp only [H]
        field_simp
      _ = _ := by rw [hmap y hy]; ring
  have hnear y (hy : y ∈ S) : |G (y,x y/M)-g| ≤ 8*B*(Δ+5/M) := by
    have hroundpos z (hz : z ∈ Icc M (2*M)) : (0:ℝ) < round z := by
      have hh := abs_le.mp (abs_sub_round z)
      linarith only [hh.2,hz.1,hM]
    have hμ y z (hy : y ∈ Icc (1:ℝ) 2) (hz : z ∈ Icc M (2*M)) :
        μ y z=(T/(6*M^3))*G (y,(round z:ℝ)/M) := by
      dsimp only [μ]
      rw [hd 3 _ _ (hroundpos z hz) hy]
      dsimp only [G]
      ring
    have hthird' :
        |G (y,(round (M*(x y/M)):ℝ)/M)/
          G (ya,(round (M*(xa/M)):ℝ)/M)*t^3-1| ≤ Δ := by
      have he z : M*(z/M)=z := mul_div_cancel₀ z hMpos.ne'
      rw [he,he]
      have hh := hthird y hy
      rw [hμ y _ (hpoints y hy).1 (hpoints y hy).2,hμ ya _ hya hxa,
        mul_div_mul_left _ _ (show T/(6*M^3) ≠ 0 by positivity)] at hh
      exact hh
    have hh := positive_difference_rounded_weighted_third_bound F hσ hc hU hη hηmax
      hM (hnorm _ hxa) (hnorm _ (hpoints y hy).2) hya (hpoints y hy).1
      hf hbound htests hΔ hthird'
    change |G (y,x y/M)*t^3-G (ya,xa/M)| ≤ B*(Δ+(|t^3|+1)/(2*M)) at hh
    have htp : |t^3| ≤ 8 := by
      rw [abs_of_nonneg (pow_nonneg htpos.le 3)]
      exact (pow_le_pow_left₀ htpos.le ht.2 3).trans_eq (by norm_num)
    have hround : (|t^3|+1)/(2*M) ≤ 5/M := by
      apply (div_le_div_iff₀ (show 0 < 2*M by positivity) hMpos).mpr
      nlinarith only [htp,hMpos]
    have hb : |G (y,x y/M)*t^3-G (ya,xa/M)| ≤ B*(Δ+5/M) :=
      hh.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hround)
        (by dsimp only [B]; positivity))
    have htl : (1/8:ℝ) ≤ t^3 := by
      convert pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) ht.1 3 using 1
      norm_num
    calc
      _ = |G (y,x y/M)*t^3-G (ya,xa/M)|/t^3 := by
        have he : G (y,x y/M)-g=(G (y,x y/M)*t^3-G (ya,xa/M))/t^3 := by
          dsimp only [g]
          field_simp
        rw [he,abs_div,abs_of_pos (pow_pos htpos 3)]
      _ ≤ |G (y,x y/M)*t^3-G (ya,xa/M)|/(1/8) :=
        div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) htl
      _ ≤ (B*(Δ+5/M))/(1/8) := div_le_div_of_nonneg_right hb (by norm_num)
      _ = _ := by ring
  have hh := hcount F η (8*B*(Δ+5/M)) J (2*M^2*q/T) g S (fun y => x y/M)
    hη hηmax hf hbound htests (by dsimp only [B]; positivity) hJ
    (fun y hy => ⟨(hpoints y hy).1,hnorm _ (hpoints y hy).2⟩) hsep hroots hnear
  convert hh using 1
  ring

                                                                    
                                                                       
                                                                   
theorem exists_right_neighbor_at_order {a b H : ℤ}
    (hb : 0 < b) (hbH : b ≤ H) (hcop : IsCoprime a b) :
    ∃ c d : ℤ, 1 ≤ d ∧ d ≤ H ∧ H < b+d ∧ IsCoprime c d ∧
      c*b-a*d=1 ∧
      ∀ m n : ℤ, 1 ≤ n → n ≤ H → a*n < b*m → c*n ≤ m*d := by
  obtain ⟨c₀,d₀,hd₀,hd₀b,_hcop₀,hdet₀,_hclose₀⟩ :=
    TaoTrudgianYang2025.HuxleyLinearForm.exists_right_neighbor hb hcop
  let k := (H-d₀)/b
  let c := c₀+a*k
  let d := d₀+b*k
  have hk : 0 ≤ k := Int.ediv_nonneg (by omega) hb.le
  have hd : 1 ≤ d := by
    have hh := mul_nonneg hb.le hk
    dsimp only [d]
    linarith only [hd₀,hh]
  have hremainder := Int.emod_add_mul_ediv (H-d₀) b
  have hlo := Int.emod_nonneg (H-d₀) hb.ne'
  have hhi := Int.emod_lt_of_pos (H-d₀) hb
  have hform : d=H-(H-d₀)%b := by
    dsimp only [d,k]
    nlinarith only [hremainder]
  have hdH : d ≤ H := by rw [hform]; omega
  have hsum : H < b+d := by rw [hform]; omega
  have hdet : c*b-a*d=1 := by
    dsimp only [c,d]
    nlinarith only [hdet₀]
  refine ⟨c,d,hd,hdH,hsum,⟨b,-a,by nlinarith only [hdet]⟩,hdet,?_⟩
  intro m n _hn hnH hleft
  by_contra hright
  have he₁ : 1 ≤ b*m-a*n := by omega
  have he₂ : 1 ≤ c*n-m*d := by omega
  have hid : n=d*(b*m-a*n)+b*(c*n-m*d) := by
    nlinarith only [congrArg (fun z : ℤ => n*z) hdet]
  have hl := mul_le_mul_of_nonneg_left he₁ (show 0 ≤ d by omega)
  have hr := mul_le_mul_of_nonneg_left he₂ hb.le
  nlinarith only [hid,hl,hr,hnH,hsum]

                                                                  
                                                                      
                                                        
theorem exists_farey_bracket_unit {H : ℤ} (hH : 1 ≤ H)
    {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) :
    ∃ a b c d : ℤ, 1 ≤ b ∧ b ≤ H ∧ 1 ≤ d ∧ d ≤ H ∧ H < b+d ∧
      IsCoprime a b ∧ IsCoprime c d ∧ c*b-a*d=1 ∧
      (a:ℝ)/b ≤ x ∧ x < (c:ℝ)/d := by
  classical
  let grid : Finset (ℤ × ℤ) := (Finset.Icc (0:ℤ) H) ×ˢ (Finset.Icc (1:ℤ) H)
  let V : Finset ℚ := (grid.image (fun p => Rat.divInt p.1 p.2)).filter
    (fun q : ℚ => (q:ℝ) ≤ x)
  have hzero : (0:ℚ) ∈ V := by
    apply Finset.mem_filter.mpr
    refine ⟨?_,by simpa only [Rat.cast_zero] using hx.1⟩
    apply Finset.mem_image.mpr
    refine ⟨(0,1),?_,by norm_num⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩,Finset.mem_Icc.mpr ⟨le_rfl,hH⟩⟩
  have hV : V.Nonempty := ⟨0,hzero⟩
  let q : ℚ := V.max' hV
  have hqV : q ∈ V := Finset.max'_mem V hV
  have hqmax v (hv : v ∈ V) : v ≤ q := Finset.le_max' V v hv
  have hq0 : (0:ℝ) ≤ q := by exact_mod_cast hqmax 0 hzero
  have hqx : (q:ℝ) ≤ x := (Finset.mem_filter.mp hqV).2
  have hb : (0:ℤ) < q.den := by exact_mod_cast q.den_pos
  have hbH : (q.den:ℤ) ≤ H := by
    obtain ⟨p,hp,hpq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hqV).1
    have hpgrid := Finset.mem_product.mp hp
    have hpd := Finset.mem_Icc.mp hpgrid.2
    have hh : ((Rat.divInt p.1 p.2).den:ℤ) ≤ p.2 :=
      Int.le_of_dvd (by omega) (Rat.den_dvd p.1 p.2)
    rw [hpq] at hh
    exact hh.trans hpd.2
  obtain ⟨c,d,hd,hdH,hsum,hcop,hdet,_hclose⟩ :=
    exists_right_neighbor_at_order hb hbH q.isCoprime_num_den
  have hbR : (0:ℝ) < q.den := by exact_mod_cast hb
  have hdR : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hqval : (q:ℝ)=(q.num:ℝ)/q.den := Rat.cast_def q
  have hgap : (c:ℝ)/d-(q:ℝ)=1/((q.den:ℝ)*d) := by
    rw [hqval]
    field_simp
    exact_mod_cast (show c*(q.den:ℤ)-d*q.num=1 by nlinarith only [hdet])
  have hright : (q:ℝ) < (c:ℝ)/d := by
    have hp : 0 < 1/((q.den:ℝ)*d) := by positivity
    linarith only [hgap,hp]
  have hxright : x < (c:ℝ)/d := by
    by_contra hbad
    have hcx : (c:ℝ)/d ≤ x := le_of_not_gt hbad
    have hc0R : 0 ≤ (c:ℝ) := by
      have hh := (le_div_iff₀ hdR).mp (hq0.trans hright.le)
      simpa only [zero_mul] using hh
    have hc0 : 0 ≤ c := by exact_mod_cast hc0R
    have hcdR : (c:ℝ) < d := (div_lt_one hdR).mp (hcx.trans_lt hx.2)
    have hcd : c < d := by exact_mod_cast hcdR
    have hcH : c ≤ H := le_trans hcd.le hdH
    have hcast : ((Rat.divInt c d):ℝ)=(c:ℝ)/d := by simp only [Rat.cast_divInt]
    have hv : Rat.divInt c d ∈ V := by
      apply Finset.mem_filter.mpr
      refine ⟨?_,by simpa only [hcast] using hcx⟩
      apply Finset.mem_image.mpr
      refine ⟨(c,d),?_,rfl⟩
      exact Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨hc0,hcH⟩,Finset.mem_Icc.mpr ⟨hd,hdH⟩⟩
    have hle : ((Rat.divInt c d):ℝ) ≤ q := by exact_mod_cast hqmax _ hv
    rw [hcast] at hle
    exact (not_le_of_gt hright) hle
  refine ⟨q.num,q.den,c,d,by omega,hbH,hd,hdH,hsum,q.isCoprime_num_den,hcop,hdet,?_,hxright⟩
  simpa only [hqval,Int.cast_natCast] using hqx

                                                                  
                                                                     
theorem exists_farey_bracket {H : ℤ} (hH : 1 ≤ H) (x : ℝ) :
    ∃ a b c d : ℤ, 1 ≤ b ∧ b ≤ H ∧ 1 ≤ d ∧ d ≤ H ∧ H < b+d ∧
      IsCoprime a b ∧ IsCoprime c d ∧ c*b-a*d=1 ∧
      (a:ℝ)/b ≤ x ∧ x < (c:ℝ)/d ∧
      (c:ℝ)/d-(a:ℝ)/b=1/((b:ℝ)*d) := by
  let m : ℤ := ⌊x⌋
  have hy : x-(m:ℝ) ∈ Ico (0:ℝ) 1 := by
    have hlo := Int.floor_le x
    have hhi := Int.lt_floor_add_one x
    change (m:ℝ) ≤ x at hlo
    change x < (m:ℝ)+1 at hhi
    constructor <;> linarith only [hlo,hhi]
  obtain ⟨a,b,c,d,hb,hbH,hd,hdH,hsum,_hab,_hcd,hdet,hlo,hhi⟩ :=
    exists_farey_bracket_unit hH hy
  let aa := a+m*b
  let cc := c+m*d
  have hdet' : cc*b-aa*d=1 := by
    dsimp only [aa,cc]
    nlinarith only [hdet]
  have hab' : IsCoprime aa b := ⟨-d,cc,by nlinarith only [hdet']⟩
  have hcd' : IsCoprime cc d := ⟨b,-aa,by nlinarith only [hdet']⟩
  have hbR : (0:ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hdR : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hea : (aa:ℝ)/b=(a:ℝ)/b+m := by
    dsimp only [aa]
    push_cast
    field_simp
  have hec : (cc:ℝ)/d=(c:ℝ)/d+m := by
    dsimp only [cc]
    push_cast
    field_simp
  refine ⟨aa,b,cc,d,hb,hbH,hd,hdH,hsum,hab',hcd',hdet',?_,?_,?_⟩
  · rw [hea]
    linarith only [hlo]
  · rw [hec]
    linarith only [hhi]
  · field_simp
    exact_mod_cast (show cc*b-d*aa=1 by nlinarith only [hdet'])

                                                                  
                                                                       
                                        
theorem exists_seeded_separated_reference_cover
    (A seed : Set ℝ) (ε : NNReal) (hA : A.Finite)
    (hseed : seed ⊆ A) (hsep : Metric.IsSeparated ε seed) :
    ∃ S : Set ℝ, seed ⊆ S ∧ S ⊆ A ∧ S.Finite ∧
      Metric.IsSeparated ε S ∧ Metric.IsCover ε A S := by
  let P := {S : Set ℝ | seed ⊆ S ∧ S ⊆ A ∧ Metric.IsSeparated ε S}
  have hP : P.Finite := hA.powerset.subset (fun _ hS => hS.2.1)
  have hne : P.Nonempty := ⟨seed,Subset.rfl,hseed,hsep⟩
  obtain ⟨S,hmax⟩ := hP.exists_maximal hne
  have hS : seed ⊆ S ∧ S ⊆ A ∧ Metric.IsSeparated ε S := hmax.1
  refine ⟨S,hS.1,hS.2.1,hA.subset hS.2.1,hS.2.2,?_⟩
  apply Metric.IsCover.of_maximal_isSeparated
  refine ⟨⟨hS.2.1,hS.2.2⟩,?_⟩
  intro T hT hST
  exact hmax.2 ⟨hS.1.trans hST,hT.1,hT.2⟩ hST

                                                                   
                                                                      
                                                    
theorem exists_mediant_reference_cover {e r f s : ℤ} {δ : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hdet : f*r-e*s=1)
    (hδ : 0 < δ) (hscale : 1 ≤ δ*(r:ℝ)^2) :
    ∃ K : ℕ,
      (∀ n : ℕ, n ≤ K →
        IsCoprime (e+f*(n:ℤ)) (r+s*(n:ℤ)) ∧ r ≤ r+s*(n:ℤ)) ∧
      ∀ x ∈ Icc ((e:ℝ)/r) ((f:ℝ)/s),
        ∃ n ≤ K, |x-((e:ℝ)+f*n)/((r:ℝ)+s*n)| ≤ δ := by
  classical
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hsR : (0:ℝ) < s := by exact_mod_cast hs
  let K : ℕ := ⌈1/(δ*(s:ℝ)^2)⌉₊
  let q := fun n : ℕ => ((e:ℝ)+f*n)/((r:ℝ)+s*n)
  have hden (n : ℕ) : 0 < (r:ℝ)+s*(n:ℝ) := by positivity
  have hlabel (n : ℕ) : IsCoprime (e+f*(n:ℤ)) (r+s*(n:ℤ)) ∧ r ≤ r+s*(n:ℤ) := by
    constructor
    · refine ⟨-s,f,?_⟩
      nlinarith only [hdet]
    · have hh := mul_nonneg hs.le (Int.natCast_nonneg n)
      linarith only [hh]
  have hdetR : (f:ℝ)*r-e*s=1 := by exact_mod_cast hdet
  have hend n : (f:ℝ)/s-q n=1/((s:ℝ)*((r:ℝ)+s*n)) := by
    dsimp only [q]
    field_simp
    nlinarith only [hdetR]
  have hstep n : q (n+1)-q n =
      1/(((r:ℝ)+s*n)*((r:ℝ)+s*(n+1:ℕ))) := by
    dsimp only [q]
    field_simp
    push_cast
    nlinarith only [hdetR]
  have hgap n : q (n+1)-q n ≤ δ := by
    rw [hstep]
    apply (div_le_iff₀ (mul_pos (hden n) (hden (n+1)))).mpr
    have hleft : (r:ℝ) ≤ (r:ℝ)+s*n := le_add_of_nonneg_right (by positivity)
    have hright : (r:ℝ) ≤ (r:ℝ)+s*(n+1:ℕ) := le_add_of_nonneg_right (by positivity)
    have hh := mul_le_mul hleft hright hrR.le (hden n).le
    have hh' := mul_le_mul_of_nonneg_left hh hδ.le
    nlinarith only [hscale,hh']
  have hK : 1/(δ*(s:ℝ)^2) ≤ (K:ℝ) := Nat.le_ceil _
  have hlast : (f:ℝ)/s-q K ≤ δ := by
    rw [hend]
    apply (div_le_iff₀ (mul_pos hsR (hden K))).mpr
    have hh := (div_le_iff₀ (show 0 < δ*(s:ℝ)^2 by positivity)).mp hK
    have hextra : 0 ≤ δ*(s:ℝ)*r := by positivity
    nlinarith only [hh,hextra]
  refine ⟨K,fun n _ => hlabel n,?_⟩
  intro x hx
  let I := (Finset.range (K+1)).filter (fun n => q n ≤ x)
  have hz : 0 ∈ I := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega),?_⟩
    simpa only [q,Nat.cast_zero,mul_zero,add_zero] using hx.1
  have hI : I.Nonempty := ⟨0,hz⟩
  let n := I.max' hI
  have hnI : n ∈ I := Finset.max'_mem I hI
  have hnK : n ≤ K := by
    have hh := Finset.mem_range.mp (Finset.mem_filter.mp hnI).1
    omega
  have hnx : q n ≤ x := (Finset.mem_filter.mp hnI).2
  refine ⟨n,hnK,?_⟩
  change |x-q n| ≤ δ
  rw [abs_of_nonneg (sub_nonneg.mpr hnx)]
  rcases lt_or_eq_of_le hnK with hnlt | hnEq
  · have hxnext : x < q (n+1) := by
      by_contra hbad
      have hmem : n+1 ∈ I := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega),le_of_not_gt hbad⟩
      have hh := Finset.le_max' I (n+1) hmem
      change n+1 ≤ n at hh
      omega
    have hh := hgap n
    linarith only [hxnext,hh]
  · rw [hnEq]
    linarith only [hx.2,hlast]

                                                                      
                                                                      
                                                            
theorem exists_separated_mediant_reference_cover {e r f s : ℤ} {δ : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hdet : f*r-e*s=1)
    (hδ : 0 < δ) (hscale : 1 ≤ δ*(r:ℝ)^2)
    (hlong : δ < (f:ℝ)/s-(e:ℝ)/r) :
    ∃ S : Finset ℝ, (e:ℝ)/r ∈ S ∧ (f:ℝ)/s ∈ S ∧
      (∀ x ∈ S, x ∈ Icc ((e:ℝ)/r) ((f:ℝ)/s)) ∧
      (∀ x ∈ S, x ≠ (f:ℝ)/s →
        ∃ n : ℕ, x=((e:ℝ)+f*n)/((r:ℝ)+s*n) ∧
          IsCoprime (e+f*(n:ℤ)) (r+s*(n:ℤ)) ∧ r ≤ r+s*(n:ℤ)) ∧
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/4 < |x-y|) ∧
      (∀ x ∈ Icc ((e:ℝ)/r) ((f:ℝ)/s), ∃ y ∈ S, |x-y| ≤ 5*δ/4) ∧
      (∀ x ∈ S, ∀ y ∈ S, x < y →
        (∀ z ∈ S, ¬ (x < z ∧ z < y)) →
        δ/4 < y-x ∧ y-x ≤ 5*δ/2) := by
  classical
  obtain ⟨K,hlabels,hmesh⟩ := exists_mediant_reference_cover hr hs hdet hδ hscale
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hsR : (0:ℝ) < s := by exact_mod_cast hs
  have hdetR : (f:ℝ)*r-e*s=1 := by exact_mod_cast hdet
  let q := fun n : ℕ => ((e:ℝ)+f*n)/((r:ℝ)+s*n)
  let A : Finset ℝ := insert ((f:ℝ)/s) ((Finset.range (K+1)).image q)
  let ε : NNReal := ⟨δ/4,by positivity⟩
  have hden (n : ℕ) : 0 < (r:ℝ)+s*(n:ℝ) := by positivity
  have hq0 : q 0=(e:ℝ)/r := by simp only [q,Nat.cast_zero,mul_zero,add_zero]
  have hqA n (hn : n ≤ K) : q n ∈ A := Finset.mem_insert_of_mem
    (Finset.mem_image_of_mem q (Finset.mem_range.mpr (by omega)))
  have hseed : ({(e:ℝ)/r,(f:ℝ)/s} : Set ℝ) ⊆ A := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with he | hf
    · rw [he,←hq0]
      exact hqA 0 (Nat.zero_le _)
    · rw [Set.mem_singleton_iff.mp hf]
      exact Finset.mem_insert_self _ _
  have hseedSep : Metric.IsSeparated ε ({(e:ℝ)/r,(f:ℝ)/s} : Set ℝ) := by
    apply Metric.isSeparated_insert.mpr
    refine ⟨Metric.IsSeparated.singleton,?_⟩
    intro y hy _hne
    rw [Set.mem_singleton_iff.mp hy,edist_dist,Real.dist_eq,ENNReal.coe_lt_ofReal]
    change δ/4 < |(e:ℝ)/r-(f:ℝ)/s|
    rw [abs_of_neg (by linarith only [hlong,hδ])]
    linarith only [hlong,hδ]
  obtain ⟨N,hseedN,hNA,hNfin,hNsep,hcover⟩ :=
    exists_seeded_separated_reference_cover (A : Set ℝ) _ ε A.finite_toSet hseed hseedSep
  let S := hNfin.toFinset
  have hNS x : x ∈ S ↔ x ∈ N := hNfin.mem_toFinset
  have hSA x (hx : x ∈ S) : x ∈ A := hNA ((hNS x).mp hx)
  have hqI n : q n ∈ Icc ((e:ℝ)/r) ((f:ℝ)/s) := by
    have hlo : q n-(e:ℝ)/r=(n:ℝ)/((r:ℝ)*((r:ℝ)+s*n)) := by
      dsimp only [q]
      field_simp
      nlinarith only [congrArg (fun z : ℝ => n*z) hdetR]
    have hhi : (f:ℝ)/s-q n=1/((s:ℝ)*((r:ℝ)+s*n)) := by
      dsimp only [q]
      field_simp
      nlinarith only [hdetR]
    constructor
    · have hh : 0 ≤ (n:ℝ)/((r:ℝ)*((r:ℝ)+s*n)) := by positivity
      linarith only [hlo,hh]
    · have hh : 0 ≤ 1/((s:ℝ)*((r:ℝ)+s*n)) := by positivity
      linarith only [hhi,hh]
  have hpoints x (hx : x ∈ S) : x ∈ Icc ((e:ℝ)/r) ((f:ℝ)/s) := by
    rcases Finset.mem_insert.mp (hSA x hx) with he | hi
    · rw [he]
      exact ⟨by linarith only [hlong,hδ],le_rfl⟩
    · obtain ⟨n,_hn,rfl⟩ := Finset.mem_image.mp hi
      exact hqI n
  have hsep x (hx : x ∈ S) y (hy : y ∈ S) (hne : x ≠ y) : δ/4 < |x-y| := by
    have hh := hNsep ((hNS x).mp hx) ((hNS y).mp hy) hne
    change (ε:ENNReal) < edist x y at hh
    rw [edist_dist,Real.dist_eq,ENNReal.coe_lt_ofReal] at hh
    exact hh
  have hnet x (hx : x ∈ Icc ((e:ℝ)/r) ((f:ℝ)/s)) :
      ∃ y ∈ S, |x-y| ≤ 5*δ/4 := by
    obtain ⟨n,hn,hnear⟩ := hmesh x hx
    obtain ⟨y,hy,hdist⟩ := hcover (hqA n hn)
    have hdistR : |q n-y| ≤ δ/4 := by
      change edist (q n) y ≤ (ε:ENNReal) at hdist
      rw [edist_dist,Real.dist_eq,ENNReal.ofReal_le_coe] at hdist
      exact hdist
    refine ⟨y,(hNS y).mpr hy,?_⟩
    calc
      _ ≤ |x-q n|+|q n-y| := abs_sub_le x (q n) y
      _ ≤ δ+δ/4 := add_le_add hnear hdistR
      _ = _ := by ring
  refine ⟨S,(hNS _).mpr (hseedN (Set.mem_insert _ _)),
    (hNS _).mpr (hseedN (Set.mem_insert_of_mem _ (Set.mem_singleton _))),
    hpoints,?_,hsep,hnet,?_⟩
  · intro x hx hne
    have hi := (Finset.mem_insert.mp (hSA x hx)).resolve_left hne
    obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hi
    have hnK : n ≤ K := by have hh := Finset.mem_range.mp hn; omega
    exact ⟨n,he.symm,(hlabels n hnK).1,(hlabels n hnK).2⟩
  · intro x hx y hy hxy hadj
    refine ⟨?_,?_⟩
    · have hh := hsep y hy x hx hxy.ne'
      simpa only [abs_of_pos (sub_pos.mpr hxy)] using hh
    have hmid : (x+y)/2 ∈ Icc ((e:ℝ)/r) ((f:ℝ)/s) := by
      have hxI := hpoints x hx
      have hyI := hpoints y hy
      constructor <;> linarith only [hxI.1,hyI.2,hxy]
    obtain ⟨z,hz,hzdist⟩ := hnet _ hmid
    have hzabs := abs_le.mp hzdist
    by_cases hxz : x < z
    · have hyz : y ≤ z := le_of_not_gt (fun hzy => hadj z hz ⟨hxz,hzy⟩)
      linarith only [hzabs.1,hyz]
    · have hzx : z ≤ x := le_of_not_gt hxz
      linarith only [hzabs.2,hzx]

                                                                  
                                                                         
theorem exists_separated_reflected_mediant_reference_cover {e r f s : ℤ} {δ : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hdet : f*r-e*s=1)
    (hδ : 0 < δ) (hscale : 1 ≤ δ*(s:ℝ)^2)
    (hlong : δ < (f:ℝ)/s-(e:ℝ)/r) :
    ∃ S : Finset ℝ, (e:ℝ)/r ∈ S ∧ (f:ℝ)/s ∈ S ∧
      (∀ x ∈ S, x ∈ Icc ((e:ℝ)/r) ((f:ℝ)/s)) ∧
      (∀ x ∈ S, x ≠ (e:ℝ)/r →
        ∃ n : ℕ, x=((f:ℝ)+e*n)/((s:ℝ)+r*n) ∧
          IsCoprime (f+e*(n:ℤ)) (s+r*(n:ℤ)) ∧ s ≤ s+r*(n:ℤ)) ∧
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/4 < |x-y|) ∧
      (∀ x ∈ Icc ((e:ℝ)/r) ((f:ℝ)/s), ∃ y ∈ S, |x-y| ≤ 5*δ/4) ∧
      (∀ x ∈ S, ∀ y ∈ S, x < y →
        (∀ z ∈ S, ¬ (x < z ∧ z < y)) →
        δ/4 < y-x ∧ y-x ≤ 5*δ/2) := by
  classical
  obtain ⟨S,hleft,hright,hpoints,hlabels,hsep,hnet,hgaps⟩ :=
    exists_separated_mediant_reference_cover (e:=-f) (f:=-e) hs hr
      (by nlinarith only [hdet]) hδ hscale (by
        push_cast
        simp only [neg_div]
        linarith only [hlong])
  let V := S.image (fun x : ℝ => -x)
  have hVS x : x ∈ V ↔ -x ∈ S := by
    constructor
    · intro hx
      obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hx
      rw [←he,neg_neg]
      exact hy
    · intro hx
      exact Finset.mem_image.mpr ⟨-x,hx,neg_neg x⟩
  have hleft' : (e:ℝ)/r ∈ V := (hVS _).mpr (by
    simpa only [Int.cast_neg,neg_div] using hright)
  have hright' : (f:ℝ)/s ∈ V := (hVS _).mpr (by
    simpa only [Int.cast_neg,neg_div] using hleft)
  have hpoints' x (hx : x ∈ V) : x ∈ Icc ((e:ℝ)/r) ((f:ℝ)/s) := by
    have hh := hpoints (-x) ((hVS x).mp hx)
    simp only [Int.cast_neg,neg_div] at hh
    constructor <;> linarith only [hh.1,hh.2]
  have hsep' x (hx : x ∈ V) y (hy : y ∈ V) (hne : x ≠ y) : δ/4 < |x-y| := by
    have hh := hsep (-x) ((hVS x).mp hx) (-y) ((hVS y).mp hy)
      (fun he => hne (neg_injective he))
    simpa only [neg_sub_neg,abs_sub_comm] using hh
  have hnet' x (hx : x ∈ Icc ((e:ℝ)/r) ((f:ℝ)/s)) :
      ∃ y ∈ V, |x-y| ≤ 5*δ/4 := by
    have hxi : -x ∈ Icc (((-f:ℤ):ℝ)/s) (((-e:ℤ):ℝ)/r) := by
      simp only [Int.cast_neg,neg_div]
      constructor <;> linarith only [hx.1,hx.2]
    obtain ⟨y,hy,hh⟩ := hnet (-x) hxi
    refine ⟨-y,(hVS _).mpr (by simpa only [neg_neg] using hy),?_⟩
    rw [show -x-y=-(x+y) by ring,abs_neg] at hh
    simpa only [sub_neg_eq_add] using hh
  refine ⟨V,hleft',hright',hpoints',?_,hsep',hnet',?_⟩
  · intro x hx hne
    have hne' : -x ≠ ((-e:ℤ):ℝ)/r := by
      simp only [Int.cast_neg,neg_div,ne_eq,neg_inj]
      exact hne
    obtain ⟨n,he,hcop,hden⟩ := hlabels (-x) ((hVS x).mp hx) hne'
    refine ⟨n,?_,?_,hden⟩
    · have he' := congrArg Neg.neg he
      simpa only [Int.cast_neg,neg_mul,←neg_add,neg_div,neg_neg] using he'
    · convert hcop.neg_left using 1
      ring
  · intro x hx y hy hxy hadj
    have hh := hgaps (-y) ((hVS y).mp hy) (-x) ((hVS x).mp hx) (neg_lt_neg hxy) (by
      intro z hz hbetween
      have hzin : -z ∈ V := (hVS _).mpr (by simpa only [neg_neg] using hz)
      exact hadj (-z) hzin ⟨by linarith only [hbetween.2],by linarith only [hbetween.1]⟩)
    simpa only [neg_sub_neg] using hh

                                                              
                                                                  
                                                                
theorem exists_farey_reference_refinement {a b c d : ℤ} {δ : ℝ}
    (hb : 0 < b) (hd : 0 < d) (hdet : c*b-a*d=1) (hδ : 0 < δ)
    (hscale : 1 ≤ δ*((max b d:ℤ):ℝ)^2)
    (hgap : δ/4 ≤ (c:ℝ)/d-(a:ℝ)/b) :
    ∃ S : Finset ℝ, (a:ℝ)/b ∈ S ∧ (c:ℝ)/d ∈ S ∧
      (∀ x ∈ S, x ∈ Icc ((a:ℝ)/b) ((c:ℝ)/d)) ∧
      (∀ x ∈ S, x ≠ (a:ℝ)/b → x ≠ (c:ℝ)/d →
        ∃ m n u v : ℤ, x=(m:ℝ)/n ∧ IsCoprime m n ∧ max b d ≤ n ∧
          ((u=a ∧ v=b) ∨ (u=c ∧ v=d)) ∧ |m*v-u*n|=1) ∧
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/4 ≤ |x-y|) ∧
      (∀ x ∈ Icc ((a:ℝ)/b) ((c:ℝ)/d), ∃ y ∈ S, |x-y| ≤ 5*δ/4) ∧
      (∀ x ∈ S, ∀ y ∈ S, x < y →
        (∀ z ∈ S, ¬ (x < z ∧ z < y)) →
        δ/4 ≤ y-x ∧ y-x ≤ 5*δ/2) := by
  classical
  have hpos : (a:ℝ)/b < (c:ℝ)/d := by linarith only [hgap,hδ]
  by_cases hshort : (c:ℝ)/d-(a:ℝ)/b ≤ δ
  · let S : Finset ℝ := {(a:ℝ)/b,(c:ℝ)/d}
    have hpoints x (hx : x ∈ S) : x ∈ Icc ((a:ℝ)/b) ((c:ℝ)/d) := by
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨le_rfl,hpos.le⟩
      · rw [Finset.mem_singleton.mp hx]
        exact ⟨hpos.le,le_rfl⟩
    have hsep x (hx : x ∈ S) y (hy : y ∈ S) (hne : x ≠ y) : δ/4 ≤ |x-y| := by
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rcases Finset.mem_insert.mp hy with he | hy
        · exact (hne he.symm).elim
        · rw [Finset.mem_singleton.mp hy,abs_of_neg (sub_neg.mpr hpos)]
          linarith only [hgap]
      · have he := Finset.mem_singleton.mp hx
        rw [he]
        rcases Finset.mem_insert.mp hy with rfl | hy
        · simpa only [abs_of_pos (sub_pos.mpr hpos)] using hgap
        · exact (hne (he.trans (Finset.mem_singleton.mp hy).symm)).elim
    refine ⟨S,Finset.mem_insert_self _ _,Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
      hpoints,?_,hsep,?_,?_⟩
    · intro x hx hleft hright
      rcases Finset.mem_insert.mp hx with he | he
      · exact (hleft he).elim
      · exact (hright (Finset.mem_singleton.mp he)).elim
    · intro x hx
      refine ⟨(a:ℝ)/b,Finset.mem_insert_self _ _,?_⟩
      rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
      linarith only [hx.2,hshort,hδ]
    · intro x hx y hy hxy _hadj
      refine ⟨?_,?_⟩
      · simpa only [abs_of_pos (sub_pos.mpr hxy)] using hsep y hy x hx hxy.ne'
      · have hxI := hpoints x hx
        have hyI := hpoints y hy
        linarith only [hxI.1,hyI.2,hshort,hδ]
  have hlong : δ < (c:ℝ)/d-(a:ℝ)/b := lt_of_not_ge hshort
  rcases le_total d b with hdb | hbd
  · have hscale' : 1 ≤ δ*(b:ℝ)^2 := by simpa only [max_eq_left hdb] using hscale
    obtain ⟨S,hl,hr,hpoints,hlabels,hsep,hnet,hgaps⟩ :=
      exists_separated_mediant_reference_cover hb hd hdet hδ hscale' hlong
    refine ⟨S,hl,hr,hpoints,?_,fun x hx y hy hne => (hsep x hx y hy hne).le,hnet,?_⟩
    · intro x hx _hleft hright
      obtain ⟨n,he,hcop,hden⟩ := hlabels x hx hright
      refine ⟨a+c*(n:ℤ),b+d*(n:ℤ),c,d,?_,hcop,?_,Or.inr ⟨rfl,rfl⟩,?_⟩
      · simpa only [Int.cast_add,Int.cast_mul,Int.cast_natCast] using he
      · simpa only [max_eq_left hdb] using hden
      · rw [show (a+c*(n:ℤ))*d-c*(b+d*(n:ℤ))=(-1:ℤ) by nlinarith only [hdet]]
        norm_num
    · intro x hx y hy hxy hadj
      exact ⟨(hgaps x hx y hy hxy hadj).1.le,(hgaps x hx y hy hxy hadj).2⟩
  · have hscale' : 1 ≤ δ*(d:ℝ)^2 := by simpa only [max_eq_right hbd] using hscale
    obtain ⟨S,hl,hr,hpoints,hlabels,hsep,hnet,hgaps⟩ :=
      exists_separated_reflected_mediant_reference_cover hb hd hdet hδ hscale' hlong
    refine ⟨S,hl,hr,hpoints,?_,fun x hx y hy hne => (hsep x hx y hy hne).le,hnet,?_⟩
    · intro x hx hleft _hright
      obtain ⟨n,he,hcop,hden⟩ := hlabels x hx hleft
      refine ⟨c+a*(n:ℤ),d+b*(n:ℤ),a,b,?_,hcop,?_,Or.inl ⟨rfl,rfl⟩,?_⟩
      · simpa only [Int.cast_add,Int.cast_mul,Int.cast_natCast] using he
      · simpa only [max_eq_right hbd] using hden
      · rw [show (c+a*(n:ℤ))*b-a*(d+b*(n:ℤ))=(1:ℤ) by nlinarith only [hdet]]
        norm_num
    · intro x hx y hy hxy hadj
      exact ⟨(hgaps x hx y hy hxy hadj).1.le,(hgaps x hx y hy hxy hadj).2⟩

                                                                   
                                                                       
                                                            
theorem exists_source_farey_order {δ : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ 1) :
    ∃ H : ℤ, 2 ≤ H ∧
      ∀ b d : ℤ, 0 < b → b ≤ H → 0 < d → d ≤ H → H < b+d →
        1 ≤ δ*((max b d:ℤ):ℝ)^2 ∧ δ/4 ≤ 1/((b:ℝ)*d) := by
  let H : ℤ := ⌊2/Real.sqrt δ⌋
  have hsqrt : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hsqrt1 : Real.sqrt δ ≤ 1 := by
    have hh := Real.sq_sqrt hδ.le
    nlinarith only [hh,hδmax,hsqrt]
  have htwo : (2:ℝ) ≤ 2/Real.sqrt δ := by
    apply (le_div_iff₀ hsqrt).mpr
    linarith only [hsqrt1]
  have hH : 2 ≤ H := Int.le_floor.mpr (by exact_mod_cast htwo)
  have hHpos : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hHupper : (H:ℝ) ≤ 2/Real.sqrt δ := Int.floor_le _
  have hHlower : 2/Real.sqrt δ < (H:ℝ)+1 := Int.lt_floor_add_one _
  have hHsq : δ*(H:ℝ)^2 ≤ 4 := by
    have hh := (le_div_iff₀ hsqrt).mp hHupper
    have hh2 := pow_le_pow_left₀ (mul_pos hHpos hsqrt).le hh 2
    rw [mul_pow,Real.sq_sqrt hδ.le] at hh2
    nlinarith only [hh2]
  refine ⟨H,hH,?_⟩
  intro b d hb hbH hd hdH hsum
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hbH' : (b:ℝ) ≤ H := by exact_mod_cast hbH
  have hdH' : (d:ℝ) ≤ H := by exact_mod_cast hdH
  have hsum' : (H:ℝ)+1 ≤ (b:ℝ)+d := by
    exact_mod_cast (show H+1 ≤ b+d by omega)
  have hmaxb : (b:ℝ) ≤ (max b d:ℤ) := by exact_mod_cast le_max_left b d
  have hmaxd : (d:ℝ) ≤ (max b d:ℤ) := by exact_mod_cast le_max_right b d
  have hmaxlo : 1/Real.sqrt δ ≤ ((max b d:ℤ):ℝ) := by
    rw [show 2/Real.sqrt δ=2*(1/Real.sqrt δ) by ring] at hHlower
    linarith only [hHlower,hsum',hmaxb,hmaxd]
  have hmaxsq : 1 ≤ δ*((max b d:ℤ):ℝ)^2 := by
    have hh := (div_le_iff₀ hsqrt).mp hmaxlo
    have hh2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hh 2
    rw [mul_pow,Real.sq_sqrt hδ.le] at hh2
    nlinarith only [hh2]
  refine ⟨hmaxsq,?_⟩
  have hprod : (b:ℝ)*d ≤ (H:ℝ)^2 := by
    simpa only [pow_two] using mul_le_mul hbH' hdH' hdR.le hHpos.le
  have hh := (mul_le_mul_of_nonneg_left hprod hδ.le).trans hHsq
  apply (le_div_iff₀ (mul_pos hbR hdR)).mpr
  nlinarith only [hh]

                                                                
                                                                      
                                                                   
theorem unimodular_interval_denominator_lower {a b c d m n : ℤ}
    (hb : 0 < b) (hd : 0 < d) (hn : 0 < n) (hdet : c*b-a*d=1)
    (hleft : (a:ℝ)/b < (m:ℝ)/n) (hright : (m:ℝ)/n < (c:ℝ)/d) :
    b+d ≤ n := by
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hl : a*n < m*b := by
    exact_mod_cast (div_lt_div_iff₀ hbR hnR).mp hleft
  have hr : m*d < c*n := by
    exact_mod_cast (div_lt_div_iff₀ hnR hdR).mp hright
  have hl1 : 1 ≤ b*m-a*n := by nlinarith only [hl]
  have hr1 : 1 ≤ c*n-d*m := by nlinarith only [hr]
  have hid : n=d*(b*m-a*n)+b*(c*n-d*m) := by
    nlinarith only [congrArg (fun z : ℤ => n*z) hdet]
  have hh₁ := mul_le_mul_of_nonneg_left hl1 hd.le
  have hh₂ := mul_le_mul_of_nonneg_left hr1 hb.le
  nlinarith only [hid,hh₁,hh₂]


                                                                  
                                                                         
                              
theorem farey_bracket_unit_bounds {a b c d : ℤ} {x : ℝ}
    (hb : 0 < b) (hd : 0 < d)
    (hdet : c*b-a*d=1) (hx : x ∈ Ico (0:ℝ) 1)
    (hleft : (a:ℝ)/b ≤ x) (hright : x < (c:ℝ)/d) :
    0 ≤ a ∧ c ≤ d := by
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  constructor
  · by_contra hbad
    have ha : a < 0 := lt_of_not_ge hbad
    have hneg : (a:ℝ)/b < 0 := div_neg_of_neg_of_pos (by exact_mod_cast ha) hbR
    have hpos : (0:ℝ) < (c:ℝ)/d := hx.1.trans_lt hright
    have hh := unimodular_interval_denominator_lower (m:=0) (n:=1)
      hb hd (by norm_num) hdet (by simpa only [Int.cast_zero,zero_div] using hneg)
      (by simpa only [Int.cast_zero,zero_div] using hpos)
    omega
  · by_contra hbad
    have hdc : d < c := lt_of_not_ge hbad
    have hgt : (1:ℝ) < (c:ℝ)/d := (one_lt_div hdR).mpr (by exact_mod_cast hdc)
    have hlt : (a:ℝ)/b < 1 := hleft.trans_lt hx.2
    have hh := unimodular_interval_denominator_lower (m:=1) (n:=1)
      hb hd (by norm_num) hdet (by simpa only [Int.cast_one,div_one] using hlt)
      (by simpa only [Int.cast_one,div_one] using hgt)
    omega

                                                                 
                                                                          
                                                        
theorem bounded_denominator_strict_separation {q r : ℚ} {H : ℤ}
    (hH : 2 ≤ H) (hq : (q.den:ℤ) ≤ H) (hr : (r.den:ℤ) ≤ H) (hne : q ≠ r) :
    1/(H:ℝ)^2 < |(q:ℝ)-(r:ℝ)| := by
  have hH1 : (1:ℝ) < H := by exact_mod_cast (show 1 < H by omega)
  have hHpos : (0:ℝ) < H := zero_lt_one.trans hH1
  have hqpos : (0:ℝ) < q.den := by exact_mod_cast q.den_pos
  have hrpos : (0:ℝ) < r.den := by exact_mod_cast r.den_pos
  have hqH : (q.den:ℝ) ≤ H := by exact_mod_cast hq
  have hrH : (r.den:ℝ) ≤ H := by exact_mod_cast hr
  have hdiff : 0 < |(q:ℝ)-(r:ℝ)| := abs_pos.mpr (sub_ne_zero.mpr (by
    intro he
    exact hne (Rat.cast_injective he)))
  apply (div_lt_iff₀ (sq_pos_of_pos hHpos)).mpr
  by_cases hden : q.den=r.den
  · have hnum : q.num ≠ r.num := by
      intro he
      apply hne
      apply Rat.cast_injective (α:=ℝ)
      simp only [Rat.cast_def,he,hden]
    have hi : (1:ℝ) ≤ |(q.num:ℝ)-(r.num:ℝ)| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hnum)
    have hid : |(q:ℝ)-(r:ℝ)| * (r.den:ℝ)=|(q.num:ℝ)-(r.num:ℝ)| := by
      rw [Rat.cast_def q,Rat.cast_def r,hden,←sub_div,abs_div,abs_of_pos hrpos]
      field_simp
    have hh : 1 ≤ |(q:ℝ)-(r:ℝ)| * (H:ℝ) := by
      calc
        _ ≤ |(q.num:ℝ)-(r.num:ℝ)| := hi
        _ = |(q:ℝ)-(r:ℝ)| * (r.den:ℝ) := hid.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hrH hdiff.le
    have hh2 := mul_le_mul_of_nonneg_right hh hHpos.le
    nlinarith only [hh2,hH1]
  · have hproduct : (q.den:ℝ)*(r.den:ℝ) < (H:ℝ)^2 := by
      rcases lt_or_eq_of_le hqH with hqstrict | hqeq
      · calc
          _ ≤ (q.den:ℝ)*(H:ℝ) := mul_le_mul_of_nonneg_left hrH hqpos.le
          _ < (H:ℝ)*(H:ℝ) := mul_lt_mul_of_pos_right hqstrict hHpos
          _ = _ := by ring
      · have hrne : (r.den:ℝ) ≠ H := by
          intro he
          apply hden
          have hh : (q.den:ℝ)=(r.den:ℝ) := hqeq.trans he.symm
          exact_mod_cast hh
        have hrstrict : (r.den:ℝ) < H := lt_of_le_of_ne hrH hrne
        rw [hqeq]
        simpa only [pow_two] using mul_lt_mul_of_pos_left hrstrict hHpos
    have hsep := rational_separation_scaled hne
    have hh := mul_lt_mul_of_pos_left hproduct hdiff
    nlinarith only [hsep,hh]

                                                                 
                                                                    
theorem exists_finite_farey_seed {H : ℤ} (hH : 2 ≤ H) :
    ∃ B : Finset ℝ,
      (∀ x, x ∈ B ↔ ∃ q : ℚ, x=(q:ℝ) ∧ (q.den:ℤ) ≤ H ∧
        (q:ℝ) ∈ Icc (0:ℝ) 1) ∧
      (∀ x ∈ B, ∀ y ∈ B, x ≠ y → 1/(H:ℝ)^2 < |x-y|) := by
  classical
  let grid : Finset (ℤ × ℤ) := (Finset.Icc (0:ℤ) H) ×ˢ (Finset.Icc (1:ℤ) H)
  let Q : Finset ℚ := (grid.image (fun p => Rat.divInt p.1 p.2)).filter
    (fun q : ℚ => (q:ℝ) ≤ 1)
  let B : Finset ℝ := Q.image (fun q : ℚ => (q:ℝ))
  have hQ (q : ℚ) : q ∈ Q ↔ (q.den:ℤ) ≤ H ∧ (q:ℝ) ∈ Icc (0:ℝ) 1 := by
    constructor
    · intro hq
      obtain ⟨hm,hq1⟩ := Finset.mem_filter.mp hq
      obtain ⟨p,hp,hpq⟩ := Finset.mem_image.mp hm
      have hpgrid := Finset.mem_product.mp hp
      have hpn := Finset.mem_Icc.mp hpgrid.1
      have hpd := Finset.mem_Icc.mp hpgrid.2
      have hden : ((Rat.divInt p.1 p.2).den:ℤ) ≤ p.2 :=
        Int.le_of_dvd (by omega) (Rat.den_dvd p.1 p.2)
      rw [hpq] at hden
      refine ⟨hden.trans hpd.2,?_,hq1⟩
      rw [←hpq,Rat.cast_divInt]
      exact div_nonneg (by exact_mod_cast hpn.1) (by exact_mod_cast (show 0 ≤ p.2 by omega))
    · rintro ⟨hqH,hq0,hq1⟩
      have hden : (0:ℝ) < q.den := by exact_mod_cast q.den_pos
      have hnum0 : (0:ℤ) ≤ q.num := by
        have hh : (0:ℝ) ≤ q.num := by
          have hh := (le_div_iff₀ hden).mp (show (0:ℝ) ≤ (q.num:ℝ)/q.den by
            simpa only [Rat.cast_def] using hq0)
          simpa only [zero_mul] using hh
        exact_mod_cast hh
      have hnumden : q.num ≤ (q.den:ℤ) := by
        have hh : (q.num:ℝ) ≤ q.den := (div_le_one hden).mp
          (by simpa only [Rat.cast_def] using hq1)
        exact_mod_cast hh
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨(q.num,q.den),?_,?_⟩,hq1⟩
      · exact Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨hnum0,hnumden.trans hqH⟩,
            Finset.mem_Icc.mpr ⟨by change 1 ≤ (q.den:ℤ); exact_mod_cast q.den_pos,hqH⟩⟩
      · apply Rat.cast_injective (α:=ℝ)
        rw [Rat.cast_divInt,Int.cast_natCast,Rat.cast_def q]
  have hB x : x ∈ B ↔ ∃ q : ℚ, x=(q:ℝ) ∧ (q.den:ℤ) ≤ H ∧
      (q:ℝ) ∈ Icc (0:ℝ) 1 := by
    constructor
    · intro hx
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
      exact ⟨q,rfl,(hQ q).mp hq⟩
    · rintro ⟨q,rfl,hq⟩
      exact Finset.mem_image_of_mem _ ((hQ q).mpr hq)
  refine ⟨B,hB,?_⟩
  intro x hx y hy hne
  obtain ⟨q,rfl,hq,_⟩ := (hB x).mp hx
  obtain ⟨r,rfl,hr,_⟩ := (hB y).mp hy
  apply bounded_denominator_strict_separation hH hq hr
  intro he
  exact hne (congrArg (fun t : ℚ => (t:ℝ)) he)

                                                                      
                                                                       
                                                                
theorem exists_unit_reference_candidate {δ : ℝ} {H : ℤ}
    (hδ : 0 < δ) (hH : 2 ≤ H)
    (hscale : ∀ b d : ℤ, 0 < b → b ≤ H → 0 < d → d ≤ H → H < b+d →
      1 ≤ δ*((max b d:ℤ):ℝ)^2 ∧ δ/4 ≤ 1/((b:ℝ)*d))
    {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    ∃ z ∈ Icc (0:ℝ) 1, |x-z| ≤ 5*δ/4 ∧
      ((∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ H) ∨
       (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
         1 ≤ δ*(n:ℝ)^2 ∧ 0 < v ∧ v ≤ H ∧
         (u:ℝ)/v ∈ Icc (0:ℝ) 1 ∧ |m*v-u*n|=1)) := by
  by_cases hx1 : x=1
  · refine ⟨1,by norm_num,?_,Or.inl ⟨1,by norm_num,by norm_num; omega⟩⟩
    rw [hx1]
    simp only [sub_self,abs_zero]
    positivity
  have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
  obtain ⟨a,b,c,d,hb,hbH,hd,hdH,hsum,_hcopb,_hcopd,hdet,hleft,hright,hgap⟩ :=
    exists_farey_bracket (show 1 ≤ H by omega) x
  have hbpos : 0 < b := by omega
  have hdpos : 0 < d := by omega
  have hbR : (0:ℝ) < b := by exact_mod_cast hbpos
  have hdR : (0:ℝ) < d := by exact_mod_cast hdpos
  obtain ⟨ha0,hcd⟩ := farey_bracket_unit_bounds hbpos hdpos hdet ⟨hx.1,hxlt⟩ hleft hright
  have hleftI : (a:ℝ)/b ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg (by exact_mod_cast ha0) hbR.le,hleft.trans hx.2⟩
  have hrightI : (c:ℝ)/d ∈ Icc (0:ℝ) 1 :=
    ⟨hx.1.trans hright.le,(div_le_one hdR).mpr (by exact_mod_cast hcd)⟩
  obtain ⟨hmax,hmin⟩ := hscale b d hbpos hbH hdpos hdH hsum
  obtain ⟨S,_haS,_hcS,hSI,hlabels,_hsep,hcover,_hadj⟩ :=
    exists_farey_reference_refinement hbpos hdpos hdet hδ hmax
      (by simpa only [hgap] using hmin)
  obtain ⟨z,hz,hnear⟩ := hcover x ⟨hleft,hright.le⟩
  have hzI : z ∈ Icc (0:ℝ) 1 :=
    ⟨hleftI.1.trans (hSI z hz).1,(hSI z hz).2.trans hrightI.2⟩
  refine ⟨z,hzI,hnear,?_⟩
  by_cases hza : z=(a:ℝ)/b
  · left
    refine ⟨Rat.divInt a b,?_,?_⟩
    · simpa only [Rat.cast_divInt] using hza
    · exact (Int.le_of_dvd hbpos (Rat.den_dvd a b)).trans hbH
  by_cases hzc : z=(c:ℝ)/d
  · left
    refine ⟨Rat.divInt c d,?_,?_⟩
    · simpa only [Rat.cast_divInt] using hzc
    · exact (Int.le_of_dvd hdpos (Rat.den_dvd c d)).trans hdH
  right
  obtain ⟨m,n,u,v,hzval,hcop,hnmax,huv,hdetmn⟩ := hlabels z hz hza hzc
  have hmaxpos : 0 < max b d := hbpos.trans_le (le_max_left b d)
  have hnpos : 0 < n := hmaxpos.trans_le hnmax
  have hnscale : 1 ≤ δ*(n:ℝ)^2 := by
    apply hmax.trans
    have hmaxR : (0:ℝ) ≤ ((max b d:ℤ):ℝ) := by exact_mod_cast hmaxpos.le
    have hnmaxR : ((max b d:ℤ):ℝ) ≤ (n:ℝ) := by exact_mod_cast hnmax
    gcongr
  refine ⟨m,n,u,v,hzval,hcop,hnpos,hnscale,?_⟩
  rcases huv with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨hbpos,hbH,hleftI,hdetmn⟩
  · exact ⟨hdpos,hdH,hrightI,hdetmn⟩

                                                                  
                                                                    
                                                                      
                                                                  
theorem exists_unit_reference_system {δ : ℝ} {H : ℤ}
    (hδ : 0 < δ) (hH : 2 ≤ H)
    (hscale : ∀ b d : ℤ, 0 < b → b ≤ H → 0 < d → d ≤ H → H < b+d →
      1 ≤ δ*((max b d:ℤ):ℝ)^2 ∧ δ/4 ≤ 1/((b:ℝ)*d)) :
    ∃ S : Finset ℝ,
      (∀ q : ℚ, (q.den:ℤ) ≤ H → (q:ℝ) ∈ Icc (0:ℝ) 1 → (q:ℝ) ∈ S) ∧
      (∀ z ∈ S, z ∈ Icc (0:ℝ) 1) ∧
      (∀ z ∈ S,
        (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ H) ∨
        (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
          1 ≤ δ*(n:ℝ)^2 ∧ 0 < v ∧ v ≤ H ∧
          (u:ℝ)/v ∈ Icc (0:ℝ) 1 ∧ |m*v-u*n|=1)) ∧
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/4 < |x-y|) ∧
      (∀ x ∈ Icc (0:ℝ) 1, ∃ y ∈ S, |x-y| ≤ 7*δ/4) ∧
      (∀ x ∈ S, ∀ y ∈ S, x < y →
        (∀ z ∈ S, ¬ (x < z ∧ z < y)) →
        δ/4 < y-x ∧ y-x ≤ 7*δ/2) := by
  classical
  let C : Set ℝ := {z | z ∈ Icc (0:ℝ) 1 ∧
    ((∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ H) ∨
     (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
       1 ≤ δ*(n:ℝ)^2 ∧ 0 < v ∧ v ≤ H ∧
       (u:ℝ)/v ∈ Icc (0:ℝ) 1 ∧ |m*v-u*n|=1))}
  have hCcover : Icc (0:ℝ) 1 ⊆ ⋃ z ∈ C, Metric.ball z (3*δ/2) := by
    intro x hx
    obtain ⟨z,hzI,hnear,hlabel⟩ := exists_unit_reference_candidate hδ hH hscale hx
    apply Set.mem_iUnion.mpr
    refine ⟨z,Set.mem_iUnion.mpr ⟨⟨hzI,hlabel⟩,?_⟩⟩
    rw [Metric.mem_ball,Real.dist_eq]
    linarith only [hnear,hδ]
  obtain ⟨A,hAC,hAfin,hAcover⟩ :=
    isCompact_Icc.elim_finite_subcover_image (fun z (_hz : z ∈ C) => Metric.isOpen_ball) hCcover
  obtain ⟨B,hB,hBsep⟩ := exists_finite_farey_seed hH
  have hBC : (B : Set ℝ) ⊆ C := by
    intro z hz
    obtain ⟨q,rfl,hqH,hqI⟩ := (hB z).mp hz
    exact ⟨hqI,Or.inl ⟨q,rfl,hqH⟩⟩
  let ε : NNReal := ⟨δ/4,by positivity⟩
  have hseedSep : Metric.IsSeparated ε (B : Set ℝ) := by
    intro x hx y hy hne
    rw [edist_dist,Real.dist_eq,ENNReal.coe_lt_ofReal]
    change δ/4 < |x-y|
    have hHpos : 0 < H := by omega
    have hh := (hscale H H hHpos le_rfl hHpos le_rfl (by omega)).2
    have hbound : δ/4 ≤ 1/(H:ℝ)^2 := by simpa only [pow_two] using hh
    exact hbound.trans_lt (hBsep x hx y hy hne)
  obtain ⟨N,hBN,hNA,hNfin,hNsep,hNcover⟩ :=
    exists_seeded_separated_reference_cover (A ∪ (B : Set ℝ)) (B : Set ℝ) ε
      (hAfin.union B.finite_toSet) Set.subset_union_right hseedSep
  let S := hNfin.toFinset
  have hNS z : z ∈ S ↔ z ∈ N := hNfin.mem_toFinset
  have hSC z (hz : z ∈ S) : z ∈ C := by
    rcases hNA ((hNS z).mp hz) with hzA | hzB
    · exact hAC hzA
    · exact hBC hzB
  have hpoints z (hz : z ∈ S) : z ∈ Icc (0:ℝ) 1 := (hSC z hz).1
  have hsep x (hx : x ∈ S) y (hy : y ∈ S) (hne : x ≠ y) : δ/4 < |x-y| := by
    have hh := hNsep ((hNS x).mp hx) ((hNS y).mp hy) hne
    change (ε:ENNReal) < edist x y at hh
    rw [edist_dist,Real.dist_eq,ENNReal.coe_lt_ofReal] at hh
    exact hh
  have hnet x (hx : x ∈ Icc (0:ℝ) 1) :
      ∃ y ∈ S, |x-y| ≤ 7*δ/4 := by
    obtain ⟨z,hz⟩ := Set.mem_iUnion.mp (hAcover hx)
    obtain ⟨hzA,hxz⟩ := Set.mem_iUnion.mp hz
    have hdist : |x-z| < 3*δ/2 := by simpa only [Metric.mem_ball,Real.dist_eq] using hxz
    obtain ⟨y,hy,hzy⟩ := hNcover (Or.inl hzA)
    have hdist2 : |z-y| ≤ δ/4 := by
      change edist z y ≤ (ε:ENNReal) at hzy
      rw [edist_dist,Real.dist_eq,ENNReal.ofReal_le_coe] at hzy
      exact hzy
    refine ⟨y,(hNS y).mpr hy,?_⟩
    calc
      _ ≤ |x-z|+|z-y| := abs_sub_le x z y
      _ ≤ 3*δ/2+δ/4 := add_le_add hdist.le hdist2
      _ = _ := by ring
  refine ⟨S,?_,hpoints,(fun z hz => (hSC z hz).2),hsep,hnet,?_⟩
  · intro q hqH hqI
    exact (hNS _).mpr (hBN ((hB _).mpr ⟨q,rfl,hqH,hqI⟩))
  · intro x hx y hy hxy hadj
    refine ⟨?_,?_⟩
    · have hh := hsep y hy x hx hxy.ne'
      simpa only [abs_of_pos (sub_pos.mpr hxy)] using hh
    have hmid : (x+y)/2 ∈ Icc (0:ℝ) 1 := by
      have hxI := hpoints x hx
      have hyI := hpoints y hy
      constructor <;> linarith only [hxI.1,hyI.2,hxy]
    obtain ⟨z,hz,hzdist⟩ := hnet _ hmid
    have hzabs := abs_le.mp hzdist
    by_cases hxz : x < z
    · have hyz : y ≤ z := le_of_not_gt (fun hzy => hadj z hz ⟨hxz,hzy⟩)
      linarith only [hzabs.1,hyz]
    · have hzx : z ≤ x := le_of_not_gt hxz
      linarith only [hzabs.2,hzx]

                                                             
                                                                        
                                                                         
                                                  
theorem reference_adjacent_denominator_scale (S : Finset ℝ) {δ L U : ℝ} {H : ℤ}
    (hδ : 0 < δ)
    (hseed : ∀ q : ℚ, (q.den:ℤ) ≤ H → (q:ℝ) ∈ Icc L U → (q:ℝ) ∈ S)
    (hpoints : ∀ z ∈ S, z ∈ Icc L U)
    (hscale : ∀ b d : ℤ, 0 < b → b ≤ H → 0 < d → d ≤ H → H < b+d →
      1 ≤ δ*((max b d:ℤ):ℝ)^2)
    {a b c d : ℤ} (hb : 0 < b) (hd : 0 < d)
    (haS : (a:ℝ)/b ∈ S) (hcS : (c:ℝ)/d ∈ S)
    (hac : (a:ℝ)/b < (c:ℝ)/d)
    (hadj : ∀ z ∈ S, ¬ ((a:ℝ)/b < z ∧ z < (c:ℝ)/d))
    (hbcase : b ≤ H ∨ 1 ≤ δ*(b:ℝ)^2)
    (hdcase : d ≤ H ∨ 1 ≤ δ*(d:ℝ)^2) :
    1 ≤ δ*((max b d:ℤ):ℝ)^2 := by
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hbmax : (b:ℝ) ≤ ((max b d:ℤ):ℝ) := by exact_mod_cast le_max_left b d
  have hdmax : (d:ℝ) ≤ ((max b d:ℤ):ℝ) := by exact_mod_cast le_max_right b d
  rcases hbcase with hbH | hbscale
  · rcases hdcase with hdH | hdscale
    · apply hscale b d hb hbH hd hdH
      by_contra hbad
      have hsum : b+d ≤ H := le_of_not_gt hbad
      have hsumpos : 0 < b+d := add_pos hb hd
      have hsumR : (0:ℝ) < (b:ℝ)+d := add_pos hbR hdR
      have hcross : (a:ℝ)*d < (c:ℝ)*b := (div_lt_div_iff₀ hbR hdR).mp hac
      let q : ℚ := Rat.divInt (a+c) (b+d)
      have hqval : (q:ℝ)=((a:ℝ)+c)/((b:ℝ)+d) := by
        simp only [q,Rat.cast_divInt,Int.cast_add]
      have hleft : (a:ℝ)/b < (q:ℝ) := by
        rw [hqval]
        apply (div_lt_div_iff₀ hbR hsumR).mpr
        nlinarith only [hcross]
      have hright : (q:ℝ) < (c:ℝ)/d := by
        rw [hqval]
        apply (div_lt_div_iff₀ hsumR hdR).mpr
        nlinarith only [hcross]
      have hqden : (q.den:ℤ) ≤ H :=
        (Int.le_of_dvd hsumpos (Rat.den_dvd (a+c) (b+d))).trans hsum
      have hqI : (q:ℝ) ∈ Icc L U :=
        ⟨(hpoints _ haS).1.trans hleft.le,hright.le.trans (hpoints _ hcS).2⟩
      exact hadj q (hseed q hqden hqI) ⟨hleft,hright⟩
    · apply hdscale.trans
      gcongr
  · apply hbscale.trans
    gcongr

                                                                       
                                                                     
                                                                       
                                            
theorem integer_translate_reference_separation (S : Finset ℝ) {ε : ℝ}
    (hzero : (0:ℝ) ∈ S) (hone : (1:ℝ) ∈ S)
    (hpoints : ∀ z ∈ S, z ∈ Icc (0:ℝ) 1)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ε < |x-y|)
    {i j : ℤ} {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S)
    (hne : (i:ℝ)+x ≠ (j:ℝ)+y) :
    ε < |((i:ℝ)+x)-((j:ℝ)+y)| := by
  have h01 : ε < 1 := by simpa only [sub_zero,abs_one] using hsep 1 hone 0 hzero one_ne_zero
  have hordered (i j : ℤ) (x y : ℝ) (hx : x ∈ S) (hy : y ∈ S)
      (hij : i < j) (hne : (i:ℝ)+x ≠ (j:ℝ)+y) :
      ε < ((j:ℝ)+y)-((i:ℝ)+x) := by
    have hxI := hpoints x hx
    have hyI := hpoints y hy
    have hijR : (i:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast (show i+1 ≤ j by omega)
    by_cases hx1 : x=1
    · by_cases hy0 : y=0
      · have hij2 : i+2 ≤ j := by
          by_contra hbad
          have he : j=i+1 := by omega
          apply hne
          rw [he,hx1,hy0,Int.cast_add,Int.cast_one,add_zero]
        have hij2R : (i:ℝ)+2 ≤ (j:ℝ) := by exact_mod_cast hij2
        linarith only [h01,hij2R,hx1,hy0]
      · have hh := hsep y hy 0 hzero hy0
        rw [sub_zero,abs_of_nonneg hyI.1] at hh
        linarith only [hh,hijR,hx1]
    · have hh := hsep 1 hone x hx (Ne.symm hx1)
      rw [abs_of_nonneg (sub_nonneg.mpr hxI.2)] at hh
      linarith only [hh,hijR,hyI.1]
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hh := (hordered i j x y hx hy hij hne).trans_le (le_abs_self _)
    simpa only [abs_sub_comm] using hh
  · have hxy : x ≠ y := by intro he; exact hne (congrArg (fun t => (i:ℝ)+t) he)
    have he : (i:ℝ)+x-((i:ℝ)+y)=x-y := by ring
    rw [he]
    exact hsep x hx y hy hxy
  · have hh := (hordered j i y x hy hx hji hne.symm).trans_le (le_abs_self _)
    simpa only [abs_sub_comm] using hh

                                                                      
                                                                      
                                                                        
                                            
theorem exists_source_interval_reference_system {δ : ℝ}
    (hδ : 0 < δ) (hδmax : δ ≤ 1) :
    ∃ H : ℤ, 2 ≤ H ∧ ∀ L U : ℤ, L ≤ U →
      ∃ T : Finset ℝ,
        (∀ q : ℚ, (q.den:ℤ) ≤ H →
          (q:ℝ) ∈ Icc (L:ℝ) ((U:ℝ)+1) → (q:ℝ) ∈ T) ∧
        (∀ z ∈ T, z ∈ Icc (L:ℝ) ((U:ℝ)+1)) ∧
        (∀ z ∈ T,
          (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ H) ∨
          (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
            1 ≤ δ*(n:ℝ)^2 ∧ 0 < v ∧ v ≤ H ∧
            (u:ℝ)/v ∈ Icc (L:ℝ) ((U:ℝ)+1) ∧ |m*v-u*n|=1)) ∧
        (∀ x ∈ T, ∀ y ∈ T, x ≠ y → δ/4 < |x-y|) ∧
        (∀ x ∈ Icc (L:ℝ) ((U:ℝ)+1), ∃ y ∈ T, |x-y| ≤ 7*δ/4) ∧
        (∀ x ∈ T, ∀ y ∈ T, x < y →
          (∀ z ∈ T, ¬ (x < z ∧ z < y)) →
          δ/4 < y-x ∧ y-x ≤ 7*δ/2 ∧
          ∃ a b c d : ℤ, x=(a:ℝ)/b ∧ y=(c:ℝ)/d ∧
            IsCoprime a b ∧ IsCoprime c d ∧ 0 < b ∧ 0 < d ∧
            1 ≤ δ*((max b d:ℤ):ℝ)^2) := by
  classical
  obtain ⟨H,hH,hscale⟩ := exists_source_farey_order hδ hδmax
  obtain ⟨S,hseed,hpoints,hlabels,hsep,hcover,_hgaps⟩ :=
    exists_unit_reference_system hδ hH hscale
  have hzero : (0:ℝ) ∈ S := by
    simpa only [Rat.cast_zero] using hseed 0 (by norm_num; omega) (by norm_num)
  have hone : (1:ℝ) ∈ S := by
    simpa only [Rat.cast_one] using hseed 1 (by norm_num; omega) (by norm_num)
  refine ⟨H,hH,?_⟩
  intro L U hLU
  let T : Finset ℝ := ((Finset.Icc L U) ×ˢ S).image (fun p : ℤ × ℝ => (p.1:ℝ)+p.2)
  have hT z : z ∈ T ↔ ∃ j ∈ Finset.Icc L U, ∃ s ∈ S, z=(j:ℝ)+s := by
    constructor
    · intro hz
      obtain ⟨⟨j,s⟩,hjs,hval⟩ := Finset.mem_image.mp hz
      have hjs' := Finset.mem_product.mp hjs
      exact ⟨j,hjs'.1,s,hjs'.2,hval.symm⟩
    · rintro ⟨j,hj,s,hs,hval⟩
      exact Finset.mem_image.mpr ⟨(j,s),Finset.mem_product.mpr ⟨hj,hs⟩,hval.symm⟩
  have hcell x (hx : x ∈ Icc (L:ℝ) ((U:ℝ)+1)) :
      ∃ j ∈ Finset.Icc L U, x-(j:ℝ) ∈ Icc (0:ℝ) 1 := by
    by_cases hxU : x=(U:ℝ)+1
    · refine ⟨U,Finset.mem_Icc.mpr ⟨hLU,le_rfl⟩,?_⟩
      rw [hxU]
      constructor <;> linarith
    have hxlt : x < (U:ℝ)+1 := lt_of_le_of_ne hx.2 hxU
    have hjL : L ≤ Int.floor x := Int.le_floor.mpr hx.1
    have hjU : Int.floor x ≤ U := by
      have hh : Int.floor x < U+1 := Int.floor_lt.mpr (by simpa only [Int.cast_add,Int.cast_one] using hxlt)
      omega
    refine ⟨Int.floor x,Finset.mem_Icc.mpr ⟨hjL,hjU⟩,?_⟩
    constructor
    · linarith only [Int.floor_le x]
    · linarith only [Int.lt_floor_add_one x]
  have hTpoints z (hz : z ∈ T) : z ∈ Icc (L:ℝ) ((U:ℝ)+1) := by
    obtain ⟨j,hj,s,hs,rfl⟩ := (hT z).mp hz
    have hjI := Finset.mem_Icc.mp hj
    have hjL : (L:ℝ) ≤ j := by exact_mod_cast hjI.1
    have hjU : (j:ℝ) ≤ U := by exact_mod_cast hjI.2
    have hsI := hpoints s hs
    constructor <;> linarith only [hjL,hjU,hsI.1,hsI.2]
  have hTseed (q : ℚ) (hqH : (q.den:ℤ) ≤ H)
      (hqI : (q:ℝ) ∈ Icc (L:ℝ) ((U:ℝ)+1)) : (q:ℝ) ∈ T := by
    obtain ⟨j,hj,hlocal⟩ := hcell q hqI
    have hden : ((q-(j:ℚ)).den:ℤ) ≤ H := by simpa only [Rat.sub_intCast_den] using hqH
    have hlocal' : ((q-(j:ℚ):ℚ):ℝ) ∈ Icc (0:ℝ) 1 := by
      simpa only [Rat.cast_sub,Rat.cast_intCast] using hlocal
    refine (hT _).mpr ⟨j,hj,(q-(j:ℚ):ℚ),hseed _ hden hlocal',?_⟩
    simp only [Rat.cast_sub,Rat.cast_intCast]
    ring
  have hTlabels z (hz : z ∈ T) :
      (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ H) ∨
      (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
        1 ≤ δ*(n:ℝ)^2 ∧ 0 < v ∧ v ≤ H ∧
        (u:ℝ)/v ∈ Icc (L:ℝ) ((U:ℝ)+1) ∧ |m*v-u*n|=1) := by
    obtain ⟨j,hj,s,hs,rfl⟩ := (hT z).mp hz
    rcases hlabels s hs with ⟨q,hq,hqH⟩ | ⟨m,n,u,v,hval,hcop,hn,hnscale,hv,hvH,huI,hdet⟩
    · left
      refine ⟨(j:ℚ)+q,?_,?_⟩
      · simp only [Rat.cast_add,Rat.cast_intCast,hq]
      · simpa only [Rat.intCast_add_den] using hqH
    · right
      have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have hvR : (v:ℝ) ≠ 0 := by exact_mod_cast hv.ne'
      have hnum : (j:ℝ)+s=((m+j*n:ℤ):ℝ)/n := by
        rw [hval]
        push_cast
        field_simp
        ring
      have hneighbor : ((u+j*v:ℤ):ℝ)/v=(j:ℝ)+(u:ℝ)/v := by
        push_cast
        field_simp
        ring
      have hjI := Finset.mem_Icc.mp hj
      have hjL : (L:ℝ) ≤ j := by exact_mod_cast hjI.1
      have hjU : (j:ℝ) ≤ U := by exact_mod_cast hjI.2
      refine ⟨m+j*n,n,u+j*v,v,hnum,hcop.add_mul_right_left j,hn,hnscale,hv,hvH,?_,?_⟩
      · rw [hneighbor]
        constructor <;> linarith only [hjL,hjU,huI.1,huI.2]
      · convert hdet using 1
        congr 1
        ring
  have hTsep x (hx : x ∈ T) y (hy : y ∈ T) (hne : x ≠ y) : δ/4 < |x-y| := by
    obtain ⟨i,hi,s,hs,rfl⟩ := (hT x).mp hx
    obtain ⟨j,hj,t,ht,rfl⟩ := (hT y).mp hy
    exact integer_translate_reference_separation S hzero hone hpoints hsep hs ht hne
  have hTcover x (hx : x ∈ Icc (L:ℝ) ((U:ℝ)+1)) :
      ∃ y ∈ T, |x-y| ≤ 7*δ/4 := by
    obtain ⟨j,hj,hlocal⟩ := hcell x hx
    obtain ⟨s,hs,hnear⟩ := hcover _ hlocal
    refine ⟨(j:ℝ)+s,(hT _).mpr ⟨j,hj,s,hs,rfl⟩,?_⟩
    have he : x-((j:ℝ)+s)=(x-(j:ℝ))-s := by ring
    simpa only [he] using hnear
  have hlabel z (hz : z ∈ T) :
      ∃ a b : ℤ, z=(a:ℝ)/b ∧ IsCoprime a b ∧ 0 < b ∧
        (b ≤ H ∨ 1 ≤ δ*(b:ℝ)^2) := by
    rcases hTlabels z hz with ⟨q,hq,hqH⟩ | ⟨m,n,u,v,hval,hcop,hn,hnscale,_⟩
    · refine ⟨q.num,q.den,?_,q.isCoprime_num_den,?_,Or.inl hqH⟩
      · simpa only [Rat.cast_def,Int.cast_natCast] using hq
      · exact_mod_cast q.den_pos
    · exact ⟨m,n,hval,hcop,hn,Or.inr hnscale⟩
  refine ⟨T,hTseed,hTpoints,hTlabels,hTsep,hTcover,?_⟩
  intro x hx y hy hxy hadj
  have hlower : δ/4 < y-x := by
    simpa only [abs_of_pos (sub_pos.mpr hxy)] using hTsep y hy x hx hxy.ne'
  have hupper : y-x ≤ 7*δ/2 := by
    have hmid : (x+y)/2 ∈ Icc (L:ℝ) ((U:ℝ)+1) := by
      have hxI := hTpoints x hx
      have hyI := hTpoints y hy
      constructor <;> linarith only [hxI.1,hyI.2,hxy]
    obtain ⟨z,hz,hzdist⟩ := hTcover _ hmid
    have hzabs := abs_le.mp hzdist
    by_cases hxz : x < z
    · have hyz : y ≤ z := le_of_not_gt (fun hzy => hadj z hz ⟨hxz,hzy⟩)
      linarith only [hzabs.1,hyz]
    · have hzx : z ≤ x := le_of_not_gt hxz
      linarith only [hzabs.2,hzx]
  obtain ⟨a,b,hxval,hcopb,hb,hbcase⟩ := hlabel x hx
  obtain ⟨c,d,hyval,hcopd,hd,hdcase⟩ := hlabel y hy
  refine ⟨hlower,hupper,a,b,c,d,hxval,hyval,hcopb,hcopd,hb,hd,?_⟩
  apply reference_adjacent_denominator_scale T (a:=a) (c:=c) hδ hTseed hTpoints
    (fun b d hb hbH hd hdH hsum => (hscale b d hb hbH hd hdH hsum).1)
    hb hd (by simpa only [←hxval] using hx) (by simpa only [←hyval] using hy)
    (by simpa only [←hxval,←hyval] using hxy)
    (by simpa only [←hxval,←hyval] using hadj) hbcase hdcase

                                                                   
                                                                      
                                                                    
                                                   
theorem positive_difference_reference_preimage_width
    (F : ℝ → ℝ) {σ c η y T M N R U x z : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hy : y ∈ Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hphase : T*N*R^2=M^3)
    (hx : x ∈ Icc M (2*M)) (hz : z ∈ Icc M (2*M)) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    |iteratedDeriv 2 f z/2-iteratedDeriv 2 f x/2| ≤ 7*U/(2*R^2) →
    |z-x| ≤ (14*σ/c)*U*N := by
  intro f hgap
  let L := c*T/(4*σ*M^3)
  have hL : 0 < L := by dsimp only [L]; positivity
  have hnorm w (hw : w ∈ Icc M (2*M)) : w/M ∈ Icc (3/4:ℝ) (9/4) := by
    constructor
    · apply (le_div_iff₀ hM).mpr
      linarith only [hw.1,hM]
    · apply (div_le_iff₀ hM).mpr
      linarith only [hw.2,hM]
  have hcf w (hw : w ∈ Icc M (2*M)) : ContDiffAt ℝ 3 f w := by
    have hw0 : 0 < w/M := div_pos (hM.trans_le hw.1) hM
    have hs0 : 0 < w/M+η*y := add_pos hw0 (mul_pos hη (by linarith only [hy.1]))
    exact (contDiffAt_const.mul (((hf _ hw0).comp w (contDiffAt_id.div_const M)).sub
      ((hf _ hs0).comp w ((contDiffAt_id.div_const M).add contDiffAt_const)))).div_const
      (σ*η) |>.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hd w (hw : w ∈ Icc M (2*M)) :
      HasDerivAt (fun u => iteratedDeriv 2 f u/2) (iteratedDeriv 3 f w/2) w :=
    (hasDerivAt_iteratedDeriv_finite (by norm_num : 2 < 3) (hcf w hw)).div_const 2
  have hlower w (hw : w ∈ Icc M (2*M)) : L ≤ |iteratedDeriv 3 f w/2| := by
    have hid : iteratedDeriv 3 f w=
        T/M^3*((iteratedDeriv 3 F (w/M)-iteratedDeriv 3 F (w/M+η*y))/(σ*η)) :=
      positive_difference_physical_iteratedDeriv F hM (hM.trans_le hw.1)
        (mul_nonneg hη.le (by linarith only [hy.1])) hf 3
    have hlow := positive_difference_third_signed_lower F (y:=y) hσ hη hηmax hc
      (hnorm w hw) ⟨by linarith only [hy.1],by linarith only [hy.2]⟩ hf hnegative
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlow (show 0 ≤ T/M^3 by positivity))
      (by norm_num : (0:ℝ) ≤ 2)
    have hh' : L ≤ iteratedDeriv 3 f w/2 := by
      rw [hid]
      have he : L=(T/M^3)*(c/(2*σ))/2 := by dsimp only [L]; ring
      rw [he]
      exact hh
    exact hh'.trans (le_abs_self _)
  have hcomp := interval_abs_derivative_lower
    (fun u => iteratedDeriv 2 f u/2) (fun u => iteratedDeriv 3 f u/2)
    hx hz hd hlower
  have hbound := hcomp.trans hgap
  calc
    _ ≤ (7*U/(2*R^2))/L := (le_div_iff₀ hL).mpr (by simpa only [mul_comm] using hbound)
    _ = (14*σ/c)*U*N := by
      dsimp only [L]
      rw [←hphase]
      field_simp
      ring

                                                                     
                                                                     
                                                                         
                                                                    
theorem positive_difference_constructed_reference_system
    (F : ℝ → ℝ) {σ c J η T M N R U : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (htests : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hU : 0 < U) (hUmax : U ≤ R^2) (hphase : T*N*R^2=M^3) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let curvatureScale := 3*J*T/(2*σ*M^2)
    ∃ H : ℤ, 2 ≤ H ∧ ∃ S : Finset ℝ,
      (∀ q : ℚ, (q.den:ℤ) ≤ H → |(q:ℝ)| ≤ curvatureScale → (q:ℝ) ∈ S) ∧
      (∀ a ∈ S, ∀ b ∈ S, ∀ q : ℚ, (q.den:ℤ) ≤ H →
        (q:ℝ) ∈ Icc a b → (q:ℝ) ∈ S) ∧
      (∃ l ∈ S, ∃ u ∈ S, l ≤ -curvatureScale ∧ curvatureScale ≤ u) ∧
      (∀ z ∈ S, |z| ≤ curvatureScale+1) ∧
      (∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M), |h y x| ≤ curvatureScale) ∧
      (∀ z ∈ S,
        (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ H) ∨
        (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
          R^2 ≤ U*(n:ℝ)^2 ∧ 0 < v ∧ v ≤ H ∧ (u:ℝ)/v ∈ S ∧ |m*v-u*n|=1)) ∧
      (∀ x ∈ S, ∀ z ∈ S, x ≠ z → U/(4*R^2) < |x-z|) ∧
      (∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M),
        ∃ q ∈ S, |h y x-q| ≤ 7*U/(4*R^2)) ∧
      (∀ y ∈ Icc (1:ℝ) 2, ∀ q ∈ S,
        q ∈ Icc (h y M) (h y (2*M)) →
        ∃ x ∈ Icc M (2*M), h y x=q) ∧
      (∀ a ∈ S, ∀ b ∈ S, a < b →
        (∀ z ∈ S, ¬ (a < z ∧ z < b)) →
        U/(4*R^2) < b-a ∧ b-a ≤ 7*U/(2*R^2) ∧
        (∃ m n u v : ℤ, a=(m:ℝ)/n ∧ b=(u:ℝ)/v ∧
          IsCoprime m n ∧ IsCoprime u v ∧ 0 < n ∧ 0 < v ∧
          R^2 ≤ U*((max n v:ℤ):ℝ)^2) ∧
        (∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M), ∀ z ∈ Icc M (2*M),
          h y x=a → h y z=b → |z-x| ≤ (14*σ/c)*U*N)) := by
  intro f h curvatureScale
  let δ := U/R^2
  have hδ : 0 < δ := div_pos hU (sq_pos_of_pos hR)
  have hδmax : δ ≤ 1 := (div_le_one (sq_pos_of_pos hR)).mpr hUmax
  have hcurvpos : 0 ≤ curvatureScale := by dsimp only [curvatureScale]; positivity
  let L : ℤ := Int.floor (-curvatureScale)
  let V : ℤ := Int.floor curvatureScale
  have hLV : L ≤ V := Int.floor_mono (by linarith only [hcurvpos])
  obtain ⟨H,hH,hbuild⟩ := exists_source_interval_reference_system hδ hδmax
  obtain ⟨S,hseed,hpoints,hlabels,hsep,hcover,hgaps⟩ := hbuild L V hLV
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
  have hscaled (n : ℤ) (hn : 1 ≤ δ*(n:ℝ)^2) : R^2 ≤ U*(n:ℝ)^2 := by
    have hh : 1 ≤ U*(n:ℝ)^2/R^2 := by dsimp only [δ] at hn; convert hn using 1; ring
    simpa only [one_mul] using (le_div_iff₀ (sq_pos_of_pos hR)).mp hh
  have hcurv y x (hy : y ∈ Icc (1:ℝ) 2) (hx : x ∈ Icc M (2*M)) :
      |h y x| ≤ curvatureScale := by
    have hnorm : x/M ∈ Icc (3/4:ℝ) (9/4) := by
      constructor
      · apply (le_div_iff₀ hM).mpr
        linarith only [hx.1,hM]
      · apply (div_le_iff₀ hM).mpr
        linarith only [hx.2,hM]
    have hy' : y ∈ Icc (1/2:ℝ) 3 :=
      ⟨by linarith only [hy.1],by linarith only [hy.2]⟩
    have hj := positive_jets_difference_curvature_entry F hσ hc hJ hη hηmax hnorm hy'
      hf hbound htests 3 (by norm_num) (by norm_num)
    have hu := positive_jets_difference_mixed_upper F hσ hJ hη hηmax hnorm hy' hf hbound
      2 0 (by norm_num) (by norm_num)
    simp only [iteratedDeriv_zero] at hu
    have he : iteratedDeriv 2 (fun u => (F u-F (u+η*y))/(σ*η)) (x/M) =
        (iteratedDeriv 2 F (x/M)-iteratedDeriv 2 F (x/M+η*y))/(σ*η) := hj.1
    rw [he] at hu
    have hd := positive_difference_physical_iteratedDeriv F (T:=T) (σ:=σ) hM
      (hM.trans_le hx.1) (mul_nonneg hη.le (by linarith only [hy.1])) hf 2
    dsimp only [h,f]
    rw [hd,abs_div,abs_mul,abs_of_pos (show 0 < T/M^2 by positivity)]
    rw [abs_of_pos (by norm_num : (0:ℝ) < 2)]
    calc
      _ ≤ (T/M^2)*(3*J/σ)/2 := by gcongr
      _ = curvatureScale := by dsimp only [curvatureScale]; ring
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
  refine ⟨H,hH,S,(fun q hqH hq => hseed q hqH (hinside q hq)),
    (fun a ha b hb q hqH hqI => hseed q hqH
      ⟨(hpoints a ha).1.trans hqI.1,hqI.2.trans (hpoints b hb).2⟩),
    ⟨L,hLmem,(V:ℝ)+1,hVmem,Int.floor_le (-curvatureScale),(Int.lt_floor_add_one curvatureScale).le⟩,
    (fun z hz => houtside z (hpoints z hz)),(fun y hy x hx => hcurv y x hy hx),?_,?_,?_,?_,?_⟩
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
      have hs0 : 0 < x/M+η*y := add_pos hx0 (mul_pos hη (by linarith only [hy.1]))
      have hcf : ContDiffAt ℝ 3 (f y) x :=
        (contDiffAt_const.mul (((hf _ hx0).comp x (contDiffAt_id.div_const M)).sub
          ((hf _ hs0).comp x ((contDiffAt_id.div_const M).add contDiffAt_const)))).div_const
          (σ*η) |>.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
      exact ((hasDerivAt_iteratedDeriv_finite (by norm_num : 2 < 3) hcf).div_const 2).continuousAt.continuousWithinAt
    exact intermediate_value_Icc (by linarith only [hM] : M ≤ 2*M) hcont hqI
  · intro a ha b hb hab hadj
    obtain ⟨hlow,hupp,m,n,u,v,haval,hbval,hcopn,hcopv,hn,hv,hmax⟩ :=
      hgaps a ha b hb hab hadj
    refine ⟨by simpa only [hgapLower] using hlow,by simpa only [hgapUpper] using hupp,
      ⟨m,n,u,v,haval,hbval,hcopn,hcopv,hn,hv,hscaled (max n v) hmax⟩,?_⟩
    intro y hy x hx z hz hxa hzb
    apply positive_difference_reference_preimage_width F hσ hc hη hηmax hy hf hnegative
      hT hM hN hR hphase hx hz
    change |h y z-h y x| ≤ 7*U/(2*R^2)
    rw [hxa,hzb,abs_of_pos (sub_pos.mpr hab)]
    simpa only [hgapUpper] using hupp



                                                                       
                                                                     
                                                                         
theorem bounded_denominator_adjacent_unimodular
    (S : Finset ℝ) {H a b c d : ℤ} {L U : ℝ}
    (hseed : ∀ q : ℚ, (q.den:ℤ) ≤ H → (q:ℝ) ∈ Icc L U → (q:ℝ) ∈ S)
    (hb : 0 < b) (hbH : b ≤ H) (hd : 0 < d) (hdH : d ≤ H)
    (hcopb : IsCoprime a b) (hcopd : IsCoprime c d)
    (haI : (a:ℝ)/b ∈ Icc L U) (hcI : (c:ℝ)/d ∈ Icc L U)
    (hac : (a:ℝ)/b < (c:ℝ)/d)
    (hadj : ∀ z ∈ S, ¬ ((a:ℝ)/b < z ∧ z < (c:ℝ)/d)) :
    c*b-a*d=1 := by
  obtain ⟨e,r,hr,hrH,_hsum,hcopr,hdet,hnext⟩ :=
    exists_right_neighbor_at_order hb hbH hcopb
  have hrpos : 0 < r := by omega
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hrR : (0:ℝ) < r := by exact_mod_cast hrpos
  have hcross : a*d < b*c := by
    have hh := (div_lt_div_iff₀ hbR hdR).mp hac
    exact_mod_cast (show (a:ℝ)*d < (b:ℝ)*c by nlinarith only [hh])
  have hright : (e:ℝ)/r ≤ (c:ℝ)/d := by
    apply (div_le_div_iff₀ hrR hdR).mpr
    exact_mod_cast hnext c d (by omega) hdH hcross
  have hleft : (a:ℝ)/b < (e:ℝ)/r := by
    apply (div_lt_div_iff₀ hbR hrR).mpr
    have hh : (e:ℝ)*b-a*r=1 := by exact_mod_cast hdet
    nlinarith only [hh]
  have hqI : ((Rat.divInt e r):ℝ) ∈ Icc L U := by
    rw [Rat.cast_divInt]
    exact ⟨haI.1.trans hleft.le,hright.trans hcI.2⟩
  have hqS : (e:ℝ)/r ∈ S := by
    have hh := hseed (Rat.divInt e r)
      ((Int.le_of_dvd hrpos (Rat.den_dvd e r)).trans hrH) hqI
    simpa only [Rat.cast_divInt] using hh
  have heq : (e:ℝ)/r=(c:ℝ)/d := by
    apply le_antisymm hright
    exact le_of_not_gt (fun hh => hadj _ hqS ⟨hleft,hh⟩)
  have heqQ : (e:ℚ)/r=(c:ℚ)/d := by exact_mod_cast heq
  obtain ⟨he,hrd⟩ := Rat.div_int_inj hrpos hd
    (Int.isCoprime_iff_nat_coprime.mp hcopr)
    (Int.isCoprime_iff_nat_coprime.mp hcopd) heqQ
  simpa only [he,hrd] using hdet


                                                                 
                                                                       
                                                                          
theorem reference_max_denominator_neighbor
    (S : Finset ℝ) {H a b c d : ℤ} {L U : ℝ}
    (hseed : ∀ q : ℚ, (q.den:ℤ) ≤ H → (q:ℝ) ∈ Icc L U → (q:ℝ) ∈ S)
    (hlabels : ∀ z ∈ S,
      (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ H) ∨
      (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
        0 < v ∧ v ≤ H ∧ (u:ℝ)/v ∈ S ∧ |m*v-u*n|=1))
    (hb : 0 < b) (hd : 0 < d)
    (hcopb : IsCoprime a b) (hcopd : IsCoprime c d)
    (haS : (a:ℝ)/b ∈ S) (hcS : (c:ℝ)/d ∈ S)
    (haI : (a:ℝ)/b ∈ Icc L U) (hcI : (c:ℝ)/d ∈ Icc L U)
    (hac : (a:ℝ)/b < (c:ℝ)/d)
    (hadj : ∀ z ∈ S, ¬ ((a:ℝ)/b < z ∧ z < (c:ℝ)/d)) :
    ∃ e r f s : ℤ, ((e=a ∧ r=b) ∨ (e=c ∧ r=d)) ∧
      r=max b d ∧ IsCoprime e r ∧ 0 < r ∧ 0 < s ∧ s ≤ r ∧ s ≤ H ∧
      (f:ℝ)/s ∈ S ∧ |e*s-f*r|=1 := by
  have hlarge (m n : ℤ) (hn : 0 < n) (hcop : IsCoprime m n)
      (hmS : (m:ℝ)/n ∈ S) (hbig : H < n) :
      ∃ u v : ℤ, 0 < v ∧ v ≤ H ∧ (u:ℝ)/v ∈ S ∧ |m*v-u*n|=1 := by
    rcases hlabels _ hmS with ⟨q,hq,hqH⟩ | ⟨m',n',u,v,he,hcop',hn',hv,hvH,huS,hdet⟩
    · have heq : (m:ℚ)/n=q := by
        apply Rat.cast_injective (α:=ℝ)
        simpa only [Rat.cast_div,Rat.cast_intCast] using hq
      have hden := Rat.den_div_eq_of_coprime hn (Int.isCoprime_iff_nat_coprime.mp hcop)
      rw [heq] at hden
      omega
    · have heq : (m:ℚ)/n=(m':ℚ)/n' := by exact_mod_cast he
      obtain ⟨hem,hen⟩ := Rat.div_int_inj hn hn'
        (Int.isCoprime_iff_nat_coprime.mp hcop)
        (Int.isCoprime_iff_nat_coprime.mp hcop') heq
      refine ⟨u,v,hv,hvH,huS,?_⟩
      simpa only [hem,hen] using hdet
  by_cases hdb : d ≤ b
  · by_cases hbH : b ≤ H
    · have hdH : d ≤ H := hdb.trans hbH
      have hdet := bounded_denominator_adjacent_unimodular S hseed
        hb hbH hd hdH hcopb hcopd haI hcI hac hadj
      refine ⟨a,b,c,d,Or.inl ⟨rfl,rfl⟩,(max_eq_left hdb).symm,hcopb,hb,hd,hdb,hdH,hcS,?_⟩
      have he : a*d-c*b= -(c*b-a*d) := by ring
      rw [he,abs_neg,hdet]
      norm_num
    · obtain ⟨u,v,hv,hvH,huS,hdet⟩ := hlarge a b hb hcopb haS (lt_of_not_ge hbH)
      exact ⟨a,b,u,v,Or.inl ⟨rfl,rfl⟩,(max_eq_left hdb).symm,hcopb,hb,
        hv,hvH.trans (lt_of_not_ge hbH).le,hvH,huS,hdet⟩
  · have hbd : b ≤ d := (lt_of_not_ge hdb).le
    by_cases hdH : d ≤ H
    · have hbH : b ≤ H := hbd.trans hdH
      have hdet := bounded_denominator_adjacent_unimodular S hseed
        hb hbH hd hdH hcopb hcopd haI hcI hac hadj
      refine ⟨c,d,a,b,Or.inr ⟨rfl,rfl⟩,(max_eq_right hbd).symm,hcopd,hd,hb,hbd,hbH,haS,?_⟩
      rw [hdet]
      norm_num
    · obtain ⟨u,v,hv,hvH,huS,hdet⟩ := hlarge c d hd hcopd hcS (lt_of_not_ge hdH)
      exact ⟨c,d,u,v,Or.inr ⟨rfl,rfl⟩,(max_eq_right hbd).symm,hcopd,hd,
        hv,hvH.trans (lt_of_not_ge hdH).le,hvH,huS,hdet⟩


                                                               
                                                                      
                                                               
theorem finite_reference_bracket (S : Finset ℝ) {l u x : ℝ}
    (hl : l ∈ S) (hu : u ∈ S) (hlx : l ≤ x) (hxu : x ≤ u) (hx : x ∉ S) :
    ∃ a ∈ S, ∃ b ∈ S, a < x ∧ x < b ∧
      ∀ z ∈ S, ¬ (a < z ∧ z < b) := by
  classical
  let A := S.filter (fun z => z < x)
  let B := S.filter (fun z => x < z)
  have hlstrict : l < x := lt_of_le_of_ne hlx (fun he => hx (he ▸ hl))
  have hustrict : x < u := lt_of_le_of_ne hxu (fun he => hx (he.symm ▸ hu))
  have hA : A.Nonempty := ⟨l,Finset.mem_filter.mpr ⟨hl,hlstrict⟩⟩
  have hB : B.Nonempty := ⟨u,Finset.mem_filter.mpr ⟨hu,hustrict⟩⟩
  let a := A.max' hA
  let b := B.min' hB
  have ha := Finset.mem_filter.mp (Finset.max'_mem A hA)
  have hb := Finset.mem_filter.mp (Finset.min'_mem B hB)
  refine ⟨a,ha.1,b,hb.1,ha.2,hb.2,?_⟩
  intro z hz hinside
  rcases lt_trichotomy z x with hzx | rfl | hxz
  · have hzA : z ∈ A := Finset.mem_filter.mpr ⟨hz,hzx⟩
    have hh : z ≤ a := Finset.le_max' A z hzA
    exact (not_lt_of_ge hh) hinside.1
  · exact hx hz
  · have hzB : z ∈ B := Finset.mem_filter.mpr ⟨hz,hxz⟩
    have hh : b ≤ z := Finset.min'_le B z hzB
    exact (not_lt_of_ge hh) hinside.2


                                                                  
                                                   
theorem physical_block_count_of_pairwise_width
    (S : Finset ℤ) (x : ℤ → ℝ) {N Z C : ℝ} (hN : 0 < N) (hC : 0 ≤ C)
    (hwindow : ∀ k ∈ S, Z+(k:ℝ)*N ≤ x k ∧ x k ≤ Z+((k:ℝ)+1)*N)
    (hwidth : ∀ i ∈ S, ∀ j ∈ S, |x j-x i| ≤ C*N) :
    (S.card:ℝ) ≤ 2+C := by
  classical
  by_cases hS : S.Nonempty
  · let a := S.min' hS
    let b := S.max' hS
    have ha : a ∈ S := Finset.min'_mem S hS
    have hb : b ∈ S := Finset.max'_mem S hS
    have hab : a ≤ b := Finset.min'_le S b hb
    have hspan : (b:ℝ)-(a:ℝ) ≤ C+1 := by
      have hw := (abs_le.mp (hwidth a ha b hb)).2
      have hh : ((b:ℝ)-(a:ℝ))*N ≤ (C+1)*N := by
        nlinarith only [hw,(hwindow a ha).2,(hwindow b hb).1]
      exact (mul_le_mul_iff_left₀ hN).mp hh
    have hcount := TaoTrudgianYang2025.integer_card_le_interval_length_add_one S
      (show (a:ℝ) ≤ b by exact_mod_cast hab) (by
        intro k hk
        exact ⟨by exact_mod_cast Finset.min'_le S k hk,
          by exact_mod_cast Finset.le_max' S k hk⟩)
    linarith only [hcount,hspan]
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [he]
    simp only [Finset.card_empty,Nat.cast_zero]
    linarith only [hC]

                                                                    
                                                         
theorem positive_difference_reference_preimage_width_lower
    (F : ℝ → ℝ) {σ J η y T M N R U x z : ℝ}
    (hσ : 0 < σ) (hJ : 0 < J) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hy : y ∈ Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hphase : T*N*R^2=M^3)
    (hx : x ∈ Icc (3*M/4) (9*M/4)) (hz : z ∈ Icc (3*M/4) (9*M/4)) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    U/(4*R^2) ≤ |iteratedDeriv 2 f z/2-iteratedDeriv 2 f x/2| →
    (σ/(6*J))*U*N ≤ |z-x| := by
  intro f hgap
  let L := 3*J*T/(2*σ*M^3)
  have hL : 0 < L := by dsimp only [L]; positivity
  have hnorm w (hw : w ∈ Icc (3*M/4) (9*M/4)) :
      w/M ∈ Icc (3/4:ℝ) (9/4) := by
    constructor
    · apply (le_div_iff₀ hM).mpr
      linarith only [hw.1]
    · apply (div_le_iff₀ hM).mpr
      linarith only [hw.2]
  have hcf w (hw : w ∈ Icc (3*M/4) (9*M/4)) : ContDiffAt ℝ 3 f w := by
    have hw0 : 0 < w/M := by
      have hh := (hnorm w hw).1
      linarith only [hh]
    have hs0 : 0 < w/M+η*y := add_pos hw0 (mul_pos hη (by linarith only [hy.1]))
    exact (contDiffAt_const.mul (((hf _ hw0).comp w (contDiffAt_id.div_const M)).sub
      ((hf _ hs0).comp w ((contDiffAt_id.div_const M).add contDiffAt_const)))).div_const
      (σ*η) |>.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hd w (hw : w ∈ Icc (3*M/4) (9*M/4)) :
      HasDerivAt (fun u => iteratedDeriv 2 f u/2) (iteratedDeriv 3 f w/2) w :=
    (hasDerivAt_iteratedDeriv_finite (by norm_num : 2 < 3) (hcf w hw)).div_const 2
  have hupper w (hw : w ∈ Icc (3*M/4) (9*M/4)) :
      |iteratedDeriv 3 f w/2| ≤ L := by
    have hn := hnorm w hw
    have hy' : y ∈ Icc (1/2:ℝ) 3 :=
      ⟨by linarith only [hy.1],by linarith only [hy.2]⟩
    have hu := positive_jets_difference_mixed_upper F hσ hJ hη hηmax hn hy' hf hbound
      3 0 (by norm_num) (by norm_num)
    simp only [iteratedDeriv_zero] at hu
    have hw0 : 0 < w/M := by linarith only [hn.1]
    have hs0 : 0 < w/M+η*y := add_pos hw0 (mul_pos hη (by linarith only [hy.1]))
    have hFx : ContDiffAt ℝ 3 F (w/M) :=
      (hf _ hw0).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
    have hFz : ContDiffAt ℝ 3 (fun u => F (u+η*y)) (w/M) :=
      ((hf _ hs0).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)).comp
        (w/M) (contDiffAt_id.add contDiffAt_const)
    rw [iteratedDeriv_div_const,iteratedDeriv_fun_sub hFx hFz,iteratedDeriv_comp_add_const] at hu
    have hid := positive_difference_physical_iteratedDeriv F (T:=T) (σ:=σ) hM
      (show 0 < w by linarith only [hw.1,hM])
      (mul_nonneg hη.le (by linarith only [hy.1])) hf 3
    dsimp only [f]
    rw [hid,abs_div,abs_mul,abs_of_pos (show 0 < T/M^3 by positivity)]
    rw [abs_of_pos (by norm_num : (0:ℝ) < 2)]
    calc
      _ ≤ (T/M^3)*(3*J/σ)/2 := by gcongr
      _ = L := by dsimp only [L]; ring
  have hcomp : |iteratedDeriv 2 f z/2-iteratedDeriv 2 f x/2| ≤ L*|z-x| := by
    apply (convex_Icc (3*M/4) (9*M/4)).norm_image_sub_le_of_norm_deriv_le
      (fun w hw => (hd w hw).differentiableAt) (fun w hw => ?_) hx hz
    rw [(hd w hw).deriv]
    exact hupper w hw
  have hbound' := hgap.trans hcomp
  have hh : (U/(4*R^2))/L ≤ |z-x| :=
    (div_le_iff₀ hL).mpr (by simpa only [mul_comm] using hbound')
  have he : (U/(4*R^2))/L=(σ/(6*J))*U*N := by
    dsimp only [L]
    rw [←hphase]
    field_simp
    ring
  simpa only [he] using hh

                                                                  
                                                                     
theorem physical_grid_interval_card {N Z x z : ℝ} (hN : 0 < N) (hxz : x ≤ z) :
    ∃ A : Finset ℤ,
      (∀ k : ℤ, k ∈ A ↔ x ≤ Z+(k:ℝ)*N ∧ Z+(k:ℝ)*N ≤ z) ∧
      (z-x)/N-1 ≤ (A.card:ℝ) ∧ (A.card:ℝ) ≤ (z-x)/N+1 := by
  let a := (x-Z)/N
  let b := (z-Z)/N
  let A := Finset.Icc (Int.ceil a) (Int.floor b)
  have hab : a ≤ b := div_le_div_of_nonneg_right (sub_le_sub_right hxz Z) hN.le
  have hleft := Int.ceil_lt_add_one a
  have hright := Int.lt_floor_add_one b
  have hround : Int.ceil a ≤ Int.floor b+1 := by
    have hh : (Int.ceil a:ℝ) < (Int.floor b:ℝ)+2 := by
      linarith only [hleft,hright,hab]
    have hh' : Int.ceil a < Int.floor b+2 := by exact_mod_cast hh
    omega
  have hcard : (A.card:ℝ)=(Int.floor b:ℝ)+1-(Int.ceil a:ℝ) := by
    exact_mod_cast Int.card_Icc_of_le (Int.ceil a) (Int.floor b) hround
  have hmem k : k ∈ A ↔ x ≤ Z+(k:ℝ)*N ∧ Z+(k:ℝ)*N ≤ z := by
    change (k ∈ Finset.Icc (Int.ceil a) (Int.floor b)) ↔ _
    rw [Finset.mem_Icc,Int.ceil_le,Int.le_floor]
    constructor
    · intro hk
      have hl := (div_le_iff₀ hN).mp hk.1
      have hu := (le_div_iff₀ hN).mp hk.2
      constructor <;> linarith only [hl,hu]
    · intro hk
      constructor
      · apply (div_le_iff₀ hN).mpr
        linarith only [hk.1]
      · apply (le_div_iff₀ hN).mpr
        linarith only [hk.2]
  refine ⟨A,hmem,?_,?_⟩
  · rw [hcard]
    have he : (z-x)/N=b-a := by dsimp only [a,b]; ring
    rw [he]
    linarith only [hleft,hright]
  · have hh := TaoTrudgianYang2025.integer_card_le_interval_length_add_one A hab (by
      intro k hk
      have hm := Finset.mem_Icc.mp hk
      exact ⟨Int.ceil_le.mp hm.1,Int.le_floor.mp hm.2⟩)
    convert hh using 1
    dsimp only [a,b]
    ring

                                                               
                                                             
theorem positive_difference_physical_curvature_strictMono
    (F : ℝ → ℝ) {σ c η y T M : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hy : y ∈ Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    StrictMonoOn (fun w => iteratedDeriv 2 f w/2) (Icc (3*M/4) (9*M/4)) := by
  intro f
  have hnorm w (hw : w ∈ Icc (3*M/4) (9*M/4)) :
      w/M ∈ Icc (3/4:ℝ) (9/4) := by
    constructor
    · apply (le_div_iff₀ hM).mpr
      linarith only [hw.1]
    · apply (div_le_iff₀ hM).mpr
      linarith only [hw.2]
  have hd w (hw : w ∈ Icc (3*M/4) (9*M/4)) :
      HasDerivAt (fun u => iteratedDeriv 2 f u/2) (iteratedDeriv 3 f w/2) w := by
    have hw0 : 0 < w/M := by
      have hh := (hnorm w hw).1
      linarith only [hh]
    have hs0 : 0 < w/M+η*y := add_pos hw0 (mul_pos hη (by linarith only [hy.1]))
    have hcf : ContDiffAt ℝ 3 f w :=
      (contDiffAt_const.mul (((hf _ hw0).comp w (contDiffAt_id.div_const M)).sub
        ((hf _ hs0).comp w ((contDiffAt_id.div_const M).add contDiffAt_const)))).div_const
        (σ*η) |>.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
    exact (hasDerivAt_iteratedDeriv_finite (by norm_num : 2 < 3) hcf).div_const 2
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (fun w hw => (hd w hw).continuousAt.continuousWithinAt)
  intro w hw
  have hw' := interior_subset hw
  rw [(hd w hw').deriv]
  have hl := positive_difference_third_signed_lower F (y:=y) hσ hη hηmax hc (hnorm w hw')
    ⟨by linarith only [hy.1],by linarith only [hy.2]⟩ hf hnegative
  have hp : 0 < (iteratedDeriv 3 F (w/M)-iteratedDeriv 3 F (w/M+η*y))/(σ*η) :=
    (show 0 < c/(2*σ) by positivity).trans_le hl
  have hid := positive_difference_physical_iteratedDeriv F (T:=T) (σ:=σ) hM
    (show 0 < w by linarith only [hw'.1,hM])
    (mul_nonneg hη.le (by linarith only [hy.1])) hf 3
  dsimp only [f]
  rw [hid]
  positivity

                                                                    
                                                                      
                                                                   
                                                                 
open scoped FourierTransform BigOperators

end TaoTrudgianYang2025.HuxleyRationalPhase

-- Generated closures: source context is replayed in the next part.
end
end
