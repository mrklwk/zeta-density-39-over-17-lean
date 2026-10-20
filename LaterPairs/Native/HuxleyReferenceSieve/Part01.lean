module
public import LaterPairs.Native.HuxleyProfileGeometry
public import GuthMaynard.AffineSource.Foundation
public import LaterPairs.Native.DoubledBlockPrefixes
public import LaterPairs.Native.ExponentPairDifferencingBound
public import LaterPairs.Native.ExponentPairShiftJets
public import LaterPairs.Native.ExponentPairShiftUniformity
public import LaterPairs.Native.ExponentPairSourceCorrelation
public import LaterPairs.Native.ExponentPairSourceWeyl
public import LaterPairs.Native.FiniteSmoothTaylor
public import LaterPairs.Native.FiniteSmoothThirdDerivative
public import LaterPairs.Native.HuxleyModelNondegeneracy
public import LaterPairs.Native.IntegerIntervalCount
public import LaterPairs.Native.ParabolaBilinearLocalization
public import LaterPairs.Native.ReciprocalSecondDerivativeBounds
public import LaterPairs.Native.RobertSargosInitialDyadicLog
public import LaterPairs.Native.SargosLocalAffineJets
public import LaterPairs.Native.SecondDerivativeComposition
public import LaterPairs.Native.SquareProductCount
public import LaterPairs.Native.ZetaSourceLogScales
public import MathCollab.Density.Stronger.PointMean.HorizontalEdges
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaAmplitudeMonotonicity
public import TaoTrudgianYang2025.BetaExpandedModelJets
public import TaoTrudgianYang2025.BetaInverseJets
public import TaoTrudgianYang2025.BetaLegendreAllOrders
public import TaoTrudgianYang2025.BetaModelJetEstimatesFull
public import TaoTrudgianYang2025.BetaStationaryMain
public import TaoTrudgianYang2025.BetaTaylorPolynomialRemainder
public import TaoTrudgianYang2025.BetaUniformity
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import TaoTrudgianYang2025.HeathBrownModelJetCore
public import TaoTrudgianYang2025.HeathBrownPhysicalPhase
public import TaoTrudgianYang2025.ModelEndpointEntry

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
noncomputable section
namespace TaoTrudgianYang2025.HuxleyRationalPhase
theorem positive_difference_minimal_curvature_arc_count
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (F : ℝ → ℝ)
    (k : ι → ℤ) (N Bmul : ℕ) (s : ℝ) {σ c J η y T M R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y ∈ Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hNM : (N:ℝ) ≤ M) (hphase : T*(N:ℝ)*R^2=M^3)
    (hmul : ∀ n : ℤ, (S.filter (fun i => k i=n)).card ≤ Bmul)
    (hpoints : ∀ i∈S, s+(N:ℝ)*(k i:ℝ) ∈ Icc M (2*M)) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let t := fun i => s+(N:ℝ)*(k i:ℝ)
    let v := fun i => iteratedDeriv 2 f (t i)/2
    let delta := c/(16*σ*R^2)
    let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
    ∃ (r : ι → ℚ) (z : ι → ℝ),
      (∀ i∈S, z i∈Ioo (t i-(N:ℝ)/4) (t i+(N:ℝ)/4) ∧
        iteratedDeriv 2 f (z i)/2=(r i:ℝ) ∧
        (r i:ℝ)∈Ioo (v i-delta) (v i+delta) ∧
        ∀ a : ℚ, (a:ℝ)∈Ioo (v i-delta) (v i+delta) → (r i).den ≤ a.den) ∧
      (∀ i∈S, ∀ a∈Icc M (2*M), ∀ b∈Icc M (2*M),
        a+(N:ℝ)/4 ≤ t i → t i ≤ b-(N:ℝ)/4 →
        (r i:ℝ)∈Ioo (iteratedDeriv 2 f a/2) (iteratedDeriv 2 f b/2)) ∧
      ∀ Q : ℕ, 2 ≤ Q →
        let G := S.filter (fun i => Q ≤ (r i).den)
        let D := 16*σ*R^2/(c*(Q:ℝ))
        (G.card:ℝ) ≤ Bmul*(4*(Vbound+1)*D^2+D*(2+Real.log (D+1))) := by
  intro f t v delta Vbound
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  let L := c/(2*σ*(N:ℝ)*R^2)
  have hL : 0 < L := by dsimp only [L]; positivity
  have hX : 0 ≤ Vbound := by dsimp only [Vbound]; positivity
  have hnorm w (hw : w∈Icc (3*M/4) (9*M/4)) :
      w/M∈Icc (3/4:ℝ) (9/4) := by
    constructor
    · apply (le_div_iff₀ hM).mpr
      linarith only [hw.1]
    · apply (div_le_iff₀ hM).mpr
      linarith only [hw.2]
  have hcf w (hw : w∈Icc (3*M/4) (9*M/4)) : ContDiffAt ℝ 3 f w := by
    have hn := hnorm w hw
    have hw0 : 0 < w/M := by linarith only [hn.1]
    have hs0 : 0 < w/M+η*y := add_pos hw0 (mul_pos hη (by linarith only [hy.1]))
    exact (contDiffAt_const.mul (((hf _ hw0).comp w (contDiffAt_id.div_const M)).sub
      ((hf _ hs0).comp w ((contDiffAt_id.div_const M).add contDiffAt_const)))).div_const (σ*η)
      |>.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hscale3 : T/M^3=1/((N:ℝ)*R^2) := by
    apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    nlinarith only [hphase]
  have hthree w (hw : w∈Icc (3*M/4) (9*M/4)) : L ≤ iteratedDeriv 3 f w := by
    have hl := positive_difference_third_signed_lower F (y:=y) hσ hη hηmax hc (hnorm w hw)
      ⟨by linarith only [hy.1],by linarith only [hy.2]⟩ hf hnegative
    have hid := positive_difference_physical_iteratedDeriv F (T:=T) (σ:=σ) hM
      (show 0 < w by linarith only [hw.1,hM])
      (mul_nonneg hη.le (by linarith only [hy.1])) hf 3
    dsimp only [f]
    rw [hid,hscale3]
    convert mul_le_mul_of_nonneg_left hl
      (show 0 ≤ 1/((N:ℝ)*R^2) by positivity) using 1
    dsimp only [L]
    ring
  have hbuffer i (hi : i∈S) :
      Icc (t i-(N:ℝ)/4) (t i+(N:ℝ)/4) ⊆ Icc (3*M/4) (9*M/4) := by
    intro w hw
    have ht := hpoints i hi
    change M ≤ t i ∧ t i ≤ 2*M at ht
    constructor <;> linarith only [ht.1,ht.2,hw.1,hw.2,hNM]
  have hv i (hi : i∈S) : |v i| ≤ Vbound := by
    have htI : t i∈Icc (3*M/4) (9*M/4) :=
      hbuffer i hi ⟨by linarith only [hNp],by linarith only [hNp]⟩
    have hn := hnorm (t i) htI
    have hu := positive_jets_difference_mixed_upper F hσ hJ hη hηmax hn
      (show y∈Icc (1/2:ℝ) 3 from ⟨by linarith only [hy.1],by linarith only [hy.2]⟩)
      hf hbound 2 0 (by norm_num) (by norm_num)
    simp only [iteratedDeriv_zero] at hu
    have ht0 : 0 < t i/M := by linarith only [hn.1]
    have hs0 : 0 < t i/M+η*y := add_pos ht0 (mul_pos hη (by linarith only [hy.1]))
    have hFx : ContDiffAt ℝ 2 F (t i/M) :=
      (hf _ ht0).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have hFz : ContDiffAt ℝ 2 (fun u => F (u+η*y)) (t i/M) :=
      ((hf _ hs0).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp
        (t i/M) (contDiffAt_id.add contDiffAt_const)
    rw [iteratedDeriv_div_const,iteratedDeriv_fun_sub hFx hFz,iteratedDeriv_comp_add_const] at hu
    have hid := positive_difference_physical_iteratedDeriv F (T:=T) (σ:=σ) hM
      (show 0 < t i by linarith only [htI.1,hM])
      (mul_nonneg hη.le (by linarith only [hy.1])) hf 2
    dsimp only [v,f]
    rw [hid,abs_div,abs_mul,abs_of_pos (show 0 < T/M^2 by positivity)]
    rw [abs_of_pos (by norm_num : (0:ℝ) < 2)]
    calc
      _ ≤ (T/M^2)*(3*J/σ)/2 := by gcongr
      _ = Vbound := by
        have he : T/M^2=M/((N:ℝ)*R^2) := by
          apply (div_eq_div_iff (by positivity) (by positivity)).mpr
          nlinarith only [hphase]
        rw [he]
        dsimp only [Vbound]
        ring
  obtain ⟨r,z,hdata,hcount⟩ :=
    TaoTrudgianYang2025.exists_bourgain_C3_minimal_curvature_arc_count S f k N Bmul s
      hN hL hX hcf hthree hmul hbuffer hv
  have hdelta : L*(N:ℝ)/8=delta := by dsimp only [L,delta]; field_simp; norm_num
  refine ⟨r,z,?_,?_,?_⟩
  · simpa only [hdelta] using hdata
  · intro i hi a ha b hb hat htb
    have hz := (hdata i hi).1
    have hza : a < z i := by linarith only [hz.1,hat]
    have hzb : z i < b := by linarith only [hz.2,htb]
    have hwide w (hw : w∈Icc M (2*M)) : w∈Icc (3*M/4) (9*M/4) := by
      constructor <;> linarith only [hw.1,hw.2,hM]
    have hzwide : z i∈Icc (3*M/4) (9*M/4) :=
      ⟨(hwide a ha).1.trans hza.le,hzb.le.trans (hwide b hb).2⟩
    have hmono := positive_difference_physical_curvature_strictMono F hσ hc hη hηmax hy
      hf hnegative hT hM
    change StrictMonoOn (fun w => iteratedDeriv 2 f w/2) (Icc (3*M/4) (9*M/4)) at hmono
    rw [←(hdata i hi).2.1]
    exact ⟨hmono (hwide a ha) hzwide hza,hmono hzwide (hwide b hb) hzb⟩
  · intro Q hQ G D
    have hQp : (0:ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
    have hD : 8/(L*(N:ℝ)*(Q:ℝ))=D := by dsimp only [L,D]; field_simp; norm_num
    have hh := hcount Q hQ
    dsimp only at hh
    rw [hD] at hh
    exact hh

                                                              
                                                                      
                                                                      
                                                                   
theorem positive_difference_reference_gap_minimal_arcs
    (F : ℝ → ℝ) (N : ℕ) {σ c J η y T M R U x z s : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y ∈ Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hU : 0 < U)
    (hNM : (N:ℝ) ≤ M) (hUlarge : 3*J ≤ σ*U)
    (hphase : T*(N:ℝ)*R^2=M^3) (hx : x∈Icc M (2*M)) (hz : z∈Icc M (2*M)) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    let t := fun k : ℤ => s+(N:ℝ)*k
    let delta := c/(16*σ*R^2)
    let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
    U/(4*R^2) ≤ h z-h x → h z-h x ≤ 7*U/(2*R^2) →
    ∃ A : Finset ℤ, ∃ (r : ℤ → ℚ) (w : ℤ → ℝ),
      (∀ k : ℤ, k∈A ↔ x+(N:ℝ)/4 ≤ t k ∧ t k ≤ z-(N:ℝ)/4) ∧
      (∀ k∈A, w k∈Ioo x z ∧ h (w k)=(r k:ℝ) ∧
        (r k:ℝ)∈Ioo (h x) (h z) ∧
        (r k:ℝ)∈Ioo (h (t k)-delta) (h (t k)+delta) ∧
        ∀ a : ℚ, (a:ℝ)∈Ioo (h (t k)-delta) (h (t k)+delta) → (r k).den ≤ a.den) ∧
      (σ/(6*J))*U-3/2 ≤ (A.card:ℝ) ∧
      (A.card:ℝ) ≤ (14*σ/c)*U+1/2 ∧
      ∀ Q : ℕ, 2 ≤ Q →
        let G := A.filter (fun k => Q ≤ (r k).den)
        let D := 16*σ*R^2/(c*(Q:ℝ))
        (G.card:ℝ) ≤ 4*(Vbound+1)*D^2+D*(2+Real.log (D+1)) := by
  classical
  intro f h t delta Vbound hgaplow hgapup
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hwide a (ha : a∈Icc M (2*M)) : a∈Icc (3*M/4) (9*M/4) := by
    constructor <;> linarith only [ha.1,ha.2,hM]
  have hmono := positive_difference_physical_curvature_strictMono F hσ hc hη hηmax hy
    hf hnegative hT hM
  change StrictMonoOn h (Icc (3*M/4) (9*M/4)) at hmono
  have hgap : 0 < h z-h x := (show 0 < U/(4*R^2) by positivity).trans_le hgaplow
  have hxz : x < z := by
    by_contra hn
    have hh := hmono.monotoneOn (hwide z hz) (hwide x hx) (le_of_not_gt hn)
    linarith only [hh,hgap]
  have hlower := positive_difference_reference_preimage_width_lower F hσ hJ hη hηmax hy
    hf hbound hT hM hNp hR hphase (hwide x hx) (hwide z hz)
    (by change U/(4*R^2) ≤ |h z-h x|; rwa [abs_of_pos hgap])
  have hupper := positive_difference_reference_preimage_width F hσ hc hη hηmax hy
    hf hnegative hT hM hNp hR hphase hx hz
    (by change |h z-h x| ≤ 7*U/(2*R^2); rwa [abs_of_pos hgap])
  rw [abs_of_pos (sub_pos.mpr hxz)] at hlower hupper
  have hhalf : (1:ℝ)/2 ≤ (σ/(6*J))*U := by
    have hh : 3*J/(6*J) ≤ σ*U/(6*J) :=
      div_le_div_of_nonneg_right hUlarge (by positivity)
    have he : 3*J/(6*J)=(1:ℝ)/2 := by field_simp; norm_num
    rw [he] at hh
    convert hh using 1
    ring
  have hwidth : (N:ℝ)/2 ≤ z-x := by
    have hh := mul_le_mul_of_nonneg_right hhalf hNp.le
    linarith only [hh,hlower]
  have htrim : x+(N:ℝ)/4 ≤ z-(N:ℝ)/4 := by linarith only [hwidth]
  obtain ⟨A,hmem,hcardlow,hcardup⟩ := physical_grid_interval_card (Z:=s) hNp htrim
  have hmem' k : k∈A ↔ x+(N:ℝ)/4 ≤ t k ∧ t k ≤ z-(N:ℝ)/4 := by
    dsimp only [t]
    simpa only [mul_comm (N:ℝ) (k:ℝ)] using hmem k
  have hpoints k (hk : k∈A) : t k∈Icc M (2*M) := by
    have hh := (hmem' k).mp hk
    constructor <;> linarith only [hh.1,hh.2,hx.1,hz.2,hNp]
  have hmul n : (A.filter (fun k => id k=n)).card ≤ 1 := by
    have hsub : A.filter (fun k => id k=n) ⊆ {n} := by
      intro k hk
      exact Finset.mem_singleton.mpr (Finset.mem_filter.mp hk).2
    simpa using Finset.card_le_card hsub
  obtain ⟨r,w,hdata,hlocal,hcount⟩ :=
    positive_difference_minimal_curvature_arc_count A F id N 1 s hσ hc hJ hη hηmax hy
      hf hbound hnegative hT hM hN hR hNM hphase hmul hpoints
  refine ⟨A,r,w,hmem',?_,?_,?_,?_⟩
  · intro k hk
    have hkI := (hmem' k).mp hk
    have hd := hdata k hk
    have hloc := hlocal k hk x hx z hz hkI.1 hkI.2
    refine ⟨⟨?_,?_⟩,hd.2.1,hloc,hd.2.2.1,hd.2.2.2⟩
    · have hh := hd.1.1
      change t k-(N:ℝ)/4 < w k at hh
      linarith only [hh,hkI.1]
    · have hh := hd.1.2
      change w k < t k+(N:ℝ)/4 at hh
      linarith only [hh,hkI.2]
  · have hh : (σ/(6*J))*U ≤ (z-x)/(N:ℝ) := (le_div_iff₀ hNp).mpr hlower
    have he : ((z-(N:ℝ)/4)-(x+(N:ℝ)/4))/(N:ℝ)-1=(z-x)/(N:ℝ)-3/2 := by field_simp; ring
    rw [he] at hcardlow
    linarith only [hh,hcardlow]
  · have hh : (z-x)/(N:ℝ) ≤ (14*σ/c)*U := (div_le_iff₀ hNp).mpr hupper
    have he : ((z-(N:ℝ)/4)-(x+(N:ℝ)/4))/(N:ℝ)+1=(z-x)/(N:ℝ)+1/2 := by field_simp; ring
    rw [he] at hcardup
    linarith only [hh,hcardup]
  · intro Q hQ G D
    have hh := hcount Q hQ
    dsimp only at hh
    simpa only [Nat.cast_one,one_mul] using hh

                                                                   
                                                                
                                                                    
theorem positive_difference_chosen_arcs_band_fourier
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (S : Finset ι) (F : ℝ → ℝ)
      (y : ι → ℝ) (L : ι → ℤ) (H : ι → ℕ) (r : ι → ℚ) (z : ι → ℝ)
      (N : ℕ) (η T M R : ℝ),
      1 ≤ N → (∀ i∈S, H i ≤ N) →
      0 < η → η ≤ 1/8 → 0 < T → 0 < M → 0 < R →
      (∀ i∈S, y i∈Icc (1:ℝ) 2) →
      (∀ i∈S, (L i:ℝ)-2*(N:ℝ)∈Icc M (2*M)) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 →
      7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      let f := fun i w => T*(F (w/M)-F (w/M+η*y i))/(σ*η)
      (∀ i∈S, z i∈Ioo ((L i:ℝ)-2*(N:ℝ)-(N:ℝ)/4)
        ((L i:ℝ)-2*(N:ℝ)+(N:ℝ)/4) ∧
        iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ)) →
      let m := fun i => round (z i)
      let A := fun i => (L i-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i) (m i)/6
      let ℓ := fun i => deriv (f i) (m i)
      let lambda := c/(12*σ*(N:ℝ)*R^2)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      let G := S.filter (fun i => q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)
      (∀ i∈S, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i) ∧
      ∀ Q₀ : ℕ, (∀ i∈G, q i ≤ Q₀) →
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q₀:ℝ)*(N:ℝ)^2 ≤ K₀ →
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
  intro ι S F y L H r z N η T M R hN hH hη hηmax hT hM hR hy hbase hf hbound hnegative
    hphase hbuffer hfourBudget hquadBudget f hroots m A q μ ℓ lambda U₃ G
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlambda : 0 < lambda := by dsimp only [lambda]; positivity
  have hU₃ : 0 < U₃ := by dsimp only [U₃]; positivity
  let beta := 3*J/(σ*M*(N:ℝ)*R^2)
  have hbeta : 0 ≤ beta := by dsimp only [beta]; positivity
  have hnorm w (hw : w∈Icc (3*M/4) (9*M/4)) :
      w/M∈Icc (3/4:ℝ) (9/4) := by
    constructor
    · apply (le_div_iff₀ hM).mpr
      linarith only [hw.1]
    · apply (div_le_iff₀ hM).mpr
      linarith only [hw.2]
  have hcf i (hi : i∈S) w (hw : w∈Icc (3*M/4) (9*M/4)) :
      ContDiffAt ℝ ∞ (f i) w := by
    have hn := hnorm w hw
    have hw0 : 0 < w/M := by linarith only [hn.1]
    have hs0 : 0 < w/M+η*y i := add_pos hw0 (mul_pos hη (by linarith only [(hy i hi).1]))
    exact (contDiffAt_const.mul (((hf _ hw0).comp w (contDiffAt_id.div_const M)).sub
      ((hf _ hs0).comp w ((contDiffAt_id.div_const M).add contDiffAt_const)))).div_const (σ*η)
  have hupper i (hi : i∈S) w (hw : w∈Icc (3*M/4) (9*M/4)) n (hn : n ≤ 4) :
      |iteratedDeriv n (f i) w| ≤ (T/M^n)*(3*J/σ) := by
    have hw' := hnorm w hw
    have hy' : y i∈Icc (1/2:ℝ) 3 :=
      ⟨by linarith only [(hy i hi).1],by linarith only [(hy i hi).2]⟩
    have hu := positive_jets_difference_mixed_upper F hσ hJ hη hηmax hw' hy' hf hbound
      n 0 (by norm_num) (by omega)
    simp only [iteratedDeriv_zero] at hu
    have hw0 : 0 < w/M := by linarith only [hw'.1]
    have hs0 : 0 < w/M+η*y i := add_pos hw0 (mul_pos hη (by linarith only [(hy i hi).1]))
    have hFx : ContDiffAt ℝ n F (w/M) :=
      (hf _ hw0).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
    have hFz : ContDiffAt ℝ n (fun u => F (u+η*y i)) (w/M) :=
      ((hf _ hs0).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).comp
        (w/M) (contDiffAt_id.add contDiffAt_const)
    rw [iteratedDeriv_div_const,iteratedDeriv_fun_sub hFx hFz,iteratedDeriv_comp_add_const] at hu
    have hid := positive_difference_physical_iteratedDeriv F (T:=T) (σ:=σ) hM
      (show 0 < w by linarith only [hw.1,hM])
      (mul_nonneg hη.le (by linarith only [(hy i hi).1])) hf n
    dsimp only [f]
    rw [hid,abs_mul,abs_of_pos (show 0 < T/M^n by positivity)]
    exact mul_le_mul_of_nonneg_left hu (by positivity)
  have hscale3 : T/M^3=1/((N:ℝ)*R^2) := by
    apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    nlinarith only [hphase]
  have hscale4 : T/M^4=1/(M*(N:ℝ)*R^2) := by
    apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    calc
      T*(M*(N:ℝ)*R^2)=M*(T*(N:ℝ)*R^2) := by ring
      _ = M*M^3 := by rw [hphase]
      _ = 1*M^4 := by ring
  have hthree i (hi : i∈S) w (hw : w∈Icc (3*M/4) (9*M/4)) :
      6*lambda ≤ iteratedDeriv 3 (f i) w ∧ iteratedDeriv 3 (f i) w ≤ 6*U₃ := by
    have hl := positive_difference_third_signed_lower F (y:=y i) hσ hη hηmax hc (hnorm w hw)
      ⟨by linarith only [(hy i hi).1],by linarith only [(hy i hi).2]⟩ hf hnegative
    have hid := positive_difference_physical_iteratedDeriv F (T:=T) (σ:=σ) hM
      (show 0 < w by linarith only [hw.1,hM])
      (mul_nonneg hη.le (by linarith only [(hy i hi).1])) hf 3
    have hu := (le_abs_self (iteratedDeriv 3 (f i) w)).trans (hupper i hi w hw 3 (by norm_num))
    rw [hscale3] at hu
    constructor
    · dsimp only [f]
      rw [hid,hscale3]
      convert mul_le_mul_of_nonneg_left hl
        (show 0 ≤ 1/((N:ℝ)*R^2) by positivity) using 1
      dsimp only [lambda]
      ring
    · convert hu using 1
      dsimp only [U₃]
      ring
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
  refine ⟨(fun i hi => ⟨(hgeo i hi).2.1,hA i hi⟩),?_⟩
  intro Q₀ hQ₀ K₀ inst hK₀
  have hKG i (hi : i∈G) : 7*(μ i*(q i:ℝ)*(A i:ℝ)^2) ≤ K₀ := by
    have hiS := hGS hi
    have hAr : (A i:ℝ) ≤ 3*(N:ℝ) := by exact_mod_cast (hA i hiS).2.1
    have hqr : (q i:ℝ) ≤ Q₀ := by exact_mod_cast hQ₀ i hi
    calc
      _ ≤ 7*(U₃*(Q₀:ℝ)*(3*(N:ℝ))^2) := by gcongr; exact (hmu i hiS).2.2
      _ = 63*U₃*(Q₀:ℝ)*(N:ℝ)^2 := by ring
      _ ≤ _ := hK₀
  obtain ⟨v,hv,hfourier⟩ := hentry ι G f (fun i => (m i:ℝ)) (fun i => (r i).num) q A H
    (fun i hi => hN.trans (hA i (hGS hi)).1)
    (fun i hi => (hH i (hGS hi)).trans (hA i (hGS hi)).1)
    beta (3*U₃/2) hbeta (by positivity)
    (fun i hi => (hsmall i (hGS hi)).1) (fun i hi => (hsmall i (hGS hi)).2)
    (fun i hi w hw => (hcf i (hGS hi) w (hsub i (hGS hi) hw)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4))
    (by
      intro i hi w hw
      have hh := hupper i (hGS hi) w (hsub i (hGS hi) hw) 4 (by norm_num)
      rw [hscale4] at hh
      convert hh using 1
      dsimp only [beta]
      ring)
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

                                                                         
                                                                  
                                                                            
theorem positive_difference_rounded_cubic_scales
    (F : ℝ → ℝ) {σ c J η y z T M N R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hM : 2 ≤ M) (hN : 0 < N) (hR : 0 < R)
    (hz : z∈Icc M (2*M)) (hphase : T*N*R^2=M^3) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    c/(12*σ*N*R^2) ≤ iteratedDeriv 3 f (round z)/6 ∧
      iteratedDeriv 3 f (round z)/6 ≤ J/(2*σ*N*R^2) := by
  intro f
  have hMp : 0 < M := by linarith only [hM]
  have hr := abs_le.mp (abs_sub_round z)
  have hm : (round z:ℝ)∈Icc (3*M/4) (9*M/4) := by
    constructor <;> linarith only [hr.1,hr.2,hz.1,hz.2,hM]
  have hn : (round z:ℝ)/M∈Icc (3/4:ℝ) (9/4) := by
    constructor
    · apply (le_div_iff₀ hMp).mpr
      linarith only [hm.1]
    · apply (div_le_iff₀ hMp).mpr
      linarith only [hm.2]
  have hy' : y∈Icc (1/2:ℝ) 3 :=
    ⟨by linarith only [hy.1],by linarith only [hy.2]⟩
  have hlow := positive_difference_third_signed_lower F (y:=y) hσ hη hηmax hc hn hy' hf hnegative
  have hu := positive_jets_difference_mixed_upper F hσ hJ hη hηmax hn hy' hf hbound
    3 0 (by norm_num) (by norm_num)
  simp only [iteratedDeriv_zero] at hu
  have hm0 : 0 < (round z:ℝ)/M := by linarith only [hn.1]
  have hs0 : 0 < (round z:ℝ)/M+η*y := add_pos hm0 (mul_pos hη (by linarith only [hy.1]))
  have hFx : ContDiffAt ℝ 3 F ((round z:ℝ)/M) :=
    (hf _ hm0).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hFz : ContDiffAt ℝ 3 (fun u => F (u+η*y)) ((round z:ℝ)/M) :=
    ((hf _ hs0).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)).comp
      ((round z:ℝ)/M) (contDiffAt_id.add contDiffAt_const)
  rw [iteratedDeriv_div_const,iteratedDeriv_fun_sub hFx hFz,iteratedDeriv_comp_add_const] at hu
  have hid := positive_difference_physical_iteratedDeriv F (T:=T) (σ:=σ) hMp
    (show 0 < (round z:ℝ) by linarith only [hm.1,hMp])
    (mul_nonneg hη.le (by linarith only [hy.1])) hf 3
  have hscale : T/M^3=1/(N*R^2) := by
    apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    nlinarith only [hphase]
  dsimp only [f]
  rw [hid,hscale]
  have hupper := (le_abs_self _).trans hu
  constructor
  · have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlow (show 0 ≤ 1/(N*R^2) by positivity))
      (by norm_num : (0:ℝ) ≤ 6)
    convert hh using 1
    ring
  · have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hupper (show 0 ≤ 1/(N*R^2) by positivity))
      (by norm_num : (0:ℝ) ≤ 6)
    convert hh using 1
    ring

                                                                  
                                                                
                                                                     
                                      
                                                                  
theorem source_arc_fourier_cloud_matrices
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ι → ℝ → ℝ) (z : ι → ℝ) (r : ι → ℚ) (v : ι → ℤ)
    (Q K₀ : ℕ) [NeZero K₀] (μ₀ U₀ : ℝ) (hμ₀ : 0 < μ₀)
    (hμbounds : ∀ i∈S, μ₀ ≤ iteratedDeriv 3 (f i) (round (z i))/6 ∧
      iteratedDeriv 3 (f i) (round (z i))/6 ≤ U₀)
    (hlevel : ∀ i∈S, iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ))
    (hden : ∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den)
    (hinv : ∀ i∈S, ((r i).den:ℤ) ∣ (r i).num*v i-1) :
    let q := fun i => (r i).den
    let μ := fun i => iteratedDeriv 3 (f i) (round (z i))/6
    let ℓ := fun i => deriv (f i) (round (z i))
    let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
    let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
    let K := fun i => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun i p =>
      (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let w := fun ip : ι × Fin 2 =>
      (![Int.fract (x ip.1 ip.2 0),Int.fract (x ip.1 ip.2 1),
        x ip.1 ip.2 2/Real.sqrt K₀,x ip.1 ip.2 3/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    let P := (V ×ˢ V).filter (fun ij => ∀ d, |w ij.1 d-w ij.2 d| ≤ 2*radius d)
    let h := fun i => iteratedDeriv 2 (f i) (z i)/2
    let D := (Real.sqrt K₀/(9*(K₀:ℝ))+Real.sqrt K₀/(12*(K₀:ℝ)^2))*
      Real.sqrt (U₀*(Q:ℝ)^3)
    ∃ A : ((ι × Fin 2) × (ι × Fin 2)) → Fin 4 → ℤ,
      ∀ ij∈P,
        A ij 0*A ij 3-A ij 1*A ij 2=1 ∧
        let t := (A ij 2:ℝ)*h ij.1.1+A ij 3
        t=(q ij.2.1:ℝ)/q ij.1.1 ∧ (1:ℝ)/2 ≤ t ∧ t ≤ 2 ∧
        ((A ij 0:ℝ)*h ij.1.1+A ij 1)/t=h ij.2.1 ∧
        |(A ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) ∧
        |μ ij.2.1/μ ij.1.1*t^3-1| ≤
          (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2) ∧
        |τ ij.1.1 ij.1.2-τ ij.2.1 ij.2.2| ≤ D ∧
        (∃ e₁ e₂ : ℤ,
          let F₁ := 2*(round (z ij.2.1):ℝ)-2*(A ij 3:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 2:ℝ)*ℓ ij.1.1
          let F₂ := ℓ ij.2.1-2*(A ij 1:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 0:ℝ)*ℓ ij.1.1
          |F₁-e₁| ≤ (q ij.2.1:ℝ)/(6*(K₀:ℝ))+|(A ij 2:ℝ)|/q ij.1.1 ∧
          |(F₂-e₂)-h ij.2.1*(F₁-e₁)| ≤ 2*D/q ij.2.1) ∧
        ((Q:ℝ)^2/(6*(K₀:ℝ)^2) < 1 →
          A ij 2=0 ∧ q ij.1.1=q ij.2.1 ∧
            (q ij.1.1:ℤ) ∣ (r ij.2.1).num-(r ij.1.1).num) := by
  classical
  intro q μ ℓ b τ K x V w radius P h D
  have hK : (0:ℝ) < K₀ := by exact_mod_cast (NeZero.pos K₀)
  have hone (ij : (ι × Fin 2) × (ι × Fin 2)) (hij : ij∈P) :
      ∃ A : Fin 4 → ℤ, A 0*A 3-A 1*A 2=1 ∧
        let t := (A 2:ℝ)*h ij.1.1+A 3
        t=(q ij.2.1:ℝ)/q ij.1.1 ∧ (1:ℝ)/2 ≤ t ∧ t ≤ 2 ∧
        ((A 0:ℝ)*h ij.1.1+A 1)/t=h ij.2.1 ∧
        |(A 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) ∧
        |μ ij.2.1/μ ij.1.1*t^3-1| ≤
          (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2) ∧
        |τ ij.1.1 ij.1.2-τ ij.2.1 ij.2.2| ≤ D ∧
        (∃ e₁ e₂ : ℤ,
          let F₁ := 2*(round (z ij.2.1):ℝ)-2*(A 3:ℝ)*(round (z ij.1.1):ℝ)-
            (A 2:ℝ)*ℓ ij.1.1
          let F₂ := ℓ ij.2.1-2*(A 1:ℝ)*(round (z ij.1.1):ℝ)-
            (A 0:ℝ)*ℓ ij.1.1
          |F₁-e₁| ≤ (q ij.2.1:ℝ)/(6*(K₀:ℝ))+|(A 2:ℝ)|/q ij.1.1 ∧
          |(F₂-e₂)-h ij.2.1*(F₁-e₁)| ≤ 2*D/q ij.2.1) ∧
        ((Q:ℝ)^2/(6*(K₀:ℝ)^2) < 1 →
          A 2=0 ∧ q ij.1.1=q ij.2.1 ∧
            (q ij.1.1:ℤ) ∣ (r ij.2.1).num-(r ij.1.1).num) := by
    have hp := Finset.mem_filter.mp hij
    have hi : ij.1.1∈S := (Finset.mem_product.mp (Finset.mem_product.mp hp.1).1).1
    have hj : ij.2.1∈S := (Finset.mem_product.mp (Finset.mem_product.mp hp.1).2).1
    have hqi : (0:ℝ) < q ij.1.1 := Nat.cast_pos.mpr (r ij.1.1).pos
    have hqj : (0:ℝ) < q ij.2.1 := Nat.cast_pos.mpr (r ij.2.1).pos
    have hmi : μ₀ ≤ μ ij.1.1 ∧ μ ij.1.1 ≤ U₀ := hμbounds _ hi
    have hmj : μ₀ ≤ μ ij.2.1 ∧ μ ij.2.1 ≤ U₀ := hμbounds _ hj
    have hmip : 0 < μ ij.1.1 := hμ₀.trans_le hmi.1
    have hmjp : 0 < μ ij.2.1 := hμ₀.trans_le hmj.1
    have hU₀ : 0 < U₀ := hmip.trans_le hmi.2
    have hconstraints := TaoTrudgianYang2025.actual_four_coordinate_constraints
      K₀ (q ij.1.1) (q ij.2.1) Q (r ij.2.1).num (v ij.1.1) (v ij.2.1)
      (r ij.1.1).pos (r ij.2.1).pos (hden _ hi).1 (hinv _ hj)
      hmip hmjp hmi.2 ij.1.2 ij.2.2 hp.2
    have htau : |τ ij.1.1 ij.1.2-τ ij.2.1 ij.2.2| ≤ D := hconstraints.1
    obtain ⟨a,b₀,c,d,e₁,e₂,hdet,hnum,hdenom,hgamma,hstrip₁,hstrip₂⟩ :=
      TaoTrudgianYang2025.actual_source_affine_lattice_strip
        K₀ (q ij.1.1) (q ij.2.1) Q
        (r ij.1.1).num (r ij.2.1).num (v ij.1.1) (v ij.2.1)
        (round (z ij.1.1)) (round (z ij.2.1))
        (r ij.1.1).pos (r ij.2.1).pos (hden _ hi).1 (hinv _ hi) (hinv _ hj)
        hmip hmjp hmi.2 ij.1.2 ij.2.2 hp.2
    have hhi : h ij.1.1=((r ij.1.1).num:ℝ)/q ij.1.1 := by
      dsimp only [h]
      rw [hlevel _ hi,Rat.cast_def]
    have hhj : h ij.2.1=((r ij.2.1).num:ℝ)/q ij.2.1 := by
      dsimp only [h]
      rw [hlevel _ hj,Rat.cast_def]
    have hnumR : (a:ℝ)*(r ij.1.1).num+(b₀:ℝ)*q ij.1.1=(r ij.2.1).num := by
      exact_mod_cast hnum
    have hdenR : (c:ℝ)*(r ij.1.1).num+(d:ℝ)*q ij.1.1=q ij.2.1 := by
      exact_mod_cast hdenom
    have ht : (c:ℝ)*h ij.1.1+d=(q ij.2.1:ℝ)/q ij.1.1 := by
      rw [hhi]
      apply (eq_div_iff hqi.ne').mpr
      field_simp
      nlinarith only [hdenR]
    have hm : ((a:ℝ)*h ij.1.1+b₀)/((c:ℝ)*h ij.1.1+d)=h ij.2.1 := by
      rw [ht,hhi,hhj]
      field_simp
      nlinarith only [hnumR]
    have hqiQ : (q ij.1.1:ℝ) ≤ Q := by exact_mod_cast (hden _ hi).1
    have hqjQ : (q ij.2.1:ℝ) ≤ Q := by exact_mod_cast (hden _ hj).1
    have hQqi : (Q:ℝ) ≤ 2*q ij.1.1 := by exact_mod_cast (hden _ hi).2
    have hQqj : (Q:ℝ) ≤ 2*q ij.2.1 := by exact_mod_cast (hden _ hj).2
    have hbudget : (q ij.1.1:ℝ)*q ij.2.1/(6*(K₀:ℝ)^2) ≤
        (Q:ℝ)^2/(6*(K₀:ℝ)^2) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      calc
        _ ≤ (Q:ℝ)*Q := by gcongr
        _ = _ := by ring
    have hsqrt : 0 < Real.sqrt (K₀:ℝ) := Real.sqrt_pos.mpr hK
    have hdual : |K ij.1.1-K ij.2.1| ≤ Real.sqrt K₀/(6*(K₀:ℝ)^2) := by
      have hh := hp.2 (2 : Fin 4)
      change |K ij.1.1/Real.sqrt K₀-K ij.2.1/Real.sqrt K₀| ≤
        2*((1/(K₀:ℝ)^2)/12) at hh
      rw [←sub_div,abs_div,abs_of_pos hsqrt] at hh
      have hh' := (div_le_iff₀ hsqrt).mp hh
      convert hh' using 1
      ring
    have hcoef := TaoTrudgianYang2025.bourgain_dual_variable_denominator_difference
      hmip hmjp hqi hqj hmi.2 hmj.2 hqiQ hqjQ hQqi hdual
    have hrelative :
        |μ ij.2.1/μ ij.1.1*((c:ℝ)*h ij.1.1+d)^3-1| ≤
          (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2) := by
      rw [ht]
      have he : μ ij.2.1/μ ij.1.1*((q ij.2.1:ℝ)/q ij.1.1)^3-1 =
          (μ ij.2.1*((q ij.2.1:ℝ)/q ij.1.1)^3-μ ij.1.1)/μ ij.1.1 := by
        field_simp
      rw [he,abs_div,abs_of_pos hmip]
      calc
        _ ≤ (16*U₀*Real.sqrt (U₀*(Q:ℝ)^3)*
            (Real.sqrt K₀/(6*(K₀:ℝ)^2)))/μ ij.1.1 :=
          div_le_div_of_nonneg_right hcoef hmip.le
        _ ≤ (16*U₀*Real.sqrt (U₀*(Q:ℝ)^3)*
            (Real.sqrt K₀/(6*(K₀:ℝ)^2)))/μ₀ :=
          div_le_div_of_nonneg_left (by positivity) hμ₀ hmi.1
        _ = _ := by ring
    refine ⟨![a,b₀,c,d],hdet,ht,?_,?_,hm,hgamma.trans hbudget,hrelative,htau,?_,?_⟩
    · change (1:ℝ)/2 ≤ (c:ℝ)*h ij.1.1+d
      rw [ht]
      apply (le_div_iff₀ hqi).mpr
      linarith only [hqiQ,hQqj]
    · change (c:ℝ)*h ij.1.1+d ≤ 2
      rw [ht]
      exact (div_le_iff₀ hqi).mpr (hqjQ.trans hQqi)
    · refine ⟨e₁,e₂,hstrip₁,?_⟩
      rw [hhj]
      exact hstrip₂
    · intro hb
      have hg : c=0 := Int.abs_lt_one_iff.mp (by exact_mod_cast hgamma.trans_lt (hbudget.trans_lt hb))
      have hqiZ : (0:ℤ) < q ij.1.1 := by exact_mod_cast hqi
      have hqjZ : (0:ℤ) < q ij.2.1 := by exact_mod_cast hqj
      rw [hg,zero_mul,zero_add] at hdenom
      rw [hg,mul_zero,sub_zero] at hdet
      have hd : 0 < d := by nlinarith only [hqiZ,hqjZ,hdenom]
      have ha : 0 < a := by nlinarith only [hd,hdet]
      have hd1 : d=1 := by nlinarith only [hd,ha,hdet]
      have ha1 : a=1 := by nlinarith only [hdet,hd1]
      refine ⟨hg,?_,?_⟩
      · have he : (q ij.1.1:ℤ)=q ij.2.1 := by simpa only [hd1,one_mul] using hdenom
        exact_mod_cast he
      · refine ⟨b₀,?_⟩
        rw [ha1,one_mul] at hnum
        nlinarith only [hnum]
  let A := fun ij => if hij : ij∈P then Classical.choose (hone ij hij) else 0
  refine ⟨A,?_⟩
  intro ij hij
  dsimp only [A]
  rw [dite_eq_left hij]
  exact Classical.choose_spec (hone ij hij)

                                                                       
                                                                    
                                                
theorem curvature_pair_card_le_matrix_blocks
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2)))
    (A : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (ha hb : ℝ → ℝ) (za zb : ℤ → ℝ) (D : Set ℝ) {N Z : ℝ}
    (hN : 0 < N) (hinj : Set.InjOn hb D)
    (hz : ∀ ij∈P, zb ij.2.1∈D)
    (hspan : ∀ ij∈P, N ≤ Z+(ij.2.1:ℝ)*N+2*N-(round (zb ij.2.1):ℝ) ∧
      Z+(ij.2.1:ℝ)*N+2*N-(round (zb ij.2.1):ℝ) ≤ 3*N)
    (hmap : ∀ ij∈P,
      ((A ij 0:ℝ)*ha (za ij.1.1)+A ij 1)/
        ((A ij 2:ℝ)*ha (za ij.1.1)+A ij 3)=hb (zb ij.2.1)) :
    P.card ≤ 12*(P.image (fun ij => (A ij,ij.1.1))).card := by
  classical
  apply Finset.card_le_mul_card_image P 12
  intro key hkey
  obtain ⟨ij₀,hij₀,hkey₀⟩ := Finset.mem_image.mp hkey
  let m : ℝ := round (zb ij₀.2.1)
  obtain ⟨J,hJ,_hJlow,hJhigh⟩ := physical_grid_interval_card (Z:=Z)
    (x:=m-N) (z:=m+N) hN (by linarith only [hN])
  have hJcard : J.card ≤ 3 := by
    have hh : (J.card:ℝ) ≤ 3 := hJhigh.trans_eq (by field_simp; ring)
    exact_mod_cast hh
  let W := (Finset.univ : Finset (Fin 2)) ×ˢ (J ×ˢ (Finset.univ : Finset (Fin 2)))
  let E := P.filter (fun ij => (A ij,ij.1.1)=key)
  have hsame ij (hij : ij∈E) : zb ij.2.1=zb ij₀.2.1 := by
    have hd := Finset.mem_filter.mp hij
    have hAe : A ij=A ij₀ := (congrArg Prod.fst hd.2).trans (congrArg Prod.fst hkey₀).symm
    have hke : ij.1.1=ij₀.1.1 := (congrArg Prod.snd hd.2).trans (congrArg Prod.snd hkey₀).symm
    apply hinj (hz ij hd.1) (hz ij₀ hij₀)
    rw [←hmap ij hd.1,←hmap ij₀ hij₀,hAe,hke]
  have hbound : E.card ≤ W.card := by
    apply Finset.card_le_card_of_injOn (fun ij => (ij.1.2,(ij.2.1,ij.2.2)))
    · intro ij hij
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_univ _,Finset.mem_product.mpr ⟨?_,Finset.mem_univ _⟩⟩
      apply (hJ ij.2.1).mpr
      have hh := hspan ij (Finset.mem_filter.mp hij).1
      rw [hsame ij hij] at hh
      change N ≤ Z+(ij.2.1:ℝ)*N+2*N-m ∧ Z+(ij.2.1:ℝ)*N+2*N-m ≤ 3*N at hh
      constructor <;> linarith only [hh.1,hh.2]
    · intro u hu v hv he
      have hku : u.1.1=key.2 := congrArg Prod.snd (Finset.mem_filter.mp hu).2
      have hkv : v.1.1=key.2 := congrArg Prod.snd (Finset.mem_filter.mp hv).2
      apply Prod.ext
      · exact Prod.ext (hku.trans hkv.symm) (congrArg Prod.fst he)
      · exact Prod.ext (congrArg (fun x => x.2.1) he) (congrArg (fun x => x.2.2) he)
  have hw : W.card=2*(J.card*2) := by simp only [W,Finset.card_product,Finset.card_univ,Fintype.card_fin]
  rw [hw] at hbound
  change E.card ≤ 12
  omega

                                                                     
                                                                 
                                                          
theorem rounded_offset_floor_block_count
    (I : Finset ℤ) (z : ℤ → ℝ) (Alen : ℤ → ℕ) (N : ℕ) (Z : ℤ) (W : ℝ)
    (hN : 0 < N)
    (hgeometry : ∀ k∈I, N ≤ Alen k ∧ Alen k ≤ 3*N ∧
      round (z k)+(Alen k:ℤ)=Z+(N:ℤ)*k+2*(N:ℤ)) :
    I.card ≤ 5*(I.image (fun k => ⌊(z k-W)/(N:ℝ)⌋)).card := by
  classical
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  apply Finset.card_le_mul_card_image I 5
  intro j _
  let lower := W+(j:ℝ)*N-(N:ℝ)-1/2
  let upper := W+((j:ℝ)+1)*N+(N:ℝ)+1/2
  obtain ⟨J,hJ,_hJlow,hJhigh⟩ := physical_grid_interval_card (N:=(N:ℝ)) (Z:=(Z:ℝ))
    (x:=lower) (z:=upper) hNp (by dsimp only [lower,upper]; nlinarith only [hNp])
  have hJcard : J.card ≤ 5 := by
    have hwidth : upper-lower ≤ 4*(N:ℝ) := by
      dsimp only [upper,lower]
      nlinarith only [hN1]
    have hd : (upper-lower)/(N:ℝ) ≤ 4 := (div_le_iff₀ hNp).mpr hwidth
    have hh : (J.card:ℝ) ≤ 5 := by linarith only [hJhigh,hd]
    exact_mod_cast hh
  apply (Finset.card_le_card ?_).trans hJcard
  intro k hk
  have hkI := (Finset.mem_filter.mp hk).1
  have hklabel := (Finset.mem_filter.mp hk).2
  change ⌊(z k-W)/(N:ℝ)⌋=j at hklabel
  have hlo := Int.floor_le ((z k-W)/(N:ℝ))
  have hhi := Int.lt_floor_add_one ((z k-W)/(N:ℝ))
  rw [hklabel] at hlo hhi
  have hzl := (le_div_iff₀ hNp).mp hlo
  have hzu := (div_lt_iff₀ hNp).mp hhi
  have hr := abs_le.mp (abs_sub_round (z k))
  have hg := hgeometry k hkI
  have hAlo : (N:ℝ) ≤ Alen k := by exact_mod_cast hg.1
  have hAhi : (Alen k:ℝ) ≤ 3*(N:ℝ) := by exact_mod_cast hg.2.1
  have he : (round (z k):ℝ)+(Alen k:ℝ)=(Z:ℝ)+(N:ℝ)*k+2*(N:ℝ) := by
    exact_mod_cast hg.2.2
  apply (hJ k).mpr
  dsimp only [lower,upper]
  constructor <;> nlinarith only [hzl,hzu,hr.1,hr.2,hAlo,hAhi,he]

                                                                       
                                                                       
                                                   
theorem bounded_action_narrow_ratios_trace_two
    (a b c d : ℤ) {x y H L : ℝ}
    (hdet : a*d-b*c=1) (hx0 : x ≠ 0)
    (hx : |x| ≤ H) (hy : |y| ≤ H)
    (haction : |(c:ℝ)| * H ≤ L)
    (hmap : ((a:ℝ)*x+b)/((c:ℝ)*x+d)=y)
    (hden : |((c:ℝ)*x+d)-1| ≤ 1/(8*(L+3)))
    (hnum : |((a:ℝ)*x+b)/x-1| ≤ 1/(8*(L+3))) :
    a+d=2 ∧ (a-1)^2= -b*c := by
  let θ : ℝ := (c:ℝ)*x+d
  let φ : ℝ := ((a:ℝ)*x+b)/x
  have hθ : |θ-1| ≤ 1/(8*(L+3)) := hden
  have hφ : |φ-1| ≤ 1/(8*(L+3)) := hnum
  have hH : 0 ≤ H := (abs_nonneg x).trans hx
  have hL : 0 ≤ L := (mul_nonneg (abs_nonneg (c:ℝ)) hH).trans haction
  have hLp : 0 < L+3 := by linarith only [hL]
  have hε : 1/(8*(L+3)) ≤ (1:ℝ)/24 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith only [hL])
  have hθbounds := abs_le.mp (hθ.trans hε)
  have hdetR : (a:ℝ)*d-(b:ℝ)*c=1 := by exact_mod_cast hdet
  have hentries := TaoTrudgianYang2025.bourgain_mobius_entry_bounds hdetR
    (by dsimp only [θ] at hθbounds; linarith only [hθbounds.1])
    (by dsimp only [θ] at hθbounds; linarith only [hθbounds.2]) hmap hx hy
  have ha : |1-(a:ℝ)| ≤ L+3 := by
    calc
      _ ≤ |(1:ℝ)|+|(a:ℝ)| := abs_sub _ _
      _ ≤ L+3 := by norm_num only [abs_one]; linarith only [hentries.1,haction]
  have hd : |1-(d:ℝ)| ≤ L+3 := by
    calc
      _ ≤ |(1:ℝ)|+|(d:ℝ)| := abs_sub _ _
      _ ≤ L+3 := by norm_num only [abs_one]; linarith only [hentries.2,haction]
  have hid : θ*(a:ℝ)+φ*(d:ℝ)=1+θ*φ := by
    dsimp only [θ,φ]
    field_simp [hx0]
    nlinarith only [congrArg (fun w : ℝ => w*x) hdetR]
  have h1 : |(θ-1)*(1-(a:ℝ))| ≤ 1/8 := by
    rw [abs_mul]
    exact (mul_le_mul hθ ha (abs_nonneg _) (by positivity)).trans_eq (by field_simp)
  have h2 : |(φ-1)*(1-(d:ℝ))| ≤ 1/8 := by
    rw [abs_mul]
    exact (mul_le_mul hφ hd (abs_nonneg _) (by positivity)).trans_eq (by field_simp)
  have h3 : |(θ-1)*(φ-1)| ≤ 1/576 := by
    rw [abs_mul]
    exact (mul_le_mul (hθ.trans hε) (hφ.trans hε) (abs_nonneg _)
      (by norm_num)).trans_eq (by norm_num)
  have he : |((a+d-2:ℤ):ℝ)| < 1 := by
    push_cast
    have hb1 := abs_le.mp h1
    have hb2 := abs_le.mp h2
    have hb3 := abs_le.mp h3
    apply abs_lt.mpr
    constructor <;> nlinarith only [hid,hb1.1,hb1.2,hb2.1,hb2.2,hb3.1,hb3.2]
  have hz : a+d-2=0 := Int.abs_lt_one_iff.mp (by exact_mod_cast he)
  refine ⟨by omega,?_⟩
  have hdform : d=2-a := by omega
  rw [hdform] at hdet
  nlinarith only [hdet]

                                                                      
                                                                    
                                                                    
theorem bounded_action_narrow_nontriangular_matrix_count
    (S : Finset (Fin 4 → ℤ)) (x y : (Fin 4 → ℤ) → ℝ) {H L : ℝ}
    (hL : 0 ≤ L)
    (hdet : ∀ A∈S, A 0*A 3-A 1*A 2=1)
    (hnontri : ∀ A∈S, A 1 ≠ 0 ∧ A 2 ≠ 0)
    (hpoints : ∀ A∈S, x A ≠ 0 ∧ |x A| ≤ H ∧ |y A| ≤ H)
    (haction : ∀ A∈S, |(A 2:ℝ)| * H ≤ L)
    (hmap : ∀ A∈S, ((A 0:ℝ)*x A+A 1)/((A 2:ℝ)*x A+A 3)=y A)
    (hden : ∀ A∈S, |((A 2:ℝ)*x A+A 3)-1| ≤ 1/(8*(L+3)))
    (hnum : ∀ A∈S, |((A 0:ℝ)*x A+A 1)/x A-1| ≤ 1/(8*(L+3))) :
    (S.card:ℝ) ≤ (2*(L+3)^2+1)*(2*L+5)^2*(L+3)^2 := by
  classical
  have hε : 1/(8*(L+3)) ≤ (1:ℝ)/24 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith only [hL])
  have hdata A (hA : A∈S) :
      |(A 2:ℝ)| ≤ (L+3)^2 ∧
      |(A 0:ℝ)| ≤ |(A 2:ℝ)| * L+2 ∧
      |(A 3:ℝ)| ≤ |(A 2:ℝ)| * L+2 := by
    have hp := hpoints A hA
    have htr := bounded_action_narrow_ratios_trace_two (A 0) (A 1) (A 2) (A 3)
      (hdet A hA) hp.1 hp.2.1 hp.2.2 (haction A hA)
      (hmap A hA) (hden A hA) (hnum A hA)
    have hdetR : (A 0:ℝ)*A 3-(A 1:ℝ)*A 2=1 := by exact_mod_cast hdet A hA
    have ht := abs_le.mp ((hden A hA).trans hε)
    have he := TaoTrudgianYang2025.bourgain_mobius_entry_bounds hdetR
      (by linarith only [ht.1]) (by linarith only [ht.2])
      (hmap A hA) hp.2.1 hp.2.2
    have ha : |(A 0:ℝ)| ≤ L+2 := by linarith only [he.1,haction A hA]
    have hd : |(A 3:ℝ)| ≤ L+2 := by linarith only [he.2,haction A hA]
    have hb1 : (1:ℝ) ≤ |(A 1:ℝ)| := by exact_mod_cast Int.one_le_abs (hnontri A hA).1
    have hc1 : (1:ℝ) ≤ |(A 2:ℝ)| := by exact_mod_cast Int.one_le_abs (hnontri A hA).2
    have hasub : |(A 0:ℝ)-1| ≤ L+3 := by
      calc
        _ ≤ |(A 0:ℝ)|+|(1:ℝ)| := abs_sub _ _
        _ ≤ L+3 := by rw [abs_one]; linarith only [ha]
    have hsq := pow_le_pow_left₀ (abs_nonneg ((A 0:ℝ)-1)) hasub 2
    rw [sq_abs] at hsq
    have hsqR : ((A 0:ℝ)-1)^2= -(A 1:ℝ)*A 2 := by exact_mod_cast htr.2
    have hprod := congrArg abs hsqR
    rw [abs_of_nonneg (sq_nonneg _),abs_mul,abs_neg] at hprod
    refine ⟨?_,?_,?_⟩
    · nlinarith only [hb1,hprod,hsq,abs_nonneg (A 2:ℝ)]
    · nlinarith only [ha,hc1,hL]
    · nlinarith only [hd,hc1,hL]
  have hsum := TaoTrudgianYang2025.bourgain_resonance_matrix_weight_sum
    (X:=L) (Gamma:=(L+3)^2) (W:=0) S hL (sq_nonneg _) (by norm_num)
    hdet (fun A hA => ⟨(hnontri A hA).2,(hdata A hA).1⟩)
    (fun A hA => (hdata A hA).2.1) (fun A hA => (hdata A hA).2.2)
  simpa only [zero_div,add_zero,Finset.sum_const,nsmul_eq_mul,mul_one] using hsum

                                                                 
                                                                  
                                                                  
                                                                     
theorem same_scaled_floor_relative_bound {u v Q δ : ℝ}
    (hQ : 0 < Q) (hδ : 0 < δ) (hu : Q ≤ |u|)
    (hbin : ⌊u/(δ*Q)⌋=⌊v/(δ*Q)⌋) :
    |v/u-1| ≤ δ := by
  have hden : 0 < δ*Q := mul_pos hδ hQ
  have hup : 0 < |u| := hQ.trans_le hu
  have hdiff := Int.abs_sub_lt_one_of_floor_eq_floor hbin
  rw [←sub_div,abs_div,abs_of_pos hden] at hdiff
  have hd : |v-u| ≤ δ*Q := by
    have hh := (div_lt_iff₀ hden).mp hdiff
    simpa only [one_mul,abs_sub_comm u v] using hh.le
  have he : v/u-1=(v-u)/u := by field_simp [abs_pos.mp hup]
  rw [he,abs_div]
  exact (div_le_iff₀ hup).mpr (hd.trans (mul_le_mul_of_nonneg_left hu hδ.le))


                                                               
                                                                
                          
theorem scaled_floor_image_card
    {ι : Type*} (S : Finset ι) (u : ι → ℝ) {Q δ R : ℝ}
    (hQ : 0 < Q) (hδ : 0 < δ) (hR : 0 ≤ R)
    (hu : ∀ i∈S, |u i| ≤ R*Q) :
    ((S.image (fun i => ⌊u i/(δ*Q)⌋)).card:ℝ) ≤ 2*R/δ+3 := by
  classical
  have hden : 0 < δ*Q := mul_pos hδ hQ
  have hper i (hi : i∈S) : |(⌊u i/(δ*Q)⌋:ℝ)| ≤ R/δ+1 := by
    have hb : |u i/(δ*Q)| ≤ R/δ := by
      rw [abs_div,abs_of_pos hden]
      calc
        _ ≤ R*Q/(δ*Q) := div_le_div_of_nonneg_right (hu i hi) hden.le
        _ = _ := by field_simp
    have hb' := abs_le.mp hb
    have hlo := Int.floor_le (u i/(δ*Q))
    have hhi := Int.lt_floor_add_one (u i/(δ*Q))
    apply abs_le.mpr
    constructor <;> linarith only [hb'.1,hb'.2,hlo,hhi]
  have hh := integer_card_le_of_abs_sub_le (a:=0)
    (S.image (fun i => ⌊u i/(δ*Q)⌋)) (by positivity : (0:ℝ) ≤ R/δ+1)
    (by
      intro k hk
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
      simpa only [sub_zero] using hper i hi)
  convert hh using 1
  ring

                                                                       
                                                                     
                                                                       
theorem rational_narrow_band_partition
    {ι : Type*} (S : Finset ι) (r : ι → ℚ) (Q : ℕ) {lambda U δ : ℝ}
    (hQ : 0 < Q) (hlambda : 0 < lambda) (hU : 0 ≤ U) (hδ : 0 < δ)
    (hcurv : ∀ i∈S, lambda ≤ |(r i:ℝ)| ∧ |(r i:ℝ)| ≤ U)
    (hden : ∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den) :
    let q₀ := (Q:ℝ)/2
    let p₀ := lambda*(Q:ℝ)/2
    let color := fun i => (⌊((r i).den:ℝ)/(δ*q₀)⌋,⌊((r i).num:ℝ)/(δ*p₀)⌋)
    ((S.image color).card:ℝ) ≤ (4/δ+3)*(4*U/(lambda*δ)+3) ∧
      ∀ i∈S, ∀ j∈S, color i=color j →
        |((r j).den:ℝ)/(r i).den-1| ≤ δ ∧
        |((r j).num:ℝ)/(r i).num-1| ≤ δ := by
  classical
  intro q₀ p₀ color
  have hQR : (0:ℝ) < Q := by exact_mod_cast hQ
  have hq₀ : 0 < q₀ := by dsimp only [q₀]; positivity
  have hp₀ : 0 < p₀ := by dsimp only [p₀]; positivity
  have hqlo i (hi : i∈S) : q₀ ≤ ((r i).den:ℝ) := by
    have hh : (Q:ℝ) ≤ 2*((r i).den:ℝ) := by exact_mod_cast (hden i hi).2
    dsimp only [q₀]
    linarith only [hh]
  have hqhi i (hi : i∈S) : ((r i).den:ℝ) ≤ Q := by exact_mod_cast (hden i hi).1
  have hn i (hi : i∈S) :
      p₀ ≤ |((r i).num:ℝ)| ∧ |((r i).num:ℝ)| ≤ U*(Q:ℝ) := by
    have hd : (0:ℝ) < (r i).den := by exact_mod_cast (r i).pos
    have hl := (hcurv i hi).1
    have hu := (hcurv i hi).2
    rw [Rat.cast_def,abs_div,abs_of_pos hd] at hl hu
    have hl' := (le_div_iff₀ hd).mp hl
    have hu' := (div_le_iff₀ hd).mp hu
    constructor
    · calc
        p₀ = lambda*q₀ := by dsimp only [p₀,q₀]; ring
        _ ≤ lambda*((r i).den:ℝ) := mul_le_mul_of_nonneg_left (hqlo i hi) hlambda.le
        _ ≤ _ := hl'
    · exact hu'.trans (mul_le_mul_of_nonneg_left (hqhi i hi) hU)
  have hfirst := scaled_floor_image_card S (fun i => ((r i).den:ℝ))
    hq₀ hδ (by norm_num : (0:ℝ) ≤ 2)
    (by
      intro i hi
      rw [abs_of_pos (by exact_mod_cast (r i).pos : (0:ℝ) < (r i).den)]
      have hh := hqhi i hi
      dsimp only [q₀]
      linarith only [hh])
  have hsecond := scaled_floor_image_card (R:=2*U/lambda) S (fun i => ((r i).num:ℝ))
    hp₀ hδ (div_nonneg (mul_nonneg (by norm_num) hU) hlambda.le)
    (by
      intro i hi
      calc
        _ ≤ U*(Q:ℝ) := (hn i hi).2
        _ = (2*U/lambda)*p₀ := by dsimp only [p₀]; field_simp)
  have hc₁ : ((S.image (fun i => (color i).1)).card:ℝ) ≤ 4/δ+3 := by
    convert hfirst using 1
    ring
  have hc₂ : ((S.image (fun i => (color i).2)).card:ℝ) ≤ 4*U/(lambda*δ)+3 := by
    convert hsecond using 1
    ring
  constructor
  · have hs : S.image color ⊆
        (S.image (fun i => (color i).1)) ×ˢ (S.image (fun i => (color i).2)) := by
      intro v hv
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hi,Finset.mem_image_of_mem _ hi⟩
    have hh := Finset.card_le_card hs
    rw [Finset.card_product] at hh
    have hhR : ((S.image color).card:ℝ) ≤
        ((S.image (fun i => (color i).1)).card:ℝ)*
          ((S.image (fun i => (color i).2)).card:ℝ) := by exact_mod_cast hh
    exact hhR.trans (mul_le_mul hc₁ hc₂ (by positivity) (by positivity))
  · intro i hi j _hj he
    constructor
    · apply same_scaled_floor_relative_bound hq₀ hδ
      · simpa only [abs_of_nonneg (Nat.cast_nonneg ((r i).den) : (0:ℝ) ≤ (r i).den)] using hqlo i hi
      · exact congrArg Prod.fst he
    · exact same_scaled_floor_relative_bound hp₀ hδ (hn i hi).1 (congrArg Prod.snd he)

                                                                 
                                                              
                                                    
theorem rational_narrow_band_twelfth_partition
    {ι : Type*} (S : Finset ι) (r : ι → ℚ) (Q : ℕ) {lambda U δ : ℝ}
    (hQ : 0 < Q) (hlambda : 0 < lambda) (hU : 0 ≤ U) (hδ : 0 < δ)
    (hcurv : ∀ i∈S, lambda ≤ |(r i:ℝ)| ∧ |(r i:ℝ)| ≤ U)
    (hden : ∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den) :
    let q₀ := (Q:ℝ)/2
    let p₀ := lambda*(Q:ℝ)/2
    let color := fun i => (⌊((r i).den:ℝ)/(δ*q₀)⌋,⌊((r i).num:ℝ)/(δ*p₀)⌋)
    ((S.image color).card:ℝ) ≤ (4/δ+3)*(4*U/(lambda*δ)+3) ∧
      (∀ i∈S, ∀ j∈S, color i=color j →
        |((r j).den:ℝ)/(r i).den-1| ≤ δ ∧
        |((r j).num:ℝ)/(r i).num-1| ≤ δ) ∧
      ∀ z : ι → ℂ, ‖∑ i∈S,z i‖^12 ≤
        ((4/δ+3)*(4*U/(lambda*δ)+3))^11*
          ∑ j∈S.image color, ‖∑ i∈S.filter (fun i => color i=j),z i‖^12 := by
  classical
  intro q₀ p₀ color
  have hd := rational_narrow_band_partition S r Q hQ hlambda hU hδ hcurv hden
  refine ⟨hd.1,hd.2,?_⟩
  intro z
  let J := S.image color
  let V := fun j => S.filter (fun i => color i=j)
  let g := fun j => ∑ i∈V j,z i
  have he : (∑ j∈J,g j)=∑ i∈S,z i :=
    Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem color hi) z
  have hnorm : ‖∑ i∈S,z i‖ ≤ ∑ j∈J,‖g j‖ := by
    rw [←he]
    exact norm_sum_le _ _
  have hp := pow_le_pow_left₀ (norm_nonneg _) hnorm 12
  have hholder := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg J
    (f:=fun j => ‖g j‖) (p:=(12:ℝ)) (by norm_num) (fun _ _ => norm_nonneg _)
  have hh : (∑ j∈J,‖g j‖)^12 ≤ (J.card:ℝ)^11*∑ j∈J,‖g j‖^12 := by
    simpa only [show (12:ℝ)-1=11 by norm_num,Real.rpow_ofNat] using hholder
  exact (hp.trans hh).trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ J.card) hd.1 11)
    (Finset.sum_nonneg (fun _ _ => by positivity)))

                                                                   
                                                            
theorem positive_difference_half_curvature_source_bounds
    (F : ℝ → ℝ) {σ c U η T M y z : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hT : 0 < T) (hM : 0 < M)
    (hy : y∈Icc (1:ℝ) 2) (hz : z∈Icc M (2*M))
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    c*T/(4*σ*M^2) ≤ |h y z| ∧ |h y z| ≤ (3*U/σ)*T/(2*M^2) := by
  intro f h
  let Hcurv := (3*U/σ)*T/(2*M^2)
  let Low := c*T/(4*σ*M^2)
  have hx : z/M∈Icc (3/4:ℝ) (9/4) := by
    constructor
    · apply (le_div_iff₀ hM).mpr
      linarith only [hz.1,hM]
    · apply (div_le_iff₀ hM).mpr
      linarith only [hz.2,hM]
  have hywide : y∈Icc (1/2:ℝ) 3 :=
    ⟨by linarith only [hy.1],by linarith only [hy.2]⟩
  have hxpos : 0 < z/M := by linarith only [hx.1]
  have hspos : 0 < z/M+η*y := add_pos hxpos (mul_pos hη (by linarith only [hy.1]))
  have hFx : ContDiffAt ℝ 2 F (z/M) :=
    (hf _ hxpos).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hFz : ContDiffAt ℝ 2 (fun u => F (u+η*y)) (z/M) :=
    ((hf _ hspos).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp
      (z/M) (contDiffAt_id.add contDiffAt_const)
  have hu := positive_jets_difference_mixed_upper F hσ hU hη hηmax hx hywide
    hf hbound 2 0 (by norm_num) (by norm_num)
  simp only [iteratedDeriv_zero] at hu
  have hl := positive_jets_difference_spatial_lower F hσ hc hη hηmax hx hywide
    hf htests 2 (by norm_num) (by norm_num)
  rw [iteratedDeriv_div_const,iteratedDeriv_fun_sub hFx hFz,iteratedDeriv_comp_add_const] at hu hl
  have hd := positive_difference_physical_iteratedDeriv F (T:=T) (σ:=σ) hM
    (hM.trans_le hz.1) (mul_nonneg hη.le (by linarith only [hy.1])) hf 2
  have hlow : Low ≤ |h y z| := by
    dsimp only [h,f]
    rw [hd,abs_div,abs_mul,abs_of_pos (div_pos hT (pow_pos hM 2)),
      abs_of_pos (by norm_num : (0:ℝ) < 2)]
    calc
      Low = (T/M^2)*(c/(2*σ))/2 := by dsimp only [Low]; ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hl (by positivity)) (by norm_num)
  refine ⟨hlow,?_⟩
  dsimp only [h,f]
  rw [hd,abs_div,abs_mul,abs_of_pos (div_pos hT (pow_pos hM 2)),
    abs_of_pos (by norm_num : (0:ℝ) < 2)]
  calc
    _ ≤ (T/M^2)*(3*U/σ)/2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hu (by positivity)) (by norm_num)
    _ = Hcurv := by dsimp only [Hcurv]; ring



                                                                    
                                                                     
                                                                        
                                                          
theorem narrow_band_matrix_translation_cases
    (a b c d : ℤ) {x lambda H δ : ℝ}
    (hlambda : 0 < lambda) (hxlo : lambda ≤ |x|) (hxhi : |x| ≤ H)
    (hδ : 0 ≤ δ) (hδmax : δ < 1)
    (hdet : a*d-b*c=1)
    (hden : |((c:ℝ)*x+d)-1| ≤ δ)
    (hnum : |((a:ℝ)*x+b)/x-1| ≤ δ) :
    (a=1 ∧ b=0 ∧ c=0 ∧ d=1) ∨
    (a=1 ∧ d=1 ∧ c=0 ∧ b≠0 ∧ |(b:ℝ)| ≤ δ*H) ∨
    (a=1 ∧ d=1 ∧ b=0 ∧ c≠0 ∧ |(c:ℝ)| ≤ δ/lambda) ∨
    (b≠0 ∧ c≠0) := by
  have hxabs : 0 < |x| := hlambda.trans_le hxlo
  have hx : x ≠ 0 := abs_pos.mp hxabs
  by_cases hc : c=0
  · have hdabs : |((d-1:ℤ):ℝ)| < 1 := by
      push_cast
      simpa only [hc,Int.cast_zero,zero_mul,zero_add] using hden.trans_lt hδmax
    have hd : d=1 := by
      have hh := Int.abs_lt_one_iff.mp (by exact_mod_cast hdabs)
      omega
    have ha : a=1 := by simpa only [hc,hd,mul_zero,mul_one,sub_zero] using hdet
    by_cases hb : b=0
    · exact Or.inl ⟨ha,hb,hc,hd⟩
    · apply Or.inr ∘ Or.inl
      refine ⟨ha,hd,hc,hb,?_⟩
      have he : ((a:ℝ)*x+b)/x-1=(b:ℝ)/x := by rw [ha]; push_cast; field_simp; ring
      rw [he,abs_div] at hnum
      calc
        |(b:ℝ)| ≤ δ*|x| := (div_le_iff₀ hxabs).mp hnum
        _ ≤ δ*H := mul_le_mul_of_nonneg_left hxhi hδ
  · by_cases hb : b=0
    · have he : ((a:ℝ)*x+b)/x-1=(a:ℝ)-1 := by rw [hb]; push_cast; field_simp; ring
      rw [he] at hnum
      have haabs : |((a-1:ℤ):ℝ)| < 1 := by
        push_cast
        exact hnum.trans_lt hδmax
      have ha : a=1 := by
        have hh := Int.abs_lt_one_iff.mp (by exact_mod_cast haabs)
        omega
      have hd : d=1 := by simpa only [hb,ha,zero_mul,one_mul,sub_zero] using hdet
      apply Or.inr ∘ Or.inr ∘ Or.inl
      refine ⟨ha,hd,hb,hc,?_⟩
      have hcx : |(c:ℝ)| * |x| ≤ δ := by
        simpa only [hd,Int.cast_one,add_sub_cancel_right,abs_mul] using hden
      apply (le_div_iff₀ hlambda).mpr
      exact (mul_le_mul_of_nonneg_left hxlo (abs_nonneg _)).trans hcx
    · exact Or.inr (Or.inr (Or.inr ⟨hb,hc⟩))


                                                                               
                                                                           
                                                                     
                                                          
theorem positive_difference_physical_family_fiber_count
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (S : Finset ((ℝ × ℤ) × Fin 2)) (F : ℝ → ℝ)
        (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ) (N : ℕ) (Z : ℝ → ℤ)
        (η ya xa Δ J q t T M : ℝ),
      0 < η → η ≤ 1/8 → ya∈Icc (1:ℝ) 2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J → t∈Icc (1/2:ℝ) 2 →
      xa∈Icc M (2*M) →
      (∀ ip∈S, ip.1.1∈Icc (1:ℝ) 2 ∧ z ip.1.1 ip.1.2∈Icc M (2*M)) →
      (∀ ip∈S, N ≤ Alen ip.1.1 ip.1.2 ∧ Alen ip.1.1 ip.1.2 ≤ 3*N ∧
        round (z ip.1.1 ip.1.2)+(Alen ip.1.1 ip.1.2:ℤ)=
          Z ip.1.1+(N:ℤ)*ip.1.2+2*(N:ℤ)) →
      (∀ ip∈S, ∀ jp∈S, ip.1.1 ≠ jp.1.1 → 1 ≤ J*|ip.1.1-jp.1.1|) →
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let μ := fun y w => iteratedDeriv 3 (f y) (round w)/6
      (∀ ip∈S, h ip.1.1 (z ip.1.1 ip.1.2)=q) →
      (∀ ip∈S, |μ ip.1.1 (z ip.1.1 ip.1.2)/μ ya xa*t^3-1| ≤ Δ) →
      let B := max 1 (max (3*U/σ) (2*σ/c))
      (S.card:ℝ) ≤ 6*K*(1+8*C*B*(Δ+5/M)*J) := by
  obtain ⟨K,C,hK,hC,hcount⟩ := positive_difference_physical_parameter_count hσ hc hU
  refine ⟨K,C,hK,hC,?_⟩
  intro S F z Alen N Z η ya xa Δ J q t T M hη hηmax hya hf hbound htests hnegative
    hT hM hN hΔ hJ ht hxa hpoints hgeometry hsep f h μ hlevel hthird B
  classical
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hMp : 0 < M := by linarith only [hM]
  let Y := S.image (fun ip => ip.1.1)
  have hex y (hy : y∈Y) : ∃ ip, ip∈S ∧ ip.1.1=y := Finset.mem_image.mp hy
  let pick := fun y => if hy : y∈Y then Classical.choose (hex y hy) else ((y,0),0)
  have hpick y (hy : y∈Y) : pick y∈S ∧ (pick y).1.1=y := by
    dsimp only [pick]
    rw [dite_eq_left hy]
    exact Classical.choose_spec (hex y hy)
  let root := fun y => z y (pick y).1.2
  have hparams y (hy : y∈Y) : y∈Icc (1:ℝ) 2 ∧ root y∈Icc M (2*M) := by
    have hh := hpoints _ (hpick y hy).1
    rw [(hpick y hy).2] at hh
    exact hh
  have hY := hcount F η ya xa Δ J q t T M Y root hη hηmax hya hf hbound htests
    hT hM hΔ hJ ht hxa hparams
    (by
      intro y hy y' hy' hne
      have hh := hsep _ (hpick y hy).1 _ (hpick y' hy').1
      rw [(hpick y hy).2,(hpick y' hy').2] at hh
      exact hh hne)
    (by
      intro y hy
      have hh := hlevel _ (hpick y hy).1
      rw [(hpick y hy).2] at hh
      exact hh)
    (by
      intro y hy
      have hh := hthird _ (hpick y hy).1
      rw [(hpick y hy).2] at hh
      exact hh)
  have hcard : S.card ≤ 6*Y.card := by
    apply Finset.card_le_mul_card_image S 6
    intro y hy
    let E := S.filter (fun ip => ip.1.1=y)
    let m : ℝ := round (root y)
    obtain ⟨I,hI,_hIlow,hIhigh⟩ := physical_grid_interval_card (Z:=(Z y:ℝ))
      (x:=m-(N:ℝ)) (z:=m+(N:ℝ)) hNp (by linarith only [hNp])
    have hIcard : I.card ≤ 3 := by
      have hh : (I.card:ℝ) ≤ 3 := hIhigh.trans_eq (by field_simp; ring)
      exact_mod_cast hh
    have hmono := positive_difference_physical_curvature_strictMono F hσ hc hη hηmax
      (hparams y hy).1 hf hnegative hT hMp
    have hsubset : Icc M (2*M) ⊆ Icc (3*M/4) (9*M/4) := by
      intro w hw
      constructor <;> linarith only [hw.1,hw.2,hMp]
    have hsame ip (hip : ip∈E) : z ip.1.1 ip.1.2=root y := by
      have hd := Finset.mem_filter.mp hip
      have hz := (hpoints ip hd.1).2
      have he := hlevel ip hd.1
      have hp := hlevel _ (hpick y hy).1
      rw [hd.2] at hz he ⊢
      rw [(hpick y hy).2] at hp
      exact hmono.injOn (hsubset hz) (hsubset (hparams y hy).2) (he.trans hp.symm)
    have hfiber : E.card ≤ (I ×ˢ (Finset.univ : Finset (Fin 2))).card := by
      apply Finset.card_le_card_of_injOn (fun ip => (ip.1.2,ip.2))
      · intro ip hip
        refine Finset.mem_product.mpr ⟨?_,Finset.mem_univ _⟩
        apply (hI ip.1.2).mpr
        have hd := Finset.mem_filter.mp hip
        have hg := hgeometry ip hd.1
        have hlo : (N:ℝ) ≤ Alen ip.1.1 ip.1.2 := by exact_mod_cast hg.1
        have hhi : (Alen ip.1.1 ip.1.2:ℝ) ≤ 3*(N:ℝ) := by exact_mod_cast hg.2.1
        have he : (round (z ip.1.1 ip.1.2):ℝ)+(Alen ip.1.1 ip.1.2:ℝ)=
            (Z ip.1.1:ℝ)+(N:ℝ)*ip.1.2+2*(N:ℝ) := by exact_mod_cast hg.2.2
        rw [hsame ip hip,hd.2] at he
        change m+(Alen y ip.1.2:ℝ)=(Z y:ℝ)+(N:ℝ)*ip.1.2+2*(N:ℝ) at he
        rw [hd.2] at hlo hhi
        constructor <;> nlinarith only [he,hlo,hhi]
      · intro ip hip jp hjp he
        have hi := (Finset.mem_filter.mp hip).2
        have hj := (Finset.mem_filter.mp hjp).2
        have he1 : ip.1.2=jp.1.2 := congrArg (fun p : ℤ × Fin 2 => p.1) he
        have he2 : ip.2=jp.2 := congrArg (fun p : ℤ × Fin 2 => p.2) he
        exact Prod.ext (Prod.ext (hi.trans hj.symm) he1) he2
    have he : (I ×ˢ (Finset.univ : Finset (Fin 2))).card=I.card*2 := by
      simp only [Finset.card_product,Finset.card_univ,Fintype.card_fin]
    rw [he] at hfiber
    change E.card ≤ 6
    omega
  have hcardR : (S.card:ℝ) ≤ 6*(Y.card:ℝ) := by exact_mod_cast hcard
  have hh := hcardR.trans (mul_le_mul_of_nonneg_left hY (by norm_num : (0:ℝ) ≤ 6))
  convert hh using 1
  ring


                                                                       
                                                                          
                                                                         
                                     
theorem positive_difference_family_pair_card_le_matrix_points
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
        (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
        (F : ℝ → ℝ) (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ)
        (N : ℕ) (Z : ℝ → ℤ) (η Δ J T M : ℝ),
      0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J →
      (∀ ij∈P,
        (ij.1.1.1∈Icc (1:ℝ) 2 ∧ z ij.1.1.1 ij.1.1.2∈Icc M (2*M)) ∧
        (ij.2.1.1∈Icc (1:ℝ) 2 ∧ z ij.2.1.1 ij.2.1.2∈Icc M (2*M))) →
      (∀ ij∈P, N ≤ Alen ij.2.1.1 ij.2.1.2 ∧ Alen ij.2.1.1 ij.2.1.2 ≤ 3*N ∧
        round (z ij.2.1.1 ij.2.1.2)+(Alen ij.2.1.1 ij.2.1.2:ℤ)=
          Z ij.2.1.1+(N:ℤ)*ij.2.1.2+2*(N:ℤ)) →
      (∀ ij∈P, ∀ kl∈P, ij.2.1.1 ≠ kl.2.1.1 → 1 ≤ J*|ij.2.1.1-kl.2.1.1|) →
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let μ := fun y w => iteratedDeriv 3 (f y) (round w)/6
      let t := fun ij => (Mat ij 2:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 3
      (∀ ij∈P, t ij∈Icc (1/2:ℝ) 2) →
      (∀ ij∈P, ((Mat ij 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 1)/t ij=
        h ij.2.1.1 (z ij.2.1.1 ij.2.1.2)) →
      (∀ ij∈P, |μ ij.2.1.1 (z ij.2.1.1 ij.2.1.2)/
        μ ij.1.1.1 (z ij.1.1.1 ij.1.1.2)*(t ij)^3-1| ≤ Δ) →
      let B := max 1 (max (3*U/σ) (2*σ/c))
      (P.card:ℝ) ≤ 6*K*(1+8*C*B*(Δ+5/M)*J)*
        ((P.image (fun ij => (Mat ij,ij.1))).card:ℝ) := by
  obtain ⟨K,C,hK,hC,hcount⟩ := positive_difference_physical_family_fiber_count hσ hc hU
  refine ⟨K,C,hK,hC,?_⟩
  intro P Mat F z Alen N Z η Δ J T M hη hηmax hf hbound htests hnegative
    hT hM hN hΔ hJ hpoints hgeometry hsep f h μ t ht hmap hthird B
  classical
  let key := fun ij => (Mat ij,ij.1)
  let I := P.image key
  let Vbound := 6*K*(1+8*C*B*(Δ+5/M)*J)
  have hfiber k (hk : k∈I) :
      ((P.filter (fun ij => key ij=k)).card:ℝ) ≤ Vbound := by
    obtain ⟨ij₀,hij₀,he₀⟩ := Finset.mem_image.mp hk
    let E := P.filter (fun ij => key ij=k)
    let S := E.image Prod.snd
    have hmem ij (hij : ij∈E) : ij∈P ∧ Mat ij=Mat ij₀ ∧ ij.1=ij₀.1 := by
      have hh := Finset.mem_filter.mp hij
      exact ⟨hh.1,(congrArg Prod.fst hh.2).trans (congrArg Prod.fst he₀).symm,
        (congrArg Prod.snd hh.2).trans (congrArg Prod.snd he₀).symm⟩
    have htE ij (hij : ij∈E) : t ij=t ij₀ := by
      dsimp only [t]
      rw [(hmem ij hij).2.1,(hmem ij hij).2.2]
    have hcS := hcount S F z Alen N Z η ij₀.1.1.1 (z ij₀.1.1.1 ij₀.1.1.2)
      Δ J (((Mat ij₀ 0:ℝ)*h ij₀.1.1.1 (z ij₀.1.1.1 ij₀.1.1.2)+Mat ij₀ 1)/t ij₀)
      (t ij₀) T M hη hηmax (hpoints ij₀ hij₀).1.1 hf hbound htests hnegative
      hT hM hN hΔ hJ (ht ij₀ hij₀) (hpoints ij₀ hij₀).1.2
      (by
        intro ip hip
        obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hip
        exact (hpoints ij (hmem ij hij).1).2)
      (by
        intro ip hip
        obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hip
        exact hgeometry ij (hmem ij hij).1)
      (by
        intro ip hip jp hjp hne
        obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hip
        obtain ⟨kl,hkl,rfl⟩ := Finset.mem_image.mp hjp
        exact hsep ij (hmem ij hij).1 kl (hmem kl hkl).1 hne)
      (by
        intro ip hip
        obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hip
        have hh := (hmap ij (hmem ij hij).1).symm
        rw [htE ij hij,(hmem ij hij).2.1,(hmem ij hij).2.2] at hh
        exact hh)
      (by
        intro ip hip
        obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hip
        have hh := hthird ij (hmem ij hij).1
        rw [htE ij hij,(hmem ij hij).2.2] at hh
        exact hh)
    have he : S.card=E.card := Finset.card_image_of_injOn (by
      intro ij hij kl hkl he
      exact Prod.ext ((hmem ij hij).2.2.trans (hmem kl hkl).2.2.symm) he)
    rw [he] at hcS
    exact hcS
  have he : (P.card:ℝ)=∑ k∈I,((P.filter (fun ij => key ij=k)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image key P
  rw [he]
  calc
    _ ≤ ∑ k∈I,Vbound := Finset.sum_le_sum hfiber
    _ = Vbound*(I.card:ℝ) := by rw [Finset.sum_const,nsmul_eq_mul,mul_comm]
    _ = _ := rfl


                                                                    
                                                                    
                                                                      
theorem positive_difference_family_identity_pair_count
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
        (F : ℝ → ℝ) (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ)
        (N : ℕ) (Z : ℝ → ℤ) (η Δ J T M : ℝ),
      0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J →
      (∀ ij∈P,
        (ij.1.1.1∈Icc (1:ℝ) 2 ∧ z ij.1.1.1 ij.1.1.2∈Icc M (2*M)) ∧
        (ij.2.1.1∈Icc (1:ℝ) 2 ∧ z ij.2.1.1 ij.2.1.2∈Icc M (2*M))) →
      (∀ ij∈P, N ≤ Alen ij.2.1.1 ij.2.1.2 ∧ Alen ij.2.1.1 ij.2.1.2 ≤ 3*N ∧
        round (z ij.2.1.1 ij.2.1.2)+(Alen ij.2.1.1 ij.2.1.2:ℤ)=
          Z ij.2.1.1+(N:ℤ)*ij.2.1.2+2*(N:ℤ)) →
      (∀ ij∈P, ∀ kl∈P, ij.2.1.1 ≠ kl.2.1.1 → 1 ≤ J*|ij.2.1.1-kl.2.1.1|) →
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let μ := fun y w => iteratedDeriv 3 (f y) (round w)/6
      (∀ ij∈P, h ij.2.1.1 (z ij.2.1.1 ij.2.1.2)=h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)) →
      (∀ ij∈P, |μ ij.2.1.1 (z ij.2.1.1 ij.2.1.2)/
        μ ij.1.1.1 (z ij.1.1.1 ij.1.1.2)-1| ≤ Δ) →
      let B := max 1 (max (3*U/σ) (2*σ/c))
      (P.card:ℝ) ≤ 6*K*(1+8*C*B*(Δ+5/M)*J)*
        ((P.image Prod.fst).card:ℝ) := by
  obtain ⟨K,C,hK,hC,hcount⟩ := positive_difference_family_pair_card_le_matrix_points hσ hc hU
  refine ⟨K,C,hK,hC,?_⟩
  intro P F z Alen N Z η Δ J T M hη hηmax hf hbound htests hnegative
    hT hM hN hΔ hJ hpoints hgeometry hsep f h μ hmap hthird B
  classical
  let Id : Fin 4 → ℤ := ![1,0,0,1]
  have hI0 : (Id 0:ℝ)=1 := by norm_num [Id]
  have hI1 : (Id 1:ℝ)=0 := by norm_num [Id]
  have hI2 : (Id 2:ℝ)=0 := by
    have hh : Id 2=0 := by decide
    exact_mod_cast hh
  have hI3 : (Id 3:ℝ)=1 := by
    have hh : Id 3=1 := by decide
    exact_mod_cast hh
  have hh := hcount P (fun _ => Id) F z Alen N Z η Δ J T M hη hηmax hf hbound htests hnegative
    hT hM hN hΔ hJ hpoints hgeometry hsep
    (by
      intro ij _
      change ((Id 2:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Id 3)∈Icc (1/2:ℝ) 2
      rw [hI2,hI3]
      norm_num)
    (by
      intro ij hij
      change ((Id 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Id 1)/
        ((Id 2:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Id 3)=h ij.2.1.1 (z ij.2.1.1 ij.2.1.2)
      simpa only [hI0,hI1,hI2,hI3,one_mul,add_zero,zero_mul,zero_add,div_one] using (hmap ij hij).symm)
    (by
      intro ij hij
      change |μ ij.2.1.1 (z ij.2.1.1 ij.2.1.2)/μ ij.1.1.1 (z ij.1.1.1 ij.1.1.2)*
        ((Id 2:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Id 3)^3-1| ≤ Δ
      simpa only [hI2,hI3,zero_mul,zero_add,one_pow,mul_one] using hthird ij hij)
  have he : P.image (fun ij => (Id,ij.1))=(P.image Prod.fst).image (fun ip => (Id,ip)) := by
    rw [Finset.image_image]
    rfl
  have hinj : Function.Injective (fun ip : (ℝ × ℤ) × Fin 2 => (Id,ip)) := by
    intro ip jp he
    exact congrArg Prod.snd he
  rw [he,Finset.card_image_of_injective _ hinj] at hh
  exact hh


                                                                       
                                                                      
                                                                    
                                                          
theorem positive_difference_family_bounded_action_pair_count
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
        (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
        (F : ℝ → ℝ) (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ)
        (N : ℕ) (Z : ℝ → ℤ) (η Δ J T M L : ℝ),
      0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J → 0 ≤ L →
      (∀ ij∈P,
        (ij.1.1.1∈Icc (1:ℝ) 2 ∧ z ij.1.1.1 ij.1.1.2∈Icc M (2*M)) ∧
        (ij.2.1.1∈Icc (1:ℝ) 2 ∧ z ij.2.1.1 ij.2.1.2∈Icc M (2*M))) →
      (∀ ij∈P, N ≤ Alen ij.2.1.1 ij.2.1.2 ∧ Alen ij.2.1.1 ij.2.1.2 ≤ 3*N ∧
        round (z ij.2.1.1 ij.2.1.2)+(Alen ij.2.1.1 ij.2.1.2:ℤ)=
          Z ij.2.1.1+(N:ℤ)*ij.2.1.2+2*(N:ℤ)) →
      (∀ ij∈P, ∀ kl∈P, ij.2.1.1 ≠ kl.2.1.1 → 1 ≤ J*|ij.2.1.1-kl.2.1.1|) →
      (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
      (∀ ij∈P, Mat ij 1 ≠ 0 ∧ Mat ij 2 ≠ 0) →
      (∀ ij∈P, |(Mat ij 2:ℝ)| * ((3*U/σ)*T/(2*M^2)) ≤ L) →
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let μ := fun y w => iteratedDeriv 3 (f y) (round w)/6
      let t := fun ij => (Mat ij 2:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 3
      (∀ ij∈P, ((Mat ij 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 1)/t ij=
        h ij.2.1.1 (z ij.2.1.1 ij.2.1.2)) →
      (∀ ij∈P, |t ij-1| ≤ 1/(8*(L+3))) →
      (∀ ij∈P, |((Mat ij 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 1)/
        h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)-1| ≤ 1/(8*(L+3))) →
      (∀ ij∈P, |μ ij.2.1.1 (z ij.2.1.1 ij.2.1.2)/
        μ ij.1.1.1 (z ij.1.1.1 ij.1.1.2)*(t ij)^3-1| ≤ Δ) →
      let B := max 1 (max (3*U/σ) (2*σ/c))
      (P.card:ℝ) ≤ 6*K*(1+8*C*B*(Δ+5/M)*J)*
        ((2*(L+3)^2+1)*(2*L+5)^2*(L+3)^2)*
        ((P.image Prod.fst).card:ℝ) := by
  obtain ⟨K,C,hK,hC,hcount⟩ := positive_difference_family_pair_card_le_matrix_points hσ hc hU
  refine ⟨K,C,hK,hC,?_⟩
  intro P Mat F z Alen N Z η Δ J T M L hη hηmax hf hbound htests hnegative
    hT hM hN hΔ hJ hL hpoints hgeometry hsep hdet hnontri haction f h μ t hmap hden hnum hthird B
  classical
  have hMp : 0 < M := by linarith only [hM]
  let Hcurv := (3*U/σ)*T/(2*M^2)
  let Smat := P.image Mat
  have hex A (hA : A∈Smat) : ∃ ij, ij∈P ∧ Mat ij=A := Finset.mem_image.mp hA
  let pick := fun A => if hA : A∈Smat then Classical.choose (hex A hA) else (((0,0),0),((0,0),0))
  have hpick A (hA : A∈Smat) : pick A∈P ∧ Mat (pick A)=A := by
    dsimp only [pick]
    rw [dite_eq_left hA]
    exact Classical.choose_spec (hex A hA)
  let x := fun A => h (pick A).1.1.1 (z (pick A).1.1.1 (pick A).1.1.2)
  let y := fun A => h (pick A).2.1.1 (z (pick A).2.1.1 (pick A).2.1.2)
  have hcurv u w (hu : u∈Icc (1:ℝ) 2) (hw : w∈Icc M (2*M)) :
      h u w ≠ 0 ∧ |h u w| ≤ Hcurv := by
    have hh := positive_difference_half_curvature_source_bounds F hσ hc hU hη hηmax
      hT hMp hu hw hf hbound htests
    exact ⟨abs_pos.mp ((by positivity : (0:ℝ) < c*T/(4*σ*M^2)).trans_le hh.1),hh.2⟩
  have hmat := bounded_action_narrow_nontriangular_matrix_count (H:=Hcurv) Smat x y hL
    (by intro A hA; have hh := hdet _ (hpick A hA).1; rw [(hpick A hA).2] at hh; exact hh)
    (by intro A hA; have hh := hnontri _ (hpick A hA).1; rw [(hpick A hA).2] at hh; exact hh)
    (by
      intro A hA
      have hp := hpoints _ (hpick A hA).1
      have ha := hcurv _ _ hp.1.1 hp.1.2
      have hb := hcurv _ _ hp.2.1 hp.2.2
      exact ⟨ha.1,ha.2,hb.2⟩)
    (by intro A hA; have hh := haction _ (hpick A hA).1; rw [(hpick A hA).2] at hh; exact hh)
    (by
      intro A hA
      have hh := hmap _ (hpick A hA).1
      dsimp only [t] at hh
      rw [(hpick A hA).2] at hh
      exact hh)
    (by
      intro A hA
      have hh := hden _ (hpick A hA).1
      dsimp only [t] at hh
      rw [(hpick A hA).2] at hh
      exact hh)
    (by
      intro A hA
      have hh := hnum _ (hpick A hA).1
      rw [(hpick A hA).2] at hh
      exact hh)
  have ht ij (hij : ij∈P) : t ij∈Icc (1/2:ℝ) 2 := by
    have hε : 1/(8*(L+3)) ≤ (1:ℝ)/24 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith only [hL])
    have hh := abs_le.mp ((hden ij hij).trans hε)
    constructor <;> linarith only [hh.1,hh.2]
  have hpair := hcount P Mat F z Alen N Z η Δ J T M hη hηmax hf hbound htests hnegative
    hT hM hN hΔ hJ hpoints hgeometry hsep ht hmap hthird
  have hsub : P.image (fun ij => (Mat ij,ij.1)) ⊆ Smat ×ˢ P.image Prod.fst := by
    intro a ha
    obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem Mat hij,Finset.mem_image_of_mem Prod.fst hij⟩
  have hcard : ((P.image (fun ij => (Mat ij,ij.1))).card:ℝ) ≤
      (Smat.card:ℝ)*((P.image Prod.fst).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_product Smat (P.image Prod.fst))
  have hlast := hcard.trans (mul_le_mul_of_nonneg_right hmat
    (by positivity : (0:ℝ) ≤ (P.image Prod.fst).card))
  have hh := hpair.trans (mul_le_mul_of_nonneg_left hlast
    (by dsimp only [B]; positivity : (0:ℝ) ≤ 6*K*(1+8*C*B*(Δ+5/M)*J)))
  convert hh using 1
  ring


                                                                       
                                                                        
theorem rounded_offset_family_point_count
    (S : Finset ((ℝ × ℤ) × Fin 2)) (z : ℝ → ℤ → ℝ)
    (Alen : ℝ → ℤ → ℕ) (N : ℕ) (Z : ℝ → ℤ) {M : ℝ}
    (hM : 0 ≤ M) (hN : 0 < N)
    (hpoints : ∀ ip∈S, z ip.1.1 ip.1.2∈Icc M (2*M))
    (hgeometry : ∀ ip∈S, N ≤ Alen ip.1.1 ip.1.2 ∧ Alen ip.1.1 ip.1.2 ≤ 3*N ∧
      round (z ip.1.1 ip.1.2)+(Alen ip.1.1 ip.1.2:ℤ)=
        Z ip.1.1+(N:ℤ)*ip.1.2+2*(N:ℤ)) :
    (S.card:ℝ) ≤ 2*(4+M/(N:ℝ))*((S.image (fun ip => ip.1.1)).card:ℝ) := by
  classical
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  let Y := S.image (fun ip => ip.1.1)
  have hfiber y (hy : y∈Y) :
      ((S.filter (fun ip => ip.1.1=y)).card:ℝ) ≤ 2*(4+M/(N:ℝ)) := by
    let E := S.filter (fun ip => ip.1.1=y)
    obtain ⟨I,hI,_hIlow,hIhigh⟩ := physical_grid_interval_card (Z:=(Z y:ℝ))
      (x:=M-(N:ℝ)-1/2) (z:=2*M+(N:ℝ)+1/2) hNp (by linarith only [hM,hNp])
    have hIcard : (I.card:ℝ) ≤ 4+M/(N:ℝ) := by
      apply hIhigh.trans
      apply (le_of_sub_nonneg ?_)
      have he : 4+M/(N:ℝ)-((2*M+(N:ℝ)+1/2-(M-(N:ℝ)-1/2))/(N:ℝ)+1)=
          ((N:ℝ)-1)/(N:ℝ) := by field_simp; ring
      rw [he]
      exact div_nonneg (by linarith only [hN1]) hNp.le
    have hc : E.card ≤ (I ×ˢ (Finset.univ : Finset (Fin 2))).card := by
      apply Finset.card_le_card_of_injOn (fun ip => (ip.1.2,ip.2))
      · intro ip hip
        have hd := Finset.mem_filter.mp hip
        refine Finset.mem_product.mpr ⟨?_,Finset.mem_univ _⟩
        apply (hI ip.1.2).mpr
        have hz := hpoints ip hd.1
        have hr := abs_le.mp (abs_sub_round (z ip.1.1 ip.1.2))
        have hg := hgeometry ip hd.1
        have hlo : (N:ℝ) ≤ Alen ip.1.1 ip.1.2 := by exact_mod_cast hg.1
        have hhi : (Alen ip.1.1 ip.1.2:ℝ) ≤ 3*(N:ℝ) := by exact_mod_cast hg.2.1
        have he : (round (z ip.1.1 ip.1.2):ℝ)+(Alen ip.1.1 ip.1.2:ℝ)=
            (Z ip.1.1:ℝ)+(N:ℝ)*ip.1.2+2*(N:ℝ) := by exact_mod_cast hg.2.2
        rw [←hd.2]
        constructor <;> nlinarith only [he,hlo,hhi,hz.1,hz.2,hr.1,hr.2]
      · intro ip hip jp hjp he
        have hi := (Finset.mem_filter.mp hip).2
        have hj := (Finset.mem_filter.mp hjp).2
        have he1 : ip.1.2=jp.1.2 := congrArg (fun p : ℤ × Fin 2 => p.1) he
        have he2 : ip.2=jp.2 := congrArg (fun p : ℤ × Fin 2 => p.2) he
        exact Prod.ext (Prod.ext (hi.trans hj.symm) he1) he2
    have hcR : (E.card:ℝ) ≤ (I.card:ℝ)*2 := by
      exact_mod_cast hc.trans_eq (by simp only [Finset.card_product,Finset.card_univ,Fintype.card_fin])
    exact hcR.trans (by nlinarith only [hIcard])
  have he : (S.card:ℝ)=∑ y∈Y,((S.filter (fun ip => ip.1.1=y)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image (fun ip => ip.1.1) S
  rw [he]
  calc
    _ ≤ ∑ _y∈Y,2*(4+M/(N:ℝ)) := Finset.sum_le_sum hfiber
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul,mul_comm]

                                                                     
                                                                        
                                                                     
                                                          
theorem positive_difference_family_identity_source_scale
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
        (F : ℝ → ℝ) (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ)
        (N : ℕ) (Z : ℝ → ℤ) (η Δ J T M : ℝ),
      0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J → (N:ℝ) ≤ M → J ≤ M →
      (∀ ij∈P,
        (ij.1.1.1∈Icc (1:ℝ) 2 ∧ z ij.1.1.1 ij.1.1.2∈Icc M (2*M)) ∧
        (ij.2.1.1∈Icc (1:ℝ) 2 ∧ z ij.2.1.1 ij.2.1.2∈Icc M (2*M))) →
      (∀ ij∈P, N ≤ Alen ij.1.1.1 ij.1.1.2 ∧ Alen ij.1.1.1 ij.1.1.2 ≤ 3*N ∧
        round (z ij.1.1.1 ij.1.1.2)+(Alen ij.1.1.1 ij.1.1.2:ℤ)=
          Z ij.1.1.1+(N:ℤ)*ij.1.1.2+2*(N:ℤ)) →
      (∀ ij∈P, N ≤ Alen ij.2.1.1 ij.2.1.2 ∧ Alen ij.2.1.1 ij.2.1.2 ≤ 3*N ∧
        round (z ij.2.1.1 ij.2.1.2)+(Alen ij.2.1.1 ij.2.1.2:ℤ)=
          Z ij.2.1.1+(N:ℤ)*ij.2.1.2+2*(N:ℤ)) →
      (∀ ij∈P, ∀ kl∈P, ij.2.1.1 ≠ kl.2.1.1 → 1 ≤ J*|ij.2.1.1-kl.2.1.1|) →
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let μ := fun y w => iteratedDeriv 3 (f y) (round w)/6
      (∀ ij∈P, h ij.2.1.1 (z ij.2.1.1 ij.2.1.2)=h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)) →
      (∀ ij∈P, |μ ij.2.1.1 (z ij.2.1.1 ij.2.1.2)/
        μ ij.1.1.1 (z ij.1.1.1 ij.1.1.2)-1| ≤ Δ) →
      (P.card:ℝ) ≤ D*((P.image (fun ij => ij.1.1.1)).card:ℝ)*
        (M/(N:ℝ))*(1+Δ*J) := by
  obtain ⟨K,C,hK,hC,hcount⟩ := positive_difference_family_identity_pair_count hσ hc hU
  let B := max 1 (max (3*U/σ) (2*σ/c))
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨60*K*(1+40*C*B),by positivity,?_⟩
  intro P F z Alen N Z η Δ J T M hη hηmax hf hbound htests hnegative
    hT hM hN hΔ hJ hNM hJM hpoints hgeometryA hgeometryB hsep f h μ hmap hthird
  classical
  have hMp : 0 < M := by linarith only [hM]
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hh := hcount P F z Alen N Z η Δ J T M hη hηmax hf hbound htests hnegative
    hT hM hN hΔ hJ hpoints hgeometryB hsep hmap hthird
  have hfirst := rounded_offset_family_point_count (P.image Prod.fst) z Alen N Z hMp.le hN
    (by
      intro ip hip
      obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hip
      exact (hpoints ij hij).1.2)
    (by
      intro ip hip
      obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hip
      exact hgeometryA ij hij)
  rw [Finset.image_image] at hfirst
  let I := ((P.image (fun ij => ij.1.1.1)).card:ℝ)
  have hI : 0 ≤ I := by dsimp only [I]; positivity
  have hscale : 1 ≤ M/(N:ℝ) := (le_div_iff₀ hNp).mpr (by simpa only [one_mul] using hNM)
  have hfirst' : ((P.image Prod.fst).card:ℝ) ≤ 10*(M/(N:ℝ))*I := by
    apply hfirst.trans
    apply mul_le_mul_of_nonneg_right _ hI
    linarith only [hscale]
  have hJM' : J/M ≤ 1 := (div_le_iff₀ hMp).mpr (by simpa only [one_mul] using hJM)
  have hfactor : 1+8*C*B*(Δ+5/M)*J ≤ (1+40*C*B)*(1+Δ*J) := by
    calc
      _ = 1+8*C*B*(Δ*J+5*(J/M)) := by ring
      _ ≤ 1+8*C*B*(Δ*J+5) := by
        gcongr
        nlinarith only [hJM']
      _ ≤ _ := by
        have hp : 0 ≤ (32*C*B+1)*(Δ*J) := by positivity
        nlinarith only [hp]
  calc
    (P.card:ℝ) ≤ 6*K*(1+8*C*B*(Δ+5/M)*J)*((P.image Prod.fst).card:ℝ) := hh
    _ ≤ 6*K*((1+40*C*B)*(1+Δ*J))*(10*(M/(N:ℝ))*I) := by
      gcongr
    _ = _ := by ring


                                                                      
                                                                      
                                                                       
theorem separated_reference_interval_card
    (S : Finset ℝ) {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hsep : ∀ x∈S, ∀ y∈S, x≠y → d ≤ |x-y|)
    (hmem : ∀ x∈S, a ≤ x ∧ x ≤ b) :
    (S.card:ℝ) ≤ (b-a)/d+1 := by
  classical
  let V := S.image (fun x => x/d)
  have hinj : Function.Injective (fun x : ℝ => x/d) := by
    intro x y he
    exact (div_left_inj' hd.ne').mp he
  have hs : ∀ x∈V, ∀ y∈V, x≠y → 1 ≤ |x-y| := by
    intro x hx y hy hne
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
    have huv : u≠v := fun he => hne (congrArg (fun z : ℝ => z/d) he)
    rw [←sub_div,abs_div,abs_of_pos hd]
    exact (le_div_iff₀ hd).mpr (by simpa only [one_mul] using hsep u hu v hv huv)
  have hh := TaoTrudgianYang2025.oneSeparated_card_cast_le_interval_length_add_one V hs
    (show 0 ≤ b/d-a/d from sub_nonneg.mpr (div_le_div_of_nonneg_right hab hd.le))
    (by
      intro x hx
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
      exact ⟨div_le_div_of_nonneg_right (hmem u hu).1 hd.le,
        div_le_div_of_nonneg_right (hmem u hu).2 hd.le⟩)
  rw [Finset.card_image_of_injective S hinj] at hh
  convert hh using 1
  ring


                                                                    
                                                                    
                                                                   
                                               
theorem adjacent_reference_gap_card
    (S : Finset ℝ) (G : Finset (ℝ × ℝ)) {lo hi d : ℝ}
    (hd : 0 < d) (hlohi : lo ≤ hi)
    (hsep : ∀ x∈S, ∀ y∈S, x≠y → d ≤ |x-y|)
    (hgap : ∀ ab∈G, ab.1∈S ∧ ab.2∈S ∧ ab.1<ab.2 ∧
      ∀ t∈S, ¬(ab.1<t ∧ t<ab.2))
    (hmeet : ∀ ab∈G, ab.1<hi ∧ lo<ab.2) :
    (G.card:ℝ) ≤ (hi-lo)/d+2 := by
  classical
  have hinj : Set.InjOn Prod.fst (G : Set (ℝ × ℝ)) := by
    intro ab hab cd hcd he
    apply Prod.ext he
    rcases lt_trichotomy ab.2 cd.2 with hlt | heq | hgt
    · exact False.elim ((hgap cd hcd).2.2.2 _ (hgap ab hab).2.1
        ⟨by rw [←he]; exact (hgap ab hab).2.2.1,hlt⟩)
    · exact heq
    · exact False.elim ((hgap ab hab).2.2.2 _ (hgap cd hcd).2.1
        ⟨by rw [he]; exact (hgap cd hcd).2.2.1,hgt⟩)
  let G₀ := G.filter (fun ab => ab.1<lo)
  let G₁ := G.filter (fun ab => ¬ab.1<lo)
  have hsmall : G₀.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro ab hab cd hcd
    have ha := Finset.mem_filter.mp hab
    have hc := Finset.mem_filter.mp hcd
    apply hinj ha.1 hc.1
    rcases lt_trichotomy ab.1 cd.1 with hlt | heq | hgt
    · exact False.elim ((hgap ab ha.1).2.2.2 _ (hgap cd hc.1).1
        ⟨hlt,hc.2.trans (hmeet ab ha.1).2⟩)
    · exact heq
    · exact False.elim ((hgap cd hc.1).2.2.2 _ (hgap ab ha.1).1
        ⟨hgt,ha.2.trans (hmeet cd hc.1).2⟩)
  have hlarge := separated_reference_interval_card (G₁.image Prod.fst) hd hlohi
    (by
      intro x hx y hy hne
      obtain ⟨ab,hab,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hy
      exact hsep _ (hgap ab (Finset.mem_filter.mp hab).1).1
        _ (hgap cd (Finset.mem_filter.mp hcd).1).1 hne)
    (by
      intro x hx
      obtain ⟨ab,hab,rfl⟩ := Finset.mem_image.mp hx
      have ha := Finset.mem_filter.mp hab
      exact ⟨le_of_not_gt ha.2,(hmeet ab ha.1).1.le⟩)
  have he : (G₁.image Prod.fst).card=G₁.card :=
    Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _))
  rw [he] at hlarge
  have hcard : G.card=G₀.card+G₁.card :=
    (Finset.card_filter_add_card_filter_not (s:=G) (fun ab => ab.1<lo)).symm
  have hcardR : (G.card:ℝ)=(G₀.card:ℝ)+(G₁.card:ℝ) := by exact_mod_cast hcard
  have hsmallR : (G₀.card:ℝ) ≤ 1 := by exact_mod_cast hsmall
  linarith only [hcardR,hsmallR,hlarge]


                                                                  
                                                                    
                                                                 
theorem positive_difference_reference_gap_packing
    (F : ℝ → ℝ) (S : Finset ℝ) (G : Finset (ℝ × ℝ))
    {σ c J η y T M N R U : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hU : 0 < U)
    (hphase : T*N*R^2=M^3)
    (hsep : ∀ a∈S, ∀ b∈S, a≠b → U/(4*R^2) ≤ |a-b|)
    (hgap : ∀ ab∈G, ab.1∈S ∧ ab.2∈S ∧ ab.1<ab.2 ∧
      ∀ t∈S, ¬(ab.1<t ∧ t<ab.2)) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    (∀ ab∈G, ab.1<h (2*M) ∧ h M<ab.2) →
    (G.card:ℝ) ≤ (12*J/σ)*M/(N*U)+2 := by
  intro f h hmeet
  let d := U/(4*R^2)
  let Hcurv := (3*J/σ)*T/(2*M^2)
  have hd : 0 < d := by dsimp only [d]; positivity
  have hmono := positive_difference_physical_curvature_strictMono F hσ hc hη hηmax hy
    hf hnegative hT hM
  have hwideM : M∈Icc (3*M/4) (9*M/4) := by constructor <;> linarith only [hM]
  have hwide2M : 2*M∈Icc (3*M/4) (9*M/4) := by constructor <;> linarith only [hM]
  have hlohi : h M ≤ h (2*M) :=
    hmono.monotoneOn hwideM hwide2M (by linarith only [hM])
  have hleft := positive_difference_half_curvature_source_bounds F hσ hc hJ hη hηmax
    hT hM hy (show M∈Icc M (2*M) from ⟨le_rfl,by linarith only [hM]⟩) hf hbound htests
  have hright := positive_difference_half_curvature_source_bounds F hσ hc hJ hη hηmax
    hT hM hy (show 2*M∈Icc M (2*M) from ⟨by linarith only [hM],le_rfl⟩) hf hbound htests
  have hrange : h (2*M)-h M ≤ 2*Hcurv := by
    have hl : -Hcurv ≤ h M := (abs_le.mp hleft.2).1
    have hr : h (2*M) ≤ Hcurv := (abs_le.mp hright.2).2
    linarith only [hl,hr]
  have hscale : 2*Hcurv/d=(12*J/σ)*M/(N*U) := by
    have hTeq : T=M^3/(N*R^2) := (eq_div_iff (by positivity)).mpr (by nlinarith only [hphase])
    dsimp only [Hcurv,d]
    rw [hTeq]
    field_simp
    ring
  have hh := adjacent_reference_gap_card S G hd hlohi hsep hgap hmeet
  calc
    (G.card:ℝ) ≤ (h (2*M)-h M)/d+2 := hh
    _ ≤ 2*Hcurv/d+2 := add_le_add (div_le_div_of_nonneg_right hrange hd.le) (le_refl 2)
    _ = _ := by rw [hscale]


                                                                    
                                                                        
                                                                       
theorem positive_difference_reference_family_packing
    (F : ℝ → ℝ) (Y S : Finset ℝ)
    {σ c J η T M N R U : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : ∀ y∈Y, y∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hU : 0 < U)
    (hphase : T*N*R^2=M^3)
    (hsep : ∀ a∈S, ∀ b∈S, a≠b → U/(4*R^2) ≤ |a-b|) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let V := (Y ×ˢ (S ×ˢ S)).filter (fun yab =>
      yab.2.1<yab.2.2 ∧ (∀ t∈S, ¬(yab.2.1<t ∧ t<yab.2.2)) ∧
        yab.2.1<h yab.1 (2*M) ∧ h yab.1 M<yab.2.2)
    (V.card:ℝ) ≤ ((12*J/σ)*M/(N*U)+2)*(Y.card:ℝ) := by
  classical
  intro f h V
  let G := fun y => (S ×ˢ S).filter (fun ab =>
    ab.1<ab.2 ∧ (∀ t∈S, ¬(ab.1<t ∧ t<ab.2)) ∧
      ab.1<h y (2*M) ∧ h y M<ab.2)
  have hG y (hyY : y∈Y) : ((G y).card:ℝ) ≤ (12*J/σ)*M/(N*U)+2 := by
    apply positive_difference_reference_gap_packing F S (G y) hσ hc hJ hη hηmax
      (hy y hyY) hf hbound htests hnegative hT hM hN hR hU hphase hsep
    · intro ab hab
      have hh := Finset.mem_filter.mp hab
      have he := Finset.mem_product.mp hh.1
      exact ⟨he.1,he.2,hh.2.1,hh.2.2.1⟩
    · intro ab hab
      exact (Finset.mem_filter.mp hab).2.2.2
  have hmaps : Set.MapsTo Prod.fst (V : Set (ℝ × (ℝ × ℝ))) (Y : Set ℝ) := by
    intro yab hyab
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hyab).1).1
  have hfiber y (hyY : y∈Y) : (V.filter (fun yab => yab.1=y)).card=(G y).card := by
    let E := V.filter (fun yab => yab.1=y)
    have he : E.image Prod.snd=G y := by
      ext ab
      constructor
      · intro hab
        obtain ⟨yab,hyab,rfl⟩ := Finset.mem_image.mp hab
        have hh := Finset.mem_filter.mp hyab
        have hv := Finset.mem_filter.mp hh.1
        apply Finset.mem_filter.mpr
        refine ⟨(Finset.mem_product.mp hv.1).2,?_⟩
        rw [hh.2] at hv
        exact hv.2
      · intro hab
        have hh := Finset.mem_filter.mp hab
        apply Finset.mem_image.mpr
        refine ⟨(y,ab),?_,rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hyY,hh.1⟩,hh.2⟩,rfl⟩
    have hi : Set.InjOn Prod.snd (E : Set (ℝ × (ℝ × ℝ))) := by
      intro a ha b hb he
      have hya := (Finset.mem_filter.mp ha).2
      have hyb := (Finset.mem_filter.mp hb).2
      exact Prod.ext (hya.trans hyb.symm) he
    exact (Finset.card_image_of_injOn hi).symm.trans (congrArg Finset.card he)
  have he : (V.card:ℝ)=∑ y∈Y,((G y).card:ℝ) := by
    have hh := Finset.card_eq_sum_card_fiberwise hmaps
    rw [Finset.sum_congr rfl (fun y hyY => hfiber y hyY)] at hh
    exact_mod_cast hh
  rw [he]
  calc
    _ ≤ ∑ _y∈Y,((12*J/σ)*M/(N*U)+2) := Finset.sum_le_sum hG
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul,mul_comm]

                                                                   
                                                                
                                                                   
                                                                     
               
theorem positive_difference_common_model
    {σ : ℝ} (hσ : 0 < σ) (P : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (F : ℝ → ℝ) (δ η y y₀ : ℝ),
      0 ≤ δ → 0 < η → η ≤ 1/8 →
      y∈Icc (1:ℝ) 2 → y₀∈Icc (1:ℝ) 2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ p ≤ P+1,
        |iteratedDeriv (p+1) F w-iteratedDeriv p (Expdb.modelPhase σ) w| ≤ δ) →
      Expdb.IsApproximateModelPhaseFunction
        (fun u => (F u-F (u+η*y))/(σ*η*y₀)) (σ+1) P
        (C*(δ+η+|y-y₀|)) := by
  classical
  choose B hB hLip using fun j : Fin (P+1) =>
    TaoTrudgianYang2025.iteratedDeriv_modelPhase_positive_compact_lipschitz
      (r:=3) (show (0:ℝ)<1/2 by norm_num) (σ+1) j.val
  let V := ∑ j : Fin (P+1), B j
  let J := ∑ j : Fin (P+1),
    TaoTrudgianYang2025.modelPhaseJetCoefficient (σ+1) j.val
  have hV : 0 ≤ V := Finset.sum_nonneg (fun j _ => zero_le_one.trans (hB j))
  have hJ : 0 ≤ J := Finset.sum_nonneg
    (fun j _ => TaoTrudgianYang2025.modelPhaseJetCoefficient_nonneg _ _)
  let C := max 1 (max (2/σ) (max (4*V) J))
  have hCδ : 2/σ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCη : 4*V ≤ C := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hCy : J ≤ C := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨C,le_max_left _ _,?_⟩
  intro F δ η y y₀ hδ hη hηmax hy hy₀ hf hjets
  have hypos : 0 < y := zero_lt_one.trans_le hy.1
  have hy₀pos : 0 < y₀ := zero_lt_one.trans_le hy₀.1
  have hshift : 0 < η*y := mul_pos hη hypos
  have hshmax : η*y ≤ 1/4 := by
    nlinarith only [mul_le_mul hηmax hy.2 hypos.le (by norm_num : (0:ℝ) ≤ 1/8)]
  apply TaoTrudgianYang2025.approximateModelPhase_of_interior_bounds
  · intro u hu
    have hu0 : 0 < u := zero_lt_one.trans_le hu.1
    exact (((hf u hu0).sub
      ((hf _ (add_pos hu0 hshift)).comp u
        (contDiffAt_id.add contDiffAt_const))).div_const (σ*η*y₀)).contDiffWithinAt
  · intro u hu p hp
    let R := iteratedDeriv p (Expdb.modelPhase (σ+1)) u
    let D := iteratedDeriv (p+1) F u-iteratedDeriv (p+1) F (u+η*y)
    let g := fun w => iteratedDeriv (p+1) F w+σ*w*R
    have hu0 : 0 < u := zero_lt_one.trans hu.1
    have hwide w (hw : w∈Icc u (u+η*y)) : w∈Icc (1/2:ℝ) 3 := by
      constructor <;> linarith only [hu.1,hu.2,hw.1,hw.2,hshmax]
    have huwide : u∈Icc (1/2:ℝ) 3 := by
      constructor <;> linarith only [hu.1,hu.2]
    have hBp : B ⟨p,by omega⟩ ≤ V :=
      Finset.single_le_sum (fun j _ => zero_le_one.trans (hB j)) (Finset.mem_univ _)
    have hJp : TaoTrudgianYang2025.modelPhaseJetCoefficient (σ+1) p ≤ J :=
      Finset.single_le_sum
        (fun j _ => TaoTrudgianYang2025.modelPhaseJetCoefficient_nonneg (σ+1) j.val)
        (Finset.mem_univ (⟨p,by omega⟩ : Fin (P+1)))
    have hd w (hw : w∈Icc u (u+η*y)) :
        HasDerivAt g (iteratedDeriv (p+2) F w+σ*R) w := by
      have hw0 : 0 < w := hu0.trans_le hw.1
      have hh := (contDiffAt_iteratedDeriv_infty (hf w hw0) (p+1)).differentiableAt
        (by simp : (∞ : WithTop ℕ∞) ≠ 0)
      have hj : HasDerivAt (iteratedDeriv (p+1) F) (iteratedDeriv (p+2) F w) w := by
        simpa only [iteratedDeriv_succ] using hh.hasDerivAt
      convert hj.add (((hasDerivAt_id w).const_mul σ).mul_const R) using 1
      · rfl
      · ring
    have hb w (hw : w∈Icc u (u+η*y)) :
        ‖deriv g w‖ ≤ δ+σ*V*(η*y) := by
      rw [(hd w hw).deriv,Real.norm_eq_abs]
      have he := hjets w (hwide w hw) (p+1) (by omega)
      have hl := hLip ⟨p,by omega⟩ u huwide w (hwide w hw)
      have hdist : |u-w| ≤ η*y := by
        rw [abs_of_nonpos (sub_nonpos.mpr hw.1)]
        linarith only [hw.2]
      have hl' : |R-iteratedDeriv p (Expdb.modelPhase (σ+1)) w| ≤ V*(η*y) :=
        hl.trans (mul_le_mul hBp hdist (abs_nonneg _) hV)
      calc
        _ = |(iteratedDeriv (p+2) F w-iteratedDeriv (p+1) (Expdb.modelPhase σ) w)+
            σ*(R-iteratedDeriv p (Expdb.modelPhase (σ+1)) w)| := by
          rw [TaoTrudgianYang2025.modelPhase_iteratedDeriv_succ_parameter σ
            (hu0.trans_le hw.1) p]
          congr 1
          ring
        _ ≤ |iteratedDeriv (p+2) F w-iteratedDeriv (p+1) (Expdb.modelPhase σ) w|+
            |σ*(R-iteratedDeriv p (Expdb.modelPhase (σ+1)) w)| := abs_add_le _ _
        _ ≤ δ+σ*(V*(η*y)) := by
          rw [abs_mul,abs_of_pos hσ]
          exact add_le_add he (mul_le_mul_of_nonneg_left hl' hσ.le)
        _ = _ := by ring
    have hm := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun w hw => (hd w hw).differentiableAt) hb (convex_Icc u (u+η*y))
      (show u+η*y∈Icc u (u+η*y) from ⟨by linarith only [hshift],le_rfl⟩)
      (show u∈Icc u (u+η*y) from ⟨le_rfl,by linarith only [hshift]⟩)
    have herror : |D-σ*(η*y)*R| ≤ (δ+σ*V*(η*y))*(η*y) := by
      rw [Real.norm_eq_abs,Real.norm_eq_abs,
        show u-(u+η*y)= -(η*y) by ring,abs_neg,abs_of_pos hshift] at hm
      convert hm using 1
      dsimp only [D,g]
      congr 1
      ring
    have hden : 0 < σ*η*y₀ := by positivity
    have hquot : |D/(σ*η*y₀)-(y/y₀)*R| ≤ (δ/σ+V*(η*y))*(y/y₀) := by
      have hh := div_le_div_of_nonneg_right herror hden.le
      rw [show D/(σ*η*y₀)-(y/y₀)*R=(D-σ*(η*y)*R)/(σ*η*y₀) by field_simp,
        abs_div,abs_of_pos hden]
      convert hh using 1
      field_simp
    have hratio : y/y₀ ≤ 2 := (div_le_iff₀ hy₀pos).mpr (by linarith only [hy.2,hy₀.1])
    have hquot' : |D/(σ*η*y₀)-(y/y₀)*R| ≤ 2*δ/σ+4*V*η := by
      apply hquot.trans
      calc
        _ ≤ (δ/σ+V*(η*2))*2 := by gcongr; exact hy.2
        _ = _ := by ring
    have hR : |R| ≤ J := (TaoTrudgianYang2025.iteratedDeriv_modelPhase_abs_le
      (show 0 ≤ σ+1 by linarith only [hσ]) hu p).trans hJp
    have hamp : |(y/y₀)*R-R| ≤ J*|y-y₀| := by
      rw [show (y/y₀)*R-R=((y-y₀)/y₀)*R by field_simp,
        abs_mul,abs_div,abs_of_pos hy₀pos]
      calc
        _ ≤ |y-y₀| * J := mul_le_mul
          (div_le_self (abs_nonneg _) hy₀.1) hR (abs_nonneg _) (abs_nonneg _)
        _ = _ := by ring
    have hreg : ContDiffAt ℝ (p+1) F u :=
      (hf u hu0).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl (p+1))
    have hregShift : ContDiffAt ℝ (p+1) (fun w => F (w+η*y)) u :=
      ((hf _ (add_pos hu0 hshift)).comp u (contDiffAt_id.add contDiffAt_const)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl (p+1))
    rw [iteratedDeriv_div_const,iteratedDeriv_fun_sub hreg hregShift,
      iteratedDeriv_comp_add_const]
    change |D/(σ*η*y₀)-R| ≤ _
    calc
      _ ≤ |D/(σ*η*y₀)-(y/y₀)*R|+|(y/y₀)*R-R| := abs_sub_le _ _ _
      _ ≤ 2*δ/σ+4*V*η+J*|y-y₀| := add_le_add hquot' hamp
      _ ≤ C*δ+C*η+C*|y-y₀| := by
        have hd := mul_le_mul_of_nonneg_right hCδ hδ
        have he := mul_le_mul_of_nonneg_right hCη hη.le
        have hyc := mul_le_mul_of_nonneg_right hCy (abs_nonneg (y-y₀))
        rw [show 2*δ/σ=(2/σ)*δ by ring]
        exact add_le_add (add_le_add hd he) hyc
      _ = _ := by ring

                                                                 
                                                                  
                                                                         
                                                                       
theorem approximateModelPhase_enlarged_common_difference_models
    {σ ε : ℝ} (hσ : 0 < σ) (P : ℕ) (hε : 0 < ε) :
    ∃ δ η₀ a : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      ∀ (N : ℝ) (F : ℝ → ℝ), 1 ≤ N →
      Expdb.IsApproximateModelPhaseFunction F σ (P+2) δ →
      ∃ Fext : ℝ → ℝ,
        (∀ x, 0 < x → ContDiffAt ℝ ∞ Fext x) ∧
        (∀ w∈Icc (1/2:ℝ) 3, ∀ p ≤ P+1,
          |iteratedDeriv (p+1) Fext w-iteratedDeriv p (Expdb.modelPhase σ) w| ≤ ε) ∧
        (∀ (T : ℝ) (m n : ℕ), N ≤ (m:ℝ) → (n:ℝ) ≤ 2*N →
          ‖Expdb.exponentialSumAt F T N m n-Expdb.exponentialSumAt Fext T N m n‖ ≤ 6) ∧
        ∀ (η y y₀ : ℝ), 0 < η → η ≤ η₀ →
          y∈Icc (1:ℝ) 2 → y₀∈Icc (1:ℝ) 2 → |y-y₀| ≤ a →
          let G := fun u => (Fext u-Fext (u+η*y))/(σ*η*y₀)
          Expdb.IsApproximateModelPhaseFunction G (σ+1) P ε ∧
          ∀ T M A x : ℝ,
            TaoTrudgianYang2025.heathBrownPhysicalPhase G (T*y₀) M A 1 x =
              T*(Fext ((A+x)/M)-Fext ((A+x)/M+η*y))/(σ*η) := by
  obtain ⟨C,hC,hmodel⟩ := positive_difference_common_model hσ P
  obtain ⟨B,hB,hbuild⟩ := approximateModelPhase_enlarged_sharp_transport (P+1)
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hBp : 0 < B := zero_lt_one.trans_le hB
  let t := ε/(3*C)
  let δ := t/B
  let η₀ := min (1/8:ℝ) t
  have ht : 0 < t := by dsimp only [t]; positivity
  have hδ : 0 < δ := div_pos ht hBp
  have hη₀ : 0 < η₀ := lt_min (by norm_num) ht
  have hBt : B*δ=t := by dsimp only [δ]; field_simp
  have hCt : C*(t+t+t)=ε := by dsimp only [t]; field_simp; ring
  refine ⟨δ,η₀,t,hδ,hη₀,min_le_left _ _,ht,?_⟩
  intro N F hN hF
  obtain ⟨Fext,hreg,hjets,hsharp⟩ := hbuild σ δ N F hδ.le hN hF
  have hte : t ≤ ε := by
    dsimp only [t]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 3*C)).mpr
    nlinarith only [hε,mul_le_mul_of_nonneg_left hC hε.le]
  have hjetbound w (hw : w∈Icc (1/2:ℝ) 3) p (hp : p ≤ P+1) :
      |iteratedDeriv (p+1) Fext w-iteratedDeriv p (Expdb.modelPhase σ) w| ≤ ε := by
    have hh := hjets w hw p hp
    rw [hBt] at hh
    exact hh.trans hte
  refine ⟨Fext,hreg,hjetbound,hsharp,?_⟩
  intro η y y₀ hη hηmax hy hy₀ hnear G
  have hηsmall : η ≤ 1/8 := hηmax.trans (min_le_left _ _)
  have hηt : η ≤ t := hηmax.trans (min_le_right _ _)
  have hm := hmodel Fext t η y y₀ ht.le hη hηsmall hy hy₀ hreg
    (fun w hw p hp => by simpa only [hBt] using hjets w hw p hp)
  have herror : C*(t+η+|y-y₀|) ≤ ε := by
    calc
      _ ≤ C*(t+t+t) := by gcongr
      _ = _ := hCt
  refine ⟨TaoTrudgianYang2025.approximateModelPhase_mono hm le_rfl herror,?_⟩
  intro T M A x
  have hy₀pos : 0 < y₀ := zero_lt_one.trans_le hy₀.1
  dsimp only [TaoTrudgianYang2025.heathBrownPhysicalPhase,G]
  field_simp

                                                                 
                                                                       
                                                                 
                                                                  
                                           
theorem approximateModelPhase_enlarged_colored_difference_models
    {σ ε : ℝ} (hσ : 0 < σ) (P : ℕ) (hε : 0 < ε) :
    ∃ δ η₀ a : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1 ≤ M →
      Expdb.IsApproximateModelPhaseFunction F σ (P+2) δ →
      ∃ Fext : ℝ → ℝ,
        (∀ w, 0 < w → ContDiffAt ℝ ∞ Fext w) ∧
        (∀ w∈Icc (1/2:ℝ) 3, ∀ p ≤ P+1,
          |iteratedDeriv (p+1) Fext w-iteratedDeriv p (Expdb.modelPhase σ) w| ≤ ε) ∧
        (∀ (T : ℝ) (m n : ℕ), M ≤ (m:ℝ) → (n:ℝ) ≤ 2*M →
          ‖Expdb.exponentialSumAt F T M m n-Expdb.exponentialSumAt Fext T M m n‖ ≤ 6) ∧
        ∀ {ι : Type*} (S : Finset ι) (y : ι → ℝ) (η : ℝ),
          (∀ i∈S, y i∈Icc (1:ℝ) 2) → 0 < η → η ≤ η₀ →
          let color := fun i => ⌊y i/a⌋
          let Cap := 4/a+3
          ((S.image color).card:ℝ) ≤ Cap ∧
          (∀ z : ι → ℂ, ‖∑ i∈S,z i‖^12 ≤
            Cap^11*∑ j∈S.image color, ‖∑ i∈S.filter (fun i => color i=j),z i‖^12) ∧
          ∀ j∈S.image color, ∃ i₀∈S, color i₀=j ∧
            ∀ i∈S, color i=j →
              let G := fun u => (Fext u-Fext (u+η*y i))/(σ*η*y i₀)
              Expdb.IsApproximateModelPhaseFunction G (σ+1) P ε ∧
              ∀ T A x : ℝ,
                TaoTrudgianYang2025.heathBrownPhysicalPhase G (T*y i₀) M A 1 x =
                  T*(Fext ((A+x)/M)-Fext ((A+x)/M+η*y i))/(σ*η) := by
  obtain ⟨δ,η₀,a,hδ,hη₀,hηcap,ha,hsource⟩ :=
    approximateModelPhase_enlarged_common_difference_models hσ P hε
  refine ⟨δ,η₀,a,hδ,hη₀,hηcap,ha,?_⟩
  intro M F hM hF
  obtain ⟨Fext,hreg,hjets,hsharp,hmodels⟩ := hsource M F hM hF
  refine ⟨Fext,hreg,hjets,hsharp,?_⟩
  intro ι S y η hy hη hηmax color Cap
  classical
  have hcard : ((S.image color).card:ℝ) ≤ Cap := by
    have hh := scaled_floor_image_card (Q:=1) (δ:=a) (R:=2) S y
      (by norm_num) ha (by norm_num)
      (by
        intro i hi
        rw [abs_of_pos (zero_lt_one.trans_le (hy i hi).1)]
        simpa only [mul_one] using (hy i hi).2)
    simpa only [mul_one,show (2:ℝ)*2=4 by norm_num] using hh
  refine ⟨hcard,?_,?_⟩
  · intro z
    let J := S.image color
    let V := fun j => S.filter (fun i => color i=j)
    let g := fun j => ∑ i∈V j,z i
    have he : (∑ j∈J,g j)=∑ i∈S,z i :=
      Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem color hi) z
    have hnorm : ‖∑ i∈S,z i‖ ≤ ∑ j∈J,‖g j‖ := by
      rw [←he]
      exact norm_sum_le _ _
    have hp := pow_le_pow_left₀ (norm_nonneg _) hnorm 12
    have hholder := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg J
      (f:=fun j => ‖g j‖) (p:=(12:ℝ)) (by norm_num) (fun _ _ => norm_nonneg _)
    have hh : (∑ j∈J,‖g j‖)^12 ≤ (J.card:ℝ)^11*∑ j∈J,‖g j‖^12 := by
      simpa only [show (12:ℝ)-1=11 by norm_num,Real.rpow_ofNat] using hholder
    exact (hp.trans hh).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ J.card) hcard 11)
      (Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) _)))
  · intro j hj
    obtain ⟨i₀,hi₀,hcol₀⟩ := Finset.mem_image.mp hj
    refine ⟨i₀,hi₀,hcol₀,?_⟩
    intro i hi hcol G
    have hbin : ⌊y i/a⌋=⌊y i₀/a⌋ := hcol.trans hcol₀.symm
    have hh := Int.abs_sub_lt_one_of_floor_eq_floor hbin
    rw [←sub_div,abs_div,abs_of_pos ha] at hh
    have hnear : |y i-y i₀| ≤ a :=
      (by simpa only [one_mul] using ((div_lt_iff₀ ha).mp hh).le)
    have hm := hmodels η (y i) (y i₀) hη hηmax (hy i hi) (hy i₀ hi₀) hnear
    exact ⟨hm.1,fun T A x => hm.2 T M A x⟩

                                                                   
                                                                   
                                                                     
                                               
theorem fourier_parity_round_partition
    {ι : Type*} (S : Finset ι) (z : ι → ℝ) :
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let color := fun ip : ι × Fin 2 => ⌊z ip.1⌋+(ip.2:ℕ)-round (z ip.1)
    (∀ ip∈V, -(1:ℤ) ≤ color ip ∧ color ip ≤ 1) ∧
    (V.image color).card ≤ 3 ∧
    (∀ a : ι × Fin 2 → ℂ, ‖∑ ip∈V,a ip‖^12 ≤
      (3:ℝ)^11*∑ j∈V.image color, ‖∑ ip∈V.filter (fun ip => color ip=j),a ip‖^12) := by
  classical
  intro V color
  have hbound (ip : ι × Fin 2) : -(1:ℤ) ≤ color ip ∧ color ip ≤ 1 := by
    have hlo : ⌊z ip.1⌋ ≤ round (z ip.1) := by
      rw [round_eq]
      exact Int.floor_mono (by linarith)
    have hhi : round (z ip.1) ≤ ⌊z ip.1⌋+1 := by
      rw [round_eq,←Int.floor_add_one]
      exact Int.floor_mono (by linarith)
    have hp := ip.2.isLt
    dsimp only [color]
    omega
  have hcard : (V.image color).card ≤ 3 := by
    have hsub : V.image color ⊆ Finset.Icc (-1:ℤ) 1 := by
      intro j hj
      obtain ⟨ip,_hip,rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_Icc.mpr (hbound ip)
    have hh := Finset.card_le_card hsub
    norm_num at hh
    exact hh
  refine ⟨fun ip _ => hbound ip,hcard,?_⟩
  intro a
  let J := V.image color
  let g := fun j => ∑ ip∈V.filter (fun ip => color ip=j),a ip
  have he : (∑ j∈J,g j)=∑ ip∈V,a ip :=
    Finset.sum_fiberwise_of_maps_to (fun ip hip => Finset.mem_image_of_mem color hip) a
  have hnorm : ‖∑ ip∈V,a ip‖ ≤ ∑ j∈J,‖g j‖ := by
    rw [←he]
    exact norm_sum_le _ _
  have hp := pow_le_pow_left₀ (norm_nonneg _) hnorm 12
  have hholder := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg J
    (f:=fun j => ‖g j‖) (p:=(12:ℝ)) (by norm_num) (fun _ _ => norm_nonneg _)
  have hh : (∑ j∈J,‖g j‖)^12 ≤ (J.card:ℝ)^11*∑ j∈J,‖g j‖^12 := by
    simpa only [show (12:ℝ)-1=11 by norm_num,Real.rpow_ofNat] using hholder
  have hc : (J.card:ℝ) ≤ 3 := by exact_mod_cast hcard
  exact (hp.trans hh).trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ J.card) hc 11)
    (Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) _)))


                                                                   
                                                                    
theorem fourier_inverse_normalized_chart
    {q e v : ℤ} (hq : q ≠ 0) (hinv : q ∣ e*v-1) :
    let s := -v-q*⌊-(v:ℝ)/q⌋
    ∃ u : ℤ, u*q-e*s=1 ∧ (s:ℝ)/q=Int.fract (-(v:ℝ)/q) := by
  intro s
  obtain ⟨m,hm⟩ := hinv
  refine ⟨-m-e*⌊-(v:ℝ)/q⌋,?_,?_⟩
  · dsimp only [s]
    nlinarith only [hm]
  · have hqr : (q:ℝ) ≠ 0 := by exact_mod_cast hq
    simp only [s,Int.cast_sub,Int.cast_neg,Int.cast_mul,Int.fract]
    field_simp

                                                                
                                                                   
                                                                  
                                                                         
theorem fourier_cloud_round_farey_conditions
    (q e v : Fin 2 → ℤ) (ell : Fin 2 → ℝ) (p : Fin 2 → Fin 2)
    {E₀ E₁ D : ℝ}
    (hq : ∀ i, q i ≠ 0) (hinv : ∀ i, q i ∣ e i*v i-1) :
    let b := fun i => ⌊(q i:ℝ)*ell i⌋+(p i:ℕ)
    let c := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let X := fun i => -(v i:ℝ)/q i
    let s := fun i => -v i-q i*⌊X i⌋
    b 0-c 0=b 1-c 1 →
    |Int.fract (X 0*b 0)-Int.fract (X 1*b 1)| ≤ E₀ →
    |Int.fract (X 0)-Int.fract (X 1)| ≤ E₁ →
    |tau 0-tau 1| ≤ D →
    ∃ u : Fin 2 → ℤ, (∀ i, u i*q i-e i*s i=1) ∧
      (∀ i, (s i:ℝ)/q i=Int.fract (X i)) ∧
      |(s 1:ℝ)/q 1-(s 0:ℝ)/q 0| ≤ E₁ ∧
      let C := (c 0:ℝ)*s 0/q 0-(c 1:ℝ)*s 1/q 1
      |C-round C| ≤ E₀+E₁ ∧
      |((q 0:ℝ)*ell 0-c 0)-((q 1:ℝ)*ell 1-c 1)| ≤ 2*D := by
  classical
  intro b c tau X s hcolor hnear₀ hnear₁ htau
  choose u hu hs using fun i => fourier_inverse_normalized_chart (hq i) (hinv i)
  have hs' i : (s i:ℝ)/q i=Int.fract (X i) := hs i
  refine ⟨u,hu,hs',?_,?_⟩
  · rw [hs' 0,hs' 1,abs_sub_comm]
    exact hnear₁
  intro C
  let k := b 0-c 0
  have hc0 : b 0-c 0=k := rfl
  have hc1 : b 1-c 1=k := hcolor.symm
  have hbound := (fourier_parity_round_partition
    (Finset.univ : Finset (Fin 2)) (fun i => (q i:ℝ)*ell i)).1
    (0,p 0) (by simp)
  change -(1:ℤ) ≤ k ∧ k ≤ 1 at hbound
  have hk : |(k:ℝ)| ≤ 1 := by
    rw [abs_le]
    exact_mod_cast hbound
  let n : ℤ := ⌊X 0*b 0⌋-⌊X 1*b 1⌋-k*(⌊X 0⌋-⌊X 1⌋)-
    c 0*⌊X 0⌋+c 1*⌊X 1⌋
  have hcr0 : (c 0:ℝ)=(b 0:ℝ)-k := by exact_mod_cast (by omega : c 0=b 0-k)
  have hcr1 : (c 1:ℝ)=(b 1:ℝ)-k := by exact_mod_cast (by omega : c 1=b 1-k)
  have he : C-(n:ℝ)=
      Int.fract (X 0*b 0)-Int.fract (X 1*b 1)-
        (k:ℝ)*(Int.fract (X 0)-Int.fract (X 1)) := by
    change (c 0:ℝ)*s 0/q 0-(c 1:ℝ)*s 1/q 1-(n:ℝ)=_
    rw [mul_div_assoc,mul_div_assoc,hs' 0,hs' 1]
    simp only [n,Int.cast_add,Int.cast_sub,Int.cast_mul,Int.fract,hcr0,hcr1]
    ring
  constructor
  · apply (round_le C n).trans
    rw [he]
    calc
      _ ≤ |Int.fract (X 0*b 0)-Int.fract (X 1*b 1)|+
          |(k:ℝ)*(Int.fract (X 0)-Int.fract (X 1))| := abs_sub _ _
      _ ≤ E₀+E₁ := by
        apply add_le_add hnear₀
        rw [abs_mul]
        calc
          _ ≤ 1*|Int.fract (X 0)-Int.fract (X 1)| :=
            mul_le_mul_of_nonneg_right hk (abs_nonneg _)
          _ ≤ E₁ := by simpa only [one_mul] using hnear₁
  · have hcR : (b 0:ℝ)-c 0=(b 1:ℝ)-c 1 := by exact_mod_cast hcolor
    have heq : ((q 0:ℝ)*ell 0-c 0)-((q 1:ℝ)*ell 1-c 1)=
        -2*(tau 0-tau 1) := by
      dsimp only [tau]
      linarith only [hcR]
    rw [heq,abs_mul,show |(-2:ℝ)|=2 by norm_num]
    exact mul_le_mul_of_nonneg_left htau (by norm_num)

                                                                    
                                                                   
                                                                 
theorem source_arc_fourier_cloud_rounded_conditions
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ι → ℝ → ℝ) (z : ι → ℝ) (r : ι → ℚ) (v : ι → ℤ)
    (Q K₀ : ℕ) [NeZero K₀] (μ₀ U₀ : ℝ) (hμ₀ : 0 < μ₀)
    (hμbounds : ∀ i∈S, μ₀ ≤ iteratedDeriv 3 (f i) (round (z i))/6 ∧
      iteratedDeriv 3 (f i) (round (z i))/6 ≤ U₀)
    (hlevel : ∀ i∈S, iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ))
    (hden : ∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den)
    (hinv : ∀ i∈S, ((r i).den:ℤ) ∣ (r i).num*v i-1) :
    let q := fun i => (r i).den
    let μ := fun i => iteratedDeriv 3 (f i) (round (z i))/6
    let ℓ := fun i => deriv (f i) (round (z i))
    let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
    let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
    let K := fun i => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun i p =>
      (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let w := fun ip : ι × Fin 2 =>
      (![Int.fract (x ip.1 ip.2 0),Int.fract (x ip.1 ip.2 1),
        x ip.1 ip.2 2/Real.sqrt K₀,x ip.1 ip.2 3/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    let P := (V ×ˢ V).filter (fun ij => ∀ d, |w ij.1 d-w ij.2 d| ≤ 2*radius d)
    let h := fun i => iteratedDeriv 2 (f i) (z i)/2
    let D := (Real.sqrt K₀/(9*(K₀:ℝ))+Real.sqrt K₀/(12*(K₀:ℝ)^2))*
      Real.sqrt (U₀*(Q:ℝ)^3)
    let c := fun i => round ((q i:ℝ)*ℓ i)
    let color := fun ip : ι × Fin 2 => b ip.1 ip.2-c ip.1
    let s := fun i => -v i-(q i:ℤ)*⌊-(v i:ℝ)/q i⌋
    (V.image color).card ≤ 3 ∧
    (∀ coeff : ι × Fin 2 → ℂ, ‖∑ ip∈V,coeff ip‖^12 ≤
      (3:ℝ)^11*∑ j∈V.image color, ‖∑ ip∈V.filter (fun ip => color ip=j),coeff ip‖^12) ∧
    ∃ A : ((ι × Fin 2) × (ι × Fin 2)) → Fin 4 → ℤ,
      (∀ ij∈P,
        A ij 0*A ij 3-A ij 1*A ij 2=1 ∧
        let t := (A ij 2:ℝ)*h ij.1.1+A ij 3
        t=(q ij.2.1:ℝ)/q ij.1.1 ∧ (1:ℝ)/2 ≤ t ∧ t ≤ 2 ∧
        ((A ij 0:ℝ)*h ij.1.1+A ij 1)/t=h ij.2.1 ∧
        |(A ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) ∧
        |μ ij.2.1/μ ij.1.1*t^3-1| ≤
          (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2) ∧
        |τ ij.1.1 ij.1.2-τ ij.2.1 ij.2.2| ≤ D ∧
        (∃ e₁ e₂ : ℤ,
          let F₁ := 2*(round (z ij.2.1):ℝ)-2*(A ij 3:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 2:ℝ)*ℓ ij.1.1
          let F₂ := ℓ ij.2.1-2*(A ij 1:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 0:ℝ)*ℓ ij.1.1
          |F₁-e₁| ≤ (q ij.2.1:ℝ)/(6*(K₀:ℝ))+|(A ij 2:ℝ)|/q ij.1.1 ∧
          |(F₂-e₂)-h ij.2.1*(F₁-e₁)| ≤ 2*D/q ij.2.1) ∧
        ((Q:ℝ)^2/(6*(K₀:ℝ)^2) < 1 →
          A ij 2=0 ∧ q ij.1.1=q ij.2.1 ∧
            (q ij.1.1:ℤ) ∣ (r ij.2.1).num-(r ij.1.1).num)) ∧
      ∀ ij∈P, color ij.1=color ij.2 →
        ∃ u₀ u₁ : ℤ,
          u₀*(q ij.1.1:ℤ)-(r ij.1.1).num*s ij.1.1=1 ∧
          u₁*(q ij.2.1:ℤ)-(r ij.2.1).num*s ij.2.1=1 ∧
          |(s ij.2.1:ℝ)/q ij.2.1-(s ij.1.1:ℝ)/q ij.1.1| ≤ 1/(6*(K₀:ℝ)^2) ∧
          let C := (c ij.1.1:ℝ)*s ij.1.1/q ij.1.1-(c ij.2.1:ℝ)*s ij.2.1/q ij.2.1
          |C-round C| ≤ 1/(6*(K₀:ℝ))+1/(6*(K₀:ℝ)^2) ∧
          |((q ij.1.1:ℝ)*ℓ ij.1.1-c ij.1.1)-((q ij.2.1:ℝ)*ℓ ij.2.1-c ij.2.1)| ≤ 2*D := by
  classical
  intro q μ ℓ b τ K x V w radius P h D c color s
  have hpartition := fourier_parity_round_partition S (fun i => (q i:ℝ)*ℓ i)
  obtain ⟨A,hA⟩ := source_arc_fourier_cloud_matrices S f z r v Q K₀ μ₀ U₀
    hμ₀ hμbounds hlevel hden hinv
  refine ⟨hpartition.2.1,hpartition.2.2,A,hA,?_⟩
  intro ij hij hcolor
  have hp := Finset.mem_filter.mp hij
  have hi : ij.1.1∈S := (Finset.mem_product.mp (Finset.mem_product.mp hp.1).1).1
  have hj : ij.2.1∈S := (Finset.mem_product.mp (Finset.mem_product.mp hp.1).2).1
  let qq : Fin 2 → ℤ := ![(q ij.1.1:ℤ),(q ij.2.1:ℤ)]
  let ee : Fin 2 → ℤ := ![(r ij.1.1).num,(r ij.2.1).num]
  let vv : Fin 2 → ℤ := ![v ij.1.1,v ij.2.1]
  let ll : Fin 2 → ℝ := ![ℓ ij.1.1,ℓ ij.2.1]
  let pp : Fin 2 → Fin 2 := ![ij.1.2,ij.2.2]
  have hqq i : qq i ≠ 0 := by
    fin_cases i
    · change ((q ij.1.1:ℤ)) ≠ 0
      exact_mod_cast (r ij.1.1).den_nz
    · change ((q ij.2.1:ℤ)) ≠ 0
      exact_mod_cast (r ij.2.1).den_nz
  have hinvv i : qq i ∣ ee i*vv i-1 := by
    fin_cases i
    · exact hinv _ hi
    · exact hinv _ hj
  have hnear₀ :
      |Int.fract ((-(v ij.1.1:ℝ)/q ij.1.1)*b ij.1.1 ij.1.2)-
        Int.fract ((-(v ij.2.1:ℝ)/q ij.2.1)*b ij.2.1 ij.2.2)| ≤ 1/(6*(K₀:ℝ)) := by
    have hh := hp.2 (0:Fin 4)
    change |Int.fract (-(v ij.1.1:ℝ)*b ij.1.1 ij.1.2/q ij.1.1)-
      Int.fract (-(v ij.2.1:ℝ)*b ij.2.1 ij.2.2/q ij.2.1)| ≤ 2*(1/(12*(K₀:ℝ))) at hh
    rw [show (-(v ij.1.1:ℝ)/q ij.1.1)*b ij.1.1 ij.1.2=
        -(v ij.1.1:ℝ)*b ij.1.1 ij.1.2/q ij.1.1 by ring,
      show (-(v ij.2.1:ℝ)/q ij.2.1)*b ij.2.1 ij.2.2=
        -(v ij.2.1:ℝ)*b ij.2.1 ij.2.2/q ij.2.1 by ring]
    convert hh using 1
    ring
  have hnear₁ :
      |Int.fract (-(v ij.1.1:ℝ)/q ij.1.1)-Int.fract (-(v ij.2.1:ℝ)/q ij.2.1)| ≤
        1/(6*(K₀:ℝ)^2) := by
    have hh := hp.2 (1:Fin 4)
    change _ ≤ 2*(1/(12*(K₀:ℝ)^2)) at hh
    convert hh using 1
    · change _ = |Int.fract (-(v ij.1.1:ℝ)/q ij.1.1)-Int.fract (-(v ij.2.1:ℝ)/q ij.2.1)|
      rfl
    · ring
  have htau : |τ ij.1.1 ij.1.2-τ ij.2.1 ij.2.2| ≤ D :=
    (hA ij hij).2.2.2.2.2.2.2.1
  have hcol : ⌊(qq 0:ℝ)*ll 0⌋+(pp 0:ℕ)-round ((qq 0:ℝ)*ll 0)=
      ⌊(qq 1:ℝ)*ll 1⌋+(pp 1:ℕ)-round ((qq 1:ℝ)*ll 1) := by
    simpa only [qq,ll,pp,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
      Int.cast_natCast] using hcolor
  have hh := fourier_cloud_round_farey_conditions qq ee vv ll pp hqq hinvv hcol
    (by simpa only [qq,vv,ll,pp,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_fin_one,Int.cast_natCast] using hnear₀)
    (by simpa only [qq,vv,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_fin_one,Int.cast_natCast] using hnear₁)
    (by simpa only [qq,ll,pp,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_fin_one,Int.cast_natCast] using htau)
  obtain ⟨u,hu,_hs,hfirst,hsecond,hfourth⟩ := hh
  refine ⟨u 0,u 1,?_,?_,?_,?_,?_⟩
  · simpa only [qq,ee,vv,Matrix.cons_val_zero,Int.cast_natCast] using hu 0
  · simpa only [qq,ee,vv,Matrix.cons_val_one,Matrix.cons_val_fin_one,Int.cast_natCast] using hu 1
  · simpa only [qq,vv,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_fin_one,Int.cast_natCast] using hfirst
  · simpa only [qq,vv,ll,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_fin_one,Int.cast_natCast] using hsecond
  · simpa only [qq,ll,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_fin_one,Int.cast_natCast] using hfourth

                                                                  
                                                                  
                                                       
theorem positive_difference_common_physical_normalization
    (F : ℝ → ℝ) {σ xi eta y y₀ T M N R : ℝ}
    (hσ : 0 < σ) (hxi : 0 < xi) (heta : 0 < eta) (hy₀ : 0 < y₀)
    (hT : 0 < T) (hR : 0 < R) (hscale : T*N*R^2=M^3) :
    let G := fun u => (F u-F (u+eta*y))/(σ*eta*y₀)
    let Tnew := T*σ*y₀/xi
    let Rnew := R*Real.sqrt (xi/(σ*y₀))
    let f := fun w => T*(F (w/M)-F (w/M+eta*y))/(xi*eta)
    0 < Tnew ∧ 0 < Rnew ∧ Rnew^2=R^2*xi/(σ*y₀) ∧
      Tnew*N*Rnew^2=M^3 ∧
      (∀ A x : ℝ, heathBrownPhysicalPhase G Tnew M A 1 x=f (A+x)) ∧
      (∀ (A : ℤ) (w : ℝ) (k : ℕ),
        iteratedDeriv k (heathBrownPhysicalPhase G Tnew M A 1) (round (w-A))=
          iteratedDeriv k f (round w)) := by
  intro G Tnew Rnew f
  have hratio : 0 < xi/(σ*y₀) := by positivity
  have hsq : Rnew^2=R^2*xi/(σ*y₀) := by
    dsimp only [Rnew]
    rw [mul_pow,Real.sq_sqrt hratio.le]
    ring
  have hfun A : heathBrownPhysicalPhase G Tnew M A 1=fun x => f (A+x) := by
    funext x
    dsimp only [heathBrownPhysicalPhase,G,Tnew,f]
    field_simp
  refine ⟨by dsimp only [Tnew]; positivity,
    mul_pos hR (Real.sqrt_pos.mpr hratio),hsq,?_,?_,?_⟩
  · rw [hsq]
    dsimp only [Tnew]
    calc
      _ = T*N*R^2 := by field_simp
      _ = M^3 := hscale
  · intro A x
    exact congrFun (hfun A) x
  · intro A w k
    rw [hfun,iteratedDeriv_comp_const_add,round_sub_intCast,Int.cast_sub]
    simp only [add_sub_cancel]

                                                           
                                                                  
                                                           
theorem fourier_cloud_linked_error_bounds
    {J c N R Q K : ℝ} (hJ : 0 < J) (hc : 0 < c)
    (hN : 0 < N) (hR : 0 < R) (hQ : 0 < Q)
    (hK : 1 ≤ K) (hscale : Q*N ≤ K*R^2) :
    let U := J/(N*R^2)
    let mu := c/(N*R^2)
    let D := (Real.sqrt K/(9*K)+Real.sqrt K/(12*K^2))*Real.sqrt (U*Q^3)
    1/(6*K^2) ≤ R^4/(6*Q^2*N^2) ∧
      1/(6*K)+1/(6*K^2) ≤ R^2/(3*Q*N) ∧
      D ≤ (7/36:ℝ)*Real.sqrt J*Q/N ∧
      (16*U/mu)*Real.sqrt (U*Q^3)*Real.sqrt K/(6*K^2) ≤
        (8*J*Real.sqrt J/(3*c))*R^2/N^2 := by
  intro U mu D
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hmesh : 1/K ≤ R^2/(Q*N) := by
    apply (div_le_div_iff₀ hKp (mul_pos hQ hN)).mpr
    simpa only [one_mul,mul_one,mul_comm] using hscale
  have hmesh2 : 1/K^2 ≤ R^4/(Q^2*N^2) := by
    have hh := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1/K) hmesh 2
    convert hh using 1 <;> field_simp
  have hKinv : 1/K ≤ 1 := (div_le_one hKp).mpr hK
  have hKtwo : 1/K^2 ≤ 1/K := by
    rw [show 1/K^2=(1/K)*(1/K) by field_simp]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hKinv
      (by positivity : (0:ℝ) ≤ 1/K)
  let B := Real.sqrt (U*Q^3)*Real.sqrt K/K
  have hBp : 0 ≤ B := by dsimp only [B,U]; positivity
  have hBsquare : B^2=J*Q^3/(N*R^2*K) := by
    dsimp only [B,U]
    rw [div_pow,mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt hKp.le]
    field_simp
  have hBbound : B ≤ Real.sqrt J*Q/N := by
    apply (sq_le_sq₀ hBp (by positivity)).mp
    rw [hBsquare,div_pow,mul_pow,Real.sq_sqrt hJ.le]
    apply (div_le_div_iff₀ (by positivity : 0 < N*R^2*K) (sq_pos_of_pos hN)).mpr
    convert mul_le_mul_of_nonneg_left hscale
      (show 0 ≤ J*Q^2*N by positivity) using 1 <;> ring
  have hfactor : (1/9:ℝ)+1/(12*K) ≤ 7/36 := by
    have hh := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)
      (by norm_num : (0:ℝ) < 12) (by linarith only [hK] : 12 ≤ 12*K)
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_left hmesh2 (by norm_num : (0:ℝ) ≤ 1/6)
    convert hh using 1 <;> ring
  · have hh := add_le_add hmesh (hKtwo.trans hmesh)
    have hh' := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 1/6)
    convert hh' using 1 <;> ring
  · calc
      D = ((1/9:ℝ)+1/(12*K))*B := by dsimp only [D,B]; field_simp
      _ ≤ (7/36:ℝ)*(Real.sqrt J*Q/N) :=
        mul_le_mul hfactor hBbound hBp (by norm_num)
      _ = _ := by ring
  · have he : 16*U/mu=16*J/c := by dsimp only [U,mu]; field_simp
    calc
      _ = (8*J/(3*c))*B*(1/K) := by rw [he]; dsimp only [B]; field_simp; ring
      _ ≤ (8*J/(3*c))*(Real.sqrt J*Q/N)*(R^2/(Q*N)) := by
        gcongr
      _ = _ := by field_simp

                                                                
                                                               
                                                    
theorem source_arc_fourier_cloud_linked_conditions
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ι → ℝ → ℝ) (z : ι → ℝ) (r : ι → ℚ) (v : ι → ℤ)
    (Q K₀ : ℕ) [NeZero K₀] {c J N R : ℝ}
    (hc : 0 < c) (hJ : 0 < J) (hN : 0 < N) (hR : 0 < R) (hQ : 0 < Q)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hμbounds : ∀ i∈S, c/(N*R^2) ≤ iteratedDeriv 3 (f i) (round (z i))/6 ∧
      iteratedDeriv 3 (f i) (round (z i))/6 ≤ J/(N*R^2))
    (hlevel : ∀ i∈S, iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ))
    (hden : ∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den)
    (hinv : ∀ i∈S, ((r i).den:ℤ) ∣ (r i).num*v i-1) :
    let U₀ := J/(N*R^2)
    let q := fun i => (r i).den
    let μ := fun i => iteratedDeriv 3 (f i) (round (z i))/6
    let ℓ := fun i => deriv (f i) (round (z i))
    let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
    let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
    let K := fun i => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun i p =>
      (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let w := fun ip : ι × Fin 2 =>
      (![Int.fract (x ip.1 ip.2 0),Int.fract (x ip.1 ip.2 1),
        x ip.1 ip.2 2/Real.sqrt K₀,x ip.1 ip.2 3/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    let P := (V ×ˢ V).filter (fun ij => ∀ d, |w ij.1 d-w ij.2 d| ≤ 2*radius d)
    let h := fun i => iteratedDeriv 2 (f i) (z i)/2
    let D := (Real.sqrt K₀/(9*(K₀:ℝ))+Real.sqrt K₀/(12*(K₀:ℝ)^2))*
      Real.sqrt (U₀*(Q:ℝ)^3)
    let cround := fun i => round ((q i:ℝ)*ℓ i)
    let color := fun ip : ι × Fin 2 => b ip.1 ip.2-cround ip.1
    let s := fun i => -v i-(q i:ℤ)*⌊-(v i:ℝ)/q i⌋
    (V.image color).card ≤ 3 ∧
    (∀ coeff : ι × Fin 2 → ℂ, ‖∑ ip∈V,coeff ip‖^12 ≤
      (3:ℝ)^11*∑ j∈V.image color, ‖∑ ip∈V.filter (fun ip => color ip=j),coeff ip‖^12) ∧
    ∃ A : ((ι × Fin 2) × (ι × Fin 2)) → Fin 4 → ℤ,
      (∀ ij∈P,
        A ij 0*A ij 3-A ij 1*A ij 2=1 ∧
        let t := (A ij 2:ℝ)*h ij.1.1+A ij 3
        t=(q ij.2.1:ℝ)/q ij.1.1 ∧ (1:ℝ)/2 ≤ t ∧ t ≤ 2 ∧
        ((A ij 0:ℝ)*h ij.1.1+A ij 1)/t=h ij.2.1 ∧
        |(A ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) ∧
        |μ ij.2.1/μ ij.1.1*t^3-1| ≤
          (8*J*Real.sqrt J/(3*c))*R^2/N^2 ∧
        |τ ij.1.1 ij.1.2-τ ij.2.1 ij.2.2| ≤ D ∧
        (∃ e₁ e₂ : ℤ,
          let F₁ := 2*(round (z ij.2.1):ℝ)-2*(A ij 3:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 2:ℝ)*ℓ ij.1.1
          let F₂ := ℓ ij.2.1-2*(A ij 1:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 0:ℝ)*ℓ ij.1.1
          |F₁-e₁| ≤ (q ij.2.1:ℝ)/(6*(K₀:ℝ))+|(A ij 2:ℝ)|/q ij.1.1 ∧
          |(F₂-e₂)-h ij.2.1*(F₁-e₁)| ≤ 2*D/q ij.2.1) ∧
        ((Q:ℝ)^2/(6*(K₀:ℝ)^2) < 1 →
          A ij 2=0 ∧ q ij.1.1=q ij.2.1 ∧
            (q ij.1.1:ℤ) ∣ (r ij.2.1).num-(r ij.1.1).num)) ∧
      ∀ ij∈P, color ij.1=color ij.2 →
        ∃ u₀ u₁ : ℤ,
          u₀*(q ij.1.1:ℤ)-(r ij.1.1).num*s ij.1.1=1 ∧
          u₁*(q ij.2.1:ℤ)-(r ij.2.1).num*s ij.2.1=1 ∧
          |(s ij.2.1:ℝ)/q ij.2.1-(s ij.1.1:ℝ)/q ij.1.1| ≤ R^4/(6*(Q:ℝ)^2*N^2) ∧
          let C := (cround ij.1.1:ℝ)*s ij.1.1/q ij.1.1-(cround ij.2.1:ℝ)*s ij.2.1/q ij.2.1
          |C-round C| ≤ R^2/(3*(Q:ℝ)*N) ∧
          |((q ij.1.1:ℝ)*ℓ ij.1.1-cround ij.1.1)-((q ij.2.1:ℝ)*ℓ ij.2.1-cround ij.2.1)| ≤ (7/18:ℝ)*Real.sqrt J*(Q:ℝ)/N := by
  classical
  intro U₀ q μ ℓ b τ K x V w radius P h D cround color s
  let μ₀ := c/(N*R^2)
  have hμ₀ : 0 < μ₀ := by dsimp only [μ₀]; positivity
  have hK : (1:ℝ) ≤ K₀ := by exact_mod_cast (NeZero.pos K₀)
  have hQR : (0:ℝ) < Q := by exact_mod_cast hQ
  have herrors := fourier_cloud_linked_error_bounds hJ hc hN hR hQR hK hmesh
  obtain ⟨hcard,hloss,A,hA,hround⟩ :=
    source_arc_fourier_cloud_rounded_conditions S f z r v Q K₀ μ₀ U₀ hμ₀
      hμbounds hlevel hden hinv
  refine ⟨hcard,hloss,A,?_,?_⟩
  · intro ij hij
    obtain ⟨hdet,ht,htlo,hthi,hmap,hgamma,hthird,htau,hstrip,hupper⟩ := hA ij hij
    exact ⟨hdet,ht,htlo,hthi,hmap,hgamma,hthird.trans herrors.2.2.2,htau,hstrip,hupper⟩
  · intro ij hij hcolor
    obtain ⟨u₀,u₁,hu₀,hu₁,hfirst,hsecond,hfourth⟩ := hround ij hij hcolor
    refine ⟨u₀,u₁,hu₀,hu₁,hfirst.trans herrors.1,hsecond.trans herrors.2.1,?_⟩
    have hh := mul_le_mul_of_nonneg_left herrors.2.2.1 (by norm_num : (0:ℝ) ≤ 2)
    exact hfourth.trans (hh.trans_eq (by ring))

                                                                  
                                                                   
                                                                        
theorem physicalModelPhase_actual_fourier_conditions
    {σ δ T M N R : ℝ} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let s := fun i => -vinv i-(q i:ℤ)*⌊-(vinv i:ℝ)/q i⌋
    ∃ v : Fin 2 → ℤ, (∀ i, v i*(q i:ℤ)-(rat i).num*s i=1) ∧
      |mu 1*(q 1:ℝ)^3/(mu 0*(q 0:ℝ)^3)-1| ≤ B*R^2/N^2 ∧
      |(s 1:ℝ)/q 1-(s 0:ℝ)/q 0| ≤ B*R^4/((q 0:ℝ)^2*N^2) ∧
      let C := (cround 0:ℝ)*s 0/q 0-(cround 1:ℝ)*s 1/q 1
      |C-round C| ≤ B*R^2/((q 0:ℝ)*N) ∧
      |((q 0:ℝ)*ell 0-cround 0)-((q 1:ℝ)*ell 1-cround 1)| ≤ B*(q 0:ℝ)/N := by
  classical
  intro f hlevel q mu ell b cround tau dual w radius hcolor hnear c J B s
  have hκ := modelPhaseThirdLower_pos hσ
  have hc : 0 < c := by dsimp only [c]; positivity
  have hJ : 0 < J := by dsimp only [J]; positivity
  have hTeq : T=M^3/(N*R^2) :=
    (eq_div_iff (by positivity)).mpr (by nlinarith only [hscale])
  have hbounds i :
      c/(N*R^2) ≤ mu i ∧ mu i ≤ J/(N*R^2) := by
    have hF₂ := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 3) le_rfl
    have hrnd := physicalModelPhase_halfCurvature_round_error hσ.le hF₂
      hT hM (hA i) (hW i) (hx₀ i)
    have hh := physicalModelPhase_cubicCoefficient_bounds hσ hδ hF₂
      hT hM (hA i) (hW i) hrnd.1
    change modelPhaseThirdLower σ*T/(6*M^3) ≤ mu i ∧
      mu i ≤ (σ*(σ+1)+1)*T/(6*M^3) at hh
    convert hh using 1 <;> rw [hTeq] <;> dsimp only [c,J] <;> field_simp
  have hqp i : (0:ℝ) < q i := by exact_mod_cast (rat i).pos
  have hQR : (0:ℝ) < Q := by exact_mod_cast hQ
  have hqQ : (q 0:ℝ) ≤ Q := by exact_mod_cast (hden 0).1
  have hQq : (Q:ℝ) ≤ 2*q 0 := by exact_mod_cast (hden 0).2
  have hmu : 0 < mu 0 := lt_of_lt_of_le (by positivity) (hbounds 0).1
  obtain ⟨_hcard,_hloss,Mat,hMat,hround⟩ :=
    source_arc_fourier_cloud_linked_conditions (Finset.univ : Finset (Fin 2))
      f x₀ rat vinv Q K₀ hc hJ hN hR hQ hmesh
      (fun i _ => hbounds i) (fun i _ => hlevel i)
      (fun i _ => hden i) (fun i _ => hinv i)
  let ij : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) := ((0,parity 0),(1,parity 1))
  have hdata := hMat ij (by
    apply Finset.mem_filter.mpr
    exact ⟨by simp,hnear⟩)
  obtain ⟨_hdet,ht,_htlo,_hthi,_hmap,_hgamma,hthird,_htau,_hstrip,_hupper⟩ := hdata
  obtain ⟨v₀,v₁,hv₀,hv₁,hfirst,hsecond,hfourth⟩ := hround ij (by
    apply Finset.mem_filter.mpr
    exact ⟨by simp,hnear⟩) hcolor
  have hB1 : 1 ≤ B := le_max_left _ _
  have hBJ : 2*Real.sqrt J ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hBC : 8*J*Real.sqrt J/(3*c) ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨![v₀,v₁],?_,?_,?_,?_,?_⟩
  · intro i
    fin_cases i
    · exact hv₀
    · exact hv₁
  · rw [ht] at hthird
    have he : mu 1/mu 0*((q 1:ℝ)/q 0)^3-1=
        mu 1*(q 1:ℝ)^3/(mu 0*(q 0:ℝ)^3)-1 := by field_simp
    change |mu 1/mu 0*((q 1:ℝ)/q 0)^3-1| ≤ _ at hthird
    rw [he] at hthird
    exact hthird.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hBC (sq_nonneg R)) (sq_nonneg N))
  · apply hfirst.trans
    calc
      R^4/(6*(Q:ℝ)^2*N^2) ≤ R^4/((q 0:ℝ)^2*N^2) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        have hh := pow_le_pow_left₀ (hqp 0).le hqQ 2
        nlinarith only [mul_le_mul_of_nonneg_right hh (sq_nonneg N),
          mul_nonneg (sq_nonneg (Q:ℝ)) (sq_nonneg N)]
      _ ≤ B*(R^4/((q 0:ℝ)^2*N^2)) :=
        le_mul_of_one_le_left (by positivity) hB1
      _ = _ := by ring
  · apply hsecond.trans
    calc
      R^2/(3*(Q:ℝ)*N) ≤ R^2/((q 0:ℝ)*N) := by
        apply div_le_div_of_nonneg_left (sq_nonneg R) (by positivity)
        nlinarith only [mul_le_mul_of_nonneg_right hqQ hN.le,mul_pos hQR hN]
      _ ≤ B*(R^2/((q 0:ℝ)*N)) :=
        le_mul_of_one_le_left (by positivity) hB1
      _ = _ := by ring
  · apply hfourth.trans
    calc
      (7/18:ℝ)*Real.sqrt J*(Q:ℝ)/N ≤ Real.sqrt J*(Q:ℝ)/N := by
        gcongr
        nlinarith only [Real.sqrt_nonneg J]
      _ ≤ (2*Real.sqrt J)*(q 0:ℝ)/N := by
        apply div_le_div_of_nonneg_right _ hN.le
        have hh := mul_le_mul_of_nonneg_left hQq (Real.sqrt_nonneg J)
        nlinarith only [hh]
      _ ≤ _ := by gcongr

                                                              
                                                                      
                                                                  
theorem minorArcCenterLabels_fourier_parity
    {x eps : ℝ} {c : ℤ} (heps : eps < 1/2)
    (hc : c∈minorArcCenterLabels x eps) :
    ∃ p : Fin 2, c=⌊x⌋+(p:ℕ) := by
  have hnear : |x-c| < 1 :=
    ((mem_minorArcCenterLabels_iff heps).mp hc).trans_lt (by linarith only [heps])
  have hh := abs_lt.mp hnear
  have hlo : (⌊x⌋:ℝ)-1 < c := by
    linarith only [Int.floor_le x,hh.2]
  have hhi : (c:ℝ) < (⌊x⌋:ℝ)+2 := by
    linarith only [Int.lt_floor_add_one x,hh.1]
  have hloZ : ⌊x⌋-1 < c := by exact_mod_cast hlo
  have hhiZ : c < ⌊x⌋+2 := by exact_mod_cast hhi
  have hcCases : c=⌊x⌋ ∨ c=⌊x⌋+1 := by omega
  rcases hcCases with hh | hh
  · exact ⟨0,by simpa using hh⟩
  · exact ⟨1,by simpa using hh⟩

                                                                        
                                                                     
                                                                  
                                                                       
theorem farey_matrix_companion_unique
    {a b c d e₀ r₀ v₀ s₀ e₁ r₁ v₁ s₁ : ℤ}
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (h₀ : v₀*r₀-e₀*s₀=1) (h₁ : v₁*r₁-e₁*s₁=1)
    (hdet : a*d-b*c=1)
    (he : a*e₀+b*r₀=e₁) (hr : c*e₀+d*r₀=r₁)
    (hsmall : |c|+|r₀*s₁-s₀*r₁| < r₀*r₁) :
    a*v₀+b*s₀=v₁ ∧ c*v₀+d*s₀=s₁ := by
  let ds := c*v₀+d*s₀-s₁
  let dv := a*v₀+b*s₀-v₁
  have htransport : (a*v₀+b*s₀)*r₁-e₁*(c*v₀+d*s₀)=1 := by
    calc
      _ = (a*d-b*c)*(v₀*r₀-e₀*s₀) := by rw [←he,←hr]; ring
      _ = 1 := by rw [hdet,h₀]; norm_num
  have hrel : dv*r₁-e₁*ds=0 := by
    dsimp only [ds,dv]
    linear_combination htransport-h₁
  let k := v₁*ds-s₁*dv
  have hds : ds=k*r₁ := by
    dsimp only [k]
    linear_combination -ds*h₁+s₁*hrel
  have hc : c-(r₀*s₁-s₀*r₁)=r₀*ds := by
    dsimp only [ds]
    linear_combination -c*h₀-s₀*hr
  have hkbound : |r₀*r₁*k| < r₀*r₁ := by
    calc
      _ = |c-(r₀*s₁-s₀*r₁)| := by rw [hc,hds]; congr 1; ring
      _ ≤ |c|+|r₀*s₁-s₀*r₁| := abs_sub c _
      _ < _ := hsmall
  rw [abs_mul,abs_of_pos (mul_pos hr₀ hr₁)] at hkbound
  have hk : |k| < 1 := by nlinarith only [hkbound,mul_pos hr₀ hr₁]
  have hkzero : k=0 := Int.abs_lt_one_iff.mp hk
  have hdszero : ds=0 := by rw [hds,hkzero,zero_mul]
  have hdvzero : dv=0 := by
    rw [hdszero,mul_zero,sub_zero] at hrel
    exact (mul_eq_zero.mp hrel).resolve_right hr₁.ne'
  constructor <;> dsimp only [ds,dv] at hdszero hdvzero <;> omega


                                                                       
                                                                     
                                                               
theorem fourier_matrix_normalized_chart_transport
    (q e vinv : Fin 2 → ℤ) (A : Fin 4 → ℤ) {Q K : ℝ}
    (hq : ∀ i, 0 < q i) (hK : 1 ≤ K)
    (hband : ∀ i, (q i:ℝ) ≤ Q ∧ Q ≤ 2*q i)
    (hinv : ∀ i, q i ∣ e i*vinv i-1)
    (hdet : A 0*A 3-A 1*A 2=1)
    (ht : (A 2:ℝ)*((e 0:ℝ)/q 0)+A 3=(q 1:ℝ)/q 0)
    (hmap : ((A 0:ℝ)*((e 0:ℝ)/q 0)+A 1)/
      ((A 2:ℝ)*((e 0:ℝ)/q 0)+A 3)=(e 1:ℝ)/q 1)
    (hgamma : |(A 2:ℝ)| ≤ Q^2/(6*K^2))
    (hnear : |Int.fract (-(vinv 0:ℝ)/q 0)-
      Int.fract (-(vinv 1:ℝ)/q 1)| ≤ 1/(6*K^2)) :
    let s := fun i => -vinv i-q i*⌊-(vinv i:ℝ)/q i⌋
    ∃ v : Fin 2 → ℤ,
      (∀ i, v i*q i-e i*s i=1) ∧
      (∀ i, (s i:ℝ)/q i=Int.fract (-(vinv i:ℝ)/q i)) ∧
      ∀ u t : ℤ,
        A 0*(e 0*u+v 0*t)+A 1*(q 0*u+s 0*t)=e 1*u+v 1*t ∧
        A 2*(e 0*u+v 0*t)+A 3*(q 0*u+s 0*t)=q 1*u+s 1*t := by
  classical
  intro s
  have hqr i : (0:ℝ) < q i := by exact_mod_cast hq i
  have hq₀ : (q 0:ℝ) ≠ 0 := (hqr 0).ne'
  have hq₁ : (q 1:ℝ) ≠ 0 := (hqr 1).ne'
  choose v hv hs using fun i => fourier_inverse_normalized_chart (hq i).ne' (hinv i)
  have hs' i : (s i:ℝ)/q i=Int.fract (-(vinv i:ℝ)/q i) := hs i
  have hdenR : (A 2:ℝ)*e 0+A 3*q 0=q 1 := by
    calc
      _ = ((A 2:ℝ)*((e 0:ℝ)/q 0)+A 3)*q 0 := by field_simp
      _ = q 1 := by rw [ht]; field_simp
  have hnumR : (A 0:ℝ)*e 0+A 1*q 0=e 1 := by
    rw [ht] at hmap
    have hh := (div_eq_iff (div_ne_zero (hqr 1).ne' (hqr 0).ne')).mp hmap
    field_simp [hq₀,hq₁] at hh
    nlinarith only [hh]
  have hden : A 2*e 0+A 3*q 0=q 1 := by exact_mod_cast hdenR
  have hnum : A 0*e 0+A 1*q 0=e 1 := by exact_mod_cast hnumR
  have hp : (0:ℝ) < (q 0:ℝ)*q 1 := mul_pos (hqr 0) (hqr 1)
  have hcanon : |(q 0:ℝ)*s 1-(s 0:ℝ)*q 1| ≤ (q 0:ℝ)*q 1/(6*K^2) := by
    calc
      _ = |(s 1:ℝ)/q 1-(s 0:ℝ)/q 0| *((q 0:ℝ)*q 1) := by
        rw [←abs_of_pos hp,←abs_mul]
        congr 1
        field_simp
      _ ≤ (1/(6*K^2))*((q 0:ℝ)*q 1) := by
        apply mul_le_mul_of_nonneg_right _ hp.le
        rw [hs' 0,hs' 1,abs_sub_comm]
        exact hnear
      _ = _ := by ring
  have hKden : 6 ≤ 6*K^2 := by nlinarith only [hK,sq_nonneg (K-1)]
  have hQ : 0 < Q := (hqr 0).trans_le (hband 0).1
  have hQsq : Q^2 ≤ 4*((q 0:ℝ)*q 1) := by
    have hh := mul_le_mul (hband 0).2 (hband 1).2 hQ.le
      (mul_nonneg (by norm_num) (hqr 0).le)
    nlinarith only [hh]
  have hgamma' : |(A 2:ℝ)| ≤ Q^2/6 :=
    hgamma.trans (div_le_div_of_nonneg_left (sq_nonneg Q) (by norm_num) hKden)
  have hcanon' : |(q 0:ℝ)*s 1-(s 0:ℝ)*q 1| ≤ (q 0:ℝ)*q 1/6 :=
    hcanon.trans (div_le_div_of_nonneg_left hp.le (by norm_num) hKden)
  have hsmallR : |(A 2:ℝ)|+|(q 0:ℝ)*s 1-(s 0:ℝ)*q 1| < (q 0:ℝ)*q 1 := by
    nlinarith only [hgamma',hcanon',hQsq,hp]
  have hsmall : |A 2|+|q 0*s 1-s 0*q 1| < q 0*q 1 := by exact_mod_cast hsmallR
  have hc := farey_matrix_companion_unique (hq 0) (hq 1)
    (hv 0) (hv 1) hdet hnum hden hsmall
  refine ⟨v,hv,hs',?_⟩
  intro u t
  constructor
  · linear_combination u*hnum+t*hc.1
  · linear_combination u*hden+t*hc.2


theorem physicalModelPhase_short_block_residual_difference_signed
    {σ δ T M N R Q K : ℝ} {u t : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (hsmall : K*R^2/N^2 ≤ 1/2)
    (hNR : N ≤ R^2) (hRN : R ≤ N) (hcube : N^3 ≤ M*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, 0 < r i) (ht : t ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1) :
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun i => round (x₁ i)-round (x₀ i)
    let q := fun i => (r i:ℝ)*u+s i*t
    let d₀ := fun i => iteratedDeriv 1 (f i) (round (x₀ i))
    let d₁ := fun i => iteratedDeriv 1 (f i) (round (x₁ i))
    let c := fun i => round ((r i:ℝ)*d₀ i)
    let θ := fun i => (r i:ℝ)*d₀ i-c i
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let C := (c 0:ℝ)*s 0/r 0-(c 1:ℝ)*s 1/r 1
    let C₂ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ
    let C₃ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ
    let κ := TaoTrudgianYang2025.modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let γ := fun i => q i*(d₁ i-d₀ i-2*(e i:ℝ)*n i/r i-
      (n i:ℝ)*t/(r i*q i))
    let H := fun i => ((c i:ℝ)*s i-n i)*t/r i+θ i*q i/r i+γ i
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    (∀ i, |(n i:ℝ)| ≤ N) →
    (∀ i, 0 < q i ∧ q i ≤ Q) →
    (∀ i, |(t:ℝ)|/r i ≤ q i/R^2) →
    R^2/N ≤ (r 0:ℝ) →
    |μ 1*(r 1:ℝ)^3/(μ 0*(r 0:ℝ)^3)-1| ≤ K*R^2/N^2 →
    |(s 1:ℝ)/r 1-(s 0:ℝ)/r 0| ≤ K*R^4/((r 0:ℝ)^2*N^2) →
    |C-round C| ≤ K*R^2/((r 0:ℝ)*N) →
    |θ 0-θ 1| ≤ K*(r 0:ℝ)/N →
    |H 0-H 1-(round C:ℝ)*t| ≤ (37*K/2+16*K*Cc+2*Ct+2*Cc)*Q/N := by

  let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
  let n := fun i => round (x₁ i)-round (x₀ i)
  let q := fun i => (r i:ℝ)*u+s i*t
  let d₀ := fun i => iteratedDeriv 1 (f i) (round (x₀ i))
  let d₁ := fun i => iteratedDeriv 1 (f i) (round (x₁ i))
  let c := fun i => round ((r i:ℝ)*d₀ i)
  let θ := fun i => (r i:ℝ)*d₀ i-c i
  let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
  let U := (u:ℝ)/t+(s 0:ℝ)/r 0
  let C := (c 0:ℝ)*s 0/r 0-(c 1:ℝ)*s 1/r 1
  let C₂ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ
  let C₃ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ
  let κ := TaoTrudgianYang2025.modelPhaseThirdLower σ
  let Ct := C₂/2+5*C₃/12
  let Cc := C₂/κ+C₃/(2*κ)

  change _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _
  intro hbase hpoint hnN hqpos hgeom hminr hthird hfirst hsecond hfourth
  have hr' (i) : (0:ℝ) < r i := by exact_mod_cast hr i
  have ht' : (t:ℝ) ≠ 0 := by exact_mod_cast ht
  have htpos : 0 < |(t:ℝ)| := abs_pos.mpr ht'
  have hrne (i) : r i ≠ 0 := (hr i).ne'
  have htne : t ≠ 0 := ht
  have hq (i) : r i*u+s i*t ≠ 0 := by
    have hh : q i ≠ 0 := (hqpos i).1.ne'
    dsimp only [q] at hh
    exact_mod_cast hh
  have hq' (i) : q i ≠ 0 := (hqpos i).1.ne'
  have hdet' (i) : (v i:ℝ)*r i-e i*s i=1 := by exact_mod_cast hdet i
  have hF₂ (i) := TaoTrudgianYang2025.approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 3) le_rfl
  have hround := (physicalModelPhase_halfCurvature_round_error hσ.le (hF₂ 0)
    hT hM (hA 0) (hW 0) (hx₀ 0)).1
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans
    (TaoTrudgianYang2025.approximateModelPhase_iteratedDeriv_error (hF 0)
      (TaoTrudgianYang2025.heathBrownPhysicalPoint_mem_interior hM (hA 0) (hW 0) hround)
      3 le_rfl)
  have hC₂ : 0 ≤ C₂ := add_nonneg (TaoTrudgianYang2025.modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ : 0 ≤ C₃ := add_nonneg (TaoTrudgianYang2025.modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hκ : 0 < κ := TaoTrudgianYang2025.modelPhaseThirdLower_pos hσ
  let G := minorArcCoordinate (μ 0) (r 0) (s 0) ((u:ℝ)/t)
  have hcoord : |(n 0:ℝ)-G| ≤ C₂/κ+C₃*|(n 0:ℝ)|^2/(2*κ*M) := by
    have hh := physicalModelPhase_rounded_minorArcCoordinate_entry hσ hδ (hF 0)
      hT hM (hA 0) (hW 0) (hx₀ 0) (hx₁ 0) (hr' 0).ne' ht' (hq' 0) (hdet' 0)
      (hbase 0) (hpoint 0)
    dsimp only [n,G,μ,f,C₂,C₃,κ]
    push_cast
    exact hh
  have hG : |G| ≤ |(n 0:ℝ)|+(C₂/κ+C₃*|(n 0:ℝ)|^2/(2*κ*M)) := by
    have hh := abs_sub_le G (n 0:ℝ) 0
    simp only [sub_zero,abs_sub_comm G] at hh
    linarith only [hh,hcoord]
  have hgeomQ (i) : |(t:ℝ)|/r i ≤ Q/R^2 := (hgeom i).trans
    (div_le_div_of_nonneg_right (hqpos i).2 (sq_nonneg R))
  have hU : U=q 0/((r 0:ℝ)*t) := by
    dsimp [U,q]
    field_simp [ht',(hr' 0).ne']
  have hUabs : |U|=q 0/((r 0:ℝ)*|(t:ℝ)|) := by
    rw [hU,abs_div,abs_mul,abs_of_pos (hqpos 0).1,abs_of_pos (hr' 0)]
  have hfirstNormalized : |(s 1:ℝ)/r 1-(s 0:ℝ)/r 0| ≤ (K*R^2/N^2)*|U| := by
    apply hfirst.trans
    rw [hUabs]
    have hg := (div_le_div_iff₀ (hr' 0) (pow_pos hR 2)).mp (hgeom 0)
    have hrat : R^2/(r 0:ℝ)^2 ≤ q 0/((r 0:ℝ)*|(t:ℝ)|) := by
      apply (div_le_div_iff₀ (pow_pos (hr' 0) 2) (mul_pos (hr' 0) htpos)).mpr
      have hh := mul_le_mul_of_nonneg_left hg (hr' 0).le
      dsimp only [q] at hh ⊢
      nlinarith only [hh]
    have hh := mul_le_mul_of_nonneg_left hrat (show 0 ≤ K*R^2/N^2 by positivity)
    convert hh using 1
    ring
  have hbudget := short_block_fourth_budget hC₂ hC₃ hκ hM hN hR hQ hK
    (abs_nonneg (n 0:ℝ)) (abs_nonneg (n 1:ℝ)) (hnN 0) (hnN 1)
    (hr' 0) (abs_nonneg (t:ℝ)) (hqpos 0).1.le (hqpos 1).1.le (hqpos 0).2 (hqpos 1).2
    hNR hRN hcube hminr (hgeomQ 0) (hgeomQ 1) hG
  have hnear := physicalModelPhase_base_residual_difference_bound hσ hδ hF
    hT hM hN hR hscale hsmall hsmall hA hW hx₀ hx₁ hrne htne hq hdet
    hbase hpoint hthird hfirstNormalized hsecond hfourth
  let D := fun z => C₂*z/(2*N*R^2)+5*C₃*z^3/(12*M*N*R^2)
  let V := fun z => C₂/κ+C₃*z^2/(2*κ*M)
  apply hnear.trans
  change (K*R^2/((r 0:ℝ)*N))*|(t:ℝ)|+
      (12*(K*R^2/N^2)+4*(K*R^2/N^2))*
        |rationalBranch (μ 0) (r 0) (s 0) ((u:ℝ)/t)| * |(t:ℝ)|+
      (K*(r 0:ℝ)/N)*|q 0/r 0|+(1/2:ℝ)*|(t:ℝ)| * ((K*R^2/N^2)*|U|)+
      |q 0| * D |(n 0:ℝ)|+|q 1| * D |(n 1:ℝ)|+
      V |(n 0:ℝ)| * |(t:ℝ)/r 0|+V |(n 1:ℝ)| * |(t:ℝ)/r 1| ≤
        (37*K/2+16*K*Cc+2*Ct+2*Cc)*Q/N
  rw [← minorArcCoordinate_div_eq_branch]
  change (K*R^2/((r 0:ℝ)*N))*|(t:ℝ)|+
      (12*(K*R^2/N^2)+4*(K*R^2/N^2))*|G/r 0| * |(t:ℝ)|+
      (K*(r 0:ℝ)/N)*|q 0/r 0|+(1/2:ℝ)*|(t:ℝ)| * ((K*R^2/N^2)*|U|)+
      |q 0| * D |(n 0:ℝ)|+|q 1| * D |(n 1:ℝ)|+
      V |(n 0:ℝ)| * |(t:ℝ)/r 0|+V |(n 1:ℝ)| * |(t:ℝ)/r 1| ≤ _
  rw [abs_of_pos (show 0 < q 0 from (hqpos 0).1),
    abs_of_pos (show 0 < q 1 from (hqpos 1).1)]
  simp only [abs_div,abs_of_pos (hr' 0),abs_of_pos (hr' 1),hUabs,
    abs_of_pos (show 0 < q 0 from (hqpos 0).1)]
  rw [show (1/2:ℝ)*|(t:ℝ)| *((K*R^2/N^2)*(q 0/((r 0:ℝ)*|(t:ℝ)|))) =
    (K*R^2/(2*N^2))*(q 0/r 0) by field_simp [htpos.ne']]
  simp only [abs_div,abs_of_pos (hr' 0)] at hbudget
  convert hbudget using 1
  dsimp only [q,D,V]
  ring

                                                            
                                                
theorem physicalModelPhase_short_block_fourth_signed
    {σ δ T M N R Q K : ℝ} {u t : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (hsmall : K*R^2/N^2 ≤ 1/2)
    (hNR : N ≤ R^2) (hRN : R ≤ N) (hcube : N^3 ≤ M*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, 0 < r i) (ht : t ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1) :
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun i => round (x₁ i)-round (x₀ i)
    let q := fun i => (r i:ℝ)*u+s i*t
    let d₀ := fun i => iteratedDeriv 1 (f i) (round (x₀ i))
    let d₁ := fun i => iteratedDeriv 1 (f i) (round (x₁ i))
    let c := fun i => round ((r i:ℝ)*d₀ i)
    let θ := fun i => (r i:ℝ)*d₀ i-c i
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let C := (c 0:ℝ)*s 0/r 0-(c 1:ℝ)*s 1/r 1
    let C₂ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ
    let C₃ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ
    let κ := TaoTrudgianYang2025.modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let z := fun i => q i*d₁ i
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    (∀ i, |(n i:ℝ)| ≤ N) →
    (∀ i, 0 < q i ∧ q i ≤ Q) →
    (∀ i, |(t:ℝ)|/r i ≤ q i/R^2) →
    R^2/N ≤ (r 0:ℝ) →
    |μ 1*(r 1:ℝ)^3/(μ 0*(r 0:ℝ)^3)-1| ≤ K*R^2/N^2 →
    |(s 1:ℝ)/r 1-(s 0:ℝ)/r 0| ≤ K*R^4/((r 0:ℝ)^2*N^2) →
    |C-round C| ≤ K*R^2/((r 0:ℝ)*N) →
    |θ 0-θ 1| ≤ K*(r 0:ℝ)/N →
    |(z 0-z 1)-round (z 0-z 1)| ≤ (37*K/2+16*K*Cc+2*Ct+2*Cc)*Q/N := by
  let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
  let n := fun i => round (x₁ i)-round (x₀ i)
  let d₀ := fun i => iteratedDeriv 1 (f i) (round (x₀ i))
  let d₁ := fun i => iteratedDeriv 1 (f i) (round (x₁ i))
  let c := fun i => round ((r i:ℝ)*d₀ i)
  let C := (c 0:ℝ)*s 0/r 0-(c 1:ℝ)*s 1/r 1
  change _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _
  intro hbase hpoint hnN hqpos hgeom hminr hthird hfirst hsecond hfourth
  have hbound := physicalModelPhase_short_block_residual_difference_signed hσ hδ hF
    hT hM hN hR hscale hQ hK hsmall hNR hRN hcube hA hW hx₀ hx₁ hr ht hdet
    hbase hpoint hnN hqpos hgeom hminr hthird hfirst hsecond hfourth
  have hq (i) : r i*u+s i*t ≠ 0 := by
    have hh : (0:ℝ) < (r i:ℝ)*u+s i*t := (hqpos i).1
    exact_mod_cast hh.ne'
  exact (actual_derivative_base_centered_bound (fun i => (hr i).ne') hq hdet
    (d₀ := d₀) (d₁ := d₁) (n := n) (b := round C)).trans hbound

                                                                
                                                                
theorem physicalModelPhase_short_window_geometry_signed
    {σ δ T M N R A W x₀ x₁ e r v s u t : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx₀ : x₀ ∈ Set.Ioo 0 W) (hx₁ : x₁ ∈ Set.Ioo 0 W)
    (hr : 0 < r) (hq : 0 < r*u+s*t) (hdet : v*r-e*s=1)
    (hwidth : |x₁-x₀| ≤ N-1)
    (hphasewidth : (σ*(σ+1)+1)*|x₁-x₀| ≤ 2*N) :
    let f := heathBrownPhysicalPhase F T M A 1
    iteratedDeriv 2 f x₀/2=e/r →
    iteratedDeriv 2 f x₁/2=(e*u+v*t)/(r*u+s*t) →
    |(round x₁:ℝ)-(round x₀:ℝ)| ≤ N ∧ |t|/r ≤ (r*u+s*t)/R^2 := by
  let f := heathBrownPhysicalPhase F T M A 1
  let C := σ*(σ+1)+1
  change _ → _ → _
  intro hbase hpoint
  have hn : |(round x₁:ℝ)-(round x₀:ℝ)| ≤ N :=
    (rounded_displacement_bound x₁ x₀).trans (by linarith only [hwidth])
  refine ⟨hn,?_⟩
  have hdiff : iteratedDeriv 2 f x₁/2-iteratedDeriv 2 f x₀/2=t/(r*(r*u+s*t)) := by
    rw [hbase,hpoint]
    generalize hqdef : r*u+s*t=q at hq ⊢
    field_simp
    linear_combination t*hdet+e*hqdef
  have hc := physicalModelPhase_halfCurvature_lipschitz hσ hδ hF hT hM hA hW hx₀ hx₁
  change |iteratedDeriv 2 f x₁/2-iteratedDeriv 2 f x₀/2| ≤ C*T/(2*M^3)*|x₁-x₀| at hc
  rw [hdiff,abs_div,abs_of_pos (mul_pos hr hq)] at hc
  have hid : C*T/(2*M^3)*|x₁-x₀|=C*|x₁-x₀|/(2*N*R^2) := by
    rw [← hscale]
    field_simp
  change _ ≤ C*T/(2*M^3)*|x₁-x₀| at hc
  rw [hid] at hc
  have hmain : |t|/(r*(r*u+s*t)) ≤ 1/R^2 := by
    apply hc.trans
    apply (div_le_iff₀ (show 0 < 2*N*R^2 by positivity)).mpr
    rw [show (1/R^2)*(2*N*R^2)=2*N by field_simp]
    exact hphasewidth
  have hh := mul_le_mul_of_nonneg_right hmain hq.le
  generalize hqdef : r*u+s*t=q at hq hh ⊢
  convert hh using 1 <;> field_simp


                                                                   
                                                                  
                                                                   
                              
theorem physicalModelPhase_short_window_fourth
    {σ δ T M N R Q K : ℝ} {u t : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (hsmall : K*R^2/N^2 ≤ 1/2)
    (hNR : N ≤ R^2) (hRN : R ≤ N) (hcube : N^3 ≤ M*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, 0 < r i) (hdet : ∀ i, v i*r i-e i*s i=1) :
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let q := fun i => (r i:ℝ)*u+s i*t
    let d₀ := fun i => iteratedDeriv 1 (f i) (round (x₀ i))
    let d₁ := fun i => iteratedDeriv 1 (f i) (round (x₁ i))
    let c := fun i => round ((r i:ℝ)*d₀ i)
    let θ := fun i => (r i:ℝ)*d₀ i-c i
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let C := (c 0:ℝ)*s 0/r 0-(c 1:ℝ)*s 1/r 1
    let C₂ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ
    let C₃ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ
    let κ := TaoTrudgianYang2025.modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let z := fun i => q i*d₁ i
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    (∀ i, |x₁ i-x₀ i| ≤ N-1) →
    (∀ i, 0 < q i ∧ q i ≤ Q) →
    (∀ i, (σ*(σ+1)+1)*|x₁ i-x₀ i| ≤ 2*N) →
    R^2/N ≤ (r 0:ℝ) →
    |μ 1*(r 1:ℝ)^3/(μ 0*(r 0:ℝ)^3)-1| ≤ K*R^2/N^2 →
    |(s 1:ℝ)/r 1-(s 0:ℝ)/r 0| ≤ K*R^4/((r 0:ℝ)^2*N^2) →
    |C-round C| ≤ K*R^2/((r 0:ℝ)*N) →
    |θ 0-θ 1| ≤ K*(r 0:ℝ)/N →
    |(z 0-z 1)-round (z 0-z 1)| ≤ (37*K/2+16*K*Cc+2*Ct+2*Cc)*Q/N := by
  classical
  intro f q d₀ d₁ c θ μ C C₂ C₃ κ Ct Cc z
    hbase hpoint hwidth hqpos hphasewidth hminr hthird hfirst hsecond hfourth
  let n := fun i => round (x₁ i)-round (x₀ i)
  have hr' (i) : (0:ℝ) < r i := by exact_mod_cast hr i
  have hF₂ i := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 3) le_rfl
  have hdet' i : (v i:ℝ)*r i-e i*s i=1 := by exact_mod_cast hdet i
  have hgeo i := physicalModelPhase_short_window_geometry_signed hσ hδ (hF₂ i)
    hT hM hN hR hscale (hA i) (hW i)
    (show x₀ i∈Ioo 0 (W i) from ⟨by linarith [(hx₀ i).1],by linarith [(hx₀ i).2]⟩)
    (show x₁ i∈Ioo 0 (W i) from ⟨by linarith [(hx₁ i).1],by linarith [(hx₁ i).2]⟩)
    (hr' i) (hqpos i).1 (hdet' i) (hwidth i) (hphasewidth i) (hbase i) (hpoint i)
  have hn i : |(n i:ℝ)| ≤ N := by
    simpa only [n,Int.cast_sub] using (hgeo i).1
  by_cases ht : t ≠ 0
  · exact physicalModelPhase_short_block_fourth_signed hσ hδ hF hT hM hN hR
      hscale hQ hK hsmall hNR hRN hcube hA hW hx₀ hx₁ hr ht hdet
      hbase hpoint hn hqpos (fun i => (hgeo i).2) hminr hthird hfirst hsecond hfourth
  have htzero : t=0 := not_ne_iff.mp ht
  have hq₀ : 0 < (r 0:ℝ)*u := by
    simpa only [q,htzero,Int.cast_zero,mul_zero,add_zero] using (hqpos 0).1
  have hu : (0:ℝ) < u := (mul_pos_iff_of_pos_left (hr' 0)).mp hq₀
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hlevels i : iteratedDeriv 2 (f i) (x₁ i)/2=iteratedDeriv 2 (f i) (x₀ i)/2 := by
    rw [hpoint i,hbase i]
    simp only [q,htzero,Int.cast_zero,mul_zero,add_zero]
    field_simp
  have hsame i : x₁ i=x₀ i := by
    have hmono : StrictMonoOn (fun x => iteratedDeriv 2 (f i) x/2) (Ioo 0 (W i)) := by
      intro a ha b hb hab
      have hh := physicalModelPhase_halfCurvature_growth hσ hδ (hF₂ i)
        hT hM (hA i) (hW i) ha hb hab.le
      have hc : 0 < modelPhaseThirdLower σ*T/(2*M^3) := by positivity
      exact sub_pos.mp ((mul_pos hc (sub_pos.mpr hab)).trans_le hh)
    exact hmono.injOn
      ⟨by linarith [(hx₁ i).1],by linarith [(hx₁ i).2]⟩
      ⟨by linarith [(hx₀ i).1],by linarith [(hx₀ i).2]⟩ (hlevels i)
  have hz i : z i=(u:ℝ)*((r i:ℝ)*d₀ i) := by
    dsimp only [z,d₁,d₀]
    rw [hsame i]
    dsimp only [q]
    simp only [htzero,Int.cast_zero,mul_zero,add_zero]
    ring
  have hid : z 0-z 1-(u*(c 0-c 1):ℤ)=(u:ℝ)*(θ 0-θ 1) := by
    rw [hz 0,hz 1]
    dsimp only [θ]
    push_cast
    ring
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans
    (approximateModelPhase_iteratedDeriv_error (hF 0)
      (by norm_num : (3/2:ℝ)∈Ioo 1 2) 3 le_rfl)
  have hC₂ : 0 ≤ C₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ : 0 ≤ C₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hCt : 0 ≤ Ct := by dsimp only [Ct]; positivity
  have hCc : 0 ≤ Cc := by dsimp only [Cc]; positivity
  have hcoef : K ≤ 37*K/2+16*K*Cc+2*Ct+2*Cc := by
    nlinarith only [hK,hCt,hCc,mul_nonneg hK hCc]
  apply (round_le (z 0-z 1) (u*(c 0-c 1))).trans
  rw [hid,abs_mul,abs_of_pos hu]
  calc
    _ ≤ (u:ℝ)*(K*(r 0:ℝ)/N) := mul_le_mul_of_nonneg_left hfourth hu.le
    _ = K*q 0/N := by dsimp only [q]; simp only [htzero,Int.cast_zero,mul_zero,add_zero]; ring
    _ ≤ K*Q/N := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hqpos 0).2 hK) hN.le
    _ ≤ _ := by
      simpa only [mul_div_assoc] using
        mul_le_mul_of_nonneg_right hcoef (div_nonneg hQ hN.le)


                                                                 
                                                                    
                                                              
                                                                  
theorem physicalModelPhase_actual_fourier_signed_fourth
    {σ δ T M N R : ℝ} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let s := fun i => -vinv i-(q i:ℤ)*⌊-(vinv i:ℝ)/q i⌋
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    ∃ v : Fin 2 → ℤ, (∀ i, v i*(q i:ℤ)-(rat i).num*s i=1) ∧
      ∀ (x₁ : Fin 2 → ℝ) (u t : ℤ),
      (∀ i, x₁ i∈Ioo (1/2:ℝ) (W i-1/2)) →
      let qnew := fun i => (q i:ℝ)*u+s i*t
      let d₁ := fun i => deriv (f i) (round (x₁ i))
      let C₂ := modelPhaseJetCoefficient σ 2+δ
      let C₃ := modelPhaseJetCoefficient σ 3+δ
      let κ := modelPhaseThirdLower σ
      let Ct := C₂/2+5*C₃/12
      let Cc := C₂/κ+C₃/(2*κ)
      let z := fun i => qnew i*d₁ i
      let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
      (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=
        (((rat i).num:ℝ)*u+v i*t)/qnew i) →
      (∀ i, |x₁ i-x₀ i| ≤ N-1) →
      (∀ i, (σ*(σ+1)+1)*|x₁ i-x₀ i| ≤ 2*N) →
      (∀ i, 0 < qnew i ∧ qnew i ≤ Q) →
      |(z 0-z 1)-round (z 0-z 1)| ≤ Δ ∧
      (Δ < 1/2 →
        ∃ cnew∈minorArcCenterLabels (z 0) Δ,
          ∃ cnew₁∈minorArcCenterLabels (z 1) Δ,
          cnew=round (z 0) ∧ |(z 0-cnew)-(z 1-cnew₁)| ≤ Δ ∧
          ∃ p₀ p₁ : Fin 2, cnew=⌊z 0⌋+(p₀:ℕ) ∧ cnew₁=⌊z 1⌋+(p₁:ℕ)) := by
  classical
  intro f hlevel q mu ell b cround tau dual w radius hcolor hnear c J B s
    hsmall hNR hRN hcube hminscale
  obtain ⟨v,hv,hthird,hfirst,hsecond,hfourth⟩ :=
    physicalModelPhase_actual_fourier_conditions Q K₀ rat vinv parity
      hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv hlevel hcolor hnear
  refine ⟨v,hv,?_⟩
  intro x₁ u t hx₁ qnew d₁ C₂ C₃ κ Ct Cc z Δ hpoint hwidth hphasewidth hqbound
  have hQreal : (0:ℝ) < Q := by exact_mod_cast hQ
  have hr i : (0:ℤ) < (q i:ℤ) := by exact_mod_cast (rat i).pos
  have hQq : (Q:ℝ) ≤ 2*q 0 := by exact_mod_cast (hden 0).2
  have hminr : R^2/N ≤ (q 0:ℝ) := by
    apply (div_le_iff₀ hN).mpr
    have hh := mul_le_mul_of_nonneg_right hQq hN.le
    nlinarith only [hminscale,hh]
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hbase i : iteratedDeriv 2 (f i) (x₀ i)/2=((rat i).num:ℝ)/(q i:ℝ) := by
    rw [hlevel i,Rat.cast_def]
  have hh := physicalModelPhase_short_window_fourth
    (e:=fun i => (rat i).num) (r:=fun i => (q i:ℤ)) (v:=v) (s:=s)
    hσ hδ hF hT hM hN hR hscale hQreal.le hB hsmall hNR hRN hcube
    hA hW hx₀ hx₁ hr hv
    (by simpa only [Int.cast_natCast] using hbase)
    (by simpa only [Int.cast_natCast] using hpoint)
    hwidth
    (by simpa only [Int.cast_natCast] using hqbound)
    hphasewidth
    (by simpa only [Int.cast_natCast] using hminr)
    (by simpa only [Int.cast_natCast] using hthird)
    (by simpa only [Int.cast_natCast] using hfirst)
    (by simpa only [Int.cast_natCast,iteratedDeriv_one] using hsecond)
    (by simpa only [Int.cast_natCast,iteratedDeriv_one] using hfourth)
  simp only [Int.cast_natCast,iteratedDeriv_one] at hh
  refine ⟨hh,?_⟩
  intro hΔ
  obtain ⟨cnew,hcnew,cnew₁,hcnew₁,hround,hfour⟩ := exists_compatible_center_labels hΔ hh
  obtain ⟨p₀,hp₀⟩ := minorArcCenterLabels_fourier_parity hΔ hcnew
  obtain ⟨p₁,hp₁⟩ := minorArcCenterLabels_fourier_parity hΔ hcnew₁
  exact ⟨cnew,hcnew,cnew₁,hcnew₁,hround,hfour,p₀,p₁,hp₀,hp₁⟩


                                                              
                                                                   
                                                                  
                                                                
theorem physicalModelPhase_actual_fourier_matrix_fourth
    {σ δ T M N R : ℝ} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2) (Mat : Fin 4 → ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=(q 1:ℝ)/q 0 →
    ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    ∀ (x₁ : Fin 2 → ℝ) (a d : ℤ),
      let anew : Fin 2 → ℤ := ![a,Mat 0*a+Mat 1*d]
      let qnew : Fin 2 → ℤ := ![d,Mat 2*a+Mat 3*d]
      let C₂ := modelPhaseJetCoefficient σ 2+δ
      let C₃ := modelPhaseJetCoefficient σ 3+δ
      let κ := modelPhaseThirdLower σ
      let Ct := C₂/2+5*C₃/12
      let Cc := C₂/κ+C₃/(2*κ)
      let z := fun i => (qnew i:ℝ)*deriv (f i) (round (x₁ i))
      let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
      (∀ i, x₁ i∈Ioo (1/2:ℝ) (W i-1/2)) →
      (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=(anew i:ℝ)/qnew i) →
      (∀ i, |x₁ i-x₀ i| ≤ N-1) →
      (∀ i, (σ*(σ+1)+1)*|x₁ i-x₀ i| ≤ 2*N) →
      (∀ i, 0 < (qnew i:ℝ) ∧ (qnew i:ℝ) ≤ Q) →
      |(z 0-z 1)-round (z 0-z 1)| ≤ Δ ∧
      (Δ < 1/2 →
        ∃ cnew∈minorArcCenterLabels (z 0) Δ,
          ∃ cnew₁∈minorArcCenterLabels (z 1) Δ,
          cnew=round (z 0) ∧ |(z 0-cnew)-(z 1-cnew₁)| ≤ Δ ∧
          ∃ p₀ p₁ : Fin 2, cnew=⌊z 0⌋+(p₀:ℕ) ∧ cnew₁=⌊z 1⌋+(p₁:ℕ)) := by
  classical
  intro f hlevel q mu ell b cround tau dual w radius hcolor hnear c J B
    hsmall hNR hRN hcube hminscale hMatdet hMatt hMatmap hMatgamma
  let s := fun i => -vinv i-(q i:ℤ)*⌊-(vinv i:ℝ)/q i⌋
  obtain ⟨v,hv,hprop⟩ := physicalModelPhase_actual_fourier_signed_fourth
    Q K₀ rat vinv parity hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀
    hden hinv hlevel hcolor hnear hsmall hNR hRN hcube hminscale
  let qi := fun i => (q i:ℤ)
  let ei := fun i => (rat i).num
  have hqi i : 0 < qi i := by
    change (0:ℤ) < (rat i).den
    exact_mod_cast (rat i).pos
  have hKi : (1:ℝ) ≤ K₀ := by exact_mod_cast (NeZero.one_le : 1 ≤ K₀)
  have hband i : (qi i:ℝ) ≤ Q ∧ (Q:ℝ) ≤ 2*qi i := by
    change ((rat i).den:ℝ) ≤ Q ∧ (Q:ℝ) ≤ 2*(rat i).den
    exact_mod_cast hden i
  have ht' : (Mat 2:ℝ)*((ei 0:ℝ)/qi 0)+Mat 3=(qi 1:ℝ)/qi 0 := by
    simpa only [ei,qi,q,Int.cast_natCast,Rat.cast_def] using hMatt
  have hm' : ((Mat 0:ℝ)*((ei 0:ℝ)/qi 0)+Mat 1)/
      ((Mat 2:ℝ)*((ei 0:ℝ)/qi 0)+Mat 3)=(ei 1:ℝ)/qi 1 := by
    simpa only [ei,qi,q,Int.cast_natCast,Rat.cast_def] using hMatmap
  have hnear' : |Int.fract (-(vinv 0:ℝ)/qi 0)-
      Int.fract (-(vinv 1:ℝ)/qi 1)| ≤ 1/(6*(K₀:ℝ)^2) := by
    have hh := hnear (1:Fin 4)
    change |Int.fract (-(vinv 0:ℝ)/q 0)-
      Int.fract (-(vinv 1:ℝ)/q 1)| ≤ 2*(1/(12*(K₀:ℝ)^2)) at hh
    convert hh using 1
    ring
  obtain ⟨vc,hvc,_hs,htransport⟩ :=
    fourier_matrix_normalized_chart_transport qi ei vinv Mat hqi hKi hband hinv
      hMatdet ht' hm' hMatgamma hnear'
  have heqv : vc=v := by
    funext i
    have hc : vc i*(q i:ℤ)-(rat i).num*s i=1 := by
      simpa only [qi,ei,Int.cast_natCast] using hvc i
    have hd : v i*(q i:ℤ)-(rat i).num*s i=1 := hv i
    have hh : (vc i-v i)*(q i:ℤ)=0 := by nlinarith only [hc,hd]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right (hqi i).ne')
  subst vc
  simp only [qi,ei,Int.cast_natCast] at htransport
  intro x₁ a d anew qnew C₂ C₃ κ Ct Cc z Δ hx₁ hpoint hwidth hphasewidth hqbound
  let u := v 0*d-s 0*a
  let t := (q 0:ℤ)*a-(rat 0).num*d
  have he₀ : (rat 0).num*u+v 0*t=a := by
    dsimp only [u,t]
    linear_combination a*hv 0
  have hq₀ : (q 0:ℤ)*u+s 0*t=d := by
    dsimp only [u,t]
    linear_combination d*hv 0
  have htr := htransport u t
  change Mat 0*((rat 0).num*u+v 0*t)+Mat 1*((q 0:ℤ)*u+s 0*t)=
      (rat 1).num*u+v 1*t ∧
    Mat 2*((rat 0).num*u+v 0*t)+Mat 3*((q 0:ℤ)*u+s 0*t)=
      (q 1:ℤ)*u+s 1*t at htr
  rw [he₀,hq₀] at htr
  have he i : (rat i).num*u+v i*t=anew i := by
    fin_cases i
    · exact he₀
    · exact htr.1.symm
  have hq i : (q i:ℤ)*u+s i*t=qnew i := by
    fin_cases i
    · exact hq₀
    · exact htr.2.symm
  have heR i : ((rat i).num:ℝ)*u+v i*t=(anew i:ℝ) := by
    simpa only [Int.cast_add,Int.cast_mul] using congrArg (fun z : ℤ => (z:ℝ)) (he i)
  have hqR i : (q i:ℝ)*u+s i*t=(qnew i:ℝ) := by
    simpa only [Int.cast_add,Int.cast_mul,Int.cast_natCast] using
      congrArg (fun z : ℤ => (z:ℝ)) (hq i)
  dsimp only [q,s] at hqR
  have hroot' i : iteratedDeriv 2 (f i) (x₁ i)/2=
      (((rat i).num:ℝ)*u+v i*t)/((q i:ℝ)*u+s i*t) := by
    rw [heR i,show (q i:ℝ)*u+s i*t=(qnew i:ℝ) from hqR i]
    exact hpoint i
  have hbound' i : 0 < (q i:ℝ)*u+s i*t ∧ (q i:ℝ)*u+s i*t ≤ Q := by
    rw [show (q i:ℝ)*u+s i*t=(qnew i:ℝ) from hqR i]
    exact hqbound i
  have hh := hprop x₁ u t hx₁
    hroot' hwidth hphasewidth hbound'
  simpa only [hqR] using hh

                                                                  
                                                                   
                                                                        
                                                    
theorem physicalModelPhase_matrix_window_roots
    {σ δ T M N R : ℝ} (Mat : Fin 4 → ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hRN : R ≤ N) (hscale : T*N*R^2=M^3)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hdet : Mat 0*Mat 3-Mat 1*Mat 2=1)
    (hgamma : |(Mat 2:ℝ)| ≤ R^4/(6*N^2)) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let C := σ*(σ+1)+1
    let H := N/(C+2)
    let ε := modelPhaseThirdLower σ/(16*(C+2)*R^2)
    let y₀ := iteratedDeriv 2 (f 0) (x₀ 0)/2
    let target := fun y => (![y,((Mat 0:ℝ)*y+Mat 1)/((Mat 2:ℝ)*y+Mat 3)] : Fin 2 → ℝ)
    (∀ i, x₀ i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1/2:ℝ) ≤ (Mat 2:ℝ)*y₀+Mat 3 →
    (Mat 2:ℝ)*y₀+Mat 3 ≤ 2 →
    target y₀ 1=iteratedDeriv 2 (f 1) (x₀ 1)/2 →
    0 < ε ∧ ∃ ρ : ℝ → Fin 2 → ℝ, ∀ y, |y-y₀| ≤ ε →
      ((1/4:ℝ) ≤ (Mat 2:ℝ)*y+Mat 3 ∧ (Mat 2:ℝ)*y+Mat 3 ≤ 3) ∧
      ∀ i, ρ y i∈Icc (x₀ i-H) (x₀ i+H) ∧
        ρ y i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (ρ y i)/2=target y i ∧
        |ρ y i-x₀ i| ≤ H ∧
        |(round (ρ y i):ℝ)-(round (x₀ i):ℝ)| ≤ H+1 := by
  classical
  intro f C H ε y₀ target hL hU htlo hthi hmap
  let κ := modelPhaseThirdLower σ
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hC : 0 < C := by dsimp only [C]; positivity
  have hC₂ : 0 < C+2 := by positivity
  have hH : 0 < H := by dsimp only [H]; positivity
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hκC : κ ≤ C := by
    have hh := approximateModelPhase_thirdDeriv_bounds hσ hδ (hF 0)
      (by norm_num : (3/2:ℝ)∈Ioo 1 2)
    exact hh.1.trans hh.2
  have hratio : κ/(C+2) ≤ 1 := (div_le_one hC₂).mpr (by linarith only [hκC])
  have hRN₂ : R^2/N^2 ≤ 1 := (div_le_one (sq_pos_of_pos hN)).mpr
    (pow_le_pow_left₀ hR.le hRN 2)
  have hsmall : |(Mat 2:ℝ)| *ε ≤ 1/4 := by
    calc
      _ ≤ (R^4/(6*N^2))*ε := mul_le_mul_of_nonneg_right hgamma hε.le
      _ = (κ/(C+2))*(R^2/N^2)/96 := by dsimp only [ε,κ]; field_simp; ring
      _ ≤ 1*1/96 := by gcongr
      _ ≤ _ := by norm_num
  have hdetR : (Mat 0:ℝ)*Mat 3-(Mat 1:ℝ)*Mat 2=1 := by exact_mod_cast hdet
  have htpos : 0 < (Mat 2:ℝ)*y₀+Mat 3 := by linarith only [htlo]
  have hvariation (y : ℝ) (hy : |y-y₀| ≤ ε) :
      ((1/4:ℝ) ≤ (Mat 2:ℝ)*y+Mat 3 ∧ (Mat 2:ℝ)*y+Mat 3 ≤ 3) ∧
      ∀ i, |target y i-iteratedDeriv 2 (f i) (x₀ i)/2| ≤ 8*ε := by
    have hd : |((Mat 2:ℝ)*y+Mat 3)-((Mat 2:ℝ)*y₀+Mat 3)| ≤ 1/4 := by
      calc
        _ = |(Mat 2:ℝ)| *|y-y₀| := by rw [←abs_mul]; congr 1; ring
        _ ≤ |(Mat 2:ℝ)| *ε := mul_le_mul_of_nonneg_left hy (abs_nonneg _)
        _ ≤ _ := hsmall
    have hdle := abs_le.mp hd
    have hlo : (1/4:ℝ) ≤ (Mat 2:ℝ)*y+Mat 3 := by linarith only [htlo,hdle.1]
    have hhi : (Mat 2:ℝ)*y+Mat 3 ≤ 3 := by linarith only [hthi,hdle.2]
    have hypos : 0 < (Mat 2:ℝ)*y+Mat 3 := by linarith only [hlo]
    refine ⟨⟨hlo,hhi⟩,?_⟩
    intro i
    fin_cases i
    · change |y-y₀| ≤ 8*ε
      linarith only [hy,hε]
    · change |((Mat 0:ℝ)*y+Mat 1)/((Mat 2:ℝ)*y+Mat 3)-
        iteratedDeriv 2 (f 1) (x₀ 1)/2| ≤ 8*ε
      rw [←hmap]
      have hid : ((Mat 0:ℝ)*y+Mat 1)/((Mat 2:ℝ)*y+Mat 3)-
          ((Mat 0:ℝ)*y₀+Mat 1)/((Mat 2:ℝ)*y₀+Mat 3) =
          (y-y₀)/(((Mat 2:ℝ)*y+Mat 3)*((Mat 2:ℝ)*y₀+Mat 3)) := by
        rw [div_sub_div _ _ hypos.ne' htpos.ne']
        congr 1
        linear_combination (y-y₀)*hdetR
      change |((Mat 0:ℝ)*y+Mat 1)/((Mat 2:ℝ)*y+Mat 3)-
        ((Mat 0:ℝ)*y₀+Mat 1)/((Mat 2:ℝ)*y₀+Mat 3)| ≤ _
      rw [hid,abs_div,abs_of_pos (mul_pos hypos htpos)]
      have hp : (1/8:ℝ) ≤ ((Mat 2:ℝ)*y+Mat 3)*((Mat 2:ℝ)*y₀+Mat 3) := by
        have hh := mul_le_mul hlo htlo (by norm_num : (0:ℝ) ≤ 1/2) hypos.le
        norm_num at hh
        exact hh
      calc
        _ ≤ |y-y₀|/(1/8:ℝ) := div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hp
        _ ≤ 8*ε := by norm_num; linarith only [hy]
  have hrate : modelPhaseThirdLower σ*T/(2*M^3)*H=8*ε := by
    rw [←hscale]
    dsimp only [H,ε]
    field_simp
    ring
  have hlower i : 8*ε ≤ iteratedDeriv 2 (f i) (x₀ i)/2-
      iteratedDeriv 2 (f i) (x₀ i-H)/2 := by
    have hh := physicalModelPhase_halfCurvature_growth hσ hδ (hF i) hT hM (hA i) (hW i)
      (show x₀ i-H∈Ioo 0 (W i) from ⟨by linarith [(hL i).1],by linarith [(hL i).2]⟩)
      (show x₀ i∈Ioo 0 (W i) from ⟨by linarith [(hx₀ i).1],by linarith [(hx₀ i).2]⟩)
      (by linarith only [hH])
    rw [show x₀ i-(x₀ i-H)=H by ring,hrate] at hh
    exact hh
  have hupper i : 8*ε ≤ iteratedDeriv 2 (f i) (x₀ i+H)/2-
      iteratedDeriv 2 (f i) (x₀ i)/2 := by
    have hh := physicalModelPhase_halfCurvature_growth hσ hδ (hF i) hT hM (hA i) (hW i)
      (show x₀ i∈Ioo 0 (W i) from ⟨by linarith [(hx₀ i).1],by linarith [(hx₀ i).2]⟩)
      (show x₀ i+H∈Ioo 0 (W i) from ⟨by linarith [(hU i).1],by linarith [(hU i).2]⟩)
      (by linarith only [hH])
    rw [add_sub_cancel_left,hrate] at hh
    exact hh
  have hex (y : ℝ) : ∃ ξ : Fin 2 → ℝ, |y-y₀| ≤ ε →
      ∀ i, ξ i∈Icc (x₀ i-H) (x₀ i+H) ∧
        ξ i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (ξ i)/2=target y i ∧
        |ξ i-x₀ i| ≤ H ∧
        |(round (ξ i):ℝ)-(round (x₀ i):ℝ)| ≤ H+1 := by
    by_cases hy : |y-y₀| ≤ ε
    · have hcoverage i : target y i∈uIcc
          (iteratedDeriv 2 (f i) (x₀ i-H)/2) (iteratedDeriv 2 (f i) (x₀ i+H)/2) := by
        apply Icc_subset_uIcc
        have hh := abs_le.mp ((hvariation y hy).2 i)
        exact ⟨by linarith [hlower i],by linarith [hupper i]⟩
      have hexi i := physicalModelPhase_exists_rounded_halfCurvature_center hσ.le (hF i)
        hT hM (hA i) (hW i) (hL i) (hU i) (hcoverage i)
      choose ξ hξ hroot _hround _herr using hexi
      refine ⟨ξ,fun _ i => ?_⟩
      have hi : ξ i∈Icc (x₀ i-H) (x₀ i+H) := by
        simpa only [uIcc_of_le (by linarith only [hH] : x₀ i-H ≤ x₀ i+H)] using hξ i
      have hbuf : ξ i∈Ioo (1/2:ℝ) (W i-1/2) :=
        ⟨(hL i).1.trans_le hi.1,hi.2.trans_lt (hU i).2⟩
      have hdist : |ξ i-x₀ i| ≤ H := abs_le.mpr ⟨by linarith [hi.1],by linarith [hi.2]⟩
      exact ⟨hi,hbuf,hroot i,hdist,
        (rounded_displacement_bound (ξ i) (x₀ i)).trans (add_le_add hdist le_rfl)⟩
    · exact ⟨x₀,fun h => False.elim (hy h)⟩
  choose ρ hρ using hex
  exact ⟨hε,ρ,fun y hy => ⟨(hvariation y hy).1,hρ y hy⟩⟩


                                                                    
                                                                  
                                                                   
                                                           
theorem physicalModelPhase_actual_fourier_matrix_root_fourth
    {σ δ T M N R : ℝ} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2) (Mat : Fin 4 → ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=(q 1:ℝ)/q 0 →
    ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let C := σ*(σ+1)+1
    let H := N/(C+2)
    let ε := modelPhaseThirdLower σ/(16*(C+2)*R^2)
    2 ≤ N →
    (∀ i, x₀ i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    0 < ε ∧ ∃ ρ : ℝ → Fin 2 → ℝ, ∀ (a d : ℤ),
      0 < (d:ℝ) → (d:ℝ) ≤ (Q:ℝ)/3 → |(a:ℝ)/d-(rat 0:ℝ)| ≤ ε →
      let x₁ := ρ ((a:ℝ)/d)
      let anew : Fin 2 → ℤ := ![a,Mat 0*a+Mat 1*d]
      let qnew : Fin 2 → ℤ := ![d,Mat 2*a+Mat 3*d]
      let C₂ := modelPhaseJetCoefficient σ 2+δ
      let C₃ := modelPhaseJetCoefficient σ 3+δ
      let κ := modelPhaseThirdLower σ
      let Ct := C₂/2+5*C₃/12
      let Cc := C₂/κ+C₃/(2*κ)
      let z := fun i => (qnew i:ℝ)*deriv (f i) (round (x₁ i))
      let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
      (∀ i, x₁ i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (x₁ i)/2=(anew i:ℝ)/qnew i ∧
        |x₁ i-x₀ i| ≤ H ∧ 0 < (qnew i:ℝ) ∧ (qnew i:ℝ) ≤ Q) ∧
      |(z 0-z 1)-round (z 0-z 1)| ≤ Δ ∧
      (Δ < 1/2 →
        ∃ cnew∈minorArcCenterLabels (z 0) Δ,
          ∃ cnew₁∈minorArcCenterLabels (z 1) Δ,
          cnew=round (z 0) ∧ |(z 0-cnew)-(z 1-cnew₁)| ≤ Δ ∧
          ∃ p₀ p₁ : Fin 2, cnew=⌊z 0⌋+(p₀:ℕ) ∧ cnew₁=⌊z 1⌋+(p₁:ℕ)) := by
  classical
  intro f hlevel q mu ell b cround tau dual w radius hcolor hnear c J B
    hsmall hNR hRN hcube hminscale hMatdet hMatt hMatmap hMatgamma
    C H ε hNtwo hL hU
  have hF₂ i := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 3) le_rfl
  have hK : (0:ℝ) < K₀ := by exact_mod_cast (NeZero.pos K₀)
  have hQreal : (0:ℝ) < Q := by exact_mod_cast hQ
  have hgamma : |(Mat 2:ℝ)| ≤ R^4/(6*N^2) := by
    apply hMatgamma.trans
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh := pow_le_pow_left₀ (mul_nonneg hQreal.le hN.le) hmesh 2
    nlinarith only [hh]
  have hqpos i : (0:ℝ) < q i := by exact_mod_cast (rat i).pos
  have hband i : (q i:ℝ) ≤ Q ∧ (Q:ℝ) ≤ 2*q i := by
    exact_mod_cast hden i
  have htlo : (1/2:ℝ) ≤ (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3 := by
    rw [hMatt]
    apply (le_div_iff₀ (hqpos 0)).mpr
    linarith only [(hband 0).1,(hband 1).2]
  have hthi : (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3 ≤ 2 := by
    rw [hMatt]
    apply (div_le_iff₀ (hqpos 0)).mpr
    linarith only [(hband 1).1,(hband 0).2]
  have hinit i : iteratedDeriv 2 (heathBrownPhysicalPhase (F i) T M (A i) 1) (x₀ i)/2=
      (rat i:ℝ) := hlevel i
  have htlo' : (1/2:ℝ) ≤ (Mat 2:ℝ)*(iteratedDeriv 2 (f 0) (x₀ 0)/2)+Mat 3 := by
    rw [hlevel 0]; exact htlo
  have hthi' : (Mat 2:ℝ)*(iteratedDeriv 2 (f 0) (x₀ 0)/2)+Mat 3 ≤ 2 := by
    rw [hlevel 0]; exact hthi
  have hmap' : ((Mat 0:ℝ)*(iteratedDeriv 2 (f 0) (x₀ 0)/2)+Mat 1)/
      ((Mat 2:ℝ)*(iteratedDeriv 2 (f 0) (x₀ 0)/2)+Mat 3)=
      iteratedDeriv 2 (f 1) (x₀ 1)/2 := by
    rw [hlevel 0,hlevel 1]; exact hMatmap
  obtain ⟨hε,ρ,hρ⟩ := physicalModelPhase_matrix_window_roots Mat
    hσ hδ hF₂ hT hM hN hR hRN hscale hA hW hx₀ hMatdet hgamma
    hL hU htlo' hthi' hmap'
  simp only [hinit 0] at hρ
  have hC : 0 < C := by dsimp only [C]; positivity
  have hC₂ : 0 < C+2 := by positivity
  have hH : 0 < H := by dsimp only [H]; positivity
  have hHsmall : H ≤ N-1 := by
    have hh : H ≤ N/2 := by
      exact div_le_div_of_nonneg_left hN.le (by norm_num) (by linarith only [hC])
    linarith only [hh,hNtwo]
  have hCH : C*H ≤ 2*N := by
    have hh : C/(C+2) ≤ 1 := (div_le_one hC₂).mpr (by linarith)
    have hh' := mul_le_mul_of_nonneg_right hh hN.le
    calc
      C*H = C/(C+2)*N := by dsimp only [H]; ring
      _ ≤ 1*N := hh'
      _ ≤ 2*N := by linarith only [hN]
  refine ⟨hε,ρ,?_⟩
  intro a d hd hdQ hy x₁ anew qnew C₂ C₃ κ Ct Cc z Δ
  have hr := hρ ((a:ℝ)/d) hy
  let y : ℝ := (a:ℝ)/d
  have hqd : (qnew 1:ℝ)=((Mat 2:ℝ)*y+Mat 3)*(d:ℝ) := by
    dsimp only [qnew,y]
    simp only [Fin.isValue,Matrix.cons_val_one,Matrix.cons_val_zero,
      Int.cast_add,Int.cast_mul]
    field_simp
  have had : (anew 1:ℝ)=((Mat 0:ℝ)*y+Mat 1)*(d:ℝ) := by
    dsimp only [anew,y]
    simp only [Fin.isValue,Matrix.cons_val_one,Matrix.cons_val_zero,
      Int.cast_add,Int.cast_mul]
    field_simp
  have hb i : 0 < (qnew i:ℝ) ∧ (qnew i:ℝ) ≤ Q := by
    fin_cases i
    · change 0 < (d:ℝ) ∧ (d:ℝ) ≤ Q
      exact ⟨hd,by linarith only [hdQ,hQreal]⟩
    · change 0 < (qnew 1:ℝ) ∧ (qnew 1:ℝ) ≤ Q
      rw [hqd]
      have hhlo := mul_le_mul_of_nonneg_right hr.1.1 hd.le
      have hhhi := mul_le_mul_of_nonneg_right hr.1.2 hd.le
      exact ⟨by nlinarith only [hhlo,hd],by nlinarith only [hhhi,hdQ]⟩
  have hx₁ i : x₁ i∈Ioo (1/2:ℝ) (W i-1/2) := (hr.2 i).2.1
  have hdist i : |x₁ i-x₀ i| ≤ H := (hr.2 i).2.2.2.1
  have hroot i : iteratedDeriv 2 (f i) (x₁ i)/2=(anew i:ℝ)/qnew i := by
    have hh := (hr.2 i).2.2.1
    change iteratedDeriv 2 (f i) (x₁ i)/2=
      (![y,((Mat 0:ℝ)*y+Mat 1)/((Mat 2:ℝ)*y+Mat 3)] : Fin 2 → ℝ) i at hh
    rw [hh]
    fin_cases i
    · rfl
    · change ((Mat 0:ℝ)*y+Mat 1)/((Mat 2:ℝ)*y+Mat 3)=(anew 1:ℝ)/qnew 1
      rw [had,hqd,mul_div_mul_right _ _ hd.ne']
  have hwidth i : |x₁ i-x₀ i| ≤ N-1 := (hdist i).trans hHsmall
  have hphasewidth i : (σ*(σ+1)+1)*|x₁ i-x₀ i| ≤ 2*N :=
    (mul_le_mul_of_nonneg_left (hdist i) hC.le).trans hCH
  have hh := physicalModelPhase_actual_fourier_matrix_fourth Q K₀ rat vinv parity Mat
    hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv hlevel
    hcolor hnear hsmall hNR hRN hcube hminscale hMatdet hMatt hMatmap hMatgamma
    x₁ a d hx₁ hroot hwidth hphasewidth hb
  exact ⟨fun i => ⟨hx₁ i,hroot i,hdist i,hb i⟩,hh⟩

                                                                    
                                                                        
                                                                      
                                                                       
theorem physicalModelPhase_matrix_long_window_roots
    {σ δ T M N R L : ℝ} (Mat : Fin 4 → ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hLpos : 0 < L) (hscale : T*N*R^2=M^3)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hdet : Mat 0*Mat 3-Mat 1*Mat 2=1)
    (hgamma : |(Mat 2:ℝ)| ≤ R^4/(6*N^2))
    (hwindow : modelPhaseThirdLower σ*L*R^2 ≤ 24*N^2) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let H := L*N
    let ε := modelPhaseThirdLower σ*L/(16*R^2)
    let y₀ := iteratedDeriv 2 (f 0) (x₀ 0)/2
    let target := fun y => (![y,((Mat 0:ℝ)*y+Mat 1)/((Mat 2:ℝ)*y+Mat 3)] : Fin 2 → ℝ)
    (∀ i, x₀ i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1/2:ℝ) ≤ (Mat 2:ℝ)*y₀+Mat 3 →
    (Mat 2:ℝ)*y₀+Mat 3 ≤ 2 →
    target y₀ 1=iteratedDeriv 2 (f 1) (x₀ 1)/2 →
    0 < ε ∧ ∃ ρ : ℝ → Fin 2 → ℝ, ∀ y, |y-y₀| ≤ ε →
      ((1/4:ℝ) ≤ (Mat 2:ℝ)*y+Mat 3 ∧ (Mat 2:ℝ)*y+Mat 3 ≤ 3) ∧
      ∀ i, ρ y i∈Icc (x₀ i-H) (x₀ i+H) ∧
        ρ y i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (ρ y i)/2=target y i ∧
        |ρ y i-x₀ i| ≤ H ∧
        |(round (ρ y i):ℝ)-(round (x₀ i):ℝ)| ≤ H+1 := by
  classical
  intro f H ε y₀ target hL hU htlo hthi hmap
  let κ := modelPhaseThirdLower σ
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hH : 0 < H := by dsimp only [H]; positivity
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hsmall : |(Mat 2:ℝ)| *ε ≤ 1/4 := by
    calc
      _ ≤ (R^4/(6*N^2))*ε := mul_le_mul_of_nonneg_right hgamma hε.le
      _ = κ*L*R^2/(96*N^2) := by dsimp only [ε,κ]; field_simp; ring
      _ ≤ 1/4 := (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hwindow])
  have hdetR : (Mat 0:ℝ)*Mat 3-(Mat 1:ℝ)*Mat 2=1 := by exact_mod_cast hdet
  have htpos : 0 < (Mat 2:ℝ)*y₀+Mat 3 := by linarith only [htlo]
  have hvariation (y : ℝ) (hy : |y-y₀| ≤ ε) :
      ((1/4:ℝ) ≤ (Mat 2:ℝ)*y+Mat 3 ∧ (Mat 2:ℝ)*y+Mat 3 ≤ 3) ∧
      ∀ i, |target y i-iteratedDeriv 2 (f i) (x₀ i)/2| ≤ 8*ε := by
    have hd : |((Mat 2:ℝ)*y+Mat 3)-((Mat 2:ℝ)*y₀+Mat 3)| ≤ 1/4 := by
      calc
        _ = |(Mat 2:ℝ)| *|y-y₀| := by rw [←abs_mul]; congr 1; ring
        _ ≤ |(Mat 2:ℝ)| *ε := mul_le_mul_of_nonneg_left hy (abs_nonneg _)
        _ ≤ _ := hsmall
    have hdle := abs_le.mp hd
    have hlo : (1/4:ℝ) ≤ (Mat 2:ℝ)*y+Mat 3 := by linarith only [htlo,hdle.1]
    have hhi : (Mat 2:ℝ)*y+Mat 3 ≤ 3 := by linarith only [hthi,hdle.2]
    have hypos : 0 < (Mat 2:ℝ)*y+Mat 3 := by linarith only [hlo]
    refine ⟨⟨hlo,hhi⟩,?_⟩
    intro i
    fin_cases i
    · change |y-y₀| ≤ 8*ε
      linarith only [hy,hε]
    · change |((Mat 0:ℝ)*y+Mat 1)/((Mat 2:ℝ)*y+Mat 3)-
        iteratedDeriv 2 (f 1) (x₀ 1)/2| ≤ 8*ε
      rw [←hmap]
      have hid : ((Mat 0:ℝ)*y+Mat 1)/((Mat 2:ℝ)*y+Mat 3)-
          ((Mat 0:ℝ)*y₀+Mat 1)/((Mat 2:ℝ)*y₀+Mat 3) =
          (y-y₀)/(((Mat 2:ℝ)*y+Mat 3)*((Mat 2:ℝ)*y₀+Mat 3)) := by
        rw [div_sub_div _ _ hypos.ne' htpos.ne']
        congr 1
        linear_combination (y-y₀)*hdetR
      change |((Mat 0:ℝ)*y+Mat 1)/((Mat 2:ℝ)*y+Mat 3)-
        ((Mat 0:ℝ)*y₀+Mat 1)/((Mat 2:ℝ)*y₀+Mat 3)| ≤ _
      rw [hid,abs_div,abs_of_pos (mul_pos hypos htpos)]
      have hp : (1/8:ℝ) ≤ ((Mat 2:ℝ)*y+Mat 3)*((Mat 2:ℝ)*y₀+Mat 3) := by
        have hh := mul_le_mul hlo htlo (by norm_num : (0:ℝ) ≤ 1/2) hypos.le
        norm_num at hh
        exact hh
      calc
        _ ≤ |y-y₀|/(1/8:ℝ) := div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hp
        _ ≤ 8*ε := by norm_num; linarith only [hy]
  have hrate : modelPhaseThirdLower σ*T/(2*M^3)*H=8*ε := by
    rw [←hscale]
    dsimp only [H,ε]
    field_simp
    ring
  have hlower i : 8*ε ≤ iteratedDeriv 2 (f i) (x₀ i)/2-
      iteratedDeriv 2 (f i) (x₀ i-H)/2 := by
    have hh := physicalModelPhase_halfCurvature_growth hσ hδ (hF i) hT hM (hA i) (hW i)
      (show x₀ i-H∈Ioo 0 (W i) from ⟨by linarith [(hL i).1],by linarith [(hL i).2]⟩)
      (show x₀ i∈Ioo 0 (W i) from ⟨by linarith [(hx₀ i).1],by linarith [(hx₀ i).2]⟩)
      (by linarith only [hH])
    rw [show x₀ i-(x₀ i-H)=H by ring,hrate] at hh
    exact hh
  have hupper i : 8*ε ≤ iteratedDeriv 2 (f i) (x₀ i+H)/2-
      iteratedDeriv 2 (f i) (x₀ i)/2 := by
    have hh := physicalModelPhase_halfCurvature_growth hσ hδ (hF i) hT hM (hA i) (hW i)
      (show x₀ i∈Ioo 0 (W i) from ⟨by linarith [(hx₀ i).1],by linarith [(hx₀ i).2]⟩)
      (show x₀ i+H∈Ioo 0 (W i) from ⟨by linarith [(hU i).1],by linarith [(hU i).2]⟩)
      (by linarith only [hH])
    rw [add_sub_cancel_left,hrate] at hh
    exact hh
  have hex (y : ℝ) : ∃ ξ : Fin 2 → ℝ, |y-y₀| ≤ ε →
      ∀ i, ξ i∈Icc (x₀ i-H) (x₀ i+H) ∧
        ξ i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (ξ i)/2=target y i ∧
        |ξ i-x₀ i| ≤ H ∧
        |(round (ξ i):ℝ)-(round (x₀ i):ℝ)| ≤ H+1 := by
    by_cases hy : |y-y₀| ≤ ε
    · have hcoverage i : target y i∈uIcc
          (iteratedDeriv 2 (f i) (x₀ i-H)/2) (iteratedDeriv 2 (f i) (x₀ i+H)/2) := by
        apply Icc_subset_uIcc
        have hh := abs_le.mp ((hvariation y hy).2 i)
        exact ⟨by linarith [hlower i],by linarith [hupper i]⟩
      have hexi i := physicalModelPhase_exists_rounded_halfCurvature_center hσ.le (hF i)
        hT hM (hA i) (hW i) (hL i) (hU i) (hcoverage i)
      choose ξ hξ hroot _hround _herr using hexi
      refine ⟨ξ,fun _ i => ?_⟩
      have hi : ξ i∈Icc (x₀ i-H) (x₀ i+H) := by
        simpa only [uIcc_of_le (by linarith only [hH] : x₀ i-H ≤ x₀ i+H)] using hξ i
      have hbuf : ξ i∈Ioo (1/2:ℝ) (W i-1/2) :=
        ⟨(hL i).1.trans_le hi.1,hi.2.trans_lt (hU i).2⟩
      have hdist : |ξ i-x₀ i| ≤ H := abs_le.mpr ⟨by linarith [hi.1],by linarith [hi.2]⟩
      exact ⟨hi,hbuf,hroot i,hdist,
        (rounded_displacement_bound (ξ i) (x₀ i)).trans (add_le_add hdist le_rfl)⟩
    · exact ⟨x₀,fun h => False.elim (hy h)⟩
  choose ρ hρ using hex
  exact ⟨hε,ρ,fun y hy => ⟨(hvariation y hy).1,hρ y hy⟩⟩


                                                                  
                                                                     
                                                               
                                                   
theorem physicalModelPhase_actual_matrix_reference_roots
    {σ δ T M N R L : ℝ} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (Mat : Fin 4 → ℤ) (e r : ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hLpos : 0 < L) (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hdet : Mat 0*Mat 3-Mat 1*Mat 2=1)
    (hgamma : |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2))
    (hwindow : modelPhaseThirdLower σ*L*R^2 ≤ 24*N^2)
    (hr : 0 < r) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=((rat 1).den:ℝ)/(rat 0).den →
    ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ) →
    (∀ i, x₀ i-L*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+L*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    |(e:ℝ)/r-(rat 0:ℝ)| ≤ modelPhaseThirdLower σ*L/(16*R^2) →
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    ∃ xref : Fin 2 → ℝ, ∀ i,
      0 < rp i ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
      iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
      |xref i-x₀ i| ≤ L*N ∧
      |(round (xref i):ℝ)-(round (x₀ i):ℝ)| ≤ L*N+1 := by
  classical
  intro f hlevel hMatt hMatmap hL hU hy ep rp
  have hK : (0:ℝ) < K₀ := by exact_mod_cast (NeZero.pos K₀)
  have hQreal : (0:ℝ) < Q := by exact_mod_cast hQ
  have hgamma' : |(Mat 2:ℝ)| ≤ R^4/(6*N^2) := by
    apply hgamma.trans
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh := pow_le_pow_left₀ (mul_nonneg hQreal.le hN.le) hmesh 2
    nlinarith only [hh]
  have hqpos i : (0:ℝ) < (rat i).den := by exact_mod_cast (rat i).pos
  have hband i : ((rat i).den:ℝ) ≤ Q ∧ (Q:ℝ) ≤ 2*(rat i).den := by
    exact_mod_cast hden i
  have htlo : (1/2:ℝ) ≤ (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3 := by
    rw [hMatt]
    apply (le_div_iff₀ (hqpos 0)).mpr
    linarith only [(hband 0).1,(hband 1).2]
  have hthi : (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3 ≤ 2 := by
    rw [hMatt]
    apply (div_le_iff₀ (hqpos 0)).mpr
    linarith only [(hband 1).1,(hband 0).2]
  have hinit i : iteratedDeriv 2 (heathBrownPhysicalPhase (F i) T M (A i) 1) (x₀ i)/2=
      (rat i:ℝ) := hlevel i
  have htlo' : (1/2:ℝ) ≤ (Mat 2:ℝ)*(iteratedDeriv 2 (f 0) (x₀ 0)/2)+Mat 3 := by
    rw [hlevel 0]; exact htlo
  have hthi' : (Mat 2:ℝ)*(iteratedDeriv 2 (f 0) (x₀ 0)/2)+Mat 3 ≤ 2 := by
    rw [hlevel 0]; exact hthi
  have hmap' : ((Mat 0:ℝ)*(iteratedDeriv 2 (f 0) (x₀ 0)/2)+Mat 1)/
      ((Mat 2:ℝ)*(iteratedDeriv 2 (f 0) (x₀ 0)/2)+Mat 3)=
      iteratedDeriv 2 (f 1) (x₀ 1)/2 := by
    rw [hlevel 0,hlevel 1]; exact hMatmap
  obtain ⟨_hε,ρ,hρ⟩ := physicalModelPhase_matrix_long_window_roots Mat
    hσ hδ hF hT hM hN hR hLpos hscale hA hW hx₀ hdet hgamma' hwindow
    hL hU htlo' hthi' hmap'
  simp only [hinit 0] at hρ
  have hh := hρ ((e:ℝ)/r) hy
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hrd : (rp 1:ℝ)=((Mat 2:ℝ)*((e:ℝ)/r)+Mat 3)*(r:ℝ) := by
    change ((Mat 2*e+Mat 3*r:ℤ):ℝ)=_
    push_cast
    field_simp
  have hed : (ep 1:ℝ)=((Mat 0:ℝ)*((e:ℝ)/r)+Mat 1)*(r:ℝ) := by
    change ((Mat 0*e+Mat 1*r:ℤ):ℝ)=_
    push_cast
    field_simp
  have hratios i :
      (![ (e:ℝ)/r,((Mat 0:ℝ)*((e:ℝ)/r)+Mat 1)/((Mat 2:ℝ)*((e:ℝ)/r)+Mat 3)] : Fin 2 → ℝ) i=
      (ep i:ℝ)/rp i := by
    fin_cases i
    · rfl
    · change ((Mat 0:ℝ)*((e:ℝ)/r)+Mat 1)/((Mat 2:ℝ)*((e:ℝ)/r)+Mat 3)=(ep 1:ℝ)/rp 1
      rw [hed,hrd,mul_div_mul_right _ _ hrR.ne']
  have hrp i : 0 < rp i := by
    fin_cases i
    · exact hr
    · have ht : 0 < (Mat 2:ℝ)*((e:ℝ)/r)+Mat 3 := by linarith only [hh.1.1]
      have hp : (0:ℝ) < rp 1 := by rw [hrd]; exact mul_pos ht hrR
      exact_mod_cast hp
  refine ⟨ρ ((e:ℝ)/r),fun i => ⟨hrp i,(hh.2 i).2.1,?_,(hh.2 i).2.2.2⟩⟩
  exact (hh.2 i).2.2.1.trans (hratios i)


                                                                
                                                                      
                                                                     
                                                                     
open TaoTrudgianYang2025.HuxleyLinearForm in
theorem physicalModelPhase_curvature_boundary_window_count
    (S : Finset ℕ) (x : ℕ → ℝ)
    {σ δ T M A W N R base ε boundary : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hphase : T*N*R^2=M^3)
    (hsmall : 4*ε*R^2 ≤ modelPhaseThirdLower σ)
    (hx : ∀ j∈S, x j∈Ioo 0 W)
    (hwindow : ∀ j∈S, x j∈Icc (base+(j:ℝ)*N) (base+((j:ℝ)+1)*N)) :
    let f := heathBrownPhysicalPhase F T M A 1
    (∀ j∈S, |iteratedDeriv 2 f (x j)/2-boundary| ≤ ε) →
    S.card ≤ 3 := by
  classical
  intro f hnear
  have hκ : 0 < modelPhaseThirdLower σ := modelPhaseThirdLower_pos hσ
  have hcoef : modelPhaseThirdLower σ*T/(2*M^3)=
      modelPhaseThirdLower σ/(2*N*R^2) := by
    rw [←hphase]
    field_simp
  have hord i (hi : i∈S) j (hj : j∈S) (hij : x i ≤ x j) :
      x j-x i ≤ N := by
    have hg := physicalModelPhase_halfCurvature_growth hσ hδ hF hT hM hA hW
      (hx i hi) (hx j hj) hij
    rw [hcoef] at hg
    have ha := abs_le.mp (hnear i hi)
    have hb := abs_le.mp (hnear j hj)
    have hh : modelPhaseThirdLower σ/(2*N*R^2)*(x j-x i) ≤ 2*ε := by
      linarith only [hg,ha.1,hb.2]
    have hh' : modelPhaseThirdLower σ*(x j-x i) ≤ 2*ε*(2*N*R^2) := by
      apply (div_le_iff₀ (show 0 < 2*N*R^2 by positivity)).mp
      convert hh using 1
      ring
    have hs := mul_le_mul_of_nonneg_right hsmall hN.le
    apply (mul_le_mul_iff_of_pos_left hκ).mp
    nlinarith only [hh',hs]
  have hwidth i (hi : i∈S) j (hj : j∈S) : |x j-x i| ≤ N := by
    rcases le_total (x i) (x j) with hij | hji
    · rw [abs_of_nonneg (sub_nonneg.mpr hij)]
      exact hord i hi j hj hij
    · rw [abs_of_nonpos (sub_nonpos.mpr hji)]
      have hh := hord j hj i hi hji
      linarith only [hh]
  let SI := S.image (fun j : ℕ => (j:ℤ))
  have hh := physical_block_count_of_pairwise_width
    SI (fun j => x j.toNat) (C:=1) hN (by norm_num)
    (by
      intro j hj
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
      simpa only [Int.toNat_natCast,Int.cast_natCast,Set.mem_Icc] using hwindow i hi)
    (by
      intro j hj k hk
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hk
      simpa only [Int.toNat_natCast,one_mul] using hwidth i hi m hm)
  have hSI : SI.card=S.card := Finset.card_image_of_injective _ Int.ofNat_injective
  rw [hSI] at hh
  have hc : (S.card:ℝ) ≤ 3 := by linarith only [hh]
  exact_mod_cast hc


                                                                   
                                                                   
                                                                      
theorem physicalModelPhase_farey_boundary_crossing_count
    (S : Finset ℕ) (Z : Finset ℝ) (x : ℕ → ℝ)
    {σ δ T M A W N R base ε e r v s : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hphase : T*N*R^2=M^3)
    (hsmall : 4*ε*R^2 ≤ modelPhaseThirdLower σ)
    (hx : ∀ j∈S, x j∈Ioo 0 W)
    (hwindow : ∀ j∈S, x j∈Icc (base+(j:ℝ)*N) (base+((j:ℝ)+1)*N))
    (hZden : ∀ z∈Z, 0 < r*z+s) :
    let f := heathBrownPhysicalPhase F T M A 1
    let q := fun j => iteratedDeriv 2 f (x j)/2
    let α := fun j => (v-s*(q j+ε))/(r*(q j+ε)-e)
    let β := fun j => (v-s*(q j-ε))/(r*(q j-ε)-e)
    (∀ j∈S, 0 < r*(q j-ε)-e ∧ 0 < r*(q j+ε)-e) →
    ((S.filter (fun j => ∃ z∈Z, z∈Icc (α j) (β j))).card ≤ 3*Z.card) := by
  classical
  intro f q α β hchart
  let fiber := fun z => S.filter (fun j => z∈Icc (α j) (β j))
  have hcount z (hz : z∈Z) : (fiber z).card ≤ 3 := by
    apply physicalModelPhase_curvature_boundary_window_count (fiber z) x
      hσ hδ hF hT hM hN hR hA hW hphase hsmall
      (fun j hj => hx j (Finset.mem_filter.mp hj).1)
      (fun j hj => hwindow j (Finset.mem_filter.mp hj).1)
      (boundary := (e*z+v)/(r*z+s))
    intro j hj
    obtain ⟨hjS,hlo,hhi⟩ := Finset.mem_filter.mp hj
    have ha := (div_le_iff₀ (hchart j hjS).2).mp hlo
    have hb := (le_div_iff₀ (hchart j hjS).1).mp hhi
    have hleft : q j-ε ≤ (e*z+v)/(r*z+s) := by
      apply (le_div_iff₀ (hZden z hz)).mpr
      nlinarith only [hb]
    have hright : (e*z+v)/(r*z+s) ≤ q j+ε := by
      apply (div_le_iff₀ (hZden z hz)).mpr
      nlinarith only [ha]
    change |q j-(e*z+v)/(r*z+s)| ≤ ε
    apply abs_le.mpr
    constructor <;> linarith only [hleft,hright]
  have he : S.filter (fun j => ∃ z∈Z, z∈Icc (α j) (β j))=Z.biUnion fiber := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_biUnion,fiber]
    aesop
  rw [he]
  calc
    _ ≤ ∑ z∈Z, (fiber z).card := Finset.card_biUnion_le
    _ ≤ ∑ _z∈Z, 3 := Finset.sum_le_sum hcount
    _ = 3*Z.card := by simp [Nat.mul_comm]


                                                               
                                                              
                                                                  
theorem farey_matrix_original_seed_coordinates
    (rat : Fin 2 → ℚ) (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    (hchart : v*r-e*s=1)
    (hMatt : (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=((rat 1).den:ℝ)/(rat 0).den)
    (hMatmap : ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ)) :
    let p : ℤ × ℤ := (v*((rat 0).den:ℤ)-s*(rat 0).num,
      r*(rat 0).num-e*((rat 0).den:ℤ))
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let vp : Fin 2 → ℤ := ![v,Mat 0*v+Mat 1*s]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    ∀ i, (rp i:ℝ)*p.1+sp i*p.2=((rat i).den:ℝ) ∧
      (ep i:ℝ)*p.1+vp i*p.2=((rat i).num:ℝ) := by
  intro p ep rp vp sp
  have hqpos i : (0:ℝ) < (rat i).den := by exact_mod_cast (rat i).pos
  have hrat i : (rat i:ℝ)=((rat i).num:ℝ)/((rat i).den:ℝ) := Rat.cast_def _
  have hchartR : (v:ℝ)*r-e*s=1 := by exact_mod_cast hchart
  have hdenR : (Mat 2:ℝ)*(rat 0).num+Mat 3*(rat 0).den=(rat 1).den := by
    calc
      _ = ((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)*(rat 0).den := by
        rw [hrat]; field_simp [(hqpos 0).ne']
      _ = (rat 1).den := by rw [hMatt]; field_simp [(hqpos 0).ne']
  have hnumR : (Mat 0:ℝ)*(rat 0).num+Mat 1*(rat 0).den=(rat 1).num := by
    have hm := hMatmap
    rw [hMatt,hrat 0,hrat 1] at hm
    have hh := (div_eq_iff (div_ne_zero (hqpos 1).ne' (hqpos 0).ne')).mp hm
    field_simp [(hqpos 0).ne',(hqpos 1).ne'] at hh
    nlinarith only [hh]
  intro i
  fin_cases i <;> constructor
  · dsimp only [p,rp,sp]; push_cast
    linear_combination ((rat 0).den:ℝ)*hchartR
  · dsimp only [p,ep,vp]; push_cast
    linear_combination ((rat 0).num:ℝ)*hchartR
  · dsimp only [p,rp,sp]; push_cast
    linear_combination ((Mat 2:ℝ)*(rat 0).num+Mat 3*(rat 0).den)*hchartR+hdenR
  · dsimp only [p,ep,vp]; push_cast
    linear_combination ((Mat 0:ℝ)*(rat 0).num+Mat 1*(rat 0).den)*hchartR+hnumR


                                                              
                                                                  
                                                                      
                                      
theorem exists_dyadic_rational_near_anchor {Q : ℕ} {a : ℚ} {ε : ℝ}
    (hcut : 2*a.den ≤ Q) (hscale : 4 ≤ ε*(Q:ℝ)*a.den) :
    ∃ b : ℚ, b.den ≤ Q ∧ Q ≤ 2*b.den ∧
      (a:ℝ) < b ∧ |(b:ℝ)-(a:ℝ)| ≤ ε/2 ∧
      (b:ℝ)-(a:ℝ)=1/((a.den:ℝ)*b.den) := by
  have ha : (0:ℤ) < a.den := by exact_mod_cast a.den_pos
  have hQ : 0 < Q := by have hh := a.den_pos; omega
  have haQ : (a.den:ℤ) ≤ Q := by exact_mod_cast (show a.den ≤ Q by omega)
  obtain ⟨c,d,hd,hdQ,hsum,hcop,hdet,_⟩ :=
    exists_right_neighbor_at_order ha haQ a.isCoprime_num_den
  have hdpos : 0 < d := by omega
  let b : ℚ := (c:ℚ)/(d:ℚ)
  have hden : (b.den:ℤ)=d :=
    Rat.den_div_eq_of_coprime hdpos (Int.isCoprime_iff_nat_coprime.mp hcop)
  have hbQ : b.den ≤ Q := by exact_mod_cast (hden ▸ hdQ)
  have hcutI : 2*(a.den:ℤ) ≤ Q := by exact_mod_cast hcut
  have hhalfI : (Q:ℤ) ≤ 2*(b.den:ℤ) := by omega
  have hhalf : Q ≤ 2*b.den := by exact_mod_cast hhalfI
  have haR : (0:ℝ) < a.den := by exact_mod_cast a.den_pos
  have hdR : (0:ℝ) < d := by exact_mod_cast hdpos
  have hbR : (0:ℝ) < b.den := by exact_mod_cast b.den_pos
  have hdenR : (b.den:ℝ)=d := by exact_mod_cast hden
  have hval : (b:ℝ)=(c:ℝ)/d := by dsimp only [b]; push_cast; rfl
  have hgap : (b:ℝ)-(a:ℝ)=1/((a.den:ℝ)*b.den) := by
    rw [hval,Rat.cast_def a,hdenR]
    field_simp
    exact_mod_cast (show c*(a.den:ℤ)-d*a.num=1 by nlinarith only [hdet])
  have hpos : 0 < (b:ℝ)-(a:ℝ) := by rw [hgap]; positivity
  have hQpos : (0:ℝ) < Q := by exact_mod_cast hQ
  have hε : 0 < ε := by
    have hp : 0 < ε*((Q:ℝ)*a.den) := by nlinarith only [hscale]
    exact (mul_pos_iff_of_pos_right (mul_pos hQpos haR)).mp hp
  have hhalfR : (Q:ℝ) ≤ 2*(b.den:ℝ) := by exact_mod_cast hhalf
  have hbscale : 2 ≤ ε*(a.den:ℝ)*b.den := by
    have hh := mul_le_mul_of_nonneg_left hhalfR (mul_nonneg hε.le haR.le)
    nlinarith only [hh,hscale]
  refine ⟨b,hbQ,hhalf,by linarith only [hpos],?_,hgap⟩
  rw [abs_of_pos hpos,hgap]
  apply (div_le_iff₀ (mul_pos haR hbR)).mpr
  nlinarith only [hbscale]



                                                                   
                                                                   
                                                                     
theorem positive_difference_dyadic_anchor_center
    (F : ℝ → ℝ) {Q : ℕ} {a : ℚ} {σ c η y T M N R x : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hy : y∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hNM : N ≤ M)
    (hphase : T*N*R^2=M^3)
    (hx : x∈Icc (7*M/8) (17*M/8))
    (hcut : 2*a.den ≤ Q) (hmajor : 128*σ*R^2 ≤ c*(Q:ℝ)*a.den) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    iteratedDeriv 2 f x/2=(a:ℝ) →
    ∃ b : ℚ, b.den ≤ Q ∧ Q ≤ 2*b.den ∧
      (a:ℝ) < b ∧ |(b:ℝ)-(a:ℝ)| ≤ c/(64*σ*R^2) ∧
      ∃ z∈Icc x (x+N/16), iteratedDeriv 2 f z/2=(b:ℝ) := by
  intro f hlevel
  let ε := c/(32*σ*R^2)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hmajor' : 4 ≤ ε*(Q:ℝ)*a.den := by
    dsimp only [ε]
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0 < 32*σ*R^2)).mpr
    nlinarith only [hmajor]
  obtain ⟨b,hb,hbhalf,hab,hclose,_⟩ := exists_dyadic_rational_near_anchor hcut hmajor'
  have hclose' : |(b:ℝ)-(a:ℝ)| ≤ c/(64*σ*R^2) := by
    convert hclose using 1
    dsimp only [ε]
    ring
  let g := fun w => iteratedDeriv 2 f w/2
  let K := c*T/(4*σ*M^3)
  have hnorm w (hw : w∈Icc (3*M/4) (9*M/4)) : w/M∈Icc (3/4:ℝ) (9/4) := by
    constructor
    · apply (le_div_iff₀ hM).mpr; linarith only [hw.1]
    · apply (div_le_iff₀ hM).mpr; linarith only [hw.2]
  have hd w (hw : w∈Icc (3*M/4) (9*M/4)) :
      HasDerivAt g (iteratedDeriv 3 f w/2) w := by
    have hw0 : 0 < w/M := by linarith only [(hnorm w hw).1]
    have hs0 : 0 < w/M+η*y := add_pos hw0 (mul_pos hη (by linarith only [hy.1]))
    have hcf : ContDiffAt ℝ 3 f w :=
      (contDiffAt_const.mul (((hf _ hw0).comp w (contDiffAt_id.div_const M)).sub
        ((hf _ hs0).comp w ((contDiffAt_id.div_const M).add contDiffAt_const)))).div_const
        (σ*η) |>.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
    exact (hasDerivAt_iteratedDeriv_finite (by norm_num : 2 < 3) hcf).div_const 2
  have hlower w (hw : w∈Icc (3*M/4) (9*M/4)) : K ≤ deriv g w := by
    rw [(hd w hw).deriv]
    have hl := positive_difference_third_signed_lower F (y:=y) hσ hη hηmax hc
      (hnorm w hw) ⟨by linarith only [hy.1],by linarith only [hy.2]⟩ hf hnegative
    have hid := positive_difference_physical_iteratedDeriv F (T:=T) (σ:=σ) hM
      (show 0 < w by linarith only [hw.1,hM])
      (mul_nonneg hη.le (by linarith only [hy.1])) hf 3
    dsimp only [f]
    rw [hid]
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hl (show 0 ≤ T/M^3 by positivity))
      (by norm_num : (0:ℝ) ≤ 2)
    convert hh using 1
    dsimp only [K]
    ring
  have hxwide : x∈Icc (3*M/4) (9*M/4) := by
    constructor <;> linarith only [hx.1,hx.2,hM]
  have hUwide : x+N/16∈Icc (3*M/4) (9*M/4) := by
    constructor <;> linarith only [hx.1,hx.2,hM,hN,hNM]
  have hinc := (convex_Icc (3*M/4) (9*M/4)).mul_sub_le_image_sub_of_le_deriv
    (fun w hw => (hd w hw).continuousAt.continuousWithinAt)
    (fun w hw => (hd w (interior_subset hw)).differentiableAt.differentiableWithinAt)
    (fun w hw => hlower w (interior_subset hw)) x hxwide (x+N/16) hUwide
    (show x ≤ x+N/16 by linarith only [hN])
  have hrate : K*(N/16)=c/(64*σ*R^2) := by
    dsimp only [K]
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
    change c/(64*σ*R^2) ≤ g (x+N/16)-iteratedDeriv 2 f x/2 at hinc
    rw [hlevel] at hinc
    linarith only [hinc,(abs_le.mp hclose').2]
  obtain ⟨z,hz,hzlevel⟩ := intermediate_value_Icc
    (show x ≤ x+N/16 by linarith only [hN])
    (fun w hw => (hd w (hsub hw)).continuousAt.continuousWithinAt) htarget
  exact ⟨b,hb,hbhalf,hab,hclose',z,hz,hzlevel⟩



                                                                       
                                                                   
                                                                      
                                                                        
                                                             
theorem positive_difference_dyadic_anchor_source_fourier
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (S : Finset ι) (F : ℝ → ℝ)
      (y : ι → ℝ) (L : ι → ℤ) (H : ι → ℕ) (anchor : ι → ℚ) (za : ι → ℝ)
      (N Q : ℕ) (η T M R : ℝ),
      1 ≤ N → (∀ i∈S, H i ≤ N) →
      0 < η → η ≤ 1/8 → 0 < T → 0 < M → 0 < R →
      (∀ i∈S, y i∈Icc (1:ℝ) 2) →
      (∀ i∈S, (L i:ℝ)-2*(N:ℝ)∈Icc M (2*M)) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 →
      7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      Q ≤ N → (∀ i∈S, 2*(anchor i).den ≤ Q) →
      (∀ i∈S, 128*σ*R^2 ≤ c*(Q:ℝ)*(anchor i).den) →
      let f := fun i w => T*(F (w/M)-F (w/M+η*y i))/(σ*η)
      (∀ i∈S, za i∈Ioo ((L i:ℝ)-2*(N:ℝ)-(N:ℝ)/8)
        ((L i:ℝ)-2*(N:ℝ)+(N:ℝ)/8) ∧
        iteratedDeriv 2 (f i) (za i)/2=(anchor i:ℝ)) →
      ∃ (r : ι → ℚ) (z : ι → ℝ),
      (∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i:ℝ) < r i ∧ |(r i:ℝ)-(anchor i:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i) (za i+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ)) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i) (m i)/6
      let ℓ := fun i => deriv (f i) (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈S, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
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
  obtain ⟨C,hC,hentry⟩ := positive_difference_chosen_arcs_band_fourier hσ hc hJ
  refine ⟨C,hC,?_⟩
  intro ι S F y L H anchor za N Q η T M R hN hH hη hηmax hT hM hR
    hy hbase hf hbound hnegative hphase hbuffer hfourBudget hquadBudget
    hQN hcut hmajor f hanchors
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNM : (N:ℝ) ≤ M := by linarith only [hbuffer,hNp]
  have hex i : ∃ b : ℚ, ∃ z : ℝ, i∈S →
      b.den ≤ Q ∧ Q ≤ 2*b.den ∧ (anchor i:ℝ) < b ∧
      |(b:ℝ)-(anchor i:ℝ)| ≤ c/(64*σ*R^2) ∧
      z∈Icc (za i) (za i+(N:ℝ)/16) ∧
      iteratedDeriv 2 (f i) z/2=(b:ℝ) := by
    by_cases hi : i∈S
    · have hx : za i∈Icc (7*M/8) (17*M/8) := by
        have hh := (hanchors i hi).1
        have hb := hbase i hi
        constructor <;> linarith only [hh.1,hh.2,hb.1,hb.2,hNM]
      obtain ⟨b,hb,hhalf,hab,hclose,z,hz,he⟩ :=
        positive_difference_dyadic_anchor_center F hσ hc hη hηmax (hy i hi) hf hnegative
          hT hM hNp hR hNM hphase hx (hcut i hi) (hmajor i hi) (hanchors i hi).2
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
  obtain ⟨hgeo,hcomplete⟩ := hentry ι S F y L H r z N η T M R hN hH hη hηmax
    hT hM hR hy hbase hf hbound hnegative hphase hbuffer hfourBudget hquadBudget hroots
  let lambda := c/(12*σ*(N:ℝ)*R^2)
  have hgood i (hi : i∈S) : q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N := by
    refine ⟨(hr i hi).1.trans hQN,?_⟩
    have hcutR : 2*((anchor i).den:ℝ) ≤ Q := by exact_mod_cast hcut i hi
    have hqR : (Q:ℝ) ≤ 2*(q i:ℝ) := by exact_mod_cast (hr i hi).2.1
    have haQ : ((anchor i).den:ℝ) ≤ (q i:ℝ) := by linarith only [hcutR,hqR]
    have hprod : c*(Q:ℝ)*(anchor i).den ≤ 2*c*(q i:ℝ)^2 := by
      calc
        _ ≤ c*(2*(q i:ℝ))*(q i:ℝ) := by gcongr
        _ = _ := by ring
    have hbudget : 12*σ*R^2 ≤ c*(q i:ℝ)^2 := by
      have hpositive : 0 < σ*R^2 := by positivity
      nlinarith only [hmajor i hi,hprod,hpositive]
    have heq : lambda*(q i:ℝ)^2*N=c*(q i:ℝ)^2/(12*σ*R^2) := by
      dsimp only [lambda]
      field_simp
    rw [heq]
    exact (one_le_div (by positivity : 0 < 12*σ*R^2)).mpr hbudget
  have hGS : S.filter (fun i => q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)=S :=
    Finset.filter_eq_self.mpr hgood
  have hBad : S.filter (fun i => ¬ (q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N))=∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i hi hn
    exact hn (hgood i hi)
  dsimp only [q,lambda] at hGS hBad
  refine ⟨hgeo,?_⟩
  intro K₀ inst hK₀
  have hqG i (hi : i∈S.filter (fun i => q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)) :
      q i ≤ Q := (hr i (Finset.mem_filter.mp hi).1).1
  obtain ⟨v,hv,hout⟩ := hcomplete Q hqG K₀ hK₀
  refine ⟨v,?_,?_⟩
  · simpa only [hGS] using hv
  · intro b τ s K x
    simpa only [hGS,hBad,Finset.sum_empty,zero_add] using hout



                                                                  
                                                                        
                                                                      
                                                                            
private theorem positive_difference_dyadic_anchor_source_partition_cutoffs
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (S : Finset ι) (F : ℝ → ℝ)
      (y : ι → ℝ) (L : ι → ℤ) (H : ι → ℕ) (anchor : ι → ℚ) (za : ι → ℝ)
      (N Q : ℕ) (η T M R : ℝ),
      1 ≤ N → (∀ i∈S, H i ≤ N) →
      0 < η → η ≤ 1/8 → 0 < T → 0 < M → 0 < R →
      (∀ i∈S, y i∈Icc (1:ℝ) 2) →
      (∀ i∈S, (L i:ℝ)-2*(N:ℝ)∈Icc M (2*M)) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 →
      7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      Q ≤ N →
      let f := fun i w => T*(F (w/M)-F (w/M+η*y i))/(σ*η)
      (∀ i∈S, za i∈Ioo ((L i:ℝ)-2*(N:ℝ)-(N:ℝ)/8)
        ((L i:ℝ)-2*(N:ℝ)+(N:ℝ)/8) ∧
        iteratedDeriv 2 (f i) (za i)/2=(anchor i:ℝ)) →
      ∀ (Acut : ℕ) (Bmajor : ℝ), 2 ≤ Acut → 128*σ ≤ Bmajor →
      let Good := fun i => Acut*(anchor i).den ≤ Q ∧
        Bmajor*R^2 ≤ c*(Q:ℝ)*(anchor i).den
      let G := S.filter Good
      ∃ (r : ι → ℚ) (z : ι → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i:ℝ) < r i ∧ |(r i:ℝ)-(anchor i:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i) (za i+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ)) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i) (m i)/6
      let ℓ := fun i => deriv (f i) (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ι → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈S, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f i n):ℂ)‖) ≤
          C*((∑ i∈S.filter (fun i => ¬ Good i),(H i:ℝ))+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) := by
  classical
  obtain ⟨C,hC,hentry⟩ := positive_difference_dyadic_anchor_source_fourier hσ hc hJ
  refine ⟨C,hC,?_⟩
  intro ι S F y L H anchor za N Q η T M R hN hH hη hηmax hT hM hR
    hy hbase hf hbound hnegative hphase hbuffer hfourBudget hquadBudget
    hQN f hanchors Acut Bmajor hAcut hBmajor Good G
  have hGS : G ⊆ S := fun i hi => (Finset.mem_filter.mp hi).1
  obtain ⟨r,z,hr,hconsumer⟩ := hentry ι G F y L H anchor za N Q η T M R hN
    (fun i hi => hH i (hGS hi)) hη hηmax hT hM hR
    (fun i hi => hy i (hGS hi)) (fun i hi => hbase i (hGS hi)) hf hbound hnegative
    hphase hbuffer hfourBudget hquadBudget hQN
    (fun i hi => (Nat.mul_le_mul_right _ hAcut).trans (Finset.mem_filter.mp hi).2.1)
    (fun i hi => (mul_le_mul_of_nonneg_right hBmajor (sq_nonneg R)).trans
      (Finset.mem_filter.mp hi).2.2)
    (fun i hi => hanchors i (hGS hi))
  refine ⟨r,z,hr,?_⟩
  intro m A q μ ℓ U₃
  obtain ⟨hgeo,hcomplete⟩ := hconsumer
  refine ⟨hgeo,?_⟩
  intro K₀ inst hK₀
  obtain ⟨v,hv,hfourier⟩ := hcomplete K₀ hK₀
  refine ⟨v,hv,?_⟩
  intro b τ s K x
  obtain ⟨k,hk⟩ := hfourier
  refine ⟨k,?_⟩
  let Src := fun i => ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f i n):ℂ)‖
  let Bad := S.filter (fun i => ¬ Good i)
  have hbad : (∑ i∈Bad,Src i) ≤ ∑ i∈Bad,(H i:ℝ) := by
    apply Finset.sum_le_sum
    intro i _hi
    dsimp only [Src]
    apply (norm_sum_le _ _).trans_eq
    simp
  have hbad0 : 0 ≤ ∑ i∈Bad,(H i:ℝ) :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hbadC := mul_le_mul_of_nonneg_right hC hbad0
  simp only [one_mul] at hbadC
  have hsplit : (∑ i∈S,Src i)=(∑ i∈G,Src i)+(∑ i∈Bad,Src i) :=
    (Finset.sum_filter_add_sum_filter_not S Good Src).symm
  change (∑ i∈S,Src i) ≤ _
  rw [hsplit]
  have hh := add_le_add hk (hbad.trans hbadC)
  convert hh using 1
  dsimp only [Bad]
  ring

                                                                             
theorem positive_difference_dyadic_anchor_source_partition
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (S : Finset ι) (F : ℝ → ℝ)
      (y : ι → ℝ) (L : ι → ℤ) (H : ι → ℕ) (anchor : ι → ℚ) (za : ι → ℝ)
      (N Q : ℕ) (η T M R : ℝ),
      1 ≤ N → (∀ i∈S, H i ≤ N) →
      0 < η → η ≤ 1/8 → 0 < T → 0 < M → 0 < R →
      (∀ i∈S, y i∈Icc (1:ℝ) 2) →
      (∀ i∈S, (L i:ℝ)-2*(N:ℝ)∈Icc M (2*M)) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 →
      7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      Q ≤ N →
      let f := fun i w => T*(F (w/M)-F (w/M+η*y i))/(σ*η)
      (∀ i∈S, za i∈Ioo ((L i:ℝ)-2*(N:ℝ)-(N:ℝ)/8)
        ((L i:ℝ)-2*(N:ℝ)+(N:ℝ)/8) ∧
        iteratedDeriv 2 (f i) (za i)/2=(anchor i:ℝ)) →
      let Good := fun i => 2*(anchor i).den ≤ Q ∧
        128*σ*R^2 ≤ c*(Q:ℝ)*(anchor i).den
      let G := S.filter Good
      ∃ (r : ι → ℚ) (z : ι → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i:ℝ) < r i ∧ |(r i:ℝ)-(anchor i:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i) (za i+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ)) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i) (m i)/6
      let ℓ := fun i => deriv (f i) (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ι → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈S, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f i n):ℂ)‖) ≤
          C*((∑ i∈S.filter (fun i => ¬ Good i),(H i:ℝ))+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) := by
  obtain ⟨C,hC,hentry⟩ := positive_difference_dyadic_anchor_source_partition_cutoffs hσ hc hJ
  refine ⟨C,hC,?_⟩
  intro ι S F y L H anchor za N Q η T M R hN hH hη hηmax hT hM hR
    hy hbase hf hbound hnegative hphase hbuffer hfourBudget hquadBudget hQN f hanchors
  exact hentry ι S F y L H anchor za N Q η T M R hN hH hη hηmax hT hM hR
    hy hbase hf hbound hnegative hphase hbuffer hfourBudget hquadBudget hQN hanchors
    2 (128*σ) (by norm_num) le_rfl



                                                                      
                                                                        
                                                                          
                                                                     
                                                         
theorem positive_difference_interior_gap_dyadic_source_fourier
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (F : ℝ → ℝ) (N : ℕ) (s : ℤ) (H : ℤ → ℕ)
      (η y T M R U x₁ x₂ : ℝ),
      1 ≤ N → (∀ k, H k ≤ N) →
      0 < η → η ≤ 1/8 → y∈Icc (1:ℝ) 2 → 0 < T → 0 < M → 0 < R → 0 < U →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      3*J ≤ σ*U → x₁∈Icc M (2*M) → x₂∈Icc M (2*M) →
      let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun w => iteratedDeriv 2 f w/2
      let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
      let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      let delta := c/(64*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      U/(4*R^2) ≤ h x₂-h x₁ → h x₂-h x₁ ≤ 7*U/(2*R^2) →
      ∃ S : Finset ℤ, ∃ (anchor : ℤ → ℚ) (za : ℤ → ℝ),
        (∀ k : ℤ, k∈S ↔ x₁+(N:ℝ)/4 ≤ t k ∧ t k ≤ x₂-(N:ℝ)/4) ∧
        (∀ k∈S, za k∈Ioo x₁ x₂ ∧ h (za k)=(anchor k:ℝ) ∧
          (anchor k:ℝ)∈Ioo (h x₁) (h x₂) ∧
          (anchor k:ℝ)∈Ioo (h (t k)-delta) (h (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo (h (t k)-delta) (h (t k)+delta) → (anchor k).den ≤ a.den) ∧
        (∀ k∈S, |za k-t k| ≤ (N:ℝ)/16) ∧
        (σ/(6*J))*U-3/2 ≤ (S.card:ℝ) ∧ (S.card:ℝ) ≤ (56*σ/c)*U+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 64*σ*R^2/(c*(Q:ℝ))
          ((S.filter (fun k => Q ≤ (anchor k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1))) ∧
      ∀ Q : ℕ, Q ≤ N →
      let Good := fun i => 2*(anchor i).den ≤ Q ∧
        128*σ*R^2 ≤ c*(Q:ℝ)*(anchor i).den
      let G := S.filter Good
      ∃ (r : ℤ → ℚ) (z : ℤ → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i:ℝ) < r i ∧ |(r i:ℝ)-(anchor i:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i) (za i+(N:ℝ)/16) ∧
        iteratedDeriv 2 f (z i)/2=(r i:ℝ)) ∧
      (∀ i∈G, z i∈Ioo x₁ x₂) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 f (m i)/6
      let ℓ := fun i => deriv f (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈S, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f n):ℂ)‖) ≤
          C*((∑ i∈S.filter (fun i => ¬ Good i),(H i:ℝ))+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) := by
  classical
  obtain ⟨C,hC,hentry⟩ := positive_difference_dyadic_anchor_source_partition hσ hc hJ
  refine ⟨C,hC,?_⟩
  intro F N s H η y T M R U x₁ x₂ hN hH hη hηmax hy hT hM hR hU
    hf hbound hnegative hphase hbuffer hfourBudget hquadBudget hUlarge hx₁ hx₂
    f h t L delta Vbound hgaplow hgapup
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNM : (N:ℝ) ≤ M := by linarith only [hbuffer,hNp]
  have hc4 : 0 < c/4 := by positivity
  have hnegative4 w (hw : w∈Icc (1/2:ℝ) 3) : iteratedDeriv 4 F w ≤ -(c/4) := by
    linarith only [hnegative w hw,hc]
  obtain ⟨S,anchor,za,hmem,hdata,hcardlow,hcardup,htail⟩ :=
    positive_difference_reference_gap_minimal_arcs F N (s:=(s:ℝ))
      hσ hc4 hJ hη hηmax hy hf hbound hnegative4 hT hM
      (show 0 < N by omega) hR hU hNM hUlarge hphase hx₁ hx₂ hgaplow hgapup
  have hdelta : (c/4)/(16*σ*R^2)=delta := by dsimp only [delta]; ring
  rw [hdelta] at hdata
  have hpoints i (hi : i∈S) : t i∈Icc M (2*M) := by
    have hh := (hmem i).mp hi
    constructor <;> linarith only [hh.1,hh.2,hx₁.1,hx₂.2,hNp]
  have hdist i (hi : i∈S) : |za i-t i| ≤ (N:ℝ)/16 := by
    have hzI : za i∈Icc M (2*M) :=
      ⟨hx₁.1.trans (hdata i hi).1.1.le,(hdata i hi).1.2.le.trans hx₂.2⟩
    have hnear : |h (za i)-h (t i)| ≤ 7*(c/(224*σ))/(2*R^2) := by
      have he : h (za i)=(anchor i:ℝ) := (hdata i hi).2.1
      rw [he]
      have hh := (hdata i hi).2.2.2.1
      change (anchor i:ℝ)∈Ioo (h (t i)-delta) (h (t i)+delta) at hh
      have ha : |(anchor i:ℝ)-h (t i)| ≤ delta := abs_le.mpr
        ⟨by linarith only [hh.1],by linarith only [hh.2]⟩
      convert ha using 1
      dsimp only [delta]
      ring
    have hh := positive_difference_reference_preimage_width F hσ hc hη hηmax hy
      hf hnegative hT hM hNp hR hphase (hpoints i hi) hzI hnear
    convert hh using 1
    field_simp
    ring
  have hupper : (S.card:ℝ) ≤ (56*σ/c)*U+1/2 := by
    convert hcardup using 1
    ring
  refine ⟨S,anchor,za,hmem,hdata,hdist,hcardlow,hupper,?_,?_⟩
  · intro Q hQ D
    have hh := htail Q hQ
    have he : 16*σ*R^2/((c/4)*(Q:ℝ))=D := by dsimp only [D]; ring
    simpa only [he] using hh
  · intro Q hQN Good G
    have hL i : (L i:ℝ)-2*(N:ℝ)=t i := by
      dsimp only [L,t]
      push_cast
      ring
    have hanchors i (hi : i∈S) :
        za i∈Ioo ((L i:ℝ)-2*(N:ℝ)-(N:ℝ)/8)
          ((L i:ℝ)-2*(N:ℝ)+(N:ℝ)/8) ∧
        iteratedDeriv 2 f (za i)/2=(anchor i:ℝ) := by
      refine ⟨?_,(hdata i hi).2.1⟩
      rw [hL]
      have hh := abs_le.mp (hdist i hi)
      constructor <;> linarith only [hh.1,hh.2,hNp]
    obtain ⟨r,z,hr,hfourier⟩ := hentry ℤ S F (fun _ => y) L H anchor za N Q η T M R hN
      (fun i _ => hH i) hη hηmax hT hM hR (fun _ _ => hy)
      (fun i hi => by rw [hL]; exact hpoints i hi) hf hbound hnegative
      hphase hbuffer hfourBudget hquadBudget hQN hanchors
    refine ⟨r,z,hr,?_,hfourier⟩
    intro i hi
    have hiS := (Finset.mem_filter.mp hi).1
    have hh := abs_le.mp (hdist i hiS)
    have hg := (hmem i).mp hiS
    have hz := (hr i hi).2.2.2.2.1
    constructor <;> linarith only [hh.1,hh.2,hg.1,hg.2,hz.1,hz.2,hNp]



                                                                    
                                                                    
                                                                        
                                                                          
                                        
public  theorem positive_difference_tagged_gap_dyadic_source_fourier_cutoffs
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (Y : Finset ι) (F : ℝ → ℝ)
      (N : ℕ) (s : ℤ) (H : ι → ℤ → ℕ)
      (η T M R U : ℝ) (y x₁ x₂ : ι → ℝ),
      1 ≤ N → (∀ i∈Y, ∀ k, H i k ≤ N) →
      0 < η → η ≤ 1/8 → (∀ i∈Y, y i∈Icc (1:ℝ) 2) →
      0 < T → 0 < M → 0 < R → 0 < U →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      3*J ≤ σ*U →
      (∀ i∈Y, x₁ i∈Icc M (2*M)) → (∀ i∈Y, x₂ i∈Icc M (2*M)) →
      let f := fun i w => T*(F (w/M)-F (w/M+η*y i))/(σ*η)
      let h := fun i w => iteratedDeriv 2 (f i) w/2
      let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
      let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      let delta := c/(64*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      (∀ i∈Y, U/(4*R^2) ≤ h i (x₂ i)-h i (x₁ i) ∧
        h i (x₂ i)-h i (x₁ i) ≤ 7*U/(2*R^2)) →
      ∃ (S : ι → Finset ℤ) (anchor : ι → ℤ → ℚ) (za : ι → ℤ → ℝ),
        (∀ i∈Y,
          (∀ k : ℤ, k∈(S i) ↔ (x₁ i)+(N:ℝ)/4 ≤ t k ∧ t k ≤ (x₂ i)-(N:ℝ)/4) ∧
        (∀ k∈(S i), (za i) k∈Ioo (x₁ i) (x₂ i) ∧ (h i) ((za i) k)=((anchor i) k:ℝ) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i) (x₁ i)) ((h i) (x₂ i)) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) → ((anchor i) k).den ≤ a.den) ∧
        (∀ k∈(S i), |(za i) k-t k| ≤ (N:ℝ)/16) ∧
        (σ/(6*J))*U-3/2 ≤ ((S i).card:ℝ) ∧ ((S i).card:ℝ) ≤ (56*σ/c)*U+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 64*σ*R^2/(c*(Q:ℝ))
          (((S i).filter (fun k => Q ≤ ((anchor i) k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1)))) ∧
      ∀ Q : ℕ, Q ≤ N →
      ∀ (Acut : ℕ) (Bmajor : ℝ), 2 ≤ Acut → 128*σ ≤ Bmajor →
      let Sall := Y.biUnion (fun i => (S i).image (fun k => (i,k)))
      let Good := fun i => Acut*(anchor i.1 i.2).den ≤ Q ∧
        Bmajor*R^2 ≤ c*(Q:ℝ)*(anchor i.1 i.2).den
      let G := Sall.filter Good
      ∃ (r : ι × ℤ → ℚ) (z : ι × ℤ → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i.1 i.2:ℝ) < r i ∧ |(r i:ℝ)-(anchor i.1 i.2:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i.1 i.2) (za i.1 i.2+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i.1) (z i)/2=(r i:ℝ)) ∧
      (∀ i∈G, z i∈Ioo (x₁ i.1) (x₂ i.1)) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i.2-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i.1) (m i)/6
      let ℓ := fun i => deriv (f i.1) (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i.2) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ι × ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1 i.2),(𝐞 (f i.1 n):ℂ)‖) ≤
          C*((∑ i∈Sall.filter (fun i => ¬ Good i),(H i.1 i.2:ℝ))+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) := by
  classical
  obtain ⟨C,hC,hentry⟩ := positive_difference_dyadic_anchor_source_partition_cutoffs hσ hc hJ
  obtain ⟨_Cgap,_hCgap,hgapEntry⟩ := positive_difference_interior_gap_dyadic_source_fourier hσ hc hJ
  refine ⟨C,hC,?_⟩
  intro ι Y F N s H η T M R U y x₁ x₂ hN hH hη hηmax hy hT hM hR hU
    hf hbound hnegative hphase hbuffer hfourBudget hquadBudget hUlarge hx₁ hx₂
    f h t L delta Vbound hgap
  let Data (i : ι) (Si : Finset ℤ) (ai : ℤ → ℚ) (zi : ℤ → ℝ) : Prop :=
    (∀ k : ℤ, k∈Si ↔ (x₁ i)+(N:ℝ)/4 ≤ t k ∧ t k ≤ (x₂ i)-(N:ℝ)/4) ∧
        (∀ k∈Si, zi k∈Ioo (x₁ i) (x₂ i) ∧ (h i) (zi k)=(ai k:ℝ) ∧
          (ai k:ℝ)∈Ioo ((h i) (x₁ i)) ((h i) (x₂ i)) ∧
          (ai k:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) → (ai k).den ≤ a.den) ∧
        (∀ k∈Si, |zi k-t k| ≤ (N:ℝ)/16) ∧
        (σ/(6*J))*U-3/2 ≤ (Si.card:ℝ) ∧ (Si.card:ℝ) ≤ (56*σ/c)*U+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 64*σ*R^2/(c*(Q:ℝ))
          ((Si.filter (fun k => Q ≤ (ai k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1)))
  have hex : ∀ i∈Y, ∃ Si ai zi, Data i Si ai zi := by
    intro i hi
    obtain ⟨Si,ai,zi,hmem,hdata,hdist,hcardlow,hcardup,htail,_hfourier⟩ :=
      hgapEntry F N s (H i) η (y i) T M R U (x₁ i) (x₂ i)
        hN (hH i hi) hη hηmax (hy i hi) hT hM hR hU hf hbound hnegative
        hphase hbuffer hfourBudget hquadBudget hUlarge (hx₁ i hi) (hx₂ i hi)
        (hgap i hi).1 (hgap i hi).2
    exact ⟨Si,ai,zi,hmem,hdata,hdist,hcardlow,hcardup,htail⟩
  choose! S anchor za hinfo using hex
  refine ⟨S,anchor,za,hinfo,?_⟩
  intro Q hQN Acut Bmajor hAcut hBmajor Sall Good G
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmem (j : ι × ℤ) : j∈Sall ↔ j.1∈Y ∧ j.2∈S j.1 := by
    constructor
    · intro hj
      obtain ⟨i,hi,hj⟩ := Finset.mem_biUnion.mp hj
      obtain ⟨k,hk,he⟩ := Finset.mem_image.mp hj
      subst j
      exact ⟨hi,hk⟩
    · rintro ⟨hi,hj⟩
      exact Finset.mem_biUnion.mpr ⟨j.1,hi,Finset.mem_image.mpr ⟨j.2,hj,rfl⟩⟩
  have hL k : (L k:ℝ)-2*(N:ℝ)=t k := by
    dsimp only [L,t]
    push_cast
    ring
  have hbase j (hj : j∈Sall) : (L j.2:ℝ)-2*(N:ℝ)∈Icc M (2*M) := by
    rw [hL]
    obtain ⟨hi,hk⟩ := (hmem j).mp hj
    have hg := ((hinfo j.1 hi).1 j.2).mp hk
    constructor <;> linarith only [hg.1,hg.2,(hx₁ j.1 hi).1,(hx₂ j.1 hi).2,hNp]
  have hanchors j (hj : j∈Sall) :
      za j.1 j.2∈Ioo ((L j.2:ℝ)-2*(N:ℝ)-(N:ℝ)/8)
        ((L j.2:ℝ)-2*(N:ℝ)+(N:ℝ)/8) ∧
      iteratedDeriv 2 (f j.1) (za j.1 j.2)/2=(anchor j.1 j.2:ℝ) := by
    obtain ⟨hi,hk⟩ := (hmem j).mp hj
    refine ⟨?_,((hinfo j.1 hi).2.1 j.2 hk).2.1⟩
    rw [hL]
    have hh := abs_le.mp ((hinfo j.1 hi).2.2.1 j.2 hk)
    constructor <;> linarith only [hh.1,hh.2,hNp]
  obtain ⟨r,z,hr,hfourier⟩ := hentry (ι × ℤ) Sall F (fun j => y j.1)
    (fun j => L j.2) (fun j => H j.1 j.2) (fun j => anchor j.1 j.2) (fun j => za j.1 j.2)
    N Q η T M R hN (fun j hj => hH j.1 ((hmem j).mp hj).1 j.2)
    hη hηmax hT hM hR (fun j hj => hy j.1 ((hmem j).mp hj).1) hbase hf hbound hnegative
    hphase hbuffer hfourBudget hquadBudget hQN hanchors Acut Bmajor hAcut hBmajor
  refine ⟨r,z,hr,?_,hfourier⟩
  intro j hj
  obtain ⟨hi,hk⟩ := (hmem j).mp (Finset.mem_filter.mp hj).1
  have hh := abs_le.mp ((hinfo j.1 hi).2.2.1 j.2 hk)
  have hg := ((hinfo j.1 hi).1 j.2).mp hk
  have hz := (hr j hj).2.2.2.2.1
  constructor <;> linarith only [hh.1,hh.2,hg.1,hg.2,hz.1,hz.2,hNp]

                                                                            
theorem approximateModelPhase_enlarged_colored_linked_models
    {σ ε : ℝ} (hσ : 0 < σ) (P : ℕ) (hε : 0 < ε) :
    ∃ δ η₀ a : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1 ≤ M →
      Expdb.IsApproximateModelPhaseFunction F σ (P+2) δ →
      ∃ Fext : ℝ → ℝ,
        (∀ w, 0 < w → ContDiffAt ℝ ∞ Fext w) ∧
        (∀ w∈Icc (1/2:ℝ) 3, ∀ p ≤ P+1,
          |iteratedDeriv (p+1) Fext w-iteratedDeriv p (Expdb.modelPhase σ) w| ≤ ε) ∧
        (∀ (T : ℝ) (m n : ℕ), M ≤ (m:ℝ) → (n:ℝ) ≤ 2*M →
          ‖Expdb.exponentialSumAt F T M m n-Expdb.exponentialSumAt Fext T M m n‖ ≤ 6) ∧
        ∀ {ι : Type*} (S : Finset ι) (y : ι → ℝ) (η : ℝ),
          (∀ i∈S, y i∈Icc (1:ℝ) 2) → 0 < η → η ≤ η₀ →
          let color := fun i => ⌊y i/a⌋
          let Cap := 4/a+3
          ((S.image color).card:ℝ) ≤ Cap ∧
          (∀ z : ι → ℂ, ‖∑ i∈S,z i‖^12 ≤
            Cap^11*∑ j∈S.image color, ‖∑ i∈S.filter (fun i => color i=j),z i‖^12) ∧
          ∀ j∈S.image color, ∃ i₀∈S, color i₀=j ∧
            ∀ xi T N R : ℝ, 0 < xi → 0 < T → 0 < R → T*N*R^2=M^3 →
            let Tnew := T*σ*y i₀/xi
            let Rnew := R*Real.sqrt (xi/(σ*y i₀))
            0 < Tnew ∧ 0 < Rnew ∧ Rnew^2=R^2*xi/(σ*y i₀) ∧
              Tnew*N*Rnew^2=M^3 ∧
            ∀ i∈S, color i=j →
              let G := fun u => (Fext u-Fext (u+η*y i))/(σ*η*y i₀)
              let f := fun w => T*(Fext (w/M)-Fext (w/M+η*y i))/(xi*η)
              Expdb.IsApproximateModelPhaseFunction G (σ+1) P ε ∧
                (∀ A x : ℝ, heathBrownPhysicalPhase G Tnew M A 1 x=f (A+x)) ∧
                (∀ (A : ℤ) (w : ℝ) (k : ℕ),
                  iteratedDeriv k (heathBrownPhysicalPhase G Tnew M A 1) (round (w-A))=
                    iteratedDeriv k f (round w)) := by
  obtain ⟨δ,η₀,a,hδ,hη₀,hηcap,ha,hsource⟩ :=
    approximateModelPhase_enlarged_colored_difference_models hσ P hε
  refine ⟨δ,η₀,a,hδ,hη₀,hηcap,ha,?_⟩
  intro M F hM hF
  obtain ⟨Fext,hreg,hjets,hsharp,hcolors⟩ := hsource M F hM hF
  refine ⟨Fext,hreg,hjets,hsharp,?_⟩
  intro ι S y η hy hη hηmax color Cap
  obtain ⟨hcard,hmoment,hmodels⟩ := hcolors S y η hy hη hηmax
  refine ⟨hcard,hmoment,?_⟩
  intro j hj
  obtain ⟨i₀,hi₀,hcolor₀,hmodels₀⟩ := hmodels j hj
  refine ⟨i₀,hi₀,hcolor₀,?_⟩
  intro xi T N R hxi hT hR hscale Tnew Rnew
  have hy₀ : 0 < y i₀ := zero_lt_one.trans_le (hy i₀ hi₀).1
  have hn₀ := positive_difference_common_physical_normalization Fext (y:=y i₀)
    hσ hxi hη hy₀ hT hR hscale
  refine ⟨hn₀.1,hn₀.2.1,hn₀.2.2.1,hn₀.2.2.2.1,?_⟩
  intro i hi hcolor G f
  have hm := hmodels₀ i hi hcolor
  have hn := positive_difference_common_physical_normalization Fext (y:=y i)
    hσ hxi hη hy₀ hT hR hscale
  exact ⟨hm.1,hn.2.2.2.2.1,hn.2.2.2.2.2⟩


                                                                 
                                                                    
                                                                       
theorem modelPhase_compact_jet_signed_source_tests {σ : ℝ} (hσ : 0 < σ) :
    ∃ ε c J : ℝ, 0 < ε ∧ 0 < c ∧ 0 < J ∧
      ∀ Fext : ℝ → ℝ,
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6,
          |iteratedDeriv (n+1) Fext x-iteratedDeriv n (Expdb.modelPhase σ) x| ≤ ε) →
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fext x| ≤ J) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ j,
          c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
            (fun i : Fin 4 => iteratedDeriv (i.val+3) Fext x) j|) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 Fext x ≤ -c) := by
  obtain ⟨ε,c,hε,hc,htests⟩ := TaoTrudgianYang2025.HuxleyModel.exists_uniform_test_lower_positive_compact
    (a:=1/2) (b:=3) hσ (by norm_num) (by norm_num)
  let W := fun (x : ℝ) (j : Fin 7) => iteratedDeriv j.val (Expdb.modelPhase σ) x
  have hW : ContinuousOn W (Icc (1/2:ℝ) 3) := by
    apply continuousOn_pi.mpr
    intro j x hx
    have hx0 : x ≠ 0 := ne_of_gt (by linarith only [hx.1] : 0 < x)
    exact (contDiffAt_iteratedDeriv_infty
      (Real.contDiffAt_rpow_const_of_ne hx0) j.val).continuousAt.continuousWithinAt
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hW
  have hthird : ContinuousOn (iteratedDeriv 3 (Expdb.modelPhase σ)) (Icc (1/2:ℝ) 3) := by
    intro x hx
    exact (contDiffAt_iteratedDeriv_infty
      (Real.contDiffAt_rpow_const_of_ne (by linarith only [hx.1] : x ≠ 0)) 3).continuousAt.continuousWithinAt
  have hneg x (hx : x ∈ Icc (1/2:ℝ) 3) : iteratedDeriv 3 (Expdb.modelPhase σ) x < 0 := by
    have hx0 : 0 < x := by linarith only [hx.1]
    have hj : iteratedDeriv 3 (Expdb.modelPhase σ) x =
        (descPochhammer ℝ 3).eval (-σ)*x^(-σ-(3:ℝ)) := by
      rw [iteratedDeriv_eq_iterate]
      exact Real.iter_deriv_rpow_const (-σ) x 3
    have he : (descPochhammer ℝ 3).eval (-σ) = -(σ*(σ+1)*(σ+2)) := by
      norm_num [descPochhammer_eval_eq_prod_range,Finset.prod_range_succ]
      ring
    rw [hj,he]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) (Real.rpow_pos_of_pos hx0 _)
  obtain ⟨x₀,hx₀,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (1/2:ℝ) 3).Nonempty from ⟨1,by norm_num⟩) hthird
  let q := -iteratedDeriv 3 (Expdb.modelPhase σ) x₀
  have hq : 0 < q := neg_pos.mpr (hneg x₀ hx₀)
  let e := min (min ε 1) (q/2)
  have hepos : 0 < e := lt_min (lt_min hε zero_lt_one) (by positivity)
  have heε : e ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have heone : e ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have heq : e ≤ q/2 := min_le_right _ _
  refine ⟨e,min c (q/2),max 1 B+1,hepos,lt_min hc (by positivity),
    by linarith [le_max_left (1:ℝ) B],?_⟩
  intro Fext hjets
  refine ⟨?_,?_,?_⟩
  · intro x hx n hn
    have hh := hjets x hx n hn
    have hmodel : |iteratedDeriv n (Expdb.modelPhase σ) x| ≤ max 1 B :=
      ((norm_le_pi_norm (W x) ⟨n,by omega⟩).trans (hB x hx)).trans (le_max_right 1 B)
    have htri := abs_add_le
      (iteratedDeriv (n+1) Fext x-iteratedDeriv n (Expdb.modelPhase σ) x)
      (iteratedDeriv n (Expdb.modelPhase σ) x)
    rw [sub_add_cancel] at htri
    linarith only [hmodel,hh,htri,heone]
  · intro x hx j
    apply (min_le_left c (q/2)).trans
    apply htests x hx (fun i : Fin 4 => iteratedDeriv (i.val+3) Fext x)
    intro i
    have hh := hjets x hx (i.val+2) (by omega)
    exact hh.trans heε
  · intro x hx
    have hh := hjets x hx 3 (by norm_num)
    have hup : iteratedDeriv 3 (Expdb.modelPhase σ) x ≤ -q := by
      simpa only [q,neg_neg,Set.mem_ofPred_eq] using hmax hx
    have herr := (abs_le.mp hh).2
    have hcq := min_le_right c (q/2)
    linarith only [hup,herr,heq,hcq]


                                                              
                                                                 
                                                                  
                                                                
                                   
theorem approximateModelPhase_enlarged_colored_linked_source_tests
    {σ ε : ℝ} (hσ : 0 < σ) (P : ℕ) (hP : 5 ≤ P) (hε : 0 < ε) :
    ∃ δ η₀ a c J : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < c ∧ 0 < J ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1 ≤ M →
      Expdb.IsApproximateModelPhaseFunction F σ (P+2) δ →
      ∃ Fext : ℝ → ℝ,
        (∀ w, 0 < w → ContDiffAt ℝ ∞ Fext w) ∧
        (∀ w∈Icc (1/2:ℝ) 3, ∀ p ≤ P+1,
          |iteratedDeriv (p+1) Fext w-iteratedDeriv p (Expdb.modelPhase σ) w| ≤ ε) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fext x| ≤ J) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ j,
          c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
            (fun i : Fin 4 => iteratedDeriv (i.val+3) Fext x) j|) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 Fext x ≤ -c) ∧
        (∀ (T : ℝ) (m n : ℕ), M ≤ (m:ℝ) → (n:ℝ) ≤ 2*M →
          ‖Expdb.exponentialSumAt F T M m n-Expdb.exponentialSumAt Fext T M m n‖ ≤ 6) ∧
        ∀ {ι : Type*} (S : Finset ι) (y : ι → ℝ) (η : ℝ),
          (∀ i∈S, y i∈Icc (1:ℝ) 2) → 0 < η → η ≤ η₀ →
          let color := fun i => ⌊y i/a⌋
          let Cap := 4/a+3
          ((S.image color).card:ℝ) ≤ Cap ∧
          (∀ z : ι → ℂ, ‖∑ i∈S,z i‖^12 ≤
            Cap^11*∑ j∈S.image color, ‖∑ i∈S.filter (fun i => color i=j),z i‖^12) ∧
          ∀ j∈S.image color, ∃ i₀∈S, color i₀=j ∧
            ∀ xi T N R : ℝ, 0 < xi → 0 < T → 0 < R → T*N*R^2=M^3 →
            let Tnew := T*σ*y i₀/xi
            let Rnew := R*Real.sqrt (xi/(σ*y i₀))
            0 < Tnew ∧ 0 < Rnew ∧ Rnew^2=R^2*xi/(σ*y i₀) ∧
              Tnew*N*Rnew^2=M^3 ∧
            ∀ i∈S, color i=j →
              let G := fun u => (Fext u-Fext (u+η*y i))/(σ*η*y i₀)
              let f := fun w => T*(Fext (w/M)-Fext (w/M+η*y i))/(xi*η)
              Expdb.IsApproximateModelPhaseFunction G (σ+1) P ε ∧
                (∀ A x : ℝ, heathBrownPhysicalPhase G Tnew M A 1 x=f (A+x)) ∧
                (∀ (A : ℤ) (w : ℝ) (k : ℕ),
                  iteratedDeriv k (heathBrownPhysicalPhase G Tnew M A 1) (round (w-A))=
                    iteratedDeriv k f (round w)) := by
  obtain ⟨e,c,J,he,hc,hJ,htests⟩ := modelPhase_compact_jet_signed_source_tests hσ
  obtain ⟨δ,η₀,a,hδ,hη₀,hηcap,ha,hsource⟩ :=
    approximateModelPhase_enlarged_colored_linked_models hσ P (lt_min hε he)
  refine ⟨δ,η₀,a,c,J,hδ,hη₀,hηcap,ha,hc,hJ,?_⟩
  intro M F hM hF
  obtain ⟨Fext,hreg,hjets,hsharp,hcolors⟩ := hsource M F hM hF
  have hsourceJets : ∀ x ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6,
      |iteratedDeriv (n+1) Fext x-iteratedDeriv n (Expdb.modelPhase σ) x| ≤ e :=
    fun x hx n hn => (hjets x hx n (by omega)).trans (min_le_right ε e)
  obtain ⟨hbound,htest,hnegative⟩ := htests Fext hsourceJets
  refine ⟨Fext,hreg,fun x hx n hn => (hjets x hx n hn).trans (min_le_left ε e),
    hbound,htest,hnegative,hsharp,?_⟩
  intro ι S y η hy hη hηmax color Cap
  obtain ⟨hcard,hmoment,hmodels⟩ := hcolors S y η hy hη hηmax
  refine ⟨hcard,hmoment,?_⟩
  intro j hj
  obtain ⟨i₀,hi₀,hcolor₀,hlinked⟩ := hmodels j hj
  refine ⟨i₀,hi₀,hcolor₀,?_⟩
  intro xi T N R hxi hT hR hscale Tnew Rnew
  obtain ⟨hTnew,hRnew,hRsq,hlink,hmodels₀⟩ := hlinked xi T N R hxi hT hR hscale
  refine ⟨hTnew,hRnew,hRsq,hlink,?_⟩
  intro i hi hcolor G f
  obtain ⟨hm,hphysical,hrounded⟩ := hmodels₀ i hi hcolor
  exact ⟨TaoTrudgianYang2025.approximateModelPhase_mono hm le_rfl (min_le_left ε e),
    hphysical,hrounded⟩


                                                          
                                                                     
                                                                     
                                                                    
theorem exists_positive_difference_source_fourier_mesh
    {σ J N R Q : ℝ} (hσ : 0 < σ)
    (hN : 0 < N) (hR : 0 < R) (hQ : 0 < Q) (hbase : R^2 ≤ Q*N) :
    let C := max 1 (63*J/(2*σ))
    ∃ K₀ : ℕ, 0 < K₀ ∧
      63*(J/(2*σ*N*R^2))*Q*N^2 ≤ K₀ ∧
      Q*N ≤ (K₀:ℝ)*R^2 ∧
      (K₀:ℝ) ≤ 2*C*Q*N/R^2 := by
  intro C
  let x := C*(Q*N/R^2)
  have hC : 1 ≤ C := le_max_left _ _
  have hcoeff : 63*J/(2*σ) ≤ C := le_max_right _ _
  have hrate : 1 ≤ Q*N/R^2 := (le_div_iff₀ (sq_pos_of_pos hR)).mpr (by simpa using hbase)
  have hratepos : 0 < Q*N/R^2 := by positivity
  have hCX : Q*N/R^2 ≤ x := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hratepos.le
  have hx : 1 ≤ x := hrate.trans hCX
  have hceil : x ≤ (⌈x⌉₊:ℝ) := Nat.le_ceil x
  have hceilup : (⌈x⌉₊:ℝ) < x+1 := Nat.ceil_lt_add_one (zero_le_one.trans hx)
  refine ⟨⌈x⌉₊,Nat.one_le_ceil_iff.mpr (zero_lt_one.trans_le hx),?_,?_,?_⟩
  · have he : 63*(J/(2*σ*N*R^2))*Q*N^2=(63*J/(2*σ))*(Q*N/R^2) := by
      field_simp
    rw [he]
    exact (mul_le_mul_of_nonneg_right hcoeff hratepos.le).trans hceil
  · apply (div_le_iff₀ (sq_pos_of_pos hR)).mp
    exact hCX.trans hceil
  · have hh : (⌈x⌉₊:ℝ) ≤ 2*x := by linarith only [hceilup,hx]
    convert hh using 1
    dsimp only [x]
    ring


                                                                   
                                                                  
                                                                    
theorem physicalModelPhase_actual_matrix_reference_roots_signed
    {σ δ T M N R L : ℝ} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (Mat : Fin 4 → ℤ) (e r : ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hLpos : 0 < L) (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hdet : Mat 0*Mat 3-Mat 1*Mat 2=1)
    (hgamma : |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2))
    (hwindow : modelPhaseThirdLower σ*L*R^2 ≤ 24*N^2)
    (hr : r ≠ 0) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=((rat 1).den:ℝ)/(rat 0).den →
    ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ) →
    (∀ i, x₀ i-L*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+L*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    |(e:ℝ)/r-(rat 0:ℝ)| ≤ modelPhaseThirdLower σ*L/(16*R^2) →
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    ∃ xref : Fin 2 → ℝ, ∀ i,
      0 < rp i*r ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
      iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
      |xref i-x₀ i| ≤ L*N ∧
      |(round (xref i):ℝ)-(round (x₀ i):ℝ)| ≤ L*N+1 := by
  intro f hlevel hMatt hMatmap hL hU hy ep rp
  by_cases hrpos : 0 < r
  · obtain ⟨xref,hxr⟩ := physicalModelPhase_actual_matrix_reference_roots Q K₀ rat Mat e r
      hσ hδ hF hT hM hN hR hLpos hQ hscale hmesh hA hW hx₀ hden
      hdet hgamma hwindow hrpos hlevel hMatt hMatmap hL hU hy
    refine ⟨xref,fun i => ⟨mul_pos (hxr i).1 hrpos,(hxr i).2⟩⟩
  · have hrneg : r < 0 := by omega
    have hr' : 0 < -r := neg_pos.mpr hrneg
    have hy' : ((-e:ℤ):ℝ)/(-r:ℤ)-(rat 0:ℝ) ∈
        Icc (-(modelPhaseThirdLower σ*L/(16*R^2))) (modelPhaseThirdLower σ*L/(16*R^2)) := by
      simpa only [Int.cast_neg,neg_div_neg_eq,Set.mem_Icc] using abs_le.mp hy
    obtain ⟨xref,hxr⟩ := physicalModelPhase_actual_matrix_reference_roots Q K₀ rat Mat (-e) (-r)
      hσ hδ hF hT hM hN hR hLpos hQ hscale hmesh hA hW hx₀ hden
      hdet hgamma hwindow hr' hlevel hMatt hMatmap hL hU (abs_le.mpr hy')
    have he i :
        (![ -e,Mat 0*(-e)+Mat 1*(-r)] : Fin 2 → ℤ) i= -ep i := by
      fin_cases i
      · rfl
      · change Mat 0*(-e)+Mat 1*(-r)= -(Mat 0*e+Mat 1*r)
        ring
    have hd i :
        (![ -r,Mat 2*(-e)+Mat 3*(-r)] : Fin 2 → ℤ) i= -rp i := by
      fin_cases i
      · rfl
      · change Mat 2*(-e)+Mat 3*(-r)= -(Mat 2*e+Mat 3*r)
        ring
    refine ⟨xref,?_⟩
    intro i
    have hi := hxr i
    rw [he,hd] at hi
    have hsign : 0 < rp i*r := mul_pos_of_neg_of_neg (neg_pos.mp hi.1) hrneg
    refine ⟨hsign,hi.2.1,?_,hi.2.2.2⟩
    simpa only [Int.cast_neg,neg_div_neg_eq] using hi.2.2.1

                                                                   
                                                                       
theorem inverseFarey_mem_interval_signed {e r v s l w x : ℝ}
    (hdet : v*r-e*s=1) (hl : 0 < r*l-e) (hw : 0 < r*w-e)
    (hx : x∈Icc l w) :
    (v-s*x)/(r*x-e)∈Icc ((v-s*w)/(r*w-e)) ((v-s*l)/(r*l-e)) := by
  have hxx : 0 < r*x-e := by
    rcases le_total 0 r with hr | hr
    · exact hl.trans_le (sub_le_sub_right (mul_le_mul_of_nonneg_left hx.1 hr) e)
    · exact hw.trans_le (sub_le_sub_right (mul_le_mul_of_nonpos_left hx.2 hr) e)
  have ha := inverseFarey_difference hdet hxx.ne' hw.ne'
  have hb := inverseFarey_difference hdet hl.ne' hxx.ne'
  have h₁ : 0 ≤ (w-x)/((r*x-e)*(r*w-e)) :=
    div_nonneg (sub_nonneg.mpr hx.2) (mul_pos hxx hw).le
  have h₂ : 0 ≤ (x-l)/((r*l-e)*(r*x-e)) :=
    div_nonneg (sub_nonneg.mpr hx.1) (mul_pos hl hxx).le
  exact ⟨by linarith only [ha,h₁],by linarith only [hb,h₂]⟩

                                                                
                                                              
                                                                        
                                                                
theorem completeSector_density_from_curvature_signed
    {e r v s : ℤ} {a : ℚ} {l w Q : ℝ}
    (hdet : v*r-e*s=1)
    (hlw : l < w) (hl : 0 < (r:ℝ)*l-e) (hw : 0 < (r:ℝ)*w-e)
    (hnw : 0 < (v:ℝ)-s*w)
    (ha : (a:ℝ) ∈ Set.Icc l w)
    (hdyad : max ((r:ℝ)*l-e) ((r:ℝ)*w-e) ≤ 2*min ((r:ℝ)*l-e) ((r:ℝ)*w-e))
    (hcut : 256*(a.den:ℝ) ≤ Q) (hscale : 256 ≤ (w-l)*Q*a.den) :
    let α := ((v:ℝ)-s*w)/((r:ℝ)*w-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊Q*min ((r:ℝ)*l-e) ((r:ℝ)*w-e)⌋₊
    max ((β-α)*(K:ℝ)^2/128:ℝ) 2 ≤ (HuxleyLinearForm.fareySector K α β).card ∧
      ∀ p ∈ HuxleyLinearForm.fareySector K α β,
        0 < (r:ℝ)*p.1+s*p.2 ∧ (r:ℝ)*p.1+s*p.2 ≤ Q ∧
        ((e:ℝ)*p.1+v*p.2)/((r:ℝ)*p.1+s*p.2) ∈ Set.Icc l w := by
  let dl := (r:ℝ)*l-e
  let dw := (r:ℝ)*w-e
  let α := ((v:ℝ)-s*w)/dw
  let β := ((v:ℝ)-s*l)/dl
  let dm := min dl dw
  let dx := max dl dw
  let K := ⌊Q*dm⌋₊
  let t : ℤ := r*a.num-e*a.den
  let b : ℚ := ((v*a.den-s*a.num:ℤ):ℚ)/((r*a.num-e*a.den:ℤ):ℚ)
  have hd : (v:ℝ)*r-e*s=1 := by exact_mod_cast hdet
  have hdl : 0 < dl := hl
  have hdw : 0 < dw := hw
  have hdm : 0 < dm := lt_min hdl hdw
  have hdx : 0 < dx := hdl.trans_le (le_max_left _ _)
  have hdyad' : dx ≤ 2*dm := hdyad
  have haRange : dm ≤ (r:ℝ)*(a:ℝ)-e ∧ (r:ℝ)*(a:ℝ)-e ≤ dx := by
    rcases le_total 0 (r:ℝ) with hr | hr
    · exact ⟨(min_le_left dl dw).trans
        (sub_le_sub_right (mul_le_mul_of_nonneg_left ha.1 hr) _),
        (sub_le_sub_right (mul_le_mul_of_nonneg_left ha.2 hr) _).trans (le_max_right dl dw)⟩
    · exact ⟨(min_le_right dl dw).trans
        (sub_le_sub_right (mul_le_mul_of_nonpos_left ha.2 hr) _),
        (sub_le_sub_right (mul_le_mul_of_nonpos_left ha.1 hr) _).trans (le_max_left dl dw)⟩
  have haDen : (0:ℝ) < a.den := by exact_mod_cast a.pos
  have hQ : 0 < Q := lt_of_lt_of_le (by positivity) hcut
  have hat : (a.num:ℝ)=(a:ℝ)*a.den := by
    have hh : (a:ℝ)=(a.num:ℝ)/a.den := by exact_mod_cast (Rat.num_div_den a).symm
    exact ((eq_div_iff haDen.ne').mp hh).symm
  have ht : (t:ℝ)=((r:ℝ)*(a:ℝ)-e)*a.den := by dsimp [t]; push_cast; rw [hat]; ring
  have htlo : dm*a.den ≤ (t:ℝ) := by
    rw [ht]
    exact mul_le_mul_of_nonneg_right haRange.1 haDen.le
  have hthi : (t:ℝ) ≤ dx*a.den := by
    rw [ht]
    exact mul_le_mul_of_nonneg_right haRange.2 haDen.le
  have htpos : 0 < t := by exact_mod_cast (lt_of_lt_of_le (mul_pos hdm haDen) htlo)
  have htone : (1:ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  obtain ⟨hbden,hbval⟩ := inverseFarey_rational_anchor hdet htpos
  change (b.den:ℤ)=t at hbden
  have hbdenR : (b.den:ℝ)=t := by exact_mod_cast hbden
  have hbI : (b:ℝ) ∈ Set.Icc α β := by
    rw [hbval]
    exact inverseFarey_mem_interval_signed hd hdl hdw ha
  have hwidth : β-α=(w-l)/(dm*dx) := by
    change β-α=(w-l)/(min dl dw*max dl dw)
    rw [min_mul_max]
    exact inverseFarey_difference hd hdl.ne' hdw.ne'
  have hα : 0 < α := div_pos hnw hdw
  have hαβ : α < β := by
    have hh : 0 < (w-l)/(dm*dx) := div_pos (sub_pos.mpr hlw) (mul_pos hdm hdx)
    linarith only [hwidth,hh]
  have hQdl : 2 ≤ Q*dm := by
    have h₁ := mul_le_mul_of_nonneg_right hdyad' haDen.le
    have h₂ := mul_le_mul_of_nonneg_right hcut hdm.le
    change dx*a.den ≤ 2*dm*a.den at h₁
    nlinarith only [htone,hthi,h₁,h₂]
  have hfloor : Q*dm/2 ≤ (K:ℝ) := by
    have hh := Nat.lt_floor_add_one (Q*dm)
    change Q*dm < (K:ℝ)+1 at hh
    linarith only [hh,hQdl]
  have hK : 64*b.den ≤ K := by
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    rw [hbdenR]
    have h₁ := mul_le_mul_of_nonneg_right hdyad' haDen.le
    have h₂ := mul_le_mul_of_nonneg_right hcut hdm.le
    change dx*a.den ≤ 2*dm*a.den at h₁
    nlinarith only [hfloor,hthi,h₁,h₂]
  have hscaled : 64 ≤ (β-α)*(K:ℝ)*b.den := by
    have h₁ : (w-l)*Q*a.den/4 ≤ (β-α)*(Q*dm/2)*(dm*a.den) := by
      rw [hwidth]
      have hid : (w-l)/(dm*dx)*(Q*dm/2)*(dm*a.den)=
          (w-l)*Q*a.den*dm/(2*dx) := by field_simp
      rw [hid]
      apply (le_div_iff₀ (by positivity)).mpr
      have hh := mul_le_mul_of_nonneg_left hdyad'
        (show 0 ≤ (w-l)*Q*a.den by positivity)
      nlinarith only [hh]
    have h₂ := mul_le_mul
      (mul_le_mul_of_nonneg_left hfloor (sub_nonneg.mpr hαβ.le)) htlo
      (by positivity : 0 ≤ dm*(a.den:ℝ)) (by positivity : 0 ≤ (β-α)*(K:ℝ))
    rw [hbdenR]
    linarith only [hscale,h₁,h₂]
  refine ⟨fareySector_source_density_gate hα hαβ hbI hK hscaled,?_⟩
  have hden (z : ℝ) (hz : (r:ℝ)*z-e ≠ 0) :
      (r:ℝ)*(((v:ℝ)-s*z)/((r:ℝ)*z-e))+s=1/((r:ℝ)*z-e) := by
    field_simp [hz]
    nlinarith only [hd]
  have hdenα : (r:ℝ)*α+s=1/dw := hden w hdw.ne'
  have hdenβ : (r:ℝ)*β+s=1/dl := hden l hdl.ne'
  have hmap (z : ℝ) (hz : (r:ℝ)*z-e ≠ 0) :
      ((e:ℝ)*(((v:ℝ)-s*z)/((r:ℝ)*z-e))+v)/
        ((r:ℝ)*(((v:ℝ)-s*z)/((r:ℝ)*z-e))+s)=z := by
    rw [hden z hz]
    rw [div_div_eq_mul_div,div_one,add_mul,mul_assoc,div_mul_cancel₀ _ hz]
    linear_combination z*hd
  intro p hp
  have hh := fareySector_curvature_targets (e := e) (v := v) hα hαβ.le
    (by rw [hdenα]; positivity) (by rw [hdenβ]; positivity) hp
  have hb := fareySector_denominator_bound hα hαβ.le
    (by rw [hdenα]; positivity) (by rw [hdenβ]; positivity) hp
  have hm : max ((r:ℝ)*α+s) ((r:ℝ)*β+s)=1/dm := by
    rw [hdenα,hdenβ]
    rcases le_total dl dw with hle | hle
    · rw [max_eq_right (one_div_le_one_div_of_le hdl hle)]
      exact congrArg (fun z : ℝ => 1/z) (min_eq_left hle).symm
    · rw [max_eq_left (one_div_le_one_div_of_le hdw hle)]
      exact congrArg (fun z : ℝ => 1/z) (min_eq_right hle).symm
  have hq : (r:ℝ)*p.1+s*p.2 ≤ Q := by
    rw [abs_of_pos hh.1,hm] at hb
    have hk : (K:ℝ) ≤ Q*dm := Nat.floor_le (mul_pos hQ hdm).le
    calc
      _ ≤ (K:ℝ)*(1/dm) := hb
      _ ≤ Q*dm*(1/dm) := mul_le_mul_of_nonneg_right hk (by positivity)
      _ = Q := by field_simp
  refine ⟨hh.1,hq,?_⟩
  simpa only [α,β,dw,dl,hmap w hdw.ne',hmap l hdl.ne',Set.uIcc_of_ge hlw.le] using hh.2

                                                                  
                                                                     
                                                                       
                                                                          
theorem physicalModelPhase_actual_fourier_complete_sector_fourth_signed
    {σ δ T M N R : ℝ} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2) (Mat : Fin 4 → ℤ) (anchor : ℚ) (e r v s : ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=(q 1:ℝ)/q 0 →
    ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let C := σ*(σ+1)+1
    let H := N/(C+2)
    let ε := modelPhaseThirdLower σ/(16*(C+2)*R^2)
    2 ≤ N →
    (∀ i, x₀ i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    v*r-e*s=1 →
    0 < (r:ℝ)*((rat 0:ℝ)-ε)-e →
    0 < (r:ℝ)*((rat 0:ℝ)+ε)-e →
    0 < (v:ℝ)-s*((rat 0:ℝ)+ε) →
    max ((r:ℝ)*((rat 0:ℝ)-ε)-e) ((r:ℝ)*((rat 0:ℝ)+ε)-e) ≤
      2*min ((r:ℝ)*((rat 0:ℝ)-ε)-e) ((r:ℝ)*((rat 0:ℝ)+ε)-e) →
    |(anchor:ℝ)-(rat 0:ℝ)| ≤ ε →
    256*(anchor.den:ℝ) ≤ (Q:ℝ)/3 →
    256 ≤ (2*ε)*((Q:ℝ)/3)*anchor.den →
    let l := (rat 0:ℝ)-ε
    let w' := (rat 0:ℝ)+ε
    let α := ((v:ℝ)-s*w')/((r:ℝ)*w'-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊((Q:ℝ)/3)*min ((r:ℝ)*l-e) ((r:ℝ)*w'-e)⌋₊
    let S := HuxleyLinearForm.fareySector K α β
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let κ := modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    max ((β-α)*(K:ℝ)^2/128:ℝ) 2 ≤ S.card ∧
    ∃ ξ : ℝ → Fin 2 → ℝ, ∀ p∈S,
      let a := e*p.1+v*p.2
      let d := r*p.1+s*p.2
      let x₁ := ξ ((p.1:ℝ)/p.2)
      let anew : Fin 2 → ℤ := ![a,Mat 0*a+Mat 1*d]
      let qnew : Fin 2 → ℤ := ![d,Mat 2*a+Mat 3*d]
      let z := fun i => (qnew i:ℝ)*deriv (f i) (round (x₁ i))
      (∀ i, x₁ i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (x₁ i)/2=(anew i:ℝ)/qnew i ∧
        |x₁ i-x₀ i| ≤ H ∧ 0 < (qnew i:ℝ) ∧ (qnew i:ℝ) ≤ Q) ∧
      |(z 0-z 1)-round (z 0-z 1)| ≤ Δ ∧
      (Δ < 1/2 →
        ∃ cnew∈minorArcCenterLabels (z 0) Δ,
          ∃ cnew₁∈minorArcCenterLabels (z 1) Δ,
          cnew=round (z 0) ∧ |(z 0-cnew)-(z 1-cnew₁)| ≤ Δ ∧
          ∃ p₀ p₁ : Fin 2, cnew=⌊z 0⌋+(p₀:ℕ) ∧ cnew₁=⌊z 1⌋+(p₁:ℕ)) := by
  classical
  intro f hlevel q mu ell b cround tau dual w radius hcolor hnear c J B
    hsmall hNR hRN hcube hminscale hMatdet hMatt hMatmap hMatgamma
    C H ε hNtwo hL hU hchart hdl hdw hnum hdyad hanchor hcut hcount
    l w' α β K S C₂ C₃ κ Ct Cc Δ
  obtain ⟨hε,ρ,hρ⟩ := physicalModelPhase_actual_fourier_matrix_root_fourth
    Q K₀ rat vinv parity Mat hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW
    hx₀ hden hinv hlevel hcolor hnear hsmall hNR hRN hcube hminscale
    hMatdet hMatt hMatmap hMatgamma hNtwo hL hU
  have hε' : 0 < ε := hε
  have hlw : l < w' := by dsimp only [l,w']; linarith only [hε']
  have ha : (anchor:ℝ)∈Icc l w' := by
    have hh := abs_le.mp hanchor
    exact ⟨by dsimp only [l]; linarith only [hh.1],
      by dsimp only [w']; linarith only [hh.2]⟩
  have hcount' : 256 ≤ (w'-l)*((Q:ℝ)/3)*anchor.den := by
    simpa only [show w'-l=2*ε by dsimp only [w',l]; ring] using hcount
  obtain ⟨hcard,htarget⟩ := completeSector_density_from_curvature_signed
    hchart hlw hdl hdw hnum ha hdyad hcut hcount'
  let ξ := fun y => ρ (((e:ℝ)*y+v)/((r:ℝ)*y+s))
  refine ⟨hcard,ξ,?_⟩
  intro p hp a d x₁ anew qnew z
  have ht := htarget p hp
  have hd : 0 < (d:ℝ) := by
    simpa only [d,Int.cast_add,Int.cast_mul] using ht.1
  have hdQ : (d:ℝ) ≤ (Q:ℝ)/3 := by
    simpa only [d,Int.cast_add,Int.cast_mul] using ht.2.1
  have hy : |(a:ℝ)/d-(rat 0:ℝ)| ≤ ε := by
    have hI : (a:ℝ)/d∈Icc l w' := by
      simpa only [a,d,Int.cast_add,Int.cast_mul] using ht.2.2
    exact abs_le.mpr ⟨by dsimp only [l] at hI; linarith only [hI.1],
      by dsimp only [w'] at hI; linarith only [hI.2]⟩
  have hα : 0 < α := div_pos hnum hdw
  have hαβ : α ≤ β := by
    have hc : (v:ℝ)*r-e*s=1 := by exact_mod_cast hchart
    have hh := inverseFarey_difference hc hdl.ne' hdw.ne'
    change β-α=(w'-l)/(((r:ℝ)*l-e)*((r:ℝ)*w'-e)) at hh
    have hp' : 0 ≤ (w'-l)/(((r:ℝ)*l-e)*((r:ℝ)*w'-e)) := by positivity
    linarith only [hh,hp']
  obtain ⟨hpt,_,_,_,_⟩ :=
    (HuxleyLinearForm.mem_fareySector_iff hα (hα.le.trans hαβ)).mp hp
  have htpos : (0:ℝ) < p.2 := by exact_mod_cast (show 0 < p.2 by omega)
  have hfrac : ((e:ℝ)*((p.1:ℝ)/p.2)+v)/((r:ℝ)*((p.1:ℝ)/p.2)+s)=(a:ℝ)/d := by
    have hn : (e:ℝ)*((p.1:ℝ)/p.2)+v=(a:ℝ)/(p.2:ℝ) := by
      dsimp only [a]; push_cast; field_simp
    have hdn : (r:ℝ)*((p.1:ℝ)/p.2)+s=(d:ℝ)/(p.2:ℝ) := by
      dsimp only [d]; push_cast; field_simp
    rw [hn,hdn,div_div_div_cancel_right₀ htpos.ne']
  have hx : x₁=ρ ((a:ℝ)/d) := by
    change ρ (((e:ℝ)*((p.1:ℝ)/p.2)+v)/((r:ℝ)*((p.1:ℝ)/p.2)+s))=_
    rw [hfrac]
  have hh := hρ a d hd hdQ hy
  simpa only [z,hx] using hh

                                                                        
                                                                          
                                                                  
theorem inverseFarey_original_seed_enlarged_rectangle_signed
    {e r v s : ℤ} {anchor seed : ℚ} {l w Q : ℝ}
    (hdet : v*r-e*s=1)
    (hl : 0 < (r:ℝ)*l-e) (hw : 0 < (r:ℝ)*w-e)
    (hnw : 0 < (v:ℝ)-s*w)
    (ha : (anchor:ℝ)∈Icc l w) (hseed : (seed:ℝ)∈Icc l w)
    (hdyad : max ((r:ℝ)*l-e) ((r:ℝ)*w-e) ≤ 2*min ((r:ℝ)*l-e) ((r:ℝ)*w-e))
    (hcut : 256*(anchor.den:ℝ) ≤ Q/3) (hseedQ : (seed.den:ℝ) ≤ Q) :
    let α := ((v:ℝ)-s*w)/((r:ℝ)*w-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊(Q/3)*min ((r:ℝ)*l-e) ((r:ℝ)*w-e)⌋₊
    let p : ℤ × ℤ := (v*seed.den-s*seed.num,r*seed.num-e*seed.den)
    0 < (p.2:ℝ) ∧ (p.1:ℝ)/p.2∈Icc α β ∧
      0 ≤ (p.1:ℝ) ∧ (p.1:ℝ) ≤ 12*(β*(K:ℝ)) ∧
      (p.2:ℝ) ≤ 12*(K:ℝ) := by
  intro α β K p
  let dl := (r:ℝ)*l-e
  let dw := (r:ℝ)*w-e
  let dm := min dl dw
  let dx := max dl dw
  have hd : (v:ℝ)*r-e*s=1 := by exact_mod_cast hdet
  have hdm : 0 < dm := lt_min hl hw
  have hdx : 0 < dx := hl.trans_le (le_max_left _ _)
  have hdyad' : dx ≤ 2*dm := hdyad
  have hRange (z : ℝ) (hz : z∈Icc l w) :
      dm ≤ (r:ℝ)*z-e ∧ (r:ℝ)*z-e ≤ dx := by
    rcases le_total 0 (r:ℝ) with hr | hr
    · exact ⟨(min_le_left dl dw).trans
        (sub_le_sub_right (mul_le_mul_of_nonneg_left hz.1 hr) _),
        (sub_le_sub_right (mul_le_mul_of_nonneg_left hz.2 hr) _).trans (le_max_right dl dw)⟩
    · exact ⟨(min_le_right dl dw).trans
        (sub_le_sub_right (mul_le_mul_of_nonpos_left hz.2 hr) _),
        (sub_le_sub_right (mul_le_mul_of_nonpos_left hz.1 hr) _).trans (le_max_left dl dw)⟩
  have hden (a : ℚ) : (0:ℝ) < a.den := by exact_mod_cast a.pos
  have hnum (a : ℚ) : (a.num:ℝ)=(a:ℝ)*a.den := by
    have hh : (a:ℝ)=(a.num:ℝ)/a.den := by exact_mod_cast (Rat.num_div_den a).symm
    exact ((eq_div_iff (hden a).ne').mp hh).symm
  have hQ : 0 < Q := by nlinarith only [hcut,hden anchor]
  let t : ℤ := r*anchor.num-e*anchor.den
  have ht : (t:ℝ)=((r:ℝ)*(anchor:ℝ)-e)*anchor.den := by
    dsimp only [t]; push_cast; rw [hnum]; ring
  have htlo : dm*anchor.den ≤ (t:ℝ) := by
    rw [ht]
    exact mul_le_mul_of_nonneg_right (hRange _ ha).1 (hden anchor).le
  have hthi : (t:ℝ) ≤ dx*anchor.den := by
    rw [ht]
    exact mul_le_mul_of_nonneg_right (hRange _ ha).2 (hden anchor).le
  have htpos : 0 < t := by
    exact_mod_cast (lt_of_lt_of_le (mul_pos hdm (hden anchor)) htlo)
  have htone : (1:ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have hQdm : 2 ≤ (Q/3)*dm := by
    have h₁ := mul_le_mul_of_nonneg_right hdyad' (hden anchor).le
    have h₂ := mul_le_mul_of_nonneg_right hcut hdm.le
    change dx*anchor.den ≤ 2*dm*anchor.den at h₁
    nlinarith only [htone,hthi,h₁,h₂]
  have hfloor : (Q/3)*dm/2 ≤ (K:ℝ) := by
    have hh := Nat.lt_floor_add_one ((Q/3)*dm)
    change (Q/3)*dm < (K:ℝ)+1 at hh
    linarith only [hh,hQdm]
  have hpden : (p.2:ℝ)=((r:ℝ)*(seed:ℝ)-e)*seed.den := by
    dsimp only [p]; push_cast; rw [hnum]; ring
  have hseedden : 0 < (r:ℝ)*(seed:ℝ)-e := hdm.trans_le (hRange _ hseed).1
  have hpt : 0 < (p.2:ℝ) := by rw [hpden]; exact mul_pos hseedden (hden seed)
  have hpthi : (p.2:ℝ) ≤ dx*seed.den := by
    rw [hpden]
    exact mul_le_mul_of_nonneg_right (hRange _ hseed).2 (hden seed).le
  have hpK : (p.2:ℝ) ≤ 12*(K:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hseedQ hdx.le
    have hy := mul_le_mul_of_nonneg_right hdyad' hQ.le
    change dx*Q ≤ 2*dm*Q at hy
    nlinarith only [hpthi,hh,hy,hfloor]
  have hfrac : (p.1:ℝ)/p.2=
      ((v:ℝ)-s*(seed:ℝ))/((r:ℝ)*(seed:ℝ)-e) := by
    rw [hpden]
    have hpnum : (p.1:ℝ)=((v:ℝ)-s*(seed:ℝ))*seed.den := by
      dsimp only [p]; push_cast; rw [hnum]; ring
    rw [hpnum,mul_div_mul_right _ _ (hden seed).ne']
  have hpI : (p.1:ℝ)/p.2∈Icc α β := by
    rw [hfrac]
    exact inverseFarey_mem_interval_signed hd hl hw hseed
  have hα : 0 < α := div_pos hnw hw
  have hβ : 0 ≤ β := hα.le.trans (hpI.1.trans hpI.2)
  have hp0 : 0 ≤ (p.1:ℝ) := by
    have hh := (le_div_iff₀ hpt).mp hpI.1
    exact (mul_nonneg hα.le hpt.le).trans hh
  have hphi := (div_le_iff₀ hpt).mp hpI.2
  refine ⟨hpt,hpI,hp0,?_,hpK⟩
  calc
    _ ≤ β*(p.2:ℝ) := hphi
    _ ≤ β*(12*(K:ℝ)) := mul_le_mul_of_nonneg_left hpK hβ
    _ = _ := by ring

                                                                      
                                                                       
                                                                   
                                             
theorem physicalModelPhase_farey_common_cell_selection_signed
    (S : Finset ℕ) (Z : Finset ℝ) (x : ℕ → ℝ)
    {σ δ T M A W N R base ε e r v s l w : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hphase : T*N*R^2=M^3)
    (hsmall : 4*ε*R^2 ≤ modelPhaseThirdLower σ) (hε : 0 ≤ ε)
    (hdet : v*r-e*s=1) (hZ : Z.card ≤ 16)
    (hx : ∀ j∈S, x j∈Ioo 0 W)
    (hwindow : ∀ j∈S, x j∈Icc (base+(j:ℝ)*N) (base+((j:ℝ)+1)*N))
    (hregion : ∀ z∈Icc l w, 0 < r*z+s) :
    let f := heathBrownPhysicalPhase F T M A 1
    let q := fun j => iteratedDeriv 2 f (x j)/2
    let α := fun j => (v-s*(q j+ε))/(r*(q j+ε)-e)
    let β := fun j => (v-s*(q j-ε))/(r*(q j-ε)-e)
    (∀ j∈S, 0 < r*(q j-ε)-e ∧ 0 < r*(q j+ε)-e) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    ∃ (k : Fin 17) (E : Finset ℕ), E⊆S ∧ S.card ≤ 48+17*E.card ∧
      ∀ j∈E, α j∈finiteBoundaryCell Z l w k ∧ β j∈finiteBoundaryCell Z l w k := by
  classical
  intro f q α β hcharts hends
  have hchart j (hj : j∈S) := (hcharts j hj).1
  have hchart' j (hj : j∈S) := (hcharts j hj).2
  have hab j (hj : j∈S) : α j ≤ β j := by
    have hh := inverseFarey_difference hdet (hchart j hj).ne' (hchart' j hj).ne'
    have hn : 0 ≤ ((q j+ε)-(q j-ε))/((r*(q j-ε)-e)*(r*(q j+ε)-e)) :=
      div_nonneg (by linarith only [hε]) (mul_pos (hchart j hj) (hchart' j hj)).le
    change (v-s*(q j+ε))/(r*(q j+ε)-e) ≤ (v-s*(q j-ε))/(r*(q j-ε)-e)
    linarith only [hh,hn]
  let ZI := Z.filter (fun z => z∈Icc l w)
  let bad := fun j => ∃ z∈Z, z∈Icc (α j) (β j)
  let good := S.filter (fun j => ¬bad j)
  have hbad : (S.filter bad).card ≤ 48 := by
    have hh := physicalModelPhase_farey_boundary_crossing_count S ZI x (v:=v)
      hσ hδ hF hT hM hN hR hA hW hphase hsmall hx hwindow
      (fun z hz => hregion z (Finset.mem_filter.mp hz).2)
      (fun j hj => ⟨hchart j hj,hchart' j hj⟩)
    have he : S.filter bad=S.filter (fun j => ∃ z∈ZI, z∈Icc (α j) (β j)) := by
      ext j
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hj,z,hz,hza,hzb⟩
        refine ⟨hj,z,Finset.mem_filter.mpr ⟨hz,?_⟩,hza,hzb⟩
        exact ⟨(hends j hj).1.1.trans hza,hzb.trans (hends j hj).2.2⟩
      · rintro ⟨hj,z,hz,hzz⟩
        exact ⟨hj,z,(Finset.mem_filter.mp hz).1,hzz⟩
    rw [he]
    change (S.filter (fun j => ∃ z∈ZI, z∈Icc (α j) (β j))).card ≤ 3*ZI.card at hh
    have hc : ZI.card ≤ 16 := (Finset.card_filter_le _ _).trans hZ
    omega
  let color : ℕ → Fin 17 := fun j =>
    ⟨(Z.filter (fun z => z<α j)).card,lt_of_le_of_lt (Finset.card_filter_le _ _) (by omega)⟩
  have hbudget : (Finset.univ : Finset (Fin 17)).card • ((good.card:ℝ)/17) ≤ (good.card:ℝ) := by
    simp only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    norm_num
    linarith
  obtain ⟨k,_hk,hcount⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (fun j (_hj : j∈good) => Finset.mem_univ (color j)) Finset.univ_nonempty hbudget
  let E := good.filter (fun j => color j=k)
  have hmass : good.card ≤ 17*E.card := by
    have hh : (good.card:ℝ) ≤ 17*(E.card:ℝ) := by
      change (good.card:ℝ)/17 ≤ (E.card:ℝ) at hcount
      linarith only [hcount]
    exact_mod_cast hh
  have hES : E⊆S := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  refine ⟨k,E,hES,?_,?_⟩
  · have he := Finset.card_filter_add_card_filter_not (s:=S) bad
    change (S.filter bad).card+good.card=S.card at he
    omega
  · intro j hj
    have hjG := (Finset.mem_filter.mp hj).1
    have hjS := (Finset.mem_filter.mp hjG).1
    have hn := (Finset.mem_filter.mp hjG).2
    have haZ : α j∉Z := by
      intro hz
      exact hn ⟨α j,hz,le_rfl,hab j hjS⟩
    have hbZ : β j∉Z := by
      intro hz
      exact hn ⟨β j,hz,hab j hjS,le_rfl⟩
    have he : Z.filter (fun z => z<α j)=Z.filter (fun z => z<β j) := by
      ext z
      simp only [Finset.mem_filter]
      constructor
      · intro hz
        exact ⟨hz.1,hz.2.trans_le (hab j hjS)⟩
      · intro hz
        refine ⟨hz.1,?_⟩
        by_contra hnot
        exact hn ⟨z,hz.1,le_of_not_gt hnot,hz.2.le⟩
    have hc : (Z.filter (fun z => z<α j)).card=k.val :=
      congrArg Fin.val (Finset.mem_filter.mp hj).2
    exact ⟨⟨(hends j hjS).1,haZ,hc⟩,
      ⟨(hends j hjS).2,hbZ,by rw [←he]; exact hc⟩⟩

                                                                
                                                                      
                                                                
theorem completeNegativeSector_density_from_curvature
    {e r v s : ℤ} {a : ℚ} {l w Q : ℝ}
    (hdet : v*r-e*s=1)
    (hlw : l < w) (hl : 0 < (r:ℝ)*l-e) (hw : 0 < (r:ℝ)*w-e)
    (hnl : (v:ℝ)-s*l < 0)
    (ha : (a:ℝ) ∈ Set.Icc l w)
    (hdyad : max ((r:ℝ)*l-e) ((r:ℝ)*w-e) ≤ 2*min ((r:ℝ)*l-e) ((r:ℝ)*w-e))
    (hcut : 256*(a.den:ℝ) ≤ Q) (hscale : 256 ≤ (w-l)*Q*a.den) :
    let α := ((v:ℝ)-s*w)/((r:ℝ)*w-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊Q*min ((r:ℝ)*l-e) ((r:ℝ)*w-e)⌋₊
    let P := HuxleyLinearForm.fareySector K (-β) (-α)
    let S := P.image (fun p : ℤ × ℤ => (-p.1,p.2))
    max ((β-α)*(K:ℝ)^2/128:ℝ) 2 ≤ S.card ∧
      ∀ p ∈ S,
        0 < (r:ℝ)*p.1+s*p.2 ∧ (r:ℝ)*p.1+s*p.2 ≤ Q ∧
        ((e:ℝ)*p.1+v*p.2)/((r:ℝ)*p.1+s*p.2) ∈ Set.Icc l w := by
  classical
  intro α β K P S
  have hd : (-v)*(-r)-e*s=1 := by nlinarith only [hdet]
  have hdl : 0 < ((-r:ℤ):ℝ)*(-w)-e := by
    simpa only [Int.cast_neg,neg_mul_neg] using hw
  have hdw : 0 < ((-r:ℤ):ℝ)*(-l)-e := by
    simpa only [Int.cast_neg,neg_mul_neg] using hl
  have hn : 0 < ((-v:ℤ):ℝ)-s*(-l) := by
    push_cast
    nlinarith only [hnl]
  have ha' : ((-a:ℚ):ℝ)∈Icc (-w) (-l) := by
    simp only [Rat.cast_neg,Set.mem_Icc]
    exact ⟨neg_le_neg ha.2,neg_le_neg ha.1⟩
  have hdyad' : max (((-r:ℤ):ℝ)*(-w)-e) (((-r:ℤ):ℝ)*(-l)-e) ≤
      2*min (((-r:ℤ):ℝ)*(-w)-e) (((-r:ℤ):ℝ)*(-l)-e) := by
    simpa only [Int.cast_neg,neg_mul_neg,max_comm,min_comm] using hdyad
  have hcut' : 256*((-a).den:ℝ) ≤ Q := by simpa only [Rat.neg_den] using hcut
  have hscale' : 256 ≤ ((-l)-(-w))*Q*(-a).den := by
    simpa only [Rat.neg_den,show (-l)-(-w)=w-l by ring] using hscale
  have hh := completeSector_density_from_curvature_signed hd
    (neg_lt_neg hlw) hdl hdw hn ha' hdyad' hcut' hscale'
  have hα : (((-v:ℤ):ℝ)-s*(-l))/(((-r:ℤ):ℝ)*(-l)-e) = -β := by
    dsimp only [β]
    push_cast
    ring
  have hβ : (((-v:ℤ):ℝ)-s*(-w))/(((-r:ℤ):ℝ)*(-w)-e) = -α := by
    dsimp only [α]
    push_cast
    ring
  have hK : ⌊Q*min (((-r:ℤ):ℝ)*(-w)-e) (((-r:ℤ):ℝ)*(-l)-e)⌋₊ = K := by
    simp only [Int.cast_neg,neg_mul_neg,min_comm,K]
  dsimp only at hh
  rw [hα,hβ,hK] at hh
  have hinj : Function.Injective (fun p : ℤ × ℤ => (-p.1,p.2)) := by
    intro p q hpq
    have h₁ := congrArg Prod.fst hpq
    have h₂ := congrArg Prod.snd hpq
    exact Prod.ext (neg_injective h₁) h₂
  have hcard : S.card=P.card := Finset.card_image_of_injective P hinj
  refine ⟨?_,?_⟩
  · rw [hcard]
    simpa only [show (-α)-(-β)=β-α by ring] using hh.1
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    have hq' := hh.2 q hq
    simp only [Int.cast_neg,neg_mul] at hq'
    refine ⟨?_,?_,?_⟩
    · simpa only [Int.cast_neg,mul_neg,neg_mul] using hq'.1
    · simpa only [Int.cast_neg,mul_neg,neg_mul] using hq'.2.1
    · have heq : ((e:ℝ)*(-q.1:ℤ)+v*q.2)/((r:ℝ)*(-q.1:ℤ)+s*q.2) =
          -(((e:ℝ)*q.1+ -(v:ℝ)*q.2)/(-(r:ℝ)*q.1+s*q.2)) := by
        push_cast
        ring
      rw [heq]
      constructor
      · simpa only [neg_neg,neg_mul] using neg_le_neg hq'.2.2.2
      · simpa only [neg_neg,neg_mul] using neg_le_neg hq'.2.2.1

                                                                     
                                                                        
                                                                    
                                      
theorem physicalModelPhase_actual_fourier_complete_negative_sector_fourth
    {σ δ T M N R : ℝ} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2) (Mat : Fin 4 → ℤ) (anchor : ℚ) (e r v s : ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=(q 1:ℝ)/q 0 →
    ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let C := σ*(σ+1)+1
    let H := N/(C+2)
    let ε := modelPhaseThirdLower σ/(16*(C+2)*R^2)
    2 ≤ N →
    (∀ i, x₀ i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    v*r-e*s=1 →
    0 < (r:ℝ)*((rat 0:ℝ)-ε)-e →
    0 < (r:ℝ)*((rat 0:ℝ)+ε)-e →
    (v:ℝ)-s*((rat 0:ℝ)-ε) < 0 →
    max ((r:ℝ)*((rat 0:ℝ)-ε)-e) ((r:ℝ)*((rat 0:ℝ)+ε)-e) ≤
      2*min ((r:ℝ)*((rat 0:ℝ)-ε)-e) ((r:ℝ)*((rat 0:ℝ)+ε)-e) →
    |(anchor:ℝ)-(rat 0:ℝ)| ≤ ε →
    256*(anchor.den:ℝ) ≤ (Q:ℝ)/3 →
    256 ≤ (2*ε)*((Q:ℝ)/3)*anchor.den →
    let l := (rat 0:ℝ)-ε
    let w' := (rat 0:ℝ)+ε
    let α := ((v:ℝ)-s*w')/((r:ℝ)*w'-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊((Q:ℝ)/3)*min ((r:ℝ)*l-e) ((r:ℝ)*w'-e)⌋₊
    let S := (HuxleyLinearForm.fareySector K (-β) (-α)).image
      (fun p : ℤ × ℤ => (-p.1,p.2))
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let κ := modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    max ((β-α)*(K:ℝ)^2/128:ℝ) 2 ≤ S.card ∧
    ∃ ξ : ℝ → Fin 2 → ℝ, ∀ p∈S,
      let a := e*p.1+v*p.2
      let d := r*p.1+s*p.2
      let x₁ := ξ ((p.1:ℝ)/p.2)
      let anew : Fin 2 → ℤ := ![a,Mat 0*a+Mat 1*d]
      let qnew : Fin 2 → ℤ := ![d,Mat 2*a+Mat 3*d]
      let z := fun i => (qnew i:ℝ)*deriv (f i) (round (x₁ i))
      (∀ i, x₁ i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (x₁ i)/2=(anew i:ℝ)/qnew i ∧
        |x₁ i-x₀ i| ≤ H ∧ 0 < (qnew i:ℝ) ∧ (qnew i:ℝ) ≤ Q) ∧
      |(z 0-z 1)-round (z 0-z 1)| ≤ Δ ∧
      (Δ < 1/2 →
        ∃ cnew∈minorArcCenterLabels (z 0) Δ,
          ∃ cnew₁∈minorArcCenterLabels (z 1) Δ,
          cnew=round (z 0) ∧ |(z 0-cnew)-(z 1-cnew₁)| ≤ Δ ∧
          ∃ p₀ p₁ : Fin 2, cnew=⌊z 0⌋+(p₀:ℕ) ∧ cnew₁=⌊z 1⌋+(p₁:ℕ)) := by
  classical
  intro f hlevel q mu ell b cround tau dual w radius hcolor hnear c J B
    hsmall hNR hRN hcube hminscale hMatdet hMatt hMatmap hMatgamma
    C H ε hNtwo hL hU hchart hdl hdw hnum hdyad hanchor hcut hcount
    l w' α β K S C₂ C₃ κ Ct Cc Δ
  obtain ⟨hε,ρ,hρ⟩ := physicalModelPhase_actual_fourier_matrix_root_fourth
    Q K₀ rat vinv parity Mat hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW
    hx₀ hden hinv hlevel hcolor hnear hsmall hNR hRN hcube hminscale
    hMatdet hMatt hMatmap hMatgamma hNtwo hL hU
  have hε' : 0 < ε := hε
  have hlw : l < w' := by dsimp only [l,w']; linarith only [hε']
  have ha : (anchor:ℝ)∈Icc l w' := by
    have hh := abs_le.mp hanchor
    exact ⟨by dsimp only [l]; linarith only [hh.1],
      by dsimp only [w']; linarith only [hh.2]⟩
  have hcount' : 256 ≤ (w'-l)*((Q:ℝ)/3)*anchor.den := by
    simpa only [show w'-l=2*ε by dsimp only [w',l]; ring] using hcount
  obtain ⟨hcard,htarget⟩ := completeNegativeSector_density_from_curvature
    hchart hlw hdl hdw hnum ha hdyad hcut hcount'
  let ξ := fun y => ρ (((e:ℝ)*y+v)/((r:ℝ)*y+s))
  refine ⟨hcard,ξ,?_⟩
  intro p hp a d x₁ anew qnew z
  have ht := htarget p hp
  have hd : 0 < (d:ℝ) := by
    simpa only [d,Int.cast_add,Int.cast_mul] using ht.1
  have hdQ : (d:ℝ) ≤ (Q:ℝ)/3 := by
    simpa only [d,Int.cast_add,Int.cast_mul] using ht.2.1
  have hy : |(a:ℝ)/d-(rat 0:ℝ)| ≤ ε := by
    have hI : (a:ℝ)/d∈Icc l w' := by
      simpa only [a,d,Int.cast_add,Int.cast_mul] using ht.2.2
    exact abs_le.mpr ⟨by dsimp only [l] at hI; linarith only [hI.1],
      by dsimp only [w'] at hI; linarith only [hI.2]⟩
  have htpos : (0:ℝ) < p.2 := by
    obtain ⟨p',hp',he⟩ := Finset.mem_image.mp hp
    have ht : 1 ≤ p'.2 :=
      (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp').1).2).1
    have he' := congrArg Prod.snd he
    change p'.2=p.2 at he'
    rw [←he']
    exact_mod_cast (show 0 < p'.2 by omega)
  have hfrac : ((e:ℝ)*((p.1:ℝ)/p.2)+v)/((r:ℝ)*((p.1:ℝ)/p.2)+s)=(a:ℝ)/d := by
    have hn : (e:ℝ)*((p.1:ℝ)/p.2)+v=(a:ℝ)/(p.2:ℝ) := by
      dsimp only [a]; push_cast; field_simp
    have hdn : (r:ℝ)*((p.1:ℝ)/p.2)+s=(d:ℝ)/(p.2:ℝ) := by
      dsimp only [d]; push_cast; field_simp
    rw [hn,hdn,div_div_div_cancel_right₀ htpos.ne']
  have hx : x₁=ρ ((a:ℝ)/d) := by
    change ρ (((e:ℝ)*((p.1:ℝ)/p.2)+v)/((r:ℝ)*((p.1:ℝ)/p.2)+s))=_
    rw [hfrac]
  have hh := hρ a d hd hdQ hy
  simpa only [z,hx] using hh

                                                               
                                                                   
theorem inverseFarey_negative_original_seed_enlarged_rectangle
    {e r v s : ℤ} {anchor seed : ℚ} {l w Q : ℝ}
    (hdet : v*r-e*s=1)
    (hl : 0 < (r:ℝ)*l-e) (hw : 0 < (r:ℝ)*w-e)
    (hnl : (v:ℝ)-s*l < 0)
    (ha : (anchor:ℝ)∈Icc l w) (hseed : (seed:ℝ)∈Icc l w)
    (hdyad : max ((r:ℝ)*l-e) ((r:ℝ)*w-e) ≤ 2*min ((r:ℝ)*l-e) ((r:ℝ)*w-e))
    (hcut : 256*(anchor.den:ℝ) ≤ Q/3) (hseedQ : (seed.den:ℝ) ≤ Q) :
    let α := ((v:ℝ)-s*w)/((r:ℝ)*w-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊(Q/3)*min ((r:ℝ)*l-e) ((r:ℝ)*w-e)⌋₊
    let p : ℤ × ℤ := (v*seed.den-s*seed.num,r*seed.num-e*seed.den)
    0 < (p.2:ℝ) ∧ (p.1:ℝ)/p.2∈Icc α β ∧
      0 ≤ -(p.1:ℝ) ∧ -(p.1:ℝ) ≤ 12*((-α)*(K:ℝ)) ∧
      (p.2:ℝ) ≤ 12*(K:ℝ) := by
  intro α β K p
  have hd : (-v)*(-r)-e*s=1 := by nlinarith only [hdet]
  have hdl : 0 < ((-r:ℤ):ℝ)*(-w)-e := by
    simpa only [Int.cast_neg,neg_mul_neg] using hw
  have hdw : 0 < ((-r:ℤ):ℝ)*(-l)-e := by
    simpa only [Int.cast_neg,neg_mul_neg] using hl
  have hn : 0 < ((-v:ℤ):ℝ)-s*(-l) := by
    push_cast
    nlinarith only [hnl]
  have hmem (z : ℚ) (hz : (z:ℝ)∈Icc l w) :
      ((-z:ℚ):ℝ)∈Icc (-w) (-l) := by
    simp only [Rat.cast_neg,Set.mem_Icc]
    exact ⟨neg_le_neg hz.2,neg_le_neg hz.1⟩
  have hdyad' : max (((-r:ℤ):ℝ)*(-w)-e) (((-r:ℤ):ℝ)*(-l)-e) ≤
      2*min (((-r:ℤ):ℝ)*(-w)-e) (((-r:ℤ):ℝ)*(-l)-e) := by
    simpa only [Int.cast_neg,neg_mul_neg,max_comm,min_comm] using hdyad
  have hc : 256*((-anchor).den:ℝ) ≤ Q/3 := by simpa only [Rat.neg_den] using hcut
  have hs : ((-seed).den:ℝ) ≤ Q := by simpa only [Rat.neg_den] using hseedQ
  have hh := inverseFarey_original_seed_enlarged_rectangle_signed hd hdl hdw hn
    (hmem anchor ha) (hmem seed hseed) hdyad' hc hs
  have hα : (((-v:ℤ):ℝ)-s*(-l))/(((-r:ℤ):ℝ)*(-l)-e) = -β := by
    dsimp only [β]
    push_cast
    ring
  have hβ : (((-v:ℤ):ℝ)-s*(-w))/(((-r:ℤ):ℝ)*(-w)-e) = -α := by
    dsimp only [α]
    push_cast
    ring
  have hK : ⌊(Q/3)*min (((-r:ℤ):ℝ)*(-w)-e) (((-r:ℤ):ℝ)*(-l)-e)⌋₊ = K := by
    simp only [Int.cast_neg,neg_mul_neg,min_comm,K]
  have hp : ((-v)*(-seed).den-s*(-seed).num,(-r)*(-seed).num-e*(-seed).den) =
      (-p.1,p.2) := by
    dsimp only [p]
    simp only [Rat.neg_den,Rat.neg_num]
    apply Prod.ext <;> dsimp <;> ring
  dsimp only at hh
  have hp₁ := congrArg Prod.fst hp
  have hp₂ := congrArg Prod.snd hp
  dsimp only at hp₁ hp₂
  rw [hα,hβ,hK,hp₁,hp₂] at hh
  simp only [Int.cast_neg,neg_div] at hh
  refine ⟨hh.1,?_,hh.2.2⟩
  exact ⟨by linarith only [hh.2.1.2],by linarith only [hh.2.1.1]⟩

theorem mem_negative_fareySector_iff {N : ℕ} {l w : ℝ} {p : ℤ × ℤ}
    (hw : w < 0) (hlw : l ≤ w) :
    p ∈ (HuxleyLinearForm.fareySector N (-w) (-l)).image
      (fun q : ℤ × ℤ => (-q.1,q.2)) ↔
      1 ≤ p.2 ∧ p.2 ≤ N ∧ IsCoprime p.1 p.2 ∧
        l*(p.2:ℝ) ≤ p.1 ∧ (p.1:ℝ) ≤ w*p.2 := by
  classical
  have hw' : 0 < -w := neg_pos.mpr hw
  have hl' : 0 ≤ -l := by linarith only [hw,hlw]
  constructor
  · intro hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨ht,htN,hcop,hlo,hhi⟩ :=
      (HuxleyLinearForm.mem_fareySector_iff hw' hl').mp hq
    refine ⟨ht,htN,hcop.neg_left,?_,?_⟩
    · simp only [Int.cast_neg]
      nlinarith only [hhi]
    · simp only [Int.cast_neg]
      nlinarith only [hlo]
  · rintro ⟨ht,htN,hcop,hlo,hhi⟩
    apply Finset.mem_image.mpr
    refine ⟨(-p.1,p.2),?_,by simp⟩
    apply (HuxleyLinearForm.mem_fareySector_iff hw' hl').mpr
    refine ⟨ht,htN,hcop.neg_left,?_,?_⟩
    · simp only [Int.cast_neg]
      nlinarith only [hhi]
    · simp only [Int.cast_neg]
      nlinarith only [hlo]

                                                                                 
                                                                       
theorem fareySector_card_le_rectangle_all_slopes {N : ℕ} {l w : ℝ}
    (hw : 0 ≤ w) :
    ((HuxleyLinearForm.fareySector N l w).card:ℝ) ≤ w*(N:ℝ)^2 := by
  classical
  have hc : (HuxleyLinearForm.fareySector N l w).card ≤ ⌊w*(N:ℝ)⌋₊*N := by
    calc
      _ ≤ (((Finset.Icc (1:ℤ) ⌊w*(N:ℝ)⌋) ×ˢ Finset.Icc 1 (N:ℤ))).card :=
        Finset.card_filter_le _ _
      _ = _ := by simp [Finset.card_product,Int.floor_toNat]
  have hc' : ((HuxleyLinearForm.fareySector N l w).card:ℝ) ≤
      (⌊w*(N:ℝ)⌋₊:ℝ)*(N:ℝ) := by exact_mod_cast hc
  have hf := Nat.floor_le (mul_nonneg hw (Nat.cast_nonneg N))
  exact hc'.trans (by nlinarith only [mul_le_mul_of_nonneg_right hf (Nat.cast_nonneg N)])

                                                                   
                                                                  
                                                                    
                                     
theorem fareySector_numerator_fiber_bounds
    {N : ℕ} {l w : ℝ} {m : ℤ}
    (hl : 0 < l) (hlw : l ≤ w) (hm : 0 ≤ m) :
    let T := (HuxleyLinearForm.fareySector N l w).filter (fun p => p.1=m)
    (T.card:ℝ) ≤ N ∧ (T.card:ℝ) ≤ (m:ℝ)/l-(m:ℝ)/w+1 := by
  classical
  intro T
  let A := T.image Prod.snd
  have hw : 0 < w := hl.trans_le hlw
  have hcard : A.card=T.card := Finset.card_image_of_injOn (by
    intro p hp q hq he
    exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) he)
  have hdata (n : ℤ) (hn : n∈A) :
      1 ≤ n ∧ n ≤ N ∧ (m:ℝ)/w ≤ n ∧ (n:ℝ) ≤ (m:ℝ)/l := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hpS,hpm⟩ := Finset.mem_filter.mp hp
    obtain ⟨ht,htN,_hc,hlo,hhi⟩ :=
      (HuxleyLinearForm.mem_fareySector_iff hl hw.le).mp hpS
    rw [hpm] at hlo hhi
    refine ⟨ht,htN,?_,?_⟩
    · apply (div_le_iff₀ hw).mpr
      nlinarith only [hhi]
    · apply (le_div_iff₀ hl).mpr
      nlinarith only [hlo]
  have hcN : A.card ≤ N := by
    calc
      _ ≤ (Finset.Icc (1:ℤ) (N:ℤ)).card := Finset.card_le_card (by
        intro n hn
        exact Finset.mem_Icc.mpr ⟨(hdata n hn).1,(hdata n hn).2.1⟩)
      _ = N := by simp
  have hmR : (0:ℝ) ≤ m := by exact_mod_cast hm
  have hwidth : 0 ≤ (m:ℝ)/l-(m:ℝ)/w :=
    sub_nonneg.mpr (div_le_div_of_nonneg_left hmR hl hlw)
  have hb := integer_card_le_of_abs_sub_le A
    (a := ((m:ℝ)/l+(m:ℝ)/w)/2)
    (show 0 ≤ ((m:ℝ)/l-(m:ℝ)/w)/2 by positivity) (by
      intro n hn
      have hh := hdata n hn
      exact abs_le.mpr ⟨by linarith only [hh.2.2.1],by linarith only [hh.2.2.2]⟩)
  rw [hcard] at hcN hb
  refine ⟨by exact_mod_cast hcN,?_⟩
  linarith only [hb]

                                                                
                                                                         
theorem fareySector_numerator_common_divisor {N q : ℕ} {l w : ℝ}
    (hl : 0 < l) (hw : 0 ≤ w) (hR : 2 ≤ (HuxleyLinearForm.fareySector N l w).card)
    (hdvd : ∀ p ∈ HuxleyLinearForm.fareySector N l w, q ∣ p.1.natAbs) : q=1 := by
  classical
  let S := HuxleyLinearForm.fareySector N l w
  change 2 ≤ S.card at hR
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p₀,hp₀,hmax⟩ := S.exists_max_image Prod.snd hne
  obtain ⟨p,hp,hneq⟩ := Finset.exists_mem_ne (by omega : 1 < S.card) p₀
  obtain ⟨r,hr,hunit⟩ := HuxleyLinearForm.fareySector_exists_unit_determinant
    hl hw hp₀ hp hneq (hmax p hp)
  have hd₀ : (q:ℤ) ∣ p₀.1 := Int.natCast_dvd.mpr (hdvd p₀ hp₀)
  have hdr : (q:ℤ) ∣ r.1 := Int.natCast_dvd.mpr (hdvd r hr)
  have hd : (q:ℤ) ∣ p₀.1*r.2-p₀.2*r.1 :=
    dvd_sub (dvd_mul_of_dvd_left hd₀ _) (dvd_mul_of_dvd_right hdr _)
  have hh : q ∣ (p₀.1*r.2-p₀.2*r.1).natAbs := Int.natCast_dvd.mp hd
  have hu : (p₀.1*r.2-p₀.2*r.1).natAbs=1 :=
    Int.ofNat_inj.mp ((Int.natCast_natAbs _).trans hunit)
  rw [hu] at hh
  exact Nat.dvd_one.mp hh

                                                                    
                                                                  
                                                    
theorem fareySector_numerator_card_lower {N : ℕ} {l w B : ℝ}
    (hl : 0 < l) (hlw : l ≤ w) (hN : 0 < N) (hB : 1 ≤ B)
    (hR : w*(N:ℝ) ≤ (HuxleyLinearForm.fareySector N l w).card)
    (hdensity : (w-l)*(N:ℝ)^2 ≤ B*(HuxleyLinearForm.fareySector N l w).card) :
    w*(N:ℝ) ≤ 3*B*((HuxleyLinearForm.fareySector N l w).image Prod.fst).card := by
  classical
  let S := HuxleyLinearForm.fareySector N l w
  let E := S.image Prod.fst
  let M := w*(N:ℝ)
  have hw : 0 < w := hl.trans_le hlw
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hM : 0 < M := mul_pos hw hNR
  have hSR : (0:ℝ) < S.card := hM.trans_le hR
  have hfiber : ∀ m∈E, M*((S.filter (fun p => p.1=m)).card:ℝ) ≤ 3*B*(S.card:ℝ) := by
    intro m hm
    obtain ⟨p,hp,hpm⟩ := Finset.mem_image.mp hm
    obtain ⟨ht,htN,_hc,hlo,hhi⟩ :=
      (HuxleyLinearForm.mem_fareySector_iff hl hw.le).mp hp
    have hpt : (0:ℝ) < p.2 := by exact_mod_cast (show 0 < p.2 by omega)
    have hmpos : (0:ℝ) < m := by
      rw [←hpm]
      exact (mul_pos hl hpt).trans_le hlo
    have hmZ : 0 ≤ m := by exact_mod_cast hmpos.le
    have hmM : (m:ℝ) ≤ w*(N:ℝ) := by
      rw [←hpm]
      exact hhi.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast htN) hw.le)
    have hb := fareySector_numerator_fiber_bounds (N:=N) hl hlw hmZ
    by_cases hwide : 2*l ≤ w
    · have hwidth : M*(N:ℝ) ≤ 2*B*(S.card:ℝ) := by
        have hh := mul_nonneg (show 0 ≤ w-2*l by linarith only [hwide])
          (sq_nonneg (N:ℝ))
        dsimp only [M]
        nlinarith only [hdensity,hh]
      calc
        _ ≤ M*(N:ℝ) := mul_le_mul_of_nonneg_left hb.1 hM.le
        _ ≤ 2*B*(S.card:ℝ) := hwidth
        _ ≤ _ := by nlinarith only [hB,hSR,mul_nonneg (show 0 ≤ B by linarith only [hB]) hSR.le]
    · have hz : M*((m:ℝ)/l-(m:ℝ)/w) ≤ 2*(w-l)*(N:ℝ)^2 := by
        have heq : l*(M*((m:ℝ)/l-(m:ℝ)/w))=(m:ℝ)*(N:ℝ)*(w-l) := by
          dsimp only [M]
          field_simp [hl.ne',hw.ne']
        have hh := mul_le_mul_of_nonneg_right hmM
          (mul_nonneg hNR.le (sub_nonneg.mpr hlw))
        have hh' := mul_nonneg (show 0 ≤ 2*l-w by linarith only [not_le.mp hwide])
          (mul_nonneg (sub_nonneg.mpr hlw) (sq_nonneg (N:ℝ)))
        have hscaled : l*(M*((m:ℝ)/l-(m:ℝ)/w)) ≤ l*(2*(w-l)*(N:ℝ)^2) := by
          rw [heq]
          nlinarith only [hh,hh']
        exact (mul_le_mul_iff_right₀ hl).mp hscaled
      have hh := mul_le_mul_of_nonneg_left hb.2 hM.le
      have hBR : (S.card:ℝ) ≤ B*(S.card:ℝ) := by
        nlinarith only [mul_le_mul_of_nonneg_right hB hSR.le]
      change M ≤ (S.card:ℝ) at hR
      nlinarith only [hh,hz,hdensity,hR,hBR]
  have heq : (S.card:ℝ) = ∑ m∈E, ((S.filter (fun p => p.1=m)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise (fun p hp => Finset.mem_image_of_mem Prod.fst hp)
  have hh := Finset.sum_le_sum hfiber
  rw [←Finset.mul_sum,←heq,Finset.sum_const,nsmul_eq_mul] at hh
  change M ≤ 3*B*(E.card:ℝ)
  have hs : M*(S.card:ℝ) ≤ (3*B*(E.card:ℝ))*(S.card:ℝ) := by
    nlinarith only [hh]
  exact (mul_le_mul_iff_left₀ hSR).mp hs

theorem fareySector_numerator_fiber_cutoff_bound
    {N : ℕ} {l w : ℝ} {m : ℤ}
    (hl : 0 < l) (hlw : l ≤ w) (hmM : (m:ℝ) ≤ w*(N:ℝ)) :
    (((HuxleyLinearForm.fareySector N l w).filter (fun p => p.1=m)).card:ℝ) ≤
      (N:ℝ)-(m:ℝ)/w+1 := by
  classical
  let T := (HuxleyLinearForm.fareySector N l w).filter (fun p => p.1=m)
  let A := T.image Prod.snd
  have hw : 0 < w := hl.trans_le hlw
  have hcard : A.card=T.card := Finset.card_image_of_injOn (by
    intro p hp q hq he
    exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) he)
  have hinterval : (m:ℝ)/w ≤ (N:ℝ) :=
    (div_le_iff₀ hw).mpr (by nlinarith only [hmM])
  have hb := integer_card_le_interval_length_add_one A hinterval (by
    intro n hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hpS,hpm⟩ := Finset.mem_filter.mp hp
    obtain ⟨_ht,htN,_hc,_hlo,hhi⟩ :=
      (HuxleyLinearForm.mem_fareySector_iff hl hw.le).mp hpS
    rw [hpm] at hhi
    refine ⟨(div_le_iff₀ hw).mpr (by nlinarith only [hhi]),?_⟩
    exact_mod_cast htN)
  rw [hcard] at hb
  exact hb

theorem fareySector_numerator_projection_card_le {N : ℕ} {l w : ℝ}
    (hw : 0 ≤ w) :
    (((HuxleyLinearForm.fareySector N l w).image Prod.fst).card:ℝ) ≤ w*(N:ℝ) := by
  classical
  have hc : ((HuxleyLinearForm.fareySector N l w).image Prod.fst).card ≤ ⌊w*(N:ℝ)⌋₊ := by
    calc
      _ ≤ (Finset.Icc (1:ℤ) ⌊w*(N:ℝ)⌋).card := Finset.card_le_card (by
        intro m hm
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hm
        exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1)
      _ = _ := by simp [Int.floor_toNat]
  have hc' : (((HuxleyLinearForm.fareySector N l w).image Prod.fst).card:ℝ) ≤
      (⌊w*(N:ℝ)⌋₊:ℝ) := by exact_mod_cast hc
  exact hc'.trans (Nat.floor_le (mul_nonneg hw (Nat.cast_nonneg N)))

                                                                   
                                                                   
                                                                       
theorem fareySector_large_numerator_width {N : ℕ} {l w : ℝ}
    (hl : 0 < l) (hlw : l ≤ w) (hN : 0 < N)
    (hR : 40*w*(N:ℝ) ≤ (HuxleyLinearForm.fareySector N l w).card) :
    39 ≤ (w*(N:ℝ))*(1/l-1/w) ∧ 39 ≤ (N:ℝ)-1/w := by
  classical
  let S := HuxleyLinearForm.fareySector N l w
  let E := S.image Prod.fst
  let M := w*(N:ℝ)
  let D := 1/l-1/w
  have hw : 0 < w := hl.trans_le hlw
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hM : 0 < M := mul_pos hw hNR
  have hSR : (0:ℝ) < S.card := by
    have hh : 40*M ≤ (S.card:ℝ) := by simpa only [M,mul_assoc] using hR
    exact (by positivity : 0 < 40*M).trans_le hh
  have hnum (m : ℤ) (hm : m∈E) : (1:ℝ) ≤ m ∧ (m:ℝ) ≤ M := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨ht,htN,_hc,hlo,hhi⟩ :=
      (HuxleyLinearForm.mem_fareySector_iff hl hw.le).mp hp
    have hpt : (0:ℝ) < p.2 := by exact_mod_cast (show 0 < p.2 by omega)
    have hpm : (0:ℝ) < p.1 := (mul_pos hl hpt).trans_le hlo
    have hpZ : 1 ≤ p.1 := by
      have hh : 0 < p.1 := by exact_mod_cast hpm
      omega
    exact ⟨by exact_mod_cast hpZ,
      hhi.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast htN) hw.le)⟩
  have hMone : 1 ≤ M := by
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (by exact_mod_cast hSR : 0 < S.card)
    have hh := hnum p.1 (Finset.mem_image_of_mem Prod.fst hp)
    exact hh.1.trans hh.2
  have hD : 0 ≤ D := sub_nonneg.mpr (one_div_le_one_div_of_le hl hlw)
  have hcut : 0 ≤ (N:ℝ)-1/w := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hw).mpr
    change 1 ≤ w*(N:ℝ) at hMone
    nlinarith only [hMone]
  have hE : (E.card:ℝ) ≤ M := fareySector_numerator_projection_card_le hw.le
  have hsum : (S.card:ℝ) = ∑ m∈E, ((S.filter (fun p => p.1=m)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise (fun p hp => Finset.mem_image_of_mem Prod.fst hp)
  have hfirst : (S.card:ℝ) ≤ M*(M*D+1) := by
    have hf : ∀ m∈E, ((S.filter (fun p => p.1=m)).card:ℝ) ≤ M*D+1 := by
      intro m hm
      have hmR := hnum m hm
      have hmZ : 0 ≤ m := by exact_mod_cast (zero_le_one.trans hmR.1)
      have hh := (fareySector_numerator_fiber_bounds (N:=N) hl hlw hmZ).2
      have he : (m:ℝ)/l-(m:ℝ)/w=(m:ℝ)*D := by dsimp only [D]; ring
      rw [he] at hh
      exact hh.trans (add_le_add (mul_le_mul_of_nonneg_right hmR.2 hD) le_rfl)
    have hh := Finset.sum_le_sum hf
    rw [←hsum,Finset.sum_const,nsmul_eq_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hE (by positivity))
  have hsecond : (S.card:ℝ) ≤ M*((N:ℝ)-1/w+1) := by
    have hf : ∀ m∈E, ((S.filter (fun p => p.1=m)).card:ℝ) ≤ (N:ℝ)-1/w+1 := by
      intro m hm
      have hmR := hnum m hm
      have hh := fareySector_numerator_fiber_cutoff_bound (N:=N) hl hlw hmR.2
      have hdiv := div_le_div_of_nonneg_right hmR.1 hw.le
      linarith only [hh,hdiv]
    have hh := Finset.sum_le_sum hf
    rw [←hsum,Finset.sum_const,nsmul_eq_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hE (by positivity))
  have hlarge : 40*M ≤ (S.card:ℝ) := by simpa only [M,mul_assoc] using hR
  have h₁ : M*39 ≤ M*(M*D) := by nlinarith only [hlarge,hfirst]
  have h₂ : M*39 ≤ M*((N:ℝ)-1/w) := by nlinarith only [hlarge,hsecond]
  exact ⟨(mul_le_mul_iff_right₀ hM).mp h₁,(mul_le_mul_iff_right₀ hM).mp h₂⟩

                                                                       
                                                                             
theorem fareySector_consecutive_denominators {N : ℕ} {l w : ℝ}
    (hl : 0 < l) (hlw : l ≤ w) (hN : 0 < N)
    (hR : 40*w*(N:ℝ) ≤ (HuxleyLinearForm.fareySector N l w).card) :
    ∃ m n : ℤ, (m,n) ∈ HuxleyLinearForm.fareySector N l w ∧
      (m,n+1) ∈ HuxleyLinearForm.fareySector N l w := by
  have hw : 0 < w := hl.trans_le hlw
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  let M := w*(N:ℝ)
  let D := 1/l-1/w
  have hM : 0 < M := mul_pos hw hNR
  have hD : 0 ≤ D := sub_nonneg.mpr (one_div_le_one_div_of_le hl hlw)
  obtain ⟨hwidth,hcut⟩ := fareySector_large_numerator_width hl hlw hN hR
  change 39 ≤ M*D at hwidth
  have hbuild (p : ℕ)
      (hwide : 4 ≤ (p:ℝ)/l-(p:ℝ)/w)
      (hbound : 4 ≤ (N:ℝ)-(p:ℝ)/w)
      (hcop : ∀ a : ℕ, ∃ n : ℕ, a ≤ n ∧ n ≤ a+2 ∧
        p.Coprime n ∧ p.Coprime (n+1)) :
      ∃ m n : ℤ, (m,n) ∈ HuxleyLinearForm.fareySector N l w ∧
        (m,n+1) ∈ HuxleyLinearForm.fareySector N l w := by
    let a := ⌊(p:ℝ)/w⌋₊+1
    obtain ⟨n,han,hna,hcn,hcn1⟩ := hcop a
    have hn : 1 ≤ n := by dsimp [a] at han; omega
    have hlow : (p:ℝ)/w ≤ n := by
      have hf := Nat.lt_floor_add_one ((p:ℝ)/w)
      have hh : (⌊(p:ℝ)/w⌋₊:ℝ)+1 ≤ n := by exact_mod_cast han
      linarith only [hf,hh]
    have hupp : (n:ℝ)+1 ≤ (p:ℝ)/w+4 := by
      have hf := Nat.floor_le (div_nonneg (Nat.cast_nonneg p) hw.le)
      have hh : (n:ℝ) ≤ (⌊(p:ℝ)/w⌋₊:ℝ)+3 := by exact_mod_cast hna
      linarith only [hf,hh]
    have hnN : (n:ℝ)+1 ≤ N := by linarith only [hupp,hbound]
    have hnl : (n:ℝ)+1 ≤ (p:ℝ)/l := by linarith only [hupp,hwide]
    have hln : l*(n:ℝ) ≤ p := by
      have hh := (le_div_iff₀ hl).mp (show (n:ℝ) ≤ (p:ℝ)/l by linarith only [hnl])
      nlinarith only [hh]
    have hln1 : l*((n:ℝ)+1) ≤ p := by
      have hh := (le_div_iff₀ hl).mp hnl
      nlinarith only [hh]
    have hpn : (p:ℝ) ≤ w*n := by
      have hh := (div_le_iff₀ hw).mp hlow
      nlinarith only [hh]
    have hpn1 : (p:ℝ) ≤ w*((n:ℝ)+1) := by nlinarith only [hpn,hw]
    have hnNZ : (n:ℤ)+1 ≤ N := by exact_mod_cast hnN
    refine ⟨p,n,?_,?_⟩
    · apply (HuxleyLinearForm.mem_fareySector_iff hl hw.le).mpr
      refine ⟨by dsimp; exact_mod_cast hn,by dsimp; omega,hcn.isCoprime,?_,?_⟩
      · simpa only [Int.cast_natCast] using hln
      · simpa only [Int.cast_natCast] using hpn
    · apply (HuxleyLinearForm.mem_fareySector_iff hl hw.le).mpr
      refine ⟨by dsimp; omega,hnNZ,?_,?_,?_⟩
      · simpa only [Nat.cast_add,Nat.cast_one] using hcn1.isCoprime
      · simpa only [Int.cast_natCast,Int.cast_add,Int.cast_one] using hln1
      · simpa only [Int.cast_natCast,Int.cast_add,Int.cast_one] using hpn1
  by_cases hsmall : M < 8
  · refine hbuild 1 ?_ ?_ ?_
    · norm_num only [Nat.cast_one]
      change 4 ≤ D
      nlinarith only [hwidth,hsmall,hD]
    · norm_num only [Nat.cast_one]
      linarith only [hcut]
    · intro a
      exact ⟨a,le_rfl,by omega,by simp,by simp⟩
  · have hM8 : 8 ≤ M := le_of_not_gt hsmall
    let k := ⌊M/4⌋₊
    have hk : 2 ≤ k := by
      apply (Nat.le_floor_iff (by positivity : 0 ≤ M/4)).mpr
      norm_num
      linarith only [hM8]
    obtain ⟨p,hp,hkp,hpk⟩ := Nat.exists_prime_lt_and_le_two_mul k (by omega)
    have hp3 : 3 ≤ p := by omega
    have hpl : M/4 < (p:ℝ) := by
      have hf := Nat.lt_floor_add_one (M/4)
      have hh : (k:ℝ)+1 ≤ p := by exact_mod_cast hkp
      exact hf.trans_le hh
    have hpu : (p:ℝ) ≤ M/2 := by
      have hf := Nat.floor_le (by positivity : 0 ≤ M/4)
      have hh : (p:ℝ) ≤ 2*(k:ℝ) := by exact_mod_cast hpk
      dsimp only [k] at hh
      linarith only [hf,hh]
    refine hbuild p ?_ ?_ ?_
    · have hh := mul_le_mul_of_nonneg_right hpl.le hD
      have he : (p:ℝ)/l-(p:ℝ)/w=(p:ℝ)*D := by dsimp only [D]; ring
      rw [he]
      nlinarith only [hh,hwidth]
    · have hpw : (p:ℝ)/w ≤ (N:ℝ)/2 := by
        apply (div_le_iff₀ hw).mpr
        dsimp only [M] at hpu
        nlinarith only [hpu]
      have hi : 0 ≤ 1/w := by positivity
      linarith only [hpw,hi,hcut]
    · exact HuxleyLinearForm.prime_coprime_consecutive hp hp3

-- Generated closures: source context is replayed in the next part.
end TaoTrudgianYang2025.HuxleyRationalPhase
end
end
