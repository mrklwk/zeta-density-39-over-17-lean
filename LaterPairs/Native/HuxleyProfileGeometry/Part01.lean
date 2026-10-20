module
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

 
                                                                    

                                                                   
                                                                        
                                                                         
                                                                     

                                                                          
                                                                         
                                                                         
                                                                            
                                                 

                                                                     
                                                                        
                                                                       
                                                                           
                                                                   
                                                                       
                                                                      
                                                                       
                                                                 
                                                                  
                                                                       
                                                                         
                                                                         
                                                                   
                                                                          
                                                                          
                                                                         
                                                                           
                                                                      
                                                                       
                                                                    
                                                                    
                                                                      
                                                                        
                                                           
                                                                       
                                                                           
                                                                      
                                                                          
                                                                           
                                                                    
                                                                          
                                                                        
                                                                          
                                                                  
                                                                         
                                                                          
                                                                        
                                                              
                                                                         
                                                                       
                                                                       
                                                                       
                                                                            
                                                                     
                                                                           
                                                                        
                                                                        
                                                                      
                                                                   
                                                                         
                                                                            
                                                                         
                                                                       
                                                                          
                                                                       
                                                                         
                                                                         
                                                                        
                                                                          
                                                                         
                                                                      
                                                                    
                                                                      
                                                                        
                                                                       
                                                                      
                                                                        
                                                                        
                                                                    
                                                                       
                                                                        
                                                                          
                                                                     
                                                                      
                                                                         
                                                                            
                                                                       
                                                                          
                                                                     
                                                                          
                                                                       
                                                                  
                                                                  
                                                                
                                                                       
                                                                      
                                                                    
                                                                      
                                                                
                                                             
                                                                      
                                                                        
                                                                       
                                                                   
                                                                       
                                                                           
                                                                         
                                                                       
                                                                       
                                                                        
                                                                     
                                                                     
                                                                       
                                                                          
                                                                     
                                                                        
                                                                           
                                                                     
                                                                          
                                                                       
                                                                       
                                                                     
                                                                     
                                                                           
                                                                         
                                                                       
                                                                           
                                                                    

                                                                     
                                         
                                                                   
                                                                 
                                                                          
                                                                            
                                                                       


noncomputable section
open Set

namespace TaoTrudgianYang2025.HuxleyLinearForm

                                                                 
                                                                   
                                                                         
theorem small_denominator_integer_identity
    {N q n : ℕ} {a b : ℤ} {α δ : ℝ}
    (hN : 0 < N) (hq : 0 < q) (hn : n ≤ N)
    (happrox : |(q:ℝ)*α-a| ≤ 1/(2*(N:ℝ)))
    (hsmall : (q:ℝ)*δ < 1/2)
    (hnear : |(n:ℝ)*α-b| ≤ δ) :
    (n:ℤ)*a = (q:ℤ)*b := by
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hnR : (n:ℝ) ≤ N := Nat.cast_le.mpr hn
  have hqR : (0:ℝ) < q := Nat.cast_pos.mpr hq
  have hterm : (n:ℝ)*|(q:ℝ)*α-a| ≤ 1/2 := by
    calc
      _ ≤ (N:ℝ)*(1/(2*(N:ℝ))) :=
        mul_le_mul hnR happrox (abs_nonneg _) hNR.le
      _ = _ := by field_simp
  have he : |(((n:ℤ)*a-(q:ℤ)*b:ℤ):ℝ)| < 1 := by
    have hident : (((n:ℤ)*a-(q:ℤ)*b:ℤ):ℝ) =
        (q:ℝ)*((n:ℝ)*α-b)-(n:ℝ)*((q:ℝ)*α-a) := by
      push_cast
      ring
    rw [hident]
    calc
      _ ≤ |(q:ℝ)*((n:ℝ)*α-b)|+|(n:ℝ)*((q:ℝ)*α-a)| := abs_sub _ _
      _ = (q:ℝ)*|(n:ℝ)*α-b|+(n:ℝ)*|(q:ℝ)*α-a| := by
        simp only [abs_mul,abs_of_pos hqR,
          abs_of_nonneg (show (0:ℝ) ≤ n from Nat.cast_nonneg n)]
      _ ≤ (q:ℝ)*δ+1/2 := add_le_add (mul_le_mul_of_nonneg_left hnear hqR.le) hterm
      _ < 1 := by linarith
  have he' : |(n:ℤ)*a-(q:ℤ)*b| < 1 := by exact_mod_cast he
  have hab := abs_lt.mp he'
  omega

theorem card_mul_le_of_dvd
    (S : Finset ℕ) {q N : ℕ} (hq : 0 < q)
    (hS : ∀ n ∈ S, 1 ≤ n ∧ n ≤ N)
    (hdvd : ∀ n ∈ S, q ∣ n) : q*S.card ≤ N := by
  have hmap : Set.MapsTo (fun n : ℕ => n/q) S (Finset.Icc 1 (N/q)) := by
    intro n hn
    apply Finset.mem_Icc.mpr
    constructor
    · exact (Nat.le_div_iff_mul_le hq).mpr
        (by simpa using Nat.le_of_dvd (hS n hn).1 (hdvd n hn))
    · exact Nat.div_le_div_right (hS n hn).2
  have hinj : Set.InjOn (fun n : ℕ => n/q) S := by
    intro n hn m hm he
    change n/q=m/q at he
    calc
      n = (n/q)*q := (Nat.div_mul_cancel (hdvd n hn)).symm
      _ = (m/q)*q := by rw [he]
      _ = m := Nat.div_mul_cancel (hdvd m hm)
  have hc : S.card ≤ N/q := by
    have h := Finset.card_le_card_of_injOn (fun n : ℕ => n/q) hmap hinj
    simpa using h
  exact (Nat.mul_le_mul_left q hc).trans (by simpa [Nat.mul_comm] using Nat.div_mul_le_self N q)

theorem small_denominator_branch
    (S : Finset ℕ) {N q : ℕ} {a : ℤ} {α δ : ℝ}
    (hN : 0 < N) (hq : 0 < q) (hδ : 0 ≤ δ)
    (hcop : IsCoprime a (q:ℤ))
    (hS : ∀ n ∈ S, 1 ≤ n ∧ n ≤ N)
    (happrox : |(q:ℝ)*α-a| ≤ 1/(2*(N:ℝ)))
    (hsmall : (q:ℝ)*δ < 1/2)
    (hnear : ∀ n ∈ S, ∃ b : ℤ, |(n:ℝ)*α-b| ≤ δ) :
    (∀ n ∈ S, q ∣ n) ∧ q*S.card ≤ N ∧
      |(q:ℝ)*α-a| * (S.card:ℝ) ≤ δ := by
  have hdvd : ∀ n ∈ S, q ∣ n := by
    intro n hn
    obtain ⟨b,hb⟩ := hnear n hn
    have he := small_denominator_integer_identity hN hq (hS n hn).2 happrox hsmall hb
    have hdiv : (q:ℤ) ∣ (n:ℤ)*a := ⟨b,he⟩
    exact_mod_cast hcop.symm.dvd_of_dvd_mul_right hdiv
  refine ⟨hdvd,card_mul_le_of_dvd S hq hS hdvd,?_⟩
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simpa using hδ
  let n := S.max' hne
  have hn : n ∈ S := Finset.max'_mem S hne
  have hcard : q*S.card ≤ n := card_mul_le_of_dvd S hq
    (fun m hm => ⟨(hS m hm).1,Finset.le_max' S m hm⟩) hdvd
  obtain ⟨b,hb⟩ := hnear n hn
  have he := small_denominator_integer_identity hN hq (hS n hn).2 happrox hsmall hb
  have heR : (n:ℝ)*((q:ℝ)*α-a) = (q:ℝ)*((n:ℝ)*α-b) := by
    have h : (n:ℝ)*(a:ℝ) = (q:ℝ)*(b:ℝ) := by exact_mod_cast he
    nlinarith only [h]
  have hbound : (n:ℝ)*|(q:ℝ)*α-a| ≤ (q:ℝ)*δ := by
    calc
      _ = |(n:ℝ)*((q:ℝ)*α-a)| := by
        rw [abs_mul,abs_of_nonneg (show (0:ℝ) ≤ n from Nat.cast_nonneg n)]
      _ = (q:ℝ)*|(n:ℝ)*α-b| := by
        rw [heR,abs_mul,abs_of_nonneg (show (0:ℝ) ≤ q from Nat.cast_nonneg q)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg q)
  have hcardR : (q:ℝ)*(S.card:ℝ) ≤ n := by exact_mod_cast hcard
  have hm := mul_le_mul_of_nonneg_right hcardR (abs_nonneg ((q:ℝ)*α-a))
  have hqR : (0:ℝ) < q := Nat.cast_pos.mpr hq
  nlinarith only [hbound,hm,hqR]

                                                                             
theorem exists_reduced_approximation (α : ℝ) {N : ℕ} (hN : 0 < N) :
    ∃ a : ℤ, ∃ q : ℕ, 0 < q ∧ q ≤ 2*N-1 ∧ IsCoprime a (q:ℤ) ∧
      |(q:ℝ)*α-a| ≤ 1/(2*(N:ℝ)) := by
  obtain ⟨r,hr,hden⟩ := Real.exists_rat_abs_sub_le_and_den_le α
    (show 0 < 2*N-1 by omega)
  have hd : (0:ℝ) < r.den := Nat.cast_pos.mpr r.pos
  have hscale : ((2*N-1:ℕ):ℝ)+1 = 2*(N:ℝ) := by
    have he : (2*N-1)+1=2*N := by omega
    exact_mod_cast he
  refine ⟨r.num,r.den,r.pos,hden,r.isCoprime_num_den,?_⟩
  rw [hscale] at hr
  have h := mul_le_mul_of_nonneg_right hr hd.le
  have he : |α-(r:ℝ)| * (r.den:ℝ) = |(r.den:ℝ)*α-r.num| := by
    calc
      _ = |(α-(r:ℝ))*(r.den:ℝ)| := by rw [abs_mul,abs_of_pos hd]
      _ = _ := by
        congr 1
        rw [Rat.cast_def]
        field_simp
  rw [he] at h
  convert h using 1
  field_simp

theorem fixed_residual_separated {q n m : ℕ} {a e : ℤ}
    (b : ℕ → ℤ) (hq : 0 < q) (hcop : IsCoprime a (q:ℤ))
    (hn : a*(n:ℤ)-(q:ℤ)*b n=e) (hm : a*(m:ℤ)-(q:ℤ)*b m=e)
    (hne : n ≠ m) : (q:ℝ) ≤ |(n:ℝ)-(m:ℝ)| := by
  have hdiv : (q:ℤ) ∣ a*((n:ℤ)-(m:ℤ)) :=
    ⟨b n-b m,by nlinarith only [hn,hm]⟩
  obtain ⟨k,hk⟩ := hcop.symm.dvd_of_dvd_mul_left hdiv
  have hk0 : k ≠ 0 := by
    intro he
    rw [he,mul_zero] at hk
    exact hne (by exact_mod_cast sub_eq_zero.mp hk)
  have hk1 : (1:ℤ) ≤ |k| := by have h := abs_pos.mpr hk0; omega
  have hkr : (1:ℝ) ≤ |(k:ℝ)| := by exact_mod_cast hk1
  have he : (n:ℝ)-(m:ℝ) = (q:ℝ)*(k:ℝ) := by exact_mod_cast hk
  rw [he,abs_mul,abs_of_pos (show (0:ℝ) < q from Nat.cast_pos.mpr hq)]
  exact le_mul_of_one_le_right (Nat.cast_nonneg q) hkr

theorem fixed_residual_card_bound (S : Finset ℕ) (b : ℕ → ℤ)
    {N q : ℕ} {a e : ℤ} (hN : 0 < N) (hq : 0 < q)
    (hcop : IsCoprime a (q:ℤ)) (hS : ∀ n ∈ S, 1 ≤ n ∧ n ≤ N)
    (he : ∀ n ∈ S, a*(n:ℤ)-(q:ℤ)*b n=e) :
    (S.card:ℝ) ≤ ((N:ℝ)-1)/q+1 := by
  classical
  let W := S.image (fun n : ℕ => (n:ℝ)/q)
  have hqR : (0:ℝ) < q := Nat.cast_pos.mpr hq
  have hsep : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → 1 ≤ |x-y| := by
    intro x hx y hy hxy
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hy
    have hnm : n ≠ m := by intro h; exact hxy (by rw [h])
    have hd := fixed_residual_separated b hq hcop (he n hn) (he m hm) hnm
    rw [← sub_div,abs_div,abs_of_pos hqR]
    exact (le_div_iff₀ hqR).mpr (by simpa using hd)
  have hmem : ∀ x ∈ W, 1/(q:ℝ) ≤ x ∧ x ≤ (N:ℝ)/q := by
    intro x hx
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hx
    exact ⟨div_le_div_of_nonneg_right (by exact_mod_cast (hS n hn).1) hqR.le,
      div_le_div_of_nonneg_right (by exact_mod_cast (hS n hn).2) hqR.le⟩
  have hlen : 0 ≤ (N:ℝ)/q-1/q := sub_nonneg.mpr
    (div_le_div_of_nonneg_right (by exact_mod_cast hN) hqR.le)
  have hc := oneSeparated_card_cast_le_interval_length_add_one W hsep hlen hmem
  have hcard : W.card=S.card := Finset.card_image_of_injective S
    (fun _ _ h => Nat.cast_injective ((div_left_inj' hqR.ne').mp h))
  rw [hcard,← sub_div] at hc
  exact hc

theorem large_denominator_branch
    (S : Finset ℕ) {N q : ℕ} {a : ℤ} {α δ : ℝ}
    (hN : 0 < N) (hq : 0 < q) (hqN : q ≤ 2*N) (hδ : 0 ≤ δ)
    (hcop : IsCoprime a (q:ℤ))
    (hS : ∀ n ∈ S, 1 ≤ n ∧ n ≤ N)
    (happrox : |(q:ℝ)*α-a| ≤ 1/(2*(N:ℝ)))
    (hlarge : 1/2 ≤ (q:ℝ)*δ)
    (hnear : ∀ n ∈ S, ∃ b : ℤ, |(n:ℝ)*α-b| ≤ δ) :
    (S.card:ℝ) ≤ 12*δ*N := by
  classical
  let b : ℕ → ℤ := fun n => if hn : n ∈ S then Classical.choose (hnear n hn) else 0
  have hb (n : ℕ) (hn : n ∈ S) : |(n:ℝ)*α-b n| ≤ δ := by
    simpa only [b,dite_eq_left hn] using Classical.choose_spec (hnear n hn)
  let e : ℕ → ℤ := fun n => a*(n:ℤ)-(q:ℤ)*b n
  let E := S.image e
  have hqR : (0:ℝ) < q := Nat.cast_pos.mpr hq
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have he (n : ℕ) (hn : n ∈ S) : |(e n:ℝ)| ≤ 2*(q:ℝ)*δ := by
    have hterm : (n:ℝ)*|(q:ℝ)*α-a| ≤ 1/2 := by
      calc
        _ ≤ (N:ℝ)*(1/(2*(N:ℝ))) :=
          mul_le_mul (by exact_mod_cast (hS n hn).2) happrox (abs_nonneg _) hNR.le
        _ = _ := by field_simp
    have hid : (e n:ℝ) =
        (q:ℝ)*((n:ℝ)*α-b n)-(n:ℝ)*((q:ℝ)*α-a) := by
      dsimp [e]
      push_cast
      ring
    rw [hid]
    calc
      _ ≤ |(q:ℝ)*((n:ℝ)*α-b n)|+|(n:ℝ)*((q:ℝ)*α-a)| := abs_sub _ _
      _ = (q:ℝ)*|(n:ℝ)*α-b n|+(n:ℝ)*|(q:ℝ)*α-a| := by
        simp only [abs_mul,abs_of_pos hqR,
          abs_of_nonneg (show (0:ℝ) ≤ n from Nat.cast_nonneg n)]
      _ ≤ (q:ℝ)*δ+1/2 := add_le_add (mul_le_mul_of_nonneg_left (hb n hn) hqR.le) hterm
      _ ≤ _ := by linarith
  have hE : (E.card:ℝ) ≤ 6*(q:ℝ)*δ := by
    have hcount := integer_card_le_of_abs_sub_le E (a := 0)
      (by positivity : 0 ≤ 2*(q:ℝ)*δ) (fun z hz => by
        obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hz
        simpa only [sub_zero] using he n hn)
    linarith
  let B : ℝ := if q ≤ N then 2*(N:ℝ)/q else 1
  have hB : 0 ≤ B := by dsimp only [B]; split <;> positivity
  have hfiber (z : ℤ) : ((S.filter (fun n => e n=z)).card:ℝ) ≤ B := by
    let T := S.filter (fun n => e n=z)
    have hc := fixed_residual_card_bound T b hN hq hcop
      (fun n hn => hS n (Finset.mem_filter.mp hn).1)
      (fun n hn => (Finset.mem_filter.mp hn).2)
    by_cases hqN' : q ≤ N
    · dsimp only [B]
      rw [ite_eq_left hqN']
      have hqr : (q:ℝ) ≤ N := by exact_mod_cast hqN'
      have hcomp : ((N:ℝ)-1)/q+1 ≤ 2*(N:ℝ)/q := by
        apply (le_div_iff₀ hqR).mpr
        rw [add_mul,div_mul_cancel₀ _ hqR.ne']
        linarith
      exact hc.trans hcomp
    · dsimp only [B]
      rw [ite_eq_right hqN']
      have hqr : (N:ℝ) < q := by exact_mod_cast Nat.lt_of_not_ge hqN'
      have hlt : ((N:ℝ)-1)/q < 1 := (div_lt_one hqR).mpr (by linarith)
      have hn : T.card < 2 := by exact_mod_cast (show (T.card:ℝ) < 2 by linarith)
      exact_mod_cast (show T.card ≤ 1 by omega)
  have hmaps : Set.MapsTo e S E := fun n hn => Finset.mem_image.mpr ⟨n,hn,rfl⟩
  have hcard : (S.card:ℝ) = ∑ z ∈ E, ((S.filter (fun n => e n=z)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  have hbound : (S.card:ℝ) ≤ (6*(q:ℝ)*δ)*B := by
    calc
      _ = _ := hcard
      _ ≤ ∑ _z ∈ E, B := Finset.sum_le_sum (fun z _ => hfiber z)
      _ = (E.card:ℝ)*B := by simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hE hB
  apply hbound.trans
  dsimp only [B]
  split
  · have heq : 6*(q:ℝ)*δ*(2*(N:ℝ)/q)=12*δ*N := by field_simp; ring
    exact heq.le
  · have hqr : (q:ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast hqN
    have hmul := mul_le_mul_of_nonneg_right hqr hδ
    nlinarith only [hmul]

                                                                     
                                                        
theorem linear_form_dichotomy
    (S : Finset ℕ) {N : ℕ} {α δ : ℝ}
    (hN : 0 < N) (hδ : 0 ≤ δ)
    (hS : ∀ n ∈ S, 1 ≤ n ∧ n ≤ N)
    (hnear : ∀ n ∈ S, ∃ b : ℤ, |(n:ℝ)*α-b| ≤ δ) :
    (S.card:ℝ) ≤ 12*δ*N ∨
      ∃ q : ℕ, 0 < q ∧ q*S.card ≤ N ∧ (∀ n ∈ S, q ∣ n) ∧
        ∃ a : ℤ, |(q:ℝ)*α-a| * (S.card:ℝ) ≤ δ := by
  obtain ⟨a,q,hq,hqN,hcop,happrox⟩ := exists_reduced_approximation α hN
  by_cases hsmall : (q:ℝ)*δ < 1/2
  · obtain ⟨hdvd,hcard,hclose⟩ := small_denominator_branch S hN hq hδ hcop
      hS happrox hsmall hnear
    exact Or.inr ⟨q,hq,hcard,hdvd,a,hclose⟩
  · exact Or.inl (large_denominator_branch S hN hq (by omega) hδ hcop
      hS happrox (le_of_not_gt hsmall) hnear)

                                                                        
theorem maximal_denominator_determinant_injective
    {m₀ n₀ : ℤ} (hn₀ : 0 < n₀) (hcop : IsCoprime m₀ n₀) :
    Set.InjOn (fun p : ℤ × ℤ => m₀*p.2-n₀*p.1)
      {p | 1 ≤ p.2 ∧ p.2 ≤ n₀} := by
  intro p hp q hq he
  have hdiv : n₀ ∣ m₀*(p.2-q.2) := ⟨p.1-q.1,by dsimp at he; nlinarith only [he]⟩
  obtain ⟨k,hk⟩ := hcop.symm.dvd_of_dvd_mul_left hdiv
  have hk0 : k=0 := by
    by_contra hne
    have hd : k ≤ -1 ∨ 1 ≤ k := by omega
    rcases hd with hd | hd <;> nlinarith [hp.1,hp.2,hq.1,hq.2]
  have hden : p.2=q.2 := by rw [hk0,mul_zero] at hk; exact sub_eq_zero.mp hk
  have hnum : p.1=q.1 := by
    have he' : n₀*(p.1-q.1)=0 := by dsimp at he; rw [hden] at he; nlinarith only [he]
    exact sub_eq_zero.mp ((mul_eq_zero.mp he').resolve_left hn₀.ne')
  exact Prod.ext hnum hden

                                                                    
                                                    
theorem determinant_alpha_near
    (m₀ n₀ m n b₀ b : ℤ) {α β δ N : ℝ}
    (hn : |(n:ℝ)| ≤ N) (hn₀ : |(n₀:ℝ)| ≤ N)
    (hzero : |(m₀:ℝ)*α+(n₀:ℝ)*β-b₀| ≤ δ)
    (hpoint : |(m:ℝ)*α+(n:ℝ)*β-b| ≤ δ) :
    |((m₀*n-n₀*m:ℤ):ℝ)*α-((n*b₀-n₀*b:ℤ):ℝ)| ≤ 2*N*δ := by
  have he : ((m₀*n-n₀*m:ℤ):ℝ)*α-((n*b₀-n₀*b:ℤ):ℝ) =
      (n:ℝ)*((m₀:ℝ)*α+(n₀:ℝ)*β-b₀)-(n₀:ℝ)*((m:ℝ)*α+(n:ℝ)*β-b) := by
    push_cast
    ring
  rw [he]
  have hN : 0 ≤ N := (abs_nonneg _).trans hn
  calc
    _ ≤ |(n:ℝ)*((m₀:ℝ)*α+(n₀:ℝ)*β-b₀)|+
        |(n₀:ℝ)*((m:ℝ)*α+(n:ℝ)*β-b)| := abs_sub _ _
    _ ≤ N*δ+N*δ := by
      rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul hn hzero (abs_nonneg _) hN)
        (mul_le_mul hn₀ hpoint (abs_nonneg _) hN)
    _ = _ := by ring

theorem determinant_beta_near
    (m₀ n₀ m n b₀ b : ℤ) {α β δ M : ℝ}
    (hm : |(m:ℝ)| ≤ M) (hm₀ : |(m₀:ℝ)| ≤ M)
    (hzero : |(m₀:ℝ)*α+(n₀:ℝ)*β-b₀| ≤ δ)
    (hpoint : |(m:ℝ)*α+(n:ℝ)*β-b| ≤ δ) :
    |((m₀*n-n₀*m:ℤ):ℝ)*β-((m₀*b-m*b₀:ℤ):ℝ)| ≤ 2*M*δ := by
  have h := determinant_alpha_near n₀ m₀ n m b₀ b hm hm₀
    (α := β) (β := α) (by simpa only [add_comm] using hzero)
    (by simpa only [add_comm] using hpoint)
  have he : ((m₀*n-n₀*m:ℤ):ℝ)*β-((m₀*b-m*b₀:ℤ):ℝ) =
      -(((n₀*m-m₀*n:ℤ):ℝ)*β-((m*b₀-m₀*b:ℤ):ℝ)) := by
    push_cast
    ring
  rw [he,abs_neg]
  exact h

                                                                       
                                                                       
                                                                   
theorem exists_right_neighbor {m₀ n₀ : ℤ}
    (hn₀ : 0 < n₀) (hcop : IsCoprime m₀ n₀) :
    ∃ a b : ℤ, 1 ≤ b ∧ b ≤ n₀ ∧ IsCoprime a b ∧
      m₀*b-n₀*a = -1 ∧
      ∀ m n : ℤ, 1 ≤ n → n ≤ n₀ → m₀*n < n₀*m → a*n ≤ m*b := by
  obtain ⟨u,v,huv⟩ := hcop
  let k : ℤ := (-u-1)/n₀
  let b : ℤ := (-u-1)%n₀+1
  let a : ℤ := v-k*m₀
  have hb : 1 ≤ b ∧ b ≤ n₀ := by
    have hlow := Int.emod_nonneg (-u-1) hn₀.ne'
    have hhigh := Int.emod_lt_of_pos (-u-1) hn₀
    dsimp [b]
    omega
  have hbform : b = -u-k*n₀ := by
    have he := Int.emod_add_mul_ediv (-u-1) n₀
    dsimp [b,k]
    nlinarith only [he]
  have hdet : m₀*b-n₀*a = -1 := by
    dsimp [a]
    rw [hbform]
    nlinarith only [huv]
  refine ⟨a,b,hb.1,hb.2,⟨n₀,-m₀,by nlinarith only [hdet]⟩,hdet,?_⟩
  intro m n _hn hnmax hright
  have hd : 1 ≤ n₀*m-m₀*n := by omega
  have hprod : 1 ≤ (n₀*m-m₀*n)*b := one_le_mul_of_one_le_of_one_le hd hb.1
  have he : n-(n₀*m-m₀*n)*b = n₀*(a*n-m*b) := by
    have h := congrArg (fun z : ℤ => z*n) hdet
    nlinarith only [h]
  by_contra hbad
  have hc : 1 ≤ a*n-m*b := by omega
  have hlarge := mul_le_mul_of_nonneg_left hc hn₀.le
  nlinarith only [he,hprod,hnmax,hlarge]

theorem exists_left_neighbor {m₀ n₀ : ℤ}
    (hn₀ : 0 < n₀) (hcop : IsCoprime m₀ n₀) :
    ∃ a b : ℤ, 1 ≤ b ∧ b ≤ n₀ ∧ IsCoprime a b ∧
      m₀*b-n₀*a = 1 ∧
      ∀ m n : ℤ, 1 ≤ n → n ≤ n₀ → n₀*m < m₀*n → m*b ≤ a*n := by
  obtain ⟨a,b,hb,hbmax,hcop',hdet,hclose⟩ := exists_right_neighbor hn₀ hcop.neg_left
  refine ⟨-a,b,hb,hbmax,hcop'.neg_left,by nlinarith only [hdet],?_⟩
  intro m n hn hnmax hleft
  have h := hclose (-m) n hn hnmax (by nlinarith only [hleft])
  nlinarith only [h]

                                                                   
                                                                       
def fareySector (N : ℕ) (l μ : ℝ) : Finset (ℤ × ℤ) := by
  classical
  exact ((Finset.Icc 1 ⌊μ*(N:ℝ)⌋) ×ˢ (Finset.Icc 1 (N:ℤ))).filter
    (fun p => IsCoprime p.1 p.2 ∧ l*(p.2:ℝ) ≤ p.1 ∧ (p.1:ℝ) ≤ μ*p.2)

theorem mem_fareySector_iff {N : ℕ} {l μ : ℝ} {p : ℤ × ℤ}
    (hl : 0 < l) (hμ : 0 ≤ μ) :
    p ∈ fareySector N l μ ↔ 1 ≤ p.2 ∧ p.2 ≤ N ∧
      IsCoprime p.1 p.2 ∧ l*(p.2:ℝ) ≤ p.1 ∧ (p.1:ℝ) ≤ μ*p.2 := by
  classical
  simp only [fareySector,Finset.mem_filter,Finset.mem_product,Finset.mem_Icc]
  constructor
  · rintro ⟨⟨_hm,hn⟩,hc,hlower,hu⟩
    exact ⟨hn.1,hn.2,hc,hlower,hu⟩
  · rintro ⟨hn,hnmax,hc,hlower,hu⟩
    have hnR : (0:ℝ) < p.2 := by exact_mod_cast (show 0 < p.2 by omega)
    have hmR : (0:ℝ) < p.1 := (mul_pos hl hnR).trans_le hlower
    have hm : 1 ≤ p.1 := by
      have h : 0 < p.1 := by exact_mod_cast hmR
      omega
    have hmmax : p.1 ≤ ⌊μ*(N:ℝ)⌋ := Int.le_floor.mpr
      (hu.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hnmax) hμ))
    exact ⟨⟨⟨hm,hmmax⟩,hn,hnmax⟩,hc,hlower,hu⟩

                                                                     
                                                                         
                                                        
theorem fareySector_exists_unit_determinant
    {N : ℕ} {l μ : ℝ} {p₀ p : ℤ × ℤ}
    (hl : 0 < l) (hμ : 0 ≤ μ)
    (hp₀ : p₀ ∈ fareySector N l μ) (hp : p ∈ fareySector N l μ)
    (hne : p ≠ p₀) (hmax : p.2 ≤ p₀.2) :
    ∃ r ∈ fareySector N l μ, |p₀.1*r.2-p₀.2*r.1|=1 := by
  obtain ⟨hn₀,hn₀N,hcop₀,hl₀,hu₀⟩ := (mem_fareySector_iff hl hμ).mp hp₀
  obtain ⟨hn,_hnN,_hcop,hlp,hup⟩ := (mem_fareySector_iff hl hμ).mp hp
  have hn₀pos : 0 < p₀.2 := by omega
  have hn₀R : (0:ℝ) < p₀.2 := by exact_mod_cast hn₀pos
  have hnR : (0:ℝ) < p.2 := by exact_mod_cast (show 0 < p.2 by omega)
  have hdetne : p₀.1*p.2 ≠ p₀.2*p.1 := by
    intro he
    apply hne
    apply maximal_denominator_determinant_injective hn₀pos hcop₀
      (show 1 ≤ p.2 ∧ p.2 ≤ p₀.2 from ⟨hn,hmax⟩)
      (show 1 ≤ p₀.2 ∧ p₀.2 ≤ p₀.2 from ⟨hn₀,le_rfl⟩)
    nlinarith only [he]
  rcases lt_or_gt_of_ne hdetne with hright | hleft
  · obtain ⟨a,b,hb,hbmax,hcop',hdet,hclose⟩ := exists_right_neighbor hn₀pos hcop₀
    have hbR : (0:ℝ) ≤ b := by exact_mod_cast (show 0 ≤ b by omega)
    have hdetR : (p₀.1:ℝ)*b-(p₀.2:ℝ)*a = -1 := by exact_mod_cast hdet
    have hcloseR : (a:ℝ)*p.2 ≤ (p.1:ℝ)*b := by
      exact_mod_cast hclose p.1 p.2 hn hmax hright
    refine ⟨(a,b),(mem_fareySector_iff hl hμ).mpr ⟨hb,hbmax.trans hn₀N,hcop',?_,?_⟩,?_⟩
    · apply (mul_le_mul_iff_right₀ hn₀R).mp
      nlinarith only [mul_le_mul_of_nonneg_right hl₀ hbR,hdetR]
    · apply (mul_le_mul_iff_right₀ hnR).mp
      nlinarith only [mul_le_mul_of_nonneg_right hup hbR,hcloseR]
    · simp only [hdet,abs_neg,abs_one]
  · obtain ⟨a,b,hb,hbmax,hcop',hdet,hclose⟩ := exists_left_neighbor hn₀pos hcop₀
    have hbR : (0:ℝ) ≤ b := by exact_mod_cast (show 0 ≤ b by omega)
    have hdetR : (p₀.1:ℝ)*b-(p₀.2:ℝ)*a = 1 := by exact_mod_cast hdet
    have hcloseR : (p.1:ℝ)*b ≤ (a:ℝ)*p.2 := by
      exact_mod_cast hclose p.1 p.2 hn hmax hleft
    refine ⟨(a,b),(mem_fareySector_iff hl hμ).mpr ⟨hb,hbmax.trans hn₀N,hcop',?_,?_⟩,?_⟩
    · apply (mul_le_mul_iff_right₀ hnR).mp
      nlinarith only [mul_le_mul_of_nonneg_right hlp hbR,hcloseR]
    · apply (mul_le_mul_iff_right₀ hn₀R).mp
      nlinarith only [mul_le_mul_of_nonneg_right hu₀ hbR,hdetR]
    · simp only [hdet,abs_one]

                                                                      
theorem card_le_two_mul_nonzero_abs_card_add_one (D : Finset ℤ) :
    D.card ≤ 2*((D.erase 0).image Int.natAbs).card+1 := by
  classical
  let P := (D.erase 0).image Int.natAbs
  have hsub : D.erase 0 ⊆ (P.image (fun n : ℕ => (n:ℤ))) ∪
      (P.image (fun n : ℕ => -(n:ℤ))) := by
    intro d hd
    have habs : d.natAbs ∈ P := Finset.mem_image.mpr ⟨d,hd,rfl⟩
    rcases Int.natAbs_eq d with he | he
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨d.natAbs,habs,he.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨d.natAbs,habs,he.symm⟩)
  have hc : (D.erase 0).card ≤ 2*P.card := by
    calc
      _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ P.card+P.card := add_le_add (Finset.card_image_le) (Finset.card_image_le)
      _ = _ := by omega
  have hD : D ⊆ insert 0 (D.erase 0) := by
    intro d hd
    by_cases he : d=0
    · simp only [he,Finset.mem_insert_self]
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨he,hd⟩)
  change D.card ≤ 2*P.card+1
  exact (Finset.card_le_card hD).trans ((Finset.card_insert_le _ _).trans (by omega))

                                                                      
                                                                       
                               
theorem small_error_integer_of_unit_determinant
    (D : Finset ℤ) {B ε α : ℝ}
    (hε : 0 ≤ ε) (hunit : ∃ d ∈ D, d.natAbs=1)
    (hsize : ∀ d ∈ D, (d.natAbs:ℝ) ≤ B*(D.card:ℝ))
    (hsmall : 36*B*ε < 1)
    (hnear : ∀ d ∈ D, ∃ b : ℤ, |(d:ℝ)*α-b| ≤ ε) :
    |α-(round α:ℤ)| ≤ 3*ε/(D.card:ℝ) := by
  classical
  let P := (D.erase 0).image Int.natAbs
  obtain ⟨d₁,hd₁,hone⟩ := hunit
  have hd₁ne : d₁ ≠ 0 := by intro he; simp only [he,Int.natAbs_zero] at hone; omega
  have h1 : 1 ∈ P := Finset.mem_image.mpr ⟨d₁,Finset.mem_erase.mpr ⟨hd₁ne,hd₁⟩,hone⟩
  have hPne : P.Nonempty := ⟨1,h1⟩
  have hDR : (0:ℝ) < D.card := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨d₁,hd₁⟩)
  have hcard : (D.card:ℝ) ≤ 3*(P.card:ℝ) := by
    have h := card_le_two_mul_nonzero_abs_card_add_one D
    change D.card ≤ 2*P.card+1 at h
    have hp : 1 ≤ P.card := Finset.card_pos.mpr hPne
    exact_mod_cast (show D.card ≤ 3*P.card by omega)
  let L := P.max' hPne
  have hL : L ∈ P := Finset.max'_mem _ _
  have hLN : 0 < L := by have h := Finset.le_max' P 1 h1; omega
  have hPL : ∀ n ∈ P, 1 ≤ n ∧ n ≤ L := by
    intro n hn
    refine ⟨?_,Finset.le_max' P n hn⟩
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hn
    have hdne := (Finset.mem_erase.mp hd).1
    exact Nat.pos_of_ne_zero (by simpa using hdne)
  have hLsize : (L:ℝ) ≤ B*(D.card:ℝ) := by
    obtain ⟨d,hd,he⟩ := Finset.mem_image.mp hL
    rw [← he]
    exact hsize d (Finset.mem_erase.mp hd).2
  have hPnear : ∀ n ∈ P, ∃ b : ℤ, |(n:ℝ)*α-b| ≤ ε := by
    intro n hn
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨b,hb⟩ := hnear d (Finset.mem_erase.mp hd).2
    rcases Int.natAbs_eq d with he | he
    · refine ⟨b,?_⟩
      have heR : (d:ℝ) = (d.natAbs:ℝ) := by
        simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ℝ)) he
      rwa [← heR]
    · refine ⟨-b,?_⟩
      have heR : (d:ℝ) = -(d.natAbs:ℝ) := by
        simpa only [Int.cast_natCast,Int.cast_neg] using congrArg (fun z : ℤ => (z:ℝ)) he
      have hid : (d.natAbs:ℝ)*α-((-b:ℤ):ℝ) = -((d:ℝ)*α-b) := by
        rw [heR,Int.cast_neg]
        ring
      rwa [hid,abs_neg]
  rcases linear_form_dichotomy P hLN hε hPL hPnear with hc | ⟨q,_hq,_hqL,hdvd,a,ha⟩
  · have hbound := mul_le_mul_of_nonneg_left hLsize (by positivity : 0 ≤ 12*ε)
    have hstrict := mul_lt_mul_of_pos_right hsmall hDR
    nlinarith only [hc,hbound,hcard,hstrict]
  · have hq : q=1 := Nat.dvd_one.mp (hdvd 1 h1)
    rw [hq] at ha
    simp only [Nat.cast_one,one_mul] at ha
    have hr := round_le α a
    have hbound := mul_le_mul_of_nonneg_right hcard (abs_nonneg (α-(a:ℝ)))
    have hfinal : |α-(a:ℝ)| * (D.card:ℝ) ≤ 3*ε := by nlinarith only [hbound,ha]
    exact hr.trans ((le_div_iff₀ hDR).mpr hfinal)

theorem fareySector_determinant_bound
    {N : ℕ} {l μ : ℝ} {p₀ p : ℤ × ℤ}
    (hl : 0 < l) (hμ : 0 ≤ μ)
    (hp₀ : p₀ ∈ fareySector N l μ) (hp : p ∈ fareySector N l μ) :
    |((p₀.1*p.2-p₀.2*p.1:ℤ):ℝ)| ≤ (μ-l)*(N:ℝ)^2 := by
  obtain ⟨hn₀,hn₀N,_hc₀,hl₀,hu₀⟩ := (mem_fareySector_iff hl hμ).mp hp₀
  obtain ⟨hn,hnN,_hc,hlp,hup⟩ := (mem_fareySector_iff hl hμ).mp hp
  have hn₀R : (0:ℝ) < p₀.2 := by exact_mod_cast (show 0 < p₀.2 by omega)
  have hnR : (0:ℝ) < p.2 := by exact_mod_cast (show 0 < p.2 by omega)
  have hn₀NR : (p₀.2:ℝ) ≤ N := by exact_mod_cast hn₀N
  have hnNR : (p.2:ℝ) ≤ N := by exact_mod_cast hnN
  have hlμ : l ≤ μ := (mul_le_mul_iff_left₀ hn₀R).mp (by nlinarith only [hl₀,hu₀])
  have hlocal : |(p₀.1:ℝ)*p.2-(p₀.2:ℝ)*p.1| ≤ (μ-l)*((p.2:ℝ)*p₀.2) := by
    apply abs_le.mpr
    constructor
    · nlinarith only [mul_le_mul_of_nonneg_right hl₀ hnR.le,
        mul_le_mul_of_nonneg_right hup hn₀R.le]
    · nlinarith only [mul_le_mul_of_nonneg_right hu₀ hnR.le,
        mul_le_mul_of_nonneg_right hlp hn₀R.le]
  have hprod : (p.2:ℝ)*p₀.2 ≤ (N:ℝ)^2 := by
    nlinarith only [mul_le_mul hnNR hn₀NR hn₀R.le (Nat.cast_nonneg N)]
  push_cast
  exact hlocal.trans (mul_le_mul_of_nonneg_left hprod (sub_nonneg.mpr hlμ))

                                                               
                                                                        
                                                                    
                                                                        
theorem fareySector_small_error_bounds
    {N : ℕ} {l μ B α β δ : ℝ}
    (hl : 0 < l) (hμ : 1 ≤ μ) (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hR : max ((μ-l)*(N:ℝ)^2/B) 2 ≤ (fareySector N l μ).card)
    (hsmall : (μ*(N:ℝ))*δ ≤ 1/(96*B))
    (hnear : ∀ p ∈ fareySector N l μ,
      ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ) :
    |α-(round α:ℤ)| ≤ 8*(N:ℝ)*δ/(fareySector N l μ).card ∧
    |β-(round β:ℤ)| ≤ 8*(μ*(N:ℝ))*δ/(fareySector N l μ).card := by
  classical
  let S := fareySector N l μ
  have hμ0 : 0 ≤ μ := by linarith
  have hB0 : 0 < B := by linarith
  have hR2 : 2 ≤ S.card := by
    exact_mod_cast (le_trans (le_max_right ((μ-l)*(N:ℝ)^2/B) 2) hR)
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p₀,hp₀,hmax⟩ := S.exists_max_image Prod.snd hSne
  obtain ⟨p,hp,hne⟩ := Finset.exists_mem_ne (by omega : 1 < S.card) p₀
  obtain ⟨r,hr,hrunit⟩ := fareySector_exists_unit_determinant hl hμ0 hp₀ hp hne (hmax p hp)
  obtain ⟨hn₀,hn₀N,hcop₀,_hl₀,hu₀⟩ := (mem_fareySector_iff hl hμ0).mp hp₀
  have hn₀pos : 0 < p₀.2 := by omega
  let f : ℤ × ℤ → ℤ := fun t => p₀.1*t.2-p₀.2*t.1
  let D := S.image f
  have hinj : Set.InjOn f S := by
    intro t ht u hu he
    exact maximal_denominator_determinant_injective hn₀pos hcop₀
      ⟨((mem_fareySector_iff hl hμ0).mp ht).1,hmax t ht⟩
      ⟨((mem_fareySector_iff hl hμ0).mp hu).1,hmax u hu⟩ he
  have hDcard : D.card=S.card := Finset.card_image_of_injOn hinj
  have hunit : ∃ d ∈ D, d.natAbs=1 := by
    refine ⟨f r,Finset.mem_image.mpr ⟨r,hr,rfl⟩,?_⟩
    have h : |f r|=1 := hrunit
    exact Int.ofNat_inj.mp ((Int.natCast_natAbs (f r)).trans h)
  have hsize : ∀ d ∈ D, (d.natAbs:ℝ) ≤ B*(D.card:ℝ) := by
    intro d hd
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hd
    have hb := fareySector_determinant_bound hl hμ0 hp₀ ht
    have hw : (μ-l)*(N:ℝ)^2 ≤ B*(S.card:ℝ) := by
      have h := le_trans (le_max_left ((μ-l)*(N:ℝ)^2/B) 2) hR
      have hd := (div_le_iff₀ hB0).mp h
      nlinarith only [hd]
    rw [hDcard,Nat.cast_natAbs,Int.cast_abs]
    exact hb.trans hw
  have hNleM : (N:ℝ) ≤ μ*(N:ℝ) := by nlinarith only [mul_le_mul_of_nonneg_right hμ (Nat.cast_nonneg N)]
  have hbase : 96*B*(μ*(N:ℝ))*δ ≤ 1 := by
    have h := (le_div_iff₀ (by positivity : 0 < 96*B)).mp hsmall
    nlinarith only [h]
  have hsmallα : 36*B*(2*(N:ℝ)*δ) < 1 := by
    have h := mul_le_mul_of_nonneg_left hNleM (by positivity : 0 ≤ B*δ)
    nlinarith only [h,hbase]
  have hsmallβ : 36*B*(2*(μ*(N:ℝ))*δ) < 1 := by nlinarith only [hbase]
  obtain ⟨b₀,hb₀⟩ := hnear p₀ hp₀
  have hnearα : ∀ d ∈ D, ∃ b : ℤ, |(d:ℝ)*α-b| ≤ 2*(N:ℝ)*δ := by
    intro d hd
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨b,hb⟩ := hnear t ht
    obtain ⟨hn,hnN,_hc,_hl,_hu⟩ := (mem_fareySector_iff hl hμ0).mp ht
    have htn : |(t.2:ℝ)| ≤ N := by
      rw [abs_of_nonneg (by exact_mod_cast (show 0 ≤ t.2 by omega))]
      exact_mod_cast hnN
    have htn₀ : |(p₀.2:ℝ)| ≤ N := by
      rw [abs_of_nonneg (by exact_mod_cast hn₀pos.le)]
      exact_mod_cast hn₀N
    exact ⟨t.2*b₀-p₀.2*b,determinant_alpha_near p₀.1 p₀.2 t.1 t.2 b₀ b htn htn₀ hb₀ hb⟩
  have hnum : ∀ t ∈ S, |(t.1:ℝ)| ≤ μ*(N:ℝ) := by
    intro t ht
    obtain ⟨hn,hnN,_hc,hlower,hupper⟩ := (mem_fareySector_iff hl hμ0).mp ht
    have hnR : (0:ℝ) ≤ t.2 := by exact_mod_cast (show 0 ≤ t.2 by omega)
    have htpos : (0:ℝ) ≤ t.1 := (mul_nonneg hl.le hnR).trans hlower
    rw [abs_of_nonneg htpos]
    exact hupper.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hnN) hμ0)
  have hnearβ : ∀ d ∈ D, ∃ b : ℤ, |(d:ℝ)*β-b| ≤ 2*(μ*(N:ℝ))*δ := by
    intro d hd
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨b,hb⟩ := hnear t ht
    exact ⟨p₀.1*b-t.1*b₀,determinant_beta_near p₀.1 p₀.2 t.1 t.2 b₀ b
      (hnum t ht) (hnum p₀ hp₀) hb₀ hb⟩
  have ha := small_error_integer_of_unit_determinant D (by positivity) hunit hsize hsmallα hnearα
  have hb := small_error_integer_of_unit_determinant D (by positivity) hunit hsize hsmallβ hnearβ
  rw [hDcard] at ha hb
  constructor
  · apply ha.trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    nlinarith only [mul_nonneg (Nat.cast_nonneg N) hδ]
  · apply hb.trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    nlinarith only [mul_nonneg (mul_nonneg hμ0 (Nat.cast_nonneg N)) hδ]

theorem denominator_fiber_card
    {N : ℕ} {l μ : ℝ} (hl : 0 < l) (hlμ : l ≤ μ)
    {n : ℤ} (hn : 0 ≤ n) :
    (((fareySector N l μ).filter (fun p => p.2=n)).card:ℝ) ≤ (μ-l)*(n:ℝ)+1 := by
  classical
  let T := (fareySector N l μ).filter (fun p => p.2=n)
  let A := T.image Prod.fst
  have hcard : A.card=T.card := Finset.card_image_of_injOn (by
    intro p hp q hq he
    exact Prod.ext he ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm))
  have hμ : 0 ≤ μ := hl.le.trans hlμ
  have hnR : (0:ℝ) ≤ n := by exact_mod_cast hn
  have hrad : 0 ≤ (μ-l)*(n:ℝ)/2 := by positivity
  have hnear : ∀ m ∈ A, |(m:ℝ)-(l+μ)*(n:ℝ)/2| ≤ (μ-l)*(n:ℝ)/2 := by
    intro m hm
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hpS,hpn⟩ := Finset.mem_filter.mp hp
    obtain ⟨_hpn,_hpN,_hc,hlower,hupper⟩ := (mem_fareySector_iff hl hμ).mp hpS
    rw [hpn] at hlower hupper
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have h := integer_card_le_of_abs_sub_le A hrad hnear
  rw [hcard] at h
  change (T.card:ℝ) ≤ _
  linarith


                                                                    
                                                                      
theorem fareySector_card_le (N : ℕ) {l μ : ℝ} (hl : 0 < l) (hlμ : l ≤ μ) :
    ((fareySector N l μ).card:ℝ) ≤ (μ-l)*(N:ℝ)*((N:ℝ)+1)/2+(N:ℝ) := by
  classical
  have hμ : 0 ≤ μ := hl.le.trans hlμ
  induction N with
  | zero =>
    have hS : fareySector 0 l μ=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have h := (mem_fareySector_iff hl hμ).mp hp
      norm_num at h
      omega
    simp [hS]
  | succ N ih =>
    let T := (fareySector (N+1) l μ).filter (fun p => p.2=((N+1:ℕ):ℤ))
    have hsub : fareySector (N+1) l μ ⊆ fareySector N l μ ∪ T := by
      intro p hp
      obtain ⟨hn,hnN,hc,hlower,hupper⟩ := (mem_fareySector_iff hl hμ).mp hp
      by_cases hnold : p.2 ≤ (N:ℤ)
      · exact Finset.mem_union_left _ ((mem_fareySector_iff hl hμ).mpr
          ⟨hn,hnold,hc,hlower,hupper⟩)
      · apply Finset.mem_union_right
        apply Finset.mem_filter.mpr
        refine ⟨hp,?_⟩
        push_cast at hnN ⊢
        omega
    have hc : ((fareySector (N+1) l μ).card:ℝ) ≤
        (fareySector N l μ).card+(T.card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hf : (T.card:ℝ) ≤ (μ-l)*((N:ℝ)+1)+1 := by
      simpa only [T,Nat.cast_add,Nat.cast_one,Int.cast_natCast,Int.cast_add,Int.cast_one] using
        denominator_fiber_card (N := N+1) hl hlμ (n := (N+1:ℕ)) (by positivity)
    push_cast at hc ⊢
    nlinarith only [ih,hc,hf]

theorem large_sector_width
    {N : ℕ} {l μ : ℝ} (hl : 0 < l) (hlμ : l ≤ μ) (hN : 4 ≤ N)
    (hR : 16*(N:ℝ) ≤ (fareySector N l μ).card) :
    3*((fareySector N l μ).card:ℝ) ≤ 2*(μ-l)*(N:ℝ)^2 := by
  have hc := fareySector_card_le N hl hlμ
  have hNR : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hmul : 0 ≤ (μ-l)*(N:ℝ)*((N:ℝ)-4) :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hlμ) (Nat.cast_nonneg N)) (sub_nonneg.mpr hNR)
  nlinarith only [hc,hR,hmul]

theorem prime_coprime_consecutive {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (a : ℕ) :
    ∃ m : ℕ, a ≤ m ∧ m ≤ a+2 ∧ p.Coprime m ∧ p.Coprime (m+1) := by
  have h1 : ¬p ∣ 1 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have h2 : ¬p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  by_cases ha : p ∣ a
  · refine ⟨a+1,by omega,by omega,hp.coprime_iff_not_dvd.mpr ?_,hp.coprime_iff_not_dvd.mpr ?_⟩
    · intro h; exact h1 ((Nat.dvd_add_right ha).mp h)
    · intro h
      exact h2 ((Nat.dvd_add_right ha).mp (by simpa only [Nat.add_assoc] using h))
  · by_cases ha1 : p ∣ a+1
    · refine ⟨a+2,by omega,by omega,hp.coprime_iff_not_dvd.mpr ?_,hp.coprime_iff_not_dvd.mpr ?_⟩
      · intro h
        exact h1 ((Nat.dvd_add_right ha1).mp (by convert h using 1))
      · intro h
        exact h2 ((Nat.dvd_add_right ha1).mp (by convert h using 1))
    · exact ⟨a,le_rfl,by omega,hp.coprime_iff_not_dvd.mpr ha,hp.coprime_iff_not_dvd.mpr ha1⟩


                                                                    
                                                                       
                                                                      
theorem large_sector_consecutive_numerators {N : ℕ} {l μ : ℝ}
    (hl : 0 < l) (hlμ : l ≤ μ) (hN : 4 ≤ N)
    (hR : 16*(N:ℝ) ≤ (fareySector N l μ).card) :
    ∃ m n : ℤ, (m,n) ∈ fareySector N l μ ∧ (m+1,n) ∈ fareySector N l μ := by
  have hμ : 0 ≤ μ := hl.le.trans hlμ
  obtain ⟨p,hp,hpl,hpu⟩ := Nat.exists_prime_lt_and_le_two_mul (N/2) (by omega)
  have hp3 : 3 ≤ p := by omega
  have hpN : p ≤ N := by omega
  have hNp : (N:ℝ) ≤ 2*(p:ℝ) := by exact_mod_cast (show N ≤ 2*p by omega)
  have hNR : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hw := large_sector_width hl hlμ hN hR
  have hwN : 24 ≤ (μ-l)*(N:ℝ) := by
    apply (mul_le_mul_iff_right₀ hNR).mp
    nlinarith only [hw,hR]
  have hwp : 4 ≤ (μ-l)*(p:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hNp (sub_nonneg.mpr hlμ)
    nlinarith only [hwN,h]
  let a := ⌊l*(p:ℝ)⌋₊+1
  obtain ⟨m,ham,hma,hcm,hcm1⟩ := prime_coprime_consecutive hp hp3 a
  have hlow : l*(p:ℝ) ≤ (m:ℝ) := by
    have hf := Nat.lt_floor_add_one (l*(p:ℝ))
    have hm : (⌊l*(p:ℝ)⌋₊:ℝ)+1 ≤ m := by exact_mod_cast ham
    linarith
  have hupp : (m:ℝ)+1 ≤ μ*(p:ℝ) := by
    have hf := Nat.floor_le (mul_nonneg hl.le (Nat.cast_nonneg p))
    have hm : (m:ℝ) ≤ (⌊l*(p:ℝ)⌋₊:ℝ)+3 := by exact_mod_cast hma
    linarith
  have hm0 : (m:ℝ) ≤ (m:ℝ)+1 := by linarith
  refine ⟨m,p,?_,?_⟩
  · apply (mem_fareySector_iff hl hμ).mpr
    refine ⟨by dsimp; exact_mod_cast hp.one_lt.le,by dsimp; exact_mod_cast hpN,hcm.symm.isCoprime,?_,?_⟩
    · simpa only [Int.cast_natCast] using hlow
    · simpa only [Int.cast_natCast] using hm0.trans hupp
  · apply (mem_fareySector_iff hl hμ).mpr
    refine ⟨by dsimp; exact_mod_cast hp.one_lt.le,by dsimp; exact_mod_cast hpN,?_,?_,?_⟩
    · simpa only [Nat.cast_add,Nat.cast_one] using hcm1.symm.isCoprime
    · simpa only [Int.cast_natCast,Int.cast_add,Int.cast_one] using hlow.trans hm0
    · simpa only [Int.cast_natCast,Int.cast_add,Int.cast_one] using hupp


                                                                    
                                                                               
theorem sector_consecutive_numerators {N : ℕ} {l μ : ℝ}
    (hl : 0 < l) (hlμ : l ≤ μ) (hN : 0 < N)
    (hR : 16*(N:ℝ) ≤ (fareySector N l μ).card) :
    ∃ m n : ℤ, (m,n) ∈ fareySector N l μ ∧ (m+1,n) ∈ fareySector N l μ := by
  by_cases hN4 : 4 ≤ N
  · exact large_sector_consecutive_numerators hl hlμ hN4 hR
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hN3 : (N:ℝ) ≤ 3 := by exact_mod_cast (show N ≤ 3 by omega)
  have hupper := fareySector_card_le N hl hlμ
  have hw : 4 ≤ μ-l := by
    have hh := mul_nonneg (mul_nonneg (sub_nonneg.mpr hlμ) hNR.le) (sub_nonneg.mpr hN3)
    apply (mul_le_mul_iff_right₀ hNR).mp
    nlinarith only [hupper,hR,hh]
  let m : ℤ := ⌊l⌋+1
  have hlow : l ≤ (m:ℝ) := by
    have hh := Int.lt_floor_add_one l
    simpa only [m,Int.cast_add,Int.cast_one] using hh.le
  have hupp : (m:ℝ)+1 ≤ μ := by
    have hh := Int.floor_le l
    dsimp [m]
    push_cast
    linarith
  have hN1 : (1:ℤ) ≤ N := by exact_mod_cast hN
  have hμ0 := hl.le.trans hlμ
  refine ⟨m,1,?_,?_⟩
  · apply (mem_fareySector_iff hl hμ0).mpr
    refine ⟨le_rfl,hN1,isCoprime_one_right,?_,?_⟩
    · simpa only [Int.cast_one,mul_one] using hlow
    · simp only [Int.cast_one,mul_one]; linarith
  · apply (mem_fareySector_iff hl hμ0).mpr
    refine ⟨le_rfl,hN1,isCoprime_one_right,?_,?_⟩
    · simp only [Int.cast_one,Int.cast_add,mul_one]; linarith
    · simpa only [Int.cast_one,Int.cast_add,mul_one] using hupp


                                                                      
                                                                        
                                         
theorem large_sector_alpha_bound {N : ℕ} {l μ α β δ : ℝ}
    (hl : 0 < l) (hμ : 1 ≤ μ) (hlμ : l ≤ μ) (hN : 0 < N)
    (hR : 16*(N:ℝ) ≤ (fareySector N l μ).card) (hδ : 0 ≤ δ)
    (hnear : ∀ p ∈ fareySector N l μ,
      ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ) :
    ((fareySector N l μ).card:ℝ) ≤ 96*δ*(μ*(N:ℝ))*(N:ℝ) ∨
      |α-(round α:ℤ)| ≤ 8*(N:ℝ)*δ/(fareySector N l μ).card := by
  classical
  let S := fareySector N l μ
  have hμ0 : 0 ≤ μ := by linarith
  have hNR : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hSR : (0:ℝ) < S.card := by dsimp [S]; nlinarith only [hR,hNR]
  have hmaps : ∀ p ∈ S, p.2 ∈ Finset.Icc (1:ℤ) N := by
    intro p hp
    have h := (mem_fareySector_iff hl hμ0).mp hp
    exact Finset.mem_Icc.mpr ⟨h.1,h.2.1⟩
  have hI : (Finset.Icc (1:ℤ) N).card=N := by simp
  have hIne : (Finset.Icc (1:ℤ) N).Nonempty := by
    exact ⟨1,Finset.mem_Icc.mpr ⟨le_rfl,by exact_mod_cast (show 1 ≤ N by omega)⟩⟩
  obtain ⟨n,_hn,hcount⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    hmaps hIne (b := (S.card:ℝ)/(N:ℝ)) (by rw [hI,nsmul_eq_mul]; exact le_of_eq (mul_div_cancel₀ _ hNR.ne'))
  let T := S.filter (fun p => p.2=n)
  change (S.card:ℝ)/(N:ℝ) ≤ (T.card:ℝ) at hcount
  have hTne : T.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp ((div_pos hSR hNR).trans_le hcount))
  obtain ⟨p₀,hp₀⟩ := hTne
  let D := T.image (fun p => p.1-p₀.1)
  let P := insert 1 ((D.erase 0).image Int.natAbs)
  have hDcard : D.card=T.card := Finset.card_image_of_injOn (by
    intro p hp q hq he
    apply Prod.ext (by dsimp at he; omega)
    exact (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm)
  have hTP : (T.card:ℝ) ≤ 2*(P.card:ℝ)+1 := by
    have hc := card_le_two_mul_nonzero_abs_card_add_one D
    have hsub : (D.erase 0).image Int.natAbs ⊆ P := Finset.subset_insert _ _
    have hh := Finset.card_le_card hsub
    rw [hDcard] at hc
    exact_mod_cast (show T.card ≤ 2*P.card+1 by omega)
  have hcard : (S.card:ℝ) ≤ 4*(N:ℝ)*(P.card:ℝ) := by
    have hc := (div_le_iff₀ hNR).mp hcount
    have ht := mul_le_mul_of_nonneg_left hTP hNR.le
    change 16*(N:ℝ) ≤ (S.card:ℝ) at hR
    nlinarith only [hc,ht,hR]
  have hPne : P.Nonempty := ⟨1,Finset.mem_insert_self _ _⟩
  let L := P.max' hPne
  have hL : L ∈ P := Finset.max'_mem _ _
  have hLpos : 0 < L := by have hh := Finset.le_max' P 1 (Finset.mem_insert_self _ _); omega
  have hnum (p : ℤ × ℤ) (hp : p ∈ S) : 0 ≤ (p.1:ℝ) ∧ (p.1:ℝ) ≤ μ*(N:ℝ) := by
    obtain ⟨hn,hnN,_hc,hlo,hu⟩ := (mem_fareySector_iff hl hμ0).mp hp
    have hnR : (0:ℝ) ≤ p.2 := by exact_mod_cast (show 0 ≤ p.2 by omega)
    exact ⟨(mul_nonneg hl.le hnR).trans hlo,
      hu.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hnN) hμ0)⟩
  have hPsize : ∀ k ∈ P, 1 ≤ k ∧ (k:ℝ) ≤ μ*(N:ℝ) := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · refine ⟨le_rfl,?_⟩
      have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      simpa only [one_mul,Nat.cast_one] using mul_le_mul hμ hN1 (by norm_num : (0:ℝ) ≤ 1) hμ0
    · obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hd0,hd⟩ := Finset.mem_erase.mp hd
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hd
      refine ⟨Nat.pos_of_ne_zero (by simpa using hd0),?_⟩
      rw [Nat.cast_natAbs,Int.cast_abs,Int.cast_sub]
      have hpnum := hnum p (Finset.mem_filter.mp hp).1
      have hp₀num := hnum p₀ (Finset.mem_filter.mp hp₀).1
      exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hdiff (p r : ℤ × ℤ) (hp : p ∈ S) (hr : r ∈ S) (he : p.2=r.2) :
      ∃ b : ℤ, |((p.1-r.1:ℤ):ℝ)*α-b| ≤ 2*δ := by
    obtain ⟨bp,hbp⟩ := hnear p hp
    obtain ⟨br,hbr⟩ := hnear r hr
    refine ⟨bp-br,?_⟩
    have hid : ((p.1-r.1:ℤ):ℝ)*α-((bp-br:ℤ):ℝ) =
        ((p.1:ℝ)*α+(p.2:ℝ)*β-bp)-((r.1:ℝ)*α+(r.2:ℝ)*β-br) := by
      rw [he]; push_cast; ring
    rw [hid]
    exact (abs_sub _ _).trans (by linarith)
  have hPnear : ∀ k ∈ P, ∃ b : ℤ, |(k:ℝ)*α-b| ≤ 2*δ := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · obtain ⟨m,n,hm,hm1⟩ := sector_consecutive_numerators hl hlμ hN hR
      simpa only [Prod.fst,add_sub_cancel_left,Int.cast_one,Nat.cast_one,one_mul] using
        hdiff (m+1,n) (m,n) hm1 hm rfl
    · obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hd).2
      obtain ⟨b,hb⟩ := hdiff p p₀ (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp₀).1
        ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hp₀).2.symm)
      rcases Int.natAbs_eq (p.1-p₀.1) with he | he
      · refine ⟨b,?_⟩
        have heR : ((p.1-p₀.1:ℤ):ℝ) = ((p.1-p₀.1).natAbs:ℝ) := by
          simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ℝ)) he
        rwa [← heR]
      · refine ⟨-b,?_⟩
        have heR : ((p.1-p₀.1:ℤ):ℝ) = -((p.1-p₀.1).natAbs:ℝ) := by
          simpa only [Int.cast_natCast,Int.cast_neg] using congrArg (fun z : ℤ => (z:ℝ)) he
        have hid : ((p.1-p₀.1).natAbs:ℝ)*α-((-b:ℤ):ℝ) = -(((p.1-p₀.1:ℤ):ℝ)*α-b) := by
          rw [heR,Int.cast_neg]; ring
        rwa [hid,abs_neg]
  rcases linear_form_dichotomy P hLpos (by positivity)
    (fun k hk => ⟨(hPsize k hk).1,Finset.le_max' P k hk⟩) hPnear with hc | ⟨q,_hq,_hqL,hdvd,a,ha⟩
  · left
    have hm := mul_le_mul_of_nonneg_left (hPsize L hL).2 (show 0 ≤ 24*δ by positivity)
    have hc' : (P.card:ℝ) ≤ 24*δ*(μ*(N:ℝ)) := by nlinarith only [hc,hm]
    have ht := mul_le_mul_of_nonneg_left hc' (show 0 ≤ 4*(N:ℝ) by positivity)
    
    nlinarith only [hcard,ht]
  · right
    have hq : q=1 := Nat.dvd_one.mp (hdvd 1 (Finset.mem_insert_self _ _))
    rw [hq] at ha
    simp only [Nat.cast_one,one_mul] at ha
    have ht := mul_le_mul_of_nonneg_left hcard (abs_nonneg (α-(a:ℝ)))
    have hh := mul_le_mul_of_nonneg_left ha (show 0 ≤ 4*(N:ℝ) by positivity)
    apply (round_le α a).trans
    apply (le_div_iff₀ hSR).mpr
    nlinarith only [ht,hh]


theorem sector_denominator_card_lower {N : ℕ} {l μ B : ℝ}
    (hl : 0 < l) (hlμ : l ≤ μ) (hN : 0 < N)
    (hR : (N:ℝ) ≤ (fareySector N l μ).card)
    (hdensity : (μ-l)*(N:ℝ)^2 ≤ B*(fareySector N l μ).card) :
    (N:ℝ) ≤ (B+1)*((fareySector N l μ).image Prod.snd).card := by
  classical
  let S := fareySector N l μ
  let E := S.image Prod.snd
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hSR : (0:ℝ) < S.card := hNR.trans_le hR
  have hwidth : (μ-l)*(N:ℝ)+1 ≤ (B+1)*(S.card:ℝ)/(N:ℝ) := by
    apply (le_div_iff₀ hNR).mpr
    nlinarith only [hdensity,hR]
  have hfiber : ∀ n ∈ E, ((S.filter (fun p => p.2=n)).card:ℝ) ≤
      (B+1)*(S.card:ℝ)/(N:ℝ) := by
    intro n hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    have hs := (mem_fareySector_iff hl (hl.le.trans hlμ)).mp hp
    apply (denominator_fiber_card hl hlμ (by omega : 0 ≤ p.2)).trans
    apply le_trans _ hwidth
    have hnN : (p.2:ℝ) ≤ N := by exact_mod_cast hs.2.1
    nlinarith only [mul_le_mul_of_nonneg_left hnN (sub_nonneg.mpr hlμ)]
  have heq : (S.card:ℝ) = ∑ n ∈ E, ((S.filter (fun p => p.2=n)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise (fun p hp => Finset.mem_image_of_mem Prod.snd hp)
  have hsum := Finset.sum_le_sum hfiber
  rw [← heq,Finset.sum_const,nsmul_eq_mul] at hsum
  have hprod := (le_div_iff₀ hNR).mp (show (S.card:ℝ) ≤
      ((E.card:ℝ)*((B+1)*(S.card:ℝ)))/(N:ℝ) by simpa only [mul_div_assoc] using hsum)
  apply (mul_le_mul_iff_right₀ hSR).mp
  nlinarith only [hprod]

theorem sector_denominator_common_divisor {N q : ℕ} {l μ : ℝ}
    (hl : 0 < l) (hμ : 0 ≤ μ) (hR : 2 ≤ (fareySector N l μ).card)
    (hdvd : ∀ p ∈ fareySector N l μ, q ∣ p.2.natAbs) : q=1 := by
  classical
  let S := fareySector N l μ
  change 2 ≤ S.card at hR
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p₀,hp₀,hmax⟩ := S.exists_max_image Prod.snd hne
  obtain ⟨p,hp,hneq⟩ := Finset.exists_mem_ne (by omega : 1 < S.card) p₀
  obtain ⟨r,hr,hunit⟩ := fareySector_exists_unit_determinant hl hμ hp₀ hp hneq (hmax p hp)
  have hd₀ : (q:ℤ) ∣ p₀.2 := Int.natCast_dvd.mpr (hdvd p₀ hp₀)
  have hdr : (q:ℤ) ∣ r.2 := Int.natCast_dvd.mpr (hdvd r hr)
  have hd : (q:ℤ) ∣ p₀.1*r.2-p₀.2*r.1 := dvd_sub (dvd_mul_of_dvd_right hdr _) (dvd_mul_of_dvd_left hd₀ _)
  have hh : q ∣ (p₀.1*r.2-p₀.2*r.1).natAbs := Int.natCast_dvd.mp hd
  have hu : (p₀.1*r.2-p₀.2*r.1).natAbs=1 :=
    Int.ofNat_inj.mp ((Int.natCast_natAbs _).trans hunit)
  rw [hu] at hh
  exact Nat.dvd_one.mp hh


theorem sector_card_le_twice_rectangle {N : ℕ} {l μ : ℝ}
    (hl : 0 < l) (hμ : 1 ≤ μ) (hlμ : l ≤ μ) (hN : 0 < N) :
    ((fareySector N l μ).card:ℝ) ≤ 2*μ*(N:ℝ)^2 := by
  have hu := fareySector_card_le N hl hlμ
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hμ0 : 0 ≤ μ := by linarith
  have ha := mul_le_mul_of_nonneg_left hN1 (mul_nonneg hμ0 hN0)
  have hb := mul_le_mul_of_nonneg_left hN1 hN0
  have hc := mul_le_mul_of_nonneg_right hμ (sq_nonneg (N:ℝ))
  have hd : 0 ≤ l*(N:ℝ)*((N:ℝ)+1) := by positivity
  nlinarith only [hu,ha,hb,hc,hd]

                                                                        
                                                                        
theorem sector_beta_bound {N : ℕ} {l μ B α β δ : ℝ}
    (hl : 0 < l) (hμ : 1 ≤ μ) (hlμ : l ≤ μ) (hB : 1 ≤ B) (hN : 0 < N)
    (hR : (N:ℝ) ≤ (fareySector N l μ).card) (hR2 : 2 ≤ (fareySector N l μ).card)
    (hdensity : (μ-l)*(N:ℝ)^2 ≤ B*(fareySector N l μ).card) (hδ : 0 ≤ δ)
    (hα : |α-(round α:ℤ)| ≤ 8*(N:ℝ)*δ/(fareySector N l μ).card)
    (hnear : ∀ p ∈ fareySector N l μ,
      ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ) :
    ((fareySector N l μ).card:ℝ) ≤ 240*B*δ*(μ*(N:ℝ))*(N:ℝ) ∨
      |β-(round β:ℤ)| ≤ 20*B*(μ*(N:ℝ))*δ/(fareySector N l μ).card := by
  classical
  let S := fareySector N l μ
  let E := S.image Prod.snd
  let D := E.image Int.natAbs
  let ε := 10*δ*μ*(N:ℝ)^2/(S.card:ℝ)
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hSR : (0:ℝ) < S.card := hNR.trans_le hR
  have hμ0 : 0 ≤ μ := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hden : ∀ n ∈ E, 1 ≤ n ∧ n ≤ N := by
    intro n hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    have h := (mem_fareySector_iff hl hμ0).mp hp
    exact ⟨h.1,h.2.1⟩
  have hDcard : D.card=E.card := Finset.card_image_of_injOn (by
    intro n hn m hm he
    exact (Int.natAbs_inj_of_nonneg_of_nonneg (by have hh := hden n hn; omega)
      (by have hh := hden m hm; omega)).mp he)
  have hdens := sector_denominator_card_lower hl hlμ hN hR hdensity
  change (N:ℝ) ≤ (B+1)*(E.card:ℝ) at hdens
  rw [← hDcard] at hdens
  have hDsize : ∀ n ∈ D, 1 ≤ n ∧ n ≤ N := by
    intro n hn
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
    have hh := hden m hm
    have he : (m.natAbs:ℤ)=m := (Int.natCast_natAbs m).trans (abs_of_nonneg (by omega))
    constructor <;> exact_mod_cast (show _ by omega)
  have hDnear : ∀ n ∈ D, ∃ b : ℤ, |(n:ℝ)*β-b| ≤ ε := by
    intro n hn
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hn₁,hnN,_hc,hlo,hu⟩ := (mem_fareySector_iff hl hμ0).mp hp
    have hn0 : (0:ℝ) ≤ p.2 := by exact_mod_cast (show 0 ≤ p.2 by omega)
    have hm0 : (0:ℝ) ≤ p.1 := (mul_nonneg hl.le hn0).trans hlo
    have hmM : (p.1:ℝ) ≤ μ*(N:ℝ) :=
      hu.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hnN) hμ0)
    obtain ⟨b,hb⟩ := hnear p hp
    refine ⟨b-p.1*(round α),?_⟩
    have he : (p.2.natAbs:ℝ)=(p.2:ℝ) := by
      rw [Nat.cast_natAbs,Int.cast_abs,abs_of_nonneg hn0]
    rw [he]
    have hid : (p.2:ℝ)*β-((b-p.1*(round α):ℤ):ℝ) =
        ((p.1:ℝ)*α+(p.2:ℝ)*β-b)-(p.1:ℝ)*(α-(round α:ℤ)) := by push_cast; ring
    rw [hid]
    apply (abs_sub _ _).trans
    rw [abs_mul,abs_of_nonneg hm0]
    have ha := mul_le_mul hmM hα (abs_nonneg _) (mul_nonneg hμ0 hNR.le)
    have hs := mul_le_mul_of_nonneg_left (sector_card_le_twice_rectangle hl hμ hlμ hN) hδ
    have hαR := (le_div_iff₀ hSR).mp (show (p.1:ℝ)*|α-(round α:ℤ)| ≤
        (μ*(N:ℝ)*(8*(N:ℝ)*δ))/(S.card:ℝ) by simpa only [mul_div_assoc] using ha)
    apply (le_div_iff₀ hSR).mpr
    have hbR := mul_le_mul_of_nonneg_right hb hSR.le
    nlinarith only [hs,hαR,hbR]
  rcases linear_form_dichotomy D hN (show 0 ≤ ε by dsimp [ε]; positivity)
    hDsize hDnear with hc | ⟨q,_hq,_hqN,hdvd,a,ha⟩
  · left
    have hcR : (D.card:ℝ)*(S.card:ℝ) ≤ 120*δ*μ*(N:ℝ)^3 := by
      have h := (le_div_iff₀ hSR).mp (show (D.card:ℝ) ≤
          (120*δ*μ*(N:ℝ)^3)/(S.card:ℝ) by convert hc using 1; dsimp [ε]; ring)
      exact h
    have hdR := mul_le_mul_of_nonneg_right hdens hSR.le
    have hcB := mul_le_mul_of_nonneg_left hcR (show 0 ≤ B+1 by linarith)
    have hB1 : B+1 ≤ 2*B := by linarith
    have hBB := mul_le_mul_of_nonneg_right hB1 (show 0 ≤ 120*δ*μ*(N:ℝ)^3 by positivity)
    apply (mul_le_mul_iff_right₀ hNR).mp
    nlinarith only [hdR,hcB,hBB]
  · right
    have hq : q=1 := sector_denominator_common_divisor hl hμ0 hR2 (by
      intro p hp
      exact hdvd p.2.natAbs (Finset.mem_image_of_mem Int.natAbs (Finset.mem_image_of_mem Prod.snd hp)))
    rw [hq] at ha
    simp only [Nat.cast_one,one_mul] at ha
    have haR := (le_div_iff₀ hSR).mp ha
    have hdA := mul_le_mul_of_nonneg_left hdens (abs_nonneg (β-(a:ℝ)))
    have hdAR := mul_le_mul_of_nonneg_right hdA hSR.le
    have haB := mul_le_mul_of_nonneg_left haR (show 0 ≤ B+1 by linarith)
    have hBB := mul_le_mul_of_nonneg_right (show B+1 ≤ 2*B by linarith)
      (show 0 ≤ 10*δ*μ*(N:ℝ)^2 by positivity)
    apply (round_le β a).trans
    apply (le_div_iff₀ hSR).mpr
    apply (mul_le_mul_iff_right₀ hNR).mp
    nlinarith only [hdAR,haB,hBB]


                                                                       
                                                                        
                                                                        
                                                                        
theorem fareySector_bounded_density_dichotomy
    {N : ℕ} {l μ B α β δ : ℝ}
    (hl : 0 < l) (hμ : 1 ≤ μ) (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hR : max ((μ-l)*(N:ℝ)^2/B) 2 ≤ (fareySector N l μ).card)
    (hnear : ∀ p ∈ fareySector N l μ,
      ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ) :
    ((fareySector N l μ).card:ℝ) ≤ 1536*B*δ*(μ*(N:ℝ))*(N:ℝ) ∨
      (|α-(round α:ℤ)| ≤ 8*(N:ℝ)*δ/(fareySector N l μ).card ∧
       |β-(round β:ℤ)| ≤ 20*B*(μ*(N:ℝ))*δ/(fareySector N l μ).card) := by
  have hB0 : 0 < B := by linarith
  have hμ0 : 0 ≤ μ := by linarith
  have hR2R : (2:ℝ) ≤ (fareySector N l μ).card := (le_max_right _ _).trans hR
  have hR2 : 2 ≤ (fareySector N l μ).card := by exact_mod_cast hR2R
  have hSne : (fareySector N l μ).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p,hp⟩ := hSne
  obtain ⟨hn,hnN,_hc,hlo,hu⟩ := (mem_fareySector_iff hl hμ0).mp hp
  have hN : 0 < N := by omega
  have hnR : (0:ℝ) < p.2 := by exact_mod_cast (show 0 < p.2 by omega)
  have hlμ : l ≤ μ := (mul_le_mul_iff_left₀ hnR).mp (hlo.trans hu)
  have hdensity : (μ-l)*(N:ℝ)^2 ≤ B*(fareySector N l μ).card := by
    have hh := (div_le_iff₀ hB0).mp ((le_max_left _ _).trans hR)
    nlinarith only [hh]
  by_cases hsmall : (μ*(N:ℝ))*δ ≤ 1/(96*B)
  · obtain ⟨ha,hb⟩ := fareySector_small_error_bounds hl hμ hB hδ hR hsmall hnear
    refine Or.inr ⟨ha,hb.trans ?_⟩
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have hh := mul_le_mul_of_nonneg_right hB (show 0 ≤ (μ*(N:ℝ))*δ by positivity)
    nlinarith only [hh,mul_nonneg (mul_nonneg hμ0 (Nat.cast_nonneg N)) hδ]
  by_cases hsize : ((fareySector N l μ).card:ℝ) ≤ 1536*B*δ*(μ*(N:ℝ))*(N:ℝ)
  · exact Or.inl hsize
  have hbase : 1 < 96*B*((μ*(N:ℝ))*δ) := by
    have hh := (div_lt_iff₀ (show 0 < 96*B by positivity)).mp (lt_of_not_ge hsmall)
    nlinarith only [hh]
  have hlarge : 16*(N:ℝ) ≤ (fareySector N l μ).card := by
    have hh := mul_le_mul_of_nonneg_right hbase.le (show 0 ≤ 16*(N:ℝ) by positivity)
    nlinarith only [hh,lt_of_not_ge hsize]
  have hRgeN : (N:ℝ) ≤ (fareySector N l μ).card := by
    nlinarith only [hlarge,(Nat.cast_nonneg N : (0:ℝ) ≤ N)]
  have hprod : 0 ≤ δ*(μ*(N:ℝ))*(N:ℝ) := by positivity
  rcases large_sector_alpha_bound hl hμ hlμ hN hlarge hδ hnear with hbad | ha
  · exact (hsize (by nlinarith only [hbad,mul_le_mul_of_nonneg_right hB hprod,hprod])).elim
  · rcases sector_beta_bound hl hμ hlμ hB hN hRgeN hR2 hdensity hδ ha hnear with hbad | hb
    · have hh : 0 ≤ B*(δ*(μ*(N:ℝ))*(N:ℝ)) := mul_nonneg hB0.le hprod
      exact (hsize (by nlinarith only [hbad,hh])).elim
    · exact Or.inr ⟨ha,hb⟩


                                                                            
                                                                       
                                                                           
end TaoTrudgianYang2025.HuxleyLinearForm
namespace TaoTrudgianYang2025.HuxleyRationalPhase
noncomputable def rationalBranch (μ r s x : ℝ) : ℝ := 1/(3*μ*r^2*(r*x+s))

theorem rationalBranch_second {μ r s x : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hx : r*x+s ≠ 0) :
    iteratedDeriv 2 (rationalBranch μ r s) x = 2/(3*μ*(r*x+s)^3) := by
  let f : ℝ → ℝ := fun y => 3*μ*r^2*(r*y+s)
  have hd : deriv f = fun _ => 3*μ*r^3 := by
    funext y
    have hh := (((hasDerivAt_id y).const_mul r).add_const s).const_mul (3*μ*r^2)
    have he : HasDerivAt f (3*μ*r^3) y := by
      convert hh using 1
      dsimp
      ring
    exact he.deriv
  have hne : f x ≠ 0 := by dsimp [f]; positivity
  have he := TaoTrudgianYang2025.iteratedDeriv_two_real_inv
    (show ContDiffAt ℝ 2 f x by dsimp [f]; fun_prop) hne
  have hbranch : rationalBranch μ r s = fun y => (f y)⁻¹ := by
    funext y
    simp only [rationalBranch,f,one_div]
  rw [hbranch,he,iteratedDeriv_succ,iteratedDeriv_one,hd]
  simp only [deriv_const,zero_div,sub_zero,f]
  field_simp

noncomputable def rationalPhase (μ r s μ₁ r₁ s₁ x : ℝ) : ℝ :=
  rationalBranch μ r s x-rationalBranch μ₁ r₁ s₁ x

                                                                   
                                                                         
theorem rationalPhase_second {μ r s μ₁ r₁ s₁ x : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr₁ : r₁ ≠ 0)
    (hx : r*x+s ≠ 0) (hx₁ : r₁*x+s₁ ≠ 0) :
    iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) x =
      2/(3*μ*(r*x+s)^3)-2/(3*μ₁*(r₁*x+s₁)^3) := by
  have ha : ContDiffAt ℝ 2 (rationalBranch μ r s) x := by
    exact contDiffAt_const.div (by fun_prop) (by positivity)
  have hb : ContDiffAt ℝ 2 (rationalBranch μ₁ r₁ s₁) x := by
    exact contDiffAt_const.div (by fun_prop) (by positivity)
  unfold rationalPhase
  rw [iteratedDeriv_fun_sub ha hb,
    rationalBranch_second hμ hr hx,rationalBranch_second hμ₁ hr₁ hx₁]

                                                                
                                                                    
theorem rationalPhase_curvature_of_cubic_ratio
    {μ r s μ₁ r₁ s₁ x ε : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hμ₁ : 0 < μ₁) (hr₁ : r₁ ≠ 0)
    (hx : r*x+s ≠ 0) (hx₁ : 0 < r₁*x+s₁)
    (hratio : |μ₁*(r₁*x+s₁)^3/(μ*(r*x+s)^3)-1| ≤ ε) :
    |iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) x| ≤
      (2/(3*μ₁*(r₁*x+s₁)^3))*ε := by
  rw [rationalPhase_second hμ hr hμ₁.ne' hr₁ hx hx₁.ne']
  have he : 2/(3*μ*(r*x+s)^3)-2/(3*μ₁*(r₁*x+s₁)^3) =
      (2/(3*μ₁*(r₁*x+s₁)^3))*(μ₁*(r₁*x+s₁)^3/(μ*(r*x+s)^3)-1) := by
    have haux (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
        2/(3*a)-2/(3*b) = (2/(3*b))*(b/a-1) := by field_simp
    simpa only [mul_assoc] using haux (μ*(r*x+s)^3) (μ₁*(r₁*x+s₁)^3)
      (mul_ne_zero hμ (pow_ne_zero 3 hx)) (mul_ne_zero hμ₁.ne' (pow_ne_zero 3 hx₁.ne'))
  rw [he,abs_mul,abs_of_pos (by positivity : 0 < 2/(3*μ₁*(r₁*x+s₁)^3))]
  exact mul_le_mul_of_nonneg_left hratio (by positivity)


                                                                   
                                                                 
                                                                     
                                              
noncomputable def minorArcCoordinate (μ r s x : ℝ) : ℝ := 1/(3*μ*r*(r*x+s))

                                                                
                                                                   
theorem exists_small_deriv_of_two_values {f f' : ℝ → ℝ} {a b h E : ℝ}
    (hh : 0 < h) (hgap : h ≤ b-a)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (ha : |f a| ≤ E) (hb : |f b| ≤ E) :
    ∃ y ∈ Set.Ioo a b, |f' y| ≤ 2*E/h := by
  have hab : a < b := by linarith only [hh,hgap]
  have hE : 0 ≤ E := (abs_nonneg _).trans ha
  obtain ⟨y,hy,he⟩ := exists_hasDerivAt_eq_slope f f' hab
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => hf x ⟨hx.1.le,hx.2.le⟩)
  refine ⟨y,hy,?_⟩
  rw [he,abs_div,abs_of_pos (sub_pos.mpr hab)]
  have hsum : |f b-f a| ≤ 2*E := by
    have ht : |f b-f a| ≤ |f b|+|f a| := by
      simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (f b) 0 (f a)
    linarith only [ht,ha,hb]
  exact (div_le_div_of_nonneg_right hsum (sub_pos.mpr hab).le).trans
    (div_le_div_of_nonneg_left (by positivity) hh hgap)

                                                                   
                                                                      
theorem four_point_curvature {f : ℝ → ℝ} {a b c d h E : ℝ}
    (hh : 0 < h) (hab : h ≤ b-a) (hbc : h ≤ c-b) (hcd : h ≤ d-c)
    (hf : ∀ x ∈ Set.Icc a d, ContDiffAt ℝ 2 f x)
    (ha : |f a| ≤ E) (hb : |f b| ≤ E) (hc : |f c| ≤ E) (hd : |f d| ≤ E) :
    ∃ z ∈ Set.Ioo a d, |iteratedDeriv 2 f z| ≤ 4*E/h^2 := by
  have hab' : a < b := by linarith only [hh,hab]
  have hbc' : b < c := by linarith only [hh,hbc]
  have hcd' : c < d := by linarith only [hh,hcd]
  have hf' (x : ℝ) (hx : x ∈ Set.Icc a d) : HasDerivAt f (deriv f x) x :=
    ((hf x hx).differentiableAt (by norm_num)).hasDerivAt
  obtain ⟨y₁,hy₁,he₁⟩ := exists_small_deriv_of_two_values hh hab
    (fun x hx => hf' x ⟨hx.1,le_trans hx.2 (hbc'.trans hcd').le⟩) ha hb
  obtain ⟨y₂,hy₂,he₂⟩ := exists_small_deriv_of_two_values hh hcd
    (fun x hx => hf' x ⟨le_trans (hab'.trans hbc').le hx.1,hx.2⟩) hc hd
  have hygap : h ≤ y₂-y₁ := by linarith only [hbc,hy₁.2,hy₂.1]
  have hder (x : ℝ) (hx : x ∈ Set.Icc y₁ y₂) :
      HasDerivAt (deriv f) (iteratedDeriv 2 f x) x := by
    have hhx := TaoTrudgianYang2025.hasDerivAt_iteratedDeriv_finite
      (by norm_num : 1 < 2) (hf x ⟨hy₁.1.le.trans hx.1,hx.2.trans hy₂.2.le⟩)
    simpa only [iteratedDeriv_one] using hhx
  obtain ⟨z,hz,hez⟩ := exists_small_deriv_of_two_values hh hygap hder he₁ he₂
  refine ⟨z,⟨hy₁.1.trans hz.1,hz.2.trans hy₂.2⟩,?_⟩
  convert hez using 1
  ring

                                                                   
                                                 
theorem rationalPhase_cubic_ratio_abs_eq
    {μ r s μ₁ r₁ s₁ x : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr₁ : r₁ ≠ 0)
    (hx : r*x+s ≠ 0) (hx₁ : r₁*x+s₁ ≠ 0) :
    |μ₁*(r₁*x+s₁)^3/(μ*(r*x+s)^3)-1| =
      (3*|μ₁| * |r₁*x+s₁|^3/2)*|iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) x| := by
  rw [rationalPhase_second hμ hr hμ₁ hr₁ hx hx₁]
  have haux (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
      b/a-1=(3*b/2)*(2/(3*a)-2/(3*b)) := by field_simp
  rw [haux (μ*(r*x+s)^3) (μ₁*(r₁*x+s₁)^3)
    (mul_ne_zero hμ (pow_ne_zero 3 hx)) (mul_ne_zero hμ₁ (pow_ne_zero 3 hx₁))]
  norm_num only [abs_mul,abs_div,abs_pow,abs_of_pos (by norm_num : (0:ℝ) < 3),
    abs_of_pos (by norm_num : (0:ℝ) < 2)]
  ring_nf


                                                                  
                                                                       
                                                                           
theorem minorArcCoordinate_difference {μ r s a b : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (ha : r*a+s ≠ 0) (hb : r*b+s ≠ 0) :
    minorArcCoordinate μ r s b-minorArcCoordinate μ r s a =
      -(b-a)/(3*μ*(r*b+s)*(r*a+s)) := by
  dsimp [minorArcCoordinate]
  field_simp [hμ,hr,ha,hb]
  ring

                                                                
                                                                   
theorem minorArcCoordinate_gap_lower {μ r s a b h D : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hh : 0 < h) (hD : 0 < D)
    (ha : r*a+s ≠ 0) (hb : r*b+s ≠ 0)
    (haD : |r*a+s| ≤ D) (hbD : |r*b+s| ≤ D) (hgap : h ≤ b-a) :
    h/(3*|μ| * D^2) ≤ |minorArcCoordinate μ r s b-minorArcCoordinate μ r s a| := by
  rw [minorArcCoordinate_difference hμ hr ha hb,abs_div,abs_neg,
    abs_of_pos (by linarith only [hh,hgap] : 0 < b-a)]
  norm_num only [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 3)]
  have hmul : |r*b+s| * |r*a+s| ≤ D^2 := by
    nlinarith only [mul_le_mul hbD haD (abs_nonneg (r*a+s)) hD.le]
  calc
    _ ≤ (b-a)/(3*|μ| * D^2) := div_le_div_of_nonneg_right hgap (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by linarith only [hh,hgap]) (by positivity)
      (by nlinarith only [mul_le_mul_of_nonneg_left hmul (show 0 ≤ 3*|μ| by positivity)])

                                                                       
                                                                          
                                                                        
                                                                       
theorem point_gap_of_minorArcCoordinate_gap {μ r s a b d H : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hab : a ≤ b) (hd : 0 < d) (hH : 0 ≤ H)
    (ha : d ≤ |r*a+s|) (hb : d ≤ |r*b+s|)
    (hgap : H ≤ |minorArcCoordinate μ r s b-minorArcCoordinate μ r s a|) :
    3*|μ| * d^2*H ≤ b-a := by
  have hna : r*a+s ≠ 0 := abs_pos.mp (hd.trans_le ha)
  have hnb : r*b+s ≠ 0 := abs_pos.mp (hd.trans_le hb)
  rw [minorArcCoordinate_difference hμ hr hna hnb,abs_div,abs_neg,
    abs_of_nonneg (sub_nonneg.mpr hab)] at hgap
  norm_num only [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 3)] at hgap
  have hg := (le_div_iff₀ (by positivity : 0 < 3*|μ| * |r*b+s| * |r*a+s|)).mp hgap
  have hp : d^2 ≤ |r*b+s| * |r*a+s| := by
    nlinarith only [mul_le_mul hb ha hd.le (abs_nonneg (r*b+s))]
  have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ 3*|μ| * H by positivity)
  nlinarith only [hh,hg]

theorem scaled_minorArcCoordinate_abs {μ r s x : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hx : r*x+s ≠ 0) :
    |r*minorArcCoordinate μ r s x| = 1/(3*|μ| * |r*x+s|) := by
  dsimp [minorArcCoordinate]
  norm_num only [abs_mul,abs_div,abs_one,abs_of_pos (by norm_num : (0:ℝ) < 3)]
  field_simp

                                                              
                                                                          
                                                                        
                                                                 
                                                                   
theorem affine_ratio_mem_endpoint_interval {r s r₁ s₁ a b z : ℝ}
    (hz : z ∈ Set.Icc a b) (ha : 0 < r*a+s) (hb : 0 < r*b+s) (hmid : 0 < r*z+s) :
    (r₁*z+s₁)/(r*z+s) ∈ Set.uIcc ((r₁*a+s₁)/(r*a+s)) ((r₁*b+s₁)/(r*b+s)) := by
  rcases le_total 0 (r*s₁-s*r₁) with hC | hC
  · apply Set.mem_uIcc_of_ge
    · apply (div_le_div_iff₀ hb hmid).mpr
      nlinarith only [mul_nonneg hC (sub_nonneg.mpr hz.2)]
    · apply (div_le_div_iff₀ hmid ha).mpr
      nlinarith only [mul_nonneg hC (sub_nonneg.mpr hz.1)]
  · apply Set.mem_uIcc_of_le
    · apply (div_le_div_iff₀ ha hmid).mpr
      nlinarith only [mul_nonpos_of_nonpos_of_nonneg hC (sub_nonneg.mpr hz.1)]
    · apply (div_le_div_iff₀ hmid hb).mpr
      nlinarith only [mul_nonpos_of_nonpos_of_nonneg hC (sub_nonneg.mpr hz.2)]

                                                                    
                                                                     
                                                              
theorem ratio_relative_perturbation {a u v ε η : ℝ}
    (ha : |a-1| ≤ ε) (hu : |u-1| ≤ η) (hv : |v-1| ≤ η) (hη : η ≤ 1/2) :
    |a*u/v-1| ≤ 3*ε+4*η := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans ha
  have hη0 : 0 ≤ η := (abs_nonneg _).trans hu
  have hvhalf : (1:ℝ)/2 ≤ v := by linarith [(abs_le.mp hv).1]
  have hvpos : 0 < v := by linarith only [hvhalf]
  have hubound : |u| ≤ (3:ℝ)/2 := by
    apply abs_le.mpr
    constructor <;> linarith [(abs_le.mp hu).1,(abs_le.mp hu).2]
  have hid : a*u/v-1 = (u*(a-1)+(u-1)-(v-1))/v := by field_simp; ring
  have hnum : |u*(a-1)+(u-1)-(v-1)| ≤ (3/2:ℝ)*ε+2*η := by
    have h₁ := abs_add_le (u*(a-1)) (u-1)
    have h₂ := abs_add_le (u*(a-1)+(u-1)) (-(v-1))
    rw [abs_neg] at h₂
    rw [abs_mul] at h₁
    have hp := mul_le_mul hubound ha (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 3/2)
    change |u*(a-1)+(u-1)-(v-1)| ≤ _ at h₂
    linarith only [h₁,h₂,hp,hu,hv]
  rw [hid,abs_div,abs_of_pos hvpos]
  calc
    _ ≤ ((3/2:ℝ)*ε+2*η)/v := div_le_div_of_nonneg_right hnum hvpos.le
    _ ≤ ((3/2:ℝ)*ε+2*η)/(1/2) := div_le_div_of_nonneg_left (by positivity) (by norm_num) hvhalf
    _ = _ := by ring

                                                                
                                                                    
                                                                            
theorem cubicTaylorCoefficient_relative_variation
    {f : ℝ → ℝ} {a b U κ : ℝ} (hκ : 0 < κ)
    (hf : ∀ y ∈ Set.uIcc a b, ContDiffAt ℝ 4 f y)
    (hfourth : ∀ y ∈ Set.uIcc a b, |iteratedDeriv 4 f y| ≤ U)
    (hlower : κ ≤ |iteratedDeriv 3 f a|) :
    |(iteratedDeriv 3 f b/6)/(iteratedDeriv 3 f a/6)-1| ≤ U*|b-a|/κ := by
  have hbase : iteratedDeriv 3 f a ≠ 0 := abs_pos.mp (hκ.trans_le hlower)
  have hd (y : ℝ) (hy : y ∈ Set.uIcc a b) :
      HasDerivAt (iteratedDeriv 3 f) (iteratedDeriv 4 f y) y :=
    TaoTrudgianYang2025.hasDerivAt_iteratedDeriv_finite (by norm_num : 3 < 4) (hf y hy)
  have hdiff := (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y hy => (hd y hy).hasDerivWithinAt)
    (fun y hy => by simpa only [Real.norm_eq_abs] using hfourth y hy)
    Set.left_mem_uIcc Set.right_mem_uIcc
  change |iteratedDeriv 3 f b-iteratedDeriv 3 f a| ≤ U*|b-a| at hdiff
  have hid : (iteratedDeriv 3 f b/6)/(iteratedDeriv 3 f a/6)-1 =
      (iteratedDeriv 3 f b-iteratedDeriv 3 f a)/(iteratedDeriv 3 f a) := by field_simp
  rw [hid,abs_div]
  have hU : 0 ≤ U := (abs_nonneg _).trans (hfourth a Set.left_mem_uIcc)
  exact (div_le_div_of_nonneg_right hdiff (abs_nonneg _)).trans
    (div_le_div_of_nonneg_left (by positivity) hκ hlower)


                                                                  
                                                                         
                                                                          
                                                                         
theorem approximateModelPhase_cubicCoefficient_relative_variation
    {σ δ a b : ℝ} {F : ℝ → ℝ} (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 3 δ)
    (ha : a ∈ Set.Ioo (1:ℝ) 2) (hb : b ∈ Set.Ioo (1:ℝ) 2) :
    |(iteratedDeriv 3 F b/6)/(iteratedDeriv 3 F a/6)-1| ≤
      (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*|b-a|/
        TaoTrudgianYang2025.modelPhaseThirdLower σ := by
  have hseg (y : ℝ) (hy : y ∈ Set.uIcc a b) : y ∈ Set.Ioo (1:ℝ) 2 := by
    rw [Set.mem_uIcc] at hy
    rcases hy with hy | hy
    · exact ⟨ha.1.trans_le hy.1,hy.2.trans_lt hb.2⟩
    · exact ⟨hb.1.trans_le hy.1,hy.2.trans_lt ha.2⟩
  have hc (y : ℝ) (hy : y ∈ Set.uIcc a b) : ContDiffAt ℝ 4 F y :=
    (TaoTrudgianYang2025.approximateModelPhase_contDiffAt hF (hseg y hy)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)
  have hfourth (y : ℝ) (hy : y ∈ Set.uIcc a b) :
      |iteratedDeriv 4 F y| ≤ TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ := by
    have he := TaoTrudgianYang2025.approximateModelPhase_iteratedDeriv_error hF (hseg y hy) 3 le_rfl
    have hr := TaoTrudgianYang2025.iteratedDeriv_modelPhase_abs_le hσ.le (hseg y hy) 3
    have ht := abs_add_le (iteratedDeriv 4 F y-iteratedDeriv 3 (Expdb.modelPhase σ) y)
      (iteratedDeriv 3 (Expdb.modelPhase σ) y)
    rw [sub_add_cancel] at ht
    linarith only [he,hr,ht]
  have hlo := (TaoTrudgianYang2025.approximateModelPhase_thirdDeriv_bounds hσ hδ
    (TaoTrudgianYang2025.approximateModelPhase_mono hF (by norm_num : 2 ≤ 3) le_rfl) ha).1
  have hlo' : TaoTrudgianYang2025.modelPhaseThirdLower σ ≤ |iteratedDeriv 3 F a| := by
    have hraw : TaoTrudgianYang2025.modelPhaseThirdLower σ ≤ iteratedDeriv 3 F a := by
      simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hlo
    exact hraw.trans (le_abs_self _)
  exact cubicTaylorCoefficient_relative_variation
    (TaoTrudgianYang2025.modelPhaseThirdLower_pos hσ) hc hfourth hlo'


                                                                  
                                                                
                                                                        
theorem physicalModelPhase_cubicCoefficient_relative_variation
    {σ δ T M A W a b : ℝ} {F : ℝ → ℝ} (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 3 δ)
    (hT : T ≠ 0) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (ha : a ∈ Set.Ioo 0 W) (hb : b ∈ Set.Ioo 0 W) :
    let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
    |(iteratedDeriv 3 f b/6)/(iteratedDeriv 3 f a/6)-1| ≤
      (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*|b-a|/
        (TaoTrudgianYang2025.modelPhaseThirdLower σ*M) := by
  dsimp only
  rw [TaoTrudgianYang2025.heathBrownPhysicalPhase_iteratedDeriv hF.1 hM hA hW hb,
    TaoTrudgianYang2025.heathBrownPhysicalPhase_iteratedDeriv hF.1 hM hA hW ha]
  simp only [one_mul]
  have hcoeff : T/M^3 ≠ 0 := div_ne_zero hT (pow_ne_zero _ hM.ne')
  have hcancel (u v c : ℝ) (hc : c ≠ 0) : (c*u/6)/(c*v/6)=(u/6)/(v/6) := by
    rw [show c*u/6=c*(u/6) by ring,show c*v/6=c*(v/6) by ring,mul_div_mul_left _ _ hc]
  rw [hcancel _ _ _ hcoeff]
  have he := approximateModelPhase_cubicCoefficient_relative_variation hσ hδ hF
    (TaoTrudgianYang2025.heathBrownPhysicalPoint_mem_interior hM hA hW ha)
    (TaoTrudgianYang2025.heathBrownPhysicalPoint_mem_interior hM hA hW hb)
  have hdist : (A+b)/M-(A+a)/M = (b-a)/M := by ring
  rw [hdist,abs_div,abs_of_pos hM] at he
  convert he using 1
  ring


                                                                   
                                                                          
                                                                     
                                                                 
theorem halfCurvature_first_order_remainder
    {f : ℝ → ℝ} {a b U : ℝ}
    (hf : ∀ y ∈ Set.uIcc a b, ContDiffAt ℝ 4 f y)
    (hfourth : ∀ y ∈ Set.uIcc a b, |iteratedDeriv 4 f y| ≤ U) :
    |iteratedDeriv 2 f b/2-iteratedDeriv 2 f a/2-
      3*(iteratedDeriv 3 f a/6)*(b-a)| ≤ U*|b-a|^2/4 := by
  have hg (y : ℝ) (hy : y ∈ Set.uIcc a b) : ContDiffAt ℝ 2 (iteratedDeriv 2 f) y :=
    TaoTrudgianYang2025.contDiffAt_iteratedDeriv_finite (n := 2) (j := 2) (hf y hy)
  have hgg (y : ℝ) (hy : y ∈ Set.uIcc a b) :
      |iteratedDeriv 2 (iteratedDeriv 2 f) y| ≤ U := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hfourth y hy
  have he := TaoTrudgianYang2025.abs_finiteTaylorPolynomial_remainder_le_finite 1 hg hgg
  have hpoly : TaoTrudgianYang2025.finiteTaylorPolynomial (iteratedDeriv 2 f) 1 a b =
      iteratedDeriv 2 f a+iteratedDeriv 3 f a*(b-a) := by
    simp [TaoTrudgianYang2025.finiteTaylorPolynomial,taylor_within_apply,iteratedDeriv_succ]
    ring
  rw [hpoly] at he
  norm_num only [Nat.reduceAdd,Nat.factorial,Nat.cast_ofNat] at he
  have hid : iteratedDeriv 2 f b/2-iteratedDeriv 2 f a/2-
      3*(iteratedDeriv 3 f a/6)*(b-a) =
      (iteratedDeriv 2 f b-(iteratedDeriv 2 f a+iteratedDeriv 3 f a*(b-a)))/2 := by ring
  rw [hid,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hh := div_le_div_of_nonneg_right he (by norm_num : (0:ℝ) ≤ 2)
  convert hh using 1
  ring


                                                               
                                                            
theorem farey_curvature_coordinate_identity {μ e r v s u t : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0)
    (hdet : v*r-e*s=1) :
    (e*u+v*t)/(r*u+s*t)-e/r = 3*μ*minorArcCoordinate μ r s (u/t) := by
  have hleft : (e*u+v*t)/(r*u+s*t)-e/r = t/(r*(r*u+s*t)) := by
    apply (div_sub_div _ _ hq hr).trans
    rw [mul_comm (r*u+s*t) r]
    congr 1
    linear_combination t*hdet
  rw [hleft]
  dsimp [minorArcCoordinate]
  have hden : r*(u/t)+s = (r*u+s*t)/t := by field_simp
  rw [hden]
  field_simp

                                                                    
                                                                        
                                                                       
theorem minorArcCoordinate_taylor_entry
    {f : ℝ → ℝ} {a b U e r v s u t δ₀ δ₁ : ℝ}
    (hf : ∀ y ∈ Set.uIcc a b, ContDiffAt ℝ 4 f y)
    (hfourth : ∀ y ∈ Set.uIcc a b, |iteratedDeriv 4 f y| ≤ U)
    (hμ : iteratedDeriv 3 f a/6 ≠ 0)
    (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1)
    (hbase : iteratedDeriv 2 f a/2 = e/r+δ₀)
    (hpoint : iteratedDeriv 2 f b/2 = (e*u+v*t)/(r*u+s*t)+δ₁) :
    |(b-a)-minorArcCoordinate (iteratedDeriv 3 f a/6) r s (u/t)-
      (δ₁-δ₀)/(3*(iteratedDeriv 3 f a/6))| ≤
      U*|b-a|^2/(12*|iteratedDeriv 3 f a/6|) := by
  let μ := iteratedDeriv 3 f a/6
  have he := halfCurvature_first_order_remainder hf hfourth
  have hg := farey_curvature_coordinate_identity hμ hr ht hq hdet
  change (e*u+v*t)/(r*u+s*t)-e/r = 3*μ*minorArcCoordinate μ r s (u/t) at hg
  rw [hbase,hpoint] at he
  change |(e*u+v*t)/(r*u+s*t)+δ₁-(e/r+δ₀)-3*μ*(b-a)| ≤ U*|b-a|^2/4 at he
  have hnum : (e*u+v*t)/(r*u+s*t)+δ₁-(e/r+δ₀)-3*μ*(b-a) =
      -(3*μ*((b-a)-minorArcCoordinate μ r s (u/t)-(δ₁-δ₀)/(3*μ))) := by
    have hc : (3*μ)*((δ₁-δ₀)/(3*μ)) = δ₁-δ₀ :=
      mul_div_cancel₀ _ (mul_ne_zero (by norm_num) hμ)
    linear_combination hg-hc
  rw [hnum,abs_neg,abs_mul] at he
  change |(b-a)-minorArcCoordinate μ r s (u/t)-(δ₁-δ₀)/(3*μ)| ≤ _
  have hpos : 0 < |3*μ| := abs_pos.mpr (mul_ne_zero (by norm_num) hμ)
  have hh : |(b-a)-minorArcCoordinate μ r s (u/t)-(δ₁-δ₀)/(3*μ)| ≤
      (U*|b-a|^2/4)/|3*μ| :=
    (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using he)
  apply hh.trans_eq
  norm_num only [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 3)]
  ring


                                                                  
                                                                      
                                                                    
theorem physicalModelPhase_minorArcCoordinate_taylor_entry
    {σ δ T M A W a b e r v s u t δ₀ δ₁ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (ha : a ∈ Set.Ioo 0 W) (hb : b ∈ Set.Ioo 0 W)
    (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1) :
    let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
    iteratedDeriv 2 f a/2 = e/r+δ₀ →
    iteratedDeriv 2 f b/2 = (e*u+v*t)/(r*u+s*t)+δ₁ →
    |(b-a)-minorArcCoordinate (iteratedDeriv 3 f a/6) r s (u/t)-
      (δ₁-δ₀)/(3*(iteratedDeriv 3 f a/6))| ≤
      (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*|b-a|^2/
        (2*TaoTrudgianYang2025.modelPhaseThirdLower σ*M) := by
  let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
  let C := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ
  let κ := TaoTrudgianYang2025.modelPhaseThirdLower σ
  change _ → _ → _
  intro hbase hpoint
  have hκ : 0 < κ := TaoTrudgianYang2025.modelPhaseThirdLower_pos hσ
  have hseg (y : ℝ) (hy : y ∈ Set.uIcc a b) : y ∈ Set.Ioo 0 W := by
    rcases Set.mem_uIcc.mp hy with hy | hy
    · exact ⟨ha.1.trans_le hy.1,hy.2.trans_lt hb.2⟩
    · exact ⟨hb.1.trans_le hy.1,hy.2.trans_lt ha.2⟩
  have hc (y : ℝ) (hy : y ∈ Set.uIcc a b) : ContDiffAt ℝ 4 f y := by
    have hcf := TaoTrudgianYang2025.heathBrownPhysicalPhase_contDiffOn hF.1 hM hA hW T 1
    exact ((hcf y (Set.Ioo_subset_Icc_self (hseg y hy))).contDiffAt
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds (hseg y hy)) Set.Ioo_subset_Icc_self)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans
    (TaoTrudgianYang2025.approximateModelPhase_iteratedDeriv_error hF
      (TaoTrudgianYang2025.heathBrownPhysicalPoint_mem_interior hM hA hW ha) 3 le_rfl)
  have hC : 0 ≤ C := add_nonneg
    (TaoTrudgianYang2025.modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hf4 (y : ℝ) (hy : y ∈ Set.uIcc a b) : |iteratedDeriv 4 f y| ≤ T/M^4*C := by
    have hyp := TaoTrudgianYang2025.heathBrownPhysicalPoint_mem_interior hM hA hW (hseg y hy)
    have he := TaoTrudgianYang2025.approximateModelPhase_iteratedDeriv_error hF hyp 3 le_rfl
    have hm := TaoTrudgianYang2025.iteratedDeriv_modelPhase_abs_le hσ.le hyp 3
    have htri := abs_add_le (iteratedDeriv 4 F ((A+y)/M)-iteratedDeriv 3 (Expdb.modelPhase σ) ((A+y)/M))
      (iteratedDeriv 3 (Expdb.modelPhase σ) ((A+y)/M))
    rw [sub_add_cancel] at htri
    have hu : |iteratedDeriv 4 F ((A+y)/M)| ≤ C := by dsimp [C]; linarith only [he,hm,htri]
    dsimp only [f]
    rw [TaoTrudgianYang2025.heathBrownPhysicalPhase_iteratedDeriv hF.1 hM hA hW (hseg y hy),
      one_mul,abs_mul,abs_of_pos (by positivity : 0 < T/M^4)]
    exact mul_le_mul_of_nonneg_left hu (by positivity)
  have hlo : κ ≤ iteratedDeriv 3 F ((A+a)/M) := by
    have hh := (TaoTrudgianYang2025.approximateModelPhase_thirdDeriv_bounds hσ hδ
      (TaoTrudgianYang2025.approximateModelPhase_mono hF (by norm_num : 2 ≤ 3) le_rfl)
      (TaoTrudgianYang2025.heathBrownPhysicalPoint_mem_interior hM hA hW ha)).1
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hh
  have hμlo : (T/M^3)*κ/6 ≤ iteratedDeriv 3 f a/6 := by
    dsimp only [f]
    rw [TaoTrudgianYang2025.heathBrownPhysicalPhase_iteratedDeriv hF.1 hM hA hW ha,one_mul]
    gcongr
  have hμ : 0 < iteratedDeriv 3 f a/6 := lt_of_lt_of_le (by positivity) hμlo
  have he := minorArcCoordinate_taylor_entry hc hf4 hμ.ne' hr ht hq hdet hbase hpoint
  apply he.trans
  rw [abs_of_pos hμ]
  calc
    (T/M^4*C)*|b-a|^2/(12*(iteratedDeriv 3 f a/6)) ≤
        (T/M^4*C)*|b-a|^2/(12*((T/M^3)*κ/6)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hμlo (by norm_num))
    _ = C*|b-a|^2/(2*κ*M) := by field_simp; ring


                                                                   
                                                                    
theorem halfCurvature_round_error {f : ℝ → ℝ} {W x U : ℝ}
    (hx : x ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hf : ∀ y ∈ Set.Ioo 0 W, ContDiffAt ℝ 3 f y)
    (hthird : ∀ y ∈ Set.Ioo 0 W, |iteratedDeriv 3 f y| ≤ U) :
    (round x:ℝ) ∈ Set.Ioo 0 W ∧
      |iteratedDeriv 2 f (round x)/2-iteratedDeriv 2 f x/2| ≤ U/4 := by
  have hd : |(round x:ℝ)-x| ≤ 1/2 := by simpa only [abs_sub_comm] using abs_sub_round x
  have hm : (round x:ℝ) ∈ Set.Ioo 0 W := by
    have hh := abs_le.mp hd
    constructor <;> linarith [hx.1,hx.2,hh.1,hh.2]
  have hx0 : x ∈ Set.Ioo 0 W := by constructor <;> linarith [hx.1,hx.2]
  have hseg (y : ℝ) (hy : y ∈ Set.uIcc x (round x:ℝ)) : y ∈ Set.Ioo 0 W := by
    rcases Set.mem_uIcc.mp hy with hy | hy
    · exact ⟨hx0.1.trans_le hy.1,hy.2.trans_lt hm.2⟩
    · exact ⟨hm.1.trans_le hy.1,hy.2.trans_lt hx0.2⟩
  have hder (y : ℝ) (hy : y ∈ Set.uIcc x (round x:ℝ)) :
      HasDerivAt (fun z => iteratedDeriv 2 f z/2) (iteratedDeriv 3 f y/2) y :=
    (TaoTrudgianYang2025.hasDerivAt_iteratedDeriv_finite (by norm_num : 2 < 3)
      (hf y (hseg y hy))).div_const 2
  have he := (convex_uIcc x (round x:ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y hy => (hder y hy).hasDerivWithinAt)
    (C := U/2)
    (fun y hy => by
      simp only [Real.norm_eq_abs,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2)]
      exact div_le_div_of_nonneg_right (hthird y (hseg y hy)) (by norm_num))
    Set.left_mem_uIcc Set.right_mem_uIcc
  have hU : 0 ≤ U := (abs_nonneg _).trans (hthird x hx0)
  refine ⟨hm,?_⟩
  change |iteratedDeriv 2 f (round x)/2-iteratedDeriv 2 f x/2| ≤ U/2*|(round x:ℝ)-x| at he
  exact he.trans (by nlinarith [mul_le_mul_of_nonneg_left hd hU])


                                                                
theorem physicalModelPhase_halfCurvature_round_error
    {σ δ T M A W x : ℝ} {F : ℝ → ℝ} (hσ : 0 ≤ σ)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx : x ∈ Set.Ioo (1/2:ℝ) (W-1/2)) :
    let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
    (round x:ℝ) ∈ Set.Ioo 0 W ∧
      |iteratedDeriv 2 f (round x)/2-iteratedDeriv 2 f x/2| ≤
        T*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)/(4*M^3) := by
  let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
  have hc (y : ℝ) (hy : y ∈ Set.Ioo 0 W) : ContDiffAt ℝ 3 f y := by
    have hcf := TaoTrudgianYang2025.heathBrownPhysicalPhase_contDiffOn hF.1 hM hA hW T 1
    exact ((hcf y (Set.Ioo_subset_Icc_self hy)).contDiffAt
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hy) Set.Ioo_subset_Icc_self)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hthird (y : ℝ) (hy : y ∈ Set.Ioo 0 W) :
      |iteratedDeriv 3 f y| ≤ T/M^3*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ) := by
    have hyp := TaoTrudgianYang2025.heathBrownPhysicalPoint_mem_interior hM hA hW hy
    have he := TaoTrudgianYang2025.approximateModelPhase_iteratedDeriv_error hF hyp 2 le_rfl
    have hm := TaoTrudgianYang2025.iteratedDeriv_modelPhase_abs_le hσ hyp 2
    have htri := abs_add_le (iteratedDeriv 3 F ((A+y)/M)-iteratedDeriv 2 (Expdb.modelPhase σ) ((A+y)/M))
      (iteratedDeriv 2 (Expdb.modelPhase σ) ((A+y)/M))
    rw [sub_add_cancel] at htri
    have hu : |iteratedDeriv 3 F ((A+y)/M)| ≤ TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ := by
      linarith only [he,hm,htri]
    dsimp only [f]
    rw [TaoTrudgianYang2025.heathBrownPhysicalPhase_iteratedDeriv hF.1 hM hA hW hy,
      one_mul,abs_mul,abs_of_pos (by positivity : 0 < T/M^3)]
    exact mul_le_mul_of_nonneg_left hu (by positivity)
  have he := halfCurvature_round_error hx hc hthird
  refine ⟨he.1,he.2.trans_eq ?_⟩
  ring


                                                                     
                                                                  
theorem physicalModelPhase_exists_rounded_halfCurvature_center
    {σ δ T M A W l v q : ℝ} {F : ℝ → ℝ} (hσ : 0 ≤ σ)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hl : l ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hv : v ∈ Set.Ioo (1/2:ℝ) (W-1/2)) :
    let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
    q ∈ Set.uIcc (iteratedDeriv 2 f l/2) (iteratedDeriv 2 f v/2) →
    ∃ x ∈ Set.uIcc l v, iteratedDeriv 2 f x/2=q ∧
      (round x:ℝ) ∈ Set.Ioo 0 W ∧
      |iteratedDeriv 2 f (round x)/2-q| ≤
        T*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)/(4*M^3) := by
  let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
  change _ → _
  intro hq
  have hseg (y : ℝ) (hy : y ∈ Set.uIcc l v) : y ∈ Set.Ioo (1/2:ℝ) (W-1/2) := by
    rcases Set.mem_uIcc.mp hy with hy | hy
    · exact ⟨hl.1.trans_le hy.1,hy.2.trans_lt hv.2⟩
    · exact ⟨hv.1.trans_le hy.1,hy.2.trans_lt hl.2⟩
  have hc : ContinuousOn (fun y => iteratedDeriv 2 f y/2) (Set.uIcc l v) := by
    intro y hy
    have hy0 : y ∈ Set.Ioo 0 W := by
      have hh := hseg y hy
      constructor <;> linarith [hh.1,hh.2]
    have hcf := TaoTrudgianYang2025.heathBrownPhysicalPhase_contDiffOn hF.1 hM hA hW T 1
    have hf3 : ContDiffAt ℝ 3 f y :=
      ((hcf y (Set.Ioo_subset_Icc_self hy0)).contDiffAt
        (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hy0) Set.Ioo_subset_Icc_self)).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
    exact ((TaoTrudgianYang2025.hasDerivAt_iteratedDeriv_finite
      (by norm_num : 2 < 3) hf3).div_const 2).continuousAt.continuousWithinAt
  obtain ⟨x,hx,hfx⟩ := intermediate_value_uIcc hc hq
  have he := physicalModelPhase_halfCurvature_round_error hσ hF hT hM hA hW (hseg x hx)
  refine ⟨x,hx,hfx,he.1,?_⟩
  rw [← hfx]
  exact he.2


                                                                     
                                                                       
                                                
theorem physicalModelPhase_rounded_minorArcCoordinate_entry
    {σ δ T M A W x₀ x₁ e r v s u t : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx₀ : x₀ ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hx₁ : x₁ ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1) :
    let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
    let n := (round x₁:ℝ)-(round x₀:ℝ)
    let μ := iteratedDeriv 3 f (round x₀)/6
    iteratedDeriv 2 f x₀/2=e/r →
    iteratedDeriv 2 f x₁/2=(e*u+v*t)/(r*u+s*t) →
    |n-minorArcCoordinate μ r s (u/t)| ≤
      (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)/
        TaoTrudgianYang2025.modelPhaseThirdLower σ+
      (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*|n|^2/
        (2*TaoTrudgianYang2025.modelPhaseThirdLower σ*M) := by
  let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
  let a : ℝ := round x₀
  let b : ℝ := round x₁
  let μ := iteratedDeriv 3 f a/6
  let κ := TaoTrudgianYang2025.modelPhaseThirdLower σ
  let C₂ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ
  let δ₀ := iteratedDeriv 2 f a/2-e/r
  let δ₁ := iteratedDeriv 2 f b/2-(e*u+v*t)/(r*u+s*t)
  change _ → _ → _
  intro hbase hpoint
  have hF₂ := TaoTrudgianYang2025.approximateModelPhase_mono hF (by norm_num : 2 ≤ 3) le_rfl
  have hround₀ := physicalModelPhase_halfCurvature_round_error hσ.le hF₂ hT hM hA hW hx₀
  have hround₁ := physicalModelPhase_halfCurvature_round_error hσ.le hF₂ hT hM hA hW hx₁
  have hδ₀ : |δ₀| ≤ T*C₂/(4*M^3) := by simpa only [hbase] using hround₀.2
  have hδ₁ : |δ₁| ≤ T*C₂/(4*M^3) := by simpa only [hpoint] using hround₁.2
  have hκ : 0 < κ := TaoTrudgianYang2025.modelPhaseThirdLower_pos hσ
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans
    (TaoTrudgianYang2025.approximateModelPhase_iteratedDeriv_error hF
      (TaoTrudgianYang2025.heathBrownPhysicalPoint_mem_interior hM hA hW hround₀.1) 3 le_rfl)
  have hC₂ : 0 ≤ C₂ := add_nonneg
    (TaoTrudgianYang2025.modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hlo : κ ≤ iteratedDeriv 3 F ((A+a)/M) := by
    have hh := (TaoTrudgianYang2025.approximateModelPhase_thirdDeriv_bounds hσ hδ hF₂
      (TaoTrudgianYang2025.heathBrownPhysicalPoint_mem_interior hM hA hW hround₀.1)).1
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hh
  have hμlo : (T/M^3)*κ/6 ≤ μ := by
    dsimp only [μ,f]
    rw [TaoTrudgianYang2025.heathBrownPhysicalPhase_iteratedDeriv hF.1 hM hA hW hround₀.1,one_mul]
    gcongr
  have hμ : 0 < μ := lt_of_lt_of_le (by positivity) hμlo
  have hde : |δ₁-δ₀| ≤ T*C₂/(2*M^3) := by
    have hh := abs_add_le δ₁ (-δ₀)
    rw [abs_neg,← sub_eq_add_neg] at hh
    calc
      |δ₁-δ₀| ≤ T*C₂/(4*M^3)+T*C₂/(4*M^3) := hh.trans (add_le_add hδ₁ hδ₀)
      _ = T*C₂/(2*M^3) := by ring
  have hpert : |(δ₁-δ₀)/(3*μ)| ≤ C₂/κ := by
    rw [abs_div,abs_of_pos (mul_pos (by norm_num) hμ)]
    calc
      |δ₁-δ₀|/(3*μ) ≤ (T*C₂/(2*M^3))/(3*((T/M^3)*κ/6)) :=
        div_le_div₀ (by positivity) hde (by positivity)
          (mul_le_mul_of_nonneg_left hμlo (by norm_num))
      _ = C₂/κ := by field_simp; ring
  have he := physicalModelPhase_minorArcCoordinate_taylor_entry hσ hδ hF hT hM hA hW
    hround₀.1 hround₁.1 hr ht hq hdet
    (δ₀ := δ₀) (δ₁ := δ₁) (by dsimp [δ₀]; ring) (by dsimp [δ₁]; ring)
  have htri := abs_add_le ((b-a)-minorArcCoordinate μ r s (u/t)-(δ₁-δ₀)/(3*μ))
    ((δ₁-δ₀)/(3*μ))
  rw [sub_add_cancel] at htri
  apply htri.trans
  linarith only [he,hpert]

                                                                     
                                                                      
                                                                      
theorem firstDerivative_halfCurvature_remainder
    {f : ℝ → ℝ} {a b U : ℝ}
    (hf : ∀ y ∈ Set.uIcc a b, ContDiffAt ℝ 4 f y)
    (hfourth : ∀ y ∈ Set.uIcc a b, |iteratedDeriv 4 f y| ≤ U) :
    |iteratedDeriv 1 f b-iteratedDeriv 1 f a-
      (b-a)*(iteratedDeriv 2 f a/2+iteratedDeriv 2 f b/2)| ≤ 5*U*|b-a|^3/12 := by
  have hg (y : ℝ) (hy : y ∈ Set.uIcc a b) : ContDiffAt ℝ 3 (iteratedDeriv 1 f) y :=
    TaoTrudgianYang2025.contDiffAt_iteratedDeriv_finite (n := 3) (j := 1) (hf y hy)
  have hgg (y : ℝ) (hy : y ∈ Set.uIcc a b) :
      |iteratedDeriv 3 (iteratedDeriv 1 f) y| ≤ U := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hfourth y hy
  have he₁ := TaoTrudgianYang2025.abs_finiteTaylorPolynomial_remainder_le_finite 2 hg hgg
  have hpoly : TaoTrudgianYang2025.finiteTaylorPolynomial (iteratedDeriv 1 f) 2 a b =
      iteratedDeriv 1 f a+iteratedDeriv 2 f a*(b-a)+iteratedDeriv 3 f a*(b-a)^2/2 := by
    simp [TaoTrudgianYang2025.finiteTaylorPolynomial,taylor_within_apply,iteratedDeriv_succ]
    ring
  rw [hpoly] at he₁
  norm_num only [Nat.reduceAdd,Nat.factorial,Nat.cast_ofNat] at he₁
  have he₂ := halfCurvature_first_order_remainder hf hfourth
  have hid : iteratedDeriv 1 f b-iteratedDeriv 1 f a-
      (b-a)*(iteratedDeriv 2 f a/2+iteratedDeriv 2 f b/2) =
      (iteratedDeriv 1 f b-(iteratedDeriv 1 f a+iteratedDeriv 2 f a*(b-a)+
        iteratedDeriv 3 f a*(b-a)^2/2))-
      (b-a)*(iteratedDeriv 2 f b/2-iteratedDeriv 2 f a/2-
        3*(iteratedDeriv 3 f a/6)*(b-a)) := by ring
  rw [hid]
  have ht := abs_add_le
    (iteratedDeriv 1 f b-(iteratedDeriv 1 f a+iteratedDeriv 2 f a*(b-a)+
      iteratedDeriv 3 f a*(b-a)^2/2))
    (-((b-a)*(iteratedDeriv 2 f b/2-iteratedDeriv 2 f a/2-
      3*(iteratedDeriv 3 f a/6)*(b-a))))
  rw [abs_neg,abs_mul,← sub_eq_add_neg] at ht
  exact ht.trans ((add_le_add he₁ (mul_le_mul_of_nonneg_left he₂ (abs_nonneg _))).trans_eq (by ring))


                                                                 
                                                                  
theorem physicalModelPhase_firstDerivative_halfCurvature_remainder
    {σ δ T M A W a b : ℝ} {F : ℝ → ℝ} (hσ : 0 ≤ σ)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (ha : a ∈ Set.Ioo 0 W) (hb : b ∈ Set.Ioo 0 W) :
    let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
    |iteratedDeriv 1 f b-iteratedDeriv 1 f a-
      (b-a)*(iteratedDeriv 2 f a/2+iteratedDeriv 2 f b/2)| ≤
      5*T*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*|b-a|^3/(12*M^4) := by
  let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
  have hseg (y : ℝ) (hy : y ∈ Set.uIcc a b) : y ∈ Set.Ioo 0 W := by
    rcases Set.mem_uIcc.mp hy with hy | hy
    · exact ⟨ha.1.trans_le hy.1,hy.2.trans_lt hb.2⟩
    · exact ⟨hb.1.trans_le hy.1,hy.2.trans_lt ha.2⟩
  have hc (y : ℝ) (hy : y ∈ Set.uIcc a b) : ContDiffAt ℝ 4 f y := by
    have hcf := TaoTrudgianYang2025.heathBrownPhysicalPhase_contDiffOn hF.1 hM hA hW T 1
    exact ((hcf y (Set.Ioo_subset_Icc_self (hseg y hy))).contDiffAt
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds (hseg y hy)) Set.Ioo_subset_Icc_self)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)
  have hf4 (y : ℝ) (hy : y ∈ Set.uIcc a b) :
      |iteratedDeriv 4 f y| ≤ T/M^4*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ) := by
    have hyp := TaoTrudgianYang2025.heathBrownPhysicalPoint_mem_interior hM hA hW (hseg y hy)
    have he := TaoTrudgianYang2025.approximateModelPhase_iteratedDeriv_error hF hyp 3 le_rfl
    have hm := TaoTrudgianYang2025.iteratedDeriv_modelPhase_abs_le hσ hyp 3
    have htri := abs_add_le (iteratedDeriv 4 F ((A+y)/M)-iteratedDeriv 3 (Expdb.modelPhase σ) ((A+y)/M))
      (iteratedDeriv 3 (Expdb.modelPhase σ) ((A+y)/M))
    rw [sub_add_cancel] at htri
    have hu : |iteratedDeriv 4 F ((A+y)/M)| ≤ TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ := by
      linarith only [he,hm,htri]
    dsimp only [f]
    rw [TaoTrudgianYang2025.heathBrownPhysicalPhase_iteratedDeriv hF.1 hM hA hW (hseg y hy),
      one_mul,abs_mul,abs_of_pos (by positivity : 0 < T/M^4)]
    exact mul_le_mul_of_nonneg_left hu (by positivity)
  exact (firstDerivative_halfCurvature_remainder hc hf4).trans_eq (by ring)


                                                                 
                                                             
theorem physicalModelPhase_rounded_firstDerivative_residual
    {σ δ T M A W x₀ x₁ e r v s u t : ℝ} {F : ℝ → ℝ}
    (hσ : 0 ≤ σ) (hF : Expdb.IsApproximateModelPhaseFunction F σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx₀ : x₀ ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hx₁ : x₁ ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hr : r ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1) :
    let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
    let a : ℝ := round x₀
    let b : ℝ := round x₁
    let n := b-a
    let q := r*u+s*t
    iteratedDeriv 2 f x₀/2=e/r →
    iteratedDeriv 2 f x₁/2=(e*u+v*t)/q →
    |q*(iteratedDeriv 1 f b-iteratedDeriv 1 f a-2*e*n/r-n*t/(r*q))| ≤
      |q| * (T*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)*|n|/(2*M^3)+
        5*T*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*|n|^3/(12*M^4)) := by
  let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
  let a : ℝ := round x₀
  let b : ℝ := round x₁
  let q := r*u+s*t
  change _ → _ → _
  intro hbase hpoint
  have hF₂ := TaoTrudgianYang2025.approximateModelPhase_mono hF (by norm_num : 2 ≤ 3) le_rfl
  have hround₀ := physicalModelPhase_halfCurvature_round_error hσ hF₂ hT hM hA hW hx₀
  have hround₁ := physicalModelPhase_halfCurvature_round_error hσ hF₂ hT hM hA hW hx₁
  have herr₀ : |iteratedDeriv 2 f a/2-e/r| ≤
      T*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)/(4*M^3) := by
    simpa only [hbase] using hround₀.2
  have herr₁ : |iteratedDeriv 2 f b/2-(e*u+v*t)/q| ≤
      T*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)/(4*M^3) := by
    simpa only [hpoint] using hround₁.2
  have hrat : (e*u+v*t)/q-e/r = t/(r*q) := by
    apply (div_sub_div _ _ hq hr).trans
    rw [mul_comm q r]
    congr 1
    linear_combination t*hdet
  have hcurv : |iteratedDeriv 2 f a/2+iteratedDeriv 2 f b/2-(2*e/r+t/(r*q))| ≤
      T*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)/(2*M^3) := by
    have hid : iteratedDeriv 2 f a/2+iteratedDeriv 2 f b/2-(2*e/r+t/(r*q)) =
        (iteratedDeriv 2 f a/2-e/r)+(iteratedDeriv 2 f b/2-(e*u+v*t)/q) := by
      linear_combination hrat
    rw [hid]
    apply (abs_add_le _ _).trans
    exact (add_le_add herr₀ herr₁).trans_eq (by ring)
  have he := physicalModelPhase_firstDerivative_halfCurvature_remainder hσ hF hT hM hA hW
    hround₀.1 hround₁.1
  have hid : iteratedDeriv 1 f b-iteratedDeriv 1 f a-2*e*(b-a)/r-(b-a)*t/(r*q) =
      (iteratedDeriv 1 f b-iteratedDeriv 1 f a-
        (b-a)*(iteratedDeriv 2 f a/2+iteratedDeriv 2 f b/2))+
      (b-a)*(iteratedDeriv 2 f a/2+iteratedDeriv 2 f b/2-(2*e/r+t/(r*q))) := by ring
  change |q*(iteratedDeriv 1 f b-iteratedDeriv 1 f a-2*e*(b-a)/r-(b-a)*t/(r*q))| ≤ _
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg q)
  rw [hid]
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  exact (add_le_add he (mul_le_mul_of_nonneg_left hcurv (abs_nonneg _))).trans_eq (by ring)


                                                                   
                                                                      
theorem farey_firstDerivative_residual_identity
    {e r v s u t n c θ d₀ d₁ : ℝ}
    (hr : r ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1)
    (hd₀ : r*d₀=c+θ) :
    let q := r*u+s*t
    let γ := q*(d₁-d₀-2*e*n/r-n*t/(r*q))
    q*d₁ = c*u+2*n*(e*u+v*t)+(c*s-n)*t/r+θ*q/r+γ := by
  dsimp only
  have hfrac : (r*u+s*t)*(n*t/(r*(r*u+s*t)))=n*t/r := by field_simp
  rw [mul_sub,mul_sub,mul_sub,hfrac]
  field_simp
  linear_combination (r*u+s*t)*hd₀-2*n*t*hdet


                                                                 
                                                
noncomputable def roundedMinorArcLinearForm (f : ℝ → ℝ) (x₀ e r s u t : ℝ) : ℝ :=
  let a : ℝ := round x₀
  let d₀ := iteratedDeriv 1 f a
  let μ := iteratedDeriv 3 f a/6
  let δ₀ := iteratedDeriv 2 f a/2-e/r
  (r*d₀-round (r*d₀))*u+(d₀*s+2*δ₀/(3*μ*r))*t-t*rationalBranch μ r s (u/t)

                                                                
theorem firstDerivative_linearization_identity
    {f : ℝ → ℝ} {x₀ x₁ e r v s u t : ℝ}
    (hr : r ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1) :
    let a : ℝ := round x₀
    let b : ℝ := round x₁
    let n := b-a
    let μ := iteratedDeriv 3 f a/6
    let δ₀ := iteratedDeriv 2 f a/2-e/r
    let q := r*u+s*t
    let γ := q*(iteratedDeriv 1 f b-iteratedDeriv 1 f a-2*e*n/r-n*t/(r*q))
    q*iteratedDeriv 1 f b-
      (round (r*iteratedDeriv 1 f a)*u+2*n*(e*u+v*t))-
      roundedMinorArcLinearForm f x₀ e r s u t =
      γ-n*t/r-t/r*(2*δ₀/(3*μ)-minorArcCoordinate μ r s (u/t)) := by
  let a : ℝ := round x₀
  let b : ℝ := round x₁
  let μ := iteratedDeriv 3 f a/6
  have hb : rationalBranch μ r s (u/t)=minorArcCoordinate μ r s (u/t)/r := by
    dsimp [rationalBranch,minorArcCoordinate]
    rw [div_div]
    congr 1
    ring
  have hh := farey_firstDerivative_residual_identity hr hq hdet
    (n := b-a) (c := round (r*iteratedDeriv 1 f a))
    (θ := r*iteratedDeriv 1 f a-round (r*iteratedDeriv 1 f a))
    (d₀ := iteratedDeriv 1 f a) (d₁ := iteratedDeriv 1 f b) (by ring)
  dsimp only at hh ⊢
  rw [hh]
  dsimp only [roundedMinorArcLinearForm]
  rw [hb]
  dsimp only [a,b,μ]
  field_simp [hr]
  ring


                                                                 
                                                                       
                                                      
theorem physicalModelPhase_rounded_cubicCoefficient_pos
    {σ δ T M A W x : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx : x ∈ Set.Ioo (1/2:ℝ) (W-1/2)) :
    0 < iteratedDeriv 3 (TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1) (round x)/6 := by
  have hr := (physicalModelPhase_halfCurvature_round_error hσ.le hF hT hM hA hW hx).1
  have hlo : TaoTrudgianYang2025.modelPhaseThirdLower σ ≤
      iteratedDeriv 3 F ((A+(round x:ℝ))/M) := by
    have hh := (TaoTrudgianYang2025.approximateModelPhase_thirdDeriv_bounds hσ hδ hF
      (TaoTrudgianYang2025.heathBrownPhysicalPoint_mem_interior hM hA hW hr)).1
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hh
  have hp := lt_of_lt_of_le (TaoTrudgianYang2025.modelPhaseThirdLower_pos hσ) hlo
  rw [TaoTrudgianYang2025.heathBrownPhysicalPhase_iteratedDeriv hF.1 hM hA hW hr,one_mul]
  positivity


                                                                       
                                                                      
                                                                    
theorem sum_nonunit_inverse_square_le (N : ℕ) :
    (∑ d ∈ Finset.Icc 2 N, 1/(d:ℝ)^2) ≤ 3/4 := by
  by_cases hN : 2 ≤ N
  · have hI : Finset.Icc 2 N = insert 2 (Finset.Icc 3 N) := by
      ext d
      simp only [Finset.mem_Icc,Finset.mem_insert]
      omega
    rw [hI,Finset.sum_insert (by simp)]
    let f : ℕ → ℝ := fun d => if 2 < d then 1/(d:ℝ)^2 else 0
    have hs : Summable f := by
      have h := (Real.summable_one_div_nat_pow.mpr
        (by norm_num : 1 < (2:ℕ))).indicator {d | 2 < d}
      apply h.congr
      intro d
      by_cases hd : 2 < d <;> simp [f,hd]
    have hsum : (∑ d ∈ Finset.Icc 3 N, 1/(d:ℝ)^2) ≤ ∑' d, f d := by
      calc
        _ = ∑ d ∈ Finset.Icc 3 N, f d := by
          apply Finset.sum_congr rfl
          intro d hd
          have hd2 : 2 < d := by have h := (Finset.mem_Icc.mp hd).1; omega
          simp only [f,ite_eq_left hd2]
        _ ≤ _ := hs.sum_le_tsum _ (fun _ _ => by dsimp [f]; split <;> positivity)
    have ht := tsum_nat_inverse_square_tail_le (R := 2) (by norm_num)
    change (∑' d, f d) ≤ 1/(2:ℝ) at ht
    calc
      _ ≤ 1/(2:ℝ)^2+1/2 := add_le_add le_rfl (hsum.trans ht)
      _ = 3/4 := by norm_num
  · have hI : Finset.Icc 2 N = ∅ := Finset.Icc_eq_empty (by omega)
    simp only [hI,Finset.sum_empty]
    norm_num

                                                                     
theorem affine_positive_between {r s l w y : ℝ}
    (hy : y ∈ Set.Icc l w) (hl : 0 < r*l+s) (hw : 0 < r*w+s) : 0 < r*y+s := by
  rcases le_total 0 r with hr | hr
  · have hh := mul_nonneg hr (sub_nonneg.mpr hy.1)
    nlinarith only [hh,hl]
  · have hh := mul_nonpos_of_nonpos_of_nonneg hr (sub_nonneg.mpr hy.2)
    nlinarith only [hh,hw]


                                                                   
                                                               
theorem fareySector_curvature_targets {K : ℕ} {l w : ℝ} {e r v s : ℤ}
    (hl : 0 < l) (hlw : l ≤ w)
    (hdenl : 0 < (r:ℝ)*l+s) (hdenw : 0 < (r:ℝ)*w+s)
    {p : ℤ × ℤ} (hp : p ∈ TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w) :
    0 < (r:ℝ)*p.1+s*p.2 ∧
      ((e:ℝ)*p.1+v*p.2)/((r:ℝ)*p.1+s*p.2) ∈
        Set.uIcc (((e:ℝ)*l+v)/((r:ℝ)*l+s)) (((e:ℝ)*w+v)/((r:ℝ)*w+s)) := by
  have hm := (TaoTrudgianYang2025.HuxleyLinearForm.mem_fareySector_iff hl (hl.le.trans hlw)).mp hp
  have ht : (0:ℝ) < p.2 := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℤ) < 1) hm.1)
  have hx : (p.1:ℝ)/(p.2:ℝ) ∈ Set.Icc l w :=
    ⟨(le_div_iff₀ ht).mpr hm.2.2.2.1,(div_le_iff₀ ht).mpr hm.2.2.2.2⟩
  have hden := affine_positive_between hx hdenl hdenw
  have hq : 0 < (r:ℝ)*p.1+s*p.2 := by
    have hh := mul_pos hden ht
    have hid : ((r:ℝ)*((p.1:ℝ)/(p.2:ℝ))+s)*(p.2:ℝ)=(r:ℝ)*p.1+s*p.2 := by
      field_simp
    rwa [hid] at hh
  refine ⟨hq,?_⟩
  have hh := affine_ratio_mem_endpoint_interval (r₁ := (e:ℝ)) (s₁ := (v:ℝ)) hx hdenl hdenw hden
  have hid : ((e:ℝ)*((p.1:ℝ)/(p.2:ℝ))+v)/((r:ℝ)*((p.1:ℝ)/(p.2:ℝ))+s) =
      ((e:ℝ)*p.1+v*p.2)/((r:ℝ)*p.1+s*p.2) := by
    field_simp
  rwa [hid] at hh


                                                                
theorem rounded_displacement_bound (x y : ℝ) :
    |(round x:ℝ)-(round y:ℝ)| ≤ |x-y|+1 := by
  have hx := abs_sub_round x
  have hy := abs_sub_round y
  have ht := abs_add_le ((round x:ℝ)-x) ((x-y)+(y-(round y:ℝ)))
  have hs := abs_add_le (x-y) (y-(round y:ℝ))
  rw [abs_sub_comm (round x:ℝ) x] at ht
  have hid : (round x:ℝ)-x+((x-y)+(y-(round y:ℝ)))=(round x:ℝ)-(round y:ℝ) := by ring
  rw [hid] at ht
  linarith only [ht,hs,hx,hy]


                                                                     
                                                                       
                                                                         
theorem fareySector_denominator_bound {K : ℕ} {l w : ℝ} {r s : ℤ}
    (hl : 0 < l) (hlw : l ≤ w)
    (hdenl : 0 < (r:ℝ)*l+s) (hdenw : 0 < (r:ℝ)*w+s)
    {p : ℤ × ℤ} (hp : p ∈ TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w) :
    |(r:ℝ)*p.1+s*p.2| ≤ (K:ℝ)*max ((r:ℝ)*l+s) ((r:ℝ)*w+s) := by
  have hm := (TaoTrudgianYang2025.HuxleyLinearForm.mem_fareySector_iff hl (hl.le.trans hlw)).mp hp
  have ht : (0:ℝ) < p.2 := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℤ) < 1) hm.1)
  have htK : (p.2:ℝ) ≤ K := by exact_mod_cast hm.2.1
  have hx : (p.1:ℝ)/(p.2:ℝ) ∈ Set.Icc l w :=
    ⟨(le_div_iff₀ ht).mpr hm.2.2.2.1,(div_le_iff₀ ht).mpr hm.2.2.2.2⟩
  have hpos := (fareySector_curvature_targets (e := 0) (v := 0) hl hlw hdenl hdenw hp).1
  have hmax : (r:ℝ)*((p.1:ℝ)/(p.2:ℝ))+s ≤ max ((r:ℝ)*l+s) ((r:ℝ)*w+s) := by
    rcases le_total 0 (r:ℝ) with hr | hr
    · exact (add_le_add (mul_le_mul_of_nonneg_left hx.2 hr) le_rfl).trans (le_max_right _ _)
    · exact (add_le_add (mul_le_mul_of_nonpos_left hx.1 hr) le_rfl).trans (le_max_left _ _)
  rw [abs_of_pos hpos]
  calc
    (r:ℝ)*p.1+s*p.2 = (p.2:ℝ)*((r:ℝ)*((p.1:ℝ)/(p.2:ℝ))+s) := by field_simp
    _ ≤ (K:ℝ)*max ((r:ℝ)*l+s) ((r:ℝ)*w+s) :=
      mul_le_mul htK hmax (le_of_lt (affine_positive_between hx hdenl hdenw))
        (by exact_mod_cast Nat.zero_le K)


                                                              
                                                                       
                                                                       
theorem coprime_rectangle_card_lower (M N : ℕ) :
    (M:ℝ)*N/4 ≤
      ((((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 N)).filter
        (fun p => Nat.Coprime p.1 p.2)).card:ℝ) := by
  classical
  let A := (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 N)
  let G := A.filter (fun p => Nat.Coprime p.1 p.2)
  let F := A.filter (fun p => ¬Nat.Coprime p.1 p.2)
  let U : ℕ → Finset (ℕ × ℕ) := fun d =>
    ((Finset.Icc 1 (M/d)) ×ˢ (Finset.Icc 1 (N/d))).image
      (fun p => (d*p.1,d*p.2))
  have hcover : F ⊆ (Finset.Icc 2 M).biUnion U := by
    intro p hp
    obtain ⟨hpA,hbad⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp₁,hp₂⟩ := Finset.mem_product.mp hpA
    obtain ⟨hp₁pos,hp₁M⟩ := Finset.mem_Icc.mp hp₁
    obtain ⟨hp₂pos,hp₂N⟩ := Finset.mem_Icc.mp hp₂
    let d := Nat.gcd p.1 p.2
    have hdpos : 0 < d := Nat.gcd_pos_of_pos_left p.2 hp₁pos
    have hdne : d ≠ 1 := hbad
    have hdM : d ≤ M := (Nat.gcd_le_left p.2 hp₁pos).trans hp₁M
    have hd₁ : d ∣ p.1 := Nat.gcd_dvd_left _ _
    have hd₂ : d ∣ p.2 := Nat.gcd_dvd_right _ _
    apply Finset.mem_biUnion.mpr
    refine ⟨d,Finset.mem_Icc.mpr ⟨by omega,hdM⟩,?_⟩
    apply Finset.mem_image.mpr
    refine ⟨(p.1/d,p.2/d),Finset.mem_product.mpr ⟨?_,?_⟩,?_⟩
    · exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hp₁pos hd₁) hdpos,
        Nat.div_le_div_right hp₁M⟩
    · exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hp₂pos hd₂) hdpos,
        Nat.div_le_div_right hp₂N⟩
    · exact Prod.ext (Nat.mul_div_cancel' hd₁) (Nat.mul_div_cancel' hd₂)
  have hU (d : ℕ) : (U d).card ≤ (M/d)*(N/d) := by
    have hh := Finset.card_image_le (s := (Finset.Icc 1 (M/d)) ×ˢ (Finset.Icc 1 (N/d)))
      (f := fun p : ℕ × ℕ => (d*p.1,d*p.2))
    simpa only [U,Finset.card_product,Nat.card_Icc,Nat.add_sub_cancel] using hh
  have hF : F.card ≤ ∑ d ∈ Finset.Icc 2 M, (M/d)*(N/d) := by
    calc
      _ ≤ _ := Finset.card_le_card hcover
      _ ≤ _ := Finset.card_biUnion_le
      _ ≤ _ := Finset.sum_le_sum (fun d _ => hU d)
  have hFR : (F.card:ℝ) ≤ (3/4:ℝ)*(M:ℝ)*N := by
    calc
      _ ≤ ∑ d ∈ Finset.Icc 2 M, (((M/d)*(N/d):ℕ):ℝ) := by exact_mod_cast hF
      _ ≤ ∑ d ∈ Finset.Icc 2 M, ((M:ℝ)/(d:ℝ))*((N:ℝ)/(d:ℝ)) := by
        apply Finset.sum_le_sum
        intro d _hd
        rw [Nat.cast_mul]
        exact mul_le_mul Nat.cast_div_le Nat.cast_div_le (Nat.cast_nonneg _) (by positivity)
      _ = (M:ℝ)*N * ∑ d ∈ Finset.Icc 2 M, 1/(d:ℝ)^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _hd
        ring
      _ ≤ (M:ℝ)*N*(3/4) := mul_le_mul_of_nonneg_left
        (sum_nonunit_inverse_square_le M) (by positivity)
      _ = _ := by ring
  have htotal : G.card+F.card=M*N := by
    have hh := Finset.card_filter_add_card_filter_not (s := A) (fun p => Nat.Coprime p.1 p.2)
    simpa only [A,Finset.card_product,Nat.card_Icc,Nat.add_sub_cancel] using hh
  have htotalR : (G.card:ℝ)+(F.card:ℝ)=(M:ℝ)*N := by exact_mod_cast htotal
  change (M:ℝ)*N/4 ≤ (G.card:ℝ)
  linarith


                                                               
                                                                         
theorem isCoprime_unimodular_image {a b c d m n : ℤ}
    (hdet : a*d-b*c=1) (hmn : IsCoprime m n) : IsCoprime (a*m+b*n) (c*m+d*n) := by
  obtain ⟨x,y,hxy⟩ := hmn
  refine ⟨x*d-y*c,y*a-x*b,?_⟩
  linear_combination hxy+(x*m+y*n)*hdet


                                                                
theorem unimodular_image_injective {a b c d : ℤ} (hdet : a*d-b*c=1) :
    Function.Injective (fun p : ℤ × ℤ => (a*p.1+b*p.2,c*p.1+d*p.2)) := by
  intro p q hpq
  have h₁ := congrArg Prod.fst hpq
  have h₂ := congrArg Prod.snd hpq
  apply Prod.ext
  · dsimp only at h₁ h₂
    linear_combination d*h₁-b*h₂-(p.1-q.1)*hdet
  · dsimp only at h₁ h₂
    linear_combination a*h₂-c*h₁-(p.2-q.2)*hdet


                                                               
                                                                      
                                                                           
theorem unimodular_rectangle_fareySector_interior_card_lower
    {M N K : ℕ} {a b c d : ℤ} {l w : ℝ}
    (hdet : a*d-b*c=1) (hc : 0 < c) (hd : 0 < d)
    (hcap : c*(M:ℤ)+d*(N:ℤ) ≤ K) (hl : 0 < l) (hlw : l ≤ w)
    (ha : l*(c:ℝ) ≤ a ∧ (a:ℝ) ≤ w*c)
    (hb : l*(d:ℝ) ≤ b ∧ (b:ℝ) ≤ w*d) :
    (M:ℝ)*N/4 ≤ ((TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).filter
      (fun p => b*p.2 < d*p.1 ∧ c*p.1 < a*p.2)).card := by
  classical
  let S := ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 N)).filter (fun p => Nat.Coprime p.1 p.2)
  let f : ℕ × ℕ → ℤ × ℤ := fun p => (a*p.1+b*p.2,c*p.1+d*p.2)
  have hfi : Function.Injective f := by
    intro p q hpq
    have hh : ((p.1:ℤ),(p.2:ℤ))=((q.1:ℤ),(q.2:ℤ)) := unimodular_image_injective hdet hpq
    apply Prod.ext
    · have h₁ : (p.1:ℤ)=q.1 := congrArg Prod.fst hh
      exact_mod_cast h₁
    · have h₂ : (p.2:ℤ)=q.2 := congrArg Prod.snd hh
      exact_mod_cast h₂
  have hsub : S.image f ⊆ (TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).filter
      (fun p => b*p.2 < d*p.1 ∧ c*p.1 < a*p.2) := by
    intro y hy
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hpbox,hcop⟩ := Finset.mem_filter.mp hp
    obtain ⟨hm,hn⟩ := Finset.mem_product.mp hpbox
    obtain ⟨hmpos,hmM⟩ := Finset.mem_Icc.mp hm
    obtain ⟨hnpos,hnN⟩ := Finset.mem_Icc.mp hn
    have hmI : (0:ℤ) < p.1 := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℕ) < 1) hmpos)
    have hnI : (0:ℤ) < p.2 := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℕ) < 1) hnpos)
    have hden : 0 < c*(p.1:ℤ)+d*(p.2:ℤ) := add_pos (mul_pos hc hmI) (mul_pos hd hnI)
    apply Finset.mem_filter.mpr
    refine ⟨?_,?_⟩
    swap
    · dsimp [f]
      constructor
      · nlinarith only [mul_pos hmI (show 0 < a*d-b*c by omega)]
      · nlinarith only [mul_pos hnI (show 0 < a*d-b*c by omega)]
    apply (TaoTrudgianYang2025.HuxleyLinearForm.mem_fareySector_iff hl (hl.le.trans hlw)).mpr
    refine ⟨by dsimp [f]; omega,?_,isCoprime_unimodular_image hdet hcop.isCoprime,?_,?_⟩
    · exact (add_le_add (mul_le_mul_of_nonneg_left (by exact_mod_cast hmM) hc.le)
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hnN) hd.le)).trans hcap
    · have h₁ := mul_le_mul_of_nonneg_right ha.1 (Nat.cast_nonneg p.1 : (0:ℝ) ≤ p.1)
      have h₂ := mul_le_mul_of_nonneg_right hb.1 (Nat.cast_nonneg p.2 : (0:ℝ) ≤ p.2)
      dsimp [f]
      push_cast
      nlinarith only [h₁,h₂]
    · have h₁ := mul_le_mul_of_nonneg_right ha.2 (Nat.cast_nonneg p.1 : (0:ℝ) ≤ p.1)
      have h₂ := mul_le_mul_of_nonneg_right hb.2 (Nat.cast_nonneg p.2 : (0:ℝ) ≤ p.2)
      dsimp [f]
      push_cast
      nlinarith only [h₁,h₂]
  have hcard : S.card ≤ ((TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).filter
      (fun p => b*p.2 < d*p.1 ∧ c*p.1 < a*p.2)).card := by
    rw [← Finset.card_image_of_injective S hfi]
    exact Finset.card_le_card hsub
  exact (coprime_rectangle_card_lower M N).trans (by exact_mod_cast hcard)


theorem unimodular_cone_fareySector_interior_card_lower
    {K : ℕ} {a b c d : ℤ} {l w : ℝ}
    (hdet : a*d-b*c=1) (hc : 0 < c) (hd : 0 < d)
    (hcK : 4*c ≤ (K:ℤ)) (hdK : 4*d ≤ (K:ℤ))
    (hl : 0 < l) (hlw : l ≤ w)
    (ha : l*(c:ℝ) ≤ a ∧ (a:ℝ) ≤ w*c)
    (hb : l*(d:ℝ) ≤ b ∧ (b:ℝ) ≤ w*d) :
    (K:ℝ)^2/(64*(c:ℝ)*d) ≤ ((TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).filter
      (fun p => b*p.2 < d*p.1 ∧ c*p.1 < a*p.2)).card := by
  classical
  let M := ⌊(K:ℝ)/(2*(c:ℝ))⌋₊
  let N := ⌊(K:ℝ)/(2*(d:ℝ))⌋₊
  have hcR : (0:ℝ) < c := by exact_mod_cast hc
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hcx : (2:ℝ) ≤ (K:ℝ)/(2*(c:ℝ)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hh : 4*(c:ℝ) ≤ K := by exact_mod_cast hcK
    linarith only [hh]
  have hdx : (2:ℝ) ≤ (K:ℝ)/(2*(d:ℝ)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hh : 4*(d:ℝ) ≤ K := by exact_mod_cast hdK
    linarith only [hh]
  have hMhi : (M:ℝ) ≤ (K:ℝ)/(2*(c:ℝ)) := Nat.floor_le (by positivity)
  have hNhi : (N:ℝ) ≤ (K:ℝ)/(2*(d:ℝ)) := Nat.floor_le (by positivity)
  have hMlo : (K:ℝ)/(4*(c:ℝ)) ≤ M := by
    have hh := Nat.lt_floor_add_one ((K:ℝ)/(2*(c:ℝ)))
    change (K:ℝ)/(2*(c:ℝ)) < (M:ℝ)+1 at hh
    rw [show (K:ℝ)/(4*(c:ℝ))=((K:ℝ)/(2*(c:ℝ)))/2 by ring]
    linarith only [hh,hcx]
  have hNlo : (K:ℝ)/(4*(d:ℝ)) ≤ N := by
    have hh := Nat.lt_floor_add_one ((K:ℝ)/(2*(d:ℝ)))
    change (K:ℝ)/(2*(d:ℝ)) < (N:ℝ)+1 at hh
    rw [show (K:ℝ)/(4*(d:ℝ))=((K:ℝ)/(2*(d:ℝ)))/2 by ring]
    linarith only [hh,hdx]
  have hcapR : (c:ℝ)*M+(d:ℝ)*N ≤ K := by
    calc
      _ ≤ (c:ℝ)*((K:ℝ)/(2*(c:ℝ)))+(d:ℝ)*((K:ℝ)/(2*(d:ℝ))) := by gcongr
      _ = _ := by field_simp; ring
  have hcap : c*(M:ℤ)+d*(N:ℤ) ≤ (K:ℤ) := by exact_mod_cast hcapR
  have he := unimodular_rectangle_fareySector_interior_card_lower hdet hc hd hcap hl hlw ha hb
  apply le_trans _ he
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul hMlo hNlo (by positivity) (Nat.cast_nonneg M)) (by norm_num : (0:ℝ) ≤ 4)
  convert hh using 1
  ring


theorem rational_interval_determinant_split {a b c d : ℤ}
    (hc : 0 < c) (hd : 0 < d) (ha : IsCoprime a c) (hb : IsCoprime b d)
    (hdet : 1 < a*d-b*c) :
    ∃ m n : ℤ, 0 < n ∧ n ≤ max c d ∧ IsCoprime m n ∧
      0 < a*n-m*c ∧ a*n-m*c < a*d-b*c ∧
      0 < m*d-b*n ∧ m*d-b*n < a*d-b*c := by
  rcases le_total d c with hdc | hcd
  · obtain ⟨m,n,hn,hnc,hcop,hunit,hclose⟩ :=
      TaoTrudgianYang2025.HuxleyLinearForm.exists_left_neighbor hc ha
    have hweak : b*n ≤ m*d := hclose b d (by omega) hdc (by nlinarith only [hdet])
    have hid : n*(a*d-b*c)-d=c*(m*d-b*n) := by
      linear_combination d*hunit
    have hstrict : 0 < m*d-b*n := by
      by_contra hbad
      have he : m*d=b*n := by omega
      have hdvd : d ∣ n := hb.symm.dvd_of_dvd_mul_left
        (show d ∣ b*n from he ▸ dvd_mul_left d m)
      have hdn : d ≤ n := Int.le_of_dvd (by omega) hdvd
      have hh := mul_le_mul_of_nonneg_left hdn (show 0 ≤ a*d-b*c by omega)
      rw [he,sub_self,mul_zero] at hid
      have hh' := mul_lt_mul_of_pos_right hdet hd
      nlinarith only [hid,hh,hh']
    have hless : m*d-b*n < a*d-b*c := by
      have hh := mul_le_mul_of_nonneg_right hnc (show 0 ≤ a*d-b*c by omega)
      nlinarith only [hid,hh,hd,hc]
    exact ⟨m,n,by omega,hnc.trans (le_max_left _ _),hcop,
      by nlinarith only [hunit],by nlinarith only [hunit,hdet],hstrict,hless⟩
  · obtain ⟨m,n,hn,hnd,hcop,hunit,hclose⟩ :=
      TaoTrudgianYang2025.HuxleyLinearForm.exists_right_neighbor hd hb
    have hweak : m*c ≤ a*n := hclose a c (by omega) hcd (by nlinarith only [hdet])
    have hid : n*(a*d-b*c)-c=d*(a*n-m*c) := by
      linear_combination -c*hunit
    have hstrict : 0 < a*n-m*c := by
      by_contra hbad
      have he : a*n=m*c := by omega
      have hcvd : c ∣ n := ha.symm.dvd_of_dvd_mul_left
        (show c ∣ a*n from he ▸ dvd_mul_left c m)
      have hcn : c ≤ n := Int.le_of_dvd (by omega) hcvd
      have hh := mul_le_mul_of_nonneg_left hcn (show 0 ≤ a*d-b*c by omega)
      rw [he,sub_self,mul_zero] at hid
      have hh' := mul_lt_mul_of_pos_right hdet hc
      nlinarith only [hid,hh,hh']
    have hless : a*n-m*c < a*d-b*c := by
      have hh := mul_le_mul_of_nonneg_right hnd (show 0 ≤ a*d-b*c by omega)
      nlinarith only [hid,hh,hd,hc]
    exact ⟨m,n,by omega,hnd.trans (le_max_right _ _),hcop,hstrict,hless,
      by nlinarith only [hunit],by nlinarith only [hunit,hdet]⟩


                                                                          
theorem interval_filter_split_card {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) :
    (S.filter (fun p => x < f p ∧ f p < y)).card +
      (S.filter (fun p => y < f p ∧ f p < z)).card ≤
      (S.filter (fun p => x < f p ∧ f p < z)).card := by
  classical
  let A := S.filter (fun p => x < f p ∧ f p < y)
  let B := S.filter (fun p => y < f p ∧ f p < z)
  have hd : Disjoint A B := Finset.disjoint_left.mpr (by
    intro p hp hq
    exact (Finset.mem_filter.mp hp).2.2.not_gt (Finset.mem_filter.mp hq).2.1)
  have hs : A ∪ B ⊆ S.filter (fun p => x < f p ∧ f p < z) := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨hp,hlo,hhi⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨hp,hlo,hhi.trans_le hyz⟩
    · obtain ⟨hp,hlo,hhi⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨hp,hxy.trans_lt hlo,hhi⟩
  rw [← Finset.card_union_of_disjoint hd]
  exact Finset.card_le_card hs


theorem rational_interior_filter_eq {K : ℕ} {a b c d : ℤ} {l w : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hl : 0 < l) (hlw : l ≤ w) :
    (TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).filter
        (fun p => b*p.2 < d*p.1 ∧ c*p.1 < a*p.2) =
      (TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).filter
        (fun p => (b:ℝ)/d < (p.1:ℝ)/p.2 ∧ (p.1:ℝ)/p.2 < (a:ℝ)/c) := by
  classical
  apply Finset.filter_congr
  intro p hp
  have htI : 0 < p.2 := by
    have hh := ((TaoTrudgianYang2025.HuxleyLinearForm.mem_fareySector_iff hl (hl.le.trans hlw)).mp hp).1
    omega
  have ht : (0:ℝ) < p.2 := by exact_mod_cast htI
  have hcR : (0:ℝ) < c := by exact_mod_cast hc
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  rw [div_lt_div_iff₀ hdR ht,div_lt_div_iff₀ ht hcR]
  constructor
  · rintro ⟨h₁,h₂⟩
    constructor <;> exact_mod_cast (by nlinarith only [h₁,h₂] : _)
  · rintro ⟨h₁,h₂⟩
    have h₁I : b*p.2 < p.1*d := by exact_mod_cast h₁
    have h₂I : p.1*c < a*p.2 := by exact_mod_cast h₂
    constructor <;> nlinarith only [h₁I,h₂I]


                                                                 
                                                                    
                                                                       
                                                                 
theorem rational_interval_fareySector_interior_card_lower
    {K : ℕ} {a b c d : ℤ} {l w : ℝ}
    (hc : 0 < c) (hd : 0 < d) (ha : IsCoprime a c) (hb : IsCoprime b d)
    (hdet : 0 < a*d-b*c) (hcK : 4*c ≤ (K:ℤ)) (hdK : 4*d ≤ (K:ℤ))
    (hl : 0 < l) (hlw : l ≤ w)
    (hsa : l ≤ (a:ℝ)/c ∧ (a:ℝ)/c ≤ w)
    (hsb : l ≤ (b:ℝ)/d ∧ (b:ℝ)/d ≤ w) :
    ((a:ℝ)/c-(b:ℝ)/d)*(K:ℝ)^2/64 ≤
      ((TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).filter
        (fun p => (b:ℝ)/d < (p.1:ℝ)/p.2 ∧ (p.1:ℝ)/p.2 < (a:ℝ)/c)).card := by
  classical
  generalize hD : (a*d-b*c).toNat = D
  induction D using Nat.strong_induction_on generalizing a b c d with
  | h D ih =>
    have hcR : (0:ℝ) < c := by exact_mod_cast hc
    have hdR : (0:ℝ) < d := by exact_mod_cast hd
    by_cases hu : a*d-b*c=1
    · have hgap : (a:ℝ)/c-(b:ℝ)/d=1/((c:ℝ)*d) := by
        field_simp
        exact_mod_cast (show a*d-c*b=1 by nlinarith only [hu])
      have he := unimodular_cone_fareySector_interior_card_lower hu hc hd hcK hdK hl hlw
        ⟨(le_div_iff₀ hcR).mp hsa.1,(div_le_iff₀ hcR).mp hsa.2⟩
        ⟨(le_div_iff₀ hdR).mp hsb.1,(div_le_iff₀ hdR).mp hsb.2⟩
      rw [rational_interior_filter_eq hc hd hl hlw] at he
      calc
        _ = (K:ℝ)^2/(64*(c:ℝ)*d) := by rw [hgap]; ring
        _ ≤ _ := he
    · obtain ⟨m,n,hn,hnmax,hm,hup,hupD,hlo,hloD⟩ :=
        rational_interval_determinant_split hc hd ha hb (by omega)
      have hnK : 4*n ≤ (K:ℤ) := by
        rcases le_max_iff.mp hnmax with hh | hh <;> omega
      have hnR : (0:ℝ) < n := by exact_mod_cast hn
      have hx : (b:ℝ)/d < (m:ℝ)/n := (div_lt_div_iff₀ hdR hnR).mpr
        (by exact_mod_cast (show b*n < m*d by omega))
      have hy : (m:ℝ)/n < (a:ℝ)/c := (div_lt_div_iff₀ hnR hcR).mpr
        (by exact_mod_cast (show m*c < a*n by omega))
      have hsm : l ≤ (m:ℝ)/n ∧ (m:ℝ)/n ≤ w :=
        ⟨hsb.1.trans hx.le,hy.le.trans hsa.2⟩
      have hupper := ih (a*n-m*c).toNat (by omega)
        hc hn ha hm hup hcK hnK hsa hsm rfl
      have hlower := ih (m*d-b*n).toNat (by omega)
        hn hd hm hb hlo hnK hdK hsm hsb rfl
      have hcount := interval_filter_split_card
        (TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w)
        (fun p => (p.1:ℝ)/p.2) hx.le hy.le
      have hcountR :
          (((TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).filter
            (fun p => (b:ℝ)/d < (p.1:ℝ)/p.2 ∧ (p.1:ℝ)/p.2 < (m:ℝ)/n)).card:ℝ) +
          (((TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).filter
            (fun p => (m:ℝ)/n < (p.1:ℝ)/p.2 ∧ (p.1:ℝ)/p.2 < (a:ℝ)/c)).card:ℝ) ≤
          ((TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).filter
            (fun p => (b:ℝ)/d < (p.1:ℝ)/p.2 ∧ (p.1:ℝ)/p.2 < (a:ℝ)/c)).card := by
        have hh := (Nat.cast_le (α := ℝ)).mpr hcount
        simpa only [Nat.cast_add] using hh
      calc
        _ = ((m:ℝ)/n-(b:ℝ)/d)*(K:ℝ)^2/64 +
            ((a:ℝ)/c-(m:ℝ)/n)*(K:ℝ)^2/64 := by ring
        _ ≤ _ := (add_le_add hlower hupper).trans hcountR


                                                                   
                                                                          
theorem rational_separation_scaled {q r : ℚ} (hne : q ≠ r) :
    1 ≤ |(q:ℝ)-(r:ℝ)| * (q.den:ℝ)*r.den := by
  have hq : (q.den:ℝ) ≠ 0 := by exact_mod_cast q.den_nz
  have hr : (r.den:ℝ) ≠ 0 := by exact_mod_cast r.den_nz
  have hqid : (q:ℝ)=(q.num:ℝ)/q.den := by
    exact_mod_cast (Rat.num_div_den q).symm
  have hrid : (r:ℝ)=(r.num:ℝ)/r.den := by
    exact_mod_cast (Rat.num_div_den r).symm
  have hid : ((q.num*(r.den:ℤ)-r.num*(q.den:ℤ):ℤ):ℝ)=
      ((q:ℝ)-(r:ℝ))*(q.den:ℝ)*r.den := by
    rw [hqid,hrid]
    push_cast
    field_simp
  have hneI : q.num*(r.den:ℤ)-r.num*(q.den:ℤ) ≠ 0 := by
    intro he
    have hh : (q:ℝ)=(r:ℝ) := by
      have hz : ((q:ℝ)-(r:ℝ))*(q.den:ℝ)*r.den=0 := by rw [← hid,he]; simp
      rcases mul_eq_zero.mp hz with hz | hz
      · rcases mul_eq_zero.mp hz with hz | hz
        · exact sub_eq_zero.mp hz
        · exact (hq hz).elim
      · exact (hr hz).elim
    exact hne (Rat.cast_injective hh)
  have hsep : (1:ℝ) ≤ |((q.num*(r.den:ℤ)-r.num*(q.den:ℤ):ℤ):ℝ)| := by
    exact_mod_cast (show (1:ℤ) ≤ |q.num*(r.den:ℤ)-r.num*(q.den:ℤ)| by
      have hh := abs_pos.mpr hneI
      omega)
  rw [hid,abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg q.den : (0:ℝ) ≤ q.den),
    abs_of_nonneg (Nat.cast_nonneg r.den : (0:ℝ) ≤ r.den)] at hsep
  exact hsep


                                                                    
                                                                       
                                                       
theorem exists_rational_near_anchor {H : ℕ} {x Δ : ℝ} {r : ℚ}
    (hΔ : 0 < Δ) (hH : 16*r.den ≤ H)
    (hscale : 8 ≤ Δ*(H:ℝ)*r.den) (hx : |x-(r:ℝ)| ≤ Δ) :
    ∃ q : ℚ, q.den ≤ H ∧ |x-(q:ℝ)| ≤ Δ/8 := by
  have hH0 : 0 < H := by have hh := r.pos; omega
  have hHR : (0:ℝ) < H := by exact_mod_cast hH0
  obtain ⟨q,hq,hqH⟩ := Real.exists_rat_abs_sub_le_and_den_le x hH0
  refine ⟨q,hqH,?_⟩
  have hd : (0:ℝ) < q.den := by exact_mod_cast q.pos
  have hr : (0:ℝ) < r.den := by exact_mod_cast r.pos
  have hHRbound : 16*(r.den:ℝ) ≤ H := by exact_mod_cast hH
  have herr : |x-(q:ℝ)| * (q.den:ℝ)*(H:ℝ) ≤ 1 := by
    have hh := (le_div_iff₀ (mul_pos (by positivity : (0:ℝ) < H+1) hd)).mp hq
    have hm := mul_le_mul_of_nonneg_left (show (H:ℝ) ≤ H+1 by linarith)
      (mul_nonneg (abs_nonneg (x-(q:ℝ))) hd.le)
    nlinarith only [hh,hm]
  by_cases heq : q=r
  · subst q
    have hm := mul_le_mul_of_nonneg_left hscale (abs_nonneg (x-(r:ℝ)))
    have hh := mul_le_mul_of_nonneg_right herr hΔ.le
    nlinarith only [hm,hh]
  · have hsep := rational_separation_scaled heq
    have htri : |(q:ℝ)-(r:ℝ)| ≤ |x-(q:ℝ)|+Δ := by
      have hh := abs_sub_le (q:ℝ) x (r:ℝ)
      rw [abs_sub_comm (q:ℝ) x] at hh
      exact hh.trans (add_le_add le_rfl hx)
    have hsep' := hsep.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htri hd.le) hr.le)
    have he : |x-(q:ℝ)| * (q.den:ℝ)*r.den ≤ 1/16 := by
      have hh := mul_le_mul_of_nonneg_left hHRbound
        (mul_nonneg (abs_nonneg (x-(q:ℝ))) hd.le)
      nlinarith only [hh,herr]
    have hlo : 1/2 ≤ Δ*(q.den:ℝ)*r.den := by nlinarith only [hsep',he]
    have hh := mul_le_mul_of_nonneg_left hlo (abs_nonneg (x-(q:ℝ)))
    have hh' := mul_le_mul_of_nonneg_right he hΔ.le
    nlinarith only [hh,hh']


                                                                    
                                                                        
theorem exists_rational_inner_endpoints {H : ℕ} {l w : ℝ} {r : ℚ}
    (hlw : l < w) (hr : (r:ℝ) ∈ Set.Icc l w)
    (hH : 16*r.den ≤ H) (hscale : 8 ≤ (w-l)*(H:ℝ)*r.den) :
    ∃ a b : ℚ, a.den ≤ H ∧ b.den ≤ H ∧
      w-(w-l)/4 ≤ (a:ℝ) ∧ (a:ℝ) ≤ w ∧
      l ≤ (b:ℝ) ∧ (b:ℝ) ≤ l+(w-l)/4 := by
  have hΔ : 0 < w-l := sub_pos.mpr hlw
  obtain ⟨b,hbH,hb⟩ := exists_rational_near_anchor hΔ hH hscale
    (show |l+(w-l)/8-(r:ℝ)| ≤ w-l from abs_le.mpr ⟨by linarith [hr.2],by linarith [hr.1]⟩)
  obtain ⟨a,haH,ha⟩ := exists_rational_near_anchor hΔ hH hscale
    (show |w-(w-l)/8-(r:ℝ)| ≤ w-l from abs_le.mpr ⟨by linarith [hr.2],by linarith [hr.1]⟩)
  obtain ⟨halo,hahi⟩ := abs_le.mp ha
  obtain ⟨hblo,hbhi⟩ := abs_le.mp hb
  exact ⟨a,b,haH,hbH,by linarith,by linarith,by linarith,by linarith⟩


                                                                      
                                                                       
                                                                        
theorem fareySector_card_lower_of_rational_anchor
    {H K : ℕ} {l w : ℝ} {r : ℚ}
    (hl : 0 < l) (hlw : l < w) (hr : (r:ℝ) ∈ Set.Icc l w)
    (hH : 16*r.den ≤ H) (hHK : 4*H ≤ K)
    (hscale : 8 ≤ (w-l)*(H:ℝ)*r.den) :
    (w-l)*(K:ℝ)^2/128 ≤
      (TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).card := by
  classical
  obtain ⟨a,b,haH,hbH,halo,hahi,hblo,hbhi⟩ :=
    exists_rational_inner_endpoints hlw hr hH hscale
  have hab : (b:ℝ) < (a:ℝ) := by linarith
  have haR : (0:ℝ) < a.den := by exact_mod_cast a.pos
  have hbR : (0:ℝ) < b.den := by exact_mod_cast b.pos
  have hadiv : (a.num:ℝ)/(a.den:ℝ)=(a:ℝ) := by exact_mod_cast Rat.num_div_den a
  have hbdiv : (b.num:ℝ)/(b.den:ℝ)=(b:ℝ) := by exact_mod_cast Rat.num_div_den b
  have hdet : 0 < a.num*(b.den:ℤ)-b.num*(a.den:ℤ) := by
    have hh := (div_lt_div_iff₀ hbR haR).mp (show (b.num:ℝ)/b.den < (a.num:ℝ)/a.den by
      rwa [hadiv,hbdiv])
    exact_mod_cast (sub_pos.mpr hh)
  have haK : 4*(a.den:ℤ) ≤ (K:ℤ) := by exact_mod_cast (show 4*a.den ≤ K by omega)
  have hbK : 4*(b.den:ℤ) ≤ (K:ℤ) := by exact_mod_cast (show 4*b.den ≤ K by omega)
  have hsa : l ≤ (a.num:ℝ)/(a.den:ℤ) ∧ (a.num:ℝ)/(a.den:ℤ) ≤ w := by
    simp only [Int.cast_natCast,hadiv]
    exact ⟨by linarith,hahi⟩
  have hsb : l ≤ (b.num:ℝ)/(b.den:ℤ) ∧ (b.num:ℝ)/(b.den:ℤ) ≤ w := by
    simp only [Int.cast_natCast,hbdiv]
    exact ⟨hblo,by linarith⟩
  have he := rational_interval_fareySector_interior_card_lower
    (by exact_mod_cast a.pos) (by exact_mod_cast b.pos)
    a.isCoprime_num_den b.isCoprime_num_den hdet haK hbK hl hlw.le hsa hsb
  have hfilter := Finset.card_filter_le
    (TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w)
    (fun p => (b.num:ℝ)/(b.den:ℤ) < (p.1:ℝ)/p.2 ∧ (p.1:ℝ)/p.2 < (a.num:ℝ)/(a.den:ℤ))
  have hcount := he.trans ((Nat.cast_le (α := ℝ)).mpr hfilter)
  simp only [Int.cast_natCast,hadiv,hbdiv] at hcount
  have hwidth : (w-l)/2 ≤ (a:ℝ)-(b:ℝ) := by linarith
  have hh := mul_le_mul_of_nonneg_right hwidth (sq_nonneg (K:ℝ))
  linarith only [hh,hcount]


                                                                   
                                                       
                                                                       
theorem fareySector_card_lower_source_scale
    {K : ℕ} {l w : ℝ} {r : ℚ}
    (hl : 0 < l) (hlw : l < w) (hr : (r:ℝ) ∈ Set.Icc l w)
    (hden : 64*r.den ≤ K) (hscale : 64 ≤ (w-l)*(K:ℝ)*r.den) :
    (w-l)*(K:ℝ)^2/128 ≤
      (TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).card := by
  let H := K/4
  have hH : 16*r.den ≤ H := by dsimp [H]; omega
  have hHK : 4*H ≤ K := by dsimp [H]; omega
  have hK8 : K ≤ 8*H := by have hh := r.pos; dsimp [H]; omega
  have hscaleH : 8 ≤ (w-l)*(H:ℝ)*r.den := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (show (K:ℝ) ≤ 8*(H:ℝ) by exact_mod_cast hK8)
        (sub_nonneg.mpr hlw.le)) (Nat.cast_nonneg r.den : (0:ℝ) ≤ r.den)
    nlinarith only [hh,hscale]
  exact fareySector_card_lower_of_rational_anchor hl hlw hr hH hHK hscaleH


                                                                    
                                                         
theorem fareySector_source_density_gate
    {K : ℕ} {l w : ℝ} {r : ℚ}
    (hl : 0 < l) (hlw : l < w) (hr : (r:ℝ) ∈ Set.Icc l w)
    (hden : 64*r.den ≤ K) (hscale : 64 ≤ (w-l)*(K:ℝ)*r.den) :
    max ((w-l)*(K:ℝ)^2/128:ℝ) 2 ≤
      (TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).card := by
  have he := fareySector_card_lower_source_scale hl hlw hr hden hscale
  have hh := mul_le_mul_of_nonneg_left
    (show 64*(r.den:ℝ) ≤ K by exact_mod_cast hden)
    (mul_nonneg (sub_nonneg.mpr hlw.le) (Nat.cast_nonneg K))
  apply max_le he
  have hbig : 4096 ≤ (w-l)*(K:ℝ)^2 := by nlinarith only [hh,hscale]
  linarith only [hbig,he]


                                                                  
                                                                   
                                                 
theorem physicalModelPhase_halfCurvature_growth
    {σ δ T M A W x y : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx : x ∈ Set.Ioo 0 W) (hy : y ∈ Set.Ioo 0 W) (hxy : x ≤ y) :
    let f := heathBrownPhysicalPhase F T M A 1
    modelPhaseThirdLower σ*T/(2*M^3)*(y-x) ≤
      iteratedDeriv 2 f y/2-iteratedDeriv 2 f x/2 := by
  let f := heathBrownPhysicalPhase F T M A 1
  let g := fun z => iteratedDeriv 2 f z/2
  have hd (z : ℝ) (hz : z ∈ Set.Ioo 0 W) :
      HasDerivAt g (iteratedDeriv 3 f z/2) z := by
    have hcf := heathBrownPhysicalPhase_contDiffOn hF.1 hM hA hW T 1
    have hf3 : ContDiffAt ℝ 3 f z :=
      ((hcf z (Set.Ioo_subset_Icc_self hz)).contDiffAt
        (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hz) Set.Ioo_subset_Icc_self)).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
    exact (hasDerivAt_iteratedDeriv_finite (by norm_num : 2 < 3) hf3).div_const 2
  have hb (z : ℝ) (hz : z ∈ Set.Ioo 0 W) :
      modelPhaseThirdLower σ*T/(2*M^3) ≤ deriv g z := by
    rw [(hd z hz).deriv,heathBrownPhysicalPhase_iteratedDeriv hF.1 hM hA hW hz,one_mul]
    have hlo : modelPhaseThirdLower σ ≤ iteratedDeriv 3 F ((A+z)/M) := by
      have hh := (approximateModelPhase_thirdDeriv_bounds hσ hδ hF
        (heathBrownPhysicalPoint_mem_interior hM hA hW hz)).1
      simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hh
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlo (by positivity : 0 ≤ T/M^3)) (by norm_num : (0:ℝ) ≤ 2)
    convert hh using 1
    ring
  exact (convex_Ioo (0:ℝ) W).mul_sub_le_image_sub_of_le_deriv
    (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
    (fun z hz => (hd z (by simpa only [interior_Ioo] using hz)).differentiableAt.differentiableWithinAt)
    (fun z hz => hb z (by simpa only [interior_Ioo] using hz)) x hx y hy hxy


                                                                   
theorem physicalModelPhase_minorArcCoordinate_growth
    {σ δ T M A W x y μ e r v s : ℝ} {F : ℝ → ℝ} (u t : Fin 2 → ℝ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx : x ∈ Set.Ioo 0 W) (hy : y ∈ Set.Ioo 0 W) (hxy : x ≤ y)
    (hμ : 0 < μ) (hr : r ≠ 0) (ht : ∀ i, t i ≠ 0)
    (hq : ∀ i, r*u i+s*t i ≠ 0) (hdet : v*r-e*s=1) :
    let f := heathBrownPhysicalPhase F T M A 1
    iteratedDeriv 2 f x/2=(e*u 0+v*t 0)/(r*u 0+s*t 0) →
    iteratedDeriv 2 f y/2=(e*u 1+v*t 1)/(r*u 1+s*t 1) →
    modelPhaseThirdLower σ*T/(6*μ*M^3)*(y-x) ≤
      minorArcCoordinate μ r s (u 1/t 1)-minorArcCoordinate μ r s (u 0/t 0) := by
  change _ → _ → _
  intro h₀ h₁
  have hh := physicalModelPhase_halfCurvature_growth hσ hδ hF hT hM hA hW hx hy hxy
  dsimp only at hh
  rw [h₀,h₁] at hh
  have he₀ := farey_curvature_coordinate_identity hμ.ne' hr (ht 0) (hq 0) hdet
  have he₁ := farey_curvature_coordinate_identity hμ.ne' hr (ht 1) (hq 1) hdet
  have he : modelPhaseThirdLower σ*T/(2*M^3)*(y-x) ≤
      3*μ*(minorArcCoordinate μ r s (u 1/t 1)-minorArcCoordinate μ r s (u 0/t 0)) := by
    linarith only [hh,he₀,he₁]
  have hd : (modelPhaseThirdLower σ*T/(2*M^3)*(y-x))/(3*μ) ≤
      minorArcCoordinate μ r s (u 1/t 1)-minorArcCoordinate μ r s (u 0/t 0) :=
    (div_le_iff₀ (show 0 < 3*μ by positivity)).mpr (by nlinarith only [he])
  convert hd using 1
  ring


                                                                    
                                                                     
                                                                          
                                                   
theorem inverseFarey_difference {e r v s x y : ℝ}
    (hdet : v*r-e*s=1) (hx : r*x-e ≠ 0) (hy : r*y-e ≠ 0) :
    (v-s*x)/(r*x-e)-(v-s*y)/(r*y-e)=(y-x)/((r*x-e)*(r*y-e)) := by
  rw [div_sub_div _ _ hx hy]
  congr 1
  linear_combination (y-x)*hdet


theorem inverseFarey_rational_anchor {e r v s : ℤ} {a : ℚ}
    (hdet : v*r-e*s=1) (hpos : 0 < r*a.num-e*a.den) :
    let b : ℚ := ((v*a.den-s*a.num:ℤ):ℚ)/((r*a.num-e*a.den:ℤ):ℚ)
    (b.den:ℤ)=r*a.num-e*a.den ∧
      (b:ℝ)=((v:ℝ)-s*(a:ℝ))/((r:ℝ)*(a:ℝ)-e) := by
  let u : ℤ := v*a.den-s*a.num
  let t : ℤ := r*a.num-e*a.den
  have ht : 0 < t := hpos
  have hc := isCoprime_unimodular_image (a := r) (b := -e) (c := -s) (d := v)
    (by nlinarith only [hdet]) (Rat.isCoprime_num_den a)
  have hcop : IsCoprime u t := by
    simpa only [u,t,neg_mul,← sub_eq_add_neg,add_comm] using hc.symm
  have hden := Rat.den_div_eq_of_coprime ht (Int.isCoprime_iff_nat_coprime.mp hcop)
  change (((u:ℚ)/(t:ℚ)).den:ℤ)=t ∧ _
  refine ⟨hden,?_⟩
  have hq : (a.den:ℝ) ≠ 0 := by exact_mod_cast a.den_nz
  have ha : (a:ℝ)=(a.num:ℝ)/a.den := by exact_mod_cast (Rat.num_div_den a).symm
  push_cast
  rw [ha]
  field_simp [hq]


                                                                       
                                                                      
                                                                      
                                                
theorem exists_eight_block_indices {B : ℕ} (hB : 32 ≤ B) :
    ∃ j : Fin 8 → Fin B, StrictMono j ∧
      ∀ i : Fin 7, (B:ℝ)/16 ≤ ((j i.succ).val:ℝ)-(j i.castSucc).val-1 := by
  let k := B/8
  have hk : 4 ≤ k := by dsimp [k]; omega
  have hkpos : 0 < k := by omega
  have hb : 8*k ≤ B := by dsimp [k]; omega
  have hbhi : B < 8*k+8 := by dsimp [k]; omega
  let j : Fin 8 → Fin B := fun i => ⟨i.val*k,by
    have hh := Nat.mul_lt_mul_of_pos_right i.isLt hkpos
    omega⟩
  have hj : StrictMono j := by
    intro i i' hii'
    change i.val*k < i'.val*k
    exact Nat.mul_lt_mul_of_pos_right hii' hkpos
  refine ⟨j,hj,?_⟩
  intro i
  have hBR : (B:ℝ) ≤ 8*(k:ℝ)+7 := by exact_mod_cast (show B ≤ 8*k+7 by omega)
  have hkR : (4:ℝ) ≤ k := by exact_mod_cast hk
  change (B:ℝ)/16 ≤ (((i.val+1)*k:ℕ):ℝ)-(i.val*k:ℕ)-1
  push_cast
  nlinarith only [hBR,hkR]


                                                              
                                                                      
                                                                         
                                                                         
                                                                     
theorem physicalModelPhase_cubicCoefficient_bounds
    {σ δ T M A W z : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hz : z ∈ Set.Ioo 0 W) :
    let μ := iteratedDeriv 3 (heathBrownPhysicalPhase F T M A 1) z/6
    modelPhaseThirdLower σ*T/(6*M^3) ≤ μ ∧
      μ ≤ (σ*(σ+1)+1)*T/(6*M^3) := by
  have hh := approximateModelPhase_thirdDeriv_bounds hσ hδ hF
    (heathBrownPhysicalPoint_mem_interior hM hA hW hz)
  have hb : modelPhaseThirdLower σ ≤ iteratedDeriv 3 F ((A+z)/M) ∧
      iteratedDeriv 3 F ((A+z)/M) ≤ σ*(σ+1)+1 := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hh
  dsimp only
  rw [heathBrownPhysicalPhase_iteratedDeriv hF.1 hM hA hW hz,one_mul]
  have hlo := mul_le_mul_of_nonneg_left hb.1 (show 0 ≤ T/(6*M^3) by positivity)
  have hhi := mul_le_mul_of_nonneg_left hb.2 (show 0 ≤ T/(6*M^3) by positivity)
  constructor
  · convert hlo using 1 <;> ring
  · convert hhi using 1 <;> ring


                                                                   
                                                               
theorem physicalModelPhase_cubicCoefficient_source_scale
    {σ δ T M A W z N R : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hz : z ∈ Set.Ioo 0 W) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) :
    let μ := iteratedDeriv 3 (heathBrownPhysicalPhase F T M A 1) z/6
    0 < μ ∧ 1 ≤ (6/modelPhaseThirdLower σ)*μ*N*R^2 ∧
      modelPhaseThirdLower σ/(16*(σ*(σ+1)+1)) ≤ modelPhaseThirdLower σ*T/(96*μ*M^3) := by
  let μ := iteratedDeriv 3 (heathBrownPhysicalPhase F T M A 1) z/6
  obtain ⟨hlo,hhi⟩ := physicalModelPhase_cubicCoefficient_bounds hσ hδ hF hT hM hA hW hz
  change modelPhaseThirdLower σ*T/(6*M^3) ≤ μ at hlo
  change μ ≤ (σ*(σ+1)+1)*T/(6*M^3) at hhi
  have hκ := modelPhaseThirdLower_pos hσ
  have hμ : 0 < μ := lt_of_lt_of_le (by positivity) hlo
  have hC : 0 < σ*(σ+1)+1 := by positivity
  have hlom := (div_le_iff₀ (show 0 < 6*M^3 by positivity)).mp hlo
  have hhim := (le_div_iff₀ (show 0 < 6*M^3 by positivity)).mp hhi
  refine ⟨hμ,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_right hlom (show 0 ≤ N*R^2 by positivity)
    have hc : modelPhaseThirdLower σ ≤ 6*μ*N*R^2 := by
      have hid : modelPhaseThirdLower σ*T*(N*R^2)=modelPhaseThirdLower σ*M^3 := by
        linear_combination modelPhaseThirdLower σ*hscale
      rw [hid] at hh
      apply (mul_le_mul_iff_of_pos_right (show 0 < M^3 by positivity)).mp
      nlinarith only [hh]
    have hh' : (1:ℝ) ≤ (6*μ*N*R^2)/modelPhaseThirdLower σ :=
      (le_div_iff₀ hκ).mpr (by nlinarith only [hc])
    convert hh' using 1
    ring
  · change modelPhaseThirdLower σ/(16*(σ*(σ+1)+1)) ≤ modelPhaseThirdLower σ*T/(96*μ*M^3)
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_left hhim (show 0 ≤ 16*modelPhaseThirdLower σ by positivity)
    nlinarith only [hh]


                                                                    
                                                                      
                                                                            
noncomputable def minorArcCenterLabels (x ε : ℝ) : Finset ℤ :=
  ({round x, if 0 ≤ x-round x then round x+1 else round x-1} : Finset ℤ).filter
    (fun c => |x-c| ≤ 1/2+ε)

theorem mem_minorArcCenterLabels_iff {x ε : ℝ} {n : ℤ} (hε : ε < 1/2) :
    n ∈ minorArcCenterLabels x ε ↔ |x-n| ≤ 1/2+ε := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro hn
    have hr := abs_sub_round x
    have hlo : (round x:ℝ)-2 < n := by
      nlinarith only [(abs_le.mp hn).2,(abs_le.mp hr).1,hε]
    have hhi : (n:ℝ) < round x+2 := by
      nlinarith only [(abs_le.mp hn).1,(abs_le.mp hr).2,hε]
    have hloI : round x-2 < n := by exact_mod_cast hlo
    have hhiI : n < round x+2 := by exact_mod_cast hhi
    have hcases : n=round x ∨ n=round x+1 ∨ n=round x-1 := by omega
    apply Finset.mem_filter.mpr
    refine ⟨?_,hn⟩
    simp only [Finset.mem_insert,Finset.mem_singleton]
    rcases hcases with rfl | rfl | rfl
    · exact Or.inl rfl
    · right
      have hx : 0 ≤ x-round x := by
        have hh := (abs_le.mp hn).1
        push_cast at hh
        linarith only [hh,hε]
      simp only [ite_eq_left hx]
    · right
      have hx : ¬ 0 ≤ x-round x := by
        have hh := (abs_le.mp hn).2
        push_cast at hh
        linarith only [hh,hε]
      simp only [ite_eq_right hx]


                                                                    
                                                                       
theorem exists_compatible_center_labels {x y ε : ℝ}
    (hε : ε < 1/2) (hnear : |(x-y)-round (x-y)| ≤ ε) :
    ∃ c ∈ minorArcCenterLabels x ε, ∃ d ∈ minorArcCenterLabels y ε,
      c=round x ∧ |(x-c)-(y-d)| ≤ ε := by
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans hnear
  let c := round x
  let d := c-round (x-y)
  have hc : |x-c| ≤ 1/2+ε := (abs_sub_round x).trans (by linarith)
  have hid : (x-c)-(y-d)=(x-y)-round (x-y) := by dsimp [d]; push_cast; ring
  have hd : |y-d| ≤ 1/2+ε := by
    have hh := abs_sub_le (x-c) 0 ((x-c)-(y-d))
    rw [sub_zero,zero_sub,abs_neg,show (x-c)-((x-c)-(y-d))=y-d by ring,hid] at hh
    exact hh.trans (add_le_add (abs_sub_round x) hnear)
  exact ⟨c,(mem_minorArcCenterLabels_iff hε).mpr hc,
    d,(mem_minorArcCenterLabels_iff hε).mpr hd,rfl,by rwa [hid]⟩


                                                                    
                                                                 
theorem linearization_pair_bound_with_labels {z z₁ L L₁ E E₁ Δ : ℝ} {j j₁ c c₁ : ℤ}
    (hL : |z-j-L| ≤ E) (hL₁ : |z₁-j₁-L₁| ≤ E₁)
    (hfourth : |(z-c)-(z₁-c₁)| ≤ Δ) :
    |(L-L₁)-((c-j)-(c₁-j₁):ℤ)| ≤ Δ+E+E₁ := by
  have hid : (L-L₁)-((c-j)-(c₁-j₁):ℤ) =
      ((z-c)-(z₁-c₁))-(z-j-L)+(z₁-j₁-L₁) := by
    push_cast
    ring
  rw [hid]
  have ht := abs_add_le ((z-c)-(z₁-c₁)) (-(z-j-L))
  rw [abs_neg,← sub_eq_add_neg] at ht
  exact (abs_add_le _ _).trans (add_le_add (ht.trans (add_le_add hfourth hL)) hL₁)


                                                                      
                                                                        
                                                                         
                                                                 
theorem second_condition_taylor_source_scale {T M N R C₂ C₃ n : ℝ}
    (hM : M ≠ 0) (hN : N ≠ 0) (hR : R ≠ 0) (hscale : T*N*R^2=M^3) :
    T*C₂*n/(2*M^3)+5*T*C₃*n^3/(12*M^4) =
      C₂*n/(2*N*R^2)+5*C₃*n^3/(12*M*N*R^2) := by
  have hT : T=M^3/(N*R^2) := (eq_div_iff (by positivity)).mpr (by nlinarith only [hscale])
  rw [hT]
  field_simp

                                                                      
                                                                          
                                                                         
                                                                    
theorem rationalBranch_base_normal_form {μ r s x : ℝ} (hr : r ≠ 0) :
    rationalBranch μ r s x=1/(3*(μ*r^3)*(x+s/r)) := by
  unfold rationalBranch
  congr 1
  field_simp

                                                                   
                                                                      
theorem rationalPhase_bound_from_base_coincidences
    {μ r s μ₁ r₁ s₁ x ε η : ℝ}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hx : x+s/r ≠ 0)
    (hthird : |μ₁*r₁^3/(μ*r^3)-1| ≤ ε) (hε : ε ≤ 1/2)
    (hfirst : |s₁/r₁-s/r| ≤ η*|x+s/r|) (hη : η ≤ 1/2) :
    |rationalPhase μ r s μ₁ r₁ s₁ x| ≤
      (12*ε+4*η)*|rationalBranch μ r s x| := by
  let A := μ*r^3
  let B := μ₁*r₁^3
  let X := x+s/r
  let Y := x+s₁/r₁
  have hA : A ≠ 0 := mul_ne_zero hμ (pow_ne_zero 3 hr)
  have hB : B ≠ 0 := mul_ne_zero hμ₁ (pow_ne_zero 3 hr₁)
  have hX : X ≠ 0 := hx
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans hthird
  have hoff : |Y/X-1| ≤ η := by
    have hi : Y/X-1=(s₁/r₁-s/r)/X := by
      calc
        Y/X-1=Y/X-X/X := by rw [div_self hX]
        _ = (Y-X)/X := by rw [sub_div]
        _ = (s₁/r₁-s/r)/X := by congr 1; dsimp [Y,X]; ring
    rw [hi,abs_div]
    exact (div_le_iff₀ (abs_pos.mpr hX)).mpr hfirst
  have hη0 : 0 ≤ η := (abs_nonneg _).trans hoff
  have hY : Y ≠ 0 := by
    intro hz
    rw [hz,zero_div] at hoff
    norm_num at hoff
    linarith
  have hinv := ratio_relative_perturbation (a := (1:ℝ)) (u := (1:ℝ))
    (v := B/A) (ε := 0) (η := ε) (by norm_num)
    (by simpa using hε0) hthird hε
  norm_num only [one_mul,zero_mul,zero_add] at hinv
  have hp := ratio_relative_perturbation hinv (u := (1:ℝ)) (v := Y/X)
    (by simpa using hη0) hoff hη
  have halg (a b X Y : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
      (hX : X ≠ 0) (hY : Y ≠ 0) :
      1/(3*a*X)-1/(3*b*Y) =
        (1/(3*a*X))*(1-(1/(b/a))*1/(Y/X)) := by
    field_simp
  have hid : rationalPhase μ r s μ₁ r₁ s₁ x =
      rationalBranch μ r s x*(1-(1/(B/A))*1/(Y/X)) := by
    unfold rationalPhase
    rw [rationalBranch_base_normal_form hr,rationalBranch_base_normal_form hr₁]
    exact halg A B X Y hA hB hX hY
  rw [hid,abs_mul]
  have hsame : |1-(1/(B/A))*1/(Y/X)| ≤ 12*ε+4*η := by
    rw [abs_sub_comm]
    convert hp using 1
    ring
  exact (mul_le_mul_of_nonneg_left hsame (abs_nonneg _)).trans_eq (mul_comm _ _)



                                                                  
                                                                       
theorem farey_base_difference_identity
    {r s r₁ s₁ u t n n₁ c c₁ θ θ₁ γ γ₁ G G₁ b : ℝ}
    (hr : r ≠ 0) (hr₁ : r₁ ≠ 0) :
    let H := (c*s-n)*t/r+θ*(r*u+s*t)/r+γ
    let H₁ := (c₁*s₁-n₁)*t/r₁+θ₁*(r₁*u+s₁*t)/r₁+γ₁
    H-H₁-b*t =
      (c*s/r-c₁*s₁/r₁-b)*t-(G/r-G₁/r₁)*t+
      (θ-θ₁)*(r*u+s*t)/r+θ₁*t*(s/r-s₁/r₁)+
      γ-γ₁-(n-G)*t/r+(n₁-G₁)*t/r₁ := by
  dsimp only
  field_simp
  ring

                                                                      
                                                                           
theorem minorArcCoordinate_div_eq_branch (μ r s x : ℝ) :
    minorArcCoordinate μ r s x/r=rationalBranch μ r s x := by
  dsimp [minorArcCoordinate,rationalBranch]
  rw [div_div]
  congr 1
  ring

                                                                 
                                                                       
                                                                 
theorem farey_base_coincidence_difference_bound
    {μ r s μ₁ r₁ s₁ u t n n₁ c c₁ θ θ₁ γ γ₁ b
      ε η D₁ D₂ D₄ A A₁ V V₁ : ℝ}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hx : u/t+s/r ≠ 0)
    (hthird : |μ₁*r₁^3/(μ*r^3)-1| ≤ ε) (hε : ε ≤ 1/2)
    (hfirstRelative : |s₁/r₁-s/r| ≤ η*|u/t+s/r|) (hη : η ≤ 1/2)
    (hfirst : |s/r-s₁/r₁| ≤ D₁)
    (hsecond : |c*s/r-c₁*s₁/r₁-b| ≤ D₂)
    (hfourth : |θ-θ₁| ≤ D₄) (hcenter : |θ₁| ≤ 1/2)
    (hcoord : |n-minorArcCoordinate μ r s (u/t)| ≤ A)
    (hcoord₁ : |n₁-minorArcCoordinate μ₁ r₁ s₁ (u/t)| ≤ A₁)
    (hγ : |γ| ≤ V) (hγ₁ : |γ₁| ≤ V₁) :
    let H := (c*s-n)*t/r+θ*(r*u+s*t)/r+γ
    let H₁ := (c₁*s₁-n₁)*t/r₁+θ₁*(r₁*u+s₁*t)/r₁+γ₁
    |H-H₁-b*t| ≤
      D₂*|t|+(12*ε+4*η)*|rationalBranch μ r s (u/t)| * |t|+
      D₄*|(r*u+s*t)/r|+(1/2:ℝ)*|t| * D₁+
      V+V₁+A*|t/r|+A₁*|t/r₁| := by
  let G := minorArcCoordinate μ r s (u/t)
  let G₁ := minorArcCoordinate μ₁ r₁ s₁ (u/t)
  have hg := rationalPhase_bound_from_base_coincidences hμ hμ₁ hr hr₁ hx
    hthird hε hfirstRelative hη
  have hid := farey_base_difference_identity (G := G) (G₁ := G₁)
    (n := n) (n₁ := n₁) (c := c) (c₁ := c₁) (θ := θ) (θ₁ := θ₁)
    (γ := γ) (γ₁ := γ₁) (s := s) (s₁ := s₁) (u := u) (t := t) (b := b) hr hr₁
  have hG : G/r-G₁/r₁=rationalPhase μ r s μ₁ r₁ s₁ (u/t) := by
    rw [minorArcCoordinate_div_eq_branch,minorArcCoordinate_div_eq_branch]
    rfl
  dsimp only at hid ⊢
  rw [hid,hG]
  have h1 := mul_le_mul_of_nonneg_right hsecond (abs_nonneg t)
  have h2 := mul_le_mul_of_nonneg_right hg (abs_nonneg t)
  have h3 := mul_le_mul_of_nonneg_right hfourth (abs_nonneg ((r*u+s*t)/r))
  have h4 := mul_le_mul hcenter hfirst (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1/2)
  have h4' := mul_le_mul_of_nonneg_right h4 (abs_nonneg t)
  have h5 := mul_le_mul_of_nonneg_right hcoord (abs_nonneg (t/r))
  have h6 := mul_le_mul_of_nonneg_right hcoord₁ (abs_nonneg (t/r₁))
  calc
    _ ≤ |(c*s/r-c₁*s₁/r₁-b)*t|+
        |rationalPhase μ r s μ₁ r₁ s₁ (u/t)*t|+
        |(θ-θ₁)*(r*u+s*t)/r|+|θ₁*t*(s/r-s₁/r₁)|+
        |γ|+|γ₁|+|(n-G)*t/r|+|(n₁-G₁)*t/r₁| := by
      have htri (a b c d e f g h : ℝ) :
          |a-b+c+d+e-f-g+h| ≤ |a|+|b|+|c|+|d|+|e|+|f|+|g|+|h| := by
        have h0 := abs_sub a b
        have h1 := abs_add_le (a-b) c
        have h2 := abs_add_le (a-b+c) d
        have h3 := abs_add_le (a-b+c+d) e
        have h4 := abs_sub (a-b+c+d+e) f
        have h5 := abs_sub (a-b+c+d+e-f) g
        have h6 := abs_add_le (a-b+c+d+e-f-g) h
        linarith only [h0,h1,h2,h3,h4,h5,h6]
      exact htri _ _ _ _ _ _ _ _
    _ ≤ _ := by
      dsimp only [G,G₁] at *
      simp only [abs_mul,div_eq_mul_inv] at *
      nlinarith only [h1,h2,h3,h4',h5,h6,hγ,hγ₁]



                                                                    
                                                                        
                                                                      
theorem actual_derivative_base_centered_bound
    {e r v s n : Fin 2 → ℤ} {d₀ d₁ : Fin 2 → ℝ} {u t b : ℤ}
    (hr : ∀ i, r i ≠ 0) (hq : ∀ i, r i*u+s i*t ≠ 0)
    (hdet : ∀ i, v i*r i-e i*s i=1) :
    let q := fun i => (r i:ℝ)*u+s i*t
    let c := fun i => round ((r i:ℝ)*d₀ i)
    let θ := fun i => (r i:ℝ)*d₀ i-c i
    let γ := fun i => q i*(d₁ i-d₀ i-2*(e i:ℝ)*n i/r i-
      (n i:ℝ)*t/(r i*q i))
    let H := fun i => ((c i:ℝ)*s i-n i)*t/r i+θ i*q i/r i+γ i
    let z := fun i => q i*d₁ i
    |(z 0-z 1)-round (z 0-z 1)| ≤ |H 0-H 1-(b:ℝ)*t| := by
  let q := fun i => (r i:ℝ)*u+s i*t
  let c := fun i => round ((r i:ℝ)*d₀ i)
  let θ := fun i => (r i:ℝ)*d₀ i-c i
  let γ := fun i => q i*(d₁ i-d₀ i-2*(e i:ℝ)*n i/r i-
    (n i:ℝ)*t/(r i*q i))
  let H := fun i => ((c i:ℝ)*s i-n i)*t/r i+θ i*q i/r i+γ i
  let z := fun i => q i*d₁ i
  let j := fun i => c i*u+2*n i*(e i*u+v i*t)
  have hid (i) : z i=(j i:ℝ)+H i := by
    have hr' : (r i:ℝ) ≠ 0 := by exact_mod_cast hr i
    have hq' : q i ≠ 0 := by dsimp [q]; exact_mod_cast hq i
    have hdet' : (v i:ℝ)*r i-e i*s i=1 := by exact_mod_cast hdet i
    have hh := farey_firstDerivative_residual_identity hr' hq' hdet'
      (n := (n i:ℝ)) (c := (c i:ℝ)) (θ := θ i) (d₀ := d₀ i) (d₁ := d₁ i)
      (by dsimp [θ]; ring)
    dsimp only at hh
    dsimp only [z,j,H]
    push_cast
    linear_combination hh
  have heq : (z 0-z 1)-((j 0-j 1+b*t:ℤ):ℝ)=H 0-H 1-(b:ℝ)*t := by
    rw [hid 0,hid 1]
    push_cast
    ring
  have hh := round_le (z 0-z 1) (j 0-j 1+b*t)
  rw [heq] at hh
  exact hh



                                                                   
                                                                         
                                                                   
                                                                        
                                              
theorem physicalModelPhase_base_residual_difference_bound
    {σ δ T M N R ε η D₂ D₄ : ℝ} {u t : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) (hε : ε ≤ 1/2) (hη : η ≤ 1/2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (ht : t ≠ 0)
    (hq : ∀ i, r i*u+s i*t ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1) :
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
    let D := fun i =>
      (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)*|(n i:ℝ)|/(2*N*R^2)+
      5*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*|(n i:ℝ)|^3/(12*M*N*R^2)
    let V := fun i => (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)/
      TaoTrudgianYang2025.modelPhaseThirdLower σ+
      (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*|(n i:ℝ)|^2/
        (2*TaoTrudgianYang2025.modelPhaseThirdLower σ*M)
    let γ := fun i => q i*(d₁ i-d₀ i-2*(e i:ℝ)*n i/r i-
      (n i:ℝ)*t/(r i*q i))
    let H := fun i => ((c i:ℝ)*s i-n i)*t/r i+θ i*q i/r i+γ i
    let Λ := D₂*|(t:ℝ)|+
      (12*ε+4*η)*|rationalBranch (μ 0) (r 0) (s 0) ((u:ℝ)/t)| * |(t:ℝ)|+
      D₄*|q 0/r 0|+(1/2:ℝ)*|(t:ℝ)| * (η*|U|)+
      |q 0| * D 0+|q 1| * D 1+V 0*|(t:ℝ)/r 0|+V 1*|(t:ℝ)/r 1|
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    |μ 1*(r 1:ℝ)^3/(μ 0*(r 0:ℝ)^3)-1| ≤ ε →
    |(s 1:ℝ)/r 1-(s 0:ℝ)/r 0| ≤ η*|U| →
    |C-round C| ≤ D₂ →
    |θ 0-θ 1| ≤ D₄ →
    |H 0-H 1-(round C:ℝ)*t| ≤ Λ := by
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
  let D := fun i =>
    (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)*|(n i:ℝ)|/(2*N*R^2)+
    5*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*|(n i:ℝ)|^3/(12*M*N*R^2)
  let V := fun i => (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)/
    TaoTrudgianYang2025.modelPhaseThirdLower σ+
    (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*|(n i:ℝ)|^2/
      (2*TaoTrudgianYang2025.modelPhaseThirdLower σ*M)
  let γ := fun i => q i*(d₁ i-d₀ i-2*(e i:ℝ)*n i/r i-
    (n i:ℝ)*t/(r i*q i))
  change _ → _ → _ → _ → _ → _ → _
  intro hbase hpoint hthird hfirst hsecond hfourth
  have hr' (i) : (r i:ℝ) ≠ 0 := by exact_mod_cast hr i
  have ht' : (t:ℝ) ≠ 0 := by exact_mod_cast ht
  have hq' (i) : q i ≠ 0 := by dsimp [q]; exact_mod_cast hq i
  have hdet' (i) : (v i:ℝ)*r i-e i*s i=1 := by exact_mod_cast hdet i
  have hμ (i) : μ i ≠ 0 := (physicalModelPhase_rounded_cubicCoefficient_pos hσ hδ
    (TaoTrudgianYang2025.approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 3) le_rfl)
    hT hM (hA i) (hW i) (hx₀ i)).ne'
  have hU : U ≠ 0 := by
    have hid : U*((r 0:ℝ)*t)=q 0 := by dsimp [U,q]; field_simp [ht',hr' 0]
    intro hz
    rw [hz,zero_mul] at hid
    exact hq' 0 hid.symm
  have hG (i) : |(n i:ℝ)-minorArcCoordinate (μ i) (r i) (s i) ((u:ℝ)/t)| ≤ V i := by
    have hh := physicalModelPhase_rounded_minorArcCoordinate_entry hσ hδ (hF i)
      hT hM (hA i) (hW i) (hx₀ i) (hx₁ i) (hr' i) ht' (hq' i) (hdet' i)
      (hbase i) (hpoint i)
    dsimp only [n,V,μ,f]
    push_cast
    exact hh
  have hγ (i) : |γ i| ≤ |q i| * D i := by
    have hh := physicalModelPhase_rounded_firstDerivative_residual hσ.le (hF i)
      hT hM (hA i) (hW i) (hx₀ i) (hx₁ i) (hr' i) (hq' i) (hdet' i)
      (hbase i) (hpoint i)
    have hD := second_condition_taylor_source_scale (C₂ :=
      TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)
      (C₃ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)
      (n := |(n i:ℝ)|) hM.ne' hN.ne' hR.ne' hscale
    change _ = D i at hD
    rw [← hD]
    dsimp only [γ,n,d₀,d₁,f,q]
    push_cast
    exact hh
  have hfirst' : |(s 0:ℝ)/r 0-(s 1:ℝ)/r 1| ≤ η*|U| := by
    rwa [abs_sub_comm]
  have hθ : |θ 1| ≤ 1/2 := abs_sub_round ((r 1:ℝ)*d₀ 1)
  have hbound := farey_base_coincidence_difference_bound (hμ 0) (hμ 1)
    (hr' 0) (hr' 1) hU hthird hε hfirst hη hfirst' hsecond hfourth hθ
    (hG 0) (hG 1) (hγ 0) (hγ 1)
  exact hbound

                                                                
                                                                    
theorem short_block_taylor_budget {C₂ C₃ n M N R : ℝ}
    (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hn : 0 ≤ n)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hnN : n ≤ N) (hNR : N ≤ R^2) (hcube : N^3 ≤ M*R^2) :
    C₂*n/(2*N*R^2)+5*C₃*n^3/(12*M*N*R^2) ≤ (C₂/2+5*C₃/12)/N := by
  have hnR : n ≤ R^2 := hnN.trans hNR
  have hn3 : n^3 ≤ M*R^2 := (pow_le_pow_left₀ hn hnN 3).trans hcube
  have h1 : C₂*n/(2*N*R^2) ≤ (C₂/2)/N := by
    apply (div_le_iff₀ (by positivity : 0 < 2*N*R^2)).mpr
    rw [show (C₂/2/N)*(2*N*R^2)=C₂*R^2 by field_simp]
    exact mul_le_mul_of_nonneg_left hnR hC₂
  have h2 : 5*C₃*n^3/(12*M*N*R^2) ≤ (5*C₃/12)/N := by
    apply (div_le_iff₀ (by positivity : 0 < 12*M*N*R^2)).mpr
    rw [show (5*C₃/12/N)*(12*M*N*R^2)=5*C₃*(M*R^2) by field_simp]
    exact mul_le_mul_of_nonneg_left hn3 (by positivity)
  rw [add_div]
  exact add_le_add h1 h2

                                                                 
                                                                           
theorem short_block_coordinate_budget {C₂ C₃ κ n M N R Q L : ℝ}
    (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hκ : 0 < κ) (hn : 0 ≤ n)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hQ : 0 ≤ Q)
    (hnN : n ≤ N) (hNR : N ≤ R^2) (hcube : N^3 ≤ M*R^2)
    (hLQ : L ≤ Q/R^2) :
    L*(C₂/κ+C₃*n^2/(2*κ*M)) ≤ (C₂/κ+C₃/(2*κ))*Q/N := by
  have hN2 : n^2 ≤ N^2 := pow_le_pow_left₀ hn hnN 2
  have hNn2 : N*n^2 ≤ M*R^2 := by
    have hh := mul_le_mul_of_nonneg_left hN2 hN.le
    nlinarith only [hh,hcube]
  have h1 : L*(C₂/κ) ≤ (C₂/κ)*Q/N := by
    calc
      _ ≤ (Q/R^2)*(C₂/κ) := mul_le_mul_of_nonneg_right hLQ (by positivity)
      _ ≤ (Q/N)*(C₂/κ) := by gcongr
      _ = _ := by ring
  have h2 : L*(C₃*n^2/(2*κ*M)) ≤ (C₃/(2*κ))*Q/N := by
    calc
      _ ≤ (Q/R^2)*(C₃*n^2/(2*κ*M)) := mul_le_mul_of_nonneg_right hLQ (by positivity)
      _ ≤ _ := by
        apply (mul_le_mul_iff_of_pos_right (show 0 < 2*κ*M*N*R^2 by positivity)).mp
        field_simp
        nlinarith only [mul_le_mul_of_nonneg_left hNn2 (show 0 ≤ Q*C₃ by positivity)]
  rw [mul_add]
  exact (add_le_add h1 h2).trans_eq (by ring)



                                                                 
                                                      
theorem short_block_phase_budget {C₂ C₃ κ n M N R Q L G : ℝ}
    (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hκ : 0 < κ) (hn : 0 ≤ n)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hQ : 0 ≤ Q) (hL : 0 ≤ L)
    (hnN : n ≤ N) (hNR : N ≤ R^2) (hRN : R ≤ N) (hcube : N^3 ≤ M*R^2)
    (hLQ : L ≤ Q/R^2)
    (hG : |G| ≤ n+(C₂/κ+C₃*n^2/(2*κ*M))) :
    (R^2/N^2)*L*|G| ≤ (1+C₂/κ+C₃/(2*κ))*Q/N := by
  let V := C₂/κ+C₃*n^2/(2*κ*M)
  let K := C₂/κ+C₃/(2*κ)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hc : L*V ≤ K*Q/N := short_block_coordinate_budget hC₂ hC₃ hκ hn
    hM hN hR hQ hnN hNR hcube hLQ
  have hfrac : R^2/N^2 ≤ 1 := (div_le_one (by positivity : 0 < N^2)).mpr
    (pow_le_pow_left₀ hR.le hRN 2)
  have hmain : (R^2/N^2)*L*n ≤ Q/N := by
    calc
      _ ≤ (R^2/N^2)*(Q/R^2)*n := by gcongr
      _ = Q*n/N^2 := by field_simp
      _ ≤ Q/N := by
        apply (div_le_iff₀ (by positivity : 0 < N^2)).mpr
        rw [show Q/N*N^2=Q*N by field_simp]
        exact mul_le_mul_of_nonneg_left hnN hQ
  have herr : (R^2/N^2)*(L*V) ≤ K*Q/N := by
    calc
      _ ≤ L*V := by simpa using mul_le_mul_of_nonneg_right hfrac (mul_nonneg hL hV)
      _ ≤ _ := hc
  have hscaled := mul_le_mul_of_nonneg_left hG
    (show 0 ≤ (R^2/N^2)*L by positivity)
  change (R^2/N^2)*L*|G| ≤ (R^2/N^2)*L*(n+V) at hscaled
  have hh : (R^2/N^2)*L*|G| ≤ Q/N+K*Q/N := by
    nlinarith only [hscaled,hmain,herr]
  exact hh.trans_eq (by dsimp [K]; ring)



                                                                   
                                                                     
                                                
theorem short_block_fourth_budget
    {C₂ C₃ κ M N R Q K n n₁ r r₁ t q q₁ G : ℝ}
    (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hκ : 0 < κ)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (hn : 0 ≤ n) (hn₁ : 0 ≤ n₁) (hnN : n ≤ N) (hn₁N : n₁ ≤ N)
    (hr : 0 < r) (ht : 0 ≤ t)
    (hq : 0 ≤ q) (hq₁ : 0 ≤ q₁) (hqQ : q ≤ Q) (hq₁Q : q₁ ≤ Q)
    (hNR : N ≤ R^2) (hRN : R ≤ N) (hcube : N^3 ≤ M*R^2)
    (hminr : R^2/N ≤ r) (hgeom : t/r ≤ Q/R^2) (hgeom₁ : t/r₁ ≤ Q/R^2)
    (hG : |G| ≤ n+(C₂/κ+C₃*n^2/(2*κ*M))) :
    let D := fun z => C₂*z/(2*N*R^2)+5*C₃*z^3/(12*M*N*R^2)
    let V := fun z => C₂/κ+C₃*z^2/(2*κ*M)
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    (K*R^2/(r*N))*t+(16*K*R^2/N^2)*|G/r| * t+
      (K*r/N)*(q/r)+(K*R^2/(2*N^2))*(q/r)+
      q*D n+q₁*D n₁+V n*(t/r)+V n₁*(t/r₁) ≤
        (37*K/2+16*K*Cc+2*Ct+2*Cc)*Q/N := by
  let D := fun z => C₂*z/(2*N*R^2)+5*C₃*z^3/(12*M*N*R^2)
  let V := fun z => C₂/κ+C₃*z^2/(2*κ*M)
  let Ct := C₂/2+5*C₃/12
  let Cc := C₂/κ+C₃/(2*κ)
  have hCt : 0 ≤ Ct := by dsimp [Ct]; positivity
  have hCc : 0 ≤ Cc := by dsimp [Cc]; positivity
  have hD := short_block_taylor_budget hC₂ hC₃ hn hM hN hR hnN hNR hcube
  have hD₁ := short_block_taylor_budget hC₂ hC₃ hn₁ hM hN hR hn₁N hNR hcube
  change D n ≤ Ct/N at hD
  change D n₁ ≤ Ct/N at hD₁
  have h1 : (K*R^2/(r*N))*t ≤ K*Q/N := by
    have hh := mul_le_mul_of_nonneg_left hgeom (show 0 ≤ K*R^2/N by positivity)
    convert hh using 1 <;> field_simp
  have h2 : (16*K*R^2/N^2)*|G/r| * t ≤ 16*K*(1+Cc)*Q/N := by
    have hh := short_block_phase_budget hC₂ hC₃ hκ hn hM hN hR hQ
      (show 0 ≤ t/r by positivity) hnN hNR hRN hcube hgeom hG
    have hscaled := mul_le_mul_of_nonneg_left hh (show 0 ≤ 16*K by positivity)
    rw [abs_div,abs_of_pos hr]
    convert hscaled using 1 <;> ring
  have h3 : (K*r/N)*(q/r) ≤ K*Q/N := by
    rw [show (K*r/N)*(q/r)=K*q/N by field_simp]
    gcongr
  have h4 : (K*R^2/(2*N^2))*(q/r) ≤ (K/2)*Q/N := by
    have hRr : R^2 ≤ r*N := (div_le_iff₀ hN).mp hminr
    have hqprod : R^2*q ≤ r*N*Q :=
      (mul_le_mul_of_nonneg_right hRr hq).trans
        (mul_le_mul_of_nonneg_left hqQ (by positivity))
    apply (mul_le_mul_iff_of_pos_right (show 0 < 2*N^2*r by positivity)).mp
    field_simp
    nlinarith only [mul_le_mul_of_nonneg_left hqprod hK]
  have h5 : q*D n ≤ Ct*Q/N := by
    calc
      _ ≤ q*(Ct/N) := mul_le_mul_of_nonneg_left hD hq
      _ ≤ Q*(Ct/N) := mul_le_mul_of_nonneg_right hqQ (by positivity)
      _ = _ := by ring
  have h6 : q₁*D n₁ ≤ Ct*Q/N := by
    calc
      _ ≤ q₁*(Ct/N) := mul_le_mul_of_nonneg_left hD₁ hq₁
      _ ≤ Q*(Ct/N) := mul_le_mul_of_nonneg_right hq₁Q (by positivity)
      _ = _ := by ring
  have h7 : V n*(t/r) ≤ Cc*Q/N := by
    rw [mul_comm]
    exact short_block_coordinate_budget hC₂ hC₃ hκ hn hM hN hR hQ hnN hNR hcube hgeom
  have h8 : V n₁*(t/r₁) ≤ Cc*Q/N := by
    rw [mul_comm]
    exact short_block_coordinate_budget hC₂ hC₃ hκ hn₁ hM hN hR hQ hn₁N hNR hcube hgeom₁
  change _ ≤ (37*K/2+16*K*Cc+2*Ct+2*Cc)*Q/N
  change (K*R^2/(r*N))*t+(16*K*R^2/N^2)*|G/r| * t+
      (K*r/N)*(q/r)+(K*R^2/(2*N^2))*(q/r)+
      q*D n+q₁*D n₁+V n*(t/r)+V n₁*(t/r₁) ≤ _
  exact (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add (add_le_add h1 h2) h3) h4) h5) h6) h7) h8).trans_eq (by ring)



                                                                         
                                                                         
                                                                           
theorem physicalModelPhase_halfCurvature_lipschitz
    {σ δ T M A W x y : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx : x ∈ Set.Ioo 0 W) (hy : y ∈ Set.Ioo 0 W) :
    let f := heathBrownPhysicalPhase F T M A 1
    |iteratedDeriv 2 f y/2-iteratedDeriv 2 f x/2| ≤
      (σ*(σ+1)+1)*T/(2*M^3)*|y-x| := by
  let f := heathBrownPhysicalPhase F T M A 1
  let C := σ*(σ+1)+1
  have hκ := modelPhaseThirdLower_pos hσ
  have hseg (z : ℝ) (hz : z ∈ Set.uIcc x y) : z ∈ Set.Ioo 0 W := by
    rcases Set.mem_uIcc.mp hz with hz | hz
    · exact ⟨hx.1.trans_le hz.1,hz.2.trans_lt hy.2⟩
    · exact ⟨hy.1.trans_le hz.1,hz.2.trans_lt hx.2⟩
  have hd (z : ℝ) (hz : z ∈ Set.uIcc x y) :
      HasDerivAt (fun w => iteratedDeriv 2 f w/2) (iteratedDeriv 3 f z/2) z := by
    have hcf := heathBrownPhysicalPhase_contDiffOn hF.1 hM hA hW T 1
    have hf3 : ContDiffAt ℝ 3 f z :=
      ((hcf z (Set.Ioo_subset_Icc_self (hseg z hz))).contDiffAt
        (Filter.mem_of_superset (isOpen_Ioo.mem_nhds (hseg z hz)) Set.Ioo_subset_Icc_self)).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
    exact (hasDerivAt_iteratedDeriv_finite (by norm_num : 2 < 3) hf3).div_const 2
  have hb (z : ℝ) (hz : z ∈ Set.uIcc x y) : |iteratedDeriv 3 f z/2| ≤ C*T/(2*M^3) := by
    have hh := physicalModelPhase_cubicCoefficient_bounds hσ hδ hF hT hM hA hW (hseg z hz)
    change modelPhaseThirdLower σ*T/(6*M^3) ≤ iteratedDeriv 3 f z/6 ∧
      iteratedDeriv 3 f z/6 ≤ C*T/(6*M^3) at hh
    have hlo : 0 ≤ iteratedDeriv 3 f z/2 := by
      have hpos : 0 ≤ modelPhaseThirdLower σ*T/(6*M^3) := by positivity
      linarith only [hh.1,hpos]
    rw [abs_of_nonneg hlo]
    calc
      _ = 3*(iteratedDeriv 3 f z/6) := by ring
      _ ≤ 3*(C*T/(6*M^3)) := mul_le_mul_of_nonneg_left hh.2 (by norm_num)
      _ = _ := by ring
  have he := (convex_uIcc x y).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (hd z hz).hasDerivWithinAt)
    (C := C*T/(2*M^3))
    (fun z hz => by simpa only [Real.norm_eq_abs] using hb z hz)
    Set.left_mem_uIcc Set.right_mem_uIcc
  exact he



                                                             
                                                                   
theorem physicalModelPhase_quartic_cubicCoefficient_remainder
    {σ δ T M A W a b : ℝ} {F : ℝ → ℝ} (hσ : 0 ≤ σ)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (ha : a ∈ Set.Ioo 0 W) (hb : b ∈ Set.Ioo 0 W) :
    let f := heathBrownPhysicalPhase F T M A 1
    |iteratedDeriv 3 f b/6-iteratedDeriv 3 f a/6-
      4*(iteratedDeriv 4 f a/24)*(b-a)| ≤
      T*(modelPhaseJetCoefficient σ 4+δ)*|b-a|^2/(12*M^5) := by
  let f := heathBrownPhysicalPhase F T M A 1
  have hseg (y : ℝ) (hy : y ∈ Set.uIcc a b) : y ∈ Set.Ioo 0 W := by
    rcases Set.mem_uIcc.mp hy with hy | hy
    · exact ⟨ha.1.trans_le hy.1,hy.2.trans_lt hb.2⟩
    · exact ⟨hb.1.trans_le hy.1,hy.2.trans_lt ha.2⟩
  have hc (y : ℝ) (hy : y ∈ Set.uIcc a b) : ContDiffAt ℝ 5 f y := by
    have hcf := heathBrownPhysicalPhase_contDiffOn hF.1 hM hA hW T 1
    exact ((hcf y (Set.Ioo_subset_Icc_self (hseg y hy))).contDiffAt
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds (hseg y hy)) Set.Ioo_subset_Icc_self)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 5)
  have hf5 (y : ℝ) (hy : y ∈ Set.uIcc a b) :
      |iteratedDeriv 5 f y| ≤ T/M^5*(modelPhaseJetCoefficient σ 4+δ) := by
    have hyp := heathBrownPhysicalPoint_mem_interior hM hA hW (hseg y hy)
    have he := approximateModelPhase_iteratedDeriv_error hF hyp 4 le_rfl
    have hm := iteratedDeriv_modelPhase_abs_le hσ hyp 4
    have htri := abs_add_le (iteratedDeriv 5 F ((A+y)/M)-iteratedDeriv 4 (Expdb.modelPhase σ) ((A+y)/M))
      (iteratedDeriv 4 (Expdb.modelPhase σ) ((A+y)/M))
    rw [sub_add_cancel] at htri
    have hu : |iteratedDeriv 5 F ((A+y)/M)| ≤ modelPhaseJetCoefficient σ 4+δ := by
      linarith only [he,hm,htri]
    dsimp only [f]
    rw [heathBrownPhysicalPhase_iteratedDeriv hF.1 hM hA hW (hseg y hy),
      one_mul,abs_mul,abs_of_pos (by positivity : 0 < T/M^5)]
    exact mul_le_mul_of_nonneg_left hu (by positivity)
  have hg (y : ℝ) (hy : y ∈ Set.uIcc a b) : ContDiffAt ℝ 2 (iteratedDeriv 3 f) y :=
    contDiffAt_iteratedDeriv_finite (n := 2) (j := 3) (hc y hy)
  have hgg (y : ℝ) (hy : y ∈ Set.uIcc a b) :
      |iteratedDeriv 2 (iteratedDeriv 3 f) y| ≤ T/M^5*(modelPhaseJetCoefficient σ 4+δ) := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hf5 y hy
  have he := abs_finiteTaylorPolynomial_remainder_le_finite 1 hg hgg
  have hpoly : finiteTaylorPolynomial (iteratedDeriv 3 f) 1 a b =
      iteratedDeriv 3 f a+iteratedDeriv 4 f a*(b-a) := by
    simp [finiteTaylorPolynomial,taylor_within_apply,iteratedDeriv_succ]
    ring
  rw [hpoly] at he
  norm_num only [Nat.reduceAdd,Nat.factorial,Nat.cast_ofNat] at he
  have hid : iteratedDeriv 3 f b/6-iteratedDeriv 3 f a/6-
      4*(iteratedDeriv 4 f a/24)*(b-a) =
      (iteratedDeriv 3 f b-(iteratedDeriv 3 f a+iteratedDeriv 4 f a*(b-a)))/6 := by ring
  change |iteratedDeriv 3 f b/6-iteratedDeriv 3 f a/6-
    4*(iteratedDeriv 4 f a/24)*(b-a)| ≤ _
  rw [hid,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 6)]
  exact (div_le_div_of_nonneg_right he (by norm_num : (0:ℝ) ≤ 6)).trans_eq (by ring)

open Filter
open scoped Topology

                                                          
                                                              
noncomputable def quarticBranch (μ ν r s x : ℝ) : ℝ :=
  4*ν/(27*μ^3*r^3*(r*x+s)^2)

theorem quarticBranch_hasDerivAt {μ ν r s x : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hx : r*x+s ≠ 0) :
    HasDerivAt (quarticBranch μ ν r s) (-8*ν/(27*μ^3*r^2*(r*x+s)^3)) x := by
  have hd := ((((hasDerivAt_id x).const_mul r).add_const s).pow 2).inv
    (pow_ne_zero 2 hx)
  convert hd.const_mul (4*ν/(27*μ^3*r^3)) using 1
  · ext y
    change 4*ν/(27*μ^3*r^3*(r*y+s)^2) =
      (4*ν/(27*μ^3*r^3))*((r*y+s)^2)⁻¹
    rw [div_mul_eq_div_div,div_eq_mul_inv]
  · dsimp
    field_simp
    ring

theorem quarticBranch_second {μ ν r s x : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hx : r*x+s ≠ 0) :
    iteratedDeriv 2 (quarticBranch μ ν r s) x =
      8*ν/(9*μ^3*r*(r*x+s)^4) := by
  have hd := ((((hasDerivAt_id x).const_mul r).add_const s).pow 3).inv
    (pow_ne_zero 3 hx)
  have hformula : HasDerivAt
      (fun y : ℝ => -8*ν/(27*μ^3*r^2*(r*y+s)^3))
      (8*ν/(9*μ^3*r*(r*x+s)^4)) x := by
    convert hd.const_mul (-8*ν/(27*μ^3*r^2)) using 1
    · ext y
      rw [div_mul_eq_div_div,div_eq_mul_inv]
      rfl
    · dsimp
      field_simp
      ring
  have hnear : ∀ᶠ y in 𝓝 x, r*y+s ≠ 0 :=
    (show ContinuousAt (fun y : ℝ => r*y+s) x by fun_prop).eventually_ne hx
  have heq : deriv (quarticBranch μ ν r s) =ᶠ[𝓝 x]
      (fun y : ℝ => -8*ν/(27*μ^3*r^2*(r*y+s)^3)) := by
    filter_upwards [hnear] with y hy
    exact (quarticBranch_hasDerivAt hμ hr hy).deriv
  simpa only [iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using
    (hformula.congr_of_eventuallyEq heq).deriv

                                                                   
noncomputable def quarticPhase (μ ν r s μ₁ ν₁ r₁ s₁ x : ℝ) : ℝ :=
  quarticBranch μ ν r s x-quarticBranch μ₁ ν₁ r₁ s₁ x

theorem quarticPhase_second {μ ν r s μ₁ ν₁ r₁ s₁ x : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr₁ : r₁ ≠ 0)
    (hx : r*x+s ≠ 0) (hx₁ : r₁*x+s₁ ≠ 0) :
    iteratedDeriv 2 (quarticPhase μ ν r s μ₁ ν₁ r₁ s₁) x =
      8*ν/(9*μ^3*r*(r*x+s)^4)-8*ν₁/(9*μ₁^3*r₁*(r₁*x+s₁)^4) := by
  have ha : ContDiffAt ℝ 2 (quarticBranch μ ν r s) x := by
    exact contDiffAt_const.div (by fun_prop) (by positivity)
  have hb : ContDiffAt ℝ 2 (quarticBranch μ₁ ν₁ r₁ s₁) x := by
    exact contDiffAt_const.div (by fun_prop) (by positivity)
  unfold quarticPhase
  rw [iteratedDeriv_fun_sub ha hb,
    quarticBranch_second hμ hr hx,quarticBranch_second hμ₁ hr₁ hx₁]

                                                                           
theorem physicalModelPhase_quartic_cubic_ratio_bound
    {σ δ T M A W z : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hz : z ∈ Set.Ioo 0 W) :
    let f := heathBrownPhysicalPhase F T M A 1
    let μ := iteratedDeriv 3 f z/6
    let ν := iteratedDeriv 4 f z/24
    |2*ν/μ| ≤ (modelPhaseJetCoefficient σ 3+δ)/(2*modelPhaseThirdLower σ*M) := by
  let f := heathBrownPhysicalPhase F T M A 1
  let μ := iteratedDeriv 3 f z/6
  let κ := modelPhaseThirdLower σ
  let C₃ := modelPhaseJetCoefficient σ 3+δ
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hlo : κ*T/(6*M^3) ≤ μ :=
    (physicalModelPhase_cubicCoefficient_bounds hσ hδ
      (approximateModelPhase_mono hF (by norm_num : 2 ≤ 3) le_rfl)
      hT hM hA hW hz).1
  have hμ : 0 < μ := lt_of_lt_of_le (by positivity) hlo
  have hyp := heathBrownPhysicalPoint_mem_interior hM hA hW hz
  have he := approximateModelPhase_iteratedDeriv_error hF hyp 3 le_rfl
  have hm := iteratedDeriv_modelPhase_abs_le hσ.le hyp 3
  have htri := abs_add_le
    (iteratedDeriv 4 F ((A+z)/M)-iteratedDeriv 3 (Expdb.modelPhase σ) ((A+z)/M))
    (iteratedDeriv 3 (Expdb.modelPhase σ) ((A+z)/M))
  rw [sub_add_cancel] at htri
  have hu : |iteratedDeriv 4 F ((A+z)/M)| ≤ C₃ := by
    dsimp only [C₃]
    linarith only [he,hm,htri]
  have hC : 0 ≤ C₃ := (abs_nonneg _).trans hu
  have hfour : |iteratedDeriv 4 f z| ≤ T/M^4*C₃ := by
    dsimp only [f]
    rw [heathBrownPhysicalPhase_iteratedDeriv hF.1 hM hA hW hz,one_mul,
      abs_mul,abs_of_pos (by positivity : 0 < T/M^4)]
    exact mul_le_mul_of_nonneg_left hu (by positivity)
  change |2*(iteratedDeriv 4 f z/24)/μ| ≤ C₃/(2*κ*M)
  calc
    _ = |iteratedDeriv 4 f z|/(12*μ) := by
      rw [abs_div,abs_mul,abs_div,abs_of_pos hμ]
      norm_num
      ring
    _ ≤ (T/M^4*C₃)/(12*μ) :=
      div_le_div_of_nonneg_right hfour (by positivity)
    _ ≤ (T/M^4*C₃)/(12*(κ*T/(6*M^3))) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hlo (by norm_num))
    _ = _ := by field_simp; ring

                                                                         
                                                                            
theorem quartic_corrected_nonlinear_residual_identity
    {μ ν r s u t n δ E : ℝ} (hμ : μ ≠ 0) (hr : r ≠ 0)
    (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) :
    let q := r*u+s*t
    let G := minorArcCoordinate μ r s (u/t)
    let γ := q*(E+2*δ*n+3*μ*n^2+4*ν*n^3-n*t/(r*q))
    γ-n*t/r-t/r*(2*δ/(3*μ)-G)-t*quarticBranch μ ν r s (u/t) =
      q*(E+(n-G)*(3*μ*(n-G)+2*δ)+4*ν*(n^3-G^3)) := by
  have hG : minorArcCoordinate μ r s (u/t) = t/(3*μ*r*(r*u+s*t)) := by
    dsimp [minorArcCoordinate]
    have hden : r*(u/t)+s=(r*u+s*t)/t := by field_simp
    rw [hden]
    field_simp
  have hH : t*quarticBranch μ ν r s (u/t) =
      (r*u+s*t)*4*ν*(minorArcCoordinate μ r s (u/t))^3 := by
    rw [hG]
    dsimp [quarticBranch]
    field_simp
    ring
  dsimp only
  rw [hH,hG]
  field_simp
  ring

                                                                   
                                                                         
theorem firstDerivative_quartic_corrected_nonlinear_residual_bound
    {f : ℝ → ℝ} {a b U e r s u t : ℝ}
    (hf : ∀ y ∈ Set.uIcc a b, ContDiffAt ℝ 5 f y)
    (hfifth : ∀ y ∈ Set.uIcc a b, |iteratedDeriv 5 f y| ≤ U)
    (hμ : iteratedDeriv 3 f a/6 ≠ 0) (hr : r ≠ 0)
    (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) :
    let n := b-a
    let μ := iteratedDeriv 3 f a/6
    let ν := iteratedDeriv 4 f a/24
    let δ := iteratedDeriv 2 f a/2-e/r
    let q := r*u+s*t
    let G := minorArcCoordinate μ r s (u/t)
    let γ := q*(iteratedDeriv 1 f b-iteratedDeriv 1 f a-2*e*n/r-n*t/(r*q))
    |γ-n*t/r-t/r*(2*δ/(3*μ)-G)-t*quarticBranch μ ν r s (u/t)| ≤
      |q| * (U*|n|^4/24+|n-G| * (3*|μ| * |n-G|+2*|δ|)+
        4*|ν| * |n^3-G^3|) := by
  let n := b-a
  let μ := iteratedDeriv 3 f a/6
  let ν := iteratedDeriv 4 f a/24
  let δ := iteratedDeriv 2 f a/2-e/r
  let q := r*u+s*t
  let G := minorArcCoordinate μ r s (u/t)
  let E := iteratedDeriv 1 f b-
    (iteratedDeriv 1 f a+iteratedDeriv 2 f a*n+3*μ*n^2+4*ν*n^3)
  have hg (y : ℝ) (hy : y ∈ Set.uIcc a b) : ContDiffAt ℝ 4 (iteratedDeriv 1 f) y :=
    contDiffAt_iteratedDeriv_finite (n := 4) (j := 1) (hf y hy)
  have hgg (y : ℝ) (hy : y ∈ Set.uIcc a b) :
      |iteratedDeriv 4 (iteratedDeriv 1 f) y| ≤ U := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hfifth y hy
  have hE : |E| ≤ U*|n|^4/24 := by
    have he := abs_finiteTaylorPolynomial_remainder_le_finite 3 hg hgg
    have hpoly : finiteTaylorPolynomial (iteratedDeriv 1 f) 3 a b =
        iteratedDeriv 1 f a+iteratedDeriv 2 f a*n+3*μ*n^2+4*ν*n^3 := by
      dsimp [n,μ,ν]
      simp [finiteTaylorPolynomial,taylor_within_apply,iteratedDeriv_succ]
      ring
    rw [hpoly] at he
    norm_num only [Nat.reduceAdd,Nat.factorial,Nat.cast_ofNat] at he
    exact he
  have hid : q*(iteratedDeriv 1 f b-iteratedDeriv 1 f a-2*e*n/r-n*t/(r*q)) =
      q*(E+2*δ*n+3*μ*n^2+4*ν*n^3-n*t/(r*q)) := by dsimp [E,δ]; ring
  have hc := quartic_corrected_nonlinear_residual_identity
    hμ hr ht hq (ν := ν) (n := n) (δ := δ) (E := E)
  change |q*(iteratedDeriv 1 f b-iteratedDeriv 1 f a-2*e*n/r-n*t/(r*q))-
    n*t/r-t/r*(2*δ/(3*μ)-G)-t*quarticBranch μ ν r s (u/t)| ≤ _
  rw [hid,hc,abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg q)
  calc
    _ ≤ |E+(n-G)*(3*μ*(n-G)+2*δ)|+|4*ν*(n^3-G^3)| := abs_add_le _ _
    _ ≤ (|E|+|(n-G)*(3*μ*(n-G)+2*δ)|)+|4*ν*(n^3-G^3)| :=
      add_le_add_left (abs_add_le _ _) _
    _ ≤ (U*|n|^4/24+|n-G| * (3*|μ| * |n-G|+2*|δ|))+4*|ν| * |n^3-G^3| := by
      simp only [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 4)]
      apply add_le_add _ le_rfl
      apply add_le_add hE
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg (n-G))
      apply (abs_add_le _ _).trans
      simp only [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 3),
        abs_of_pos (by norm_num : (0:ℝ) < 2)]
      exact le_rfl


                                                                    
                                     
theorem coordinate_cube_difference_bound {n G D : ℝ} (hn : |n-G| ≤ D) :
    |n^3-G^3| ≤ D*(3*|n|^2+3*|n| * D+D^2) := by
  have hD : 0 ≤ D := (abs_nonneg _).trans hn
  have hG : |G| ≤ |n|+D := by
    calc
      _ = |n-(n-G)| := by ring_nf
      _ ≤ |n|+|n-G| := abs_sub _ _
      _ ≤ _ := add_le_add_right hn _
  calc
    _ = |n-G| * |n^2+n*G+G^2| := by rw [← abs_mul]; congr 1; ring
    _ ≤ D*(|n|^2+|n| * |G|+|G|^2) := by
      apply mul_le_mul hn _ (abs_nonneg _) hD
      calc
        _ ≤ |n^2+n*G|+|G^2| := abs_add_le _ _
        _ ≤ |n^2|+|n*G|+|G^2| := add_le_add_left (abs_add_le _ _) _
        _ = _ := by rw [abs_mul,abs_pow,abs_pow]
    _ ≤ D*(|n|^2+|n| * (|n|+D)+(|n|+D)^2) := by gcongr
    _ = _ := by ring

                                                                   
                                                                       
theorem physicalModelPhase_quartic_nonlinear_residual_bound
    {σ δ T M A W x₀ x₁ e r v s u t : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx₀ : x₀ ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hx₁ : x₁ ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1) :
    let f := heathBrownPhysicalPhase F T M A 1
    let a : ℝ := round x₀
    let b : ℝ := round x₁
    let n := b-a
    let μ := iteratedDeriv 3 f a/6
    let ν := iteratedDeriv 4 f a/24
    let δ₀ := iteratedDeriv 2 f a/2-e/r
    let q := r*u+s*t
    let G := minorArcCoordinate μ r s (u/t)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let C₄ := modelPhaseJetCoefficient σ 4+δ
    let κ := modelPhaseThirdLower σ
    let D := C₂/κ+C₃*|n|^2/(2*κ*M)
    let γ := q*(iteratedDeriv 1 f b-iteratedDeriv 1 f a-2*e*n/r-n*t/(r*q))
    iteratedDeriv 2 f x₀/2=e/r →
    iteratedDeriv 2 f x₁/2=(e*u+v*t)/q →
    |γ-n*t/r-t/r*(2*δ₀/(3*μ)-G)-t*quarticBranch μ ν r s (u/t)| ≤
      |q| * (T/M^3) * (C₄*|n|^4/(24*M^2)+C₂/2*D*(D+1)+
        C₃/(6*M)*D*(3*|n|^2+3*|n| * D+D^2)) := by
  let f := heathBrownPhysicalPhase F T M A 1
  let a : ℝ := round x₀
  let b : ℝ := round x₁
  let n := b-a
  let μ := iteratedDeriv 3 f a/6
  let ν := iteratedDeriv 4 f a/24
  let δ₀ := iteratedDeriv 2 f a/2-e/r
  let q := r*u+s*t
  let G := minorArcCoordinate μ r s (u/t)
  let C₂ := modelPhaseJetCoefficient σ 2+δ
  let C₃ := modelPhaseJetCoefficient σ 3+δ
  let C₄ := modelPhaseJetCoefficient σ 4+δ
  let κ := modelPhaseThirdLower σ
  let D := C₂/κ+C₃*|n|^2/(2*κ*M)
  change _ → _ → _
  intro hbase hpoint
  have hF₂ := approximateModelPhase_mono hF (by norm_num : 2 ≤ 4) le_rfl
  have hF₃ := approximateModelPhase_mono hF (by norm_num : 3 ≤ 4) le_rfl
  have hround₀ := physicalModelPhase_halfCurvature_round_error hσ.le hF₂ hT hM hA hW hx₀
  have hround₁ := physicalModelPhase_halfCurvature_round_error hσ.le hF₂ hT hM hA hW hx₁
  have hcoord : |n-G| ≤ D := physicalModelPhase_rounded_minorArcCoordinate_entry
    hσ hδ hF₃ hT hM hA hW hx₀ hx₁ hr ht hq hdet hbase hpoint
  have hD : 0 ≤ D := (abs_nonneg _).trans hcoord
  have hδ₀ : |δ₀| ≤ T*C₂/(4*M^3) := by simpa only [hbase] using hround₀.2
  have hμ : μ ≠ 0 := by
    have hv := physicalModelPhase_cubicCoefficient_relative_variation hσ hδ hF₃ hT.ne' hM hA hW
      hround₀.1 hround₀.1
    change |μ/μ-1| ≤ _ at hv
    intro hz
    rw [hz,div_zero] at hv
    norm_num at hv
  have hseg (y : ℝ) (hy : y ∈ Set.uIcc a b) : y ∈ Set.Ioo 0 W := by
    rcases Set.mem_uIcc.mp hy with hy | hy
    · exact ⟨hround₀.1.1.trans_le hy.1,hy.2.trans_lt hround₁.1.2⟩
    · exact ⟨hround₁.1.1.trans_le hy.1,hy.2.trans_lt hround₀.1.2⟩
  have hc (y : ℝ) (hy : y ∈ Set.uIcc a b) : ContDiffAt ℝ 5 f y := by
    have hcf := heathBrownPhysicalPhase_contDiffOn hF.1 hM hA hW T 1
    exact ((hcf y (Set.Ioo_subset_Icc_self (hseg y hy))).contDiffAt
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds (hseg y hy)) Set.Ioo_subset_Icc_self)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 5)
  have hjet (p : ℕ) (hp : p ≤ 4) (y : ℝ) (hy : y ∈ Set.Ioo 0 W) :
      |iteratedDeriv (p+1) f y| ≤ T/M^(p+1)*(modelPhaseJetCoefficient σ p+δ) := by
    have hyp := heathBrownPhysicalPoint_mem_interior hM hA hW hy
    have he := approximateModelPhase_iteratedDeriv_error hF hyp p hp
    have hm := iteratedDeriv_modelPhase_abs_le hσ.le hyp p
    have htri := abs_add_le (iteratedDeriv (p+1) F ((A+y)/M)-iteratedDeriv p (Expdb.modelPhase σ) ((A+y)/M))
      (iteratedDeriv p (Expdb.modelPhase σ) ((A+y)/M))
    rw [sub_add_cancel] at htri
    have hu : |iteratedDeriv (p+1) F ((A+y)/M)| ≤ modelPhaseJetCoefficient σ p+δ := by
      linarith only [he,hm,htri]
    dsimp only [f]
    rw [heathBrownPhysicalPhase_iteratedDeriv hF.1 hM hA hW hy,
      one_mul,abs_mul,abs_of_pos (by positivity : 0 < T/M^(p+1))]
    exact mul_le_mul_of_nonneg_left hu (by positivity)
  have hμhi : |μ| ≤ T/M^3*C₂/6 := by
    dsimp only [μ]
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ) < 6)]
    exact div_le_div_of_nonneg_right (hjet 2 (by norm_num) a hround₀.1) (by norm_num)
  have hνhi : |ν| ≤ T/M^4*C₃/24 := by
    dsimp only [ν]
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ) < 24)]
    exact div_le_div_of_nonneg_right (hjet 3 (by norm_num) a hround₀.1) (by norm_num)
  have he := firstDerivative_quartic_corrected_nonlinear_residual_bound hc
    (fun y hy => hjet 4 le_rfl y (hseg y hy)) hμ hr ht hq (e := e)
  have hcubes := coordinate_cube_difference_bound hcoord
  apply he.trans
  have hC₂ : 0 ≤ C₂ := by
    have hh := (abs_nonneg _).trans (hjet 2 (by norm_num) a hround₀.1)
    exact nonneg_of_mul_nonneg_right hh (by positivity : 0 < T/M^3)
  have hC₃ : 0 ≤ C₃ := by
    have hh := (abs_nonneg _).trans (hjet 3 (by norm_num) a hround₀.1)
    exact nonneg_of_mul_nonneg_right hh (by positivity : 0 < T/M^4)
  calc
    |q| * ((T/M^5*C₄)*|n|^4/24+|n-G| * (3*|μ| * |n-G|+2*|δ₀|)+
        4*|ν| * |n^3-G^3|) ≤
        |q| * ((T/M^5*C₄)*|n|^4/24+D*(3*(T/M^3*C₂/6)*D+2*(T*C₂/(4*M^3)))+
        4*(T/M^4*C₃/24)*(D*(3*|n|^2+3*|n| * D+D^2))) := by
      gcongr
    _ = |q| * (T/M^3) * (C₄*|n|^4/(24*M^2)+C₂/2*D*(D+1)+
        C₃/(6*M)*D*(3*|n|^2+3*|n| * D+D^2)) := by ring


                                                              
                                                                           
theorem quartic_residual_source_scale_budget
    {A B C₂ C₃ C₄ n M N R T : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hC₄ : 0 ≤ C₄)
    (hn : 0 ≤ n) (hM : 0 < M) (hnM : n ≤ M) (hN : 0 < N)
    (hR : 1 ≤ R) (hRM : R ≤ M) (hT : 0 < T)
    (hscale : T*N*R^2=M^3) (hsquare : n^2 ≤ M*R) :
    let K := A+B
    let D := A+B*n^2/M
    (T/M^3)*(C₄*n^4/(24*M^2)+C₂/2*D*(D+1)+
      C₃/(6*M)*D*(3*n^2+3*n*D+D^2)) ≤
      (C₄/24+C₂/2*K*(K+1)+C₃/6*(3*K+3*K^2+K^3))/N := by
  let K := A+B
  let D := A+B*n^2/M
  have hK : 0 ≤ K := add_nonneg hA hB
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hx : n^2/M ≤ R := (div_le_iff₀ hM).mpr (by simpa only [mul_comm] using hsquare)
  have hDb : D ≤ K*R := by
    have hb := mul_le_mul_of_nonneg_left hx hB
    have ha := mul_le_mul_of_nonneg_left hR hA
    calc
      D = A+B*(n^2/M) := by dsimp [D]; ring
      _ ≤ A*R+B*R := add_le_add (by simpa only [mul_one] using ha) hb
      _ = K*R := by dsimp [K]; ring
  have hquartic : n^4/M^2 ≤ R^2 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ n^2/M) hx 2
    convert hh using 1
    ring
  have hquad : D*(D+1) ≤ K*(K+1)*R^2 := by
    calc
      _ ≤ (K*R)*(K*R+R) :=
        mul_le_mul hDb (add_le_add hDb hR) (by positivity) (by positivity)
      _ = _ := by ring
  have hcube : D*(3*n^2+3*n*D+D^2)/M ≤ (3*K+3*K^2+K^3)*R^2 := by
    have hrr : R^3/M ≤ R^2 := by
      apply (div_le_iff₀ hM).mpr
      have hh := mul_le_mul_of_nonneg_right hRM (sq_nonneg R)
      nlinarith only [hh]
    calc
      _ ≤ (K*R)*(3*(M*R)+3*M*(K*R)+(K*R)^2)/M := by gcongr
      _ = (3*K+3*K^2)*R^2+K^3*(R^3/M) := by field_simp
      _ ≤ (3*K+3*K^2)*R^2+K^3*R^2 := by
        gcongr
      _ = _ := by ring
  have htotal : C₄*n^4/(24*M^2)+C₂/2*D*(D+1)+
      C₃/(6*M)*D*(3*n^2+3*n*D+D^2) ≤
      (C₄/24+C₂/2*K*(K+1)+C₃/6*(3*K+3*K^2+K^3))*R^2 := by
    calc
      _ = C₄/24*(n^4/M^2)+C₂/2*(D*(D+1))+
          C₃/6*(D*(3*n^2+3*n*D+D^2)/M) := by ring
      _ ≤ C₄/24*R^2+C₂/2*(K*(K+1)*R^2)+
          C₃/6*((3*K+3*K^2+K^3)*R^2) := by gcongr
      _ = _ := by ring
  change (T/M^3)*(C₄*n^4/(24*M^2)+C₂/2*D*(D+1)+
      C₃/(6*M)*D*(3*n^2+3*n*D+D^2)) ≤ _
  calc
    _ ≤ (T/M^3)*((C₄/24+C₂/2*K*(K+1)+C₃/6*(3*K+3*K^2+K^3))*R^2) :=
      mul_le_mul_of_nonneg_left htotal (by positivity)
    _ = _ := by
      apply (eq_div_iff hN.ne').mpr
      rw [show (T/M^3)*((C₄/24+C₂/2*K*(K+1)+C₃/6*(3*K+3*K^2+K^3))*R^2)*N =
        (C₄/24+C₂/2*K*(K+1)+C₃/6*(3*K+3*K^2+K^3))*(T*N*R^2)/M^3 by ring,hscale]
      field_simp
      dsimp only [K]
      ring


                                                          
noncomputable def quarticNonlinearResidualConstant (σ δ : ℝ) : ℝ :=
  let C₂ := modelPhaseJetCoefficient σ 2+δ
  let C₃ := modelPhaseJetCoefficient σ 3+δ
  let C₄ := modelPhaseJetCoefficient σ 4+δ
  let κ := modelPhaseThirdLower σ
  let K := C₂/κ+C₃/(2*κ)
  C₄/24+C₂/2*K*(K+1)+C₃/6*(3*K+3*K^2+K^3)

                                                                     
                                                            
theorem physicalModelPhase_quartic_residual_le_fourth_scale
    {σ δ T M N R A W x₀ x₁ e r v s u t : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 4 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hscale : T*N*R^2=M^3) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx₀ : x₀ ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hx₁ : x₁ ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1) :
    let f := heathBrownPhysicalPhase F T M A 1
    let a : ℝ := round x₀
    let b : ℝ := round x₁
    let n := b-a
    let μ := iteratedDeriv 3 f a/6
    let ν := iteratedDeriv 4 f a/24
    let δ₀ := iteratedDeriv 2 f a/2-e/r
    let q := r*u+s*t
    let G := minorArcCoordinate μ r s (u/t)
    let γ := q*(iteratedDeriv 1 f b-iteratedDeriv 1 f a-2*e*n/r-n*t/(r*q))
    iteratedDeriv 2 f x₀/2=e/r →
    iteratedDeriv 2 f x₁/2=(e*u+v*t)/q →
    |n|^2 ≤ M*R →
    |γ-n*t/r-t/r*(2*δ₀/(3*μ)-G)-t*quarticBranch μ ν r s (u/t)| ≤ quarticNonlinearResidualConstant σ δ*|q|/N := by
  let f := heathBrownPhysicalPhase F T M A 1
  let a : ℝ := round x₀
  let b : ℝ := round x₁
  let n := b-a
  let C₂ := modelPhaseJetCoefficient σ 2+δ
  let C₃ := modelPhaseJetCoefficient σ 3+δ
  let C₄ := modelPhaseJetCoefficient σ 4+δ
  let κ := modelPhaseThirdLower σ
  have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) hM
  change _ → _ → _ → _
  intro hbase hpoint hsquare
  have hF₂ := approximateModelPhase_mono hF (by norm_num : 2 ≤ 4) le_rfl
  have hround₀ := physicalModelPhase_halfCurvature_round_error hσ.le hF₂ hT hM0 hA hW hx₀
  have hround₁ := physicalModelPhase_halfCurvature_round_error hσ.le hF₂ hT hM0 hA hW hx₁
  have hnM : |n| ≤ M := by
    have hWM : W ≤ M := by linarith only [hA,hW]
    apply abs_le.mpr
    dsimp [n,a,b]
    constructor <;> linarith only [hround₀.1.1,hround₀.1.2,hround₁.1.1,hround₁.1.2,hWM]
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans
    (approximateModelPhase_iteratedDeriv_error hF
      (heathBrownPhysicalPoint_mem_interior hM0 hA hW hround₀.1) 4 le_rfl)
  have hC₂ : 0 ≤ C₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ : 0 ≤ C₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hC₄ : 0 ≤ C₄ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ0
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hb := quartic_residual_source_scale_budget (A := C₂/κ) (B := C₃/(2*κ))
    (by positivity) (by positivity) hC₂ hC₃ hC₄ (abs_nonneg n) hM0 hnM hN hR hRM hT hscale hsquare
  have he := physicalModelPhase_quartic_nonlinear_residual_bound
    hσ hδ hF hT hM0 hA hW hx₀ hx₁ hr ht hq hdet hbase hpoint
  apply he.trans
  have hh := mul_le_mul_of_nonneg_left hb (abs_nonneg (r*u+s*t))
  convert hh using 1 <;> dsimp [quarticNonlinearResidualConstant,C₂,C₃,C₄,κ,n,a,b] <;> ring

                                                               
noncomputable def roundedMinorArcQuarticLinearForm
    (f : ℝ → ℝ) (x₀ e r s u t : ℝ) : ℝ :=
  let a : ℝ := round x₀
  roundedMinorArcLinearForm f x₀ e r s u t+
    t*quarticBranch (iteratedDeriv 3 f a/6) (iteratedDeriv 4 f a/24) r s (u/t)


                                                                             
theorem physicalModelPhase_quartic_rounded_linearization
    {σ δ T M N R A W x₀ x₁ : ℝ} {e r v s u t : ℤ} {F : ℝ → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 4 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hscale : T*N*R^2=M^3) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx₀ : x₀ ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hx₁ : x₁ ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1) :
    let f := heathBrownPhysicalPhase F T M A 1
    let a := round x₀
    let b := round x₁
    let n := b-a
    let q : ℝ := r*u+s*t
    let j := round ((r:ℝ)*iteratedDeriv 1 f a)*u+2*n*(e*u+v*t)
    iteratedDeriv 2 f x₀/2=(e:ℝ)/r →
    iteratedDeriv 2 f x₁/2=((e:ℝ)*u+v*t)/q →
    |(n:ℝ)|^2 ≤ M*R →
    |q*iteratedDeriv 1 f b-j-roundedMinorArcQuarticLinearForm f x₀ e r s u t| ≤
      quarticNonlinearResidualConstant σ δ*|q|/N := by
  let f := heathBrownPhysicalPhase F T M A 1
  have hr' : (r:ℝ) ≠ 0 := by exact_mod_cast hr
  have ht' : (t:ℝ) ≠ 0 := by exact_mod_cast ht
  have hq' : (r:ℝ)*u+s*t ≠ 0 := by exact_mod_cast hq
  have hdet' : (v:ℝ)*r-e*s=1 := by exact_mod_cast hdet
  change _ → _ → _ → _
  intro hbase hpoint hsquare
  have hsquare' : |(round x₁:ℝ)-(round x₀:ℝ)|^2 ≤ M*R := by
    simpa only [Int.cast_sub] using hsquare
  have he := physicalModelPhase_quartic_residual_le_fourth_scale
    hσ hδ hF hT hM hN hR hRM hscale hA hW hx₀ hx₁ hr' ht' hq' hdet' hbase hpoint hsquare'
  have hid := firstDerivative_linearization_identity (f := f) (x₀ := x₀) (x₁ := x₁) hr' hq' hdet'
  dsimp only at he hid ⊢
  push_cast
  dsimp only [roundedMinorArcQuarticLinearForm]
  rw [sub_add_eq_sub_sub,hid]
  exact he

                                                                       
                                                                         
theorem physicalModelPhase_quartic_fourth_condition_nonlinear_with_labels
    {σ δ T M N R Δ : ℝ} {u t : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ} {e r v s cnew : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hscale : T*N*R^2=M^3) (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (ht : t ≠ 0)
    (hq : ∀ i, r i*u+s i*t ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let a := fun i => round (x₀ i)
    let b := fun i => round (x₁ i)
    let n := fun i => b i-a i
    let q := fun i => (r i:ℝ)*u+s i*t
    let d₀ := fun i => iteratedDeriv 1 (f i) (a i)
    let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
    let ν := fun i => iteratedDeriv 4 (f i) (a i)/24
    let δ₀ := fun i => iteratedDeriv 2 (f i) (a i)/2-(e i:ℝ)/r i
    let θ := fun i => (r i:ℝ)*d₀ i-round ((r i:ℝ)*d₀ i)
    let β₀ := fun i => d₀ i*s i+2*δ₀ i/(3*μ i*r i)
    let z := fun i => q i*iteratedDeriv 1 (f i) (b i)
    let j := fun i => round ((r i:ℝ)*d₀ i)*u+2*n i*(e i*u+v i*t)
    let h := (cnew 0-j 0)-(cnew 1-j 1)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    (∀ i, |(n i:ℝ)|^2 ≤ M*R) →
    |(z 0-cnew 0)-(z 1-cnew 1)| ≤ Δ →
    |(θ 0-θ 1)*u+(β₀ 0-β₀ 1)*t-
      (t:ℝ)*rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1) ((u:ℝ)/t)+
      (t:ℝ)*quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1) ((u:ℝ)/t)-h| ≤
      Δ+quarticNonlinearResidualConstant σ δ*(|q 0|+|q 1|)/N := by
  let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
  let q := fun i => (r i:ℝ)*u+s i*t
  let j := fun i => round ((r i:ℝ)*iteratedDeriv 1 (f i) (round (x₀ i)))*u+
    2*(round (x₁ i)-round (x₀ i))*(e i*u+v i*t)
  let z := fun i => q i*iteratedDeriv 1 (f i) (round (x₁ i))
  let L := fun i => roundedMinorArcQuarticLinearForm (f i) (x₀ i) (e i) (r i) (s i) u t
  change _ → _ → _ → _ → _
  intro hbase hpoint hsquare hfourth
  have hL (i : Fin 2) : |z i-j i-L i| ≤ quarticNonlinearResidualConstant σ δ*|q i|/N :=
    physicalModelPhase_quartic_rounded_linearization hσ hδ (hF i) hT hM hN hR hRM hscale
      (hA i) (hW i) (hx₀ i) (hx₁ i) (hr i) ht (hq i) (hdet i) (hbase i) (hpoint i) (hsquare i)
  have he := linearization_pair_bound_with_labels (hL 0) (hL 1) hfourth
  have hid : L 0-L 1 =
      (((r 0:ℝ)*iteratedDeriv 1 (f 0) (round (x₀ 0))-round ((r 0:ℝ)*iteratedDeriv 1 (f 0) (round (x₀ 0))))-
        ((r 1:ℝ)*iteratedDeriv 1 (f 1) (round (x₀ 1))-round ((r 1:ℝ)*iteratedDeriv 1 (f 1) (round (x₀ 1)))))*u+
      (iteratedDeriv 1 (f 0) (round (x₀ 0))*s 0+
        2*(iteratedDeriv 2 (f 0) (round (x₀ 0))/2-(e 0:ℝ)/r 0)/(3*(iteratedDeriv 3 (f 0) (round (x₀ 0))/6)*r 0)-
        (iteratedDeriv 1 (f 1) (round (x₀ 1))*s 1+
        2*(iteratedDeriv 2 (f 1) (round (x₀ 1))/2-(e 1:ℝ)/r 1)/(3*(iteratedDeriv 3 (f 1) (round (x₀ 1))/6)*r 1)))*t-
      (t:ℝ)*rationalPhase (iteratedDeriv 3 (f 0) (round (x₀ 0))/6) (r 0) (s 0)
        (iteratedDeriv 3 (f 1) (round (x₀ 1))/6) (r 1) (s 1) ((u:ℝ)/t)+
      (t:ℝ)*quarticPhase (iteratedDeriv 3 (f 0) (round (x₀ 0))/6)
        (iteratedDeriv 4 (f 0) (round (x₀ 0))/24) (r 0) (s 0)
        (iteratedDeriv 3 (f 1) (round (x₀ 1))/6)
        (iteratedDeriv 4 (f 1) (round (x₀ 1))/24) (r 1) (s 1) ((u:ℝ)/t) := by
    dsimp [L,roundedMinorArcQuarticLinearForm,roundedMinorArcLinearForm,rationalPhase,quarticPhase]
    ring
  rw [hid] at he
  exact he.trans_eq (by ring)

                                                                  
                                                                        
           
theorem reciprocal_linear_remainder_bound {x y d : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    |x/y-1+d/x| ≤ x/y*((d/x)^2+(|d/x|+1)*|(y-x-d)/x|) := by
  have hid : x/y-1+d/x =
      (x/y)*((d/x)^2+(d/x-1)*((y-x-d)/x)) := by field_simp; ring
  rw [hid,abs_mul,abs_of_pos (div_pos hx hy)]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hx.le hy.le)
  calc
    _ ≤ |(d/x)^2|+|(d/x-1)*((y-x-d)/x)| := abs_add_le _ _
    _ ≤ (d/x)^2+(|d/x|+1)*|(y-x-d)/x| := by
      rw [abs_of_nonneg (sq_nonneg _),abs_mul]
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      exact (abs_sub _ _).trans_eq (by norm_num)

                                                                    
                                                                        
                                                           
theorem physicalModelPhase_quartic_reciprocal_remainder
    {σ δ T M A W a b : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (ha : a ∈ Set.Ioo 0 W) (hb : b ∈ Set.Ioo 0 W) :
    let f := heathBrownPhysicalPhase F T M A 1
    let μ := iteratedDeriv 3 f a/6
    let μ₁ := iteratedDeriv 3 f b/6
    let ν := iteratedDeriv 4 f a/24
    let n := b-a
    let κ := modelPhaseThirdLower σ
    let L := (modelPhaseJetCoefficient σ 3+δ)/κ
    let V := (modelPhaseJetCoefficient σ 4+δ)/(2*κ)
    |μ/μ₁-1+4*ν*n/μ| ≤ ((σ*(σ+1)+1)/κ)*(L^2+(L+1)*V)*|n|^2/M^2 := by
  let f := heathBrownPhysicalPhase F T M A 1
  let μ := iteratedDeriv 3 f a/6
  let μ₁ := iteratedDeriv 3 f b/6
  let ν := iteratedDeriv 4 f a/24
  let n := b-a
  let κ := modelPhaseThirdLower σ
  let C₃ := modelPhaseJetCoefficient σ 3+δ
  let C₄ := modelPhaseJetCoefficient σ 4+δ
  let L := C₃/κ
  let V := C₄/(2*κ)
  let U := σ*(σ+1)+1
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hF₂ := approximateModelPhase_mono hF (by norm_num : 2 ≤ 4) le_rfl
  have hF₃ := approximateModelPhase_mono hF (by norm_num : 3 ≤ 4) le_rfl
  have hlo := physicalModelPhase_cubicCoefficient_bounds hσ hδ hF₂ hT hM hA hW ha
  have hlo₁ := physicalModelPhase_cubicCoefficient_bounds hσ hδ hF₂ hT hM hA hW hb
  have hμ : 0 < μ := lt_of_lt_of_le (by positivity : 0 < κ*T/(6*M^3)) hlo.1
  have hμ₁ : 0 < μ₁ := lt_of_lt_of_le (by positivity : 0 < κ*T/(6*M^3)) hlo₁.1
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans
    (approximateModelPhase_iteratedDeriv_error hF
      (heathBrownPhysicalPoint_mem_interior hM hA hW ha) 4 le_rfl)
  have hC₃ : 0 ≤ C₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hC₄ : 0 ≤ C₄ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ0
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  have hnM : |n| ≤ M := by
    apply abs_le.mpr
    dsimp only [n]
    constructor <;> linarith only [ha.1,ha.2,hb.1,hb.2,hA,hW]
  have hratio : μ/μ₁ ≤ U/κ := by
    calc
      _ ≤ (U*T/(6*M^3))/(κ*T/(6*M^3)) :=
        div_le_div₀ (by positivity) hlo.2 (by positivity) hlo₁.1
      _ = _ := by field_simp
  have hν := physicalModelPhase_quartic_cubic_ratio_bound hσ hδ hF₃ hT hM hA hW ha
  have hd : |4*ν*n/μ| ≤ L*(|n|/M) := by
    calc
      _ = 2*|2*ν/μ| * |n| := by
        rw [show 4*ν*n/μ=2*(2*ν/μ)*n by ring,abs_mul,abs_mul,
          abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      _ ≤ 2*(C₃/(2*κ*M))*|n| := by gcongr
      _ = _ := by dsimp [L]; ring
  have hdL : |4*ν*n/μ| ≤ L := hd.trans (by
    have hh := (div_le_one hM).mpr hnM
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh hL)
  have hd2 : (4*ν*n/μ)^2 ≤ L^2*(|n|^2/M^2) := by
    have hh := pow_le_pow_left₀ (abs_nonneg _) hd 2
    simpa only [sq_abs,mul_pow,div_pow] using hh
  have hrem := physicalModelPhase_quartic_cubicCoefficient_remainder
    hσ.le hF hT hM hA hW ha hb
  have he : |(μ₁-μ-4*ν*n)/μ| ≤ V*(|n|^2/M^2) := by
    rw [abs_div,abs_of_pos hμ]
    calc
      _ ≤ (T*C₄*|n|^2/(12*M^5))/μ :=
        div_le_div_of_nonneg_right hrem hμ.le
      _ ≤ (T*C₄*|n|^2/(12*M^5))/(κ*T/(6*M^3)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hlo.1
      _ = _ := by dsimp [V]; field_simp; ring
  have hrec := reciprocal_linear_remainder_bound hμ hμ₁ (d := 4*ν*n)
  apply hrec.trans
  calc
    μ/μ₁*((4*ν*n/μ)^2+(|4*ν*n/μ|+1)*|(μ₁-μ-4*ν*n)/μ|) ≤
        (U/κ)*(L^2*(|n|^2/M^2)+(L+1)*(V*(|n|^2/M^2))) := by gcongr
    _ = _ := by dsimp [U,L,V,C₃,C₄,κ,n]; ring


                                                                    
noncomputable def quarticReciprocalConstant (σ δ : ℝ) : ℝ :=
  let κ := modelPhaseThirdLower σ
  let C₂ := modelPhaseJetCoefficient σ 2+δ
  let C₃ := modelPhaseJetCoefficient σ 3+δ
  let C₄ := modelPhaseJetCoefficient σ 4+δ
  let L := C₃/κ
  ((σ*(σ+1)+1)/κ)*(L^2+(L+1)*C₄/(2*κ))+L*(C₂/κ+C₃/(2*κ))

                                                                
                                                                        
                                       
theorem physicalModelPhase_quartic_reciprocal_coordinate_source_scale
    {σ δ T M N R A W x₀ x₁ e r v s u t : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hNscale : N^2 ≤ M*R) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx₀ : x₀ ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hx₁ : x₁ ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1) :
    let f := heathBrownPhysicalPhase F T M A 1
    let a : ℝ := round x₀
    let b : ℝ := round x₁
    let n := b-a
    let μ := iteratedDeriv 3 f a/6
    let μ₁ := iteratedDeriv 3 f b/6
    let ν := iteratedDeriv 4 f a/24
    let G := minorArcCoordinate μ r s (u/t)
    iteratedDeriv 2 f x₀/2=e/r →
    iteratedDeriv 2 f x₁/2=(e*u+v*t)/(r*u+s*t) →
    |n|^2 ≤ M*R →
    |μ/μ₁-1+4*ν*G/μ| ≤ quarticReciprocalConstant σ δ*R^2/N^2 := by
  let f := heathBrownPhysicalPhase F T M A 1
  let a : ℝ := round x₀
  let b : ℝ := round x₁
  let n := b-a
  let μ := iteratedDeriv 3 f a/6
  let μ₁ := iteratedDeriv 3 f b/6
  let ν := iteratedDeriv 4 f a/24
  let G := minorArcCoordinate μ r s (u/t)
  let κ := modelPhaseThirdLower σ
  let C₂ := modelPhaseJetCoefficient σ 2+δ
  let C₃ := modelPhaseJetCoefficient σ 3+δ
  let C₄ := modelPhaseJetCoefficient σ 4+δ
  let L := C₃/κ
  let K := ((σ*(σ+1)+1)/κ)*(L^2+(L+1)*C₄/(2*κ))
  let D := C₂/κ+C₃/(2*κ)
  change _ → _ → _ → _
  intro hbase hpoint hsquare
  have hF₂ := approximateModelPhase_mono hF (by norm_num : 2 ≤ 4) le_rfl
  have hF₃ := approximateModelPhase_mono hF (by norm_num : 3 ≤ 4) le_rfl
  have ha := physicalModelPhase_halfCurvature_round_error hσ.le hF₂ hT hM hA hW hx₀
  have hb := physicalModelPhase_halfCurvature_round_error hσ.le hF₂ hT hM hA hW hx₁
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans
    (approximateModelPhase_iteratedDeriv_error hF
      (heathBrownPhysicalPoint_mem_interior hM hA hW ha.1) 4 le_rfl)
  have hC₂ : 0 ≤ C₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ : 0 ≤ C₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hC₄ : 0 ≤ C₄ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ0
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hcoord := physicalModelPhase_rounded_minorArcCoordinate_entry
    hσ hδ hF₃ hT hM hA hW hx₀ hx₁ hr ht hq hdet hbase hpoint
  have hV : |n-G| ≤ D*R := by
    apply hcoord.trans
    have hn2 : |n|^2/M ≤ R := (div_le_iff₀ hM).mpr (by simpa only [mul_comm] using hsquare)
    calc
      C₂/κ+C₃*|n|^2/(2*κ*M) = C₂/κ+(C₃/(2*κ))*(|n|^2/M) := by ring
      _ ≤ (C₂/κ)*R+(C₃/(2*κ))*R := by
        apply add_le_add
        · simpa only [mul_one] using mul_le_mul_of_nonneg_left hR (show 0 ≤ C₂/κ by positivity)
        · exact mul_le_mul_of_nonneg_left hn2 (by positivity)
      _ = D*R := by dsimp [D]; ring
  have hrec := physicalModelPhase_quartic_reciprocal_remainder
    hσ hδ hF hT hM hA hW ha.1 hb.1
  have hrec' : |μ/μ₁-1+4*ν*n/μ| ≤ K*(R/M) := by
    apply hrec.trans
    have hn2 : |n|^2/M^2 ≤ R/M := by
      apply (div_le_div_iff₀ (by positivity : 0 < M^2) hM).mpr
      have hh := mul_le_mul_of_nonneg_right hsquare hM.le
      nlinarith only [hh]
    calc
      _ = K*(|n|^2/M^2) := by dsimp [K,L,C₄,κ,n]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hn2 hK
  have hν := physicalModelPhase_quartic_cubic_ratio_bound hσ hδ hF₃ hT hM hA hW ha.1
  have hcoef : |4*ν/μ| ≤ L/M := by
    calc
      _ = 2*|2*ν/μ| := by
        rw [show 4*ν/μ=2*(2*ν/μ) by ring,abs_mul]
        norm_num
      _ ≤ 2*(C₃/(2*κ*M)) := mul_le_mul_of_nonneg_left hν (by norm_num)
      _ = _ := by dsimp [L]; ring
  have hscale : R/M ≤ R^2/N^2 := by
    apply (div_le_div_iff₀ hM (by positivity : 0 < N^2)).mpr
    have hh := mul_le_mul_of_nonneg_left hNscale hR0.le
    nlinarith only [hh]
  calc
    |μ/μ₁-1+4*ν*G/μ| =
        |(μ/μ₁-1+4*ν*n/μ)+(4*ν/μ)*(G-n)| := by congr 1; ring
    _ ≤ |μ/μ₁-1+4*ν*n/μ|+|(4*ν/μ)*(G-n)| := abs_add_le _ _
    _ ≤ K*(R/M)+(L/M)*(D*R) := by
      rw [abs_mul,abs_sub_comm G n]
      exact add_le_add hrec' (mul_le_mul hcoef hV (abs_nonneg _) (by positivity))
    _ = (K+L*D)*(R/M) := by ring
    _ ≤ (K+L*D)*(R^2/N^2) := mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = _ := by dsimp [quarticReciprocalConstant,K,L,D,C₂,C₃,C₄,κ]; ring


                                                                      
                                                          
theorem quarticBranch_curvature_transfer
    {μ ν μnew r s x ε : ℝ}
    (hμ : 0 < μ) (hμnew : μnew ≠ 0) (hr : r ≠ 0) (hx : 0 < r*x+s)
    (he : |μ/μnew-1+4*ν*minorArcCoordinate μ r s x/μ| ≤ ε) :
    |iteratedDeriv 2 (rationalBranch μ r s) x-
        iteratedDeriv 2 (quarticBranch μ ν r s) x-2/(3*μnew*(r*x+s)^3)| ≤
      (2/(3*μ*(r*x+s)^3))*ε := by
  rw [rationalBranch_second hμ.ne' hr hx.ne',quarticBranch_second hμ.ne' hr hx.ne']
  have hid : 2/(3*μ*(r*x+s)^3)-8*ν/(9*μ^3*r*(r*x+s)^4)-
      2/(3*μnew*(r*x+s)^3) =
      -(2/(3*μ*(r*x+s)^3))*(μ/μnew-1+4*ν*minorArcCoordinate μ r s x/μ) := by
    dsimp [minorArcCoordinate]
    field_simp
    ring
  rw [hid,abs_mul,abs_neg,abs_of_pos (by positivity : 0 < 2/(3*μ*(r*x+s)^3))]
  exact mul_le_mul_of_nonneg_left he (by positivity)

                                                               
                                                                          
theorem quarticPhase_curvature_of_reciprocal_errors
    {μ ν μnew r s μ₁ ν₁ μnew₁ r₁ s₁ x ε ε₁ Δ : ℝ}
    (hμ : 0 < μ) (hμ₁ : 0 < μ₁) (hμnew : 0 < μnew) (hμnew₁ : 0 < μnew₁)
    (hr : r ≠ 0) (hr₁ : r₁ ≠ 0) (hx : 0 < r*x+s) (hx₁ : 0 < r₁*x+s₁)
    (he : |μ/μnew-1+4*ν*minorArcCoordinate μ r s x/μ| ≤ ε)
    (he₁ : |μ₁/μnew₁-1+4*ν₁*minorArcCoordinate μ₁ r₁ s₁ x/μ₁| ≤ ε₁)
    (hthird : |μnew₁*(r₁*x+s₁)^3/(μnew*(r*x+s)^3)-1| ≤ Δ) :
    |iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) x-
        iteratedDeriv 2 (quarticPhase μ ν r s μ₁ ν₁ r₁ s₁) x| ≤
      2*Δ/(3*μnew₁*(r₁*x+s₁)^3)+
        2*ε/(3*μ*(r*x+s)^3)+2*ε₁/(3*μ₁*(r₁*x+s₁)^3) := by
  have h0 := quarticBranch_curvature_transfer hμ hμnew.ne' hr hx he
  have h1 := quarticBranch_curvature_transfer hμ₁ hμnew₁.ne' hr₁ hx₁ he₁
  have ht := rationalPhase_curvature_of_cubic_ratio hμnew.ne' hr hμnew₁ hr₁ hx.ne' hx₁ hthird
  rw [rationalBranch_second hμ.ne' hr hx.ne',quarticBranch_second hμ.ne' hr hx.ne'] at h0
  rw [rationalBranch_second hμ₁.ne' hr₁ hx₁.ne',quarticBranch_second hμ₁.ne' hr₁ hx₁.ne'] at h1
  rw [rationalPhase_second hμnew.ne' hr hμnew₁.ne' hr₁ hx.ne' hx₁.ne'] at ht
  rw [rationalPhase_second hμ.ne' hr hμ₁.ne' hr₁ hx.ne' hx₁.ne',
    quarticPhase_second hμ.ne' hr hμ₁.ne' hr₁ hx.ne' hx₁.ne']
  have hsplit : ∀ a b c d e f : ℝ,
      |(a-b)-(c-d)| ≤ |e-f|+|a-c-e|+|b-d-f| := by
    intro a b c d e f
    calc
      _ = |(e-f)+(a-c-e)-(b-d-f)| := by congr 1; ring
      _ ≤ |(e-f)+(a-c-e)|+|b-d-f| := abs_sub _ _
      _ ≤ |e-f|+|a-c-e|+|b-d-f| := add_le_add_left (abs_add_le _ _) _
  exact (hsplit _ _ _ _ _ _).trans ((add_le_add (add_le_add ht h0) h1).trans_eq (by ring))

                                                               
                                                                
                                                                 
theorem physicalModelPhase_quartic_third_condition_curvature
    {σ δ T M N R Δ u t : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ e r v s : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hNscale : N^2 ≤ M*R) (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (ht : 0 < t) (hq : ∀ i, 0 < r i*u+s i*t)
    (hdet : ∀ i, v i*r i-e i*s i=1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let a := fun i => (round (x₀ i):ℝ)
    let b := fun i => (round (x₁ i):ℝ)
    let n := fun i => b i-a i
    let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
    let μnew := fun i => iteratedDeriv 3 (f i) (b i)/6
    let ν := fun i => iteratedDeriv 4 (f i) (a i)/24
    let q := fun i => r i*u+s i*t
    let d := fun i => r i*(u/t)+s i
    let E := quarticReciprocalConstant σ δ*R^2/N^2
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=e i/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=(e i*u+v i*t)/q i) →
    (∀ i, |n i|^2 ≤ M*R) →
    |μnew 1*(q 1)^3/(μnew 0*(q 0)^3)-1| ≤ Δ →
    |iteratedDeriv 2 (rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)) (u/t)-
        iteratedDeriv 2 (quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)) (u/t)| ≤
      2*Δ/(3*μnew 1*(d 1)^3)+2*E/(3*μ 0*(d 0)^3)+2*E/(3*μ 1*(d 1)^3) := by
  let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
  let a := fun i => (round (x₀ i):ℝ)
  let b := fun i => (round (x₁ i):ℝ)
  let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
  let μnew := fun i => iteratedDeriv 3 (f i) (b i)/6
  let ν := fun i => iteratedDeriv 4 (f i) (a i)/24
  let q := fun i => r i*u+s i*t
  let d := fun i => r i*(u/t)+s i
  let E := quarticReciprocalConstant σ δ*R^2/N^2
  change _ → _ → _ → _ → _
  intro hbase hpoint hsquare hthird
  have hF₂ (i) := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl
  have ha (i) := physicalModelPhase_halfCurvature_round_error hσ.le (hF₂ i) hT hM (hA i) (hW i) (hx₀ i)
  have hb (i) := physicalModelPhase_halfCurvature_round_error hσ.le (hF₂ i) hT hM (hA i) (hW i) (hx₁ i)
  have hκ := modelPhaseThirdLower_pos hσ
  have hμ (i) : 0 < μ i := lt_of_lt_of_le (by positivity)
    (physicalModelPhase_cubicCoefficient_bounds hσ hδ (hF₂ i) hT hM (hA i) (hW i) (ha i).1).1
  have hμnew (i) : 0 < μnew i := lt_of_lt_of_le (by positivity)
    (physicalModelPhase_cubicCoefficient_bounds hσ hδ (hF₂ i) hT hM (hA i) (hW i) (hb i).1).1
  have he (i) : |μ i/μnew i-1+4*ν i*minorArcCoordinate (μ i) (r i) (s i) (u/t)/μ i| ≤ E :=
    physicalModelPhase_quartic_reciprocal_coordinate_source_scale hσ hδ (hF i)
      hT hM hN hR hNscale (hA i) (hW i) (hx₀ i) (hx₁ i) (hr i) ht.ne' (hq i).ne'
      (hdet i) (hbase i) (hpoint i) (hsquare i)
  have hd (i) : d i=q i/t := by dsimp [d,q]; field_simp
  have hdpos (i) : 0 < d i := by rw [hd i]; exact div_pos (hq i) ht
  have hthird' : |μnew 1*(d 1)^3/(μnew 0*(d 0)^3)-1| ≤ Δ := by
    have hid : μnew 1*(d 1)^3/(μnew 0*(d 0)^3) =
        μnew 1*(q 1)^3/(μnew 0*(q 0)^3) := by
      rw [hd 0,hd 1]
      field_simp
    rw [hid]
    exact hthird
  exact quarticPhase_curvature_of_reciprocal_errors (hμ 0) (hμ 1) (hμnew 0) (hμnew 1)
    (hr 0) (hr 1) (hdpos 0) (hdpos 1) (he 0) (he 1) hthird'


                                                               
                                                                   
                                                                           
theorem physicalModelPhase_quartic_curvature_source_scale
    {σ δ T M N R B dmin u t : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ e r v s : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hNscale : N^2 ≤ M*R) (hscale : T*N*R^2=M^3) (hB : 0 ≤ B) (hdmin : 0 < dmin) (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (ht : 0 < t) (hq : ∀ i, 0 < r i*u+s i*t)
    (hdet : ∀ i, v i*r i-e i*s i=1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let a := fun i => (round (x₀ i):ℝ)
    let b := fun i => (round (x₁ i):ℝ)
    let n := fun i => b i-a i
    let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
    let μnew := fun i => iteratedDeriv 3 (f i) (b i)/6
    let ν := fun i => iteratedDeriv 4 (f i) (a i)/24
    let q := fun i => r i*u+s i*t
    let d := fun i => r i*(u/t)+s i
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=e i/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=(e i*u+v i*t)/q i) →
    (∀ i, |n i|^2 ≤ M*R) →
    (∀ i, dmin ≤ d i) →
    |μnew 1*(q 1)^3/(μnew 0*(q 0)^3)-1| ≤ B*R^2/N^2 →
    |iteratedDeriv 2 (rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)) (u/t)-
        iteratedDeriv 2 (quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)) (u/t)| ≤
      (4/modelPhaseThirdLower σ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3) := by
  let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
  let a := fun i => (round (x₀ i):ℝ)
  let b := fun i => (round (x₁ i):ℝ)
  let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
  let μnew := fun i => iteratedDeriv 3 (f i) (b i)/6
  let d := fun i => r i*(u/t)+s i
  let κ := modelPhaseThirdLower σ
  let C := quarticReciprocalConstant σ δ
  let E := C*R^2/N^2
  change _ → _ → _ → _ → _ → _
  intro hbase hpoint hsquare hden hthird
  have he := physicalModelPhase_quartic_third_condition_curvature hσ hδ hF
    hT hM hN hR hNscale hA hW hx₀ hx₁ hr ht hq hdet hbase hpoint hsquare hthird
  have hF₂ (i) := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl
  have ha (i) := physicalModelPhase_halfCurvature_round_error hσ.le (hF₂ i) hT hM (hA i) (hW i) (hx₀ i)
  have hb (i) := physicalModelPhase_halfCurvature_round_error hσ.le (hF₂ i) hT hM (hA i) (hW i) (hx₁ i)
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hlo (i) : κ*T/(6*M^3) ≤ μ i :=
    (physicalModelPhase_cubicCoefficient_bounds hσ hδ (hF₂ i) hT hM (hA i) (hW i) (ha i).1).1
  have hloNew : κ*T/(6*M^3) ≤ μnew 1 :=
    (physicalModelPhase_cubicCoefficient_bounds hσ hδ (hF₂ 1) hT hM (hA 1) (hW 1) (hb 1).1).1
  have hcoef (m z : ℝ) (hm : κ*T/(6*M^3) ≤ m) (hz : dmin ≤ z) :
      2/(3*m*z^3) ≤ 4*N*R^2/(κ*dmin^3) := by
    have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hm
    have hz0 : 0 < z := hdmin.trans_le hz
    calc
      _ ≤ 2/(3*(κ*T/(6*M^3))*dmin^3) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        gcongr
      _ = 4*M^3/(κ*T*dmin^3) := by field_simp; norm_num
      _ = _ := by rw [← hscale]; field_simp
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans
    (approximateModelPhase_iteratedDeriv_error (hF 0)
      (heathBrownPhysicalPoint_mem_interior hM (hA 0) (hW 0) (ha 0).1) 4 le_rfl)
  have hC : 0 ≤ C := by
    have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
    have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
    have hC₄ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ0
    dsimp [C,quarticReciprocalConstant]
    positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  apply he.trans
  calc
    2*(B*R^2/N^2)/(3*μnew 1*(d 1)^3)+2*E/(3*μ 0*(d 0)^3)+2*E/(3*μ 1*(d 1)^3) =
        (2/(3*μnew 1*(d 1)^3))*(B*R^2/N^2)+
        (2/(3*μ 0*(d 0)^3))*E+(2/(3*μ 1*(d 1)^3))*E := by ring
    _ ≤ (4*N*R^2/(κ*dmin^3))*(B*R^2/N^2)+
        (4*N*R^2/(κ*dmin^3))*E+(4*N*R^2/(κ*dmin^3))*E := by
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_right (hcoef _ _ hloNew (hden 1)) (by positivity)
        · exact mul_le_mul_of_nonneg_right (hcoef _ _ (hlo 0) (hden 0)) hE
      · exact mul_le_mul_of_nonneg_right (hcoef _ _ (hlo 1) (hden 1)) hE
    _ = _ := by dsimp [E,C,κ]; field_simp; ring


                                                                   
                                                                         
                                                                        
open Set
open Polynomial
open Set
open scoped Classical
noncomputable def quarticCurvatureNumerator
    (μ ν r s μ₁ ν₁ r₁ s₁ : ℝ) : Polynomial ℝ :=
  (C (2/(3*μ))*(C r*X+C s)-C (8*ν/(9*μ^3*r)))*(C r₁*X+C s₁)^4-
  (C (2/(3*μ₁))*(C r₁*X+C s₁)-C (8*ν₁/(9*μ₁^3*r₁)))*(C r*X+C s)^4

theorem quarticCurvatureNumerator_degree (μ ν r s μ₁ ν₁ r₁ s₁ : ℝ) :
    (quarticCurvatureNumerator μ ν r s μ₁ ν₁ r₁ s₁).natDegree ≤ 5 := by
  have ha (a b : ℝ) : (C a*X+C b).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · simpa using (natDegree_mul_le (p := C a) (q := X))
    · simp
  have hb (c d a b : ℝ) : (C c*(C a*X+C b)-C d).natDegree ≤ 1 := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact (natDegree_mul_le).trans (by simpa using ha a b)
    · simp
  dsimp [quarticCurvatureNumerator]
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact natDegree_mul_le.trans (by
      have h0 := hb (2/(3*μ)) (8*ν/(9*μ^3*r)) r s
      have h1 := natDegree_pow_le_of_le 4 (ha r₁ s₁)
      omega)
  · exact natDegree_mul_le.trans (by
      have h0 := hb (2/(3*μ₁)) (8*ν₁/(9*μ₁^3*r₁)) r₁ s₁
      have h1 := natDegree_pow_le_of_le 4 (ha r s)
      omega)

theorem quarticCurvatureNumerator_eval
    {μ ν r s μ₁ ν₁ r₁ s₁ x : ℝ}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hx : r*x+s ≠ 0) (hx₁ : r₁*x+s₁ ≠ 0) :
    iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) x-
      iteratedDeriv 2 (quarticPhase μ ν r s μ₁ ν₁ r₁ s₁) x =
      (quarticCurvatureNumerator μ ν r s μ₁ ν₁ r₁ s₁).eval x/
        ((r*x+s)^4*(r₁*x+s₁)^4) := by
  rw [rationalPhase_second hμ hr hμ₁ hr₁ hx hx₁,
    quarticPhase_second hμ hr hμ₁ hr₁ hx hx₁]
  simp only [quarticCurvatureNumerator,eval_sub,eval_mul,eval_add,eval_C,eval_X,eval_pow]
  have hx₁' : x*r₁+s₁ ≠ 0 := by simpa only [mul_comm] using hx₁
  field_simp [hx₁']
  ring

                                                                
noncomputable def quarticCurvatureBoundaryPolynomial
    (μ ν r s μ₁ ν₁ r₁ s₁ c : ℝ) : Polynomial ℝ :=
  quarticCurvatureNumerator μ ν r s μ₁ ν₁ r₁ s₁-
    C c*((C r*X+C s)^4*(C r₁*X+C s₁)^4)

theorem quarticCurvatureBoundaryPolynomial_degree
    (μ ν r s μ₁ ν₁ r₁ s₁ c : ℝ) :
    (quarticCurvatureBoundaryPolynomial μ ν r s μ₁ ν₁ r₁ s₁ c).natDegree ≤ 8 := by
  have ha (a b : ℝ) : (C a*X+C b).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · simpa using (natDegree_mul_le (p := C a) (q := X))
    · simp
  have hd : ((C r*X+C s)^4*(C r₁*X+C s₁)^4).natDegree ≤ 8 :=
    natDegree_mul_le.trans (by
      have h0 := natDegree_pow_le_of_le 4 (ha r s)
      have h1 := natDegree_pow_le_of_le 4 (ha r₁ s₁)
      omega)
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact (quarticCurvatureNumerator_degree μ ν r s μ₁ ν₁ r₁ s₁).trans (by norm_num)
  · exact natDegree_mul_le.trans (by simpa using hd)

theorem quarticCurvatureBoundaryPolynomial_eval
    {μ ν r s μ₁ ν₁ r₁ s₁ c x : ℝ}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hx : r*x+s ≠ 0) (hx₁ : r₁*x+s₁ ≠ 0) :
    (quarticCurvatureBoundaryPolynomial μ ν r s μ₁ ν₁ r₁ s₁ c).eval x =
      ((r*x+s)^4*(r₁*x+s₁)^4)*
        (iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) x-
          iteratedDeriv 2 (quarticPhase μ ν r s μ₁ ν₁ r₁ s₁) x-c) := by
  rw [quarticCurvatureNumerator_eval hμ hμ₁ hr hr₁ hx hx₁]
  simp only [quarticCurvatureBoundaryPolynomial,eval_sub,eval_mul,eval_C,eval_pow,eval_add,eval_X]
  have hx₁' : x*r₁+s₁ ≠ 0 := by simpa only [mul_comm] using hx₁
  field_simp [hx₁']






                                                                 
                             
theorem quarticCurvatureBoundaryPolynomial_isRoot_iff
    {μ ν r s μ₁ ν₁ r₁ s₁ c x : ℝ}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hx : r*x+s ≠ 0) (hx₁ : r₁*x+s₁ ≠ 0) :
    (quarticCurvatureBoundaryPolynomial μ ν r s μ₁ ν₁ r₁ s₁ c).IsRoot x ↔
      iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) x-
        iteratedDeriv 2 (quarticPhase μ ν r s μ₁ ν₁ r₁ s₁) x=c := by
  rw [Polynomial.IsRoot,quarticCurvatureBoundaryPolynomial_eval hμ hμ₁ hr hr₁ hx hx₁]
  have hd : (r*x+s)^4*(r₁*x+s₁)^4 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 4 hx) (pow_ne_zero 4 hx₁)
  rw [mul_eq_zero,or_iff_right hd,sub_eq_zero]

                                                                        
                                                                      
noncomputable def quarticCurvatureBoundaryRoots
    (μ ν r s μ₁ ν₁ r₁ s₁ U : ℝ) : Finset ℝ :=
  (quarticCurvatureBoundaryPolynomial μ ν r s μ₁ ν₁ r₁ s₁ U).roots.toFinset ∪
  (quarticCurvatureBoundaryPolynomial μ ν r s μ₁ ν₁ r₁ s₁ (-U)).roots.toFinset

theorem quarticCurvatureBoundaryRoots_card
    (μ ν r s μ₁ ν₁ r₁ s₁ U : ℝ) :
    (quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U).card ≤ 16 := by
  have hcard (c : ℝ) :
      (quarticCurvatureBoundaryPolynomial μ ν r s μ₁ ν₁ r₁ s₁ c).roots.toFinset.card ≤ 8 :=
    (Multiset.toFinset_card_le _).trans
      ((Polynomial.card_roots' _).trans
        (quarticCurvatureBoundaryPolynomial_degree μ ν r s μ₁ ν₁ r₁ s₁ c))
  exact (Finset.card_union_le _ _).trans (by have hp := hcard U; have hm := hcard (-U); omega)

theorem mem_quarticCurvatureBoundaryRoots_iff
    {μ ν r s μ₁ ν₁ r₁ s₁ U x : ℝ}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hp : quarticCurvatureBoundaryPolynomial μ ν r s μ₁ ν₁ r₁ s₁ U ≠ 0)
    (hm : quarticCurvatureBoundaryPolynomial μ ν r s μ₁ ν₁ r₁ s₁ (-U) ≠ 0)
    (hx : r*x+s ≠ 0) (hx₁ : r₁*x+s₁ ≠ 0) :
    x ∈ quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U ↔
      (iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) x-
        iteratedDeriv 2 (quarticPhase μ ν r s μ₁ ν₁ r₁ s₁) x=U) ∨
      (iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) x-
        iteratedDeriv 2 (quarticPhase μ ν r s μ₁ ν₁ r₁ s₁) x= -U) := by
  simp only [quarticCurvatureBoundaryRoots,Finset.mem_union,Multiset.mem_toFinset,
    Polynomial.mem_roots hp,Polynomial.mem_roots hm,
    quarticCurvatureBoundaryPolynomial_isRoot_iff hμ hμ₁ hr hr₁ hx hx₁]

                                                                
                                                                      
                                                                          
theorem finite_boundary_rank_interval {S : Finset ℝ} {x y : ℝ}
    (hx : x ∉ S) (hy : y ∉ S)
    (heq : (S.filter (fun z => z<x)).card=(S.filter (fun z => z<y)).card) :
    ∀ z ∈ Set.uIcc x y, z ∉ S := by
  have hordered {a b : ℝ} (hab : a ≤ b) (hb : b ∉ S)
      (he : (S.filter (fun z => z<a)).card=(S.filter (fun z => z<b)).card) :
      ∀ z ∈ Set.Icc a b, z ∉ S := by
    have hsub : S.filter (fun z => z<a) ⊆ S.filter (fun z => z<b) := by
      intro z hz
      obtain ⟨hzS,hza⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hzS,hza.trans_le hab⟩
    have hsets : S.filter (fun z => z<a)=S.filter (fun z => z<b) :=
      Finset.eq_of_subset_of_card_le hsub he.ge
    intro z hz hzS
    have hzb : z<b := lt_of_le_of_ne hz.2 (by
      intro hzb
      exact hb (hzb ▸ hzS))
    have hm : z ∈ S.filter (fun w => w<b) := Finset.mem_filter.mpr ⟨hzS,hzb⟩
    rw [← hsets] at hm
    exact (not_lt_of_ge hz.1) (Finset.mem_filter.mp hm).2
  rcases le_total x y with hxy | hyx
  · simpa only [Set.uIcc_of_le hxy] using hordered hxy hy heq
  · simpa only [Set.uIcc_of_ge hyx] using hordered hyx hx heq.symm

                                                                  
                                                                   
                                                                  
theorem continuous_band_constant_on_boundary_rank
    {f : ℝ → ℝ} {S : Finset ℝ} {x y U : ℝ}
    (hf : ContinuousOn f (Set.uIcc x y))
    (hboundary : ∀ z ∈ Set.uIcc x y, |f z|=U → z ∈ S)
    (hx : x ∉ S) (hy : y ∉ S)
    (heq : (S.filter (fun z => z<x)).card=(S.filter (fun z => z<y)).card) :
    (|f x| ≤ U ↔ |f y| ≤ U) := by
  have hno := finite_boundary_rank_interval hx hy heq
  have hnone (z : ℝ) (hz : z ∈ Set.uIcc x y) : |f z| ≠ U := by
    intro hh
    exact hno z hz (hboundary z hz hh)
  have hIVT := intermediate_value_uIcc hf.abs
  constructor
  · intro hfx
    by_contra hfy
    have hmem : U ∈ Set.uIcc |f x| |f y| :=
      Set.mem_uIcc.mpr (Or.inl ⟨hfx,(lt_of_not_ge hfy).le⟩)
    obtain ⟨z,hz,he⟩ := hIVT hmem
    exact hnone z hz he
  · intro hfy
    by_contra hfx
    have hmem : U ∈ Set.uIcc |f x| |f y| :=
      Set.mem_uIcc.mpr (Or.inr ⟨hfy,(lt_of_not_ge hfx).le⟩)
    obtain ⟨z,hz,he⟩ := hIVT hmem
    exact hnone z hz he




                                                                     
                                                                
                                                                
theorem quartic_curvature_band_rank_partition
    {μ ν r s μ₁ ν₁ r₁ s₁ U l w : ℝ}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hden : ∀ x ∈ Set.Icc l w, r*x+s ≠ 0)
    (hden₁ : ∀ x ∈ Set.Icc l w, r₁*x+s₁ ≠ 0) :
    let F := fun x => iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) x-
      iteratedDeriv 2 (quarticPhase μ ν r s μ₁ ν₁ r₁ s₁) x
    let S := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    S.card ≤ 16 ∧
      ∀ x ∈ Set.Icc l w, ∀ y ∈ Set.Icc l w, x ∉ S → y ∉ S →
        (S.filter (fun z => z<x)).card=(S.filter (fun z => z<y)).card →
        (|F x| ≤ U ↔ |F y| ≤ U) := by
  let F := fun x => iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) x-
    iteratedDeriv 2 (quarticPhase μ ν r s μ₁ ν₁ r₁ s₁) x
  let S := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
  refine ⟨quarticCurvatureBoundaryRoots_card μ ν r s μ₁ ν₁ r₁ s₁ U,?_⟩
  intro x hx y hy hxS hyS hrank
  have hlevel {c : ℝ} (hp : quarticCurvatureBoundaryPolynomial μ ν r s μ₁ ν₁ r₁ s₁ c=0)
      (z : ℝ) (hz : z ∈ Set.Icc l w) : F z=c := by
    apply (quarticCurvatureBoundaryPolynomial_isRoot_iff hμ hμ₁ hr hr₁
      (hden z hz) (hden₁ z hz)).mp
    simp [hp,Polynomial.IsRoot]
  by_cases hp : quarticCurvatureBoundaryPolynomial μ ν r s μ₁ ν₁ r₁ s₁ U=0
  · change |F x| ≤ U ↔ |F y| ≤ U
    rw [hlevel hp x hx,hlevel hp y hy]
  by_cases hm : quarticCurvatureBoundaryPolynomial μ ν r s μ₁ ν₁ r₁ s₁ (-U)=0
  · change |F x| ≤ U ↔ |F y| ≤ U
    rw [hlevel hm x hx,hlevel hm y hy]
  have hseg := Set.uIcc_subset_Icc hx hy
  have hpoly : ContinuousOn
      (fun z => (quarticCurvatureNumerator μ ν r s μ₁ ν₁ r₁ s₁).eval z/
        ((r*z+s)^4*(r₁*z+s₁)^4)) (Set.uIcc x y) :=
    (Polynomial.continuous _).continuousOn.div (by fun_prop) (fun z hz =>
      mul_ne_zero (pow_ne_zero 4 (hden z (hseg hz))) (pow_ne_zero 4 (hden₁ z (hseg hz))))
  have hF : ContinuousOn F (Set.uIcc x y) := by
    apply hpoly.congr
    intro z hz
    exact quarticCurvatureNumerator_eval hμ hμ₁ hr hr₁ (hden z (hseg hz)) (hden₁ z (hseg hz))
  apply continuous_band_constant_on_boundary_rank hF _ hxS hyS hrank
  intro z hz he
  apply (mem_quarticCurvatureBoundaryRoots_iff hμ hμ₁ hr hr₁ hp hm
    (hden z (hseg hz)) (hden₁ z (hseg hz))).mpr
  by_cases hfz : 0 ≤ F z
  · exact Or.inl (by simpa only [abs_of_nonneg hfz] using he)
  · right
    have hh : -F z=U := by simpa only [abs_of_nonpos (le_of_not_ge hfz)] using he
    change F z= -U
    linarith only [hh]



                                                           
noncomputable def finiteBoundaryCell (S : Finset ℝ) (l w : ℝ) (k : ℕ) : Set ℝ :=
  {x | x ∈ Set.Icc l w ∧ x ∉ S ∧ (S.filter (fun z => z<x)).card=k}

theorem finiteBoundaryCell_ordConnected (S : Finset ℝ) (l w : ℝ) (k : ℕ) :
    Set.OrdConnected (finiteBoundaryCell S l w k) := by
  constructor
  intro x hx y hy z hz
  have hmon {a b : ℝ} (hab : a ≤ b) :
      (S.filter (fun v => v<a)).card ≤ (S.filter (fun v => v<b)).card := by
    apply Finset.card_le_card
    intro v hv
    obtain ⟨hvS,hva⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨hvS,hva.trans_le hab⟩
  have hx' : x ∈ Set.Icc l w ∧ x ∉ S ∧ (S.filter (fun v => v<x)).card=k := hx
  have hy' : y ∈ Set.Icc l w ∧ y ∉ S ∧ (S.filter (fun v => v<y)).card=k := hy
  have hno := finite_boundary_rank_interval hx'.2.1 hy'.2.1 (hx'.2.2.trans hy'.2.2.symm)
  have hzI : z ∈ Set.uIcc x y := Set.Icc_subset_uIcc hz
  refine ⟨⟨hx'.1.1.trans hz.1,hz.2.trans hy'.1.2⟩,hno z hzI,?_⟩
  have hleft := hmon hz.1
  have hright := hmon hz.2
  omega

                                                                    
                                                                     
                                                                       
                                                                       
theorem quartic_curvature_band_finite_interval_partition
    {μ ν r s μ₁ ν₁ r₁ s₁ U l w : ℝ}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hden : ∀ x ∈ Set.Icc l w, r*x+s ≠ 0)
    (hden₁ : ∀ x ∈ Set.Icc l w, r₁*x+s₁ ≠ 0) :
    let F := fun x => iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) x-
      iteratedDeriv 2 (quarticPhase μ ν r s μ₁ ν₁ r₁ s₁) x
    let S := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    S.card ≤ 16 ∧
      (∀ k : Fin 17, Set.OrdConnected (finiteBoundaryCell S l w k)) ∧
      (∀ x ∈ Set.Icc l w, x ∈ S ∨ ∃ k : Fin 17, x ∈ finiteBoundaryCell S l w k) ∧
      (∀ k : Fin 17, ∀ x ∈ finiteBoundaryCell S l w k,
        ∀ y ∈ finiteBoundaryCell S l w k, |F x| ≤ U ↔ |F y| ≤ U) := by
  let S := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
  have hpart := quartic_curvature_band_rank_partition (ν := ν) (ν₁ := ν₁)
    (U := U) hμ hμ₁ hr hr₁ hden hden₁
  refine ⟨hpart.1,fun k => finiteBoundaryCell_ordConnected S l w k,?_,?_⟩
  · intro x hx
    by_cases hxS : x ∈ S
    · exact Or.inl hxS
    · right
      have hcard : S.card ≤ 16 := hpart.1
      have hk : (S.filter (fun z => z<x)).card < 17 :=
        lt_of_le_of_lt (Finset.card_filter_le _ _) (by omega)
      exact ⟨⟨_,hk⟩,hx,hxS,rfl⟩
  · intro k x hx y hy
    exact hpart.2 x hx.1 y hy.1 hx.2.1 hy.2.1 (hx.2.2.trans hy.2.2.symm)





                                                                       
                                                                         
                                                                            
theorem quartic_phase_taylor_on_boundary_cell
    {μ ν r s μ₁ ν₁ r₁ s₁ U l w x₀ x : ℝ} {k : Fin 17}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hden : ∀ y ∈ Set.Icc l w, r*y+s ≠ 0)
    (hden₁ : ∀ y ∈ Set.Icc l w, r₁*y+s₁ ≠ 0) :
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun y => g y-h y
    let S := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    x₀ ∈ finiteBoundaryCell S l w k →
    x ∈ finiteBoundaryCell S l w k →
    |iteratedDeriv 2 g x₀-iteratedDeriv 2 h x₀| ≤ U →
    |φ x-φ x₀-deriv φ x₀*(x-x₀)| ≤ U*|x-x₀|^2/2 := by
  let g := rationalPhase μ r s μ₁ r₁ s₁
  let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
  let φ := fun y => g y-h y
  let S := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
  change _ → _ → _ → _
  intro hx₀ hx hbound
  have hpart := quartic_curvature_band_finite_interval_partition (ν := ν) (ν₁ := ν₁)
    (U := U) hμ hμ₁ hr hr₁ hden hden₁
  have hcell (y : ℝ) (hy : y ∈ Set.uIcc x₀ x) : y ∈ finiteBoundaryCell S l w k :=
    (hpart.2.1 k).uIcc_subset hx₀ hx hy
  have hg (y : ℝ) (hy : y ∈ Set.uIcc x₀ x) : ContDiffAt ℝ 2 g y := by
    have hd := hden y (hcell y hy).1
    have hd₁ := hden₁ y (hcell y hy).1
    change ContDiffAt ℝ 2
      (fun z => 1/(3*μ*r^2*(r*z+s))-1/(3*μ₁*r₁^2*(r₁*z+s₁))) y
    exact (contDiffAt_const.div (by fun_prop) (by positivity)).sub
      (contDiffAt_const.div (by fun_prop) (by positivity))
  have hh (y : ℝ) (hy : y ∈ Set.uIcc x₀ x) : ContDiffAt ℝ 2 h y := by
    have hd := hden y (hcell y hy).1
    have hd₁ := hden₁ y (hcell y hy).1
    change ContDiffAt ℝ 2
      (fun z => 4*ν/(27*μ^3*r^3*(r*z+s)^2)-4*ν₁/(27*μ₁^3*r₁^3*(r₁*z+s₁)^2)) y
    exact (contDiffAt_const.div (by fun_prop) (by positivity)).sub
      (contDiffAt_const.div (by fun_prop) (by positivity))
  have hcurv (y : ℝ) (hy : y ∈ Set.uIcc x₀ x) : |iteratedDeriv 2 φ y| ≤ U := by
    change |iteratedDeriv 2 (fun z => g z-h z) y| ≤ U
    rw [iteratedDeriv_fun_sub (hg y hy) (hh y hy)]
    exact (hpart.2.2.2 k x₀ hx₀ y (hcell y hy)).mp hbound
  have he := abs_finiteTaylorPolynomial_remainder_le_finite 1
    (fun y hy => (hg y hy).sub (hh y hy)) hcurv
  have hpoly : finiteTaylorPolynomial φ 1 x₀ x=φ x₀+deriv φ x₀*(x-x₀) := by
    simp [finiteTaylorPolynomial,taylor_within_apply,iteratedDeriv_succ]
    ring
  rw [hpoly] at he
  norm_num only [Nat.reduceAdd,Nat.factorial,Nat.cast_ofNat] at he
  change |φ x-φ x₀-deriv φ x₀*(x-x₀)| ≤ U*|x-x₀|^2/2
  change |φ x-(φ x₀+deriv φ x₀*(x-x₀))| ≤ U*|x-x₀|^2/2 at he
  convert he using 1
  congr 1
  ring




                                                                   
                                                                         
                                                                           
                                                                    
theorem physicalModelPhase_quartic_taylor_on_boundary_cell
    {σ δ T M N R B dmin u t l w y : ℝ} {k : Fin 17}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ e r v s : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hNscale : N^2 ≤ M*R) (hscale : T*N*R^2=M^3)
    (hB : 0 ≤ B) (hdmin : 0 < dmin)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (ht : 0 < t)
    (hdet : ∀ i, v i*r i-e i*s i=1)
    (hden : ∀ z ∈ Set.Icc l w, ∀ i, dmin ≤ r i*z+s i) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let a := fun i => (round (x₀ i):ℝ)
    let b := fun i => (round (x₁ i):ℝ)
    let n := fun i => b i-a i
    let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
    let μnew := fun i => iteratedDeriv 3 (f i) (b i)/6
    let ν := fun i => iteratedDeriv 4 (f i) (a i)/24
    let q := fun i => r i*u+s i*t
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let h := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let φ := fun z => g z-h z
    let U := (4/modelPhaseThirdLower σ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let S := quarticCurvatureBoundaryRoots (μ 0) (ν 0) (r 0) (s 0)
      (μ 1) (ν 1) (r 1) (s 1) U
    u/t ∈ finiteBoundaryCell S l w k →
    y ∈ finiteBoundaryCell S l w k →
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=e i/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=(e i*u+v i*t)/q i) →
    (∀ i, |n i|^2 ≤ M*R) →
    |μnew 1*(q 1)^3/(μnew 0*(q 0)^3)-1| ≤ B*R^2/N^2 →
    |φ y-φ (u/t)-deriv φ (u/t)*(y-u/t)| ≤ U*|y-u/t|^2/2 := by
  let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
  let a := fun i => (round (x₀ i):ℝ)
  let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
  change _ → _ → _ → _ → _ → _ → _
  intro hu hy hbase hpoint hsquare hthird
  have hF₂ (i) := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl
  have ha (i) := physicalModelPhase_halfCurvature_round_error hσ.le (hF₂ i)
    hT hM (hA i) (hW i) (hx₀ i)
  have hκ := modelPhaseThirdLower_pos hσ
  have hμ (i) : 0 < μ i := lt_of_lt_of_le (by positivity)
    (physicalModelPhase_cubicCoefficient_bounds hσ hδ (hF₂ i) hT hM (hA i) (hW i) (ha i).1).1
  have hd (z : ℝ) (hz : z ∈ Set.Icc l w) (i) : 0 < r i*z+s i :=
    hdmin.trans_le (hden z hz i)
  have hq (i) : 0 < r i*u+s i*t := by
    have he : r i*u+s i*t=(r i*(u/t)+s i)*t := by field_simp
    rw [he]
    exact mul_pos (hd (u/t) hu.1 i) ht
  have hcurv := physicalModelPhase_quartic_curvature_source_scale
    hσ hδ hF hT hM hN hR hNscale hscale hB hdmin hA hW hx₀ hx₁ hr ht hq hdet
    hbase hpoint hsquare (hden (u/t) hu.1) hthird
  exact quartic_phase_taylor_on_boundary_cell (hμ 0).ne' (hμ 1).ne' (hr 0) (hr 1)
    (fun z hz => (hd z hz 0).ne') (fun z hz => (hd z hz 1).ne') hu hy hcurv




                                                                  
                                                                       
                                      
theorem quartic_phase_derivative_variation_on_boundary_cell
    {μ ν r s μ₁ ν₁ r₁ s₁ U l w x₀ x : ℝ} {k : Fin 17}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hden : ∀ y ∈ Set.Icc l w, r*y+s ≠ 0)
    (hden₁ : ∀ y ∈ Set.Icc l w, r₁*y+s₁ ≠ 0) :
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun y => g y-h y
    let S := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    x₀ ∈ finiteBoundaryCell S l w k →
    x ∈ finiteBoundaryCell S l w k →
    |iteratedDeriv 2 g x₀-iteratedDeriv 2 h x₀| ≤ U →
    |deriv φ x-deriv φ x₀| ≤ U*|x-x₀| := by
  let g := rationalPhase μ r s μ₁ r₁ s₁
  let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
  let φ := fun y => g y-h y
  let S := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
  change _ → _ → _ → _
  intro hx₀ hx hbound
  have hpart := quartic_curvature_band_finite_interval_partition (ν := ν) (ν₁ := ν₁)
    (U := U) hμ hμ₁ hr hr₁ hden hden₁
  have hcell (y : ℝ) (hy : y ∈ Set.uIcc x₀ x) : y ∈ finiteBoundaryCell S l w k :=
    (hpart.2.1 k).uIcc_subset hx₀ hx hy
  have hg (y : ℝ) (hy : y ∈ Set.uIcc x₀ x) : ContDiffAt ℝ 2 g y := by
    have hd := hden y (hcell y hy).1
    have hd₁ := hden₁ y (hcell y hy).1
    change ContDiffAt ℝ 2
      (fun z => 1/(3*μ*r^2*(r*z+s))-1/(3*μ₁*r₁^2*(r₁*z+s₁))) y
    fun_prop (disch := positivity)
  have hh (y : ℝ) (hy : y ∈ Set.uIcc x₀ x) : ContDiffAt ℝ 2 h y := by
    have hd := hden y (hcell y hy).1
    have hd₁ := hden₁ y (hcell y hy).1
    change ContDiffAt ℝ 2
      (fun z => 4*ν/(27*μ^3*r^3*(r*z+s)^2)-4*ν₁/(27*μ₁^3*r₁^3*(r₁*z+s₁)^2)) y
    fun_prop (disch := positivity)
  have hcurv (y : ℝ) (hy : y ∈ Set.uIcc x₀ x) : |iteratedDeriv 2 φ y| ≤ U := by
    change |iteratedDeriv 2 (fun z => g z-h z) y| ≤ U
    rw [iteratedDeriv_fun_sub (hg y hy) (hh y hy)]
    exact (hpart.2.2.2 k x₀ hx₀ y (hcell y hy)).mp hbound
  have hdφ (y : ℝ) (hy : y ∈ Set.uIcc x₀ x) :
      HasDerivAt (deriv φ) (iteratedDeriv 2 φ y) y := by
    simpa only [iteratedDeriv_one] using hasDerivAt_iteratedDeriv_finite
      (by norm_num : 1 < 2) ((hg y hy).sub (hh y hy))
  exact (convex_uIcc x₀ x).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y hy => (hdφ y hy).hasDerivWithinAt) (C := U)
    (fun y hy => by simpa only [Real.norm_eq_abs] using hcurv y hy)
    Set.left_mem_uIcc Set.right_mem_uIcc

                                                                    
                                                                  
                                                                       
open scoped Classical
open scoped Classical
theorem quarticPhase_four_point_curvature
    {μ ν r s μ₁ ν₁ r₁ s₁ a b c d h E A B : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr₁ : r₁ ≠ 0)
    (hh : 0 < h) (hab : h ≤ b-a) (hbc : h ≤ c-b) (hcd : h ≤ d-c)
    (hden : ∀ x ∈ Set.Icc a d, r*x+s ≠ 0)
    (hden₁ : ∀ x ∈ Set.Icc a d, r₁*x+s₁ ≠ 0) :
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let H := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    (∀ x ∈ ({a,b,c,d} : Finset ℝ), |A*x+B-g x+H x| ≤ E) →
    ∃ z ∈ Set.Ioo a d,
      |iteratedDeriv 2 g z-iteratedDeriv 2 H z| ≤ 4*E/h^2 := by
  let g := rationalPhase μ r s μ₁ r₁ s₁
  let H := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
  let f := fun x => A*x+B-g x+H x
  change _ → _
  intro hres
  have hg (x : ℝ) (hx : x ∈ Set.Icc a d) : ContDiffAt ℝ 2 g x := by
    change ContDiffAt ℝ 2 (fun y => 1/(3*μ*r^2*(r*y+s))-1/(3*μ₁*r₁^2*(r₁*y+s₁))) x
    have hd := hden x hx
    have hd₁ := hden₁ x hx
    fun_prop (disch := positivity)
  have hH (x : ℝ) (hx : x ∈ Set.Icc a d) : ContDiffAt ℝ 2 H x := by
    change ContDiffAt ℝ 2
      (fun y => 4*ν/(27*μ^3*r^3*(r*y+s)^2)-4*ν₁/(27*μ₁^3*r₁^3*(r₁*y+s₁)^2)) x
    have hd := hden x hx
    have hd₁ := hden₁ x hx
    fun_prop (disch := positivity)
  have hf (x : ℝ) (hx : x ∈ Set.Icc a d) : ContDiffAt ℝ 2 f x :=
    ((show ContDiffAt ℝ 2 (fun y => A*y+B) x by fun_prop).sub (hg x hx)).add (hH x hx)
  obtain ⟨z,hz,hez⟩ := four_point_curvature hh hab hbc hcd hf
    (hres a (by simp)) (hres b (by simp)) (hres c (by simp)) (hres d (by simp))
  have hz' : z ∈ Set.Icc a d := ⟨hz.1.le,hz.2.le⟩
  have hid : iteratedDeriv 2 f z=-(iteratedDeriv 2 g z-iteratedDeriv 2 H z) := by
    dsimp only [f]
    rw [iteratedDeriv_fun_add
      ((show ContDiffAt ℝ 2 (fun y => A*y+B) z by fun_prop).sub (hg z hz')) (hH z hz'),
      iteratedDeriv_fun_sub (by fun_prop) (hg z hz')]
    have hdlin : deriv (fun y : ℝ => A*y+B)=fun _ => A := by
      funext y
      simpa only [mul_one,id_eq] using (((hasDerivAt_id y).const_mul A).add_const B).deriv
    rw [iteratedDeriv_succ,iteratedDeriv_one,hdlin]
    simp only [deriv_const]
    ring
  rw [hid,abs_neg] at hez
  exact ⟨z,hz,hez⟩


                                                                    
                                                                    
                                               
theorem quarticPhase_cubic_ratio_of_curvature
    {μ ν μnew r s μ₁ ν₁ μnew₁ r₁ s₁ x ε ε₁ D : ℝ}
    (hμ : 0 < μ) (hμ₁ : 0 < μ₁) (hμnew : 0 < μnew) (hμnew₁ : 0 < μnew₁)
    (hr : r ≠ 0) (hr₁ : r₁ ≠ 0) (hx : 0 < r*x+s) (hx₁ : 0 < r₁*x+s₁)
    (he : |μ/μnew-1+4*ν*minorArcCoordinate μ r s x/μ| ≤ ε)
    (he₁ : |μ₁/μnew₁-1+4*ν₁*minorArcCoordinate μ₁ r₁ s₁ x/μ₁| ≤ ε₁)
    (hcurv : |iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) x-
      iteratedDeriv 2 (quarticPhase μ ν r s μ₁ ν₁ r₁ s₁) x| ≤ D) :
    |μnew₁*(r₁*x+s₁)^3/(μnew*(r*x+s)^3)-1| ≤
      (3*μnew₁*(r₁*x+s₁)^3/2)*
        (D+2*ε/(3*μ*(r*x+s)^3)+2*ε₁/(3*μ₁*(r₁*x+s₁)^3)) := by
  have h0 := quarticBranch_curvature_transfer hμ hμnew.ne' hr hx he
  have h1 := quarticBranch_curvature_transfer hμ₁ hμnew₁.ne' hr₁ hx₁ he₁
  rw [rationalBranch_second hμ.ne' hr hx.ne',quarticBranch_second hμ.ne' hr hx.ne'] at h0
  rw [rationalBranch_second hμ₁.ne' hr₁ hx₁.ne',quarticBranch_second hμ₁.ne' hr₁ hx₁.ne'] at h1
  rw [rationalPhase_second hμ.ne' hr hμ₁.ne' hr₁ hx.ne' hx₁.ne',
    quarticPhase_second hμ.ne' hr hμ₁.ne' hr₁ hx.ne' hx₁.ne'] at hcurv
  have hsplit : ∀ a b c d e f : ℝ,
      |e-f| ≤ |(a-b)-(c-d)|+|a-c-e|+|b-d-f| := by
    intro a b c d e f
    calc
      _ = |((a-b)-(c-d))-(a-c-e)+(b-d-f)| := by congr 1; ring
      _ ≤ |((a-b)-(c-d))-(a-c-e)|+|b-d-f| := abs_add_le _ _
      _ ≤ |(a-b)-(c-d)|+|a-c-e|+|b-d-f| :=
        add_le_add (abs_sub _ _) le_rfl
  have hb := (hsplit _ _ _ _ _ _).trans (add_le_add (add_le_add hcurv h0) h1)
  rw [rationalPhase_cubic_ratio_abs_eq hμnew.ne' hr hμnew₁.ne' hr₁ hx.ne' hx₁.ne',
    abs_of_pos hμnew₁,abs_of_pos hx₁,
    rationalPhase_second hμnew.ne' hr hμnew₁.ne' hr₁ hx.ne' hx₁.ne']
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact hb.trans_eq (by ring)



                                                                      
                                                                        
                                                                   
                                                                    
theorem physicalModelPhase_quartic_four_point_third_condition
    {σ δ T M N R L a b c d h E α β : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ e r v s : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hL : 0 < L)
    (hNL : (L*N)^2 ≤ M*R)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ y ∈ Set.Icc a d, ∀ i, x₁ y i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hden : ∀ y ∈ Set.Icc a d, ∀ i, 0 < r i*y+s i)
    (hh : 0 < h) (hab : h ≤ b-a) (hbc : h ≤ c-b) (hcd : h ≤ d-c) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun y i => (round (x₁ y i):ℝ)-(round (x₀ i):ℝ)
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let μnew := fun y i => iteratedDeriv 3 (f i) (round (x₁ y i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (round (x₀ i))/24
    let D := fun y i => r i*y+s i
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let H := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let ε := quarticReciprocalConstant σ δ*R^2/(L*N)^2
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=e i/r i) →
    (∀ y ∈ Set.Icc a d, ∀ i, iteratedDeriv 2 (f i) (x₁ y i)/2=(e i*y+v i)/D y i) →
    (∀ y ∈ Set.Icc a d, ∀ i, |n y i|^2 ≤ M*R) →
    (∀ y ∈ ({a,b,c,d} : Finset ℝ), |α*y+β-g y+H y| ≤ E) →
    ∃ z ∈ Set.Ioo a d,
      |μnew z 1*(D z 1)^3/(μnew z 0*(D z 0)^3)-1| ≤
        (3*μnew z 1*(D z 1)^3/2)*
          (4*E/h^2+2*ε/(3*μ 0*(D z 0)^3)+2*ε/(3*μ 1*(D z 1)^3)) := by
  let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
  let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
  let μnew := fun y i => iteratedDeriv 3 (f i) (round (x₁ y i))/6
  let ν := fun i => iteratedDeriv 4 (f i) (round (x₀ i))/24
  let ε := quarticReciprocalConstant σ δ*R^2/(L*N)^2
  change _ → _ → _ → _ → _
  intro hbase hpoint hsquare hres
  have hF₂ (i) := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl
  have ha (i) := physicalModelPhase_halfCurvature_round_error hσ.le (hF₂ i)
    hT hM (hA i) (hW i) (hx₀ i)
  have hκ := modelPhaseThirdLower_pos hσ
  have hμ (i) : 0 < μ i := lt_of_lt_of_le (by positivity)
    (physicalModelPhase_cubicCoefficient_bounds hσ hδ (hF₂ i) hT hM (hA i) (hW i) (ha i).1).1
  obtain ⟨z,hz,hcurv⟩ := quarticPhase_four_point_curvature
    (hμ 0).ne' (hr 0) (hμ 1).ne' (hr 1) hh hab hbc hcd
    (fun y hy => (hden y hy 0).ne') (fun y hy => (hden y hy 1).ne') hres
  have hz' : z ∈ Set.Icc a d := ⟨hz.1.le,hz.2.le⟩
  have hb (i) := physicalModelPhase_halfCurvature_round_error hσ.le (hF₂ i)
    hT hM (hA i) (hW i) (hx₁ z hz' i)
  have hμnew (i) : 0 < μnew z i := lt_of_lt_of_le (by positivity)
    (physicalModelPhase_cubicCoefficient_bounds hσ hδ (hF₂ i) hT hM (hA i) (hW i) (hb i).1).1
  have he (i) : |μ i/μnew z i-1+4*ν i*minorArcCoordinate (μ i) (r i) (s i) z/μ i| ≤ ε := by
    have hrm := physicalModelPhase_quartic_reciprocal_coordinate_source_scale
      (N := L*N) (u := z) (t := 1) hσ hδ (hF i) hT hM (mul_pos hL hN) hR hNL
      (hA i) (hW i) (hx₀ i) (hx₁ z hz' i) (hr i) (by norm_num)
      (by simpa only [mul_one] using (hden z hz' i).ne')
      (hdet i) (hbase i) (by simpa only [mul_one] using hpoint z hz' i)
      (hsquare z hz' i)
    simpa only [div_one] using hrm
  refine ⟨z,hz,?_⟩
  exact quarticPhase_cubic_ratio_of_curvature (hμ 0) (hμ 1) (hμnew 0) (hμnew 1)
    (hr 0) (hr 1) (hden z hz' 0) (hden z hz' 1) (he 0) (he 1) hcurv

open scoped Classical

                                                                    
                                                                        
                                                                   
theorem quartic_four_point_third_source_budget
    {μ₀ μ₁ μnew d₀ d₁ d K L N R Γ C : ℝ}
    (hμ₀ : 0 < μ₀) (hμ₁ : 0 < μ₁)
    (hd : 0 < d) (hL : 0 < L) (hN : 0 < N)
    (hK : 0 ≤ K) (hΓ : 0 ≤ Γ) (hC : 0 ≤ C)
    (hd₀ : d ≤ d₀) (hd₁ : d ≤ d₁) (hD₁ : d₁ ≤ 2*d)
    (hcoef₀ : μnew ≤ Γ*μ₀) (hcoef₁ : μnew ≤ Γ*μ₁) :
    (3*μnew*d₁^3/2)*
      (4*(6*K*μ₀*R^2*d)/(3*μ₀*d^2*L*N)^2+
        2*(C*R^2/(L*N)^2)/(3*μ₀*d₀^3)+
        2*(C*R^2/(L*N)^2)/(3*μ₁*d₁^3)) ≤
      Γ*(32*K+9*C)*R^2/(L^2*N^2) := by
  have hd₀pos := hd.trans_le hd₀
  have hd₁pos := hd.trans_le hd₁
  have hrat₀ : μnew/μ₀ ≤ Γ := (div_le_iff₀ hμ₀).mpr hcoef₀
  have hrat₁ : μnew/μ₁ ≤ Γ := (div_le_iff₀ hμ₁).mpr hcoef₁
  have hpow : d₁^3 ≤ 8*d^3 := by nlinarith only [pow_le_pow_left₀ hd₁pos.le hD₁ 3]
  have hpow₀ : d^3 ≤ d₀^3 := pow_le_pow_left₀ hd.le hd₀ 3
  have hdrel : d₁^3/d₀^3 ≤ 8 := (div_le_iff₀ (by positivity : 0 < d₀^3)).mpr
    (hpow.trans (mul_le_mul_of_nonneg_left hpow₀ (by norm_num)))
  have hdscale : d₁^3/d^3 ≤ 8 := (div_le_iff₀ (by positivity : 0 < d^3)).mpr hpow
  have hfirst : (4*K*(μnew/μ₀)*(d₁^3/d^3))*R^2/(L^2*N^2) ≤
      (32*K*Γ)*R^2/(L^2*N^2) := by
    have hh : 4*K*(μnew/μ₀)*(d₁^3/d^3) ≤ 4*K*Γ*8 := by gcongr
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg R)
    exact hh.trans_eq (by ring)
  have hsecond : ((μnew/μ₀)*(d₁^3/d₀^3)*C)*R^2/(L^2*N^2) ≤
      (8*Γ*C)*R^2/(L^2*N^2) := by
    have hh : (μnew/μ₀)*(d₁^3/d₀^3)*C ≤ Γ*8*C := by gcongr
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg R)
    exact hh.trans_eq (by ring)
  have hthird : ((μnew/μ₁)*C)*R^2/(L^2*N^2) ≤
      (Γ*C)*R^2/(L^2*N^2) := by gcongr
  calc
    _ = (4*K*(μnew/μ₀)*(d₁^3/d^3))*R^2/(L^2*N^2)+
        ((μnew/μ₀)*(d₁^3/d₀^3)*C)*R^2/(L^2*N^2)+
        ((μnew/μ₁)*C)*R^2/(L^2*N^2) := by field_simp; ring
    _ ≤ (32*K*Γ)*R^2/(L^2*N^2)+(8*Γ*C)*R^2/(L^2*N^2)+
        (Γ*C)*R^2/(L^2*N^2) := add_le_add (add_le_add hfirst hsecond) hthird
    _ = _ := by ring



                                                                      
                                                                        
                                                                   
                                                           
theorem physicalModelPhase_quartic_long_block_third_condition
    {σ δ T M N R L d K α β : ℝ} (x : Fin 4 → ℝ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ e r v s : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hL : 0 < L)
    (hNL : (L*N)^2 ≤ M*R) (hd : 0 < d) (hK : 0 ≤ K)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ y ∈ Set.Icc (x 0) (x 3), ∀ i,
      x₁ y i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hden : ∀ y ∈ Set.Icc (x 0) (x 3), ∀ i, d ≤ r i*y+s i)
    (hdenUpper : ∀ y ∈ Set.Icc (x 0) (x 3), ∀ i, r i*y+s i ≤ 2*d)
    (hmono : StrictMono x) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun y i => (round (x₁ y i):ℝ)-(round (x₀ i):ℝ)
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let μnew := fun y i => iteratedDeriv 3 (f i) (round (x₁ y i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (round (x₀ i))/24
    let D := fun y i => r i*y+s i
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let H := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let G := minorArcCoordinate (μ 0) (r 0) (s 0)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=e i/r i) →
    (∀ y ∈ Set.Icc (x 0) (x 3), ∀ i,
      iteratedDeriv 2 (f i) (x₁ y i)/2=(e i*y+v i)/D y i) →
    (∀ y ∈ Set.Icc (x 0) (x 3), ∀ i, |n y i|^2 ≤ M*R) →
    (∀ j : Fin 3, L*N ≤ |G (x j.succ)-G (x j.castSucc)|) →
    (∀ j : Fin 4, |α*x j+β-g (x j)+H (x j)| ≤ K*R^2/|r 0*G (x j)|) →
    ∃ z ∈ Set.Ioo (x 0) (x 3),
      |μnew z 1*(D z 1)^3/(μnew z 0*(D z 0)^3)-1| ≤
        ((σ*(σ+1)+1)/modelPhaseThirdLower σ)*
          (32*K+9*quarticReciprocalConstant σ δ)*R^2/(L^2*N^2) := by
  let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
  let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
  let μnew := fun y i => iteratedDeriv 3 (f i) (round (x₁ y i))/6
  let ν := fun i => iteratedDeriv 4 (f i) (round (x₀ i))/24
  let Γ := (σ*(σ+1)+1)/modelPhaseThirdLower σ
  let Hgap := 3*μ 0*d^2*L*N
  let E := 6*K*μ 0*R^2*d
  change _ → _ → _ → _ → _ → _
  intro hbase hpoint hsquare hgap hres
  have hκ := modelPhaseThirdLower_pos hσ
  have hΓ : 0 ≤ Γ := by dsimp [Γ]; positivity
  have hF₂ (i) := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl
  have ha (i) := physicalModelPhase_halfCurvature_round_error hσ.le (hF₂ i)
    hT hM (hA i) (hW i) (hx₀ i)
  have hμbounds (i) := physicalModelPhase_cubicCoefficient_bounds hσ hδ
    (hF₂ i) hT hM (hA i) (hW i) (ha i).1
  have hμ (i) : 0 < μ i := lt_of_lt_of_le (by positivity) (hμbounds i).1
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans
    (approximateModelPhase_iteratedDeriv_error (hF 0)
      (heathBrownPhysicalPoint_mem_interior hM (hA 0) (hW 0) (ha 0).1) 4 le_rfl)
  have hC : 0 ≤ quarticReciprocalConstant σ δ := by
    have hC₂ := modelPhaseJetCoefficient_nonneg σ 2
    have hC₃ := modelPhaseJetCoefficient_nonneg σ 3
    have hC₄ := modelPhaseJetCoefficient_nonneg σ 4
    dsimp [quarticReciprocalConstant]
    positivity
  have hx (j : Fin 4) : x j ∈ Set.Icc (x 0) (x 3) :=
    ⟨hmono.monotone (by omega),hmono.monotone (by omega)⟩
  have hdenpos (y) (hy : y ∈ Set.Icc (x 0) (x 3)) (i) :
      0 < r i*y+s i := hd.trans_le (hden y hy i)
  have hGgap (j : Fin 3) : Hgap ≤ x j.succ-x j.castSucc := by
    have he := point_gap_of_minorArcCoordinate_gap (hμ 0).ne' (hr 0)
      (hmono.monotone j.castSucc_le_succ) hd (mul_pos hL hN).le
      (by simpa only [abs_of_pos (hdenpos _ (hx j.castSucc) 0)] using hden _ (hx j.castSucc) 0)
      (by simpa only [abs_of_pos (hdenpos _ (hx j.succ) 0)] using hden _ (hx j.succ) 0)
      (hgap j)
    convert he using 1
    rw [abs_of_pos (hμ 0)]
    ring
  have hE (j : Fin 4) :
      |α*x j+β-rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1) (x j)+
        quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1) (x j)| ≤ E := by
    apply (hres j).trans
    rw [scaled_minorArcCoordinate_abs (hμ 0).ne' (hr 0) (hdenpos _ (hx j) 0).ne',
      abs_of_pos (hμ 0),abs_of_pos (hdenpos _ (hx j) 0),one_div,div_inv_eq_mul]
    calc
      _ ≤ K*R^2*(3*μ 0*(2*d)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left (hdenUpper _ (hx j) 0)
          (mul_nonneg (by norm_num) (hμ 0).le)
      _ = _ := by dsimp [E]; ring
  obtain ⟨z,hz,hthird⟩ := physicalModelPhase_quartic_four_point_third_condition
    (h := Hgap) (E := E) hσ hδ hF hT hM hN hR hL hNL hA hW hx₀ hx₁ hr hdet hdenpos
    (by dsimp [Hgap]; have hh := hμ 0; positivity)
    (hGgap 0) (hGgap 1) (hGgap 2) hbase hpoint hsquare
    (by
      intro y hy
      simp only [Finset.mem_insert,Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> exact hE _)
  have hz' : z ∈ Set.Icc (x 0) (x 3) := ⟨hz.1.le,hz.2.le⟩
  have hb := physicalModelPhase_halfCurvature_round_error hσ.le (hF₂ 1)
    hT hM (hA 1) (hW 1) (hx₁ z hz' 1)
  have hnew := physicalModelPhase_cubicCoefficient_bounds hσ hδ
    (hF₂ 1) hT hM (hA 1) (hW 1) hb.1
  have hcoef (i) : μnew z 1 ≤ Γ*μ i := by
    calc
      _ ≤ (σ*(σ+1)+1)*T/(6*M^3) := hnew.2
      _ = Γ*(modelPhaseThirdLower σ*T/(6*M^3)) := by dsimp [Γ]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hμbounds i).1 hΓ
  refine ⟨z,hz,hthird.trans ?_⟩
  exact quartic_four_point_third_source_budget (hμ 0) (hμ 1)
    hd hL hN hK hΓ hC (hden z hz' 0) (hden z hz' 1) (hdenUpper z hz' 1)
    (hcoef 0) (hcoef 1)



                                                                   
                                                                     
                                                        
theorem ratio_relative_perturbation_of_inverse_bound
    {a u v ε η Γ : ℝ} (hv : 0 < v) (hΓ : 0 ≤ Γ)
    (ha : |a-1| ≤ ε) (hu : |u-1| ≤ η) (hvv : |v-1| ≤ η)
    (hub : |u| ≤ Γ) (hvinv : 1/v ≤ Γ) :
    |a*u/v-1| ≤ Γ^2*ε+2*Γ*η := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans ha
  have hη : 0 ≤ η := (abs_nonneg _).trans hu
  have hdiff : |u-v| ≤ 2*η := by
    calc
      _ = |(u-1)-(v-1)| := by congr 1; ring
      _ ≤ |u-1|+|v-1| := abs_sub _ _
      _ ≤ _ := by linarith only [hu,hvv]
  calc
    _ = |(u/v)*(a-1)+(1/v)*(u-v)| := by congr 1; field_simp; ring
    _ ≤ |(u/v)*(a-1)|+|(1/v)*(u-v)| := abs_add_le _ _
    _ = |u| * (1/v)*|a-1|+(1/v)*|u-v| := by
      rw [abs_mul,abs_div,abs_of_pos hv,abs_mul,
        abs_of_pos (one_div_pos.mpr hv)]
      ring
    _ ≤ Γ*Γ*ε+Γ*(2*η) := by gcongr
    _ = _ := by ring



                                                                     
                                                                        
                                                                     
          
theorem physicalModelPhase_quartic_two_long_block_witnesses
    {σ δ T M N R L d K α β : ℝ} (x : Fin 8 → ℝ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ e r v s : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hL : 0 < L)
    (hNL : (L*N)^2 ≤ M*R) (hd : 0 < d) (hK : 0 ≤ K)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      x₁ y i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hden : ∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, d ≤ r i*y+s i)
    (hdenUpper : ∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, r i*y+s i ≤ 2*d)
    (hmono : StrictMono x) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun y i => (round (x₁ y i):ℝ)-(round (x₀ i):ℝ)
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let μnew := fun y i => iteratedDeriv 3 (f i) (round (x₁ y i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (round (x₀ i))/24
    let D := fun y i => r i*y+s i
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let H := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let G := minorArcCoordinate (μ 0) (r 0) (s 0)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=e i/r i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      iteratedDeriv 2 (f i) (x₁ y i)/2=(e i*y+v i)/D y i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, |n y i|^2 ≤ M*R) →
    (∀ j : Fin 7, L*N ≤ |G (x j.succ)-G (x j.castSucc)|) →
    (∀ j : Fin 8, |α*x j+β-g (x j)+H (x j)| ≤ K*R^2/|r 0*G (x j)|) →
    ∃ z₀ ∈ Set.Ioo (x 0) (x 3), ∃ z₁ ∈ Set.Ioo (x 4) (x 7),
      L*N/4 ≤ |G z₁-G z₀| ∧
      (∀ z ∈ ({z₀,z₁} : Finset ℝ),
        |μnew z 1*(D z 1)^3/(μnew z 0*(D z 0)^3)-1| ≤
          ((σ*(σ+1)+1)/modelPhaseThirdLower σ)*
            (32*K+9*quarticReciprocalConstant σ δ)*R^2/(L^2*N^2)) := by

  let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
  let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
  let G := minorArcCoordinate (μ 0) (r 0) (s 0)
  let xl := fun j : Fin 4 => x ⟨j.val,by omega⟩
  let xr := fun j : Fin 4 => x ⟨j.val+4,by omega⟩
  change _ → _ → _ → _ → _ → _
  intro hbase hpoint hsquare hgap hres
  have hleft : Set.Icc (x 0) (x 3) ⊆ Set.Icc (x 0) (x 7) :=
    fun y hy => ⟨hy.1,hy.2.trans (hmono.monotone (by decide))⟩
  have hright : Set.Icc (x 4) (x 7) ⊆ Set.Icc (x 0) (x 7) :=
    fun y hy => ⟨(hmono.monotone (by decide)).trans hy.1,hy.2⟩
  have hxl : StrictMono xl := by
    intro i j hij
    exact hmono hij
  have hxr : StrictMono xr := by
    intro i j hij
    apply hmono
    change i.val+4 < j.val+4
    exact Nat.add_lt_add_right hij 4
  have hgl (j : Fin 3) : L*N ≤ |G (xl j.succ)-G (xl j.castSucc)| :=
    hgap ⟨j.val,by omega⟩
  have hgr (j : Fin 3) : L*N ≤ |G (xr j.succ)-G (xr j.castSucc)| := by
    fin_cases j
    · exact hgap 4
    · exact hgap 5
    · exact hgap 6
  obtain ⟨z₀,hz₀,hthird₀⟩ := physicalModelPhase_quartic_long_block_third_condition
    xl hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀
    (fun y hy => hx₁ y (hleft hy)) hr hdet
    (fun y hy => hden y (hleft hy)) (fun y hy => hdenUpper y (hleft hy)) hxl
    hbase (fun y hy => hpoint y (hleft hy)) (fun y hy => hsquare y (hleft hy))
    hgl (fun j => hres ⟨j.val,by omega⟩)
  obtain ⟨z₁,hz₁,hthird₁⟩ := physicalModelPhase_quartic_long_block_third_condition
    xr hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀
    (fun y hy => hx₁ y (hright hy)) hr hdet
    (fun y hy => hden y (hright hy)) (fun y hy => hdenUpper y (hright hy)) hxr
    hbase (fun y hy => hpoint y (hright hy)) (fun y hy => hsquare y (hright hy))
    hgr (fun j => hres ⟨j.val+4,by omega⟩)
  change z₀ ∈ Set.Ioo (x 0) (x 3) at hz₀
  change z₁ ∈ Set.Ioo (x 4) (x 7) at hz₁
  have hz₀' := hleft ⟨hz₀.1.le,hz₀.2.le⟩
  have hz₁' := hright ⟨hz₁.1.le,hz₁.2.le⟩
  have hF₂ := approximateModelPhase_mono (hF 0) (by norm_num : 2 ≤ 4) le_rfl
  have ha := physicalModelPhase_halfCurvature_round_error hσ.le hF₂ hT hM (hA 0) (hW 0) (hx₀ 0)
  have hκ := modelPhaseThirdLower_pos hσ
  have hμ : 0 < μ 0 := lt_of_lt_of_le (by positivity)
    (physicalModelPhase_cubicCoefficient_bounds hσ hδ hF₂ hT hM (hA 0) (hW 0) ha.1).1
  have hx (j : Fin 8) : x j ∈ Set.Icc (x 0) (x 7) :=
    ⟨hmono.monotone (by omega),hmono.monotone (by omega)⟩
  have hdpos (y) (hy : y ∈ Set.Icc (x 0) (x 7)) : 0 < r 0*y+s 0 :=
    hd.trans_le (hden y hy 0)
  have hmid := point_gap_of_minorArcCoordinate_gap hμ.ne' (hr 0)
    (hmono.monotone (by decide : (3:Fin 8) ≤ 4)) hd (mul_pos hL hN).le
    (by simpa only [abs_of_pos (hdpos _ (hx 3))] using hden _ (hx 3) 0)
    (by simpa only [abs_of_pos (hdpos _ (hx 4))] using hden _ (hx 4) 0)
    (hgap 3)
  have hsp : 3*|μ 0| * d^2*(L*N) ≤ z₁-z₀ := by
    linarith only [hmid,hz₀.2,hz₁.1]
  have hg := minorArcCoordinate_gap_lower hμ.ne' (hr 0)
    (by positivity : 0 < 3*|μ 0| * d^2*(L*N)) (by positivity : 0 < 2*d)
    (hdpos _ hz₀').ne' (hdpos _ hz₁').ne'
    (by simpa only [abs_of_pos (hdpos _ hz₀')] using hdenUpper _ hz₀' 0)
    (by simpa only [abs_of_pos (hdpos _ hz₁')] using hdenUpper _ hz₁' 0) hsp
  refine ⟨z₀,hz₀,z₁,hz₁,?_,?_⟩
  · convert hg using 1
    field_simp
    ring
  · intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hthird₀
    · exact hthird₁



                                                                      
                                                                      
                                                                        
                                                                     
theorem physicalModelPhase_interval_root_family
    {σ δ T M A W l w L U x₀ H e r v s : ℝ} {F : ℝ → ℝ}
    (hσ : 0 ≤ σ) (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hL : L ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hU : U ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hdenl : 0 < r*l+s) (hdenw : 0 < r*w+s)
    (hLdist : |L-x₀| ≤ H) (hUdist : |U-x₀| ≤ H) :
    let f := heathBrownPhysicalPhase F T M A 1
    let I := Set.uIcc (iteratedDeriv 2 f L/2) (iteratedDeriv 2 f U/2)
    (e*l+v)/(r*l+s) ∈ I → (e*w+v)/(r*w+s) ∈ I →
    ∃ ρ : ℝ → ℝ,
      (∀ y ∈ Set.Icc l w, ρ y ∈ Set.uIcc L U ∧
        ρ y ∈ Set.Ioo (1/2:ℝ) (W-1/2) ∧
        iteratedDeriv 2 f (ρ y)/2=(e*y+v)/(r*y+s) ∧
        (round (ρ y):ℝ) ∈ Set.Ioo 0 W ∧
        |(round (ρ y):ℝ)-(round x₀:ℝ)| ≤ H+1) ∧
      (∀ y ∈ Set.Icc l w, ∀ z ∈ Set.Icc l w,
        |(round (ρ y):ℝ)-(round (ρ z):ℝ)| ≤ |U-L|+1) := by
  classical
  let f := heathBrownPhysicalPhase F T M A 1
  change _ → _ → _
  intro hleft hright
  have hex (y : ℝ) : ∃ z : ℝ, y ∈ Set.Icc l w →
      z ∈ Set.uIcc L U ∧ z ∈ Set.Ioo (1/2:ℝ) (W-1/2) ∧
      iteratedDeriv 2 f z/2=(e*y+v)/(r*y+s) ∧
      (round z:ℝ) ∈ Set.Ioo 0 W ∧
      |(round z:ℝ)-(round x₀:ℝ)| ≤ H+1 := by
    by_cases hy : y ∈ Set.Icc l w
    · have htarget := Set.uIcc_subset_uIcc hleft hright
        (affine_ratio_mem_endpoint_interval (r₁ := e) (s₁ := v) hy hdenl hdenw
          (affine_positive_between hy hdenl hdenw))
      obtain ⟨z,hz,hroot,hrnd,_⟩ := physicalModelPhase_exists_rounded_halfCurvature_center
        hσ hF hT hM hA hW hL hU htarget
      have hbuf : z ∈ Set.Ioo (1/2:ℝ) (W-1/2) := by
        rcases Set.mem_uIcc.mp hz with hh | hh
        · exact ⟨hL.1.trans_le hh.1,hh.2.trans_lt hU.2⟩
        · exact ⟨hU.1.trans_le hh.1,hh.2.trans_lt hL.2⟩
      have hdist : |z-x₀| ≤ H := by
        have hl := abs_le.mp hLdist
        have hu := abs_le.mp hUdist
        rcases Set.mem_uIcc.mp hz with hh | hh
        · exact abs_le.mpr ⟨by linarith only [hl.1,hh.1],by linarith only [hu.2,hh.2]⟩
        · exact abs_le.mpr ⟨by linarith only [hu.1,hh.1],by linarith only [hl.2,hh.2]⟩
      exact ⟨z,fun _ => ⟨hz,hbuf,hroot,hrnd,
        (rounded_displacement_bound z x₀).trans (add_le_add hdist le_rfl)⟩⟩
    · exact ⟨0,fun h => False.elim (hy h)⟩
  choose ρ hρ using hex
  refine ⟨ρ,hρ,?_⟩
  intro y hy z hz
  have hd : |ρ y-ρ z| ≤ |U-L| := by
    have hh := Real.dist_le_of_mem_uIcc (hρ y hy).1 (hρ z hz).1
    simpa only [Real.dist_eq,abs_sub_comm L U] using hh
  exact (rounded_displacement_bound (ρ y) (ρ z)).trans (add_le_add hd le_rfl)



                                                                         
                                                                            
                                                                             
                                                                         
theorem scaled_paired_C4_nontriangular_resonance_compression
    (f f₁ : ℝ → ℝ) {A B A₁ B₁ L E xl xr yl yr : ℝ}
    (a b c d : ℤ) (hdet : a*d-b*c=1) (hc : c ≠ 0) (hL : 0 < L)
    (hf : ∀ z ∈ Set.Ioo A B, ContDiffAt ℝ 4 f z)
    (hthree : ∀ z ∈ Set.Ioo A B, L ≤ iteratedDeriv 3 f z)
    (hfour : ∀ z ∈ Set.Ioo A B, |iteratedDeriv 4 f z| ≤ |(c:ℝ)| *L^2/16)
    (hf₁ : ∀ z ∈ Set.Ioo A₁ B₁, ContDiffAt ℝ 4 f₁ z)
    (hthree₁ : ∀ z ∈ Set.Ioo A₁ B₁, L ≤ iteratedDeriv 3 f₁ z)
    (hfour₁ : ∀ z ∈ Set.Ioo A₁ B₁, |iteratedDeriv 4 f₁ z| ≤ |(c:ℝ)| *L^2/16)
    (hxl : xl ∈ Set.Ioo A B) (hxr : xr ∈ Set.Ioo A B)
    (hyl : yl ∈ Set.Ioo A₁ B₁) (hyr : yr ∈ Set.Ioo A₁ B₁) :
    let h := fun z => iteratedDeriv 2 f z/2
    let h₁ := fun z => iteratedDeriv 2 f₁ z/2
    let t := fun z => (c:ℝ)*z+d
    h xl ≤ h xr →
    ((a:ℝ)*h xl+b)/t (h xl)=h₁ yl →
    ((a:ℝ)*h xr+b)/t (h xr)=h₁ yr →
    ((1:ℝ)/2 ≤ t (h xl) ∧ t (h xl) ≤ 2) →
    ((1:ℝ)/2 ≤ t (h xr) ∧ t (h xr) ≤ 2) →
    |(iteratedDeriv 3 f₁ yl/6)*t (h xl)^3-iteratedDeriv 3 f xl/6| ≤ E →
    |(iteratedDeriv 3 f₁ yr/6)*t (h xr)^3-iteratedDeriv 3 f xr/6| ≤ E →
    h xr-h xl ≤ 48*E/(|(c:ℝ)| *L) := by
  intro h h₁ t hlr hmapl hmapr htl htr hel her
  let k : ℝ := |(c:ℝ)|
  let fs : ℝ → ℝ := fun z => k*f z
  let fs₁ : ℝ → ℝ := fun z => k*f₁ z
  have hk : 0 < k := abs_pos.mpr (by exact_mod_cast hc)
  have hsign : (c.sign:ℝ)*k=(c:ℝ) := by
    dsimp only [k]
    exact_mod_cast Int.sign_mul_abs c
  have hsignabs : |(c.sign:ℝ)|=1 := by exact_mod_cast Int.abs_sign_of_ne_zero hc
  have hsignne : c.sign ≠ 0 := by
    intro hh
    rw [hh,Int.cast_zero,abs_zero] at hsignabs
    norm_num at hsignabs
  have hdet' : a*d-(|c| *b)*c.sign=1 := by
    have hh := congrArg (fun z : ℤ => b*z) (Int.sign_mul_abs c)
    nlinarith only [hdet,hh]
  have hjet (n : ℕ) (z : ℝ) : iteratedDeriv n fs z=k*iteratedDeriv n f z :=
    iteratedDeriv_const_mul_field k f
  have hjet₁ (n : ℕ) (z : ℝ) : iteratedDeriv n fs₁ z=k*iteratedDeriv n f₁ z :=
    iteratedDeriv_const_mul_field k f₁
  have hprofile₁ (z : ℝ) : iteratedDeriv 2 fs₁ z/2=k*h₁ z := by
    rw [hjet₁]
    dsimp only [h₁]
    ring
  have hprofile (z : ℝ) : iteratedDeriv 2 fs z/2=k*h z := by
    rw [hjet]
    dsimp only [h]
    ring
  have htarg (z : ℝ) : (c.sign:ℝ)*(k*h z)+d=t (h z) := by
    dsimp only [t]
    nlinarith only [congrArg (fun u : ℝ => u*h z) hsign]
  have hmap (z : ℝ) :
      ((a:ℝ)*(k*h z)+((|c| *b:ℤ):ℝ))/((c.sign:ℝ)*(k*h z)+d)=
        k*(((a:ℝ)*h z+b)/t (h z)) := by
    rw [htarg]
    push_cast
    dsimp only [k]
    ring
  have hcf (z) (hz : z ∈ Set.Ioo A B) : ContDiffAt ℝ 4 fs z :=
    contDiffAt_const.mul (hf z hz)
  have hthree' (z) (hz : z ∈ Set.Ioo A B) : k*L ≤ iteratedDeriv 3 fs z := by
    rw [hjet]
    exact mul_le_mul_of_nonneg_left (hthree z hz) hk.le
  have hfour' (z) (hz : z ∈ Set.Ioo A B) : |iteratedDeriv 4 fs z| ≤ (k*L)^2/16 := by
    rw [hjet,abs_mul,abs_of_pos hk]
    calc
      _ ≤ k*(k*L^2/16) := mul_le_mul_of_nonneg_left (hfour z hz) hk.le
      _ = _ := by ring
  have hcf₁ (z) (hz : z ∈ Set.Ioo A₁ B₁) : ContDiffAt ℝ 4 fs₁ z :=
    contDiffAt_const.mul (hf₁ z hz)
  have hthree₁' (z) (hz : z ∈ Set.Ioo A₁ B₁) : k*L ≤ iteratedDeriv 3 fs₁ z := by
    rw [hjet₁]
    exact mul_le_mul_of_nonneg_left (hthree₁ z hz) hk.le
  have hfour₁' (z) (hz : z ∈ Set.Ioo A₁ B₁) : |iteratedDeriv 4 fs₁ z| ≤ (k*L)^2/16 := by
    rw [hjet₁,abs_mul,abs_of_pos hk]
    calc
      _ ≤ k*(k*L^2/16) := mul_le_mul_of_nonneg_left (hfour₁ z hz) hk.le
      _ = _ := by ring
  have hres (z w : ℝ)
      (hz : |(iteratedDeriv 3 f₁ w/6)*t (h z)^3-iteratedDeriv 3 f z/6| ≤ E) :
      |(iteratedDeriv 3 fs₁ w/6)*((c.sign:ℝ)*(iteratedDeriv 2 fs z/2)+d)^3-
        iteratedDeriv 3 fs z/6| ≤ k*E := by
    rw [hjet₁ 3 w,hjet 3 z,hprofile,htarg]
    rw [show k*iteratedDeriv 3 f₁ w/6*t (h z)^3-k*iteratedDeriv 3 f z/6=
      k*((iteratedDeriv 3 f₁ w/6)*t (h z)^3-iteratedDeriv 3 f z/6) by ring,
      abs_mul,abs_of_pos hk]
    exact mul_le_mul_of_nonneg_left hz hk.le
  have hb := bourgain_paired_C4_nontriangular_resonance_compression fs fs₁ a (|c| *b) c.sign d
    hdet' hsignne (mul_pos hk hL) hcf hthree' hfour' hcf₁ hthree₁' hfour₁' hxl hxr hyl hyr
    (by dsimp only; rw [hprofile,hprofile]; exact mul_le_mul_of_nonneg_left hlr hk.le)
    (by dsimp only; rw [hprofile,hprofile₁,hmap,hmapl])
    (by dsimp only; rw [hprofile,hprofile₁,hmap,hmapr])
    (by dsimp only; rwa [hprofile,htarg])
    (by dsimp only; rwa [hprofile,htarg])
    (hres xl yl hel) (hres xr yr her)
  dsimp only at hb
  rw [hprofile,hprofile,hsignabs,one_mul] at hb
  apply (mul_le_mul_iff_of_pos_left hk).mp
  calc
    k*(h xr-h xl) = k*h xr-k*h xl := by ring
    _ ≤ 48*(k*E)/(k*L) := hb
    _ = k*(48*E/(|(c:ℝ)| *L)) := by change _ = k*(48*E/(k*L)); field_simp


                                                                         
                                                                     
                                                                        
open Filter
open scoped Topology
theorem curvature_fiber_hasDerivAt
    (H : ℝ → ℝ → ℝ) (ρ : ℝ → ℝ) {z hy hx : ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hbase : ρ z ∈ I) (hx0 : hx ≠ 0)
    (hH : HasStrictFDerivAt (fun p : ℝ × ℝ => H p.1 p.2)
      (hy • ContinuousLinearMap.fst ℝ ℝ ℝ + hx • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (z,ρ z))
    (hroot : ∀ᶠ w in 𝓝 z, ρ w ∈ I ∧ H w (ρ w)=H z (ρ z))
    (huniq : ∀ᶠ w in 𝓝 z, Set.InjOn (H w) I) :
    HasDerivAt ρ (-hy/hx) z := by
  let L : ℝ × ℝ →L[ℝ] ℝ :=
    hy • ContinuousLinearMap.fst ℝ ℝ ℝ + hx • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hleft : L.comp (ContinuousLinearMap.inl ℝ ℝ ℝ)=hy • ContinuousLinearMap.id ℝ ℝ := by
    ext
    simp [L]
  have hright : L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)=hx • ContinuousLinearMap.id ℝ ℝ := by
    ext
    simp [L]
  have hcomp₁ : (L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)).comp
      (hx⁻¹ • ContinuousLinearMap.id ℝ ℝ)=ContinuousLinearMap.id ℝ ℝ := by
    rw [hright]
    ext
    simp [hx0]
  have hcomp₂ : (hx⁻¹ • ContinuousLinearMap.id ℝ ℝ).comp
      (L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ))=ContinuousLinearMap.id ℝ ℝ := by
    rw [hright]
    ext
    simp [hx0]
  have hinv : (L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)).IsInvertible :=
    ContinuousLinearMap.IsInvertible.of_inverse hcomp₁ hcomp₂
  have hinveq : (L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)).inverse=
      hx⁻¹ • ContinuousLinearMap.id ℝ ℝ :=
    ContinuousLinearMap.inverse_eq hcomp₁ hcomp₂
  change HasStrictFDerivAt (fun p : ℝ × ℝ => H p.1 p.2) L (z,ρ z) at hH
  let ψ := hH.implicitFunctionOfProdDomain hinv
  have hψder : HasDerivAt ψ (-hy/hx) z := by
    have hh := (hH.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv).hasFDerivAt
    rw [hinveq,hleft] at hh
    have hd := hh.hasDerivAt
    convert hd using 1
    simp only [ContinuousLinearMap.comp_apply,neg_apply,
      smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul]
    ring
  have hψin : ∀ᶠ w in 𝓝 z, ψ w ∈ I :=
    (hH.tendsto_implicitFunctionOfProdDomain hinv) (hI.mem_nhds hbase)
  have hψroot := hH.eventually_apply_implicitFunctionOfProdDomain hinv
  have heq : ρ =ᶠ[𝓝 z] ψ := by
    filter_upwards [hroot,huniq,hψin,hψroot] with w hw hu hi he
    exact hu hw.1 hi (hw.2.trans he.symm)
  exact hψder.congr_of_eventuallyEq heq



                                                                      
                                                                       
                                                                         
theorem curvature_fiber_vertical_profile_hasDerivAt
    (H : ℝ × ℝ → ℝ) (ρ : ℝ → ℝ) {z : ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hbase : ρ z ∈ I)
    (hH : ContDiffAt ℝ 2 H (z,ρ z))
    (hx0 : fderiv ℝ H (z,ρ z) (0,1) ≠ 0)
    (hroot : ∀ᶠ w in 𝓝 z, ρ w ∈ I ∧ H (w,ρ w)=H (z,ρ z))
    (huniq : ∀ᶠ w in 𝓝 z, Set.InjOn (fun u => H (w,u)) I) :
    let G := fun p => fderiv ℝ H p (0,1)
    let B := fun p => fderiv ℝ H p (1,0)
    HasDerivAt (fun w => G (w,ρ w))
      (G (z,ρ z)*deriv (fun u => B (z,u)/G (z,u)) (ρ z)) z := by
  intro G B
  let p : ℝ × ℝ := (z,ρ z)
  let vx : ℝ × ℝ := (0,1)
  let vy : ℝ × ℝ := (1,0)
  let D₂ := fderiv ℝ (fderiv ℝ H) p
  have hsplit : fderiv ℝ H p =
      B p • ContinuousLinearMap.fst ℝ ℝ ℝ + G p • ContinuousLinearMap.snd ℝ ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro v
    have hv : v=v.1 • vy+v.2 • vx := by dsimp [vx,vy]; ext <;> simp
    calc
      _ = fderiv ℝ H p (v.1 • vy+v.2 • vx) := congrArg (fderiv ℝ H p) hv
      _ = _ := by
        rw [map_add,map_smul,map_smul]
        change v.1*B p+v.2*G p=B p*v.1+G p*v.2
        ring
  have hstrict := hH.hasStrictFDerivAt (by norm_num : (2:WithTop ℕ∞) ≠ 0)
  have hstrict' : HasStrictFDerivAt (fun q : ℝ × ℝ => H (q.1,q.2))
      (B p • ContinuousLinearMap.fst ℝ ℝ ℝ + G p • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (z,ρ z) := by
    change HasStrictFDerivAt H (fderiv ℝ H p) (z,ρ z) at hstrict
    rw [hsplit] at hstrict
    exact hstrict
  have hρ := curvature_fiber_hasDerivAt (fun w u => H (w,u)) ρ hI hbase hx0
    hstrict' hroot huniq
  change HasDerivAt ρ (-B p/G p) z at hρ
  have hcurve : HasDerivAt (fun w => (w,ρ w)) (1,-B p/G p) z :=
    (hasDerivAt_id z).prodMk hρ
  have hD : HasFDerivAt (fderiv ℝ H) D₂ p :=
    (hH.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1 ≤ 2)).differentiableAt_one.hasFDerivAt
  have hDc : HasDerivAt (fun w => fderiv ℝ H (w,ρ w)) (D₂ (1,-B p/G p)) z :=
    hD.comp_hasDerivAt z hcurve
  have hprofile : HasDerivAt (fun w => G (w,ρ w)) (D₂ (1,-B p/G p) vx) z := by
    have hh : HasDerivAt (fun w => (fderiv ℝ H (w,ρ w)) vx)
        (D₂ (1,-B p/G p) vx+(fderiv ℝ H (z,ρ z)) 0) z :=
      hDc.clm_apply (hasDerivAt_const z vx)
    simpa only [G,vx,map_zero,add_zero] using hh
  have hline : HasDerivAt (fun u : ℝ => (z,u)) vx (ρ z) :=
    (hasDerivAt_const (ρ z) z).prodMk (hasDerivAt_id (ρ z))
  have hDl : HasDerivAt (fun u => fderiv ℝ H (z,u)) (D₂ vx) (ρ z) :=
    hD.comp_hasDerivAt (ρ z) hline
  have hxder : HasDerivAt (fun u => G (z,u)) (D₂ vx vx) (ρ z) := by
    have hh : HasDerivAt (fun u => (fderiv ℝ H (z,u)) vx)
        (D₂ vx vx+(fderiv ℝ H (z,ρ z)) 0) (ρ z) :=
      hDl.clm_apply (hasDerivAt_const (ρ z) vx)
    simpa only [G,vx,map_zero,add_zero] using hh
  have hbder : HasDerivAt (fun u => B (z,u)) (D₂ vx vy) (ρ z) := by
    have hh : HasDerivAt (fun u => (fderiv ℝ H (z,u)) vy)
        (D₂ vx vy+(fderiv ℝ H (z,ρ z)) 0) (ρ z) :=
      hDl.clm_apply (hasDerivAt_const (ρ z) vy)
    simpa only [B,vy,map_zero,add_zero] using hh
  have hquot := hbder.div hxder hx0
  have hq : deriv (fun u => B (z,u)/G (z,u)) (ρ z)=
      (D₂ vx vy*G p-B p*D₂ vx vx)/(G p)^2 := by
    exact hquot.deriv
  rw [hq]
  have hsymm : D₂ vy vx=D₂ vx vy :=
    hH.isSymmSndFDerivAt (by norm_num) vy vx
  have hv : (1,-B p/G p)=vy+(-B p/G p) • vx := by
    dsimp [vx,vy]
    ext <;> simp
  convert hprofile using 1
  change G p*((D₂ vx vy*G p-B p*D₂ vx vx)/(G p)^2)=D₂ (1,-B p/G p) vx
  rw [hv,map_add,map_smul,add_apply,smul_apply,
    smul_eq_mul,hsymm]
  have hGp : G p ≠ 0 := hx0
  field_simp [hGp]
  ring



                                                                        
                                                                      
                                                      
theorem curvature_fiber_parameter_compression
    (H : ℝ × ℝ → ℝ) (ρ : ℝ → ℝ)
    {a b A B s t q L K E : ℝ}
    (hL : 0 < L) (hK : 0 < K) (hst : s ≤ t)
    (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b)
    (hH : ∀ y ∈ Set.Ioo a b, ∀ x ∈ Set.Ioo A B, ContDiffAt ℝ 2 H (y,x))
    (hroot : ∀ y ∈ Set.Ioo a b, ρ y ∈ Set.Ioo A B ∧ H (y,ρ y)=q) :
    let G := fun p => fderiv ℝ H p (0,1)
    let Z := fun p => fderiv ℝ H p (1,0)
    (∀ y ∈ Set.Ioo a b, ∀ x ∈ Set.Ioo A B, L ≤ |G (y,x)|) →
    (∀ y ∈ Set.Ioo a b, ∀ x ∈ Set.Ioo A B,
      K ≤ |deriv (fun u => Z (y,u)/G (y,u)) x|) →
    |G (t,ρ t)-G (s,ρ s)| ≤ E →
    t-s ≤ E/(L*K) := by
  intro G Z hG hQ hE
  have hLK : 0 < L*K := mul_pos hL hK
  have hE0 : 0 ≤ E := (abs_nonneg _).trans hE
  have hHx y (hy : y ∈ Set.Ioo a b) x (hx : x ∈ Set.Ioo A B) :
      HasDerivAt (fun u => H (y,u)) (G (y,x)) x :=
    ((hH y hy x hx).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt x
      ((hasDerivAt_const x y).prodMk (hasDerivAt_id x))
  have huniq y (hy : y ∈ Set.Ioo a b) : Set.InjOn (fun x => H (y,x)) (Set.Ioo A B) := by
    have hneval x v (hx : x ∈ Set.Ioo A B) (hv : v ∈ Set.Ioo A B) (hlt : x < v) :
        H (y,x) ≠ H (y,v) := by
      intro he
      have hsub : Set.Icc x v ⊆ Set.Ioo A B :=
        fun w hw => ⟨hx.1.trans_le hw.1,hw.2.trans_lt hv.2⟩
      obtain ⟨w,hw,hd⟩ := exists_hasDerivAt_eq_slope
        (fun u => H (y,u)) (fun u => G (y,u)) hlt
        (fun u hu => (hHx y hy u (hsub hu)).continuousAt.continuousWithinAt)
        (fun u hu => hHx y hy u (hsub ⟨hu.1.le,hu.2.le⟩))
      have hh := hG y hy w (hsub ⟨hw.1.le,hw.2.le⟩)
      rw [he,sub_self,zero_div] at hd
      rw [hd,abs_zero] at hh
      linarith only [hh,hL]
    intro x hx v hv he
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hneval x v hx hv hlt he
    · exact hneval v x hv hx hgt he.symm
  let F := fun y => G (y,ρ y)
  let F' := fun y => G (y,ρ y)*deriv (fun u => Z (y,u)/G (y,u)) (ρ y)
  have hder y (hy : y ∈ Set.Ioo a b) : HasDerivAt F (F' y) y := by
    apply curvature_fiber_vertical_profile_hasDerivAt H ρ isOpen_Ioo (hroot y hy).1
      (hH y hy _ (hroot y hy).1)
    · exact abs_pos.mp (hL.trans_le (hG y hy _ (hroot y hy).1))
    · filter_upwards [isOpen_Ioo.mem_nhds hy] with w hw
      exact ⟨(hroot w hw).1,(hroot w hw).2.trans (hroot y hy).2.symm⟩
    · filter_upwards [isOpen_Ioo.mem_nhds hy] with w hw
      exact huniq w hw
  rcases hst.eq_or_lt with he | hlt
  · subst t
    simp only [sub_self]
    positivity
  have hsub : Set.Icc s t ⊆ Set.Ioo a b :=
    fun y hy => ⟨hs.1.trans_le hy.1,hy.2.trans_lt ht.2⟩
  obtain ⟨w,hw,hd⟩ := exists_hasDerivAt_eq_slope F F' hlt
    (fun y hy => (hder y (hsub hy)).continuousAt.continuousWithinAt)
    (fun y hy => hder y (hsub ⟨hy.1.le,hy.2.le⟩))
  have hwJ := hsub ⟨hw.1.le,hw.2.le⟩
  have hb : L*K ≤ |F' w| := by
    dsimp only [F']
    rw [abs_mul]
    exact mul_le_mul (hG w hwJ _ (hroot w hwJ).1)
      (hQ w hwJ _ (hroot w hwJ).1) hK.le (abs_nonneg _)
  rw [hd,abs_div,abs_of_pos (sub_pos.mpr hlt)] at hb
  have hh := (le_div_iff₀ (sub_pos.mpr hlt)).mp hb
  apply (le_div_iff₀ hLK).mpr
  change |F t-F s| ≤ E at hE
  nlinarith only [hh,hE]



                                                                   
                                                                        
                                                                   
theorem curvature_fiber_parameter_count
    (S : Finset ℝ) (H : ℝ × ℝ → ℝ) (ρ : ℝ → ℝ)
    {a b A B q L K E J g : ℝ}
    (hL : 0 < L) (hK : 0 < K) (hE : 0 ≤ E) (hJ : 0 < J)
    (hS : ∀ y ∈ S, y ∈ Set.Ioo a b)
    (hsep : ∀ y ∈ S, ∀ w ∈ S, y ≠ w → 1 ≤ J*|y-w|)
    (hH : ∀ y ∈ Set.Ioo a b, ∀ x ∈ Set.Ioo A B, ContDiffAt ℝ 2 H (y,x))
    (hroot : ∀ y ∈ Set.Ioo a b, ρ y ∈ Set.Ioo A B ∧ H (y,ρ y)=q) :
    let G := fun p => fderiv ℝ H p (0,1)
    let Z := fun p => fderiv ℝ H p (1,0)
    (∀ y ∈ Set.Ioo a b, ∀ x ∈ Set.Ioo A B, L ≤ |G (y,x)|) →
    (∀ y ∈ Set.Ioo a b, ∀ x ∈ Set.Ioo A B,
      K ≤ |deriv (fun u => Z (y,u)/G (y,u)) x|) →
    (∀ y ∈ S, |G (y,ρ y)-g| ≤ E) →
    (S.card:ℝ) ≤ 1+2*E*J/(L*K) := by
  classical
  intro G Z hG hQ hres
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.card_empty,Nat.cast_zero]
    positivity
  let l := S.min' hne
  let r := S.max' hne
  have hl : l ∈ S := S.min'_mem hne
  have hr : r ∈ S := S.max'_mem hne
  have hlr : l ≤ r := S.min'_le r hr
  have hdiff : |G (r,ρ r)-G (l,ρ l)| ≤ 2*E := by
    calc
      _ = |(G (r,ρ r)-g)-(G (l,ρ l)-g)| := by congr 1; ring
      _ ≤ |G (r,ρ r)-g|+|G (l,ρ l)-g| := abs_sub _ _
      _ ≤ _ := by linarith only [hres r hr,hres l hl]
  have hwidth := curvature_fiber_parameter_compression H ρ hL hK hlr
    (hS l hl) (hS r hr) hH hroot hG hQ hdiff
  let V := S.image (fun y => J*y)
  have hinj : Function.Injective (fun y : ℝ => J*y) :=
    fun _ _ he => (mul_right_inj' hJ.ne').mp he
  have hVs : ∀ u ∈ V, ∀ v ∈ V, u ≠ v → 1 ≤ |u-v| := by
    intro u hu v hv huv
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    rw [←mul_sub,abs_mul,abs_of_pos hJ]
    exact hsep y hy w hw (fun he => huv (congrArg (fun z => J*z) he))
  have hb := oneSeparated_card_cast_le_interval_length_add_one V hVs
    (sub_nonneg.mpr (mul_le_mul_of_nonneg_left hlr hJ.le)) (by
      intro v hv
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
      exact ⟨mul_le_mul_of_nonneg_left (S.min'_le y hy) hJ.le,
        mul_le_mul_of_nonneg_left (S.le_max' y hy) hJ.le⟩)
  have hcard : V.card=S.card := Finset.card_image_of_injOn hinj.injOn
  rw [hcard] at hb
  calc
    (S.card:ℝ) ≤ J*r-J*l+1 := hb
    _ = J*(r-l)+1 := by ring
    _ ≤ J*(2*E/(L*K))+1 :=
      add_le_add (mul_le_mul_of_nonneg_left hwidth hJ.le) le_rfl
    _ = _ := by ring



                                                                     
                                                                       
                                                                     
                                                                             
open scoped ContDiff
theorem difference_logarithmic_ratio_lower
    (f : ℝ → ℝ) {x z η y l c U V : ℝ}
    (hη : 0 < η) (hy : 1 ≤ y) (hy' : y ≤ 2) (hz : z=x+η*y)
    (hl : 0 < l) (hc : 0 < c) (hU : 0 < U) (hV : 0 < V)
    (hf : ∀ w ∈ Set.Icc x z, ContDiffAt ℝ 2 f w)
    (hvalue : ∀ w ∈ Set.Icc x z, l ≤ |f w| ∧ |f w| ≤ V)
    (hder : ∀ w ∈ Set.Icc x z, c ≤ |deriv f w| ∧ |deriv f w| ≤ U)
    (hdet : ∀ w ∈ Set.Icc x z, c ≤ |f w*iteratedDeriv 2 f w-(deriv f w)^2|) :
    f x-f z ≠ 0 ∧ c*(z-x) ≤ |f x-f z| ∧
    l^2*c/(2*U^2*V^2) ≤
      |η*(f z*deriv f x-deriv f z*f x)/(f x-f z)^2| := by
  have hyd : 0 < y := by linarith only [hy]
  have hdist : z-x=η*y := by linarith only [hz]
  have hxz : x < z := by nlinarith only [hz,mul_pos hη hyd]
  have hxI : x ∈ Set.Icc x z := ⟨le_rfl,hxz.le⟩
  have hzI : z ∈ Set.Icc x z := ⟨hxz.le,le_rfl⟩
  have hn w (hw : w ∈ Set.Icc x z) : f w ≠ 0 :=
    abs_pos.mp (hl.trans_le (hvalue w hw).1)
  have hd w (hw : w ∈ Set.Icc x z) : HasDerivAt f (deriv f w) w :=
    ((hf w hw).differentiableAt (by norm_num)).hasDerivAt
  have hdd w (hw : w ∈ Set.Icc x z) :
      HasDerivAt (deriv f) (iteratedDeriv 2 f w) w := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using
      ((contDiffAt_iteratedDeriv_finite (n:=1) (j:=1) (hf w hw)).differentiableAt_one).hasDerivAt
  obtain ⟨u,hu,he⟩ := exists_hasDerivAt_eq_slope f (deriv f) hxz
    (fun w hw => (hd w hw).continuousAt.continuousWithinAt)
    (fun w hw => hd w ⟨hw.1.le,hw.2.le⟩)
  have huI : u ∈ Set.Icc x z := ⟨hu.1.le,hu.2.le⟩
  have hDne : f x-f z ≠ 0 := by
    intro hh
    have heq : f z=f x := by linarith only [hh]
    rw [heq,sub_self,zero_div] at he
    have hb := (hder u huI).1
    rw [he,abs_zero] at hb
    linarith only [hb,hc]
  have hD : |f x-f z| ≤ U*(z-x) := by
    have hb := (hder u huI).2
    rw [he,abs_div,abs_of_pos (sub_pos.mpr hxz)] at hb
    rw [abs_sub_comm]
    exact (div_le_iff₀ (sub_pos.mpr hxz)).mp hb
  let g := fun w => deriv f w/f w
  let gp := fun w => (f w*iteratedDeriv 2 f w-(deriv f w)^2)/(f w)^2
  have hgd w (hw : w ∈ Set.Icc x z) : HasDerivAt g (gp w) w := by
    have hh := (hdd w hw).div (hd w hw) (hn w hw)
    convert hh using 1
    dsimp only [gp]
    ring
  have hgp w (hw : w ∈ Set.Icc x z) : c/V^2 ≤ |gp w| := by
    dsimp only [gp]
    rw [abs_div,abs_of_nonneg (sq_nonneg (f w))]
    have hfw := hn w hw
    apply div_le_div₀ (by positivity) (hdet w hw) (by positivity)
    have hh := pow_le_pow_left₀ (abs_nonneg (f w)) (hvalue w hw).2 2
    simpa only [sq_abs] using hh
  obtain ⟨v,hv,hve⟩ := exists_hasDerivAt_eq_slope g gp hxz
    (fun w hw => (hgd w hw).continuousAt.continuousWithinAt)
    (fun w hw => hgd w ⟨hw.1.le,hw.2.le⟩)
  have hb := hgp v ⟨hv.1.le,hv.2.le⟩
  rw [hve,abs_div,abs_of_pos (sub_pos.mpr hxz)] at hb
  have hdiff : c/V^2*(z-x) ≤ |g x-g z| := by
    rw [abs_sub_comm]
    exact (le_div_iff₀ (sub_pos.mpr hxz)).mp hb
  let A := f z*deriv f x-deriv f z*f x
  have hA : l^2*(c/V^2*(z-x)) ≤ |A| := by
    have hprod : l^2 ≤ |f z| *|f x| := by
      simpa only [pow_two] using mul_le_mul (hvalue z hzI).1 (hvalue x hxI).1
        hl.le (abs_nonneg _)
    calc
      _ ≤ (|f z| *|f x|)*|g x-g z| :=
        mul_le_mul hprod hdiff (by positivity) (by positivity)
      _ = |A| := by
        rw [←abs_mul,←abs_mul]
        congr 1
        dsimp only [g,A]
        field_simp [hn x hxI,hn z hzI]
  have hDsq : (f x-f z)^2 ≤ U^2*(z-x)^2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg (f x-f z)) hD 2
    simpa only [sq_abs,mul_pow] using hh
  have hshort : (z-x)^2 ≤ 2*η*(z-x) := by
    rw [hdist]
    nlinarith only [mul_nonneg hyd.le (sub_nonneg.mpr hy'),sq_nonneg η]
  have hA' : l^2*c*(z-x) ≤ V^2*|A| := by
    have hh := mul_le_mul_of_nonneg_left hA (sq_nonneg V)
    field_simp at hh
    nlinarith only [hh]
  have hchain : l^2*c*(f x-f z)^2 ≤ 2*U^2*V^2*η*|A| := by
    calc
      _ ≤ l^2*c*(U^2*(z-x)^2) :=
        mul_le_mul_of_nonneg_left hDsq (by positivity)
      _ ≤ l^2*c*(U^2*(2*η*(z-x))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hshort (sq_nonneg U)) (by positivity)
      _ = 2*U^2*η*(l^2*c*(z-x)) := by ring
      _ ≤ 2*U^2*η*(V^2*|A|) := mul_le_mul_of_nonneg_left hA' (by positivity)
      _ = _ := by ring
  have hDlower : c*(z-x) ≤ |f x-f z| := by
    have hb := (hder u huI).1
    rw [he,abs_div,abs_of_pos (sub_pos.mpr hxz)] at hb
    rw [abs_sub_comm]
    exact (le_div_iff₀ (sub_pos.mpr hxz)).mp hb
  refine ⟨hDne,hDlower,?_⟩
  rw [abs_div,abs_mul,abs_of_pos hη,abs_of_nonneg (sq_nonneg (f x-f z))]
  apply (div_le_div_iff₀ (show 0 < 2*U^2*V^2 by positivity)
    (sq_pos_of_ne_zero hDne)).mpr
  change l^2*c*(f x-f z)^2 ≤ η*|A| *(2*U^2*V^2)
  nlinarith only [hchain]


                                                                      
                                                                       
                                                                            
theorem difference_curvature_mixed_jets
    (f : ℝ → ℝ) {σ η y x : ℝ}
    (hσ : σ ≠ 0) (hη : η ≠ 0)
    (hx : ContDiffAt ℝ 2 f x) (hz : ContDiffAt ℝ 2 f (x+η*y))
    (hd : deriv f x-deriv f (x+η*y) ≠ 0) :
    let H := fun p : ℝ × ℝ => (f p.2-f (p.2+η*p.1))/(σ*η)
    let G := fun p => fderiv ℝ H p (0,1)
    let Z := fun p => fderiv ℝ H p (1,0)
    ContDiffAt ℝ 2 H (y,x) ∧
    G (y,x)=(deriv f x-deriv f (x+η*y))/(σ*η) ∧
    Z (y,x)= -deriv f (x+η*y)/σ ∧
    deriv (fun u => Z (y,u)/G (y,u)) x =
      η*(deriv f (x+η*y)*iteratedDeriv 2 f x-
        iteratedDeriv 2 f (x+η*y)*deriv f x)/
        (deriv f x-deriv f (x+η*y))^2 := by
  dsimp only
  let H := fun p : ℝ × ℝ => (f p.2-f (p.2+η*p.1))/(σ*η)
  let G := fun p => fderiv ℝ H p (0,1)
  let Z := fun p => fderiv ℝ H p (1,0)
  change ContDiffAt ℝ 2 H (y,x) ∧ G (y,x)=_ ∧ Z (y,x)=_ ∧ _
  have hfirst u (hu : DifferentiableAt ℝ f u)
      (hv : DifferentiableAt ℝ f (u+η*y)) :
      G (y,u)=(deriv f u-deriv f (u+η*y))/(σ*η) ∧
      Z (y,u)= -deriv f (u+η*y)/σ := by
    have hp : HasFDerivAt (fun p : ℝ × ℝ => p.2+η*p.1)
        (ContinuousLinearMap.snd ℝ ℝ ℝ+η • ContinuousLinearMap.fst ℝ ℝ ℝ) (y,u) :=
      hasFDerivAt_snd.add (hasFDerivAt_fst.const_mul η)
    have hh := ((hu.hasDerivAt.comp_hasFDerivAt (y,u) hasFDerivAt_snd).sub
      (hv.hasDerivAt.comp_hasFDerivAt (y,u) hp)).mul_const (σ*η)⁻¹
    have he : fderiv ℝ H (y,u) =
        (σ*η)⁻¹ • (deriv f u • ContinuousLinearMap.snd ℝ ℝ ℝ -
          deriv f (u+η*y) •
            (ContinuousLinearMap.snd ℝ ℝ ℝ+η • ContinuousLinearMap.fst ℝ ℝ ℝ)) :=
      hh.fderiv
    constructor
    · dsimp only [G]
      rw [he]
      change (σ*η)⁻¹*(deriv f u*1-deriv f (u+η*y)*(1+η*0))=_
      ring
    · dsimp only [Z]
      rw [he]
      change (σ*η)⁻¹*(deriv f u*0-deriv f (u+η*y)*(0+η*1))=_
      field_simp
      ring
  have hreg : ContDiffAt ℝ 2 H (y,x) :=
    ((hx.comp (y,x) contDiffAt_snd).sub
      (hz.comp (y,x) (contDiffAt_snd.add (contDiffAt_const.mul contDiffAt_fst)))).div_const (σ*η)
  have hfx := hx.differentiableAt (by norm_num)
  have hfz := hz.differentiableAt (by norm_num)
  obtain ⟨hG,hZ⟩ := hfirst x hfx hfz
  refine ⟨hreg,hG,hZ,?_⟩
  have hx1 : ContDiffAt ℝ 1 f x := hx.of_le (by norm_num)
  have hz1 : ContDiffAt ℝ 1 f (x+η*y) := hz.of_le (by norm_num)
  have hznear : ∀ᶠ u in 𝓝 x, ContDiffAt ℝ 1 f (u+η*y) :=
    ((continuousAt_id.add_const (η*y)).tendsto).eventually
      (hz1.eventually (by norm_num))
  have heq : (fun u => Z (y,u)/G (y,u)) =ᶠ[𝓝 x]
      (fun u => -η*deriv f (u+η*y)/(deriv f u-deriv f (u+η*y))) := by
    filter_upwards [hx1.eventually (by norm_num),hznear] with u hu hv
    obtain ⟨hgu,hzu⟩ := hfirst u (hu.differentiableAt_one) (hv.differentiableAt_one)
    rw [hgu,hzu]
    field_simp
  have hdx : HasDerivAt (deriv f) (iteratedDeriv 2 f x) x := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using
      (contDiffAt_iteratedDeriv_finite (n:=1) (j:=1) hx).differentiableAt_one.hasDerivAt
  have hdz : HasDerivAt (fun u => deriv f (u+η*y))
      (iteratedDeriv 2 f (x+η*y)) x := by
    have hh : HasDerivAt (deriv f) (iteratedDeriv 2 f (x+η*y)) (x+η*y) := by
      simpa only [iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using
        (contDiffAt_iteratedDeriv_finite (n:=1) (j:=1) hz).differentiableAt_one.hasDerivAt
    convert hh.comp x ((hasDerivAt_id x).add_const (η*y)) using 1
    · rfl
    · simp only [mul_one]
  rw [heq.deriv_eq]
  calc
    _ = ((-η*iteratedDeriv 2 f (x+η*y))*(deriv f x-deriv f (x+η*y))-
        (-η*deriv f (x+η*y))*(iteratedDeriv 2 f x-iteratedDeriv 2 f (x+η*y)))/
        (deriv f x-deriv f (x+η*y))^2 :=
      ((hdz.const_mul (-η)).div (hdx.sub hdz) hd).deriv
    _ = _ := by ring


                                                                        
                                                                         
                                                                       
                                                                           
theorem approximateModelPhase_buffered_extension_uniform (Q : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (σ δ h : ℝ) (F : ℝ → ℝ),
      0 ≤ δ → 0 < h → h < 1/4 →
      Expdb.IsApproximateModelPhaseFunction F σ (Q+1) δ →
      ∃ Fext : ℝ → ℝ,
        (∀ x, 0 < x → ContDiffAt ℝ ∞ Fext x) ∧
        (∀ x ∈ Set.Icc (1+2*h) (2-2*h), Fext x=F x) ∧
        (∀ x ∈ Set.Icc (1/2:ℝ) 3, ∀ n ≤ Q,
          |iteratedDeriv (n+1) Fext x-iteratedDeriv n (Expdb.modelPhase σ) x| ≤ C*δ) := by
  obtain ⟨C,hC,hpaste⟩ := taylorPastedExtension_uniform_jets (Q+1) (D:=3) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro σ δ h F hδ hh hhmax hF
  let c₀ := F (3/2)-referenceModelPrimitive σ (3/2)
  let E := fun x => F x-referenceModelPrimitive σ x-c₀
  have hE x (hx : x ∈ Set.Ioo (1:ℝ) 2) : ContDiffAt ℝ ∞ E x :=
    ((approximateModelPhase_contDiffAt hF hx).sub
      (referenceModelPrimitive_contDiffAt σ (by linarith only [hx.1]))).sub contDiffAt_const
  have hjet n (hn : n ≤ Q+1) x (hx : x ∈ Set.Ioo (1:ℝ) 2) :
      |iteratedDeriv (n+1) E x| ≤ δ := by
    have he : E = fun u => -c₀+(F u-referenceModelPrimitive σ u) := by
      funext u
      dsimp only [E]
      ring
    have hFx : ContDiffAt ℝ (n+1) F x :=
      (approximateModelPhase_contDiffAt hF hx).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl (n+1))
    have hRx : ContDiffAt ℝ (n+1) (referenceModelPrimitive σ) x :=
      (referenceModelPrimitive_contDiffAt σ (by linarith only [hx.1])).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl (n+1))
    rw [he,iteratedDeriv_const_add (by omega),iteratedDeriv_fun_sub hFx hRx,
      referenceModelPrimitive_iteratedDeriv σ (by linarith only [hx.1]) n]
    exact approximateModelPhase_iteratedDeriv_error hF hx n hn
  have hzero x (hx : x ∈ Set.Ioo (1:ℝ) 2) : |E x| ≤ δ := by
    have hd : ∀ u ∈ Set.Ioo (1:ℝ) 2, DifferentiableAt ℝ E u :=
      fun u hu => (hE u hu).differentiableAt (by simp)
    have hb : ∀ u ∈ Set.Ioo (1:ℝ) 2, ‖deriv E u‖ ≤ δ := by
      intro u hu
      simpa only [Nat.zero_add,iteratedDeriv_one,Real.norm_eq_abs] using hjet 0 (by omega) u hu
    have hnorm := Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_Ioo 1 2)
      (show (3/2:ℝ) ∈ Set.Ioo (1:ℝ) 2 by norm_num) hx
    have he0 : E (3/2)=0 := by dsimp [E,c₀]; ring
    rw [he0,sub_zero,Real.norm_eq_abs,Real.norm_eq_abs] at hnorm
    apply hnorm.trans
    have hdist : |x-3/2| ≤ 1 := abs_le.mpr ⟨by linarith only [hx.1],by linarith only [hx.2]⟩
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hdist hδ
  have hb x (hx : x ∈ Set.Ioo (1:ℝ) 2) j (hj : j ≤ Q+1+1) :
      |iteratedDeriv j E x| ≤ δ := by
    cases j with
    | zero => simpa only [iteratedDeriv_zero] using hzero x hx
    | succ n => exact hjet n (by omega) x hx
  let P := taylorPastedExtension E (Q+1) 1 2 h
  have hP : ContDiff ℝ ∞ P := taylorPastedExtension_contDiff hh hE (Q+1)
  let Fext := fun x => c₀+(referenceModelPrimitive σ x+P x)
  refine ⟨Fext,?_,?_,?_⟩
  · intro x hx
    exact contDiffAt_const.add ((referenceModelPrimitive_contDiffAt σ hx).add hP.contDiffAt)
  · intro x hx
    have he := taylorPastedExtension_agrees E (Q+1) hh hx
    change c₀+(referenceModelPrimitive σ x+P x)=F x
    rw [show P x=E x from he]
    dsimp only [E]
    ring
  · intro x hx n hn
    have hpx : |iteratedDeriv (n+1) P x| ≤ C*δ :=
      hpaste E 1 2 h x δ hh (by linarith only [hhmax]) (by linarith only [hhmax]) hE hb
        (abs_le.mpr ⟨by linarith only [hx.1,hhmax],by linarith only [hx.2,hh]⟩)
        (abs_le.mpr ⟨by linarith only [hx.1,hh],by linarith only [hx.2,hhmax]⟩)
        (n+1) (by omega)
    have hxpos : 0 < x := by linarith only [hx.1]
    have hRx : ContDiffAt ℝ (n+1) (referenceModelPrimitive σ) x :=
      (referenceModelPrimitive_contDiffAt σ hxpos).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl (n+1))
    have hPx : ContDiffAt ℝ (n+1) P x :=
      hP.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl (n+1))
    dsimp only [Fext]
    rw [iteratedDeriv_const_add (by omega),iteratedDeriv_fun_add hRx hPx,
      referenceModelPrimitive_iteratedDeriv σ hxpos n,add_sub_cancel_left]
    exact hpx


                                                                        
                                                                              
theorem buffered_phase_sharp_sum_comparison
    (F Fext : ℝ → ℝ) {N h : ℝ} (hN : 0 < N) (hh : 0 < h)
    (hagrees : ∀ x ∈ Set.Icc (1+2*h) (2-2*h), Fext x=F x)
    (T : ℝ) (a b : ℕ) (ha : N ≤ (a:ℝ)) (hb : (b:ℝ) ≤ 2*N) :
    ‖Expdb.exponentialSumAt F T N a b-Expdb.exponentialSumAt Fext T N a b‖ ≤ 16*N*h+4 := by
  let χ := modelPhaseBufferedCutoff ((a:ℝ)/N) ((b:ℝ)/N) (2*h)
  have hh2 : 0 < 2*h := by positivity
  have hχ : ∀ u ∈ tsupport χ, u ∈ Set.Icc (1+2*h) (2-2*h) := by
    intro u hu
    have hh' := modelPhaseBufferedCutoff_tsupport hh2 hu
    have ha' : 1 ≤ (a:ℝ)/N := (one_le_div hN).mpr ha
    have hb' : (b:ℝ)/N ≤ 2 := (div_le_iff₀ hN).mpr hb
    constructor <;> linarith only [hh'.1,hh'.2,ha',hb']
  have hker (n : ℤ) : modelPhaseWeightedKernel χ F T N n=modelPhaseWeightedKernel χ Fext T N n := by
    by_cases hz : χ ((n:ℝ)/N)=0
    · simp only [modelPhaseWeightedKernel,hz,Complex.ofReal_zero,zero_mul]
    · have hu : (n:ℝ)/N ∈ tsupport χ := subset_tsupport χ hz
      have he := hagrees _ (hχ _ hu)
      simp only [modelPhaseWeightedKernel,he]
  have hsum : (∑' n : ℤ, modelPhaseWeightedKernel χ F T N n)=
      ∑' n : ℤ, modelPhaseWeightedKernel χ Fext T N n := tsum_congr hker
  have h₁ := norm_modelPhase_source_sub_buffered_le hN hh2 F T a b
  have h₂ := norm_modelPhase_source_sub_buffered_le hN hh2 Fext T a b
  rw [←exponentialSumAt_eq_int_sum] at h₁ h₂
  change ‖Expdb.exponentialSumAt F T N a b-∑' n : ℤ, modelPhaseWeightedKernel χ F T N n‖ ≤ _ at h₁
  change ‖Expdb.exponentialSumAt Fext T N a b-∑' n : ℤ, modelPhaseWeightedKernel χ Fext T N n‖ ≤ _ at h₂
  rw [hsum] at h₁
  have ht := norm_sub_le_norm_sub_add_norm_sub (Expdb.exponentialSumAt F T N a b)
    (∑' n : ℤ, modelPhaseWeightedKernel χ Fext T N n)
    (Expdb.exponentialSumAt Fext T N a b)
  rw [norm_sub_rev (∑' n : ℤ, modelPhaseWeightedKernel χ Fext T N n)] at ht
  linarith only [h₁,h₂,ht]


                                                                     
                                                                       
                                                              
theorem approximateModelPhase_enlarged_sharp_transport (Q : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (σ δ N : ℝ) (F : ℝ → ℝ),
      0 ≤ δ → 1 ≤ N →
      Expdb.IsApproximateModelPhaseFunction F σ (Q+1) δ →
      ∃ Fext : ℝ → ℝ,
        (∀ x, 0 < x → ContDiffAt ℝ ∞ Fext x) ∧
        (∀ x ∈ Set.Icc (1/2:ℝ) 3, ∀ n ≤ Q,
          |iteratedDeriv (n+1) Fext x-iteratedDeriv n (Expdb.modelPhase σ) x| ≤ C*δ) ∧
        (∀ (T : ℝ) (a b : ℕ), N ≤ (a:ℝ) → (b:ℝ) ≤ 2*N →
          ‖Expdb.exponentialSumAt F T N a b-Expdb.exponentialSumAt Fext T N a b‖ ≤ 6) := by
  obtain ⟨C,hC,hbuild⟩ := approximateModelPhase_buffered_extension_uniform Q
  refine ⟨C,hC,?_⟩
  intro σ δ N F hδ hN hF
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  let h := 1/(8*N)
  have hh : 0 < h := by dsimp only [h]; positivity
  have hhmax : h < 1/4 := by
    dsimp only [h]
    apply (div_lt_iff₀ (by positivity : 0 < 8*N)).mpr
    linarith only [hN]
  obtain ⟨Fext,hreg,hagree,hjets⟩ := hbuild σ δ h F hδ hh hhmax hF
  refine ⟨Fext,hreg,hjets,?_⟩
  intro T a b ha hb
  have hh' := buffered_phase_sharp_sum_comparison F Fext hNpos hh hagree T a b ha hb
  have he : 16*N*h+4=6 := by dsimp only [h]; field_simp; ring
  rwa [he] at hh'



                                                                    
                                                                   
                                                                     
theorem positive_jets_difference_curvature_entry
    (F : ℝ → ℝ) {σ c U η x y : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hx : x ∈ Set.Icc (3/4:ℝ) (9/4)) (hy : y ∈ Set.Icc (1/2:ℝ) 3)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Set.Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w ∈ Set.Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (r : ℕ) (hr : 3 ≤ r) (hr' : r ≤ 4) :
    let H := fun p : ℝ × ℝ =>
      (iteratedDeriv (r-1) F p.2-iteratedDeriv (r-1) F (p.2+η*p.1))/(σ*η)
    let G := fun p => fderiv ℝ H p (0,1)
    let Z := fun p => fderiv ℝ H p (1,0)
    iteratedDeriv (r-1) (fun u => (F u-F (u+η*y))/(σ*η)) x=H (y,x) ∧
    ContDiffAt ℝ 2 H (y,x) ∧
    G (y,x)=(iteratedDeriv r F x-iteratedDeriv r F (x+η*y))/(σ*η) ∧
    c/(2*σ) ≤ |G (y,x)| ∧
    c^2*c/(6*U^4) ≤ |deriv (fun u => Z (y,u)/G (y,u)) x| := by
  intro H G Z
  have hy0 : 0 < y := by linarith only [hy.1]
  have hstep : 0 < η*y := mul_pos hη hy0
  have hI w (hw : w ∈ Set.Icc x (x+η*y)) : w ∈ Set.Icc (1/2:ℝ) 3 := by
    have hu := mul_le_mul hηmax hy.2 hy0.le (by norm_num : (0:ℝ) ≤ 1/8)
    constructor <;> linarith only [hx.1,hx.2,hw.1,hw.2,hu]
  have hpos w (hw : w ∈ Set.Icc x (x+η*y)) : 0 < w := by
    have hh := (hI w hw).1
    linarith only [hh]
  have hreg w (hw : w ∈ Set.Icc x (x+η*y)) : ContDiffAt ℝ 2 (iteratedDeriv r F) w :=
    (contDiffAt_iteratedDeriv_infty (hf w (hpos w hw)) r).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hv w (hw : w ∈ Set.Icc x (x+η*y)) :
      c ≤ |iteratedDeriv r F w| ∧ |iteratedDeriv r F w| ≤ U := by
    have ht := htests w (hI w hw)
    interval_cases r
    · exact ⟨ht 0,hbound w (hI w hw) 2 (by norm_num)⟩
    · exact ⟨ht 1,hbound w (hI w hw) 3 (by norm_num)⟩
  have hd w (hw : w ∈ Set.Icc x (x+η*y)) :
      c ≤ |deriv (iteratedDeriv r F) w| ∧ |deriv (iteratedDeriv r F) w| ≤ U := by
    rw [←iteratedDeriv_succ]
    have ht := htests w (hI w hw)
    interval_cases r
    · exact ⟨ht 1,hbound w (hI w hw) 3 (by norm_num)⟩
    · exact ⟨ht 2,hbound w (hI w hw) 4 (by norm_num)⟩
  have hdet w (hw : w ∈ Set.Icc x (x+η*y)) :
      c ≤ |iteratedDeriv r F w*iteratedDeriv 2 (iteratedDeriv r F) w-
        (deriv (iteratedDeriv r F) w)^2| := by
    have ht := htests w (hI w hw)
    interval_cases r
    · have hh : c ≤ |iteratedDeriv 3 F w*iteratedDeriv 5 F w-(iteratedDeriv 4 F w)^2| := ht 3
      simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hh
    · have hh : c ≤ |iteratedDeriv 4 F w*iteratedDeriv 6 F w-(iteratedDeriv 5 F w)^2| := ht 4
      simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hh
  obtain ⟨hne,hlo,hratio⟩ := difference_logarithmic_ratio_lower (iteratedDeriv r F)
    (η:=η*y) (y:=1) hstep le_rfl (by norm_num) (by ring) hc hc hU hU hreg hv hd hdet
  have hxpos : 0 < x := by linarith only [hx.1]
  have hzpos : 0 < x+η*y := add_pos hxpos hstep
  have hpred : deriv (iteratedDeriv (r-1) F)=iteratedDeriv r F := by
    rw [←iteratedDeriv_succ,Nat.sub_add_cancel (by omega : 1 ≤ r)]
  have hpred2 : iteratedDeriv 2 (iteratedDeriv (r-1) F)=iteratedDeriv (r+1) F := by
    rw [iteratedDeriv_real_comp_order]
    congr 1
    omega
  have hFx : ContDiffAt ℝ 2 (iteratedDeriv (r-1) F) x :=
    (contDiffAt_iteratedDeriv_infty (hf x hxpos) (r-1)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hFz : ContDiffAt ℝ 2 (iteratedDeriv (r-1) F) (x+η*y) :=
    (contDiffAt_iteratedDeriv_infty (hf _ hzpos) (r-1)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hne' : deriv (iteratedDeriv (r-1) F) x-deriv (iteratedDeriv (r-1) F) (x+η*y) ≠ 0 := by
    simpa only [hpred] using hne
  have hj := difference_curvature_mixed_jets (iteratedDeriv (r-1) F)
    hσ.ne' hη.ne' hFx hFz hne'
  have hGe : G (y,x)=(iteratedDeriv r F x-iteratedDeriv r F (x+η*y))/(σ*η) := by
    simpa only [hpred] using hj.2.1
  refine ⟨?_,hj.1,hGe,?_,?_⟩
  · have hF₀ : ContDiffAt ℝ (r-1) F x :=
      (hf x hxpos).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl (r-1))
    have hF₁ : ContDiffAt ℝ (r-1) (fun u => F (u+η*y)) x :=
      ((hf _ hzpos).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl (r-1))).comp x
        (contDiffAt_id.add contDiffAt_const)
    rw [iteratedDeriv_div_const,iteratedDeriv_fun_sub hF₀ hF₁,iteratedDeriv_comp_add_const]
  · rw [hGe,abs_div,abs_of_pos (mul_pos hσ hη)]
    apply (le_div_iff₀ (mul_pos hσ hη)).mpr
    have he : c/(2*σ)*(σ*η)=c*η/2 := by field_simp
    rw [he]
    apply le_trans ?_ hlo
    nlinarith only [mul_le_mul_of_nonneg_left hy.1 (mul_pos hc hη).le]
  · have hh := hj.2.2.2
    change deriv (fun u => Z (y,u)/G (y,u)) x = _ at hh
    rw [hh,hpred,hpred2]
    rw [←iteratedDeriv_succ] at hratio
    let V := |η*(iteratedDeriv r F (x+η*y)*iteratedDeriv (r+1) F x-
        iteratedDeriv (r+1) F (x+η*y)*iteratedDeriv r F x)/
        (iteratedDeriv r F x-iteratedDeriv r F (x+η*y))^2|
    have hs : c^2*c/(2*U^2*U^2) ≤ y*V := by
      calc
        _ ≤ _ := hratio
        _ = y*V := by
          rw [show η*y*(iteratedDeriv r F (x+η*y)*iteratedDeriv (r+1) F x-
              iteratedDeriv (r+1) F (x+η*y)*iteratedDeriv r F x)/
              (iteratedDeriv r F x-iteratedDeriv r F (x+η*y))^2 =
            y*(η*(iteratedDeriv r F (x+η*y)*iteratedDeriv (r+1) F x-
              iteratedDeriv (r+1) F (x+η*y)*iteratedDeriv r F x)/
              (iteratedDeriv r F x-iteratedDeriv r F (x+η*y))^2) by ring,
            abs_mul,abs_of_pos hy0]
    have hv0 : 0 ≤ V := abs_nonneg _
    have hu := mul_le_mul_of_nonneg_right hy.2 hv0
    have he : 3*(c^2*c/(6*U^4))=c^2*c/(2*U^2*U^2) := by field_simp; ring
    change c^2*c/(6*U^4) ≤ V
    nlinarith only [hs,hu,he]


                                                                        
                                                                         
                                                                         
theorem positive_difference_mixed_derivative
    (F : ℝ → ℝ) {σ η x y : ℝ}
    (hσ : σ ≠ 0) (hη : 0 < η) (hx : 0 < x) (hy : 0 < y)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (r s : ℕ) (hs : 0 < s) :
    iteratedDeriv r (fun u => iteratedDeriv s
      (fun v => (F u-F (u+η*v))/(σ*η)) y) x =
      -(η^(s-1)/σ)*iteratedDeriv (r+s) F (x+η*y) := by
  have he : (fun u => iteratedDeriv s
      (fun v => (F u-F (u+η*v))/(σ*η)) y) =ᶠ[𝓝 x]
      (fun u => -(η^(s-1)/σ)*iteratedDeriv s F (u+η*y)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with u hu
    have hreg : ∀ v ∈ Ioo (0:ℝ) (y+1), ContDiffAt ℝ ∞ F (η*v+u) := by
      intro v hv
      exact hf _ (add_pos (mul_pos hη hv.1) hu)
    have hj := sargos_iteratedDeriv_comp_affine_local hreg
      (show y ∈ Ioo (0:ℝ) (y+1) from ⟨hy,by linarith⟩) s
    rw [iteratedDeriv_div_const,iteratedDeriv_const_sub hs,iteratedDeriv_neg]
    have ha : (fun v => F (u+η*v))=(fun v => F (η*v+u)) := by
      funext v
      rw [add_comm u]
    rw [ha,hj,add_comm (η*y)]
    rw [show η^s=η^(s-1)*η by rw [←pow_succ,Nat.sub_add_cancel hs]]
    field_simp
  rw [he.iteratedDeriv_eq r,iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_add_const,iteratedDeriv_real_comp_order]


                                                              
                                                                      
theorem positive_jets_difference_mixed_upper
    (F : ℝ → ℝ) {σ U η x y : ℝ}
    (hσ : 0 < σ) (hU : 0 < U) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hx : x ∈ Icc (3/4:ℝ) (9/4)) (hy : y ∈ Icc (1/2:ℝ) 3)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (r s : ℕ) (hs : s ≤ 2) (hrs : r+s ≤ 6) :
    |iteratedDeriv r (fun u => iteratedDeriv s
      (fun v => (F u-F (u+η*v))/(σ*η)) y) x| ≤ 3*U/σ := by
  have hx0 : 0 < x := by linarith only [hx.1]
  have hy0 : 0 < y := by linarith only [hy.1]
  have hp : 0 < η*y := mul_pos hη hy0
  have hI w (hw : w ∈ Icc x (x+η*y)) : w ∈ Icc (1/2:ℝ) 3 := by
    have hu := mul_le_mul hηmax hy.2 hy0.le (by norm_num : (0:ℝ) ≤ 1/8)
    constructor <;> linarith only [hx.1,hx.2,hw.1,hw.2,hu]
  have hz : x+η*y ∈ Icc (1/2:ℝ) 3 := hI _ ⟨by linarith only [hp],le_rfl⟩
  cases s with
  | zero =>
    simp only [iteratedDeriv_zero]
    have hFx : ContDiffAt ℝ r F x :=
      (hf x hx0).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl r)
    have hFz : ContDiffAt ℝ r (fun u => F (u+η*y)) x :=
      ((hf _ (add_pos hx0 hp)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl r)).comp x
          (contDiffAt_id.add contDiffAt_const)
    rw [iteratedDeriv_div_const,iteratedDeriv_fun_sub hFx hFz,
      iteratedDeriv_comp_add_const,abs_div,abs_of_pos (mul_pos hσ hη)]
    have hreg w (hw : w ∈ Icc x (x+η*y)) :
        DifferentiableAt ℝ (iteratedDeriv r F) w :=
      (contDiffAt_iteratedDeriv_infty (hf w (by
        have hh := (hI w hw).1
        linarith only [hh])) r).differentiableAt (by simp)
    have hb w (hw : w ∈ Icc x (x+η*y)) : ‖deriv (iteratedDeriv r F) w‖ ≤ U := by
      rw [←iteratedDeriv_succ,Real.norm_eq_abs]
      exact hbound w (hI w hw) r (by omega)
    have hv := Convex.norm_image_sub_le_of_norm_deriv_le hreg hb
      (convex_Icc x (x+η*y))
      (show x+η*y ∈ Icc x (x+η*y) from ⟨by linarith only [hp],le_rfl⟩)
      (show x ∈ Icc x (x+η*y) from ⟨le_rfl,by linarith only [hp]⟩)
    rw [Real.norm_eq_abs,Real.norm_eq_abs,show x-(x+η*y)= -(η*y) by ring,
      abs_neg,abs_of_pos hp] at hv
    apply (div_le_iff₀ (mul_pos hσ hη)).mpr
    have he : 3*U/σ*(σ*η)=3*U*η := by field_simp
    rw [he]
    exact hv.trans (by nlinarith only [mul_le_mul_of_nonneg_left hy.2 (mul_pos hU hη).le])
  | succ s =>
    rw [positive_difference_mixed_derivative F hσ.ne' hη hx0 hy0 hf r (s+1) (by omega),
      abs_mul,abs_neg,abs_div,abs_of_pos hσ]
    have ht : |iteratedDeriv (r+(s+1)) F (x+η*y)| ≤ U := by
      have hh := hbound _ hz (r+s) (by omega)
      simpa only [Nat.add_assoc] using hh
    have hpow : |η^((s+1)-1)| ≤ 1 := by
      have he : η ≤ 1 := by linarith only [hηmax]
      simpa only [Nat.add_sub_cancel,abs_of_nonneg (pow_nonneg hη.le s)] using
        (pow_le_one₀ (n:=s) hη.le he)
    apply le_trans (mul_le_mul (div_le_div_of_nonneg_right hpow hσ.le) ht
      (abs_nonneg _) (by positivity : 0 ≤ 1/σ))
    calc
      1/σ*U=U/σ := by ring
      _ ≤ 3*U/σ := div_le_div_of_nonneg_right (by linarith only [hU]) hσ.le


                                                                      
                                                                       
theorem positive_jets_difference_spatial_lower
    (F : ℝ → ℝ) {σ c η x y : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hx : x ∈ Icc (3/4:ℝ) (9/4)) (hy : y ∈ Icc (1/2:ℝ) 3)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (htests : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (r : ℕ) (hr : 2 ≤ r) (hr' : r ≤ 4) :
    c/(2*σ) ≤ |iteratedDeriv r (fun u => (F u-F (u+η*y))/(σ*η)) x| := by
  have hx0 : 0 < x := by linarith only [hx.1]
  have hy0 : 0 < y := by linarith only [hy.1]
  have hp : 0 < η*y := mul_pos hη hy0
  have hxz : x < x+η*y := by linarith only [hp]
  have hI w (hw : w ∈ Icc x (x+η*y)) : w ∈ Icc (1/2:ℝ) 3 := by
    have hu := mul_le_mul hηmax hy.2 hy0.le (by norm_num : (0:ℝ) ≤ 1/8)
    constructor <;> linarith only [hx.1,hx.2,hw.1,hw.2,hu]
  have hd w (hw : w ∈ Icc x (x+η*y)) :
      HasDerivAt (iteratedDeriv r F) (iteratedDeriv (r+1) F w) w := by
    have hF := hf w (by have hh := (hI w hw).1; linarith only [hh])
    exact hasDerivAt_iteratedDeriv_finite (show r < r+1 by omega)
      (hF.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl (r+1)))
  obtain ⟨u,hu,he⟩ := exists_hasDerivAt_eq_slope (iteratedDeriv r F)
    (iteratedDeriv (r+1) F) hxz
    (fun w hw => (hd w hw).continuousAt.continuousWithinAt)
    (fun w hw => hd w ⟨hw.1.le,hw.2.le⟩)
  have ht := htests u (hI u ⟨hu.1.le,hu.2.le⟩)
  have hlo : c ≤ |iteratedDeriv (r+1) F u| := by
    interval_cases r
    · exact ht 0
    · exact ht 1
    · exact ht 2
  rw [he,abs_div,abs_of_pos (sub_pos.mpr hxz)] at hlo
  have hprod := (le_div_iff₀ (sub_pos.mpr hxz)).mp hlo
  rw [abs_sub_comm] at hprod
  have hFx : ContDiffAt ℝ r F x :=
    (hf x hx0).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl r)
  have hFz : ContDiffAt ℝ r (fun u => F (u+η*y)) x :=
    ((hf _ (add_pos hx0 hp)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl r)).comp x
        (contDiffAt_id.add contDiffAt_const)
  rw [iteratedDeriv_div_const,iteratedDeriv_fun_sub hFx hFz,
    iteratedDeriv_comp_add_const,abs_div,abs_of_pos (mul_pos hσ hη)]
  apply (le_div_iff₀ (mul_pos hσ hη)).mpr
  have heq : c/(2*σ)*(σ*η)=c*η/2 := by field_simp
  rw [heq]
  apply le_trans ?_ hprod
  nlinarith only [mul_le_mul_of_nonneg_left hy.1 (mul_pos hc hη).le]


                                                                       
                                                                      
theorem positive_difference_curvature_directions
    (F : ℝ → ℝ) {σ η x y : ℝ}
    (hx : 0 < x) (hz : 0 < x+η*y)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w) (r : ℕ) :
    let H := fun p : ℝ × ℝ =>
      (iteratedDeriv r F p.2-iteratedDeriv r F (p.2+η*p.1))/(σ*η)
    ContDiffAt ℝ ∞ H (y,x) ∧
    fderiv ℝ H (y,x) (0,1) =
      (iteratedDeriv (r+1) F x-iteratedDeriv (r+1) F (x+η*y))/(σ*η) ∧
    fderiv ℝ H (y,x) (1,0) =
      -η*iteratedDeriv (r+1) F (x+η*y)/(σ*η) := by
  intro H
  have hcx := contDiffAt_iteratedDeriv_infty (hf x hx) r
  have hcz := contDiffAt_iteratedDeriv_infty (hf _ hz) r
  have hd₀ := hasDerivAt_iteratedDeriv_finite (show r < r+1 by omega)
    ((hf x hx).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl (r+1)))
  have hd₁ := hasDerivAt_iteratedDeriv_finite (show r < r+1 by omega)
    ((hf _ hz).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl (r+1)))
  have hshift : HasFDerivAt (fun p : ℝ × ℝ => p.2+η*p.1)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ)+η • (ContinuousLinearMap.fst ℝ ℝ ℝ)) (y,x) := by
    exact hasFDerivAt_snd.add (hasFDerivAt_fst.const_mul η)
  have h₀ : HasFDerivAt (fun p : ℝ × ℝ => iteratedDeriv r F p.2)
      (iteratedDeriv (r+1) F x • ContinuousLinearMap.snd ℝ ℝ ℝ) (y,x) :=
    hd₀.comp_hasFDerivAt (f:=fun p : ℝ × ℝ => p.2) (y,x) hasFDerivAt_snd
  have h₁ : HasFDerivAt (fun p : ℝ × ℝ => iteratedDeriv r F (p.2+η*p.1))
      (iteratedDeriv (r+1) F (x+η*y) •
        (ContinuousLinearMap.snd ℝ ℝ ℝ+η • ContinuousLinearMap.fst ℝ ℝ ℝ)) (y,x) :=
    hd₁.comp_hasFDerivAt (f:=fun p : ℝ × ℝ => p.2+η*p.1) (y,x) hshift
  have hder := (h₀.sub h₁).mul_const ((σ*η)⁻¹)
  have hH : fderiv ℝ H (y,x) = (σ*η)⁻¹ •
      (iteratedDeriv (r+1) F x • ContinuousLinearMap.snd ℝ ℝ ℝ-
        iteratedDeriv (r+1) F (x+η*y) •
          (ContinuousLinearMap.snd ℝ ℝ ℝ+η • ContinuousLinearMap.fst ℝ ℝ ℝ)) :=
    hder.fderiv
  refine ⟨?_,?_,?_⟩
  · exact ((hcx.comp (y,x) contDiffAt_snd).sub
      (hcz.comp (y,x) (contDiffAt_snd.add (contDiffAt_const.mul contDiffAt_fst)))).div_const _
  · rw [hH]
    change (σ*η)⁻¹*(iteratedDeriv (r+1) F x*1-
      iteratedDeriv (r+1) F (x+η*y)*(1+η*0))=_
    ring
  · rw [hH]
    change (σ*η)⁻¹*(iteratedDeriv (r+1) F x*0-
      iteratedDeriv (r+1) F (x+η*y)*(0+η*1))=_
    ring


                                                                    
                                                                           
theorem positive_difference_jet_small_shift
    (F : ℝ → ℝ) {σ U η x y : ℝ}
    (hσ : 0 < σ) (hU : 0 < U) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hx : x ∈ Icc (3/4:ℝ) (9/4)) (hy : y ∈ Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (r : ℕ) (hr : r ≤ 5) :
    |iteratedDeriv r (fun u => (F u-F (u+η*y))/(σ*η)) x+
      y/σ*iteratedDeriv (r+1) F x| ≤ 4*U*η/σ ∧
    |iteratedDeriv r (fun u => deriv (fun v => (F u-F (u+η*v))/(σ*η)) y) x+
      1/σ*iteratedDeriv (r+1) F x| ≤ 2*U*η/σ := by
  have hx0 : 0 < x := by linarith only [hx.1]
  have hy0 : 0 < y := zero_lt_one.trans_le hy.1
  have hp : 0 < η*y := mul_pos hη hy0
  have hxz : x < x+η*y := by linarith only [hp]
  have hxI : x ∈ Icc x (x+η*y) := ⟨le_rfl,hxz.le⟩
  have hzI : x+η*y ∈ Icc x (x+η*y) := ⟨hxz.le,le_rfl⟩
  have hI w (hw : w ∈ Icc x (x+η*y)) : w ∈ Icc (1/2:ℝ) 3 := by
    have hu := mul_le_mul hηmax hy.2 hy0.le (by norm_num : (0:ℝ) ≤ 1/8)
    constructor <;> linarith only [hx.1,hx.2,hw.1,hw.2,hu]
  have hreg w (hw : w ∈ Icc x (x+η*y)) : ContDiffAt ℝ ∞ F w :=
    hf w (by have hh := (hI w hw).1; linarith only [hh])
  have hLip a (ha : a ∈ Icc x (x+η*y)) b (hb : b ∈ Icc x (x+η*y)) :
      |iteratedDeriv (r+1) F a-iteratedDeriv (r+1) F b| ≤ U*|a-b| := by
    have hd w (hw : w ∈ Icc x (x+η*y)) :
        DifferentiableAt ℝ (iteratedDeriv (r+1) F) w :=
      (contDiffAt_iteratedDeriv_infty (hreg w hw) (r+1)).differentiableAt (by simp)
    have hbnd w (hw : w ∈ Icc x (x+η*y)) :
        ‖deriv (iteratedDeriv (r+1) F) w‖ ≤ U := by
      rw [←iteratedDeriv_succ,Real.norm_eq_abs]
      exact hbound w (hI w hw) (r+1) (by omega)
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_deriv_le hd hbnd (convex_Icc x (x+η*y)) hb ha
  have hd w (hw : w ∈ Icc x (x+η*y)) :
      HasDerivAt (iteratedDeriv r F) (iteratedDeriv (r+1) F w) w :=
    hasDerivAt_iteratedDeriv_finite (show r < r+1 by omega)
      ((hreg w hw).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl (r+1)))
  obtain ⟨u,hu,he⟩ := exists_hasDerivAt_eq_slope (iteratedDeriv r F)
    (iteratedDeriv (r+1) F) hxz
    (fun w hw => (hd w hw).continuousAt.continuousWithinAt)
    (fun w hw => hd w ⟨hw.1.le,hw.2.le⟩)
  have hFx : ContDiffAt ℝ r F x :=
    (hf x hx0).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl r)
  have hFz : ContDiffAt ℝ r (fun t => F (t+η*y)) x :=
    ((hf _ (add_pos hx0 hp)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl r)).comp x
        (contDiffAt_id.add contDiffAt_const)
  have hjet : iteratedDeriv r (fun t => (F t-F (t+η*y))/(σ*η)) x =
      -(y/σ)*iteratedDeriv (r+1) F u := by
    rw [iteratedDeriv_div_const,iteratedDeriv_fun_sub hFx hFz,iteratedDeriv_comp_add_const,he]
    rw [show x+η*y-x=η*y by ring]
    field_simp
    ring
  constructor
  · rw [hjet,show -(y/σ)*iteratedDeriv (r+1) F u+y/σ*iteratedDeriv (r+1) F x =
      -(y/σ)*(iteratedDeriv (r+1) F u-iteratedDeriv (r+1) F x) by ring,
      abs_mul,abs_neg,abs_div,abs_of_pos hy0,abs_of_pos hσ]
    have huI : u ∈ Icc x (x+η*y) := ⟨hu.1.le,hu.2.le⟩
    have hdist : |u-x| ≤ η*y := by rw [abs_of_pos (sub_pos.mpr hu.1)]; linarith only [hu.2]
    calc
      _ ≤ (y/σ)*(U*|u-x|) :=
        mul_le_mul_of_nonneg_left (hLip u huI x hxI) (by positivity)
      _ ≤ (y/σ)*(U*(η*y)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hdist hU.le) (by positivity)
      _ = U*η*y^2/σ := by ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ hσ.le
        have hysq : y^2 ≤ 4 := by nlinarith only [pow_le_pow_left₀ hy0.le hy.2 2]
        have hmul := mul_le_mul_of_nonneg_left hysq (mul_pos hU hη).le
        nlinarith only [hmul]
  · have hj := positive_difference_mixed_derivative F hσ.ne' hη hx0 hy0 hf r 1 (by norm_num)
    simp only [iteratedDeriv_one,Nat.sub_self,pow_zero] at hj
    rw [hj,show -(1/σ)*iteratedDeriv (r+1) F (x+η*y)+
        1/σ*iteratedDeriv (r+1) F x =
        -(1/σ)*(iteratedDeriv (r+1) F (x+η*y)-iteratedDeriv (r+1) F x) by ring,
      abs_mul,abs_neg,abs_div,abs_one,abs_of_pos hσ]
    have hh := hLip _ hzI x hxI
    rw [show x+η*y-x=η*y by ring,abs_of_pos hp] at hh
    calc
      _ ≤ (1/σ)*(U*(η*y)) := mul_le_mul_of_nonneg_left hh (by positivity)
      _ = U*η*y/σ := by ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (by nlinarith only [mul_le_mul_of_nonneg_left hy.2 (mul_pos hU hη).le]) hσ.le


                                                                  
                                                                            
theorem positive_jets_difference_case_two_tests {σ c U : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ η₀ d : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < d ∧
      ∀ F : ℝ → ℝ,
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ x ∈ Icc (3/4:ℝ) (9/4), ∀ y ∈ Icc (1:ℝ) 2,
      let D := fun r => iteratedDeriv r (fun u => (F u-F (u+η*y))/(σ*η)) x
      let B := fun r => iteratedDeriv r
        (fun u => deriv (fun v => (F u-F (u+η*v))/(σ*η)) y) x
      ∀ j, d ≤ |HuxleyModel.caseTwoTests ![D 2,D 3,D 4,D 5,B 2,B 3,B 4] j| := by
  obtain ⟨ε,d,hε,hd,hstab⟩ := HuxleyModel.caseTwoTests_uniform_stability (U:=U) hσ hc
  let η₀ := min (1/8:ℝ) (ε*σ/(4*U))
  have hη₀ : 0 < η₀ := lt_min (by norm_num) (by positivity)
  refine ⟨η₀,d,hη₀,min_le_left _ _,hd,?_⟩
  intro F hf hbound htests η hη hηsmall x hx y hy D B
  have hηmax : η ≤ 1/8 := hηsmall.trans (min_le_left _ _)
  have hcap : η ≤ ε*σ/(4*U) := hηsmall.trans (min_le_right _ _)
  have hbudget : 4*U*η/σ ≤ ε := by
    apply (div_le_iff₀ hσ).mpr
    have hh := (le_div_iff₀ (by positivity : 0 < 4*U)).mp hcap
    nlinarith only [hh]
  have hbudget' : 2*U*η/σ ≤ ε := by
    apply le_trans ?_ hbudget
    apply div_le_div_of_nonneg_right _ hσ.le
    nlinarith only [mul_pos hU hη]
  let v := fun i : Fin 4 => iteratedDeriv (i.val+3) F x
  let w : Fin 7 → ℝ := ![D 2,D 3,D 4,D 5,B 2,B 3,B 4]
  have hxI : x ∈ Icc (1/2:ℝ) 3 := ⟨by linarith only [hx.1],by linarith only [hx.2]⟩
  have hv (i : Fin 4) : |v i| ≤ U := hbound x hxI (i.val+2) (by omega)
  have hj r (hr : r ≤ 5) := positive_difference_jet_small_shift F hσ hU hη hηmax
    hx hy hf hbound r hr
  change ∀ j, d ≤ |HuxleyModel.caseTwoTests w j|
  apply hstab v y hv (htests x hxI 5) (htests x hxI 6) hy w
  intro i
  fin_cases i
  · simpa [v,w,D,sub_eq_add_neg,neg_mul,neg_div] using (hj 2 (by norm_num)).1.trans hbudget
  · simpa [v,w,D,sub_eq_add_neg,neg_mul,neg_div] using (hj 3 (by norm_num)).1.trans hbudget
  · simpa [v,w,D,sub_eq_add_neg,neg_mul,neg_div] using (hj 4 (by norm_num)).1.trans hbudget
  · simpa [v,w,D,sub_eq_add_neg,neg_mul,neg_div] using (hj 5 (by norm_num)).1.trans hbudget
  · simpa [v,w,B,sub_eq_add_neg,neg_mul,neg_div] using (hj 2 (by norm_num)).2.trans hbudget'
  · simpa [v,w,B,sub_eq_add_neg,neg_mul,neg_div] using (hj 3 (by norm_num)).2.trans hbudget'
  · simpa [v,w,B,sub_eq_add_neg,neg_mul,neg_div] using (hj 4 (by norm_num)).2.trans hbudget'


                                                                 
                                                                     
                                                                       
theorem difference_family_dyadic_parameter_geometry {H : ℝ} (hH : 0 < H) :
    (∀ r : ℕ, H ≤ (r:ℝ) → (r:ℝ) ≤ 2*H → (r:ℝ)/H-1 ∈ Icc (0:ℝ) 1) ∧
    (∀ r s : ℕ, r ≠ s →
      1 ≤ H*|(r:ℝ)/H-1-((s:ℝ)/H-1)|) := by
  constructor
  · intro r hr hr'
    have hlo := (one_le_div hH).mpr hr
    have hhi := (div_le_iff₀ hH).mpr hr'
    constructor <;> linarith only [hlo,hhi]
  · intro r s hrs
    rw [show (r:ℝ)/H-1-((s:ℝ)/H-1)=((r:ℝ)-(s:ℝ))/H by ring,
      abs_div,abs_of_pos hH]
    have he : H*(|(r:ℝ)-(s:ℝ)|/H)=|(r:ℝ)-(s:ℝ)| := by field_simp
    rw [he]
    rcases lt_or_gt_of_ne hrs with hlt | hgt
    · have hh : (r:ℝ)+1 ≤ (s:ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hlt)
      rw [abs_of_nonpos (by linarith only [hh])]
      linarith only [hh]
    · have hh : (s:ℝ)+1 ≤ (r:ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hgt)
      rw [abs_of_nonneg (by linarith only [hh])]
      linarith only [hh]


open scoped FourierTransform BigOperators

-- Generated closures: source context is replayed in the next part.
end TaoTrudgianYang2025.HuxleyRationalPhase
end
end
