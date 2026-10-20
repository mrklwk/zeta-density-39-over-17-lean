module
public import LaterPairs.Native.HuxleyReferenceSieve.Part02

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




                                                                
                                                                          
                                                                    
            
theorem positive_difference_minimal_anchor_complement_count
    (S : Finset ℤ) (F : ℝ → ℝ) (anchor : ℤ → ℚ)
    (N : ℕ) (s : ℝ) {σ c J η y T M R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hpoints : ∀ i∈S, s+(N:ℝ)*i∈Icc M (2*M)) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    let t := fun i : ℤ => s+(N:ℝ)*i
    let delta := c/(64*σ*R^2)
    let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
    (∀ i∈S, (anchor i:ℝ)∈Ioo (h (t i)-delta) (h (t i)+delta) ∧
      ∀ a : ℚ, (a:ℝ)∈Ioo (h (t i)-delta) (h (t i)+delta) → (anchor i).den ≤ a.den) →
    ∀ (Q Acut : ℕ) (Bmajor : ℝ), 2 ≤ Acut → Acut ≤ Q → 0 ≤ Bmajor →
    let Bad := S.filter (fun i => ¬ (Acut*(anchor i).den ≤ Q ∧
      Bmajor*R^2 ≤ c*(Q:ℝ)*(anchor i).den))
    let Dlow := Bmajor*R^2/(c*(Q:ℝ))
    let Khigh := Q/Acut+1
    let Dhigh := 64*σ*R^2/(c*(Khigh:ℝ))
    let Cost := 4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
      Dlow*(2*(Vbound+delta)*Dlow+1)
    (Bad.card:ℝ) ≤ Cost ∧
      ∀ H : ℤ → ℕ, (∀ i∈S, H i ≤ N) →
        (∑ i∈Bad,(H i:ℝ)) ≤ (N:ℝ)*Cost := by
  classical
  intro f h t delta Vbound hanchors Q Acut Bmajor hAcut hAQ hBmajor
    Bad Dlow Khigh Dhigh Cost
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hQ : 0 < Q := by omega
  have hQr : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hApos : 0 < Acut := by omega
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hV : 0 ≤ Vbound := by dsimp only [Vbound]; positivity
  have hDlow : 0 ≤ Dlow := by dsimp only [Dlow]; positivity
  have hnear i (hi : i∈S) : |(anchor i:ℝ)-h (t i)| ≤ delta := by
    have hh := (hanchors i hi).1
    exact abs_le.mpr ⟨by linarith only [hh.1],by linarith only [hh.2]⟩
  have hinj := positive_difference_near_anchor_injective S F anchor N s
    hσ hc hη hηmax hy hf hnegative hT hM hN hR hphase hpoints hnear
  have hK : 2 ≤ Khigh := by
    have hh : 1 ≤ Q/Acut := (Nat.le_div_iff_mul_le hApos).mpr (by simpa only [one_mul] using hAQ)
    dsimp only [Khigh]
    omega
  let High := S.filter (fun i => Khigh ≤ (anchor i).den)
  have hhigh : (High.card:ℝ) ≤ 4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1)) := by
    exact (positive_difference_actual_minimal_anchor_sharp_tail S F anchor N s
      hσ hc hJ hη hηmax hy hf hbound htests hnegative hT hM hN hR hphase hpoints
      (fun i hi => (hanchors i hi).2) Khigh hK).1
  have hscale2 : T/M^2=M/((N:ℝ)*R^2) := by
    apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    nlinarith only [hphase]
  have hvalues i (hi : i∈S) : |(anchor i:ℝ)| ≤ Vbound+delta := by
    have hh := (positive_difference_half_curvature_source_bounds F
      hσ hc hJ hη hηmax hT hM hy (hpoints i hi) hf hbound htests).2
    have he : (3*J/σ)*T/(2*M^2)=Vbound := by
      calc
        _ = (3*J/(2*σ))*(T/M^2) := by ring
        _ = Vbound := by rw [hscale2]; dsimp only [Vbound]; ring
    rw [he] at hh
    calc
      |(anchor i:ℝ)| = |((anchor i:ℝ)-h (t i))+h (t i)| := by rw [sub_add_cancel]
      _ ≤ |(anchor i:ℝ)-h (t i)|+|h (t i)| := abs_add_le _ _
      _ ≤ delta+Vbound := add_le_add (hnear i hi) hh
      _ = Vbound+delta := by ring
  let Low := S.filter (fun i => c*(Q:ℝ)*(anchor i).den < Bmajor*R^2)
  have hlowden i (hi : i∈Low) : (anchor i).den ≤ ⌊Dlow⌋₊ := by
    apply Nat.le_floor
    apply (le_div_iff₀ (mul_pos hc hQr)).mpr
    have hh := (Finset.mem_filter.mp hi).2
    nlinarith only [hh]
  have hlow : (Low.card:ℝ) ≤ Dlow*(2*(Vbound+delta)*Dlow+1) := by
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



                                                                  
                                                                      
                                                                  
private theorem tagged_cost_source_scale
    {a N C D Q L cost : ℝ}
    (ha : 0 ≤ a) (hN : 0 < N) (hQ : 0 < Q)
    (hcost : cost ≤ C*(D/(N*Q))*L) :
    a*N*cost ≤ a*C*(D/Q)*L := by
  calc
    _ ≤ a*N*(C*(D/(N*Q))*L) :=
      mul_le_mul_of_nonneg_left hcost (mul_nonneg ha hN.le)
    _ = _ := by field_simp

private theorem tagged_anchor_complement_grouped_count
    {ι : Type*} [DecidableEq ι] (Y : Finset ι) (S : ι → Finset ℤ)
    (F : ℝ → ℝ) (y : ι → ℝ) (anchor : ι → ℤ → ℚ)
    (N : ℕ) (s : ℝ) {σ c J η T M R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : ∀ i∈Y, y i∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hpoints : ∀ i∈Y, ∀ k∈S i, s+(N:ℝ)*k∈Icc M (2*M))
    (hdisjoint : ∀ i∈Y, ∀ j∈Y, i≠j → y i=y j → Disjoint (S i) (S j)) :
    let f := fun u w => T*(F (w/M)-F (w/M+η*u))/(σ*η)
    let h := fun u w => iteratedDeriv 2 (f u) w/2
    let t := fun k : ℤ => s+(N:ℝ)*k
    let delta := c/(64*σ*R^2)
    let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
    (∀ i∈Y, ∀ k∈S i,
      (anchor i k:ℝ)∈Ioo (h (y i) (t k)-delta) (h (y i) (t k)+delta) ∧
      ∀ a : ℚ, (a:ℝ)∈Ioo (h (y i) (t k)-delta) (h (y i) (t k)+delta) →
        (anchor i k).den ≤ a.den) →
    ∀ (Q Acut : ℕ) (Bmajor : ℝ), 2 ≤ Acut → Acut ≤ Q → 0 ≤ Bmajor →
      let Sall := Y.biUnion (fun i => (S i).image (fun k => (i,k)))
      let Good : ι × ℤ → Prop := fun p => Acut*(anchor p.1 p.2).den ≤ Q ∧
        Bmajor*R^2 ≤ c*(Q:ℝ)*(anchor p.1 p.2).den
      let Dlow := Bmajor*R^2/(c*(Q:ℝ))
      let Dhigh := 64*σ*R^2/(c*((Q/Acut+1:ℕ):ℝ))
      let Cost := 4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
        Dlow*(2*(Vbound+delta)*Dlow+1)
      ((Sall.filter (fun p => ¬ Good p)).card:ℝ) ≤ ((Y.image y).card:ℝ)*Cost ∧
      ∀ H : ι → ℤ → ℕ, (∀ i∈Y, ∀ k∈S i, H i k ≤ N) →
        (∑ p∈Sall.filter (fun p => ¬ Good p),(H p.1 p.2:ℝ)) ≤
          ((Y.image y).card:ℝ)*(N:ℝ)*Cost := by
  classical
  intro f h t delta Vbound hanchors Q Acut Bmajor hA hAQ hB Sall Good Dlow Dhigh Cost
  let Phases := Y.image y
  let P := Sall.filter (fun p => ¬ Good p)
  let Grid := fun u => (Y.filter (fun i => y i=u)).biUnion S
  have hgrid u k : k∈Grid u ↔ ∃ i∈Y, y i=u ∧ k∈S i := by
    constructor
    · intro hk
      obtain ⟨i,hi,hk⟩ := Finset.mem_biUnion.mp hk
      exact ⟨i,(Finset.mem_filter.mp hi).1,(Finset.mem_filter.mp hi).2,hk⟩
    · rintro ⟨i,hi,hu,hk⟩
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,hu⟩,hk⟩
  let ag := fun u k => if hh : ∃ i∈Y, y i=u ∧ k∈S i then
    anchor (Classical.choose hh) k else (0:ℚ)
  have hag i (hi : i∈Y) k (hk : k∈S i) : ag (y i) k=anchor i k := by
    have hex : ∃ j∈Y, y j=y i ∧ k∈S j := ⟨i,hi,rfl,hk⟩
    dsimp only [ag]
    rw [dite_eq_left hex]
    have hh := Classical.choose_spec hex
    have he : Classical.choose hex=i := by
      by_contra hne
      exact Finset.disjoint_left.mp
        (hdisjoint _ hh.1 i hi hne hh.2.1) hh.2.2 hk
    rw [he]
  have hmem p : p∈Sall ↔ p.1∈Y ∧ p.2∈S p.1 := by
    constructor
    · intro hp
      obtain ⟨i,hi,hp⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨k,hk,he⟩ := Finset.mem_image.mp hp
      subst p
      exact ⟨hi,hk⟩
    · rintro ⟨hi,hk⟩
      exact Finset.mem_biUnion.mpr ⟨p.1,hi,Finset.mem_image.mpr ⟨p.2,hk,rfl⟩⟩
  have hGcount u (hu : u∈Phases) :
      ((Grid u).filter (fun k => ¬ (Acut*(ag u k).den ≤ Q ∧
        Bmajor*R^2 ≤ c*(Q:ℝ)*(ag u k).den))).card ≤ (Cost:ℝ) := by
    have hyp : u∈Icc (1:ℝ) 2 := by
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
      exact hy i hi
    have hpts k (hk : k∈Grid u) : t k∈Icc M (2*M) := by
      obtain ⟨i,hi,_hui,hk⟩ := (hgrid u k).mp hk
      exact hpoints i hi k hk
    have hanc k (hk : k∈Grid u) :
        (ag u k:ℝ)∈Ioo (h u (t k)-delta) (h u (t k)+delta) ∧
        ∀ a : ℚ, (a:ℝ)∈Ioo (h u (t k)-delta) (h u (t k)+delta) →
          (ag u k).den ≤ a.den := by
      obtain ⟨i,hi,hui,hk⟩ := (hgrid u k).mp hk
      rw [←hui,hag i hi k hk]
      exact hanchors i hi k hk
    exact (positive_difference_minimal_anchor_complement_count (Grid u) F (ag u) N s
      hσ hc hJ hη hηmax hyp hf hbound htests hnegative hT hM hN hR hphase
      hpts hanc Q Acut Bmajor hA hAQ hB).1
  have hfiber u (hu : u∈Phases) :
      ((P.filter (fun p => y p.1=u)).card:ℝ) ≤ Cost := by
    let V := P.filter (fun p => y p.1=u)
    have hdata p (hp : p∈V) : p.1∈Y ∧ p.2∈S p.1 ∧ ¬ Good p ∧ y p.1=u := by
      have hh := Finset.mem_filter.mp hp
      have hpP := Finset.mem_filter.mp hh.1
      have hm := (hmem p).mp hpP.1
      exact ⟨hm.1,hm.2,hpP.2,hh.2⟩
    have hinj : Set.InjOn Prod.snd (V:Set (ι × ℤ)) := by
      intro p hp q hq he
      have hpS := hdata p hp
      have hqS := hdata q hq
      have hij : p.1=q.1 := by
        by_contra hne
        exact Finset.disjoint_left.mp
          (hdisjoint p.1 hpS.1 q.1 hqS.1 hne (hpS.2.2.2.trans hqS.2.2.2.symm))
          hpS.2.1 (by rw [he]; exact hqS.2.1)
      exact Prod.ext hij he
    have hsub : V.image Prod.snd ⊆ (Grid u).filter (fun k =>
        ¬ (Acut*(ag u k).den ≤ Q ∧ Bmajor*R^2 ≤ c*(Q:ℝ)*(ag u k).den)) := by
      intro k hk
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hk
      have hh := hdata p hp
      refine Finset.mem_filter.mpr ⟨(hgrid u p.2).mpr ⟨p.1,hh.1,hh.2.2.2,hh.2.1⟩,?_⟩
      rw [←hh.2.2.2,hag p.1 hh.1 p.2 hh.2.1]
      exact hh.2.2.1
    have hh := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hGcount u hu)
    rwa [Finset.card_image_of_injOn hinj] at hh
  have hcard : (P.card:ℝ) ≤ (Phases.card:ℝ)*Cost := by
    have he : (P.card:ℝ)=∑ u∈Phases,((P.filter (fun p => y p.1=u)).card:ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_fiberwise
        (fun p hp => Finset.mem_image_of_mem y ((hmem p).mp (Finset.mem_filter.mp hp).1).1)
    calc
      _ = _ := he
      _ ≤ ∑ _u∈Phases,Cost := Finset.sum_le_sum hfiber
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
  refine ⟨hcard,?_⟩
  intro H hH
  have hNp : (0:ℝ) ≤ N := Nat.cast_nonneg _
  calc
    (∑ p∈P,(H p.1 p.2:ℝ)) ≤ ∑ _p∈P,(N:ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hh := (hmem p).mp (Finset.mem_filter.mp hp).1
      exact Nat.cast_le.mpr (hH p.1 hh.1 p.2 hh.2)
    _ = (N:ℝ)*(P.card:ℝ) := by simp only [Finset.sum_const,nsmul_eq_mul,mul_comm]
    _ ≤ (N:ℝ)*((Phases.card:ℝ)*Cost) := mul_le_mul_of_nonneg_left hcard hNp
    _ = _ := by ring

                                                                       
                                                                       
                                                                     
                                                       
private theorem strong_anchor_cutoff_dense
    (Acut Q d : ℕ) {σ c R Bmajor : ℝ}
    (hσ : 0 < σ) (hR : 0 < R)
    (hA : 768 ≤ Acut) (hB : 24576*σ ≤ Bmajor)
    (hcut : Acut*d ≤ Q) (hlow : Bmajor*R^2 ≤ c*(Q:ℝ)*d) :
    256*(d:ℝ) ≤ (Q:ℝ)/3 ∧
      ∀ eps : ℝ, c/(64*σ*R^2) ≤ eps →
        256 ≤ 2*eps*((Q:ℝ)/3)*d := by
  have hcut' : (768:ℝ)*d ≤ Q := by
    exact_mod_cast (Nat.mul_le_mul_right d hA).trans hcut
  have hraw := (mul_le_mul_of_nonneg_right hB (sq_nonneg R)).trans hlow
  have hdelta : 256 ≤ 2*(c/(64*σ*R^2))*((Q:ℝ)/3)*d := by
    have hh : (256:ℝ) ≤ c*(Q:ℝ)*d/(96*σ*R^2) := by
      apply (le_div_iff₀ (by positivity : 0 < 96*σ*R^2)).mpr
      nlinarith only [hraw]
    convert hh using 1
    ring
  refine ⟨by linarith only [hcut'],?_⟩
  intro eps heps
  apply hdelta.trans
  gcongr


                                                                            
                                                                             
theorem positive_difference_tagged_gap_controlled_complement_fourier
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (Y : Finset ι) (F : ℝ → ℝ)
      (N : ℕ) (s : ℤ) (H : ι → ℤ → ℕ)
      (η T M R U : ℝ) (y x₁ x₂ : ι → ℝ),
      1 ≤ N → (∀ i∈Y, ∀ k, H i k ≤ N) →
      0 < η → η ≤ 1/8 → (∀ i∈Y, y i∈Icc (1:ℝ) 2) →
      0 < T → 0 < M → 0 < R → 0 < U →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      3*J ≤ σ*U →
      (∀ i∈Y, x₁ i∈Icc M (2*M)) → (∀ i∈Y, x₂ i∈Icc M (2*M)) →
      (∀ i∈Y, ∀ j∈Y, i≠j → y i=y j → x₂ i ≤ x₁ j ∨ x₂ j ≤ x₁ i) →
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
      ∀ Q : ℕ, 2 ≤ Q → Q ≤ N →
      ∀ (Acut : ℕ) (Bmajor : ℝ), 2 ≤ Acut → Acut ≤ Q → 128*σ ≤ Bmajor →
      let Sall := Y.biUnion (fun i => (S i).image (fun k => (i,k)))
      let Good := fun i => Acut*(anchor i.1 i.2).den ≤ Q ∧
        Bmajor*R^2 ≤ c*(Q:ℝ)*(anchor i.1 i.2).den
      let G := Sall.filter Good
      let Dlow := Bmajor*R^2/(c*(Q:ℝ))
      let Khigh := Q/Acut+1
      let Dhigh := 64*σ*R^2/(c*(Khigh:ℝ))
      let Dlog := 64*σ*R^2/(c*((Q:ℝ)/Acut))
      let Cost := 4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
        Dlow*(2*(Vbound+delta)*Dlow+1)
      ∃ (r : ι × ℤ → ℚ) (z : ι × ℤ → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i.1 i.2:ℝ) < r i ∧ |(r i:ℝ)-(anchor i.1 i.2:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i.1 i.2) (za i.1 i.2+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i.1) (z i)/2=(r i:ℝ)) ∧
      (∀ i∈G, z i∈Ioo (x₁ i.1) (x₂ i.1)) ∧
      (768 ≤ Acut → 24576*σ ≤ Bmajor →
        ∀ i∈G, 256*((anchor i.1 i.2).den:ℝ) ≤ (Q:ℝ)/3 ∧
          ∀ eps : ℝ, delta ≤ eps → 256 ≤ 2*eps*((Q:ℝ)/3)*(anchor i.1 i.2).den) ∧
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
      let FourierCost :=
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))
      let Cerror := (Acut:ℝ)*((6*J/σ)*(64*σ/c)^2+192*σ/c)+
        ((3*J/σ+c/(32*σ))*(Bmajor/c)^2+Bmajor/c)
      (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1 i.2),(𝐞 (f i.1 n):ℂ)‖) ≤ C*(((Y.image y).card:ℝ)*(N:ℝ)*Cost+FourierCost) ∧
      ((Acut:ℝ)*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1 i.2),(𝐞 (f i.1 n):ℂ)‖) ≤
          C*(((Y.image y).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1))+FourierCost)) := by
  classical
  obtain ⟨C,hC,hentry⟩ := positive_difference_tagged_gap_dyadic_source_fourier_cutoffs hσ hc hJ
  refine ⟨C,hC,?_⟩
  intro ι Y F N s H η T M R U y x₁ x₂ hN hH hη hηmax hy hT hM hR hU
    hf hbound htests hnegative hphase hbuffer hfourBudget hquadBudget hUlarge hx₁ hx₂
    hGapSep f h t L delta Vbound hgap
  obtain ⟨S,anchor,za,hinfo,hfourier⟩ :=
    hentry ι Y F N s H η T M R U y x₁ x₂ hN hH hη hηmax hy hT hM hR hU
      hf hbound hnegative hphase hbuffer hfourBudget hquadBudget hUlarge hx₁ hx₂ hgap
  refine ⟨S,anchor,za,hinfo,?_⟩
  intro Q hQ hQN Acut Bmajor hAcut hAQ hBmajor Sall Good G Dlow Khigh Dhigh Dlog Cost
  have hB0 : 0 ≤ Bmajor := (show 0 ≤ 128*σ by positivity).trans hBmajor
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpoints i (hi : i∈Y) k (hk : k∈S i) : t k∈Icc M (2*M) := by
    have hh := ((hinfo i hi).1 k).mp hk
    constructor <;> linarith only [hh.1,hh.2,(hx₁ i hi).1,(hx₂ i hi).2,hNp]
  have hanchors i (hi : i∈Y) k (hk : k∈S i) := ((hinfo i hi).2.1 k hk).2.2.2
  have hdisjoint i (hi : i∈Y) j (hj : j∈Y) (hne : i≠j) (hye : y i=y j) :
      Disjoint (S i) (S j) := by
    apply Finset.disjoint_left.mpr
    intro k hki hkj
    have hai := ((hinfo i hi).1 k).mp hki
    have haj := ((hinfo j hj).1 k).mp hkj
    rcases hGapSep i hi j hj hne hye with hij | hji
    · linarith only [hai.1,hai.2,haj.1,haj.2,hij,hNp]
    · linarith only [hai.1,hai.2,haj.1,haj.2,hji,hNp]
  have hgroup := tagged_anchor_complement_grouped_count Y S F y anchor N (s:ℝ)
    hσ hc hJ hη hηmax hy hf hbound htests hnegative hT hM
    (show 0 < N by omega) hR hphase hpoints hdisjoint hanchors
    Q Acut Bmajor hAcut hAQ hB0
  have hweight : (∑ i∈Sall.filter (fun i => ¬ Good i),(H i.1 i.2:ℝ)) ≤
      ((Y.image y).card:ℝ)*(N:ℝ)*Cost :=
    hgroup.2 H (fun i hi k _ => hH i hi k)
  obtain ⟨r,z,hr,hzg,hcenter,hcompletion⟩ := hfourier Q hQN Acut Bmajor hAcut hBmajor
  have hdense : 768 ≤ Acut → 24576*σ ≤ Bmajor →
      ∀ i∈G, 256*((anchor i.1 i.2).den:ℝ) ≤ (Q:ℝ)/3 ∧
        ∀ eps : ℝ, delta ≤ eps → 256 ≤ 2*eps*((Q:ℝ)/3)*(anchor i.1 i.2).den := by
    intro hAstrong hBstrong i hi
    exact strong_anchor_cutoff_dense Acut Q (anchor i.1 i.2).den hσ hR
      hAstrong hBstrong (Finset.mem_filter.mp hi).2.1 (Finset.mem_filter.mp hi).2.2
  refine ⟨r,z,hr,hzg,hdense,hcenter,?_⟩
  dsimp only
  intro K₀ _ hK₀
  obtain ⟨v,hv,k,hfour⟩ := hcompletion K₀ hK₀
  refine ⟨v,hv,k,?_⟩
  let m := fun i => round (z i)
  let A := fun i => (L i.2-m i).toNat
  let q := fun i => (r i).den
  let μ := fun i => iteratedDeriv 3 (f i.1) (m i)/6
  let ℓ := fun i => deriv (f i.1) (m i)
  let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
  let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
  let stretch := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
  let K := fun i => -2*μ i*(stretch i)^3
  let x := fun i p =>
    (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
  let FourierCost :=
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))
  let Cerror := (Acut:ℝ)*((6*J/σ)*(64*σ/c)^2+192*σ/c)+
        ((3*J/σ+c/(32*σ))*(Bmajor/c)^2+Bmajor/c)
  have hbase : (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1 i.2),(𝐞 (f i.1 n):ℂ)‖) ≤ C*(((Y.image y).card:ℝ)*(N:ℝ)*Cost+FourierCost) := by
    apply hfour.trans
    dsimp only [FourierCost]
    rw [←add_assoc (((Y.image y).card:ℝ)*(N:ℝ)*Cost)]
    gcongr
  refine ⟨hbase,?_⟩
  intro hRQ hNR
  have hcost : Cost ≤ Cerror*(M*R/((N:ℝ)*Q))*(2+Real.log (Dlog+1)) :=
    huxley_anchor_complement_source_scale Q Acut
      hσ hc hJ hM hNp hR hAcut hAQ hB0 hRQ hNR
  have hscaled : ((Y.image y).card:ℝ)*(N:ℝ)*Cost ≤
      ((Y.image y).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1)) :=
    tagged_cost_source_scale (Nat.cast_nonneg _) hNp
      (by exact_mod_cast (show 0 < Q by omega)) hcost
  apply hbase.trans
  apply mul_le_mul_of_nonneg_left _ (by linarith only [hC])
  exact add_le_add hscaled (le_refl FourierCost)

                                                                    
                                                                   
private theorem resonance_matrix_reciprocal_sum
    (S : Finset (Fin 4 → ℤ)) {X Gamma : ℝ}
    (hX : 0 ≤ X) (hGamma : 0 ≤ Gamma)
    (hdet : ∀ M∈S, M 0*M 3-M 1*M 2=1)
    (hc : ∀ M∈S, M 2 ≠ 0 ∧ |(M 2:ℝ)| ≤ Gamma)
    (ha : ∀ M∈S, |(M 0:ℝ)| ≤ |(M 2:ℝ)| *X+2)
    (hd : ∀ M∈S, |(M 3:ℝ)| ≤ |(M 2:ℝ)| *X+2) :
    ∑ M∈S,1/|(M 2:ℝ)| ≤ (2*Gamma+1)*(2*X+5)^2 := by
  let Z := ∑ M∈S,1/|(M 2:ℝ)|
  let K := (2*Gamma+1)*(2*X+5)^2
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  by_contra! hbad
  have hgap : 0 < Z-K := sub_pos.mpr hbad
  let W := (K*Gamma+1)/(Z-K)
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hh := bourgain_resonance_matrix_weight_sum S hX hGamma hW hdet hc ha hd
  have he : (∑ M∈S,(1+W/|(M 2:ℝ)|))=(S.card:ℝ)+W*Z := by
    dsimp only [Z]
    simp only [Finset.sum_add_distrib,div_eq_mul_inv,←Finset.mul_sum,
      Finset.sum_const,nsmul_eq_mul,mul_one,one_mul]
  rw [he] at hh
  have hw : W*(Z-K)=K*Gamma+1 := by dsimp only [W]; field_simp
  change (S.card:ℝ)+W*Z ≤ K*(Gamma+W) at hh
  nlinarith only [hh,hw,(show (0:ℝ) ≤ S.card from Nat.cast_nonneg _)]

private theorem adjacent_reference_pairs_order
    (S : Finset ℝ) {a b : ℝ × ℝ}
    (ha : a.1∈S ∧ a.2∈S ∧ a.1<a.2 ∧ ∀ t∈S, ¬(a.1<t ∧ t<a.2))
    (hb : b.1∈S ∧ b.2∈S ∧ b.1<b.2 ∧ ∀ t∈S, ¬(b.1<t ∧ t<b.2))
    (hne : a≠b) : a.2 ≤ b.1 ∨ b.2 ≤ a.1 := by
  rcases lt_trichotomy a.1 b.1 with hlt | he | hgt
  · left
    exact le_of_not_gt (fun hh => ha.2.2.2 _ hb.1 ⟨hlt,hh⟩)
  · exfalso
    apply hne
    apply Prod.ext he
    rcases lt_trichotomy a.2 b.2 with hlt₂ | he₂ | hgt₂
    · exact False.elim (hb.2.2.2 _ ha.2.1 ⟨by rw [←he]; exact ha.2.2.1,hlt₂⟩)
    · exact he₂
    · exact False.elim (ha.2.2.2 _ hb.2.1 ⟨by rw [he]; exact hb.2.2.1,hgt₂⟩)
  · right
    exact le_of_not_gt (fun hh => hb.2.2.2 _ ha.1 ⟨hgt,hh⟩)

private theorem adjacent_reference_crossing_family_card
    (Y S : Finset ℝ) (E : Finset (ℝ × (ℝ × ℝ))) (t : ℝ → ℝ)
    (hdata : ∀ i∈E, i.1∈Y ∧
      (i.2.1∈S ∧ i.2.2∈S ∧ i.2.1 < i.2.2 ∧ ∀ u∈S, ¬(i.2.1 < u ∧ u < i.2.2)) ∧
      i.2.1 < t i.1 ∧ t i.1 < i.2.2) :
    E.card ≤ Y.card := by
  classical
  have hinj : Set.InjOn Prod.fst (E : Set (ℝ × (ℝ × ℝ))) := by
    intro i hi j hj he
    by_contra hne
    have hp : i.2≠j.2 := fun hh => hne (Prod.ext he hh)
    have ho := adjacent_reference_pairs_order S (hdata i hi).2.1 (hdata j hj).2.1 hp
    have hti := (hdata i hi).2.2
    have htj := (hdata j hj).2.2
    rw [←he] at htj
    rcases ho with hleft | hright
    · linarith only [hti.1,hti.2,htj.1,htj.2,hleft]
    · linarith only [hti.1,hti.2,htj.1,htj.2,hright]
  have hsub : E.image Prod.fst ⊆ Y := by
    intro y hy
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
    exact (hdata i hi).1
  rw [←Finset.card_image_of_injOn hinj]
  exact Finset.card_le_card hsub


                                                                 
                                                                    
                                                              
theorem positive_difference_reference_family_interior_geometry
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
    (hsep : ∀ a∈S, ∀ b∈S, a≠b → U/(4*R^2) ≤ |a-b|)
    (hgapUpper : ∀ a∈S, ∀ b∈S, a<b →
      (∀ t∈S, ¬(a<t ∧ t<b)) → b-a ≤ 7*U/(2*R^2)) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let V := (Y ×ˢ (S ×ˢ S)).filter (fun i =>
      i.2.1 < i.2.2 ∧ (∀ t∈S, ¬(i.2.1 < t ∧ t < i.2.2)) ∧
        i.2.1 < h i.1 (2*M) ∧ h i.1 M < i.2.2)
    let G := V.filter (fun i => h i.1 M ≤ i.2.1 ∧ i.2.2 ≤ h i.1 (2*M))
    (V.card:ℝ) ≤ ((12*J/σ)*M/(N*U)+2)*(Y.card:ℝ) ∧
    (V \ G).card ≤ 2*Y.card ∧ (G.image Prod.fst).card ≤ Y.card ∧
    ∃ x₁ x₂ : ℝ × (ℝ × ℝ) → ℝ,
      (∀ i∈G, x₁ i∈Icc M (2*M) ∧ x₂ i∈Icc M (2*M) ∧ x₁ i < x₂ i ∧
        h i.1 (x₁ i)=i.2.1 ∧ h i.1 (x₂ i)=i.2.2 ∧
        U/(4*R^2) ≤ h i.1 (x₂ i)-h i.1 (x₁ i) ∧
        h i.1 (x₂ i)-h i.1 (x₁ i) ≤ 7*U/(2*R^2)) ∧
      (∀ i∈G, ∀ j∈G, i≠j → i.1=j.1 → x₂ i ≤ x₁ j ∨ x₂ j ≤ x₁ i) := by
  classical
  intro f h V G
  have hVdata i (hi : i∈V) : i.1∈Y ∧
      (i.2.1∈S ∧ i.2.2∈S ∧ i.2.1 < i.2.2 ∧ ∀ t∈S, ¬(i.2.1 < t ∧ t < i.2.2)) ∧
      i.2.1 < h i.1 (2*M) ∧ h i.1 M < i.2.2 := by
    have hh := Finset.mem_filter.mp hi
    have hp := Finset.mem_product.mp hh.1
    have he := Finset.mem_product.mp hp.2
    exact ⟨hp.1,⟨he.1,he.2,hh.2.1,hh.2.2.1⟩,hh.2.2.2⟩
  have hGS : G⊆V := Finset.filter_subset _ _
  let Left := V.filter (fun i => i.2.1 < h i.1 M)
  let Right := V.filter (fun i => h i.1 (2*M) < i.2.2)
  have hleft : Left.card ≤ Y.card := by
    apply adjacent_reference_crossing_family_card Y S Left (fun y => h y M)
    intro i hi
    have hh := Finset.mem_filter.mp hi
    have hd := hVdata i hh.1
    exact ⟨hd.1,hd.2.1,hh.2,hd.2.2.2⟩
  have hright : Right.card ≤ Y.card := by
    apply adjacent_reference_crossing_family_card Y S Right (fun y => h y (2*M))
    intro i hi
    have hh := Finset.mem_filter.mp hi
    have hd := hVdata i hh.1
    exact ⟨hd.1,hd.2.1,hd.2.2.1,hh.2⟩
  have hbadSub : V \ G ⊆ Left∪Right := by
    intro i hi
    have hh := Finset.mem_sdiff.mp hi
    by_cases hlo : h i.1 M ≤ i.2.1
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_filter.mpr
      refine ⟨hh.1,?_⟩
      by_contra hnot
      exact hh.2 (Finset.mem_filter.mpr ⟨hh.1,hlo,le_of_not_gt hnot⟩)
    · exact Finset.mem_union.mpr (Or.inl
        (Finset.mem_filter.mpr ⟨hh.1,lt_of_not_ge hlo⟩))
  have hboundary : (V \ G).card ≤ 2*Y.card := by
    have hh := (Finset.card_le_card hbadSub).trans (Finset.card_union_le Left Right)
    omega
  have hphaseCount : (G.image Prod.fst).card ≤ Y.card := by
    apply Finset.card_le_card
    intro y hyG
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hyG
    exact (hVdata i (hGS hi)).1
  have hmono y (hyY : y∈Y) : StrictMonoOn (h y) (Icc M (2*M)) := by
    apply (positive_difference_physical_curvature_strictMono F hσ hc hη hηmax
      (hy y hyY) hf hnegative hT hM).mono
    intro w hw
    constructor <;> linarith only [hw.1,hw.2,hM]
  have hcont y (hyY : y∈Y) : ContinuousOn (h y) (Icc M (2*M)) := by
    intro w hw
    have hw0 : 0 < w/M := div_pos (hM.trans_le hw.1) hM
    have hs0 : 0 < w/M+η*y := add_pos hw0 (mul_pos hη (zero_lt_one.trans_le (hy y hyY).1))
    have hcf : ContDiffAt ℝ 3 (f y) w :=
      (contDiffAt_const.mul (((hf _ hw0).comp w (contDiffAt_id.div_const M)).sub
        ((hf _ hs0).comp w ((contDiffAt_id.div_const M).add contDiffAt_const)))).div_const
        (σ*η) |>.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
    exact ((hasDerivAt_iteratedDeriv_finite (by norm_num : 2 < 3) hcf).div_const 2).continuousAt.continuousWithinAt
  have hex : ∀ i∈G, ∃ a b : ℝ, a∈Icc M (2*M) ∧ b∈Icc M (2*M) ∧
      h i.1 a=i.2.1 ∧ h i.1 b=i.2.2 := by
    intro i hi
    have hh := Finset.mem_filter.mp hi
    have hd := hVdata i hh.1
    have ha : i.2.1∈Icc (h i.1 M) (h i.1 (2*M)) := ⟨hh.2.1,hd.2.2.1.le⟩
    have hb : i.2.2∈Icc (h i.1 M) (h i.1 (2*M)) := ⟨hd.2.2.2.le,hh.2.2⟩
    obtain ⟨a,haM,hae⟩ := intermediate_value_Icc (by linarith only [hM] : M ≤ 2*M) (hcont i.1 hd.1) ha
    obtain ⟨b,hbM,hbe⟩ := intermediate_value_Icc (by linarith only [hM] : M ≤ 2*M) (hcont i.1 hd.1) hb
    exact ⟨a,b,haM,hbM,hae,hbe⟩
  choose! x₁ x₂ hroots using hex
  have hpack := positive_difference_reference_family_packing F Y S hσ hc hJ
    hη hηmax hy hf hbound htests hnegative hT hM hN hR hU hphase hsep
  refine ⟨hpack,hboundary,hphaseCount,x₁,x₂,?_,?_⟩
  · intro i hi
    have hd := hVdata i (hGS hi)
    have hr := hroots i hi
    have hlt : x₁ i < x₂ i := by
      by_contra hnot
      have hh := (hmono i.1 hd.1).monotoneOn hr.2.1 hr.1 (le_of_not_gt hnot)
      rw [hr.2.2.1,hr.2.2.2] at hh
      exact (not_le_of_gt hd.2.1.2.2.1) hh
    refine ⟨hr.1,hr.2.1,hlt,hr.2.2.1,hr.2.2.2,?_,?_⟩
    · rw [hr.2.2.1,hr.2.2.2]
      have hh := hsep _ hd.2.1.1 _ hd.2.1.2.1 (ne_of_lt hd.2.1.2.2.1)
      rw [abs_sub_comm,abs_of_pos (sub_pos.mpr hd.2.1.2.2.1)] at hh
      exact hh
    · rw [hr.2.2.1,hr.2.2.2]
      exact hgapUpper _ hd.2.1.1 _ hd.2.1.2.1 hd.2.1.2.2.1 hd.2.1.2.2.2
  · intro i hi j hj hne hye
    have hdi := hVdata i (hGS hi)
    have hdj := hVdata j (hGS hj)
    have hp : i.2≠j.2 := fun he => hne (Prod.ext hye he)
    have ho := adjacent_reference_pairs_order S hdi.2.1 hdj.2.1 hp
    have hri := hroots i hi
    have hrj := hroots j hj
    have hjleft : h i.1 (x₁ j)=j.2.1 := by simpa only [hye] using hrj.2.2.1
    have hjright : h i.1 (x₂ j)=j.2.2 := by simpa only [hye] using hrj.2.2.2
    rcases ho with hleft | hright
    · left
      apply le_of_not_gt
      intro hbad
      have hh := hmono i.1 hdi.1 hrj.1 hri.2.1 hbad
      rw [hjleft,hri.2.2.2] at hh
      exact (not_lt_of_ge hleft) hh
    · right
      apply le_of_not_gt
      intro hbad
      have hh := hmono i.1 hdi.1 hri.1 hrj.2.1 hbad
      rw [hri.2.2.1,hjright] at hh
      exact (not_lt_of_ge hright) hh


                                                               
                                                                        
                                                                         
                                                                             
public  theorem finite_reference_closed_bracket (S : Finset ℝ) {l u lo hi x : ℝ}
    (hl : l ∈ S) (hu : u ∈ S) (hlo : l ≤ lo) (hhi : hi ≤ u)
    (hwidth : lo < hi) (hx : x ∈ Icc lo hi) :
    ∃ a ∈ S, ∃ b ∈ S, a < b ∧ a ≤ x ∧ x ≤ b ∧
      (∀ z ∈ S, ¬ (a < z ∧ z < b)) ∧ a < hi ∧ lo < b := by
  classical
  by_cases htop : x < hi
  · let A := S.filter (fun z => z ≤ x)
    let B := S.filter (fun z => x < z)
    have hA : A.Nonempty := ⟨l,Finset.mem_filter.mpr ⟨hl,hlo.trans hx.1⟩⟩
    have hB : B.Nonempty := ⟨u,Finset.mem_filter.mpr ⟨hu,htop.trans_le hhi⟩⟩
    let a := A.max' hA
    let b := B.min' hB
    have ha := Finset.mem_filter.mp (Finset.max'_mem A hA)
    have hb := Finset.mem_filter.mp (Finset.min'_mem B hB)
    refine ⟨a,ha.1,b,hb.1,ha.2.trans_lt hb.2,ha.2,hb.2.le,?_,
      ha.2.trans_lt htop,hx.1.trans_lt hb.2⟩
    intro z hz hzab
    by_cases hzx : z ≤ x
    · have hzA : z ∈ A := Finset.mem_filter.mpr ⟨hz,hzx⟩
      exact (not_lt_of_ge (Finset.le_max' A z hzA)) hzab.1
    · have hzB : z ∈ B := Finset.mem_filter.mpr ⟨hz,lt_of_not_ge hzx⟩
      exact (not_lt_of_ge (Finset.min'_le B z hzB)) hzab.2
  · have hxe : x = hi := le_antisymm hx.2 (le_of_not_gt htop)
    let A := S.filter (fun z => z < x)
    let B := S.filter (fun z => x ≤ z)
    have hA : A.Nonempty := ⟨l,Finset.mem_filter.mpr ⟨hl,by linarith⟩⟩
    have hB : B.Nonempty := ⟨u,Finset.mem_filter.mpr ⟨hu,by linarith⟩⟩
    let a := A.max' hA
    let b := B.min' hB
    have ha := Finset.mem_filter.mp (Finset.max'_mem A hA)
    have hb := Finset.mem_filter.mp (Finset.min'_mem B hB)
    refine ⟨a,ha.1,b,hb.1,ha.2.trans_le hb.2,ha.2.le,hb.2,?_,
      by simpa only [hxe] using ha.2,by linarith only [hwidth,hxe,hb.2]⟩
    intro z hz hzab
    by_cases hzx : z < x
    · have hzA : z ∈ A := Finset.mem_filter.mpr ⟨hz,hzx⟩
      exact (not_lt_of_ge (Finset.le_max' A z hzA)) hzab.1
    · have hzB : z ∈ B := Finset.mem_filter.mpr ⟨hz,le_of_not_gt hzx⟩
      exact (not_lt_of_ge (Finset.min'_le B z hzB)) hzab.2

private theorem grid_short_interval_card (K : Finset ℤ) {s N a : ℝ}
    (hN : 0 < N)
    (hK : ∀ k ∈ K, a ≤ s+N*(k:ℝ) ∧ s+N*(k:ℝ) ≤ a+N/4) :
    K.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hiw := hK i hi
  have hjw := hK j hj
  have hij : (i:ℝ) < (j:ℝ)+1 := by nlinarith
  have hji : (j:ℝ) < (i:ℝ)+1 := by nlinarith
  have hij' : i < j+1 := by exact_mod_cast hij
  have hji' : j < i+1 := by exact_mod_cast hji
  omega

private theorem trimmed_grid_boundary_card (K : Finset ℤ) {s N a b : ℝ}
    (hN : 0 < N)
    (hK : ∀ k ∈ K, a ≤ s+N*(k:ℝ) ∧ s+N*(k:ℝ) ≤ b ∧
      ¬(a+N/4 ≤ s+N*(k:ℝ) ∧ s+N*(k:ℝ) ≤ b-N/4)) :
    K.card ≤ 2 := by
  classical
  let L := K.filter (fun k : ℤ => s+N*(k:ℝ) < a+N/4)
  let R := K.filter (fun k : ℤ => b-N/4 < s+N*(k:ℝ))
  have hL : L.card ≤ 1 := grid_short_interval_card L hN (by
    intro k hk
    have hh := Finset.mem_filter.mp hk
    exact ⟨(hK k hh.1).1,hh.2.le⟩)
  have hR : R.card ≤ 1 := grid_short_interval_card R hN (by
    intro k hk
    have hh := Finset.mem_filter.mp hk
    exact ⟨hh.2.le,by linarith only [(hK k hh.1).2.1]⟩)
  have hsub : K ⊆ L∪R := by
    intro k hk
    by_cases hleft : s+N*(k:ℝ) < a+N/4
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hk,hleft⟩))
    · have hr : b-N/4 < s+N*(k:ℝ) := by
        by_contra hnot
        exact (hK k hk).2.2 ⟨le_of_not_gt hleft,le_of_not_gt hnot⟩
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hk,hr⟩))
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le L R)
  omega


private theorem reference_grid_missing_card
    (Y S : Finset ℝ) (I : Finset ℤ) (h : ℝ → ℝ → ℝ)
    {M N s C : ℝ} (hM : 0 < M) (hN : 0 < N) (hC : 0 ≤ C)
    (hI : ∀ k∈I, s+N*(k:ℝ)∈Icc M (2*M))
    (hmono : ∀ y∈Y, StrictMonoOn (h y) (Icc M (2*M)))
    (henclose : ∀ y∈Y, ∃ l∈S, ∃ u∈S, l ≤ h y M ∧ h y (2*M) ≤ u)
    (x₁ x₂ : ℝ × (ℝ × ℝ) → ℝ) :
    let V := (Y ×ˢ (S ×ˢ S)).filter (fun i =>
      i.2.1 < i.2.2 ∧ (∀ z∈S, ¬(i.2.1 < z ∧ z < i.2.2)) ∧
        i.2.1 < h i.1 (2*M) ∧ h i.1 M < i.2.2)
    let G := V.filter (fun i => h i.1 M ≤ i.2.1 ∧ i.2.2 ≤ h i.1 (2*M))
    (∀ i∈G, x₁ i∈Icc M (2*M) ∧ x₂ i∈Icc M (2*M) ∧
      h i.1 (x₁ i)=i.2.1 ∧ h i.1 (x₂ i)=i.2.2) →
    (∀ i∈V, ∀ j∈I, ∀ k∈I,
      h i.1 (s+N*(j:ℝ))∈Icc i.2.1 i.2.2 →
      h i.1 (s+N*(k:ℝ))∈Icc i.2.1 i.2.2 →
      |(s+N*(k:ℝ))-(s+N*(j:ℝ))| ≤ C*N) →
    let Bad := (Y ×ˢ I).filter (fun p => ¬∃ i∈G, p.1=i.1 ∧
      x₁ i+N/4 ≤ s+N*(p.2:ℝ) ∧ s+N*(p.2:ℝ) ≤ x₂ i-N/4)
    (Bad.card:ℝ) ≤ 2*(V.card:ℝ)+C*((V\G).card:ℝ) := by
  classical
  intro V G hroots hwidth Bad
  let K := fun i : ℝ × (ℝ × ℝ) => I.filter (fun k : ℤ =>
    (i.1,k)∈Bad ∧ h i.1 (s+N*(k:ℝ))∈Icc i.2.1 i.2.2)
  have hVdata i (hi : i∈V) : i.1∈Y := by
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hi).1).1
  have hcover : Bad ⊆ V.biUnion (fun i => (K i).image (fun k => (i.1,k))) := by
    intro p hp
    have hpfull := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    obtain ⟨l,hl,u,hu,hlo,hhi⟩ := henclose p.1 hpfull.1
    have hleft : M∈Icc M (2*M) := ⟨le_rfl,by linarith only [hM]⟩
    have hright : 2*M∈Icc M (2*M) := ⟨by linarith only [hM],le_rfl⟩
    have hm := hmono p.1 hpfull.1
    have hpr := hI p.2 hpfull.2
    have hcurv : h p.1 (s+N*(p.2:ℝ))∈Icc (h p.1 M) (h p.1 (2*M)) :=
      ⟨hm.monotoneOn hleft hpr hpr.1,hm.monotoneOn hpr hright hpr.2⟩
    obtain ⟨a,ha,b,hb,hab,hax,hxb,hadj,hahi,hlob⟩ :=
      finite_reference_closed_bracket S hl hu hlo hhi
        (hm hleft hright (by linarith only [hM])) hcurv
    have hi : (p.1,(a,b))∈V :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨hpfull.1,Finset.mem_product.mpr ⟨ha,hb⟩⟩,hab,hadj,hahi,hlob⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨(p.1,(a,b)),hi,Finset.mem_image.mpr ?_⟩
    exact ⟨p.2,Finset.mem_filter.mpr ⟨hpfull.2,hp,hax,hxb⟩,Prod.eta p⟩
  have hKgood i (hi : i∈G) : (K i).card ≤ 2 := by
    apply trimmed_grid_boundary_card (K i) hN
    intro k hk
    have hh := Finset.mem_filter.mp hk
    have hr := hroots i hi
    have hm := hmono i.1 (hVdata i (Finset.mem_filter.mp hi).1)
    have hpk := hI k hh.1
    have hlo : x₁ i ≤ s+N*(k:ℝ) := by
      by_contra hnot
      have hz := hm hpk hr.1 (lt_of_not_ge hnot)
      rw [hr.2.2.1] at hz
      exact (not_lt_of_ge hh.2.2.1) hz
    have hhi : s+N*(k:ℝ) ≤ x₂ i := by
      by_contra hnot
      have hz := hm hr.2.1 hpk (lt_of_not_ge hnot)
      rw [hr.2.2.2] at hz
      exact (not_lt_of_ge hh.2.2.2) hz
    refine ⟨hlo,hhi,?_⟩
    intro htrim
    exact (Finset.mem_filter.mp hh.2.1).2 ⟨i,hi,rfl,htrim⟩
  have hKall i (hi : i∈V) : ((K i).card:ℝ) ≤ 2+C := by
    apply TaoTrudgianYang2025.HuxleyRationalPhase.physical_block_count_of_pairwise_width
      (K i) (fun k => s+N*(k:ℝ)) (Z:=s) hN hC
    · intro k _
      constructor <;> nlinarith only [hN]
    · intro j hj k hk
      have hjd := Finset.mem_filter.mp hj
      have hkd := Finset.mem_filter.mp hk
      exact hwidth i hi j hjd.1 k hkd.1 hjd.2.2 hkd.2.2
  have hcard : Bad.card ≤ ∑ i∈V, (K i).card :=
    (Finset.card_le_card hcover).trans (Finset.card_biUnion_le.trans
      (Finset.sum_le_sum (fun i _ => Finset.card_image_le)))
  have hcardR : (Bad.card:ℝ) ≤ ∑ i∈V, ((K i).card:ℝ) := by exact_mod_cast hcard
  have hsum : (∑ i∈V, ((K i).card:ℝ)) ≤
      ∑ i∈V, (2 + if i∈G then 0 else C) := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases hg : i∈G
    · simpa only [ite_eq_left hg,add_zero] using
        (show ((K i).card:ℝ) ≤ 2 by exact_mod_cast hKgood i hg)
    · simpa only [ite_eq_right hg] using hKall i hi
  have he : (∑ i∈V, (2 + if i∈G then (0:ℝ) else C)) =
      2*(V.card:ℝ)+C*((V\G).card:ℝ) := by
    rw [Finset.sum_add_distrib]
    have hid : (∑ i∈V, if i∈G then (0:ℝ) else C) = ∑ i∈V\G, C := by
      conv_rhs => rw [Finset.sdiff_eq_filter,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i∈G <;> simp only [hi,ite_true,ite_false,not_true_eq_false,not_false_eq_true]
    rw [hid]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  exact hcardR.trans (hsum.trans_eq he)


private theorem finite_sum_le_tagged_image_add_complement
    {α β : Type*} [DecidableEq α] (A : Finset α) (B : Finset β)
    (g : β → α) (w : α → ℝ) {N : ℝ}
    (hw : ∀ a, 0 ≤ w a) (hupper : ∀ a∈A, w a ≤ N) :
    (∑ a∈A, w a) ≤ (∑ b∈B, w (g b))+N*((A\B.image g).card:ℝ) := by
  classical
  have hc : (∑ a∈A∩B.image g, w a) ≤ ∑ b∈B, w (g b) :=
    (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun a _ _ => hw a)).trans (Finset.sum_image_le_of_nonneg (fun a _ => hw a))
  have hb : (∑ a∈A\B.image g, w a) ≤ N*((A\B.image g).card:ℝ) := by
    calc
      (∑ a∈A\B.image g, w a) ≤ ∑ _a∈A\B.image g, N :=
        Finset.sum_le_sum (fun a ha => hupper a (Finset.mem_sdiff.mp ha).1)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,mul_comm]
  have he : (∑ a∈A∩B.image g, w a)+(∑ a∈A\B.image g, w a)=∑ a∈A, w a := by
    simpa only [Finset.filter_mem_eq_inter,←Finset.sdiff_eq_filter] using
      Finset.sum_filter_add_sum_filter_not A (fun a => a∈B.image g) w
  linarith only [hc,hb,he]


                                                                                               
theorem positive_difference_reference_family_whole_grid_geometry
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
    (hsep : ∀ a∈S, ∀ b∈S, a≠b → U/(4*R^2) ≤ |a-b|)
    (hgapUpper : ∀ a∈S, ∀ b∈S, a<b →
      (∀ t∈S, ¬(a<t ∧ t<b)) → b-a ≤ 7*U/(2*R^2)) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let V := (Y ×ˢ (S ×ˢ S)).filter (fun i =>
      i.2.1 < i.2.2 ∧ (∀ t∈S, ¬(i.2.1 < t ∧ t < i.2.2)) ∧
        i.2.1 < h i.1 (2*M) ∧ h i.1 M < i.2.2)
    let G := V.filter (fun i => h i.1 M ≤ i.2.1 ∧ i.2.2 ≤ h i.1 (2*M))
    (V.card:ℝ) ≤ ((12*J/σ)*M/(N*U)+2)*(Y.card:ℝ) ∧
    (V \ G).card ≤ 2*Y.card ∧ (G.image Prod.fst).card ≤ Y.card ∧
    ∃ x₁ x₂ : ℝ × (ℝ × ℝ) → ℝ,
      (∀ i∈G, x₁ i∈Icc M (2*M) ∧ x₂ i∈Icc M (2*M) ∧ x₁ i < x₂ i ∧
        h i.1 (x₁ i)=i.2.1 ∧ h i.1 (x₂ i)=i.2.2 ∧
        U/(4*R^2) ≤ h i.1 (x₂ i)-h i.1 (x₁ i) ∧
        h i.1 (x₂ i)-h i.1 (x₁ i) ≤ 7*U/(2*R^2)) ∧
      (∀ i∈G, ∀ j∈G, i≠j → i.1=j.1 → x₂ i ≤ x₁ j ∨ x₂ j ≤ x₁ i) ∧
      (∀ (s : ℝ) (I : Finset ℤ),
        (∀ k∈I, s+N*(k:ℝ)∈Icc M (2*M)) →
        (∀ y∈Y, ∃ l∈S, ∃ u∈S, l ≤ h y M ∧ h y (2*M) ≤ u) →
        let Bad := (Y ×ˢ I).filter (fun p => ¬∃ i∈G, p.1=i.1 ∧
          x₁ i+N/4 ≤ s+N*(p.2:ℝ) ∧ s+N*(p.2:ℝ) ≤ x₂ i-N/4)
        let Inner := (G ×ˢ I).filter (fun i =>
          x₁ i.1+N/4 ≤ s+N*(i.2:ℝ) ∧ s+N*(i.2:ℝ) ≤ x₂ i.1-N/4)
        let ErrorCount := (Y.card:ℝ)*((24*J/σ)*M/(N*U)+28*σ*U/c+4)
        (Bad.card:ℝ) ≤ ErrorCount ∧
        ∀ (L : ℤ → ℤ) (H : ℝ → ℤ → ℕ),
          (∀ y∈Y, ∀ k∈I, (H y k:ℝ) ≤ N) →
          (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),
            (𝐞 (f p.1 n):ℂ)‖) ≤
          (∑ i∈Inner, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),
            (𝐞 (f i.1.1 n):ℂ)‖)+N*ErrorCount) := by
  classical
  intro f h V G
  obtain ⟨hpack,hboundary,hphaseCount,x₁,x₂,hgeometry,hdisjoint⟩ :=
    TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reference_family_interior_geometry
      F Y S hσ hc hJ hη hηmax hy hf hbound htests hnegative
      hT hM hN hR hU hphase hsep hgapUpper
  refine ⟨hpack,hboundary,hphaseCount,x₁,x₂,hgeometry,hdisjoint,?_⟩
  intro s I hI henclose Bad Inner ErrorCount
  have hm y (hyY : y∈Y) : StrictMonoOn (h y) (Icc M (2*M)) := by
    apply (TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_physical_curvature_strictMono
      F hσ hc hη hηmax (hy y hyY) hf hnegative hT hM).mono
    intro w hw
    constructor <;> linarith only [hw.1,hw.2,hM]
  have hraw := reference_grid_missing_card Y S I h hM hN
    (show 0 ≤ (14*σ/c)*U by positivity) hI hm henclose x₁ x₂
    (fun i hi => ⟨(hgeometry i hi).1,(hgeometry i hi).2.1,
      (hgeometry i hi).2.2.2.1,(hgeometry i hi).2.2.2.2.1⟩) (by
      intro i hi j hj k hk hjc hkc
      have hv := Finset.mem_filter.mp hi
      have hp := Finset.mem_product.mp hv.1
      have hs := Finset.mem_product.mp hp.2
      have hgap := hgapUpper _ hs.1 _ hs.2 hv.2.1 hv.2.2.1
      apply TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reference_preimage_width
        F hσ hc hη hηmax (hy i.1 hp.1) hf hnegative hT hM hN hR hphase
        (hI j hj) (hI k hk)
      change |h i.1 (s+N*(k:ℝ))-h i.1 (s+N*(j:ℝ))| ≤ 7*U/(2*R^2)
      apply (abs_le.mpr ?_).trans hgap
      constructor <;> linarith only [hjc.1,hjc.2,hkc.1,hkc.2])
  have hbd : ((V\G).card:ℝ) ≤ 2*(Y.card:ℝ) := by exact_mod_cast hboundary
  have hcount : (Bad.card:ℝ) ≤ ErrorCount := by
    calc
      (Bad.card:ℝ) ≤ 2*(V.card:ℝ)+((14*σ/c)*U)*((V\G).card:ℝ) := hraw
      _ ≤ 2*(((12*J/σ)*M/(N*U)+2)*(Y.card:ℝ))+
          ((14*σ/c)*U)*(2*(Y.card:ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hpack (by norm_num))
          (mul_le_mul_of_nonneg_left hbd (by positivity))
      _ = ErrorCount := by dsimp only [ErrorCount]; ring
  refine ⟨hcount,?_⟩
  intro L H hH
  let w := fun p : ℝ × ℤ => ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),
    (𝐞 (f p.1 n):ℂ)‖
  let tag := fun i : (ℝ × (ℝ × ℝ)) × ℤ => (i.1.1,i.2)
  have he : Bad=(Y ×ˢ I)\Inner.image tag := by
    ext p
    constructor
    · intro hp
      have hh := Finset.mem_filter.mp hp
      apply Finset.mem_sdiff.mpr
      refine ⟨hh.1,?_⟩
      intro hin
      obtain ⟨⟨i,k⟩,hik,hpeq⟩ := Finset.mem_image.mp hin
      have hd := Finset.mem_filter.mp hik
      have hg := Finset.mem_product.mp hd.1
      have hye : i.1=p.1 := congrArg Prod.fst hpeq
      have hke : k=p.2 := congrArg Prod.snd hpeq
      exact hh.2 ⟨i,hg.1,hye.symm,by simpa only [hke] using hd.2⟩
    · intro hp
      have hh := Finset.mem_sdiff.mp hp
      apply Finset.mem_filter.mpr
      refine ⟨hh.1,?_⟩
      rintro ⟨i,hi,hye,htrim⟩
      apply hh.2
      apply Finset.mem_image.mpr
      refine ⟨(i,p.2),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨hi,(Finset.mem_product.mp hh.1).2⟩,htrim⟩,?_⟩
      exact Prod.ext hye.symm rfl
  have hwbound p (hp : p∈Y ×ˢ I) : w p ≤ N := by
    have hh := Finset.mem_product.mp hp
    have hsum : w p ≤ H p.1 p.2 := by
      apply (norm_sum_le _ _).trans_eq
      simp
    exact hsum.trans (hH p.1 hh.1 p.2 hh.2)
  have hs := finite_sum_le_tagged_image_add_complement
    (Y ×ˢ I) Inner tag w (fun _ => norm_nonneg _) hwbound
  rw [←he] at hs
  exact hs.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hcount hN.le))


                                                                                                                                               
private theorem adjacent_reference_gap_card_closed
    (S : Finset ℝ) (G : Finset (ℝ × ℝ)) {lo hi d : ℝ}
    (hd : 0 < d) (hlohi : lo ≤ hi)
    (hsep : ∀ x∈S, ∀ y∈S, x≠y → d ≤ |x-y|)
    (hgap : ∀ ab∈G, ab.1∈S ∧ ab.2∈S ∧ ab.1<ab.2 ∧
      ∀ t∈S, ¬(ab.1<t ∧ t<ab.2))
    (hmeet : ∀ ab∈G, ab.1 ≤ hi ∧ lo ≤ ab.2) :
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
        ⟨hlt,hc.2.trans_le (hmeet ab ha.1).2⟩)
    · exact heq
    · exact False.elim ((hgap cd hc.1).2.2.2 _ (hgap ab ha.1).1
        ⟨hgt,ha.2.trans_le (hmeet cd hc.1).2⟩)
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
      exact ⟨le_of_not_gt ha.2,(hmeet ab ha.1).1⟩)
  have he : (G₁.image Prod.fst).card=G₁.card :=
    Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _))
  rw [he] at hlarge
  have hcard : G.card=G₀.card+G₁.card :=
    (Finset.card_filter_add_card_filter_not (s:=G) (fun ab => ab.1<lo)).symm
  have hcardR : (G.card:ℝ)=(G₀.card:ℝ)+(G₁.card:ℝ) := by exact_mod_cast hcard
  have hsmallR : (G₀.card:ℝ) ≤ 1 := by exact_mod_cast hsmall
  linarith only [hcardR,hsmallR,hlarge]


public  theorem reference_gap_count_of_closed_profile_width
    (S : Finset ℝ) (G : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ)
    {d D : ℝ} (hd : 0 < d) (hD : 0 ≤ D)
    (hsep : ∀ x∈S, ∀ y∈S, x≠y → d ≤ |x-y|)
    (hgap : ∀ ab∈G, ab.1∈S ∧ ab.2∈S ∧ ab.1 < ab.2 ∧
      ∀ t∈S, ¬(ab.1 < t ∧ t < ab.2))
    (hpoint : ∀ ab∈G, p ab∈Icc ab.1 ab.2)
    (hwidth : ∀ ab∈G, ∀ cd∈G, |p cd-p ab| ≤ D) :
    (G.card:ℝ) ≤ D/d+2 := by
  classical
  by_cases hG : G.Nonempty
  · let Values := G.image p
    have hv : Values.Nonempty := Finset.Nonempty.image hG p
    let lo := Values.min' hv
    let hi := Values.max' hv
    obtain ⟨ab,hab,hablo⟩ := Finset.mem_image.mp (Finset.min'_mem Values hv)
    obtain ⟨cd,hcd,hcdhi⟩ := Finset.mem_image.mp (Finset.max'_mem Values hv)
    have hbounds g (hg : g∈G) : lo ≤ p g ∧ p g ≤ hi :=
      ⟨Finset.min'_le Values _ (Finset.mem_image.mpr ⟨g,hg,rfl⟩),
        Finset.le_max' Values _ (Finset.mem_image.mpr ⟨g,hg,rfl⟩)⟩
    have hlohi : lo ≤ hi := (hbounds ab hab).1.trans (hbounds ab hab).2
    have hspan : hi-lo ≤ D := by
      change Values.max' hv-Values.min' hv ≤ D
      rw [←hablo,←hcdhi]
      exact (abs_le.mp (hwidth ab hab cd hcd)).2
    have hc := adjacent_reference_gap_card_closed S G hd hlohi hsep hgap (by
      intro g hg
      exact ⟨(hpoint g hg).1.trans (hbounds g hg).2,
        (hbounds g hg).1.trans (hpoint g hg).2⟩)
    exact hc.trans (add_le_add (div_le_div_of_nonneg_right hspan hd.le) le_rfl)
  · have he : G=∅ := Finset.not_nonempty_iff_eq_empty.mp hG
    rw [he]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity


private theorem paired_large_entry_closed_reference_gap_packing
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ))
    (x y : ℝ × ℝ → ℝ) (Mat : Fin 4 → ℤ)
    {σ δ T M R U Δ : ℝ} {τ A W : Fin 2 → ℝ} {F : Fin 2 → ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hτ : ∀ i, T ≤ τ i ∧ τ i ≤ 2*T)
    (hM : 0 < M) (hR : 0 < R) (hU : 0 < U) (hΔ : 0 ≤ Δ)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hMat : Mat 0*Mat 3-Mat 1*Mat 2=1) (hc : Mat 2≠0)
    (hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a≠b → U/(4*R^2) ≤ |a-b|)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ z∈Refs, ¬(ab.1 < z ∧ z < ab.2))
    (hx : ∀ ab∈Gaps, x ab∈Ioo (1/2:ℝ) (W 0-1/2))
    (hy : ∀ ab∈Gaps, y ab∈Ioo (1/2:ℝ) (W 1-1/2)) :
    let f := fun i => heathBrownPhysicalPhase (F i) (τ i) M (A i) 1
    let p := fun ab => iteratedDeriv 2 (f 0) (x ab)/2
    let mu := fun i z => iteratedDeriv 3 (f i) (round z)/6
    let t := fun ab => (Mat 2:ℝ)*p ab+Mat 3
    (∀ ab∈Gaps, p ab∈Icc ab.1 ab.2) →
    (∀ ab∈Gaps, ((Mat 0:ℝ)*p ab+Mat 1)/t ab=iteratedDeriv 2 (f 1) (y ab)/2) →
    (∀ ab∈Gaps, t ab∈Icc (1/2:ℝ) 2) →
    (∀ ab∈Gaps, |mu 1 (y ab)*(t ab)^3/mu 0 (x ab)-1| ≤ Δ) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let Gamma := Cphys/κ
    let eta := (modelPhaseJetCoefficient σ 3+δ)/(2*κ*M)
    (Gaps.card:ℝ) ≤ 64*Cphys*(Gamma^2*Δ+2*Gamma*eta)*R^2/
      (κ*|(Mat 2:ℝ)| *U)+2 := by
  classical
  intro f p mu t hpoint hmap ht hthird κ Cphys Gamma eta
  have hδ0 : 0 ≤ δ := approximateModelPhase_tolerance_nonneg (hF 0)
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCp : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hGamma : 0 < Gamma := div_pos hCp hκ
  have hC₃ : 0 ≤ modelPhaseJetCoefficient σ 3+δ :=
    add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have heta : 0 ≤ eta := by dsimp only [eta]; positivity
  have hcpos : 0 < |(Mat 2:ℝ)| := abs_pos.mpr (by exact_mod_cast hc)
  let Width := 16*Cphys*(Gamma^2*Δ+2*Gamma*eta)/(κ*|(Mat 2:ℝ)|)
  have hw0 : 0 ≤ Width := by dsimp only [Width]; positivity
  have hordered ab (hab : ab∈Gaps) cd (hcd : cd∈Gaps) (horder : p ab ≤ p cd) :
      p cd-p ab ≤ Width := by
    exact physicalModelPhase_paired_large_entry_curvature_diameter
      ![x ab,x cd] ![y ab,y cd] (Mat 0) (Mat 1) (Mat 2) (Mat 3)
      hσ hδ hδ0 hF hT hτ hM hA hW hΔ hMat hc hlarge
      (by intro i; fin_cases i; exact hx ab hab; exact hx cd hcd)
      (by intro i; fin_cases i; exact hy ab hab; exact hy cd hcd)
      horder
      (by intro i; fin_cases i; exact hmap ab hab; exact hmap cd hcd)
      (by intro i; fin_cases i; exact ht ab hab; exact ht cd hcd)
      (by intro i; fin_cases i; exact hthird ab hab; exact hthird cd hcd)
  have hwidth ab (hab : ab∈Gaps) cd (hcd : cd∈Gaps) : |p cd-p ab| ≤ Width := by
    by_cases hle : p ab ≤ p cd
    · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
      exact hordered ab hab cd hcd hle
    · rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hle))]
      exact hordered cd hcd ab hab (le_of_not_ge hle)
  have hp := reference_gap_count_of_closed_profile_width Refs Gaps p
    (show 0 < U/(4*R^2) by positivity) hw0 hsep hgap hpoint hwidth
  apply hp.trans_eq
  dsimp only [Width]
  field_simp
  ring_nf




private theorem paired_large_entry_reference_gap_packing
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ))
    (x y : ℝ × ℝ → ℝ) (Mat : Fin 4 → ℤ)
    {σ δ T M R U Δ : ℝ} {τ A W : Fin 2 → ℝ} {F : Fin 2 → ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hτ : ∀ i, T ≤ τ i ∧ τ i ≤ 2*T)
    (hM : 0 < M) (hR : 0 < R) (hU : 0 < U) (hΔ : 0 ≤ Δ)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hMat : Mat 0*Mat 3-Mat 1*Mat 2=1) (hc : Mat 2≠0)
    (hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a≠b → U/(4*R^2) ≤ |a-b|)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ z∈Refs, ¬(ab.1 < z ∧ z < ab.2))
    (hx : ∀ ab∈Gaps, x ab∈Ioo (1/2:ℝ) (W 0-1/2))
    (hy : ∀ ab∈Gaps, y ab∈Ioo (1/2:ℝ) (W 1-1/2)) :
    let f := fun i => heathBrownPhysicalPhase (F i) (τ i) M (A i) 1
    let p := fun ab => iteratedDeriv 2 (f 0) (x ab)/2
    let mu := fun i z => iteratedDeriv 3 (f i) (round z)/6
    let t := fun ab => (Mat 2:ℝ)*p ab+Mat 3
    (∀ ab∈Gaps, p ab∈Ioo ab.1 ab.2) →
    (∀ ab∈Gaps, ((Mat 0:ℝ)*p ab+Mat 1)/t ab=iteratedDeriv 2 (f 1) (y ab)/2) →
    (∀ ab∈Gaps, t ab∈Icc (1/2:ℝ) 2) →
    (∀ ab∈Gaps, |mu 1 (y ab)*(t ab)^3/mu 0 (x ab)-1| ≤ Δ) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let Gamma := Cphys/κ
    let eta := (modelPhaseJetCoefficient σ 3+δ)/(2*κ*M)
    (Gaps.card:ℝ) ≤ 64*Cphys*(Gamma^2*Δ+2*Gamma*eta)*R^2/
      (κ*|(Mat 2:ℝ)| *U)+2 := by
  intro f p mu t hpoint hmap ht hthird κ Cphys Gamma eta
  exact paired_large_entry_closed_reference_gap_packing Refs Gaps x y Mat
    hσ hδ hF hT hτ hM hR hU hΔ hA hW hMat hc hlarge hsep hgap hx hy
    (fun ab hab => ⟨(hpoint ab hab).1.le,(hpoint ab hab).2.le⟩) hmap ht hthird


public  theorem reference_chart_fraction_antitone {e v r s a b : ℝ}
    (hdet : v*r-e*s=1) (ha : 0 < r*a+s) (hb : 0 < r*b+s) (hab : a ≤ b) :
    (e*b+v)/(r*b+s) ≤ (e*a+v)/(r*a+s) := by
  apply (div_le_div_iff₀ hb ha).mpr
  have he : (e*a+v)*(r*b+s)-(e*b+v)*(r*a+s)=b-a := by
    linear_combination (b-a)*hdet
  have hh := sub_nonneg.mpr hab
  rw [←he] at hh
  exact sub_nonneg.mp hh


theorem physicalModelPhase_quartic_long_reference_gap_packing
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) (Mat : Fin 4 → ℤ)
    (x : ℝ × ℝ → Fin 4 → ℝ)
    (xref e r v s : ℝ × ℝ → Fin 2 → ℝ)
    (curve : ℝ × ℝ → ℝ → Fin 2 → ℝ) (d alpha beta : ℝ × ℝ → ℝ)
    {σ δ T M N R U L K : ℝ} {A W : Fin 2 → ℝ} {F : Fin 2 → ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hU : 0 < U) (hL : 0 < L) (hNL : (L*N)^2 ≤ M*R) (hK : 0 ≤ K)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hMat : Mat 0*Mat 3-Mat 1*Mat 2=1) (hc : Mat 2≠0)
    (hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a≠b → U/(4*R^2) ≤ |a-b|)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2))
    (hd : ∀ ab∈Gaps, 0 < d ab)
    (href : ∀ ab∈Gaps, ∀ i, xref ab i∈Ioo (1/2:ℝ) (W i-1/2))
    (hcurve : ∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i,
      curve ab t i∈Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ ab∈Gaps, ∀ i, r ab i≠0)
    (hdet : ∀ ab∈Gaps, ∀ i, v ab i*r ab i-e ab i*s ab i=1)
    (hden : ∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i,
      d ab ≤ r ab i*t+s ab i ∧ r ab i*t+s ab i ≤ 2*d ab)
    (hmono : ∀ ab∈Gaps, StrictMono (x ab))
    (htransport : ∀ ab∈Gaps,
      e ab 1=(Mat 0:ℝ)*e ab 0+Mat 1*r ab 0 ∧
      v ab 1=(Mat 0:ℝ)*v ab 0+Mat 1*s ab 0 ∧
      r ab 1=(Mat 2:ℝ)*e ab 0+Mat 3*r ab 0 ∧
      s ab 1=(Mat 2:ℝ)*v ab 0+Mat 3*s ab 0) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun ab t i => (round (curve ab t i):ℝ)-(round (xref ab i):ℝ)
    let mu := fun ab i => iteratedDeriv 3 (f i) (round (xref ab i))/6
    let munew := fun ab t i => iteratedDeriv 3 (f i) (round (curve ab t i))/6
    let nu := fun ab i => iteratedDeriv 4 (f i) (round (xref ab i))/24
    let Den := fun ab t i => r ab i*t+s ab i
    let g := fun ab => rationalPhase (mu ab 0) (r ab 0) (s ab 0) (mu ab 1) (r ab 1) (s ab 1)
    let H := fun ab => quarticPhase (mu ab 0) (nu ab 0) (r ab 0) (s ab 0)
      (mu ab 1) (nu ab 1) (r ab 1) (s ab 1)
    let Gcoord := fun ab => minorArcCoordinate (mu ab 0) (r ab 0) (s ab 0)
    let profile := fun ab t => iteratedDeriv 2 (f 0) (curve ab t 0)/2
    (∀ ab∈Gaps, ∀ i, iteratedDeriv 2 (f i) (xref ab i)/2=e ab i/r ab i) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i,
      iteratedDeriv 2 (f i) (curve ab t i)/2=(e ab i*t+v ab i)/Den ab t i) →
    (∀ ab∈Gaps, profile ab (x ab 0)∈Ioo ab.1 ab.2 ∧
      profile ab (x ab 3)∈Ioo ab.1 ab.2) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i, |n ab t i|^2 ≤ M*R) →
    (∀ ab∈Gaps, ∀ j : Fin 3, L*N ≤ |Gcoord ab (x ab j.succ)-Gcoord ab (x ab j.castSucc)|) →
    (∀ ab∈Gaps, ∀ j : Fin 4, |alpha ab*x ab j+beta ab-g ab (x ab j)+H ab (x ab j)| ≤
      K*R^2/|r ab 0*Gcoord ab (x ab j)|) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*K+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    ∃ z : ℝ × ℝ → ℝ,
      (∀ ab∈Gaps, z ab∈Ioo (x ab 0) (x ab 3) ∧ profile ab (z ab)∈Ioo ab.1 ab.2 ∧
        let t := (Mat 2:ℝ)*profile ab (z ab)+Mat 3
        t∈Icc (1/2:ℝ) 2 ∧
        ((Mat 0:ℝ)*profile ab (z ab)+Mat 1)/t=iteratedDeriv 2 (f 1) (curve ab (z ab) 1)/2 ∧
        |munew ab (z ab) 1*t^3/munew ab (z ab) 0-1| ≤ Cthird*R^2/(L^2*N^2)) ∧
      (Gaps.card:ℝ) ≤ Cpack*R^4/(L^2*N^2*|(Mat 2:ℝ)| *U)+2 := by
  classical
  intro f n mu munew nu Den g H Gcoord profile hbase hpoint hends hsquare hspacing hres
    κ Cphys Gamma Cthird Cpack
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCp : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hGamma : 0 < Gamma := div_pos hCp hκ
  have hδ0 : 0 ≤ δ := approximateModelPhase_tolerance_nonneg (hF 0)
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hC₄ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ0
  have hCR : 0 ≤ quarticReciprocalConstant σ δ := by
    dsimp only [quarticReciprocalConstant]
    positivity
  have hCt : 0 ≤ Cthird := by dsimp only [Cthird]; positivity
  have hdenpos ab (hab : ab∈Gaps) t (ht : t∈Icc (x ab 0) (x ab 3)) i :
      0 < Den ab t i := (hd ab hab).trans_le (hden ab hab t ht i).1
  have hex : ∀ ab∈Gaps, ∃ z∈Ioo (x ab 0) (x ab 3),
      |munew ab z 1*(Den ab z 1)^3/(munew ab z 0*(Den ab z 0)^3)-1| ≤ Cthird*R^2/(L^2*N^2) := by
    intro ab hab
    exact physicalModelPhase_quartic_long_block_third_condition (x ab)
      hσ hδ hF hT hM hN hR hL hNL (hd ab hab) hK hA hW
      (href ab hab) (hcurve ab hab) (hr ab hab) (hdet ab hab)
      (fun t ht i => (hden ab hab t ht i).1)
      (fun t ht i => (hden ab hab t ht i).2) (hmono ab hab)
      (hbase ab hab) (hpoint ab hab) (hsquare ab hab) (hspacing ab hab) (hres ab hab)
  choose! z hz hthird using hex
  have hzcc ab (hab : ab∈Gaps) : z ab∈Icc (x ab 0) (x ab 3) := ⟨(hz ab hab).1.le,(hz ab hab).2.le⟩
  have hinside ab (hab : ab∈Gaps) : profile ab (z ab)∈Ioo ab.1 ab.2 := by
    have hx03 : x ab 0 ≤ x ab 3 := (hmono ab hab).monotone (by decide)
    have hx0 : x ab 0∈Icc (x ab 0) (x ab 3) := ⟨le_rfl,hx03⟩
    have hx3 : x ab 3∈Icc (x ab 0) (x ab 3) := ⟨hx03,le_rfl⟩
    have hlow : profile ab (x ab 3) ≤ profile ab (z ab) := by
      dsimp only [profile]
      rw [hpoint ab hab _ hx3 0,hpoint ab hab _ (hzcc ab hab) 0]
      exact reference_chart_fraction_antitone (hdet ab hab 0)
        (hdenpos ab hab _ (hzcc ab hab) 0) (hdenpos ab hab _ hx3 0) (hzcc ab hab).2
    have hhigh : profile ab (z ab) ≤ profile ab (x ab 0) := by
      dsimp only [profile]
      rw [hpoint ab hab _ (hzcc ab hab) 0,hpoint ab hab _ hx0 0]
      exact reference_chart_fraction_antitone (hdet ab hab 0)
        (hdenpos ab hab _ hx0 0) (hdenpos ab hab _ (hzcc ab hab) 0) (hzcc ab hab).1
    exact ⟨(hends ab hab).2.1.trans_le hlow,hhigh.trans_lt (hends ab hab).1.2⟩
  let t := fun ab => (Mat 2:ℝ)*profile ab (z ab)+Mat 3
  have htid ab (hab : ab∈Gaps) : t ab=Den ab (z ab) 1/Den ab (z ab) 0 := by
    change (Mat 2:ℝ)*(iteratedDeriv 2 (f 0) (curve ab (z ab) 0)/2)+Mat 3=_
    rw [hpoint ab hab _ (hzcc ab hab) 0]
    apply (eq_div_iff (hdenpos ab hab _ (hzcc ab hab) 0).ne').mpr
    rw [add_mul,mul_assoc,div_mul_cancel₀ _ (hdenpos ab hab _ (hzcc ab hab) 0).ne']
    dsimp only [Den]
    rw [(htransport ab hab).2.2.1,(htransport ab hab).2.2.2]
    ring_nf
  have htband ab (hab : ab∈Gaps) : t ab∈Icc (1/2:ℝ) 2 := by
    rw [htid ab hab]
    constructor
    · apply (le_div_iff₀ (hdenpos ab hab _ (hzcc ab hab) 0)).mpr
      linarith only [(hden ab hab _ (hzcc ab hab) 1).1,(hden ab hab _ (hzcc ab hab) 0).2]
    · apply (div_le_iff₀ (hdenpos ab hab _ (hzcc ab hab) 0)).mpr
      linarith only [(hden ab hab _ (hzcc ab hab) 1).2,(hden ab hab _ (hzcc ab hab) 0).1]
  have hmap ab (hab : ab∈Gaps) :
      ((Mat 0:ℝ)*profile ab (z ab)+Mat 1)/t ab=
        iteratedDeriv 2 (f 1) (curve ab (z ab) 1)/2 := by
    rw [htid ab hab]
    have he : (Mat 0:ℝ)*profile ab (z ab)+Mat 1=
        (e ab 1*z ab+v ab 1)/Den ab (z ab) 0 := by
      change (Mat 0:ℝ)*(iteratedDeriv 2 (f 0) (curve ab (z ab) 0)/2)+Mat 1=_
      rw [hpoint ab hab _ (hzcc ab hab) 0]
      apply (eq_div_iff (hdenpos ab hab _ (hzcc ab hab) 0).ne').mpr
      rw [add_mul,mul_assoc,div_mul_cancel₀ _ (hdenpos ab hab _ (hzcc ab hab) 0).ne']
      rw [(htransport ab hab).1,(htransport ab hab).2.1]
      dsimp only [Den]
      ring_nf
    rw [he,div_div_div_cancel_right₀ (hdenpos ab hab _ (hzcc ab hab) 0).ne']
    exact (hpoint ab hab _ (hzcc ab hab) 1).symm
  have hthirdMat ab (hab : ab∈Gaps) :
      |munew ab (z ab) 1*(t ab)^3/munew ab (z ab) 0-1| ≤ Cthird*R^2/(L^2*N^2) := by
    rw [htid ab hab]
    have he : munew ab (z ab) 1*(Den ab (z ab) 1/Den ab (z ab) 0)^3/munew ab (z ab) 0=
        munew ab (z ab) 1*(Den ab (z ab) 1)^3/(munew ab (z ab) 0*(Den ab (z ab) 0)^3) := by
      rw [div_pow]
      ring_nf
    rw [he]
    exact hthird ab hab
  refine ⟨z,fun ab hab => ⟨hz ab hab,hinside ab hab,htband ab hab,hmap ab hab,hthirdMat ab hab⟩,?_⟩
  have hp := paired_large_entry_reference_gap_packing Refs Gaps
    (fun ab => curve ab (z ab) 0) (fun ab => curve ab (z ab) 1) Mat
    hσ hδ (fun i => approximateModelPhase_mono (hF i) (by norm_num : 3 ≤ 4) le_rfl)
    hT (fun _ => ⟨le_rfl,by linarith only [hT]⟩) hM hRpos hU
    (show 0 ≤ Cthird*R^2/(L^2*N^2) by positivity) hA hW hMat hc hlarge hsep hgap
    (fun ab hab => hcurve ab hab _ (hzcc ab hab) 0)
    (fun ab hab => hcurve ab hab _ (hzcc ab hab) 1)
    hinside hmap htband hthirdMat
  have hNL' : L^2*N^2 ≤ M*R^2 := by
    have hRR : R ≤ R^2 := by nlinarith only [hR]
    calc
      L^2*N^2 = (L*N)^2 := by ring_nf
      _ ≤ M*R := hNL
      _ ≤ M*R^2 := mul_le_mul_of_nonneg_left hRR hM.le
  have hInv : 1/M ≤ R^2/(L^2*N^2) :=
    (div_le_div_iff₀ hM (by positivity)).mpr (by simpa only [one_mul,mul_one,mul_comm] using hNL')
  have heta : 2*Gamma*((modelPhaseJetCoefficient σ 3+δ)/(2*κ*M)) ≤
      (Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)*(R^2/(L^2*N^2)) := by
    calc
      _ = (Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)*(1/M) := by ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left hInv (by positivity)
  apply hp.trans
  calc
    _ ≤ 64*Cphys*(Gamma^2*(Cthird*R^2/(L^2*N^2))+
        (Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)*(R^2/(L^2*N^2)))*R^2/
          (κ*|(Mat 2:ℝ)| *U)+2 := by
      apply add_le_add _ le_rfl
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg R)
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 64*Cphys)
      exact add_le_add le_rfl heta
    _ = Cpack*R^4/(L^2*N^2*|(Mat 2:ℝ)| *U)+2 := by
      dsimp only [Cpack]
      ring_nf



                                                                          
                                                                             
                                                                    
private theorem reciprocal_square_prefix (J : ℕ) :
    (∑ m∈Finset.range J, 1/((m:ℝ)+1)^2) ≤ 2-2/((J:ℝ)+1) := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    rw [Finset.sum_range_succ,Nat.cast_add,Nat.cast_one]
    have hJ : (0:ℝ) ≤ J := Nat.cast_nonneg J
    have hstep : 1/((J:ℝ)+1)^2 ≤ 2/((J:ℝ)+1)-2/((J:ℝ)+1+1) := by
      have h₁ : (J:ℝ)+1 ≠ 0 := by positivity
      have h₂ : (J:ℝ)+1+1 ≠ 0 := by positivity
      have he : 2/((J:ℝ)+1)-2/((J:ℝ)+1+1)=2/(((J:ℝ)+1)*((J:ℝ)+1+1)) := by
        field_simp
        ring
      rw [he]
      apply (div_le_div_iff₀ (by positivity : 0 < ((J:ℝ)+1)^2)
        (by positivity : 0 < ((J:ℝ)+1)*((J:ℝ)+1+1))).mpr
      nlinarith
    linarith only [ih,hstep]

private theorem finite_occupied_tail_sum
    {ι : Type*} (S : Finset ι) (n : ι → ℕ) (J : ℕ)
    {A B : ℝ} (hB : 0 ≤ B) (hcap : ∀ i∈S, n i ≤ J)
    (htail : ∀ m∈Finset.range J,
      ((S.filter (fun i => m < n i)).card:ℝ) ≤ A+B/((m:ℝ)+1)^2) :
    (∑ i∈S, (n i:ℝ)) ≤ A*(J:ℝ)+2*B := by
  classical
  have hrepr :
      (∑ m∈Finset.range J, ((S.filter (fun i => m < n i)).card:ℝ)) =
        ∑ i∈S, (n i:ℝ) := by
    calc
      _ = ∑ m∈Finset.range J, ∑ i∈S, if m < n i then (1:ℝ) else 0 := by
        simp
      _ = ∑ i∈S, ∑ m∈Finset.range J, if m < n i then (1:ℝ) else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        have hfilter : (Finset.range J).filter (fun m => m < n i)=Finset.range (n i) := by
          ext m
          simp only [Finset.mem_filter,Finset.mem_range]
          have hiCap := hcap i hi
          omega
        rw [← Finset.sum_filter,hfilter]
        simp
  rw [← hrepr]
  calc
    _ ≤ ∑ m∈Finset.range J, (A+B/((m:ℝ)+1)^2) := Finset.sum_le_sum htail
    _ = A*(J:ℝ)+B*(∑ m∈Finset.range J,1/((m:ℝ)+1)^2) := by
      simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,
        nsmul_eq_mul,div_eq_mul_inv,one_mul,Finset.mul_sum]
      ring
    _ ≤ A*(J:ℝ)+2*B := by
      have hh : (∑ m∈Finset.range J,1/((m:ℝ)+1)^2) ≤ 2 :=
        (reciprocal_square_prefix J).trans (sub_le_self _ (by positivity))
      nlinarith only [mul_le_mul_of_nonneg_left hh hB]

public  theorem finite_occupied_cubic_tail_sum
    {ι : Type*} (S : Finset ι) (n : ι → ℕ)
    {A B K c : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K) (hc : 0 < c)
    (hcap : ∀ i∈S, (n i:ℝ)^3*c ≤ K)
    (htail : ∀ m : ℕ, 0 < m →
      ((S.filter (fun i => m ≤ n i)).card:ℝ) ≤ A+B/(m:ℝ)^2) :
    (∑ i∈S, (n i:ℝ)) ≤ A*(K/c)^((3:ℝ)⁻¹)+2*B := by
  classical
  let J := S.sup n
  let root := (K/c)^((3:ℝ)⁻¹)
  have hroot : 0 ≤ root := Real.rpow_nonneg (div_nonneg hK hc.le) _
  have hrootcube : root^3=K/c :=
    Real.rpow_inv_natCast_pow (div_nonneg hK hc.le) (by norm_num : (3:ℕ) ≠ 0)
  have hJcube : (J:ℝ)^3 ≤ K/c := by
    by_cases hs : S.Nonempty
    · obtain ⟨i,hi,he⟩ := Finset.sup_mem_of_nonempty (f:=n) hs
      change n i=J at he
      rw [← he]
      exact (le_div_iff₀ hc).mpr (hcap i hi)
    · have hJzero : J=0 := by simp [J,Finset.not_nonempty_iff_eq_empty.mp hs]
      rw [hJzero]
      simpa using div_nonneg hK hc.le
  have hJ : (J:ℝ) ≤ root := (pow_le_pow_iff_left₀ (Nat.cast_nonneg J)
    hroot (by decide : (3:ℕ) ≠ 0)).mp (by rw [hrootcube]; exact hJcube)
  have hh := finite_occupied_tail_sum S n J hB (fun i hi => Finset.le_sup hi)
    (fun m _ => by
      simpa only [Nat.lt_iff_add_one_le,Nat.cast_add,Nat.cast_one] using htail (m+1) (by omega))
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hJ hA) le_rfl)


public  theorem quotient_block_mass (a b : ℕ) (hb : 0 < b) (hba : b ≤ a) :
    0 < a/b ∧ b*(a/b) ≤ a ∧ a ≤ 2*b*(a/b) := by
  have hpos := Nat.div_pos hba hb
  have hrem := Nat.mod_lt a hb
  have he := Nat.div_add_mod a b
  have hmul : b ≤ b*(a/b) := Nat.le_mul_of_pos_right b hpos
  refine ⟨hpos,Nat.mul_div_le a b,?_⟩
  nlinarith only [hrem,he,hmul]

private theorem two_term_first_cubic_cap
    {C A B N scale length n : ℝ}
    (hC : 0 ≤ C) (hN : 0 < N) (hs : 0 < scale)
    (hl : 0 < length) (hn : 0 ≤ n) (hshort : scale*n ≤ length)
    (hfirst : C ≤ A/(length^3*N^2)+B) (hsmall : 2*B ≤ C) :
    n^3*C ≤ 2*A/(scale^3*N^2) := by
  have hden : 0 < length^3*N^2 := by positivity
  have hhalf : C/2 ≤ A/(length^3*N^2) := by linarith only [hfirst,hsmall]
  have hm := (le_div_iff₀ hden).mp hhalf
  have hp := pow_le_pow_left₀ (mul_nonneg hs.le hn) hshort 3
  have hh := mul_le_mul_of_nonneg_right hp (mul_nonneg (sq_nonneg N) hC)
  apply (le_div_iff₀ (by positivity : 0 < scale^3*N^2)).mpr
  nlinarith only [hm,hh]

                                                                    
                                                                             
                                                                         
                                                               
private theorem physicalModelPhase_actual_fourier_large_entry_closed_reference_gap_count
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) (Mat : Fin 4 → ℤ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℝ × ℝ → Fin 2 → ℚ) (vinv : ℝ × ℝ → Fin 2 → ℤ)
    (parity : ℝ × ℝ → Fin 2 → Fin 2) (x : ℝ × ℝ → Fin 2 → ℝ)
    {σ δ T M N R U : ℝ} {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hU : 0 < U)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2) (hNscale : N^2 ≤ M*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hMat : Mat 0*Mat 3-Mat 1*Mat 2=1) (hc : Mat 2≠0)
    (hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a≠b → U/(4*R^2) ≤ |a-b|)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2))
    (hx : ∀ ab∈Gaps, ∀ i, x ab i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ ab∈Gaps, ∀ i, (rat ab i).den ≤ Q ∧ Q ≤ 2*(rat ab i).den)
    (hinv : ∀ ab∈Gaps, ∀ i, ((rat ab i).den:ℤ) ∣ (rat ab i).num*vinv ab i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ab∈Gaps, ∀ i, iteratedDeriv 2 (f i) (x ab i)/2=(rat ab i:ℝ)) →
    let q := fun ab i => (rat ab i).den
    let mu := fun ab i => iteratedDeriv 3 (f i) (round (x ab i))/6
    let ell := fun ab i => deriv (f i) (round (x ab i))
    let b := fun ab i => (⌊(q ab i:ℝ)*ell ab i⌋+(parity ab i:ℕ) : ℤ)
    let cround := fun ab i => round ((q ab i:ℝ)*ell ab i)
    let tau := fun ab i => ((b ab i:ℝ)-(q ab i:ℝ)*ell ab i)/2
    let dual := fun ab i => -2*mu ab i*(Real.sqrt (2/(3*mu ab i*(q ab i:ℝ))))^3
    let cloud := fun ab i => (![Int.fract (-(vinv ab i:ℝ)*b ab i/q ab i),
      Int.fract (-(vinv ab i:ℝ)/q ab i),dual ab i/Real.sqrt K₀,
      (3*dual ab i*tau ab i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ab∈Gaps, b ab 0-cround ab 0=b ab 1-cround ab 1) →
    (∀ ab∈Gaps, ∀ a, |cloud ab 0 a-cloud ab 1 a| ≤ 2*radius a) →
    (∀ ab∈Gaps, (Mat 2:ℝ)*(rat ab 0:ℝ)+Mat 3=(q ab 1:ℝ)/q ab 0) →
    (∀ ab∈Gaps, ((Mat 0:ℝ)*(rat ab 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat ab 0:ℝ)+Mat 3)=(rat ab 1:ℝ)) →
    (∀ ab∈Gaps, (rat ab 0:ℝ)∈Icc ab.1 ab.2) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let Gamma := Cphys/κ
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    (Gaps.card:ℝ) ≤ 2+Cgap*R^4/(N^2*|(Mat 2:ℝ)| *U) := by
  classical
  intro f hlevel q mu ell b cround tau dual cloud radius hcolor hnear hMatt hMatmap
    hsourceGap κ Cphys c J B Gamma Cgap
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hGamma : 0 < Gamma := div_pos hCphys hκ
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hδ0 := approximateModelPhase_tolerance_nonneg (hF 0)
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hratio ab (hab : ab∈Gaps) : (q ab 1:ℝ)/q ab 0∈Icc (1/2:ℝ) 2 := by
    have hq : (0:ℝ) < q ab 0 := by exact_mod_cast (rat ab 0).den_pos
    have hlo₀ : ((q ab 0):ℝ) ≤ Q := by exact_mod_cast (hden ab hab 0).1
    have hhi₀ : (Q:ℝ) ≤ 2*q ab 0 := by exact_mod_cast (hden ab hab 0).2
    have hlo₁ : ((q ab 1):ℝ) ≤ Q := by exact_mod_cast (hden ab hab 1).1
    have hhi₁ : (Q:ℝ) ≤ 2*q ab 1 := by exact_mod_cast (hden ab hab 1).2
    constructor
    · apply (le_div_iff₀ hq).mpr
      linarith only [hlo₀,hhi₁]
    · apply (div_le_iff₀ hq).mpr
      linarith only [hlo₁,hhi₀]
  have hthird ab (hab : ab∈Gaps) :
      |mu ab 1*((Mat 2:ℝ)*(iteratedDeriv 2 (f 0) (x ab 0)/2)+Mat 3)^3/mu ab 0-1| ≤ B*R^2/N^2 := by
    obtain ⟨_v,_hv,hh,_hrest⟩ := physicalModelPhase_actual_fourier_conditions
      Q K₀ (rat ab) (vinv ab) (parity ab)
      hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW
      (hx ab hab) (hden ab hab) (hinv ab hab) (hlevel ab hab)
      (hcolor ab hab) (hnear ab hab)
    rw [hlevel ab hab 0,hMatt ab hab]
    have he : mu ab 1*((q ab 1:ℝ)/q ab 0)^3/mu ab 0-1=
        mu ab 1*(q ab 1:ℝ)^3/(mu ab 0*(q ab 0:ℝ)^3)-1 := by
      rw [div_pow]
      ring_nf
    rw [he]
    exact hh
  have hp := paired_large_entry_closed_reference_gap_packing (τ:=fun _ => T)
    Refs Gaps (fun ab => x ab 0) (fun ab => x ab 1) Mat
    hσ hδ hF hT (fun _ => ⟨le_rfl,by linarith only [hT]⟩) hM hR hU
    (show 0 ≤ B*R^2/N^2 by positivity) hA hW hMat hc hlarge hsep hgap
    (fun ab hab => hx ab hab 0) (fun ab hab => hx ab hab 1)
    (fun ab hab => by
      change iteratedDeriv 2 (f 0) (x ab 0)/2∈Icc ab.1 ab.2
      rw [hlevel ab hab 0]
      exact hsourceGap ab hab)
    (fun ab hab => by
      change ((Mat 0:ℝ)*(iteratedDeriv 2 (f 0) (x ab 0)/2)+Mat 1)/
        ((Mat 2:ℝ)*(iteratedDeriv 2 (f 0) (x ab 0)/2)+Mat 3)=iteratedDeriv 2 (f 1) (x ab 1)/2
      rw [hlevel ab hab 0,hlevel ab hab 1]
      exact hMatmap ab hab)
    (fun ab hab => by
      change (Mat 2:ℝ)*(iteratedDeriv 2 (f 0) (x ab 0)/2)+Mat 3∈Icc (1/2:ℝ) 2
      rw [hlevel ab hab 0,hMatt ab hab]
      exact hratio ab hab)
    hthird
  have hInv : 1/M ≤ R^2/N^2 := (div_le_div_iff₀ hM (sq_pos_of_pos hN)).mpr
    (by simpa only [one_mul,mul_one,mul_comm] using hNscale)
  have heta : 2*Gamma*((modelPhaseJetCoefficient σ 3+δ)/(2*κ*M)) ≤
      (Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)*(R^2/N^2) := by
    calc
      _ = (Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)*(1/M) := by ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left hInv (by positivity)
  apply hp.trans
  calc
    _ ≤ 64*Cphys*(Gamma^2*(B*R^2/N^2)+
        (Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)*(R^2/N^2))*R^2/
        (κ*|(Mat 2:ℝ)| *U)+2 := by
      apply add_le_add _ le_rfl
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg R)
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 64*Cphys)
      exact add_le_add le_rfl heta
    _ = _ := by dsimp only [Cgap]; ring_nf


                                                                        
                                                                             
                                                                            
private theorem charted_selected_blocks
    {b B c C n nSource nSelected : ℕ}
    (hc : 0 < c) (hbB : b ≤ B) (hcC : c ≤ C) (hn : 0 < n)
    (hselection : nSource ≤ 6+c*(105+17*nSelected))
    (hblocks : (6+C*(105+544*B))*n ≤ nSource) :
    32*b*n ≤ nSelected := by
  have hbudget : 6+c*(105+544*b) ≤ 6+C*(105+544*B) := by gcongr
  have hlower := (Nat.mul_le_mul_right n hbudget).trans hblocks
  have hoffset : 6+105*c ≤ (6+105*c)*n := Nat.le_mul_of_pos_right _ hn
  have hmul : c*(17*(32*b*n)) ≤ c*(17*nSelected) := by
    nlinarith only [hlower,hselection,hoffset]
  have hh := Nat.le_of_mul_le_mul_left hmul hc
  exact Nat.le_of_mul_le_mul_left hh (by decide : 0 < (17:ℕ))

                                                                  
                                                                     
public  theorem charted_selected_source_length
    {b B c C n nSource nSelected : ℕ} {κ Cphys : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hbB : b ≤ B) (hcC : c ≤ C) (hn : 0 < n)
    (hκ : 0 < κ) (hCphys : 0 < Cphys)
    (hselection : nSource ≤ 6+c*(105+17*nSelected))
    (hblocks : (6+C*(105+544*B))*n ≤ nSource) :
    (2*κ/Cphys)*(n:ℝ) ≤ κ/(16*(b:ℝ)*Cphys)*(nSelected:ℝ) := by
  have hmass : (32:ℝ)*(b:ℝ)*(n:ℝ) ≤ (nSelected:ℝ) := by
    exact_mod_cast charted_selected_blocks hc hbB hcC hn hselection hblocks
  have hbreal : (0:ℝ) < b := Nat.cast_pos.mpr hb
  calc
    _ = κ/(16*(b:ℝ)*Cphys)*((32:ℝ)*(b:ℝ)*(n:ℝ)) := by
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)

                                                                 
                                                                     
                                                                     
                                                                    
                                                                        
theorem physicalModelPhase_actual_fourier_charted_long_gap_packing
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Bmajor Cmajor n : ℕ) (hn : 0 < n)
    (S : ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℝ × ℝ → ℕ → Fin 2 → ℚ) (vinv : ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : ℝ × ℝ → ℕ → Fin 2 → Fin 2) (anchor : ℝ × ℝ → ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℝ × ℝ → ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T)
    (hM : 0 < M)
    (hN : 0 < N)
    (hR : 1 ≤ R)
    (hRM : R ≤ M)
    (hQ : 0 < Q)
    (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i)
    (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ ab∈Gaps, ∀ j∈(S ab), (x ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hden : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, ((rat ab) j i).den ≤ Q ∧ Q ≤ 2*((rat ab) j i).den)
    (hlambda : 0 < lambda)
    (hUband : 0 ≤ Uband)
    (hθ : 0 < θ)
    (hθmax : θ ≤ 1/24)
    (hcurv : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, lambda ≤ |((rat ab) j i:ℝ)| ∧ |((rat ab) j i:ℝ)| ≤ Uband)
    (hinv : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (((rat ab) j i).den:ℤ) ∣ ((rat ab) j i).num*(vinv ab) j i-1)
    (hchart : ∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1)
    (horientation : ∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2))
    (hBcut : 0 < Bcut)
    (hs : ∀ ab∈Gaps, (s ab) ≠ 0)
    (hrefSet : ∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs)
    (hparentSet : ∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hwideL : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : ∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ))
    (hgapWidth : ∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2))
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ ab∈Gaps, ∀ j∈(S ab), ((rat ab) j 0:ℝ)∈Icc ab.1 ab.2)
    (hc : Mat 2 ≠ 0)
    (hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun (ab : ℝ × ℝ) => fun j i => (⌊(((rat ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊(((rat ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ab∈Gaps, ∀ j∈(S ab), (sourceColor ab) j 0=(sourceColor ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, iteratedDeriv 2 (f i) ((x ab) j i)/2=((rat ab) j i:ℝ)) →
    let q := fun (ab : ℝ × ℝ) => fun j i => ((rat ab) j i).den
    let mu := fun (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round ((x ab) j i))/6
    let ell := fun (ab : ℝ × ℝ) => fun j i => deriv (f i) (round ((x ab) j i))
    let b := fun (ab : ℝ × ℝ) => fun j i => (⌊((q ab) j i:ℝ)*(ell ab) j i⌋+((parity ab) j i:ℕ) : ℤ)
    let cround := fun (ab : ℝ × ℝ) => fun j i => round (((q ab) j i:ℝ)*(ell ab) j i)
    let tau := fun (ab : ℝ × ℝ) => fun j i => (((b ab) j i:ℝ)-((q ab) j i:ℝ)*(ell ab) j i)/2
    let dual := fun (ab : ℝ × ℝ) => fun j i => -2*(mu ab) j i*(Real.sqrt (2/(3*(mu ab) j i*((q ab) j i:ℝ))))^3
    let cloud := fun (ab : ℝ × ℝ) => fun j i => (![Int.fract (-((vinv ab) j i:ℝ)*(b ab) j i/(q ab) j i),
      Int.fract (-((vinv ab) j i:ℝ)/(q ab) j i),(dual ab) j i/Real.sqrt K₀,
      (3*(dual ab) j i*(tau ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ab∈Gaps, ∀ j∈(S ab), (b ab) j 0-(cround ab) j 0=(b ab) j 1-(cround ab) j 1) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ a, |(cloud ab) j 0 a-(cloud ab) j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ ab∈Gaps, ∀ j∈(S ab), (Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3=((q ab) j 1:ℝ)/(q ab) j 0) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ((Mat 0:ℝ)*((rat ab) j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3)=((rat ab) j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), |((anchor ab) j:ℝ)-((rat ab) j 0:ℝ)| ≤ ε) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256*(((anchor ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*((anchor ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    (∀ ab∈Gaps, m0*n ≤ (S ab).card) →
    let L := (2*κ/Cphys)*(n:ℝ)
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    (Gaps.Nonempty →
      |(Mat 2:ℝ)| ≤ Cfirst*R^4/(L^3*N^2)+Csecond*N*R^2/M) ∧
    (Gaps.card:ℝ) ≤ Cpack*R^4/(L^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ))+2 := by
  classical
  intro Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor hblocks L Gamma Cthird Cpack Cfirst Csecond
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hLp : 0 < L := by dsimp only [L]; positivity
  have hUp : (0:ℝ) < Uref := by exact_mod_cast (show 0 < Uref by omega)
  have hS ab (hab : ab∈Gaps) :
      6+Ccharts ab*(105+544*Blabels ab) ≤ (S ab).card := by
    have hb : 6+Ccharts ab*(105+544*Blabels ab) ≤ m0 := by
      dsimp only [m0]
      gcongr
      exact hCmajor ab hab
      exact hBmajor ab hab
    exact hb.trans ((Nat.le_mul_of_pos_right m0 hn).trans (hblocks ab hab))
  have hall ab (hab : ab∈Gaps) :=
    physicalModelPhase_actual_fourier_charted_reference_gap_quartic_witnesses
      Uref Refs (Bselect:=Bselect) (gapLo:=ab.1) (gapHi:=ab.2)
      (S ab) Q K₀ (rat ab) (vinv ab) (parity ab) (anchor ab) Mat
      (e ab) (r ab) (v ab) (s ab)
      hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW (hx ab hab) (hwindow ab hab) (hden ab hab) hlambda hUband hθ hθmax (hcurv ab hab) (hinv ab hab) (hchart ab hab) (horientation ab hab) hBcut (hs ab hab) (hrefSet ab hab) (hparentSet ab hab) hsep (hwideL ab hab) (hwideU ab hab) hUref hBselectSize hcutMargin hselectedWrap (hreferenceDen ab hab) (hgapWidth ab hab) hRQ hselectedUpper hscaleTen (hfamilyGap ab hab)
      (hsourceColor ab hab) (hS ab hab) (hlevel ab hab) (hcolor ab hab) (hnear ab hab)
      hsmall hNR hRN hNcube hminscale hMatdet (hMatt ab hab) (hMatmap ab hab) hMatgamma
      hNtwo (hL ab hab) (hU ab hab) (hanchor ab hab) (hcut ab hab) (hcount ab hab)
  choose! Schart hSchart hSmass Good hGood hGoodmass jref hjref xref hxr hrest using hall
  have hselected ab (hab : ab∈Gaps) := hrest ab hab hsize hD hΔ hBsize
  choose! d l w hd S₀ hS₀ hcard hinside j z curve alpha beta hj hmono hLsource hNL hKp
    hcurve hspacing hres using hselected
  let ep := fun ab => (![e ab,Mat 0*e ab+Mat 1*r ab] : Fin 2 → ℤ)
  let rp := fun ab => (![r ab,Mat 2*e ab+Mat 3*r ab] : Fin 2 → ℤ)
  let vp := fun ab => (![v ab,Mat 0*v ab+Mat 1*s ab] : Fin 2 → ℤ)
  let sp := fun ab => (![s ab,Mat 2*v ab+Mat 3*s ab] : Fin 2 → ℤ)
  have hlong ab (hab : ab∈Gaps) :
      L ≤ κ/(16*(Blabels ab:ℝ)*Cphys)*((S₀ ab).card:ℝ) :=
    charted_selected_source_length
      (by dsimp only [Blabels]; omega) (by dsimp only [Ccharts]; omega)
      (hBmajor ab hab) (hCmajor ab hab) hn hκ hCphys (hcard ab hab) (hblocks ab hab)
  by_cases hne : Gaps.Nonempty
  · obtain ⟨ab₀,hab₀⟩ := hne
    have hδ0 := approximateModelPhase_tolerance_nonneg (hF 0)
    have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
    have hCR := (physical_source_quartic_constants_nonneg hσ hδ0).1
    have hΓ : 0 ≤ Gamma := div_nonneg hCphys.le hκ.le
    have hCthird : 0 ≤ Cthird :=
      mul_nonneg hΓ (add_nonneg (mul_nonneg (by norm_num) (hKp ab₀ hab₀))
        (mul_nonneg (by norm_num) hCR))
    have hCfirst : 0 ≤ Cfirst :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCphys.le)
        (add_nonneg (mul_nonneg (sq_nonneg Gamma) hCthird)
          (div_nonneg (mul_nonneg hΓ hC₃) hκ.le))) (sq_nonneg κ)
    have hNLL : (L*N)^2 ≤ M*R :=
      (pow_le_pow_left₀ (mul_pos hLp hN).le
        (mul_le_mul_of_nonneg_right (hlong ab₀ hab₀) hN.le) 2).trans (hNL ab₀ hab₀)
    let take : Fin 4 → Fin 8 := fun i => ⟨i.val,by omega⟩
    have htake : StrictMono take := fun _ _ hh => hh
    let z4 := fun ab i => z ab (take i)
    have hsub ab (hab : ab∈Gaps) : Icc (z4 ab 0) (z4 ab 3) ⊆ Icc (z ab 0) (z ab 7) := by
      intro t ht
      exact ⟨ht.1,ht.2.trans ((hmono ab hab).monotone (by change (3:Fin 8) ≤ 7; decide))⟩
    have hdetp ab (hab : ab∈Gaps) i : vp ab i*rp ab i-ep ab i*sp ab i=1 := by
      fin_cases i
      · exact hchart ab hab
      · change (Mat 0*v ab+Mat 1*s ab)*(Mat 2*e ab+Mat 3*r ab)-
          (Mat 0*e ab+Mat 1*r ab)*(Mat 2*v ab+Mat 3*s ab)=1
        linear_combination (v ab*r ab-e ab*s ab)*hMatdet+hchart ab hab
    have htransport ab : (ep ab 1:ℝ)=(Mat 0:ℝ)*ep ab 0+Mat 1*rp ab 0 ∧
        (vp ab 1:ℝ)=(Mat 0:ℝ)*vp ab 0+Mat 1*sp ab 0 ∧
        (rp ab 1:ℝ)=(Mat 2:ℝ)*ep ab 0+Mat 3*rp ab 0 ∧
        (sp ab 1:ℝ)=(Mat 2:ℝ)*vp ab 0+Mat 3*sp ab 0 := by
      simp [ep,vp,rp,sp,Int.cast_add,Int.cast_mul]
    have hends ab (hab : ab∈Gaps) (a : Fin 4) :
        iteratedDeriv 2 (f 0) (curve ab (z4 ab a) 0)/2∈Ioo ab.1 ab.2 := by
      have ha : z4 ab a∈Icc (z ab 0) (z ab 7) :=
        ⟨(hmono ab hab).monotone (by omega),(hmono ab hab).monotone (by omega)⟩
      rw [((hcurve ab hab _ ha).2 0).2.2.2.1,←(hj ab hab (take a)).2 0]
      exact hinside ab hab _ (hj ab hab (take a)).1
    have hFirst := physicalModelPhase_quartic_matrix_long_block_first_condition
      (e:=fun i => (ep ab₀ i:ℝ)) (r:=fun i => (rp ab₀ i:ℝ))
      (v:=fun i => (vp ab₀ i:ℝ)) (s:=fun i => (sp ab₀ i:ℝ))
      (x₁:=curve ab₀) (α:=alpha ab₀) (β:=beta ab₀) (z ab₀) Mat
      hσ hδ hF hT hM hN hR (hLsource ab₀ hab₀) (hNL ab₀ hab₀) (hd ab₀ hab₀)
      (hKp ab₀ hab₀) hA hW (fun i => (hxr ab₀ hab₀ i).2.1)
      (fun t ht i => ((hcurve ab₀ hab₀ t ht).2 i).1)
      (fun i => by
        exact_mod_cast (mul_ne_zero_iff.mp (hxr ab₀ hab₀ i).1.ne').1)
      (fun i => by
        exact_mod_cast hdetp ab₀ hab₀ i)
      (fun t ht i => ((hcurve ab₀ hab₀ t ht).2 i).2.1)
      (fun t ht i => ((hcurve ab₀ hab₀ t ht).2 i).2.2.1)
      (hmono ab₀ hab₀) hscale hMatdet (htransport ab₀)
      (fun i => (hxr ab₀ hab₀ i).2.2.1)
      (fun t ht i => ((hcurve ab₀ hab₀ t ht).2 i).2.2.2.1)
      (fun t ht i => ((hcurve ab₀ hab₀ t ht).2 i).2.2.2.2)
      (hspacing ab₀ hab₀) (hres ab₀ hab₀)
    have hFirstUnit :
        |(Mat 2:ℝ)| ≤ Cfirst*R^4/(L^3*N^2)+Csecond*N*R^2/M := by
      apply hFirst.trans
      apply add_le_add _ le_rfl
      apply div_le_div_of_nonneg_left (mul_nonneg hCfirst (by positivity)) (by positivity)
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hLp.le (hlong ab₀ hab₀) 3) (sq_nonneg N)
    obtain ⟨_t,_ht,hpack⟩ := physicalModelPhase_quartic_long_reference_gap_packing
      Refs Gaps Mat z4 xref
      (fun ab i => (ep ab i:ℝ)) (fun ab i => (rp ab i:ℝ))
      (fun ab i => (vp ab i:ℝ)) (fun ab i => (sp ab i:ℝ))
      curve d alpha beta hσ hδ hF hT hM hN hR hUp hLp hNLL (hKp ab₀ hab₀)
      hA hW hMatdet hc hlarge
      (by
        intro a ha b hb hne
        calc
          (Uref:ℝ)/(4*R^2)=((Uref:ℝ)/R^2)/4 := by ring
          _ ≤ |a-b| := (hsep a ha b hb hne).le)
      hgap hd
      (fun ab hab i => (hxr ab hab i).2.1)
      (fun ab hab t ht i => ((hcurve ab hab t (hsub ab hab ht)).2 i).1)
      (fun ab hab i => by
        exact_mod_cast (mul_ne_zero_iff.mp (hxr ab hab i).1.ne').1)
      (fun ab hab i => by
        exact_mod_cast hdetp ab hab i)
      (fun ab hab t ht i => ⟨((hcurve ab hab t (hsub ab hab ht)).2 i).2.1,
        ((hcurve ab hab t (hsub ab hab ht)).2 i).2.2.1⟩)
      (fun ab hab => (hmono ab hab).comp htake) (fun ab _ => htransport ab)
      (fun ab hab i => (hxr ab hab i).2.2.1)
      (fun ab hab t ht i => ((hcurve ab hab t (hsub ab hab ht)).2 i).2.2.2.1)
      (fun ab hab => ⟨hends ab hab 0,hends ab hab 3⟩)
      (fun ab hab t ht i => ((hcurve ab hab t (hsub ab hab ht)).2 i).2.2.2.2)
      (fun ab hab i => (mul_le_mul_of_nonneg_right (hlong ab hab) hN.le).trans
        (hspacing ab hab (⟨i.val,by omega⟩ : Fin 7)))
      (fun ab hab i => hres ab hab (take i))
    exact ⟨fun _ => hFirstUnit,hpack⟩
  · refine ⟨fun hh => False.elim (hne hh),?_⟩
    rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero]
    have hδ0 := approximateModelPhase_tolerance_nonneg (hF 0)
    have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
    have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
    obtain ⟨hCR,hCN⟩ := physical_source_quartic_constants_nonneg hσ hδ0
    have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
    dsimp only [Cpack,Cthird,Kres,Gamma,Cc,Ct,C₂,C₃]
    positivity


                                                                       
                                                                          
theorem physicalModelPhase_actual_fourier_charted_reference_sample_mass
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Bmajor Cmajor : ℕ)
    (S : ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℝ × ℝ → ℕ → Fin 2 → ℚ) (vinv : ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : ℝ × ℝ → ℕ → Fin 2 → Fin 2) (anchor : ℝ × ℝ → ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℝ × ℝ → ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T)
    (hM : 0 < M)
    (hN : 0 < N)
    (hR : 1 ≤ R)
    (hRM : R ≤ M)
    (hQ : 0 < Q)
    (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i)
    (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ ab∈Gaps, ∀ j∈(S ab), (x ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hden : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, ((rat ab) j i).den ≤ Q ∧ Q ≤ 2*((rat ab) j i).den)
    (hlambda : 0 < lambda)
    (hUband : 0 ≤ Uband)
    (hθ : 0 < θ)
    (hθmax : θ ≤ 1/24)
    (hcurv : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, lambda ≤ |((rat ab) j i:ℝ)| ∧ |((rat ab) j i:ℝ)| ≤ Uband)
    (hinv : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (((rat ab) j i).den:ℤ) ∣ ((rat ab) j i).num*(vinv ab) j i-1)
    (hchart : ∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1)
    (horientation : ∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2))
    (hBcut : 0 < Bcut)
    (hs : ∀ ab∈Gaps, (s ab) ≠ 0)
    (hrefSet : ∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs)
    (hparentSet : ∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hwideL : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : ∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ))
    (hgapWidth : ∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2))
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ ab∈Gaps, ∀ j∈(S ab), ((rat ab) j 0:ℝ)∈Icc ab.1 ab.2)
    (hc : Mat 2 ≠ 0)
    (hlarge : 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun (ab : ℝ × ℝ) => fun j i => (⌊(((rat ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊(((rat ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ab∈Gaps, ∀ j∈(S ab), (sourceColor ab) j 0=(sourceColor ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, iteratedDeriv 2 (f i) ((x ab) j i)/2=((rat ab) j i:ℝ)) →
    let q := fun (ab : ℝ × ℝ) => fun j i => ((rat ab) j i).den
    let mu := fun (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round ((x ab) j i))/6
    let ell := fun (ab : ℝ × ℝ) => fun j i => deriv (f i) (round ((x ab) j i))
    let b := fun (ab : ℝ × ℝ) => fun j i => (⌊((q ab) j i:ℝ)*(ell ab) j i⌋+((parity ab) j i:ℕ) : ℤ)
    let cround := fun (ab : ℝ × ℝ) => fun j i => round (((q ab) j i:ℝ)*(ell ab) j i)
    let tau := fun (ab : ℝ × ℝ) => fun j i => (((b ab) j i:ℝ)-((q ab) j i:ℝ)*(ell ab) j i)/2
    let dual := fun (ab : ℝ × ℝ) => fun j i => -2*(mu ab) j i*(Real.sqrt (2/(3*(mu ab) j i*((q ab) j i:ℝ))))^3
    let cloud := fun (ab : ℝ × ℝ) => fun j i => (![Int.fract (-((vinv ab) j i:ℝ)*(b ab) j i/(q ab) j i),
      Int.fract (-((vinv ab) j i:ℝ)/(q ab) j i),(dual ab) j i/Real.sqrt K₀,
      (3*(dual ab) j i*(tau ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ab∈Gaps, ∀ j∈(S ab), (b ab) j 0-(cround ab) j 0=(b ab) j 1-(cround ab) j 1) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ a, |(cloud ab) j 0 a-(cloud ab) j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ ab∈Gaps, ∀ j∈(S ab), (Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3=((q ab) j 1:ℝ)/(q ab) j 0) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ((Mat 0:ℝ)*((rat ab) j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3)=((rat ab) j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), |((anchor ab) j:ℝ)-((rat ab) j 0:ℝ)| ≤ ε) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256*(((anchor ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*((anchor ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    (∀ ab∈Gaps, m0 ≤ (S ab).card) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤
      4*(m0:ℝ)*((2*Cfirst*R^4/(Lunit^3*N^2)/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+
        Cpack*R^4/(Lunit^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ))) := by
  classical
  intro Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor hS Lunit Gamma Cthird Cpack Cfirst
  let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hunit : 0 < Lunit := div_pos (mul_pos (by norm_num) hκ) hCphys
  have hm0 : 0 < m0 := by dsimp only [m0]; omega
  have hUp : (0:ℝ) < Uref := by exact_mod_cast (show 0 < Uref by omega)
  have hδ0 := approximateModelPhase_tolerance_nonneg (hF 0)
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  obtain ⟨hCR,hCN⟩ := physical_source_quartic_constants_nonneg hσ hδ0
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hCt : 0 ≤ Ct := by dsimp only [Ct]; positivity
  have hCc : 0 ≤ Cc := by dsimp only [Cc]; positivity
  have hK : 0 ≤ Kres := by dsimp only [Kres]; positivity
  have hΓ : 0 ≤ Gamma := div_nonneg hCphys.le hκ.le
  have hCthird : 0 ≤ Cthird :=
    mul_nonneg hΓ (add_nonneg (mul_nonneg (by norm_num) hK)
      (mul_nonneg (by norm_num) hCR))
  have hcore : 0 ≤ Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ :=
    add_nonneg (mul_nonneg (sq_nonneg Gamma) hCthird)
      (div_nonneg (mul_nonneg hΓ hC₃) hκ.le)
  have hCpack : 0 ≤ Cpack :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCphys.le) hcore) hκ.le
  have hCfirst : 0 ≤ Cfirst :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCphys.le) hcore) (sq_nonneg κ)
  have hCmat : 0 < |(Mat 2:ℝ)| := abs_pos.mpr (by exact_mod_cast hc)
  have hlarge32 : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *κ^2*T := by
    have hn := mul_nonneg hC₃ (sq_nonneg M)
    nlinarith only [hlarge,hn]
  have habsorb : 2*(Csecond*N*R^2/M) ≤ |(Mat 2:ℝ)| := by
    have hs : 64*(modelPhaseJetCoefficient σ 3+δ)*N*R^2 ≤ |(Mat 2:ℝ)| *κ^2*M := by
      apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hM)).mp
      calc
        _ = (64*(modelPhaseJetCoefficient σ 3+δ)*M^2)*(N*R^2) := by ring
        _ ≤ (|(Mat 2:ℝ)| *κ^2*T)*(N*R^2) :=
          mul_le_mul_of_nonneg_right hlarge (by positivity)
        _ = (|(Mat 2:ℝ)| *κ^2)*(T*N*R^2) := by ring
        _ = _ := by rw [hscale]; ring
    calc
      _ = (64*(modelPhaseJetCoefficient σ 3+δ)*N*R^2)/(κ^2*M) := by
        dsimp only [Csecond]
        ring
      _ ≤ _ := (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hs])
  let n := fun ab => (S ab).card/m0
  have hn ab (hab : ab∈Gaps) := quotient_block_mass (S ab).card m0 hm0 (hS ab hab)
  have hfamily (G : Finset (ℝ × ℝ)) (hsub : G ⊆ Gaps) (m : ℕ) (hm : 0 < m)
      (hblocks : ∀ ab∈G, m0*m ≤ (S ab).card) :
      (G.Nonempty → |(Mat 2:ℝ)| ≤
        Cfirst*R^4/((Lunit*(m:ℝ))^3*N^2)+Csecond*N*R^2/M) ∧
      (G.card:ℝ) ≤ Cpack*R^4/((Lunit*(m:ℝ))^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ))+2 := by
    exact physicalModelPhase_actual_fourier_charted_long_gap_packing
      Uref Refs G (Bselect:=Bselect) Bmajor Cmajor m hm
      S Q K₀ rat vinv parity anchor Mat e r v s
      hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW (fun ab hab => hx ab (hsub hab)) (fun ab hab => hwindow ab (hsub hab)) (fun ab hab => hden ab (hsub hab)) hlambda hUband hθ hθmax (fun ab hab => hcurv ab (hsub hab)) (fun ab hab => hinv ab (hsub hab)) (fun ab hab => hchart ab (hsub hab)) (fun ab hab => horientation ab (hsub hab)) hBcut (fun ab hab => hs ab (hsub hab)) (fun ab hab => hrefSet ab (hsub hab)) (fun ab hab => hparentSet ab (hsub hab)) hsep (fun ab hab => hwideL ab (hsub hab)) (fun ab hab => hwideU ab (hsub hab)) hUref hBselectSize hcutMargin hselectedWrap (fun ab hab => hreferenceDen ab (hsub hab)) (fun ab hab => hgapWidth ab (hsub hab)) hRQ hselectedUpper hscaleTen (fun ab hab => hfamilyGap ab (hsub hab))
      hc hlarge32 (fun ab hab => hgap ab (hsub hab))
      (fun ab hab => hsourceColor ab (hsub hab)) (fun ab hab => hlevel ab (hsub hab)) (fun ab hab => hcolor ab (hsub hab)) (fun ab hab => hnear ab (hsub hab)) hsmall hNR hRN hNcube hminscale hMatdet (fun ab hab => hMatt ab (hsub hab)) (fun ab hab => hMatmap ab (hsub hab)) hMatgamma hNtwo (fun ab hab => hL ab (hsub hab)) (fun ab hab => hU ab (hsub hab)) (fun ab hab => hanchor ab (hsub hab)) (fun ab hab => hcut ab (hsub hab)) (fun ab hab => hcount ab (hsub hab))
      hsize hD hΔ hBsize
      (fun ab hab => hBmajor ab (hsub hab))
      (fun ab hab => hCmajor ab (hsub hab)) hblocks
  have hfirst ab (hab : ab∈Gaps) :
      |(Mat 2:ℝ)| ≤ Cfirst*R^4/((Lunit*(n ab:ℝ))^3*N^2)+Csecond*N*R^2/M := by
    have hs : ({ab} : Finset (ℝ × ℝ)) ⊆ Gaps := Finset.singleton_subset_iff.mpr hab
    have hb : ∀ t∈({ab} : Finset (ℝ × ℝ)), m0*n ab ≤ (S t).card := by
      intro t ht
      have he : t=ab := Finset.mem_singleton.mp ht
      subst t
      exact (hn ab hab).2.1
    exact (hfamily {ab} hs (n ab) (hn ab hab).1 hb).1 (Finset.singleton_nonempty ab)
  have hcap ab (hab : ab∈Gaps) :
      (n ab:ℝ)^3*|(Mat 2:ℝ)| ≤ 2*(Cfirst*R^4)/(Lunit^3*N^2) :=
    two_term_first_cubic_cap hCmat.le hN hunit
      (mul_pos hunit (by exact_mod_cast (hn ab hab).1))
      (Nat.cast_nonneg _) le_rfl (hfirst ab hab) habsorb
  let Cost := Cpack*R^4/(Lunit^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ))
  have htail (m : ℕ) (hm : 0 < m) :
      ((Gaps.filter (fun ab => m ≤ n ab)).card:ℝ) ≤ 2+Cost/(m:ℝ)^2 := by
    let Long := Gaps.filter (fun ab => m ≤ n ab)
    have hin : Long ⊆ Gaps := Finset.filter_subset _ _
    have hb ab (hab : ab∈Long) : m0*m ≤ (S ab).card :=
      (Nat.mul_le_mul_left m0 (Finset.mem_filter.mp hab).2).trans (hn ab (hin hab)).2.1
    exact (hfamily Long hin m hm hb).2.trans_eq (by dsimp only [Cost]; ring)
  have hsum := finite_occupied_cubic_tail_sum Gaps n (by norm_num : (0:ℝ) ≤ 2)
    (show 0 ≤ Cost by dsimp only [Cost]; positivity)
    (show 0 ≤ 2*(Cfirst*R^4)/(Lunit^3*N^2) by positivity) hCmat hcap htail
  have hmass : (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤ 2*(m0:ℝ)*(∑ ab∈Gaps, (n ab:ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ab hab
    exact_mod_cast (hn ab hab).2.2
  calc
    _ ≤ 2*(m0:ℝ)*(∑ ab∈Gaps, (n ab:ℝ)) := hmass
    _ ≤ 2*(m0:ℝ)*(2*(2*(Cfirst*R^4)/(Lunit^3*N^2)/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+2*Cost) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by dsimp only [Cost]; ring_nf


                                                                       
                                                                            
theorem physicalModelPhase_actual_fourier_charted_all_reference_sample_mass
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Bmajor Cmajor : ℕ)
    (S : ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℝ × ℝ → ℕ → Fin 2 → ℚ) (vinv : ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : ℝ × ℝ → ℕ → Fin 2 → Fin 2) (anchor : ℝ × ℝ → ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℝ × ℝ → ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T)
    (hM : 0 < M)
    (hN : 0 < N)
    (hR : 1 ≤ R)
    (hRM : R ≤ M)
    (hQ : 0 < Q)
    (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i)
    (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ ab∈Gaps, ∀ j∈(S ab), (x ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hden : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, ((rat ab) j i).den ≤ Q ∧ Q ≤ 2*((rat ab) j i).den)
    (hlambda : 0 < lambda)
    (hUband : 0 ≤ Uband)
    (hθ : 0 < θ)
    (hθmax : θ ≤ 1/24)
    (hcurv : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, lambda ≤ |((rat ab) j i:ℝ)| ∧ |((rat ab) j i:ℝ)| ≤ Uband)
    (hinv : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (((rat ab) j i).den:ℤ) ∣ ((rat ab) j i).num*(vinv ab) j i-1)
    (hchart : ∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1)
    (horientation : ∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2))
    (hBcut : 0 < Bcut)
    (hs : ∀ ab∈Gaps, (s ab) ≠ 0)
    (hrefSet : ∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs)
    (hparentSet : ∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hwideL : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : ∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ))
    (hgapWidth : ∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2))
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ ab∈Gaps, ∀ j∈(S ab), ((rat ab) j 0:ℝ)∈Icc ab.1 ab.2)
    (hc : Mat 2 ≠ 0)
    (hlarge : 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun (ab : ℝ × ℝ) => fun j i => (⌊(((rat ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊(((rat ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ab∈Gaps, ∀ j∈(S ab), (sourceColor ab) j 0=(sourceColor ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, iteratedDeriv 2 (f i) ((x ab) j i)/2=((rat ab) j i:ℝ)) →
    let q := fun (ab : ℝ × ℝ) => fun j i => ((rat ab) j i).den
    let mu := fun (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round ((x ab) j i))/6
    let ell := fun (ab : ℝ × ℝ) => fun j i => deriv (f i) (round ((x ab) j i))
    let b := fun (ab : ℝ × ℝ) => fun j i => (⌊((q ab) j i:ℝ)*(ell ab) j i⌋+((parity ab) j i:ℕ) : ℤ)
    let cround := fun (ab : ℝ × ℝ) => fun j i => round (((q ab) j i:ℝ)*(ell ab) j i)
    let tau := fun (ab : ℝ × ℝ) => fun j i => (((b ab) j i:ℝ)-((q ab) j i:ℝ)*(ell ab) j i)/2
    let dual := fun (ab : ℝ × ℝ) => fun j i => -2*(mu ab) j i*(Real.sqrt (2/(3*(mu ab) j i*((q ab) j i:ℝ))))^3
    let cloud := fun (ab : ℝ × ℝ) => fun j i => (![Int.fract (-((vinv ab) j i:ℝ)*(b ab) j i/(q ab) j i),
      Int.fract (-((vinv ab) j i:ℝ)/(q ab) j i),(dual ab) j i/Real.sqrt K₀,
      (3*(dual ab) j i*(tau ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ab∈Gaps, ∀ j∈(S ab), (b ab) j 0-(cround ab) j 0=(b ab) j 1-(cround ab) j 1) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ a, |(cloud ab) j 0 a-(cloud ab) j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ ab∈Gaps, ∀ j∈(S ab), (Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3=((q ab) j 1:ℝ)/(q ab) j 0) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ((Mat 0:ℝ)*((rat ab) j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3)=((rat ab) j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), |((anchor ab) j:ℝ)-((rat ab) j 0:ℝ)| ≤ ε) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256*(((anchor ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*((anchor ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤
      4*(m0:ℝ)*((2*Cfirst*R^4/(Lunit^3*N^2)/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+
        Cpack*R^4/(Lunit^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ)))+
      (m0:ℝ)*(2+Cgap*R^4/(N^2*|(Mat 2:ℝ)| *(Uref:ℝ))) := by
  classical
  intro Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor Lunit Gamma Cthird Cpack Cfirst Cgap
  let Long := Gaps.filter (fun ab => m0 ≤ (S ab).card)
  let Short := Gaps.filter (fun ab => (S ab).Nonempty ∧ (S ab).card < m0)
  have hinLong : Long ⊆ Gaps := Finset.filter_subset _ _
  have hinShort : Short ⊆ Gaps := Finset.filter_subset _ _
  have hlong := physicalModelPhase_actual_fourier_charted_reference_sample_mass
    Uref Refs Long (Bselect:=Bselect) Bmajor Cmajor S Q K₀ rat vinv parity anchor Mat e r v s
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW (fun ab hab => hx ab (hinLong hab)) (fun ab hab => hwindow ab (hinLong hab)) (fun ab hab => hden ab (hinLong hab)) hlambda hUband hθ hθmax (fun ab hab => hcurv ab (hinLong hab)) (fun ab hab => hinv ab (hinLong hab)) (fun ab hab => hchart ab (hinLong hab)) (fun ab hab => horientation ab (hinLong hab)) hBcut (fun ab hab => hs ab (hinLong hab)) (fun ab hab => hrefSet ab (hinLong hab)) (fun ab hab => hparentSet ab (hinLong hab)) hsep (fun ab hab => hwideL ab (hinLong hab)) (fun ab hab => hwideU ab (hinLong hab)) hUref hBselectSize hcutMargin hselectedWrap (fun ab hab => hreferenceDen ab (hinLong hab)) (fun ab hab => hgapWidth ab (hinLong hab)) hRQ hselectedUpper hscaleTen (fun ab hab => hfamilyGap ab (hinLong hab))
    hc hlarge (fun ab hab => hgap ab (hinLong hab))
    (fun ab hab => hsourceColor ab (hinLong hab)) (fun ab hab => hlevel ab (hinLong hab)) (fun ab hab => hcolor ab (hinLong hab)) (fun ab hab => hnear ab (hinLong hab)) hsmall hNR hRN hNcube hminscale hMatdet (fun ab hab => hMatt ab (hinLong hab)) (fun ab hab => hMatmap ab (hinLong hab)) hMatgamma hNtwo (fun ab hab => hL ab (hinLong hab)) (fun ab hab => hU ab (hinLong hab)) (fun ab hab => hanchor ab (hinLong hab)) (fun ab hab => hcut ab (hinLong hab)) (fun ab hab => hcount ab (hinLong hab))
    hsize hD hΔ hBsize
    (fun ab hab => hBmajor ab (hinLong hab))
    (fun ab hab => hCmajor ab (hinLong hab))
    (fun _ hab => (Finset.mem_filter.mp hab).2)
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hδ0 := approximateModelPhase_tolerance_nonneg (hF 0)
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hlarge32 : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *κ^2*T := by
    have hn := mul_nonneg hC₃ (sq_nonneg M)
    nlinarith only [hlarge,hn]
  have hUp : (0:ℝ) < Uref := by exact_mod_cast (show 0 < Uref by omega)
  have hF₃ i := approximateModelPhase_mono (hF i) (by norm_num : 3 ≤ 4) le_rfl
  have hNscale : N^2 ≤ M*R^2 := by
    have hm := mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ N by linarith only [hNtwo])
      (sq_nonneg N)
    nlinarith only [hm,hNcube]
  have hchoose ab (hab : ab∈Short) : ∃ j, j∈S ab :=
    (Finset.mem_filter.mp hab).2.1
  choose! j hj using hchoose
  have hshortcount :
      (Short.card:ℝ) ≤ 2+Cgap*R^4/(N^2*|(Mat 2:ℝ)| *(Uref:ℝ)) := by
    exact physicalModelPhase_actual_fourier_large_entry_closed_reference_gap_count
      Refs Short Mat Q K₀ (fun ab => rat ab (j ab)) (fun ab => vinv ab (j ab))
      (fun ab => parity ab (j ab)) (fun ab => x ab (j ab))
      hσ hδ hF₃ hT hM hN (zero_lt_one.trans_le hR) hUp hQ hscale hmesh hNscale
      hA hW hMatdet hc hlarge32
      (by
        intro a ha b hb hne
        calc
          (Uref:ℝ)/(4*R^2)=((Uref:ℝ)/R^2)/4 := by ring
          _ ≤ |a-b| := (hsep a ha b hb hne).le)
      (fun ab hab => hgap ab (hinShort hab))
      (fun ab hab => hx ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hden ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hinv ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hlevel ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hcolor ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hnear ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hMatt ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hMatmap ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hfamilyGap ab (hinShort hab) _ (hj ab hab))
  have hshortmass : (∑ ab∈Short, ((S ab).card:ℝ)) ≤
      (m0:ℝ)*(2+Cgap*R^4/(N^2*|(Mat 2:ℝ)| *(Uref:ℝ))) := by
    calc
      _ ≤ ∑ _ab∈Short, (m0:ℝ) := by
        apply Finset.sum_le_sum
        intro ab hab
        exact_mod_cast (Finset.mem_filter.mp hab).2.2.le
      _ = (m0:ℝ)*(Short.card:ℝ) := by simp [mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left hshortcount (Nat.cast_nonneg _)
  have hpartition : (∑ ab∈Gaps, ((S ab).card:ℝ)) =
      (∑ ab∈Long, ((S ab).card:ℝ))+(∑ ab∈Short, ((S ab).card:ℝ)) := by
    simp only [Long,Short,Finset.sum_filter,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ab _
    by_cases hh : m0 ≤ (S ab).card
    · simp [hh,not_lt.mpr hh]
    · have hlt : (S ab).card < m0 := lt_of_not_ge hh
      by_cases he : (S ab).Nonempty
      · simp [hh,he,hlt]
      · have hz : (S ab).card=0 := by simp [Finset.not_nonempty_iff_eq_empty.mp he]
        simp [he,hz]
  rw [hpartition]
  exact add_le_add hlong hshortmass

                                                                       
                                                              
theorem fourier_matrix_narrowed_coordinate_entry_bound
    (q e vinv : Fin 2 → ℤ) (A : Fin 4 → ℤ) {Q K V N R : ℝ}
    (hq : ∀ i, 0 < q i) (hK : 1 ≤ K) (hV : 1 ≤ V)
    (hN : 0 < N)
    (hmesh : Q*N ≤ K*R^2)
    (hband : ∀ i, (q i:ℝ) ≤ Q ∧ Q ≤ 2*q i)
    (hinv : ∀ i, q i ∣ e i*vinv i-1)
    (hdet : A 0*A 3-A 1*A 2=1)
    (ht : (A 2:ℝ)*((e 0:ℝ)/q 0)+A 3=(q 1:ℝ)/q 0)
    (hmap : ((A 0:ℝ)*((e 0:ℝ)/q 0)+A 1)/
      ((A 2:ℝ)*((e 0:ℝ)/q 0)+A 3)=(e 1:ℝ)/q 1)
    (hgamma : |(A 2:ℝ)| ≤ Q^2/(6*K^2))
    (hnear : |Int.fract (-(vinv 0:ℝ)/q 0)-
      Int.fract (-(vinv 1:ℝ)/q 1)| ≤ 1/(6*K^2*V)) :
    |(A 2:ℝ)| ≤ Q^2/(6*K^2*V) ∧ |(A 2:ℝ)| ≤ R^4/(6*N^2*V) := by
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hVp : 0 < V := zero_lt_one.trans_le hV
  have hqr i : (0:ℝ) < q i := by exact_mod_cast hq i
  have hQp : 0 < Q := (hqr 0).trans_le (hband 0).1
  have hnear₀ : |Int.fract (-(vinv 0:ℝ)/q 0)-
      Int.fract (-(vinv 1:ℝ)/q 1)| ≤ 1/(6*K^2) := by
    apply hnear.trans
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith only [mul_le_mul_of_nonneg_left hV (show 0 ≤ 6*K^2 by positivity)]
  obtain ⟨v,hv,hs,htransport⟩ := fourier_matrix_normalized_chart_transport
    q e vinv A (Q:=Q) (K:=K) hq hK hband hinv hdet ht hmap hgamma hnear₀
  let s := fun i => -vinv i-q i*⌊-(vinv i:ℝ)/q i⌋
  have hc : A 2=q 0*s 1-s 0*q 1 := by
    have hden := (htransport 1 0).2
    have hcomp := (htransport 0 1).2
    simp only [mul_one,mul_zero,add_zero,zero_add] at hden hcomp
    change A 2*v 0+A 3*s 0=s 1 at hcomp
    linear_combination -(A 2)*(hv 0)+(q 0)*hcomp-(s 0)*hden
  have hcR : (A 2:ℝ)=(q 0:ℝ)*s 1-(s 0:ℝ)*q 1 := by exact_mod_cast hc
  have hp : 0 < (q 0:ℝ)*q 1 := mul_pos (hqr 0) (hqr 1)
  have hentry : |(A 2:ℝ)| ≤ Q^2/(6*K^2*V) := by
    calc
      _ = |(s 1:ℝ)/q 1-(s 0:ℝ)/q 0| *((q 0:ℝ)*q 1) := by
        rw [←abs_of_pos hp,←abs_mul,hcR]
        congr 1
        field_simp [(hqr 0).ne',(hqr 1).ne']
      _ ≤ (1/(6*K^2*V))*((q 0:ℝ)*q 1) := by
        apply mul_le_mul_of_nonneg_right _ hp.le
        rw [hs 0,hs 1,abs_sub_comm]
        exact hnear
      _ ≤ (1/(6*K^2*V))*Q^2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith only [mul_le_mul (hband 0).1 (hband 1).1 (hqr 1).le hQp.le]
      _ = _ := by ring
  refine ⟨hentry,hentry.trans ?_⟩
  apply (div_le_div_iff₀ (by positivity : 0 < 6*K^2*V)
    (by positivity : 0 < 6*N^2*V)).mpr
  have hsq := pow_le_pow_left₀ (mul_pos hQp hN).le hmesh 2
  have hm := mul_le_mul_of_nonneg_right hsq (show 0 ≤ 6*V by positivity)
  nlinarith only [hm]


private theorem mobius_upper_right_large_action_comparison
    {a b c d x y lambda H : ℝ}
    (hlambda : 0 ≤ lambda)
    (hdet : a*d-b*c=1) (htl : (1:ℝ)/2 ≤ c*x+d) (htu : c*x+d ≤ 2)
    (hmap : (a*x+b)/(c*x+d)=y)
    (hx : lambda ≤ |x| ∧ |x| ≤ H) (hy : lambda ≤ |y| ∧ |y| ≤ H)
    (hlarge : 8*H ≤ |c| *lambda^2) :
    |c| *lambda^2/2 ≤ |b| ∧ |b| ≤ (3/2)*|c| *H^2 := by
  let t := c*x+d
  have ht : 0 < t := by dsimp only [t]; linarith only [htl]
  have hH : 0 ≤ H := (abs_nonneg x).trans hx.2
  have he := (div_eq_iff ht.ne').mp hmap
  have ha : a=c*y+1/t := by
    have hid : (a-c*y)*t=1 := by
      dsimp only [t]
      nlinarith only [hdet,congrArg (fun z : ℝ => c*z) he]
    have hh : a-c*y=1/t := (eq_div_iff ht.ne').mpr hid
    linarith only [hh]
  have herrorId : b+c*x*y=t*y-x/t := by
    rw [ha] at he
    change (c*y+1/t)*x+b=y*t at he
    linear_combination he
  have htInv : 1/t ≤ 2 := by
    apply (div_le_iff₀ ht).mpr
    change (1:ℝ)/2 ≤ t at htl
    linarith only [htl]
  have herror : |b+c*x*y| ≤ 4*H := by
    rw [herrorId]
    calc
      _ ≤ |t*y|+|x/t| := abs_sub _ _
      _ = t*|y|+(1/t)*|x| := by
        rw [abs_mul,abs_div,abs_of_pos ht]
        ring
      _ ≤ 2*H+2*H := add_le_add
        (mul_le_mul htu hy.2 (abs_nonneg y) (by norm_num))
        (mul_le_mul htInv hx.2 (abs_nonneg x) (by norm_num))
      _ = _ := by ring
  have hprod : |c*x*y|=|c| *|x| *|y| := by rw [abs_mul,abs_mul]
  have hlo : |c| *lambda^2 ≤ |c*x*y| := by
    rw [hprod]
    have hh := mul_le_mul hx.1 hy.1 hlambda (abs_nonneg x)
    nlinarith only [mul_le_mul_of_nonneg_left hh (abs_nonneg c)]
  have hhi : |c*x*y| ≤ |c| *H^2 := by
    rw [hprod]
    have hh := mul_le_mul hx.2 hy.2 (abs_nonneg y) hH
    nlinarith only [mul_le_mul_of_nonneg_left hh (abs_nonneg c)]
  have hlowTri : |c*x*y| ≤ |b+c*x*y|+|b| := by
    calc
      _ = |(b+c*x*y)-b| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
  have hhighTri : |b| ≤ |b+c*x*y|+|c*x*y| := by
    calc
      _ = |(b+c*x*y)-(c*x*y)| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
  constructor
  · nlinarith only [hlo,hlowTri,herror,hlarge]
  · nlinarith only [hlo,hhi,hhighTri,herror,hlarge]

private theorem mobius_reciprocal_entry_bounds
    {a b c d x y lambda : ℝ}
    (hlambda : 0 < lambda)
    (hdet : a*d-b*c=1) (ht : c*x+d ≠ 0)
    (hmap : (a*x+b)/(c*x+d)=y)
    (hx : lambda ≤ |x|) (hy : lambda ≤ |y|)
    (hnumlo : (1:ℝ)/2 ≤ (a*x+b)/x)
    (hnumhi : (a*x+b)/x ≤ 2) :
    |a| ≤ |b|/lambda+2 ∧ |d| ≤ |b|/lambda+2 := by
  have hx0 : x ≠ 0 := abs_pos.mp (hlambda.trans_le hx)
  have hy0 : y ≠ 0 := abs_pos.mp (hlambda.trans_le hy)
  have he := (div_eq_iff ht).mp hmap
  have hden : b*(1/x)+a=(a*x+b)/x := by
    field_simp [hx0]
    ring
  have hdenp : 0 < b*(1/x)+a := by rw [hden]; linarith only [hnumlo]
  have hrmap : (d*(1/x)+c)/(b*(1/x)+a)=1/y := by
    apply (div_eq_iff hdenp.ne').mpr
    field_simp [hx0,hy0]
    nlinarith only [he]
  have hrx : |1/x| ≤ 1/lambda := by
    rw [abs_div,abs_one]
    exact one_div_le_one_div_of_le hlambda hx
  have hry : |1/y| ≤ 1/lambda := by
    rw [abs_div,abs_one]
    exact one_div_le_one_div_of_le hlambda hy
  have hh := bourgain_mobius_entry_bounds
    (a:=d) (b:=c) (c:=b) (d:=a) (x:=1/x) (y:=1/y)
    (by nlinarith only [hdet]) (by rw [hden]; exact hnumlo)
    (by rw [hden]; exact hnumhi) hrmap hrx hry
  constructor
  · simpa only [mul_one_div] using hh.2
  · simpa only [mul_one_div] using hh.1

private theorem cubic_reciprocal_majorant {K c Gamma : ℝ}
    (hK : 0 ≤ K) (hc : 0 < c) (hcap : c ≤ Gamma) :
    (K/c)^((3:ℝ)⁻¹) ≤ K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)/c := by
  apply (le_div_iff₀ hc).mpr
  calc
    _ = K^((3:ℝ)⁻¹)*c^(1-(3:ℝ)⁻¹) := by
      rw [Real.div_rpow hK hc.le,Real.rpow_sub hc,Real.rpow_one]
      ring
    _ ≤ K^((3:ℝ)⁻¹)*Gamma^(1-(3:ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hc.le hcap (by norm_num))
        (Real.rpow_nonneg hK _)
    _ = _ := by norm_num

private theorem resonance_matrix_cubic_weight_sum
    (S : Finset (Fin 4 → ℤ)) {Vbound Gamma A K B : ℝ}
    (hV : 0 ≤ Vbound) (hGamma : 0 ≤ Gamma)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hdet : ∀ Mat∈S, Mat 0*Mat 3-Mat 1*Mat 2=1)
    (hc : ∀ Mat∈S, Mat 2 ≠ 0 ∧ |(Mat 2:ℝ)| ≤ Gamma)
    (ha : ∀ Mat∈S, |(Mat 0:ℝ)| ≤ |(Mat 2:ℝ)| *Vbound+2)
    (hd : ∀ Mat∈S, |(Mat 3:ℝ)| ≤ |(Mat 2:ℝ)| *Vbound+2) :
    ∑ Mat∈S,(A*(K/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+B/|(Mat 2:ℝ)|) ≤
      ((2*Gamma+1)*(2*Vbound+5)^2)*(A*K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)+B) := by
  have hw := resonance_matrix_reciprocal_sum S hV hGamma hdet hc ha hd
  have hp Mat (hMat : Mat∈S) : 0 < |(Mat 2:ℝ)| :=
    abs_pos.mpr (by exact_mod_cast (hc Mat hMat).1)
  let C := A*K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)+B
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg (mul_nonneg (mul_nonneg hA (Real.rpow_nonneg hK _))
      (Real.rpow_nonneg hGamma _)) hB
  calc
    _ ≤ ∑ Mat∈S,C*(1/|(Mat 2:ℝ)|) := by
      apply Finset.sum_le_sum
      intro Mat hMat
      have hh := mul_le_mul_of_nonneg_left
        (cubic_reciprocal_majorant hK (hp Mat hMat) (hc Mat hMat).2) hA
      dsimp only [C]
      calc
        _ ≤ A*(K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)/|(Mat 2:ℝ)|)+B/|(Mat 2:ℝ)| :=
          add_le_add hh le_rfl
        _ = _ := by ring
    _ = C*(∑ Mat∈S,1/|(Mat 2:ℝ)|) := (Finset.mul_sum S _ _).symm
    _ ≤ C*((2*Gamma+1)*(2*Vbound+5)^2) := mul_le_mul_of_nonneg_left hw hC
    _ = _ := by dsimp only [C]; ring

private theorem resonance_matrix_reciprocal_cubic_weight_sum
    (S : Finset (Fin 4 → ℤ)) {X Gamma Theta A K B : ℝ}
    (hX : 0 ≤ X) (hGamma : 0 ≤ Gamma) (hTheta : 0 ≤ Theta)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hdet : ∀ Mat∈S, Mat 0*Mat 3-Mat 1*Mat 2=1)
    (hc : ∀ Mat∈S, Mat 2 ≠ 0)
    (hb : ∀ Mat∈S, Mat 1 ≠ 0 ∧ |(Mat 1:ℝ)| ≤ Gamma)
    (hcompare : ∀ Mat∈S, |(Mat 1:ℝ)| ≤ Theta*|(Mat 2:ℝ)|)
    (ha : ∀ Mat∈S, |(Mat 0:ℝ)| ≤ |(Mat 1:ℝ)| *X+2)
    (hd : ∀ Mat∈S, |(Mat 3:ℝ)| ≤ |(Mat 1:ℝ)| *X+2) :
    ∑ Mat∈S,(A*(K/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+B/|(Mat 2:ℝ)|) ≤
      ((2*Gamma+1)*(2*X+5)^2)*
        (A*(Theta*K)^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)+Theta*B) := by
  classical
  let flip := fun Mat : Fin 4 → ℤ => (![Mat 3,Mat 2,Mat 1,Mat 0] : Fin 4 → ℤ)
  have hflip Mat : flip (flip Mat)=Mat := by
    funext i
    fin_cases i <;> rfl
  have hinj : Function.Injective flip := by
    intro Mat Mat' he
    have hh := congrArg flip he
    rw [hflip,hflip] at hh
    exact hh
  have hw := resonance_matrix_cubic_weight_sum (S.image flip)
    hX hGamma hA (mul_nonneg hTheta hK) (mul_nonneg hTheta hB)
    (by
      intro W hW
      obtain ⟨Mat,hMat,rfl⟩ := Finset.mem_image.mp hW
      change Mat 3*Mat 0-Mat 2*Mat 1=1
      nlinarith only [hdet Mat hMat])
    (by
      intro W hW
      obtain ⟨Mat,hMat,rfl⟩ := Finset.mem_image.mp hW
      exact hb Mat hMat)
    (by
      intro W hW
      obtain ⟨Mat,hMat,rfl⟩ := Finset.mem_image.mp hW
      exact hd Mat hMat)
    (by
      intro W hW
      obtain ⟨Mat,hMat,rfl⟩ := Finset.mem_image.mp hW
      exact ha Mat hMat)
  rw [Finset.sum_image hinj.injOn] at hw
  apply le_trans _ hw
  apply Finset.sum_le_sum
  intro Mat hMat
  have hcp : 0 < |(Mat 2:ℝ)| := abs_pos.mpr (by exact_mod_cast hc Mat hMat)
  have hbp : 0 < |(Mat 1:ℝ)| := abs_pos.mpr (by exact_mod_cast (hb Mat hMat).1)
  have hKbound : K/|(Mat 2:ℝ)| ≤ (Theta*K)/|(Mat 1:ℝ)| := by
    apply (div_le_div_iff₀ hcp hbp).mpr
    nlinarith only [mul_le_mul_of_nonneg_left (hcompare Mat hMat) hK]
  have hBbound : B/|(Mat 2:ℝ)| ≤ (Theta*B)/|(Mat 1:ℝ)| := by
    apply (div_le_div_iff₀ hcp hbp).mpr
    nlinarith only [mul_le_mul_of_nonneg_left (hcompare Mat hMat) hB]
  exact add_le_add (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (div_nonneg hK hcp.le) hKbound (by norm_num)) hA) hBbound

private theorem resonance_matrix_curvature_band_cubic_weight_sum
    (S : Finset (Fin 4 → ℤ)) (x y : (Fin 4 → ℤ) → ℝ)
    {lambda H Gamma A K B : ℝ}
    (hlambda : 0 < lambda) (hGamma : 0 ≤ Gamma)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hdet : ∀ Mat∈S, Mat 0*Mat 3-Mat 1*Mat 2=1)
    (hc : ∀ Mat∈S, Mat 2 ≠ 0 ∧ |(Mat 2:ℝ)| ≤ Gamma)
    (hx : ∀ Mat∈S, lambda ≤ |x Mat| ∧ |x Mat| ≤ H)
    (hy : ∀ Mat∈S, lambda ≤ |y Mat| ∧ |y Mat| ≤ H)
    (ht : ∀ Mat∈S, (1:ℝ)/2 ≤ (Mat 2:ℝ)*x Mat+Mat 3 ∧
      (Mat 2:ℝ)*x Mat+Mat 3 ≤ 2)
    (hmap : ∀ Mat∈S, ((Mat 0:ℝ)*x Mat+Mat 1)/
      ((Mat 2:ℝ)*x Mat+Mat 3)=y Mat)
    (hnum : ∀ Mat∈S, (1:ℝ)/2 ≤ ((Mat 0:ℝ)*x Mat+Mat 1)/x Mat ∧
      ((Mat 0:ℝ)*x Mat+Mat 1)/x Mat ≤ 2)
    (hlarge : ∀ Mat∈S, 8*H ≤ |(Mat 2:ℝ)| *lambda^2) :
    ∑ Mat∈S,(A*(K/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+B/|(Mat 2:ℝ)|) ≤
      588*(H/lambda)^2*H^2*Gamma*
        (A*K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)+B) := by
  classical
  let E := A*K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)+B
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hFactor {g v : ℝ} (hg : 1 ≤ g) (hv : 1 ≤ v) :
      (2*g+1)*(2*v+5)^2 ≤ 147*g*v^2 := by
    have hg0 : 0 ≤ g := zero_le_one.trans hg
    have hv0 : 0 ≤ v := zero_le_one.trans hv
    have hgl : 2*g+1 ≤ 3*g := by linarith only [hg]
    have hvl : 2*v+5 ≤ 7*v := by linarith only [hv]
    have hvp := pow_le_pow_left₀ (by positivity : 0 ≤ 2*v+5) hvl 2
    have hh := mul_le_mul hgl hvp (sq_nonneg _) (by positivity : 0 ≤ 3*g)
    nlinarith only [hh]
  by_cases hS : S.Nonempty
  · obtain ⟨Mat₀,hMat₀⟩ := hS
    have hLH : lambda ≤ H := (hx Mat₀ hMat₀).1.trans (hx Mat₀ hMat₀).2
    have hH : 0 < H := hlambda.trans_le hLH
    have hGammaOne : 1 ≤ Gamma :=
      (show (1:ℝ) ≤ |(Mat₀ 2:ℝ)| by exact_mod_cast Int.one_le_abs (hc Mat₀ hMat₀).1).trans
        (hc Mat₀ hMat₀).2
    have hcp Mat (hMat : Mat∈S) : 0 < |(Mat 2:ℝ)| :=
      abs_pos.mpr (by exact_mod_cast (hc Mat hMat).1)
    have hdetR Mat (hMat : Mat∈S) :
        (Mat 0:ℝ)*Mat 3-(Mat 1:ℝ)*Mat 2=1 := by exact_mod_cast hdet Mat hMat
    by_cases hWide : 1 ≤ H
    · have hentries Mat (hMat : Mat∈S) :=
        bourgain_mobius_entry_bounds (hdetR Mat hMat) (ht Mat hMat).1 (ht Mat hMat).2
          (hmap Mat hMat) (hx Mat hMat).2 (hy Mat hMat).2
      have hw := resonance_matrix_cubic_weight_sum S hH.le hGamma hA hK hB hdet hc
        (fun Mat hMat => (hentries Mat hMat).1) (fun Mat hMat => (hentries Mat hMat).2)
      have hratio : 1 ≤ H/lambda := (le_div_iff₀ hlambda).mpr (by simpa using hLH)
      have hsquare : 1 ≤ (H/lambda)^2 := by nlinarith only [hratio,sq_nonneg (H/lambda-1)]
      have hscale := mul_le_mul_of_nonneg_right hsquare (sq_nonneg H)
      have hmul := mul_le_mul_of_nonneg_left hscale (show 0 ≤ 147*Gamma by positivity)
      have hpos : 0 ≤ (H/lambda)^2*H^2*Gamma := by positivity
      have hfac : 147*Gamma*H^2 ≤ 588*(H/lambda)^2*H^2*Gamma := by
        nlinarith only [hmul,hpos]
      exact hw.trans ((mul_le_mul_of_nonneg_right (hFactor hGammaOne hWide) hE).trans
        (mul_le_mul_of_nonneg_right hfac hE))
    · let Theta := 2*H^2
      let G := Theta*Gamma
      have hTheta : 0 < Theta := by dsimp only [Theta]; positivity
      have hG : 0 ≤ G := mul_nonneg hTheta.le hGamma
      have hcompare Mat (hMat : Mat∈S) : |(Mat 1:ℝ)| ≤ Theta*|(Mat 2:ℝ)| := by
        have hh := mobius_upper_right_large_action_comparison hlambda.le
          (hdetR Mat hMat) (ht Mat hMat).1 (ht Mat hMat).2 (hmap Mat hMat)
          (hx Mat hMat) (hy Mat hMat) (hlarge Mat hMat)
        have hp := mul_nonneg (abs_nonneg (Mat 2:ℝ)) (sq_nonneg H)
        dsimp only [Theta]
        nlinarith only [hh.2,hp]
      have hb Mat (hMat : Mat∈S) : Mat 1 ≠ 0 ∧ |(Mat 1:ℝ)| ≤ G := by
        have hh := mobius_upper_right_large_action_comparison hlambda.le
          (hdetR Mat hMat) (ht Mat hMat).1 (ht Mat hMat).2 (hmap Mat hMat)
          (hx Mat hMat) (hy Mat hMat) (hlarge Mat hMat)
        have hcpos := hcp Mat hMat
        have hp : 0 < |(Mat 1:ℝ)| :=
          (show 0 < |(Mat 2:ℝ)| *lambda^2/2 by positivity).trans_le hh.1
        refine ⟨?_,(hcompare Mat hMat).trans
          (mul_le_mul_of_nonneg_left (hc Mat hMat).2 hTheta.le)⟩
        exact_mod_cast abs_pos.mp hp
      have hentries Mat (hMat : Mat∈S) :=
        mobius_reciprocal_entry_bounds hlambda (hdetR Mat hMat)
          (show (Mat 2:ℝ)*x Mat+Mat 3 ≠ 0 by linarith only [(ht Mat hMat).1])
          (hmap Mat hMat) (hx Mat hMat).1 (hy Mat hMat).1
          (hnum Mat hMat).1 (hnum Mat hMat).2
      have hw := resonance_matrix_reciprocal_cubic_weight_sum S
        (show 0 ≤ 1/lambda by positivity) hG hTheta.le hA hK hB hdet
        (fun Mat hMat => (hc Mat hMat).1) hb hcompare
        (fun Mat hMat => by simpa only [mul_one_div] using (hentries Mat hMat).1)
        (fun Mat hMat => by simpa only [mul_one_div] using (hentries Mat hMat).2)
      have hGOne : 1 ≤ G :=
        (show (1:ℝ) ≤ |(Mat₀ 1:ℝ)| by exact_mod_cast Int.one_le_abs (hb Mat₀ hMat₀).1).trans
          (hb Mat₀ hMat₀).2
      have hInv : 1 ≤ 1/lambda := (le_div_iff₀ hlambda).mpr
        (by linarith only [hLH,le_of_not_ge hWide])
      have hpow : Theta^((3:ℝ)⁻¹)*Theta^((2:ℝ)/3)=Theta := by
        rw [←Real.rpow_add hTheta]
        norm_num
      have he : A*(Theta*K)^((3:ℝ)⁻¹)*G^((2:ℝ)/3)+Theta*B=Theta*E := by
        dsimp only [G,E]
        rw [Real.mul_rpow hTheta.le hK,Real.mul_rpow hTheta.le hGamma]
        calc
          _ = (Theta^((3:ℝ)⁻¹)*Theta^((2:ℝ)/3))*
              (A*K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3))+Theta*B := by ring
          _ = _ := by rw [hpow]; ring
      rw [he] at hw
      calc
        _ ≤ ((2*G+1)*(2*(1/lambda)+5)^2)*(Theta*E) := hw
        _ ≤ (147*G*(1/lambda)^2)*(Theta*E) :=
          mul_le_mul_of_nonneg_right (hFactor hGOne hInv) (mul_nonneg hTheta.le hE)
        _ = _ := by dsimp only [Theta,G,E]; ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS,Finset.sum_empty]
    change 0 ≤ 588*(H/lambda)^2*H^2*Gamma*E
    positivity

private theorem matrix_sample_mass_weight_majorant
    {mass m K P G R L N U C Gamma : ℝ}
    (hm : 0 ≤ m) (hC : 0 < C) (hcap : C ≤ Gamma)
    (hmass : mass ≤ 4*m*((K/C)^((3:ℝ)⁻¹)+P*R^4/(L^2*N^2*C*U))+
      m*(2+G*R^4/(N^2*C*U))) :
    mass ≤ 4*m*(K/C)^((3:ℝ)⁻¹)+
      (4*m*P*R^4/(L^2*N^2*U)+m*G*R^4/(N^2*U)+2*m*Gamma)/C := by
  have hconstant : 2*m ≤ 2*m*Gamma/C :=
    (le_div_iff₀ hC).mpr (mul_le_mul_of_nonneg_left hcap (mul_nonneg (by norm_num) hm))
  calc
    _ ≤ 4*m*((K/C)^((3:ℝ)⁻¹)+P*R^4/(L^2*N^2*C*U))+
        m*(2+G*R^4/(N^2*C*U)) := hmass
    _ = 4*m*(K/C)^((3:ℝ)⁻¹)+
        (4*m*P*R^4/(L^2*N^2*U)+m*G*R^4/(N^2*U))/C+2*m := by ring
    _ ≤ 4*m*(K/C)^((3:ℝ)⁻¹)+
        (4*m*P*R^4/(L^2*N^2*U)+m*G*R^4/(N^2*U))/C+2*m*Gamma/C :=
      add_le_add le_rfl hconstant
    _ = _ := by ring

private theorem cubic_matrix_source_scale
    {Z k b m U V G : ℝ}
    (hZ : 0 < Z) (hk : 0 ≤ k) (hb : 0 ≤ b) (hm : 0 ≤ m)
    (hU : 0 < U) (hV : 1 ≤ V) (hG : 0 ≤ G) (hcap : G ≤ Z/V) :
    G*(4*m*(k*Z)^((3:ℝ)⁻¹)*G^((2:ℝ)/3)+m*b*Z/U+2*m*G) ≤
      m*Z^2*((4*k^((3:ℝ)⁻¹)+2)/V^((5:ℝ)/3)+b/(U*V)) := by
  have hVp : 0 < V := zero_lt_one.trans_le hV
  have hratio : 0 ≤ Z/V := (div_pos hZ hVp).le
  have hcoeff : 0 ≤ 4*m*(k*Z)^((3:ℝ)⁻¹) := by positivity
  have hinner :
      4*m*(k*Z)^((3:ℝ)⁻¹)*G^((2:ℝ)/3)+m*b*Z/U+2*m*G ≤
      4*m*(k*Z)^((3:ℝ)⁻¹)*(Z/V)^((2:ℝ)/3)+m*b*Z/U+2*m*(Z/V) := by
    exact add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hG hcap (by norm_num)) hcoeff) le_rfl)
      (mul_le_mul_of_nonneg_left hcap (by positivity))
  have hproduct : (k*Z)^((3:ℝ)⁻¹)*(Z/V)^((2:ℝ)/3)=
      k^((3:ℝ)⁻¹)*Z/V^((2:ℝ)/3) := by
    rw [Real.mul_rpow hk hZ.le,Real.div_rpow hZ.le hVp.le]
    have hpow : Z^((3:ℝ)⁻¹)*Z^((2:ℝ)/3)=Z := by
      rw [←Real.rpow_add hZ]
      norm_num
    calc
      _ = k^((3:ℝ)⁻¹)*(Z^((3:ℝ)⁻¹)*Z^((2:ℝ)/3))/V^((2:ℝ)/3) := by ring
      _ = _ := by rw [hpow]
  have hVpow : V*V^((2:ℝ)/3)=V^((5:ℝ)/3) := by
    calc
      _ = V^(1:ℝ)*V^((2:ℝ)/3) := by rw [Real.rpow_one]
      _ = V^((1:ℝ)+2/3) := (Real.rpow_add hVp _ _).symm
      _ = _ := by norm_num
  have hsquare : V^((5:ℝ)/3) ≤ V^2 := by
    have hh := Real.rpow_le_rpow_of_exponent_le hV (by norm_num : (5:ℝ)/3 ≤ 2)
    simpa only [Real.rpow_two] using hh
  have htail : 2/V^2 ≤ 2/V^((5:ℝ)/3) :=
    div_le_div_of_nonneg_left (by norm_num) (Real.rpow_pos_of_pos hVp _) hsquare
  calc
    _ ≤ (Z/V)*(4*m*(k*Z)^((3:ℝ)⁻¹)*(Z/V)^((2:ℝ)/3)+m*b*Z/U+2*m*(Z/V)) :=
      mul_le_mul hcap hinner (by positivity) hratio
    _ = m*Z^2*(4*k^((3:ℝ)⁻¹)/V^((5:ℝ)/3)+b/(U*V)+2/V^2) := by
      have he : 4*m*(k*Z)^((3:ℝ)⁻¹)*(Z/V)^((2:ℝ)/3)=
          4*m*(k^((3:ℝ)⁻¹)*Z/V^((2:ℝ)/3)) := by rw [←hproduct]; ring
      rw [he,←hVpow]
      ring
    _ ≤ m*Z^2*(4*k^((3:ℝ)⁻¹)/V^((5:ℝ)/3)+b/(U*V)+2/V^((5:ℝ)/3)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl htail) (by positivity)
    _ = _ := by ring

private theorem matrix_physical_source_scale
    {R N L U V Cfirst Cpack Cgap m H lambda : ℝ}
    (hR : 0 < R) (hN : 0 < N) (hL : 0 < L) (hU : 0 < U) (hV : 1 ≤ V)
    (hCf : 0 ≤ Cfirst) (hCp : 0 ≤ Cpack) (hCg : 0 ≤ Cgap) (hm : 0 ≤ m) :
    let G := R^4/(6*N^2*V)
    let K := 2*Cfirst*R^4/(L^3*N^2)
    let B := 4*m*Cpack*R^4/(L^2*N^2*U)+m*Cgap*R^4/(N^2*U)+2*m*G
    588*(H/lambda)^2*H^2*G*(4*m*K^((3:ℝ)⁻¹)*G^((2:ℝ)/3)+B) ≤
      588*m*(H/lambda)^2*H^2*(R^8/N^4)*
        ((4*(2*Cfirst/L^3)^((3:ℝ)⁻¹)+2)/V^((5:ℝ)/3)+
          (4*Cpack/L^2+Cgap)/(U*V)) := by
  intro G K B
  let Z := R^4/N^2
  let k := 2*Cfirst/L^3
  let b := 4*Cpack/L^2+Cgap
  have hVp : 0 < V := zero_lt_one.trans_le hV
  have hZ : 0 < Z := by dsimp only [Z]; positivity
  have hk : 0 ≤ k := by dsimp only [k]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hcap : G ≤ Z/V := by
    calc
      G = Z/(6*V) := by dsimp only [G,Z]; ring
      _ ≤ Z/V := div_le_div_of_nonneg_left hZ.le hVp (by linarith only [hVp])
  have hh := cubic_matrix_source_scale hZ hk hb hm hU hV hG hcap
  have hK : K=k*Z := by dsimp only [K,k,Z]; ring
  have hB : B=m*b*Z/U+2*m*G := by dsimp only [B,b,Z]; ring
  have hZsquare : Z^2=R^8/N^4 := by dsimp only [Z]; ring
  have hs := mul_le_mul_of_nonneg_left hh
    (show 0 ≤ 588*(H/lambda)^2*H^2 by positivity)
  rw [hK,hB]
  convert hs using 1
  · ring
  · rw [hZsquare]
    dsimp only [k,b]
    ring

private theorem physicalModelPhase_actual_fourier_charted_matrix_source_mass_core
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Matrices : Finset (Fin 4 → ℤ)) (Bmajor Cmajor : ℕ)
    (S : (Fin 4 → ℤ) → ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → Fin 2 → ℚ)
    (vinv : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → Fin 2 → Fin 2)
    (anchor : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ V : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T)
    (hM : 0 < M)
    (hN : 0 < N)
    (hR : 1 ≤ R)
    (hRM : R ≤ M)
    (hQ : 0 < Q)
    (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i)
    (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((x Mat) ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hden : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, (((rat Mat) ab) j i).den ≤ Q ∧ Q ≤ 2*(((rat Mat) ab) j i).den)
    (hlambda : 0 < lambda)
    (hUband : 0 ≤ Uband)
    (hθ : 0 < θ)
    (hθmax : θ ≤ 1/24)
    (hcurv : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, lambda ≤ |(((rat Mat) ab) j i:ℝ)| ∧ |(((rat Mat) ab) j i:ℝ)| ≤ Uband)
    (hinv : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((((rat Mat) ab) j i).den:ℤ) ∣ (((rat Mat) ab) j i).num*((vinv Mat) ab) j i-1)
    (hchart : ∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1)
    (horientation : ∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2))
    (hBcut : 0 < Bcut)
    (hs : ∀ ab∈Gaps, (s ab) ≠ 0)
    (hrefSet : ∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs)
    (hparentSet : ∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hwideL : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : ∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ))
    (hgapWidth : ∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2))
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), (((rat Mat) ab) j 0:ℝ)∈Icc ab.1 ab.2)
    (hc : ∀ Mat∈Matrices, Mat 2 ≠ 0)
    (hlarge : ∀ Mat∈Matrices, 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (haction : ∀ Mat∈Matrices, 8*Uband ≤ |(Mat 2:ℝ)| *lambda^2)
    (hV : 1 ≤ V)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (⌊((((rat Mat) ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((((rat Mat) ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((sourceColor Mat) ab) j 0=((sourceColor Mat) ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, iteratedDeriv 2 (f i) (((x Mat) ab) j i)/2=(((rat Mat) ab) j i:ℝ)) →
    let q := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (((rat Mat) ab) j i).den
    let mu := fun Mat => fun (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round (((x Mat) ab) j i))/6
    let ell := fun Mat => fun (ab : ℝ × ℝ) => fun j i => deriv (f i) (round (((x Mat) ab) j i))
    let b := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (⌊(((q Mat) ab) j i:ℝ)*((ell Mat) ab) j i⌋+(((parity Mat) ab) j i:ℕ) : ℤ)
    let cround := fun Mat => fun (ab : ℝ × ℝ) => fun j i => round ((((q Mat) ab) j i:ℝ)*((ell Mat) ab) j i)
    let tau := fun Mat => fun (ab : ℝ × ℝ) => fun j i => ((((b Mat) ab) j i:ℝ)-(((q Mat) ab) j i:ℝ)*((ell Mat) ab) j i)/2
    let dual := fun Mat => fun (ab : ℝ × ℝ) => fun j i => -2*((mu Mat) ab) j i*(Real.sqrt (2/(3*((mu Mat) ab) j i*(((q Mat) ab) j i:ℝ))))^3
    let cloud := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (![Int.fract (-(((vinv Mat) ab) j i:ℝ)*((b Mat) ab) j i/((q Mat) ab) j i),
      Int.fract (-(((vinv Mat) ab) j i:ℝ)/((q Mat) ab) j i),((dual Mat) ab) j i/Real.sqrt K₀,
      (3*((dual Mat) ab) j i*((tau Mat) ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((b Mat) ab) j 0-((cround Mat) ab) j 0=((b Mat) ab) j 1-((cround Mat) ab) j 1) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ a, |((cloud Mat) ab) j 0 a-((cloud Mat) ab) j 1 a| ≤ 2*radius a) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈S Mat ab,
      |cloud Mat ab j 0 1-cloud Mat ab j 1 1| ≤ 1/(6*(K₀:ℝ)^2*V)) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    (∀ Mat∈Matrices, Mat 0*Mat 3-Mat 1*Mat 2=1) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), (Mat 2:ℝ)*(((rat Mat) ab) j 0:ℝ)+Mat 3=(((q Mat) ab) j 1:ℝ)/((q Mat) ab) j 0) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((Mat 0:ℝ)*(((rat Mat) ab) j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(((rat Mat) ab) j 0:ℝ)+Mat 3)=(((rat Mat) ab) j 1:ℝ)) →
    (∀ Mat∈Matrices, |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), |(((anchor Mat) ab) j:ℝ)-(((rat Mat) ab) j 0:ℝ)| ≤ ε) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), 256*((((anchor Mat) ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*(((anchor Mat) ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Gcap := R^4/(6*N^2*V)
    let Kstar := 2*Cfirst*R^4/(Lunit^3*N^2)
    let Aweight := 4*(m0:ℝ)
    let Bweight := 4*(m0:ℝ)*Cpack*R^4/(Lunit^2*N^2*(Uref:ℝ))+
      (m0:ℝ)*Cgap*R^4/(N^2*(Uref:ℝ))+2*(m0:ℝ)*Gcap
    (∑ Mat∈Matrices, ∑ ab∈Gaps, ((S Mat ab).card:ℝ)) ≤
      588*(Uband/lambda)^2*Uband^2*Gcap*
        (Aweight*Kstar^((3:ℝ)⁻¹)*Gcap^((2:ℝ)/3)+Bweight) := by
  classical
  intro Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear hnearNarrow
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor Lunit Gamma Cthird Cpack Cfirst Cgap
    Gcap Kstar Aweight Bweight
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hunit : 0 < Lunit := div_pos (mul_pos (by norm_num) hκ) hCphys
  have hm0 : 0 < m0 := by dsimp only [m0]; omega
  have hUp : (0:ℝ) < Uref := by exact_mod_cast (show 0 < Uref by omega)
  have hδ0 := approximateModelPhase_tolerance_nonneg (hF 0)
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  obtain ⟨hCR,hCN⟩ := physical_source_quartic_constants_nonneg hσ hδ0
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hCt : 0 ≤ Ct := by dsimp only [Ct]; positivity
  have hCc : 0 ≤ Cc := by dsimp only [Cc]; positivity
  have hK : 0 ≤ Kres := by dsimp only [Kres]; positivity
  have hΓ : 0 ≤ Gamma := div_nonneg hCphys.le hκ.le
  have hCthird : 0 ≤ Cthird :=
    mul_nonneg hΓ (add_nonneg (mul_nonneg (by norm_num) hK)
      (mul_nonneg (by norm_num) hCR))
  have hcore : 0 ≤ Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ :=
    add_nonneg (mul_nonneg (sq_nonneg Gamma) hCthird)
      (div_nonneg (mul_nonneg hΓ hC₃) hκ.le)
  have hCpack : 0 ≤ Cpack :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCphys.le) hcore) hκ.le
  have hCfirst : 0 ≤ Cfirst :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCphys.le) hcore) (sq_nonneg κ)
  have hCgap : 0 ≤ Cgap :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCphys.le)
      (add_nonneg (mul_nonneg (sq_nonneg Gamma) hB)
        (div_nonneg (mul_nonneg hΓ hC₃) hκ.le))) hκ.le
  have hVp : 0 < V := zero_lt_one.trans_le hV
  have hGcap : 0 ≤ Gcap := by dsimp only [Gcap]; positivity
  have hKstar : 0 ≤ Kstar := by dsimp only [Kstar]; positivity
  have hAweight : 0 ≤ Aweight := by dsimp only [Aweight]; positivity
  have hBweight : 0 ≤ Bweight := by dsimp only [Bweight]; positivity
  have hK₀ : (1:ℝ) ≤ K₀ := by exact_mod_cast (show 1 ≤ K₀ from NeZero.pos K₀)
  have hmass Mat (hMat : Mat∈Matrices) :
      (∑ ab∈Gaps, ((S Mat ab).card:ℝ)) ≤
        4*(m0:ℝ)*((Kstar/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+
          Cpack*R^4/(Lunit^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ)))+
        (m0:ℝ)*(2+Cgap*R^4/(N^2*|(Mat 2:ℝ)| *(Uref:ℝ))) := by
    exact physicalModelPhase_actual_fourier_charted_all_reference_sample_mass
      Uref Refs Gaps (Bselect:=Bselect) Bmajor Cmajor (S Mat) Q K₀
      (rat Mat) (vinv Mat) (parity Mat) (anchor Mat) Mat e r v s
      hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW (hx Mat hMat) (hwindow Mat hMat) (hden Mat hMat) hlambda hUband hθ hθmax (hcurv Mat hMat) (hinv Mat hMat) hchart horientation hBcut hs hrefSet hparentSet hsep (hwideL Mat hMat) (hwideU Mat hMat) hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen (hfamilyGap Mat hMat)
      (hc Mat hMat) (hlarge Mat hMat) hgap
      (hsourceColor Mat hMat) (hlevel Mat hMat) (hcolor Mat hMat) (hnear Mat hMat) hsmall hNR hRN hNcube hminscale (hMatdet Mat hMat) (hMatt Mat hMat) (hMatmap Mat hMat) (hMatgamma Mat hMat) hNtwo (hL Mat hMat) (hU Mat hMat) (hanchor Mat hMat) (hcut Mat hMat) (hcount Mat hMat)
      hsize hD hΔ hBsize hBmajor hCmajor
  let Occupied := Matrices.filter (fun Mat => ∃ ab∈Gaps, (S Mat ab).Nonempty)
  have hin : Occupied ⊆ Matrices := Finset.filter_subset _ _
  have hpick Mat (hMat : Mat∈Occupied) : ∃ ab, ab∈Gaps ∧ ∃ j, j∈S Mat ab := by
    obtain ⟨ab,hab,hne⟩ := (Finset.mem_filter.mp hMat).2
    obtain ⟨j,hj⟩ := hne
    exact ⟨ab,hab,j,hj⟩
  choose! ab hab j hj using hpick
  let pr := fun Mat i => rat Mat (ab Mat) (j Mat) i
  have hpden Mat (hMat : Mat∈Occupied) i := hden Mat (hin hMat) _ (hab Mat hMat) _ (hj Mat hMat) i
  have hpcurv Mat (hMat : Mat∈Occupied) i := hcurv Mat (hin hMat) _ (hab Mat hMat) _ (hj Mat hMat) i
  have hpMatt Mat (hMat : Mat∈Occupied) := hMatt Mat (hin hMat) _ (hab Mat hMat) _ (hj Mat hMat)
  have hpmap Mat (hMat : Mat∈Occupied) := hMatmap Mat (hin hMat) _ (hab Mat hMat) _ (hj Mat hMat)
  have hpcap Mat (hMat : Mat∈Occupied) : Mat 2 ≠ 0 ∧ |(Mat 2:ℝ)| ≤ Gcap := by
    have hh := fourier_matrix_narrowed_coordinate_entry_bound
      (fun i => ((pr Mat i).den:ℤ)) (fun i => (pr Mat i).num)
      (vinv Mat (ab Mat) (j Mat)) Mat (Q:=(Q:ℝ)) (K:=(K₀:ℝ)) (V:=V)
      (N:=N) (R:=R)
      (fun i => by
        exact_mod_cast (pr Mat i).den_pos)
      hK₀ hV hN hmesh
      (fun i => by
        have hlo : ((pr Mat i).den:ℝ) ≤ Q := by exact_mod_cast (hpden Mat hMat i).1
        have hhi : (Q:ℝ) ≤ 2*((pr Mat i).den:ℝ) := by exact_mod_cast (hpden Mat hMat i).2
        simpa only [Int.cast_natCast] using And.intro hlo hhi)
      (hinv Mat (hin hMat) _ (hab Mat hMat) _ (hj Mat hMat))
      (hMatdet Mat (hin hMat))
      (by simpa only [Int.cast_natCast,Rat.cast_def] using hpMatt Mat hMat)
      (by simpa only [Int.cast_natCast,Rat.cast_def] using hpmap Mat hMat)
      (hMatgamma Mat (hin hMat))
      (by
        have hh := hnearNarrow Mat (hin hMat) _ (hab Mat hMat) _ (hj Mat hMat)
        change |Int.fract (-(vinv Mat (ab Mat) (j Mat) 0:ℝ)/(pr Mat 0).den)-
          Int.fract (-(vinv Mat (ab Mat) (j Mat) 1:ℝ)/(pr Mat 1).den)| ≤
            1/(6*(K₀:ℝ)^2*V) at hh
        simpa only [Int.cast_natCast] using hh)
    exact ⟨hc Mat (hin hMat),hh.2⟩
  have hratios Mat (hMat : Mat∈Occupied) :
      |((pr Mat 1).den:ℝ)/(pr Mat 0).den-1| ≤ θ ∧
      |((pr Mat 1).num:ℝ)/(pr Mat 0).num-1| ≤ θ := by
    have hh := (rational_narrow_band_partition Finset.univ (pr Mat) Q
      hQ hlambda hUband hθ (fun i _ => hpcurv Mat hMat i)
      (fun i _ => hpden Mat hMat i)).2
    exact hh 0 (Finset.mem_univ _) 1 (Finset.mem_univ _)
      (hsourceColor Mat (hin hMat) _ (hab Mat hMat) _ (hj Mat hMat))
  have hpt Mat (hMat : Mat∈Occupied) :
      (1:ℝ)/2 ≤ (Mat 2:ℝ)*(pr Mat 0:ℝ)+Mat 3 ∧
      (Mat 2:ℝ)*(pr Mat 0:ℝ)+Mat 3 ≤ 2 := by
    rw [hpMatt Mat hMat]
    have hh := abs_le.mp (hratios Mat hMat).1
    constructor <;> linarith only [hh.1,hh.2,hθmax]
  have hpnum Mat (hMat : Mat∈Occupied) :
      (1:ℝ)/2 ≤ ((Mat 0:ℝ)*(pr Mat 0:ℝ)+Mat 1)/(pr Mat 0:ℝ) ∧
      ((Mat 0:ℝ)*(pr Mat 0:ℝ)+Mat 1)/(pr Mat 0:ℝ) ≤ 2 := by
    have hx0 : (pr Mat 0:ℝ) ≠ 0 := abs_pos.mp (hlambda.trans_le (hpcurv Mat hMat 0).1)
    have hnum0 : ((pr Mat 0).num:ℝ) ≠ 0 := by
      intro hh
      apply hx0
      rw [Rat.cast_def,hh,zero_div]
    have hq0 : (0:ℝ) < (pr Mat 0).den := by exact_mod_cast (pr Mat 0).den_pos
    have hq1 : (0:ℝ) < (pr Mat 1).den := by exact_mod_cast (pr Mat 1).den_pos
    have htp : 0 < (Mat 2:ℝ)*(pr Mat 0:ℝ)+Mat 3 := by
      linarith only [(hpt Mat hMat).1]
    have he := (div_eq_iff htp.ne').mp (hpmap Mat hMat)
    have hid : ((Mat 0:ℝ)*(pr Mat 0:ℝ)+Mat 1)/(pr Mat 0:ℝ)=
        ((pr Mat 1).num:ℝ)/(pr Mat 0).num := by
      rw [he,hpMatt Mat hMat]
      change ((pr Mat 1:ℝ)*(((pr Mat 1).den:ℝ)/(pr Mat 0).den))/(pr Mat 0:ℝ)=
        ((pr Mat 1).num:ℝ)/(pr Mat 0).num
      simp only [Rat.cast_def]
      field_simp [hq0.ne',hq1.ne',hnum0]
    rw [hid]
    have hh := abs_le.mp (hratios Mat hMat).2
    constructor <;> linarith only [hh.1,hh.2,hθmax]
  have hpointMass Mat (hMat : Mat∈Occupied) :
      (∑ ab∈Gaps, ((S Mat ab).card:ℝ)) ≤
        Aweight*(Kstar/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+Bweight/|(Mat 2:ℝ)| := by
    exact matrix_sample_mass_weight_majorant (Nat.cast_nonneg m0)
      (abs_pos.mpr (by exact_mod_cast (hpcap Mat hMat).1)) (hpcap Mat hMat).2
      (hmass Mat (hin hMat))
  have hsum := resonance_matrix_curvature_band_cubic_weight_sum Occupied
    (fun Mat => (pr Mat 0:ℝ)) (fun Mat => (pr Mat 1:ℝ))
    hlambda hGcap hAweight hKstar hBweight
    (fun Mat hMat => hMatdet Mat (hin hMat)) hpcap
    (fun Mat hMat => hpcurv Mat hMat 0) (fun Mat hMat => hpcurv Mat hMat 1)
    hpt hpmap hpnum (fun Mat hMat => haction Mat (hin hMat))
  have hsumOcc : (∑ Mat∈Matrices, ∑ ab∈Gaps, ((S Mat ab).card:ℝ))=
      ∑ Mat∈Occupied, ∑ ab∈Gaps, ((S Mat ab).card:ℝ) := by
    symm
    apply Finset.sum_subset hin
    intro Mat hMat hnot
    apply Finset.sum_eq_zero
    intro ab hab
    have he : S Mat ab=∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hne
      exact hnot (Finset.mem_filter.mpr ⟨hMat,ab,hab,hne⟩)
    simp only [he,Finset.card_empty,Nat.cast_zero]
  rw [hsumOcc]
  exact (Finset.sum_le_sum hpointMass).trans hsum

                                                                                                 
theorem physicalModelPhase_actual_fourier_charted_matrix_source_mass
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Matrices : Finset (Fin 4 → ℤ)) (Bmajor Cmajor : ℕ)
    (S : (Fin 4 → ℤ) → ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → Fin 2 → ℚ)
    (vinv : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → Fin 2 → Fin 2)
    (anchor : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ V : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T)
    (hM : 0 < M)
    (hN : 0 < N)
    (hR : 1 ≤ R)
    (hRM : R ≤ M)
    (hQ : 0 < Q)
    (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i)
    (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((x Mat) ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hden : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, (((rat Mat) ab) j i).den ≤ Q ∧ Q ≤ 2*(((rat Mat) ab) j i).den)
    (hlambda : 0 < lambda)
    (hUband : 0 ≤ Uband)
    (hθ : 0 < θ)
    (hθmax : θ ≤ 1/24)
    (hcurv : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, lambda ≤ |(((rat Mat) ab) j i:ℝ)| ∧ |(((rat Mat) ab) j i:ℝ)| ≤ Uband)
    (hinv : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((((rat Mat) ab) j i).den:ℤ) ∣ (((rat Mat) ab) j i).num*((vinv Mat) ab) j i-1)
    (hchart : ∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1)
    (horientation : ∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2))
    (hBcut : 0 < Bcut)
    (hs : ∀ ab∈Gaps, (s ab) ≠ 0)
    (hrefSet : ∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs)
    (hparentSet : ∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hwideL : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : ∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ))
    (hgapWidth : ∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2))
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), (((rat Mat) ab) j 0:ℝ)∈Icc ab.1 ab.2)
    (hc : ∀ Mat∈Matrices, Mat 2 ≠ 0)
    (hlarge : ∀ Mat∈Matrices, 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (haction : ∀ Mat∈Matrices, 8*Uband ≤ |(Mat 2:ℝ)| *lambda^2)
    (hV : 1 ≤ V)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (⌊((((rat Mat) ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((((rat Mat) ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((sourceColor Mat) ab) j 0=((sourceColor Mat) ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, iteratedDeriv 2 (f i) (((x Mat) ab) j i)/2=(((rat Mat) ab) j i:ℝ)) →
    let q := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (((rat Mat) ab) j i).den
    let mu := fun Mat => fun (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round (((x Mat) ab) j i))/6
    let ell := fun Mat => fun (ab : ℝ × ℝ) => fun j i => deriv (f i) (round (((x Mat) ab) j i))
    let b := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (⌊(((q Mat) ab) j i:ℝ)*((ell Mat) ab) j i⌋+(((parity Mat) ab) j i:ℕ) : ℤ)
    let cround := fun Mat => fun (ab : ℝ × ℝ) => fun j i => round ((((q Mat) ab) j i:ℝ)*((ell Mat) ab) j i)
    let tau := fun Mat => fun (ab : ℝ × ℝ) => fun j i => ((((b Mat) ab) j i:ℝ)-(((q Mat) ab) j i:ℝ)*((ell Mat) ab) j i)/2
    let dual := fun Mat => fun (ab : ℝ × ℝ) => fun j i => -2*((mu Mat) ab) j i*(Real.sqrt (2/(3*((mu Mat) ab) j i*(((q Mat) ab) j i:ℝ))))^3
    let cloud := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (![Int.fract (-(((vinv Mat) ab) j i:ℝ)*((b Mat) ab) j i/((q Mat) ab) j i),
      Int.fract (-(((vinv Mat) ab) j i:ℝ)/((q Mat) ab) j i),((dual Mat) ab) j i/Real.sqrt K₀,
      (3*((dual Mat) ab) j i*((tau Mat) ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((b Mat) ab) j 0-((cround Mat) ab) j 0=((b Mat) ab) j 1-((cround Mat) ab) j 1) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ a, |((cloud Mat) ab) j 0 a-((cloud Mat) ab) j 1 a| ≤ 2*radius a) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈S Mat ab,
      |cloud Mat ab j 0 1-cloud Mat ab j 1 1| ≤ 1/(6*(K₀:ℝ)^2*V)) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    (∀ Mat∈Matrices, Mat 0*Mat 3-Mat 1*Mat 2=1) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), (Mat 2:ℝ)*(((rat Mat) ab) j 0:ℝ)+Mat 3=(((q Mat) ab) j 1:ℝ)/((q Mat) ab) j 0) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((Mat 0:ℝ)*(((rat Mat) ab) j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(((rat Mat) ab) j 0:ℝ)+Mat 3)=(((rat Mat) ab) j 1:ℝ)) →
    (∀ Mat∈Matrices, |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), |(((anchor Mat) ab) j:ℝ)-(((rat Mat) ab) j 0:ℝ)| ≤ ε) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), 256*((((anchor Mat) ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*(((anchor Mat) ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Gcap := R^4/(6*N^2*V)
    let Kstar := 2*Cfirst*R^4/(Lunit^3*N^2)
    let Aweight := 4*(m0:ℝ)
    let Bweight := 4*(m0:ℝ)*Cpack*R^4/(Lunit^2*N^2*(Uref:ℝ))+
      (m0:ℝ)*Cgap*R^4/(N^2*(Uref:ℝ))+2*(m0:ℝ)*Gcap
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    ((∑ Mat∈Matrices, ∑ ab∈Gaps, ((S Mat ab).card:ℝ)) ≤
      588*(Uband/lambda)^2*Uband^2*Gcap*
        (Aweight*Kstar^((3:ℝ)⁻¹)*Gcap^((2:ℝ)/3)+Bweight)) ∧
    (∑ Mat∈Matrices, ∑ ab∈Gaps, ((S Mat ab).card:ℝ)) ≤
      588*(m0:ℝ)*(Uband/lambda)^2*Uband^2*(R^8/N^4)*
        (Cmain/V^((5:ℝ)/3)+Ctail/((Uref:ℝ)*V)) := by
  classical
  intro Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear hnearNarrow
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor Lunit Gamma Cthird Cpack Cfirst Cgap
    Gcap Kstar Aweight Bweight Cmain Ctail
  have hraw := physicalModelPhase_actual_fourier_charted_matrix_source_mass_core
    Uref Refs Gaps (Bselect:=Bselect) Matrices Bmajor Cmajor S Q K₀
    rat vinv parity anchor e r v s
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap
    hc hlarge haction hV hgap
    hsourceColor hlevel hcolor hnear hnearNarrow
    hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    hNtwo hL hU hanchor hcut hcount hsize hD hΔ hBsize hBmajor hCmajor
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hunit : 0 < Lunit := div_pos (mul_pos (by norm_num) hκ) hCphys
  have hUp : (0:ℝ) < Uref := by exact_mod_cast (show 0 < Uref by omega)
  have hδ0 := approximateModelPhase_tolerance_nonneg (hF 0)
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  obtain ⟨hCR,hCN⟩ := physical_source_quartic_constants_nonneg hσ hδ0
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hCt : 0 ≤ Ct := by dsimp only [Ct]; positivity
  have hCc : 0 ≤ Cc := by dsimp only [Cc]; positivity
  have hK : 0 ≤ Kres := by dsimp only [Kres]; positivity
  have hΓ : 0 ≤ Gamma := div_nonneg hCphys.le hκ.le
  have hCthird : 0 ≤ Cthird :=
    mul_nonneg hΓ (add_nonneg (mul_nonneg (by norm_num) hK)
      (mul_nonneg (by norm_num) hCR))
  have hcore : 0 ≤ Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ :=
    add_nonneg (mul_nonneg (sq_nonneg Gamma) hCthird)
      (div_nonneg (mul_nonneg hΓ hC₃) hκ.le)
  have hCpack : 0 ≤ Cpack :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCphys.le) hcore) hκ.le
  have hCfirst : 0 ≤ Cfirst :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCphys.le) hcore) (sq_nonneg κ)
  have hCgap : 0 ≤ Cgap :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCphys.le)
      (add_nonneg (mul_nonneg (sq_nonneg Gamma) hB)
        (div_nonneg (mul_nonneg hΓ hC₃) hκ.le))) hκ.le
  refine ⟨hraw,hraw.trans ?_⟩
  exact matrix_physical_source_scale (zero_lt_one.trans_le hR) hN hunit hUp hV
    hCfirst hCpack hCgap (Nat.cast_nonneg m0)


                                                                                          
theorem physicalModelPhase_reference_matrix_window_selection
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2)))
    (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ)
    (F : Fin 2 → ℝ → ℝ) (A Wlim : Fin 2 → ℝ) (za zb : ℤ → ℝ) (AlenA Alen : ℤ → ℕ)
    (N : ℕ) (Za Z : ℤ) (W : ℝ)
    {σ δ T M : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+Wlim i ≤ 2*M)
    (hbase : ∀ ij∈P, W ≤ za ij.1.1)
    (hz : ∀ ij∈P, zb ij.2.1∈Ioo 0 (Wlim 1))
    (hgeometryA : ∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ))
    (hgeometry : ∀ ij∈P, N ≤ Alen ij.2.1 ∧ Alen ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(Alen ij.2.1:ℤ)=Z+(N:ℤ)*ij.2.1+2*(N:ℤ)) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    (∀ ij∈P, ((Mat ij 0:ℝ)*h 0 (za ij.1.1)+Mat ij 1)/
      ((Mat ij 2:ℝ)*h 0 (za ij.1.1)+Mat ij 3)=h 1 (zb ij.2.1)) →
    let block := fun ij : (ℤ × Fin 2) × (ℤ × Fin 2) =>
      ⌊(za ij.1.1-W)/(N:ℝ)⌋.toNat
    let S := fun A ab => (P.filter (fun ij => Mat ij=A ∧ gap ij=ab)).image block
    ∃ pick : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → (ℤ × Fin 2) × (ℤ × Fin 2),
      (∀ A∈P.image Mat, ∀ ab∈P.image gap, ∀ j∈S A ab,
        pick A ab j∈P ∧ Mat (pick A ab j)=A ∧ gap (pick A ab j)=ab ∧
        block (pick A ab j)=j ∧
        za (pick A ab j).1.1∈Icc (W+(N:ℝ)*j) (W+(N:ℝ)*((j:ℝ)+1))) ∧
      P.card ≤ 60*∑ A∈P.image Mat, ∑ ab∈P.image gap, (S A ab).card := by
  classical
  intro f h hmap block S
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hnonneg ij (hij : ij∈P) : 0 ≤ ⌊(za ij.1.1-W)/(N:ℝ)⌋ :=
    Int.floor_nonneg.mpr (div_nonneg (sub_nonneg.mpr (hbase ij hij)) hNp.le)
  have hwindow ij (hij : ij∈P) :
      za ij.1.1∈Icc (W+(N:ℝ)*block ij) (W+(N:ℝ)*((block ij:ℝ)+1)) := by
    have he : (block ij:ℤ)=⌊(za ij.1.1-W)/(N:ℝ)⌋ :=
      Int.toNat_of_nonneg (hnonneg ij hij)
    have heR : (block ij:ℝ)=(⌊(za ij.1.1-W)/(N:ℝ)⌋:ℝ) := by exact_mod_cast he
    have hlo := Int.floor_le ((za ij.1.1-W)/(N:ℝ))
    have hhi := Int.lt_floor_add_one ((za ij.1.1-W)/(N:ℝ))
    rw [←heR] at hlo hhi
    have hl := (le_div_iff₀ hNp).mp hlo
    have hu := (div_lt_iff₀ hNp).mp hhi
    constructor <;> nlinarith only [hl,hu]
  have hex A ab j (hj : j∈S A ab) :
      ∃ ij, ij∈P ∧ Mat ij=A ∧ gap ij=ab ∧ block ij=j := by
    obtain ⟨ij,hij,he⟩ := Finset.mem_image.mp hj
    have hh := Finset.mem_filter.mp hij
    exact ⟨ij,hh.1,hh.2.1,hh.2.2,he⟩
  let pick := fun A ab j => if hj : j∈S A ab then
    Classical.choose (hex A ab j hj) else ((0,0),(0,0))
  refine ⟨pick,?_,?_⟩
  · intro A _hA ab _hab j hj
    have hp : pick A ab j∈P ∧ Mat (pick A ab j)=A ∧
        gap (pick A ab j)=ab ∧ block (pick A ab j)=j := by
      dsimp only [pick]
      rw [dite_eq_left hj]
      exact Classical.choose_spec (hex A ab j hj)
    refine ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2,?_⟩
    simpa only [hp.2.2.2] using hwindow (pick A ab j) hp.1
  · have hmono : StrictMonoOn (h 1) (Ioo 0 (Wlim 1)) := by
      intro a ha b hb hab
      have hh := physicalModelPhase_halfCurvature_growth hσ hδ (hF 1)
        hT hM (hA 1) (hW 1) ha hb hab.le
      have hκ := modelPhaseThirdLower_pos hσ
      have hc : 0 < modelPhaseThirdLower σ*T/(2*M^3) := by positivity
      exact sub_pos.mp ((mul_pos hc (sub_pos.mpr hab)).trans_le hh)
    have hspan ij (hij : ij∈P) :
        (N:ℝ) ≤ (Z:ℝ)+(ij.2.1:ℝ)*N+2*N-(round (zb ij.2.1):ℝ) ∧
        (Z:ℝ)+(ij.2.1:ℝ)*N+2*N-(round (zb ij.2.1):ℝ) ≤ 3*N := by
      have hg := hgeometry ij hij
      have hlo : (N:ℝ) ≤ Alen ij.2.1 := by exact_mod_cast hg.1
      have hhi : (Alen ij.2.1:ℝ) ≤ 3*(N:ℝ) := by exact_mod_cast hg.2.1
      have he : (round (zb ij.2.1):ℝ)+(Alen ij.2.1:ℝ)=
          (Z:ℝ)+(N:ℝ)*ij.2.1+2*(N:ℝ) := by exact_mod_cast hg.2.2
      constructor <;> nlinarith only [hlo,hhi,he]
    have hprojection := curvature_pair_card_le_matrix_blocks P Mat (h 0) (h 1)
      za zb (Ioo 0 (Wlim 1)) hNp hmono.injOn hz hspan hmap
    let Vfirst := P.image (fun ij => (Mat ij,ij.1.1))
    have hcard : Vfirst.card=∑ B∈P.image Mat,
        ((P.filter (fun ij => Mat ij=B)).image (fun ij => ij.1.1)).card := by
      calc
        _ = ∑ B∈P.image Mat, (Vfirst.filter (fun v => v.1=B)).card := by
          apply Finset.card_eq_sum_card_fiberwise
          intro v hv
          obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hv
          exact Finset.mem_image.mpr ⟨ij,hij,rfl⟩
        _ = _ := by
          apply Finset.sum_congr rfl
          intro B _
          have hImage : (Vfirst.filter (fun v => v.1=B)).image Prod.snd=
              (P.filter (fun ij => Mat ij=B)).image (fun ij => ij.1.1) := by
            ext k
            simp only [Vfirst,Finset.mem_image,Finset.mem_filter]
            constructor
            · rintro ⟨v,⟨⟨ij,hij,he⟩,hvB⟩,hvk⟩
              refine ⟨ij,⟨hij,?_⟩,?_⟩
              · rw [←he] at hvB
                exact hvB
              · rw [←he] at hvk
                exact hvk
            · rintro ⟨ij,⟨hij,hB⟩,hk⟩
              exact ⟨(Mat ij,ij.1.1),⟨⟨ij,hij,rfl⟩,hB⟩,hk⟩
          rw [←hImage]
          symm
          apply Finset.card_image_of_injOn
          intro x hx y hy he
          exact Prod.ext ((Finset.mem_filter.mp hx).2.trans
            (Finset.mem_filter.mp hy).2.symm) he
    change P.card ≤ 12*Vfirst.card at hprojection
    rw [hcard] at hprojection
    have hper B : ((P.filter (fun ij => Mat ij=B)).image (fun ij => ij.1.1)).card ≤
        5*((P.filter (fun ij => Mat ij=B)).image
          (fun ij => ⌊(za ij.1.1-W)/(N:ℝ)⌋)).card := by
      have hh := rounded_offset_floor_block_count
        ((P.filter (fun ij => Mat ij=B)).image (fun ij => ij.1.1))
        za AlenA N Za W hN
        (by
          intro k hk
          obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hk
          exact hgeometryA ij (Finset.mem_filter.mp hij).1)
      simpa only [Finset.image_image,Function.comp_def] using hh
    have hp : P.card ≤ 60*∑ B∈P.image Mat,
        ((P.filter (fun ij => Mat ij=B)).image
          (fun ij => ⌊(za ij.1.1-W)/(N:ℝ)⌋)).card := by
      calc
        _ ≤ 12*∑ B∈P.image Mat,
            ((P.filter (fun ij => Mat ij=B)).image (fun ij => ij.1.1)).card := hprojection
        _ ≤ 12*∑ B∈P.image Mat, 5*((P.filter (fun ij => Mat ij=B)).image
            (fun ij => ⌊(za ij.1.1-W)/(N:ℝ)⌋)).card :=
          Nat.mul_le_mul_left 12 (Finset.sum_le_sum (fun B _ => hper B))
        _ = _ := by rw [←Finset.mul_sum]; ring
    apply hp.trans
    apply Nat.mul_le_mul_left 60
    apply Finset.sum_le_sum
    intro A _hA
    let E := P.filter (fun ij => Mat ij=A)
    let I := E.image (fun ij => ⌊(za ij.1.1-W)/(N:ℝ)⌋)
    have hinj : Set.InjOn Int.toNat (↑I) := by
      intro x hx y hy he
      obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨kl,hkl,rfl⟩ := Finset.mem_image.mp hy
      have hix := hnonneg ij (Finset.mem_filter.mp hij).1
      have hiy := hnonneg kl (Finset.mem_filter.mp hkl).1
      omega
    have he : I.card=(E.image block).card := by
      rw [←Finset.card_image_of_injOn hinj,Finset.image_image]
      rfl
    change I.card ≤ _
    rw [he]
    have hsub : E.image block ⊆ (P.image gap).biUnion (fun ab => S A ab) := by
      intro j hj
      obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hj
      have hh := Finset.mem_filter.mp hij
      exact Finset.mem_biUnion.mpr ⟨gap ij,Finset.mem_image_of_mem gap hh.1,
        Finset.mem_image.mpr ⟨ij,Finset.mem_filter.mpr ⟨hh.1,hh.2,rfl⟩,rfl⟩⟩
    exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)

universe huxleyNarrowV

private theorem huxley_narrowed_sieve_frequency_scale {N t η ζ Vscale : ℝ}
    (hN : 1≤N) (ht : t∈Icc 1 N) (hη : 0<η) (hζ : 0<ζ) (hV : 1≤Vscale) :
    let a : Fin 4 → ℝ := ![1/(12*N),1/(12*N^2*Vscale),η/12,ζ/12]
    let U : Fin 4 → ℝ := ![t,t^2,(1/η)*(t/N)^((3:ℝ)/2),(1/ζ)*Real.sqrt (t/N)]
    ∀ d, a d*|U d| ≤ 1/12 := by
  have hNp : 0<N := by linarith
  have hVp : 0<Vscale := zero_lt_one.trans_le hV
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
  · change (1/(12*N^2*Vscale))*|t^2|≤1/12
    rw [abs_of_nonneg (sq_nonneg _)]
    have hsq : t^2≤N^2 := pow_le_pow_left₀ ht0 ht.2 2
    have hh := mul_le_mul_of_nonneg_left hsq (by positivity : 0≤1/(12*N^2*Vscale))
    calc
      _ ≤ (1/(12*N^2*Vscale))*N^2 := hh
      _ = 1/(12*Vscale) := by field_simp
      _ ≤ 1/12 := one_div_le_one_div_of_le (by norm_num) (by linarith)
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

private theorem huxley_narrowed_sieve_box_scale {N η ζ Vscale : ℝ}
    (hN : 1≤N) (hη : η∈Ioc 0 1) (hζ : ζ∈Ioc 0 1) (hV : 1≤Vscale) :
    let a : Fin 4 → ℝ := ![1/(12*N),1/(12*N^2*Vscale),η/12,ζ/12]
    let δ : Fin 4 → ℝ := ![1,1,2,2]
    (∀ d, 0<a d) ∧
    (∀ d, 1/(δ d+2*a d) ≤ (![1,1,1/2,1/2] : Fin 4 → ℝ) d) ∧
    16777216*(∏ d, (δ d+2*a d))/(∏ d, a d) ≤
      (16777216*36*12^4)*N^3*Vscale/(η*ζ) := by
  dsimp only
  let a : Fin 4 → ℝ := ![1/(12*N),1/(12*N^2*Vscale),η/12,ζ/12]
  let δ : Fin 4 → ℝ := ![1,1,2,2]
  have hNp : 0<N := by linarith
  have hVp : 0<Vscale := zero_lt_one.trans_le hV
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
      · change 1/(12*N^2*Vscale)≤1/12
        have hNsq : (1:ℝ) ≤ N^2 := by nlinarith
        have hNV : (1:ℝ) ≤ N^2*Vscale :=
          one_mul (1:ℝ) ▸ mul_le_mul hNsq hV zero_le_one (sq_nonneg N)
        exact one_div_le_one_div_of_le (by norm_num) (by nlinarith only [hNV])
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
    have hprod : (∏ d, a d) = η*ζ/(12^4*N^3*Vscale) := by
      norm_num [a,Fin.prod_univ_succ]
      field_simp
      ring
    have hp : 0<∏ d, a d := Finset.prod_pos (fun d _ => ha d)
    calc
      _ ≤ 16777216*36/(∏ d, a d) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hD (by norm_num)) hp.le
      _ = _ := by rw [hprod]; field_simp


private theorem huxley_narrowed_sieve_final_scale
    {N η ζ Vscale L C B a p ε : ℝ}
    (hN : 0<N) (hη : 0<η) (hζ : 0<ζ) :
    (a*p)*((L*N^3*Vscale/(η*ζ))*
      (C*η*ζ*N^((9:ℝ)+ε)*B^12)) =
    (L*C)*Vscale*N^((12:ℝ)+ε)*a*B^12*p := by
  have hpow : N^3*N^((9:ℝ)+ε)=N^((12:ℝ)+ε) := by
    rw [←Real.rpow_ofNat,←Real.rpow_add hN]
    congr 1
    ring
  rw [←hpow]
  field_simp

                                                                        
                                                                        
                                                                     
private theorem exists_huxleySourceCurve_narrowed_double_sieve {ε : ℝ} (hε : 0<ε) :
    ∃ C>(0:ℝ), ∀ (N : ℕ), 1≤N → ∀ (η ζ Vscale : ℝ),
      η∈Icc (1/(N:ℝ)^2) 1 → ζ∈Icc (1/(N:ℝ)) 1 → 1≤Vscale →
      ∀ (ι κ : Type huxleyNarrowV) (S : Finset ι) (T : Finset κ) (w : κ → ℂ)
        (m : κ → ℤ) (x : ι → Fin 4 → ℝ) (B : ℝ),
        0≤B → (∀ j∈T,1 ≤ m j ∧ m j≤N) →
        (∀ j∈T,‖w j‖≤1) →
        (∀ q : ℤ,((T.filter (fun j => m j=q)).card:ℝ)≤B) →
        (∀ i∈S,x i∈Icc ![0,0,-1,-1] (fun _ => 1)) →
        let U := fun j => ![(m j:ℝ),(m j:ℝ)^2,
          (1/η)*((m j:ℝ)/N)^((3:ℝ)/2),(1/ζ)*Real.sqrt ((m j:ℝ)/N)]
        let a : Fin 4 → ℝ := ![1/(12*(N:ℝ)),1/(12*(N:ℝ)^2*Vscale),η/12,ζ/12]
        (∑ i∈S,‖∑ j∈T,w j*GafniTao.fordAdditiveCharacter (∑ d,U j d*x i d)‖)^12 ≤
          C*Vscale*(N:ℝ)^((12:ℝ)+ε)*(S.card:ℝ)^10*B^12*
            (((S ×ˢ S).filter (fun ij => ∀ d, |x ij.1 d-x ij.2 d|≤2*a d)).card:ℝ) := by
  classical
  obtain ⟨C,hC,hcount⟩ := exists_bourgainSourceCurve_six_tuple_first_spacing.{huxleyNarrowV} hε
  let L : ℝ := 16777216*36*12^4
  refine ⟨L*C,by dsimp [L]; positivity,?_⟩
  intro N hN η ζ Vscale hη hζ hV ι κ S T w m x B hB hm hw hmass hx
  dsimp only
  have hNr : (1:ℝ)≤N := by exact_mod_cast hN
  have hNp : (0:ℝ)<N := by linarith
  have hηp : 0<η := lt_of_lt_of_le (by positivity) hη.1
  have hζp : 0<ζ := lt_of_lt_of_le (by positivity) hζ.1
  let a : Fin 4 → ℝ := ![1/(12*(N:ℝ)),1/(12*(N:ℝ)^2*Vscale),η/12,ζ/12]
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
    huxley_narrowed_sieve_box_scale hNr ⟨hηp,hη.2⟩ ⟨hζp,hζ.2⟩ hV
  have hD d : 0<D d := by fin_cases d <;> norm_num [D,Matrix.cons_val_succ]
  have hU j (hj : j∈T) : ∀ d,a d*|U j d|≤1/12 :=
    huxley_narrowed_sieve_frequency_scale hNr
      (by exact ⟨by exact_mod_cast (hm j hj).1,by exact_mod_cast (hm j hj).2⟩) hηp hζp hV
  have hx' i (hi : i∈S) d : x i d∈Icc (c d) (c d+D d) := by
    refine ⟨(hx i hi).1 d,?_⟩
    have hh := (hx i hi).2 d
    fin_cases d <;> norm_num [c,D,Matrix.cons_val_succ] <;> exact hh
  have hs := bourgain_four_dimensional_sixth_power_sieve S T w x U ha hD hw hx' hU
  change (∑ i∈S,‖∑ j∈T,w j*GafniTao.fordAdditiveCharacter (∑ d,U j d*x i d)‖)^12 ≤
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
  have hbound := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hscale hR) hCouter
  calc
    _ ≤ (S.card:ℝ)^10*K*(P.card:ℝ)*(C*η*ζ*(N:ℝ)^((9:ℝ)+ε)*B^12) :=
      hs.trans (mul_le_mul_of_nonneg_left hQ (by positivity))
    _ = ((S.card:ℝ)^10*(P.card:ℝ))*(K*(C*η*ζ*(N:ℝ)^((9:ℝ)+ε)*B^12)) := by ring
    _ ≤ ((S.card:ℝ)^10*(P.card:ℝ))*
        ((L*(N:ℝ)^3*Vscale/(η*ζ))*(C*η*ζ*(N:ℝ)^((9:ℝ)+ε)*B^12)) := hbound
    _ = _ := huxley_narrowed_sieve_final_scale hNp hηp hζp

private theorem huxley_completed_phase_normalize
    {M : ℕ} (hM : 0 < M) (x : Fin 4 → ℝ) (n : ℤ) (hn : 0 ≤ n) :
    GafniTao.fordAdditiveCharacter (∑ d,x d*
      (![(n:ℝ),(n:ℝ)^2,(n:ℝ)^((3:ℝ)/2),Real.sqrt (n:ℝ)] : Fin 4 → ℝ) d)=
    GafniTao.fordAdditiveCharacter (∑ d,
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
  simp only [GafniTao.fordAdditiveCharacter_add]
  have he1 : GafniTao.fordAdditiveCharacter (x 0*(n:ℝ))=
      GafniTao.fordAdditiveCharacter ((n:ℝ)*Int.fract (x 0)) := by
    simpa only [mul_comm] using (sargos_character_integer_fract n (x 0)).symm
  have he2 : GafniTao.fordAdditiveCharacter (x 1*(n:ℝ)^2)=
      GafniTao.fordAdditiveCharacter ((n:ℝ)^2*Int.fract (x 1)) := by
    have hh := sargos_character_integer_fract (n^2) (x 1)
    push_cast at hh
    simpa only [mul_comm] using hh.symm
  change GafniTao.fordAdditiveCharacter (x 0*(n:ℝ))*
      (GafniTao.fordAdditiveCharacter (x 1*(n:ℝ)^2)*
        (GafniTao.fordAdditiveCharacter (x 2*(n:ℝ)^((3:ℝ)/2))*
          GafniTao.fordAdditiveCharacter (x 3*Real.sqrt (n:ℝ))))=
    GafniTao.fordAdditiveCharacter ((n:ℝ)*Int.fract (x 0))*
      (GafniTao.fordAdditiveCharacter ((n:ℝ)^2*Int.fract (x 1))*
        (GafniTao.fordAdditiveCharacter (x 2*(n:ℝ)^((3:ℝ)/2))*
          GafniTao.fordAdditiveCharacter (x 3*Real.sqrt (n:ℝ))))
  rw [he1,he2]


public  theorem huxley_completed_narrowed_source_sieve {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (M : ℕ) [NeZero M] (Vscale : ℝ), 1≤Vscale → ∀ (ι : Type huxleyNarrowV) (S : Finset ι)
      (x : ι → Fin 4 → ℝ),
      (∀ i∈S, |x i 2| ≤ Real.sqrt M ∧ |x i 3| ≤ Real.sqrt M) →
      let y := fun i => (![Int.fract (x i 0),Int.fract (x i 1),
        x i 2/Real.sqrt M,x i 3/Real.sqrt M] : Fin 4 → ℝ)
      let a : Fin 4 → ℝ :=
        ![1/(12*(M:ℝ)),1/(12*(M:ℝ)^2*Vscale),(1/(M:ℝ)^2)/12,(1/(M:ℝ))/12]
      ∀ k : ZMod M,
      (∑ i∈S, ‖∑ j : ZMod M,ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x i d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
        C*Vscale*(M:ℝ)^((12:ℝ)+ε)*(S.card:ℝ)^10*
          (((S ×ˢ S).filter (fun ij => ∀ d,|y ij.1 d-y ij.2 d| ≤ 2*a d)).card:ℝ) := by
  classical
  obtain ⟨C,hC,hsource⟩ := exists_huxleySourceCurve_narrowed_double_sieve.{huxleyNarrowV} hε
  refine ⟨C,hC,?_⟩
  intro M inst Vscale hV ι S x hx y a k
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hMr : (0:ℝ) < M := Nat.cast_pos.mpr hM
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hsqrt : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMr
  let T : Finset (ULift.{huxleyNarrowV} (ZMod M)) := Finset.univ
  let m := fun j : ULift.{huxleyNarrowV} (ZMod M) => (j.down.val:ℤ)+1
  let w := fun j : ULift.{huxleyNarrowV} (ZMod M) => ZMod.stdAddChar (-(j.down*k))
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
    Vscale hη hζ hV ι (ULift.{huxleyNarrowV} (ZMod M)) S T w m y 1 (by norm_num) hm
    (fun j _ => (sargos_stdAddChar_norm _).le) hmass hy
  simp only [one_div_one_div,one_pow,mul_one] at hh
  let U := fun j : ULift.{huxleyNarrowV} (ZMod M) =>
    (![(m j:ℝ),(m j:ℝ)^2,(M:ℝ)^2*((m j:ℝ)/M)^((3:ℝ)/2),
      (M:ℝ)*Real.sqrt ((m j:ℝ)/M)] : Fin 4 → ℝ)
  have he :
      (∑ i∈S, ‖∑ j : ZMod M,ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x i d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)=
      ∑ i∈S, ‖∑ j∈T,w j*GafniTao.fordAdditiveCharacter (∑ d,U j d*y i d)‖ := by
    apply Finset.sum_congr rfl
    intro i _hi
    congr 1
    calc
      _ = ∑ j : ULift.{huxleyNarrowV} (ZMod M),w j*
          GafniTao.fordAdditiveCharacter (∑ d,x i d*
            (![(m j:ℝ),(m j:ℝ)^2,(m j:ℝ)^((3:ℝ)/2),
              Real.sqrt (m j:ℝ)] : Fin 4 → ℝ) d) := by
        apply Fintype.sum_equiv Equiv.ulift.symm
        intro j
        simp [w,m,Equiv.ulift]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _hj
        congr 1
        exact huxley_completed_phase_normalize hM (x i) (m j) (by dsimp only [m]; omega)
  rw [he]
  exact hh


private theorem huxley_dual_physical_scale {μ q N : ℝ}
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

public  theorem huxley_actual_dual_source_box
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
  obtain ⟨hA,hK⟩ := huxley_dual_physical_scale hμ hqr hNr hqNr hscale
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


                                                                      
                                                                         
                                                                          
private theorem exists_huxley_cubic_dual_narrowed_source_sieve {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (M : ℕ) [NeZero M] (Vscale : ℝ), 1≤Vscale → ∀ (ι : Type huxleyNarrowV) (S : Finset ι)
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
        ![1/(12*(M:ℝ)),1/(12*(M:ℝ)^2*Vscale),(1/(M:ℝ)^2)/12,(1/(M:ℝ))/12]
      ∀ k : ZMod M,
      (∑ i∈S, ∑ p : Fin 2, ‖∑ j : ZMod M,ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x i p d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
        C*Vscale*(M:ℝ)^((12:ℝ)+ε)*(V.card:ℝ)^10*
          (((V ×ˢ V).filter (fun ij => ∀ d,|y ij.1 d-y ij.2 d| ≤ 2*a d)).card:ℝ) := by
  classical
  obtain ⟨C,hC,hsource⟩ := huxley_completed_narrowed_source_sieve.{huxleyNarrowV} hε
  refine ⟨C,hC,?_⟩
  intro M inst Vscale hV ι S q N r μ ℓ hscale hM b τ K x V y a k
  have hbox ip (hip : ip∈V) :
      |x ip.1 ip.2 2| ≤ Real.sqrt M ∧ |x ip.1 ip.2 3| ≤ Real.sqrt M := by
    have hi := (Finset.mem_product.mp hip).1
    have hd := hscale ip.1 hi
    exact huxley_actual_dual_source_box hd.1 hd.2.1 hd.2.2.1
      hd.2.2.2.1 hd.2.2.2.2 (hM ip.1 hi) (r ip.1) ip.2
  have hh := hsource M Vscale hV (ι × Fin 2) V (fun ip => x ip.1 ip.2) hbox k
  simpa only [V,Finset.sum_product] using hh

theorem exists_source_arc_fourier_narrowed_sieve_matrices {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (ι : Type huxleyNarrowV) [DecidableEq ι] (S : Finset ι)
    (f : ι → ℝ → ℝ) (z : ι → ℝ) (r : ι → ℚ) (v : ι → ℤ)
    (Q K₀ : ℕ) [NeZero K₀] (μ₀ U₀ : ℝ), 0 < μ₀ →
    (∀ i∈S, μ₀ ≤ iteratedDeriv 3 (f i) (round (z i))/6 ∧
      iteratedDeriv 3 (f i) (round (z i))/6 ≤ U₀) →
    (∀ i∈S, iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ)) →
    (∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den) →
    (∀ i∈S, ((r i).den:ℤ) ∣ (r i).num*v i-1) →
    ∀ (Nlen : ι → ℕ) (Vscale Nphys Rphys : ℝ),
    1 ≤ Vscale → 0 < Nphys →
    (Q:ℝ)*Nphys ≤ (K₀:ℝ)*Rphys^2 →
    (∀ i∈S, 1 ≤ Nlen i ∧ (r i).den ≤ Nlen i ∧
      1 ≤ (iteratedDeriv 3 (f i) (round (z i))/6)*((r i).den:ℝ)^2*Nlen i) →
    (∀ i∈S, 7*((iteratedDeriv 3 (f i) (round (z i))/6)*
      ((r i).den:ℝ)*(Nlen i:ℝ)^2) ≤ K₀) →
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
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2*Vscale),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    let P := (V ×ˢ V).filter (fun ij => ∀ d, |w ij.1 d-w ij.2 d| ≤ 2*radius d)
    let h := fun i => iteratedDeriv 2 (f i) (z i)/2
    let D := (Real.sqrt K₀/(9*(K₀:ℝ))+Real.sqrt K₀/(12*(K₀:ℝ)^2))*
      Real.sqrt (U₀*(Q:ℝ)^3)
    ∃ A : ((ι × Fin 2) × (ι × Fin 2)) → Fin 4 → ℤ,
      (∀ k : ZMod K₀,
        (∑ i∈S, ∑ p : Fin 2, ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
          GafniTao.fordAdditiveCharacter (∑ d,x i p d*
            (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
              Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
          C*Vscale*(K₀:ℝ)^((12:ℝ)+ε)*(V.card:ℝ)^10*(P.card:ℝ)) ∧
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
      (∀ ij∈P, |(A ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2*Vscale) ∧
        |(A ij 2:ℝ)| ≤ Rphys^4/(6*Nphys^2*Vscale)) := by
  classical
  obtain ⟨C,hC,hsieve⟩ := exists_huxley_cubic_dual_narrowed_source_sieve.{huxleyNarrowV} hε
  refine ⟨C,hC,?_⟩
  intro ι inst S f z r v Q K₀ instK μ₀ U₀ hμ₀ hμbounds hlevel hden hinv
    Nlen Vscale Nphys Rphys hV hNphys hmesh hminor hcomplete
    q μ ℓ b τ K x V w radius P h D
  have hsum := hsieve K₀ Vscale hV ι S q Nlen v μ ℓ
    (by
      intro i hi
      exact ⟨(r i).pos,(hminor i hi).1,(hminor i hi).2.1,
        hμ₀.trans_le (hμbounds i hi).1,(hminor i hi).2.2⟩) hcomplete
  let radius0 : Fin 4 → ℝ :=
    ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
  let P0 := (V ×ˢ V).filter (fun ij => ∀ d, |w ij.1 d-w ij.2 d| ≤ 2*radius0 d)
  have hKpos : (0:ℝ) < K₀ := by exact_mod_cast NeZero.pos K₀
  have hKone : (1:ℝ) ≤ K₀ := by exact_mod_cast (NeZero.pos K₀)
  have hVp : 0 < Vscale := zero_lt_one.trans_le hV
  have hrad d : radius d ≤ radius0 d := by
    fin_cases d
    · exact le_rfl
    · change 1/(12*(K₀:ℝ)^2*Vscale) ≤ 1/(12*(K₀:ℝ)^2)
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith only [mul_nonneg (show 0 ≤ 12*(K₀:ℝ)^2 by positivity)
        (sub_nonneg.mpr hV)]
    · exact le_rfl
    · exact le_rfl
  have hsub : P ⊆ P0 := by
    intro ij hij
    have hh := Finset.mem_filter.mp hij
    exact Finset.mem_filter.mpr ⟨hh.1,fun d =>
      (hh.2 d).trans (mul_le_mul_of_nonneg_left (hrad d) (by norm_num))⟩
  obtain ⟨A,hA⟩ := source_arc_fourier_cloud_matrices S f z r v Q K₀ μ₀ U₀
    hμ₀ hμbounds hlevel hden hinv
  change ∀ ij∈P0, _ at hA
  refine ⟨A,hsum,(fun ij hij => hA ij (hsub hij)),?_⟩
  intro ij hij
  have hp := Finset.mem_filter.mp hij
  have hi := (Finset.mem_product.mp (Finset.mem_product.mp hp.1).1).1
  have hj := (Finset.mem_product.mp (Finset.mem_product.mp hp.1).2).1
  let pr : Fin 2 → ℚ := ![r ij.1.1,r ij.2.1]
  let qi : Fin 2 → ℤ := ![(q ij.1.1:ℤ),(q ij.2.1:ℤ)]
  let ei : Fin 2 → ℤ := ![(r ij.1.1).num,(r ij.2.1).num]
  let vi : Fin 2 → ℤ := ![v ij.1.1,v ij.2.1]
  have hcast d : (ei d:ℝ)/qi d=(pr d:ℝ) := by
    fin_cases d
    · change ((r ij.1.1).num:ℝ)/(r ij.1.1).den=(r ij.1.1:ℝ)
      exact (Rat.cast_def _).symm
    · change ((r ij.2.1).num:ℝ)/(r ij.2.1).den=(r ij.2.1:ℝ)
      exact (Rat.cast_def _).symm
  have hband : ∀ d, (qi d:ℝ) ≤ (Q:ℝ) ∧ (Q:ℝ) ≤ 2*(qi d:ℝ) := by
    intro d
    fin_cases d
    · change ((r ij.1.1).den:ℝ) ≤ Q ∧ (Q:ℝ) ≤ 2*((r ij.1.1).den:ℝ)
      exact ⟨by exact_mod_cast (hden _ hi).1,by exact_mod_cast (hden _ hi).2⟩
    · change ((r ij.2.1).den:ℝ) ≤ Q ∧ (Q:ℝ) ≤ 2*((r ij.2.1).den:ℝ)
      exact ⟨by exact_mod_cast (hden _ hj).1,by exact_mod_cast (hden _ hj).2⟩
  obtain ⟨hdet,ht,_htlo,_hthi,hmap,hgamma,_hrest⟩ := hA ij (hsub hij)
  have ht' : (A ij 2:ℝ)*((ei 0:ℝ)/qi 0)+A ij 3=(qi 1:ℝ)/qi 0 := by
    rw [hcast]
    change (A ij 2:ℝ)*(r ij.1.1:ℝ)+A ij 3=
      ((r ij.2.1).den:ℝ)/(r ij.1.1).den
    simpa only [hlevel _ hi] using ht
  have hmap' : ((A ij 0:ℝ)*((ei 0:ℝ)/qi 0)+A ij 1)/
      ((A ij 2:ℝ)*((ei 0:ℝ)/qi 0)+A ij 3)=(ei 1:ℝ)/qi 1 := by
    rw [hcast,hcast]
    change ((A ij 0:ℝ)*(r ij.1.1:ℝ)+A ij 1)/
      ((A ij 2:ℝ)*(r ij.1.1:ℝ)+A ij 3)=(r ij.2.1:ℝ)
    simpa only [hlevel _ hi,hlevel _ hj] using hmap
  have hnear : |Int.fract (-(vi 0:ℝ)/qi 0)-Int.fract (-(vi 1:ℝ)/qi 1)| ≤
      1/(6*(K₀:ℝ)^2*Vscale) := by
    have hn := hp.2 (1:Fin 4)
    change |Int.fract (-(vi 0:ℝ)/qi 0)-Int.fract (-(vi 1:ℝ)/qi 1)| ≤
      2*(1/(12*(K₀:ℝ)^2*Vscale)) at hn
    convert hn using 1
    field_simp
    norm_num
  exact fourier_matrix_narrowed_coordinate_entry_bound qi ei vi (A ij)
    (by
      intro d
      fin_cases d
      · change (0:ℤ) < (r ij.1.1).den
        exact_mod_cast (r ij.1.1).pos
      · change (0:ℤ) < (r ij.2.1).den
        exact_mod_cast (r ij.2.1).pos)
    hKone hV hNphys hmesh hband
    (by intro d; fin_cases d; exact hinv _ hi; exact hinv _ hj)
    hdet ht' hmap' hgamma hnear

private theorem huxley_narrowing_balanced_scale
    {U V a b : ℝ} (hU : 0 < U) (hV : V=U^((3:ℝ)/2)) :
    V*(a/V^((5:ℝ)/3)+b/(U*V))=(a+b)/U := by
  subst V
  have hUp : 0 < U^((3:ℝ)/2) := Real.rpow_pos_of_pos hU _
  have he : (U^((3:ℝ)/2))^((5:ℝ)/3)=U*U^((3:ℝ)/2) := by
    rw [←Real.rpow_mul hU.le]
    rw [show ((3:ℝ)/2)*(5/3)=1+3/2 by norm_num,Real.rpow_add hU,Real.rpow_one]
  rw [he]
  field_simp

private theorem huxley_narrowing_balanced_mass
    {mass K a b U V : ℝ} (hU : 0 < U) (hV : V=U^((3:ℝ)/2))
    (h : mass ≤ K*(a/V^((5:ℝ)/3)+b/(U*V))) :
    V*mass ≤ K*(a+b)/U := by
  have hVp : 0 < V := by rw [hV]; exact Real.rpow_pos_of_pos hU _
  calc
    V*mass ≤ V*(K*(a/V^((5:ℝ)/3)+b/(U*V))) :=
      mul_le_mul_of_nonneg_left h hVp.le
    _ = K*(V*(a/V^((5:ℝ)/3)+b/(U*V))) := by ring
    _ = K*((a+b)/U) := by rw [huxley_narrowing_balanced_scale hU hV]
    _ = _ := by ring

private theorem huxley_reference_reciprocal_scale
    {N Q B U : ℝ} (hN : 0 < N) (hQ : 0 < Q) (hB : 0 < B)
    (hU : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    1/U ≤ 2*B*(Q/N)^((2:ℝ)/3) := by
  have hp : 0 < (N/Q)^((2:ℝ)/3) :=
    Real.rpow_pos_of_pos (div_pos hN hQ) _
  have hh := one_div_le_one_div_of_le (div_pos hp (by positivity)) hU
  apply hh.trans_eq
  rw [one_div_div,div_eq_mul_inv,←Real.inv_rpow (div_pos hN hQ).le]
  rw [inv_div]

                                                                      
                                                                             
                                                               
theorem physicalModelPhase_actual_fourier_original_pair_mass
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2))) (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ) (Bmajor Cmajor : ℕ)
    (Q K₀ : ℕ) [NeZero K₀]
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ)
    (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2)
    (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M R base Bcut lambda Uband θ V : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℝ}
    (hbase : ∀ ij∈P, base ≤ za ij.1.1)
    (hxa : ∀ ij∈P, x ij 0=za ij.1.1)
    (hxb : ∀ ij∈P, x ij 1=zb ij.2.1)
    (hgapMem : ∀ ij∈P, gap ij∈Gaps)
    (hgeometryA : ∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ))
    (hgeometryB : ∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ))
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T)
    (hM : 0 < M)
    (hN : 0 < (N:ℝ))
    (hR : 1 ≤ R)
    (hRM : R ≤ M)
    (hQ : 0 < Q)
    (hscale : T*(N:ℝ)*R^2=M^3)
    (hmesh : (Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i)
    (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ ij∈P, ∀ i, x ij i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ ij∈P, ∀ i, (rat ij i).den ≤ Q ∧ Q ≤ 2*(rat ij i).den)
    (hlambda : 0 < lambda)
    (hUband : 0 ≤ Uband)
    (hθ : 0 < θ)
    (hθmax : θ ≤ 1/24)
    (hcurv : ∀ ij∈P, ∀ i, lambda ≤ |(rat ij i:ℝ)| ∧ |(rat ij i:ℝ)| ≤ Uband)
    (hinv : ∀ ij∈P, ∀ i, ((rat ij i).den:ℤ) ∣ (rat ij i).num*vinv ij i-1)
    (hchart : ∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1)
    (horientation : ∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2))
    (hBcut : 0 < Bcut)
    (hs : ∀ ab∈Gaps, (s ab) ≠ 0)
    (hrefSet : ∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs)
    (hparentSet : ∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hwideL : ∀ ij∈P, ∀ i, x ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ ij∈P, ∀ i, x ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2)
    (hreferenceDen : ∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ))
    (hgapWidth : ∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2))
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : (N:ℝ)^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ ij∈P, (rat ij 0:ℝ)∈Icc (gap ij).1 (gap ij).2)
    (hc : ∀ ij∈P, Mat ij 2 ≠ 0)
    (hlarge : ∀ ij∈P, 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat ij 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (haction : ∀ ij∈P, 8*Uband ≤ |(Mat ij 2:ℝ)| *lambda^2)
    (hV : 1 ≤ V)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun ij i => (⌊((rat ij i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat ij i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ij∈P, sourceColor ij 0=sourceColor ij 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ij∈P, ∀ i, iteratedDeriv 2 (f i) (x ij i)/2=(rat ij i:ℝ)) →
    let q := fun ij i => (rat ij i).den
    let mu := fun ij i => iteratedDeriv 3 (f i) (round (x ij i))/6
    let ell := fun ij i => deriv (f i) (round (x ij i))
    let b := fun ij i => (⌊(q ij i:ℝ)*ell ij i⌋+(parity ij i:ℕ) : ℤ)
    let cround := fun ij i => round ((q ij i:ℝ)*ell ij i)
    let tau := fun ij i => ((b ij i:ℝ)-(q ij i:ℝ)*ell ij i)/2
    let dual := fun ij i => -2*mu ij i*(Real.sqrt (2/(3*mu ij i*(q ij i:ℝ))))^3
    let cloud := fun ij i => (![Int.fract (-(vinv ij i:ℝ)*b ij i/q ij i),
      Int.fract (-(vinv ij i:ℝ)/q ij i),dual ij i/Real.sqrt K₀,
      (3*dual ij i*tau ij i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ij∈P, b ij 0-cround ij 0=b ij 1-cround ij 1) →
    (∀ ij∈P, ∀ a, |cloud ij 0 a-cloud ij 1 a| ≤ 2*radius a) →
    (∀ ij∈P,
      |cloud ij 0 1-cloud ij 1 1| ≤ 1/(6*(K₀:ℝ)^2*V)) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 →
    R ≤ (N:ℝ) →
    (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
    (∀ ij∈P, (Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat ij 0:ℝ)*(rat ij 0:ℝ)+Mat ij 1)/
      ((Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3)=(rat ij 1:ℝ)) →
    (∀ ij∈P, |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ ij∈P, ∀ i, x ij i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, x ij i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, |(anchor ij:ℝ)-(rat ij 0:ℝ)| ≤ ε) →
    (∀ ij∈P, 256*((anchor ij).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ij∈P, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor ij).den) →
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
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Gcap := R^4/(6*(N:ℝ)^2*V)
    let Kstar := 2*Cfirst*R^4/(Lunit^3*(N:ℝ)^2)
    let Aweight := 4*(m0:ℝ)
    let Bweight := 4*(m0:ℝ)*Cpack*R^4/(Lunit^2*(N:ℝ)^2*(Uref:ℝ))+
      (m0:ℝ)*Cgap*R^4/((N:ℝ)^2*(Uref:ℝ))+2*(m0:ℝ)*Gcap
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Kmass := 60*588*(m0:ℝ)*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)
    ((P.card:ℝ) ≤
      60*588*(Uband/lambda)^2*Uband^2*Gcap*
        (Aweight*Kstar^((3:ℝ)⁻¹)*Gcap^((2:ℝ)/3)+Bweight)) ∧
    (P.card:ℝ) ≤
      60*588*(m0:ℝ)*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
        (Cmain/V^((5:ℝ)/3)+Ctail/((Uref:ℝ)*V)) ∧
    (V=(Uref:ℝ)^((3:ℝ)/2) →
      V*(P.card:ℝ) ≤ Kmass*(Cmain+Ctail)/(Uref:ℝ)) ∧
    (V=(Uref:ℝ)^((3:ℝ)/2) →
      ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Uref:ℝ) →
      V*(P.card:ℝ) ≤ 2*Bselect*Kmass*(Cmain+Ctail)*
        ((Q:ℝ)/(N:ℝ))^((2:ℝ)/3)) := by
  classical
  intro Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear hnearNarrow
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor Lunit Gamma Cthird Cpack Cfirst Cgap
    Gcap Kstar Aweight Bweight Cmain Ctail Kmass
  have hNnat : 0 < N := by exact_mod_cast hN
  have hF₂ i := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl
  have hz ij (hij : ij∈P) : zb ij.2.1∈Ioo 0 (W 1) := by
    have hh := hx ij hij 1
    rw [hxb ij hij] at hh
    constructor <;> linarith only [hh.1,hh.2]
  have hmodelMap ij (hij : ij∈P) :
      ((Mat ij 0:ℝ)*(iteratedDeriv 2 (f 0) (za ij.1.1)/2)+Mat ij 1)/
      ((Mat ij 2:ℝ)*(iteratedDeriv 2 (f 0) (za ij.1.1)/2)+Mat ij 3)=
        iteratedDeriv 2 (f 1) (zb ij.2.1)/2 := by
    rw [←hxa ij hij,←hxb ij hij,hlevel ij hij 0,hlevel ij hij 1]
    exact hMatmap ij hij
  let block := fun ij : (ℤ × Fin 2) × (ℤ × Fin 2) =>
    ⌊(za ij.1.1-base)/(N:ℝ)⌋.toNat
  let S := fun B ab => (P.filter (fun ij => Mat ij=B ∧ gap ij=ab)).image block
  let Matrices := P.image Mat
  obtain ⟨pick,hpick,hpairNat⟩ := physicalModelPhase_reference_matrix_window_selection
    P Mat gap F A W za zb AlenA AlenB N Za Zb base hσ hδ hF₂ hT hM hNnat
    hA hW hbase hz hgeometryA hgeometryB hmodelMap
  have hdata B (hB : B∈Matrices) ab (_hab : ab∈Gaps) j (hj : j∈S B ab) :
      pick B ab j∈P ∧ Mat (pick B ab j)=B ∧ gap (pick B ab j)=ab ∧
        block (pick B ab j)=j ∧
        za (pick B ab j).1.1∈Icc (base+(N:ℝ)*j) (base+(N:ℝ)*((j:ℝ)+1)) := by
    obtain ⟨ij,hij,_he⟩ := Finset.mem_image.mp hj
    have hh := Finset.mem_filter.mp hij
    have hab' : ab∈P.image gap := Finset.mem_image.mpr ⟨ij,hh.1,hh.2.2⟩
    exact hpick B hB ab hab' j hj
  have hgapSub : P.image gap ⊆ Gaps := by
    intro ab hab
    obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hab
    exact hgapMem ij hij
  have hpairNat' : P.card ≤ 60*∑ B∈Matrices, ∑ ab∈Gaps, (S B ab).card := by
    apply hpairNat.trans
    apply Nat.mul_le_mul_left 60
    apply Finset.sum_le_sum
    intro B _hB
    exact Finset.sum_le_sum_of_subset_of_nonneg hgapSub (fun _ _ _ => Nat.zero_le _)
  have hpair : (P.card:ℝ) ≤ 60*(∑ B∈Matrices, ∑ ab∈Gaps, ((S B ab).card:ℝ)) := by
    exact_mod_cast hpairNat'
  have hmass :
      ((∑ B∈Matrices, ∑ ab∈Gaps, ((S B ab).card:ℝ)) ≤
        588*(Uband/lambda)^2*Uband^2*Gcap*
          (Aweight*Kstar^((3:ℝ)⁻¹)*Gcap^((2:ℝ)/3)+Bweight)) ∧
      (∑ B∈Matrices, ∑ ab∈Gaps, ((S B ab).card:ℝ)) ≤
        588*(m0:ℝ)*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
          (Cmain/V^((5:ℝ)/3)+Ctail/((Uref:ℝ)*V)) := by
    exact physicalModelPhase_actual_fourier_charted_matrix_source_mass
      Uref Refs Gaps (Bselect:=Bselect) Matrices Bmajor Cmajor S Q K₀
      (fun B ab j => rat (pick B ab j))
      (fun B ab j => vinv (pick B ab j))
      (fun B ab j => parity (pick B ab j))
      (fun B ab j => anchor (pick B ab j)) e r v s
      (x:=fun B ab j => x (pick B ab j))
      hσ
      hδ
      hF
      hT
      hM
      hN
      hR
      hRM
      hQ
      hscale
      hmesh
      hA
      hW
      (by
        intro B hB ab hab j hj
        exact hx _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        have hp := hdata B hB ab hab j hj
        change x (pick B ab j) 0∈_
        rw [hxa _ hp.1]
        exact hp.2.2.2.2)
      (by
        intro B hB ab hab j hj
        exact hden _ (hdata B hB ab hab j hj).1)
      hlambda
      hUband
      hθ
      hθmax
      (by
        intro B hB ab hab j hj
        exact hcurv _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        exact hinv _ (hdata B hB ab hab j hj).1)
      hchart
      horientation
      hBcut
      hs
      hrefSet
      hparentSet
      hsep
      (by
        intro B hB ab hab j hj
        exact hwideL _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        exact hwideU _ (hdata B hB ab hab j hj).1)
      hUref
      hBselectSize
      hcutMargin
      hselectedWrap
      hreferenceDen
      hgapWidth
      hRQ
      hselectedUpper
      hscaleTen
      (by
        intro B hB ab hab j hj
        have hp := hdata B hB ab hab j hj
        have hh := hfamilyGap _ hp.1
        rw [hp.2.2.1] at hh
        exact hh)
      (by
        intro B hB
        obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hB
        exact hc ij hij)
      (by
        intro B hB
        obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hB
        exact hlarge ij hij)
      (by
        intro B hB
        obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hB
        exact haction ij hij)
      hV
      hgap
      (by
        intro B hB ab hab j hj
        exact hsourceColor _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        exact hlevel _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        exact hcolor _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        exact hnear _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        exact hnearNarrow _ (hdata B hB ab hab j hj).1)
      hsmall
      hNR
      hRN
      hNcube
      hminscale
      (by
        intro B hB
        obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hB
        exact hMatdet ij hij)
      (by
        intro B hB ab hab j hj
        have hp := hdata B hB ab hab j hj
        have hh := hMatt _ hp.1
        rw [hp.2.1] at hh
        exact hh)
      (by
        intro B hB ab hab j hj
        have hp := hdata B hB ab hab j hj
        have hh := hMatmap _ hp.1
        rw [hp.2.1] at hh
        exact hh)
      (by
        intro B hB
        obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hB
        exact hMatgamma ij hij)
      hNtwo
      (by
        intro B hB ab hab j hj
        exact hL _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        exact hU _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        exact hanchor _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        exact hcut _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        exact hcount _ (hdata B hB ab hab j hj).1)
      hsize
      hD
      hΔ
      hBsize
      hBmajor
      hCmajor
  have hraw : (P.card:ℝ) ≤ 60*588*(Uband/lambda)^2*Uband^2*Gcap*
      (Aweight*Kstar^((3:ℝ)⁻¹)*Gcap^((2:ℝ)/3)+Bweight) := by
    simpa only [mul_assoc] using hpair.trans
      (mul_le_mul_of_nonneg_left hmass.1 (by norm_num : (0:ℝ) ≤ 60))
  have hnorm : (P.card:ℝ) ≤ Kmass*
      (Cmain/V^((5:ℝ)/3)+Ctail/((Uref:ℝ)*V)) := by
    simpa only [Kmass,mul_assoc] using hpair.trans
      (mul_le_mul_of_nonneg_left hmass.2 (by norm_num : (0:ℝ) ≤ 60))
  have hUp : (0:ℝ) < Uref := by exact_mod_cast (show 0 < Uref by omega)
  have hbalanced (hv : V=(Uref:ℝ)^((3:ℝ)/2)) :
      V*(P.card:ℝ) ≤ Kmass*(Cmain+Ctail)/(Uref:ℝ) :=
    huxley_narrowing_balanced_mass hUp hv hnorm
  refine ⟨hraw,hnorm,hbalanced,?_⟩
  intro hv hUlo
  have hκ := modelPhaseThirdLower_pos hσ
  have hBsel : 0 < Bselect := (by positivity : (0:ℝ) < 2+168/modelPhaseThirdLower σ).trans_le hBselectSize
  have hinvU := huxley_reference_reciprocal_scale hN
    (by exact_mod_cast hQ) hBsel hUlo
  have hVm : 0 ≤ V*(P.card:ℝ) :=
    mul_nonneg (zero_le_one.trans hV) (Nat.cast_nonneg _)
  have hcoef : 0 ≤ Kmass*(Cmain+Ctail) :=
    (mul_nonneg hVm hUp.le).trans ((le_div_iff₀ hUp).mp (hbalanced hv))
  calc
    V*(P.card:ℝ) ≤ Kmass*(Cmain+Ctail)/(Uref:ℝ) := hbalanced hv
    _ = Kmass*(Cmain+Ctail)*(1/(Uref:ℝ)) := by ring
    _ ≤ Kmass*(Cmain+Ctail)*(2*Bselect*((Q:ℝ)/(N:ℝ))^((2:ℝ)/3)) :=
      mul_le_mul_of_nonneg_left hinvU hcoef
    _ = _ := by ring

public  theorem eventually_reference_chart_majorants
    {Ch Cc ε : ℝ} (hCh : 1 ≤ Ch) (hCc : 1 ≤ Cc) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in Filter.atTop,
    let Bmajor := 6+216*(⌊Real.logb 2 ((Ch*T^3)^2)⌋₊+1)
    let Cmajor := ⌊Real.logb (5/4) (Cc*T)⌋₊+1
    ((6+Cmajor*(105+544*Bmajor):ℕ):ℝ) ≤ T^ε := by
  let Kb : ℝ := 222+1728/Real.log 2
  let Kc : ℝ := 1+2/Real.log (5/4)
  let K : ℝ := 6+Kc*(105+544*Kb)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlc : 0 < Real.log (5/4) := Real.log_pos (by norm_num)
  have hKb : 0 ≤ Kb := by dsimp only [Kb]; positivity
  have hKc : 0 ≤ Kc := by dsimp only [Kc]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  filter_upwards [eventually_const_log_pow_le_rpow K hK 2 hε,
    Filter.eventually_ge_atTop Ch, Filter.eventually_ge_atTop Cc,
    Filter.eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hsmall hh hc hT hlogT
  dsimp only
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hheight1 : 1 ≤ Ch*T^3 := one_le_mul_of_one_le_of_one_le hCh (one_le_pow₀ hT)
  have hheight : (Ch*T^3)^2 ≤ T^8 := by
    calc
      _ ≤ (T*T^3)^2 := pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_right hh (by positivity)) 2
      _ = _ := by ring
  have hlogh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (by positivity : 0 < (Ch*T^3)^2) hheight
  rw [Real.logb_pow 2 T 8] at hlogh
  have hfloorh := Nat.floor_le (Real.logb_nonneg (by norm_num : (1:ℝ)<2)
    (one_le_pow₀ hheight1 : 1 ≤ (Ch*T^3)^2))
  have hB : ((6+216*(⌊Real.logb 2 ((Ch*T^3)^2)⌋₊+1):ℕ):ℝ) ≤ Kb*Real.log T := by
    have he : Kb*Real.log T=222*Real.log T+216*(8*Real.logb 2 T) := by
      dsimp only [Kb,Real.logb]
      ring
    rw [he]
    push_cast
    norm_num only [Nat.cast_ofNat] at hlogh
    linarith only [hfloorh,hlogh,hlogT]
  have hchart1 : 1 ≤ Cc*T := one_le_mul_of_one_le_of_one_le hCc hT
  have hchart : Cc*T ≤ T^2 := by nlinarith only [mul_le_mul_of_nonneg_right hc hTp.le]
  have hlogc := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<5/4)
    (zero_lt_one.trans_le hchart1) hchart
  rw [Real.logb_pow] at hlogc
  have hfloorc := Nat.floor_le (Real.logb_nonneg (by norm_num : (1:ℝ)<5/4) hchart1)
  have hC : ((⌊Real.logb (5/4) (Cc*T)⌋₊+1:ℕ):ℝ) ≤ Kc*Real.log T := by
    have he : Kc*Real.log T=Real.log T+2*Real.logb (5/4) T := by
      dsimp only [Kc,Real.logb]
      ring
    rw [he]
    push_cast
    norm_num only [Nat.cast_ofNat] at hlogc
    linarith only [hfloorc,hlogc,hlogT]
  have hinner : 105+544*((6+216*(⌊Real.logb 2 ((Ch*T^3)^2)⌋₊+1):ℕ):ℝ) ≤
      (105+544*Kb)*Real.log T := by linarith only [hB,hlogT]
  have hmul := mul_le_mul hC hinner (by positivity) (mul_nonneg hKc (by linarith only [hlogT]))
  have hlogsq : 1 ≤ (Real.log T)^2 := one_le_pow₀ hlogT
  have hcost : ((6+(⌊Real.logb (5/4) (Cc*T)⌋₊+1)*
      (105+544*(6+216*(⌊Real.logb 2 ((Ch*T^3)^2)⌋₊+1))):ℕ):ℝ) ≤ K*(Real.log T)^2 := by
    push_cast
    dsimp only [K]
    push_cast at hmul
    nlinarith only [hmul,hlogsq]
  exact hcost.trans hsmall

public  theorem physical_reference_chart_ratio
    {κ Cp R U d : ℝ} (hκ : 0 < κ) (hCp : 0 < Cp+2) (hR : 0 < R)
    (hd : d ≤ 7*U/(2*R^2)) :
    d/(12*(κ/(16*(Cp+2)*R^2))) ≤ ((14:ℝ)/3)*(Cp+2)/κ*U := by
  have hh := div_le_div_of_nonneg_right hd
    (by positivity : 0 ≤ 12*(κ/(16*(Cp+2)*R^2)))
  apply hh.trans_eq
  field_simp
  ring

private theorem physical_reference_radius_le_source
    {T M N R Q : ℝ} (hT : 0 < T) (hM : 0 < M) (hR : 1 ≤ R)
    (hRQ : R ≤ Q) (hQN : Q ≤ N) (hNM : N^2 ≤ M)
    (hscale : T*N*R^2=M^3) : R^2 ≤ T := by
  have hN : 1 ≤ N := hR.trans (hRQ.trans hQN)
  have hNM' : N ≤ M := (by nlinarith only [hN] : N ≤ N^2).trans hNM
  have hR₂ : R^2 ≤ M :=
    (pow_le_pow_left₀ (zero_le_one.trans hR) (hRQ.trans hQN) 2).trans hNM
  have hprod : N*R^2 ≤ M^2 := by
    calc
      _ ≤ M*M := mul_le_mul hNM' hR₂ (sq_nonneg R) hM.le
      _ = _ := by ring
  have hMT : M ≤ T := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hM)).mp
    calc
      M*M^2 = M^3 := by ring
      _ = T*(N*R^2) := by nlinarith only [hscale]
      _ ≤ T*M^2 := mul_le_mul_of_nonneg_left hprod hT.le
  exact hR₂.trans hMT

                                                                     
                                                                      
                                                                             
public  theorem eventually_physical_reference_chart_budgets
    {σ Jref εloss : ℝ} (hσ : 0 < σ) (hJref : 0 ≤ Jref) (hεloss : 0 < εloss) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀
    (Gaps : Finset (ℝ × ℝ)) (e r v s : ℝ × ℝ → ℤ) (Q Uref : ℕ)
    {δ M N R : ℝ},
    0 ≤ δ → δ ≤ 1 → 0 < T → 0 < M → 1 ≤ R →
    R ≤ (Q:ℝ) → (Q:ℝ) ≤ N → N^2 ≤ M →
    1 ≤ Uref → (Uref:ℝ) ≤ R^2 → T*N*R^2=M^3 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((v ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, ab.1 < ab.2 ∧ ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun ab => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun ab => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let εchart := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    ∃ Bmajor Cmajor : ℕ,
      (∀ ab∈Gaps, 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1) ≤ Bmajor) ∧
      (∀ ab∈Gaps, ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*εchart))⌋₊+1 ≤ Cmajor) ∧
      ((6+Cmajor*(105+544*Bmajor):ℕ):ℝ) ≤ T^εloss := by
  let Jv := modelPhaseJetCoefficient σ 1+1
  let Ch := 1+4*(3*Jref/(2*σ)+1+Jv/2)
  let κ := modelPhaseThirdLower σ
  let Cp := σ*(σ+1)+1
  let Cc := 1+((14:ℝ)/3)*(Cp+2)/κ
  have hJv : 0 ≤ Jv := add_nonneg (modelPhaseJetCoefficient_nonneg σ 1) zero_le_one
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCp : 0 < Cp+2 := by dsimp only [Cp]; positivity
  have hCh : 1 ≤ Ch := by dsimp only [Ch]; exact le_add_of_nonneg_right (by positivity)
  have hCc : 1 ≤ Cc := by dsimp only [Cc]; exact le_add_of_nonneg_right (by positivity)
  filter_upwards [eventually_reference_chart_majorants hCh hCc hεloss,
    Filter.eventually_ge_atTop (1:ℝ)] with T hmajor hT1
  intro Gaps e r v s Q Uref δ M N R hδ₀ hδmax hT hM hR hRQ hQN hNM
    hU hUR hscale hr hs he hv hgap Vheight P₁ P₂ εchart
  let Bmajor := 6+216*(⌊Real.logb 2 ((Ch*T^3)^2)⌋₊+1)
  let Cmajor := ⌊Real.logb (5/4) (Cc*T)⌋₊+1
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hUr : (1:ℝ) ≤ Uref := by exact_mod_cast hU
  have hV₀ : 0 ≤ Vheight := div_nonneg
    (mul_nonneg hT.le (add_nonneg (modelPhaseJetCoefficient_nonneg σ 1) hδ₀)) (by positivity)
  have hVmax : Vheight ≤ Jv*T/(2*M^2) := by
    dsimp only [Vheight,Jv]
    rw [mul_comm (modelPhaseJetCoefficient σ 1+1) T]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hδmax) hT.le) (by positivity)
  have hheight ab (hab : ab∈Gaps) :=
    source_reference_seed_height_polynomial hσ hJref hJv hT hM hR hRQ hQN hNM
      hUr hscale hV₀ hVmax (hr ab hab) (hs ab hab) (he ab hab) (hv ab hab)
  have hP₁ ab : 1 ≤ P₁ ab := le_add_of_nonneg_right
    (mul_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) hV₀)) (Nat.cast_nonneg Q))
  have hP₂ ab : 1 ≤ P₂ ab := le_add_of_nonneg_right
    (mul_nonneg (add_nonneg (mul_nonneg (abs_nonneg _) hV₀) (abs_nonneg _)) (Nat.cast_nonneg Q))
  have hRT := physical_reference_radius_le_source hT hM hR hRQ hQN hNM hscale
  refine ⟨Bmajor,Cmajor,?_,?_,hmajor⟩
  · intro ab hab
    apply Nat.add_le_add_left
    apply Nat.mul_le_mul_left
    apply Nat.add_le_add_right
    apply Nat.floor_mono
    apply Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
      (mul_pos (zero_lt_one.trans_le (hP₁ ab)) (zero_lt_one.trans_le (hP₂ ab)))
    calc
      P₁ ab*P₂ ab ≤ (Ch*T^3)*(Ch*T^3) :=
        mul_le_mul (hheight ab hab).2.2.1 (hheight ab hab).2.2.2
          (zero_le_one.trans (hP₂ ab)) (by positivity)
      _ = _ := by ring
  · intro ab hab
    have hε : 0 < εchart := by change 0 < κ/(16*(Cp+2)*R^2); positivity
    have hratio := physical_reference_chart_ratio hκ hCp hRp (hgap ab hab).2
    have hratio' : (ab.2-ab.1)/(12*εchart) ≤ Cc*T := by
      apply hratio.trans
      calc
        ((14:ℝ)/3)*(Cp+2)/κ*(Uref:ℝ) ≤ ((14:ℝ)/3)*(Cp+2)/κ*T :=
          mul_le_mul_of_nonneg_left (hUR.trans hRT) (by positivity)
        _ ≤ Cc*T := mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left zero_le_one) hT.le
    apply Nat.add_le_add_right
    apply Nat.floor_mono
    exact Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<5/4)
      (div_pos (sub_pos.mpr (hgap ab hab).1) (by positivity)) hratio'


                                                                         
                                                                     
                                                                             
                                                    
theorem eventually_physicalModelPhase_actual_fourier_original_pair_mass
    {σ Jref εloss : ℝ} (hσ : 0 < σ) (hJref : 0 ≤ Jref) (hεloss : 0 < εloss) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2))) (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ)
    (Q K₀ : ℕ) [NeZero K₀]
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ)
    (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2)
    (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {δ M R base Bcut lambda Uband θ V : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℝ},
    (∀ ij∈P, base ≤ za ij.1.1) →
    (∀ ij∈P, x ij 0=za ij.1.1) →
    (∀ ij∈P, x ij 1=zb ij.2.1) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ)) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < (N:ℝ)) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*(N:ℝ)*R^2=M^3) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ ij∈P, ∀ i, x ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, (rat ij i).den ≤ Q ∧ Q ≤ 2*(rat ij i).den) →
    (0 < lambda) →
    (0 ≤ Uband) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ij∈P, ∀ i, lambda ≤ |(rat ij i:ℝ)| ∧ |(rat ij i:ℝ)| ≤ Uband) →
    (∀ ij∈P, ∀ i, ((rat ij i).den:ℤ) ∣ (rat ij i).num*vinv ij i-1) →
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) →
    (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ ij∈P, ∀ i, x ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, x ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ ij∈P, (rat ij 0:ℝ)∈Icc (gap ij).1 (gap ij).2) →
    (∀ ij∈P, Mat ij 2 ≠ 0) →
    (∀ ij∈P, 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat ij 2:ℝ)| *(modelPhaseThirdLower σ)^2*T) →
    (∀ ij∈P, 8*Uband ≤ |(Mat ij 2:ℝ)| *lambda^2) →
    (1 ≤ V) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((v ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let sourceColor := fun ij i => (⌊((rat ij i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat ij i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ij∈P, sourceColor ij 0=sourceColor ij 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ij∈P, ∀ i, iteratedDeriv 2 (f i) (x ij i)/2=(rat ij i:ℝ)) →
    let q := fun ij i => (rat ij i).den
    let mu := fun ij i => iteratedDeriv 3 (f i) (round (x ij i))/6
    let ell := fun ij i => deriv (f i) (round (x ij i))
    let b := fun ij i => (⌊(q ij i:ℝ)*ell ij i⌋+(parity ij i:ℕ) : ℤ)
    let cround := fun ij i => round ((q ij i:ℝ)*ell ij i)
    let tau := fun ij i => ((b ij i:ℝ)-(q ij i:ℝ)*ell ij i)/2
    let dual := fun ij i => -2*mu ij i*(Real.sqrt (2/(3*mu ij i*(q ij i:ℝ))))^3
    let cloud := fun ij i => (![Int.fract (-(vinv ij i:ℝ)*b ij i/q ij i),
      Int.fract (-(vinv ij i:ℝ)/q ij i),dual ij i/Real.sqrt K₀,
      (3*dual ij i*tau ij i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ij∈P, b ij 0-cround ij 0=b ij 1-cround ij 1) →
    (∀ ij∈P, ∀ a, |cloud ij 0 a-cloud ij 1 a| ≤ 2*radius a) →
    (∀ ij∈P,
      |cloud ij 0 1-cloud ij 1 1| ≤ 1/(6*(K₀:ℝ)^2*V)) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 →
    R ≤ (N:ℝ) →
    (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
    (∀ ij∈P, (Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat ij 0:ℝ)*(rat ij 0:ℝ)+Mat ij 1)/
      ((Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3)=(rat ij 1:ℝ)) →
    (∀ ij∈P, |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ ij∈P, ∀ i, x ij i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, x ij i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, |(anchor ij:ℝ)-(rat ij 0:ℝ)| ≤ ε) →
    (∀ ij∈P, 256*((anchor ij).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ij∈P, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor ij).den) →
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
    V=(Uref:ℝ)^((3:ℝ)/2) →
    ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Uref:ℝ) →
    V*(P.card:ℝ) ≤
      (2*Bselect*60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
        (Cmain+Ctail)*((Q:ℝ)/(N:ℝ))^((2:ℝ)/3))*T^εloss := by
  filter_upwards [eventually_physical_reference_chart_budgets hσ hJref hεloss] with T hbudgets
  intro Uref Refs Gaps Bselect P Mat gap Q K₀ _ N za zb AlenA AlenB Za Zb
    rat vinv parity anchor e r v s δ M R base Bcut lambda Uband θ V F A W x
    hbase hxa hxb hgapMem hgeometryA hgeometryB hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hc hlarge haction hV hgap
    hQN hNM hUR hrHeight hsHeight heHeight hvHeight
    ε sourceColor hsourceColor f hlevel q mu ell b cround tau dual cloud radius
    hcolor hnear hnearNarrow κ Cphys c J B hsmall hNR hRN hNcube hminscale
    hMatdet hMatt hMatmap hMatgamma H hNtwo hL hU hanchor hcut hcount
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird Cpack Cfirst Cgap Cmain Ctail hvchoice hUlo
  have hδ₀ := approximateModelPhase_tolerance_nonneg (hF 0)
  obtain ⟨Bmajor,Cmajor,hBmajor,hCmajor,hcost⟩ := hbudgets
    Gaps e r v s Q Uref hδ₀ (hδ.trans (min_le_right _ _)) hT hM hR hRQ hQN
    hNM hUref hUR hscale hrHeight hsHeight heHeight hvHeight
    (fun ab hab => ⟨(hgap ab hab).2.2.1,hgapWidth ab hab⟩)
  have hh := physicalModelPhase_actual_fourier_original_pair_mass Uref Refs Gaps (Bselect:=Bselect) P Mat gap Bmajor Cmajor Q K₀ N za zb AlenA AlenB Za Zb rat vinv parity anchor e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (R:=R) (base:=base) (Bcut:=Bcut) (lambda:=lambda) (Uband:=Uband) (θ:=θ) (V:=V) (F:=F) (A:=A) (W:=W) (x:=x) hbase hxa hxb hgapMem hgeometryA hgeometryB hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hc hlarge haction hV hgap
    hsourceColor hlevel hcolor hnear hnearNarrow hsmall hNR hRN hNcube hminscale
    hMatdet hMatt hMatmap hMatgamma hNtwo hL hU hanchor hcut hcount
    hsize hD hΔ hBsize hBmajor hCmajor
  have hmass := hh.2.2.2 hvchoice hUlo
  let m0 := 6+Cmajor*(105+544*Bmajor)
  let Kbase := 2*Bselect*60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
    (Cmain+Ctail)*((Q:ℝ)/(N:ℝ))^((2:ℝ)/3)
  have hmass' : V*(P.card:ℝ) ≤ (m0:ℝ)*Kbase := by
    convert hmass using 1
    dsimp only [m0,Kbase]
    ring
  have hmpos : (0:ℝ) < m0 := by dsimp only [m0]; positivity
  have hknon : 0 ≤ Kbase := by
    have hnon : 0 ≤ (m0:ℝ)*Kbase :=
      (mul_nonneg (zero_le_one.trans hV) (Nat.cast_nonneg _)).trans hmass'
    nlinarith only [hnon,hmpos]
  exact hmass'.trans (by
    calc
      (m0:ℝ)*Kbase ≤ T^εloss*Kbase := mul_le_mul_of_nonneg_right hcost hknon
      _ = Kbase*T^εloss := mul_comm _ _)

                                                                     
                                                                       
private theorem positive_difference_actual_endpoint_compression
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1/2 ∧ 0 < C ∧
    ∀ (F : ℝ → ℝ) (η x₀ y₀ ya yb b l r δ : ℝ) (xa xb : Fin 2 → ℝ),
    0 < η → η ≤ 1/8 → x₀∈Icc (1:ℝ) 2 → y₀∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
    let H := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 F z.2-iteratedDeriv 2 F (z.2+η*z.1))/(σ*η)
    let G := fun z : ℝ × ℝ =>
      (iteratedDeriv 3 F z.2-iteratedDeriv 3 F (z.2+η*z.1))/(σ*η)
    let t : Fin 2 → ℝ := ![l,r]
    let z₀ := (y₀,H (y₀,x₀))
    l < r →
    (∀ i, xa i∈Icc (1:ℝ) 2 ∧ xb i∈Icc (1:ℝ) 2 ∧
      H (ya,xa i)=t i ∧ H (yb,xb i)=t i+b) →
    (∀ i, ‖((ya,t i):ℝ × ℝ)-z₀‖ < a ∧ ‖((yb,t i+b):ℝ × ℝ)-z₀‖ < a) →
    (∀ i, |G (yb,xb i)-G (ya,xa i)| ≤ δ) →
    ‖((yb-ya,b):ℝ × ℝ)‖*(r-l) ≤ C*δ := by
  obtain ⟨a₀,ha₀,hcompression⟩ := positive_difference_constructed_endpoint_compression hσ hc hU
  let a := min a₀ (1/2:ℝ)
  let R := max 1 (max (3*U/σ) (2*σ/c))
  let κ := (c/(6*U))^2*(c^2*c/(6*U^4))
  have hR : 0 < R := zero_lt_one.trans_le (le_max_left _ _)
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  refine ⟨a,64*R^6/κ,lt_min ha₀ (by norm_num),min_le_right _ _,by positivity,?_⟩
  intro F η x₀ y₀ ya yb b l r δ xa xb hη hηmax hx₀ hy₀ hya hyb
    hf hbound htests H G t z₀ hlr hroots hends hnear
  let ρ := fun w : ℝ × ℝ =>
    Function.invFunOn (fun x => H (w.1,x)) (Ioo (3/4:ℝ) (9/4)) w.2
  let g := fun w => fderiv ℝ H (w.1,ρ w) (0,1)
  have hxext x (hx : x∈Icc (1:ℝ) 2) : x∈Ioo (3/4:ℝ) (9/4) :=
    ⟨by linarith only [hx.1],by linarith only [hx.2]⟩
  have hyext y (hy : y∈Icc (1:ℝ) 2) : y∈Icc (1/2:ℝ) 3 :=
    ⟨by linarith only [hy.1],by linarith only [hy.2]⟩
  have hGder x y (hx : x∈Icc (1:ℝ) 2) (hy : y∈Icc (1:ℝ) 2) :
      fderiv ℝ H (y,x) (0,1)=G (y,x) := by
    have hxpos : 0 < x := by linarith only [hx.1]
    have hypos : 0 < y := by linarith only [hy.1]
    exact (positive_difference_curvature_directions F (σ:=σ) hxpos
      (add_pos hxpos (mul_pos hη hypos)) hf 2).2.1
  have hcanonical i : |g (yb,t i+b)-g (ya,t i)| ≤ δ := by
    have ha : ρ (ya,t i)=xa i := positive_difference_curvature_inverse_eq F
      hσ hc hU hη hηmax (hxext _ (hroots i).1) (hyext _ hya)
      hf hbound htests (hroots i).2.2.1
    have hb : ρ (yb,t i+b)=xb i := positive_difference_curvature_inverse_eq F
      hσ hc hU hη hηmax (hxext _ (hroots i).2.1) (hyext _ hyb)
      hf hbound htests (hroots i).2.2.2
    dsimp only [g]
    rw [ha,hb,hGder _ _ (hroots i).1 hya,hGder _ _ (hroots i).2.1 hyb]
    exact hnear i
  have hsegment y β
      (hl : ‖((y,l+β):ℝ × ℝ)-z₀‖ < a)
      (hr : ‖((y,r+β):ℝ × ℝ)-z₀‖ < a)
      u (hu : u∈Icc l r) : ‖((y,u+β):ℝ × ℝ)-z₀‖ < a := by
    change max |y-z₀.1| |l+β-z₀.2| < a at hl
    change max |y-z₀.1| |r+β-z₀.2| < a at hr
    change max |y-z₀.1| |u+β-z₀.2| < a
    refine max_lt_iff.mpr ⟨(max_lt_iff.mp hl).1,abs_lt.mpr ⟨?_,?_⟩⟩
    · linarith only [(abs_lt.mp (max_lt_iff.mp hl).2).1,hu.1]
    · linarith only [(abs_lt.mp (max_lt_iff.mp hr).2).2,hu.2]
  have hpts u (hu : u∈Icc l r) :
      ‖((ya,u):ℝ × ℝ)-z₀‖ < a₀ ∧ ‖((yb,u+b):ℝ × ℝ)-z₀‖ < a₀ := by
    constructor
    · have hh := hsegment ya 0 (by simpa only [t,Matrix.cons_val_zero,add_zero] using (hends 0).1)
        (by
          have hr : ‖((ya,r):ℝ × ℝ)-z₀‖ < a := (hends 1).1
          simpa only [add_zero] using hr) u hu
      have hh' : ‖((ya,u):ℝ × ℝ)-z₀‖ < a := by simpa only [add_zero] using hh
      exact hh'.trans_le (min_le_left _ _)
    · exact (hsegment yb b (hends 0).2 (hends 1).2 u hu).trans_le (min_le_left _ _)
  have hlen : r-l ≤ 2 := by
    have hl := (norm_snd_le (((ya,l):ℝ × ℝ)-z₀)).trans_lt (hends 0).1
    have hr := (norm_snd_le (((ya,r):ℝ × ℝ)-z₀)).trans_lt (hends 1).1
    change |l-z₀.2| < a at hl
    change |r-z₀.2| < a at hr
    have ha : a ≤ 1/2 := min_le_right _ _
    linarith only [(abs_lt.mp hl).1,(abs_lt.mp hr).2,ha]
  have hh := hcompression F η x₀ y₀ ya yb b l r δ hη hηmax hx₀ hy₀
    hf hbound htests hlr hlen hpts (hcanonical 0) (hcanonical 1)
  have hdiv := (le_div_iff₀ hκ).mpr (by nlinarith only [hh] :
    ‖((yb-ya,b):ℝ × ℝ)‖*(r-l)*κ ≤ 64*R^6*δ)
  exact hdiv.trans_eq (by ring)

                                                                  
                                                                            
public  theorem positive_difference_physical_upper_endpoint_compression
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1/2 ∧ 0 < C ∧
    ∀ (F : ℝ → ℝ) (η x₀ y₀ ya yb b Δ T M : ℝ) (xa xb : Fin 2 → ℝ),
    0 < η → η ≤ 1/8 → x₀∈Icc (1:ℝ) 2 → y₀∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
    0 < T → 2 ≤ M → 0 ≤ Δ →
    (∀ i, xa i∈Icc M (2*M) ∧ xb i∈Icc M (2*M)) →
    let f := fun y z => T*(F (z/M)-F (z/M+η*y))/(σ*η)
    let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
    let u := fun i => iteratedDeriv 2 (f ya) (xa i)/2
    let t := fun i => (2*M^2/T)*u i
    let bnorm := 2*M^2*b/T
    let H := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 F z.2-iteratedDeriv 2 F (z.2+η*z.1))/(σ*η)
    let z₀ := (y₀,H (y₀,x₀))
    u 0 < u 1 →
    (∀ i, iteratedDeriv 2 (f yb) (xb i)/2=u i+b) →
    (∀ i, |μ yb (xb i)/μ ya (xa i)-1| ≤ Δ) →
    (∀ i, ‖((ya,t i):ℝ × ℝ)-z₀‖ < a ∧
      ‖((yb,t i+bnorm):ℝ × ℝ)-z₀‖ < a) →
    4*M^4*|b| *(u 1-u 0) ≤ C*(Δ+1/M)*T^2 := by
  obtain ⟨a,C,ha,hac,hC,hcompression⟩ :=
    positive_difference_actual_endpoint_compression hσ hc hU
  let B := max 1 (max (3*U/σ) (2*σ/c))
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨a,C*B,ha,hac,mul_pos hC hB,?_⟩
  intro F η x₀ y₀ ya yb b Δ T M xa xb hη hηmax hx₀ hy₀ hya hyb
    hf hbound htests hT hM hΔ hpoints f μ u t bnorm H z₀ hu hmap hthird hends
  have hMp : 0 < M := by linarith only [hM]
  let G := fun z : ℝ × ℝ =>
    (iteratedDeriv 3 F z.2-iteratedDeriv 3 F (z.2+η*z.1))/(σ*η)
  have hnorm z (hz : z∈Icc M (2*M)) : z/M∈Icc (1:ℝ) 2 := by
    constructor
    · exact (le_div_iff₀ hMp).mpr (by simpa using hz.1)
    · exact (div_le_iff₀ hMp).mpr hz.2
  have hpos z (hz : z∈Icc M (2*M)) : 0 < z := hMp.trans_le hz.1
  have hroundpos z (hz : z∈Icc M (2*M)) : (0:ℝ) < round z := by
    have hh := abs_le.mp (abs_sub_round z)
    linarith only [hh.2,hz.1,hM]
  have hd n z y (hz : 0 < z) (hy : y∈Icc (1:ℝ) 2) :
      iteratedDeriv n (f y) z=
        T/M^n*((iteratedDeriv n F (z/M)-iteratedDeriv n F (z/M+η*y))/(σ*η)) :=
    positive_difference_physical_iteratedDeriv F hMp hz
      (mul_nonneg hη.le (by linarith only [hy.1])) hf n
  have hrootA i : H (ya,xa i/M)=t i := by
    dsimp only [t,u]
    rw [hd 2 _ _ (hpos _ (hpoints i).1) hya]
    change H (ya,xa i/M)=(2*M^2/T)*(T/M^2*H (ya,xa i/M)/2)
    field_simp
  have hrootB i : H (yb,xb i/M)=t i+bnorm := by
    have he := congrArg (fun z : ℝ => (2*M^2/T)*z) (hmap i)
    rw [hd 2 _ _ (hpos _ (hpoints i).2) hyb] at he
    change (2*M^2/T)*(T/M^2*H (yb,xb i/M)/2)=(2*M^2/T)*(u i+b) at he
    change H (yb,xb i/M)=(2*M^2/T)*u i+2*M^2*b/T
    field_simp at he ⊢
    nlinarith only [he]
  have hrounded i :
      |G (yb,(round (M*(xb i/M)):ℝ)/M)/
        G (ya,(round (M*(xa i/M)):ℝ)/M)-1| ≤ Δ := by
    have he z : M*(z/M)=z := mul_div_cancel₀ z hMp.ne'
    rw [he,he]
    have ha : μ ya (xa i)=(T/(6*M^3))*G (ya,(round (xa i):ℝ)/M) := by
      dsimp only [μ]
      rw [hd 3 _ _ (hroundpos _ (hpoints i).1) hya]
      dsimp only [G]
      ring
    have hb : μ yb (xb i)=(T/(6*M^3))*G (yb,(round (xb i):ℝ)/M) := by
      dsimp only [μ]
      rw [hd 3 _ _ (hroundpos _ (hpoints i).2) hyb]
      dsimp only [G]
      ring
    have hh := hthird i
    rw [ha,hb,mul_div_mul_left _ _ (by positivity : T/(6*M^3) ≠ 0)] at hh
    exact hh
  have hnear i : |G (yb,xb i/M)-G (ya,xa i/M)| ≤ B*(Δ+1/M) :=
    positive_difference_rounded_third_bound F hσ hc hU hη hηmax hM
      (hnorm _ (hpoints i).1) (hnorm _ (hpoints i).2) hya hyb
      hf hbound htests hΔ (hrounded i)
  have ht : t 0 < t 1 := mul_lt_mul_of_pos_left hu (by positivity)
  have htvec (i : Fin 2) : (![t 0,t 1] : Fin 2 → ℝ) i=t i := by fin_cases i <;> rfl
  have hh := hcompression F η x₀ y₀ ya yb bnorm (t 0) (t 1) (B*(Δ+1/M))
    (fun i => xa i/M) (fun i => xb i/M) hη hηmax hx₀ hy₀ hya hyb hf hbound htests ht
    (by intro i; rw [htvec]; exact ⟨hnorm _ (hpoints i).1,hnorm _ (hpoints i).2,hrootA i,hrootB i⟩)
    (by intro i; rw [htvec]; exact hends i)
    hnear
  have hn : 2*M^2*|b|/T ≤ ‖((yb-ya,bnorm):ℝ × ℝ)‖ := by
    have he := norm_snd_le ((yb-ya,bnorm):ℝ × ℝ)
    simpa only [bnorm,Real.norm_eq_abs,abs_div,abs_mul,abs_of_pos hT,
      abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_nonneg (sq_nonneg M)] using he
  have hm := (mul_le_mul_of_nonneg_right hn (sub_nonneg.mpr ht.le)).trans hh
  have hm' := mul_le_mul_of_nonneg_right hm (sq_nonneg T)
  have he : (2*M^2*|b|/T*(t 1-t 0))*T^2=4*M^4*|b| *(u 1-u 0) := by
    dsimp only [t]
    field_simp
    ring
  rw [he] at hm'
  exact hm'.trans_eq (by ring)


private theorem huxley_upper_endpoint_source_scale
    {κ L R M N T S E C D b g : ℝ}
    (hL : 0 < L) (hR : 1 ≤ R) (hM : 0 < M)
    (hN : 0 < N) (hS : 0 < S)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hb : 0 ≤ b)
    (hNL : (L*N)^2 ≤ M*R) (hscale : T*N*R^2=M^3)
    (hST : S ≤ E*T) (hlow : κ*L/(8*R^2) ≤ g)
    (hu : 4*M^4*b*g ≤ C*(D*R^2/(L^2*N^2)+1/M)*S^2) :
    κ*b*L^3*N^4 ≤ 2*C*(D+1)*E^2*M^2 := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hNLR : L^2*N^2 ≤ M*R^2 := by
    calc
      _ = (L*N)^2 := by ring
      _ ≤ M*R := hNL
      _ ≤ M*R^2 := mul_le_mul_of_nonneg_left (by nlinarith only [hR] : R ≤ R^2) hM.le
  have hInv : 1/M ≤ R^2/(L^2*N^2) :=
    (div_le_div_iff₀ hM (by positivity)).mpr (by nlinarith only [hNLR])
  have hcost : D*R^2/(L^2*N^2)+1/M ≤ (D+1)*R^2/(L^2*N^2) := by
    calc
      _ ≤ D*R^2/(L^2*N^2)+R^2/(L^2*N^2) := add_le_add le_rfl hInv
      _ = _ := by ring
  have hsquare : S^2 ≤ E^2*T^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hS.le hST 2
  have hupper : 4*M^4*b*g ≤ C*((D+1)*R^2/(L^2*N^2))*(E^2*T^2) :=
    hu.trans (mul_le_mul
      (mul_le_mul_of_nonneg_left hcost hC) hsquare (sq_nonneg S) (by positivity))
  have hh := (mul_le_mul_of_nonneg_left hlow
    (by positivity : 0 ≤ 4*M^4*b)).trans hupper
  have heleft : 4*M^4*b*(κ*L/(8*R^2))=κ*b*L*M^4/(2*R^2) := by ring
  have heright : C*((D+1)*R^2/(L^2*N^2))*(E^2*T^2)=
      C*(D+1)*R^2*E^2*T^2/(L^2*N^2) := by ring
  rw [heleft,heright] at hh
  have hcross := (div_le_div_iff₀ (by positivity : 0 < 2*R^2)
    (by positivity : 0 < L^2*N^2)).mp hh
  have hmul := mul_le_mul_of_nonneg_right hcross (sq_nonneg N)
  have hsq : T^2*N^2*R^4=M^6 := by
    have he := congrArg (fun z : ℝ => z^2) hscale
    nlinarith only [he]
  have hright : (C*(D+1)*R^2*E^2*T^2*(2*R^2))*N^2=
      2*C*(D+1)*E^2*M^6 := by
    calc
      _ = 2*C*(D+1)*E^2*(T^2*N^2*R^4) := by ring
      _ = _ := by rw [hsq]
  rw [hright] at hmul
  apply (mul_le_mul_iff_right₀ (pow_pos hM 4)).mp
  convert hmul using 1 <;> ring

                                                                
                                                                 
                                                                                              
private theorem positive_difference_quartic_upper_long_block_constraint
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ a Csrc : ℝ, 0 < a ∧ 0 < Csrc ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb b Tsrc E : ℝ)
    {σ δ T M N R L d K α β : ℝ} (x : Fin 8 → ℝ)
    {F : Fin 2 → ℝ → ℝ} (A : Fin 2 → ℤ) {W x₀ e r v s : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ},
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (0 < L) →
    ((L*N)^2 ≤ M*R) →
    (0 < d) →
    (0 ≤ K) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      x₁ y i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, r i ≠ 0) →
    (∀ i, v i*r i-e i*s i=1) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, d ≤ r i*y+s i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, r i*y+s i ≤ 2*d) →
    (StrictMono x) →
    (T*N*R^2=M^3) →
    (e 1=e 0+b*r 0 ∧ v 1=v 0+b*s 0 ∧ r 1=r 0 ∧ s 1=s 0) →
    0 < η → η ≤ 1/8 → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun y i => (round (x₁ y i):ℝ)-(round (x₀ i):ℝ)
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
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
    let κ := modelPhaseThirdLower σ
    let Γ := (σ*(σ+1)+1)/κ
    let C := Γ*(32*K+9*quarticReciprocalConstant σ δ)
    let yp : Fin 2 → ℝ := ![ya,yb]
    let Src := fun y z => Tsrc*(Fsrc (z/M)-Fsrc (z/M+η*y))/(σsrc*η)
    let Hsrc := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc z.2-iteratedDeriv 2 Fsrc (z.2+η*z.1))/(σsrc*η)
    let center := (ycenter,Hsrc (ycenter,xcenter))
    (∀ i, f i=fun z => Src (yp i) ((A i:ℝ)+z)) →
    (∀ z∈({x 0,x 7} : Finset ℝ), ∀ i,
      ‖((yp i,(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (x₁ z i)/2)):ℝ × ℝ)-center‖ < a) →
    κ*|b| *L^3*N^4 ≤ 2*Csrc*(C+1)*E^2*M^2 := by
  obtain ⟨a,Csrc,ha,_hac,hCsrc,hcompression⟩ :=
    positive_difference_physical_upper_endpoint_compression hσsrc hcsrc hUsrc
  refine ⟨a,Csrc,ha,hCsrc,?_⟩
  intro Fsrc η xcenter ycenter ya yb b Tsrc E σ δ T M N R L d K α β x F A W x₀ e r v s x₁
    hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀ hx₁ hr hdet hden hdenUpper hmono hscale
    htransport hη hηmax hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
    f n μ ν D g H G hbase hpoint hsquare hgap hres κ Γ C yp Src Hsrc center hsource hlocalEnds
  have hxleft : x 0∈Icc (x 0) (x 7) := ⟨le_rfl,hmono.monotone (by decide)⟩
  have hxright : x 7∈Icc (x 0) (x 7) := ⟨hmono.monotone (by decide),le_rfl⟩
  have hcurvOrder u w (hu : u∈Icc (x 0) (x 7)) (hv : w∈Icc (x 0) (x 7))
      (huv : u ≤ w) i :
      iteratedDeriv 2 (f i) (x₁ w i)/2 ≤ iteratedDeriv 2 (f i) (x₁ u i)/2 := by
    apply sub_nonneg.mp
    have hdu : 0 < D u i := hd.trans_le (hden u hu i)
    have hdv : 0 < D w i := hd.trans_le (hden w hv i)
    rw [hpoint u hu i,hpoint w hv i,div_sub_div _ _ hdu.ne' hdv.ne']
    have hnum : (e i*u+v i)*D w i-D u i*(e i*w+v i)=w-u := by
      dsimp only [D]
      linear_combination (w-u)*hdet i
    rw [hnum]
    exact div_nonneg (sub_nonneg.mpr huv) (mul_pos hdu hdv).le
  have hlocal z (hz : z∈Icc (x 0) (x 7)) i :
      ‖((yp i,(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (x₁ z i)/2)):ℝ × ℝ)-center‖ < a := by
    have hl := hlocalEnds (x 7) (by simp) i
    have hu := hlocalEnds (x 0) (by simp) i
    have hlo := mul_le_mul_of_nonneg_left (hcurvOrder z (x 7) hz hxright hz.2 i)
      (by positivity : 0 ≤ 2*M^2/Tsrc)
    have hhi := mul_le_mul_of_nonneg_left (hcurvOrder (x 0) z hxleft hz hz.1 i)
      (by positivity : 0 ≤ 2*M^2/Tsrc)
    change max |yp i-center.1|
      |(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (x₁ (x 7) i)/2)-center.2| < a at hl
    change max |yp i-center.1|
      |(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (x₁ (x 0) i)/2)-center.2| < a at hu
    change max |yp i-center.1|
      |(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (x₁ z i)/2)-center.2| < a
    refine max_lt_iff.mpr ⟨(max_lt_iff.mp hl).1,abs_lt.mpr ⟨?_,?_⟩⟩
    · linarith only [(abs_lt.mp (max_lt_iff.mp hl).2).1,hlo]
    · linarith only [(abs_lt.mp (max_lt_iff.mp hu).2).2,hhi]
  let μnew := fun y i => iteratedDeriv 3 (f i) (round (x₁ y i))/6
  obtain ⟨z₀,hz₀,z₁,hz₁,hG,hthird⟩ := physicalModelPhase_quartic_two_long_block_witnesses
    x hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀ hx₁ hr hdet
    hden hdenUpper hmono hbase hpoint hsquare hgap hres
  have hz₀' : z₀∈Icc (x 0) (x 7) :=
    ⟨hz₀.1.le,hz₀.2.le.trans (hmono.monotone (by decide))⟩
  have hz₁' : z₁∈Icc (x 0) (x 7) :=
    ⟨(hmono.monotone (by decide)).trans hz₁.1.le,hz₁.2.le⟩
  have hzorder : z₀ ≤ z₁ := hz₀.2.le.trans
    ((hmono.monotone (by decide : (3:Fin 8) ≤ 4)).trans hz₁.1.le)
  have hdpos z (hz : z∈Icc (x 0) (x 7)) i : 0 < D z i :=
    hd.trans_le (hden z hz i)
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hF₂ i := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl
  have hround := physicalModelPhase_halfCurvature_round_error hσ.le (hF₂ 0)
    hT hM (hA 0) (hW 0) (hx₀ 0)
  have hμbounds := physicalModelPhase_cubicCoefficient_bounds hσ hδ (hF₂ 0)
    hT hM (hA 0) (hW 0) hround.1
  have hμ : 0 < μ 0 := lt_of_lt_of_le (by positivity) hμbounds.1
  let z : Fin 2 → ℝ := ![z₁,z₀]
  let profile : ℝ → ℝ := fun t => iteratedDeriv 2 (f 0) (x₁ t 0)/2
  have hz p : z p∈Icc (x 0) (x 7) := by
    fin_cases p
    · exact hz₁'
    · exact hz₀'
  have hdiff : profile z₀-profile z₁=(z₁-z₀)/(D z₀ 0*D z₁ 0) := by
    dsimp only [profile]
    rw [hpoint z₀ hz₀' 0,hpoint z₁ hz₁' 0,
      div_sub_div _ _ (hdpos z₀ hz₀' 0).ne' (hdpos z₁ hz₁' 0).ne']
    congr 1
    dsimp only [D]
    linear_combination (z₁-z₀)*hdet 0
  have horder : profile z₁ ≤ profile z₀ := sub_nonneg.mp (by
    rw [hdiff]
    exact div_nonneg (sub_nonneg.mpr hzorder)
      (mul_pos (hdpos z₀ hz₀' 0) (hdpos z₁ hz₁' 0)).le)
  have hGid t (ht : t∈Icc (x 0) (x 7)) : profile t-e 0/r 0=3*μ 0*G t := by
    rw [show profile t=(e 0*t+v 0)/(r 0*t+s 0) from hpoint t ht 0]
    simpa only [mul_one,div_one] using
      (farey_curvature_coordinate_identity (u:=t) (t:=1) hμ.ne' (hr 0)
        one_ne_zero (by simpa only [mul_one] using (hdpos t ht 0).ne') (hdet 0))
  have hdiffG : profile z₀-profile z₁=3*μ 0*(G z₀-G z₁) := by
    linarith only [hGid z₀ hz₀',hGid z₁ hz₁']
  have hGorder : 0 ≤ G z₀-G z₁ := by
    apply (mul_nonneg_iff_of_pos_left (mul_pos (by norm_num : (0:ℝ)<3) hμ)).mp
    rw [← hdiffG]
    exact sub_nonneg.mpr horder
  rw [abs_sub_comm,abs_of_nonneg hGorder] at hG
  have hlo : κ*L/(8*R^2) ≤ profile z₀-profile z₁ := by
    have hmul := mul_le_mul_of_nonneg_left hG
      (mul_pos (by norm_num : (0:ℝ)<3) hμ).le
    calc
      _ = 3*(κ*T/(6*M^3))*(L*N/4) := by
        have hTval : T=M^3/(N*R^2) :=
          (eq_div_iff (by positivity)).mpr (by nlinarith only [hscale])
        rw [hTval]
        field_simp
        ring_nf
      _ ≤ 3*μ 0*(L*N/4) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hμbounds.1 (by norm_num : (0:ℝ) ≤ 3))
        (by positivity)
      _ ≤ _ := by linarith only [hmul,hdiffG]
  let Δ := C*R^2/(L^2*N^2)
  have hΔ : 0 ≤ Δ := (abs_nonneg _).trans (hthird z₀ (by simp))
  have hC : 0 ≤ C := by
    have hh : 0 ≤ C*(R^2/(L^2*N^2)) := by simpa only [Δ,mul_div_assoc] using hΔ
    have hp : 0 < R^2/(L^2*N^2) := by positivity
    nlinarith only [hh,hp]
  have hDsame t : D t 1=D t 0 := by
    dsimp only [D]
    rw [htransport.2.2.1,htransport.2.2.2]
  have hmap t (ht : t∈Icc (x 0) (x 7)) :
      iteratedDeriv 2 (f 1) (x₁ t 1)/2=profile t+b := by
    change _=iteratedDeriv 2 (f 0) (x₁ t 0)/2+b
    rw [hpoint t ht 1,hpoint t ht 0,hDsame]
    rw [htransport.1,htransport.2.1]
    have hd0 : r 0*t+s 0 ≠ 0 := (hdpos t ht 0).ne'
    dsimp only [D]
    field_simp [hd0]
    ring
  have hthird' p : |μnew (z p) 1/μnew (z p) 0-1| ≤ Δ := by
    have hh := hthird (z p) (by fin_cases p <;> simp [z])
    change |μnew (z p) 1*(D (z p) 1)^3/(μnew (z p) 0*(D (z p) 0)^3)-1| ≤ Δ at hh
    rw [hDsame] at hh
    rwa [mul_div_mul_right _ _ (pow_ne_zero 3 (hdpos _ (hz p) 0).ne')] at hh
  have hjet i k t : iteratedDeriv k (f i) t=
      iteratedDeriv k (Src (yp i)) ((A i:ℝ)+t) := by
    rw [hsource,iteratedDeriv_comp_const_add]
  have hrounded i t :
      iteratedDeriv 3 (f i) (round t)=
        iteratedDeriv 3 (Src (yp i)) (round ((A i:ℝ)+t)) := by
    rw [hjet,round_intCast_add,Int.cast_add]
  let xa := fun p => (A 0:ℝ)+x₁ (z p) 0
  let xb := fun p => (A 1:ℝ)+x₁ (z p) 1
  have hphysical p : xa p∈Icc M (2*M) ∧ xb p∈Icc M (2*M) := by
    constructor
    · exact ⟨by dsimp only [xa]; linarith only [hA 0,(hx₁ _ (hz p) 0).1],
        by dsimp only [xa]; linarith only [hW 0,(hx₁ _ (hz p) 0).2]⟩
    · exact ⟨by dsimp only [xb]; linarith only [hA 1,(hx₁ _ (hz p) 1).1],
        by dsimp only [xb]; linarith only [hW 1,(hx₁ _ (hz p) 1).2]⟩
  have hua p : iteratedDeriv 2 (Src ya) (xa p)/2=profile (z p) := by
    exact (congrArg (fun u : ℝ => u/2) (hjet 0 2 (x₁ (z p) 0))).symm
  have hub p : iteratedDeriv 2 (Src yb) (xb p)/2=profile (z p)+b := by
    exact (congrArg (fun u : ℝ => u/2) (hjet 1 2 (x₁ (z p) 1))).symm.trans (hmap _ (hz p))
  have hstrict : profile z₁ < profile z₀ := by
    have hp : 0 < κ*L/(8*R^2) := by positivity
    linarith only [hlo,hp]
  have hh := hcompression Fsrc η xcenter ycenter ya yb b Δ Tsrc M xa xb
    hη hηmax hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hΔ hphysical
    (by
      change iteratedDeriv 2 (Src ya) (xa 0)/2 < iteratedDeriv 2 (Src ya) (xa 1)/2
      rw [hua,hua]
      exact hstrict)
    (by
      intro p
      change iteratedDeriv 2 (Src yb) (xb p)/2=iteratedDeriv 2 (Src ya) (xa p)/2+b
      rw [hua,hub])
    (by
      intro p
      have hh := hthird' p
      change |(iteratedDeriv 3 (f 1) (round (x₁ (z p) 1))/6)/
        (iteratedDeriv 3 (f 0) (round (x₁ (z p) 0))/6)-1| ≤ Δ at hh
      rw [hrounded,hrounded] at hh
      exact hh)
    (by
      intro p
      change ‖((ya,(2*M^2/Tsrc)*(iteratedDeriv 2 (Src ya) (xa p)/2)):ℝ × ℝ)-center‖ < a ∧
        ‖((yb,(2*M^2/Tsrc)*(iteratedDeriv 2 (Src ya) (xa p)/2)+2*M^2*b/Tsrc):ℝ × ℝ)-center‖ < a
      constructor
      · rw [hua]
        exact hlocal _ (hz p) 0
      · have he : (2*M^2/Tsrc)*(iteratedDeriv 2 (Src ya) (xa p)/2)+
            2*M^2*b/Tsrc=(2*M^2/Tsrc)*(iteratedDeriv 2 (f 1) (x₁ (z p) 1)/2) := by
          rw [hua,hmap _ (hz p)]
          ring
        rw [he]
        exact hlocal _ (hz p) 1)
  change 4*M^4*|b| *(iteratedDeriv 2 (Src ya) (xa 1)/2-iteratedDeriv 2 (Src ya) (xa 0)/2) ≤
    Csrc*(Δ+1/M)*Tsrc^2 at hh
  rw [hua,hua] at hh
  exact huxley_upper_endpoint_source_scale hL hR hM hN hTsrc hCsrc.le hC
    (abs_nonneg b) hNL hscale hsourceScale hlo hh

                                                                
                                                                        
                                                                     
theorem positive_difference_normalized_quartic_upper_long_block_constraint
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ a Csrc : ℝ, 0 < a ∧ 0 < Csrc ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb b Tsrc E : ℝ)
    {σ δ T M N R L d K α β : ℝ} (x : Fin 8 → ℝ)
    (A : Fin 2 → ℤ) {W x₀ e r v s : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ},
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*(![ya,yb] : Fin 2 → ℝ) i))/(σsrc*η)
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (0 < L) →
    ((L*N)^2 ≤ M*R) →
    (0 < d) →
    (0 ≤ K) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      x₁ y i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, r i ≠ 0) →
    (∀ i, v i*r i-e i*s i=1) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, d ≤ r i*y+s i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, r i*y+s i ≤ 2*d) →
    (StrictMono x) →
    (T*N*R^2=M^3) →
    (e 1=e 0+b*r 0 ∧ v 1=v 0+b*s 0 ∧ r 1=r 0 ∧ s 1=s 0) →
    0 < η → η ≤ 1/8 → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun y i => (round (x₁ y i):ℝ)-(round (x₀ i):ℝ)
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
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
    let κ := modelPhaseThirdLower σ
    let Γ := (σ*(σ+1)+1)/κ
    let C := Γ*(32*K+9*quarticReciprocalConstant σ δ)
    let yp : Fin 2 → ℝ := ![ya,yb]
    let Hsrc := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc z.2-iteratedDeriv 2 Fsrc (z.2+η*z.1))/(σsrc*η)
    let center := (ycenter,Hsrc (ycenter,xcenter))
    (∀ z∈({x 0,x 7} : Finset ℝ), ∀ i,
      ‖((yp i,(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (x₁ z i)/2)):ℝ × ℝ)-center‖ < a) →
    κ*|b| *L^3*N^4 ≤ 2*Csrc*(C+1)*E^2*M^2 := by
  obtain ⟨a,Csrc,ha,hCsrc,hcore⟩ :=
    positive_difference_quartic_upper_long_block_constraint hσsrc hcsrc hUsrc
  refine ⟨a,Csrc,ha,hCsrc,?_⟩
  intro Fsrc η xcenter ycenter ya yb b Tsrc E σ δ T M N R L d K α β x A W x₀ e r v s x₁
    F hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀ hx₁ hr hdet hden hdenUpper hmono hscale
    htransport hη hηmax hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
    f n μ ν D g H G hbase hpoint hsquare hgap hres κ Γ C yp Hsrc center hlocalEnds
  let Src := fun y z => Tsrc*(Fsrc (z/M)-Fsrc (z/M+η*y))/(σsrc*η)
  have hsource i : f i=fun z => Src (yp i) ((A i:ℝ)+z) := by
    funext z
    dsimp only [f,heathBrownPhysicalPhase,F,Src,yp]
    field_simp
  exact hcore Fsrc η xcenter ycenter ya yb b Tsrc E x (F:=F) A
    hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀ hx₁ hr hdet hden hdenUpper hmono hscale
    htransport hη hηmax hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
    hbase hpoint hsquare hgap hres hsource hlocalEnds

private theorem positive_difference_actual_reciprocal_endpoint_compression
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ η₀ a C : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ a ≤ 1/2 ∧ 0 < C ∧
    ∀ (F : ℝ → ℝ) (η x₀ y₀ ya yb b l r δ : ℝ) (xa xb : Fin 2 → ℝ),
    0 < η → η ≤ η₀ → x₀∈Icc (1:ℝ) 2 → y₀∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
    let H := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 F z.2-iteratedDeriv 2 F (z.2+η*z.1))/(σ*η)
    let G := fun z : ℝ × ℝ =>
      (iteratedDeriv 3 F z.2-iteratedDeriv 3 F (z.2+η*z.1))/(σ*η)
    let t : Fin 2 → ℝ := ![l,r]
    let z₀ := (y₀,(H (y₀,x₀))⁻¹)
    l < r →
    (∀ i, xa i∈Icc (1:ℝ) 2 ∧ xb i∈Icc (1:ℝ) 2 ∧
      H (ya,xa i)=(t i)⁻¹ ∧ H (yb,xb i)=(t i+b)⁻¹) →
    (∀ i, ‖((ya,t i):ℝ × ℝ)-z₀‖ < a ∧ ‖((yb,t i+b):ℝ × ℝ)-z₀‖ < a) →
    (∀ i, |G (yb,xb i)*((H (yb,xb i))⁻¹)^3-
      G (ya,xa i)*((H (ya,xa i))⁻¹)^3| ≤ δ) →
    ‖((yb-ya,b):ℝ × ℝ)‖*(r-l) ≤ C*δ := by
  obtain ⟨η₀,a₀,C,hη₀,hηcap,ha₀,hC,hcompression⟩ :=
    positive_difference_constructed_reciprocal_endpoint_compression hσ hc hU
  let a := min a₀ (1/2:ℝ)
  refine ⟨η₀,a,C,hη₀,hηcap,lt_min ha₀ (by norm_num),min_le_right _ _,hC,?_⟩
  intro F η x₀ y₀ ya yb b l r δ xa xb hη hηsmall hx₀ hy₀ hya hyb
    hf hbound htests H G t z₀ hlr hroots hends hnear
  have hηmax : η ≤ 1/8 := hηsmall.trans hηcap
  let ρ := fun w : ℝ × ℝ =>
    Function.invFunOn (fun x => H (w.1,x)) (Ioo (3/4:ℝ) (9/4)) w.2
  let g := fun w => fderiv ℝ H (w.1,ρ w) (0,1)
  let k := fun w : ℝ × ℝ => w.2^3*g (w.1,w.2⁻¹)
  have hxext x (hx : x∈Icc (1:ℝ) 2) : x∈Ioo (3/4:ℝ) (9/4) :=
    ⟨by linarith only [hx.1],by linarith only [hx.2]⟩
  have hyext y (hy : y∈Icc (1:ℝ) 2) : y∈Icc (1/2:ℝ) 3 :=
    ⟨by linarith only [hy.1],by linarith only [hy.2]⟩
  have hGder x y (hx : x∈Icc (1:ℝ) 2) (hy : y∈Icc (1:ℝ) 2) :
      fderiv ℝ H (y,x) (0,1)=G (y,x) := by
    have hxpos : 0 < x := by linarith only [hx.1]
    have hypos : 0 < y := by linarith only [hy.1]
    exact (positive_difference_curvature_directions F (σ:=σ) hxpos
      (add_pos hxpos (mul_pos hη hypos)) hf 2).2.1
  have hcanonical i : |k (yb,t i+b)-k (ya,t i)| ≤ δ := by
    have ha : ρ (ya,(t i)⁻¹)=xa i := positive_difference_curvature_inverse_eq F
      hσ hc hU hη hηmax (hxext _ (hroots i).1) (hyext _ hya)
      hf hbound htests (hroots i).2.2.1
    have hb : ρ (yb,(t i+b)⁻¹)=xb i := positive_difference_curvature_inverse_eq F
      hσ hc hU hη hηmax (hxext _ (hroots i).2.1) (hyext _ hyb)
      hf hbound htests (hroots i).2.2.2
    dsimp only [k,g]
    rw [ha,hb,hGder _ _ (hroots i).1 hya,hGder _ _ (hroots i).2.1 hyb]
    have hh := hnear i
    rw [(hroots i).2.2.1,(hroots i).2.2.2,inv_inv,inv_inv] at hh
    simpa only [mul_comm] using hh
  have hsegment y β
      (hl : ‖((y,l+β):ℝ × ℝ)-z₀‖ < a)
      (hr : ‖((y,r+β):ℝ × ℝ)-z₀‖ < a)
      u (hu : u∈Icc l r) : ‖((y,u+β):ℝ × ℝ)-z₀‖ < a := by
    change max |y-z₀.1| |l+β-z₀.2| < a at hl
    change max |y-z₀.1| |r+β-z₀.2| < a at hr
    change max |y-z₀.1| |u+β-z₀.2| < a
    refine max_lt_iff.mpr ⟨(max_lt_iff.mp hl).1,abs_lt.mpr ⟨?_,?_⟩⟩
    · linarith only [(abs_lt.mp (max_lt_iff.mp hl).2).1,hu.1]
    · linarith only [(abs_lt.mp (max_lt_iff.mp hr).2).2,hu.2]
  have hpts u (hu : u∈Icc l r) :
      ‖((ya,u):ℝ × ℝ)-z₀‖ < a₀ ∧ ‖((yb,u+b):ℝ × ℝ)-z₀‖ < a₀ := by
    constructor
    · have hh := hsegment ya 0 (by simpa only [t,Matrix.cons_val_zero,add_zero] using (hends 0).1)
        (by
          have hr : ‖((ya,r):ℝ × ℝ)-z₀‖ < a := (hends 1).1
          simpa only [add_zero] using hr) u hu
      have hh' : ‖((ya,u):ℝ × ℝ)-z₀‖ < a := by simpa only [add_zero] using hh
      exact hh'.trans_le (min_le_left _ _)
    · exact (hsegment yb b (hends 0).2 (hends 1).2 u hu).trans_le (min_le_left _ _)
  have hlen : r-l ≤ 2 := by
    have hl := (norm_snd_le (((ya,l):ℝ × ℝ)-z₀)).trans_lt (hends 0).1
    have hr := (norm_snd_le (((ya,r):ℝ × ℝ)-z₀)).trans_lt (hends 1).1
    change |l-z₀.2| < a at hl
    change |r-z₀.2| < a at hr
    have ha : a ≤ 1/2 := min_le_right _ _
    linarith only [(abs_lt.mp hl).1,(abs_lt.mp hr).2,ha]
  exact hcompression F η x₀ y₀ ya yb b l r δ hη hηsmall hx₀ hy₀ hya hyb
    hf hbound htests hlr hlen hpts (hcanonical 0) (hcanonical 1)



private theorem reciprocal_endpoint_curvature_bound
    {a b T M R C D γ : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hT : 0 < T) (hM : 0 < M)
    (horder : a⁻¹ ≤ b⁻¹)
    (hA : |a| ≤ T*R/(2*M^2)) (hB : |b| ≤ T*R/(2*M^2))
    (hraw : T^2*|γ| *(b⁻¹-a⁻¹) ≤ 4*C*D*M^4) :
    |γ| *|b-a| ≤ C*D*R^2 := by
  have hi : 0 ≤ b⁻¹-a⁻¹ := sub_nonneg.mpr horder
  have hbox : 0 ≤ T*R/(2*M^2) := (abs_nonneg a).trans hA
  have hab : |a| *|b| ≤ (T*R/(2*M^2))^2 := by
    simpa only [pow_two] using mul_le_mul hA hB (abs_nonneg b) hbox
  have hid : |b-a|=|a| *|b| *(b⁻¹-a⁻¹) := by
    have he : b-a=a*b*(a⁻¹-b⁻¹) := by field_simp
    rw [he,abs_mul,abs_mul,abs_sub_comm,abs_of_nonneg hi]
  have hmain : T^2*|γ| *(b⁻¹-a⁻¹)/(4*M^4) ≤ C*D :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hraw])
  calc
    |γ| *|b-a| = |γ| *(|a| *|b| *(b⁻¹-a⁻¹)) := by rw [hid]
    _ ≤ |γ| *((T*R/(2*M^2))^2*(b⁻¹-a⁻¹)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hab hi) (abs_nonneg _)
    _ = (T^2*|γ| *(b⁻¹-a⁻¹)/(4*M^4))*R^2 := by field_simp; ring
    _ ≤ C*D*R^2 := mul_le_mul_of_nonneg_right hmain (sq_nonneg R)



                                                                
                                                           
public  theorem positive_difference_physical_lower_endpoint_compression
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ η₀ a C : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ a ≤ 1/2 ∧ 0 < C ∧
    ∀ (F : ℝ → ℝ) (η x₀ y₀ ya yb γ Δ T M : ℝ) (xa xb : Fin 2 → ℝ),
    0 < η → η ≤ η₀ → x₀∈Icc (1:ℝ) 2 → y₀∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
    0 < T → 2 ≤ M → 0 ≤ Δ →
    (∀ i, xa i∈Icc M (2*M) ∧ xb i∈Icc M (2*M)) →
    let f := fun y z => T*(F (z/M)-F (z/M+η*y))/(σ*η)
    let h := fun y z => iteratedDeriv 2 (f y) z/2
    let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
    let u := fun i => (h ya (xa i))⁻¹
    let t := fun i => (T/(2*M^2))*u i
    let bnorm := T*γ/(2*M^2)
    let H := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 F z.2-iteratedDeriv 2 F (z.2+η*z.1))/(σ*η)
    let z₀ := (y₀,(H (y₀,x₀))⁻¹)
    u 0 < u 1 →
    (∀ i, h yb (xb i)=h ya (xa i)/(γ*h ya (xa i)+1)) →
    (∀ i, |μ yb (xb i)/μ ya (xa i)*(γ*h ya (xa i)+1)^3-1| ≤ Δ) →
    (∀ i, ‖((ya,t i):ℝ × ℝ)-z₀‖ < a ∧
      ‖((yb,t i+bnorm):ℝ × ℝ)-z₀‖ < a) →
    |γ| *|h ya (xa 1)-h ya (xa 0)| ≤ C*(Δ+1/M) := by
  obtain ⟨η₀,a,C,hη₀,hηcap,ha,hac,hC,hcompression⟩ :=
    positive_difference_actual_reciprocal_endpoint_compression hσ hc hU
  let R := max 1 (max (3*U/σ) (2*σ/c))
  have hR : 0 < R := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨η₀,a,C*R^12,hη₀,hηcap,ha,hac,by positivity,?_⟩
  intro F η x₀ y₀ ya yb γ Δ T M xa xb hη hηsmall hx₀ hy₀ hya hyb
    hf hbound htests hT hM hΔ hpoints f h μ u t bnorm H z₀ hu hmap hthird hends
  have hηmax : η ≤ 1/8 := hηsmall.trans hηcap
  have hMpos : 0 < M := by linarith only [hM]
  let G := fun v : ℝ × ℝ =>
    (iteratedDeriv 3 F v.2-iteratedDeriv 3 F (v.2+η*v.1))/(σ*η)
  let P := fun v => G v*((H v)⁻¹)^3
  let L := T/(2*M^2)
  have hL : L ≠ 0 := by dsimp only [L]; positivity
  have hnorm x (hx : x ∈ Icc M (2*M)) : x/M ∈ Icc (1:ℝ) 2 := by
    constructor
    · exact (le_div_iff₀ hMpos).mpr (by simpa using hx.1)
    · exact (div_le_iff₀ hMpos).mpr hx.2
  have hpos x (hx : x ∈ Icc M (2*M)) : 0 < x := hMpos.trans_le hx.1
  have hroundpos x (hx : x ∈ Icc M (2*M)) : (0:ℝ) < round x := by
    have hh := abs_le.mp (abs_sub_round x)
    linarith only [hh.2,hx.1,hM]
  have hd n x y (hx : 0 < x) (hy : y ∈ Icc (1:ℝ) 2) :
      iteratedDeriv n (f y) x=
        T/M^n*((iteratedDeriv n F (x/M)-iteratedDeriv n F (x/M+η*y))/(σ*η)) :=
    positive_difference_physical_iteratedDeriv F hMpos hx
      (mul_nonneg hη.le (by linarith only [hy.1])) hf n
  have hHne x y (hx : x ∈ Icc M (2*M)) (hy : y ∈ Icc (1:ℝ) 2) :
      H (y,x/M) ≠ 0 := by
    have hx' := hnorm x hx
    have hxwide : x/M ∈ Icc (3/4:ℝ) (9/4) :=
      ⟨by linarith only [hx'.1],by linarith only [hx'.2]⟩
    have hywide : y ∈ Icc (1/2:ℝ) 3 :=
      ⟨by linarith only [hy.1],by linarith only [hy.2]⟩
    have he := (positive_jets_difference_curvature_entry F hσ hc hU hη hηmax
      hxwide hywide hf hbound htests 3 (by norm_num) (by norm_num)).1
    change iteratedDeriv 2 (fun u => (F u-F (u+η*y))/(σ*η)) (x/M)=H (y,x/M) at he
    have hlo := positive_jets_difference_spatial_lower F hσ hc hη hηmax
      hxwide hywide hf htests 2 (by norm_num) (by norm_num)
    rw [he] at hlo
    exact abs_pos.mp (lt_of_lt_of_le (by positivity) hlo)
  have hHbound x y (hx : x∈Icc M (2*M)) (hy : y∈Icc (1:ℝ) 2) :
      |H (y,x/M)| ≤ R := by
    have hx' := hnorm x hx
    have hxwide : x/M∈Icc (3/4:ℝ) (9/4) :=
      ⟨by linarith only [hx'.1],by linarith only [hx'.2]⟩
    have hywide : y∈Icc (1/2:ℝ) 3 :=
      ⟨by linarith only [hy.1],by linarith only [hy.2]⟩
    have he := (positive_jets_difference_curvature_entry F hσ hc hU hη hηmax
      hxwide hywide hf hbound htests 3 (by norm_num) (by norm_num)).1
    change iteratedDeriv 2 (fun u => (F u-F (u+η*y))/(σ*η)) (x/M)=H (y,x/M) at he
    have hup := positive_jets_difference_mixed_upper F hσ hU hη hηmax
      hxwide hywide hf hbound 2 0 (by norm_num) (by norm_num)
    simp only [iteratedDeriv_zero] at hup
    rw [he] at hup
    exact hup.trans ((le_max_left _ _).trans (le_max_right _ _))
  have hscale x y (hx : x ∈ Icc M (2*M)) (hy : y ∈ Icc (1:ℝ) 2) :
      h y x=L*H (y,x/M) := by
    dsimp only [h]
    rw [hd 2 x y (hpos x hx) hy]
    dsimp only [L,H]
    ring
  have hroots k :
      xa k/M ∈ Icc (1:ℝ) 2 ∧ xb k/M ∈ Icc (1:ℝ) 2 ∧
      (H (yb,xb k/M))⁻¹=(H (ya,xa k/M))⁻¹+T*γ/(2*M^2) := by
    refine ⟨hnorm _ (hpoints k).1,hnorm _ (hpoints k).2,?_⟩
    have hh := hmap k
    rw [hscale _ _ (hpoints k).2 hyb,hscale _ _ (hpoints k).1 hya] at hh
    have hHa := hHne _ _ (hpoints k).1 hya
    calc
      _ = L*(L*H (yb,xb k/M))⁻¹ := by simp [mul_inv_rev,hL,mul_comm]
      _ = L*((γ*(L*H (ya,xa k/M))+1)/(L*H (ya,xa k/M))) := by rw [hh,inv_div]
      _ = _ := by dsimp only [L]; field_simp; ring
  have hratio k :
      H (ya,xa k/M)/H (yb,xb k/M)=γ*h ya (xa k)+1 := by
    have hHa : h ya (xa k) ≠ 0 := by
      rw [hscale _ _ (hpoints k).1 hya]
      exact mul_ne_zero hL (hHne _ _ (hpoints k).1 hya)
    calc
      _ = h ya (xa k)/h yb (xb k) := by
        rw [hscale _ _ (hpoints k).1 hya,hscale _ _ (hpoints k).2 hyb,
          mul_div_mul_left _ _ hL]
      _ = h ya (xa k)/(h ya (xa k)/(γ*h ya (xa k)+1)) := by rw [hmap k]
      _ = _ := by field_simp
  have hrounded k :
      |G (yb,(round (M*(xb k/M)):ℝ)/M)/
        G (ya,(round (M*(xa k/M)):ℝ)/M)*(H (ya,xa k/M)/H (yb,xb k/M))^3-1| ≤ Δ := by
    have he x : M*(x/M)=x := mul_div_cancel₀ x hMpos.ne'
    rw [he,he]
    have ha : μ ya (xa k)=(T/(6*M^3))*G (ya,(round (xa k):ℝ)/M) := by
      dsimp only [μ]
      rw [hd 3 _ _ (hroundpos _ (hpoints k).1) hya]
      dsimp only [G]
      ring
    have hb : μ yb (xb k)=(T/(6*M^3))*G (yb,(round (xb k):ℝ)/M) := by
      dsimp only [μ]
      rw [hd 3 _ _ (hroundpos _ (hpoints k).2) hyb]
      dsimp only [G]
      ring
    have hh := hthird k
    rw [←hratio k] at hh
    rw [ha,hb,mul_div_mul_left _ _ (by positivity : T/(6*M^3) ≠ 0)] at hh
    exact hh
  have hnear k : |P (yb,xb k/M)-P (ya,xa k/M)| ≤ R^10*(Δ+1/M) :=
    positive_difference_rounded_reciprocal_profile_bound F hσ hc hU hη hηmax hM
      (hroots k).1 (hroots k).2.1 hya hyb hf hbound htests hΔ (hrounded k)
  have htA k : (H (ya,xa k/M))⁻¹=t k := by
    change _=(T/(2*M^2))*(h ya (xa k))⁻¹
    rw [hscale _ _ (hpoints k).1 hya]
    change _=L*(L*H (ya,xa k/M))⁻¹
    simp [mul_inv_rev,hL,mul_comm]
  have hrootA k : H (ya,xa k/M)=(t k)⁻¹ := by
    rw [←htA,inv_inv]
  have hrootB k : H (yb,xb k/M)=(t k+bnorm)⁻¹ := by
    have hh := (hroots k).2.2
    rw [htA] at hh
    change (H (yb,xb k/M))⁻¹=t k+bnorm at hh
    rw [←hh,inv_inv]
  have ht : t 0 < t 1 := mul_lt_mul_of_pos_left hu (by positivity)
  have htvec (i : Fin 2) : (![t 0,t 1] : Fin 2 → ℝ) i=t i := by fin_cases i <;> rfl
  have hh := hcompression F η x₀ y₀ ya yb bnorm (t 0) (t 1) (R^10*(Δ+1/M))
    (fun i => xa i/M) (fun i => xb i/M) hη hηsmall hx₀ hy₀ hya hyb hf hbound htests ht
    (by intro i; rw [htvec]; exact ⟨hnorm _ (hpoints i).1,hnorm _ (hpoints i).2,hrootA i,hrootB i⟩)
    (by intro i; rw [htvec]; exact hends i)
    hnear
  have hn : T*|γ|/(2*M^2) ≤ ‖((yb-ya,bnorm):ℝ × ℝ)‖ := by
    have he := norm_snd_le ((yb-ya,bnorm):ℝ × ℝ)
    simpa only [bnorm,Real.norm_eq_abs,abs_div,abs_mul,abs_of_pos hT,
      abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_nonneg (sq_nonneg M)] using he
  have hm := (mul_le_mul_of_nonneg_right hn (sub_nonneg.mpr ht.le)).trans hh
  have hm' := mul_le_mul_of_nonneg_right hm (by positivity : 0 ≤ 4*M^4)
  have he : (T*|γ|/(2*M^2)*(t 1-t 0))*(4*M^4)=T^2*|γ| *(u 1-u 0) := by
    dsimp only [t]
    field_simp
    ring
  rw [he] at hm'
  have hraw : T^2*|γ| *(u 1-u 0) ≤ 4*(C*R^10)*(Δ+1/M)*M^4 :=
    hm'.trans_eq (by ring)
  have hne i : h ya (xa i) ≠ 0 := by
    rw [hscale _ _ (hpoints i).1 hya]
    exact mul_ne_zero hL (hHne _ _ (hpoints i).1 hya)
  have hheight i : |h ya (xa i)| ≤ T*R/(2*M^2) := by
    rw [hscale _ _ (hpoints i).1 hya,abs_mul,abs_of_pos (by dsimp only [L]; positivity : 0 < L)]
    calc
      L*|H (ya,xa i/M)| ≤ L*R :=
        mul_le_mul_of_nonneg_left (hHbound _ _ (hpoints i).1 hya) (by dsimp only [L]; positivity)
      _ = _ := by dsimp only [L]; ring
  have hfinal := reciprocal_endpoint_curvature_bound (hne 0) (hne 1) hT hMpos
    hu.le (hheight 0) (hheight 1) hraw
  exact hfinal.trans_eq (by ring)



private theorem huxley_lower_endpoint_source_scale
    {κ γ L N R M C K Δg : ℝ}
    (hL : 0 < L) (hN : 0 < N) (hR : 1 ≤ R) (hM : 0 < M)
    (hC : 0 ≤ C) (hNL : (L*N)^2 ≤ M*R)
    (hlo : κ*L/(8*R^2) ≤ Δg)
    (hhi : |γ| *Δg ≤ C*(K*R^2/(L^2*N^2)+1/M)) :
    κ*|γ| *L^3*N^2 ≤ 8*C*(K+1)*R^4 := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hround : 1/M ≤ R^2/(L^2*N^2) := by
    apply (div_le_div_iff₀ hM (by positivity)).mpr
    nlinarith only [hNL,mul_nonneg hM.le (show 0 ≤ R^2-R by nlinarith only [hR])]
  have hbound := (mul_le_mul_of_nonneg_left hlo (abs_nonneg γ)).trans hhi
  have hh := hbound.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hround) hC)
  have hm := mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ 8*R^2*L^2*N^2)
  have he : |γ| *(κ*L/(8*R^2))*(8*R^2*L^2*N^2)=κ*|γ| *L^3*N^2 := by
    field_simp
  have he' : C*(K*R^2/(L^2*N^2)+R^2/(L^2*N^2))*(8*R^2*L^2*N^2)=8*C*(K+1)*R^4 := by
    field_simp
  rwa [he,he'] at hm

public  theorem reciprocal_fraction_strictMonoOn
    {e r v s l u : ℝ} (hdet : v*r-e*s=1)
    (hne : ∀ z∈Icc l u, e*z+v ≠ 0) :
    StrictMonoOn (fun z => (r*z+s)/(e*z+v)) (Icc l u) := by
  have hd z (hz : z∈Icc l u) :
      HasDerivAt (fun z => (r*z+s)/(e*z+v)) (1/(e*z+v)^2) z := by
    have hh := (((hasDerivAt_id z).const_mul r).add_const s).div
      (((hasDerivAt_id z).const_mul e).add_const v) (hne z hz)
    convert hh using 1
    · rfl
    · have he : r*(e*z+v)-(r*z+s)*e=1 := by linear_combination hdet
      simp only [id_eq,mul_one,he]
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc l u)
    (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
    (fun z hz => (hd z (interior_subset hz)).hasDerivWithinAt)
  intro z hz
  exact div_pos zero_lt_one (sq_pos_of_ne_zero (hne z (interior_subset hz)))



                                                                         
                                                                 
                                                                                              
private theorem positive_difference_quartic_lower_long_block_constraint
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Csrc : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < Csrc ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb γ Tsrc : ℝ)
    {σ δ T M N R L d K α β : ℝ} (x : Fin 8 → ℝ)
    {F : Fin 2 → ℝ → ℝ} (A : Fin 2 → ℤ) {W x₀ e r v s : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ},
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (0 < L) →
    ((L*N)^2 ≤ M*R) →
    (0 < d) →
    (0 ≤ K) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      x₁ y i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, r i ≠ 0) →
    (∀ i, v i*r i-e i*s i=1) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, d ≤ r i*y+s i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, r i*y+s i ≤ 2*d) →
    (StrictMono x) →
    (T*N*R^2=M^3) →
    (e 1=e 0 ∧ v 1=v 0 ∧ r 1=r 0+γ*e 0 ∧ s 1=s 0+γ*v 0) →
    0 < η → η ≤ η₀ → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun y i => (round (x₁ y i):ℝ)-(round (x₀ i):ℝ)
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
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
    let κ := modelPhaseThirdLower σ
    let Γ := (σ*(σ+1)+1)/κ
    let C := Γ*(32*K+9*quarticReciprocalConstant σ δ)
    let yp : Fin 2 → ℝ := ![ya,yb]
    let Src := fun y z => Tsrc*(Fsrc (z/M)-Fsrc (z/M+η*y))/(σsrc*η)
    let Hsrc := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc z.2-iteratedDeriv 2 Fsrc (z.2+η*z.1))/(σsrc*η)
    let center := (ycenter,(Hsrc (ycenter,xcenter))⁻¹)
    (∀ i, f i=fun z => Src (yp i) ((A i:ℝ)+z)) →
    (∀ z∈({x 0,x 7} : Finset ℝ), ∀ i,
      ‖((yp i,(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (x₁ z i)/2)⁻¹):ℝ × ℝ)-center‖ < a) →
    κ*|γ| *L^3*N^2 ≤ 8*Csrc*(C+1)*R^4 := by
  obtain ⟨η₀,a,Csrc,hη₀,hηcap,ha,_hac,hCsrc,hcompression⟩ :=
    positive_difference_physical_lower_endpoint_compression hσsrc hcsrc hUsrc
  refine ⟨η₀,a,Csrc,hη₀,hηcap,ha,hCsrc,?_⟩
  intro Fsrc η xcenter ycenter ya yb γ Tsrc σ δ T M N R L d K α β x F A W x₀ e r v s x₁
    hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀ hx₁ hr hdet hden hdenUpper hmono hscale
    htransport hη hηmax hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo
    f n μ ν D g H G hbase hpoint hsquare hgap hres κ Γ C yp Src Hsrc center hsource hlocalEnds
  have hxleft : x 0∈Icc (x 0) (x 7) := ⟨le_rfl,hmono.monotone (by decide)⟩
  have hxright : x 7∈Icc (x 0) (x 7) := ⟨hmono.monotone (by decide),le_rfl⟩
  have hηmax' : η ≤ 1/8 := hηmax.trans hηcap
  have hjet i k t : iteratedDeriv k (f i) t=
      iteratedDeriv k (Src (yp i)) ((A i:ℝ)+t) := by
    rw [hsource,iteratedDeriv_comp_const_add]
  have hrounded i t :
      iteratedDeriv 3 (f i) (round t)=
        iteratedDeriv 3 (Src (yp i)) (round ((A i:ℝ)+t)) := by
    rw [hjet,round_intCast_add,Int.cast_add]
  have hyp i : yp i∈Icc (1:ℝ) 2 := by fin_cases i <;> assumption
  have hcurvNe t (ht : t∈Icc (x 0) (x 7)) i :
      iteratedDeriv 2 (f i) (x₁ t i)/2 ≠ 0 := by
    let q := (A i:ℝ)+x₁ t i
    have hq : q∈Icc M (2*M) :=
      ⟨by dsimp only [q]; linarith only [hA i,(hx₁ _ ht i).1],
       by dsimp only [q]; linarith only [hW i,(hx₁ _ ht i).2]⟩
    have hqnorm : q/M∈Icc (3/4:ℝ) (9/4) := by
      constructor
      · apply (le_div_iff₀ hM).mpr
        linarith only [hq.1,hM]
      · apply (div_le_iff₀ hM).mpr
        linarith only [hq.2,hM]
    have hywide : yp i∈Icc (1/2:ℝ) 3 :=
      ⟨by linarith only [(hyp i).1],by linarith only [(hyp i).2]⟩
    have he := (positive_jets_difference_curvature_entry Fsrc hσsrc hcsrc hUsrc hη hηmax'
      hqnorm hywide hreg hjets htests 3 (by norm_num) (by norm_num)).1
    change iteratedDeriv 2 (fun u => (Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)) (q/M)=
      Hsrc (yp i,q/M) at he
    have hloH := positive_jets_difference_spatial_lower Fsrc hσsrc hcsrc hη hηmax'
      hqnorm hywide hreg htests 2 (by norm_num) (by norm_num)
    rw [he] at hloH
    have hneH : Hsrc (yp i,q/M) ≠ 0 :=
      abs_pos.mp (lt_of_lt_of_le (by positivity) hloH)
    have hd : iteratedDeriv 2 (Src (yp i)) q=Tsrc/M^2*Hsrc (yp i,q/M) :=
      positive_difference_physical_iteratedDeriv Fsrc hM (hM.trans_le hq.1)
        (mul_nonneg hη.le (by linarith only [(hyp i).1])) hreg 2
    rw [hjet]
    change iteratedDeriv 2 (Src (yp i)) q/2 ≠ 0
    rw [hd]
    exact div_ne_zero (mul_ne_zero (div_ne_zero hTsrc.ne' (pow_ne_zero 2 hM.ne')) hneH)
      (by norm_num)
  have hnumNe t (ht : t∈Icc (x 0) (x 7)) i : e i*t+v i ≠ 0 := by
    intro he
    have hh := hcurvNe t ht i
    rw [hpoint t ht i,he,zero_div] at hh
    exact hh rfl
  have hinvEq t (ht : t∈Icc (x 0) (x 7)) i :
      (iteratedDeriv 2 (f i) (x₁ t i)/2)⁻¹=(r i*t+s i)/(e i*t+v i) := by
    rw [hpoint t ht i,inv_div]
  have hinvMono i : StrictMonoOn
      (fun t => (iteratedDeriv 2 (f i) (x₁ t i)/2)⁻¹) (Icc (x 0) (x 7)) := by
    intro u hu w hw huw
    change (iteratedDeriv 2 (f i) (x₁ u i)/2)⁻¹ < (iteratedDeriv 2 (f i) (x₁ w i)/2)⁻¹
    rw [hinvEq u hu i,hinvEq w hw i]
    exact reciprocal_fraction_strictMonoOn (hdet i) (fun t ht => hnumNe t ht i) hu hw huw
  have hlocal z (hz : z∈Icc (x 0) (x 7)) i :
      ‖((yp i,(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (x₁ z i)/2)⁻¹):ℝ × ℝ)-center‖ < a := by
    have hl := hlocalEnds (x 0) (by simp) i
    have hu := hlocalEnds (x 7) (by simp) i
    have hlo := mul_le_mul_of_nonneg_left ((hinvMono i).monotoneOn hxleft hz hz.1)
      (by positivity : 0 ≤ Tsrc/(2*M^2))
    have hhi := mul_le_mul_of_nonneg_left ((hinvMono i).monotoneOn hz hxright hz.2)
      (by positivity : 0 ≤ Tsrc/(2*M^2))
    change max |yp i-center.1|
      |(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (x₁ (x 0) i)/2)⁻¹-center.2| < a at hl
    change max |yp i-center.1|
      |(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (x₁ (x 7) i)/2)⁻¹-center.2| < a at hu
    change max |yp i-center.1|
      |(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (x₁ z i)/2)⁻¹-center.2| < a
    refine max_lt_iff.mpr ⟨(max_lt_iff.mp hl).1,abs_lt.mpr ⟨?_,?_⟩⟩
    · linarith only [(abs_lt.mp (max_lt_iff.mp hl).2).1,hlo]
    · linarith only [(abs_lt.mp (max_lt_iff.mp hu).2).2,hhi]
  let μnew := fun y i => iteratedDeriv 3 (f i) (round (x₁ y i))/6
  obtain ⟨z₀,hz₀,z₁,hz₁,hG,hthird⟩ := physicalModelPhase_quartic_two_long_block_witnesses
    x hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀ hx₁ hr hdet
    hden hdenUpper hmono hbase hpoint hsquare hgap hres
  have hz₀' : z₀∈Icc (x 0) (x 7) :=
    ⟨hz₀.1.le,hz₀.2.le.trans (hmono.monotone (by decide))⟩
  have hz₁' : z₁∈Icc (x 0) (x 7) :=
    ⟨(hmono.monotone (by decide)).trans hz₁.1.le,hz₁.2.le⟩
  have hzorder : z₀ ≤ z₁ := hz₀.2.le.trans
    ((hmono.monotone (by decide : (3:Fin 8) ≤ 4)).trans hz₁.1.le)
  have hdpos z (hz : z∈Icc (x 0) (x 7)) i : 0 < D z i :=
    hd.trans_le (hden z hz i)
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hF₂ i := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl
  have hround := physicalModelPhase_halfCurvature_round_error hσ.le (hF₂ 0)
    hT hM (hA 0) (hW 0) (hx₀ 0)
  have hμbounds := physicalModelPhase_cubicCoefficient_bounds hσ hδ (hF₂ 0)
    hT hM (hA 0) (hW 0) hround.1
  have hμ : 0 < μ 0 := lt_of_lt_of_le (by positivity) hμbounds.1
  let z : Fin 2 → ℝ := ![z₀,z₁]
  let profile : ℝ → ℝ := fun t => iteratedDeriv 2 (f 0) (x₁ t 0)/2
  have hz p : z p∈Icc (x 0) (x 7) := by
    fin_cases p
    · exact hz₀'
    · exact hz₁'
  have hdiff : profile z₀-profile z₁=(z₁-z₀)/(D z₀ 0*D z₁ 0) := by
    dsimp only [profile]
    rw [hpoint z₀ hz₀' 0,hpoint z₁ hz₁' 0,
      div_sub_div _ _ (hdpos z₀ hz₀' 0).ne' (hdpos z₁ hz₁' 0).ne']
    congr 1
    dsimp only [D]
    linear_combination (z₁-z₀)*hdet 0
  have horder : profile z₁ ≤ profile z₀ := sub_nonneg.mp (by
    rw [hdiff]
    exact div_nonneg (sub_nonneg.mpr hzorder)
      (mul_pos (hdpos z₀ hz₀' 0) (hdpos z₁ hz₁' 0)).le)
  have hGid t (ht : t∈Icc (x 0) (x 7)) : profile t-e 0/r 0=3*μ 0*G t := by
    rw [show profile t=(e 0*t+v 0)/(r 0*t+s 0) from hpoint t ht 0]
    simpa only [mul_one,div_one] using
      (farey_curvature_coordinate_identity (u:=t) (t:=1) hμ.ne' (hr 0)
        one_ne_zero (by simpa only [mul_one] using (hdpos t ht 0).ne') (hdet 0))
  have hdiffG : profile z₀-profile z₁=3*μ 0*(G z₀-G z₁) := by
    linarith only [hGid z₀ hz₀',hGid z₁ hz₁']
  have hGorder : 0 ≤ G z₀-G z₁ := by
    apply (mul_nonneg_iff_of_pos_left (mul_pos (by norm_num : (0:ℝ)<3) hμ)).mp
    rw [← hdiffG]
    exact sub_nonneg.mpr horder
  rw [abs_sub_comm,abs_of_nonneg hGorder] at hG
  have hlo : κ*L/(8*R^2) ≤ profile z₀-profile z₁ := by
    have hmul := mul_le_mul_of_nonneg_left hG
      (mul_pos (by norm_num : (0:ℝ)<3) hμ).le
    calc
      _ = 3*(κ*T/(6*M^3))*(L*N/4) := by
        have hTval : T=M^3/(N*R^2) :=
          (eq_div_iff (by positivity)).mpr (by nlinarith only [hscale])
        rw [hTval]
        field_simp
        ring_nf
      _ ≤ 3*μ 0*(L*N/4) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hμbounds.1 (by norm_num : (0:ℝ) ≤ 3))
        (by positivity)
      _ ≤ _ := by linarith only [hmul,hdiffG]
  let Δ := C*R^2/(L^2*N^2)
  have hΔ : 0 ≤ Δ := (abs_nonneg _).trans (hthird z₀ (by simp))
  have hDmap t : D t 1=D t 0+γ*(e 0*t+v 0) := by
    dsimp only [D]
    rw [htransport.2.2.1,htransport.2.2.2]
    ring_nf
  have hratio t (ht : t∈Icc (x 0) (x 7)) : γ*profile t+1=D t 1/D t 0 := by
    change γ*(iteratedDeriv 2 (f 0) (x₁ t 0)/2)+1=_
    rw [hpoint t ht 0,hDmap]
    field_simp [(hdpos t ht 0).ne']
    ring_nf
  have hmap t (ht : t∈Icc (x 0) (x 7)) :
      iteratedDeriv 2 (f 1) (x₁ t 1)/2=profile t/(γ*profile t+1) := by
    rw [hratio t ht]
    change _=(iteratedDeriv 2 (f 0) (x₁ t 0)/2)/(D t 1/D t 0)
    rw [hpoint t ht 1,hpoint t ht 0,htransport.1,htransport.2.1]
    field_simp [(hdpos t ht 0).ne',(hdpos t ht 1).ne']
  have hinvMap t (ht : t∈Icc (x 0) (x 7)) :
      (iteratedDeriv 2 (f 1) (x₁ t 1)/2)⁻¹=(profile t)⁻¹+γ := by
    rw [hmap t ht,inv_div]
    have hp : profile t ≠ 0 := hcurvNe t ht 0
    rw [add_div,mul_div_cancel_right₀ γ hp,one_div,add_comm]
  have hthird' p :
      |μnew (z p) 1/μnew (z p) 0*(γ*profile (z p)+1)^3-1| ≤ Δ := by
    have hh := hthird (z p) (by fin_cases p <;> simp [z])
    change |μnew (z p) 1*(D (z p) 1)^3/(μnew (z p) 0*(D (z p) 0)^3)-1| ≤ Δ at hh
    have he : μnew (z p) 1/μnew (z p) 0*(D (z p) 1/D (z p) 0)^3=
        μnew (z p) 1*(D (z p) 1)^3/(μnew (z p) 0*(D (z p) 0)^3) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring_nf
    rw [hratio _ (hz p),he]
    exact hh
  let xa := fun p => (A 0:ℝ)+x₁ (z p) 0
  let xb := fun p => (A 1:ℝ)+x₁ (z p) 1
  have hphysical p : xa p∈Icc M (2*M) ∧ xb p∈Icc M (2*M) := by
    constructor
    · exact ⟨by dsimp only [xa]; linarith only [hA 0,(hx₁ _ (hz p) 0).1],
        by dsimp only [xa]; linarith only [hW 0,(hx₁ _ (hz p) 0).2]⟩
    · exact ⟨by dsimp only [xb]; linarith only [hA 1,(hx₁ _ (hz p) 1).1],
        by dsimp only [xb]; linarith only [hW 1,(hx₁ _ (hz p) 1).2]⟩
  have hua p : iteratedDeriv 2 (Src ya) (xa p)/2=profile (z p) := by
    exact (congrArg (fun u : ℝ => u/2) (hjet 0 2 (x₁ (z p) 0))).symm
  have hub p : iteratedDeriv 2 (Src yb) (xb p)/2=profile (z p)/(γ*profile (z p)+1) := by
    exact (congrArg (fun u : ℝ => u/2) (hjet 1 2 (x₁ (z p) 1))).symm.trans (hmap _ (hz p))
  have hzstrict : z₀ < z₁ := hz₀.2.trans_le
    ((hmono.monotone (by decide : (3:Fin 8) ≤ 4)).trans hz₁.1.le)
  have hh := hcompression Fsrc η xcenter ycenter ya yb γ Δ Tsrc M xa xb
    hη hηmax hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hΔ hphysical
    (by
      change (iteratedDeriv 2 (Src ya) (xa 0)/2)⁻¹ <
        (iteratedDeriv 2 (Src ya) (xa 1)/2)⁻¹
      rw [hua,hua]
      exact hinvMono 0 hz₀' hz₁' hzstrict)
    (by
      intro p
      change iteratedDeriv 2 (Src yb) (xb p)/2=
        (iteratedDeriv 2 (Src ya) (xa p)/2)/(γ*(iteratedDeriv 2 (Src ya) (xa p)/2)+1)
      rw [hua,hub])
    (by
      intro p
      have hh := hthird' p
      change |(iteratedDeriv 3 (f 1) (round (x₁ (z p) 1))/6)/
        (iteratedDeriv 3 (f 0) (round (x₁ (z p) 0))/6)*(γ*profile (z p)+1)^3-1| ≤ Δ at hh
      rw [hrounded,hrounded] at hh
      change |(iteratedDeriv 3 (Src yb) (round (xb p))/6)/
        (iteratedDeriv 3 (Src ya) (round (xa p))/6)*
        (γ*(iteratedDeriv 2 (Src ya) (xa p)/2)+1)^3-1| ≤ Δ
      rw [hua]
      exact hh)
    (by
      intro p
      change ‖((ya,(Tsrc/(2*M^2))*(iteratedDeriv 2 (Src ya) (xa p)/2)⁻¹):ℝ × ℝ)-center‖ < a ∧
        ‖((yb,(Tsrc/(2*M^2))*(iteratedDeriv 2 (Src ya) (xa p)/2)⁻¹+Tsrc*γ/(2*M^2)):ℝ × ℝ)-center‖ < a
      constructor
      · rw [hua]
        exact hlocal _ (hz p) 0
      · have he : (Tsrc/(2*M^2))*(iteratedDeriv 2 (Src ya) (xa p)/2)⁻¹+
            Tsrc*γ/(2*M^2)=(Tsrc/(2*M^2))*(iteratedDeriv 2 (f 1) (x₁ (z p) 1)/2)⁻¹ := by
          rw [hua,hinvMap _ (hz p)]
          ring_nf
        rw [he]
        exact hlocal _ (hz p) 1)
  change |γ| *|iteratedDeriv 2 (Src ya) (xa 1)/2-iteratedDeriv 2 (Src ya) (xa 0)/2| ≤
    Csrc*(Δ+1/M) at hh
  rw [hua,hua] at hh
  change |γ| *|profile z₁-profile z₀| ≤ Csrc*(Δ+1/M) at hh
  rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr horder)] at hh
  exact huxley_lower_endpoint_source_scale hL hN hR hM hCsrc.le hNL hlo hh


                                                                
                                                                        
                                                                     
theorem positive_difference_normalized_quartic_lower_long_block_constraint
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Csrc : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < Csrc ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb γ Tsrc : ℝ)
    {σ δ T M N R L d K α β : ℝ} (x : Fin 8 → ℝ)
    (A : Fin 2 → ℤ) {W x₀ e r v s : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ},
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*(![ya,yb] : Fin 2 → ℝ) i))/(σsrc*η)
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (0 < L) →
    ((L*N)^2 ≤ M*R) →
    (0 < d) →
    (0 ≤ K) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      x₁ y i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, r i ≠ 0) →
    (∀ i, v i*r i-e i*s i=1) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, d ≤ r i*y+s i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, r i*y+s i ≤ 2*d) →
    (StrictMono x) →
    (T*N*R^2=M^3) →
    (e 1=e 0 ∧ v 1=v 0 ∧ r 1=r 0+γ*e 0 ∧ s 1=s 0+γ*v 0) →
    0 < η → η ≤ η₀ → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun y i => (round (x₁ y i):ℝ)-(round (x₀ i):ℝ)
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
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
    let κ := modelPhaseThirdLower σ
    let Γ := (σ*(σ+1)+1)/κ
    let C := Γ*(32*K+9*quarticReciprocalConstant σ δ)
    let yp : Fin 2 → ℝ := ![ya,yb]
    let Hsrc := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc z.2-iteratedDeriv 2 Fsrc (z.2+η*z.1))/(σsrc*η)
    let center := (ycenter,(Hsrc (ycenter,xcenter))⁻¹)
    (∀ z∈({x 0,x 7} : Finset ℝ), ∀ i,
      ‖((yp i,(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (x₁ z i)/2)⁻¹):ℝ × ℝ)-center‖ < a) →
    κ*|γ| *L^3*N^2 ≤ 8*Csrc*(C+1)*R^4 := by
  obtain ⟨η₀,a,Csrc,hη₀,hηcap,ha,hCsrc,hcore⟩ :=
    positive_difference_quartic_lower_long_block_constraint hσsrc hcsrc hUsrc
  refine ⟨η₀,a,Csrc,hη₀,hηcap,ha,hCsrc,?_⟩
  intro Fsrc η xcenter ycenter ya yb γ Tsrc σ δ T M N R L d K α β x A W x₀ e r v s x₁
    F hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀ hx₁ hr hdet hden hdenUpper hmono hscale
    htransport hη hηmax hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo
    f n μ ν D g H G hbase hpoint hsquare hgap hres κ Γ C yp Hsrc center hlocalEnds
  let Src := fun y z => Tsrc*(Fsrc (z/M)-Fsrc (z/M+η*y))/(σsrc*η)
  have hsource i : f i=fun z => Src (yp i) ((A i:ℝ)+z) := by
    funext z
    dsimp only [f,heathBrownPhysicalPhase,F,Src,yp]
    field_simp
  exact hcore Fsrc η xcenter ycenter ya yb γ Tsrc x (F:=F) A
    hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀ hx₁ hr hdet hden hdenUpper hmono hscale
    htransport hη hηmax hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo
    hbase hpoint hsquare hgap hres hsource hlocalEnds


                                                                   
                                                                      
                                                                        
                                                                  
theorem positive_difference_actual_fourier_charted_triangular_constraints
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb Tsrc E : ℝ)
    (Uref : ℕ) (Refs : Finset ℝ) {Bselect gapLo gapHi : ℝ}
    (S : Finset ℕ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ}
    {x : ℕ → Fin 2 → ℝ},
    0 < η → η ≤ η₀ → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let Hsrc := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc z.2-iteratedDeriv 2 Fsrc (z.2+η*z.1))/(σsrc*η)
    let center := (ycenter,Hsrc (ycenter,xcenter))
    let centerInv := (ycenter,(Hsrc (ycenter,xcenter))⁻¹)
    (∀ j∈S, ∀ i,
      ‖((yp i,(2*M^2/Tsrc)*(rat j i:ℝ)):ℝ × ℝ)-center‖ < a ∧
      ‖((yp i,(Tsrc/(2*M^2))*(rat j i:ℝ)⁻¹):ℝ × ℝ)-centerInv‖ < a) →
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*N*R^2=M^3) →
    ((Q:ℝ)*N ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1))) →
    (∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den) →
    (0 < lambda) →
    (0 ≤ Uband) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ j∈S, ∀ i, lambda ≤ |(rat j i:ℝ)| ∧ |(rat j i:ℝ)| ≤ Uband) →
    (∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1) →
    (v*r-e*s=1) →
    (((0:ℝ) < r ∧ (e:ℝ)/r=gapLo) ∨
      ((r:ℝ) < 0 ∧ (e:ℝ)/r=gapHi)) →
    (0 < Bcut) →
    (s ≠ 0) →
    ((e:ℝ)/r∈Refs) →
    ((v:ℝ)/s∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ j∈S, ∀ i, x j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, ∀ i, x j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2) →
    (R^2 ≤ (r:ℝ)^2*(Uref:ℝ)) →
    (gapHi-gapLo ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    (N^10 ≤ M^3*R^7) →
    (∀ j∈S, (rat j 0:ℝ)∈Icc gapLo gapHi) →
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := ⌊Real.logb (5/4) ((gapHi-gapLo)/(12*ε))⌋₊+1
    let sourceColor := fun j i => (⌊((rat j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ j∈S, sourceColor j 0=sourceColor j 1) →
    6+Ccharts*(105+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1))) ≤ S.card →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=(rat j i:ℝ)) →
    let q := fun j i => (rat j i).den
    let mu := fun j i => iteratedDeriv 3 (f i) (round (x j i))/6
    let ell := fun j i => deriv (f i) (round (x j i))
    let b := fun j i => (⌊(q j i:ℝ)*ell j i⌋+(parity j i:ℕ) : ℤ)
    let cround := fun j i => round ((q j i:ℝ)*ell j i)
    let tau := fun j i => ((b j i:ℝ)-(q j i:ℝ)*ell j i)/2
    let dual := fun j i => -2*mu j i*(Real.sqrt (2/(3*mu j i*(q j i:ℝ))))^3
    let cloud := fun j i => (![Int.fract (-(vinv j i:ℝ)*b j i/q j i),
      Int.fract (-(vinv j i:ℝ)/q j i),dual j i/Real.sqrt K₀,
      (3*dual j i*tau j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ j∈S, b j 0-cround j 0=b j 1-cround j 1) →
    (∀ j∈S, ∀ a, |cloud j 0 a-cloud j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ j∈S, (Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3=(q j 1:ℝ)/q j 0) →
    (∀ j∈S, ((Mat 0:ℝ)*(rat j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3)=(rat j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ j∈S, ∀ i, x j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, ∀ i, x j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, |(anchor j:ℝ)-(rat j 0:ℝ)| ≤ ε) →
    (∀ j∈S, 256*((anchor j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ j∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 →
    61*Ccurv*Cphys ≤ Bcut →
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let Cthird := ((σ*(σ+1)+1)/κ)*(32*Kres+9*quarticReciprocalConstant σ δ)
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 6+Ccharts*(105+17*S₀.card) ∧
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    0 < L ∧
    ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) →
      κ*|(Mat 1:ℝ)| *L^3*N^4 ≤ 2*Cupper*(Cthird+1)*E^2*M^2) ∧
    ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) →
      κ*|(Mat 2:ℝ)| *L^3*N^2 ≤ 8*Clower*(Cthird+1)*R^4) ∧
    ∀ Bmajor Cmajor n : ℕ, Blabels ≤ Bmajor → Ccharts ≤ Cmajor → 0 < n →
      (6+Cmajor*(105+544*Bmajor))*n ≤ S.card →
      let Lblock := (2*κ/Cphys)*(n:ℝ)
      ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) →
        κ*|(Mat 1:ℝ)| *Lblock^3*N^4 ≤ 2*Cupper*(Cthird+1)*E^2*M^2) ∧
      ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) →
        κ*|(Mat 2:ℝ)| *Lblock^3*N^2 ≤ 8*Clower*(Cthird+1)*R^4) := by
  classical
  obtain ⟨aU,CU,haU,hCU,hupper⟩ :=
    positive_difference_normalized_quartic_upper_long_block_constraint hσsrc hcsrc hUsrc
  obtain ⟨η₀,aL,CL,hη₀,hηcap,haL,hCL,hlower⟩ :=
    positive_difference_normalized_quartic_lower_long_block_constraint hσsrc hcsrc hUsrc
  refine ⟨η₀,min aU aL,CU,CL,hη₀,hηcap,lt_min haU haL,hCU,hCL,?_⟩
  intro Fsrc η xcenter ycenter ya yb Tsrc E Uref Refs Bselect gapLo gapHi S Q K₀ inst
    rat vinv parity anchor Mat e r v s σ δ T M N R base Bcut lambda Uband θ A W x
    hη hηsmall hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
    yp F Hsrc center centerInv hlocal
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap
    Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor hS
    f hlevel q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize Blabels Cthird
  have hηmax : η ≤ 1/8 := hηsmall.trans hηcap
  have hselected := physicalModelPhase_actual_fourier_charted_reference_gap_quartic_witnesses
    Uref Refs (Bselect:=Bselect) (gapLo:=gapLo) (gapHi:=gapHi) S
    Q K₀ rat vinv parity anchor Mat e r v s
    (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (Bcut:=Bcut)
    (lambda:=lambda) (Uband:=Uband) (θ:=θ) (F:=F) (A:=fun i => (A i:ℝ)) (W:=W) (x:=x)
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap
    hsourceColor hS hlevel hcolor hnear hsmall hNR hRN hNcube hminscale
    hMatdet hMatt hMatmap hMatgamma hNtwo hL hU hanchor hcut hcount
  obtain ⟨_Schart,_hSchart,_hSchartMass,_G,_hG,_hGMass,_jref,_hjref,xref,hxr,hrest⟩ := hselected
  obtain ⟨d,l,w,hd,S₀,hS₀,hSmass,_hinside,j,z,curve,alpha,beta,
    hpairs,hmono,hLpos,hspan,hK,hcurve,hgap,hres⟩ := hrest hsize hD hΔ hBsize
  let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
  let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
  let vp : Fin 2 → ℤ := ![v,Mat 0*v+Mat 1*s]
  let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
  let Ep : Fin 2 → ℝ := fun i => ep i
  let Rp : Fin 2 → ℝ := fun i => rp i
  let Vp : Fin 2 → ℝ := fun i => vp i
  let Sp : Fin 2 → ℝ := fun i => sp i
  have hrp i : Rp i ≠ 0 := by
    have hh := (hxr i).1
    change 0 < rp i*r at hh
    intro hz
    change (rp i:ℝ)=0 at hz
    have hz' : rp i=0 := by exact_mod_cast hz
    rw [hz',zero_mul] at hh
    exact (lt_irrefl 0) hh
  have hdet i : Vp i*Rp i-Ep i*Sp i=1 := by
    have hd₀ : (v:ℝ)*r-e*s=1 := by exact_mod_cast hchart
    have hd₁ : (Mat 0:ℝ)*Mat 3-(Mat 1:ℝ)*Mat 2=1 := by exact_mod_cast hMatdet
    fin_cases i
    · exact hd₀
    · change ((Mat 0*v+Mat 1*s:ℤ):ℝ)*((Mat 2*e+Mat 3*r:ℤ):ℝ)-
        ((Mat 0*e+Mat 1*r:ℤ):ℝ)*((Mat 2*v+Mat 3*s:ℤ):ℝ)=1
      push_cast
      linear_combination ((v:ℝ)*r-e*s)*hd₁+hd₀
  have hxref i : xref i∈Ioo (1/2:ℝ) (W i-1/2) := (hxr i).2.1
  have hbase i : iteratedDeriv 2 (f i) (xref i)/2=Ep i/Rp i := (hxr i).2.2.1
  have hxcurve t (ht : t∈Icc (z 0) (z 7)) i :
      curve t i∈Ioo (1/2:ℝ) (W i-1/2) := ((hcurve t ht).2 i).1
  have hdenL t (ht : t∈Icc (z 0) (z 7)) i : d ≤ Rp i*t+Sp i :=
    ((hcurve t ht).2 i).2.1
  have hdenU t (ht : t∈Icc (z 0) (z 7)) i : Rp i*t+Sp i ≤ 2*d :=
    ((hcurve t ht).2 i).2.2.1
  have hpoint t (ht : t∈Icc (z 0) (z 7)) i :
      iteratedDeriv 2 (f i) (curve t i)/2=(Ep i*t+Vp i)/(Rp i*t+Sp i) :=
    ((hcurve t ht).2 i).2.2.2.1
  have hsquare t (ht : t∈Icc (z 0) (z 7)) i :
      |(round (curve t i):ℝ)-(round (xref i):ℝ)|^2 ≤ M*R :=
    ((hcurve t ht).2 i).2.2.2.2
  have hendlevel k i : iteratedDeriv 2 (f i) (curve (z k) i)/2=(rat (j k) i:ℝ) := by
    have hzk : z k∈Icc (z 0) (z 7) := ⟨hmono.monotone (by omega),hmono.monotone (by omega)⟩
    exact (hpoint _ hzk i).trans ((hpairs k).2 i).symm
  let Lsource := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
  have hupperBound : (Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) →
      κ*|(Mat 1:ℝ)| *Lsource^3*N^4 ≤ 2*CU*(Cthird+1)*E^2*M^2 := by
    intro htri
    have htransport : Ep 1=Ep 0+(Mat 1:ℝ)*Rp 0 ∧
        Vp 1=Vp 0+(Mat 1:ℝ)*Sp 0 ∧ Rp 1=Rp 0 ∧ Sp 1=Sp 0 := by
      simp [Ep,Rp,Vp,Sp,ep,rp,vp,sp,htri.1,htri.2.1,htri.2.2]
    apply hupper Fsrc η xcenter ycenter ya yb (Mat 1) Tsrc E z A
      hσ hδ hF hT hM hN hR hLpos hspan hd hK hA hW hxref hxcurve hrp hdet
      hdenL hdenU hmono hscale htransport hη hηmax hcenterx hcentery hya hyb
      hreg hjets htests hTsrc hMtwo hsourceScale hbase hpoint hsquare hgap hres
    intro t ht i
    rcases Finset.mem_insert.mp ht with he | he
    · subst t
      change ‖((yp i,(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (curve (z 0) i)/2)):ℝ × ℝ)-center‖ < aU
      rw [hendlevel]
      exact ((hlocal _ (hS₀ (hpairs 0).1) i).1).trans_le (min_le_left _ _)
    · have he' : t=z 7 := Finset.mem_singleton.mp he
      subst t
      change ‖((yp i,(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (curve (z 7) i)/2)):ℝ × ℝ)-center‖ < aU
      rw [hendlevel]
      exact ((hlocal _ (hS₀ (hpairs 7).1) i).1).trans_le (min_le_left _ _)
  have hlowerBound : (Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) →
      κ*|(Mat 2:ℝ)| *Lsource^3*N^2 ≤ 8*CL*(Cthird+1)*R^4 := by
    intro htri
    have htransport : Ep 1=Ep 0 ∧ Vp 1=Vp 0 ∧
        Rp 1=Rp 0+(Mat 2:ℝ)*Ep 0 ∧ Sp 1=Sp 0+(Mat 2:ℝ)*Vp 0 := by
      simp [Ep,Rp,Vp,Sp,ep,rp,vp,sp,htri.1,htri.2.1,htri.2.2,add_comm]
    apply hlower Fsrc η xcenter ycenter ya yb (Mat 2) Tsrc z A
      hσ hδ hF hT hM hN hR hLpos hspan hd hK hA hW hxref hxcurve hrp hdet
      hdenL hdenU hmono hscale htransport hη hηsmall hcenterx hcentery hya hyb
      hreg hjets htests hTsrc hMtwo hbase hpoint hsquare hgap hres
    intro t ht i
    rcases Finset.mem_insert.mp ht with he | he
    · subst t
      change ‖((yp i,(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (curve (z 0) i)/2)⁻¹):ℝ × ℝ)-centerInv‖ < aL
      rw [hendlevel]
      exact ((hlocal _ (hS₀ (hpairs 0).1) i).2).trans_le (min_le_right _ _)
    · have he' : t=z 7 := Finset.mem_singleton.mp he
      subst t
      change ‖((yp i,(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (curve (z 7) i)/2)⁻¹):ℝ × ℝ)-centerInv‖ < aL
      rw [hendlevel]
      exact ((hlocal _ (hS₀ (hpairs 7).1) i).2).trans_le (min_le_right _ _)
  refine ⟨S₀,hS₀,hSmass,hLpos,hupperBound,hlowerBound,?_⟩
  intro Bmajor Cmajor n hBmajor hCmajor hn hblocks Lblock
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hlength : Lblock ≤ Lsource :=
    charted_selected_source_length (by dsimp only [Blabels]; omega)
      (by dsimp only [Ccharts]; omega) hBmajor hCmajor hn hκ hCphys hSmass hblocks
  have hLblock : 0 ≤ Lblock := by dsimp only [Lblock]; positivity
  have hpower := pow_le_pow_left₀ hLblock hlength 3
  constructor
  · intro htri
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpower (mul_nonneg hκ.le (abs_nonneg _)))
      (by positivity : 0 ≤ N^4)).trans (hupperBound htri)
  · intro htri
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpower (mul_nonneg hκ.le (abs_nonneg _)))
      (sq_nonneg N)).trans (hlowerBound htri)

                                                                
                                                           

-- Exact proof abbreviations: every original parameter and premise is retained.
abbrev nativeHuxleyReference_physical_source_quartic_constants_nonneg := @physical_source_quartic_constants_nonneg
abbrev nativeHuxleyReference_finite_reference_closed_bracket := @finite_reference_closed_bracket
abbrev nativeHuxleyReference_reference_gap_count_of_closed_profile_width := @reference_gap_count_of_closed_profile_width
abbrev nativeHuxleyReference_reference_chart_fraction_antitone := @reference_chart_fraction_antitone
abbrev nativeHuxleyReference_finite_occupied_cubic_tail_sum := @finite_occupied_cubic_tail_sum
abbrev nativeHuxleyReference_quotient_block_mass := @quotient_block_mass
abbrev nativeHuxleyReference_charted_selected_source_length := @charted_selected_source_length
abbrev nativeHuxleyReference_huxley_completed_narrowed_source_sieve := @huxley_completed_narrowed_source_sieve
abbrev nativeHuxleyReference_huxley_actual_dual_source_box := @huxley_actual_dual_source_box
abbrev nativeHuxleyReference_eventually_reference_chart_majorants := @eventually_reference_chart_majorants
abbrev nativeHuxleyReference_physical_reference_chart_ratio := @physical_reference_chart_ratio
abbrev nativeHuxleyReference_eventually_physical_reference_chart_budgets := @eventually_physical_reference_chart_budgets
abbrev nativeHuxleyReference_positive_difference_physical_upper_endpoint_compression := @positive_difference_physical_upper_endpoint_compression
abbrev nativeHuxleyReference_positive_difference_physical_lower_endpoint_compression := @positive_difference_physical_lower_endpoint_compression
abbrev nativeHuxleyReference_reciprocal_fraction_strictMonoOn := @reciprocal_fraction_strictMonoOn

end TaoTrudgianYang2025.HuxleyRationalPhase

-- Generated closures: source context is replayed in the next part.
end
end
