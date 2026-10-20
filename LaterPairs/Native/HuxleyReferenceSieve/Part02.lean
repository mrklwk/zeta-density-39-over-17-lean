module
public import LaterPairs.Native.HuxleyReferenceSieve.Part01

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


                                                                  
                                            
theorem fareySector_large_beta_bound {N : ℕ} {l w α β δ : ℝ}
    (hl : 0 < l) (hlw : l ≤ w) (hN : 0 < N)
    (hR : 40*w*(N:ℝ) ≤ (HuxleyLinearForm.fareySector N l w).card) (hδ : 0 ≤ δ)
    (hnear : ∀ p ∈ HuxleyLinearForm.fareySector N l w,
      ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ) :
    ((HuxleyLinearForm.fareySector N l w).card:ℝ) ≤ 96*δ*(w*(N:ℝ))*(N:ℝ) ∨
      |β-(round β:ℤ)| ≤ 8*(w*(N:ℝ))*δ/(HuxleyLinearForm.fareySector N l w).card := by
  classical
  let S := HuxleyLinearForm.fareySector N l w
  let E := S.image Prod.fst
  let M := w*(N:ℝ)
  have hw : 0 < w := hl.trans_le hlw
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hM : 0 < M := mul_pos hw hNR
  have hSR : (0:ℝ) < S.card := by
    have hh : 40*M ≤ (S.card:ℝ) := by simpa only [M,mul_assoc] using hR
    exact (by positivity : 0 < 40*M).trans_le hh
  have hmaps : ∀ p∈S, p.1 ∈ E := fun p hp => Finset.mem_image_of_mem Prod.fst hp
  have hEne : E.Nonempty := by
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (by exact_mod_cast hSR : 0 < S.card)
    exact ⟨p.1,hmaps p hp⟩
  have hE : (E.card:ℝ) ≤ M := fareySector_numerator_projection_card_le hw.le
  obtain ⟨n,_hn,hcount⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    hmaps hEne (b := (S.card:ℝ)/M) (by
      rw [nsmul_eq_mul]
      calc
        (E.card:ℝ)*((S.card:ℝ)/M) ≤ M*((S.card:ℝ)/M) :=
          mul_le_mul_of_nonneg_right hE (div_nonneg hSR.le hM.le)
        _ = (S.card:ℝ) := mul_div_cancel₀ _ hM.ne')
  let T := S.filter (fun p => p.1=n)
  change (S.card:ℝ)/M ≤ (T.card:ℝ) at hcount
  have hTne : T.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp ((div_pos hSR hM).trans_le hcount))
  obtain ⟨p₀,hp₀⟩ := hTne
  let D := T.image (fun p => p.2-p₀.2)
  let P := insert 1 ((D.erase 0).image Int.natAbs)
  have hDcard : D.card=T.card := Finset.card_image_of_injOn (by
    intro p hp q hq he
    apply Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm)
    dsimp at he
    omega)
  have hTP : (T.card:ℝ) ≤ 2*(P.card:ℝ)+1 := by
    have hc := HuxleyLinearForm.card_le_two_mul_nonzero_abs_card_add_one D
    have hsub : (D.erase 0).image Int.natAbs ⊆ P := Finset.subset_insert _ _
    have hh := Finset.card_le_card hsub
    rw [hDcard] at hc
    exact_mod_cast (show T.card ≤ 2*P.card+1 by omega)
  have hcard : (S.card:ℝ) ≤ 4*M*(P.card:ℝ) := by
    have hc := (div_le_iff₀ hM).mp hcount
    have ht := mul_le_mul_of_nonneg_left hTP hM.le
    have hlarge : 40*M ≤ (S.card:ℝ) := by simpa only [M,mul_assoc] using hR
    nlinarith only [hc,ht,hlarge]
  have hPne : P.Nonempty := ⟨1,Finset.mem_insert_self _ _⟩
  let L := P.max' hPne
  have hL : L ∈ P := Finset.max'_mem _ _
  have hLpos : 0 < L := by have hh := Finset.le_max' P 1 (Finset.mem_insert_self _ _); omega
  have hden (p : ℤ × ℤ) (hp : p ∈ S) : 0 ≤ (p.2:ℝ) ∧ (p.2:ℝ) ≤ N := by
    have hh := (HuxleyLinearForm.mem_fareySector_iff hl hw.le).mp hp
    exact ⟨by exact_mod_cast (show 0 ≤ p.2 by omega),by exact_mod_cast hh.2.1⟩
  have hPsize : ∀ k ∈ P, 1 ≤ k ∧ (k:ℝ) ≤ N := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact ⟨le_rfl,by exact_mod_cast hN⟩
    · obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hd0,hd⟩ := Finset.mem_erase.mp hd
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hd
      refine ⟨Nat.pos_of_ne_zero (by simpa using hd0),?_⟩
      rw [Nat.cast_natAbs,Int.cast_abs,Int.cast_sub]
      have hpnum := hden p (Finset.mem_filter.mp hp).1
      have hp₀num := hden p₀ (Finset.mem_filter.mp hp₀).1
      exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hdiff (p r : ℤ × ℤ) (hp : p ∈ S) (hr : r ∈ S) (he : p.1=r.1) :
      ∃ b : ℤ, |((p.2-r.2:ℤ):ℝ)*β-b| ≤ 2*δ := by
    obtain ⟨bp,hbp⟩ := hnear p hp
    obtain ⟨br,hbr⟩ := hnear r hr
    refine ⟨bp-br,?_⟩
    have hid : ((p.2-r.2:ℤ):ℝ)*β-((bp-br:ℤ):ℝ) =
        ((p.1:ℝ)*α+(p.2:ℝ)*β-bp)-((r.1:ℝ)*α+(r.2:ℝ)*β-br) := by
      rw [he]; push_cast; ring
    rw [hid]
    exact (abs_sub _ _).trans (by linarith)
  have hPnear : ∀ k ∈ P, ∃ b : ℤ, |(k:ℝ)*β-b| ≤ 2*δ := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · obtain ⟨m,n,hm,hm1⟩ := fareySector_consecutive_denominators hl hlw hN hR
      simpa only [Prod.snd,add_sub_cancel_left,Int.cast_one,Nat.cast_one,one_mul] using
        hdiff (m,n+1) (m,n) hm1 hm rfl
    · obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hd).2
      obtain ⟨b,hb⟩ := hdiff p p₀ (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp₀).1
        ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hp₀).2.symm)
      rcases Int.natAbs_eq (p.2-p₀.2) with he | he
      · refine ⟨b,?_⟩
        have heR : ((p.2-p₀.2:ℤ):ℝ) = ((p.2-p₀.2).natAbs:ℝ) := by
          simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ℝ)) he
        rwa [← heR]
      · refine ⟨-b,?_⟩
        have heR : ((p.2-p₀.2:ℤ):ℝ) = -((p.2-p₀.2).natAbs:ℝ) := by
          simpa only [Int.cast_natCast,Int.cast_neg] using congrArg (fun z : ℤ => (z:ℝ)) he
        have hid : ((p.2-p₀.2).natAbs:ℝ)*β-((-b:ℤ):ℝ) = -(((p.2-p₀.2:ℤ):ℝ)*β-b) := by
          rw [heR,Int.cast_neg]; ring
        rwa [hid,abs_neg]
  rcases HuxleyLinearForm.linear_form_dichotomy P hLpos (by positivity)
    (fun k hk => ⟨(hPsize k hk).1,Finset.le_max' P k hk⟩) hPnear with hc | ⟨q,_hq,_hqL,hdvd,a,ha⟩
  · left
    have hm := mul_le_mul_of_nonneg_left (hPsize L hL).2 (show 0 ≤ 24*δ by positivity)
    have hc' : (P.card:ℝ) ≤ 24*δ*(N:ℝ) := by nlinarith only [hc,hm]
    have ht := mul_le_mul_of_nonneg_left hc' (show 0 ≤ 4*M by positivity)
    
    dsimp only [M] at hcard ht
    nlinarith only [hcard,ht]
  · right
    have hq : q=1 := Nat.dvd_one.mp (hdvd 1 (Finset.mem_insert_self _ _))
    rw [hq] at ha
    simp only [Nat.cast_one,one_mul] at ha
    have ht := mul_le_mul_of_nonneg_left hcard (abs_nonneg (β-(a:ℝ)))
    have hh := mul_le_mul_of_nonneg_left ha (show 0 ≤ 4*M by positivity)
    apply (round_le β a).trans
    apply (le_div_iff₀ hSR).mpr
    dsimp only [M] at ht hh
    nlinarith only [ht,hh]

                                                                   
                                                                  
theorem fareySector_small_error_bounds_all_slopes
    {N : ℕ} {l μ B α β δ : ℝ}
    (hl : 0 < l) (hμ : 0 ≤ μ) (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hR : max ((μ-l)*(N:ℝ)^2/B) 2 ≤ (HuxleyLinearForm.fareySector N l μ).card)
    (hsmall : (max 1 μ*(N:ℝ))*δ ≤ 1/(96*B))
    (hnear : ∀ p ∈ HuxleyLinearForm.fareySector N l μ,
      ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ) :
    |α-(round α:ℤ)| ≤ 8*(N:ℝ)*δ/(HuxleyLinearForm.fareySector N l μ).card ∧
    |β-(round β:ℤ)| ≤ 8*(μ*(N:ℝ))*δ/(HuxleyLinearForm.fareySector N l μ).card := by
  classical
  let S := HuxleyLinearForm.fareySector N l μ
  have hμ0 : 0 ≤ μ := hμ
  have hB0 : 0 < B := by linarith
  have hR2 : 2 ≤ S.card := by
    exact_mod_cast (le_trans (le_max_right ((μ-l)*(N:ℝ)^2/B) 2) hR)
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p₀,hp₀,hmax⟩ := S.exists_max_image Prod.snd hSne
  obtain ⟨p,hp,hne⟩ := Finset.exists_mem_ne (by omega : 1 < S.card) p₀
  obtain ⟨r,hr,hrunit⟩ := HuxleyLinearForm.fareySector_exists_unit_determinant hl hμ0 hp₀ hp hne (hmax p hp)
  obtain ⟨hn₀,hn₀N,hcop₀,_hl₀,hu₀⟩ := (HuxleyLinearForm.mem_fareySector_iff hl hμ0).mp hp₀
  have hn₀pos : 0 < p₀.2 := by omega
  let f : ℤ × ℤ → ℤ := fun t => p₀.1*t.2-p₀.2*t.1
  let D := S.image f
  have hinj : Set.InjOn f S := by
    intro t ht u hu he
    exact HuxleyLinearForm.maximal_denominator_determinant_injective hn₀pos hcop₀
      ⟨((HuxleyLinearForm.mem_fareySector_iff hl hμ0).mp ht).1,hmax t ht⟩
      ⟨((HuxleyLinearForm.mem_fareySector_iff hl hμ0).mp hu).1,hmax u hu⟩ he
  have hDcard : D.card=S.card := Finset.card_image_of_injOn hinj
  have hunit : ∃ d ∈ D, d.natAbs=1 := by
    refine ⟨f r,Finset.mem_image.mpr ⟨r,hr,rfl⟩,?_⟩
    have h : |f r|=1 := hrunit
    exact Int.ofNat_inj.mp ((Int.natCast_natAbs (f r)).trans h)
  have hsize : ∀ d ∈ D, (d.natAbs:ℝ) ≤ B*(D.card:ℝ) := by
    intro d hd
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hd
    have hb := HuxleyLinearForm.fareySector_determinant_bound hl hμ0 hp₀ ht
    have hw : (μ-l)*(N:ℝ)^2 ≤ B*(S.card:ℝ) := by
      have h := le_trans (le_max_left ((μ-l)*(N:ℝ)^2/B) 2) hR
      have hd := (div_le_iff₀ hB0).mp h
      nlinarith only [hd]
    rw [hDcard,Nat.cast_natAbs,Int.cast_abs]
    exact hb.trans hw
  have hNleH : (N:ℝ) ≤ max 1 μ*(N:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right (le_max_left (1:ℝ) μ) (Nat.cast_nonneg N)
    simpa only [one_mul] using hh
  have hMleH : μ*(N:ℝ) ≤ max 1 μ*(N:ℝ) :=
    mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) μ) (Nat.cast_nonneg N)
  have hbase : 96*B*(max 1 μ*(N:ℝ))*δ ≤ 1 := by
    have h := (le_div_iff₀ (by positivity : 0 < 96*B)).mp hsmall
    nlinarith only [h]
  have hsmallα : 36*B*(2*(N:ℝ)*δ) < 1 := by
    have h := mul_le_mul_of_nonneg_left hNleH (by positivity : 0 ≤ B*δ)
    nlinarith only [h,hbase]
  have hsmallβ : 36*B*(2*(μ*(N:ℝ))*δ) < 1 := by
    have h := mul_le_mul_of_nonneg_left hMleH (by positivity : 0 ≤ B*δ)
    nlinarith only [h,hbase]
  obtain ⟨b₀,hb₀⟩ := hnear p₀ hp₀
  have hnearα : ∀ d ∈ D, ∃ b : ℤ, |(d:ℝ)*α-b| ≤ 2*(N:ℝ)*δ := by
    intro d hd
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨b,hb⟩ := hnear t ht
    obtain ⟨hn,hnN,_hc,_hl,_hu⟩ := (HuxleyLinearForm.mem_fareySector_iff hl hμ0).mp ht
    have htn : |(t.2:ℝ)| ≤ N := by
      rw [abs_of_nonneg (by exact_mod_cast (show 0 ≤ t.2 by omega))]
      exact_mod_cast hnN
    have htn₀ : |(p₀.2:ℝ)| ≤ N := by
      rw [abs_of_nonneg (by exact_mod_cast hn₀pos.le)]
      exact_mod_cast hn₀N
    exact ⟨t.2*b₀-p₀.2*b,HuxleyLinearForm.determinant_alpha_near p₀.1 p₀.2 t.1 t.2 b₀ b htn htn₀ hb₀ hb⟩
  have hnum : ∀ t ∈ S, |(t.1:ℝ)| ≤ μ*(N:ℝ) := by
    intro t ht
    obtain ⟨hn,hnN,_hc,hlower,hupper⟩ := (HuxleyLinearForm.mem_fareySector_iff hl hμ0).mp ht
    have hnR : (0:ℝ) ≤ t.2 := by exact_mod_cast (show 0 ≤ t.2 by omega)
    have htpos : (0:ℝ) ≤ t.1 := (mul_nonneg hl.le hnR).trans hlower
    rw [abs_of_nonneg htpos]
    exact hupper.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hnN) hμ0)
  have hnearβ : ∀ d ∈ D, ∃ b : ℤ, |(d:ℝ)*β-b| ≤ 2*(μ*(N:ℝ))*δ := by
    intro d hd
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨b,hb⟩ := hnear t ht
    exact ⟨p₀.1*b-t.1*b₀,HuxleyLinearForm.determinant_beta_near p₀.1 p₀.2 t.1 t.2 b₀ b
      (hnum t ht) (hnum p₀ hp₀) hb₀ hb⟩
  have ha := HuxleyLinearForm.small_error_integer_of_unit_determinant D (by positivity) hunit hsize hsmallα hnearα
  have hb := HuxleyLinearForm.small_error_integer_of_unit_determinant D (by positivity) hunit hsize hsmallβ hnearβ
  rw [hDcard] at ha hb
  constructor
  · apply ha.trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    nlinarith only [mul_nonneg (Nat.cast_nonneg N) hδ]
  · apply hb.trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    nlinarith only [mul_nonneg (mul_nonneg hμ0 (Nat.cast_nonneg N)) hδ]

                                                                        
                                                                    
theorem fareySector_alpha_of_beta_bound {N : ℕ} {l w B α β δ : ℝ}
    (hl : 0 < l) (hlw : l ≤ w) (hN : 0 < N) (hB : 1 ≤ B)
    (hR : w*(N:ℝ) ≤ (HuxleyLinearForm.fareySector N l w).card)
    (hR2 : 2 ≤ (HuxleyLinearForm.fareySector N l w).card)
    (hdensity : (w-l)*(N:ℝ)^2 ≤ B*(HuxleyLinearForm.fareySector N l w).card)
    (hδ : 0 ≤ δ)
    (hβ : |β-(round β:ℤ)| ≤ 8*(w*(N:ℝ))*δ/(HuxleyLinearForm.fareySector N l w).card)
    (hnear : ∀ p∈HuxleyLinearForm.fareySector N l w,
      ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ) :
    ((HuxleyLinearForm.fareySector N l w).card:ℝ) ≤ 324*B*δ*(w*(N:ℝ))*(N:ℝ) ∨
      |α-(round α:ℤ)| ≤ 27*B*(N:ℝ)*δ/(HuxleyLinearForm.fareySector N l w).card := by
  classical
  let S := HuxleyLinearForm.fareySector N l w
  let E := S.image Prod.fst
  let D := E.image Int.natAbs
  let M := w*(N:ℝ)
  let ε := 9*δ*M*(N:ℝ)/(S.card:ℝ)
  have hw : 0 < w := hl.trans_le hlw
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hM : 0 < M := mul_pos hw hNR
  have hSR : (0:ℝ) < S.card := hM.trans_le hR
  have hB0 : 0 ≤ B := by linarith only [hB]
  have hnum : ∀ m∈E, 1 ≤ m ∧ (m:ℝ) ≤ M := by
    intro m hm
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hn,hnN,_hc,hlo,hhi⟩ := (HuxleyLinearForm.mem_fareySector_iff hl hw.le).mp hp
    have hnp : (0:ℝ) < p.2 := by exact_mod_cast (show 0 < p.2 by omega)
    have hmp : (0:ℝ) < p.1 := (mul_pos hl hnp).trans_le hlo
    have hmZ : 0 < p.1 := by exact_mod_cast hmp
    exact ⟨by omega,hhi.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hnN) hw.le)⟩
  have hDcard : D.card=E.card := Finset.card_image_of_injOn (by
    intro m hm n hn he
    exact (Int.natAbs_inj_of_nonneg_of_nonneg (by have hh := hnum m hm; omega)
      (by have hh := hnum n hn; omega)).mp he)
  have hdens := fareySector_numerator_card_lower hl hlw hN hB hR hdensity
  change M ≤ 3*B*(E.card:ℝ) at hdens
  rw [←hDcard] at hdens
  have hDsize : ∀ m∈D, 1 ≤ m ∧ (m:ℝ) ≤ M := by
    intro m hm
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hm
    have hh := hnum n hn
    have he : (n.natAbs:ℤ)=n := (Int.natCast_natAbs n).trans (abs_of_nonneg (by omega))
    refine ⟨by exact_mod_cast (show (1:ℤ) ≤ n.natAbs by omega),?_⟩
    have heR : (n.natAbs:ℝ)=(n:ℝ) := by
      simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ℝ)) he
    rw [heR]
    exact hh.2
  have hDne : D.Nonempty := by
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (by exact_mod_cast hSR : 0 < S.card)
    exact ⟨p.1.natAbs,Finset.mem_image_of_mem Int.natAbs (Finset.mem_image_of_mem Prod.fst hp)⟩
  let L := D.max' hDne
  have hLmem : L∈D := Finset.max'_mem _ _
  have hL : 0 < L := (hDsize L hLmem).1
  have hLM : (L:ℝ) ≤ M := (hDsize L hLmem).2
  have hDnear : ∀ m∈D, ∃ b : ℤ, |(m:ℝ)*α-b| ≤ ε := by
    intro m hm
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hn₁,hnN,_hc,hlo,_hhi⟩ := (HuxleyLinearForm.mem_fareySector_iff hl hw.le).mp hp
    have hn0 : (0:ℝ) ≤ p.2 := by exact_mod_cast (show 0 ≤ p.2 by omega)
    have hnR : (p.2:ℝ) ≤ N := by exact_mod_cast hnN
    have hm0 : (0:ℝ) ≤ p.1 := (mul_nonneg hl.le hn0).trans hlo
    obtain ⟨b,hb⟩ := hnear p hp
    refine ⟨b-p.2*(round β),?_⟩
    have he : (p.1.natAbs:ℝ)=(p.1:ℝ) := by
      rw [Nat.cast_natAbs,Int.cast_abs,abs_of_nonneg hm0]
    rw [he]
    have hid : (p.1:ℝ)*α-((b-p.2*(round β):ℤ):ℝ) =
        ((p.1:ℝ)*α+(p.2:ℝ)*β-b)-(p.2:ℝ)*(β-(round β:ℤ)) := by push_cast; ring
    rw [hid]
    apply (abs_sub _ _).trans
    rw [abs_mul,abs_of_nonneg hn0]
    have ha := mul_le_mul hnR hβ (abs_nonneg _) hNR.le
    have hs := mul_le_mul_of_nonneg_left (fareySector_card_le_rectangle_all_slopes (N:=N) (l:=l) hw.le) hδ
    have hβR := (le_div_iff₀ hSR).mp (show (p.2:ℝ)*|β-(round β:ℤ)| ≤
        ((N:ℝ)*(8*M*δ))/(S.card:ℝ) by simpa only [mul_div_assoc,M] using ha)
    apply (le_div_iff₀ hSR).mpr
    have hbR := mul_le_mul_of_nonneg_right hb hSR.le
    dsimp only [M]
    nlinarith only [hs,hβR,hbR]
  rcases HuxleyLinearForm.linear_form_dichotomy D hL
    (show 0 ≤ ε by dsimp [ε]; positivity)
    (fun m hm => ⟨(hDsize m hm).1,Finset.le_max' D m hm⟩) hDnear
    with hc | ⟨q,_hq,_hqL,hdvd,a,ha⟩
  · left
    have heps : 0 ≤ ε := by dsimp [ε]; positivity
    have hh := mul_le_mul_of_nonneg_left hLM (show 0 ≤ 12*ε by positivity)
    have hcount : (D.card:ℝ) ≤ 12*ε*M := hc.trans hh
    have hcR := (le_div_iff₀ hSR).mp (show (D.card:ℝ) ≤
      (108*δ*M^2*(N:ℝ))/(S.card:ℝ) by convert hcount using 1; dsimp [ε]; ring)
    have hdR := mul_le_mul_of_nonneg_right hdens hSR.le
    have hcB := mul_le_mul_of_nonneg_left hcR (show 0 ≤ 3*B by positivity)
    apply (mul_le_mul_iff_right₀ hM).mp
    change M*(S.card:ℝ) ≤ M*(324*B*δ*M*(N:ℝ))
    nlinarith only [hdR,hcB]
  · right
    have hq : q=1 := fareySector_numerator_common_divisor hl hw.le hR2 (by
      intro p hp
      exact hdvd p.1.natAbs (Finset.mem_image_of_mem Int.natAbs (Finset.mem_image_of_mem Prod.fst hp)))
    rw [hq] at ha
    simp only [Nat.cast_one,one_mul] at ha
    have haR := (le_div_iff₀ hSR).mp ha
    have hdA := mul_le_mul_of_nonneg_left hdens (abs_nonneg (α-(a:ℝ)))
    have hdAR := mul_le_mul_of_nonneg_right hdA hSR.le
    have haB := mul_le_mul_of_nonneg_left haR (show 0 ≤ 3*B by positivity)
    apply (round_le α a).trans
    apply (le_div_iff₀ hSR).mpr
    apply (mul_le_mul_iff_right₀ hM).mp
    nlinarith only [hdAR,haB]

                                                                    
                                                                               
theorem fareySector_bounded_density_dichotomy_all_slopes
    {N : ℕ} {l w B α β δ : ℝ}
    (hl : 0 < l) (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hR : max ((w-l)*(N:ℝ)^2/B) 2 ≤ (HuxleyLinearForm.fareySector N l w).card)
    (hnear : ∀ p∈HuxleyLinearForm.fareySector N l w,
      ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ) :
    ((HuxleyLinearForm.fareySector N l w).card:ℝ) ≤ 3840*B*δ*(w*(N:ℝ))*(N:ℝ) ∨
      (|α-(round α:ℤ)| ≤ 27*B*(N:ℝ)*δ/(HuxleyLinearForm.fareySector N l w).card ∧
       |β-(round β:ℤ)| ≤ 20*B*(w*(N:ℝ))*δ/(HuxleyLinearForm.fareySector N l w).card) := by
  have hB0 : 0 < B := by linarith only [hB]
  have hR2R : (2:ℝ) ≤ (HuxleyLinearForm.fareySector N l w).card :=
    (le_max_right _ _).trans hR
  have hR2 : 2 ≤ (HuxleyLinearForm.fareySector N l w).card := by exact_mod_cast hR2R
  have hSne : (HuxleyLinearForm.fareySector N l w).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hw : 0 ≤ w := by
    by_contra hh
    have hemp : HuxleyLinearForm.fareySector N l w = ∅ := by
      unfold HuxleyLinearForm.fareySector
      have hwN : w*(N:ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hh) (Nat.cast_nonneg N)
      have hf : ⌊w*(N:ℝ)⌋ ≤ (0:ℤ) := by
        exact_mod_cast (Int.floor_le (w*(N:ℝ))).trans hwN
      simp [Finset.Icc_eq_empty_of_lt (show ⌊w*(N:ℝ)⌋ < (1:ℤ) by omega)]
    rw [hemp] at hSne
    exact Finset.not_nonempty_empty hSne
  obtain ⟨p,hp⟩ := hSne
  obtain ⟨hn,hnN,_hc,hlo,hhi⟩ := (HuxleyLinearForm.mem_fareySector_iff hl hw).mp hp
  have hN : 0 < N := by omega
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hnR : (0:ℝ) < p.2 := by exact_mod_cast (show 0 < p.2 by omega)
  have hlw : l ≤ w := (mul_le_mul_iff_left₀ hnR).mp (hlo.trans hhi)
  have hwp : 0 < w := hl.trans_le hlw
  have hprod : 0 ≤ δ*(w*(N:ℝ))*(N:ℝ) := by positivity
  have hBprod := mul_le_mul_of_nonneg_right hB hprod
  have halpha : 8*(N:ℝ)*δ ≤ 27*B*(N:ℝ)*δ := by
    have hh := mul_le_mul_of_nonneg_right hB (show 0 ≤ (N:ℝ)*δ by positivity)
    nlinarith only [hh,mul_nonneg hNR.le hδ]
  have hbeta : 8*(w*(N:ℝ))*δ ≤ 20*B*(w*(N:ℝ))*δ := by
    have hh := mul_le_mul_of_nonneg_right hB (show 0 ≤ (w*(N:ℝ))*δ by positivity)
    nlinarith only [hh,mul_nonneg (mul_nonneg hw hNR.le) hδ]
  by_cases hw1 : 1 ≤ w
  · rcases HuxleyLinearForm.fareySector_bounded_density_dichotomy hl hw1 hB hδ hR hnear
      with hbad | ⟨ha,hb⟩
    · exact Or.inl (by nlinarith only [hbad,hBprod,hprod])
    · exact Or.inr ⟨ha.trans (div_le_div_of_nonneg_right halpha (Nat.cast_nonneg _)),hb⟩
  have hwle : w ≤ 1 := le_of_lt (lt_of_not_ge hw1)
  have hdensity : (w-l)*(N:ℝ)^2 ≤ B*(HuxleyLinearForm.fareySector N l w).card := by
    have hh := (div_le_iff₀ hB0).mp ((le_max_left _ _).trans hR)
    nlinarith only [hh]
  by_cases hsmall : (N:ℝ)*δ ≤ 1/(96*B)
  · have hs : (max 1 w*(N:ℝ))*δ ≤ 1/(96*B) := by
      simpa only [max_eq_left hwle,one_mul] using hsmall
    obtain ⟨ha,hb⟩ := fareySector_small_error_bounds_all_slopes hl hw hB hδ hR hs hnear
    exact Or.inr ⟨ha.trans (div_le_div_of_nonneg_right halpha (Nat.cast_nonneg _)),
      hb.trans (div_le_div_of_nonneg_right hbeta (Nat.cast_nonneg _))⟩
  by_cases hsize : ((HuxleyLinearForm.fareySector N l w).card:ℝ) ≤
      3840*B*δ*(w*(N:ℝ))*(N:ℝ)
  · exact Or.inl hsize
  have hbase : 1 < 96*B*((N:ℝ)*δ) := by
    have hh := (div_lt_iff₀ (show 0 < 96*B by positivity)).mp (lt_of_not_ge hsmall)
    nlinarith only [hh]
  have hlarge : 40*w*(N:ℝ) ≤ (HuxleyLinearForm.fareySector N l w).card := by
    have hh := mul_le_mul_of_nonneg_right hbase.le (show 0 ≤ 40*w*(N:ℝ) by positivity)
    nlinarith only [hh,lt_of_not_ge hsize]
  have hRM : w*(N:ℝ) ≤ (HuxleyLinearForm.fareySector N l w).card := by
    nlinarith only [hlarge,mul_nonneg hw hNR.le]
  rcases fareySector_large_beta_bound hl hlw hN hlarge hδ hnear with hbad | hb
  · exact (hsize (by nlinarith only [hbad,hBprod,hprod])).elim
  · rcases fareySector_alpha_of_beta_bound hl hlw hN hB hRM hR2 hdensity hδ hb hnear
      with hbad | ha
    · exact (hsize (by nlinarith only [hbad,hBprod,hprod])).elim
    · exact Or.inr ⟨ha,hb.trans (div_le_div_of_nonneg_right hbeta (Nat.cast_nonneg _))⟩

theorem fareySector_integer_labels_enlarged_rectangle_all_slopes
    {N : ℕ} {l μ B α β δ : ℝ}
    (hl : 0 < l) (hμ : 0 ≤ μ) (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hR : max ((μ-l)*(N:ℝ)^2/B) 2 ≤ (HuxleyLinearForm.fareySector N l μ).card)
    (hlarge : 3840*B*δ*(μ*(N:ℝ))*(N:ℝ) < (HuxleyLinearForm.fareySector N l μ).card)
    (hnear : ∀ p ∈ HuxleyLinearForm.fareySector N l μ,
      ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ) :
    ∀ p : ℤ × ℤ, 0 ≤ (p.1:ℝ) → (p.1:ℝ) ≤ 12*(μ*(N:ℝ)) →
      0 ≤ (p.2:ℝ) → (p.2:ℝ) ≤ 12*(N:ℝ) → ∀ b : ℤ,
      |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ →
      b=p.1*(round α)+p.2*(round β) := by
  have hbnd := fareySector_bounded_density_dichotomy_all_slopes hl hB hδ hR hnear
  obtain ⟨ha,hb⟩ := hbnd.resolve_left (not_le.mpr hlarge)
  have hμ0 : 0 ≤ μ := hμ
  intro p hp0 hpM hpn0 hpnN b hpnear
  let R : ℝ := (HuxleyLinearForm.fareySector N l μ).card
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) ((le_max_right _ _).trans hR)
  have hrect : R ≤ μ*(N:ℝ)^2 := fareySector_card_le_rectangle_all_slopes hμ
  have hδR := mul_le_mul_of_nonneg_left hrect hδ
  have hprod : 0 ≤ δ*μ*(N:ℝ)^2 := by positivity
  have hBprod := mul_le_mul_of_nonneg_right hB hprod
  have herrR : (δ+12*(27*B+20*B)*(μ*(N:ℝ))*(N:ℝ)*δ/R)*R < R := by
    have hcancel : (δ+12*(27*B+20*B)*(μ*(N:ℝ))*(N:ℝ)*δ/R)*R =
        δ*R+12*(27*B+20*B)*(μ*(N:ℝ))*(N:ℝ)*δ := by field_simp
    rw [hcancel]
    change 3840*B*δ*(μ*(N:ℝ))*(N:ℝ) < R at hlarge
    nlinarith only [hlarge,hδR,hBprod,hprod]
  have herr : δ+12*(27*B+20*B)*(μ*(N:ℝ))*(N:ℝ)*δ/R < 1 :=
    (mul_lt_mul_iff_left₀ hR0).mp (by simpa only [one_mul] using herrR)
  let z : ℤ := b-(p.1*(round α)+p.2*(round β))
  have hz : |(z:ℝ)| ≤ δ+12*(27*B+20*B)*(μ*(N:ℝ))*(N:ℝ)*δ/R := by
    have hid : (z:ℝ) = -((p.1:ℝ)*α+(p.2:ℝ)*β-b)+
        ((p.1:ℝ)*(α-(round α:ℤ))+(p.2:ℝ)*(β-(round β:ℤ))) := by
      dsimp [z]; push_cast; ring
    rw [hid]
    apply (abs_add_le _ _).trans
    rw [abs_neg]
    have ht := abs_add_le ((p.1:ℝ)*(α-(round α:ℤ))) ((p.2:ℝ)*(β-(round β:ℤ)))
    rw [abs_mul,abs_mul,abs_of_nonneg hp0,abs_of_nonneg hpn0] at ht
    have hpa := mul_le_mul hpM ha (abs_nonneg _) (by positivity : 0 ≤ 12*(μ*(N:ℝ)))
    have hpb := mul_le_mul hpnN hb (abs_nonneg _) (by positivity : (0:ℝ) ≤ 12*N)
    have hab : (12*(μ*(N:ℝ)))*(27*B*(N:ℝ)*δ/R)+(12*(N:ℝ))*(20*B*(μ*(N:ℝ))*δ/R) =
        12*(27*B+20*B)*(μ*(N:ℝ))*(N:ℝ)*δ/R := by ring
    change (p.1:ℝ)*|α-(round α:ℤ)| ≤ (12*(μ*(N:ℝ)))*(27*B*(N:ℝ)*δ/R) at hpa
    change (p.2:ℝ)*|β-(round β:ℤ)| ≤ (12*(N:ℝ))*(20*B*(μ*(N:ℝ))*δ/R) at hpb
    linarith only [hpnear,ht,hpa,hpb,hab]
  have hzsmall : |z| < 1 := by exact_mod_cast hz.trans_lt herr
  have hz0 : z=0 := by have hh := abs_lt.mp hzsmall; omega
  dsimp [z] at hz0
  exact sub_eq_zero.mp hz0

theorem sector_seed_label_of_taylor_remainders_all_slopes
    {K : ℕ} {l w B y₀ α β δ C : ℝ} {g : ℝ → ℝ} {H : ℤ × ℤ → ℤ} {p₀ : ℤ × ℤ} {H₀ : ℤ}
    (hl : 0 < l) (hw : 0 ≤ w) (hlw : l ≤ w) (hB : 1 ≤ B)
    (hy₀ : y₀ ∈ Set.Icc l w) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hcard : max ((w-l)*(K:ℝ)^2/B) 2 ≤ (HuxleyLinearForm.fareySector K l w).card)
    (htaylor : ∀ p ∈ HuxleyLinearForm.fareySector K l w,
      |g ((p.1:ℝ)/p.2)-g y₀-deriv g y₀*((p.1:ℝ)/p.2-y₀)| ≤
        C*|((p.1:ℝ)/p.2)-y₀|^2)
    (hnear : ∀ p ∈ HuxleyLinearForm.fareySector K l w,
      |(p.1:ℝ)*α+(p.2:ℝ)*β-(p.2:ℝ)*g ((p.1:ℝ)/p.2)-H p| ≤ δ) :
    let η := δ+(K:ℝ)*C*(w-l)^2
    3840*B*η*(w*(K:ℝ))*(K:ℝ) < (HuxleyLinearForm.fareySector K l w).card →
    0 ≤ (p₀.1:ℝ) → (p₀.1:ℝ) ≤ 12*(w*(K:ℝ)) →
    0 < (p₀.2:ℝ) → (p₀.2:ℝ) ≤ 12*(K:ℝ) →
    (p₀.1:ℝ)/p₀.2=y₀ →
    |(p₀.1:ℝ)*α+(p₀.2:ℝ)*β-(p₀.2:ℝ)*g y₀-H₀| ≤ δ →
    H₀=p₀.1*round (α-deriv g y₀)+p₀.2*round (β-g y₀+y₀*deriv g y₀) := by
  let η := δ+(K:ℝ)*C*(w-l)^2
  change _ → _
  intro hlarge
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hlin (p : ℤ × ℤ) (hp : p ∈ HuxleyLinearForm.fareySector K l w) :
      |(p.1:ℝ)*(α-deriv g y₀)+(p.2:ℝ)*(β-g y₀+y₀*deriv g y₀)-H p| ≤ η := by
    obtain ⟨ht,htK,_hc,hlo,hhi⟩ :=
      (HuxleyLinearForm.mem_fareySector_iff hl (hl.le.trans hlw)).mp hp
    have ht0 : (0:ℝ) < p.2 := by exact_mod_cast (show 0 < p.2 by omega)
    have htK' : (p.2:ℝ) ≤ K := by exact_mod_cast htK
    let x : ℝ := (p.1:ℝ)/p.2
    have hx : x ∈ Set.Icc l w :=
      ⟨(le_div_iff₀ ht0).mpr hlo,(div_le_iff₀ ht0).mpr hhi⟩
    have hdist : |x-y₀| ≤ w-l := abs_le.mpr
      ⟨by linarith [hx.1,hy₀.2],by linarith [hx.2,hy₀.1]⟩
    have htay := htaylor p hp
    have hbudget : (p.2:ℝ)*|g x-g y₀-deriv g y₀*(x-y₀)| ≤ (K:ℝ)*C*(w-l)^2 := by
      calc
        _ ≤ (p.2:ℝ)*(C*|x-y₀|^2) := mul_le_mul_of_nonneg_left htay ht0.le
        _ ≤ (K:ℝ)*(C*(w-l)^2) := by gcongr
        _ = _ := by ring
    have hid : (p.1:ℝ)*(α-deriv g y₀)+(p.2:ℝ)*(β-g y₀+y₀*deriv g y₀)-H p =
        (p.2:ℝ)*(g x-g y₀-deriv g y₀*(x-y₀))+
        ((p.1:ℝ)*α+(p.2:ℝ)*β-(p.2:ℝ)*g x-H p) := by
      dsimp [x]
      field_simp
      ring
    rw [hid]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_of_pos ht0]
    exact (add_le_add hbudget (hnear p hp)).trans_eq (by dsimp [η]; ring)
  intro hp0 hpu hpt hptK hy hpnear
  have hmul : (p₀.1:ℝ)=y₀*(p₀.2:ℝ) := (div_eq_iff hpt.ne').mp hy
  have hid : (p₀.1:ℝ)*(α-deriv g y₀)+(p₀.2:ℝ)*(β-g y₀+y₀*deriv g y₀)-H₀ =
      (p₀.1:ℝ)*α+(p₀.2:ℝ)*β-(p₀.2:ℝ)*g y₀-H₀ := by
    rw [hmul]
    ring
  have hpnear' : |(p₀.1:ℝ)*(α-deriv g y₀)+
      (p₀.2:ℝ)*(β-g y₀+y₀*deriv g y₀)-H₀| ≤ η := by
    rw [hid]
    exact hpnear.trans (le_add_of_nonneg_right (by positivity))
  exact fareySector_integer_labels_enlarged_rectangle_all_slopes hl hw hB hη hcard hlarge
    (fun q hq => ⟨H q,hlin q hq⟩) p₀ hp0 hpu hpt.le hptK H₀ hpnear'

theorem physicalModelPhase_quartic_original_seed_linearization_all_slopes
    {K : ℕ} {σ δ T M N R B dmin l w Bd Δ Q : ℝ}
    {p₀ : ℤ × ℤ} {k : Fin 17}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ xseed : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    {cnew : ℤ × ℤ → Fin 2 → ℤ} {cseed : Fin 2 → ℤ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hNscale : N^2 ≤ M*R) (hscale : T*N*R^2=M^3)
    (hB : 0 ≤ B) (hdmin : 0 < dmin) (hΔ : 0 ≤ Δ) (hQ : 0 ≤ Q)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ p ∈ HuxleyLinearForm.fareySector K l w, ∀ i,
      x₁ ((p.1:ℝ)/p.2) i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hxseed : ∀ i, xseed i∈Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hl : 0 < l) (hw : 0 ≤ w) (hlw : l ≤ w) (hBd : 1 ≤ Bd) (htseed : 0 < p₀.2)
    (hyseed : (p₀.1:ℝ)/p₀.2∈Set.Icc l w)
    (hden : ∀ y ∈ Set.Icc l w, ∀ i, dmin ≤ (r i:ℝ)*y+s i) :
    let S := HuxleyLinearForm.fareySector K l w
    let y₀ := (p₀.1:ℝ)/p₀.2
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let a := fun i => round (x₀ i)
    let b := fun y i => round (x₁ y i)
    let n := fun y i => b y i-a i
    let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
    let μseed := fun i => iteratedDeriv 3 (f i) (round (xseed i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (a i)/24
    let q := fun (p : ℤ × ℤ) i => (r i:ℝ)*p.1+s i*p.2
    let d₀ := fun i => iteratedDeriv 1 (f i) (a i)
    let δ₀ := fun i => iteratedDeriv 2 (f i) (a i)/2-(e i:ℝ)/r i
    let θ := fun i => (r i:ℝ)*d₀ i-round ((r i:ℝ)*d₀ i)
    let β₀ := fun i => d₀ i*s i+2*δ₀ i/(3*μ i*r i)
    let α := θ 0-θ 1
    let β := β₀ 0-β₀ 1
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let h := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let φ := fun y => g y-h y
    let z := fun (p : ℤ × ℤ) i => q p i*iteratedDeriv 1 (f i) (b ((p.1:ℝ)/p.2) i)
    let zseed := fun i => q p₀ i*iteratedDeriv 1 (f i) (round (xseed i))
    let jseed := fun i => round ((r i:ℝ)*d₀ i)*p₀.1+
      2*(round (xseed i)-a i)*(e i*p₀.1+v i*p₀.2)
    let Hseed := (cseed 0-jseed 0)-(cseed 1-jseed 1)
    let C := (2/modelPhaseThirdLower σ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*Q/N
    let η := D+(K:ℝ)*C*(w-l)^2
    let U := (4/modelPhaseThirdLower σ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let Z := quarticCurvatureBoundaryRoots (μ 0) (ν 0) (r 0) (s 0)
      (μ 1) (ν 1) (r 1) (s 1) U
    l ∈ finiteBoundaryCell Z l w k →
    w ∈ finiteBoundaryCell Z l w k →
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (xseed i)/2=((e i:ℝ)*p₀.1+v i*p₀.2)/q p₀ i) →
    (∀ i, |(round (xseed i):ℝ)-(a i:ℝ)|^2 ≤ M*R) →
    (∀ p ∈ S, ∀ i,
      iteratedDeriv 2 (f i) (x₁ ((p.1:ℝ)/p.2) i)/2=((e i:ℝ)*p.1+v i*p.2)/q p i) →
    (∀ p ∈ S, ∀ i, |(n ((p.1:ℝ)/p.2) i:ℝ)|^2 ≤ M*R) →
    |μseed 1*(q p₀ 1)^3/(μseed 0*(q p₀ 0)^3)-1| ≤ B*R^2/N^2 →
    (∀ p ∈ S, |(z p 0-cnew p 0)-(z p 1-cnew p 1)| ≤ Δ) →
    (∀ p ∈ S, |q p 0|+|q p 1| ≤ Q) →
    max ((w-l)*(K:ℝ)^2/Bd) 2 ≤ S.card →
    3840*Bd*η*(w*(K:ℝ))*(K:ℝ) < S.card →
    (p₀.1:ℝ) ≤ 12*(w*(K:ℝ)) →
    (p₀.2:ℝ) ≤ 12*(K:ℝ) →
    |(zseed 0-cseed 0)-(zseed 1-cseed 1)| ≤ Δ →
    |q p₀ 0|+|q p₀ 1| ≤ Q →
    Hseed=p₀.1*round (α-deriv φ y₀)+p₀.2*round (β-φ y₀+y₀*deriv φ y₀) ∧
    |(α-round (α-deriv φ y₀))*y₀+
      (β-round (β-φ y₀+y₀*deriv φ y₀))-φ y₀| ≤ D/(p₀.2:ℝ) := by
  let S := HuxleyLinearForm.fareySector K l w
  let y₀ := (p₀.1:ℝ)/p₀.2
  let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
  let a := fun i => round (x₀ i)
  let b := fun y i => round (x₁ y i)
  let n := fun y i => b y i-a i
  let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
  let ν := fun i => iteratedDeriv 4 (f i) (a i)/24
  let d := fun y i => (r i:ℝ)*y+s i
  let q := fun (p : ℤ × ℤ) i => (r i:ℝ)*p.1+s i*p.2
  let d₀ := fun i => iteratedDeriv 1 (f i) (a i)
  let δ₀ := fun i => iteratedDeriv 2 (f i) (a i)/2-(e i:ℝ)/r i
  let θ := fun i => (r i:ℝ)*d₀ i-round ((r i:ℝ)*d₀ i)
  let β₀ := fun i => d₀ i*s i+2*δ₀ i/(3*μ i*r i)
  let α := θ 0-θ 1
  let β := β₀ 0-β₀ 1
  let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
  let h := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
  let φ := fun y => g y-h y
  let j := fun (p : ℤ × ℤ) i => round ((r i:ℝ)*d₀ i)*p.1+
    2*n ((p.1:ℝ)/p.2) i*(e i*p.1+v i*p.2)
  let H := fun p => (cnew p 0-j p 0)-(cnew p 1-j p 1)
  let zseed := fun i => q p₀ i*iteratedDeriv 1 (f i) (round (xseed i))
  let jseed := fun i => round ((r i:ℝ)*d₀ i)*p₀.1+
    2*(round (xseed i)-a i)*(e i*p₀.1+v i*p₀.2)
  let Hseed := (cseed 0-jseed 0)-(cseed 1-jseed 1)
  let C := (2/modelPhaseThirdLower σ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
  let D := Δ+quarticNonlinearResidualConstant σ δ*Q/N
  let U := (4/modelPhaseThirdLower σ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
  let Z := quarticCurvatureBoundaryRoots (μ 0) (ν 0) (r 0) (s 0)
    (μ 1) (ν 1) (r 1) (s 1) U
  change _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _
  intro hleft hright hbase hseed hseedsquare hpoint hsquare hthird hfourth hqbound hcard hlarge
    hpu hptK hseedfourth hseedQ
  have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hr' (i) : (r i:ℝ) ≠ 0 := by exact_mod_cast hr i
  have hdet' (i) : (v i:ℝ)*r i-e i*s i=1 := by exact_mod_cast hdet i
  have hκ := modelPhaseThirdLower_pos hσ
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans
    (approximateModelPhase_iteratedDeriv_error (hF 0)
      (heathBrownPhysicalPoint_mem_interior hM0 (hA 0) (hW 0)
        (show x₀ 0 ∈ Set.Ioo 0 (W 0) from
          ⟨by linarith [(hx₀ 0).1],by linarith [(hx₀ 0).2]⟩)) 4 le_rfl)
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hC₄ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ0
  have hCN : 0 ≤ quarticNonlinearResidualConstant σ δ := by
    dsimp [quarticNonlinearResidualConstant]
    positivity
  have hCR : 0 ≤ quarticReciprocalConstant σ δ := by
    dsimp [quarticReciprocalConstant]
    positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hgeom (p : ℤ × ℤ) (hp : p ∈ S) :
      (0:ℝ) < p.2 ∧ (p.1:ℝ)/p.2 ∈ Set.Icc l w := by
    obtain ⟨ht,_htK,_hc,hlo,hhi⟩ :=
      (HuxleyLinearForm.mem_fareySector_iff hl (hl.le.trans hlw)).mp hp
    have ht0 : (0:ℝ) < p.2 := by exact_mod_cast (show 0 < p.2 by omega)
    exact ⟨ht0,⟨(le_div_iff₀ ht0).mpr hlo,(div_le_iff₀ ht0).mpr hhi⟩⟩
  have hy₀ : y₀ ∈ Set.Icc l w := hyseed
  have ht₀ : (0:ℝ) < p₀.2 := by exact_mod_cast htseed
  have hcell {z : ℝ} (hz : z ∈ Set.Icc l w) :
      z ∈ finiteBoundaryCell Z l w k :=
    (finiteBoundaryCell_ordConnected Z l w k).uIcc_subset hleft hright
      (by simpa only [Set.uIcc_of_le hlw] using hz)
  have htaylor (p : ℤ × ℤ) (hp : p ∈ S) :
      |φ ((p.1:ℝ)/p.2)-φ y₀-deriv φ y₀*((p.1:ℝ)/p.2-y₀)| ≤ C*|((p.1:ℝ)/p.2)-y₀|^2 := by
    have he := physicalModelPhase_quartic_taylor_on_boundary_cell
      (u := (p₀.1:ℝ)) (t := (p₀.2:ℝ)) (y := (p.1:ℝ)/p.2)
      hσ hδ hF hT hM0 hN hR hNscale hscale hB hdmin hA hW hx₀
      hxseed hr' ht₀ hdet' hden
      (hcell hy₀) (hcell (hgeom p hp).2) hbase hseed hseedsquare hthird
    exact he.trans_eq (by dsimp [C,U]; ring)
  have hnear (p : ℤ × ℤ) (hp : p ∈ S) :
      |(p.1:ℝ)*α+(p.2:ℝ)*β-(p.2:ℝ)*φ ((p.1:ℝ)/p.2)-H p| ≤ D := by
    let x : ℝ := (p.1:ℝ)/p.2
    have ht0 := (hgeom p hp).1
    have hx := (hgeom p hp).2
    have hpt : p.2 ≠ 0 := by exact_mod_cast ht0.ne'
    have hd (i) : 0 < d x i := hdmin.trans_le (hden x hx i)
    have hqd (i) : q p i=d x i*(p.2:ℝ) := by dsimp [q,d,x]; field_simp
    have hqpos (i) : 0 < q p i := by rw [hqd i]; exact mul_pos (hd i) ht0
    have hqint (i) : r i*p.1+s i*p.2 ≠ 0 := by
      have hh : (0:ℝ) < ((r i*p.1+s i*p.2:ℤ):ℝ) := by
        simpa only [Int.cast_add,Int.cast_mul] using hqpos i
      exact_mod_cast hh.ne'
    have he := physicalModelPhase_quartic_fourth_condition_nonlinear_with_labels
      (cnew := cnew p) hσ hδ hF hT hM hN hR hRM hscale hA hW hx₀
      (hx₁ p hp) hr hpt hqint hdet hbase (hpoint p hp) (hsquare p hp) (hfourth p hp)
    have hid : (p.1:ℝ)*α+(p.2:ℝ)*β-(p.2:ℝ)*φ x-H p =
        (θ 0-θ 1)*p.1+(β₀ 0-β₀ 1)*p.2-(p.2:ℝ)*g x+(p.2:ℝ)*h x-H p := by
      dsimp [α,β,φ]
      ring
    rw [hid]
    apply he.trans
    dsimp only [D]
    gcongr
    exact hqbound p hp
  have hqseedpos (i) : 0 < q p₀ i := by
    have hh : q p₀ i=d y₀ i*(p₀.2:ℝ) := by dsimp only [q,d,y₀]; field_simp
    rw [hh]
    exact mul_pos (hdmin.trans_le (hden y₀ hy₀ i)) ht₀
  have hqseedint (i) : r i*p₀.1+s i*p₀.2 ≠ 0 := by
    have hh : (0:ℝ) < ((r i*p₀.1+s i*p₀.2:ℤ):ℝ) := by
      simpa only [Int.cast_add,Int.cast_mul] using hqseedpos i
    exact_mod_cast hh.ne'
  have hseednear :
      |(p₀.1:ℝ)*α+(p₀.2:ℝ)*β-(p₀.2:ℝ)*φ y₀-Hseed| ≤ D := by
    have he := physicalModelPhase_quartic_fourth_condition_nonlinear_with_labels
      (cnew := cseed) hσ hδ hF hT hM hN hR hRM hscale hA hW hx₀
      hxseed hr htseed.ne' hqseedint hdet hbase hseed
      (fun i => by simpa only [Int.cast_sub] using hseedsquare i) hseedfourth
    have hid : (p₀.1:ℝ)*α+(p₀.2:ℝ)*β-(p₀.2:ℝ)*φ y₀-Hseed =
        (θ 0-θ 1)*p₀.1+(β₀ 0-β₀ 1)*p₀.2-
        (p₀.2:ℝ)*g y₀+(p₀.2:ℝ)*h y₀-Hseed := by
      dsimp only [α,β,φ]; ring
    rw [hid]
    apply he.trans
    dsimp only [D]
    gcongr
  have hp0 : 0 ≤ (p₀.1:ℝ) :=
    (mul_nonneg hl.le ht₀.le).trans ((le_div_iff₀ ht₀).mp hy₀.1)
  have hlabel := sector_seed_label_of_taylor_remainders_all_slopes
    hl hw hlw hBd hy₀ hD hC hcard htaylor hnear hlarge
    hp0 hpu ht₀ hptK rfl hseednear
  refine ⟨hlabel,?_⟩
  have hid : (p₀.2:ℝ)*((α-round (α-deriv φ y₀))*y₀+
      (β-round (β-φ y₀+y₀*deriv φ y₀))-φ y₀) =
      (p₀.1:ℝ)*α+(p₀.2:ℝ)*β-(p₀.2:ℝ)*φ y₀-Hseed := by
    rw [hlabel]
    push_cast
    dsimp only [y₀]
    field_simp
    ring
  have hmulabs := congrArg abs hid
  rw [abs_mul,abs_of_pos ht₀] at hmulabs
  apply (le_div_iff₀ ht₀).mpr
  rw [mul_comm]
  exact hmulabs.trans_le hseednear

theorem physicalModelPhase_actual_fourier_original_seed_residual_all_positive_slopes
    {σ δ T M N R dmin : ℝ} {k : Fin 17} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2) (Mat : Fin 4 → ℤ) (anchor : ℚ) (e r v s : ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ xref : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
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
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    let pseed : ℤ × ℤ := (v*(q 0:ℤ)-s*(rat 0).num,r*(rat 0).num-e*(q 0:ℤ))
    let yseed := (pseed.1:ℝ)/pseed.2
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let dr := fun i => deriv (f i) (ar i)
    let δr := fun i => iteratedDeriv 2 (f i) (ar i)/2-(ep i:ℝ)/rp i
    let θr := fun i => (rp i:ℝ)*dr i-round ((rp i:ℝ)*dr i)
    let βr := fun i => dr i*sp i+2*δr i/(3*μr i*rp i)
    let ac := θr 0-θr 1
    let bc := βr 0-βr 1
    let g := rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1)
    let hq := quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1)
    let φ := fun y => g y-hq y
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := D+(K:ℝ)*Ctay*(β-α)^2
    let U := (4/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
      (μr 1) (νr 1) (rp 1) (sp 1) U
    1 ≤ M → 1 ≤ R → R ≤ M → N^2 ≤ M*R → 0 < dmin →
    Δ < 1/2 →
    (∀ i, rp i ≠ 0) →
    (∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i) →
    (∀ i, (H+|x₀ i-xref i|+1)^2 ≤ M*R) →
    (∀ y∈Icc α β, ∀ i, dmin ≤ (rp i:ℝ)*y+sp i) →
    α ∈ finiteBoundaryCell Z α β k → β ∈ finiteBoundaryCell Z α β k →
    3840*128*η*(β*(K:ℝ))*(K:ℝ) < S.card →
    |(ac-round (ac-deriv φ yseed))*yseed+
      (bc-round (bc-φ yseed+yseed*deriv φ yseed))-g yseed+hq yseed| ≤ D/(pseed.2:ℝ) := by
  classical
  intro f hlevel q mu ell b cround tau dual w radius hcolor hnear c J B
    hsmall hNR hRN hcube hminscale hMatdet hMatt hMatmap hMatgamma
    C H ε hNtwo hL hU hchart hdl hdw hnum hdyad hanchor hcut hcount
    l w' α β K S C₂ C₃ κ Ct Cc Δ ep rp sp pseed yseed ar μr νr dr δr θr βr ac bc g hq φ
    Ctay D η U Z hMone hRone hRM hNscale hdmin hΔ hrp hxref href hbudget
    hd hleft hright hlarge
  let vp : Fin 2 → ℤ := ![v,Mat 0*v+Mat 1*s]
  have hF₃ i := approximateModelPhase_mono (hF i) (by norm_num : 3 ≤ 4) le_rfl
  obtain ⟨hcard,ξ,hξ⟩ := physicalModelPhase_actual_fourier_complete_sector_fourth_signed
    Q K₀ rat vinv parity Mat anchor e r v s hσ hδ hF₃ hT hM hN hR hQ hscale hmesh
    hA hW hx₀ hden hinv hlevel hcolor hnear hsmall hNR hRN hcube hminscale
    hMatdet hMatt hMatmap hMatgamma hNtwo hL hU hchart hdl hdw hnum hdyad hanchor hcut hcount
  let qp := fun (p : ℤ × ℤ) i => (rp i:ℝ)*p.1+sp i*p.2
  let ap := fun (p : ℤ × ℤ) i => (ep i:ℝ)*p.1+vp i*p.2
  let xp := fun p : ℤ × ℤ => ξ ((p.1:ℝ)/p.2)
  let zp := fun p i => qp p i*deriv (f i) (round (xp p i))
  have hqe (p : ℤ × ℤ) (i : Fin 2) :
      ((![r*p.1+s*p.2,Mat 2*(e*p.1+v*p.2)+Mat 3*(r*p.1+s*p.2)] i:ℤ):ℝ)=qp p i := by
    fin_cases i <;> dsimp only [qp,rp,sp] <;> push_cast <;> ring
  have hae (p : ℤ × ℤ) (i : Fin 2) :
      ((![e*p.1+v*p.2,Mat 0*(e*p.1+v*p.2)+Mat 1*(r*p.1+s*p.2)] i:ℤ):ℝ)=ap p i := by
    fin_cases i <;> dsimp only [ap,ep,vp] <;> push_cast <;> ring
  have hpoints (p) (hp : p∈S) (i) :
      xp p i∈Ioo (1/2:ℝ) (W i-1/2) ∧
      iteratedDeriv 2 (f i) (xp p i)/2=ap p i/qp p i ∧
      |xp p i-x₀ i| ≤ H ∧ 0 < qp p i ∧ qp p i ≤ Q := by
    have hh := (hξ p hp).1 i
    simpa only [hqe,hae] using hh
  have hlabels (p : ℤ × ℤ) : ∃ ci : Fin 2 → ℤ, p∈S →
      (∀ i, ci i∈minorArcCenterLabels (zp p i) Δ) ∧
      |(zp p 0-ci 0)-(zp p 1-ci 1)| ≤ Δ := by
    by_cases hp : p∈S
    · have hh := (hξ p hp).2.2 hΔ
      simp only [hqe] at hh
      obtain ⟨c₀,hc₀,c₁,hc₁,_hrnd,hfour,_⟩ := hh
      refine ⟨![c₀,c₁],fun _ => ⟨?_,hfour⟩⟩
      intro i
      fin_cases i
      · exact hc₀
      · exact hc₁
    · exact ⟨fun _ => 0,fun h => False.elim (hp h)⟩
  choose cnew hcnew using hlabels
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans
    (approximateModelPhase_iteratedDeriv_error (hF 0)
      (by norm_num : (3/2:ℝ)∈Ioo 1 2) 4 le_rfl)
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hC₂ : 0 ≤ C₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ : 0 ≤ C₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hΔpos : 0 ≤ Δ := by dsimp only [Δ,Ct,Cc]; positivity
  have hH : 0 < H := by dsimp only [H,C]; positivity
  have hε : 0 < ε := by dsimp only [ε,C]; positivity
  have hlw : l < w' := by dsimp only [l,w']; linarith only [hε]
  have hchartR : (v:ℝ)*r-e*s=1 := by exact_mod_cast hchart
  have hα : 0 < α := div_pos hnum hdw
  have hαβ : α ≤ β := by
    have hh := inverseFarey_difference hchartR hdl.ne' hdw.ne'
    change β-α=(w'-l)/(((r:ℝ)*l-e)*((r:ℝ)*w'-e)) at hh
    have hp' : 0 ≤ (w'-l)/(((r:ℝ)*l-e)*((r:ℝ)*w'-e)) := by positivity
    linarith only [hh,hp']
  have hqpos i : (0:ℝ) < q i := by exact_mod_cast (rat i).pos
  have hrat i : (rat i:ℝ)=((rat i).num:ℝ)/(q i:ℝ) := Rat.cast_def _
  have hdenR : (Mat 2:ℝ)*(rat 0).num+Mat 3*q 0=q 1 := by
    calc
      _ = ((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)*q 0 := by
        rw [hrat]; field_simp [(hqpos 0).ne']
      _ = q 1 := by rw [hMatt]; field_simp [(hqpos 0).ne']
  have hnumR : (Mat 0:ℝ)*(rat 0).num+Mat 1*q 0=(rat 1).num := by
    have hm := hMatmap
    rw [hMatt,hrat 0,hrat 1] at hm
    have hh := (div_eq_iff (div_ne_zero (hqpos 1).ne' (hqpos 0).ne')).mp hm
    field_simp [(hqpos 0).ne',(hqpos 1).ne'] at hh
    nlinarith only [hh]
  have hseedq (i) : qp pseed i=(q i:ℝ) := by
    fin_cases i
    · dsimp only [qp,pseed,rp,sp]; push_cast
      linear_combination (q 0:ℝ)*hchartR
    · dsimp only [qp,pseed,rp,sp]; push_cast
      linear_combination ((Mat 2:ℝ)*(rat 0).num+Mat 3*q 0)*hchartR+hdenR
  have hseeda (i) : ap pseed i=((rat i).num:ℝ) := by
    fin_cases i
    · dsimp only [ap,pseed,ep,vp]; push_cast
      linear_combination ((rat 0).num:ℝ)*hchartR
    · dsimp only [ap,pseed,ep,vp]; push_cast
      linear_combination ((Mat 0:ℝ)*(rat 0).num+Mat 1*q 0)*hchartR+hnumR
  have hseedroot (i) : iteratedDeriv 2 (f i) (x₀ i)/2=ap pseed i/qp pseed i := by
    rw [hseedq,hseeda,hlevel,hrat]
  have hseedtd : (pseed.2:ℝ)=((r:ℝ)*(rat 0:ℝ)-e)*q 0 := by
    dsimp only [pseed]; push_cast; rw [hrat]; field_simp [(hqpos 0).ne']
  have hseedd : 0 < (r:ℝ)*(rat 0:ℝ)-e := by
    nlinarith only [hdl,hdw]
  have htseed : 0 < pseed.2 := by
    have hh : (0:ℝ) < pseed.2 := by rw [hseedtd]; exact mul_pos hseedd (hqpos 0)
    exact_mod_cast hh
  have hys : yseed=((v:ℝ)-s*(rat 0:ℝ))/((r:ℝ)*(rat 0:ℝ)-e) := by
    dsimp only [yseed,pseed]
    push_cast
    rw [hrat 0]
    field_simp [(hqpos 0).ne']
  have hyseed : yseed∈Icc α β := by
    rw [hys]
    apply inverseFarey_mem_interval_signed hchartR hdl hdw
    exact ⟨by linarith only [hε],by linarith only [hε]⟩
  have hdetp (i) : vp i*rp i-ep i*sp i=1 := by
    fin_cases i
    · exact hchart
    · change (Mat 0*v+Mat 1*s)*(Mat 2*e+Mat 3*r)-
        (Mat 0*e+Mat 1*r)*(Mat 2*v+Mat 3*s)=1
      linear_combination (v*r-e*s)*hMatdet+hchart
  have hsq (p) (hp : p∈S) (i) :
      |((round (xp p i)-ar i:ℤ):ℝ)|^2 ≤ M*R := by
    have hh := rounded_displacement_bound (xp p i) (xref i)
    have htri := abs_sub_le (xp p i) (x₀ i) (xref i)
    have hdist := (hpoints p hp i).2.2.1
    have hb : |(round (xp p i):ℝ)-(ar i:ℝ)| ≤ H+|x₀ i-xref i|+1 := by
      dsimp only [ar]
      linarith only [hh,htri,hdist]
    rw [Int.cast_sub]
    exact (pow_le_pow_left₀ (abs_nonneg _) hb 2).trans (hbudget i)
  have hseedSq i : |(round (x₀ i):ℝ)-(ar i:ℝ)|^2 ≤ M*R := by
    have hh := rounded_displacement_bound (x₀ i) (xref i)
    have hb : |(round (x₀ i):ℝ)-(ar i:ℝ)| ≤ H+|x₀ i-xref i|+1 := by
      dsimp only [ar]
      linarith only [hh,hH]
    exact (pow_le_pow_left₀ (abs_nonneg _) hb 2).trans (hbudget i)
  obtain ⟨_v,_hv,hthird,_hsecond,_hfirst,hfourth⟩ := physicalModelPhase_actual_fourier_conditions
    Q K₀ rat vinv parity hσ hδ hF₃ hT hM hN hR hQ hscale hmesh
    hA hW hx₀ hden hinv hlevel hcolor hnear
  have hthird' : |mu 1*(qp pseed 1)^3/(mu 0*(qp pseed 0)^3)-1| ≤ B*R^2/N^2 := by
    simpa only [hseedq] using hthird
  have hqsum p (hp : p∈S) : |qp p 0|+|qp p 1| ≤ 2*(Q:ℝ) := by
    rw [abs_of_pos (hpoints p hp 0).2.2.2.1,abs_of_pos (hpoints p hp 1).2.2.2.1]
    linarith only [(hpoints p hp 0).2.2.2.2,(hpoints p hp 1).2.2.2.2]
  have ha : (anchor:ℝ)∈Icc l w' := by
    have hh := abs_le.mp hanchor
    exact ⟨by dsimp only [l]; linarith only [hh.1],
      by dsimp only [w']; linarith only [hh.2]⟩
  have hseedI : (rat 0:ℝ)∈Icc l w' :=
    ⟨by dsimp only [l]; linarith only [hε],
      by dsimp only [w']; linarith only [hε]⟩
  have hrect := inverseFarey_original_seed_enlarged_rectangle_signed
    hchart hdl hdw hnum ha hseedI hdyad hcut
    (show ((rat 0).den:ℝ) ≤ (Q:ℝ) by exact_mod_cast (hden 0).1)
  have hpu : (pseed.1:ℝ) ≤ 12*(β*(K:ℝ)) := hrect.2.2.2.1
  have hptK : (pseed.2:ℝ) ≤ 12*(K:ℝ) := hrect.2.2.2.2
  have hseedfourth :
      |(qp pseed 0*iteratedDeriv 1 (f 0) (round (x₀ 0))-cround 0)-
       (qp pseed 1*iteratedDeriv 1 (f 1) (round (x₀ 1))-cround 1)| ≤ Δ := by
    simp only [hseedq,iteratedDeriv_one]
    apply hfourth.trans
    have hqQ : (q 0:ℝ) ≤ Q := by exact_mod_cast (hden 0).1
    have hCt : 0 ≤ Ct := by dsimp only [Ct]; positivity
    have hCc : 0 ≤ Cc := by dsimp only [Cc]; positivity
    have hcoeff : B ≤ 37*B/2+16*B*Cc+2*Ct+2*Cc := by
      nlinarith only [hB,hCt,hCc,mul_nonneg hB hCc]
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hqQ hB) hN.le).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoeff (by positivity : (0:ℝ) ≤ Q)) hN.le)
  have hseedQ : |qp pseed 0|+|qp pseed 1| ≤ 2*(Q:ℝ) := by
    rw [hseedq,hseedq,abs_of_pos (hqpos 0),abs_of_pos (hqpos 1)]
    have hq0 : (q 0:ℝ) ≤ Q := by exact_mod_cast (hden 0).1
    have hq1 : (q 1:ℝ) ≤ Q := by exact_mod_cast (hden 1).1
    linarith only [hq0,hq1]
  have hcommon := physicalModelPhase_quartic_original_seed_linearization_all_slopes
    (p₀:=pseed) (x₀:=xref) (xseed:=x₀) (x₁:=ξ) (e:=ep) (r:=rp) (v:=vp) (s:=sp)
    (cnew:=cnew) (cseed:=cround) hσ hδ hF hT hMone hN hRone hRM hNscale hscale
    hB hdmin hΔpos (by positivity : (0:ℝ) ≤ 2*(Q:ℝ))
    hA hW hxref (fun p hp i => (hpoints p hp i).1) hx₀ hrp hdetp
    hα (hα.le.trans hαβ) hαβ (by norm_num : (1:ℝ) ≤ 128) htseed hyseed hd
    hleft hright href hseedroot hseedSq
    (fun p hp i => (hpoints p hp i).2.1) hsq hthird'
    (fun p hp => by simpa only [iteratedDeriv_one] using (hcnew p hp).2) hqsum hcard hlarge
    hpu hptK hseedfourth hseedQ
  have hres := hcommon.2
  simp only [iteratedDeriv_one] at hres
  change |(ac-round (ac-deriv φ yseed))*yseed+
    (bc-round (bc-φ yseed+yseed*deriv φ yseed))-φ yseed| ≤ D/(pseed.2:ℝ) at hres
  convert hres using 1
  congr 1
  dsimp only [φ]
  ring

                                                                    
                                                                    
theorem quartic_weighted_coefficient_budget_of_bounded_source_chart
    {C J μ N R r s d l w Bcut Kcoord : ℝ}
    (hC : 0 ≤ C) (hJ : 0 < J) (hμ : 0 < μ)
    (hN : 0 < N) (hR : 0 < R) (hr : r ≠ 0) (hd : 0 < d)
    (hlw : l ≤ w)
    (hdlo : d ≤ min (r*l+s) (r*w+s)) (hdhi : max (r*l+s) (r*w+s) ≤ 2*d)
    (hcoord : |r| * max |l| |w| ≤ Kcoord*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hBcut : 0 < Bcut) (hBsize : (2*Kcoord+1)*C*J ≤ Bcut)
    (hG : |minorArcCoordinate μ r s l| ≤ |r| *N^2/(Bcut*R^2)) :
    let U := C*R^4/(N*d^3)
    U*(w-l)*(max |l| |w|+(w-l)/2) ≤ 1/2 := by
  intro U
  let dl := r*l+s
  let r₀ := |r|
  have hr₀ : 0 < r₀ := abs_pos.mpr hr
  have hdl : 0 < dl := hd.trans_le (hdlo.trans (min_le_left _ _))
  have hdlhi : dl ≤ 2*d := (le_max_left _ _).trans hdhi
  have hdwlo : d ≤ r*w+s := hdlo.trans (min_le_right _ _)
  have hdwhi : r*w+s ≤ 2*d := (le_max_right _ _).trans hdhi
  have hG' : 1/(3*μ*r₀*dl) ≤ r₀*N^2/(Bcut*R^2) := by
    change |1/(3*μ*r*dl)| ≤ r₀*N^2/(Bcut*R^2) at hG
    simpa only [abs_div,abs_one,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 3),
      abs_of_pos hμ,abs_of_pos hdl] using hG
  have hμmul : 6*μ*N*R^2 ≤ J := by
    have hh := (le_div_iff₀ (show 0 < 6*N*R^2 by positivity)).mp hμupper
    nlinarith only [hh]
  have hGclear : Bcut*R^2 ≤ (r₀*N^2)*(3*μ*r₀*dl) := by
    have hh := (div_le_div_iff₀
      (show 0 < 3*μ*r₀*dl by positivity)
      (show 0 < Bcut*R^2 by positivity)).mp hG'
    simpa only [one_mul] using hh
  have hGfour : Bcut*R^4 ≤ (3*μ*N*R^2)*(r₀^2*dl*N) := by
    have hh := mul_le_mul_of_nonneg_right hGclear (sq_nonneg R)
    nlinarith only [hh]
  have hμhalf : 3*μ*N*R^2 ≤ J/2 := by nlinarith only [hμmul]
  have hupper : Bcut*R^4 ≤ J*r₀^2*d*N := by
    have hh := mul_le_mul_of_nonneg_right hμhalf
      (show 0 ≤ r₀^2*dl*N by positivity)
    have hh' := mul_le_mul_of_nonneg_left hdlhi
      (show 0 ≤ J*r₀^2*N/2 by positivity)
    nlinarith only [hGfour,hh,hh']
  have hsmall : (2*Kcoord+1)*C*R^4 ≤ N*r₀^2*d := by
    have hh := mul_le_mul_of_nonneg_right hBsize (pow_nonneg hR.le 4)
    have he : J*((2*Kcoord+1)*C*R^4) ≤ J*(N*r₀^2*d) := by nlinarith only [hh,hupper]
    exact (mul_le_mul_iff_right₀ hJ).mp he
  have hdiff : w-l ≤ d/r₀ := by
    apply (le_div_iff₀ hr₀).mpr
    have hdllo : d ≤ r*l+s := hdlo.trans (min_le_left _ _)
    rcases le_total 0 r with hsign | hsign
    · dsimp only [r₀]
      rw [abs_of_nonneg hsign]
      nlinarith only [hdllo,hdwhi]
    · dsimp only [r₀]
      rw [abs_of_nonpos hsign]
      change r*l+s ≤ 2*d at hdlhi
      nlinarith only [hdwlo,hdlhi]
  have hwbound : max |l| |w| ≤ Kcoord*d/r₀ := by
    apply (le_div_iff₀ hr₀).mpr
    nlinarith only [hcoord]
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hheight : U*(w-l)*(max |l| |w|+(w-l)/2) ≤ 1/2 := by
    calc
      _ ≤ U*(d/r₀)*(Kcoord*d/r₀+(d/r₀)/2) := by gcongr
      _ = (2*Kcoord+1)*C*R^4/(2*N*r₀^2*d) := by dsimp only [U]; field_simp
      _ ≤ _ := by
        apply (div_le_iff₀ (show 0 < 2*N*r₀^2*d by positivity)).mpr
        nlinarith only [hsmall]
  exact hheight

theorem convex_weighted_derivative_difference
    {f : ℝ → ℝ} {l w x y : ℝ}
    (hconv : ConvexOn ℝ (Icc l w) f)
    (hder : ∀ z∈Icc l w, DifferentiableAt ℝ f z)
    (hx : x∈Icc l w) (hy : y∈Icc l w) :
    l*|deriv f y-deriv f x| ≤
      |(y*deriv f y-f y)-(x*deriv f x-f x)| := by
  have hord (x y : ℝ) (hx : x∈Icc l w) (hy : y∈Icc l w) (hxy : x ≤ y) :
      l*|deriv f y-deriv f x| ≤
        |(y*deriv f y-f y)-(x*deriv f x-f x)| := by
    rcases eq_or_lt_of_le hxy with rfl | hxy
    · simp
    have hmono := hconv.monotoneOn_deriv hder hx hy hxy.le
    have hs := hconv.slope_le_deriv hx hy hxy (hder y hy)
    rw [slope_def_field] at hs
    have hsupport := (div_le_iff₀ (sub_pos.mpr hxy)).mp hs
    have hlo := mul_le_mul_of_nonneg_right hx.1 (sub_nonneg.mpr hmono)
    rw [abs_of_nonneg (sub_nonneg.mpr hmono)]
    apply le_trans _ (le_abs_self _)
    nlinarith only [hsupport,hlo]
  rcases le_total x y with hxy | hyx
  · exact hord x y hx hy hxy
  · simpa only [abs_sub_comm] using hord y x hy hx hyx

                                                                     
                                                                         
theorem curvature_branch_weighted_derivative_difference
    {f : ℝ → ℝ} {l w x y : ℝ}
    (hshape : ConvexOn ℝ (Icc l w) f ∨ ConcaveOn ℝ (Icc l w) f)
    (hder : ∀ z∈Icc l w, DifferentiableAt ℝ f z)
    (hx : x∈Icc l w) (hy : y∈Icc l w) :
    l*|deriv f y-deriv f x| ≤
      |(y*deriv f y-f y)-(x*deriv f x-f x)| := by
  rcases hshape with hconv | hconc
  · exact convex_weighted_derivative_difference hconv hder hx hy
  · have hh := convex_weighted_derivative_difference hconc.neg
      (fun z hz => (hder z hz).neg) hx hy
    have he (z : ℝ) : deriv (-f) z = -deriv f z := by
      exact deriv.neg
    simp only [he,Pi.neg_apply] at hh
    have ha : -deriv f y - -deriv f x = -(deriv f y-deriv f x) := by ring
    have hb : (y*(-deriv f y)- -f y)-(x*(-deriv f x)- -f x) =
        -((y*deriv f y-f y)-(x*deriv f x-f x)) := by ring
    simpa only [ha,hb,abs_neg] using hh


                                                              
                                                                   
                                                                     
                        
theorem quartic_phase_second_derivative_data
    {μ ν r s μ₁ ν₁ r₁ s₁ x : ℝ}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hx : r*x+s ≠ 0) (hx₁ : r₁*x+s₁ ≠ 0) :
    let φ := fun z => rationalPhase μ r s μ₁ r₁ s₁ z-
      quarticPhase μ ν r s μ₁ ν₁ r₁ s₁ z
    DifferentiableAt ℝ φ x ∧ DifferentiableAt ℝ (deriv φ) x ∧
      (deriv^[2] φ) x =
        (quarticCurvatureNumerator μ ν r s μ₁ ν₁ r₁ s₁).eval x/
          ((r*x+s)^4*(r₁*x+s₁)^4) := by
  intro φ
  have hg : ContDiffAt ℝ 2 (rationalPhase μ r s μ₁ r₁ s₁) x := by
    change ContDiffAt ℝ 2
      (fun z => 1/(3*μ*r^2*(r*z+s))-1/(3*μ₁*r₁^2*(r₁*z+s₁))) x
    exact (contDiffAt_const.div (by fun_prop) (by positivity)).sub
      (contDiffAt_const.div (by fun_prop) (by positivity))
  have hh : ContDiffAt ℝ 2 (quarticPhase μ ν r s μ₁ ν₁ r₁ s₁) x := by
    change ContDiffAt ℝ 2
      (fun z => 4*ν/(27*μ^3*r^3*(r*z+s)^2)-4*ν₁/(27*μ₁^3*r₁^3*(r₁*z+s₁)^2)) x
    exact (contDiffAt_const.div (by fun_prop) (by positivity)).sub
      (contDiffAt_const.div (by fun_prop) (by positivity))
  have hφ : ContDiffAt ℝ 2 φ x := hg.sub hh
  have hder := hasDerivAt_iteratedDeriv_finite (by norm_num : 1 < 2) hφ
  simp only [iteratedDeriv_one] at hder
  refine ⟨hφ.differentiableAt (by norm_num),hder.differentiableAt,?_⟩
  rw [←iteratedDeriv_eq_iterate]
  change iteratedDeriv 2 (fun z => rationalPhase μ r s μ₁ r₁ s₁ z-
    quarticPhase μ ν r s μ₁ ν₁ r₁ s₁ z) x=_
  rw [iteratedDeriv_fun_sub hg hh]
  exact quarticCurvatureNumerator_eval hμ hμ₁ hr hr₁ hx hx₁

                                                                  
                                                                   
                                                                         
theorem quartic_phase_shape_on_curvature_root_cell
    {μ ν r s μ₁ ν₁ r₁ s₁ l w a b : ℝ} {k : ℕ}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hden : ∀ z∈Icc l w, r*z+s ≠ 0)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hcell : Icc a b ⊆ finiteBoundaryCell
      (quarticCurvatureNumerator μ ν r s μ₁ ν₁ r₁ s₁).roots.toFinset l w k) :
    let φ := fun z => rationalPhase μ r s μ₁ r₁ s₁ z-
      quarticPhase μ ν r s μ₁ ν₁ r₁ s₁ z
    ConvexOn ℝ (Icc a b) φ ∨ ConcaveOn ℝ (Icc a b) φ := by
  classical
  intro φ
  let P := quarticCurvatureNumerator μ ν r s μ₁ ν₁ r₁ s₁
  have hsign : (∀ z∈Icc a b, 0 ≤ P.eval z) ∨ (∀ z∈Icc a b, P.eval z ≤ 0) := by
    by_cases hp : P=0
    · left
      simp [hp]
    have hno (z : ℝ) (hz : z∈Icc a b) : P.eval z ≠ 0 := by
      intro he
      exact (hcell hz).2.1 (by
        rw [Multiset.mem_toFinset,Polynomial.mem_roots hp]
        exact he)
    by_cases hpos : ∀ z∈Icc a b, 0 ≤ P.eval z
    · exact Or.inl hpos
    right
    push Not at hpos
    obtain ⟨x,hx,hneg⟩ := hpos
    intro y hy
    by_contra hny
    have hpy : 0 < P.eval y := lt_of_not_ge hny
    have hivt := intermediate_value_uIcc
      ((Polynomial.continuous P).continuousOn : ContinuousOn P.eval (Set.uIcc x y))
    obtain ⟨z,hz,he⟩ := hivt (Set.mem_uIcc.mpr (Or.inl ⟨hneg.le,hpy.le⟩))
    exact hno z (Set.uIcc_subset_Icc hx hy hz) he
  have hdata (z : ℝ) (hz : z∈Icc a b) := quartic_phase_second_derivative_data
    (ν:=ν) (ν₁:=ν₁) hμ hμ₁ hr hr₁
    (hden z (hcell hz).1) (hden₁ z (hcell hz).1)
  have hd : DifferentiableOn ℝ φ (Icc a b) := fun z hz => (hdata z hz).1.differentiableWithinAt
  have hdd : DifferentiableOn ℝ (deriv φ) (Icc a b) :=
    fun z hz => (hdata z hz).2.1.differentiableWithinAt
  have hdenpos (z : ℝ) (hz : z∈Icc a b) : 0 < (r*z+s)^4*(r₁*z+s₁)^4 := by
    have h0 := hden z (hcell hz).1
    have h1 := hden₁ z (hcell hz).1
    positivity
  rcases hsign with hpos | hneg
  · left
    apply convexOn_of_deriv2_nonneg' (convex_Icc a b) hd hdd
    intro z hz
    rw [(hdata z hz).2.2]
    exact div_nonneg (hpos z hz) (hdenpos z hz).le
  · right
    apply concaveOn_of_deriv2_nonpos' (convex_Icc a b) hd hdd
    intro z hz
    rw [(hdata z hz).2.2]
    exact div_nonpos_of_nonpos_of_nonneg (hneg z hz) (hdenpos z hz).le


                                                                   
                                                                         
theorem quartic_phase_weighted_coefficient_variation
    {μ ν r s μ₁ ν₁ r₁ s₁ U l w x₀ x bc : ℝ} {k : Fin 17}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hden : ∀ z∈Icc l w, r*z+s ≠ 0)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hheight : U*(w-l)*(max |l| |w|+(w-l)/2) ≤ 1/2) :
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun z => g z-h z
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    x₀∈finiteBoundaryCell Z l w k →
    x∈finiteBoundaryCell Z l w k →
    |iteratedDeriv 2 g x₀-iteratedDeriv 2 h x₀| ≤ U →
    |(bc-φ x+x*deriv φ x)-(bc-φ x₀+x₀*deriv φ x₀)| ≤ 1/2 := by
  intro g h φ Z hx₀ hx hcurv
  have hU : 0 ≤ U := (abs_nonneg _).trans hcurv
  have hlw : l ≤ w := hx₀.1.1.trans hx₀.1.2
  have hd := quartic_phase_derivative_variation_on_boundary_cell
    hμ hμ₁ hr hr₁ hden hden₁ hx₀ hx hcurv
  have ht := quartic_phase_taylor_on_boundary_cell
    hμ hμ₁ hr hr₁ hden hden₁ hx₀ hx hcurv
  have hdist : |x-x₀| ≤ w-l := abs_le.mpr
    ⟨by linarith [hx.1.1,hx₀.1.2],by linarith [hx.1.2,hx₀.1.1]⟩
  have hxabs : |x| ≤ max |l| |w| := by
    refine abs_le.mpr ⟨?_,?_⟩
    · have hh := neg_abs_le l
      have hm := le_max_left |l| |w|
      linarith only [hh,hm,hx.1.1]
    · exact hx.1.2.trans ((le_abs_self w).trans (le_max_right _ _))
  have he : (bc-φ x+x*deriv φ x)-(bc-φ x₀+x₀*deriv φ x₀) =
      x*(deriv φ x-deriv φ x₀)-(φ x-φ x₀-deriv φ x₀*(x-x₀)) := by ring
  rw [he]
  calc
    _ ≤ |x*(deriv φ x-deriv φ x₀)|+|φ x-φ x₀-deriv φ x₀*(x-x₀)| := abs_sub _ _
    _ ≤ |x| *(U*|x-x₀|)+U*|x-x₀|^2/2 := by rw [abs_mul]; gcongr
    _ ≤ max |l| |w| *(U*(w-l))+U*(w-l)^2/2 := by gcongr
    _ = U*(w-l)*(max |l| |w|+(w-l)/2) := by ring
    _ ≤ _ := hheight


                                                                 
                                                                        
                                                                        
                                                                   
theorem quartic_integer_seed_residual_source_normalization
    (p : ℤ × ℤ) {μ r s κ N R Q Cres D : ℝ}
    (hμ : 0 < μ) (hr : r ≠ 0) (hκ : 0 < κ) (hN : 0 < N)
    (hCres : 0 ≤ Cres) (hu : 0 < p.2)
    (hden : 0 < r*((p.1:ℝ)/p.2)+s)
    (hQband : Q ≤ 2*(r*(p.1:ℝ)+s*p.2))
    (hD : D ≤ Cres*Q/N)
    (hlower : κ/(2*N) ≤ 3*μ*R^2) :
    D/(p.2:ℝ) ≤ (4*Cres/κ)*R^2/
      |r*minorArcCoordinate μ r s ((p.1:ℝ)/p.2)| := by
  let d := r*((p.1:ℝ)/p.2)+s
  have huR : (0:ℝ) < p.2 := by exact_mod_cast hu
  have hdu : d*(p.2:ℝ)=r*(p.1:ℝ)+s*p.2 := by
    dsimp only [d]
    field_simp
  have hres : D/(p.2:ℝ) ≤ 2*Cres*d/N := by
    calc
      _ ≤ (Cres*Q/N)/(p.2:ℝ) := div_le_div_of_nonneg_right hD huR.le
      _ ≤ (Cres*(2*(r*(p.1:ℝ)+s*p.2))/N)/(p.2:ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hQband hCres) hN.le) huR.le
      _ = _ := by rw [←hdu]; field_simp
  apply hres.trans
  rw [scaled_minorArcCoordinate_abs hμ.ne' hr hden.ne',
    abs_of_pos hμ,abs_of_pos hden,one_div,div_inv_eq_mul]
  change 2*Cres*d/N ≤ (4*Cres/κ)*R^2*(3*μ*d)
  have hh := mul_le_mul_of_nonneg_left hlower
    (show 0 ≤ (4*Cres/κ)*d by exact mul_nonneg (by positivity) hden.le)
  convert hh using 1 <;> field_simp
  ring


                                                                   
                                                                  
                                                                        
theorem physicalModelPhase_actual_fourier_original_seed_bounds_all_positive_slopes
    {σ δ T M N R dmin : ℝ} {k : Fin 17} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2) (Mat : Fin 4 → ℤ) (anchor : ℚ) (e r v s : ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ xref : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
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
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    let pseed : ℤ × ℤ := (v*(q 0:ℤ)-s*(rat 0).num,r*(rat 0).num-e*(q 0:ℤ))
    let yseed := (pseed.1:ℝ)/pseed.2
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let dr := fun i => deriv (f i) (ar i)
    let δr := fun i => iteratedDeriv 2 (f i) (ar i)/2-(ep i:ℝ)/rp i
    let θr := fun i => (rp i:ℝ)*dr i-round ((rp i:ℝ)*dr i)
    let βr := fun i => dr i*sp i+2*δr i/(3*μr i*rp i)
    let ac := θr 0-θr 1
    let bc := βr 0-βr 1
    let g := rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1)
    let hq := quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1)
    let φ := fun y => g y-hq y
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := D+(K:ℝ)*Ctay*(β-α)^2
    let U := (4/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
      (μr 1) (νr 1) (rp 1) (sp 1) U
    1 ≤ M → 1 ≤ R → R ≤ M → N^2 ≤ M*R → 0 < dmin →
    Δ < 1/2 →
    (∀ i, rp i ≠ 0) →
    (∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i) →
    (∀ i, (H+|x₀ i-xref i|+1)^2 ≤ M*R) →
    (∀ y∈Icc α β, ∀ i, dmin ≤ (rp i:ℝ)*y+sp i) →
    α ∈ finiteBoundaryCell Z α β k → β ∈ finiteBoundaryCell Z α β k →
    3840*128*η*(β*(K:ℝ))*(K:ℝ) < S.card →
    |iteratedDeriv 2 g yseed-iteratedDeriv 2 hq yseed| ≤ U ∧
    |(ac-round (ac-deriv φ yseed))*yseed+
      (bc-round (bc-φ yseed+yseed*deriv φ yseed))-g yseed+hq yseed| ≤
      D/(pseed.2:ℝ) := by
  classical
  intro f hlevel q mu ell b cround tau dual w radius hcolor hnear c J B
    hsmall hNR hRN hcube hminscale hMatdet hMatt hMatmap hMatgamma
    C H ε hNtwo hL hU hchart hdl hdw hnum hdyad hanchor hcut hcount
    l w' α β K S C₂ C₃ κ Ct Cc Δ ep rp sp pseed yseed ar μr νr dr δr θr βr ac bc g hq φ
    Ctay D η U Z hMone hRone hRM hNscale hdmin hΔ hrp hxref href hbudget
    hd hleft hright hlarge
  have hresult := physicalModelPhase_actual_fourier_original_seed_residual_all_positive_slopes
    Q K₀ rat vinv parity Mat anchor e r v s
    hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv
    hlevel hcolor hnear hsmall hNR hRN hcube hminscale hMatdet hMatt hMatmap hMatgamma
    hNtwo hL hU hchart hdl hdw hnum hdyad hanchor hcut hcount
    hMone hRone hRM hNscale hdmin hΔ hrp hxref href hbudget hd hleft hright hlarge
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hε : 0 < ε := by dsimp only [ε,C]; positivity
  have ha : (anchor:ℝ)∈Icc l w' := by
    have hh := abs_le.mp hanchor
    exact ⟨by dsimp only [l]; linarith only [hh.1],
      by dsimp only [w']; linarith only [hh.2]⟩
  have hseedI : (rat 0:ℝ)∈Icc l w' :=
    ⟨by dsimp only [l]; linarith only [hε],
      by dsimp only [w']; linarith only [hε]⟩
  have hrect := inverseFarey_original_seed_enlarged_rectangle_signed
    hchart hdl hdw hnum ha hseedI hdyad hcut
    (show ((rat 0).den:ℝ) ≤ (Q:ℝ) by exact_mod_cast (hden 0).1)
  have ht : (0:ℝ) < pseed.2 := hrect.1
  have hyseed : yseed∈Icc α β := hrect.2.1
  have hchartR : (v:ℝ)*r-e*s=1 := by exact_mod_cast hchart
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  refine ⟨?_,hresult⟩
  let vp : Fin 2 → ℤ := ![v,Mat 0*v+Mat 1*s]
  let qp := fun (p : ℤ × ℤ) i => (rp i:ℝ)*p.1+sp i*p.2
  let ap := fun (p : ℤ × ℤ) i => (ep i:ℝ)*p.1+vp i*p.2
  have hH : 0 < H := by dsimp only [H,C]; positivity
  have hF₃ i := approximateModelPhase_mono (hF i) (by norm_num : 3 ≤ 4) le_rfl
  have hqpos i : (0:ℝ) < q i := by exact_mod_cast (rat i).pos
  have hrat i : (rat i:ℝ)=((rat i).num:ℝ)/(q i:ℝ) := Rat.cast_def _
  have hdenR : (Mat 2:ℝ)*(rat 0).num+Mat 3*q 0=q 1 := by
    calc
      _ = ((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)*q 0 := by
        rw [hrat]; field_simp [(hqpos 0).ne']
      _ = q 1 := by rw [hMatt]; field_simp [(hqpos 0).ne']
  have hnumR : (Mat 0:ℝ)*(rat 0).num+Mat 1*q 0=(rat 1).num := by
    have hm := hMatmap
    rw [hMatt,hrat 0,hrat 1] at hm
    have hh := (div_eq_iff (div_ne_zero (hqpos 1).ne' (hqpos 0).ne')).mp hm
    field_simp [(hqpos 0).ne',(hqpos 1).ne'] at hh
    nlinarith only [hh]
  have hseedq (i) : qp pseed i=(q i:ℝ) := by
    fin_cases i
    · dsimp only [qp,pseed,rp,sp]; push_cast
      linear_combination (q 0:ℝ)*hchartR
    · dsimp only [qp,pseed,rp,sp]; push_cast
      linear_combination ((Mat 2:ℝ)*(rat 0).num+Mat 3*q 0)*hchartR+hdenR
  have hseeda (i) : ap pseed i=((rat i).num:ℝ) := by
    fin_cases i
    · dsimp only [ap,pseed,ep,vp]; push_cast
      linear_combination ((rat 0).num:ℝ)*hchartR
    · dsimp only [ap,pseed,ep,vp]; push_cast
      linear_combination ((Mat 0:ℝ)*(rat 0).num+Mat 1*q 0)*hchartR+hnumR
  have hseedroot (i) : iteratedDeriv 2 (f i) (x₀ i)/2=ap pseed i/qp pseed i := by
    rw [hseedq,hseeda,hlevel,hrat]
  have hdetp (i) : vp i*rp i-ep i*sp i=1 := by
    fin_cases i
    · exact hchart
    · change (Mat 0*v+Mat 1*s)*(Mat 2*e+Mat 3*r)-
        (Mat 0*e+Mat 1*r)*(Mat 2*v+Mat 3*s)=1
      linear_combination (v*r-e*s)*hMatdet+hchart
  have hseedSq i : |(round (x₀ i):ℝ)-(ar i:ℝ)|^2 ≤ M*R := by
    have hh := rounded_displacement_bound (x₀ i) (xref i)
    have hb : |(round (x₀ i):ℝ)-(ar i:ℝ)| ≤ H+|x₀ i-xref i|+1 := by
      dsimp only [ar]
      linarith only [hh,hH]
    exact (pow_le_pow_left₀ (abs_nonneg _) hb 2).trans (hbudget i)
  obtain ⟨_v,_hv,hthird,_hsecond,_hfirst,_hfourth⟩ := physicalModelPhase_actual_fourier_conditions
    Q K₀ rat vinv parity hσ hδ hF₃ hT hM hN hR hQ hscale hmesh
    hA hW hx₀ hden hinv hlevel hcolor hnear
  have hthird' : |mu 1*(qp pseed 1)^3/(mu 0*(qp pseed 0)^3)-1| ≤ B*R^2/N^2 := by
    simpa only [hseedq] using hthird
  exact physicalModelPhase_quartic_curvature_source_scale
    (u:=(pseed.1:ℝ)) (t:=(pseed.2:ℝ)) (x₀:=xref) (x₁:=x₀)
    (e:=fun i => (ep i:ℝ)) (r:=fun i => (rp i:ℝ))
    (v:=fun i => (vp i:ℝ)) (s:=fun i => (sp i:ℝ))
    hσ hδ hF hT hM hN hRone hNscale hscale hB hdmin hA hW hxref hx₀
    (fun i => by exact_mod_cast hrp i) ht
    (fun i => by change 0 < qp pseed i; rw [hseedq]; exact hqpos i)
    (fun i => by
      exact_mod_cast hdetp i) href hseedroot hseedSq
    (hd yseed hyseed) hthird'


                                                                 
                                                                     
                                                                     
                                                                          
theorem physicalModelPhase_original_seed_coordinate_heights
    (q : ℚ) (Q : ℕ) (e r v s : ℤ)
    {σ δ T M A W x : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hσ : 0 ≤ σ) (hF : Expdb.IsApproximateModelPhaseFunction F σ P δ)
    (hP : 1 ≤ P) (hT : 0 < T) (hM : 0 < M)
    (hA : M ≤ A) (hW : A+W ≤ 2*M) (hx : x∈Ioo 0 W)
    (hden : q.den ≤ Q)
    (hlevel : iteratedDeriv 2 (heathBrownPhysicalPhase F T M A 1) x/2=(q:ℝ)) :
    let V := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let p : ℤ × ℤ := (v*(q.den:ℤ)-s*q.num,r*q.num-e*(q.den:ℤ))
    |((p.1):ℝ)| ≤ (|(v:ℝ)|+|(s:ℝ)| *V)*(Q:ℝ) ∧
      |((p.2):ℝ)| ≤ (|(r:ℝ)| *V+|(e:ℝ)|)*(Q:ℝ) := by
  intro V p
  have hjet := approximateModelPhase_iteratedDeriv_abs_le hσ hF
    (heathBrownPhysicalPoint_mem_interior hM hA hW hx) 1 hP
  have hq : |(q:ℝ)| ≤ V := by
    rw [←hlevel,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2),
      heathBrownPhysicalPhase_iteratedDeriv hF.1 hM hA hW hx,
      one_mul,abs_mul,abs_of_pos (div_pos hT (pow_pos hM 2))]
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hjet (div_pos hT (pow_pos hM 2)).le)
      (by norm_num : (0:ℝ)≤2)).trans_eq (by dsimp only [V]; ring)
  have hV : 0 ≤ V := (abs_nonneg _).trans hq
  have hqd : (0:ℝ) < q.den := by exact_mod_cast q.pos
  have hQ : (q.den:ℝ) ≤ Q := by exact_mod_cast hden
  have hnumR : (q.num:ℝ)=(q:ℝ)*(q.den:ℝ) :=
    (div_eq_iff hqd.ne').mp (Rat.cast_def q).symm
  have hp₁ : ((p.1):ℝ)=((v:ℝ)-(s:ℝ)*(q:ℝ))*(q.den:ℝ) := by
    dsimp only [p]
    push_cast
    rw [hnumR]
    ring
  have hp₂ : ((p.2):ℝ)=((r:ℝ)*(q:ℝ)-(e:ℝ))*(q.den:ℝ) := by
    dsimp only [p]
    push_cast
    rw [hnumR]
    ring
  constructor
  · rw [hp₁,abs_mul,abs_of_pos hqd]
    apply (mul_le_mul_of_nonneg_right
      ((abs_sub _ _).trans (add_le_add le_rfl
        (by simpa only [abs_mul] using mul_le_mul_of_nonneg_left hq (abs_nonneg (s:ℝ))))) hqd.le).trans
    exact mul_le_mul_of_nonneg_left hQ
      (add_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) hV))
  · rw [hp₂,abs_mul,abs_of_pos hqd]
    apply (mul_le_mul_of_nonneg_right
      ((abs_sub _ _).trans (add_le_add
        (by simpa only [abs_mul] using mul_le_mul_of_nonneg_left hq (abs_nonneg (r:ℝ))) le_rfl)) hqd.le).trans
    exact mul_le_mul_of_nonneg_left hQ
      (add_nonneg (mul_nonneg (abs_nonneg _) hV) (abs_nonneg _))

                                                                    
                                                                     
                                                                   
theorem separated_reference_parent_denominator_bound
    (S : Finset ℝ) {δ : ℝ} {m n u v : ℤ}
    (hδ : 0 < δ) (hn : 0 < n) (hv : 0 < v)
    (hm : (m:ℝ)/n∈S) (hu : (u:ℝ)/v∈S)
    (hdet : |m*v-u*n|=1)
    (hsep : ∀ x∈S, ∀ y∈S, x ≠ y → δ/4 < |x-y|) :
    (n:ℝ)*(v:ℝ) < 4/δ ∧ (n:ℝ) < 4/δ := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hvR : (0:ℝ) < v := by exact_mod_cast hv
  have hvone : (1:ℝ) ≤ v := by exact_mod_cast hv
  have hdetR : |(m:ℝ)*v-u*n|=1 := by exact_mod_cast hdet
  have hgap : |(m:ℝ)/n-(u:ℝ)/v|=1/((n:ℝ)*v) := by
    rw [div_sub_div _ _ hnR.ne' hvR.ne',abs_div,mul_comm (n:ℝ) (u:ℝ),hdetR,
      abs_of_pos (mul_pos hnR hvR)]
  have hne : (m:ℝ)/n ≠ (u:ℝ)/v := by
    apply sub_ne_zero.mp
    apply abs_pos.mp
    rw [hgap]
    exact one_div_pos.mpr (mul_pos hnR hvR)
  have hsmall := hsep _ hm _ hu hne
  rw [hgap] at hsmall
  have hmul := (lt_div_iff₀ (mul_pos hnR hvR)).mp hsmall
  have hprod : (n:ℝ)*(v:ℝ) < 4/δ := by
    apply (lt_div_iff₀ hδ).mpr
    nlinarith only [hmul]
  refine ⟨hprod,?_⟩
  have hnv : (n:ℝ) ≤ (n:ℝ)*(v:ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hvone hnR.le
  exact hnv.trans_lt hprod

                                                                     
                                                                       
theorem separated_unit_reference_order_bound
    (S : Finset ℝ) {H : ℤ} {δ : ℝ}
    (hH : 1 ≤ H) (hδ : 0 < δ)
    (hseed : ∀ q : ℚ, (q.den:ℤ) ≤ H → (q:ℝ)∈Icc (0:ℝ) 1 → (q:ℝ)∈S)
    (hsep : ∀ x∈S, ∀ y∈S, x ≠ y → δ/4 < |x-y|) :
    (H:ℝ) < 4/δ := by
  have hHp : 0 < H := lt_of_lt_of_le (by decide : (0:ℤ)<1) hH
  have hHR : (1:ℝ) ≤ H := by exact_mod_cast hH
  have hHpR : (0:ℝ) < H := zero_lt_one.trans_le hHR
  have hzero : (0:ℝ)∈S := by
    exact_mod_cast hseed 0 (by simpa only [Rat.den_zero,Int.natCast_one] using hH)
      (by norm_num)
  have hunit : (1:ℝ)/H∈S := by
    have hq := hseed (Rat.divInt 1 H)
      (Int.le_of_dvd hHp (Rat.den_dvd 1 H))
      (by
        rw [Rat.cast_divInt,Int.cast_one]
        exact ⟨(one_div_pos.mpr hHpR).le,(div_le_one hHpR).mpr hHR⟩)
    simpa only [Rat.cast_divInt,Int.cast_one] using hq
  have hsmall := hsep _ hunit _ hzero (one_div_ne_zero hHpR.ne')
  rw [sub_zero,abs_of_pos (one_div_pos.mpr hHpR)] at hsmall
  have hh := (lt_div_iff₀ hHpR).mp hsmall
  apply (lt_div_iff₀ hδ).mpr
  nlinarith only [hh]

                                                              
                                                                     
                                                                  
theorem exists_source_interval_reference_system_bounded {δ : ℝ}
    (hδ : 0 < δ) (hδmax : δ ≤ 1) :
    ∃ H : ℤ, 2 ≤ H ∧ (H:ℝ)<4/δ ∧ ∀ L U : ℤ, L ≤ U →
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
            1 ≤ δ*((max b d:ℤ):ℝ)^2) ∧
        ∀ z∈T, ∃ a b : ℤ, z=(a:ℝ)/b ∧ IsCoprime a b ∧ 0 < b ∧
          (b:ℝ)<4/δ ∧ |(a:ℝ)| ≤ max |(L:ℝ)| |(U:ℝ)+1| *(4/δ) := by
  classical
  obtain ⟨H,hH,hbuild⟩ := exists_source_interval_reference_system hδ hδmax
  obtain ⟨S₀,hseed₀,_hpoints₀,_hlabels₀,hsep₀,_hcover₀,_hgaps₀⟩ :=
    hbuild 0 0 le_rfl
  have hHbound : (H:ℝ) < 4/δ := separated_unit_reference_order_bound S₀
    (by omega) hδ
    (fun q hq hqI => hseed₀ q hq
      (by simpa only [Int.cast_zero,zero_add] using hqI)) hsep₀
  refine ⟨H,hH,hHbound,?_⟩
  intro L U hLU
  obtain ⟨S,hseed,hpoints,hlabels,hsep,hcover,hgaps⟩ := hbuild L U hLU
  refine ⟨S,hseed,hpoints,hlabels,hsep,hcover,hgaps,?_⟩
  have hfinish (z : ℝ) (hz : z∈S) (m n : ℤ)
      (hval : z=(m:ℝ)/n) (hcop : IsCoprime m n) (hn : 0 < n)
      (hnb : (n:ℝ)<4/δ) :
      ∃ a b : ℤ, z=(a:ℝ)/b ∧ IsCoprime a b ∧ 0 < b ∧
        (b:ℝ)<4/δ ∧ |(a:ℝ)| ≤ max |(L:ℝ)| |(U:ℝ)+1| *(4/δ) := by
    refine ⟨m,n,hval,hcop,hn,hnb,?_⟩
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    have hzi := hpoints z hz
    have hzabs : |z| ≤ max |(L:ℝ)| |(U:ℝ)+1| := by
      apply abs_le.mpr
      exact ⟨(neg_le_neg (le_max_left _ _)).trans ((neg_abs_le _).trans hzi.1),
        hzi.2.trans ((le_abs_self _).trans (le_max_right _ _))⟩
    have hnum : (m:ℝ)=z*(n:ℝ) := (div_eq_iff hnR.ne').mp hval.symm
    rw [hnum,abs_mul,abs_of_pos hnR]
    exact mul_le_mul hzabs hnb.le hnR.le ((abs_nonneg _).trans (le_max_left _ _))
  intro z hz
  rcases hlabels z hz with ⟨q,hval,hqH⟩ |
    ⟨m,n,u,v,hval,hcop,hn,_hnscale,hv,hvH,huI,hdet⟩
  · apply hfinish z hz q.num q.den
    · simpa only [Rat.cast_def,Int.cast_natCast] using hval
    · exact q.isCoprime_num_den
    · exact_mod_cast q.pos
    · exact (show (q.den:ℝ) ≤ H by exact_mod_cast hqH).trans_lt hHbound
  · have hparent : (u:ℝ)/v∈S := by
      have hh := hseed (Rat.divInt u v)
        ((Int.le_of_dvd hv (Rat.den_dvd u v)).trans hvH)
        (by simpa only [Rat.cast_divInt] using huI)
      simpa only [Rat.cast_divInt] using hh
    exact hfinish z hz m n hval hcop hn
      (separated_reference_parent_denominator_bound S hδ hn hv
        (hval ▸ hz) hparent hdet hsep).2

                                                             
                                                                     
                                                                
                                           
theorem signed_dyadic_first_coefficient_spread
    {f : ℝ → ℝ} {l w x y a ac bc D : ℝ} {b : ℤ}
    (ha : 0 < a) (hside : (a ≤ l ∧ w ≤ 2*a) ∨ (-2*a ≤ l ∧ w ≤ -a))
    (hD : D ≤ 1/2)
    (hshape : ConvexOn ℝ (Icc l w) f ∨ ConcaveOn ℝ (Icc l w) f)
    (hder : ∀ z∈Icc l w, DifferentiableAt ℝ f z)
    (hx : x∈Icc l w) (hy : y∈Icc l w)
    (hresx : |(ac-round (ac-deriv f x))*x+bc-b-f x| ≤ D*|x|)
    (hresy : |(ac-round (ac-deriv f y))*y+bc-b-f y| ≤ D*|y|) :
    |round (ac-deriv f y)-round (ac-deriv f x)| ≤ (5:ℤ) := by
  have hnegative {f : ℝ → ℝ}
      (hc : ConvexOn ℝ (Icc l w) f)
      (hd : ∀ z∈Icc l w, DifferentiableAt ℝ f z) :
      (-w)*|deriv f y-deriv f x| ≤
        |(y*deriv f y-f y)-(x*deriv f x-f x)| := by
    have hord (u v : ℝ) (hu : u∈Icc l w) (hv : v∈Icc l w) (huv : u ≤ v) :
        (-w)*|deriv f v-deriv f u| ≤
          |(v*deriv f v-f v)-(u*deriv f u-f u)| := by
      rcases eq_or_lt_of_le huv with rfl | huv
      · simp
      have hm := hc.monotoneOn_deriv hd hu hv huv.le
      have hs := hc.deriv_le_slope hu hv huv (hd u hu)
      rw [slope_def_field] at hs
      have ht := (le_div_iff₀ (sub_pos.mpr huv)).mp hs
      have hw := mul_le_mul_of_nonneg_right hv.2 (sub_nonneg.mpr hm)
      rw [abs_of_nonneg (sub_nonneg.mpr hm)]
      have hab := neg_abs_le ((v*deriv f v-f v)-(u*deriv f u-f u))
      nlinarith only [ht,hw,hab]
    rcases le_total x y with hxy | hyx
    · exact hord x y hx hy hxy
    · simpa only [abs_sub_comm] using hord y x hy hx hyx
  have hnweighted :
      (-w)*|deriv f y-deriv f x| ≤
        |(y*deriv f y-f y)-(x*deriv f x-f x)| := by
    rcases hshape with hc | hc
    · exact hnegative hc hder
    · have hh := hnegative hc.neg (fun z hz => (hder z hz).neg)
      have he (z : ℝ) : deriv (-f) z = -deriv f z := deriv.neg
      simp only [he,Pi.neg_apply] at hh
      have he₁ : -deriv f y- -deriv f x = -(deriv f y-deriv f x) := by ring
      have he₂ : (y*(-deriv f y)- -f y)-(x*(-deriv f x)- -f x) =
          -((y*deriv f y-f y)-(x*deriv f x-f x)) := by ring
      simpa only [he₁,he₂,abs_neg] using hh
  have hweighted :
      a*|deriv f y-deriv f x| ≤
        |(y*deriv f y-f y)-(x*deriv f x-f x)| := by
    rcases hside with hpos | hneg
    · exact (mul_le_mul_of_nonneg_right hpos.1 (abs_nonneg _)).trans
        (curvature_branch_weighted_derivative_difference hshape hder hx hy)
    · exact (mul_le_mul_of_nonneg_right (by linarith only [hneg.2])
        (abs_nonneg _)).trans hnweighted
  have hsize (z : ℝ) (hz : z∈Icc l w) : |z| ≤ 2*a := by
    apply abs_le.mpr
    rcases hside with hpos | hneg
    · constructor <;> linarith only [hz.1,hz.2,hpos.1,hpos.2,ha]
    · constructor <;> linarith only [hz.1,hz.2,hneg.1,hneg.2,ha]
  have hlevel (z : ℝ)
      (hrz : |(ac-round (ac-deriv f z))*z+bc-b-f z| ≤ D*|z|) :
      |z*deriv f z-f z+bc-b| ≤ |z| := by
    have hr := abs_sub_round (ac-deriv f z)
    have hid : z*deriv f z-f z+bc-b =
        ((ac-round (ac-deriv f z))*z+bc-b-f z)-
          z*((ac-deriv f z)-round (ac-deriv f z)) := by ring
    rw [hid]
    apply (abs_sub _ _).trans
    rw [abs_mul]
    have hh := mul_le_mul_of_nonneg_left hr (abs_nonneg z)
    have hdz := mul_le_mul_of_nonneg_right hD (abs_nonneg z)
    linarith only [hrz,hh,hdz]
  have hh := abs_sub (y*deriv f y-f y+bc-b) (x*deriv f x-f x+bc-b)
  have hid : (y*deriv f y-f y+bc-b)-(x*deriv f x-f x+bc-b) =
      (y*deriv f y-f y)-(x*deriv f x-f x) := by ring
  rw [hid] at hh
  have hspread : |deriv f y-deriv f x| ≤ 4 := by
    apply (mul_le_mul_iff_right₀ ha).mp
    nlinarith only [hweighted,hh,hlevel x hresx,hlevel y hresy,hsize x hx,hsize y hy]
  have hry := abs_sub_round (ac-deriv f y)
  have hrx := abs_sub_round (ac-deriv f x)
  have ht := abs_sub_le ((round (ac-deriv f y):ℤ):ℝ)
    (ac-deriv f y) ((round (ac-deriv f x):ℤ):ℝ)
  have ht' := abs_sub_le (ac-deriv f y) (ac-deriv f x)
    ((round (ac-deriv f x):ℤ):ℝ)
  have hry' : |((round (ac-deriv f y):ℤ):ℝ)-(ac-deriv f y)| ≤ 1/2 := by
    simpa only [abs_sub_comm] using hry
  have he : |(ac-deriv f y)-(ac-deriv f x)|=|deriv f y-deriv f x| := by
    have hi : (ac-deriv f y)-(ac-deriv f x)=-(deriv f y-deriv f x) := by ring
    rw [hi,abs_neg]
  rw [he] at ht'
  have hb : |((round (ac-deriv f y):ℤ):ℝ)-((round (ac-deriv f x):ℤ):ℝ)| ≤ 5 := by
    linarith only [ht,ht',hry',hrx,hspread]
  exact_mod_cast hb

                                                                
                                                                       
theorem signed_dyadic_curvature_branch_coefficient_pair_count
    {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    {f : ℝ → ℝ} {l w a₀ ac bc D b₀ : ℝ}
    (ha₀ : 0 < a₀)
    (hside : (a₀ ≤ l ∧ w ≤ 2*a₀) ∨ (-2*a₀ ≤ l ∧ w ≤ -a₀)) (hD : D ≤ 1/2)
    (hshape : ConvexOn ℝ (Icc l w) f ∨ ConcaveOn ℝ (Icc l w) f)
    (hder : ∀ z∈Icc l w, DifferentiableAt ℝ f z)
    (hx : ∀ i∈S, x i∈Icc l w)
    (hweighted : ∀ i∈S, |bc-f (x i)+x i*deriv f (x i)-b₀| ≤ 1/2)
    (hres : ∀ i∈S,
      |(ac-round (ac-deriv f (x i)))*x i+
        bc-round (bc-f (x i)+x i*deriv f (x i))-f (x i)| ≤ D*|x i|) :
    (S.image (fun i => (round (ac-deriv f (x i)),
      round (bc-f (x i)+x i*deriv f (x i))))).card ≤ 18 := by
  classical
  have firstCount (V : Finset ι) (b : ℤ)
      (hvx : ∀ i∈V, x i∈Icc l w)
      (hvres : ∀ i∈V, |(ac-round (ac-deriv f (x i)))*x i+bc-b-f (x i)| ≤ D*|x i|) :
      (V.image (fun i => round (ac-deriv f (x i)))).card ≤ 6 := by
    let A := V.image (fun i => round (ac-deriv f (x i)))
    change A.card ≤ 6
    by_cases hA : A.Nonempty
    · let m := A.min' hA
      have hm : m∈A := Finset.min'_mem _ _
      obtain ⟨j,hj,hjm⟩ := Finset.mem_image.mp hm
      have hbounds : ∀ a∈A, (m:ℝ) ≤ a ∧ (a:ℝ) ≤ (m:ℝ)+5 := by
        intro a ha
        have hlo : m ≤ a := Finset.min'_le A a ha
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
        have hs := signed_dyadic_first_coefficient_spread ha₀ hside hD hshape hder
          (hvx j hj) (hvx i hi) (hvres j hj) (hvres i hi)
        rw [hjm] at hs
        have hu : round (ac-deriv f (x i)) ≤ m+5 := by
          have hh := (abs_le.mp hs).2
          omega
        exact ⟨by exact_mod_cast hlo,by exact_mod_cast hu⟩
      have hh := integer_card_le_interval_length_add_one A
        (show (m:ℝ) ≤ (m:ℝ)+5 by linarith) hbounds
      have hc : (A.card:ℝ) ≤ 6 := by linarith only [hh]
      exact_mod_cast hc
    · have he : A=∅ := Finset.not_nonempty_iff_eq_empty.mp hA
      simp only [he,Finset.card_empty,Nat.zero_le]
  let a := fun i => round (ac-deriv f (x i))
  let b := fun i => round (bc-f (x i)+x i*deriv f (x i))
  let T := S.image (fun i => (a i,b i))
  let E := T.image Prod.snd
  change T.card ≤ 18
  have hE : E.card ≤ 3 := by
    have hsub : E ⊆ Finset.Icc (round b₀-1) (round b₀+1) := by
      intro n hn
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
      have hh := rounded_displacement_bound (bc-f (x i)+x i*deriv f (x i)) b₀
      have hb := hweighted i hi
      have hlt : |((b i-round b₀:ℤ):ℝ)| < 2 := by
        rw [Int.cast_sub]
        dsimp only [b]
        linarith only [hh,hb]
      have hi' : |b i-round b₀| < 2 := by exact_mod_cast hlt
      have hab := abs_lt.mp hi'
      exact Finset.mem_Icc.mpr ⟨by dsimp; omega,by dsimp; omega⟩
    apply (Finset.card_le_card hsub).trans
    rw [Int.card_Icc]
    omega
  have hfiber (n : ℤ) : (T.filter (fun p => p.2=n)).card ≤ 6 := by
    let V := S.filter (fun i => b i=n)
    let P := T.filter (fun p => p.2=n)
    have hvx : ∀ i∈V, x i∈Icc l w := fun i hi => hx i (Finset.mem_filter.mp hi).1
    have hvres : ∀ i∈V, |(ac-round (ac-deriv f (x i)))*x i+bc-n-f (x i)| ≤ D*|x i| := by
      intro i hi
      obtain ⟨hi,hbi⟩ := Finset.mem_filter.mp hi
      have hh := hres i hi
      change |(ac-round (ac-deriv f (x i)))*x i+bc-b i-f (x i)| ≤ D*|x i| at hh
      rwa [hbi] at hh
    have hv := firstCount V n hvx hvres
    have hinj : Set.InjOn (fun p : ℤ × ℤ => p.1) (P : Set (ℤ × ℤ)) := by
      intro p hp q hq he
      exact Prod.ext he ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm)
    have hcard : (P.image Prod.fst).card=P.card := Finset.card_image_of_injOn hinj
    have hsub : P.image Prod.fst ⊆ V.image a := by
      intro z hz
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hp,hpn⟩ := Finset.mem_filter.mp hp
      obtain ⟨i,hi,hpi⟩ := Finset.mem_image.mp hp
      have hbi : b i=n := by rw [←hpi] at hpn; exact hpn
      refine Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,hbi⟩,?_⟩
      exact congrArg Prod.fst hpi
    change P.card ≤ 6
    rw [←hcard]
    exact (Finset.card_le_card hsub).trans hv
  have hsum : T.card=∑ n∈E, (T.filter (fun p => p.2=n)).card :=
    Finset.card_eq_sum_card_fiberwise (fun p hp => Finset.mem_image_of_mem Prod.snd hp)
  rw [hsum]
  calc
    _ ≤ ∑ _n∈E, 6 := Finset.sum_le_sum (fun n _ => hfiber n)
    _ = E.card*6 := by simp
    _ ≤ 18 := by omega

                                                                      
                                                                 
theorem quartic_phase_signed_dyadic_root_cell_coefficient_count
    {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    {μ ν r s μ₁ ν₁ r₁ s₁ l w a₀ ac bc D b₀ : ℝ} {k : ℕ}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hden : ∀ z∈Icc l w, r*z+s ≠ 0)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (ha₀ : 0 < a₀)
    (hside : (a₀ ≤ l ∧ w ≤ 2*a₀) ∨ (-2*a₀ ≤ l ∧ w ≤ -a₀)) (hD : D ≤ 1/2) :
    let φ := fun z => rationalPhase μ r s μ₁ r₁ s₁ z-
      quarticPhase μ ν r s μ₁ ν₁ r₁ s₁ z
    let Z := (quarticCurvatureNumerator μ ν r s μ₁ ν₁ r₁ s₁).roots.toFinset
    (∀ i∈S, x i∈finiteBoundaryCell Z l w k) →
    (∀ i∈S, |bc-φ (x i)+x i*deriv φ (x i)-b₀| ≤ 1/2) →
    (∀ i∈S, |(ac-round (ac-deriv φ (x i)))*x i+
      bc-round (bc-φ (x i)+x i*deriv φ (x i))-φ (x i)| ≤ D*|x i|) →
    (S.image (fun i => (round (ac-deriv φ (x i)),
      round (bc-φ (x i)+x i*deriv φ (x i))))).card ≤ 18 := by
  classical
  intro φ Z hx hweighted hres
  by_cases hs : S.Nonempty
  · let V := S.image x
    have hv : V.Nonempty := hs.image x
    let a := V.min' hv
    let b := V.max' hv
    have ha : a∈V := Finset.min'_mem V hv
    have hb : b∈V := Finset.max'_mem V hv
    have hac : a∈finiteBoundaryCell Z l w k := by
      obtain ⟨i,hi,he⟩ := Finset.mem_image.mp ha
      exact he ▸ hx i hi
    have hbc : b∈finiteBoundaryCell Z l w k := by
      obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hb
      exact he ▸ hx i hi
    have hseg : Icc a b ⊆ finiteBoundaryCell Z l w k :=
      (finiteBoundaryCell_ordConnected Z l w k).out hac hbc
    have hshape := quartic_phase_shape_on_curvature_root_cell hμ hμ₁ hr hr₁ hden hden₁ hseg
    have hder : ∀ z∈Icc a b, DifferentiableAt ℝ φ z := fun z hz =>
      (quartic_phase_second_derivative_data (ν:=ν) (ν₁:=ν₁) hμ hμ₁ hr hr₁
        (hden z (hseg hz).1) (hden₁ z (hseg hz).1)).1
    have hxa : ∀ i∈S, x i∈Icc a b := by
      intro i hi
      have hxi : x i∈V := Finset.mem_image_of_mem x hi
      exact ⟨Finset.min'_le V (x i) hxi,Finset.le_max' V (x i) hxi⟩
    have hside' : (a₀ ≤ a ∧ b ≤ 2*a₀) ∨ (-2*a₀ ≤ a ∧ b ≤ -a₀) := by
      rcases hside with hp | hn
      · exact Or.inl ⟨hp.1.trans hac.1.1,hbc.1.2.trans hp.2⟩
      · exact Or.inr ⟨hn.1.trans hac.1.1,hbc.1.2.trans hn.2⟩
    exact signed_dyadic_curvature_branch_coefficient_pair_count S x
      ha₀ hside' hD hshape hder hxa hweighted hres
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

                                                                   
                                                                 
theorem quartic_phase_signed_subfamily_coefficient_color_count
    {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    {μ ν r s μ₁ ν₁ r₁ s₁ U l w x₀ ac bc D a b : ℝ} {k : Fin 17}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hden : ∀ z∈Icc l w, r*z+s ≠ 0)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (ha : 0 < a) (hband : ∀ i∈S, |x i|∈Icc a b) (hD : D ≤ 1/2)
    (hheight : U*(w-l)*(max |l| |w|+(w-l)/2) ≤ 1/2) :
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun z => g z-h z
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    x₀∈finiteBoundaryCell Z l w k →
    (∀ i∈S, x i∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g x₀-iteratedDeriv 2 h x₀| ≤ U →
    (∀ i∈S, |(ac-round (ac-deriv φ (x i)))*x i+
      bc-round (bc-φ (x i)+x i*deriv φ (x i))-φ (x i)| ≤ D*|x i|) →
    (S.image (fun i => (round (ac-deriv φ (x i)),
      round (bc-φ (x i)+x i*deriv φ (x i))))).card ≤ 5+216*(⌊Real.logb 2 (b/a)⌋₊+1) := by
  classical
  intro g h φ Z hx₀ hx hcurv hres
  let P := quarticCurvatureNumerator μ ν r s μ₁ ν₁ r₁ s₁
  let V := P.roots.toFinset
  let c := fun z => (round (ac-deriv φ z),round (bc-φ z+z*deriv φ z))
  let K := ⌊Real.logb 2 (b/a)⌋₊+1
  let lo := fun (n : ℕ) (e : Bool) => max l (if e then a*(2:ℝ)^n else -2*(a*(2:ℝ)^n))
  let hi := fun (n : ℕ) (e : Bool) => min w (if e then 2*(a*(2:ℝ)^n) else -(a*(2:ℝ)^n))
  let fiber := fun (n : ℕ) (e : Bool) (j : ℕ) => S.filter (fun i =>
    x i∈Icc (lo n e) (hi n e) ∧ x i∉V ∧ (V.filter (fun z => z<x i)).card=j)
  let labels := fun n e j => (fiber n e j).image (fun i => c (x i))
  have hv : V.card ≤ 5 := (Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' _).trans (quarticCurvatureNumerator_degree μ ν r s μ₁ ν₁ r₁ s₁))
  have hwgt (i) (hiS : i∈S) :
      |bc-φ (x i)+x i*deriv φ (x i)-(bc-φ x₀+x₀*deriv φ x₀)| ≤ 1/2 :=
    quartic_phase_weighted_coefficient_variation hμ hμ₁ hr hr₁ hden hden₁ hheight
      hx₀ (hx i hiS) hcurv
  have hsubI (n : ℕ) (e : Bool) : Icc (lo n e) (hi n e) ⊆ Icc l w := by
    intro z hz
    exact ⟨(le_max_left _ _).trans hz.1,hz.2.trans (min_le_left _ _)⟩
  have hlabels (n : ℕ) (e : Bool) (j : ℕ) : (labels n e j).card ≤ 18 := by
    have hapos : 0 < a*(2:ℝ)^n := mul_pos ha (pow_pos (by norm_num) n)
    have hside :
        (a*(2:ℝ)^n ≤ lo n e ∧ hi n e ≤ 2*(a*(2:ℝ)^n)) ∨
        (-2*(a*(2:ℝ)^n) ≤ lo n e ∧ hi n e ≤ -(a*(2:ℝ)^n)) := by
      cases e
      · exact Or.inr ⟨le_max_right _ _,min_le_right _ _⟩
      · exact Or.inl ⟨le_max_right _ _,min_le_right _ _⟩
    apply quartic_phase_signed_dyadic_root_cell_coefficient_count (fiber n e j) x
      hμ hμ₁ hr hr₁ (fun z hz => hden z (hsubI n e hz))
      (fun z hz => hden₁ z (hsubI n e hz)) hapos hside hD
    · intro i hiS
      obtain ⟨_,hxi,hvi,hrank⟩ := Finset.mem_filter.mp hiS
      exact ⟨hxi,hvi,hrank⟩
    · intro i hiS
      exact hwgt i (Finset.mem_filter.mp hiS).1
    · intro i hiS
      exact hres i (Finset.mem_filter.mp hiS).1
  have hcover (i) (hiS : i∈S) : ∃ n∈Finset.range K, ∃ e : Bool, x i∈Icc (lo n e) (hi n e) := by
    have hxi := (hx i hiS).1
    have hbi := hband i hiS
    have hwpos : 0 < b := ha.trans_le (hbi.1.trans hbi.2)
    obtain ⟨n,hnL,hnU⟩ := exists_nat_pow_near
      ((one_le_div ha).mpr hbi.1) (by norm_num : (1:ℝ) < 2)
    have hlow : a*(2:ℝ)^n ≤ |x i| := by
      have hh := (le_div_iff₀ ha).mp hnL
      nlinarith only [hh]
    have hupp : |x i| ≤ 2*(a*(2:ℝ)^n) := by
      have hh := (div_lt_iff₀ ha).mp hnU
      rw [pow_succ] at hh
      nlinarith only [hh]
    have hpw : (2:ℝ)^n ≤ b/a := hnL.trans (div_le_div_of_nonneg_right hbi.2 ha.le)
    have hnlog : (n:ℝ) ≤ Real.logb 2 (b/a) := by
      apply (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2) (div_pos hwpos ha)).mpr
      simpa only [Real.rpow_natCast] using hpw
    have hn : n < K := by
      have hh := Nat.le_floor hnlog
      dsimp only [K]
      omega
    refine ⟨n,Finset.mem_range.mpr hn,?_⟩
    by_cases hxpos : 0 ≤ x i
    · rw [abs_of_nonneg hxpos] at hlow hupp
      exact ⟨true,max_le hxi.1 hlow,le_min hxi.2 hupp⟩
    · rw [abs_of_neg (lt_of_not_ge hxpos)] at hlow hupp
      refine ⟨false,?_⟩
      change max l (-2*(a*(2:ℝ)^n)) ≤ x i ∧ x i ≤ min w (-(a*(2:ℝ)^n))
      exact ⟨max_le hxi.1 (by linarith only [hupp]),
        le_min hxi.2 (by linarith only [hlow])⟩
  have hsub : S.image (fun i => c (x i)) ⊆
      V.image c ∪ (Finset.range K).biUnion (fun n => Finset.univ.biUnion (fun e : Bool => (Finset.range 6).biUnion (labels n e))) := by
    intro z hz
    obtain ⟨i,hiS,rfl⟩ := Finset.mem_image.mp hz
    by_cases hiv : x i∈V
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem c hiv)
    · apply Finset.mem_union_right
      obtain ⟨n,hn,e,hxi⟩ := hcover i hiS
      apply Finset.mem_biUnion.mpr
      refine ⟨n,hn,Finset.mem_biUnion.mpr ⟨e,Finset.mem_univ _,Finset.mem_biUnion.mpr ?_⟩⟩
      have hrank : (V.filter (fun z => z<x i)).card < 6 :=
        lt_of_le_of_lt (Finset.card_filter_le _ _) (by omega)
      refine ⟨(V.filter (fun z => z<x i)).card,Finset.mem_range.mpr hrank,?_⟩
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨hiS,hxi,hiv,rfl⟩,rfl⟩
  have hroot : (V.image c).card ≤ 5 := (Finset.card_image_le).trans hv
  have hbin (n : ℕ) (e : Bool) : ((Finset.range 6).biUnion (labels n e)).card ≤ 108 := by
    calc
      _ ≤ ∑ j∈Finset.range 6, (labels n e j).card := Finset.card_biUnion_le
      _ ≤ ∑ _j∈Finset.range 6, 18 := Finset.sum_le_sum (fun j _ => hlabels n e j)
      _ = 108 := by norm_num
  have hb (n : ℕ) :
      (Finset.univ.biUnion (fun e : Bool => (Finset.range 6).biUnion (labels n e))).card ≤ 216 := by
    calc
      _ ≤ ∑ e : Bool, ((Finset.range 6).biUnion (labels n e)).card := Finset.card_biUnion_le
      _ ≤ ∑ _e : Bool, 108 := Finset.sum_le_sum (fun e _ => hbin n e)
      _ = 216 := by norm_num
  have hrest : ((Finset.range K).biUnion (fun n =>
      Finset.univ.biUnion (fun e : Bool => (Finset.range 6).biUnion (labels n e)))).card ≤
      216*K := by
    calc
      _ ≤ ∑ n∈Finset.range K,
          (Finset.univ.biUnion (fun e : Bool => (Finset.range 6).biUnion (labels n e))).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _n∈Finset.range K, 216 := Finset.sum_le_sum (fun n _ => hb n)
      _ = 216*K := by simp [Nat.mul_comm]
  change (S.image (fun i => c (x i))).card ≤ 5+216*K
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))

                                                                      
                                                                             
theorem quartic_phase_signed_integer_height_source_cutoff_coefficient_count
    {Kcoord : ℕ}
    {ι : Type*} (S : Finset ι) (p : ι → ℤ × ℤ)
    {μ ν r s μ₁ ν₁ r₁ s₁ C J N R d Bcut l w x₀ ac bc D P₁ P₂ : ℝ} {k : Fin 17}
    (hμ : 0 < μ) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hC : 0 ≤ C) (hJ : 0 < J) (hN : 0 < N) (hR : 0 < R) (hd : 0 < d)
    (hden : ∀ z∈Icc l w, d ≤ r*z+s ∧ r*z+s ≤ 2*d)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hcoord : |r| * max |l| |w| ≤ (Kcoord:ℝ)*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hBcut : 0 < Bcut) (hBsize : ((2*Kcoord+1:ℕ):ℝ)*C*J ≤ Bcut)
    (hG : |minorArcCoordinate μ r s l| ≤ |r| *N^2/(Bcut*R^2))
    (hP₂ : 0 < P₂) (hD₀ : 0 ≤ D) (hD : D ≤ 1/2)
    (hp : ∀ i∈S, 0 < (p i).2)
    (hheight : ∀ i∈S, |((p i).1:ℝ)| ≤ P₁ ∧ ((p i).2:ℝ) ≤ P₂) :
    let U := C*R^4/(N*d^3)
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun z => g z-h z
    let y := fun i => ((p i).1:ℝ)/(p i).2
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    x₀∈finiteBoundaryCell Z l w k →
    (∀ i∈S, y i∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g x₀-iteratedDeriv 2 h x₀| ≤ U →
    (∀ i∈S, |(ac-round (ac-deriv φ (y i)))*y i+
      bc-round (bc-φ (y i)+y i*deriv φ (y i))-φ (y i)| ≤ D/(p i).2) →
    (S.image (fun i => (round (ac-deriv φ (y i)),
      round (bc-φ (y i)+y i*deriv φ (y i))))).card ≤ 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1) := by
  classical
  intro U g h φ y Z hx₀ hy hcurv hres
  have hlw : l ≤ w := hx₀.1.1.trans hx₀.1.2
  have hweighted := quartic_weighted_coefficient_budget_of_bounded_source_chart
    hC hJ hμ hN hR hr hd hlw
    (le_min (hden l ⟨le_rfl,hlw⟩).1 (hden w ⟨hlw,le_rfl⟩).1)
    (max_le (hden l ⟨le_rfl,hlw⟩).2 (hden w ⟨hlw,le_rfl⟩).2)
    hcoord hμupper hBcut
    (by simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hBsize) hG
  let T := S.filter (fun i => (p i).1 ≠ 0)
  have ht (i) (hi : i∈T) : (1:ℝ) ≤ |((p i).1:ℝ)| := by
    exact_mod_cast Int.one_le_abs (Finset.mem_filter.mp hi).2
  have hband i (hi : i∈T) : |y i|∈Icc (1/P₂) P₁ := by
    have hiS := (Finset.mem_filter.mp hi).1
    have hu : (0:ℝ) < (p i).2 := by exact_mod_cast hp i hiS
    have huone : (1:ℝ) ≤ (p i).2 := by exact_mod_cast hp i hiS
    have htone := ht i hi
    have hP₁ : 0 ≤ P₁ := (zero_le_one.trans htone).trans (hheight i hiS).1
    change |((p i).1:ℝ)/(p i).2|∈Icc (1/P₂) P₁
    rw [abs_div,abs_of_pos hu]
    constructor
    · exact (one_div_le_one_div_of_le hu (hheight i hiS).2).trans
        (div_le_div_of_nonneg_right htone hu.le)
    · apply (div_le_iff₀ hu).mpr
      exact (hheight i hiS).1.trans
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left huone hP₁)
  let c := fun z => (round (ac-deriv φ z),round (bc-φ z+z*deriv φ z))
  have hcount : (T.image (fun i => c (y i))).card ≤
      5+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1) := by
    have hh := quartic_phase_signed_subfamily_coefficient_color_count (ac:=ac) (bc:=bc) T y
      hμ.ne' hμ₁ hr hr₁ (fun z hz => (hd.trans_le (hden z hz).1).ne') hden₁
      (one_div_pos.mpr hP₂) hband hD hweighted hx₀
      (fun i hi => hy i (Finset.mem_filter.mp hi).1) hcurv
    rw [one_div,div_inv_eq_mul] at hh
    apply hh
    intro i hi
    have hiS := (Finset.mem_filter.mp hi).1
    have hu : (0:ℝ) < (p i).2 := by exact_mod_cast hp i hiS
    apply (hres i hiS).trans
    change D/(p i).2 ≤ D*|((p i).1:ℝ)/(p i).2|
    rw [abs_div,abs_of_pos hu,←mul_div_assoc]
    exact div_le_div_of_nonneg_right
      (by nlinarith only [mul_le_mul_of_nonneg_left (ht i hi) hD₀]) hu.le
  have hsub : S.image (fun i => c (y i)) ⊆ {c 0} ∪ T.image (fun i => c (y i)) := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    by_cases ht0 : (p i).1=0
    · have hy0 : y i=0 := by simp [y,ht0]
      exact Finset.mem_union_left _ (by simp [hy0])
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _
        (Finset.mem_filter.mpr ⟨hi,ht0⟩))
  change (S.image (fun i => c (y i))).card ≤ _
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [Finset.card_singleton] at hh
  omega

                                                                    
                                                                        
                                                           
theorem source_reference_seed_height_polynomial
    {σ J Jv T M N R Q U V e r v s : ℝ}
    (hσ : 0 < σ) (hJ : 0 ≤ J) (hJv : 0 ≤ Jv)
    (hT : 0 < T) (hM : 0 < M) (hR : 1 ≤ R)
    (hRQ : R ≤ Q) (hQN : Q ≤ N) (hNM : N^2 ≤ M)
    (hU : 1 ≤ U) (hscale : T*N*R^2=M^3)
    (hV₀ : 0 ≤ V) (hV : V ≤ Jv*T/(2*M^2))
    (hr : |r| ≤ 4*R^2/U) (hs : |s| ≤ 4*R^2/U)
    (he : |e| ≤ (3*J*T/(2*σ*M^2)+1)*(4*R^2/U))
    (hv : |v| ≤ (3*J*T/(2*σ*M^2)+1)*(4*R^2/U)) :
    let C := 1+4*(3*J/(2*σ)+1+Jv/2)
    1 ≤ T ∧ 1 ≤ C ∧
      1+(|v|+|s| *V)*Q ≤ C*T^3 ∧
      1+(|r| *V+|e|)*Q ≤ C*T^3 := by
  intro C
  have hN : 1 ≤ N := hR.trans (hRQ.trans hQN)
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hQ₀ : 0 ≤ Q := (zero_lt_one.trans_le (hR.trans hRQ)).le
  have hR₀ : 0 ≤ R := (zero_lt_one.trans_le hR).le
  have hNM' : N ≤ M := (by nlinarith only [hN] : N ≤ N^2).trans hNM
  have hM1 : 1 ≤ M := hN.trans hNM'
  have hR₂ : R^2 ≤ M :=
    (pow_le_pow_left₀ hR₀ (hRQ.trans hQN) 2).trans hNM
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
  have hT1 : 1 ≤ T := hM1.trans hMT
  have hQT : Q ≤ T := hQN.trans (hNM'.trans hMT)
  have hM₂ : 1 ≤ M^2 := one_le_pow₀ hM1
  have hK : 4*R^2/U ≤ 4*T :=
    (div_le_self (by positivity) hU).trans (mul_le_mul_of_nonneg_left (hR₂.trans hMT) (by norm_num))
  let c := 3*J/(2*σ)
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hcurv : 3*J*T/(2*σ*M^2) ≤ c*T := by
    calc
      _ = c*T/M^2 := by dsimp only [c]; ring
      _ ≤ c*T := div_le_self (mul_nonneg hc hT.le) hM₂
  have hV' : V ≤ (Jv/2)*T := hV.trans (by
    calc
      Jv*T/(2*M^2) = ((Jv/2)*T)/M^2 := by ring
      _ ≤ (Jv/2)*T := div_le_self (by positivity) hM₂)
  have hlabel {z : ℝ}
      (hz : |z| ≤ (3*J*T/(2*σ*M^2)+1)*(4*R^2/U)) :
      |z| ≤ 4*(c+1)*T^2 := by
    have htop : 3*J*T/(2*σ*M^2)+1 ≤ (c+1)*T := by nlinarith only [hcurv,hT1]
    apply hz.trans
    calc
      _ ≤ ((c+1)*T)*(4*T) :=
        mul_le_mul htop hK (by positivity) (by positivity)
      _ = _ := by ring
  have hr' : |r| ≤ 4*T := hr.trans hK
  have hs' : |s| ≤ 4*T := hs.trans hK
  have he' := hlabel he
  have hv' := hlabel hv
  have hvV : |s| *V ≤ 2*Jv*T^2 := by
    calc
      _ ≤ (4*T)*((Jv/2)*T) := mul_le_mul hs' hV' hV₀ (by positivity)
      _ = _ := by ring
  have hrV : |r| *V ≤ 2*Jv*T^2 := by
    calc
      _ ≤ (4*T)*((Jv/2)*T) := mul_le_mul hr' hV' hV₀ (by positivity)
      _ = _ := by ring
  have hC : 1 ≤ C := by
    change 1 ≤ 1+4*(c+1+Jv/2)
    exact le_add_of_nonneg_right (by positivity)
  have hpow : 1 ≤ T^3 := one_le_pow₀ hT1
  refine ⟨hT1,hC,?_,?_⟩
  · have hsum : |v|+|s| *V ≤ (4*(c+1)+2*Jv)*T^2 := by linarith only [hv',hvV]
    have hh := mul_le_mul hsum hQT hQ₀ (by positivity : 0 ≤ (4*(c+1)+2*Jv)*T^2)
    change 1+(|v|+|s| *V)*Q ≤ (1+4*(c+1+Jv/2))*T^3
    nlinarith only [hh,hpow]
  · have hsum : |r| *V+|e| ≤ (4*(c+1)+2*Jv)*T^2 := by linarith only [he',hrV]
    have hh := mul_le_mul hsum hQT hQ₀ (by positivity : 0 ≤ (4*(c+1)+2*Jv)*T^2)
    change 1+(|r| *V+|e|)*Q ≤ (1+4*(c+1+Jv/2))*T^3
    nlinarith only [hh,hpow]

                                                               
                                                                       
                                                                 
theorem physicalModelPhase_signed_height_common_coefficient_samples_with_mass
    {Kcoord : ℕ}
    (S : Finset ℕ) (p : ℕ → ℤ × ℤ) (x : ℕ → ℝ)
    {σ δ T M A W step base μ ν r s μ₁ ν₁ r₁ s₁ C J N R d Bcut D l w y₀ ac bc e v P₁ P₂ : ℝ}
    {F : ℝ → ℝ} {k : Fin 17}
    (hS : 32*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hstep : 0 < step) (hμ : 0 < μ) (hμ₁ : μ₁ ≠ 0)
    (hr : r ≠ 0) (hr₁ : r₁ ≠ 0) (hdet : v*r-e*s=1)
    (hden : ∀ z∈Icc l w, d ≤ r*z+s ∧ r*z+s ≤ 2*d)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hC : 0 ≤ C) (hJ : 0 < J) (hN : 0 < N) (hR : 0 < R) (hd : 0 < d)
    (hcoord : |r| * max |l| |w| ≤ (Kcoord:ℝ)*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hBcut : 0 < Bcut) (hBsize : ((2*Kcoord+1:ℕ):ℝ)*C*J ≤ Bcut)
    (hGcut : |minorArcCoordinate μ r s l| ≤ |r| *N^2/(Bcut*R^2))
    (hP₂ : 0 < P₂) (hD₀ : 0 ≤ D) (hD : D ≤ 1/2)
    (hheight : ∀ i∈S, |((p i).1:ℝ)| ≤ P₁ ∧ ((p i).2:ℝ) ≤ P₂)
    (hpt : ∀ i∈S, 0 < (p i).2)
    (hx : ∀ i∈S, x i∈Ioo 0 W)
    (hwindow : ∀ i∈S, x i∈Icc (base+step*(i:ℝ)) (base+step*((i:ℝ)+1))) :
    let U := C*R^4/(N*d^3)
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let f := heathBrownPhysicalPhase F T M A 1
    let y := fun i => ((p i).1:ℝ)/(p i).2
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun z => g z-h z
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    (∀ i∈S, iteratedDeriv 2 f (x i)/2=
      (e*(p i).1+v*(p i).2)/(r*(p i).1+s*(p i).2)) →
    y₀∈finiteBoundaryCell Z l w k →
    (∀ i∈S, y i∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g y₀-iteratedDeriv 2 h y₀| ≤ U →
    (∀ i∈S, |(ac-round (ac-deriv φ (y i)))*y i+
      bc-round (bc-φ (y i)+y i*deriv φ (y i))-φ (y i)| ≤ D/(p i).2) →
    ∃ (a b : ℤ) (j : Fin 8 → ℕ), StrictMono j ∧
      (∀ i, j i∈S ∧ round (ac-deriv φ (y (j i)))=a ∧
        round (bc-φ (y (j i))+y (j i)*deriv φ (y (j i)))=b) ∧
      StrictAnti (fun i => y (j i)) ∧
      (∀ i : Fin 7, step*(S.card:ℝ)/(16*(Blabels:ℝ)) ≤ x (j i.succ)-x (j i.castSucc)) ∧
      (∀ i : Fin 7, modelPhaseThirdLower σ*T/(6*μ*M^3)*(step*(S.card:ℝ)/(16*(Blabels:ℝ))) ≤
        minorArcCoordinate μ r s (y (j i.succ))-
        minorArcCoordinate μ r s (y (j i.castSucc))) ∧
      (∀ i : Fin 7, (S.card:ℝ)/(16*(Blabels:ℝ)) ≤
        ((S.filter (fun n => j i.castSucc<n ∧ n<j i.succ)).card:ℝ)) ∧
      AntitoneOn y (S:Set ℕ) := by
  classical
  intro U Blabels f y g h φ Z hroot hy₀ hy hcurv hres
  have hBpos : (0:ℝ) < Blabels := by dsimp [Blabels]; positivity
  have hselect :
    ∃ (a b : ℤ) (j : Fin 8 → ℕ), StrictMono j ∧
      (∀ i, j i∈S ∧ round (ac-deriv φ (y (j i)))=a ∧
        round (bc-φ (y (j i))+y (j i)*deriv φ (y (j i)))=b) ∧
      (∀ i : Fin 7, (S.card:ℝ)/(16*((6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1):ℕ):ℝ)) ≤
        (j i.succ:ℝ)-(j i.castSucc:ℝ)-1) ∧
      ∀ i : Fin 7, (S.card:ℝ)/(16*((6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1):ℕ):ℝ)) ≤
        ((S.filter (fun n => j i.castSucc<n ∧ n<j i.succ)).card:ℝ) := by
    let color := fun i => (round (ac-deriv φ (y i)),round (bc-φ (y i)+y i*deriv φ (y i)))
    let T := S.image color
    let Blabels : ℕ := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    have hBposN : 0 < Blabels := by dsimp [Blabels]; omega
    have hBpos : (0:ℝ) < Blabels := by exact_mod_cast hBposN
    have hc : T.card ≤ Blabels := quartic_phase_signed_integer_height_source_cutoff_coefficient_count S p
      hμ hμ₁ hr hr₁ hC hJ hN hR hd hden hden₁ hcoord hμupper hBcut hBsize hGcut
      hP₂ hD₀ hD hpt hheight hy₀ hy hcurv hres
    have hsne : S.Nonempty := Finset.card_pos.mp (by omega)
    have htne : T.Nonempty := hsne.image color
    have hbudget : T.card • ((S.card:ℝ)/(Blabels:ℝ)) ≤ (S.card:ℝ) := by
      rw [nsmul_eq_mul]
      have hcR : (T.card:ℝ) ≤ Blabels := by exact_mod_cast hc
      calc
        _ ≤ (Blabels:ℝ)*((S.card:ℝ)/(Blabels:ℝ)) :=
          mul_le_mul_of_nonneg_right hcR (div_nonneg (Nat.cast_nonneg _) hBpos.le)
        _ = _ := by field_simp
    obtain ⟨c,_hc,hcount⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
      (fun i hi => Finset.mem_image_of_mem color hi) htne hbudget
    let V := S.filter (fun i => color i=c)
    have hcount' : (S.card:ℝ) ≤ (Blabels:ℝ)*(V.card:ℝ) := by
      change (S.card:ℝ)/(Blabels:ℝ) ≤ (V.card:ℝ) at hcount
      have hh := (div_le_iff₀ hBpos).mp hcount
      nlinarith only [hh]
    have hVN : S.card ≤ Blabels*V.card := by exact_mod_cast hcount'
    have hV : 32 ≤ V.card := by
      change 32*Blabels ≤ S.card at hS
      by_contra hh
      have hvsmall : V.card ≤ 31 := by omega
      have hmul := Nat.mul_le_mul_left Blabels hvsmall
      nlinarith only [hS,hVN,hmul,hBposN]
    obtain ⟨idx,hidx,hspacing⟩ := exists_eight_block_indices hV
    let emb := V.orderEmbOfFin rfl
    have hgap (a b : Fin V.card) (hab : a ≤ b) :
        (b.val:ℝ)-(a.val:ℝ) ≤ (emb b:ℝ)-(emb a:ℝ) := by
      have hsub : (Finset.Icc a b).image emb ⊆ Finset.Icc (emb a) (emb b) := by
        intro x hx
        obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
        have hz' := Finset.mem_Icc.mp hz
        exact Finset.mem_Icc.mpr ⟨emb.monotone hz'.1,emb.monotone hz'.2⟩
      have hh := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ emb.injective,Fin.card_Icc,Nat.card_Icc] at hh
      have hab' : a.val ≤ b.val := hab
      have he : emb a ≤ emb b := emb.monotone hab
      have hi : b.val+emb a ≤ emb b+a.val := by omega
      have hiR : (b.val:ℝ)+(emb a:ℝ) ≤ (emb b:ℝ)+(a.val:ℝ) := by exact_mod_cast hi
      linarith only [hiR]
    refine ⟨c.1,c.2,fun i => emb (idx i),emb.strictMono.comp hidx,?_,?_,?_⟩
    · intro i
      have hi := V.orderEmbOfFin_mem rfl (idx i)
      have hv := Finset.mem_filter.mp hi
      exact ⟨hv.1,congrArg Prod.fst hv.2,congrArg Prod.snd hv.2⟩
    · intro i
      have hab : idx i.castSucc ≤ idx i.succ := (hidx Fin.castSucc_lt_succ).le
      have hg := hgap _ _ hab
      have hs := hspacing i
      change (S.card:ℝ)/(16*(Blabels:ℝ)) ≤
        (emb (idx i.succ):ℝ)-(emb (idx i.castSucc):ℝ)-1
      calc
        _ ≤ (V.card:ℝ)/16 := by
          apply (div_le_div_iff₀ (by positivity : (0:ℝ)<16*(Blabels:ℝ))
            (by norm_num : (0:ℝ)<16)).mpr
          nlinarith only [hcount']
        _ ≤ (idx i.succ).val-(idx i.castSucc).val-1 := hs
        _ ≤ _ := by linarith only [hg]
    · intro i
      let D := S.filter (fun n => emb (idx i.castSucc)<n ∧ n<emb (idx i.succ))
      have hsub : (Finset.Ioo (idx i.castSucc) (idx i.succ)).image emb ⊆ D := by
        intro n hn
        obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hn
        have hz' := Finset.mem_Ioo.mp hz
        have hm := V.orderEmbOfFin_mem rfl z
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hm).1,
          emb.strictMono hz'.1,emb.strictMono hz'.2⟩
      have hh := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ emb.injective,Fin.card_Ioo] at hh
      have hiN : (idx i.succ).val ≤ D.card+(idx i.castSucc).val+1 := by omega
      have hiR : ((idx i.succ).val:ℝ) ≤ (D.card:ℝ)+((idx i.castSucc).val:ℝ)+1 := by
        exact_mod_cast hiN
      have hs := hspacing i
      change (S.card:ℝ)/(16*(Blabels:ℝ)) ≤ (D.card:ℝ)
      calc
        _ ≤ (V.card:ℝ)/16 := by
          apply (div_le_div_iff₀ (by positivity : (0:ℝ)<16*(Blabels:ℝ))
            (by norm_num : (0:ℝ)<16)).mpr
          nlinarith only [hcount']
        _ ≤ (idx i.succ).val-(idx i.castSucc).val-1 := hs
        _ ≤ _ := by linarith only [hiR]
  obtain ⟨a,b,j,hj,hcoeff,hgap,hmass⟩ := hselect
  have hcount : (0:ℝ) < S.card := by
    exact_mod_cast (show 0 < S.card by omega)
  have hspace (i : Fin 7) : step*(S.card:ℝ)/(16*(Blabels:ℝ)) ≤
      x (j i.succ)-x (j i.castSucc) := by
    have hh := mul_le_mul_of_nonneg_left (hgap i) hstep.le
    change step*((S.card:ℝ)/(16*(Blabels:ℝ))) ≤
      step*((j i.succ:ℝ)-(j i.castSucc:ℝ)-1) at hh
    rw [←mul_div_assoc] at hh
    have hlow := (hwindow (j i.succ) (hcoeff i.succ).1).1
    have hhigh := (hwindow (j i.castSucc) (hcoeff i.castSucc).1).2
    nlinarith only [hh,hlow,hhigh]
  have hcoef : 0 < modelPhaseThirdLower σ*T/(6*μ*M^3) := by
    have hκ := modelPhaseThirdLower_pos hσ
    exact div_pos (mul_pos hκ hT) (mul_pos (mul_pos (by norm_num) hμ) (pow_pos hM 3))
  have hdenj (i : Fin 8) : 0 < r*y (j i)+s :=
    hd.trans_le (hden _ (hy _ (hcoeff i).1).1).1
  have hptj (i : Fin 8) : (0:ℝ) < (p (j i)).2 := by
    exact_mod_cast hpt _ (hcoeff i).1
  have hqj (i : Fin 8) : 0 < r*(p (j i)).1+s*(p (j i)).2 := by
    have he : r*(p (j i)).1+s*(p (j i)).2 =
        (r*y (j i)+s)*(p (j i)).2 := by
      dsimp only [y]
      field_simp [(hptj i).ne']
    rw [he]
    exact mul_pos (hdenj i) (hptj i)
  have hG (i : Fin 7) : modelPhaseThirdLower σ*T/(6*μ*M^3)*(step*(S.card:ℝ)/(16*(Blabels:ℝ))) ≤
      minorArcCoordinate μ r s (y (j i.succ))-
      minorArcCoordinate μ r s (y (j i.castSucc)) := by
    have hxy : x (j i.castSucc) ≤ x (j i.succ) := by
      have hpos : 0 < step*(S.card:ℝ)/(16*(Blabels:ℝ)) :=
        div_pos (mul_pos hstep hcount) (by positivity)
      linarith only [hspace i,hpos]
    have hh := physicalModelPhase_minorArcCoordinate_growth
      ![((p (j i.castSucc)).1:ℝ),((p (j i.succ)).1:ℝ)]
      ![((p (j i.castSucc)).2:ℝ),((p (j i.succ)).2:ℝ)]
      hσ hδ hF hT hM hA hW (hx _ (hcoeff i.castSucc).1) (hx _ (hcoeff i.succ).1)
      hxy hμ hr
      (by
        intro z
        fin_cases z
        · exact (hptj i.castSucc).ne'
        · exact (hptj i.succ).ne')
      (by
        intro z
        fin_cases z
        · exact (hqj i.castSucc).ne'
        · exact (hqj i.succ).ne')
      hdet (hroot _ (hcoeff i.castSucc).1) (hroot _ (hcoeff i.succ).1)
    exact (mul_le_mul_of_nonneg_left (hspace i) hcoef.le).trans hh
  have hptAll j (hj' : j∈S) : (0:ℝ) < (p j).2 := by exact_mod_cast hpt j hj'
  have hdAll j (hj' : j∈S) : 0 < r*y j+s := hd.trans_le (hden _ (hy j hj').1).1
  have hqAll j (hj' : j∈S) : 0 < r*(p j).1+s*(p j).2 := by
    have he : r*(p j).1+s*(p j).2=(r*y j+s)*(p j).2 := by
      dsimp only [y]
      field_simp [(hptAll j hj').ne']
    rw [he]
    exact mul_pos (hdAll j hj') (hptAll j hj')
  have hantiAll : AntitoneOn y (S:Set ℕ) := by
    intro a ha b hb hab
    rcases eq_or_lt_of_le hab with rfl | hab
    · exact le_rfl
    have hstepR : (a:ℝ)+1 ≤ (b:ℝ) := by exact_mod_cast (show a+1 ≤ b by omega)
    have hxorder : x a ≤ x b := by
      have hh := mul_le_mul_of_nonneg_left hstepR hstep.le
      linarith only [hh,(hwindow a ha).2,(hwindow b hb).1]
    have hh := physicalModelPhase_minorArcCoordinate_growth
      ![((p a).1:ℝ),((p b).1:ℝ)] ![((p a).2:ℝ),((p b).2:ℝ)]
      hσ hδ hF hT hM hA hW (hx a ha) (hx b hb) hxorder hμ hr
      (by
        intro i
        fin_cases i
        · exact (hptAll a ha).ne'
        · exact (hptAll b hb).ne')
      (by
        intro i
        fin_cases i
        · exact (hqAll a ha).ne'
        · exact (hqAll b hb).ne')
      hdet (hroot a ha) (hroot b hb)
    have hg : 0 ≤ minorArcCoordinate μ r s (y b)-minorArcCoordinate μ r s (y a) :=
      (mul_nonneg hcoef.le (sub_nonneg.mpr hxorder)).trans hh
    rw [minorArcCoordinate_difference hμ.ne' hr (hdAll a ha).ne' (hdAll b hb).ne'] at hg
    have hn := (le_div_iff₀
      (show 0 < 3*μ*(r*y b+s)*(r*y a+s) by
        exact mul_pos (mul_pos (mul_pos (by norm_num) hμ) (hdAll b hb)) (hdAll a ha))).mp hg
    linarith only [hn]
  refine ⟨a,b,j,hj,hcoeff,?_,hspace,hG,hmass,hantiAll⟩
  apply Fin.strictAnti_iff_succ_lt.mpr
  intro i
  have hg : 0 < minorArcCoordinate μ r s (y (j i.succ))-
      minorArcCoordinate μ r s (y (j i.castSucc)) :=
    lt_of_lt_of_le (mul_pos hcoef (div_pos (mul_pos hstep hcount) (by positivity))) (hG i)
  rw [minorArcCoordinate_difference hμ.ne' hr (hdenj i.castSucc).ne' (hdenj i.succ).ne'] at hg
  have hn := (div_pos_iff_of_pos_right
    (show 0 < 3*μ*(r*y (j i.succ)+s)*(r*y (j i.castSucc)+s) by
      exact mul_pos (mul_pos (mul_pos (by norm_num) hμ) (hdenj i.succ)) (hdenj i.castSucc))).mp hg
  linarith only [hn]


                                                                
                                                                
                                                                 
theorem physicalModelPhase_paired_large_entry_curvature_diameter
    (x y : Fin 2 → ℝ) (a b c d : ℤ)
    {σ δ T M Δ : ℝ} {τ A W : Fin 2 → ℝ} {F : Fin 2 → ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1) (hδ0 : 0 ≤ δ)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hτ : ∀ i, T ≤ τ i ∧ τ i ≤ 2*T) (hM : 0 < M)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hΔ : 0 ≤ Δ) (hdet : a*d-b*c=1) (hc : c ≠ 0)
    (hscale : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤ |(c:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hx : ∀ p, x p ∈ Set.Ioo (1/2:ℝ) (W 0-1/2))
    (hy : ∀ p, y p ∈ Set.Ioo (1/2:ℝ) (W 1-1/2))
    :
    let f := fun i => heathBrownPhysicalPhase (F i) (τ i) M (A i) 1
    let μ := fun i z => iteratedDeriv 3 (f i) (round z)/6
    let t := fun p : Fin 2 => (c:ℝ)*(iteratedDeriv 2 (f 0) (x p)/2)+d
    iteratedDeriv 2 (f 0) (x 0)/2 ≤ iteratedDeriv 2 (f 0) (x 1)/2 →
    (∀ p, ((a:ℝ)*(iteratedDeriv 2 (f 0) (x p)/2)+b)/t p=
      iteratedDeriv 2 (f 1) (y p)/2) →
    (∀ p, (1:ℝ)/2 ≤ t p ∧ t p ≤ 2) →
    (∀ p, |μ 1 (y p)*(t p)^3/μ 0 (x p)-1| ≤ Δ) →
    let κ := modelPhaseThirdLower σ
    let Γ := (σ*(σ+1)+1)/κ
    let η := (modelPhaseJetCoefficient σ 3+δ)/(2*κ*M)
    iteratedDeriv 2 (f 0) (x 1)/2-iteratedDeriv 2 (f 0) (x 0)/2 ≤
      16*(σ*(σ+1)+1)*(Γ^2*Δ+2*Γ*η)/(κ*|(c:ℝ)|) := by
  classical
  let f := fun i => heathBrownPhysicalPhase (F i) (τ i) M (A i) 1
  let μ := fun i z => iteratedDeriv 3 (f i) z/6
  let κ := modelPhaseThirdLower σ
  let Γ := (σ*(σ+1)+1)/κ
  let η := (modelPhaseJetCoefficient σ 3+δ)/(2*κ*M)
  let E := Γ^2*Δ+2*Γ*η
  let U := 2*(σ*(σ+1)+1)*T/(6*M^3)
  let L := κ*T/M^3
  let t := fun p : Fin 2 => (c:ℝ)*(iteratedDeriv 2 (f 0) (x p)/2)+d
  change _ → _ → _ → _ → _
  intro horder hmap ht hthird
  have hτpos i : 0 < τ i := hT.trans_le (hτ i).1
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hΓ : 0 < Γ := by dsimp [Γ]; positivity
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hC₂ : 0 < σ*(σ+1)+1 := by positivity
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hF₂ i := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 3) le_rfl
  have hbuf i (z : ℝ) (hz : z ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) :
      z ∈ Set.Ioo 0 (W i) := ⟨by linarith only [hz.1],by linarith only [hz.2]⟩
  have hrnd i (z : ℝ) (hz : z ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) :
      (round z:ℝ) ∈ Set.Ioo 0 (W i) :=
    (physicalModelPhase_halfCurvature_round_error hσ.le (hF₂ i) (hτpos i) hM
      (hA i) (hW i) hz).1
  have hbounds i (z : ℝ) (hz : z ∈ Set.Ioo 0 (W i)) :
      κ*τ i/(6*M^3) ≤ μ i z ∧ μ i z ≤ (σ*(σ+1)+1)*τ i/(6*M^3) :=
    physicalModelPhase_cubicCoefficient_bounds hσ hδ (hF₂ i) (hτpos i) hM
      (hA i) (hW i) hz
  have hcommon i (z : ℝ) (hz : z ∈ Set.Ioo 0 (W i)) :
      L/6 ≤ μ i z ∧ μ i z ≤ U := by
    constructor
    · calc
        _ = κ*T/(6*M^3) := by dsimp [L]; ring
        _ ≤ κ*τ i/(6*M^3) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hτ i).1 hκ.le) (by positivity)
        _ ≤ μ i z := (hbounds i z hz).1
    · calc
        _ ≤ (σ*(σ+1)+1)*τ i/(6*M^3) := (hbounds i z hz).2
        _ ≤ (σ*(σ+1)+1)*(2*T)/(6*M^3) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hτ i).2 hC₂.le) (by positivity)
        _ = U := by dsimp [U]; ring
  have hμpos i (z : ℝ) (hz : z ∈ Set.Ioo 0 (W i)) : 0 < μ i z :=
    lt_of_lt_of_le (by positivity) (hcommon i z hz).1
  have hratio i (z w : ℝ) (hz : z ∈ Set.Ioo 0 (W i)) (hw : w ∈ Set.Ioo 0 (W i)) :
      μ i z/μ i w ≤ Γ := by
    have hτi := hτpos i
    calc
      _ ≤ ((σ*(σ+1)+1)*τ i/(6*M^3))/(κ*τ i/(6*M^3)) :=
        div_le_div₀ (by positivity) (hbounds i z hz).2 (by positivity) (hbounds i w hw).1
      _ = Γ := by dsimp [Γ]; field_simp
  have hroundvar i (z : ℝ) (hz : z ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) :
      |μ i z/μ i (round z)-1| ≤ η := by
    have hb := physicalModelPhase_cubicCoefficient_relative_variation hσ hδ (hF i)
      (hτpos i).ne' hM (hA i) (hW i) (hrnd i z hz) (hbuf i z hz)
    calc
      _ ≤ (modelPhaseJetCoefficient σ 3+δ)*|z-(round z:ℝ)|/(κ*M) := hb
      _ ≤ (modelPhaseJetCoefficient σ 3+δ)*(1/2)/(κ*M) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (abs_sub_round z) hC₃) (by positivity)
      _ = η := by dsimp [η]; ring
  have hrealThird (p : Fin 2) :
      |μ 1 (y p)*(t p)^3/μ 0 (x p)-1| ≤ E := by
    have hxp := hμpos 0 (x p) (hbuf 0 _ (hx p))
    have hxrp := hμpos 0 (round (x p)) (hrnd 0 _ (hx p))
    have hyp := hμpos 1 (y p) (hbuf 1 _ (hy p))
    have hyrp := hμpos 1 (round (y p)) (hrnd 1 _ (hy p))
    have hrat := ratio_relative_perturbation_of_inverse_bound (div_pos hxp hxrp) hΓ.le
      (hthird p) (hroundvar 1 _ (hy p)) (hroundvar 0 _ (hx p))
      (by rw [abs_of_pos (div_pos hyp hyrp)]; exact hratio 1 _ _ (hbuf 1 _ (hy p)) (hrnd 1 _ (hy p)))
      (by rw [one_div_div]; exact hratio 0 _ _ (hrnd 0 _ (hx p)) (hbuf 0 _ (hx p)))
    change |(μ 1 (round (y p))*(t p)^3/μ 0 (round (x p)))*
      (μ 1 (y p)/μ 1 (round (y p)))/(μ 0 (x p)/μ 0 (round (x p)))-1| ≤ E at hrat
    convert hrat using 1
    congr 1
    field_simp [hxp.ne',hxrp.ne',hyrp.ne']
  have hres (p : Fin 2) : |μ 1 (y p)*(t p)^3-μ 0 (x p)| ≤ U*E := by
    calc
      _ = |μ 0 (x p)*(μ 1 (y p)*(t p)^3/μ 0 (x p)-1)| := by
        congr 1
        field_simp [(hμpos 0 _ (hbuf 0 _ (hx p))).ne']
      _ = μ 0 (x p)*|μ 1 (y p)*(t p)^3/μ 0 (x p)-1| := by
        rw [abs_mul,abs_of_pos (hμpos 0 _ (hbuf 0 _ (hx p)))]
      _ ≤ U*E := mul_le_mul (hcommon 0 _ (hbuf 0 _ (hx p))).2
        (hrealThird p) (abs_nonneg _) hU.le
  have hcf i z (hz : z ∈ Set.Ioo 0 (W i)) : ContDiffAt ℝ 4 (f i) z := by
    have hh := heathBrownPhysicalPhase_contDiffOn (hF i).1 hM (hA i) (hW i) (τ i) 1
    exact ((hh z (Set.Ioo_subset_Icc_self hz)).contDiffAt
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hz) Set.Ioo_subset_Icc_self)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)
  have hthree i z (hz : z ∈ Set.Ioo 0 (W i)) : L ≤ iteratedDeriv 3 (f i) z := by
    have hh := (hcommon i z hz).1
    change L/6 ≤ iteratedDeriv 3 (f i) z/6 at hh
    linarith only [hh]
  have hfour i z (hz : z ∈ Set.Ioo 0 (W i)) :
      |iteratedDeriv 4 (f i) z| ≤ |(c:ℝ)| *L^2/16 := by
    have hτi := hτpos i
    have hyp := heathBrownPhysicalPoint_mem_interior hM (hA i) (hW i) hz
    have he := approximateModelPhase_iteratedDeriv_error (hF i) hyp 3 le_rfl
    have hm := iteratedDeriv_modelPhase_abs_le hσ.le hyp 3
    have htri := abs_add_le
      (iteratedDeriv 4 (F i) ((A i+z)/M)-iteratedDeriv 3 (Expdb.modelPhase σ) ((A i+z)/M))
      (iteratedDeriv 3 (Expdb.modelPhase σ) ((A i+z)/M))
    rw [sub_add_cancel] at htri
    have hu : |iteratedDeriv 4 (F i) ((A i+z)/M)| ≤ modelPhaseJetCoefficient σ 3+δ := by
      linarith only [he,hm,htri]
    have hj : |iteratedDeriv 4 (f i) z| ≤ τ i/M^4*(modelPhaseJetCoefficient σ 3+δ) := by
      dsimp only [f]
      rw [heathBrownPhysicalPhase_iteratedDeriv (hF i).1 hM (hA i) (hW i) hz,one_mul,
        abs_mul,abs_of_pos (by positivity : 0 < τ i/M^4)]
      exact mul_le_mul_of_nonneg_left hu (by positivity)
    apply hj.trans
    calc
      _ ≤ 2*T/M^4*(modelPhaseJetCoefficient σ 3+δ) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hτ i).2 (by positivity)) hC₃
      _ ≤ _ := by
        dsimp only [L]
        apply (mul_le_mul_iff_of_pos_right (show 0 < 16*M^6 by positivity)).mp
        have hh := mul_le_mul_of_nonneg_left hscale hT.le
        convert hh using 1 <;> field_simp
        · ring
        · rfl
  have hb := scaled_paired_C4_nontriangular_resonance_compression
    (f 0) (f 1) a b c d hdet hc hL
    (hcf 0) (hthree 0) (hfour 0) (hcf 1) (hthree 1) (hfour 1)
    (hbuf 0 _ (hx 0)) (hbuf 0 _ (hx 1))
    (hbuf 1 _ (hy 0)) (hbuf 1 _ (hy 1))
    horder (hmap 0) (hmap 1) (ht 0) (ht 1) (hres 0) (hres 1)
  apply hb.trans_eq
  change 48*(U*E)/(|(c:ℝ)| *L)=16*(σ*(σ+1)+1)*E/(κ*|(c:ℝ)|)
  dsimp only [U,L]
  field_simp
  ring


                                                                   
                                                                       
                                                                    
                                                                    
theorem physicalModelPhase_large_entry_quartic_long_block_constraint
    {σ δ T M N R L d K α β : ℝ} (x : Fin 8 → ℝ) (Mat : Fin 4 → ℤ)
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
    (hmono : StrictMono x) (hscale : T*N*R^2=M^3)
    (hMat : Mat 0*Mat 3-Mat 1*Mat 2=1) (hc : Mat 2 ≠ 0)
    (htransport : e 1=(Mat 0:ℝ)*e 0+Mat 1*r 0 ∧
      v 1=(Mat 0:ℝ)*v 0+Mat 1*s 0 ∧
      r 1=(Mat 2:ℝ)*e 0+Mat 3*r 0 ∧
      s 1=(Mat 2:ℝ)*v 0+Mat 3*s 0)
    (hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T) :
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
    κ^2*|(Mat 2:ℝ)| *L^3*N^2 ≤
      128*(σ*(σ+1)+1)*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^4 := by
  intro f n μ ν D g H G hbase hpoint hsquare hgap hres κ Γ C
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
  have hCp : 0 < σ*(σ+1)+1 := by positivity
  have hΓ : 0 < Γ := div_pos hCp hκ
  have hcpos : 0 < |(Mat 2:ℝ)| := abs_pos.mpr (by exact_mod_cast hc)
  have hF₂ i := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl
  have hF₃ i := approximateModelPhase_mono (hF i) (by norm_num : 3 ≤ 4) le_rfl
  have hround := physicalModelPhase_halfCurvature_round_error hσ.le (hF₂ 0)
    hT hM (hA 0) (hW 0) (hx₀ 0)
  have hμbounds := physicalModelPhase_cubicCoefficient_bounds hσ hδ (hF₂ 0)
    hT hM (hA 0) (hW 0) hround.1
  have hμ : 0 < μ 0 := lt_of_lt_of_le (by positivity) hμbounds.1
  have hδ0 : 0 ≤ δ := approximateModelPhase_tolerance_nonneg (hF 0)
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  let z : Fin 2 → ℝ := ![z₁,z₀]
  let xx : Fin 2 → ℝ := fun p => x₁ (z p) 0
  let yy : Fin 2 → ℝ := fun p => x₁ (z p) 1
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
  have ht p : (Mat 2:ℝ)*profile (z p)+Mat 3=D (z p) 1/D (z p) 0 := by
    rw [show profile (z p)=(e 0*z p+v 0)/D (z p) 0 from hpoint _ (hz p) 0]
    apply (eq_div_iff (hdpos _ (hz p) 0).ne').mpr
    rw [add_mul,mul_assoc,div_mul_cancel₀ _ (hdpos _ (hz p) 0).ne']
    dsimp only [D]
    rw [htransport.2.2.1,htransport.2.2.2]
    ring_nf
  have hmap p : ((Mat 0:ℝ)*profile (z p)+Mat 1)/
      ((Mat 2:ℝ)*profile (z p)+Mat 3)=iteratedDeriv 2 (f 1) (yy p)/2 := by
    rw [ht]
    have he : (Mat 0:ℝ)*profile (z p)+Mat 1=
        (e 1*z p+v 1)/D (z p) 0 := by
      rw [show profile (z p)=(e 0*z p+v 0)/D (z p) 0 from hpoint _ (hz p) 0]
      apply (eq_div_iff (hdpos _ (hz p) 0).ne').mpr
      rw [add_mul,mul_assoc,div_mul_cancel₀ _ (hdpos _ (hz p) 0).ne']
      dsimp only [D]
      rw [htransport.1,htransport.2.1]
      ring_nf
    rw [he,div_div_div_cancel_right₀ (hdpos _ (hz p) 0).ne']
    exact (hpoint _ (hz p) 1).symm
  have htband p : (1:ℝ)/2 ≤ (Mat 2:ℝ)*profile (z p)+Mat 3 ∧
      (Mat 2:ℝ)*profile (z p)+Mat 3 ≤ 2 := by
    rw [ht]
    constructor
    · apply (le_div_iff₀ (hdpos _ (hz p) 0)).mpr
      linarith only [hden _ (hz p) 1,hdenUpper _ (hz p) 0]
    · apply (div_le_iff₀ (hdpos _ (hz p) 0)).mpr
      linarith only [hden _ (hz p) 0,hdenUpper _ (hz p) 1]
  have hthird' p : |μnew (z p) 1*((Mat 2:ℝ)*profile (z p)+Mat 3)^3/
      μnew (z p) 0-1| ≤ Δ := by
    rw [ht]
    have he : μnew (z p) 1*(D (z p) 1/D (z p) 0)^3/μnew (z p) 0=
        μnew (z p) 1*(D (z p) 1)^3/(μnew (z p) 0*(D (z p) 0)^3) := by
      rw [div_pow]
      ring_nf
    rw [he]
    apply hthird
    fin_cases p <;> simp [z]
  have hcompression := physicalModelPhase_paired_large_entry_curvature_diameter
    (τ:=fun _ => T) xx yy (Mat 0) (Mat 1) (Mat 2) (Mat 3)
    hσ hδ hδ0 hF₃ hT (fun _ => ⟨le_rfl,by linarith only [hT]⟩)
    hM hA hW hΔ hMat hc hlarge
    (fun p => hx₁ _ (hz p) 0) (fun p => hx₁ _ (hz p) 1)
    horder hmap htband hthird'
  have hNL' : L^2*N^2 ≤ M*R^2 := by
    calc
      _ = (L*N)^2 := by ring_nf
      _ ≤ M*R := hNL
      _ ≤ M*R^2 := mul_le_mul_of_nonneg_left
        (by nlinarith only [mul_le_mul_of_nonneg_left hR hRpos.le] : R ≤ R^2) hM.le
  have hInv : 1/M ≤ R^2/(L^2*N^2) :=
    (div_le_div_iff₀ hM (by positivity)).mpr (by simpa only [one_mul,mul_one,mul_comm] using hNL')
  have hη : 2*Γ*((modelPhaseJetCoefficient σ 3+δ)/(2*κ*M)) ≤
      (Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*(R^2/(L^2*N^2)) := by
    calc
      _ = (Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*(1/M) := by ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left hInv
        (div_nonneg (mul_nonneg hΓ.le hC₃) hκ.le)
  let B := Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ
  have hupper : profile z₀-profile z₁ ≤
      16*(σ*(σ+1)+1)*B*R^2/((κ*|(Mat 2:ℝ)|)*(L^2*N^2)) := by
    apply hcompression.trans
    calc
      _ ≤ 16*(σ*(σ+1)+1)*(Γ^2*Δ+
          (Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*(R^2/(L^2*N^2)))/
          (κ*|(Mat 2:ℝ)|) := by
        apply div_le_div_of_nonneg_right _ (mul_pos hκ hcpos).le
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hη)
          (mul_pos (by norm_num) hCp).le
      _ = _ := by dsimp only [Δ,B]; ring_nf
  have hcross := (div_le_div_iff₀ (by positivity : 0 < 8*R^2)
    (by positivity : 0 < (κ*|(Mat 2:ℝ)|)*(L^2*N^2))).mp (hlo.trans hupper)
  change κ^2*|(Mat 2:ℝ)| *L^3*N^2 ≤ 128*(σ*(σ+1)+1)*B*R^4
  nlinarith only [hcross]


                                                                         
                                                                        
                                                                         
theorem physicalModelPhase_quartic_matrix_long_block_first_condition
    {σ δ T M N R L d K α β : ℝ} (x : Fin 8 → ℝ) (Mat : Fin 4 → ℤ)
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
    (hmono : StrictMono x) (hscale : T*N*R^2=M^3)
    (hMat : Mat 0*Mat 3-Mat 1*Mat 2=1)
    (htransport : e 1=(Mat 0:ℝ)*e 0+Mat 1*r 0 ∧
      v 1=(Mat 0:ℝ)*v 0+Mat 1*s 0 ∧
      r 1=(Mat 2:ℝ)*e 0+Mat 3*r 0 ∧
      s 1=(Mat 2:ℝ)*v 0+Mat 3*s 0)
    :
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
    let Cfirst := 128*(σ*(σ+1)+1)*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    |(Mat 2:ℝ)| ≤ Cfirst*R^4/(L^3*N^2)+Csecond*N*R^2/M := by
  intro f n μ ν D g H G hbase hpoint hsquare hgap hres κ Γ C Cfirst Csecond
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hδ0 : 0 ≤ δ := approximateModelPhase_tolerance_nonneg (hF 0)
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hC₄ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ0
  have hCR : 0 ≤ quarticReciprocalConstant σ δ := by
    dsimp only [quarticReciprocalConstant]
    positivity
  have hΓ : 0 < Γ := by dsimp only [Γ]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hfirst : 0 ≤ Cfirst*R^4/(L^3*N^2) := by
    dsimp only [Cfirst]
    positivity
  have hsecond : 0 ≤ Csecond*N*R^2/M := by
    dsimp only [Csecond]
    positivity
  by_cases hc : Mat 2=0
  · rw [hc,Int.cast_zero,abs_zero]
    exact add_nonneg hfirst hsecond
  by_cases hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T
  · have hh := physicalModelPhase_large_entry_quartic_long_block_constraint
      x Mat hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀ hx₁ hr hdet
      hden hdenUpper hmono hscale hMat hc htransport hlarge
      hbase hpoint hsquare hgap hres
    have hb : |(Mat 2:ℝ)| ≤ Cfirst*R^4/(L^3*N^2) := by
      apply (le_div_iff₀ (by positivity : 0 < L^3*N^2)).mpr
      have hh' : |(Mat 2:ℝ)| *(L^3*N^2) ≤
          (128*(σ*(σ+1)+1)*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^4)/κ^2 := by
        apply (le_div_iff₀ (pow_pos hκ 2)).mpr
        calc
          _ = κ^2*|(Mat 2:ℝ)| *L^3*N^2 := by ring
          _ ≤ _ := hh
      exact hh'.trans_eq (by dsimp only [Cfirst]; ring)
    exact hb.trans (le_add_of_nonneg_right hsecond)
  · have hs : |(Mat 2:ℝ)| ≤
        (32*(modelPhaseJetCoefficient σ 3+δ)*M^2)/(κ^2*T) := by
      apply (le_div_iff₀ (mul_pos (pow_pos hκ 2) hT)).mpr
      simpa only [mul_assoc] using (lt_of_not_ge hlarge).le
    have he : (32*(modelPhaseJetCoefficient σ 3+δ)*M^2)/(κ^2*T)=
        Csecond*N*R^2/M := by
      have hTval : T=M^3/(N*R^2) :=
        (eq_div_iff (by positivity)).mpr (by nlinarith only [hscale])
      rw [hTval]
      dsimp only [Csecond]
      field_simp
    exact (hs.trans_eq he).trans (le_add_of_nonneg_left hfirst)


                                                                      
                                                                      
                                                                      
                                                                          
private theorem physicalModelPhase_signed_height_square_span_quartic_witnesses
    {Kcoord : ℕ}
    (S : Finset ℕ) (p : ℕ → ℤ × ℤ) (x : ℕ → Fin 2 → ℝ)
    {σ δ T M N R base d Cres Q D nSpan Ccurv Bcut l w y₀ ac bc P₁ P₂ : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W xref e r v s H : Fin 2 → ℝ} {k : Fin 17}
    (hS : 32*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hd : 0 < d) (hCres : 0 ≤ Cres)
    (hD₀ : 0 ≤ D) (hD : D ≤ 1/2) (hDupper : D ≤ Cres*Q/N)
    (hscale : T*N*R^2=M^3)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hxref : ∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2))
    (hheight : ∀ j∈S, |((p j).1:ℝ)| ≤ P₁ ∧ ((p j).2:ℝ) ≤ P₂)
    (hpt : ∀ j∈S, 0 < (p j).2)
    (hQband : ∀ j∈S, Q ≤ 2*(r 0*(p j).1+s 0*(p j).2))
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hdisplacement : ∀ j∈S, ∀ i, |x j i-xref i| ≤ H i)
    (hspan : ∀ i, 2*H i+1 ≤ nSpan)
    (hnsquare : nSpan^2 ≤ M*R)
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hden : ∀ z∈Icc l w, ∀ i, d ≤ r i*z+s i ∧ r i*z+s i ≤ 2*d)
    (hcoord : |r 0| * max |l| |w| ≤ (Kcoord:ℝ)*d) (hP₂ : 0 < P₂)
    (hCcurv : 0 ≤ Ccurv) (hBcut : 0 < Bcut)
    (hBsize : ((2*Kcoord+1:ℕ):ℝ)*Ccurv*(σ*(σ+1)+1) ≤ Bcut)
    :
    let U := Ccurv*R^4/(N*d^3)
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let μ := fun i => iteratedDeriv 3 (f i) (round (xref i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (round (xref i))/24
    let y := fun j => ((p j).1:ℝ)/(p j).2
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let h := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let φ := fun z => g z-h z
    let G := minorArcCoordinate (μ 0) (r 0) (s 0)
    let Z := quarticCurvatureBoundaryRoots (μ 0) (ν 0) (r 0) (s 0)
      (μ 1) (ν 1) (r 1) (s 1) U
    let κ := modelPhaseThirdLower σ
    let K := 4*Cres/κ
    let L := κ/(16*(Blabels:ℝ)*(σ*(σ+1)+1))*(S.card:ℝ)
    |G l| ≤ |r 0| *N^2/(Bcut*R^2) →
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=
      (e i*(p j).1+v i*(p j).2)/(r i*(p j).1+s i*(p j).2)) →
    y₀∈finiteBoundaryCell Z l w k →
    (∀ j∈S, y j∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g y₀-iteratedDeriv 2 h y₀| ≤ U →
    (∀ j∈S, |(ac-round (ac-deriv φ (y j)))*y j+
      (bc-round (bc-φ (y j)+y j*deriv φ (y j)))-g (y j)+h (y j)| ≤
      D/(p j).2) →
    ∃ j : Fin 8 → ℕ, ∃ z : Fin 8 → ℝ, ∃ curve : ℝ → Fin 2 → ℝ, ∃ alpha beta : ℝ,
      (∀ a, j a∈S ∧ z a=y (j a) ∧ ∀ i,
        iteratedDeriv 2 (f i) (x (j a) i)/2=(e i*z a+v i)/(r i*z a+s i)) ∧ StrictMono z ∧
      0 < L ∧ (L*N)^2 ≤ M*R ∧ 0 ≤ K ∧
      (∀ t∈Icc (z 0) (z 7), t∈Icc l w ∧ ∀ i,
        curve t i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        d ≤ r i*t+s i ∧ r i*t+s i ≤ 2*d ∧
        iteratedDeriv 2 (f i) (curve t i)/2=(e i*t+v i)/(r i*t+s i) ∧
        |(round (curve t i):ℝ)-(round (xref i):ℝ)|^2 ≤ M*R) ∧
      (∀ i : Fin 7, L*N ≤ |G (z i.succ)-G (z i.castSucc)|) ∧
      (∀ i : Fin 8, |alpha*z i+beta-g (z i)+h (z i)| ≤ K*R^2/|r 0*G (z i)|) := by
  classical
  intro U Blabels f μ ν y g h φ G Z κ K L hGcut hpoint hy₀ hy hcurv hres
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hBpos : (0:ℝ) < Blabels := by dsimp [Blabels]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcount : (0:ℝ) < S.card := by exact_mod_cast (show 0 < S.card by omega)
  have hCpos : 0 < σ*(σ+1)+1 := by positivity
  have hL : 0 < L := mul_pos (div_pos hκ (mul_pos (by positivity) hCpos)) hcount
  have hF₂ i := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl
  have hround i := physicalModelPhase_halfCurvature_round_error hσ.le (hF₂ i)
    hT hM (hA i) (hW i) (hxref i)
  have hμbounds i := physicalModelPhase_cubicCoefficient_bounds hσ hδ (hF₂ i)
    hT hM (hA i) (hW i) (hround i).1
  have hμpos i : 0 < μ i := lt_of_lt_of_le (by positivity) (hμbounds i).1
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hμupper : μ 0 ≤ (σ*(σ+1)+1)/(6*N*R^2) := by
    have hb := (hμbounds 0).2
    have hTeq : T=M^3/(N*R^2) :=
      (eq_div_iff (by positivity)).mpr (by nlinarith only [hscale])
    have he : (σ*(σ+1)+1)*T/(6*M^3)=(σ*(σ+1)+1)/(6*N*R^2) := by
      rw [hTeq]
      field_simp
    exact hb.trans_eq he
  have hdx (j) (hj : j∈S) : x j 0∈Ioo 0 (W 0) :=
    ⟨by linarith only [(hx j hj 0).1],by linarith only [(hx j hj 0).2]⟩
  obtain ⟨a,b,j,_hj,hcoeff,hanti,hphys,hG,_hmass,_hantiAll⟩ := physicalModelPhase_signed_height_common_coefficient_samples_with_mass
    (ac:=ac) (bc:=bc) (C:=Ccurv) (J:=σ*(σ+1)+1) (N:=N) (R:=R) (d:=d)
    S p (fun n => x n 0) hS hσ hδ (hF₂ 0) hT hM (hA 0) (hW 0) hN
    (hμpos 0) (hμpos 1).ne' (hr 0) (hr 1) (hdet 0)
    (fun z hz => hden z hz 0) (fun z hz => (hd.trans_le (hden z hz 1).1).ne')
    hCcurv hCpos hN hRpos hd hcoord hμupper hBcut hBsize hGcut
    hP₂ hD₀ hD hheight hpt hdx hwindow (fun n hn => hpoint n hn 0) hy₀ hy hcurv
    (fun n hn => by
      convert hres n hn using 1
      dsimp only [φ]
      congr 1
      ring)
  have hphaseLower : κ/(2*N) ≤ 3*μ 0*R^2 := by
    have hh := mul_le_mul_of_nonneg_right (hμbounds 0).1 (show 0 ≤ 3*R^2 by positivity)
    have hTeq : T=M^3/(N*R^2) :=
      (eq_div_iff (by positivity)).mpr (by nlinarith only [hscale])
    have he : (κ*T/(6*M^3))*(3*R^2)=κ/(2*N) := by
      rw [hTeq]
      field_simp
      norm_num
    rw [he] at hh
    change κ/(2*N) ≤ μ 0*(3*R^2) at hh
    nlinarith only [hh]
  have hresnorm (n) (hn : n∈S) :
      |(ac-round (ac-deriv φ (y n)))*y n+
        (bc-round (bc-φ (y n)+y n*deriv φ (y n)))-g (y n)+h (y n)| ≤
        K*R^2/|r 0*G (y n)| := by
    exact (hres n hn).trans (quartic_integer_seed_residual_source_normalization (p n)
      (hμpos 0) (hr 0) hκ hN hCres (hpt n hn)
      (hd.trans_le (hden _ (hy n hn).1 0).1) (hQband n hn) hDupper hphaseLower)
  have hH i : 0 ≤ H i := (abs_nonneg _).trans (hdisplacement _ (hcoeff 0).1 i)
  have hsquare i : (H i+1)^2 ≤ M*R := by
    apply (pow_le_pow_left₀ (add_nonneg (hH i) zero_le_one)
      (show H i+1 ≤ nSpan by linarith only [hH i,hspan i]) 2).trans hnsquare
  have hκle : κ ≤ σ*(σ+1)+1 := by
    have hh := approximateModelPhase_thirdDeriv_bounds hσ hδ (hF₂ 0)
      (by norm_num : (3/2:ℝ)∈Ioo 1 2)
    exact hh.1.trans hh.2
  have hLspan : L*N ≤ nSpan := by
    have hrati : κ/(σ*(σ+1)+1) ≤ 1 := (div_le_one hCpos).mpr hκle
    have hsmall := mul_le_mul_of_nonneg_right hrati
      (div_pos (mul_pos hN hcount) (by positivity : (0:ℝ)<16*(Blabels:ℝ))).le
    have he : L*N=κ/(σ*(σ+1)+1)*(N*(S.card:ℝ)/(16*(Blabels:ℝ))) := by
      dsimp only [L]
      field_simp
    rw [← he,one_mul] at hsmall
    have hg := hphys (0:Fin 7)
    have hdiff := le_abs_self (x (j (1:Fin 8)) 0-x (j (0:Fin 8)) 0)
    have htri := abs_sub_le (x (j (1:Fin 8)) 0) (xref 0) (x (j (0:Fin 8)) 0)
    rw [abs_sub_comm (xref 0)] at htri
    have hleft := hdisplacement _ (hcoeff (0:Fin 8)).1 0
    have hright := hdisplacement _ (hcoeff (1:Fin 8)).1 0
    change N*(S.card:ℝ)/(16*(Blabels:ℝ)) ≤ x (j 1) 0-x (j 0) 0 at hg
    linarith only [hsmall,hg,hdiff,htri,hleft,hright,hspan 0]
  have hNL : (L*N)^2 ≤ M*R :=
    (pow_le_pow_left₀ (mul_pos hL hN).le hLspan 2).trans hnsquare
  let z : Fin 8 → ℝ := fun i => y (j i.rev)
  have hmono : StrictMono z := hanti.comp Fin.rev_strictAnti
  have hz (i : Fin 8) : z i∈Icc l w := (hy _ (hcoeff i.rev).1).1
  have hsub : Icc (z 0) (z 7) ⊆ Icc l w :=
    fun q hq => ⟨(hz 0).1.trans hq.1,hq.2.trans (hz 7).2⟩
  have hcoef : κ/(σ*(σ+1)+1) ≤ κ*T/(6*μ 0*M^3) := by
    have hb : 6*μ 0*M^3 ≤ (σ*(σ+1)+1)*T := by
      have hh := (le_div_iff₀ (show 0 < 6*M^3 by positivity)).mp (hμbounds 0).2
      change μ 0*(6*M^3) ≤ (σ*(σ+1)+1)*T at hh
      nlinarith only [hh]
    apply (div_le_div_iff₀ hCpos
      (mul_pos (mul_pos (by norm_num) (hμpos 0)) (pow_pos hM 3))).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hb hκ.le]
  have hgap (i : Fin 7) : L*N ≤ |G (z i.succ)-G (z i.castSucc)| := by
    have hh := mul_le_mul_of_nonneg_right hcoef
      (div_pos (mul_pos hN hcount) (by positivity : (0:ℝ) < 16*(Blabels:ℝ))).le
    have he : L*N=κ/(σ*(σ+1)+1)*(N*(S.card:ℝ)/(16*(Blabels:ℝ))) := by
      dsimp only [L]
      field_simp
    rw [he]
    dsimp only [z]
    rw [Fin.rev_succ,Fin.rev_castSucc,abs_sub_comm]
    exact (hh.trans (hG i.rev)).trans (le_abs_self _)
  have hroot (i : Fin 8) (a : Fin 2) :
      iteratedDeriv 2 (f a) (x (j i.rev) a)/2=(e a*z i+v a)/(r a*z i+s a) := by
    rw [hpoint _ (hcoeff i.rev).1 a]
    have ht : ((p (j i.rev)).2:ℝ) ≠ 0 := by
      exact_mod_cast (hpt _ (hcoeff i.rev).1).ne'
    dsimp only [z,y]
    have hn : e a*(((p (j i.rev)).1:ℝ)/(p (j i.rev)).2)+v a=
      (e a*(p (j i.rev)).1+v a*(p (j i.rev)).2)/(p (j i.rev)).2 := by field_simp
    have hd' : r a*(((p (j i.rev)).1:ℝ)/(p (j i.rev)).2)+s a=
      (r a*(p (j i.rev)).1+s a*(p (j i.rev)).2)/(p (j i.rev)).2 := by field_simp
    rw [hn,hd',div_div_div_cancel_right₀ ht]
  have hex (i : Fin 2) := physicalModelPhase_interval_root_family
    (l:=z 0) (w:=z 7) (x₀:=xref i) hσ.le (hF₂ i) hT hM (hA i) (hW i)
    (hx _ (hcoeff (0:Fin 8).rev).1 i) (hx _ (hcoeff (7:Fin 8).rev).1 i)
    (hd.trans_le (hden _ (hz 0) i).1) (hd.trans_le (hden _ (hz 7) i).1)
    (hdisplacement _ (hcoeff (0:Fin 8).rev).1 i)
    (hdisplacement _ (hcoeff (7:Fin 8).rev).1 i)
    (by rw [← hroot 0 i]; exact Set.left_mem_uIcc)
    (by rw [← hroot 7 i]; exact Set.right_mem_uIcc)
  choose ρ hρ _hρdiam using hex
  refine ⟨(fun a => j a.rev),z,(fun q i => ρ i q),ac-a,bc-b,
    (fun a => ⟨(hcoeff a.rev).1,rfl,hroot a⟩),hmono,hL,hNL,hK,?_,hgap,?_⟩
  · intro t ht
    refine ⟨hsub ht,fun i => ⟨(hρ i t ht).2.1,
      (hden t (hsub ht) i).1,(hden t (hsub ht) i).2,(hρ i t ht).2.2.1,?_⟩⟩
    exact (pow_le_pow_left₀ (abs_nonneg _) (hρ i t ht).2.2.2.2 2).trans (hsquare i)
  · intro i
    have hh := hresnorm _ (hcoeff i.rev).1
    rw [(hcoeff i.rev).2.1,(hcoeff i.rev).2.2] at hh
    exact hh


theorem source_selected_reference_square_span_budget
    (U : ℕ) {M N R Q B : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hRQ : R ≤ Q) (hB : 0 < B)
    (hU : (U:ℝ) ≤ (N/Q)^((2:ℝ)/3)/B)
    (hscale : N^10 ≤ M^3*R^7) :
    (B*(U:ℝ)*N)^2 ≤ M*R := by
  have hQ : 0 < Q := hR.trans_le hRQ
  have hpow : ((N/Q)^((2:ℝ)/3))^3=(N/Q)^2 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (div_pos hN hQ).le]
    norm_num
  have hcube : B^3*(U:ℝ)^3*Q^2 ≤ N^2 := by
    have hh := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg U) hU 3)
      (show 0 ≤ B^3*Q^2 by positivity)
    have he : (B^3*Q^2)*((N/Q)^((2:ℝ)/3)/B)^3=N^2 := by
      rw [div_pow,hpow,div_pow]
      field_simp
    rw [he] at hh
    nlinarith only [hh]
  apply (pow_le_pow_iff_left₀ (sq_nonneg (B*(U:ℝ)*N))
    (mul_pos hM hR).le (by decide : (3:ℕ) ≠ 0)).mp
  apply (mul_le_mul_iff_of_pos_right (pow_pos hQ 4)).mp
  calc
    _ = (B^3*(U:ℝ)^3*Q^2)^2*N^6 := by ring
    _ ≤ (N^2)^2*N^6 := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) hcube 2) (pow_nonneg hN.le 6)
    _ = N^10 := by ring
    _ ≤ M^3*R^7 := hscale
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hR.le hRQ 4) (show 0 ≤ M^3*R^3 by positivity)
      convert hh using 1 <;> ring


                                                                           
theorem physicalModelPhase_reference_gap_minorArc_cutoff
    {σ δ T M A W xref N R U B Bcut a b e r v s l : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hxref : xref ∈ Ioo (1/2:ℝ) (W-1/2))
    (hN : 0 < N) (hR : 0 < R) (hU : 0 ≤ U)
    (hB : 0 < B) (hBcut : 0 < Bcut)
    (hscale : T*N*R^2=M^3)
    (hmargin : 7*Bcut ≤ modelPhaseThirdLower σ*B)
    (hr : r ≠ 0) (hchart : r*l+s ≠ 0) (hdet : v*r-e*s=1)
    (hgap : b-a ≤ 7*U/(2*R^2))
    (hden : R^2 ≤ r^2*U) (hwrap : B^2*U^3*R^2 ≤ N^2)
    (hpoint : (e*l+v)/(r*l+s) ∈ Icc a b) :
    let f := heathBrownPhysicalPhase F T M A 1
    iteratedDeriv 2 f xref/2=e/r →
    (iteratedDeriv 2 f xref/2=a ∨ iteratedDeriv 2 f xref/2=b) →
    |minorArcCoordinate (iteratedDeriv 3 f (round xref)/6) r s l| ≤
      |r| *N^2/(Bcut*R^2) := by
  intro f hbase hendpoint
  let κ := modelPhaseThirdLower σ
  let μ := iteratedDeriv 3 f (round xref)/6
  let G := minorArcCoordinate μ r s l
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hround := (physicalModelPhase_halfCurvature_round_error hσ.le
    hF hT hM hA hW hxref).1
  have hsource := physicalModelPhase_cubicCoefficient_source_scale
    hσ hδ hF hT hM hA hW hround hN hR hscale
  have hμ : 0 < μ := hsource.1
  have hlower : κ ≤ 6*μ*N*R^2 := by
    have hh := mul_le_mul_of_nonneg_left hsource.2.1 hκ.le
    change κ*1 ≤ κ*((6/κ)*μ*N*R^2) at hh
    have he : κ*((6/κ)*μ*N*R^2)=6*μ*N*R^2 := by field_simp
    simpa only [he,mul_one] using hh
  have hid : (e*l+v)/(r*l+s)-e/r=3*μ*G := by
    simpa only [mul_one,div_one] using
      (farey_curvature_coordinate_identity (μ:=μ) (u:=l) (t:=1)
        hμ.ne' hr (by norm_num) (by simpa only [mul_one] using hchart) hdet)
  have hdistance : |(e*l+v)/(r*l+s)-e/r| ≤ b-a := by
    rw [hbase] at hendpoint
    rcases hendpoint with ha | hb
    · rw [ha,abs_of_nonneg (sub_nonneg.mpr hpoint.1)]
      linarith only [hpoint.2]
    · rw [hb,abs_of_nonpos (sub_nonpos.mpr hpoint.2)]
      linarith only [hpoint.1]
  have hupper : (3*μ*|G|)*(2*R^2) ≤ 7*U := by
    have hh := hdistance.trans hgap
    rw [hid,abs_mul,abs_of_pos (mul_pos (by norm_num) hμ)] at hh
    exact (le_div_iff₀ (by positivity)).mp hh
  have hwidth : |G| ≤ 7*U*N/κ := by
    apply (le_div_iff₀ hκ).mpr
    have hlo := mul_le_mul_of_nonneg_right hlower (abs_nonneg G)
    have hhi := mul_le_mul_of_nonneg_right hupper hN.le
    nlinarith only [hlo,hhi]
  have hsq : (B*U*R^2)^2 ≤ (|r| *N)^2 := by
    calc
      _ = (B^2*U^2*R^2)*R^2 := by ring
      _ ≤ (B^2*U^2*R^2)*(r^2*U) :=
        mul_le_mul_of_nonneg_left hden (by positivity)
      _ = r^2*(B^2*U^3*R^2) := by ring
      _ ≤ r^2*N^2 := mul_le_mul_of_nonneg_left hwrap (sq_nonneg r)
      _ = _ := by rw [mul_pow,sq_abs]
  have hnowrap : B*U*R^2 ≤ |r| *N :=
    (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
  have hmargin' : 7/κ ≤ B/Bcut := by
    apply (div_le_div_iff₀ hκ hBcut).mpr
    nlinarith only [hmargin]
  have hwide : |G| ≤ (B/Bcut)*U*N := by
    calc
      _ ≤ 7*U*N/κ := hwidth
      _ = (7/κ)*U*N := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hmargin' hU) hN.le
  change |G| ≤ |r| *N^2/(Bcut*R^2)
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    _ ≤ ((B/Bcut)*U*N)*(Bcut*R^2) :=
      mul_le_mul_of_nonneg_right hwide (by positivity)
    _ = (B*U*R^2)*N := by field_simp
    _ ≤ (|r| *N)*N := mul_le_mul_of_nonneg_right hnowrap hN.le
    _ = _ := by ring


                                                                  
                                                                  
                                                                  
                                                                
theorem physicalModelPhase_actual_matrix_gap_displacement
    (Q : ℕ) (rat₀ rat₁ : Fin 2 → ℚ) (Mat : Fin 4 → ℤ)
    {σ δ T M N R U a b : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hU : 0 ≤ U)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo 0 (W i)) (hx₁ : ∀ i, x₁ i∈Ioo 0 (W i))
    (hscale : T*N*R^2=M^3)
    (hden₀ : ∀ i, (rat₀ i).den ≤ Q ∧ Q ≤ 2*(rat₀ i).den)
    (hden₁ : ∀ i, (rat₁ i).den ≤ Q ∧ Q ≤ 2*(rat₁ i).den)
    (hdet : Mat 0*Mat 3-Mat 1*Mat 2=1)
    (ht₀ : (Mat 2:ℝ)*(rat₀ 0:ℝ)+Mat 3=((rat₀ 1).den:ℝ)/(rat₀ 0).den)
    (ht₁ : (Mat 2:ℝ)*(rat₁ 0:ℝ)+Mat 3=((rat₁ 1).den:ℝ)/(rat₁ 0).den)
    (hmap₀ : ((Mat 0:ℝ)*(rat₀ 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat₀ 0:ℝ)+Mat 3)=(rat₀ 1:ℝ))
    (hmap₁ : ((Mat 0:ℝ)*(rat₁ 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat₁ 0:ℝ)+Mat 3)=(rat₁ 1:ℝ))
    (hgap : b-a ≤ 7*U/(2*R^2))
    (hgap₀ : (rat₀ 0:ℝ)∈Icc a b) (hgap₁ : (rat₁ 0:ℝ)∈Icc a b) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat₀ i:ℝ)) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=(rat₁ i:ℝ)) →
    ∀ i, |x₁ i-x₀ i| ≤ 28*U*N/modelPhaseThirdLower σ := by
  intro f hlevel₀ hlevel₁
  let κ := modelPhaseThirdLower σ
  let D := 7*U/(2*R^2)
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have htlo (rat : Fin 2 → ℚ)
      (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) :
      (1/2:ℝ) ≤ ((rat 1).den:ℝ)/(rat 0).den := by
    apply (le_div_iff₀ (by exact_mod_cast (rat 0).pos)).mpr
    have hh : ((rat 0).den:ℝ) ≤ 2*(rat 1).den := by
      exact_mod_cast (hden 0).1.trans (hden 1).2
    linarith only [hh]
  have hlow₀ : (1/2:ℝ) ≤ (Mat 2:ℝ)*(rat₀ 0:ℝ)+Mat 3 := by
    rw [ht₀]; exact htlo rat₀ hden₀
  have hlow₁ : (1/2:ℝ) ≤ (Mat 2:ℝ)*(rat₁ 0:ℝ)+Mat 3 := by
    rw [ht₁]; exact htlo rat₁ hden₁
  have hpos₀ : 0 < (Mat 2:ℝ)*(rat₀ 0:ℝ)+Mat 3 := by linarith only [hlow₀]
  have hpos₁ : 0 < (Mat 2:ℝ)*(rat₁ 0:ℝ)+Mat 3 := by linarith only [hlow₁]
  have hcurv₀ : |(rat₁ 0:ℝ)-(rat₀ 0:ℝ)| ≤ D := by
    apply le_trans _ hgap
    apply abs_le.mpr
    constructor <;> linarith only [hgap₀.1,hgap₀.2,hgap₁.1,hgap₁.2]
  have hcurv₁ : |(rat₁ 1:ℝ)-(rat₀ 1:ℝ)| ≤ 4*D := by
    have hdetR : (Mat 0:ℝ)*Mat 3-(Mat 1:ℝ)*Mat 2=1 := by exact_mod_cast hdet
    have hid : (rat₁ 1:ℝ)-(rat₀ 1:ℝ)=
        ((rat₁ 0:ℝ)-(rat₀ 0:ℝ))/
        (((Mat 2:ℝ)*(rat₁ 0:ℝ)+Mat 3)*((Mat 2:ℝ)*(rat₀ 0:ℝ)+Mat 3)) := by
      rw [←hmap₁,←hmap₀,div_sub_div _ _ hpos₁.ne' hpos₀.ne']
      congr 1
      linear_combination ((rat₁ 0:ℝ)-(rat₀ 0:ℝ))*hdetR
    rw [hid,abs_div,abs_of_pos (mul_pos hpos₁ hpos₀)]
    apply (div_le_iff₀ (mul_pos hpos₁ hpos₀)).mpr
    have hprod := mul_le_mul hlow₁ hlow₀ (by norm_num : (0:ℝ) ≤ 1/2) hpos₁.le
    have hh := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 4*D by positivity)
    nlinarith only [hcurv₀,hh]
  have hcoef : κ*T/(2*M^3)=κ/(2*N*R^2) := by
    rw [←hscale]
    field_simp
  intro i
  have hgrowth : κ/(2*N*R^2)*|x₁ i-x₀ i| ≤ |(rat₁ i:ℝ)-(rat₀ i:ℝ)| := by
    rcases le_total (x₀ i) (x₁ i) with hle | hle
    · have hh := physicalModelPhase_halfCurvature_growth hσ hδ (hF i)
        hT hM (hA i) (hW i) (hx₀ i) (hx₁ i) hle
      change κ*T/(2*M^3)*(x₁ i-x₀ i) ≤ _ at hh
      rw [hcoef,hlevel₀ i,hlevel₁ i] at hh
      rw [abs_of_nonneg (sub_nonneg.mpr hle)]
      exact hh.trans (le_abs_self _)
    · have hh := physicalModelPhase_halfCurvature_growth hσ hδ (hF i)
        hT hM (hA i) (hW i) (hx₁ i) (hx₀ i) hle
      change κ*T/(2*M^3)*(x₀ i-x₁ i) ≤ _ at hh
      rw [hcoef,hlevel₀ i,hlevel₁ i] at hh
      rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hle),abs_sub_comm (rat₁ i:ℝ)]
      exact hh.trans (le_abs_self _)
  have hcurv : |(rat₁ i:ℝ)-(rat₀ i:ℝ)| ≤ 4*D := by
    fin_cases i
    · exact hcurv₀.trans (by linarith only [hD])
    · exact hcurv₁
  have hh := mul_le_mul_of_nonneg_left (hgrowth.trans hcurv)
    (show 0 ≤ 2*N*R^2 by positivity)
  have he : (2*N*R^2)*(κ/(2*N*R^2)*|x₁ i-x₀ i|)=κ*|x₁ i-x₀ i| := by field_simp
  rw [he] at hh
  apply (le_div_iff₀ hκ).mpr
  have he' : (2*N*R^2)*(4*D)=28*U*N := by dsimp only [D]; field_simp; ring
  rw [he'] at hh
  nlinarith only [hh]


                                                                   
                                                                        
                                                                       
                                                                        
theorem negative_fareySector_integer_labels_enlarged_rectangle_all_slopes
    {N : ℕ} {l w B α β δ : ℝ}
    (hw : w < 0) (hlw : l ≤ w) (hB : 1 ≤ B) (hδ : 0 ≤ δ) :
    let P := HuxleyLinearForm.fareySector N (-w) (-l)
    let S := P.image (fun p : ℤ × ℤ => (-p.1,p.2))
    max ((w-l)*(N:ℝ)^2/B) 2 ≤ (S.card:ℝ) →
    3840*B*δ*((-l)*(N:ℝ))*(N:ℝ) < (S.card:ℝ) →
    (∀ p∈S, ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ) →
    ∀ p : ℤ × ℤ, 0 ≤ -(p.1:ℝ) → -(p.1:ℝ) ≤ 12*((-l)*(N:ℝ)) →
      0 ≤ (p.2:ℝ) → (p.2:ℝ) ≤ 12*(N:ℝ) → ∀ b : ℤ,
      |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ →
      b=p.1*round α+p.2*round β := by
  classical
  intro P S hR hlarge hnear
  have hinj : Function.Injective (fun p : ℤ × ℤ => (-p.1,p.2)) := by
    intro p q hpq
    have h₁ := congrArg Prod.fst hpq
    have h₂ := congrArg Prod.snd hpq
    exact Prod.ext (neg_injective h₁) h₂
  have hcard : S.card=P.card := Finset.card_image_of_injective P hinj
  rw [hcard] at hR hlarge
  have hw' : 0 < -w := neg_pos.mpr hw
  have hl' : 0 ≤ -l := by linarith only [hlw,hw]
  have hR' : max (((-l)-(-w))*(N:ℝ)^2/B) 2 ≤ (P.card:ℝ) := by
    have heq : (-l)-(-w)=w-l := by ring
    rw [heq]
    exact hR
  have hnear' : ∀ p∈P, ∃ b : ℤ, |(p.1:ℝ)*(-α)+(p.2:ℝ)*β-b| ≤ δ := by
    intro p hp
    obtain ⟨b,hb⟩ := hnear (-p.1,p.2) (Finset.mem_image_of_mem _ hp)
    refine ⟨b,?_⟩
    simpa only [Int.cast_neg,neg_mul,mul_neg] using hb
  obtain ⟨ha,_hb⟩ :=
    (fareySector_bounded_density_dichotomy_all_slopes
      hw' hB hδ hR' hnear').resolve_left (not_le.mpr hlarge)
  have hPtwo : (2:ℝ) ≤ P.card := (le_max_right _ _).trans hR'
  have hPpos : (0:ℝ) < P.card := lt_of_lt_of_le (by norm_num) hPtwo
  obtain ⟨p₀,hp₀⟩ := Finset.card_pos.mp
    (show 0 < P.card by exact_mod_cast hPpos)
  have hpdata := (HuxleyLinearForm.mem_fareySector_iff hw' hl').mp hp₀
  have ht : (0:ℝ) < p₀.2 := by exact_mod_cast (show 0 < p₀.2 by omega)
  have htN : (p₀.2:ℝ) ≤ N := by exact_mod_cast hpdata.2.1
  have hnum : (0:ℝ) < p₀.1 :=
    (mul_pos hw' ht).trans_le hpdata.2.2.2.1
  have hnumOne : (1:ℝ) ≤ p₀.1 := by
    have hh : (0:ℤ) < p₀.1 := by exact_mod_cast hnum
    exact_mod_cast (show 1 ≤ p₀.1 by omega)
  have hμN : 1 ≤ (-l)*(N:ℝ) :=
    hnumOne.trans (hpdata.2.2.2.2.trans (mul_le_mul_of_nonneg_left htN hl'))
  have hfactor : 54*B ≤ 3840*B*(-l)*(N:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hμN (show 0 ≤ 3840*B by positivity)
    nlinarith only [hh,hB]
  have hscaled := mul_le_mul_of_nonneg_right hfactor
    (mul_nonneg (Nat.cast_nonneg N : (0:ℝ) ≤ N) hδ)
  have hsmall : 27*B*(N:ℝ)*δ/(P.card:ℝ) < 1/2 := by
    apply (div_lt_iff₀ hPpos).mpr
    nlinarith only [hlarge,hscaled]
  have hhalf := abs_lt.mp (ha.trans_lt hsmall)
  have hround : round α= -round (-α) := by
    apply round_eq_iff.mpr
    simp only [Int.cast_neg,Set.mem_Ico]
    constructor <;> linarith only [hhalf.1,hhalf.2]
  have hlabels := fareySector_integer_labels_enlarged_rectangle_all_slopes
    hw' hl' hB hδ hR' hlarge hnear'
  intro p hp0 hpM hpt0 hptN b hb
  have hh := hlabels (-p.1,p.2)
    (by simpa only [Int.cast_neg] using hp0)
    (by simpa only [Int.cast_neg] using hpM) hpt0 hptN b
    (by simpa only [Int.cast_neg,neg_mul,mul_neg,neg_neg] using hb)
  change b=(-p.1)*round (-α)+p.2*round β at hh
  rw [hround]
  nlinarith only [hh]


private theorem negative_sector_seed_label_of_taylor_remainders_all_slopes
    {K : ℕ} {l w B y₀ α β δ C : ℝ} {g : ℝ → ℝ} {H : ℤ × ℤ → ℤ} {p₀ : ℤ × ℤ} {H₀ : ℤ}
    (hw : w < 0) (hlw : l ≤ w) (hB : 1 ≤ B)
    (hy₀ : y₀ ∈ Set.Icc l w) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hcard : max ((w-l)*(K:ℝ)^2/B) 2 ≤ (((HuxleyLinearForm.fareySector K (-w) (-l)).image
      (fun p : ℤ × ℤ => (-p.1,p.2)))).card)
    (htaylor : ∀ p ∈ ((HuxleyLinearForm.fareySector K (-w) (-l)).image
      (fun p : ℤ × ℤ => (-p.1,p.2))),
      |g ((p.1:ℝ)/p.2)-g y₀-deriv g y₀*((p.1:ℝ)/p.2-y₀)| ≤
        C*|((p.1:ℝ)/p.2)-y₀|^2)
    (hnear : ∀ p ∈ ((HuxleyLinearForm.fareySector K (-w) (-l)).image
      (fun p : ℤ × ℤ => (-p.1,p.2))),
      |(p.1:ℝ)*α+(p.2:ℝ)*β-(p.2:ℝ)*g ((p.1:ℝ)/p.2)-H p| ≤ δ) :
    let η := δ+(K:ℝ)*C*(w-l)^2
    3840*B*η*((-l)*(K:ℝ))*(K:ℝ) < (((HuxleyLinearForm.fareySector K (-w) (-l)).image
      (fun p : ℤ × ℤ => (-p.1,p.2)))).card →
    0 ≤ -(p₀.1:ℝ) → -(p₀.1:ℝ) ≤ 12*((-l)*(K:ℝ)) →
    0 < (p₀.2:ℝ) → (p₀.2:ℝ) ≤ 12*(K:ℝ) →
    (p₀.1:ℝ)/p₀.2=y₀ →
    |(p₀.1:ℝ)*α+(p₀.2:ℝ)*β-(p₀.2:ℝ)*g y₀-H₀| ≤ δ →
    H₀=p₀.1*round (α-deriv g y₀)+p₀.2*round (β-g y₀+y₀*deriv g y₀) := by
  let η := δ+(K:ℝ)*C*(w-l)^2
  change _ → _
  intro hlarge
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hlin (p : ℤ × ℤ) (hp : p ∈ ((HuxleyLinearForm.fareySector K (-w) (-l)).image
      (fun p : ℤ × ℤ => (-p.1,p.2)))) :
      |(p.1:ℝ)*(α-deriv g y₀)+(p.2:ℝ)*(β-g y₀+y₀*deriv g y₀)-H p| ≤ η := by
    obtain ⟨ht,htK,_hc,hlo,hhi⟩ :=
      (mem_negative_fareySector_iff hw hlw).mp hp
    have ht0 : (0:ℝ) < p.2 := by exact_mod_cast (show 0 < p.2 by omega)
    have htK' : (p.2:ℝ) ≤ K := by exact_mod_cast htK
    let x : ℝ := (p.1:ℝ)/p.2
    have hx : x ∈ Set.Icc l w :=
      ⟨(le_div_iff₀ ht0).mpr hlo,(div_le_iff₀ ht0).mpr hhi⟩
    have hdist : |x-y₀| ≤ w-l := abs_le.mpr
      ⟨by linarith [hx.1,hy₀.2],by linarith [hx.2,hy₀.1]⟩
    have htay := htaylor p hp
    have hbudget : (p.2:ℝ)*|g x-g y₀-deriv g y₀*(x-y₀)| ≤ (K:ℝ)*C*(w-l)^2 := by
      calc
        _ ≤ (p.2:ℝ)*(C*|x-y₀|^2) := mul_le_mul_of_nonneg_left htay ht0.le
        _ ≤ (K:ℝ)*(C*(w-l)^2) := by gcongr
        _ = _ := by ring
    have hid : (p.1:ℝ)*(α-deriv g y₀)+(p.2:ℝ)*(β-g y₀+y₀*deriv g y₀)-H p =
        (p.2:ℝ)*(g x-g y₀-deriv g y₀*(x-y₀))+
        ((p.1:ℝ)*α+(p.2:ℝ)*β-(p.2:ℝ)*g x-H p) := by
      dsimp [x]
      field_simp
      ring
    rw [hid]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_of_pos ht0]
    exact (add_le_add hbudget (hnear p hp)).trans_eq (by dsimp [η]; ring)
  intro hp0 hpu hpt hptK hy hpnear
  have hmul : (p₀.1:ℝ)=y₀*(p₀.2:ℝ) := (div_eq_iff hpt.ne').mp hy
  have hid : (p₀.1:ℝ)*(α-deriv g y₀)+(p₀.2:ℝ)*(β-g y₀+y₀*deriv g y₀)-H₀ =
      (p₀.1:ℝ)*α+(p₀.2:ℝ)*β-(p₀.2:ℝ)*g y₀-H₀ := by
    rw [hmul]
    ring
  have hpnear' : |(p₀.1:ℝ)*(α-deriv g y₀)+
      (p₀.2:ℝ)*(β-g y₀+y₀*deriv g y₀)-H₀| ≤ η := by
    rw [hid]
    exact hpnear.trans (le_add_of_nonneg_right (by positivity))
  exact negative_fareySector_integer_labels_enlarged_rectangle_all_slopes hw hlw hB hη hcard hlarge
    (fun q hq => ⟨H q,hlin q hq⟩) p₀ hp0 hpu hpt.le hptK H₀ hpnear'


                                                                                
                                                                      
                                                                        
                                                      
private theorem physicalModelPhase_quartic_negative_original_seed_linearization_all_slopes
    {K : ℕ} {σ δ T M N R B dmin l w Bd Δ Q : ℝ}
    {p₀ : ℤ × ℤ} {k : Fin 17}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ xseed : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    {cnew : ℤ × ℤ → Fin 2 → ℤ} {cseed : Fin 2 → ℤ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hNscale : N^2 ≤ M*R) (hscale : T*N*R^2=M^3)
    (hB : 0 ≤ B) (hdmin : 0 < dmin) (hΔ : 0 ≤ Δ) (hQ : 0 ≤ Q)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ p ∈ ((HuxleyLinearForm.fareySector K (-w) (-l)).image
      (fun p : ℤ × ℤ => (-p.1,p.2))), ∀ i,
      x₁ ((p.1:ℝ)/p.2) i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hxseed : ∀ i, xseed i∈Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hw : w < 0) (hlw : l ≤ w) (hBd : 1 ≤ Bd) (htseed : 0 < p₀.2)
    (hyseed : (p₀.1:ℝ)/p₀.2∈Set.Icc l w)
    (hden : ∀ y ∈ Set.Icc l w, ∀ i, dmin ≤ (r i:ℝ)*y+s i) :
    let S := ((HuxleyLinearForm.fareySector K (-w) (-l)).image
      (fun p : ℤ × ℤ => (-p.1,p.2)))
    let y₀ := (p₀.1:ℝ)/p₀.2
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let a := fun i => round (x₀ i)
    let b := fun y i => round (x₁ y i)
    let n := fun y i => b y i-a i
    let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
    let μseed := fun i => iteratedDeriv 3 (f i) (round (xseed i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (a i)/24
    let q := fun (p : ℤ × ℤ) i => (r i:ℝ)*p.1+s i*p.2
    let d₀ := fun i => iteratedDeriv 1 (f i) (a i)
    let δ₀ := fun i => iteratedDeriv 2 (f i) (a i)/2-(e i:ℝ)/r i
    let θ := fun i => (r i:ℝ)*d₀ i-round ((r i:ℝ)*d₀ i)
    let β₀ := fun i => d₀ i*s i+2*δ₀ i/(3*μ i*r i)
    let α := θ 0-θ 1
    let β := β₀ 0-β₀ 1
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let h := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let φ := fun y => g y-h y
    let z := fun (p : ℤ × ℤ) i => q p i*iteratedDeriv 1 (f i) (b ((p.1:ℝ)/p.2) i)
    let zseed := fun i => q p₀ i*iteratedDeriv 1 (f i) (round (xseed i))
    let jseed := fun i => round ((r i:ℝ)*d₀ i)*p₀.1+
      2*(round (xseed i)-a i)*(e i*p₀.1+v i*p₀.2)
    let Hseed := (cseed 0-jseed 0)-(cseed 1-jseed 1)
    let C := (2/modelPhaseThirdLower σ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*Q/N
    let η := D+(K:ℝ)*C*(w-l)^2
    let U := (4/modelPhaseThirdLower σ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let Z := quarticCurvatureBoundaryRoots (μ 0) (ν 0) (r 0) (s 0)
      (μ 1) (ν 1) (r 1) (s 1) U
    l ∈ finiteBoundaryCell Z l w k →
    w ∈ finiteBoundaryCell Z l w k →
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (xseed i)/2=((e i:ℝ)*p₀.1+v i*p₀.2)/q p₀ i) →
    (∀ i, |(round (xseed i):ℝ)-(a i:ℝ)|^2 ≤ M*R) →
    (∀ p ∈ S, ∀ i,
      iteratedDeriv 2 (f i) (x₁ ((p.1:ℝ)/p.2) i)/2=((e i:ℝ)*p.1+v i*p.2)/q p i) →
    (∀ p ∈ S, ∀ i, |(n ((p.1:ℝ)/p.2) i:ℝ)|^2 ≤ M*R) →
    |μseed 1*(q p₀ 1)^3/(μseed 0*(q p₀ 0)^3)-1| ≤ B*R^2/N^2 →
    (∀ p ∈ S, |(z p 0-cnew p 0)-(z p 1-cnew p 1)| ≤ Δ) →
    (∀ p ∈ S, |q p 0|+|q p 1| ≤ Q) →
    max ((w-l)*(K:ℝ)^2/Bd) 2 ≤ S.card →
    3840*Bd*η*((-l)*(K:ℝ))*(K:ℝ) < S.card →
    -(p₀.1:ℝ) ≤ 12*((-l)*(K:ℝ)) →
    (p₀.2:ℝ) ≤ 12*(K:ℝ) →
    |(zseed 0-cseed 0)-(zseed 1-cseed 1)| ≤ Δ →
    |q p₀ 0|+|q p₀ 1| ≤ Q →
    Hseed=p₀.1*round (α-deriv φ y₀)+p₀.2*round (β-φ y₀+y₀*deriv φ y₀) ∧
    |(α-round (α-deriv φ y₀))*y₀+
      (β-round (β-φ y₀+y₀*deriv φ y₀))-φ y₀| ≤ D/(p₀.2:ℝ) := by
  let S := ((HuxleyLinearForm.fareySector K (-w) (-l)).image
      (fun p : ℤ × ℤ => (-p.1,p.2)))
  let y₀ := (p₀.1:ℝ)/p₀.2
  let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
  let a := fun i => round (x₀ i)
  let b := fun y i => round (x₁ y i)
  let n := fun y i => b y i-a i
  let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
  let ν := fun i => iteratedDeriv 4 (f i) (a i)/24
  let d := fun y i => (r i:ℝ)*y+s i
  let q := fun (p : ℤ × ℤ) i => (r i:ℝ)*p.1+s i*p.2
  let d₀ := fun i => iteratedDeriv 1 (f i) (a i)
  let δ₀ := fun i => iteratedDeriv 2 (f i) (a i)/2-(e i:ℝ)/r i
  let θ := fun i => (r i:ℝ)*d₀ i-round ((r i:ℝ)*d₀ i)
  let β₀ := fun i => d₀ i*s i+2*δ₀ i/(3*μ i*r i)
  let α := θ 0-θ 1
  let β := β₀ 0-β₀ 1
  let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
  let h := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
  let φ := fun y => g y-h y
  let j := fun (p : ℤ × ℤ) i => round ((r i:ℝ)*d₀ i)*p.1+
    2*n ((p.1:ℝ)/p.2) i*(e i*p.1+v i*p.2)
  let H := fun p => (cnew p 0-j p 0)-(cnew p 1-j p 1)
  let zseed := fun i => q p₀ i*iteratedDeriv 1 (f i) (round (xseed i))
  let jseed := fun i => round ((r i:ℝ)*d₀ i)*p₀.1+
    2*(round (xseed i)-a i)*(e i*p₀.1+v i*p₀.2)
  let Hseed := (cseed 0-jseed 0)-(cseed 1-jseed 1)
  let C := (2/modelPhaseThirdLower σ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
  let D := Δ+quarticNonlinearResidualConstant σ δ*Q/N
  let U := (4/modelPhaseThirdLower σ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
  let Z := quarticCurvatureBoundaryRoots (μ 0) (ν 0) (r 0) (s 0)
    (μ 1) (ν 1) (r 1) (s 1) U
  change _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _
  intro hleft hright hbase hseed hseedsquare hpoint hsquare hthird hfourth hqbound hcard hlarge
    hpu hptK hseedfourth hseedQ
  have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hr' (i) : (r i:ℝ) ≠ 0 := by exact_mod_cast hr i
  have hdet' (i) : (v i:ℝ)*r i-e i*s i=1 := by exact_mod_cast hdet i
  have hκ := modelPhaseThirdLower_pos hσ
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans
    (approximateModelPhase_iteratedDeriv_error (hF 0)
      (heathBrownPhysicalPoint_mem_interior hM0 (hA 0) (hW 0)
        (show x₀ 0 ∈ Set.Ioo 0 (W 0) from
          ⟨by linarith [(hx₀ 0).1],by linarith [(hx₀ 0).2]⟩)) 4 le_rfl)
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hC₄ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ0
  have hCN : 0 ≤ quarticNonlinearResidualConstant σ δ := by
    dsimp [quarticNonlinearResidualConstant]
    positivity
  have hCR : 0 ≤ quarticReciprocalConstant σ δ := by
    dsimp [quarticReciprocalConstant]
    positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hgeom (p : ℤ × ℤ) (hp : p ∈ S) :
      (0:ℝ) < p.2 ∧ (p.1:ℝ)/p.2 ∈ Set.Icc l w := by
    obtain ⟨ht,_htK,_hc,hlo,hhi⟩ :=
      (mem_negative_fareySector_iff hw hlw).mp hp
    have ht0 : (0:ℝ) < p.2 := by exact_mod_cast (show 0 < p.2 by omega)
    exact ⟨ht0,⟨(le_div_iff₀ ht0).mpr hlo,(div_le_iff₀ ht0).mpr hhi⟩⟩
  have hy₀ : y₀ ∈ Set.Icc l w := hyseed
  have ht₀ : (0:ℝ) < p₀.2 := by exact_mod_cast htseed
  have hcell {z : ℝ} (hz : z ∈ Set.Icc l w) :
      z ∈ finiteBoundaryCell Z l w k :=
    (finiteBoundaryCell_ordConnected Z l w k).uIcc_subset hleft hright
      (by simpa only [Set.uIcc_of_le hlw] using hz)
  have htaylor (p : ℤ × ℤ) (hp : p ∈ S) :
      |φ ((p.1:ℝ)/p.2)-φ y₀-deriv φ y₀*((p.1:ℝ)/p.2-y₀)| ≤ C*|((p.1:ℝ)/p.2)-y₀|^2 := by
    have he := physicalModelPhase_quartic_taylor_on_boundary_cell
      (u := (p₀.1:ℝ)) (t := (p₀.2:ℝ)) (y := (p.1:ℝ)/p.2)
      hσ hδ hF hT hM0 hN hR hNscale hscale hB hdmin hA hW hx₀
      hxseed hr' ht₀ hdet' hden
      (hcell hy₀) (hcell (hgeom p hp).2) hbase hseed hseedsquare hthird
    exact he.trans_eq (by dsimp [C,U]; ring)
  have hnear (p : ℤ × ℤ) (hp : p ∈ S) :
      |(p.1:ℝ)*α+(p.2:ℝ)*β-(p.2:ℝ)*φ ((p.1:ℝ)/p.2)-H p| ≤ D := by
    let x : ℝ := (p.1:ℝ)/p.2
    have ht0 := (hgeom p hp).1
    have hx := (hgeom p hp).2
    have hpt : p.2 ≠ 0 := by exact_mod_cast ht0.ne'
    have hd (i) : 0 < d x i := hdmin.trans_le (hden x hx i)
    have hqd (i) : q p i=d x i*(p.2:ℝ) := by dsimp [q,d,x]; field_simp
    have hqpos (i) : 0 < q p i := by rw [hqd i]; exact mul_pos (hd i) ht0
    have hqint (i) : r i*p.1+s i*p.2 ≠ 0 := by
      have hh : (0:ℝ) < ((r i*p.1+s i*p.2:ℤ):ℝ) := by
        simpa only [Int.cast_add,Int.cast_mul] using hqpos i
      exact_mod_cast hh.ne'
    have he := physicalModelPhase_quartic_fourth_condition_nonlinear_with_labels
      (cnew := cnew p) hσ hδ hF hT hM hN hR hRM hscale hA hW hx₀
      (hx₁ p hp) hr hpt hqint hdet hbase (hpoint p hp) (hsquare p hp) (hfourth p hp)
    have hid : (p.1:ℝ)*α+(p.2:ℝ)*β-(p.2:ℝ)*φ x-H p =
        (θ 0-θ 1)*p.1+(β₀ 0-β₀ 1)*p.2-(p.2:ℝ)*g x+(p.2:ℝ)*h x-H p := by
      dsimp [α,β,φ]
      ring
    rw [hid]
    apply he.trans
    dsimp only [D]
    gcongr
    exact hqbound p hp
  have hqseedpos (i) : 0 < q p₀ i := by
    have hh : q p₀ i=d y₀ i*(p₀.2:ℝ) := by dsimp only [q,d,y₀]; field_simp
    rw [hh]
    exact mul_pos (hdmin.trans_le (hden y₀ hy₀ i)) ht₀
  have hqseedint (i) : r i*p₀.1+s i*p₀.2 ≠ 0 := by
    have hh : (0:ℝ) < ((r i*p₀.1+s i*p₀.2:ℤ):ℝ) := by
      simpa only [Int.cast_add,Int.cast_mul] using hqseedpos i
    exact_mod_cast hh.ne'
  have hseednear :
      |(p₀.1:ℝ)*α+(p₀.2:ℝ)*β-(p₀.2:ℝ)*φ y₀-Hseed| ≤ D := by
    have he := physicalModelPhase_quartic_fourth_condition_nonlinear_with_labels
      (cnew := cseed) hσ hδ hF hT hM hN hR hRM hscale hA hW hx₀
      hxseed hr htseed.ne' hqseedint hdet hbase hseed
      (fun i => by simpa only [Int.cast_sub] using hseedsquare i) hseedfourth
    have hid : (p₀.1:ℝ)*α+(p₀.2:ℝ)*β-(p₀.2:ℝ)*φ y₀-Hseed =
        (θ 0-θ 1)*p₀.1+(β₀ 0-β₀ 1)*p₀.2-
        (p₀.2:ℝ)*g y₀+(p₀.2:ℝ)*h y₀-Hseed := by
      dsimp only [α,β,φ]; ring
    rw [hid]
    apply he.trans
    dsimp only [D]
    gcongr
  have hp0 : 0 ≤ -(p₀.1:ℝ) := by
    have hh := (div_le_iff₀ ht₀).mp hy₀.2
    have hw0 : w*(p₀.2:ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hw.le ht₀.le
    linarith only [hh,hw0]
  have hlabel := negative_sector_seed_label_of_taylor_remainders_all_slopes
    hw hlw hBd hy₀ hD hC hcard htaylor hnear hlarge
    hp0 hpu ht₀ hptK rfl hseednear
  refine ⟨hlabel,?_⟩
  have hid : (p₀.2:ℝ)*((α-round (α-deriv φ y₀))*y₀+
      (β-round (β-φ y₀+y₀*deriv φ y₀))-φ y₀) =
      (p₀.1:ℝ)*α+(p₀.2:ℝ)*β-(p₀.2:ℝ)*φ y₀-Hseed := by
    rw [hlabel]
    push_cast
    dsimp only [y₀]
    field_simp
    ring
  have hmulabs := congrArg abs hid
  rw [abs_mul,abs_of_pos ht₀] at hmulabs
  apply (le_div_iff₀ ht₀).mpr
  rw [mul_comm]
  exact hmulabs.trans_le hseednear


                                                                    
                                                                     
private theorem physicalModelPhase_actual_fourier_negative_original_seed_residual_all_slopes
    {σ δ T M N R dmin : ℝ} {k : Fin 17} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2) (Mat : Fin 4 → ℤ) (anchor : ℚ) (e r v s : ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ xref : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
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
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    let pseed : ℤ × ℤ := (v*(q 0:ℤ)-s*(rat 0).num,r*(rat 0).num-e*(q 0:ℤ))
    let yseed := (pseed.1:ℝ)/pseed.2
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let dr := fun i => deriv (f i) (ar i)
    let δr := fun i => iteratedDeriv 2 (f i) (ar i)/2-(ep i:ℝ)/rp i
    let θr := fun i => (rp i:ℝ)*dr i-round ((rp i:ℝ)*dr i)
    let βr := fun i => dr i*sp i+2*δr i/(3*μr i*rp i)
    let ac := θr 0-θr 1
    let bc := βr 0-βr 1
    let g := rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1)
    let hq := quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1)
    let φ := fun y => g y-hq y
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := D+(K:ℝ)*Ctay*(β-α)^2
    let U := (4/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
      (μr 1) (νr 1) (rp 1) (sp 1) U
    1 ≤ M → 1 ≤ R → R ≤ M → N^2 ≤ M*R → 0 < dmin →
    Δ < 1/2 →
    (∀ i, rp i ≠ 0) →
    (∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i) →
    (∀ i, (H+|x₀ i-xref i|+1)^2 ≤ M*R) →
    (∀ y∈Icc α β, ∀ i, dmin ≤ (rp i:ℝ)*y+sp i) →
    α ∈ finiteBoundaryCell Z α β k → β ∈ finiteBoundaryCell Z α β k →
    3840*128*η*((-α)*(K:ℝ))*(K:ℝ) < S.card →
    |(ac-round (ac-deriv φ yseed))*yseed+
      (bc-round (bc-φ yseed+yseed*deriv φ yseed))-g yseed+hq yseed| ≤ D/(pseed.2:ℝ) := by
  classical
  intro f hlevel q mu ell b cround tau dual w radius hcolor hnear c J B
    hsmall hNR hRN hcube hminscale hMatdet hMatt hMatmap hMatgamma
    C H ε hNtwo hL hU hchart hdl hdw hnum hdyad hanchor hcut hcount
    l w' α β K S C₂ C₃ κ Ct Cc Δ ep rp sp pseed yseed ar μr νr dr δr θr βr ac bc g hq φ
    Ctay D η U Z hMone hRone hRM hNscale hdmin hΔ hrp hxref href hbudget
    hd hleft hright hlarge
  let vp : Fin 2 → ℤ := ![v,Mat 0*v+Mat 1*s]
  have hF₃ i := approximateModelPhase_mono (hF i) (by norm_num : 3 ≤ 4) le_rfl
  obtain ⟨hcard,ξ,hξ⟩ := physicalModelPhase_actual_fourier_complete_negative_sector_fourth
    Q K₀ rat vinv parity Mat anchor e r v s hσ hδ hF₃ hT hM hN hR hQ hscale hmesh
    hA hW hx₀ hden hinv hlevel hcolor hnear hsmall hNR hRN hcube hminscale
    hMatdet hMatt hMatmap hMatgamma hNtwo hL hU hchart hdl hdw hnum hdyad hanchor hcut hcount
  let qp := fun (p : ℤ × ℤ) i => (rp i:ℝ)*p.1+sp i*p.2
  let ap := fun (p : ℤ × ℤ) i => (ep i:ℝ)*p.1+vp i*p.2
  let xp := fun p : ℤ × ℤ => ξ ((p.1:ℝ)/p.2)
  let zp := fun p i => qp p i*deriv (f i) (round (xp p i))
  have hqe (p : ℤ × ℤ) (i : Fin 2) :
      ((![r*p.1+s*p.2,Mat 2*(e*p.1+v*p.2)+Mat 3*(r*p.1+s*p.2)] i:ℤ):ℝ)=qp p i := by
    fin_cases i <;> dsimp only [qp,rp,sp] <;> push_cast <;> ring
  have hae (p : ℤ × ℤ) (i : Fin 2) :
      ((![e*p.1+v*p.2,Mat 0*(e*p.1+v*p.2)+Mat 1*(r*p.1+s*p.2)] i:ℤ):ℝ)=ap p i := by
    fin_cases i <;> dsimp only [ap,ep,vp] <;> push_cast <;> ring
  have hpoints (p) (hp : p∈S) (i) :
      xp p i∈Ioo (1/2:ℝ) (W i-1/2) ∧
      iteratedDeriv 2 (f i) (xp p i)/2=ap p i/qp p i ∧
      |xp p i-x₀ i| ≤ H ∧ 0 < qp p i ∧ qp p i ≤ Q := by
    have hh := (hξ p hp).1 i
    simpa only [hqe,hae] using hh
  have hlabels (p : ℤ × ℤ) : ∃ ci : Fin 2 → ℤ, p∈S →
      (∀ i, ci i∈minorArcCenterLabels (zp p i) Δ) ∧
      |(zp p 0-ci 0)-(zp p 1-ci 1)| ≤ Δ := by
    by_cases hp : p∈S
    · have hh := (hξ p hp).2.2 hΔ
      simp only [hqe] at hh
      obtain ⟨c₀,hc₀,c₁,hc₁,_hrnd,hfour,_⟩ := hh
      refine ⟨![c₀,c₁],fun _ => ⟨?_,hfour⟩⟩
      intro i
      fin_cases i
      · exact hc₀
      · exact hc₁
    · exact ⟨fun _ => 0,fun h => False.elim (hp h)⟩
  choose cnew hcnew using hlabels
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans
    (approximateModelPhase_iteratedDeriv_error (hF 0)
      (by norm_num : (3/2:ℝ)∈Ioo 1 2) 4 le_rfl)
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hC₂ : 0 ≤ C₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ : 0 ≤ C₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hΔpos : 0 ≤ Δ := by dsimp only [Δ,Ct,Cc]; positivity
  have hH : 0 < H := by dsimp only [H,C]; positivity
  have hε : 0 < ε := by dsimp only [ε,C]; positivity
  have hlw : l < w' := by dsimp only [l,w']; linarith only [hε]
  have hchartR : (v:ℝ)*r-e*s=1 := by exact_mod_cast hchart
  have hnegβ : β < 0 := div_neg_of_neg_of_pos hnum hdl
  have hαβ : α ≤ β := by
    have hh := inverseFarey_difference hchartR hdl.ne' hdw.ne'
    change β-α=(w'-l)/(((r:ℝ)*l-e)*((r:ℝ)*w'-e)) at hh
    have hp' : 0 ≤ (w'-l)/(((r:ℝ)*l-e)*((r:ℝ)*w'-e)) := by positivity
    linarith only [hh,hp']
  have hqpos i : (0:ℝ) < q i := by exact_mod_cast (rat i).pos
  have hrat i : (rat i:ℝ)=((rat i).num:ℝ)/(q i:ℝ) := Rat.cast_def _
  have hdenR : (Mat 2:ℝ)*(rat 0).num+Mat 3*q 0=q 1 := by
    calc
      _ = ((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)*q 0 := by
        rw [hrat]; field_simp [(hqpos 0).ne']
      _ = q 1 := by rw [hMatt]; field_simp [(hqpos 0).ne']
  have hnumR : (Mat 0:ℝ)*(rat 0).num+Mat 1*q 0=(rat 1).num := by
    have hm := hMatmap
    rw [hMatt,hrat 0,hrat 1] at hm
    have hh := (div_eq_iff (div_ne_zero (hqpos 1).ne' (hqpos 0).ne')).mp hm
    field_simp [(hqpos 0).ne',(hqpos 1).ne'] at hh
    nlinarith only [hh]
  have hseedq (i) : qp pseed i=(q i:ℝ) := by
    fin_cases i
    · dsimp only [qp,pseed,rp,sp]; push_cast
      linear_combination (q 0:ℝ)*hchartR
    · dsimp only [qp,pseed,rp,sp]; push_cast
      linear_combination ((Mat 2:ℝ)*(rat 0).num+Mat 3*q 0)*hchartR+hdenR
  have hseeda (i) : ap pseed i=((rat i).num:ℝ) := by
    fin_cases i
    · dsimp only [ap,pseed,ep,vp]; push_cast
      linear_combination ((rat 0).num:ℝ)*hchartR
    · dsimp only [ap,pseed,ep,vp]; push_cast
      linear_combination ((Mat 0:ℝ)*(rat 0).num+Mat 1*q 0)*hchartR+hnumR
  have hseedroot (i) : iteratedDeriv 2 (f i) (x₀ i)/2=ap pseed i/qp pseed i := by
    rw [hseedq,hseeda,hlevel,hrat]
  have hseedtd : (pseed.2:ℝ)=((r:ℝ)*(rat 0:ℝ)-e)*q 0 := by
    dsimp only [pseed]; push_cast; rw [hrat]; field_simp [(hqpos 0).ne']
  have hseedd : 0 < (r:ℝ)*(rat 0:ℝ)-e := by
    nlinarith only [hdl,hdw]
  have htseed : 0 < pseed.2 := by
    have hh : (0:ℝ) < pseed.2 := by rw [hseedtd]; exact mul_pos hseedd (hqpos 0)
    exact_mod_cast hh
  have hys : yseed=((v:ℝ)-s*(rat 0:ℝ))/((r:ℝ)*(rat 0:ℝ)-e) := by
    dsimp only [yseed,pseed]
    push_cast
    rw [hrat 0]
    field_simp [(hqpos 0).ne']
  have hyseed : yseed∈Icc α β := by
    rw [hys]
    apply inverseFarey_mem_interval_signed hchartR hdl hdw
    exact ⟨by linarith only [hε],by linarith only [hε]⟩
  have hdetp (i) : vp i*rp i-ep i*sp i=1 := by
    fin_cases i
    · exact hchart
    · change (Mat 0*v+Mat 1*s)*(Mat 2*e+Mat 3*r)-
        (Mat 0*e+Mat 1*r)*(Mat 2*v+Mat 3*s)=1
      linear_combination (v*r-e*s)*hMatdet+hchart
  have hsq (p) (hp : p∈S) (i) :
      |((round (xp p i)-ar i:ℤ):ℝ)|^2 ≤ M*R := by
    have hh := rounded_displacement_bound (xp p i) (xref i)
    have htri := abs_sub_le (xp p i) (x₀ i) (xref i)
    have hdist := (hpoints p hp i).2.2.1
    have hb : |(round (xp p i):ℝ)-(ar i:ℝ)| ≤ H+|x₀ i-xref i|+1 := by
      dsimp only [ar]
      linarith only [hh,htri,hdist]
    rw [Int.cast_sub]
    exact (pow_le_pow_left₀ (abs_nonneg _) hb 2).trans (hbudget i)
  have hseedSq i : |(round (x₀ i):ℝ)-(ar i:ℝ)|^2 ≤ M*R := by
    have hh := rounded_displacement_bound (x₀ i) (xref i)
    have hb : |(round (x₀ i):ℝ)-(ar i:ℝ)| ≤ H+|x₀ i-xref i|+1 := by
      dsimp only [ar]
      linarith only [hh,hH]
    exact (pow_le_pow_left₀ (abs_nonneg _) hb 2).trans (hbudget i)
  obtain ⟨_v,_hv,hthird,_hsecond,_hfirst,hfourth⟩ := physicalModelPhase_actual_fourier_conditions
    Q K₀ rat vinv parity hσ hδ hF₃ hT hM hN hR hQ hscale hmesh
    hA hW hx₀ hden hinv hlevel hcolor hnear
  have hthird' : |mu 1*(qp pseed 1)^3/(mu 0*(qp pseed 0)^3)-1| ≤ B*R^2/N^2 := by
    simpa only [hseedq] using hthird
  have hqsum p (hp : p∈S) : |qp p 0|+|qp p 1| ≤ 2*(Q:ℝ) := by
    rw [abs_of_pos (hpoints p hp 0).2.2.2.1,abs_of_pos (hpoints p hp 1).2.2.2.1]
    linarith only [(hpoints p hp 0).2.2.2.2,(hpoints p hp 1).2.2.2.2]
  have ha : (anchor:ℝ)∈Icc l w' := by
    have hh := abs_le.mp hanchor
    exact ⟨by dsimp only [l]; linarith only [hh.1],
      by dsimp only [w']; linarith only [hh.2]⟩
  have hseedI : (rat 0:ℝ)∈Icc l w' :=
    ⟨by dsimp only [l]; linarith only [hε],
      by dsimp only [w']; linarith only [hε]⟩
  have hrect := inverseFarey_negative_original_seed_enlarged_rectangle
    hchart hdl hdw hnum ha hseedI hdyad hcut
    (show ((rat 0).den:ℝ) ≤ (Q:ℝ) by exact_mod_cast (hden 0).1)
  have hpu : -(pseed.1:ℝ) ≤ 12*((-α)*(K:ℝ)) := hrect.2.2.2.1
  have hptK : (pseed.2:ℝ) ≤ 12*(K:ℝ) := hrect.2.2.2.2
  have hseedfourth :
      |(qp pseed 0*iteratedDeriv 1 (f 0) (round (x₀ 0))-cround 0)-
       (qp pseed 1*iteratedDeriv 1 (f 1) (round (x₀ 1))-cround 1)| ≤ Δ := by
    simp only [hseedq,iteratedDeriv_one]
    apply hfourth.trans
    have hqQ : (q 0:ℝ) ≤ Q := by exact_mod_cast (hden 0).1
    have hCt : 0 ≤ Ct := by dsimp only [Ct]; positivity
    have hCc : 0 ≤ Cc := by dsimp only [Cc]; positivity
    have hcoeff : B ≤ 37*B/2+16*B*Cc+2*Ct+2*Cc := by
      nlinarith only [hB,hCt,hCc,mul_nonneg hB hCc]
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hqQ hB) hN.le).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoeff (by positivity : (0:ℝ) ≤ Q)) hN.le)
  have hseedQ : |qp pseed 0|+|qp pseed 1| ≤ 2*(Q:ℝ) := by
    rw [hseedq,hseedq,abs_of_pos (hqpos 0),abs_of_pos (hqpos 1)]
    have hq0 : (q 0:ℝ) ≤ Q := by exact_mod_cast (hden 0).1
    have hq1 : (q 1:ℝ) ≤ Q := by exact_mod_cast (hden 1).1
    linarith only [hq0,hq1]
  have hcommon := physicalModelPhase_quartic_negative_original_seed_linearization_all_slopes
    (p₀:=pseed) (x₀:=xref) (xseed:=x₀) (x₁:=ξ) (e:=ep) (r:=rp) (v:=vp) (s:=sp)
    (cnew:=cnew) (cseed:=cround) hσ hδ hF hT hMone hN hRone hRM hNscale hscale
    hB hdmin hΔpos (by positivity : (0:ℝ) ≤ 2*(Q:ℝ))
    hA hW hxref (fun p hp i => (hpoints p hp i).1) hx₀ hrp hdetp
    hnegβ hαβ (by norm_num : (1:ℝ) ≤ 128) htseed hyseed hd
    hleft hright href hseedroot hseedSq
    (fun p hp i => (hpoints p hp i).2.1) hsq hthird'
    (fun p hp => by simpa only [iteratedDeriv_one] using (hcnew p hp).2) hqsum hcard hlarge
    hpu hptK hseedfourth hseedQ
  have hres := hcommon.2
  simp only [iteratedDeriv_one] at hres
  change |(ac-round (ac-deriv φ yseed))*yseed+
    (bc-round (bc-φ yseed+yseed*deriv φ yseed))-φ yseed| ≤ D/(pseed.2:ℝ) at hres
  convert hres using 1
  congr 1
  dsimp only [φ]
  ring


                                                                 
                                                                        
                                                                     
                                        
theorem physicalModelPhase_actual_fourier_original_seed_bounds_all_negative_slopes
    {σ δ T M N R dmin : ℝ} {k : Fin 17} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2) (Mat : Fin 4 → ℤ) (anchor : ℚ) (e r v s : ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ xref : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
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
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    let pseed : ℤ × ℤ := (v*(q 0:ℤ)-s*(rat 0).num,r*(rat 0).num-e*(q 0:ℤ))
    let yseed := (pseed.1:ℝ)/pseed.2
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let dr := fun i => deriv (f i) (ar i)
    let δr := fun i => iteratedDeriv 2 (f i) (ar i)/2-(ep i:ℝ)/rp i
    let θr := fun i => (rp i:ℝ)*dr i-round ((rp i:ℝ)*dr i)
    let βr := fun i => dr i*sp i+2*δr i/(3*μr i*rp i)
    let ac := θr 0-θr 1
    let bc := βr 0-βr 1
    let g := rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1)
    let hq := quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1)
    let φ := fun y => g y-hq y
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := D+(K:ℝ)*Ctay*(β-α)^2
    let U := (4/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
      (μr 1) (νr 1) (rp 1) (sp 1) U
    1 ≤ M → 1 ≤ R → R ≤ M → N^2 ≤ M*R → 0 < dmin →
    Δ < 1/2 →
    (∀ i, rp i ≠ 0) →
    (∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i) →
    (∀ i, (H+|x₀ i-xref i|+1)^2 ≤ M*R) →
    (∀ y∈Icc α β, ∀ i, dmin ≤ (rp i:ℝ)*y+sp i) →
    α ∈ finiteBoundaryCell Z α β k → β ∈ finiteBoundaryCell Z α β k →
    3840*128*η*((-α)*(K:ℝ))*(K:ℝ) < S.card →
    |iteratedDeriv 2 g yseed-iteratedDeriv 2 hq yseed| ≤ U ∧
    |(ac-round (ac-deriv φ yseed))*yseed+
      (bc-round (bc-φ yseed+yseed*deriv φ yseed))-g yseed+hq yseed| ≤
      D/(pseed.2:ℝ) := by
  classical
  intro f hlevel q mu ell b cround tau dual w radius hcolor hnear c J B
    hsmall hNR hRN hcube hminscale hMatdet hMatt hMatmap hMatgamma
    C H ε hNtwo hL hU hchart hdl hdw hnum hdyad hanchor hcut hcount
    l w' α β K S C₂ C₃ κ Ct Cc Δ ep rp sp pseed yseed ar μr νr dr δr θr βr ac bc g hq φ
    Ctay D η U Z hMone hRone hRM hNscale hdmin hΔ hrp hxref href hbudget
    hd hleft hright hlarge
  have hresult := physicalModelPhase_actual_fourier_negative_original_seed_residual_all_slopes
    Q K₀ rat vinv parity Mat anchor e r v s
    hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv
    hlevel hcolor hnear hsmall hNR hRN hcube hminscale hMatdet hMatt hMatmap hMatgamma
    hNtwo hL hU hchart hdl hdw hnum hdyad hanchor hcut hcount
    hMone hRone hRM hNscale hdmin hΔ hrp hxref href hbudget hd hleft hright hlarge
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hε : 0 < ε := by dsimp only [ε,C]; positivity
  have ha : (anchor:ℝ)∈Icc l w' := by
    have hh := abs_le.mp hanchor
    exact ⟨by dsimp only [l]; linarith only [hh.1],
      by dsimp only [w']; linarith only [hh.2]⟩
  have hseedI : (rat 0:ℝ)∈Icc l w' :=
    ⟨by dsimp only [l]; linarith only [hε],
      by dsimp only [w']; linarith only [hε]⟩
  have hrect := inverseFarey_negative_original_seed_enlarged_rectangle
    hchart hdl hdw hnum ha hseedI hdyad hcut
    (show ((rat 0).den:ℝ) ≤ (Q:ℝ) by exact_mod_cast (hden 0).1)
  have ht : (0:ℝ) < pseed.2 := hrect.1
  have hyseed : yseed∈Icc α β := hrect.2.1
  have hchartR : (v:ℝ)*r-e*s=1 := by exact_mod_cast hchart
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  refine ⟨?_,hresult⟩
  let vp : Fin 2 → ℤ := ![v,Mat 0*v+Mat 1*s]
  let qp := fun (p : ℤ × ℤ) i => (rp i:ℝ)*p.1+sp i*p.2
  let ap := fun (p : ℤ × ℤ) i => (ep i:ℝ)*p.1+vp i*p.2
  have hH : 0 < H := by dsimp only [H,C]; positivity
  have hF₃ i := approximateModelPhase_mono (hF i) (by norm_num : 3 ≤ 4) le_rfl
  have hqpos i : (0:ℝ) < q i := by exact_mod_cast (rat i).pos
  have hrat i : (rat i:ℝ)=((rat i).num:ℝ)/(q i:ℝ) := Rat.cast_def _
  have hdenR : (Mat 2:ℝ)*(rat 0).num+Mat 3*q 0=q 1 := by
    calc
      _ = ((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)*q 0 := by
        rw [hrat]; field_simp [(hqpos 0).ne']
      _ = q 1 := by rw [hMatt]; field_simp [(hqpos 0).ne']
  have hnumR : (Mat 0:ℝ)*(rat 0).num+Mat 1*q 0=(rat 1).num := by
    have hm := hMatmap
    rw [hMatt,hrat 0,hrat 1] at hm
    have hh := (div_eq_iff (div_ne_zero (hqpos 1).ne' (hqpos 0).ne')).mp hm
    field_simp [(hqpos 0).ne',(hqpos 1).ne'] at hh
    nlinarith only [hh]
  have hseedq (i) : qp pseed i=(q i:ℝ) := by
    fin_cases i
    · dsimp only [qp,pseed,rp,sp]; push_cast
      linear_combination (q 0:ℝ)*hchartR
    · dsimp only [qp,pseed,rp,sp]; push_cast
      linear_combination ((Mat 2:ℝ)*(rat 0).num+Mat 3*q 0)*hchartR+hdenR
  have hseeda (i) : ap pseed i=((rat i).num:ℝ) := by
    fin_cases i
    · dsimp only [ap,pseed,ep,vp]; push_cast
      linear_combination ((rat 0).num:ℝ)*hchartR
    · dsimp only [ap,pseed,ep,vp]; push_cast
      linear_combination ((Mat 0:ℝ)*(rat 0).num+Mat 1*q 0)*hchartR+hnumR
  have hseedroot (i) : iteratedDeriv 2 (f i) (x₀ i)/2=ap pseed i/qp pseed i := by
    rw [hseedq,hseeda,hlevel,hrat]
  have hdetp (i) : vp i*rp i-ep i*sp i=1 := by
    fin_cases i
    · exact hchart
    · change (Mat 0*v+Mat 1*s)*(Mat 2*e+Mat 3*r)-
        (Mat 0*e+Mat 1*r)*(Mat 2*v+Mat 3*s)=1
      linear_combination (v*r-e*s)*hMatdet+hchart
  have hseedSq i : |(round (x₀ i):ℝ)-(ar i:ℝ)|^2 ≤ M*R := by
    have hh := rounded_displacement_bound (x₀ i) (xref i)
    have hb : |(round (x₀ i):ℝ)-(ar i:ℝ)| ≤ H+|x₀ i-xref i|+1 := by
      dsimp only [ar]
      linarith only [hh,hH]
    exact (pow_le_pow_left₀ (abs_nonneg _) hb 2).trans (hbudget i)
  obtain ⟨_v,_hv,hthird,_hsecond,_hfirst,_hfourth⟩ := physicalModelPhase_actual_fourier_conditions
    Q K₀ rat vinv parity hσ hδ hF₃ hT hM hN hR hQ hscale hmesh
    hA hW hx₀ hden hinv hlevel hcolor hnear
  have hthird' : |mu 1*(qp pseed 1)^3/(mu 0*(qp pseed 0)^3)-1| ≤ B*R^2/N^2 := by
    simpa only [hseedq] using hthird
  exact physicalModelPhase_quartic_curvature_source_scale
    (u:=(pseed.1:ℝ)) (t:=(pseed.2:ℝ)) (x₀:=xref) (x₁:=x₀)
    (e:=fun i => (ep i:ℝ)) (r:=fun i => (rp i:ℝ))
    (v:=fun i => (vp i:ℝ)) (s:=fun i => (sp i:ℝ))
    hσ hδ hF hT hM hN hRone hNscale hscale hB hdmin hA hW hxref hx₀
    (fun i => by exact_mod_cast hrp i) ht
    (fun i => by change 0 < qp pseed i; rw [hseedq]; exact hqpos i)
    (fun i => by
      exact_mod_cast hdetp i) href hseedroot hseedSq
    (hd yseed hyseed) hthird'



                                                                           
private theorem physicalModelPhase_actual_fourier_signed_height_square_span_fixed_reference_quartic_witnesses
    {Kcoord : ℕ}
    (S : Finset ℕ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R d nSpan base l w Bcut : ℝ} {k : Fin 17}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hsourcesquare : nSpan^2 ≤ M*R)
    (hden : ∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den)
    (hinv : ∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1)
    (hchart : v*r-e*s=1)
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ (Kcoord:ℝ)*d) (hBcut : 0 < Bcut) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    32*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card →
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
    let ε := κ/(16*(Cphys+2)*R^2)
    2 ≤ N →
    (∀ j∈S, ∀ i, x j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, ∀ i, x j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, 0 < (r:ℝ)*((rat j 0:ℝ)-ε)-e) →
    (∀ j∈S, 0 < (r:ℝ)*((rat j 0:ℝ)+ε)-e) →
    (∀ j∈S, 0 < (v:ℝ)-s*((rat j 0:ℝ)+ε) ∨ (v:ℝ)-s*((rat j 0:ℝ)-ε) < 0) →
    (∀ j∈S, max ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e) ≤
      2*min ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e)) →
    (∀ j∈S, |(anchor j:ℝ)-(rat j 0:ℝ)| ≤ ε) →
    (∀ j∈S, 256*((anchor j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ j∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor j).den) →
    let lo := fun j => (rat j 0:ℝ)-ε
    let hi := fun j => (rat j 0:ℝ)+ε
    let α := fun j => ((v:ℝ)-s*hi j)/((r:ℝ)*hi j-e)
    let β := fun j => ((v:ℝ)-s*lo j)/((r:ℝ)*lo j-e)
    let Kaux := fun j => ⌊((Q:ℝ)/3)*min ((r:ℝ)*lo j-e) ((r:ℝ)*hi j-e)⌋₊
    let Saux := fun j => if 0 < α j then HuxleyLinearForm.fareySector (Kaux j) (α j) (β j)
      else (HuxleyLinearForm.fareySector (Kaux j) (-β j) (-α j)).image
        (fun p : ℤ × ℤ => (-p.1,p.2))
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    ∀ xref : Fin 2 → ℝ,
      (∀ i, rp i ≠ 0 ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i) →
    ∀ Hspan : Fin 2 → ℝ,
    (∀ j∈S, ∀ i, |x j i-xref i| ≤ Hspan i) →
    (∀ i, 2*Hspan i+1 ≤ nSpan) →
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let G := minorArcCoordinate (μr 0) (rp 0) (sp 0)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*d^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := fun j => D+(Kaux j:ℝ)*Ctay*(β j-α j)^2
    let U := Ccurv*R^4/(N*d^3)
    let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
      (μr 1) (νr 1) (rp 1) (sp 1) U
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    (∀ j∈S, ∀ i, (H+|x j i-xref i|+1)^2 ≤ M*R) →
    D ≤ 1/2 → Δ < 1/2 →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈finiteBoundaryCell Z l w k) →
    (∀ j∈S, β j∈finiteBoundaryCell Z l w k) →
    (∀ j∈S, 3840*128*η j*((max |α j| |β j|)*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    ((2*Kcoord+1:ℕ):ℝ)*Ccurv*Cphys ≤ Bcut →
    |G l| ≤ |(rp 0:ℝ)| *N^2/(Bcut*R^2) →
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S.card:ℝ)
    let vp : Fin 2 → ℤ := ![v,Mat 0*v+Mat 1*s]
    ∃ j : Fin 8 → ℕ, ∃ z : Fin 8 → ℝ, ∃ curve : ℝ → Fin 2 → ℝ, ∃ alpha beta : ℝ,
      (∀ a, j a∈S ∧ ∀ i,
        (rat (j a) i:ℝ)=((ep i:ℝ)*z a+vp i)/((rp i:ℝ)*z a+sp i)) ∧
      StrictMono z ∧ 0 < L ∧ (L*N)^2 ≤ M*R ∧ 0 ≤ Kres ∧
      (∀ t∈Icc (z 0) (z 7), t∈Icc l w ∧ ∀ i,
        curve t i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        d ≤ (rp i:ℝ)*t+sp i ∧ (rp i:ℝ)*t+sp i ≤ 2*d ∧
        iteratedDeriv 2 (f i) (curve t i)/2=((ep i:ℝ)*t+vp i)/((rp i:ℝ)*t+sp i) ∧
        |(round (curve t i):ℝ)-(round (xref i):ℝ)|^2 ≤ M*R) ∧
      (∀ i : Fin 7, L*N ≤ |G (z i.succ)-G (z i.castSucc)|) ∧
      (∀ i : Fin 8,
        |alpha*z i+beta-rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1) (z i)+
          quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1) (z i)| ≤
          Kres*R^2/|(rp 0:ℝ)*G (z i)|) := by
  classical
  intro Vheight P₁ P₂ hS f hlevel q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H ε hNtwo hL hU hdl hdw hnum hdyad hanchor hcut hcount
    lo hi α β Kaux Saux C₂ C₃ Ct Cc Δ ep rp sp
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hF₂ i := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl
  intro xref hxr Hspan hdisplacement hspan ar μr νr G Ccurv Ctay D η U Z Kres hbudget hD hΔ
    hdenregion hleft hright hlarge hBsize hGcut Blabels L vp
  have hrp i : rp i ≠ 0 := (hxr i).1
  have hxref i : xref i∈Ioo (1/2:ℝ) (W i-1/2) := (hxr i).2.1
  have href i : iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i := (hxr i).2.2
  let p : ℕ → ℤ × ℤ := fun j =>
    (v*(q j 0:ℤ)-s*(rat j 0).num,r*(rat j 0).num-e*(q j 0:ℤ))
  let y := fun j => ((p j).1:ℝ)/(p j).2
  let dr := fun i => deriv (f i) (ar i)
  let δr := fun i => iteratedDeriv 2 (f i) (ar i)/2-(ep i:ℝ)/rp i
  let θr := fun i => (rp i:ℝ)*dr i-round ((rp i:ℝ)*dr i)
  let βr := fun i => dr i*sp i+2*δr i/(3*μr i*rp i)
  let ac := θr 0-θr 1
  let bc := βr 0-βr 1
  let g := rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1)
  let hq := quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1)
  let φ := fun z => g z-hq z
  have hMone : 1 ≤ M := hR.trans hRM
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hε : 0 < ε := by dsimp only [ε,Cphys]; positivity
  have hNscale : N^2 ≤ M*R := by
    apply (pow_le_pow_iff_left₀ (sq_nonneg N) (mul_nonneg hM.le hRpos.le)
      (by norm_num : (3:ℕ) ≠ 0)).mp
    have hh := pow_le_pow_left₀ (pow_nonneg hN.le 3) hNcube 2
    have hh' := mul_le_mul_of_nonneg_left hRM (show 0 ≤ M^2*R^3 by positivity)
    nlinarith only [hh,hh']
  have hrect j (hj : j∈S) : 0 < (p j).2 ∧ y j∈Icc (α j) (β j) := by
    have ha : (anchor j:ℝ)∈Icc (lo j) (hi j) := by
      have hh := abs_le.mp (hanchor j hj)
      exact ⟨by dsimp only [lo]; linarith only [hh.1],
        by dsimp only [hi]; linarith only [hh.2]⟩
    have hp : (rat j 0:ℝ)∈Icc (lo j) (hi j) := by
      constructor <;> dsimp only [lo,hi] <;> linarith only [hε]
    rcases hnum j hj with hpos | hneg
    · have hh := inverseFarey_original_seed_enlarged_rectangle_signed
        hchart (hdl j hj) (hdw j hj) hpos ha hp (hdyad j hj) (hcut j hj)
        (show ((rat j 0).den:ℝ) ≤ (Q:ℝ) by exact_mod_cast (hden j hj 0).1)
      exact ⟨by exact_mod_cast hh.1,hh.2.1⟩
    · have hh := inverseFarey_negative_original_seed_enlarged_rectangle
        hchart (hdl j hj) (hdw j hj) hneg ha hp (hdyad j hj) (hcut j hj)
        (show ((rat j 0).den:ℝ) ≤ (Q:ℝ) by exact_mod_cast (hden j hj 0).1)
      exact ⟨by exact_mod_cast hh.1,hh.2.1⟩
  have hy j (hj : j∈S) : y j∈finiteBoundaryCell Z l w k :=
    (finiteBoundaryCell_ordConnected Z l w k).out (hleft j hj) (hright j hj) (hrect j hj).2
  have hlocalI j (hj : j∈S) : Icc (α j) (β j) ⊆ Icc l w :=
    fun z hz => ⟨(hleft j hj).1.1.trans hz.1,hz.2.trans (hright j hj).1.2⟩
  have hleft' j (hj : j∈S) : α j∈finiteBoundaryCell Z (α j) (β j) k :=
    ⟨⟨le_rfl,(hrect j hj).2.1.trans (hrect j hj).2.2⟩,(hleft j hj).2⟩
  have hright' j (hj : j∈S) : β j∈finiteBoundaryCell Z (α j) (β j) k :=
    ⟨⟨(hrect j hj).2.1.trans (hrect j hj).2.2,le_rfl⟩,(hright j hj).2⟩
  have hsource j (hj : j∈S) :
      |iteratedDeriv 2 g (y j)-iteratedDeriv 2 hq (y j)| ≤ U ∧
      |(ac-round (ac-deriv φ (y j)))*y j+
        (bc-round (bc-φ (y j)+y j*deriv φ (y j)))-g (y j)+hq (y j)| ≤
        D/(p j).2 := by
    have hαβ : α j ≤ β j := (hrect j hj).2.1.trans (hrect j hj).2.2
    rcases hnum j hj with hpos | hneg
    · have hαpos : 0 < α j := div_pos hpos (hdw j hj)
      have hβpos : 0 < β j := hαpos.trans_le hαβ
      have hmax : max |α j| |β j|=β j := by
        rw [abs_of_pos hαpos,abs_of_pos hβpos,max_eq_right hαβ]
      have hlarge' := hlarge j hj
      dsimp only [Saux] at hlarge'
      rw [ite_eq_left hαpos,hmax] at hlarge'
      exact physicalModelPhase_actual_fourier_original_seed_bounds_all_positive_slopes
        Q K₀ (rat j) (vinv j) (parity j) Mat (anchor j) e r v s
        hσ hδ hF hT hM hN hRpos hQ hscale hmesh hA hW (hx j hj)
        (hden j hj) (hinv j hj) (hlevel j hj) (hcolor j hj) (hnear j hj)
        hsmall hNR hRN hNcube hminscale hMatdet (hMatt j hj) (hMatmap j hj) hMatgamma
        hNtwo (hL j hj) (hU j hj) hchart (hdl j hj) (hdw j hj) hpos
        (hdyad j hj) (hanchor j hj) (hcut j hj) (hcount j hj)
        hMone hR hRM hNscale hd hΔ hrp hxref href (hbudget j hj)
        (fun z hz i => (hdenregion z (hlocalI j hj hz) i).1)
        (hleft' j hj) (hright' j hj) hlarge'
    · have hβneg : β j < 0 := div_neg_of_neg_of_pos hneg (hdl j hj)
      have hαneg : α j < 0 := hαβ.trans_lt hβneg
      have hmax : max |α j| |β j|= -α j := by
        rw [abs_of_neg hαneg,abs_of_neg hβneg,max_eq_left (neg_le_neg hαβ)]
      have hlarge' := hlarge j hj
      dsimp only [Saux] at hlarge'
      rw [ite_eq_right (not_lt.mpr hαneg.le),hmax] at hlarge'
      exact physicalModelPhase_actual_fourier_original_seed_bounds_all_negative_slopes
        Q K₀ (rat j) (vinv j) (parity j) Mat (anchor j) e r v s
        hσ hδ hF hT hM hN hRpos hQ hscale hmesh hA hW (hx j hj)
        (hden j hj) (hinv j hj) (hlevel j hj) (hcolor j hj) (hnear j hj)
        hsmall hNR hRN hNcube hminscale hMatdet (hMatt j hj) (hMatmap j hj) hMatgamma
        hNtwo (hL j hj) (hU j hj) hchart (hdl j hj) (hdw j hj) hneg
        (hdyad j hj) (hanchor j hj) (hcut j hj) (hcount j hj)
        hMone hR hRM hNscale hd hΔ hrp hxref href (hbudget j hj)
        (fun z hz i => (hdenregion z (hlocalI j hj hz) i).1)
        (hleft' j hj) (hright' j hj) hlarge'
  have hchartR : (v:ℝ)*r-e*s=1 := by exact_mod_cast hchart
  have hdetp i : vp i*rp i-ep i*sp i=1 := by
    fin_cases i
    · exact hchart
    · change (Mat 0*v+Mat 1*s)*(Mat 2*e+Mat 3*r)-
        (Mat 0*e+Mat 1*r)*(Mat 2*v+Mat 3*s)=1
      linear_combination (v*r-e*s)*hMatdet+hchart
  have hcoordinates j (hj : j∈S) :
      (∀ i, (rp i:ℝ)*(p j).1+sp i*(p j).2=(q j i:ℝ)) ∧
      (∀ i, iteratedDeriv 2 (f i) (x j i)/2=
        ((ep i:ℝ)*(p j).1+vp i*(p j).2)/((rp i:ℝ)*(p j).1+sp i*(p j).2)) := by
    have hc := farey_matrix_original_seed_coordinates (rat j) Mat e r v s
      hchart (hMatt j hj) (hMatmap j hj)
    refine ⟨fun i => (hc i).1,?_⟩
    intro i
    rw [(hc i).1,(hc i).2,hlevel j hj]
    exact Rat.cast_def _
  have hpoint j (hj : j∈S) i := (hcoordinates j hj).2 i
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans
    (approximateModelPhase_iteratedDeriv_error (hF 0)
      (by norm_num : (3/2:ℝ)∈Ioo 1 2) 4 le_rfl)
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hC₄ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ0
  have hCR : 0 ≤ quarticReciprocalConstant σ δ := by
    dsimp only [quarticReciprocalConstant]; positivity
  have hCcurv : 0 ≤ Ccurv := by dsimp only [Ccurv]; positivity
  let Cres := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
  have hCres : 0 ≤ Cres := by
    dsimp only [Cres,Cc,Ct,C₂,C₃,quarticNonlinearResidualConstant]
    positivity
  have hDeq : D=Cres*(Q:ℝ)/N := by dsimp only [D,Δ,Cres]; ring
  have hD₀ : 0 ≤ D := by
    rw [hDeq]
    exact div_nonneg (mul_nonneg hCres (Nat.cast_nonneg Q)) hN.le
  have hVheight : 0 ≤ Vheight := div_nonneg
    (mul_nonneg hT.le (add_nonneg (modelPhaseJetCoefficient_nonneg σ 1) hδ0))
    (by positivity)
  have hP₂ : 0 < P₂ := add_pos_of_pos_of_nonneg zero_lt_one
    (mul_nonneg (add_nonneg (mul_nonneg (abs_nonneg _) hVheight) (abs_nonneg _))
      (Nat.cast_nonneg Q))
  have hpheight j (hj : j∈S) :
      |((p j).1:ℝ)| ≤ P₁ ∧ ((p j).2:ℝ) ≤ P₂ := by
    have hxj : x j 0∈Ioo 0 (W 0) :=
      ⟨by linarith only [(hx j hj 0).1],by linarith only [(hx j hj 0).2]⟩
    have hh := physicalModelPhase_original_seed_coordinate_heights (rat j 0) Q e r v s
      hσ.le (hF 0) (by norm_num : 1 ≤ 4) hT hM (hA 0) (hW 0)
      hxj (hden j hj 0).1 (hlevel j hj 0)
    exact ⟨hh.1.trans (le_add_of_nonneg_left zero_le_one),
      (le_abs_self _).trans (hh.2.trans (le_add_of_nonneg_left zero_le_one))⟩
  have hpband j (hj : j∈S) :
      (Q:ℝ) ≤ 2*((rp 0:ℝ)*(p j).1+sp 0*(p j).2) := by
    rw [(hcoordinates j hj).1 0]
    exact_mod_cast (hden j hj 0).2
  obtain ⟨j₀,hj₀⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  obtain ⟨j,z,curve,alpha,beta,hj,hmono,hLp,hNL,hKp,hcurve,hspacing,hres⟩ :=
    physicalModelPhase_signed_height_square_span_quartic_witnesses
    (ac:=ac) (bc:=bc) (y₀:=y j₀) (Ccurv:=Ccurv) (Bcut:=Bcut)
    (Cres:=Cres) (Q:=(Q:ℝ)) (D:=D)
    (e:=fun i => (ep i:ℝ)) (r:=fun i => (rp i:ℝ))
    (v:=fun i => (vp i:ℝ)) (s:=fun i => (sp i:ℝ))
    S p x hS hσ hδ hF hT hM hN hR hd hCres hD₀ hD hDeq.le hscale hA hW hxref
    hpheight (fun j hj => (hrect j hj).1) hpband hx hwindow hdisplacement hspan hsourcesquare
    (fun i => by exact_mod_cast hrp i)
    (fun i => by
      exact_mod_cast hdetp i)
    hdenregion hcoord hP₂ hCcurv hBcut hBsize hGcut
    hpoint (hy j₀ hj₀) hy (hsource j₀ hj₀).1 (fun j hj => (hsource j hj).2)
  refine ⟨j,z,curve,alpha,beta,?_,hmono,hLp,hNL,hKp,hcurve,hspacing,hres⟩
  intro a
  refine ⟨(hj a).1,fun i => ?_⟩
  rw [← hlevel _ (hj a).1 i]
  exact (hj a).2.2 i

                                                                                  
private theorem physicalModelPhase_zero_crossing_window_count
    (S : Finset ℕ) (x : ℕ → ℝ)
    {σ δ T M A W N R base ε e r v s l w : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hA : M ≤ A) (hW : A+W ≤ 2*M) (hphase : T*N*R^2=M^3)
    (hsmall : 4*ε*R^2 ≤ modelPhaseThirdLower σ)
    (hx : ∀ j∈S, x j∈Ioo 0 W)
    (hwindow : ∀ j∈S, x j∈Icc (base+(j:ℝ)*N) (base+((j:ℝ)+1)*N))
    (hregion : ∀ z∈Icc l w, 0 < r*z+s) :
    let f := heathBrownPhysicalPhase F T M A 1
    let q := fun j => iteratedDeriv 2 f (x j)/2
    let α := fun j => (v-s*(q j+ε))/(r*(q j+ε)-e)
    let β := fun j => (v-s*(q j-ε))/(r*(q j-ε)-e)
    (∀ j∈S, 0 < r*(q j-ε)-e ∧ 0 < r*(q j+ε)-e) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    (S.filter (fun j => ¬(0 < α j ∨ β j < 0))).card ≤ 3 := by
  classical
  intro f q α β hcharts hends
  let Z : Finset ℝ := ({0}:Finset ℝ).filter (fun z => z∈Icc l w)
  have hc := physicalModelPhase_farey_boundary_crossing_count S Z x (v:=v)
    hσ hδ hF hT hM hN hR hA hW hphase hsmall hx hwindow
    (fun z hz => hregion z (Finset.mem_filter.mp hz).2) hcharts
  have he : S.filter (fun j => ¬(0 < α j ∨ β j < 0))=
      S.filter (fun j => ∃ z∈Z, z∈Icc (α j) (β j)) := by
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hj,hnot⟩
      have hh := not_or.mp hnot
      have ha : α j ≤ 0 := le_of_not_gt hh.1
      have hb : 0 ≤ β j := le_of_not_gt hh.2
      refine ⟨hj,0,?_,ha,hb⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_singleton_self 0,
        (hends j hj).1.1.trans ha,hb.trans (hends j hj).2.2⟩
    · rintro ⟨hj,z,hz,haz,hzb⟩
      have hz0 : z=0 := Finset.mem_singleton.mp (Finset.mem_filter.mp hz).1
      subst z
      exact ⟨hj,fun hh => hh.elim (not_lt_of_ge haz) (not_lt_of_ge hzb)⟩
  rw [he]
  have hZ : Z.card ≤ 1 := by
    simpa only [Finset.card_singleton] using
      (Finset.card_filter_le (s:=({0}:Finset ℝ)) (p:=fun z => z∈Icc l w))
  exact hc.trans (by omega)


                                                                 
                                                                  
                                                                      
                                                           
private theorem physicalModelPhase_actual_fourier_signed_height_square_span_selected_cell_quartic_witnesses
    {Kcoord : ℕ}
    (S : Finset ℕ) (jref : ℕ) (hjref : jref∈S)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R d nSpan base l w Bcut Lref : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hsourcesquare : nSpan^2 ≤ M*R)
    (hden : ∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den)
    (hinv : ∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1)
    (hchart : v*r-e*s=1) (hr : r ≠ 0)
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ (Kcoord:ℝ)*d) (hBcut : 0 < Bcut)
    (hLref : 0 < Lref) (hrefWindow : modelPhaseThirdLower σ*Lref*R^2 ≤ 24*N^2)
    (hwideL : ∀ i, x jref i-Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ i, x jref i+Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hrefNear : |(e:ℝ)/r-(rat jref 0:ℝ)| ≤ modelPhaseThirdLower σ*Lref/(16*R^2)) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    99+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card →
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
    let ε := κ/(16*(Cphys+2)*R^2)
    2 ≤ N →
    (∀ j∈S, ∀ i, x j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, ∀ i, x j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, 0 < (r:ℝ)*((rat j 0:ℝ)-ε)-e) →
    (∀ j∈S, 0 < (r:ℝ)*((rat j 0:ℝ)+ε)-e) →
    (∀ j∈S, max ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e) ≤
      2*min ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e)) →
    (∀ j∈S, |(anchor j:ℝ)-(rat j 0:ℝ)| ≤ ε) →
    (∀ j∈S, 256*((anchor j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ j∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor j).den) →
    let lo := fun j => (rat j 0:ℝ)-ε
    let hi := fun j => (rat j 0:ℝ)+ε
    let α := fun j => ((v:ℝ)-s*hi j)/((r:ℝ)*hi j-e)
    let β := fun j => ((v:ℝ)-s*lo j)/((r:ℝ)*lo j-e)
    let Kaux := fun j => ⌊((Q:ℝ)/3)*min ((r:ℝ)*lo j-e) ((r:ℝ)*hi j-e)⌋₊
    let Saux := fun j => if 0 < α j then HuxleyLinearForm.fareySector (Kaux j) (α j) (β j)
      else (HuxleyLinearForm.fareySector (Kaux j) (-β j) (-α j)).image
        (fun p : ℤ × ℤ => (-p.1,p.2))
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    ∃ xref : Fin 2 → ℝ,
      (∀ i, 0 < rp i*r ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
        |xref i-x jref i| ≤ Lref*N ∧
        |(round (xref i):ℝ)-(round (x jref i):ℝ)| ≤ Lref*N+1) ∧
    ∀ Hspan : Fin 2 → ℝ,
    (∀ j∈S, ∀ i, |x j i-xref i| ≤ Hspan i) →
    (∀ i, 2*Hspan i+1 ≤ nSpan) →
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let G := minorArcCoordinate (μr 0) (rp 0) (sp 0)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*d^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := fun j => D+(Kaux j:ℝ)*Ctay*(β j-α j)^2
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    (∀ j∈S, ∀ i, (H+|x j i-xref i|+1)^2 ≤ M*R) →
    D ≤ 1/2 → Δ < 1/2 →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    (∀ j∈S, (0 < α j ∨ β j < 0) → 3840*128*η j*((max |α j| |β j|)*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    ((2*Kcoord+1:ℕ):ℝ)*Ccurv*Cphys ≤ Bcut →
    |G l| ≤ |(rp 0:ℝ)| *N^2/(Bcut*R^2) →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 99+17*S₀.card ∧
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    let vp : Fin 2 → ℤ := ![v,Mat 0*v+Mat 1*s]
    ∃ j : Fin 8 → ℕ, ∃ z : Fin 8 → ℝ, ∃ curve : ℝ → Fin 2 → ℝ, ∃ alpha beta : ℝ,
      (∀ a, j a∈S₀ ∧ ∀ i,
        (rat (j a) i:ℝ)=((ep i:ℝ)*z a+vp i)/((rp i:ℝ)*z a+sp i)) ∧
      StrictMono z ∧ 0 < L ∧ (L*N)^2 ≤ M*R ∧ 0 ≤ Kres ∧
      (∀ t∈Icc (z 0) (z 7), t∈Icc l w ∧ ∀ i,
        curve t i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        d ≤ (rp i:ℝ)*t+sp i ∧ (rp i:ℝ)*t+sp i ≤ 2*d ∧
        iteratedDeriv 2 (f i) (curve t i)/2=((ep i:ℝ)*t+vp i)/((rp i:ℝ)*t+sp i) ∧
        |(round (curve t i):ℝ)-(round (xref i):ℝ)|^2 ≤ M*R) ∧
      (∀ i : Fin 7, L*N ≤ |G (z i.succ)-G (z i.castSucc)|) ∧
      (∀ i : Fin 8,
        |alpha*z i+beta-rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1) (z i)+
          quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1) (z i)| ≤
          Kres*R^2/|(rp 0:ℝ)*G (z i)|) := by
 classical
  intro Vheight P₁ P₂ hS f hlevel q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H ε hNtwo hL hU hdl hdw hdyad hanchor hcut hcount
    lo hi α β Kaux Saux C₂ C₃ Ct Cc Δ ep rp sp
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hF₂ i := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl
  obtain ⟨xref,hxr⟩ := physicalModelPhase_actual_matrix_reference_roots_signed
    Q K₀ (rat jref) Mat e r hσ hδ hF₂ hT hM hN hRpos hLref hQ hscale hmesh
    hA hW (hx jref hjref) (hden jref hjref) hMatdet hMatgamma hrefWindow hr
    (hlevel jref hjref) (hMatt jref hjref) (hMatmap jref hjref) hwideL hwideU hrefNear
  refine ⟨xref,hxr,?_⟩
  intro Hspan hdisplacement hspan ar μr νr G Ccurv Ctay D η Kres hbudget hD hΔ
    hdenregion hends hlarge hBsize hGcut
  let U := Ccurv*R^4/(N*d^3)
  let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
    (μr 1) (νr 1) (rp 1) (sp 1) U
  have hκp : 0 < κ := modelPhaseThirdLower_pos hσ
  have hchartReal : (v:ℝ)*r-e*s=1 := by exact_mod_cast hchart
  have hεnonneg : 0 ≤ ε := by dsimp only [ε,Cphys]; positivity
  have hεsmall : 4*ε*R^2 ≤ κ := by
    have hCpos : 0 < Cphys+2 := by dsimp only [Cphys]; positivity
    have heq : 4*ε*R^2=κ/(4*(Cphys+2)) := by
      dsimp only [ε]
      field_simp
      ring
    rw [heq]
    apply (div_le_iff₀ (mul_pos (by norm_num) hCpos)).mpr
    have hh : 1 ≤ 4*(Cphys+2) := by
      have hp := mul_nonneg hσ.le (add_nonneg hσ.le zero_le_one)
      dsimp only [Cphys]
      linarith only [hp]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh hκp.le
  obtain ⟨k,Spre,hSpreS,hSprecard,hcellsPre⟩ :=
    physicalModelPhase_farey_common_cell_selection_signed S Z (fun j => x j 0)
      (ε:=ε) (e:=(e:ℝ)) (r:=(r:ℝ)) (v:=(v:ℝ)) (s:=(s:ℝ))
      hσ hδ (hF₂ 0) hT hM hN hRpos (hA 0) (hW 0) hscale hεsmall hεnonneg
      hchartReal
      (quarticCurvatureBoundaryRoots_card (μr 0) (νr 0) (rp 0) (sp 0)
        (μr 1) (νr 1) (rp 1) (sp 1) U)
      (fun j hj => ⟨by linarith only [(hx j hj 0).1],by linarith only [(hx j hj 0).2]⟩)
      (fun j hj => by simpa only [mul_comm] using hwindow j hj)
      (fun z hz => by
        have hh := (hdenregion z hz 0).1
        change d ≤ (r:ℝ)*z+s at hh
        exact hd.trans_le hh)
      (by
        intro j hj
        change 0 < (r:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2-ε)-e ∧
          0 < (r:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2+ε)-e
        rw [hlevel j hj 0]
        exact ⟨hdl j hj,hdw j hj⟩)
      (by
        intro j hj
        change (v-s*(iteratedDeriv 2 (f 0) (x j 0)/2+ε))/
            (r*(iteratedDeriv 2 (f 0) (x j 0)/2+ε)-e)∈Icc l w ∧
          (v-s*(iteratedDeriv 2 (f 0) (x j 0)/2-ε))/
            (r*(iteratedDeriv 2 (f 0) (x j 0)/2-ε)-e)∈Icc l w
        rw [hlevel j hj 0]
        exact hends j hj)
  let good := fun j => 0 < α j ∨ β j < 0
  have hbad : (S.filter (fun j => ¬good j)).card ≤ 3 := by
    have hh := physicalModelPhase_zero_crossing_window_count S (fun j => x j 0)
      (ε:=ε) (e:=(e:ℝ)) (r:=(r:ℝ)) (v:=(v:ℝ)) (s:=(s:ℝ))
      (l:=l) (w:=w)
      hσ hδ (hF₂ 0) hT hM hN hRpos (hA 0) (hW 0) hscale hεsmall
      (fun j hj => ⟨by linarith only [(hx j hj 0).1],by linarith only [(hx j hj 0).2]⟩)
      (fun j hj => by simpa only [mul_comm] using hwindow j hj)
      (fun z hz => by
        have hz' := (hdenregion z hz 0).1
        change d ≤ (r:ℝ)*z+s at hz'
        exact hd.trans_le hz')
      (by
        intro j hj
        change 0 < (r:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2-ε)-e ∧
          0 < (r:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2+ε)-e
        rw [hlevel j hj 0]
        exact ⟨hdl j hj,hdw j hj⟩)
      (by
        intro j hj
        change (v-s*(iteratedDeriv 2 (f 0) (x j 0)/2+ε))/
            (r*(iteratedDeriv 2 (f 0) (x j 0)/2+ε)-e)∈Icc l w ∧
          (v-s*(iteratedDeriv 2 (f 0) (x j 0)/2-ε))/
            (r*(iteratedDeriv 2 (f 0) (x j 0)/2-ε)-e)∈Icc l w
        rw [hlevel j hj 0]
        exact hends j hj)
    convert hh using 1
    congr 1
    apply Finset.filter_congr
    intro j hj
    dsimp only [good,α,β,lo,hi]
    rw [hlevel j hj 0]
  let S₀ := Spre.filter good
  have hS₀S : S₀⊆S := (Finset.filter_subset _ _).trans hSpreS
  have hS₀card : S.card ≤ 99+17*S₀.card := by
    have hb : (Spre.filter (fun j => ¬good j)).card ≤ 3 := by
      apply le_trans (Finset.card_le_card ?_) hbad
      intro j hj
      exact Finset.mem_filter.mpr ⟨hSpreS (Finset.mem_filter.mp hj).1,
        (Finset.mem_filter.mp hj).2⟩
    have he := Finset.card_filter_add_card_filter_not (s:=Spre) good
    change S₀.card+(Spre.filter (fun j => ¬good j)).card=Spre.card at he
    omega
  have hcells j (hj : j∈S₀) := hcellsPre j (Finset.mem_filter.mp hj).1
  have hS₀ : 32*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S₀.card := by
    apply Nat.le_of_mul_le_mul_left (c:=17) _ (by decide)
    apply Nat.le_of_add_le_add_left (a:=99)
    calc
      _ = 99+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) := by ring
      _ ≤ _ := hS.trans hS₀card
  have hcells' j (hj : j∈S₀) :
      α j∈finiteBoundaryCell Z l w k ∧ β j∈finiteBoundaryCell Z l w k := by
    have hh := hcells j hj
    change (v-s*(iteratedDeriv 2 (f 0) (x j 0)/2+ε))/
        (r*(iteratedDeriv 2 (f 0) (x j 0)/2+ε)-e)∈finiteBoundaryCell Z l w k ∧
      (v-s*(iteratedDeriv 2 (f 0) (x j 0)/2-ε))/
        (r*(iteratedDeriv 2 (f 0) (x j 0)/2-ε)-e)∈finiteBoundaryCell Z l w k at hh
    rw [hlevel j (hS₀S hj) 0] at hh
    exact hh
  refine ⟨S₀,hS₀S,hS₀card,?_⟩
  intro Blabels L vp
  have hx j (hj : j∈S₀) := hx j (hS₀S hj)
  have hwindow j (hj : j∈S₀) := hwindow j (hS₀S hj)
  have hden j (hj : j∈S₀) := hden j (hS₀S hj)
  have hinv j (hj : j∈S₀) := hinv j (hS₀S hj)
  have hlevel j (hj : j∈S₀) := hlevel j (hS₀S hj)
  have hcolor j (hj : j∈S₀) := hcolor j (hS₀S hj)
  have hnear j (hj : j∈S₀) := hnear j (hS₀S hj)
  have hMatt j (hj : j∈S₀) := hMatt j (hS₀S hj)
  have hMatmap j (hj : j∈S₀) := hMatmap j (hS₀S hj)
  have hL j (hj : j∈S₀) := hL j (hS₀S hj)
  have hU j (hj : j∈S₀) := hU j (hS₀S hj)
  have hdl j (hj : j∈S₀) := hdl j (hS₀S hj)
  have hdw j (hj : j∈S₀) := hdw j (hS₀S hj)
  have hnum j (hj : j∈S₀) :
      0 < (v:ℝ)-s*((rat j 0:ℝ)+ε) ∨ (v:ℝ)-s*((rat j 0:ℝ)-ε) < 0 := by
    rcases (Finset.mem_filter.mp hj).2 with hpos | hneg
    · left
      have hh := (lt_div_iff₀ (hdw j hj)).mp hpos
      simpa only [zero_mul] using hh
    · right
      have hh := (div_lt_iff₀ (hdl j hj)).mp hneg
      simpa only [zero_mul] using hh
  have hdyad j (hj : j∈S₀) := hdyad j (hS₀S hj)
  have hanchor j (hj : j∈S₀) := hanchor j (hS₀S hj)
  have hcut j (hj : j∈S₀) := hcut j (hS₀S hj)
  have hcount j (hj : j∈S₀) := hcount j (hS₀S hj)
  have hdisplacement j (hj : j∈S₀) := hdisplacement j (hS₀S hj)
  have hbudget j (hj : j∈S₀) := hbudget j (hS₀S hj)
  have hlarge j (hj : j∈S₀) := hlarge j (hS₀S hj) (Finset.mem_filter.mp hj).2
  have hleft j (hj : j∈S₀) := (hcells' j hj).1
  have hright j (hj : j∈S₀) := (hcells' j hj).2
  exact physicalModelPhase_actual_fourier_signed_height_square_span_fixed_reference_quartic_witnesses S₀ Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (k:=k) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcesquare hden hinv hchart hd hcoord hBcut
    hS₀ hlevel hcolor hnear hsmall hNR hRN hNcube hminscale
    hMatdet hMatt hMatmap hMatgamma hNtwo hL hU hdl hdw hnum hdyad
    hanchor hcut hcount xref
    (fun i => ⟨(mul_ne_zero_iff.mp (hxr i).1.ne').1,(hxr i).2.1,(hxr i).2.2.1⟩)
    Hspan hdisplacement hspan hbudget hD hΔ hdenregion hleft hright
    hlarge hBsize hGcut

                                                                                    
theorem physicalModelPhase_actual_fourier_signed_selected_reference_gap_quartic_witnesses
    {Kcoord : ℕ}
    (Uref : ℕ) {Bselect gapLo gapHi : ℝ}
    (S : Finset ℕ) (jref : ℕ) (hjref : jref∈S)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R d base l w Bcut : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hden : ∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den)
    (hinv : ∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1)
    (hchart : v*r-e*s=1) (hr : r ≠ 0)
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ (Kcoord:ℝ)*d) (hBcut : 0 < Bcut)
    (hwideL : ∀ i, x jref i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ i, x jref i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : R^2 ≤ (r:ℝ)^2*(Uref:ℝ))
    (hgapWidth : gapHi-gapLo ≤ 7*(Uref:ℝ)/(2*R^2))
    (hreferenceEndpoint : (e:ℝ)/r=gapLo ∨ (e:ℝ)/r=gapHi)
    (hchartLeft : ((e:ℝ)*l+v)/((r:ℝ)*l+s)∈Icc gapLo gapHi)
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ j∈S, (rat j 0:ℝ)∈Icc gapLo gapHi) :
    let Lref := 56*(Uref:ℝ)/modelPhaseThirdLower σ
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    99+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card →
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
    let ε := κ/(16*(Cphys+2)*R^2)
    2 ≤ N →
    (∀ j∈S, ∀ i, x j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, ∀ i, x j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, 0 < (r:ℝ)*((rat j 0:ℝ)-ε)-e) →
    (∀ j∈S, 0 < (r:ℝ)*((rat j 0:ℝ)+ε)-e) →
    (∀ j∈S, max ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e) ≤
      2*min ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e)) →
    (∀ j∈S, |(anchor j:ℝ)-(rat j 0:ℝ)| ≤ ε) →
    (∀ j∈S, 256*((anchor j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ j∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor j).den) →
    let lo := fun j => (rat j 0:ℝ)-ε
    let hi := fun j => (rat j 0:ℝ)+ε
    let α := fun j => ((v:ℝ)-s*hi j)/((r:ℝ)*hi j-e)
    let β := fun j => ((v:ℝ)-s*lo j)/((r:ℝ)*lo j-e)
    let Kaux := fun j => ⌊((Q:ℝ)/3)*min ((r:ℝ)*lo j-e) ((r:ℝ)*hi j-e)⌋₊
    let Saux := fun j => if 0 < α j then HuxleyLinearForm.fareySector (Kaux j) (α j) (β j)
      else (HuxleyLinearForm.fareySector (Kaux j) (-β j) (-α j)).image
        (fun p : ℤ × ℤ => (-p.1,p.2))
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    ∃ xref : Fin 2 → ℝ,
      (∀ i, 0 < rp i*r ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
        |xref i-x jref i| ≤ Lref*N ∧
        |(round (xref i):ℝ)-(round (x jref i):ℝ)| ≤ Lref*N+1) ∧
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*d^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := fun j => D+(Kaux j:ℝ)*Ctay*(β j-α j)^2
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    D ≤ 1/2 → Δ < 1/2 →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    (∀ j∈S, (0 < α j ∨ β j < 0) → 3840*128*η j*((max |α j| |β j|)*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    ((2*Kcoord+1:ℕ):ℝ)*Ccurv*Cphys ≤ Bcut →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 99+17*S₀.card ∧
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let G := minorArcCoordinate (μr 0) (rp 0) (sp 0)
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    let vp : Fin 2 → ℤ := ![v,Mat 0*v+Mat 1*s]
    ∃ j : Fin 8 → ℕ, ∃ z : Fin 8 → ℝ, ∃ curve : ℝ → Fin 2 → ℝ, ∃ alpha beta : ℝ,
      (∀ a, j a∈S₀ ∧ ∀ i,
        (rat (j a) i:ℝ)=((ep i:ℝ)*z a+vp i)/((rp i:ℝ)*z a+sp i)) ∧
      StrictMono z ∧ 0 < L ∧ (L*N)^2 ≤ M*R ∧ 0 ≤ Kres ∧
      (∀ t∈Icc (z 0) (z 7), t∈Icc l w ∧ ∀ i,
        curve t i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        d ≤ (rp i:ℝ)*t+sp i ∧ (rp i:ℝ)*t+sp i ≤ 2*d ∧
        iteratedDeriv 2 (f i) (curve t i)/2=((ep i:ℝ)*t+vp i)/((rp i:ℝ)*t+sp i) ∧
        |(round (curve t i):ℝ)-(round (xref i):ℝ)|^2 ≤ M*R) ∧
      (∀ i : Fin 7, L*N ≤ |G (z i.succ)-G (z i.castSucc)|) ∧
      (∀ i : Fin 8,
        |alpha*z i+beta-rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1) (z i)+
          quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1) (z i)| ≤
          Kres*R^2/|(rp 0:ℝ)*G (z i)|) := by
 classical
  intro Lref
  have hκearly : 0 < modelPhaseThirdLower σ := modelPhaseThirdLower_pos hσ
  have hUone : (1:ℝ) ≤ Uref := by exact_mod_cast hUref
  have hUp : (0:ℝ) < Uref := zero_lt_one.trans_le hUone
  have hBtwo : 2 ≤ Bselect := by
    have hp : 0 < 168/modelPhaseThirdLower σ := by positivity
    linarith only [hBselectSize,hp]
  have hBselect : 0 < Bselect := lt_of_lt_of_le (by norm_num) hBtwo
  have hLref : 0 < Lref := by dsimp only [Lref]; positivity
  have hspanMargin :
      2*Lref+56*(Uref:ℝ)/modelPhaseThirdLower σ+2 ≤ Bselect*(Uref:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hBselectSize hUp.le
    have he : (2+168/modelPhaseThirdLower σ)*(Uref:ℝ)=
        2*(Uref:ℝ)+2*Lref+56*(Uref:ℝ)/modelPhaseThirdLower σ := by
      dsimp only [Lref]
      ring
    rw [he] at hh
    linarith only [hh,hUone]
  have hrefWindow : modelPhaseThirdLower σ*Lref*R^2 ≤ 24*N^2 := by
    have hBsq : (4:ℝ) ≤ Bselect^2 := by nlinarith only [hBtwo]
    have hUsq : (1:ℝ) ≤ (Uref:ℝ)^2 := by
      simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hUone 2
    have hUcube : (Uref:ℝ) ≤ (Uref:ℝ)^3 := by
      have hh := mul_le_mul_of_nonneg_right hUsq hUp.le
      nlinarith only [hh]
    have hscaled : 4*(Uref:ℝ)*R^2 ≤ N^2 := by
      apply le_trans _ hselectedWrap
      calc
        _ ≤ Bselect^2*(Uref:ℝ)*R^2 := by gcongr
        _ ≤ Bselect^2*(Uref:ℝ)^3*R^2 := by gcongr
    have he : modelPhaseThirdLower σ*Lref*R^2=56*(Uref:ℝ)*R^2 := by
      dsimp only [Lref]
      field_simp
    rw [he]
    nlinarith only [hscaled,sq_nonneg N]
  have hrefNear : |(e:ℝ)/r-(rat jref 0:ℝ)| ≤
      modelPhaseThirdLower σ*Lref/(16*R^2) := by
    have hinside := hfamilyGap jref hjref
    have hdist : |(e:ℝ)/r-(rat jref 0:ℝ)| ≤ gapHi-gapLo := by
      rcases hreferenceEndpoint with he | he
      · rw [he,abs_of_nonpos (sub_nonpos.mpr hinside.1)]
        linarith only [hinside.2]
      · rw [he,abs_of_nonneg (sub_nonneg.mpr hinside.2)]
        linarith only [hinside.1]
    apply (hdist.trans hgapWidth).trans
    apply le_of_eq
    dsimp only [Lref]
    field_simp
    ring
  let nSpan := Bselect*(Uref:ℝ)*N
  have hsourcesquare : nSpan^2 ≤ M*R :=
    source_selected_reference_square_span_budget Uref hM hN (zero_lt_one.trans_le hR)
      hRQ hBselect hselectedUpper hscaleTen
  intro Vheight P₁ P₂ hS
  have hlong := physicalModelPhase_actual_fourier_signed_height_square_span_selected_cell_quartic_witnesses S jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (Lref:=Lref) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcesquare hden hinv hchart hr hd hcoord hBcut hLref hrefWindow hwideL hwideU hrefNear
  intro f hlevel q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H ε hNtwo hL hU hdl hdw hdyad hanchor hcut hcount
    lo hi α β Kaux Saux C₂ C₃ Ct Cc Δ ep rp sp
  obtain ⟨xref,hxr,hconsumer⟩ := hlong hS hlevel hcolor hnear
    hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    hNtwo hL hU hdl hdw hdyad hanchor hcut hcount
  clear hlong
  refine ⟨xref,hxr,?_⟩
  intro Ccurv Ctay D η Kres hD hΔ hdenregion hends hsector hBsize
  let G := minorArcCoordinate (iteratedDeriv 3 (f 0) (round (xref 0))/6) (rp 0) (sp 0)
  have hlw : l ≤ w := (hends jref hjref).1.1.trans (hends jref hjref).1.2
  have hchartLeftPos : 0 < (r:ℝ)*l+s :=
    hd.trans_le (hdenregion l ⟨le_rfl,hlw⟩ 0).1
  have hbase : iteratedDeriv 2 (f 0) (xref 0)/2=(e:ℝ)/r := (hxr 0).2.2.1
  have hGcut : |G l| ≤ |(rp 0:ℝ)| *N^2/(Bcut*R^2) := by
    exact physicalModelPhase_reference_gap_minorArc_cutoff hσ hδ
      (approximateModelPhase_mono (hF 0) (by norm_num : 2 ≤ 4) le_rfl)
      hT hM (hA 0) (hW 0) (hxr 0).2.1 hN (zero_lt_one.trans_le hR)
      (Nat.cast_nonneg Uref) hBselect hBcut hscale hcutMargin
      (by exact_mod_cast hr) hchartLeftPos.ne' (by exact_mod_cast hchart)
      hgapWidth hreferenceDen hselectedWrap hchartLeft hbase
      (by rw [hbase]; exact hreferenceEndpoint)
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hpair (j : ℕ) (hj : j∈S) (i : Fin 2) :
      |x j i-x jref i| ≤ 28*(Uref:ℝ)*N/κ := by
    exact physicalModelPhase_actual_matrix_gap_displacement Q (rat jref) (rat j) Mat
      hσ hδ (fun i => approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl)
      hT hM hN (zero_lt_one.trans_le hR) (Nat.cast_nonneg Uref) hA hW
      (fun i => ⟨by linarith only [(hx jref hjref i).1],
        by linarith only [(hx jref hjref i).2]⟩)
      (fun i => ⟨by linarith only [(hx j hj i).1],
        by linarith only [(hx j hj i).2]⟩)
      hscale (hden jref hjref) (hden j hj) hMatdet
      (hMatt jref hjref) (hMatt j hj) (hMatmap jref hjref) (hMatmap j hj)
      hgapWidth (hfamilyGap jref hjref) (hfamilyGap j hj)
      (hlevel jref hjref) (hlevel j hj) i
  let span := (Lref+28*(Uref:ℝ)/κ)*N
  have hspan0 : 0 ≤ span := by dsimp only [span]; positivity
  have hdisplacement (j : ℕ) (hj : j∈S) (i : Fin 2) :
      |x j i-xref i| ≤ span := by
    calc
      _ ≤ |x j i-x jref i|+|x jref i-xref i| := abs_sub_le _ _ _
      _ ≤ 28*(Uref:ℝ)*N/κ+Lref*N := by
        apply add_le_add (hpair j hj i)
        rw [abs_sub_comm]
        exact (hxr i).2.2.2.1
      _ = span := by dsimp only [span]; ring
  have hspanBuffer : 2*span+2*N ≤ nSpan := by
    have hh := mul_le_mul_of_nonneg_right hspanMargin hN.le
    change (2*Lref+56*(Uref:ℝ)/κ+2)*N ≤ nSpan at hh
    have he : (2*Lref+56*(Uref:ℝ)/κ+2)*N=2*span+2*N := by
      dsimp only [span]
      ring
    rwa [he] at hh
  have hspan : 2*span+1 ≤ nSpan := by
    linarith only [hspanBuffer,hNtwo]
  have hHN : H ≤ N := by
    apply (div_le_iff₀ (show 0 < Cphys+2 by dsimp only [Cphys]; positivity)).mpr
    have hh : 1 ≤ Cphys+2 := by
      have hp := mul_nonneg hσ.le (add_nonneg hσ.le zero_le_one)
      dsimp only [Cphys]
      linarith only [hp]
    simpa only [one_mul,mul_one,mul_comm] using mul_le_mul_of_nonneg_right hh hN.le
  have hbudget (j : ℕ) (hj : j∈S) (i : Fin 2) :
      (H+|x j i-xref i|+1)^2 ≤ M*R := by
    have hH0 : 0 ≤ H := by dsimp only [H,Cphys]; positivity
    have hb : H+|x j i-xref i|+1 ≤ nSpan := by
      linarith only [hdisplacement j hj i,hspanBuffer,hHN,hspan0,hNtwo]
    exact (pow_le_pow_left₀ (by positivity) hb 2).trans hsourcesquare
  exact hconsumer (fun _ => span) hdisplacement (fun _ => hspan)
    hbudget hD hΔ hdenregion hends hsector hBsize hGcut

                                                         
private theorem separated_farey_reference_chart_coordinate_bound
    (S : Finset ℝ) {δ a b e r v s z d : ℝ}
    (hr : r ≠ 0) (hs : s ≠ 0)
    (hdet : v*r-e*s=1)
    (href : e/r∈S) (hparent : v/s∈S)
    (hsep : ∀ x∈S, ∀ y∈S, x ≠ y → δ/4 < |x-y|)
    (hgap : b-a ≤ 7*δ/2)
    (hendpoint : e/r=a ∨ e/r=b)
    (hd : 0 < d) (hden : d ≤ r*z+s ∧ r*z+s ≤ 2*d)
    (hpoint : (e*z+v)/(r*z+s)∈Icc a b) :
    |r| * |z| ≤ 30*d := by
  let D := r*z+s
  let ξ := (e*z+v)/D
  have hD : 0 < D := hd.trans_le hden.1
  have hprod : 0 < |r*s| := abs_pos.mpr (mul_ne_zero hr hs)
  have hparentGap : |v/s-e/r|=1/|r*s| := by
    rw [div_sub_div _ _ hs hr,abs_div]
    have he : v*r-s*e=1 := by nlinarith only [hdet]
    rw [he,abs_one,mul_comm s r]
  have hne : v/s ≠ e/r := by
    apply sub_ne_zero.mp
    apply abs_pos.mp
    rw [hparentGap]
    exact one_div_pos.mpr hprod
  have hseparated := hsep _ hparent _ href hne
  rw [hparentGap] at hseparated
  have hproduct : δ*|r*s| < 4 := by
    have hh := (lt_div_iff₀ hprod).mp hseparated
    nlinarith only [hh]
  have hdist : |ξ-e/r| ≤ 7*δ/2 := by
    apply le_trans _ hgap
    rcases hendpoint with ha | hb
    · rw [ha,abs_of_nonneg (sub_nonneg.mpr hpoint.1)]
      linarith only [hpoint.2]
    · rw [hb,abs_of_nonpos (sub_nonpos.mpr hpoint.2)]
      linarith only [hpoint.1]
  have hfactor : |r*s| * |ξ-e/r| ≤ 14 := by
    have hh := mul_le_mul_of_nonneg_left hdist hprod.le
    nlinarith only [hh,hproduct]
  have hid : (r*s)*(ξ-e/r)*D=s := by
    dsimp only [ξ]
    field_simp
    dsimp only [D]
    nlinarith only [hdet]
  have hsbound : |s| ≤ 14*D := by
    rw [←hid,abs_mul,abs_mul,abs_of_pos hD]
    exact mul_le_mul_of_nonneg_right hfactor hD.le
  calc
    |r| * |z| = |D-s| := by rw [←abs_mul]; congr 1; dsimp only [D]; ring
    _ ≤ |D|+|s| := abs_sub _ _
    _ = D+|s| := by rw [abs_of_pos hD]
    _ ≤ 15*D := by linarith only [hsbound]
    _ ≤ 30*d := by linarith only [hden.2]

                                                                    
                                                             
theorem separated_farey_reference_interval_coordinate_bound
    (S : Finset ℝ) {δ a b e r v s l w d : ℝ}
    (hr : r ≠ 0) (hs : s ≠ 0) (hdet : v*r-e*s=1)
    (href : e/r∈S) (hparent : v/s∈S)
    (hsep : ∀ x∈S, ∀ y∈S, x ≠ y → δ/4 < |x-y|)
    (hgap : b-a ≤ 7*δ/2) (hendpoint : e/r=a ∨ e/r=b)
    (hd : 0 < d)
    (hdenl : d ≤ r*l+s ∧ r*l+s ≤ 2*d)
    (hdenw : d ≤ r*w+s ∧ r*w+s ≤ 2*d)
    (hleft : (e*l+v)/(r*l+s)∈Icc a b)
    (hright : (e*w+v)/(r*w+s)∈Icc a b) :
    |r| * max |l| |w| ≤ 30*d := by
  rw [mul_max_of_nonneg _ _ (abs_nonneg r)]
  exact max_le
    (separated_farey_reference_chart_coordinate_bound S hr hs hdet href hparent
      hsep hgap hendpoint hd hdenl hleft)
    (separated_farey_reference_chart_coordinate_bound S hr hs hdet href hparent
      hsep hgap hendpoint hd hdenw hright)

                                                                        
                                                                      
                                                                    
                                                          
private theorem physicalModelPhase_actual_fourier_separated_reference_gap_quartic_witnesses
    (Uref : ℕ) (Refs : Finset ℝ) {Bselect gapLo gapHi : ℝ}
    (S : Finset ℕ) (jref : ℕ) (hjref : jref∈S)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R d base l w Bcut : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hden : ∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den)
    (hinv : ∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1)
    (hchart : v*r-e*s=1) (hr : r ≠ 0)
    (hd : 0 < d) (hBcut : 0 < Bcut)
    (hs : s ≠ 0)
    (hrefSet : (e:ℝ)/r∈Refs) (hparentSet : (v:ℝ)/s∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hdenl : d ≤ (r:ℝ)*l+s ∧ (r:ℝ)*l+s ≤ 2*d)
    (hdenw : d ≤ (r:ℝ)*w+s ∧ (r:ℝ)*w+s ≤ 2*d)
    (hwideL : ∀ i, x jref i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ i, x jref i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : R^2 ≤ (r:ℝ)^2*(Uref:ℝ))
    (hgapWidth : gapHi-gapLo ≤ 7*(Uref:ℝ)/(2*R^2))
    (hreferenceEndpoint : (e:ℝ)/r=gapLo ∨ (e:ℝ)/r=gapHi)
    (hchartLeft : ((e:ℝ)*l+v)/((r:ℝ)*l+s)∈Icc gapLo gapHi)
    (hchartRight : ((e:ℝ)*w+v)/((r:ℝ)*w+s)∈Icc gapLo gapHi)
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ j∈S, (rat j 0:ℝ)∈Icc gapLo gapHi) :
    let Lref := 56*(Uref:ℝ)/modelPhaseThirdLower σ
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    99+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card →
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
    let ε := κ/(16*(Cphys+2)*R^2)
    2 ≤ N →
    (∀ j∈S, ∀ i, x j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, ∀ i, x j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, 0 < (r:ℝ)*((rat j 0:ℝ)-ε)-e) →
    (∀ j∈S, 0 < (r:ℝ)*((rat j 0:ℝ)+ε)-e) →
    (∀ j∈S, max ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e) ≤
      2*min ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e)) →
    (∀ j∈S, |(anchor j:ℝ)-(rat j 0:ℝ)| ≤ ε) →
    (∀ j∈S, 256*((anchor j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ j∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor j).den) →
    let lo := fun j => (rat j 0:ℝ)-ε
    let hi := fun j => (rat j 0:ℝ)+ε
    let α := fun j => ((v:ℝ)-s*hi j)/((r:ℝ)*hi j-e)
    let β := fun j => ((v:ℝ)-s*lo j)/((r:ℝ)*lo j-e)
    let Kaux := fun j => ⌊((Q:ℝ)/3)*min ((r:ℝ)*lo j-e) ((r:ℝ)*hi j-e)⌋₊
    let Saux := fun j => if 0 < α j then HuxleyLinearForm.fareySector (Kaux j) (α j) (β j)
      else (HuxleyLinearForm.fareySector (Kaux j) (-β j) (-α j)).image
        (fun p : ℤ × ℤ => (-p.1,p.2))
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    ∃ xref : Fin 2 → ℝ,
      (∀ i, 0 < rp i*r ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
        |xref i-x jref i| ≤ Lref*N ∧
        |(round (xref i):ℝ)-(round (x jref i):ℝ)| ≤ Lref*N+1) ∧
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*d^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := fun j => D+(Kaux j:ℝ)*Ctay*(β j-α j)^2
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    D ≤ 1/2 → Δ < 1/2 →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    (∀ j∈S, (0 < α j ∨ β j < 0) → 3840*128*η j*((max |α j| |β j|)*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    61*Ccurv*Cphys ≤ Bcut →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 99+17*S₀.card ∧
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let G := minorArcCoordinate (μr 0) (rp 0) (sp 0)
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    let vp : Fin 2 → ℤ := ![v,Mat 0*v+Mat 1*s]
    ∃ j : Fin 8 → ℕ, ∃ z : Fin 8 → ℝ, ∃ curve : ℝ → Fin 2 → ℝ, ∃ alpha beta : ℝ,
      (∀ a, j a∈S₀ ∧ ∀ i,
        (rat (j a) i:ℝ)=((ep i:ℝ)*z a+vp i)/((rp i:ℝ)*z a+sp i)) ∧
      StrictMono z ∧ 0 < L ∧ (L*N)^2 ≤ M*R ∧ 0 ≤ Kres ∧
      (∀ t∈Icc (z 0) (z 7), t∈Icc l w ∧ ∀ i,
        curve t i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        d ≤ (rp i:ℝ)*t+sp i ∧ (rp i:ℝ)*t+sp i ≤ 2*d ∧
        iteratedDeriv 2 (f i) (curve t i)/2=((ep i:ℝ)*t+vp i)/((rp i:ℝ)*t+sp i) ∧
        |(round (curve t i):ℝ)-(round (xref i):ℝ)|^2 ≤ M*R) ∧
      (∀ i : Fin 7, L*N ≤ |G (z i.succ)-G (z i.castSucc)|) ∧
      (∀ i : Fin 8,
        |alpha*z i+beta-rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1) (z i)+
          quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1) (z i)| ≤
          Kres*R^2/|(rp 0:ℝ)*G (z i)|) := by
  have hcoord : |(r:ℝ)| * max |l| |w| ≤ 30*d :=
    separated_farey_reference_interval_coordinate_bound Refs
      (δ:=(Uref:ℝ)/R^2) (by exact_mod_cast hr) (by exact_mod_cast hs)
      (by exact_mod_cast hchart) hrefSet hparentSet hsep
      (hgapWidth.trans_eq (by ring)) hreferenceEndpoint hd hdenl hdenw
      hchartLeft hchartRight
  exact physicalModelPhase_actual_fourier_signed_selected_reference_gap_quartic_witnesses (Kcoord:=30) Uref (Bselect:=Bselect) (gapLo:=gapLo) (gapHi:=gapHi) S jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hinv hchart hr hd hcoord hBcut hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hreferenceEndpoint hchartLeft hRQ hselectedUpper hscaleTen hfamilyGap

                                                             
private theorem affine_endpoint_factor_two
    {r e q ε : ℝ} (hε : 0 ≤ ε)
    (hcentral : 3*|r| *ε < r*q-e) :
    0 < r*(q-ε)-e ∧ 0 < r*(q+ε)-e ∧
      max (r*(q-ε)-e) (r*(q+ε)-e) ≤
        2*min (r*(q-ε)-e) (r*(q+ε)-e) := by
  have hsmall : 0 ≤ |r| *ε := mul_nonneg (abs_nonneg r) hε
  have hlo := mul_le_mul_of_nonneg_right (neg_abs_le r) hε
  have hhi := mul_le_mul_of_nonneg_right (le_abs_self r) hε
  have hlow : 0 < r*(q-ε)-e := by nlinarith only [hcentral,hsmall,hhi]
  have hupp : 0 < r*(q+ε)-e := by nlinarith only [hcentral,hsmall,hlo]
  refine ⟨hlow,hupp,?_⟩
  rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
  apply max_le
  · apply le_min
    · linarith only [hlow]
    · nlinarith only [hcentral,hlo]
  · apply le_min
    · nlinarith only [hcentral,hhi]
    · linarith only [hupp]

                                                                     
                                                                 
                                                                  
                                                                      
theorem physicalModelPhase_reference_gap_interior_chart_selection
    (S : Finset ℕ) (x : ℕ → ℝ)
    {σ δ T M A W N R base a b e r : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hphase : T*N*R^2=M^3)
    (horientation : (0 < r ∧ e/r=a) ∨ (r < 0 ∧ e/r=b))
    (hx : ∀ j∈S, x j∈Ioo 0 W)
    (hwindow : ∀ j∈S, x j∈Icc (base+(j:ℝ)*N) (base+((j:ℝ)+1)*N)) :
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let f := heathBrownPhysicalPhase F T M A 1
    let q := fun j => iteratedDeriv 2 f (x j)/2
    (∀ j∈S, q j∈Icc a b) →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 6+S₀.card ∧ ∀ j∈S₀,
      a+3*ε < q j ∧ q j < b-3*ε ∧
      0 < r*(q j-ε)-e ∧ 0 < r*(q j+ε)-e ∧
      max (r*(q j-ε)-e) (r*(q j+ε)-e) ≤
        2*min (r*(q j-ε)-e) (r*(q j+ε)-e) ∧
      Icc (q j-ε) (q j+ε) ⊆ Icc a b := by
  classical
  intro ε f q hgap
  have hκ : 0 < modelPhaseThirdLower σ := modelPhaseThirdLower_pos hσ
  have hC : 0 < σ*(σ+1)+3 := by positivity
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  let badA := S.filter (fun j => |q j-a| ≤ 3*ε)
  let badB := S.filter (fun j => |q j-b| ≤ 3*ε)
  let bad := fun j => |q j-a| ≤ 3*ε ∨ |q j-b| ≤ 3*ε
  let good := S.filter (fun j => ¬ bad j)
  have hrad : 4*(3*ε)*R^2 ≤ modelPhaseThirdLower σ := by
    have he : 4*(3*ε)*R^2=3*modelPhaseThirdLower σ/(4*(σ*(σ+1)+3)) := by
      dsimp only [ε]
      field_simp
      ring
    rw [he]
    apply (div_le_iff₀ (mul_pos (by norm_num) hC)).mpr
    have hh : 0 ≤ (σ*(σ+1))*modelPhaseThirdLower σ := by positivity
    nlinarith only [hh,hκ]
  have hcountA : badA.card ≤ 3 :=
    physicalModelPhase_curvature_boundary_window_count badA x
      hσ hδ hF hT hM hN hR hA hW hphase hrad
      (fun j hj => hx j (Finset.mem_filter.mp hj).1)
      (fun j hj => hwindow j (Finset.mem_filter.mp hj).1)
      (fun j hj => (Finset.mem_filter.mp hj).2)
  have hcountB : badB.card ≤ 3 :=
    physicalModelPhase_curvature_boundary_window_count badB x
      hσ hδ hF hT hM hN hR hA hW hphase hrad
      (fun j hj => hx j (Finset.mem_filter.mp hj).1)
      (fun j hj => hwindow j (Finset.mem_filter.mp hj).1)
      (fun j hj => (Finset.mem_filter.mp hj).2)
  have he : S.filter bad=badA∪badB := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_union,bad,badA,badB]
    tauto
  have hbad : (S.filter bad).card ≤ 6 := by
    rw [he]
    exact (Finset.card_union_le _ _).trans (by omega)
  refine ⟨good,Finset.filter_subset _ _,?_,?_⟩
  · have hh := Finset.card_filter_add_card_filter_not (s:=S) bad
    change (S.filter bad).card+good.card=S.card at hh
    omega
  · intro j hj
    obtain ⟨hjS,hgood⟩ := Finset.mem_filter.mp hj
    have hleft : 3*ε < q j-a := by
      have hh : ¬ |q j-a| ≤ 3*ε := fun h => hgood (Or.inl h)
      rw [abs_of_nonneg (sub_nonneg.mpr (hgap j hjS).1)] at hh
      exact lt_of_not_ge hh
    have hright : 3*ε < b-q j := by
      have hh : ¬ |q j-b| ≤ 3*ε := fun h => hgood (Or.inr h)
      rw [abs_of_nonpos (sub_nonpos.mpr (hgap j hjS).2)] at hh
      linarith only [lt_of_not_ge hh]
    have hcentral : 3*|r| *ε < r*q j-e := by
      rcases horientation with ⟨hr,href⟩ | ⟨hr,href⟩
      · have heq : e=a*r := (div_eq_iff hr.ne').mp href
        rw [abs_of_pos hr,heq]
        nlinarith only [mul_lt_mul_of_pos_left hleft hr]
      · have heq : e=b*r := (div_eq_iff hr.ne).mp href
        rw [abs_of_neg hr,heq]
        nlinarith only [mul_lt_mul_of_pos_left hright (neg_pos.mpr hr)]
    obtain ⟨hlo,hhi,hratio⟩ := affine_endpoint_factor_two hε hcentral
    refine ⟨by linarith only [hleft],by linarith only [hright],hlo,hhi,hratio,?_⟩
    intro z hz
    constructor <;> linarith only [hleft,hright,hε,hz.1,hz.2]

private theorem source_sector_linearization_error_bound
    (K : ℕ) {D D₀ Ct E R N Q d width : ℝ}
    (hCt : 0 ≤ Ct)
    (hR : 0 < R) (hN : 0 < N) (hQ : 0 < Q) (hd : 0 < d)
    (hK : (K:ℝ) ≤ Q/d)
    (hwidth : 0 ≤ width ∧ width ≤ 8*(E/R^2)*d^2)
    (hD : D ≤ D₀*Q/N) :
    D+(K:ℝ)*(Ct*R^4/(N*d^3))*width^2 ≤
      (D₀+64*Ct*E^2)*Q/N := by
  have hw0 := hwidth.1
  have hwupper := hwidth.2
  have hterm : (K:ℝ)*(Ct*R^4/(N*d^3))*width^2 ≤ 64*Ct*E^2*Q/N := by
    calc
      _ ≤ (Q/d)*(Ct*R^4/(N*d^3))*(8*(E/R^2)*d^2)^2 := by gcongr
      _ = _ := by field_simp; ring
  calc
    _ ≤ D₀*Q/N+64*Ct*E^2*Q/N := add_le_add hD hterm
    _ = _ := by ring

private theorem source_sector_weighted_error_bound
    {η Cη Q N height width U E B : ℝ}
    (hC : 0 ≤ Cη) (hQ : 0 < Q) (hN : 0 < N)
    (hheight : 0 ≤ height) (hwidth : 0 ≤ width)
    (hE : 0 < E) (hB : 0 < B)
    (hη : η ≤ Cη*Q/N) (hheightBound : height ≤ 105*U/E*width)
    (hselected : B*U*Q ≤ N)
    (hmargin : 2*3840*128^2*105*Cη ≤ B*E) :
    3840*128*η*height ≤ width/256 := by
  have hratio : U*Q/N ≤ 1/B := by
    apply (div_le_div_iff₀ hN hB).mpr
    nlinarith only [hselected]
  have hconstant : (3840*128*105*Cη)/(B*E) ≤ 1/256 := by
    apply (div_le_iff₀ (mul_pos hB hE)).mpr
    nlinarith only [hmargin]
  calc
    _ ≤ 3840*128*(Cη*Q/N)*height := by gcongr
    _ ≤ 3840*128*(Cη*Q/N)*(105*U/E*width) := by gcongr
    _ = ((3840*128*105*Cη)/E)*(U*Q/N)*width := by field_simp
    _ ≤ ((3840*128*105*Cη)/E)*(1/B)*width := by gcongr
    _ = ((3840*128*105*Cη)/(B*E))*width := by field_simp
    _ ≤ (1/256)*width := mul_le_mul_of_nonneg_right hconstant hwidth
    _ = width/256 := by ring

private theorem source_sector_height_width_bound
    {height width E R r d U : ℝ}
    (hE : 0 < E) (hR : 0 < R) (hr : 0 < r) (hd : 0 < d) (hU : 0 ≤ U)
    (hheight : r*height ≤ 30*d)
    (hgap : R^2 ≤ 7*r*d*U)
    (hwidth : 2*(E/R^2)*d^2 ≤ width) :
    height ≤ 105*U/E*width := by
  have hH : height ≤ 30*d/r := (le_div_iff₀ hr).mpr (by nlinarith only [hheight])
  have hmain : 30*d/r ≤ (105*U/E)*(2*(E/R^2)*d^2) := by
    apply (mul_le_mul_iff_of_pos_right (mul_pos hr (pow_pos hR 2))).mp
    have hleft : (30*d/r)*(r*R^2)=30*d*R^2 := by field_simp
    have hright : ((105*U/E)*(2*(E/R^2)*d^2))*(r*R^2)=210*U*d^2*r := by
      field_simp
      ring
    rw [hleft,hright]
    nlinarith only [mul_le_mul_of_nonneg_left hgap (show 0 ≤ 30*d by positivity)]
  exact hH.trans (hmain.trans (mul_le_mul_of_nonneg_left hwidth (by positivity)))

                                                                     
                                                                          
                                                                      
                                                     
theorem reference_gap_complete_sector_linearization_size
    (e r v s : ℤ) (anchor : ℚ)
    {q ε E R Q N d l w gapLo gapHi U B D D₀ Ct : ℝ}
    (hdet : v*r-e*s=1) (hr : r ≠ 0)
    (hE : 0 < E) (hR : 0 < R) (hQ : 0 < Q) (hN : 0 < N)
    (hd : 0 < d) (hU : 0 ≤ U) (hB : 0 < B)
    (hCt : 0 ≤ Ct) (hD₀ : 0 ≤ D₀) (heps : ε=E/R^2)
    (hminus : 0 < (r:ℝ)*(q-ε)-e)
    (hplus : 0 < (r:ℝ)*(q+ε)-e)
    (hdyad : max ((r:ℝ)*(q-ε)-e) ((r:ℝ)*(q+ε)-e) ≤
      2*min ((r:ℝ)*(q-ε)-e) ((r:ℝ)*(q+ε)-e))
    (hanchor : |(anchor:ℝ)-q| ≤ ε)
    (hcut : 256*(anchor.den:ℝ) ≤ Q/3)
    (hcount : 256 ≤ (2*ε)*(Q/3)*anchor.den)
    (hden : ∀ z∈Icc l w, d ≤ (r:ℝ)*z+s ∧ (r:ℝ)*z+s ≤ 2*d)
    (hcoord : |(r:ℝ)| * max |l| |w| ≤ 30*d)
    (hgap : gapHi-gapLo ≤ 7*U/(2*R^2))
    (hendpoint : (e:ℝ)/r=gapLo ∨ (e:ℝ)/r=gapHi)
    (hpoint : q+ε∈Icc gapLo gapHi)
    (hselected : B*U*Q ≤ N)
    (hmargin : 2*3840*128^2*105*(D₀+64*Ct*E^2) ≤ B*E)
    (hD : D ≤ D₀*Q/N) :
    let α := ((v:ℝ)-s*(q+ε))/((r:ℝ)*(q+ε)-e)
    let β := ((v:ℝ)-s*(q-ε))/((r:ℝ)*(q-ε)-e)
    let K := ⌊(Q/3)*min ((r:ℝ)*(q-ε)-e) ((r:ℝ)*(q+ε)-e)⌋₊
    let S := if 0 < α then HuxleyLinearForm.fareySector K α β
      else (HuxleyLinearForm.fareySector K (-β) (-α)).image
        (fun p : ℤ × ℤ => (-p.1,p.2))
    let η := D+(K:ℝ)*(Ct*R^4/(N*d^3))*(β-α)^2
    α∈Icc l w → β∈Icc l w → (0 < α ∨ β < 0) →
    3840*128*η*((max |α| |β|)*(K:ℝ))*(K:ℝ) < S.card := by
  classical
  intro α β K S η hαI hβI hsign
  have hε : 0 < ε := by rw [heps]; positivity
  have hdetR : (v:ℝ)*r-e*s=1 := by exact_mod_cast hdet
  have hrR : (r:ℝ) ≠ 0 := by exact_mod_cast hr
  have hαden : (r:ℝ)*α+s=1/((r:ℝ)*(q+ε)-e) := by
    dsimp only [α]
    field_simp
    nlinarith only [hdetR]
  have hβden : (r:ℝ)*β+s=1/((r:ℝ)*(q-ε)-e) := by
    dsimp only [β]
    field_simp
    nlinarith only [hdetR]
  have hwidth : β-α=2*ε*((r:ℝ)*α+s)*((r:ℝ)*β+s) := by
    rw [hαden,hβden]
    have hh := inverseFarey_difference hdetR hminus.ne' hplus.ne'
    change β-α=((q+ε)-(q-ε))/(((r:ℝ)*(q-ε)-e)*((r:ℝ)*(q+ε)-e)) at hh
    rw [hh]
    field_simp
    ring
  have hαd := hden α hαI
  have hβd := hden β hβI
  have hαlo := hαd.1
  have hαhi := hαd.2
  have hβlo := hβd.1
  have hβhi := hβd.2
  have hαpos := hd.trans_le hαlo
  have hβpos := hd.trans_le hβlo
  have hwidth0 : 0 < β-α := by
    rw [hwidth]
    exact mul_pos (mul_pos (mul_pos (by norm_num) hε) (hd.trans_le hαd.1))
      (hd.trans_le hβd.1)
  have hwidthLower : 2*(E/R^2)*d^2 ≤ β-α := by
    rw [hwidth,←heps]
    calc
      _ = 2*ε*d*d := by ring
      _ ≤ _ := by gcongr
  have hwidthUpper : β-α ≤ 8*(E/R^2)*d^2 := by
    rw [hwidth,←heps]
    calc
      _ ≤ 2*ε*(2*d)*(2*d) := by gcongr
      _ = _ := by ring
  have hAupper : (r:ℝ)*(q-ε)-e ≤ 1/d := by
    have hh := hβd.1
    rw [hβden] at hh
    have hx := (le_div_iff₀ hminus).mp hh
    apply (le_div_iff₀ hd).mpr
    nlinarith only [hx]
  have hK : (K:ℝ) ≤ Q/d := by
    have hm : 0 < min ((r:ℝ)*(q-ε)-e) ((r:ℝ)*(q+ε)-e) := lt_min hminus hplus
    calc
      _ ≤ (Q/3)*min ((r:ℝ)*(q-ε)-e) ((r:ℝ)*(q+ε)-e) := Nat.floor_le (by positivity)
      _ ≤ Q*(1/d) := by
        apply mul_le_mul
        · linarith only [hQ]
        · exact (min_le_left _ _).trans hAupper
        · exact hm.le
        · exact hQ.le
      _ = Q/d := by ring
  have hη : η ≤ (D₀+64*Ct*E^2)*Q/N :=
    source_sector_linearization_error_bound K hCt hR hN hQ hd hK
      ⟨hwidth0.le,hwidthUpper⟩ hD
  have habs (z : ℝ) (hz : z∈Icc l w) : |z| ≤ max |l| |w| := by
    apply abs_le.mpr
    exact ⟨(neg_le_neg (le_max_left _ _)).trans ((neg_abs_le l).trans hz.1),
      hz.2.trans ((le_abs_self w).trans (le_max_right _ _))⟩
  have hheight : |(r:ℝ)| * max |α| |β| ≤ 30*d :=
    (mul_le_mul_of_nonneg_left (max_le (habs α hαI) (habs β hβI))
      (abs_nonneg _)).trans hcoord
  have hdist : |q+ε-(e:ℝ)/r| ≤ 7*U/(2*R^2) := by
    apply le_trans _ hgap
    rcases hendpoint with he | he
    · rw [he,abs_of_nonneg (sub_nonneg.mpr hpoint.1)]
      linarith only [hpoint.2]
    · rw [he,abs_of_nonpos (sub_nonpos.mpr hpoint.2)]
      linarith only [hpoint.1]
  have hid : (q+ε-(e:ℝ)/r)*(r:ℝ)*((r:ℝ)*α+s)=1 := by
    rw [hαden]
    field_simp
    exact div_self (by nlinarith only [hplus])
  have hidentity : |q+ε-(e:ℝ)/r| * |(r:ℝ)| *((r:ℝ)*α+s)=1 := by
    have hh := congrArg abs hid
    simpa only [abs_mul,abs_one,abs_of_pos (hd.trans_le hαd.1)] using hh
  have hgapScale : R^2 ≤ 7*|(r:ℝ)| *d*U := by
    have hh : (1:ℝ) ≤ 7*U/(2*R^2)*|(r:ℝ)| *(2*d) := by
      rw [←hidentity]
      gcongr
    have he : 7*U/(2*R^2)*|(r:ℝ)| *(2*d)=(7*|(r:ℝ)| *d*U)/R^2 := by
      field_simp
    rw [he] at hh
    simpa only [one_mul] using (le_div_iff₀ (pow_pos hR 2)).mp hh
  have hheightWidth : max |α| |β| ≤ 105*U/E*(β-α) :=
    source_sector_height_width_bound hE hR (abs_pos.mpr hrR) hd hU
      hheight hgapScale hwidthLower
  have hweighted : 3840*128*η*(max |α| |β|) ≤ (β-α)/256 :=
    source_sector_weighted_error_bound (by positivity) hQ hN
      ((abs_nonneg α).trans (le_max_left _ _)) hwidth0.le hE hB
      hη hheightWidth hselected hmargin
  have hanchorI : (anchor:ℝ)∈Icc (q-ε) (q+ε) := by
    have hh := abs_le.mp hanchor
    constructor <;> linarith only [hh.1,hh.2]
  have hcount' : 256 ≤ ((q+ε)-(q-ε))*(Q/3)*anchor.den := by
    convert hcount using 1
    ring
  have hdensity : max ((β-α)*(K:ℝ)^2/128:ℝ) 2 ≤ (S.card:ℝ) := by
    by_cases ha : 0 < α
    · have hn : 0 < (v:ℝ)-s*(q+ε) := (div_pos_iff_of_pos_right hplus).mp ha
      have hh := completeSector_density_from_curvature_signed hdet
        (by linarith only [hε] : q-ε < q+ε) hminus hplus hn hanchorI hdyad hcut hcount'
      simpa only [S,ite_eq_left ha] using hh.1
    · have hb : β < 0 := hsign.resolve_left ha
      have hn : (v:ℝ)-s*(q-ε) < 0 := by
        simpa only [zero_mul] using (div_lt_iff₀ hminus).mp hb
      have hh := completeNegativeSector_density_from_curvature hdet
        (by linarith only [hε] : q-ε < q+ε) hminus hplus hn hanchorI hdyad hcut hcount'
      simpa only [S,ite_eq_right ha] using hh.1
  have hhalf : 2*(3840*128*η*((max |α| |β|)*(K:ℝ))*(K:ℝ)) ≤
      (β-α)*(K:ℝ)^2/128 := by
    have hh := mul_le_mul_of_nonneg_right hweighted
      (show 0 ≤ 2*(K:ℝ)^2 by positivity)
    nlinarith only [hh]
  have hlow := (le_max_left _ _).trans hdensity
  have hpos := (le_max_right _ _).trans hdensity
  linarith only [hhalf,hlow,hpos]

private theorem selected_reference_linear_budget
    (U : ℕ) {B N Q : ℝ}
    (hN : 0 < N) (hQ : 0 < Q) (hB : 1 ≤ B) (hU : 1 ≤ U)
    (hupper : (U:ℝ) ≤ (N/Q)^((2:ℝ)/3)/B) :
    B*(U:ℝ)*Q ≤ N := by
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hUone : (1:ℝ) ≤ U := by exact_mod_cast hU
  have hh := (le_div_iff₀ hBp).mp hupper
  have hlower : 1 ≤ (N/Q)^((2:ℝ)/3) := by
    have hb := mul_le_mul hUone hB (by norm_num : (0:ℝ) ≤ 1) (Nat.cast_nonneg U)
    linarith only [hb,hh]
  have hratio : 1 ≤ N/Q := by
    by_contra hn
    have ht := Real.rpow_lt_one (div_pos hN hQ).le (lt_of_not_ge hn)
      (by norm_num : (0:ℝ) < (2:ℝ)/3)
    exact (not_lt_of_ge hlower) ht
  have hp := Real.rpow_le_self_of_one_le hratio (by norm_num : (2:ℝ)/3 ≤ 1)
  apply (le_div_iff₀ hQ).mp
  nlinarith only [hh,hp]

public  theorem physical_source_quartic_constants_nonneg
    {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 ≤ δ) :
    0 ≤ quarticReciprocalConstant σ δ ∧ 0 ≤ quarticNonlinearResidualConstant σ δ := by
  have hκ := modelPhaseThirdLower_pos hσ
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ
  have hC₄ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ
  constructor
  · dsimp only [quarticReciprocalConstant]
    positivity
  · dsimp only [quarticNonlinearResidualConstant]
    positivity

                                                                
                                                                   
                                                                  
                                                  
private theorem physicalModelPhase_actual_fourier_certified_reference_gap_quartic_witnesses
    (Uref : ℕ) (Refs : Finset ℝ) {Bselect gapLo gapHi : ℝ}
    (S : Finset ℕ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R d base l w Bcut : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hden : ∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den)
    (hinv : ∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1)
    (hchart : v*r-e*s=1)
    (horientation : ((0:ℝ) < r ∧ (e:ℝ)/r=gapLo) ∨
      ((r:ℝ) < 0 ∧ (e:ℝ)/r=gapHi))
    (hd : 0 < d) (hBcut : 0 < Bcut)
    (hs : s ≠ 0)
    (hrefSet : (e:ℝ)/r∈Refs) (hparentSet : (v:ℝ)/s∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hdenl : d ≤ (r:ℝ)*l+s ∧ (r:ℝ)*l+s ≤ 2*d)
    (hdenw : d ≤ (r:ℝ)*w+s ∧ (r:ℝ)*w+s ≤ 2*d)
    (hwideL : ∀ j∈S, ∀ i, x j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ j∈S, ∀ i, x j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : R^2 ≤ (r:ℝ)^2*(Uref:ℝ))
    (hgapWidth : gapHi-gapLo ≤ 7*(Uref:ℝ)/(2*R^2))
    (hchartLeft : ((e:ℝ)*l+v)/((r:ℝ)*l+s)∈Icc gapLo gapHi)
    (hchartRight : ((e:ℝ)*w+v)/((r:ℝ)*w+s)∈Icc gapLo gapHi)
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ j∈S, (rat j 0:ℝ)∈Icc gapLo gapHi) :
    let Lref := 56*(Uref:ℝ)/modelPhaseThirdLower σ
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    105+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card →
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
    let ε := κ/(16*(Cphys+2)*R^2)
    2 ≤ N →
    (∀ j∈S, ∀ i, x j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, ∀ i, x j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, |(anchor j:ℝ)-(rat j 0:ℝ)| ≤ ε) →
    (∀ j∈S, 256*((anchor j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ j∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor j).den) →
    let lo := fun j => (rat j 0:ℝ)-ε
    let hi := fun j => (rat j 0:ℝ)+ε
    let α := fun j => ((v:ℝ)-s*hi j)/((r:ℝ)*hi j-e)
    let β := fun j => ((v:ℝ)-s*lo j)/((r:ℝ)*lo j-e)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    ∃ G : Finset ℕ, G⊆S ∧ S.card ≤ 6+G.card ∧
    ∃ jref : ℕ, jref∈G ∧
    ∃ xref : Fin 2 → ℝ,
      (∀ i, 0 < rp i*r ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
        |xref i-x jref i| ≤ Lref*N ∧
        |(round (xref i):ℝ)-(round (x jref i):ℝ)| ≤ Lref*N+1) ∧
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈G, α j∈Icc l w ∧ β j∈Icc l w) →
    61*Ccurv*Cphys ≤ Bcut →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 105+17*S₀.card ∧
    (∀ a∈S₀, (rat a 0:ℝ)∈Ioo gapLo gapHi) ∧
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let G := minorArcCoordinate (μr 0) (rp 0) (sp 0)
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    let vp : Fin 2 → ℤ := ![v,Mat 0*v+Mat 1*s]
    ∃ j : Fin 8 → ℕ, ∃ z : Fin 8 → ℝ, ∃ curve : ℝ → Fin 2 → ℝ, ∃ alpha beta : ℝ,
      (∀ a, j a∈S₀ ∧ ∀ i,
        (rat (j a) i:ℝ)=((ep i:ℝ)*z a+vp i)/((rp i:ℝ)*z a+sp i)) ∧
      StrictMono z ∧ 0 < L ∧ (L*N)^2 ≤ M*R ∧ 0 ≤ Kres ∧
      (∀ t∈Icc (z 0) (z 7), t∈Icc l w ∧ ∀ i,
        curve t i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        d ≤ (rp i:ℝ)*t+sp i ∧ (rp i:ℝ)*t+sp i ≤ 2*d ∧
        iteratedDeriv 2 (f i) (curve t i)/2=((ep i:ℝ)*t+vp i)/((rp i:ℝ)*t+sp i) ∧
        |(round (curve t i):ℝ)-(round (xref i):ℝ)|^2 ≤ M*R) ∧
      (∀ i : Fin 7, L*N ≤ |G (z i.succ)-G (z i.castSucc)|) ∧
      (∀ i : Fin 8,
        |alpha*z i+beta-rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1) (z i)+
          quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1) (z i)| ≤
          Kres*R^2/|(rp 0:ℝ)*G (z i)|) := by
  classical
  intro Lref Vheight P₁ P₂ hS f hlevel q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H ε hNtwo hL hU hanchor hcut hcount
    lo hi α β C₂ C₃ Ct Cc Δ ep rp sp
  let Kaux := fun j => ⌊((Q:ℝ)/3)*min ((r:ℝ)*lo j-e) ((r:ℝ)*hi j-e)⌋₊
  let Saux := fun j => if 0 < α j then HuxleyLinearForm.fareySector (Kaux j) (α j) (β j)
    else (HuxleyLinearForm.fareySector (Kaux j) (-β j) (-α j)).image
      (fun p : ℤ × ℤ => (-p.1,p.2))
  have hr : r ≠ 0 := by
    rcases horientation with ⟨hr,_⟩ | ⟨hr,_⟩
    · exact_mod_cast hr.ne'
    · exact_mod_cast hr.ne
  have hreferenceEndpoint : (e:ℝ)/r=gapLo ∨ (e:ℝ)/r=gapHi :=
    horientation.imp And.right And.right
  obtain ⟨G,hGS,hS6G,hgeom⟩ :=
    physicalModelPhase_reference_gap_interior_chart_selection S (fun j => x j 0)
      hσ hδ (approximateModelPhase_mono (hF 0) (by norm_num : 2 ≤ 4) le_rfl)
      hT hM hN (zero_lt_one.trans_le hR) (hA 0) (hW 0) hscale horientation
      (fun j hj => ⟨by linarith only [(hx j hj 0).1],by linarith only [(hx j hj 0).2]⟩)
      (fun j hj => by simpa only [mul_comm] using hwindow j hj)
      (fun j hj => by
        change iteratedDeriv 2 (f 0) (x j 0)/2∈Icc gapLo gapHi
        rw [hlevel j hj 0]
        exact hfamilyGap j hj)
  have hGlarge : 99+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ G.card := by
    have hb := hS.trans hS6G
    exact Nat.le_of_add_le_add_left (a:=6)
      (by simpa only [←Nat.add_assoc] using hb)
  have hGpos : 0 < G.card :=
    (by decide : 0 < 99).trans_le ((Nat.le_add_right 99 _).trans hGlarge)
  obtain ⟨jref,hjref⟩ := Finset.card_pos.mp hGpos
  have hgeometry j (hj : j∈G) :
      0 < (r:ℝ)*((rat j 0:ℝ)-ε)-e ∧
      0 < (r:ℝ)*((rat j 0:ℝ)+ε)-e ∧
      max ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e) ≤
        2*min ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e) := by
    have hh := (hgeom j hj).2.2
    change 0 < (r:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2-ε)-e ∧
      0 < (r:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2+ε)-e ∧
      max ((r:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2-ε)-e)
          ((r:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2+ε)-e) ≤
        2*min ((r:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2-ε)-e)
          ((r:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2+ε)-e) ∧ _ at hh
    rw [hlevel j (hGS hj) 0] at hh
    exact ⟨hh.1,hh.2.1,hh.2.2.1⟩
  have hconsumer := physicalModelPhase_actual_fourier_separated_reference_gap_quartic_witnesses Uref Refs (Bselect:=Bselect) (gapLo:=gapLo) (gapHi:=gapHi) G jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW (fun j hj => hx j (hGS hj)) (fun j hj => hwindow j (hGS hj)) (fun j hj => hden j (hGS hj)) (fun j hj => hinv j (hGS hj)) hchart hr hd hBcut hs hrefSet hparentSet hsep hdenl hdenw (hwideL jref (hGS hjref)) (hwideU jref (hGS hjref)) hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hreferenceEndpoint hchartLeft hchartRight hRQ hselectedUpper hscaleTen (fun j hj => hfamilyGap j (hGS hj))
  obtain ⟨xref,hxr,hrest⟩ := hconsumer hGlarge
    (fun j hj => hlevel j (hGS hj)) (fun j hj => hcolor j (hGS hj))
    (fun j hj => hnear j (hGS hj))
    hsmall hNR hRN hNcube hminscale hMatdet
    (fun j hj => hMatt j (hGS hj)) (fun j hj => hMatmap j (hGS hj)) hMatgamma
    hNtwo (fun j hj => hL j (hGS hj)) (fun j hj => hU j (hGS hj))
    (fun j hj => (hgeometry j hj).1) (fun j hj => (hgeometry j hj).2.1)
    (fun j hj => (hgeometry j hj).2.2)
    (fun j hj => hanchor j (hGS hj)) (fun j hj => hcut j (hGS hj))
    (fun j hj => hcount j (hGS hj))
  refine ⟨G,hGS,hS6G,jref,hjref,xref,hxr,?_⟩
  intro Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hdenregion hends hBsize
  let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*d^3)
  let η := fun j => D+(Kaux j:ℝ)*Ctay*(β j-α j)^2
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCp : 0 < Cphys+2 := by dsimp only [Cphys]; positivity
  have hEsize : 0 < Esize := by dsimp only [Esize]; positivity
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hQpos : (0:ℝ) < Q := by exact_mod_cast hQ
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hBselect : 0 < Bselect := by
    have hh : 0 < 168/κ := by positivity
    change 2+168/κ ≤ Bselect at hBselectSize
    linarith only [hBselectSize,hh]
  have hBselectOne : 1 ≤ Bselect := by
    have hh : 0 < 168/κ := by positivity
    change 2+168/κ ≤ Bselect at hBselectSize
    linarith only [hBselectSize,hh]
  have hselectedLinear : Bselect*(Uref:ℝ)*(Q:ℝ) ≤ N :=
    selected_reference_linear_budget Uref hN hQpos hBselectOne hUref hselectedUpper
  have hδ0 : 0 ≤ δ := approximateModelPhase_tolerance_nonneg (hF 0)
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  obtain ⟨hCR,hCN⟩ := physical_source_quartic_constants_nonneg hσ hδ0
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hCt : 0 ≤ Ct := by dsimp only [Ct,C₂,C₃]; positivity
  have hCc : 0 ≤ Cc := by dsimp only [Cc,C₂,C₃]; positivity
  have hDbase : 0 ≤ Dbase := by dsimp only [Dbase]; positivity
  have hTbase : 0 ≤ Tbase := by dsimp only [Tbase]; positivity
  have hDupper : D ≤ Dbase*(Q:ℝ)/N := by
    apply le_of_eq
    dsimp only [D,Dbase,Δ]
    ring
  have heps : ε=Esize/R^2 := by
    dsimp only [ε,Esize]
    field_simp
  have hcoord : |(r:ℝ)| * max |l| |w| ≤ 30*d :=
    separated_farey_reference_interval_coordinate_bound Refs
      (δ:=(Uref:ℝ)/R^2) (by exact_mod_cast hr) (by exact_mod_cast hs)
      (by exact_mod_cast hchart) hrefSet hparentSet hsep
      (hgapWidth.trans_eq (by ring)) hreferenceEndpoint hd hdenl hdenw
      hchartLeft hchartRight
  have hsector j (hj : j∈G) (hsign : 0 < α j ∨ β j < 0) :
      3840*128*η j*((max |α j| |β j|)*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card := by
    have hpoint : (rat j 0:ℝ)+ε∈Icc gapLo gapHi := by
      have hh := (hgeom j hj).2.2.2.2.2
        ⟨by linarith only [hε],le_rfl⟩
      change iteratedDeriv 2 (f 0) (x j 0)/2+ε∈Icc gapLo gapHi at hh
      rw [hlevel j (hGS hj) 0] at hh
      exact hh
    exact reference_gap_complete_sector_linearization_size e r v s (anchor j)
      hchart hr hEsize hRpos hQpos hN hd (Nat.cast_nonneg Uref) hBselect
      hTbase hDbase heps (hgeometry j hj).1 (hgeometry j hj).2.1 (hgeometry j hj).2.2
      (hanchor j (hGS hj)) (hcut j (hGS hj)) (hcount j (hGS hj))
      (fun z hz => hdenregion z hz 0) hcoord hgapWidth hreferenceEndpoint hpoint
      hselectedLinear hsize hDupper (hends j hj).1 (hends j hj).2 hsign
  obtain ⟨S₀,hS₀G,hGmass,hbound⟩ := hrest hD hΔ hdenregion hends hsector hBsize
  have htotal : S.card ≤ 105+17*S₀.card := by
    calc
      S.card ≤ 6+G.card := hS6G
      _ ≤ 6+(99+17*S₀.card) := Nat.add_le_add_left hGmass 6
      _ = 105+17*S₀.card := by simp only [←Nat.add_assoc]
  refine ⟨S₀,hS₀G.trans hGS,htotal,?_,hbound⟩
  intro a ha
  have hleft : gapLo+3*ε < (rat a 0:ℝ) := by
    have hh := (hgeom a (hS₀G ha)).1
    change gapLo+3*ε < iteratedDeriv 2 (f 0) (x a 0)/2 at hh
    rwa [hlevel a (hGS (hS₀G ha)) 0] at hh
  have hright : (rat a 0:ℝ) < gapHi-3*ε := by
    have hh := (hgeom a (hS₀G ha)).2.1
    change iteratedDeriv 2 (f 0) (x a 0)/2 < gapHi-3*ε at hh
    rwa [hlevel a (hGS (hS₀G ha)) 0] at hh
  exact ⟨by linarith only [hleft,hε],by linarith only [hright,hε]⟩

                                                             
private theorem logarithmic_quarter_band_partition
    {ι : Type*} (S : Finset ι) (a : ι → ℝ) {a₀ cap : ℝ}
    (ha₀ : 0 < a₀)
    (ha : ∀ j∈S, a₀ ≤ a j ∧ a j ≤ cap*a₀) :
    let color := fun j => ⌊Real.logb (5/4) (a j/a₀)⌋₊
    (S.image color).card ≤ ⌊Real.logb (5/4) cap⌋₊+1 ∧
    ∀ j∈S, a₀*(5/4:ℝ)^(color j) ≤ a j ∧
      a j ≤ (5/4)*(a₀*(5/4:ℝ)^(color j)) := by
  classical
  intro color
  have hbase : (1:ℝ) < 5/4 := by norm_num
  have hjpos j (hj : j∈S) : 0 < a j := ha₀.trans_le (ha j hj).1
  have hratio j (hj : j∈S) : 1 ≤ a j/a₀ :=
    (le_div_iff₀ ha₀).mpr (by simpa only [one_mul] using (ha j hj).1)
  constructor
  · have hs : S.image color ⊆ Finset.range (⌊Real.logb (5/4) cap⌋₊+1) := by
      intro k hk
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
      have hu : a j/a₀ ≤ cap := (div_le_iff₀ ha₀).mpr (ha j hj).2
      have hh := Real.logb_le_logb_of_le hbase (div_pos (hjpos j hj) ha₀) hu
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono hh))
    simpa only [Finset.card_range] using Finset.card_le_card hs
  · intro j hj
    have hp : 0 < a j/a₀ := div_pos (hjpos j hj) ha₀
    have hlog : 0 ≤ Real.logb (5/4) (a j/a₀) :=
      Real.logb_nonneg hbase (hratio j hj)
    have hlo := (Real.le_logb_iff_rpow_le hbase hp).mp (Nat.floor_le hlog)
    have hhi := (Real.logb_lt_iff_lt_rpow hbase hp).mp
      (Nat.lt_floor_add_one (Real.logb (5/4) (a j/a₀)))
    change (5/4:ℝ)^(color j:ℝ) ≤ a j/a₀ at hlo
    rw [Real.rpow_natCast] at hlo
    have hhi' : a j/a₀ < (5/4:ℝ)^(color j+1) := by
      rw [←Nat.cast_one,←Nat.cast_add,Real.rpow_natCast] at hhi
      exact hhi
    constructor
    · have hh := (le_div_iff₀ ha₀).mp hlo
      simpa only [mul_comm] using hh
    · have hh := (div_lt_iff₀ ha₀).mp hhi'
      rw [pow_succ] at hh
      nlinarith only [hh]

private theorem inverse_paired_chart_point_bounds
    {e r v s c t q y ε a₀ : ℝ}
    (hdet : v*r-e*s=1)
    (ha₀ : 0 < a₀)
    (hcentral : 12*|r| *ε < r*q-e)
    (hband : a₀ ≤ r*q-e ∧ r*q-e ≤ (5/4)*a₀)
    (hnear : |c*q+t-1| ≤ 1/24)
    (hsmall : |c| *ε ≤ 1/24)
    (hy : |y-q| ≤ ε) :
    let z := (v-s*y)/(r*y-e)
    let d := 2/(3*a₀)
    0 < r*y-e ∧
      (d ≤ r*z+s ∧ r*z+s ≤ 2*d) ∧
      (d ≤ (c*e+t*r)*z+(c*v+t*s) ∧
        (c*e+t*r)*z+(c*v+t*s) ≤ 2*d) := by
  intro z d
  have hdiff : |r*(y-q)| ≤ |r| *ε := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hy (abs_nonneg r)
  have habs := abs_le.mp hdiff
  have hAlo : (11/12)*a₀ ≤ r*y-e := by
    nlinarith only [hcentral,hband.1,habs.1]
  have hAhi : r*y-e ≤ (65/48)*a₀ := by
    nlinarith only [hcentral,hband.2,habs.2]
  have hA : 0 < r*y-e := lt_of_lt_of_le (by positivity) hAlo
  have hc : |c*(y-q)| ≤ 1/24 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hy (abs_nonneg c)).trans hsmall
  have ht : |c*y+t-1| ≤ 1/12 := by
    calc
      _ = |(c*q+t-1)+c*(y-q)| := by congr 1; ring
      _ ≤ |c*q+t-1|+|c*(y-q)| := abs_add_le _ _
      _ ≤ 1/12 := by linarith only [hnear,hc]
  have ht' := abs_le.mp ht
  have hid : r*z+s=1/(r*y-e) := by
    dsimp only [z]
    field_simp
    nlinarith only [hdet]
  have hid₁ : (c*e+t*r)*z+(c*v+t*s)=(c*y+t)/(r*y-e) := by
    dsimp only [z]
    field_simp
    linear_combination (c*y+t)*hdet
  rw [hid,hid₁]
  refine ⟨hA,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · apply (le_div_iff₀ hA).mpr
    dsimp only [d]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 3*a₀)).mpr
    nlinarith only [hAhi,ha₀]
  · apply (div_le_iff₀ hA).mpr
    dsimp only [d]
    rw [show 2*(2/(3*a₀))*(r*y-e)=4*(r*y-e)/(3*a₀) by ring]
    apply (le_div_iff₀ (by positivity : 0 < 3*a₀)).mpr
    nlinarith only [hAlo,ha₀]
  · apply (le_div_iff₀ hA).mpr
    dsimp only [d]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 3*a₀)).mpr
    nlinarith only [hAhi,ha₀,mul_nonneg ha₀.le (show 0 ≤ c*y+t-11/12 by linarith only [ht'.1])]
  · apply (div_le_iff₀ hA).mpr
    dsimp only [d]
    rw [show 2*(2/(3*a₀))*(r*y-e)=4*(r*y-e)/(3*a₀) by ring]
    apply (le_div_iff₀ (by positivity : 0 < 3*a₀)).mpr
    nlinarith only [hAlo,ha₀,mul_nonneg ha₀.le (show 0 ≤ 13/12-(c*y+t) by linarith only [ht'.2])]

private theorem physical_reference_gap_twelve_radius_selection
    (S : Finset ℕ) (x : ℕ → ℝ)
    {σ δ T M A W N R base a b e r : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hphase : T*N*R^2=M^3)
    (horientation : (0 < r ∧ e/r=a) ∨ (r < 0 ∧ e/r=b))
    (hx : ∀ j∈S, x j∈Ioo 0 W)
    (hwindow : ∀ j∈S, x j∈Icc (base+(j:ℝ)*N) (base+((j:ℝ)+1)*N)) :
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let f := heathBrownPhysicalPhase F T M A 1
    let q := fun j => iteratedDeriv 2 f (x j)/2
    (∀ j∈S, q j∈Icc a b) →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 6+S₀.card ∧ ∀ j∈S₀,
      a+12*ε < q j ∧ q j < b-12*ε ∧
      12*|r| *ε < r*q j-e := by
  classical
  intro ε f q hgap
  have hκ : 0 < modelPhaseThirdLower σ := modelPhaseThirdLower_pos hσ
  have hC : 0 < σ*(σ+1)+3 := by positivity
  let badA := S.filter (fun j => |q j-a| ≤ 12*ε)
  let badB := S.filter (fun j => |q j-b| ≤ 12*ε)
  let bad := fun j => |q j-a| ≤ 12*ε ∨ |q j-b| ≤ 12*ε
  let good := S.filter (fun j => ¬ bad j)
  have hrad : 4*(12*ε)*R^2 ≤ modelPhaseThirdLower σ := by
    have he : 4*(12*ε)*R^2=3*modelPhaseThirdLower σ/(σ*(σ+1)+3) := by
      dsimp only [ε]
      field_simp
      ring
    rw [he]
    apply (div_le_iff₀ hC).mpr
    have hh : 0 ≤ (σ*(σ+1))*modelPhaseThirdLower σ := by positivity
    nlinarith only [hh,hκ]
  have hcountA : badA.card ≤ 3 :=
    physicalModelPhase_curvature_boundary_window_count badA x
      hσ hδ hF hT hM hN hR hA hW hphase hrad
      (fun j hj => hx j (Finset.mem_filter.mp hj).1)
      (fun j hj => hwindow j (Finset.mem_filter.mp hj).1)
      (fun j hj => (Finset.mem_filter.mp hj).2)
  have hcountB : badB.card ≤ 3 :=
    physicalModelPhase_curvature_boundary_window_count badB x
      hσ hδ hF hT hM hN hR hA hW hphase hrad
      (fun j hj => hx j (Finset.mem_filter.mp hj).1)
      (fun j hj => hwindow j (Finset.mem_filter.mp hj).1)
      (fun j hj => (Finset.mem_filter.mp hj).2)
  have he : S.filter bad=badA∪badB := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_union,bad,badA,badB]
    tauto
  have hbad : (S.filter bad).card ≤ 6 := by
    rw [he]
    exact (Finset.card_union_le _ _).trans (by omega)
  refine ⟨good,Finset.filter_subset _ _,?_,?_⟩
  · have hh := Finset.card_filter_add_card_filter_not (s:=S) bad
    change (S.filter bad).card+good.card=S.card at hh
    omega
  · intro j hj
    obtain ⟨hjS,hgood⟩ := Finset.mem_filter.mp hj
    have hleft : 12*ε < q j-a := by
      have hh : ¬ |q j-a| ≤ 12*ε := fun h => hgood (Or.inl h)
      rw [abs_of_nonneg (sub_nonneg.mpr (hgap j hjS).1)] at hh
      exact lt_of_not_ge hh
    have hright : 12*ε < b-q j := by
      have hh : ¬ |q j-b| ≤ 12*ε := fun h => hgood (Or.inr h)
      rw [abs_of_nonpos (sub_nonpos.mpr (hgap j hjS).2)] at hh
      linarith only [lt_of_not_ge hh]
    have hcentral : 12*|r| *ε < r*q j-e := by
      rcases horientation with ⟨hr,href⟩ | ⟨hr,href⟩
      · have heq : e=a*r := (div_eq_iff hr.ne').mp href
        rw [abs_of_pos hr,heq]
        nlinarith only [mul_lt_mul_of_pos_left hleft hr]
      · have heq : e=b*r := (div_eq_iff hr.ne).mp href
        rw [abs_of_neg hr,heq]
        nlinarith only [mul_lt_mul_of_pos_left hright (neg_pos.mpr hr)]
    exact ⟨by linarith only [hleft],by linarith only [hright],hcentral⟩

private theorem affine_interval_bounds
    {r s l w d z : ℝ} (hz : z∈Icc l w)
    (hl : d ≤ r*l+s ∧ r*l+s ≤ 2*d)
    (hw : d ≤ r*w+s ∧ r*w+s ≤ 2*d) :
    d ≤ r*z+s ∧ r*z+s ≤ 2*d := by
  rcases le_total 0 r with hr | hr
  · constructor
    · nlinarith only [hl.1,mul_nonneg hr (sub_nonneg.mpr hz.1)]
    · nlinarith only [hw.2,mul_nonneg hr (sub_nonneg.mpr hz.2)]
  · constructor
    · nlinarith only [hw.1,mul_nonpos_of_nonpos_of_nonneg hr (sub_nonneg.mpr hz.2)]
    · nlinarith only [hl.2,mul_nonpos_of_nonpos_of_nonneg hr (sub_nonneg.mpr hz.1)]

private theorem reference_gap_quarter_band_chart_cover
    {ι : Type*} (S : Finset ι) (q : ι → ℝ)
    {e r v s c t ε a b : ℝ}
    (hdet : v*r-e*s=1) (hr : r ≠ 0) (hε : 0 < ε)
    (hcentral : ∀ j∈S, 12*|r| *ε < r*q j-e)
    (hupper : ∀ j∈S, r*q j-e ≤ |r| *(b-a))
    (hinterval : ∀ j∈S, Icc (q j-ε) (q j+ε) ⊆ Icc a b)
    (hnear : ∀ j∈S, |c*q j+t-1| ≤ 1/24)
    (hsmall : |c| *ε ≤ 1/24) :
    let color := fun j => ⌊Real.logb (5/4) ((r*q j-e)/(12*|r| *ε))⌋₊
    let α := fun j => (v-s*(q j+ε))/(r*(q j+ε)-e)
    let β := fun j => (v-s*(q j-ε))/(r*(q j-ε)-e)
    (S.image color).card ≤ ⌊Real.logb (5/4) ((b-a)/(12*ε))⌋₊+1 ∧
    ∀ n∈S.image color, ∃ d l w : ℝ, 0 < d ∧ l ≤ w ∧
      (∀ j∈S, color j=n → α j∈Icc l w ∧ β j∈Icc l w) ∧
      (∀ z∈Icc l w,
        (d ≤ r*z+s ∧ r*z+s ≤ 2*d) ∧
        (d ≤ (c*e+t*r)*z+(c*v+t*s) ∧ (c*e+t*r)*z+(c*v+t*s) ≤ 2*d)) ∧
      (e*l+v)/(r*l+s)∈Icc a b ∧ (e*w+v)/(r*w+s)∈Icc a b := by
  classical
  intro color α β
  let a₀ := 12*|r| *ε
  have ha₀ : 0 < a₀ := by dsimp only [a₀]; exact mul_pos (mul_pos (by norm_num) (abs_pos.mpr hr)) hε
  have hband := logarithmic_quarter_band_partition S (fun j => r*q j-e) ha₀
    (cap:=(b-a)/(12*ε)) (by
      intro j hj
      refine ⟨(hcentral j hj).le,?_⟩
      calc
        r*q j-e ≤ |r| *(b-a) := hupper j hj
        _ = ((b-a)/(12*ε))*a₀ := by dsimp only [a₀]; field_simp)
  refine ⟨hband.1,?_⟩
  intro n hn
  let G := S.filter (fun j => color j=n)
  obtain ⟨j₀,hj₀,hcolor₀⟩ := Finset.mem_image.mp hn
  have hG : G.Nonempty := ⟨j₀,Finset.mem_filter.mpr ⟨hj₀,hcolor₀⟩⟩
  let V := (G.image α)∪(G.image β)
  have hV : V.Nonempty := (hG.image α).mono (Finset.subset_union_left)
  let l := V.min' hV
  let w := V.max' hV
  let scale := a₀*(5/4:ℝ)^n
  let d := 2/(3*scale)
  have hscale : 0 < scale := by dsimp only [scale]; positivity
  have hd : 0 < d := by dsimp only [d]; positivity
  have hpoint j (hj : j∈G) y (hy : |y-q j| ≤ ε) :
      let z := (v-s*y)/(r*y-e)
      0 < r*y-e ∧
        (d ≤ r*z+s ∧ r*z+s ≤ 2*d) ∧
        (d ≤ (c*e+t*r)*z+(c*v+t*s) ∧
          (c*e+t*r)*z+(c*v+t*s) ≤ 2*d) := by
    obtain ⟨hjS,hcolor⟩ := Finset.mem_filter.mp hj
    have hb := hband.2 j hjS
    change a₀*(5/4:ℝ)^(color j) ≤ r*q j-e ∧
      r*q j-e ≤ (5/4)*(a₀*(5/4:ℝ)^(color j)) at hb
    rw [hcolor] at hb
    exact inverse_paired_chart_point_bounds hdet hscale (hcentral j hjS)
      hb (hnear j hjS) hsmall hy
  have hVpoint z (hz : z∈V) :
      (d ≤ r*z+s ∧ r*z+s ≤ 2*d) ∧
      (d ≤ (c*e+t*r)*z+(c*v+t*s) ∧ (c*e+t*r)*z+(c*v+t*s) ≤ 2*d) ∧
      (e*z+v)/(r*z+s)∈Icc a b := by
    have hex : ∃ j∈G, ∃ y, |y-q j| ≤ ε ∧ z=(v-s*y)/(r*y-e) := by
      rcases Finset.mem_union.mp hz with hz | hz
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
        exact ⟨j,hj,q j+ε,by simpa only [add_sub_cancel_left,abs_of_pos hε] using (le_rfl : ε ≤ ε),rfl⟩
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
        exact ⟨j,hj,q j-ε,by simpa only [sub_sub_cancel_left,abs_neg,abs_of_pos hε] using (le_rfl : ε ≤ ε),rfl⟩
    obtain ⟨j,hj,y,hy,rfl⟩ := hex
    have hh := hpoint j hj y hy
    refine ⟨hh.2.1,hh.2.2,?_⟩
    have he : (e*((v-s*y)/(r*y-e))+v)/(r*((v-s*y)/(r*y-e))+s)=y := by
      apply (div_eq_iff (hd.trans_le hh.2.1.1).ne').mpr
      have hmul : (r*y-e)*(r*y-e)⁻¹=1 := mul_inv_cancel₀ hh.1.ne'
      simp only [div_eq_mul_inv]
      linear_combination -(v-s*y)*hmul
    rw [he]
    apply hinterval j (Finset.mem_filter.mp hj).1
    obtain ⟨hyl,hyu⟩ := abs_le.mp hy
    constructor <;> linarith only [hyl,hyu]
  have hlmem : l∈V := Finset.min'_mem V hV
  have hwmem : w∈V := Finset.max'_mem V hV
  have hl := hVpoint l hlmem
  have hw := hVpoint w hwmem
  refine ⟨d,l,w,hd,Finset.min'_le V w hwmem,?_,?_,hl.2.2,hw.2.2⟩
  · intro j hj hcolor
    have hjG : j∈G := Finset.mem_filter.mpr ⟨hj,hcolor⟩
    have hα : α j∈V := Finset.mem_union_left _ (Finset.mem_image_of_mem α hjG)
    have hβ : β j∈V := Finset.mem_union_right _ (Finset.mem_image_of_mem β hjG)
    exact ⟨⟨Finset.min'_le V _ hα,Finset.le_max' V _ hα⟩,
      ⟨Finset.min'_le V _ hβ,Finset.le_max' V _ hβ⟩⟩
  · intro z hz
    exact ⟨affine_interval_bounds hz hl.1 hw.1,
      affine_interval_bounds hz hl.2.1 hw.2.1⟩

                                                                  
                                                                        
                                                                  
                                                         
theorem physicalModelPhase_same_color_reference_gap_paired_chart_cover
    (S : Finset ℕ) (x : ℕ → ℝ) (rat : ℕ → Fin 2 → ℚ)
    (Q K₀ : ℕ) [NeZero K₀] (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M A W N R base a b lambda U θ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hRN : R ≤ N) (hQ : 0 < Q)
    (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hphase : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hgamma : |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2))
    (hchart : v*r-e*s=1)
    (horientation : ((0:ℝ) < r ∧ (e:ℝ)/r=a) ∨ ((r:ℝ) < 0 ∧ (e:ℝ)/r=b))
    (hx : ∀ j∈S, x j∈Ioo 0 W)
    (hwindow : ∀ j∈S, x j∈Icc (base+(j:ℝ)*N) (base+((j:ℝ)+1)*N))
    (hlambda : 0 < lambda) (hU : 0 ≤ U)
    (hθ : 0 < θ) (hθmax : θ ≤ 1/24)
    (hcurv : ∀ j∈S, ∀ i, lambda ≤ |(rat j i:ℝ)| ∧ |(rat j i:ℝ)| ≤ U)
    (hden : ∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den)
    (hgap : ∀ j∈S, (rat j 0:ℝ)∈Icc a b)
    (hMatt : ∀ j∈S, (Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3=
      ((rat j 1).den:ℝ)/(rat j 0).den) :
    let f := heathBrownPhysicalPhase F T M A 1
    (∀ j∈S, iteratedDeriv 2 f (x j)/2=(rat j 0:ℝ)) →
    let color := fun j i => (⌊((rat j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ j∈S, color j 0=color j 1) →
    (((S ×ˢ (Finset.univ : Finset (Fin 2))).image
      (fun ji => color ji.1 ji.2)).card:ℝ) ≤ (4/θ+3)*(4*U/(lambda*θ)+3) ∧
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let chartColor := fun j => ⌊Real.logb (5/4)
      (((r:ℝ)*(rat j 0:ℝ)-e)/(12*|(r:ℝ)| *ε))⌋₊
    let α := fun j => ((v:ℝ)-s*((rat j 0:ℝ)+ε))/((r:ℝ)*((rat j 0:ℝ)+ε)-e)
    let β := fun j => ((v:ℝ)-s*((rat j 0:ℝ)-ε))/((r:ℝ)*((rat j 0:ℝ)-ε)-e)
    ∃ G : Finset ℕ, G⊆S ∧ S.card ≤ 6+G.card ∧
      (G.image chartColor).card ≤ ⌊Real.logb (5/4) ((b-a)/(12*ε))⌋₊+1 ∧
      ∀ n∈G.image chartColor, ∃ d l w : ℝ, 0 < d ∧ l ≤ w ∧
        (∀ j∈G, chartColor j=n → α j∈Icc l w ∧ β j∈Icc l w) ∧
        (∀ z∈Icc l w,
          (d ≤ (r:ℝ)*z+s ∧ (r:ℝ)*z+s ≤ 2*d) ∧
          (d ≤ ((Mat 2:ℝ)*e+Mat 3*r)*z+((Mat 2:ℝ)*v+Mat 3*s) ∧
            ((Mat 2:ℝ)*e+Mat 3*r)*z+((Mat 2:ℝ)*v+Mat 3*s) ≤ 2*d)) ∧
        ((e:ℝ)*l+v)/((r:ℝ)*l+s)∈Icc a b ∧
        ((e:ℝ)*w+v)/((r:ℝ)*w+s)∈Icc a b := by
  classical
  intro f hlevel color hsame
  have hbands := rational_narrow_band_partition
    (S ×ˢ (Finset.univ : Finset (Fin 2)))
    (fun ji : ℕ × Fin 2 => rat ji.1 ji.2) Q hQ hlambda hU hθ
    (fun ji hji => hcurv ji.1 (Finset.mem_product.mp hji).1 ji.2)
    (fun ji hji => hden ji.1 (Finset.mem_product.mp hji).1 ji.2)
  refine ⟨hbands.1,?_⟩
  intro ε chartColor α β
  have hnear j (hj : j∈S) :
      |(Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3-1| ≤ 1/24 := by
    rw [hMatt j hj]
    have hh := hbands.2 (j,0) (by simp only [Finset.mem_product,Finset.mem_univ,and_true]; exact hj)
      (j,1) (by simp only [Finset.mem_product,Finset.mem_univ,and_true]; exact hj)
      (hsame j hj)
    exact hh.1.trans hθmax
  have hκ := modelPhaseThirdLower_pos hσ
  have hC : 0 < σ*(σ+1)+1+2 := by positivity
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hr : (r:ℝ) ≠ 0 := by
    rcases horientation with ⟨hr,_⟩ | ⟨hr,_⟩
    · exact hr.ne'
    · exact hr.ne
  have hK : (0:ℝ) < K₀ := by exact_mod_cast NeZero.pos K₀
  have hQR : (0:ℝ) < Q := by exact_mod_cast hQ
  have hgamma' : |(Mat 2:ℝ)| ≤ R^4/(6*N^2) := by
    apply hgamma.trans
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh := pow_le_pow_left₀ (mul_nonneg hQR.le hN.le) hmesh 2
    nlinarith only [hh]
  have hκC : modelPhaseThirdLower σ ≤ σ*(σ+1)+1 := by
    have hh := approximateModelPhase_thirdDeriv_bounds hσ hδ hF
      (by norm_num : (3/2:ℝ)∈Ioo 1 2)
    exact hh.1.trans hh.2
  have hratio : modelPhaseThirdLower σ/(σ*(σ+1)+1+2) ≤ 1 :=
    (div_le_one hC).mpr (by linarith only [hκC])
  have hRN₂ : R^2/N^2 ≤ 1 := (div_le_one (sq_pos_of_pos hN)).mpr
    (pow_le_pow_left₀ hR.le hRN 2)
  have hsmall : |(Mat 2:ℝ)| *ε ≤ 1/24 := by
    calc
      _ ≤ (R^4/(6*N^2))*ε := mul_le_mul_of_nonneg_right hgamma' hε.le
      _ = (modelPhaseThirdLower σ/(σ*(σ+1)+1+2))*(R^2/N^2)/96 := by
        dsimp only [ε]
        field_simp
        ring
      _ ≤ 1*1/96 := by gcongr
      _ ≤ _ := by norm_num
  obtain ⟨G,hGS,hmass,hgeom⟩ := physical_reference_gap_twelve_radius_selection S x
    hσ hδ hF hT hM hN hR hA hW hphase horientation hx hwindow
    (fun j hj => by change iteratedDeriv 2 f (x j)/2∈Icc a b; rw [hlevel j hj]; exact hgap j hj)
  have hgeometry j (hj : j∈G) :
      a+12*ε < (rat j 0:ℝ) ∧ (rat j 0:ℝ) < b-12*ε ∧
      12*|(r:ℝ)| *ε < (r:ℝ)*(rat j 0:ℝ)-e := by
    have hh := hgeom j hj
    change a+12*ε < iteratedDeriv 2 f (x j)/2 ∧
      iteratedDeriv 2 f (x j)/2 < b-12*ε ∧
      12*|(r:ℝ)| *ε < (r:ℝ)*(iteratedDeriv 2 f (x j)/2)-e at hh
    rw [hlevel j (hGS hj)] at hh
    exact hh
  have hupper j (hj : j∈G) : (r:ℝ)*(rat j 0:ℝ)-e ≤ |(r:ℝ)| *(b-a) := by
    have hg := hgap j (hGS hj)
    rcases horientation with ⟨hrpos,href⟩ | ⟨hrneg,href⟩
    · have heq : (e:ℝ)=a*r := (div_eq_iff hrpos.ne').mp href
      rw [heq,abs_of_pos hrpos]
      nlinarith only [mul_nonneg hrpos.le (sub_nonneg.mpr hg.2)]
    · have heq : (e:ℝ)=b*r := (div_eq_iff hrneg.ne).mp href
      rw [heq,abs_of_neg hrneg]
      nlinarith only [mul_nonpos_of_nonpos_of_nonneg hrneg.le (sub_nonneg.mpr hg.1)]
  have hinterval j (hj : j∈G) : Icc ((rat j 0:ℝ)-ε) ((rat j 0:ℝ)+ε) ⊆ Icc a b := by
    intro y hy
    have hg := hgeometry j hj
    constructor <;> linarith only [hg.1,hg.2.1,hy.1,hy.2,hε]
  refine ⟨G,hGS,hmass,?_⟩
  exact reference_gap_quarter_band_chart_cover G (fun j => (rat j 0:ℝ))
    (by exact_mod_cast hchart) hr hε
    (fun j hj => (hgeometry j hj).2.2) hupper hinterval
    (fun j hj => hnear j (hGS hj)) hsmall


theorem physicalModelPhase_actual_fourier_charted_reference_gap_quartic_witnesses
    (Uref : ℕ) (Refs : Finset ℝ) {Bselect gapLo gapHi : ℝ}
    (S : Finset ℕ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hden : ∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den)
    (hlambda : 0 < lambda) (hUband : 0 ≤ Uband)
    (hθ : 0 < θ) (hθmax : θ ≤ 1/24)
    (hcurv : ∀ j∈S, ∀ i, lambda ≤ |(rat j i:ℝ)| ∧ |(rat j i:ℝ)| ≤ Uband)
    (hinv : ∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1)
    (hchart : v*r-e*s=1)
    (horientation : ((0:ℝ) < r ∧ (e:ℝ)/r=gapLo) ∨
      ((r:ℝ) < 0 ∧ (e:ℝ)/r=gapHi))
    (hBcut : 0 < Bcut)
    (hs : s ≠ 0)
    (hrefSet : (e:ℝ)/r∈Refs) (hparentSet : (v:ℝ)/s∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hwideL : ∀ j∈S, ∀ i, x j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ j∈S, ∀ i, x j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : R^2 ≤ (r:ℝ)^2*(Uref:ℝ))
    (hgapWidth : gapHi-gapLo ≤ 7*(Uref:ℝ)/(2*R^2))
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ j∈S, (rat j 0:ℝ)∈Icc gapLo gapHi) :
    let Lref := 56*(Uref:ℝ)/modelPhaseThirdLower σ
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
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    ∃ Schart : Finset ℕ, Schart⊆S ∧ S.card ≤ 6+Ccharts*Schart.card ∧
    ∃ G : Finset ℕ, G⊆Schart ∧ Schart.card ≤ 6+G.card ∧
    ∃ jref : ℕ, jref∈G ∧
    ∃ xref : Fin 2 → ℝ,
      (∀ i, 0 < rp i*r ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
        |xref i-x jref i| ≤ Lref*N ∧
        |(round (xref i):ℝ)-(round (x jref i):ℝ)| ≤ Lref*N+1) ∧
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
    ∃ d l w : ℝ, 0 < d ∧
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 6+Ccharts*(105+17*S₀.card) ∧
    (∀ a∈S₀, (rat a 0:ℝ)∈Ioo gapLo gapHi) ∧
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let G := minorArcCoordinate (μr 0) (rp 0) (sp 0)
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    let vp : Fin 2 → ℤ := ![v,Mat 0*v+Mat 1*s]
    ∃ j : Fin 8 → ℕ, ∃ z : Fin 8 → ℝ, ∃ curve : ℝ → Fin 2 → ℝ, ∃ alpha beta : ℝ,
      (∀ a, j a∈S₀ ∧ ∀ i,
        (rat (j a) i:ℝ)=((ep i:ℝ)*z a+vp i)/((rp i:ℝ)*z a+sp i)) ∧
      StrictMono z ∧ 0 < L ∧ (L*N)^2 ≤ M*R ∧ 0 ≤ Kres ∧
      (∀ t∈Icc (z 0) (z 7), t∈Icc l w ∧ ∀ i,
        curve t i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        d ≤ (rp i:ℝ)*t+sp i ∧ (rp i:ℝ)*t+sp i ≤ 2*d ∧
        iteratedDeriv 2 (f i) (curve t i)/2=((ep i:ℝ)*t+vp i)/((rp i:ℝ)*t+sp i) ∧
        |(round (curve t i):ℝ)-(round (xref i):ℝ)|^2 ≤ M*R) ∧
      (∀ i : Fin 7, L*N ≤ |G (z i.succ)-G (z i.castSucc)|) ∧
      (∀ i : Fin 8,
        |alpha*z i+beta-rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1) (z i)+
          quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1) (z i)| ≤
          Kres*R^2/|(rp 0:ℝ)*G (z i)|) := by
  classical
  intro Lref Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor hS
    f hlevel q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ ep rp sp
  have hcover := physicalModelPhase_same_color_reference_gap_paired_chart_cover
    S (fun j => x j 0) rat Q K₀ Mat e r v s
    hσ hδ (approximateModelPhase_mono (hF 0) (by norm_num : 2 ≤ 4) le_rfl)
    hT hM hN (zero_lt_one.trans_le hR) hRN hQ (hA 0) (hW 0) hscale
    hmesh hMatgamma hchart horientation
    (fun j hj => ⟨by linarith only [(hx j hj 0).1],by linarith only [(hx j hj 0).2]⟩)
    (fun j hj => by simpa only [mul_comm] using hwindow j hj)
    hlambda hUband hθ hθmax hcurv hden hfamilyGap hMatt
    (fun j hj => hlevel j hj 0) hsourceColor
  obtain ⟨G₀,hG₀S,hS6G₀,hcolors,hcharts⟩ := hcover.2
  let chartColor := fun j => ⌊Real.logb (5/4)
    (((r:ℝ)*(rat j 0:ℝ)-e)/(12*|(r:ℝ)| *ε))⌋₊
  let colors := G₀.image chartColor
  let fiber := fun n => G₀.filter (fun j => chartColor j=n)
  have hCap : 1 ≤ Ccharts := by dsimp only [Ccharts]; omega
  have hlargeS : 6+105 ≤ S.card := by
    apply le_trans _ hS
    nlinarith only [hCap]
  have hG₀ : G₀.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨n,hn,hmax⟩ := colors.exists_max_image (fun n => (fiber n).card)
    (hG₀.image chartColor)
  let Schart := fiber n
  have hSchartG : Schart⊆G₀ := Finset.filter_subset _ _
  have hSchartS : Schart⊆S := hSchartG.trans hG₀S
  have hGmass : G₀.card ≤ Ccharts*Schart.card := by
    calc
      G₀.card = ∑ k∈colors,(fiber k).card :=
        Finset.card_eq_sum_card_fiberwise (fun j hj => Finset.mem_image_of_mem chartColor hj)
      _ ≤ ∑ _k∈colors,Schart.card := Finset.sum_le_sum hmax
      _ = colors.card*Schart.card := by simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id]
      _ ≤ Ccharts*Schart.card := Nat.mul_le_mul_right _ hcolors
  have hSmass : S.card ≤ 6+Ccharts*Schart.card := by omega
  have hSchartLarge : 105+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ Schart.card := by
    have hh : Ccharts*(105+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1))) ≤
        Ccharts*Schart.card := Nat.le_of_add_le_add_left (hS.trans hSmass)
    nlinarith only [hh,hCap]
  obtain ⟨d,l,w,hd,hlw,hends,hregion,hchartLeft,hchartRight⟩ := hcharts n hn
  have hSchartEnds j (hj : j∈Schart) :
      ((v:ℝ)-s*((rat j 0:ℝ)+ε))/((r:ℝ)*((rat j 0:ℝ)+ε)-e)∈Icc l w ∧
      ((v:ℝ)-s*((rat j 0:ℝ)-ε))/((r:ℝ)*((rat j 0:ℝ)-ε)-e)∈Icc l w :=
    hends j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
  have hdenl : d ≤ (r:ℝ)*l+s ∧ (r:ℝ)*l+s ≤ 2*d :=
    (hregion l ⟨le_rfl,hlw⟩).1
  have hdenw : d ≤ (r:ℝ)*w+s ∧ (r:ℝ)*w+s ≤ 2*d :=
    (hregion w ⟨hlw,le_rfl⟩).1
  have hconsumer := physicalModelPhase_actual_fourier_certified_reference_gap_quartic_witnesses
    Uref Refs (Bselect:=Bselect) (gapLo:=gapLo) (gapHi:=gapHi) Schart
    Q K₀ rat vinv parity anchor Mat e r v s
    (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d)
    (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (F:=F) (A:=A) (W:=W) (x:=x)
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW
    (fun j hj => hx j (hSchartS hj))
    (fun j hj => hwindow j (hSchartS hj))
    (fun j hj => hden j (hSchartS hj))
    (fun j hj => hinv j (hSchartS hj))
    hchart horientation hd hBcut hs hrefSet hparentSet hsep hdenl hdenw
    (fun j hj => hwideL j (hSchartS hj))
    (fun j hj => hwideU j (hSchartS hj))
    hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth
    hchartLeft hchartRight hRQ hselectedUpper hscaleTen
    (fun j hj => hfamilyGap j (hSchartS hj))
  obtain ⟨G,hGSchart,hSchart6G,jref,hjref,xref,hxr,hrest⟩ :=
    hconsumer hSchartLarge
      (fun j hj => hlevel j (hSchartS hj))
      (fun j hj => hcolor j (hSchartS hj))
      (fun j hj => hnear j (hSchartS hj))
      hsmall hNR hRN hNcube hminscale hMatdet
      (fun j hj => hMatt j (hSchartS hj))
      (fun j hj => hMatmap j (hSchartS hj)) hMatgamma
      hNtwo (fun j hj => hL j (hSchartS hj))
      (fun j hj => hU j (hSchartS hj))
      (fun j hj => hanchor j (hSchartS hj))
      (fun j hj => hcut j (hSchartS hj))
      (fun j hj => hcount j (hSchartS hj))
  refine ⟨Schart,hSchartS,hSmass,G,hGSchart,hSchart6G,jref,hjref,xref,hxr,?_⟩
  intro Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
  have hdenregion z (hz : z∈Icc l w) (i : Fin 2) :
      d ≤ (rp i:ℝ)*z+(![s,Mat 2*v+Mat 3*s] i:ℤ) ∧
        (rp i:ℝ)*z+(![s,Mat 2*v+Mat 3*s] i:ℤ) ≤ 2*d := by
    fin_cases i
    · exact (hregion z hz).1
    · change d ≤ ((Mat 2*e+Mat 3*r:ℤ):ℝ)*z+((Mat 2*v+Mat 3*s:ℤ):ℝ) ∧
        ((Mat 2*e+Mat 3*r:ℤ):ℝ)*z+((Mat 2*v+Mat 3*s:ℤ):ℝ) ≤ 2*d
      simpa only [Int.cast_add,Int.cast_mul] using (hregion z hz).2
  obtain ⟨S₀,hS₀Schart,hSchartMass,hinside,hbound⟩ :=
    hrest hsize hD hΔ hdenregion
      (fun j hj => hSchartEnds j (hGSchart hj)) hBsize
  refine ⟨d,l,w,hd,S₀,hS₀Schart.trans hSchartS,?_,hinside,hbound⟩
  exact hSmass.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hSchartMass) 6)

                                                           
private theorem huxley_sharp_tail_source_scale
    {σ c J M N R Q : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hQ : 0 < Q)
    (hRQ : R ≤ Q) (hNR : N*R ≤ M) :
    let Vcurv := 3*J*M/(2*σ*N*R^2)
    let D := 64*σ*R^2/(c*Q)
    let C := (6*J/σ)*(64*σ/c)^2+192*σ/c
    4*Vcurv*D^2+3*D*(2+Real.log (D+1)) ≤
      C*(M*R/(N*Q))*(2+Real.log (D+1)) := by
  intro Vcurv D C
  let A := 64*σ/c
  let K := M*R/(N*Q)
  let L := 2+Real.log (D+1)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hL : 1 ≤ L := by
    have hh := Real.log_nonneg (show 1 ≤ D+1 by linarith only [hD])
    dsimp only [L]
    linarith only [hh]
  have hratio : R/Q ≤ 1 := (div_le_one₀ hQ).mpr hRQ
  have hbase : R^2/Q ≤ K := by
    apply (div_le_div_iff₀ hQ (mul_pos hN hQ)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hNR (mul_nonneg hR.le hQ.le)]
  have hfirst : 4*Vcurv*D^2 ≤ (6*J/σ)*A^2*K*L := by
    have he : 4*Vcurv*D^2=((6*J/σ)*A^2*K)*(R/Q) := by
      dsimp only [Vcurv,D,A,K]
      field_simp
      ring
    rw [he]
    exact (mul_le_mul_of_nonneg_left hratio (by positivity)).trans
      (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hL (show 0 ≤ (6*J/σ)*A^2*K by positivity))
  have hsecond : 3*D*L ≤ 3*A*K*L := by
    have he : D=A*(R^2/Q) := by dsimp only [D,A]; ring
    rw [he,←mul_assoc (3:ℝ) A]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hbase (by positivity)) (by linarith only [hL])
  have hh := add_le_add hfirst hsecond
  convert hh using 1
  dsimp only [C,A]
  ring


                                                                          
                                                                    
                                                                
theorem positive_difference_actual_minimal_anchor_sharp_tail
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
    let Vcurv := 3*J*M/(2*σ*(N:ℝ)*R^2)
    let C := (6*J/σ)*(64*σ/c)^2+192*σ/c
    (∀ i∈S, ∀ a : ℚ, (a:ℝ)∈Ioo (h (t i)-delta) (h (t i)+delta) →
      (anchor i).den ≤ a.den) →
    ∀ Q : ℕ, 2 ≤ Q →
      let High := S.filter (fun i => Q ≤ (anchor i).den)
      let D := 64*σ*R^2/(c*(Q:ℝ))
      (High.card:ℝ) ≤ 4*Vcurv*D^2+3*D*(2+Real.log (D+1)) ∧
      ((R ≤ (Q:ℝ)) → (N:ℝ)*R ≤ M →
        (High.card:ℝ) ≤ C*(M*R/((N:ℝ)*Q))*(2+Real.log (D+1)) ∧
        ∀ (L : ℤ → ℤ) (H : ℤ → ℕ), (∀ i∈S, H i ≤ N) →
          (∑ i∈High, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f n):ℂ)‖) ≤
            C*(M*R/Q)*(2+Real.log (D+1))) := by
  classical
  intro f h t delta Vcurv C hanchors Q hQ High D
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hQp : (0:ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  let eta := c/(4*σ*R^2)
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hX : 0 ≤ Vcurv := by dsimp only [Vcurv]; positivity
  have hwidth : 4*delta ≤ eta := by
    have he : 4*delta=eta/4 := by dsimp only [delta,eta]; ring
    rw [he]
    linarith only [heta]
  have hsep i (hi : i∈S) j (hj : j∈S) :
      eta*|((id i:ℤ):ℝ)-(id j:ℤ)| ≤ |h (t i)-h (t j)| := by
    let V := |h (t i)-h (t j)|
    have he : 7*(2*R^2*V/7)/(2*R^2)=V := by field_simp
    have hnear : |h (t j)-h (t i)| ≤ 7*(2*R^2*V/7)/(2*R^2) := by
      rw [he,abs_sub_comm]
    have hw := positive_difference_reference_preimage_width F
      hσ hc hη hηmax hy hf hnegative hT hM hNp hR hphase
      (hpoints i hi) (hpoints j hj) hnear
    have hgrid : |t j-t i|=(N:ℝ)*|(i:ℝ)-j| := by
      rw [abs_sub_comm (t j) (t i),←abs_of_pos hNp,←abs_mul]
      congr 1
      dsimp only [t]
      ring
    rw [hgrid] at hw
    have hmul : (N:ℝ)*|(i:ℝ)-j| ≤ (N:ℝ)*((4*σ*R^2/c)*V) := by
      convert hw using 1
      ring
    have hh := (mul_le_mul_iff_right₀ hNp).mp hmul
    calc
      _ ≤ eta*((4*σ*R^2/c)*V) := mul_le_mul_of_nonneg_left hh heta.le
      _ = _ := by dsimp only [eta,V]; field_simp
  have hscale : T/M^2=M/((N:ℝ)*R^2) := by
    apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    nlinarith only [hphase]
  have hv i (hi : i∈S) : |h (t i)| ≤ Vcurv := by
    have hh := (positive_difference_half_curvature_source_bounds F
      hσ hc hJ hη hηmax hT hM hy (hpoints i hi) hf hbound htests).2
    convert hh using 1
    calc
      Vcurv = (3*J/(2*σ))*(M/((N:ℝ)*R^2)) := by dsimp only [Vcurv]; ring
      _ = (3*J/σ)*T/(2*M^2) := by rw [←hscale]; ring
  have hmul n : (S.filter (fun i => id i=n)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact ((Finset.mem_filter.mp hi).2).trans ((Finset.mem_filter.mp hj).2).symm
  have hraw := bourgain_actual_minimal_arc_sharp_tail S id (fun i => h (t i))
    anchor 1 heta hdelta hX hwidth hmul hsep hv hanchors Q hQ
  have hD : 1/(delta*(Q:ℝ))=D := by dsimp only [delta,D]; field_simp
  rw [hD] at hraw
  simp only [Nat.cast_one,one_mul] at hraw
  refine ⟨hraw,?_⟩
  intro hRQ hNR
  have hcount := hraw.trans
    (huxley_sharp_tail_source_scale hσ hc hJ hM hNp hR hQp hRQ hNR)
  refine ⟨hcount,?_⟩
  intro L H hH
  calc
    (∑ i∈High, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f n):ℂ)‖) ≤
        ∑ _i∈High,(N:ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hn : ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f n):ℂ)‖ ≤ H i := by
        apply (norm_sum_le _ _).trans_eq
        simp
      exact hn.trans (Nat.cast_le.mpr (hH i (Finset.mem_filter.mp hi).1))
    _ = (N:ℝ)*(High.card:ℝ) := by simp only [Finset.sum_const,nsmul_eq_mul,mul_comm]
    _ ≤ (N:ℝ)*(C*(M*R/((N:ℝ)*Q))*(2+Real.log (D+1))) :=
      mul_le_mul_of_nonneg_left hcount hNp.le
    _ = _ := by field_simp


private theorem huxley_low_anchor_source_scale
    {σ c J M N R Q B : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 1 ≤ Q) (hB : 0 ≤ B) (hRQ : R ≤ Q) (hNR : N*R ≤ M) :
    let Vcurv := 3*J*M/(2*σ*N*R^2)
    let delta := c/(64*σ*R^2)
    let D := B*R^2/(c*Q)
    let C := (3*J/σ+c/(32*σ))*(B/c)^2+B/c
    D*(2*(Vcurv+delta)*D+1) ≤ C*(M*R/(N*Q)) := by
  intro Vcurv delta D C
  let E := B/c
  let K := M*R/(N*Q)
  have hQp : 0 < Q := by linarith only [hQ]
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hratio : R/Q ≤ 1 := (div_le_one₀ hQp).mpr hRQ
  have hbase : R^2/Q ≤ K := by
    apply (div_le_div_iff₀ hQp (mul_pos hN hQp)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hNR (mul_nonneg hR.le hQp.le)]
  have hsquare : R^2/Q^2 ≤ K := by
    have he : R^2/Q^2=(R^2/Q)*(1/Q) := by ring
    rw [he]
    exact (mul_le_mul_of_nonneg_left ((div_le_one₀ hQp).mpr hQ)
      (by positivity)).trans (by simpa only [mul_one] using hbase)
  have hfirst : ((3*J/σ)*E^2*K)*(R/Q) ≤ (3*J/σ)*E^2*K := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio
      (show 0 ≤ (3*J/σ)*E^2*K by positivity)
  have hsecond : ((c/(32*σ))*E^2)*(R^2/Q^2) ≤ ((c/(32*σ))*E^2)*K :=
    mul_le_mul_of_nonneg_left hsquare (by positivity)
  have hthird : E*(R^2/Q) ≤ E*K := mul_le_mul_of_nonneg_left hbase hE
  calc
    _ = ((3*J/σ)*E^2*K)*(R/Q)+((c/(32*σ))*E^2)*(R^2/Q^2)+E*(R^2/Q) := by
      dsimp only [Vcurv,delta,D,E,K]
      field_simp
      ring
    _ ≤ ((3*J/σ)*E^2*K)+((c/(32*σ))*E^2)*K+E*K := add_le_add (add_le_add hfirst hsecond) hthird
    _ = _ := by dsimp only [C,E]; ring


theorem huxley_anchor_complement_source_scale
    (Q Acut : ℕ) {σ c J M N R B : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hA : 2 ≤ Acut) (hAQ : Acut ≤ Q) (hB : 0 ≤ B)
    (hRQ : (Acut:ℝ)*R ≤ Q) (hNR : N*R ≤ M) :
    let Vcurv := 3*J*M/(2*σ*N*R^2)
    let delta := c/(64*σ*R^2)
    let Dlow := B*R^2/(c*(Q:ℝ))
    let Dhigh := 64*σ*R^2/(c*((Q/Acut+1:ℕ):ℝ))
    let Dupper := 64*σ*R^2/(c*((Q:ℝ)/Acut))
    let Ctail := (6*J/σ)*(64*σ/c)^2+192*σ/c
    let Clow := (3*J/σ+c/(32*σ))*(B/c)^2+B/c
    (4*Vcurv*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1)))+
      Dlow*(2*(Vcurv+delta)*Dlow+1) ≤
        ((Acut:ℝ)*Ctail+Clow)*(M*R/(N*Q))*(2+Real.log (Dupper+1)) := by
  intro Vcurv delta Dlow Dhigh Dupper Ctail Clow
  have hAp : 0 < Acut := by omega
  have hQp : 0 < Q := by omega
  have hAr : (0:ℝ) < Acut := Nat.cast_pos.mpr hAp
  have hQr : (0:ℝ) < Q := Nat.cast_pos.mpr hQp
  have hA1 : (1:ℝ) ≤ Acut := by exact_mod_cast (show 1 ≤ Acut by omega)
  have hQ1 : (1:ℝ) ≤ Q := by exact_mod_cast hQp
  have hthreshold : (Q:ℝ)/Acut ≤ (Q/Acut+1:ℕ) := by
    apply (div_le_iff₀ hAr).mpr
    have hh : Q < Acut*(Q/Acut+1) := Nat.lt_mul_div_succ Q hAp
    have hr : (Q:ℝ) < (Acut:ℝ)*((Q/Acut+1:ℕ):ℝ) := by exact_mod_cast hh
    simpa only [mul_comm] using hr.le
  have hRQeff : R ≤ (Q:ℝ)/Acut := (le_div_iff₀ hAr).mpr (by nlinarith only [hRQ])
  have hRQfull : R ≤ (Q:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hA1 hR.le
    nlinarith only [hh,hRQ]
  have hDhigh : 0 ≤ Dhigh := by dsimp only [Dhigh]; positivity
  have hDupper : 0 ≤ Dupper := by dsimp only [Dupper]; positivity
  have hDle : Dhigh ≤ Dupper := by
    exact div_le_div_of_nonneg_left (by positivity)
      (mul_pos hc (div_pos hQr hAr)) (mul_le_mul_of_nonneg_left hthreshold hc.le)
  have hlog : 1 ≤ 2+Real.log (Dupper+1) := by
    have hh := Real.log_nonneg (show 1 ≤ Dupper+1 by linarith only [hDupper])
    linarith only [hh]
  have hhigh :
      4*Vcurv*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1)) ≤
        (Acut:ℝ)*Ctail*(M*R/(N*Q))*(2+Real.log (Dupper+1)) := by
    have hmono :
        4*Vcurv*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1)) ≤
          4*Vcurv*Dupper^2+3*Dupper*(2+Real.log (Dupper+1)) := by
      have hX : 0 ≤ Vcurv := by dsimp only [Vcurv]; positivity
      have hlogHigh : 0 ≤ Real.log (Dhigh+1) :=
        Real.log_nonneg (by linarith only [hDhigh])
      gcongr
    have hh := hmono.trans
      (huxley_sharp_tail_source_scale hσ hc hJ hM hN hR (div_pos hQr hAr) hRQeff hNR)
    change _ ≤ Ctail*(M*R/(N*((Q:ℝ)/Acut)))*(2+Real.log (Dupper+1)) at hh
    convert hh using 1
    field_simp
  have hlow : Dlow*(2*(Vcurv+delta)*Dlow+1) ≤
      Clow*(M*R/(N*Q))*(2+Real.log (Dupper+1)) := by
    have hh := huxley_low_anchor_source_scale hσ hc hJ hM hN hR hQ1 hB hRQfull hNR
    apply hh.trans
    have hp : 0 ≤ Clow*(M*R/(N*Q)) := by dsimp only [Clow]; positivity
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hlog hp
  convert add_le_add hhigh hlow using 1
  ring


public  theorem positive_difference_near_anchor_injective
    (S : Finset ℤ) (F : ℝ → ℝ) (anchor : ℤ → ℚ)
    (N : ℕ) (s : ℝ) {σ c η y T M R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hpoints : ∀ i∈S, s+(N:ℝ)*i∈Icc M (2*M)) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    let t := fun i : ℤ => s+(N:ℝ)*i
    (∀ i∈S, |(anchor i:ℝ)-h (t i)| ≤ c/(64*σ*R^2)) →
    Set.InjOn anchor (S : Set ℤ) := by
  intro f h t hnear i hi j hj he
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hcurv : |h (t i)-h (t j)| ≤ 7*(c/(112*σ))/(2*R^2) := by
    calc
      _ = |(h (t i)-(anchor i:ℝ))+((anchor j:ℝ)-h (t j))| := by rw [he]; congr 1; ring
      _ ≤ |h (t i)-(anchor i:ℝ)|+|(anchor j:ℝ)-h (t j)| := abs_add_le _ _
      _ ≤ c/(64*σ*R^2)+c/(64*σ*R^2) := by
        rw [abs_sub_comm (h (t i)) (anchor i:ℝ)]
        exact add_le_add (hnear i hi) (hnear j hj)
      _ = _ := by ring
  have hwidth := positive_difference_reference_preimage_width F
    hσ hc hη hηmax hy hf hnegative hT hM hNp hR hphase
    (hpoints i hi) (hpoints j hj) (by simpa only [abs_sub_comm] using hcurv)
  have hw : |t j-t i| ≤ (N:ℝ)/8 := by
    convert hwidth using 1
    field_simp
    ring
  have heq : |t j-t i|=(N:ℝ)*|((j-i:ℤ):ℝ)| := by
    rw [←abs_of_pos hNp,←abs_mul]
    congr 1
    dsimp only [t]
    push_cast
    ring
  rw [heq] at hw
  have hdiff : |((j-i:ℤ):ℝ)| < 1 := by nlinarith only [hw,hNp]
  have hz : j-i=0 := Int.abs_lt_one_iff.mp (by exact_mod_cast hdiff)
  exact (sub_eq_zero.mp hz).symm

-- Generated closures: source context is replayed in the next part.
end TaoTrudgianYang2025.HuxleyRationalPhase
end
end
