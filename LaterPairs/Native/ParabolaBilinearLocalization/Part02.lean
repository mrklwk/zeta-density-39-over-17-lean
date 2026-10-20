module
public import LaterPairs.Native.ParabolaBilinearLocalization.Part01

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
open scoped ComplexConjugate
open scoped ComplexConjugate
universe v


                                                                    
                                                                          
                                                   
private theorem bourgain_physical_cloud_count_le_two_coordinate_count
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (q : ι → ℕ) (r : ι → ℤ)
    (mu ell : ι → ℝ) (M : ℕ) [NeZero M] :
    let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ell i⌋+(p:ℕ) : ℤ)
    let tau := fun i p => ((b i p:ℝ)-(q i:ℝ)*ell i)/2
    let K := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let x := fun i p =>
      (![-(r i:ℝ)*b i p/q i,-(r i:ℝ)/q i,K i,3*K i*tau i p/2] : Fin 4 → ℝ)
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let y := fun ip : ι × Fin 2 =>
      (![Int.fract (x ip.1 ip.2 0),Int.fract (x ip.1 ip.2 1),
        x ip.1 ip.2 2/Real.sqrt M,x ip.1 ip.2 3/Real.sqrt M] : Fin 4 → ℝ)
    let A : Fin 4 → ℝ :=
      ![1/(12*(M:ℝ)),1/(12*(M:ℝ)^2),(1/(M:ℝ)^2)/12,(1/(M:ℝ))/12]
    (((V ×ˢ V).filter (fun ij => ∀ e, |y ij.1 e-y ij.2 e| ≤ 2*A e)).card:ℝ) ≤
      4*((((S ×ˢ S).filter (fun ij =>
        |Int.fract (-(r ij.1:ℝ)/q ij.1)-Int.fract (-(r ij.2:ℝ)/q ij.2)| ≤ 1/(6*(M:ℝ)^2) ∧
        |K ij.1-K ij.2| ≤ Real.sqrt M/(6*(M:ℝ)^2))).card):ℝ) := by
  classical
  intro b tau K x V y A
  let P := (V ×ˢ V).filter (fun ij => ∀ e, |y ij.1 e-y ij.2 e| ≤ 2*A e)
  let R := (S ×ˢ S).filter (fun ij =>
    |Int.fract (-(r ij.1:ℝ)/q ij.1)-Int.fract (-(r ij.2:ℝ)/q ij.2)| ≤ 1/(6*(M:ℝ)^2) ∧
    |K ij.1-K ij.2| ≤ Real.sqrt M/(6*(M:ℝ)^2))
  let encode := fun ij : (ι × Fin 2) × (ι × Fin 2) =>
    ((ij.1.1,ij.2.1),(ij.1.2,ij.2.2))
  have hMr : (0:ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hroot : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMr
  let Target : Finset ((ι × ι) × (Fin 2 × Fin 2)) := R ×ˢ Finset.univ
  have hmaps : Set.MapsTo encode (P:Set ((ι × Fin 2) × (ι × Fin 2)))
      (Target:Set ((ι × ι) × (Fin 2 × Fin 2))) := by
    intro ij hij
    obtain ⟨hijV,hnear⟩ := Finset.mem_filter.mp hij
    have hi := (Finset.mem_product.mp (Finset.mem_product.mp hijV).1).1
    have hj := (Finset.mem_product.mp (Finset.mem_product.mp hijV).2).1
    change encode ij ∈ Target
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi,hj⟩,?_,?_⟩,Finset.mem_univ _⟩
    · have h1 := hnear 1
      change |Int.fract (-(r ij.1.1:ℝ)/q ij.1.1)-Int.fract (-(r ij.2.1:ℝ)/q ij.2.1)| ≤
        2*(1/(12*(M:ℝ)^2)) at h1
      convert h1 using 1
      ring
    · have h2 := hnear 2
      change |K ij.1.1/Real.sqrt M-K ij.2.1/Real.sqrt M| ≤ 2*((1/(M:ℝ)^2)/12) at h2
      rw [←sub_div,abs_div,abs_of_pos hroot] at h2
      have hh := (div_le_iff₀ hroot).mp h2
      convert hh using 1
      ring
  have hinj : Set.InjOn encode (P:Set ((ι × Fin 2) × (ι × Fin 2))) := by
    rintro ⟨⟨i,p⟩,⟨j,q⟩⟩ hi ⟨⟨i',p'⟩,⟨j',q'⟩⟩ hj he
    simp only [encode,Prod.mk.injEq] at he
    obtain ⟨⟨rfl,rfl⟩,⟨rfl,rfl⟩⟩ := he
    rfl
  have hc := Finset.card_le_card_of_injOn encode hmaps hinj
  dsimp only [Target] at hc
  rw [Finset.card_product,Finset.card_univ,Fintype.card_prod,Fintype.card_fin] at hc
  change (P.card:ℝ) ≤ 4*(R.card:ℝ)
  exact_mod_cast (by simpa only [mul_comm] using hc)

                                                                    
                                                                          
                                                                       
theorem bourgain_C4_physical_cloud_second_spacing
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ℝ → ℝ) (z : ι → ℝ) (m k p r : ι → ℤ) (q : ι → ℕ)
    (N Q Bmul : ℕ) (s : ℤ) (M : ℕ) [NeZero M] {A B L F U X lambda : ℝ}
    (hN : 0 < N) (hL : 0 < L) (hF : 0 ≤ F) (hU : 0 < U)
    (hX : 0 ≤ X) (hlambda : 0 < lambda)
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
    let ell := fun i => deriv f (m i)
    let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ell i⌋+(p:ℕ) : ℤ)
    let tau := fun i p => ((b i p:ℝ)-(q i:ℝ)*ell i)/2
    let K := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let x := fun i p =>
      (![-(r i:ℝ)*b i p/q i,-(r i:ℝ)/q i,K i,3*K i*tau i p/2] : Fin 4 → ℝ)
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let y := fun ip : ι × Fin 2 =>
      (![Int.fract (x ip.1 ip.2 0),Int.fract (x ip.1 ip.2 1),
        x ip.1 ip.2 2/Real.sqrt M,x ip.1 ip.2 3/Real.sqrt M] : Fin 4 → ℝ)
    let window : Fin 4 → ℝ :=
      ![1/(12*(M:ℝ)),1/(12*(M:ℝ)^2),(1/(M:ℝ)^2)/12,(1/(M:ℝ))/12]
    let eta := 1/(6*(M:ℝ)^2)
    let zeta := Real.sqrt M/(6*(M:ℝ)^2)
    let E := 16*U*Real.sqrt (U*(Q:ℝ)^3)*zeta+3*F/4
    let Gamma := eta*(Q:ℝ)^2
    let rho := (12*U*Real.sqrt (U*(Q:ℝ)^3)/lambda)*zeta
    (∀ i∈S, h (z i)=(p i:ℝ)/q i) →
    (∀ i∈S, |h (z i)| ≤ X) →
    (((V ×ˢ V).filter (fun ij => ∀ e, |y ij.1 e-y ij.2 e| ≤ 2*window e)).card:ℝ) ≤
      4*(4*Bmul*S.card*(1+6*U*(rho+1))+
        16*(Bmul:ℝ)^2*(2*Gamma+1)*(2*X+5)^2*
          (Gamma+48*E*(Q:ℝ)^2/L)) := by
  classical
  intro h mu ell b tau K x V y window eta zeta E Gamma rho hlevel hlevelX
  have hb := bourgain_C4_two_coordinate_second_spacing S f z m k p r q N Q Bmul s
    (eta:=eta) (zeta:=zeta) hN hL hF hU hX hlambda (by dsimp only [eta]; positivity)
    (by dsimp only [zeta]; positivity) hFL hf hthree hfour
    hz hm hround hspan hmul hq hinv hlevel hlevelX
  have hc := bourgain_physical_cloud_count_le_two_coordinate_count S q r mu ell M
  exact hc.trans (mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ) ≤ 4))

theorem exists_bourgain_C4_variable_source_common_fourier :
    ∃ C≥(1:ℝ), ∀ (ι : Type*) (S : Finset ι) (f : ι → ℝ → ℝ)
      (m : ι → ℝ) (a : ι → ℤ) (q : ι → ℕ) (N H : ι → ℕ),
      (∀ i∈S, 1≤N i) → (∀ i∈S, H i≤N i) → ∀ B D : ℝ, 0≤B → 0≤D →
      (∀ i∈S, B*(2*(N i:ℝ)+1)^4≤1) → (∀ i∈S, D*(2*(N i:ℝ)+1)^2≤1) →
      (∀ i∈S, ∀ y∈Icc (m i-(2*(N i:ℝ)+1)) (m i+(2*(N i:ℝ)+1)),
        ContDiffAt ℝ 4 (f i) y) →
      (∀ i∈S, ∀ y∈Icc (m i-(2*(N i:ℝ)+1)) (m i+(2*(N i:ℝ)+1)),
        |iteratedDeriv 4 (f i) y|≤B) →
      (∀ i∈S, |iteratedDeriv 2 (f i) (m i)/2-(a i:ℝ)/(q i:ℝ)|≤D) →
      let μ := fun i => iteratedDeriv 3 (f i) (m i)/6
      let ℓ := fun i => deriv (f i) (m i)
      (∀ i∈S, 0<q i ∧ q i≤N i ∧ IsCoprime (a i) (q i:ℤ) ∧
        0<μ i ∧ μ i*(N i:ℝ)^2≤1 ∧ 1≤μ i*(q i:ℝ)^2*N i) →
      ∀ (M : ℕ) [NeZero M], (∀ i∈S, 7*(μ i*(q i:ℝ)*(N i:ℝ)^2)≤M) →
      ∃ r : ι → ℤ, (∀ i∈S, (q i:ℤ)∣a i*r i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(r i:ℝ)*b i p/q i,-(r i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod M,
        (∑ i∈S, ‖∑ n∈Finset.Ioc (N i:ℤ) ((N i:ℤ)+H i),
          (𝐞 (f i (m i+n)):ℂ)‖) ≤
        C*((1+Real.log M)*
          (∑ i∈S, ∑ p : Fin 2,
            (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*N i)))*
            ‖∑ j : ZMod M,ZMod.stdAddChar (-(j*k))*
              fordAdditiveCharacter (∑ d,x i p d*
                (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                  Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
          ∑ i∈S, (Real.sqrt (N i)*Real.log (2*(N i:ℝ))+1/(μ i*(N i:ℝ)^2))) := by
  classical
  obtain ⟨C,hC,hsource⟩ := exists_bourgain_cubic_C4_source_entry
  let Q : ℝ := 6*(3+56*Real.pi)
  have hQ : 1≤Q := by dsimp only [Q]; linarith [Real.pi_pos]
  refine ⟨C*Q,one_le_mul_of_one_le_of_one_le hC hQ,?_⟩
  intro ι S f m a q N H hN hH B D hB hD hfourSmall hquadSmall hf hfour hcurv
    μ ℓ hscale M inst hM
  have hinv i (hi : i∈S) : ∃ r : ℤ, (q i:ℤ)∣a i*r-1 := by
    obtain ⟨r,t,he⟩ := (hscale i hi).2.2.1
    exact ⟨r,-t,by nlinarith only [he]⟩
  let r := fun i => if hi : i∈S then Classical.choose (hinv i hi) else 0
  have har i (hi : i∈S) : (q i:ℤ)∣a i*r i-1 := by
    dsimp only [r]
    rw [dite_eq_left hi]
    exact Classical.choose_spec (hinv i hi)
  refine ⟨r,har,?_⟩
  intro b τ s K x
  let Src := fun i => ‖∑ n∈Finset.Ioc (N i:ℤ) ((N i:ℤ)+H i),
    (𝐞 (f i (m i+n)):ℂ)‖
  let Main := fun i (J : ℕ) => ‖(q i:ℂ)⁻¹*∑ k∈Finset.Icc
    ⌈(q i:ℝ)*(3*μ i*(N i:ℝ)^2+ℓ i)⌉
    ⌊(q i:ℝ)*(3*μ i*((N i:ℝ)+J)^2+ℓ i)⌋,
    let u := Real.sqrt (((k:ℝ)/(q i:ℝ)-ℓ i)/(3*μ i))
    bourgainQuadraticGauss (q i) (a i) k*
      ((𝐞 ((1:ℝ)/8-2*μ i*u^3):ℂ)/(Real.sqrt (6*μ i*u):ℂ))‖
  let E := fun i => Real.sqrt (N i)*Real.log (2*(N i:ℝ))+1/(μ i*(N i:ℝ)^2)
  have hprefix i (hi : i∈S) : ∃ J : ℕ, J≤H i ∧ Src i≤C*(Main i J+E i) := by
    obtain ⟨J,hJ,hbound⟩ := hsource Unit {()} (fun _ => f i) (fun _ => m i)
      (fun _ => a i) (fun _ => q i) (N i) (H i) (hN i hi) (hH i hi)
      B D hB hD (hfourSmall i hi) (hquadSmall i hi)
      (fun _ _ => hf i hi) (fun _ _ => hfour i hi)
      (fun _ _ => hcurv i hi) (fun _ _ => hscale i hi)
    simp only [Finset.sum_singleton] at hbound
    exact ⟨J,hJ,hbound⟩
  let J := fun i => if hi : i∈S then Classical.choose (hprefix i hi) else 0
  have hJ i (hi : i∈S) : J i≤H i ∧ Src i≤C*(Main i (J i)+E i) := by
    dsimp only [J]
    rw [dite_eq_left hi]
    exact Classical.choose_spec (hprefix i hi)
  have hs : (∑ i∈S,Src i) ≤ C*((∑ i∈S,Main i (J i))+(∑ i∈S,E i)) := by
    calc
      _ ≤ ∑ i∈S,C*(Main i (J i)+E i) := Finset.sum_le_sum (fun i hi => (hJ i hi).2)
      _ = _ := by rw [←Finset.mul_sum,Finset.sum_add_distrib]
  obtain ⟨k,hk⟩ := bourgain_cubic_gauss_main_common_fourier S q N
    (fun i => N i+J i) a r μ ℓ
    (fun i hi => (hscale i hi).1) hN
    (fun i hi => by

      have hj := (hJ i hi).1
      have hh := hH i hi
      omega)
    (fun i hi => (hscale i hi).2.1)
    (fun i hi => (hscale i hi).2.2.2.1)
    (fun i hi => (hscale i hi).2.2.2.2.2) har hM
  simp only [Nat.cast_add] at hk
  refine ⟨k,?_⟩
  have hC0 : 0≤C := zero_le_one.trans hC
  have hE : 0≤∑ i∈S,E i := by
    apply Finset.sum_nonneg
    intro i hi
    have hNr : (1:ℝ)≤N i := by exact_mod_cast hN i hi
    have hlog : 0≤Real.log (2*(N i:ℝ)) := Real.log_nonneg (by linarith only [hNr])
    have hm := (hscale i hi).2.2.2.1
    dsimp only [E]
    positivity
  have hQE : (∑ i∈S,E i) ≤ Q*(∑ i∈S,E i) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hQ hE
  apply hs.trans
  have hc := mul_le_mul_of_nonneg_left (add_le_add hk hQE) hC0
  convert hc using 1
  dsimp only [Q,E]
  ring

set_option maxHeartbeats 400000 in
private theorem exists_bourgain_C4_variable_source_second_spacing_reduction
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (ι : Type v) (S : Finset ι) (f : ι → ℝ → ℝ)
      (m : ι → ℤ) (a : ι → ℤ) (q : ι → ℕ) (N H : ι → ℕ),
      (∀ i∈S, 1 ≤ N i) → (∀ i∈S, H i ≤ N i) → ∀ B D : ℝ, 0 ≤ B → 0 ≤ D →
      (∀ i∈S, B*(2*(N i:ℝ)+1)^4 ≤ 1) → (∀ i∈S, D*(2*(N i:ℝ)+1)^2 ≤ 1) →
      (∀ i∈S, ∀ y∈Icc ((m i:ℝ)-(2*(N i:ℝ)+1)) ((m i:ℝ)+(2*(N i:ℝ)+1)),
        ContDiffAt ℝ 4 (f i) y) →
      (∀ i∈S, ∀ y∈Icc ((m i:ℝ)-(2*(N i:ℝ)+1)) ((m i:ℝ)+(2*(N i:ℝ)+1)),
        |iteratedDeriv 4 (f i) y| ≤ B) →
      (∀ i∈S, |iteratedDeriv 2 (f i) (m i)/2-(a i:ℝ)/(q i:ℝ)| ≤ D) →
      let μ := fun i => iteratedDeriv 3 (f i) (m i)/6
      let ℓ := fun i => deriv (f i) (m i)
      (∀ i∈S, 0 < q i ∧ q i ≤ N i ∧ IsCoprime (a i) (q i:ℤ) ∧
        0 < μ i ∧ μ i*(N i:ℝ)^2 ≤ 1 ∧ 1 ≤ μ i*(q i:ℝ)^2*N i) →
      ∀ d : ℝ, 0 < d → (∀ i∈S, d ≤ μ i*(q i:ℝ)*N i) →
      ∀ (M : ℕ) [NeZero M], (∀ i∈S, 7*(μ i*(q i:ℝ)*(N i:ℝ)^2) ≤ M) →
      ∃ r : ι → ℤ, (∀ i∈S, (q i:ℤ)∣a i*r i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let K := fun i => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
      let x := fun i p =>
        (![-(r i:ℝ)*b i p/q i,-(r i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      let V := S ×ˢ (Finset.univ : Finset (Fin 2))
      let y := fun ip : ι × Fin 2 =>
        (![Int.fract (x ip.1 ip.2 0),Int.fract (x ip.1 ip.2 1),
          x ip.1 ip.2 2/Real.sqrt M,x ip.1 ip.2 3/Real.sqrt M] : Fin 4 → ℝ)
      let A : Fin 4 → ℝ :=
        ![1/(12*(M:ℝ)),1/(12*(M:ℝ)^2),(1/(M:ℝ)^2)/12,(1/(M:ℝ))/12]
      (∑ i∈S, ‖∑ n∈Finset.Ioc (m i+N i) (m i+N i+H i),(𝐞 (f i n):ℂ)‖)^12 ≤
        C*((2/d)^6*(1+Real.log M)^12*(M:ℝ)^((12:ℝ)+ε)*(V.card:ℝ)^10*
          (((V ×ˢ V).filter (fun ij => ∀ e,|y ij.1 e-y ij.2 e| ≤ 2*A e)).card:ℝ)+
          (∑ i∈S, (Real.sqrt (N i)*Real.log (2*(N i:ℝ))+1/(μ i*(N i:ℝ)^2)))^12) := by
  classical
  obtain ⟨F,hF,hsource⟩ := exists_bourgain_C4_variable_source_common_fourier
  obtain ⟨C₀,hC₀,hsieve⟩ := exists_bourgain_cubic_dual_source_sieve.{v} hε
  have hF0 : 0 < F := lt_of_lt_of_le zero_lt_one hF
  refine ⟨2^11*F^12*(C₀+1),by positivity,?_⟩
  intro ι S f m a q N H hN hH B D hB hD hfourSmall hquadSmall hf hfour hcurv
    μ ℓ hscale d hd hdscale M inst hM
  obtain ⟨r,hr,k,hk⟩ := hsource ι S f (fun i => (m i:ℝ)) a q N H hN hH
    B D hB hD hfourSmall hquadSmall hf hfour hcurv hscale M hM
  refine ⟨r,hr,?_⟩
  intro b τ K x V y A
  let E := ∑ i∈S, (Real.sqrt (N i)*Real.log (2*(N i:ℝ))+1/(μ i*(N i:ℝ)^2))
  let L := 1+Real.log M
  let W := Real.sqrt (2/d)
  let P := ∑ i∈S, ∑ p : Fin 2, ‖∑ j : ZMod M,ZMod.stdAddChar (-(j*k))*
    fordAdditiveCharacter (∑ e,x i p e*
      (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
        Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) e)‖
  let T := (M:ℝ)^((12:ℝ)+ε)*(V.card:ℝ)^10*
    (((V ×ˢ V).filter (fun ij => ∀ e,|y ij.1 e-y ij.2 e| ≤ 2*A e)).card:ℝ)
  let R := (2/d)^6*L^12*T
  have hL : 0 ≤ L := by
    have hM1 : (1:ℝ) ≤ M := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne M))
    have hh := Real.log_nonneg hM1
    dsimp only [L]
    linarith only [hh]
  have hW : 0 ≤ W := Real.sqrt_nonneg _
  have hP : 0 ≤ P := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hE : 0 ≤ E := by
    apply Finset.sum_nonneg
    intro i hi
    have hmu := (hscale i hi).2.2.2.1
    have hNr : (1:ℝ) ≤ N i := by exact_mod_cast hN i hi
    have hlog : 0 ≤ Real.log (2*(N i:ℝ)) := Real.log_nonneg (by linarith only [hNr])
    positivity
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hWP :
      (∑ i∈S, ∑ p : Fin 2,
        (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*N i)))*
        ‖∑ j : ZMod M,ZMod.stdAddChar (-(j*k))*
          fordAdditiveCharacter (∑ e,x i p e*
            (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
              Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) e)‖) ≤ W*P := by
    dsimp only [P]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p _
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact bourgain_dual_amplitude_coefficient_le (hscale i hi).2.2.2.1
      (by exact_mod_cast (hscale i hi).1) (by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (hN i hi)) hd (hdscale i hi)
  have hsum :
      (∑ i∈S, ‖∑ n∈Finset.Ioc (m i+N i) (m i+N i+H i),(𝐞 (f i n):ℂ)‖) ≤
        F*(L*W*P+E) := by
    calc
      _ = ∑ i∈S, ‖∑ n∈Finset.Ioc (N i:ℤ) ((N i:ℤ)+H i),
          (𝐞 (f i ((m i:ℝ)+n)):ℂ)‖ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [bourgain_integer_source_translation]
      _ ≤ _ := hk.trans (by
        apply mul_le_mul_of_nonneg_left _ hF0.le
        have hh := mul_le_mul_of_nonneg_left hWP hL
        change L*_+E ≤ L*W*P+E
        nlinarith only [hh])
  have hPs : P^12 ≤ C₀*T := by
    have hh := hsieve M ι S q N r μ ℓ
      (fun i hi => ⟨(hscale i hi).1,hN i hi,(hscale i hi).2.1,
        (hscale i hi).2.2.2.1,(hscale i hi).2.2.2.2.2⟩) hM k
    convert hh using 1
    dsimp only [T]
    ring
  have hW12 : W^12=(2/d)^6 := by
    calc
      _ = (W^2)^6 := by ring
      _ = _ := by rw [Real.sq_sqrt (by positivity : 0 ≤ 2/d)]
  have hmain : (L*W*P)^12 ≤ C₀*R := by
    rw [mul_pow,mul_pow,hW12]
    calc
      _ ≤ L^12*(2/d)^6*(C₀*T) :=
        mul_le_mul_of_nonneg_left hPs (by positivity)
      _ = _ := by dsimp only [R]; ring
  have hlast : C₀*R+E^12 ≤ (C₀+1)*(R+E^12) := by
    nlinarith only [mul_nonneg hC₀.le (pow_nonneg hE 12),hR]
  have hsource0 : 0 ≤ ∑ i∈S, ‖∑ n∈Finset.Ioc (m i+N i) (m i+N i+H i),
      (𝐞 (f i n):ℂ)‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  calc
    _ ≤ (F*(L*W*P+E))^12 := pow_le_pow_left₀ hsource0 hsum 12
    _ = F^12*(L*W*P+E)^12 := mul_pow _ _ _
    _ ≤ F^12*(2^11*((L*W*P)^12+E^12)) :=
      mul_le_mul_of_nonneg_left (add_pow_le (by positivity) hE 12) (by positivity)
    _ ≤ F^12*(2^11*(C₀*R+E^12)) := by
      gcongr
    _ ≤ F^12*(2^11*((C₀+1)*(R+E^12))) := by
      gcongr
    _ = _ := by dsimp only [R,T,L,E]; ring

set_option maxHeartbeats 400000 in
                                                                        
                                                                           
                                                            
theorem exists_bourgain_C4_prescribed_source_second_spacing
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (ι : Type v) [DecidableEq ι] (S : Finset ι)
      (f : ℝ → ℝ) (z : ι → ℝ) (m k p : ι → ℤ) (q H : ι → ℕ)
      (N Q Bmul : ℕ) (s : ℤ) (M : ℕ) [NeZero M]
      (A B L F U X lambda : ℝ),
      0 < N → 0 < Q → 0 < L → 0 ≤ F → 0 < U → 0 ≤ X → 0 < lambda →
      F ≤ L^2/16 →
      F*(6*(N:ℝ)+1)^4 ≤ 1 → (3*U/2)*(6*(N:ℝ)+1)^2 ≤ 1 →
      (∀ x∈Icc A B, ContDiffAt ℝ 4 f x) →
      (∀ x∈Icc A B, L ≤ iteratedDeriv 3 f x ∧ iteratedDeriv 3 f x ≤ 6*U) →
      (∀ x∈Icc A B, lambda ≤ |iteratedDeriv 4 f x| ∧ |iteratedDeriv 4 f x| ≤ F) →
      (∀ i∈S, z i∈Ioo A B) →
      (∀ i∈S, Icc ((m i:ℝ)-(6*(N:ℝ)+1)) ((m i:ℝ)+(6*(N:ℝ)+1)) ⊆ Icc A B) →
      (∀ i∈S, |z i-m i| ≤ 1/2) →
      (∀ i∈S, (N:ℤ) ≤ s+(N:ℤ)*k i-m i ∧ s+(N:ℤ)*k i-m i ≤ 3*(N:ℤ)) →
      (∀ j : ℤ, (S.filter (fun i => k i=j)).card ≤ Bmul) →
      (∀ i∈S, H i ≤ N) →
      (∀ i∈S, 0 < q i ∧ q i ≤ Q ∧ Q ≤ 2*q i ∧ q i ≤ N ∧ IsCoprime (p i) (q i:ℤ)) →
      (∀ i∈S, iteratedDeriv 2 f (z i)/2=(p i:ℝ)/q i) →
      (∀ i∈S, |iteratedDeriv 2 f (z i)/2| ≤ X) →
      (∀ i∈S, 1 ≤ (L/6)*(q i:ℝ)^2*N) →
      63*U*(Q:ℝ)*(N:ℝ)^2 ≤ M →
      let W := fun i => (s+(N:ℤ)*k i-m i).toNat
      let mu := fun i => iteratedDeriv 3 f (m i)/6
      let d := L*(Q:ℝ)*N/12
      let eta := 1/(6*(M:ℝ)^2)
      let zeta := Real.sqrt M/(6*(M:ℝ)^2)
      let E := 16*U*Real.sqrt (U*(Q:ℝ)^3)*zeta+3*F/4
      let Gamma := eta*(Q:ℝ)^2
      let rho := (12*U*Real.sqrt (U*(Q:ℝ)^3)/lambda)*zeta
      (∑ i∈S, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),
        (𝐞 (f n):ℂ)‖)^12 ≤
        C*((2/d)^6*(1+Real.log M)^12*(M:ℝ)^((12:ℝ)+ε)*(2*(S.card:ℝ))^10*
          (4*Bmul*S.card*(1+6*U*(rho+1))+
            16*(Bmul:ℝ)^2*(2*Gamma+1)*(2*X+5)^2*(Gamma+48*E*(Q:ℝ)^2/L))+
          (∑ i∈S, (Real.sqrt (W i)*Real.log (2*(W i:ℝ))+1/(mu i*(W i:ℝ)^2)))^12) := by
  classical
  obtain ⟨C,hC,hsource⟩ := exists_bourgain_C4_variable_source_second_spacing_reduction.{v} hε
  refine ⟨4*C,by positivity,?_⟩
  intro ι instι S f z m k p q H N Q Bmul s M instM A B L F U X lambda
    hN hQ hL hF hU hX hlambda hFL hfourSmall hquadSmall hf hthree hfour
    hz hbuffer hround hspan hmul hH hq hlevel hlevelX hminor hM
    W mu d eta zeta E Gamma rho
  have hNr : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hQr : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hW i (hi : i∈S) : N ≤ W i ∧ W i ≤ 3*N ∧ m i+(W i:ℤ)=s+(N:ℤ)*k i := by
    have hh := hspan i hi
    dsimp only [W]
    constructor
    · omega
    · constructor <;> omega
  have hWp i (hi : i∈S) : 1 ≤ W i := (Nat.succ_le_iff.mpr hN).trans (hW i hi).1
  have hWr i (hi : i∈S) : (N:ℝ) ≤ W i ∧ (W i:ℝ) ≤ 3*(N:ℝ) := by
    constructor <;> exact_mod_cast (by first | exact (hW i hi).1 | exact (hW i hi).2.1)
  have hm i (hi : i∈S) : (m i:ℝ)∈Ioo A B := by
    have hrad : 0 < 6*(N:ℝ)+1 := by positivity
    have hlo := (hbuffer i hi (left_mem_Icc.mpr (by linarith only [hrad]))).1
    have hhi := (hbuffer i hi (right_mem_Icc.mpr (by linarith only [hrad]))).2
    constructor <;> linarith only [hlo,hhi,hrad]
  have hmu i (hi : i∈S) : 0 < mu i ∧ L/6 ≤ mu i ∧ mu i ≤ U := by
    have hh := hthree (m i) ⟨(hm i hi).1.le,(hm i hi).2.le⟩
    dsimp only [mu]
    constructor
    · linarith only [hh.1,hL]
    · constructor <;> linarith only [hh.1,hh.2]
  have hbuf i (hi : i∈S) :
      Icc ((m i:ℝ)-(2*(W i:ℝ)+1)) ((m i:ℝ)+(2*(W i:ℝ)+1)) ⊆ Icc A B := by
    intro x hx
    apply hbuffer i hi
    have hw := (hWr i hi).2
    constructor <;> linarith only [hx.1,hx.2,hw]
  have hsmall i (hi : i∈S) :
      F*(2*(W i:ℝ)+1)^4 ≤ 1 ∧ (3*U/2)*(2*(W i:ℝ)+1)^2 ≤ 1 := by
    have hw : 2*(W i:ℝ)+1 ≤ 6*(N:ℝ)+1 := by linarith only [(hWr i hi).2]
    constructor
    · exact (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hw 4) hF).trans hfourSmall
    · exact (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hw 2) (by positivity)).trans hquadSmall
  have hcurv i (hi : i∈S) :
      |iteratedDeriv 2 f (m i)/2-(p i:ℝ)/q i| ≤ 3*U/2 := by
    have hh := bourgain_curvature_level_difference f hf
      (fun x hx => ⟨hL.le.trans (hthree x hx).1,(hthree x hx).2⟩)
      ⟨(hm i hi).1.le,(hm i hi).2.le⟩ ⟨(hz i hi).1.le,(hz i hi).2.le⟩
    rw [hlevel i hi,abs_sub_comm (m i:ℝ) (z i)] at hh
    have hr := mul_le_mul_of_nonneg_left (hround i hi) (show 0 ≤ 3*U by positivity)
    exact hh.trans (by linarith only [hr])
  have hscale i (hi : i∈S) :
      0 < q i ∧ q i ≤ W i ∧ IsCoprime (p i) (q i:ℤ) ∧
        0 < mu i ∧ mu i*(W i:ℝ)^2 ≤ 1 ∧ 1 ≤ mu i*(q i:ℝ)^2*W i := by
    have hd := hq i hi
    have hh := hmu i hi
    refine ⟨hd.1,hd.2.2.2.1.trans (hW i hi).1,hd.2.2.2.2,hh.1,?_,?_⟩
    · have ha : (W i:ℝ)^2 ≤ (2*(W i:ℝ)+1)^2 := by
        nlinarith only [show (0:ℝ) ≤ W i from Nat.cast_nonneg _]
      calc
        _ ≤ U*(2*(W i:ℝ)+1)^2 := mul_le_mul hh.2.2 ha (sq_nonneg _) hU.le
        _ ≤ (3*U/2)*(2*(W i:ℝ)+1)^2 := by gcongr; linarith only [hU]
        _ ≤ _ := (hsmall i hi).2
    · exact (hminor i hi).trans (mul_le_mul
        (mul_le_mul_of_nonneg_right hh.2.1 (sq_nonneg (q i:ℝ)))
        (hWr i hi).1 hNr.le (mul_nonneg hh.1.le (sq_nonneg _)))
  have hd : 0 < d := by dsimp only [d]; positivity
  have hdscale i (hi : i∈S) : d ≤ mu i*(q i:ℝ)*W i := by
    have hqr : (Q:ℝ) ≤ 2*(q i:ℝ) := by exact_mod_cast (hq i hi).2.2.1
    calc
      d = (L/6)*((Q:ℝ)/2)*N := by dsimp only [d]; ring
      _ ≤ mu i*(q i:ℝ)*W i :=
        mul_le_mul (mul_le_mul (hmu i hi).2.1 (by linarith only [hqr])
          (by positivity) (hmu i hi).1.le)
          (hWr i hi).1 hNr.le (mul_nonneg (hmu i hi).1.le (Nat.cast_nonneg _))
  have hMG i (hi : i∈S) : 7*(mu i*(q i:ℝ)*(W i:ℝ)^2) ≤ M := by
    have hqQ : (q i:ℝ) ≤ Q := by exact_mod_cast (hq i hi).2.1
    calc
      _ ≤ 7*(U*(Q:ℝ)*(3*(N:ℝ))^2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (mul_le_mul (hmu i hi).2.2 hqQ (Nat.cast_nonneg _) hU.le)
            (pow_le_pow_left₀ (Nat.cast_nonneg _) (hWr i hi).2 2)
            (sq_nonneg _) (by positivity)) (by norm_num)
      _ = 63*U*(Q:ℝ)*(N:ℝ)^2 := by ring
      _ ≤ _ := hM
  obtain ⟨r,hr,hbound⟩ := hsource ι S (fun _ => f) m p q W H hWp
    (fun i hi => (hH i hi).trans (hW i hi).1) F (3*U/2) hF (by positivity)
    (fun i hi => (hsmall i hi).1) (fun i hi => (hsmall i hi).2)
    (fun i hi x hx => hf x (hbuf i hi hx))
    (fun i hi x hx => (hfour x (hbuf i hi hx)).2) hcurv hscale d hd hdscale M hMG
  have hc := bourgain_C4_physical_cloud_second_spacing S f z m k p r q N Q Bmul s M
    hN hL hF hU hX hlambda hFL hf hthree hfour hz hm hround hspan hmul
    (fun i hi => ⟨(hq i hi).1,(hq i hi).2.1,(hq i hi).2.2.1⟩) hr hlevel hlevelX
  have hsrc :
      (∑ i∈S, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖) =
      ∑ i∈S, ‖∑ n∈Finset.Ioc (m i+W i) (m i+W i+H i),(𝐞 (f n):ℂ)‖ := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [(hW i hi).2.2]
  rw [hsrc]
  dsimp only at hbound hc
  rw [Finset.card_product,Finset.card_univ,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] at hbound
  have he : (0:ℝ) ≤ (∑ i∈S, (Real.sqrt (W i)*Real.log (2*(W i:ℝ))+
      1/(mu i*(W i:ℝ)^2)))^12 := by positivity
  have hh := mul_le_mul_of_nonneg_left hc
    (show 0 ≤ (2/d)^6*(1+Real.log M)^12*(M:ℝ)^((12:ℝ)+ε)*
      ((S.card:ℝ)*2)^10 by positivity)
  apply hbound.trans
  dsimp only [d,eta,zeta,E,Gamma,rho,mu] at *
  nlinarith only [mul_le_mul_of_nonneg_left hh hC.le,mul_nonneg hC.le he]

                                                                      
public  theorem bourgain_prescribed_source_error_le
    {N W : ℕ} {mu L : ℝ} (hN : 0 < N) (hNW : N ≤ W) (hW : W ≤ 3*N)
    (hL : 0 < L) (hmu : L/6 ≤ mu) :
    Real.sqrt W*Real.log (2*(W:ℝ))+1/(mu*(W:ℝ)^2) ≤
      Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2) := by
  have hNr : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hNW' : (N:ℝ) ≤ W := by exact_mod_cast hNW
  have hW' : (W:ℝ) ≤ 3*(N:ℝ) := by exact_mod_cast hW
  have hWp : (0:ℝ) < W := hNr.trans_le hNW'
  have hmul : 0 < mu := by linarith only [hL,hmu]
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (2*(W:ℝ)) := Real.log_nonneg (by linarith only [hN1,hNW'])
  have hlogs : Real.log (2*(W:ℝ)) ≤ Real.log (6*(N:ℝ)) :=
    Real.log_le_log (by positivity) (by linarith only [hW'])
  apply add_le_add (mul_le_mul (Real.sqrt_le_sqrt hW') hlogs hlog
    (Real.sqrt_nonneg _))
  have hden : (L/6)*(N:ℝ)^2 ≤ mu*(W:ℝ)^2 :=
    mul_le_mul hmu (pow_le_pow_left₀ hNr.le hNW' 2) (sq_nonneg _) hmul.le
  calc
    _ ≤ 1/((L/6)*(N:ℝ)^2) :=
      one_div_le_one_div_of_le (by positivity) hden
    _ = _ := by field_simp


set_option maxHeartbeats 400000 in
private theorem bourgain_exists_minimal_denominator_in_arc
    {a b : ℝ} (hab : a < b) :
    ∃ r : ℚ, (r:ℝ)∈Ioo a b ∧
      ∀ t : ℚ, (t:ℝ)∈Ioo a b → r.den ≤ t.den := by
  classical
  obtain ⟨t,hat,htb⟩ := exists_rat_btwn hab
  let P : ℕ → Prop := fun n => ∃ r : ℚ, r.den=n ∧ (r:ℝ)∈Ioo a b
  have hex : ∃ n,P n := ⟨t.den,t,rfl,hat,htb⟩
  obtain ⟨r,hrden,hr⟩ := Nat.find_spec hex
  refine ⟨r,hr,?_⟩
  intro u hu
  rw [hrden]
  exact Nat.find_min' hex ⟨u,rfl,hu⟩

private theorem bourgain_minimal_arc_dirichlet_compression
    {xi delta : ℝ} (hdelta : 0 < delta) (Q : ℕ) (hQ : 2 ≤ Q)
    (r : ℚ)
    (hminimal : ∀ t : ℚ, (t:ℝ)∈Ioo (xi-delta) (xi+delta) → r.den ≤ t.den)
    (hrQ : Q ≤ r.den) :
    ∃ a : ℚ, 0 < a.den ∧ a.den < Q ∧
      (a.den:ℝ) ≤ 1/(delta*(Q:ℝ)) ∧
      |xi-(a:ℝ)| ≤ 1/((Q:ℝ)*a.den) := by
  obtain ⟨a,ha,haden⟩ := Real.exists_rat_abs_sub_le_and_den_le xi
    (n:=Q-1) (by omega)
  have hQpred : ((Q-1:ℕ):ℝ)+1=Q := by
    have hh : Q-1+1=Q := by omega
    exact_mod_cast hh
  rw [hQpred] at ha
  have haQ : a.den < Q := by omega
  have hfar : delta ≤ |xi-(a:ℝ)| := by
    by_contra! hh
    have ht := abs_lt.mp hh
    have hinside : (a:ℝ)∈Ioo (xi-delta) (xi+delta) := by
      constructor <;> linarith only [ht.1,ht.2]
    have hm := hminimal a hinside
    omega
  have hQp : (0:ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hadp : (0:ℝ) < a.den := Nat.cast_pos.mpr a.pos
  refine ⟨a,a.pos,haQ,?_,ha⟩
  have hh := (le_div_iff₀ (mul_pos hQp hadp)).mp (hfar.trans ha)
  apply (le_div_iff₀ (mul_pos hdelta hQp)).mpr
  nlinarith only [hh]

private theorem bourgain_separated_level_band_count
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (k : ι → ℤ) (v : ι → ℝ)
    (B : ℕ) {eta a w : ℝ} (heta : 0 < eta) (hw : 0 ≤ w)
    (hmul : ∀ n : ℤ, (S.filter (fun i => k i=n)).card ≤ B)
    (hsep : ∀ i∈S, ∀ j∈S, eta*|(k i:ℝ)-k j| ≤ |v i-v j|) :
    ((S.filter (fun i => |v i-a| ≤ w)).card:ℝ) ≤
      B*(4*w/eta+1) := by
  classical
  let T := S.filter (fun i => |v i-a| ≤ w)
  by_cases hempty : T=∅
  · change (T.card:ℝ) ≤ _
    rw [hempty,Finset.card_empty,Nat.cast_zero]
    positivity
  obtain ⟨i₀,hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hTsub : T ⊆ S := Finset.filter_subset _ _
  have hnear i (hi : i∈T) : |(k i:ℝ)-k i₀| ≤ 2*w/eta := by
    have hpair := hsep i (hTsub hi) i₀ (hTsub hi₀)
    have hdist : |v i-v i₀| ≤ 2*w := by
      have hh := abs_sub_le (v i) a (v i₀)
      rw [abs_sub_comm a (v i₀)] at hh
      linarith only [hh,(Finset.mem_filter.mp hi).2,(Finset.mem_filter.mp hi₀).2]
    apply (le_div_iff₀ heta).mpr
    nlinarith only [hpair,hdist]
  have himage : ((T.image k).card:ℝ) ≤ 4*w/eta+1 := by
    have hb := integer_card_le_of_abs_sub_le (T.image k) (a:=(k i₀:ℝ))
      (B:=2*w/eta) (by positivity) (by
        intro n hn
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hn
        exact hnear i hi)
    convert hb using 1
    ring
  have hcard : T.card ≤ (T.image k).card*B := by
    calc
      _ = ∑ n∈T.image k,(T.filter (fun i => k i=n)).card :=
        Finset.card_eq_sum_card_image k T
      _ ≤ ∑ _n∈T.image k,B := by
        apply Finset.sum_le_sum
        intro n hn
        exact (Finset.card_le_card (Finset.filter_subset_filter _ hTsub)).trans (hmul n)
      _ = _ := by simp
  change (T.card:ℝ) ≤ _
  calc
    _ ≤ ((T.image k).card:ℝ)*B := by exact_mod_cast hcard
    _ ≤ (4*w/eta+1)*B := mul_le_mul_of_nonneg_right himage (Nat.cast_nonneg _)
    _ = _ := mul_comm _ _

private theorem bourgain_rational_neighborhood_block_count_sharp
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (k : ι → ℤ)
    (v : ι → ℝ) (a : ι → ℚ) (J Q B : ℕ) {eta X : ℝ}
    (heta : 0 < eta) (hQ : 0 < Q) (hX : 0 ≤ X)
    (hmul : ∀ n : ℤ, (S.filter (fun i => k i=n)).card ≤ B)
    (hsep : ∀ i∈S, ∀ j∈S, eta*|(k i:ℝ)-k j| ≤ |v i-v j|)
    (hv : ∀ i∈S, |v i| ≤ X)
    (hden : ∀ i∈S, (a i).den ≤ J)
    (hnear : ∀ i∈S, |v i-(a i:ℝ)| ≤ 1/((Q:ℝ)*(a i).den)) :
    (S.card:ℝ) ≤ B*∑ q∈Finset.Icc 1 J,
      (2*X*(q:ℝ)+3)*(4/(eta*(Q:ℝ)*q)+1) := by
  classical
  have hQr : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hQ1 : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  have hnum i (hi : i∈S) : |((a i).num:ℝ)| ≤ X*(a i).den+1 := by
    have hd : (0:ℝ) < (a i).den := Nat.cast_pos.mpr (a i).pos
    have hval : |(a i:ℝ)| ≤ X+1/((Q:ℝ)*(a i).den) := by
      have hh := abs_add_le (v i) ((a i:ℝ)-v i)
      rw [add_sub_cancel,abs_sub_comm (a i:ℝ) (v i)] at hh
      linarith only [hh,hv i hi,hnear i hi]
    rw [Rat.cast_def,abs_div,abs_of_pos hd] at hval
    have hh := (div_le_iff₀ hd).mp hval
    have he : (X+1/((Q:ℝ)*(a i).den))*(a i).den=X*(a i).den+1/(Q:ℝ) := by
      field_simp
    rw [he] at hh
    have hinv : 1/(Q:ℝ) ≤ 1 := (div_le_one₀ hQr).mpr hQ1
    linarith only [hh,hinv]
  have hfiber (q : ℕ) (hq : q∈Finset.Icc 1 J) :
      ((S.filter (fun i => (a i).den=q)).card:ℝ) ≤
        (2*X*(q:ℝ)+3)*(B*(4/(eta*(Q:ℝ)*q)+1)) := by
    let T := S.filter (fun i => (a i).den=q)
    let W := T.image (fun i => (a i).num)
    have hqpos : 0 < q := by have hh := Finset.mem_Icc.mp hq; omega
    have hqr : (0:ℝ) < q := Nat.cast_pos.mpr hqpos
    have hW : (W.card:ℝ) ≤ 2*X*(q:ℝ)+3 := by
      have hh := integer_card_le_of_abs_sub_le W (a:=0) (B:=X*(q:ℝ)+1)
        (by positivity) (by
          intro p hp
          obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
          obtain ⟨hiS,he⟩ := Finset.mem_filter.mp hi
          simpa only [sub_zero,he] using hnum i hiS)
      convert hh using 1
      ring
    have hpcount p (hp : p∈W) :
        ((T.filter (fun i => (a i).num=p)).card:ℝ) ≤
          B*(4/(eta*(Q:ℝ)*q)+1) := by
      have hsub : T.filter (fun i => (a i).num=p) ⊆
          S.filter (fun i => |v i-(p:ℝ)/q| ≤ 1/((Q:ℝ)*q)) := by
        intro i hi
        obtain ⟨hiT,he⟩ := Finset.mem_filter.mp hi
        obtain ⟨hiS,hd⟩ := Finset.mem_filter.mp hiT
        refine Finset.mem_filter.mpr ⟨hiS,?_⟩
        simpa only [Rat.cast_def,he,hd] using hnear i hiS
      have hb := bourgain_separated_level_band_count S k v B heta
        (w:=1/((Q:ℝ)*q)) (a:=(p:ℝ)/q) (by positivity) hmul hsep
      have hc := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hb
      convert hc using 1
      ring
    calc
      _ = ∑ p∈W,((T.filter (fun i => (a i).num=p)).card:ℝ) := by
        exact_mod_cast Finset.card_eq_sum_card_image (fun i => (a i).num) T
      _ ≤ ∑ _p∈W,B*(4/(eta*(Q:ℝ)*q)+1) :=
        Finset.sum_le_sum (fun p hp => hpcount p hp)
      _ = (W.card:ℝ)*(B*(4/(eta*(Q:ℝ)*q)+1)) := by
        simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hW (by positivity)
  have hcard : S.card=∑ q∈Finset.Icc 1 J,(S.filter (fun i => (a i).den=q)).card :=
    Finset.card_eq_sum_card_fiberwise (fun i hi =>
      Finset.mem_Icc.mpr ⟨(a i).pos,hden i hi⟩)
  calc
    _ = ∑ q∈Finset.Icc 1 J,((S.filter (fun i => (a i).den=q)).card:ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ q∈Finset.Icc 1 J,
        (2*X*(q:ℝ)+3)*(B*(4/(eta*(Q:ℝ)*q)+1)) :=
      Finset.sum_le_sum hfiber
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q hq; ring


private theorem bourgain_rational_neighborhood_block_count
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (k : ι → ℤ)
    (v : ι → ℝ) (a : ι → ℚ) (J Q B : ℕ) {eta X : ℝ}
    (heta : 0 < eta) (hQ : 0 < Q) (hX : 0 ≤ X)
    (hmul : ∀ n : ℤ, (S.filter (fun i => k i=n)).card ≤ B)
    (hsep : ∀ i∈S, ∀ j∈S, eta*|(k i:ℝ)-k j| ≤ |v i-v j|)
    (hv : ∀ i∈S, |v i| ≤ X)
    (hden : ∀ i∈S, (a i).den ≤ J)
    (hnear : ∀ i∈S, |v i-(a i:ℝ)| ≤ 1/((Q:ℝ)*(a i).den)) :
    (S.card:ℝ) ≤ B*∑ q∈Finset.Icc 1 J,
      (2*(X+1)*(q:ℝ)+1)*(4/(eta*(Q:ℝ)*q)+1) := by
  classical
  have hh := bourgain_rational_neighborhood_block_count_sharp S k v a J Q B
    heta hQ hX hmul hsep hv hden hnear
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg B)
  apply Finset.sum_le_sum
  intro q hq
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
  nlinarith only [hq1]


                                                                 
                                                                         
                                    
theorem bourgain_actual_minimal_arc_sharp_tail
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (k : ι → ℤ)
    (v : ι → ℝ) (r : ι → ℚ) (B : ℕ) {eta delta X : ℝ}
    (heta : 0 < eta) (hdelta : 0 < delta) (hX : 0 ≤ X)
    (hwidth : 4*delta ≤ eta)
    (hmul : ∀ n : ℤ, (S.filter (fun i => k i=n)).card ≤ B)
    (hsep : ∀ i∈S, ∀ j∈S, eta*|(k i:ℝ)-k j| ≤ |v i-v j|)
    (hv : ∀ i∈S, |v i| ≤ X)
    (hminimal : ∀ i∈S, ∀ a : ℚ,
      (a:ℝ)∈Ioo (v i-delta) (v i+delta) → (r i).den ≤ a.den) :
    ∀ Q : ℕ, 2 ≤ Q →
      let D := 1/(delta*(Q:ℝ))
      ((S.filter (fun i => Q ≤ (r i).den)).card:ℝ) ≤
        B*(4*X*D^2+3*D*(2+Real.log (D+1))) := by
  classical
  intro Q hQ D
  let G := S.filter (fun i => Q ≤ (r i).den)
  let J := ⌊D⌋₊
  have hGsub : G ⊆ S := Finset.filter_subset _ _
  have hQp : 0 < Q := by omega
  have hQr : (0:ℝ) < Q := Nat.cast_pos.mpr hQp
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hJ : (J:ℝ) ≤ D := Nat.floor_le hD
  have hex i : ∃ a : ℚ, i∈G →
      0 < a.den ∧ a.den < Q ∧ (a.den:ℝ) ≤ D ∧
        |v i-(a:ℝ)| ≤ 1/((Q:ℝ)*a.den) := by
    by_cases hi : i∈G
    · obtain ⟨a,ha⟩ := bourgain_minimal_arc_dirichlet_compression hdelta Q hQ
        (r i) (hminimal i (hGsub hi)) (Finset.mem_filter.mp hi).2
      exact ⟨a,fun _ => ha⟩
    · exact ⟨0,fun hh => False.elim (hi hh)⟩
  choose a ha using hex
  have hden i (hi : i∈G) : (a i).den ≤ J :=
    (Nat.le_floor_iff' (a i).pos.ne').mpr (ha i hi).2.2.1
  have hmulG n : (G.filter (fun i => k i=n)).card ≤ B :=
    (Finset.card_le_card (Finset.filter_subset_filter _ hGsub)).trans (hmul n)
  have hb := bourgain_rational_neighborhood_block_count_sharp G k v a J Q B
    heta hQp hX hmulG
    (fun i hi j hj => hsep i (hGsub hi) j (hGsub hj))
    (fun i hi => hv i (hGsub hi)) hden
    (fun i hi => (ha i hi).2.2.2)
  have hE : 4/(eta*(Q:ℝ)) ≤ D := by
    apply (div_le_div_iff₀ (mul_pos heta hQr) (mul_pos hdelta hQr)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hwidth hQr.le]
  have hlog : Real.log (J:ℝ) ≤ Real.log (D+1) := by
    by_cases hzero : J=0
    · rw [hzero,Nat.cast_zero,Real.log_zero]
      exact Real.log_nonneg (by linarith only [hD])
    · exact Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hzero))
        (by linarith only [hJ])
  have hharm : (∑ q∈Finset.Icc 1 J,1/(q:ℝ)) ≤ 1+Real.log (D+1) := by
    have hh : (∑ q∈Finset.Icc 1 J,1/(q:ℝ)) ≤ 1+Real.log J := by
      simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,
        Rat.cast_natCast,one_div] using harmonic_le_one_add_log J
    linarith only [hh,hlog]
  have hcard : (Finset.Icc 1 J).card=J := by simp
  have hlinear : (∑ q∈Finset.Icc 1 J,(2*X*(q:ℝ)+3)) ≤ (2*X*D+3)*D := by
    calc
      _ ≤ ∑ _q∈Finset.Icc 1 J,(2*X*D+3) := by
        apply Finset.sum_le_sum
        intro q hq
        have hqD : (q:ℝ) ≤ D := (Nat.cast_le.mpr (Finset.mem_Icc.mp hq).2).trans hJ
        nlinarith only [mul_nonneg hX (sub_nonneg.mpr hqD)]
      _ = (2*X*D+3)*(J:ℝ) := by simp only [Finset.sum_const,nsmul_eq_mul,hcard,mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left hJ (by positivity)
  have heq q (hq : q∈Finset.Icc 1 J) :
      (2*X*(q:ℝ)+3)*(4/(eta*(Q:ℝ)*q)+1)=
        (2*X*(q:ℝ)+3)+(4/(eta*(Q:ℝ)))*(2*X+3/(q:ℝ)) := by
    have hqp : (0:ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
    field_simp
    ring
  have hsum :
      (∑ q∈Finset.Icc 1 J,(2*X*(q:ℝ)+3)*(4/(eta*(Q:ℝ)*q)+1)) ≤
        4*X*D^2+3*D*(2+Real.log (D+1)) := by
    calc
      _ = (∑ q∈Finset.Icc 1 J,(2*X*(q:ℝ)+3))+
          (4/(eta*(Q:ℝ)))*(2*X*J+3*∑ q∈Finset.Icc 1 J,1/(q:ℝ)) := by
        rw [Finset.sum_congr rfl heq]
        simp only [Finset.sum_add_distrib,div_eq_mul_inv,←Finset.mul_sum,
          Finset.sum_const,nsmul_eq_mul,hcard]
        ring
      _ ≤ (2*X*D+3)*D+D*(2*X*D+3*(1+Real.log (D+1))) := by
        apply add_le_add hlinear
        apply (mul_le_mul_of_nonneg_right hE (by positivity)).trans
        apply mul_le_mul_of_nonneg_left _ hD
        nlinarith only [hharm,mul_nonneg hX (sub_nonneg.mpr hJ)]
      _ = _ := by ring
  exact hb.trans (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg B))

private theorem bourgain_rational_neighborhood_sum_bound
    (J Q : ℕ) {eta X : ℝ} (heta : 0 < eta) (hQ : 0 < Q) (hX : 0 ≤ X) :
    (∑ q∈Finset.Icc 1 J,
      (2*(X+1)*(q:ℝ)+1)*(4/(eta*(Q:ℝ)*q)+1)) ≤
      (2*(X+1)*(J:ℝ)+1)*J+
        (4/(eta*(Q:ℝ)))*(2*(X+1)*J+1+Real.log J) := by
  have hQr : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hharm : (∑ q∈Finset.Icc 1 J,1/(q:ℝ)) ≤ 1+Real.log J := by
    simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,
      Rat.cast_natCast,one_div] using harmonic_le_one_add_log J
  have hcard : (Finset.Icc 1 J).card=J := by simp
  have hlinear : (∑ q∈Finset.Icc 1 J,(2*(X+1)*(q:ℝ)+1)) ≤
      (2*(X+1)*(J:ℝ)+1)*J := by
    calc
      _ ≤ ∑ _q∈Finset.Icc 1 J,(2*(X+1)*(J:ℝ)+1) := by
        apply Finset.sum_le_sum
        intro q hq
        have hh : (q:ℝ) ≤ J := by exact_mod_cast (Finset.mem_Icc.mp hq).2
        nlinarith only [hh,mul_nonneg (by linarith only [hX] : 0 ≤ 2*(X+1))
          (sub_nonneg.mpr hh)]
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,hcard]; ring
  have heq q (hq : q∈Finset.Icc 1 J) :
      (2*(X+1)*(q:ℝ)+1)*(4/(eta*(Q:ℝ)*q)+1)=
        (2*(X+1)*(q:ℝ)+1)+(4/(eta*(Q:ℝ)))*(2*(X+1)+1/(q:ℝ)) := by
    have hqp : (0:ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
    field_simp
    ring
  calc
    _ = (∑ q∈Finset.Icc 1 J,(2*(X+1)*(q:ℝ)+1))+
        (4/(eta*(Q:ℝ)))*(2*(X+1)*J+∑ q∈Finset.Icc 1 J,1/(q:ℝ)) := by
      rw [Finset.sum_congr rfl heq]
      simp only [Finset.sum_add_distrib,←Finset.mul_sum,
        Finset.sum_const,nsmul_eq_mul,hcard]
      ring
    _ ≤ _ := by
      apply add_le_add hlinear
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith only [hharm]

private theorem exists_bourgain_minimal_arc_family_count
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (k : ι → ℤ)
    (v : ι → ℝ) (B : ℕ) {eta delta X : ℝ}
    (heta : 0 < eta) (hdelta : 0 < delta) (hX : 0 ≤ X)
    (hmul : ∀ n : ℤ, (S.filter (fun i => k i=n)).card ≤ B)
    (hsep : ∀ i∈S, ∀ j∈S, eta*|(k i:ℝ)-k j| ≤ |v i-v j|)
    (hv : ∀ i∈S, |v i| ≤ X) :
    ∃ r : ι → ℚ,
      (∀ i, (r i:ℝ)∈Ioo (v i-delta) (v i+delta) ∧
        ∀ t : ℚ, (t:ℝ)∈Ioo (v i-delta) (v i+delta) → (r i).den ≤ t.den) ∧
      ∀ Q : ℕ, 2 ≤ Q →
        let G := S.filter (fun i => Q ≤ (r i).den)
        let J := ⌊1/(delta*(Q:ℝ))⌋₊
        (G.card:ℝ) ≤ B*((2*(X+1)*(J:ℝ)+1)*J+
          (4/(eta*(Q:ℝ)))*(2*(X+1)*J+1+Real.log J)) := by
  classical
  choose r hr using fun i : ι => bourgain_exists_minimal_denominator_in_arc
    (a:=v i-delta) (b:=v i+delta) (by linarith only [hdelta])
  refine ⟨r,hr,?_⟩
  intro Q hQ G J
  have hGsub : G ⊆ S := Finset.filter_subset _ _
  have hex i : ∃ a : ℚ, i∈G →
      0 < a.den ∧ a.den < Q ∧ (a.den:ℝ) ≤ 1/(delta*(Q:ℝ)) ∧
        |v i-(a:ℝ)| ≤ 1/((Q:ℝ)*a.den) := by
    by_cases hi : i∈G
    · obtain ⟨a,ha⟩ := bourgain_minimal_arc_dirichlet_compression hdelta Q hQ
        (r i) (hr i).2 (Finset.mem_filter.mp hi).2
      exact ⟨a,fun _ => ha⟩
    · exact ⟨0,fun hh => False.elim (hi hh)⟩
  choose a ha using hex
  have hden i (hi : i∈G) : (a i).den ≤ J := by
    exact (Nat.le_floor_iff' (a i).pos.ne').mpr (ha i hi).2.2.1
  have hmulG n : (G.filter (fun i => k i=n)).card ≤ B :=
    (Finset.card_le_card (Finset.filter_subset_filter _ hGsub)).trans (hmul n)
  have hQp : 0 < Q := by omega
  have hb := bourgain_rational_neighborhood_block_count G k v a J Q B
    heta hQp hX hmulG
    (fun i hi j hj => hsep i (hGsub hi) j (hGsub hj))
    (fun i hi => hv i (hGsub hi)) hden
    (fun i hi => (ha i hi).2.2.2)
  exact hb.trans (mul_le_mul_of_nonneg_left
    (bourgain_rational_neighborhood_sum_bound J Q heta hQp hX) (Nat.cast_nonneg B))

private theorem bourgain_curvature_lower_difference
    (f : ℝ → ℝ) {A B x y L : ℝ}
    (hf : ∀ z∈Icc A B, ContDiffAt ℝ 3 f z)
    (hthree : ∀ z∈Icc A B, L ≤ iteratedDeriv 3 f z)
    (hx : x∈Icc A B) (hy : y∈Icc A B) (hxy : x ≤ y) :
    (L/2)*(y-x) ≤ iteratedDeriv 2 f y/2-iteratedDeriv 2 f x/2 := by
  rcases hxy.eq_or_lt with rfl | hxy
  · simp
  have hsub : Icc x y ⊆ Icc A B := fun z hz => ⟨hx.1.trans hz.1,hz.2.trans hy.2⟩
  have hd z (hz : z∈Icc x y) :
      HasDerivAt (fun w => iteratedDeriv 2 f w/2) (iteratedDeriv 3 f z/2) z := by
    have hh := contDiffAt_iteratedDeriv_finite (n:=1) (j:=2) (hf z (hsub hz))
    have he : HasDerivAt (iteratedDeriv 2 f) (iteratedDeriv 3 f z) z := by
      simpa only [iteratedDeriv_succ] using hh.differentiableAt_one.hasDerivAt
    exact he.div_const 2
  obtain ⟨z,hz,he⟩ := exists_hasDerivAt_eq_slope
    (fun w => iteratedDeriv 2 f w/2) (fun w => iteratedDeriv 3 f w/2) hxy
    (fun w hw => (hd w hw).continuousAt.continuousWithinAt)
    (fun w hw => hd w ⟨hw.1.le,hw.2.le⟩)
  have hb : L/2 ≤ iteratedDeriv 3 f z/2 := by
    linarith only [hthree z (hsub ⟨hz.1.le,hz.2.le⟩)]
  rw [he] at hb
  exact (le_div_iff₀ (sub_pos.mpr hxy)).mp hb

private theorem bourgain_minimal_arc_floor_budget
    {D X : ℝ} (hD : 0 ≤ D) (hX : 0 ≤ X) :
    let J := ⌊D⌋₊
    (2*(X+1)*(J:ℝ)+1)*J+D*(2*(X+1)*J+1+Real.log J) ≤
      4*(X+1)*D^2+D*(2+Real.log (D+1)) := by
  intro J
  have hJ : (J:ℝ) ≤ D := Nat.floor_le hD
  have hJ0 : (0:ℝ) ≤ J := Nat.cast_nonneg _
  have hlog : Real.log (J:ℝ) ≤ Real.log (D+1) := by
    by_cases hzero : J=0
    · rw [hzero,Nat.cast_zero,Real.log_zero]
      exact Real.log_nonneg (by linarith only [hD])
    · exact Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hzero))
        (by linarith only [hJ])
  have hc : 0 ≤ 2*(X+1) := by positivity
  have hfirst : (2*(X+1)*(J:ℝ)+1)*J ≤ (2*(X+1)*D+1)*D :=
    mul_le_mul (by nlinarith only [mul_nonneg hc (sub_nonneg.mpr hJ)])
      hJ hJ0 (by positivity)
  have hsecond := mul_le_mul_of_nonneg_left
    (show 2*(X+1)*(J:ℝ)+1+Real.log J ≤ 2*(X+1)*D+1+Real.log (D+1) by
      nlinarith only [mul_nonneg hc (sub_nonneg.mpr hJ),hlog]) hD
  nlinarith only [hfirst,hsecond]

set_option maxHeartbeats 400000 in
                                                                       
                                                                         
                                                            
theorem exists_bourgain_C3_minimal_curvature_arc_count
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ℝ → ℝ)
    (k : ι → ℤ) (N Bmul : ℕ) (s : ℝ) {A B L X : ℝ}
    (hN : 0 < N) (hL : 0 < L) (hX : 0 ≤ X)
    (hf : ∀ x∈Icc A B, ContDiffAt ℝ 3 f x)
    (hthree : ∀ x∈Icc A B, L ≤ iteratedDeriv 3 f x)
    (hmul : ∀ n : ℤ, (S.filter (fun i => k i=n)).card ≤ Bmul) :
    let t := fun i => s+(N:ℝ)*(k i:ℝ)
    let v := fun i => iteratedDeriv 2 f (t i)/2
    let delta := L*(N:ℝ)/8
    (∀ i∈S, Icc (t i-(N:ℝ)/4) (t i+(N:ℝ)/4) ⊆ Icc A B) →
    (∀ i∈S, |v i| ≤ X) →
    ∃ (r : ι → ℚ) (z : ι → ℝ),
      (∀ i∈S, z i∈Ioo (t i-(N:ℝ)/4) (t i+(N:ℝ)/4) ∧
        iteratedDeriv 2 f (z i)/2=(r i:ℝ) ∧
        (r i:ℝ)∈Ioo (v i-delta) (v i+delta) ∧
        ∀ a : ℚ, (a:ℝ)∈Ioo (v i-delta) (v i+delta) → (r i).den ≤ a.den) ∧
      ∀ Q : ℕ, 2 ≤ Q →
        let G := S.filter (fun i => Q ≤ (r i).den)
        let D := 8/(L*(N:ℝ)*(Q:ℝ))
        (G.card:ℝ) ≤ Bmul*(4*(X+1)*D^2+D*(2+Real.log (D+1))) := by
  classical
  intro t v delta hbuffer hv
  have hNr : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have ht i (hi : i∈S) : t i∈Icc A B :=
    hbuffer i hi ⟨by linarith only [hNr],by linarith only [hNr]⟩
  have hsep : ∀ i∈S, ∀ j∈S, (L*(N:ℝ)/2)*|(k i:ℝ)-k j| ≤ |v i-v j| := by
    have hordered i (hi : i∈S) j (hj : j∈S) (hij : t i ≤ t j) :
        (L*(N:ℝ)/2)*|(k i:ℝ)-k j| ≤ |v i-v j| := by
      have hc := bourgain_curvature_lower_difference f hf hthree (ht i hi) (ht j hj) hij
      have hki : (k i:ℝ) ≤ k j := by
        apply (mul_le_mul_iff_right₀ hNr).mp
        dsimp only [t] at hij
        linarith only [hij]
      have hvij : v i ≤ v j := by
        change (L/2)*(t j-t i) ≤ v j-v i at hc
        have hp := mul_nonneg (by positivity : 0 ≤ L/2) (sub_nonneg.mpr hij)
        linarith only [hc,hp]
      rw [abs_of_nonpos (sub_nonpos.mpr hki),abs_of_nonpos (sub_nonpos.mpr hvij)]
      dsimp only [t] at hc
      change (L/2)*((s+(N:ℝ)*(k j:ℝ))-(s+(N:ℝ)*(k i:ℝ))) ≤ v j-v i at hc
      nlinarith only [hc]
    intro i hi j hj
    rcases le_total (t i) (t j) with hij | hji
    · exact hordered i hi j hj hij
    · simpa only [abs_sub_comm] using hordered j hj i hi hji
  obtain ⟨r,hr,hcount⟩ := exists_bourgain_minimal_arc_family_count S k v Bmul
    (eta:=L*(N:ℝ)/2) (by positivity) hdelta hX hmul hsep hv
  have hex i : ∃ z : ℝ, i∈S →
      z∈Ioo (t i-(N:ℝ)/4) (t i+(N:ℝ)/4) ∧
        iteratedDeriv 2 f z/2=(r i:ℝ) := by
    by_cases hi : i∈S
    · have hlo : t i-(N:ℝ)/4∈Icc A B :=
        hbuffer i hi (left_mem_Icc.mpr (by linarith only [hNr]))
      have hhi : t i+(N:ℝ)/4∈Icc A B :=
        hbuffer i hi (right_mem_Icc.mpr (by linarith only [hNr]))
      have hleft := bourgain_curvature_lower_difference f hf hthree hlo (ht i hi)
        (by linarith only [hNr])
      have hright := bourgain_curvature_lower_difference f hf hthree (ht i hi) hhi
        (by linarith only [hNr])
      have hlevel : (r i:ℝ)∈Ioo
          (iteratedDeriv 2 f (t i-(N:ℝ)/4)/2)
          (iteratedDeriv 2 f (t i+(N:ℝ)/4)/2) := by
        have hh := (hr i).1
        dsimp only [v,delta] at hh
        constructor <;> nlinarith only [hleft,hright,hh.1,hh.2]
      have hcont : ContinuousOn (fun x => iteratedDeriv 2 f x/2)
          (Icc (t i-(N:ℝ)/4) (t i+(N:ℝ)/4)) := by
        intro x hx
        have hh := contDiffAt_iteratedDeriv_finite (n:=1) (j:=2) (hf x (hbuffer i hi hx))
        exact (hh.continuousAt.div_const 2).continuousWithinAt
      obtain ⟨z,hz,he⟩ := intermediate_value_Ioo
        (by linarith only [hNr] : t i-(N:ℝ)/4 ≤ t i+(N:ℝ)/4) hcont hlevel
      exact ⟨z,fun _ => ⟨hz,he⟩⟩
    · exact ⟨0,fun h => False.elim (hi h)⟩
  choose z hz using hex
  refine ⟨r,z,fun i hi => ⟨(hz i hi).1,(hz i hi).2,(hr i).1,(hr i).2⟩,?_⟩
  intro Q hQ G D
  have he : 1/(delta*(Q:ℝ))=8/(L*(N:ℝ)*(Q:ℝ)) := by dsimp only [delta]; ring
  have he' : 4/((L*(N:ℝ)/2)*(Q:ℝ))=8/(L*(N:ℝ)*(Q:ℝ)) := by ring
  have hb := hcount Q hQ
  dsimp only at hb
  rw [he,he'] at hb
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  exact hb.trans (mul_le_mul_of_nonneg_left
    (bourgain_minimal_arc_floor_budget hD hX) (Nat.cast_nonneg Bmul))

theorem bourgain_minimal_arc_rounded_source_geometry
    {N : ℕ} {start : ℤ} {base z A B : ℝ} (hN : 0 < N)
    (hstart : (start:ℝ)=base+2*(N:ℝ))
    (hz : z∈Ioo (base-(N:ℝ)/4) (base+(N:ℝ)/4))
    (hbuffer : Icc (base-(7*(N:ℝ)+2)) (base+(7*(N:ℝ)+2)) ⊆ Icc A B) :
    z∈Ioo A B ∧ |z-(round z:ℝ)| ≤ 1/2 ∧
      ((N:ℤ) ≤ start-round z ∧ start-round z ≤ 3*(N:ℤ)) ∧
      Icc ((round z:ℝ)-(6*(N:ℝ)+1)) ((round z:ℝ)+(6*(N:ℝ)+1)) ⊆ Icc A B := by
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hround : |z-(round z:ℝ)| ≤ 1/2 := abs_sub_round z
  have hround' := abs_le.mp hround
  have hlo := (hbuffer (left_mem_Icc.mpr (by linarith only [hNr]))).1
  have hhi := (hbuffer (right_mem_Icc.mpr (by linarith only [hNr]))).2
  refine ⟨⟨by linarith only [hlo,hz.1,hNr],by linarith only [hhi,hz.2,hNr]⟩,hround,?_,?_⟩
  · have hlow : (N:ℝ) ≤ (start:ℝ)-(round z:ℝ) := by
      linarith only [hz.1,hz.2,hround'.1,hround'.2,hstart,hNr]
    have hhigh : (start:ℝ)-(round z:ℝ) ≤ 3*(N:ℝ) := by
      linarith only [hz.1,hz.2,hround'.1,hround'.2,hstart,hNr]
    constructor
    · exact_mod_cast hlow
    · exact_mod_cast hhigh
  · intro x hx
    apply hbuffer
    constructor <;> linarith only [hx.1,hx.2,hz.1,hz.2,hround'.1,hround'.2,hNr]


set_option maxHeartbeats 400000 in
                                                                         
                                                                         
                                                                                               
                                                                        
theorem exists_bourgain_C4_minimal_arc_source_band
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (ι : Type v) [DecidableEq ι] (S : Finset ι)
      (f : ℝ → ℝ) (k : ι → ℤ) (H : ι → ℕ) (N Bmul : ℕ) (s : ℤ)
      (A B L F U X lambda : ℝ),
      0 < N → 0 < L → 0 ≤ F → 0 < U → 0 ≤ X → 0 < lambda →
      F ≤ L^2/16 →
      F*(6*(N:ℝ)+1)^4 ≤ 1 → (3*U/2)*(6*(N:ℝ)+1)^2 ≤ 1 →
      (∀ x∈Icc A B, ContDiffAt ℝ 4 f x) →
      (∀ x∈Icc A B, L ≤ iteratedDeriv 3 f x ∧ iteratedDeriv 3 f x ≤ 6*U) →
      (∀ x∈Icc A B, lambda ≤ |iteratedDeriv 4 f x| ∧ |iteratedDeriv 4 f x| ≤ F) →
      (∀ x∈Icc A B, |iteratedDeriv 2 f x/2| ≤ X) →
      (∀ n : ℤ, (S.filter (fun i => k i=n)).card ≤ Bmul) →
      (∀ i∈S, H i ≤ N) →
      let base := fun i => (s:ℝ)-2*(N:ℝ)+(N:ℝ)*(k i:ℝ)
      let curv := fun i => iteratedDeriv 2 f (base i)/2
      let delta := L*(N:ℝ)/8
      (∀ i∈S, Icc (base i-(7*(N:ℝ)+2)) (base i+(7*(N:ℝ)+2)) ⊆ Icc A B) →
      ∃ (r : ι → ℚ) (z : ι → ℝ),
        (∀ i∈S, z i∈Ioo (base i-(N:ℝ)/4) (base i+(N:ℝ)/4) ∧
          iteratedDeriv 2 f (z i)/2=(r i:ℝ) ∧
          (r i:ℝ)∈Ioo (curv i-delta) (curv i+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo (curv i-delta) (curv i+delta) → (r i).den ≤ a.den) ∧
      (∀ Q₀ : ℕ, 2 ≤ Q₀ →
        let D₀ := 8/(L*(N:ℝ)*(Q₀:ℝ))
        (∑ i∈S.filter (fun i => Q₀ ≤ (r i).den),
          ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖) ≤
          (N:ℝ)*Bmul*(4*(X+1)*D₀^2+D₀*(2+Real.log (D₀+1)))) ∧
      ∀ j : ℕ, 1 ≤ j →
      let q := fun i => (r i).den
      let Q : ℕ := 2^(j+1)
      let G := (S.filter (fun i => q i ≤ N ∧ 3 ≤ (L/2)*(q i:ℝ)^2*N)).filter
        (fun i => Nat.log 2 (q i)=j)
      let M : ℕ := ⌈63*U*(Q:ℝ)*(N:ℝ)^2⌉₊+1
      let D := 16/(L*(N:ℝ)*(Q:ℝ))
      let Y := (Bmul:ℝ)*(4*(X+1)*D^2+D*(2+Real.log (D+1)))
      let d := L*(Q:ℝ)*N/12
      let eta := 1/(6*(M:ℝ)^2)
      let zeta := Real.sqrt M/(6*(M:ℝ)^2)
      let E := 16*U*Real.sqrt (U*(Q:ℝ)^3)*zeta+3*F/4
      let Gamma := eta*(Q:ℝ)^2
      let rho := (12*U*Real.sqrt (U*(Q:ℝ)^3)/lambda)*zeta
      (G.card:ℝ) ≤ Y ∧
      (∑ i∈G, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖)^12 ≤
        C*((2/d)^6*(1+Real.log M)^12*(M:ℝ)^((12:ℝ)+ε)*(2*Y)^10*
          (4*Bmul*Y*(1+6*U*(rho+1))+
            16*(Bmul:ℝ)^2*(2*Gamma+1)*(2*X+5)^2*(Gamma+48*E*(Q:ℝ)^2/L))+
          (Y*(Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)))^12) := by
  classical
  obtain ⟨C,hC,hsource⟩ := exists_bourgain_C4_prescribed_source_second_spacing.{v} hε
  refine ⟨C,hC,?_⟩
  intro ι instι S f k H N Bmul s A B L F U X lambda
    hN hL hF hU hX hlambda hFL hfourSmall hquadSmall hf hthree hfour
    hlevelX hmul hH base curv delta hbuffer
  have hNr : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hsmallbuf i (hi : i∈S) :
      Icc (base i-(N:ℝ)/4) (base i+(N:ℝ)/4) ⊆ Icc A B := by
    intro x hx
    apply hbuffer i hi
    constructor <;> linarith only [hx.1,hx.2,hNr]
  have hbase i (hi : i∈S) : base i∈Icc A B :=
    hsmallbuf i hi ⟨by linarith only [hNr],by linarith only [hNr]⟩
  obtain ⟨r,z,hr,hfamily⟩ := exists_bourgain_C3_minimal_curvature_arc_count
    S f k N Bmul ((s:ℝ)-2*(N:ℝ)) hN hL hX
    (fun x hx => (hf x hx).of_le (by norm_num))
    (fun x hx => (hthree x hx).1) hmul hsmallbuf
    (fun i hi => hlevelX (base i) (hbase i hi))
  have htail (Q₀ : ℕ) (hQ₀ : 2 ≤ Q₀) :
      let D₀ := 8/(L*(N:ℝ)*(Q₀:ℝ))
      (∑ i∈S.filter (fun i => Q₀ ≤ (r i).den),
        ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖) ≤
        (N:ℝ)*Bmul*(4*(X+1)*D₀^2+D₀*(2+Real.log (D₀+1))) := by
    intro D₀
    calc
      _ ≤ ∑ _i∈S.filter (fun i => Q₀ ≤ (r i).den),(N:ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hn : ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),
            (𝐞 (f n):ℂ)‖ ≤ H i := by
          apply (norm_sum_le _ _).trans_eq
          simp
        exact hn.trans (Nat.cast_le.mpr (hH i (Finset.mem_filter.mp hi).1))
      _ = (N:ℝ)*(S.filter (fun i => Q₀ ≤ (r i).den)).card := by
        simp only [Finset.sum_const,nsmul_eq_mul,mul_comm]
      _ ≤ _ := by
        simpa only [D₀,mul_assoc] using
          mul_le_mul_of_nonneg_left (hfamily Q₀ hQ₀) hNr.le
  refine ⟨r,z,hr,htail,?_⟩
  intro j hj q Q G M D Y d eta zeta E Gamma rho
  have hGS : G ⊆ S := fun i hi =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
  have hgeo i (hi : i∈S) :
      z i∈Ioo A B ∧ |z i-(round (z i):ℝ)| ≤ 1/2 ∧
        ((N:ℤ) ≤ s+(N:ℤ)*k i-round (z i) ∧
          s+(N:ℤ)*k i-round (z i) ≤ 3*(N:ℤ)) ∧
        Icc ((round (z i):ℝ)-(6*(N:ℝ)+1))
          ((round (z i):ℝ)+(6*(N:ℝ)+1)) ⊆ Icc A B := by
    exact bourgain_minimal_arc_rounded_source_geometry hN
      (by dsimp only [base]; push_cast; ring) (hr i hi).1 (hbuffer i hi)
  have hlow : 2 ≤ 2^j := by
    calc
      2 = 2^1 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hj
  have hqdata i (hi : i∈G) :
      0 < q i ∧ q i ≤ Q ∧ Q ≤ 2*q i ∧ q i ≤ N ∧
        IsCoprime (r i).num (q i:ℤ) := by
    obtain ⟨hiS,hiScale⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hi).1
    have he := (Finset.mem_filter.mp hi).2
    have hqpos : 0 < q i := (r i).pos
    have hlo := Nat.pow_log_le_self 2 hqpos.ne'
    have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)) (q i)
    rw [he] at hlo hhi
    refine ⟨hqpos,hhi.le,?_,hiScale.1,(r i).isCoprime_num_den⟩
    calc
      Q = 2*2^j := by dsimp only [Q]; rw [pow_succ,Nat.mul_comm]
      _ ≤ _ := Nat.mul_le_mul_left _ hlo
  have hGtail : G ⊆ S.filter (fun i => 2^j ≤ (r i).den) := by
    intro i hi
    refine Finset.mem_filter.mpr ⟨hGS hi,?_⟩
    have hh := Nat.pow_log_le_self 2 (r i).pos.ne'
    have he := (Finset.mem_filter.mp hi).2
    change Nat.log 2 (r i).den=j at he
    rwa [he] at hh
  have hDeq : 8/(L*(N:ℝ)*(2^j:ℕ))=D := by
    dsimp only [D,Q]
    rw [pow_succ,Nat.cast_mul,Nat.cast_ofNat]
    ring
  have hcard : (G.card:ℝ) ≤ Y := by
    have hh := hfamily (2^j) hlow
    dsimp only at hh
    rw [hDeq] at hh
    exact (Nat.cast_le.mpr (Finset.card_le_card hGtail)).trans hh
  refine ⟨hcard,?_⟩
  have hY : 0 ≤ Y := (Nat.cast_nonneg G.card).trans hcard
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hM : 63*U*(Q:ℝ)*(N:ℝ)^2 ≤ M := by
    have hh := Nat.le_ceil (63*U*(Q:ℝ)*(N:ℝ)^2)
    dsimp only [M]
    push_cast
    linarith only [hh]
  have : NeZero M := ⟨by dsimp only [M]; omega⟩
  have hminor i (hi : i∈G) : 1 ≤ (L/6)*(q i:ℝ)^2*N := by
    have hh := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2.2
    nlinarith only [hh]
  have hmulG n : (G.filter (fun i => k i=n)).card ≤ Bmul :=
    (Finset.card_le_card (Finset.filter_subset_filter _ hGS)).trans (hmul n)
  have hbound := hsource ι G f z (fun i => round (z i)) k
    (fun i => (r i).num) q H N Q Bmul s M A B L F U X lambda
    hN hQ hL hF hU hX hlambda hFL hfourSmall hquadSmall hf hthree hfour
    (fun i hi => (hgeo i (hGS hi)).1)
    (fun i hi => (hgeo i (hGS hi)).2.2.2)
    (fun i hi => (hgeo i (hGS hi)).2.1)
    (fun i hi => (hgeo i (hGS hi)).2.2.1)
    hmulG (fun i hi => hH i (hGS hi)) hqdata
    (fun i hi => by simpa only [Rat.cast_def] using (hr i (hGS hi)).2.1)
    (fun i hi => hlevelX (z i)
      ⟨(hgeo i (hGS hi)).1.1.le,(hgeo i (hGS hi)).1.2.le⟩)
    hminor hM
  let W := fun i => (s+(N:ℤ)*k i-round (z i)).toNat
  let mu := fun i => iteratedDeriv 3 f (round (z i))/6
  let Err := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)
  let K := (2/d)^6*(1+Real.log M)^12*(M:ℝ)^((12:ℝ)+ε)
  let V := 16*(Bmul:ℝ)^2*(2*Gamma+1)*(2*X+5)^2*(Gamma+48*E*(Q:ℝ)^2/L)
  let T := K*(2*(G.card:ℝ))^10*(4*Bmul*G.card*(1+6*U*(rho+1))+V)
  have hNr1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (6*(N:ℝ)) := Real.log_nonneg (by linarith only [hNr1])
  have hErr : 0 ≤ Err := by dsimp only [Err]; positivity
  have herror i (hi : i∈G) :
      0 ≤ Real.sqrt (W i)*Real.log (2*(W i:ℝ))+1/(mu i*(W i:ℝ)^2) ∧
      Real.sqrt (W i)*Real.log (2*(W i:ℝ))+1/(mu i*(W i:ℝ)^2) ≤ Err := by
    have hw := (hgeo i (hGS hi)).2.2.1
    have hw0 : 0 ≤ s+(N:ℤ)*k i-round (z i) :=
      (Int.natCast_nonneg N).trans hw.1
    have hWcast : (W i:ℤ)=s+(N:ℤ)*k i-round (z i) := Int.toNat_of_nonneg hw0
    have hNW : N ≤ W i := by exact_mod_cast (hw.1.trans_eq hWcast.symm)
    have hW3 : W i ≤ 3*N := by exact_mod_cast (hWcast.trans_le hw.2)
    have hm : (round (z i):ℝ)∈Icc A B :=
      (hgeo i (hGS hi)).2.2.2
        ⟨by linarith only [hNr],by linarith only [hNr]⟩
    have hmule : L/6 ≤ mu i := by
      have hh := (hthree (round (z i)) hm).1
      dsimp only [mu]
      linarith only [hh]
    have hmup : 0 < mu i := by linarith only [hmule,hL]
    have hw1 : (1:ℝ) ≤ W i := by exact_mod_cast hN.trans_le hNW
    have hlogW : 0 ≤ Real.log (2*(W i:ℝ)) :=
      Real.log_nonneg (by linarith only [hw1])
    exact ⟨by positivity,bourgain_prescribed_source_error_le hN hNW hW3 hL hmule⟩
  have herrorSum0 : 0 ≤ ∑ i∈G,
      (Real.sqrt (W i)*Real.log (2*(W i:ℝ))+1/(mu i*(W i:ℝ)^2)) :=
    Finset.sum_nonneg (fun i hi => (herror i hi).1)
  have herrorSum : (∑ i∈G,
      (Real.sqrt (W i)*Real.log (2*(W i:ℝ))+1/(mu i*(W i:ℝ)^2))) ≤ Y*Err := by
    calc
      _ ≤ ∑ _i∈G,Err := Finset.sum_le_sum (fun i hi => (herror i hi).2)
      _ = G.card*Err := by simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard hErr
  have hE : 0 ≤ E := by dsimp only [E,zeta]; positivity
  have hGamma : 0 ≤ Gamma := by dsimp only [Gamma,eta]; positivity
  have hrho : 0 ≤ rho := by dsimp only [rho,zeta]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hcoef : 0 ≤ 1+6*U*(rho+1) := by positivity
  have htri : 4*(Bmul:ℝ)*G.card*(1+6*U*(rho+1)) ≤
      4*(Bmul:ℝ)*Y*(1+6*U*(rho+1)) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcard (by positivity)) hcoef
  have hT : T ≤ K*(2*Y)^10*(4*Bmul*Y*(1+6*U*(rho+1))+V) := by
    dsimp only [T]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_left hcard (by norm_num)) 10) hK)
      (add_le_add_left htri V) (by positivity) (by positivity)
  change (∑ i∈G, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),
    (𝐞 (f n):ℂ)‖)^12 ≤ C*(T+
      (∑ i∈G,(Real.sqrt (W i)*Real.log (2*(W i:ℝ))+1/(mu i*(W i:ℝ)^2)))^12) at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (add_le_add hT (pow_le_pow_left₀ herrorSum0 herrorSum 12)) hC.le)

private theorem bourgain_cubic_stationary_main_norm
    {N N₁ q : ℕ} (hN : 1 ≤ N) (hNN : N ≤ N₁) (hN₁ : N₁ ≤ 2*N)
    (hq : 0 < q) {μ : ℝ} (hμ : 0 < μ) (a : ℤ)
    (ha : IsCoprime a (q:ℤ)) (ℓ : ℝ) :
    ‖(q:ℂ)⁻¹*∑ k∈Finset.Icc
      ⌈(q:ℝ)*(3*μ*(N:ℝ)^2+ℓ)⌉ ⌊(q:ℝ)*(3*μ*(N₁:ℝ)^2+ℓ)⌋,
      let r := Real.sqrt (((k:ℝ)/(q:ℝ)-ℓ)/(3*μ))
      bourgainQuadraticGauss q a k*
        ((𝐞 ((1:ℝ)/8-2*μ*r^3):ℂ)/(Real.sqrt (6*μ*r):ℂ))‖ ≤
      18*(N:ℝ)*Real.sqrt (μ*(q:ℝ)*N)+
        2/(Real.sqrt (μ*(N:ℝ))*Real.sqrt q) := by
  classical
  let : NeZero q := ⟨hq.ne'⟩
  have hqr : (0:ℝ) < q := Nat.cast_pos.mpr hq
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hNNr : (N:ℝ) ≤ N₁ := by exact_mod_cast hNN
  have hN₁r : (N₁:ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast hN₁
  let V := Finset.Icc ⌈(q:ℝ)*(3*μ*(N:ℝ)^2+ℓ)⌉
    ⌊(q:ℝ)*(3*μ*(N₁:ℝ)^2+ℓ)⌋
  have hV : (V.card:ℝ) ≤ 9*μ*q*(N:ℝ)^2+1 := by
    have hsq : (N:ℝ)^2 ≤ (N₁:ℝ)^2 := pow_le_pow_left₀ hNr.le hNNr 2
    have hsq' : (N₁:ℝ)^2 ≤ 4*(N:ℝ)^2 := by nlinarith only [hN₁r,hNr,hNNr]
    have hh := integer_card_le_interval_length_add_one V
      (show (q:ℝ)*(3*μ*(N:ℝ)^2+ℓ) ≤ (q:ℝ)*(3*μ*(N₁:ℝ)^2+ℓ) by
        nlinarith only [mul_nonneg hqr.le (mul_nonneg hμ.le (sub_nonneg.mpr hsq))])
      (by intro k hk; simpa only [V,Finset.mem_Icc,Int.ceil_le,Int.le_floor] using hk)
    have hscale := mul_le_mul_of_nonneg_left hsq' (by positivity : 0 ≤ 3*μ*(q:ℝ))
    nlinarith only [hh,hscale]
  have hterm k (hk : k∈V) :
      let r := Real.sqrt (((k:ℝ)/(q:ℝ)-ℓ)/(3*μ))
      ‖bourgainQuadraticGauss q a k*
        ((𝐞 ((1:ℝ)/8-2*μ*r^3):ℂ)/(Real.sqrt (6*μ*r):ℂ))‖ ≤
          Real.sqrt (2*(q:ℝ))/Real.sqrt (μ*(N:ℝ)) := by
    intro r
    have hk' := hk
    simp only [V,Finset.mem_Icc,Int.ceil_le,Int.le_floor] at hk'
    have harg : (N:ℝ)^2 ≤ ((k:ℝ)/(q:ℝ)-ℓ)/(3*μ) := by
      apply (le_div_iff₀ (by positivity : 0 < 3*μ)).mpr
      have hh : 3*μ*(N:ℝ)^2+ℓ ≤ (k:ℝ)/(q:ℝ) :=
        (le_div_iff₀ hqr).mpr (by nlinarith only [hk'.1])
      nlinarith only [hh]
    have hr : (N:ℝ) ≤ r := by
      have hh := Real.sqrt_le_sqrt harg
      simpa only [Real.sqrt_sq hNr.le] using hh
    have hrp : 0 < r := hNr.trans_le hr
    have hroot : Real.sqrt (μ*(N:ℝ)) ≤ Real.sqrt (6*μ*r) :=
      Real.sqrt_le_sqrt (by
        have hh := mul_le_mul_of_nonneg_left hr hμ.le
        have hp := mul_nonneg hμ.le hrp.le
        nlinarith only [hh,hp])
    rw [norm_mul,norm_div,Circle.norm_coe,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      _ ≤ Real.sqrt (2*(q:ℝ))*(1/Real.sqrt (μ*(N:ℝ))) :=
        mul_le_mul (bourgainQuadraticGauss_norm_le q a k ha)
          (one_div_le_one_div_of_le (by positivity) hroot) (by positivity) (by positivity)
      _ = _ := by ring
  have hm :
      ‖(q:ℂ)⁻¹*∑ k∈V,
        let r := Real.sqrt (((k:ℝ)/(q:ℝ)-ℓ)/(3*μ))
        bourgainQuadraticGauss q a k*
          ((𝐞 ((1:ℝ)/8-2*μ*r^3):ℂ)/(Real.sqrt (6*μ*r):ℂ))‖ ≤
        (9*μ*q*(N:ℝ)^2+1)*Real.sqrt (2*(q:ℝ))/
          ((q:ℝ)*Real.sqrt (μ*(N:ℝ))) := by
    rw [norm_mul,norm_inv,Complex.norm_natCast]
    apply (mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
      (Finset.sum_le_sum hterm)) (by positivity)).trans
    simp only [Finset.sum_const,nsmul_eq_mul]
    have hh := mul_le_mul_of_nonneg_right hV
      (by positivity : 0 ≤ Real.sqrt (2*(q:ℝ))/Real.sqrt (μ*(N:ℝ)))
    have hh' := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (q:ℝ)⁻¹)
    convert hh' using 1
    ring
  apply hm.trans
  have hsQ : 0 < Real.sqrt (q:ℝ) := Real.sqrt_pos.mpr hqr
  have hsN : 0 < Real.sqrt (μ*(N:ℝ)) := by positivity
  have htwo : Real.sqrt (2*(q:ℝ)) ≤ 2*Real.sqrt (q:ℝ) := by
    nlinarith only [Real.sq_sqrt (by positivity : 0 ≤ 2*(q:ℝ)),
      Real.sq_sqrt hqr.le,Real.sqrt_nonneg (2*(q:ℝ)),hsQ]
  have he : Real.sqrt (μ*(q:ℝ)*N)=Real.sqrt (μ*(N:ℝ))*Real.sqrt (q:ℝ) := by
    rw [←Real.sqrt_mul (by positivity : 0 ≤ μ*(N:ℝ))]
    congr 1
    ring
  have hsQ2 := Real.sq_sqrt hqr.le
  have hsN2 := Real.sq_sqrt (by positivity : 0 ≤ μ*(N:ℝ))
  calc
    _ ≤ (9*μ*q*(N:ℝ)^2+1)*(2*Real.sqrt (q:ℝ))/
        ((q:ℝ)*Real.sqrt (μ*(N:ℝ))) := by gcongr
    _ = _ := by
      rw [he]
      field_simp
      rw [hsQ2,hsN2]
      ring

private theorem exists_bourgain_cubic_unrestricted_absolute_bound :
    ∃ C ≥ (1:ℝ), ∀ N N₁ q : ℕ, 1 ≤ N → N ≤ N₁ → N₁ ≤ 2*N →
      0 < q → q ≤ N → ∀ μ : ℝ, 0 < μ → μ*(N:ℝ)^2 ≤ 1 →
      ∀ a : ℤ, IsCoprime a (q:ℤ) → ∀ ℓ : ℝ,
      ‖∑ n∈Finset.Ioc (N:ℤ) (N₁:ℤ),
        (𝐞 (μ*(n:ℝ)^3+(a:ℝ)*(n:ℝ)^2/(q:ℝ)+ℓ*n):ℂ)‖ ≤
        C*((N:ℝ)*Real.sqrt (μ*(q:ℝ)*N)+
          Real.sqrt N*Real.log (2*(N:ℝ))+1/(μ*(N:ℝ)^2)+
          1/(Real.sqrt (μ*(N:ℝ))*Real.sqrt q)) := by
  obtain ⟨C,hC,hstationary⟩ := exists_bourgain_cubic_real_linear_stationary
  refine ⟨C+20,by linarith only [hC],?_⟩
  intro N N₁ q hN hNN hN₁ hq hqN μ hμ hμN a ha ℓ
  let S := ∑ n∈Finset.Ioc (N:ℤ) (N₁:ℤ),
    (𝐞 (μ*(n:ℝ)^3+(a:ℝ)*(n:ℝ)^2/(q:ℝ)+ℓ*n):ℂ)
  let A := (q:ℂ)⁻¹*∑ k∈Finset.Icc
    ⌈(q:ℝ)*(3*μ*(N:ℝ)^2+ℓ)⌉ ⌊(q:ℝ)*(3*μ*(N₁:ℝ)^2+ℓ)⌋,
    let r := Real.sqrt (((k:ℝ)/(q:ℝ)-ℓ)/(3*μ))
    bourgainQuadraticGauss q a k*
      ((𝐞 ((1:ℝ)/8-2*μ*r^3):ℂ)/(Real.sqrt (6*μ*r):ℂ))
  let U := (N:ℝ)*Real.sqrt (μ*(q:ℝ)*N)
  let E := Real.sqrt N*Real.log (2*(N:ℝ))+1/(μ*(N:ℝ)^2)
  let R := 1/(Real.sqrt (μ*(N:ℝ))*Real.sqrt q)
  have hS : ‖S-A‖ ≤ C*(E+R) := hstationary N N₁ q hN hNN hN₁ hq hqN μ hμ hμN a ha ℓ
  have hA : ‖A‖ ≤ 18*U+2*R := by
    convert bourgain_cubic_stationary_main_norm hN hNN hN₁ hq hμ a ha ℓ using 1
    dsimp only [U,R]
    ring
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (2*(N:ℝ)) :=
    Real.log_nonneg (by linarith only [hN1])
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hCU : 0 ≤ C*U := mul_nonneg (by linarith only [hC]) hU
  have htri : ‖S‖ ≤ ‖S-A‖+‖A‖ := by
    simpa only [sub_add_cancel] using norm_add_le (S-A) A
  change ‖S‖ ≤ (C+20)*(U+Real.sqrt N*Real.log (2*(N:ℝ))+
    1/(μ*(N:ℝ)^2)+R)
  have hfinal : ‖S‖ ≤ (C+20)*((U+E)+R) := by
    nlinarith only [htri,hS,hA,hU,hE,hR,hCU]
  convert hfinal using 1
  dsimp only [E]
  ring

private theorem exists_bourgain_C4_unrestricted_absolute_bound :
    ∃ C ≥ (1:ℝ), ∀ (f : ℝ → ℝ) (m : ℝ) (a : ℤ) (q N H : ℕ),
      1 ≤ N → H ≤ N → 0 < q → q ≤ N → IsCoprime a (q:ℤ) →
      ∀ B D : ℝ, 0 ≤ B → 0 ≤ D →
      B*(2*(N:ℝ)+1)^4 ≤ 1 → D*(2*(N:ℝ)+1)^2 ≤ 1 →
      (∀ x∈Icc (m-(2*(N:ℝ)+1)) (m+(2*(N:ℝ)+1)), ContDiffAt ℝ 4 f x) →
      (∀ x∈Icc (m-(2*(N:ℝ)+1)) (m+(2*(N:ℝ)+1)), |iteratedDeriv 4 f x| ≤ B) →
      |iteratedDeriv 2 f m/2-(a:ℝ)/q| ≤ D →
      let μ := iteratedDeriv 3 f m/6
      0 < μ → μ*(N:ℝ)^2 ≤ 1 →
      ‖∑ n∈Finset.Ioc (N:ℤ) ((N:ℤ)+H),(𝐞 (f (m+n)):ℂ)‖ ≤
        C*((N:ℝ)*Real.sqrt (μ*(q:ℝ)*N)+
          Real.sqrt N*Real.log (2*(N:ℝ))+1/(μ*(N:ℝ)^2)+
          1/(Real.sqrt (μ*(N:ℝ))*Real.sqrt q)) := by
  classical
  obtain ⟨C,hC,hcubic⟩ := exists_bourgain_cubic_unrestricted_absolute_bound
  have hp : 1 ≤ 1+6*Real.pi := by linarith only [Real.pi_pos]
  refine ⟨(1+6*Real.pi)*C,one_le_mul_of_one_le_of_one_le hp hC,?_⟩
  intro f m a q N H hN hH hq hqN ha B D hB hD hfour hquad hf hfourBound hcurv μ hμ hμN
  have hNr : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hHr : (H:ℝ) ≤ N := Nat.cast_le.mpr hH
  obtain ⟨J,hJ,hprefix⟩ := bourgain_cubic_taylor_common_prefix
    ({()} : Finset Unit) (fun _ => f) (fun _ => m) (fun _ => (a:ℝ)/q)
    ((N:ℝ)+1) H (L:=2*(N:ℝ)+1) (B:=B) (D:=D)
    (by positivity) hB hD
    (by intro x hx; rw [abs_of_nonneg (by linarith only [hx.1,hNr])];
        linarith only [hx.2,hHr])
    (fun _ _ => hf) (fun _ _ => hfourBound) (fun _ _ => hcurv)
  simp only [Finset.sum_singleton] at hprefix
  have hshort := bourgain_cubic_taylor_short_cost hH hB hD hfour hquad
  have hsum :
      ‖∑ j∈Finset.range H,(𝐞 (f (m+((N:ℝ)+1+j))):ℂ)‖ ≤
        (1+6*Real.pi)*‖∑ j∈Finset.range J,
          (𝐞 (μ*((N:ℝ)+1+j)^3+((a:ℝ)/q)*((N:ℝ)+1+j)^2+
            deriv f m*((N:ℝ)+1+j)):ℂ)‖ :=
    hprefix.trans (mul_le_mul_of_nonneg_right hshort (norm_nonneg _))
  have hraw := hcubic N (N+J) q hN (by omega) (by omega) hq hqN μ hμ hμN a ha (deriv f m)
  have he : (∑ n∈Finset.Ioc (N:ℤ) ((N+J:ℕ):ℤ),
      (𝐞 (μ*(n:ℝ)^3+(a:ℝ)*(n:ℝ)^2/(q:ℝ)+deriv f m*n):ℂ)) =
      ∑ j∈Finset.range J,
        (𝐞 (μ*((N:ℝ)+1+j)^3+((a:ℝ)/q)*((N:ℝ)+1+j)^2+
          deriv f m*((N:ℝ)+1+j)):ℂ) := by
    simpa only [Nat.cast_add,div_mul_eq_mul_div] using
      bourgain_cubic_Ioc_range N J μ ((a:ℝ)/q) (deriv f m)
  rw [he] at hraw
  rw [bourgain_source_Ioc_range]
  exact hsum.trans ((mul_le_mul_of_nonneg_left hraw (by linarith only [hp])).trans_eq (by ring))

                                                                     
                                                                       
theorem bourgain_bounded_denominator_count
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (r : ι → ℚ)
    (Q B : ℕ) {X : ℝ} (hX : 0 ≤ X)
    (hlevel : ∀ i∈S, |(r i:ℝ)| ≤ X)
    (hden : ∀ i∈S, (r i).den ≤ Q)
    (hmul : ∀ a : ℚ, (S.filter (fun i => r i=a)).card ≤ B) :
    (S.card:ℝ) ≤ B*(Q:ℝ)*(2*X*Q+1) := by
  classical
  have hnum i (hi : i∈S) : |((r i).num:ℝ)| ≤ X*Q := by
    have hd : (0:ℝ) < (r i).den := Nat.cast_pos.mpr (r i).pos
    have hv := hlevel i hi
    rw [Rat.cast_def,abs_div,abs_of_pos hd] at hv
    exact ((div_le_iff₀ hd).mp hv).trans
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hden i hi)) hX)
  have hfiber (q : ℕ) :
      ((S.filter (fun i => (r i).den=q)).card:ℝ) ≤ (2*X*Q+1)*B := by
    let T := S.filter (fun i => (r i).den=q)
    let W := T.image (fun i => (r i).num)
    have hW : (W.card:ℝ) ≤ 2*X*Q+1 := by
      have hh := integer_card_le_of_abs_sub_le W (a:=0) (B:=X*Q)
        (by positivity) (by
          intro p hp
          obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
          simpa only [sub_zero] using hnum i (Finset.mem_filter.mp hi).1)
      convert hh using 1
      ring
    have hpcount p : (T.filter (fun i => (r i).num=p)).card ≤ B := by
      apply (Finset.card_le_card (show T.filter (fun i => (r i).num=p) ⊆
        S.filter (fun i => r i=(p:ℚ)/q) from ?_)).trans (hmul ((p:ℚ)/q))
      intro i hi
      obtain ⟨hiT,hn⟩ := Finset.mem_filter.mp hi
      obtain ⟨hiS,hd⟩ := Finset.mem_filter.mp hiT
      refine Finset.mem_filter.mpr ⟨hiS,?_⟩
      rw [←Rat.num_div_den (r i),hn,hd]
    calc
      _ = ∑ p∈W,((T.filter (fun i => (r i).num=p)).card:ℝ) := by
        exact_mod_cast Finset.card_eq_sum_card_image (fun i => (r i).num) T
      _ ≤ ∑ _p∈W,(B:ℝ) := Finset.sum_le_sum (fun p _ => Nat.cast_le.mpr (hpcount p))
      _ = (W.card:ℝ)*B := by simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hW (Nat.cast_nonneg B)
  have hcard : S.card=∑ q∈Finset.Icc 1 Q,(S.filter (fun i => (r i).den=q)).card :=
    Finset.card_eq_sum_card_fiberwise (fun i hi =>
      Finset.mem_Icc.mpr ⟨(r i).pos,hden i hi⟩)
  calc
    _ = ∑ q∈Finset.Icc 1 Q,((S.filter (fun i => (r i).den=q)).card:ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ _q∈Finset.Icc 1 Q,(2*X*Q+1)*(B:ℝ) := Finset.sum_le_sum (fun q _ => hfiber q)
    _ = _ := by
      simp only [Finset.sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]
      ring

set_option maxHeartbeats 400000 in
                                                                     
                                                                     
                                                                     
theorem exists_bourgain_C4_low_denominator_source :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type v) [DecidableEq ι] (S : Finset ι)
      (f : ℝ → ℝ) (r : ι → ℚ) (z : ι → ℝ) (m k : ι → ℤ)
      (H : ι → ℕ) (N Q Bmul : ℕ) (s : ℤ) (A B L F U X : ℝ),
      0 < N → 0 < Q → 0 < L → 0 ≤ F → 0 < U → 0 ≤ X →
      F*(6*(N:ℝ)+1)^4 ≤ 1 → (3*U/2)*(6*(N:ℝ)+1)^2 ≤ 1 →
      (∀ x∈Icc A B, ContDiffAt ℝ 4 f x) →
      (∀ x∈Icc A B, L ≤ iteratedDeriv 3 f x ∧ iteratedDeriv 3 f x ≤ 6*U) →
      (∀ x∈Icc A B, |iteratedDeriv 4 f x| ≤ F) →
      (∀ i∈S, z i∈Ioo A B) →
      (∀ i∈S, Icc ((m i:ℝ)-(6*(N:ℝ)+1)) ((m i:ℝ)+(6*(N:ℝ)+1)) ⊆ Icc A B) →
      (∀ i∈S, |z i-m i| ≤ 1/2) →
      (∀ i∈S, (N:ℤ) ≤ s+(N:ℤ)*k i-m i ∧ s+(N:ℤ)*k i-m i ≤ 3*(N:ℤ)) →
      (∀ n : ℤ, (S.filter (fun i => k i=n)).card ≤ Bmul) →
      (∀ i∈S, H i ≤ N) →
      (∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧ (r i).den ≤ N) →
      (∀ i∈S, iteratedDeriv 2 f (z i)/2=(r i:ℝ)) →
      (∀ i∈S, |iteratedDeriv 2 f (z i)/2| ≤ X) →
      let Z := 4*(Bmul:ℝ)*(Q:ℝ)*(2*X*Q+1)
      (S.card:ℝ) ≤ Z ∧
      (∑ i∈S, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖) ≤
        C*Z*(3*(N:ℝ)*Real.sqrt (3*U*(Q:ℝ)*N)+
          Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)+
          Real.sqrt (12/(L*(N:ℝ)*Q))) := by

  classical
  obtain ⟨C,hC,hpoint⟩ := exists_bourgain_C4_unrestricted_absolute_bound
  refine ⟨C,hC,?_⟩
  intro ι instι S f r z m k H N Q Bmul s A B L F U X
    hN hQ hL hF hU hX hfourSmall hquadSmall hf hthree hfour
    hz hbuffer hround hspan hmul hH hq hlevel hlevelX Z
  have hNr : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hQr : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hfiber a : (S.filter (fun i => r i=a)).card ≤ 4*Bmul := by
    have hh := bourgain_curvature_level_block_multiplicity S f z m k N Bmul s
      hN hL (fun x hx => hf x ⟨hx.1.le,hx.2.le⟩)
      (fun x hx => (hthree x ⟨hx.1.le,hx.2.le⟩).1)
      hz hround hspan hmul (a:ℝ)
    apply (Finset.card_le_card (show S.filter (fun i => r i=a) ⊆
      S.filter (fun i => iteratedDeriv 2 f (z i)/2=(a:ℝ)) from ?_)).trans hh
    intro i hi
    obtain ⟨hiS,he⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hiS,(hlevel i hiS).trans (by rw [he])⟩
  have hcard : (S.card:ℝ) ≤ Z := by
    have hh := bourgain_bounded_denominator_count S r Q (4*Bmul) hX
      (fun i hi => by rw [←hlevel i hi]; exact hlevelX i hi)
      (fun i hi => (hq i hi).1) hfiber
    simpa only [Z,Nat.cast_mul,Nat.cast_ofNat] using hh
  refine ⟨hcard,?_⟩
  let W := fun i => (s+(N:ℤ)*k i-m i).toNat
  let mu := fun i => iteratedDeriv 3 f (m i)/6
  let Err := 3*(N:ℝ)*Real.sqrt (3*U*(Q:ℝ)*N)+
    Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)+
    Real.sqrt (12/(L*(N:ℝ)*Q))
  have hW i (hi : i∈S) : N ≤ W i ∧ W i ≤ 3*N ∧ m i+(W i:ℤ)=s+(N:ℤ)*k i := by
    have hh := hspan i hi
    dsimp only [W]
    constructor
    · omega
    · constructor <;> omega
  have hWp i (hi : i∈S) : 1 ≤ W i := (Nat.succ_le_iff.mpr hN).trans (hW i hi).1
  have hWr i (hi : i∈S) : (N:ℝ) ≤ W i ∧ (W i:ℝ) ≤ 3*(N:ℝ) := by
    constructor <;> exact_mod_cast (by first | exact (hW i hi).1 | exact (hW i hi).2.1)
  have hm i (hi : i∈S) : (m i:ℝ)∈Ioo A B := by
    have hrad : 0 < 6*(N:ℝ)+1 := by positivity
    have hlo := (hbuffer i hi (left_mem_Icc.mpr (by linarith only [hrad]))).1
    have hhi := (hbuffer i hi (right_mem_Icc.mpr (by linarith only [hrad]))).2
    constructor <;> linarith only [hlo,hhi,hrad]
  have hmu i (hi : i∈S) : 0 < mu i ∧ L/6 ≤ mu i ∧ mu i ≤ U := by
    have hh := hthree (m i) ⟨(hm i hi).1.le,(hm i hi).2.le⟩
    dsimp only [mu]
    constructor
    · linarith only [hh.1,hL]
    · constructor <;> linarith only [hh.1,hh.2]
  have hbuf i (hi : i∈S) :
      Icc ((m i:ℝ)-(2*(W i:ℝ)+1)) ((m i:ℝ)+(2*(W i:ℝ)+1)) ⊆ Icc A B := by
    intro x hx
    apply hbuffer i hi
    have hw := (hWr i hi).2
    constructor <;> linarith only [hx.1,hx.2,hw]
  have hsmall i (hi : i∈S) :
      F*(2*(W i:ℝ)+1)^4 ≤ 1 ∧ (3*U/2)*(2*(W i:ℝ)+1)^2 ≤ 1 := by
    have hw : 2*(W i:ℝ)+1 ≤ 6*(N:ℝ)+1 := by linarith only [(hWr i hi).2]
    constructor
    · exact (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hw 4) hF).trans hfourSmall
    · exact (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hw 2) (by positivity)).trans hquadSmall
  have hcurv i (hi : i∈S) :
      |iteratedDeriv 2 f (m i)/2-((r i).num:ℝ)/(r i).den| ≤ 3*U/2 := by
    have hh := bourgain_curvature_level_difference f hf
      (fun x hx => ⟨hL.le.trans (hthree x hx).1,(hthree x hx).2⟩)
      ⟨(hm i hi).1.le,(hm i hi).2.le⟩ ⟨(hz i hi).1.le,(hz i hi).2.le⟩
    rw [hlevel i hi,Rat.cast_def,abs_sub_comm (m i:ℝ) (z i)] at hh
    have hr := mul_le_mul_of_nonneg_left (hround i hi) (show 0 ≤ 3*U by positivity)
    exact hh.trans (by linarith only [hr])
  have hscale i (hi : i∈S) : mu i*(W i:ℝ)^2 ≤ 1 := by
    have ha : (W i:ℝ)^2 ≤ (2*(W i:ℝ)+1)^2 := by
      nlinarith only [show (0:ℝ) ≤ W i from Nat.cast_nonneg _]
    calc
      _ ≤ U*(2*(W i:ℝ)+1)^2 :=
        mul_le_mul (hmu i hi).2.2 ha (sq_nonneg _) hU.le
      _ ≤ (3*U/2)*(2*(W i:ℝ)+1)^2 := by gcongr; linarith only [hU]
      _ ≤ _ := (hsmall i hi).2
  have hraw i (hi : i∈S) :
      ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖ ≤
        C*((W i:ℝ)*Real.sqrt (mu i*((r i).den:ℝ)*W i)+
          Real.sqrt (W i)*Real.log (2*(W i:ℝ))+1/(mu i*(W i:ℝ)^2)+
          1/(Real.sqrt (mu i*(W i:ℝ))*Real.sqrt (r i).den)) := by
    have hh := hpoint f (m i) (r i).num (r i).den (W i) (H i)
      (hWp i hi) ((hH i hi).trans (hW i hi).1) (r i).pos
      ((hq i hi).2.2.trans (hW i hi).1) (r i).isCoprime_num_den
      F (3*U/2) hF (by positivity) (hsmall i hi).1 (hsmall i hi).2
      (fun x hx => hf x (hbuf i hi hx)) (fun x hx => hfour x (hbuf i hi hx))
      (hcurv i hi) (hmu i hi).1 (hscale i hi)
    rw [←(hW i hi).2.2,bourgain_integer_source_translation]
    exact hh

  have hErr i (hi : i∈S) :
      (W i:ℝ)*Real.sqrt (mu i*((r i).den:ℝ)*W i)+
        Real.sqrt (W i)*Real.log (2*(W i:ℝ))+1/(mu i*(W i:ℝ)^2)+
        1/(Real.sqrt (mu i*(W i:ℝ))*Real.sqrt (r i).den) ≤ Err := by
    have hqQ : ((r i).den:ℝ) ≤ Q := Nat.cast_le.mpr (hq i hi).1
    have hQq : (Q:ℝ)/2 ≤ (r i).den := by
      have hh : (Q:ℝ) ≤ 2*((r i).den:ℝ) := by exact_mod_cast (hq i hi).2.1
      linarith only [hh]
    have hmup : 0 < mu i := (hmu i hi).1
    have hWi : (0:ℝ) < W i := by exact_mod_cast hWp i hi
    have hqi : (0:ℝ) < (r i).den := Nat.cast_pos.mpr (r i).pos
    have hmain : (W i:ℝ)*Real.sqrt (mu i*((r i).den:ℝ)*W i) ≤
        3*(N:ℝ)*Real.sqrt (3*U*(Q:ℝ)*N) := by
      have hh := mul_le_mul (mul_le_mul (hmu i hi).2.2 hqQ hqi.le hU.le)
        (hWr i hi).2 hWi.le (by positivity : 0 ≤ U*(Q:ℝ))
      have hh' : mu i*((r i).den:ℝ)*W i ≤ 3*U*(Q:ℝ)*N := by
        nlinarith only [hh]
      exact mul_le_mul (hWr i hi).2 (Real.sqrt_le_sqrt hh') (Real.sqrt_nonneg _) (by positivity)
    have herr := bourgain_prescribed_source_error_le hN (hW i hi).1
      (hW i hi).2.1 hL (hmu i hi).2.1
    have hprod : L*(N:ℝ)*Q/12 ≤ mu i*(W i:ℝ)*(r i).den := by
      have hh := mul_le_mul (mul_le_mul (hmu i hi).2.1 (hWr i hi).1 hNr.le hmup.le)
        hQq (by positivity : 0 ≤ (Q:ℝ)/2) (by positivity : 0 ≤ mu i*(W i:ℝ))
      nlinarith only [hh]
    have hcap : 1/(Real.sqrt (mu i*(W i:ℝ))*Real.sqrt (r i).den) ≤
        Real.sqrt (12/(L*(N:ℝ)*Q)) := by
      rw [←Real.sqrt_mul (by positivity : 0 ≤ mu i*(W i:ℝ)),one_div,←Real.sqrt_inv]
      have hh := one_div_le_one_div_of_le (by positivity : 0 < L*(N:ℝ)*Q/12) hprod
      apply Real.sqrt_le_sqrt
      convert hh using 1
      · simp only [one_div]
      · field_simp
    dsimp only [Err]
    linarith only [hmain,herr,hcap]
  have hlog : 0 ≤ Real.log (6*(N:ℝ)) := by
    have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
    exact Real.log_nonneg (by linarith only [hn])
  have hErr0 : 0 ≤ Err := by dsimp only [Err]; positivity
  have hC0 : 0 ≤ C := by linarith only [hC]
  calc
    _ ≤ ∑ _i∈S,C*Err :=
      Finset.sum_le_sum (fun i hi => (hraw i hi).trans
        (mul_le_mul_of_nonneg_left (hErr i hi) hC0))
    _ = C*(S.card:ℝ)*Err := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcard hC0) hErr0

private theorem bourgain_dual_second_order_remainder_derivative
    {x τ : ℝ} (hx : 0<x) (ht : 0<x+τ) :
    HasDerivAt (fun y : ℝ =>
      (Real.sqrt (y+τ))^3-(Real.sqrt y)^3-(3*τ/2)*Real.sqrt y-
        (3*τ^2/8)/Real.sqrt y)
      (-(3*τ^2)/(4*Real.sqrt x*(Real.sqrt (x+τ)+Real.sqrt x)^2)+
        3*τ^2/(16*x*Real.sqrt x)) x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hr := bourgain_dual_three_halves_remainder_derivative hx ht
  have hd := (Real.hasDerivAt_sqrt hx.ne').inv hs.ne'
  have he := hr.sub (hd.const_mul (3*τ^2/8))
  convert he using 1
  · funext y
    simp only [Pi.sub_apply,Pi.inv_apply,div_eq_mul_inv]
  · rw [Real.sq_sqrt hx.le]
    field_simp
    ring
private theorem bourgain_dual_second_order_remainder_bound
    {H x τ : ℝ} (hH : 1≤H) (hx : H≤x) (hτ : |τ|≤1/2) :
    |-(3*τ^2)/(4*Real.sqrt x*(Real.sqrt (x+τ)+Real.sqrt x)^2)+
        3*τ^2/(16*x*Real.sqrt x)| ≤ 1/(H^2*Real.sqrt H) := by
  have hHp : 0 < H := by linarith only [hH]
  have hxp : 0 < x := hHp.trans_le hx
  have ht := abs_le.mp hτ
  have hxt : 0 < x+τ := by linarith only [hH,hx,ht.1]
  let p := Real.sqrt x
  let s := Real.sqrt (x+τ)+p
  have hp : 0 < p := Real.sqrt_pos.mpr hxp
  have hs : 0 < s := by dsimp only [s]; positivity
  have hps : p ≤ s := by dsimp only [s]; linarith only [Real.sqrt_nonneg (x+τ)]
  have hp2 : p^2=x := Real.sq_sqrt hxp.le
  have ht2 : (Real.sqrt (x+τ))^2=x+τ := Real.sq_sqrt hxt.le
  have hbase : s^2-4*x=τ*(1+2*p/s) := by
    field_simp
    dsimp only [s]
    linear_combination (Real.sqrt (x+τ)+3*p)*ht2+(3*Real.sqrt (x+τ)+p)*hp2
  have he :
      -(3*τ^2)/(4*p*s^2)+3*τ^2/(16*x*p)=
        (3*τ^3*(1+2*p/s))/(16*x*p*s^2) := by
    calc
      _ = 3*τ^2*(s^2-4*x)/(16*x*p*s^2) := by field_simp; ring
      _ = _ := by rw [hbase]; ring
  have hfac : 0 ≤ 1+2*p/s ∧ 1+2*p/s ≤ 3 := by
    have hh : p/s ≤ 1 := (div_le_one hs).mpr hps
    constructor
    · positivity
    · calc
        _ = 1+2*(p/s) := by ring
        _ ≤ 3 := by linarith only [hh]
  have hnum : |3*τ^3*(1+2*p/s)| ≤ 9/8 := by
    rw [abs_mul,abs_mul,abs_pow,abs_of_nonneg hfac.1]
    norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 3)]
    have hh := pow_le_pow_left₀ (abs_nonneg τ) hτ 3
    have hh' := mul_le_mul hh hfac.2 hfac.1 (by norm_num : (0:ℝ) ≤ (1/2)^3)
    nlinarith only [hh']
  have hs2 : H ≤ s^2 := hx.trans (hp2 ▸ pow_le_pow_left₀ hp.le hps 2)
  have hroot : Real.sqrt H ≤ p := Real.sqrt_le_sqrt hx
  have hden : H^2*Real.sqrt H ≤ x*p*s^2 := by
    have hh := mul_le_mul hx hroot (Real.sqrt_nonneg H) hxp.le
    have hh' := mul_le_mul hh hs2 hHp.le (mul_nonneg hxp.le hp.le)
    nlinarith only [hh']
  change |-(3*τ^2)/(4*p*s^2)+3*τ^2/(16*x*p)| ≤ _
  rw [he,abs_div,abs_of_pos (by positivity : 0 < 16*x*p*s^2)]
  apply (div_le_div_iff₀ (by positivity : 0 < 16*x*p*s^2) (by positivity : 0 < H^2*Real.sqrt H)).mpr
  have hh := mul_le_mul_of_nonneg_right hnum (by positivity : 0 ≤ H^2*Real.sqrt H)
  have hb := mul_le_mul_of_nonneg_left hden (by norm_num : (0:ℝ) ≤ 9/8)
  have hpden : 0 ≤ x*p*s^2 := by positivity
  nlinarith only [hh,hb,hpden]


private theorem bourgain_dual_frozen_remainder_derivative
    {H x τ K : ℝ} (hH : 1 ≤ H) (hx : H ≤ x) (hτ : |τ| ≤ 1/2)
    (hK : |K| ≤ H*Real.sqrt H) :
    let b := ⌊(3*K*τ^2/8)/Real.sqrt H⌋
    let R := fun y : ℝ => K*((Real.sqrt (y+τ))^3-(Real.sqrt y)^3-
      (3*τ/2)*Real.sqrt y)-(b:ℝ)*Real.sqrt H/Real.sqrt y
    HasDerivAt R (deriv R x) x ∧ |deriv R x| ≤ 2/H := by
  intro b R
  have hHp : 0 < H := by linarith only [hH]
  have hxp : 0 < x := hHp.trans_le hx
  have ht := abs_le.mp hτ
  have hxt : 0 < x+τ := by linarith only [hH,hx,ht.1]
  have hsH : 0 < Real.sqrt H := Real.sqrt_pos.mpr hHp
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxp
  let A := (3*K*τ^2/8)/Real.sqrt H
  let D := 3*K*τ^2/8-(b:ℝ)*Real.sqrt H
  have hDbound : |D| ≤ Real.sqrt H := by
    have hlo := Int.floor_le A
    have hhi := Int.lt_floor_add_one A
    have he : D=(A-(b:ℝ))*Real.sqrt H := by
      dsimp only [D,A]
      field_simp
    have hab : |A-(b:ℝ)| ≤ 1 := by
      change (b:ℝ) ≤ A at hlo
      change A < (b:ℝ)+1 at hhi
      exact abs_le.mpr ⟨by linarith only [hlo],by linarith only [hhi]⟩
    rw [he,abs_mul,abs_of_pos hsH]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hab hsH.le
  let d₂ := -(3*τ^2)/(4*Real.sqrt x*(Real.sqrt (x+τ)+Real.sqrt x)^2)+
    3*τ^2/(16*x*Real.sqrt x)
  have hd₂ := bourgain_dual_second_order_remainder_derivative hxp hxt
  change HasDerivAt _ d₂ x at hd₂
  have hinv : HasDerivAt (fun y : ℝ => (Real.sqrt y)⁻¹)
      (-1/(2*x*Real.sqrt x)) x := by
    convert (Real.hasDerivAt_sqrt hxp.ne').inv hsx.ne' using 1
    rw [Real.sq_sqrt hxp.le]
    field_simp
  have hder : HasDerivAt R (K*d₂+D*(-1/(2*x*Real.sqrt x))) x := by
    convert (hd₂.const_mul K).add (hinv.const_mul D) using 1
    funext y
    dsimp only [R,D,Pi.add_apply]
    ring
  refine ⟨hder.differentiableAt.hasDerivAt,?_⟩
  rw [hder.deriv]
  have hrem : |d₂| ≤ 1/(H^2*Real.sqrt H) :=
    bourgain_dual_second_order_remainder_bound hH hx hτ
  have hfirst : |K*d₂| ≤ 1/H := by
    rw [abs_mul]
    calc
      _ ≤ (H*Real.sqrt H)*(1/(H^2*Real.sqrt H)) :=
        mul_le_mul hK hrem (abs_nonneg d₂) (by positivity)
      _ = _ := by field_simp
  have hden : 2*H*Real.sqrt H ≤ 2*x*Real.sqrt x := by
    have hh := mul_le_mul hx (Real.sqrt_le_sqrt hx) hsH.le hxp.le
    linarith only [hh]
  have hinvBound : |-1/(2*x*Real.sqrt x)| ≤ 1/(2*H*Real.sqrt H) := by
    rw [abs_div,abs_neg,abs_one,abs_of_pos (by positivity : 0 < 2*x*Real.sqrt x)]
    exact one_div_le_one_div_of_le (by positivity) hden
  have hsecond : |D*(-1/(2*x*Real.sqrt x))| ≤ 1/(2*H) := by
    rw [abs_mul]
    calc
      _ ≤ Real.sqrt H*(1/(2*H*Real.sqrt H)) :=
        mul_le_mul hDbound hinvBound (abs_nonneg _) hsH.le
      _ = _ := by field_simp
  calc
    _ ≤ |K*d₂|+|D*(-1/(2*x*Real.sqrt x))| := abs_add_le _ _
    _ ≤ 1/H+1/(2*H) := add_le_add hfirst hsecond
    _ ≤ 2/H := by
      have hh : 0 ≤ 1/H := by positivity
      calc
        _ = (3/2)*(1/H) := by ring
        _ ≤ 2*(1/H) := mul_le_mul_of_nonneg_right (by norm_num) hh
        _ = _ := by ring


private theorem bourgain_dual_frozen_label_bound
    {H τ K W : ℝ} (hH : 0 < H) (hτ : |τ| ≤ 1/2)
    (hW : |K|/Real.sqrt H ≤ W) :
    |(⌊(3*K*τ^2/8)/Real.sqrt H⌋:ℝ)| ≤ W+1 := by
  let A := (3*K*τ^2/8)/Real.sqrt H
  have hs : 0 < Real.sqrt H := Real.sqrt_pos.mpr hH
  have hτ2 : τ^2 ≤ 1/4 := by
    have hh := pow_le_pow_left₀ (abs_nonneg τ) hτ 2
    norm_num [sq_abs] at hh
    exact hh
  have hA : |A| ≤ W := by
    have hc : 0 ≤ 3*τ^2/8 ∧ 3*τ^2/8 ≤ 1 := by
      constructor
      · positivity
      · linarith only [hτ2]
    have he : |A|=(|K|/Real.sqrt H)*(3*τ^2/8) := by
      dsimp only [A]
      rw [abs_div,abs_of_pos hs,abs_div,abs_mul,abs_mul,abs_pow]
      norm_num
      ring
    rw [he]
    have hh := mul_le_mul_of_nonneg_left hc.2 (by positivity : 0 ≤ |K|/Real.sqrt H)
    have hh' : (|K|/Real.sqrt H)*(3*τ^2/8) ≤ |K|/Real.sqrt H := by
      simpa only [mul_one] using hh
    exact hh'.trans hW
  have hlo := Int.floor_le A
  have hhi := Int.lt_floor_add_one A
  have hdist : |(⌊A⌋:ℝ)-A| ≤ 1 :=
    abs_le.mpr ⟨by linarith only [hhi],by linarith only [hlo]⟩
  have hh := abs_add_le ((⌊A⌋:ℝ)-A) A
  rw [sub_add_cancel] at hh
  exact hh.trans (by linarith only [hA,hdist])


private theorem bourgain_dual_frozen_weight_variation
    {μ q N L τ H₀ V : ℝ} (hμ : 0<μ) (hq : 0<q) (hN : 0<N)
    (hA : 1≤μ*q*N^2) (hL : μ*q*N^2≤L) (hτ : |τ|≤1/2)
    (hH₀ : 0<H₀) (hV : 0≤V)
    (H : ℕ) (hH : (H:ℝ)≤V*H₀) (R : ℝ → ℝ)
    (hR : ∀ y : ℝ, μ*q*N^2≤y →
      HasDerivAt R (deriv R y) y ∧ |deriv R y|≤2/H₀) :
    let w := fun j : ℕ =>
      ((Real.sqrt (μ*N)/Real.sqrt
        (6*μ*Real.sqrt (2/(3*μ*q))*Real.sqrt (L+j+τ))):ℂ)*
        fordAdditiveCharacter (R (L+j))
    ‖w (H-1)‖≤1 ∧
      (∑ j∈Finset.range (H-1), ‖w (j+1)-w j‖)≤2*(1+4*Real.pi*V) := by
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
    (by positivity : 0≤2/H₀)
    (fun y hy => (hR y (hL.trans hy.1)).1)
    (fun y hy => (hR y (hL.trans hy.1)).2)
  have hvar :
      (∑ j∈Finset.range (H-1),
        ‖fordAdditiveCharacter (R (L+(j+1)))-fordAdditiveCharacter (R (L+j))‖)≤
        1+4*Real.pi*V := by
    apply hv.trans
    have hHp : (H:ℝ)/H₀≤V :=
      (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    have ht := mul_le_mul_of_nonneg_left hHp (by positivity : 0≤4*Real.pi)
    calc
      _ = 4*Real.pi*((H:ℝ)/H₀) := by ring
      _ ≤ 4*Real.pi*V := ht
      _ ≤ _ := by linarith
  have hev : FiniteVariationBound (fun j => fordAdditiveCharacter (R (L+j)))
      (H-1) (1+4*Real.pi*V) := by
    refine ⟨by positivity,?_,?_⟩
    · intro j hj
      rw [sargos_character_norm]
      have hp := mul_nonneg Real.pi_pos.le hV
      nlinarith only [hp]
    · simpa only [Nat.cast_add,Nat.cast_one] using hvar
  have hprod := hgv.mul hev
  constructor
  · rw [norm_mul,sargos_character_norm,mul_one,←Complex.ofReal_div]
    change ‖(g (H-1):ℂ)‖≤1
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hg (H-1)).1]
    exact (hg (H-1)).2
  · simpa only [g,Complex.ofReal_div,mul_one] using hprod.variation_le



set_option maxHeartbeats 400000 in
private theorem bourgain_cubic_frozen_branch_common_fourier
    {M : ℕ} [NeZero M] {ι : Type*} (S : Finset ι)
    (q N L H : ι → ℕ) (a r : ι → ℤ) (μ ℓ : ι → ℝ) (p : ι → Fin 2)
    (H₀ V : ℝ) (label : ℤ) (hH₀ : 1≤H₀) (hV : 0≤V)
    (hq : ∀ i∈S, 0<q i) (hN : ∀ i∈S, 1≤N i)
    (hμ : ∀ i∈S, 0<μ i) (hscale : ∀ i∈S, H₀≤μ i*(q i:ℝ)*(N i:ℝ)^2)
    (hK : ∀ i∈S, |-2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3|≤H₀*Real.sqrt H₀)
    (har : ∀ i∈S, (q i:ℤ)∣a i*r i-1)
    (hL : ∀ i∈S, μ i*(q i:ℝ)*(N i:ℝ)^2≤L i)
    (hH : ∀ i∈S, (H i:ℝ)≤V*H₀)
    (hwindow : ∀ i∈S, L i+H i≤M+1) :
    let b := fun i => (⌊(q i:ℝ)*ℓ i⌋+(p i:ℕ) : ℤ)
    let τ := fun i => ((b i:ℝ)-(q i:ℝ)*ℓ i)/2
    let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
    let K := fun i => -2*μ i*(s i)^3
    let x := fun i => (![-(r i:ℝ)*b i/q i,-(r i:ℝ)/q i,K i,3*K i*τ i/2] : Fin 4 → ℝ)
    (∀ i∈S, ⌊(3*K i*(τ i)^2/8)/Real.sqrt H₀⌋=label) →
    ∃ k : ZMod M,
      (∑ i∈S, ‖(q i:ℂ)⁻¹*∑ j∈Finset.range (H i),
        let h : ℤ := L i+j
        let u := Real.sqrt ((((b i+2*h:ℤ):ℝ)/(q i:ℝ)-ℓ i)/(3*μ i))
        bourgainQuadraticGauss (q i) (a i) (b i+2*h)*
          ((𝐞 ((1:ℝ)/8-2*μ i*u^3):ℂ)/(Real.sqrt (6*μ i*u):ℂ))‖) ≤
        (6*(3+8*Real.pi*V)*(1+Real.log M))*
          ∑ i∈S, (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*N i)))*
            ‖∑ j : ZMod M,
            ZMod.stdAddChar (-(j*k))*
              fordAdditiveCharacter ((label:ℝ)*Real.sqrt H₀/Real.sqrt (j.val+1:ℝ))*
              fordAdditiveCharacter (∑ d,x i d*
                (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                  Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖ := by
  classical
  dsimp only
  intro hlabel
  let b := fun i => (⌊(q i:ℝ)*ℓ i⌋+(p i:ℕ) : ℤ)
  let τ := fun i => ((b i:ℝ)-(q i:ℝ)*ℓ i)/2
  let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
  let K := fun i => -2*μ i*(s i)^3
  let x := fun i => (![-(r i:ℝ)*b i/q i,-(r i:ℝ)/q i,K i,3*K i*τ i/2] : Fin 4 → ℝ)
  let R := fun i y => K i*((Real.sqrt (y+τ i))^3-(Real.sqrt y)^3-(3*τ i/2)*Real.sqrt y)-
    (label:ℝ)*Real.sqrt H₀/Real.sqrt y
  let C := fun i => (q i:ℂ)⁻¹*bourgainQuadraticGauss (q i) (a i) (b i)*
    (𝐞 ((1:ℝ)/8):ℂ)/(Real.sqrt (μ i*N i):ℂ)
  let U := fun y : ℝ => (![y,y^2,y^((3:ℝ)/2),Real.sqrt y] : Fin 4 → ℝ)
  let f := fun i (j : ZMod M) => C i*fordAdditiveCharacter ((label:ℝ)*Real.sqrt H₀/Real.sqrt (j.val+1:ℝ))*fordAdditiveCharacter (∑ d,x i d*U (j.val+1) d)
  let w := fun i (j : ℕ) =>
    ((Real.sqrt (μ i*N i)/Real.sqrt
      (6*μ i*s i*Real.sqrt ((L i:ℝ)+j+τ i))):ℂ)*
      fordAdditiveCharacter (R i ((L i:ℝ)+j))
  have hdata i (hi : i∈S) :
      1≤L i ∧ ‖w i (H i-1)‖≤1 ∧
      (∑ j∈Finset.range (H i-1),‖w i (j+1)-w i j‖)≤2*(1+4*Real.pi*V) := by
    let : NeZero (q i) := ⟨(hq i hi).ne'⟩
    have hp := bourgain_cubic_dual_phase_coordinates (q i) (a i) (r i) (har i hi)
      (hμ i hi) (ℓ i) (p i)
    have hA : 1≤μ i*(q i:ℝ)*(N i:ℝ)^2 := hH₀.trans (hscale i hi)
    have hL' : (1:ℝ)≤L i := hA.trans (hL i hi)
    refine ⟨by exact_mod_cast hL',?_⟩
    apply bourgain_dual_frozen_weight_variation (hμ i hi)
      (by exact_mod_cast hq i hi) (by exact_mod_cast (by have := hN i hi; omega : 0<N i))
      hA (hL i hi) hp.1 (by linarith only [hH₀]) hV (H i) (hH i hi) (R i)
    intro y hy
    have hd := bourgain_dual_frozen_remainder_derivative hH₀
      ((hscale i hi).trans hy) hp.1 (hK i hi)
    dsimp only at hd
    rw [hlabel i hi] at hd
    exact hd
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
    have hre : fordAdditiveCharacter (R i ((L i:ℝ)+j))*
        fordAdditiveCharacter ((label:ℝ)*Real.sqrt H₀/Real.sqrt ((L i:ℝ)+j)) =
        fordAdditiveCharacter (K i*((Real.sqrt (((L i:ℝ)+j)+τ i))^3-
          (Real.sqrt ((L i:ℝ)+j))^3-(3*τ i/2)*Real.sqrt ((L i:ℝ)+j))) := by
      rw [←fordAdditiveCharacter_add]
      congr 1
      dsimp only [R]
      ring
    calc
      _ = (C i*fordAdditiveCharacter (∑ d,x i d*U ((L i:ℝ)+j) d))*
          (((Real.sqrt (μ i*N i)/Real.sqrt
            (6*μ i*s i*Real.sqrt ((L i:ℝ)+j+τ i))):ℂ)*
          (fordAdditiveCharacter (R i ((L i:ℝ)+j))*
            fordAdditiveCharacter ((label:ℝ)*Real.sqrt H₀/Real.sqrt ((L i:ℝ)+j)))) := by
        dsimp only [w]
        ring
      _ = _ := by
        rw [hre]
        rw [mul_comm]
        simpa only [C,x,U,K,s,τ,b,Nat.cast_add,Int.cast_natCast,Int.cast_add] using he.symm
  obtain ⟨k,hk⟩ := bourgain_weighted_interval_common_fourier S f w (fun i => L i-1) H
    (by positivity : 0≤2*(1+4*Real.pi*V))
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
        ZMod.stdAddChar (-(j*k))*
        fordAdditiveCharacter ((label:ℝ)*Real.sqrt H₀/Real.sqrt (j.val+1:ℝ))*
        fordAdditiveCharacter (∑ d,x i d*U (j.val+1) d) := by
    rw [ZMod.dft_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [f,smul_eq_mul]
    ring
  simp_rw [heDFT] at hk
  have heSum := Finset.sum_congr rfl (fun i hi => congrArg norm (he i hi))
  rw [heSum] at hk
  rw [show 6*(1+2*(1+4*Real.pi*V))=6*(3+8*Real.pi*V) by ring] at hk
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



private theorem bourgain_source_sieve_wide_box_scale {N η ζ W : ℝ}
    (hN : 1≤N) (hη : η∈Ioc 0 1) (hζ : ζ∈Ioc 0 1) (hW : 1≤W) :
    let a : Fin 4 → ℝ := ![1/(12*N),1/(12*N^2),η/12,ζ/12]
    let δ : Fin 4 → ℝ := ![1,1,2*W,2*W]
    (∀ d, 0<a d) ∧
    (∀ d, 1/(δ d+2*a d) ≤ (![1,1,1/2,1/2] : Fin 4 → ℝ) d) ∧
    16777216*(∏ d, (δ d+2*a d))/(∏ d, a d) ≤
      (16777216*36*12^4)*W^2*N^3/(η*ζ) := by
  dsimp only
  let a : Fin 4 → ℝ := ![1/(12*N),1/(12*N^2),η/12,ζ/12]
  let δ : Fin 4 → ℝ := ![1,1,2*W,2*W]
  have hNp : 0<N := by linarith
  have hηp := hη.1
  have hζp := hζ.1
  have ha d : 0<a d := by
    fin_cases d <;> norm_num [a,Matrix.cons_val_succ] <;> positivity
  refine ⟨ha,?_,?_⟩
  · intro d
    have hb : 0 < δ d := by fin_cases d <;> norm_num [δ,Matrix.cons_val_succ] <;> linarith only [hW]
    have hh : 1/(δ d+2*a d) ≤ 1/(δ d) :=
      one_div_le_one_div_of_le hb (by linarith [ha d])
    apply hh.trans
    fin_cases d
    · norm_num [δ]
    · norm_num [δ]
    · change 1/(2*W) ≤ 1/2
      exact one_div_le_one_div_of_le (by norm_num) (by linarith only [hW])
    · change 1/(2*W) ≤ 1/2
      exact one_div_le_one_div_of_le (by norm_num) (by linarith only [hW])
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
    have hD : (∏ d, (δ d+2*a d)) ≤ 36*W^2 := by
      have hb := Finset.prod_le_prod₀
        (fun d (_:d∈(Finset.univ:Finset (Fin 4))) => (by
          have hd : 0≤δ d := by fin_cases d <;> norm_num [δ,Matrix.cons_val_succ] <;> linarith only [hW]
          linarith [ha d] : 0≤δ d+2*a d))
        (g := (![2,2,3*W,3*W] : Fin 4 → ℝ))
        (fun d _ => by
          have hh := ha1 d
          calc
            δ d+2*a d ≤ δ d+1 := by linarith
            _ ≤ _ := by fin_cases d <;> norm_num [δ,Matrix.cons_val_succ] <;> linarith only [hW])
      norm_num [Fin.prod_univ_succ] at hb ⊢
      nlinarith only [hb]
    have hprod : (∏ d, a d) = η*ζ/(12^4*N^3) := by
      norm_num [a,Fin.prod_univ_succ]
      field_simp
      ring
    have hp : 0<∏ d, a d := Finset.prod_pos (fun d _ => ha d)
    calc
      _ ≤ 16777216*(36*W^2)/(∏ d, a d) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hD (by norm_num)) hp.le
      _ = _ := by rw [hprod]; field_simp




set_option maxHeartbeats 400000 in
private theorem exists_bourgainSourceCurve_wide_double_sieve {ε : ℝ} (hε : 0<ε) :
    ∃ C>(0:ℝ), ∀ (N : ℕ), 1≤N → ∀ (η ζ W : ℝ), 1≤W →
      η∈Icc (1/(N:ℝ)^2) 1 → ζ∈Icc (1/(N:ℝ)) 1 →
      ∀ (ι κ : Type v) (S : Finset ι) (T : Finset κ) (w : κ → ℂ)
        (m : κ → ℤ) (x : ι → Fin 4 → ℝ) (B : ℝ),
        0≤B → (∀ j∈T,1 ≤ m j ∧ m j≤N) →
        (∀ j∈T,‖w j‖≤1) →
        (∀ q : ℤ,((T.filter (fun j => m j=q)).card:ℝ)≤B) →
        (∀ i∈S,x i∈Icc ![0,0,-W,-W] ![1,1,W,W]) →
        let U := fun j => ![(m j:ℝ),(m j:ℝ)^2,
          (1/η)*((m j:ℝ)/N)^((3:ℝ)/2),(1/ζ)*Real.sqrt ((m j:ℝ)/N)]
        let a : Fin 4 → ℝ := ![1/(12*(N:ℝ)),1/(12*(N:ℝ)^2),η/12,ζ/12]
        (∑ i∈S,‖∑ j∈T,w j*fordAdditiveCharacter (∑ d,U j d*x i d)‖)^12 ≤
          C*W^2*(N:ℝ)^((12:ℝ)+ε)*(S.card:ℝ)^10*B^12*
            (((S ×ˢ S).filter (fun ij => ∀ d, |x ij.1 d-x ij.2 d|≤2*a d)).card:ℝ) := by
  classical
  obtain ⟨C,hC,hcount⟩ := exists_bourgainSourceCurve_six_tuple_first_spacing.{v} hε
  let L : ℝ := 16777216*36*12^4
  refine ⟨L*C,by dsimp [L]; positivity,?_⟩
  intro N hN η ζ W hW hη hζ ι κ S T w m x B hB hm hw hmass hx
  dsimp only
  have hNr : (1:ℝ)≤N := by exact_mod_cast hN
  have hNp : (0:ℝ)<N := by linarith
  have hηp : 0<η := lt_of_lt_of_le (by positivity) hη.1
  have hζp : 0<ζ := lt_of_lt_of_le (by positivity) hζ.1
  let a : Fin 4 → ℝ := ![1/(12*(N:ℝ)),1/(12*(N:ℝ)^2),η/12,ζ/12]
  let D : Fin 4 → ℝ := ![1,1,2*W,2*W]
  let c : Fin 4 → ℝ := ![0,0,-W,-W]
  let U := fun j => ![(m j:ℝ),(m j:ℝ)^2,
    (1/η)*((m j:ℝ)/N)^((3:ℝ)/2),(1/ζ)*Real.sqrt ((m j:ℝ)/N)]
  let V := Fintype.piFinset (fun _ : Fin 6 => T)
  let y := fun (j : Fin 6 → κ) d => ∑ k, U (j k) d
  let P := (S ×ˢ S).filter (fun ij => ∀ d, |x ij.1 d-x ij.2 d|≤2*a d)
  let Q := (V ×ˢ V).filter (fun ij => ∀ d, |y ij.1 d-y ij.2 d|≤1/(D d+2*a d))
  let K := 16777216*(∏ d,(D d+2*a d))/(∏ d,a d)
  obtain ⟨ha,hthreshold,hscale⟩ :=
    bourgain_source_sieve_wide_box_scale hNr ⟨hηp,hη.2⟩ ⟨hζp,hζ.2⟩ hW
  have hD d : 0<D d := by fin_cases d <;> norm_num [D,Matrix.cons_val_succ] <;> linarith only [hW]
  have hU j (hj : j∈T) : ∀ d,a d*|U j d|≤1/12 :=
    bourgain_source_sieve_frequency_scale hNr
      (by exact ⟨by exact_mod_cast (hm j hj).1,by exact_mod_cast (hm j hj).2⟩) hηp hζp
  have hx' i (hi : i∈S) d : x i d∈Icc (c d) (c d+D d) := by
    refine ⟨(hx i hi).1 d,?_⟩
    have hh := (hx i hi).2 d
    fin_cases d <;> norm_num [c,D,Matrix.cons_val_succ] at hh ⊢ <;>
      linarith only [hh]
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
        ((L*W^2*(N:ℝ)^3/(η*ζ))*(C*η*ζ*(N:ℝ)^((9:ℝ)+ε)*B^12)) := hbound
    _ = _ := by
      change _ = (L*C)*W^2*(N:ℝ)^((12:ℝ)+ε)*(S.card:ℝ)^10*B^12*(P.card:ℝ)
      rw [←hpow]
      field_simp




private theorem bourgain_completed_wide_source_sieve {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (M : ℕ) [NeZero M] (ι : Type v) (S : Finset ι)
      (x : ι → Fin 4 → ℝ) (W : ℝ), 1≤W →
      (∀ i∈S, |x i 2| ≤ W*Real.sqrt M ∧ |x i 3| ≤ W*Real.sqrt M) →
      let y := fun i => (![Int.fract (x i 0),Int.fract (x i 1),
        x i 2/Real.sqrt M,x i 3/Real.sqrt M] : Fin 4 → ℝ)
      let a : Fin 4 → ℝ :=
        ![1/(12*(M:ℝ)),1/(12*(M:ℝ)^2),(1/(M:ℝ)^2)/12,(1/(M:ℝ))/12]
      ∀ w₀ : ZMod M → ℂ, (∀ j, ‖w₀ j‖ ≤ 1) →
      (∑ i∈S, ‖∑ j : ZMod M,w₀ j*
        fordAdditiveCharacter (∑ d,x i d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
        C*W^2*(M:ℝ)^((12:ℝ)+ε)*(S.card:ℝ)^10*
          (((S ×ˢ S).filter (fun ij => ∀ d,|y ij.1 d-y ij.2 d| ≤ 2*a d)).card:ℝ) := by
  classical
  obtain ⟨C,hC,hsource⟩ := exists_bourgainSourceCurve_wide_double_sieve.{v} hε
  refine ⟨C,hC,?_⟩
  intro M inst ι S x W hW hx y a w₀ hw₀
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hMr : (0:ℝ) < M := Nat.cast_pos.mpr hM
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hsqrt : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMr
  let T : Finset (ULift.{v} (ZMod M)) := Finset.univ
  let m := fun j : ULift.{v} (ZMod M) => (j.down.val:ℤ)+1
  let w := fun j : ULift.{v} (ZMod M) => w₀ j.down
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
  have hy i (hi : i∈S) : y i∈Icc ![0,0,-W,-W] ![1,1,W,W] := by
    have h2 : |x i 2/Real.sqrt M| ≤ W := by
      rw [abs_div,abs_of_pos hsqrt]
      exact (div_le_iff₀ hsqrt).mpr (hx i hi).1
    have h3 : |x i 3/Real.sqrt M| ≤ W := by
      rw [abs_div,abs_of_pos hsqrt]
      exact (div_le_iff₀ hsqrt).mpr (hx i hi).2
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
  have hh := hsource M (by omega) (1/(M:ℝ)^2) (1/(M:ℝ)) W hW
    hη hζ ι (ULift.{v} (ZMod M)) S T w m y 1 (by norm_num) hm
    (fun j _ => hw₀ j.down) hmass hy
  simp only [one_div_one_div,one_pow,mul_one] at hh
  let U := fun j : ULift.{v} (ZMod M) =>
    (![(m j:ℝ),(m j:ℝ)^2,(M:ℝ)^2*((m j:ℝ)/M)^((3:ℝ)/2),
      (M:ℝ)*Real.sqrt ((m j:ℝ)/M)] : Fin 4 → ℝ)
  have he :
      (∑ i∈S, ‖∑ j : ZMod M,w₀ j*
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




private theorem bourgain_fiber_twelfth_sum
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (label : ι → ℤ)
    (J : Finset ℤ) (f : ι → ℝ) (P : Finset (ι × ι)) {K : ℝ}
    (hK : 0≤K) (hf : ∀ i∈S, 0≤f i)
    (hlabel : ∀ i∈S, label i∈J)
    (hbound : ∀ b∈J,
      (∑ i∈S.filter (fun i => label i=b),f i)^12 ≤
        K*((S.filter (fun i => label i=b)).card:ℝ)^10*
          ((P.filter (fun ij => label ij.1=b ∧ label ij.2=b)).card:ℝ)) :
    (∑ i∈S,f i)^12 ≤
      (J.card:ℝ)^11*K*(S.card:ℝ)^10*(P.card:ℝ) := by
  classical
  let G := fun b => S.filter (fun i => label i=b)
  let R := fun b => P.filter (fun ij => label ij.1=b ∧ label ij.2=b)
  have hsum : (∑ i∈S,f i)=∑ b∈J,∑ i∈G b,f i := by
    exact (Finset.sum_fiberwise_of_maps_to hlabel f).symm
  have hR : (∑ b∈J,((R b).card:ℝ)) ≤ (P.card:ℝ) := by
    calc
      _ ≤ ∑ b∈J,((P.filter (fun ij => label ij.1=b)).card:ℝ) := by
        apply Finset.sum_le_sum
        intro b _
        apply Nat.cast_le.mpr
        apply Finset.card_le_card
        intro ij hij
        obtain ⟨hp,hb,_⟩ := Finset.mem_filter.mp hij
        exact Finset.mem_filter.mpr ⟨hp,hb⟩
      _ = ∑ b∈J,∑ _ij∈P.filter (fun ij => label ij.1=b),(1:ℝ) := by simp
      _ ≤ ∑ _ij∈P,(1:ℝ) := Finset.sum_fiberwise_le_sum_of_sum_fiber_nonneg
        (fun _ _ => Finset.sum_nonneg (fun _ _ => by norm_num))
      _ = _ := by simp
  have hG b : ((G b).card:ℝ) ≤ S.card :=
    Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
  have hpower : (∑ b∈J,(∑ i∈G b,f i)^12) ≤ K*(S.card:ℝ)^10*(P.card:ℝ) := by
    calc
      _ ≤ ∑ b∈J,K*(S.card:ℝ)^10*((R b).card:ℝ) := by
        apply Finset.sum_le_sum
        intro b hb
        apply (hbound b hb).trans
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (Nat.cast_nonneg _) (hG b) 10) hK)
          (Nat.cast_nonneg _)
      _ = K*(S.card:ℝ)^10*(∑ b∈J,((R b).card:ℝ)) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hR (by positivity)
  have hh := pow_sum_le_card_mul_sum_pow (s:=J)
    (f:=fun b => ∑ i∈G b,f i)
    (fun b _ => Finset.sum_nonneg (fun i hi => hf i (Finset.mem_filter.mp hi).1)) 11
  rw [hsum]
  calc
    _ ≤ (J.card:ℝ)^11*(∑ b∈J,(∑ i∈G b,f i)^12) := hh
    _ ≤ (J.card:ℝ)^11*(K*(S.card:ℝ)^10*(P.card:ℝ)) :=
      mul_le_mul_of_nonneg_left hpower (by positivity)
    _ = _ := by ring


set_option maxHeartbeats 400000 in
private theorem exists_bourgain_cubic_frozen_branch_sieve {ε : ℝ} (hε : 0<ε) :
    ∃ C>(0:ℝ), ∀ (M : ℕ) [NeZero M] (ι : Type v) [DecidableEq ι]
      (S : Finset ι) (q N L H : ι → ℕ) (a r : ι → ℤ)
      (μ ℓ : ι → ℝ) (p : ι → Fin 2) (H₀ V W d : ℝ),
      1≤H₀ → H₀≤M → 0≤V → 1≤W → 0<d →
      (∀ i∈S, 0<q i ∧ 1≤N i ∧ 0<μ i) →
      (∀ i∈S, H₀≤μ i*(q i:ℝ)*(N i:ℝ)^2) →
      (∀ i∈S, |-2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3|≤H₀*Real.sqrt H₀) →
      (∀ i∈S, |-2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3|/Real.sqrt H₀≤W) →
      (∀ i∈S, (q i:ℤ)∣a i*r i-1) →
      (∀ i∈S, μ i*(q i:ℝ)*(N i:ℝ)^2≤L i) →
      (∀ i∈S, (H i:ℝ)≤V*H₀) →
      (∀ i∈S, L i+H i≤M+1) →
      (∀ i∈S, d≤μ i*(q i:ℝ)*N i) →
      let b := fun i => (⌊(q i:ℝ)*ℓ i⌋+(p i:ℕ) : ℤ)
      let τ := fun i => ((b i:ℝ)-(q i:ℝ)*ℓ i)/2
      let K := fun i => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
      let x := fun i => (![-(r i:ℝ)*b i/q i,-(r i:ℝ)/q i,K i,3*K i*τ i/2] : Fin 4 → ℝ)
      let y := fun i => (![Int.fract (x i 0),Int.fract (x i 1),
        x i 2/Real.sqrt M,x i 3/Real.sqrt M] : Fin 4 → ℝ)
      let window : Fin 4 → ℝ :=
        ![1/(12*(M:ℝ)),1/(12*(M:ℝ)^2),(1/(M:ℝ)^2)/12,(1/(M:ℝ))/12]
      let P := (S ×ˢ S).filter (fun ij => ∀ e, |y ij.1 e-y ij.2 e|≤2*window e)
      let F := fun i => ‖(q i:ℂ)⁻¹*∑ j∈Finset.range (H i),
        let h : ℤ := L i+j
        let u := Real.sqrt ((((b i+2*h:ℤ):ℝ)/(q i:ℝ)-ℓ i)/(3*μ i))
        bourgainQuadraticGauss (q i) (a i) (b i+2*h)*
          ((𝐞 ((1:ℝ)/8-2*μ i*u^3):ℂ)/(Real.sqrt (6*μ i*u):ℂ))‖
      (∑ i∈S,F i)^12 ≤
        C*(5*W)^11*W^2*(6*(3+8*Real.pi*V)*(1+Real.log M))^12*
          (2/d)^6*(M:ℝ)^((12:ℝ)+ε)*(S.card:ℝ)^10*(P.card:ℝ) := by


  classical
  obtain ⟨C,hC,hsieve⟩ := bourgain_completed_wide_source_sieve.{v} hε
  refine ⟨C,hC,?_⟩
  intro M instM ι instι S q N L H a r μ ℓ p H₀ V W d
    hH₀ hH₀M hV hW hd hdata hscale hK hKW har hL hH hwindow hdscale
    b τ K x y window P F
  have hH₀p : 0<H₀ := by linarith only [hH₀]
  have hsH : 0<Real.sqrt H₀ := Real.sqrt_pos.mpr hH₀p
  have hWp : 0<W := by linarith only [hW]
  have hM : (1:ℝ)≤M := by exact_mod_cast NeZero.pos M
  have hτ i (hi : i∈S) : |τ i|≤1/2 := by
    let : NeZero (q i) := ⟨(hdata i hi).1.ne'⟩
    exact (bourgain_cubic_dual_phase_coordinates (q i) (a i) (r i)
      (har i hi) (hdata i hi).2.2 (ℓ i) (p i)).1
  have hbox i (hi : i∈S) :
      |x i 2|≤W*Real.sqrt M ∧ |x i 3|≤W*Real.sqrt M := by
    have hki : |K i|≤W*Real.sqrt H₀ := (div_le_iff₀ hsH).mp (hKW i hi)
    have hkM : |K i|≤W*Real.sqrt M :=
      hki.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hH₀M) hWp.le)
    constructor
    · exact hkM
    · change |3*K i*τ i/2|≤W*Real.sqrt M
      rw [abs_div,abs_mul,abs_mul]
      norm_num
      have hh := mul_le_mul_of_nonneg_left (hτ i hi) (abs_nonneg (K i))
      nlinarith only [hh,hkM,abs_nonneg (K i)]
  let label := fun i => ⌊(3*K i*(τ i)^2/8)/Real.sqrt H₀⌋
  let J := S.image label
  have hJ : (J.card:ℝ)≤5*W := by
    have hb := integer_card_le_of_abs_sub_le J (a:=0) (B:=W+1)
      (by positivity) (by
        intro t ht
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht
        simpa only [sub_zero] using
          bourgain_dual_frozen_label_bound hH₀p (hτ i hi) (hKW i hi))
    linarith only [hb,hW]
  let A := 6*(3+8*Real.pi*V)*(1+Real.log M)
  let alpha := Real.sqrt (2/d)
  let D := C*W^2*A^12*(2/d)^6*(M:ℝ)^((12:ℝ)+ε)
  have hA : 0≤A := by
    have hlog := Real.log_nonneg hM
    dsimp only [A]
    positivity
  have hD : 0≤D := by dsimp only [D]; positivity
  have hAlpha : alpha^12=(2/d)^6 := by
    dsimp only [alpha]
    rw [show (12:ℕ)=2*6 from rfl,pow_mul,Real.sq_sqrt (by positivity : 0≤2/d)]
  have hF i : 0≤F i := norm_nonneg _
  have hbin t (_ht : t∈J) :
      (∑ i∈S.filter (fun i => label i=t),F i)^12 ≤
        D*((S.filter (fun i => label i=t)).card:ℝ)^10*
          ((P.filter (fun ij => label ij.1=t ∧ label ij.2=t)).card:ℝ) := by
    let G := S.filter (fun i => label i=t)
    have hG i (hi : i∈G) : i∈S := (Finset.mem_filter.mp hi).1
    obtain ⟨k,hk⟩ := bourgain_cubic_frozen_branch_common_fourier G q N L H a r μ ℓ p
      H₀ V t hH₀ hV
      (fun i hi => (hdata i (hG i hi)).1)
      (fun i hi => (hdata i (hG i hi)).2.1)
      (fun i hi => (hdata i (hG i hi)).2.2)
      (fun i hi => hscale i (hG i hi)) (fun i hi => hK i (hG i hi))
      (fun i hi => har i (hG i hi)) (fun i hi => hL i (hG i hi))
      (fun i hi => hH i (hG i hi)) (fun i hi => hwindow i (hG i hi))
      (fun i hi => (Finset.mem_filter.mp hi).2)
    let w₀ := fun j : ZMod M => ZMod.stdAddChar (-(j*k))*
      fordAdditiveCharacter ((t:ℝ)*Real.sqrt H₀/Real.sqrt (j.val+1:ℝ))
    let Z := fun i => ‖∑ j : ZMod M,w₀ j*
      fordAdditiveCharacter (∑ e,x i e*
        (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
          Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) e)‖
    change (∑ i∈G,F i) ≤ A*(∑ i∈G,
      (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*N i)))*Z i) at hk
    have hcoef i (hi : i∈G) :
        Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*N i)) ≤ alpha :=
      bourgain_dual_amplitude_coefficient_le (hdata i (hG i hi)).2.2
        (Nat.cast_pos.mpr (hdata i (hG i hi)).1)
        (by
          have hn : (1:ℝ)≤N i := by exact_mod_cast (hdata i (hG i hi)).2.1
          linarith only [hn])
        hd (hdscale i (hG i hi))
    have hbound : (∑ i∈G,F i) ≤ A*(alpha*(∑ i∈G,Z i)) := by
      apply hk.trans
      apply mul_le_mul_of_nonneg_left _ hA
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun i hi =>
        mul_le_mul_of_nonneg_right (hcoef i hi) (norm_nonneg _))
    have hs := hsieve M ι G x W hW (fun i hi => hbox i (hG i hi)) w₀
      (fun j => by
        dsimp only [w₀]
        rw [norm_mul,sargos_stdAddChar_norm,sargos_character_norm]
        norm_num)
    have hP : ((G ×ˢ G).filter (fun ij => ∀ e,|y ij.1 e-y ij.2 e|≤2*window e)) =
        P.filter (fun ij => label ij.1=t ∧ label ij.2=t) := by
      ext ij
      simp only [G,P,Finset.mem_filter,Finset.mem_product]
      tauto
    change (∑ i∈G,Z i)^12 ≤
      C*W^2*(M:ℝ)^((12:ℝ)+ε)*(G.card:ℝ)^10*
        (((G ×ˢ G).filter (fun ij => ∀ e,|y ij.1 e-y ij.2 e|≤2*window e)).card:ℝ) at hs
    rw [hP] at hs
    calc
      _ ≤ (A*(alpha*(∑ i∈G,Z i)))^12 :=
        pow_le_pow_left₀ (Finset.sum_nonneg (fun i _ => hF i)) hbound 12
      _ = A^12*alpha^12*(∑ i∈G,Z i)^12 := by ring
      _ = A^12*(2/d)^6*(∑ i∈G,Z i)^12 := by rw [hAlpha]
      _ ≤ A^12*(2/d)^6*
          (C*W^2*(M:ℝ)^((12:ℝ)+ε)*(G.card:ℝ)^10*
            ((P.filter (fun ij => label ij.1=t ∧ label ij.2=t)).card:ℝ)) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by dsimp only [D,G]; ring
  have hh := bourgain_fiber_twelfth_sum S label J F P hD
    (fun i _ => hF i) (fun i hi => Finset.mem_image_of_mem label hi) hbin
  calc
    _ ≤ (J.card:ℝ)^11*D*(S.card:ℝ)^10*(P.card:ℝ) := hh
    _ ≤ (5*W)^11*D*(S.card:ℝ)^10*(P.card:ℝ) := by
      gcongr
    _ = _ := by dsimp only [D,A]; ring


private theorem bourgain_cubic_unrestricted_parity_scales
    {q N N₁ M : ℕ} (hq : 0<q) (hN₁ : N₁≤2*N)
    {μ ℓ : ℝ} (hμ : 0<μ) (hA : 1≤μ*(q:ℝ)*(N:ℝ)^2)
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
  change 1≤A at hA
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



set_option maxHeartbeats 400000 in
private theorem exists_bourgain_cubic_frozen_gauss_sieve {ε : ℝ} (hε : 0<ε) :
    ∃ C>(0:ℝ), ∀ (M : ℕ) [NeZero M] (ι : Type v) [DecidableEq ι]
      (S : Finset ι) (q N N₁ : ι → ℕ) (a r : ι → ℤ)
      (μ ℓ : ι → ℝ) (H₀ V W d : ℝ),
      1≤H₀ → H₀≤M → 0≤V → 1≤W → 0<d →
      (∀ i∈S, 0<q i ∧ 1≤N i ∧ N₁ i≤2*N i ∧ 0<μ i) →
      (∀ i∈S, H₀≤μ i*(q i:ℝ)*(N i:ℝ)^2) →
      (∀ i∈S, |-2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3|≤H₀*Real.sqrt H₀) →
      (∀ i∈S, |-2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3|/Real.sqrt H₀≤W) →
      (∀ i∈S, (q i:ℤ)∣a i*r i-1) →
      (∀ i∈S, 7*(μ i*(q i:ℝ)*(N i:ℝ)^2)≤M) →
      (∀ i∈S, 7*(μ i*(q i:ℝ)*(N i:ℝ)^2)≤V*H₀) →
      (∀ i∈S, d≤μ i*(q i:ℝ)*N i) →
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let K := fun i => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
      let x := fun i p => (![-(r i:ℝ)*b i p/q i,-(r i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      let T := S ×ˢ (Finset.univ : Finset (Fin 2))
      let y := fun ip : ι × Fin 2 =>
        (![Int.fract (x ip.1 ip.2 0),Int.fract (x ip.1 ip.2 1),
          x ip.1 ip.2 2/Real.sqrt M,x ip.1 ip.2 3/Real.sqrt M] : Fin 4 → ℝ)
      let window : Fin 4 → ℝ :=
        ![1/(12*(M:ℝ)),1/(12*(M:ℝ)^2),(1/(M:ℝ)^2)/12,(1/(M:ℝ))/12]
      let P := (T ×ˢ T).filter (fun ij => ∀ e, |y ij.1 e-y ij.2 e|≤2*window e)
      (∑ i∈S, ‖(q i:ℂ)⁻¹*∑ k∈Finset.Icc
        ⌈(q i:ℝ)*(3*μ i*(N i:ℝ)^2+ℓ i)⌉
        ⌊(q i:ℝ)*(3*μ i*(N₁ i:ℝ)^2+ℓ i)⌋,
        let u := Real.sqrt (((k:ℝ)/(q i:ℝ)-ℓ i)/(3*μ i))
        bourgainQuadraticGauss (q i) (a i) k*
          ((𝐞 ((1:ℝ)/8-2*μ i*u^3):ℂ)/(Real.sqrt (6*μ i*u):ℂ))‖)^12 ≤
        C*(5*W)^11*W^2*(6*(3+8*Real.pi*V)*(1+Real.log M))^12*
          (2/d)^6*(M:ℝ)^((12:ℝ)+ε)*(T.card:ℝ)^10*(P.card:ℝ) := by


  classical
  obtain ⟨C,hC,hsieve⟩ := exists_bourgain_cubic_frozen_branch_sieve.{v} hε
  refine ⟨C,hC,?_⟩
  intro M instM ι instι S q N N₁ a r μ ℓ H₀ V W d
    hH₀ hH₀M hV hW hd hsource hscale hK hKW har hM hVscale hdscale
    b τ K x T y window P
  let K₀ := fun i => ⌈(q i:ℝ)*(3*μ i*(N i:ℝ)^2+ℓ i)⌉
  let K₁ := fun i => ⌊(q i:ℝ)*(3*μ i*(N₁ i:ℝ)^2+ℓ i)⌋
  let l := fun i p => (K₀ i-b i p+1)/2
  let u := fun i p => (K₁ i-b i p)/2
  let L := fun ip : ι × Fin 2 => (l ip.1 ip.2).toNat
  let H := fun ip : ι × Fin 2 => (u ip.1 ip.2-l ip.1 ip.2+1).toNat
  let F := fun i (v : ℤ) =>
    let t := Real.sqrt (((v:ℝ)/(q i:ℝ)-ℓ i)/(3*μ i))
    bourgainQuadraticGauss (q i) (a i) v*
      ((𝐞 ((1:ℝ)/8-2*μ i*t^3):ℂ)/(Real.sqrt (6*μ i*t):ℂ))
  have hdata i (hi : i∈S) (p : Fin 2) :
      0≤l i p ∧ μ i*(q i:ℝ)*(N i:ℝ)^2≤(L (i,p):ℝ) ∧
        (H (i,p):ℝ)≤7*(μ i*(q i:ℝ)*(N i:ℝ)^2) ∧ L (i,p)+H (i,p)≤M+1 :=
    bourgain_cubic_unrestricted_parity_scales (hsource i hi).1 (hsource i hi).2.2.1
      (hsource i hi).2.2.2 (hH₀.trans (hscale i hi)) (hM i hi) p

  have hT ip (hip : ip∈T) : ip.1∈S := (Finset.mem_product.mp hip).1
  have hs := hsieve M (ι × Fin 2) T (fun ip => q ip.1) (fun ip => N ip.1)
    L H (fun ip => a ip.1) (fun ip => r ip.1) (fun ip => μ ip.1)
    (fun ip => ℓ ip.1) (fun ip => ip.2) H₀ V W d hH₀ hH₀M hV hW hd
    (fun ip hip => ⟨(hsource ip.1 (hT ip hip)).1,
      (hsource ip.1 (hT ip hip)).2.1,(hsource ip.1 (hT ip hip)).2.2.2⟩)
    (fun ip hip => hscale ip.1 (hT ip hip))
    (fun ip hip => hK ip.1 (hT ip hip))
    (fun ip hip => hKW ip.1 (hT ip hip))
    (fun ip hip => har ip.1 (hT ip hip))
    (fun ip hip => (hdata ip.1 (hT ip hip) ip.2).2.1)
    (fun ip hip => ((hdata ip.1 (hT ip hip) ip.2).2.2.1).trans (hVscale ip.1 (hT ip hip)))
    (fun ip hip => (hdata ip.1 (hT ip hip) ip.2).2.2.2)
    (fun ip hip => hdscale ip.1 (hT ip hip))
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

  have hp := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hbound 12
  apply hp.trans
  simpa only [F,b,K₀,K₁,Nat.cast_add] using hs


private theorem exists_bourgain_cubic_unrestricted_C4_source_entry :
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
        0 < μ i ∧ μ i*(N : ℝ)^2 ≤ 1) →
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
          ∑ i ∈ S, (Real.sqrt N*Real.log (2*(N : ℝ))+1/(μ i*(N : ℝ)^2)+
            1/(Real.sqrt (μ i*(N:ℝ))*Real.sqrt (q i:ℝ)))) := by
  classical
  obtain ⟨C,hC,htransform⟩ := exists_bourgain_cubic_real_linear_stationary
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
  let E : ι → ℝ := fun i => Real.sqrt N*Real.log (2*(N : ℝ))+1/(μ i*(N : ℝ)^2)+
            1/(Real.sqrt (μ i*(N:ℝ))*Real.sqrt (q i:ℝ))
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
    obtain ⟨hqi,hqiN,hai,hμi,hμiN⟩ := hscale i hi
    have ht := htransform N (N+J) (q i) hN (by omega) (by omega) hqi hqiN
      (μ i) hμi hμiN (a i) hai (ℓ i)
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




private theorem bourgain_frozen_twelfth_assembly
    {a main err budget C D : ℝ} (ha : 0 ≤ a) (hm : 0 ≤ main) (he : 0 ≤ err)
    (hb : 0 ≤ budget) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hs : a ≤ C*(main+err)) (hd : main^12 ≤ D*budget) :
    a^12 ≤ (C^12*2^11*(D+1))*(budget+err^12) := by
  have hlast : D*budget+err^12 ≤ (D+1)*(budget+err^12) := by
    nlinarith only [hb,mul_nonneg hD (pow_nonneg he 12)]
  calc
    _ ≤ (C*(main+err))^12 := pow_le_pow_left₀ ha hs 12
    _ = C^12*(main+err)^12 := by rw [mul_pow]
    _ ≤ C^12*(2^11*(main^12+err^12)) :=
      mul_le_mul_of_nonneg_left (add_pow_le hm he 12) (pow_nonneg hC 12)
    _ ≤ C^12*(2^11*(D*budget+err^12)) := by gcongr
    _ ≤ C^12*(2^11*((D+1)*(budget+err^12))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hlast (by norm_num)) (pow_nonneg hC 12)
    _ = _ := by ring

set_option maxHeartbeats 400000 in
                                                                          
                                                                      
                                                                          
theorem exists_bourgain_C4_frozen_source_second_spacing_reduction
    {ε : ℝ} (hε : 0<ε) :
    ∃ C>(0:ℝ), ∀ (ι : Type v) [DecidableEq ι] (S : Finset ι) (f : ι → ℝ → ℝ)
      (m : ι → ℝ) (a : ι → ℤ) (q : ι → ℕ) (N H : ι → ℕ),
      (∀ i∈S, 1≤N i) → (∀ i∈S, H i≤N i) → ∀ B D : ℝ, 0≤B → 0≤D →
      (∀ i∈S, B*(2*(N i:ℝ)+1)^4≤1) → (∀ i∈S, D*(2*(N i:ℝ)+1)^2≤1) →
      (∀ i∈S, ∀ y∈Icc (m i-(2*(N i:ℝ)+1)) (m i+(2*(N i:ℝ)+1)),
        ContDiffAt ℝ 4 (f i) y) →
      (∀ i∈S, ∀ y∈Icc (m i-(2*(N i:ℝ)+1)) (m i+(2*(N i:ℝ)+1)),
        |iteratedDeriv 4 (f i) y|≤B) →
      (∀ i∈S, |iteratedDeriv 2 (f i) (m i)/2-(a i:ℝ)/(q i:ℝ)|≤D) →
      let μ := fun i => iteratedDeriv 3 (f i) (m i)/6
      let ℓ := fun i => deriv (f i) (m i)
      (∀ i∈S, 0<q i ∧ q i≤N i ∧ IsCoprime (a i) (q i:ℤ) ∧
        0<μ i ∧ μ i*(N i:ℝ)^2≤1) →
      ∀ (M : ℕ) [NeZero M] (H₀ V W d : ℝ),
      1≤H₀ → H₀≤M → 0≤V → 1≤W → 0<d →
      (∀ i∈S, H₀≤μ i*(q i:ℝ)*(N i:ℝ)^2) →
      (∀ i∈S, |-2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3|≤H₀*Real.sqrt H₀) →
      (∀ i∈S, |-2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3|/Real.sqrt H₀≤W) →
      (∀ i∈S, 7*(μ i*(q i:ℝ)*(N i:ℝ)^2)≤M) →
      (∀ i∈S, 7*(μ i*(q i:ℝ)*(N i:ℝ)^2)≤V*H₀) →
      (∀ i∈S, d≤μ i*(q i:ℝ)*N i) →
      ∃ r : ι → ℤ, (∀ i∈S, (q i:ℤ)∣a i*r i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let K := fun i => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
      let x := fun i p => (![-(r i:ℝ)*b i p/q i,-(r i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      let T := S ×ˢ (Finset.univ : Finset (Fin 2))
      let y := fun ip : ι × Fin 2 =>
        (![Int.fract (x ip.1 ip.2 0),Int.fract (x ip.1 ip.2 1),
          x ip.1 ip.2 2/Real.sqrt M,x ip.1 ip.2 3/Real.sqrt M] : Fin 4 → ℝ)
      let window : Fin 4 → ℝ :=
        ![1/(12*(M:ℝ)),1/(12*(M:ℝ)^2),(1/(M:ℝ)^2)/12,(1/(M:ℝ))/12]
      let P := (T ×ˢ T).filter (fun ij => ∀ e, |y ij.1 e-y ij.2 e|≤2*window e)
      (∑ i∈S, ‖∑ n∈Finset.Ioc (N i:ℤ) ((N i:ℤ)+H i),
          (𝐞 (f i (m i+n)):ℂ)‖)^12 ≤
        C*((5*W)^11*W^2*(6*(3+8*Real.pi*V)*(1+Real.log M))^12*
          (2/d)^6*(M:ℝ)^((12:ℝ)+ε)*(T.card:ℝ)^10*(P.card:ℝ)+
          (∑ i∈S, (Real.sqrt (N i)*Real.log (2*(N i:ℝ))+1/(μ i*(N i:ℝ)^2)+
            1/(Real.sqrt (μ i*(N i:ℝ))*Real.sqrt (q i:ℝ))))^12) := by


  classical
  obtain ⟨C,hC,hsource⟩ := exists_bourgain_cubic_unrestricted_C4_source_entry
  obtain ⟨C₂,hC₂,hgauss⟩ := exists_bourgain_cubic_frozen_gauss_sieve.{v} hε
  refine ⟨C^12*2^11*(C₂+1),by positivity,?_⟩
  intro ι instι S f m a q N H hN hH B D hB hD hfourSmall hquadSmall hf hfour hcurv
    μ ℓ hscale M instM H₀ V W d hH₀ hH₀M hV hW hd hdual hK hKW hM hVscale hdscale
  have hinv i (hi : i∈S) : ∃ r : ℤ, (q i:ℤ)∣a i*r-1 := by
    obtain ⟨r,t,he⟩ := (hscale i hi).2.2.1
    exact ⟨r,-t,by nlinarith only [he]⟩
  let r := fun i => if hi : i∈S then Classical.choose (hinv i hi) else 0
  have har i (hi : i∈S) : (q i:ℤ)∣a i*r i-1 := by
    dsimp only [r]
    rw [dite_eq_left hi]
    exact Classical.choose_spec (hinv i hi)
  refine ⟨r,har,?_⟩
  intro b τ K x T y window P
  let Src := fun i => ‖∑ n∈Finset.Ioc (N i:ℤ) ((N i:ℤ)+H i),
    (𝐞 (f i (m i+n)):ℂ)‖
  let Main := fun i (J : ℕ) => ‖(q i:ℂ)⁻¹*∑ k∈Finset.Icc
    ⌈(q i:ℝ)*(3*μ i*(N i:ℝ)^2+ℓ i)⌉
    ⌊(q i:ℝ)*(3*μ i*((N i:ℝ)+J)^2+ℓ i)⌋,
    let u := Real.sqrt (((k:ℝ)/(q i:ℝ)-ℓ i)/(3*μ i))
    bourgainQuadraticGauss (q i) (a i) k*
      ((𝐞 ((1:ℝ)/8-2*μ i*u^3):ℂ)/(Real.sqrt (6*μ i*u):ℂ))‖
  let E := fun i => Real.sqrt (N i)*Real.log (2*(N i:ℝ))+1/(μ i*(N i:ℝ)^2)+
    1/(Real.sqrt (μ i*(N i:ℝ))*Real.sqrt (q i:ℝ))
  have hprefix i (hi : i∈S) : ∃ J : ℕ, J≤H i ∧ Src i≤C*(Main i J+E i) := by
    obtain ⟨J,hJ,hbound⟩ := hsource Unit {()} (fun _ => f i) (fun _ => m i)
      (fun _ => a i) (fun _ => q i) (N i) (H i) (hN i hi) (hH i hi)
      B D hB hD (hfourSmall i hi) (hquadSmall i hi)
      (fun _ _ => hf i hi) (fun _ _ => hfour i hi)
      (fun _ _ => hcurv i hi) (fun _ _ => hscale i hi)
    simp only [Finset.sum_singleton] at hbound
    exact ⟨J,hJ,hbound⟩
  let J := fun i => if hi : i∈S then Classical.choose (hprefix i hi) else 0
  have hJ i (hi : i∈S) : J i≤H i ∧ Src i≤C*(Main i (J i)+E i) := by
    dsimp only [J]
    rw [dite_eq_left hi]
    exact Classical.choose_spec (hprefix i hi)
  have hs : (∑ i∈S,Src i) ≤ C*((∑ i∈S,Main i (J i))+(∑ i∈S,E i)) := by
    calc
      _ ≤ ∑ i∈S,C*(Main i (J i)+E i) := Finset.sum_le_sum (fun i hi => (hJ i hi).2)
      _ = _ := by rw [←Finset.mul_sum,Finset.sum_add_distrib]

  have hg := hgauss M ι S q N (fun i => N i+J i) a r μ ℓ H₀ V W d
    hH₀ hH₀M hV hW hd
    (fun i hi => ⟨(hscale i hi).1,hN i hi,by

      have hj := (hJ i hi).1
      have hh := hH i hi
      omega,(hscale i hi).2.2.2.1⟩)
    hdual hK hKW har hM hVscale hdscale
  let Budget := (5*W)^11*W^2*(6*(3+8*Real.pi*V)*(1+Real.log M))^12*
    (2/d)^6*(M:ℝ)^((12:ℝ)+ε)*(T.card:ℝ)^10*(P.card:ℝ)
  have hBudget : 0≤Budget := by dsimp only [Budget]; positivity
  have hg' : (∑ i∈S,Main i (J i))^12 ≤ C₂*Budget := by
    convert hg using 1 <;> simp only [Main,Budget,Nat.cast_add]
    ring
  have hC0 : 0≤C := zero_le_one.trans hC
  have hmain : 0≤∑ i∈S,Main i (J i) := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hE : 0≤∑ i∈S,E i := by
    apply Finset.sum_nonneg
    intro i hi
    have hNr : (1:ℝ)≤N i := by exact_mod_cast hN i hi
    have hlog : 0≤Real.log (2*(N i:ℝ)) := Real.log_nonneg (by linarith only [hNr])
    have hm := (hscale i hi).2.2.2.1
    dsimp only [E]
    positivity
  exact bourgain_frozen_twelfth_assembly
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hmain hE hBudget hC0 hC₂.le hs hg'


                                                                       
theorem bourgain_frozen_physical_dual_scales
    {L U N Q μ q n : ℝ} (hL : 0<L) (hU : 0<U) (hN : 0<N) (hQ : 0<Q)
    (hμ : L/6≤μ ∧ μ≤U) (hq : Q/2≤q ∧ q≤Q) (hn : N≤n ∧ n≤3*N)
    (hdual : 12≤L*Q*N^2) (hfrozen : 384≤L^2*Q^3*N^3) :
    let H₀ := L*Q*N^2/12
    let V := 756*U/L
    let W := 1+32/(L*Q^2*N)
    let K := -2*μ*(Real.sqrt (2/(3*μ*q)))^3
    1≤H₀ ∧ H₀≤μ*q*n^2 ∧
      7*(μ*q*n^2)≤63*U*Q*N^2 ∧
      7*(μ*q*n^2)≤V*H₀ ∧
      |K|≤H₀*Real.sqrt H₀ ∧ |K|/Real.sqrt H₀≤W := by
  intro H₀ V W K
  have hμp : 0<μ := (by positivity : 0<L/6).trans_le hμ.1
  have hqp : 0<q := (by positivity : 0<Q/2).trans_le hq.1
  have hnp : 0<n := hN.trans_le hn.1
  have hH₀ : 1≤H₀ := by dsimp only [H₀]; linarith only [hdual]
  have hH₀p : 0<H₀ := by linarith only [hH₀]
  have hsH : 0<Real.sqrt H₀ := Real.sqrt_pos.mpr hH₀p
  have hlo : H₀≤μ*q*n^2 := by
    calc
      H₀ = (L/6)*(Q/2)*N^2 := by dsimp only [H₀]; ring
      _ ≤ μ*q*n^2 :=
        mul_le_mul (mul_le_mul hμ.1 hq.1 (by positivity) hμp.le)
          (pow_le_pow_left₀ hN.le hn.1 2) (sq_nonneg _) (by positivity)
  have hhi : 7*(μ*q*n^2)≤63*U*Q*N^2 := by
    calc
      _ ≤ 7*(U*Q*(3*N)^2) := by gcongr <;> linarith only [hμ.2,hq.2,hn.2]
      _ = _ := by ring
  have hVeq : V*H₀=63*U*Q*N^2 := by
    dsimp only [V,H₀]
    field_simp
    ring
  refine ⟨hH₀,hlo,hhi,by rw [hVeq]; exact hhi,?_,?_⟩
  all_goals
    have hroot : (Real.sqrt (2/(3*μ*q)))^2*(3*μ*q)=2 :=
      (eq_div_iff (by positivity : 3*μ*q≠0)).mp (Real.sq_sqrt (by positivity))
    have he : K^2*(27*μ*q^3)=32 := by
      calc
        _ = 4*((Real.sqrt (2/(3*μ*q)))^2*(3*μ*q))^3 := by dsimp only [K]; ring
        _ = _ := by rw [hroot]; norm_num
    let D := (9/16)*L*Q^3
    have hDp : 0<D := by dsimp only [D]; positivity
    have hDle : D≤27*μ*q^3 := by
      have hh := mul_le_mul hμ.1 (pow_le_pow_left₀ (by positivity) hq.1 3)
        (by positivity : 0≤(Q/2)^3) hμp.le
      dsimp only [D]
      nlinarith only [hh]
    have hKD : K^2*D≤32 :=
      (mul_le_mul_of_nonneg_left hDle (sq_nonneg K)).trans_eq he
  · have hbig : 32≤(H₀*Real.sqrt H₀)^2*D := by
      have hx := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤384) hfrozen 2
      have heq : (H₀*Real.sqrt H₀)^2*D=(L^2*Q^3*N^3)^2/3072 := by
        rw [mul_pow,Real.sq_sqrt hH₀p.le]
        dsimp only [H₀,D]
        ring
      rw [heq]
      nlinarith only [hx]
    have hsq : K^2≤(H₀*Real.sqrt H₀)^2 :=
      (mul_le_mul_iff_left₀ hDp).mp (by nlinarith only [hKD,hbig])
    have hpos : 0≤H₀*Real.sqrt H₀ := by positivity
    nlinarith only [hsq,abs_nonneg K,sq_abs K,hpos]
  · let W₀ := 32/(L*Q^2*N)
    have hW₀ : 0<W₀ := by dsimp only [W₀]; positivity
    have heq : (W₀*Real.sqrt H₀)^2*D=48 := by
      rw [mul_pow,Real.sq_sqrt hH₀p.le]
      dsimp only [W₀,H₀,D]
      field_simp
      ring
    have hsq : K^2≤(W₀*Real.sqrt H₀)^2 :=
      (mul_le_mul_iff_left₀ hDp).mp (by nlinarith only [hKD,heq])
    have hpos : 0≤W₀*Real.sqrt H₀ := by positivity
    have hk : |K|≤W₀*Real.sqrt H₀ := by
      nlinarith only [hsq,abs_nonneg K,sq_abs K,hpos]
    have hh := (div_le_iff₀ hsH).mpr hk
    change |K|/Real.sqrt H₀≤1+W₀
    linarith only [hh]


private theorem bourgain_frozen_card_assembly
    {a C Loss s Z B t NonTri err Err : ℝ}
    (hC : 0 ≤ C) (hLoss : 0 ≤ Loss) (hs : 0 ≤ s) (hB : 0 ≤ B)
    (ht : 0 ≤ t) (hNT : 0 ≤ NonTri) (herr : 0 ≤ err)
    (hcard : s ≤ Z) (herror : err ≤ Z*Err)
    (hfirst : a ≤ C*(Loss*(2*s)^10*(4*(4*B*s*t+NonTri))+err^12)) :
    a ≤ 4*C*(Loss*(2*Z)^10*(4*B*Z*t+NonTri)+(Z*Err)^12) := by
  have hZ : 0 ≤ Z := hs.trans hcard
  have hraw : a ≤ 4*C*(Loss*(2*s)^10*(4*B*s*t+NonTri)+err^12) := by
    apply hfirst.trans
    nlinarith only [mul_nonneg hC (pow_nonneg herr 12)]
  have htri : 4*B*s*t ≤ 4*B*Z*t :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcard (mul_nonneg (by norm_num) hB)) ht
  have hT : Loss*(2*s)^10*(4*B*s*t+NonTri) ≤ 
      Loss*(2*Z)^10*(4*B*Z*t+NonTri) :=
    mul_le_mul
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg (by norm_num) hs)
          (mul_le_mul_of_nonneg_left hcard (by norm_num)) 10) hLoss)
      (add_le_add htri le_rfl)
      (add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB) hs) ht) hNT)
      (mul_nonneg hLoss (pow_nonneg (mul_nonneg (by norm_num) hZ) 10))
  exact hraw.trans (mul_le_mul_of_nonneg_left
    (add_le_add hT (pow_le_pow_left₀ herr herror 12))
    (mul_nonneg (by norm_num) hC))

set_option maxHeartbeats 400000 in
                                                                         
                                                                     
                                                                    
theorem exists_bourgain_C4_frozen_physical_source
    {ε : ℝ} (hε : 0<ε) :
    ∃ C > (0:ℝ), ∀ (ι : Type v) [DecidableEq ι] (S : Finset ι)
      (f : ℝ → ℝ) (r : ι → ℚ) (z : ι → ℝ) (m k : ι → ℤ)
      (H : ι → ℕ) (N Q Bmul : ℕ) (s : ℤ) (A B L F U X lambda : ℝ),
      0 < N → 0 < Q → 0 < L → 0 ≤ F → 0 < U → 0 ≤ X → 0<lambda → F≤L^2/16 →
      F*(6*(N:ℝ)+1)^4 ≤ 1 → (3*U/2)*(6*(N:ℝ)+1)^2 ≤ 1 →
      (∀ x∈Icc A B, ContDiffAt ℝ 4 f x) →
      (∀ x∈Icc A B, L ≤ iteratedDeriv 3 f x ∧ iteratedDeriv 3 f x ≤ 6*U) →
      (∀ x∈Icc A B, lambda≤|iteratedDeriv 4 f x| ∧ |iteratedDeriv 4 f x|≤F) →
      (∀ i∈S, z i∈Ioo A B) →
      (∀ i∈S, Icc ((m i:ℝ)-(6*(N:ℝ)+1)) ((m i:ℝ)+(6*(N:ℝ)+1)) ⊆ Icc A B) →
      (∀ i∈S, |z i-m i| ≤ 1/2) →
      (∀ i∈S, (N:ℤ) ≤ s+(N:ℤ)*k i-m i ∧ s+(N:ℤ)*k i-m i ≤ 3*(N:ℤ)) →
      (∀ n : ℤ, (S.filter (fun i => k i=n)).card ≤ Bmul) →
      (∀ i∈S, H i ≤ N) →
      (∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧ (r i).den ≤ N) →
      (∀ i∈S, iteratedDeriv 2 f (z i)/2=(r i:ℝ)) →
      (∀ i∈S, |iteratedDeriv 2 f (z i)/2| ≤ X) →
      12≤L*(Q:ℝ)*(N:ℝ)^2 → 384≤L^2*(Q:ℝ)^3*(N:ℝ)^3 →
      let Z := 4*(Bmul:ℝ)*(Q:ℝ)*(2*X*Q+1)
      let M : ℕ := ⌈63*U*(Q:ℝ)*(N:ℝ)^2⌉₊+1
      let V := 756*U/L
      let Wloss := 1+32/(L*(Q:ℝ)^2*N)
      let d := L*(Q:ℝ)*N/12
      let eta := 1/(6*(M:ℝ)^2)
      let zeta := Real.sqrt M/(6*(M:ℝ)^2)
      let E := 16*U*Real.sqrt (U*(Q:ℝ)^3)*zeta+3*F/4
      let Gamma := eta*(Q:ℝ)^2
      let rho := (12*U*Real.sqrt (U*(Q:ℝ)^3)/lambda)*zeta
      (S.card:ℝ)≤Z ∧
      (∑ i∈S, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖)^12 ≤
        C*((5*Wloss)^11*Wloss^2*(6*(3+8*Real.pi*V)*(1+Real.log M))^12*
          (2/d)^6*(M:ℝ)^((12:ℝ)+ε)*(2*Z)^10*
          (4*Bmul*Z*(1+6*U*(rho+1))+
            16*(Bmul:ℝ)^2*(2*Gamma+1)*(2*X+5)^2*(Gamma+48*E*(Q:ℝ)^2/L))+
          (Z*(Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)+
            Real.sqrt (12/(L*(N:ℝ)*Q))))^12) := by


  classical
  obtain ⟨C,hC,hsource⟩ := exists_bourgain_C4_frozen_source_second_spacing_reduction.{v} hε
  refine ⟨4*C,by positivity,?_⟩
  intro ι instι S f r z m k H N Q Bmul s A B L F U X lambda
    hN hQ hL hF hU hX hlambda hFL hfourSmall hquadSmall hf hthree hfour
    hz hbuffer hround hspan hmul hH hq hlevel hlevelX hdual hfrozen
    Z M V Wloss d eta zeta E Gamma rho
  let H₀ := L*(Q:ℝ)*(N:ℝ)^2/12
  have hNr : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hQr : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hfiber a : (S.filter (fun i => r i=a)).card ≤ 4*Bmul := by
    have hh := bourgain_curvature_level_block_multiplicity S f z m k N Bmul s
      hN hL (fun x hx => hf x ⟨hx.1.le,hx.2.le⟩)
      (fun x hx => (hthree x ⟨hx.1.le,hx.2.le⟩).1)
      hz hround hspan hmul (a:ℝ)
    apply (Finset.card_le_card (show S.filter (fun i => r i=a) ⊆
      S.filter (fun i => iteratedDeriv 2 f (z i)/2=(a:ℝ)) from ?_)).trans hh
    intro i hi
    obtain ⟨hiS,he⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hiS,(hlevel i hiS).trans (by rw [he])⟩
  have hcard : (S.card:ℝ) ≤ Z := by
    have hh := bourgain_bounded_denominator_count S r Q (4*Bmul) hX
      (fun i hi => by rw [←hlevel i hi]; exact hlevelX i hi)
      (fun i hi => (hq i hi).1) hfiber
    simpa only [Z,Nat.cast_mul,Nat.cast_ofNat] using hh
  refine ⟨hcard,?_⟩
  let W := fun i => (s+(N:ℤ)*k i-m i).toNat
  let mu := fun i => iteratedDeriv 3 f (m i)/6
  have hW i (hi : i∈S) : N ≤ W i ∧ W i ≤ 3*N ∧ m i+(W i:ℤ)=s+(N:ℤ)*k i := by
    have hh := hspan i hi
    dsimp only [W]
    constructor
    · omega
    · constructor <;> omega
  have hWp i (hi : i∈S) : 1 ≤ W i := (Nat.succ_le_iff.mpr hN).trans (hW i hi).1
  have hWr i (hi : i∈S) : (N:ℝ) ≤ W i ∧ (W i:ℝ) ≤ 3*(N:ℝ) := by
    constructor <;> exact_mod_cast (by first | exact (hW i hi).1 | exact (hW i hi).2.1)
  have hm i (hi : i∈S) : (m i:ℝ)∈Ioo A B := by
    have hrad : 0 < 6*(N:ℝ)+1 := by positivity
    have hlo := (hbuffer i hi (left_mem_Icc.mpr (by linarith only [hrad]))).1
    have hhi := (hbuffer i hi (right_mem_Icc.mpr (by linarith only [hrad]))).2
    constructor <;> linarith only [hlo,hhi,hrad]
  have hmu i (hi : i∈S) : 0 < mu i ∧ L/6 ≤ mu i ∧ mu i ≤ U := by
    have hh := hthree (m i) ⟨(hm i hi).1.le,(hm i hi).2.le⟩
    dsimp only [mu]
    constructor
    · linarith only [hh.1,hL]
    · constructor <;> linarith only [hh.1,hh.2]
  have hbuf i (hi : i∈S) :
      Icc ((m i:ℝ)-(2*(W i:ℝ)+1)) ((m i:ℝ)+(2*(W i:ℝ)+1)) ⊆ Icc A B := by
    intro x hx
    apply hbuffer i hi
    have hw := (hWr i hi).2
    constructor <;> linarith only [hx.1,hx.2,hw]
  have hsmall i (hi : i∈S) :
      F*(2*(W i:ℝ)+1)^4 ≤ 1 ∧ (3*U/2)*(2*(W i:ℝ)+1)^2 ≤ 1 := by
    have hw : 2*(W i:ℝ)+1 ≤ 6*(N:ℝ)+1 := by linarith only [(hWr i hi).2]
    constructor
    · exact (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hw 4) hF).trans hfourSmall
    · exact (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hw 2) (by positivity)).trans hquadSmall
  have hcurv i (hi : i∈S) :
      |iteratedDeriv 2 f (m i)/2-((r i).num:ℝ)/(r i).den| ≤ 3*U/2 := by
    have hh := bourgain_curvature_level_difference f hf
      (fun x hx => ⟨hL.le.trans (hthree x hx).1,(hthree x hx).2⟩)
      ⟨(hm i hi).1.le,(hm i hi).2.le⟩ ⟨(hz i hi).1.le,(hz i hi).2.le⟩
    rw [hlevel i hi,Rat.cast_def,abs_sub_comm (m i:ℝ) (z i)] at hh
    have hr := mul_le_mul_of_nonneg_left (hround i hi) (show 0 ≤ 3*U by positivity)
    exact hh.trans (by linarith only [hr])
  have hscale i (hi : i∈S) : mu i*(W i:ℝ)^2 ≤ 1 := by
    have ha : (W i:ℝ)^2 ≤ (2*(W i:ℝ)+1)^2 := by
      nlinarith only [show (0:ℝ) ≤ W i from Nat.cast_nonneg _]
    calc
      _ ≤ U*(2*(W i:ℝ)+1)^2 :=
        mul_le_mul (hmu i hi).2.2 ha (sq_nonneg _) hU.le
      _ ≤ (3*U/2)*(2*(W i:ℝ)+1)^2 := by gcongr; linarith only [hU]
      _ ≤ _ := (hsmall i hi).2

  let : NeZero M := ⟨by dsimp only [M]; omega⟩
  have hM : 63*U*(Q:ℝ)*(N:ℝ)^2≤(M:ℝ) := by
    have hh := Nat.le_ceil (63*U*(Q:ℝ)*(N:ℝ)^2)
    dsimp only [M]
    push_cast
    linarith only [hh]
  have hV : 0≤V := by dsimp only [V]; positivity
  have hWloss : 1≤Wloss := by
    have hp : 0≤32/(L*(Q:ℝ)^2*N) := by positivity
    dsimp only [Wloss]
    linarith only [hp]
  have hd : 0<d := by dsimp only [d]; positivity
  have hphysical i (hi : i∈S) :
      1≤H₀ ∧ H₀≤ mu i*((r i).den:ℝ)*(W i:ℝ)^2 ∧
        7*(mu i*((r i).den:ℝ)*(W i:ℝ)^2)≤63*U*(Q:ℝ)*(N:ℝ)^2 ∧
        7*(mu i*((r i).den:ℝ)*(W i:ℝ)^2)≤V*H₀ ∧
        |-2*mu i*(Real.sqrt (2/(3*mu i*((r i).den:ℝ))))^3|≤H₀*Real.sqrt H₀ ∧
        |-2*mu i*(Real.sqrt (2/(3*mu i*((r i).den:ℝ))))^3|/Real.sqrt H₀≤Wloss := by
    have hQq : (Q:ℝ)/2≤(r i).den := by
      have hh : (Q:ℝ)≤2*((r i).den:ℝ) := by exact_mod_cast (hq i hi).2.1
      linarith only [hh]
    exact bourgain_frozen_physical_dual_scales hL hU hNr hQr (hmu i hi).2
      ⟨hQq,Nat.cast_le.mpr (hq i hi).1⟩ (hWr i hi) hdual hfrozen
  have hdscale i (hi : i∈S) : d≤ mu i*((r i).den:ℝ)*W i := by
    have hqr : (Q:ℝ)≤2*((r i).den:ℝ) := by exact_mod_cast (hq i hi).2.1
    calc
      d = (L/6)*((Q:ℝ)/2)*N := by dsimp only [d]; ring
      _ ≤ mu i*((r i).den:ℝ)*W i :=
        mul_le_mul (mul_le_mul (hmu i hi).2.1 (by linarith only [hqr])
          (by positivity) (hmu i hi).1.le)
          (hWr i hi).1 hNr.le (mul_nonneg (hmu i hi).1.le (Nat.cast_nonneg _))
  by_cases hS : S.Nonempty
  · obtain ⟨i₀,hi₀⟩ := hS
    have hH₀ := (hphysical i₀ hi₀).1
    have hH₀M : H₀≤(M:ℝ) := by
      have hlow := (hphysical i₀ hi₀).2.1
      have hhigh := (hphysical i₀ hi₀).2.2.1.trans hM
      linarith only [hlow,hhigh,hH₀]
    obtain ⟨rinv,hinv,hbound⟩ := hsource ι S (fun _ => f) (fun i => (m i:ℝ))
      (fun i => (r i).num) (fun i => (r i).den) W H hWp
      (fun i hi => (hH i hi).trans (hW i hi).1) F (3*U/2) hF (by positivity)
      (fun i hi => (hsmall i hi).1) (fun i hi => (hsmall i hi).2)
      (fun i hi x hx => hf x (hbuf i hi hx))
      (fun i hi x hx => (hfour x (hbuf i hi hx)).2) hcurv
      (fun i hi => ⟨(r i).pos,((hq i hi).2.2.trans (hW i hi).1),
        (r i).isCoprime_num_den,(hmu i hi).1,hscale i hi⟩)
      M H₀ V Wloss d hH₀ hH₀M hV hWloss hd
      (fun i hi => (hphysical i hi).2.1)
      (fun i hi => (hphysical i hi).2.2.2.2.1)
      (fun i hi => (hphysical i hi).2.2.2.2.2)
      (fun i hi => (hphysical i hi).2.2.1.trans hM)
      (fun i hi => (hphysical i hi).2.2.2.1) hdscale
    have hc := bourgain_C4_physical_cloud_second_spacing S f z m k
      (fun i => (r i).num) rinv (fun i => (r i).den) N Q Bmul s M
      hN hL hF hU hX hlambda hFL hf hthree hfour hz hm hround hspan hmul
      (fun i hi => ⟨(r i).pos,(hq i hi).1,(hq i hi).2.1⟩) hinv
      (fun i hi => by simpa only [Rat.cast_def] using hlevel i hi) hlevelX


    let Err := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)+
      Real.sqrt (12/(L*(N:ℝ)*Q))
    have hErr i (hi : i∈S) :
        Real.sqrt (W i)*Real.log (2*(W i:ℝ))+1/(mu i*(W i:ℝ)^2)+
          1/(Real.sqrt (mu i*(W i:ℝ))*Real.sqrt (r i).den) ≤ Err := by
      have hQq : (Q:ℝ)/2 ≤ (r i).den := by
        have hh : (Q:ℝ) ≤ 2*((r i).den:ℝ) := by exact_mod_cast (hq i hi).2.1
        linarith only [hh]
      have hmup : 0 < mu i := (hmu i hi).1
      have hWi : (0:ℝ) < W i := by exact_mod_cast hWp i hi
      have hqi : (0:ℝ) < (r i).den := Nat.cast_pos.mpr (r i).pos
      have herr := bourgain_prescribed_source_error_le hN (hW i hi).1
        (hW i hi).2.1 hL (hmu i hi).2.1
      have hprod : L*(N:ℝ)*Q/12 ≤ mu i*(W i:ℝ)*(r i).den := by
        have hh := mul_le_mul (mul_le_mul (hmu i hi).2.1 (hWr i hi).1 hNr.le hmup.le)
          hQq (by positivity : 0 ≤ (Q:ℝ)/2) (by positivity : 0 ≤ mu i*(W i:ℝ))
        nlinarith only [hh]
      have hcap : 1/(Real.sqrt (mu i*(W i:ℝ))*Real.sqrt (r i).den) ≤
          Real.sqrt (12/(L*(N:ℝ)*Q)) := by
        rw [←Real.sqrt_mul (by positivity : 0 ≤ mu i*(W i:ℝ)),one_div,←Real.sqrt_inv]
        have hh := one_div_le_one_div_of_le (by positivity : 0 < L*(N:ℝ)*Q/12) hprod
        apply Real.sqrt_le_sqrt
        convert hh using 1
        · simp only [one_div]
        · field_simp
      dsimp only [Err]
      linarith only [herr,hcap]

    have hlog : 0≤Real.log (6*(N:ℝ)) := by
      have hn : (1:ℝ)≤N := by exact_mod_cast hN
      exact Real.log_nonneg (by linarith only [hn])
    have hErr0 : 0≤Err := by dsimp only [Err]; positivity
    let ErrorSum := ∑ i∈S,(Real.sqrt (W i)*Real.log (2*(W i:ℝ))+1/(mu i*(W i:ℝ)^2)+
      1/(Real.sqrt (mu i*(W i:ℝ))*Real.sqrt (r i).den))
    have hErrorSum0 : 0≤ErrorSum := by
      apply Finset.sum_nonneg
      intro i hi
      have hw1 : (1:ℝ)≤W i := by exact_mod_cast hWp i hi
      have hl := Real.log_nonneg (by linarith only [hw1] : 1≤2*(W i:ℝ))
      have hmup := (hmu i hi).1
      positivity
    have herrorSum : ErrorSum≤Z*Err := by
      calc
        _ ≤ ∑ _i∈S,Err := Finset.sum_le_sum hErr
        _ = S.card*Err := by simp only [Finset.sum_const,nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right hcard hErr0
    let Loss := (5*Wloss)^11*Wloss^2*(6*(3+8*Real.pi*V)*(1+Real.log M))^12*
      (2/d)^6*(M:ℝ)^((12:ℝ)+ε)
    let NonTri := 16*(Bmul:ℝ)^2*(2*Gamma+1)*(2*X+5)^2*(Gamma+48*E*(Q:ℝ)^2/L)
    let Pair := 4*Bmul*S.card*(1+6*U*(rho+1))+NonTri
    have hLoss : 0≤Loss := by dsimp only [Loss]; positivity
    have hE : 0≤E := by dsimp only [E,zeta]; positivity
    have hGamma : 0≤Gamma := by dsimp only [Gamma,eta]; positivity
    have hrho : 0≤rho := by dsimp only [rho,zeta]; positivity
    have hNT : 0≤NonTri := by dsimp only [NonTri]; positivity
    have hsrc :
        (∑ i∈S, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖)=
        ∑ i∈S, ‖∑ n∈Finset.Ioc (W i:ℤ) ((W i:ℤ)+H i),(𝐞 (f ((m i:ℝ)+n)):ℂ)‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [←(hW i hi).2.2,bourgain_integer_source_translation]
    dsimp only at hbound hc
    rw [←hsrc] at hbound
    rw [Finset.card_product,Finset.card_univ,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] at hbound
    rw [mul_comm (S.card:ℝ) 2] at hbound
    change _≤4*Pair at hc
    have hcweighted := mul_le_mul_of_nonneg_left hc
      (show 0≤Loss*(2*(S.card:ℝ))^10 by positivity)
    change _≤C*(Loss*(2*(S.card:ℝ))^10*_+ErrorSum^12) at hbound
    have hfirst := hbound.trans (mul_le_mul_of_nonneg_left
      (add_le_add hcweighted (le_refl (ErrorSum^12))) hC.le)
    exact bourgain_frozen_card_assembly hC.le hLoss (Nat.cast_nonneg S.card)
      (Nat.cast_nonneg Bmul) (by positivity) hNT hErrorSum0 hcard herrorSum hfirst
  · have hempty : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [hempty]
    simp only [Finset.sum_empty,zero_pow (by norm_num : (12:ℕ)≠0)]
    dsimp only [Z,Wloss,V,d,E,Gamma,rho,eta,zeta]
    positivity

open Expdb

private theorem sum_integer_Ioc_join (g : ℤ → ℂ) {a b c : ℤ}
    (hab : a≤b) (hbc : b≤c) :
    (∑ n∈Finset.Ioc a b,g n)+(∑ n∈Finset.Ioc b c,g n)=
      ∑ n∈Finset.Ioc a c,g n := by
  have hd : Disjoint (Finset.Ioc a b) (Finset.Ioc b c) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    simp only [Finset.mem_Ioc] at hn hm
    omega
  rw [←Finset.sum_union hd,Finset.Ioc_union_Ioc_eq_Ioc hab hbc]

private theorem sum_integer_blocks (g : ℤ → ℂ) (a : ℤ) {N u v : ℕ}
    (huv : u≤v) :
    (∑ k∈Finset.Ico u v,∑ n∈Finset.Ioc (a+(N:ℤ)*k)
      (a+(N:ℤ)*((k:ℤ)+1)),g n)=
      ∑ n∈Finset.Ioc (a+(N:ℤ)*u) (a+(N:ℤ)*v),g n := by
  induction v,huv using Nat.le_induction with
  | base => simp
  | succ v hv ih =>
    rw [Finset.sum_Ico_succ_top hv,ih]
    push_cast
    exact sum_integer_Ioc_join g
      (by gcongr)
      (by nlinarith only [Int.natCast_nonneg N])

                                                                                 
theorem norm_sum_integer_Ioc_le (g : ℤ → ℂ) (hg : ∀ n,‖g n‖≤1)
    {a b : ℤ} (hab : a≤b) :
    ‖∑ n∈Finset.Ioc a b,g n‖≤(b:ℝ)-a := by
  calc
    _ ≤ ∑ n∈Finset.Ioc a b,‖g n‖ := norm_sum_le _ _
    _ ≤ ∑ _n∈Finset.Ioc a b,(1:ℝ) := Finset.sum_le_sum (fun n _ => hg n)
    _ = _ := by
      simp only [Finset.sum_const,nsmul_eq_mul,mul_one,Int.card_Ioc]
      exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr hab)

                                                                                
theorem exists_buffered_integer_source_blocks_interval
    (g : ℤ → ℂ) (hg : ∀ n,‖g n‖≤1)
    {a b : ℤ} {A B : ℝ} (hab : a≤b) (ha : A≤a) (hb : (b:ℝ)≤B)
    (N : ℕ) (hN : 0<N) :
    ∃ S : Finset ℕ,
      (∀ k∈S, Icc ((a:ℝ)-2*(N:ℝ)+(N:ℝ)*k-(7*(N:ℝ)+2))
        ((a:ℝ)-2*(N:ℝ)+(N:ℝ)*k+(7*(N:ℝ)+2)) ⊆ Icc (A+1/2) (B-1/2)) ∧
      (∀ k∈S, a≤a+(N:ℤ)*k ∧ a+(N:ℤ)*k+N≤b) ∧
      ‖∑ n∈Finset.Ioc a b,g n‖≤23*(N:ℝ)+
        ∑ k∈S,‖∑ n∈Finset.Ioc (a+(N:ℤ)*k) (a+(N:ℤ)*k+N),g n‖ := by
  classical
  let q := (b-a).toNat/N
  have hNr : (1:ℝ)≤N := by exact_mod_cast hN
  have hcast : ((b-a).toNat:ℤ)=b-a := Int.toNat_of_nonneg (sub_nonneg.mpr hab)
  have hlow : (N:ℤ)*q≤b-a := by
    have h := Nat.div_mul_le_self (b-a).toNat N
    have h' : (q:ℤ)*(N:ℤ)≤((b-a).toNat:ℤ) := by exact_mod_cast h
    nlinarith only [h',hcast]
  have hhigh : b-a<(N:ℤ)*((q:ℤ)+1) := by
    have h := Nat.lt_mul_div_succ (b-a).toNat hN
    have h' : ((b-a).toNat:ℤ)<(N:ℤ)*((q:ℤ)+1) := by exact_mod_cast h
    omega
  have hlowR : (N:ℝ)*q≤(b:ℝ)-a := by exact_mod_cast hlow
  have hhighR : (b:ℝ)-a<(N:ℝ)*((q:ℝ)+1) := by exact_mod_cast hhigh
  by_cases hq : 22≤q
  · let S := Finset.Ico 12 (q-10)
    refine ⟨S,?_,?_,?_⟩
    · intro k hk x hx
      obtain ⟨hk₁,hk₂⟩ := Finset.mem_Ico.mp hk
      have hkr : (12:ℝ)≤k := by exact_mod_cast hk₁
      have hkr' : (k:ℝ)+11≤q := by exact_mod_cast (show k+11≤q by omega)
      have hNl := mul_le_mul_of_nonneg_left hkr (le_trans zero_le_one hNr)
      have hNu := mul_le_mul_of_nonneg_left hkr' (le_trans zero_le_one hNr)
      constructor <;> nlinarith only [ha,hb,hx.1,hx.2,hNl,hNu,hlowR,hNr]
    · intro k hk
      obtain ⟨hk₁,hk₂⟩ := Finset.mem_Ico.mp hk
      have hkq : (k:ℤ)+1≤q := by exact_mod_cast (show k+1≤q by omega)
      constructor
      · nlinarith only [Int.natCast_nonneg N,Int.natCast_nonneg k]
      · have h := mul_le_mul_of_nonneg_left hkq (Int.natCast_nonneg N)
        nlinarith only [h,hlow]
    · let lo := a+(N:ℤ)*12
      let hi := a+(N:ℤ)*(q-10:ℕ)
      have hqcast : ((q-10:ℕ):ℝ)=(q:ℝ)-10 := by rw [Nat.cast_sub (by omega)]; norm_num
      have hlo : a≤lo := by dsimp only [lo]; nlinarith only [Int.natCast_nonneg N]
      have hmid : lo≤hi := by dsimp only [lo,hi]; gcongr; omega
      have hhi : hi≤b := by
        have hh : ((q-10:ℕ):ℤ)≤q := by exact_mod_cast Nat.sub_le q 10
        have h := mul_le_mul_of_nonneg_left hh (Int.natCast_nonneg N)
        dsimp only [hi]
        omega
      have he := (sum_integer_Ioc_join g hlo (hmid.trans hhi))
      rw [←sum_integer_Ioc_join g hmid hhi] at he
      rw [←he]
      have hnorm := (norm_add_le (∑ n∈Finset.Ioc a lo,g n)
        ((∑ n∈Finset.Ioc lo hi,g n)+(∑ n∈Finset.Ioc hi b,g n))).trans
        (add_le_add le_rfl (norm_add_le (∑ n∈Finset.Ioc lo hi,g n)
          (∑ n∈Finset.Ioc hi b,g n)))
      have hb₁ := norm_sum_integer_Ioc_le g hg hlo
      have hb₂ := norm_sum_integer_Ioc_le g hg hhi
      have hblocks := sum_integer_blocks g a (N:=N) (u:=12) (v:=q-10) (by omega)
      norm_num only [Nat.cast_ofNat] at hblocks
      have hcore : ‖∑ n∈Finset.Ioc lo hi,g n‖≤
          ∑ k∈S,‖∑ n∈Finset.Ioc (a+(N:ℤ)*k) (a+(N:ℤ)*k+N),g n‖ := by
        dsimp only [lo,hi]
        rw [←hblocks]
        convert norm_sum_le _ _ using 1
        simp only [S,mul_add,mul_one,add_assoc]
      have hlor : (lo:ℝ)=(a:ℝ)+(N:ℝ)*12 := by simp only [lo,Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_ofNat]
      have hhir : (hi:ℝ)=(a:ℝ)+(N:ℝ)*((q:ℝ)-10) := by
        simp only [hi,Int.cast_add,Int.cast_mul,Int.cast_natCast,hqcast]
      nlinarith only [hnorm,hb₁,hb₂,hcore,hlor,hhir,hhighR]
  · refine ⟨∅,by simp,by simp,?_⟩
    simp only [Finset.sum_empty,add_zero]
    have hqR : (q:ℝ)+1≤22 := by exact_mod_cast (show q+1≤22 by omega)
    have h := mul_le_mul_of_nonneg_left hqR (le_trans zero_le_one hNr)
    have hn := norm_sum_integer_Ioc_le g hg hab
    nlinarith only [hn,hhighR,h,hNr]

                                                                                 
theorem exists_buffered_integer_source_blocks
    (g : ℤ → ℂ) (hg : ∀ n,‖g n‖≤1)
    {a b : ℤ} {P : ℝ} (hab : a≤b) (ha : P≤a) (hb : (b:ℝ)≤2*P)
    (N : ℕ) (hN : 0<N) :
    ∃ S : Finset ℕ,
      (∀ k∈S, Icc ((a:ℝ)-2*(N:ℝ)+(N:ℝ)*k-(7*(N:ℝ)+2))
        ((a:ℝ)-2*(N:ℝ)+(N:ℝ)*k+(7*(N:ℝ)+2)) ⊆ Icc (P+1/2) (2*P-1/2)) ∧
      (∀ k∈S, a≤a+(N:ℤ)*k ∧ a+(N:ℤ)*k+N≤b) ∧
      ‖∑ n∈Finset.Ioc a b,g n‖≤23*(N:ℝ)+
        ∑ k∈S,‖∑ n∈Finset.Ioc (a+(N:ℤ)*k) (a+(N:ℤ)*k+N),g n‖ :=
  exists_buffered_integer_source_blocks_interval g hg hab ha hb N hN

private theorem model_source_derivative_data {σ : ℝ} (hσ : 0<σ) :
    ∃ δ>(0:ℝ), ∀ (F : ℝ → ℝ) (T P : ℝ),
      0<T → 0<P → IsApproximateModelPhaseFunction F σ 3 δ →
      let f := fun x => T*F (x/P)
      (∀ x∈Ioo P (2*P), ContDiffAt ℝ 4 f x) ∧
      (∀ x∈Ioo P (2*P),
        modelPhaseJetLower σ 2*T/P^3 ≤ iteratedDeriv 3 f x ∧
        iteratedDeriv 3 f x ≤ (modelPhaseJetCoefficient σ 2+1)*T/P^3) ∧
      (∀ x∈Ioo P (2*P),
        modelPhaseJetLower σ 3*T/P^4 ≤ |iteratedDeriv 4 f x| ∧
        |iteratedDeriv 4 f x| ≤ (modelPhaseJetCoefficient σ 3+1)*T/P^4) ∧
      (∀ x∈Ioo P (2*P),
        |iteratedDeriv 2 f x/2| ≤ (modelPhaseJetCoefficient σ 1+1)*T/P^2/2) := by
  let δ := min 1 (min (modelPhaseJetLower σ 2) (modelPhaseJetLower σ 3))
  have hδ : 0<δ := lt_min (by norm_num)
    (lt_min (modelPhaseJetLower_pos hσ 2) (modelPhaseJetLower_pos hσ 3))
  refine ⟨δ,hδ,?_⟩
  intro F T P hT hP hF f
  have hpoint x (hx : x∈Ioo P (2*P)) : x/P∈Ioo (1:ℝ) 2 := by
    constructor
    · exact (lt_div_iff₀ hP).mpr (by simpa only [one_mul] using hx.1)
    · exact (div_lt_iff₀ hP).mpr hx.2
  have hfc x (hx : x∈Ioo P (2*P)) : ContDiffAt ℝ ∞ F (x/P) :=
    approximateModelPhase_contDiffAt hF (hpoint x hx)
  have hfd x (hx : x∈Ioo P (2*P)) : ContDiffAt ℝ ∞ f x := by
    dsimp only [f]
    exact contDiffAt_const.mul ((hfc x hx).comp x (by fun_prop))
  have hd x (hx : x∈Ioo P (2*P)) (n : ℕ) :
      iteratedDeriv n f x=T/P^n*iteratedDeriv n F (x/P) := by
    have hh : ∀ y∈Ioo P (2*P), ContDiffAt ℝ ∞ F (P⁻¹*y+0) := by
      intro y hy
      simpa only [add_zero,div_eq_mul_inv,mul_comm] using hfc y hy
    have ha := sargos_iteratedDeriv_comp_affine_local hh hx n
    simp only [add_zero] at ha
    have he : (fun y => F (y/P))=(fun y => F (P⁻¹*y)) := by
      funext y
      rw [div_eq_mul_inv,mul_comm]
    dsimp only [f]
    rw [iteratedDeriv_const_mul_field,he,ha,inv_pow]
    simp only [div_eq_mul_inv,mul_assoc,mul_comm P⁻¹ x]
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ min (modelPhaseJetLower σ 2) 1 :=
    le_min ((min_le_right _ _).trans (min_le_left _ _)) hδ1
  have hδ3 : δ ≤ min (modelPhaseJetLower σ 3) 1 :=
    le_min ((min_le_right _ _).trans (min_le_right _ _)) hδ1
  have hsign : modelPhaseJetSign σ 2=1 := by
    have he : (descPochhammer ℝ 2).eval (-σ)=σ*(σ+1) := by
      simp only [descPochhammer_eval_eq_prod_range,Finset.prod_range_succ,
        Finset.prod_range_zero,Nat.cast_zero,Nat.cast_one]
      ring
    unfold modelPhaseJetSign
    rw [he,ite_eq_left (by positivity)]
  refine ⟨fun x hx => (hfd x hx).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4),?_,?_,?_⟩
  · intro x hx
    have hh := approximateModelPhase_signedJet_bounds hσ hF (hpoint x hx) 2 (by norm_num) hδ2
    rw [hsign,one_mul] at hh
    rw [hd x hx 3]
    constructor
    · convert mul_le_mul_of_nonneg_left hh.1 (show 0 ≤ T/P^3 by positivity) using 1; ring
    · convert mul_le_mul_of_nonneg_left hh.2 (show 0 ≤ T/P^3 by positivity) using 1; ring
  · intro x hx
    have hh := approximateModelPhase_signedJet_bounds hσ hF (hpoint x hx) 3 le_rfl hδ3
    have hnon : 0 ≤ modelPhaseJetSign σ 3*iteratedDeriv 4 F (x/P) :=
      (modelPhaseJetLower_pos hσ 3).le.trans hh.1
    have he : |iteratedDeriv 4 F (x/P)|=
        modelPhaseJetSign σ 3*iteratedDeriv 4 F (x/P) := by
      rw [←abs_of_nonneg hnon,abs_mul,modelPhaseJetSign_abs,one_mul]
    rw [hd x hx 4,abs_mul,abs_of_pos (by positivity : 0<T/P^4),he]
    constructor
    · convert mul_le_mul_of_nonneg_left hh.1 (show 0 ≤ T/P^4 by positivity) using 1; ring
    · convert mul_le_mul_of_nonneg_left hh.2 (show 0 ≤ T/P^4 by positivity) using 1; ring
  · intro x hx
    have hh := approximateModelPhase_iteratedDeriv_error hF (hpoint x hx) 1 (by norm_num)
    have hr := iteratedDeriv_modelPhase_abs_le hσ.le (hpoint x hx) 1
    have hb : |iteratedDeriv 2 F (x/P)| ≤ modelPhaseJetCoefficient σ 1+1 := by
      have he := abs_add_le (iteratedDeriv 2 F (x/P)-iteratedDeriv 1 (modelPhase σ) (x/P))
        (iteratedDeriv 1 (modelPhase σ) (x/P))
      rw [sub_add_cancel] at he
      linarith only [he,hh,hr,hδ1]
    rw [hd x hx 2,abs_div,abs_mul,abs_of_pos (by positivity : 0<T/P^2)]
    rw [abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact div_le_div_of_nonneg_right
      (by convert mul_le_mul_of_nonneg_left hb (show 0 ≤ T/P^2 by positivity) using 1; ring)
      (by norm_num)

private theorem model_source_buffered_entry {σ : ℝ} (hσ : 0<σ) :
    ∃ δ>(0:ℝ), ∀ (F : ℝ → ℝ) (T P : ℝ) (a b N : ℕ),
      0<T → 0<P → 0<N → a ≤ b → P ≤ a → (b:ℝ) ≤ 2*P →
      IsApproximateModelPhaseFunction F σ 3 δ →
      let f := fun x => T*F (x/P)
      let A := P+1/2
      let B := 2*P-1/2
      let L := modelPhaseJetLower σ 2*T/P^3
      let U := (modelPhaseJetCoefficient σ 2+1)*T/P^3/6
      let lambda := modelPhaseJetLower σ 3*T/P^4
      let F4 := (modelPhaseJetCoefficient σ 3+1)*T/P^4
      let X := (modelPhaseJetCoefficient σ 1+1)*T/P^2/2
      0<L ∧ 0<U ∧ 0<lambda ∧ 0 ≤ F4 ∧ 0 ≤ X ∧
      (∀ x∈Icc A B, ContDiffAt ℝ 4 f x) ∧
      (∀ x∈Icc A B, L ≤ iteratedDeriv 3 f x ∧ iteratedDeriv 3 f x ≤ 6*U) ∧
      (∀ x∈Icc A B, lambda ≤ |iteratedDeriv 4 f x| ∧ |iteratedDeriv 4 f x| ≤ F4) ∧
      (∀ x∈Icc A B, |iteratedDeriv 2 f x/2| ≤ X) ∧
      ∃ S : Finset ℕ,
        (∀ k∈S, Icc ((a:ℝ)-2*(N:ℝ)+(N:ℝ)*k-(7*(N:ℝ)+2))
          ((a:ℝ)-2*(N:ℝ)+(N:ℝ)*k+(7*(N:ℝ)+2)) ⊆ Icc A B) ∧
        (∀ k∈S, (a:ℤ) ≤ a+(N:ℤ)*k ∧ a+(N:ℤ)*k+N ≤ b) ∧
        (∀ j : ℤ, (S.filter (fun k : ℕ => (k:ℤ)=j)).card ≤ 1) ∧
        ‖exponentialSumAt F T P a b‖ ≤ 1+23*(N:ℝ)+
          ∑ k∈S,‖∑ n∈Finset.Ioc ((a:ℤ)+(N:ℤ)*k)
            ((a:ℤ)+(N:ℤ)*k+N),(𝐞 (f n):ℂ)‖ := by
  obtain ⟨δ,hδ,hdata⟩ := model_source_derivative_data hσ
  refine ⟨δ,hδ,?_⟩
  intro F T P a b N hT hP hN hab ha hb hF f A B L U lambda F4 X
  obtain ⟨hreg,hthree,hfour,hcurv⟩ := hdata F T P hT hP hF
  have hinside : Icc A B ⊆ Ioo P (2*P) := by
    intro x hx
    dsimp only [A,B] at hx
    constructor <;> linarith only [hx.1,hx.2]
  have hc₂ := modelPhaseJetLower_pos hσ 2
  have hc₃ := modelPhaseJetLower_pos hσ 3
  have hC₁ := modelPhaseJetCoefficient_nonneg σ 1
  have hC₂ := modelPhaseJetCoefficient_nonneg σ 2
  have hC₃ := modelPhaseJetCoefficient_nonneg σ 3
  refine ⟨by dsimp only [L]; positivity,by dsimp only [U]; positivity,
    by dsimp only [lambda]; positivity,by dsimp only [F4]; positivity,
    by dsimp only [X]; positivity,
    fun x hx => hreg x (hinside hx),?_,
    fun x hx => hfour x (hinside hx),fun x hx => hcurv x (hinside hx),?_⟩
  · intro x hx
    obtain ⟨hl,hu⟩ := hthree x (hinside hx)
    refine ⟨hl,hu.trans_eq ?_⟩
    dsimp only [U]
    ring
  · obtain ⟨S,hbuf,hspan,hbound⟩ := exists_buffered_integer_source_blocks
      (fun n => (𝐞 (f n):ℂ)) (by intro n; simp)
      (a:=(a:ℤ)) (b:=(b:ℤ)) (P:=P) (by exact_mod_cast hab)
      (by exact_mod_cast ha) (by exact_mod_cast hb) N hN
    refine ⟨S,hbuf,hspan,?_,?_⟩
    · intro j
      apply Finset.card_le_one.mpr
      intro k hk l hl
      have hk' := (Finset.mem_filter.mp hk).2
      have hl' := (Finset.mem_filter.mp hl).2
      exact_mod_cast hk'.trans hl'.symm
    · rw [exponentialSumAt_eq_int_sum]
      rw [Finset.Icc_eq_cons_Ioc (by exact_mod_cast hab),Finset.sum_cons]
      have hh := norm_add_le (oscillatory F T P a)
        (∑ n∈Finset.Ioc (a:ℤ) b,oscillatory F T P n)
      rw [norm_oscillatory] at hh
      change ‖oscillatory F T P a+(∑ n∈Finset.Ioc (a:ℤ) b,oscillatory F T P n)‖ ≤ _
      dsimp only [f] at hbound
      change ‖∑ n∈Finset.Ioc (a:ℤ) b,oscillatory F T P n‖ ≤ _ at hbound
      linarith only [hh,hbound]

set_option maxHeartbeats 400000 in
private theorem exists_C4_all_minimal_arc_source_bands
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∃ Cdirect ≥ (1:ℝ), ∃ Cfrozen > (0:ℝ), ∀ (ι : Type v) [DecidableEq ι] (S : Finset ι)
      (f : ℝ → ℝ) (k : ι → ℤ) (H : ι → ℕ) (N Bmul : ℕ) (s : ℤ)
      (A B L F U X lambda : ℝ),
      0 < N → 0 < L → 0 ≤ F → 0 < U → 0 ≤ X → 0 < lambda →
      F ≤ L^2/16 →
      F*(6*(N:ℝ)+1)^4 ≤ 1 → (3*U/2)*(6*(N:ℝ)+1)^2 ≤ 1 →
      (∀ x∈Icc A B, ContDiffAt ℝ 4 f x) →
      (∀ x∈Icc A B, L ≤ iteratedDeriv 3 f x ∧ iteratedDeriv 3 f x ≤ 6*U) →
      (∀ x∈Icc A B, lambda ≤ |iteratedDeriv 4 f x| ∧ |iteratedDeriv 4 f x| ≤ F) →
      (∀ x∈Icc A B, |iteratedDeriv 2 f x/2| ≤ X) →
      (∀ n : ℤ, (S.filter (fun i => k i=n)).card ≤ Bmul) →
      (∀ i∈S, H i ≤ N) →
      let base := fun i => (s:ℝ)-2*(N:ℝ)+(N:ℝ)*(k i:ℝ)
      let curv := fun i => iteratedDeriv 2 f (base i)/2
      let delta := L*(N:ℝ)/8
      (∀ i∈S, Icc (base i-(7*(N:ℝ)+2)) (base i+(7*(N:ℝ)+2)) ⊆ Icc A B) →
      ∃ (r : ι → ℚ) (z : ι → ℝ),
        (∀ i∈S, z i∈Ioo (base i-(N:ℝ)/4) (base i+(N:ℝ)/4) ∧
          iteratedDeriv 2 f (z i)/2=(r i:ℝ) ∧
          (r i:ℝ)∈Ioo (curv i-delta) (curv i+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo (curv i-delta) (curv i+delta) → (r i).den ≤ a.den) ∧
      (∀ Q₀ : ℕ, 2 ≤ Q₀ →
        let D₀ := 8/(L*(N:ℝ)*(Q₀:ℝ))
        (∑ i∈S.filter (fun i => Q₀ ≤ (r i).den),
          ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖) ≤
          (N:ℝ)*Bmul*(4*(X+1)*D₀^2+D₀*(2+Real.log (D₀+1)))) ∧
      (∀ j : ℕ, 1 ≤ j →
      let q := fun i => (r i).den
      let Q : ℕ := 2^(j+1)
      let G := (S.filter (fun i => q i ≤ N ∧ 3 ≤ (L/2)*(q i:ℝ)^2*N)).filter
        (fun i => Nat.log 2 (q i)=j)
      let M : ℕ := ⌈63*U*(Q:ℝ)*(N:ℝ)^2⌉₊+1
      let D := 16/(L*(N:ℝ)*(Q:ℝ))
      let Y := (Bmul:ℝ)*(4*(X+1)*D^2+D*(2+Real.log (D+1)))
      let d := L*(Q:ℝ)*N/12
      let eta := 1/(6*(M:ℝ)^2)
      let zeta := Real.sqrt M/(6*(M:ℝ)^2)
      let E := 16*U*Real.sqrt (U*(Q:ℝ)^3)*zeta+3*F/4
      let Gamma := eta*(Q:ℝ)^2
      let rho := (12*U*Real.sqrt (U*(Q:ℝ)^3)/lambda)*zeta
      (G.card:ℝ) ≤ Y ∧
      (∑ i∈G, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖)^12 ≤
        C*((2/d)^6*(1+Real.log M)^12*(M:ℝ)^((12:ℝ)+ε)*(2*Y)^10*
          (4*Bmul*Y*(1+6*U*(rho+1))+
            16*(Bmul:ℝ)^2*(2*Gamma+1)*(2*X+5)^2*(Gamma+48*E*(Q:ℝ)^2/L))+
          (Y*(Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)))^12)) ∧
      (∀ j : ℕ,
      let Q : ℕ := 2^(j+1)
      let G := (S.filter (fun i => (r i).den ≤ N)).filter
        (fun i => Nat.log 2 (r i).den=j)
      let Z := 4*(Bmul:ℝ)*(Q:ℝ)*(2*X*Q+1)
      let M : ℕ := ⌈63*U*(Q:ℝ)*(N:ℝ)^2⌉₊+1
      let V := 756*U/L
      let Wloss := 1+32/(L*(Q:ℝ)^2*N)
      let d := L*(Q:ℝ)*N/12
      let eta := 1/(6*(M:ℝ)^2)
      let zeta := Real.sqrt M/(6*(M:ℝ)^2)
      let E := 16*U*Real.sqrt (U*(Q:ℝ)^3)*zeta+3*F/4
      let Gamma := eta*(Q:ℝ)^2
      let rho := (12*U*Real.sqrt (U*(Q:ℝ)^3)/lambda)*zeta
      (G.card:ℝ) ≤ Z ∧
      (∑ i∈G, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖) ≤
        Cdirect*Z*(3*(N:ℝ)*Real.sqrt (3*U*(Q:ℝ)*N)+
          Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)+
          Real.sqrt (12/(L*(N:ℝ)*Q))) ∧
      (12 ≤ L*(Q:ℝ)*(N:ℝ)^2 → 384 ≤ L^2*(Q:ℝ)^3*(N:ℝ)^3 →
      (∑ i∈G, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖)^12 ≤
        Cfrozen*((5*Wloss)^11*Wloss^2*(6*(3+8*Real.pi*V)*(1+Real.log M))^12*
          (2/d)^6*(M:ℝ)^((12:ℝ)+ε)*(2*Z)^10*
          (4*Bmul*Z*(1+6*U*(rho+1))+
            16*(Bmul:ℝ)^2*(2*Gamma+1)*(2*X+5)^2*(Gamma+48*E*(Q:ℝ)^2/L))+
          (Z*(Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)+
            Real.sqrt (12/(L*(N:ℝ)*Q))))^12))) := by
  classical
  obtain ⟨C,hC,hminorSource⟩ := exists_bourgain_C4_minimal_arc_source_band.{v} hε
  obtain ⟨Cdirect,hCdirect,hdirect⟩ := exists_bourgain_C4_low_denominator_source.{v}
  obtain ⟨Cfrozen,hCfrozen,hfrozenSource⟩ := exists_bourgain_C4_frozen_physical_source.{v} hε
  refine ⟨C,hC,Cdirect,hCdirect,Cfrozen,hCfrozen,?_⟩
  intro ι instι S f k H N Bmul s A B L F U X lambda
    hN hL hF hU hX hlambda hFL hfourSmall hquadSmall hf hthree hfour
    hlevelX hmul hH base curv delta hbuffer
  obtain ⟨r,z,hr,htail,hminor⟩ := hminorSource ι S f k H N Bmul s
    A B L F U X lambda hN hL hF hU hX hlambda hFL hfourSmall hquadSmall
    hf hthree hfour hlevelX hmul hH hbuffer
  refine ⟨r,z,hr,htail,hminor,?_⟩
  have hgeo i (hi : i∈S) :
      z i∈Ioo A B ∧ |z i-(round (z i):ℝ)| ≤ 1/2 ∧
        ((N:ℤ) ≤ s+(N:ℤ)*k i-round (z i) ∧
          s+(N:ℤ)*k i-round (z i) ≤ 3*(N:ℤ)) ∧
        Icc ((round (z i):ℝ)-(6*(N:ℝ)+1))
          ((round (z i):ℝ)+(6*(N:ℝ)+1)) ⊆ Icc A B :=
    bourgain_minimal_arc_rounded_source_geometry hN
      (by dsimp only [base]; push_cast; ring) (hr i hi).1 (hbuffer i hi)
  intro j Q G Z M V Wloss d eta zeta E Gamma rho
  have hQ : 0<Q := by dsimp only [Q]; positivity
  have hGS : G ⊆ S := fun i hi =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
  have hmulG n : (G.filter (fun i => k i=n)).card ≤ Bmul :=
    (Finset.card_le_card (Finset.filter_subset_filter _ hGS)).trans (hmul n)
  have hqdata i (hi : i∈G) :
      (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧ (r i).den ≤ N := by
    obtain ⟨hi',hj⟩ := Finset.mem_filter.mp hi
    have hlo := Nat.pow_log_le_self 2 (r i).pos.ne'
    have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1<(2:ℕ)) (r i).den
    rw [hj] at hlo hhi
    refine ⟨hhi.le,?_,(Finset.mem_filter.mp hi').2⟩
    calc
      Q=2*2^j := by dsimp only [Q]; rw [pow_succ,Nat.mul_comm]
      _ ≤ _ := Nat.mul_le_mul_left _ hlo
  have hbound := hdirect ι G f r z (fun i => round (z i)) k H N Q Bmul s
    A B L F U X hN hQ hL hF hU hX hfourSmall hquadSmall
    hf hthree (fun x hx => (hfour x hx).2)
    (fun i hi => (hgeo i (hGS hi)).1)
    (fun i hi => (hgeo i (hGS hi)).2.2.2)
    (fun i hi => (hgeo i (hGS hi)).2.1)
    (fun i hi => (hgeo i (hGS hi)).2.2.1)
    hmulG (fun i hi => hH i (hGS hi)) hqdata
    (fun i hi => (hr i (hGS hi)).2.1)
    (fun i hi => hlevelX (z i)
      ⟨(hgeo i (hGS hi)).1.1.le,(hgeo i (hGS hi)).1.2.le⟩)
  refine ⟨hbound.1,hbound.2,?_⟩
  intro hdual hfrozen
  exact (hfrozenSource ι G f r z (fun i => round (z i)) k H N Q Bmul s
    A B L F U X lambda hN hQ hL hF hU hX hlambda hFL
    hfourSmall hquadSmall hf hthree hfour
    (fun i hi => (hgeo i (hGS hi)).1)
    (fun i hi => (hgeo i (hGS hi)).2.2.2)
    (fun i hi => (hgeo i (hGS hi)).2.1)
    (fun i hi => (hgeo i (hGS hi)).2.2.1)
    hmulG (fun i hi => hH i (hGS hi)) hqdata
    (fun i hi => (hr i (hGS hi)).2.1)
    (fun i hi => hlevelX (z i)
      ⟨(hgeo i (hGS hi)).1.1.le,(hgeo i (hGS hi)).1.2.le⟩)
    hdual hfrozen).2

set_option maxHeartbeats 400000 in
                                                                                        
                                                                                      
                                                                                  
theorem exists_bourgain_model_source_bands {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∃ δ>(0:ℝ), ∃ C>(0:ℝ), ∃ Cdirect ≥ (1:ℝ), ∃ Cfrozen>(0:ℝ),
      ∀ (G : ℝ → ℝ) (T P : ℝ) (a b N : ℕ),
      0<T → 0<P → 0<N → a ≤ b → P ≤ a → (b:ℝ) ≤ 2*P →
      IsApproximateModelPhaseFunction G σ 3 δ →
      let f := fun x => T*G (x/P)
      let L := modelPhaseJetLower σ 2*T/P^3
      let U := (modelPhaseJetCoefficient σ 2+1)*T/P^3/6
      let lambda := modelPhaseJetLower σ 3*T/P^4
      let F := (modelPhaseJetCoefficient σ 3+1)*T/P^4
      let X := (modelPhaseJetCoefficient σ 1+1)*T/P^2/2
      F ≤ L^2/16 →
      F*(6*(N:ℝ)+1)^4 ≤ 1 → (3*U/2)*(6*(N:ℝ)+1)^2 ≤ 1 →
      ∃ S : Finset ℕ,
      let s : ℤ := a
      let k := fun i : ℕ => (i:ℤ)
      let H := fun _ : ℕ => N
      let Bmul : ℕ := 1
      let base := fun i => (s:ℝ)-2*(N:ℝ)+(N:ℝ)*(k i:ℝ)
      let curv := fun i => iteratedDeriv 2 f (base i)/2
      let delta := L*(N:ℝ)/8
      (‖exponentialSumAt G T P a b‖ ≤ 1+23*(N:ℝ)+
        ∑ i∈S,‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖) ∧
      ∃ (r : ℕ → ℚ) (z : ℕ → ℝ),
        (∀ i∈S, z i∈Ioo (base i-(N:ℝ)/4) (base i+(N:ℝ)/4) ∧
          iteratedDeriv 2 f (z i)/2=(r i:ℝ) ∧
          (r i:ℝ)∈Ioo (curv i-delta) (curv i+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo (curv i-delta) (curv i+delta) → (r i).den ≤ a.den) ∧
      (∀ Q₀ : ℕ, 2 ≤ Q₀ →
        let D₀ := 8/(L*(N:ℝ)*(Q₀:ℝ))
        (∑ i∈S.filter (fun i => Q₀ ≤ (r i).den),
          ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖) ≤
          (N:ℝ)*Bmul*(4*(X+1)*D₀^2+D₀*(2+Real.log (D₀+1)))) ∧
      (∀ j : ℕ, 1 ≤ j →
      let q := fun i => (r i).den
      let Q : ℕ := 2^(j+1)
      let G := (S.filter (fun i => q i ≤ N ∧ 3 ≤ (L/2)*(q i:ℝ)^2*N)).filter
        (fun i => Nat.log 2 (q i)=j)
      let M : ℕ := ⌈63*U*(Q:ℝ)*(N:ℝ)^2⌉₊+1
      let D := 16/(L*(N:ℝ)*(Q:ℝ))
      let Y := (Bmul:ℝ)*(4*(X+1)*D^2+D*(2+Real.log (D+1)))
      let d := L*(Q:ℝ)*N/12
      let eta := 1/(6*(M:ℝ)^2)
      let zeta := Real.sqrt M/(6*(M:ℝ)^2)
      let E := 16*U*Real.sqrt (U*(Q:ℝ)^3)*zeta+3*F/4
      let Gamma := eta*(Q:ℝ)^2
      let rho := (12*U*Real.sqrt (U*(Q:ℝ)^3)/lambda)*zeta
      (G.card:ℝ) ≤ Y ∧
      (∑ i∈G, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖)^12 ≤
        C*((2/d)^6*(1+Real.log M)^12*(M:ℝ)^((12:ℝ)+ε)*(2*Y)^10*
          (4*Bmul*Y*(1+6*U*(rho+1))+
            16*(Bmul:ℝ)^2*(2*Gamma+1)*(2*X+5)^2*(Gamma+48*E*(Q:ℝ)^2/L))+
          (Y*(Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)))^12)) ∧
      (∀ j : ℕ,
      let Q : ℕ := 2^(j+1)
      let G := (S.filter (fun i => (r i).den ≤ N)).filter
        (fun i => Nat.log 2 (r i).den=j)
      let Z := 4*(Bmul:ℝ)*(Q:ℝ)*(2*X*Q+1)
      let M : ℕ := ⌈63*U*(Q:ℝ)*(N:ℝ)^2⌉₊+1
      let V := 756*U/L
      let Wloss := 1+32/(L*(Q:ℝ)^2*N)
      let d := L*(Q:ℝ)*N/12
      let eta := 1/(6*(M:ℝ)^2)
      let zeta := Real.sqrt M/(6*(M:ℝ)^2)
      let E := 16*U*Real.sqrt (U*(Q:ℝ)^3)*zeta+3*F/4
      let Gamma := eta*(Q:ℝ)^2
      let rho := (12*U*Real.sqrt (U*(Q:ℝ)^3)/lambda)*zeta
      (G.card:ℝ) ≤ Z ∧
      (∑ i∈G, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖) ≤
        Cdirect*Z*(3*(N:ℝ)*Real.sqrt (3*U*(Q:ℝ)*N)+
          Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)+
          Real.sqrt (12/(L*(N:ℝ)*Q))) ∧
      (12 ≤ L*(Q:ℝ)*(N:ℝ)^2 → 384 ≤ L^2*(Q:ℝ)^3*(N:ℝ)^3 →
      (∑ i∈G, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖)^12 ≤
        Cfrozen*((5*Wloss)^11*Wloss^2*(6*(3+8*Real.pi*V)*(1+Real.log M))^12*
          (2/d)^6*(M:ℝ)^((12:ℝ)+ε)*(2*Z)^10*
          (4*Bmul*Z*(1+6*U*(rho+1))+
            16*(Bmul:ℝ)^2*(2*Gamma+1)*(2*X+5)^2*(Gamma+48*E*(Q:ℝ)^2/L))+
          (Z*(Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)+
            Real.sqrt (12/(L*(N:ℝ)*Q))))^12))) := by
  classical
  obtain ⟨δ,hδ,hentry⟩ := model_source_buffered_entry hσ
  obtain ⟨C,hC,Cdirect,hCdirect,Cfrozen,hCfrozen,hbands⟩ :=
    exists_C4_all_minimal_arc_source_bands.{0} hε
  refine ⟨δ,hδ,C,hC,Cdirect,hCdirect,Cfrozen,hCfrozen,?_⟩
  intro G T P a b N hT hP hN hab ha hb hG f L U lambda F X hFL hsmall hquad
  let A := P+1/2
  let B := 2*P-1/2
  obtain ⟨hL,hU,hlambda,hF,hX,hreg,hthree,hfour,hcurv,S,hbuf,_hspan,hmul,hsource⟩ :=
    hentry G T P a b N hT hP hN hab ha hb hG
  refine ⟨S,?_⟩
  intro s k H Bmul base curv delta
  refine ⟨?_,?_⟩
  · exact hsource
  · exact hbands ℕ S f k H N Bmul s A B L F U X lambda
      hN hL hF hU hX hlambda hFL hsmall hquad hreg hthree hfour hcurv
      hmul (fun _ _ => le_rfl) hbuf

                                                                                 
theorem sum_by_denominator_bands {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (q : ι → ℕ) (w : ι → ℝ) (N : ℕ) :
    (∑ i∈S,w i) =
      (∑ i∈S.filter (fun i => N+1 ≤ q i),w i)+
      ∑ j∈Finset.range (Nat.log 2 N+1),
        ∑ i∈(S.filter (fun i => q i ≤ N)).filter (fun i => Nat.log 2 (q i)=j),w i := by
  have hmap : ∀ i∈S.filter (fun i => q i ≤ N),
      Nat.log 2 (q i)∈Finset.range (Nat.log 2 N+1) := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      (Nat.log_mono_right (Finset.mem_filter.mp hi).2))
  rw [Finset.sum_fiberwise_of_maps_to hmap w]
  have h := Finset.sum_filter_add_sum_filter_not S (fun i => N+1 ≤ q i) w
  simpa only [Nat.not_le, Nat.lt_succ_iff] using h.symm

public  theorem boundary_and_bands_twelfth (B A : ℝ) (g : ℕ → ℝ)
    (J : ℕ) (hB : 0 ≤ B) (hA : 0 ≤ A) (hg : ∀ j,0 ≤ g j) :
    (B+A+∑ j∈Finset.range J,g j)^12 ≤
      ((J:ℝ)+2)^11*(B^12+A^12+∑ j∈Finset.range J,(g j)^12) := by
  let f : ℕ → ℝ := fun j => if j=0 then B else if j=1 then A else g (j-2)
  have hf (j : ℕ) : 0 ≤ f j := by
    dsimp only [f]
    split_ifs
    · exact hB
    · exact hA
    · exact hg _
  have hs (p : ℕ) :
      (∑ j∈Finset.range (2+J),(f j)^p) =
        B^p+A^p+∑ j∈Finset.range J,(g j)^p := by
    rw [Finset.sum_range_add]
    have hne (x : ℕ) : 2+x≠1 := by omega
    simp [Finset.sum_range_succ,f,hne]
  have h := pow_sum_le_card_mul_sum_pow
    (s:=Finset.range (2+J)) (f:=f) (fun j _ => hf j) 11
  have hs1 := hs 1
  simp only [pow_one] at hs1
  rw [hs1,hs 12] at h
  simpa only [Finset.card_range,Nat.cast_add,Nat.cast_ofNat,add_comm (2:ℝ)] using h

private theorem band_minor_threshold {L n Q q : ℝ}
    (hL : 0 ≤ L) (hn : 0 ≤ n) (hQ : 0 ≤ Q) (hbound : Q ≤ 2*q)
    (hminor : 3 ≤ L*Q^2*n/8) :
    3 ≤ (L/2)*q^2*n := by
  have hsq : Q^2 ≤ 4*q^2 := by nlinarith
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsq hL) hn
  nlinarith only [h,hminor]

set_option maxHeartbeats 400000 in
                                                                             
                                                                                
                                                                             
theorem exists_bourgain_model_source_global {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∃ δ>(0:ℝ), ∃ C>(0:ℝ), ∃ Cdirect ≥ (1:ℝ), ∃ Cfrozen>(0:ℝ),
      ∀ (G : ℝ → ℝ) (T P : ℝ) (a b N : ℕ),
      0<T → 0<P → 0<N → a ≤ b → P ≤ a → (b:ℝ) ≤ 2*P →
      IsApproximateModelPhaseFunction G σ 3 δ →
      let L := modelPhaseJetLower σ 2*T/P^3
      let U := (modelPhaseJetCoefficient σ 2+1)*T/P^3/6
      let lambda := modelPhaseJetLower σ 3*T/P^4
      let F := (modelPhaseJetCoefficient σ 3+1)*T/P^4
      let X := (modelPhaseJetCoefficient σ 1+1)*T/P^2/2
      F ≤ L^2/16 →
      F*(6*(N:ℝ)+1)^4 ≤ 1 → (3*U/2)*(6*(N:ℝ)+1)^2 ≤ 1 →
      let J := Nat.log 2 N+1
      let Dtail := 8/(L*(N:ℝ)*(N+1:ℕ))
      let Tail := (N:ℝ)*(4*(X+1)*Dtail^2+Dtail*(2+Real.log (Dtail+1)))
      let budget := fun j : ℕ =>
        let Q : ℕ := 2^(j+1)
        let Z := 4*(Q:ℝ)*(2*X*Q+1)
        let M : ℕ := ⌈63*U*(Q:ℝ)*(N:ℝ)^2⌉₊+1
        let V := 756*U/L
        let Wloss := 1+32/(L*(Q:ℝ)^2*N)
        let d := L*(Q:ℝ)*N/12
        let eta := 1/(6*(M:ℝ)^2)
        let zeta := Real.sqrt M/(6*(M:ℝ)^2)
        let E := 16*U*Real.sqrt (U*(Q:ℝ)^3)*zeta+3*F/4
        let Gamma := eta*(Q:ℝ)^2
        let rho := (12*U*Real.sqrt (U*(Q:ℝ)^3)/lambda)*zeta
        let D := 16/(L*(N:ℝ)*(Q:ℝ))
        let Y := 4*(X+1)*D^2+D*(2+Real.log (D+1))
        let Err := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)
        let Pair := fun R : ℝ =>
          4*R*(1+6*U*(rho+1))+
            16*(2*Gamma+1)*(2*X+5)^2*(Gamma+48*E*(Q:ℝ)^2/L)
        if 1 ≤ j ∧ 3 ≤ L*(Q:ℝ)^2*N/8 then
          C*((2/d)^6*(1+Real.log M)^12*(M:ℝ)^((12:ℝ)+ε)*(2*Y)^10*Pair Y+
            (Y*Err)^12)
        else if 12 ≤ L*(Q:ℝ)*(N:ℝ)^2 ∧ 384 ≤ L^2*(Q:ℝ)^3*(N:ℝ)^3 then
          Cfrozen*((5*Wloss)^11*Wloss^2*(6*(3+8*Real.pi*V)*(1+Real.log M))^12*
            (2/d)^6*(M:ℝ)^((12:ℝ)+ε)*(2*Z)^10*Pair Z+
            (Z*(Err+Real.sqrt (12/(L*(N:ℝ)*Q))))^12)
        else
          (Cdirect*Z*(3*(N:ℝ)*Real.sqrt (3*U*(Q:ℝ)*N)+
            Err+Real.sqrt (12/(L*(N:ℝ)*Q))))^12
      ‖exponentialSumAt G T P a b‖^12 ≤
        ((J:ℝ)+2)^11*((1+23*(N:ℝ))^12+Tail^12+
          ∑ j∈Finset.range J,budget j) := by
  classical
  obtain ⟨δ,hδ,C,hC,Cd,hCd,Cf,hCf,hentry⟩ := exists_bourgain_model_source_bands hσ hε
  refine ⟨δ,hδ,C,hC,Cd,hCd,Cf,hCf,?_⟩
  intro G T P a b N hT hP hN hab ha hb hG L U lambda F X hFL hsmall hquad J Dtail Tail budget
  obtain ⟨S,hs,r,_z,_harc,htail,hminor,hlow⟩ :=
    hentry G T P a b N hT hP hN hab ha hb hG hFL hsmall hquad
  let w : ℕ → ℝ := fun i => ‖∑ n∈Finset.Ioc ((a:ℤ)+(N:ℤ)*i)
    ((a:ℤ)+(N:ℤ)*i+N),(𝐞 (T*G ((n:ℝ)/P)):ℂ)‖
  let q : ℕ → ℕ := fun i => (r i).den
  let band : ℕ → ℝ := fun j =>
    ∑ i∈(S.filter (fun i => q i ≤ N)).filter (fun i => Nat.log 2 (q i)=j),w i
  let tail := ∑ i∈S.filter (fun i => N+1 ≤ q i),w i
  have hw (i : ℕ) : 0 ≤ w i := norm_nonneg _
  have hband (j : ℕ) : 0 ≤ band j := Finset.sum_nonneg (fun i _ => hw i)
  have ht0 : 0 ≤ tail := Finset.sum_nonneg (fun i _ => hw i)
  have ht : tail ≤ Tail := by
    simpa only [tail,Tail,Dtail,w,q,Nat.cast_one,mul_one,one_mul] using
      htail (N+1) (by omega)
  have hL : 0<L := div_pos (mul_pos (modelPhaseJetLower_pos hσ 2) hT)
    (pow_pos hP 3)
  have hbnd (j : ℕ) : (band j)^12 ≤ budget j := by
    let Q : ℕ := 2^(j+1)
    by_cases hm : 1 ≤ j ∧ 3 ≤ L*(Q:ℝ)^2*N/8
    · have hsub (i : ℕ) (hi : Nat.log 2 (q i)=j) :
          3 ≤ (L/2)*(q i:ℝ)^2*N := by
        have hlo := Nat.pow_log_le_self 2 (r i).pos.ne'
        change 2^Nat.log 2 (q i) ≤ q i at hlo
        rw [hi] at hlo
        have hQ : Q ≤ 2*q i := by
          dsimp only [Q]
          rw [pow_succ]
          omega
        exact band_minor_threshold hL.le (Nat.cast_nonneg N)
          (Nat.cast_nonneg Q) (by exact_mod_cast hQ) hm.2
      have hset :
          (S.filter (fun i => q i ≤ N)).filter (fun i => Nat.log 2 (q i)=j) =
          (S.filter (fun i => q i ≤ N ∧ 3 ≤ (L/2)*(q i:ℝ)^2*N)).filter
            (fun i => Nat.log 2 (q i)=j) := by
        ext i
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨hi,hiN⟩,hij⟩
          exact ⟨⟨hi,hiN,hsub i hij⟩,hij⟩
        · rintro ⟨⟨hi,hiN,_⟩,hij⟩
          exact ⟨⟨hi,hiN⟩,hij⟩
      have hh := (hminor j hm.1).2
      change (∑ i∈(S.filter (fun i => q i ≤ N ∧ 3 ≤ (L/2)*(q i:ℝ)^2*N)).filter
        (fun i => Nat.log 2 (q i)=j),w i)^12 ≤ _ at hh
      rw [← hset] at hh
      simpa only [budget,ite_eq_left hm,Q,band,Nat.cast_one,mul_one,one_mul,one_pow,
        add_assoc] using hh
    · by_cases hf : 12 ≤ L*(Q:ℝ)*(N:ℝ)^2 ∧
          384 ≤ L^2*(Q:ℝ)^3*(N:ℝ)^3
      · have hh := (hlow j).2.2 hf.1 hf.2
        simpa only [budget,ite_eq_right hm,ite_eq_left hf,Q,band,w,q,Nat.cast_one,mul_one,
          one_mul,one_pow,add_assoc] using hh
      · have hh := pow_le_pow_left₀ (hband j) (hlow j).2.1 12
        simpa only [budget,ite_eq_right hm,ite_eq_right hf,Q,band,w,q,Nat.cast_one,mul_one,
          one_mul,add_assoc] using hh
  change ‖exponentialSumAt G T P a b‖ ≤ 1+23*(N:ℝ)+∑ i∈S,w i at hs
  rw [sum_by_denominator_bands S q w N] at hs
  change ‖exponentialSumAt G T P a b‖ ≤ 1+23*(N:ℝ)+
    (tail+∑ j∈Finset.range J,band j) at hs
  have hpow := pow_le_pow_left₀ (norm_nonneg _) hs 12
  have hholder := boundary_and_bands_twelfth (1+23*(N:ℝ)) tail band J
    (by positivity) ht0 hband
  rw [← add_assoc] at hpow
  apply hpow.trans (hholder.trans ?_)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add
    (add_le_add le_rfl (pow_le_pow_left₀ ht0 ht 12))
    (Finset.sum_le_sum (fun j _ => hbnd j))

                                                                 

open Filter Expdb
open scoped Topology

private theorem source_smallness_of_scale
    {c C D T P R n : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hT : 0 ≤ T) (hP : 0<P) (hR : 0<R)
    (hn : 1 ≤ n) (hupper : n ≤ P/R)
    (hfirst : 16*D*P^2 ≤ c^2*T)
    (hfour : D*7^4*T ≤ R^4)
    (hthird : (49*C/4)*T ≤ P*R^2) :
    let L := c*T/P^3
    let U := C*T/P^3/6
    let F := D*T/P^4
    F ≤ L^2/16 ∧ F*(6*n+1)^4 ≤ 1 ∧ (3*U/2)*(6*n+1)^2 ≤ 1 := by
  intro L U F
  have hsum : 6*n+1 ≤ 7*P/R := by
    calc
      6*n+1 ≤ 7*n := by linarith only [hn]
      _ ≤ 7*(P/R) := mul_le_mul_of_nonneg_left hupper (by norm_num)
      _ = _ := by ring
  have hs0 : 0 ≤ 6*n+1 := by linarith
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hU : 0 ≤ 3*U/2 := by dsimp [U]; positivity
  refine ⟨?_,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_right hfirst (show 0 ≤ T/(16*P^6) by positivity)
    convert hh using 1 <;> dsimp only [F,L] <;> field_simp
  · calc
      F*(6*n+1)^4 ≤ F*(7*P/R)^4 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0 hsum 4) hF
      _ = D*7^4*T/R^4 := by dsimp only [F]; field_simp
      _ ≤ 1 := (div_le_one (pow_pos hR 4)).mpr hfour
  · calc
      (3*U/2)*(6*n+1)^2 ≤ (3*U/2)*(7*P/R)^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0 hsum 2) hU
      _ = ((49*C/4)*T)/(P*R^2) := by dsimp only [U]; field_simp; ring
      _ ≤ 1 := (div_le_one (mul_pos hP (pow_pos hR 2))).mpr hthird

private theorem eventually_model_block_smallness
    {σ a b δ : ℝ} (hσ : 0<σ)
    (hfour : 1<4*b) (hthird : 1<a-δ+2*b)
    (hfirst : 2*(a+δ)<1) (hlen : b<a-δ) :
    ∀ᶠ T : ℝ in atTop, ∀ P : ℝ, 0<P →
      T^(a-δ) ≤ P → P ≤ T^(a+δ) →
      let R := T^b
      let N : ℕ := ⌊P/R⌋₊
      let L := modelPhaseJetLower σ 2*T/P^3
      let U := (modelPhaseJetCoefficient σ 2+1)*T/P^3/6
      let F := (modelPhaseJetCoefficient σ 3+1)*T/P^4
      0<N ∧ P/(2*R) ≤ (N:ℝ) ∧ (N:ℝ) ≤ P/R ∧
      F ≤ L^2/16 ∧ F*(6*(N:ℝ)+1)^4 ≤ 1 ∧
        (3*U/2)*(6*(N:ℝ)+1)^2 ≤ 1 := by
  let c := modelPhaseJetLower σ 2
  let C := modelPhaseJetCoefficient σ 2+1
  let D := modelPhaseJetCoefficient σ 3+1
  have hc : 0<c := modelPhaseJetLower_pos hσ 2
  have hC : 0<C := by have h := modelPhaseJetCoefficient_pos hσ 2; dsimp [C]; linarith
  have hD : 0<D := by have h := modelPhaseJetCoefficient_pos hσ 3; dsimp [D]; linarith
  have he1 := eventually_const_mul_rpow_le_rpow (D:=16*D/c^2) hfirst
  have he4 := eventually_const_mul_rpow_le_rpow (D:=D*7^4) hfour
  have he3 := eventually_const_mul_rpow_le_rpow (D:=49*C/4) hthird
  have hel := eventually_const_mul_rpow_le_rpow (D:=(2:ℝ)) hlen
  filter_upwards [he1,he4,he3,hel,eventually_gt_atTop (0:ℝ)] with T h1 h4 h3 hl hT
  intro P hP hlo hhi R N L U F
  have hR : 0<R := Real.rpow_pos_of_pos hT b
  have hrange : 2 ≤ P/R := (le_div_iff₀ hR).mpr (hl.trans hlo)
  have hNat : 1 ≤ N := Nat.le_floor (by norm_num; linarith only [hrange])
  have hNr : 1 ≤ (N:ℝ) := by exact_mod_cast hNat
  have hupper : (N:ℝ) ≤ P/R := Nat.floor_le (div_pos hP hR).le
  have hlower : P/(2*R) ≤ (N:ℝ) := by
    have hh := (Nat.div_two_lt_floor (show 1 ≤ P/R by linarith only [hrange])).le
    convert hh using 1
    ring
  have hP2 : P^2 ≤ T^(2*(a+δ)) := by
    calc
      P^2 ≤ (T^(a+δ))^2 := pow_le_pow_left₀ hP.le hhi 2
      _ = _ := by rw [← Real.rpow_mul_natCast hT.le]; congr 1; ring
  have hphysical1 : 16*D*P^2 ≤ c^2*T := by
    have hscaled := mul_le_mul_of_nonneg_left h1 (sq_nonneg c)
    rw [Real.rpow_one] at hscaled
    have hcancel : c^2*(16*D/c^2)=16*D := by field_simp
    rw [← mul_assoc,hcancel] at hscaled
    exact (mul_le_mul_of_nonneg_left hP2 (by positivity)).trans hscaled
  have hphysical4 : D*7^4*T ≤ R^4 := by
    rw [Real.rpow_one] at h4
    convert h4 using 1
    dsimp only [R]
    rw [← Real.rpow_mul_natCast hT.le]
    congr 1
    ring
  have hphysical3 : (49*C/4)*T ≤ P*R^2 := by
    rw [Real.rpow_one] at h3
    calc
      _ ≤ T^(a-δ+2*b) := h3
      _ = T^(a-δ)*R^2 := by
        dsimp only [R]
        rw [← Real.rpow_mul_natCast hT.le,← Real.rpow_add hT]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hlo (sq_nonneg R)
  exact ⟨by omega,hlower,hupper,
    source_smallness_of_scale hC.le hD.le hT.le hP hR hNr hupper
      hphysical1 hphysical4 hphysical3⟩

private theorem baseline_scale_geometry
    {a δ η T P : ℝ} (ha : (3:ℝ)/7 ≤ a) (hgap : a+δ ≤ 1/2)
    (hδη : δ ≤ η) (hη : 0 ≤ η) (hη' : η ≤ 1/100)
    (hT : 1 ≤ T) (hP : 0<P)
    (hlo : T^(a-δ) ≤ P) (hhi : P ≤ T^(a+δ)) :
    let R := T^((2:ℝ)/7+η)
    1 ≤ P ∧ 1 ≤ R ∧ P^2 ≤ T ∧ P ≤ R^2 ∧ T^2 ≤ R^7 ∧ R^3 ≤ T ∧
      R^33 ≤ T^10 ∧ T ≤ P^3 ∧ T^2 ≤ P^2*R^4 ∧
      R^3/P^2 ≤ T^(5*η) := by
  intro R
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hp : 1 ≤ P := (Real.one_le_rpow hT (by linarith only [ha,hδη,hη'])).trans hlo
  have hr : 1 ≤ R := Real.one_le_rpow hT (by positivity)
  have hP2 : P^2 ≤ T := by
    calc
      _ ≤ (T^(a+δ))^2 := pow_le_pow_left₀ hP.le hhi 2
      _ = T^((a+δ)*2) := (Real.rpow_mul_natCast hTp.le _ 2).symm
      _ ≤ T^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by linarith only [hgap])
      _ = T := Real.rpow_one T
  have hPR : P ≤ R^2 := by
    calc
      _ ≤ T^(a+δ) := hhi
      _ ≤ T^(((2:ℝ)/7+η)*2) :=
        Real.rpow_le_rpow_of_exponent_le hT (by linarith only [hgap,hη])
      _ = R^2 := Real.rpow_mul_natCast hTp.le _ 2
  have hseven : T^2 ≤ R^7 := by
    rw [← Real.rpow_natCast T 2]
    dsimp only [R]
    rw [← Real.rpow_mul_natCast hTp.le]
    exact Real.rpow_le_rpow_of_exponent_le hT (by norm_num; linarith only [hη])
  have hthree : R^3 ≤ T := by
    calc
      _ = T^(((2:ℝ)/7+η)*3) := (Real.rpow_mul_natCast hTp.le _ 3).symm
      _ ≤ T^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by linarith only [hη'])
      _ = _ := Real.rpow_one T
  have hthirtythree : R^33 ≤ T^10 := by
    dsimp only [R]
    rw [← Real.rpow_mul_natCast hTp.le,← Real.rpow_natCast T 10]
    exact Real.rpow_le_rpow_of_exponent_le hT (by norm_num; linarith only [hη'])
  have hphase : T ≤ P^3 := by
    calc
      T = T^(1:ℝ) := (Real.rpow_one T).symm
      _ ≤ T^((a-δ)*3) := Real.rpow_le_rpow_of_exponent_le hT
        (by linarith only [ha,hδη,hη'])
      _ = (T^(a-δ))^3 := Real.rpow_mul_natCast hTp.le _ 3
      _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hTp.le _) hlo 3
  have hgamma : T^2 ≤ P^2*R^4 := by
    calc
      T^2 = T^(2:ℝ) := (Real.rpow_natCast T 2).symm
      _ ≤ T^((a-δ)*2+((2:ℝ)/7+η)*4) := Real.rpow_le_rpow_of_exponent_le hT
        (by linarith only [ha,hδη,hη])
      _ = (T^(a-δ))^2*R^4 := by
        rw [Real.rpow_add hTp]
        exact congrArg₂ (fun x y : ℝ => x*y)
          (Real.rpow_mul_natCast hTp.le (a-δ) 2)
          (Real.rpow_mul_natCast hTp.le ((2:ℝ)/7+η) 4)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Real.rpow_nonneg hTp.le _) hlo 2) (by positivity)
  refine ⟨hp,hr,hP2,hPR,hseven,hthree,hthirtythree,hphase,hgamma,?_⟩
  apply (div_le_iff₀ (pow_pos hP 2)).mpr
  have hPlo : (T^(a-δ))^2 ≤ P^2 :=
    pow_le_pow_left₀ (Real.rpow_nonneg hTp.le _) hlo 2
  calc
    R^3 = T^(((2:ℝ)/7+η)*3) := (Real.rpow_mul_natCast hTp.le _ 3).symm
    _ ≤ T^(5*η+(a-δ)*2) :=
      Real.rpow_le_rpow_of_exponent_le hT (by linarith only [ha,hδη])
    _ = T^(5*η)*(T^(a-δ))^2 := by
      rw [Real.rpow_add hTp]
      exact congrArg (fun x : ℝ => T^(5*η)*x) (Real.rpow_mul_natCast hTp.le (a-δ) 2)
    _ ≤ _ := mul_le_mul_of_nonneg_left hPlo (Real.rpow_nonneg hTp.le _)

private theorem normalized_frozen_main_le
    {K T P R Q : ℝ} (hK : 0 ≤ K) (hT : 0<T) (hP : 0<P)
    (hR : 0<R) (hQ : 0<Q) (hcut : T*Q^2 ≤ K*P^2*R)
    (hscale : T^2 ≤ R^7) :
    (P^2*R/(T*Q^2))^13*(T^6*Q^6/R^18)*(T*Q^2/P^2)^10*
      (T*Q^2/P^2+R^8/T^2) ≤ (K+1)*P^6*T*R^3 := by
  have htri : P^4*T^4*Q^2/R^5 ≤ K*P^6*T^3/R^4 := by
    have hh := mul_le_mul_of_nonneg_left hcut
      (show 0 ≤ P^4*T^3/R^5 by positivity)
    convert hh using 1 <;> field_simp
  have htri' : K*P^6*T^3/R^4 ≤ K*P^6*T*R^3 := by
    have hh := mul_le_mul_of_nonneg_left hscale
      (show 0 ≤ K*P^6*T/R^4 by positivity)
    convert hh using 1 <;> field_simp
  calc
    _ = P^4*T^4*Q^2/R^5+P^6*T*R^3 := by field_simp
    _ ≤ K*P^6*T*R^3+P^6*T*R^3 := add_le_add (htri.trans htri') le_rfl
    _ = _ := by ring

private theorem normalized_minor_main_le
    {K T P R Q : ℝ} (hT : 0<T) (hP : 0<P)
    (hR : 0<R) (hQ : 0<Q) (hcut : P^2*R ≤ K*T*Q^2)
    (hscale : T^2 ≤ R^7) :
    (T^6*Q^6/R^18)*(P^2*R^2/(T*Q^2))^10*
      (P^2*R^2/(T*Q^2)+R^8/T^2+Q^2*R^7/(P^2*T)) ≤
        (K^8+K^7+K^6)*P^6*T*R^3 := by
  have htri : P^22*R^4/(T^5*Q^16) ≤ K^8*P^6*T^3/R^4 := by
    have hpow := pow_le_pow_left₀ (show 0 ≤ P^2*R by positivity) hcut 8
    have hh := mul_le_mul_of_nonneg_left hpow
      (show 0 ≤ P^6/(T^5*Q^16*R^4) by positivity)
    convert hh using 1 <;> field_simp
  have htri' : K^8*P^6*T^3/R^4 ≤ K^8*P^6*T*R^3 := by
    have hh := mul_le_mul_of_nonneg_left hscale
      (show 0 ≤ K^8*P^6*T/R^4 by positivity)
    convert hh using 1 <;> field_simp
  have hnontri₁ : P^20*R^10/(T^6*Q^14) ≤ K^7*P^6*T*R^3 := by
    have hpow := pow_le_pow_left₀ (show 0 ≤ P^2*R by positivity) hcut 7
    have hh := mul_le_mul_of_nonneg_left hpow
      (show 0 ≤ P^6*R^3/(T^6*Q^14) by positivity)
    convert hh using 1 <;> field_simp
  have hnontri₂ : P^18*R^9/(T^5*Q^12) ≤ K^6*P^6*T*R^3 := by
    have hpow := pow_le_pow_left₀ (show 0 ≤ P^2*R by positivity) hcut 6
    have hh := mul_le_mul_of_nonneg_left hpow
      (show 0 ≤ P^6*R^3/(T^5*Q^12) by positivity)
    convert hh using 1 <;> field_simp
  calc
    _ = P^22*R^4/(T^5*Q^16)+P^20*R^10/(T^6*Q^14)+
        P^18*R^9/(T^5*Q^12) := by field_simp
    _ ≤ K^8*P^6*T*R^3+K^7*P^6*T*R^3+K^6*P^6*T*R^3 :=
      add_le_add (add_le_add (htri.trans htri') hnontri₁) hnontri₂
    _ = _ := by ring

private theorem physical_dual_ceiling_bounds
    {c u T P R N Q : ℝ} (hc : 0<c) (hu : 0<u) (hT : 0<T)
    (hP : 0<P) (hR : 0<R) (hQ : 0<Q)
    (hlo : P/(2*R) ≤ N) (hhi : N ≤ P/R)
    (hdual : 12 ≤ (c*T/P^3)*Q*N^2) :
    let M : ℕ := ⌈63*(u*T/P^3)*Q*N^2⌉₊+1
    (63*u/4)*(T*Q/(P*R^2)) ≤ (M:ℝ) ∧
      (M:ℝ) ≤ (63*u+c/6)*(T*Q/(P*R^2)) := by
  intro M
  let V := T*Q/(P*R^2)
  let x := 63*(u*T/P^3)*Q*N^2
  have hN : 0<N := (div_pos hP (by positivity : 0<2*R)).trans_le hlo
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  have hlow : (63*u/4)*V ≤ x := by
    calc
      _ = 63*(u*T/P^3)*Q*(P/(2*R))^2 := by dsimp only [V]; field_simp; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hlo 2) (by positivity)
  have hupp : x ≤ 63*u*V := by
    calc
      x ≤ 63*(u*T/P^3)*Q*(P/R)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hN.le hhi 2) (by positivity)
      _ = _ := by dsimp only [V]; field_simp
  have hV : 12 ≤ c*V := by
    apply hdual.trans
    calc
      (c*T/P^3)*Q*N^2 ≤ (c*T/P^3)*Q*(P/R)^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hN.le hhi 2) (by positivity)
      _ = _ := by dsimp only [V]; field_simp
  have hceilLow : x ≤ (⌈x⌉₊:ℝ) := Nat.le_ceil x
  have hceilHigh : (⌈x⌉₊:ℝ) < x+1 := Nat.ceil_lt_add_one hx
  dsimp only [M]
  rw [Nat.cast_add,Nat.cast_one]
  change (63*u/4)*V ≤ (⌈x⌉₊:ℝ)+1 ∧ (⌈x⌉₊:ℝ)+1 ≤ (63*u+c/6)*V
  constructor
  · linarith only [hlow,hceilLow]
  · nlinarith only [hupp,hV,hceilHigh]

private theorem physical_dual_sqrt_weight_bound
    {K T P R Q U M : ℝ} (hK : 0<K) (hT : 0<T) (hP : 0<P)
    (hR : 0<R) (hQ : 0<Q) (hU : 0 ≤ U) (hM : 0<M)
    (hUupper : U ≤ K*T/P^3) (hMlower : T*Q/(K*P*R^2) ≤ M) :
    Real.sqrt (U*Q^3)*(Real.sqrt M/(6*M^2)) ≤ K^2*R^3/T := by
  let B := Real.sqrt (U*Q^3)*(Real.sqrt M/(6*M^2))
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hBsq : B^2=U*Q^3/(36*M^3) := by
    dsimp only [B]
    rw [mul_pow,div_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt hM.le]
    field_simp
    ring
  have hmodel : U*Q^3*T^2 ≤ K^4*R^6*M^3 := by
    calc
      _ ≤ (K*T/P^3)*Q^3*T^2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hUupper (by positivity)) (by positivity)
      _ = K^4*R^6*(T*Q/(K*P*R^2))^3 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hMlower 3) (by positivity)
  have hcross : U*Q^3*T^2 ≤ (K^4*R^6)*(36*M^3) := by
    apply hmodel.trans
    exact mul_le_mul_of_nonneg_left
      (show M^3 ≤ 36*M^3 by nlinarith only [pow_pos hM 3]) (by positivity)
  have hsq : B^2 ≤ (K^2*R^3/T)^2 := by
    calc
      _ = U*Q^3/(36*M^3) := hBsq
      _ ≤ K^4*R^6/T^2 :=
        (div_le_div_iff₀ (by positivity) (pow_pos hT 2)).mpr hcross
      _ = _ := by ring
  exact (sq_le_sq₀ hB (by positivity)).mp hsq

private theorem physical_dual_error_bounds
    {K T P R Q U M L F lam : ℝ}
    (hK : 0<K) (hT : 0<T) (hP : 0<P) (hR : 0<R) (hQ : 0<Q)
    (hU : 0 ≤ U) (hM : 0<M)
    (hUupper : U ≤ K*T/P^3) (hMlower : T*Q/(K*P*R^2) ≤ M)
    (hLlower : T/(K*P^3) ≤ L) (hlamLower : T/(K*P^4) ≤ lam)
    (hFupper : F ≤ K*T/P^4) (hgeom : T ≤ P*R^3) :
    let zeta := Real.sqrt M/(6*M^2)
    let E := 16*U*Real.sqrt (U*Q^3)*zeta+3*F/4
    let rho := (12*U*Real.sqrt (U*Q^3)/lam)*zeta
    E*Q^2/L ≤ (16*K^4+3*K^2/4)*(Q^2*R^3/T) ∧
      U*rho ≤ 12*K^5*(R^3/P^2) := by
  intro zeta E rho
  let A := Real.sqrt (U*Q^3)*zeta
  let Umax := K*T/P^3
  let Amax := K^2*R^3/T
  let Emax := 16*Umax*Amax+3*(K*T/P^4)/4
  have hL : 0<L := (show 0<T/(K*P^3) by positivity).trans_le hLlower
  have hlam : 0<lam := (show 0<T/(K*P^4) by positivity).trans_le hlamLower
  have hA : 0 ≤ A := by dsimp only [A,zeta]; positivity
  have hAupper : A ≤ Amax :=
    physical_dual_sqrt_weight_bound hK hT hP hR hQ hU hM hUupper hMlower
  have hEmax : 0 ≤ Emax := by dsimp only [Emax,Umax,Amax]; positivity
  have hE : E ≤ Emax := by
    have hre : E=16*(U*A)+3*F/4 := by dsimp only [E,A]; ring
    rw [hre]
    have hprod : U*A ≤ Umax*Amax :=
      mul_le_mul hUupper hAupper hA (by dsimp only [Umax]; positivity)
    dsimp only [Emax]
    nlinarith only [hprod,hFupper]
  constructor
  · have hlast : 3*K^2*Q^2/(4*P) ≤ (3*K^2/4)*(Q^2*R^3/T) := by
      have hh := mul_le_mul_of_nonneg_left hgeom
        (show 0 ≤ 3*K^2*Q^2/(4*P*T) by positivity)
      convert hh using 1 <;> field_simp
    calc
      E*Q^2/L ≤ Emax*Q^2/L :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hE (sq_nonneg Q)) hL.le
      _ ≤ Emax*Q^2/(T/(K*P^3)) :=
        div_le_div_of_nonneg_left (mul_nonneg hEmax (sq_nonneg Q))
          (by positivity) hLlower
      _ = 16*K^4*(Q^2*R^3/T)+3*K^2*Q^2/(4*P) := by
        dsimp only [Emax,Umax,Amax]
        field_simp
      _ ≤ 16*K^4*(Q^2*R^3/T)+(3*K^2/4)*(Q^2*R^3/T) :=
        add_le_add le_rfl hlast
      _ = _ := by ring
  · have hnum : 12*U^2*A ≤ 12*Umax^2*Amax := by
      have hprod := mul_le_mul (pow_le_pow_left₀ hU hUupper 2) hAupper hA (sq_nonneg Umax)
      nlinarith only [hprod]
    calc
      U*rho = (12*U^2*A)/lam := by dsimp only [rho,A]; ring
      _ ≤ (12*Umax^2*Amax)/lam := div_le_div_of_nonneg_right hnum hlam.le
      _ ≤ (12*Umax^2*Amax)/(T/(K*P^4)) :=
        div_le_div_of_nonneg_left (by dsimp only [Amax]; positivity)
          (by positivity) hlamLower
      _ = _ := by dsimp only [Umax,Amax]; field_simp

private theorem exists_model_scale_constant {σ : ℝ} (hσ : 0<σ)
    (B₁ B₂ B₃ : ℝ) :
    let c := modelPhaseJetLower σ 2
    let u := (modelPhaseJetCoefficient σ 2+1)/6
    let ell := modelPhaseJetLower σ 3
    let f := modelPhaseJetCoefficient σ 3+1
    let x := (modelPhaseJetCoefficient σ 1+1)/2
    ∃ K ≥ (1000:ℝ), (1/K ≤ c ∧ c ≤ K) ∧ (1/K ≤ u ∧ u ≤ K) ∧
      (1/K ≤ ell ∧ ell ≤ K) ∧ f ≤ K ∧ x ≤ K ∧ B₁ ≤ K ∧ B₂ ≤ K ∧ B₃ ≤ K := by
  classical
  intro c u ell f x
  obtain ⟨K,hK⟩ := Finset.exists_le
    ({1000,c,1/c,u,1/u,ell,1/ell,f,x,B₁,B₂,B₃}:Finset ℝ)
  have hK1000 : 1000 ≤ K := hK _ (by simp)
  have hKpos : 0<K := by linarith only [hK1000]
  have hc : 0<c := modelPhaseJetLower_pos hσ 2
  have hu : 0<u := by
    have hh := modelPhaseJetCoefficient_pos hσ 2
    dsimp only [u]
    positivity
  have hell : 0<ell := modelPhaseJetLower_pos hσ 3
  refine ⟨K,hK1000,⟨?_,hK _ (by simp)⟩,⟨?_,hK _ (by simp)⟩,
    ⟨?_,hK _ (by simp)⟩,hK _ (by simp),hK _ (by simp),
    hK _ (by simp),hK _ (by simp),hK _ (by simp)⟩
  · exact (one_div_le hKpos hc).mpr (hK _ (by simp))
  · exact (one_div_le hKpos hu).mpr (hK _ (by simp))
  · exact (one_div_le hKpos hell).mpr (hK _ (by simp))

private theorem normalized_physical_dual_ceiling
    {K c u T P R N Q : ℝ} (hK : 1000 ≤ K)
    (hc : 1/K ≤ c ∧ c ≤ K) (hu : 1/K ≤ u ∧ u ≤ K)
    (hT : 0<T) (hP : 0<P) (hR : 0<R) (hQ : 0<Q)
    (hlo : P/(2*R) ≤ N) (hhi : N ≤ P/R)
    (hdual : 12 ≤ (c*T/P^3)*Q*N^2) :
    let M : ℕ := ⌈63*(u*T/P^3)*Q*N^2⌉₊+1
    T*Q/(K*P*R^2) ≤ (M:ℝ) ∧
      (M:ℝ) ≤ K^2*T*Q/(P*R^2) := by
  intro M
  have hKpos : 0<K := by linarith only [hK]
  have hcp : 0<c := (one_div_pos.mpr hKpos).trans_le hc.1
  have hup : 0<u := (one_div_pos.mpr hKpos).trans_le hu.1
  have hb := physical_dual_ceiling_bounds hcp hup hT hP hR hQ hlo hhi hdual
  have hlow : 1/K ≤ 63*u/4 := by linarith only [hu.1,hup]
  have hupper : 63*u+c/6 ≤ K^2 := by
    calc
      _ ≤ 64*K := by linarith only [hu.2,hc.2,hK]
      _ ≤ K*K := mul_le_mul_of_nonneg_right (by linarith only [hK]) hKpos.le
      _ = _ := by ring
  constructor
  · calc
      _ = (1/K)*(T*Q/(P*R^2)) := by field_simp
      _ ≤ (63*u/4)*(T*Q/(P*R^2)) := mul_le_mul_of_nonneg_right hlow (by positivity)
      _ ≤ _ := hb.1
  · calc
      _ ≤ (63*u+c/6)*(T*Q/(P*R^2)) := hb.2
      _ ≤ K^2*(T*Q/(P*R^2)) := mul_le_mul_of_nonneg_right hupper (by positivity)
      _ = _ := by ring

private theorem direct_branch_cube_cutoff
    {K c T P R N Q : ℝ} (hK : 1000 ≤ K) (hc : 1/K ≤ c)
    (hT : 0<T) (hP : 0<P) (hR : 0<R) (hQ : 0<Q)
    (hNlo : P/(2*R) ≤ N) (hRthree : R^3 ≤ T)
    (hfail : ¬(12 ≤ (c*T/P^3)*Q*N^2 ∧ 384 ≤ (c*T/P^3)^2*Q^3*N^3)) :
    T^2*Q^3 ≤ K^6*P^3*R^3 := by
  have hKpos : 0<K := by linarith only [hK]
  have hN : 0<N := (show 0<P/(2*R) by positivity).trans_le hNlo
  have hcp : 0<c := (one_div_pos.mpr hKpos).trans_le hc
  have hcT : (1/K)*T/P^3 ≤ c*T/P^3 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc hT.le) (by positivity)
  rcases not_and_or.mp hfail with hfail | hfail
  · have hlo : T*Q/(4*K*P*R^2) ≤ (c*T/P^3)*Q*N^2 := by
      calc
        _ = ((1/K)*T/P^3)*Q*(P/(2*R))^2 := by field_simp; norm_num
        _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right hcT hQ.le)
          (pow_le_pow_left₀ (by positivity) hNlo 2) (by positivity) (by positivity)
    have hh := (div_lt_iff₀ (show 0<4*K*P*R^2 by positivity)).mp
      (hlo.trans_lt (lt_of_not_ge hfail))
    have hqcut : Q ≤ 48*K*P*R^2/T := by
      apply (le_div_iff₀ hT).mpr
      nlinarith only [hh]
    have hpow := pow_le_pow_left₀ hQ.le hqcut 3
    have hfirst : T^2*Q^3 ≤ (48*K)^3*P^3*R^6/T := by
      have hh' := mul_le_mul_of_nonneg_left hpow (sq_nonneg T)
      convert hh' using 1
      field_simp
    have hcoefficient : (48*K)^3 ≤ K^6 := by
      calc
        _ = (48:ℝ)^3*K^3 := by ring
        _ ≤ K^3*K^3 := mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 48)
            (by linarith only [hK]) 3) (by positivity)
        _ = _ := by ring
    have hlast : K^6*P^3*R^6/T ≤ K^6*P^3*R^3 := by
      have hh' := mul_le_mul_of_nonneg_left hRthree
        (show 0 ≤ K^6*P^3*R^3/T by positivity)
      convert hh' using 1 <;> field_simp
    calc
      _ ≤ (48*K)^3*P^3*R^6/T := hfirst
      _ ≤ K^6*P^3*R^6/T := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoefficient (by positivity)) (by positivity)) hT.le
      _ ≤ _ := hlast
  · have hlo : T^2*Q^3/(8*K^2*P^3*R^3) ≤ (c*T/P^3)^2*Q^3*N^3 := by
      calc
        _ = (((1/K)*T/P^3)^2)*Q^3*(P/(2*R))^3 := by field_simp; norm_num
        _ ≤ _ := mul_le_mul
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hcT 2) (by positivity))
          (pow_le_pow_left₀ (by positivity) hNlo 3) (by positivity) (by positivity)
    have hh := (div_lt_iff₀ (show 0<8*K^2*P^3*R^3 by positivity)).mp
      (hlo.trans_lt (lt_of_not_ge hfail))
    have hKfour : (3072:ℝ) ≤ K^4 := by
      have hh' := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1000) hK 4
      norm_num at hh'
      linarith only [hh']
    have hcoefficient : 3072*K^2 ≤ K^6 := by
      calc
        _ ≤ K^4*K^2 := mul_le_mul_of_nonneg_right hKfour (sq_nonneg K)
        _ = _ := by ring
    calc
      T^2*Q^3 ≤ 3072*K^2*P^3*R^3 := by nlinarith only [hh]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoefficient (by positivity)) (by positivity)

private theorem minor_branch_scales
    {K c T P R N Q : ℝ} (hc : 0<c) (hcK : c ≤ K)
    (hT : 0<T) (hP : 0<P) (hR : 0<R) (hN : 0 ≤ N) (hQ : 0 ≤ Q)
    (hQN : Q ≤ 2*N) (hNupper : N ≤ P/R)
    (hminor : 3 ≤ (c*T/P^3)*Q^2*N/8) :
    12 ≤ (c*T/P^3)*Q*N^2 ∧ P^2*R ≤ K*T*Q^2 := by
  have hK : 0<K := hc.trans_le hcK
  have hmono := mul_le_mul_of_nonneg_left hQN
    (show 0 ≤ (c*T/P^3)*Q*N by positivity)
  have hupper : (c*T/P^3)*Q^2*N ≤ K*T*Q^2/(P^2*R) := by
    calc
      _ ≤ (K*T/P^3)*Q^2*(P/R) := mul_le_mul
        (mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcK hT.le) (by positivity))
          (sq_nonneg Q))
        hNupper hN (by positivity)
      _ = _ := by field_simp
  constructor
  · nlinarith only [hmono,hminor]
  · have hb : 24 ≤ K*T*Q^2/(P^2*R) := by linarith only [hupper,hminor]
    have hh := (le_div_iff₀ (show 0<P^2*R by positivity)).mp hb
    nlinarith only [hh,show 0<P^2*R by positivity]

private theorem frozen_branch_scales
    {K c T P R N Q : ℝ} (hK : 1000 ≤ K) (hc : 1/K ≤ c)
    (hT : 0<T) (hP : 0<P) (hR : 0<R) (hQ : 0<Q)
    (hNlo : P/(2*R) ≤ N) (hgeom : T ≤ P^2*R)
    (hcase : Q=2 ∨ (c*T/P^3)*Q^2*N/8<3) :
    T*Q^2 ≤ 48*K*P^2*R ∧
      1+32/((c*T/P^3)*Q^2*N) ≤ K^2*(P^2*R/(T*Q^2)) := by
  have hKpos : 0<K := by linarith only [hK]
  have hN : 0<N := (show 0<P/(2*R) by positivity).trans_le hNlo
  have hcp : 0<c := (one_div_pos.mpr hKpos).trans_le hc
  have hcT : (1/K)*T/P^3 ≤ c*T/P^3 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc hT.le) (by positivity)
  have hlo : T*Q^2/(2*K*P^2*R) ≤ (c*T/P^3)*Q^2*N := by
    calc
      _ = ((1/K)*T/P^3)*Q^2*(P/(2*R)) := by field_simp
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right hcT (sq_nonneg Q))
        hNlo (by positivity) (by positivity)
  have hcut : T*Q^2 ≤ 48*K*P^2*R := by
    rcases hcase with htwo | hsmall
    · calc
        _ = 4*T := by rw [htwo]; ring
        _ ≤ 4*(P^2*R) := mul_le_mul_of_nonneg_left hgeom (by norm_num)
        _ ≤ (48*K)*(P^2*R) :=
          mul_le_mul_of_nonneg_right (by linarith only [hK]) (by positivity)
        _ = _ := by ring
    · have hh : T*Q^2/(2*K*P^2*R)<24 := by linarith only [hlo,hsmall]
      have hh' := (div_lt_iff₀ (show 0<2*K*P^2*R by positivity)).mp hh
      nlinarith only [hh']
  have hone : 1 ≤ 48*K*(P^2*R/(T*Q^2)) := by
    have hh := div_le_div_of_nonneg_right hcut (show 0 ≤ T*Q^2 by positivity)
    convert hh using 1 <;> field_simp
  have hreciprocal : 32/((c*T/P^3)*Q^2*N) ≤ 64*K*(P^2*R/(T*Q^2)) := by
    calc
      _ ≤ 32/(T*Q^2/(2*K*P^2*R)) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hlo
      _ = _ := by field_simp; norm_num
  refine ⟨hcut,?_⟩
  calc
    _ ≤ 48*K*(P^2*R/(T*Q^2))+64*K*(P^2*R/(T*Q^2)) :=
      add_le_add hone hreciprocal
    _ = (112*K)*(P^2*R/(T*Q^2)) := by ring
    _ ≤ (K*K)*(P^2*R/(T*Q^2)) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith only [hK]) hKpos.le) (by positivity)
    _ = _ := by ring

private theorem physical_coordinate_budget_bounds
    {K T P R Q M X : ℝ} (hK : 1000 ≤ K)
    (hT : 0<T) (hP : 0<P) (hR : 0<R) (hQ : 0<Q)
    (hX : 0 ≤ X) (hXupper : X ≤ K*(T/P^2))
    (hMlower : T*Q/(K*P*R^2) ≤ M)
    (hgeom : T^2 ≤ P^2*R^4) (hPtwo : P^2 ≤ T) :
    let Gamma := Q^2/(6*M^2)
    let G0 := P^2*R^4/T^2
    let X0 := T/P^2
    Gamma ≤ K^2*G0 ∧ 2*Gamma+1 ≤ K^2*G0 ∧
      (2*X+5)^2 ≤ K^4*X0^2 := by
  intro Gamma G0 X0
  have hKpos : 0<K := by linarith only [hK]
  have hG : 1 ≤ G0 := by
    apply (le_div_iff₀ (pow_pos hT 2)).mpr
    simpa using hgeom
  have hX0 : 1 ≤ X0 := by
    apply (le_div_iff₀ (pow_pos hP 2)).mpr
    simpa using hPtwo
  have hGamma : Gamma ≤ K^2*G0/6 := by
    calc
      _ ≤ Q^2/(6*(T*Q/(K*P*R^2))^2) :=
        div_le_div_of_nonneg_left (sq_nonneg Q) (by positivity)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hMlower 2) (by norm_num))
      _ = _ := by dsimp only [G0]; field_simp
  have hKK : 1000*K ≤ K^2 := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hK hKpos.le
  have hcoef : K^2/3+1 ≤ K^2 := by nlinarith only [hKK,hK]
  have hcoefX : 2*K+5 ≤ K^2 := by nlinarith only [hKK,hK]
  refine ⟨?_,?_,?_⟩
  · have hh : 0 ≤ K^2*G0 := by dsimp only [G0]; positivity
    linarith only [hGamma,hh]
  · calc
      2*Gamma+1 ≤ (K^2/3+1)*G0 := by nlinarith only [hGamma,hG]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (by linarith only [hG])
  · have hlinear : 2*X+5 ≤ K^2*X0 := by
      calc
        _ ≤ (2*K+5)*X0 := by nlinarith only [hXupper,hX0]
        _ ≤ _ := mul_le_mul_of_nonneg_right hcoefX (by linarith only [hX0])
    have hh := pow_le_pow_left₀ (show 0 ≤ 2*X+5 by positivity) hlinear 2
    convert hh using 1
    ring

private theorem physical_pair_factor_bounds
    {K T P R Q U M L F lam X : ℝ}
    (hK : 1000 ≤ K) (hT : 0<T) (hP : 0<P) (hR : 0<R) (hQ : 0<Q)
    (hU : 0 ≤ U) (hM : 0<M) (hX : 0 ≤ X)
    (hUupper : U ≤ K*T/P^3) (hMlower : T*Q/(K*P*R^2) ≤ M)
    (hLlower : T/(K*P^3) ≤ L) (hlamLower : T/(K*P^4) ≤ lam)
    (hFupper : F ≤ K*T/P^4) (hXupper : X ≤ K*(T/P^2))
    (hgeom : T ≤ P*R^3) (hPthree : T ≤ P^3)
    (hgamma : T^2 ≤ P^2*R^4) (hPtwo : P^2 ≤ T) :
    let zeta := Real.sqrt M/(6*M^2)
    let E := 16*U*Real.sqrt (U*Q^3)*zeta+3*F/4
    let rho := (12*U*Real.sqrt (U*Q^3)/lam)*zeta
    let Gamma := Q^2/(6*M^2)
    let G0 := P^2*R^4/T^2
    let X0 := T/P^2
    let H := 1+R^3/P^2
    1+6*U*(rho+1) ≤ K^6*H ∧
      Gamma+48*E*Q^2/L ≤ K^6*(G0+Q^2*R^3/T) ∧
      16*(2*Gamma+1)*(2*X+5)^2*(Gamma+48*E*Q^2/L) ≤
        K^13*G0*X0^2*(G0+Q^2*R^3/T) := by
  intro zeta E rho Gamma G0 X0 H
  have hKpos : 0<K := by linarith only [hK]
  have hKone : 1 ≤ K := by linarith only [hK]
  have hE := physical_dual_error_bounds hKpos hT hP hR hQ hU hM
    hUupper hMlower hLlower hlamLower hFupper hgeom
  have hco := physical_coordinate_budget_bounds hK hT hP hR hQ
    hX hXupper hMlower hgamma hPtwo
  have hUmax : U ≤ K := hUupper.trans ((div_le_iff₀ (pow_pos hP 3)).mpr
    (mul_le_mul_of_nonneg_left hPthree hKpos.le))
  have h15 : 1 ≤ K^5 := one_le_pow₀ hKone
  have h25 : K^2 ≤ K^5 := pow_le_pow_right₀ hKone (by norm_num)
  have h45 : K^4 ≤ K^5 := pow_le_pow_right₀ hKone (by norm_num)
  have hK5 : K ≤ K^5 := by simpa using pow_le_pow_right₀ hKone (show 1 ≤ 5 by norm_num)
  have h56 : 1000*K^5 ≤ K^6 := by
    simpa only [pow_succ'] using mul_le_mul_of_nonneg_right hK (by positivity : 0 ≤ K^5)
  have h26 : K^2 ≤ K^6 := pow_le_pow_right₀ hKone (by norm_num)
  have htriCoeff : 1+6*K+72*K^5 ≤ K^6 := by
    linarith only [h15,hK5,h56]
  have herrCoeff : 768*K^4+36*K^2 ≤ K^6 := by
    linarith only [h45,h25,h56,h15]
  have htri : 1+6*U*(rho+1) ≤ K^6*H := by
    have hA : 0 ≤ R^3/P^2 := by positivity
    calc
      _ ≤ 1+6*K+72*K^5*(R^3/P^2) := by nlinarith only [hUmax,hE.2]
      _ ≤ (1+6*K+72*K^5)*H := by
        dsimp only [H]
        nlinarith only [mul_nonneg (show 0 ≤ 1+6*K by positivity) hA,
          show 0 ≤ K^5 by positivity]
      _ ≤ _ := mul_le_mul_of_nonneg_right htriCoeff (by dsimp only [H]; positivity)
  have hpair : Gamma+48*E*Q^2/L ≤ K^6*(G0+Q^2*R^3/T) := by
    have hErr : 48*E*Q^2/L ≤ K^6*(Q^2*R^3/T) := by
      calc
        _ = 48*(E*Q^2/L) := by ring
        _ ≤ 48*((16*K^4+3*K^2/4)*(Q^2*R^3/T)) :=
          mul_le_mul_of_nonneg_left hE.1 (by norm_num)
        _ = (768*K^4+36*K^2)*(Q^2*R^3/T) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right herrCoeff (by positivity)
    have hGamma : Gamma ≤ K^6*G0 := hco.1.trans
      (mul_le_mul_of_nonneg_right h26 (by positivity))
    nlinarith only [hGamma,hErr]
  refine ⟨htri,hpair,?_⟩
  calc
    _ ≤ 16*(2*Gamma+1)*(2*X+5)^2*(K^6*(G0+Q^2*R^3/T)) :=
      mul_le_mul_of_nonneg_left hpair (by dsimp only [Gamma]; positivity)
    _ ≤ 16*(K^2*G0)*(K^4*X0^2)*(K^6*(G0+Q^2*R^3/T)) := by
      apply mul_le_mul_of_nonneg_right _ (by dsimp only [G0]; positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hco.2.1 (by norm_num))
        hco.2.2 (sq_nonneg _) (by dsimp only [G0]; positivity)
    _ = 16*K^12*G0*X0^2*(G0+Q^2*R^3/T) := by ring
    _ ≤ _ := by
      have hh : 16*K^12 ≤ K^13 := by
        simpa only [pow_succ'] using mul_le_mul_of_nonneg_right
          (show 16 ≤ K by linarith only [hK]) (by positivity : 0 ≤ K^12)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh
          (by dsimp only [G0]; positivity)) (sq_nonneg X0))
        (by dsimp only [G0]; positivity)

private theorem physical_block_count_bounds
    {K T P R N Q X L : ℝ} (hK : 1000 ≤ K)
    (hT : 1 ≤ T) (hP : 0<P) (hR : 0<R) (hQ : 1 ≤ Q)
    (hXupper : X ≤ K*(T/P^2))
    (hLlower : T/(K*P^3) ≤ L) (hNlower : P/(2*R) ≤ N)
    (hPtwo : P^2 ≤ T) (hQR : Q ≤ 2*R) (hRT : R ≤ T) :
    let D := 16/(L*N*Q)
    let Y := 4*(X+1)*D^2+D*(2+Real.log (D+1))
    let Z := 4*Q*(2*X*Q+1)
    Y ≤ K^6*(P^2*R^2/(T*Q^2))*(1+Real.log T) ∧
      Z ≤ K^2*(T*Q^2/P^2) := by
  intro D Y Z
  let D0 := P^2*R/(T*Q)
  let Y0 := P^2*R^2/(T*Q^2)
  let X0 := T/P^2
  let Log := 1+Real.log T
  have hKp : 0<K := by linarith only [hK]
  have hK1 : 1 ≤ K := by linarith only [hK]
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hQp : 0<Q := zero_lt_one.trans_le hQ
  have hL : 0<L := (show 0<T/(K*P^3) by positivity).trans_le hLlower
  have hN : 0<N := (show 0<P/(2*R) by positivity).trans_le hNlower
  have hD : 0<D := by dsimp only [D]; positivity
  have hLog : 1 ≤ Log := by dsimp only [Log]; linarith only [Real.log_nonneg hT]
  have hX0 : 1 ≤ X0 := (one_le_div (pow_pos hP 2)).mpr hPtwo
  have hDupper : D ≤ 32*K*D0 := by
    calc
      _ ≤ 16/((T/(K*P^3))*(P/(2*R))*Q) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (mul_le_mul_of_nonneg_right
            (mul_le_mul hLlower hNlower (by positivity) hL.le) hQp.le)
      _ = _ := by dsimp only [D0]; field_simp; norm_num
  have hD0Y : D0 ≤ 2*Y0 := by
    have hh := mul_le_mul_of_nonneg_left hQR
      (show 0 ≤ P^2*R/(T*Q^2) by positivity)
    convert hh using 1 <;> dsimp only [D0,Y0] <;> field_simp
  have hD0R : D0 ≤ R := by
    apply (div_le_iff₀ (show 0<T*Q by positivity)).mpr
    have hTQ := le_mul_of_one_le_right hTp.le hQ
    have hh := mul_le_mul_of_nonneg_right (hPtwo.trans hTQ) hR.le
    convert hh using 1
    ring
  have hlogD : 2+Real.log (D+1) ≤ K^2*Log := by
    have hd : D+1 ≤ (32*K+1)*T := by
      have hh := mul_le_mul_of_nonneg_left (hD0R.trans hRT) (by positivity : 0 ≤ 32*K)
      nlinarith only [hDupper,hh,hT]
    have hh := Real.log_le_log (by positivity : 0<D+1) hd
    rw [Real.log_mul (by positivity) hTp.ne'] at hh
    have hl := Real.log_le_sub_one_of_pos (show 0<32*K+1 by positivity)
    have hKK : 1000*K ≤ K^2 := by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right hK hKp.le
    have hc : 32*K+2 ≤ K^2 := by linarith only [hKK,hK]
    calc
      _ ≤ 32*K+2+Real.log T := by linarith only [hh,hl]
      _ ≤ (32*K+2)*Log := by
        dsimp only [Log]
        nlinarith only [mul_nonneg (show 0 ≤ 32*K+1 by positivity) (Real.log_nonneg hT)]
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by linarith only [hLog])
  have hXplus : X+1 ≤ 2*K*X0 := by
    have hh : X0 ≤ K*X0 := le_mul_of_one_le_left (by linarith only [hX0]) hK1
    linarith only [hXupper,hX0,hh]
  have hmain : 4*(X+1)*D^2 ≤ 8192*K^3*Y0 := by
    calc
      _ ≤ 4*(2*K*X0)*(32*K*D0)^2 := mul_le_mul
        (mul_le_mul_of_nonneg_left hXplus (by norm_num))
        (pow_le_pow_left₀ hD.le hDupper 2) (sq_nonneg D)
        (by dsimp only [X0]; positivity)
      _ = _ := by dsimp only [X0,D0,Y0]; field_simp; ring
  have herror : D*(2+Real.log (D+1)) ≤ 64*K^3*Y0*Log := by
    have hd : D ≤ 64*K*Y0 := by
      have hh := mul_le_mul_of_nonneg_left hD0Y (by positivity : 0 ≤ 32*K)
      linarith only [hDupper,hh]
    calc
      _ ≤ D*(K^2*Log) := mul_le_mul_of_nonneg_left hlogD hD.le
      _ ≤ (64*K*Y0)*(K^2*Log) := mul_le_mul_of_nonneg_right hd (by positivity)
      _ = _ := by ring
  have hcoeff : 8256*K^3 ≤ K^6 := by
    have hh : (8256:ℝ) ≤ K^3 := by
      have hk := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1000) hK 3
      norm_num at hk
      linarith only [hk]
    calc
      _ ≤ K^3*K^3 := mul_le_mul_of_nonneg_right hh (by positivity)
      _ = _ := by ring
  constructor
  · calc
      Y ≤ 8192*K^3*Y0+64*K^3*Y0*Log := add_le_add hmain herror
      _ ≤ 8192*K^3*Y0*Log+64*K^3*Y0*Log := add_le_add
        (le_mul_of_one_le_right (by dsimp only [Y0]; positivity) hLog) le_rfl
      _ = (8256*K^3)*Y0*Log := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoeff (by dsimp only [Y0]; positivity))
        (by linarith only [hLog])
  · have hunit : 1 ≤ X0*Q := hX0.trans
      (le_mul_of_one_le_right (by linarith only [hX0]) hQ)
    have hcoef : 4*(2*K+1) ≤ K^2 := by
      have hh : 1000*K ≤ K^2 := by
        simpa only [pow_two] using mul_le_mul_of_nonneg_right hK hKp.le
      linarith only [hh,hK]
    calc
      Z ≤ 4*Q*((2*K+1)*X0*Q) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hh := mul_le_mul_of_nonneg_right hXupper hQp.le
        nlinarith only [hh,hunit]
      _ = (4*(2*K+1))*(T*Q^2/P^2) := by dsimp only [X0]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (by positivity)

private theorem normalized_pair_count_bounds
    {K T P R Q B W Y Z H Log : ℝ}
    (hK : 1000 ≤ K) (hT : 0<T) (hP : 0<P) (hR : 0<R) (hQ : 0<Q)
    (hH : 1 ≤ H) (hLog : 1 ≤ Log) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hB : B ≤ K^6*H)
    (hW : W ≤ K^13*(P^2*R^4/T^2)*(T/P^2)^2*
      (P^2*R^4/T^2+Q^2*R^3/T))
    (hYupper : Y ≤ K^6*(P^2*R^2/(T*Q^2))*Log)
    (hZupper : Z ≤ K^2*(T*Q^2/P^2)) :
    4*Y*B+W ≤ K^13*H*Log*
      (P^2*R^2/(T*Q^2)+R^8/T^2+Q^2*R^7/(P^2*T)) ∧
    (T*Q^2 ≤ 48*K*P^2*R →
      4*Z*B+W ≤ K^15*H*(T*Q^2/P^2+R^8/T^2)) := by
  have hKp : 0<K := by linarith only [hK]
  have hHp : 0 ≤ H := by linarith only [hH]
  have hLp : 0 ≤ Log := by linarith only [hLog]
  have hW' : W ≤ K^13*(R^8/T^2+Q^2*R^7/(P^2*T)) := by
    convert hW using 1
    field_simp
  have hcoef (n : ℕ) : 4*K^n ≤ K^(n+1) := by
    simpa only [pow_succ'] using mul_le_mul_of_nonneg_right
      (show (4:ℝ) ≤ K by linarith only [hK]) (pow_nonneg hKp.le n)
  constructor
  · have htri : 4*Y*B ≤ K^13*H*Log*(P^2*R^2/(T*Q^2)) := by
      calc
        _ ≤ 4*Y*(K^6*H) := mul_le_mul_of_nonneg_left hB (by positivity)
        _ ≤ 4*(K^6*(P^2*R^2/(T*Q^2))*Log)*(K^6*H) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hYupper (by norm_num)) (by positivity)
        _ = (4*K^12)*(H*Log*(P^2*R^2/(T*Q^2))) := by ring
        _ ≤ _ := by
          have hh := mul_le_mul_of_nonneg_right (hcoef 12)
            (show 0 ≤ H*Log*(P^2*R^2/(T*Q^2)) by positivity)
          convert hh using 1
          ring
    have hnontri : W ≤ K^13*H*Log*(R^8/T^2+Q^2*R^7/(P^2*T)) := by
      apply hW'.trans
      have hh := le_mul_of_one_le_right
        (show 0 ≤ K^13*(R^8/T^2+Q^2*R^7/(P^2*T)) by positivity)
        (hH.trans (le_mul_of_one_le_right hHp hLog))
      convert hh using 1
      ring
    nlinarith only [htri,hnontri]
  · intro hcut
    have hnontri : W ≤ K^15*(R^8/T^2) := by
      have hlast : Q^2*R^7/(P^2*T) ≤ (48*K)*(R^8/T^2) := by
        have hh := mul_le_mul_of_nonneg_left hcut
          (show 0 ≤ R^7/(P^2*T^2) by positivity)
        convert hh using 1 <;> field_simp
      have hc : 1+48*K ≤ K^2 := by
        have hh : 1000*K ≤ K^2 := by
          simpa only [pow_two] using mul_le_mul_of_nonneg_right hK hKp.le
        linarith only [hh,hK]
      calc
        W ≤ K^13*(R^8/T^2+Q^2*R^7/(P^2*T)) := hW'
        _ ≤ K^13*((1+48*K)*(R^8/T^2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith only [hlast]
        _ ≤ K^13*(K^2*(R^8/T^2)) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)
        _ = _ := by ring
    have htri : 4*Z*B ≤ K^15*H*(T*Q^2/P^2) := by
      have hpow : K^9 ≤ K^15 := pow_le_pow_right₀
        (show 1 ≤ K by linarith only [hK]) (by norm_num)
      calc
        _ ≤ 4*Z*(K^6*H) := mul_le_mul_of_nonneg_left hB (by positivity)
        _ ≤ 4*(K^2*(T*Q^2/P^2))*(K^6*H) := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hZupper (by norm_num)) (by positivity)
        _ = (4*K^8)*(H*(T*Q^2/P^2)) := by ring
        _ ≤ K^15*(H*(T*Q^2/P^2)) := mul_le_mul_of_nonneg_right
          ((hcoef 8).trans hpow) (by positivity)
        _ = _ := by ring
    have hlast : K^15*(R^8/T^2) ≤ K^15*H*(R^8/T^2) := by
      have hh := le_mul_of_one_le_right (show 0 ≤ K^15*(R^8/T^2) by positivity) hH
      convert hh using 1
      ring
    nlinarith only [htri,hnontri.trans hlast]

private theorem physical_moment_prefactors
    {K T P R N Q L U M : ℝ} (hK : 1000 ≤ K)
    (hT : 1 ≤ T) (hP : 0<P) (hR : 1 ≤ R) (hQ : 0<Q)
    (hNlo : P/(2*R) ≤ N) (hNhi : N ≤ P/R) (hQN : Q ≤ 2*N)
    (hLlo : T/(K*P^3) ≤ L) (hU : 0 ≤ U) (hUhi : U ≤ K*T/P^3)
    (hM : 0<M) (hMhi : M ≤ K^2*T*Q/(P*R^2)) :
    let d := L*Q*N/12
    let V := 756*U/L
    M ≤ K^3*T ∧
      1+Real.log M ≤ K^3*(1+Real.log T) ∧
      6*(3+8*Real.pi*V)*(1+Real.log M) ≤ K^7*(1+Real.log T) ∧
      (2/d)^6*M^12 ≤ K^36*(T^6*Q^6/R^18) := by
  intro d V
  have hKp : 0<K := by linarith only [hK]
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hRp : 0<R := zero_lt_one.trans_le hR
  have hNp : 0<N := (show 0<P/(2*R) by positivity).trans_le hNlo
  have hLp : 0<L := (show 0<T/(K*P^3) by positivity).trans_le hLlo
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hMmax : M ≤ K^3*T := by
    have hq : Q ≤ 2*(P/R) := hQN.trans (mul_le_mul_of_nonneg_left hNhi (by norm_num))
    have hr3 : 1 ≤ R^3 := one_le_pow₀ hR
    calc
      M ≤ K^2*T*Q/(P*R^2) := hMhi
      _ ≤ K^2*T*(2*(P/R))/(P*R^2) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hq (by positivity)) (by positivity)
      _ = 2*K^2*T/R^3 := by field_simp
      _ ≤ 2*K^2*T := div_le_self (by positivity) hr3
      _ ≤ K*K^2*T := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith only [hK] : (2:ℝ) ≤ K)
          (sq_nonneg K)) hTp.le
      _ = _ := by ring
  have hlog : 1+Real.log M ≤ K^3*(1+Real.log T) := by
    have hh := Real.log_le_log hM hMmax
    rw [Real.log_mul (pow_ne_zero 3 hKp.ne') hTp.ne'] at hh
    have hl := Real.log_le_sub_one_of_pos (pow_pos hKp 3)
    have hk3 : 1 ≤ K^3 := one_le_pow₀ (show 1 ≤ K by linarith only [hK])
    nlinarith only [hh,hl,mul_nonneg (sub_nonneg.mpr hk3) hlogT]
  have hV : V ≤ K^3 := by
    calc
      V ≤ 756*(K*T/P^3)/L := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hUhi (by norm_num)) hLp.le
      _ ≤ 756*(K*T/P^3)/(T/(K*P^3)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hLlo
      _ = 756*K^2 := by field_simp
      _ ≤ K*K^2 := mul_le_mul_of_nonneg_right (by linarith only [hK]) (sq_nonneg K)
      _ = _ := by ring
  have hV0 : 0 ≤ V := by dsimp only [V]; positivity
  have hVfactor : 6*(3+8*Real.pi*V) ≤ K^4 := by
    have hpi := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hV0
    have hscale : 1000*K^3 ≤ K^4 := by
      simpa only [pow_succ'] using mul_le_mul_of_nonneg_right hK
        (by positivity : 0 ≤ K^3)
    have hk3 : 1 ≤ K^3 := one_le_pow₀ (show 1 ≤ K by linarith only [hK])
    nlinarith only [hpi,hV,hscale,hk3]
  have hdlo : T*Q/(24*K*P^2*R) ≤ d := by
    calc
      _ = (T/(K*P^3))*Q*(P/(2*R))/12 := by field_simp; norm_num
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_right hLlo hQ.le) hNlo
          (by positivity) (by positivity)) (by norm_num)
  have htwo : 2/d ≤ K^2*P^2*R/(T*Q) := by
    calc
      _ ≤ 2/(T*Q/(24*K*P^2*R)) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hdlo
      _ = (48*K)*(P^2*R/(T*Q)) := by field_simp; norm_num
      _ ≤ (K*K)*(P^2*R/(T*Q)) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith only [hK]) hKp.le) (by positivity)
      _ = _ := by ring
  refine ⟨hMmax,hlog,?_,?_⟩
  · calc
      _ ≤ 6*(3+8*Real.pi*V)*(K^3*(1+Real.log T)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ K^4*(K^3*(1+Real.log T)) :=
        mul_le_mul_of_nonneg_right hVfactor (by positivity)
      _ = _ := by ring
  · have hdp : 0<d := (show 0<T*Q/(24*K*P^2*R) by positivity).trans_le hdlo
    calc
      _ ≤ (K^2*P^2*R/(T*Q))^6*(K^2*T*Q/(P*R^2))^12 := mul_le_mul
        (pow_le_pow_left₀ (by positivity) htwo 6)
        (pow_le_pow_left₀ hM.le hMhi 12) (by positivity) (by positivity)
      _ = _ := by field_simp

private theorem moment_rpow_prefactor
    {K T R Q d M ε : ℝ}
    (hK : 0<K) (hT : 0<T) (hR : 0<R) (hQ : 0<Q)
    (hM : 0<M) (hε : 0 ≤ ε) (hMmax : M ≤ K^3*T)
    (hbase : (2/d)^6*M^12 ≤ K^36*(T^6*Q^6/R^18)) :
    (2/d)^6*M^((12:ℝ)+ε) ≤
      K^36*((K^3*T)^ε)*(T^6*Q^6/R^18) := by
  have hsmall : M^ε ≤ (K^3*T)^ε := Real.rpow_le_rpow hM.le hMmax hε
  calc
    _ = ((2/d)^6*M^12)*M^ε := by
      rw [Real.rpow_add hM]
      norm_num only [Real.rpow_ofNat]
      ring
    _ ≤ (K^36*(T^6*Q^6/R^18))*((K^3*T)^ε) :=
      mul_le_mul hbase hsmall (Real.rpow_nonneg hM.le _) (by positivity)
    _ = _ := by ring

private theorem normalized_minor_moment_main
    {K T P R Q C A LogM Y Pair H Log Eps : ℝ}
    (hK : 1000 ≤ K) (hT : 0<T) (hP : 0<P) (hR : 0<R) (hQ : 0<Q)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hY : 0 ≤ Y) (hLogM : 0 ≤ LogM)
    (hH : 0 ≤ H) (hLog : 0 ≤ Log) (hEps : 0 ≤ Eps)
    (hCupper : C ≤ K) (hAupper : A ≤ K^36*Eps*(T^6*Q^6/R^18))
    (hLogUpper : LogM ≤ K^3*Log)
    (hYupper : Y ≤ K^6*(P^2*R^2/(T*Q^2))*Log)
    (hPair : Pair ≤ K^13*H*Log*
      (P^2*R^2/(T*Q^2)+R^8/T^2+Q^2*R^7/(P^2*T)))
    (hcut : P^2*R ≤ K*T*Q^2) (hscale : T^2 ≤ R^7) :
    C*(A*LogM^12*(2*Y)^10*Pair) ≤ K^165*Eps*H*Log^23*(P^6*T*R^3) := by
  have hKp : 0<K := by linarith only [hK]
  have hY2 : 2*Y ≤ K^7*(P^2*R^2/(T*Q^2))*Log := by
    have hc : 2*K^6 ≤ K^7 := by
      simpa only [pow_succ'] using mul_le_mul_of_nonneg_right
        (show (2:ℝ) ≤ K by linarith only [hK]) (by positivity : 0 ≤ K^6)
    calc
      _ ≤ 2*(K^6*(P^2*R^2/(T*Q^2))*Log) :=
        mul_le_mul_of_nonneg_left hYupper (by norm_num)
      _ = (2*K^6)*(P^2*R^2/(T*Q^2))*Log := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (by positivity)) hLog
  have hcore := normalized_minor_main_le hT hP hR hQ hcut hscale
  have hcoeff : K^8+K^7+K^6 ≤ K^9 := by
    have h1 : 1 ≤ K := by linarith only [hK]
    have h78 : K^7 ≤ K^8 := pow_le_pow_right₀ h1 (by norm_num)
    have h68 : K^6 ≤ K^8 := pow_le_pow_right₀ h1 (by norm_num)
    have hh : 1000*K^8 ≤ K^9 := by
      simpa only [pow_succ'] using mul_le_mul_of_nonneg_right hK
        (by positivity : 0 ≤ K^8)
    nlinarith only [h78,h68,hh,show 0 ≤ K^8 by positivity]
  calc
    _ ≤ C*(A*LogM^12*(2*Y)^10*
        (K^13*H*Log*(P^2*R^2/(T*Q^2)+R^8/T^2+Q^2*R^7/(P^2*T)))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hPair (by positivity)) hC
    _ ≤ K*((K^36*Eps*(T^6*Q^6/R^18))*(K^3*Log)^12*
        (K^7*(P^2*R^2/(T*Q^2))*Log)^10*
        (K^13*H*Log*(P^2*R^2/(T*Q^2)+R^8/T^2+Q^2*R^7/(P^2*T)))) := by
      gcongr
    _ = (K^156*Eps*H*Log^23)*
        ((T^6*Q^6/R^18)*(P^2*R^2/(T*Q^2))^10*
          (P^2*R^2/(T*Q^2)+R^8/T^2+Q^2*R^7/(P^2*T))) := by ring
    _ ≤ (K^156*Eps*H*Log^23)*((K^8+K^7+K^6)*P^6*T*R^3) :=
      mul_le_mul_of_nonneg_left hcore (by positivity)
    _ ≤ (K^156*Eps*H*Log^23)*(K^9*P^6*T*R^3) := by gcongr
    _ = _ := by ring

private theorem normalized_frozen_moment_main
    {K T P R Q C A LogV W Z Pair H Log Eps : ℝ}
    (hK : 1000 ≤ K) (hT : 0<T) (hP : 0<P) (hR : 0<R) (hQ : 0<Q)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hZ : 0 ≤ Z) (hLogV : 0 ≤ LogV)
    (hW : 0 ≤ W) (hH : 0 ≤ H) (hEps : 0 ≤ Eps)
    (hCupper : C ≤ K) (hAupper : A ≤ K^36*Eps*(T^6*Q^6/R^18))
    (hLogUpper : LogV ≤ K^7*Log) (hWupper : W ≤ K^2*(P^2*R/(T*Q^2)))
    (hZupper : Z ≤ K^2*(T*Q^2/P^2))
    (hPair : Pair ≤ K^15*H*(T*Q^2/P^2+R^8/T^2))
    (hcut : T*Q^2 ≤ 48*K*P^2*R) (hscale : T^2 ≤ R^7) :
    C*((5*W)^11*W^2*LogV^12*A*(2*Z)^10*Pair) ≤
      K^205*Eps*H*Log^12*(P^6*T*R^3) := by
  have hKp : 0<K := by linarith only [hK]
  have hcoeff (a : ℝ) (ha : a ≤ K) (n : ℕ) : a*K^n ≤ K^(n+1) := by
    simpa only [pow_succ'] using mul_le_mul_of_nonneg_right ha (pow_nonneg hKp.le n)
  have hZ2 : 2*Z ≤ K^3*(T*Q^2/P^2) := by
    calc
      _ ≤ 2*(K^2*(T*Q^2/P^2)) := mul_le_mul_of_nonneg_left hZupper (by norm_num)
      _ = (2*K^2)*(T*Q^2/P^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (hcoeff 2 (by linarith only [hK]) 2) (by positivity)
  have hW5 : 5*W ≤ K^3*(P^2*R/(T*Q^2)) := by
    calc
      _ ≤ 5*(K^2*(P^2*R/(T*Q^2))) := mul_le_mul_of_nonneg_left hWupper (by norm_num)
      _ = (5*K^2)*(P^2*R/(T*Q^2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (hcoeff 5 (by linarith only [hK]) 2) (by positivity)
  have hcore := normalized_frozen_main_le (show 0 ≤ 48*K by positivity)
    hT hP hR hQ hcut hscale
  have hlast : 48*K+1 ≤ K^2 := by
    have hh := hcoeff 1000 hK 1
    norm_num only [pow_one] at hh
    linarith only [hh,hK]
  calc
    _ ≤ C*((5*W)^11*W^2*LogV^12*A*(2*Z)^10*
        (K^15*H*(T*Q^2/P^2+R^8/T^2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPair (by positivity)) hC
    _ ≤ K*((K^3*(P^2*R/(T*Q^2)))^11*(K^2*(P^2*R/(T*Q^2)))^2*
        (K^7*Log)^12*(K^36*Eps*(T^6*Q^6/R^18))*(K^3*(T*Q^2/P^2))^10*
        (K^15*H*(T*Q^2/P^2+R^8/T^2))) := by
      gcongr
    _ = (K^203*Eps*H*Log^12)*
        ((P^2*R/(T*Q^2))^13*(T^6*Q^6/R^18)*(T*Q^2/P^2)^10*
          (T*Q^2/P^2+R^8/T^2)) := by ring
    _ ≤ (K^203*Eps*H*Log^12)*((48*K+1)*P^6*T*R^3) :=
      mul_le_mul_of_nonneg_left hcore (by positivity)
    _ ≤ (K^203*Eps*H*Log^12)*(K^2*P^6*T*R^3) := by gcongr
    _ = _ := by ring

private theorem physical_common_error_powers
    {K T P R N L B : ℝ} (hK : 1000 ≤ K)
    (hT : 1 ≤ T) (hP : 1 ≤ P) (hR : 1 ≤ R) (hN : 1 ≤ N)
    (hNlo : P/(2*R) ≤ N) (hNhi : N ≤ P/R)
    (hLlo : T/(K*P^3) ≤ L) (hB : 0 ≤ B)
    (hBupper : B ≤ K^7*R*(1+Real.log T))
    (hPtwo : P^2 ≤ T) (hRthree : R^3 ≤ T) (hR33 : R^33 ≤ T^10) :
    (B*(Real.sqrt (3*N)*Real.log (6*N)+6/(L*N^2)))^12 ≤
      K^111*(1+Real.log T)^24*(P^6*T*R^3) := by
  let Log := 1+Real.log T
  have hKp : 0<K := by linarith only [hK]
  have hK1 : 1 ≤ K := by linarith only [hK]
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hPp : 0<P := zero_lt_one.trans_le hP
  have hRp : 0<R := zero_lt_one.trans_le hR
  have hNp : 0<N := zero_lt_one.trans_le hN
  have hLp : 0<L := (show 0<T/(K*P^3) by positivity).trans_le hLlo
  have hLog : 1 ≤ Log := by dsimp only [Log]; linarith only [Real.log_nonneg hT]
  have hNT : N ≤ T := by
    have hP2 : P ≤ P^2 := by nlinarith only [hP]
    exact hNhi.trans ((div_le_self hPp.le hR).trans (hP2.trans hPtwo))
  have hlogN : 0 ≤ Real.log (6*N) := Real.log_nonneg (by linarith only [hN])
  have hlogUpper : Real.log (6*N) ≤ K*Log := by
    have hh := Real.log_le_log (by positivity : 0<6*N)
      (mul_le_mul_of_nonneg_left hNT (by norm_num))
    rw [Real.log_mul (by norm_num : (6:ℝ) ≠ 0) hTp.ne'] at hh
    have hl := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<6)
    have hlogT := Real.log_nonneg hT
    dsimp only [Log]
    nlinarith only [hh,hl,hK,mul_nonneg (show 0 ≤ K-1 by linarith only [hK]) hlogT]
  have hsqrtSq : (B*Real.sqrt (3*N)*Real.log (6*N))^2 ≤
      K^17*P*R*Log^4 := by
    calc
      _ = B^2*(3*N)*(Real.log (6*N))^2 := by
        rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity)]
      _ ≤ (K^7*R*Log)^2*(3*(P/R))*(K*Log)^2 := by gcongr
      _ = (3*K^16)*(P*R*Log^4) := by field_simp
      _ ≤ K^17*(P*R*Log^4) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simpa only [pow_succ'] using mul_le_mul_of_nonneg_right
          (show (3:ℝ) ≤ K by linarith only [hK]) (by positivity : 0 ≤ K^16)
      _ = _ := by ring
  have hsqrtPow : (B*Real.sqrt (3*N)*Real.log (6*N))^12 ≤
      K^102*Log^24*(P^6*T*R^3) := by
    have hh := pow_le_pow_left₀ (sq_nonneg _) hsqrtSq 6
    calc
      _ ≤ (K^17*P*R*Log^4)^6 := by simpa only [← pow_mul] using hh
      _ = K^102*Log^24*(P^6*R^3*R^3) := by ring
      _ ≤ _ := by gcongr
  have hreciprocal : 6/(L*N^2) ≤ 24*K*P*R^2/T := by
    calc
      _ ≤ 6/((T/(K*P^3))*(P/(2*R))^2) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (mul_le_mul hLlo (pow_le_pow_left₀ (by positivity) hNlo 2)
            (by positivity) hLp.le)
      _ = _ := by field_simp; norm_num
  have hrecB : B*(6/(L*N^2)) ≤ K^9*(P*R^3/T)*Log := by
    calc
      _ ≤ (K^7*R*Log)*(24*K*P*R^2/T) :=
        mul_le_mul hBupper hreciprocal (by positivity) (by positivity)
      _ = (24*K^8)*(P*R^3/T)*Log := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by linarith only [hLog])
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simpa only [pow_succ'] using mul_le_mul_of_nonneg_right
          (show (24:ℝ) ≤ K by linarith only [hK]) (by positivity : 0 ≤ K^8)
  have hrecScale : (P*R^3/T)^12 ≤ P^6*T*R^3 := by
    have hp6 : P^6 ≤ T^3 := by
      simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg P) hPtwo 3
    have hh := mul_le_mul hp6 hR33 (by positivity) (by positivity)
    have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ P^6*R^3/T^12 by positivity)
    convert hh' using 1 <;> field_simp
  have hrecPow : (B*(6/(L*N^2)))^12 ≤ K^108*Log^24*(P^6*T*R^3) := by
    have hlpow : Log^12 ≤ Log^24 := pow_le_pow_right₀ hLog (by norm_num)
    calc
      _ ≤ (K^9*(P*R^3/T)*Log)^12 := pow_le_pow_left₀ (by positivity) hrecB 12
      _ = K^108*Log^12*((P*R^3/T)^12) := by ring
      _ ≤ _ := by gcongr
  have hcoeff : (2:ℝ)^11*(K^102+K^108) ≤ K^111 := by
    have hpow : K^102 ≤ K^108 := pow_le_pow_right₀ hK1 (by norm_num)
    have hcube : (4096:ℝ) ≤ K^3 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1000) hK 3
      norm_num at hh
      linarith only [hh]
    calc
      _ ≤ 4096*K^108 := by nlinarith only [hpow]
      _ ≤ K^3*K^108 := mul_le_mul_of_nonneg_right hcube (by positivity)
      _ = _ := by ring
  calc
    _ = (B*Real.sqrt (3*N)*Real.log (6*N)+B*(6/(L*N^2)))^12 := by ring
    _ ≤ 2^11*((B*Real.sqrt (3*N)*Real.log (6*N))^12+(B*(6/(L*N^2)))^12) :=
      add_pow_le (by positivity) (by positivity) 12
    _ ≤ 2^11*(K^102*Log^24*(P^6*T*R^3)+K^108*Log^24*(P^6*T*R^3)) :=
      mul_le_mul_of_nonneg_left (add_le_add hsqrtPow hrecPow) (by norm_num)
    _ = (2^11*(K^102+K^108))*(Log^24*(P^6*T*R^3)) := by ring
    _ ≤ K^111*(Log^24*(P^6*T*R^3)) :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = _ := by ring

private theorem direct_cut_implies_quadratic_cut
    {K T P R Q : ℝ} (hK : 0<K) (hT : 0<T) (hP : 0<P)
    (hR : 0<R) (hQ : 0<Q) (hRthree : R^3 ≤ T)
    (hcut : T^2*Q^3 ≤ K^6*P^3*R^3) :
    T*Q^2 ≤ K^4*P^2*R := by
  have hsquare := pow_le_pow_left₀ (show 0 ≤ T^2*Q^3 by positivity) hcut 2
  have hh := mul_le_mul_of_nonneg_left hsquare (show 0 ≤ 1/T by positivity)
  have hpow : (T*Q^2)^3 ≤ (K^4*P^2*R)^3 := by
    calc
      _ ≤ K^12*P^6*R^6/T := by convert hh using 1 <;> field_simp
      _ = (K^12*P^6*R^3)*(R^3/T) := by ring
      _ ≤ (K^12*P^6*R^3)*1 := mul_le_mul_of_nonneg_left
        ((div_le_one hT).mpr hRthree) (by positivity)
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : 3 ≠ 0)).mp hpow

private theorem physical_endpoint_error_power
    {K T P R N Q L Z : ℝ} (hK : 1000 ≤ K)
    (hT : 0<T) (hP : 0<P) (hR : 0<R) (hQ : 0<Q)
    (hNlo : P/(2*R) ≤ N) (hLlo : T/(K*P^3) ≤ L)
    (hZ : 0 ≤ Z) (hZupper : Z ≤ K^2*(T*Q^2/P^2))
    (hcut : T*Q^2 ≤ K^4*P^2*R) (hRthree : R^3 ≤ T) :
    (Z*Real.sqrt (12/(L*N*Q)))^12 ≤ K^72*(P^6*T*R^3) := by
  have hKp : 0<K := by linarith only [hK]
  have hN : 0<N := (show 0<P/(2*R) by positivity).trans_le hNlo
  have hL : 0<L := (show 0<T/(K*P^3) by positivity).trans_le hLlo
  have hrec : 12/(L*N*Q) ≤ 24*K*P^2*R/(T*Q) := by
    calc
      _ ≤ 12/((T/(K*P^3))*(P/(2*R))*Q) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (mul_le_mul_of_nonneg_right
            (mul_le_mul hLlo hNlo (by positivity) hL.le) hQ.le)
      _ = _ := by field_simp; norm_num
  have hsquare : (Z*Real.sqrt (12/(L*N*Q)))^2 ≤ K^6*(T*Q^3*R/P^2) := by
    calc
      _ = Z^2*(12/(L*N*Q)) := by rw [mul_pow,Real.sq_sqrt (by positivity)]
      _ ≤ (K^2*(T*Q^2/P^2))^2*(24*K*P^2*R/(T*Q)) := mul_le_mul
        (pow_le_pow_left₀ hZ hZupper 2) hrec (by positivity) (by positivity)
      _ = (24*K^5)*(T*Q^3*R/P^2) := by field_simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simpa only [pow_succ'] using mul_le_mul_of_nonneg_right
          (show (24:ℝ) ≤ K by linarith only [hK]) (by positivity : 0 ≤ K^5)
  have hscale : T^6*Q^18*R^6/P^12 ≤ K^36*(P^6*T*R^3) := by
    have hh := pow_le_pow_left₀ (show 0 ≤ T*Q^2 by positivity) hcut 9
    have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ R^6/(T^3*P^12) by positivity)
    have hr := pow_le_pow_left₀ (show 0 ≤ R^3 by positivity) hRthree 4
    have hr' : R^12/T^3 ≤ T := by
      apply (div_le_iff₀ (pow_pos hT 3)).mpr
      convert hr using 1 <;> ring
    calc
      _ ≤ K^36*P^6*R^15/T^3 := by convert hh' using 1 <;> field_simp
      _ = (K^36*P^6*R^3)*(R^12/T^3) := by ring
      _ ≤ (K^36*P^6*R^3)*T := mul_le_mul_of_nonneg_left hr' (by positivity)
      _ = _ := by ring
  calc
    _ ≤ (K^6*(T*Q^3*R/P^2))^6 := by
      simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg _) hsquare 6
    _ = K^36*(T^6*Q^18*R^6/P^12) := by ring
    _ ≤ K^36*(K^36*(P^6*T*R^3)) := mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = _ := by ring

private theorem physical_direct_main_power
    {K T P R N Q U Z : ℝ} (hK : 1000 ≤ K)
    (hT : 0<T) (hP : 0<P) (hR : 0<R) (hQ : 0<Q)
    (hN : 0 ≤ N) (hU : 0 ≤ U) (hZ : 0 ≤ Z)
    (hNhi : N ≤ P/R) (hUhi : U ≤ K*T/P^3)
    (hZupper : Z ≤ K^2*(T*Q^2/P^2))
    (hcut : T^2*Q^3 ≤ K^6*P^3*R^3) (hRthree : R^3 ≤ T) :
    (Z*(3*N*Real.sqrt (3*U*Q*N)))^12 ≤ K^96*(P^6*T*R^3) := by
  have hKp : 0<K := by linarith only [hK]
  have hsquare : (Z*(3*N*Real.sqrt (3*U*Q*N)))^2 ≤
      K^6*(T^3*Q^5/(P^4*R^3)) := by
    calc
      _ = 27*Z^2*U*Q*N^3 := by
        rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity)]
        ring
      _ ≤ 27*(K^2*(T*Q^2/P^2))^2*(K*T/P^3)*Q*(P/R)^3 := by gcongr
      _ = (27*K^5)*(T^3*Q^5/(P^4*R^3)) := by field_simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simpa only [pow_succ'] using mul_le_mul_of_nonneg_right
          (show (27:ℝ) ≤ K by linarith only [hK]) (by positivity : 0 ≤ K^5)
  have hscale : T^18*Q^30/(P^24*R^18) ≤ K^60*(P^6*T*R^3) := by
    have hh := pow_le_pow_left₀ (show 0 ≤ T^2*Q^3 by positivity) hcut 10
    have hh' := mul_le_mul_of_nonneg_left hh
      (show 0 ≤ 1/(T^2*P^24*R^18) by positivity)
    have hr : R^9/T^2 ≤ T := by
      apply (div_le_iff₀ (pow_pos hT 2)).mpr
      have hh := pow_le_pow_left₀ (show 0 ≤ R^3 by positivity) hRthree 3
      convert hh using 1 <;> ring
    calc
      _ ≤ K^60*P^6*R^12/T^2 := by convert hh' using 1 <;> field_simp
      _ = (K^60*P^6*R^3)*(R^9/T^2) := by ring
      _ ≤ (K^60*P^6*R^3)*T := mul_le_mul_of_nonneg_left hr (by positivity)
      _ = _ := by ring
  calc
    _ ≤ (K^6*(T^3*Q^5/(P^4*R^3)))^6 := by
      simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg _) hsquare 6
    _ = K^36*(T^18*Q^30/(P^24*R^18)) := by ring
    _ ≤ K^36*(K^60*(P^6*T*R^3)) := mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = _ := by ring

private theorem physical_boundary_power
    {K T P R N : ℝ} (hK : 1000 ≤ K) (hT : 0<T) (hP : 0<P)
    (hR : 1 ≤ R) (hN : 1 ≤ N) (hNhi : N ≤ P/R)
    (hPtwo : P^2 ≤ T) (hTtwo : T^2 ≤ R^7) :
    (1+23*N)^12 ≤ K^12*(P^6*T*R^3) := by
  have hRp : 0<R := zero_lt_one.trans_le hR
  have hKp : 0<K := by linarith only [hK]
  have hlinear : 1+23*N ≤ K*(P/R) := by
    calc
      _ ≤ 24*N := by linarith only [hN]
      _ ≤ 24*(P/R) := mul_le_mul_of_nonneg_left hNhi (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hK]) (by positivity)
  have hp6 : P^6 ≤ T^3 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg P) hPtwo 3
  have hr715 : R^7 ≤ R^15 := pow_le_pow_right₀ hR (by norm_num)
  have hscale : (P/R)^12 ≤ P^6*T*R^3 := by
    have hh := mul_le_mul_of_nonneg_left (hTtwo.trans hr715) hT.le
    have hh' : P^6 ≤ T*R^15 := by nlinarith only [hp6,hh]
    have hh'' := mul_le_mul_of_nonneg_left hh' (show 0 ≤ P^6/R^12 by positivity)
    convert hh'' using 1 <;> field_simp
  calc
    _ ≤ (K*(P/R))^12 := pow_le_pow_left₀ (by linarith only [hN]) hlinear 12
    _ = K^12*(P/R)^12 := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hscale (by positivity)

private theorem physical_tail_component_bounds
    {K T P R N L X : ℝ} (hK : 1000 ≤ K)
    (hT : 1 ≤ T) (hP : 1 ≤ P) (hR : 1 ≤ R) (hN : 1 ≤ N)
    (hNlo : P/(2*R) ≤ N) (hNhi : N ≤ P/R)
    (hLlo : T/(K*P^3) ≤ L) (hX : 0 ≤ X) (hXhi : X ≤ K*(T/P^2))
    (hPtwo : P^2 ≤ T) (hRthree : R^3 ≤ T) :
    let D := 8/(L*N*(N+1))
    N*(4*(X+1)*D^2) ≤ K^5*(P*R^3/T) ∧
      N*(D*(2+Real.log (D+1))) ≤ K^4*(P^2*R/T)*(1+Real.log T) := by
  intro D
  let Log := 1+Real.log T
  have hKp : 0<K := by linarith only [hK]
  have hK1 : 1 ≤ K := by linarith only [hK]
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hPp : 0<P := zero_lt_one.trans_le hP
  have hRp : 0<R := zero_lt_one.trans_le hR
  have hNp : 0<N := zero_lt_one.trans_le hN
  have hLp : 0<L := (show 0<T/(K*P^3) by positivity).trans_le hLlo
  have hD : 0<D := by dsimp only [D]; positivity
  have hLog : 1 ≤ Log := by dsimp only [Log]; linarith only [Real.log_nonneg hT]
  have hDhi : D ≤ 32*K*P*R^2/T := by
    calc
      _ ≤ 8/(L*N^2) := div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (by nlinarith only [mul_nonneg hLp.le hNp.le])
      _ ≤ 8/((T/(K*P^3))*(P/(2*R))^2) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (mul_le_mul hLlo (pow_le_pow_left₀ (by positivity) hNlo 2)
            (by positivity) hLp.le)
      _ = _ := by field_simp; norm_num
  have hPR : P*R^2/T ≤ T := by
    have hp : P ≤ T := (show P ≤ P^2 by nlinarith only [hP]).trans hPtwo
    have hr : R^2 ≤ T := (pow_le_pow_right₀ hR (show 2 ≤ 3 by norm_num)).trans hRthree
    apply (div_le_iff₀ hTp).mpr
    exact mul_le_mul hp hr (sq_nonneg R) hTp.le
  have hlogD : 2+Real.log (D+1) ≤ K^2*Log := by
    have hscaled := mul_le_mul_of_nonneg_left hPR (show 0 ≤ 32*K by positivity)
    have hdT : D ≤ 32*K*T := hDhi.trans (by convert hscaled using 1; ring)
    have hd : D+1 ≤ (32*K+1)*T := by nlinarith only [hdT,hT]
    have hh := Real.log_le_log (by positivity : 0<D+1) hd
    rw [Real.log_mul (by positivity) hTp.ne'] at hh
    have hl := Real.log_le_sub_one_of_pos (show 0<32*K+1 by positivity)
    have hcoef : 32*K+2 ≤ K^2 := by
      have hh : 1000*K ≤ K^2 := by
        simpa only [pow_two] using mul_le_mul_of_nonneg_right hK hKp.le
      linarith only [hh,hK]
    calc
      _ ≤ 32*K+2+Real.log T := by linarith only [hh,hl]
      _ ≤ (32*K+2)*Log := by
        dsimp only [Log]
        nlinarith only [mul_nonneg (show 0 ≤ 32*K+1 by positivity) (Real.log_nonneg hT)]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (by linarith only [hLog])
  have hXplus : X+1 ≤ 2*K*(T/P^2) := by
    have hX0 : 1 ≤ T/P^2 := (one_le_div (pow_pos hPp 2)).mpr hPtwo
    have hh := le_mul_of_one_le_left (show 0 ≤ T/P^2 by positivity) hK1
    nlinarith only [hXhi,hX0,hh]
  have hfirst : N*(4*(X+1)*D^2) ≤ K^5*(P*R^3/T) := by
    have hcoeff : 8192*K^3 ≤ K^5 := by
      have hkk : (8192:ℝ) ≤ K^2 := by
        have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1000) hK 2
        norm_num at hh
        linarith only [hh]
      calc
        _ ≤ K^2*K^3 := mul_le_mul_of_nonneg_right hkk (by positivity)
        _ = _ := by ring
    calc
      _ ≤ (P/R)*(4*(2*K*(T/P^2))*(32*K*P*R^2/T)^2) := by gcongr
      _ = (8192*K^3)*(P*R^3/T) := by field_simp; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (by positivity)
  have hsecond : N*(D*(2+Real.log (D+1))) ≤ K^4*(P^2*R/T)*Log := by
    have hcoef : 32*K^3 ≤ K^4 := by
      simpa only [pow_succ'] using mul_le_mul_of_nonneg_right
        (show (32:ℝ) ≤ K by linarith only [hK]) (by positivity : 0 ≤ K^3)
    calc
      _ ≤ N*(D*(K^2*Log)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hlogD hD.le) hNp.le
      _ ≤ (P/R)*((32*K*P*R^2/T)*(K^2*Log)) := by gcongr
      _ = (32*K^3)*(P^2*R/T)*Log := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef (by positivity)) (by linarith only [hLog])
  exact ⟨hfirst,hsecond⟩

private theorem physical_tail_monomial_power
    {K T P R Log : ℝ} (hK : 1000 ≤ K) (hT : 1 ≤ T)
    (hPp : 0<P) (hRp : 0<R) (hLog : 1 ≤ Log)
    (hPtwo : P^2 ≤ T) (hRthree : R^3 ≤ T) (hR33 : R^33 ≤ T^10) :
    (K^5*(P*R^3/T)+K^4*(P^2*R/T)*Log)^12 ≤
      K^63*Log^12*(P^6*T*R^3) := by
  have hKp : 0<K := by linarith only [hK]
  have hK1 : 1 ≤ K := by linarith only [hK]
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hscale1 : (P*R^3/T)^12 ≤ P^6*T*R^3 := by
    have hp6 : P^6 ≤ T^3 := by
      simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg P) hPtwo 3
    have hh := mul_le_mul hp6 hR33 (by positivity) (by positivity)
    have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ P^6*R^3/T^12 by positivity)
    convert hh' using 1 <;> field_simp
  have hscale2 : (P^2*R/T)^12 ≤ P^6*T*R^3 := by
    have hp18 : P^18 ≤ T^9 := by
      simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg P) hPtwo 9
    have hr9 : R^9 ≤ T^3 := by
      simpa only [← pow_mul] using pow_le_pow_left₀ (by positivity) hRthree 3
    have hh : P^18*R^9 ≤ T^13 := by
      calc
        _ ≤ T^9*T^3 := mul_le_mul hp18 hr9 (by positivity) (by positivity)
        _ = T^12 := by ring
        _ ≤ _ := pow_le_pow_right₀ hT (by norm_num)
    have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ P^6*R^3/T^12 by positivity)
    convert hh' using 1 <;> field_simp
  have hfirstPow : (K^5*(P*R^3/T))^12 ≤ K^60*Log^12*(P^6*T*R^3) := by
    calc
      _ = K^60*((P*R^3/T)^12) := by ring
      _ ≤ K^60*(P^6*T*R^3) := mul_le_mul_of_nonneg_left hscale1 (by positivity)
      _ ≤ _ := by
        have hh := le_mul_of_one_le_right (show 0 ≤ K^60*(P^6*T*R^3) by positivity)
          (one_le_pow₀ hLog : 1 ≤ Log^12)
        convert hh using 1
        ring
  have hsecondPow : (K^4*(P^2*R/T)*Log)^12 ≤ K^48*Log^12*(P^6*T*R^3) := by
    calc
      _ = K^48*Log^12*((P^2*R/T)^12) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hscale2 (by positivity)
  have hcoeff : (2:ℝ)^11*(K^60+K^48) ≤ K^63 := by
    have hpow : K^48 ≤ K^60 := pow_le_pow_right₀ hK1 (by norm_num)
    have hk3 : (4096:ℝ) ≤ K^3 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1000) hK 3
      norm_num at hh
      linarith only [hh]
    calc
      _ ≤ 4096*K^60 := by nlinarith only [hpow]
      _ ≤ K^3*K^60 := mul_le_mul_of_nonneg_right hk3 (by positivity)
      _ = _ := by ring
  calc
    _ ≤ 2^11*((K^5*(P*R^3/T))^12+(K^4*(P^2*R/T)*Log)^12) :=
      add_pow_le (by positivity) (by positivity) 12
    _ ≤ 2^11*(K^60*Log^12*(P^6*T*R^3)+K^48*Log^12*(P^6*T*R^3)) :=
      mul_le_mul_of_nonneg_left (add_le_add hfirstPow hsecondPow) (by norm_num)
    _ = (2^11*(K^60+K^48))*(Log^12*(P^6*T*R^3)) := by ring
    _ ≤ K^63*(Log^12*(P^6*T*R^3)) :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = _ := by ring

private theorem physical_tail_power
    {K T P R N L X : ℝ} (hK : 1000 ≤ K)
    (hT : 1 ≤ T) (hP : 1 ≤ P) (hR : 1 ≤ R) (hN : 1 ≤ N)
    (hNlo : P/(2*R) ≤ N) (hNhi : N ≤ P/R)
    (hLlo : T/(K*P^3) ≤ L) (hX : 0 ≤ X) (hXhi : X ≤ K*(T/P^2))
    (hPtwo : P^2 ≤ T) (hRthree : R^3 ≤ T) (hR33 : R^33 ≤ T^10) :
    let D := 8/(L*N*(N+1))
    (N*(4*(X+1)*D^2+D*(2+Real.log (D+1))))^12 ≤
      K^63*(1+Real.log T)^12*(P^6*T*R^3) := by
  intro D
  let Log := 1+Real.log T
  have hKp : 0<K := by linarith only [hK]
  have hK1 : 1 ≤ K := by linarith only [hK]
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hPp : 0<P := zero_lt_one.trans_le hP
  have hRp : 0<R := zero_lt_one.trans_le hR
  have hNp : 0<N := zero_lt_one.trans_le hN
  have hLp : 0<L := (show 0<T/(K*P^3) by positivity).trans_le hLlo
  have hD : 0<D := by dsimp only [D]; positivity
  have hLog : 1 ≤ Log := by dsimp only [Log]; linarith only [Real.log_nonneg hT]
  obtain ⟨hfirst,hsecond⟩ := physical_tail_component_bounds hK hT hP hR hN
    hNlo hNhi hLlo hX hXhi hPtwo hRthree
  have hlogDpos : 0 ≤ Real.log (D+1) := Real.log_nonneg (by linarith only [hD])
  have hsum : N*(4*(X+1)*D^2+D*(2+Real.log (D+1))) ≤
      K^5*(P*R^3/T)+K^4*(P^2*R/T)*Log := by
    rw [mul_add]
    exact add_le_add hfirst hsecond
  exact (pow_le_pow_left₀ (by positivity) hsum 12).trans
    (physical_tail_monomial_power hK hT hPp hRp hLog hPtwo hRthree hR33)

private theorem sum_twelfth_common_bound
    {K D a b : ℝ} (hK : 1000 ≤ K) (hD : 0 ≤ D)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ)
    (ha' : a^12 ≤ K^n*D) (hb' : b^12 ≤ K^n*D) :
    (a+b)^12 ≤ K^(n+3)*D := by
  have hKp : 0<K := by linarith only [hK]
  have hk3 : (4096:ℝ) ≤ K^3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1000) hK 3
    norm_num at hh
    linarith only [hh]
  calc
    _ ≤ 2^11*(a^12+b^12) := add_pow_le ha hb 12
    _ ≤ 2^11*(K^n*D+K^n*D) :=
      mul_le_mul_of_nonneg_left (add_le_add ha' hb') (by norm_num)
    _ = 4096*(K^n*D) := by ring
    _ ≤ K^3*(K^n*D) := mul_le_mul_of_nonneg_right hk3 (by positivity)
    _ = _ := by rw [pow_add]; ring

private theorem physical_nonminor_error_power
    {K T P R N Q L Z : ℝ} (hK : 1000 ≤ K)
    (hT : 1 ≤ T) (hP : 1 ≤ P) (hR : 1 ≤ R) (hN : 1 ≤ N) (hQ : 0<Q)
    (hNlo : P/(2*R) ≤ N) (hNhi : N ≤ P/R)
    (hLlo : T/(K*P^3) ≤ L) (hZ : 0 ≤ Z)
    (hZupper : Z ≤ K^2*(T*Q^2/P^2))
    (hcut : T*Q^2 ≤ K^4*P^2*R)
    (hPtwo : P^2 ≤ T) (hRthree : R^3 ≤ T) (hR33 : R^33 ≤ T^10) :
    (Z*(Real.sqrt (3*N)*Real.log (6*N)+6/(L*N^2)+
      Real.sqrt (12/(L*N*Q))))^12 ≤
        K^114*(1+Real.log T)^24*(P^6*T*R^3) := by
  let Log := 1+Real.log T
  let D := Log^24*(P^6*T*R^3)
  have hKp : 0<K := by linarith only [hK]
  have hK1 : 1 ≤ K := by linarith only [hK]
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hPp : 0<P := zero_lt_one.trans_le hP
  have hRp : 0<R := zero_lt_one.trans_le hR
  have hNp : 0<N := zero_lt_one.trans_le hN
  have hLp : 0<L := (show 0<T/(K*P^3) by positivity).trans_le hLlo
  have hLog : 1 ≤ Log := by dsimp only [Log]; linarith only [Real.log_nonneg hT]
  have hZR : Z ≤ K^7*R*Log := by
    have hqscale : T*Q^2/P^2 ≤ K^4*R := by
      apply (div_le_iff₀ (pow_pos hPp 2)).mpr
      nlinarith only [hcut]
    calc
      Z ≤ K^2*(T*Q^2/P^2) := hZupper
      _ ≤ K^2*(K^4*R) := mul_le_mul_of_nonneg_left hqscale (sq_nonneg K)
      _ = K^6*R := by ring
      _ ≤ K^7*R := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hK1 (by norm_num)) hRp.le
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hLog
  have hcommon := physical_common_error_powers hK hT hP hR hN hNlo hNhi
    hLlo hZ hZR hPtwo hRthree hR33
  have hend := physical_endpoint_error_power hK hTp hPp hRp hQ hNlo hLlo hZ
    hZupper hcut hRthree
  have hend' : (Z*Real.sqrt (12/(L*N*Q)))^12 ≤ K^111*D := by
    calc
      _ ≤ K^72*(P^6*T*R^3) := hend
      _ ≤ K^111*(P^6*T*R^3) := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hK1 (by norm_num)) (by positivity)
      _ ≤ K^111*((P^6*T*R^3)*Log^24) := mul_le_mul_of_nonneg_left
        (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hLog)) (by positivity)
      _ = _ := by dsimp only [D]; ring
  have hlogN : 0 ≤ Real.log (6*N) := Real.log_nonneg (by linarith only [hN])
  have hcommon' : (Z*(Real.sqrt (3*N)*Real.log (6*N)+6/(L*N^2)))^12 ≤
      K^111*D := by
    dsimp only [D,Log]
    simpa only [mul_assoc] using hcommon
  have hh := sum_twelfth_common_bound hK (show 0 ≤ D by dsimp only [D]; positivity)
    (show 0 ≤ Z*(Real.sqrt (3*N)*Real.log (6*N)+6/(L*N^2)) by positivity)
    (show 0 ≤ Z*Real.sqrt (12/(L*N*Q)) by positivity) 111
    hcommon' hend'
  dsimp only [D,Log] at hh
  simpa only [Nat.reduceAdd,mul_add,mul_assoc,add_assoc] using hh

private theorem physical_direct_budget_power
    {K T P R N Q L U Z Cd : ℝ} (hK : 1000 ≤ K)
    (hT : 1 ≤ T) (hP : 1 ≤ P) (hR : 1 ≤ R) (hN : 1 ≤ N) (hQ : 0<Q)
    (hNlo : P/(2*R) ≤ N) (hNhi : N ≤ P/R)
    (hLlo : T/(K*P^3) ≤ L) (hU : 0 ≤ U) (hUhi : U ≤ K*T/P^3)
    (hZ : 0 ≤ Z) (hZupper : Z ≤ K^2*(T*Q^2/P^2))
    (hCd : 0 ≤ Cd) (hCdhi : Cd ≤ K)
    (hcut : T^2*Q^3 ≤ K^6*P^3*R^3)
    (hPtwo : P^2 ≤ T) (hRthree : R^3 ≤ T) (hR33 : R^33 ≤ T^10) :
    (Cd*Z*(3*N*Real.sqrt (3*U*Q*N)+
      (Real.sqrt (3*N)*Real.log (6*N)+6/(L*N^2))+
      Real.sqrt (12/(L*N*Q))))^12 ≤
        K^129*(1+Real.log T)^24*(P^6*T*R^3) := by
  let Log := 1+Real.log T
  let D := Log^24*(P^6*T*R^3)
  let a := Z*(3*N*Real.sqrt (3*U*Q*N))
  let b := Z*(Real.sqrt (3*N)*Real.log (6*N)+6/(L*N^2)+Real.sqrt (12/(L*N*Q)))
  have hKp : 0<K := by linarith only [hK]
  have hK1 : 1 ≤ K := by linarith only [hK]
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hPp : 0<P := zero_lt_one.trans_le hP
  have hRp : 0<R := zero_lt_one.trans_le hR
  have hNp : 0<N := zero_lt_one.trans_le hN
  have hLp : 0<L := (show 0<T/(K*P^3) by positivity).trans_le hLlo
  have hLog : 1 ≤ Log := by dsimp only [Log]; linarith only [Real.log_nonneg hT]
  have hlogN : 0 ≤ Real.log (6*N) := Real.log_nonneg (by linarith only [hN])
  have ha := physical_direct_main_power hK hTp hPp hRp hQ hNp.le hU hZ
    hNhi hUhi hZupper hcut hRthree
  have hb := physical_nonminor_error_power hK hT hP hR hN hQ hNlo hNhi hLlo
    hZ hZupper (direct_cut_implies_quadratic_cut hKp hTp hPp hRp hQ hRthree hcut)
    hPtwo hRthree hR33
  have ha' : a^12 ≤ K^114*D := by
    calc
      _ ≤ K^96*(P^6*T*R^3) := ha
      _ ≤ K^114*(P^6*T*R^3) := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hK1 (by norm_num)) (by positivity)
      _ ≤ K^114*((P^6*T*R^3)*Log^24) := mul_le_mul_of_nonneg_left
        (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hLog)) (by positivity)
      _ = _ := by dsimp only [D]; ring
  have hb' : b^12 ≤ K^114*D := by
    dsimp only [D,Log,b]
    simpa only [mul_assoc] using hb
  have hh := sum_twelfth_common_bound hK (show 0 ≤ D by dsimp only [D]; positivity)
    (show 0 ≤ a by dsimp only [a]; positivity)
    (show 0 ≤ b by dsimp only [b]; positivity) 114 ha' hb'
  have hsum : (a+b)^12 ≤ K^117*D := by simpa only [Nat.reduceAdd] using hh
  calc
    _ = Cd^12*(a+b)^12 := by dsimp only [a,b]; ring
    _ ≤ K^12*(K^117*D) := mul_le_mul (pow_le_pow_left₀ hCd hCdhi 12) hsum
      (by positivity) (by positivity)
    _ = _ := by dsimp only [D,Log]; ring

private theorem physical_moment_band_main_bounds
    {K c u T P R N Q lam F X C Cf ε : ℝ} (hK : 1000 ≤ K)
    (hc : 1/K ≤ c ∧ c ≤ K) (hu : 1/K ≤ u ∧ u ≤ K)
    (hT : 1 ≤ T) (hP : 1 ≤ P) (hR : 1 ≤ R) (hQ : 1 ≤ Q)
    (hNlo : P/(2*R) ≤ N) (hNhi : N ≤ P/R) (hQN : Q ≤ 2*N)
    (hlam : T/(K*P^4) ≤ lam) (hF : F ≤ K*T/P^4)
    (hX : 0 ≤ X) (hXhi : X ≤ K*(T/P^2))
    (hC : 0 ≤ C) (hChi : C ≤ K) (hCf : 0 ≤ Cf) (hCfhi : Cf ≤ K)
    (hε : 0 ≤ ε) (hPtwo : P^2 ≤ T) (hPR : P ≤ R^2)
    (hTtwo : T^2 ≤ R^7) (hRthree : R^3 ≤ T)
    (hPthree : T ≤ P^3) (hgamma : T^2 ≤ P^2*R^4)
    (hdual : 12 ≤ (c*T/P^3)*Q*N^2) :
    let L := c*T/P^3
    let U := u*T/P^3
    let M : ℕ := ⌈63*U*Q*N^2⌉₊+1
    let V := 756*U/L
    let W := 1+32/(L*Q^2*N)
    let d := L*Q*N/12
    let zeta := Real.sqrt M/(6*(M:ℝ)^2)
    let E := 16*U*Real.sqrt (U*Q^3)*zeta+3*F/4
    let Gamma := Q^2/(6*(M:ℝ)^2)
    let rho := (12*U*Real.sqrt (U*Q^3)/lam)*zeta
    let D := 16/(L*N*Q)
    let Y := 4*(X+1)*D^2+D*(2+Real.log (D+1))
    let Z := 4*Q*(2*X*Q+1)
    let Pair := fun A : ℝ =>
      4*A*(1+6*U*(rho+1))+16*(2*Gamma+1)*(2*X+5)^2*(Gamma+48*E*Q^2/L)
    let H := 1+R^3/P^2
    let Log := 1+Real.log T
    let Eps := (K^3*T)^ε
    (3 ≤ L*Q^2*N/8 →
      C*((2/d)^6*(1+Real.log M)^12*(M:ℝ)^((12:ℝ)+ε)*(2*Y)^10*Pair Y) ≤
        K^165*Eps*H*Log^23*(P^6*T*R^3)) ∧
    (Q=2 ∨ L*Q^2*N/8<3 →
      Cf*((5*W)^11*W^2*(6*(3+8*Real.pi*V)*(1+Real.log M))^12*
        (2/d)^6*(M:ℝ)^((12:ℝ)+ε)*(2*Z)^10*Pair Z) ≤
          K^205*Eps*H*Log^12*(P^6*T*R^3)) := by
  intro L U M V W d zeta E Gamma rho D Y Z Pair H Log Eps
  have hKp : 0<K := by linarith only [hK]
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hPp : 0<P := zero_lt_one.trans_le hP
  have hRp : 0<R := zero_lt_one.trans_le hR
  have hQp : 0<Q := zero_lt_one.trans_le hQ
  have hNp : 0<N := (show 0<P/(2*R) by positivity).trans_le hNlo
  have hcp : 0<c := (one_div_pos.mpr hKp).trans_le hc.1
  have hup : 0<u := (one_div_pos.mpr hKp).trans_le hu.1
  have hLp : 0<L := by dsimp only [L]; positivity
  have hUp : 0<U := by dsimp only [U]; positivity
  have hLlo : T/(K*P^3) ≤ L := by
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc.1 hTp.le) (pow_nonneg hPp.le 3)
    convert hh using 1
    ring
  have hUhi : U ≤ K*T/P^3 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hu.2 hTp.le) (pow_nonneg hPp.le 3)
  have hMnat : 0<M := by dsimp only [M]; omega
  have hMp : 0<(M:ℝ) := by exact_mod_cast hMnat
  have hMbound := normalized_physical_dual_ceiling hK hc hu hTp hPp hRp hQp
    hNlo hNhi hdual
  have hgeom1 : T ≤ P^2*R := by
    have hh := mul_le_mul_of_nonneg_left hRthree (show 0 ≤ P^2*R by positivity)
    have hstep : T*T ≤ (P^2*R)*T := by nlinarith only [hgamma,hh]
    exact (mul_le_mul_iff_right₀ hTp).mp (by nlinarith only [hstep])
  have hgeom2 : T ≤ P*R^3 := by
    have hh : T ≤ P*R^2 := (sq_le_sq₀ hTp.le (by positivity)).mp
      (by convert hgamma using 1; ring)
    have hr : R^2 ≤ R^3 := pow_le_pow_right₀ hR (by norm_num)
    exact hh.trans (mul_le_mul_of_nonneg_left hr hPp.le)
  have hRT : R ≤ T := (show R ≤ R^3 by
    simpa using pow_le_pow_right₀ hR (show 1 ≤ 3 by norm_num)).trans hRthree
  have hQR : Q ≤ 2*R := by
    have hh : P/R ≤ R := (div_le_iff₀ hRp).mpr (by simpa only [pow_two] using hPR)
    exact hQN.trans (mul_le_mul_of_nonneg_left (hNhi.trans hh) (by norm_num))
  have hcounts := physical_block_count_bounds hK hT hPp hRp hQ hXhi
    hLlo hNlo hPtwo hQR hRT
  have hDpos : 0<D := by dsimp only [D]; positivity
  have hY : 0 ≤ Y := by
    have hh : 0 ≤ Real.log (D+1) := Real.log_nonneg (by linarith only [hDpos])
    dsimp only [Y]
    positivity
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hH : 1 ≤ H := by
    dsimp only [H]
    linarith only [show 0 ≤ R^3/P^2 by positivity]
  have hLog : 1 ≤ Log := by dsimp only [Log]; linarith only [Real.log_nonneg hT]
  have hfactors := physical_pair_factor_bounds hK hTp hPp hRp hQp hUp.le hMp hX
    hUhi hMbound.1 hLlo hlam hF hXhi hgeom2 hPthree hgamma hPtwo
  have hpairs := normalized_pair_count_bounds hK hTp hPp hRp hQp hH hLog hY hZ
    hfactors.1 hfactors.2.2 hcounts.1 hcounts.2
  have hpref := physical_moment_prefactors hK hT hPp hR hQp hNlo hNhi hQN
    hLlo hUp.le hUhi hMp hMbound.2
  have houter := moment_rpow_prefactor hKp hTp hRp hQp hMp hε hpref.1 hpref.2.2.2
  have hlogM : 0 ≤ 1+Real.log (M:ℝ) := by
    have hh := Real.log_natCast_nonneg M
    linarith only [hh]
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hA : 0 ≤ (2/d)^6*(M:ℝ)^((12:ℝ)+ε) := by positivity
  have hEps : 0 ≤ Eps := by dsimp only [Eps]; positivity
  constructor
  · intro hminor
    have hscale := minor_branch_scales hcp hc.2 hTp hPp hRp hNp.le hQp.le
      hQN hNhi hminor
    have hh := normalized_minor_moment_main (Pair:=Pair Y) (Log:=Log) hK hTp hPp hRp hQp
      hC hA hY hlogM (by linarith only [hH]) (by linarith only [hLog]) hEps
      hChi houter hpref.2.1 hcounts.1 hpairs.1 hscale.2 hTtwo
    convert hh using 1
    ac_rfl
  · intro hcase
    have hscale := frozen_branch_scales hK hc.1 hTp hPp hRp hQp hNlo hgeom1 hcase
    have hh := normalized_frozen_moment_main (Pair:=Pair Z) (Log:=Log) hK hTp hPp hRp hQp hCf hA hZ
      (show 0 ≤ 6*(3+8*Real.pi*V)*(1+Real.log (M:ℝ)) by positivity)
      hW (by linarith only [hH]) hEps hCfhi houter hpref.2.2.1 hscale.2
      hcounts.2 (hpairs.2 hscale.1) hscale.1 hTtwo
    convert hh using 1
    ac_rfl

                                                                                 
theorem physical_dyadic_geometry
    {K T : ℝ} {N : ℕ} (hK : 1000 ≤ K) (hT : 1 ≤ T)
    (hN : 0<N) (hNT : (N:ℝ) ≤ T) :
    let J := Nat.log 2 N+1
    (J:ℝ)+2 ≤ K*(1+Real.log T) ∧
      ∀ j∈Finset.range J, (1:ℝ) ≤ (2^(j+1):ℕ) ∧ (2^(j+1):ℝ) ≤ 2*(N:ℝ) := by
  intro J
  have hNreal : 0<(N:ℝ) := by exact_mod_cast hN
  have hp : (2:ℝ)^(Nat.log 2 N) ≤ (N:ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (Nat.ne_of_gt hN)
  have hh := Real.log_le_log (pow_pos (by norm_num : (0:ℝ)<2) _) hp
  rw [Real.log_pow] at hh
  have hlogtwo : (1:ℝ)/2 ≤ Real.log 2 := by
    have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hl ⊢
    exact hl
  have hlogN := Real.log_le_log hNreal hNT
  have hlogT := Real.log_nonneg hT
  constructor
  · have hhalf := mul_le_mul_of_nonneg_left hlogtwo (Nat.cast_nonneg (Nat.log 2 N))
    have hcoef := mul_nonneg (show 0 ≤ K-2 by linarith only [hK]) hlogT
    dsimp only [J]
    rw [Nat.cast_add,Nat.cast_one]
    nlinarith only [hh,hhalf,hlogN,hcoef,hK]
  · intro j hj
    have hjlog : j ≤ Nat.log 2 N := by
      have hh := Finset.mem_range.mp hj
      dsimp only [J] at hh
      omega
    have hQ : 2^(j+1) ≤ 2*N := by
      calc
        _ = 2*2^j := by rw [pow_succ,Nat.mul_comm]
        _ ≤ 2*2^(Nat.log 2 N) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hjlog)
        _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2 (Nat.ne_of_gt hN))
    constructor
    · exact_mod_cast (one_le_pow₀ (by norm_num : (1:ℕ) ≤ 2) : 1 ≤ 2^(j+1))
    · exact_mod_cast hQ

private theorem absorb_moment_band_error
    {K Eps H Log V C A err : ℝ} {m n r : ℕ}
    (hK : 1000 ≤ K) (hEps : 1 ≤ Eps) (hH : 1 ≤ H) (hLog : 1 ≤ Log)
    (hV : 0 ≤ V) (hC : 0 ≤ C) (hChi : C ≤ K)
    (hm : m ≤ 205) (hn : n ≤ 114) (hr : r ≤ 24)
    (hmain : C*A ≤ K^m*Eps*H*Log^r*V)
    (herr : err ≤ K^n*Log^24*V) :
    C*(A+err) ≤ K^210*Eps*H*Log^24*V := by
  have hKp : 0<K := by linarith only [hK]
  have hK1 : 1 ≤ K := by linarith only [hK]
  have hEp : 0 ≤ Eps := by linarith only [hEps]
  have hHp : 0 ≤ H := by linarith only [hH]
  have hLp : 0 ≤ Log := by linarith only [hLog]
  have hmain' : C*A ≤ K^205*Eps*H*Log^24*V := by
    apply hmain.trans
    gcongr
  have herr' : C*err ≤ K^205*Eps*H*Log^24*V := by
    have hpow : K^(n+1) ≤ K^205 := pow_le_pow_right₀ hK1 (by omega)
    have hpos : 0 ≤ K^205*Log^24*V :=
      mul_nonneg (mul_nonneg (pow_nonneg hKp.le 205) (pow_nonneg hLp 24)) hV
    calc
      C*err ≤ C*(K^n*Log^24*V) := mul_le_mul_of_nonneg_left herr hC
      _ ≤ K*(K^n*Log^24*V) := mul_le_mul_of_nonneg_right hChi (by positivity)
      _ = K^(n+1)*Log^24*V := by rw [pow_succ']; ring
      _ ≤ K^205*Log^24*V := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpow (by positivity)) hV
      _ ≤ (K^205*Log^24*V)*Eps :=
        le_mul_of_one_le_right hpos hEps
      _ ≤ ((K^205*Log^24*V)*Eps)*H :=
        le_mul_of_one_le_right (mul_nonneg hpos hEp) hH
      _ = _ := by ring
  have hcoeff : 2*K^205 ≤ K^210 := by
    calc
      _ ≤ K*K^205 := mul_le_mul_of_nonneg_right
        (by linarith only [hK]) (by positivity)
      _ = K^206 := by ring
      _ ≤ _ := pow_le_pow_right₀ hK1 (by norm_num)
  calc
    C*(A+err) = C*A+C*err := mul_add _ _ _
    _ ≤ K^205*Eps*H*Log^24*V+K^205*Eps*H*Log^24*V :=
      add_le_add hmain' herr'
    _ = (2*K^205)*(Eps*H*Log^24*V) := by ring
    _ ≤ K^210*(Eps*H*Log^24*V) :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = _ := by ring

private theorem physical_moment_band_budget_bounds
    {K c u T P R N Q lam F X C Cf ε : ℝ} (hK : 1000 ≤ K)
    (hc : 1/K ≤ c ∧ c ≤ K) (hu : 1/K ≤ u ∧ u ≤ K)
    (hT : 1 ≤ T) (hP : 1 ≤ P) (hR : 1 ≤ R) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hNlo : P/(2*R) ≤ N) (hNhi : N ≤ P/R) (hQN : Q ≤ 2*N)
    (hlam : T/(K*P^4) ≤ lam) (hF : F ≤ K*T/P^4)
    (hX : 0 ≤ X) (hXhi : X ≤ K*(T/P^2))
    (hC : 0 ≤ C) (hChi : C ≤ K) (hCf : 0 ≤ Cf) (hCfhi : Cf ≤ K)
    (hε : 0 ≤ ε) (hPtwo : P^2 ≤ T) (hPR : P ≤ R^2)
    (hTtwo : T^2 ≤ R^7) (hRthree : R^3 ≤ T) (hR33 : R^33 ≤ T^10)
    (hPthree : T ≤ P^3) (hgamma : T^2 ≤ P^2*R^4)
    (hdual : 12 ≤ (c*T/P^3)*Q*N^2) :
    let L := c*T/P^3
    let U := u*T/P^3
    let M : ℕ := ⌈63*U*Q*N^2⌉₊+1
    let V := 756*U/L
    let W := 1+32/(L*Q^2*N)
    let d := L*Q*N/12
    let zeta := Real.sqrt M/(6*(M:ℝ)^2)
    let E := 16*U*Real.sqrt (U*Q^3)*zeta+3*F/4
    let Gamma := Q^2/(6*(M:ℝ)^2)
    let rho := (12*U*Real.sqrt (U*Q^3)/lam)*zeta
    let D := 16/(L*N*Q)
    let Y := 4*(X+1)*D^2+D*(2+Real.log (D+1))
    let Z := 4*Q*(2*X*Q+1)
    let Err := Real.sqrt (3*N)*Real.log (6*N)+6/(L*N^2)
    let Pair := fun A : ℝ =>
      4*A*(1+6*U*(rho+1))+16*(2*Gamma+1)*(2*X+5)^2*(Gamma+48*E*Q^2/L)
    let H := 1+R^3/P^2
    let Log := 1+Real.log T
    let Eps := (K^3*T)^ε
    (3 ≤ L*Q^2*N/8 →
      C*((2/d)^6*(1+Real.log M)^12*(M:ℝ)^((12:ℝ)+ε)*(2*Y)^10*Pair Y+(Y*Err)^12) ≤
        K^210*Eps*H*Log^24*(P^6*T*R^3)) ∧
    (Q=2 ∨ L*Q^2*N/8<3 →
      Cf*((5*W)^11*W^2*(6*(3+8*Real.pi*V)*(1+Real.log M))^12*
        (2/d)^6*(M:ℝ)^((12:ℝ)+ε)*(2*Z)^10*Pair Z+(Z*(Err+Real.sqrt (12/(L*N*Q))))^12) ≤
          K^210*Eps*H*Log^24*(P^6*T*R^3)) := by
  intro L U M V W d zeta E Gamma rho D Y Z Err Pair H Log Eps
  have hmain := physical_moment_band_main_bounds hK hc hu hT hP hR hQ hNlo hNhi hQN
    hlam hF hX hXhi hC hChi hCf hCfhi hε hPtwo hPR hTtwo hRthree hPthree hgamma hdual
  have hKp : 0<K := by linarith only [hK]
  have hK1 : 1 ≤ K := by linarith only [hK]
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hPp : 0<P := zero_lt_one.trans_le hP
  have hRp : 0<R := zero_lt_one.trans_le hR
  have hQp : 0<Q := zero_lt_one.trans_le hQ
  have hNp : 0<N := zero_lt_one.trans_le hN
  have hcp : 0<c := (one_div_pos.mpr hKp).trans_le hc.1
  have hLp : 0<L := by dsimp only [L]; positivity
  have hLlo : T/(K*P^3) ≤ L := by
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc.1 hTp.le) (pow_nonneg hPp.le 3)
    convert hh using 1
    ring
  have hRT : R ≤ T := (show R ≤ R^3 by
    simpa using pow_le_pow_right₀ hR (show 1 ≤ 3 by norm_num)).trans hRthree
  have hQR : Q ≤ 2*R := by
    have hh : P/R ≤ R := (div_le_iff₀ hRp).mpr (by simpa only [pow_two] using hPR)
    exact hQN.trans (mul_le_mul_of_nonneg_left (hNhi.trans hh) (by norm_num))
  have hcounts := physical_block_count_bounds hK hT hPp hRp hQ hXhi
    hLlo hNlo hPtwo hQR hRT
  have hDpos : 0<D := by dsimp only [D]; positivity
  have hY : 0 ≤ Y := by
    have hh : 0 ≤ Real.log (D+1) := Real.log_nonneg (by linarith only [hDpos])
    dsimp only [Y]
    positivity
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hH : 1 ≤ H := by
    dsimp only [H]
    linarith only [show 0 ≤ R^3/P^2 by positivity]
  have hLog : 1 ≤ Log := by dsimp only [Log]; linarith only [Real.log_nonneg hT]
  have hEps : 1 ≤ Eps := Real.one_le_rpow
    (hT.trans (le_mul_of_one_le_left hTp.le (one_le_pow₀ hK1))) hε
  constructor
  · intro hminor
    have hscale := minor_branch_scales hcp hc.2 hTp hPp hRp hNp.le hQp.le
      hQN hNhi hminor
    have hY0 : P^2*R^2/(T*Q^2) ≤ K*R := by
      have hh := mul_le_mul_of_nonneg_left hscale.2 (show 0 ≤ R/(T*Q^2) by positivity)
      convert hh using 1 <;> field_simp
    have hYR : Y ≤ K^7*R*Log := by
      calc
        _ ≤ K^6*(P^2*R^2/(T*Q^2))*Log := hcounts.1
        _ ≤ K^6*(K*R)*Log := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hY0 (by positivity)) (by linarith only [hLog])
        _ = _ := by ring
    have herror := physical_common_error_powers hK hT hP hR hN hNlo hNhi
      hLlo hY hYR hPtwo hRthree hR33
    have hMain : C*((2/d)^6*(1+Real.log M)^12*(M:ℝ)^((12:ℝ)+ε)*
        (2*Y)^10*Pair Y) ≤ K^165*Eps*H*Log^23*(P^6*T*R^3) := hmain.1 hminor
    exact absorb_moment_band_error hK hEps hH hLog (by positivity) hC hChi
      (by norm_num) (by norm_num) (by norm_num) hMain herror
  · intro hcase
    have hgeom : T ≤ P^2*R := by
      have hh := mul_le_mul_of_nonneg_left hRthree (show 0 ≤ P^2*R by positivity)
      have hstep : T*T ≤ T*(P^2*R) := by nlinarith only [hgamma,hh]
      exact (mul_le_mul_iff_right₀ hTp).mp hstep
    have hscale := frozen_branch_scales hK hc.1 hTp hPp hRp hQp hNlo hgeom hcase
    have hcoef : 48*K ≤ K^4 := by
      calc
        _ ≤ K*K := mul_le_mul_of_nonneg_right (by linarith only [hK]) hKp.le
        _ = K^2 := by ring
        _ ≤ _ := pow_le_pow_right₀ hK1 (by norm_num)
    have hcut : T*Q^2 ≤ K^4*P^2*R := hscale.1.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef (sq_nonneg P)) hRp.le)
    have herror := physical_nonminor_error_power hK hT hP hR hN hQp hNlo hNhi
      hLlo hZ hcounts.2 hcut hPtwo hRthree hR33
    have hMain : Cf*((5*W)^11*W^2*(6*(3+8*Real.pi*V)*(1+Real.log M))^12*
        (2/d)^6*(M:ℝ)^((12:ℝ)+ε)*(2*Z)^10*Pair Z) ≤
          K^205*Eps*H*Log^12*(P^6*T*R^3) := hmain.2 hcase
    exact absorb_moment_band_error hK hEps hH hLog (by positivity) hCf hCfhi
      (by norm_num) (by norm_num) (by norm_num) hMain herror

private theorem physical_source_band_budget
    {K c u T P R N Q lam F X C Cd Cf ε : ℝ} (j : ℕ) (hK : 1000 ≤ K)
    (hc : 1/K ≤ c ∧ c ≤ K) (hu : 1/K ≤ u ∧ u ≤ K)
    (hT : 1 ≤ T) (hP : 1 ≤ P) (hR : 1 ≤ R) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hNlo : P/(2*R) ≤ N) (hNhi : N ≤ P/R) (hQN : Q ≤ 2*N)
    (hlam : T/(K*P^4) ≤ lam) (hF : F ≤ K*T/P^4)
    (hX : 0 ≤ X) (hXhi : X ≤ K*(T/P^2))
    (hC : 0 ≤ C) (hChi : C ≤ K) (hCd : 0 ≤ Cd) (hCdhi : Cd ≤ K) (hCf : 0 ≤ Cf) (hCfhi : Cf ≤ K)
    (hε : 0 ≤ ε) (hPtwo : P^2 ≤ T) (hPR : P ≤ R^2)
    (hTtwo : T^2 ≤ R^7) (hRthree : R^3 ≤ T) (hR33 : R^33 ≤ T^10)
    (hPthree : T ≤ P^3) (hgamma : T^2 ≤ P^2*R^4)
    (hQzero : j=0 → Q=2) :
    let L := c*T/P^3
    let U := u*T/P^3
    let M : ℕ := ⌈63*U*Q*N^2⌉₊+1
    let V := 756*U/L
    let W := 1+32/(L*Q^2*N)
    let d := L*Q*N/12
    let zeta := Real.sqrt M/(6*(M:ℝ)^2)
    let E := 16*U*Real.sqrt (U*Q^3)*zeta+3*F/4
    let Gamma := Q^2/(6*(M:ℝ)^2)
    let rho := (12*U*Real.sqrt (U*Q^3)/lam)*zeta
    let D := 16/(L*N*Q)
    let Y := 4*(X+1)*D^2+D*(2+Real.log (D+1))
    let Z := 4*Q*(2*X*Q+1)
    let Err := Real.sqrt (3*N)*Real.log (6*N)+6/(L*N^2)
    let Pair := fun A : ℝ =>
      4*A*(1+6*U*(rho+1))+16*(2*Gamma+1)*(2*X+5)^2*(Gamma+48*E*Q^2/L)
    let H := 1+R^3/P^2
    let Log := 1+Real.log T
    let Eps := (K^3*T)^ε
    (if 1 ≤ j ∧ 3 ≤ L*Q^2*N/8 then
      C*((2/d)^6*(1+Real.log M)^12*(M:ℝ)^((12:ℝ)+ε)*(2*Y)^10*Pair Y+(Y*Err)^12)
    else if 12 ≤ L*Q*N^2 ∧ 384 ≤ L^2*Q^3*N^3 then
      Cf*((5*W)^11*W^2*(6*(3+8*Real.pi*V)*(1+Real.log M))^12*
        (2/d)^6*(M:ℝ)^((12:ℝ)+ε)*(2*Z)^10*Pair Z+(Z*(Err+Real.sqrt (12/(L*N*Q))))^12)
    else
      (Cd*Z*(3*N*Real.sqrt (3*U*Q*N)+Err+Real.sqrt (12/(L*N*Q))))^12) ≤
        K^210*Eps*H*Log^24*(P^6*T*R^3) := by
  intro L U M V W d zeta E Gamma rho D Y Z Err Pair H Log Eps
  have hKp : 0<K := by linarith only [hK]
  have hK1 : 1 ≤ K := by linarith only [hK]
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hPp : 0<P := zero_lt_one.trans_le hP
  have hRp : 0<R := zero_lt_one.trans_le hR
  have hQp : 0<Q := zero_lt_one.trans_le hQ
  have hNp : 0<N := zero_lt_one.trans_le hN
  have hcp : 0<c := (one_div_pos.mpr hKp).trans_le hc.1
  have hup : 0<u := (one_div_pos.mpr hKp).trans_le hu.1
  have hLp : 0<L := by dsimp only [L]; positivity
  have hUp : 0<U := by dsimp only [U]; positivity
  have hLlo : T/(K*P^3) ≤ L := by
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc.1 hTp.le) (pow_nonneg hPp.le 3)
    convert hh using 1
    ring
  have hUhi : U ≤ K*T/P^3 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hu.2 hTp.le) (pow_nonneg hPp.le 3)
  by_cases hm : 1 ≤ j ∧ 3 ≤ L*Q^2*N/8
  · rw [ite_eq_left hm]
    have hs := minor_branch_scales hcp hc.2 hTp hPp hRp hNp.le hQp.le hQN hNhi hm.2
    exact (physical_moment_band_budget_bounds hK hc hu hT hP hR hN hQ hNlo hNhi hQN
      hlam hF hX hXhi hC hChi hCf hCfhi hε hPtwo hPR hTtwo hRthree hR33
      hPthree hgamma hs.1).1 hm.2
  · rw [ite_eq_right hm]
    by_cases hf : 12 ≤ L*Q*N^2 ∧ 384 ≤ L^2*Q^3*N^3
    · rw [ite_eq_left hf]
      have hcase : Q=2 ∨ L*Q^2*N/8<3 := by
        by_cases hj : 1 ≤ j
        · exact Or.inr (lt_of_not_ge (fun hh => hm ⟨hj,hh⟩))
        · exact Or.inl (hQzero (by omega))
      exact (physical_moment_band_budget_bounds hK hc hu hT hP hR hN hQ hNlo hNhi hQN
        hlam hF hX hXhi hC hChi hCf hCfhi hε hPtwo hPR hTtwo hRthree hR33
        hPthree hgamma hf.1).2 hcase
    · rw [ite_eq_right hf]
      have hcut := direct_branch_cube_cutoff hK hc.1 hTp hPp hRp hQp hNlo hRthree hf
      have hRT : R ≤ T := (show R ≤ R^3 by
        simpa using pow_le_pow_right₀ hR (show 1 ≤ 3 by norm_num)).trans hRthree
      have hQR : Q ≤ 2*R := by
        have hh : P/R ≤ R := (div_le_iff₀ hRp).mpr (by simpa only [pow_two] using hPR)
        exact hQN.trans (mul_le_mul_of_nonneg_left (hNhi.trans hh) (by norm_num))
      have hZhi := (physical_block_count_bounds hK hT hPp hRp hQ hXhi
        hLlo hNlo hPtwo hQR hRT).2
      have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
      have hh := physical_direct_budget_power hK hT hP hR hN hQp hNlo hNhi hLlo
        hUp.le hUhi hZ hZhi hCd hCdhi hcut hPtwo hRthree hR33
      have hH : 1 ≤ H := by
        dsimp only [H]
        linarith only [show 0 ≤ R^3/P^2 by positivity]
      have hEps : 1 ≤ Eps := Real.one_le_rpow
        (hT.trans (le_mul_of_one_le_left hTp.le (one_le_pow₀ hK1))) hε
      have hLog : 0 ≤ Log := by
        dsimp only [Log]
        linarith only [Real.log_nonneg hT]
      have hpos : 0 ≤ K^210*Log^24*(P^6*T*R^3) :=
        mul_nonneg (mul_nonneg (pow_nonneg hKp.le 210) (pow_nonneg hLog 24)) (by positivity)
      calc
        _ ≤ K^129*Log^24*(P^6*T*R^3) := hh
        _ ≤ K^210*Log^24*(P^6*T*R^3) := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK1 (by norm_num))
            (pow_nonneg hLog 24)) (by positivity)
        _ ≤ (K^210*Log^24*(P^6*T*R^3))*Eps := le_mul_of_one_le_right hpos hEps
        _ ≤ ((K^210*Log^24*(P^6*T*R^3))*Eps)*H :=
          le_mul_of_one_le_right (mul_nonneg hpos (by linarith only [hEps])) hH
        _ = _ := by ring

private theorem finite_source_budget_sum
    {K Eps H Log V boundary tail : ℝ} (J : ℕ) (budget : ℕ → ℝ)
    (hK : 0 ≤ K) (hEps : 0 ≤ Eps) (hH : 0 ≤ H) (hLog : 0 ≤ Log) (hV : 0 ≤ V)
    (hJ : (J:ℝ)+2 ≤ K*Log)
    (hboundary : boundary ≤ K^210*Eps*H*Log^24*V)
    (htail : tail ≤ K^210*Eps*H*Log^24*V)
    (hband : ∀ j∈Finset.range J, budget j ≤ K^210*Eps*H*Log^24*V) :
    ((J:ℝ)+2)^11*(boundary+tail+∑ j∈Finset.range J,budget j) ≤
      K^222*Eps*H*Log^36*V := by
  let B := K^210*Eps*H*Log^24*V
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (pow_nonneg hK 210) hEps) hH) (pow_nonneg hLog 24)) hV
  have hsum : ∑ j∈Finset.range J,budget j ≤ (J:ℝ)*B := by
    calc
      _ ≤ ∑ _j∈Finset.range J,B := Finset.sum_le_sum hband
      _ = _ := by simp
  have hinside : boundary+tail+∑ j∈Finset.range J,budget j ≤ ((J:ℝ)+2)*B := by
    have hh := add_le_add (add_le_add hboundary htail) hsum
    change boundary+tail+∑ j∈Finset.range J,budget j ≤ B+B+(J:ℝ)*B at hh
    nlinarith only [hh]
  calc
    _ ≤ ((J:ℝ)+2)^11*(((J:ℝ)+2)*B) :=
      mul_le_mul_of_nonneg_left hinside (by positivity)
    _ = ((J:ℝ)+2)^12*B := by ring
    _ ≤ (K*Log)^12*B := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) hJ 12) hB
    _ = _ := by dsimp only [B]; ring

private theorem exists_model_physical_global_bound {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∃ δ>(0:ℝ), ∃ K ≥ (1000:ℝ),
      ∀ (G : ℝ → ℝ) (T P R : ℝ) (a b N : ℕ),
      1 ≤ T → 1 ≤ P → 1 ≤ R → 0<N → a ≤ b → P ≤ a → (b:ℝ) ≤ 2*P →
      IsApproximateModelPhaseFunction G σ 3 δ →
      P/(2*R) ≤ (N:ℝ) → (N:ℝ) ≤ P/R →
      P^2 ≤ T → P ≤ R^2 → T^2 ≤ R^7 → R^3 ≤ T → R^33 ≤ T^10 →
      T ≤ P^3 → T^2 ≤ P^2*R^4 →
      let L := modelPhaseJetLower σ 2*T/P^3
      let U := (modelPhaseJetCoefficient σ 2+1)*T/P^3/6
      let F := (modelPhaseJetCoefficient σ 3+1)*T/P^4
      F ≤ L^2/16 → F*(6*(N:ℝ)+1)^4 ≤ 1 → (3*U/2)*(6*(N:ℝ)+1)^2 ≤ 1 →
      ‖exponentialSumAt G T P a b‖^12 ≤
        K^222*(K^3*T)^ε*(1+R^3/P^2)*(1+Real.log T)^36*(P^6*T*R^3) := by
  obtain ⟨δ,hδ,C,hC,Cd,hCd,Cf,hCf,hsource⟩ :=
    exists_bourgain_model_source_global hσ hε
  obtain ⟨K,hK,hc,hu,hell,hf,hx,hChi,hCdhi,hCfhi⟩ :=
    exists_model_scale_constant hσ C Cd Cf
  refine ⟨δ,hδ,K,hK,?_⟩
  intro G T P R a b N hT hP hR hN hab ha hb hG hNlo hNhi
    hPtwo hPR hTtwo hRthree hR33 hPthree hgamma L U F hFL hsmall hquad
  let c := modelPhaseJetLower σ 2
  let u := (modelPhaseJetCoefficient σ 2+1)/6
  let lam := modelPhaseJetLower σ 3*T/P^4
  let X := (modelPhaseJetCoefficient σ 1+1)*T/P^2/2
  let Eps := (K^3*T)^ε
  let H := 1+R^3/P^2
  let Log := 1+Real.log T
  let Main := P^6*T*R^3
  have hKp : 0<K := by linarith only [hK]
  have hK1 : 1 ≤ K := by linarith only [hK]
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hPp : 0<P := zero_lt_one.trans_le hP
  have hRp : 0<R := zero_lt_one.trans_le hR
  have hNreal : 1 ≤ (N:ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hNp : 0<(N:ℝ) := zero_lt_one.trans_le hNreal
  have hLp : 0<L := by
    have hh := modelPhaseJetLower_pos hσ 2
    dsimp only [L]
    positivity
  have hUeq : U=u*T/P^3 := by dsimp only [U,u]; ring
  have hX : 0 ≤ X := by
    have hh := modelPhaseJetCoefficient_pos hσ 1
    dsimp only [X]
    positivity
  have hLlo : T/(K*P^3) ≤ L := by
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc.1 hTp.le) (pow_nonneg hPp.le 3)
    convert hh using 1
    ring
  have hlam : T/(K*P^4) ≤ lam := by
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hell.1 hTp.le) (pow_nonneg hPp.le 4)
    convert hh using 1
    ring
  have hFhi : F ≤ K*T/P^4 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hf hTp.le) (pow_nonneg hPp.le 4)
  have hXhi : X ≤ K*(T/P^2) := by
    have hh := mul_le_mul_of_nonneg_right hx (show 0 ≤ T/P^2 by positivity)
    convert hh using 1
    dsimp only [X]
    ring
  have hH : 1 ≤ H := by dsimp only [H]; linarith only [show 0 ≤ R^3/P^2 by positivity]
  have hLog : 1 ≤ Log := by dsimp only [Log]; linarith only [Real.log_nonneg hT]
  have hEps : 1 ≤ Eps := Real.one_le_rpow
    (hT.trans (le_mul_of_one_le_left hTp.le (one_le_pow₀ hK1))) hε.le
  have hMain : 0 ≤ Main := by dsimp only [Main]; positivity
  have hNT : (N:ℝ) ≤ T := hNhi.trans ((div_le_self hPp.le hR).trans
    ((show P ≤ P^2 by nlinarith only [hP]).trans hPtwo))
  have hdyadic := physical_dyadic_geometry hK hT hN hNT
  have hsrc := hsource G T P a b N hTp hPp hN hab ha hb hG hFL hsmall hquad
  extract_lets -descend J Dtail Tail budget at hsrc
  have hlift (m n : ℕ) (hm : m ≤ 210) (hn : n ≤ 24) :
      K^m*Log^n*Main ≤ K^210*Eps*H*Log^24*Main := by
    have hpos : 0 ≤ K^210*Log^24*Main :=
      mul_nonneg (mul_nonneg (pow_nonneg hKp.le 210)
        (pow_nonneg (by linarith only [hLog]) 24)) hMain
    calc
      _ ≤ K^210*Log^24*Main := by gcongr
      _ ≤ (K^210*Log^24*Main)*Eps := le_mul_of_one_le_right hpos hEps
      _ ≤ ((K^210*Log^24*Main)*Eps)*H :=
        le_mul_of_one_le_right (mul_nonneg hpos (by linarith only [hEps])) hH
      _ = _ := by ring
  have hbnd := physical_boundary_power hK hTp hPp hR hNreal hNhi hPtwo hTtwo
  have hboundary : (1+23*(N:ℝ))^12 ≤ K^210*Eps*H*Log^24*Main := by
    apply hbnd.trans
    simpa only [pow_zero,mul_one] using hlift 12 0 (by norm_num) (by norm_num)
  have ht := physical_tail_power hK hT hP hR hNreal hNlo hNhi hLlo hX hXhi
    hPtwo hRthree hR33
  have htail : Tail^12 ≤ K^210*Eps*H*Log^24*Main := by
    have hh : Tail^12 ≤ K^63*Log^12*Main := by
      simpa only [Tail,Dtail,Log,Main,Nat.cast_add,Nat.cast_one] using ht
    exact hh.trans (hlift 63 12 (by norm_num) (by norm_num))
  have hband (j : ℕ) (hj : j∈Finset.range J) :
      budget j ≤ K^210*Eps*H*Log^24*Main := by
    let Q : ℝ := (2^(j+1):ℕ)
    have hQ : 1 ≤ Q := (hdyadic.2 j hj).1
    have hQN : Q ≤ 2*(N:ℝ) := by
      simpa only [Q,Nat.cast_pow,Nat.cast_ofNat] using (hdyadic.2 j hj).2
    have hQzero : j=0 → Q=2 := by intro hj0; subst j; norm_num [Q]
    have hh := physical_source_band_budget (Q:=Q) j hK hc hu hT hP hR hNreal hQ
      hNlo hNhi hQN hlam hFhi hX hXhi hC.le hChi
      (by linarith only [hCd]) hCdhi hCf.le hCfhi hε.le
      hPtwo hPR hTtwo hRthree hR33 hPthree hgamma hQzero
    dsimp only [U] at hUeq
    simpa only [budget,hUeq,Q,u,X,lam,F,Eps,H,Log,Main,
      div_mul_eq_mul_div,one_mul] using hh
  have hsum := finite_source_budget_sum J budget hKp.le
    (by linarith only [hEps]) (by linarith only [hH]) (by linarith only [hLog])
    hMain hdyadic.1 hboundary htail hband
  exact hsrc.trans hsum

public  theorem eventually_const_log36_le_rpow {D q : ℝ} (hD : 0 ≤ D) (hq : 0<q) :
    ∀ᶠ T : ℝ in atTop, D*(1+Real.log T)^36 ≤ T^q := by
  have hl := ((isLittleO_log_rpow_rpow_atTop (36:ℝ) hq).const_mul_left (D*2^36)).eventuallyLE
  filter_upwards [hl,eventually_ge_atTop (Real.exp 1)] with T hh hT
  have hTp : 0<T := (Real.exp_pos 1).trans_le hT
  have hlog : 1 ≤ Real.log T := by
    have ht := Real.log_le_log (Real.exp_pos 1) hT
    simpa only [Real.log_exp] using ht
  have hlog0 : 0 ≤ Real.log T := zero_le_one.trans hlog
  have hp : 0 ≤ D*2^36*(Real.log T)^(36:ℝ) := by positivity
  rw [Real.norm_eq_abs,abs_of_nonneg hp,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hTp.le q)] at hh
  norm_num only [Real.rpow_ofNat] at hh
  calc
    _ ≤ D*(2*Real.log T)^36 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith only [hlog]) 36) hD
    _ = D*2^36*(Real.log T)^36 := by ring
    _ ≤ _ := by
      convert hh using 1
      norm_num

private theorem eventually_baseline_scale_majorant
    {K a δ η ε : ℝ} (hK : 1000 ≤ K) (ha : (3:ℝ)/7 ≤ a)
    (hgap : a+δ ≤ 1/2) (hδη : δ ≤ η) (hη : 0<η)
    (hηsmall : η ≤ 1/100) (hε : 0<ε) (hηε : η ≤ ε/100) :
    ∀ᶠ T : ℝ in atTop, ∀ P : ℝ, 0<P → T^(a-δ) ≤ P → P ≤ T^(a+δ) →
      let R := T^((2:ℝ)/7+η)
      K^222*(K^3*T)^η*(1+R^3/P^2)*(1+Real.log T)^36*(P^6*T*R^3) ≤
        T^(12*((13:ℝ)/84+a/2+ε)) := by
  have hKp : 0<K := by linarith only [hK]
  let D := 2*K^222*(K^3)^η
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hKp.le 222))
    (Real.rpow_nonneg (pow_nonneg hKp.le 3) η)
  filter_upwards [eventually_const_log36_le_rpow hD hη,eventually_ge_atTop (1:ℝ)]
    with T hlog hT
  intro P hP hlo hhi R
  have hTp : 0<T := zero_lt_one.trans_le hT
  obtain ⟨_hP1,_hR1,_hP2,_hPR,_hT2,_hR3,_hR33,_hP3,_hgamma,hRatio⟩ :=
    baseline_scale_geometry ha hgap hδη hη.le hηsmall hT hP hlo hhi
  have hH : 1+R^3/P^2 ≤ 2*T^(5*η) := by
    have hone : 1 ≤ T^(5*η) := Real.one_le_rpow hT (by positivity)
    linarith only [hRatio,hone]
  have hP6 : P^6 ≤ T^((a+δ)*6) := by
    calc
      _ ≤ (T^(a+δ))^6 := pow_le_pow_left₀ hP.le hhi 6
      _ = _ := (Real.rpow_mul_natCast hTp.le _ 6).symm
  have hR3 : R^3=T^(((2:ℝ)/7+η)*3) := (Real.rpow_mul_natCast hTp.le _ 3).symm
  have hprod : P^6*T*R^3 ≤ T^((a+δ)*6)*T*T^(((2:ℝ)/7+η)*3) := by
    rw [← hR3]
    gcongr
  have hEps : (K^3*T)^η=(K^3)^η*T^η := Real.mul_rpow (pow_nonneg hKp.le 3) hTp.le
  have hlog0 : 0 ≤ 1+Real.log T := by linarith only [Real.log_nonneg hT]
  calc
    _ ≤ K^222*((K^3)^η*T^η)*(2*T^(5*η))*(1+Real.log T)^36*
        (T^((a+δ)*6)*T*T^(((2:ℝ)/7+η)*3)) := by
      rw [hEps]
      gcongr
    _ = (D*(1+Real.log T)^36)*
        (T^η*T^(5*η)*T^((a+δ)*6)*T^(1:ℝ)*T^(((2:ℝ)/7+η)*3)) := by
      rw [Real.rpow_one]
      dsimp only [D]
      ring
    _ = (D*(1+Real.log T)^36)*T^(6*a+13/7+6*δ+9*η) := by
      rw [← Real.rpow_add hTp,← Real.rpow_add hTp,← Real.rpow_add hTp,← Real.rpow_add hTp]
      congr 2
      ring
    _ ≤ T^η*T^(6*a+13/7+6*δ+9*η) := mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg hTp.le _)
    _ = T^(6*a+13/7+6*δ+10*η) := by
      rw [← Real.rpow_add hTp]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT (by linarith only [hδη,hηε,hε])

                                                                        
                                                                       
                                                                         
                                                                        
                                       
theorem isExponentSumBoundNonAsymptotic_bourgain_baseline_interior
    {α : NNReal} (hα : (3:ℝ)/7 ≤ (α:ℝ)) (hαupper : (α:ℝ)<1/2) :
    IsExponentSumBoundNonAsymptotic α ((13:ℝ)/84+(α:ℝ)/2) := by
  intro ε hε σ hσ
  let η := min ((1:ℝ)/1000) (ε/100)
  have hη : 0<η := lt_min (by norm_num) (by positivity)
  have hηsmall : η ≤ 1/1000 := min_le_left _ _
  have hηε : η ≤ ε/100 := min_le_right _ _
  obtain ⟨δ₀,hδ₀,K,hK,hsource⟩ := exists_model_physical_global_bound hσ hη
  let δ := min δ₀ (min η ((1/2-(α:ℝ))/2))
  have hδ : 0<δ := lt_min hδ₀ (lt_min hη (by linarith only [hαupper]))
  have hδ0 : δ ≤ δ₀ := min_le_left _ _
  have hδη : δ ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hδgap : δ ≤ (1/2-(α:ℝ))/2 := (min_le_right _ _).trans (min_le_right _ _)
  have hgap : (α:ℝ)+δ<1/2 := by linarith only [hδgap,hαupper]
  have hentry := eventually_model_block_smallness (a:=(α:ℝ)) (δ:=δ)
    (b:=(2:ℝ)/7+η) hσ (by linarith only [hη])
    (by linarith only [hα,hδη,hη]) (by linarith only [hgap])
    (by linarith only [hα,hδη,hηsmall])
  have hmajor := eventually_baseline_scale_majorant hK hα hgap.le hδη hη
    (by linarith only [hηsmall]) hε hηε
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hentry.and hmajor)
  let C := max 1 M
  have hC : 1 ≤ C := le_max_left _ _
  have hMC : M ≤ C := le_max_right _ _
  refine ⟨δ,hδ,3,by norm_num,C,hC,?_⟩
  intro T P G a b hs
  have hT : 1 ≤ T := hC.trans hs.threshold_le_param
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hPp : 0<P := (Real.rpow_pos_of_pos hTp _).trans_le hs.rpow_sub_le_scale
  let R := T^((2:ℝ)/7+η)
  let N : ℕ := ⌊P/R⌋₊
  obtain ⟨hphysical,hbudget⟩ := hM T (hMC.trans hs.threshold_le_param)
  obtain ⟨hN,hNlo,hNhi,hFL,hsmall,hquad⟩ :=
    hphysical P hPp hs.rpow_sub_le_scale hs.scale_le_rpow_add
  obtain ⟨hP1,hR1,hPtwo,hPR,hTtwo,hRthree,hR33,hPthree,hgamma,_hRatio⟩ :=
    baseline_scale_geometry hα hgap.le hδη hη.le
      (by linarith only [hηsmall]) hT hPp hs.rpow_sub_le_scale hs.scale_le_rpow_add
  by_cases hab : a ≤ b
  · have hbound := hsource G T P R a b N hT hP1 hR1 hN hab
      hs.scale_le_start hs.end_le_two_mul_scale
      (approximateModelPhase_mono hs.isApproximateModelPhase le_rfl hδ0)
      hNlo hNhi hPtwo hPR hTtwo hRthree hR33 hPthree hgamma hFL hsmall hquad
    have hpower := hbound.trans (hbudget P hPp hs.rpow_sub_le_scale hs.scale_le_rpow_add)
    have hpower' : ‖exponentialSumAt G T P a b‖^12 ≤
        (T^((13:ℝ)/84+(α:ℝ)/2+ε))^12 := by
      rw [← Real.rpow_mul_natCast hTp.le]
      convert hpower using 1
      congr 1
      ring
    have hbound' := (pow_le_pow_iff_left₀ (norm_nonneg _)
      (Real.rpow_nonneg hTp.le _) (by norm_num : (12:ℕ) ≠ 0)).mp hpower'
    exact hbound'.trans (le_mul_of_one_le_left (Real.rpow_nonneg hTp.le _) hC)
  · have hEmpty : Finset.Icc a b=∅ := Finset.Icc_eq_empty_of_lt (lt_of_not_ge hab)
    simp only [exponentialSumAt,hEmpty,Finset.sum_empty,norm_zero]
    exact mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg hTp.le _)

                                                                     
                                             
theorem exponentSumGrowthExponent_le_bourgain_baseline_interior
    {α : NNReal} (hα : (3:ℝ)/7 ≤ (α:ℝ)) (hαupper : (α:ℝ)<1/2) :
    exponentSumGrowthExponent α ≤ (13:ℝ)/84+(α:ℝ)/2 :=
  exponentSumGrowthExponent_le_iff_nonAsymptotic.mpr
    (isExponentSumBoundNonAsymptotic_bourgain_baseline_interior hα hαupper)

open scoped ContDiff

private theorem compression_power_error {η : ℝ} (hη : 0 ≤ η) (hη₁ : η ≤ 1)
    (p : ℕ) : |(1-η)^p-1| ≤ (p : ℝ)*η := by
  have hc : 0 ≤ 1-η := by linarith
  have hp : (1-η)^p ≤ 1 := pow_le_one₀ hc (by linarith)
  rw [abs_of_nonpos (sub_nonpos.mpr hp)]
  have h := one_add_mul_le_pow (a := -η) (by linarith : -2 ≤ -η) p
  rw [← sub_eq_add_neg] at h
  linarith

private theorem compression_jet_error
    {σ δ η : ℝ} {Q p : ℕ} {G : ℝ → ℝ}
    (hσ : 0 ≤ σ) (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hη₁ : η < 1)
    (hG : IsApproximateModelPhaseFunction G σ Q δ) (hp : p ≤ Q)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    |iteratedDeriv (p+1) (fun v => G (aProcessShiftPoint η 0 v)) u -
        iteratedDeriv p (modelPhase σ) u| ≤
      δ+(modelPhaseJetCoefficient σ (p+1)+(p+1)*modelPhaseJetCoefficient σ p)*η := by
  have hv := aProcessShiftPoint_mem_Ioo hη hη₁ (by norm_num : (0:ℝ) ∈ Icc 0 1) hu
  have hc : 0 ≤ 1-η := by linarith
  have hcp : 0 ≤ (1-η)^(p+1) := pow_nonneg hc _
  have hc1 : (1-η)^(p+1) ≤ 1 := pow_le_one₀ hc (by linarith)
  have hd := sargos_iteratedDeriv_comp_affine_local
    (c := 1-η) (d := (1+0)*η)
    (fun y hy => approximateModelPhase_contDiffAt hG
      (aProcessShiftPoint_mem_Ioo hη hη₁ (by norm_num : (0:ℝ) ∈ Icc 0 1) hy))
    hu (p+1)
  change iteratedDeriv (p+1) (fun v => G (aProcessShiftPoint η 0 v)) u = _ at hd
  rw [hd]
  have herr := approximateModelPhase_iteratedDeriv_error hG hv p hp
  have hlip := iteratedDeriv_modelPhase_lipschitz hσ hv hu p
  have hdist := aProcessShiftPoint_distance hη (by norm_num : (0:ℝ) ∈ Icc 0 1)
    (Ioo_subset_Icc_self hu)
  have hb := iteratedDeriv_modelPhase_abs_le hσ hu p
  have hpow := compression_power_error hη hη₁.le (p+1)
  have h1 : |(1-η)^(p+1) *
      (iteratedDeriv (p+1) G (aProcessShiftPoint η 0 u) -
        iteratedDeriv p (modelPhase σ) (aProcessShiftPoint η 0 u))| ≤ δ := by
    rw [abs_mul,abs_of_nonneg hcp]
    exact (mul_le_mul_of_nonneg_left herr hcp).trans (mul_le_of_le_one_left hδ hc1)
  have h2 : |(1-η)^(p+1) *
      (iteratedDeriv p (modelPhase σ) (aProcessShiftPoint η 0 u) -
        iteratedDeriv p (modelPhase σ) u)| ≤ modelPhaseJetCoefficient σ (p+1)*η := by
    rw [abs_mul,abs_of_nonneg hcp]
    exact (mul_le_mul_of_nonneg_left
      (hlip.trans (mul_le_mul_of_nonneg_left hdist (modelPhaseJetCoefficient_nonneg σ _))) hcp).trans
        (mul_le_of_le_one_left (mul_nonneg (modelPhaseJetCoefficient_nonneg σ _) hη) hc1)
  have h3 : |((1-η)^(p+1)-1)*iteratedDeriv p (modelPhase σ) u| ≤
      (p+1)*modelPhaseJetCoefficient σ p*η := by
    rw [abs_mul]
    have hh := mul_le_mul hpow hb (abs_nonneg _) (by positivity : 0 ≤ ((p+1:ℕ):ℝ)*η)
    push_cast at hh
    nlinarith only [hh]
  calc
    _ = |(1-η)^(p+1) *
        (iteratedDeriv (p+1) G (aProcessShiftPoint η 0 u) -
          iteratedDeriv p (modelPhase σ) (aProcessShiftPoint η 0 u)) +
        (1-η)^(p+1) * (iteratedDeriv p (modelPhase σ) (aProcessShiftPoint η 0 u) -
          iteratedDeriv p (modelPhase σ) u) +
        ((1-η)^(p+1)-1)*iteratedDeriv p (modelPhase σ) u| := by
      congr 1
      change (1-η)^(p+1)*iteratedDeriv (p+1) G (aProcessShiftPoint η 0 u)-_ = _
      ring
    _ ≤ _ := by
      exact (abs_add_le _ _).trans
        (add_le_add ((abs_add_le _ _).trans (add_le_add h1 h2)) h3) |>.trans_eq (by ring)

private theorem compression_model_phase {σ : ℝ} (hσ : 0 ≤ σ) (Q : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (G : ℝ → ℝ) (δ η : ℝ),
      0 ≤ δ → 0 ≤ η → η < 1 →
      IsApproximateModelPhaseFunction G σ Q δ →
      IsApproximateModelPhaseFunction (fun v => G (aProcessShiftPoint η 0 v)) σ Q (δ+K*η) := by
  let B : ℕ → ℝ := fun p =>
    modelPhaseJetCoefficient σ (p+1)+(p+1)*modelPhaseJetCoefficient σ p
  have hB (p : ℕ) : 0 ≤ B p := by
    dsimp [B]
    exact add_nonneg (modelPhaseJetCoefficient_nonneg σ _) (mul_nonneg
      (by positivity) (modelPhaseJetCoefficient_nonneg σ _))
  refine ⟨1+∑ p ∈ Finset.range (Q+1), B p, ?_, ?_⟩
  · have hh := Finset.sum_nonneg (s := Finset.range (Q+1)) (fun p _ => hB p)
    linarith
  intro G δ η hδ hη hη₁ hG
  apply approximateModelPhase_of_interior_bounds
  · apply hG.1.comp (by unfold aProcessShiftPoint; fun_prop)
    intro u hu
    exact aProcessShiftPoint_mem_Icc hη hη₁.le (by norm_num : (0:ℝ) ∈ Icc 0 1) hu
  · intro u hu p hp
    have hb : B p ≤ 1+∑ j ∈ Finset.range (Q+1), B j := by
      have hh := Finset.single_le_sum (s := Finset.range (Q+1)) (f := B)
        (fun j _ => hB j) (Finset.mem_range.mpr (by omega : p < Q+1))
      linarith
    exact (compression_jet_error hσ hδ hη hη₁ hG hp hu).trans
      (add_le_add_right (mul_le_mul_of_nonneg_right hb hη) δ)


private theorem residue_core_bound {h r a b : ℕ} {P B : ℝ} {f : ℕ → ℂ}
    (hh : 0 < h) (hr : r < h) (hB : 0 ≤ B)
    (ha : P ≤ (a : ℝ))
    (hbound : ∀ c d : ℕ, (P-r)/(h:ℝ) ≤ c → (d:ℝ) ≤ 2*((P-r)/(h:ℝ)) →
      ‖∑ m ∈ Finset.Icc c d, f (h*m+r)‖ ≤ B) :
    ‖∑ n ∈ (Finset.Icc a b).filter (fun n => n%h=r ∧ (n:ℝ) ≤ 2*P-r), f n‖ ≤ B := by
  classical
  let S := (Finset.Icc a b).filter (fun n => n%h=r ∧ (n:ℝ) ≤ 2*P-r)
  change ‖∑ n ∈ S, f n‖ ≤ B
  by_cases hS : S.Nonempty
  · let l := S.min' hS
    let u := S.max' hS
    have hl : l ∈ S := Finset.min'_mem _ _
    have hu : u ∈ S := Finset.max'_mem _ _
    have hlp := Finset.mem_filter.mp hl
    have hup := Finset.mem_filter.mp hu
    have hid {n : ℕ} (hn : n ∈ S) : h*(n/h)+r=n := by
      have hm := (Finset.mem_filter.mp hn).2.1
      have hd := Nat.mod_add_div n h
      omega
    have hlid := hid hl
    have huid := hid hu
    have hreal : (0:ℝ) < h := by exact_mod_cast hh
    have hcl : (P-r)/(h:ℝ) ≤ (l/h:ℕ) := by
      apply (div_le_iff₀ hreal).mpr
      have hal : (a:ℝ) ≤ l := by exact_mod_cast (Finset.mem_Icc.mp hlp.1).1
      have hi : (h:ℝ)*(l/h:ℕ)+r=l := by exact_mod_cast hlid
      nlinarith
    have hdu : ((u/h:ℕ):ℝ) ≤ 2*((P-r)/(h:ℝ)) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hreal).mpr
      have hi : (h:ℝ)*(u/h:ℕ)+r=u := by exact_mod_cast huid
      nlinarith [hup.2.2]
    have he : (∑ m ∈ Finset.Icc (l/h) (u/h), f (h*m+r)) = ∑ n ∈ S, f n := by
      apply Finset.sum_bij (fun m _ => h*m+r)
      · intro m hm
        have hm' := Finset.mem_Icc.mp hm
        have hlo := Nat.mul_le_mul_left h hm'.1
        have hhi := Nat.mul_le_mul_left h hm'.2
        have hlm : l ≤ h*m+r := by omega
        have hmu : h*m+r ≤ u := by omega
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hlp.1).1.trans hlm,
          hmu.trans (Finset.mem_Icc.mp hup.1).2⟩, ?_, ?_⟩
        · simp [Nat.add_mod,Nat.mod_eq_of_lt hr]
        · have hn : ((h*m+r:ℕ):ℝ) ≤ u := by exact_mod_cast hmu
          exact hn.trans hup.2.2
      · intro m hm k hk heq
        exact Nat.eq_of_mul_eq_mul_left hh (Nat.add_right_cancel heq)
      · intro n hn
        refine ⟨n/h,Finset.mem_Icc.mpr ⟨?_,?_⟩,hid hn⟩
        · exact Nat.div_le_div_right (Finset.min'_le _ _ hn)
        · exact Nat.div_le_div_right (Finset.le_max' _ _ hn)
      · intro m hm
        rfl
    rw [← he]
    exact hbound _ _ hcl hdu
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simpa only [he,Finset.sum_empty,norm_zero] using hB

private theorem residue_upper_tail_card {h r a b : ℕ} {P : ℝ}
    (hh : 0 < h) (hr : r < h) (hb : (b:ℝ) ≤ 2*P) :
    ((Finset.Icc a b).filter (fun n => n%h=r ∧ ¬ (n:ℝ) ≤ 2*P-r)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro n hn m hm
  have hnp := Finset.mem_filter.mp hn
  have hmp := Finset.mem_filter.mp hm
  have hnup : (n:ℝ) ≤ 2*P :=
    (by exact_mod_cast (Finset.mem_Icc.mp hnp.1).2 : (n:ℝ) ≤ b).trans hb
  have hmup : (m:ℝ) ≤ 2*P :=
    (by exact_mod_cast (Finset.mem_Icc.mp hmp.1).2 : (m:ℝ) ≤ b).trans hb
  have hnd : h*(n/h)+r=n := by
    have he := Nat.mod_add_div n h
    omega
  have hmd : h*(m/h)+r=m := by
    have he := Nat.mod_add_div m h
    omega
  have hnr : (h:ℝ)*(n/h:ℕ)+r=n := by exact_mod_cast hnd
  have hmr : (h:ℝ)*(m/h:ℕ)+r=m := by exact_mod_cast hmd
  have hrr : (r:ℝ) < h := by exact_mod_cast hr
  have hpos : (0:ℝ) < h := by exact_mod_cast hh
  have heq : n/h=m/h := by
    apply le_antisymm
    · by_contra hnle
      have hi : ((m/h:ℕ):ℝ)+1 ≤ (n/h:ℕ) := by exact_mod_cast (by omega : m/h+1 ≤ n/h)
      have hnlo := lt_of_not_ge hnp.2.2
      have hmlo := lt_of_not_ge hmp.2.2
      nlinarith
    · by_contra hmle
      have hi : ((n/h:ℕ):ℝ)+1 ≤ (m/h:ℕ) := by exact_mod_cast (by omega : n/h+1 ≤ m/h)
      have hnlo := lt_of_not_ge hnp.2.2
      have hmlo := lt_of_not_ge hmp.2.2
      nlinarith
  rw [heq] at hnd
  omega

private theorem residue_interval_sum_bound {h a b : ℕ} {P B : ℝ} {f : ℕ → ℂ}
    (hh : 0 < h) (hB : 0 ≤ B) (ha : P ≤ (a:ℝ)) (hb : (b:ℝ) ≤ 2*P)
    (hf : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (hbound : ∀ r < h, ∀ c d : ℕ, (P-r)/(h:ℝ) ≤ c →
      (d:ℝ) ≤ 2*((P-r)/(h:ℝ)) →
      ‖∑ m ∈ Finset.Icc c d, f (h*m+r)‖ ≤ B) :
    ‖∑ n ∈ Finset.Icc a b, f n‖ ≤ (h:ℝ)*(B+1) := by
  classical
  have hpart := Finset.sum_fiberwise_of_maps_to
    (s := Finset.Icc a b) (t := Finset.range h) (g := fun n => n%h)
    (fun n _ => Finset.mem_range.mpr (Nat.mod_lt n hh)) f
  rw [← hpart]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ r ∈ Finset.range h, (B+1) := by
      apply Finset.sum_le_sum
      intro r hr
      have hrc : r < h := Finset.mem_range.mp hr
      have hcore := residue_core_bound (b := b) hh hrc hB ha (hbound r hrc)
      have hcard := residue_upper_tail_card hh hrc hb (a := a)
      let S : Finset ℕ := (Finset.Icc a b).filter (fun n => n%h=r)
      have he := Finset.sum_filter_add_sum_filter_not S (fun n : ℕ => (n:ℝ) ≤ 2*P-r) f
      have htail : ‖∑ n ∈ S.filter (fun n : ℕ => ¬ (n:ℝ) ≤ 2*P-r), f n‖ ≤ 1 := by
        refine (norm_sum_le _ _).trans ?_
        calc
          _ ≤ ∑ n ∈ S.filter (fun n : ℕ => ¬ (n:ℝ) ≤ 2*P-r), (1:ℝ) :=
            Finset.sum_le_sum (fun n _ => hf n)
          _ = ((S.filter (fun n : ℕ => ¬ (n:ℝ) ≤ 2*P-r)).card:ℝ) := by simp
          _ ≤ 1 := by
            have hc : (S.filter (fun n : ℕ => ¬ (n:ℝ) ≤ 2*P-r)).card ≤ 1 := by
              simpa only [S,Finset.filter_filter] using hcard
            exact_mod_cast hc
      have hc : ‖∑ n ∈ S.filter (fun n : ℕ => (n:ℝ) ≤ 2*P-r), f n‖ ≤ B := by
        simpa only [S,Finset.filter_filter] using hcore
      change ‖∑ n ∈ S, f n‖ ≤ B+1
      rw [← he]
      exact (norm_add_le _ _).trans (add_le_add hc htail)
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]



private theorem endpoint_residue_scales
    {T P q δ δs K : ℝ} (hT : 1 ≤ T) (hq : 0 ≤ q)
    (hδs : 0 < δs) (hδ : δ ≤ δs/2) (hK : 1 ≤ K)
    (hPlo : T^((1:ℝ)/2-δ) ≤ P) (hPhi : P ≤ T^((1:ℝ)/2+δ))
    (hsize : 8*T^q ≤ T^((1:ℝ)/2-δ))
    (habsorb : 4*T^((1:ℝ)/2-δs) ≤ T^((1:ℝ)/2-δ))
    (hjet : (4*K/δs)*T^q ≤ T^((1:ℝ)/2-δ)) :
    1 ≤ ⌈T^q⌉₊ ∧ (⌈T^q⌉₊:ℝ) ≤ 2*T^q ∧ ∀ r < ⌈T^q⌉₊,
      0 ≤ (r:ℝ)/P ∧ (r:ℝ)/P < 1 ∧
      T^((1:ℝ)/2-q-δs) ≤ (P-r)/(⌈T^q⌉₊:ℝ) ∧
      (P-r)/(⌈T^q⌉₊:ℝ) ≤ T^((1:ℝ)/2-q+δs) ∧
      δ+K*((r:ℝ)/P) ≤ δs := by
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hz : 1 ≤ T^q := Real.one_le_rpow hT hq
  have hzp : 0 < T^q := zero_lt_one.trans_le hz
  have hMlo : T^q ≤ (⌈T^q⌉₊:ℝ) := Nat.le_ceil _
  have hMhi : (⌈T^q⌉₊:ℝ) ≤ 2*T^q := by
    have hh := Nat.ceil_lt_add_one hzp.le
    linarith
  have hMpos : (0:ℝ) < ⌈T^q⌉₊ := hzp.trans_le hMlo
  have hPp : 0 < P := (Real.rpow_pos_of_pos hTp _).trans_le hPlo
  refine ⟨Nat.one_le_ceil_iff.mpr hzp,hMhi,?_⟩
  intro r hr
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg _
  have hrM : (r:ℝ) < ⌈T^q⌉₊ := by exact_mod_cast hr
  have hrP : (r:ℝ) < P := by linarith
  have hrhalf : (r:ℝ) ≤ P/2 := by linarith
  refine ⟨div_nonneg hr0 hPp.le,(div_lt_one hPp).mpr hrP,?_,?_,?_⟩
  · apply (le_div_iff₀ hMpos).mpr
    have he : T^((1:ℝ)/2-q-δs)*T^q = T^((1:ℝ)/2-δs) := by
      rw [← Real.rpow_add hTp]
      congr 1
      ring
    have hh := mul_le_mul_of_nonneg_left hMhi (Real.rpow_nonneg hTp.le ((1:ℝ)/2-q-δs))
    have he' : T^((1:ℝ)/2-q-δs)*(2*T^q) = 2*T^((1:ℝ)/2-δs) := by
      calc
        _ = 2*(T^((1:ℝ)/2-q-δs)*T^q) := by ring
        _ = _ := by rw [he]
    rw [he'] at hh
    linarith
  · apply (div_le_iff₀ hMpos).mpr
    have hdd : δ ≤ δs := by linarith
    have hphi : P ≤ T^((1:ℝ)/2+δs) :=
      hPhi.trans (Real.rpow_le_rpow_of_exponent_le hT (by linarith))
    have he : T^((1:ℝ)/2-q+δs)*T^q = T^((1:ℝ)/2+δs) := by
      rw [← Real.rpow_add hTp]
      congr 1
      ring
    have hh := mul_le_mul_of_nonneg_left hMlo (Real.rpow_nonneg hTp.le ((1:ℝ)/2-q+δs))
    rw [he] at hh
    linarith
  · have hj : 4*K*T^q ≤ δs*P := by
      have h := hjet.trans hPlo
      have hx : 4*K/δs*T^q = (4*K*T^q)/δs := by ring
      rw [hx] at h
      have hh := (div_le_iff₀ hδs).mp h
      nlinarith only [hh]
    have hm : K*(r:ℝ) ≤ K*(2*T^q) :=
      mul_le_mul_of_nonneg_left (hrM.le.trans hMhi) (zero_le_one.trans hK)
    have hh : K*(r:ℝ)/P ≤ δs/2 := by
      apply (div_le_iff₀ hPp).mpr
      nlinarith only [hj,hm]
    rw [mul_div_assoc] at hh
    linarith

private theorem endpoint_affine_sample {P : ℝ} {h r m : ℕ}
    (hP : P ≠ 0) (hr : P-(r:ℝ) ≠ 0) :
    aProcessShiftPoint ((r:ℝ)/P) 0 ((m:ℝ)/((P-r)/(h:ℝ))) =
      ((h*m+r:ℕ):ℝ)/P := by
  unfold aProcessShiftPoint
  push_cast
  field_simp
  ring



                                                                    
                                                           
theorem isExponentSumBoundNonAsymptotic_bourgain_square_root :
    IsExponentSumBoundNonAsymptotic (1/2) ((17:ℝ)/42) := by
  intro ε hε σ hσ
  let q : ℝ := min ((1:ℝ)/100) (ε/4)
  have hq : 0 < q := lt_min (by norm_num) (by positivity)
  have hqsmall : q ≤ (1:ℝ)/100 := min_le_left _ _
  have hqε : q ≤ ε/4 := min_le_right _ _
  let α : NNReal := ⟨(1:ℝ)/2-q,by linarith⟩
  have hαlo : (3:ℝ)/7 ≤ (α:ℝ) := by change (3:ℝ)/7 ≤ 1/2-q; linarith
  have hαhi : (α:ℝ) < (1:ℝ)/2 := by change (1:ℝ)/2-q < 1/2; linarith
  obtain ⟨δs,hδs,Q,hQ,C₀,hC₀,hsource⟩ :=
    isExponentSumBoundNonAsymptotic_bourgain_baseline_interior
      hαlo hαhi (ε/4) (by positivity) σ hσ
  obtain ⟨K,hK,hcompression⟩ := compression_model_phase hσ.le Q
  let δ : ℝ := min (δs/4) (q/4)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδs4 : δ ≤ δs/4 := min_le_left _ _
  have hδq : δ ≤ q/4 := min_le_right _ _
  have hgap : q < (1:ℝ)/2-δ := by linarith
  have hsize := eventually_const_mul_rpow_le_rpow (D := 8) hgap
  have habsorb := eventually_const_mul_rpow_le_rpow
    (D := 4) (a := (1:ℝ)/2-δs) (b := (1:ℝ)/2-δ) (by linarith)
  have hjet := eventually_const_mul_rpow_le_rpow (D := 4*K/δs) hgap
  obtain ⟨U,hU⟩ := eventually_atTop.mp (hsize.and (habsorb.and hjet))
  let C : ℝ := max 1 (max (4*C₀) U)
  have hC : 1 ≤ C := le_max_left _ _
  have hCC : 4*C₀ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hUC : U ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨δ,hδ,Q,hQ,C,hC,?_⟩
  intro T P G a b hs
  have hT : 1 ≤ T := hC.trans hs.threshold_le_param
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hPlo : T^((1:ℝ)/2-δ) ≤ P := by simpa using hs.rpow_sub_le_scale
  have hPhi : P ≤ T^((1:ℝ)/2+δ) := by simpa using hs.scale_le_rpow_add
  have hPp : 0 < P := (Real.rpow_pos_of_pos hTp _).trans_le hPlo
  obtain ⟨hsizeT,habsorbT,hjetT⟩ := hU T (hUC.trans hs.threshold_le_param)
  obtain ⟨hM1,hMhi,hscales⟩ := endpoint_residue_scales hT hq.le hδs
    (by linarith : δ ≤ δs/2) hK hPlo hPhi hsizeT habsorbT hjetT
  let M : ℕ := ⌈T^q⌉₊
  let B : ℝ := C₀*T^((13:ℝ)/84+(α:ℝ)/2+ε/4)
  have hB : 1 ≤ B := by
    exact one_le_mul_of_one_le_of_one_le hC₀ (Real.one_le_rpow hT (by positivity))
  have hC₀T : C₀ ≤ T := by linarith [hs.threshold_le_param]
  have hresidue (r : ℕ) (hr : r < M) (c d : ℕ)
      (hc : (P-r)/(M:ℝ) ≤ c) (hd : (d:ℝ) ≤ 2*((P-r)/(M:ℝ))) :
      ‖∑ m ∈ Finset.Icc c d, oscillatory G T P ((M*m+r:ℕ):ℝ)‖ ≤ B := by
    obtain ⟨hη,hη₁,hPrlo,hPrhi,hjetR⟩ := hscales r hr
    let Gr : ℝ → ℝ := fun v => G (aProcessShiftPoint ((r:ℝ)/P) 0 v)
    have hGr := hcompression G δ ((r:ℝ)/P) hδ.le hη hη₁ hs.isApproximateModelPhase
    have hGr' : IsApproximateModelPhaseFunction Gr σ Q δs :=
      approximateModelPhase_mono hGr le_rfl hjetR
    have hPrlo' : T^((α:ℝ)-δs) ≤ (P-r)/(M:ℝ) := hPrlo
    have hPrhi' : (P-r)/(M:ℝ) ≤ T^((α:ℝ)+δs) := hPrhi
    have hsetup : IsModelPhaseSumSetupAt (α:ℝ) σ δs Q C₀ T
        ((P-r)/(M:ℝ)) Gr c d :=
      ⟨hC₀T,hPrlo',hPrhi',hGr',hc,hd⟩
    have hh := hsource T ((P-r)/(M:ℝ)) Gr c d hsetup
    have hrP : (r:ℝ) < P := (div_lt_one hPp).mp hη₁
    have he : exponentialSumAt Gr T ((P-r)/(M:ℝ)) c d =
        ∑ m ∈ Finset.Icc c d, oscillatory G T P ((M*m+r:ℕ):ℝ) := by
      unfold exponentialSumAt
      apply Finset.sum_congr rfl
      intro m hm
      unfold oscillatory
      dsimp only [Gr]
      rw [endpoint_affine_sample hPp.ne' (sub_ne_zero.mpr hrP.ne')]
    rw [he] at hh
    exact hh
  have hsum := residue_interval_sum_bound (h := M)
    (by omega : 0 < M) (zero_le_one.trans hB) hs.scale_le_start hs.end_le_two_mul_scale
    (f := fun n => oscillatory G T P n) (fun n => by simp) hresidue
  change ‖exponentialSumAt G T P a b‖ ≤ _ at hsum
  have hexp : q+((13:ℝ)/84+(α:ℝ)/2+ε/4) ≤ (17:ℝ)/42+ε := by
    change q+((13:ℝ)/84+((1:ℝ)/2-q)/2+ε/4) ≤ (17:ℝ)/42+ε
    linarith
  calc
    ‖exponentialSumAt G T P a b‖ ≤ (M:ℝ)*(B+1) := hsum
    _ ≤ (2*T^q)*(2*B) := mul_le_mul hMhi (by linarith) (by linarith) (by positivity)
    _ = 4*C₀*T^(q+((13:ℝ)/84+(α:ℝ)/2+ε/4)) := by
      rw [Real.rpow_add hTp]
      dsimp only [B]
      ring
    _ ≤ C*T^((17:ℝ)/42+ε) :=
      mul_le_mul hCC (Real.rpow_le_rpow_of_exponent_le hT hexp)
        (Real.rpow_nonneg hTp.le _) (zero_le_one.trans hC)



                                                                           
theorem exponentSumGrowthExponent_le_bourgain_baseline {α : NNReal}
    (hα : (3:ℝ)/7 ≤ (α:ℝ)) (hαupper : (α:ℝ) ≤ 1/2) :
    exponentSumGrowthExponent α ≤ (13:ℝ)/84+(α:ℝ)/2 := by
  rcases lt_or_eq_of_le hαupper with hlt|heq
  · exact exponentSumGrowthExponent_le_bourgain_baseline_interior hα hlt
  · have ha : α = (1/2:NNReal) := by
      ext
      simpa using heq
    subst α
    have hh := exponentSumGrowthExponent_le_iff_nonAsymptotic.mpr isExponentSumBoundNonAsymptotic_bourgain_square_root
    norm_num at hh ⊢
    exact hh

                                                                    

open Expdb Filter Set
open scoped ContDiff FourierTransform Topology

public  theorem fourth_coordinate_shift_error {K K' τ τ' κ δ₃ δ₄ : ℝ}
    (hκ : 0 < κ) (hK : κ ≤ |K|) (hτ' : |τ'| ≤ 1/2)
    (hthree : |K-K'| ≤ δ₃)
    (hfour : |3*K*τ/2-3*K'*τ'/2| ≤ δ₄) :
    |τ-τ'| ≤ (2*δ₄/3+δ₃/2)/κ := by
  have he : |K*τ-K'*τ'| ≤ 2*δ₄/3 := by
    have hh : |3*K*τ/2-3*K'*τ'/2| = (3/2)*|K*τ-K'*τ'| := by
      rw [show 3*K*τ/2-3*K'*τ'/2=(3/2)*(K*τ-K'*τ') by ring,abs_mul]
      norm_num
    rw [hh] at hfour
    linarith
  have hδ₃ : 0 ≤ δ₃ := (abs_nonneg _).trans hthree
  have hprod : |(K'-K)*τ'| ≤ δ₃/2 := by
    rw [abs_mul,abs_sub_comm]
    have hh := mul_le_mul hthree hτ' (abs_nonneg _) hδ₃
    nlinarith only [hh]
  have ht : |K| * |τ-τ'| ≤ 2*δ₄/3+δ₃/2 := by
    calc
      _ = |(K*τ-K'*τ')+(K'-K)*τ'| := by
        rw [← abs_mul]
        congr 1
        ring
      _ ≤ |K*τ-K'*τ'|+|(K'-K)*τ'| := abs_add_le _ _
      _ ≤ _ := add_le_add he hprod
  apply (le_div_iff₀ hκ).mpr
  have hh := mul_le_mul_of_nonneg_right hK (abs_nonneg (τ-τ'))
  nlinarith only [ht,hh]

private theorem joint_linear_resonance
    (R R' b b' : ℤ) {q q' ℓ ℓ' τ τ' D δ₁ δ₂ : ℝ}
    (hq : q ≠ 0) (hq' : q' ≠ 0)
    (hτ' : |τ'| ≤ 1/2) (hg : |(R:ℝ)/q| ≤ 1)
    (hb : (b:ℝ)-q*ℓ=2*τ) (hb' : (b':ℝ)-q'*ℓ'=2*τ')
    (htau : |τ-τ'| ≤ D)
    (hfirst : |Int.fract (-(R:ℝ)*b/q)-Int.fract (-(R':ℝ)*b'/q')| ≤ δ₁)
    (hsecond : |(R:ℝ)/q-(R':ℝ)/q'| ≤ δ₂) :
    ∃ u v : ℤ, |q*ℓ-q'*ℓ'-(u:ℝ)| ≤ 2*D ∧
      |-(R:ℝ)*ℓ+(R':ℝ)*ℓ'-(v:ℝ)| ≤ δ₁+2*D+δ₂ := by
  let v : ℤ := ⌊-(R:ℝ)*b/q⌋-⌊-(R':ℝ)*b'/q'⌋
  have hraw : |-(R:ℝ)*b/q+(R':ℝ)*b'/q'-(v:ℝ)| ≤ δ₁ := by
    convert hfirst using 1
    dsimp only [v,Int.fract]
    push_cast
    congr 1
    ring
  refine ⟨b-b',v,?_,?_⟩
  · have he : q*ℓ-q'*ℓ'-((b-b':ℤ):ℝ) = -2*(τ-τ') := by
      push_cast
      linarith only [hb,hb']
    rw [he,abs_mul]
    norm_num
    linarith only [htau]
  · have hD : 0 ≤ D := (abs_nonneg _).trans htau
    have hδ₂ : 0 ≤ δ₂ := (abs_nonneg _).trans hsecond
    have herror : |2*((R:ℝ)/q)*(τ-τ')+
        2*((R:ℝ)/q-(R':ℝ)/q')*τ'| ≤ 2*D+δ₂ := by
      have h1 : |2*((R:ℝ)/q)*(τ-τ')| ≤ 2*D := by
        rw [abs_mul,abs_mul]
        norm_num
        have hh := mul_le_mul hg htau (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
        nlinarith only [hh]
      have h2 : |2*((R:ℝ)/q-(R':ℝ)/q')*τ'| ≤ δ₂ := by
        rw [abs_mul,abs_mul]
        norm_num
        have hh := mul_le_mul hsecond hτ' (abs_nonneg _) hδ₂
        nlinarith only [hh]
      exact (abs_add_le _ _).trans (add_le_add h1 h2)
    have he : -(R:ℝ)*ℓ+(R':ℝ)*ℓ'-(v:ℝ) =
        (-(R:ℝ)*b/q+(R':ℝ)*b'/q'-(v:ℝ))+
          (2*((R:ℝ)/q)*(τ-τ')+2*((R:ℝ)/q-(R':ℝ)/q')*τ') := by
      have hbq := (div_eq_iff hq).mpr (by linarith only [hb] : (b:ℝ)-2*τ=ℓ*q)
      have hbq' := (div_eq_iff hq').mpr (by linarith only [hb'] : (b':ℝ)-2*τ'=ℓ'*q')
      rw [← hbq,← hbq']
      ring
    rw [he]
    exact (abs_add_le _ _).trans (by linarith only [hraw,herror])

private theorem canonical_inverse_coordinate (r : ℤ) (q : ℕ) (hq : 0 < q) :
    ∃ R : ℤ, (q:ℤ) ∣ R-r ∧ (R:ℝ)/q=-Int.fract (-(r:ℝ)/q) ∧
      |(R:ℝ)/q| ≤ 1 ∧ ∀ b : ℤ,
        Int.fract (-(R:ℝ)*b/q)=Int.fract (-(r:ℝ)*b/q) := by
  let t : ℤ := ⌊-(r:ℝ)/q⌋
  let R : ℤ := r+(q:ℤ)*t
  have hqr : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have he : (R:ℝ)/q=-Int.fract (-(r:ℝ)/q) := by
    dsimp only [R,t,Int.fract]
    push_cast
    field_simp
    ring
  refine ⟨R,⟨t,by dsimp [R]; ring⟩,he,?_,?_⟩
  · rw [he,abs_neg,abs_of_nonneg (Int.fract_nonneg _)]
    exact (Int.fract_lt_one _).le
  · intro b
    have hb : -(R:ℝ)*b/q=-(r:ℝ)*b/q-((t*b:ℤ):ℝ) := by
      dsimp only [R]
      push_cast
      field_simp
      ring
    rw [hb,Int.fract_sub_intCast]

public  theorem four_coordinate_integer_constraints
    (q q' : ℕ) (r r' b b' : ℤ)
    {ℓ ℓ' K K' τ τ' κ δ₁ δ₂ δ₃ δ₄ : ℝ}
    (hq : 0 < q) (hq' : 0 < q')
    (hκ : 0 < κ) (hK : κ ≤ |K|) (hτ' : |τ'| ≤ 1/2)
    (hb : (b:ℝ)-(q:ℝ)*ℓ=2*τ) (hb' : (b':ℝ)-(q':ℝ)*ℓ'=2*τ')
    (hfirst : |Int.fract (-(r:ℝ)*b/q)-Int.fract (-(r':ℝ)*b'/q')| ≤ δ₁)
    (hsecond : |Int.fract (-(r:ℝ)/q)-Int.fract (-(r':ℝ)/q')| ≤ δ₂)
    (hthree : |K-K'| ≤ δ₃) (hfour : |3*K*τ/2-3*K'*τ'/2| ≤ δ₄) :
    let D := (2*δ₄/3+δ₃/2)/κ
    ∃ R R' u v : ℤ, (q:ℤ) ∣ R-r ∧ (q':ℤ) ∣ R'-r' ∧
      |(((q':ℤ)*R-(q:ℤ)*R':ℤ):ℝ)| ≤ δ₂*(q:ℝ)*q' ∧
      |(q:ℝ)*ℓ-(q':ℝ)*ℓ'-(u:ℝ)| ≤ 2*D ∧
      |-(R:ℝ)*ℓ+(R':ℝ)*ℓ'-(v:ℝ)| ≤ δ₁+2*D+δ₂ := by
  intro D
  obtain ⟨R,hRd,hR,hRabs,hRb⟩ := canonical_inverse_coordinate r q hq
  obtain ⟨R',hR'd,hR',hR'abs,hR'b⟩ := canonical_inverse_coordinate r' q' hq'
  have hqr : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hq'r : (q':ℝ) ≠ 0 := by exact_mod_cast hq'.ne'
  have htau : |τ-τ'| ≤ D := fourth_coordinate_shift_error hκ hK hτ' hthree hfour
  have hsecond' : |(R:ℝ)/q-(R':ℝ)/q'| ≤ δ₂ := by
    rw [hR,hR',neg_sub_neg,abs_sub_comm]
    exact hsecond
  obtain ⟨u,v,hu,hv⟩ := joint_linear_resonance R R' b b' (δ₁ := δ₁) hqr hq'r hτ' hRabs
    hb hb' htau (by rw [hRb,hR'b]; exact hfirst) hsecond'
  refine ⟨R,R',u,v,hRd,hR'd,?_,hu,hv⟩
  have he : (((q':ℤ)*R-(q:ℤ)*R':ℤ):ℝ) =
      (q:ℝ)*q'*((R:ℝ)/q-(R':ℝ)/q') := by
    push_cast
    field_simp
  rw [he,abs_mul,abs_of_nonneg (by positivity : 0 ≤ (q:ℝ)*q')]
  have hh := mul_le_mul_of_nonneg_left hsecond' (by positivity : 0 ≤ (q:ℝ)*q')
  nlinarith only [hh]

public  theorem dual_coefficient_lower
    {μ U q Q : ℝ} (hμ : 0 < μ) (hq : 0 < q)
    (hμU : μ ≤ U) (hqQ : q ≤ Q) :
    1/Real.sqrt (U*Q^3) ≤ |-2*μ*(Real.sqrt (2/(3*μ*q)))^3| := by
  let K := -2*μ*(Real.sqrt (2/(3*μ*q)))^3
  have hU : 0 < U := hμ.trans_le hμU
  have hQ : 0 < Q := hq.trans_le hqQ
  have hroot := Real.sq_sqrt (by positivity : 0 ≤ 2/(3*μ*q))
  have hKsq : K^2*(μ*q^3)=32/27 := by
    dsimp only [K]
    calc
      _ = 4*μ^2*((Real.sqrt (2/(3*μ*q)))^2)^3*(μ*q^3) := by ring
      _ = 4*μ^2*(2/(3*μ*q))^3*(μ*q^3) := by rw [hroot]
      _ = _ := by field_simp; ring
  have hscale : μ*q^3 ≤ U*Q^3 := by gcongr
  have hsq : (abs K*Real.sqrt (U*Q^3))^2 ≥ 32/27 := by
    rw [mul_pow,sq_abs,Real.sq_sqrt (by positivity : 0 ≤ U*Q^3)]
    exact hKsq ▸ mul_le_mul_of_nonneg_left hscale (sq_nonneg K)
  have hpos : 0 ≤ abs K*Real.sqrt (U*Q^3) := by positivity
  have hone : 1 ≤ abs K*Real.sqrt (U*Q^3) := by nlinarith only [hsq,hpos]
  exact (div_le_iff₀ (Real.sqrt_pos.mpr (by positivity : 0 < U*Q^3))).mpr hone

-- Generated closures: source context is replayed in the next part.
end TaoTrudgianYang2025
end
end
