import GuthMaynard.Improvement.MaskedAffine
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped SchwartzMap FourierTransform ContDiff
namespace GuthMaynard.Improvement
open RiemannZeta.GuthMaynard

/-- Independent slope and denominator shells with translation bounded by the outer scale. -/
def InMixedAffineBox (B Q R C₀ : ℝ) (p : ℤ × (ℤ × ℤ)) : Prop :=
  B ≤ |(p.1:ℝ)| ∧ |(p.1:ℝ)| ≤ 2*B ∧ Q ≤ (p.2.1:ℝ) ∧
    (p.2.1:ℝ) ≤ 2*Q ∧ |(p.2.2:ℝ)| ≤ C₀*R

set_option maxHeartbeats 800000 in
theorem mixed_finite_box (D : ℝ → ℕ → ℝ) (hD : ∀ β n, 0 ≤ D β n)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T R K B Q : ℝ) (f : 𝓢(ℝ, ℝ)) (S : Finset (ℤ × (ℤ × ℤ))),
      2 ≤ T → 1 ≤ K → K ≤ R → 1 ≤ B → B ≤ R → 1 ≤ Q → Q ≤ K → R ≤ T^4 →
      (∀ x, 0 ≤ f x) → GMAffineSourceSupported f → FourierSupFamily D T f →
      (∀ p ∈ S, InMixedAffineBox B Q R C₀ p) →
      affineIndexIntegral f S ≤ C*T^ε*
        (R^2*K^4*(∫ x, f x)^2+R*K^3*(∫ x, f x^2)) := by
  obtain ⟨C,hC,h⟩ := mixed_affine_real_scales D hD (C₀+2) (by linarith) hε
  refine ⟨16*C,by positivity,?_⟩
  intro T R K B Q f S hT hK hKR hB hBR hQ hQK hRT hf hs hp hbox
  have hR : 1 ≤ R := hK.trans hKR
  let M₃ := ⌈C₀*R+1⌉₊
  have hM₃ : 0 < M₃ := Nat.ceil_pos.mpr (by positivity)
  have hM₃r : (M₃:ℝ) ≤ (C₀+2)*R := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ C₀*R+1 by positivity)
    have hBmax := le_refl R
    have hr1 : 1 ≤ R := hK.trans hKR
    have hmul := mul_le_mul_of_nonneg_left hBmax hC₀
    dsimp only [M₃]
    nlinarith only [hh,hr1,hmul]
  have h₁bound : ∀ i : Bool, (twoShell B i:ℝ) ≤ (C₀+2)*R := by
    intro i
    have hb := twoShell_le hB i
    have hbm := hBR
    have hm : 0 ≤ C₀*R := by positivity
    nlinarith only [hb,hbm,hm]
  have h₂bound : ∀ i : Bool, (twoShell Q i:ℝ) ≤ (C₀+2)*K := by
    intro i
    have hb := twoShell_le hQ i
    have hm : 0 ≤ C₀*K := by positivity
    nlinarith only [hb,hm,hQK]
  let A : Finset (Bool × Bool) := Finset.univ
  have hcover : ∀ p ∈ S, ∃ i ∈ A,
      p ∈ gmAffineIndexSet (twoShell B i.1) (twoShell Q i.2) M₃ := by
    intro p hpS
    obtain ⟨hb1,hb2,hq1,hq2,hd⟩ := hbox p hpS
    have hb := real_signed_two_shells hB hb1 hb2
    have hq := real_dyadic_two_shells hQ hq1 hq2
    have hdM : p.2.2 ∈ gmAffineCentralShell M₃ := by
      have hc : C₀*R+1 ≤ (M₃:ℝ) := Nat.le_ceil _
      have hMp : (0:ℝ) < M₃ := by exact_mod_cast hM₃
      have hadd : |(p.2.2:ℝ)| ≤ 8*(M₃:ℝ) := by linarith only [hd,hc,hMp]
      have ha := abs_le.mp hadd
      apply mem_gmAffineCentralShell.mpr
      constructor
      · exact_mod_cast ha.1
      · exact_mod_cast ha.2
    rcases hb with hb | hb <;> rcases hq with hq | hq
    · exact ⟨(false,false),Finset.mem_univ _,mem_gmAffineIndexSet.mpr ⟨hb,hq,hdM⟩⟩
    · exact ⟨(false,true),Finset.mem_univ _,mem_gmAffineIndexSet.mpr ⟨hb,hq,hdM⟩⟩
    · exact ⟨(true,false),Finset.mem_univ _,mem_gmAffineIndexSet.mpr ⟨hb,hq,hdM⟩⟩
    · exact ⟨(true,true),Finset.mem_univ _,mem_gmAffineIndexSet.mpr ⟨hb,hq,hdM⟩⟩
  have hcov := affine_integral_le_cover f hf S A (fun i => twoShell B i.1)
    (fun i => twoShell Q i.2) (fun _ => M₃)
    (fun i _ => twoShell_pos hB i.1) (fun i _ => twoShell_pos hQ i.2) hcover
  have hpoint : ∀ i ∈ A, gmAffineTransformIntegral f (twoShell B i.1) (twoShell Q i.2) M₃ ≤
      C*T^ε*(R^2*K^4*(∫ x, f x)^2+R*K^3*(∫ x, f x^2)) := by
    intro i hi
    exact h T R K f (twoShell B i.1) (twoShell Q i.2) M₃ hT hK
      hKR hRT hf hs hp (twoShell_pos hB i.1) (twoShell_pos hQ i.2) hM₃
      (h₁bound i.1) (h₂bound i.2) hM₃r
  have hsum := Finset.sum_le_sum hpoint
  have hcard : A.card = 4 := by simp [A]
  rw [Finset.sum_const,hcard] at hsum
  rw [hcard] at hcov
  norm_num only [Nat.cast_ofNat,nsmul_eq_mul] at hsum hcov
  exact hcov.trans (by nlinarith only [hsum])

set_option maxHeartbeats 800000 in
/-- Full arbitrary-support finite-box estimate. The support radius and
translation constant are fixed before epsilon; T,R,K are real. The only
analytic input is the uniform supremum Fourier-decay family. -/
theorem mixed_affine_full_finite (D : ℝ → ℕ → ℝ) (hD : ∀ β n, 0 ≤ D β n)
    (L : ℕ) (hL : 0 < L) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T R K B Q : ℝ) (f : 𝓢(ℝ, ℝ)) (S : Finset (ℤ × (ℤ × ℤ))),
      2 ≤ T → 1 ≤ K → K ≤ R → 1 ≤ B → B ≤ R → 1 ≤ Q → Q ≤ K → R ≤ T^4 → (∀ x, 0 ≤ f x) →
      GMAffineSupportedOn 0 L f → FourierSupFamily D T f →
      (∀ p ∈ S, InMixedAffineBox B Q R C₀ p) →
      affineIndexIntegral f S ≤ C*T^ε*
        (R^2*K^4*(∫ x, f x)^2+R*K^3*(∫ x, f x^2)) := by
  have hLp : (0:ℝ) < L := by exact_mod_cast hL
  have hL1 : (1:ℝ) ≤ L := by exact_mod_cast hL
  obtain ⟨C,hC,h⟩ := mixed_finite_box D hD (C₀+2*L) (by positivity) hε
  refine ⟨C*(L:ℝ)^ε*(L:ℝ)^6,by positivity,?_⟩
  intro T R K B Q f S hT hK hKR hB hBR hQ hQK hRT hf hs hp hbox
  have hTp : 0 < T := by linarith
  have hR : 1 ≤ R := hK.trans hKR
  obtain ⟨g,hg,hgs⟩ := canonical_affine_input f hLp (f.smooth ⊤) hs
  have hg0 : ∀ x, 0 ≤ g x := by intro x; rw [hg]; exact hf _
  have hgp := affine_input_fourier_family D hD hTp hL1 hg hp
  let S' := S.image (supportIndexMap L)
  have hbox' : ∀ p ∈ S', InMixedAffineBox B ((L:ℝ)*Q) ((L:ℝ)*R) (C₀+2*L) p := by
    intro p hpS
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hpS
    obtain ⟨hb1,hb2,hq1,hq2,hd⟩ := hbox q hq
    unfold InMixedAffineBox supportIndexMap
    push_cast
    refine ⟨hb1,hb2,?_,?_,?_⟩
    · exact mul_le_mul_of_nonneg_left hq1 hLp.le
    · nlinarith only [mul_le_mul_of_nonneg_left hq2 hLp.le]
    · calc
        _ ≤ |(q.2.2:ℝ)|+|(L:ℝ)*(q.2.1:ℝ)| := abs_add_le _ _
        _ = |(q.2.2:ℝ)|+(L:ℝ)*(q.2.1:ℝ) := by rw [abs_of_nonneg (mul_nonneg hLp.le (by linarith only [hq1,hQ]))]
        _ ≤ C₀*R+(L:ℝ)*(2*Q) := add_le_add hd (mul_le_mul_of_nonneg_left hq2 hLp.le)
        _ ≤ C₀*R+(L:ℝ)*(2*R) := by gcongr; exact hQK.trans hKR
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (show 0 ≤ R by linarith) hL1) (show 0 ≤ C₀+2*L by positivity)]
  have hTS : T ≤ (L:ℝ)*T := le_mul_of_one_le_left hTp.le hL1
  have hS : 2 ≤ (L:ℝ)*T := hT.trans hTS
  have hLK : 1 ≤ (L:ℝ)*K := one_le_mul_of_one_le_of_one_le hL1 hK
  have hscale' : (L:ℝ)*R ≤ ((L:ℝ)*T)^4 := by
    calc
      _ ≤ (L:ℝ)*T^4 := by gcongr
      _ ≤ (L:ℝ)^4*T^4 := by gcongr; simpa only [pow_one] using pow_le_pow_right₀ hL1 (show 1 ≤ 4 by decide)
      _ = _ := by ring
  have hLQ : 1 ≤ (L:ℝ)*Q := one_le_mul_of_one_le_of_one_le hL1 hQ
  have hmain := h ((L:ℝ)*T) ((L:ℝ)*R) ((L:ℝ)*K) B ((L:ℝ)*Q) g S'
    hS hLK (by gcongr) hB (hBR.trans (le_mul_of_one_le_left (by linarith) hL1))
    hLQ (by gcongr) hscale' hg0 hgs hgp hbox'

  have heq : affineIndexIntegral f S = affineIndexIntegral g S' := by
    unfold affineIndexIntegral
    apply integral_congr_ae
    filter_upwards with u
    dsimp only [S']
    rw [Finset.sum_image (by intro p _ q _ hpq; exact supportIndexMap_injective hL hpq)]
    congr 1
    apply Finset.sum_congr rfl
    intro p hpS
    have hq : p.2.1 ≠ 0 := by
      have hh := (hbox p hpS).2.2.1
      intro hz
      rw [hz,Int.cast_zero] at hh
      linarith only [hh,hQ]
    exact supportIndexMap_term hL hg p hq u
  have hmass := (affine_input_integrals f hLp).1
  have hL2 := (affine_input_integrals f hLp).2
  simp_rw [← hg] at hmass hL2
  have hmass0 : 0 ≤ ∫ x, f x := integral_nonneg hf
  have hgMass0 : 0 ≤ ∫ x, g x := integral_nonneg hg0
  have hf20 : 0 ≤ ∫ x, f x^2 := integral_nonneg (fun _ => sq_nonneg _)
  have hLi : (L:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL1
  have hmassle : (∫ x, g x) ≤ ∫ x, f x := by rw [hmass]; exact mul_le_of_le_one_left hmass0 hLi
  have hL2le : (∫ x, g x^2) ≤ ∫ x, f x^2 := by rw [hL2]; exact mul_le_of_le_one_left hf20 hLi
  have hw : ((L:ℝ)*R)^2*((L:ℝ)*K)^4*(∫ x, g x)^2+
      ((L:ℝ)*R)*((L:ℝ)*K)^3*(∫ x, g x^2) ≤
      (L:ℝ)^6*(R^2*K^4*(∫ x, f x)^2+R*K^3*(∫ x, f x^2)) := by
    calc
      _ ≤ ((L:ℝ)*R)^2*((L:ℝ)*K)^4*(∫ x, f x)^2+
        ((L:ℝ)*R)*((L:ℝ)*K)^3*(∫ x, f x^2) := by gcongr
      _ = (L:ℝ)^6*(R^2*K^4*(∫ x, f x)^2)+(L:ℝ)^4*(R*K^3*(∫ x, f x^2)) := by ring
      _ ≤ (L:ℝ)^6*(R^2*K^4*(∫ x, f x)^2)+(L:ℝ)^6*(R*K^3*(∫ x, f x^2)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ hL1 (show 4 ≤ 6 by decide)) (by positivity))
      _ = _ := by ring
  rw [heq]
  apply hmain.trans
  calc
    _ ≤ C*((L:ℝ)*T)^ε*((L:ℝ)^6*(R^2*K^4*(∫ x, f x)^2+R*K^3*(∫ x, f x^2))) := by gcongr
    _ = _ := by rw [Real.mul_rpow hLp.le hTp.le]; ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.mixed_finite_box
#print axioms GuthMaynard.Improvement.mixed_affine_full_finite
