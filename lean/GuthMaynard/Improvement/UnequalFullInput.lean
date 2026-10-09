import GuthMaynard.Improvement.AffineBox
import GuthMaynard.Improvement.AffineSupportTransfer
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped SchwartzMap ContDiff
namespace GuthMaynard.Improvement
open RiemannZeta.GuthMaynard

/-- Integer injection induced by g(x)=f(L(x-1)). -/
def supportIndexMap (L : ℕ) (p : ℤ × (ℤ × ℤ)) : ℤ × (ℤ × ℤ) :=
  (p.1,(L:ℤ)*p.2.1,p.2.2+(L:ℤ)*p.2.1)

theorem supportIndexMap_injective {L : ℕ} (hL : 0 < L) : Function.Injective (supportIndexMap L) := by
  intro p q hpq
  have h₁ := congrArg (fun p : ℤ × (ℤ × ℤ) => p.1) hpq
  have h₂ := congrArg (fun p : ℤ × (ℤ × ℤ) => p.2.1) hpq
  have h₃ := congrArg (fun p : ℤ × (ℤ × ℤ) => p.2.2) hpq
  dsimp only [supportIndexMap] at h₁ h₂ h₃
  have hLi : (L:ℤ) ≠ 0 := by exact_mod_cast hL.ne'
  have hq : p.2.1 = q.2.1 := mul_left_cancel₀ hLi h₂
  apply Prod.ext h₁
  apply Prod.ext hq
  rw [hq] at h₃
  exact add_right_cancel h₃

/-- No Jacobian in u: only the integer denominator and translation change. -/
theorem supportIndexMap_term {L : ℕ} (hL : 0 < L) {f g : ℝ → ℝ}
    (hg : ∀ x, g x = f ((L:ℝ)*(x-1))) (p : ℤ × (ℤ × ℤ)) (hq : p.2.1 ≠ 0) (u : ℝ) :
    gmAffineTerm f p.1 p.2.1 p.2.2 u =
      gmAffineTerm g (supportIndexMap L p).1 (supportIndexMap L p).2.1 (supportIndexMap L p).2.2 u := by
  unfold gmAffineTerm supportIndexMap
  rw [hg]
  congr 1
  push_cast
  have hLr : (L:ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hqr : (p.2.1:ℝ) ≠ 0 := by exact_mod_cast hq
  field_simp [hLr,hqr]
  ring

set_option maxHeartbeats 800000 in
/-- Full arbitrary-support finite-box estimate. The support radius and
translation constant are fixed before epsilon; T,R,K are real. The only
analytic input is the uniform supremum Fourier-decay family. -/
theorem unequal_affine_full_finite (D : ℝ → ℕ → ℝ) (hD : ∀ β n, 0 ≤ D β n)
    (L : ℕ) (hL : 0 < L) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T R K : ℝ) (f : 𝓢(ℝ, ℝ)) (S : Finset (ℤ × (ℤ × ℤ))),
      2 ≤ T → 1 ≤ K → K ≤ R → R ≤ T^4 → (∀ x, 0 ≤ f x) →
      GMAffineSupportedOn 0 L f → FourierSupFamily D T f →
      (∀ p ∈ S, InAffineBox R K C₀ p) →
      affineIndexIntegral f S ≤ C*T^ε*
        (R^2*K^4*(∫ x, f x)^2+R*K^3*(∫ x, f x^2)) := by
  have hLp : (0:ℝ) < L := by exact_mod_cast hL
  have hL1 : (1:ℝ) ≤ L := by exact_mod_cast hL
  obtain ⟨C,hC,h⟩ := affine_finite_box D hD (C₀+2*L) (by positivity) hε
  refine ⟨C*(L:ℝ)^ε*(L:ℝ)^6,by positivity,?_⟩
  intro T R K f S hT hK hKR hRT hf hs hp hbox
  have hTp : 0 < T := by linarith
  have hR : 1 ≤ R := hK.trans hKR
  obtain ⟨g,hg,hgs⟩ := canonical_affine_input f hLp (f.smooth ⊤) hs
  have hg0 : ∀ x, 0 ≤ g x := by intro x; rw [hg]; exact hf _
  have hgp := affine_input_fourier_family D hD hTp hL1 hg hp
  let S' := S.image (supportIndexMap L)
  have hbox' : ∀ p ∈ S', InAffineBox R ((L:ℝ)*K) (C₀+2*L) p := by
    intro p hpS
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hpS
    obtain ⟨hb1,hb2,hq1,hq2,hd⟩ := hbox q hq
    unfold InAffineBox supportIndexMap
    push_cast
    refine ⟨hb1,hb2,?_,?_,?_⟩
    · exact mul_le_mul_of_nonneg_left hq1 hLp.le
    · nlinarith only [mul_le_mul_of_nonneg_left hq2 hLp.le]
    · calc
        _ ≤ |(q.2.2:ℝ)|+|(L:ℝ)*(q.2.1:ℝ)| := abs_add_le _ _
        _ = |(q.2.2:ℝ)|+(L:ℝ)*(q.2.1:ℝ) := by rw [abs_of_nonneg (mul_nonneg hLp.le (by linarith only [hq1,hK]))]
        _ ≤ C₀*R+(L:ℝ)*(2*K) := add_le_add hd (mul_le_mul_of_nonneg_left hq2 hLp.le)
        _ ≤ C₀*R+(L:ℝ)*(2*R) := by gcongr
        _ = _ := by ring
  have hmax : max R ((L:ℝ)*K) ≤ (L:ℝ)*R := max_le
    (le_mul_of_one_le_left (by linarith) hL1) (mul_le_mul_of_nonneg_left hKR hLp.le)
  have hTS : T ≤ (L:ℝ)*T := le_mul_of_one_le_left hTp.le hL1
  have hS : 2 ≤ (L:ℝ)*T := hT.trans hTS
  have hLK : 1 ≤ (L:ℝ)*K := one_le_mul_of_one_le_of_one_le hL1 hK
  have hscale : max R ((L:ℝ)*K) ≤ ((L:ℝ)*T)^4 := by
    calc
      _ ≤ (L:ℝ)*R := hmax
      _ ≤ (L:ℝ)*T^4 := by gcongr
      _ ≤ (L:ℝ)^4*T^4 := by
        gcongr
        simpa only [pow_one] using pow_le_pow_right₀ hL1 (show 1 ≤ 4 by decide)
      _ = _ := by ring
  have hmain := h ((L:ℝ)*T) R ((L:ℝ)*K) g S' hS hR hLK hscale hg0 hgs hgp hbox'
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
      linarith only [hh,hK]
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
  have hw : (max R ((L:ℝ)*K))^2*((L:ℝ)*K)^4*(∫ x, g x)^2+
      max R ((L:ℝ)*K)*((L:ℝ)*K)^3*(∫ x, g x^2) ≤
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
#print axioms GuthMaynard.Improvement.supportIndexMap_injective
#print axioms GuthMaynard.Improvement.supportIndexMap_term
#print axioms GuthMaynard.Improvement.unequal_affine_full_finite
