import GuthMaynard.Improvement.AffineScaleTransfer
import GuthMaynard.Improvement.PoissonReduction
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped SchwartzMap FourierTransform ContDiff
namespace GuthMaynard.Improvement
open RiemannZeta.GuthMaynard

/-- Exact Fourier norm under the support-normalizing affine change. -/
theorem fourier_norm_affine_input (f : ℝ → ℝ) {L : ℝ} (hL : 0 < L) (ξ : ℝ) :
    ‖𝓕 (fun x => (f (L*(x-1)) : ℂ)) ξ‖ =
      L⁻¹*‖𝓕 (fun x => (f x : ℂ)) (ξ/L)‖ := by
  let ψ : ℝ → ℂ := fun x => (f (L*x) : ℂ)
  have heq : ψ = scaledModulated (fun x => (f x : ℂ)) L⁻¹ 0 := by
    funext x
    simp [ψ,scaledModulated,phase,mul_comm]
  have ht := congrFun (VectorFourier.fourierIntegral_comp_add_right
    Real.fourierChar volume (innerₗ ℝ) ψ (-1)) ξ
  have hg : (fun x => (f (L*(x-1)) : ℂ)) = ψ ∘ (fun x => x+(-1)) := by rfl
  rw [hg]
  change ‖VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
    (ψ ∘ (fun x => x+(-1))) ξ‖ = _
  rw [ht,Circle.norm_smul]
  change ‖𝓕 ψ ξ‖ = _
  rw [heq,fourier_scaledModulated _ (inv_pos.mpr hL),norm_smul]
  simp only [sub_zero,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hL)]
  congr 2
  ring

/-- Affine changes preserve the literal source supremum. -/
theorem affine_input_sup_eq {f g : 𝓢(ℝ, ℝ)} {L : ℝ} (hL : 0 < L)
    (hg : ∀ x, g x = f (L*(x-1))) :
    SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify g) =
      SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f) := by
  apply le_antisymm
  · apply SchwartzMap.seminorm_le_bound' (𝕜 := ℝ) 0 0 _ (by positivity)
    intro x
    simpa only [pow_zero,iteratedDeriv_zero,one_mul,gmAffineComplexify_apply,hg x] using
      SchwartzMap.norm_le_seminorm (𝕜 := ℝ) (gmAffineComplexify f) (L*(x-1))
  · apply SchwartzMap.seminorm_le_bound' (𝕜 := ℝ) 0 0 _ (by positivity)
    intro x
    have hpoint := SchwartzMap.norm_le_seminorm (𝕜 := ℝ) (gmAffineComplexify g) (x/L+1)
    have heq : L*(x/L+1-1) = x := by field_simp; ring
    simpa only [pow_zero,iteratedDeriv_zero,one_mul,gmAffineComplexify_apply,hg (x/L+1),heq] using hpoint

/-- The support-normalizing change preserves the fixed Fourier family
at the enlarged height LT, without introducing function-dependent constants. -/
theorem affine_input_fourier_family (D : ℝ → ℕ → ℝ) (hD : ∀ β n, 0 ≤ D β n)
    {T L : ℝ} (hT : 0 < T) (hL : 1 ≤ L) {f g : 𝓢(ℝ, ℝ)}
    (hg : ∀ x, g x = f (L*(x-1))) (hp : FourierSupFamily D T f) :
    FourierSupFamily D (L*T) g := by
  have hLp : 0 < L := by linarith
  have hsup := affine_input_sup_eq hLp hg
  intro β hβ n ξ hξ
  have hfreq : ξ/L ≠ 0 := div_ne_zero hξ hLp.ne'
  have heq : (fun x => (g x : ℂ)) = (fun x => (f (L*(x-1)) : ℂ)) := by funext x; rw [hg]
  change ‖𝓕 (fun x => (g x : ℂ)) ξ‖ ≤ _
  rw [heq,fourier_norm_affine_input _ hLp]
  have hdec := mul_le_mul_of_nonneg_left (hp β hβ n (ξ/L) hfreq) (inv_nonneg.mpr hLp.le)
  have harg : T/|ξ/L| = (L*T)/|ξ| := by rw [abs_div,abs_of_pos hLp]; field_simp
  rw [harg] at hdec
  have hTS : T ≤ L*T := le_mul_of_one_le_left hT.le hL
  have hLi : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL
  have hd := hD β n
  calc
    _ ≤ L⁻¹*(D β n*T^β*((L*T)/|ξ|)^n*SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f)) := hdec
    _ ≤ 1*(D β n*(L*T)^β*((L*T)/|ξ|)^n*SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f)) := by
      gcongr
    _ = _ := by rw [one_mul,hsup]

/-- Every smooth input supported on [0,L] has the canonical representative.
This constructs Schwartz structure from compact support, so no extra rapid
spatial decay or derivative estimates are required. -/
theorem canonical_affine_input (f : ℝ → ℝ) {L : ℝ} (hL : 0 < L)
    (hf : ContDiff ℝ ∞ f) (hs : ∀ x, x ∉ Icc (0:ℝ) L → f x = 0) :
    ∃ g : 𝓢(ℝ, ℝ), (∀ x, g x = f (L*(x-1))) ∧ GMAffineSourceSupported g := by
  let g : ℝ → ℝ := fun x => f (L*(x-1))
  have hg : ∀ x, x ∉ Icc (1:ℝ) 2 → g x = 0 := by
    intro x hx
    apply hs
    intro hh
    apply hx
    constructor
    · have : 0 ≤ x-1 := (mul_nonneg_iff_of_pos_left hL).mp hh.1
      linarith
    · have : x-1 ≤ 1 := by nlinarith only [hh.2,hL]
      linarith
  have hc : HasCompactSupport g := HasCompactSupport.intro isCompact_Icc hg
  have hd : ContDiff ℝ ∞ g := hf.comp (by fun_prop)
  refine ⟨hc.toSchwartzMap hd,fun _ => rfl,?_⟩
  intro x hx
  exact hg x (fun hh => hx ⟨by linarith [hh.1],hh.2⟩)

/-- Exact mass and squared-L2 Jacobians for the support-normalizing change. -/
theorem affine_input_integrals (f : ℝ → ℝ) {L : ℝ} (hL : 0 < L) :
    (∫ x, f (L*(x-1))) = L⁻¹*(∫ x, f x) ∧
    (∫ x, f (L*(x-1))^2) = L⁻¹*(∫ x, f x^2) := by
  constructor
  · rw [integral_sub_right_eq_self (fun x => f (L*x)) 1,
      Measure.integral_comp_mul_left f L]
    simp [abs_of_pos hL,smul_eq_mul]
  · rw [integral_sub_right_eq_self (fun x => f (L*x)^2) 1,
      Measure.integral_comp_mul_left (fun x => f x^2) L]
    simp [abs_of_pos hL,smul_eq_mul]

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.fourier_norm_affine_input
#print axioms GuthMaynard.Improvement.affine_input_sup_eq
#print axioms GuthMaynard.Improvement.affine_input_fourier_family
#print axioms GuthMaynard.Improvement.canonical_affine_input
#print axioms GuthMaynard.Improvement.affine_input_integrals
