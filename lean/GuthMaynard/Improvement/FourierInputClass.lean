module
public import GuthMaynard.AffineSource.LargeValuesAffineHeight

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped SchwartzMap FourierTransform
namespace GuthMaynard.Improvement
open RiemannZeta.GuthMaynard

/-- The fixed family of supremum-normalized Fourier constants.
D is fixed before T and f; the condition is imposed only at nonzero frequency. -/
def FourierSupFamily (D : ℝ → ℕ → ℝ) (T : ℝ) (f : 𝓢(ℝ, ℝ)) : Prop :=
  ∀ β : ℝ, 0 < β → ∀ n : ℕ, ∀ ξ : ℝ, ξ ≠ 0 →
    ‖𝓕 (gmAffineComplexify f) ξ‖ ≤ D β n*T^β*(T/|ξ|)^n*
      SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f)

/-- Extension across frequency zero and conversion to the actual Fourier
Schwartz seminorm; no derivative seminorm is imposed. -/
theorem fourier_sup_family_seminorm (D : ℝ → ℕ → ℝ) (hD : ∀ β n, 0 ≤ D β n)
    {T β : ℝ} (hT : 0 ≤ T) (hβ : 0 < β) {f : 𝓢(ℝ, ℝ)}
    (hf : FourierSupFamily D T f) (n : ℕ) :
    SchwartzMap.seminorm ℝ n 0 (𝓕 (gmAffineComplexify f)) ≤
      D β n*T^β*T^n*SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f) := by
  let F := 𝓕 (gmAffineComplexify f)
  let C := D β n*T^β*T^n*SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f)
  have hclosed : IsClosed {ξ : ℝ | ‖ξ‖^n*‖F ξ‖ ≤ C} :=
    isClosed_le ((continuous_norm.pow n).mul F.continuous.norm) continuous_const
  have hsub : ({0}:Set ℝ)ᶜ ⊆ {ξ : ℝ | ‖ξ‖^n*‖F ξ‖ ≤ C} := by
    intro ξ hξ
    have hξ0 : ξ ≠ 0 := hξ
    have h := mul_le_mul_of_nonneg_left (hf β hβ n ξ hξ0) (pow_nonneg (abs_nonneg ξ) n)
    have hξa : |ξ| ≠ 0 := abs_ne_zero.mpr hξ0
    change ‖ξ‖^n*‖F ξ‖ ≤ C
    dsimp only [C,F]
    rw [Real.norm_eq_abs]
    convert h using 1
    rw [div_pow]
    field_simp [hξa]
  have hall : ∀ ξ : ℝ, ‖ξ‖^n*‖F ξ‖ ≤ C := by
    intro ξ
    exact closure_minimal hsub hclosed ((dense_compl_singleton (0:ℝ)) ξ)
  apply SchwartzMap.seminorm_le_bound' (𝕜 := ℝ) n 0 _ (by
    have hd := hD β n
    positivity)
  intro ξ
  simpa only [iteratedDeriv_zero,Real.norm_eq_abs,F,C] using hall ξ

/-- Fourier inversion bounds the source supremum by the Fourier L1 norm. -/
theorem source_sup_le_fourier_l1 (f : 𝓢(ℝ, ℝ)) :
    SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f) ≤
      ∫ ξ, ‖𝓕 (gmAffineComplexify f) ξ‖ := by
  apply SchwartzMap.seminorm_le_bound' (𝕜 := ℝ) 0 0 _
    (integral_nonneg (fun _ => norm_nonneg _))
  intro x
  simp only [pow_zero,iteratedDeriv_zero,one_mul]
  have heq : (𝓕⁻ (𝓕 (gmAffineComplexify f))) x = gmAffineComplexify f x := by
    rw [FourierTransform.fourierInv_fourier_eq]
  rw [← heq, SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm
    Real.fourierChar volume (innerₗ ℝ) _ (-x)

/-- Splitting at U gives the uniform mass/supremum interpolation used to
replace supremum-normalized decay by a height-mass Fourier profile. -/
theorem fourier_l1_le_mass_and_tail (f : 𝓢(ℝ, ℝ)) (hf : ∀ x, 0 ≤ f x)
    {U B : ℝ} (hU : 0 < U)
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ‖𝓕 (gmAffineComplexify f) ξ‖ ≤ B/|ξ|^2) :
    (∫ ξ, ‖𝓕 (gmAffineComplexify f) ξ‖) ≤ 2*U*(∫ x, f x)+2*B/U := by
  let F := 𝓕 (gmAffineComplexify f)
  have hFi : Integrable (fun ξ => ‖F ξ‖) := F.integrable.norm
  have hlo : (∫ ξ in gmAffineLowFrequencyRegion U, ‖F ξ‖) ≤ 2*U*(∫ x, f x) := by
    have hmeasure : volume (gmAffineLowFrequencyRegion U) < ⊤ := by
      rw [gmAffineLowFrequencyRegion_eq_Icc]
      exact measure_Icc_lt_top
    have hnorm := norm_setIntegral_le_of_norm_le_const hmeasure
      (f := fun ξ => ‖F ξ‖) (C := ∫ x, f x) (fun ξ _ => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        have hb : ‖F ξ‖ ≤ SchwartzMap.seminorm ℝ 0 0 F := by
          simpa only [pow_zero,iteratedDeriv_zero,one_mul] using
            SchwartzMap.le_seminorm' ℝ 0 0 F ξ
        exact hb.trans (seminorm_fourier_gmAffineComplexify_le_integral f hf))
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)),
      volume_real_gmAffineLowFrequencyRegion hU.le] at hnorm
    simpa only [mul_comm] using hnorm
  have hi : IntegrableOn (fun ξ : ℝ => B*|ξ|^(-2:ℝ)) (gmAffineHighFrequencyRegion U) :=
    (integrableOn_gmAffineHighFrequencyRegion_abs_rpow (by norm_num : (-2:ℝ) < -1) hU).const_mul B
  have hhi : (∫ ξ in gmAffineHighFrequencyRegion U, ‖F ξ‖) ≤ 2*B/U := by
    calc
      _ ≤ ∫ ξ in gmAffineHighFrequencyRegion U, B*|ξ|^(-2:ℝ) := by
        apply setIntegral_mono_on hFi.integrableOn hi (measurableSet_gmAffineHighFrequencyRegion U)
        intro ξ hξ
        have hξ0 : ξ ≠ 0 := by
          intro hz
          subst ξ
          simp only [gmAffineHighFrequencyRegion, mem_ofPred_eq, abs_zero] at hξ
          linarith
        rw [Real.rpow_neg (abs_nonneg ξ),Real.rpow_two,← div_eq_mul_inv]
        exact hdec ξ hξ0
      _ = _ := by
        rw [integral_const_mul,integral_gmAffineHighFrequencyRegion_abs_rpow (by norm_num : (-2:ℝ) < -1) hU]
        norm_num
        rw [Real.rpow_neg_one]
        ring
  have hcompl : (gmAffineLowFrequencyRegion U)ᶜ = gmAffineHighFrequencyRegion U := by
    ext ξ
    simp [gmAffineLowFrequencyRegion,gmAffineHighFrequencyRegion]
  have hsplit := integral_add_compl (measurableSet_gmAffineLowFrequencyRegion U) hFi
  rw [hcompl] at hsplit
  rw [← hsplit]
  exact add_le_add hlo hhi

/-- A uniform supremum-to-mass estimate derived from order-two Fourier
 decay. It includes zero input without dividing by mass or supremum. -/
theorem fourier_sup_le_height_mass (D : ℝ → ℕ → ℝ) (hD : ∀ β n, 0 ≤ D β n)
    {T β : ℝ} (hT : 0 < T) (hβ : 0 < β) (f : 𝓢(ℝ, ℝ))
    (hf : ∀ x, 0 ≤ f x) (hp : FourierSupFamily D T f) :
    SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f) ≤
      16*(D β 2+1)*T^β*T^2*(∫ x, f x) := by
  let S := SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f)
  let A := (D β 2+1)*T^β*T^2
  have hD2 := hD β 2
  have hA : 0 < A := by dsimp only [A]; positivity
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hdec : ∀ ξ : ℝ, ξ ≠ 0 → ‖𝓕 (gmAffineComplexify f) ξ‖ ≤ (A*S)/|ξ|^2 := by
    intro ξ hξ
    calc
      _ ≤ D β 2*T^β*(T/|ξ|)^2*S := hp β hβ 2 ξ hξ
      _ ≤ (D β 2+1)*T^β*(T/|ξ|)^2*S := by gcongr; linarith
      _ = _ := by dsimp only [A]; rw [div_pow]; ring
  have hbound := (source_sup_le_fourier_l1 f).trans
    (fourier_l1_le_mass_and_tail f hf (U := 4*A) (by positivity) hdec)
  have hcancel : 2*(A*S)/(4*A) = S/2 := by field_simp [hA.ne']; ring
  rw [hcancel] at hbound
  change S ≤ _
  have hlast : S ≤ 16*A*(∫ x, f x) := by linarith only [hbound]
  convert hlast using 1
  dsimp only [A]
  ring

/-- The fixed mass-normalized profile derived from the fixed Fourier constants. -/
def massProfile (D : ℝ → ℕ → ℝ) (β : ℝ) (n : ℕ) : ℝ :=
  16*D (β/2) n*(D (β/2) 2+1)

theorem massProfile_nonneg (D : ℝ → ℕ → ℝ) (hD : ∀ β n, 0 ≤ D β n) :
    ∀ β n, 0 ≤ massProfile D β n := by
  intro β n
  unfold massProfile
  have h1 := hD (β/2) n
  have h2 := hD (β/2) 2
  positivity

/-- Full input-class bridge: the supremum-normalized decay
implies the audited height-family premise, with one fixed profile before
all heights and all nonnegative Schwartz inputs. No smoothing-class premise. -/
theorem fourier_sup_family_to_height_mass (D : ℝ → ℕ → ℝ)
    (hD : ∀ β n, 0 ≤ D β n) {T : ℝ} (hT : 0 < T)
    (f : 𝓢(ℝ, ℝ)) (hf : ∀ x, 0 ≤ f x) (hp : FourierSupFamily D T f) :
    GMAffineHeightFourierMassFamilyAtDepth T (massProfile D) 0 f := by
  intro β hβ n
  have hhalf : 0 < β/2 := by positivity
  have hsemi := fourier_sup_family_seminorm D hD hT.le hhalf hp n
  have hsup := fourier_sup_le_height_mass D hD hT hhalf f hf hp
  have hDn := hD (β/2) n
  have hmul := mul_le_mul_of_nonneg_left hsup
    (show 0 ≤ D (β/2) n*T^(β/2)*T^n by positivity)
  have hpow : T^(β/2)*T^(β/2) = T^β := by
    rw [← Real.rpow_add hT]
    congr 1
    ring
  unfold GMAffineHeightFourierMassBound
  simp only [pow_zero,one_mul]
  refine hsemi.trans (hmul.trans_eq ?_)
  calc
    _ = (16*D (β/2) n*(D (β/2) 2+1))*(T^(β/2)*T^(β/2))*
        (T^n*T^2)*(∫ x, f x) := by ring
    _ = _ := by rw [hpow,← pow_add]; rfl

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.fourier_sup_family_seminorm
#print axioms GuthMaynard.Improvement.source_sup_le_fourier_l1
#print axioms GuthMaynard.Improvement.fourier_l1_le_mass_and_tail

#print axioms GuthMaynard.Improvement.fourier_sup_le_height_mass
#print axioms GuthMaynard.Improvement.massProfile_nonneg
#print axioms GuthMaynard.Improvement.fourier_sup_family_to_height_mass
