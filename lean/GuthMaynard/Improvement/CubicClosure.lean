module
public import Mathlib

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- Actual fourth-moment split at a level, retaining the exact exceptional
square mass. This does not assume a Fourier or Plancherel theorem. -/
theorem fourth_moment_level_split {F : ℝ → ℝ} {Λ B : ℝ}
    (hF : Measurable F) (hF0 : ∀ x, 0 ≤ F x) (hB : ∀ x, F x ≤ B)
    (hΛ : 0 ≤ Λ) (h2 : Integrable (fun x => F x^2))
    (h4 : Integrable (fun x => F x^4)) :
    (∫ x in {x | F x ≤ Λ}, F x^4) ≤ Λ^2*(∫ x, F x^2) ∧
    (∫ x, F x^4) ≤ Λ^2*(∫ x, F x^2)+B^2*(∫ x in {x | Λ < F x}, F x^2) := by
  have hA : MeasurableSet {x | Λ < F x} := measurableSet_lt measurable_const hF
  have hAc : MeasurableSet {x | F x ≤ Λ} := measurableSet_le hF measurable_const
  have hpoint : ∀ x, F x^4 ≤ Λ^2*F x^2 + B^2*({x | Λ < F x}.indicator (fun x => F x^2) x) := by
    intro x
    by_cases hx : Λ < F x
    · rw [indicator_of_mem (show x ∈ {x | Λ < F x} from hx)]
      have hh : F x^2 ≤ B^2 := by nlinarith [hF0 x,hB x]
      nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg (F x)),sq_nonneg Λ]
    · rw [indicator_of_notMem (show x ∉ {x | Λ < F x} from hx),mul_zero,add_zero]
      have hh : F x^2 ≤ Λ^2 := by nlinarith [hF0 x,le_of_not_gt hx]
      nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg (F x))]
  constructor
  · calc
      _ ≤ ∫ x in {x | F x ≤ Λ}, Λ^2*F x^2 := by
        apply setIntegral_mono_on h4.integrableOn (h2.const_mul _).integrableOn hAc
        intro x hx
        change F x ≤ Λ at hx
        have hh : F x^2 ≤ Λ^2 := by nlinarith [hF0 x]
        nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg (F x))]
      _ ≤ ∫ x, Λ^2*F x^2 := setIntegral_le_integral (h2.const_mul _)
        (Filter.Eventually.of_forall (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
      _ = _ := integral_const_mul _ _
  · have hh := integral_mono h4 ((h2.const_mul (Λ^2)).add ((h2.indicator hA).const_mul (B^2))) hpoint
    simpa only [Pi.add_apply,integral_add (h2.const_mul (Λ^2)) ((h2.indicator hA).const_mul (B^2)),
      integral_const_mul,integral_indicator hA] using hh

/-- Scalar closing step of the restricted cubic argument, conditional only
on the displayed masked majorant and norm estimates. H is an arbitrary
real trace value here; no operator theorem is asserted. -/
theorem restricted_cubic_of_masked {H Q T L M M₁ A E E₀ Λ c : ℝ}
    (hQ : 0 ≤ Q) (hT : 0 ≤ T) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hM₁ : 0 ≤ M₁) (hA : 0 ≤ A) (hΛ : 0 ≤ Λ) (hc : 1 ≤ c)
    (hAM : A ≤ c*M) (hE₀ : E₀ ≤ c*Λ^2*M) (hE : E ≤ c*Λ^2*M+M₁^2*A)
    (hmasked : |H| ≤ Q*(T^2*M*Real.sqrt M + T*L*Real.sqrt M*Real.sqrt E₀ +
      Real.sqrt A*(T^2*M+T*L*Real.sqrt E))) :
    |H| ≤ Q*(1+2*c)*(T^2*M*Real.sqrt M+T*L*Λ*M+T*L*M₁*A) := by
  have hc0 : 0 ≤ c := by linarith
  have hsM := Real.sq_sqrt hM
  have hsA := Real.sq_sqrt hA
  have hsM0 := Real.sqrt_nonneg M
  have hsA0 := Real.sqrt_nonneg A
  have hsa : Real.sqrt A ≤ Real.sqrt c*Real.sqrt M := by
    rw [← Real.sqrt_mul hc0]
    exact Real.sqrt_le_sqrt hAM
  have hsc := Real.sq_sqrt hc0
  have hsc0 := Real.sqrt_nonneg c
  have he0 : Real.sqrt E₀ ≤ Real.sqrt c*Λ*Real.sqrt M := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    calc
      _ ≤ c*Λ^2*M := hE₀
      _ = _ := by rw [mul_pow,mul_pow,hsc,hsM]
  have he : Real.sqrt E ≤ Real.sqrt c*Λ*Real.sqrt M+M₁*Real.sqrt A := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    have hid : (Real.sqrt c*Λ*Real.sqrt M)^2 = c*Λ^2*M := by rw [mul_pow,mul_pow,hsc,hsM]
    have hid' : (M₁*Real.sqrt A)^2 = M₁^2*A := by rw [mul_pow,hsA]
    nlinarith [mul_nonneg (show 0 ≤ Real.sqrt c*Λ*Real.sqrt M by positivity) (show 0 ≤ M₁*Real.sqrt A by positivity)]
  have hscle : Real.sqrt c ≤ c := (Real.sqrt_le_left hc0).mpr (by nlinarith)
  have hterm0 : Real.sqrt M*Real.sqrt E₀ ≤ c*Λ*M := by
    calc
      _ ≤ Real.sqrt M*(Real.sqrt c*Λ*Real.sqrt M) := mul_le_mul_of_nonneg_left he0 hsM0
      _ = Real.sqrt c*Λ*(Real.sqrt M)^2 := by ring
      _ = Real.sqrt c*Λ*M := by rw [hsM]
      _ ≤ c*Λ*M := by gcongr
  have htermA : Real.sqrt A*M ≤ c*M*Real.sqrt M := by
    calc
      _ ≤ (Real.sqrt c*Real.sqrt M)*M := mul_le_mul_of_nonneg_right hsa hM
      _ ≤ (c*Real.sqrt M)*M := by gcongr
      _ = _ := by ring
  have htermE : Real.sqrt A*Real.sqrt E ≤ c*Λ*M+M₁*A := by
    calc
      _ ≤ Real.sqrt A*(Real.sqrt c*Λ*Real.sqrt M+M₁*Real.sqrt A) := mul_le_mul_of_nonneg_left he hsA0
      _ = Real.sqrt A*(Real.sqrt c*Λ*Real.sqrt M)+M₁*A := by nlinarith [hsA]
      _ ≤ (Real.sqrt c*Real.sqrt M)*(Real.sqrt c*Λ*Real.sqrt M)+M₁*A := by gcongr
      _ = (Real.sqrt c)^2*Λ*(Real.sqrt M)^2+M₁*A := by ring
      _ = _ := by rw [hsc,hsM]
  apply hmasked.trans
  rw [mul_assoc Q (1+2*c)]
  apply mul_le_mul_of_nonneg_left _ hQ
  nlinarith [mul_le_mul_of_nonneg_left hterm0 (mul_nonneg hT hL),
    mul_le_mul_of_nonneg_left htermA (sq_nonneg T),
    mul_le_mul_of_nonneg_left htermE (mul_nonneg hT hL),
    mul_nonneg (show 0 ≤ 2*c by positivity) (show 0 ≤ T^2*M*Real.sqrt M by positivity),
    mul_nonneg (show 0 ≤ 2*c by positivity) (show 0 ≤ T*L*M₁*A by positivity),
    show 0 ≤ T*L*Λ*M by positivity]

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.fourth_moment_level_split
#print axioms GuthMaynard.Improvement.restricted_cubic_of_masked
