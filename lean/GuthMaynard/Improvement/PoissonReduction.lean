module
public import Mathlib

@[expose] public section

/-! Exact Fourier/Poisson identities for the unequal-scale reduction.
Quantitative tails and divisor-counting estimates are separate obligations.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Asymptotics
open scoped FourierTransform

namespace GuthMaynard.Improvement

def phase (t : ℝ) : ℂ := Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

theorem phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  simp only [phase, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem fourier_eq_phase_integral (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 f ξ = ∫ x, phase (-ξ * x) * f x := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [show -2 * Real.pi * x * ξ = 2 * Real.pi * (-ξ * x) by ring]
  rfl

def scaledModulated (ψ : ℝ → ℂ) (R α : ℝ) (x : ℝ) : ℂ :=
  ψ (x / R) * phase (α * x)

/-- Exact scale and modulation calculation; no asymptotic loss. -/
theorem fourier_scaledModulated (ψ : ℝ → ℂ) {R : ℝ} (hR : 0 < R) (α ξ : ℝ) :
    𝓕 (scaledModulated ψ R α) ξ = R • 𝓕 ψ (R * (ξ - α)) := by
  rw [fourier_eq_phase_integral, fourier_eq_phase_integral]
  have hid : (fun x => phase (-ξ * x) * scaledModulated ψ R α x) =
      (fun x => phase (-(R * (ξ - α)) * (x / R)) * ψ (x / R)) := by
    funext x
    dsimp only [scaledModulated]
    calc
      phase (-ξ * x) * (ψ (x / R) * phase (α * x)) =
          (phase (-ξ * x) * phase (α * x)) * ψ (x / R) := by ring
      _ = phase (-ξ * x + α * x) * ψ (x / R) := by rw [phase_add]
      _ = phase (-(R * (ξ - α)) * (x / R)) * ψ (x / R) := by
        congr 2
        field_simp
        ring
  rw [hid]
  simpa only [abs_of_pos hR] using
    Measure.integral_comp_div (fun x => phase (-(R * (ξ - α)) * x) * ψ x) R

/-- A scaled Poisson formula. Continuity and both decay premises are explicit;
the formula itself is proved from mathlib Poisson summation, not postulated.
This is an identity, so its constant and all scale losses are exactly fixed. -/
theorem poisson_scaled_modulated {ψ : ℝ → ℂ} {R α b : ℝ} (hR : 0 < R)
    (hc : Continuous (scaledModulated ψ R α)) (hb : 1 < b)
    (hdecay : scaledModulated ψ R α =O[cocompact ℝ] (|·| ^ (-b)))
    (hfourier : (𝓕 (scaledModulated ψ R α)) =O[cocompact ℝ] (|·| ^ (-b))) :
    (∑' d : ℤ, ψ ((d : ℝ) / R) * phase (α * d)) =
      R • ∑' ℓ : ℤ, 𝓕 ψ (R * ((ℓ : ℝ) - α)) := by
  have h := Real.tsum_eq_tsum_fourier_of_rpow_decay hc hb hdecay hfourier 0
  simp only [zero_add] at h
  have heq : (∑' n : ℤ, 𝓕 (scaledModulated ψ R α) n *
      fourier n ((0 : ℝ) : UnitAddCircle)) =
      ∑' n : ℤ, R • 𝓕 ψ (R * ((n : ℝ) - α)) := by
    apply tsum_congr
    intro n
    simp [fourier_scaledModulated ψ hR α]
  rw [heq, tsum_const_smul''] at h
  exact h

/-- The second Poisson kernel has prefactor S/K and argument
(S/K)*(j-q'*u'+q*u), even when K differs from the slope scale. -/
theorem second_poisson_kernel {ψ : ℝ → ℂ} {S K b : ℝ} (hS : 0 < S) (hK : 0 < K)
    (q q' u u' : ℝ)
    (hc : Continuous (scaledModulated ψ (S / K) (q' * u' - q * u))) (hb : 1 < b)
    (hdecay : scaledModulated ψ (S / K) (q' * u' - q * u)
      =O[cocompact ℝ] (|·| ^ (-b)))
    (hfourier : (𝓕 (scaledModulated ψ (S / K) (q' * u' - q * u)))
      =O[cocompact ℝ] (|·| ^ (-b))) :
    (∑' ℓ : ℤ, ψ (K * ℓ / S) * phase ((q' * u' - q * u) * ℓ)) =
      (S / K) • ∑' j : ℤ, 𝓕 ψ ((S / K) * ((j : ℝ) - q' * u' + q * u)) := by
  have h := poisson_scaled_modulated (div_pos hS hK) hc hb hdecay hfourier
  have ha : ∀ x : ℝ, x / (S / K) = K * x / S := by intro x; field_simp
  have harg : ∀ x : ℝ, x - (q' * u' - q * u) = x - q' * u' + q * u := by
    intro x
    ring
  simpa only [ha, harg] using h

/-- The affine Fourier factor before the first Poisson sum.
Positive b,q are required; splitting slope signs remains separate. -/
theorem fourier_affine (f : ℝ → ℂ) {b q : ℝ} (hb : 0 < b) (hq : 0 < q)
    (d ξ : ℝ) :
    𝓕 (fun x => f ((b * x + d) / q)) ξ =
      phase (ξ * d / b) * ((q / b) • 𝓕 f (q * ξ / b)) := by
  rw [fourier_eq_phase_integral]
  rw [← integral_sub_right_eq_self
    (fun x => phase (-ξ * x) * f ((b * x + d) / q)) (d / b)]
  have hid : (fun x => phase (-ξ * (x - d / b)) * f ((b * (x - d / b) + d) / q)) =
      (fun x => phase (ξ * d / b) * (phase (-ξ * x) * f (x / (q / b)))) := by
    funext x
    have harg : (b * (x - d / b) + d) / q = x / (q / b) := by
      field_simp
      ring
    rw [harg, show -ξ * (x - d / b) = ξ * d / b + (-ξ * x) by ring, phase_add]
    ring
  rw [hid, integral_const_mul]
  have hd := fourier_scaledModulated f (div_pos hq hb) 0 ξ
  have hz : scaledModulated f (q / b) 0 = (fun x => f (x / (q / b))) := by
    funext x
    simp [scaledModulated, phase]
  rw [hz, sub_zero] at hd
  rw [← fourier_eq_phase_integral]
  rw [hd, show q / b * ξ = q * ξ / b by ring]

/-- Fourier phase multiplication preserves integrability. -/
theorem integrable_phase_mul {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    Integrable (fun x => phase (-ξ * x) * f x) := by
  apply hf.bdd_mul (c := 1)
  · have hc : Continuous (fun x : ℝ => phase (-ξ * x)) := by
      dsimp [phase]
      fun_prop
    exact hc.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x => by
      simp only [phase, Complex.norm_exp_ofReal_mul_I, le_refl])

theorem fourier_finite_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ s, Integrable (f i)) (ξ : ℝ) :
    𝓕 (fun x => ∑ i ∈ s, f i x) ξ = ∑ i ∈ s, 𝓕 (f i) ξ := by
  simp only [fourier_eq_phase_integral, Finset.mul_sum]
  exact integral_finsetSum s (fun i hi => integrable_phase_mul (hf i hi) ξ)

theorem fourier_constant_mul (f : ℝ → ℂ) (c : ℂ) (ξ : ℝ) :
    𝓕 (fun x => c * f x) ξ = c * 𝓕 f ξ := by
  simp only [fourier_eq_phase_integral, mul_left_comm (phase (-ξ * _)) c]
  exact integral_const_mul _ _

theorem integrable_affine {f : ℝ → ℂ} (hf : Integrable f)
    {b q : ℝ} (hb : 0 < b) (hq : 0 < q) (d : ℝ) :
    Integrable (fun x => f ((b * x + d) / q)) := by
  have h := (hf.comp_add_right (d / q)).comp_mul_left' (div_ne_zero hb.ne' hq.ne')
  convert h using 1
  funext x
  congr 1
  ring

/-- The actual translation sum for one positive slope and denominator.
Compact cutoff support is represented by the explicit finite support D.
The decay premises belong only to the cutoff's Poisson formula. The factor
R and affine factor q/b are retained separately, in the stated scale normalization. -/
theorem first_poisson_translation_sum {f ψ : ℝ → ℂ} {R b q p : ℝ}
    (hf : Integrable f) (hR : 0 < R) (hb : 0 < b) (hq : 0 < q)
    (D : Finset ℤ) (hsupport : ∀ d : ℤ, d ∉ D → ψ ((d : ℝ) / R) = 0)
    (ξ : ℝ)
    (hc : Continuous (scaledModulated ψ R (ξ / b))) (hp : 1 < p)
    (hdecay : scaledModulated ψ R (ξ / b) =O[cocompact ℝ] (|·| ^ (-p)))
    (hfourier : (𝓕 (scaledModulated ψ R (ξ / b))) =O[cocompact ℝ] (|·| ^ (-p))) :
    𝓕 (fun x => ∑ d ∈ D, ψ ((d : ℝ) / R) * f ((b * x + d) / q)) ξ =
      (R • ∑' ℓ : ℤ, 𝓕 ψ (R * ((ℓ : ℝ) - ξ / b))) *
        ((q / b) • 𝓕 f (q * ξ / b)) := by
  rw [fourier_finite_sum D _ (fun d _ =>
    (integrable_affine hf hb hq (d : ℝ)).const_mul (ψ ((d : ℝ) / R)))]
  simp_rw [fourier_constant_mul, fourier_affine f hb hq]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  have hfinite : (∑ d ∈ D, ψ ((d : ℝ) / R) * phase (ξ * d / b)) =
      ∑' d : ℤ, ψ ((d : ℝ) / R) * phase ((ξ / b) * d) := by
    rw [tsum_eq_sum (s := D) (fun d hd => by rw [hsupport d hd, zero_mul])]
    apply Finset.sum_congr rfl
    intro d _
    congr 2
    ring
  rw [hfinite, poisson_scaled_modulated hR hc hp hdecay hfourier]

/-- The complete first Poisson identity for finite slope/denominator boxes.
No scale comparison is used: R, b and q remain distinct in the formula. -/
theorem first_poisson_box {f ψ : ℝ → ℂ} {R p : ℝ}
    (hf : Integrable f) (hR : 0 < R) (B Q : Finset ℝ)
    (hB : ∀ b ∈ B, 0 < b) (hQ : ∀ q ∈ Q, 0 < q)
    (D : Finset ℤ) (hsupport : ∀ d : ℤ, d ∉ D → ψ ((d : ℝ) / R) = 0)
    (ξ : ℝ) (hp : 1 < p)
    (hc : ∀ b ∈ B, Continuous (scaledModulated ψ R (ξ / b)))
    (hdecay : ∀ b ∈ B, scaledModulated ψ R (ξ / b) =O[cocompact ℝ] (|·| ^ (-p)))
    (hfourier : ∀ b ∈ B, (𝓕 (scaledModulated ψ R (ξ / b))) =O[cocompact ℝ] (|·| ^ (-p))) :
    𝓕 (fun x => ∑ b ∈ B, ∑ q ∈ Q, ∑ d ∈ D,
      ψ ((d : ℝ) / R) * f ((b * x + d) / q)) ξ =
      ∑ b ∈ B, (R • ∑' ℓ : ℤ, 𝓕 ψ (R * ((ℓ : ℝ) - ξ / b))) *
        (∑ q ∈ Q, (q / b) • 𝓕 f (q * ξ / b)) := by
  have hint : ∀ b ∈ B, ∀ q ∈ Q,
      Integrable (fun x => ∑ d ∈ D, ψ ((d : ℝ) / R) * f ((b * x + d) / q)) := by
    intro b hb q hq
    exact integrable_finsetSum D (fun d _ =>
      (integrable_affine hf (hB b hb) (hQ q hq) (d : ℝ)).const_mul (ψ ((d : ℝ) / R)))
  rw [fourier_finite_sum B _ (fun b hb => integrable_finsetSum Q (hint b hb))]
  apply Finset.sum_congr rfl
  intro b hb
  rw [fourier_finite_sum Q _ (hint b hb), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  exact first_poisson_translation_sum hf hR (hB b hb) (hQ q hq)
    D hsupport ξ (hc b hb) hp (hdecay b hb) (hfourier b hb)

end GuthMaynard.Improvement

#print axioms GuthMaynard.Improvement.phase_add
#print axioms GuthMaynard.Improvement.fourier_eq_phase_integral
#print axioms GuthMaynard.Improvement.fourier_scaledModulated
#print axioms GuthMaynard.Improvement.poisson_scaled_modulated
#print axioms GuthMaynard.Improvement.second_poisson_kernel
#print axioms GuthMaynard.Improvement.fourier_affine
#print axioms GuthMaynard.Improvement.integrable_phase_mul
#print axioms GuthMaynard.Improvement.fourier_finite_sum
#print axioms GuthMaynard.Improvement.fourier_constant_mul
#print axioms GuthMaynard.Improvement.integrable_affine
#print axioms GuthMaynard.Improvement.first_poisson_translation_sum
#print axioms GuthMaynard.Improvement.first_poisson_box
