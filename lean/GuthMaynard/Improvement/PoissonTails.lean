module
public import GuthMaynard.Improvement.SmoothingFourier
public import MathCollab.Density.Packing

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped SchwartzMap FourierTransform
namespace GuthMaynard.Improvement

/-- A uniform shifted lattice majorant, reusing the audited packing estimate. -/
theorem shifted_lattice_decay (α : ℝ) :
    Summable (fun n : ℤ => 1/(1+|(n:ℝ)-α|)^2) ∧
    (∑' n : ℤ, 1/(1+|(n:ℝ)-α|)^2) ≤ MathCollab.Density.separationMass := by
  let q := ⌊-α⌋
  let F : ℤ → ℝ := fun n => 4/(1+|(n:ℝ)|)^2
  have hs : Summable (fun n : ℤ => F (n+q)) :=
    (Equiv.addRight q).summable_iff.mpr MathCollab.Density.summable_separation_majorant
  have hb (n : ℤ) : 1/(1+|(n:ℝ)-α|)^2 ≤ F (n+q) := by
    simpa [F, q, sub_eq_add_neg, Int.floor_intCast_add] using
      MathCollab.Density.decay_le_floor_majorant ((n:ℝ)-α)
  have hi := hs.of_nonneg_of_le (fun n => by positivity) hb
  refine ⟨hi, (hi.tsum_le_tsum hb hs).trans_eq ?_⟩
  exact (Equiv.addRight q).tsum_eq F

theorem schwartz_fourier_one_add_bound (ψ : 𝓢(ℝ, ℂ)) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, (1+|x|)^p * ‖𝓕 (ψ:ℝ→ℂ) x‖ ≤ C := by
  let C := 2^p * (Finset.Iic (p,0)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) (𝓕 ψ)
  refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
    (m := (p,0)) (k := p) (n := 0) le_rfl le_rfl (𝓕 ψ) x
  have h' : (1+|x|)^p * ‖𝓕 (ψ:ℝ→ℂ) x‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, SchwartzMap.fourier_coe] using h
  exact h'.trans (le_max_right _ _)

def poissonRemainder (ψ : ℝ → ℂ) (R α H : ℝ) (n : ℤ) : ℂ :=
  if H < |R*((n:ℝ)-α)| then 𝓕 ψ (R*((n:ℝ)-α)) else 0

/-- A quantitative actual Poisson lattice remainder. All constants precede
R>0, every real shift alpha, and every nonnegative cutoff H.
The explicit small-spacing loss also covers the second Poisson scale S/K<1. -/
theorem uniform_poisson_remainder (ψ : 𝓢(ℝ, ℂ)) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R α H : ℝ, 0 < R → 0 ≤ H →
      Summable (fun n : ℤ => ‖poissonRemainder ψ R α H n‖) ∧
      ‖∑' n : ℤ, poissonRemainder ψ R α H n‖ ≤ C*(1+R⁻¹)^2/(1+H)^j := by
  obtain ⟨C, hC, hc⟩ := schwartz_fourier_one_add_bound ψ (j+2)
  refine ⟨C*MathCollab.Density.separationMass,
    mul_nonneg hC.le MathCollab.Density.separationMass_nonneg, ?_⟩
  intro R α H hR hH
  have hRp : 0 < R := hR
  have hb (n : ℤ) : ‖poissonRemainder ψ R α H n‖ ≤
      (C*(1+R⁻¹)^2/(1+H)^j)*(1/(1+|(n:ℝ)-α|)^2) := by
    unfold poissonRemainder
    split_ifs with hn
    · let t := |R*((n:ℝ)-α)|
      have ht0 : 0 ≤ t := abs_nonneg _
      have he : R⁻¹*t = |(n:ℝ)-α| := by
        dsimp [t]
        rw [abs_mul, abs_of_pos hRp, ← mul_assoc, inv_mul_cancel₀ hRp.ne', one_mul]
      have ht : 1+|(n:ℝ)-α| ≤ (1+R⁻¹)*(1+t) := by
        have hr0 : 0 ≤ R⁻¹ := inv_nonneg.mpr hRp.le
        nlinarith
      have hp : (1+H)^j*(1+|(n:ℝ)-α|)^2 ≤ (1+R⁻¹)^2*(1+t)^(j+2) := by
        have h1 := pow_le_pow_left₀ (by positivity : 0 ≤ 1+H)
          (by dsimp [t]; linarith : 1+H ≤ 1+t) j
        have h2 := pow_le_pow_left₀ (by positivity : 0 ≤ 1+|(n:ℝ)-α|) ht 2
        have hh := mul_le_mul h1 h2 (by positivity) (by positivity)
        simpa only [pow_add, mul_pow, mul_assoc, mul_left_comm, mul_comm] using hh
      have hh := (mul_le_mul_of_nonneg_right hp
        (norm_nonneg (𝓕 (ψ:ℝ→ℂ) (R*((n:ℝ)-α))))).trans (by
          have hh := mul_le_mul_of_nonneg_left (hc (R*((n:ℝ)-α))) (sq_nonneg (1+R⁻¹))
          simpa only [mul_assoc] using hh)
      have hh' : ‖𝓕 (ψ:ℝ→ℂ) (R*((n:ℝ)-α))‖ ≤ (C*(1+R⁻¹)^2)/((1+H)^j*(1+|(n:ℝ)-α|)^2) :=
        (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hh)
      simpa only [div_mul_div_comm, mul_one] using hh'
    · simp only [norm_zero]
      positivity
  obtain ⟨hs, hsum⟩ := shifted_lattice_decay α
  have hm := hs.mul_left (C*(1+R⁻¹)^2/(1+H)^j)
  have hi := hm.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∑' n : ℤ, ‖poissonRemainder ψ R α H n‖ := norm_tsum_le_tsum_norm hi
    _ ≤ ∑' n : ℤ, (C*(1+R⁻¹)^2/(1+H)^j)*(1/(1+|(n:ℝ)-α|)^2) := hi.tsum_le_tsum hb hm
    _ = (C*(1+R⁻¹)^2/(1+H)^j)*(∑' n : ℤ, 1/(1+|(n:ℝ)-α|)^2) := tsum_mul_left
    _ ≤ (C*(1+R⁻¹)^2/(1+H)^j)*MathCollab.Density.separationMass :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- The actual second-Poisson prefactor, with no assumption S>=K. -/
theorem second_poisson_remainder_bound (ψ : 𝓢(ℝ, ℂ)) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S K q q' u u' H : ℝ,
      0 < S → 0 < K → 0 ≤ H →
      ‖((S/K:ℝ):ℂ) * ∑' n : ℤ, poissonRemainder ψ (S/K) (q'*u'-q*u) H n‖ ≤
        C*(S/K)*(1+K/S)^2/(1+H)^j := by
  obtain ⟨C, hC, h⟩ := uniform_poisson_remainder ψ j
  refine ⟨C, hC, ?_⟩
  intro S K q q' u u' H hS hK hH
  have hp := (h (S/K) (q'*u'-q*u) H (div_pos hS hK) hH).2
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hS hK)]
  have hh := mul_le_mul_of_nonneg_left hp (div_nonneg hS.le hK.le)
  simpa only [inv_div, mul_div_assoc, mul_assoc, mul_left_comm, mul_comm] using hh

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.shifted_lattice_decay
#print axioms GuthMaynard.Improvement.schwartz_fourier_one_add_bound
#print axioms GuthMaynard.Improvement.uniform_poisson_remainder

#print axioms GuthMaynard.Improvement.second_poisson_remainder_bound
