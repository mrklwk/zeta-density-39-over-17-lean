module
public import SmallGcdCubicEnergy

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment

/-- Exact absorption of the square-root energy term; V is strictly positive. -/
theorem discrete_energy_absorb {E A B V : ℝ} (hE : 0 ≤ E) (hV : 0 < V)
    (h : E*V^2 ≤ A*Real.sqrt E+B) :
    E ≤ A^2/V^4+2*B/V^2 := by
  have he : (V^2*Real.sqrt E)^2=V^4*E := by
    rw [mul_pow,Real.sq_sqrt hE]
    ring
  have hy : 2*A*Real.sqrt E*V^2 ≤ E*V^4+A^2 := by
    have hh := sq_nonneg (V^2*Real.sqrt E-A)
    nlinarith [he]
  have hh := mul_le_mul_of_nonneg_right h (sq_nonneg V)
  have hb : E*V^4 ≤ A^2+2*B*V^2 := by nlinarith
  calc
    E ≤ (A^2+2*B*V^2)/V^4 := (le_div_iff₀ (pow_pos hV 4)).mpr hb
    _ = _ := by field_simp

/-- The full two-term additive-energy theorem for the actual detecting
polynomial and the literal quadruple count. All Fourier, gcd, moment and
reproducing estimates are discharged, rather than theorem hypotheses. -/
theorem discrete_additive_energy_two_term {K : ℕ} (hK : 1 ≤ K)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ N : ℝ, 1 < T → 0 < N → N ≤ T →
      ∀ (a : ℕ → ℂ) (W : Finset ℝ) (V : ℝ),
      T^(((K:ℝ)+1)/(2*K+1)) ≤ W.card → (T/N)^K ≤ W.card →
      (∀ n ∈ GuthMaynard.Improvement.sourceRatioIndices N, ‖a n‖ ≤ 1) →
      0 < V → (∀ t ∈ W, V ≤ ‖GuthMaynard.Improvement.boundedPolynomial N a t‖) →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (discreteAdditiveEnergy W:ℝ) ≤
        C*T^η*(N^4*(W.card:ℝ)/V^4+N*(W.card:ℝ)^3/V^2) := by
  obtain ⟨C₀,hC₀,hreduction⟩ := discrete_energy_small_gcd_reduction hK hη
  obtain ⟨C₁,hC₁,hsmall⟩ := small_gcd_cubic_sum
  refine ⟨(C₀*C₁)^2+2*C₀,by positivity,?_⟩
  intro T t₀ N hT hN hNT a W V hR hNR ha hV hlarge hW hsep
  have hTp : 0 < T := by linarith
  have hr := hreduction T t₀ N hT hN hNT a W V hR hNR ha hV.le hlarge hW hsep
  have hs := hsmall T t₀ N hT hN W hW hsep
  have hh : (discreteAdditiveEnergy W:ℝ)*V^2 ≤
      (C₀*C₁*N^2*Real.sqrt (W.card:ℝ))*Real.sqrt (discreteAdditiveEnergy W:ℝ)+
        C₀*T^η*N*(W.card:ℝ)^3 := by
    have hmul := mul_le_mul_of_nonneg_left hs hC₀.le
    nlinarith
  have hb := discrete_energy_absorb (Nat.cast_nonneg (discreteAdditiveEnergy W)) hV hh
  have hid : (C₀*C₁*N^2*Real.sqrt (W.card:ℝ))^2 = (C₀*C₁)^2*N^4*(W.card:ℝ) := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg W.card)]
    ring
  rw [hid] at hb
  have hpow : 1 ≤ T^η := Real.one_le_rpow hT.le hη.le
  calc
    _ ≤ (C₀*C₁)^2*N^4*(W.card:ℝ)/V^4+2*(C₀*T^η*N*(W.card:ℝ)^3)/V^2 := hb
    _ ≤ (C₀*C₁)^2*T^η*N^4*(W.card:ℝ)/V^4+2*(C₀*T^η*N*(W.card:ℝ)^3)/V^2 := by
      gcongr
      nlinarith [mul_le_mul_of_nonneg_left hpow (sq_nonneg (C₀*C₁))]
    _ = (C₀*C₁)^2*(T^η*N^4*(W.card:ℝ)/V^4)+
        2*C₀*(T^η*N*(W.card:ℝ)^3/V^2) := by ring
    _ ≤ ((C₀*C₁)^2+2*C₀)*((T^η*N^4*(W.card:ℝ)/V^4)+(T^η*N*(W.card:ℝ)^3/V^2)) := by
      have h1 : 0 ≤ T^η*N^4*(W.card:ℝ)/V^4 := by positivity
      have h2 : 0 ≤ T^η*N*(W.card:ℝ)^3/V^2 := by positivity
      nlinarith [mul_nonneg (sq_nonneg (C₀*C₁)) h2,mul_nonneg hC₀.le h1]
    _ = _ := by ring

end Montgomery.RationalMoment
