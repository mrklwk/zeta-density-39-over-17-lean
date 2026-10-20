module
public import DiscreteEnergyReproduction
public import RationalLargeGcdEnergy

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment

/-- The exact remaining small-gcd cubic contribution, using the actual
integer support of the detecting polynomial and the transition N^2/T. -/
def smallGcdCubicSum (N T : ℝ) (W : Finset ℝ) : ℝ :=
  ∑ p ∈ (GuthMaynard.Improvement.sourceRatioIndices N ×ˢ
      GuthMaynard.Improvement.sourceRatioIndices N).filter
      (fun p => (pairGcd p:ℝ) < N^2/T),
    ‖∑ t ∈ W, phase (pairRatio p) t‖^3

/-- Combining the proved reproducing bridge with the proved large-gcd
estimate leaves precisely smallGcdCubicSum. This is a reduction, not the
still-open two-term additive-energy conclusion. -/
theorem discrete_energy_small_gcd_reduction {K : ℕ} (hK : 1 ≤ K)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ N : ℝ, 1 < T → 0 < N → N ≤ T →
      ∀ (a : ℕ → ℂ) (W : Finset ℝ) (V : ℝ),
      T^(((K:ℝ)+1)/(2*K+1)) ≤ W.card → (T/N)^K ≤ W.card →
      (∀ n ∈ GuthMaynard.Improvement.sourceRatioIndices N, ‖a n‖ ≤ 1) →
      0 ≤ V → (∀ t ∈ W, V ≤ ‖GuthMaynard.Improvement.boundedPolynomial N a t‖) →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (discreteAdditiveEnergy W:ℝ)*V^2 ≤
        C*(smallGcdCubicSum N T W+T^η*N*(W.card:ℝ)^3) := by
  classical
  obtain ⟨C₀,hC₀,hrepro⟩ := discrete_additive_energy_reproducing
  obtain ⟨C₁,hC₁,hlarge⟩ := large_gcd_cubic_at_transition hK hη
  refine ⟨C₀*(1+C₁),by positivity,?_⟩
  intro T t₀ N hT hN hNT a W V hR hNR ha hV hlargeW hW hsep
  let A := GuthMaynard.Improvement.sourceRatioIndices N
  let P := A ×ˢ A
  let F := fun p : ℕ × ℕ => ‖∑ t ∈ W, phase (pairRatio p) t‖^3
  have hP : ∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
      N < p.1 ∧ (p.1:ℝ) ≤ 2*N ∧ N < p.2 ∧ (p.2:ℝ) ≤ 2*N := by
    intro p hp
    obtain ⟨hp1,hp2⟩ := mem_product.mp hp
    obtain ⟨hl1,hu1⟩ := (GuthMaynard.Improvement.sourceRatioIndices_mem hN.le p.1).mp hp1
    obtain ⟨hl2,hu2⟩ := (GuthMaynard.Improvement.sourceRatioIndices_mem hN.le p.2).mp hp2
    exact ⟨by exact_mod_cast hN.trans hl1,by exact_mod_cast hN.trans hl2,hl1,hu1,hl2,hu2⟩
  have hl := hlarge T t₀ N hT hN hNT P hP W hR hNR hW hsep
  have he : (∑ p ∈ P, F p) = smallGcdCubicSum N T W+
      ∑ p ∈ P.filter (fun p => N^2/T ≤ (pairGcd p:ℝ)), F p := by
    have hh := sum_filter_add_sum_filter_not P (fun p => (pairGcd p:ℝ) < N^2/T) F
    simpa only [not_lt,smallGcdCubicSum,P,A,F] using hh.symm
  have hr := hrepro N hN a W V ha hV hlargeW hsep
  have hpair : (∑ n ∈ A, ∑ m ∈ A, ‖∑ t ∈ W, phase ((n:ℝ)/m) t‖^3) = ∑ p ∈ P, F p := by
    simp only [P,F,sum_product,pairRatio,Rat.cast_div,Rat.cast_natCast]
  rw [hpair,he] at hr
  have h0 : 0 ≤ smallGcdCubicSum N T W := sum_nonneg (fun _ _ => by positivity)
  have ht0 : 0 ≤ T^η*N*(W.card:ℝ)^3 := by positivity
  exact hr.trans (by
    have hh := mul_le_mul_of_nonneg_left hl hC₀.le
    change C₀*(smallGcdCubicSum N T W+∑ p ∈ P.filter (fun p => N^2/T ≤ (pairGcd p:ℝ)), F p) ≤ _
    dsimp only [F] at *
    nlinarith [mul_nonneg (hC₀.le) (mul_nonneg hC₁.le h0)])

end Montgomery.RationalMoment
