module
public import GeneralCoprimeEnergy
public import RationalDifferenceEnergy

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Finset
namespace Montgomery.RationalMoment

/-- Exact gcd multiplicities are summed after the unrestricted coprime
estimate; the harmonic loss is absorbed uniformly before any data vary. -/
theorem general_pair_energy {K : ℕ} (hK : 1 ≤ K)
    {η B : ℝ} (hη : 0 < η) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ X : ℝ, 1 < T → 0 ≤ X → X ≤ B*T →
      ∀ P : Finset (ℕ × ℕ),
      (∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
        X < p.1 ∧ (p.1:ℝ) ≤ 2*X ∧ X < p.2 ∧ (p.2:ℝ) ≤ 2*X) →
      ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∑ p ∈ P, ‖∑ t ∈ W, phase (pairRatio p) t‖^2) ≤
        C*T^η*X*((W.card:ℝ)^2+X*(W.card:ℝ)^(2-1/(K:ℝ))+
          T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))) := by
  obtain ⟨C,hC,hb⟩ := coprime_dyadic_adjacent_general hK (show 0 < η/2 by positivity) hB
  let L : ℝ := 1+4^(η/2)/(η/2)
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨C*L*B^(η/2),by positivity,?_⟩
  intro T t₀ X hT hX hXT P hP W hW hsep
  have ht : 0 < T := by linarith
  have hblock : ∀ d ∈ gcdValues P,
      (∑ q ∈ reducedFiber P d, ‖∑ t ∈ W,phase (pairRatio q) t‖^2) ≤
        (C*T^(η/2)*((W.card:ℝ)^2+X*(W.card:ℝ)^(2-1/(K:ℝ))+
          T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))))*(X/d) := by
    intro d hd
    obtain ⟨p,hp,he⟩ := mem_image.mp hd
    have hd0 : 0 < d := he ▸ Nat.gcd_pos_of_pos_left _ (hP p hp).1
    have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd0
    have hdiv : X/(d:ℝ) ≤ X := div_le_self hX hd1
    have hQ : ∀ q ∈ reducedFiber P d,
        0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2 ∧
        X/d < q.1 ∧ (q.1:ℝ) ≤ 2*(X/d) ∧ X/d < q.2 ∧ (q.2:ℝ) ≤ 2*(X/d) :=
      fun q hq => (reduced_fiber_bounds hP hq).2
    have hh := hb T t₀ (X/d) hT (by positivity) (hdiv.trans hXT)
      (reducedFiber P d) hQ W hW hsep
    have hm : (X/(d:ℝ))^2 ≤ X*(X/d) := by
      have hh := mul_le_mul_of_nonneg_right hdiv (show 0 ≤ X/(d:ℝ) by positivity)
      nlinarith only [hh]
    apply hh.trans
    have hm' := mul_le_mul_of_nonneg_right hm
      (show 0 ≤ (W.card:ℝ)^(2-1/(K:ℝ)) by positivity)
    have hm'' := mul_le_mul_of_nonneg_left hm' (show 0 ≤ C*T^(η/2) by positivity)
    nlinarith only [hm'']
  have h2X : 0 ≤ 2*X := by positivity
  have hpN : ∀ p ∈ P, 0 < p.1 ∧ p.1 ≤ ⌊2*X⌋₊ := by
    intro p hp
    exact ⟨(hP p hp).1,(Nat.le_floor_iff h2X).mpr (hP p hp).2.2.2.1⟩
  have hh := pair_energy_le_log P hpN W (show 0 ≤ C*T^(η/2)*
      ((W.card:ℝ)^2+X*(W.card:ℝ)^(2-1/(K:ℝ))+
        T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))) by positivity) hX hblock
  have hBT : 1 ≤ B*T := by nlinarith
  have hN : (⌊2*X⌋₊:ℝ) ≤ 4*(B*T) := (Nat.floor_le h2X).trans (by nlinarith)
  have hl := logarithmic_height_loss hBT (show 0 < η/2 by positivity) ⌊2*X⌋₊ hN
  change 1+Real.log ⌊2*X⌋₊ ≤ L*(B*T)^(η/2) at hl
  rw [Real.mul_rpow (by linarith : 0 ≤ B) ht.le] at hl
  have hp : T^(η/2)*T^(η/2)=T^η := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  calc
    _ ≤ (C*T^(η/2)*((W.card:ℝ)^2+X*(W.card:ℝ)^(2-1/(K:ℝ))+
        T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))))*X*(1+Real.log ⌊2*X⌋₊) := hh
    _ ≤ (C*T^(η/2)*((W.card:ℝ)^2+X*(W.card:ℝ)^(2-1/(K:ℝ))+
        T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))))*X*
          (L*(B^(η/2)*T^(η/2))) := by gcongr
    _ = (C*L*B^(η/2))*(T^(η/2)*T^(η/2))*X*((W.card:ℝ)^2+
        X*(W.card:ℝ)^(2-1/(K:ℝ))+
        T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))) := by ring
    _ = _ := by rw [hp]

/-- The literal Dirichlet difference sum, with arbitrary bounded complex
coefficients, real dyadic length, bounded reflected heights and no R floor. -/
theorem general_dirichlet_difference {K : ℕ} (hK : 1 ≤ K)
    {η B : ℝ} (hη : 0 < η) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ X : ℝ, 1 < T → 0 ≤ X → X ≤ B*T →
      ∀ A : Finset ℕ,
      (∀ n ∈ A, 0 < n ∧ X < n ∧ (n:ℝ) ≤ 2*X) →
      ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      ∀ a : ℕ → ℂ, (∀ n ∈ A, ‖a n‖ ≤ 1) →
      (∑ t ∈ W,∑ u ∈ W,‖∑ n ∈ A,a n*phase n (t-u)‖^2) ≤
        C*T^η*X*((W.card:ℝ)^2+X*(W.card:ℝ)^(2-1/(K:ℝ))+
          T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))) := by
  obtain ⟨C,hC,hb⟩ := general_pair_energy hK hη hB
  refine ⟨C,hC,?_⟩
  intro T t₀ X hT hX hXT A hA W hW hsep a ha
  have hh := hb T t₀ X hT hX hXT (A ×ˢ A) (by
    intro p hp
    obtain ⟨hp1,hp2⟩ := mem_product.mp hp
    obtain ⟨h1,hl1,hu1⟩ := hA p.1 hp1
    obtain ⟨h2,hl2,hu2⟩ := hA p.2 hp2
    exact ⟨h1,h2,hl1,hu1,hl2,hu2⟩) W hW hsep
  simp only [sum_product,pairRatio,Rat.cast_div,Rat.cast_natCast] at hh
  exact (dirichlet_difference_energy_le A (fun n hn => (hA n hn).1) W a ha).trans hh

end Montgomery.RationalMoment
