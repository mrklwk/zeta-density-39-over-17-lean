module
public import AdjacentAbsorption
public import AdjacentMonomialBudgets
public import AdjacentUpperValues

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement

theorem adjacent_lower_large_values {σ a p α δ : ℝ}
    (hw : AdjacentWindow σ a p α) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T N t₀ : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      2 ≤ T → T^a ≤ N → N ≤ T^α →
      (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) →
      (∀ t ∈ W, t₀ ≤ t ∧ t ≤ t₀+T) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ*T^(-2*δ) ≤ ‖boundedPolynomial N b t‖) →
      (W.card:ℝ) ≤ C*T^(p+18*δ) := by
  obtain ⟨A,hA,hc⟩ := finite_cubic_large_value_bound MathCollab.Density.comparisonCutoff
    (K:=4) (by norm_num) hδ
  obtain ⟨B,hB,he⟩ := discrete_additive_energy_adjacent hδ
  refine ⟨1+A*(4+4*B),by positivity,?_⟩
  intro T N t₀ b W hT hlo hhi hb hloc hsep hlarge
  have ht : 1 ≤ T := by linarith
  have htp : 0 < T := by linarith
  have hn1 : 1 ≤ N := (Real.one_le_rpow ht (show 0 ≤ a by linarith [hw.a_low])).trans hlo
  have hn : 0 < N := by linarith
  let L := twoTermAmplifier T N σ p
  obtain ⟨hnl,hll,hlt,hs,hen⟩ := adjacent_amplifier_budgets hw ht hn hlo hhi
  have hnt : N ≤ T := hnl.trans hlt
  have hlp : 0 < L := hn.trans_le hnl
  have hv : 0 < N^σ*T^(-2*δ) := by positivity
  have hp : 0 < T^p := by positivity
  have hpow : 1 ≤ T^(18*δ) := Real.one_le_rpow ht (by positivity)
  by_cases hr : (W.card:ℝ) ≤ T^p
  · calc
      _ ≤ T^p := hr
      _ ≤ (1+A*(4+4*B))*(T^(18*δ)*T^p) := by
        have hh : 1 ≤ 1+A*(4+4*B) := by nlinarith [mul_nonneg hA.le (show 0 ≤ 4+4*B by linarith)]
        nlinarith only [mul_le_mul_of_nonneg_right hpow hp.le,mul_nonneg (by positivity : 0 ≤ A*(4+4*B)) (by positivity : 0 ≤ T^(18*δ)*T^p)]
      _ = _ := by rw [← Real.rpow_add htp]; congr 2; ring
  · have hrs : T^p ≤ (W.card:ℝ) := (lt_of_not_ge hr).le
    have hrange : T^(((4:ℝ)+1)/(2*4+1)) ≤ (W.card:ℝ) := by
      norm_num
      exact hs.trans hrs
    have hnlow : T^((2:ℝ)/3) ≤ N :=
      (Real.rpow_le_rpow_of_exponent_le ht (by linarith [hw.a_low])).trans hlo
    have henergy := he T t₀ N (by linarith) hnlow hnt b W (N^σ*T^(-2*δ))
      (hs.trans hrs) hb hv hlarge hloc hsep
    have hlen : (T/L)^4 ≤ (W.card:ℝ) := hen.trans hrs
    have hcubic := hc T t₀ N L hT hn1 hnl hll hlt b hb W (N^σ*T^(-2*δ))
      hv.le hrange hlen hloc hlarge hsep
    obtain ⟨h1,h2,h3,h4,h5,h6,h7⟩ := adjacent_monomial_budgets hw hδ.le ht hn hlo hhi
    have hh := adjacent_scalar_absorption hn hlp htp hv hp hrs
      (Real.one_le_rpow ht (show 0 ≤ 16*δ by positivity))
      (Real.one_le_rpow ht hδ.le) hA.le hB.le
      (Nat.cast_nonneg (discreteAdditiveEnergy W)) henergy hcubic h1 h2 h3 h4 h5 h6 h7
    have heq : (T^δ)^2*T^(16*δ)*T^p = T^(p+18*δ) := by
      rw [← Real.rpow_natCast (T^δ) 2,← Real.rpow_mul htp.le,
        ← Real.rpow_add htp,← Real.rpow_add htp]
      congr 1
      norm_num
      ring
    calc
      _ ≤ A*(4+4*B)*(T^δ)^2*T^(16*δ)*T^p := hh
      _ = A*(4+4*B)*T^(p+18*δ) := by rw [← heq]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)



theorem adjacent_full_window_large_values {σ a p α δ : ℝ}
    (hw : AdjacentWindow σ a p α) (hδ : 0 < δ) (hδ' : δ ≤ 1/100) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T N t₀ : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      2 ≤ T → 2 ≤ N → T^a ≤ N → N ≤ T^(3*a/2+δ) →
      (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) →
      (∀ t ∈ W, t₀ ≤ t ∧ t ≤ t₀+T) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ*T^(-2*δ) ≤ ‖boundedPolynomial N b t‖) →
      (W.card:ℝ) ≤ C*T^(p+18*δ) := by
  obtain ⟨C,hC,hlo⟩ := adjacent_lower_large_values hw hδ
  obtain ⟨D,hD,hhi⟩ := adjacent_upper_large_values hw hδ hδ'
  refine ⟨C+D,by positivity,?_⟩
  intro T N t₀ b W hT hN hl hu hb hloc hsep hlarge
  by_cases hm : N ≤ T^α
  · exact (hlo T N t₀ b W hT hl hm hb hloc hsep hlarge).trans
      (mul_le_mul_of_nonneg_right (by linarith : C ≤ C+D) (by positivity))
  · exact (hhi T N t₀ b W hT hN (le_of_not_ge hm) hu hb hloc hsep hlarge).trans
      (mul_le_mul_of_nonneg_right (by linarith : D ≤ C+D) (by positivity))

end Montgomery.RationalMoment
