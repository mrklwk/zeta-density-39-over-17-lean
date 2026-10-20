module
public import ThirdAbsorption
public import ThirdMonomialBudgets
public import ThirdUpperValues

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement

theorem third_lower_large_values {σ a p α δ : ℝ}
    (hw : ThirdWindow σ a p α) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T N t₀ : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      2 ≤ T → T^a ≤ N → N ≤ T^α →
      (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) →
      (∀ t ∈ W, t₀ ≤ t ∧ t ≤ t₀+T) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ*T^(-2*δ) ≤ ‖boundedPolynomial N b t‖) →
      (W.card:ℝ) ≤ C*T^(p+18*δ) := by
  obtain ⟨A,hA,hc⟩ := finite_cubic_large_value_general MathCollab.Density.comparisonCutoff
    (K:=4) (by norm_num) hδ
  obtain ⟨B,hB,he⟩ := discrete_energy_adjacent_unrestricted hδ
  refine ⟨1+A*(6+4*B),by positivity,?_⟩
  intro T N t₀ b W hT hlo hhi hb hloc hsep hlarge
  have ht : 1 ≤ T := by linarith
  have htp : 0 < T := by linarith
  have hn1 : 1 ≤ N := (Real.one_le_rpow ht (show 0 ≤ a by linarith [hw.a_low])).trans hlo
  have hn : 0 < N := by linarith
  obtain ⟨L,hnl,hll,hlt,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩ :=
    third_monomial_budgets hw hδ.le (by linarith) hn hlo hhi
  have hnt : N ≤ T := hnl.trans hlt
  have hlp : 0 < L := hn.trans_le hnl
  have hv : 0 < N^σ*T^(-2*δ) := by positivity
  have hp : 0 < T^p := by positivity
  have hpow : 1 ≤ T^(18*δ) := Real.one_le_rpow ht (by positivity)
  by_cases hr : (W.card:ℝ) ≤ T^p
  · calc
      _ ≤ T^p := hr
      _ ≤ (1+A*(6+4*B))*(T^(18*δ)*T^p) := by
        have hh : 1 ≤ 1+A*(6+4*B) := by nlinarith [mul_nonneg hA.le (show 0 ≤ 6+4*B by linarith)]
        nlinarith only [mul_le_mul_of_nonneg_right hpow hp.le,mul_nonneg (by positivity : 0 ≤ A*(6+4*B)) (by positivity : 0 ≤ T^(18*δ)*T^p)]
      _ = _ := by rw [← Real.rpow_add htp]; congr 2; ring
  · have hrs : T^p ≤ (W.card:ℝ) := (lt_of_not_ge hr).le
    have henergy := he T t₀ N (by linarith) hn hnt b W (N^σ*T^(-2*δ))
      hb hv hlarge hloc hsep
    have hcubic := hc T t₀ N L hT hn1 hnl hll hlt b hb W (N^σ*T^(-2*δ))
      hv.le hloc hlarge hsep
    norm_num [adjacentCenteredBudget] at hcubic
    rw [mul_add,mul_add] at hcubic
    have hcubic' : (W.card:ℝ)^3*(N^σ*T^(-2*δ))^6 ≤ A*T^δ*((N*L)^3+
        (N^4*T^2/L)*(W.card:ℝ)*Real.sqrt (W.card:ℝ)+
        N^4*T*Real.sqrt (W.card:ℝ)*Real.sqrt (discreteAdditiveEnergy W:ℝ)+
        N^4*L*(W.card:ℝ)^2+N^4*T*(W.card:ℝ)^((7:ℝ)/4)+
        N^4*L*T^((1:ℝ)/8)*(W.card:ℝ)^((71:ℝ)/40)) := by
      convert hcubic using 1 <;> ring_nf
    have hh := third_scalar_absorption hn hlp htp hv hp hrs
      (Real.one_le_rpow ht (show 0 ≤ 16*δ by positivity))
      (Real.one_le_rpow ht hδ.le) hA.le hB.le
      (Nat.cast_nonneg (discreteAdditiveEnergy W)) henergy hcubic' h1 h2 h3 h4 h5 h6 h7 h8 h9
    have heq : (T^δ)^2*T^(16*δ)*T^p = T^(p+18*δ) := by
      rw [← Real.rpow_natCast (T^δ) 2,← Real.rpow_mul htp.le,
        ← Real.rpow_add htp,← Real.rpow_add htp]
      congr 1
      norm_num
      ring
    calc
      _ ≤ A*(6+4*B)*(T^δ)^2*T^(16*δ)*T^p := hh
      _ = A*(6+4*B)*T^(p+18*δ) := by rw [← heq]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)



theorem third_full_window_large_values {σ a p α δ : ℝ}
    (hw : ThirdWindow σ a p α) (hδ : 0 < δ) (hδ' : δ ≤ 1/100) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T N t₀ : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      2 ≤ T → 2 ≤ N → T^a ≤ N → N ≤ T^(3*a/2+δ) →
      (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) →
      (∀ t ∈ W, t₀ ≤ t ∧ t ≤ t₀+T) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ*T^(-2*δ) ≤ ‖boundedPolynomial N b t‖) →
      (W.card:ℝ) ≤ C*T^(p+18*δ) := by
  obtain ⟨C,hC,hlo⟩ := third_lower_large_values hw hδ
  obtain ⟨D,hD,hhi⟩ := third_upper_large_values hw hδ hδ'
  refine ⟨C+D,by positivity,?_⟩
  intro T N t₀ b W hT hN hl hu hb hloc hsep hlarge
  by_cases hm : N ≤ T^α
  · exact (hlo T N t₀ b W hT hl hm hb hloc hsep hlarge).trans
      (mul_le_mul_of_nonneg_right (by linarith : C ≤ C+D) (by positivity))
  · exact (hhi T N t₀ b W hT hN (le_of_not_ge hm) hu hb hloc hsep hlarge).trans
      (mul_le_mul_of_nonneg_right (by linarith : D ≤ C+D) (by positivity))

end Montgomery.RationalMoment
