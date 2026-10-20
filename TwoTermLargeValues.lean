module
public import TwoTermAbsorption

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Finset
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement

/-- The proved energy theorem and actual signed finite cubic bound imply the
large-value count uniformly over every real length in the lower window. -/
theorem two_term_lower_large_values {σ a p α δ : ℝ}
    (hw : TwoTermWindow σ a p α) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T N t₀ : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      2 ≤ T → T^a ≤ N → N ≤ T^α →
      (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) →
      (∀ t ∈ W, t₀ ≤ t ∧ t ≤ t₀+T) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ*T^(-2*δ) ≤ ‖boundedPolynomial N b t‖) →
      (W.card:ℝ) ≤ C*T^(p+18*δ) := by
  obtain ⟨A,hA,hc⟩ := finite_cubic_large_value_bound MathCollab.Density.comparisonCutoff
    (K:=2) (by norm_num) hδ
  obtain ⟨B,hB,he⟩ := discrete_additive_energy_two_term (K:=2) (by norm_num) hδ
  refine ⟨1+A*(4+2*B),by positivity,?_⟩
  intro T N t₀ b W hT hlo hhi hb hloc hsep hlarge
  have ht : 1 ≤ T := by linarith
  have htp : 0 < T := by linarith
  have hn1 : 1 ≤ N := (Real.one_le_rpow ht (show 0 ≤ a by linarith [hw.a_low])).trans hlo
  have hn : 0 < N := by linarith
  let L := twoTermAmplifier T N σ p
  obtain ⟨hnl,hll,hlt,hs,hen⟩ := two_term_amplifier_budgets hw ht hn hlo hhi
  have hnt : N ≤ T := hnl.trans hlt
  have hlp : 0 < L := hn.trans_le hnl
  have hv : 0 < N^σ*T^(-2*δ) := by positivity
  have hp : 0 < T^p := by positivity
  have hpow : 1 ≤ T^(18*δ) := Real.one_le_rpow ht (by positivity)
  by_cases hr : (W.card:ℝ) ≤ T^p
  · calc
      _ ≤ T^p := hr
      _ ≤ (1+A*(4+2*B))*(T^(18*δ)*T^p) := by
        have hh : 1 ≤ 1+A*(4+2*B) := by nlinarith [mul_nonneg hA.le (show 0 ≤ 4+2*B by linarith)]
        nlinarith only [mul_le_mul_of_nonneg_right hpow hp.le,mul_nonneg (by positivity : 0 ≤ A*(4+2*B)) (by positivity : 0 ≤ T^(18*δ)*T^p)]
      _ = _ := by rw [← Real.rpow_add htp]; congr 2; ring
  · have hrs : T^p ≤ (W.card:ℝ) := (lt_of_not_ge hr).le
    have hrange : T^(((2:ℝ)+1)/(2*2+1)) ≤ (W.card:ℝ) := by
      norm_num
      exact hs.trans hrs
    have henergy := he T t₀ N (by linarith) hn hnt b W (N^σ*T^(-2*δ))
      hrange (hen.trans hrs) hb hv hlarge hloc hsep
    have hlen : (T/L)^2 ≤ (W.card:ℝ) := by
      have hh : T/L ≤ T/N := div_le_div_of_nonneg_left htp.le hn hnl
      exact (pow_le_pow_left₀ (by positivity) hh 2).trans (hen.trans hrs)
    have hcubic := hc T t₀ N L hT hn1 hnl hll hlt b hb W (N^σ*T^(-2*δ))
      hv.le hrange hlen hloc hlarge hsep
    obtain ⟨h1,h2,h3,h4,h5⟩ := two_term_monomial_budgets hw hδ.le ht hn hlo hhi
    have hh := two_term_scalar_absorption hn hlp htp hv hp hrs
      (Real.one_le_rpow ht (show 0 ≤ 16*δ by positivity))
      (Real.one_le_rpow ht hδ.le) hA.le hB.le
      (Nat.cast_nonneg (discreteAdditiveEnergy W)) henergy hcubic h1 h2 h3 h4 h5
    have heq : (T^δ)^2*T^(16*δ)*T^p = T^(p+18*δ) := by
      rw [← Real.rpow_natCast (T^δ) 2,← Real.rpow_mul htp.le,
        ← Real.rpow_add htp,← Real.rpow_add htp]
      congr 1
      norm_num
      ring
    calc
      _ ≤ A*(4+2*B)*(T^δ)^2*T^(16*δ)*T^p := hh
      _ = A*(4+2*B)*T^(p+18*δ) := by rw [← heq]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)


/-- The upper detecting window is covered by the ordinary second moment,
including lengths greater than the observation time. -/
theorem two_term_upper_large_values {σ a p α δ : ℝ}
    (hw : TwoTermWindow σ a p α) (hδ : 0 < δ) (hδ' : δ ≤ 1/100) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H N t₀ : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      2 ≤ H → 2 ≤ N → H^α ≤ N → N ≤ H^(3*a/2+δ) →
      (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) →
      (∀ t ∈ W, t₀ ≤ t ∧ t ≤ t₀+H) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ*H^(-2*δ) ≤ ‖boundedPolynomial N b t‖) →
      (W.card:ℝ) ≤ C*H^(p+18*δ) := by
  let D : ℝ := Real.log 2+1/δ
  have hD : 0 < D := by
    dsimp [D]
    exact add_pos_of_nonneg_of_pos (Real.log_nonneg (by norm_num)) (one_div_pos.mpr hδ)
  refine ⟨102*(1+D),by positivity,?_⟩
  intro H N t₀ b W hH hN hlo hhi hb hloc hsep hlarge
  have hH1 : 1 ≤ H := by linarith
  have hH0 : 0 < H := by linarith
  have hN0 : 0 < N := by linarith
  have hV : 0 < N^σ*H^(-2*δ) := by positivity
  have hsmall : N^δ ≤ H^(2*δ) := by
    calc
      _ ≤ (H^(3*a/2+δ))^δ := Real.rpow_le_rpow hN0.le hhi hδ.le
      _ = H^((3*a/2+δ)*δ) := (Real.rpow_mul hH0.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hH1 (by
        have hh := mul_nonneg hδ.le (show 0 ≤ 2-3*a/2-δ by linarith [hw.a_high])
        nlinarith only [hh])
  have hpos : N^(2-2*σ) ≤ H^(p+2*δ) := by
    calc
      _ ≤ (H^(3*a/2+δ))^(2-2*σ) := Real.rpow_le_rpow hN0.le hhi (by linarith [hw.sigma_high])
      _ = H^((3*a/2+δ)*(2-2*σ)) := (Real.rpow_mul hH0.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hH1 (by
        have hh := mul_nonneg (show 0 ≤ 2*σ by linarith [hw.sigma_low]) hδ.le
        nlinarith only [hw.p_identity,hh])
  have hmean1 : H*N^(1-2*σ) ≤ H^p := by
    calc
      _ ≤ H*(H^α)^(1-2*σ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by positivity) hlo (by linarith [hw.sigma_low])) hH0.le
      _ = H^(1+α*(1-2*σ)) := by
        rw [← Real.rpow_mul hH0.le]
        nth_rw 1 [← Real.rpow_one H]
        rw [← Real.rpow_add hH0]
      _ = _ := by rw [hw.mean_identity]
  obtain ⟨_hdiv2,_hdiv4,hdivM⟩ := short_density_height_budgets hH0 hN0 σ δ
  have hmean := separated_second_moment hN hH0.le b hb W hloc hsep
  have hcard : (W.card:ℝ)*(N^σ*H^(-2*δ))^2 ≤ 102*N*(H+N*Real.log (2*N)) := by
    calc
      _ = ∑ _t ∈ W, (N^σ*H^(-2*δ))^2 := by simp
      _ ≤ ∑ t ∈ W, ‖boundedPolynomial N b t‖^2 :=
        sum_le_sum (fun t ht => pow_le_pow_left₀ hV.le (hlarge t ht) 2)
      _ ≤ _ := hmean
  have hc : (W.card:ℝ) ≤ 102*((H*N^(1-2*σ)+N^(2-2*σ)*Real.log (2*N))*H^(4*δ)) := by
    have hh := (le_div_iff₀ (sq_pos_of_pos hV)).mpr hcard
    have he : 102*N*(H+N*Real.log (2*N))/(N^σ*H^(-2*δ))^2 =
        102*(N*(H+N*Real.log (2*N))/(N^σ*H^(-2*δ))^2) := by ring
    rw [he,hdivM] at hh
    exact hh
  have hlog : Real.log (2*N) ≤ D*H^(2*δ) :=
    (classical_log_budget (by linarith : 1 ≤ N) hδ).trans
      (mul_le_mul_of_nonneg_left hsmall hD.le)
  have hmean2 : N^(2-2*σ)*Real.log (2*N) ≤ D*H^(p+4*δ) := by
    calc
      _ ≤ H^(p+2*δ)*(D*H^(2*δ)) :=
        mul_le_mul hpos hlog (Real.log_nonneg (by linarith)) (by positivity)
      _ = D*(H^(p+2*δ)*H^(2*δ)) := by ring
      _ = _ := by rw [← Real.rpow_add hH0]; congr 2; ring
  have hmean1' : H*N^(1-2*σ) ≤ H^(p+4*δ) :=
    hmean1.trans (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith))
  have hsum : H*N^(1-2*σ)+N^(2-2*σ)*Real.log (2*N) ≤
      (1+D)*H^(p+4*δ) := by nlinarith
  have hbudget : 102*((H*N^(1-2*σ)+N^(2-2*σ)*Real.log (2*N))*H^(4*δ)) ≤
      (102*(1+D))*H^(p+18*δ) := by
    calc
      _ ≤ 102*(((1+D)*H^(p+4*δ))*H^(4*δ)) := by gcongr
      _ = (102*(1+D))*(H^(p+4*δ)*H^(4*δ)) := by ring
      _ = (102*(1+D))*H^(p+8*δ) := by
        rw [← Real.rpow_add hH0]; congr 2; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)) (by positivity)
  exact hc.trans hbudget


/-- Uniform count for every actual detecting length, with no intermediate gap. -/
theorem two_term_full_window_large_values {σ a p α δ : ℝ}
    (hw : TwoTermWindow σ a p α) (hδ : 0 < δ) (hδ' : δ ≤ 1/100) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T N t₀ : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      2 ≤ T → 2 ≤ N → T^a ≤ N → N ≤ T^(3*a/2+δ) →
      (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) →
      (∀ t ∈ W, t₀ ≤ t ∧ t ≤ t₀+T) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ*T^(-2*δ) ≤ ‖boundedPolynomial N b t‖) →
      (W.card:ℝ) ≤ C*T^(p+18*δ) := by
  obtain ⟨C,hC,hlo⟩ := two_term_lower_large_values hw hδ
  obtain ⟨D,hD,hhi⟩ := two_term_upper_large_values hw hδ hδ'
  refine ⟨C+D,by positivity,?_⟩
  intro T N t₀ b W hT hN hl hu hb hloc hsep hlarge
  by_cases hm : N ≤ T^α
  · exact (hlo T N t₀ b W hT hl hm hb hloc hsep hlarge).trans
      (mul_le_mul_of_nonneg_right (by linarith : C ≤ C+D) (by positivity))
  · exact (hhi T N t₀ b W hT hN (le_of_not_ge hm) hu hb hloc hsep hlarge).trans
      (mul_le_mul_of_nonneg_right (by linarith : D ≤ C+D) (by positivity))

end Montgomery.RationalMoment
