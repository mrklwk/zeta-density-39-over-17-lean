module
public import AdjacentWindow

@[expose] public section

set_option autoImplicit false
noncomputable section
open Real
namespace Montgomery.RationalMoment

/-- All five monomial inequalities hold for every real detecting length
in the lower window. The normalized detector height loses exactly T^(-2δ),
and Q=T^(16δ) pays that loss explicitly. -/
theorem adjacent_monomial_budgets {σ a p α δ T N : ℝ}
    (hw : AdjacentWindow σ a p α) (hδ : 0 ≤ δ) (hT : 1 ≤ T) (hN : 0 < N)
    (hlo : T^a ≤ N) (hhi : N ≤ T^α) :
    let L := twoTermAmplifier T N σ p
    let S := T^p
    let Q := T^(16*δ)
    let V := N^σ*T^(-2*δ)
    (N*L)^3 ≤ Q*S^3*V^6 ∧
    (N^4*T^2/L)^2 ≤ Q^2*S^3*V^12 ∧
    N^12*T^2 ≤ Q^2*S^4*V^16 ∧
    N^9*T^2 ≤ Q^2*S^2*V^14 ∧
    N^4*L ≤ Q*S*V^6 ∧
    N^8*T^3 ≤ Q^2*S^((5:ℝ)/2)*V^14 ∧
    N^9*T^((9:ℝ)/4) ≤ Q^2*S^((29:ℝ)/12)*V^14 := by
  have hTp : 0 < T := by linarith
  have ha : 0 ≤ a := by linarith [hw.a_low]
  have hN1 : 1 ≤ N := (Real.one_le_rpow hT ha).trans hlo
  have ht : 0 ≤ Real.log T := Real.log_nonneg hT
  have hn : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hlow : a*Real.log T ≤ Real.log N := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hTp a) hlo
    simpa only [Real.log_rpow hTp] using hh
  have hhigh : Real.log N ≤ α*Real.log T := by
    have hh := Real.log_le_log hN hhi
    simpa only [Real.log_rpow hTp] using hh
  have hd := mul_nonneg hδ ht
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  all_goals
    apply (Real.log_le_log_iff (by first | (unfold twoTermAmplifier; positivity) | positivity)
      (by positivity)).mp
    simp (disch := positivity) only [twoTermAmplifier,Real.log_mul,Real.log_div,
      Real.log_pow,Real.log_rpow]
    norm_num only [Nat.cast_ofNat]
  · have hh := mul_nonneg (show 0 ≤ 9-12*σ by linarith [hw.sigma_high]) hn
    nlinarith only [hh,hd]
  · have hh := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 24*σ-16 by linarith [hw.sigma_low])
    have hb := mul_nonneg (show 0 ≤ 5*p-4+a*(24*σ-16) by linarith [hw.cubic_balance]) ht
    nlinarith only [hh,hb,hd]
  · have hh := mul_le_mul_of_nonneg_left hhigh (show 0 ≤ 12-16*σ by linarith [hw.sigma_high])
    have hb := mul_nonneg (show 0 ≤ 4*p-2-α*(12-16*σ) by linarith [hw.energy_first]) ht
    nlinarith only [hh,hb]
  · have hh := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 14*σ-9 by linarith [hw.sigma_low])
    have hb := mul_nonneg (show 0 ≤ 2*p-2+a*(14*σ-9) by linarith [hw.energy_resonant]) ht
    nlinarith only [hh,hb,hd]
  · nlinarith only [hd]
  · have hh := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 14*σ-8 by linarith [hw.sigma_low])
    have hb := mul_nonneg (show 0 ≤ (5/2)*p+a*(14*σ-8)-3 by linarith [hw.energy_adjacent_third]) ht
    nlinarith only [hh,hb,hd]
  · have hh := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 14*σ-9 by linarith [hw.sigma_low])
    have hb := mul_nonneg (show 0 ≤ (29/12)*p+a*(14*σ-9)-9/4 by linarith [hw.energy_adjacent_fourth]) ht
    nlinarith only [hh,hb,hd]

end Montgomery.RationalMoment
