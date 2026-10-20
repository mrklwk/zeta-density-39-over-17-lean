module
public import ThirdWindow

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Montgomery.RationalMoment

/-- All nine budgets, including both unrestricted order-four trace terms.
The actual normalized detector height and its loss are retained. -/
theorem third_monomial_budgets {σ a p α δ T N : ℝ}
    (hw : ThirdWindow σ a p α) (hδ : 0 ≤ δ) (hT : 1 < T) (hN : 0 < N)
    (hlo : T^a ≤ N) (hhi : N ≤ T^α) :
    ∃ L : ℝ, N ≤ L ∧ T^((4:ℝ)/5) ≤ L ∧ L ≤ T ∧
    let S := T^p
    let Q := T^(16*δ)
    let V := N^σ*T^(-2*δ)
    (N*L)^3 ≤ Q*S^3*V^6 ∧
    (N^4*T^2/L)^2 ≤ Q^2*S^3*V^12 ∧
    N^12*T^2 ≤ Q^2*S^4*V^16 ∧
    N^9*T^2 ≤ Q^2*S^2*V^14 ∧
    N^4*L ≤ Q*S*V^6 ∧
    N^8*T^3 ≤ Q^2*S^((5:ℝ)/2)*V^14 ∧
    N^9*T^((9:ℝ)/4) ≤ Q^2*S^((29:ℝ)/12)*V^14 ∧
    N^4*T ≤ Q*S^((5:ℝ)/4)*V^6 ∧
    N^4*L*T^((1:ℝ)/8) ≤ Q*S^((49:ℝ)/40)*V^6 := by
  have hTp : 0 < T := by linarith
  have ht : 0 < Real.log T := Real.log_pos hT
  let x : ℝ := Real.logb T N
  have hNx : T^x=N := Real.rpow_logb hTp (by linarith) hN
  have hxa : a ≤ x := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hTp a) hlo
    rw [Real.log_rpow hTp] at hh
    exact (le_div_iff₀ ht).mpr hh
  have hxα : x ≤ α := by
    have hh := Real.log_le_log hN hhi
    rw [Real.log_rpow hTp] at hh
    exact (div_le_iff₀ ht).mpr hh
  let l := thirdAmplifierExponent σ p x
  let L := T^l
  have hLp : 0 < L := by dsimp [L]; positivity
  obtain ⟨hb0,hb1,hb5,hb9,hb3,hb4,hb6,hb7,hb8⟩ := hw.budgets x hxa hxα
  have hxl : x ≤ l := le_max_left _ _
  have hll : (5/6:ℝ) ≤ l := (le_max_left _ _).trans (le_max_right _ _)
  have hbl : 2+(4-6*σ)*x-3*p/2 ≤ l := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨L,?_,?_,?_,?_⟩
  · rw [← hNx]
    exact Real.rpow_le_rpow_of_exponent_le hT.le hxl
  · exact Real.rpow_le_rpow_of_exponent_le hT.le (by linarith)
  · exact (Real.rpow_le_rpow_of_exponent_le hT.le hb0).trans_eq (Real.rpow_one T)
  have hlogN : Real.log N=x*Real.log T := by rw [← hNx,Real.log_rpow hTp]
  have hlogL : Real.log L=l*Real.log T := Real.log_rpow hTp l
  have hd := mul_nonneg hδ ht.le
  have hm (q : ℝ) (hq : 0 ≤ q) : 0 ≤ q*Real.log T := mul_nonneg hq ht.le
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    simp (disch := positivity) only [Real.log_mul,Real.log_div,Real.log_pow,Real.log_rpow]
    norm_num only [Nat.cast_ofNat]
    simp only [hlogN,hlogL]
  · have hh := hm _ (show 0 ≤ p+(2*σ-1)*x-l by linarith only [hb1])
    nlinarith only [hh,hd]
  · have hh := hm _ (show 0 ≤ l-(2+(4-6*σ)*x-3*p/2) by linarith only [hbl])
    nlinarith only [hh,hd]
  · have hh := hm _ (show 0 ≤ 4*p+(16*σ-12)*x-2 by linarith only [hb3])
    nlinarith only [hh]
  · have hh := hm _ (show 0 ≤ 2*p+(14*σ-9)*x-2 by linarith only [hb4])
    nlinarith only [hh,hd]
  · have hh := hm _ (show 0 ≤ p+(6*σ-4)*x-l by linarith only [hb5])
    nlinarith only [hh,hd]
  · have hh := hm _ (show 0 ≤ (5/2)*p+(14*σ-8)*x-3 by linarith only [hb6])
    nlinarith only [hh,hd]
  · have hh := hm _ (show 0 ≤ (29/12)*p+(14*σ-9)*x-9/4 by linarith only [hb7])
    nlinarith only [hh,hd]
  · have hh := hm _ (show 0 ≤ (5/4)*p+(6*σ-4)*x-1 by linarith only [hb8])
    nlinarith only [hh,hd]
  · have hh := hm _ (show 0 ≤ (49/40)*p+(6*σ-4)*x-1/8-l by linarith only [hb9])
    nlinarith only [hh,hd]

end Montgomery.RationalMoment
