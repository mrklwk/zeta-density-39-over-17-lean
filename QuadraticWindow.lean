module
public import QuadraticScalarAbsorption
public import DraftParameters

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

/-- Algebraic conditions for the full right-hand general-polynomial window.
A separate coefficient-one detector bridge is still required for density. -/
structure QuadraticWindow (σ a : ℝ) : Prop where
  sigma_low : 3/4 < σ
  sigma_high : σ < 1
  a_low : 1/2 ≤ a
  a_high : a < 2/3
  first : 2 ≤ a*(3*σ+1)
  second : 1 ≤ a*(11*σ-7)

theorem quadratic_monomial_budgets {σ a δ T N : ℝ}
    (hw : QuadraticWindow σ a) (hδ : 0 ≤ δ) (hδ' : δ ≤ (1-3*a/2)/2) (hT : 1 < T) (hN : 0 < N)
    (hlo : T^a ≤ N) (hhi : N ≤ T^(3*a/2+δ)) :
    ∃ L : ℝ, N ≤ L ∧ L ≤ T ∧
    let p := 3*a*(1-σ)
    let S := T^p
    let Q := T^(16*δ)
    let V := N^σ*T^(-2*δ)
    (N*L)^2 ≤ Q*S^2*V^4 ∧
    N^3*T/L ≤ Q*S^((1:ℝ)/2)*V^4 ∧
    N^3*T^((1:ℝ)/4) ≤ Q*S^((5:ℝ)/12)*V^4 := by
  have hTp : 0 < T := by linarith
  have ht : 0 < Real.log T := Real.log_pos hT
  let x : ℝ := Real.logb T N
  have hNx : T^x=N := Real.rpow_logb hTp (by linarith) hN
  have hxa : a ≤ x := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hTp a) hlo
    rw [Real.log_rpow hTp] at hh
    exact (le_div_iff₀ ht).mpr hh
  have hxhi : x ≤ 3*a/2+δ := by
    have hh := Real.log_le_log hN hhi
    rw [Real.log_rpow hTp] at hh
    exact (div_le_iff₀ ht).mpr hh
  let p := 3*a*(1-σ)
  let l := max x (p+(2*σ-1)*x)
  let L := T^l
  have hLp : 0 < L := by dsimp [L]; positivity
  obtain ⟨_,_,hb1a,hb2a⟩ := Montgomery.DraftParameters.quadratic_window
    hw.sigma_low hw.sigma_high (by linarith [hw.a_low]) hw.a_high.le hw.first hw.second
    (le_rfl : a ≤ a) (by linarith [hw.a_low] : a ≤ 3*a/2)
  have hmono1 := mul_le_mul_of_nonneg_left hxa (show 0 ≤ 6*σ-4 by linarith [hw.sigma_low])
  have hmono2 := mul_le_mul_of_nonneg_left hxa (show 0 ≤ 4*σ-3 by linarith [hw.sigma_low])
  have hb1 : 1 ≤ (3/2)*p+(6*σ-4)*x := by linarith only [hb1a,hmono1]
  have hb2 : 1/4 ≤ (5/12)*p+(4*σ-3)*x := by linarith only [hb2a,hmono2]
  have hlx : x ≤ l := le_max_left _ _
  have hlower : p+(2*σ-1)*x ≤ l := le_max_right _ _
  have hupper : l ≤ p+(2*σ-1)*x+δ := by
    apply max_le ?_ (by linarith only [hδ])
    have hm := mul_le_mul_of_nonneg_left hxhi (show 0 ≤ 2*(1-σ) by linarith [hw.sigma_high])
    have hd := mul_nonneg hδ (show 0 ≤ 2*σ-1 by linarith [hw.sigma_low])
    dsimp [p]
    nlinarith only [hm,hd]
  have hlu : l ≤ 1 := by
    have hxu : x ≤ 1 := by linarith [hw.a_high]
    apply max_le hxu
    have hm := mul_le_mul_of_nonneg_left hxhi (show 0 ≤ 2*σ-1 by linarith [hw.sigma_low])
    have hd := mul_nonneg hδ (show 0 ≤ 2-2*σ by linarith [hw.sigma_high])
    dsimp [p]
    nlinarith only [hm,hd,hδ',hw.a_high]
  refine ⟨L,?_,?_,?_⟩
  · rw [← hNx]
    exact Real.rpow_le_rpow_of_exponent_le hT.le hlx
  · exact (Real.rpow_le_rpow_of_exponent_le hT.le hlu).trans_eq (Real.rpow_one T)
  have hlogN : Real.log N=x*Real.log T := by rw [← hNx,Real.log_rpow hTp]
  have hlogL : Real.log L=l*Real.log T := Real.log_rpow hTp l
  have hd := mul_nonneg hδ ht.le
  dsimp only
  refine ⟨?_,?_,?_⟩
  all_goals
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    simp (disch := positivity) only [Real.log_mul,Real.log_div,Real.log_pow,Real.log_rpow]
    norm_num only [Nat.cast_ofNat]
    simp only [hlogN,hlogL]
  · have hh := mul_nonneg (show 0 ≤ p+(2*σ-1)*x+δ-l by linarith only [hupper]) ht.le
    nlinarith only [hh,hd]
  · have hh := mul_nonneg (show 0 ≤ (3/2)*p+(6*σ-4)*x-1 by linarith only [hb1]) ht.le
    have hh' := mul_nonneg (show 0 ≤ l-(p+(2*σ-1)*x) by linarith only [hlower]) ht.le
    nlinarith only [hh,hh',hd]
  · have hh := mul_nonneg (show 0 ≤ (5/12)*p+(4*σ-3)*x-1/4 by linarith only [hb2]) ht.le
    nlinarith only [hh,hd]

end Montgomery.RationalMoment
