module
public import PairLongZeroCount
public import RetunedActualDensity

@[expose] public section
set_option autoImplicit false
noncomputable section
open Real Filter MeasureTheory Set
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger MathCollab.Density TaoTrudgianYang2025

/-- Actual zeta zeros from a genuine analytic pair, with every detector and
tail input discharged. The two exact exponent budgets are numerical. -/
theorem density_of_pair_tail_window {k l σ a ε : ℝ}
    (hpair : ExponentPair k l) (hk : 0 < k) (hlog : 2+4*l/k ≤ 7)
    (hw : QuadraticWindow σ a) (hsigma : 7/9 ≤ σ)
    (hthreshold : 1/8 < (3*a/4)*(σ-1/2))
    (hfirst : 1-6*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ))
    (hsecond : 1+l/k-(4+(2+4*l)/k)*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ))
    (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : ℝ,2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(3*a*(1-σ)+ε) := by
  let θ : ℝ := (3*a/4)*(σ-1/2)
  let b : ℝ := 4+(2+4*l)/k
  have hl : 0 < l := lt_of_lt_of_le (by norm_num) hpair.inTriangle.2.2.1
  have hb : 0 < b := by dsimp [b]; positivity
  let s : ℝ := min ((θ-1/8)/4) (ε/(8*(b+6)))
  have hs : 0 < s := by dsimp [s]; exact lt_min (by dsimp [θ]; linarith) (by positivity)
  have hsθ : s ≤ (θ-1/8)/4 := min_le_left _ _
  have hse : s ≤ ε/(8*(b+6)) := min_le_right _ _
  have hsb : s*(8*(b+6)) ≤ ε := (le_div_iff₀ (by positivity)).mp hse
  have hs6 : 6*s ≤ ε/4 := by nlinarith [mul_pos hs hb]
  have hsb' : b*s ≤ ε/4 := by nlinarith
  let q : ℝ := θ-s
  let δ : ℝ := min s (1/16)
  have hδ : 0 < δ := lt_min hs (by norm_num)
  have hδs : δ ≤ s := min_le_left _ _
  have hδcap : δ ≤ 1/16 := min_le_right _ _
  have hq : 1/8 < q := by dsimp [q]; linarith
  have hmargin : q+δ/2 < θ := by dsimp [q]; linarith
  let η : ℝ := min (ε/1000) (min ((1-3*a/2)/4) (a*(4*σ-3)/100))
  have ha : 0 < a := by linarith [hw.a_low]
  have hgap : 0 < a*(4*σ-3) := mul_pos ha (by linarith [hw.sigma_low])
  have hη : 0 < η := by
    dsimp [η]
    exact lt_min (by positivity) (lt_min (by linarith [hw.a_high]) (by positivity))
  have hηeps : η ≤ ε/1000 := min_le_left _ _
  have hηa : η ≤ (1-3*a/2)/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hηg : η ≤ a*(4*σ-3)/100 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨Cs,hCs,hshort⟩ := smoothShortZeroCount_bound hw hη
    (by linarith [hw.a_high]) (by linarith) δ
  obtain ⟨Cl,hCl,hlong⟩ := smoothLongZeroCount_pair_tail hpair hk hlog hw hsigma
    hδ (by linarith) hη (show 0 < ε/2 by positivity) hq hmargin
    (show 1-6*q ≤ 3*a*(1-σ)+(ε/2)/2 by dsimp [q,θ] at *; linarith)
    (show 1+l/k-(4+(2+4*l)/k)*q ≤ 3*a*(1-σ)+(ε/2)/2 by
      change 1+l/k-b*(θ-s) ≤ _
      change 1+l/k-b*θ ≤ _ at hsecond
      nlinarith)
  have hslab : ∀ᶠ T : ℝ in atTop,
      (zetaSlabCount σ T (2*T):ℝ) ≤ (Cs+Cl)*T^(3*a*(1-σ)+ε) := by
    filter_upwards [hshort,hlong,eventually_ge_atTop (1:ℝ)] with T hsT hlT hT
    have hs' := hsT.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT (show 3*a*(1-σ)+52*η ≤ 3*a*(1-σ)+ε by linarith)) hCs.le)
    have hl' := hlT.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT (show 3*a*(1-σ)+ε/2 ≤ 3*a*(1-σ)+ε by linarith)) hCl.le)
    rw [smooth_zeroCount_partition η σ a δ T,Nat.cast_add]
    nlinarith only [hs',hl']
  have hp : 0 < 3*a*(1-σ)+ε := by
    have hh : 0 < 3*a*(1-σ) := mul_pos (mul_pos (by norm_num) ha) (by linarith [hw.sigma_high])
    linarith
  exact zetaDensity_bound_of_eventual_slabs hp (by positivity : 0 < Cs+Cl) hslab
end Montgomery.RationalMoment.RightDetector
