module
public import RetunedTwelfthCount
public import RightQuadraticParameters

@[expose] public section

open Real Complex Filter MeasureTheory Set
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger MathCollab.Density

/-- Actual-zero composition at every retuned quadratic parameter where the
native twelfth moment supplies the long-detector count. Only numerical
conditions remain in the window, and the actual moment is proved. -/
theorem density_of_twelfth_window {σ a ε : ℝ}
    (hw : QuadraticWindow σ a) (hsigma : 7/9 ≤ σ)
    (h12 : 2 ≤ a*(6*σ-3/2)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(3*a*(1-σ)+ε) := by
  let η := min (ε/1000) (min ((1-3*a/2)/4) (a*(4*σ-3)/100))
  let δ := min (ε/1000) (1/16)
  have ha : 0 < a := by linarith [hw.a_low]
  have hgap : 0 < a*(4*σ-3) := mul_pos ha (by linarith [hw.sigma_low])
  have hη : 0 < η := by dsimp [η]; exact lt_min (by positivity) (lt_min (by linarith [hw.a_high]) (by positivity))
  have hηeps : η ≤ ε/1000 := min_le_left _ _
  have hηa : η ≤ (1-3*a/2)/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hηg : η ≤ a*(4*σ-3)/100 := (min_le_right _ _).trans (min_le_right _ _)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδeps : δ ≤ ε/1000 := min_le_left _ _
  have hδcap : δ ≤ 1/16 := min_le_right _ _
  obtain ⟨Cs,hCs,hs⟩ := smoothShortZeroCount_bound hw hη (by linarith [hw.a_high]) (by linarith) δ
  obtain ⟨Cl,hCl,hl⟩ := smoothLongZeroCount_twelfth hw hsigma hδ (by linarith)
    (ε:=ε/2) (by linarith) hη (by positivity) h12
  have hslab : ∀ᶠ T : ℝ in atTop,
      (zetaSlabCount σ T (2*T):ℝ) ≤ (Cs+Cl)*T^(3*a*(1-σ)+ε) := by
    filter_upwards [eventually_ge_atTop (1:ℝ),hs,hl] with T hT hsT hlT
    have hs' : (smoothShortZeroCount η σ a δ T:ℝ) ≤ Cs*T^(3*a*(1-σ)+ε) := hsT.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT (by linarith)) hCs.le)
    have hl' : (smoothLongZeroCount η σ a δ T:ℝ) ≤ Cl*T^(3*a*(1-σ)+ε) := hlT.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT (by linarith)) hCl.le)
    rw [smooth_zeroCount_partition η σ a δ T,Nat.cast_add]
    nlinarith only [hs',hl']
  have hp : 0 < 3*a*(1-σ)+ε := by
    have hh : 0 < 3*a*(1-σ) := mul_pos (mul_pos (by norm_num) ha) (by linarith [hw.sigma_high])
    linarith
  exact zetaDensity_bound_of_eventual_slabs hp (by positivity : 0 < Cs+Cl) hslab

/-- The portion of the first solid right-hand branch supplied by the native
twelfth moment. The exact full target ends at29359/37574; its small remaining
piece requires the stronger critical-line tail and is not claimed here. -/
theorem density_first_twelfth {σ ε : ℝ}
    (hl : 7/9 ≤ σ) (hr : σ ≤ 25/32) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(3*(1-σ)/(11*σ-7)+ε) := by
  have hw := right_quadratic_window_first σ hl (hr.trans (by norm_num : (25:ℝ)/32 ≤ 29359/37574))
  have hD : 0 < 11*σ-7 := by linarith
  have h12 : 2 ≤ (1/(11*σ-7))*(6*σ-3/2) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hD).mpr
    linarith only [hr]
  have he : 3*(1/(11*σ-7))*(1-σ)=3*(1-σ)/(11*σ-7) := by ring
  simpa only [he] using density_of_twelfth_window hw hl h12 hε

/-- The actual pictured .78 gain: the zero-density exponent is33/79. -/
theorem density_at_078 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount (39/50) T:ℝ) ≤ C*T^((33:ℝ)/79+ε) := by
  simpa only [show (3:ℝ)*(1-39/50)/(11*(39/50)-7)=33/79 by norm_num] using
    density_first_twelfth (σ:=39/50) (by norm_num) (by norm_num) hε

/-- Uniform monotonicity consequence of the new closed endpoint. -/
theorem density_plateau {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 25/32 ≤ σ → ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^((7:ℝ)/17+ε) := by
  have hh := density_first_twelfth (σ:=25/32) (by norm_num) le_rfl hε
  norm_num at hh
  obtain ⟨C,hC,hb⟩ := hh
  refine ⟨C,hC,?_⟩
  intro σ hσ T hT
  exact (show (zetaDensityCount σ T:ℝ) ≤ (zetaDensityCount (25/32) T:ℝ) by
    exact_mod_cast zetaDensityCount_mono hσ le_rfl).trans (hb T hT)

end Montgomery.RationalMoment.RightDetector
