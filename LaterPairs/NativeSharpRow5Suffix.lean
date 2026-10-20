module
public import LaterPairs.NativeSharpRow6
public import LaterPairs.SharpPreservedCurveComparisons

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace TaoTrudgianYang2025

/-- The genuine B A image of the native Sargos D Bourgain pair. -/
theorem exponentPair_BATY2 : ExponentPair (593/1736) (235/434) := by
  convert CubicJointCount.exponentPair_sargosD_bourgain.aProcess.bProcess using 1 <;> norm_num

end TaoTrudgianYang2025

namespace Montgomery.RationalMoment

/-- The already proved sharp trace controls the stated suffix of row5.
This theorem deliberately does not assert the missing full row5 window. -/
theorem sharpCountWindow_row5_suffix {σ : ℝ}
    (hlo : 5553/6526 ≤ σ) (hhi : σ ≤ 1959705/2298302) :
    SharpCountWindow σ (3066/(10848*σ-3645)) := by
  have hd : 0 < 10848*σ-3645 := by linarith
  have hσ : 4/5 ≤ σ := by linarith
  have ha : 1/2 ≤ 3066/(10848*σ-3645) := by
    apply (le_div_iff₀ hd).mpr
    linarith
  refine ⟨hσ,by linarith,ha,?_,?_⟩
  · apply (div_lt_iff₀ hd).mpr
    linarith
  · intro x hxa j i
    have hb : 0 ≤ gmTraceEnergyMargin σ (3066/(10848*σ-3645))
        (3066/(10848*σ-3645)) j i := by
      have he := gmTraceEnergyMargin_affine_length σ 3066 10848 3645 1 hd.ne' j i
      simp only [one_mul] at he
      rw [he]
      apply div_nonneg _ hd.le
      fin_cases j <;> fin_cases i <;>
        norm_num [gmTraceA,gmTraceB,gmTraceG,gmTraceD,
          gmEnergyU,gmEnergyV,gmEnergyW,gmEnergyR] <;> linarith
    exact hb.trans (gmTraceEnergyMargin_mono_length hσ hxa j i)

/-- Exact obstruction for this sharp-trace budget below the suffix endpoint;
it is a budget identity, not a counterexample to a zero-density theorem. -/
theorem sharp_row5_limiting_margin {σ : ℝ} (hσ : 2018/2375 ≤ σ) :
    gmTraceEnergyMargin σ (3066/(10848*σ-3645))
      (3066/(10848*σ-3645)) 2 0 =
      9*(6526*σ-5553)/(20*(10848*σ-3645)) := by
  have hd : 0 < 10848*σ-3645 := by linarith
  have he := gmTraceEnergyMargin_affine_length σ 3066 10848 3645 1 hd.ne' 2 0
  simp only [one_mul] at he
  rw [he]
  norm_num [gmTraceA,gmTraceB,gmTraceG,gmTraceD,
    gmEnergyU,gmEnergyV,gmEnergyW,gmEnergyR]
  field_simp [hd.ne']
  ring

/-- Below this endpoint the specific sharp-GM budget really fails.
No failure of the requested density conclusion is asserted. -/
theorem sharp_row5_budget_fails_below_suffix {σ : ℝ}
    (hlo : 2018/2375 ≤ σ) (hhi : σ < 5553/6526) :
    ¬ SharpCountWindow σ (3066/(10848*σ-3645)) := by
  intro hw
  have hb := hw.budgets (3066/(10848*σ-3645)) le_rfl 2 0
  rw [sharp_row5_limiting_margin hlo] at hb
  have hd : 0 < 10848*σ-3645 := by linarith
  have hn : 9*(6526*σ-5553)/(20*(10848*σ-3645)) < 0 :=
    div_neg_of_neg_of_pos (by linarith) (by positivity)
  exact (not_lt_of_ge hb) hn

theorem sharp_row5_tail_budgets {σ : ℝ}
    (hlo : 5553/6526 ≤ σ) (_hhi : σ ≤ 1959705/2298302) :
    let a : ℝ := 3066/(10848*σ-3645)
    1-6*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ) ∧
    1+(235/434:ℝ)/(593/1736)-
      (4+(2+4*(235/434))/(593/1736))*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ) := by
  dsimp only
  have hd : 0 < 10848*σ-3645 := by linarith
  rw [show (1:ℝ)+(235/434)/(593/1736)=1533/593 by norm_num,
    show (4:ℝ)+(2+4*(235/434))/(593/1736)=9604/593 by norm_num]
  apply tail_budgets_of_fraction hd
  · linarith
  · nlinarith

theorem sharp_row5_density_exponent {σ : ℝ} :
    3*(3066/(10848*σ-3645))*(1-σ) = 3066*(1-σ)/(3616*σ-1215) := by
  have hd : 10848*σ-3645 = 3*(3616*σ-1215) := by ring
  calc
    _ = (3*3066/(3*(3616*σ-1215)))*(1-σ) := by rw [hd]; ring
    _ = (3066/(3616*σ-1215))*(1-σ) := by
      rw [mul_div_mul_left _ _ (by norm_num : (3:ℝ) ≠ 0)]
    _ = _ := div_mul_eq_mul_div _ _ _

theorem sharp_row5_suffix_preserved_exponent_comparison {σ : ℝ}
    (hlo : 5553/6526 ≤ σ) (hhi : σ ≤ 1959705/2298302) :
    3066*(1-σ)/(3616*σ-1215) < Montgomery.PeakTailDensity.exponent σ := by
  rw [preserved_peak_tail_exponent_on_sharp_rows (by linarith)]
  have hg : 0 < 1-σ := by linarith
  have hd : 0 < 3616*σ-1215 := by linarith
  apply (div_lt_div_iff₀ hd (show 0 < 3*σ+1 by positivity)).mpr
  have hm : 3066*(3*σ+1) < 6*(3616*σ-1215) := by linarith
  have hh := mul_lt_mul_of_pos_left hm hg
  nlinarith only [hh]

theorem sharp_row5_suffix_palomar_exponent_comparison {σ : ℝ}
    (hlo : 5553/6526 ≤ σ) (hhi : σ ≤ 1959705/2298302) :
    3066*(1-σ)/(3616*σ-1215) < 3*(1-σ)/(2*σ) := by
  have hs : 0 < σ := by linarith
  have hg : 0 < 1-σ := by linarith
  have hd : 0 < 3616*σ-1215 := by linarith
  apply (div_lt_div_iff₀ hd (show 0 < 2*σ by positivity)).mpr
  have hm : 3066*(2*σ) < 3*(3616*σ-1215) := by linarith
  have hh := mul_lt_mul_of_pos_left hm hg
  nlinarith only [hh]

end Montgomery.RationalMoment

namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density.Stronger MathCollab.Density

/-- Actual zeros on an explicit suffix, with the original requested row5 exponent. -/
theorem density_sharp_row5_suffix {σ ε : ℝ}
    (hlo : 5553/6526 ≤ σ) (hhi : σ ≤ 1959705/2298302) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(3066*(1-σ)/(3616*σ-1215)+ε) := by
  obtain ⟨hf,hs⟩ := sharp_row5_tail_budgets hlo hhi
  simpa only [sharp_row5_density_exponent] using
    density_of_pair_sharp_window TaoTrudgianYang2025.exponentPair_BATY2
      (by norm_num) (physicalDetectorWindow_row5 (by linarith) hhi)
      (sharpCountWindow_row5_suffix hlo hhi) hf hs hε

end Montgomery.RationalMoment.RightDetector.Physical
