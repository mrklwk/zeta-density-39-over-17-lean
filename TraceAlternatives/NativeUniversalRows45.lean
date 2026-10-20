module
public import TraceAlternatives.PhysicalUniversalActualDensity
public import TraceAlternatives.NativeCubeRows34
public import LaterPairs.NativeSharpRow5Suffix

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

theorem universal_row5_tail_budgets {σ : ℝ}
    (hlo : 2018/2375 ≤ σ) (_hhi : σ ≤ 1959705/2298302) :
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

end Montgomery.RationalMoment

namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density

/-- Full original closed fourth segment, actual symmetric zeta-zero
multiplicity, arbitrary positive epsilon and every real height at least2. -/
theorem density_universal_row4 {σ ε : ℝ}
    (hlo : 7873/9370 ≤ σ) (hhi : σ ≤ 2018/2375) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ T : ℝ, 2≤T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(1261710*(1-σ)/(1447460*σ-465509)+ε) := by
  obtain ⟨hf,hs⟩ := cube_row4_tail_budgets hlo hhi
  simpa only [cube_row4_density_exponent] using
    density_of_pair_universal_window TaoTrudgianYang2025.exponentPair_BTTY3 (by norm_num)
      (physicalDetectorWindow_row4 hlo hhi) (universalCountWindow_row4 hlo hhi) hf hs hε

/-- Full original closed fifth segment. The cutoff and retained quadratic
cardinality term are discharged inside the actual count producer. -/
theorem density_universal_row5 {σ ε : ℝ}
    (hlo : 2018/2375 ≤ σ) (hhi : σ ≤ 1959705/2298302) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ T : ℝ, 2≤T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(3066*(1-σ)/(3616*σ-1215)+ε) := by
  obtain ⟨hf,hs⟩ := universal_row5_tail_budgets hlo hhi
  simpa only [sharp_row5_density_exponent] using
    density_of_pair_universal_window TaoTrudgianYang2025.exponentPair_BATY2 (by norm_num)
      (physicalDetectorWindow_row5 hlo hhi) (universalCountWindow_row5 hlo hhi) hf hs hε

end Montgomery.RationalMoment.RightDetector.Physical
