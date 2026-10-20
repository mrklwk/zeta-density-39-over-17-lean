module

public import CountCore
public import MathCollab.Density.ZetaCounting

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal

public section

namespace LewkoDensityPalomar

/-- The independently defined Mathlib-only extended-real count agrees exactly
with the proof development's natural-valued density count, at every real
sigma and height. There is no analytic or finiteness assumption. -/
theorem zeroCount_eq_zetaDensityCount (σ T : ℝ) :
    zeroCount σ T = (MathCollab.Density.zetaDensityCount σ T : ℝ≥0∞) := by
  apply zeroCount_eq_finset σ T (MathCollab.Density.zetaZeroFinset σ (-T) T)
  intro ρ
  rw [MathCollab.Density.mem_zetaDensityFinset]
  simp only [MathCollab.Density.IsNontrivialZetaZero, and_assoc]

/-- A real-valued project count bound is mathematically equivalent to the
advertised extended-real bound whenever the proposed upper bound is
nonnegative. No `toReal` convention for infinity is used. -/
theorem zeroCount_le_iff_project (σ T B : ℝ) (hB : 0 ≤ B) :
    zeroCount σ T ≤ ENNReal.ofReal B ↔
      (MathCollab.Density.zetaDensityCount σ T : ℝ) ≤ B := by
  rw [zeroCount_eq_zetaDensityCount, ← ENNReal.ofReal_natCast,
    ENNReal.ofReal_le_ofReal_iff hB]

end LewkoDensityPalomar
