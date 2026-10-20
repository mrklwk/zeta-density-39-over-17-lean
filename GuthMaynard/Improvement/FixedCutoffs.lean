module
public import MathCollab.Density.ComparisonCutoff

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace GuthMaynard.Improvement

/-- Squaring any existing reflection cutoff, without constructing a new bump. -/
def squareReflectionCutoff (w : MathCollab.Density.ReflectionCutoff) : MathCollab.Density.ReflectionCutoff where
  toFun x := w x^2
  smooth := w.smooth.pow 2
  support := by
    simpa only [pow_two] using (tsupport_mul_subset_left (f := w) (g := w)).trans w.support

theorem squareReflectionCutoff_apply (w : MathCollab.Density.ReflectionCutoff) (x : ℝ) :
    squareReflectionCutoff w x = w x^2 := rfl

/-- The actual audited comparison cutoff inherits the bump's upper bound.
This property does not follow from the abstract ComparisonCutoff structure alone. -/
theorem comparisonCutoff_le_one (x : ℝ) : MathCollab.Density.comparisonCutoff x ≤ 1 := by
  let f : ContDiffBump (5/2:ℝ) :=
    { rIn := 3/2, rOut := 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  change f x ≤ 1
  exact f.le_one

/-- The fixed squared spatial cutoff used by the actual row and mixed trace. -/
def fixedSquaredCutoff : MathCollab.Density.ReflectionCutoff :=
  squareReflectionCutoff MathCollab.Density.comparisonCutoff.toReflectionCutoff

theorem fixedSquaredCutoff_bounds (x : ℝ) : 0 ≤ fixedSquaredCutoff x ∧ fixedSquaredCutoff x ≤ 1 := by
  change 0 ≤ MathCollab.Density.comparisonCutoff x^2 ∧ MathCollab.Density.comparisonCutoff x^2 ≤ 1
  have h0 := MathCollab.Density.comparisonCutoff.nonneg x
  have h1 := comparisonCutoff_le_one x
  constructor
  · positivity
  · nlinarith

theorem fixedSquaredCutoff_one {x : ℝ} (hx : x ∈ Icc (1:ℝ) 4) : fixedSquaredCutoff x=1 := by
  change MathCollab.Density.comparisonCutoff x^2=1
  rw [MathCollab.Density.comparisonCutoff.one_on x hx]
  norm_num

/-- Shift the audited fixed bump; no new cutoff existence theorem is required. -/
def fixedTimeCutoff (s : ℝ) : ℝ := MathCollab.Density.comparisonCutoff (s+2)

theorem fixedTimeCutoff_smooth : ContDiff ℝ ∞ fixedTimeCutoff :=
  MathCollab.Density.comparisonCutoff.smooth.comp (contDiff_id.add contDiff_const)

theorem fixedTimeCutoff_bounds (s : ℝ) : 0 ≤ fixedTimeCutoff s ∧ fixedTimeCutoff s ≤ 1 :=
  ⟨MathCollab.Density.comparisonCutoff.nonneg _,comparisonCutoff_le_one _⟩

theorem fixedTimeCutoff_one {s : ℝ} (hs : s ∈ Icc (-1:ℝ) 2) : fixedTimeCutoff s=1 := by
  apply MathCollab.Density.comparisonCutoff.one_on
  exact ⟨by linarith [hs.1],by linarith [hs.2]⟩

theorem fixedTimeCutoff_support : tsupport fixedTimeCutoff ⊆ Icc (-2:ℝ) 3 := by
  apply closure_minimal _ isClosed_Icc
  intro s hs
  have hh : s+2 ∈ tsupport MathCollab.Density.comparisonCutoff :=
    subset_closure (show s+2 ∈ Function.support MathCollab.Density.comparisonCutoff from hs)
  have hb := MathCollab.Density.comparisonCutoff.support hh
  exact ⟨by linarith [hb.1],by linarith [hb.2]⟩

theorem fixedTimeCutoff_compact : HasCompactSupport fixedTimeCutoff :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) fixedTimeCutoff_support

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.squareReflectionCutoff_apply
#print axioms GuthMaynard.Improvement.comparisonCutoff_le_one
#print axioms GuthMaynard.Improvement.fixedSquaredCutoff_bounds
#print axioms GuthMaynard.Improvement.fixedSquaredCutoff_one
#print axioms GuthMaynard.Improvement.fixedTimeCutoff_smooth
#print axioms GuthMaynard.Improvement.fixedTimeCutoff_bounds
#print axioms GuthMaynard.Improvement.fixedTimeCutoff_one
#print axioms GuthMaynard.Improvement.fixedTimeCutoff_support
#print axioms GuthMaynard.Improvement.fixedTimeCutoff_compact
