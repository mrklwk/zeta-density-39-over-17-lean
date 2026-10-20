module
public import Mathlib
public import GafniTao.FordVinogradovIntegral

@[expose] public section
open MeasureTheory Finset
open scoped BigOperators
namespace GafniTao
noncomputable section
theorem continuous_fordVinogradovWeylSum (k Q : ℕ) :
    Continuous (fordVinogradovWeylSum k Q) := by
  unfold fordVinogradovWeylSum fordVinogradovMonomial
  exact continuous_finsetSum _ fun n _ =>
    (UnitAddTorus.mFourier (fordVinogradovExponent n)).continuous

/-- The nonnegative torus integral of a power of the complete Weyl sum is
the corresponding literal finite solution count. -/
theorem ford_vinogradov_lintegral_mean_eq (s k Q : ℕ) :
    (∫⁻ α : UnitAddTorus (Fin k),
        (ENNReal.ofReal ‖fordVinogradovWeylSum k Q α‖) ^ (2 * s)
        ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) =
      (fordVinogradovMomentNat s k Q : ENNReal) := by
  have hint : Integrable (fun α : UnitAddTorus (Fin k) =>
      ‖fordVinogradovWeylSum k Q α‖ ^ (2 * s))
      (Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) := by
    rw [← integrableOn_univ]
    apply ContinuousOn.integrableOn_compact isCompact_univ
    exact ((continuous_fordVinogradovWeylSum k Q).norm.pow (2 * s)).continuousOn
  calc
    (∫⁻ α : UnitAddTorus (Fin k),
        (ENNReal.ofReal ‖fordVinogradovWeylSum k Q α‖) ^ (2 * s)
        ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) =
        ∫⁻ α : UnitAddTorus (Fin k), ENNReal.ofReal
          (‖fordVinogradovWeylSum k Q α‖ ^ (2 * s))
          ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle) := by
      apply lintegral_congr
      intro α
      rw [ENNReal.ofReal_pow (norm_nonneg _)]
    _ = ENNReal.ofReal (∫ α : UnitAddTorus (Fin k),
          ‖fordVinogradovWeylSum k Q α‖ ^ (2 * s)
          ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) :=
      (ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun _ => by positivity)).symm
    _ = (fordVinogradovMomentNat s k Q : ENNReal) := by
      rw [ford_vinogradov_torus_real_mean_eq]
      norm_num


end
end GafniTao
