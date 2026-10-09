module
public import GuthMaynard.Improvement.GlobalDensityConditional
public import GuthMaynard.Improvement.NativeDensitySourceBridge
public import GuthMaynard.NativeSource.GuthMaynard.ClassicalEndpointDensity

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- Actual Ingham estimate on the complementary lower strip. The native
positive-slab proof, dyadic transfer, and exact multiplicity-count bridge
supply every analytic input. Constants may depend on sigma and epsilon. -/
theorem ingham_lower_density : InghamLowerDensity := by
  intro σ hσLower hσUpper ε hε
  have hσ : 0 < σ := by linarith
  have hp : 0 ≤ 3 * (1 - σ) / (2 - σ) :=
    div_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
  apply native_density_epsilon_bound hσ hp _ hε
  rcases hσLower.eq_or_lt with hHalf | hInterior
  · subst σ
    exact NativeMoment.ingham_zero_density_at_half_native
  · exact NativeMoment.dyadicToGlobalZeroCount σ (3 * (1 - σ) / (2 - σ)) hp
      (NativeMoment.ingham_endpoint_positive_slab_native hInterior (by linarith))

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.ingham_lower_density
