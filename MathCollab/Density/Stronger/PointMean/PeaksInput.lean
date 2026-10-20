module
/- Native point-mean producer for the actual finite-peak interface. -/
public import MathCollab.Density.Stronger.PointMean.Equation44
public import MathCollab.Density.Stronger.Peaks.Inputs

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.PointMean

/-- The analytic point-to-local-second-mean input is proved by the actual
Gamma-zeta-square contour and exponential-overlap chain. -/
theorem pointMeanInput_native : Peaks.PointMeanInput :=
  heathBrown_equation44_native

end MathCollab.Density.Stronger.PointMean
