module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.RobertSargosNormalizationCoordinates

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                         

noncomputable section
namespace TaoTrudgianYang2025

def robertSargosGcdKey (p : RobertSargosPoint) : ℕ × ℕ :=
  (robertSargosCoefficientGcd p,robertSargosFrequencyGcd p)

end TaoTrudgianYang2025
