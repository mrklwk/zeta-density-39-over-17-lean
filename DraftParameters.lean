module
public import Mathlib

@[expose] public section

/- These are parameter theorems only. No zero-density result is asserted
from the newer rational moment or trace estimates in this module. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Montgomery.DraftParameters

/-- Complete quadratic length-window budgets from the two lower bounds on a.
The equality p=3a(1-s) is retained in the statement. -/
theorem quadratic_window {s a x : ℝ}
    (hs : 3/4 < s) (hs' : s < 1) (_ha : 0 ≤ a) (ha' : a ≤ 2/3)
    (h₁ : 2 ≤ a*(3*s+1)) (h₂ : 1 ≤ a*(11*s-7))
    (hx : a ≤ x) (hx' : x ≤ 3*a/2) :
    let p := 3*a*(1-s)
    let ell := p+(2*s-1)*x
    x ≤ ell ∧ ell ≤ 1 ∧
    1 ≤ (3/2)*p+(6*s-4)*x ∧
    (1/4) ≤ (5/12)*p+(4*s-3)*x := by
  dsimp
  have ht : 0 ≤ (1-s)*(3*a-2*x) := mul_nonneg (by linarith) (by linarith)
  have hu : 0 ≤ (2*s-1)*(3*a/2-x) := mul_nonneg (by linarith) (by linarith)
  have hv : 0 ≤ (6*s-4)*(x-a) := mul_nonneg (by linarith) (by linarith)
  have hw : 0 ≤ (4*s-3)*(x-a) := mul_nonneg (by linarith) (by linarith)
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- The coefficient-one tail budget for the stated exponent pair is precisely
its reciprocal-affine detector constraint. This does not prove the tail input. -/
theorem tail_identity (s a : ℝ) :
    a*(6*(1+2*(122/243:ℝ))*s+6*(64/135:ℝ)-6*(122/243:ℝ)-3)
       -4*((64/135:ℝ)+(122/243:ℝ)) =
    (3*a*(4870*s-1283)-4744)/1215 := by ring

theorem quadratic_at_078 :
    (3*(1-(39/50:ℝ))/(11*(39/50)-7)) = 33/79 ∧
    (3*(1-(39/50:ℝ))/(2*(39/50)))-33/79 = 33/6162 ∧
    (81/193:ℝ)-33/79 = 30/15247 := by norm_num

theorem rational_at_075 :
    (255*(1-(3/4:ℝ))/(153*(3/4)+7)) = 255/487 ∧
    (6/11:ℝ)-255/487 = 117/5357 := by norm_num

end Montgomery.DraftParameters
#print axioms Montgomery.DraftParameters.quadratic_window
#print axioms Montgomery.DraftParameters.tail_identity
