module
public import QuadraticFiniteLargeValues

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

lemma quadratic_mass_scalar {m P b k Z : ℝ}
    (hm : 0 ≤ m) (hP : 0 < P) (_hb : 0 ≤ b) (hk : 0 < k)
    (hgate : k*(max (m/P-b) 0)^2 ≤ Z) :
    m^2 ≤ 4*P^2*(b^2+Z/k) := by
  have hZ : 0 ≤ Z := (by positivity : 0 ≤ k*(max (m/P-b) 0)^2).trans hgate
  have hZk : 0 ≤ Z/k := by positivity
  have hlevel : 0 ≤ m/P := by positivity
  have hsq : (m/P)^2 ≤ 4*(b^2+Z/k) := by
    by_cases hh : m/P ≤ 2*b
    · have hh' := pow_le_pow_left₀ hlevel hh 2
      nlinarith only [hh',hZk]
    · have hmax : (m/P)/2 ≤ max (m/P-b) 0 := by
        exact (by linarith only [hh] : (m/P)/2 ≤ m/P-b).trans (le_max_left _ _)
      have hmaxsq := pow_le_pow_left₀ (by positivity : 0 ≤ (m/P)/2) hmax 2
      have hbound : (max (m/P-b) 0)^2 ≤ Z/k := (le_div_iff₀ hk).mpr (by nlinarith only [hgate])
      nlinarith only [hmaxsq,hbound,sq_nonneg b]
  have he : P^2*(m/P)^2=m^2 := by field_simp
  calc
    _ = P^2*(m/P)^2 := he.symm
    _ ≤ P^2*(4*(b^2+Z/k)) := mul_le_mul_of_nonneg_left hsq (sq_nonneg P)
    _ = _ := by ring

end Montgomery.RationalMoment
