module
public import GafniTao.FordLemma51Fibers

@[expose] public section
noncomputable section
open scoped ComplexConjugate
namespace GafniTao
theorem conj_fordAdditiveCharacter (x : ℝ) :
    conj (fordAdditiveCharacter x) = fordAdditiveCharacter (-x) := by
  unfold fordAdditiveCharacter
  calc
    conj (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) =
        Complex.exp (conj (2 * Real.pi * Complex.I * (x : ℂ))) :=
      (Complex.exp_conj (2 * Real.pi * Complex.I * (x : ℂ))).symm
    _ = Complex.exp (2 * Real.pi * Complex.I * ((-x : ℝ) : ℂ)) := by
      congr 1
      rw [map_mul, map_mul, map_mul]
      simp only [map_ofNat, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring


end GafniTao
