import MathCollab.Density.GammaStrip
import MathCollab.Density.MollifierDirichlet
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace GuthMaynard.Improvement

/-- Correct negative Gamma strip, uniformly on the entire imaginary axis.
The singular dependence on the distance to zero is explicit. -/
theorem short_detector_gamma_bound {a : ℝ} (ha : 0 < a) (hahi : a ≤ 1/2) (u : ℝ) :
    ‖Complex.Gamma (((-a:ℝ):ℂ)+(u:ℂ)*Complex.I)‖ ≤
      (12/a)*(1+|u|)*Real.exp (-|u|) := by
  let z : ℂ := ((-a:ℝ):ℂ)+(u:ℂ)*Complex.I
  have hz : z ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp [z] at hr
    linarith
  have hlower : a ≤ ‖z‖ := by
    simpa [z,abs_of_pos ha] using Complex.abs_re_le_norm z
  have hrec := congrArg norm (Complex.Gamma_add_one z hz)
  rw [norm_mul] at hrec
  have hshift := MathCollab.Density.GammaBounds.norm_Gamma_positive_strip_le_exp
    (s := 1-a) (t := u) (by linarith) (by linarith)
  have he : z+1 = MathCollab.Density.GammaBounds.stripPoint (1-a) u := by
    dsimp [z,MathCollab.Density.GammaBounds.stripPoint]
    push_cast
    ring
  rw [← he,hrec] at hshift
  have hm : a*‖Complex.Gamma z‖ ≤ 12*(1+|u|)*Real.exp (-|u|) := by
    exact (mul_le_mul_of_nonneg_right hlower (norm_nonneg _)).trans hshift
  have hd := (le_div_iff₀ ha).mpr (show ‖Complex.Gamma z‖*a ≤
    12*(1+|u|)*Real.exp (-|u|) by nlinarith [hm])
  change ‖Complex.Gamma z‖ ≤ _
  convert hd using 1; ring

/-- Open classical analytic input, expressed with the actual floor-cutoff
Möbius polynomial and actual zeta function. This definition asserts no proof. -/
def ShortMobiusFourthMoment : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C H₀ : ℝ, 0 < C ∧ 2 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H →
    (∫ t in Set.Icc (H/2) (3*H),
      ‖riemannZeta ((1/2:ℂ)+(t:ℂ)*Complex.I) *
        MathCollab.Density.zetaMollifier (2*H^((1:ℝ)/100))
          ((1/2:ℂ)+(t:ℂ)*Complex.I)‖^4) ≤ C*H^(1+ε)

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.short_detector_gamma_bound
#print GuthMaynard.Improvement.ShortMobiusFourthMoment
