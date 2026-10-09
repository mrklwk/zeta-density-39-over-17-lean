module
public import GuthMaynard.Improvement.CenteredKernelBridge
public import MathCollab.Density.Reflection

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped FourierTransform
namespace GuthMaynard.Improvement

/-- Exact identification with the independently audited density mode integral.
No reflection estimate is assumed by this change of normalization. -/
theorem reflection_mode_fourier (w : MathCollab.Density.ReflectionCutoff) (s ξ : ℝ) :
    MathCollab.Density.modeIntegral (fun x => (w x:ℂ)) s ξ =
      𝓕 (logModulated (fun x => (w x:ℂ)) s) ξ := by
  rw [MathCollab.Density.modeIntegral,logModulated_fourier_integral]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    have hw : w x = 0 := image_eq_zero_of_notMem_tsupport (fun hw => by
      have hh := (w.support hw).1
      exact hx (by change 0 < x; linarith))
    simp [hw])]
  apply integral_congr_ae
  filter_upwards with x
  congr 1
  unfold phase mellinFrequency
  congr 1
  have he : 2*Real.pi*(s*(Real.log x/(2*Real.pi))-ξ*x) = s*Real.log x-2*Real.pi*ξ*x := by
    field_simp
  rw [he]

/-- The new actual centered kernel is literally the audited density hKernel,
with the same cutoff and scale; this is not a bound imported as a premise. -/
theorem centeredKernel_eq_density_hKernel (w : MathCollab.Density.ReflectionCutoff)
    {L : ℝ} (hL : 0 < L) (s : ℝ) :
    centeredKernel (fun x => (w x:ℂ)) (1/2) 5 L s = MathCollab.Density.hKernel w L s := by
  have hs : ∀ x, x ∉ Icc (1/2:ℝ) 5 → (w x:ℂ) = 0 := by
    intro x hx
    have hz : w x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (w.support hh))
    simp only [hz,Complex.ofReal_zero]
  rw [centeredKernel_poisson w.complex_smooth (by norm_num : (0:ℝ)<1/2)
    (by norm_num : (1/2:ℝ)≤5) hL hs,MathCollab.Density.hKernel_poisson w hL]
  congr 1
  apply tsum_congr
  intro m
  unfold MathCollab.Density.nonzeroMode
  rw [reflection_mode_fourier]
  simp only [mul_comm L]

/-- Reflection controls the true centered kernel on each positive shell.
The scalar error constant is fixed before all scales and frequencies. -/
theorem centeredKernel_reflection_shell (w : MathCollab.Density.ReflectionCutoff)
    {A : ℕ} (hA : 1 < A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L H v : ℝ, 0 < L → 0 < H → H ≤ v → v ≤ 2*H →
      ‖centeredKernel (fun x => (w x:ℂ)) (1/2) 5 L v‖^2 ≤
        (1000/Real.pi^2)*MathCollab.Density.mellinMass w*(L^2/H)*
          (∫ r, ‖MathCollab.Density.mellinLine (fun x => (w x:ℂ)) r‖*
            ‖MathCollab.Density.bandPhaseSum L H v r‖^2)+2*(K*L/L^A)^2 := by
  obtain ⟨K,hK,h⟩ := MathCollab.Density.uniform_fixedBand_and_diagonal_error w hA
  refine ⟨K,hK,?_⟩
  intro L H v hL hH hv hv2
  rw [centeredKernel_eq_density_hKernel w hL]
  have he := MathCollab.Density.hKernel_sq_le_band_error w L H v (K*L/L^A)
    (h L H v hL hH hv hv2).1
  have hb := MathCollab.Density.norm_bandContribution_sq_le w hL hH v
  calc
    _ ≤ 2*‖MathCollab.Density.bandContribution w L H v‖^2+2*(K*L/L^A)^2 := he
    _ ≤ 2*((500/Real.pi^2)*MathCollab.Density.mellinMass w*(L^2/H)*
        (∫ r, ‖MathCollab.Density.mellinLine (fun x => (w x:ℂ)) r‖*
          ‖MathCollab.Density.bandPhaseSum L H v r‖^2))+2*(K*L/L^A)^2 :=
      add_le_add (mul_le_mul_of_nonneg_left hb (by norm_num)) le_rfl
    _ = _ := by ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.reflection_mode_fourier
#print axioms GuthMaynard.Improvement.centeredKernel_eq_density_hKernel
#print axioms GuthMaynard.Improvement.centeredKernel_reflection_shell
