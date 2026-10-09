/- The interval-translation argument is adapted from the user-owned task6
TypeIIFourthMomentReduction. Weighted overlap reuses audited Density.Packing;
no donor zero-family, tail assumption, or7/10 restriction is imported. -/
import GuthMaynard.Improvement.ShortGammaPacking
set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Set Filter MathCollab.Density
open scoped Topology
namespace GuthMaynard.Improvement

theorem short_setIntegral_comp_add_Icc (f : ℝ → ℝ) (u R : ℝ) :
    (∫ v in Icc (-R) R,f (u+v)) = ∫ t in Icc (u-R) (u+R),f t := by
  rw [← integral_indicator measurableSet_Icc,← integral_indicator measurableSet_Icc]
  have he : (Icc (-R) R).indicator (fun v => f (u+v)) =
      fun v => (Icc (u-R) (u+R)).indicator f (v+u) := by
    funext v
    by_cases hv : v ∈ Icc (-R) R
    · have ht : v+u ∈ Icc (u-R) (u+R) := ⟨by linarith [hv.1],by linarith [hv.2]⟩
      simp only [indicator_of_mem hv,indicator_of_mem ht]
      congr 1
      ring
    · have ht : v+u ∉ Icc (u-R) (u+R) := by
        intro ht
        apply hv
        exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
      simp only [indicator_of_notMem hv,indicator_of_notMem ht]
  rw [he]
  exact integral_add_right_eq_self _ u

/-- Actual Gamma windows have bounded total overlap for every one-separated
family, even when each representative has a different real part. -/
theorem short_typeII_window_packing :
    ∃ B : ℝ, 0 < B ∧ ∀ H : ℝ, 0 ≤ H → ∀ (W : Finset ℝ) (ρ : ℝ → ℂ),
      oneSeparated W → (∀ u ∈ W,u ∈ Icc H (2*H)) →
      (∀ u ∈ W,9/13 ≤ (ρ u).re ∧ (ρ u).re ≤ 1) →
      (∑ u ∈ W, ∫ v in Icc (-(H/2)) (H/2),
        ‖Complex.Gamma (((1/2-(ρ u).re:ℝ):ℂ)+(v:ℂ)*I)‖*(shortTwistedNorm H (u+v))^4) ≤
        B*(∫ t in Icc (H/2) (3*H),(shortTwistedNorm H t)^4) := by
  obtain ⟨K,hK,hk⟩ := short_gamma_decay
  refine ⟨K*separationMass+1,by have hm := separationMass_nonneg; positivity,?_⟩
  intro H hH W ρ hsep hw hβ
  let F := fun t => (shortTwistedNorm H t)^4
  let q := fun u t : ℝ => K/(1+|t-u|)^2
  have hf : Continuous F := (shortTwistedNorm_continuous H).pow 4
  have hf0 (t : ℝ) : 0 ≤ F t := by dsimp [F]; positivity
  have hq (u : ℝ) : Continuous (q u) := by
    dsimp [q]
    exact continuous_const.div ((continuous_const.add (continuous_id.sub continuous_const).abs).pow 2)
      (fun t => by positivity)
  have hi (u : ℝ) : IntegrableOn (fun t => q u t*F t) (Icc (H/2) (3*H)) :=
    ((hq u).mul hf).integrableOn_Icc
  have hone (u : ℝ) (hu : u ∈ W) :
      (∫ v in Icc (-(H/2)) (H/2),
        ‖Complex.Gamma (((1/2-(ρ u).re:ℝ):ℂ)+(v:ℂ)*I)‖*(shortTwistedNorm H (u+v))^4) ≤
      ∫ t in Icc (H/2) (3*H), q u t*F t := by
    let g := fun v : ℝ => ‖Complex.Gamma (((1/2-(ρ u).re:ℝ):ℂ)+(v:ℂ)*I)‖
    have hg : Continuous g := (short_continuous_Gamma_detector_strip
      (by linarith [(hβ u hu).2]) (by linarith [(hβ u hu).1])).norm
    have he : (∫ v in Icc (-(H/2)) (H/2),g v*F (u+v)) =
        ∫ t in Icc (u-H/2) (u+H/2),g (t-u)*F t := by
      have hh := short_setIntegral_comp_add_Icc (fun t => g (t-u)*F t) u (H/2)
      simpa only [add_sub_cancel_left] using hh
    change (∫ v in Icc (-(H/2)) (H/2),g v*F (u+v)) ≤ _
    rw [he]
    calc
      _ ≤ ∫ t in Icc (u-H/2) (u+H/2),q u t*F t := by
        apply setIntegral_mono_on (((hg.comp (continuous_id.sub continuous_const)).mul hf).integrableOn_Icc)
          (((hq u).mul hf).integrableOn_Icc) measurableSet_Icc
        intro t _
        exact mul_le_mul_of_nonneg_right (hk (ρ u).re (t-u) (hβ u hu).1 (hβ u hu).2) (hf0 t)
      _ ≤ _ := by
        apply setIntegral_mono_set (hi u) (Filter.Eventually.of_forall (fun t => by dsimp [q]; positivity))
        apply Filter.Eventually.of_forall
        intro t ht
        obtain ⟨hu0,hu1⟩ := hw u hu
        exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  calc
    _ ≤ ∑ u ∈ W, ∫ t in Icc (H/2) (3*H),q u t*F t := Finset.sum_le_sum hone
    _ = ∫ t in Icc (H/2) (3*H),∑ u ∈ W,q u t*F t := (integral_finsetSum W (fun u _ => hi u)).symm
    _ ≤ ∫ t in Icc (H/2) (3*H),(K*separationMass+1)*F t := by
      apply integral_mono (integrable_finsetSum W (fun u _ => hi u))
        (hf.integrableOn_Icc.const_mul _)
      intro t
      dsimp only
      rw [← Finset.sum_mul]
      apply mul_le_mul_of_nonneg_right _ (hf0 t)
      have hh := mul_le_mul_of_nonneg_left (separated_decay_row hsep t) hK.le
      have he : (∑ u ∈ W,q u t)=K*(∑ u ∈ W,1/(1+|t-u|)^2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        dsimp [q]
        ring
      rw [he]
      linarith
    _ = _ := integral_const_mul _ _

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.short_setIntegral_comp_add_Icc
#print axioms GuthMaynard.Improvement.short_typeII_window_packing
