module
public import GuthMaynard.Improvement.SourceReproducingKernel

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped FourierTransform SchwartzMap
namespace GuthMaynard.Improvement

/-- The nonnegative actual reproducing weight. Smoothness of its norm is
not assumed; the Schwartz kernel supplies arbitrary decay. -/
def sourceQuarticWeight (t : ℝ) : ℝ := ‖sourceReproducingKernel t‖

theorem source_quartic_weight_decay (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t, sourceQuarticWeight t ≤ C/(1+|t|)^q := by
  let C := 2^q*(Finset.Iic (q,0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) sourceReproducingKernel
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C+1,by positivity,?_⟩
  intro t
  have hh := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (q,0)) le_rfl le_rfl sourceReproducingKernel t
  simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at hh
  apply (le_div_iff₀ (by positivity : 0 < (1+|t|)^q)).mpr
  dsimp [sourceQuarticWeight]
  have he : (1+|t|)^q*‖sourceReproducingKernel t‖ ≤ C := hh
  nlinarith

/-- Bounded overlap is the audited separated-decay packing theorem,
with one constant for every finite one-separated set. -/
theorem source_quartic_weight_overlap :
    ∃ C : ℝ, 0 < C ∧ ∀ W : Finset ℝ, MathCollab.Density.oneSeparated W →
      ∀ t : ℝ, (∑ w ∈ W, sourceQuarticWeight (t-w)) ≤ C := by
  obtain ⟨D,hD,hd⟩ := source_quartic_weight_decay 2
  refine ⟨D*MathCollab.Density.separationMass+1,?_,?_⟩
  · have hm := MathCollab.Density.separationMass_nonneg
    positivity
  intro W hW t
  calc
    _ ≤ ∑ w ∈ W, D/(1+|t-w|)^2 := Finset.sum_le_sum (fun w _ => hd (t-w))
    _ = D*(∑ w ∈ W, 1/(1+|t-w|)^2) := by rw [Finset.mul_sum]; simp only [mul_one_div]
    _ ≤ D*MathCollab.Density.separationMass :=
      mul_le_mul_of_nonneg_left (MathCollab.Density.separated_decay_row hW t) hD.le
    _ ≤ _ := by linarith

/-- Every weighted polynomial moment is integrable by the fixed L1
kernel and finite-sum boundedness, with no global L1 claim for D. -/
theorem source_quartic_weighted_integrable (N : ℝ) (a : ℕ → ℂ) (w : ℝ) (q : ℕ) :
    Integrable (fun t => sourceQuarticWeight (t-w)*‖boundedPolynomial N a t‖^q) := by
  obtain ⟨hc,hb⟩ := boundedPolynomial_regular N a
  have hi : Integrable (fun t => sourceQuarticWeight (t-w)) :=
    (sourceReproducingKernel.integrable.comp_sub_right w).norm
  apply hi.mul_bdd (hc.norm.pow q).aestronglyMeasurable (c := (∑ n ∈ sourceRatioIndices N, ‖a n‖)^q)
  filter_upwards with t
  simp only [Pi.pow_apply,Real.norm_eq_abs,abs_pow,abs_norm]
  exact pow_le_pow_left₀ (norm_nonneg _) (hb t) q

/-- Actual quartic reproduction follows by two applications of the audited
weighted Cauchy--Schwarz theorem. -/
theorem boundedPolynomial_quartic_reproduce {N : ℝ} (hN : 0 < N)
    (a : ℕ → ℂ) (w : ℝ) :
    ‖boundedPolynomial N a w‖^4 ≤ (∫ s, sourceQuarticWeight s)^3*
      ∫ t, sourceQuarticWeight (t-w)*‖boundedPolynomial N a t‖^4 := by
  obtain ⟨hc,hb⟩ := boundedPolynomial_regular N a
  have hi : Integrable (fun t => sourceReproducingKernel (t-w)) :=
    sourceReproducingKernel.integrable.comp_sub_right w
  have hfirst := MathCollab.Density.norm_integral_mul_sq_le hi hc.aestronglyMeasurable hb
  rw [← boundedPolynomial_reproduce hN a w] at hfirst
  have hmass : (∫ t, sourceQuarticWeight (t-w)) = ∫ t, sourceQuarticWeight t :=
    integral_sub_right_eq_self _ w
  change ‖boundedPolynomial N a w‖^2 ≤
    (∫ t, sourceQuarticWeight (t-w))*(∫ t, sourceQuarticWeight (t-w)*‖boundedPolynomial N a t‖^2) at hfirst
  rw [hmass] at hfirst
  have hsecond := MathCollab.Density.weighted_integral_sq_le
    (ρ := fun t => sourceQuarticWeight (t-w)) (f := fun t => ‖boundedPolynomial N a t‖^2)
    (fun t => norm_nonneg (sourceReproducingKernel (t-w))) hi.norm
    (source_quartic_weighted_integrable N a w 2)
    (show Integrable (fun t => sourceQuarticWeight (t-w)*(‖boundedPolynomial N a t‖^2)^2) volume by
      simpa only [← pow_mul] using source_quartic_weighted_integrable N a w 4)
  rw [hmass] at hsecond
  have h0 : 0 ≤ ∫ s, sourceQuarticWeight s := integral_nonneg (fun s => norm_nonneg _)
  have hsq := pow_le_pow_left₀ (sq_nonneg _) hfirst 2
  have hh := mul_le_mul_of_nonneg_left hsecond (sq_nonneg (∫ s, sourceQuarticWeight s))
  simp only [← pow_mul] at hsq hh
  nlinarith

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.source_quartic_weight_decay
#print axioms GuthMaynard.Improvement.source_quartic_weight_overlap
#print axioms GuthMaynard.Improvement.source_quartic_weighted_integrable
#print axioms GuthMaynard.Improvement.boundedPolynomial_quartic_reproduce
