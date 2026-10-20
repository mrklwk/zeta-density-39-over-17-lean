module
public import CenteredShortTrace
public import MathCollab.Density.ComparisonCutoff
public import MathCollab.Density.Packing

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
namespace Montgomery.RationalMoment

/-- Finite Schur control of a mixed trace. No commutation of the matrices
is required, and the statement applies to arbitrary complex H. -/
theorem matrix_mixed_trace_schur {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C H : Matrix ι ι ℂ) {B : ℝ} (_hB : 0 ≤ B)
    (hrow : ∀ i, ∑ j, ‖C i j‖ ≤ B) (hcol : ∀ j, ∑ i, ‖C i j‖ ≤ B) :
    ‖Matrix.trace (C*H*H)‖ ≤ B*(∑ i, ∑ j, ‖H i j‖^2) := by
  have hfirst : (∑ i, ∑ j, ∑ k, ‖C i j‖*‖H j k‖^2) ≤
      B*(∑ j, ∑ k, ‖H j k‖^2) := by
    rw [sum_comm]
    simp_rw [← mul_sum,← sum_mul]
    rw [mul_sum]
    exact sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hcol j)
      (sum_nonneg (fun _ _ => sq_nonneg _)))
  have hsecond : (∑ i, ∑ j, ∑ k, ‖C i j‖*‖H k i‖^2) ≤
      B*(∑ i, ∑ j, ‖H i j‖^2) := by
    simp_rw [← mul_sum,← sum_mul]
    calc
      _ ≤ ∑ i, B*(∑ k, ‖H k i‖^2) := sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_right (hrow i) (sum_nonneg (fun _ _ => sq_nonneg _)))
      _ = _ := by rw [← mul_sum,sum_comm]
  have he : Matrix.trace (C*H*H) = ∑ i, ∑ j, ∑ k, C i j*H j k*H k i := by
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,sum_mul]
    apply sum_congr rfl
    intro i _
    rw [sum_comm]
  have hsum (f g : ι → ι → ι → ℝ) :
      (∑ i, ∑ j, ∑ k, (f i j k+g i j k)/2) =
        ((∑ i, ∑ j, ∑ k, f i j k)+(∑ i, ∑ j, ∑ k, g i j k))/2 := by
    simp only [div_eq_mul_inv,add_mul,Finset.sum_add_distrib,← Finset.sum_mul]
  rw [he]
  calc
    _ ≤ ∑ i, ∑ j, ∑ k, ‖C i j*H j k*H k i‖ :=
      (norm_sum_le _ _).trans (sum_le_sum (fun _ _ =>
        (norm_sum_le _ _).trans (sum_le_sum (fun _ _ => norm_sum_le _ _))))
    _ ≤ ∑ i, ∑ j, ∑ k, (‖C i j‖*‖H j k‖^2+‖C i j‖*‖H k i‖^2)/2 := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro j _
      apply sum_le_sum
      intro k _
      simp only [norm_mul]
      nlinarith [mul_nonneg (norm_nonneg (C i j)) (sq_nonneg (‖H j k‖-‖H k i‖))]
    _ = ((∑ i, ∑ j, ∑ k, ‖C i j‖*‖H j k‖^2)+
        (∑ i, ∑ j, ∑ k, ‖C i j‖*‖H k i‖^2))/2 := by
      exact hsum _ _
    _ ≤ _ := by linarith

/-- The actual continuous Gram term has a uniform row and column bound
on every one-separated set. The constant does not depend on |W|. -/
theorem cutoff_continuous_schur (w : MathCollab.Density.ReflectionCutoff) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ L : ℝ, 0 ≤ L → ∀ W : Finset ℝ,
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t : W, ∑ u : W, ‖cutoffContinuousMatrix w L W t u‖ ≤ B*L) ∧
      (∀ u : W, ∑ t : W, ‖cutoffContinuousMatrix w L W t u‖ ≤ B*L) := by
  obtain ⟨B,hB,hdec⟩ := MathCollab.Density.cutoffIntegral_quadratic_decay (reflectionSquare w)
  refine ⟨B*MathCollab.Density.separationMass,
    mul_nonneg hB MathCollab.Density.separationMass_nonneg,?_⟩
  intro L hL W hsep
  have hpoint (t u : W) : ‖cutoffContinuousMatrix w L W t u‖ ≤
      L*B*(1/(1+|(t:ℝ)-u|)^2) := by
    simp only [cutoffContinuousMatrix,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hL]
    have hh := mul_le_mul_of_nonneg_left (hdec ((t:ℝ)-u)) hL
    convert hh using 1; ring
  have hbound (t : W) : ∑ u : W, L*B*(1/(1+|(t:ℝ)-u|)^2) ≤
      (B*MathCollab.Density.separationMass)*L := by
    rw [← mul_sum,Finset.sum_coe_sort W (fun u => 1/(1+|(t:ℝ)-u|)^2)]
    have hh := mul_le_mul_of_nonneg_left (MathCollab.Density.separated_decay_row hsep (t:ℝ))
      (mul_nonneg hL hB)
    convert hh using 1; ring
  constructor
  · intro t
    exact (sum_le_sum (fun u _ => hpoint t u)).trans (hbound t)
  · intro u
    calc
      _ ≤ ∑ t : W, L*B*(1/(1+|(u:ℝ)-t|)^2) := by
        apply sum_le_sum
        intro t _
        simpa only [abs_sub_comm] using hpoint t u
      _ ≤ _ := hbound u

/-- The mixed trace for the actual centered matrix has the required L^2
scale. No moment, reflection, Schur, or matrix-norm estimate is assumed. -/
theorem centered_mixed_trace_short_range (w : MathCollab.Density.ReflectionCutoff)
    {K : ℕ} (hK : 1 ≤ K) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ L : ℝ, 1 < T → 1 ≤ L → ∀ W : Finset ℝ,
      T^(((K:ℝ)+1)/(2*K+1)) ≤ W.card →
      (T/L)^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      ‖Matrix.trace (cutoffContinuousMatrix w L W*cutoffCenteredMatrix w L W*
        cutoffCenteredMatrix w L W)‖ ≤ C*T^η*L^2*(W.card:ℝ)^2 := by
  obtain ⟨B,hB,hschur⟩ := cutoff_continuous_schur w
  obtain ⟨C,hC,hbound⟩ := centered_energy_short_range (reflectionSquare w) hK hη
  refine ⟨1+B*C,by positivity,?_⟩
  intro T t₀ L hT hL W hR hlen hW hsep
  have hLp : 0 ≤ L := by linarith
  obtain ⟨hrow,hcol⟩ := hschur L hLp W hsep
  have hh := matrix_mixed_trace_schur (cutoffContinuousMatrix w L W) (cutoffCenteredMatrix w L W)
    (mul_nonneg hB hLp) hrow hcol
  have he : (∑ t : W, ∑ u : W, ‖cutoffCenteredMatrix w L W t u‖^2) =
      ∑ t ∈ W, ∑ u ∈ W, ‖MathCollab.Density.hKernel (reflectionSquare w) L (t-u)‖^2 := by
    simp only [cutoff_centered_entry]
    rw [Finset.sum_coe_sort W (fun t => ∑ u : W,
      ‖MathCollab.Density.hKernel (reflectionSquare w) L (t-(u:ℝ))‖^2)]
    apply sum_congr rfl
    intro t _
    exact Finset.sum_coe_sort W (fun u =>
      ‖MathCollab.Density.hKernel (reflectionSquare w) L (t-u)‖^2)
  rw [he] at hh
  calc
    _ ≤ (B*L)*(∑ t ∈ W, ∑ u ∈ W, ‖MathCollab.Density.hKernel (reflectionSquare w) L (t-u)‖^2) := hh
    _ ≤ (B*L)*(C*T^η*L*(W.card:ℝ)^2) := by
      apply mul_le_mul_of_nonneg_left (hbound T t₀ L hT hL W hR hlen hW hsep) (by positivity)
    _ = (B*C)*T^η*L^2*(W.card:ℝ)^2 := by ring
    _ ≤ _ := by gcongr; linarith

end Montgomery.RationalMoment
