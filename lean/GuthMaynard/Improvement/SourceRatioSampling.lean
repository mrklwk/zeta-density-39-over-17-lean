import GuthMaynard.Improvement.SourceRatioAssembly
import GuthMaynard.Improvement.SamplingFourier
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Finset
open scoped FourierTransform
namespace GuthMaynard.Improvement

def sourceRatioFrequency (q : ℕ × ℕ) : ℝ := Real.log ((q.1:ℝ)/q.2)/(2*Real.pi)

/-- Primitive separation in the actual 2π-normalized Fourier frequency. -/
theorem source_ratio_frequency_separated (S : Finset (ℕ × ℕ)) {Y : ℝ}
    (hS : ∀ q ∈ S, 0 < q.1 ∧ 0 < q.2 ∧ q.1.Coprime q.2 ∧
      (q.1:ℝ) ≤ Y ∧ (q.2:ℝ) ≤ Y) :
    Pairwise (fun p q : S => (2*Real.pi*Y^2)⁻¹ ≤
      |sourceRatioFrequency p-sourceRatioFrequency q|) := by
  intro p q hpq
  obtain ⟨hp1,hp2,hpc,hpY,hpY'⟩ := hS p p.property
  obtain ⟨hq1,hq2,hqc,hqY,hqY'⟩ := hS q q.property
  have hh := primitive_log_ratio_separated hp1 hp2 hq1 hq2 hpc hqc
    (show (p.val.1,p.val.2) ≠ (q.val.1,q.val.2) by intro he; apply hpq; exact Subtype.ext he)
    hpY hpY' hqY hqY'
  unfold sourceRatioFrequency
  rw [← sub_div,abs_div,abs_of_pos (by positivity : 0 < 2*Real.pi)]
  simpa [mul_inv_rev,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using
    div_le_div_of_nonneg_right hh (by positivity : 0 ≤ 2*Real.pi)

/-- Actual square sampling on any finite primitive ratio family. -/
theorem source_ratio_fourier_square (S : Finset (ℕ × ℕ)) {Y : ℝ} (hY : 0 < Y)
    (hS : ∀ q ∈ S, 0 < q.1 ∧ 0 < q.2 ∧ q.1.Coprime q.2 ∧
      (q.1:ℝ) ≤ Y ∧ (q.2:ℝ) ≤ Y)
    {f : ℝ → ℂ} (h1 : Integrable f) (h2 : MemLp f 2)
    {R : ℝ} (hR : 0 ≤ R) (hs : Function.support f ⊆ Icc (-R) R) :
    (∑ q ∈ S, ‖𝓕 f (sourceRatioFrequency q)‖^2) ≤
      (2*Real.pi*Y^2+4*Real.pi*R)*(∫ t, ‖f t‖^2) := by
  have hh := sampling_fourier_square h1 h2 hR hs
    (fun q : S => sourceRatioFrequency q) (by positivity : 0 < (2*Real.pi*Y^2)⁻¹)
    (source_ratio_frequency_separated S hS)
  have he : (∑ q : S, ‖𝓕 f (sourceRatioFrequency q)‖^2) =
      ∑ q ∈ S, ‖𝓕 f (sourceRatioFrequency q)‖^2 :=
    Finset.sum_coe_sort S (fun q => ‖𝓕 f (sourceRatioFrequency q)‖^2)
  rw [← he]
  simpa only [inv_inv] using hh

/-- Squared multiplicity and genuine Fourier square sampling combine by
finite Cauchy--Schwarz; the height and moment factors remain separate. -/
theorem source_ratio_fourier_weighted_low (S : Finset (ℕ × ℕ)) {Y : ℝ} (hY : 0 < Y)
    (hS : ∀ q ∈ S, 0 < q.1 ∧ 0 < q.2 ∧ q.1.Coprime q.2 ∧
      (q.1:ℝ) ≤ Y ∧ (q.2:ℝ) ≤ Y) (w : ℕ × ℕ → ℝ) {W : ℝ}
    (hW : (∑ q ∈ S, (w q)^2) ≤ W)
    {f : ℝ → ℂ} (h1 : Integrable f) (h2 : MemLp f 2)
    {R : ℝ} (hR : 0 ≤ R) (hs : Function.support f ⊆ Icc (-R) R) :
    (∑ q ∈ S, w q*‖𝓕 f (sourceRatioFrequency q)‖) ≤
      Real.sqrt W * Real.sqrt ((2*Real.pi*Y^2+4*Real.pi*R)*(∫ t, ‖f t‖^2)) := by
  exact (Real.sum_mul_le_sqrt_mul_sqrt S w (fun q => ‖𝓕 f (sourceRatioFrequency q)‖)).trans
    (mul_le_mul (Real.sqrt_le_sqrt hW)
      (Real.sqrt_le_sqrt (source_ratio_fourier_square S hY hS h1 h2 hR hs))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- High-height sampling with literal normalized frequencies and the
original restricted Fourier L1 integral. -/
theorem source_ratio_fourier_first (S : Finset (ℕ × ℕ)) {Y : ℝ} (hY : 1 ≤ Y)
    (hS : ∀ q ∈ S, 0 < q.1 ∧ 0 < q.2 ∧ q.1.Coprime q.2 ∧
      (q.1:ℝ) ≤ Y ∧ (q.2:ℝ) ≤ Y)
    (hband : ∀ q ∈ S, |sourceRatioFrequency q| ≤ 1)
    {f : ℝ → ℂ} (h1 : Integrable f) (h2 : MemLp f 2)
    {R : ℝ} (hR : 0 ≤ R) (hs : Function.support f ⊆ Icc (-R) R) :
    (∑ q ∈ S, ‖𝓕 f (sourceRatioFrequency q)‖) ≤
      2*Real.pi*Y^2*(∫ ξ in Icc (-2:ℝ) 2, ‖𝓕 f ξ‖)+
      4*Real.pi*R*Real.sqrt (∫ t, ‖f t‖^2) := by
  have hd : 0 < (2*Real.pi*Y^2)⁻¹ := by positivity
  have hd1 : (2*Real.pi*Y^2)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    have hy2 : 1 ≤ Y^2 := by nlinarith
    nlinarith [Real.pi_gt_three]
  have hb : ∀ q : S, Ioc (sourceRatioFrequency q)
      (sourceRatioFrequency q+(2*Real.pi*Y^2)⁻¹) ⊆ Icc (-2:ℝ) 2 := by
    intro q t ht
    have hq := abs_le.mp (hband q q.property)
    constructor <;> linarith [ht.1,ht.2]
  have hh := sampling_fourier_first_variation h1 h2 hR hs
    (fun q : S => sourceRatioFrequency q) hd (source_ratio_frequency_separated S hS) hb
  have he : (∑ q : S, ‖𝓕 f (sourceRatioFrequency q)‖) =
      ∑ q ∈ S, ‖𝓕 f (sourceRatioFrequency q)‖ :=
    Finset.sum_coe_sort S (fun q => ‖𝓕 f (sourceRatioFrequency q)‖)
  rw [← he]
  simpa only [inv_inv] using hh

/-- A shell Q<height≤2Q has multiplicity at most X/Q. This is the exact
high-shell analytic bound used before geometric summation. -/
theorem source_ratio_fourier_weighted_shell (S : Finset (ℕ × ℕ)) {Q X : ℝ}
    (hQ : 1 ≤ Q) (hX : 0 ≤ X)
    (hS : ∀ q ∈ S, 0 < q.1 ∧ 0 < q.2 ∧ q.1.Coprime q.2 ∧
      Q < (max q.1 q.2:ℕ) ∧ (max q.1 q.2:ℕ) ≤ 2*Q)
    (hband : ∀ q ∈ S, |sourceRatioFrequency q| ≤ 1)
    (w : ℕ × ℕ → ℝ) (hw : ∀ q ∈ S, w q ≤ X/(max q.1 q.2:ℕ))
    {f : ℝ → ℂ} (h1 : Integrable f) (h2 : MemLp f 2)
    {R : ℝ} (hR : 0 ≤ R) (hs : Function.support f ⊆ Icc (-R) R) :
    (∑ q ∈ S, w q*‖𝓕 f (sourceRatioFrequency q)‖) ≤
      8*Real.pi*X*Q*(∫ ξ in Icc (-2:ℝ) 2, ‖𝓕 f ξ‖)+
      4*Real.pi*X*R/Q*Real.sqrt (∫ t, ‖f t‖^2) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hb := source_ratio_fourier_first S (Y := 2*Q) (by linarith)
    (fun q hq => by
      obtain ⟨ha,hb,hc,_,hh⟩ := hS q hq
      refine ⟨ha,hb,hc,?_,?_⟩
      · exact (show (q.1:ℝ) ≤ (max q.1 q.2:ℕ) by exact_mod_cast (le_max_left q.1 q.2)).trans hh
      · exact (show (q.2:ℝ) ≤ (max q.1 q.2:ℕ) by exact_mod_cast (le_max_right q.1 q.2)).trans hh)
    hband h1 h2 hR hs
  calc
    _ ≤ ∑ q ∈ S, (X/Q)*‖𝓕 f (sourceRatioFrequency q)‖ := by
      apply sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact (hw q hq).trans (div_le_div_of_nonneg_left hX hQ0 (hS q hq).2.2.2.1.le)
    _ = (X/Q)*(∑ q ∈ S, ‖𝓕 f (sourceRatioFrequency q)‖) := (mul_sum ..).symm
    _ ≤ (X/Q)*(2*Real.pi*(2*Q)^2*(∫ ξ in Icc (-2:ℝ) 2, ‖𝓕 f ξ‖)+
        4*Real.pi*R*Real.sqrt (∫ t, ‖f t‖^2)) := mul_le_mul_of_nonneg_left hb (div_nonneg hX hQ0.le)
    _ = _ := by field_simp; ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.source_ratio_frequency_separated
#print axioms GuthMaynard.Improvement.source_ratio_fourier_square
#print axioms GuthMaynard.Improvement.source_ratio_fourier_weighted_low
#print axioms GuthMaynard.Improvement.source_ratio_fourier_first
#print axioms GuthMaynard.Improvement.source_ratio_fourier_weighted_shell
