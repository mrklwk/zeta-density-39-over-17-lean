import GuthMaynard.Improvement.SourceRatioSampling
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Finset
open scoped FourierTransform
namespace GuthMaynard.Improvement

def sourceRatioPairSet (N : ℝ) : Finset (ℕ × ℕ) :=
  (sourceRatioIndices N) ×ˢ (sourceRatioIndices N)
def sourceRatioImage (N : ℝ) : Finset (ℕ × ℕ) := (sourceRatioPairSet N).image sourceReducedPair
def sourceRatioWeight (N : ℝ) (q : ℕ × ℕ) : ℝ := (sourceRatioFiber (sourceRatioPairSet N) q).card

theorem source_ratio_pair_box {N : ℝ} (hN : 0 ≤ N) :
    ∀ p ∈ sourceRatioPairSet N, 0 < p.1 ∧ 0 < p.2 ∧ p.1 ≤ ⌊2*N⌋₊ ∧ p.2 ≤ ⌊2*N⌋₊ := by
  intro p hp
  obtain ⟨hn,hm⟩ := mem_product.mp hp
  have hn' := (sourceRatioIndices_mem hN p.1).mp hn
  have hm' := (sourceRatioIndices_mem hN p.2).mp hm
  exact ⟨by exact_mod_cast hN.trans_lt hn'.1,by exact_mod_cast hN.trans_lt hm'.1,
    Nat.le_floor hn'.2,Nat.le_floor hm'.2⟩

/-- The actual primitive image, actual multiplicity, and actual normalized
frequency obey the geometry needed by both sampling regimes. -/
theorem source_ratio_image_data {N : ℝ} (hN : 0 ≤ N) {q : ℕ × ℕ}
    (hq : q ∈ sourceRatioImage N) :
    0 < q.1 ∧ 0 < q.2 ∧ q.1.Coprime q.2 ∧ max q.1 q.2 ≤ ⌊2*N⌋₊ ∧
    (max q.1 q.2:ℕ) ≤ 2*N ∧ |sourceRatioFrequency q| ≤ 1 ∧
    0 ≤ sourceRatioWeight N q ∧ sourceRatioWeight N q ≤ 2*N/(max q.1 q.2:ℕ) := by
  have hp := source_ratio_image_properties (sourceRatioPairSet N) (source_ratio_pair_box hN) q hq
  have hweight : sourceRatioWeight N q ≤ 2*N/(max q.1 q.2:ℕ) := by
    calc
      _ ≤ ((⌊2*N⌋₊/max q.1 q.2:ℕ):ℝ) := by
        unfold sourceRatioWeight
        exact_mod_cast sourceRatioFiber_card (source_ratio_pair_box hN) hq
      _ ≤ (⌊2*N⌋₊:ℝ)/(max q.1 q.2:ℕ) := Nat.cast_div_le
      _ ≤ _ := div_le_div_of_nonneg_right (Nat.floor_le (by positivity)) (by positivity)
  have hband : |sourceRatioFrequency q| ≤ 1 := by
    obtain ⟨p,hp',rfl⟩ := mem_image.mp hq
    have hb := source_ratio_pair_box hN p hp'
    obtain ⟨hn,hm⟩ := mem_product.mp hp'
    have hl := source_ratio_log_band hN hn hm
    unfold sourceRatioFrequency
    rw [sourceReducedPair_ratio ⟨hb.1,hb.2.1⟩,abs_div,abs_of_pos (by positivity : 0 < 2*Real.pi)]
    apply (div_le_one (by positivity : 0 < 2*Real.pi)).mpr
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith [Real.pi_gt_three]
  exact ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2,
    (show ((max q.1 q.2:ℕ):ℝ) ≤ (⌊2*N⌋₊:ℝ) by exact_mod_cast hp.2.2.2).trans (Nat.floor_le (by positivity)),hband,by unfold sourceRatioWeight; positivity,hweight⟩

/-- The global square-weight budget dominates every actual low-height subset.
Its logarithm is the source length log(2N), avoiding an artificial floor loss. -/
theorem source_ratio_image_square_weight {N : ℝ} (hN : 2 ≤ N)
    (S : Finset (ℕ × ℕ)) (hS : S ⊆ sourceRatioImage N) :
    (∑ q ∈ S, (sourceRatioWeight N q)^2) ≤ 16*N^2*Real.log (2*N) := by
  have hN0 : 0 ≤ N := by linarith
  have hlog : 1 ≤ Real.log (2*N) := by
    have h4 : Real.log 4 ≤ Real.log (2*N) := Real.log_le_log (by norm_num) (by linarith)
    have he : Real.log 4 = 2*Real.log 2 := by
      rw [show (4:ℝ)=2*2 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
      ring
    rw [he] at h4
    linarith [Real.log_two_gt_d9]
  have hfloor : (0:ℝ) < (⌊2*N⌋₊:ℝ) := by
    have hh : 1 ≤ ⌊2*N⌋₊ := Nat.le_floor (by norm_num; linarith)
    exact_mod_cast hh
  have hlf := Real.log_le_log hfloor (Nat.floor_le (by positivity : 0 ≤ 2*N))
  have hb := positive_ratio_square_weight_log S (X := 2*N) (Y := ⌊2*N⌋₊) (by positivity)
    (fun q hq => ⟨(source_ratio_image_data hN0 (hS hq)).1,(source_ratio_image_data hN0 (hS hq)).2.1⟩)
    (fun q hq => (source_ratio_image_data hN0 (hS hq)).2.2.2.1)
    (sourceRatioWeight N)
    (fun q _ => by unfold sourceRatioWeight; positivity)
    (fun q hq => (source_ratio_image_data hN0 (hS hq)).2.2.2.2.2.2.2)
  calc
    _ ≤ 2*(2*N)^2*(1+Real.log (⌊2*N⌋₊:ℝ)) := hb
    _ ≤ 2*(2*N)^2*(2*Real.log (2*N)) := by
      apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

/-- Exact low-height estimate for actual gcd fibers. -/
theorem source_actual_ratio_low {N : ℝ} (hN : 2 ≤ N) {Y : ℝ} (hY : 0 < Y)
    {f : ℝ → ℂ} (h1 : Integrable f) (h2 : MemLp f 2)
    {R : ℝ} (hR : 0 ≤ R) (hs : Function.support f ⊆ Icc (-R) R) :
    (∑ q ∈ (sourceRatioImage N).filter (fun q => (max q.1 q.2:ℕ) ≤ Y),
      sourceRatioWeight N q*‖𝓕 f (sourceRatioFrequency q)‖) ≤
    Real.sqrt (16*N^2*Real.log (2*N))*Real.sqrt ((2*Real.pi*Y^2+4*Real.pi*R)*(∫ t, ‖f t‖^2)) := by
  apply source_ratio_fourier_weighted_low _ hY _ (sourceRatioWeight N)
    (source_ratio_image_square_weight hN _ (filter_subset ..)) h1 h2 hR hs
  intro q hq
  obtain ⟨hq,hheight⟩ := mem_filter.mp hq
  have hp := source_ratio_image_data (by linarith : 0 ≤ N) hq
  refine ⟨hp.1,hp.2.1,hp.2.2.1,?_,?_⟩
  · exact (show (q.1:ℝ) ≤ (max q.1 q.2:ℕ) by exact_mod_cast (le_max_left q.1 q.2)).trans hheight
  · exact (show (q.2:ℝ) ≤ (max q.1 q.2:ℕ) by exact_mod_cast (le_max_right q.1 q.2)).trans hheight

/-- Actual high-shell estimate with no arithmetic premise left open. -/
theorem source_actual_ratio_shell {N : ℝ} (hN : 2 ≤ N) {Q : ℝ} (hQ : 1 ≤ Q)
    {f : ℝ → ℂ} (h1 : Integrable f) (h2 : MemLp f 2)
    {R : ℝ} (hR : 0 ≤ R) (hs : Function.support f ⊆ Icc (-R) R) :
    (∑ q ∈ (sourceRatioImage N).filter (fun q => Q < (max q.1 q.2:ℕ) ∧ (max q.1 q.2:ℕ) ≤ 2*Q),
      sourceRatioWeight N q*‖𝓕 f (sourceRatioFrequency q)‖) ≤
    16*Real.pi*N*Q*(∫ ξ in Icc (-2:ℝ) 2, ‖𝓕 f ξ‖)+
      8*Real.pi*N*R/Q*Real.sqrt (∫ t, ‖f t‖^2) := by
  have hh := source_ratio_fourier_weighted_shell
    ((sourceRatioImage N).filter (fun q => Q < (max q.1 q.2:ℕ) ∧ (max q.1 q.2:ℕ) ≤ 2*Q)) hQ
    (X := 2*N) (by linarith) (fun q hq => by
      obtain ⟨hq,hheight⟩ := mem_filter.mp hq
      have hp := source_ratio_image_data (by linarith : 0 ≤ N) hq
      exact ⟨hp.1,hp.2.1,hp.2.2.1,hheight.1,hheight.2⟩)
    (fun q hq => (source_ratio_image_data (by linarith : 0 ≤ N) (mem_filter.mp hq).1).2.2.2.2.2.1)
    (sourceRatioWeight N)
    (fun q hq => (source_ratio_image_data (by linarith : 0 ≤ N) (mem_filter.mp hq).1).2.2.2.2.2.2.2)
    h1 h2 hR hs
  convert hh using 1; ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.source_ratio_pair_box
#print axioms GuthMaynard.Improvement.source_ratio_image_data
#print axioms GuthMaynard.Improvement.source_ratio_image_square_weight
#print axioms GuthMaynard.Improvement.source_actual_ratio_low
#print axioms GuthMaynard.Improvement.source_actual_ratio_shell
