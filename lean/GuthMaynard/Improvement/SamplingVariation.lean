import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Actual fundamental-theorem variation on a sampling interval. -/
theorem sampling_interval_variation {f f' : ℝ → E} {a δ t : ℝ}
    (hd : ∀ x, HasDerivAt f (f' x) x)
    (hi : IntegrableOn f' (Ioc a (a+δ))) (ht : t ∈ Ioc a (a+δ)) :
    ‖f a‖ ≤ ‖f t‖ + ∫ x in Ioc a (a+δ), ‖f' x‖ := by
  have hat : a ≤ t := ht.1.le
  have hit : IntervalIntegrable f' volume a t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hat]
    exact hi.mono_set (Ioc_subset_Ioc le_rfl ht.2)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hit
  have hv : ‖f t-f a‖ ≤ ∫ x in Ioc a (a+δ), ‖f' x‖ := by
    rw [← he]
    calc
      _ ≤ ∫ x in a..t, ‖f' x‖ := intervalIntegral.norm_integral_le_integral_norm hat
      _ = ∫ x in Ioc a t, ‖f' x‖ := intervalIntegral.integral_of_le hat
      _ ≤ _ := setIntegral_mono_set hi.norm (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
        (Filter.Eventually.of_forall (fun _ hx => Ioc_subset_Ioc le_rfl ht.2 hx))
  have hh := norm_sub_le (f t) (f t-f a)
  rw [sub_sub_cancel] at hh
  exact hh.trans (add_le_add le_rfl hv)

/-- Integrating the pointwise variation supplies the exact averaging cost. -/
theorem sampling_interval_average {f f' : ℝ → E} {a δ : ℝ}
    (hδ : 0 < δ) (hd : ∀ x, HasDerivAt f (f' x) x)
    (hf : IntegrableOn f (Ioc a (a+δ)))
    (hi : IntegrableOn f' (Ioc a (a+δ))) :
    δ*‖f a‖ ≤ (∫ x in Ioc a (a+δ), ‖f x‖)+
      δ*(∫ x in Ioc a (a+δ), ‖f' x‖) := by
  have hc : IntegrableOn (fun _ : ℝ => ‖f a‖) (Ioc a (a+δ)) := integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hv : IntegrableOn (fun _ : ℝ => ∫ x in Ioc a (a+δ), ‖f' x‖)
      (Ioc a (a+δ)) := integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hh := setIntegral_mono_on hc (hf.norm.add hv) measurableSet_Ioc
    (fun t ht => sampling_interval_variation hd hi ht)
  simp only [Pi.add_apply] at hh
  rw [integral_add hf.norm hv] at hh
  simpa only [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le (by linarith : a ≤ a+δ),
    add_sub_cancel_left] using hh

/-- Finite point sampling on disjoint actual intervals, with no point-value
estimate premise. The ambient set may be bounded; no global L1 of f' is required. -/
theorem sampling_disjoint_intervals {ι : Type*} [Fintype ι]
    {f f' : ℝ → E} (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ t, HasDerivAt f (f' t) t)
    (hs : Pairwise (fun i j => Disjoint (Ioc (x i) (x i+δ)) (Ioc (x j) (x j+δ))))
    {A : Set ℝ} (hsub : ∀ i, Ioc (x i) (x i+δ) ⊆ A)
    (hf : IntegrableOn f A) (hi : IntegrableOn f' A) :
    δ*(∑ i, ‖f (x i)‖) ≤ (∫ t in A, ‖f t‖)+δ*(∫ t in A, ‖f' t‖) := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    sampling_interval_average hδ hd (hf.mono_set (hsub i)) (hi.mono_set (hsub i)))
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hu : (⋃ i, Ioc (x i) (x i+δ)) ⊆ A := iUnion_subset hsub
  have hnorm (g : ℝ → E) (hg : IntegrableOn g A) :
      (∑ i, ∫ t in Ioc (x i) (x i+δ), ‖g t‖) ≤ ∫ t in A, ‖g t‖ := by
    rw [← integral_iUnion_fintype (fun _ => measurableSet_Ioc) hs
      (fun i => (hg.mono_set (hsub i)).norm)]
    exact setIntegral_mono_set hg.norm (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
      (Filter.Eventually.of_forall (fun _ ht => hu ht))
  exact hsum.trans (add_le_add (hnorm f hf) (mul_le_mul_of_nonneg_left (hnorm f' hi) hδ.le))


/-- Separation gives literal disjointness for half-open sampling intervals. -/
theorem sampling_intervals_disjoint {ι : Type*} (x : ι → ℝ) (δ : ℝ)
    (hsep : Pairwise (fun i j => δ ≤ |x i-x j|)) :
    Pairwise (fun i j => Disjoint (Ioc (x i) (x i+δ)) (Ioc (x j) (x j+δ))) := by
  intro i j hij
  apply disjoint_left.mpr
  intro t hti htj
  have hh : δ ≤ |x i-x j| := hsep hij
  by_cases hx : x i ≤ x j
  · rw [abs_of_nonpos (sub_nonpos.mpr hx)] at hh
    linarith [hti.2, htj.1]
  · rw [abs_of_nonneg (by linarith : 0 ≤ x i-x j)] at hh
    linarith [htj.2, hti.1]

/-- First-variation point sampling on any ambient set containing the
separated sampling intervals; all costs are ordinary integrals. -/
theorem sampling_separated_norm {ι : Type*} [Fintype ι]
    {f f' : ℝ → E} (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ t, HasDerivAt f (f' t) t)
    (hsep : Pairwise (fun i j => δ ≤ |x i-x j|))
    {A : Set ℝ} (hsub : ∀ i, Ioc (x i) (x i+δ) ⊆ A)
    (hf : IntegrableOn f A) (hi : IntegrableOn f' A) :
    (∑ i, ‖f (x i)‖) ≤ δ⁻¹*(∫ t in A, ‖f t‖)+(∫ t in A, ‖f' t‖) := by
  have hh := sampling_disjoint_intervals x hδ hd (sampling_intervals_disjoint x δ hsep) hsub hf hi
  apply (mul_le_mul_iff_right₀ hδ).mp
  convert hh using 1
  field_simp

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.sampling_interval_variation
#print axioms GuthMaynard.Improvement.sampling_interval_average
#print axioms GuthMaynard.Improvement.sampling_disjoint_intervals

#print axioms GuthMaynard.Improvement.sampling_intervals_disjoint
#print axioms GuthMaynard.Improvement.sampling_separated_norm
